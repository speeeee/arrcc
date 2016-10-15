{- based off of same set-stream/pass-stream idea.
 - concatenative: (f g)(x) -> f(g(x)).
 - tuples:        f(x,y,z) -> f is a function and (x,y,z) is a tuple of type (T0,T1,T2).
 -       :        (f g, h q)(x,y) -> (f(g(x,y)),h(q(x,y)))
 - function def:  :- type f := (int32, int32) -> int32.
 -             :  f := (+)
 -             :  :- type isqrt := (int32 ((>)&0)) -> (int32 ((>)&0)).
 - language based off of functions on tuples and operators. e.g. +, :-, and = are operators.
 - types are predicates too, making for easy composition.
 - instead of true/false, all values are truthy except for false.  also maybe type.
 - all is point-free except monads and dyads, having static variable names @x and @y.
 - functions on symbols are runtime only.
 - all symbols are 3-ples with default value (Val,Type,Scope = 0). 
 - proofing example: -- warning: this is all very rough and may not even be part of the language.
   type positive := runtime int32 -> bool,
   positive := >&0, -- specifically for runtime int32 s.

   :> (runtime int32) positive, -- all new runtime int32 s will be tested with this predicate.
   H add@(positive int32, int32) := rebuke positive -- if a positive is added to a regular, then
                                                    -- the positive is no longer provably positive. -}
{-# LANGUAGE MultiWayIf, ScopedTypeVariables #-}
import Data.List (union,find,(\\))
import Data.List.Split
import Text.Read (readMaybe)

import Debug.Trace

data Typ   = C [Char] | S SType deriving (Show,Eq)
data SType = SType [Typ] | SF [SType] SType | Tu [SType] deriving (Show)
instance Eq SType where
  (SType a) == (SType b) = all (`elem`a) b||C"any"`elem`b
  (SF a b) == (SF c d) = a==c&&b==d

data Dyad = Dyad ([Var] -> Expr -> Expr -> ([Var],Expr))
data Mon  = Mon ([Var] -> Expr -> ([Var],Expr))

data Args = X | Y | PArg deriving (Show,Eq)

data Var  = Var [Char] Expr Int deriving (Show) -- scope; C-based
instance Eq Var where
  (Var na _ _) == (Var nb _ _) = na==nb
data Expr = Lit [Char] SType
          | Sym Expr SType Int -- (Val,Type,Scope).
          | Tup [Expr] | Lst [Expr] SType
          | Quote [Expr] | OpD ([Var] -> Expr -> Expr -> ([Var],Expr)) SType
          | OpM ([Var] -> Expr -> ([Var],Expr)) SType
          -- | D Expr Dyad Expr
          -- | M Mon Expr
          | Function ([Var] -> [Expr] -> Int -> ([Var],Expr)) SType
              -- functions/variables -> tuple -> scope -> result.
          -- | C Expr Expr -- composition or special application. e.g. (f, g)(x).
          | Arg Args | LError [Char]
instance Eq Expr where
  (Lit a ta) == (Lit b tb) = a==b&&tb==ta
  (Sym e t s) == (Sym eb tb sb) = e==eb&&t==tb&&s==sb
  (Tup a) == (Tup b) = a==b
  a == b = False
instance Show Expr where
  show (OpM _ _) = "<monadic function>"
  show (OpD _ _) = "<dyadic function>"
  show (Function _ _) = "<function>"
  show (Lit a t) = concat ["Lit ",show a," ",show t]
  show (Quote a) = "Quote "++show a
  show (LError a) = "Error: "++a++"\n"
  show (Tup e) = "Tuple "++show e

inputs :: SType -> [SType]
inputs (SF a _) = a
inputs _ = []

-- DONE: fix `,' function.
-- TODO: make `cprog' (updated after each `exec').
-- TODO: define `cons/mk-list' as `;'.
pvs :: [Var]
pvs = [Var "pprog" (Lit [] $ SType [C"program"]) 0
      ,Var "add" (Function (\vs tup sc -> case tup of
                             (Lit a _:Lit b _:_) ->
                               let (Var _ (Lit prog _) _) = head vs
                                   res = concat ["int32_t add_",a,"_",b," = (",a,"+",b,");\n"]
                                   nv  = Var "pprog" (Lit (prog++res) $ SType [C"program"]) 0
                               in (nv:tail vs
                                  ,Lit ("add_"++a++"_"++b) $ SType [C"int32"])
                             _ -> (vs,LError "not enough arguments.\n"))
                  (SF [SType [C"int32"],SType [C"int32"]] $ SType [C"int32"])) 0
      ,Var "," (OpD (\vs a b -> case b of (Tup q) -> (vs,Tup (a:q))
                                          _ -> (vs,Tup [a,b]))
                 (SF [SType [C"any"],SType [C"any"]] $ SType [C"T"])) 0]

downLevel :: [Char] -> [[Char]]
downLevel = chop (\k@(kh:ks) -> if | kh=='(' -> let (kka,kks) = parens "()" ([],ks) 1
                                                in (concat ["(",kka,")"],kks)
                                   | kh=='{' -> let (kka,kks) = parens "{}" ([],ks) 1
                                                in (concat ["{",kka,"}"],kks)
                                   | kh`elem`" \r\t\n" ->
                                       ([],snd $ span (`elem`" \r\t\n") ks)
                                   | kh`elem`"<>+-/*," -> ([kh],ks)
                                   | otherwise -> span (not . (`elem`" \r\t\n({,<>+-/*")) k)

parens :: [Char] -> ([Char],[Char]) -> Int -> ([Char],[Char])
parens (a:b:_) (e,(kh:ks)) amt = if | kh==a -> parens (a:b:[]) (e++[a],ks) (amt+1)
                                    | kh==b -> if amt == 1 then (e,ks) else parens (a:b:[]) (e++[b],ks) (amt-1)
                                    | otherwise -> parens (a:b:[]) (e++[kh],ks) amt
parens _ _ _ = ([],[])

conv :: [[Char]] -> [([Char],SType)]
-- use of head here is dangerous, but empty strings were filtered previously.
conv = map (\k -> case head k of
             '(' -> (init $ tail k,SType [C"runtime",C"group"])
             _   -> (k,typeOf k))

lexer :: [Char] -> [Expr]
lexer =
  map (\k -> case k of (a,SType [C"runtime",C"group"]) -> Quote $ lexer a
                       (a,t)                   -> Lit a t)
  . conv . filter (not . null) . downLevel

typeF :: Double -> SType
typeI :: Int    -> SType
typeF _ = SType [C"runtime",C"float32"]
typeI _ = SType [C"runtime",C"int32"]

typeOf :: [Char] -> SType
typeOf str = maybe (maybe (SType [C"runtime",C"sym/var"]) typeF (readMaybe str :: Maybe Double))
                   typeI (readMaybe str :: Maybe Int)

symvar :: [Var] -> [Expr] -> [Expr]
symvar vs = map (\k -> case k of
                  (Lit a (SType [C"runtime",C"sym/var"])) -> 
                    case find (\(Var n _ _) -> n==a) vs of
                      Just (Var n x _) -> x
                      Nothing          -> Lit a $ SType [C"runtime",C"symbol"]
                  a -> a)

getType :: Expr -> SType
getType (Lit _ t) = t
getType (OpD _ t) = t
getType (OpM _ t) = t
getType (Function _ t) = t
getType (Quote _) = SType [C"runtime",C"group"]
getType (Tup _) = SType [C"tuple"]
getType (Lst _ t) = SType [C"list",S t]
getType _ = SType [C"error"]
typeCheck :: [SType] -> [SType] -> Bool
typeCheck = (==)

combC :: Var -> Var -> Var
combC (Var "pprog" (Lit a _) _) (Var "pprog" (Lit b _) _) =
  Var "pprog" (Lit (a++b) $ SType [C"program"]) 0

--exec :: [Var] -> [Expr] -> ([Var],Expr)
--exec vs = foldl (\q nvs ->) vs . splitOn ","
-- any output of a given expression is documented in the 'cprog' variable.
-- WARNING: `flip union' done because when two elements match (wrt Eq instance), the LHS is preferred.
exec :: [Var] -> [Expr] -> [Var]
exec vs e = foldl (\nvs q -> flip union nvs $ fst $ parse nvs $ symvar nvs q) vs $ splitOn
              [(Lit "," $ SType [C"runtime",C"sym/var"])] e

{- Rules of parsing:
   - if the first expression Q in list L is a symbol and a monad -> Q (tail L)
   ; if there exists a symbol S in list L that is a dyad -> (left of S in L) S (right of S in L)
       (note: (,) is a dyad that can make tuples)
   ; if expression A is adjacent to expression B (right associative) ->
       if A is a function and B is a tuple -> apply A to B if type matches correctly
     ; if both A and B are functions -> perform function compositions if types permit
     ; if type of A is (T1,T2,...) and Tn is a function and B is a tuple ->
         if types permit, apply all functions to that tuple and return a tuple of the results
     ; return syntax error
   ; return syntax error -}
{- General use:
   - monad 'dyad' is used to define a dyadic function: type f := (int32, int32) -> int32,
                                                       dyad f := @x + @y
   - the same is with monad 'monad'. -}
{- set names at current scope in expression -}
-- untyped so far
-- not yet implemented composition
parse :: [Var] -> [Expr] -> ([Var],Expr)
{-parse vs (a:[]) = (vs,a)
parse vs (OpM f typ:r) = uncurry f $ parse vs r
parse vs (l:OpD f typ:r) = f vs (snd $ parse vs [l]) (snd $ parse vs r)
parse vs (Quote a:r) = parse vs $ (snd $ parse vs a):r
parse vs (Function fa typ:r) = case parse vs r of
  (_,Tup lst) -> if (map getType lst) == (inputs typ) 
                 then fa vs lst 0 else (vs,LError "type mismatch.\n")
  _           -> (vs,LError "function could not be applied correctly.")
-- parse vs (a:[]) = (vs,a)
parse vs a = (vs,LError "ill-formed expression.")-}
parse vs q = case q of
  --(a:[]) -> (vs,a)
  (OpM f typ:r) -> uncurry f $ parse vs r
  (l:OpD f typ:r) -> let (lvs,lhs) = parse vs [l]
                         (rvs,rhs) = parse vs r
                     in f (combC (head lvs) (head rvs):tail lvs) lhs rhs
  (Quote a:r) -> let (nvs,nq) = parse vs $ symvar vs a
                 in parse nvs $ nq:r
  (Function fa typ:r) -> case parse vs r of
    (nvs,Tup lst) -> if (map getType lst) == (inputs typ) 
                   then fa nvs lst 0 else (nvs,LError "type mismatch.\n")
    _           -> (vs,LError "function could not be applied correctly.")
  (a:[]) -> (vs,a)
  _ -> (vs,LError "ill-formed expression.")

main = do
  putStrLn $ show $ exec pvs $ lexer "add(1,add(2,3))"

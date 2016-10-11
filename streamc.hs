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

type Typ   = [[Char]]
data SType = SType Typ | SF [Typ] Typ deriving (Show)
instance Eq SType where
  (SType a) == (SType b) = all (`elem`a) b
  (SF a b) == (SF c d) = a==c&&b==d

data Dyad = Dyad ([Var] -> Expr -> Expr -> ([Var],Expr))
data Mon  = Mon ([Var] -> Expr -> ([Var],Expr))

data Args = X | Y | PArg deriving (Show,Eq)

data Var  = Var [Char] Expr Int deriving (Show) -- scope; C-based
instance Eq Var where
  (Var na _ _) == (Var nb _ _) = na==nb
data Expr = Lit [Char] SType
          | Sym Expr SType Int -- (Val,Type,Scope).
          | Tup [Expr]
          | Quote [Expr] | OpD ([Var] -> Expr -> Expr -> ([Var],Expr))
          | OpM ([Var] -> Expr -> ([Var],Expr))
          -- | D Expr Dyad Expr
          -- | M Mon Expr
          | Function ([Var] -> [Expr] -> Int -> ([Var],Expr))
              -- functions/variables -> tuple -> scope -> result.
          | C Expr Expr -- composition or special application. e.g. (f, g)(x).
          | Arg Args | LError [Char]
instance Eq Expr where
  (Lit a ta) == (Lit b tb) = a==b&&tb==ta
  (Sym e t s) == (Sym eb tb sb) = e==eb&&t==tb&&s==sb
  (Tup a) == (Tup b) = a==b
  a == b = True
instance Show Expr where
  show (OpM _) = "<monadic function>"
  show (OpD _) = "<dyadic function>"
  show (Function _) = "<function>"
  show (Lit a t) = concat ["Lit ",show a," ",show t]
  show (Quote a) = "Quote "++show a
  show (LError a) = "Error: "++a++"\n"
  show (Tup e) = "Tuple "++show e

pvs :: [Var]
pvs = [Var "cprog" (Lit [] $ SType ["program"]) 0
      ,Var "add" (Function (\vs tup sc -> case tup of
                             (Lit a (SType ["int32"]):Lit b (SType ["int32"]):_) ->
                               let (Var _ (Lit prog _) _) = head vs
                                   res = concat ["int32_t add_",a,"_",b," = (",a,"+",b,");\n"]
                               in (Var "cprog" (Lit (prog++res) $ SType ["program"]) 0:tail vs
                                  ,Lit ("add_"++"a"++"_"++"b") $ SType ["int32"])
                             _ -> (vs,LError "type mismatch.\n"))) 0]

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
             '(' -> (init $ tail k,SType ["runtime","group"])
             _   -> (k,typeOf k))

lexer :: [Char] -> [Expr]
lexer =
  map (\k -> case k of (a,SType ["runtime","group"]) -> Quote $ lexer a
                       (a,t)                   -> Lit a t)
  . conv . filter (not . null) . downLevel

typeF :: Double -> SType
typeI :: Int    -> SType
typeF _ = SType ["runtime","float32"]
typeI _ = SType ["runtime","int32"]

typeOf :: [Char] -> SType
typeOf str = maybe (maybe (SType ["runtime","sym/var"]) typeF (readMaybe str :: Maybe Double))
                   typeI (readMaybe str :: Maybe Int)

symvar :: [Var] -> [Expr] -> [Expr]
symvar vs = map (\k -> case k of
                  (Lit a (SType ["runtime","sym/var"])) -> 
                    case find (\(Var n _ _) -> n==a) vs of
                      Just (Var n x _) -> x
                      Nothing     -> Lit a $ SType ["runtime","symbol"]
                  a -> a)

--exec :: [Var] -> [Expr] -> ([Var],Expr)
--exec vs = foldl (\q nvs ->) vs . splitOn ","
-- any output of a given expression is documented in the 'cprog' variable.
exec :: [Var] -> [Expr] -> [Var]
exec vs e = foldl (\nvs q -> union nvs $ fst $ parse vs $ symvar vs q) vs $ splitOn
              [(Lit "," $ SType ["runtime","sym/var"])] e

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
parse vs (OpM f:r) = uncurry f $ parse vs r
parse vs (l:OpD f:r) = f vs (snd $ parse vs [l]) (snd $ parse vs r)
parse vs (Quote a:r) = parse vs $ (snd $ parse vs a):r
parse vs (Function fa:r) = case parse vs r of
  (_,Tup lst) -> fa vs lst 0
  _           -> (vs,LError "function could not be applied correctly.")
parse vs (a:[]) = (vs,a)
parse vs _ = (vs,LError "ill-formed expression.")

main = do
  putStrLn $ show $ snd $ parse pvs $ lexer "add(1,2)"

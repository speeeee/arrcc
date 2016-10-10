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

type Typ   = [[Char]]
data SType = SType Typ | SF [Typ] Typ deriving (Show,Eq)

data Dyad = Dyad [Char] ([Var] -> Expr -> Expr -> ([Var],Expr))
data Mon  = Mon [Char] ([Var] -> Expr -> ([Var],Expr))

data Args = X | Y | PArg deriving (Show,Eq)

data Var  = Var Name Expr SType Int deriving (Show,Eq) -- scope
data Expr = Lit [Char] SType
          | Sym Expr SType Int -- (Val,Type,Scope).
          | Tup [Expr]
          | Quote [Expr]
          | D Expr Dyad Expr
          | M Mon Expr
          | Function [Char] ([Var] -> [Expr] -> Int -> ([Var],Expr))
              -- functions/variables -> tuple -> scope -> result.
          | C Expr Expr -- composition or special application. e.g. (f, g)(x).
          | Arg Args | LError

vs :: [Var]
vs = []

downLevel :: [Char] -> [[Char]]
downLevel = chop (\k@(kh:ks) -> if | kh == '(' -> concat ["(",parens "()" ([],ks) 1,")"]
                                   | kh == '{' -> concat ["{",parens "{}" ([],ks) 1,"}"]
                                   | kh`elem`" \r\t\n" -> ([],snd $ span (flip elem " \r\t\n") ks)
                                   | otherwise -> span (not . flip elem " \r\t\n({,<>+-/*") k)

parens :: [Char] -> ([Char],[Char]) -> Int -> ([Char],[Char])
parens (a:b:_) (e,(kh:ks)) amt = if | kh==a -> parens (a:b:[]) (e++[a],ks) (amt+1)
                                    | kh==b -> if amt == 1 then (e,ks) else parens (a:b:[]) (e++[b],ks) (amt-1)
                                    | otherwise -> parens (a:b:[]) (e++[kh],ks) amt
parens _ _ _ = ([],[])

{- lexe :: [Char] -> SExp
lexe q = let qx = filter (not . null) $ downLevel q in
  case qx of (('\'':ks):[]) -> Quote $ lexe ks
             (":A:":[]) -> Arg
             (qh:[]) -> SL qh (typeOf qh)
             (qh:qs) -> SApp (lexe qh) (map lexe qs)
             _       -> SList [] -}

conv :: [[Char]] -> ([Char],SType)
conv = map (\k -> case (kh:_) of
             '(' -> (init $ tail k,SType ["runtime","group"])
             _   -> typeOf k)

lexer :: [[Char]] -> [Expr]
lexer =
  map (\k -> case k of (a,["runtime","group"]) -> Quote a
                       (a,t)                   -> Lit a t
                       _                       -> LError) . conv . filter (not . null) . downLevel

typeF :: Double -> SType
typeI :: Int    -> SType
typeF _ = SType ["runtime","float32"]
typeI _ = SType ["runtime","int32"]

typeOf :: [Char] -> SType
typeOf str = maybe (maybe (SType ["runtime","sym/var"]) typeF (readMaybe str :: Maybe Double))
                   typeI (readMaybe str :: Maybe Int)
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
{-parse :: [Expr] -> Expr
parse ((Lit a ["runtime","sym/var"):r) = -}

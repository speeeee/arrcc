{- Mid-level array programming language that compiles to C.
 - 12 20 34 5 Int alloc -- allocates integer array with supplied values. -}

data SType    = TInt8 | TInt16 | TInt32 | TInt64 | TFloat32 | TFloat64
              | Vec | RuntimeL | Func [SType] | Any | LError deriving (Show,Eq)
data Function = Function [Char] ([SExp] -> SExp) [Int] [SType] SType
instance Show Function where
  show (Function n _ _ i o) = n ++ " " ++ show i ++ " " ++ show o

data SExp = SApp Function [SExp] 
          | SL [Char] SType | Quote [SExp]
          | SError [Char] deriving (Show)

fs = [Function "+" (\lst -> case lst of
                     (SL a _:SL b _:_) -> SL (concat ["(",a,"+",b,")"]) TInt32
                     _ -> SError "Error.\n") [] [TInt32,TInt32] TInt32]
add = head fs

ltype :: SExp -> SType
ltype (SL _ t) = t
ltype _ = LError

appF :: Function -> [SExp] -> SExp
appF (Function _ f _ t _) e =
  if t /= map ltype e then SError "Error: type mismatch.\n"
  else f e

eval :: SExp -> SExp
eval (SApp f a) = appF f $ map eval a
eval a = a

main = do
  putStrLn $ show $ eval (SApp add [SL "4" TInt32, SL "5" TInt32])

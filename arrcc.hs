{- Mid-level array programming language that compiles to C.
 - 12 20 34 5 Int alloc -- allocates integer array with supplied values. -}

import Debug.Trace

-- (lambda (type Int32 Int32) (quote + 1 (head :A:))) 
--   --> Function "Lambda" (+ 1 (head :A:)) [TInt32,TInt32]

data SType    = TInt8 | TInt16 | TInt32 | TInt64 | TFloat32 | TFloat64
              | Symbol | Quot | TArr | TList | Func [SType] | Any | LError deriving (Show)
-- because of Any, any function type must be on RHS.
instance Eq SType where
  a == Any = True
  a == b = show a == show b
data Function = Function [Char] ([Function] -> [SExp] -> ([Function],SExp)) [Int] [SType]
instance Show Function where
  show (Function n _ _ io) = "{" ++ n ++ " " ++ show io ++ "}"
instance Eq Function where
  _ == _ = False

data SExp = SApp SExp [SExp] | SFunc Function
          | SL [Char] SType | Quote SExp | SArr [SType] | SList [SExp]
          | Arg | SError [Char]  deriving (Show,Eq)

fs :: [Function]
fs = [Function "+" (\nfs lst -> case lst of
                     (SL a _:SL b _:_) -> (nfs,SL (concat ["(",a,"+",b,")"]) TInt32)
                     _ -> (nfs,SError "Error.\n")) [] [TInt32,TInt32,TInt32]
     ,Function "head" (\nfs lst -> case lst of
                        (SList a:_) -> (nfs,head a)
                        _ -> (nfs,SError "Error.\n")) [] [TList,Any]
     ,Function "def" (\nfs lst -> case lst of
                       (SL n _:SArr a:Quote b:_) ->
                         (Function n (\nnfs nlst -> eval nnfs $ repl nlst b) [] a:nfs,SList [])
                       _ -> (nfs,SError "Error.\n")) [] [Symbol,TArr,Quot,TList]
     ,Function "error" (\_ _ -> ([],SError "Error.\n")) [] []]
add, def :: Function
add    = head fs
def    = fs!!2
shead  = fs!!1
serror = fs!!3

repl :: [SExp] -> SExp -> SExp
repl l k = case k of Arg           -> SList l
                     (SApp f args) -> SApp f $ map (repl l) args
                     (SList s)     -> SList $ map (repl l) s
                     a             -> a

ltype :: SExp -> SType
ltype (SL _ t) = t
ltype (Quote _) = Quot
ltype (SArr _) = TArr
ltype (SList _) = TList
ltype (SFunc (Function _ _ _ io)) = Func io
ltype _ = LError

appF :: Function -> ([Function],[SExp]) -> ([Function],SExp)
appF (Function "serror" _ _ _) _ = ([], SError "Error: s-exp head not a function.\n")
appF (Function n f _ t) (nfs,e) =
  if map ltype e /= (init t) then
    (nfs,SError $ concat ["Error: type mismatch: ", show $ map ltype e, " ", show $ init t, "\n"])
  else (f nfs) e

eval :: [Function] -> SExp -> ([Function],SExp)
eval nfs (SApp f a) = appF fun $ (fst $ last ev, map snd ev)
  where ev = map (eval nfs) a
        fun = case snd $ eval nfs f of (SFunc fu) -> fu
                                       _          -> serror
eval nfs (SList a) = (fst $ last ev, SList $ map snd ev) where ev = map (eval nfs) a
eval nfs a = (nfs,a)

main = do
  let (nfs,res) = eval [] (SApp (SFunc def) [SL "inc" Symbol, SArr [TInt32,TInt32]
                                            ,Quote (SApp (SFunc add)
                                               [SApp (SFunc shead) [Arg],SL "1" TInt32])])
  putStrLn $ show $ eval [] (SApp (SFunc $ nfs!!0) [SL "1" TInt32]) 

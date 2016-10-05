{-# LANGUAGE MultiWayIf #-}
{- Mid-level array programming language that compiles to C.
 - 12 20 34 5 Int alloc -- allocates integer array with supplied values. -}

{- Stream-based idea would make best of looping.  Values can be added to the stream and removed. -}

import Data.List
import Data.List.Split
import Text.Read (readMaybe)

import Debug.Trace

-- (lambda (type Int32 Int32) (quote + 1 (head :A:))) 
--   --> Function "Lambda" (+ 1 (head :A:)) [TInt32,TInt32]

data SType    = TInt8 | TInt16 | TInt32 | TInt64 | TFloat32 | TFloat64
              | Symbol | Quot | TArr | TList | Func [SType] | Any 
              | Varying SType | LError deriving (Show,Read)
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

-- TODO: add lambda function. DONE
-- TODO: make type-casting functions for Int8, Int16, etc. from Int32.
-- TODO: make function: SList -> SArr
-- TODO: make function: {Args} -> SList DONE
fs :: [Function]
fs = [Function "+" (\nfs lst -> case lst of
                     (SL a _:SL b _:_) -> (nfs,SL (concat ["(",a,"+",b,")"]) TInt32)
                     _ -> (nfs,SError "Error.\n")) [] [TInt32,TInt32,TInt32]
     ,Function "head" (\nfs lst -> case lst of
                        (SList a:_) -> (nfs,head a)
                        _ -> (nfs,SError "Error.\n")) [] [TList,Any]
     {-,Function "tail" (\nfs lst -> case lst of
                        (SList a:_) -> (nfs,SList $ tail a)
                        _ -> (nfs,SError "Error.\n")) [] [TList,Any]
     ,Function "empty?" (\nfs lst -> case lst of
                          (SList a:_) -> (nfs, SL (show $ fromEnum $ null a) TInt32)
                          _ -> (nfs,SError "Error.\n")) [] [TList,TInt32]
     ,Function "lambda" (\nfs lst -> case lst of
                          (SArr a:Quote  b:_) ->
                            (nfs,SFunc $ Function "LAMB" (\nnfs nlst -> eval nnfs $ repl nlst b) [] a)
                          _ -> (nfs,SError "Error.\n")) [] [TArr,Quot,Any]
     ,Function "list" (\nfs lst -> (nfs,SList lst)) [] [Varying Any]
     ,Function "type" (\nfs lst -> case lst of
                        (SList a:_) -> (nfs,SArr $ map lstToType a)
                        _ -> (nfs,SError "Error.\n")) [] [TList,TArr]-}
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

{-lstToType :: [SExp] -> SType
lstToType (SL a Symbol) = read a :: SType
lstToType (SList a) = SArr $ map lstToType a
lstToType _ = LError-}

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
appF (Function "error" _ _ _) _ = ([], SError "Error: s-exp head not a function.\n")
appF (Function n f _ [Varying a]) (nfs,e) =
  if all (==a) $ map ltype e then (f nfs) e
  else (nfs,SError $ concat ["Error: type mismatch: ", show $ map ltype e, " ", show a, "...\n"])
appF (Function n f _ t) (nfs,e) =
  if map ltype e /= (init t) then
    (nfs,SError $ concat ["Error: type mismatch: ", show $ map ltype e, " ", show $ init t, "\n"])
  else (f nfs) e

eval :: [Function] -> SExp -> ([Function],SExp)
eval nfs (SApp f a) = appF fun $ (fst $ last ev, map snd ev)
  where ev = map (eval nfs) a
        fun = case snd $ eval nfs f of
                (SFunc fu)    -> fu
                (SL n Symbol) -> maybe serror id (find (\(Function k _ _ _) -> k==n) (nfs++fs))
                _             -> serror
eval nfs (SList a) = (fst $ last ev, SList $ map snd ev) where ev = map (eval nfs) a
eval nfs a = (nfs,a)

{-- Lexer ---------------------------------------}
-- standard LISP-style lexer (topmost parentheses omitted)

-- takes character list and parses the toplevel as if it were an s-expr.
--   e.g. "+ (+ 1 2) 1" --> ["+", "+ 1 2", "1"]
downLevel :: [Char] -> [[Char]]
downLevel = chop (\k@(kh:ks) -> if | kh == '(' -> parens "()" ([],ks) 1
                                   | kh == '{' -> parens "{}" ([],ks) 1
                                   | kh`elem`" \r\t\n" -> ([],snd $ span (flip elem " \r\t\n") ks)
                                   | otherwise -> span (not . flip elem " \r\t\n(") k)

parens :: [Char] -> ([Char],[Char]) -> Int -> ([Char],[Char])
parens (a:b:_) (e,(kh:ks)) amt = if | kh==a -> parens (a:b:[]) (e++[a],ks) (amt+1)
                                    | kh==b -> if amt == 1 then (e,ks) else parens (a:b:[]) (e++[b],ks) (amt-1)
                                    | otherwise -> parens (a:b:[]) (e++[kh],ks) amt
parens _ _ _ = ([],[])

lexe :: [Char] -> SExp
lexe q = let qx = filter (not . null) $ downLevel q in
  case qx of (('\'':ks):[]) -> Quote $ lexe ks
             (":A:":[]) -> Arg
             (qh:[]) -> SL qh (typeOf qh)
             (qh:qs) -> SApp (lexe qh) (map lexe qs)
             _       -> SList []

typeF :: Double -> SType
typeI :: Int    -> SType
typeF _ = TFloat64
typeI _ = TInt32

typeOf :: [Char] -> SType
typeOf str = maybe (maybe Symbol typeF (readMaybe str :: Maybe Double))
                   typeI (readMaybe str :: Maybe Int)
{------------------------------------------------}

main = do
  {-let (nfs,res) = eval [] (SApp (SL "def" Symbol)
                            [SL "inc" Symbol, SArr [TInt32,TInt32]
                            ,Quote (SApp (SL "+" Symbol)
                              [SApp (SL "head" Symbol) [Arg],SL "1" TInt32])])
  putStrLn $ show $ eval nfs (SApp (SL "inc" Symbol) [SL "1" TInt32])-}
  let (nfs,res) = eval [] $ lexe "+ (+ 1 2) 3"
  putStrLn $ show res

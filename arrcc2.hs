{-# LANGUAGE MultiWayIf #-}

{- more or less similar to arrcc(1) but with a deque-based idea now.  It is still based off of
 - streams: $ 1 2 3 Int32 salloc $ 2 3 4 Int32 salloc {x let y let x [+ <<] stream}
 - - First, {1,2,3} is allocated, followed by {2,3,4}
 - - { dup's the references of the two arrays and pushes &a &b SCOPE to the back of the deque:
 - Back:  {1,2,3}
          {2,3,4}
   Front: SCOPE
 - `x let' simply takes the reference for {1,2,3} and assigns it to x.  assignment is done by
     pushing to the back of the deque adding to the "things-to-be-derefeced".  lets are write-once.
 - `y let' does the same with {2,3,4}.
 - `x' push x
 - `[+ <<] stream' is a stream combinator that will add the first two elements of the stream
      and push the sum back to it until the stream is empty.  This is effectively a fold: 9. -}

import Data.List (find,intersect)
import Data.List.Split
import Text.Read (readMaybe)
import Debug.Trace

data SType = TSym | TInt8 | TInt16 | TInt32 | TInt64 | TFloat32 | TFloat64 deriving (Show,Eq)

type Deque = [Lit]
data Lit = SL [Char] SType | SQ [Lit] | SError [Char] deriving (Show,Eq)
data Func = Func [Char] ([Func] -> [Lit] -> ([Func],[Lit]))
instance Show Func where
  show (Func n _) = "<function: "++n++">"

fs :: [Func]
fs = [Func "+" (\nfs deq -> case deq of
                  (SL a TInt32:SL b TInt32:r) -> (nfs, SL (concat ["(",a,"+",b,")"]) TInt32:r)
                  _ -> (nfs,[SError "Error: stack underflow or type mismatch.\n"]))
     ,Func "call" (\nfs deq -> case deq of
                    (SQ a:r) -> eval (nfs,r) a
                    _ -> (nfs,[SError "Error: Callee not a valid quote.\n"]))
     ,Func "error" (\_ _ -> ([],[SError "Error: attempted to call unbound variable.\n"]))]
serror :: [Func] -> [Lit] -> ([Func],[Lit])
serror = let (Func _ b) = fs!!2 in b

pushf, pushb :: Lit -> [Lit] -> [Lit]
pushf = (:)
pushb = flip (++) . (:[])

popf, popb :: [Lit] -> Lit
popf = head
popb = last

tokens :: [Char] -> [[Char]]
tokens = chop (\k@(kh:ks) -> if | kh`elem`" \t\r\n" -> ([], snd $ span (`elem`" \t\r\n") ks)
                                | kh`elem`"(){}'" -> ([kh],ks)
                                | kh=='[' -> parens ([],ks) 1 
                                | otherwise -> span (not . (`elem`" \t\r\n(){}[]'")) k)

-- cleaning needed..
parens :: ([Char],[Char]) -> Int -> ([Char],[Char])
parens (e,('[':ks)) amt = parens (e++"[",ks) (amt+1)
parens (e,(']':ks)) amt = if amt == 1 then (e,ks) else parens (e++"]",ks) (amt-1)
parens (e,k:ks) amt = parens (e++[k],ks) amt
parens _ _ = ([],[])

typeF :: Double -> SType
typeI :: Int    -> SType
typeF _ = TFloat64
typeI _ = TInt32

lexer :: [[Char]] -> [Lit]
lexer =
  map (\k -> maybe (maybe (if null $ intersect k " \t\r\n" then SL k TSym
                                                           else SQ $ lexer $ tokens k)
                     (SL k . typeF) (readMaybe k :: Maybe Double))
               (SL k . typeI) (readMaybe k :: Maybe Int)) . filter (not . null)

eval :: ([Func],[Lit]) -> [Lit] -> ([Func],[Lit])
eval = foldl (\(nfs,nd) lit -> case lit of
               (SL a TSym) -> f nfs nd where f = case find (\(Func n _) -> n==a) $ fs++nfs of
                                                   Just (Func _ fun) -> fun
                                                   Nothing           -> serror
               a        -> (nfs,a:nd))

main = do
  putStrLn $ show $ eval ([],[]) $ lexer $ tokens "1 3 +"

{-@ LIQUID "--reflection" @-}

module Ceu.Expr where

import Ceu.LH as LH
import Prelude hiding (read)
import qualified Data.Set as S

-- Variable name.
type Id = String

-- Variable value.
type Val = Int

-- Memory.
type Mem = [(Id,Maybe Val)]

-- Expression.
data Expr
  = Const Val
  | Read Id
  | Add Expr Expr
  deriving (Eq, Show)

-- Gets the set of variables declared in memory 'm'.
{-@ measure declSet @-}
declSet :: Mem -> S.Set Id
declSet m = case m of
  []       -> S.empty
  (x,_):xs -> S.union (S.singleton x) (declSet xs)

-- Gets the set of variables defined in memory 'm'.
{-@ measure defnSet @-}
defnSet :: Mem -> S.Set Id
defnSet m = case m of
  []                     -> S.empty
  (x,y):xs | LH.isJust y -> S.union (S.singleton x) (defnSet xs)
           | otherwise   -> S.difference (defnSet xs) (S.singleton x)

{-@ predicate DeclP M ID = member ID (declSet M) @-}
{-@ predicate DefnP M ID = member ID (defnSet M) @-}

-- Gets the set of variables referenced in expression 'e'.
{-@ measure readSet @-}
readSet :: Expr -> S.Set Id
readSet e = case e of
  Const _   -> S.empty
  Read id   -> (S.singleton id)
  Add e1 e2 -> S.union (readSet e1) (readSet e2)

-- Declares variable 'id' in memory 'm'.
{-@ decl
 :: m:Mem
 -> id:Id
 -> m':{Mem | S.isSubsetOf (declSet m) (declSet m') && DeclP m' id} @-}
decl :: Mem -> Id -> Mem
decl m id = (id,Nothing):m

-- Writes value 'val' to variable 'id' in memory 'm'.
{-@ write
 :: m:Mem
 -> id:{Id | DeclP m id}
 -> val:Val
 -> m':{Mem | declSet m == declSet m' &&
              S.isSubsetOf (defnSet m) (defnSet m') &&
              DefnP m' id}
@-}
write :: Mem -> Id -> Val -> Mem
write m id val = case m of
  []                   -> liquidError "impossible"
  (x,y):xs | x == id   -> (x,Just val):xs
           | otherwise -> (x,y):(write xs id val)

-- Reads the value of variable 'id' in memory 'm'.
{-@ read
 :: m:Mem
 -> id:{Id | DefnP m id}
 -> Val
@-}
read :: Mem -> Id -> Val
read m id = case m of
  []                         -> liquidError "impossible"
  (x,Nothing):xs | x == id   -> liquidError "impossible"
                 | otherwise -> read xs id
  (x,Just y):xs  | x == id   -> y
                 | otherwise -> read xs id

-- Evaluates expression 'e' in memory 'm'.
{-@ eval
 :: e:Expr
 -> m:{Mem | S.isSubsetOf (readSet e) (defnSet m)}
 -> Val
@-}
eval :: Expr -> Mem -> Val
eval e m = case e of
  Const n   -> n
  Read id   -> read m id
  Add e1 e2 -> (eval e1 m) + (eval e2 m)

-- UNSAFE ------------------------------------------------------------------

{-@ reflect decl' @-}
decl' :: Mem -> Id -> Mem
decl' m id = (id,Nothing):m

{-@ reflect write' @-}
write' :: Mem -> Id -> Val -> Mem
write' m id val = case m of
  []                   -> m     -- error
  (x,y):xs | x == id   -> (x,Just val):xs
           | otherwise -> (x,y):(write' xs id val)

{-@ reflect read' @-}
read' :: Mem -> Id -> Val
read' m id = case m of
  []                         -> 0 -- error
  (x,Nothing):xs | x == id   -> 0 -- error
                 | otherwise -> read' xs id
  (x,Just y):xs  | x == id   -> y
                 | otherwise -> read' xs id

{-@ reflect eval' @-}
eval' :: Expr -> Mem -> Val
eval' e m = case e of
  Const n   -> n
  Read id   -> read' m id
  Add e1 e2 -> (eval' e1 m) + (eval' e2 m)

-- TESTS -------------------------------------------------------------------

{-@ mem_pass1 :: m:{Mem | not (DeclP m "x")} @-}
mem_pass1 :: Mem
mem_pass1 = []

{-@ mem_pass2 :: m:{Mem | DeclP m "x" && DefnP m "y"} @-}
mem_pass2 :: Mem
mem_pass2 = [("x",Just 1),("y",Just 2)]

{-@ decl_pass1 :: m:{Mem | DeclP m "x"} @-}
decl_pass1 = decl [] "x"

{-@ decl_pass2 :: m:{Mem | DeclP m "x" && DeclP m "y"} @-}
decl_pass2 = decl decl_pass1 "y"

write_pass1 = write (decl [] "x") "x" 5

{-@ write_pass2 :: m:{Mem | DeclP m "y"} @-}
write_pass2 :: Mem
write_pass2 = write (decl write_pass1 "y") "y" 4

{-@ write_pass3 :: m:{Mem | DeclP m "y"} @-}
write_pass3 = write (decl write_pass2 "x") "x" 3

{-@ write_pass4 :: m:{Mem | DefnP m "y"} @-}
write_pass4 = write write_pass3 "y" 2

-- write_fail1 = write [] "x" 5
-- write_fail2 = write (decl [] "y") "x" 5
-- write_fail3 = write write_pass3 "z" 2

read_pass1 = read mem_pass2 "y"
read_pass2 = read (write (decl [] "x") "x" 5) "x"
read_pass3 = read (write_pass4) "y"
read_pass4 = read (write (decl (decl (decl [] "x") "y") "z") "x" 5) "x"

-- read_fail1 = read [] "x"
-- read_fail2 = read (write (decl [] "x") "x" 5) "y"

eval_pass1 = eval (Const 0) []
eval_pass2 = eval (Add (Const 0) (Const 2)) []
eval_pass3 = eval (Read "x") [("x",Just 4)]
eval_pass4 = eval (Read "x") (write (decl [] "x") "x" 3)

-- eval_fail1 = eval (Add (Read "x") (Const 2)) []
-- eval_fail2 = eval (Read "x") (decl [] "x")
-- eval_fail3 = eval (Read "y") (write (decl [] "x") "x" 3)

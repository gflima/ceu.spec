{-@ LIQUID "--reflection" @-}

module Ceu.Expr () where

import Ceu.LH as LH
import qualified Ceu.Mem as M
import qualified Data.Set as S

type Val = M.Val
type Id = M.Id
type Mem = M.Mem

data Expr
  = Const Val
  | Read Id
  | Add Expr Expr
  deriving (Eq, Show)

{-@ measure readSet @-}
readSet :: Expr -> S.Set Id
readSet e = case e of
  Const _   -> S.empty
  Read id   -> (S.singleton id)
  Add e1 e2 -> S.union (readSet e1) (readSet e2)

{-@ eval
 :: e:Expr
 -> m:{Mem | S.isSubsetOf (readSet e) (M.defnSet m)}
 -> Val
@-}
eval :: Expr -> Mem -> Val
eval e m = case e of
  Const n   -> n
  Read id   -> M.read m id
  Add e1 e2 -> (eval e1 m) + (eval e2 m)

-- TESTS -------------------------------------------------------------------

eval_pass1 = eval (Const 0) []
eval_pass2 = eval (Add (Const 0) (Const 2)) []
eval_pass3 = eval (Read "x") [("x",Just 4)]
eval_pass4 = eval (Read "x") (M.write (M.decl [] "x") "x" 3)

-- eval_fail1 = eval (Add (Read "x") (Const 2)) []
-- eval_fail2 = eval (Read "x") (M.decl [] "x")

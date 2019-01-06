-- Required for deep pattern-matching over structured data.
{-@ LIQUID "--exact-data-cons" @-}

-- Required for reflection.
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Expr where

import Data.Maybe
import Data.Set
import Data.Tuple

type ID = String
type Val = Int
type Mem = [(ID, Maybe Val)]

data Expr
  = Read ID
  | Const Val
  | Add Expr Expr
  deriving (Eq, Show)

{-@ measure notReached :: {s:String | False} -> a @-}
notReached :: String -> a
notReached msg = error msg

-- FIXME: For some reason the standard lib versions do not work:

{-@ measure isJustS @-}
isJustS :: Maybe a -> Bool
isJustS Nothing  = False
isJustS (Just _) = True

{-@ measure lengthS @-}
lengthS :: [a] -> Int
lengthS [] = 0
lengthS (_:xs) = 1 + lengthS xs

----
-- Gets the set of variables referenced by expression.
--
{-@ measure exprVarSet @-}
exprVarSet :: Expr -> Set ID
exprVarSet (Read var)  = singleton var
exprVarSet (Add e1 e2) = union (exprVarSet e1) (exprVarSet e2)
exprVarSet _           = empty

----
-- Gets the set of variables declared in memory.
--
{-@ measure memDclSet @-}
memDclSet :: Mem -> Set ID
memDclSet []         = empty
memDclSet ((x,_):xs) = union (singleton x) (memDclSet xs)

---
-- Gets the set of variables defined in memory.
-- (Only the left-most occurrence of the variable is considered.)
--
{-@ measure memDefSet @-}
memDefSet :: Mem -> Set ID
memDefSet [] = empty
memDefSet ((x,y):xs)
  | isJustS y = union (singleton x) res
  | otherwise = difference res (singleton x)
  where res = memDefSet xs

{-@ predicate MemDcl M V = member V (memDclSet M) @-}
{-@ predicate MemDef M V = member V (memDefSet M) @-}

----
-- Writes value to variable in memory.
--
-- Pre: Variable is _declared_ in input memory.
-- Post: Variable is _defined_ in output memory.
--
{-@ memWrite
 :: m:Mem
 -> {v:ID | MemDcl m v || MemDef m v}
 -> Val
 -> {m':Mem | MemDef m' v}
@-}
memWrite :: Mem -> ID -> Val -> Mem
memWrite [] var val = notReached ("memWrite: undeclared variable: " ++ var)
memWrite ((x,y):xs) var val
  | x == var  = (x, Just val):xs
  | otherwise = (x,y):(memWrite xs var val)

----
-- Reads value of variable in memory.
--
-- Pre: Variable is _defined_ in input memory.
--
{-@ memRead
 :: m:Mem
 -> {v:ID | MemDef m v}
 -> Val
@-}
memRead :: Mem -> ID -> Val
memRead [] var = notReached ("memRead: undeclared variable: " ++ var)
memRead ((x,y):xs) var
  | x == var = if (isJustS y) then (fromJust y)
               else notReached ("memRead: undefined variable: " ++ var)
  | otherwise = memRead xs var

----
-- Evaluates expression in the given memory.
--
-- Pre: Variables referenced by expression are defined in memory.
--
-- NOTE: The assumption that all variables occurring in the expression are
-- defined rules out the possibility of short-circuits with invalid
-- components that do not execute.
--
{-@ memEval
 :: m:Mem
  -> {e:Expr | isSubsetOf (exprVarSet e) (memDefSet m)}
  -> Val
@-}
memEval :: Mem -> Expr -> Val
memEval mem expr = case expr of
  Read var  -> memRead mem var
  Const val -> val
  Add e1 e2 -> memEval mem e1 + memEval mem e2

-- Tests -------------------------------------------------------------------

{-@ expr1 :: {e:Expr | exprVarSet e == empty} @-}
expr1 :: Expr
expr1 = Const 0

{-@ expr2 :: {e:Expr | exprVarSet e == singleton "x"} @-}
expr2 :: Expr
expr2 = Read "x"

{-@ expr3 ::
{e:Expr | exprVarSet e == (union (singleton"x") (singleton "y"))} @-}
expr3 :: Expr
expr3 = (Add (Read "x") (Add (Read "y") (Const 1)))

{-@ mem1 :: {m:Mem | MemDef m "x" && MemDef m "y" } @-}
mem1 :: Mem
mem1 = [("x",Just 1),("y",Just 2)]

{-@ mem2 :: {m:Mem | MemDcl m "x" && not (MemDef m "x")} @-}
mem2 :: Mem
mem2 = [("x",Nothing),("x",Just 1)]

{-@ mem3 :: {m:Mem | MemDef m "x"} @-}
mem3 :: Mem
mem3 = [("x",Just 3),("x",Nothing),("x",Just 1)]

{-@ mem4 :: {m:Mem | MemDef m "x" && MemDcl m "y" && not (MemDef m "y")} @-}
mem4 :: Mem
mem4 = [("x", Just 1),("y",Nothing),("y",Just 2)]

mem5 = memWrite mem3 "x" 8
--mem5_fail = memWrite mem3 "y" 0

mem6 = memWrite mem4 "y" 5
--mem6_fail = memWrite mem4 "z" 5

mem7 = memRead mem3 "x"
--mem7_fail = memRead mem3 "y"

mem8 = memRead mem4 "x"
-- mem8_fail = memRead mem4 "y"

mem9 = memRead (memWrite [("x",Nothing)] "x" 1) "x"

mem10 = memEval mem3 (Add (Read "x") (Const 1))
-- mem10_fail = memEval mem3 (Add (Read "x") (Read "y"))

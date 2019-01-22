{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--reflection" @-}

module Ceu.Expr () where
import Ceu.LH as LH
import Data.Maybe
import Data.List

type Id = String
type Val = Int

-- Memory.
type Mem = [(Id, Maybe Val)]

-- Expression.
data Expr
  = Const Int
  | Read Id
  | Umn Expr
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  deriving (Eq, Show)

{-@ measure memSize @-}
{-@ memSize :: Mem -> Nat @-}
memSize :: Mem -> Int
memSize m = case m of
  []   -> 0
  _:xs -> 1 + memSize xs

{-@ reflect memEmpty @-}
memEmpty = []

{-@ type MemEmpty = {m:Mem | memSize m == 0} @-}
{-@ type MemNonEmpty = {m:Mem | memSize m > 0} @-}

{-@ reflect memGetDecl @-}
memGetDecl :: Mem -> Id -> Mem
memGetDecl m id = case m of
  []                   -> []
  (x,y):xs | x == id   -> m
           | otherwise -> memGetDecl xs id

{-@ reflect memIsDecl @-}
memIsDecl m id = memGetDecl m id /= memEmpty

-- {-@ reflect memIsDefn @-}
-- memIsDefn :: Mem -> Id -> Bool
-- memIsDefn m id = case m of
--   []                   -> False
--   (x,y):xs | x == id   -> LH.isJust y
--            | otherwise -> memIsDefn xs id

-- {-@ memWrite
--  :: m:MemNonEmpty
--  -> id:{Id | memIsDecl m id}
--  -> Val
--  -> MemNonEmpty
-- @-}
-- memWrite :: Mem -> Id -> Val -> Mem
-- memWrite m id val = case m of
--   [] -> liquidError "impossible"
--   (x,y):xs | x == id   -> (x,Just val):xs
--            | otherwise -> (x,y):(memWrite xs id val)

-- LEMMAS ------------------------------------------------------------------

{-@ lem_memIsDecl1
 :: m:MemEmpty
 -> id:Id
 -> {not (memIsDecl m id)}
@-}
lem_memIsDecl1 :: Mem -> Id -> Proof
lem_memIsDecl1 m id = case m of
  [] -> memIsDecl m id
        === memIsDecl memEmpty id
        === memGetDecl memEmpty id /= []
        === False
        *** QED
  _  -> impossible *** QED


-- {-@ lem_memIsDecl2
--  :: m:Mem
--  -> id:{Id | memIsDecl m id}
--  -> {id == fst (head m) || memSize (memGetDecl m id) > 1}
-- @-}
-- lem_memIsDecl2 :: Mem -> Id -> Proof
-- lem_memIsDecl2 m id = case m of
--   []
--     -> impossible ? lem_memIsDecl1 m id
--        *** QED

--   (x,y):xs
--     | id == x
--       -> memSize (memGetDecl m id)
--          === memSize m
--          =>= 0
--          *** QED

--     | otherwise
--       -> memSize (memGetDecl m id)
--          === memSize (memGetDecl xs id) ? lem_memIsDecl2 xs id
--          =>= 0
--          *** QED

-- {-@ lem_memIsDecl
--  :: m:MemNonEmpty
--  -> id:{Id | memIsDecl m id}
--  -> {id == fst (head m) || ((tail m) /= memEmpty && memIsDecl (tail m) id)}
-- @-}
-- lem_memIsDecl :: Mem -> Id -> Proof
-- lem_memIsDecl m id = case m of
--   []
--     -> impossible
--        *** QED

--   (x,y):xs
--     | x == id
--       -> trivial
--          *** QED

--     | otherwise
--       -> memIsDecl (tail m) id
--          === memIsDecl xs id
--          === memIsDecl ((x,y):xs) id
--          *** QED

-- {-@ lem_memIsDefn
--  :: m:MemNonEmpty
--  -> id:{Id | memIsDefn m id}
--  -> {m /= memEmpty && (fst (head m) == id || memIsDefn (tail m) id)}
-- @-}
-- lem_memIsDefn :: Mem -> Id -> Proof
-- lem_memIsDefn m id = case m of
--   []
--     -> impossible
--        *** QED

--   (x,y):xs
--     | x == id
--       -> trivial
--          *** QED

--     | otherwise
--       -> memIsDefn (tail m) id
--          === memIsDefn xs id
--          === memIsDefn ((x,y):xs) id
--          *** QED

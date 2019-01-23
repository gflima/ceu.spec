{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--reflection" @-}

module Ceu.Expr () where

import Ceu.LH as LH
import Data.Maybe
import Data.Set hiding (size)
import Prelude hiding (read)

type Id = String
type Val = Int

-- Memory.
type Mem = [(Id, Maybe Val)]

-- Expression.
data Expr
  = Const Int
  | Read Id
  | Add Expr Expr
  deriving (Eq, Show)

-- Gets the size of memory 'm'.
{-@ measure size @-}
{-@ size :: Mem -> Nat @-}
size :: Mem -> Int
size m = case m of
  []   -> 0
  _:xs -> 1 + size xs

-- The empty memory.
{-@ reflect memEmpty @-}
memEmpty :: Mem
memEmpty = []

{-@ type MemEmpty = {m:Mem | size m == 0} @-}
{-@ type MemNonEmpty = {m:Mem | size m > 0} @-}

-- Gets the set of variables declared in memory 'm'.
{-@ measure declSet @-}
declSet :: Mem -> Set Id
declSet m = case m of
  []         -> empty
  ((x,_):xs) -> union (singleton x) (declSet xs)

-- Gets the set of variables defined in memory 'm'.
-- (Only the left-most occurrence of each variable is considered.)
{-@ measure defnSet @-}
defnSet :: Mem -> Set Id
defnSet m = case m of
  []                       -> empty
  ((x,y):xs) | LH.isJust y -> union (singleton x) (defnSet xs)
             | otherwise   -> difference (defnSet xs) (singleton x)

{-@ predicate MemDecl M V = member V (declSet M) @-}
{-@ predicate MemDefn M V = member V (defnSet M) @-}

-- Reads value of variable 'id' in memory 'm'.
-- * Pre: Variable 'id' is defined in memory 'm'.
-- * Post: Returns a 'Just' with a value.
{-@ reflect read' @-}
{-@ read'
 :: m:Mem
 -> id:{Id | MemDefn m id}
 -> val:{Maybe Val | isJust val}
@-}
read' :: Mem -> Id -> Maybe Val
read' m id = case m of
  []                         -> Nothing -- impossible
  (x,Nothing):xs | x == id   -> Nothing -- impossible
                 | otherwise -> read' xs id
  (x,Just y):xs  | x == id   -> Just y
                 | otherwise -> read' xs id

-- Writes value 'val' to variable 'id' in memory 'm'.
-- * Pre: Variable 'id' is declared in memory 'm'.
-- * Post: Variable 'id' is defined in the returned memory.
{-@ write'
 :: m:Mem
 -> {id:Id | MemDecl m id || MemDefn m id}
 -> Val
 -> {m':Mem | MemDefn m' id && size m > 0}
@-}
write' :: Mem -> Id -> Val -> Mem
write' m id val = case m of
  []                   -> [] -- impossible
  (x,y):xs | x == id   -> (x, Just val):xs
           | otherwise -> (x,y):(write' xs id val)

-- Safe read.
{-@ read
 :: m:Mem
 -> id:{Id | MemDefn m id}
 -> Val
@-}
read m id
  | val == Nothing = liquidError "impossible"
  | otherwise      = fromJust val
  where val = read' m id

-- Safe write.
{-@ write
 :: m:Mem
 -> id:{Id | MemDecl m id || MemDefn m id}
 -> Val
 -> {m':Mem | MemDefn m' id}
@-}
write :: Mem -> Id -> Val -> Mem
write m id val = write' m id val


-- LEMMAS ------------------------------------------------------------------

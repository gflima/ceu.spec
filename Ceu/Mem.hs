{-@ LIQUID "--reflection" @-}

module Ceu.Mem () where

import Ceu.LH as LH

type Id = String
type Val = Int
type Bind = (Id,Maybe Val)
type Mem = [Bind]

{-@ type MemEmpty = {m:Mem | m == []} @-}
{-@ type MemNonEmpty = {m:Mem | m /= []} @-}

{-@ reflect isDeclared @-}
isDeclared :: Mem -> Id -> Bool
isDeclared m id = case m of
  []                   -> False
  (x,_):xs | x == id   -> True
           | otherwise -> isDeclared xs id

{-@ reflect isDefined @-}
isDefined :: Mem -> Id -> Bool
isDefined m id = case m of
  []                         -> False
  (x,Nothing):xs | x == id   -> False
                 | otherwise -> isDefined xs id
  (x,Just _):xs  | x == id   -> True
                 | otherwise -> isDefined xs id

{-@ reflect isDefinedWithValue @-}
isDefinedWithValue :: Mem -> Id -> Val -> Bool
isDefinedWithValue m id val = case m of
  []                         -> False
  (x,Nothing):xs | x == id   -> False
                 | otherwise -> isDefined xs id
  (x,Just y):xs  | x == id   -> y == val
                 | otherwise -> isDefined xs id

{-@ reflect declare' @-}
{-@ declare'
 :: m:Mem
 -> id:Id
 -> m':{Mem | len m' > len m && fst (head m') == id} @-}
declare' :: Mem -> Id -> Mem
declare' m id = (id,Nothing):m

{-@ declare :: m:Mem -> id:Id -> m':{Mem | isDeclared m' id} @-}
declare :: Mem -> Id -> Mem
declare m id = m' ? lem_declare m id m'
  where m' = declare' m id

{-@ reflect write' @-}
write' :: Mem -> Id -> Val -> Mem
write' m id val = case m of
  []                   -> []    -- impossible
  (x,y):xs | x == id   -> (x,Just val):xs
           | otherwise -> (x,y):(write' xs id val)

{-@ write
 :: m:Mem
 -> id:{Id | isDeclared m id}
 -> Val
 -> m':{Mem | isDeclared m' id}
@-}
write :: Mem -> Id -> Val -> Mem
write m id val = m' ? lem_write m id val m'
  where m' = write' m id val

-- LEMMAS ------------------------------------------------------------------

{-@ lem_isDeclared
 :: m:MemNonEmpty
 -> id:{Id | isDeclared m id}
 -> {isDeclared [head m] id || (tail m /= [] && isDeclared (tail m) id)}
@-}
lem_isDeclared :: Mem -> Id -> Proof
lem_isDeclared m id = case m of
  []
    -> impossible
       *** QED

  (x,y):xs
    | x == id
      -> isDeclared m id
         === isDeclared ((x,y):xs) id
         === isDeclared ((x,y):[]) id
         === isDeclared (head m:[]) id
         *** QED

    | xs == []
      -> impossible
         *** QED

    | otherwise
      -> isDeclared m id
         === isDeclared xs id
         *** QED

{-@ lem_declare
 :: m:Mem
 -> id:Id
 -> m':{Mem | m' == declare' m id}
 -> {isDeclared m' id}
@-}
lem_declare :: Mem -> Id -> Mem -> Proof
lem_declare m id m'
  = let x = (id,Nothing) in
      isDeclared m' id
      === isDeclared (declare' m id) id
      === isDeclared (x:m) id
      *** QED

{-@ lem_isDeclaredImpNonEmpty
 :: m:Mem
 -> id:{Id | isDeclared m id}
 -> {m /= []}
@-}
lem_isDeclaredImpNonEmpty :: Mem -> Id -> Proof
lem_isDeclaredImpNonEmpty m id = case m of
  []
    -> isDeclared m id
       === m /= []
       *** QED

  x:xs
    -> isDeclared m id
       === m /= []
       *** QED

{-@ lem_write
 :: m:Mem
 -> id:{Id | isDeclared m id}
 -> val:Val
 -> m':{Mem | m' == write' m id val}
 -> {isDeclared m' id && len m' > 0}
@-}
lem_write :: Mem -> Id -> Val -> Mem -> Proof
lem_write m id val m' = case m of
  []
    -> impossible ? lem_isDeclaredImpNonEmpty m id
       *** QED

  (x,y):xs
    | x == id
      -> isDeclared m' id
         === isDeclared (write' m id val) id
         === isDeclared ((x,Just val):xs) id
         *** QED

    | otherwise
      -> isDeclared m id
         === isDeclared ((x,y):xs) id
         === isDeclared xs id
             ? lem_isDeclaredImpNonEmpty xs id
             ? lem_write xs id val (write' xs id val)
         === isDeclared (write' xs id val) id
         === isDeclared ((x,y):(write' xs id val)) id
         === isDeclared (write' ((x,y):xs) id val) id
         === isDeclared m' id
         *** QED

-- TESTS -------------------------------------------------------------------

write_pass1 = write (declare [] "x") "x" 5
-- write_fail1 = write [] "x" 5
-- write_fail2 = write (declare [] "y") "x" 5

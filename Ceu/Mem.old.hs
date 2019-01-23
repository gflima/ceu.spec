{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

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
                 | otherwise -> isDefinedWithValue xs id val
  (x,Just y):xs  | x == id   -> y == val
                 | otherwise -> isDefinedWithValue xs id val

{-@ predicate IsDeclaredP M ID = len M > 0 && M /= [] && isDeclared M ID @-}
{-@ predicate IsDefinedP M ID = IsDeclaredP M ID && isDefined M ID @-}
{-@ predicate IsDefinedWithValueP M ID VAL
    = IsDefinedP M ID && isDefinedWithValue M ID VAL @-}

{-@ reflect declare' @-}
{-@ declare'
 :: m:Mem
 -> id:Id
 -> m':{Mem | len m' > len m && fst (head m') == id} @-}
declare' :: Mem -> Id -> Mem
declare' m id = (id,Nothing):m

{-@ declare :: m:Mem -> id:Id -> m':{Mem | IsDeclaredP m' id} @-}
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
 -> id:{Id | IsDeclaredP m id}
 -> val:Val
 -> m':{Mem | IsDefinedWithValueP m' id val}
@-}
write :: Mem -> Id -> Val -> Mem
write m id val = m' ? lem_write m id val m'
  where m' = write' m id val

-- LEMMAS ------------------------------------------------------------------

{-@ lem_isDeclared
 :: m:Mem
 -> id:{Id | isDeclared m id}
 -> {isDeclared [head m] id || isDeclared (tail m) id}
@-}
lem_isDeclared :: Mem -> Id -> Proof
lem_isDeclared m id = case m of
  []
    -> impossible ? lem_isDeclaredImpNonEmpty m id
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

{-@ lem_isDeclaredImpNonEmpty
 :: m:Mem
 -> id:{Id | isDeclared m id}
 -> {m /= []}
@-}
lem_isDeclaredImpNonEmpty :: Mem -> Id -> Proof
lem_isDeclaredImpNonEmpty m id
  = isDeclared m id
    === m /= []
    *** QED

{-@ lem_isDefinedImpNonEmpty
 :: m:Mem
 -> id:{Id | isDefined m id}
 -> {m /= []}
@-}
lem_isDefinedImpNonEmpty :: Mem -> Id -> Proof
lem_isDefinedImpNonEmpty m id
  = isDefined m id
    === m /= []
    *** QED

{-@ lem_isDefinedWithValueImpNonEmpty
 :: m:Mem
 -> id:Id
 -> val:{Val | isDefinedWithValue m id val}
 -> {m /= []}
@-}
lem_isDefinedWithValueImpNonEmpty :: Mem -> Id -> Val -> Proof
lem_isDefinedWithValueImpNonEmpty m id val
  = isDefinedWithValue m id val
    === m /= []
    *** QED

{-@ lem_isDefinedImpIsDeclared
 :: m:Mem
 -> id:{Id | isDefined m id}
 -> {isDeclared m id}
@-}
lem_isDefinedImpIsDeclared :: Mem -> Id -> Proof
lem_isDefinedImpIsDeclared m id = case m of
  []
    -> impossible ? lem_isDefinedImpNonEmpty m id
       *** QED

  (x,y):xs
    | x == id
      -> isDefined m id
         === isDeclared m id
         *** QED

    | otherwise
      -> isDefined m id
         === isDefined xs id ? lem_isDefinedImpIsDeclared xs id
         === isDeclared xs id
         === isDeclared ((x,y):xs) id
         === isDeclared m id
         *** QED

{-@ lem_isDefinedWithValueImpIsDefined
 :: m:Mem
 -> id:Id
 -> val:{Val | isDefinedWithValue m id val}
 -> {isDefined m id}
@-}
lem_isDefinedWithValueImpIsDefined :: Mem -> Id -> Val -> Proof
lem_isDefinedWithValueImpIsDefined m id val = case m of
  []
    -> impossible ? lem_isDefinedWithValueImpNonEmpty m id val
       *** QED

  (x,y):xs
    | x == id
      -> isDefinedWithValue m id val
         === isDefined m id
         *** QED

    | otherwise
      -> isDefinedWithValue m id val
         === isDefinedWithValue xs id val
             ? lem_isDefinedWithValueImpIsDefined xs id val
         === isDefined xs id
         === isDefined ((x,y):xs) id
         === isDefined m id
         *** QED

{-@ lem_declare
 :: m:Mem
 -> id:Id
 -> m':{Mem | m' == declare' m id}
 -> {IsDeclaredP m' id}
@-}
lem_declare :: Mem -> Id -> Mem -> Proof
lem_declare m id m'
  = isDeclared m' id
    === isDeclared (declare' m id) id
    === isDeclared ((id,Nothing):m) id ? lem_isDeclaredImpNonEmpty m' id
    *** QED

-- {-@ lem_write
--  :: m:Mem
--  -> id:{Id | isDeclared m id}
--  -> val:Val
--  -> m':{Mem | m' == write' m id val}
--  -> {isDeclared m' id && len m' > 0}
-- @-}
-- lem_write :: Mem -> Id -> Val -> Mem -> Proof
-- lem_write m id val m' = case m of
--   []
--     -> impossible ? lem_isDeclaredImpNonEmpty m id
--        *** QED

--   (x,y):xs
--     | x == id
--       -> isDeclared ((x,Just val):xs) id
--          === isDeclared (write' m id val) id
--          === isDeclared m' id
--          *** QED

--     | otherwise
--       -> isDeclared m id
--          === isDeclared ((x,y):xs) id
--          === isDeclared xs id
--              ? lem_isDeclaredImpNonEmpty xs id
--              ? lem_write xs id val (write' xs id val)
--          === isDeclared (write' xs id val) id
--          === isDeclared ((x,y):(write' xs id val)) id
--          === isDeclared (write' ((x,y):xs) id val) id
--          === isDeclared m' id
--          *** QED

-- {-@ lem_write
--  :: m:Mem
--  -> id:{Id | isDeclared m id}
--  -> val:Val
--  -> m':{Mem | m' == write' m id val}
--  -> {isDeclared m' id && isDefined m' id && len m' > 0}
-- @-}
-- lem_write :: Mem -> Id -> Val -> Mem -> Proof
-- lem_write m id val m' = case m of
--   []
--     -> impossible ? lem_isDeclaredImpNonEmpty m id
--        *** QED

--   (x,y):xs
--     | x == id
--       -> isDefined ((x,Just val):xs) id
--          === isDefined (write' m id val) id
--          === isDefined m' id ? lem_isDefinedImpIsDeclared m' id
--          *** QED

--     | otherwise
--       -> isDeclared m id
--          === isDeclared ((x,y):xs) id
--          === isDeclared xs id
--              ? lem_isDeclaredImpNonEmpty xs id
--              ? lem_write xs id val (write' xs id val)
--          === isDefined (write' xs id val) id
--          === isDefined ((x,y):(write' xs id val)) id
--          === isDefined (write' ((x,y):xs) id val) id
--          === isDefined m' id ? lem_isDefinedImpIsDeclared m' id
--          *** QED

{-@ lem_write
 :: m:Mem
 -> id:{Id | isDeclared m id}
 -> val:Val
 -> m':{Mem | m' == write' m id val}
 -> {IsDefinedWithValueP m' id val}
@-}
lem_write :: Mem -> Id -> Val -> Mem -> Proof
lem_write m id val m' = case m of
  []
    -> impossible ? lem_isDeclaredImpNonEmpty m id
       *** QED

  (x,y):xs
    | x == id
      -> isDefinedWithValue ((x,Just val):xs) id val
         === isDefinedWithValue (write' m id val) id val
         === isDefinedWithValue m' id val
         === isDefined m' id
         === isDeclared m' id
             ? lem_isDefinedImpIsDeclared m' id
             ? lem_isDeclaredImpNonEmpty m' id
         *** QED

    | otherwise
      -> isDeclared m id
         === isDeclared ((x,y):xs) id
         === isDeclared xs id
             ? lem_isDeclaredImpNonEmpty xs id
             ? lem_write xs id val (write' xs id val)
         === isDefinedWithValue (write' xs id val) id val
         === isDefinedWithValue ((x,y):(write' xs id val)) id val
         === isDefinedWithValue (write' ((x,y):xs) id val) id val
         === isDefined m' id
             ? lem_isDefinedImpIsDeclared m' id
             ? lem_isDeclaredImpNonEmpty m' id
         *** QED

-- TESTS -------------------------------------------------------------------

-- TODO: Declarations/definitions must be preserved from input to output.

{-@ write_pass1 :: m:{Mem | isDeclared m "x"} @-}
write_pass1 :: Mem
write_pass1 = declare [] "x"

-- write_pass2 :: Mem
-- write_pass2 = write (declare write_pass1 "y") "y" 4

-- write_pass3 :: Mem
-- write_pass3 = write (declare write_pass2 "x") "x" 3

-- write_pass4 :: Mem
-- write_pass4 = write write_pass3 "y" 2 ? isDeclared write_pass3 "y"

-- write_fail1 = write [] "x" 5
-- write_fail2 = write (declare [] "y") "x" 5

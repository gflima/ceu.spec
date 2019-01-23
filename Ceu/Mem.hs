{-@ LIQUID "--reflection" @-}

module Ceu.Mem where

import Ceu.LH as LH
import Prelude hiding (read)
import qualified Data.Set as S

type Id = String
type Val = Int
type Mem = [(Id,Maybe Val)]

{-@ type MemEmpty = {m:Mem | m == []} @-}
{-@ type MemNonEmpty = {m:Mem | m /= []} @-}

{-@ measure declSet @-}
declSet :: Mem -> S.Set Id
declSet m = case m of
  []       -> S.empty
  (x,_):xs -> S.union (S.singleton x) (declSet xs)

{-@ measure defnSet @-}
defnSet :: Mem -> S.Set Id
defnSet m = case m of
  []                     -> S.empty
  (x,y):xs | LH.isJust y -> S.union (S.singleton x) (defnSet xs)
           | otherwise   -> S.difference (defnSet xs) (S.singleton x)

{-@ predicate DeclP M ID = member ID (declSet M) @-}
{-@ predicate DefnP M ID = member ID (defnSet M) @-}

{-@ decl
 :: m:Mem
 -> id:Id
 -> m':{Mem | S.isSubsetOf (declSet m) (declSet m') && DeclP m' id} @-}
decl :: Mem -> Id -> Mem
decl m id = (id,Nothing):m

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

-- TESTS -------------------------------------------------------------------

{-@ mem_pass1 :: m:{Mem | DeclP m "x" && DefnP m "y"} @-}
mem_pass1 :: Mem
mem_pass1 = [("x",Just 1),("y",Just 2)]

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

read_pass1 = read mem_pass1 "y"
read_pass2 = read (write (decl [] "x") "x" 5) "x"
read_pass3 = read (write_pass4) "y"
read_pass4 = read (write (decl (decl (decl [] "x") "y") "z") "x" 5) "x"

-- read_fail1 = read [] "x"
-- read_fail2 = read (write (decl [] "x") "x" 5) "y"

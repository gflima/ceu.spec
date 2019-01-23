module Ceu.LH
  (liquidAssert,
   liquidError,
   Proof,
   QED(..),
   impossible,
   trivial,
   (===),
   (=<=),
   (=>=),
   (***),
   (?),
   min,
   max,
   isJust
  ) where

import Prelude hiding (min, max)
import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators

{-@ inline min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y

{-@ inline max @-}
max :: Int -> Int -> Int
max x y = if x <= y then y else x

{-@ measure isJust @-}
isJust :: Maybe a -> Bool
isJust Nothing  = False
isJust (Just _) = True

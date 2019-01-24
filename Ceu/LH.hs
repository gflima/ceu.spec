{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

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
   min',
   max',
   isJust',
   fromJust',
   fst',
   snd'
  ) where

import Prelude hiding (min, max)
import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators

{-@ inline min' @-}
min' :: Int -> Int -> Int
min' x y = if x <= y then x else y

{-@ inline max' @-}
max' :: Int -> Int -> Int
max' x y = if x <= y then y else x

{-@ measure isJust' @-}
isJust' :: Maybe a -> Bool
isJust' Nothing  = False
isJust' (Just _) = True

{-@ measure fromJust' @-}
{-@ fromJust' :: v:{Maybe a | isJust' v} -> a @-}
fromJust' :: Maybe a -> a
fromJust' (Just x) = x

{-@ measure fst' @-}
fst' :: (a,b) -> a
fst' (x,_) = x

{-@ measure fst' @-}
snd' :: (a,b) -> b
snd' (_,y) = y

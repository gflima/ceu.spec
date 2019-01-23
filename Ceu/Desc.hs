{-@ LIQUID "--reflection" @-}

module Ceu.Desc where

import Ceu.Expr
import Ceu.LH as LH
import Ceu.Stmt
import Debug.Trace

-- Description.
type Desc = (Stmt,Mem)

{-@ inline nstMayExhaust @-}
nstMayExhaust :: Desc -> Bool
nstMayExhaust (x,_) = mayExhaust x

{-@ inline isNstIrreducible @-}
isNstIrreducible :: Desc -> Bool
isNstIrreducible (x,_) = isIrreducible x

{-@ type DescNstIrreducible = {d:Desc | isNstIrreducible d} @-}
{-@ type DescNotNstIrreducible = {d:Desc | not (isNstIrreducible d)} @-}

{-@ measure nstRank @-}
{-@ nstRank :: Desc -> {i:Int | i > 0} @-}
nstRank :: Desc -> Int
nstRank (x,m) = rank x

{-@ reflect nst1 @-}
{-@ nst1
 :: d:DescNotNstIrreducible
 -> d':Desc
  / [nstRank d]
@-}
nst1 :: Desc -> Desc
nst1 (x,m) = case x of
  Write id e            -> (Nop, write' m id (eval' e m))

  If b p q
    | b                 -> (p,m)
    | otherwise         -> (q,m)

  Seq p q
    | p == Nop          -> (q,m)
    | p == Break        -> (Break, m)
    | otherwise         -> let (p',m') = nst1 (p,m) in (Seq p' q, m')

  Loop p q
    | p == Nop          -> (Loop q q, m)
    | p == Break        -> (Nop, m)
    | otherwise         -> let (p',m') = nst1 (p,m) in (Loop p' q, m')

  ParOr p q
    | p == Nop          -> (Seq (clear q) Nop, m)
    | p == Break        -> (Seq (clear q) Break, m)
    | not (isBlocked p) -> let (p',m') = nst1 (p,m) in (ParOr p' q, m')
    | q == Nop          -> (Seq (clear p) Nop, m)
    | q == Break        -> (Seq (clear p) Break, m)
    | not (isBlocked q) -> let (q',m') = nst1 (q,m) in (ParOr p q', m')
    | otherwise         -> (x,m) -- impossible
  _                     -> (x,m) -- impossible

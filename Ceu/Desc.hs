{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-} -- required by the lemmas!

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

-- Nested transition.
-- FIXME: The Var rule with reflection on is crashing LH
-- (revision 57213512a9d69093c12d644b21dbf9da95811894).
{-@ reflect nst1 @-}
{-@ nst1
 :: d:DescNotNstIrreducible
 -> d':{Desc | mayExhaust (fst d') => mayExhaust (fst d)}
  / [nstRank d]
@-}
nst1 :: Desc -> Desc
nst1 (x,m) = case x of
  Write id e            -> (Nop, write' m id (eval' e m))

  (Var id val p)
    | p == Nop          -> (Nop, m)
    | p == Break        -> (Break, m)
    | otherwise         -> let (p',m') = nst1 (p,m) -- FIXME: (p,(id,val):m)
                           in case m' of
                                []           -> (x,m) -- impossible
                                (_,val'):m'' -> (Var id val' p', m'')
    | otherwise         -> (Nop, m)

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

-- -- Safe version of 'nst1'.
-- {-@ nst
--  :: d:DescNotNstIrreducible
--  -> d':{Desc | nstRank d > nstRank d'}
-- @-}
-- nst d = let d' = nst1 d in d' ? lem_nst1DecreasesRank d d'

-- -- Transitive closure of 'nst'.
-- {-@ nstPlus
--  :: d:DescNotNstIrreducible
--  -> d':DescNstIrreducible
--   / [nstRank d]
-- @-}
-- nstPlus :: Desc -> Desc
-- nstPlus d
--   | isNstIrreducible d = liquidError "impossible"
--   | otherwise = let d' = nst d
--                     s  = show d  ++ " <" ++ show (nstRank d)  ++ ">"
--                     s' = show d' ++ " <" ++ show (nstRank d') ++ ">"
--     in trace (s ++ " -> " ++ s')
--        $ if isNstIrreducible d' then d' else nstPlus d'


-- LEMMAS ------------------------------------------------------------------

-- {-@ lem_nst1DecreasesRank
--  :: d:DescNotNstIrreducible
--  -> d':{Desc | d' == nst1 d}
--  -> {nstRank d > nstRank d'}
--   / [nstRank d]
-- @-}
-- lem_nst1DecreasesRank :: Desc -> Desc -> Proof
-- lem_nst1DecreasesRank d d' = case d of
--   (Nop, _)
--     -> impossible               -- d is not nst-irreducible
--        *** QED

--   (Write _ _, _)
--     -> nstRank d'
--        === nstRank (nst1 d)
--        === nstRank (Nop, snd d')
--        =<= nstRank d
--        *** QED

--   (Break, _)
--     -> impossible               -- d is not nst-irreducible
--        *** QED

--   (If b p q, _)
--     | b == True
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (p, snd d')
--          =<= nstRank d
--          *** QED

--     | otherwise
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (q, snd d')
--          =<= nstRank d
--          *** QED

--   (Seq p q, m)
--     | p == Nop
--       -> nstRank d'
--          === nstRank (nst1 d)
--          =<= nstRank d
--          *** QED

--     | p == Break
--       -> nstRank d'
--          === nstRank (nst1 d)
--          =<= nstRank d
--          *** QED

--     | otherwise
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Seq (fst $ nst1 (p,m)) q, snd $ nst1 (p,m))
--          =<= 1 + nstRank (nst1 (p,m)) + nstRank (q,m)
--              ? lem_nst1DecreasesRank (p,m) (nst1 (p,m))
--          =<= nstRank d
--          *** QED

--   (Loop p q, m)
--     | p == Nop
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Loop q q, m)
--          =<= nstRank d
--          *** QED

--     | p == Break
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Nop, m)
--          =<= nstRank d
--          *** QED

--     | not (mayExhaust p)
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Loop (fst $ nst1 (p,m)) q, snd $ nst1 (p,m))
--          === 1 + nstRank (nst1 (p,m))
--              ? lem_nst1DecreasesRank (p,m) (nst1 (p,m))
--          =<= nstRank d
--          *** QED

--     | otherwise
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Loop (fst $ nst1 (p,m)) q, snd $ nst1 (p,m))
--          =<= 1 + nstRank (nst1 (p,m)) + nstRank (q,m)
--              ? lem_nst1DecreasesRank (p,m) (nst1 (p,m))
--          =<= nstRank d
--          *** QED

--   (ParOr p q, m)
--     | p == Nop
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Seq (clear q) Nop, m)
--          =<= nstRank d
--          *** QED

--     | p == Break
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Seq (clear q) Break, m)
--          =<= nstRank d
--          *** QED

--     | not (isBlocked p)
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (ParOr (fst $ nst1 (p,m)) q, snd $ nst1 (p,m))
--              ? lem_nst1DecreasesRank (p,m) (nst1 (p,m))
--          =<= nstRank d
--          *** QED

--     | q == Nop
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Seq (clear p) Nop, m)
--          =<= nstRank d
--          *** QED

--     | q == Break
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (Seq (clear p) Break, m)
--          =<= nstRank d
--          *** QED

--     | not (isBlocked q)
--       -> nstRank d'
--          === nstRank (nst1 d)
--          === nstRank (ParOr p (fst $ nst1 (q,m)), snd $ nst1 (q,m))
--              ? lem_nst1DecreasesRank (q,m) (nst1 (q,m))
--          =<= nstRank d
--          *** QED

--     | otherwise
--       -> impossible
--          *** QED
--   _
--     -> impossible
--        *** QED

-- TESTS -------------------------------------------------------------------

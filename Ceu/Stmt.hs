{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Ceu.Stmt where

import Ceu.Expr (Expr, Id, Val)
import Ceu.LH as LH
import Debug.Trace

-- Statement.
-- * Function 'rank' is the default termination measure.
-- * 'Fin' body must not contain 'Loop', 'Break', 'Await', or 'Fin'.
-- * 'Loop' body must always reach a 'Break', 'Await', or 'Fin'.
{-@
data Stmt [rank]
  = Nop
  | Write {write1 :: Id, write2 :: Expr}
  | Var {var1 :: Id, var2 :: Maybe Val, var3 :: Stmt}
  | Break
  | Await
  | Fin {fin1 :: {p:Stmt | isWellFormedFinBody p}}
  | If {if1 :: Bool, if2 :: Stmt, if3 :: Stmt}
  | Seq {seq1 :: Stmt, seq2 :: Stmt}
  | Loop {loop1 :: Stmt, loop2 :: {p:Stmt | isWellFormedLoopBody p}}
  | ParOr {parOr1 :: Stmt, parOr2 :: Stmt}
@-}
data Stmt
  = Nop
  | Write Id Expr
  | Var Id (Maybe Val) Stmt
  | Break
  | Await
  | Fin Stmt
  | If Bool Stmt Stmt
  | Seq Stmt Stmt
  | Loop Stmt Stmt
  | ParOr Stmt Stmt
  | ParAnd Stmt Stmt
  deriving (Eq, Show)

-- Tests whether 'x' is a well-formed fin body, i.e., if 'x' does not
-- contain a Loop, Break, Await, or Fin.
{-@ measure isWellFormedFinBody @-}
isWellFormedFinBody x = case x of
  Nop       -> True
  Write _ _ -> True
  Var _ _ p -> isWellFormedFinBody p
  Break     -> False
  Await     -> False
  Fin _     -> False
  If _ p q  -> isWellFormedFinBody p && isWellFormedFinBody q
  Seq p q   -> isWellFormedFinBody p && isWellFormedFinBody q
  Loop _ _  -> False
  ParOr p q -> isWellFormedFinBody p && isWellFormedFinBody q

-- Tests whether 'x' is a well-formed loop body, i.e., if every execution
-- path in 'x' reaches a 'Break', 'Await', or 'Fin'.
{-@ inline isWellFormedLoopBody @-}
isWellFormedLoopBody x = not (mayExhaust x)

-- Tests whether 'x' may exhaust, i.e., if 'x' may run to completion without
-- ever executing a 'Break', 'Await', or 'Fin'.  Here we do a crude
-- analysis.  We assume that any Loop may exhaust although this is not
-- always the case, e.g., @(Loop Nop Await)@ will never exhaust.
{-@ measure mayExhaust @-}
mayExhaust x = case x of
  Nop       -> True
  Write _ _ -> True
  Var _ _ p -> mayExhaust p
  Break     -> False
  Await     -> False
  Fin _     -> False
  If _ p q  -> mayExhaust p || mayExhaust q
  Seq p q   -> mayExhaust p && mayExhaust q
  Loop _ _  -> True
  ParOr p q -> mayExhaust p || mayExhaust q

-- Tests whether 'x' is blocked, i.e., if the first instruction in each of
-- its trails is an 'Await' or 'Fin'.
{-@ measure isBlocked @-}
isBlocked x = case x of
  Nop       -> False
  Write _ _ -> False
  Var _ _ p -> isBlocked p
  Break     -> False
  Await     -> True
  Fin _     -> True
  If _ _ _  -> False
  Seq p _   -> isBlocked p
  Loop p _  -> isBlocked p
  ParOr p q -> isBlocked p && isBlocked q

-- Tests whether 'x' is irreducible, i.e., if it cannot be advanced by the
-- 'step' function.
{-@ inline isIrreducible @-}
isIrreducible x = x == Nop || x == Break || isBlocked x

{-@ type StmtIrreducible = {p:Stmt | isIrreducible p} @-}
{-@ type StmtNotIrreducible = {p:Stmt | not (isIrreducible p)} @-}

-- Extracts the bodies of all active 'Fin' statements in 'x'.
{-@ reflect clear @-}
{-@ clear :: x:Stmt -> y:{Stmt | rank x >= rank y} @-}
clear x = case x of
  Nop       -> Nop
  Write _ _ -> Nop
  Var _ _ p -> clear p
  Break     -> Nop
  Await     -> Nop
  Fin p     -> p
  If _ p q  -> Nop
  Seq p _   -> clear p
  Loop p _  -> clear p
  ParOr p q -> Seq (clear p) (clear q)

-- Termination measure for 'Stmt'.
{-@ measure rank @-}
{-@ rank :: Stmt -> {i:Int | i > 0} @-}
rank :: Stmt -> Int
rank x = case x of
  Nop       -> 1
  Write _ _ -> 2
  Var _ _ p -> 1 + rank p
  Break     -> 1
  Await     -> 1
  Fin p     -> 1 + rank p
  If _ p q  -> 1 + max' (rank p) (rank q)
  Seq p q   -> 1 + rank p + if p == Break then 0 else rank q
  Loop p q  -> 1 + rank p + if not (mayExhaust p) then 0 else rank q
  ParOr p q -> 2 + rank p + rank q

-- {-@ reflect step1 @-}
-- {-@ step1
--  :: x:StmtNotIrreducible
--  -> y:{Stmt | mayExhaust y => mayExhaust x}
-- @-}
-- step1 :: Stmt -> Stmt
-- step1 x = case x of
--   Write _ _            -> Nop

--   If b p q
--     | b                -> p
--     | otherwise        -> q

--   Seq p q
--     | p == Nop          -> q
--     | p == Break        -> Break
--     | otherwise         -> Seq (step1 p) q

--   Loop p q
--     | p == Nop          -> Loop q q
--     | p == Break        -> Nop
--     | otherwise         -> Loop (step1 p) q

--   ParOr p q
--     | p == Nop          -> Seq (clear q) Nop
--     | p == Break        -> Seq (clear q) Break
--     | not (isBlocked p) -> ParOr (step1 p) q
--     | q == Nop          -> Seq (clear p) Nop
--     | q == Break        -> Seq (clear p) Break
--     | not (isBlocked q) -> ParOr p (step1 q)
--     | otherwise         -> x      -- impossible
--   x                     -> x      -- impossible

-- -- Safe version of step.
-- {-@ step
--  :: x:StmtNotIrreducible
--  -> y:{Stmt | rank x > rank y}
-- @-}
-- step x = let y = step1 x in y ? lem_step1DecreasesRank x y

-- {-@ run
--  :: StmtNotIrreducible
--  -> StmtIrreducible
-- @-}
-- run :: Stmt -> Stmt
-- run x
--   | isIrreducible x = liquidError "impossible"
--   | otherwise = let x' = step x
--                     s  = show x  ++ " <" ++ show (rank x)  ++ ">"
--                     s' = show x' ++ " <" ++ show (rank x') ++ ">"
--     in trace (s ++ " -> " ++ s') $ if isIrreducible x' then x' else run x'

-- LEMMAS ------------------------------------------------------------------

-- Lemma: If x == (step1 y) then stmtRank x > stmtRank y.
-- Proof: By induction on the structure of x.
-- {-@ lem_step1DecreasesRank
--  :: x:StmtNotIrreducible
--  -> y:{Stmt | y == step1 x}
--  -> {rank x > rank y}
-- @-}
-- lem_step1DecreasesRank :: Stmt -> Stmt -> Proof
-- lem_step1DecreasesRank x y = case x of
--   Nop
--       -> impossible
--          *** QED

--   Break
--       -> impossible
--          *** QED

--   Write id e
--       -> rank y
--          === rank (step1 x)
--          === rank Nop
--          =<= rank x
--          *** QED

--   If b p q
--     | (step1 x) == p
--       -> rank y
--          === rank (step1 x)
--          === rank p
--          =<= rank x
--          *** QED

--     | otherwise
--       -> rank y
--          === rank (step1 x)
--          === rank q
--          =<= rank x
--          *** QED

--   Seq p q
--     | p == Nop
--       -> rank y
--          === rank (step1 x)
--          =<= rank x
--          *** QED

--     | p == Break
--       -> rank y
--          === rank (step1 x)
--          =<= rank x
--          *** QED

--     | otherwise
--       -> rank y
--          === rank (step1 x)
--          === rank (Seq (step1 p) q)
--          =<= 1 + rank (step1 p) + rank q
--              ? lem_step1DecreasesRank p (step1 p)
--          =<= rank x
--          *** QED

--   Loop p q
--     | p == Nop
--       -> rank y
--          === rank (step1 x)
--          === rank (Loop q q)
--          =<= rank x
--          *** QED

--     | p == Break
--       -> rank y
--          === rank (step1 x)
--          === rank Nop
--          =<= rank x
--          *** QED

--     | not (mayExhaust p)
--       -> rank y
--          === rank (step1 x)
--          === rank (Loop (step1 p) q)
--          === 1 + rank (step1 p) ? lem_step1DecreasesRank p (step1 p)
--          =<= rank x
--          *** QED

--     | otherwise
--       -> rank y
--          === rank (step1 x)
--          === rank (Loop (step1 p) q)
--          =<= 1 + rank (step1 p) + rank q ? lem_step1DecreasesRank p (step1 p)
--          =<= rank x
--          *** QED

--   ParOr p q
--     | p == Nop
--       -> rank y
--          === rank (step1 x)
--          === rank (Seq (clear q) Nop)
--          =<= rank x
--          *** QED

--     | p == Break
--       -> rank y
--          === rank (step1 x)
--          === rank (Seq (clear q) Break)
--          =<= rank x
--          *** QED

--     | not (isBlocked p)
--       -> rank y
--          === rank (step1 x)
--          === rank (ParOr (step1 p) q) ? lem_step1DecreasesRank p (step1 p)
--          =<= rank x
--          *** QED

--     | q == Nop
--       -> rank y
--          === rank (step1 x)
--          === rank (Seq (clear p) Nop)
--          =<= rank x
--          *** QED

--     | q == Break
--       -> rank y
--          === rank (step1 x)
--          === rank (Seq (clear p) Break)
--          =<= rank x
--          *** QED

--     | not (isBlocked q)
--       -> rank y
--          === rank (step1 x)
--          === rank (ParOr p (step1 q)) ? lem_step1DecreasesRank q (step1 q)
--          =<= rank x
--          *** QED

--     | otherwise
--       -> impossible
--          *** QED

--   _ -> impossible *** QED

-- TESTS -------------------------------------------------------------------

loop_pass1 = Loop Nop Break
loop_pass2 = Loop Nop Await
loop_pass3 = Loop Nop (Seq (Loop Nop Await) Break)

-- Bad Loop's.
-- loop_fail1 = Loop Nop Nop
-- loop_fail2 = Loop Break Nop
-- loop_fail3 = Loop Nop (Loop Nop Await) -- see loop_pass3

fin_pass1 = Fin Nop
fin_pass2 = Fin (If False Nop (Seq Nop Nop))
fin_pass3 = Fin (ParOr (ParOr (ParOr Nop Nop) Nop) Nop)

-- Bad Fin's.
-- fin_fail1 = Fin Break
-- fin_fail2 = Fin (Seq Nop Await)
-- fin_fail3 = Fin (ParOr (ParOr (ParOr Nop (Loop Nop Break)) Nop) Nop)

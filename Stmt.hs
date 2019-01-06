-- Required for reflection.
{-@ LIQUID "--reflection" @-}

module Stmt where

import Language.Haskell.Liquid.ProofCombinators

----
-- Refined type for `Stmt`:
-- . `stmtRank` is the default termination measure.
-- . `Loop` body must always reach a `Break`.
--
{-@
data Stmt [stmtRank]
  = Nop
  | Break
  | Seq {seq1 :: Stmt, seq2 :: Stmt}
  | Loop {loop1 :: Stmt, loop2 :: StmtReachesBreak}
@-}
data Stmt
  = Nop
  | Break
  | Seq Stmt Stmt
  | Loop Stmt Stmt
  deriving (Eq, Show)

{-@ measure notReached :: {s:String | False} -> a @-}
notReached :: String -> a
notReached msg = error msg

----
-- Tests whether all execution paths in statement reach a `Break`.
--
{-@ measure stmtReachesBreak @-}
stmtReachesBreak stmt = case stmt of
  Nop       -> False
  Break     -> True
  Seq p q   -> stmtReachesBreak p || stmtReachesBreak q
  Loop  _ _ -> False

----
-- Termination measure for `Stmt`.
-- Post: Rank is a positive integer (> 1).
--
{-@ measure stmtRank @-}
{-@ stmtRank :: Stmt -> {i:Int | i > 0} @-}
stmtRank :: Stmt -> Int
stmtRank stmt = case stmt of
  Nop      -> 1
  Break    -> 2
  Seq p q  -> 3 + stmtRank p + if p == Break then 0 else stmtRank q
  Loop p q -> 4 + stmtRank p + if stmtReachesBreak p then 0 else stmtRank q

-- Reflections of the datatype constructors:
{-@ reflect stmtNop @-}
stmtNop = Nop

{-@ reflect stmtBreak @-}
stmtBreak = Break

{-@ reflect stmtSeq @-}
stmtSeq p q = Seq p q

{-@ reflect stmtLoop @-}
{-@ stmtLoop :: Stmt -> StmtReachesBreak -> Stmt @-}
stmtLoop p q = Loop p q

-- Type aliases:
{-@ type StmtReachesBreak = {p:Stmt | stmtReachesBreak p} @-}
{-@ type StmtExhausted    = {p:Stmt | p == Nop || p == Break} @-}
{-@ type StmtNotExhausted = {p:Stmt | p /= Nop && p /= Break} @-}

----
-- Auxiliary (reflected) function used by the `step` function.
--
-- Pre:  A non-exhausted statement `p`.
-- Post: The resulting statement `q` such that `q` and `p` agree on `Break`
--       reachability.
--
{-@ reflect step1 @-}
{-@ step1
 :: x:StmtNotExhausted
 -> y:{Stmt | stmtReachesBreak y <=> stmtReachesBreak x}
@-}
step1 :: Stmt -> Stmt
step1 x = case x of
 Seq Nop q    -> q
 Seq Break _  -> Break
 Seq p q      -> Seq (step1 p) q
 Loop Nop q   -> Loop q q
 Loop Break _ -> Nop
 Loop p q     -> Loop (step1 p) q
 _            -> Nop            -- impossible

----
-- Steps `Stmt` once.
--
-- Pre:  A non-exhausted statement `p`.
-- Post: The resulting statement `q` such that |p| > |q|.
--
-- This function uses thm_step1DecreasesRank.
--
{-@ step
 :: x:StmtNotExhausted
 -> y:{Stmt | stmtRank x > stmtRank y}
@-}
step x = let y = step1 x in y ? thm_step1DecreasesRank x y

----
-- Steps `Stmt` until it exhausts.
--
-- Pre:  A non-exhausted statement.
-- Post: An exhausted statement.
--
{-@ run
 :: p:StmtNotExhausted
 -> q:StmtExhausted
@-}
run :: Stmt -> Stmt
run Nop    = notReached "impossible"
run Break  = notReached "impossible"
run p      = if p' == Nop || p' == Break  then p' else run p'
  where p' = step p

--- THEOREMS ---------------------------------------------------------------

---
-- Thm: x == (step1 y) => stmtRank x > stmtRank y.
-- Proof: By induction on the structure of x.
--
{-@ thm_step1DecreasesRank
 :: x:StmtNotExhausted
 -> y:{Stmt | y == step1 x}
 -> {stmtRank x > stmtRank y}
@-}
thm_step1DecreasesRank :: Stmt -> Stmt -> Proof
thm_step1DecreasesRank x y = case x of
  Seq p q
    | p == Nop
      -> stmtRank (step1 x)
         === stmtRank q
         =<= stmtRank x
         *** QED

    | p == Break
      -> stmtRank y
         === stmtRank (step1 x)
         === stmtRank p
         =<= stmtRank x
         *** QED

    | otherwise
      -> stmtRank y
         === stmtRank (step1 x)
         === stmtRank (Seq (step1 p) q)
         =<= 3 + stmtRank (step1 p) + stmtRank q
             ? thm_step1DecreasesRank p (step1 p)
         =<= stmtRank x
         *** QED

  Loop p q
    | p == Nop
      -> stmtRank y
         === stmtRank (step1 x)
         === stmtRank (Loop q q)
         =<= stmtRank x
         *** QED

    | p == Break
      -> stmtRank y
         === stmtRank (step1 x)
         === stmtRank Nop
         =<= stmtRank x
         *** QED

    | stmtReachesBreak p && stmtReachesBreak (step1 p)
      -> stmtRank y
         === stmtRank (step1 x)
         === stmtRank (Loop (step1 p) q)
         === 4 + stmtRank (step1 p) ? thm_step1DecreasesRank p (step1 p)
         =<= stmtRank x
         *** QED

    | not (stmtReachesBreak p) && not (stmtReachesBreak (step1 p))
      -> stmtRank y
         === stmtRank (step1 x)
         === stmtRank (Loop (step1 p) q)
         === 4 + stmtRank (step1 p) + stmtRank q
         ? thm_step1DecreasesRank p (step1 p)
         =<= stmtRank x
         *** QED

    | otherwise
      -> impossible             -- p and (step1 p) must agree on `reak`
         *** QED                --   reachability

  -- Nop/Break
  _   -> impossible             -- x cannot be exhausted
         *** QED

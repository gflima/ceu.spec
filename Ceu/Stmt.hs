-- Required for reflection.
{-@ LIQUID "--reflection" @-}

module Ceu.Stmt where
import Ceu.LH as LH

-- Refined type for Stmt.
-- . Function rank is the default termination measure.
-- . Loop body must always reach a Break or Await.
{-@
data Stmt [rank]
  = Nop
  | Break
  | Await
  | If {if1 :: Bool, if2 :: Stmt, if3 :: Stmt}
  | Seq {seq1 :: Stmt, seq2 :: Stmt}
  | Loop {loop1 :: Stmt, loop2 :: {p:Stmt | not (mayExhaust p)}}
@-}
data Stmt
  = Nop
  | Break
  | Await
  | If Bool Stmt Stmt
  | Seq Stmt Stmt
  | Loop Stmt Stmt
  deriving (Eq, Show)

-- A statement x _may exhaust_ if it may run to completion without ever
-- executing a Break or Await.  Here we do a crude analysis.  We assume that
-- any Loop may exhaust, although in practice this is not always the case,
-- e.g., (Loop Nop Await) will never exhaust.
{-@ measure mayExhaust @-}
mayExhaust x = case x of
  Nop      -> True
  Break    -> False
  Await    -> False
  If _ p q -> mayExhaust p || mayExhaust q
  Seq p q  -> mayExhaust p && mayExhaust q
  Loop _ _ -> True

-- A statement x _is blocked_ if the first instruction in each execution
-- path in x is an Await.
{-@ measure isBlocked @-}
isBlocked x = case x of
  Nop      -> False
  Break    -> False
  Await    -> True
  If _ _ _ -> False
  Seq p _  -> isBlocked p
  Loop p _ -> isBlocked p

{-@ predicate StmtIsIrreducible P
  = P == Nop || P == Break || isBlocked P @-}
{-@ type StmtIrreducible = {p:Stmt | StmtIsIrreducible p} @-}
{-@ type StmtNotIrreducible = {p:Stmt | not (StmtIsIrreducible p)} @-}

{-@ measure rank @-}
{-@ rank :: Stmt -> {i:Int | i > 0} @-}
rank :: Stmt -> Int
rank x = case x of
  Nop      -> 1
  Break    -> 1
  Await    -> 1
  If _ p q -> 1 + LH.max (rank p) (rank q)
  Seq p q  -> 1 + rank p + if p == Break then 0 else rank q
  Loop p q -> 1 + rank p + if not (mayExhaust p) then 0 else rank q

{-@ reflect step1 @-}
{-@ step1
 :: p:StmtNotIrreducible
 -> q:{Stmt | mayExhaust q => mayExhaust p}
@-}
step1 :: Stmt -> Stmt
step1 x = case x of
 If b p q
   | b         -> p
   | otherwise -> q
 Seq Nop q     -> q
 Seq Break _   -> Break
 Seq p q       -> Seq (step1 p) q
 Loop Nop q    -> Loop q q
 Loop Break _  -> Nop
 Loop p q      -> Loop (step1 p) q
 x             -> x              -- impossible

{-@ step
 :: x:StmtNotIrreducible
 -> y:{Stmt | rank x > rank y}
@-}
step x = let y = step1 x in y ? lem_step1DecreasesRank x y

{-@ run
 :: StmtNotIrreducible
 -> StmtIrreducible
@-}
run :: Stmt -> Stmt
run Nop   = liquidError "impossible"
run Break = liquidError "impossible"
run p     = if p' == Nop || p' == Break || isBlocked p' then p'
            else run p'
  where p' = step p

-- LEMMAS ------------------------------------------------------------------

-- Lemma: If x == (step1 y) then stmtRank x > stmtRank y.
-- Proof: By induction on the structure of x.
{-@ lem_step1DecreasesRank
 :: x:StmtNotIrreducible
 -> y:{Stmt | y == step1 x} -> {rank x > rank y}
@-}
lem_step1DecreasesRank :: Stmt -> Stmt -> Proof
lem_step1DecreasesRank x y = case x of
  Nop   -> impossible *** QED
  Break -> impossible *** QED

  If b p q
    | (step1 x) == p
      -> rank y
         === rank (step1 x)
         === rank p
         =<= rank x
         *** QED

    | otherwise
      -> rank y
         === rank (step1 x)
         === rank q
         =<= rank x
         *** QED

  Seq p q
    | p == Nop
      -> rank y
         === rank (step1 x)
         =<= rank x
         *** QED

    | p == Break
      -> rank y
         === rank (step1 x)
         =<= rank x
         *** QED

    | otherwise
      -> rank y
         === rank (step1 x)
         === rank (Seq (step1 p) q)
         =<= 1 + rank (step1 p) + rank q
             ? lem_step1DecreasesRank p (step1 p)
         =<= rank x
         *** QED

  Loop p q
    | p == Nop
      -> rank y
         === rank (step1 x)
         === rank (Loop q q)
         =<= rank x
         *** QED

    | p == Break
      -> rank y
         === rank (step1 x)
         === rank Nop
         =<= rank x
         *** QED

    | not (mayExhaust p)
      -> rank y
         === rank (step1 x)
         === rank (Loop (step1 p) q)
         === 1 + rank (step1 p) ? lem_step1DecreasesRank p (step1 p)
         =<= rank x
         *** QED

    | otherwise
      -> rank y
         === rank (step1 x)
         === rank (Loop (step1 p) q)
         =<= 1 + rank (step1 p) + rank q ? lem_step1DecreasesRank p (step1 p)
         =<= rank x
         *** QED

-- TESTS -------------------------------------------------------------------

-- fail1 = Loop Nop Nop
-- fail2 = Loop Break Nop
-- pass3 = Loop Nop Break
-- pass4 = Loop Nop Await
-- fail5 = Loop Nop (Loop Nop Await)
-- pass6 = Loop Nop (Seq (Loop Nop Await) Break)

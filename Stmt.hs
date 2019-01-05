-- Required for deep pattern-matching over structured data.
{-@ LIQUID "--exact-data-cons" @-}

-- Required for reflection.
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Stmt where

-- Refined type for `Stmt`: The loop body must always reach a `Break`.
{-@
data Stmt
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

----
-- Tests whether all execution paths in statement reach a `Break`.
--
-- The "measure" directive lifts the function to LH.
--
{-@ measure stmtReachesBreak @-}
stmtReachesBreak :: Stmt -> Bool
stmtReachesBreak stmt = case stmt of
  Nop       -> False
  Break     -> True
  Seq p q   -> stmtReachesBreak p || stmtReachesBreak q
  Loop  _ _ -> False

----
-- Termination measure for `Stmt`.
--
-- LH proves termination by identifying a parameter that decreases some
-- integer measure in recursive calls.
--
{-@ measure stmtRank @-}
{-@ stmtRank :: Stmt -> {i:Int | i > 0} @-}
stmtRank :: Stmt -> Int
stmtRank stmt = case stmt of
  Nop      -> 1
  Break    -> 2
  Seq p q  -> 3 + stmtRank p + if stmtIsBreak p then 0 else stmtRank q
  Loop p q -> 3 + stmtRank p + if stmtReachesBreak p then 0 else stmtRank q

{-@ measure stmtIsNop @-}
stmtIsNop :: Stmt -> Bool
stmtIsNop stmt = case stmt of
  Nop -> True
  _   -> False

{-@ measure stmtIsBreak @-}
stmtIsBreak :: Stmt -> Bool
stmtIsBreak stmt = case stmt of
  Break -> True
  _     -> False

{-@ measure stmtIsSeq @-}
stmtIsSeq :: Stmt -> Bool
stmtIsSeq stmt = case stmt of
  Seq _ _ -> True
  _       -> False

{-@ measure stmtIsLoop @-}
stmtIsLoop :: Stmt -> Bool
stmtIsLoop stmt = case stmt of
  Loop _ _ -> True
  _        -> False

{-@ predicate StmtIsExhausted P = stmtIsNop P || stmtIsBreak P @-}

-- TODO: Lift the constructors:
--
-- {-@ invariant {p:Stmt | stmtRank p > 0} @-}
--
-- {-@ measure stmtNop :: Stmt @-}
-- {-@ assume stmtNop :: {p:Stmt | stmtIsNop p && stmtRank p == 1} @-}
-- stmtNop :: Stmt
-- stmtNop = Nop
--
-- {-@ measure stmtBreak :: Stmt @-}
-- {-@ assume stmtBreak :: {p:Stmt | stmtIsBreak p && stmtRank p == 2} @-}
-- stmtBreak :: Stmt
-- stmtBreak = Break

-- TODO: Relate rank with statement structure:
--
-- {-@ stmtIsExhausted :: p:Stmt -> {v:Bool | StmtIsExhausted p} @-}
-- stmtIsExhausted :: Stmt -> Bool
-- stmtIsExhausted p = stmtRank p >= 0 && stmtRank p <= 2

-- Type aliases:
{-@ type StmtReachesBreak = {p:Stmt | stmtReachesBreak p} @-}
{-@ type StmtExhausted    = {p:Stmt | StmtIsExhausted p} @-}
{-@ type StmtNotExhausted = {p:Stmt | not (StmtIsExhausted p)} @-}
{-@ type StmtNop          = {p:Stmt | stmtIsNop p} @-}
{-@ type StmtBreak        = {p:Stmt | stmtIsBreak p} @-}
{-@ type StmtSeq          = {p:Stmt | stmtIsSeq p} @-}
{-@ type StmtLoop         = {p:Stmt | stmtIsLoop p} @-}
{-@ type StmtAtom         = {p:Stmt | stmtIsNop p || stmtIsBreak p} @-}
{-@ type StmtComplex      = {p:Stmt | stmtIsSeq p || stmtIsLoop p} @-}

----
-- Checks for impossible conditions.
--
{-@ unreachable :: {s:String | False} -> a @-}
unreachable :: String -> a
unreachable msg = error msg

----
-- Tests whether `p` is the 1st sub-statement of `stmt`.
--
-- The "reflect" directive lifts the function to LH.  The same restrictions
-- that apply to measures also apply to reflected functions, but reflected
-- functions can take more than one argument.
--
{-@ reflect stmtIsSub1 @-}
stmtIsSub1 :: Stmt -> Stmt -> Bool
stmtIsSub1 stmt p = case stmt of
  Nop       -> False
  Break     -> False
  Seq p' _  -> p == p'
  Loop p' _ -> p == p'

----
-- Tests whether `p` is the 2nd sub-statement of `stmt`.
--
{-@ reflect stmtIsSub2 @-}
stmtIsSub2 :: Stmt -> Stmt -> Bool
stmtIsSub2 stmt q = case stmt of
  Nop       -> False
  Break     -> False
  Seq _ q'  -> q == q'
  Loop _ q' -> q == q'

{-@ predicate StmtIsSub X P = stmtIsSub1 X P || stmtIsSub2 X P @-}
{-@ predicate StmtIsSub1 X P = stmtIsSub1 X P @-}
{-@ predicate StmtIsSub2 X P = stmtIsSub2 X P @-}

---
-- Gets the 1st sub-statement of `stmt`.
--
-- Pre: A complex statement.
-- Post: Its 1st sub-statement.
--
{-@ stmtSub1 :: x:StmtComplex -> {p:Stmt | StmtIsSub1 x p} @-}
stmtSub1 :: Stmt -> Stmt
stmtSub1 stmt = case stmt of
  Seq p _  -> p
  Loop p _ -> p
  _        -> unreachable "stmtSub1: impossible"

---
-- Gets the 2nd sub-statement of `stmt`
--
-- Pre: A complex statement.
-- Post: Its 2nd sub-statement.
--
{-@ stmtSub2 :: x:StmtComplex -> {p:Stmt | StmtIsSub2 x p} @-}
stmtSub2 :: Stmt -> Stmt
stmtSub2 stmt = case stmt of
  Seq _ q  -> q
  Loop _ q -> q
  _        -> unreachable "stmtSub2: impossible"

----
-- Steps `Stmt` once.
--
-- Pre: A non-exhausted statement `p`.
-- Post: The resulting statement `q` such that
--   (i) `q` has a lower rank than `p`, and
--  (ii) `q` and `p` agree on `Break` reachability.
--
-- The "[stmtRank p]" makes LH use this the termination measure.
--
-- FIXME: Although LH proves (i), I couldn't make it prove (ii). To see this
-- uncomment one of the alternative declarations below.
--

{- step
 :: p:StmtNotExhausted
 -> q:{Stmt | stmtReachesBreak p <=> stmtReachesBreak q && stmtRank p > stmtRank q}
  / [stmtRank p]
@-}

{- step
 :: p:StmtNotExhausted
 -> q:{Stmt | stmtRank p > stmtRank q}
  / [stmtRank p]
@-}

{-@ step
 :: p:StmtNotExhausted
 -> q:{Stmt | stmtReachesBreak p <=> stmtReachesBreak q}
  / [stmtRank p]
@-}

step :: Stmt -> Stmt
step stmt = case stmt of
 Seq Nop q    -> q
 Seq Break _  -> Break
 Seq p q      -> Seq (step p) q
 Loop Nop q   -> Loop q q
 Loop Break _ -> Nop
 Loop p q     -> Loop (step p) q
 _            -> unreachable "step: impossible"

----
-- Steps `Stmt` until it exhausts.
--
-- Pre: A non-exhausted statement.
-- Post: An exhausted statement.
--
-- FIXME: The termination check for this is failing.  We need to make LH see
-- that `step` decreases the rank of the output statement.
--
-- {-@ run :: p:StmtNotExhausted -> q:StmtExhausted / [stmtRank p] @-}
-- run :: Stmt -> Stmt
-- run Nop   = unreachable "impossible"
-- run Break = unreachable "impossible"
-- run p     = if stmtIsNop p' || stmtIsBreak p' then p' else run p'
--   where p' = step p

-- Tests -------------------------------------------------------------------

{-@ stmt1 :: StmtNop @-}
stmt1 = Nop

{-@ stmt2 :: StmtBreak @-}
stmt2 = Break

{-@ stmt2' :: StmtAtom @-}
stmt2' = Break

{-@ stmt3 :: StmtSeq @-}
stmt3 = Seq Nop Nop

{-@ stmt4 :: StmtLoop @-}
stmt4 = Loop Nop Break

{-@ stmt4' :: StmtComplex @-}
stmt4' = Loop Nop Break

-- These do not type check:
-- stmt4'' = Loop Nop Nop
-- stmt4''' = Loop Nop (Loop Nop Break)
-- stmt4'''' = Loop Nop (Loop (Loop Nop Break) Break)

{-@ stmt5 :: {p:StmtLoop | stmtRank p == 14} @-}
stmt5 = Loop Nop (Seq (Loop Break Break) Break)

{-@ stmt6 :: {p:StmtLoop | stmtRank p == 5} @-}
stmt6 = Loop Break (Seq Nop (Seq Nop Break))

-- TT means "always True".
{-@ stmt7 :: x:StmtComplex -> {p:Stmt | StmtIsSub1 x p} -> TT @-}
stmt7 :: Stmt -> Stmt -> Bool
stmt7 x p = stmtSub1 x == p

stmt8 = step (Seq Nop Nop)

-- These do not type check:
-- stmt8' = step Nop
-- stmt8'' = step Break

-- FIXME: These should type-check!
-- {-@ stmt9 :: StmtNop @-}
-- stmt9 = step (Seq Nop Nop)
-- {-@ stmt10 :: StmtBreak @-}
-- stmt10 = step (Loop Break Break)

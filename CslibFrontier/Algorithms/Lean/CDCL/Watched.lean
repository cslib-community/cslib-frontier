/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Minimize
public import CslibFrontier.Algorithms.Lean.CDCL.Watch
public import CslibFrontier.Algorithms.Lean.CDCL.VSIDS
public import CslibFrontier.Algorithms.Lean.CDCL.Phase
public import CslibFrontier.Algorithms.Lean.CDCL.Luby
public import CslibFrontier.Logics.Propositional.CNF.DenseRenaming
public import CslibFrontier.Logics.Propositional.CNF.LRATRelabel
import CslibFrontier.Foundations.Data.List.Fold
import Mathlib.Tactic.Linarith

/-! # A CDCL solver with watched literals and LRAT certificates

An executable instance of abstract DPLL with learning, which returns a model or an LRAT certificate
(`Cslib.Algorithms.Lean.CDCL.solve`). Its moves are those of `Cslib.Algorithms.Lean.CDCL.Exec`;
this module finds conflicts and unit clauses among the clauses of at least two literals with two
watched literals per clause, as MiniSat does, instead of scanning them. Each trail literal is
queued when it is assigned; processing it visits the watchers of its negation: a watcher whose
blocker is true is skipped without reading its clause, and otherwise the clause finds another
watch, is satisfied by its other watch, becomes unit, or is false.

The state `WExec` extends `Exec` with the value of each variable on the trail in an array indexed by
variable (`Assign`, MiniSat's `assigns`), read by the visits of watchers, the checks of the short
clauses and the choice of decision variable instead of scanning the trail, the watch store, the
queue, and the clauses with fewer than two different literals, which cannot be watched and are
scanned when the queue is empty. Conflict analysis reads the literals of the current level from an
array of its own. Its
invariant `WExec.Inv` adds to `Exec.Inv`:

* the watch store's invariant `WatchStore.Inv`: every clause with two different literals is
  stored, and a stored clause with both watches falsified by *processed* literals (literals of the
  trail not on the queue) has a literal that is true and stays true after any backjump keeping
  both watches false;
* the queue is on the trail, without repetitions, and above the newest decision;
* the array of values agrees with the trail (`Assign.Agrees`): Backjump unassigns the variables
  undone, and Restart recomputes it from the root of the trail;
* the variables occurring in the database are marked (`WExec.occurs`), so that the variable order
  skips those that left it.

The condition on the queue makes the invariant survive Backjump without decision levels: the
literals removed include all those above the newest decision, so every processed literal kept was
processed before. It also makes skipping a watcher on a true blocker safe: the literal being
processed is above the newest decision, so any backjump that keeps it false keeps the blocker
true. With the queue empty, no clause of the database is false unless a short one is
(`WExec.Inv.noConflict`), so the loop finds conflicts and units among long clauses without
scanning them. Choosing the next decision variable, or seeing that every variable is assigned and
returning the model, still searches the variables of the database (`CNF.vars`), which can traverse
every literal occurrence.

**The loop** (`Cslib.Algorithms.Lean.CDCL.loop`). While the queue is not empty, it processes its
oldest literal. As in MiniSat, the queue is the part of the trail from a head position on
(`Cslib.Algorithms.Lean.CDCL.WExec.qhead`, `Cslib.Algorithms.Lean.CDCL.WExec.queue`): a literal is
queued by being pushed on the trail, and processed by moving the head past it. A conflict with
no decision on the trail ends with a certificate; otherwise it is analysed, the learned clause is
minimized (`Cslib.Algorithms.Lean.CDCL.Learned.minimize`), and Backjump and Learn follow; the
variables met by the analysis are bumped
(`Cslib.Algorithms.Lean.CDCL.Activity.bump`). With the queue empty, it checks the short clauses for
a conflict or a unit, then decides an unassigned variable of the database of greatest activity
(VSIDS, `Cslib.Algorithms.Lean.CDCL.WExec.pickVar`), popped from the variable order
(`Cslib.Algorithms.Lean.CDCL.VarOrder.pop`), with its saved phase
(`Cslib.Algorithms.Lean.CDCL.Phases.get`), or returns the trail as a model. Backjump saves the
phases of the literals it undoes (`Cslib.Algorithms.Lean.CDCL.Phases.save`); the variables bumped
move up in the variable order and those undone go back in it, keeping its invariant
(`Cslib.Algorithms.Lean.CDCL.WExec.OrderInv`), under which the decision variable has the greatest
activity (`Cslib.Algorithms.Lean.CDCL.WExec.Inv.pickVar_max`). Every move lowers
the measure: the rank of the abstract system, times the number of variables plus two, plus the
length of the queue. A move is `Cslib.Algorithms.Lean.CDCL.step`; the loop makes up to `2 ^ d`
moves by making `2 ^ (d - 1)` moves twice, structurally on `d`, so the kernel can run the solver.
Since every state has measure below `restartBound φ`, a `d` with `restartBound φ < 2 ^ d`, computed
once, never runs out; the measure appears only in proofs, so at run time a move does no
arithmetic on it.

**Reducing the learned clauses** (`Cslib.Algorithms.Lean.CDCL.WExec.maybeReduce`). As in
MiniSat's `reduceDB`, once the learned clauses exceed the assigned variables by a limit, which
grows on a schedule, the less active half of them is forgotten
(`Cslib.Algorithms.Lean.CDCL.Exec.forget`), except the reasons of the trail and the clauses of at
most two literals, and the watch store is rebuilt on the trail
(`Cslib.Algorithms.Lean.CDCL.WatchStore.build`). This happens with the queue empty and no clause
false, and keeps the measure.

**Certified deletion of root-satisfied clauses** (`Cslib.Algorithms.Lean.CDCL.WExec.maybeSimplify`).
At decision level `0` (checked on the trail, `WExec.maybeSimplify_root`) and when the trail grew
since the last time, before the reduction, the clauses satisfied by a literal of the trail are
deleted, input clauses included (MiniSat's `remove_satisfied`, `Options.removeSatisfied`), except
the reasons of the trail; the watch store and the marks of the variables occurring in the database
are rebuilt (`Cslib.Algorithms.Lean.CDCL.WExec.simplify`). At level `0` the trail is its root, so
under total assignments the remaining clauses entail the input clauses, and with them the
clauses deleted; for partial assignments the guarantee concerns the input clauses only
(`Cslib.Algorithms.Lean.CDCL.Exec.forget_inv`). Each deletion is a step of the certificate. If no
clause is satisfied, only the schedule advances.

This is part of MiniSat's `simplify`, not all of it. MiniSat also removes the false literals from
the clauses it keeps, can delete a satisfied clause that is the reason of a root literal after
clearing that reason, and bounds the work of `simplify` by a budget of propagations; it checks the
restart budget before simplifying. Here reasons are kept, which keeps the LRAT proof of the root
literals simple, and kept clauses are not shortened.

**Restarts** (`Cslib.Algorithms.Lean.CDCL.solveWith.search`). As in MiniSat, once a run of the loop
has had its budget of conflicts (`restartFirst` times the Luby sequence, `Options.restartBudget`),
at the next point with an empty queue and no conflict it goes back to the root of the trail, the
literals implied below every decision (`WExec.restart`), keeping the learned clauses, the activities
and the phases. Restarts raise the measure, so each run is bounded by its own measure: each move of
the loop counts at most one conflict and lowers the measure, so a run that restarts has had fewer
conflicts than the bound `restartBound φ` on the measure of every state, which depends only on the
number of variables. The budgets are unbounded (`luby_pow`): the budget of restart
`Options.restartRuns (restartBound φ)` exceeds the bound (`Options.lt_restartBudget`), so that run
does not restart, and the search ends there. Termination is structural on `d` within a run, and on
the runs left before that one. This adapts Theorem 2.16 of Nieuwenhuis, Oliveras and Tinelli,
which asks the number of steps between restarts to increase: it is enough that some run's budget
exceeds the conflicts any run can have, with Forget keeping the measure.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.WExec`, `Cslib.Algorithms.Lean.CDCL.WExec.Inv`: the state and its
  invariant.
* `Cslib.Algorithms.Lean.CDCL.WExec.processFrom`, `Cslib.Algorithms.Lean.CDCL.WExec.processQueue`:
  visiting a watch list, and processing the queue.
* `Cslib.Algorithms.Lean.CDCL.Reduction`, `Cslib.Algorithms.Lean.CDCL.WExec.reduce`: the reduction
  of the learned clauses.
* `Cslib.Algorithms.Lean.CDCL.WExec.simplify`: deleting the clauses satisfied at the root.
* `Cslib.Algorithms.Lean.CDCL.step`, `Cslib.Algorithms.Lean.CDCL.loop`,
  `Cslib.Algorithms.Lean.CDCL.solveWith.search`, `Cslib.Algorithms.Lean.CDCL.solve`: the solver.
* `Cslib.Algorithms.Lean.CDCL.Options`, `Cslib.Algorithms.Lean.CDCL.Stats`,
  `Cslib.Algorithms.Lean.CDCL.solveWith`: the solver with options, returning its statistics.

## Main results

* `Cslib.Algorithms.Lean.CDCL.solve_sat`, `Cslib.Algorithms.Lean.CDCL.solve_unsat`: both answers are
  correct.
* `Cslib.Algorithms.Lean.CDCL.isSat_solve_iff`: the solver decides satisfiability.
* `Cslib.Algorithms.Lean.CDCL.isSat_solveWith_iff`: so it does whatever the options.
* `Cslib.Algorithms.Lean.CDCL.WExec.Inv.pickVar_max`: with VSIDS, every decision is of greatest
  activity among the unassigned variables.
* `Cslib.Algorithms.Lean.CDCL.Options.lt_restartBudget`,
  `Cslib.Algorithms.Lean.CDCL.WExec.Inv.measure_lt_restartBound`: some restart budget exceeds the
  conflicts of any run, so the search with restarts and Forget terminates, with no limit on the
  restarts.
* `Cslib.Algorithms.Lean.CDCL.solveCompactWith_sat`,
  `Cslib.Algorithms.Lean.CDCL.solveCompactWith_unsat`,
  `Cslib.Algorithms.Lean.CDCL.isSat_solveCompactWith_iff`: the same for the solver on renamed
  variables.

**Variable names.** `solve` keeps arrays indexed by variable, sized by the largest variable of the
formula (`Cslib.Algorithms.Lean.CDCL.varSlots`), so a formula such as `[[], [(10⁹, true)]]` with
one variable allocates `10⁹ + 1` slots, and a formula with no variables allocates none.
`Cslib.Algorithms.Lean.CDCL.solveCompact` first renames the `k` distinct variables to
`0, …, k - 1` (`Cslib.Logic.PL.CNF.denseRenaming`), solves the renamed formula, and translates the
answer back: the model through the renaming, and the certificate through the injective map back
(`Cslib.Logic.PL.CNF.checkLRAT_relabel`). The renaming uses a hash map, which the kernel does not
evaluate, so `decide +kernel` clients call `solve`.
-/

public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF
open Cslib.Algorithms.WordRAM.ClauseCode (litCode litCode_injective)

variable {φ : CNF ℕ}

/-- **The minimization of the learned clauses**, MiniSat's `ccmin_mode`: none (`0`), basic (`1`),
or recursive (`2`). -/
inductive CcminMode where
  /-- No minimization (`ccmin_mode = 0`). -/
  | none
  /-- Basic minimization (`ccmin_mode = 1`): a literal goes if the reason of its negation has only
  literals of the clause or implied at level `0`. -/
  | basic
  /-- Recursive minimization (`ccmin_mode = 2`). -/
  | recursive
  deriving DecidableEq, Repr

/-- **Options** of the solver, after MiniSat's: VSIDS for the decision variable (otherwise the
first unassigned variable of the database); phase saving for its polarity (MiniSat's
`phase_saving = 2`; otherwise `false`, MiniSat's `phase_saving = 0`); and restarts, the `i`-th
after `restartFirst * luby restartInc i` more conflicts (MiniSat's `luby_restart`), or
`restartFirst * restartInc ^ i` without `luby`; the minimization of learned clauses (MiniSat's
`ccmin_mode`: `0` none, `1` basic, `2` recursive); and the reduction of the learned clauses
(MiniSat's `reduceDB`; otherwise they are kept). None affects correctness. -/
structure Options where
  /-- Choose decision variables by VSIDS. -/
  vsids : Bool := true
  /-- Choose polarities by phase saving. -/
  phaseSaving : Bool := true
  /-- Restart. -/
  restarts : Bool := true
  /-- Space the restarts by the Luby sequence, rather than geometrically. -/
  luby : Bool := true
  /-- The conflicts before the first restart (MiniSat's `restart_first`). MiniSat requires it to be
  at least `1`; here `0` counts as `1` (`Options.restartBudget`). -/
  restartFirst : ℕ := 100
  /-- The growth of the conflicts between restarts (MiniSat's `restart_inc`). MiniSat requires it to
  exceed `1`; here `0` and `1` count as `2`, so that the budgets are unbounded
  (`Options.restartBudget`). With the Luby sequence, the peaks are `restartInc ^ m`
  (`Cslib.Algorithms.Lean.CDCL.luby_pow`), unbounded from base `2`. -/
  restartInc : ℕ := 2
  /-- The minimization of the learned clauses (MiniSat's `ccmin_mode`). -/
  ccminMode : CcminMode := .recursive
  /-- Forget learned clauses of low activity. -/
  reduce : Bool := true
  /-- The limit on the learned clauses starts at the clauses of the formula divided by this
  (MiniSat's `1 / learntsize_factor`). -/
  learntsDivisor : ℕ := 3
  /-- Simplification deletes the input clauses satisfied at the root too, not only the learned
  ones (MiniSat's `remove_satisfied`). -/
  removeSatisfied : Bool := true
  deriving Repr

/-- The conflicts allowed before the restart numbered `i`. As MiniSat requires `restart_first ≥ 1`
and `restart_inc > 1`, `restartFirst` counts as at least `1` and `restartInc` as at least `2`, so
that the budgets are unbounded. -/
@[expose] def Options.restartBudget (o : Options) (i : ℕ) : ℕ :=
  max 1 o.restartFirst *
    if o.luby then CDCL.luby (max 2 o.restartInc) i else max 2 o.restartInc ^ i

/-- **A restart whose budget exceeds `B`**: its index. With Luby restarts it ends a complete
subsequence of the Luby sequence (`luby_pow`). -/
@[expose] def Options.restartRuns (o : Options) (B : ℕ) : ℕ :=
  if o.luby then 2 ^ (B.log2 + 2) - 2 else B.log2 + 1

theorem Options.lt_restartBudget (o : Options) (B : ℕ) : B < o.restartBudget (o.restartRuns B) := by
  have hB : B < 2 ^ (B.log2 + 1) := Nat.lt_log2_self
  have hy : 2 ^ (B.log2 + 1) ≤ max 2 o.restartInc ^ (B.log2 + 1) :=
    Nat.pow_le_pow_left (Nat.le_max_left _ _) _
  have hf : 1 ≤ max 1 o.restartFirst := Nat.le_max_left _ _
  unfold restartBudget restartRuns
  cases o.luby
  · simp only [Bool.false_eq_true, ↓reduceIte]
    calc B < max 2 o.restartInc ^ (B.log2 + 1) := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ hf
  · simp only [↓reduceIte, luby_pow]
    calc B < max 2 o.restartInc ^ (B.log2 + 1) := by omega
      _ ≤ _ := Nat.le_mul_of_pos_left _ hf

/-- **Statistics** of a run, as MiniSat reports them. -/
structure Stats where
  /-- Conflicts, the last one included when the formula is unsatisfiable. -/
  conflicts : ℕ := 0
  /-- Decisions. -/
  decisions : ℕ := 0
  /-- Propagations, counted as MiniSat counts them: the literals taken from the propagation queue
  for processing, decisions and implied literals alike. -/
  propagations : ℕ := 0
  /-- Restarts. -/
  restarts : ℕ := 0
  /-- Different literals of the learned clauses before minimization (MiniSat's
  `max_literals`). -/
  maxLiterals : ℕ := 0
  /-- Different literals of the learned clauses (MiniSat's `tot_literals`). -/
  literals : ℕ := 0
  /-- Learned clauses forgotten. -/
  removed : ℕ := 0
  /-- Clauses satisfied at the root, deleted by simplification. -/
  simplified : ℕ := 0
  deriving Repr

/-- One more literal taken from the propagation queue. -/
@[expose] def Stats.propagation (s : Stats) : Stats := { s with propagations := s.propagations + 1 }

/-- One more decision. -/
@[expose] def Stats.decision (s : Stats) : Stats := { s with decisions := s.decisions + 1 }

/-- Merging two lists sorted by `le`, in at most `fuel` steps. A loop of `sortBy`, which supplies
enough fuel. -/
@[expose, specialize] def sortBy.merge {α : Type} (le : α → α → Bool) :
    (fuel : ℕ) → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | n + 1, x :: xs, y :: ys =>
    if le x y then x :: sortBy.merge le n xs (y :: ys) else y :: sortBy.merge le n (x :: xs) ys

/-- The elements of a list at even positions, and those at odd positions. -/
@[expose] def splitAlternate {α : Type} : List α → List α × List α
  | [] => ([], [])
  | x :: xs => let p := splitAlternate xs; (x :: p.2, p.1)

/-- Merge sort by `le`, to depth `fuel`. A loop of `sortBy`, which supplies enough fuel. -/
@[expose, specialize] def sortBy.go {α : Type} (le : α → α → Bool) : (fuel : ℕ) → List α → List α
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | n + 1, xs =>
    let p := splitAlternate xs
    sortBy.merge le xs.length (sortBy.go le n p.1) (sortBy.go le n p.2)

/-- **Merge sort by `le`**, to the depth of the length of the list, which is enough. Unlike
`List.mergeSort`, it is structurally recursive, so the kernel can run it. -/
@[expose, specialize] def sortBy {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  sortBy.go le xs.length xs

/-- Whether the clause numbered `id` is a learned clause of a formula of `n` clauses: the clauses of
the formula are numbered `1` to `n`. Counting the learned clauses at insertion and in the store
(`Cslib.Algorithms.Lean.CDCL.WatchStore.learntCount`) both use it. -/
@[expose] def isLearntId (n id : ℕ) : Bool := n < id

/-- **The reduction of the learned clauses**, after MiniSat: the clause activities, by number,
bumped for the clauses met by each analysis and decaying by `1 / 0.999` (MiniSat's
`clause_decay`); the number of learned clauses in the watch store; their limit (MiniSat's
`max_learnts`, a third of the clauses of the formula to begin with, by default); and the conflicts
between increases of the limit by a tenth, which grow by half each time, and the conflicts left
before the next one (MiniSat's `learntsize_adjust_confl` and `learntsize_adjust_cnt`).

MiniSat keeps the limit and the interval as floating-point numbers. Here they are natural numbers,
the limit in thousandths of a clause, so that growing it by a tenth keeps growing it: with `27`
clauses and the default divisor `3` it goes `9000`, `9900`, `10890`, … thousandths, as MiniSat's
goes `9`, `9.9`, `10.89`, …. Divisions truncate. Each division falls short of the exact value by
less than one unit, but the errors accumulate: from an interval of `100`, four increases by half
give `505` here and `506.25` unrounded. -/
structure Reduction where
  /-- The clause activities, by number. -/
  act : Activity
  /-- The learned clauses in the watch store. -/
  learnts : ℕ
  /-- The limit on the learned clauses beyond the assigned variables, in thousandths. -/
  max : ℕ
  /-- The conflicts between increases of the limit. -/
  adjust : ℕ
  /-- The conflicts left before the next increase. -/
  countdown : ℕ

/-- The reduction for a formula of `m` clauses, the limit starting at `m / d` clauses, kept in
thousandths. -/
@[expose] def Reduction.init (m d : ℕ) : Reduction :=
  ⟨Activity.init 0, 0, m * 1000 / d, 100, 100⟩

/-- After a conflict whose analysis met the clauses `used` and learned the clause numbered `id`,
the log's next number being `next`: the clause activities of `id` and of `used` are bumped and
decay, the learned clause is counted if it is `stored`, and the limit grows on schedule. The solver
passes `stored` only for a clause added to the watch store with a learned number (`isLearntId`), the
rule by which `WatchStore.learntCount` counts the store.

As in MiniSat, each clause is bumped once: the solver's `used` is the conflict clause and the reason
of each trail entry resolved, and a clause is the reason of at most one entry of a trail and never
of one when it is false, while `id` is the log's next number, met by no analysis. Repetitions would
only bump a clause twice: the activities are a heuristic, and nothing else depends on them. -/
@[expose]
def Reduction.learn (R : Reduction) (used : List ℕ) (id next : ℕ) (stored : Bool) : Reduction :=
  let act := (R.act.grow next).bumpEach (id :: used) 999
  let learnts := if stored then R.learnts + 1 else R.learnts
  if R.countdown ≤ 1 then
    let adjust := R.adjust + R.adjust / 2
    ⟨act, learnts, R.max + R.max / 10, adjust, adjust⟩
  else ⟨act, learnts, R.max, R.adjust, R.countdown - 1⟩

/-- The state of the solver with watched literals: the state `Exec`, the value of each variable on
the trail, the watch store, the queue of trail literals whose watch lists are still to be visited,
the clauses with fewer than two different literals, the variable activities and order, the saved
phases, the reduction of the learned clauses, the options and the statistics. -/
structure WExec (φ : CNF ℕ) where
  /-- The trail, database and log. -/
  exec : Exec φ
  /-- The value of each variable on the trail. -/
  assign : Assign
  /-- The variables occurring in the database, marked. -/
  occurs : Assign
  /-- The watch store. -/
  store : WatchStore
  /-- The position on the trail of the next literal to process (MiniSat's `qhead`): the literals
  still to be processed are those of the trail from it up (`WExec.queue`). -/
  qhead : ℕ
  /-- The clauses with fewer than two different literals. -/
  short : List (ℕ × Clause ℕ)
  /-- The variable activities of VSIDS, which choose the decision variables. -/
  act : Activity
  /-- The variable order of VSIDS, a heap of the variables by activity, with their positions. -/
  order : VarOrder
  /-- The saved phases, which choose the polarities of the decisions. -/
  phase : Phases
  /-- The reduction of the learned clauses. -/
  red : Reduction
  /-- The number of decisions on the trail (MiniSat's `decisionLevel`), which schedules
  simplification. -/
  level : ℕ
  /-- The length of the trail at the last simplification (MiniSat's `simpDB_assigns`). -/
  simpAssigns : ℕ
  /-- The options. -/
  opts : Options
  /-- The statistics so far. -/
  stats : Stats
  /-- An assignment array with no value, kept between conflicts: conflict analysis marks the
  current level in it, as MiniSat marks variables `seen`, in place of searching the trail, and it
  is cleared afterwards. Whether compiled code updates it in place is not established: the caller
  still holds the state while the marks are built from it, and marking a variable past the end
  grows the array, so it can be copied. -/
  marks : {A : Assign // ∀ v, A.value v = none}

/-- The abstract trail. -/
abbrev WExec.M (S : WExec φ) : Trail := XTrail.trail S.exec.trail

/-- The literals of the trail from position `h` up, oldest first. -/
@[expose] def ATrail.queueFrom (T : ATrail) (h : ℕ) : List (Literal ℕ) :=
  (T.seg h (T.size - h)).reverse.map XEntry.lit

/-- **The literals still to be processed**, oldest first: those of the trail from position
`S.qhead` up. It appears only in the invariant: the solver reads the trail at `S.qhead`. -/
@[expose] def WExec.queue (S : WExec φ) : List (Literal ℕ) := S.exec.tr.queueFrom S.qhead

theorem ATrail.queueFrom_of_le {T : ATrail} {h : ℕ} (hh : T.size ≤ h) : T.queueFrom h = [] := by
  simp [ATrail.queueFrom, Nat.sub_eq_zero_of_le hh]

theorem WExec.queue_of_le {S : WExec φ} (h : S.exec.tr.size ≤ S.qhead) : S.queue = [] :=
  ATrail.queueFrom_of_le h

/-- The queue starts with the literal at `S.qhead`. -/
theorem WExec.queue_of_lt {S : WExec φ} (h : S.qhead < S.exec.tr.size) :
    S.queue = S.exec.tr.lit S.qhead :: S.exec.tr.queueFrom (S.qhead + 1) := by
  rw [WExec.queue, ATrail.queueFrom, ATrail.queueFrom,
    show S.exec.tr.size - S.qhead = (S.exec.tr.size - (S.qhead + 1)) + 1 by omega,
    ATrail.seg_succ_bottom, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.map_cons, ATrail.entry_lit]

theorem WExec.lt_of_mem_queue {S : WExec φ} {x : Literal ℕ} (h : x ∈ S.queue) :
    S.qhead < S.exec.tr.size := by
  by_contra hc
  rw [WExec.queue_of_le (by omega)] at h
  exact List.not_mem_nil h

/-- Pushing an entry on the trail queues its literal last. -/
theorem ATrail.queueFrom_push (T : ATrail) {h : ℕ} (hh : h ≤ T.size) (e : XEntry) :
    (T.push (litCode e.lit) e.rsnCode).queueFrom h = T.queueFrom h ++ [e.lit] := by
  rw [ATrail.queueFrom, ATrail.queueFrom, ATrail.size_push,
    show T.size + 1 - h = (T.size - h) + 1 by omega, ATrail.seg_succ,
    show h + (T.size - h) = T.size by omega, ATrail.entry_push_size,
    ATrail.seg_congr (T := T) fun i _ hi => T.entry_push_lt (by omega)]
  simp

/-- With the head at the end of the trail, pushing an entry makes it the whole queue. -/
theorem ATrail.queueFrom_push_end (T : ATrail) (e : XEntry) :
    (T.push (litCode e.lit) e.rsnCode).queueFrom T.size = [e.lit] := by
  rw [ATrail.queueFrom, ATrail.size_push, Nat.add_sub_cancel_left, ATrail.seg_succ,
    Nat.add_zero, ATrail.entry_push_size]
  rfl

theorem WExec.queue_push {S S' : WExec φ} (h : S.qhead ≤ S.exec.tr.size) (e : XEntry)
    (htr : S'.exec.tr = S.exec.tr.push (litCode e.lit) e.rsnCode) (hq : S'.qhead = S.qhead) :
    S'.queue = S.queue ++ [e.lit] := by
  rw [WExec.queue, WExec.queue, htr, hq, ATrail.queueFrom_push _ h]

theorem WExec.queue_push_end {S S' : WExec φ} (e : XEntry)
    (htr : S'.exec.tr = S.exec.tr.push (litCode e.lit) e.rsnCode)
    (hq : S'.qhead = S.exec.tr.size) : S'.queue = [e.lit] := by
  rw [WExec.queue, htr, hq, ATrail.queueFrom_push_end]

/-- **The invariant of the variable order** over the variables of `φ`. -/
abbrev WExec.OrderInv (S : WExec φ) : Prop :=
  S.order.Inv S.act φ.vars S.M S.occurs.assigned

/-- The invariant of the variable order survives assigning more variables. -/
theorem WExec.OrderInv.extend {S S' : WExec φ} (h : S.OrderInv) (horder : S'.order = S.order)
    (hact : S'.act = S.act) (hocc : S'.occurs = S.occurs)
    (hM : ∀ v ∈ Trail.vars S.M, v ∈ Trail.vars S'.M) : S'.OrderInv := by
  refine ⟨by rw [horder, hact]; exact h.wf, horder ▸ h.pos, horder ▸ h.room,
    fun v hv hvM hvo => ?_⟩
  rw [horder]
  exact h.covers v hv (fun h' => hvM (hM v h')) (hocc ▸ hvo)

/-- The invariant of the variable order survives admitting fewer variables. -/
theorem WExec.OrderInv.restrict {S S' : WExec φ} (h : S.OrderInv) (horder : S'.order = S.order)
    (hact : S'.act = S.act) (hM : S'.M = S.M)
    (hocc : ∀ v, S'.occurs.assigned v = true → S.occurs.assigned v = true) : S'.OrderInv := by
  refine ⟨by rw [horder, hact]; exact h.wf, horder ▸ h.pos, horder ▸ h.room,
    fun v hv hvM hvo => ?_⟩
  rw [horder]
  exact h.covers v hv (hM ▸ hvM) (hocc v hvo)

/-- **The invariant of the solver with watched literals**: the invariant `Exec.Inv`, the
invariant of the watch store, the short clauses, and a queue of distinct trail literals above the
newest decision, with VSIDS the invariant of the variable order, and the array of values agreeing
with the trail. -/
structure WExec.Inv (S : WExec φ) : Prop where
  exec : S.exec.Inv
  store : S.store.Inv S.exec.db S.M S.queue
  short_mem : ∀ e ∈ S.short, e ∈ S.exec.db
  short_covers : ∀ e ∈ S.exec.db, e.2.dedup.length < 2 → e ∈ S.short
  queue_nodup : S.queue.Nodup
  queue_trail : ∀ x ∈ S.queue, x ∈ Trail.lits S.M
  queue_above : ∀ x ∈ S.queue, ∀ N d M₀, S.M = N ++ ⟨d, true⟩ :: M₀ → x ∉ Trail.lits M₀
  order : S.opts.vsids = true → S.OrderInv
  assign : S.assign.Agrees S.M
  occurs : ∀ v, S.occurs.assigned v = true ↔ v ∈ S.exec.clauses.vars

/-- The number of slots for arrays indexed by the variables of `φ`: one more than the largest
variable, and `0` when `φ` has no variables (`[]` and `[[]]`). -/
@[expose] def varSlots (φ : CNF ℕ) : ℕ := φ.vars.foldl (fun m v => max m (v + 1)) 0

private theorem lt_foldl_max_succ : ∀ (vs : List ℕ) (m : ℕ),
    m ≤ vs.foldl (fun m v => max m (v + 1)) m ∧
      ∀ v ∈ vs, v < vs.foldl (fun m v => max m (v + 1)) m
  | [], _ => ⟨le_rfl, fun _ h => absurd h List.not_mem_nil⟩
  | u :: vs, m => by
    obtain ⟨h₁, h₂⟩ := lt_foldl_max_succ vs (max m (u + 1))
    refine ⟨(le_max_left _ _).trans h₁, fun v hv => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right _ _).trans h₁)
    · exact h₂ v hv

/-- Every variable of `φ` has a slot. -/
theorem lt_varSlots {φ : CNF ℕ} {v : ℕ} (hv : v ∈ φ.vars) : v < varSlots φ :=
  (lt_foldl_max_succ φ.vars 0).2 v hv

/-- The initial variable order: with VSIDS, every variable of `φ`, inserted with room for all. -/
@[expose] def WExec.initOrder (φ : CNF ℕ) (o : Options) : VarOrder :=
  if o.vsids then
    (VarOrder.empty (varSlots φ)).addAll (Activity.init (varSlots φ)) φ.vars
  else VarOrder.empty 0

/-- The initial state, with the options `o`. -/
@[expose] def WExec.init (φ : CNF ℕ) (o : Options) : WExec φ :=
  ⟨Exec.init φ, Assign.empty, Assign.marks φ.vars, WatchStore.build #[] Assign.empty φ.lratDB, 0,
    φ.lratDB.filter fun e => e.2.dedup.length < 2,
    Activity.init (varSlots φ), WExec.initOrder φ o,
    Phases.init (varSlots φ), Reduction.init φ.length o.learntsDivisor, 0, 0, o, {},
    ⟨⟨#[]⟩, fun v => by simp [Assign.value]⟩⟩

theorem WExec.init_inv (φ : CNF ℕ) (o : Options) : (WExec.init φ o).Inv where
  exec := Exec.init_inv φ
  store := WatchStore.build_inv #[] Assign.agrees_nil φ.lratDB fun e _ hlen hf => by
    obtain ⟨l, hl⟩ := List.exists_mem_of_length_pos (by omega : 0 < e.2.dedup.length)
    simpa [Trail.lits] using hf l (List.mem_dedup.1 hl)
  short_mem e he := (List.mem_filter.1 he).1
  short_covers e he hlen := List.mem_filter.2 ⟨he, by simpa using hlen⟩
  queue_nodup := List.nodup_nil
  queue_trail _ h := absurd h List.not_mem_nil
  queue_above _ h := absurd h List.not_mem_nil
  assign := Assign.agrees_nil
  occurs v := by
    change (Assign.marks φ.vars).assigned v = true ↔ v ∈ (Exec.init φ).clauses.vars
    rw [Exec.clauses_init, Assign.assigned_marks]
  order hv := by
    change VarOrder.Inv (WExec.initOrder φ o) _ _ _ _
    have hv' : o.vsids = true := hv
    simp only [WExec.initOrder, hv', ↓reduceIte]
    exact VarOrder.inv_addAll_empty _ _ _ _ fun v hv => lt_varSlots hv

/-- The number of variables of `φ`, bounding the length of the trail. -/
abbrev nvars (φ : CNF ℕ) : ℕ := φ.vars.dedup.length

/-- The measure of a state: the rank of its abstract state, weighted above the length of the
queue. -/
@[expose]
def WExec.measure (S : WExec φ) : ℕ := rank φ.vars S.exec.state * (nvars φ + 2) + S.queue.length

theorem WExec.Inv.queue_length_le {S : WExec φ} (h : S.Inv) : S.queue.length ≤ nvars φ := by
  have h₁ : S.queue.length ≤ (Trail.lits S.M).length :=
    List.Nodup.length_le_of_subset h.queue_nodup h.queue_trail
  have h₂ := h.exec.run.length_le
  simp only [Exec.toL_trail] at h₂
  simp only [Trail.lits, List.length_map, WExec.M] at h₁
  simp only [nvars]
  omega

/-! ### Processing a literal -/

/-- The invariant while visiting the watch list of `t.negate`, with the watchers `L` still to be
visited: as `WExec.Inv`, except that a clause watching `t.negate` may have its watcher among `L`
instead of on the watch list, and every clause with a watcher put back on that list has a true
literal. -/
structure WExec.ProcInv (S : WExec φ) (t : Literal ℕ) (L : List Watcher) : Prop where
  exec : S.exec.Inv
  sound : ∀ e ∈ S.store.clauses, ∃ c, (e.1, c) ∈ S.exec.db ∧ ∀ l, l ∈ e.2.toList ↔ l ∈ c
  nodup : ∀ e ∈ S.store.clauses, e.2.toList.Nodup
  long : ∀ e ∈ S.store.clauses, 2 ≤ e.2.size
  covers : ∀ e ∈ S.exec.db, 2 ≤ e.2.dedup.length →
    ∃ e' ∈ S.store.clauses, e'.1 = e.1 ∧ ∀ l, l ∈ e'.2.toList ↔ l ∈ e.2
  listed : ∀ (k : ℕ) (hk : k < S.store.clauses.size), ∀ w ∈ S.store.clauses[k].2.toList.take 2,
    k ∈ clauseIds (watchList S.store.watches (litCode w)) ∨
      (w = t.negate ∧ k ∈ clauseIds L)
  blocker_mem : ∀ i, ∀ x ∈ watchList S.store.watches i,
    ∃ (hk : x.clause < S.store.clauses.size), x.blocker ∈ S.store.clauses[x.clause].2.toList
  pending : ∀ x ∈ L,
    ∃ (hk : x.clause < S.store.clauses.size), x.blocker ∈ S.store.clauses[x.clause].2.toList
  visited : ∀ k ∈ clauseIds (watchList S.store.watches (litCode t.negate)),
    ∀ (hk : k < S.store.clauses.size), ∃ b ∈ S.store.clauses[k].2.toList, b ∈ Trail.lits S.M
  covered : ∀ e ∈ S.store.clauses, ∀ w₁ w₂ rest, e.2.toList = w₁ :: w₂ :: rest →
    Processed S.M S.queue w₁.negate → Processed S.M S.queue w₂.negate →
    ∃ b ∈ e.2.toList, Supported S.M b w₁ w₂
  short_mem : ∀ e ∈ S.short, e ∈ S.exec.db
  short_covers : ∀ e ∈ S.exec.db, e.2.dedup.length < 2 → e ∈ S.short
  queue_nodup : S.queue.Nodup
  queue_trail : ∀ x ∈ S.queue, x ∈ Trail.lits S.M
  queue_above : ∀ x ∈ S.queue, ∀ N d M₀, S.M = N ++ ⟨d, true⟩ :: M₀ → x ∉ Trail.lits M₀
  t_mem : t ∈ S.queue
  t_head : S.exec.tr.lit S.qhead = t
  order : S.opts.vsids = true → S.OrderInv
  assign : S.assign.Agrees S.M
  occurs : ∀ v, S.occurs.assigned v = true ↔ v ∈ S.exec.clauses.vars

/-- Starting to process `t`: its negation's watch list is emptied and becomes the list to visit.
The watchers kept are gathered in an array of the loop (`WExec.withKept`), not in the store. -/
@[expose] def WExec.start (S : WExec φ) (t : Literal ℕ) : WExec φ :=
  { S with
    store := { S.store with watches := setWatch S.store.watches (negKey t) #[] }
    stats := S.stats.propagation }

theorem WExec.start_procInv {S : WExec φ} (h : S.Inv) {t : Literal ℕ} (ht : t ∈ S.queue)
    (hth : S.exec.tr.lit S.qhead = t) :
    (S.start t).ProcInv t (watchList S.store.watches (litCode t.negate)) where
  exec := h.exec
  sound := h.store.sound
  nodup := h.store.nodup
  long := h.store.long
  covers := h.store.covers
  listed k hk w hw := by
    have := h.store.listed k hk w hw
    simp only [WExec.start, ← litCode_negate, watchList_setWatch]
    by_cases hw' : w = t.negate
    · exact .inr ⟨hw', hw' ▸ this⟩
    · have hne : ¬ litCode w = litCode t.negate := fun h => hw' (litCode_injective h)
      exact .inl (by simp only [hne, ↓reduceIte]; exact this)
  blocker_mem i x hx := by
    simp only [WExec.start, ← litCode_negate, watchList_setWatch] at hx
    split at hx
    · simp [unpackWatchers] at hx
    · exact h.store.blocker_mem i x hx
  pending x hx := h.store.blocker_mem _ x hx
  visited k hk := by simp [WExec.start, ← litCode_negate, unpackWatchers] at hk
  covered := h.store.covered
  short_mem := h.short_mem
  short_covers := h.short_covers
  queue_nodup := h.queue_nodup
  queue_trail := h.queue_trail
  queue_above := h.queue_above
  t_mem := ht
  t_head := hth
  order := h.order
  assign := h.assign
  occurs := h.occurs

/-- Finishing the processing of `t`: the head moves past it. -/
@[expose] def WExec.finish (S : WExec φ) (_t : Literal ℕ) : WExec φ :=
  { S with qhead := S.qhead + 1 }

/-- Finishing the head of the queue removes it. -/
theorem WExec.queue_finish {S : WExec φ} {t : Literal ℕ} (ht : t ∈ S.queue)
    (hth : S.exec.tr.lit S.qhead = t) : (S.finish t).queue = S.queue.erase t := by
  have hlt := WExec.lt_of_mem_queue ht
  rw [WExec.queue_of_lt hlt, hth, List.erase_cons_head]
  rfl

theorem WExec.finish_inv {S : WExec φ} {t : Literal ℕ} (h : S.ProcInv t []) :
    (S.finish t).Inv ∧ (S.finish t).measure < S.measure := by
  have hfq := WExec.queue_finish h.t_mem h.t_head
  have hprocessed : ∀ x, Processed S.M (S.queue.erase t) x → Processed S.M S.queue x ∨ x = t :=
    fun x ⟨hx, hxq⟩ => by
      by_cases hxt : x = t
      · exact .inr hxt
      · exact .inl ⟨hx, fun hq => hxq ((List.mem_erase_of_ne hxt).2 hq)⟩
  -- a clause watching `t.negate` has a true literal, and `t` is above the newest decision
  have hsupp : ∀ (k : ℕ) (hk : k < S.store.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.store.clauses[k].2.toList = w₁ :: w₂ :: rest → (w₁.negate = t ∨ w₂.negate = t) →
      ∃ b ∈ S.store.clauses[k].2.toList, Supported S.M b w₁ w₂ := by
    intro k hk w₁ w₂ rest hc hwt
    obtain ⟨w, hw, hwt', hw₁₂⟩ : ∃ w ∈ S.store.clauses[k].2.toList.take 2, w.negate = t ∧
        (w = w₁ ∨ w = w₂) := by
      rcases hwt with h₁ | h₂
      · exact ⟨w₁, by simp [hc], h₁, .inl rfl⟩
      · exact ⟨w₂, by simp [hc], h₂, .inr rfl⟩
    have hu : w = t.negate := by rw [← hwt', negate_negate]
    rcases h.listed k hk w hw with hl | ⟨-, hL⟩
    · obtain ⟨b, hb, hbM⟩ := h.visited k (hu ▸ hl) hk
      refine ⟨b, hb, hbM, fun N d M₀ hN h₁ h₂ => ?_⟩
      have ht : t ∈ Trail.lits M₀ := by
        rcases hw₁₂ with rfl | rfl
        · exact hwt' ▸ h₁
        · exact hwt' ▸ h₂
      exact absurd ht (h.queue_above t h.t_mem N d M₀ hN)
    · simp at hL
  refine ⟨⟨h.exec, ⟨h.sound, h.nodup, h.long, h.covers, fun k hk w hw => ?_, h.blocker_mem, ?_⟩,
    h.short_mem, h.short_covers, hfq ▸ h.queue_nodup.erase t,
    fun x hx => h.queue_trail x (List.mem_of_mem_erase (hfq ▸ hx)),
    fun x hx => h.queue_above x (List.mem_of_mem_erase (hfq ▸ hx)), h.order, h.assign,
    h.occurs⟩, ?_⟩
  · rcases h.listed k hk w hw with hl | ⟨-, hL⟩
    · exact hl
    · simp at hL
  · intro e he w₁ w₂ rest hc h₁ h₂
    rw [hfq] at h₁ h₂
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 he
    rcases hprocessed _ h₁ with h₁ | h₁
    · rcases hprocessed _ h₂ with h₂ | h₂
      · exact h.covered _ he w₁ w₂ rest hc h₁ h₂
      · exact hsupp k hk w₁ w₂ rest hc (.inr h₂)
    · exact hsupp k hk w₁ w₂ rest hc (.inl h₁)
  · change rank φ.vars S.exec.state * (nvars φ + 2) + (S.finish t).queue.length <
      rank φ.vars S.exec.state * (nvars φ + 2) + S.queue.length
    rw [hfq]
    have := List.length_erase_of_mem h.t_mem
    have : 0 < S.queue.length := List.length_pos_of_mem h.t_mem
    omega

private theorem watchInj_mem {W : Watches} {a b : Literal ℕ} {k : ℕ}
    (h : litCode a = litCode b) (hk : k ∈ clauseIds (watchList W (litCode a))) :
    k ∈ clauseIds (watchList W (litCode b)) := h ▸ hk

theorem otherWatch_spec {u w₁ w₂ : Literal ℕ} (hne : w₁ ≠ w₂) :
    (w₁ = u → otherWatch u w₁ w₂ = w₂) ∧ (w₂ = u → otherWatch u w₁ w₂ = w₁) := by
  refine ⟨fun h => by simp [otherWatch, h], fun h => ?_⟩
  have : w₁ ≠ u := fun h' => hne (h'.trans h.symm)
  simp [otherWatch, this]

theorem otherWatch_mem {u w₁ w₂ : Literal ℕ} {rest : Clause ℕ} :
    otherWatch u w₁ w₂ ∈ w₁ :: w₂ :: rest := by
  unfold otherWatch; split <;> simp

/-- Putting a watcher, of the clause at position `k` with the blocker of key `b`, back on the watch
list of `t.negate`. -/
@[expose] def WExec.putBack (S : WExec φ) (t : Literal ℕ) (k b : ℕ) : WExec φ :=
  { S with store := { S.store with
      watches := addWatch S.store.watches (negKey t) k b } }

/-- **Putting back** the watcher `w` just visited, or a watcher of the same clause, with a blocker
of the clause, when the clause has a true literal. -/
theorem WExec.ProcInv.putBack {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    (h : S.ProcInv t (w :: L)) (k b : ℕ) (hx : k = w.clause)
    (hmem : ∃ (hk : k < S.store.clauses.size), litOfKey b ∈ S.store.clauses[k].2.toList)
    (htrue : ∀ (hk : k < S.store.clauses.size),
      ∃ b ∈ S.store.clauses[k].2.toList, b ∈ Trail.lits S.M) :
    (S.putBack t k b).ProcInv t L := by
  refine ⟨h.exec, h.sound, h.nodup, h.long, h.covers, fun k' hk' w' hw' => ?_, fun i y hy => ?_,
    fun y hy => h.pending y (List.mem_cons_of_mem _ hy), fun k' hk'' hk' => ?_, h.covered,
    h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem, h.t_head,
    h.order, h.assign, h.occurs⟩
  · simp only [WExec.putBack, ← litCode_negate, watchList_addWatch]
    rcases h.listed k' hk' w' hw' with hl | ⟨rfl, hL⟩
    · split
      · rename_i hi
        exact .inl (List.mem_cons_of_mem _ (watchInj_mem hi hl))
      · exact .inl hl
    · rcases List.mem_cons.1 hL with rfl | hL
      · exact .inl (by simp [hx])
      · exact .inr ⟨rfl, hL⟩
  · rcases mem_watchList_addWatch hy with rfl | hy
    · exact hmem
    · exact h.blocker_mem i y hy
  · simp only [WExec.putBack, ← litCode_negate, watchList_addWatch, ↓reduceIte, List.map_cons,
      List.mem_cons] at hk''
    rcases hk'' with rfl | hk''
    · exact htrue hk'
    · exact h.visited k' hk'' hk'

/-- A stored clause has two watched literals. -/
theorem WExec.ProcInv.exists_cons {S : WExec φ} {t : Literal ℕ} {L : List Watcher}
    (h : S.ProcInv t L) {k : ℕ} (hk : k < S.store.clauses.size) :
    ∃ w₁ w₂ rest, S.store.clauses[k].2.toList = w₁ :: w₂ :: rest := by
  have : 2 ≤ S.store.clauses[k].2.toList.length := by simpa using h.long _ (Array.getElem_mem hk)
  match hc : S.store.clauses[k].2.toList, this with
  | w₁ :: w₂ :: rest, _ => exact ⟨w₁, w₂, rest, rfl⟩

/-- **Skipping** a watcher whose blocker is true: it goes back on the watch list. -/
theorem WExec.ProcInv.skip {S : WExec φ} {t : Literal ℕ} {k b : ℕ} {L : List Watcher}
    (h : S.ProcInv t (⟨k, litOfKey b⟩ :: L))
    (hv : VisitSpec S.store S.M t.negate ⟨k, litOfKey b⟩ .skip) :
    (S.putBack t k b).ProcInv t L :=
  h.putBack k b rfl (h.pending _ List.mem_cons_self) fun _ => by
    obtain ⟨_, hb⟩ := h.pending _ List.mem_cons_self
    exact ⟨litOfKey b, hb, hv⟩

/-- **Keeping** a clause whose other watched literal is true: it goes back on the watch list, with
that literal as blocker. -/
theorem WExec.ProcInv.keep {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    {b : Literal ℕ} (h : S.ProcInv t (w :: L)) (hv : VisitSpec S.store S.M t.negate w (.keep b)) :
    (S.putBack t w.clause (litCode b)).ProcInv t L := by
  obtain ⟨hk, w₁, w₂, rest, hc, -, rfl, hb⟩ := hv
  have hbmem : otherWatch t.negate w₁ w₂ ∈ S.store.clauses[w.clause].2.toList :=
    hc ▸ otherWatch_mem
  exact h.putBack _ _ rfl ⟨hk, by rw [litOfKey_litCode]; exact hbmem⟩ fun _ => ⟨_, hbmem, hb⟩

/-- **Dropping** a watcher whose clause no longer watches the literal. -/
theorem WExec.ProcInv.drop {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    (h : S.ProcInv t (w :: L)) (hv : VisitSpec S.store S.M t.negate w .drop) :
    S.ProcInv t L := by
  refine ⟨h.exec, h.sound, h.nodup, h.long, h.covers, fun k' hk' w' hw' => ?_, h.blocker_mem,
    fun y hy => h.pending y (List.mem_cons_of_mem _ hy), h.visited, h.covered, h.short_mem,
    h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem, h.t_head,
    h.order, h.assign, h.occurs⟩
  rcases h.listed k' hk' w' hw' with hl | ⟨rfl, hL⟩
  · exact .inl hl
  · rcases List.mem_cons.1 hL with hkw | hL
    · subst hkw
      obtain ⟨w₁, w₂, rest, hc⟩ := h.exists_cons hk'
      obtain ⟨h₁, h₂⟩ := hv hk' w₁ w₂ rest hc
      rw [hc] at hw'
      simp only [List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil,
        or_false] at hw'
      rcases hw' with hw' | hw'
      · exact absurd hw'.symm h₁
      · exact absurd hw'.symm h₂
    · exact .inr ⟨rfl, hL⟩

/-- Putting `u` in place of the element `x` at position `i`, then `x` in front, permutes `u` in
front of the list. -/
theorem perm_cons_set {α : Type} {rest : List α} {i : ℕ} {x u : α} (h : rest[i]? = some x) :
    (x :: rest.set i u).Perm (u :: rest) := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.1 h
  have hr : rest = rest.take i ++ x :: rest.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i rest, List.drop_eq_getElem_cons hi, hx]
  have hs : rest.set i u = rest.take i ++ u :: rest.drop (i + 1) := by
    rw [List.set_eq_take_append_cons_drop]
    simp [hi]
  rw [hs]
  conv_rhs => rw [hr]
  exact (List.perm_middle.cons x).trans
    ((List.Perm.swap u x _).trans (List.perm_middle.symm.cons u))

/-- The clause of a store after `WatchStore.moveTo`: the literals of its array, as a list. -/
theorem toList_moveTo {a : Array (Literal ℕ)} {w₁ w₂ o x u : Literal ℕ} {rest : Clause ℕ}
    {i : ℕ} (ha : a.toList = w₁ :: w₂ :: rest) :
    (((a.setIfInBounds 0 o).setIfInBounds 1 x).setIfInBounds (i + 2) u).toList =
      o :: x :: rest.set i u := by
  simp [Array.toList_setIfInBounds, ha]

/-- **Moving** a watch to a literal that is not false. -/
theorem WExec.ProcInv.move {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    {j : ℕ} {x b : Literal ℕ} (h : S.ProcInv t (w :: L))
    (hv : VisitSpec S.store S.M t.negate w (.move j x b)) :
    ({ S with store := S.store.moveTo w.clause j (litCode b) (litCode x) (litCode t.negate) } :
      WExec φ).ProcInv t L := by
  obtain ⟨hk, w₁, w₂, rest, i, hc, hu, rfl, hxi, hxf, rfl⟩ := hv
  set k := w.clause with hkdef
  set u := t.negate
  set o := otherWatch u w₁ w₂
  set f : ℕ × Array (Literal ℕ) → ℕ × Array (Literal ℕ) := fun e =>
    (e.1, ((e.2.setIfInBounds 0 o).setIfInBounds 1 x).setIfInBounds (i + 2) u) with hf
  set C' := S.store.clauses.modify k f with hC'
  -- the clauses of the store after the move, read back
  have hcl : (S.store.moveTo k (i + 2) (litCode o) (litCode x) (litCode u)).clauses = C' := by
    rw [WatchStore.clauses_moveTo]
    · simp only [litOfKey_litCode]; rfl
    · intro hk'
      have hi := (List.getElem?_eq_some_iff.1 hxi).1
      have hlen := congrArg List.length hc
      rw [S.store.getElem_clauses hk'] at hlen
      simp only [decodeClause, Array.toList_map, List.length_map, Array.length_toList,
        Array.size_pop, List.length_cons] at hlen
      omega
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := u) hne
  have hx : x ∈ rest := List.mem_of_getElem? hxi
  have hxu : x ≠ u := by
    rintro rfl
    exact hxf (by rw [negate_negate]; exact h.queue_trail t h.t_mem)
  have hnewl : (f S.store.clauses[k]).2.toList = o :: x :: rest.set i u := by
    simp only [hf]; exact toList_moveTo hc
  -- the new clause is a permutation of the old one
  have hperm : (o :: x :: rest.set i u).Perm (w₁ :: w₂ :: rest) := by
    have hrest := perm_cons_set (u := u) hxi
    rcases hu with h₁ | h₂
    · have : o = w₂ := ho₁ h₁
      rw [this, h₁]
      exact (hrest.cons w₂).trans (List.Perm.swap u w₂ _)
    · have : o = w₁ := ho₂ h₂
      rw [this, h₂]
      exact hrest.cons w₁
  have hsize : C'.size = S.store.clauses.size := by simp [hC']
  have hnew : ∀ (hk' : k < C'.size), C'[k] = f S.store.clauses[k] :=
    fun _ => by simp only [hC', Array.getElem_modify, ↓reduceIte]
  have hothers : ∀ i' (hi : i' < S.store.clauses.size), i' ≠ k →
      C'[i']'(by rw [hsize]; exact hi) = S.store.clauses[i'] :=
    fun i' hi hik => by simp [hC', Array.getElem_modify, Ne.symm hik]
  have hmem : ∀ e ∈ C', e = f S.store.clauses[k] ∨ e ∈ S.store.clauses := fun e he => by
    obtain ⟨i', hi', rfl⟩ := Array.mem_iff_getElem.1 he
    by_cases hik : i' = k
    · subst hik; exact .inl (hnew hi')
    · have hi'' : i' < S.store.clauses.size := by rw [← hsize]; exact hi'
      rw [hothers i' hi'' hik]; exact .inr (Array.getElem_mem _)
  have hfid : (f S.store.clauses[k]).1 = S.store.clauses[k].1 := rfl
  have hou : o ≠ u := by
    change otherWatch u w₁ w₂ ≠ u
    rcases hu with h₁ | h₂
    · rw [ho₁ h₁]; exact fun h₂ => hne (h₁.trans h₂.symm)
    · rw [ho₂ h₂]; exact fun h₁ => hne (h₁.trans h₂.symm)
  have hotake : o ∈ (S.store.clauses[k].2.toList).take 2 := by
    change otherWatch u w₁ w₂ ∈ _
    rw [hc]
    rcases hu with h₁ | h₂
    · simp [ho₁ h₁]
    · simp [ho₂ h₂]
  have hidx : litCode u ≠ litCode x := fun h => hxu (litCode_injective h).symm
  -- every clause keeps its literals
  have hlits : ∀ i' (hi : i' < S.store.clauses.size) (b : Literal ℕ),
      b ∈ S.store.clauses[i'].2.toList → b ∈ (C'[i']'(by rw [hsize]; exact hi)).2.toList := by
    intro i' hi b hb
    by_cases hik : i' = k
    · subst hik
      rw [hnew, hnewl, hperm.mem_iff]
      rw [hc] at hb
      exact hb
    · rw [hothers i' hi hik]; exact hb
  have hpres : ∀ y : Watcher, (∃ (hk : y.clause < S.store.clauses.size),
      y.blocker ∈ S.store.clauses[y.clause].2.toList) →
      ∃ (hk : y.clause < C'.size), y.blocker ∈ C'[y.clause].2.toList :=
    fun y ⟨hy, hb⟩ => ⟨by rw [hsize]; exact hy, hlits _ hy _ hb⟩
  refine ⟨h.exec, ?_, ?_, ?_, ?_, ?_, fun i' y hy => ?_, fun y hy => ?_, ?_, ?_, h.short_mem,
    h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem, h.t_head,
    h.order, h.assign, h.occurs⟩ <;> rw [hcl]
  · intro e he
    rcases hmem e he with rfl | he
    · obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
      rw [hc] at hceq
      exact ⟨c, hfid ▸ hcdb, fun l => by rw [hnewl]; exact (hperm.mem_iff).trans (hceq l)⟩
    · exact h.sound e he
  · intro e he
    rcases hmem e he with rfl | he
    · rw [hnewl]; exact hperm.nodup_iff.2 hnd
    · exact h.nodup e he
  · intro e he
    rcases hmem e he with rfl | he
    · simp only [hf, Array.size_setIfInBounds]
      exact h.long _ (Array.getElem_mem hk)
    · exact h.long e he
  · intro e he hlen
    obtain ⟨e', he', hid, heq⟩ := h.covers e he hlen
    obtain ⟨i', hi, rfl⟩ := Array.mem_iff_getElem.1 he'
    by_cases hik : i' = k
    · subst hik
      refine ⟨f S.store.clauses[k], Array.mem_iff_getElem.2
        ⟨k, by rw [hsize]; exact hi, hnew _⟩, by rw [hfid]; exact hid, fun l => ?_⟩
      rw [← heq l, hnewl, hc]; exact hperm.mem_iff
    · exact ⟨_, Array.mem_iff_getElem.2 ⟨i', by rw [hsize]; exact hi, hothers i' hi hik⟩, hid,
        heq⟩
  · intro k' hk' w' hw
    have hk'' : k' < S.store.clauses.size := by rw [← hsize]; exact hk'
    by_cases hkk : k' = k
    · subst hkk
      simp only [hnew, hnewl, List.take_succ_cons, List.take_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw
      · rw [hw]
        rcases h.listed _ hk'' _ hotake with hl | ⟨hw', -⟩
        · exact .inl (mem_clauseIds_addWatch hl)
        · exact absurd hw' hou
      · rw [hw]; exact .inl (mem_clauseIds_addWatch_self _ _ _ _)
    · simp only [hothers k' hk'' hkk] at hw ⊢
      rcases h.listed k' hk'' w' hw with hl | ⟨hw', hL⟩
      · exact .inl (mem_clauseIds_addWatch hl)
      · exact .inr ⟨hw', (List.mem_cons.1 hL).resolve_left hkk⟩
  · rcases mem_watchList_addWatch hy with rfl | hy
    · exact ⟨by rw [hsize]; exact hk, by rw [hnew, hnewl]; simp⟩
    · exact hpres y (h.blocker_mem i' y hy)
  · exact hpres y (h.pending y (List.mem_cons_of_mem _ hy))
  · intro k' hk' hk''
    simp only [WatchStore.moveTo, watchList_addWatch] at hk'
    replace hk' : k' ∈ clauseIds (watchList S.store.watches (litCode t.negate)) := by
      split at hk'
      · exact absurd ‹_› hidx
      · exact hk'
    have hk3 : k' < S.store.clauses.size := by rw [← hsize]; exact hk''
    obtain ⟨b, hb, hbM⟩ := h.visited k' hk' hk3
    exact ⟨b, hlits k' hk3 b hb, hbM⟩
  · intro e he v₁ v₂ rest' hc' _ h₂
    rcases hmem e he with rfl | he
    · rw [hnewl] at hc'
      simp only [List.cons.injEq] at hc'
      obtain ⟨-, rfl, -⟩ := hc'
      exact absurd h₂.1 hxf
    · exact h.covered e he v₁ v₂ rest' hc' ‹_› h₂

/-- A variable of the trail has a literal on it. -/
theorem Trail.mem_lits_of_mem_vars {M : Trail} {v : ℕ} (h : v ∈ Trail.vars M) :
    (v, true) ∈ Trail.lits M ∨ (v, false) ∈ Trail.lits M := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
  obtain ⟨⟨w, b⟩, d⟩ := e
  have : (w, b) ∈ Trail.lits M := List.mem_map.2 ⟨_, he, rfl⟩
  cases b
  · exact .inr this
  · exact .inl this

/-- A literal that is neither true nor false is over an unassigned variable. -/
theorem not_mem_vars_of_undef {M : Trail} {l : Literal ℕ} (h₁ : l ∉ Trail.lits M)
    (h₂ : l.negate ∉ Trail.lits M) : l.1 ∉ Trail.vars M := by
  intro hv
  obtain ⟨v, b⟩ := l
  rcases Trail.mem_lits_of_mem_vars hv with h | h <;> cases b <;>
    simp_all [Std.Sat.Literal.negate]

/-- **UnitPropagate** during processing: the literal is added to the trail, with the clause
numbered `id` as its reason, and queued. -/
@[expose] def WExec.propagateUnit (S : WExec φ) (l : Literal ℕ) (id : ℕ) : WExec φ :=
  { S with
    exec := S.exec.propagate (id, []) l, assign := S.assign.assign l }

/-- **A unit clause**: its other watched literal is propagated and queued, and its watcher goes
back on the watch list with that literal as blocker. -/
theorem WExec.ProcInv.unit {S : WExec φ} {t l : Literal ℕ} {id : ℕ} {w : Watcher}
    {L : List Watcher} (h : S.ProcInv t (w :: L))
    (hv : VisitSpec S.store S.M t.negate w (.unit l id)) :
    ((S.propagateUnit l id).putBack t w.clause (litCode l)).ProcInv t L ∧
      ((S.propagateUnit l id).putBack t w.clause (litCode l)).measure < S.measure := by
  obtain ⟨hk, w₁, w₂, rest, hid, hc, hu, rfl, hl, hln, hrest⟩ := hv
  set u := t.negate
  set o := otherWatch u w₁ w₂
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := u) hne
  obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
  rw [hid] at hcdb
  rw [hc] at hceq
  have hu' : u.negate ∈ Trail.lits S.M := by
    rw [negate_negate]; exact h.queue_trail t h.t_mem
  -- every literal of the clause but the propagated one is false
  have hfalse : ∀ y ∈ c, y ≠ o → y.negate ∈ Trail.lits S.M := by
    intro y hy hne'
    rcases List.mem_cons.1 ((hceq y).2 hy) with rfl | hy
    · rcases hu with h₁ | h₂
      · exact h₁ ▸ hu'
      · exact absurd (ho₂ h₂).symm hne'
    · rcases List.mem_cons.1 hy with rfl | hy
      · rcases hu with h₁ | h₂
        · exact absurd (ho₁ h₁).symm hne'
        · exact h₂ ▸ hu'
      · exact hrest y hy
  have hmemc : o ∈ c := (hceq _).1 otherWatch_mem
  have hspec := Exec.propagate_spec h.exec hcdb hmemc (not_mem_vars_of_undef hl hln) hfalse
  have hM : (S.propagateUnit o id).M = ⟨o, false⟩ :: S.M := by
    simp only [WExec.M, WExec.propagateUnit, Exec.trail_propagate, XTrail.trail_cons,
      XEntry.entry_implied]
  have hlits : Trail.lits (S.propagateUnit o id).M = o :: Trail.lits S.M := by rw [hM]; rfl
  have hlt := WExec.lt_of_mem_queue h.t_mem
  have hq' : (S.propagateUnit o id).queue = S.queue ++ [o] :=
    WExec.queue_push (by omega) (.implied o id) rfl rfl
  have hmem : ∀ x, x ∈ (S.propagateUnit o id).queue ↔ x = o ∨ x ∈ S.queue := fun x => by
    rw [hq', List.mem_append, List.mem_singleton, or_comm]
  have hproc : ∀ x, Processed (S.propagateUnit o id).M (S.propagateUnit o id).queue x →
      Processed S.M S.queue x := by
    intro x ⟨hx, hxq⟩
    rw [hlits] at hx
    rw [hmem, not_or] at hxq
    exact ⟨(List.mem_cons.1 hx).resolve_left hxq.1, hxq.2⟩
  have h' : (S.propagateUnit o id).ProcInv t (w :: L) := by
    refine ⟨hspec.1, h.sound, h.nodup, h.long, h.covers, h.listed, h.blocker_mem, h.pending,
      fun k' hk' hk'' => ?_, fun e he v₁ v₂ rest' hc' h₁ h₂ => ?_, h.short_mem, h.short_covers,
      ?_, ?_, ?_, (hmem t).2 (.inr h.t_mem),
      by
        change (S.exec.tr.push _ _).lit S.qhead = t
        rw [← ATrail.entry_lit, ATrail.entry_push_lt _ hlt, ATrail.entry_lit]; exact h.t_head,
      fun hv => (h.order hv).extend rfl rfl rfl fun v hv => by
        rw [hM]; exact List.mem_cons_of_mem _ hv,
      by rw [hM]; exact h.assign.cons (not_mem_vars_of_undef hl hln) false, h.occurs⟩
    · obtain ⟨b, hb, hbM⟩ := h.visited k' hk' hk''
      exact ⟨b, hb, by rw [hlits]; exact List.mem_cons_of_mem _ hbM⟩
    · obtain ⟨b, hb, hs⟩ := h.covered e he v₁ v₂ rest' hc' (hproc _ h₁) (hproc _ h₂)
      exact ⟨b, hb, hM ▸ hs.cons _⟩
    · rw [hq']
      exact (List.perm_append_singleton o S.queue).nodup_iff.2
        (List.nodup_cons.2 ⟨fun hq => hl (h.queue_trail _ hq), h.queue_nodup⟩)
    · intro x hx
      rw [hlits]
      rcases (hmem x).1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h.queue_trail x hx)
    · intro x hx N d M₀ hN
      cases N with
      | nil => simp [hM] at hN
      | cons y N =>
        rw [hM] at hN
        simp only [List.cons_append, List.cons.injEq] at hN
        rcases (hmem x).1 hx with rfl | hx
        · intro hxM₀
          apply hl
          rw [hN.2, lits_append]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ hxM₀)
        · exact h.queue_above x hx N d M₀ hN.2
  have homem : o ∈ S.store.clauses[w.clause].2.toList := hc ▸ otherWatch_mem
  refine ⟨h'.putBack w.clause (litCode o) rfl ⟨hk, by rw [litOfKey_litCode]; exact homem⟩
    fun _ => ⟨o, homem, by rw [hlits]; exact List.mem_cons_self⟩, ?_⟩
  have hlen : ((S.propagateUnit o id).putBack t w.clause (litCode o)).queue.length =
      S.queue.length + 1 := by
    change (S.propagateUnit o id).queue.length = _
    rw [hq', List.length_append, List.length_singleton]
  simp only [WExec.measure, hlen]
  have : rank φ.vars (S.exec.propagate (id, []) o).state < rank φ.vars S.exec.state := hspec.2
  change rank φ.vars (S.exec.propagate (id, []) o).state * (nvars φ + 2) + (S.queue.length + 1) <
    rank φ.vars S.exec.state * (nvars φ + 2) + S.queue.length
  nlinarith

private theorem mem_clauseIds_append {A B : List Watcher} {k : ℕ} :
    k ∈ clauseIds (A ++ B) ↔ k ∈ clauseIds A ∨ k ∈ clauseIds B := by
  simp [clauseIds]

/-- **A conflict**: the clause numbered `id` is a clause of the database, the log names it, and the
trail falsifies it. -/
theorem WExec.ProcInv.conflict_clause {S : WExec φ} {t : Literal ℕ} {w : Watcher}
    {L : List Watcher} {id : ℕ} (h : S.ProcInv t (w :: L))
    (hv : VisitSpec S.store S.M t.negate w (.conflict id)) :
    ∃ c, (id, c) ∈ S.exec.db ∧ S.exec.log.clause? id = some c ∧ Trail.Falsifies S.M c := by
  obtain ⟨hk, w₁, w₂, rest, hid, hc, hu, hoth, hrest⟩ := hv
  obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
  rw [hid] at hcdb
  rw [hc] at hceq
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := t.negate) hne
  have hu' : t.negate.negate ∈ Trail.lits S.M := by
    rw [negate_negate]; exact h.queue_trail t h.t_mem
  refine ⟨c, hcdb, h.exec.db_log _ hcdb, fun y hy => ?_⟩
  rcases List.mem_cons.1 ((hceq y).2 hy) with rfl | hy
  · rcases hu with h₁ | h₂
    · exact h₁ ▸ hu'
    · rw [← ho₂ h₂]; exact hoth
  · rcases List.mem_cons.1 hy with rfl | hy
    · rcases hu with h₁ | h₂
      · rw [← ho₁ h₁]; exact hoth
      · exact h₂ ▸ hu'
    · exact hrest y hy

/-- **The state `S` with its parts**: the watch store `st`, the trail `tr`, the assignment `A`,
the head of the queue `q` and the count `p` of propagations. While the queue is processed, these
are arguments of the loops, held apart from the rest of the state, so that moving a watch,
propagating a literal or moving the head updates them without rebuilding the state; the invariants
of the loops are stated on `S.withParts st tr A q p`. -/
@[expose] def WExec.withParts (S : WExec φ) (st : WatchStore) (tr : ATrail) (A : Assign)
    (q p : ℕ) : WExec φ :=
  { S with
    store := st, exec := { S.exec with tr := tr }, assign := A, qhead := q
    stats := { S.stats with propagations := p } }

/-- Propagating a literal of key `l` on the parts of the state: the trail and the assignment get
it, with the clause numbered `id` as its reason. -/
private theorem WExec.withParts_propagateUnit (S : WExec φ) (st : WatchStore) (tr : ATrail)
    (A : Assign) (q p l id : ℕ) :
    (S.withParts st tr A q p).propagateUnit (litOfKey l) id =
      S.withParts st (tr.push l (id + 1)) (A.assign (litOfKey l)) q p := by
  simp only [WExec.propagateUnit, WExec.withParts, Exec.propagate, litCode_litOfKey]

/-- The result of visiting a watch list, from the state `S₀.withParts st tr A q p` of measure at
most `m` with `c` conflicts: done, with the parts of the state after the visit, or a conflict, with
a measure at most `m` and still `c` conflicts. The bounds are indices, so that every step of the
visit has the same result type and calls the next one in tail position; they are only used in
proofs. -/
inductive ProcResult (φ : CNF ℕ) (S₀ : WExec φ) (q p m c : ℕ) (t : Literal ℕ) : Type
  /-- Every watcher on the list was visited: the watch store, the trail and the assignment. -/
  | done (st : WatchStore) (tr : ATrail) (A : Assign) (h : (S₀.withParts st tr A q p).ProcInv t [])
      (hm : (S₀.withParts st tr A q p).measure ≤ m)
      (hc : (S₀.withParts st tr A q p).stats.conflicts = c)
  /-- A clause of the database is false. -/
  | conflict (S : WExec φ) (h : S.Inv) (e : ℕ × Clause ℕ) (he : e ∈ S.exec.db)
      (hconf : Trail.Falsifies S.M e.2) (hm : S.measure ≤ m) (hc : S.stats.conflicts = c)

-- The facts used only by the loop are private: the exposed `processFrom` names them only in tactic
-- proofs, which may use private declarations.

/-- The watchers of the first `n + 2` numbers of a watch list, read backwards: the one at `n`, then
those of the first `n`. -/
private theorem unpackWatchers_take_add_two {ws : Array ℕ} {n : ℕ} (hn : n + 2 ≤ ws.size) :
    unpackWatchers (ws.toList.take (n + 2)).reverse =
      ⟨ws[n], litOfKey ws[n + 1]⟩ :: unpackWatchers (ws.toList.take n).reverse := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem (by simp; omega),
    List.getElem?_eq_getElem (by simp; omega)]
  simp

/-- The first `m` numbers of a watch list but the first, when `m` is odd, have the same watchers,
read backwards, as the first `m`: the number left over is not read. -/
private theorem unpackWatchers_extract (ws : Array ℕ) {m : ℕ} (hm : m ≤ ws.size) :
    unpackWatchers (ws.extract (m % 2) m).toList.reverse =
      unpackWatchers (ws.toList.take m).reverse := by
  have hT : (ws.toList.take m).length = m := by simp; omega
  have hd : (ws.extract (m % 2) m).toList = (ws.toList.take m).drop (m % 2) := by
    rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_take]
  conv_rhs => rw [← List.take_append_drop (m % 2) (ws.toList.take m)]
  rw [List.reverse_append, unpackWatchers_append _ (by simp; omega),
    unpackWatchers_of_length_le_one (A := (List.take (m % 2) _).reverse) (by simp; omega),
    List.append_nil, hd]

/-- The numbers taken from a watch list at a conflict are pairs. -/
private theorem size_extract_mod_two (ws : Array ℕ) {m : ℕ} (hm : m ≤ ws.size) :
    (ws.extract (m % 2) m).size % 2 = 0 := by
  simp; omega

/-- The state `S` with `kept` as the watch list of `t.negate`. During the visit of that list, the
watchers kept are pushed on `kept`, an argument of the loop, and written into the store once, at the
end: the invariant of the visit is stated on `S.withKept t kept`. -/
@[expose] def WExec.withKept (S : WExec φ) (t : Literal ℕ) (kept : Array ℕ) : WExec φ :=
  { S with store := { S.store with watches := setWatch S.store.watches (negKey t) kept } }

private theorem WExec.withKept_putBack (S : WExec φ) (t : Literal ℕ) (kept : Array ℕ) (k b : ℕ) :
    (S.withKept t kept).putBack t k b = S.withKept t ((kept.push k).push b) := by
  simp only [WExec.withKept, WExec.putBack, addWatch_setWatch]

/-- **Restoring the watch list of `t.negate` after a conflict**: the watchers kept, then the
numbers `rest` of the watchers still to be visited, pairs of numbers. -/
theorem WExec.ProcInv.restore_inv {S : WExec φ} {t : Literal ℕ} {kept rest : Array ℕ}
    (h : (S.withKept t kept).ProcInv t (unpackWatchers rest.toList.reverse))
    (he : rest.size % 2 = 0) :
    (S.withKept t (kept ++ rest)).Inv ∧
      (S.withKept t (kept ++ rest)).measure = (S.withKept t kept).measure := by
  have hW : ∀ i, watchList (S.withKept t (kept ++ rest)).store.watches i =
      if i = negKey t then
        unpackWatchers rest.toList.reverse ++ watchList (S.withKept t kept).store.watches i
      else watchList (S.withKept t kept).store.watches i := by
    intro i
    simp only [WExec.withKept, watchList_setWatch]
    split
    · rw [Array.toList_append, List.reverse_append, unpackWatchers_append _ (by simpa using he)]
    · rfl
  refine ⟨⟨h.exec, ⟨h.sound, h.nodup, h.long, h.covers, fun k' hk' w hw => ?_, fun i y hy => ?_,
    h.covered⟩, h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above,
    h.order, h.assign, h.occurs⟩, rfl⟩
  · rw [hW]
    rcases h.listed k' hk' w hw with hl | ⟨rfl, hL⟩
    · split
      · exact mem_clauseIds_append.2 (.inr hl)
      · exact hl
    · simp only [litCode_negate, ↓reduceIte]
      exact mem_clauseIds_append.2 (.inl hL)
  · rw [hW] at hy
    split at hy
    · rcases List.mem_append.1 hy with hy | hy
      · exact h.pending y hy
      · exact h.blocker_mem _ y hy
    · exact h.blocker_mem i y hy

private theorem WExec.withKept_moveTo (S : WExec φ) (t : Literal ℕ) (kept : Array ℕ) {k j o x u : ℕ}
    (hx : x ≠ negKey t) :
    ({ S.withKept t kept with store := (S.withKept t kept).store.moveTo k j o x u } :
      WExec φ) =
      ({ S with store := S.store.moveTo k j o x u } : WExec φ).withKept t kept := by
  simp only [WExec.withKept, WatchStore.moveTo, addWatch_setWatch_comm _ (Ne.symm hx)]

/-- What a visit finds, by the key `u` of `t.negate`, meets its specification, read back on the
literals. -/
private theorem WExec.visitSpec_of {S : WExec φ} {t : Literal ℕ} {u k b : ℕ} {v : KeyVisit}
    (hu : u = litCode t.negate) (hA : S.assign.Agrees S.M) (hv : S.store.visit S.assign u k b = v) :
    VisitSpec S.store S.M t.negate ⟨k, litOfKey b⟩ v.lits := by
  subst hu; rw [← hv]; exact S.store.visit_spec hA t.negate k b

/-- **Visiting a watch list**, the array `ws` read backwards from position `n`, two numbers per
watcher, from a state of measure at most `m` with `c` conflicts: each watcher is visited in turn,
until a conflict. The array is read by position, and the list of the watchers still to visit,
`unpackWatchers (ws.toList.take n).reverse`, appears only in the invariant. Each step calls the
next in tail position, so the compiled visit is a loop. The falsified literal `u`, the negation of
`t`, is computed once, by the caller.

As in MiniSat, the state of the loop is in its arguments: the watch store `st`, the trail `tr` and
the assignment `A`, apart from the rest of the state (`WExec.withParts`), and the watchers kept,
pushed on the array `kept`, which the store gets once, at the end. A watcher kept costs two pushes,
a watch moved an update of the store, and a literal propagated a push on the trail and an update of
the assignment, none of them a rebuilt state. At a conflict, the store gets the watchers kept
followed by those still to be visited, the current one included. -/
@[expose]
def WExec.processFrom (t : Literal ℕ) (u : ℕ) (hu : u = litCode t.negate)
    (m c : ℕ) : (n : ℕ) → (ws kept : Array ℕ) → (S : WExec φ) → (st : WatchStore) →
    (tr : ATrail) → (A : Assign) → (q p : ℕ) → n ≤ ws.size →
    ((S.withParts st tr A q p).withKept t kept).ProcInv t
      (unpackWatchers (ws.toList.take n).reverse) →
    (S.withParts st tr A q p).measure ≤ m → (S.withParts st tr A q p).stats.conflicts = c →
    ProcResult φ S q p m c t
  | 0, _, kept, S, st, tr, A, q, p, _, h, hm, hc =>
    .done { st with watches := setWatch st.watches (negKey t) kept } tr A h hm hc
  | 1, ws, kept, S, st, tr, A, q, p, _, h, hm, hc =>
    .done { st with watches := setWatch st.watches (negKey t) kept } tr A
      (by rwa [unpackWatchers_of_length_le_one (by simp)] at h) hm hc
  | n + 2, ws, kept, S, st, tr, A, q, p, hn, h₀, hm, hc =>
    let k := ws[n]
    let b := ws[n + 1]
    have h : ((S.withParts st tr A q p).withKept t kept).ProcInv t
        (⟨k, litOfKey b⟩ :: unpackWatchers (ws.toList.take n).reverse) :=
      by exact unpackWatchers_take_add_two hn ▸ h₀
    have hn' : n ≤ ws.size := by omega
    have hA : ((S.withParts st tr A q p).withKept t kept).assign.Agrees
        ((S.withParts st tr A q p).withKept t kept).M := h.assign
    match hv : st.visit A u k b with
    | .skip =>
      have hs : VisitSpec ((S.withParts st tr A q p).withKept t kept).store
          ((S.withParts st tr A q p).withKept t kept).M t.negate ⟨k, litOfKey b⟩ .skip :=
        by exact WExec.visitSpec_of hu hA hv
      WExec.processFrom t u hu m c n ws ((kept.push k).push b) S st tr A q p hn'
        (by exact (S.withParts st tr A q p).withKept_putBack t kept k b ▸ h.skip hs) hm hc
    | .keep b' =>
      have hs : VisitSpec ((S.withParts st tr A q p).withKept t kept).store
          ((S.withParts st tr A q p).withKept t kept).M t.negate ⟨k, litOfKey b⟩
          (.keep (litOfKey b')) :=
        by exact WExec.visitSpec_of hu hA hv
      WExec.processFrom t u hu m c n ws ((kept.push k).push b') S st tr A q p hn'
        (by
          have h' := h.keep hs
          rw [litCode_litOfKey] at h'
          exact (S.withParts st tr A q p).withKept_putBack t kept k b' ▸ h') hm hc
    | .move j x b' =>
      have hs : VisitSpec ((S.withParts st tr A q p).withKept t kept).store
          ((S.withParts st tr A q p).withKept t kept).M t.negate ⟨k, litOfKey b⟩
          (.move j (litOfKey x) (litOfKey b')) :=
        by exact WExec.visitSpec_of hu hA hv
      have hx : x ≠ negKey t := by
        obtain ⟨-, -, -, -, -, -, -, -, -, hxf, -⟩ := hs
        intro hxt
        apply hxf
        rw [hxt, litOfKey_negKey, negate_negate]
        exact h.queue_trail t h.t_mem
      -- the store is updated in place: the loop is its only holder
      WExec.processFrom t u hu m c n ws kept S (st.moveTo k j b' x u) tr A q p hn' (by
          have h' := h.move hs
          simp only [litCode_litOfKey, ← hu] at h'
          have h'' := (S.withParts st tr A q p).withKept_moveTo t kept hx ▸ h'
          exact h'') hm hc
    | .unit l id =>
      have hs : VisitSpec ((S.withParts st tr A q p).withKept t kept).store
          ((S.withParts st tr A q p).withKept t kept).M t.negate ⟨k, litOfKey b⟩
          (.unit (litOfKey l) id) :=
        by exact WExec.visitSpec_of hu hA hv
      have hun := h.unit hs
      have heq : (((S.withParts st tr A q p).withKept t kept).propagateUnit (litOfKey l) id).putBack
            t k (litCode (litOfKey l)) =
          (S.withParts st (tr.push l (id + 1)) (A.assign (litOfKey l)) q p).withKept t
            ((kept.push k).push l) := by
        rw [litCode_litOfKey, ← S.withParts_propagateUnit st tr A q p l id]
        exact ((S.withParts st tr A q p).propagateUnit (litOfKey l) id).withKept_putBack t kept _ _
      have hlt : (S.withParts st (tr.push l (id + 1)) (A.assign (litOfKey l)) q p).measure <
          (S.withParts st tr A q p).measure := by
        have h2 := hun.2
        rw [heq] at h2
        exact h2
      WExec.processFrom t u hu m c n ws ((kept.push k).push l) S st (tr.push l (id + 1))
        (A.assign (litOfKey l)) q p hn' (heq ▸ hun.1) (hlt.le.trans hm) hc
    | .conflict id =>
      have hs : VisitSpec ((S.withParts st tr A q p).withKept t kept).store
          ((S.withParts st tr A q p).withKept t kept).M t.negate ⟨k, litOfKey b⟩ (.conflict id) :=
        by exact WExec.visitSpec_of hu hA hv
      match hcl₀ : S.exec.log.clause? id with
      | some cl =>
        have hcl : ((S.withParts st tr A q p).withKept t kept).exec.log.clause? id = some cl := hcl₀
        have hcc := h.conflict_clause hs
        -- the watchers still to be visited, the current one included, as pairs of numbers
        let rest := ws.extract ((n + 2) % 2) (n + 2)
        have hr := WExec.ProcInv.restore_inv (rest := rest)
          (by rw [unpackWatchers_extract ws hn]; exact h₀) (by exact size_extract_mod_two ws hn)
        .conflict ((S.withParts st tr A q p).withKept t (kept ++ rest)) hr.1 (id, cl)
          (by obtain ⟨c', hc', hlog, -⟩ := hcc; rw [hlog] at hcl; cases hcl; exact hc')
          (by obtain ⟨c', -, hlog, hf⟩ := hcc; rw [hlog] at hcl; cases hcl; exact hf)
          (hr.2.le.trans hm) hc
      | none =>
        have hcl : ((S.withParts st tr A q p).withKept t kept).exec.log.clause? id = none := hcl₀
        absurd hcl (by obtain ⟨c', -, hlog, -⟩ := h.conflict_clause hs; simp [hlog])
    | .drop =>
      have hs : VisitSpec ((S.withParts st tr A q p).withKept t kept).store
          ((S.withParts st tr A q p).withKept t kept).M t.negate ⟨k, litOfKey b⟩ .drop :=
        by exact WExec.visitSpec_of hu hA hv
      WExec.processFrom t u hu m c n ws kept S st tr A q p hn' (h.drop hs) hm hc

/-- The result of processing the queue from a state of measure at most `m` with `c` conflicts:
stopped, at an empty queue or after enough literals, with a lower measure, or a conflict, with a
measure at most `m`; with still `c` conflicts either way. -/
inductive QueueResult (φ : CNF ℕ) (m c : ℕ) : Type
  /-- The literals processed, with no conflict. -/
  | stop (T : WExec φ) (hT : T.Inv) (hm : T.measure < m) (hc : T.stats.conflicts = c)
  /-- A clause of the database is false. -/
  | conflict (T : WExec φ) (hT : T.Inv) (e : ℕ × Clause ℕ) (he : e ∈ T.exec.db)
      (hconf : Trail.Falsifies T.M e.2) (hm : T.measure ≤ m) (hc : T.stats.conflicts = c)

/-- **Processing the queue**, from the state `S₀.withParts st tr A q p` with the literal at the
head `q` still to process: the watch list of its negation is visited (`WExec.processFrom`), and,
with no conflict, the head moves past it and the next literal is processed, until the queue is
empty, a conflict, or `fuel` more literals. As in MiniSat's `propagate`, the parts of the state
are the arguments of the loop, so that the state is rebuilt once, at the end, instead of once per
literal. Each literal processed lowers the measure, so the result has a lower measure than the
state processed. -/
@[expose] def WExec.processQueue (S₀ : WExec φ) (m c : ℕ) :
    (fuel : ℕ) → (st : WatchStore) → (tr : ATrail) → (A : Assign) → (q p : ℕ) → q < tr.size →
    (S₀.withParts st tr A q p).Inv → (S₀.withParts st tr A q p).measure ≤ m →
    (S₀.withParts st tr A q p).stats.conflicts = c → QueueResult φ m c
  | fuel, st, tr, A, q, p, hq, hS, hm, hc =>
    -- the literal at the head of the queue
    let t := tr.lit q
    have ht : t ∈ (S₀.withParts st tr A q p).queue := by
      rw [WExec.queue_of_lt hq]; exact List.mem_cons_self
    -- the watch list is read before its slot is emptied, so that it is not shared
    let ws := st.watches.getD (negKey t) #[]
    let st₀ : WatchStore := { st with watches := setWatch st.watches (negKey t) #[] }
    have hS₀ : S₀.withParts st₀ tr A q (p + 1) = (S₀.withParts st tr A q p).start t := rfl
    -- the watchers kept go to a fresh array, twice as long as the list, so that they are pushed in
    -- place, and the watchers added to the list later are pushed in place too
    match WExec.processFrom t (negKey t) (litCode_negate t).symm m c ws.size ws
        (Array.emptyWithCapacity (2 * ws.size)) S₀ st₀ tr A q (p + 1) le_rfl
        (by
          rw [List.take_of_length_le (by simp), hS₀]
          have hk : ((S₀.withParts st tr A q p).start t).withKept t
              (Array.emptyWithCapacity (2 * ws.size)) = (S₀.withParts st tr A q p).start t := by
            simp only [WExec.withKept, WExec.start, setWatch_setWatch]; rfl
          have := WExec.start_procInv hS ht rfl
          rw [hk]
          rwa [watchList, litCode_negate] at this) (by rw [hS₀]; exact hm) (by rw [hS₀]; exact hc)
    with
    | .done st' tr' A' h hm' hc' =>
      -- finishing `t` moves the head past it
      have hfin := WExec.finish_inv h
      have hlt : (S₀.withParts st' tr' A' (q + 1) (p + 1)).measure < m :=
        lt_of_lt_of_le hfin.2 hm'
      match fuel with
      | 0 => .stop (S₀.withParts st' tr' A' (q + 1) (p + 1)) hfin.1 hlt hc'
      | fuel + 1 =>
        if hq' : q + 1 < tr'.size then
          WExec.processQueue S₀ m c fuel st' tr' A' (q + 1) (p + 1) hq' hfin.1 hlt.le hc'
        else .stop (S₀.withParts st' tr' A' (q + 1) (p + 1)) hfin.1 hlt hc'
    | .conflict T hT e he hconf hm' hc' => .conflict T hT e he hconf hm' hc'

/-! ### Moves at the top level -/

/-- The literals below a decision of a trail are on the trail. -/
theorem lits_below {N M₀ : Trail} {d : Literal ℕ} {x : Literal ℕ}
    (hx : x ∈ Trail.lits M₀) : x ∈ Trail.lits (N ++ ⟨d, true⟩ :: M₀) := by
  rw [lits_append]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)

/-- A learned clause has no repetitions. -/
theorem Learned.dedupLits_clause {log : LRATLog φ} {A M₀ : Trail} (L : Learned log A M₀) :
    dedupLits L.clause = L.clause :=
  dedupKey_of_nodup litCode_injective L.nodup


/-- The activities `A` and the variable order `H` after a conflict meeting the variables `vs`,
listed once each, with VSIDS: the variables are bumped, and those in the heap move up
(`VarOrder.bumpDistinct`). -/
@[expose] def bumpOrderWith (o : Options) (A : Activity) (H : VarOrder) (vs : List ℕ) :
    Activity × VarOrder :=
  if o.vsids then VarOrder.bumpDistinct A H vs else (A, H)


/-- The variables of the entries `M`, as `Trail.vars` of their trail (`XTrail.vars_eq`), mapped in
one pass. -/
@[expose] def XTrail.vars (M : XTrail) : List ℕ := M.map fun e => e.lit.1

@[simp] theorem XTrail.vars_eq (M : XTrail) : XTrail.vars M = Trail.vars (XTrail.trail M) := by
  simp [XTrail.vars, XTrail.trail, Trail.vars, Function.comp_def, XEntry.var_entry]

/-- **Unassigning the variables of the entries `M`**, folding over them, without listing them:
`Assign.unassign` of their variables (`Assign.unassignEntries_eq`). -/
@[expose] def Assign.unassignEntries (A : Assign) (M : XTrail) : Assign :=
  M.foldl (fun A e => A.clear e.lit.1) A

theorem Assign.unassignEntries_eq (A : Assign) (M : XTrail) :
    A.unassignEntries M = A.unassign (Trail.vars (XTrail.trail M)) := by
  induction M generalizing A with
  | nil => rfl
  | cons e M ih =>
    simp only [Assign.unassignEntries, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [Assign.unassign, Trail.vars, XTrail.trail, XEntry.var_entry]

/-- **Saving the phases of the literals of the entries `M`**, folding over them in order: what
`Phases.save` does on their trail (`Phases.saveEntries_eq`), without listing them. -/
@[expose] def Phases.saveEntries (P : Phases) (M : XTrail) : Phases :=
  M.foldl (fun P e => P.set e.lit.1 e.lit.2) P

theorem Phases.saveEntries_eq (P : Phases) (M : XTrail) :
    P.saveEntries M = P.save (XTrail.trail M) := by
  simp [Phases.saveEntries, Phases.save, XTrail.trail, Trail.lits, List.foldl_map]

/-- The variable order `H` after a conflict undoing the entries `U`, with VSIDS: the variables
undone are inserted with the activities `A`, unless they are in the heap, as MiniSat's
`insertVarOrder` does. -/
@[expose] def reorderedWith (o : Options) (H : VarOrder) (A : Activity) (U : XTrail) : VarOrder :=
  if o.vsids then U.foldl (fun H e => H.insert A e.lit.1) H else H

/-- The variables undone are inserted as `VarOrder.addAll` inserts them, without listing them. -/
theorem reorderedWith_eq (o : Options) (H : VarOrder) (A : Activity) (U : XTrail) :
    reorderedWith o H A U = if o.vsids then H.addAll A (XTrail.vars U) else H := by
  simp only [reorderedWith, VarOrder.addAll, XTrail.vars, List.foldl_map]

/-- The phases `P` after undoing the entries `U`: those of the literals undone are saved, if phase
saving is on. -/
@[expose] def savedWith (o : Options) (P : Phases) (U : XTrail) : Phases :=
  if o.phaseSaving then P.saveEntries U else P

/-- The phases after undoing the entries `U`: those of the literals undone are saved, if phase
saving is on. -/
@[expose] def WExec.saved (S : WExec φ) (U : XTrail) : Phases := savedWith S.opts S.phase U

/-- One more conflict. -/
@[expose] def Stats.conflict (s : Stats) : Stats := { s with conflicts := s.conflicts + 1 }

/-- The reduction `R` after a conflict meeting the clauses `used` and learning the clause numbered
`id`, the log's next number being `next`, stored if `stored`: updated, if reduction is on. -/
@[expose]
def reducedWith (o : Options) (R : Reduction) (used : List ℕ) (id next : ℕ) (stored : Bool) :
    Reduction :=
  if o.reduce then R.learn used id next stored else R

/-- The reduction after a conflict learning `L`, stored if `stored`: updated, if reduction is on. -/
@[expose] def WExec.reduced (S : WExec φ) {sp : Split} (L : S.exec.LearnedAt sp) (stored : Bool) :
    Reduction :=
  reducedWith S.opts S.red L.used L.id (L.id + 1) stored

/-- One more conflict, learning a clause of `k` different literals, `k₀` before minimization. -/
@[expose] def Stats.learn (s : Stats) (k₀ k : ℕ) : Stats :=
  { s with
    conflicts := s.conflicts + 1, maxLiterals := s.maxLiterals + k₀, literals := s.literals + k }

/-- **Assigning the current level** on top of `A`, read from the arrays of the trail: the
decision at position `p`, then the entries above it, oldest first. It is `Assign.assignTrail` of
the level read back (`ATrail.assignLevelAt_eq`). -/
@[expose] def ATrail.assignLevelAt (T : ATrail) (p : ℕ) (A : Assign) : Assign :=
  T.foldUp (fun A c _ => A.assign (litOfKey c)) p (T.size - p) A

theorem ATrail.assignLevelAt_eq (T : ATrail) {p : ℕ} (A : Assign) (hp : p < T.size) :
    T.assignLevelAt p A = A.assignTrail (T.level p) := by
  rw [assignLevelAt, foldUp_eq, show T.size - p = (T.size - (p + 1)) + 1 by omega,
    seg_succ_bottom, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, litOfKey_litCode, entry_lit, ATrail.level]
  generalize T.seg (p + 1) (T.size - (p + 1)) = M
  induction M with
  | nil => simp [Assign.assignTrail]
  | cons e M ih =>
    rw [List.foldr_cons, ih, XTrail.trail_cons, List.cons_append, Assign.assignTrail_cons,
      XEntry.lit_entry]

/-- The marks after an analysis: the array the analysis returns, with the variables of the
current level cleared, which leaves no value. -/
@[expose] def clearedMarks {log : LRATLog φ} (sp : Split)
    (L : Learned log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)) :
    {A : Assign // ∀ v, A.value v = none} :=
  ⟨(L.marks.unassignEntries sp.above).clear sp.decision.1, fun v => by
    rw [Assign.value_clear, Assign.unassignEntries_eq, Assign.value_unassign]
    split
    · rfl
    split
    · rfl
    rename_i h₁ h₂
    exact L.marks_none v (by
      simp only [Trail.vars, List.map_append, List.mem_append, List.map_cons, List.map_nil,
        List.mem_singleton] at h₂ ⊢
      exact fun h => h.elim h₂ h₁)⟩

/-- The marks for the backjump: the variables of the learned clause, marked in the array the
analysis returned once its level is cleared. -/
@[expose] def jumpMarks {log : LRATLog φ} (sp : Split)
    (L : Learned log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)) :
    Assign :=
  (clearedMarks sp L).val.markLits L.clause

/-- Whether a variable is marked for the backjump. It reads one array, built once: the function is
`Assign.assigned` applied to `jumpMarks sp L`. -/
@[expose] def jumpMarked {log : LRATLog φ} (sp : Split)
    (L : Learned log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)) :
    ℕ → Bool :=
  (jumpMarks sp L).assigned

/-- **The marked variables are those of the learned clause**: the array the analysis returns is
cleared before the variables of the clause are marked. -/
theorem jumpMarked_iff {log : LRATLog φ} (sp : Split)
    (L : Learned log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below))
    (v : ℕ) : jumpMarked sp L v = true ↔ v ∈ L.clause.map Prod.fst := by
  by_cases hv : v ∈ L.clause.map Prod.fst
  · simp [jumpMarked, jumpMarks, Assign.markLits_eq, Assign.assigned_eq_isSome, Assign.value_mark,
      hv]
  · simp only [jumpMarked, jumpMarks, Assign.markLits_eq, Assign.assigned_eq_isSome,
      Assign.value_mark, hv, ite_false,
      (clearedMarks sp L).property v, Option.isSome_none, Bool.false_eq_true]

theorem jumpMarked_of_mem {log : LRATLog φ} (sp : Split)
    (L : Learned log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)) :
    ∀ v ∈ L.clause.map Prod.fst, jumpMarked sp L v = true := fun v hv =>
  (jumpMarked_iff sp L v).2 hv

/-- **The level kept by the backjump has a variable of the learned clause**: either the trail
kept has no decision, or its top level, the decision `d` with the entries `N` above it, has the
variable of `d` or of an entry of `N` in the learned clause. -/
theorem ExecL.jump_kept_learned {S : ExecL φ} (sp : Split) (L : S.LearnedAt sp) :
    (∀ x ∈ (S.jump sp (jumpMarked sp L)).2, x.entry.decision = false) ∨
      ∃ N d M₀, (S.jump sp (jumpMarked sp L)).2 = N ++ .decision d :: M₀ ∧
        (∀ x ∈ N, x.entry.decision = false) ∧
        (d.1 ∈ L.clause.map Prod.fst ∨ ∃ x ∈ N, x.entry.lit.1 ∈ L.clause.map Prod.fst) := by
  refine (ExecL.jump_kept sp).imp id fun ⟨N, d, M₀, h, hN, hm⟩ => ⟨N, d, M₀, h, hN, ?_⟩
  simpa only [jumpMarked_iff] using hm

/-- The marks after the backjump: the marks `A` of the backjump, those of the learned clause
cleared again, which leaves no value. -/
@[expose] def afterJumpMarks {log : LRATLog φ} (sp : Split)
    (L : Learned log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below))
    (A : Assign) (hA : A = jumpMarks sp L) : {A : Assign // ∀ v, A.value v = none} :=
  ⟨A.unassignLits L.clause, Assign.unassignLits_eq A L.clause ▸
    Assign.value_unassign_eq_none fun v hv => by
    rw [hA, jumpMarks, Assign.markLits_eq, Assign.value_mark,
      ite_eq_right_iff.2 fun h => absurd h hv]
    exact (clearedMarks sp L).property v⟩

/-- The state with its marks taken out, replaced by an empty array, so that the marks can be
updated in place. -/
@[expose] def WExec.dropMarks (S : WExec φ) : WExec φ :=
  { S with marks := ⟨⟨#[]⟩, fun v => by simp [Assign.value]⟩ }

/-- The invariant does not read the marks. -/
theorem WExec.Inv.dropMarks {S : WExec φ} (h : S.Inv) : S.dropMarks.Inv :=
  ⟨h.exec, h.store, h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above,
    h.order, h.assign, h.occurs⟩

/-! ### The backjump on the arrays of the trail -/

/-- The marks for the backjump, read from the arrays of the trail: `jumpMarks` of the split at the
newest decision `p` (`jumpMarksAt_eq`). -/
@[expose] def jumpMarksAt {log : LRATLog φ} (T : ATrail) (p : ℕ)
    (L : Learned log (XTrail.trail (T.splitAt p).above ++ [⟨(T.splitAt p).decision, true⟩])
      (XTrail.trail (T.splitAt p).below)) : Assign :=
  ((T.foldDown (fun A c _ => A.clear (c / 2)) (p + 1) (T.size - (p + 1)) L.marks).clear
    (T.lits.getD p 0 / 2)).markLits L.clause

theorem jumpMarksAt_eq {log : LRATLog φ} (T : ATrail) (p : ℕ)
    (L : Learned log (XTrail.trail (T.splitAt p).above ++ [⟨(T.splitAt p).decision, true⟩])
      (XTrail.trail (T.splitAt p).below)) :
    jumpMarksAt T p L = jumpMarks (T.splitAt p) L := by
  simp only [jumpMarksAt, jumpMarks, clearedMarks, ATrail.foldDown_eq, Assign.unassignEntries,
    litCode_div_two]
  rfl

/-- What undoing the entries of a backjump leaves (`ATrail.undoGo`). -/
structure Undone where
  /-- The assignment with the variables undone unassigned. -/
  assign : Assign
  /-- The variable order with the variables undone put back. -/
  order : VarOrder
  /-- The phases with those of the literals undone saved. -/
  phase : Phases
  /-- The decisions among the entries undone. -/
  decisions : ℕ

/-- **Undoing the `k` entries from position `lo` up**, newest first, in one loop over the arrays:
their variables are unassigned, put back in the variable order with VSIDS, their phases saved with
phase saving, and the decisions among them counted. Each part is the backjump's operation on the
entries `T.seg lo k` (`ATrail.undoGo_assign`, `ATrail.undoGo_order`, `ATrail.undoGo_phase`,
`ATrail.undoGo_decisions`). -/
@[expose] def ATrail.undoGo (T : ATrail) (o : Options) (act : Activity) (lo : ℕ) :
    ℕ → Assign → VarOrder → Phases → ℕ → Undone
  | 0, A, H, P, n => ⟨A, H, P, n⟩
  | k + 1, A, H, P, n =>
    let c := T.lits.getD (lo + k) 0
    T.undoGo o act lo k (A.clear (c / 2)) (if o.vsids then H.insert act (c / 2) else H)
      (if o.phaseSaving then P.set (c / 2) (c % 2 == 1) else P)
      (if T.rsns.getD (lo + k) 0 == 0 then n + 1 else n)

theorem ATrail.undoGo_assign (T : ATrail) (o : Options) (act : Activity) (lo : ℕ) :
    ∀ (k : ℕ) (A : Assign) (H : VarOrder) (P : Phases) (n : ℕ),
      (T.undoGo o act lo k A H P n).assign = A.unassignEntries (T.seg lo k)
  | 0, _, _, _, _ => rfl
  | k + 1, A, H, P, n => by
    rw [undoGo, ATrail.undoGo_assign T o act lo k, seg_succ, Assign.unassignEntries,
      Assign.unassignEntries, List.foldl_cons, entry_lit]
    rfl

theorem ATrail.undoGo_order (T : ATrail) (o : Options) (act : Activity) (lo : ℕ) :
    ∀ (k : ℕ) (A : Assign) (H : VarOrder) (P : Phases) (n : ℕ),
      (T.undoGo o act lo k A H P n).order = reorderedWith o H act (T.seg lo k)
  | 0, _, _, _, _ => by unfold reorderedWith; split <;> rfl
  | k + 1, A, H, P, n => by
    rw [undoGo, ATrail.undoGo_order T o act lo k, seg_succ]
    unfold reorderedWith
    cases o.vsids
    · rfl
    · rw [List.foldl_cons, entry_lit]; rfl

theorem ATrail.undoGo_phase (T : ATrail) (o : Options) (act : Activity) (lo : ℕ) :
    ∀ (k : ℕ) (A : Assign) (H : VarOrder) (P : Phases) (n : ℕ),
      (T.undoGo o act lo k A H P n).phase = savedWith o P (T.seg lo k)
  | 0, _, _, _, _ => by unfold savedWith; split <;> rfl
  | k + 1, A, H, P, n => by
    rw [undoGo, ATrail.undoGo_phase T o act lo k, seg_succ]
    unfold savedWith
    cases o.phaseSaving
    · rfl
    · rw [Phases.saveEntries, Phases.saveEntries, List.foldl_cons, entry_lit]; rfl

theorem ATrail.undoGo_decisions (T : ATrail) (o : Options) (act : Activity) (lo : ℕ) :
    ∀ (k : ℕ) (A : Assign) (H : VarOrder) (P : Phases) (n : ℕ),
      (T.undoGo o act lo k A H P n).decisions = n + (T.seg lo k).countP XEntry.isDecision
  | 0, _, _, _, _ => rfl
  | k + 1, A, H, P, n => by
    rw [undoGo, ATrail.undoGo_decisions T o act lo k, seg_succ, List.countP_cons,
      isDecision_entry]
    split <;> simp_all
    omega

/-- **The variable of the newest marked entry** below position `i`, scanning down, or `0` if there
is none. Below the newest decision, with the variables of the learned clause marked, it is the
variable of the literal of the clause false at the highest level, the backjump level. -/
@[expose] def ATrail.topMarked (T : ATrail) (marked : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if marked (T.lits.getD i 0 / 2) then T.lits.getD i 0 / 2 else T.topMarked marked i

/-- **The clause `C` with its literal on the variable `w` second**, if it has one after its first
literal. Stored with this order, a learned clause watches its asserting literal and, as in
MiniSat, the literal false at the backjump level, the last of the others to become unassigned when
backtracking, so that the clause is not left unit with a false watched literal. -/
@[expose] def secondOn (w : ℕ) : Clause ℕ → Clause ℕ
  | l :: rest =>
    match rest.find? (fun y => y.1 == w) with
    | some y => l :: y :: rest.erase y
    | none => l :: rest
  | [] => []

/-- Moving a literal second permutes the clause. -/
theorem perm_secondOn (w : ℕ) : ∀ C : Clause ℕ, (secondOn w C).Perm C
  | [] => List.Perm.refl _
  | l :: rest => by
    rw [secondOn]
    split
    · rename_i y hy
      exact ((List.perm_cons_erase (List.mem_of_find?_eq_some hy)).symm).cons l
    · exact List.Perm.refl _

/-- **What `ATrail.topMarked` finds**: the variable of the newest entry below position `i` whose
variable is marked, or `0` if there is none. -/
theorem ATrail.topMarked_eq (T : ATrail) (marked : ℕ → Bool) : ∀ i,
    T.topMarked marked i = (((T.seg 0 i).find? fun e => marked e.lit.1).map (·.lit.1)).getD 0
  | 0 => rfl
  | i + 1 => by
    have h : (T.entry i).lit.1 = T.lits.getD i 0 / 2 := by rw [entry_lit]; rfl
    simp only [topMarked, seg_succ, List.find?_cons, Nat.zero_add, h,
      ATrail.topMarked_eq T marked i]
    cases marked (T.lits.getD i 0 / 2) <;> simp [h]

/-- **Moving the literal on `w` second**: if a literal after the first is on the variable `w`,
the second literal is on `w`. -/
theorem secondOn_var {w : ℕ} {l : Literal ℕ} {rest : Clause ℕ} (h : ∃ y ∈ rest, y.1 = w) :
    ∃ y rest', secondOn w (l :: rest) = l :: y :: rest' ∧ y.1 = w := by
  rw [secondOn]
  split
  · rename_i y hy
    exact ⟨y, _, rfl, by simpa using List.find?_some hy⟩
  · rename_i hn
    obtain ⟨y, hy, hyw⟩ := h
    exact absurd (List.find?_eq_none.1 hn y hy) (by simp [hyw])

/-- Moving a literal second keeps the first literal. -/
theorem secondOn_cons (w : ℕ) (l : Literal ℕ) (rest : Clause ℕ) :
    ∃ rest', secondOn w (l :: rest) = l :: rest' := by
  rw [secondOn]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **Backjump and Learn with watches**, at the newest decision, at position `p` of the trail: the
state after the conflict, with the learned clause in the store, watching its asserting literal, or
among the short clauses, and the asserting literal queued. The entries undone are those from the
backjump point `ATrail.cutPos` up, read from the arrays of the trail and then popped
(`Exec.afterConflictAt`). The variables met by the analysis are bumped and, with those undone, put
back in the variable order, and the phases of the literals undone are saved; the statistics count
`k₀` literals before minimization. The fields are taken out of `S` first, so that its arrays are
updated in place. The marks of the backjump are built once, read by the backjump and cleared after
it. -/
@[expose] def WExec.afterConflict (S : WExec φ) (p : ℕ) (L : S.exec.LearnedAt (S.exec.tr.splitAt p))
    (k₀ : ℕ) : WExec φ :=
  let exec := S.exec
  let assign := S.assign
  let occurs := S.occurs
  let store := S.store
  let short := S.short
  let act := S.act
  let order := S.order
  let phase := S.phase
  let red := S.red
  let level := S.level
  let simpAssigns := S.simpAssigns
  let opts := S.opts
  let stats := S.stats
  let T := exec.tr
  let marks := jumpMarksAt T p L
  let q := T.cutPos marks.assigned p
  let pr := bumpOrderWith opts act order L.seen
  let A := pr.1
  -- the entries undone, read once: unassigned, reinserted, their phases saved, decisions counted
  let u := T.undoGo opts A q (T.size - q) assign pr.2 phase 0
  let assign := u.assign.assign L.lit
  let order := u.order
  let phase := u.phase
  let occurs := occurs.markLits L.clause
  let level := level - u.decisions
  let k := L.clause.length
  let stats := stats.learn k₀ k
  if 2 ≤ k then
    -- a learned clause's number is the log's next one, beyond the clauses of `φ`
    -- (`Learned.isLearntId_id`): it counts as learned, with no test of `φ.length`
    let red := reducedWith opts red L.used L.id (L.id + 1) true
    -- the literal false at the backjump level is watched second
    let store := store.addClause L.id (secondOn (T.topMarked marks.assigned p) L.clause)
    ⟨exec.afterConflictAt L q, assign, occurs, store, q, short, A, order,
      phase, red, level, simpAssigns, opts, stats,
      afterJumpMarks (T.splitAt p) L marks (jumpMarksAt_eq T p L)⟩
  else
    let red := reducedWith opts red L.used L.id (L.id + 1) false
    ⟨exec.afterConflictAt L q, assign, occurs, store, q, (L.id, L.clause) :: short, A,
      order, phase, red, level, simpAssigns, opts, stats,
      afterJumpMarks (T.splitAt p) L marks (jumpMarksAt_eq T p L)⟩

theorem WExec.afterConflict_spec {S : WExec φ} (hS : S.Inv) {e : ℕ × Clause ℕ}
    (he : e ∈ S.exec.db) (hconf : Trail.Falsifies S.M e.2) {p : ℕ} (hp : S.exec.tr.IsNewest p)
    (L : S.exec.LearnedAt (S.exec.tr.splitAt p)) (k₀ : ℕ) :
    (S.afterConflict p L k₀).Inv ∧ (S.afterConflict p L k₀).measure < S.measure := by
  have hsp : XTrail.split S.exec.toL.trail = some (S.exec.tr.splitAt p) := hp.split
  have hspec :=
    Exec.afterConflict_spec hS.exec he hconf hp L (jumpMarked_of_mem (S.exec.tr.splitAt p) L)
  obtain ⟨hUK, ⟨J, d', hJ⟩, hfalseK, hundefK⟩ :=
    ExecL.jump_spec hsp L (jumpMarked_of_mem (S.exec.tr.splitAt p) L)
  rw [Exec.jump_eq _ hp] at hUK hJ hfalseK hundefK
  have hq := Exec.cutPos_le hp (jumpMarked (S.exec.tr.splitAt p) L)
  set q := S.exec.tr.cutPos (jumpMarked (S.exec.tr.splitAt p) L) p with hqdef
  set U := S.exec.tr.seg q (S.exec.tr.size - q) with hUdef
  set K := S.exec.tr.seg 0 q with hKdef
  set E := S.exec.afterConflictAt L q with hEdef
  have hEL : E.toL = S.exec.toL.afterConflictWith L K := Exec.toL_afterConflictAt _ L hq
  have hEinv : E.Inv := hspec.1
  have hErank : rank φ.vars E.state < rank φ.vars S.exec.state := hspec.2
  have hsplit : S.M = XTrail.trail J ++ ⟨d', true⟩ :: XTrail.trail K := by
    change XTrail.trail S.exec.toL.trail = _
    conv_lhs => rw [hUK, hJ]
    simp [XTrail.trail_append, XTrail.trail_cons]
  have hMUK : S.M = XTrail.trail U ++ XTrail.trail K := by
    change XTrail.trail S.exec.toL.trail = _
    conv_lhs => rw [hUK]
    exact XTrail.trail_append _ _
  have hM' : XTrail.trail E.trail = ⟨L.lit, false⟩ :: XTrail.trail K := by
    change XTrail.trail E.toL.trail = _
    rw [hEL]; rfl
  have hdb' : E.db = (L.id, L.clause) :: S.exec.db := rfl
  have hnodup' := hEinv.run.nodup
  change (Trail.vars (XTrail.trail E.trail)).Nodup at hnodup'
  rw [hM'] at hnodup'
  have hlitM' : L.lit ∈ Trail.lits (⟨L.lit, false⟩ :: XTrail.trail K) :=
    List.mem_cons_self
  -- the processed literals after backjumping are below the decision, hence processed before
  have hbelow : ∀ x, Processed (⟨L.lit, false⟩ :: XTrail.trail K) [L.lit] x →
      x ∈ Trail.lits (XTrail.trail K) :=
    fun x ⟨hx, hxq⟩ => (List.mem_cons.1 hx).resolve_left (by simpa using hxq)
  have hproc : ∀ x, Processed (⟨L.lit, false⟩ :: XTrail.trail K) [L.lit] x →
      Processed S.M S.queue x := by
    intro x hx
    have hx' := hbelow x hx
    refine ⟨by rw [hsplit]; exact lits_below hx', fun hq => ?_⟩
    exact hS.queue_above x hq _ _ _ hsplit hx'
  have hstore := hS.store.weaken hproc fun b w₁ w₂ h₁ h₂ hs =>
    hs.backjump hsplit (hbelow _ h₁) (hbelow _ h₂) _
  have hlitneg : ¬ Processed (⟨L.lit, false⟩ :: XTrail.trail K) [L.lit] L.lit.negate :=
    fun h => Trail.negate_not_mem hnodup' hlitM' h.1
  have hqueue : ∀ x ∈ [L.lit], ∀ N d M₀,
      (⟨L.lit, false⟩ :: XTrail.trail K : Trail) = N ++ ⟨d, true⟩ :: M₀ →
      x ∉ Trail.lits M₀ := by
    intro x hx N d M₀ hN hxM₀
    rw [List.mem_singleton] at hx
    subst hx
    cases N with
    | nil => simp at hN
    | cons y N =>
      simp only [List.cons_append, List.cons.injEq] at hN
      apply hundefK
      rw [congrArg Trail.vars hN.2]
      exact Trail.mem_vars_of_mem_lits (lits_below hxM₀)
  -- the assignment undoes the literals above the decision, then asserts the learned literal
  have hassign : ((S.assign.unassignEntries U).assign L.lit).Agrees
      (⟨L.lit, false⟩ :: XTrail.trail K) := by
    rw [Assign.unassignEntries_eq]
    have hA := hS.assign
    have hnd := hS.exec.run.nodup
    rw [hMUK] at hA
    change (Trail.vars S.M).Nodup at hnd
    rw [hMUK, vars_append] at hnd
    exact (hA.drop fun v hv => List.disjoint_of_nodup_append hnd hv).cons
      (List.nodup_cons.1 hnodup').1 false
  -- the variables met and undone are put back in the order; the others keep their entries, and
  -- bumping did not raise their activities
  have horder : S.opts.vsids = true → ∀ T : WExec φ,
      T.order = reorderedWith S.opts (bumpOrderWith S.opts S.act S.order L.seen).2
        (bumpOrderWith S.opts S.act S.order L.seen).1 U →
      T.act = (bumpOrderWith S.opts S.act S.order L.seen).1 →
      T.exec = E → T.occurs = S.occurs.mark (L.clause.map Prod.fst) → T.OrderInv := by
    intro hv T hTo hTa hTe hTocc
    have hS' := hS.order hv
    simp only [reorderedWith_eq, bumpOrderWith, hv, ↓reduceIte, XTrail.vars_eq,
      VarOrder.bumpDistinct_eq _ _ L.seen_nodup] at hTo hTa
    -- bumping keeps the heap and its variables; the variables undone are inserted
    have hk := VarOrder.bump_spec L.seen 19 hS'.wf hS'.pos
    obtain ⟨hwf₂, hp₂, hs₂, hm₂⟩ := VarOrder.addAll_spec (VarOrder.bump S.act S.order L.seen).1
      (VarOrder.bump S.act S.order L.seen).2 (Trail.vars (XTrail.trail U)) hk.pos
    have hTM : T.M = ⟨L.lit, false⟩ :: XTrail.trail K := by
      change XTrail.trail T.exec.trail = _; rw [hTe]; exact hM'
    rw [WExec.OrderInv, hTo, hTa]
    refine ⟨hwf₂ hk.wf, hp₂, fun v hv => by rw [hs₂, hk.size]; exact hS'.room v hv,
      fun v hv hvM hvo => ?_⟩
    rw [hm₂, hk.mem, hk.size]
    by_cases hvU : v ∈ Trail.vars (XTrail.trail U)
    · exact .inr ⟨hvU, hS'.room v hv⟩
    have hvM' : v ∉ Trail.vars S.M := by
      rw [hMUK, vars_append, List.mem_append, not_or]
      refine ⟨hvU, fun h => hvM ?_⟩
      rw [hTM]
      exact List.mem_cons_of_mem _ h
    -- the variables of the learned clause are all assigned after the backjump
    have hvo' : S.occurs.assigned v = true := by
      rw [hTocc, Assign.assigned_mark] at hvo
      refine hvo.resolve_left fun hvC => hvM ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hvC
      rw [hTM]
      by_cases hyl : y = L.lit
      · subst hyl; exact List.mem_cons_self
      · have := Trail.mem_vars_of_mem_lits (hfalseK y hy hyl)
        simp only [Std.Sat.Literal.negate] at this
        exact List.mem_cons_of_mem _ this
    exact .inl (hS'.covers v hv hvM' hvo')
  have hoccurs : ∀ v, (S.occurs.mark (L.clause.map Prod.fst)).assigned v = true ↔
      v ∈ E.clauses.vars := fun v => by
    rw [Assign.assigned_mark, hS.occurs v]
    simp [hEdef, Exec.afterConflictAt, Exec.clauses, CNF.vars]
  have hmeasure : rank φ.vars E.state * (nvars φ + 2) + 1 < S.measure := by
    have := hErank
    simp only [WExec.measure]
    nlinarith
  have hEq : E.tr.queueFrom q = [L.lit] := by
    have := (S.exec.tr.shrink q).queueFrom_push_end (.implied L.lit L.id)
    rwa [ATrail.size_shrink, Nat.min_eq_left hq] at this
  have hQ : ∀ T : WExec φ, T.exec = E → T.qhead = q → T.queue = [L.lit] := fun T h₁ h₂ => by
    rw [WExec.queue, h₁, h₂]; exact hEq
  unfold WExec.afterConflict
  dsimp only
  rw [show (jumpMarksAt S.exec.tr p L).assigned = jumpMarked (S.exec.tr.splitAt p) L by
      rw [jumpMarksAt_eq]; rfl, ← hqdef, ATrail.undoGo_assign, ATrail.undoGo_order,
    ← hUdef, ← hEdef, Assign.markLits_eq]
  split
  · rename_i hlen
    obtain ⟨y, rest, hc⟩ : ∃ y rest, L.clause = L.lit :: y :: rest := by
      have hh := L.head
      revert hh hlen
      generalize L.clause = C
      rcases C with _ | ⟨a, _ | ⟨y, rest⟩⟩ <;> intro hlen hh
      · simp at hlen
      · simp at hlen
      · cases Option.some.inj hh; exact ⟨y, rest, rfl⟩
    -- the clause stored is the learned clause with a literal moved second
    obtain ⟨y, rest, hc⟩ : ∃ y rest, secondOn (S.exec.tr.topMarked
        (jumpMarked (S.exec.tr.splitAt p) L) p) L.clause = L.lit :: y :: rest := by
      obtain ⟨rest', hr⟩ := secondOn_cons (S.exec.tr.topMarked
        (jumpMarked (S.exec.tr.splitAt p) L) p) L.lit (y :: rest)
      have hlen := (perm_secondOn (S.exec.tr.topMarked
        (jumpMarked (S.exec.tr.splitAt p) L) p) (L.lit :: y :: rest)).length_eq
      rw [hr] at hlen
      rcases rest' with _ | ⟨y', rest'⟩
      · simp at hlen
      · exact ⟨y', rest', hc ▸ hr⟩
    have hperm := perm_secondOn (S.exec.tr.topMarked (jumpMarked (S.exec.tr.splitAt p) L) p)
      L.clause
    rw [hc] at hperm
    have hnd : (L.lit :: y :: rest).Nodup := hperm.nodup_iff.2 L.nodup
    have hmem : ∀ l, l ∈ L.lit :: y :: rest ↔ l ∈ L.clause := fun l => hperm.mem_iff
    refine ⟨⟨hEinv, ?_, fun e' he' => ?_, fun e' he' hl => ?_,
      by rw [hQ _ rfl rfl]; exact List.nodup_singleton _,
      fun x hx => by
        rw [hQ _ rfl rfl, List.mem_singleton] at hx; subst hx
        change _ ∈ Trail.lits (XTrail.trail E.trail)
        rw [hM']; exact hlitM',
      by
        rw [hQ _ rfl rfl]
        change ∀ x ∈ [L.lit], ∀ N d M₀, XTrail.trail E.trail = _ → _; rw [hM']; exact hqueue,
      fun hv => horder hv _ rfl rfl rfl rfl,
      by
        change ((S.assign.unassignEntries U).assign L.lit).Agrees (XTrail.trail E.trail)
        rw [hM']; exact hassign,
      hoccurs⟩, ?_⟩
    · have := hstore.addClause (id := L.id) (C := L.clause) hnd hmem hlitneg
      rw [← hc] at this
      rw [hQ _ rfl rfl]
      change WatchStore.Inv E.db (XTrail.trail E.trail) [L.lit] _
      rw [hM', hdb']
      exact this
    · exact hdb' ▸ List.mem_cons_of_mem _ (hS.short_mem e' he')
    · rw [hdb'] at he'
      rcases List.mem_cons.1 he' with rfl | he'
      · simp only at hl; rw [List.dedup_eq_self.2 L.nodup] at hl; omega
      · exact hS.short_covers e' he' hl
    · simp only [WExec.measure]
      rw [hQ _ rfl rfl]
      exact hmeasure
  · rename_i hlen
    have hlen : L.clause.dedup.length < 2 := by rw [List.dedup_eq_self.2 L.nodup]; omega
    refine ⟨⟨hEinv, ?_, fun e' he' => ?_, fun e' he' hl => ?_,
      by rw [hQ _ rfl rfl]; exact List.nodup_singleton _,
      fun x hx => by
        rw [hQ _ rfl rfl, List.mem_singleton] at hx; subst hx
        change _ ∈ Trail.lits (XTrail.trail E.trail)
        rw [hM']; exact hlitM',
      by
        rw [hQ _ rfl rfl]
        change ∀ x ∈ [L.lit], ∀ N d M₀, XTrail.trail E.trail = _ → _; rw [hM']; exact hqueue,
      fun hv => horder hv _ rfl rfl rfl rfl,
      by
        change ((S.assign.unassignEntries U).assign L.lit).Agrees (XTrail.trail E.trail)
        rw [hM']; exact hassign,
      hoccurs⟩, ?_⟩
    · rw [hQ _ rfl rfl]
      change WatchStore.Inv E.db (XTrail.trail E.trail) [L.lit] _
      rw [hM', hdb']
      exact hstore.consShort (L.id, L.clause) (by simp only; omega)
    · rw [hdb']
      rcases List.mem_cons.1 he' with rfl | he'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS.short_mem e' he')
    · rw [hdb'] at he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS.short_covers e' he' hl)
    · simp only [WExec.measure]
      rw [hQ _ rfl rfl]
      exact hmeasure

/-- Adding a literal over an unassigned variable to the trail and the empty queue. -/
theorem WExec.Inv.push {S S' : WExec φ} (hS : S.Inv) (hq : S.queue = []) {l : Literal ℕ}
    {b : Bool} (hexec : S'.exec.Inv) (hM : S'.M = ⟨l, b⟩ :: S.M) (hq' : S'.queue = [l])
    (hdb : S'.exec.db = S.exec.db) (hstore : S'.store = S.store) (hshort : S'.short = S.short)
    (hundef : l.1 ∉ Trail.vars S.M) (horder : S'.opts.vsids = true → S'.OrderInv)
    (hassign : S'.assign = S.assign.assign l) (hocc : S'.occurs = S.occurs) : S'.Inv := by
  have hl : l ∉ Trail.lits S.M := fun h => hundef (Trail.mem_vars_of_mem_lits h)
  have hproc : ∀ x, Processed S'.M S'.queue x → Processed S.M S.queue x := by
    intro x ⟨hx, hxq⟩
    rw [hM] at hx
    rw [hq'] at hxq
    exact ⟨(List.mem_cons.1 hx).resolve_left (by simpa using hxq), by simp [hq]⟩
  refine ⟨hexec, ?_, ?_, ?_, ?_, ?_, ?_, horder, hassign ▸ hM ▸ hS.assign.cons hundef b,
    fun v => by rw [hocc, hS.occurs v, show S'.exec.clauses = S.exec.clauses by
      simp only [Exec.clauses, hdb]]⟩
  · rw [hstore, hdb]
    exact hS.store.weaken hproc fun _ _ _ _ _ hs => hM ▸ hs.cons _
  · rw [hshort, hdb]; exact hS.short_mem
  · rw [hshort, hdb]; exact hS.short_covers
  · rw [hq']; exact List.nodup_singleton _
  · rw [hq', hM]; intro x hx; rw [List.mem_singleton] at hx; subst hx; exact List.mem_cons_self
  · rw [hq', hM]
    intro x hx N d M₀ hN hxM₀
    rw [List.mem_singleton] at hx
    subst hx
    cases N with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hN
      exact hl (hN.2 ▸ hxM₀)
    | cons y N =>
      simp only [List.cons_append, List.cons.injEq] at hN
      exact hl (hN.2 ▸ lits_below hxM₀)

/-- The measure falls when the rank falls and one literal is queued on an empty queue. -/
theorem WExec.measure_push_lt {S S' : WExec φ} (hq : S.queue = []) (hq' : S'.queue.length = 1)
    (hrank : rank φ.vars S'.exec.state < rank φ.vars S.exec.state) : S'.measure < S.measure := by
  simp only [WExec.measure, hq, hq', List.length_nil]
  nlinarith

/-- **UnitPropagate from a short clause**, at an empty queue. -/
@[expose] def WExec.propagateShort (S : WExec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) : WExec φ :=
  -- the size of the trail is read first, so that the literal is pushed in place
  let q := S.exec.tr.size
  { S with exec := S.exec.propagate e l, assign := S.assign.assign l, qhead := q }

theorem WExec.M_propagateShort (S : WExec φ) (e : ℕ × Clause ℕ) (l : Literal ℕ) :
    (S.propagateShort e l).M = ⟨l, false⟩ :: S.M := by
  simp only [WExec.M, WExec.propagateShort, Exec.trail_propagate, XTrail.trail_cons,
    XEntry.entry_implied]

/-- The polarity of a decision on `x`: its saved phase, or `false` without phase saving. -/
@[expose] def WExec.polarity (S : WExec φ) (x : ℕ) : Bool := S.opts.phaseSaving && S.phase.get x

/-- `pickVar` with the variable order `ord` given apart from the state, so that the solver can take
it out of the state and pop the order in place. -/
@[expose] def WExec.pickVarIn (S : WExec φ) (ord : VarOrder) : VarOrder.Popped :=
  if S.opts.vsids then VarOrder.pop S.act S.assign S.occurs.assigned (ord.heap.size + 1) ord
  else ⟨(Activity.init 0).pick S.assign S.exec.clauses.vars, ord⟩

/-- **The decision variable**, and the variable order after choosing it. With VSIDS, it is popped
from the variable order (`Cslib.Algorithms.Lean.CDCL.VarOrder.pop`), with fuel enough to empty it
(`Cslib.Algorithms.Lean.CDCL.VarOrder.pop_none`). Without VSIDS, it is the first unassigned
variable of the database. -/
@[expose] def WExec.pickVar (S : WExec φ) : VarOrder.Popped := S.pickVarIn S.order

/-- **Decide** the variable `x`, at an empty queue, with the variable order `H`. -/
@[expose] def WExec.decide (S : WExec φ) (x : ℕ) (H : VarOrder) : WExec φ :=
  -- the size of the trail is read first, so that the trail is not shared when the decision is
  -- pushed, and is pushed in place
  let q := S.exec.tr.size
  { S with
    exec := S.exec.decide x (S.polarity x), assign := S.assign.assign (x, S.polarity x)
    qhead := q, order := H, level := S.level + 1
    stats := S.stats.decision }

theorem WExec.M_decide (S : WExec φ) (x : ℕ) (H : VarOrder) :
    (S.decide x H).M = ⟨(x, S.polarity x), true⟩ :: S.M := by
  simp only [WExec.M, WExec.decide, Exec.trail_decide, XTrail.trail_cons, XEntry.entry_decision]

/-- The variables of the database are variables of `φ`. -/
theorem Exec.Inv.mem_vars_of_clauses {S : Exec φ} (hS : S.Inv) {x : ℕ}
    (hx : x ∈ S.clauses.vars) : x ∈ φ.vars := by
  obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hx
  exact hS.run.db_vars c hc (x, b) hb

/-- **The decision variable** is an unassigned variable of the database. -/
theorem WExec.Inv.pickVar_some {S : WExec φ} (hS : S.Inv) {x : ℕ} {H : VarOrder}
    (h : S.pickVar = ⟨some x, H⟩) :
    x ∈ S.exec.clauses.vars ∧ x ∉ Trail.vars S.M := by
  unfold WExec.pickVar WExec.pickVarIn at h
  split at h
  · rename_i hv
    obtain ⟨-, -, -, hpop, -⟩ := VarOrder.pop_spec (V := φ.vars) hS.assign
      (S.order.heap.size + 1) S.order (hS.order hv).wf (hS.order hv).pos (hS.order hv).covers
    obtain ⟨hxM, hxo, -⟩ := hpop x (by rw [h])
    exact ⟨(hS.occurs x).1 hxo, hxM⟩
  · exact Activity.pick_some hS.assign (congrArg VarOrder.Popped.var h)

/-- Without a decision variable, every variable of the database is assigned. -/
theorem WExec.Inv.pickVar_none {S : WExec φ} (hS : S.Inv) {H : VarOrder}
    (h : S.pickVar = ⟨none, H⟩) :
    ∀ x ∈ S.exec.clauses.vars, x ∈ Trail.vars S.M := by
  unfold WExec.pickVar WExec.pickVarIn at h
  split at h
  · rename_i hv
    obtain ⟨-, -, -, -, hcov⟩ := VarOrder.pop_spec (V := φ.vars) hS.assign
      (S.order.heap.size + 1) S.order (hS.order hv).wf (hS.order hv).pos (hS.order hv).covers
    have h0 := VarOrder.pop_none S.act S.assign S.occurs.assigned _ S.order
      (Nat.lt_succ_self _) (by rw [h])
    simp only [h] at hcov h0
    intro x hx
    by_contra hxM
    have := hcov x (hS.exec.mem_vars_of_clauses hx) hxM ((hS.occurs x).2 hx) (by simp)
    exact absurd (Array.size_pos_of_mem this) (by omega)
  · exact Activity.pick_none hS.assign (congrArg VarOrder.Popped.var h)

/-- **With VSIDS, the decision variable has the greatest activity** among the unassigned variables
of the database. -/
theorem WExec.Inv.pickVar_max {S : WExec φ} (hS : S.Inv) (hv : S.opts.vsids = true) {x : ℕ}
    {H : VarOrder} (h : S.pickVar = ⟨some x, H⟩) :
    ∀ y ∈ S.exec.clauses.vars, y ∉ Trail.vars S.M → S.act.get y ≤ S.act.get x := by
  unfold WExec.pickVar WExec.pickVarIn at h
  simp only [hv, ↓reduceIte] at h
  obtain ⟨-, -, -, hpop, -⟩ := VarOrder.pop_spec (V := φ.vars) hS.assign
    (S.order.heap.size + 1) S.order (hS.order hv).wf (hS.order hv).pos (hS.order hv).covers
  exact fun z hz hzM => (hpop x (by rw [h])).2.2 z (hS.exec.mem_vars_of_clauses hz) hzM
    ((hS.occurs z).2 hz)

/-- After deciding the decision variable, the variable order keeps its invariant. -/
theorem WExec.Inv.pickVar_order {S : WExec φ} (hS : S.Inv) {x : ℕ} {H : VarOrder}
    (h : S.pickVar = ⟨some x, H⟩) (hv : (S.decide x H).opts.vsids = true) :
    (S.decide x H).OrderInv := by
  change S.opts.vsids = true at hv
  have hS' := hS.order hv
  obtain ⟨hwf, hp, hs, -, hcov⟩ := VarOrder.pop_spec (V := φ.vars) hS.assign
    (S.order.heap.size + 1) S.order hS'.wf hS'.pos hS'.covers
  have hM : ∀ v, v ∉ Trail.vars (S.decide x H).M → v ∉ Trail.vars S.M ∧ v ≠ x := fun v hv' =>
    ⟨fun h' => hv' (by rw [WExec.M_decide]; exact List.mem_cons_of_mem _ h'),
      fun h' => hv' (by rw [WExec.M_decide, h']; exact List.mem_cons_self)⟩
  change VarOrder.Inv H S.act φ.vars (S.decide x H).M S.occurs.assigned
  unfold WExec.pickVar WExec.pickVarIn at h
  simp only [hv, ↓reduceIte] at h
  simp only [h] at hwf hp hs hcov
  exact ⟨hwf, hp, fun v hv' => hs ▸ hS'.room v hv', fun v hv' hvM hvo =>
    hcov v hv' (hM v hvM).1 hvo (by simpa using (hM v hvM).2.symm)⟩

/-- With the queue empty, no clause of the database is false if no short clause is. -/
theorem WExec.Inv.noConflict {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hshort : ∀ e ∈ S.short, ¬ Trail.Falsifies S.M e.2) :
    ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  by_cases hlen : 2 ≤ e.2.dedup.length
  · exact (hq ▸ hS.store).not_falsifies hS.exec.run.nodup he hlen
  · exact hshort e (hS.short_covers e he (by omega))

/-- The variable order `H` at a restart undoing the variables `vs`, with the options `o` and the
activities `A`: with VSIDS, the variables of `vs` not in the heap are inserted. -/
@[expose] def restartOrderWith (o : Options) (H : VarOrder) (A : Activity) (vs : List ℕ) :
    VarOrder :=
  if o.vsids then H.addAll A vs else H

/-- The variable order at a restart: with VSIDS, the variables of the trail not in the heap are
inserted. -/
@[expose] def WExec.restartOrder (S : WExec φ) : VarOrder :=
  restartOrderWith S.opts S.order S.act (Trail.vars S.M)

/-- **Restart**, at an empty queue: back to the root of the trail, with VSIDS putting the variables
of the trail back in the variable order. With phase saving on, the phases of the trail's literals
are saved first, as MiniSat's `cancelUntil(0)` saves those it undoes; the root's literals stay
assigned, so only the saved phases of the undone ones are read later. The fields are taken out of
`S` first, so that the variable order is updated in place. -/
@[expose] def WExec.restart (S : WExec φ) : WExec φ :=
  let exec := S.exec
  let occurs := S.occurs
  let store := S.store
  let short := S.short
  let act := S.act
  let order := S.order
  let phase := S.phase
  let red := S.red
  let simpAssigns := S.simpAssigns
  let opts := S.opts
  let stats := S.stats
  let marks := S.marks
  let M := XTrail.trail exec.trail
  let e := exec.restart
  let order := restartOrderWith opts order act (Trail.vars M)
  let phase := if opts.phaseSaving then phase.save M else phase
  ⟨e, Assign.ofTrail (XTrail.trail e.trail), occurs, store, e.tr.size, short, act, order,
    phase, red, 0, simpAssigns, opts, { stats with restarts := stats.restarts + 1 }, marks⟩

theorem WExec.M_restart (S : WExec φ) : S.restart.M = XTrail.trail (XTrail.root S.exec.trail) :=
  congrArg XTrail.trail S.exec.trail_restart

/-- Restart keeps the invariant: the processed literals kept were processed, and the clauses with
both watched literals false keep their support, which is below the oldest decision. -/
theorem WExec.Inv.restart {S : WExec φ} (hS : S.Inv) (hq : S.queue = []) : S.restart.Inv := by
  obtain ⟨A, hA⟩ := XTrail.root_suffix S.exec.trail
  have hM : S.M = XTrail.trail A ++ S.restart.M := by
    rw [WExec.M_restart]
    change XTrail.trail S.exec.trail = _
    conv_lhs => rw [hA]
    exact XTrail.trail_append _ _
  have hrq : S.restart.queue = [] := WExec.queue_of_le le_rfl
  have hproc : ∀ x, Processed S.restart.M S.restart.queue x → Processed S.M S.queue x :=
    fun x ⟨hx, _⟩ => ⟨by rw [hM, lits_append]; exact List.mem_append_right _ hx, by simp [hq]⟩
  refine ⟨Exec.restart_inv hS.exec, hS.store.weaken hproc fun b w₁ w₂ h₁ h₂ hs => ?_,
    hS.short_mem, hS.short_covers, by rw [hrq]; exact List.nodup_nil,
    by rw [hrq]; simp, by rw [hrq]; simp, fun hv => ?_,
    Assign.agrees_ofTrail _ (Exec.restart_inv hS.exec).run.nodup, hS.occurs⟩
  swap
  · change S.opts.vsids = true at hv
    have hS' := hS.order hv
    obtain ⟨hwf₂, hp₂, hs₂, hm₂⟩ := VarOrder.addAll_spec S.act S.order (Trail.vars S.M) hS'.pos
    change VarOrder.Inv S.restartOrder S.act φ.vars S.restart.M S.occurs.assigned
    simp only [WExec.restartOrder, restartOrderWith, hv, ↓reduceIte]
    refine ⟨hwf₂ hS'.wf, hp₂, fun v hv' => hs₂ ▸ hS'.room v hv', fun v hv' hvM hvo => ?_⟩
    rw [hm₂]
    by_cases hvS : v ∈ Trail.vars S.M
    · exact .inr ⟨hvS, hS'.room v hv'⟩
    · exact .inl (hS'.covers v hv' hvS hvo)
  rcases XTrail.root_split S.exec.trail with h | ⟨N, d, hN⟩
  · have : S.restart.M = S.M := by
      rw [WExec.M_restart, h]
    exact this ▸ hs
  · exact hs.truncate (by rw [WExec.M_restart]; exact hN) h₁.1 h₂.1

/-- **The numbers of `cand` to delete**: the learned ones (`isLearntId n`) not in `locked`,
without repetitions, which LRAT checkers such as drat-trim's `lrat-check` reject. The numbers are
marked from the least of them, so that each is tested in constant time: the numbers chosen
together are mostly recent ones, so the arrays of marks are much shorter than the greatest
number. -/
@[expose] def chooseIds (n : ℕ) (locked cand : List ℕ) : List ℕ :=
  let ids := cand.filter (isLearntId n)
  let lo := ids.foldl min (ids.headD 0)
  let kept := Assign.marks (locked.filterMap fun r => if lo ≤ r then some (r - lo) else none)
  dedupKey (· - lo) <| ids.filter fun i => !kept.assigned (i - lo)

/-- **The numbers chosen**, and that each is chosen once. -/
private theorem chooseIds_spec (n : ℕ) (locked cand : List ℕ) :
    (∀ i, i ∈ chooseIds n locked cand ↔ i ∈ cand ∧ n < i ∧ i ∉ locked) ∧
      (chooseIds n locked cand).Nodup := by
  unfold chooseIds
  dsimp only
  generalize hids : cand.filter (isLearntId n) = ids
  have hlo : ∀ i ∈ ids, ids.foldl min (ids.headD 0) ≤ i := fun i hi => by
    rw [List.foldl_min_eq_min (List.ne_nil_of_mem hi)]
    exact Nat.le_trans (Nat.min_le_right _ _) (List.min_le_of_mem hi)
  generalize ids.foldl min (ids.headD 0) = lo at hlo ⊢
  obtain ⟨hmem, hnd⟩ := dedupKey_spec (key := (· - lo)) (ids.filter fun i =>
      !(Assign.marks (locked.filterMap fun r => if lo ≤ r then some (r - lo) else none)).assigned
        (i - lo)) fun x hx y hy h => by
    have := hlo x (List.mem_filter.1 hx).1
    have := hlo y (List.mem_filter.1 hy).1
    omega
  refine ⟨fun i => ?_, hnd⟩
  rw [hmem, List.mem_filter]
  constructor
  · rintro ⟨hi, hk⟩
    have hle := hlo i hi
    rw [← hids, List.mem_filter] at hi
    refine ⟨hi.1, by simpa [isLearntId] using hi.2, fun hm => ?_⟩
    have : i - lo ∈ locked.filterMap fun r => if lo ≤ r then some (r - lo) else none :=
      List.mem_filterMap.2 ⟨i, hm, by simp [hle]⟩
    rw [← Assign.assigned_marks] at this
    simp [this] at hk
  · rintro ⟨hc, hn, hl⟩
    have hi : i ∈ ids := by
      rw [← hids, List.mem_filter]; exact ⟨hc, by simpa [isLearntId] using hn⟩
    refine ⟨hi, ?_⟩
    have hle := hlo i hi
    rw [Bool.not_eq_true']
    cases hm : (Assign.marks
        (locked.filterMap fun r => if lo ≤ r then some (r - lo) else none)).assigned (i - lo)
    · rfl
    · rw [Assign.assigned_marks] at hm
      obtain ⟨r, hr, hre⟩ := List.mem_filterMap.1 hm
      split at hre
      · simp only [Option.some.injEq] at hre
        exact absurd (show r = i by omega ▸ hr) hl
      · simp at hre

/-- **The numbers chosen** are the learned ones of `cand` not in `locked`. -/
theorem mem_chooseIds {n : ℕ} {locked cand : List ℕ} {i : ℕ} :
    i ∈ chooseIds n locked cand ↔ i ∈ cand ∧ n < i ∧ i ∉ locked :=
  (chooseIds_spec n locked cand).1 i

/-- Each number is chosen once. -/
theorem nodup_chooseIds (n : ℕ) (locked cand : List ℕ) : (chooseIds n locked cand).Nodup :=
  (chooseIds_spec n locked cand).2

/-- **The learned clauses to forget**, as MiniSat's `reduceDB` chooses them: the learned clauses
of the store, those of more than two literals first by increasing activity; of the less active
half, those of more than two literals, and of the other half, those of more than two literals and
activity below the increment divided by their number. Kept in any case are the clauses of `φ`, the
reasons of the trail (MiniSat's *locked* clauses) and the short clauses. -/
@[expose] def WExec.reduceIds (S : WExec φ) : List ℕ :=
  let act := S.red.act
  -- computed once, not in each test
  let n := φ.length
  -- the learned clauses, by number and number of literals
  let learnts := S.store.codes.toList.filterMap fun a =>
    if isLearntId n (clauseId a) then some (clauseId a, a.size - 1) else none
  let sorted := sortBy (fun a b =>
    if (a.2 ≤ 2) == (b.2 ≤ 2) then act.get a.1 ≤ act.get b.1 else b.2 ≤ 2)
    learnts
  let half := sorted.length / 2
  -- MiniSat's `activity < cla_inc / learnts.size()`, without rounding the quotient
  let chosen := (sorted.take half).filter (2 < ·.2) ++
    (sorted.drop half).filter fun e => 2 < e.2 && act.get e.1 * sorted.length < act.inc
  -- the reasons of the trail (MiniSat's `locked`) and the short clauses are kept
  chooseIds n (XTrail.reasonIds S.exec.trail ++ S.short.map Prod.fst) (chosen.map Prod.fst)

/-- The number of learned clauses in the store, those numbered above `n` (`isLearntId`). Reduction
and simplification set the count of learned clauses from the rebuilt store, instead of subtracting
the numbers deleted. -/
@[expose] def WatchStore.learntCount (S : WatchStore) (n : ℕ) : ℕ :=
  S.codes.foldl (fun k a => if isLearntId n (clauseId a) then k + 1 else k) 0

/-- **Adding a clause to the store** of two or more literals adds one to the count of learned
clauses exactly when its number is a learned one. -/
theorem WatchStore.learntCount_addClause (S : WatchStore) (n id : ℕ) (w₁ w₂ : Literal ℕ)
    (rest : Clause ℕ) :
    (S.addClause id (w₁ :: w₂ :: rest)).learntCount n =
      if isLearntId n id then S.learntCount n + 1 else S.learntCount n := by
  simp only [WatchStore.addClause, WatchStore.learntCount, Array.foldl_push, clauseId_push]

/-- The invariant does not read the bookkeeping of reduction and simplification, nor the
statistics. -/
theorem WExec.Inv.withBookkeeping {S : WExec φ} (h : S.Inv) (red : Reduction) (simpAssigns : ℕ)
    (stats : Stats) : ({ S with red, simpAssigns, stats } : WExec φ).Inv :=
  ⟨h.exec, h.store, h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above,
    h.order, h.assign, h.occurs⟩

/-- **The positions of the variables on the trail**, one past each, `0` for a variable not on it,
in an array of `n` slots. They order the watches of a rebuilt store (`watchOrderAt`). -/
@[expose] def ATrail.positions (T : ATrail) (n : ℕ) : Array ℕ :=
  go 0 T.size (Array.replicate n 0)
where
  /-- The positions of the variables of the `k` entries from position `i` up, set in `P`. -/
  go : ℕ → ℕ → Array ℕ → Array ℕ
  | _, 0, P => P
  | i, k + 1, P => go (i + 1) k (P.setIfInBounds (T.lits.getD i 0 / 2) (i + 1))

private theorem ATrail.positions_go_size (T : ATrail) :
    ∀ (i k : ℕ) (P : Array ℕ), (ATrail.positions.go T i k P).size = P.size
  | _, 0, _ => rfl
  | i, k + 1, P => by
    rw [ATrail.positions.go, ATrail.positions_go_size T (i + 1) k, Array.size_setIfInBounds]

private theorem ATrail.positions_go_of_ne (T : ATrail) {v : ℕ} : ∀ (i k : ℕ) (P : Array ℕ),
    (∀ j, i ≤ j → j < i + k → (T.lit j).1 ≠ v) → (ATrail.positions.go T i k P).getD v 0 = P.getD v 0
  | _, 0, _, _ => rfl
  | i, k + 1, P, h => by
    rw [ATrail.positions.go,
      ATrail.positions_go_of_ne T (i + 1) k _ fun j h₁ h₂ => h j (by omega) (by omega)]
    have hi : T.lits.getD i 0 / 2 ≠ v := h i le_rfl (by omega)
    generalize T.lits.getD i 0 / 2 = u at hi ⊢
    simp [Array.getD_eq_getD_getElem?, hi]

private theorem ATrail.positions_go_eq (T : ATrail) {v j : ℕ} : ∀ (i k : ℕ) (P : Array ℕ),
    i ≤ j → j < i + k → (T.lit j).1 = v → v < P.size →
    (∀ j', i ≤ j' → j' < i + k → (T.lit j').1 = v → j' = j) →
    (ATrail.positions.go T i k P).getD v 0 = j + 1
  | _, 0, _, h₁, h₂, _, _, _ => absurd h₂ (by omega)
  | i, k + 1, P, h₁, h₂, hj, hv, hu => by
    rw [ATrail.positions.go]
    by_cases hij : i = j
    · subst hij
      rw [ATrail.positions_go_of_ne T (i + 1) k _ fun j' h₁' h₂' he =>
        absurd (hu j' (by omega) (by omega) he) (by omega)]
      have hj' : T.lits.getD i 0 / 2 = v := hj
      generalize T.lits.getD i 0 / 2 = u at hj' ⊢
      subst hj'
      simp [Array.getD_eq_getD_getElem?, hv]
    · exact ATrail.positions_go_eq T (i + 1) k _ (by omega) (by omega) hj (by simpa using hv)
        fun j' h₁' h₂' he => hu j' (by omega) (by omega) he

/-- **The position of a variable on the trail**: on a trail without a variable twice, the
variable of the entry at position `j`, below `n`, gets `j + 1`. -/
theorem ATrail.positions_lit {T : ATrail} {n j : ℕ} (hj : j < T.size)
    (hnd : ∀ i < T.size, (T.lit i).1 = (T.lit j).1 → i = j) (hn : (T.lit j).1 < n) :
    (T.positions n).getD (T.lit j).1 0 = j + 1 :=
  ATrail.positions_go_eq T 0 T.size _ (Nat.zero_le _) (by omega) rfl (by simpa using hn)
    fun j' _ h₂ he => hnd j' (by omega) he

/-- A variable not on the trail gets `0`. -/
theorem ATrail.positions_of_not_mem {T : ATrail} {n v : ℕ}
    (hv : ∀ j < T.size, (T.lit j).1 ≠ v) : (T.positions n).getD v 0 = 0 := by
  rw [ATrail.positions, ATrail.positions_go_of_ne T 0 T.size _ fun j _ h => hv j (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- **Forgetting clauses**: the clauses numbered `ids` are forgotten, and the watch store, the
short clauses and the marks of the variables occurring in the database are rebuilt. Reduction and
simplification both use it, each with its own bookkeeping. -/
@[expose] def WExec.forgetRebuilt (S : WExec φ) (ids : List ℕ) : WExec φ :=
  let exec := S.exec.forget ids
  { S with
    exec := exec
    occurs := Assign.marks exec.clauses.vars
    store := WatchStore.build (S.exec.tr.positions S.assign.vals.size) S.assign exec.db
    short := S.short.filter fun e => !ids.contains e.1 }

/-- Forgetting clauses at an empty queue with no false clause, when `Exec.forget` keeps its
invariant, keeps the invariant and the measure, and no clause becomes false. -/
theorem WExec.Inv.forgetRebuilt {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hnoconf : ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c) {ids : List ℕ}
    (hexec : (S.exec.forget ids).Inv) :
    (S.forgetRebuilt ids).Inv ∧
      (∀ c ∈ (S.forgetRebuilt ids).exec.clauses, ¬ Trail.Falsifies (S.forgetRebuilt ids).M c) ∧
      (S.forgetRebuilt ids).measure = S.measure := by
  have hdb : ∀ e ∈ (S.exec.forget ids).db, e ∈ S.exec.db ∧ e.1 ∉ ids := fun e he =>
    Exec.mem_forget_db.1 he
  have hsub : ∀ c ∈ (S.forgetRebuilt ids).exec.clauses, c ∈ S.exec.clauses := fun c hc => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    exact List.mem_map.2 ⟨e, (hdb e he).1, rfl⟩
  refine ⟨⟨hexec, ?_, fun e he => ?_, fun e he hlen => ?_, hS.queue_nodup, hS.queue_trail,
    hS.queue_above, fun hv => (hS.order hv).restrict rfl rfl rfl fun v hv' =>
      (hS.occurs v).2 (by
      obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 ((Assign.assigned_marks _ v).1 hv')
      exact CNF.mem_vars.2 ⟨c, hsub c hc, b, hb⟩), hS.assign,
    fun v => Assign.assigned_marks _ v⟩, fun c hc => hnoconf c (hsub c hc), rfl⟩
  · change (WatchStore.build (S.exec.tr.positions S.assign.vals.size) S.assign
      (S.exec.forget ids).db).Inv _ S.M S.queue
    rw [hq]
    exact WatchStore.build_inv _ hS.assign _ fun e he _ =>
      hnoconf e.2 (List.mem_map.2 ⟨e, (hdb e he).1, rfl⟩)
  · obtain ⟨he, hid⟩ := List.mem_filter.1 he
    exact Exec.mem_forget_db.2 ⟨hS.short_mem e he, by simpa using hid⟩
  · obtain ⟨he', hid⟩ := hdb e he
    exact List.mem_filter.2 ⟨hS.short_covers e he' hlen, by simpa using hid⟩

/-- Forgetting the learned clauses numbered `ids` and rebuilding the watch store on the current
trail. -/
@[expose] def WExec.forgetChosen (S : WExec φ) (ids : List ℕ) : WExec φ :=
  let T := S.forgetRebuilt ids
  { T with
    red := { S.red with learnts := T.store.learntCount φ.length }
    stats := { S.stats with removed := S.stats.removed + ids.length } }

/-- **Reducing the learned clauses**, at an empty queue: the clauses chosen are forgotten, and the
watch store is rebuilt on the current trail. If none is chosen, nothing changes: the store is not
rebuilt and the certificate gets no deletion step. -/
@[expose] def WExec.reduce (S : WExec φ) : WExec φ :=
  let ids := S.reduceIds
  if ids.isEmpty then S else S.forgetChosen ids

theorem WExec.mem_reduceIds {S : WExec φ} {i : ℕ} (h : i ∈ S.reduceIds) :
    φ.length < i ∧ i ∉ XTrail.reasonIds S.exec.trail ∧ ∀ e ∈ S.short, e.1 ≠ i := by
  obtain ⟨-, hlt, hnot⟩ := mem_chooseIds.1 h
  simp only [List.mem_append, List.mem_map, not_or, not_exists, not_and] at hnot
  exact ⟨hlt, hnot.1, fun e he hei => hnot.2 e he hei⟩

/-- Reducing at an empty queue with no false clause keeps the invariant and the measure, and no
clause becomes false. -/
theorem WExec.Inv.reduce {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hnoconf : ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c) :
    S.reduce.Inv ∧ (∀ c ∈ S.reduce.exec.clauses, ¬ Trail.Falsifies S.reduce.M c) ∧
      S.reduce.measure = S.measure := by
  unfold WExec.reduce
  dsimp only
  split
  · exact ⟨hS, hnoconf, rfl⟩
  · have ⟨h₁, h₂, h₃⟩ := hS.forgetRebuilt hq hnoconf (Exec.forget_inv hS.exec (fun e _ he hi => by
      have := (WExec.mem_reduceIds hi).1
      have := le_length_of_mem_lratDB he
      omega) fun r hr hi => (WExec.mem_reduceIds hi).2.1 hr)
    exact ⟨h₁.withBookkeeping _ _ _, h₂, h₃⟩

/-- **MiniSat's `reduceDB`, when due**: if reduction is on and the learned clauses in the store
exceed the assigned variables by the limit, reduce. -/
@[expose] def WExec.maybeReduce (S : WExec φ) : WExec φ :=
  if S.opts.reduce && S.red.max ≤ 1000 * S.red.learnts &&
      S.red.max + 1000 * S.exec.tr.size ≤ 1000 * S.red.learnts then S.reduce
  else S

theorem WExec.Inv.maybeReduce {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hnoconf : ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c) :
    S.maybeReduce.Inv ∧ S.maybeReduce.queue = [] ∧
      (∀ c ∈ S.maybeReduce.exec.clauses, ¬ Trail.Falsifies S.maybeReduce.M c) ∧
      S.maybeReduce.measure = S.measure := by
  unfold WExec.maybeReduce
  split
  · have ⟨h₁, h₂, h₃⟩ := hS.reduce hq hnoconf
    refine ⟨h₁, ?_, h₂, h₃⟩
    unfold WExec.reduce
    dsimp only
    split <;> exact hq
  · exact ⟨hS, hq, hnoconf, rfl⟩

/-! ### Simplifying at the root -/

/-- **The clauses to delete at the root** (MiniSat's `removeSatisfied`, on the learned clauses, and
on the input clauses with `removeSatisfied`): those satisfied by a literal of the root of the
trail, except the reasons of the trail. -/
@[expose] def WExec.simplifyIds (S : WExec φ) : List ℕ :=
  let root := Assign.ofTrail (XTrail.trail (XTrail.root S.exec.trail))
  let locked := Assign.marks (XTrail.reasonIds S.exec.trail)
  -- without repetitions, as in `reduceIds`
  dedupVars <| (S.exec.db.filter fun e =>
    (S.opts.removeSatisfied || φ.length < e.1) && e.2.any root.holds && !locked.assigned e.1).map
      Prod.fst

theorem WExec.mem_simplifyIds {S : WExec φ} (hS : S.Inv) {i : ℕ} (h : i ∈ S.simplifyIds) :
    i ∉ XTrail.reasonIds S.exec.trail ∧ ∃ e ∈ S.exec.db, e.1 = i ∧
      ∃ l ∈ e.2, l ∈ Trail.lits (XTrail.trail (XTrail.root S.exec.trail)) := by
  unfold simplifyIds at h
  rw [mem_dedupKey Function.injective_id] at h
  simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, List.any_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨e, ⟨he, ⟨-, l, hl, hroot⟩, hlock⟩, rfl⟩ := h
  have hnd : (Trail.vars (XTrail.trail (XTrail.root S.exec.trail))).Nodup := by
    have := (Exec.restart_inv hS.exec).run.nodup
    rwa [Exec.toL_trail, Exec.trail_restart] at this
  refine ⟨fun hr => ?_, e, he, rfl, l, hl, ((Assign.agrees_ofTrail _ hnd).holds_iff l).1 hroot⟩
  rw [← Assign.assigned_marks] at hr
  rw [hr] at hlock
  exact absurd hlock (by decide)

/-- **Simplifying at the root** (MiniSat's `simplify`): the clauses satisfied by the root are
forgotten, input clauses included, and the watch store and the marks of the variables occurring in
the database are rebuilt. -/
@[expose] def WExec.simplify (S : WExec φ) : WExec φ :=
  let ids := S.simplifyIds
  if ids.isEmpty then { S with simpAssigns := S.exec.tr.size }
  else
    let T := S.forgetRebuilt ids
    { T with
      red := { S.red with learnts := T.store.learntCount φ.length }
      simpAssigns := S.exec.tr.size
      stats := { S.stats with simplified := S.stats.simplified + ids.length } }

/-- Simplifying at an empty queue with no false clause keeps the invariant and the measure, and no
clause becomes false. -/
theorem WExec.Inv.simplify {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hnoconf : ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c) :
    S.simplify.Inv ∧ (∀ c ∈ S.simplify.exec.clauses, ¬ Trail.Falsifies S.simplify.M c) ∧
      S.simplify.measure = S.measure := by
  unfold WExec.simplify
  dsimp only
  split
  · exact ⟨hS.withBookkeeping _ _ _, hnoconf, rfl⟩
  · have ⟨h₁, h₂, h₃⟩ := hS.forgetRebuilt hq hnoconf (Exec.forget_inv hS.exec (fun e he _ hi => by
      obtain ⟨-, e', he', hid, hsat⟩ := WExec.mem_simplifyIds hS hi
      have h₁ := hS.exec.db_log e he
      have h₂ := hS.exec.db_log e' he'
      rw [hid, h₁, Option.some.injEq] at h₂
      exact h₂ ▸ hsat) fun r hr hi => (WExec.mem_simplifyIds hS hi).1 hr)
    exact ⟨h₁.withBookkeeping _ _ _, h₂, h₃⟩

/-- **MiniSat's `simplify`, when due**: at decision level `0`, if the trail grew since the last
simplification. The cached level is checked first; the trail is then checked to have no decision,
so that simplification provably happens at the root (`WExec.maybeSimplify_root`) whatever the
cache holds. -/
@[expose] def WExec.maybeSimplify (S : WExec φ) : WExec φ :=
  if S.level == 0 && S.simpAssigns != S.exec.tr.size &&
      S.exec.tr.foldDown (fun b _ r => b && r != 0) 0 S.exec.tr.size true then S.simplify else S

/-- **Simplification happens at the root**: either nothing happens, or the trail has no
decision. -/
theorem WExec.maybeSimplify_root (S : WExec φ) :
    S.maybeSimplify = S ∨ ∀ x ∈ S.exec.trail, x.entry.decision = false := by
  unfold WExec.maybeSimplify
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have hall := h.2
    rw [ATrail.foldDown_eq, foldl_and_eq_and_all] at hall
    simp only [Bool.true_and, List.all_eq_true, bne_iff_ne, ne_eq] at hall
    refine .inr fun x hx => ?_
    have := hall x hx
    cases x
    · exact absurd rfl this
    · rfl
  · exact .inl rfl

theorem WExec.Inv.maybeSimplify {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hnoconf : ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c) :
    S.maybeSimplify.Inv ∧ S.maybeSimplify.queue = [] ∧
      (∀ c ∈ S.maybeSimplify.exec.clauses, ¬ Trail.Falsifies S.maybeSimplify.M c) ∧
      S.maybeSimplify.measure = S.measure := by
  unfold WExec.maybeSimplify
  split
  · have ⟨h₁, h₂, h₃⟩ := hS.simplify hq hnoconf
    refine ⟨h₁, ?_, h₂, h₃⟩
    unfold WExec.simplify
    dsimp only
    split <;> exact hq
  · exact ⟨hS, hq, hnoconf, rfl⟩

theorem WExec.maybeSimplify_conflicts (S : WExec φ) :
    S.maybeSimplify.stats.conflicts = S.stats.conflicts := by
  unfold WExec.maybeSimplify WExec.simplify
  dsimp only
  split
  · split <;> rfl
  · rfl

theorem WExec.maybeReduce_conflicts (S : WExec φ) :
    S.maybeReduce.stats.conflicts = S.stats.conflicts := by
  unfold WExec.maybeReduce WExec.reduce
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- The number of a learned clause is a learned number: the log's next number, beyond the clauses
of `φ`. -/
theorem Learned.isLearntId_id {log : LRATLog φ} {A M₀ : Trail} (L : Learned log A M₀) :
    isLearntId φ.length L.id = true := by
  simp only [isLearntId, Learned.id]
  exact decide_eq_true log.next_gt

/-- **The count of learned clauses at insertion**: with reduction on, a conflict whose learned
clause goes to the watch store (two or more literals) counts it exactly when its number is a
learned one (`isLearntId`), the rule by which `WatchStore.learntCount` counts the store
(`WatchStore.learntCount_addClause`). -/
theorem WExec.afterConflict_learnts (S : WExec φ) (p : ℕ)
    (L : S.exec.LearnedAt (S.exec.tr.splitAt p)) (k₀ : ℕ)
    (hred : S.opts.reduce = true) (hk : 2 ≤ (dedupLits L.clause).length) :
    (S.afterConflict p L k₀).red.learnts =
      if isLearntId φ.length L.id then S.red.learnts + 1 else S.red.learnts := by
  unfold WExec.afterConflict
  dsimp only
  rw [ite_eq_left (L.dedupLits_clause ▸ hk), L.isLearntId_id]
  simp only [reducedWith, hred, ite_true, Reduction.learn]
  split <;> rfl

/-- A conflict counts one. -/
theorem WExec.afterConflict_conflicts (S : WExec φ) (p : ℕ)
    (L : S.exec.LearnedAt (S.exec.tr.splitAt p)) (k₀ : ℕ) :
    (S.afterConflict p L k₀).stats.conflicts = S.stats.conflicts + 1 := by
  unfold WExec.afterConflict; dsimp only; split <;> rfl

/-- **A bound on the measure** of every state, plus one; so on the conflicts of a run of the loop.
-/
@[expose] def restartBound (φ : CNF ℕ) : ℕ :=
  (nvars φ * (nvars φ + 1) ^ nvars φ + 1) * (nvars φ + 2) + nvars φ + 1

theorem WExec.Inv.measure_lt_restartBound {S : WExec φ} (hS : S.Inv) :
    S.measure < restartBound φ := by
  have hq := hS.queue_length_le
  have hr : rank φ.vars S.exec.state ≤ nvars φ * (nvars φ + 1) ^ nvars φ + 1 := by
    simp only [Exec.state, ExecL.state, rank, nvars]; omega
  have := Nat.mul_le_mul_right (nvars φ + 2) hr
  simp only [WExec.measure, restartBound]
  omega

/-- The answer of the solver, with its correctness: a model, or an LRAT certificate accepted by
the checker. -/
inductive Answer (φ : CNF ℕ) : Type
  /-- A model. -/
  | sat (σ : ℕ → Bool) (h : φ.eval σ = true)
  /-- An accepted certificate. -/
  | unsat (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) (h : φ.checkLRAT cert = true)

/-- **A run of the loop for up to `2 ^ d` moves** from the state `S`, started with `c₀` conflicts:
the answer with the statistics; a restarted state, whose conflicts have reached the limit and are
fewer than `c₀ + restartBound φ`; or, after `2 ^ d` moves, the state reached, whose measure is
lower by at least `2 ^ d` and whose conflicts plus measure have not grown. -/
inductive Run (φ : CNF ℕ) (limit : Option ℕ) (c₀ : ℕ) (S : WExec φ) (d : ℕ) : Type
  /-- The answer, with the statistics. -/
  | done (r : Answer φ × Stats)
  /-- A restarted state, whose conflicts have reached the limit and are fewer than
  `c₀ + restartBound φ`. -/
  | restart (S' : WExec φ) (h : S'.Inv)
      (hr : ∃ n, limit = some n ∧ n ≤ S'.stats.conflicts ∧ S'.stats.conflicts < c₀ + restartBound φ)
  /-- The state after `2 ^ d` moves. -/
  | next (T : WExec φ) (hT : T.Inv) (hm : T.measure + 2 ^ d ≤ S.measure)
      (hc : T.stats.conflicts + T.measure ≤ S.stats.conflicts + S.measure)

/-- One move to the state `T`, which lowers the measure and counts at most one conflict. -/
@[expose] def Run.move {limit : Option ℕ} {c₀ : ℕ} {S : WExec φ} (T : WExec φ) (hT : T.Inv)
    (hm : T.measure < S.measure) (hc : T.stats.conflicts ≤ S.stats.conflicts + 1) :
    Run φ limit c₀ S 0 :=
  .next T hT (by omega) (by omega)

/-- **A move of the CDCL loop with watched literals**, restarting once the number of conflicts
reaches `limit`, if any. While the queue is not empty, the watch list of the negation of its first
literal is visited; a conflict is analysed, followed by Backjump and Learn, or ends with a
certificate when there is no decision. With the queue empty, the short clauses are checked for a
conflict or a unit; then the loop restarts if the limit is reached, decides an unassigned variable
of the database, or returns the trail as a model. A move lowers the measure and counts at most one
conflict, so the conflicts plus the measure never grow; as they start below `c₀ + restartBound φ`,
a restarted state has fewer conflicts than that. -/
@[expose] def step (φ : CNF ℕ) (limit : Option ℕ) (c₀ : ℕ) (S : WExec φ) (hS : S.Inv)
    (hP : S.stats.conflicts + S.measure < c₀ + restartBound φ) : Run φ limit c₀ S 0 :=
  -- a conflict on a database clause, with as many conflicts counted as `S`
  let onConflict (T : WExec φ) (hT : T.Inv) (e : ℕ × Clause ℕ) (he : e ∈ T.exec.db)
      (hconf : Trail.Falsifies T.M e.2) (hm : T.measure ≤ S.measure)
      (hc : T.stats.conflicts = S.stats.conflicts) : Run φ limit c₀ S 0 :=
    match hpn : T.exec.tr.newestDecision T.exec.tr.size with
    | none =>
      let r := refute T.exec.trail T.exec.log e.1 e.2 (hT.exec.db_log e he) hT.exec.reasons
        (XTrail.split_eq_none (ATrail.split_toX_none hpn)) hconf
      .done (.unsat r.cert (LRATLog.checkLRAT_finish r.rup), T.stats.conflict)
    | some p =>
      have hp : T.exec.tr.IsNewest p := ATrail.isNewest_of_newestDecision hpn
      have hsp : XTrail.split T.exec.toL.trail = some (T.exec.tr.splitAt p) := hp.split
      -- the marks are taken out of `T` first, so that marking the level updates them in place
      let marks := T.marks
      let T₁ := T.dropMarks
      have hT₁ : T₁.Inv := hT.dropMarks
      -- the slots of the assignment array: past every variable of the trail, so that the arrays
      -- of the analysis and of minimization do not grow and no reason is missed
      let n := T₁.assign.vals.size
      let L₀ := analyze T₁.exec.log T₁.exec.tr p (T₁.exec.tr.assignLevelAt p marks.val)
        (by
          rw [ATrail.assignLevelAt_eq T₁.exec.tr _ hp.lt]
          exact Assign.agrees_assignTrail marks.property _ (hT.exec.split_level_nodup hsp))
        n e.1 e.2
        (hT.exec.db_log e he) (hT.exec.split_reasons hsp)
        (XTrail.split_eq_some hsp).2 (XTrail.falsifies_of_split hsp hconf)
        (hT.exec.split_cur hsp he hconf) (hT.exec.split_nodup hsp)
      have hbelow : Reasons T₁.exec.log (T₁.exec.tr.seg 0 p) :=
        (hT.exec.split_reasons hsp).append_right.tail
      have hnd : (Trail.vars (XTrail.trail (T₁.exec.tr.seg 0 p))).Nodup := by
        have := hT.exec.split_nodup hsp
        rw [trail_level, vars_append] at this
        exact this.of_append_right
      let L := match T₁.opts.ccminMode with
        | .none => L₀
        | .basic => L₀.minimize T₁.exec.tr p hbelow hnd n (recursive := false)
        | .recursive => L₀.minimize T₁.exec.tr p hbelow hnd n (recursive := true)
      let k₀ := L₀.clause.length
      have hspec := WExec.afterConflict_spec hT₁ he hconf hp L k₀
      .move (T₁.afterConflict p L k₀) hspec.1 (by
        have : T₁.measure = T.measure := rfl
        omega) (by
        have := T₁.afterConflict_conflicts p L k₀
        have : T₁.stats.conflicts = T.stats.conflicts := rfl
        omega)
  if hlt : S.qhead < S.exec.tr.size then
    -- the store, the trail, the assignment, the head of the queue and the count of propagations
    -- are taken out of the state, so that processing the queue updates them in place
    -- (`WExec.withParts`)
    let st := S.store
    let ex := S.exec
    let A := S.assign
    let S₀ : WExec φ :=
      { S with
        store := WatchStore.empty, exec := { ex with tr := ATrail.empty }, assign := Assign.empty }
    have hS₀ : S₀.withParts st ex.tr A S.qhead S.stats.propagations = S := rfl
    match S₀.processQueue S.measure S.stats.conflicts A.vals.size st ex.tr A S.qhead
        S.stats.propagations hlt (by rw [hS₀]; exact hS) (by rw [hS₀]) (by rw [hS₀]) with
    | .stop T hT hm hc => .move T hT hm (by omega)
    | .conflict T hT e he hconf hm hc => onConflict T hT e he hconf hm hc
  else
    have hq : S.queue = [] := WExec.queue_of_le (by omega)
    match hc : S.short.find? (fun e => S.assign.falsifies e.2) with
    | some e =>
      onConflict S hS e (hS.short_mem e (List.mem_of_find?_eq_some hc))
        ((hS.assign.falsifies_iff e.2).1
          (List.find?_some (p := fun e : ℕ × Clause ℕ => S.assign.falsifies e.2) hc))
        (by omega) rfl
    | none =>
      have hshort : ∀ e ∈ S.short, ¬ Trail.Falsifies S.M e.2 := fun e he hf =>
        List.find?_eq_none.1 hc e he ((hS.assign.falsifies_iff _).2 hf)
      have hnoconf := hS.noConflict hq hshort
      match hu : findUnit S.assign S.short with
      | some (e, l) =>
        have ⟨he, hl, hundef, hfalse⟩ := findUnit_spec hS.assign hu
        have hspec := Exec.propagate_spec hS.exec (hS.short_mem e he) hl hundef hfalse
        .move (S.propagateShort e l)
          (hS.push hq hspec.1 (WExec.M_propagateShort S e l)
            (WExec.queue_push_end (.implied l e.1) rfl rfl) rfl rfl rfl hundef (fun hv =>
            (hS.order hv).extend rfl rfl rfl fun v hv => by
              rw [WExec.M_propagateShort]; exact List.mem_cons_of_mem _ hv) rfl rfl)
          (by
            have := WExec.measure_push_lt (S' := S.propagateShort e l) hq
              (by rw [WExec.queue_push_end (.implied l e.1) rfl rfl]; rfl) hspec.2
            omega)
          (by
            have : (S.propagateShort e l).stats.conflicts = S.stats.conflicts := rfl
            omega)
      | none =>
        have ⟨hS₀, hq₀, hnoconf₀, hm₀⟩ := hS.maybeSimplify hq hnoconf
        let S₀ := S.maybeSimplify
        have ⟨hS₁, hq₁, hnoconf₁, hm₁⟩ := hS₀.maybeReduce hq₀ hnoconf₀
        let S₁ := S₀.maybeReduce
        have hc₁ : S₁.stats.conflicts = S.stats.conflicts :=
          S₀.maybeReduce_conflicts.trans S.maybeSimplify_conflicts
        match hr : limit.any (· ≤ S₁.stats.conflicts) with
        | true => .restart S₁.restart (hS₁.restart hq₁) (by
            cases hl : limit with
            | none => simp [hl] at hr
            | some n =>
              simp only [hl, Option.any_some, decide_eq_true_eq] at hr
              have : S₁.restart.stats.conflicts = S₁.stats.conflicts := rfl
              exact ⟨n, rfl, by omega, by omega⟩)
        | false =>
        -- the variable order is taken out of the state, so that popping updates it in place
        let ord := S₁.order
        let S₂ : WExec φ := { S₁ with order := VarOrder.empty 0 }
        match hx : S₂.pickVarIn ord with
        | ⟨some x, H⟩ =>
          have hx' : S₁.pickVar = ⟨some x, H⟩ := hx
          have ⟨hxV, hundef⟩ := hS₁.pickVar_some hx'
          have hspec := Exec.decide_spec hS₁.exec hnoconf₁ hxV hundef (S₁.polarity x)
          .move (S₂.decide x H)
            (hS₁.push hq₁ hspec.1 (WExec.M_decide S₂ x H)
              (WExec.queue_push_end (.decision (x, S₁.polarity x)) rfl rfl) rfl rfl rfl hundef
              (hS₁.pickVar_order hx') rfl rfl)
            (by
              have := WExec.measure_push_lt (S' := S₂.decide x H) hq₁
                (by rw [WExec.queue_push_end (.decision (x, S₁.polarity x)) rfl rfl]; rfl) hspec.2
              omega)
            (by
              have : (S₂.decide x H).stats.conflicts = S₁.stats.conflicts := rfl
              omega)
        | ⟨none, _⟩ =>
          .done (.sat (Trail.assignment S₂.M)
            (hS₁.exec.run.eval_model hnoconf₁ (hS₁.pickVar_none hx)), S₂.stats)

/-- **The CDCL loop with watched literals**: up to `2 ^ d` moves (`step`), by running `2 ^ (d - 1)`
moves twice. Each move lowers the measure, so `d` with `S.measure < 2 ^ d` lets the loop run until
it answers or restarts (`solveWith.search`). The recursion is structural on `d`, so the kernel can
run the solver, and the measure is only used in proofs; at run time a move costs no arithmetic on
the bound, and the recursion is at most `d` deep. -/
@[expose] def loop (φ : CNF ℕ) (limit : Option ℕ) (c₀ : ℕ) :
    (d : ℕ) → (S : WExec φ) → S.Inv →
      S.stats.conflicts + S.measure < c₀ + restartBound φ → Run φ limit c₀ S d
  | 0, S, hS, hP => step φ limit c₀ S hS hP
  | d + 1, S, hS, hP =>
    match loop φ limit c₀ d S hS hP with
    | .done r => .done r
    | .restart S' h hr => .restart S' h hr
    | .next T hT hm hc =>
      match loop φ limit c₀ d T hT (by omega) with
      | .done r => .done r
      | .restart S' h hr => .restart S' h hr
      | .next U hU hm' hc' => .next U hU (by rw [Nat.pow_succ]; omega) (by omega)

/-- **Search with restarts**: runs of the loop, the `i`-th restarting after `o.restartBudget i`
conflicts, if restarts are on. A run has fewer conflicts than `restartBound φ`, so a run whose
budget exceeds it does not restart; one comes within `k` runs, so the search ends there. A loop
of `solveWith`, which starts it from `WExec.init φ o`, at the first run, with enough runs. -/
@[expose] def solveWith.search (φ : CNF ℕ) (o : Options) (D : ℕ) (hD : restartBound φ < 2 ^ D) :
    (i k : ℕ) → (S : WExec φ) → S.Inv →
    (∃ j, i ≤ j ∧ j ≤ i + k ∧ restartBound φ < o.restartBudget j) → Answer φ × Stats
  | i, k, S, hS, hk =>
    let limit := if o.restarts then some (S.stats.conflicts + o.restartBudget i) else none
    have hm := hS.measure_lt_restartBound
    match loop φ limit S.stats.conflicts D S hS (by omega) with
    | .done r => r
    | .next _ _ hm' _ => absurd hm' (by omega)
    | .restart S' h hr =>
      -- the run restarted, so its budget is within the bound
      have hi : o.restartBudget i ≤ restartBound φ := by
        obtain ⟨n, hn, hn₁, hle⟩ := hr
        cases ho : o.restarts
        · simp [limit, ho] at hn
        · simp only [limit, ho, ↓reduceIte, Option.some.injEq] at hn
          omega
      match k, hk with
      | 0, hk => absurd hk (by
          rintro ⟨j, h₁, h₂, h₃⟩
          have : j = i := by omega
          subst this
          omega)
      | k + 1, hk => solveWith.search φ o D hD (i + 1) k S' h (by
          obtain ⟨j, h₁, h₂, h₃⟩ := hk
          refine ⟨j, ?_, by omega, h₃⟩
          by_contra hj
          have : j = i := by omega
          subst this
          omega)

/-- **The CDCL solver with options**: a model, or an LRAT certificate of unsatisfiability, with the
statistics of the run. -/
@[expose] def solveWith (o : Options) (φ : CNF ℕ) : DPLL.Result × Stats :=
  match solveWith.search φ o ((restartBound φ).log2 + 1) Nat.lt_log2_self 0
      (o.restartRuns (restartBound φ)) (WExec.init φ o) (WExec.init_inv φ o)
      ⟨_, Nat.zero_le _, by omega, o.lt_restartBudget _⟩ with
  | (.sat σ _, s) => (.sat σ, s)
  | (.unsat cert _, s) => (.unsat cert, s)

/-- **The CDCL solver**, with the default options. -/
@[expose] def solve (φ : CNF ℕ) : DPLL.Result := (solveWith {} φ).1

/-- **The models returned by the solver are models**, whatever the options. -/
theorem solveWith_sat {o : Options} {φ : CNF ℕ} {σ : ℕ → Bool} (h : (solveWith o φ).1 = .sat σ) :
    φ.eval σ = true := by
  unfold solveWith at h
  split at h
  · rename_i hσ _ _
    cases h
    exact hσ
  · cases h

/-- **The certificates returned by the solver are accepted by the LRAT checker**, whatever the
options. -/
theorem solveWith_unsat {o : Options} {φ : CNF ℕ}
    {cert : Array Std.Tactic.BVDecide.LRAT.IntAction} (h : (solveWith o φ).1 = .unsat cert) :
    φ.checkLRAT cert = true := by
  unfold solveWith at h
  split at h
  · cases h
  · rename_i hcert _ _
    cases h
    exact hcert

/-- **The solver decides satisfiability**, whatever the options. -/
theorem isSat_solveWith_iff (o : Options) (φ : CNF ℕ) :
    (solveWith o φ).1.isSat = true ↔ φ.Satisfiable :=
  DPLL.Result.isSat_iff (fun _ => solveWith_sat) (fun _ => solveWith_unsat)

/-- **The models returned by the solver are models.** -/
theorem solve_sat {φ : CNF ℕ} {σ : ℕ → Bool} (h : solve φ = .sat σ) : φ.eval σ = true :=
  solveWith_sat h

/-- **The certificates returned by the solver are accepted by the LRAT checker.** -/
theorem solve_unsat {φ : CNF ℕ} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction}
    (h : solve φ = .unsat cert) : φ.checkLRAT cert = true :=
  solveWith_unsat h

/-- **The solver decides satisfiability.** -/
theorem isSat_solve_iff (φ : CNF ℕ) : (solve φ).isSat = true ↔ φ.Satisfiable :=
  isSat_solveWith_iff {} φ

/-! ### Renaming the variables first -/

/-- **The CDCL solver on renamed variables, with options**: it renames the variables of `φ` to
`0, …, k - 1`, solves the renamed formula, and translates the model or certificate back, so its
arrays are indexed by at most `k` variables. -/
@[expose] def solveCompactWith (o : Options) (φ : CNF ℕ) : DPLL.Result × Stats :=
  match solveWith o (φ.relabel φ.denseRenaming.toDense) with
  | (.sat σ, st) => (.sat (σ ∘ φ.denseRenaming.toDense), st)
  | (.unsat cert, st) => (.unsat (cert.map (relabelAction φ.denseRenaming.fromDense)), st)

/-- **The CDCL solver on renamed variables**, with the default options. -/
@[expose] def solveCompact (φ : CNF ℕ) : DPLL.Result := (solveCompactWith {} φ).1

/-- **The models returned on renamed variables are models.** -/
theorem solveCompactWith_sat {o : Options} {φ : CNF ℕ} {σ : ℕ → Bool}
    (h : (solveCompactWith o φ).1 = .sat σ) : φ.eval σ = true := by
  unfold solveCompactWith at h
  split at h
  · rename_i σ' st hs
    cases h
    simpa using solveWith_sat (congrArg Prod.fst hs)
  · cases h

/-- **The certificates returned on renamed variables are accepted by the LRAT checker.** -/
theorem solveCompactWith_unsat {o : Options} {φ : CNF ℕ}
    {cert : Array Std.Tactic.BVDecide.LRAT.IntAction} (h : (solveCompactWith o φ).1 = .unsat cert) :
    φ.checkLRAT cert = true := by
  unfold solveCompactWith at h
  split at h
  · cases h
  · rename_i c st hs
    cases h
    have := solveWith_unsat (congrArg Prod.fst hs)
    rw [← CNF.checkLRAT_relabel (DenseRenaming.fromDense_injective φ),
      DenseRenaming.relabel_relabel] at this
    exact this

/-- **The solver on renamed variables decides satisfiability**, whatever the options. -/
theorem isSat_solveCompactWith_iff (o : Options) (φ : CNF ℕ) :
    (solveCompactWith o φ).1.isSat = true ↔ φ.Satisfiable :=
  DPLL.Result.isSat_iff (fun _ => solveCompactWith_sat) (fun _ => solveCompactWith_unsat)

theorem solveCompact_sat {φ : CNF ℕ} {σ : ℕ → Bool} (h : solveCompact φ = .sat σ) :
    φ.eval σ = true :=
  solveCompactWith_sat h

theorem solveCompact_unsat {φ : CNF ℕ} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction}
    (h : solveCompact φ = .unsat cert) : φ.checkLRAT cert = true :=
  solveCompactWith_unsat h

theorem isSat_solveCompact_iff (φ : CNF ℕ) : (solveCompact φ).isSat = true ↔ φ.Satisfiable :=
  isSat_solveCompactWith_iff {} φ

end Cslib.Algorithms.Lean.CDCL

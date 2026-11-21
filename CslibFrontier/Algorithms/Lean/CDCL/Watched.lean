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
  undone, and Restart recomputes it from the root of the trail.

The last condition makes the invariant survive Backjump without decision levels: the literals
removed are exactly those above the newest decision, so every processed literal kept was processed
before. It also makes skipping a watcher on a true blocker safe: the literal being processed is
above the newest decision, so any backjump that keeps it false keeps the blocker true. With the
queue empty, no clause of the database is false unless a short one is (`WExec.Inv.noConflict`), so
the loop finds conflicts and units among long clauses without scanning them. Choosing the next
decision variable, or seeing that every variable is assigned and returning the model, still
searches the variables of the database (`CNF.vars`), which can traverse every literal occurrence.

**The loop** (`Cslib.Algorithms.Lean.CDCL.loop`). While the queue is not empty, it processes its
first literal. A conflict with no decision on the trail ends with a certificate; otherwise it is
analysed, the learned clause is minimized (`Cslib.Algorithms.Lean.CDCL.Learned.minimize`), and
Backjump and Learn follow; the variables met by the analysis are bumped
(`Cslib.Algorithms.Lean.CDCL.Activity.bump`). With the queue empty, it checks the short clauses for
a conflict or a unit, then decides an unassigned variable of the database of greatest activity
(VSIDS, `Cslib.Algorithms.Lean.CDCL.WExec.pickVar`), popped from the variable order
(`Cslib.Algorithms.Lean.CDCL.VarOrder.pop`), with its saved phase
(`Cslib.Algorithms.Lean.CDCL.Phases.get`), or returns the trail as a model. Backjump saves the
phases of the literals it undoes (`Cslib.Algorithms.Lean.CDCL.Phases.save`), and puts the variables
bumped and undone back in the variable order, keeping its invariant
(`Cslib.Algorithms.Lean.CDCL.WExec.OrderInv`), under which the decision variable has the greatest
activity (`Cslib.Algorithms.Lean.CDCL.WExec.Inv.pickVar_max`). Every move lowers
the measure: the rank of the abstract system, times the number of variables plus two, plus the
length of the queue. Recursion is structural on a bound on the measure, which provably never runs
out, so the kernel can run the solver.

**Reducing the learned clauses** (`Cslib.Algorithms.Lean.CDCL.WExec.maybeReduce`). As in
MiniSat's `reduceDB`, once the learned clauses exceed the assigned variables by a limit, which
grows on a schedule, the less active half of them is forgotten
(`Cslib.Algorithms.Lean.CDCL.Exec.forget`), except the reasons of the trail and the clauses of at
most two literals, and the watch store is rebuilt on the trail
(`Cslib.Algorithms.Lean.CDCL.WatchStore.build`). This happens with the queue empty and no clause
false, and keeps the measure.

**Restarts** (`Cslib.Algorithms.Lean.CDCL.search`). As in MiniSat, once a run of the loop has had
its budget of conflicts (`restartFirst` times the Luby sequence, `Options.restartBudget`), at the
next point with an empty queue and no conflict it goes back to the root of the trail, the literals
implied below every decision (`WExec.restart`), keeping the learned clauses, the activities and
the phases. Restarts raise the measure, so each run is bounded by its own measure, and the runs
are bounded by an allowance of `2 ^ 64` restarts (`restartAllowance`), after which the solver no
longer restarts; termination is structural on both.

## Main definitions

* `Cslib.Algorithms.Lean.CDCL.WExec`, `Cslib.Algorithms.Lean.CDCL.WExec.Inv`: the state and its
  invariant.
* `Cslib.Algorithms.Lean.CDCL.WExec.processList`: visiting a watch list.
* `Cslib.Algorithms.Lean.CDCL.Reduction`, `Cslib.Algorithms.Lean.CDCL.WExec.reduce`: the reduction
  of the learned clauses.
* `Cslib.Algorithms.Lean.CDCL.loop`, `Cslib.Algorithms.Lean.CDCL.search`,
  `Cslib.Algorithms.Lean.CDCL.solve`: the solver.
* `Cslib.Algorithms.Lean.CDCL.Options`, `Cslib.Algorithms.Lean.CDCL.Stats`,
  `Cslib.Algorithms.Lean.CDCL.solveWith`: the solver with options, returning its statistics.

## Main results

* `Cslib.Algorithms.Lean.CDCL.solve_sat`, `Cslib.Algorithms.Lean.CDCL.solve_unsat`: both answers are
  correct.
* `Cslib.Algorithms.Lean.CDCL.isSat_solve_iff`: the solver decides satisfiability.
* `Cslib.Algorithms.Lean.CDCL.isSat_solveWith_iff`: so it does whatever the options.
* `Cslib.Algorithms.Lean.CDCL.WExec.Inv.pickVar_max`: with VSIDS, every decision is of greatest
  activity among the unassigned variables.
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

variable {φ : CNF ℕ}

/-- **Options** of the solver, after MiniSat's: VSIDS for the decision variable (otherwise the
first unassigned variable of the database); phase saving for its polarity (MiniSat's
`phase_saving = 2`; otherwise `false`, MiniSat's `phase_saving = 0`); and restarts, the `i`-th
after `restartFirst * luby restartInc i` more conflicts (MiniSat's `luby_restart`), or
`restartFirst * restartInc ^ i` without `luby`; the minimization of learned clauses (MiniSat's
`ccmin_mode = 2`; otherwise `0`); and the reduction of the learned clauses (MiniSat's `reduceDB`;
otherwise they are kept). None affects correctness. -/
structure Options where
  /-- Choose decision variables by VSIDS. -/
  vsids : Bool := true
  /-- Choose polarities by phase saving. -/
  phaseSaving : Bool := true
  /-- Restart. -/
  restarts : Bool := true
  /-- Space the restarts by the Luby sequence, rather than geometrically. -/
  luby : Bool := true
  /-- The conflicts before the first restart (MiniSat's `restart_first`). -/
  restartFirst : ℕ := 100
  /-- The growth of the conflicts between restarts (MiniSat's `restart_inc`). -/
  restartInc : ℕ := 2
  /-- Minimize the learned clauses. -/
  minimize : Bool := true
  /-- Forget learned clauses of low activity. -/
  reduce : Bool := true
  /-- The limit on the learned clauses starts at the clauses of the formula divided by this
  (MiniSat's `1 / learntsize_factor`). -/
  learntsDivisor : ℕ := 3
  deriving Repr

/-- The conflicts allowed before the restart numbered `i`, at least one. -/
@[expose] def Options.restartBudget (o : Options) (i : ℕ) : ℕ :=
  max 1 (o.restartFirst * if o.luby then CDCL.luby o.restartInc i else o.restartInc ^ i)

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
  deriving Repr

/-- One more literal taken from the propagation queue. -/
@[expose] def Stats.propagation (s : Stats) : Stats := { s with propagations := s.propagations + 1 }

/-- One more decision. -/
@[expose] def Stats.decision (s : Stats) : Stats := { s with decisions := s.decisions + 1 }

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
the log's next number being `next`: the clause activities are bumped and decay, the learned clause
is counted if it is `stored`, and the limit grows on schedule. -/
@[expose]
def Reduction.learn (R : Reduction) (used : List ℕ) (id next : ℕ) (stored : Bool) : Reduction :=
  let act := (R.act.grow next).bump (id :: used) 999
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
  /-- The watch store. -/
  store : WatchStore
  /-- The literals still to be processed. -/
  queue : List (Literal ℕ)
  /-- The clauses with fewer than two different literals. -/
  short : List (ℕ × Clause ℕ)
  /-- The variable activities of VSIDS, which choose the decision variables. -/
  act : Activity
  /-- The variable order of VSIDS, a heap of the variables by activity. -/
  order : VarOrder
  /-- The saved phases, which choose the polarities of the decisions. -/
  phase : Phases
  /-- The reduction of the learned clauses. -/
  red : Reduction
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

/-- **The invariant of the variable order** over the variables of `φ`. -/
abbrev WExec.OrderInv (S : WExec φ) : Prop := S.order.Inv S.act φ.vars S.M

/-- The invariant of the variable order survives assigning more variables. -/
theorem WExec.OrderInv.extend {S S' : WExec φ} (h : S.OrderInv) (horder : S'.order = S.order)
    (hact : S'.act = S.act) (hM : ∀ v ∈ Trail.vars S.M, v ∈ Trail.vars S'.M) : S'.OrderInv := by
  refine ⟨horder ▸ h.wf, horder ▸ h.vars, fun v hv hvM => ?_⟩
  rw [horder, hact]
  exact h.covers v hv fun h' => hvM (hM v h')

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

/-- The number of slots for arrays indexed by the variables of `φ`: one more than the largest
variable, and `0` when `φ` has no variables (`[]` and `[[]]`). -/
@[expose] def varSlots (φ : CNF ℕ) : ℕ := φ.vars.foldl (fun m v => max m (v + 1)) 0

/-- The initial state, with the options `o`. -/
@[expose] def WExec.init (φ : CNF ℕ) (o : Options) : WExec φ :=
  ⟨Exec.init φ, ⟨#[]⟩, WatchStore.build ⟨#[]⟩ φ.lratDB, [],
    φ.lratDB.filter fun e => e.2.dedup.length < 2,
    Activity.init (varSlots φ),
    if o.vsids then
      VarOrder.insertVars Batteries.BinaryHeap.emptyF (Activity.init (varSlots φ))
        φ.vars.dedup
    else Batteries.BinaryHeap.emptyF,
    Phases.init (varSlots φ), Reduction.init φ.length o.learntsDivisor, o, {},
    ⟨⟨#[]⟩, fun v => by simp [Assign.value]⟩⟩

theorem WExec.init_inv (φ : CNF ℕ) (o : Options) : (WExec.init φ o).Inv where
  exec := Exec.init_inv φ
  store := WatchStore.build_inv Assign.agrees_nil φ.lratDB fun e _ hlen hf => by
    obtain ⟨l, hl⟩ := List.exists_mem_of_length_pos (by omega : 0 < e.2.dedup.length)
    simpa [Trail.lits] using hf l (List.mem_dedup.1 hl)
  short_mem e he := (List.mem_filter.1 he).1
  short_covers e he hlen := List.mem_filter.2 ⟨he, by simpa using hlen⟩
  queue_nodup := List.nodup_nil
  queue_trail _ h := absurd h List.not_mem_nil
  queue_above _ h := absurd h List.not_mem_nil
  assign := Assign.agrees_nil
  order hv := by
    change VarOrder.Inv (if o.vsids then _ else _) _ _ _
    have hv' : o.vsids = true := hv
    simp only [hv', ↓reduceIte]
    have hempty : (Batteries.BinaryHeap.emptyF : VarOrder).WF := by
      rw [Batteries.BinaryHeap.emptyF_eq]; exact Batteries.BinaryHeap.empty_wf
    refine ⟨VarOrder.insertVars_wf hempty, fun e he => ?_,
      fun v hv _ => ⟨_, le_rfl, VarOrder.mem_insertVars.2 (.inr ⟨v, List.mem_dedup.2 hv, rfl⟩)⟩⟩
    rcases VarOrder.mem_insertVars.1 he with he | ⟨v, hv, rfl⟩
    · rw [Batteries.BinaryHeap.emptyF_eq] at he
      exact absurd he Batteries.BinaryHeap.mem_empty
    · exact List.mem_dedup.1 hv

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
  simp only [Trail.lits, List.length_map, WExec.M] at h₁
  simp only [nvars]
  omega

theorem watchIndex_inj {a b : Literal ℕ} (h : watchIndex a = watchIndex b) : a = b := by
  obtain ⟨v, x⟩ := a
  obtain ⟨w, y⟩ := b
  simp only [watchIndex] at h
  cases x <;> cases y <;> simp at h ⊢ <;> omega

/-! ### Processing a literal -/

/-- The invariant while visiting the watch list of `t.negate`, with the watchers `L` still to be
visited: as `WExec.Inv`, except that a clause watching `t.negate` may have its watcher among `L`
instead of on the watch list, and every clause with a watcher put back on that list has a true
literal. -/
structure WExec.ProcInv (S : WExec φ) (t : Literal ℕ) (L : List Watcher) : Prop where
  exec : S.exec.Inv
  sound : ∀ e ∈ S.store.clauses, ∃ c, (e.1, c) ∈ S.exec.db ∧ ∀ l, l ∈ e.2 ↔ l ∈ c
  nodup : ∀ e ∈ S.store.clauses, e.2.Nodup
  long : ∀ e ∈ S.store.clauses, 2 ≤ e.2.length
  covers : ∀ e ∈ S.exec.db, 2 ≤ e.2.dedup.length →
    ∃ e' ∈ S.store.clauses, e'.1 = e.1 ∧ ∀ l, l ∈ e'.2 ↔ l ∈ e.2
  listed : ∀ (k : ℕ) (hk : k < S.store.clauses.size), ∀ w ∈ S.store.clauses[k].2.take 2,
    k ∈ clauseIds (watchList S.store.watches (watchIndex w)) ∨
      (w = t.negate ∧ k ∈ clauseIds L)
  blocker_mem : ∀ i, ∀ x ∈ watchList S.store.watches i,
    ∃ (hk : x.clause < S.store.clauses.size), x.blocker ∈ S.store.clauses[x.clause].2
  pending : ∀ x ∈ L,
    ∃ (hk : x.clause < S.store.clauses.size), x.blocker ∈ S.store.clauses[x.clause].2
  visited : ∀ k ∈ clauseIds (watchList S.store.watches (watchIndex t.negate)),
    ∀ (hk : k < S.store.clauses.size), ∃ b ∈ S.store.clauses[k].2, b ∈ Trail.lits S.M
  covered : ∀ e ∈ S.store.clauses, ∀ w₁ w₂ rest, e.2 = w₁ :: w₂ :: rest →
    Processed S.M S.queue w₁.negate → Processed S.M S.queue w₂.negate →
    ∃ b ∈ e.2, Supported S.M b w₁ w₂
  short_mem : ∀ e ∈ S.short, e ∈ S.exec.db
  short_covers : ∀ e ∈ S.exec.db, e.2.dedup.length < 2 → e ∈ S.short
  queue_nodup : S.queue.Nodup
  queue_trail : ∀ x ∈ S.queue, x ∈ Trail.lits S.M
  queue_above : ∀ x ∈ S.queue, ∀ N d M₀, S.M = N ++ ⟨d, true⟩ :: M₀ → x ∉ Trail.lits M₀
  t_mem : t ∈ S.queue
  order : S.opts.vsids = true → S.OrderInv
  assign : S.assign.Agrees S.M

/-- Starting to process `t`: its negation's watch list is emptied and becomes the list to visit. -/
@[expose] def WExec.start (S : WExec φ) (t : Literal ℕ) : WExec φ :=
  { S with
    store := { S.store with watches := setWatch S.store.watches (watchIndex t.negate) [] }
    stats := S.stats.propagation }

theorem WExec.start_procInv {S : WExec φ} (h : S.Inv) {t : Literal ℕ} (ht : t ∈ S.queue) :
    (S.start t).ProcInv t (watchList S.store.watches (watchIndex t.negate)) where
  exec := h.exec
  sound := h.store.sound
  nodup := h.store.nodup
  long := h.store.long
  covers := h.store.covers
  listed k hk w hw := by
    have := h.store.listed k hk w hw
    simp only [WExec.start, watchList_setWatch]
    by_cases hw' : w = t.negate
    · exact .inr ⟨hw', hw' ▸ this⟩
    · have hne : ¬ watchIndex w = watchIndex t.negate := fun h => hw' (watchIndex_inj h)
      exact .inl (by simp only [hne, ↓reduceIte]; exact this)
  blocker_mem i x hx := by
    simp only [WExec.start, watchList_setWatch] at hx
    split at hx
    · simp at hx
    · exact h.store.blocker_mem i x hx
  pending x hx := h.store.blocker_mem _ x hx
  visited k hk := by simp [WExec.start] at hk
  covered := h.store.covered
  short_mem := h.short_mem
  short_covers := h.short_covers
  queue_nodup := h.queue_nodup
  queue_trail := h.queue_trail
  queue_above := h.queue_above
  t_mem := ht
  order := h.order
  assign := h.assign

/-- Finishing the processing of `t`: removing it from the queue. -/
@[expose]
def WExec.finish (S : WExec φ) (t : Literal ℕ) : WExec φ := { S with queue := S.queue.erase t }

theorem WExec.finish_inv {S : WExec φ} {t : Literal ℕ} (h : S.ProcInv t []) :
    (S.finish t).Inv ∧ (S.finish t).measure < S.measure := by
  have hprocessed : ∀ x, Processed S.M (S.queue.erase t) x → Processed S.M S.queue x ∨ x = t :=
    fun x ⟨hx, hxq⟩ => by
      by_cases hxt : x = t
      · exact .inr hxt
      · exact .inl ⟨hx, fun hq => hxq ((List.mem_erase_of_ne hxt).2 hq)⟩
  -- a clause watching `t.negate` has a true literal, and `t` is above the newest decision
  have hsupp : ∀ (k : ℕ) (hk : k < S.store.clauses.size) (w₁ w₂ : Literal ℕ) (rest : Clause ℕ),
      S.store.clauses[k].2 = w₁ :: w₂ :: rest → (w₁.negate = t ∨ w₂.negate = t) →
      ∃ b ∈ S.store.clauses[k].2, Supported S.M b w₁ w₂ := by
    intro k hk w₁ w₂ rest hc hwt
    obtain ⟨w, hw, hwt', hw₁₂⟩ : ∃ w ∈ S.store.clauses[k].2.take 2, w.negate = t ∧
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
    h.short_mem, h.short_covers, h.queue_nodup.erase t,
    fun x hx => h.queue_trail x (List.mem_of_mem_erase hx),
    fun x hx => h.queue_above x (List.mem_of_mem_erase hx), h.order, h.assign⟩, ?_⟩
  · rcases h.listed k hk w hw with hl | ⟨-, hL⟩
    · exact hl
    · simp at hL
  · intro e he w₁ w₂ rest hc h₁ h₂
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 he
    rcases hprocessed _ h₁ with h₁ | h₁
    · rcases hprocessed _ h₂ with h₂ | h₂
      · exact h.covered _ he w₁ w₂ rest hc h₁ h₂
      · exact hsupp k hk w₁ w₂ rest hc (.inr h₂)
    · exact hsupp k hk w₁ w₂ rest hc (.inl h₁)
  · simp only [WExec.measure, WExec.finish]
    have := List.length_erase_of_mem h.t_mem
    have : 0 < S.queue.length := List.length_pos_of_mem h.t_mem
    omega

private theorem watchInj_mem {W : Array (List Watcher)} {a b : Literal ℕ} {k : ℕ}
    (h : watchIndex a = watchIndex b) (hk : k ∈ clauseIds (watchList W (watchIndex a))) :
    k ∈ clauseIds (watchList W (watchIndex b)) := h ▸ hk

theorem otherWatch_spec {u w₁ w₂ : Literal ℕ} (hne : w₁ ≠ w₂) :
    (w₁ = u → otherWatch u w₁ w₂ = w₂) ∧ (w₂ = u → otherWatch u w₁ w₂ = w₁) := by
  refine ⟨fun h => by simp [otherWatch, h], fun h => ?_⟩
  have : w₁ ≠ u := fun h' => hne (h'.trans h.symm)
  simp [otherWatch, this]

theorem otherWatch_mem {u w₁ w₂ : Literal ℕ} {rest : Clause ℕ} :
    otherWatch u w₁ w₂ ∈ w₁ :: w₂ :: rest := by
  unfold otherWatch; split <;> simp

/-- Putting a watcher back on the watch list of `t.negate`. -/
@[expose] def WExec.putBack (S : WExec φ) (t : Literal ℕ) (x : Watcher) : WExec φ :=
  { S with store := { S.store with
      watches := addWatch S.store.watches (watchIndex t.negate) x } }

/-- **Putting back** the watcher `w` just visited, or a watcher of the same clause, with a blocker
of the clause, when the clause has a true literal. -/
theorem WExec.ProcInv.putBack {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    (h : S.ProcInv t (w :: L)) (x : Watcher) (hx : x.clause = w.clause)
    (hmem : ∃ (hk : x.clause < S.store.clauses.size), x.blocker ∈ S.store.clauses[x.clause].2)
    (htrue : ∀ (hk : x.clause < S.store.clauses.size),
      ∃ b ∈ S.store.clauses[x.clause].2, b ∈ Trail.lits S.M) :
    (S.putBack t x).ProcInv t L := by
  refine ⟨h.exec, h.sound, h.nodup, h.long, h.covers, fun k' hk' w' hw' => ?_, fun i y hy => ?_,
    fun y hy => h.pending y (List.mem_cons_of_mem _ hy), fun k' hk'' hk' => ?_, h.covered,
    h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem,
    h.order, h.assign⟩
  · simp only [WExec.putBack, watchList_addWatch]
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
  · simp only [WExec.putBack, watchList_addWatch, ↓reduceIte, List.map_cons, List.mem_cons]
      at hk''
    rcases hk'' with rfl | hk''
    · exact htrue hk'
    · exact h.visited k' hk'' hk'

/-- A stored clause has two watched literals. -/
theorem WExec.ProcInv.exists_cons {S : WExec φ} {t : Literal ℕ} {L : List Watcher}
    (h : S.ProcInv t L) {k : ℕ} (hk : k < S.store.clauses.size) :
    ∃ w₁ w₂ rest, S.store.clauses[k].2 = w₁ :: w₂ :: rest := by
  have := h.long _ (Array.getElem_mem hk)
  match hc : S.store.clauses[k].2, this with
  | w₁ :: w₂ :: rest, _ => exact ⟨w₁, w₂, rest, rfl⟩

/-- **Skipping** a watcher whose blocker is true: it goes back on the watch list. -/
theorem WExec.ProcInv.skip {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    (h : S.ProcInv t (w :: L)) (hv : VisitSpec S.store S.M t.negate w .skip) :
    (S.putBack t w).ProcInv t L :=
  h.putBack w rfl (h.pending w List.mem_cons_self) fun _ => by
    obtain ⟨_, hb⟩ := h.pending w List.mem_cons_self
    exact ⟨w.blocker, hb, hv⟩

/-- **Keeping** a clause whose other watched literal is true: it goes back on the watch list, with
that literal as blocker. -/
theorem WExec.ProcInv.keep {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    {b : Literal ℕ} (h : S.ProcInv t (w :: L)) (hv : VisitSpec S.store S.M t.negate w (.keep b)) :
    (S.putBack t ⟨w.clause, b⟩).ProcInv t L := by
  obtain ⟨hk, w₁, w₂, rest, hc, -, rfl, hb⟩ := hv
  have hbmem : otherWatch t.negate w₁ w₂ ∈ S.store.clauses[w.clause].2 :=
    hc ▸ otherWatch_mem
  exact h.putBack _ rfl ⟨hk, hbmem⟩ fun _ => ⟨_, hbmem, hb⟩

/-- **Dropping** a watcher whose clause no longer watches the literal. -/
theorem WExec.ProcInv.drop {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    (h : S.ProcInv t (w :: L)) (hv : VisitSpec S.store S.M t.negate w .drop) :
    S.ProcInv t L := by
  refine ⟨h.exec, h.sound, h.nodup, h.long, h.covers, fun k' hk' w' hw' => ?_, h.blocker_mem,
    fun y hy => h.pending y (List.mem_cons_of_mem _ hy), h.visited, h.covered, h.short_mem,
    h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem,
    h.order, h.assign⟩
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

private theorem mem_setIfInBounds_cases {α : Type} {a : Array α} {k : ℕ} {x e : α}
    (he : e ∈ a.setIfInBounds k x) : e = x ∨ e ∈ a := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 he
  have hi' : i < a.size := by simpa using hi
  by_cases hik : k = i
  · subst hik; left; simp
  · right; rw [Array.getElem_setIfInBounds_ne hi' hik]; exact Array.getElem_mem _

/-- **Moving** a watch to a literal that is not false. -/
theorem WExec.ProcInv.move {S : WExec φ} {t : Literal ℕ} {w : Watcher} {L : List Watcher}
    {S' : WatchStore} (h : S.ProcInv t (w :: L))
    (hv : VisitSpec S.store S.M t.negate w (.move S')) :
    ({ S with store := S' } : WExec φ).ProcInv t L := by
  obtain ⟨hk, id, w₁, w₂, x, rest, hc, hu, hx, hxf, rfl⟩ := hv
  set k := w.clause with hkdef
  set u := t.negate
  set o := otherWatch u w₁ w₂
  set C' := S.store.clauses.setIfInBounds k (id, o :: x :: u :: rest.erase x) with hC'
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := u) hne
  -- the new clause is a permutation of the old one
  have hxu : x ≠ u := by
    rintro rfl
    exact hxf (by rw [negate_negate]; exact h.queue_trail t h.t_mem)
  have hperm : (o :: x :: u :: rest.erase x).Perm (w₁ :: w₂ :: rest) := by
    have hrest : (x :: rest.erase x).Perm rest := (List.perm_cons_erase hx).symm
    rcases hu with h₁ | h₂
    · have : o = w₂ := ho₁ h₁
      rw [this, h₁]
      exact ((List.Perm.swap u x _).cons w₂).trans
        ((List.Perm.swap u w₂ _).trans ((hrest.cons w₂).cons u))
    · have : o = w₁ := ho₂ h₂
      rw [this, h₂]
      exact List.Perm.cons _ ((List.Perm.swap _ _ _).trans (List.Perm.cons _ hrest))
  have hold : S.store.clauses[k] = (id, w₁ :: w₂ :: rest) := hc
  have hmem : ∀ e ∈ C', e = (id, o :: x :: u :: rest.erase x) ∨ e ∈ S.store.clauses :=
    fun e he => mem_setIfInBounds_cases he
  have hsize : C'.size = S.store.clauses.size := by simp [hC']
  have hou : o ≠ u := by
    change otherWatch u w₁ w₂ ≠ u
    rcases hu with h₁ | h₂
    · rw [ho₁ h₁]; exact fun h₂ => hne (h₁.trans h₂.symm)
    · rw [ho₂ h₂]; exact fun h₁ => hne (h₁.trans h₂.symm)
  have hotake : o ∈ (S.store.clauses[k].2).take 2 := by
    change otherWatch u w₁ w₂ ∈ _
    rw [hold]
    rcases hu with h₁ | h₂
    · simp [ho₁ h₁]
    · simp [ho₂ h₂]
  have hidx : watchIndex u ≠ watchIndex x := fun h => hxu (watchIndex_inj h).symm
  have hnew : ∀ (hk' : k < C'.size), C'[k] = (id, o :: x :: u :: rest.erase x) :=
    fun _ => by simp [hC']
  have hothers : ∀ i (hi : i < S.store.clauses.size), i ≠ k →
      C'[i]'(by rw [hsize]; exact hi) = S.store.clauses[i] :=
    fun i hi hik => Array.getElem_setIfInBounds_ne hi (Ne.symm hik)
  -- every clause keeps its literals
  have hlits : ∀ i (hi : i < S.store.clauses.size) (b : Literal ℕ), b ∈ S.store.clauses[i].2 →
      b ∈ (C'[i]'(by rw [hsize]; exact hi)).2 := by
    intro i hi b hb
    by_cases hik : i = k
    · subst hik
      rw [hnew, hperm.mem_iff]
      rw [hold] at hb
      exact hb
    · rw [hothers i hi hik]; exact hb
  have hpres : ∀ y : Watcher, (∃ (hk : y.clause < S.store.clauses.size),
      y.blocker ∈ S.store.clauses[y.clause].2) →
      ∃ (hk : y.clause < C'.size), y.blocker ∈ C'[y.clause].2 :=
    fun y ⟨hy, hb⟩ => ⟨by rw [hsize]; exact hy, hlits _ hy _ hb⟩
  refine ⟨h.exec, ?_, ?_, ?_, ?_, ?_, fun i y hy => ?_, fun y hy => ?_, ?_, ?_, h.short_mem,
    h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above, h.t_mem,
    h.order, h.assign⟩
  · intro e he
    rcases hmem e he with rfl | he
    · obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
      rw [hold] at hcdb hceq
      exact ⟨c, hcdb, fun l => (hperm.mem_iff).trans (hceq l)⟩
    · exact h.sound e he
  · intro e he
    rcases hmem e he with rfl | he
    · exact hperm.nodup_iff.2 hnd
    · exact h.nodup e he
  · intro e he
    rcases hmem e he with rfl | he
    · simp
    · exact h.long e he
  · intro e he hlen
    obtain ⟨e', he', hid, heq⟩ := h.covers e he hlen
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 he'
    by_cases hik : i = k
    · subst hik
      refine ⟨(id, o :: x :: u :: rest.erase x), Array.mem_iff_getElem.2
        ⟨k, by rw [hsize]; exact hi, hnew _⟩, ?_, fun l => ?_⟩
      · rw [← hid, hold]
      · rw [← heq l, hold]; exact hperm.mem_iff
    · exact ⟨_, Array.mem_iff_getElem.2 ⟨i, by rw [hsize]; exact hi, hothers i hi hik⟩, hid, heq⟩
  · intro k' hk' w' hw
    simp only [watchList_addWatch]
    have hk'' : k' < S.store.clauses.size := by rw [← hsize]; exact hk'
    by_cases hkk : k' = k
    · subst hkk
      simp only [hnew, List.take_succ_cons, List.take_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw
      · rw [hw]
        rcases h.listed _ hk'' _ hotake with hl | ⟨hw', -⟩
        · left; split
          · exact List.mem_cons_of_mem _ (by rename_i hi; exact hi ▸ hl)
          · exact hl
        · exact absurd hw' hou
      · rw [hw]; simp
    · simp only [hothers k' hk'' hkk] at hw ⊢
      rcases h.listed k' hk'' w' hw with hl | ⟨hw', hL⟩
      · left; split
        · exact List.mem_cons_of_mem _ (by rename_i hi; exact hi ▸ hl)
        · exact hl
      · exact .inr ⟨hw', (List.mem_cons.1 hL).resolve_left hkk⟩
  · rcases mem_watchList_addWatch hy with rfl | hy
    · exact ⟨by rw [hsize]; exact hk, by rw [hnew]; simp⟩
    · exact hpres y (h.blocker_mem i y hy)
  · exact hpres y (h.pending y (List.mem_cons_of_mem _ hy))
  · intro k' hk' hk''
    simp only [watchList_addWatch] at hk'
    replace hk' : k' ∈ clauseIds (watchList S.store.watches (watchIndex t.negate)) := by
      split at hk'
      · exact absurd ‹_› hidx
      · exact hk'
    have hk''' : k' < S.store.clauses.size := by rw [← hsize]; exact hk''
    obtain ⟨b, hb, hbM⟩ := h.visited k' hk' hk'''
    exact ⟨b, hlits k' hk''' b hb, hbM⟩
  · intro e he v₁ v₂ rest' hc' _ h₂
    rcases hmem e he with rfl | he
    · simp only [List.cons.injEq] at hc'
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
    exec := S.exec.propagate (id, []) l, assign := S.assign.assign l, queue := l :: S.queue }

/-- **A unit clause**: its other watched literal is propagated and queued, and its watcher goes
back on the watch list with that literal as blocker. -/
theorem WExec.ProcInv.unit {S : WExec φ} {t l : Literal ℕ} {id : ℕ} {w : Watcher}
    {L : List Watcher} (h : S.ProcInv t (w :: L))
    (hv : VisitSpec S.store S.M t.negate w (.unit l id)) :
    ((S.propagateUnit l id).putBack t ⟨w.clause, l⟩).ProcInv t L ∧
      ((S.propagateUnit l id).putBack t ⟨w.clause, l⟩).measure < S.measure := by
  obtain ⟨hk, w₁, w₂, rest, hc, hu, rfl, hl, hln, hrest⟩ := hv
  set u := t.negate
  set o := otherWatch u w₁ w₂
  have hnd := h.nodup _ (Array.getElem_mem hk)
  rw [hc] at hnd
  have hne : w₁ ≠ w₂ := fun he => (List.nodup_cons.1 hnd).1 (he ▸ List.mem_cons_self)
  obtain ⟨ho₁, ho₂⟩ := otherWatch_spec (u := u) hne
  obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
  rw [hc] at hcdb hceq
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
  have hM : (S.propagateUnit o id).M = ⟨o, false⟩ :: S.M := rfl
  have hlits : Trail.lits (S.propagateUnit o id).M = o :: Trail.lits S.M := by rw [hM]; rfl
  have hproc : ∀ x, Processed (S.propagateUnit o id).M (S.propagateUnit o id).queue x →
      Processed S.M S.queue x := by
    intro x ⟨hx, hxq⟩
    rw [hlits] at hx
    simp only [WExec.propagateUnit, List.mem_cons, not_or] at hxq
    exact ⟨(List.mem_cons.1 hx).resolve_left hxq.1, hxq.2⟩
  have h' : (S.propagateUnit o id).ProcInv t (w :: L) := by
    refine ⟨hspec.1, h.sound, h.nodup, h.long, h.covers, h.listed, h.blocker_mem, h.pending,
      fun k' hk' hk'' => ?_, fun e he v₁ v₂ rest' hc' h₁ h₂ => ?_, h.short_mem, h.short_covers,
      ?_, ?_, ?_, List.mem_cons_of_mem _ h.t_mem,
      fun hv => (h.order hv).extend rfl rfl fun v hv => List.mem_cons_of_mem _ hv,
      by rw [hM]; exact h.assign.cons (not_mem_vars_of_undef hl hln) false⟩
    · obtain ⟨b, hb, hbM⟩ := h.visited k' hk' hk''
      exact ⟨b, hb, by rw [hlits]; exact List.mem_cons_of_mem _ hbM⟩
    · obtain ⟨b, hb, hs⟩ := h.covered e he v₁ v₂ rest' hc' (hproc _ h₁) (hproc _ h₂)
      exact ⟨b, hb, hM ▸ hs.cons _⟩
    · exact List.nodup_cons.2 ⟨fun hq => hl (h.queue_trail _ hq), h.queue_nodup⟩
    · intro x hx
      rw [hlits]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h.queue_trail x hx)
    · intro x hx N d M₀ hN
      cases N with
      | nil => simp [hM] at hN
      | cons y N =>
        rw [hM] at hN
        simp only [List.cons_append, List.cons.injEq] at hN
        rcases List.mem_cons.1 hx with rfl | hx
        · intro hxM₀
          apply hl
          rw [hN.2, lits_append]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ hxM₀)
        · exact h.queue_above x hx N d M₀ hN.2
  have homem : o ∈ S.store.clauses[w.clause].2 := hc ▸ otherWatch_mem
  refine ⟨h'.putBack ⟨w.clause, o⟩ rfl ⟨hk, homem⟩
    fun _ => ⟨o, homem, by rw [hlits]; exact List.mem_cons_self⟩, ?_⟩
  simp only [WExec.measure, WExec.putBack, WExec.propagateUnit, List.length_cons]
  have : rank φ.vars (S.exec.propagate (id, []) o).state < rank φ.vars S.exec.state := hspec.2
  nlinarith

private theorem mem_clauseIds_append {A B : List Watcher} {k : ℕ} :
    k ∈ clauseIds (A ++ B) ↔ k ∈ clauseIds A ∨ k ∈ clauseIds B := by
  simp [clauseIds]

/-- Restoring the watch list of `t.negate` after a conflict, with the watchers `L` still to be
visited. -/
@[expose] def WExec.restore (S : WExec φ) (t : Literal ℕ) (L : List Watcher) : WExec φ :=
  let i := watchIndex t.negate
  let W := setWatch S.store.watches i (L ++ watchList S.store.watches i)
  { S with store := { S.store with watches := W } }

theorem WExec.ProcInv.restore_inv {S : WExec φ} {t : Literal ℕ} {L : List Watcher}
    (h : S.ProcInv t L) : (S.restore t L).Inv ∧ (S.restore t L).measure = S.measure := by
  refine ⟨⟨h.exec, ⟨h.sound, h.nodup, h.long, h.covers, fun k' hk' w hw => ?_, fun i y hy => ?_,
    h.covered⟩, h.short_mem, h.short_covers, h.queue_nodup, h.queue_trail, h.queue_above,
    h.order, h.assign⟩, rfl⟩
  · simp only [WExec.restore, watchList_setWatch]
    rcases h.listed k' hk' w hw with hl | ⟨rfl, hL⟩
    · split
      · rename_i hi
        exact mem_clauseIds_append.2 (.inr (watchInj_mem hi hl))
      · exact hl
    · simp only [↓reduceIte]
      exact mem_clauseIds_append.2 (.inl hL)
  · simp only [WExec.restore, watchList_setWatch] at hy
    split at hy
    · rename_i hi
      rcases List.mem_append.1 hy with hy | hy
      · exact h.pending y hy
      · exact h.blocker_mem _ y hy
    · exact h.blocker_mem i y hy

/-- **A conflict**: the clause numbered `id` is a clause of the database, the log names it, and the
trail falsifies it. -/
theorem WExec.ProcInv.conflict_clause {S : WExec φ} {t : Literal ℕ} {w : Watcher}
    {L : List Watcher} {id : ℕ} (h : S.ProcInv t (w :: L))
    (hv : VisitSpec S.store S.M t.negate w (.conflict id)) :
    ∃ c, (id, c) ∈ S.exec.db ∧ S.exec.log.clause? id = some c ∧ Trail.Falsifies S.M c := by
  obtain ⟨hk, w₁, w₂, rest, hc, hu, hoth, hrest⟩ := hv
  obtain ⟨c, hcdb, hceq⟩ := h.sound _ (Array.getElem_mem hk)
  rw [hc] at hcdb hceq
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

/-- The result of visiting a watch list from the state `S₀`: done, or a conflict. -/
inductive ProcResult (φ : CNF ℕ) (S₀ : WExec φ) (t : Literal ℕ) : Type
  /-- Every watcher on the list was visited. -/
  | done (S : WExec φ) (h : S.ProcInv t []) (hm : S.measure ≤ S₀.measure)
  /-- A clause of the database is false. -/
  | conflict (S : WExec φ) (h : S.Inv) (e : ℕ × Clause ℕ) (he : e ∈ S.exec.db)
      (hconf : Trail.Falsifies S.M e.2) (hm : S.measure ≤ S₀.measure)

/-- A result from a state of smaller measure is a result from `S₀`. -/
@[expose] def ProcResult.weaken {S₀ S₁ : WExec φ} {t : Literal ℕ} (hle : S₁.measure ≤ S₀.measure) :
    ProcResult φ S₁ t → ProcResult φ S₀ t
  | .done S h hm => .done S h (hm.trans hle)
  | .conflict S h e he hc hm => .conflict S h e he hc (hm.trans hle)

/-- **Visiting a watch list**: every watcher on `L` is visited in turn, until a conflict. -/
@[expose]
def WExec.processList (t : Literal ℕ) : (L : List Watcher) → (S : WExec φ) → S.ProcInv t L →
    ProcResult φ S t
  | [], S, h => .done S h le_rfl
  | w :: L, S, h =>
    match hv : S.store.visit S.assign t.negate w with
    | .skip =>
      have hs : VisitSpec S.store S.M t.negate w .skip :=
        hv ▸ S.store.visit_spec h.assign t.negate w
      (WExec.processList t L _ (h.skip hs)).weaken (S₀ := S) (by exact le_rfl)
    | .keep b =>
      have hs : VisitSpec S.store S.M t.negate w (.keep b) :=
        hv ▸ S.store.visit_spec h.assign t.negate w
      (WExec.processList t L _ (h.keep hs)).weaken (S₀ := S) (by exact le_rfl)
    | .move S' =>
      have hs : VisitSpec S.store S.M t.negate w (.move S') :=
        hv ▸ S.store.visit_spec h.assign t.negate w
      (WExec.processList t L _ (h.move hs)).weaken (S₀ := S) (by exact le_rfl)
    | .unit l id =>
      have hs : VisitSpec S.store S.M t.negate w (.unit l id) :=
        hv ▸ S.store.visit_spec h.assign t.negate w
      have hu := h.unit hs
      (WExec.processList t L _ hu.1).weaken hu.2.le
    | .conflict id =>
      have hs : VisitSpec S.store S.M t.negate w (.conflict id) :=
        hv ▸ S.store.visit_spec h.assign t.negate w
      match hc : S.exec.log.clause? id with
      | some c =>
        have hcc := h.conflict_clause hs
        have hr := h.restore_inv
        .conflict (S.restore t (w :: L)) hr.1 (id, c)
          (by obtain ⟨c', hc', hlog, -⟩ := hcc; rw [hlog] at hc; cases hc; exact hc')
          (by obtain ⟨c', -, hlog, hf⟩ := hcc; rw [hlog] at hc; cases hc; exact hf) hr.2.le
      | none => absurd hc (by obtain ⟨c', -, hlog, -⟩ := h.conflict_clause hs; simp [hlog])
    | .drop =>
      have hs : VisitSpec S.store S.M t.negate w .drop :=
        hv ▸ S.store.visit_spec h.assign t.negate w
      (WExec.processList t L S (h.drop hs)).weaken le_rfl

/-! ### Moves at the top level -/

/-- The literals below a decision of a trail are on the trail. -/
theorem lits_below {N M₀ : Trail} {d : Literal ℕ} {x : Literal ℕ}
    (hx : x ∈ Trail.lits M₀) : x ∈ Trail.lits (N ++ ⟨d, true⟩ :: M₀) := by
  rw [lits_append]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)

/-- The learned clause without repetitions, its asserting literal first. -/
@[expose] def learnedWatched (C : Clause ℕ) (l : Literal ℕ) : Clause ℕ := l :: C.dedup.erase l

theorem learnedWatched_perm {C : Clause ℕ} {l : Literal ℕ} (hl : l ∈ C) :
    (learnedWatched C l).Perm C.dedup :=
  (List.perm_cons_erase (List.mem_dedup.2 hl)).symm

/-- The activities after a conflict meeting the variables `vs`: bumped, if VSIDS is on. -/
@[expose] def WExec.bumped (S : WExec φ) (vs : List ℕ) : Activity :=
  if S.opts.vsids then S.act.bump vs else S.act

/-- The variable order after a conflict meeting the variables `vs` and backjumping below the newest
decision of `sp`, with VSIDS: the variables met and those undone are inserted with their
activities `A`. -/
@[expose] def WExec.reordered (S : WExec φ) (A : Activity) (vs : List ℕ) (sp : Split) : VarOrder :=
  if S.opts.vsids then
    S.order.insertVars A (vs ++ Trail.vars (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]))
  else S.order

/-- The phases after backjumping below the newest decision of `sp`: those of the literals undone
are saved, if phase saving is on. -/
@[expose] def WExec.saved (S : WExec φ) (sp : Split) : Phases :=
  if S.opts.phaseSaving then S.phase.save (XTrail.trail sp.above ++ [⟨sp.decision, true⟩])
  else S.phase

/-- The assignment after backjumping below the newest decision of `sp` and asserting `l`: the
variables undone are unassigned, then `l` is assigned. -/
@[expose] def WExec.backjumped (S : WExec φ) (sp : Split) (l : Literal ℕ) : Assign :=
  (S.assign.unassign (Trail.vars (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]))).assign l

/-- One more conflict. -/
@[expose] def Stats.conflict (s : Stats) : Stats := { s with conflicts := s.conflicts + 1 }

/-- The reduction after a conflict learning `L`, stored if `stored`: updated, if reduction is on. -/
@[expose] def WExec.reduced (S : WExec φ) {sp : Split} (L : S.exec.LearnedAt sp) (stored : Bool) :
    Reduction :=
  if S.opts.reduce then S.red.learn L.used L.id L.log.next stored else S.red

/-- One more conflict, learning a clause of `k` different literals, `k₀` before minimization. -/
@[expose] def Stats.learn (s : Stats) (k₀ k : ℕ) : Stats :=
  { s with
    conflicts := s.conflicts + 1, maxLiterals := s.maxLiterals + k₀, literals := s.literals + k }

/-- The marks after an analysis: the array the analysis returns, with the variables of the
current level cleared, which leaves no value. -/
@[expose] def clearedMarks {log : LRATLog φ} (sp : Split)
    (L : Learned log (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) (XTrail.trail sp.below)) :
    {A : Assign // ∀ v, A.value v = none} :=
  ⟨L.marks.unassign (Trail.vars (XTrail.trail sp.above ++ [⟨sp.decision, true⟩])),
    Assign.value_unassign_eq_none L.marks_none⟩

/-- **Backjump and Learn with watches**: the state after the conflict, with the learned clause in
the store, watching its asserting literal, or among the short clauses, and the asserting literal
queued. The variables met by the analysis are bumped and, with those undone, put back in the
variable order, and the phases of the literals undone are saved; the statistics count `k₀`
literals before minimization. -/
@[expose] def WExec.afterConflict (S : WExec φ) (sp : Split) (L : S.exec.LearnedAt sp) (k₀ : ℕ) :
    WExec φ :=
  if 2 ≤ L.clause.dedup.length then
    ⟨S.exec.afterConflict sp L, S.backjumped sp L.lit,
      S.store.addClause L.id (learnedWatched L.clause L.lit), [L.lit],
      S.short, S.bumped L.seen, S.reordered (S.bumped L.seen) L.seen.dedup sp, S.saved sp,
      S.reduced L true, S.opts, S.stats.learn k₀ L.clause.dedup.length, clearedMarks sp L⟩
  else ⟨S.exec.afterConflict sp L, S.backjumped sp L.lit, S.store, [L.lit],
    (L.id, L.clause) :: S.short,
    S.bumped L.seen, S.reordered (S.bumped L.seen) L.seen.dedup sp, S.saved sp,
    S.reduced L false, S.opts, S.stats.learn k₀ L.clause.dedup.length, clearedMarks sp L⟩

theorem WExec.afterConflict_spec {S : WExec φ} (hS : S.Inv) {e : ℕ × Clause ℕ}
    (he : e ∈ S.exec.db) (hconf : Trail.Falsifies S.M e.2) {sp : Split}
    (hsp : XTrail.split S.exec.trail = some sp) (L : S.exec.LearnedAt sp) (k₀ : ℕ) :
    (S.afterConflict sp L k₀).Inv ∧ (S.afterConflict sp L k₀).measure < S.measure := by
  have hspec := Exec.afterConflict_spec hS.exec he hconf hsp L
  have hsplit := XTrail.trail_of_split hsp
  have hM' : XTrail.trail (S.exec.afterConflict sp L).trail =
      ⟨L.lit, false⟩ :: XTrail.trail sp.below := rfl
  have hdb' : (S.exec.afterConflict sp L).db = (L.id, L.clause) :: S.exec.db := rfl
  have hnodup' := hspec.1.run.nodup
  rw [hM'] at hnodup'
  have hlitM' : L.lit ∈ Trail.lits (⟨L.lit, false⟩ :: XTrail.trail sp.below) :=
    List.mem_cons_self
  -- the processed literals after backjumping are below the decision, hence processed before
  have hbelow : ∀ x, Processed (⟨L.lit, false⟩ :: XTrail.trail sp.below) [L.lit] x →
      x ∈ Trail.lits (XTrail.trail sp.below) :=
    fun x ⟨hx, hxq⟩ => (List.mem_cons.1 hx).resolve_left (by simpa using hxq)
  have hproc : ∀ x, Processed (⟨L.lit, false⟩ :: XTrail.trail sp.below) [L.lit] x →
      Processed S.M S.queue x := by
    intro x hx
    have hx' := hbelow x hx
    refine ⟨by rw [WExec.M, hsplit]; exact lits_below hx', fun hq => ?_⟩
    exact hS.queue_above x hq _ _ _ hsplit hx'
  have hstore := hS.store.weaken hproc fun b w₁ w₂ h₁ h₂ hs =>
    hs.backjump hsplit (hbelow _ h₁) (hbelow _ h₂) _
  have hlitneg : ¬ Processed (⟨L.lit, false⟩ :: XTrail.trail sp.below) [L.lit] L.lit.negate :=
    fun h => Trail.negate_not_mem hnodup' hlitM' h.1
  have hqueue : ∀ x ∈ [L.lit], ∀ N d M₀,
      (⟨L.lit, false⟩ :: XTrail.trail sp.below : Trail) = N ++ ⟨d, true⟩ :: M₀ →
      x ∉ Trail.lits M₀ := by
    intro x hx N d M₀ hN hxM₀
    rw [List.mem_singleton] at hx
    subst hx
    cases N with
    | nil => simp at hN
    | cons y N =>
      simp only [List.cons_append, List.cons.injEq] at hN
      apply L.undef
      rw [congrArg Trail.vars hN.2]
      exact Trail.mem_vars_of_mem_lits (lits_below hxM₀)
  -- the variables met and undone are put back in the order; the others keep their entries, and
  -- bumping did not raise their activities
  have horder : S.opts.vsids = true → ∀ T : WExec φ,
      T.order = S.reordered (S.bumped L.seen) L.seen.dedup sp → T.act = S.bumped L.seen →
      T.exec = S.exec.afterConflict sp L → T.OrderInv := by
    intro hv T hTo hTa hTe
    have hS' := hS.order hv
    simp only [WExec.reordered, WExec.bumped, hv, ↓reduceIte] at hTo hTa
    have hTM : T.M = ⟨L.lit, false⟩ :: XTrail.trail sp.below := by
      change XTrail.trail T.exec.trail = _; rw [hTe]; rfl
    refine ⟨hTo ▸ VarOrder.insertVars_wf hS'.wf, fun e he => ?_, fun v hv hvM => ?_⟩
    · rw [hTo] at he
      rcases VarOrder.mem_insertVars.1 he with he | ⟨v, hv, rfl⟩
      · exact hS'.vars e he
      · rcases List.mem_append.1 hv with hv | hv
        · exact L.seen_mem v (List.mem_dedup.1 hv)
        · refine hS.exec.run.subset v ?_
          change v ∈ Trail.vars S.M
          rw [WExec.M, hsplit, show XTrail.trail sp.above ++ ⟨sp.decision, true⟩ ::
            XTrail.trail sp.below = (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) ++
              XTrail.trail sp.below by simp, vars_append]
          exact List.mem_append_left _ hv
    · rw [hTo, hTa]
      by_cases hvs : v ∈ L.seen.dedup ++
          Trail.vars (XTrail.trail sp.above ++ [⟨sp.decision, true⟩])
      · exact ⟨_, le_rfl, VarOrder.mem_insertVars.2 (.inr ⟨v, hvs, rfl⟩)⟩
      · simp only [List.mem_append, not_or] at hvs
        have hvM' : v ∉ Trail.vars S.M := by
          rw [WExec.M, hsplit, show XTrail.trail sp.above ++ ⟨sp.decision, true⟩ ::
            XTrail.trail sp.below = (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) ++
              XTrail.trail sp.below by simp, vars_append, List.mem_append, not_or]
          refine ⟨hvs.2, fun h => hvM ?_⟩
          rw [hTM]
          exact List.mem_cons_of_mem _ h
        obtain ⟨k, hk, hmem⟩ := hS'.covers v hv hvM'
        exact ⟨k, (Activity.get_bump_le fun h => hvs.1 (List.mem_dedup.2 h)).trans hk,
          VarOrder.mem_insertVars.2 (.inl hmem)⟩
  -- the assignment undoes the literals above the decision, then asserts the learned literal
  have hassign : (S.backjumped sp L.lit).Agrees (⟨L.lit, false⟩ :: XTrail.trail sp.below) := by
    have hA := hS.assign
    have hnd := hS.exec.run.nodup
    rw [WExec.M, hsplit, show XTrail.trail sp.above ++ ⟨sp.decision, true⟩ ::
      XTrail.trail sp.below = (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) ++
        XTrail.trail sp.below by simp] at hA
    change (Trail.vars (XTrail.trail S.exec.trail)).Nodup at hnd
    rw [hsplit, show XTrail.trail sp.above ++ ⟨sp.decision, true⟩ ::
      XTrail.trail sp.below = (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) ++
        XTrail.trail sp.below by simp] at hnd
    rw [vars_append] at hnd
    exact (hA.drop fun v hv => List.disjoint_of_nodup_append hnd hv).cons
      (List.nodup_cons.1 hnodup').1 false
  have hmeasure : rank φ.vars (S.exec.afterConflict sp L).state * (nvars φ + 2) + 1 <
      S.measure := by
    have := hspec.2
    simp only [WExec.measure]
    nlinarith
  unfold WExec.afterConflict
  split
  · rename_i hlen
    have hperm := learnedWatched_perm (C := L.clause) L.mem
    have hlen' : 2 ≤ (learnedWatched L.clause L.lit).length := hperm.length_eq ▸ hlen
    obtain ⟨y, rest, hc⟩ : ∃ y rest, learnedWatched L.clause L.lit = L.lit :: y :: rest := by
      match h : learnedWatched L.clause L.lit, hlen' with
      | a :: y :: rest, _ =>
        exact ⟨y, rest, by simp only [learnedWatched, List.cons.injEq] at h; rw [← h.1]⟩
    have hnd : (L.lit :: y :: rest).Nodup := hc ▸ hperm.nodup_iff.2 (List.nodup_dedup _)
    have hmem : ∀ l, l ∈ L.lit :: y :: rest ↔ l ∈ L.clause := fun l => by
      rw [← hc, hperm.mem_iff, List.mem_dedup]
    refine ⟨⟨hspec.1, ?_, fun e' he' => ?_, fun e' he' hl => ?_, List.nodup_singleton _,
      fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hlitM', hqueue,
      fun hv => horder hv _ rfl rfl rfl, hassign⟩, ?_⟩
    · have := hstore.addClause (id := L.id) (C := L.clause) hnd hmem hlitneg
      rw [← hc] at this
      exact this
    · exact hdb' ▸ List.mem_cons_of_mem _ (hS.short_mem e' he')
    · rw [hdb'] at he'
      rcases List.mem_cons.1 he' with rfl | he'
      · simp only at hl; omega
      · exact hS.short_covers e' he' hl
    · simpa [WExec.measure] using hmeasure
  · rename_i hlen
    refine ⟨⟨hspec.1, ?_, fun e' he' => ?_, fun e' he' hl => ?_, List.nodup_singleton _,
      fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hlitM', hqueue,
      fun hv => horder hv _ rfl rfl rfl, hassign⟩, ?_⟩
    · exact hstore.consShort (L.id, L.clause) (by simp only; omega)
    · rw [hdb']
      rcases List.mem_cons.1 he' with rfl | he'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS.short_mem e' he')
    · rw [hdb'] at he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS.short_covers e' he' hl)
    · simpa [WExec.measure] using hmeasure

/-- Adding a literal over an unassigned variable to the trail and the empty queue. -/
theorem WExec.Inv.push {S S' : WExec φ} (hS : S.Inv) (hq : S.queue = []) {l : Literal ℕ}
    {b : Bool} (hexec : S'.exec.Inv) (hM : S'.M = ⟨l, b⟩ :: S.M) (hq' : S'.queue = [l])
    (hdb : S'.exec.db = S.exec.db) (hstore : S'.store = S.store) (hshort : S'.short = S.short)
    (hundef : l.1 ∉ Trail.vars S.M) (horder : S'.opts.vsids = true → S'.OrderInv)
    (hassign : S'.assign = S.assign.assign l) : S'.Inv := by
  have hl : l ∉ Trail.lits S.M := fun h => hundef (Trail.mem_vars_of_mem_lits h)
  have hproc : ∀ x, Processed S'.M S'.queue x → Processed S.M S.queue x := by
    intro x ⟨hx, hxq⟩
    rw [hM] at hx
    rw [hq'] at hxq
    exact ⟨(List.mem_cons.1 hx).resolve_left (by simpa using hxq), by simp [hq]⟩
  refine ⟨hexec, ?_, ?_, ?_, ?_, ?_, ?_, horder, hassign ▸ hM ▸ hS.assign.cons hundef b⟩
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
  { S with
    exec := S.exec.propagate e l, assign := S.assign.assign l, queue := [l] }

/-- The polarity of a decision on `x`: its saved phase, or `false` without phase saving. -/
@[expose] def WExec.polarity (S : WExec φ) (x : ℕ) : Bool := S.opts.phaseSaving && S.phase.get x

/-- **The decision variable**, and the variable order after choosing it. With VSIDS, it is popped
from the variable order (`Cslib.Algorithms.Lean.CDCL.VarOrder.pop`); should the order run out, the
unassigned variables of the database are scanned for one of greatest activity. Without VSIDS, it is
the first unassigned variable of the database. -/
@[expose] def WExec.pickVar (S : WExec φ) : Option ℕ × VarOrder :=
  if S.opts.vsids then
    match VarOrder.pop S.act S.assign (S.order.size + 1) S.order with
    | (some x, H) => (some x, H)
    | (none, H) => (S.act.pick S.assign S.exec.clauses.vars, H)
  else ((Activity.init 0).pick S.assign S.exec.clauses.vars, S.order)

/-- **Decide** the variable `x`, at an empty queue, with the variable order `H`. -/
@[expose] def WExec.decide (S : WExec φ) (x : ℕ) (H : VarOrder) : WExec φ :=
  { S with
    exec := S.exec.decide x (S.polarity x), assign := S.assign.assign (x, S.polarity x)
    queue := [(x, S.polarity x)], order := H
    stats := S.stats.decision }

/-- The variables of `φ` are variables of the database. -/
theorem Exec.Inv.mem_clauses_vars {S : Exec φ} (hS : S.Inv) {x : ℕ} (hx : x ∈ φ.vars) :
    x ∈ S.clauses.vars := by
  obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hx
  obtain ⟨e, he, rfl⟩ := exists_mem_lratDB hc
  exact CNF.mem_vars.2 ⟨e.2, List.mem_map.2 ⟨e, hS.orig e he, rfl⟩, b, hb⟩

/-- The variables of the database are variables of `φ`. -/
theorem Exec.Inv.mem_vars_of_clauses {S : Exec φ} (hS : S.Inv) {x : ℕ}
    (hx : x ∈ S.clauses.vars) : x ∈ φ.vars := by
  obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.1 hx
  exact hS.run.db_vars c hc (x, b) hb

/-- **The decision variable** is an unassigned variable of the database. -/
theorem WExec.Inv.pickVar_some {S : WExec φ} (hS : S.Inv) {x : ℕ} {H : VarOrder}
    (h : S.pickVar = (some x, H)) : x ∈ S.exec.clauses.vars ∧ x ∉ Trail.vars S.M := by
  unfold WExec.pickVar at h
  split at h
  · rename_i hv
    obtain ⟨-, -, hpop, -⟩ := VarOrder.pop_spec hS.assign (S.order.size + 1) S.order
      (hS.order hv).wf (hS.order hv).vars (hS.order hv).covers
    generalize VarOrder.pop S.act S.assign (S.order.size + 1) S.order = r at h hpop
    obtain ⟨_ | y, H'⟩ := r
    · exact Activity.pick_some hS.assign (congrArg Prod.fst h)
    · simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨hyV, hyM, -⟩ := hpop y rfl
      exact ⟨hS.exec.mem_clauses_vars hyV, hyM⟩
  · exact Activity.pick_some hS.assign (congrArg Prod.fst h)

/-- Without a decision variable, every variable of the database is assigned. -/
theorem WExec.Inv.pickVar_none {S : WExec φ} (hS : S.Inv) {H : VarOrder}
    (h : S.pickVar = (none, H)) :
    ∀ x ∈ S.exec.clauses.vars, x ∈ Trail.vars S.M := by
  unfold WExec.pickVar at h
  split at h
  · generalize VarOrder.pop S.act S.assign (S.order.size + 1) S.order = r at h
    obtain ⟨_ | y, H'⟩ := r
    · exact Activity.pick_none hS.assign (congrArg Prod.fst h)
    · simp at h
  · exact Activity.pick_none hS.assign (congrArg Prod.fst h)

/-- **With VSIDS, the decision variable has the greatest activity** among the unassigned variables
of the database. -/
theorem WExec.Inv.pickVar_max {S : WExec φ} (hS : S.Inv) (hv : S.opts.vsids = true) {x : ℕ}
    {H : VarOrder} (h : S.pickVar = (some x, H)) :
    ∀ y ∈ S.exec.clauses.vars, y ∉ Trail.vars S.M → S.act.get y ≤ S.act.get x := by
  unfold WExec.pickVar at h
  simp only [hv, ↓reduceIte] at h
  obtain ⟨-, -, hpop, -⟩ := VarOrder.pop_spec hS.assign (S.order.size + 1) S.order
    (hS.order hv).wf (hS.order hv).vars (hS.order hv).covers
  generalize VarOrder.pop S.act S.assign (S.order.size + 1) S.order = r at h hpop
  obtain ⟨_ | y, H'⟩ := r
  · exact fun z hz hzM => Activity.pick_max hS.assign (congrArg Prod.fst h) hz hzM
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact fun z hz hzM => (hpop _ rfl).2.2 z (hS.exec.mem_vars_of_clauses hz) hzM

/-- After deciding the decision variable, the variable order keeps its invariant. -/
theorem WExec.Inv.pickVar_order {S : WExec φ} (hS : S.Inv) {x : ℕ} {H : VarOrder}
    (h : S.pickVar = (some x, H)) (hv : (S.decide x H).opts.vsids = true) :
    (S.decide x H).OrderInv := by
  change S.opts.vsids = true at hv
  have hS' := hS.order hv
  obtain ⟨hwf, hV, -, hcov⟩ := VarOrder.pop_spec hS.assign (S.order.size + 1) S.order hS'.wf
    hS'.vars hS'.covers
  have hM : ∀ v, v ∉ Trail.vars (S.decide x H).M → v ∉ Trail.vars S.M ∧ v ≠ x := fun v hv' =>
    ⟨fun h' => hv' (List.mem_cons_of_mem _ h'), fun h' => hv' (h' ▸ List.mem_cons_self)⟩
  change VarOrder.Inv H S.act φ.vars (S.decide x H).M
  unfold WExec.pickVar at h
  simp only [hv, ↓reduceIte] at h
  generalize VarOrder.pop S.act S.assign (S.order.size + 1) S.order = r at h hwf hV hcov
  obtain ⟨_ | y, H'⟩ := r
  · simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hwf, hV, fun v hv' hvM => hcov v hv' (hM v hvM).1 (by simp)⟩
  · simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hwf, hV, fun v hv' hvM => hcov v hv' (hM v hvM).1 (by simpa using (hM v hvM).2.symm)⟩

/-- With the queue empty, no clause of the database is false if no short clause is. -/
theorem WExec.Inv.noConflict {S : WExec φ} (hS : S.Inv) (hq : S.queue = [])
    (hshort : ∀ e ∈ S.short, ¬ Trail.Falsifies S.M e.2) :
    ∀ c ∈ S.exec.clauses, ¬ Trail.Falsifies S.M c := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  by_cases hlen : 2 ≤ e.2.dedup.length
  · exact (hq ▸ hS.store).not_falsifies hS.exec.run.nodup he hlen
  · exact hshort e (hS.short_covers e he (by omega))

/-- **Restart**, at an empty queue: back to the root of the trail, with VSIDS putting the variables
of the trail back in the variable order. With phase saving on, the phases of the trail's literals
are saved first, as MiniSat's `cancelUntil(0)` saves those it undoes; the root's literals stay
assigned, so only the saved phases of the undone ones are read later. -/
@[expose] def WExec.restart (S : WExec φ) : WExec φ :=
  let e := S.exec.restart
  { S with
    exec := e
    assign := Assign.ofTrail (XTrail.trail e.trail)
    order := if S.opts.vsids then S.order.insertVars S.act (Trail.vars S.M) else S.order
    phase := if S.opts.phaseSaving then S.phase.save S.M else S.phase
    stats := { S.stats with restarts := S.stats.restarts + 1 } }

/-- Restart keeps the invariant: the processed literals kept were processed, and the clauses with
both watched literals false keep their support, which is below the oldest decision. -/
theorem WExec.Inv.restart {S : WExec φ} (hS : S.Inv) (hq : S.queue = []) : S.restart.Inv := by
  obtain ⟨A, hA⟩ := XTrail.root_suffix S.exec.trail
  have hM : S.M = XTrail.trail A ++ S.restart.M := by
    change XTrail.trail S.exec.trail = _ ++ XTrail.trail (XTrail.root S.exec.trail)
    conv_lhs => rw [hA]
    exact XTrail.trail_append _ _
  have hproc : ∀ x, Processed S.restart.M S.restart.queue x → Processed S.M S.queue x :=
    fun x ⟨hx, _⟩ => ⟨by rw [hM, lits_append]; exact List.mem_append_right _ hx, by simp [hq]⟩
  refine ⟨Exec.restart_inv hS.exec, hS.store.weaken hproc fun b w₁ w₂ h₁ h₂ hs => ?_,
    hS.short_mem, hS.short_covers, by simp [WExec.restart, hq], by simp [WExec.restart, hq],
    by simp [WExec.restart, hq], fun hv => ?_,
    Assign.agrees_ofTrail _ (Exec.restart_inv hS.exec).run.nodup⟩
  swap
  · change S.opts.vsids = true at hv
    have hS' := hS.order hv
    have ho : S.restart.order = S.order.insertVars S.act (Trail.vars S.M) := by
      simp [WExec.restart, hv]
    refine ⟨ho ▸ VarOrder.insertVars_wf hS'.wf, fun e he => ?_, fun v hv' hvM => ?_⟩
    · rw [ho] at he
      rcases VarOrder.mem_insertVars.1 he with he | ⟨v, hv'', rfl⟩
      · exact hS'.vars e he
      · exact hS.exec.run.subset v hv''
    · rw [ho]
      by_cases hvS : v ∈ Trail.vars S.M
      · exact ⟨_, le_rfl, VarOrder.mem_insertVars.2 (.inr ⟨v, hvS, rfl⟩)⟩
      · obtain ⟨k, hk, hmem⟩ := hS'.covers v hv' hvS
        exact ⟨k, hk, VarOrder.mem_insertVars.2 (.inl hmem)⟩
  rcases XTrail.root_split S.exec.trail with h | ⟨N, d, hN⟩
  · have : S.restart.M = S.M := by
      change XTrail.trail (XTrail.root S.exec.trail) = _; rw [h]
    exact this ▸ hs
  · exact hs.truncate hN h₁.1 h₂.1

/-- Merging two lists sorted by `le`, in at most `fuel` steps. A loop of `sortBy`, which supplies
enough fuel. -/
@[expose] def sortBy.merge {α : Type} (le : α → α → Bool) :
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
@[expose] def sortBy.go {α : Type} (le : α → α → Bool) : (fuel : ℕ) → List α → List α
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | n + 1, xs =>
    let p := splitAlternate xs
    sortBy.merge le xs.length (sortBy.go le n p.1) (sortBy.go le n p.2)

/-- **Merge sort by `le`**, to the depth of the length of the list, which is enough. Unlike
`List.mergeSort`, it is structurally recursive, so the kernel can run it. -/
@[expose] def sortBy {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  sortBy.go le xs.length xs

/-- **The learned clauses to forget**, as MiniSat's `reduceDB` chooses them: the learned clauses
of the store, those of more than two literals first by increasing activity; of the less active
half, those of more than two literals, and of the other half, those of more than two literals and
activity below the increment divided by their number. Kept in any case are the clauses of `φ`, the
reasons of the trail (MiniSat's *locked* clauses) and the short clauses. -/
@[expose] def WExec.reduceIds (S : WExec φ) : List ℕ :=
  let act := S.red.act
  let learnts := S.store.clauses.toList.filter fun e => φ.length < e.1
  let sorted := sortBy (fun a b =>
    if (a.2.length ≤ 2) == (b.2.length ≤ 2) then act.get a.1 ≤ act.get b.1 else b.2.length ≤ 2)
    learnts
  let half := sorted.length / 2
  -- MiniSat's `activity < cla_inc / learnts.size()`, without rounding the quotient
  let chosen := (sorted.take half).filter (2 < ·.2.length) ++
    (sorted.drop half).filter fun e => 2 < e.2.length && act.get e.1 * sorted.length < act.inc
  let locked := XTrail.reasonIds S.exec.trail
  (chosen.map Prod.fst).filter fun i =>
    φ.length < i && !locked.contains i && !S.short.any (·.1 == i)

/-- Forgetting the learned clauses numbered `ids` and rebuilding the watch store on the current
trail. -/
@[expose] def WExec.forgetChosen (S : WExec φ) (ids : List ℕ) : WExec φ :=
  { S with
    exec := S.exec.forget ids
    store := WatchStore.build S.assign (S.exec.forget ids).db
    red := { S.red with learnts := S.red.learnts - ids.length }
    stats := { S.stats with removed := S.stats.removed + ids.length } }

/-- **Reducing the learned clauses**, at an empty queue: the clauses chosen are forgotten, and the
watch store is rebuilt on the current trail. If none is chosen, nothing changes: the store is not
rebuilt and the certificate gets no deletion step. -/
@[expose] def WExec.reduce (S : WExec φ) : WExec φ :=
  let ids := S.reduceIds
  if ids.isEmpty then S else S.forgetChosen ids

theorem WExec.mem_reduceIds {S : WExec φ} {i : ℕ} (h : i ∈ S.reduceIds) :
    φ.length < i ∧ i ∉ XTrail.reasonIds S.exec.trail ∧ ∀ e ∈ S.short, e.1 ≠ i := by
  simp only [WExec.reduceIds, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, List.contains_eq_mem, decide_eq_false_iff_not, List.any_eq_false,
    beq_iff_eq] at h
  exact ⟨h.2.1.1, h.2.1.2, fun e he => h.2.2 e he⟩

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
  · have hexec : (S.exec.forget S.reduceIds).Inv :=
      Exec.forget_inv hS.exec (fun e he hi => by
        have := (WExec.mem_reduceIds hi).1
        have := le_length_of_mem_lratDB he
        omega) fun r hr hi => (WExec.mem_reduceIds hi).2.1 hr
    have hdb : ∀ e ∈ (S.exec.forget S.reduceIds).db, e ∈ S.exec.db := fun e he =>
      (List.mem_filter.1 he).1
    have hsub : ∀ c ∈ (S.forgetChosen S.reduceIds).exec.clauses, c ∈ S.exec.clauses :=
      fun c hc => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      exact List.mem_map.2 ⟨e, hdb e he, rfl⟩
    refine ⟨⟨hexec, ?_, fun e he => ?_, fun e he hlen => hS.short_covers e (hdb e he) hlen,
      hS.queue_nodup, hS.queue_trail, hS.queue_above, hS.order, hS.assign⟩,
      fun c hc => hnoconf c (hsub c hc), rfl⟩
    · change (WatchStore.build S.assign (S.exec.forget S.reduceIds).db).Inv _ S.M S.queue
      rw [hq]
      exact WatchStore.build_inv hS.assign _ fun e he _ =>
        hnoconf e.2 (List.mem_map.2 ⟨e, hdb e he, rfl⟩)
    · refine List.mem_filter.2 ⟨hS.short_mem e he, ?_⟩
      have : ¬ e.1 ∈ S.reduceIds := fun hi => (WExec.mem_reduceIds hi).2.2 e he rfl
      simpa using this

/-- **MiniSat's `reduceDB`, when due**: if reduction is on and the learned clauses in the store
exceed the assigned variables by the limit, reduce. -/
@[expose] def WExec.maybeReduce (S : WExec φ) : WExec φ :=
  if S.opts.reduce && S.red.max ≤ 1000 * S.red.learnts &&
      S.red.max + 1000 * S.exec.trail.length ≤ 1000 * S.red.learnts then S.reduce
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

/-- The answer of the solver, with its correctness: a model, or an LRAT certificate accepted by
the checker. -/
inductive Answer (φ : CNF ℕ) : Type
  /-- A model. -/
  | sat (σ : ℕ → Bool) (h : φ.eval σ = true)
  /-- An accepted certificate. -/
  | unsat (cert : Array Std.Tactic.BVDecide.LRAT.IntAction) (h : φ.checkLRAT cert = true)

/-- The outcome of a run of the loop: the answer with the statistics, or a restarted state, which
only a run allowed to restart returns. -/
inductive Outcome (φ : CNF ℕ) (allowed : Bool) : Type
  /-- The answer, with the statistics. -/
  | done (r : Answer φ × Stats)
  /-- A restarted state. -/
  | restart (S : WExec φ) (h : S.Inv) (ha : allowed = true)

/-- **The CDCL loop with watched literals**, restarting once the number of conflicts reaches
`limit`, if any. While the queue is not empty, the watch list of the negation of its first literal
is visited; a conflict is analysed, followed by Backjump and Learn, or ends with a certificate when
there is no decision. With the queue empty, the short clauses are checked for a conflict or a
unit; then the loop restarts if the limit is reached, decides an unassigned variable of the
database, or returns the trail as a model. -/
@[expose] def loop (φ : CNF ℕ) (limit : Option ℕ) :
    (fuel : ℕ) → (S : WExec φ) → S.Inv → S.measure < fuel → Outcome φ limit.isSome
  | 0, _, _, hfuel => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, S, hS, hfuel =>
    -- a conflict on a database clause
    let onConflict (S : WExec φ) (hS : S.Inv) (e : ℕ × Clause ℕ) (he : e ∈ S.exec.db)
        (hconf : Trail.Falsifies S.M e.2) (hm : S.measure ≤ fuel) : Outcome φ limit.isSome :=
      match hsp : XTrail.split S.exec.trail with
      | none =>
        let r := refute S.exec.trail S.exec.log e.1 e.2 (hS.exec.db_log e he) hS.exec.reasons
          (XTrail.split_eq_none hsp) hconf
        .done (.unsat r.cert (LRATLog.checkLRAT_finish r.clause?_eq), S.stats.conflict)
      | some sp =>
        let L₀ := analyze S.exec.log sp.decision sp.below
          (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]) sp.above (fun _ h => h)
          (S.marks.1.assignTrail (XTrail.trail sp.above ++ [⟨sp.decision, true⟩]))
          (Assign.agrees_assignTrail S.marks.2 _ (hS.exec.split_level_nodup hsp)) S.exec.log
          (LRATLog.Extends.refl _) e.1 e.2 (hS.exec.db_log e he) (hS.exec.split_reasons hsp)
          (XTrail.split_eq_some hsp).2 (XTrail.falsifies_of_split hsp hconf)
          (hS.exec.split_cur hsp he hconf) (hS.exec.split_nodup hsp)
        let L := if S.opts.minimize then L₀.minimize sp.below else L₀
        let k₀ := L₀.clause.dedup.length
        have hspec := WExec.afterConflict_spec hS he hconf hsp L k₀
        loop φ limit fuel (S.afterConflict sp L k₀) hspec.1 (by omega)
    match hq : S.queue with
    | t :: _ =>
      have ht : t ∈ S.queue := hq ▸ List.mem_cons_self
      match (S.start t).processList t (watchList S.store.watches (watchIndex t.negate))
          (WExec.start_procInv hS ht) with
      | .done S' h hm =>
        have hfin := WExec.finish_inv h
        loop φ limit fuel (S'.finish t) hfin.1 (by
          have : (S.start t).measure = S.measure := rfl
          omega)
      | .conflict S' h e he hconf hm =>
        onConflict S' h e he hconf (by have : (S.start t).measure = S.measure := rfl; omega)
    | [] =>
      match hc : S.short.find? (fun e => S.assign.falsifies e.2) with
      | some e =>
        onConflict S hS e (hS.short_mem e (List.mem_of_find?_eq_some hc))
          ((hS.assign.falsifies_iff e.2).1
            (List.find?_some (p := fun e : ℕ × Clause ℕ => S.assign.falsifies e.2) hc))
          (by omega)
      | none =>
        have hshort : ∀ e ∈ S.short, ¬ Trail.Falsifies S.M e.2 := fun e he hf =>
          List.find?_eq_none.1 hc e he ((hS.assign.falsifies_iff _).2 hf)
        have hnoconf := hS.noConflict hq hshort
        match hu : findUnit S.assign S.short with
        | some (e, l) =>
          have ⟨he, hl, hundef, hfalse⟩ := findUnit_spec hS.assign hu
          have hspec := Exec.propagate_spec hS.exec (hS.short_mem e he) hl hundef hfalse
          loop φ limit fuel (S.propagateShort e l)
            (hS.push hq hspec.1 rfl rfl rfl rfl rfl hundef (fun hv =>
              (hS.order hv).extend rfl rfl fun v hv => List.mem_cons_of_mem _ hv) rfl)
            (by have := WExec.measure_push_lt (S' := S.propagateShort e l) hq rfl hspec.2; omega)
        | none =>
          have ⟨hS₁, hq₁, hnoconf₁, hm₁⟩ := hS.maybeReduce hq hnoconf
          let S₁ := S.maybeReduce
          match hr : limit.any (· ≤ S₁.stats.conflicts) with
          | true => .restart S₁.restart (hS₁.restart hq₁) (by cases limit <;> simp_all)
          | false =>
          match hx : S₁.pickVar with
          | (some x, H) =>
            have ⟨hxV, hundef⟩ := hS₁.pickVar_some hx
            have hspec := Exec.decide_spec hS₁.exec hnoconf₁ hxV hundef (S₁.polarity x)
            loop φ limit fuel (S₁.decide x H)
              (hS₁.push hq₁ hspec.1 rfl rfl rfl rfl rfl hundef (hS₁.pickVar_order hx) rfl)
              (by have := WExec.measure_push_lt (S' := S₁.decide x H) hq₁ rfl hspec.2; omega)
          | (none, _) =>
            .done (.sat (Trail.assignment S₁.M)
              (hS₁.exec.run.eval_model hnoconf₁ (hS₁.pickVar_none hx)), S₁.stats)

/-- **Search with restarts**: runs of the loop, each restarting after its budget of conflicts, at
most `k` of them; the last run does not restart. -/
@[expose] def search (φ : CNF ℕ) : (k : ℕ) → (S : WExec φ) → S.Inv → Answer φ × Stats
  | 0, S, hS =>
    match loop φ none (S.measure + 1) S hS (Nat.lt_succ_self _) with
    | .done r => r
    | .restart _ _ ha => absurd ha (by decide)
  | k + 1, S, hS =>
    let limit := if S.opts.restarts then
      some (S.stats.conflicts + S.opts.restartBudget S.stats.restarts) else none
    match loop φ limit (S.measure + 1) S hS (Nat.lt_succ_self _) with
    | .done r => r
    | .restart S' h _ => search φ k S' h

/-- The number of restarts allowed: never reached in practice, it makes termination
structural. -/
@[expose] def restartAllowance : ℕ := 2 ^ 64

/-- **The CDCL solver with options**: a model, or an LRAT certificate of unsatisfiability, with the
statistics of the run. -/
@[expose] def solveWith (o : Options) (φ : CNF ℕ) : DPLL.Result × Stats :=
  match search φ restartAllowance (WExec.init φ o) (WExec.init_inv φ o) with
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
    (solveWith o φ).1.isSat = true ↔ φ.Satisfiable := by
  constructor
  · intro h
    cases hs : (solveWith o φ).1 with
    | sat σ => exact ⟨σ, solveWith_sat hs⟩
    | unsat cert => simp [hs, DPLL.Result.isSat] at h
  · intro h
    cases hs : (solveWith o φ).1 with
    | sat σ => rfl
    | unsat cert =>
      exact absurd h (CNF.not_satisfiable_of_checkLRAT (solveWith_unsat hs))

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
    (solveCompactWith o φ).1.isSat = true ↔ φ.Satisfiable := by
  constructor
  · intro h
    cases hs : (solveCompactWith o φ).1 with
    | sat σ => exact ⟨σ, solveCompactWith_sat hs⟩
    | unsat cert => simp [hs, DPLL.Result.isSat] at h
  · intro h
    cases hs : (solveCompactWith o φ).1 with
    | sat σ => rfl
    | unsat cert =>
      exact absurd h (CNF.not_satisfiable_of_checkLRAT (solveCompactWith_unsat hs))

theorem solveCompact_sat {φ : CNF ℕ} {σ : ℕ → Bool} (h : solveCompact φ = .sat σ) :
    φ.eval σ = true :=
  solveCompactWith_sat h

theorem solveCompact_unsat {φ : CNF ℕ} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction}
    (h : solveCompact φ = .unsat cert) : φ.checkLRAT cert = true :=
  solveCompactWith_unsat h

theorem isSat_solveCompact_iff (φ : CNF ℕ) : (solveCompact φ).isSat = true ↔ φ.Satisfiable :=
  isSat_solveCompactWith_iff {} φ

end Cslib.Algorithms.Lean.CDCL

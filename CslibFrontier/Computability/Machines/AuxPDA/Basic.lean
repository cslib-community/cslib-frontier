/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic

/-!
# Auxiliary pushdown automata

An *auxiliary pushdown automaton* (`Turing.AuxPDA`) extends a multi-tape nondeterministic Turing
machine (read-only input tape with clamped endmarkers, `k` two-way read/write work tapes, and a
write-only output tape) with an unbounded pushdown stack whose height is **not** charged to work
space.

Each transition inspects the control state, the symbol under the input head, the `k` symbols under
the work-tape heads, and the top symbol of the stack (`Option StackSym`, where `none` indicates an
empty stack), and performs a multi-tape Turing action (`Turing.Action`) together with a stack
operation (`AuxPDA.StackOp`: `stay`, `push γ`, or `pop`). Attempting `pop` on an empty stack fails
(stack underflow, `StackOp.apply? .pop [] = none`) and cannot fire as a step.

Work space (`AuxPDA.RunPath.space`) counts distinct cells visited on the `k` work tapes only,
matching `Turing.MultiTapeNTM.RunPath.space`; the pushdown stack is uncharged. Time bounds
(`AuxPDA.RunsInTime`) apply to **all** computation paths, preventing vacuous looping branches.

This is original machine infrastructure for cslib-frontier #7920 (Work Package 3), mirroring the
upstream multi-tape machine conventions of [Papadimitriou94] and [Sipser2013].

## Main definitions

* `Turing.AuxPDA.StackOp`: pushdown stack operations (`stay`, `push`, `pop`) and partial
  application `StackOp.apply?`.
* `Turing.AuxPDA.Action`, `Turing.AuxPDA.Cfg`: single-step actions and full configurations
  extending `Turing.Action` and `Turing.Cfg` with the pushdown stack.
* `Turing.AuxPDA`: nondeterministic auxiliary pushdown automaton.
* `Turing.AuxPDA.Step`, `Turing.AuxPDA.RunPath`, `Turing.AuxPDA.ComputationPath`: single-step
  relation and finite runs.
* `Turing.AuxPDA.RunsInTime`, `Turing.AuxPDA.RunsInSpace`, `Turing.AuxPDA.Accepts`,
  `Turing.AuxPDA.DecidesInTimeAndSpace`: all-branches time/space bounds and acceptance.
* `Turing.AuxPDA.ofMultiTapeNTM`: embedding of a `MultiTapeNTM` with an unused stack.

## Main results

* `Turing.AuxPDA.RunPath.stackHeight_le`, `Turing.AuxPDA.ComputationPath.stackHeight_le`: stack
  height grows by at most one per step.
* `Turing.AuxPDA.ComputationPath.storage_fitsIn`: work-tape heads and non-blank cells lie within
  per-tape visited-cell windows.
* `Turing.AuxPDA.DecidesInTimeAndSpace.mono`: monotone resource closure.
* `Turing.AuxPDA.ofMultiTapeNTM_runsInSpace_iff`, `Turing.AuxPDA.ofMultiTapeNTM_runsInTime_iff`,
  `Turing.AuxPDA.ofMultiTapeNTM_accepts_iff`: exact simulation of multi-tape NTMs.

## References

* [C. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing

/-! ### Stack operations, actions and configurations -/

namespace AuxPDA

/-- The elementary operations on the pushdown stack of an auxiliary pushdown automaton. -/
inductive StackOp (StackSym : Type*) where
  /-- Leave the stack unchanged. -/
  | stay
  /-- Push a symbol onto the top of the stack. -/
  | push (sym : StackSym)
  /-- Pop the top symbol of the stack; invalid (underflow) on an empty stack. -/
  | pop
  deriving DecidableEq, Repr

namespace StackOp

variable {StackSym : Type*}

/-- Apply a stack operation to a stack represented top-first. Popping an empty stack returns
`none` (stack underflow). -/
def apply? : StackOp StackSym → List StackSym → Option (List StackSym)
  | .stay, stack => some stack
  | .push sym, stack => some (sym :: stack)
  | .pop, [] => none
  | .pop, _ :: rest => some rest

@[simp]
lemma apply?_stay (stack : List StackSym) :
    (StackOp.stay : StackOp StackSym).apply? stack = some stack := rfl

@[simp]
lemma apply?_push (sym : StackSym) (stack : List StackSym) :
    (StackOp.push sym).apply? stack = some (sym :: stack) := rfl

@[simp]
lemma apply?_pop_nil : (StackOp.pop : StackOp StackSym).apply? [] = none := rfl

@[simp]
lemma apply?_pop_cons (sym : StackSym) (rest : List StackSym) :
    (StackOp.pop : StackOp StackSym).apply? (sym :: rest) = some rest := rfl

/-- A stack operation changes the stack height by at most one (increasing). -/
lemma length_le_of_apply? {op : StackOp StackSym} {s s' : List StackSym}
    (h : op.apply? s = some s') : s'.length ≤ s.length + 1 := by
  cases op <;> cases s <;> cases h <;> simp only [List.length_cons, List.length_nil] <;> omega

/-- A stack operation decreases the stack height by at most one. -/
lemma le_length_add_one_of_apply? {op : StackOp StackSym} {s s' : List StackSym}
    (h : op.apply? s = some s') : s.length ≤ s'.length + 1 := by
  cases op <;> cases s <;> cases h <;> simp only [List.length_cons, List.length_nil] <;> omega

end StackOp

/-- One step of an auxiliary pushdown automaton: a multi-tape Turing action paired with a
pushdown stack operation. -/
structure Action (k : ℕ) (Symbol StackSym State : Type*) where
  /-- The input-head move, work-tape edits/moves, optional output, and successor state. -/
  tape : Turing.Action k Symbol State
  /-- The operation applied to the pushdown stack. -/
  stackOp : StackOp StackSym

/-- A configuration of an auxiliary pushdown automaton relative to `input`: an underlying
multi-tape Turing configuration together with the pushdown stack (top symbol first). -/
@[ext]
structure Cfg (k : ℕ) (Symbol StackSym State : Type*) (input : List Symbol) where
  /-- The underlying multi-tape Turing configuration (state, input head, work tapes, output). -/
  tapes : Turing.Cfg k Symbol State input
  /-- The pushdown stack, with the top symbol at the head of the list. -/
  stack : List StackSym
  deriving Inhabited

namespace Cfg

variable {k : ℕ} {Symbol StackSym State : Type*} {input : List Symbol}

/-- The symbol at the top of the stack, or `none` when the stack is empty. -/
abbrev topSym (c : Cfg k Symbol StackSym State input) : Option StackSym :=
  c.stack.head?

/-- A configuration is halted when its underlying Turing configuration has halted. -/
abbrev Halted (c : Cfg k Symbol StackSym State input) : Prop :=
  c.tapes.Halted

/-- The control state and work-tape storage of a configuration (forgetting input head, output,
and stack). -/
abbrev storage (c : Cfg k Symbol StackSym State input) : Storage Symbol State k :=
  c.tapes.storage

/-- The initial configuration for starting state `q₀` and `input`: standard multi-tape initial
configuration with an empty pushdown stack. -/
@[simp]
def init (q₀ : State) (input : List Symbol) : Cfg k Symbol StackSym State input :=
  ⟨Turing.Cfg.init q₀ input, []⟩

end Cfg

/-- Apply an `AuxPDA.Action` to a configuration. Returns `none` on stack underflow (`pop` on an
empty stack). -/
def Action.apply? {k : ℕ} {Symbol StackSym State : Type*} {input : List Symbol}
    (act : Action k Symbol StackSym State) (cfg : Cfg k Symbol StackSym State input) :
    Option (Cfg k Symbol StackSym State input) :=
  (act.stackOp.apply? cfg.stack).map fun stack' => ⟨act.tape.apply cfg.tapes, stack'⟩

lemma Action.apply?_eq_some_iff {k : ℕ} {Symbol StackSym State : Type*} {input : List Symbol}
    {act : Action k Symbol StackSym State} {cfg cfg' : Cfg k Symbol StackSym State input} :
    act.apply? cfg = some cfg' ↔
      ∃ stack', act.stackOp.apply? cfg.stack = some stack' ∧
        cfg' = ⟨act.tape.apply cfg.tapes, stack'⟩ := by
  rw [Action.apply?, Option.map_eq_some_iff]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

end AuxPDA

/-! ### Nondeterministic auxiliary pushdown automata -/

/-- A nondeterministic auxiliary pushdown automaton with `k` read/write work tapes over
`Option Symbol` (`none` = blank), a read-only input tape, a write-only output tape, and an
unbounded pushdown stack over `StackSym`. -/
structure AuxPDA (k : ℕ) (Symbol StackSym State : Type*) where
  /-- The initial control state. -/
  q₀ : State
  /-- The nondeterministic transition relation on control state, input symbol, work-tape head
  symbols, top stack symbol (`none` when empty), and resulting action. -/
  Tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol)
    (top : Option StackSym) (action : AuxPDA.Action k Symbol StackSym State) : Prop

namespace AuxPDA

variable {k : ℕ} {Symbol StackSym State : Type*} {input : List Symbol}
variable {M : AuxPDA k Symbol StackSym State}

/-- The initial configuration of `M` on `input`. -/
@[simp]
def initCfg (M : AuxPDA k Symbol StackSym State) (input : List Symbol) :
    Cfg k Symbol StackSym State input :=
  Cfg.init M.q₀ input

/-- The one-step relation on configurations. A halted configuration steps only to itself; a
running configuration steps by applying any action related by `Tr` that does not underflow the
stack. -/
def Step (M : AuxPDA k Symbol StackSym State)
    (c₁ c₂ : Cfg k Symbol StackSym State input) : Prop :=
  match c₁.tapes.state with
  | none => c₂ = c₁
  | some q =>
    ∃ action, M.Tr q c₁.tapes.inputSymbol c₁.tapes.workTapeSymbols c₁.topSym action ∧
      action.apply? c₁ = some c₂

/-- A halted configuration steps only to itself. -/
lemma step_of_halt {c c' : Cfg k Symbol StackSym State input} (h : c.Halted) :
    M.Step c c' ↔ c' = c := by
  simp [Step, h]

/-- A single step changes each work-tape head by at most one cell. -/
lemma Step.workTapePos_le {c c' : Cfg k Symbol StackSym State input} (h : M.Step c c')
    (i : Fin k) : |c'.tapes.workTapePos i - c.tapes.workTapePos i| ≤ 1 := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨act, -, hact⟩ := h
    obtain ⟨_, -, rfl⟩ := Action.apply?_eq_some_iff.mp hact
    exact workTapePos_apply_le act.tape c.tapes i

/-- A single step does not modify any work-tape cell away from its head. -/
lemma Step.workTapes_eq_of_ne {c c' : Cfg k Symbol StackSym State input} (h : M.Step c c')
    {i : Fin k} {z : ℤ} (hz : z ≠ c.tapes.workTapePos i) :
    c'.tapes.workTapes i z = c.tapes.workTapes i z := by
  unfold Step at h
  split at h
  · simp [h]
  · obtain ⟨act, -, hact⟩ := h
    obtain ⟨_, -, rfl⟩ := Action.apply?_eq_some_iff.mp hact
    rw [Turing.Action.apply_workTapes]
    cases hw : (act.tape.workTapes i).1 <;> simp [hw, hz]

/-- A single step increases the stack height by at most one. -/
lemma Step.stackHeight_le {c c' : Cfg k Symbol StackSym State input} (h : M.Step c c') :
    c'.stack.length ≤ c.stack.length + 1 := by
  unfold Step at h
  split at h
  · exact h ▸ Nat.le_succ _
  · obtain ⟨_, -, hact⟩ := h
    obtain ⟨_, hstack, rfl⟩ := Action.apply?_eq_some_iff.mp hact
    exact StackOp.length_le_of_apply? hstack

/-- A single step decreases the stack height by at most one. -/
lemma Step.le_stackHeight_add_one {c c' : Cfg k Symbol StackSym State input} (h : M.Step c c') :
    c.stack.length ≤ c'.stack.length + 1 := by
  unfold Step at h
  split at h
  · exact h ▸ Nat.le_succ _
  · obtain ⟨_, -, hact⟩ := h
    obtain ⟨_, hstack, rfl⟩ := Action.apply?_eq_some_iff.mp hact
    exact StackOp.le_length_add_one_of_apply? hstack

/-- The one-step relation as a `SetRel`. -/
abbrev stepRel (M : AuxPDA k Symbol StackSym State) (input : List Symbol) :
    SetRel (Cfg k Symbol StackSym State input) (Cfg k Symbol StackSym State input) :=
  {(c, c') | M.Step c c'}

/-- Steps from running (non-halted) configurations. -/
abbrev runningStepRel (M : AuxPDA k Symbol StackSym State) (input : List Symbol) :
    SetRel (Cfg k Symbol StackSym State input) (Cfg k Symbol StackSym State input) :=
  {(c, c') | ¬c.Halted ∧ M.Step c c'}

/-- A finite sequence of configurations joined by steps of `M`. -/
abbrev RunPath (M : AuxPDA k Symbol StackSym State) (input : List Symbol) :=
  RelSeries (M.stepRel input)

namespace RunPath

/-- The number of steps taken by a run path. -/
def time (p : M.RunPath input) : ℕ := p.length

/-- Once a run path is halted, its configuration stays unchanged. -/
lemma last_eq_of_head_halted (p : M.RunPath input) (h : p.head.Halted) : p.last = p.head := by
  induction p using RelSeries.inductionOn' with
  | singleton c => rfl
  | snoc p c hc ih =>
    have hp : p.last = p.head := ih (by simpa using h)
    have hh : p.last.Halted := hp ▸ (show p.head.Halted by simpa using h)
    simpa using ((step_of_halt hh).mp hc).trans hp

/-- The last configuration equals any earlier halted configuration. -/
lemma last_eq_of_halted (p : M.RunPath input) (i : Fin (p.length + 1)) (h : (p i).Halted) :
    p.last = p i := by
  simpa using last_eq_of_head_halted (p.drop i) (by simpa using h)

/-- A run path that ends halted decomposes into a running prefix ending at its first halted
configuration. -/
lemma exists_running (p : M.RunPath input) (h : p.last.Halted) :
    ∃ q : RelSeries (M.runningStepRel input), q.head = p.head ∧ q.last = p.last ∧
      q.length ≤ p.length ∧ ∀ c ∈ q, c ∈ p := by
  classical
  have hex : ∃ n, ∃ hn : n < p.length + 1, (p ⟨n, hn⟩).Halted := ⟨p.length, by omega, h⟩
  obtain ⟨hn, hhalt⟩ := Nat.find_spec hex
  refine ⟨⟨Nat.find hex, fun i => p ⟨i, by omega⟩, fun i =>
    ⟨fun hi => Nat.find_min hex i.isLt ⟨_, hi⟩, p.step ⟨i, by omega⟩⟩⟩, rfl,
    (p.last_eq_of_halted _ hhalt).symm, Nat.lt_succ_iff.mp hn, fun _ ⟨i, hi⟩ => ⟨_, hi⟩⟩

/-- **Height-vs-time bound**: stack height grows by at most one per step along a run path. -/
theorem stackHeight_le (p : M.RunPath input) :
    p.last.stack.length ≤ p.head.stack.length + p.time := by
  induction p using RelSeries.inductionOn' with
  | singleton c => simp [time]
  | snoc p c hc ih =>
    have hstep := Step.stackHeight_le hc
    simp only [time, RelSeries.last_snoc, RelSeries.head_snoc, RelSeries.snoc_length] at ih ⊢
    omega

/-- The positions visited by work-tape head `i` along a run path. The pushdown stack is not
counted in space. -/
def visitedByTapeHead (p : M.RunPath input) (i : Fin k) : Finset ℤ :=
  Finset.univ.image fun n => (p n).tapes.workTapePos i

/-- The number of distinct cells visited by work-tape head `i` along a run path. -/
def spaceUsedByTape (p : M.RunPath input) (i : Fin k) : ℕ :=
  (p.visitedByTapeHead i).card

/-- Total work-tape space used by a run path (summed across the `k` work tapes; stack uncharged). -/
def space (p : M.RunPath input) : ℕ := ∑ i, p.spaceUsedByTape i

@[simp]
lemma mem_visitedByTapeHead (p : M.RunPath input) {i : Fin k} {z : ℤ} :
    z ∈ p.visitedByTapeHead i ↔ ∃ c ∈ p, c.tapes.workTapePos i = z := by
  simp [visitedByTapeHead, RelSeries.mem_def]

lemma visitedByTapeHead_take_subset (p : M.RunPath input) (j : Fin (p.length + 1)) (i : Fin k) :
    visitedByTapeHead (p.take j) i ⊆ p.visitedByTapeHead i :=
  Finset.image_subset_iff.mpr fun n _ =>
    p.mem_visitedByTapeHead.mpr ⟨_, ⟨Fin.castLE j.isLt n, rfl⟩, rfl⟩

lemma visitedByTapeHead_snoc (p : M.RunPath input) (c : Cfg k Symbol StackSym State input)
    (h : M.Step p.last c) (i : Fin k) :
    visitedByTapeHead (p.snoc c h) i =
      insert (c.tapes.workTapePos i) (p.visitedByTapeHead i) := by
  ext z
  simp [RelSeries.mem_snoc, or_and_right, exists_or, eq_comm, or_comm]

/-- Every cell between the first and last head positions of a work tape is visited. -/
lemma uIcc_workTapePos_subset_visitedByTapeHead (p : M.RunPath input) (i : Fin k) :
    Finset.uIcc (p.head.tapes.workTapePos i) (p.last.tapes.workTapePos i) ⊆
      p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp +instances [visitedByTapeHead, RelSeries.singleton, RelSeries.head, RelSeries.last]
  | snoc p c h ih =>
    have hm := abs_le.mp (Step.workTapePos_le h i)
    rw [RelSeries.head_snoc, RelSeries.last_snoc, visitedByTapeHead_snoc]
    intro z hz
    by_cases he : z = c.tapes.workTapePos i
    · exact he ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (ih (by rw [Finset.mem_uIcc] at hz ⊢; omega))

/-- Any work-tape cell that changed along a path was visited by its head. -/
lemma mem_visitedByTapeHead_of_workTapes_ne (p : M.RunPath input) {i : Fin k} {z : ℤ}
    (h : p.last.tapes.workTapes i z ≠ p.head.tapes.workTapes i z) :
    z ∈ p.visitedByTapeHead i := by
  induction p using RelSeries.inductionOn' with
  | singleton c => exact absurd rfl h
  | snoc p c hs ih =>
    rw [visitedByTapeHead_snoc]
    refine Finset.mem_insert_of_mem ?_
    by_cases hz : z = p.last.tapes.workTapePos i
    · exact hz ▸ Finset.mem_image_of_mem _ (Finset.mem_univ (Fin.last _))
    · rw [RelSeries.last_snoc, RelSeries.head_snoc, Step.workTapes_eq_of_ne hs hz] at h
      exact ih h

/-- Every visited head position lies within `spaceUsedByTape` of its starting position. -/
lemma natAbs_le_spaceUsedByTape_of_mem_visited (p : M.RunPath input) {i : Fin k} {z : ℤ}
    (hz : z ∈ p.visitedByTapeHead i) :
    (z - p.head.tapes.workTapePos i).natAbs ≤ p.spaceUsedByTape i := by
  obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hz
  have h := Finset.card_le_card
    ((uIcc_workTapePos_subset_visitedByTapeHead (p.take n) i).trans
      (p.visitedByTapeHead_take_subset n i))
  rw [RelSeries.head_take, RelSeries.last_take, Int.card_uIcc] at h
  change _ ≤ (p.visitedByTapeHead i).card
  omega

end RunPath

/-- A run path starting at the initial configuration of `M` on `input`. -/
structure ComputationPath (M : AuxPDA k Symbol StackSym State) (input : List Symbol)
    extends toRunPath : M.RunPath input where
  /-- The path starts at the initial configuration. -/
  head_eq : toRunPath.head = M.initCfg input

namespace ComputationPath

/-- The number of steps taken by a computation path. -/
def time (p : M.ComputationPath input) : ℕ := RunPath.time p.toRunPath

/-- Cells visited on work tape `i` along a computation path. -/
def spaceUsedByTape (p : M.ComputationPath input) (i : Fin k) : ℕ :=
  RunPath.spaceUsedByTape p.toRunPath i

/-- Total work-tape space used along a computation path (stack uncharged). -/
def space (p : M.ComputationPath input) : ℕ := RunPath.space p.toRunPath

/-- The stack height at the end of a computation path is at most its step count. -/
theorem stackHeight_le (p : M.ComputationPath input) : p.last.stack.length ≤ p.time := by
  simpa [time, p.head_eq] using RunPath.stackHeight_le p.toRunPath

/-- The work-tape storage at the end of a computation path fits in its per-tape visited-cell
windows, matching `Turing.MultiTapeNTM.ComputationPath.storage_fitsIn`. -/
theorem storage_fitsIn (p : M.ComputationPath input) :
    p.last.storage.FitsIn p.spaceUsedByTape := by
  refine ⟨fun j => ?_, fun j z hz => ?_⟩
  · simpa [Cfg.storage, Turing.Cfg.storage, p.head_eq, Cfg.init, Turing.Cfg.init,
      spaceUsedByTape] using
      RunPath.natAbs_le_spaceUsedByTape_of_mem_visited p.toRunPath
        ((RunPath.mem_visitedByTapeHead _).mpr ⟨_, RelSeries.last_mem _, rfl⟩)
  · simpa [Cfg.storage, Turing.Cfg.storage, p.head_eq, Cfg.init, Turing.Cfg.init,
      spaceUsedByTape] using
      RunPath.natAbs_le_spaceUsedByTape_of_mem_visited p.toRunPath
        (RunPath.mem_visitedByTapeHead_of_workTapes_ne _
          (by simpa [Cfg.storage, Turing.Cfg.storage, p.head_eq, Cfg.init, Turing.Cfg.init] using
            hz))

end ComputationPath

/-! ### Time bounds, space bounds and decision -/

/-- Every computation path on `input` of at least `t` steps ends halted. -/
def RunsInTime (M : AuxPDA k Symbol StackSym State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ p : M.ComputationPath input, t ≤ p.time → p.last.Halted

/-- A time bound can be increased. -/
lemma RunsInTime.mono {t t' : ℕ} (h : M.RunsInTime input t) (ht : t ≤ t') :
    M.RunsInTime input t' :=
  fun p hp => h p (ht.trans hp)

/-- Every computation prefix on `input` visits at most `s` work-tape cells (stack uncharged). -/
def RunsInSpace (M : AuxPDA k Symbol StackSym State) (input : List Symbol) (s : ℕ) : Prop :=
  ∀ p : M.ComputationPath input, p.space ≤ s

/-- A space bound can be increased. -/
lemma RunsInSpace.mono {s s' : ℕ} (h : M.RunsInSpace input s) (hs : s ≤ s') :
    M.RunsInSpace input s' :=
  fun p => (h p).trans hs

/-- A machine without work tapes satisfies every space bound regardless of stack usage. -/
@[simp]
lemma runsInSpace_zero_tapes (M : AuxPDA 0 Symbol StackSym State) (input : List Symbol) (s : ℕ) :
    M.RunsInSpace input s := by
  intro p
  simp [ComputationPath.space, RunPath.space]

/-- A binary `AuxPDA` accepts `input` when some computation path ends halted with output
`[true]`, matching `Turing.MultiTapeNTM.Accepts`. -/
def Accepts (M : AuxPDA k Bool StackSym State) (input : List Bool) : Prop :=
  ∃ p : M.ComputationPath input, p.last.Halted ∧ p.last.tapes.output = [true]

/-- `M` decides `A` within work space `s` and all-branches time `t` relative to `enc`: on every
encoded instance `enc a`, every computation prefix uses at most `s a` work-tape cells, every
computation path of length at least `t a` halts, and `a ∈ A ↔ M.Accepts (enc a)`. -/
def DecidesInTimeAndSpace {α : Type*} (M : AuxPDA k Bool StackSym State) (enc : α ↪ List Bool)
    (A : Set α) (s t : α → ℕ) : Prop :=
  ∀ a, M.RunsInSpace (enc a) (s a) ∧ M.RunsInTime (enc a) (t a) ∧ (a ∈ A ↔ M.Accepts (enc a))

/-- Monotone resource closure for `DecidesInTimeAndSpace`. -/
theorem DecidesInTimeAndSpace.mono {α : Type*} {M : AuxPDA k Bool StackSym State}
    {enc : α ↪ List Bool} {A : Set α} {s s' t t' : α → ℕ}
    (h : M.DecidesInTimeAndSpace enc A s t)
    (hs : ∀ a, s a ≤ s' a) (ht : ∀ a, t a ≤ t' a) :
    M.DecidesInTimeAndSpace enc A s' t' :=
  fun a => ⟨(h a).1.mono (hs a), (h a).2.1.mono (ht a), (h a).2.2⟩

/-! ### Embedding multi-tape nondeterministic Turing machines -/

/-- Embed any `MultiTapeNTM` as an `AuxPDA` with a dummy stack alphabet `PUnit` that never pushes
or pops (`StackOp.stay` on every transition). -/
def ofMultiTapeNTM (ntm : MultiTapeNTM k Symbol State) : AuxPDA k Symbol PUnit State where
  q₀ := ntm.q₀
  Tr q inp work _ act := act.stackOp = .stay ∧ ntm.Tr q inp work act.tape

lemma ofMultiTapeNTM_step_iff {ntm : MultiTapeNTM k Symbol State}
    {c₁ c₂ : Cfg k Symbol PUnit State input} :
    (ofMultiTapeNTM ntm).Step c₁ c₂ ↔ ntm.Step c₁.tapes c₂.tapes ∧ c₂.stack = c₁.stack := by
  cases hs : c₁.tapes.state with
  | none =>
    simp only [Step, MultiTapeNTM.Step, hs]
    exact ⟨fun h => ⟨h ▸ rfl, h ▸ rfl⟩, fun ⟨ht, hst⟩ => Cfg.ext ht hst⟩
  | some q =>
    simp only [Step, MultiTapeNTM.Step, ofMultiTapeNTM, hs, Action.apply?_eq_some_iff]
    refine ⟨?_, fun ⟨⟨tAct, htr, htapes⟩, hstack⟩ =>
      ⟨⟨tAct, .stay⟩, ⟨rfl, htr⟩, c₁.stack, rfl, Cfg.ext htapes hstack⟩⟩
    rintro ⟨act, ⟨hstay, htr⟩, stack', hstack, rfl⟩
    rw [hstay, StackOp.apply?_stay, Option.some.injEq] at hstack
    exact ⟨⟨act.tape, htr, rfl⟩, hstack.symm⟩

/-- Projecting an `ofMultiTapeNTM` configuration to its `Turing.Cfg` preserves steps. -/
private def ofMultiTapeNTMTapesHom (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    ((ofMultiTapeNTM ntm).stepRel input).Hom (ntm.stepRel input) :=
  ⟨fun c => c.tapes, fun h => (ofMultiTapeNTM_step_iff.mp h).1⟩

/-- Lifting a `Turing.Cfg` with an empty stack preserves steps into `ofMultiTapeNTM`. -/
private def ofMultiTapeNTMLiftHom (ntm : MultiTapeNTM k Symbol State) (input : List Symbol) :
    (ntm.stepRel input).Hom ((ofMultiTapeNTM ntm).stepRel input) :=
  ⟨fun c => ⟨c, []⟩, fun h => ofMultiTapeNTM_step_iff.mpr ⟨h, rfl⟩⟩

private lemma ofMultiTapeNTM_space_map_tapes (ntm : MultiTapeNTM k Symbol State)
    (p : (ofMultiTapeNTM ntm).RunPath input) :
    MultiTapeNTM.RunPath.space (RelSeries.map p (ofMultiTapeNTMTapesHom ntm input)) = p.space :=
  Finset.sum_congr rfl fun _ _ => congrArg Finset.card (Finset.image_congr fun _ _ => rfl)

private lemma ofMultiTapeNTM_space_map_lift (ntm : MultiTapeNTM k Symbol State)
    (p : ntm.RunPath input) :
    RunPath.space (RelSeries.map p (ofMultiTapeNTMLiftHom ntm input)) = p.space :=
  Finset.sum_congr rfl fun _ _ => congrArg Finset.card (Finset.image_congr fun _ _ => rfl)

private lemma head_map_lift {ntm : MultiTapeNTM k Symbol State}
    (p : ntm.ComputationPath input) :
    (RelSeries.map p.toRunPath (ofMultiTapeNTMLiftHom ntm input)).head =
      (ofMultiTapeNTM ntm).initCfg input :=
  congrArg (Cfg.mk · []) p.head_eq

private lemma head_map_tapes {ntm : MultiTapeNTM k Symbol State}
    (p : (ofMultiTapeNTM ntm).ComputationPath input) :
    (RelSeries.map p.toRunPath (ofMultiTapeNTMTapesHom ntm input)).head =
      ntm.initCfg input :=
  congrArg Cfg.tapes p.head_eq

/-- `ofMultiTapeNTM` preserves work-tape space bounds exactly. -/
theorem ofMultiTapeNTM_runsInSpace_iff {ntm : MultiTapeNTM k Symbol State} {s : ℕ} :
    (ofMultiTapeNTM ntm).RunsInSpace input s ↔ ntm.RunsInSpace input s :=
  ⟨fun h p => (ofMultiTapeNTM_space_map_lift ntm p.toRunPath).symm.trans_le
    (h ⟨RelSeries.map p.toRunPath (ofMultiTapeNTMLiftHom ntm input), head_map_lift p⟩),
   fun h p => (ofMultiTapeNTM_space_map_tapes ntm p.toRunPath).symm.trans_le
    (h ⟨RelSeries.map p.toRunPath (ofMultiTapeNTMTapesHom ntm input), head_map_tapes p⟩)⟩

/-- `ofMultiTapeNTM` preserves all-branches time bounds exactly. -/
theorem ofMultiTapeNTM_runsInTime_iff {ntm : MultiTapeNTM k Symbol State} {t : ℕ} :
    (ofMultiTapeNTM ntm).RunsInTime input t ↔ ntm.RunsInTime input t :=
  ⟨fun h p hp =>
    h ⟨RelSeries.map p.toRunPath (ofMultiTapeNTMLiftHom ntm input), head_map_lift p⟩
      (by simpa [ComputationPath.time, RunPath.time,
        MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time] using hp),
   fun h p hp =>
    h ⟨RelSeries.map p.toRunPath (ofMultiTapeNTMTapesHom ntm input), head_map_tapes p⟩
      (by simpa [ComputationPath.time, RunPath.time,
        MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time] using hp)⟩

/-- `ofMultiTapeNTM` preserves acceptance exactly. -/
theorem ofMultiTapeNTM_accepts_iff {ntm : MultiTapeNTM k Bool State} {input : List Bool} :
    (ofMultiTapeNTM ntm).Accepts input ↔ ntm.Accepts input :=
  ⟨fun ⟨p, hhalt, hout⟩ =>
    ⟨⟨RelSeries.map p.toRunPath (ofMultiTapeNTMTapesHom ntm input), head_map_tapes p⟩,
      hhalt, hout⟩,
   fun ⟨p, hhalt, hout⟩ =>
    ⟨⟨RelSeries.map p.toRunPath (ofMultiTapeNTMLiftHom ntm input), head_map_lift p⟩,
      hhalt, hout⟩⟩

end AuxPDA

end Turing

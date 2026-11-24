/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Oracle multi-tape Turing machines

Oracle machines over the binary alphabet, built on CSLib's multi-tape machines
(`Turing.Action`, `Turing.Cfg`). Besides its input tape, its `k` work tapes and its write-only
output tape, an oracle machine has a write-only *query tape*, here an append-only buffer
(`OCfg.query`), and *query instructions* `OAction.ask yes no`. An ordinary instruction
`OAction.step a s` performs the CSLib action `a` and appends the symbol `s`, if any, to the query
tape. A query instruction submits the query tape to the oracle `A : Set (List Bool)`, erases it,
and continues in the state `yes` or `no` according to whether the query is in `A`. This is the
convention of Ladner and Lynch (a write-only query tape, erased by each query) and of the
textbook definition of the answer (the states `q_yes` and `q_no`, [Arora and Barak,
Definition 3.6]); as in Remark 8.3 of the paper, **the query tape counts toward space**
(`OracleNTM.pathSpace`): a path uses the work cells its heads visit, as in CSLib, plus the longest
query it holds.

Nondeterministic machines (`OracleNTM`) relate each state and read symbols to a set of
instructions; deterministic machines (`OracleTM`) have a transition function. Runs, computation
paths, time and space bounds and acceptance mirror CSLib's `Turing.MultiTapeNTM` definitions
word for word, with `OracleNTM.Step A` in place of `MultiTapeNTM.Step`.

## Main definitions

* `Cslib.Complexity.NtimeDspace.Oracle.OAction`, `Cslib.Complexity.NtimeDspace.Oracle.OCfg`:
instructions and configurations.
* `Cslib.Complexity.NtimeDspace.Oracle.OracleNTM`, `Cslib.Complexity.NtimeDspace.Oracle.OracleTM`:
the machines.
* `Cslib.Complexity.NtimeDspace.Oracle.OracleNTM.Step`: one step relative to an oracle.
* `Cslib.Complexity.NtimeDspace.Oracle.OracleNTM.RunsInTime`, `.RunsInSpace`, `.Accepts`: resources
and acceptance.
* `Cslib.Complexity.NtimeDspace.Oracle.OracleTM.step`, `.DecidesIn`: the deterministic step and
deciders.

## References

* [R. E. Ladner, N. A. Lynch, *Relativization of questions about log space
  computability*, Math. Systems Theory 10 (1976)]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Definition 3.6]
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing

/-- An instruction of an oracle machine: an ordinary CSLib action together with an optional symbol
appended to the query tape, or a query. -/
inductive OAction (k : ℕ) (State : Type*) where
  /-- Perform `action` and append `query` (if any) to the query tape. -/
  | step (action : Turing.Action k Bool State) (query : Option Bool)
  /-- Submit the query tape; continue in `yes` or `no`. The query tape is erased. -/
  | ask (yes no : State)

/-- A configuration of an oracle machine: a CSLib configuration and the content of the query
tape. -/
@[ext] structure OCfg (k : ℕ) (State : Type*) (input : List Bool) where
  /-- The control state, the input head, the work tapes and the output. -/
  tapes : Cfg k Bool State input
  /-- The query tape. -/
  query : List Bool

variable {k : ℕ} {State : Type*} {input : List Bool}

open scoped Classical in
/-- The effect of an instruction relative to the oracle `A`. -/
noncomputable def OAction.apply (A : Set (List Bool)) :
    OAction k State → OCfg k State input → OCfg k State input
  | .step a s, c => ⟨a.apply c.tapes, c.query ++ s.toList⟩
  | .ask y n, c => ⟨c.tapes.withState (some (if c.query ∈ A then y else n)), []⟩

@[simp] lemma OAction.apply_step (A : Set (List Bool)) (a : Turing.Action k Bool State)
    (s : Option Bool) (c : OCfg k State input) :
    (OAction.step a s).apply A c = ⟨a.apply c.tapes, c.query ++ s.toList⟩ := rfl

open scoped Classical in
@[simp] lemma OAction.apply_ask (A : Set (List Bool)) (y n : State) (c : OCfg k State input) :
    (OAction.ask y n).apply A c =
      ⟨c.tapes.withState (some (if c.query ∈ A then y else n)), []⟩ := rfl

/-- A nondeterministic oracle machine with `k` binary work tapes. -/
structure OracleNTM (k : ℕ) (State : Type*) where
  /-- The initial state. -/
  q₀ : State
  /-- The permitted instructions in a state, given the symbols under the input and work heads. -/
  Tr : State → Option Bool → (Fin k → Option Bool) → OAction k State → Prop

namespace OracleNTM

variable (M : OracleNTM k State) (A : Set (List Bool))

/-- One step relative to the oracle `A`. A halted configuration steps only to itself. -/
def Step (c c' : OCfg k State input) : Prop :=
  match c.tapes.state with
  | none => c' = c
  | some q => ∃ a, M.Tr q c.tapes.inputSymbol c.tapes.workTapeSymbols a ∧ c' = a.apply A c

/-- The initial configuration: CSLib's initial configuration and an empty query tape. -/
def initCfg (input : List Bool) : OCfg k State input := ⟨Cfg.init M.q₀ input, []⟩

/-- The step relation on configurations for `input`. -/
abbrev stepRel (input : List Bool) : SetRel (OCfg k State input) (OCfg k State input) :=
  {(c, c') | M.Step A c c'}

/-- A nonempty sequence of configurations joined by steps. -/
abbrev RunPath (input : List Bool) := RelSeries (M.stepRel A input)

/-- A run path from the initial configuration. -/
structure ComputationPath (input : List Bool) extends toRunPath : M.RunPath A input where
  /-- The path starts at the initial configuration. -/
  head_eq : toRunPath.head = M.initCfg input

variable {M A}

/-- The space used along a path: the number of work cells visited by the heads (CSLib's
`MultiTapeNTM.RunPath.space`) plus the length of the longest query tape. -/
def pathSpace (p : M.RunPath A input) : ℕ :=
  (∑ i, (Finset.univ.image fun n => (p n).tapes.workTapePos i).card) +
    Finset.univ.sup fun n => (p n).query.length

variable (M A)

/-- Every computation path of at least `t` steps ends halted. -/
def RunsInTime (input : List Bool) (t : ℕ) : Prop :=
  ∀ p : M.ComputationPath A input, t ≤ p.length → p.last.tapes.Halted

/-- Every computation prefix uses at most `s` cells of the work tapes and the query tape. -/
def RunsInSpace (input : List Bool) (s : ℕ) : Prop :=
  ∀ p : M.ComputationPath A input, pathSpace p.toRunPath ≤ s

/-- Some computation path ends halted with output `[true]`. -/
def Accepts (input : List Bool) : Prop :=
  ∃ p : M.ComputationPath A input, p.last.tapes.Halted ∧ p.last.tapes.output = [true]

lemma RunsInTime.mono {M : OracleNTM k State} {A : Set (List Bool)} {input : List Bool}
    {t t' : ℕ} (h : M.RunsInTime A input t) (ht : t ≤ t') : M.RunsInTime A input t' :=
  fun p hp => h p (ht.trans hp)

lemma RunsInSpace.mono {M : OracleNTM k State} {A : Set (List Bool)} {input : List Bool}
    {s s' : ℕ} (h : M.RunsInSpace A input s) (hs : s ≤ s') : M.RunsInSpace A input s' :=
  fun p => (h p).trans hs

/-- The one-configuration path at the initial configuration. -/
def ComputationPath.init (input : List Bool) : M.ComputationPath A input :=
  ⟨RelSeries.singleton _ (M.initCfg input), rfl⟩

end OracleNTM

/-- A deterministic oracle machine with `k` binary work tapes. -/
structure OracleTM (k : ℕ) (State : Type*) where
  /-- The initial state. -/
  q₀ : State
  /-- The instruction in a state, given the symbols under the input and work heads. -/
  tr : State → Option Bool → (Fin k → Option Bool) → OAction k State

namespace OracleTM

variable (M : OracleTM k State) (A : Set (List Bool))

/-- A deterministic machine as a nondeterministic one with a single permitted instruction. -/
def toNTM : OracleNTM k State := ⟨M.q₀, fun q i w a => M.tr q i w = a⟩

/-- The deterministic step relative to the oracle `A`. -/
noncomputable def step (c : OCfg k State input) : OCfg k State input :=
  match c.tapes.state with
  | none => c
  | some q => (M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols).apply A c

lemma step_of_halted {c : OCfg k State input} (h : c.tapes.state = none) : M.step A c = c := by
  simp [step, h]

lemma step_of_state {c : OCfg k State input} {q : State} (h : c.tapes.state = some q) :
    M.step A c = (M.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols).apply A c := by
  simp [step, h]

/-- The step relation of `toNTM` is the graph of `step`. -/
lemma toNTM_step_iff {c c' : OCfg k State input} : M.toNTM.Step A c c' ↔ c' = M.step A c := by
  unfold OracleNTM.Step step
  cases c.tapes.state with
  | none => rfl
  | some q => simp [toNTM]

/-- The configuration after `t` steps from `c`. -/
noncomputable def runFrom (c : OCfg k State input) (t : ℕ) : OCfg k State input :=
  (M.step A)^[t] c

/-- The configuration after `t` steps on `input`. -/
noncomputable def run (input : List Bool) (t : ℕ) : OCfg k State input :=
  M.runFrom A (M.toNTM.initCfg input) t

lemma runFrom_succ (c : OCfg k State input) (t : ℕ) :
    M.runFrom A c (t + 1) = M.step A (M.runFrom A c t) :=
  Function.iterate_succ_apply' _ _ _

@[simp] lemma runFrom_zero (c : OCfg k State input) : M.runFrom A c 0 = c := rfl

lemma run_succ (input : List Bool) (t : ℕ) :
    M.run A input (t + 1) = M.step A (M.run A input t) :=
  Function.iterate_succ_apply' _ _ _

lemma runFrom_succ' (c : OCfg k State input) (t : ℕ) :
    M.runFrom A c (t + 1) = M.runFrom A (M.step A c) t :=
  Function.iterate_succ_apply _ _ _

lemma runFrom_add (c : OCfg k State input) (s t : ℕ) :
    M.runFrom A c (s + t) = M.runFrom A (M.runFrom A c s) t := by
  rw [runFrom, runFrom, runFrom, Nat.add_comm, Function.iterate_add_apply]

/-- A step appends at most one symbol to the query tape. -/
lemma length_query_step_le (c : OCfg k State input) :
    (M.step A c).query.length ≤ c.query.length + 1 := by
  unfold step
  split
  · omega
  · cases M.tr _ _ _ with
    | step a o => cases o <;> simp
    | ask y n => simp

lemma length_query_runFrom_le (c : OCfg k State input) (t : ℕ) :
    (M.runFrom A c t).query.length ≤ c.query.length + t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih => rw [runFrom_succ]; have := M.length_query_step_le A (M.runFrom A c t); omega

/-- Every path of a deterministic machine follows its step function. -/
lemma runPath_apply (p : M.toNTM.RunPath A input) (i : Fin (p.length + 1)) :
    p i = M.runFrom A p.head i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    have hs := p.step ⟨i, by omega⟩
    change M.toNTM.Step A _ _ at hs
    rw [toNTM_step_iff] at hs
    change p ⟨i + 1, hi⟩ = _
    rw [runFrom_succ, ← ih (by omega)]
    exact hs

/-- The path of the first `t` steps from `c`. -/
noncomputable def RunPath.ofRun (c : OCfg k State input) (t : ℕ) : M.toNTM.RunPath A input where
  length := t
  toFun n := M.runFrom A c n
  step n := by
    change M.toNTM.Step A _ _
    rw [toNTM_step_iff]
    exact M.runFrom_succ A c n

/-- The computation path of the first `t` steps on `input`. -/
noncomputable def ComputationPath.ofRun (input : List Bool) (t : ℕ) :
    M.toNTM.ComputationPath A input :=
  ⟨RunPath.ofRun M A (M.toNTM.initCfg input) t, rfl⟩

lemma last_ofRun (input : List Bool) (t : ℕ) :
    (ComputationPath.ofRun M A input t).last = M.run A input t := rfl

/-- A computation path ends at the iterate of its length. -/
lemma last_eq_run (p : M.toNTM.ComputationPath A input) : p.last = M.run A input p.length := by
  rw [RelSeries.last, runPath_apply, p.head_eq]
  rfl

lemma run_eq_of_halted {u v : ℕ} (h : (M.run A input u).tapes.Halted) (huv : u ≤ v) :
    M.run A input v = M.run A input u := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    rw [run, runFrom_succ, ← run, ih, step_of_halted _ _ h]

/-- A run halted after `u` steps satisfies every time bound from `u` on. -/
lemma runsInTime_of_halted {u t : ℕ} (h : (M.run A input u).tapes.Halted) (hut : u ≤ t) :
    M.toNTM.RunsInTime A input t := by
  intro p hp
  rw [last_eq_run, M.run_eq_of_halted A h (hut.trans hp)]
  exact h

/-- `M` decides `L` relative to `A` within time `T` and space `S`: on every input every computation
path of `T x` steps has halted, every computation prefix uses at most `S x` cells (work tapes and
query tape), and the run halts with output `[true]` on members of `L` and `[false]` on others. -/
def DecidesIn (L : Set (List Bool)) (T S : List Bool → ℕ) : Prop :=
  ∀ x, M.toNTM.RunsInTime A x (T x) ∧ M.toNTM.RunsInSpace A x (S x) ∧
    ∃ u, (M.run A x u).tapes.Halted ∧ (M.run A x u).tapes.output = [MultiTapeTM.indicator L x]

lemma DecidesIn.mono {M : OracleTM k State} {A L : Set (List Bool)} {T S T' S' : List Bool → ℕ}
    (h : M.DecidesIn A L T S) (hT : ∀ x, T x ≤ T' x) (hS : ∀ x, S x ≤ S' x) :
    M.DecidesIn A L T' S' :=
  fun x => ⟨(h x).1.mono (hT x), (h x).2.1.mono (hS x), (h x).2.2⟩

end OracleTM

end Cslib.Complexity.NtimeDspace.Oracle

/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Cslib.Foundations.Relation.RelatesInSteps
public import Cslib.Foundations.Semantics.FLTS.Basic
public import Mathlib.Computability.StateTransition

/-!
# Memory modules and the machines built from them

Many machine models consist of a controller attached to a few data structures, each of which
can be inspected and updated in a fixed way: a finite control register, a bidirectionally
infinite tape, a one-way input, a stack. A *memory module* packages one such data structure. It
is an `FLTS` whose states are the module's contents and whose labels are the operations the
controller may perform, together with a map `read` to what the controller observes in one step.
Modules combine by `MemoryModule.prod` and `MemoryModule.pi`, which observe and update every
component at once.

A `MemoryMachine` attaches a controller to a module: from an observation, it chooses an
operation or halts. A step reads the contents, asks the controller, and applies the chosen
operation. The finite control state is itself a module (`MemoryModule.register`), so the
controller is a stateless table. Different models are then different choices of module:

* a single-tape Turing machine is a register and a `MemoryModule.biTape`
  (`Cslib.Turing.SingleTapeTM.toMemoryComputer`);
* a multi-tape Turing machine on an input is a register, a read-only input tape, `k` work tapes
  and an output tape (`Turing.MultiTapeTM.toMemoryMachine`; the tapes are in
  `Machines.Memory.Tape`, which also has multi-dimensional and multi-head tapes);
* a deterministic finite automaton is a register and a `MemoryModule.stream`
  (`Cslib.Automata.DA.FinAcc.toMemoryComputer`), and nondeterministic automata, with or without
  `ε`-transitions, are the same through the subset construction;
* a deterministic pushdown automaton is a register, a stream and a `MemoryModule.stack`
  (`Cslib.Automata.DPDA.toMemoryMachine`);
* an unlimited register machine is a register for its program counter and a bank of registers
  that observes which registers are equal (`Cslib.URM.toMemoryComputer`);
* a pointer machine is a register for its label and a store of registers and records
  (`Cslib.PointerMachine.toMemoryMachine`).

Each of these translations is step-exact, and `MemoryMachine.relatesInSteps_iff_of_step_iff`
transfers runs of any length across such a translation.

A `MemoryComputer` adds the loading of an input (`init`) and the reading of a result
(`output`), and computes the partial function `MemoryComputer.eval`, through Mathlib's
`StateTransition.eval`. Time is the number of steps (`MemoryMachine.HaltsIn`,
`MemoryComputer.OutputsWithinTime`). Space is a size function on contents: if each step grows
it by at most one, a run halting in `n` steps stays within `n` of its starting size
(`MemoryMachine.size_le_of_haltsIn`).

The design follows the outline "Manipulable Memory Modules" in
[BoltonBailey/mathlib4#75](https://github.com/BoltonBailey/mathlib4/issues/75). Modules are not
lenses: reading after an operation need not return what the operation wrote (a tape write
followed by a move, for example).

## Main definitions

* `Cslib.Machines.MemoryModule`: contents, observations and operations.
* `MemoryModule.prod`, `MemoryModule.pi`: modules side by side.
* `MemoryModule.register`, `MemoryModule.biTape`, `MemoryModule.stream`, `MemoryModule.stack`.
* `Cslib.Machines.MemoryMachine`, `MemoryMachine.step`, `MemoryMachine.Step`,
  `MemoryMachine.HaltsIn`.
* `Cslib.Machines.MemoryComputer`, `MemoryComputer.eval`, `MemoryComputer.OutputsWithinTime`.

## Main results

* `MemoryMachine.relatesInSteps_iff_of_step_iff`, `MemoryMachine.reflTransGen_iff_of_step_iff`,
  `MemoryMachine.relatesInSteps_iff_of_step_eq`: a step-exact translation into a memory machine
  preserves and reflects runs with their lengths.
* `MemoryMachine.eval_eq_map_of_step_eq`: it commutes with running to completion.
* `MemoryMachine.mem_eval_iff_exists_haltsIn`, `MemoryComputer.mem_eval_iff`: results are the
  halting configurations reached in finitely many steps.
* `MemoryMachine.size_le_of_haltsIn`: time bounds space.
-/

public section

namespace Cslib.Machines

open Relation

universe u v w

/-- A memory module with contents `Contents`: the controller sees `read` of the contents and
changes them by applying an operation of type `Op` with the transition function `tr`. -/
structure MemoryModule (Contents : Type u) (Obs : Type v) (Op : Type w)
    extends FLTS Contents Op where
  /-- What the controller observes of the contents in one step. -/
  read : Contents → Obs

namespace MemoryModule

variable {C₁ O₁ P₁ C₂ O₂ P₂ : Type*}

/-- Two modules side by side: both are observed, and an operation updates both. -/
@[expose] def prod (M₁ : MemoryModule C₁ O₁ P₁) (M₂ : MemoryModule C₂ O₂ P₂) :
    MemoryModule (C₁ × C₂) (O₁ × O₂) (P₁ × P₂) where
  tr c p := (M₁.tr c.1 p.1, M₂.tr c.2 p.2)
  read c := (M₁.read c.1, M₂.read c.2)

/-- An indexed family of modules, such as the `k` work tapes of a `k`-tape machine. -/
@[expose] def pi {ι : Type*} {C O P : ι → Type*} (M : ∀ i, MemoryModule (C i) (O i) (P i)) :
    MemoryModule (∀ i, C i) (∀ i, O i) (∀ i, P i) where
  tr c p i := (M i).tr (c i) (p i)
  read c i := (M i).read (c i)

/-- A register holding a value of `α`, which is observed in full and overwritten by each
operation. With a finite `α` this is the finite control of a machine. -/
@[expose] def register (α : Type*) : MemoryModule α α α where
  tr _ a := a
  read := id

/-- A bidirectionally infinite tape (`Cslib.Turing.BiTape`). The controller sees the cell under
the head; an operation writes that cell and then optionally moves the head, as in
`Cslib.Turing.SingleTapeTM`. -/
@[expose] def biTape (Symbol : Type) :
    MemoryModule (Turing.BiTape Symbol) (Option Symbol) (Turing.SingleTapeTM.Stmt Symbol) where
  tr t s := (t.write s.symbol).optionMove s.movement
  read := Turing.BiTape.head

/-- A one-way read-only input: the controller sees the next symbol (`none` once the input is
exhausted), and the operation `true` consumes it while `false` leaves the input unchanged. -/
@[expose] def stream (Symbol : Type*) : MemoryModule (List Symbol) (Option Symbol) Bool where
  tr l advance := if advance then l.tail else l
  read := List.head?

/-- A stack, top first. The controller sees the top symbol (`none` on the empty stack), and an
operation `w` replaces the top symbol by the word `w`, whose first symbol becomes the new top.
On the empty stack, `w` is pushed. -/
@[expose] def stack (Γ : Type*) : MemoryModule (List Γ) (Option Γ) (List Γ) where
  tr l w := w ++ l.tail
  read := List.head?

end MemoryModule

/-- A machine on the memory module `memory`: a controller that maps each observation to the
next operation, or to `none` to halt. -/
structure MemoryMachine (Contents : Type u) (Obs : Type v) (Op : Type w) where
  /-- The memory the machine works on. -/
  memory : MemoryModule Contents Obs Op
  /-- The operation chosen on an observation, or `none` to halt. -/
  control : Obs → Option Op

namespace MemoryMachine

variable {Contents : Type u} {Obs : Type v} {Op : Type w} (M : MemoryMachine Contents Obs Op)

/-- One step: observe the contents, and apply the operation the controller chooses. `none` means
that the machine has halted. -/
@[expose] def step (c : Contents) : Option Contents :=
  (M.control (M.memory.read c)).map (M.memory.tr c)

/-- The one-step relation of a memory machine. Its reflexive transitive closure is
`StateTransition.Reaches M.step`. -/
abbrev Step (c d : Contents) : Prop := d ∈ M.step c

/-- The machine started at `c` halts at `d` after exactly `n` steps. -/
@[expose] def HaltsIn (c d : Contents) (n : ℕ) : Prop :=
  RelatesInSteps M.Step c d n ∧ M.step d = none

/-- `d` is the result of running the machine from `c` exactly when it halts there after some
number of steps. -/
theorem mem_eval_iff_exists_haltsIn {c d : Contents} :
    d ∈ StateTransition.eval M.step c ↔ ∃ n, M.HaltsIn c d n := by
  rw [StateTransition.mem_eval, StateTransition.Reaches]
  constructor
  · rintro ⟨hrun, hhalt⟩
    obtain ⟨n, hn⟩ := hrun.relatesInSteps
    exact ⟨n, hn, hhalt⟩
  · rintro ⟨n, hn, hhalt⟩
    exact ⟨hn.reflTransGen, hhalt⟩

/-- A run that halts after `n` steps visits only configurations reachable from its start in at
most `n` steps; so if each step grows `size` by at most one, every configuration reachable from
`c` has size at most `size c + n`. Time bounds space. -/
theorem size_le_of_haltsIn {c d e : Contents} {n : ℕ} (size : Contents → ℕ)
    (hsize : ∀ x y, M.Step x y → size y ≤ size x + 1) (hhalt : M.HaltsIn c d n)
    (he : ReflTransGen M.Step c e) : size e ≤ size c + n := by
  obtain ⟨hrun, hd⟩ := hhalt
  induction hrun using RelatesInSteps.head_induction_on generalizing e with
  | hrefl =>
    rcases he.cases_head with rfl | ⟨_, hx, -⟩
    · simp
    · simp [hd] at hx
  | hhead hstep _ ih =>
    rcases he.cases_head with rfl | ⟨x, hx, hxe⟩
    · omega
    · have : x = _ := Option.some_injective _ (hx.symm.trans hstep)
      subst this
      have := hsize _ _ hstep
      have := ih hxe
      omega

/-- A step-exact translation `e` of a system with one-step relation `r` into a memory machine
preserves and reflects runs, with their number of steps. -/
theorem relatesInSteps_iff_of_step_iff {α : Type*} {r : α → α → Prop} (e : α ≃ Contents)
    (h : ∀ a b, M.Step (e a) (e b) ↔ r a b) {a b : α} {n : ℕ} :
    RelatesInSteps M.Step (e a) (e b) n ↔ RelatesInSteps r a b n := by
  constructor
  · intro hrun
    simpa using hrun.map e.symm fun c d hcd => (h _ _).1 (by simpa using hcd)
  · exact RelatesInSteps.map e fun a b hab => (h a b).2 hab

/-- A step-exact translation `e` of a system with one-step relation `r` into a memory machine
preserves and reflects reachability. -/
theorem reflTransGen_iff_of_step_iff {α : Type*} {r : α → α → Prop} (e : α ≃ Contents)
    (h : ∀ a b, M.Step (e a) (e b) ↔ r a b) {a b : α} :
    ReflTransGen M.Step (e a) (e b) ↔ ReflTransGen r a b :=
  ⟨fun hrun => by
    obtain ⟨n, hn⟩ := hrun.relatesInSteps
    exact ((M.relatesInSteps_iff_of_step_iff e h).1 hn).reflTransGen,
  fun hrun => by
    obtain ⟨n, hn⟩ := hrun.relatesInSteps
    exact ((M.relatesInSteps_iff_of_step_iff e h).2 hn).reflTransGen⟩

/-- The function version of `relatesInSteps_iff_of_step_iff`: a translation `e` with
`M.step (e a) = (step' a).map e` preserves and reflects runs of `step'`. -/
theorem relatesInSteps_iff_of_step_eq {α : Type*} {step' : α → Option α} (e : α ≃ Contents)
    (h : ∀ a, M.step (e a) = (step' a).map e) {a b : α} {n : ℕ} :
    RelatesInSteps M.Step (e a) (e b) n ↔ RelatesInSteps (fun a b => step' a = some b) a b n :=
  M.relatesInSteps_iff_of_step_iff e fun a b => by simp [h]

/-- A step-exact translation `e` (not necessarily injective) of a system with step function
`step'` into a memory machine commutes with running to completion. -/
theorem eval_eq_map_of_step_eq {α : Type u} {step' : α → Option α} (e : α → Contents)
    (h : ∀ a, M.step (e a) = (step' a).map e) (a : α) :
    StateTransition.eval M.step (e a) = (StateTransition.eval step' a).map e :=
  StateTransition.tr_eval' _ _ e (StateTransition.fun_respects.2 fun a => by
    have := h a
    cases hs : step' a with
    | none => rw [hs] at this; exact this
    | some b => rw [hs] at this; exact Relation.TransGen.single this) a

end MemoryMachine

/-- A memory machine computing a partial function `In → Out`: inputs are loaded into memory by
`init`, and the result is read from the halting contents by `output`. -/
structure MemoryComputer (In Out : Type*) (Contents : Type u) (Obs : Type v) (Op : Type w)
    extends MemoryMachine Contents Obs Op where
  /-- The contents the machine starts from on an input. -/
  init : In → Contents
  /-- The result read off halting contents. -/
  output : Contents → Out

namespace MemoryComputer

variable {In Out Contents Obs Op : Type*} (M : MemoryComputer In Out Contents Obs Op)

/-- The partial function computed: run from `init x` until the machine halts, and read the
output. It is undefined when the machine runs forever. -/
@[expose] def eval (x : In) : Part Out :=
  (StateTransition.eval M.step (M.init x)).map M.output

/-- `M` outputs `y` on `x` within `t` steps. -/
@[expose] def OutputsWithinTime (x : In) (y : Out) (t : ℕ) : Prop :=
  ∃ c n, n ≤ t ∧ M.HaltsIn (M.init x) c n ∧ M.output c = y

/-- The result of `M` on `x` is `y` exactly when `M` outputs `y` on `x` within some time. -/
theorem mem_eval_iff {x : In} {y : Out} : y ∈ M.eval x ↔ ∃ t, M.OutputsWithinTime x y t := by
  simp only [eval, Part.mem_map_iff, MemoryMachine.mem_eval_iff_exists_haltsIn,
    OutputsWithinTime]
  constructor
  · rintro ⟨c, ⟨n, hn⟩, rfl⟩
    exact ⟨n, c, n, le_rfl, hn, rfl⟩
  · rintro ⟨t, c, n, -, hn, rfl⟩
    exact ⟨c, ⟨n, hn⟩, rfl⟩

end MemoryComputer

end Cslib.Machines

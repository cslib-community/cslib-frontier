/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Frame
public import CslibFrontier.Computability.Program.Structured

/-!
# Structured pointer-machine programs

Flat programs are lists of `Instr` with numeric labels, which are inconvenient to write and to
reason about. This file makes the pointer machine an instruction set (`instructionSet`) for the
structured programs of `Cslib.Program`: its data instructions (`Op`) and its two tests (`Test`),
acting on states. `Code`, `Exec` and `ExecWithin` are those of `Cslib.Program` at this
instruction set, so the sequencing, conditional and loop rules there (`Program.ExecWithin.seq`,
`Program.ExecWithin.loopUntil_invariant`, …) apply to them as they are, also by field notation.
This file adds what is specific to the machine: the effect of a data instruction, and the
program counter, validity and field frame of an execution.

`Exec c x y n` relates states and ignores the program counter: `y.pc = x.pc` (`Exec.pc_eq`).
The count `n` is exactly that of the flat program `c` assembles to (`Exec.runs` in `Assemble`).

The machine jumps when a test holds, so `Code.loopUntil t body` (while `t` fails) costs one test
and one jump per iteration; it is the natural loop for `while r ≠ null`.

Loop-free code is executed by the interpreter `Code.eval`, which `simp` evaluates on symbolic
states (`ExecWithin.of_eval`).

## Main definitions

* `Op`, `Test`, `instructionSet`: data instructions, tests and the instruction set they form.
* `Code`, `Exec`, `ExecWithin`, `Code.eval`: structured programs, their executions and the
  interpreter, at this instruction set.

## Main results

* `Exec.valid`, `Exec.pc_eq`: executions preserve validity and the program counter.
* `Exec.op`, `ExecWithin.op`: a data instruction, with the state it reaches in closed form.
* `State.ptr_setPtr`, `State.data_setData`, `State.deref_setData` and the like: simp lemmas for
  the registers and records after an assignment, for symbolic execution.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-! ## Registers and records after an assignment -/

namespace State

variable (x : State M L)

/-- The pointer registers after a pointer assignment. -/
@[simp] theorem ptr_setPtr (r : Fin L.ptrRegs) (p : Pointer) :
    (x.setPtr r p).ptr = Function.update x.ptr r p := rfl

/-- A pointer assignment keeps the data registers. -/
@[simp] theorem data_setPtr (r : Fin L.ptrRegs) (p : Pointer) : (x.setPtr r p).data = x.data := rfl

/-- A pointer assignment keeps the records. -/
@[simp] theorem heap_setPtr (r : Fin L.ptrRegs) (p : Pointer) : (x.setPtr r p).heap = x.heap := rfl

/-- A pointer assignment keeps the program counter. -/
@[simp] theorem pc_setPtr (r : Fin L.ptrRegs) (p : Pointer) : (x.setPtr r p).pc = x.pc := rfl

/-- A data assignment keeps the pointer registers. -/
@[simp] theorem ptr_setData (s : Fin L.dataRegs) (v : M.Value) : (x.setData s v).ptr = x.ptr := rfl

/-- The data registers after a data assignment. -/
@[simp] theorem data_setData (s : Fin L.dataRegs) (v : M.Value) :
    (x.setData s v).data = Function.update x.data s v := rfl

/-- A data assignment keeps the records. -/
@[simp] theorem heap_setData (s : Fin L.dataRegs) (v : M.Value) :
    (x.setData s v).heap = x.heap := rfl

/-- A data assignment keeps the program counter. -/
@[simp] theorem pc_setData (s : Fin L.dataRegs) (v : M.Value) : (x.setData s v).pc = x.pc := rfl

/-- A data assignment keeps the record a register specifies. -/
@[simp] theorem deref_setData (s : Fin L.dataRegs) (v : M.Value) (r : Fin L.ptrRegs) :
    (x.setData s v).deref r = x.deref r := rfl

/-- After assigning it a record's address, a register specifies that record. -/
theorem deref_setPtr_some (r : Fin L.ptrRegs) (a : ℕ) :
    (x.setPtr r (some a)).deref r = x.heap[a]? := by
  simp [State.deref]

/-- After assigning it null, a register specifies no record. -/
theorem deref_setPtr_none (r : Fin L.ptrRegs) : (x.setPtr r none).deref r = none := by
  simp [State.deref]

/-- A pointer assignment keeps the record another register specifies. -/
theorem deref_setPtr_of_ne {r r' : Fin L.ptrRegs} (h : r' ≠ r) (p : Pointer) :
    (x.setPtr r p).deref r' = x.deref r' := by
  simp [State.deref, Function.update_of_ne h]

end State

/-- The data instructions of a pointer machine: those of `Instr` other than jumps and `halt`. -/
inductive Op (M : Model) (L : Layout) where
  /-- `r ← null`. -/
  | null (r : Fin L.ptrRegs)
  /-- `r ← r'`. -/
  | movePtr (r r' : Fin L.ptrRegs)
  /-- `s ← s'`. -/
  | moveData (s s' : Fin L.dataRegs)
  /-- `r ← f(base)`. -/
  | loadPtr (r : Fin L.ptrRegs) (f : Fin L.ptrFields) (base : Fin L.ptrRegs)
  /-- `s ← f(base)`. -/
  | loadData (s : Fin L.dataRegs) (f : Fin L.dataFields) (base : Fin L.ptrRegs)
  /-- `f(base) ← r`. -/
  | storePtr (f : Fin L.ptrFields) (base : Fin L.ptrRegs) (r : Fin L.ptrRegs)
  /-- `f(base) ← s`. -/
  | storeData (f : Fin L.dataFields) (base : Fin L.ptrRegs) (s : Fin L.dataRegs)
  /-- `s ← s₁ o s₂`. -/
  | op (o : M.Op) (s s₁ s₂ : Fin L.dataRegs)
  /-- Create a record and place a pointer to it in `r`. -/
  | create (r : Fin L.ptrRegs)

/-- The instruction of a data instruction. -/
@[expose] def Op.instr : Op M L → Instr M L
  | .null r => .null r
  | .movePtr r r' => .movePtr r r'
  | .moveData s s' => .moveData s s'
  | .loadPtr r f base => .loadPtr r f base
  | .loadData s f base => .loadData s f base
  | .storePtr f base r => .storePtr f base r
  | .storeData f base s => .storeData f base s
  | .op o s s₁ s₂ => .op o s s₁ s₂
  | .create r => .create r

/-- The effect of a data instruction on registers and records. -/
@[expose] def Op.effect (o : Op M L) (x : State M L) : State M L := o.instr.effect x

/-- The tests of a pointer machine. -/
inductive Test (M : Model) (L : Layout) where
  /-- `r₁ = r₂`, on pointer registers. -/
  | ptrEq (r₁ r₂ : Fin L.ptrRegs)
  /-- `p(s₁, s₂)`, on data registers. -/
  | data (p : M.Test) (s₁ s₂ : Fin L.dataRegs)

/-- Whether a test holds in a state. -/
@[expose] def Test.Holds (x : State M L) : Test M L → Prop
  | .ptrEq r₁ r₂ => x.ptr r₁ = x.ptr r₂
  | .data p s₁ s₂ => M.evalTest p (x.data s₁) (x.data s₂) = true

instance (x : State M L) (t : Test M L) : Decidable (t.Holds x) := by
  cases t <;> exact inferInstanceAs (Decidable (_ = _))

/-- The instruction that goes to `label` if the test holds. -/
@[expose] def Test.instr (label : ℕ) : Test M L → Instr M L
  | .ptrEq r₁ r₂ => .ifPtrEq r₁ r₂ label
  | .data p s₁ s₂ => .ifTest p s₁ s₂ label

/-- The pointer machine as an instruction set for structured programs: data instructions and
tests on states. No data instruction faults. -/
@[expose, reducible] def instructionSet (M : Model) (L : Layout) : Program.InstructionSet where
  Data := State M L
  Op := Op M L
  Test := Test M L
  eval o x := some (o.effect x)
  Holds t x := t.Holds x

instance (t : Test M L) (x : State M L) : Decidable ((instructionSet M L).Holds t x) :=
  inferInstanceAs (Decidable (t.Holds x))

/-- Structured pointer-machine programs. -/
abbrev Code (M : Model) (L : Layout) : Type := Program.Code (Op M L) (Test M L)

/-- `Exec c x y n`: the structured program `c` leads from `x` to `y` executing exactly `n`
instructions of the flat program it assembles to. The program counter is ignored. -/
abbrev Exec (c : Code M L) (x y : State M L) (n : ℕ) : Prop :=
  Program.Exec (instructionSet M L) c x y n

/-- `ExecWithin c x y T`: the structured program `c` leads from `x` to `y` within `T`
instructions. -/
abbrev ExecWithin (c : Code M L) (x y : State M L) (T : ℕ) : Prop :=
  Program.ExecWithin (instructionSet M L) c x y T

/-- Run a structured program, allowing each loop at most `fuel` iterations per entry: the state
reached and the instruction count, or `none` if a loop runs out of iterations. -/
abbrev Code.eval (c : Code M L) (fuel : ℕ) (x : State M L) : Option (State M L × ℕ) :=
  Program.Code.eval (instructionSet M L) fuel c x

/-- A data instruction keeps the program counter. -/
@[simp] theorem Op.pc_effect (o : Op M L) (x : State M L) : (o.effect x).pc = x.pc := by
  cases o <;> simp only [Op.effect, Op.instr, Instr.effect, State.setPtr, State.setData,
    State.modify]
  case loadPtr r f base => cases x.deref base <;> rfl
  case loadData s f base => cases x.deref base <;> rfl
  case storePtr f base r => split <;> rfl
  case storeData f base s => split <;> rfl

namespace Exec

variable {c : Code M L} {x y : State M L} {n : ℕ}

/-- A data instruction is one instruction. -/
theorem op {o : Op M L} : Exec (.op o) x (o.effect x) 1 := Program.Exec.op rfl

/-- Executions keep the program counter. -/
theorem pc_eq (h : Exec c x y n) : y.pc = x.pc :=
  Program.Exec.invariant (I := instructionSet M L) (fun z => z.pc = x.pc)
    (fun o a _ hab ha => Option.some.inj hab ▸ (o.pc_effect a).trans ha) h rfl

/-- Executions preserve validity. -/
theorem valid (h : Exec c x y n) (hx : x.Valid) : y.Valid :=
  Program.Exec.invariant (I := instructionSet M L) State.Valid
    (fun _ _ _ hab ha => Option.some.inj hab ▸ Instr.effect_valid ha) h hx

end Exec

namespace ExecWithin

variable {c : Code M L} {x y : State M L} {T : ℕ}

/-- A data instruction executes within one instruction. -/
theorem op {o : Op M L} : ExecWithin (.op o) x (o.effect x) 1 :=
  ⟨1, le_rfl, Exec.op⟩

/-- A data instruction executes within one instruction, reaching a state given in advance. -/
theorem op_eq {o : Op M L} (h : o.effect x = y) : ExecWithin (.op o) x y 1 := h ▸ op

/-- A list of data instructions executes within its length, reaching the state that their
effects give in order. -/
theorem seqList_op (os : List (Op M L)) (x : State M L) :
    ExecWithin (Program.Code.seqList (os.map .op)) x (os.foldl (fun s o => o.effect s) x)
      os.length := by
  induction os generalizing x with
  | nil => exact Program.ExecWithin.skip
  | cons o os ih =>
    exact (Program.ExecWithin.seq op (ih (o.effect x))).mono (by simp [Nat.add_comm])

/-- When no data instruction of the program allocates or stores `field`, every execution
preserves that field at every address, including the absence of a record. -/
theorem data_frame (run : ExecWithin c x y T) (field : Fin L.dataFields)
    (safe : ∀ o ∈ Program.Code.ops c, ¬o.instr.WritesData field) (a : ℕ) :
    (y.heap[a]?).map (fun r => r.data field) = (x.heap[a]?).map (fun r => r.data field) :=
  let ⟨_, _, he⟩ := run
  Program.Exec.invariant_ops (I := instructionSet M L)
    (fun z => (z.heap[a]?).map (fun r => r.data field) = (x.heap[a]?).map (fun r => r.data field))
    he (fun o ho z _ hz hP => Option.some.inj hz ▸
      (Instr.effect_data_frame o.instr field (safe o ho) z a).trans hP) rfl

/-- Executions within a bound keep the program counter. -/
theorem pc_eq (h : ExecWithin c x y T) : y.pc = x.pc :=
  let ⟨_, _, he⟩ := h
  Exec.pc_eq he

/-- Executions within a bound preserve validity. -/
theorem valid (h : ExecWithin c x y T) (hx : x.Valid) : y.Valid :=
  let ⟨_, _, he⟩ := h
  Exec.valid he hx

end ExecWithin

end Cslib.PointerMachine

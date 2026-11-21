/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Structured
public import CslibFrontier.Computability.Program.Assemble

/-!
# Assembling structured pointer-machine programs

The pointer machine is a `Program.FlatMachine` for its instruction set (`flatMachine`), so a
structured program (`Code`) assembles into a flat list of instructions (`Code.assemble`) whose
conditionals and loops are tests and jumps to absolute labels. Every structured execution is a
run of the assembled program with exactly the same number of instructions (`Exec.runs`), so
bounds proved with the rules of `Structured` are bounds on the machine of `Defs`.

The assembled program followed by `halt` (`Code.program`) is an ordinary flat program, so it
composes with hand-written ones through `Executes.inBlock`, `sequence` and `branch` of `Blocks`.

## Main definitions

* `flatMachine`: the instructions and steps of the pointer machine, for assembly.
* `Code.assemble`, `Code.program`: assembly at a given label, and the complete halting program.

## Main results

* `Exec.runs`: a structured execution is a run of the assembled program inside any program.
* `Exec.executes`, `ExecWithin.executes`: it is a halting run of the complete program, with one
  more instruction for the `halt`.
-/

public section

namespace Cslib.PointerMachine

variable {M : Model} {L : Layout}

/-- The effect of an instruction does not depend on the program counter. -/
private theorem Instr.effect_withPc (i : Instr M L) (x : State M L) (pc : ℕ) :
    i.effect { x with pc := pc } = { i.effect x with pc := pc } := by
  cases i <;> simp only [Instr.effect, State.setPtr, State.setData, State.modify, State.deref]
  case loadPtr r f base => cases (x.ptr base).bind (x.heap[·]?) <;> rfl
  case loadData s f base => cases (x.ptr base).bind (x.heap[·]?) <;> rfl
  case storePtr f base r => cases x.ptr base <;> rfl
  case storeData f base s => cases x.ptr base <;> rfl

section Steps

variable {p : List (Instr M L)} {x : State M L} {pc : ℕ}

/-- A data instruction steps to the next label with its effect. -/
theorem step_op {o : Op M L} (h : p[pc]? = some o.instr) :
    step p { x with pc := pc } = some { o.effect x with pc := pc + 1 } := by
  refine step_eq_some_iff.mpr ⟨o.instr, h, by cases o <;> simp [Op.instr], ?_⟩
  rw [Instr.effect_withPc]
  cases o <;> rfl

/-- A `goto` steps to its label. -/
theorem step_goto {label : ℕ} (h : p[pc]? = some (.goto label)) :
    step p { x with pc := pc } = some { x with pc := label } :=
  step_eq_some_iff.mpr ⟨_, h, by simp, rfl⟩

/-- A test that holds steps to its label. -/
theorem step_test_pos {t : Test M L} {label : ℕ} (h : p[pc]? = some (t.instr label))
    (ht : t.Holds x) : step p { x with pc := pc } = some { x with pc := label } := by
  refine step_eq_some_iff.mpr ⟨_, h, by cases t <;> simp [Test.instr], ?_⟩
  cases t <;> simp_all [Test.instr, Test.Holds, Instr.effect, Instr.next]

/-- A test that fails steps to the next label. -/
theorem step_test_neg {t : Test M L} {label : ℕ} (h : p[pc]? = some (t.instr label))
    (ht : ¬t.Holds x) : step p { x with pc := pc } = some { x with pc := pc + 1 } := by
  refine step_eq_some_iff.mpr ⟨_, h, by cases t <;> simp [Test.instr], ?_⟩
  cases t <;> simp_all [Test.instr, Test.Holds, Instr.effect, Instr.next]

end Steps

/-- The pointer machine as a flat machine for its instruction set. A state of the flat machine
is a label and a state whose own program counter is ignored. -/
@[expose, reducible] def flatMachine (M : Model) (L : Layout) :
    Program.FlatMachine (instructionSet M L) where
  Instr := Instr M L
  op o := o.instr
  goto label := .goto label
  jumpIf t label := t.instr label
  Step p a b := step p { a.2 with pc := a.1 } = some { b.2 with pc := b.1 }
  step_op h ho := by
    cases ho
    exact step_op h
  step_goto h := step_goto h
  step_jumpIf_pos h ht := step_test_pos h ht
  step_jumpIf_neg h ht := step_test_neg h ht

/-- Assemble a structured program to be placed at label `pc`. -/
abbrev Code.assemble (c : Code M L) (pc : ℕ) : List (Instr M L) :=
  Program.Code.assemble (flatMachine M L) c pc

/-- Assembling `c` at any label gives `c.size` instructions. -/
@[simp] theorem Code.length_assemble (c : Code M L) (pc : ℕ) :
    (c.assemble pc).length = c.size :=
  Program.Code.length_assemble (flatMachine M L) c pc

/-- The complete program: the assembled structured program followed by `halt`. -/
@[expose] def Code.program (c : Code M L) : List (Instr M L) := c.assemble 0 ++ [.halt]

/-- **Assembly is correct.** A structured execution is a run of the assembled program placed
after any prefix and before any suffix, from its first instruction to the label after it, with
exactly the same number of instructions. -/
theorem Exec.runs {c : Code M L} {x y : State M L} {n : ℕ} (h : Exec c x y n)
    (pre post : List (Instr M L)) :
    Runs (pre ++ c.assemble pre.length ++ post) { x with pc := pre.length }
      { y with pc := pre.length + c.size } n := by
  have run := Program.Exec.runs (flatMachine M L) h pre post
  exact run.map (r' := fun a b => step (pre ++ c.assemble pre.length ++ post) a = some b)
    (fun a : ℕ × State M L => ({ a.2 with pc := a.1 } : State M L)) (fun _ _ step => step)

/-- A structured execution is a halting run of the complete program, with one more instruction
for the `halt`. -/
theorem Exec.executes {c : Code M L} {x y : State M L} {n : ℕ} (h : Exec c x y n)
    (pc : x.pc = 0) : Executes c.program x { y with pc := c.size } (n + 1) := by
  have run := h.runs [] [.halt]
  obtain ⟨_, _, _, _⟩ := x
  subst pc
  refine ⟨n, by simpa [Code.program] using run, ?_, rfl⟩
  simp [Code.program]

/-- A structured execution within `T` instructions is a halting run of the complete program
within `T + 1`. -/
theorem ExecWithin.executes {c : Code M L} {x y : State M L} {T : ℕ} (h : ExecWithin c x y T)
    (pc : x.pc = 0) : ∃ time ≤ T + 1, Executes c.program x { y with pc := c.size } time :=
  let ⟨n, hn, he⟩ := h
  ⟨n + 1, Nat.add_le_add_right hn 1, Exec.executes he pc⟩

end Cslib.PointerMachine

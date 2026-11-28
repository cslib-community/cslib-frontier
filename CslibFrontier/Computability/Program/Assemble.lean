/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger, Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger, Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Program.Structured
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Assembling structured programs

A structured program (`Code`) assembles into a flat list of instructions (`Code.assemble`) whose
conditionals and loops are tests and jumps to absolute labels. A machine supplies a `FlatMachine`:
its instructions, among them the data instructions, an unconditional jump and a jump on each
test, and its step relation, with the four facts about these that assembly relies on. Every
structured execution is then a run of the assembled program with exactly the same number of
instructions (`Exec.runs`), so bounds proved with the rules of `Program.Structured` are bounds on
the flat machine.

## Main definitions

* `FlatMachine`: the flat instructions and step relation of a machine with an instruction set.
* `Code.assemble`: assembly at a given label.

## Main results

* `Code.length_assemble`: the assembled program has `Code.size` instructions.
* `Exec.runs`: a structured execution is a run of the assembled program inside any program.

## References

* [MIT–ULB CompGeom Group, *Undecidability of tiling with a tromino*][Tromino2025]; assembly and
  its correctness generalize `Cslib.WordRAM.Code.assemble` and `Cslib.WordRAM.Exec.runs`, which
  are adapted from its accompanying Lean formalization.
-/

public section

namespace Cslib.Program

universe u v w i

/-- The flat instructions of a machine with instruction set `I`, and how it steps. A state is a
label and the data. The four step facts say that the instructions named here behave as data
instructions, jumps and tests; the machine may have other instructions, such as a halt. -/
structure FlatMachine (I : InstructionSet.{u, v, w}) where
  /-- Flat instructions. -/
  Instr : Type i
  /-- A data instruction. -/
  op : I.Op → Instr
  /-- Go to a label. -/
  goto : ℕ → Instr
  /-- Go to a label if a test holds. -/
  jumpIf : I.Test → ℕ → Instr
  /-- One step of a program, from a label and data to a label and data. -/
  Step : List Instr → ℕ × I.Data → ℕ × I.Data → Prop
  /-- A data instruction continues at the next label with the data it produces. -/
  step_op {p : List Instr} {pc : ℕ} {o : I.Op} {x y : I.Data} :
    p[pc]? = some (op o) → I.eval o x = some y → Step p (pc, x) (pc + 1, y)
  /-- A jump continues at its label. -/
  step_goto {p : List Instr} {pc label : ℕ} {x : I.Data} :
    p[pc]? = some (goto label) → Step p (pc, x) (label, x)
  /-- A test that holds continues at its label. -/
  step_jumpIf_pos {p : List Instr} {pc label : ℕ} {t : I.Test} {x : I.Data} :
    p[pc]? = some (jumpIf t label) → I.Holds t x → Step p (pc, x) (label, x)
  /-- A test that fails continues at the next label. -/
  step_jumpIf_neg {p : List Instr} {pc label : ℕ} {t : I.Test} {x : I.Data} :
    p[pc]? = some (jumpIf t label) → ¬I.Holds t x → Step p (pc, x) (pc + 1, x)

variable {I : InstructionSet.{u, v, w}} (F : FlatMachine.{u, v, w, i} I)

/-- Assemble a structured program to be placed at label `pc`. -/
@[expose] def Code.assemble : Code I.Op I.Test → ℕ → List F.Instr
  | .skip, _ => []
  | .op o, _ => [F.op o]
  | .seq c₁ c₂, pc => c₁.assemble pc ++ c₂.assemble (pc + c₁.size)
  | .branch t pos neg, pc =>
    F.jumpIf t (pc + neg.size + 2) :: neg.assemble (pc + 1) ++
      F.goto (pc + neg.size + pos.size + 2) :: pos.assemble (pc + neg.size + 2)
  | .loop t body, pc =>
    F.jumpIf t (pc + 2) :: F.goto (pc + body.size + 3) :: body.assemble (pc + 2) ++ [F.goto pc]
  | .loopUntil t body, pc =>
    F.jumpIf t (pc + body.size + 2) :: body.assemble (pc + 1) ++ [F.goto pc]

/-- Assembling `c` at any label gives `c.size` instructions. -/
@[simp] theorem Code.length_assemble (c : Code I.Op I.Test) (pc : ℕ) :
    (c.assemble F pc).length = c.size := by
  induction c generalizing pc with
  | branch _ _ _ ihp ihn =>
    simp only [Code.assemble, List.length_append, List.length_cons, ihp, ihn, Code.size]
    omega
  | _ => simp_all [Code.assemble]

variable {F}

/-- `p` contains `q` from label `base`. -/
@[expose] def Contains {α : Type*} (p : List α) (base : ℕ) (q : List α) : Prop :=
  ∃ pre post, p = pre ++ q ++ post ∧ pre.length = base

namespace Contains

variable {α : Type*} {p q q₁ q₂ : List α} {base : ℕ} {j : α}

/-- Retain the left part of the contained block. -/
theorem append_left (h : Contains p base (q₁ ++ q₂)) : Contains p base q₁ :=
  let ⟨pre, post, hp, hl⟩ := h
  ⟨pre, q₂ ++ post, by simp [hp], hl⟩

/-- Retain the right part and advance the starting label. -/
theorem append_right (h : Contains p base (q₁ ++ q₂)) :
    Contains p (base + q₁.length) q₂ :=
  let ⟨pre, post, hp, hl⟩ := h
  ⟨pre ++ q₁, post, by simp [hp], by simp [hl]⟩

/-- Drop the first instruction of the contained block. -/
theorem cons_tail (h : Contains p base (j :: q)) : Contains p (base + 1) q :=
  append_right (q₁ := [j]) h

/-- Fetch the first instruction of the contained block. -/
theorem head (h : Contains p base (j :: q)) : p[base]? = some j := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  simp

end Contains

open Relation in
private theorem Exec.runs_of_contains {p : List F.Instr} {c : Code I.Op I.Test} {x y : I.Data}
    {n pc : ℕ} (h : Exec I c x y n) (hp : Contains p pc (c.assemble F pc)) :
    RelatesInSteps (F.Step p) (pc, x) (pc + c.size, y) n := by
  induction h generalizing pc with
  | skip => exact .refl _
  | op ho => exact .single (F.step_op hp.head ho)
  | @seq c₁ c₂ x y z m n _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hp.append_left
    have h₂ := ih₂ (pc := pc + c₁.size) (by simpa using hp.append_right)
    simpa [Code.size, Nat.add_assoc] using h₁.trans h₂
  | @branch_pos t pos neg x y n ht _ ih =>
    have hb := F.step_jumpIf_pos hp.head ht
    have hc := (hp.cons_tail.append_right (q₁ := neg.assemble F (pc + 1))).cons_tail
    rw [Code.length_assemble, show pc + 1 + neg.size + 1 = pc + neg.size + 2 by omega] at hc
    have := RelatesInSteps.head _ _ _ _ hb (ih hc)
    simpa [Code.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | @branch_neg t pos neg x y n ht _ ih =>
    have hb := F.step_jumpIf_neg hp.head ht
    have hneg := ih (pc := pc + 1) hp.cons_tail.append_left
    have hj : F.Step p (pc + 1 + neg.size, y) (pc + neg.size + pos.size + 2, y) :=
      F.step_goto
        (by simpa using (hp.cons_tail.append_right (q₁ := neg.assemble F (pc + 1))).head)
    have := (RelatesInSteps.head _ _ _ _ hb hneg).tail _ _ _ _ hj
    simpa [Code.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | @loop_exit t body x ht =>
    have hb := F.step_jumpIf_neg hp.head ht
    have hj : F.Step p (pc + 1, x) (pc + body.size + 3, x) := F.step_goto hp.cons_tail.head
    simpa [Code.size, Nat.add_assoc] using (RelatesInSteps.single hb).tail _ _ _ _ hj
  | @loop_iter t body x y z m n ht _ _ ihb ihl =>
    have hb := F.step_jumpIf_pos hp.head ht
    have hbody := ihb (pc := pc + 2) (by
      simpa [Nat.add_assoc] using hp.cons_tail.cons_tail.append_left)
    have hj : F.Step p (pc + 2 + body.size, y) (pc, y) :=
      F.step_goto (by simpa using hp.cons_tail.cons_tail.append_right.head)
    have := ((RelatesInSteps.head _ _ _ _ hb hbody).tail _ _ _ _ hj).trans (ihl hp)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  | @loopUntil_exit t body x ht =>
    simpa [Code.size, Nat.add_assoc] using
      RelatesInSteps.single (F.step_jumpIf_pos hp.head ht)
  | @loopUntil_iter t body x y z m n ht _ _ ihb ihl =>
    have hb := F.step_jumpIf_neg hp.head ht
    have hbody := ihb (pc := pc + 1) hp.cons_tail.append_left
    have hj : F.Step p (pc + 1 + body.size, y) (pc, y) :=
      F.step_goto (by simpa using hp.cons_tail.append_right.head)
    have := ((RelatesInSteps.head _ _ _ _ hb hbody).tail _ _ _ _ hj).trans (ihl hp)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- **Assembly is correct.** A structured execution is a run of the assembled program placed
after any prefix and before any suffix, from its first instruction to the label after it, with
exactly the same number of instructions. -/
theorem Exec.runs (F : FlatMachine.{u, v, w, i} I) {c : Code I.Op I.Test} {x y : I.Data} {n : ℕ}
    (h : Exec I c x y n) (pre post : List F.Instr) :
    Relation.RelatesInSteps (F.Step (pre ++ c.assemble F pre.length ++ post))
      (pre.length, x) (pre.length + c.size, y) n :=
  h.runs_of_contains ⟨pre, post, rfl, rfl⟩

end Cslib.Program

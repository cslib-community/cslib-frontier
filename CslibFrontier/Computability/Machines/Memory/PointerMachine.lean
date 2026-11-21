/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Memory.Basic
public import CslibFrontier.Computability.PointerMachine.Defs

/-!
# Pointer machines as memory machines

A pointer machine (`Cslib.PointerMachine`, after [Tarjan1979]) runs a program on a label and a
*store*: its pointer and data registers and its pool of records. The store is a memory module
(`Cslib.PointerMachine.store`) whose operations are the instructions, acting by `Instr.effect`,
and whose observation is what a branch can test: which pointer registers are equal, and the
value of each data predicate on each pair of data registers. The label is a
`MemoryModule.register`. The controller looks up the instruction at the label (halting on
`halt` or outside the program) and computes the next label from the observation.

The store's contents are machine states whose label is `0`, so that a state is its label beside
its store (`stateEquiv`) while the store module reuses `Instr.effect`, which neither reads nor
changes the label (`Instr.effect_withPc`). The translation is step-exact (`step_toMemoryMachine`),
so the runs of the memory machine are the runs `PointerMachine.Runs` of the program
(`relatesInSteps_toMemoryMachine_iff`).

## Main definitions

* `Cslib.PointerMachine.Store`, `Cslib.PointerMachine.store`.
* `Cslib.PointerMachine.toMemoryMachine`, `Cslib.PointerMachine.stateEquiv`.

## Main results

* `Cslib.PointerMachine.step_toMemoryMachine`: one step of the memory machine is one step of
  the program.
* `Cslib.PointerMachine.relatesInSteps_toMemoryMachine_iff`: so are runs of any length.
-/

public section

namespace Cslib.PointerMachine

open Cslib.Machines Relation

variable {M : Model} {L : Layout}

/-- `x` with label `pc`. -/
@[expose] def State.withPc (x : State M L) (pc : ℕ) : State M L := { x with pc := pc }

/-- An instruction neither reads nor changes the label. -/
theorem Instr.effect_withPc (i : Instr M L) (x : State M L) (pc : ℕ) :
    i.effect (x.withPc pc) = (i.effect x).withPc pc := by
  have hderef (r) : (x.withPc pc).deref r = x.deref r := rfl
  cases i with
  | loadPtr r f base | loadData r f base =>
    simp only [Instr.effect, hderef]
    cases x.deref base <;> rfl
  | storePtr f base r | storeData f base r =>
    rcases h : x.ptr base with _ | a <;>
      simp [Instr.effect, State.modify, State.withPc, h]
  | _ => rfl

/-- The store of a pointer machine: its registers and records, as a state with label `0`. -/
abbrev Store (M : Model) (L : Layout) := {x : State M L // x.pc = 0}

/-- What a branch of a pointer machine can test: the equality of pointer registers, and each
data predicate on each pair of data registers. -/
abbrev Tests (M : Model) (L : Layout) :=
  (Fin L.ptrRegs → Fin L.ptrRegs → Bool) × (M.Test → Fin L.dataRegs → Fin L.dataRegs → Bool)

/-- The store as a memory module: the controller sees what a branch can test, and an
instruction acts by its effect. -/
@[expose] def store : MemoryModule (Store M L) (Tests M L) (Instr M L) where
  tr x i := ⟨(i.effect x.val).withPc 0, rfl⟩
  read x := (fun r₁ r₂ => decide (x.val.ptr r₁ = x.val.ptr r₂),
    fun p s₁ s₂ => M.evalTest p (x.val.data s₁) (x.val.data s₂))

/-- The label after an instruction at label `pc`, from the observed tests. -/
@[expose] def Instr.nextPc (pc : ℕ) (tests : Tests M L) : Instr M L → ℕ
  | .goto label => label
  | .ifPtrEq r₁ r₂ label => if tests.1 r₁ r₂ then label else pc + 1
  | .ifTest p s₁ s₂ label => if tests.2 p s₁ s₂ then label else pc + 1
  | _ => pc + 1

/-- A program as a memory machine on its label and its store. -/
@[expose] def toMemoryMachine (code : List (Instr M L)) :
    MemoryMachine (ℕ × Store M L) (ℕ × Tests M L) (ℕ × Instr M L) where
  memory := (MemoryModule.register ℕ).prod store
  control
    | (pc, tests) =>
      match code[pc]? with
      | none | some .halt => none
      | some i => some (i.nextPc pc tests, i)

/-- A state is its label and its store. -/
@[expose] def stateEquiv : State M L ≃ ℕ × Store M L where
  toFun x := (x.pc, ⟨x.withPc 0, rfl⟩)
  invFun
    | (pc, x) => x.val.withPc pc
  left_inv _ := rfl
  right_inv := by
    rintro ⟨pc, ⟨⟨_, _, _, _⟩, hx⟩⟩
    simp only at hx
    subst hx
    rfl

/-- The memory machine of a program takes exactly the steps of the program. -/
theorem step_toMemoryMachine (code : List (Instr M L)) (x : State M L) :
    (toMemoryMachine code).step (stateEquiv x) = (step code x).map stateEquiv := by
  have hnext (i : Instr M L) : i.nextPc x.pc (store.read ⟨x.withPc 0, rfl⟩) = i.next x := by
    cases i <;> first | rfl | simp [Instr.nextPc, Instr.next, store, State.withPc]
  have hstore (i : Instr M L) :
      (store.tr ⟨x.withPc 0, rfl⟩ i).val = (i.effect x).withPc 0 := by
    simp only [store, Instr.effect_withPc]
    rfl
  simp only [MemoryMachine.step, toMemoryMachine, step, MemoryModule.prod, MemoryModule.register,
    id, stateEquiv]
  rcases code[x.pc]? with _ | i
  · rfl
  · cases i
    case halt => rfl
    all_goals
      refine congrArg some (Prod.ext ?_ (Subtype.ext ?_)) <;> dsimp only
      · exact hnext _
      · exact hstore _

/-- A program takes `x` to `y` in `n` steps exactly when its memory machine does. -/
theorem relatesInSteps_toMemoryMachine_iff (code : List (Instr M L)) {x y : State M L} {n : ℕ} :
    RelatesInSteps (toMemoryMachine code).Step (stateEquiv x) (stateEquiv y) n ↔ Runs code x y n :=
  (toMemoryMachine code).relatesInSteps_iff_of_step_eq stateEquiv (step_toMemoryMachine code)

end Cslib.PointerMachine

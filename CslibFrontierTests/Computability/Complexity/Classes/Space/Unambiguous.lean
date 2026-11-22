/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.Space.Unambiguous
import Mathlib.Tactic.FinCases

/-! # Unambiguous space classes

A one-step counting machine that accepts according to the input bit is an unambiguous decider
within zero work space, a bound below the logarithm. Witnesses for `UL` and for
`USPACE(log₂ n)` convert in both directions, and an unambiguous witness gives an `NL` witness
through `NSPACE(log₂ n)`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Space.Unambiguous

open Turing MultiTapeCTM
open Cslib.Complexity Turing.MultiTapeTM

private def readBit : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ bit _ _ := [
    .step { inputTape := 0, workTapes := Fin.elim0, output := some (bit.getD false), state := none }
      Empty.elim Empty.elim]

/-- The one-step machine has one accepting branch on `true` and none on `false`, without work
tapes, so it is an unambiguous decider at the zero space bound. -/
example : ({true} : Set Bool) ∈ USPACE encBool fun _ => 0 := by
  let f (b : Bool) : ℕ := if b then 1 else 0
  refine ⟨0, Unit, inferInstance, readBit, 0, 0, f, fun a => ⟨?_, 1, ?_, ?_⟩, ?_, ?_⟩
  · intro p
    simp [MultiTapeNTM.ComputationPath.space, MultiTapeNTM.RunPath.space]
  · apply HaltsWithin.step (by cases a <;> decide)
    intro index
    apply HaltsWithin.halt
    cases a <;> fin_cases index <;> rfl
  · cases a <;> decide
  · intro a
    cases a <;> decide
  · intro a
    cases a <;> decide

/-- An unambiguous logspace witness is an unambiguous witness at the bound `log₂ n`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ UL enc) :
    A ∈ USPACE enc Nat.log2 :=
  UL_eq_USPACE ▸ h

/-- An unambiguous witness at the bound `log₂ n` is an `NL` witness, through `NSPACE(log₂ n)`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ USPACE enc Nat.log2) :
    A ∈ NL enc :=
  NL_eq_NSPACE ▸ USPACE_subset_NSPACE h

end CslibFrontierTests.Space.Unambiguous

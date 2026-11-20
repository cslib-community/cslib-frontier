/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting
import Mathlib.Tactic.FinCases

/-! # Native unambiguous logarithmic space

Check UL membership for a machine that accepts according to the encoded input bit, and
apply the forgetful inclusion to obtain NL membership.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LogSpace.Counting

open Turing MultiTapeCTM
open Cslib.Complexity Turing.MultiTapeTM

private def readBit : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ bit _ _ := [
    .step { inputTape := 0, workTapes := Fin.elim0, output := some (bit.getD false), state := none }
      Empty.elim Empty.elim]

/-- A one-step native witness yields both UL and NL membership, with acceptance determined by
the actual encoded input bit. -/
example : ({true} : Set Bool) ∈ UL encBool ∧ ({true} : Set Bool) ∈ NL encBool := by
  have hUL : ({true} : Set Bool) ∈ UL encBool := by
    let f (b : Bool) : ℕ := if b then 1 else 0
    refine ⟨f, ⟨0, Unit, inferInstance, readBit, 0, ?_⟩, ?_, ?_⟩
    · intro a
      refine ⟨?_, 1, ?_, ?_⟩
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
  exact ⟨hUL, UL_subset_NL hUL⟩

end CslibFrontierTests.LogSpace.Counting

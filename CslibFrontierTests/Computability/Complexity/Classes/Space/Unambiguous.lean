/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.Space.Unambiguous
import Mathlib.Tactic.FinCases

/-! # Unambiguous space classes

The general class is used here through `Classes.Space.Unambiguous` alone, without the logspace
classes. A one-step counting machine that accepts according to the input bit is an unambiguous
decider within zero work space, a bound below the logarithm, and the forgetful inclusion makes
the same language a member of nondeterministic space at that bound.
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
private theorem singleton_true_mem_USPACE : ({true} : Set Bool) ∈ USPACE encBool fun _ => 0 := by
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

/-- Forgetting multiplicity, the same language is in nondeterministic space at the zero bound. -/
example : ({true} : Set Bool) ∈ NSPACE encBool fun _ => 0 :=
  USPACE_subset_NSPACE singleton_true_mem_USPACE

end CslibFrontierTests.Space.Unambiguous

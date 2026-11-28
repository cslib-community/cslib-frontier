/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.RelationProgram.DNF

set_option linter.privateModule false

open Cslib.RelationProgram

private def sample : Program 6 1 :=
  ![.test 0 true, .write 0 0 true, .conj 1 0, .disj 4 1, .conj 4 1, .write 0 0 false]

example : evaluate sample ⟨0, 0⟩ = false := by decide
example : evaluate sample ⟨1, 0⟩ = true := by decide
example : evaluate sample ⟨2, 0⟩ = false := by decide
example : evaluate sample ⟨2, 1⟩ = true := by decide
example : evaluate sample ⟨3, 0⟩ = true := by decide
example : evaluate sample ⟨4, 0⟩ = false := by decide
example : evaluate sample ⟨5, 1⟩ = false := by decide
example : facts 0 1 = [] := by decide

example : ∀ σ, (certificateMatrix sample ⟨3, 0⟩).eval σ = true :=
  (certificateMatrix_correct sample ⟨3, 0⟩).mpr
    ((evaluate_eq_true_iff sample ⟨3, 0⟩).mp (by decide))

/-- The self-dependent predicate has no finite universal certificate. -/
example :
    ¬ ∀ σ : Fin (6 * 2 ^ 1) → Bool, (certificateMatrix sample ⟨4, 0⟩).eval
      (fun v => if h : v < 6 * 2 ^ 1 then σ ⟨v, h⟩ else false) = true := by
  intro valid
  have derived := (certificateMatrix_finite_correct sample ⟨4, 0⟩).mp valid
  exact (by decide : evaluate sample ⟨4, 0⟩ ≠ true)
    ((evaluate_eq_true_iff sample ⟨4, 0⟩).mpr derived)

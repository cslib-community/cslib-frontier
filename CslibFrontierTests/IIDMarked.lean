/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Probability.IID.Marked
import Mathlib.Tactic.NormNum

/-! # Marked coin events -/

set_option linter.privateModule false

namespace CslibFrontierTests.IIDMarked

open Cslib.Probability.PMF

-- Positive instances: exact marked-coin probability and both Claim lower bounds.
example (μ : PMF Bool) :
    (iid μ 4).toOuterMeasure {v | v 0 = true ∧ ∀ i ∈ ({1, 2} : Finset (Fin 4)), v i = false} =
      μ true * μ false ^ 2 := by
  simpa using
    toOuterMeasure_iid_marked μ {1, 2} (by decide : (0 : Fin 4) ∉ ({1, 2} : Finset (Fin 4)))

example (μ : PMF Bool) (hμ : (μ true).toReal = (3 : ℝ)⁻¹) :
    Real.exp (-1) / 3 ≤
      ((iid μ 4).toOuterMeasure
        {v | v 0 = true ∧ ∀ i ∈ ({1, 2} : Finset (Fin 4)), v i = false}).toReal :=
  exp_neg_one_div_le_toOuterMeasure_iid_marked μ hμ ({1, 2} : Finset (Fin 4))
    (by
      have hcard : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
      norm_num [hcard])
    (by decide : (0 : Fin 4) ∉ ({1, 2} : Finset (Fin 4)))

example (μ : PMF Bool) (hμ : (μ true).toReal = (3 : ℝ)⁻¹) :
    1 / (2.72 * 3) ≤
      ((iid μ 4).toOuterMeasure
        {v | v 0 = true ∧ ∀ i ∈ ({1, 2} : Finset (Fin 4)), v i = false}).toReal :=
  one_div_le_toOuterMeasure_iid_marked μ hμ ({1, 2} : Finset (Fin 4))
    (by
      have hcard : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
      norm_num [hcard])
    (by decide : (0 : Fin 4) ∉ ({1, 2} : Finset (Fin 4)))

-- Edge case: empty `R` with `a = 1` (coin always marks).
example :
    1 / (2.72 * 1) ≤
      ((iid (PMF.pure true) 1).toOuterMeasure
        {v | v 0 = true ∧ ∀ i ∈ (∅ : Finset (Fin 1)), v i = false}).toReal :=
  one_div_le_toOuterMeasure_iid_marked (PMF.pure true) (a := 1) (by simp) (∅ : Finset (Fin 1))
    (by simp) (Finset.notMem_empty 0)

/-- The hypothesis `ν ∉ R` is needed: a marked index is not unmarked. -/
example (μ : PMF Bool) :
    (iid μ 1).toOuterMeasure {v | v 0 = true ∧ ∀ i ∈ ({0} : Finset (Fin 1)), v i = false} = 0 := by
  have : {v : Fin 1 → Bool | v 0 = true ∧ ∀ i ∈ ({0} : Finset (Fin 1)), v i = false} = ∅ := by
    ext v
    simp
  rw [this]
  simp

/-- The hypothesis `|R| + 1 ≤ a` is needed: at `a = 1` the coin always marks, so one index to
avoid already gives probability `0 < e⁻¹`. -/
example : (iid (PMF.pure true) 2).toOuterMeasure
    {v | v 0 = true ∧ ∀ i ∈ ({1} : Finset (Fin 2)), v i = false} = 0 := by
  rw [toOuterMeasure_iid_marked (PMF.pure true) {1} (by decide)]
  simp

end CslibFrontierTests.IIDMarked

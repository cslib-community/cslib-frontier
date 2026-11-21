/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, kernels of positive semidefinite matrix sums)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Kernels of positive semidefinite sums

For complex positive semidefinite matrices, the kernel of a nonnegative weighted
sum is the intersection of the kernels of its positive-weight terms.

## Main results

* `Matrix.mulVec_sum_smul_eq_zero_iff`: the finite weighted kernel criterion.
-/

public section

namespace Matrix

open Finset
open scoped ComplexOrder

/-- A vector lies in the kernel of a nonnegative weighted sum of positive semidefinite
matrices exactly when it lies in the kernel of every term with nonzero weight. -/
theorem mulVec_sum_smul_eq_zero_iff {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (w : κ → ℝ) (A : κ → Matrix ι ι ℂ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hA : ∀ k ∈ s, (A k).PosSemidef) (x : ι → ℂ) :
    (∑ k ∈ s, w k • A k) *ᵥ x = 0 ↔ ∀ k ∈ s, w k ≠ 0 → A k *ᵥ x = 0 := by
  constructor
  · intro h k hk hwk
    have hq := congrArg (fun v : ι → ℂ => star x ⬝ᵥ v) h
    simp only [sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, dotProduct_zero,
      Complex.real_smul] at hq
    have hnonneg (j : κ) (hj : j ∈ s) :
        (0 : ℂ) ≤ (w j : ℂ) * (star x ⬝ᵥ (A j *ᵥ x)) :=
      mul_nonneg (Complex.zero_le_real.mpr (hw j hj)) ((hA j hj).dotProduct_mulVec_nonneg x)
    have hz := (sum_eq_zero_iff_of_nonneg hnonneg).mp hq k hk
    exact (hA k hk).dotProduct_mulVec_zero_iff.mp
      ((mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hwk))
  · intro h
    rw [sum_mulVec]
    refine sum_eq_zero fun k hk => ?_
    rw [smul_mulVec]
    by_cases hwk : w k = 0
    · rw [hwk, zero_smul]
    · rw [h k hk hwk, smul_zero]

end Matrix

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Normed/Module/Normalize.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Normalization and common scaling of vectors

The norm ratios to a shared scale control the difference between scaling a vector
and normalizing it. The comparison includes zero vectors, whose normalization is zero.

## Main results

* `NormedSpace.norm_sub_normalize_le`: compare normalized images using the scaled original error.
* `NormedSpace.norm_sub_div_le_normalized_add`: bound the scaled error of a norm-preserving map
  using the normalized error and two norm-ratio deviations.
-/

public section

namespace NormedSpace

/-- Normalization maps the space into the closed unit ball. -/
theorem norm_normalize_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) : ‖NormedSpace.normalize v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [NormedSpace.norm_normalize hv]

private theorem norm_inv_smul_sub_normalize_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (u : E) :
    ‖c⁻¹ • u - NormedSpace.normalize u‖ ≤ |1 - ‖u‖ / c| := by
  have hscale : c⁻¹ • u = (‖u‖ / c) • NormedSpace.normalize u := by
    rw [div_eq_mul_inv, mul_comm, ← smul_smul, NormedSpace.norm_smul_normalize]
  have hrem : c⁻¹ • u - NormedSpace.normalize u = (‖u‖ / c - 1) • NormedSpace.normalize u := by
    rw [sub_smul, one_smul, hscale]
  rw [hrem, norm_smul, Real.norm_eq_abs, abs_sub_comm (‖u‖ / c)]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_normalize_le_one u)

/-- Normalizing both inputs costs at most one relative norm deviation beyond scaling the
original error by the first input's norm. -/
theorem norm_sub_normalize_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] E) (v u : E) :
    ‖f (NormedSpace.normalize v) - NormedSpace.normalize u‖ ≤
      ‖f v - u‖ / ‖v‖ + |‖u‖ / ‖v‖ - 1| := by
  let c := ‖v‖⁻¹
  have hdiff : f (NormedSpace.normalize v) - c • u = c • (f v - u) := by
    rw [NormedSpace.normalize, map_smul, smul_sub]
  have h := norm_sub_le (f (NormedSpace.normalize v) - c • u) (NormedSpace.normalize u - c • u)
  have hc : 0 ≤ c := inv_nonneg.mpr (norm_nonneg _)
  rw [sub_sub_sub_cancel_right, hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
    norm_sub_rev (NormedSpace.normalize u)] at h
  rw [div_eq_inv_mul ‖f v - u‖, abs_sub_comm (‖u‖ / ‖v‖)]
  exact h.trans (add_le_add le_rfl (norm_inv_smul_sub_normalize_le ‖v‖ u))

/-- Scaling both branches by a common positive reference norm costs at most the sum
of their two relative norm deviations compared to normalizing the branches individually. -/
theorem norm_sub_div_le_normalized_add {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E →L[ℝ] E) (hf : ∀ v, ‖f v‖ = ‖v‖)
    (v u : E) {c : ℝ} (hc : 0 ≤ c) :
    ‖f v - u‖ / c ≤ ‖f (NormedSpace.normalize v) - NormedSpace.normalize u‖ +
      |1 - ‖v‖ / c| + |1 - ‖u‖ / c| := by
  have hscale : ‖f v - u‖ / c = ‖f (c⁻¹ • v) - c⁻¹ • u‖ := by
    rw [map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hc),
      div_eq_inv_mul]
  rw [hscale]
  have h₁ := norm_sub_le (f (c⁻¹ • v) - f (NormedSpace.normalize v))
    (c⁻¹ • u - f (NormedSpace.normalize v))
  have h₂ := norm_sub_le (f (NormedSpace.normalize v) - NormedSpace.normalize u)
    (c⁻¹ • u - NormedSpace.normalize u)
  rw [sub_sub_sub_cancel_right, ← map_sub, hf, norm_sub_rev (c⁻¹ • u)] at h₁
  rw [sub_sub_sub_cancel_right] at h₂
  linarith only [h₁, h₂, norm_inv_smul_sub_normalize_le c v, norm_inv_smul_sub_normalize_le c u]

end NormedSpace

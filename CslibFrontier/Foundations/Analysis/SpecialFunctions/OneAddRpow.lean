/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, real powers)

public import CslibFrontier.Init
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Real powers of `1 ± t` and `a ± b`

Two-point inequalities compare `(1 + t) ^ p + (1 - t) ^ p` with powers of `1 ± ρ t`, and reduce
`|a + b| ^ p + |a - b| ^ p` to that form. This file gives the derivatives of `(1 + t) ^ p` and
`(1 - t) ^ p` on their natural domains, and rewrites `|a + b|` and `|a - b|` as `|a| ± |b|` when
`|b| ≤ |a|`.

## Main results

* `Real.hasDerivAt_one_add_rpow`, `Real.hasDerivAt_one_sub_rpow`: the derivatives of
  `(1 + t) ^ p` for `t > -1` and of `(1 - t) ^ p` for `t < 1`.
* `Real.abs_add_rpow_add_abs_sub_rpow`: for `|b| ≤ |a|`,
  `|a + b| ^ p + |a - b| ^ p = (|a| + |b|) ^ p + (|a| - |b|) ^ p`.
-/

public section

namespace Real

/-- For `t > -1`, the derivative of `(1 + t) ^ p` is `p (1 + t) ^ (p - 1)`. -/
theorem hasDerivAt_one_add_rpow (p : ℝ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun t : ℝ => (1 + t) ^ p) (p * (1 + t) ^ (p - 1)) t := by
  simpa using ((hasDerivAt_id t).const_add 1).rpow_const (p := p) (Or.inl (by
    simp only [id_eq]
    linarith))

/-- For `t < 1`, the derivative of `(1 - t) ^ p` is `-(p (1 - t) ^ (p - 1))`. -/
theorem hasDerivAt_one_sub_rpow (p : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t : ℝ => (1 - t) ^ p) (-(p * (1 - t) ^ (p - 1))) t := by
  simpa using ((hasDerivAt_id t).const_sub 1).rpow_const (p := p) (Or.inl (by
    simp only [id_eq]
    linarith))

/-- The absolute values of `a + b` and `a - b` are `|a| + |b|` and `|a| - |b|`, in some order,
when `|b| ≤ |a|`. -/
theorem abs_add_rpow_add_abs_sub_rpow {a b : ℝ} (h : |b| ≤ |a|) (p : ℝ) :
    |a + b| ^ p + |a - b| ^ p = (|a| + |b|) ^ p + (|a| - |b|) ^ p := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb] at h ⊢
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb] at h ⊢
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), add_comm]
    ring_nf
  · rw [abs_of_nonpos ha, abs_of_nonneg hb] at h ⊢
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), add_comm]
    ring_nf
  · rw [abs_of_nonpos ha, abs_of_nonpos hb] at h ⊢
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring_nf

end Real

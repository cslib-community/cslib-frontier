/-
Copyright (c) 2026 Serge Gaspers, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Serge Gaspers, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Trivariate Sheppard orthant formula and Gaussian reflection symmetry

For unit vectors `u, v, w` in a finite-dimensional real inner product space `E` and a standard
Gaussian vector `x ~ stdGaussian E`, the trivariate positive orthant probability is

`P(0 < ⟪u, x⟫ ∧ 0 < ⟪v, x⟫ ∧ 0 < ⟪w, x⟫)`
`= 1/2 - (arccos ⟪u, v⟫ + arccos ⟪u, w⟫ + arccos ⟪v, w⟫) / (4π)`.

The proof sums the open positive and closed negative orthants via the three-sign identity
`1[p ∧ q ∧ r] + 1[¬p ∧ ¬q ∧ ¬r] = 1 - (1[p ≠ q] + 1[p ≠ r] + 1[q ≠ r]) / 2` and integrates
using `ProbabilityTheory.measureReal_stdGaussian_zero_mem_uIoc_eq_arccos` and reflection symmetry
`x ↦ -x`.

Adapted from the MIT-licensed Lean 4 companion of [Gaspers2026]
(`doi:10.5281/zenodo.23883489`, module `CubicPathwidth.C3.Sheppard`), wired directly to the
library's bivariate Sheppard formula in
`CslibFrontier.Foundations.Probability.Gaussian.Sheppard`.

## Main results

* `Cslib.Circuits.Frontier.Switched.measure_neg_preimage_stdGaussian`: reflection invariance of
  `stdGaussian E`.
* `Cslib.Circuits.Frontier.Switched.stdGaussian_inner_ne_zero_ae`: a nonzero projection vanishes
  almost nowhere.
* `Cslib.Circuits.Frontier.Switched.stdGaussian_real_pos_orthant_three`: the trivariate orthant
  formula.

## References

* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Switched

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Reflection invariance of the standard Gaussian measure under `x ↦ -x`. -/
theorem measure_neg_preimage_stdGaussian {s : Set E} (hs : MeasurableSet s) :
    stdGaussian E (Neg.neg ⁻¹' s) = stdGaussian E s := by
  let f : E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.neg ℝ
  have h := stdGaussian_map (E := E) f
  have hm : Measurable f := f.continuous.measurable
  change stdGaussian E (f ⁻¹' s) = stdGaussian E s
  rw [← Measure.map_apply hm hs, h]

/-- Real-valued reflection invariance of `stdGaussian E`. -/
theorem measureReal_neg_preimage_stdGaussian {s : Set E} (hs : MeasurableSet s) :
    (stdGaussian E).real (Neg.neg ⁻¹' s) = (stdGaussian E).real s := by
  simp only [Measure.real, measure_neg_preimage_stdGaussian hs]

/-- Under `stdGaussian E`, a nonzero linear projection vanishes with probability zero. -/
theorem measure_stdGaussian_inner_eq_zero {u : E} (hu : u ≠ 0) :
    stdGaussian E {x | ⟪u, x⟫ = 0} = 0 := by
  simpa only [Real.volume_singleton, mul_zero, nonpos_iff_eq_zero, Set.mem_singleton_iff] using
    stdGaussian_inner_mem_le hu (measurableSet_singleton (0 : ℝ))

/-- Almost surely under `stdGaussian E`, `⟪u, x⟫ ≠ 0` for any nonzero `u`. -/
theorem stdGaussian_inner_ne_zero_ae {u : E} (hu : u ≠ 0) :
    ∀ᵐ x ∂stdGaussian E, ⟪u, x⟫ ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not] using measure_stdGaussian_inner_eq_zero hu

/-- Almost surely, `⟪u, x⟫ = 0` is impossible when `⟪u, u⟫ = 1`. -/
theorem stdGaussian_unit_inner_ne_zero_ae {u : E} (hu : ⟪u, u⟫ = 1) :
    ∀ᵐ x ∂stdGaussian E, ⟪u, x⟫ ≠ 0 :=
  stdGaussian_inner_ne_zero_ae fun h => by simp [h] at hu

/-- Under `stdGaussian E`, a unit vector projects to `gaussianReal 0 1`. -/
theorem stdGaussian_map_inner_unit {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun x => ⟪u, x⟫) = gaussianReal 0 1 := by
  have hn : ‖u‖₊ = 1 := NNReal.eq hu
  simp [stdGaussian_map_inner, hn]

/-- The covariance of two linear projections under `stdGaussian E` equals their inner product. -/
theorem cov_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u, x⟫, fun x => ⟪v, x⟫; stdGaussian E] = ⟪u, v⟫ := by
  rw [← covarianceBilin_apply_eq_cov (μ := stdGaussian E) IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  rfl

/-- Pairwise sign-disagreement probability for unit vectors, using the strict/non-strict sign
predicate `0 < ⟪u, x⟫`. -/
theorem measureReal_stdGaussian_sign_disagree {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian E).real {x | ¬(0 < ⟪u, x⟫ ↔ 0 < ⟪v, x⟫)} = arccos ⟪u, v⟫ / π := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have hae : ({x : E | ¬(0 < ⟪u, x⟫ ↔ 0 < ⟪v, x⟫)} : Set E) =ᵐ[stdGaussian E]
      {x : E | (0 : ℝ) ∈ Ι ⟪u, x⟫ ⟪v, x⟫} := by
    filter_upwards [stdGaussian_inner_ne_zero_ae hu0, stdGaussian_inner_ne_zero_ae hv0] with x hx hy
    simp only [Set.mem_uIoc]
    rcases lt_or_gt_of_ne hx with hxn | hxp <;> rcases lt_or_gt_of_ne hy with hyn | hyp
    · simp [hxn.not_gt, hyn.not_gt, hxn.not_ge, hyn.not_ge]
    · simp [hxn.not_gt, hyp, hxn, hyp.le]
    · simp [hxp, hyn.not_gt, hyn, hxp.le]
    · simp [hxp, hyp, hxp.not_gt, hyp.not_gt]
  rw [measureReal_congr hae, measureReal_stdGaussian_zero_mem_uIoc_eq_arccos hu hv]

/-- The three-sign algebraic identity. -/
private theorem three_sign_identity (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    (if p ∧ q ∧ r then (1 : ℝ) else 0) + (if ¬p ∧ ¬q ∧ ¬r then 1 else 0) =
      1 - ((if (p ↔ q) then 0 else 1) + (if (p ↔ r) then 0 else 1) +
        (if (q ↔ r) then 0 else 1)) / 2 := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr]

/-- **Trivariate Sheppard orthant formula.** For unit vectors `u, v, w : E`,
`P(0 < ⟪u, x⟫ ∧ 0 < ⟪v, x⟫ ∧ 0 < ⟪w, x⟫)` equals
`1/2 - (arccos ⟪u, v⟫ + arccos ⟪u, w⟫ + arccos ⟪v, w⟫) / (4π)`. -/
theorem stdGaussian_real_pos_orthant_three {u v w : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hw : ‖w‖ = 1) :
    (stdGaussian E).real {x | 0 < ⟪u, x⟫ ∧ 0 < ⟪v, x⟫ ∧ 0 < ⟪w, x⟫} =
      1 / 2 - (arccos ⟪u, v⟫ + arccos ⟪u, w⟫ + arccos ⟪v, w⟫) / (4 * π) := by
  classical
  set μ := stdGaussian E
  set A : Set E := {x | 0 < ⟪u, x⟫ ∧ 0 < ⟪v, x⟫ ∧ 0 < ⟪w, x⟫}
  set B : Set E := {x | ⟪u, x⟫ ≤ 0 ∧ ⟪v, x⟫ ≤ 0 ∧ ⟪w, x⟫ ≤ 0}
  let dSet (a b : E) : Set E := {x | ¬(0 < ⟪a, x⟫ ↔ 0 < ⟪b, x⟫)}
  have hpos (a : E) : Measurable fun x : E => 0 < ⟪a, x⟫ :=
    measurableSet_setOfPred.mp (measurableSet_lt measurable_const (by fun_prop))
  have hnpos (a : E) : MeasurableSet {x : E | ⟪a, x⟫ ≤ 0} :=
    measurableSet_le (by fun_prop) measurable_const
  have hAm : MeasurableSet A := measurableSet_setOfPred.mpr ((hpos u).and ((hpos v).and (hpos w)))
  have hBm : MeasurableSet B := (hnpos u).inter ((hnpos v).inter (hnpos w))
  have hdm (a b : E) : MeasurableSet (dSet a b) :=
    measurableSet_setOfPred.mpr ((hpos a).iff (hpos b)).not
  have hne {a : E} (ha : ‖a‖ = 1) : ∀ᵐ x ∂μ, ⟪a, x⟫ ≠ 0 :=
    stdGaussian_inner_ne_zero_ae (norm_ne_zero_iff.mp (by rw [ha]; exact one_ne_zero))
  have hB : μ.real B = μ.real A := by
    rw [← measureReal_neg_preimage_stdGaussian hBm]
    refine measureReal_congr ?_
    filter_upwards [hne hu, hne hv, hne hw] with x hx hy hz
    simp only [A, B, preimage_ofPred_eq, inner_neg_right, neg_nonpos]
    exact ⟨fun ⟨a, b, c⟩ => ⟨a.lt_of_ne' hx, b.lt_of_ne' hy, c.lt_of_ne' hz⟩,
      fun ⟨a, b, c⟩ => ⟨a.le, b.le, c.le⟩⟩
  have hid (x : E) : A.indicator 1 x + B.indicator 1 x = 1 - ((dSet u v).indicator 1 x +
      (dSet u w).indicator 1 x + (dSet v w).indicator 1 x) / (2 : ℝ) := by
    simpa only [indicator_apply, Pi.one_apply, A, B, dSet, mem_ofPred_eq, not_lt, ite_not]
      using three_sign_identity (0 < ⟪u, x⟫) (0 < ⟪v, x⟫) (0 < ⟪w, x⟫)
  have hI {S : Set E} (hS : MeasurableSet S) : Integrable (S.indicator (1 : E → ℝ)) μ :=
    (integrable_const 1).indicator hS
  have hi (a b : E) := hI (hdm a b)
  have hd {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : μ.real (dSet a b) = arccos ⟪a, b⟫ / π :=
    measureReal_stdGaussian_sign_disagree ha hb
  have hint := integral_congr_ae (μ := μ) (ae_of_all _ hid)
  rw [integral_add (hI hAm) (hI hBm),
    integral_sub (integrable_const 1) ((((hi u v).fun_add (hi u w)).fun_add (hi v w)).div_const 2),
    integral_div, integral_add ((hi u v).fun_add (hi u w)) (hi v w),
    integral_add (hi u v) (hi u w), integral_const, probReal_univ, one_smul,
    integral_indicator_one hAm,
    integral_indicator_one hBm, integral_indicator_one (hdm u v), integral_indicator_one (hdm u w),
    integral_indicator_one (hdm v w), hB, hd hu hv, hd hu hw, hd hv hw] at hint
  linear_combination (1 / 2 : ℝ) * hint

end Cslib.Circuits.Frontier.Switched

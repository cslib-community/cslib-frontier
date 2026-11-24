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
  have hle := stdGaussian_inner_mem_le hu (measurableSet_singleton (0 : ℝ))
  simp only [Real.volume_singleton, mul_zero, nonpos_iff_eq_zero] at hle
  exact hle

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
  rw [stdGaussian_map_inner]
  have hn : ‖u‖₊ = 1 := NNReal.eq hu
  simp only [hn, one_pow]

/-- The covariance of two linear projections under `stdGaussian E` equals their inner product. -/
theorem cov_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u, x⟫, fun x => ⟪v, x⟫; stdGaussian E] = ⟪u, v⟫ := by
  have h := covarianceBilin_apply_eq_cov (μ := stdGaussian E) IsGaussian.memLp_two_id u v
  rw [covarianceBilin_stdGaussian] at h
  exact h.symm

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
    · constructor <;> intro h
      · exact absurd ⟨fun h' => absurd h' hxn.not_gt, fun h' => absurd h' hyn.not_gt⟩ h
      · rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
    · exact iff_of_true (fun h => hxn.not_gt (h.mpr hyp)) (Or.inl ⟨hxn, hyp.le⟩)
    · exact iff_of_true (fun h => hyn.not_gt (h.mp hxp)) (Or.inr ⟨hyn, hxp.le⟩)
    · constructor <;> intro h
      · exact absurd ⟨fun _ => hyp, fun _ => hxp⟩ h
      · rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
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
  have hAm : MeasurableSet A := by
    simp only [A, Set.ofPred_and]
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      ((measurableSet_lt measurable_const (by fun_prop)).inter
        (measurableSet_lt measurable_const (by fun_prop)))
  have hBm : MeasurableSet B := by
    simp only [B, Set.ofPred_and]
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const))
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  have hB : μ.real B = μ.real A := by
    have h1 : B = Neg.neg ⁻¹' {x : E | 0 ≤ ⟪u, x⟫ ∧ 0 ≤ ⟪v, x⟫ ∧ 0 ≤ ⟪w, x⟫} := by
      ext x
      simp only [B, Set.mem_ofPred_eq, Set.mem_preimage, inner_neg_right, Left.nonneg_neg_iff]
    have hCm : MeasurableSet {x : E | 0 ≤ ⟪u, x⟫ ∧ 0 ≤ ⟪v, x⟫ ∧ 0 ≤ ⟪w, x⟫} := by
      simp only [Set.ofPred_and]
      exact (measurableSet_le measurable_const (by fun_prop)).inter
        ((measurableSet_le measurable_const (by fun_prop)).inter
          (measurableSet_le measurable_const (by fun_prop)))
    have h2 : {x : E | 0 ≤ ⟪u, x⟫ ∧ 0 ≤ ⟪v, x⟫ ∧ 0 ≤ ⟪w, x⟫} =ᵐ[μ] A := by
      filter_upwards [stdGaussian_inner_ne_zero_ae hu0, stdGaussian_inner_ne_zero_ae hv0,
        stdGaussian_inner_ne_zero_ae hw0] with x hx hy hz
      simp only [A, Set.mem_ofPred_eq, le_iff_lt_or_eq]
      constructor
      · rintro ⟨a | a, b | b, c | c⟩ <;> first
          | exact ⟨a, b, c⟩
          | exact absurd a.symm hx
          | exact absurd b.symm hy
          | exact absurd c.symm hz
      · rintro ⟨a, b, c⟩
        exact ⟨Or.inl a, Or.inl b, Or.inl c⟩
    rw [h1, measureReal_neg_preimage_stdGaussian hCm, measureReal_congr h2]
  let dSet (a b : E) : Set E := {x | ¬(0 < ⟪a, x⟫ ↔ 0 < ⟪b, x⟫)}
  have hd_eq : ∀ (a b : E) (x : E),
      (dSet a b).indicator (fun _ => (1 : ℝ)) x =
        if (0 < ⟪a, x⟫ ↔ 0 < ⟪b, x⟫) then 0 else 1 := fun a b x => by
    by_cases h : 0 < ⟪a, x⟫ ↔ 0 < ⟪b, x⟫ <;> simp [dSet, h]
  have hid : ∀ x : E,
      A.indicator (fun _ => (1 : ℝ)) x + B.indicator (fun _ => (1 : ℝ)) x =
        1 - ((dSet u v).indicator (fun _ => (1 : ℝ)) x +
          (dSet u w).indicator (fun _ => (1 : ℝ)) x +
          (dSet v w).indicator (fun _ => (1 : ℝ)) x) / 2 := fun x => by
    have h := three_sign_identity (0 < ⟪u, x⟫) (0 < ⟪v, x⟫) (0 < ⟪w, x⟫)
    rw [hd_eq u v x, hd_eq u w x, hd_eq v w x]
    simp only [not_lt] at h
    simpa only [Set.indicator_apply, A, B, Set.mem_ofPred_eq] using h
  have hdm (a b : E) : MeasurableSet (dSet a b) := by
    have heq : dSet a b = ({x : E | 0 < ⟪a, x⟫} ∩ {x : E | ⟪b, x⟫ ≤ 0}) ∪
        ({x : E | ⟪a, x⟫ ≤ 0} ∩ {x : E | 0 < ⟪b, x⟫}) := by
      ext x
      simp only [dSet, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, not_lt.symm]
      tauto
    rw [heq]
    exact ((measurableSet_lt measurable_const (by fun_prop)).inter
        (measurableSet_le (by fun_prop) measurable_const)).union
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_lt measurable_const (by fun_prop)))
  have hAi : Integrable (A.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hBi : Integrable (B.indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hBm
  have hDi (a b : E) : Integrable ((dSet a b).indicator fun _ => (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator (hdm a b)
  have hind (S : Set E) (hS : MeasurableSet S) :
      ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real S := by
    rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
  have hL : ∫ x, (A.indicator (fun _ => (1 : ℝ)) x + B.indicator (fun _ => (1 : ℝ)) x) ∂μ =
      μ.real A + μ.real B := by
    rw [integral_add hAi hBi, hind A hAm, hind B hBm]
  have hDsum : ∫ x, ((dSet u v).indicator (fun _ => (1 : ℝ)) x +
      (dSet u w).indicator (fun _ => (1 : ℝ)) x +
      (dSet v w).indicator (fun _ => (1 : ℝ)) x) ∂μ =
      μ.real (dSet u v) + μ.real (dSet u w) + μ.real (dSet v w) := by
    have h12 : Integrable (fun x => (dSet u v).indicator (fun _ => (1 : ℝ)) x +
        (dSet u w).indicator (fun _ => (1 : ℝ)) x) μ := (hDi u v).add (hDi u w)
    rw [integral_add h12 (hDi v w), integral_add (hDi u v) (hDi u w),
      hind _ (hdm u v), hind _ (hdm u w), hind _ (hdm v w)]
  have hDi_sum : Integrable (fun x =>
      ((dSet u v).indicator (fun _ => (1 : ℝ)) x +
        (dSet u w).indicator (fun _ => (1 : ℝ)) x +
        (dSet v w).indicator (fun _ => (1 : ℝ)) x) / 2) μ :=
    (((hDi u v).add (hDi u w)).add (hDi v w)).div_const 2
  have hR : ∫ x, (1 - ((dSet u v).indicator (fun _ => (1 : ℝ)) x +
      (dSet u w).indicator (fun _ => (1 : ℝ)) x +
      (dSet v w).indicator (fun _ => (1 : ℝ)) x) / 2) ∂μ =
      1 - (μ.real (dSet u v) + μ.real (dSet u w) + μ.real (dSet v w)) / 2 := by
    rw [integral_sub (integrable_const (1 : ℝ)) hDi_sum,
      integral_const, smul_eq_mul, mul_one, probReal_univ, integral_div, hDsum]
  have hint : ∫ x, (A.indicator (fun _ => (1 : ℝ)) x + B.indicator (fun _ => (1 : ℝ)) x) ∂μ =
      ∫ x, (1 - ((dSet u v).indicator (fun _ => (1 : ℝ)) x +
        (dSet u w).indicator (fun _ => (1 : ℝ)) x +
        (dSet v w).indicator (fun _ => (1 : ℝ)) x) / 2) ∂μ :=
    congrArg (fun f : E → ℝ => ∫ x, f x ∂μ) (funext hid)
  rw [hL, hR, hB] at hint
  have h1 : μ.real (dSet u v) = arccos ⟪u, v⟫ / π :=
    measureReal_stdGaussian_sign_disagree hu hv
  have h2 : μ.real (dSet u w) = arccos ⟪u, w⟫ / π :=
    measureReal_stdGaussian_sign_disagree hu hw
  have h3 : μ.real (dSet v w) = arccos ⟪v, w⟫ / π :=
    measureReal_stdGaussian_sign_disagree hv hw
  rw [h1, h2, h3] at hint
  linear_combination (1 / 2 : ℝ) * hint

end Cslib.Circuits.Frontier.Switched

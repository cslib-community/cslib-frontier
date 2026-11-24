/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.Submodular
public import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
public import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian comparison inequalities for submodular Boolean functions

This module proves two comparison inequalities for thresholded centered Gaussian vectors
evaluated on a submodular function `f : (ι → Bool) → ℝ`:

* **Covariance comparison** (`integral_threshold_le_of_cov_le`): for a submodular `f` and
  unit-norm row families `a : ι → κ₁ → ℝ`, `b : ι → κ₂ → ℝ` satisfying
  `∑ k, a i k * a j k ≤ ∑ k, b i k * b j k` for all `i ≠ j` (allowing singular covariance
  matrices), for every threshold `t : ℝ`,
  `∫ y, f (thresholdVec (fun i => ∑ k, b i k * y k) t) ∂piGauss κ₂ ≤`
  `∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂piGauss κ₁`.
* **Zero-threshold maximality** (`integral_threshold_le_zero`): for a symmetric submodular `f`
  and unit-norm row family `a : ι → κ → ℝ`, the expectation
  `t ↦ ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂piGauss κ` is even
  (`integral_threshold_neg`) and antitone on `[0, ∞)`
  (`integral_threshold_antitone_on_nonneg`), hence maximized at `t = 0`.

## Main definitions

* `Cslib.Circuits.Frontier.CrossingCover.piGauss`: product of i.i.d. standard real Gaussians.
* `Cslib.Circuits.Frontier.CrossingCover.thresholdVec`: coordinatewise `< t` thresholding.
* `Cslib.Circuits.Frontier.CrossingCover.multilinearExt`: multilinear extension on `ℝ^ι`.
* `Cslib.Circuits.Frontier.CrossingCover.smoothStep`: Gaussian-smoothed step `1 - Φ(u / δ)`.
* `Cslib.Circuits.Frontier.CrossingCover.smoothExt`: smoothed threshold extension.

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.integral_mul_gaussianReal`: 1D Stein's lemma for the
  standard real Gaussian.
* `Cslib.Circuits.Frontier.CrossingCover.integral_smoothExt_le_of_cov_le`: smooth comparison
  via Gaussian interpolation.
* `Cslib.Circuits.Frontier.CrossingCover.integral_threshold_le_of_cov_le`: Slepian/Kahane-type
  comparison for submodular functions of Gaussian threshold vectors.
* `Cslib.Circuits.Frontier.CrossingCover.integral_threshold_neg`: threshold symmetry.
* `Cslib.Circuits.Frontier.CrossingCover.integral_threshold_antitone_on_nonneg`: monotonicity on
  `[0, ∞)`.
* `Cslib.Circuits.Frontier.CrossingCover.integral_threshold_le_of_abs_le`: comparison by `|t|`.
* `Cslib.Circuits.Frontier.CrossingCover.integral_threshold_le_zero`: zero-threshold maximality.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.CrossingCover

open MeasureTheory ProbabilityTheory Real Function Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology

/-! ### Standard Gaussian product measure and Stein's lemma -/

section GaussianPi

/-- Product measure of i.i.d. standard real Gaussian coordinates `N(0, 1)` on `κ → ℝ`. -/
noncomputable abbrev piGauss (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi fun _ : κ => gaussianReal 0 1

private theorem continuous_stdGaussianPDF : Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]
  fun_prop

private theorem integrable_gaussianReal_iff_mul_pdf {g : ℝ → ℝ} :
    Integrable g (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul]

private theorem hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  rw [gaussianPDFReal_def]
  refine (((((hasDerivAt_id x).sub_const 0).pow 2).neg.div_const (2 * (1 : ℝ))).exp.const_mul
    (√(2 * π * (1 : ℝ≥0)))⁻¹).congr_deriv ?_
  simp only [id, sub_zero, Pi.neg_apply, Pi.pow_apply, NNReal.coe_one, mul_one]
  ring

/-- **Stein's lemma** (Gaussian integration by parts) for the standard real Gaussian `N(0, 1)`. -/
theorem integral_mul_gaussianReal {h h' : ℝ → ℝ}
    (hh : ∀ x, HasDerivAt h (h' x) x)
    (hhi : Integrable h (gaussianReal 0 1))
    (hxhi : Integrable (fun x => x * h x) (gaussianReal 0 1))
    (hh'i : Integrable h' (gaussianReal 0 1)) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, h' x ∂(gaussianReal 0 1) := by
  have h1 : Integrable (fun x => -(gaussianPDFReal 0 1 x * (x * h x))) volume :=
    (integrable_gaussianReal_iff_mul_pdf.mp hxhi).neg
  have h2 : Integrable (fun x => gaussianPDFReal 0 1 x * h' x) volume :=
    integrable_gaussianReal_iff_mul_pdf.mp hh'i
  have heq : ∀ x : ℝ, -x * gaussianPDFReal 0 1 x * h x + gaussianPDFReal 0 1 x * h' x =
      -(gaussianPDFReal 0 1 x * (x * h x)) + gaussianPDFReal 0 1 x * h' x := fun x => by ring
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hasDerivAt_gaussianPDFReal_std x).mul (hh x))
    ((h1.add h2).congr (ae_of_all _ fun x => (heq x).symm))
    (integrable_gaussianReal_iff_mul_pdf.mp hhi)
  rw [integral_congr_ae (ae_of_all _ heq)] at h0
  change ∫ x, (fun x => -(gaussianPDFReal 0 1 x * (x * h x))) x +
    (fun x => gaussianPDFReal 0 1 x * h' x) x = 0 at h0
  rw [integral_add h1 h2, integral_neg, neg_add_eq_zero] at h0
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simpa only [smul_eq_mul] using h0

/-- Bounded version of 1D Stein's lemma for `N(0, 1)`. -/
theorem integral_mul_gaussianReal_of_bounded {h h' : ℝ → ℝ}
    (hh : ∀ x, HasDerivAt h (h' x) x)
    (hh'_meas : AEStronglyMeasurable h' (gaussianReal 0 1))
    {C : ℝ} (hbd : ∀ x, |h x| ≤ C ∧ |h' x| ≤ C) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, h' x ∂(gaussianReal 0 1) := by
  have hh_cont : Continuous h := continuous_iff_continuousAt.mpr fun x => (hh x).continuousAt
  have hhi : Integrable h (gaussianReal 0 1) :=
    Integrable.of_bound hh_cont.aestronglyMeasurable C (ae_of_all _ fun x => (hbd x).1)
  have hxhi : Integrable (fun x => x * h x) (gaussianReal 0 1) := by
    have hnorm : Integrable (fun x : ℝ => C * |x|) (gaussianReal 0 1) :=
      (memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)).norm.const_mul C
    refine hnorm.mono' (continuous_id.mul hh_cont).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbd x).1 (abs_nonneg x)
  have hh'i : Integrable h' (gaussianReal 0 1) :=
    Integrable.of_bound hh'_meas C (ae_of_all _ fun x => (hbd x).2)
  exact integral_mul_gaussianReal hh hhi hxhi hh'i

/-- Replacing coordinate `k` of `piGauss κ` with an independent `N(0, 1)` preserves `piGauss κ`. -/
private theorem measurePreserving_update_piGauss {κ : Type*} [Fintype κ] [DecidableEq κ] (k : κ) :
    MeasurePreserving (fun p : (κ → ℝ) × ℝ => update p.1 k p.2)
      ((piGauss κ).prod (gaussianReal 0 1)) (piGauss κ) := by
  have hmeas : Measurable (fun p : (κ → ℝ) × ℝ => update p.1 k p.2) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j = k
    · subst hj
      simpa only [update_self] using measurable_snd
    · have : (fun p : (κ → ℝ) × ℝ => update p.1 k p.2 j) = fun p => p.1 j :=
        funext fun p => update_of_ne hj p.2 p.1
      rw [this]
      exact (measurable_pi_apply j).comp measurable_fst
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (κ → ℝ) × ℝ => update p.1 k p.2) ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (update s k Set.univ)) ×ˢ s k := by
    ext ⟨x, u⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h k⟩
      by_cases hj : j = k
      · subst hj; simp
      · simpa [hj] using h j
    · rintro ⟨hx, hu⟩ j
      by_cases hj : j = k
      · subst hj; simpa using hu
      · simpa [hj] using hx j
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hprod : ∏ j ∈ Finset.univ.erase k, gaussianReal 0 1 (update s k Set.univ j) =
      ∏ j ∈ Finset.univ.erase k, gaussianReal 0 1 (s j) :=
    Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hprod, update_self, measure_univ, one_mul, mul_comm]

/-- Combining independent standard Gaussian vectors via `Sum.elim` yields `piGauss (κ₁ ⊕ κ₂)`. -/
private theorem measurePreserving_sumElim_piGauss {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] :
    MeasurePreserving (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) => Sum.elim p.1 p.2)
      ((piGauss κ₁).prod (piGauss κ₂)) (piGauss (κ₁ ⊕ κ₂)) := by
  have hmeas : Measurable (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) => Sum.elim p.1 p.2) := by
    rw [measurable_pi_iff]
    intro j
    cases j with
    | inl k => exact (measurable_pi_apply k).comp measurable_fst
    | inr k => exact (measurable_pi_apply k).comp measurable_snd
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) => Sum.elim p.1 p.2) ⁻¹' Set.pi Set.univ s =
      (Set.pi Set.univ (fun k => s (Sum.inl k))) ×ˢ
        (Set.pi Set.univ (fun k => s (Sum.inr k))) := by
    ext ⟨x, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
      Sum.forall, Sum.elim_inl, Sum.elim_inr]
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fintype.prod_sum_type]

/-- Every coordinate projection `x ↦ x k` is integrable under `piGauss κ`. -/
private theorem integrable_coord_piGauss {κ : Type*} [Fintype κ] (k : κ) :
    Integrable (fun x : κ → ℝ => x k) (piGauss κ) := by
  classical
  have heq : (fun x : κ → ℝ => x k) =
      fun x => (fun j => if j = k then (1 : ℝ) else 0) ⬝ᵥ x := by
    ext x; simp [dotProduct]
  rw [heq]
  exact integrable_dotProduct_pi_gaussianReal _

/-- Single-coordinate Stein's lemma on `piGauss κ`. -/
private theorem integral_coord_mul_piGauss {κ : Type*} [Fintype κ] [DecidableEq κ] (k : κ)
    {h h' : (κ → ℝ) → ℝ}
    (hh_cont : Continuous h) (hh'_cont : Continuous h')
    (hh : ∀ x u, HasDerivAt (fun t => h (update x k t)) (h' (update x k u)) u)
    {C : ℝ} (hbd : ∀ x, |h x| ≤ C ∧ |h' x| ≤ C) :
    ∫ x, x k * h x ∂(piGauss κ) = ∫ x, h' x ∂(piGauss κ) := by
  have hmp := measurePreserving_update_piGauss k
  have hupd_cont : Continuous (fun p : (κ → ℝ) × ℝ => update p.1 k p.2) :=
    continuous_pi fun j => by
      by_cases hj : j = k
      · subst hj; simpa [update_self] using continuous_snd
      · have : (fun p : (κ → ℝ) × ℝ => update p.1 k p.2 j) = fun p => p.1 j :=
          funext fun p => update_of_ne hj p.2 p.1
        rw [this]; fun_prop
  have hleft_cont : Continuous (fun x : κ → ℝ => x k * h x) :=
    (continuous_apply k).mul hh_cont
  have hpiL_cont : Continuous (fun p : (κ → ℝ) × ℝ => p.2 * h (update p.1 k p.2)) :=
    continuous_snd.mul (hh_cont.comp hupd_cont)
  have hpiL : Integrable (fun p : (κ → ℝ) × ℝ => p.2 * h (update p.1 k p.2))
      ((piGauss κ).prod (gaussianReal 0 1)) := by
    have hdom : Integrable (fun p : (κ → ℝ) × ℝ => C * |p.2|)
        ((piGauss κ).prod (gaussianReal 0 1)) :=
      ((memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)).norm.comp_snd _).const_mul C
    refine hdom.mono' hpiL_cont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbd _).1 (abs_nonneg p.2)
  have hpiR : Integrable (fun p : (κ → ℝ) × ℝ => h' (update p.1 k p.2))
      ((piGauss κ).prod (gaussianReal 0 1)) :=
    Integrable.of_bound (hh'_cont.comp hupd_cont).aestronglyMeasurable C
      (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using (hbd _).2)
  have h1 : ∫ x, x k * h x ∂(piGauss κ) =
      ∫ p, p.2 * h (update p.1 k p.2) ∂((piGauss κ).prod (gaussianReal 0 1)) := by
    conv_lhs => rw [← hmp.map_eq]
    rw [integral_map hmp.measurable.aemeasurable (by
      rw [hmp.map_eq]; exact hleft_cont.aestronglyMeasurable)]
    simp only [update_self]
  have h2 : ∫ x, h' x ∂(piGauss κ) =
      ∫ p, h' (update p.1 k p.2) ∂((piGauss κ).prod (gaussianReal 0 1)) := by
    conv_lhs => rw [← hmp.map_eq]
    rw [integral_map hmp.measurable.aemeasurable (by
      rw [hmp.map_eq]; exact hh'_cont.aestronglyMeasurable)]
  rw [h1, integral_prod _ hpiL, h2, integral_prod _ hpiR]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hx_cont : Continuous (fun u : ℝ => update x k u) :=
    hupd_cont.comp (continuous_const.prodMk continuous_id)
  exact integral_mul_gaussianReal_of_bounded (hh x)
    (hh'_cont.comp hx_cont).aestronglyMeasurable (fun u => hbd (update x k u))

/-- For a unit vector `v : κ → ℝ`, `‖WithLp.toLp 2 v‖ = 1`. -/
private theorem toLp_norm_eq_one {κ : Type*} [Fintype κ] {v : κ → ℝ}
    (hv : ∑ k, v k ^ 2 = 1) : ‖WithLp.toLp 2 v‖ = 1 := by
  have hsq : ‖WithLp.toLp 2 v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Real.norm_eq_abs, sq_abs] using hv
  nlinarith [norm_nonneg (WithLp.toLp 2 v)]

/-- For a unit-norm vector `v : κ → ℝ`, the hyperplane `{x | ∑ k, v k * x k = t}` has `piGauss`
measure zero. -/
private theorem piGauss_dotProduct_eq_zero {κ : Type*} [Fintype κ] (v : κ → ℝ)
    (hv : ∑ k, v k ^ 2 = 1) (t : ℝ) :
    piGauss κ {x : κ → ℝ | ∑ k, v k * x k = t} = 0 := by
  have hnn : ‖WithLp.toLp 2 v‖₊ ^ 2 = 1 := by
    ext
    simp [toLp_norm_eq_one hv]
  have hmap : (piGauss κ).map (v ⬝ᵥ ·) = gaussianReal 0 1 := by
    rw [pi_gaussianReal_map_dotProduct v]
    exact congrArg (gaussianReal 0) hnn
  have hset : {x : κ → ℝ | ∑ k, v k * x k = t} = (v ⬝ᵥ ·) ⁻¹' {t} := by
    ext x; simp [dotProduct]
  rw [hset, ← Measure.map_apply (by fun_prop) (MeasurableSet.singleton t), hmap]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact measure_singleton t

/-- Almost everywhere under `piGauss κ`, no linear form `∑ k, a i k * x k` hits `t`. -/
private theorem ae_piGauss_dotProduct_ne {ι κ : Type*} [Finite ι] [Fintype κ]
    (a : ι → κ → ℝ) (ha : ∀ i, ∑ k, a i k ^ 2 = 1) (t : ℝ) :
    ∀ᵐ x ∂(piGauss κ), ∀ i : ι, ∑ k, a i k * x k ≠ t := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simpa only [ne_eq, not_not] using piGauss_dotProduct_eq_zero (a i) (ha i) t

/-- Under `piGauss κ`, negation preserves the measure. -/
theorem measurePreserving_neg_piGauss {κ : Type*} [Fintype κ] :
    MeasurePreserving (fun x : κ → ℝ => -x) (piGauss κ) (piGauss κ) := by
  refine ⟨measurable_neg, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_neg (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : κ → ℝ => -x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun k => (fun t : ℝ => -t) ⁻¹' s k := by
    ext x; simp [Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  rw [← Measure.map_apply measurable_neg (hs k), hneg]

end GaussianPi

/-! ### Threshold vectors and the multilinear extension -/

section MultilinearExt

variable {ι : Type*}

/-- Coordinatewise threshold vector `fun i => decide (x i < t)`. -/
noncomputable def thresholdVec (x : ι → ℝ) (t : ℝ) : ι → Bool :=
  open Classical in
  fun i => decide (x i < t)

@[simp]
theorem thresholdVec_apply_eq_true (x : ι → ℝ) (t : ℝ) (i : ι) :
    thresholdVec x t i = true ↔ x i < t := by
  classical simp [thresholdVec]

@[simp]
theorem thresholdVec_apply_eq_false (x : ι → ℝ) (t : ℝ) (i : ι) :
    thresholdVec x t i = false ↔ t ≤ x i := by
  classical simp [thresholdVec, not_lt]

theorem thresholdVec_neg {x : ι → ℝ} {t : ℝ} (hne : ∀ i, x i ≠ t) :
    thresholdVec (-x) (-t) = notVec (thresholdVec x t) := by
  ext i
  cases h : thresholdVec x t i
  · have hge : t ≤ x i := (thresholdVec_apply_eq_false x t i).mp h
    have hgt : t < x i := lt_of_le_of_ne hge (hne i).symm
    rw [notVec_apply, h, Bool.not_false]
    exact (thresholdVec_apply_eq_true (-x) (-t) i).mpr (by simp [hgt])
  · have hlt : x i < t := (thresholdVec_apply_eq_true x t i).mp h
    rw [notVec_apply, h, Bool.not_true]
    exact (thresholdVec_apply_eq_false (-x) (-t) i).mpr (by simp [hlt.le])

/-- Thresholding a measurable family of real-valued vectors produces a measurable Boolean vector. -/
theorem measurable_thresholdVec {α : Type*} [MeasurableSpace α]
    {g : α → ι → ℝ} (hg : Measurable g) (t : α → ℝ) (ht : Measurable t) :
    Measurable (fun a => thresholdVec (g a) (t a)) := by
  rw [measurable_pi_iff]
  intro i
  have hset : MeasurableSet {a | g a i < t a} :=
    measurableSet_lt ((measurable_pi_apply i).comp hg) ht
  classical
  have heq : (fun a => thresholdVec (g a) (t a) i) =
      fun a => if g a i < t a then true else false := by
    ext a
    by_cases h : g a i < t a <;> simp [thresholdVec, h]
  rw [heq]
  exact Measurable.ite hset measurable_const measurable_const

/-- The multilinear extension of `f : (ι → Bool) → ℝ` to `ℝ^ι`. -/
def multilinearExt [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ b : ι → Bool, f b * ∏ i : ι, if b i then p i else 1 - p i

theorem multilinearExt_continuous [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) :
    Continuous (multilinearExt f) := by
  unfold multilinearExt
  refine continuous_finsetSum _ fun b _ => continuous_const.mul ?_
  refine continuous_finsetProd _ fun i _ => ?_
  cases b i
  · exact continuous_const.sub (continuous_apply i)
  · exact continuous_apply i

theorem multilinearExt_eq_of_bool [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (c : ι → Bool) :
    multilinearExt f (fun i => if c i then (1 : ℝ) else 0) = f c := by
  unfold multilinearExt
  rw [Finset.sum_eq_single c]
  · have hprod : ∏ i : ι, (if c i then if c i then (1 : ℝ) else 0
        else 1 - if c i then (1 : ℝ) else 0) = 1 :=
      Finset.prod_eq_one fun i _ => by cases c i <;> simp
    rw [hprod, mul_one]
  · intro b _ hbc
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra h; push Not at h; exact hbc (funext h)
    have hzero : (∏ j : ι, if b j then (if c j then (1 : ℝ) else 0)
        else 1 - (if c j then (1 : ℝ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by
        cases hb : b i <;> cases hc : c i <;> simp_all)
    rw [hzero, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ c) hc

theorem multilinearExt_weight_nonneg [Fintype ι] {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (b : ι → Bool) :
    0 ≤ ∏ i : ι, if b i then p i else 1 - p i :=
  Finset.prod_nonneg fun i _ => by
    cases b i <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_nonneg]
    · exact hp1 i
    · exact hp0 i

theorem abs_multilinearExt_le [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) {p : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    |multilinearExt f p| ≤ ∑ b : ι → Bool, |f b| := by
  calc |multilinearExt f p|
      ≤ ∑ b : ι → Bool, |f b * ∏ i : ι, if b i then p i else 1 - p i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : ι → Bool, |f b| := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_mul]
          have hw_nn : 0 ≤ ∏ i : ι, if b i then p i else 1 - p i :=
            multilinearExt_weight_nonneg hp0 hp1 b
          have hw_le : ∏ i : ι, (if b i then p i else 1 - p i) ≤ 1 := by
            have hstep : ∀ s : Finset ι,
                (0 ≤ ∏ i ∈ s, if b i then p i else 1 - p i) ∧
                  ∏ i ∈ s, (if b i then p i else 1 - p i) ≤ 1 := fun s =>
              Finset.prod_induction (fun i => if b i then p i else 1 - p i)
                (fun x => 0 ≤ x ∧ x ≤ 1)
                (fun _ _ ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ =>
                  ⟨mul_nonneg ha0 hb0,
                    (mul_le_mul_of_nonneg_right ha1 hb0).trans (by simpa using hb1)⟩)
                ⟨zero_le_one, le_rfl⟩
                (fun i _ => by
                  cases b i
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    exact ⟨sub_nonneg.mpr (hp1 i), by linarith [hp0 i]⟩
                  · simp only [↓reduceIte]
                    exact ⟨hp0 i, hp1 i⟩)
            exact (hstep Finset.univ).2
          rw [abs_of_nonneg hw_nn]
          exact mul_le_of_le_one_right (abs_nonneg _) hw_le

theorem multilinearExt_nonpos [Fintype ι] [DecidableEq ι] {f : (ι → Bool) → ℝ}
    (hf : ∀ b, f b ≤ 0) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    multilinearExt f p ≤ 0 :=
  Finset.sum_nonpos fun b _ =>
    mul_nonpos_of_nonpos_of_nonneg (hf b) (multilinearExt_weight_nonneg hp0 hp1 b)

/-- Product rule for `Finset.prod`. -/
private theorem hasDerivAt_finset_prod {α : Type*} [DecidableEq α] (s : Finset α)
    {g : α → ℝ → ℝ} {g' : α → ℝ} {t₀ : ℝ}
    (hg : ∀ i ∈ s, HasDerivAt (g i) (g' i) t₀) :
    HasDerivAt (fun t => ∏ i ∈ s, g i t)
      (∑ i ∈ s, g' i * ∏ j ∈ s.erase i, g j t₀) t₀ := by
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const t₀ (1 : ℝ)
  | @insert a s ha ih =>
    have hsub := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hprod := (hg a (Finset.mem_insert_self a s)).mul hsub
    refine (hprod.congr_of_eventuallyEq (Eventually.of_forall fun t => by
      simp [Finset.prod_insert ha])).congr_deriv ?_
    rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert (by simp [ha])]
    ring

/-- Bijective decomposition of sums over `ι → Bool` separating coordinate `i`. -/
private theorem sum_bool_fun_split [Fintype ι] [DecidableEq ι] (i : ι)
    (g : (ι → Bool) → ℝ) :
    ∑ b : ι → Bool, g b =
      ∑ b ∈ Finset.univ.filter (fun b : ι → Bool => b i = false),
        (g (update b i true) + g (update b i false)) := by
  rw [Finset.sum_add_distrib]
  have hsplit : ∑ b : ι → Bool, g b =
      (∑ b ∈ Finset.univ.filter (fun b : ι → Bool => b i = true), g b) +
        (∑ b ∈ Finset.univ.filter (fun b : ι → Bool => b i = false), g b) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : ι → Bool => b i = true) g]
    refine congrArg _ (Finset.sum_congr (by ext b; cases b i <;> simp) fun _ _ => rfl)
  rw [hsplit]
  congr 1
  · refine (Finset.sum_bij (fun b _ => update b i true) ?_ ?_ ?_ ?_).symm
    · intro b _; simp
    · intro b₁ hb₁ b₂ hb₂ heq
      ext j
      by_cases hj : j = i
      · subst hj
        exact ((Finset.mem_filter.mp hb₁).2).trans ((Finset.mem_filter.mp hb₂).2).symm
      · have := congrFun heq j
        simpa [update_of_ne hj] using this
    · intro b hb
      refine ⟨update b i false, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩, ?_⟩
      ext j
      by_cases hj : j = i
      · subst hj; simpa using (Finset.mem_filter.mp hb).2.symm
      · simp [update_of_ne hj]
    · intro b _; rfl
  · refine Finset.sum_congr rfl fun b hb => ?_
    have hbi : b i = false := (Finset.mem_filter.mp hb).2
    rw [show update b i false = b by ext j; by_cases hj : j = i <;> simp [hj, hbi]]

/-- For a function `h` independent of coordinate `i`, `multilinearExt h p` collapses coordinate `i`
from the product. -/
private theorem multilinearExt_indep_coord [Fintype ι] [DecidableEq ι] (i : ι)
    (h : (ι → Bool) → ℝ) (hh : ∀ b, h (update b i true) = h (update b i false))
    (p : ι → ℝ) :
    multilinearExt h p =
      ∑ b ∈ Finset.univ.filter (fun b : ι → Bool => b i = false),
        h b * ∏ j ∈ Finset.univ.erase i, (if b j then p j else 1 - p j) := by
  unfold multilinearExt
  rw [sum_bool_fun_split i]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbi : b i = false := (Finset.mem_filter.mp hb).2
  have hbf : update b i false = b := by
    ext j; by_cases hj : j = i <;> simp [hj, hbi]
  have hpt : ∏ j : ι, (if update b i true j then p j else 1 - p j) =
      p i * ∏ j ∈ Finset.univ.erase i, (if b j then p j else 1 - p j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
    simp only [↓reduceIte]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  have hpf : ∏ j : ι, (if update b i false j then p j else 1 - p j) =
      (1 - p i) * ∏ j ∈ Finset.univ.erase i, (if b j then p j else 1 - p j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hpt, hpf, hh b, hbf]
  ring

private theorem diffBool_indep_coord [DecidableEq ι] (f : (ι → Bool) → ℝ) (i : ι) (b : ι → Bool) :
    diffBool f i (update b i true) = diffBool f i (update b i false) := by
  simp [diffBool]

private theorem sum_signed_weight_eq_multilinearExt_diffBool [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (i : ι) (p : ι → ℝ) :
    ∑ b : ι → Bool, f b * (if b i then (1 : ℝ) else -1) *
        ∏ j ∈ Finset.univ.erase i, (if b j then p j else 1 - p j) =
      multilinearExt (diffBool f i) p := by
  rw [sum_bool_fun_split i, multilinearExt_indep_coord i _ (diffBool_indep_coord f i)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hpt : ∏ j ∈ Finset.univ.erase i, (if update b i true j then p j else 1 - p j) =
      ∏ j ∈ Finset.univ.erase i, (if b j then p j else 1 - p j) :=
    Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  have hpf : ∏ j ∈ Finset.univ.erase i, (if update b i false j then p j else 1 - p j) =
      ∏ j ∈ Finset.univ.erase i, (if b j then p j else 1 - p j) :=
    Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [update_self, update_self, hpt, hpf]
  simp only [↓reduceIte, Bool.false_eq_true, diffBool]
  ring

/-- Chain rule for `t ↦ multilinearExt f (p t)`. -/
theorem hasDerivAt_multilinearExt [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    {p : ℝ → ι → ℝ} {p' : ι → ℝ} {t₀ : ℝ}
    (hp : ∀ i : ι, HasDerivAt (fun t => p t i) (p' i) t₀) :
    HasDerivAt (fun t => multilinearExt f (p t))
      (∑ i : ι, p' i * multilinearExt (diffBool f i) (p t₀)) t₀ := by
  have hterm : ∀ b : ι → Bool,
      HasDerivAt (fun t => f b * ∏ i : ι, if b i then p t i else 1 - p t i)
        (f b * ∑ i : ι, (if b i then p' i else -p' i) *
          ∏ j ∈ Finset.univ.erase i, if b j then p t₀ j else 1 - p t₀ j) t₀ := by
    intro b
    refine HasDerivAt.const_mul (f b) ?_
    refine hasDerivAt_finset_prod Finset.univ fun i _ => ?_
    cases b i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h : HasDerivAt (fun t : ℝ => (1 : ℝ) - p t i) (0 - p' i) t₀ :=
        (hasDerivAt_const t₀ (1 : ℝ)).fun_sub (hp i)
      simpa only [zero_sub] using h
    · simpa only [↓reduceIte] using hp i
  refine (HasDerivAt.fun_sum fun b _ => hterm b).congr_deriv ?_
  calc ∑ b : ι → Bool, f b * ∑ i : ι, (if b i then p' i else -p' i) *
        ∏ j ∈ Finset.univ.erase i, (if b j then p t₀ j else 1 - p t₀ j)
      = ∑ b : ι → Bool, ∑ i : ι,
          p' i * (f b * (if b i then (1 : ℝ) else -1) *
            ∏ j ∈ Finset.univ.erase i, (if b j then p t₀ j else 1 - p t₀ j)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by cases b i <;> simp <;> ring
    _ = ∑ i : ι, p' i * ∑ b : ι → Bool,
          f b * (if b i then (1 : ℝ) else -1) *
            ∏ j ∈ Finset.univ.erase i, (if b j then p t₀ j else 1 - p t₀ j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i : ι, p' i * multilinearExt (diffBool f i) (p t₀) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sum_signed_weight_eq_multilinearExt_diffBool]

private theorem diffBool_self [DecidableEq ι] (f : (ι → Bool) → ℝ) (i : ι) (b : ι → Bool) :
    diffBool (diffBool f i) i b = 0 := by
  simp [diffBool]

private theorem IsSubmodularBool.diffBool_diffBool_nonpos [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) {i j : ι} (hij : i ≠ j) (b : ι → Bool) :
    diffBool (diffBool f i) j b ≤ 0 := by
  simp only [diffBool]
  have h := hf.mixedDiff_nonpos hij.symm b
  linarith

end MultilinearExt

/-! ### Gaussian-smoothed step function and smooth multilinear extension -/

section SmoothExt

/-- Smooth approximation `σ_δ(u) := P(Z ≤ -u / δ) = 1 - Φ(u / δ)` to the indicator `1_{u < 0}`. -/
noncomputable def smoothStep (δ u : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Iic (-u / δ))

/-- Derivative of `smoothStep δ`: `σ'_δ(u) = -(1 / δ) * φ(-u / δ)`. -/
noncomputable def smoothStepDeriv (δ u : ℝ) : ℝ :=
  -(1 / δ) * gaussianPDFReal 0 1 (-u / δ)

/-- Second derivative of `smoothStep δ`: `σ''_δ(u) = (u / δ ^ 3) * φ(-u / δ)`. -/
noncomputable def smoothStepDeriv₂ (δ u : ℝ) : ℝ :=
  (u / δ ^ 3) * gaussianPDFReal 0 1 (-u / δ)

theorem smoothStep_nonneg (δ u : ℝ) : 0 ≤ smoothStep δ u :=
  measureReal_nonneg

theorem smoothStep_le_one (δ u : ℝ) : smoothStep δ u ≤ 1 :=
  measureReal_le_one

private theorem hasDerivAt_gaussianCDF (y : ℝ) :
    HasDerivAt (fun z : ℝ => (gaussianReal 0 1).real (Set.Iic z))
      (gaussianPDFReal 0 1 y) y := by
  have hint : Integrable (gaussianPDFReal 0 1) volume := by
    have := (integrable_gaussianReal_iff_mul_pdf (g := fun _ => (1 : ℝ))).mp (integrable_const 1)
    simpa only [mul_one] using this
  have hdiff : ∀ z : ℝ, (gaussianReal 0 1).real (Set.Iic z) =
      (gaussianReal 0 1).real (Set.Iic 0) + ∫ x in (0 : ℝ)..z, gaussianPDFReal 0 1 x := by
    intro z
    have hval : ∀ w : ℝ, (gaussianReal 0 1).real (Set.Iic w) =
        ∫ x in Set.Iic w, gaussianPDFReal 0 1 x := fun w => by
      rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
        ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
          fun _ _ => gaussianPDFReal_nonneg 0 1 _)]
    rw [hval z, hval 0]
    rcases le_total 0 z with hz | hz
    · rw [intervalIntegral.integral_of_le hz,
        ← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
          hint.integrableOn hint.integrableOn,
        Set.Iic_union_Ioc_eq_Iic hz]
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hz]
      have hu := setIntegral_union (Set.Iic_disjoint_Ioc (le_refl z)) measurableSet_Ioc
        (hint.integrableOn (s := Set.Iic z)) (hint.integrableOn (s := Set.Ioc z 0))
      rw [Set.Iic_union_Ioc_eq_Iic hz] at hu
      linarith
  have hd : HasDerivAt (fun z => (gaussianReal 0 1).real (Set.Iic 0) +
      ∫ x in (0 : ℝ)..z, gaussianPDFReal 0 1 x) (gaussianPDFReal 0 1 y) y := by
    have h1 := intervalIntegral.integral_hasDerivAt_right
      (continuous_stdGaussianPDF.intervalIntegrable 0 y)
      (continuous_stdGaussianPDF.stronglyMeasurableAtFilter volume (𝓝 y))
      continuous_stdGaussianPDF.continuousAt
    exact (h1.const_add ((gaussianReal 0 1).real (Set.Iic 0)))
  exact hd.congr_of_eventuallyEq (Eventually.of_forall hdiff)

theorem hasDerivAt_smoothStep {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    HasDerivAt (smoothStep δ) (smoothStepDeriv δ u) u := by
  have h1 : HasDerivAt (fun x : ℝ => -x / δ) (-(1 / δ)) u := by
    simpa [neg_div] using ((hasDerivAt_id u).neg.div_const δ)
  refine ((hasDerivAt_gaussianCDF (-u / δ)).comp u h1).congr_deriv ?_
  have _ := hδ
  simp only [smoothStepDeriv]
  ring

theorem hasDerivAt_smoothStepDeriv {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    HasDerivAt (smoothStepDeriv δ) (smoothStepDeriv₂ δ u) u := by
  have h1 : HasDerivAt (fun x : ℝ => -x / δ) (-(1 / δ)) u := by
    simpa [neg_div] using ((hasDerivAt_id u).neg.div_const δ)
  have h2 := ((hasDerivAt_gaussianPDFReal_std (-u / δ)).comp u h1).const_mul (-(1 / δ))
  refine h2.congr_deriv ?_
  simp only [smoothStepDeriv₂]
  have hδne : δ ≠ 0 := hδ.ne'
  field_simp

theorem continuous_smoothStep {δ : ℝ} (hδ : 0 < δ) : Continuous (smoothStep δ) :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_smoothStep hδ u).continuousAt

theorem continuous_smoothStepDeriv (δ : ℝ) : Continuous (smoothStepDeriv δ) := by
  unfold smoothStepDeriv
  exact continuous_const.mul (continuous_stdGaussianPDF.comp (continuous_neg.div_const δ))

theorem continuous_smoothStepDeriv₂ (δ : ℝ) : Continuous (smoothStepDeriv₂ δ) := by
  unfold smoothStepDeriv₂
  exact (continuous_id.div_const (δ ^ 3)).mul
    (continuous_stdGaussianPDF.comp (continuous_neg.div_const δ))

theorem smoothStepDeriv_nonpos {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    smoothStepDeriv δ u ≤ 0 := by
  unfold smoothStepDeriv
  have hpos : 0 ≤ 1 / δ := (one_div_pos.mpr hδ).le
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpos) (gaussianPDFReal_nonneg 0 1 _)

theorem abs_smoothStepDeriv_le {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    |smoothStepDeriv δ u| ≤ (δ * √(2 * π))⁻¹ := by
  rw [smoothStepDeriv, abs_mul, abs_neg, abs_of_pos (one_div_pos.mpr hδ),
    abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _)]
  have hpdf := gaussianPDFReal_le 0 1 (-u / δ)
  simp only [NNReal.coe_one, mul_one] at hpdf
  calc (1 / δ) * gaussianPDFReal 0 1 (-u / δ)
      ≤ (1 / δ) * (√(2 * π))⁻¹ :=
          mul_le_mul_of_nonneg_left hpdf (by positivity)
    _ = (δ * √(2 * π))⁻¹ := by rw [one_div, mul_inv_rev, mul_comm]

/-- Uniform bound `|s| * exp(-(s^2 / 2)) ≤ 1` for all `s : ℝ`. -/
private theorem abs_mul_exp_neg_sq_div_two_le_one (s : ℝ) :
    |s| * Real.exp (-(s ^ 2 / 2)) ≤ 1 := by
  have h1 : |s| ≤ 1 + s ^ 2 / 2 := by
    have hsq : 0 ≤ (|s| - 1) ^ 2 := sq_nonneg _
    nlinarith [sq_abs s]
  have h2 : |s| ≤ Real.exp (s ^ 2 / 2) :=
    h1.trans (by simpa [add_comm] using Real.add_one_le_exp (s ^ 2 / 2))
  calc |s| * Real.exp (-(s ^ 2 / 2))
      ≤ Real.exp (s ^ 2 / 2) * Real.exp (-(s ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem abs_smoothStepDeriv₂_le {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    |smoothStepDeriv₂ δ u| ≤ (δ ^ 2 * √(2 * π))⁻¹ := by
  unfold smoothStepDeriv₂
  rw [gaussianPDFReal_def]
  simp only [sub_zero, NNReal.coe_one, mul_one]
  set s := -u / δ
  have hδne : δ ≠ 0 := hδ.ne'
  have heq : (u / δ ^ 3) * ((√(2 * π))⁻¹ * Real.exp (-(s ^ 2) / 2)) =
      -((δ ^ 2 * √(2 * π))⁻¹ * (s * Real.exp (-(s ^ 2 / 2)))) := by
    simp only [s, neg_div]
    field_simp
  rw [heq, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (δ ^ 2 * √(2 * π))⁻¹),
    abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (by positivity) (abs_mul_exp_neg_sq_div_two_le_one s)

/-- Explicit polynomial rate of convergence of `smoothStep δ u` to `1_{u < 0}` for `u ≠ 0`. -/
theorem abs_smoothStep_sub_indicator_le {δ u : ℝ} (hδ : 0 < δ) (hu : u ≠ 0) :
    |smoothStep δ u - (if u < 0 then (1 : ℝ) else 0)| ≤ δ ^ 2 / u ^ 2 := by
  unfold smoothStep
  rcases lt_or_gt_of_ne hu with hlt | hgt
  · have hpos : 0 < -u / δ := div_pos (neg_pos.mpr hlt) hδ
    simp only [hlt, ↓reduceIte]
    have hle1 : (gaussianReal 0 1).real (Set.Iic (-u / δ)) ≤ 1 := measureReal_le_one
    rw [abs_of_nonpos (sub_nonpos.mpr hle1), neg_sub]
    have hcomp : 1 - (gaussianReal 0 1).real (Set.Iic (-u / δ)) =
        (gaussianReal 0 1).real (Set.Ioi (-u / δ)) := by
      rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    rw [hcomp]
    have hsub : Set.Ioi (-u / δ) ⊆ {x : ℝ | -u / δ ≤ |x|} := fun x hx =>
      le_trans (le_of_lt hx) (le_abs_self x)
    calc (gaussianReal 0 1).real (Set.Ioi (-u / δ))
        ≤ (gaussianReal 0 1).real {x : ℝ | -u / δ ≤ |x|} := measureReal_mono hsub
      _ ≤ (1 : ℝ≥0) / (-u / δ) ^ 2 := by
          refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
          simpa only [sub_zero] using gaussianReal_meas_ge_le 0 1 hpos
      _ = δ ^ 2 / u ^ 2 := by
          simp only [NNReal.coe_one]
          field_simp
  · have hpos : 0 < u / δ := div_pos hgt hδ
    have hnot : ¬ u < 0 := not_lt.mpr hgt.le
    simp only [hnot, ↓reduceIte, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsub : Set.Iic (-u / δ) ⊆ {x : ℝ | u / δ ≤ |x|} := fun x (hx : x ≤ -u / δ) => by
      have : u / δ ≤ -x := by linarith [neg_div δ u]
      exact this.trans (neg_le_abs x)
    calc (gaussianReal 0 1).real (Set.Iic (-u / δ))
        ≤ (gaussianReal 0 1).real {x : ℝ | u / δ ≤ |x|} := measureReal_mono hsub
      _ ≤ (1 : ℝ≥0) / (u / δ) ^ 2 := by
          refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
          simpa only [sub_zero] using gaussianReal_meas_ge_le 0 1 hpos
      _ = δ ^ 2 / u ^ 2 := by
          simp only [NNReal.coe_one]
          field_simp

theorem tendsto_smoothStep_atTop (u : ℝ) (hu : u ≠ 0) :
    Tendsto (fun n : ℕ => smoothStep (1 / ((n : ℝ) + 1)) u) atTop
      (nhds (if u < 0 then (1 : ℝ) else 0)) := by
  have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2 / u ^ 2) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (hinv.pow 2).div_const (u ^ 2)
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ht ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  rw [Real.dist_eq]
  have hb := abs_smoothStep_sub_indicator_le hδ hu
  have htn := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at htn
  exact hb.trans_lt htn

/-- Smoothed multilinear extension `smoothExt f δ t z := multilinearExt f (σ_δ(z_i - t))`. -/
noncomputable def smoothExt {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (δ t : ℝ) (z : ι → ℝ) : ℝ :=
  multilinearExt f (fun i => smoothStep δ (z i - t))

/-- First partial derivative of `smoothExt f δ t` in coordinate `i`. -/
private noncomputable def smoothExtDeriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (δ t : ℝ) (i : ι) (z : ι → ℝ) : ℝ :=
  smoothStepDeriv δ (z i - t) *
    multilinearExt (diffBool f i) (fun j => smoothStep δ (z j - t))

/-- Second partial derivative `∂_j ∂_i (smoothExt f δ t)` at `z`. -/
private noncomputable def smoothExtHess {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (δ t : ℝ) (i j : ι) (z : ι → ℝ) : ℝ :=
  if j = i then
    smoothStepDeriv₂ δ (z i - t) *
      multilinearExt (diffBool f i) (fun k => smoothStep δ (z k - t))
  else
    smoothStepDeriv δ (z i - t) * smoothStepDeriv δ (z j - t) *
      multilinearExt (diffBool (diffBool f i) j) (fun k => smoothStep δ (z k - t))

theorem smoothExt_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : Continuous (smoothExt f δ t) :=
  (multilinearExt_continuous f).comp
    (continuous_pi fun i => (continuous_smoothStep hδ).comp
      ((continuous_apply i).sub continuous_const))

private theorem smoothExtDeriv_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (i : ι) :
    Continuous (smoothExtDeriv f δ t i) :=
  ((continuous_smoothStepDeriv δ).comp ((continuous_apply i).sub continuous_const)).mul
    ((multilinearExt_continuous _).comp
      (continuous_pi fun j => (continuous_smoothStep hδ).comp
        ((continuous_apply j).sub continuous_const)))

private theorem smoothExtHess_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (i j : ι) :
    Continuous (smoothExtHess f δ t i j) := by
  unfold smoothExtHess
  split_ifs
  · exact ((continuous_smoothStepDeriv₂ δ).comp ((continuous_apply i).sub continuous_const)).mul
      ((multilinearExt_continuous _).comp
        (continuous_pi fun k => (continuous_smoothStep hδ).comp
          ((continuous_apply k).sub continuous_const)))
  · exact (((continuous_smoothStepDeriv δ).comp ((continuous_apply i).sub continuous_const)).mul
      ((continuous_smoothStepDeriv δ).comp ((continuous_apply j).sub continuous_const))).mul
      ((multilinearExt_continuous _).comp
        (continuous_pi fun k => (continuous_smoothStep hδ).comp
          ((continuous_apply k).sub continuous_const)))

theorem abs_smoothExt_le {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (δ t : ℝ) (z : ι → ℝ) :
    |smoothExt f δ t z| ≤ ∑ b : ι → Bool, |f b| :=
  abs_multilinearExt_le f (fun _ => smoothStep_nonneg _ _) (fun _ => smoothStep_le_one _ _)

private theorem abs_smoothExtDeriv_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (i : ι) (z : ι → ℝ) :
    |smoothExtDeriv f δ t i z| ≤
      (δ * √(2 * π))⁻¹ * ∑ b : ι → Bool, |diffBool f i b| := by
  unfold smoothExtDeriv
  rw [abs_mul]
  exact mul_le_mul (abs_smoothStepDeriv_le hδ _)
    (abs_multilinearExt_le _ (fun _ => smoothStep_nonneg _ _) (fun _ => smoothStep_le_one _ _))
    (abs_nonneg _) (by positivity)

private theorem exists_bound_smoothExtHess {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i j z, |smoothExtHess f δ t i j z| ≤ M := by
  let bound : ι → ι → ℝ := fun i j =>
    max ((δ ^ 2 * √(2 * π))⁻¹ * ∑ b, |diffBool f i b|)
      ((δ * √(2 * π))⁻¹ * (δ * √(2 * π))⁻¹ * ∑ b, |diffBool (diffBool f i) j b|)
  have hbn : ∀ i j, 0 ≤ bound i j := fun i j =>
    le_max_of_le_left (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  refine ⟨∑ i : ι, ∑ j : ι, bound i j,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hbn i j, fun i j z => ?_⟩
  have hsingle : |smoothExtHess f δ t i j z| ≤ bound i j := by
    unfold smoothExtHess
    split_ifs
    · refine le_max_of_le_left ?_
      rw [abs_mul]
      exact mul_le_mul (abs_smoothStepDeriv₂_le hδ _)
        (abs_multilinearExt_le _ (fun _ => smoothStep_nonneg _ _)
          (fun _ => smoothStep_le_one _ _))
        (abs_nonneg _) (by positivity)
    · refine le_max_of_le_right ?_
      rw [abs_mul, abs_mul]
      refine mul_le_mul (mul_le_mul (abs_smoothStepDeriv_le hδ _) (abs_smoothStepDeriv_le hδ _)
        (abs_nonneg _) (by positivity))
        (abs_multilinearExt_le _ (fun _ => smoothStep_nonneg _ _)
          (fun _ => smoothStep_le_one _ _))
        (abs_nonneg _) (by positivity)
  exact hsingle.trans ((Finset.single_le_sum (fun j' _ => hbn i j') (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ => hbn i' j')
      (Finset.mem_univ i)))

private theorem smoothExtHess_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) {δ : ℝ} (hδ : 0 < δ) (t : ℝ)
    {i j : ι} (hij : i ≠ j) (z : ι → ℝ) :
    smoothExtHess f δ t i j z ≤ 0 := by
  unfold smoothExtHess
  simp only [hij.symm, ↓reduceIte]
  have hprod : 0 ≤ smoothStepDeriv δ (z i - t) * smoothStepDeriv δ (z j - t) :=
    mul_nonneg_of_nonpos_of_nonpos (smoothStepDeriv_nonpos hδ _) (smoothStepDeriv_nonpos hδ _)
  have hml : multilinearExt (diffBool (diffBool f i) j)
      (fun k => smoothStep δ (z k - t)) ≤ 0 :=
    multilinearExt_nonpos (fun b => hf.diffBool_diffBool_nonpos hij b)
      (fun _ => smoothStep_nonneg _ _) (fun _ => smoothStep_le_one _ _)
  exact mul_nonpos_of_nonneg_of_nonpos hprod hml

private theorem hasDerivAt_smoothExt_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ)
    {z : ℝ → ι → ℝ} {z' : ι → ℝ} {r₀ : ℝ}
    (hz : ∀ i, HasDerivAt (fun r => z r i) (z' i) r₀) :
    HasDerivAt (fun r => smoothExt f δ t (z r))
      (∑ i : ι, z' i * smoothExtDeriv f δ t i (z r₀)) r₀ := by
  have hp : ∀ i : ι, HasDerivAt (fun r => smoothStep δ (z r i - t))
      (smoothStepDeriv δ (z r₀ i - t) * z' i) r₀ := fun i => by
    change HasDerivAt (smoothStep δ ∘ fun r => z r i - t) _ r₀
    exact (hasDerivAt_smoothStep hδ (z r₀ i - t)).comp r₀ ((hz i).sub_const t)
  refine (hasDerivAt_multilinearExt f hp).congr_deriv ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smoothExtDeriv]; ring

private theorem hasDerivAt_smoothExtDeriv_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (i : ι)
    {z : ℝ → ι → ℝ} {z' : ι → ℝ} {r₀ : ℝ}
    (hz : ∀ j, HasDerivAt (fun r => z r j) (z' j) r₀) :
    HasDerivAt (fun r => smoothExtDeriv f δ t i (z r))
      (∑ j : ι, z' j * smoothExtHess f δ t i j (z r₀)) r₀ := by
  have h1 : HasDerivAt (fun r => smoothStepDeriv δ (z r i - t))
      (smoothStepDeriv₂ δ (z r₀ i - t) * z' i) r₀ := by
    change HasDerivAt (smoothStepDeriv δ ∘ fun r => z r i - t) _ r₀
    exact (hasDerivAt_smoothStepDeriv hδ (z r₀ i - t)).comp r₀ ((hz i).sub_const t)
  have hp : ∀ j : ι, HasDerivAt (fun r => smoothStep δ (z r j - t))
      (smoothStepDeriv δ (z r₀ j - t) * z' j) r₀ := fun j => by
    change HasDerivAt (smoothStep δ ∘ fun r => z r j - t) _ r₀
    exact (hasDerivAt_smoothStep hδ (z r₀ j - t)).comp r₀ ((hz j).sub_const t)
  have h2 := hasDerivAt_multilinearExt (diffBool f i) hp
  refine (h1.mul h2).congr_deriv ?_
  have hself : multilinearExt (diffBool (diffBool f i) i)
      (fun k => smoothStep δ (z r₀ k - t)) = 0 := by
    simp [multilinearExt, diffBool_self]
  calc smoothStepDeriv₂ δ (z r₀ i - t) * z' i *
        multilinearExt (diffBool f i) (fun k => smoothStep δ (z r₀ k - t)) +
        smoothStepDeriv δ (z r₀ i - t) *
          ∑ j : ι, smoothStepDeriv δ (z r₀ j - t) * z' j *
            multilinearExt (diffBool (diffBool f i) j)
              (fun k => smoothStep δ (z r₀ k - t))
      = z' i * (smoothStepDeriv₂ δ (z r₀ i - t) *
          multilinearExt (diffBool f i) (fun k => smoothStep δ (z r₀ k - t))) +
        ∑ j ∈ Finset.univ.erase i,
          z' j * (smoothStepDeriv δ (z r₀ i - t) * smoothStepDeriv δ (z r₀ j - t) *
            multilinearExt (diffBool (diffBool f i) j)
              (fun k => smoothStep δ (z r₀ k - t))) := by
          rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hself]
          simp only [mul_zero, zero_add]
          congr 1
          · ring
          · refine Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j : ι, z' j * smoothExtHess f δ t i j (z r₀) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          congr 1
          · simp [smoothExtHess]
          · refine Finset.sum_congr rfl fun j hj => ?_
            simp [smoothExtHess, Finset.ne_of_mem_erase hj]

theorem tendsto_smoothExt_atTop {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ)
    (t : ℝ) {z : ι → ℝ} (hz : ∀ i : ι, z i ≠ t) :
    Tendsto (fun n : ℕ => smoothExt f (1 / ((n : ℝ) + 1)) t z) atTop
      (nhds (f (thresholdVec z t))) := by
  have hp : Tendsto (fun n : ℕ => fun i : ι => smoothStep (1 / ((n : ℝ) + 1)) (z i - t))
      atTop (nhds (fun i : ι => if z i - t < 0 then (1 : ℝ) else 0)) :=
    tendsto_pi_nhds.mpr fun i => tendsto_smoothStep_atTop (z i - t) (sub_ne_zero.mpr (hz i))
  have hval : (fun i : ι => if z i - t < 0 then (1 : ℝ) else 0) =
      fun i : ι => if thresholdVec z t i then (1 : ℝ) else 0 := by
    ext i
    by_cases h : z i < t
    · have ht : thresholdVec z t i = true := (thresholdVec_apply_eq_true z t i).mpr h
      simp [sub_lt_zero.mpr h, ht]
    · have hf : thresholdVec z t i = false :=
        (thresholdVec_apply_eq_false z t i).mpr (not_lt.mp h)
      have hsub : ¬ z i - t < 0 := fun hlt => h (sub_lt_zero.mp hlt)
      simp [hsub, hf]
  rw [← multilinearExt_eq_of_bool f (thresholdVec z t), ← hval]
  exact ((multilinearExt_continuous f).tendsto _).comp hp

end SmoothExt

/-! ### Slepian/Kahane covariance comparison for submodular functions -/

section CovarianceComparison

private noncomputable def interpVec {ι κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (a : ι → κ₁ → ℝ) (b : ι → κ₂ → ℝ) (r : ℝ)
    (p : (κ₁ → ℝ) × (κ₂ → ℝ)) (i : ι) : ℝ :=
  √(1 - r) * (∑ k : κ₁, a i k * p.1 k) + √r * (∑ l : κ₂, b i l * p.2 l)

private theorem continuous_interpVec {ι κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (a : ι → κ₁ → ℝ) (b : ι → κ₂ → ℝ) (r : ℝ) :
    Continuous (interpVec a b r) := by
  unfold interpVec
  exact continuous_pi fun i => by fun_prop

private theorem hasDerivAt_interpVec {ι κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (a : ι → κ₁ → ℝ) (b : ι → κ₂ → ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (p : (κ₁ → ℝ) × (κ₂ → ℝ)) (i : ι) :
    HasDerivAt (fun s => interpVec a b s p i)
      (-(2 * √(1 - r))⁻¹ * (∑ k : κ₁, a i k * p.1 k) +
        (2 * √r)⁻¹ * (∑ l : κ₂, b i l * p.2 l)) r := by
  have h1 : HasDerivAt (fun s => √(1 - s)) (-(2 * √(1 - r))⁻¹) r := by
    have hs : HasDerivAt (fun s : ℝ => 1 - s) (-1) r :=
      (hasDerivAt_id r).const_sub (1 : ℝ) |>.congr_deriv (by ring)
    refine ((Real.hasDerivAt_sqrt (sub_pos.mpr hr1).ne').comp r hs).congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun s => √s) (2 * √r)⁻¹ r := by
    simpa [one_div] using Real.hasDerivAt_sqrt hr0.ne'
  exact (h1.mul_const _).add (h2.mul_const _)

/-- Single-coordinate Stein identity for `smoothExtDeriv` composed with an affine map of
`piGauss κ`. -/
private theorem integral_piGauss_coord_mul_smoothExtDeriv
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : (ι → Bool) → ℝ) {δ : ℝ} (hδ : 0 < δ) (t c : ℝ)
    (a : ι → κ → ℝ) (shift : ι → ℝ) (i : ι) (k : κ) :
    ∫ x, x k * smoothExtDeriv f δ t i (fun j => c * (∑ m, a j m * x m) + shift j) ∂(piGauss κ) =
      ∫ x, (∑ j : ι, c * a j k * smoothExtHess f δ t i j
        (fun l => c * (∑ m, a l m * x m) + shift l)) ∂(piGauss κ) := by
  classical
  obtain ⟨Mh, _, hMh⟩ := exists_bound_smoothExtHess f hδ t
  let g : (κ → ℝ) → ℝ := fun x =>
    smoothExtDeriv f δ t i (fun j => c * (∑ m, a j m * x m) + shift j)
  let g' : (κ → ℝ) → ℝ := fun x =>
    ∑ j : ι, c * a j k * smoothExtHess f δ t i j (fun l => c * (∑ m, a l m * x m) + shift l)
  have hmap_cont : Continuous (fun x : κ → ℝ => fun j : ι =>
      c * (∑ m, a j m * x m) + shift j) :=
    continuous_pi fun j => by fun_prop
  have hg_cont : Continuous g := (smoothExtDeriv_continuous f hδ t i).comp hmap_cont
  have hg'_cont : Continuous g' :=
    continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((smoothExtHess_continuous f hδ t i j).comp hmap_cont)
  have hg_deriv : ∀ x u, HasDerivAt (fun s => g (update x k s)) (g' (update x k u)) u := by
    intro x u
    refine hasDerivAt_smoothExtDeriv_comp f hδ t i fun j => ?_
    have hsum : ∀ s : ℝ, ∑ m : κ, a j m * update x k s m =
        a j k * s + ∑ m ∈ Finset.univ.erase k, a j m * x m := by
      intro s
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), update_self]
      congr 1
      exact Finset.sum_congr rfl fun m hm => by rw [update_of_ne (Finset.ne_of_mem_erase hm)]
    have heq : (fun s => c * (∑ m : κ, a j m * update x k s m) + shift j) =
        fun s => c * (a j k * s + ∑ m ∈ Finset.univ.erase k, a j m * x m) + shift j :=
      funext fun s => by rw [hsum s]
    rw [heq]
    set rest := ∑ m ∈ Finset.univ.erase k, a j m * x m
    have hd : HasDerivAt (fun s : ℝ => c * (a j k * s + rest) + shift j)
        (c * (a j k * 1)) u :=
      (((hasDerivAt_id u).const_mul (a j k)).add_const rest |>.const_mul c).add_const (shift j)
    refine hd.congr_deriv ?_
    ring
  let M := (δ * √(2 * π))⁻¹ * ∑ b : ι → Bool, |diffBool f i b|
  let Cg : ℝ := max M (∑ j : ι, |c * a j k| * Mh)
  refine integral_coord_mul_piGauss k hg_cont hg'_cont hg_deriv (C := Cg) fun x => ⟨?_, ?_⟩
  · exact (abs_smoothExtDeriv_le f hδ t i _).trans (le_max_left _ _)
  · refine le_max_of_le_right ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMh i j _) (abs_nonneg _)

/-- Algebraic reindexing helper canceling `c` with `(2 * c)⁻¹` inside the Gaussian interpolation
derivative. -/
private theorem sum_stein_rearrange {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → κ → ℝ) (H : ι → ℝ) {c : ℝ} (hc : c ≠ 0) (i : ι) :
    (2 * c)⁻¹ * ∑ k : κ, a i k * (c * ∑ j : ι, a j k * H j) =
      2⁻¹ * ∑ j : ι, (∑ k : κ, a i k * a j k) * H j := by
  have hswap : ∑ k : κ, a i k * (c * ∑ j : ι, a j k * H j) =
      c * ∑ j : ι, (∑ k : κ, a i k * a j k) * H j := by
    calc ∑ k : κ, a i k * (c * ∑ j : ι, a j k * H j)
        = ∑ k : κ, ∑ j : ι, c * ((a i k * a j k) * H j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : ι, ∑ k : κ, c * ((a i k * a j k) * H j) := Finset.sum_comm
      _ = c * ∑ j : ι, (∑ k : κ, a i k * a j k) * H j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by
              rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hswap]
  field_simp

/-- **Smooth Gaussian comparison inequality**: for any submodular `f : (ι → Bool) → ℝ`, any
smoothing width `δ > 0`, threshold `t : ℝ`, and unit-norm row families `a, b` with
`a i ⬝ᵥ a j ≤ b i ⬝ᵥ b j` for all `i ≠ j`, the smoothed expectation under `b` is at most that
under `a`. -/
theorem integral_smoothExt_le_of_cov_le {ι κ₁ κ₂ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ₁] [Fintype κ₂]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f)
    (a : ι → κ₁ → ℝ) (b : ι → κ₂ → ℝ)
    (ha : ∀ i, ∑ k, a i k ^ 2 = 1) (hb : ∀ i, ∑ k, b i k ^ 2 = 1)
    (hcov : ∀ i j, i ≠ j → ∑ k, a i k * a j k ≤ ∑ k, b i k * b j k)
    {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ∫ y, smoothExt f δ t (fun i => ∑ k, b i k * y k) ∂(piGauss κ₂) ≤
      ∫ x, smoothExt f δ t (fun i => ∑ k, a i k * x k) ∂(piGauss κ₁) := by
  classical
  let μ := (piGauss κ₁).prod (piGauss κ₂)
  let F : ℝ → (κ₁ → ℝ) × (κ₂ → ℝ) → ℝ := fun r p => smoothExt f δ t (interpVec a b r p)
  let Φ : ℝ → ℝ := fun r => ∫ p, F r p ∂μ
  let Bf : ℝ := ∑ c : ι → Bool, |f c|
  have hF_bd : ∀ r p, |F r p| ≤ Bf := fun r p => abs_smoothExt_le f δ t _
  have hF_cont_p : ∀ r, Continuous (F r) := fun r =>
    (smoothExt_continuous f hδ t).comp (continuous_interpVec a b r)
  have hΦ_cont : Continuous Φ := by
    refine continuous_of_dominated
      (fun r => (hF_cont_p r).aestronglyMeasurable)
      (fun r => ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hF_bd r p)
      (integrable_const Bf)
      (ae_of_all _ fun p => ?_)
    exact (smoothExt_continuous f hδ t).comp
      (continuous_pi fun i => by unfold interpVec; fun_prop)
  have hderiv_nonpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ d : ℝ, HasDerivAt Φ d r ∧ d ≤ 0 := by
    intro r ⟨hr0, hr1⟩
    let ε := min r (1 - r) / 2
    have hε_pos : 0 < ε := by positivity
    let F' : ℝ → (κ₁ → ℝ) × (κ₂ → ℝ) → ℝ := fun s p =>
      ∑ i : ι, (-(2 * √(1 - s))⁻¹ * (∑ k : κ₁, a i k * p.1 k) +
          (2 * √s)⁻¹ * (∑ l : κ₂, b i l * p.2 l)) *
        smoothExtDeriv f δ t i (interpVec a b s p)
    have hF'_deriv : ∀ p s, s ∈ Metric.ball r ε → HasDerivAt (fun u => F u p) (F' s p) s := by
      intro p s hs
      have hdist : |s - r| < ε := by simpa [Real.dist_eq] using hs
      have hs0 : 0 < s := by
        have hlo := (abs_lt.mp hdist).1
        have : ε ≤ r / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        linarith
      have hs1 : s < 1 := by
        have hhi := (abs_lt.mp hdist).2
        have : ε ≤ (1 - r) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        linarith
      exact hasDerivAt_smoothExt_comp f hδ t (fun i => hasDerivAt_interpVec a b hs0 hs1 p i)
    let M : ι → ℝ := fun i => (δ * √(2 * π))⁻¹ * ∑ c : ι → Bool, |diffBool f i c|
    let c₀ : ℝ := max (2 * √((1 - r) / 2))⁻¹ (2 * √(r / 2))⁻¹
    let bound : (κ₁ → ℝ) × (κ₂ → ℝ) → ℝ := fun p =>
      ∑ i : ι, c₀ * ((∑ k : κ₁, |a i k| * |p.1 k|) + (∑ l : κ₂, |b i l| * |p.2 l|)) * M i
    have hbound_int : Integrable bound μ := by
      refine integrable_finsetSum _ fun i _ => ((Integrable.add ?_ ?_).const_mul c₀).mul_const _
      · exact integrable_finsetSum _ fun k _ =>
          ((integrable_coord_piGauss k).norm.comp_fst _).const_mul |a i k|
      · exact integrable_finsetSum _ fun l _ =>
          ((integrable_coord_piGauss l).norm.comp_snd _).const_mul |b i l|
    have hF'_meas : AEStronglyMeasurable (F' r) μ := by
      refine Continuous.aestronglyMeasurable ?_
      exact continuous_finsetSum _ fun i _ =>
        (by fun_prop : Continuous fun p : (κ₁ → ℝ) × (κ₂ → ℝ) =>
          -(2 * √(1 - r))⁻¹ * (∑ k : κ₁, a i k * p.1 k) +
            (2 * √r)⁻¹ * (∑ l : κ₂, b i l * p.2 l)).mul
          ((smoothExtDeriv_continuous f hδ t i).comp (continuous_interpVec a b r))
    have hF'_bd : ∀ s ∈ Metric.ball r ε, ∀ p, ‖F' s p‖ ≤ bound p := by
      intro s hs p
      have hdist : |s - r| < ε := by simpa [Real.dist_eq] using hs
      have hs_lo : r / 2 ≤ s := by
        have := (abs_lt.mp hdist).1
        have : ε ≤ r / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        linarith
      have h1s_lo : (1 - r) / 2 ≤ 1 - s := by
        have := (abs_lt.mp hdist).2
        have : ε ≤ (1 - r) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        linarith
      have hinv1 : (2 * √(1 - s))⁻¹ ≤ c₀ :=
        (inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1s_lo)
          (by norm_num))).trans (le_max_left _ _)
      have hinv2 : (2 * √s)⁻¹ ≤ c₀ :=
        (inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs_lo)
          (by norm_num))).trans (le_max_right _ _)
      have hc0_nn : 0 ≤ c₀ := le_trans (by positivity) (le_max_left _ _)
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      have hA : |-(2 * √(1 - s))⁻¹ * (∑ k : κ₁, a i k * p.1 k) +
          (2 * √s)⁻¹ * (∑ l : κ₂, b i l * p.2 l)| ≤
          c₀ * ((∑ k : κ₁, |a i k| * |p.1 k|) + (∑ l : κ₂, |b i l| * |p.2 l|)) := by
        calc |-(2 * √(1 - s))⁻¹ * (∑ k : κ₁, a i k * p.1 k) +
              (2 * √s)⁻¹ * (∑ l : κ₂, b i l * p.2 l)|
            ≤ |-(2 * √(1 - s))⁻¹ * (∑ k : κ₁, a i k * p.1 k)| +
              |(2 * √s)⁻¹ * (∑ l : κ₂, b i l * p.2 l)| := abs_add_le _ _
          _ ≤ c₀ * (∑ k : κ₁, |a i k| * |p.1 k|) + c₀ * (∑ l : κ₂, |b i l| * |p.2 l|) := by
                refine add_le_add ?_ ?_
                · rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
                  exact mul_le_mul hinv1
                    ((Finset.abs_sum_le_sum_abs _ _).trans
                      (Finset.sum_le_sum fun k _ => by rw [abs_mul]))
                    (abs_nonneg _) hc0_nn
                · rw [abs_mul, abs_of_nonneg (by positivity)]
                  exact mul_le_mul hinv2
                    ((Finset.abs_sum_le_sum_abs _ _).trans
                      (Finset.sum_le_sum fun l _ => by rw [abs_mul]))
                    (abs_nonneg _) hc0_nn
          _ = _ := by ring
      exact mul_le_mul hA (abs_smoothExtDeriv_le f hδ t i _) (abs_nonneg _)
        (mul_nonneg hc0_nn
          (add_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))
    have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (Metric.ball_mem_nhds r hε_pos)
      (Eventually.of_forall fun s => (hF_cont_p s).aestronglyMeasurable)
      (Integrable.of_bound (hF_cont_p r).aestronglyMeasurable Bf
        (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hF_bd r p))
      hF'_meas
      (ae_of_all _ fun p s hs => hF'_bd s hs p)
      hbound_int
      (ae_of_all _ fun p s hs => hF'_deriv p s hs)).2
    refine ⟨∫ p, F' r p ∂μ, hderiv, ?_⟩
    obtain ⟨Mh, _, hMh⟩ := exists_bound_smoothExtHess f hδ t
    have hD_int_x : ∀ (i : ι) (k : κ₁),
        Integrable (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) =>
          p.1 k * smoothExtDeriv f δ t i (interpVec a b r p)) μ := fun i k =>
      (((integrable_coord_piGauss k).norm.comp_fst _).const_mul (M i)).mono'
        (((continuous_apply k).comp continuous_fst).mul
          ((smoothExtDeriv_continuous f hδ t i).comp
            (continuous_interpVec a b r))).aestronglyMeasurable
        (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_mul, mul_comm (M i)]
          exact mul_le_mul_of_nonneg_left (abs_smoothExtDeriv_le f hδ t i _) (abs_nonneg _))
    have hD_int_y : ∀ (i : ι) (l : κ₂),
        Integrable (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) =>
          p.2 l * smoothExtDeriv f δ t i (interpVec a b r p)) μ := fun i l =>
      (((integrable_coord_piGauss l).norm.comp_snd _).const_mul (M i)).mono'
        (((continuous_apply l).comp continuous_snd).mul
          ((smoothExtDeriv_continuous f hδ t i).comp
            (continuous_interpVec a b r))).aestronglyMeasurable
        (ae_of_all _ fun p => by
          rw [Real.norm_eq_abs, abs_mul, mul_comm (M i)]
          exact mul_le_mul_of_nonneg_left (abs_smoothExtDeriv_le f hδ t i _) (abs_nonneg _))
    have hH_int : ∀ i j : ι,
        Integrable (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) =>
          smoothExtHess f δ t i j (interpVec a b r p)) μ := fun i j =>
      Integrable.of_bound
        ((smoothExtHess_continuous f hδ t i j).comp
          (continuous_interpVec a b r)).aestronglyMeasurable Mh
        (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hMh i j _)
    have hstein_x : ∀ (i : ι) (k : κ₁),
        ∫ p, p.1 k * smoothExtDeriv f δ t i (interpVec a b r p) ∂μ =
          √(1 - r) * ∑ j : ι, a j k *
            ∫ p, smoothExtHess f δ t i j (interpVec a b r p) ∂μ := by
      intro i k
      rw [integral_prod_symm _ (hD_int_x i k)]
      simp_rw [show ∀ y : κ₂ → ℝ,
          ∫ x, x k * smoothExtDeriv f δ t i (interpVec a b r (x, y)) ∂(piGauss κ₁) =
            ∫ x, (∑ j : ι, √(1 - r) * a j k *
              smoothExtHess f δ t i j (interpVec a b r (x, y))) ∂(piGauss κ₁) from fun y =>
          integral_piGauss_coord_mul_smoothExtDeriv f hδ t √(1 - r) a
            (fun j => √r * ∑ l, b j l * y l) i k]
      rw [← integral_prod_symm _ (integrable_finsetSum _ fun j _ => (hH_int i j).const_mul _),
        integral_finsetSum _ fun j _ => (hH_int i j).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]; ring
    have hstein_y : ∀ (i : ι) (l : κ₂),
        ∫ p, p.2 l * smoothExtDeriv f δ t i (interpVec a b r p) ∂μ =
          √r * ∑ j : ι, b j l *
            ∫ p, smoothExtHess f δ t i j (interpVec a b r p) ∂μ := by
      intro i l
      rw [integral_prod _ (hD_int_y i l)]
      have hinner_y : ∀ x : κ₁ → ℝ,
          ∫ y, y l * smoothExtDeriv f δ t i (interpVec a b r (x, y)) ∂(piGauss κ₂) =
            ∫ y, (∑ j : ι, √r * b j l *
              smoothExtHess f δ t i j (interpVec a b r (x, y))) ∂(piGauss κ₂) := fun x => by
        have h := integral_piGauss_coord_mul_smoothExtDeriv f hδ t √r b
          (fun j => √(1 - r) * ∑ k, a j k * x k) i l
        have hcomm : ∀ (y : κ₂ → ℝ),
            (fun j : ι => √r * ∑ m : κ₂, b j m * y m + √(1 - r) * ∑ k : κ₁, a j k * x k) =
              interpVec a b r (x, y) := fun y => funext fun j => add_comm _ _
        simpa only [hcomm] using h
      simp_rw [hinner_y]
      rw [← integral_prod _ (integrable_finsetSum _ fun j _ => (hH_int i j).const_mul _),
        integral_finsetSum _ fun j _ => (hH_int i j).const_mul _, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]; ring
    have hsr0 : √r ≠ 0 := (Real.sqrt_pos.mpr hr0).ne'
    have hsr1 : √(1 - r) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hr1)).ne'
    let H : ι → ι → ℝ := fun i j => ∫ p, smoothExtHess f δ t i j (interpVec a b r p) ∂μ
    have hsplit_F' : ∀ p, F' r p =
        ∑ i : ι, (-(2 * √(1 - r))⁻¹ * ∑ k : κ₁, a i k *
            (p.1 k * smoothExtDeriv f δ t i (interpVec a b r p)) +
          (2 * √r)⁻¹ * ∑ l : κ₂, b i l *
            (p.2 l * smoothExtDeriv f δ t i (interpVec a b r p))) := fun p =>
      Finset.sum_congr rfl fun i _ => by
        rw [add_mul, mul_assoc, mul_assoc, Finset.sum_mul, Finset.sum_mul]
        congr 1 <;> rw [Finset.mul_sum, Finset.mul_sum] <;>
          exact Finset.sum_congr rfl fun _ _ => by ring
    have hFormula : ∫ p, F' r p ∂μ =
        2⁻¹ * ∑ i : ι, ∑ j : ι,
          (∑ l : κ₂, b i l * b j l - ∑ k : κ₁, a i k * a j k) * H i j := by
      simp_rw [hsplit_F']
      have hint_i : ∀ i : ι, Integrable (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) =>
          -(2 * √(1 - r))⁻¹ * ∑ k : κ₁, a i k *
              (p.1 k * smoothExtDeriv f δ t i (interpVec a b r p)) +
            (2 * √r)⁻¹ * ∑ l : κ₂, b i l *
              (p.2 l * smoothExtDeriv f δ t i (interpVec a b r p))) μ := fun i =>
        ((integrable_finsetSum _ fun k _ => (hD_int_x i k).const_mul _).const_mul _).add
          ((integrable_finsetSum _ fun l _ => (hD_int_y i l).const_mul _).const_mul _)
      rw [integral_finsetSum Finset.univ (fun i _ => hint_i i)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_add
        ((integrable_finsetSum _ fun k _ => (hD_int_x i k).const_mul _).const_mul _)
        ((integrable_finsetSum _ fun l _ => (hD_int_y i l).const_mul _).const_mul _),
        integral_const_mul, integral_const_mul,
        integral_finsetSum _ fun k _ => (hD_int_x i k).const_mul _,
        integral_finsetSum _ fun l _ => (hD_int_y i l).const_mul _]
      simp_rw [integral_const_mul, hstein_x i, hstein_y i]
      have hx := sum_stein_rearrange a (H i) hsr1 i
      have hy := sum_stein_rearrange b (H i) hsr0 i
      change -(2 * √(1 - r))⁻¹ * _ + (2 * √r)⁻¹ * _ = _
      rw [neg_mul, hx, hy, ← mul_neg, ← mul_add, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hFormula]
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_)
    by_cases hij : i = j
    · subst hij
      have h1 : ∑ l : κ₂, b i l * b i l = 1 := by simpa [sq] using hb i
      have h2 : ∑ k : κ₁, a i k * a i k = 1 := by simpa [sq] using ha i
      rw [h1, h2, sub_self, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hcov i j hij))
        (integral_nonpos fun p => smoothExtHess_nonpos hf hδ t hij _)
  have hanti : AntitoneOn Φ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hΦ_cont.continuousOn
      (fun r hr => ?_) (fun r hr => ?_)
    · rw [interior_Icc] at hr
      exact (hderiv_nonpos r hr).choose_spec.1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hr
      obtain ⟨d, hd, hd0⟩ := hderiv_nonpos r hr
      rwa [hd.deriv]
  have hle : Φ 1 ≤ Φ 0 := hanti (by simp) (by simp) (by norm_num)
  have hΦ0 : Φ 0 = ∫ x, smoothExt f δ t (fun i => ∑ k, a i k * x k) ∂(piGauss κ₁) := by
    have heq : F 0 = fun p => smoothExt f δ t (fun i => ∑ k, a i k * p.1 k) := by
      ext p
      dsimp only [F]
      congr 1; ext i; simp [interpVec]
    change ∫ p, F 0 p ∂((piGauss κ₁).prod (piGauss κ₂)) = _
    rw [heq, integral_prod _ (Integrable.of_bound
      ((hF_cont_p 0).aestronglyMeasurable.congr (ae_of_all _ fun p => congrFun heq p))
      Bf (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using abs_smoothExt_le f δ t _))]
    simp [integral_const]
  have hΦ1 : Φ 1 = ∫ y, smoothExt f δ t (fun i => ∑ k, b i k * y k) ∂(piGauss κ₂) := by
    have heq : F 1 = fun p => smoothExt f δ t (fun i => ∑ l, b i l * p.2 l) := by
      ext p
      dsimp only [F]
      congr 1; ext i; simp [interpVec]
    change ∫ p, F 1 p ∂((piGauss κ₁).prod (piGauss κ₂)) = _
    rw [heq, integral_prod_symm _ (Integrable.of_bound
      ((hF_cont_p 1).aestronglyMeasurable.congr (ae_of_all _ fun p => congrFun heq p))
      Bf (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using abs_smoothExt_le f δ t _))]
    simp [integral_const]
  rwa [hΦ1, hΦ0] at hle

/-- **Slepian/Kahane covariance comparison for submodular functions.**
For a submodular function `f : (ι → Bool) → ℝ` and unit-norm row families `a : ι → κ₁ → ℝ` and
`b : ι → κ₂ → ℝ` satisfying `∑ k, a i k * a j k ≤ ∑ k, b i k * b j k` for all `i ≠ j` (with
no nonsingularity assumption on the Gram matrices), for every threshold `t : ℝ`,
`E[f (thresholdVec (b · ⬝ᵥ Y) t)] ≤ E[f (thresholdVec (a · ⬝ᵥ X) t)]`. -/
theorem integral_threshold_le_of_cov_le {ι κ₁ κ₂ : Type*} [Finite ι] [Fintype κ₁] [Fintype κ₂]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f)
    (a : ι → κ₁ → ℝ) (b : ι → κ₂ → ℝ)
    (ha : ∀ i, ∑ k, a i k ^ 2 = 1) (hb : ∀ i, ∑ k, b i k ^ 2 = 1)
    (hcov : ∀ i j, i ≠ j → ∑ k, a i k * a j k ≤ ∑ k, b i k * b j k)
    (t : ℝ) :
    ∫ y, f (thresholdVec (fun i => ∑ k, b i k * y k) t) ∂(piGauss κ₂) ≤
      ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂(piGauss κ₁) := by
  classical
  have := Fintype.ofFinite ι
  let Bf : ℝ := ∑ c : ι → Bool, |f c|
  have hlim_a : Tendsto (fun n : ℕ =>
      ∫ x, smoothExt f (1 / ((n : ℝ) + 1)) t (fun i => ∑ k, a i k * x k) ∂(piGauss κ₁))
      atTop (nhds (∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂(piGauss κ₁))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Bf) ?_ (integrable_const Bf) ?_ ?_
    · intro n
      exact ((smoothExt_continuous f (by positivity) t).comp
        (continuous_pi fun i => by fun_prop)).aestronglyMeasurable
    · intro n
      exact ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using abs_smoothExt_le f (1 / ((n : ℝ) + 1)) t _
    · filter_upwards [ae_piGauss_dotProduct_ne a ha t] with x hx
      exact tendsto_smoothExt_atTop f t hx
  have hlim_b : Tendsto (fun n : ℕ =>
      ∫ y, smoothExt f (1 / ((n : ℝ) + 1)) t (fun i => ∑ k, b i k * y k) ∂(piGauss κ₂))
      atTop (nhds (∫ y, f (thresholdVec (fun i => ∑ k, b i k * y k) t) ∂(piGauss κ₂))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Bf) ?_ (integrable_const Bf) ?_ ?_
    · intro n
      exact ((smoothExt_continuous f (by positivity) t).comp
        (continuous_pi fun i => by fun_prop)).aestronglyMeasurable
    · intro n
      exact ae_of_all _ fun y => by
        simpa [Real.norm_eq_abs] using abs_smoothExt_le f (1 / ((n : ℝ) + 1)) t _
    · filter_upwards [ae_piGauss_dotProduct_ne b hb t] with y hy
      exact tendsto_smoothExt_atTop f t hy
  exact le_of_tendsto_of_tendsto hlim_b hlim_a
    (Eventually.of_forall fun n =>
      integral_smoothExt_le_of_cov_le hf a b ha hb hcov (by positivity) t)

end CovarianceComparison

/-! ### Zero-threshold maximality for symmetric submodular functions -/

section ZeroThreshold

/-- Linear reflection across the line spanned by a unit vector `u`: `x ↦ 2 ⟪u, x⟫ u - x`.
It is an orthogonal involution fixing `u` and negating `uᗮ`. -/
private noncomputable def lineReflection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) (hu : ‖u‖ = 1) : E ≃ₗᵢ[ℝ] E where
  toFun x := (2 * ⟪u, x⟫) • u - x
  invFun x := (2 * ⟪u, x⟫) • u - x
  map_add' x y := by
    rw [inner_add_right, mul_add, add_smul]; abel
  map_smul' c x := by
    simp only [RingHom.id_apply, inner_smul_right, smul_sub, smul_smul]
    congr 1; ring_nf
  left_inv x := by
    dsimp only
    have huu : ⟪u, u⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have hinner : ⟪u, (2 * ⟪u, x⟫) • u - x⟫ = ⟪u, x⟫ := by
      rw [inner_sub_right, inner_smul_right, huu]
      ring
    rw [hinner]; abel
  right_inv x := by
    dsimp only
    have huu : ⟪u, u⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have hinner : ⟪u, (2 * ⟪u, x⟫) • u - x⟫ = ⟪u, x⟫ := by
      rw [inner_sub_right, inner_smul_right, huu]
      ring
    rw [hinner]; abel
  norm_map' x := by
    change ‖(2 * ⟪u, x⟫) • u - x‖ = ‖x‖
    have huu : ⟪u, u⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have hsq : ‖(2 * ⟪u, x⟫) • u - x‖ ^ 2 = ‖x‖ ^ 2 := by
      simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, conj_trivial, real_inner_comm x u, huu]
      ring
    nlinarith [norm_nonneg ((2 * ⟪u, x⟫) • u - x), norm_nonneg x]

private theorem inner_lineReflection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E} (hu : ‖u‖ = 1) (v x : E) :
    ⟪v, lineReflection u hu x⟫ = 2 * ⟪u, v⟫ * ⟪u, x⟫ - ⟪v, x⟫ := by
  simp only [lineReflection, LinearIsometryEquiv.coe_mk, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, inner_sub_right, inner_smul_right, real_inner_comm v u]
  ring

private theorem inner_lineReflection_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E} (hu : ‖u‖ = 1) (x : E) :
    ⟪u, lineReflection u hu x⟫ = ⟪u, x⟫ := by
  rw [inner_lineReflection hu u x, real_inner_self_eq_norm_sq, hu, one_pow]
  ring

/-- Joint window probability bound for two non-collinear unit vectors under `stdGaussian E`. -/
private theorem stdGaussian_two_window_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hcorr : |⟪u, v⟫| < 1)
    {a b : ℝ} (hab : a ≤ b) :
    (stdGaussian E).real {x | ⟪u, x⟫ ∈ Set.Ico a b ∧ ⟪v, x⟫ ∈ Set.Ico a b} ≤
      ((√(2 * π))⁻¹ * (√(2 * π * (1 - ⟪u, v⟫ ^ 2)))⁻¹) * (b - a) ^ 2 := by
  set c := ⟪u, v⟫
  set w : E := v - c • u
  have h1c : 0 < 1 - c ^ 2 := by nlinarith [sq_abs c, abs_nonneg c]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have huw : ⟪u, w⟫ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, huu, c]; ring
  have hwnorm : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [w, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial, huu, hvv, real_inner_comm v u, c]
    ring
  have hwnn : (‖w‖₊ ^ 2 : ℝ≥0) ≠ 0 := by
    intro h0
    have : ‖w‖ ^ 2 = 0 := by
      have := congrArg (fun r : ℝ≥0 => (r : ℝ)) h0
      simpa using this
    linarith
  have hunn : ‖u‖₊ ^ 2 = 1 := by ext; simp [hu]
  let S : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Ico a b ∧ c * p.1 + p.2 ∈ Set.Ico a b}
  have hS_meas : MeasurableSet S :=
    ((measurableSet_Ico.preimage measurable_fst).inter
      (measurableSet_Ico.preimage ((measurable_const.mul measurable_fst).add measurable_snd)))
  have hpre : {x : E | ⟪u, x⟫ ∈ Set.Ico a b ∧ ⟪v, x⟫ ∈ Set.Ico a b} =
      (fun x : E => (⟪u, x⟫, ⟪w, x⟫)) ⁻¹' S := by
    ext x
    have hvx : ⟪v, x⟫ = c * ⟪u, x⟫ + ⟪w, x⟫ := by
      simp only [w, inner_sub_left, inner_smul_left, conj_trivial]; ring
    simp [S, hvx]
  have hprod : (stdGaussian E).map (fun x : E => (⟪u, x⟫, ⟪w, x⟫)) =
      (gaussianReal 0 1).prod (gaussianReal 0 (‖w‖₊ ^ 2)) := by
    rw [stdGaussian_map_inner_prod huw]
    exact congrArg (fun ν => ν.prod (gaussianReal 0 (‖w‖₊ ^ 2)))
      (congrArg (gaussianReal 0) hunn)
  have hpair_meas : Measurable (fun x : E => (⟪u, x⟫, ⟪w, x⟫)) := by fun_prop
  have hval : stdGaussian E {x | ⟪u, x⟫ ∈ Set.Ico a b ∧ ⟪v, x⟫ ∈ Set.Ico a b} =
      ∫⁻ s, gaussianReal 0 (‖w‖₊ ^ 2) (Prod.mk s ⁻¹' S) ∂(gaussianReal 0 1) := by
    rw [hpre, ← Measure.map_apply hpair_meas hS_meas, hprod, Measure.prod_apply hS_meas]
  have hslice : ∀ s : ℝ, gaussianReal 0 (‖w‖₊ ^ 2) (Prod.mk s ⁻¹' S) ≤
      Set.indicator (Set.Ico a b)
        (fun _ => ENNReal.ofReal ((√(2 * π * (1 - c ^ 2)))⁻¹ * (b - a))) s := by
    intro s
    by_cases hs : s ∈ Set.Ico a b
    · rw [Set.indicator_of_mem hs]
      have hset : Prod.mk s ⁻¹' S = Set.Ico (a - c * s) (b - c * s) := by
        ext t
        change (s ∈ Set.Ico a b ∧ c * s + t ∈ Set.Ico a b) ↔ t ∈ Set.Ico (a - c * s) (b - c * s)
        simp only [hs, true_and, Set.mem_Ico]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [hset]
      refine (gaussianReal_le_ofReal_mul_volume 0 hwnn _).trans ?_
      rw [Real.volume_Ico, show (b - c * s) - (a - c * s) = b - a by ring,
        NNReal.coe_pow, coe_nnNorm, hwnorm,
        ← ENNReal.ofReal_mul (by positivity)]
    · rw [Set.indicator_of_notMem hs]
      have hset : Prod.mk s ⁻¹' S = ∅ := by
        ext t
        change (s ∈ Set.Ico a b ∧ c * s + t ∈ Set.Ico a b) ↔ False
        exact iff_false_intro fun h => hs h.1
      rw [hset, measure_empty]
  have hmeas_bound : stdGaussian E {x | ⟪u, x⟫ ∈ Set.Ico a b ∧ ⟪v, x⟫ ∈ Set.Ico a b} ≤
      ENNReal.ofReal (((√(2 * π))⁻¹ * (√(2 * π * (1 - c ^ 2)))⁻¹) * (b - a) ^ 2) := by
    rw [hval]
    calc ∫⁻ s, gaussianReal 0 (‖w‖₊ ^ 2) (Prod.mk s ⁻¹' S) ∂(gaussianReal 0 1)
        ≤ ∫⁻ s, Set.indicator (Set.Ico a b)
            (fun _ => ENNReal.ofReal ((√(2 * π * (1 - c ^ 2)))⁻¹ * (b - a))) s
            ∂(gaussianReal 0 1) := lintegral_mono hslice
      _ = ENNReal.ofReal ((√(2 * π * (1 - c ^ 2)))⁻¹ * (b - a)) *
            gaussianReal 0 1 (Set.Ico a b) := by
            rw [lintegral_indicator measurableSet_Ico, setLIntegral_const]
      _ ≤ ENNReal.ofReal ((√(2 * π * (1 - c ^ 2)))⁻¹ * (b - a)) *
            (ENNReal.ofReal (√(2 * π * (1 : ℝ≥0)))⁻¹ * volume (Set.Ico a b)) :=
            mul_le_mul_right (gaussianReal_le_ofReal_mul_volume 0 one_ne_zero _) _
      _ = ENNReal.ofReal (((√(2 * π))⁻¹ * (√(2 * π * (1 - c ^ 2)))⁻¹) * (b - a) ^ 2) := by
            rw [Real.volume_Ico, NNReal.coe_one, mul_one,
              ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hmeas_bound

/-- Key pointwise cancellation under `lineReflection`: for `⟪u i, x⟫ > 0` and strict
sub-unit correlations `⟪u i, u j⟫ < 1`, reflecting `x` across `u i` makes `diffBool f i` sum to
at most `0`. -/
private theorem diffBool_add_lineReflection_nonpos {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) (hsym : IsSymmetricBool f)
    (u : ι → E) (hu : ∀ i, ‖u i‖ = 1) (hcorr : ∀ i j, i ≠ j → ⟪u i, u j⟫ < 1)
    (i : ι) {x : E} (hxpos : 0 < ⟪u i, x⟫) :
    diffBool f i (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) +
      diffBool f i (thresholdVec (fun j => ⟪u j, lineReflection (u i) (hu i) x⟫)
        ⟪u i, lineReflection (u i) (hu i) x⟫) ≤ 0 := by
  set s := ⟪u i, x⟫
  set x' := lineReflection (u i) (hu i) x
  have hs' : ⟪u i, x'⟫ = s := inner_lineReflection_self (hu i) x
  rw [hs']
  set b := thresholdVec (fun j => ⟪u j, x⟫) s
  set b' := thresholdVec (fun j => ⟪u j, x'⟫) s
  have hle : update (notVec b) i false ≤ update b' i false := by
    intro j
    by_cases hji : j = i
    · subst hji; simp
    · simp only [update_of_ne hji, notVec_apply]
      cases hbj : b j
      · have hge : s ≤ ⟪u j, x⟫ := (thresholdVec_apply_eq_false _ s j).mp hbj
        have hlt_c : ⟪u i, u j⟫ < 1 := hcorr i j (Ne.symm hji)
        have hx'j : ⟪u j, x'⟫ = 2 * ⟪u i, u j⟫ * s - ⟪u j, x⟫ :=
          inner_lineReflection (hu i) (u j) x
        have hlt' : ⟪u j, x'⟫ < s := by nlinarith
        have hbt : b' j = true := (thresholdVec_apply_eq_true _ s j).mpr hlt'
        simp [hbt]
      · exact Bool.false_le _
  have hmono := hf.diffBool_antitone i hle
  have h1 : diffBool f i (update b' i false) = diffBool f i b' := by
    simp [diffBool]
  have h2 : diffBool f i (update (notVec b) i false) = diffBool f i (notVec b) := by
    simp [diffBool]
  rw [h1, h2, hsym.diffBool_notVec i b] at hmono
  linarith

/-- The integrated conditional derivative on `(a, b)` for `0 ≤ a ≤ b` is nonpositive. -/
private theorem integral_indicator_diffBool_nonpos {ι E : Type*} [Finite ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) (hsym : IsSymmetricBool f)
    (u : ι → E) (hu : ∀ i, ‖u i‖ = 1) (hcorr : ∀ i j, i ≠ j → ⟪u i, u j⟫ < 1)
    (i : ι) {a b : ℝ} (ha : 0 ≤ a) :
    ∫ x, (if ⟪u i, x⟫ ∈ Set.Ico a b then
      diffBool f i (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) else 0) ∂(stdGaussian E) ≤ 0 := by
  have := Fintype.ofFinite ι
  let g : E → ℝ := fun x =>
    if ⟪u i, x⟫ ∈ Set.Ioo a b then
      diffBool f i (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) else 0
  let Bf : ℝ := 2 * ∑ c : ι → Bool, |f c|
  have hbound : ∀ y : (ι → Bool), |diffBool f i y| ≤ Bf := fun y => by
    unfold diffBool
    calc |f (update y i true) - f (update y i false)|
        ≤ |f (update y i true)| + |f (update y i false)| := abs_sub _ _
      _ ≤ (∑ c : ι → Bool, |f c|) + (∑ c : ι → Bool, |f c|) :=
          add_le_add
            (Finset.single_le_sum (fun c _ => abs_nonneg (f c)) (Finset.mem_univ _))
            (Finset.single_le_sum (fun c _ => abs_nonneg (f c)) (Finset.mem_univ _))
      _ = Bf := by ring
  have hg_meas : Measurable g := by
    refine Measurable.ite
      (measurableSet_Ioo.preimage (by fun_prop)) ?_ measurable_const
    exact (Measurable.of_discrete (f := diffBool f i)).comp
      (measurable_thresholdVec (measurable_pi_iff.mpr fun j => by fun_prop)
        (fun x => ⟪u i, x⟫) (by fun_prop))
  have hg_int : Integrable g (stdGaussian E) :=
    Integrable.of_bound hg_meas.aestronglyMeasurable Bf
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        dsimp [g]
        split_ifs
        · exact hbound _
        · rw [abs_zero]
          exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  have hae : (fun x : E => if ⟪u i, x⟫ ∈ Set.Ico a b then
      diffBool f i (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) else 0) =ᵐ[stdGaussian E] g := by
    have hnull : stdGaussian E {x : E | ⟪u i, x⟫ = a} = 0 := by
      have hunn : ‖u i‖₊ ^ 2 = 1 := by ext; simp [hu i]
      have hset : {x : E | ⟪u i, x⟫ = a} = (fun x => ⟪u i, x⟫) ⁻¹' {a} := rfl
      rw [hset, ← Measure.map_apply (by fun_prop) (MeasurableSet.singleton a),
        stdGaussian_map_inner (u i)]
      have hgm : (gaussianReal 0 (‖u i‖₊ ^ 2)) {a} = (gaussianReal 0 1) {a} :=
        congrArg (fun ν : Measure ℝ => ν {a}) (congrArg (gaussianReal 0) hunn)
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact hgm.trans (measure_singleton a)
    have hne : ∀ᵐ x ∂(stdGaussian E), ⟪u i, x⟫ ≠ a := by
      rw [ae_iff]; simpa only [ne_eq, not_not] using hnull
    filter_upwards [hne] with x hx
    dsimp [g]
    by_cases hlt : ⟪u i, x⟫ ∈ Set.Ioo a b
    · have hco : ⟪u i, x⟫ ∈ Set.Ico a b := ⟨hlt.1.le, hlt.2⟩
      simp [hlt, hco]
    · have hco : ⟪u i, x⟫ ∉ Set.Ico a b := fun h => hlt ⟨lt_of_le_of_ne h.1 hx.symm, h.2⟩
      simp [hlt, hco]
  rw [integral_congr_ae hae]
  let R := lineReflection (u i) (hu i)
  have hR_map : (stdGaussian E).map R = stdGaussian E := stdGaussian_map R
  have hgR_eq : ∫ x, g (R x) ∂(stdGaussian E) = ∫ x, g x ∂(stdGaussian E) := by
    conv_rhs => rw [← hR_map]
    exact (integral_map R.continuous.measurable.aemeasurable
      (by rw [hR_map]; exact hg_meas.aestronglyMeasurable)).symm
  have hsum_nonpos : ∫ x, (g x + g (R x)) ∂(stdGaussian E) ≤ 0 := by
    refine integral_nonpos fun x => ?_
    have hRx : ⟪u i, R x⟫ = ⟪u i, x⟫ := inner_lineReflection_self (hu i) x
    by_cases h : ⟪u i, x⟫ ∈ Set.Ioo a b
    · have h' : ⟪u i, R x⟫ ∈ Set.Ioo a b := hRx ▸ h
      simp only [g, h, h', ↓reduceIte]
      exact diffBool_add_lineReflection_nonpos hf hsym u hu hcorr i (lt_of_le_of_lt ha h.1)
    · have h' : ⟪u i, R x⟫ ∉ Set.Ioo a b := hRx ▸ h
      simp only [g, h, h', ↓reduceIte, add_zero]
      exact le_rfl
  have hgR_int : Integrable (fun x => g (R x)) (stdGaussian E) :=
    Integrable.of_bound (hg_meas.comp R.continuous.measurable).aestronglyMeasurable Bf
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        dsimp [g]
        split_ifs
        · exact hbound _
        · rw [abs_zero]
          exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  rw [integral_add hg_int hgR_int, hgR_eq] at hsum_nonpos
  linarith

/-- Pointwise single-step increment inequality separating 0, 1, and ≥ 2 crossings in `[a, b)`. -/
private theorem threshold_step_pointwise_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (z : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    f (thresholdVec z b) - f (thresholdVec z a) ≤
      (∑ i : ι, if z i ∈ Set.Ico a b then diffBool f i (thresholdVec z (z i)) else 0) +
        (2 * ((Fintype.card ι : ℝ) + 1) * ∑ c : ι → Bool, |f c|) *
          ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
            if (z i ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 := by
  let S : Finset ι := Finset.univ.filter fun i => z i ∈ Set.Ico a b
  let B : ℝ := ∑ c : ι → Bool, |f c|
  have hB_nn : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hf_le : ∀ c : ι → Bool, |f c| ≤ B := fun c =>
    Finset.single_le_sum (fun d _ => abs_nonneg (f d)) (Finset.mem_univ c)
  have herr_nn : 0 ≤ ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
      if (z i ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  rcases Nat.lt_trichotomy S.card 1 with h0 | h1 | h2
  · have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
    have hnone : ∀ i : ι, z i ∉ Set.Ico a b := fun i hi =>
      Finset.notMem_empty i (hSe ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    have heq : thresholdVec z b = thresholdVec z a := by
      ext i
      rcases lt_or_ge (z i) a with hlt | hge
      · have h1 : thresholdVec z b i = true :=
          (thresholdVec_apply_eq_true z b i).mpr (hlt.trans_le hab)
        have h2 : thresholdVec z a i = true := (thresholdVec_apply_eq_true z a i).mpr hlt
        rw [h1, h2]
      · have hb : b ≤ z i := by
          by_contra hlt; exact hnone i ⟨hge, not_le.mp hlt⟩
        have h1 : thresholdVec z b i = false := (thresholdVec_apply_eq_false z b i).mpr hb
        have h2 : thresholdVec z a i = false := (thresholdVec_apply_eq_false z a i).mpr hge
        rw [h1, h2]
    rw [heq, sub_self]
    have hsum0 : ∑ i : ι, (if z i ∈ Set.Ico a b then diffBool f i (thresholdVec z (z i)) else 0) =
        0 := Finset.sum_eq_zero fun i _ => by simp [hnone i]
    rw [hsum0, zero_add]
    exact mul_nonneg (by positivity) herr_nn
  · obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
    have hi₀_mem : i₀ ∈ S := by rw [hi₀]; exact Finset.mem_singleton_self i₀
    have hmem : z i₀ ∈ Set.Ico a b := (Finset.mem_filter.mp hi₀_mem).2
    have hother : ∀ j : ι, j ≠ i₀ → z j ∉ Set.Ico a b := fun j hne hj =>
      hne (Finset.mem_singleton.mp (hi₀ ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩))
    have hsum : ∑ i : ι, (if z i ∈ Set.Ico a b then diffBool f i (thresholdVec z (z i)) else 0) =
        diffBool f i₀ (thresholdVec z (z i₀)) := by
      rw [Finset.sum_eq_single i₀]
      · simp [hmem]
      · intro j _ hne; simp [hother j hne]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    have hb_eq : thresholdVec z b = update (thresholdVec z (z i₀)) i₀ true := by
      ext j
      by_cases hj : j = i₀
      · subst hj
        rw [update_self]
        exact (thresholdVec_apply_eq_true z b j).mpr hmem.2
      · rw [update_of_ne hj]
        rcases lt_or_ge (z j) a with hlt | hge
        · rw [(thresholdVec_apply_eq_true z b j).mpr (hlt.trans_le hab),
            (thresholdVec_apply_eq_true z (z i₀) j).mpr (hlt.trans_le hmem.1)]
        · have hb' : b ≤ z j := by
            by_contra hlt; exact hother j hj ⟨hge, not_le.mp hlt⟩
          rw [(thresholdVec_apply_eq_false z b j).mpr hb',
            (thresholdVec_apply_eq_false z (z i₀) j).mpr (hmem.2.le.trans hb')]
    have ha_eq : thresholdVec z a = update (thresholdVec z (z i₀)) i₀ false := by
      ext j
      by_cases hj : j = i₀
      · subst hj
        rw [update_self]
        exact (thresholdVec_apply_eq_false z a j).mpr hmem.1
      · rw [update_of_ne hj]
        rcases lt_or_ge (z j) a with hlt | hge
        · rw [(thresholdVec_apply_eq_true z a j).mpr hlt,
            (thresholdVec_apply_eq_true z (z i₀) j).mpr (hlt.trans_le hmem.1)]
        · have hb' : b ≤ z j := by
            by_contra hlt; exact hother j hj ⟨hge, not_le.mp hlt⟩
          rw [(thresholdVec_apply_eq_false z a j).mpr hge,
            (thresholdVec_apply_eq_false z (z i₀) j).mpr (hmem.2.le.trans hb')]
    rw [hsum, hb_eq, ha_eq]
    simp only [diffBool]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) herr_nn)
  · obtain ⟨i₀, hi₀, j₀, hj₀, hne⟩ := Finset.one_lt_card.mp h2
    have hmi : z i₀ ∈ Set.Ico a b := (Finset.mem_filter.mp hi₀).2
    have hmj : z j₀ ∈ Set.Ico a b := (Finset.mem_filter.mp hj₀).2
    have hge1 : (1 : ℝ) ≤ ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
        if (z i ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 := by
      have hterm_nn : ∀ i j : ι, (0 : ℝ) ≤
          if (z i ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 := fun i j => by
        split_ifs <;> norm_num
      have hinner : (1 : ℝ) ≤ ∑ j ∈ Finset.univ.erase i₀,
          if (z i₀ ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 := by
        have hjmem : j₀ ∈ Finset.univ.erase i₀ :=
          Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ j₀⟩
        have hval : (if (z i₀ ∈ Set.Ico a b ∧ z j₀ ∈ Set.Ico a b) then (1 : ℝ) else 0) = 1 := by
          simp [hmi, hmj]
        calc (1 : ℝ) = if (z i₀ ∈ Set.Ico a b ∧ z j₀ ∈ Set.Ico a b) then (1 : ℝ) else 0 :=
              hval.symm
          _ ≤ ∑ j ∈ Finset.univ.erase i₀,
              if (z i₀ ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 :=
            Finset.single_le_sum (f := fun j =>
                if (z i₀ ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0)
              (fun j _ => hterm_nn i₀ j) hjmem
      have houter : (∑ j ∈ Finset.univ.erase i₀,
            if (z i₀ ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0) ≤
          ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
            if (z i ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.univ.erase i,
            if (z i ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0)
          (fun i _ => Finset.sum_nonneg fun j _ => hterm_nn i j) (Finset.mem_univ i₀)
      exact hinner.trans houter
    have hlhs : f (thresholdVec z b) - f (thresholdVec z a) ≤ 2 * B := by
      have hb1 := hf_le (thresholdVec z b)
      have ha1 := hf_le (thresholdVec z a)
      linarith [le_abs_self (f (thresholdVec z b) - f (thresholdVec z a)),
        abs_sub (f (thresholdVec z b)) (f (thresholdVec z a))]
    have hdiff_lb : -(2 * (Fintype.card ι : ℝ) * B) ≤
        ∑ i : ι, if z i ∈ Set.Ico a b then diffBool f i (thresholdVec z (z i)) else 0 := by
      have hneg : ∀ i : ι, -(2 * B) ≤
          if z i ∈ Set.Ico a b then diffBool f i (thresholdVec z (z i)) else 0 := fun i => by
        split_ifs
        · unfold diffBool
          have h1 := neg_le_of_abs_le (hf_le (update (thresholdVec z (z i)) i true))
          have h2 := le_of_abs_le (hf_le (update (thresholdVec z (z i)) i false))
          linarith
        · linarith
      calc -(2 * (Fintype.card ι : ℝ) * B) = ∑ _i : ι, -(2 * B) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum fun i _ => hneg i
    have hmul : 2 * ((Fintype.card ι : ℝ) + 1) * B ≤
        (2 * ((Fintype.card ι : ℝ) + 1) * B) * ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
          if (z i ∈ Set.Ico a b ∧ z j ∈ Set.Ico a b) then (1 : ℝ) else 0 :=
      le_mul_of_one_le_right (by positivity) hge1
    linarith

/-- Nondegenerate version of monotonicity on `[0, ∞)` under `stdGaussian E`: when all pairwise
correlations satisfy `|⟪u i, u j⟫| < 1`, `t ↦ E[f (thresholdVec (⟪u ·, x⟫) t)]` is antitone on
`[0, ∞)`. -/
private theorem integral_threshold_stdGaussian_antitone_of_strict {ι E : Type*} [Finite ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) (hsym : IsSymmetricBool f)
    (u : ι → E) (hu : ∀ i, ‖u i‖ = 1) (hcorr : ∀ i j, i ≠ j → |⟪u i, u j⟫| < 1)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) t) ∂(stdGaussian E) ≤
      ∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) s) ∂(stdGaussian E) := by
  classical
  have := Fintype.ofFinite ι
  let B : ℝ := ∑ c : ι → Bool, |f c|
  let M : ℝ := 2 * ((Fintype.card ι : ℝ) + 1) * B
  let C : ℝ := M * ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
    (√(2 * π))⁻¹ * (√(2 * π * (1 - ⟪u i, u j⟫ ^ 2)))⁻¹
  have hE_int : ∀ r : ℝ,
      Integrable (fun x : E => f (thresholdVec (fun i => ⟪u i, x⟫) r)) (stdGaussian E) :=
    fun r => Integrable.of_bound
      ((Measurable.of_discrete (f := f)).comp
        (measurable_thresholdVec (measurable_pi_iff.mpr fun i => by fun_prop)
          (fun _ => r) measurable_const)).aestronglyMeasurable B
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (f := fun c => |f c|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _))
  have hstep : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      (∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) b) ∂(stdGaussian E)) -
        (∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) a) ∂(stdGaussian E)) ≤ C * (b - a) ^ 2 := by
    intro a b ha hab
    have hd_int : ∀ i : ι, Integrable (fun x : E =>
        if ⟪u i, x⟫ ∈ Set.Ico a b then
          diffBool f i (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) else 0) (stdGaussian E) := by
      intro i
      refine Integrable.of_bound
        ((Measurable.ite (measurableSet_Ico.preimage (by fun_prop))
          ((Measurable.of_discrete (f := diffBool f i)).comp
            (measurable_thresholdVec (measurable_pi_iff.mpr fun j => by fun_prop)
              (fun x => ⟪u i, x⟫) (by fun_prop))) measurable_const).aestronglyMeasurable)
        (2 * B) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]
          split_ifs
          · unfold diffBool
            exact (abs_sub _ _).trans (by
              have h1 := Finset.single_le_sum (fun c _ => abs_nonneg (f c))
                (Finset.mem_univ (update (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) i true))
              have h2 := Finset.single_le_sum (fun c _ => abs_nonneg (f c))
                (Finset.mem_univ (update (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) i false))
              linarith)
          · rw [abs_zero]
            exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    have hpair_int : ∀ i j : ι, Integrable (fun x : E =>
        if (⟪u i, x⟫ ∈ Set.Ico a b ∧ ⟪u j, x⟫ ∈ Set.Ico a b) then (1 : ℝ) else 0)
        (stdGaussian E) := fun i j =>
      have hm : MeasurableSet {x : E | ⟪u i, x⟫ ∈ Set.Ico a b ∧ ⟪u j, x⟫ ∈ Set.Ico a b} :=
        (measurableSet_Ico.preimage (f := fun x : E => ⟪u i, x⟫) (by fun_prop)).inter
          (measurableSet_Ico.preimage (f := fun x : E => ⟪u j, x⟫) (by fun_prop))
      Integrable.of_bound
        (Measurable.ite hm measurable_const measurable_const).aestronglyMeasurable 1
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; split_ifs <;> norm_num)
    have hmono :
        ∫ x, (f (thresholdVec (fun i => ⟪u i, x⟫) b) - f (thresholdVec (fun i => ⟪u i, x⟫) a))
          ∂(stdGaussian E) ≤
        ∫ x, ((∑ i : ι, if ⟪u i, x⟫ ∈ Set.Ico a b then
            diffBool f i (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) else 0) +
          M * ∑ i : ι, ∑ j ∈ Finset.univ.erase i,
            if (⟪u i, x⟫ ∈ Set.Ico a b ∧ ⟪u j, x⟫ ∈ Set.Ico a b) then (1 : ℝ) else 0)
          ∂(stdGaussian E) :=
      integral_mono ((hE_int b).sub (hE_int a))
        ((integrable_finsetSum _ fun i _ => hd_int i).add
          ((integrable_finsetSum _ fun i _ =>
            integrable_finsetSum _ fun j _ => hpair_int i j).const_mul M))
        (fun x => threshold_step_pointwise_le f (fun i => ⟪u i, x⟫) hab)
    rw [integral_sub (hE_int b) (hE_int a),
      integral_add (integrable_finsetSum _ fun i _ => hd_int i)
        ((integrable_finsetSum _ fun i _ =>
          integrable_finsetSum _ fun j _ => hpair_int i j).const_mul M),
      integral_const_mul,
      integral_finsetSum _ fun i _ => hd_int i,
      integral_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => hpair_int i j] at hmono
    have h1 : ∑ i : ι, ∫ x, (if ⟪u i, x⟫ ∈ Set.Ico a b then
        diffBool f i (thresholdVec (fun j => ⟪u j, x⟫) ⟪u i, x⟫) else 0)
        ∂(stdGaussian E) ≤ 0 :=
      Finset.sum_nonpos fun i _ => integral_indicator_diffBool_nonpos hf hsym u hu
        (fun i' j' hne => lt_of_le_of_lt (le_abs_self _) (hcorr i' j' hne)) i ha
    have h2 : ∑ i : ι, ∫ x, (∑ j ∈ Finset.univ.erase i,
        if (⟪u i, x⟫ ∈ Set.Ico a b ∧ ⟪u j, x⟫ ∈ Set.Ico a b) then (1 : ℝ) else 0)
        ∂(stdGaussian E) ≤ (∑ i : ι, ∑ j ∈ Finset.univ.erase i,
          (√(2 * π))⁻¹ * (√(2 * π * (1 - ⟪u i, u j⟫ ^ 2)))⁻¹) * (b - a) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hpair_int i j, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have hmeas_set : MeasurableSet {x : E | ⟪u i, x⟫ ∈ Set.Ico a b ∧ ⟪u j, x⟫ ∈ Set.Ico a b} :=
        (measurableSet_Ico.preimage (by fun_prop)).inter (measurableSet_Ico.preimage (by fun_prop))
      have hind : ∫ x, (if (⟪u i, x⟫ ∈ Set.Ico a b ∧ ⟪u j, x⟫ ∈ Set.Ico a b) then (1 : ℝ) else 0)
          ∂(stdGaussian E) =
          (stdGaussian E).real {x : E | ⟪u i, x⟫ ∈ Set.Ico a b ∧ ⟪u j, x⟫ ∈ Set.Ico a b} := by
        simpa [Set.indicator_apply] using
          integral_indicator_one (μ := stdGaussian E) hmeas_set
      rw [hind]
      exact stdGaussian_two_window_le (hu i) (hu j) (hcorr i j hji) hab
    have hM_nn : 0 ≤ M := mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    calc (∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) b) ∂(stdGaussian E)) -
          (∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) a) ∂(stdGaussian E))
        ≤ 0 + M * ((∑ i : ι, ∑ j ∈ Finset.univ.erase i,
            (√(2 * π))⁻¹ * (√(2 * π * (1 - ⟪u i, u j⟫ ^ 2)))⁻¹) * (b - a) ^ 2) :=
          hmono.trans (add_le_add h1 (mul_le_mul_of_nonneg_left h2 hM_nn))
      _ = C * (b - a) ^ 2 := by dsimp [C]; ring
  let g : ℝ → ℝ := fun r => ∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) r) ∂(stdGaussian E)
  have hteles : ∀ n : ℕ, 0 < n → g t - g s ≤ C * (t - s) ^ 2 / (n : ℝ) := by
    intro n hn
    have hnp : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    let pts : ℕ → ℝ := fun k => s + (k : ℝ) * ((t - s) / (n : ℝ))
    have hsum : ∑ k ∈ Finset.range n, (g (pts (k + 1)) - g (pts k)) = g (pts n) - g (pts 0) :=
      Finset.sum_range_sub (fun k => g (pts k)) n
    have hpt0 : pts 0 = s := by simp [pts]
    have hptn : pts n = t := by
      simp only [pts]
      field_simp [hnp.ne']
      ring
    rw [hpt0, hptn] at hsum
    rw [← hsum]
    calc ∑ k ∈ Finset.range n, (g (pts (k + 1)) - g (pts k))
        ≤ ∑ k ∈ Finset.range n, C * (pts (k + 1) - pts k) ^ 2 := by
            refine Finset.sum_le_sum fun k _ => hstep ?_ ?_
            · have : 0 ≤ (k : ℝ) * ((t - s) / (n : ℝ)) :=
                mul_nonneg (Nat.cast_nonneg k) (div_nonneg (sub_nonneg.mpr hst) hnp.le)
              linarith
            · have : pts (k + 1) - pts k = (t - s) / (n : ℝ) := by
                simp only [pts, Nat.cast_add, Nat.cast_one]; ring
              linarith [div_nonneg (sub_nonneg.mpr hst) hnp.le]
      _ = C * (t - s) ^ 2 / (n : ℝ) := by
            have hstep_eq : ∀ k : ℕ, C * (pts (k + 1) - pts k) ^ 2 =
                C * ((t - s) / (n : ℝ)) ^ 2 := fun k => by
              congr 1; simp only [pts, Nat.cast_add, Nat.cast_one]; ring
            simp_rw [hstep_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp [hnp.ne']
  have hlim : Tendsto (fun n : ℕ => C * (t - s) ^ 2 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv] using hinv.const_mul (C * (t - s) ^ 2)
  have hle0 : g t - g s ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall fun n => by
      simpa [Nat.cast_add, Nat.cast_one] using hteles (n + 1) (Nat.succ_pos n))
  linarith

/-- For a complement-symmetric function `f`, flipping the threshold `t ↦ -t` leaves the Gaussian
expectation unchanged. -/
theorem integral_threshold_neg {ι κ : Type*} [Finite ι] [Fintype κ]
    {f : (ι → Bool) → ℝ} (hsym : IsSymmetricBool f)
    (a : ι → κ → ℝ) (ha : ∀ i, ∑ k, a i k ^ 2 = 1) (t : ℝ) :
    ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) (-t)) ∂(piGauss κ) =
      ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂(piGauss κ) := by
  have hmp := measurePreserving_neg_piGauss (κ := κ)
  have hmeas : Measurable (fun x : κ → ℝ =>
      f (thresholdVec (fun i => ∑ k, a i k * x k) (-t))) :=
    (Measurable.of_discrete (f := f)).comp
      (measurable_thresholdVec (measurable_pi_iff.mpr fun i => by fun_prop)
        (fun _ => -t) measurable_const)
  calc ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) (-t)) ∂(piGauss κ)
      = ∫ x, f (thresholdVec (fun i => ∑ k, a i k * (-x k)) (-t)) ∂(piGauss κ) := by
          conv_lhs => rw [← hmp.map_eq]
          rw [integral_map hmp.measurable.aemeasurable
            (by rw [hmp.map_eq]; exact hmeas.aestronglyMeasurable)]
          simp only [Pi.neg_apply]
    _ = ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂(piGauss κ) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_piGauss_dotProduct_ne a ha t] with x hx
          have hvec : (fun i => ∑ k, a i k * (-x k)) = -(fun i => ∑ k, a i k * x k) := by
            ext i; simp [mul_neg, Finset.sum_neg_distrib]
          rw [hvec, thresholdVec_neg hx, hsym]

/-- **Monotonicity of symmetric submodular Gaussian threshold expectations on `[0, ∞)`.**
For `f : (ι → Bool) → ℝ` submodular and complement-symmetric, and unit-norm row family
`a : ι → κ → ℝ` (allowing arbitrary/singular covariance structure), whenever `0 ≤ s ≤ t`,
`E[f (thresholdVec (a · ⬝ᵥ X) t)] ≤ E[f (thresholdVec (a · ⬝ᵥ X) s)]`. -/
theorem integral_threshold_antitone_on_nonneg {ι κ : Type*} [Finite ι] [Fintype κ]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) (hsym : IsSymmetricBool f)
    (a : ι → κ → ℝ) (ha : ∀ i, ∑ k, a i k ^ 2 = 1) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂(piGauss κ) ≤
      ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) s) ∂(piGauss κ) := by
  classical
  have := Fintype.ofFinite ι
  let μ := (piGauss κ).prod (piGauss ι)
  let Bf : ℝ := ∑ c : ι → Bool, |f c|
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  let aeps : ℕ → ι → κ ⊕ ι → ℝ := fun n i =>
    Sum.elim (fun k => √(1 - eps n ^ 2) * a i k) (fun j => if j = i then eps n else 0)
  have heps_bounds : ∀ n : ℕ, 0 < eps n ∧ eps n < 1 := fun n => by
    have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    refine ⟨div_pos one_pos hpos, (div_lt_one hpos).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
  have hvec_eval : ∀ (n : ℕ) (p : (κ → ℝ) × (ι → ℝ)) (i : ι),
      ∑ m : κ ⊕ ι, aeps n i m * Sum.elim p.1 p.2 m =
        √(1 - eps n ^ 2) * (∑ k : κ, a i k * p.1 k) + eps n * p.2 i := by
    intro n p i
    rw [Fintype.sum_sum_type]
    simp only [aeps, Sum.elim_inl, Sum.elim_inr, mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hlim : ∀ r : ℝ,
      Tendsto (fun n : ℕ =>
        ∫ q, f (thresholdVec (fun i => ∑ m, aeps n i m * q m) r) ∂(piGauss (κ ⊕ ι)))
        atTop (nhds (∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) r) ∂(piGauss κ))) := by
    intro r
    have hmp := measurePreserving_sumElim_piGauss (κ₁ := κ) (κ₂ := ι)
    have hrewrite : ∀ n : ℕ,
        ∫ q, f (thresholdVec (fun i => ∑ m, aeps n i m * q m) r) ∂(piGauss (κ ⊕ ι)) =
          ∫ p, f (thresholdVec (fun i =>
            √(1 - eps n ^ 2) * (∑ k : κ, a i k * p.1 k) + eps n * p.2 i) r) ∂μ := by
      intro n
      have hmeas : Measurable (fun q : κ ⊕ ι → ℝ =>
          f (thresholdVec (fun i => ∑ m, aeps n i m * q m) r)) :=
        (Measurable.of_discrete (f := f)).comp
          (measurable_thresholdVec (measurable_pi_iff.mpr fun i => by fun_prop)
            (fun _ => r) measurable_const)
      conv_lhs => rw [← hmp.map_eq]
      rw [integral_map hmp.measurable.aemeasurable
        (by rw [hmp.map_eq]; exact hmeas.aestronglyMeasurable)]
      congr 1; ext p; simp only [hvec_eval]
    simp_rw [hrewrite]
    have htgt : ∫ p, f (thresholdVec (fun i => ∑ k, a i k * p.1 k) r) ∂μ =
        ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) r) ∂(piGauss κ) := by
      have hint : Integrable (fun p : (κ → ℝ) × (ι → ℝ) =>
          f (thresholdVec (fun i => ∑ k, a i k * p.1 k) r)) μ :=
        Integrable.of_bound
          (((Measurable.of_discrete (f := f)).comp
            (measurable_thresholdVec (measurable_pi_iff.mpr fun i => by fun_prop)
              (fun _ => r) measurable_const)).aestronglyMeasurable) Bf
          (ae_of_all _ fun _ => by
            rw [Real.norm_eq_abs]
            exact Finset.single_le_sum (f := fun c => |f c|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ _))
      rw [integral_prod _ hint]
      simp [integral_const]
    rw [← htgt]
    refine tendsto_integral_of_dominated_convergence (fun _ => Bf) ?_ (integrable_const Bf) ?_ ?_
    · intro n
      exact ((Measurable.of_discrete (f := f)).comp
        (measurable_thresholdVec (measurable_pi_iff.mpr fun i => by fun_prop)
          (fun _ => r) measurable_const)).aestronglyMeasurable
    · intro n
      exact ae_of_all _ fun _ => by
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (f := fun c => |f c|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _)
    · have hae_fst : ∀ᵐ p : (κ → ℝ) × (ι → ℝ) ∂μ,
          ∀ i : ι, ∑ k : κ, a i k * p.1 k ≠ r :=
        QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
          (ae_piGauss_dotProduct_ne a ha r)
      filter_upwards [hae_fst] with p hp
      have heps_tend : Tendsto eps atTop (nhds 0) :=
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
          (tendsto_add_atTop_nat 1)).congr fun n => by
            dsimp only [eps, Function.comp_apply]
            rw [Nat.cast_add, Nat.cast_one]
            congr 1; ring
      have hsqrt_tend : Tendsto (fun n => √(1 - eps n ^ 2)) atTop (nhds 1) := by
        have h : Tendsto (fun n => √(1 - eps n ^ 2)) atTop (nhds √((1 : ℝ) - 0 ^ 2)) :=
          ((tendsto_const_nhds (x := (1 : ℝ))).sub (heps_tend.pow 2)).sqrt
        simpa using h
      have hev_coord : ∀ i : ι, ∀ᶠ n in atTop,
          thresholdVec (fun j =>
            √(1 - eps n ^ 2) * (∑ k : κ, a j k * p.1 k) + eps n * p.2 j) r i =
          thresholdVec (fun j => ∑ k : κ, a j k * p.1 k) r i := by
        intro i
        have hi_tend : Tendsto (fun n => √(1 - eps n ^ 2) * (∑ k : κ, a i k * p.1 k) +
            eps n * p.2 i) atTop (nhds (∑ k : κ, a i k * p.1 k)) := by
          simpa using (hsqrt_tend.mul_const _).add (heps_tend.mul_const (p.2 i))
        rcases lt_or_gt_of_ne (hp i) with hlt | hgt
        · filter_upwards [hi_tend.eventually (Iio_mem_nhds hlt)] with n hn
          rw [(thresholdVec_apply_eq_true _ r i).mpr hn,
            (thresholdVec_apply_eq_true _ r i).mpr hlt]
        · filter_upwards [hi_tend.eventually (Ioi_mem_nhds hgt)] with n hn
          rw [(thresholdVec_apply_eq_false _ r i).mpr hn.le,
            (thresholdVec_apply_eq_false _ r i).mpr hgt.le]
      have hev_all : ∀ᶠ n in atTop,
          f (thresholdVec (fun j =>
            √(1 - eps n ^ 2) * (∑ k : κ, a j k * p.1 k) + eps n * p.2 j) r) =
          f (thresholdVec (fun j => ∑ k : κ, a j k * p.1 k) r) := by
        filter_upwards [eventually_all.mpr hev_coord] with n hn
        exact congrArg f (funext hn)
      exact tendsto_const_nhds.congr' (hev_all.mono fun n hn => hn.symm)
  refine le_of_tendsto_of_tendsto (hlim t) (hlim s) (Eventually.of_forall fun n => ?_)
  have ⟨heps_pos, heps_lt1⟩ := heps_bounds n
  have h1e_nn : 0 ≤ 1 - eps n ^ 2 := by nlinarith
  let u : ι → EuclideanSpace ℝ (κ ⊕ ι) := fun i => WithLp.toLp 2 (aeps n i)
  have hu : ∀ i, ‖u i‖ = 1 := fun i => toLp_norm_eq_one (by
    rw [Fintype.sum_sum_type]
    simp only [aeps, Sum.elim_inl, Sum.elim_inr]
    have h1 : ∑ k : κ, (√(1 - eps n ^ 2) * a i k) ^ 2 = 1 - eps n ^ 2 := by
      simp_rw [mul_pow, Real.sq_sqrt h1e_nn, ← Finset.mul_sum, ha i, mul_one]
    have h2 : ∑ j : ι, (if j = i then eps n else 0) ^ 2 = eps n ^ 2 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [hji]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [h1, h2]; ring)
  have hcorr : ∀ i j, i ≠ j → |⟪u i, u j⟫| < 1 := by
    intro i j hij
    have hinner : ⟪u i, u j⟫ = (1 - eps n ^ 2) * ∑ k : κ, a i k * a j k := by
      rw [EuclideanSpace.inner_toLp_toLp]
      simp only [star_trivial, dotProduct, Fintype.sum_sum_type, aeps, Sum.elim_inl, Sum.elim_inr]
      have hright : ∑ m : ι, (if m = j then eps n else 0) * (if m = i then eps n else 0) = 0 :=
        Finset.sum_eq_zero fun m _ => by
          by_cases hmj : m = j
          · subst hmj; simp [hij.symm]
          · simp [hmj]
      rw [hright, add_zero]
      calc ∑ k : κ, (√(1 - eps n ^ 2) * a j k) * (√(1 - eps n ^ 2) * a i k)
          = ∑ k : κ, (√(1 - eps n ^ 2) ^ 2) * (a i k * a j k) :=
              Finset.sum_congr rfl fun k _ => by ring
        _ = (1 - eps n ^ 2) * ∑ k : κ, a i k * a j k := by
              rw [Real.sq_sqrt h1e_nn, ← Finset.mul_sum]
    have hcs : |∑ k : κ, a i k * a j k| ≤ 1 := by
      have hinner_a : |⟪WithLp.toLp 2 (a i), WithLp.toLp 2 (a j)⟫| ≤
          ‖WithLp.toLp 2 (a i)‖ * ‖WithLp.toLp 2 (a j)‖ := abs_real_inner_le_norm _ _
      rw [toLp_norm_eq_one (ha i), toLp_norm_eq_one (ha j), mul_one,
        EuclideanSpace.inner_toLp_toLp] at hinner_a
      simpa only [star_trivial, dotProduct, mul_comm (a j _)] using hinner_a
    rw [hinner, abs_mul, abs_of_nonneg h1e_nn]
    calc (1 - eps n ^ 2) * |∑ k : κ, a i k * a j k|
        ≤ (1 - eps n ^ 2) * 1 := mul_le_mul_of_nonneg_left hcs h1e_nn
      _ < 1 := by nlinarith
  have htoLp := measurePreserving_toLp_pi_gaussianReal (κ ⊕ ι)
  have hrew : ∀ r : ℝ,
      ∫ q, f (thresholdVec (fun i => ∑ m, aeps n i m * q m) r) ∂(piGauss (κ ⊕ ι)) =
        ∫ x, f (thresholdVec (fun i => ⟪u i, x⟫) r) ∂(stdGaussian (EuclideanSpace ℝ (κ ⊕ ι))) := by
    intro r
    have hmeas : Measurable (fun x : EuclideanSpace ℝ (κ ⊕ ι) =>
        f (thresholdVec (fun i => ⟪u i, x⟫) r)) :=
      (Measurable.of_discrete (f := f)).comp
        (measurable_thresholdVec (measurable_pi_iff.mpr fun i => by fun_prop)
          (fun _ => r) measurable_const)
    conv_rhs => rw [← htoLp.map_eq]
    rw [integral_map htoLp.measurable.aemeasurable
      (by rw [htoLp.map_eq]; exact hmeas.aestronglyMeasurable)]
    congr 1; ext q; congr 2; ext i
    simp [u, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]
  dsimp only
  rw [hrew t, hrew s]
  exact integral_threshold_stdGaussian_antitone_of_strict hf hsym u hu hcorr hs hst

/-- For a symmetric submodular `f`, larger `|t|` yields smaller Gaussian threshold expectation. -/
theorem integral_threshold_le_of_abs_le {ι κ : Type*} [Finite ι] [Fintype κ]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) (hsym : IsSymmetricBool f)
    (a : ι → κ → ℝ) (ha : ∀ i, ∑ k, a i k ^ 2 = 1) {s t : ℝ} (h : |s| ≤ |t|) :
    ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂(piGauss κ) ≤
      ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) s) ∂(piGauss κ) := by
  have heq : ∀ r : ℝ,
      ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) |r|) ∂(piGauss κ) =
        ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) r) ∂(piGauss κ) := fun r => by
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr, integral_threshold_neg hsym a ha r]
  rw [← heq t, ← heq s]
  exact integral_threshold_antitone_on_nonneg hf hsym a ha (abs_nonneg s) h

/-- **Zero-threshold maximality for symmetric submodular functions.**
For any submodular, complement-symmetric `f : (ι → Bool) → ℝ` and unit-norm row family
`a : ι → κ → ℝ` (with no nonsingularity assumption), every threshold `t : ℝ` satisfies
`E[f (thresholdVec (a · ⬝ᵥ X) t)] ≤ E[f (thresholdVec (a · ⬝ᵥ X) 0)]`. -/
theorem integral_threshold_le_zero {ι κ : Type*} [Finite ι] [Fintype κ]
    {f : (ι → Bool) → ℝ} (hf : IsSubmodularBool f) (hsym : IsSymmetricBool f)
    (a : ι → κ → ℝ) (ha : ∀ i, ∑ k, a i k ^ 2 = 1) (t : ℝ) :
    ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) t) ∂(piGauss κ) ≤
      ∫ x, f (thresholdVec (fun i => ∑ k, a i k * x k) 0) ∂(piGauss κ) :=
  integral_threshold_le_of_abs_le hf hsym a ha (by simp)

end ZeroThreshold

end Cslib.Circuits.Frontier.CrossingCover

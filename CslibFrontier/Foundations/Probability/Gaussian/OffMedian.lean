/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
public import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Arccos
import CslibFrontier.Foundations.Probability.Gaussian.Correlated
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Off-median Gaussian threshold crossings

Sheppard's bound (`ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_angle`) states that two
unit-norm Gaussian projections at angle `θ = arccos ρ` are separated by *any* threshold `t` with
probability at most `θ / π`, attained at `t = 0`. Away from the median (`t ≠ 0`), the crossing
probability decays by an additional Gaussian factor `exp (-t ^ 2 / 2)`:

`(stdGaussian E).real {x | t ∈ Ι ⟪u, x⟫ ⟪v, x⟫} ≤ exp (-t ^ 2 / 2) * (angle u v / π)`.

**Polar proof.** Realize `(⟪u, X⟫, ⟪v, X⟫)` as `(r cos φ, r cos (φ - θ))` under the planar
standard Gaussian (`ProbabilityTheory.stdGaussian_map_inner_prod_eq_correlatedGaussian`).
* When `r < |t|`, both `r cos φ` and `r cos (φ - θ)` have magnitude strictly below `|t|`, so they
  lie on the same side of `t` and no crossing can occur.
* When `r > |t|`, write `c = arccos (t / r) ∈ [0, π]`. On `[-π, π]`, the indicator `g(φ)` of
  `cos c ≤ cos φ` is the interval `[-c, c]` of length `2 c`, and `g(φ - θ)` is its translate by
  `θ ∈ [0, π]`. When `2 c ≤ θ` their symmetric difference has measure at most `4 c ≤ 2 θ`; when
  `θ < 2 c`, both indicators equal `1` on `[θ - c, c] ⊆ [-π, π]`, so their overlap has length at
  least `2 c - θ` and their symmetric difference has measure at most `4 c - 2 (2 c - θ) = 2 θ`.
* Integrating `(2 θ) · (2π)⁻¹ r exp (-r ^ 2 / 2)` over `r ∈ (|t|, ∞)` gives
  `exp (-t ^ 2 / 2) · (θ / π)`.

## Main results

* `ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_exp_mul_angle`: off-median Sheppard bound.
* `ProbabilityTheory.measureReal_pi_gaussianReal_inner_eq_zero`: any unit hyperplane has Gaussian
  product measure zero.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal RealInnerProductSpace Interval Topology

namespace ProbabilityTheory

/-- For `r < |t|`, `t` cannot separate `r * cos φ` and `r * cos ψ`. -/
private theorem not_mem_uIoc_of_lt_abs {t r φ ψ : ℝ} (hr0 : 0 < r) (hrt : r < |t|) :
    t ∉ Ι (r * cos φ) (r * cos ψ) := by
  have h1 : |r * cos φ| ≤ r := by
    rw [abs_mul, abs_of_pos hr0]
    exact mul_le_of_le_one_right hr0.le (abs_cos_le_one φ)
  have h2 : |r * cos ψ| ≤ r := by
    rw [abs_mul, abs_of_pos hr0]
    exact mul_le_of_le_one_right hr0.le (abs_cos_le_one ψ)
  rw [abs_le] at h1 h2
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht] at hrt
    rw [mem_uIoc]
    rintro (⟨_, h⟩ | ⟨_, h⟩) <;> linarith
  · rw [abs_of_neg ht] at hrt
    rw [mem_uIoc]
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> linarith

/-- Angular symmetric-difference bound: for `c, θ ∈ [0, π]`, the set of angles in `(-π, π)` where
`cos c ≤ cos φ` and `cos c ≤ cos (φ - θ)` disagree has measure at most `2 * θ`. -/
private theorem angular_crossing_integral_le {c θ : ℝ} (hc0 : 0 ≤ c) (hcπ : c ≤ π)
    (hθ0 : 0 ≤ θ) (_hθπ : θ ≤ π) :
    (∫ φ in (-π)..π,
        if ¬(cos c ≤ cos φ ↔ cos c ≤ cos (φ - θ)) then (1 : ℝ) else 0) ≤ 2 * θ := by
  classical
  let g : ℝ → ℝ := fun ψ => if cos c ≤ cos ψ then 1 else 0
  have hg_per : Function.Periodic g (2 * π) := fun ψ => by
    simp only [g, cos_add_two_pi]
  have hg_meas : Measurable g :=
    Measurable.ite (measurableSet_le measurable_const continuous_cos.measurable)
      measurable_const measurable_const
  have hg0 : ∀ ψ, 0 ≤ g ψ := fun ψ => by simp only [g]; split_ifs <;> norm_num
  have hg1 : ∀ ψ, g ψ ≤ 1 := fun ψ => by simp only [g]; split_ifs <;> norm_num
  have hint_bdd : ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 2) →
      IntervalIntegrable f volume (-π) π := fun f hf h0 h2 => by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := 2) measure_Ioc_lt_top.ne
      hf.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h2 x
  have hg_ii : IntervalIntegrable g volume (-π) π :=
    hint_bdd g hg_meas hg0 fun x => (hg1 x).trans (by norm_num)
  have hg_shift_ii : IntervalIntegrable (fun φ => g (φ - θ)) volume (-π) π :=
    hint_bdd _ (hg_meas.comp (measurable_id.sub_const θ)) (fun x => hg0 _)
      (fun x => (hg1 _).trans (by norm_num))
  -- On `[-π, π]`, `cos c ≤ cos φ ↔ φ ∈ [-c, c]`.
  have hg_Icc : ∀ φ ∈ Icc (-π) π, g φ = (Icc (-c) c).indicator (fun _ => (1 : ℝ)) φ := by
    intro φ hφ
    have habs : |φ| ≤ π := abs_le.mpr hφ
    have hiff : cos c ≤ cos φ ↔ φ ∈ Icc (-c) c := by
      rw [← cos_abs φ, strictAntiOn_cos.le_iff_ge ⟨hc0, hcπ⟩ ⟨abs_nonneg φ, habs⟩, mem_Icc]
      exact abs_le
    by_cases h : φ ∈ Icc (-c) c
    · simp [g, hiff.mpr h, h]
    · simp [g, mt hiff.mp h, h]
  have hint_Icc {a b : ℝ} (ha : -π ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
      ∫ φ in (-π)..π, (Icc a b).indicator (fun _ => (1 : ℝ)) φ = b - a := by
    rw [intervalIntegral.integral_of_le (by linarith [pi_pos]),
      integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hsub : Icc a b ∩ Ioc (-π) π = Icc a b \ {-π} := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ioc, Set.mem_sdiff, mem_singleton_iff]
      refine ⟨fun ⟨hx, hx'⟩ => ⟨hx, ne_of_gt hx'.1⟩, fun ⟨hx, hne⟩ => ⟨hx, ?_, by linarith⟩⟩
      exact lt_of_le_of_ne (by linarith) (Ne.symm hne)
    rw [hsub, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      measure_sdiff_null (measure_singleton (-π)), Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
  have hint_g : ∫ φ in (-π)..π, g φ = 2 * c := by
    have hcongr : ∫ φ in (-π)..π, g φ =
        ∫ φ in (-π)..π, (Icc (-c) c).indicator (fun _ => (1 : ℝ)) φ :=
      intervalIntegral.integral_congr (by
        rw [uIcc_of_le (by linarith [pi_pos])]
        exact hg_Icc)
    rw [hcongr, hint_Icc (by linarith) (by linarith) hcπ]
    ring
  have hint_g_shift : ∫ φ in (-π)..π, g (φ - θ) = 2 * c := by
    rw [intervalIntegral.integral_comp_sub_right]
    have hper := hg_per.intervalIntegral_add_eq (-π - θ) (-π)
    have hlen : -π - θ + 2 * π = π - θ := by ring
    have hlen2 : -π + 2 * π = π := by ring
    rw [hlen, hlen2] at hper
    rw [hper, hint_g]
  let cross : ℝ → ℝ := fun φ => if ¬(cos c ≤ cos φ ↔ cos c ≤ cos (φ - θ)) then 1 else 0
  have hcross_eq : ∀ φ, cross φ = g φ + g (φ - θ) - 2 * (g φ * g (φ - θ)) := by
    intro φ
    simp only [cross, g]
    by_cases h1 : cos c ≤ cos φ <;> by_cases h2 : cos c ≤ cos (φ - θ) <;> simp [h1, h2]
    norm_num
  have hprod_ii : IntervalIntegrable (fun φ => g φ * g (φ - θ)) volume (-π) π :=
    hint_bdd _ (hg_meas.mul (hg_meas.comp (measurable_id.sub_const θ)))
      (fun x => mul_nonneg (hg0 _) (hg0 _))
      (fun x => (mul_le_of_le_one_right (hg0 _) (hg1 _)).trans ((hg1 _).trans (by norm_num)))
  have hsum_ii : IntervalIntegrable (fun φ => g φ + g (φ - θ)) volume (-π) π :=
    hg_ii.add hg_shift_ii
  change ∫ φ in (-π)..π, cross φ ≤ 2 * θ
  simp_rw [hcross_eq]
  rw [intervalIntegral.integral_sub hsum_ii (hprod_ii.const_mul 2),
    intervalIntegral.integral_add hg_ii hg_shift_ii, intervalIntegral.integral_const_mul,
    hint_g, hint_g_shift]
  rcases le_or_gt (2 * c) θ with hcθ | hθc
  · have hprod_nonneg : 0 ≤ ∫ φ in (-π)..π, g φ * g (φ - θ) :=
      intervalIntegral.integral_nonneg (by linarith [pi_pos]) fun φ _ => mul_nonneg (hg0 _) (hg0 _)
    linarith
  · have hover : 2 * c - θ ≤ ∫ φ in (-π)..π, g φ * g (φ - θ) := by
      let indI : ℝ → ℝ := (Icc (θ - c) c).indicator fun _ => (1 : ℝ)
      have hind_ii : IntervalIntegrable indI volume (-π) π :=
        hint_bdd indI (measurable_const.indicator measurableSet_Icc)
          (fun x => by simp only [indI, indicator]; split_ifs <;> norm_num)
          (fun x => by simp only [indI, indicator]; split_ifs <;> norm_num)
      have hpt : ∀ φ ∈ Icc (-π) π, indI φ ≤ g φ * g (φ - θ) := by
        intro φ _
        by_cases hφ : φ ∈ Icc (θ - c) c
        · have h1 : |φ| ≤ c := abs_le.mpr ⟨by linarith [hφ.1], hφ.2⟩
          have h2 : |φ - θ| ≤ c := abs_le.mpr ⟨by linarith [hφ.1], by linarith [hφ.2]⟩
          have hc1 : cos c ≤ cos φ := by
            rw [← cos_abs φ]
            exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) hcπ h1
          have hc2 : cos c ≤ cos (φ - θ) := by
            rw [← cos_abs (φ - θ)]
            exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hcπ h2
          simp [indI, hφ, g, hc1, hc2]
        · simp only [indI, indicator_of_notMem hφ]
          exact mul_nonneg (hg0 _) (hg0 _)
      have hmono := intervalIntegral.integral_mono_on (by linarith [pi_pos]) hind_ii hprod_ii hpt
      refine le_trans ?_ hmono
      rw [hint_Icc (by linarith) (by linarith) hcπ]
      linarith
    linarith

/-- The Gaussian tail radial integral `∫_{r > a} r exp (-r ^ 2 / 2) = exp (-a ^ 2 / 2)`. -/
private theorem integral_Ioi_mul_exp_neg_sq_div_two {a : ℝ} :
    ∫ r in Ioi a, r * exp (-(r ^ 2) / 2) = exp (-(a ^ 2) / 2) := by
  have hderiv : ∀ r ∈ Ici a, HasDerivAt (fun x => -exp (-(x ^ 2) / 2))
      (r * exp (-(r ^ 2) / 2)) r := by
    intro r _
    have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-r) r := by
      have h := ((hasDerivAt_pow 2 r).neg).div_const 2
      exact h.congr_deriv (by ring)
    exact (h1.exp.neg).congr_deriv (by ring)
  have htend : Tendsto (fun x : ℝ => -exp (-(x ^ 2) / 2)) atTop (𝓝 0) := by
    have hquad : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot := by
      have hsq : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
      have hdiv : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop := hsq.atTop_div_const (by norm_num)
      refine (tendsto_neg_atTop_atBot.comp hdiv).congr fun x => ?_
      simp [neg_div]
    simpa using (Real.tendsto_exp_atBot.comp hquad).neg
  have hint : IntegrableOn (fun r : ℝ => r * exp (-(r ^ 2) / 2)) (Ioi a) := by
    have h := integrable_mul_exp_neg_mul_sq (b := 2⁻¹) (by norm_num)
    refine h.integrableOn.congr_fun (fun r _ => ?_) measurableSet_Ioi
    exact congrArg (r * exp ·) (by ring)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  ring

/-- **Off-median Sheppard / Price bound.** For unit vectors `u, v` of a finite-dimensional real
inner product space `E` and any threshold `t : ℝ`, `t` lies between `⟪u, X⟫` and `⟪v, X⟫` under
`X ~ stdGaussian E` with probability at most `exp (-t ^ 2 / 2) * (angle u v / π)`. -/
theorem measureReal_stdGaussian_mem_uIoc_le_exp_mul_angle
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (t : ℝ) :
    (stdGaussian E).real {x | t ∈ Ι ⟪u, x⟫ ⟪v, x⟫} ≤
      exp (-t ^ 2 / 2) * (InnerProductGeometry.angle u v / π) := by
  classical
  set ρ := ⟪u, v⟫
  have hρ_abs : |ρ| ≤ 1 := by
    simpa [ρ, hu, hv] using abs_real_inner_le_norm u v
  have hρ_bounds := abs_le.mp hρ_abs
  set θ := arccos ρ
  have hθ0 : 0 ≤ θ := arccos_nonneg ρ
  have hθπ : θ ≤ π := arccos_le_pi ρ
  have hangle : InnerProductGeometry.angle u v = θ :=
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hu hv
  rw [hangle]
  have hcosθ : cos θ = ρ := cos_arccos hρ_bounds.1 hρ_bounds.2
  have hsinθ : sin θ = √(1 - ρ ^ 2) := sin_arccos ρ
  let S : Set (ℝ × ℝ) := {p | t ∈ Ι p.1 p.2}
  have hSm : MeasurableSet S := measurableSet_setOf_mem_uIoc measurable_fst measurable_snd t
  have hmap1 : (stdGaussian E).real {x | t ∈ Ι ⟪u, x⟫ ⟪v, x⟫} = (correlatedGaussian ρ).real S := by
    rw [← stdGaussian_map_inner_prod_eq_correlatedGaussian hu hv,
      map_measureReal_apply (by fun_prop) hSm]
    rfl
  let A : Set (ℝ × ℝ) := {g | t ∈ Ι g.1 (cos θ * g.1 + sin θ * g.2)}
  have hAm : MeasurableSet A := measurableSet_setOf_mem_uIoc measurable_fst (by fun_prop) t
  have hmap2 : (correlatedGaussian ρ).real S =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).real A := by
    rw [correlatedGaussian_def, map_measureReal_apply (by fun_prop) hSm]
    congr 1
    ext g
    simp [S, A, hcosθ, hsinθ]
  rw [hmap1, hmap2]
  let rad : ℝ → ℝ := fun r => (2 * π)⁻¹ * (r * exp (-(r ^ 2) / 2))
  have hrad_nonneg : ∀ r ≥ 0, 0 ≤ rad r := fun r hr => by
    dsimp [rad]; positivity
  have hrad_int : IntegrableOn rad (Ioi 0) := by
    dsimp [rad]
    refine Integrable.const_mul ?_ _
    have h := integrable_mul_exp_neg_mul_sq (b := 2⁻¹) (by norm_num)
    refine h.integrableOn.congr_fun (fun r _ => ?_) measurableSet_Ioi
    exact congrArg (r * exp ·) (by ring)
  have hdens : ∀ r φ,
      gaussianPDFReal 0 1 (r * cos φ) * gaussianPDFReal 0 1 (r * sin φ) =
        (2 * π)⁻¹ * exp (-(r ^ 2) / 2) := by
    intro r φ
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    rw [mul_mul_mul_comm, ← mul_inv, mul_self_sqrt (by positivity), ← exp_add]
    congr 2
    linear_combination (-2⁻¹ * r ^ 2) * sin_sq_add_cos_sq φ
  have hpolar_eq : ((gaussianReal 0 1).prod (gaussianReal 0 1)).real A =
      ∫ r in Ioi (0 : ℝ), rad r * ∫ φ in (-π)..π, A.indicator (fun _ => (1 : ℝ))
        (r * cos φ, r * sin φ) := by
    rw [← integral_indicator_one hAm]
    change ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
    rw [integral_withDensity_eq_integral_toReal_smul]
    · rw [← Measure.volume_eq_prod, ← integral_comp_polarCoord_symm]
      trans ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
          rad p.1 * A.indicator (fun _ => (1 : ℝ)) (p.1 * cos p.2, p.1 * sin p.2)
      · rw [polarCoord_target]
        refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p _ => ?_
        simp only [polarCoord_symm_apply, ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul,
          hdens, rad]
        ring
      · have hf_int : IntegrableOn
            (fun p : ℝ × ℝ =>
              rad p.1 * A.indicator (fun _ => (1 : ℝ)) (p.1 * cos p.2, p.1 * sin p.2))
            (Ioi 0 ×ˢ Ioo (-π) π) := by
          have hprod : Integrable (fun p : ℝ × ℝ => ‖rad p.1‖ * (1 : ℝ))
              ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))) :=
            hrad_int.norm.mul_prod (integrable_const 1)
          rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
          refine hprod.mono' ?_ (ae_of_all _ fun p => ?_)
          · refine Measurable.aestronglyMeasurable ?_
            exact (by unfold rad; fun_prop : Measurable rad).comp measurable_fst |>.mul
              ((measurable_const.indicator hAm).comp (by fun_prop))
          · rw [norm_mul, mul_one]
            refine mul_le_of_le_one_right (norm_nonneg _) ?_
            simp only [indicator_apply]
            split_ifs <;> norm_num
        rw [Measure.volume_eq_prod, setIntegral_prod _ hf_int]
        refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
        dsimp only
        rw [integral_const_mul, intervalIntegral.integral_of_le (by linarith [pi_pos]),
          integral_Ioc_eq_integral_Ioo]
    · fun_prop
    · exact ae_of_all _ fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top
  rw [hpolar_eq]
  let angInt : ℝ → ℝ := fun r =>
    ∫ φ in (-π)..π, A.indicator (fun _ => (1 : ℝ)) (r * cos φ, r * sin φ)
  have hang_ae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      rad r * angInt r ≤ rad r * (Ioi |t|).indicator (fun _ => 2 * θ) r := by
    have hne_abs : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ≠ |t| := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine (ae_iff.mpr ?_).mono fun r hr _ => hr
      simp
    filter_upwards [ae_restrict_mem measurableSet_Ioi, hne_abs] with r hr hne
    have hr0 : 0 < r := hr
    refine mul_le_mul_of_nonneg_left ?_ (hrad_nonneg r hr0.le)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [indicator_of_notMem (not_lt.mpr hlt.le)]
      have hzero : ∀ φ, A.indicator (fun _ => (1 : ℝ)) (r * cos φ, r * sin φ) = 0 := by
        intro φ
        refine indicator_of_notMem ?_ _
        simp only [A, mem_ofPred_eq]
        have hrot : cos θ * (r * cos φ) + sin θ * (r * sin φ) = r * cos (φ - θ) := by
          rw [cos_sub]; ring
        rw [hrot]
        exact not_mem_uIoc_of_lt_abs hr0 hlt
      simp [angInt, hzero]
    · rw [indicator_of_mem hgt]
      set c := arccos (t / r)
      have htr_abs : |t / r| < 1 := by
        rw [abs_div, abs_of_pos hr0, div_lt_one hr0]
        exact hgt
      have hcos_c : cos c = t / r :=
        cos_arccos (abs_lt.mp htr_abs).1.le (abs_lt.mp htr_abs).2.le
      have hpt : ∀ φ, A.indicator (fun _ => (1 : ℝ)) (r * cos φ, r * sin φ) =
          if ¬(cos c ≤ cos φ ↔ cos c ≤ cos (φ - θ)) then 1 else 0 := by
        intro φ
        have hrot : cos θ * (r * cos φ) + sin θ * (r * sin φ) = r * cos (φ - θ) := by
          rw [cos_sub]; ring
        have hiff1 : ∀ ψ, t ≤ r * cos ψ ↔ cos c ≤ cos ψ := fun ψ => by
          rw [hcos_c, div_le_iff₀ hr0, mul_comm]
        have hiff2 : ∀ ψ, r * cos ψ < t ↔ ¬cos c ≤ cos ψ := fun ψ => by
          rw [← not_le, hiff1]
        simp only [indicator_apply, A, mem_ofPred_eq, hrot, mem_uIoc, hiff1, hiff2]
        by_cases h1 : cos c ≤ cos φ <;> by_cases h2 : cos c ≤ cos (φ - θ) <;> simp [h1, h2]
      dsimp [angInt]
      simp_rw [hpt]
      exact angular_crossing_integral_le (arccos_nonneg _) (arccos_le_pi _) hθ0 hθπ
  have hang_meas : Measurable angInt := by
    have hj : Measurable (Function.uncurry fun r φ =>
        A.indicator (fun _ => (1 : ℝ)) (r * cos φ, r * sin φ)) :=
      (measurable_const.indicator hAm).comp (by fun_prop)
    dsimp [angInt]
    simp_rw [intervalIntegral.integral_of_le (by linarith [pi_pos] : -π ≤ π)]
    exact (hj.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc (-π) π))).measurable
  have hang_bdd : ∀ r, 0 ≤ angInt r ∧ angInt r ≤ 2 * π := by
    intro r
    have hii : IntervalIntegrable (fun φ => A.indicator (fun _ => (1 : ℝ)) (r * cos φ, r * sin φ))
        volume (-π) π := by
      rw [intervalIntegrable_iff]
      refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
        ((measurable_const.indicator hAm).comp (by fun_prop)).aestronglyMeasurable ?_
      filter_upwards with φ
      simp only [indicator_apply]
      split_ifs <;> norm_num
    refine ⟨intervalIntegral.integral_nonneg (by linarith [pi_pos]) fun φ _ => by
        simp only [indicator_apply]; split_ifs <;> norm_num, ?_⟩
    have hle := intervalIntegral.integral_mono_on (by linarith [pi_pos]) hii
      (intervalIntegrable_const (c := (1 : ℝ))) fun φ _ => by
        simp only [indicator_apply]; split_ifs <;> norm_num
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hle
    dsimp [angInt]
    linarith
  have hLHS_int : IntegrableOn (fun r => rad r * angInt r) (Ioi 0) := by
    refine (hrad_int.mul_const (2 * π)).mono'
      ((by unfold rad; fun_prop : Measurable rad).mul hang_meas).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hrad_nonneg r (le_of_lt hr)),
      abs_of_nonneg (hang_bdd r).1]
    exact mul_le_mul_of_nonneg_left (hang_bdd r).2 (hrad_nonneg r (le_of_lt hr))
  have hRHS_int :
      IntegrableOn (fun r => rad r * (Ioi |t|).indicator (fun _ => 2 * θ) r) (Ioi 0) := by
    refine (hrad_int.mul_const (2 * θ)).mono'
      ((by unfold rad; fun_prop : Measurable rad).mul
        (measurable_const.indicator measurableSet_Ioi)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hrad_nonneg r (le_of_lt hr))]
    refine mul_le_mul_of_nonneg_left ?_ (hrad_nonneg r (le_of_lt hr))
    simp only [indicator_apply]
    split_ifs <;> rw [Real.norm_eq_abs]
    · rw [abs_of_nonneg (by positivity)]
    · simpa using mul_nonneg zero_le_two hθ0
  calc ∫ r in Ioi (0 : ℝ), rad r * angInt r
      ≤ ∫ r in Ioi (0 : ℝ), rad r * (Ioi |t|).indicator (fun _ => 2 * θ) r :=
        integral_mono_ae hLHS_int hRHS_int hang_ae
    _ = ∫ r in Ioi |t|, rad r * (2 * θ) := by
        have hrewrite : (fun r => rad r * (Ioi |t|).indicator (fun _ => 2 * θ) r) =
            (Ioi |t|).indicator (fun r => rad r * (2 * θ)) := by
          ext r; by_cases h : r ∈ Ioi |t| <;> simp [h]
        rw [hrewrite, setIntegral_indicator measurableSet_Ioi]
        have hinter : Ioi (0 : ℝ) ∩ Ioi |t| = Ioi |t| :=
          inter_eq_right.mpr (Ioi_subset_Ioi (abs_nonneg t))
        rw [hinter]
    _ = exp (-t ^ 2 / 2) * (θ / π) := by
        dsimp [rad]
        have hconst : (fun r : ℝ => (2 * π)⁻¹ * (r * exp (-(r ^ 2) / 2)) * (2 * θ)) =
            fun r => (θ / π) * (r * exp (-(r ^ 2) / 2)) := by
          ext r; field_simp
        rw [hconst, integral_const_mul, integral_Ioi_mul_exp_neg_sq_div_two, sq_abs]
        ring_nf

/-- Under `Measure.pi (gaussianReal 0 1)`, `{ω | ⟪u, WithLp.toLp 2 ω⟫ = 0}` has measure zero for
every unit vector `u`. -/
theorem measureReal_pi_gaussianReal_inner_eq_zero {ι : Type*} [Fintype ι]
    {u : EuclideanSpace ℝ ι} (hu : ‖u‖ = 1) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {ω | ⟪u, WithLp.toLp 2 ω⟫ = 0} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hnn : ‖u‖₊ ^ 2 = 1 := by ext; simp [hu]
  have hmp : MeasurePreserving (fun ω : ι → ℝ => ⟪u, WithLp.toLp 2 ω⟫)
      (Measure.pi fun _ : ι => gaussianReal 0 1) (gaussianReal 0 1) := by
    have h1 := measurePreserving_toLp_pi_gaussianReal ι
    have h2 : MeasurePreserving (fun x : EuclideanSpace ℝ ι => ⟪u, x⟫)
        (stdGaussian (EuclideanSpace ℝ ι)) (gaussianReal 0 1) :=
      ⟨by fun_prop, by rw [stdGaussian_map_inner, hnn]⟩
    exact h2.comp h1
  have hpre : {ω : ι → ℝ | ⟪u, WithLp.toLp 2 ω⟫ = 0} =
      (fun ω => ⟪u, WithLp.toLp 2 ω⟫) ⁻¹' ({0} : Set ℝ) := rfl
  rw [hpre, hmp.measureReal_preimage (measurableSet_singleton 0).nullMeasurableSet,
    measureReal_def, measure_singleton, ENNReal.toReal_zero]

end ProbabilityTheory

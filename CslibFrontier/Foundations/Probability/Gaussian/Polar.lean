/-
Copyright (c) 2026 Samuel Schlesinger, Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vincent Liew
-/

module
-- upstream: candidate (Mathlib, a new file in `Mathlib/Probability/Distributions/Gaussian/`)

public import CslibFrontier.Init
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Planar standard Gaussian probabilities in polar coordinates

The product of two standard Gaussian measures becomes a radial weight
`r exp (-r² / 2) / (2π)` times Lebesgue measure in the angle. This lets one integrate the angular
section of a planar event at each radius. Integrating the radial weight over a tail gives
`exp (-a² / 2) / (2π)`.
-/

public section

open MeasureTheory Real Set Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

/-- The planar standard Gaussian density in polar coordinates, including the factor `r` from the
Jacobian. -/
@[expose] noncomputable def planarGaussianRadialWeight (r : ℝ) : ℝ :=
  (2 * π)⁻¹ * (r * exp (-(r ^ 2) / 2))

private theorem integrable_radialGauss :
    Integrable fun r : ℝ => r * exp (-(r ^ 2) / 2) :=
  (integrable_mul_exp_neg_mul_sq (b := 2⁻¹) (by norm_num)).congr
    (ae_of_all _ fun _ => by simp only [div_eq_mul_inv, neg_mul, mul_comm (2 : ℝ)⁻¹])

/-- The polar weight, extended by the same formula to the real line, is integrable. -/
theorem integrable_planarGaussianRadialWeight : Integrable planarGaussianRadialWeight :=
  integrable_radialGauss.const_mul _

/-- The integral of the polar weight over the radial tail above `a`. -/
theorem integral_Ioi_planarGaussianRadialWeight (a : ℝ) :
    ∫ r in Ioi a, planarGaussianRadialWeight r = (2 * π)⁻¹ * exp (-(a ^ 2) / 2) := by
  simp only [planarGaussianRadialWeight, integral_const_mul]
  congr 1
  have hderiv : ∀ r ∈ Ici a, HasDerivAt (fun x => -exp (-(x ^ 2) / 2))
      (r * exp (-(r ^ 2) / 2)) r := fun r _ =>
    (((hasDerivAt_pow 2 r).neg.div_const 2).exp.neg).congr_deriv
      (by simp only [Pi.neg_apply]; ring)
  have hquad : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)).atBot_div_const two_pos
  have htend : Tendsto (fun x : ℝ => -exp (-(x ^ 2) / 2)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hquad).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrable_radialGauss.integrableOn htend]
  simp only [zero_sub, neg_neg]

private theorem gaussianPDFReal_mul_polar (r φ : ℝ) :
    gaussianPDFReal 0 1 (r * cos φ) * gaussianPDFReal 0 1 (r * sin φ) =
      (2 * π)⁻¹ * exp (-(r ^ 2) / 2) := by
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
  rw [mul_mul_mul_comm, ← mul_inv, mul_self_sqrt (by positivity), ← exp_add]
  congr 2
  rw [← add_div, ← neg_add, mul_pow, mul_pow, ← mul_add, add_comm (cos φ ^ 2),
    sin_sq_add_cos_sq, mul_one]

/-- The standard planar Gaussian probability of an event integrates the angular section of the
event against the radial weight. -/
theorem measureReal_prod_gaussianReal_polar {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real A =
      ∫ r in Ioi (0 : ℝ), planarGaussianRadialWeight r *
        ∫ φ in Ioo (-π) π, A.indicator (fun _ => (1 : ℝ)) (r * cos φ, r * sin φ) := by
  rw [← integral_indicator_one hA]
  change ∫ z, A.indicator (fun _ => (1 : ℝ)) z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    integral_withDensity_eq_integral_toReal_smul]
  · rw [← Measure.volume_eq_prod, ← integral_comp_polarCoord_symm, polarCoord_target]
    let f : ℝ × ℝ → ℝ := fun p => planarGaussianRadialWeight p.1 *
      A.indicator (fun _ => (1 : ℝ)) (p.1 * cos p.2, p.1 * sin p.2)
    calc
      _ = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, f p :=
        setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p _ => by
          simp only [polarCoord_symm_apply, ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul,
            gaussianPDFReal_mul_polar, planarGaussianRadialWeight, f]
          ac_rfl
      _ = _ := by
        rw [Measure.volume_eq_prod]
        have hf_int : IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) (volume.prod volume) := by
          rw [IntegrableOn, ← Measure.prod_restrict]
          refine (integrable_planarGaussianRadialWeight.integrableOn.norm.mul_prod
            (integrable_const (1 : ℝ))).mono' ?_ (ae_of_all _ fun p => ?_)
          · have hrad : Measurable planarGaussianRadialWeight := by
              unfold planarGaussianRadialWeight
              fun_prop
            exact ((hrad.comp measurable_fst).mul
              ((measurable_const.indicator hA).comp
                continuous_polarCoord_symm.measurable)).aestronglyMeasurable
          · simp only [f, norm_mul, mul_one]
            exact mul_le_of_le_one_right (norm_nonneg _)
              ((norm_indicator_le_norm_self _ _).trans_eq norm_one)
        rw [setIntegral_prod _ hf_int]
        exact setIntegral_congr_fun measurableSet_Ioi fun r _ => by
          dsimp only [f]
          rw [integral_const_mul]
  · exact ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd)
  · exact ae_of_all _ fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top

end ProbabilityTheory

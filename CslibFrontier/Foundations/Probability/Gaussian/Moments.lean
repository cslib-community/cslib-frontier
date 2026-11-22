/-
Copyright (c) 2026 Samuel Schlesinger, Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Real.lean`)

public import CslibFrontier.Init
public import Mathlib.Probability.Distributions.Gaussian.Real
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Low moments of the standard Gaussian

The moment generating function of the standard Gaussian is `t ↦ exp (t ^ 2 / 2)`
(`mgf_id_gaussianReal`), and the `n`th moment is its `n`th derivative at `0`
(`iteratedDeriv_mgf_zero`). Differentiating four times gives `E[z³] = 0` and `E[z⁴] = 3`, the
moments used by the Invariance Principle [O'Donnell, Section 11.6][ODonnell2014]. By
Cauchy–Schwarz, the third absolute moment is at most `√3 ≤ 2`; the book's exact value is
`2 √(2/π)` [O'Donnell, Section 11.5, proof of the Variant Berry–Esseen Theorem][ODonnell2014].
The mean of `z` on the tail `z > t` is the density there, `E[z · 1{z > t}] = φ(t)`, since `-φ` is
an antiderivative of `z φ(z)` (`hasDerivAt_gaussianPDFReal`); by symmetry the first absolute
moment is `E[|z|] = 2 φ(0) = √(2 / π)` [O'Donnell, Section 5.2, equation (5.4)][ODonnell2014].

## Main results

* `ProbabilityTheory.integral_pow_gaussianReal_eq_iteratedDeriv`: the `n`th moment of the standard
  Gaussian is the `n`th derivative of `exp (t ^ 2 / 2)` at `0`.
* `ProbabilityTheory.integral_sq_gaussianReal`, `ProbabilityTheory.integral_pow_three_gaussianReal`,
  `ProbabilityTheory.integral_pow_four_gaussianReal`: `E[z²] = 1`, `E[z³] = 0`, `E[z⁴] = 3`.
* `ProbabilityTheory.integral_abs_pow_three_gaussianReal_le`: `E|z|³ ≤ 2`.
* `ProbabilityTheory.HasLaw.integral_eq_zero_of_gaussianReal`,
  `ProbabilityTheory.HasLaw.integral_sq_eq_one_of_gaussianReal`,
  `ProbabilityTheory.HasLaw.integral_pow_three_eq_zero_of_gaussianReal`: the moments of a random
  variable with standard Gaussian law.
* `ProbabilityTheory.setIntegral_Ioi_id_gaussianReal`: `E[z · 1{z > t}] = φ(t)`.
* `ProbabilityTheory.integral_abs_gaussianReal`: `E[|z|] = √(2 / π)`.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Set Filter Topology
open scoped NNReal

namespace ProbabilityTheory

/-- Differentiating `p t · exp (t ^ 2 / 2)`. -/
private theorem deriv_mul_exp_half_sq {p p' : ℝ → ℝ} (hp : ∀ t, HasDerivAt p (p' t) t) :
    deriv (fun t => p t * exp (t ^ 2 / 2)) = fun t => (p' t + t * p t) * exp (t ^ 2 / 2) := by
  funext t
  have hE : HasDerivAt (fun t => exp (t ^ 2 / 2)) (exp (t ^ 2 / 2) * t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert this using 1; push_cast; ring
  exact ((hp t).mul hE).deriv.trans (by ring)

private theorem iteratedDeriv_three_exp_half_sq :
    iteratedDeriv 3 (fun t => exp (t ^ 2 / 2)) = fun t => (3 * t + t ^ 3) * exp (t ^ 2 / 2) := by
  have h0 : (fun t => exp (t ^ 2 / 2)) = fun t => (fun _ => (1 : ℝ)) t * exp (t ^ 2 / 2) := by
    simp
  have h1 : iteratedDeriv 1 (fun t => exp (t ^ 2 / 2)) = fun t => t * exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_one, h0, deriv_mul_exp_half_sq (p' := fun _ => 0)
      fun t => hasDerivAt_const t 1]
    simp
  have h2 : iteratedDeriv 2 (fun t => exp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * exp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, h1, deriv_mul_exp_half_sq (p' := fun _ => 1) hasDerivAt_id']
    funext t; ring
  rw [iteratedDeriv_succ, h2, deriv_mul_exp_half_sq (p' := fun t => 2 * t)
    fun t => by simpa using ((hasDerivAt_pow 2 t).const_add 1)]
  funext t; ring

private theorem iteratedDeriv_four_exp_half_sq :
    iteratedDeriv 4 (fun t => exp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * exp (t ^ 2 / 2) := by
  rw [iteratedDeriv_succ, iteratedDeriv_three_exp_half_sq,
    deriv_mul_exp_half_sq (p' := fun t => 3 + 3 * t ^ 2) fun t => by
      convert ((hasDerivAt_id' t).const_mul 3).add (hasDerivAt_pow 3 t) using 1; norm_num]
  funext t; ring

/-- The `n`th moment of the standard Gaussian is the `n`th derivative of its moment generating
function `t ↦ exp (t ^ 2 / 2)` at `0`. -/
theorem integral_pow_gaussianReal_eq_iteratedDeriv (n : ℕ) :
    ∫ x, x ^ n ∂gaussianReal 0 1 = iteratedDeriv n (fun t => exp (t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1)
    (by simp [integrableExpSet_id_gaussianReal]) n
  rw [mgf_id_gaussianReal] at h
  simpa using h.symm

/-- The second moment of the standard Gaussian is `1`. -/
theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_of_integral_eq_zero (memLp_id_gaussianReal 2).aemeasurable
    integral_id_gaussianReal] at h
  simpa using h

/-- The third moment of the standard Gaussian is `0`. -/
theorem integral_pow_three_gaussianReal : ∫ x, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  rw [integral_pow_gaussianReal_eq_iteratedDeriv, iteratedDeriv_three_exp_half_sq]; simp

/-- The fourth moment of the standard Gaussian is `3`. -/
theorem integral_pow_four_gaussianReal : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  rw [integral_pow_gaussianReal_eq_iteratedDeriv, iteratedDeriv_four_exp_half_sq]; simp

/-- The third absolute moment of the standard Gaussian is at most `2`: by Cauchy–Schwarz,
`(E|z|³)² ≤ E[z²] E[z⁴] = 3`. (Its exact value is `2 √(2/π)`.) -/
theorem integral_abs_pow_three_gaussianReal_le : ∫ x, |x| ^ 3 ∂gaussianReal 0 1 ≤ 2 := by
  have h := sq_integral_abs_pow_three_le (μ := gaussianReal 0 1)
    (by exact_mod_cast memLp_id_gaussianReal (μ := 0) (v := 1) 4)
  rw [integral_sq_gaussianReal, integral_pow_four_gaussianReal, one_mul] at h
  nlinarith [integral_nonneg (μ := gaussianReal 0 1) fun x : ℝ => pow_nonneg (abs_nonneg x) 3]

/-- The mean of the standard Gaussian on the tail `z > t` is its density at `t`:
`E[z · 1{z > t}] = φ(t)`, since `-φ` is an antiderivative of `z φ(z)` that vanishes at
infinity. -/
theorem setIntegral_Ioi_id_gaussianReal (t : ℝ) :
    ∫ z in Ioi t, z ∂gaussianReal 0 1 = gaussianPDFReal 0 1 t := by
  have hφ (z : ℝ) :
      HasDerivAt (fun z => -gaussianPDFReal 0 1 z) (z * gaussianPDFReal 0 1 z) z := by
    convert (hasDerivAt_gaussianPDFReal 0 1 z).neg using 1
    simp
  have hint : Integrable (fun z => z * gaussianPDFReal 0 1 z) := by
    simpa only [id, mul_comm] using (integrable_gaussianReal_iff_integrable_mul_gaussianPDFReal
      one_ne_zero).1 ((memLp_id_gaussianReal 1).integrable le_rfl)
  -- TODO: use `tendsto_gaussianPDFReal_atTop` (Gaussian isoperimetric function branch) once it
  -- lands.
  have hlim : Tendsto (fun z => -gaussianPDFReal 0 1 z) atTop (𝓝 0) := by
    have h : Tendsto (fun z : ℝ => -(1 / 2) * z ^ 2) atTop atBot :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num)
    have h' := ((tendsto_exp_atBot.comp h).const_mul (√(2 * π))⁻¹).neg
    rw [mul_zero, neg_zero] at h'
    refine h'.congr fun z => ?_
    simp only [gaussianPDFReal_def, Function.comp_apply, NNReal.coe_one, mul_one, sub_zero]
    rw [show -(1 / 2 : ℝ) * z ^ 2 = -z ^ 2 / 2 by ring]
  rw [← integral_indicator measurableSet_Ioi, integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hind : (fun z => gaussianPDFReal 0 1 z • (Ioi t).indicator (fun z => z) z) =
      (Ioi t).indicator fun z => z * gaussianPDFReal 0 1 z := by
    ext z
    by_cases hz : z ∈ Ioi t <;> simp [hz, mul_comm]
  rw [hind, integral_indicator measurableSet_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun z _ => hφ z) hint.integrableOn hlim]
  ring

/-- The first absolute moment of the standard Gaussian is `E[|z|] = √(2 / π)`
[O'Donnell, Section 5.2, equation (5.4)][ODonnell2014]: by symmetry it is `2 E[z · 1{z > 0}]`,
which is `2 φ(0)`. -/
theorem integral_abs_gaussianReal : ∫ z, |z| ∂gaussianReal 0 1 = √(2 / π) := by
  have hid : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hpos : ∫ z, max z 0 ∂gaussianReal 0 1 = gaussianPDFReal 0 1 0 := by
    rw [← setIntegral_Ioi_id_gaussianReal, ← integral_indicator measurableSet_Ioi]
    congr 1 with z
    by_cases hz : 0 < z
    · simp [hz, hz.le]
    · simp [hz, not_lt.1 hz]
  -- The standard Gaussian is symmetric, so the negative part has the same mean.
  have hneg : ∫ z, max (-z) 0 ∂gaussianReal 0 1 = ∫ z, max z 0 ∂gaussianReal 0 1 := by
    rw [← integral_map (f := fun z => max z 0) measurable_neg.aemeasurable (by fun_prop),
      gaussianReal_map_neg, neg_zero]
  have habs (z : ℝ) : |z| = max z 0 + max (-z) 0 := by
    rcases le_total 0 z with hz | hz
    · simp [abs_of_nonneg hz, hz]
    · simp [abs_of_nonpos hz, hz]
  simp only [habs]
  rw [integral_add hid.pos_part hid.neg_part, hneg, hpos, gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [Real.sqrt_div' 2 pi_pos.le, Real.sqrt_mul (by norm_num)]
  field_simp
  norm_num

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {g : Ω → ℝ}

/-- A random variable with standard Gaussian law has mean `0`. -/
theorem HasLaw.integral_eq_zero_of_gaussianReal (hg : HasLaw g (gaussianReal 0 1) P) :
    ∫ ω, g ω ∂P = 0 := by
  rw [hg.integral_eq, integral_id_gaussianReal]

/-- A random variable with standard Gaussian law has second moment `1`. -/
theorem HasLaw.integral_sq_eq_one_of_gaussianReal (hg : HasLaw g (gaussianReal 0 1) P) :
    ∫ ω, g ω ^ 2 ∂P = 1 := by
  rw [← integral_sq_gaussianReal]
  exact hg.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)

/-- A random variable with standard Gaussian law has third moment `0`. -/
theorem HasLaw.integral_pow_three_eq_zero_of_gaussianReal (hg : HasLaw g (gaussianReal 0 1) P) :
    ∫ ω, g ω ^ 3 ∂P = 0 := by
  rw [← integral_pow_three_gaussianReal]
  exact hg.integral_comp (f := fun x : ℝ => x ^ 3) (by fun_prop)

end ProbabilityTheory

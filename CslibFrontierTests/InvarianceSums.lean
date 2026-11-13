/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

public import CslibFrontier.Foundations.BooleanAnalysis.InvarianceLevy
public import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
public import CslibFrontier.Foundations.Probability.InvarianceSums
public import CslibFrontier.Foundations.Probability.LevyDistance
public import CslibFrontier.Foundations.Probability.Multilinear.InvarianceLevy
public import CslibFrontierTests.InvarianceLipschitz
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Tests for the Invariance Principle for sums and for Lévy-distance invariance

Normalized sums `∑ xᵢ / √m` of `m` uniformly random signs against `∑ gᵢ / √m` for independent
standard Gaussians, as sums of coordinates under the product of the laws of `xᵢ / √m` and
`gᵢ / √m`. Every summand is `c z` for `c = 1 / √m` and a law `z` satisfying Hypothesis 11.65, so
`E|c z|³ ≤ 3 |c|³` and `γ_XY ≤ 6 / √m`. The tests instantiate the Invariance Principle for sums
with `ψ = cos` (bound `1 / √m`), Corollary 11.59 with the clamp `u ↦ min 1 (max 0 u)` (bound
`3 / 20` for `m = 10¹²`, below the trivial bound `1`), both inequalities of Corollary 11.61 at
`u = 0` and numerically for `m = 10¹²` (Lévy distance at most `3 / 10`, and the explicit-shift
form with `η = 1 / 10`), and Corollary 11.62 at `u = 0` (bound `9 / 20` for `m = 10¹²`, below the
trivial bound `1 / 2`). They also check values and the derivative bound of a smoothed step, and
the `δ = 0` (right-continuity) case of the general Lévy step.

For Corollary 11.70 they take the normalized linear form `∑ xᵢ / √m` of degree `1`, with variance
`1` and influences `1 / m`: signs and Gaussians have Lévy distance at most
`δ = 4 · 2 · m^(-1/5)`, which is `8 / 100` for `m = 100⁵`, well below the trivial bound `1`. They
also instantiate both cube inequalities for any function of small influences. -/

public section

namespace CslibFrontierTests.InvarianceSums

open MeasureTheory ProbabilityTheory Finset Cslib.BitString
open CslibFrontierTests.InvarianceLipschitz (linearForm linearForm_eq_zero
  multilinearInfluence_linearForm sum_ne_empty_linearForm_sq_le multilinearEval_linearForm signs
  gaussians lipschitzWith_clamp)
open scoped BigOperators

/-! ### Scaled laws -/

section Scaled

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The integral of a continuous `g` against the law of `c z` is the integral of `g (c z)`. -/
theorem integral_map_const_mul (c : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ s, g s ∂μ.map (c * ·) = ∫ s, g (c * s) ∂μ :=
  integral_map (measurable_const_mul c).aemeasurable hg.aestronglyMeasurable

/-- A scaled variable satisfying Hypothesis 11.65 is in `L³`. -/
theorem memLp_map_const_mul (hμ : HasInvarianceMoments μ) (c : ℝ) :
    MemLp id 3 (μ.map (c * ·)) :=
  (memLp_map_measure_iff aestronglyMeasurable_id (measurable_const_mul c).aemeasurable).2
    ((hμ.memLp_four.mono_exponent (by norm_num)).const_mul c)

omit [IsProbabilityMeasure μ] in
/-- A scaled variable satisfying Hypothesis 11.65 has mean `0`. -/
theorem integral_map_const_mul_id (hμ : HasInvarianceMoments μ) (c : ℝ) :
    ∫ s, s ∂μ.map (c * ·) = 0 := by
  rw [integral_map_const_mul (g := fun s => s) c continuous_id, integral_const_mul]
  simp [hμ.integral_id]

omit [IsProbabilityMeasure μ] in
/-- A scaled variable `c z` satisfying Hypothesis 11.65 has second moment `c²`. -/
theorem integral_map_const_mul_sq (hμ : HasInvarianceMoments μ) (c : ℝ) :
    ∫ s, s ^ 2 ∂μ.map (c * ·) = c ^ 2 := by
  rw [integral_map_const_mul (g := fun s => s ^ 2) c (continuous_pow 2)]
  simp only [mul_pow]
  rw [integral_const_mul, hμ.integral_sq, mul_one]

/-- `E|c z|³ ≤ 3 |c|³` for `z` satisfying Hypothesis 11.65. -/
theorem integral_map_const_mul_abs_pow_three_le (hμ : HasInvarianceMoments μ) (c : ℝ) :
    ∫ s, |s| ^ 3 ∂μ.map (c * ·) ≤ 3 * |c| ^ 3 := by
  rw [integral_map_const_mul (g := fun s => |s| ^ 3) c (continuous_abs.pow 3)]
  simp only [abs_mul, mul_pow]
  rw [integral_const_mul, mul_comm 3]
  exact mul_le_mul_of_nonneg_left hμ.integral_abs_pow_three_le (by positivity)

end Scaled

/-! ### The setting -/

/-- The law of a normalized sign `x / √m`. -/
noncomputable abbrev signLaw (m : ℕ) : Measure ℝ := rademacher.map ((√m)⁻¹ * ·)

/-- The law of a normalized Gaussian `g / √m`. -/
noncomputable abbrev gaussLaw (m : ℕ) : Measure ℝ := (gaussianReal 0 1).map ((√m)⁻¹ * ·)

/-- The coordinate laws are in `L³`. -/
theorem memLp_signLaw (m : ℕ) : MemLp id 3 (signLaw m) :=
  memLp_map_const_mul hasInvarianceMoments_rademacher _

/-- The coordinate laws are in `L³`. -/
theorem memLp_gaussLaw (m : ℕ) : MemLp id 3 (gaussLaw m) :=
  memLp_map_const_mul hasInvarianceMoments_gaussianReal _

/-- The first moments match. -/
theorem integral_signLaw (m : ℕ) : ∫ s, s ∂signLaw m = ∫ s, s ∂gaussLaw m := by
  rw [integral_map_const_mul_id hasInvarianceMoments_rademacher,
    integral_map_const_mul_id hasInvarianceMoments_gaussianReal]

/-- The second moments match. -/
theorem integral_sq_signLaw (m : ℕ) : ∫ s, s ^ 2 ∂signLaw m = ∫ s, s ^ 2 ∂gaussLaw m := by
  rw [integral_map_const_mul_sq hasInvarianceMoments_rademacher,
    integral_map_const_mul_sq hasInvarianceMoments_gaussianReal]

/-- `γ_XY = ∑ᵢ (E|xᵢ / √m|³ + E|gᵢ / √m|³) ≤ 6 / √m`. -/
theorem gamma_le (m : ℕ) (hm : 0 < m) :
    ∑ _i : Fin m, (∫ s, |s| ^ 3 ∂signLaw m + ∫ s, |s| ^ 3 ∂gaussLaw m) ≤ 6 / √m := by
  have hs : 0 < √(m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hsq : √(m : ℝ) ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  calc _ ≤ ∑ _i : Fin m, (3 * |(√(m : ℝ))⁻¹| ^ 3 + 3 * |(√(m : ℝ))⁻¹| ^ 3) :=
        sum_le_sum fun i _ => add_le_add
          (integral_map_const_mul_abs_pow_three_le hasInvarianceMoments_rademacher _)
          (integral_map_const_mul_abs_pow_three_le hasInvarianceMoments_gaussianReal _)
    _ = 6 / √m := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, abs_of_pos (inv_pos.2 hs)]
        field_simp
        rw [hsq]
        ring

/-- `γ_XY` is nonnegative. -/
theorem gamma_nonneg (m : ℕ) :
    0 ≤ ∑ _i : Fin m, (∫ s, |s| ^ 3 ∂signLaw m + ∫ s, |s| ^ 3 ∂gaussLaw m) :=
  sum_nonneg fun _ _ => add_nonneg (integral_nonneg fun _ => by positivity)
    (integral_nonneg fun _ => by positivity)

/-- `6 / √(10¹²) ≤ 10⁻⁵`. -/
theorem six_div_sqrt_le : 6 / √((10 ^ 12 : ℕ) : ℝ) ≤ 1 / 10 ^ 5 := by
  rw [show ((10 ^ 12 : ℕ) : ℝ) = (10 ^ 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- For `m = 10¹²`, `γ_XY ≤ 10⁻⁵`. -/
theorem gamma_le_big :
    ∑ _i : Fin (10 ^ 12), (∫ s, |s| ^ 3 ∂signLaw (10 ^ 12) + ∫ s, |s| ^ 3 ∂gaussLaw (10 ^ 12)) ≤
      1 / 10 ^ 5 :=
  (gamma_le _ (by norm_num)).trans six_div_sqrt_le

/-! ### The Invariance Principle for sums with `ψ = cos` -/

/-- `|E[cos(∑ xᵢ / √m)] - E[cos(∑ gᵢ / √m)]| ≤ 1 / 6 · 6 / √m = 1 / √m`. -/
theorem abs_integral_cos_sub_le (m : ℕ) (hm : 0 < m) :
    |∫ z, Real.cos (∑ i, z i) ∂Measure.pi (fun _ : Fin m => signLaw m) -
        ∫ z, Real.cos (∑ i, z i) ∂Measure.pi (fun _ : Fin m => gaussLaw m)| ≤ 1 / √m := by
  refine (abs_integral_comp_sum_sub_le _ _ (fun _ => memLp_signLaw m) (fun _ => memLp_gaussLaw m)
    (fun _ => integral_signLaw m) (fun _ => integral_sq_signLaw m)
    (Real.contDiff_cos.of_le le_top) (Real.abs_iteratedDeriv_cos_le_one 3)).trans ?_
  calc 1 / 6 * _ ≤ 1 / 6 * (6 / √m) := by gcongr; exact gamma_le m hm
    _ = 1 / √m := by ring

/-! ### Corollary 11.59 with the clamp -/

/-- Corollary 11.59 for `m = 10¹²` and the clamp: the difference of expectations is at most
`6 · (10⁻⁵)^(1/3) ≤ 3 / 20`, well below the trivial bound `1`. -/
example :
    |∫ z, min 1 (max 0 (∑ i, z i)) ∂Measure.pi (fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12)) -
      ∫ z, min 1 (max 0 (∑ i, z i)) ∂Measure.pi (fun _ : Fin (10 ^ 12) => gaussLaw (10 ^ 12))| ≤
      3 / 20 := by
  have h := abs_integral_comp_sum_sub_le_of_lipschitzWith
    (fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12)) (fun _ => gaussLaw (10 ^ 12))
    (fun _ => memLp_signLaw _) (fun _ => memLp_gaussLaw _) (fun _ => integral_signLaw _)
    (fun _ => integral_sq_signLaw _) lipschitzWith_clamp
  refine h.trans ?_
  have hr : (1 / 10 ^ 5 : ℝ) ^ (1 / 3 : ℝ) ≤ 1 / 40 := by
    rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    refine (Real.rpow_le_rpow (by norm_num) (show (1 / 10 ^ 5 : ℝ) ≤ (1 / 40) ^ 3 by norm_num)
      (by norm_num)).trans_eq ?_
    exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  calc 6 * ((1 : NNReal) : ℝ) * _ ≤ 6 * 1 * (1 / 10 ^ 5 : ℝ) ^ (1 / 3 : ℝ) := by
        rw [NNReal.coe_one]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (gamma_nonneg _) gamma_le_big (by norm_num)) (by norm_num)
    _ ≤ 3 / 20 := by linarith

/-! ### Corollary 11.61 at `u = 0` -/

/-- Both inequalities of Corollary 11.61 at `u = 0`: the distribution functions of the two
normalized sums at `0` differ by at most `ε` after a shift by `ε = 3 γ^(1/4)`. -/
example (m : ℕ) :
    let γ := ∑ _i : Fin m, (∫ s, |s| ^ 3 ∂signLaw m + ∫ s, |s| ^ 3 ∂gaussLaw m)
    (Measure.pi fun _ : Fin m => signLaw m).real {z | ∑ i, z i ≤ 0} ≤
        (Measure.pi fun _ : Fin m => gaussLaw m).real {z | ∑ i, z i ≤ 0 + 3 * γ ^ (1 / 4 : ℝ)} +
        3 * γ ^ (1 / 4 : ℝ) ∧
      (Measure.pi fun _ : Fin m => gaussLaw m).real {z | ∑ i, z i ≤ 0 - 3 * γ ^ (1 / 4 : ℝ)} -
        3 * γ ^ (1 / 4 : ℝ) ≤ (Measure.pi fun _ : Fin m => signLaw m).real {z | ∑ i, z i ≤ 0} :=
  ⟨measureReal_sum_le_le_add _ _ (fun _ => memLp_signLaw m) (fun _ => memLp_gaussLaw m)
      (fun _ => integral_signLaw m) (fun _ => integral_sq_signLaw m) 0,
    measureReal_sum_le_sub_le _ _ (fun _ => memLp_signLaw m) (fun _ => memLp_gaussLaw m)
      (fun _ => integral_signLaw m) (fun _ => integral_sq_signLaw m) 0⟩

/-! ### Corollary 11.62 at `u = 0` -/

/-- `∑ gᵢ / √m` is a standard Gaussian for `m ≥ 1`. -/
theorem hasLaw_sum_gaussLaw (m : ℕ) (hm : 0 < m) :
    HasLaw (fun z : Fin m → ℝ => ∑ i, z i) (gaussianReal 0 1)
      (Measure.pi fun _ : Fin m => gaussLaw m) := by
  have hpi : Measure.pi (fun _ : Fin m => gaussLaw m) =
      (gaussians m).map (fun z i => (√(m : ℝ))⁻¹ * z i) :=
    (Measure.pi_map_pi fun _ => (measurable_const_mul _).aemeasurable).symm
  have hnorm : ‖WithLp.toLp 2 (fun _ : Fin m => (√(m : ℝ))⁻¹)‖₊ ^ 2 = 1 := by
    refine NNReal.eq ?_
    rw [NNReal.coe_pow, coe_nnnorm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg m), sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_one]
    exact mul_inv_cancel₀ (by exact_mod_cast hm.ne')
  refine ⟨by fun_prop, ?_⟩
  rw [hpi, Measure.map_map (by fun_prop) (by fun_prop)]
  convert (pi_gaussianReal_map_dotProduct (fun _ : Fin m => (√(m : ℝ))⁻¹)).trans
    (by rw [hnorm]) using 2
  funext z
  simp [dotProduct]

/-- `(10⁻⁵)^(1/4) ≤ 1 / 10`. -/
theorem rpow_quarter_le : (1 / 10 ^ 5 : ℝ) ^ (1 / 4 : ℝ) ≤ 1 / 10 := by
  rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
  refine (Real.rpow_le_rpow (by norm_num) (show (1 / 10 ^ 5 : ℝ) ≤ (1 / 10) ^ 4 by norm_num)
    (by norm_num)).trans_eq ?_
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

/-- Corollary 11.62 for `m = 10¹²` at `u = 0`: `Pr[∑ xᵢ / √m ≤ 0]` is within
`9/2 · (10⁻⁵)^(1/4) ≤ 9 / 20` of `Φ(0)`, below the trivial bound `1 / 2` (as `Φ(0) = 1 / 2`).
The true distance is about `1 / √(2π m)`, half the probability `≈ √(2 / (π m))` that
`∑ xᵢ = 0`. -/
example : |(Measure.pi fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12)).real {z | ∑ i, z i ≤ 0} -
    cdf (gaussianReal 0 1) 0| ≤ 9 / 20 := by
  have h := abs_measureReal_sum_le_sub_cdf_le (fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12))
    (fun _ => gaussLaw (10 ^ 12)) (fun _ => memLp_signLaw _) (fun _ => memLp_gaussLaw _)
    (fun _ => integral_signLaw _) (fun _ => integral_sq_signLaw _)
    (hasLaw_sum_gaussLaw (10 ^ 12) (by norm_num)) 0
  refine h.trans ?_
  calc 9 / 2 * _ ≤ 9 / 2 * (1 / 10 ^ 5 : ℝ) ^ (1 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (gamma_nonneg _) gamma_le_big (by norm_num)) (by norm_num)
    _ ≤ 9 / 20 := by linarith [rpow_quarter_le]

/-! ### Numeric Lévy bounds at `m = 10¹²` -/

/-- Corollary 11.61 for `m = 10¹²`: `ε = 3 γ^(1/4) ≤ 3 · (10⁻⁵)^(1/4) ≤ 3 / 10`, so the
distribution functions of the two normalized sums are within Lévy distance `3 / 10`, below the
trivial bound `1`. -/
example (u : ℝ) :
    (Measure.pi fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12)).real {z | ∑ i, z i ≤ u} ≤
      (Measure.pi fun _ : Fin (10 ^ 12) => gaussLaw (10 ^ 12)).real
        {z | ∑ i, z i ≤ u + 3 / 10} + 3 / 10 := by
  have h := measureReal_sum_le_le_add (fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12))
    (fun _ => gaussLaw (10 ^ 12)) (fun _ => memLp_signLaw _) (fun _ => memLp_gaussLaw _)
    (fun _ => integral_signLaw _) (fun _ => integral_sq_signLaw _) u
  have h3 := mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow (gamma_nonneg _) gamma_le_big
    (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans rpow_quarter_le) (by norm_num : (0 : ℝ) ≤ 3)
  have hε := h3.trans_eq (by norm_num : (3 : ℝ) * (1 / 10) = 3 / 10)
  exact h.trans (add_le_add (measureReal_mono fun z hz => le_trans hz (add_le_add le_rfl hε)) hε)

/-- The explicit-shift form of Corollary 11.61 for `m = 10¹²` and `η = 1 / 10`: the error term is
`128 / 3 · γ / η³ ≤ 128 / 3 · 10⁻⁵ · 10³ ≤ 1 / 2`. -/
example (u : ℝ) :
    (Measure.pi fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12)).real {z | ∑ i, z i ≤ u} ≤
      (Measure.pi fun _ : Fin (10 ^ 12) => gaussLaw (10 ^ 12)).real
        {z | ∑ i, z i ≤ u + 1 / 10} + 1 / 2 := by
  have h := measureReal_sum_le_le_add_div_pow (fun _ : Fin (10 ^ 12) => signLaw (10 ^ 12))
    (fun _ => gaussLaw (10 ^ 12)) (fun _ => memLp_signLaw _) (fun _ => memLp_gaussLaw _)
    (fun _ => integral_signLaw _) (fun _ => integral_sq_signLaw _) u (η := 1 / 10) (by norm_num)
  refine h.trans (add_le_add le_rfl ?_)
  calc 128 / 3 * _ / (1 / 10 : ℝ) ^ 3 ≤ 128 / 3 * (1 / 10 ^ 5) / (1 / 10 : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left gamma_le_big (by norm_num))
          (by norm_num)
    _ ≤ 1 / 2 := by norm_num

/-! ### The smoothed step and the general Lévy step -/

/-- The three-fold smoothed step with `u = 0` and window `1` is `1` at `0`, `0` at `4`, and has
third derivative at most `2² / 1³ = 4`. -/
example : Real.stepSmoothing 3 0 1 0 = 1 ∧ Real.stepSmoothing 3 0 1 4 = 0 ∧
    ∀ s, |iteratedDeriv 3 (Real.stepSmoothing 3 0 1) s| ≤ 4 := by
  refine ⟨Real.stepSmoothing_eq_one_of_le one_pos le_rfl,
    Real.stepSmoothing_eq_zero_of_le one_pos (by norm_num), fun s => ?_⟩
  have h := Real.abs_iteratedDeriv_stepSmoothing_le 3 0 one_pos s
  norm_num at h
  exact h

/-- The `δ = 0` case of the general Lévy step, which goes through the right-continuity of
distribution functions: a random variable compared with itself, with `B = 0`. -/
example (P : Measure ℝ) [IsProbabilityMeasure P] (u : ℝ) :
    P.real {x | id x ≤ u} ≤ P.real {x | id x ≤ u + 0} + 0 :=
  measureReal_le_le_add_of_forall_contDiff (m := 1) (B := 0) aemeasurable_id aemeasurable_id
    (fun φ C _ _ => by simp) le_rfl (by simp) u

/-! ### Corollary 11.70: Lévy-distance invariance for polynomials -/

/-- Corollary 11.70 for the normalized linear form `∑ xᵢ / √m` (degree `1`, variance `1`,
influences `1 / m`): uniformly random signs and standard Gaussians have Lévy distance at most
`4 · 2 · (1 / m)^(1/5)`. -/
theorem levy_normalizedSum (m : ℕ) (hm : 0 < m) (u : ℝ) :
    (signs m).real {v | ∑ i, (√(m : ℝ))⁻¹ * v i ≤ u} ≤
        (gaussians m).real
          {v | ∑ i, (√(m : ℝ))⁻¹ * v i ≤ u + 4 * 2 ^ 1 * ((m : ℝ)⁻¹) ^ (1 / 5 : ℝ)} +
        4 * 2 ^ 1 * ((m : ℝ)⁻¹) ^ (1 / 5 : ℝ) ∧
      (gaussians m).real
          {v | ∑ i, (√(m : ℝ))⁻¹ * v i ≤ u - 4 * 2 ^ 1 * ((m : ℝ)⁻¹) ^ (1 / 5 : ℝ)} -
        4 * 2 ^ 1 * ((m : ℝ)⁻¹) ^ (1 / 5 : ℝ) ≤
      (signs m).real {v | ∑ i, (√(m : ℝ))⁻¹ * v i ≤ u} := by
  have hsq : ((√(m : ℝ))⁻¹) ^ 2 = (m : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hvar : ∑ _i : Fin m, ((√(m : ℝ))⁻¹) ^ 2 ≤ 1 := by
    rw [hsq, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hm']
  have hc : ∀ S, 1 < #S → linearForm (fun _ : Fin m => (√(m : ℝ))⁻¹) S = 0 :=
    fun S hS => linearForm_eq_zero _ (by omega)
  have hv := (sum_ne_empty_linearForm_sq_le _).trans hvar
  have hε : ∀ t, multilinearInfluence (linearForm fun _ : Fin m => (√(m : ℝ))⁻¹) t ≤ (m : ℝ)⁻¹ :=
    fun t => ((multilinearInfluence_linearForm _ t).trans hsq).le
  have h1 := measureReal_multilinearEval_le_le_add _ _ (fun _ => hasInvarianceMoments_rademacher)
    (fun _ => hasInvarianceMoments_gaussianReal) hc hv (by positivity) hε u
  have h2 := measureReal_multilinearEval_le_sub_le _ _ (fun _ => hasInvarianceMoments_rademacher)
    (fun _ => hasInvarianceMoments_gaussianReal) hc hv (by positivity) hε u
  simp only [multilinearEval_linearForm] at h1 h2
  exact ⟨h1, h2⟩

/-- For `m = 100⁵` variables the Lévy distance bound is `8 / 100`, well below the trivial bound
`1`. -/
example (u : ℝ) :
    (signs (100 ^ 5)).real {v | ∑ i, (√((100 ^ 5 : ℕ) : ℝ))⁻¹ * v i ≤ u} ≤
        (gaussians (100 ^ 5)).real {v | ∑ i, (√((100 ^ 5 : ℕ) : ℝ))⁻¹ * v i ≤ u + 8 / 100} +
        8 / 100 ∧
      (gaussians (100 ^ 5)).real {v | ∑ i, (√((100 ^ 5 : ℕ) : ℝ))⁻¹ * v i ≤ u - 8 / 100} -
        8 / 100 ≤ (signs (100 ^ 5)).real {v | ∑ i, (√((100 ^ 5 : ℕ) : ℝ))⁻¹ * v i ≤ u} ∧
      (8 / 100 : ℝ) < 1 := by
  have hδ : 4 * 2 ^ 1 * (((100 ^ 5 : ℕ) : ℝ)⁻¹) ^ (1 / 5 : ℝ) = 8 / 100 := by
    rw [Nat.cast_pow, ← inv_pow, show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    norm_num
  have h := levy_normalizedSum (100 ^ 5) (by norm_num) u
  rw [hδ] at h
  exact ⟨h.1, h.2, by norm_num⟩

/-- Corollary 11.70 on the cube: for a function of degree at most `k`, variance at most `1` and
influences at most `ε`, its distribution function at uniform bits and that of its Fourier
expansion at Gaussians are within Lévy distance `4 · 2ᵏ · ε^(1/5)`. -/
example (n k : ℕ) (f : (Fin n → Bool) → ℝ) (hf : totalDegree f ≤ k)
    (hvar : 𝔼 x, (f x - 𝔼 y, f y) ^ 2 ≤ 1) (ε : ℝ) (hε₀ : 0 ≤ ε)
    (hε : ∀ t, influence t f ≤ ε) (u : ℝ) :
    (dens {x | f x ≤ u} : ℝ) ≤ (gaussians n).real
        {y | multilinearEval (fourierCoeff f) y ≤ u + 4 * 2 ^ k * ε ^ (1 / 5 : ℝ)} +
        4 * 2 ^ k * ε ^ (1 / 5 : ℝ) ∧
      (gaussians n).real
          {y | multilinearEval (fourierCoeff f) y ≤ u - 4 * 2 ^ k * ε ^ (1 / 5 : ℝ)} -
        4 * 2 ^ k * ε ^ (1 / 5 : ℝ) ≤ (dens {x | f x ≤ u} : ℝ) :=
  ⟨dens_le_le_measureReal_multilinearEval_le_add _ (fun _ => hasInvarianceMoments_gaussianReal)
      hf hvar hε₀ hε u,
    measureReal_multilinearEval_le_sub_le_dens _ (fun _ => hasInvarianceMoments_gaussianReal) hf
      hvar hε₀ hε u⟩

end CslibFrontierTests.InvarianceSums

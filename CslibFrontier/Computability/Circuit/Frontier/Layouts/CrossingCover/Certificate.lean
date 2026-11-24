/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified AR(2) orthant probabilities and alternating wave-sum bounds

This module defines the stationary reversible Gaussian AR(2) Markov chain associated with
alternating sign paths on the infinite 3-regular tree (`ρ = -2√2 / 3`, conditional variance
`1 / 12`), proves its foundational properties (reversibility, normalization, integrability,
marginals, quadratic exponent decomposition), develops real-analytic Fourier derivative bounds
and shifted Gauss–Legendre polynomial quadrature error estimates, and certifies explicit rational
bounds on the alternating wave sum

`alternatingWaveSum J = ∑ j ∈ Icc 1 J, (-1) ^ (j + 1) * (3 / 2) * 2 ^ (j - 1) * altPathProb j`

through pure kernel-checked fixed-point `Nat` interval arithmetic (no `native_decide`, no `sorry`,
no custom axioms, and no `maxHeartbeats` overrides).

## Main definitions

* `Cslib.Circuits.Frontier.CrossingCover.ar2InitDensity`: bivariate stationary density with
  correlation `-2√2 / 3`.
* `Cslib.Circuits.Frontier.CrossingCover.ar2Kernel`: Gaussian AR(2) transition density with mean
  `-√2 y - x / 2` and variance `1 / 12`.
* `Cslib.Circuits.Frontier.CrossingCover.ar2JointDensity`: joint density of length `j + 1`.
* `Cslib.Circuits.Frontier.CrossingCover.ar2OrthantIntegral`: positive-orthant probability of
  `ar2JointDensity j`.
* `Cslib.Circuits.Frontier.CrossingCover.altPathProb`: alternating-path probability
  `2 * ar2OrthantIntegral j`.
* `Cslib.Circuits.Frontier.CrossingCover.alternatingWaveSum`: truncated alternating wave sum.
* `Cslib.Circuits.Frontier.CrossingCover.ar2QuadForm`,
  `Cslib.Circuits.Frontier.CrossingCover.ar2QuadDiag`: exact positive-semidefinite quadratic
  exponent and its diagonal precision entries `≤ 39`.

## Main results

* Time-reversibility, pointwise upper bounds, integrability, total mass `1`, and coordinate
  slicing of `ar2JointDensity`.
* Real Fourier derivative bound on `iteratedDeriv (2 * N) (fun x => exp (-q / 2 * (x - μ) ^ 2))`.
* Shifted Gauss–Legendre polynomial quadrature exactness, positivity of weights, and Hermite
  interpolation error theorem via Rolle's theorem.
* Anisotropic box truncation tail bounds via exact 2- and 3-marginal reduction.
* `Cslib.Circuits.Frontier.CrossingCover.alternatingWaveSum_13_lt`: the certified upper bound
  `alternatingWaveSum 13 < 130649 / 1000000`.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset MeasureTheory Real
open scoped BigOperators Interval

/-! ### AR(2) density, Markov kernel, and basic properties -/

section AR2Density

/-- Stationary bivariate Gaussian density with unit marginals and correlation `-2√2 / 3`. -/
noncomputable def ar2InitDensity (x y : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) *
    Real.exp (-(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y)

/-- Gaussian AR(2) transition kernel with conditional mean `-√2 y - x / 2` and variance `1 / 12`. -/
noncomputable def ar2Kernel (x y z : ℝ) : ℝ :=
  Real.sqrt (6 / Real.pi) *
    Real.exp (-6 * (z + Real.sqrt 2 * y + x / 2) ^ 2)

/-- Joint density of the first `j + 1` coordinates of the stationary AR(2) process. For `j = 0`
this is the standard 1D Gaussian density; for `j ≥ 1` it is the product of `ar2InitDensity` and
`j - 1` transition factors `ar2Kernel`. -/
noncomputable def ar2JointDensity : (j : ℕ) → (Fin (j + 1) → ℝ) → ℝ
  | 0, x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x 0) ^ 2 / 2)
  | k + 1, x =>
      ar2InitDensity (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) *
        ∏ i : Fin k, ar2Kernel (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩)
          (x ⟨i.1 + 2, by omega⟩)

/-- Positive-orthant integral `∫_{x > 0} ar2JointDensity j x dx` over `Fin (j + 1) → ℝ`. -/
noncomputable def ar2OrthantIntegral (j : ℕ) : ℝ :=
  ∫ x in Set.pi Set.univ (fun _ : Fin (j + 1) => Set.Ioi (0 : ℝ)),
    ar2JointDensity j x ∂(Measure.pi fun _ : Fin (j + 1) => volume)

/-- Alternating-sign path probability `2 * ar2OrthantIntegral j` for a path of `j` edges. -/
noncomputable def altPathProb (j : ℕ) : ℝ :=
  2 * ar2OrthantIntegral j

/-- Truncated alternating wave sum up to path length `J`. -/
noncomputable def alternatingWaveSum (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 J,
    (-1 : ℝ) ^ (j + 1) * (3 / 2) * (2 : ℝ) ^ (j - 1) * altPathProb j

/-- `ar2InitDensity x y` is strictly positive for all `x, y : ℝ`. -/
theorem ar2InitDensity_pos (x y : ℝ) : 0 < ar2InitDensity x y := by
  unfold ar2InitDensity
  positivity

/-- `ar2InitDensity x y` is nonnegative for all `x, y : ℝ`. -/
theorem ar2InitDensity_nonneg (x y : ℝ) : 0 ≤ ar2InitDensity x y :=
  (ar2InitDensity_pos x y).le

/-- `ar2Kernel x y z` is strictly positive for all `x, y, z : ℝ`. -/
theorem ar2Kernel_pos (x y z : ℝ) : 0 < ar2Kernel x y z := by
  unfold ar2Kernel
  positivity

/-- `ar2Kernel x y z` is nonnegative for all `x, y, z : ℝ`. -/
theorem ar2Kernel_nonneg (x y z : ℝ) : 0 ≤ ar2Kernel x y z :=
  (ar2Kernel_pos x y z).le

/-- `ar2JointDensity j x` is strictly positive for all `j` and `x`. -/
theorem ar2JointDensity_pos (j : ℕ) (x : Fin (j + 1) → ℝ) :
    0 < ar2JointDensity j x := by
  cases j with
  | zero =>
      unfold ar2JointDensity
      positivity
  | succ k =>
      unfold ar2JointDensity
      exact mul_pos (ar2InitDensity_pos _ _)
        (Finset.prod_pos fun i _ => ar2Kernel_pos _ _ _)

/-- `ar2JointDensity j x` is nonnegative for all `j` and `x`. -/
theorem ar2JointDensity_nonneg (j : ℕ) (x : Fin (j + 1) → ℝ) :
    0 ≤ ar2JointDensity j x :=
  (ar2JointDensity_pos j x).le

/-- `ar2InitDensity` is symmetric in its two arguments. -/
theorem ar2InitDensity_symm (x y : ℝ) : ar2InitDensity x y = ar2InitDensity y x := by
  unfold ar2InitDensity
  congr 2
  ring

/-- `ar2InitDensity` is even under joint negation. -/
theorem ar2InitDensity_neg (x y : ℝ) : ar2InitDensity (-x) (-y) = ar2InitDensity x y := by
  unfold ar2InitDensity
  congr 2
  ring

/-- `ar2Kernel` is even under joint negation. -/
theorem ar2Kernel_neg (x y z : ℝ) : ar2Kernel (-x) (-y) (-z) = ar2Kernel x y z := by
  unfold ar2Kernel
  congr 2
  ring

/-- `ar2JointDensity` is even under coordinatewise negation. -/
theorem ar2JointDensity_neg (j : ℕ) (x : Fin (j + 1) → ℝ) :
    ar2JointDensity j (-x) = ar2JointDensity j x := by
  cases j with
  | zero =>
      simp [ar2JointDensity]
  | succ k =>
      simp only [ar2JointDensity, Pi.neg_apply, ar2InitDensity_neg, ar2Kernel_neg]

/-- Upper bound `ar2InitDensity x y ≤ 3 / (2 * π)`. -/
theorem ar2InitDensity_le (x y : ℝ) : ar2InitDensity x y ≤ 3 / (2 * Real.pi) := by
  unfold ar2InitDensity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hexp : -(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y ≤ 0 := by
    have h1 : 0 ≤ 9 / 2 * (x + 2 * Real.sqrt 2 / 3 * y) ^ 2 + y ^ 2 / 2 := by positivity
    have h2 : -(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y =
        -(9 / 2 * (x + 2 * Real.sqrt 2 / 3 * y) ^ 2 + y ^ 2 / 2) := by
      linear_combination (2 * y ^ 2) * hsq
    linarith
  calc (3 / (2 * Real.pi)) * Real.exp (-(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y)
      ≤ (3 / (2 * Real.pi)) * Real.exp 0 := by gcongr
    _ = 3 / (2 * Real.pi) := by simp

/-- Upper bound `ar2Kernel x y z ≤ √(6 / π)`. -/
theorem ar2Kernel_le (x y z : ℝ) : ar2Kernel x y z ≤ Real.sqrt (6 / Real.pi) := by
  unfold ar2Kernel
  have hexp : -6 * (z + Real.sqrt 2 * y + x / 2) ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (z + Real.sqrt 2 * y + x / 2)]
  calc Real.sqrt (6 / Real.pi) * Real.exp (-6 * (z + Real.sqrt 2 * y + x / 2) ^ 2)
      ≤ Real.sqrt (6 / Real.pi) * Real.exp 0 := by gcongr
    _ = Real.sqrt (6 / Real.pi) := by simp

/-- Global pointwise upper bound on `ar2JointDensity j x` for `j ≥ 1`. -/
theorem ar2JointDensity_le {j : ℕ} (hj : 1 ≤ j) (x : Fin (j + 1) → ℝ) :
    ar2JointDensity j x ≤ (3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ (j - 1) := by
  cases j with
  | zero => omega
  | succ k =>
      simp only [ar2JointDensity, Nat.add_sub_cancel]
      have hprod : ∏ i : Fin k, ar2Kernel (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩)
          (x ⟨i.1 + 2, by omega⟩) ≤ Real.sqrt (6 / Real.pi) ^ k := by
        have hstep : ∀ s : Finset (Fin k),
            ∏ i ∈ s, ar2Kernel (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩)
              (x ⟨i.1 + 2, by omega⟩) ≤ Real.sqrt (6 / Real.pi) ^ s.card := by
          intro s
          classical
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih =>
              rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
              exact mul_le_mul (ar2Kernel_le _ _ _) ih
                (Finset.prod_nonneg fun _ _ => ar2Kernel_nonneg _ _ _) (by positivity)
        simpa [Fintype.card_fin] using hstep Finset.univ
      exact mul_le_mul (ar2InitDensity_le _ _) hprod
        (Finset.prod_nonneg fun i _ => ar2Kernel_nonneg _ _ _) (by positivity)

/-- Time-reversibility of the stationary AR(2) triple density. -/
theorem ar2InitDensity_mul_ar2Kernel_symm (x y z : ℝ) :
    ar2InitDensity x y * ar2Kernel x y z = ar2InitDensity y z * ar2Kernel z y x := by
  unfold ar2InitDensity ar2Kernel
  have hL : (3 / (2 * Real.pi)) * Real.exp (-(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y) *
      (Real.sqrt (6 / Real.pi) * Real.exp (-6 * (z + Real.sqrt 2 * y + x / 2) ^ 2)) =
      (3 / (2 * Real.pi) * Real.sqrt (6 / Real.pi)) *
        (Real.exp (-(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y) *
          Real.exp (-6 * (z + Real.sqrt 2 * y + x / 2) ^ 2)) := by ring
  have hR : (3 / (2 * Real.pi)) * Real.exp (-(9 / 2) * (y ^ 2 + z ^ 2) - 6 * Real.sqrt 2 * y * z) *
      (Real.sqrt (6 / Real.pi) * Real.exp (-6 * (x + Real.sqrt 2 * y + z / 2) ^ 2)) =
      (3 / (2 * Real.pi) * Real.sqrt (6 / Real.pi)) *
        (Real.exp (-(9 / 2) * (y ^ 2 + z ^ 2) - 6 * Real.sqrt 2 * y * z) *
          Real.exp (-6 * (x + Real.sqrt 2 * y + z / 2) ^ 2)) := by ring
  rw [hL, hR, ← Real.exp_add, ← Real.exp_add]
  congr 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination 0 * hsq

/-- Formula rewriting `ar2JointDensity (k + 2) x` by peeling off the last coordinate. -/
theorem ar2JointDensity_succ (k : ℕ) (x : Fin (k + 3) → ℝ) :
    ar2JointDensity (k + 2) x =
      ar2JointDensity (k + 1) (fun i => x i.castSucc) *
        ar2Kernel (x ⟨k, by omega⟩) (x ⟨k + 1, by omega⟩) (x ⟨k + 2, by omega⟩) := by
  simp only [ar2JointDensity]
  rw [Fin.prod_univ_castSucc, mul_assoc]
  rfl

/-- Formula rewriting `ar2JointDensity (k + 2) x` by peeling off the first coordinate using
time-reversibility. -/
theorem ar2JointDensity_succ_head (k : ℕ) (x : Fin (k + 3) → ℝ) :
    ar2JointDensity (k + 2) x =
      ar2Kernel (x ⟨2, by omega⟩) (x ⟨1, by omega⟩) (x ⟨0, by omega⟩) *
        ar2JointDensity (k + 1) (fun i => x i.succ) := by
  simp only [ar2JointDensity]
  rw [Fin.prod_univ_succ]
  have hrev : ar2InitDensity (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) *
      ar2Kernel (x ⟨(0 : Fin (k + 1)).1, by omega⟩) (x ⟨(0 : Fin (k + 1)).1 + 1, by omega⟩)
        (x ⟨(0 : Fin (k + 1)).1 + 2, by omega⟩) =
      ar2InitDensity (x (Fin.succ ⟨0, by omega⟩)) (x (Fin.succ ⟨1, by omega⟩)) *
        ar2Kernel (x ⟨2, by omega⟩) (x ⟨1, by omega⟩) (x ⟨0, by omega⟩) :=
    ar2InitDensity_mul_ar2Kernel_symm (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) (x ⟨2, by omega⟩)
  have hprod : ∏ i : Fin k, ar2Kernel (x ⟨i.succ.1, by omega⟩) (x ⟨i.succ.1 + 1, by omega⟩)
      (x ⟨i.succ.1 + 2, by omega⟩) =
      ∏ i : Fin k, ar2Kernel (x (Fin.succ ⟨i.1, by omega⟩))
        (x (Fin.succ ⟨i.1 + 1, by omega⟩)) (x (Fin.succ ⟨i.1 + 2, by omega⟩)) := rfl
  rw [hprod, ← mul_assoc, hrev]
  ring

/-- Continuity of `ar2InitDensity`. -/
theorem ar2InitDensity_continuous : Continuous fun p : ℝ × ℝ => ar2InitDensity p.1 p.2 := by
  unfold ar2InitDensity
  fun_prop

/-- Continuity of `ar2Kernel`. -/
theorem ar2Kernel_continuous :
    Continuous fun (p : ℝ × ℝ × ℝ) => let (x, y, z) := p; ar2Kernel x y z := by
  unfold ar2Kernel
  fun_prop

/-- Continuity of `ar2JointDensity j`. -/
theorem ar2JointDensity_continuous (j : ℕ) : Continuous (ar2JointDensity j) := by
  cases j with
  | zero =>
      change Continuous fun x : Fin 1 → ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x 0) ^ 2 / 2)
      fun_prop
  | succ k =>
      change Continuous fun x : Fin (k + 2) → ℝ =>
        ar2InitDensity (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) *
          ∏ i : Fin k, ar2Kernel (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩)
            (x ⟨i.1 + 2, by omega⟩)
      refine Continuous.mul ?_ ?_
      · exact ar2InitDensity_continuous.comp
          (Continuous.prodMk (continuous_apply (⟨0, by omega⟩ : Fin (k + 2)))
            (continuous_apply (⟨1, by omega⟩ : Fin (k + 2))))
      · refine Finset.univ.induction_on (by exact continuous_const) fun i s hi hs => ?_
        simp only [Finset.prod_insert hi]
        refine Continuous.mul ?_ hs
        exact ar2Kernel_continuous.comp
          (Continuous.prodMk (continuous_apply (⟨i.1, by omega⟩ : Fin (k + 2)))
            (Continuous.prodMk (continuous_apply (⟨i.1 + 1, by omega⟩ : Fin (k + 2)))
              (continuous_apply (⟨i.1 + 2, by omega⟩ : Fin (k + 2)))))

/-- Factorization of `ar2InitDensity x y` as `N(0, 1)` marginal times conditional Gaussian. -/
theorem ar2InitDensity_eq_std_mul_cond (x y : ℝ) :
    ar2InitDensity x y =
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) *
        ((Real.sqrt (2 * Real.pi / 9))⁻¹ *
          Real.exp (-(9 / 2) * (y + 2 * Real.sqrt 2 / 3 * x) ^ 2)) := by
  unfold ar2InitDensity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hnorm : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi / 9))⁻¹ =
      3 / (2 * Real.pi) := by
    rw [Real.sqrt_div (by positivity), h9, ← mul_inv]
    have hmul : Real.sqrt (2 * Real.pi) * (Real.sqrt (2 * Real.pi) / 3) = 2 * Real.pi / 3 := by
      rw [← mul_div_assoc, Real.mul_self_sqrt (by positivity)]
    rw [hmul, inv_div]
  rw [mul_mul_mul_comm (Real.sqrt (2 * Real.pi))⁻¹, hnorm, ← Real.exp_add]
  congr 2
  linear_combination (2 * x ^ 2) * hsq

/-- Integrability of `z ↦ ar2Kernel x y z`. -/
theorem ar2Kernel_integrable (x y : ℝ) : Integrable (fun z => ar2Kernel x y z) := by
  have hfn : (fun z : ℝ => ar2Kernel x y z) =
      fun z : ℝ => Real.sqrt (6 / Real.pi) *
        Real.exp (-6 * (z + (Real.sqrt 2 * y + x / 2)) ^ 2) := by
    ext z; unfold ar2Kernel; congr 3; ring
  rw [hfn]
  exact ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 6)).comp_add_right
    (Real.sqrt 2 * y + x / 2)).const_mul _

/-- Total integral `∫ z, ar2Kernel x y z = 1`. -/
theorem ar2Kernel_integral_eq_one (x y : ℝ) : ∫ z : ℝ, ar2Kernel x y z = 1 := by
  unfold ar2Kernel
  have hfn : (fun z : ℝ => Real.exp (-6 * (z + Real.sqrt 2 * y + x / 2) ^ 2)) =
      fun z : ℝ => Real.exp (-6 * (z + (Real.sqrt 2 * y + x / 2)) ^ 2) := by
    ext z; congr 2; ring
  rw [integral_const_mul, hfn, integral_add_right_eq_self
    (fun z => Real.exp (-6 * z ^ 2)) (Real.sqrt 2 * y + x / 2), integral_gaussian]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [← Real.sqrt_mul (by positivity)]
  have h1 : (6 / Real.pi) * (Real.pi / 6) = 1 := by field_simp
  rw [h1, Real.sqrt_one]

/-- Marginal integral of `ar2InitDensity x y` over `y` is the standard 1D Gaussian density. -/
theorem ar2InitDensity_integral_right (x : ℝ) :
    ∫ y : ℝ, ar2InitDensity x y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp_rw [ar2InitDensity_eq_std_mul_cond x]
  rw [integral_const_mul, integral_const_mul,
    integral_add_right_eq_self (fun y => Real.exp (-(9 / 2) * y ^ 2)) (2 * Real.sqrt 2 / 3 * x),
    integral_gaussian]
  have hnorm : (Real.sqrt (2 * Real.pi / 9))⁻¹ * Real.sqrt (Real.pi / (9 / 2)) = 1 := by
    have heq : Real.pi / (9 / 2) = 2 * Real.pi / 9 := by ring
    rw [heq, inv_mul_cancel₀ (by positivity)]
  rw [hnorm, mul_one]

/-- Total integral of the standard 1D Gaussian density `ar2JointDensity 0` is `1`. -/
theorem ar2JointDensity_zero_integrable :
    Integrable (ar2JointDensity 0) (Measure.pi fun _ : Fin 1 => volume) := by
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hmp : MeasurePreserving e (Measure.pi fun _ : Fin 1 => volume) volume :=
    MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  have hint : Integrable (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) := by
    have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (Real.sqrt (2 * Real.pi))⁻¹
    have h2 : (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * t ^ 2)) =
        fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
      ext t; congr 2; ring
    rwa [← h2]
  exact (hmp.integrable_comp_emb e.measurableEmbedding).mpr hint

/-- Total integral of `ar2JointDensity j` as a `lintegral` equals `1`. -/
theorem lintegral_ar2JointDensity_eq_one (j : ℕ) :
    ∫⁻ x : Fin (j + 1) → ℝ, ENNReal.ofReal (ar2JointDensity j x)
      ∂(Measure.pi fun _ : Fin (j + 1) => volume) = 1 := by
  induction j with
  | zero =>
      have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ)
          (Measure.pi fun _ : Fin 1 => volume) volume :=
        MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
      have hchange : ∫⁻ x : Fin 1 → ℝ, ENNReal.ofReal (ar2JointDensity 0 x)
          ∂(Measure.pi fun _ : Fin 1 => volume) =
          ∫⁻ t : ℝ, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) :=
        hmp.lintegral_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
          (fun t : ℝ => ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)))
      rw [hchange]
      have h2 : (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) =
          fun t => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * t ^ 2) := by
        ext t; congr 2; ring
      have hint :
          Integrable (fun t : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) := by
        rw [h2]; exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun t => by positivity)]
      have hval : ∫ t : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) = 1 := by
        rw [h2, integral_const_mul, integral_gaussian]
        have heq : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
        rw [heq, inv_mul_cancel₀ (by positivity)]
      rw [hval, ENNReal.ofReal_one]
  | succ k ih =>
      let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => ℝ) (Fin.last (k + 1))
      have hmp : MeasurePreserving split
          (Measure.pi fun _ : Fin (k + 2) => volume)
          (volume.prod (Measure.pi fun _ : Fin (k + 1) => volume)) :=
        MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k + 2) => ℝ)
          (Fin.last (k + 1))
      cases k with
      | zero =>
          have hker (t : ℝ) : ∫⁻ y : ℝ, ENNReal.ofReal (ar2InitDensity t y) =
              ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) := by
            have hi : Integrable (fun y : ℝ => ar2InitDensity t y) := by
              simp_rw [ar2InitDensity_eq_std_mul_cond t]
              exact ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 9 / 2)).comp_add_right
                (2 * Real.sqrt 2 / 3 * t)).const_mul _ |>.const_mul _
            rw [← ofReal_integral_eq_lintegral_ofReal hi
              (ae_of_all _ fun y => ar2InitDensity_nonneg t y),
              ar2InitDensity_integral_right]
          have h1 := hmp.lintegral_comp_emb split.measurableEmbedding
            (fun p : ℝ × (Fin 1 → ℝ) => ENNReal.ofReal (ar2InitDensity (p.2 0) p.1))
          have hrewrite : ∫⁻ x : Fin 2 → ℝ, ENNReal.ofReal (ar2JointDensity 1 x)
              ∂(Measure.pi fun _ : Fin 2 => volume) =
              ∫⁻ p : ℝ × (Fin 1 → ℝ), ENNReal.ofReal (ar2InitDensity (p.2 0) p.1)
                ∂(volume.prod (Measure.pi fun _ : Fin 1 => volume)) := by
            rw [← h1]
            refine lintegral_congr fun x => ?_
            change ENNReal.ofReal (ar2InitDensity (x 0) (x 1) * 1) =
              ENNReal.ofReal (ar2InitDensity (Fin.removeNth (Fin.last 1) x 0) (x (Fin.last 1)))
            rw [mul_one]
            rfl
          rw [hrewrite, lintegral_prod_symm]
          · simp_rw [hker]
            exact ih
          · have hc : Continuous fun p : ℝ × (Fin 1 → ℝ) => ar2InitDensity (p.2 0) p.1 :=
              ar2InitDensity_continuous.comp
                (Continuous.prodMk ((continuous_apply (0 : Fin 1)).comp continuous_snd)
                  continuous_fst)
            exact (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
      | succ m =>
          have hkernel_l (a b : ℝ) : ∫⁻ z : ℝ, ENNReal.ofReal (ar2Kernel a b z) = 1 := by
            rw [← ofReal_integral_eq_lintegral_ofReal (ar2Kernel_integrable a b)
              (ae_of_all _ fun z => ar2Kernel_nonneg a b z),
              ar2Kernel_integral_eq_one, ENNReal.ofReal_one]
          let g : ℝ × (Fin (m + 2) → ℝ) → ℝ := fun p =>
            ar2JointDensity (m + 1) p.2 *
              ar2Kernel (p.2 ⟨m, by omega⟩) (p.2 ⟨m + 1, by omega⟩) p.1
          have hg_meas : Continuous g := by
            refine (ar2JointDensity_continuous (m + 1) |>.comp continuous_snd).mul ?_
            exact ar2Kernel_continuous.comp
              (Continuous.prodMk
                ((continuous_apply (⟨m, by omega⟩ : Fin (m + 2))).comp continuous_snd)
                (Continuous.prodMk
                  ((continuous_apply (⟨m + 1, by omega⟩ : Fin (m + 2))).comp continuous_snd)
                  continuous_fst))
          have h1 := hmp.lintegral_comp_emb split.measurableEmbedding
            (fun p : ℝ × (Fin (m + 2) → ℝ) => ENNReal.ofReal (g p))
          have hrewrite : ∫⁻ x : Fin (m + 3) → ℝ, ENNReal.ofReal (ar2JointDensity (m + 2) x)
              ∂(Measure.pi fun _ : Fin (m + 3) => volume) =
              ∫⁻ p : ℝ × (Fin (m + 2) → ℝ), ENNReal.ofReal (g p)
                ∂(volume.prod (Measure.pi fun _ : Fin (m + 2) => volume)) := by
            rw [← h1]
            refine lintegral_congr fun x => ?_
            rw [ar2JointDensity_succ m x]
            have hrem : (split x).2 = fun i : Fin (m + 2) => x i.castSucc := by
              ext i
              change x ((Fin.last (m + 2)).succAbove i) = x i.castSucc
              rw [Fin.succAbove_last]
            have hfst : (split x).1 = x ⟨m + 2, by omega⟩ := rfl
            change ENNReal.ofReal _ = ENNReal.ofReal (g (split x))
            simp only [g, hrem, hfst]
            rfl
          rw [hrewrite, lintegral_prod_symm (fun p => ENNReal.ofReal (g p))
            (by exact (ENNReal.measurable_ofReal.comp hg_meas.measurable).aemeasurable)]
          have hinner : ∀ y : Fin (m + 2) → ℝ,
              ∫⁻ z : ℝ, ENNReal.ofReal (g (z, y)) = ENNReal.ofReal (ar2JointDensity (m + 1) y) := by
            intro y
            simp_rw [g, ENNReal.ofReal_mul (ar2JointDensity_nonneg (m + 1) y)]
            have hm : Measurable fun z : ℝ =>
                ENNReal.ofReal (ar2Kernel (y ⟨m, by omega⟩) (y ⟨m + 1, by omega⟩) z) :=
              ENNReal.measurable_ofReal.comp
                (ar2Kernel_continuous.comp (Continuous.prodMk continuous_const
                  (Continuous.prodMk continuous_const continuous_id))).measurable
            rw [lintegral_const_mul _ hm, hkernel_l, mul_one]
          simp_rw [hinner]
          exact ih

/-- `ar2JointDensity j` is integrable over all of `Fin (j + 1) → ℝ`. -/
theorem ar2JointDensity_integrable (j : ℕ) :
    Integrable (ar2JointDensity j) (Measure.pi fun _ : Fin (j + 1) => volume) := by
  refine ⟨(ar2JointDensity_continuous j).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have heq : ∫⁻ x : Fin (j + 1) → ℝ, ENNReal.ofReal ‖ar2JointDensity j x‖
      ∂(Measure.pi fun _ : Fin (j + 1) => volume) = 1 := by
    have hcongr : (fun x : Fin (j + 1) → ℝ => ENNReal.ofReal ‖ar2JointDensity j x‖) =
        fun x => ENNReal.ofReal (ar2JointDensity j x) := by
      ext x; rw [Real.norm_of_nonneg (ar2JointDensity_nonneg j x)]
    rw [hcongr]
    exact lintegral_ar2JointDensity_eq_one j
  rw [heq]
  exact ENNReal.one_lt_top

/-- `ar2JointDensity j` integrates to `1` over all of `Fin (j + 1) → ℝ`. -/
theorem ar2JointDensity_integral_eq_one (j : ℕ) :
    ∫ x : Fin (j + 1) → ℝ, ar2JointDensity j x
      ∂(Measure.pi fun _ : Fin (j + 1) => volume) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (ar2JointDensity_integrable j)
    (ae_of_all _ fun x => ar2JointDensity_nonneg j x)
  rw [lintegral_ar2JointDensity_eq_one j] at h
  exact ENNReal.ofReal_eq_one.mp h

/-- Integral of `ar2InitDensity x y` over `ℝ × ℝ` equals `1`. -/
theorem ar2InitDensity_integral_eq_one :
    ∫ p : ℝ × ℝ, ar2InitDensity p.1 p.2 = 1 := by
  have h := ar2JointDensity_integral_eq_one 1
  have hmp : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ))
      (Measure.pi fun _ : Fin 2 => volume) (volume.prod volume) :=
    volume_preserving_finTwoArrow ℝ
  have hcomp : ∫ x : Fin 2 → ℝ, ar2InitDensity (x 0) (x 1)
      ∂(Measure.pi fun _ : Fin 2 => volume) =
      ∫ p : ℝ × ℝ, ar2InitDensity p.1 p.2 ∂(volume.prod volume) :=
    hmp.integral_comp (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding
      (fun p : ℝ × ℝ => ar2InitDensity p.1 p.2)
  change ∫ p : ℝ × ℝ, ar2InitDensity p.1 p.2 ∂(volume.prod volume) = 1
  rw [← hcomp, ← h]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [ar2JointDensity]

end AR2Density

/-! ### Quadratic exponent, diagonal precision entries, and coordinate slicing -/

section QuadraticForm

/-- Positive-semidefinite quadratic form `xᵀ Q x` such that for `j ≥ 1`,
`ar2JointDensity j x = (3 / (2π)) * √(6 / π) ^ (j - 1) * exp (-1/2 * ar2QuadForm j x)`. -/
noncomputable def ar2QuadForm : (j : ℕ) → (Fin (j + 1) → ℝ) → ℝ
  | 0, x => (x 0) ^ 2
  | k + 1, x =>
      9 * (x ⟨0, by omega⟩ + 2 * Real.sqrt 2 / 3 * x ⟨1, by omega⟩) ^ 2 +
        (x ⟨1, by omega⟩) ^ 2 +
        ∑ i : Fin k, 12 * (x ⟨i.1 + 2, by omega⟩ + Real.sqrt 2 * x ⟨i.1 + 1, by omega⟩ +
          x ⟨i.1, by omega⟩ / 2) ^ 2

/-- `ar2QuadForm j x` is nonnegative for every `x : Fin (j + 1) → ℝ`. -/
theorem ar2QuadForm_nonneg (j : ℕ) (x : Fin (j + 1) → ℝ) : 0 ≤ ar2QuadForm j x := by
  cases j with
  | zero => exact sq_nonneg _
  | succ k =>
      unfold ar2QuadForm
      refine add_nonneg (add_nonneg (by positivity) (sq_nonneg _)) ?_
      exact Finset.sum_nonneg fun _ _ => by positivity

/-- Exact formula expressing `ar2JointDensity j x` via `ar2QuadForm j x` for `j ≥ 1`. -/
theorem ar2JointDensity_eq_exp_quad {j : ℕ} (hj : 1 ≤ j) (x : Fin (j + 1) → ℝ) :
    ar2JointDensity j x =
      (3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ (j - 1) *
        Real.exp (-(1 / 2) * ar2QuadForm j x) := by
  cases j with
  | zero => omega
  | succ k =>
      simp only [ar2JointDensity, ar2QuadForm, Nat.add_sub_cancel, ar2InitDensity, ar2Kernel]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_sum]
      have hmul : 3 / (2 * Real.pi) *
          Real.exp (-(9 / 2) * (x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) -
            6 * Real.sqrt 2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩) *
          (Real.sqrt (6 / Real.pi) ^ k *
            Real.exp (∑ i : Fin k, -6 * (x ⟨i.1 + 2, by omega⟩ +
              Real.sqrt 2 * x ⟨i.1 + 1, by omega⟩ + x ⟨i.1, by omega⟩ / 2) ^ 2)) =
          3 / (2 * Real.pi) * Real.sqrt (6 / Real.pi) ^ k *
            (Real.exp (-(9 / 2) * (x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) -
              6 * Real.sqrt 2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩) *
              Real.exp (∑ i : Fin k, -6 * (x ⟨i.1 + 2, by omega⟩ +
                Real.sqrt 2 * x ⟨i.1 + 1, by omega⟩ + x ⟨i.1, by omega⟩ / 2) ^ 2)) := by
        ring
      rw [hmul, ← Real.exp_add]
      congr 2
      have hinit : -(9 / 2) * (x ⟨0, by omega⟩ ^ 2 + x ⟨1, by omega⟩ ^ 2) -
          6 * Real.sqrt 2 * x ⟨0, by omega⟩ * x ⟨1, by omega⟩ =
          -(1 / 2) * (9 * (x ⟨0, by omega⟩ + 2 * Real.sqrt 2 / 3 * x ⟨1, by omega⟩) ^ 2 +
            x ⟨1, by omega⟩ ^ 2) := by
        have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        linear_combination (2 * x ⟨1, by omega⟩ ^ 2) * hsq
      rw [hinit]
      calc -(1 / 2) * (9 * (x ⟨0, by omega⟩ + 2 * Real.sqrt 2 / 3 * x ⟨1, by omega⟩) ^ 2 +
              x ⟨1, by omega⟩ ^ 2) +
            ∑ i : Fin k, -6 * (x ⟨i.1 + 2, by omega⟩ +
              Real.sqrt 2 * x ⟨i.1 + 1, by omega⟩ + x ⟨i.1, by omega⟩ / 2) ^ 2
          = -(1 / 2) * (9 * (x ⟨0, by omega⟩ + 2 * Real.sqrt 2 / 3 * x ⟨1, by omega⟩) ^ 2 +
              x ⟨1, by omega⟩ ^ 2) +
            -(1 / 2) * ∑ i : Fin k, 12 * (x ⟨i.1 + 2, by omega⟩ +
              Real.sqrt 2 * x ⟨i.1 + 1, by omega⟩ + x ⟨i.1, by omega⟩ / 2) ^ 2 := by
              congr 1; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        _ = -(1 / 2) * (9 * (x ⟨0, by omega⟩ + 2 * Real.sqrt 2 / 3 * x ⟨1, by omega⟩) ^ 2 +
              x ⟨1, by omega⟩ ^ 2 +
              ∑ i : Fin k, 12 * (x ⟨i.1 + 2, by omega⟩ +
                Real.sqrt 2 * x ⟨i.1 + 1, by omega⟩ + x ⟨i.1, by omega⟩ / 2) ^ 2) := by ring

/-- Exact diagonal entry `Q_{ii}` of the AR(2) precision quadratic form of order `j + 1`. -/
def ar2QuadDiag (j : ℕ) (i : Fin (j + 1)) : ℝ :=
  if j = 0 then 1
  else if j = 1 then 9
  else if i.1 = 0 ∨ i.1 = j then 12
  else if j = 2 then 33
  else if i.1 = 1 ∨ i.1 = j - 1 then 36
  else 39

/-- Every diagonal precision entry `ar2QuadDiag j i` is positive. -/
theorem ar2QuadDiag_pos (j : ℕ) (i : Fin (j + 1)) : 0 < ar2QuadDiag j i := by
  unfold ar2QuadDiag
  repeat' split_ifs <;> norm_num

/-- Every diagonal precision entry satisfies `ar2QuadDiag j i ≤ 39`. -/
theorem ar2QuadDiag_le (j : ℕ) (i : Fin (j + 1)) : ar2QuadDiag j i ≤ 39 := by
  unfold ar2QuadDiag
  repeat' split_ifs <;> norm_num

/-- Endpoint diagonal precision entry satisfies `ar2QuadDiag j 0 ≤ 12`. -/
theorem ar2QuadDiag_zero_le (j : ℕ) : ar2QuadDiag j ⟨0, by omega⟩ ≤ 12 := by
  unfold ar2QuadDiag
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = 1
    · simp [h1]; norm_num
    · simp [h0, h1]

/-- Final endpoint diagonal precision entry satisfies `ar2QuadDiag j (Fin.last j) ≤ 12`. -/
theorem ar2QuadDiag_last_le (j : ℕ) : ar2QuadDiag j (Fin.last j) ≤ 12 := by
  unfold ar2QuadDiag
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = 1
    · simp [h1]; norm_num
    · simp [h0, h1]

/-- Near-endpoint diagonal precision entry satisfies `ar2QuadDiag j ⟨1, _⟩ ≤ 36`. -/
theorem ar2QuadDiag_one_le {j : ℕ} (hj : 1 ≤ j) : ar2QuadDiag j ⟨1, by omega⟩ ≤ 36 := by
  unfold ar2QuadDiag
  by_cases h1 : j = 1
  · simp [h1]; norm_num
  · by_cases h2 : j = 2
    · simp [h2]; norm_num
    · have h0 : j ≠ 0 := by omega
      have hne : 1 ≠ j := by omega
      simp [h0, h1, h2, hne]

/-- Penultimate diagonal precision entry satisfies `ar2QuadDiag j ⟨j - 1, _⟩ ≤ 36`. -/
theorem ar2QuadDiag_penult_le {j : ℕ} (hj : 1 ≤ j) : ar2QuadDiag j ⟨j - 1, by omega⟩ ≤ 36 := by
  unfold ar2QuadDiag
  have h0 : j ≠ 0 := by omega
  by_cases h1 : j = 1
  · simp [h1]; norm_num
  · by_cases h2 : j = 2
    · simp [h2]; norm_num
    · have hne : j - 1 ≠ 0 := by omega
      have hnej : j - 1 ≠ j := by omega
      simp [h0, h1, h2, hne, hnej]

/-- Completing the square for a single quadratic polynomial `q * t^2 + 2 * b * t + c`. -/
private theorem quad_complete_sq {q b c : ℝ} (hq : q ≠ 0) :
    ∃ μ : ℝ, ∀ t : ℝ, q * t ^ 2 + 2 * b * t + c =
      (q * μ ^ 2 + 2 * b * μ + c) + q * (t - μ) ^ 2 := by
  refine ⟨-(b / q), fun t => ?_⟩
  field_simp
  ring

/-- Helper: affine form coefficient for a single `ar2Kernel` term evaluated along `update x i t`. -/
private theorem update_kernel_sq (k : ℕ) (x : Fin (k + 2) → ℝ) (i : Fin (k + 2))
    (m : Fin k) (t : ℝ) :
    12 * (Function.update x i t ⟨m.1 + 2, by omega⟩ +
      Real.sqrt 2 * Function.update x i t ⟨m.1 + 1, by omega⟩ +
      Function.update x i t ⟨m.1, by omega⟩ / 2) ^ 2 =
    let a : ℝ :=
      (if i.1 = m.1 + 2 then 1 else 0) +
      (if i.1 = m.1 + 1 then Real.sqrt 2 else 0) +
      (if i.1 = m.1 then 1 / 2 else 0)
    let base : ℝ :=
      (if i.1 = m.1 + 2 then 0 else x ⟨m.1 + 2, by omega⟩) +
      Real.sqrt 2 * (if i.1 = m.1 + 1 then 0 else x ⟨m.1 + 1, by omega⟩) +
      (if i.1 = m.1 then 0 else x ⟨m.1, by omega⟩) / 2
    12 * (a * t + base) ^ 2 := by
  have hupd : ∀ r : Fin (k + 2),
      Function.update x i t r =
        (if i.1 = r.1 then 1 else 0) * t + (if i.1 = r.1 then 0 else x r) := by
    intro r
    by_cases h : r = i
    · subst h; simp [Function.update]
    · have hne : i.1 ≠ r.1 := fun heq => h (Fin.ext heq.symm)
      simp [Function.update_of_ne h, hne]
  simp only [hupd]
  ring_nf
  split_ifs <;> ring

/-- Completing the square on a single coordinate slice of `ar2QuadForm (k + 1)`. -/
theorem ar2QuadForm_update (k : ℕ) (x : Fin (k + 2) → ℝ) (i : Fin (k + 2)) :
    ∃ μ : ℝ, ∀ t : ℝ,
      ar2QuadForm (k + 1) (Function.update x i t) =
        ar2QuadForm (k + 1) (Function.update x i μ) + ar2QuadDiag (k + 1) i * (t - μ) ^ 2 := by
  let a0 (r : Fin k) : ℝ :=
    (if i.1 = r.1 + 2 then 1 else 0) +
    (if i.1 = r.1 + 1 then Real.sqrt 2 else 0) +
    (if i.1 = r.1 then 1 / 2 else 0)
  let b0 (r : Fin k) : ℝ :=
    (if i.1 = r.1 + 2 then 0 else x ⟨r.1 + 2, by omega⟩) +
    Real.sqrt 2 * (if i.1 = r.1 + 1 then 0 else x ⟨r.1 + 1, by omega⟩) +
    (if i.1 = r.1 then 0 else x ⟨r.1, by omega⟩) / 2
  have hkern_expand : ∀ t : ℝ,
      ∑ r : Fin k, 12 * (Function.update x i t ⟨r.1 + 2, by omega⟩ +
        Real.sqrt 2 * Function.update x i t ⟨r.1 + 1, by omega⟩ +
        Function.update x i t ⟨r.1, by omega⟩ / 2) ^ 2 =
      (∑ r : Fin k, 12 * a0 r ^ 2) * t ^ 2 +
        2 * (∑ r : Fin k, 12 * a0 r * b0 r) * t +
        ∑ r : Fin k, 12 * b0 r ^ 2 := by
    intro t
    have h1 : ∀ r : Fin k, 12 * (Function.update x i t ⟨r.1 + 2, by omega⟩ +
        Real.sqrt 2 * Function.update x i t ⟨r.1 + 1, by omega⟩ +
        Function.update x i t ⟨r.1, by omega⟩ / 2) ^ 2 =
        12 * a0 r ^ 2 * t ^ 2 + 2 * (12 * a0 r * b0 r) * t + 12 * b0 r ^ 2 := by
      intro r
      rw [update_kernel_sq k x i r t]
      dsimp only [a0, b0]
      ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  have hsum_a0 : ∑ r : Fin k, 12 * a0 r ^ 2 =
      (if i.1 + 2 ≤ k + 1 then (3 : ℝ) else 0) +
      (if 1 ≤ i.1 ∧ i.1 ≤ k then 24 else 0) +
      (if 2 ≤ i.1 then 12 else 0) := by
    have hterm : ∀ r : Fin k, 12 * a0 r ^ 2 =
        (if i.1 = r.1 then (3 : ℝ) else 0) +
        (if i.1 = r.1 + 1 then 24 else 0) +
        (if i.1 = r.1 + 2 then 12 else 0) := by
      intro r
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      dsimp only [a0]
      by_cases h0 : i.1 = r.1
      · simp [h0]; norm_num
      · by_cases h1 : i.1 = r.1 + 1
        · simp [h1]; ring_nf
        · by_cases h2 : i.1 = r.1 + 2
          · simp [h2]
          · simp [h0, h1, h2]
    simp_rw [hterm, Finset.sum_add_distrib]
    have s1 : ∑ r : Fin k, (if i.1 = r.1 then (3 : ℝ) else 0) =
        if i.1 + 2 ≤ k + 1 then 3 else 0 := by
      by_cases hi : i.1 < k
      · have hle : i.1 + 2 ≤ k + 1 := by omega
        simp only [hle, ↓reduceIte]
        rw [Finset.sum_eq_single ⟨i.1, hi⟩]
        · rw [ite_eq_left_iff]; intro h; exact (h rfl).elim
        · intro r _ hne
          rw [ite_eq_right_iff]; intro heq; exact (hne (Fin.ext heq.symm)).elim
        · intro h; exact (h (Finset.mem_univ _)).elim
      · have hgt : ¬ i.1 + 2 ≤ k + 1 := by omega
        simp only [hgt, ↓reduceIte]
        exact Finset.sum_eq_zero fun r _ => by
          have hne' : i.1 ≠ r.1 := by omega
          simp only [hne', ↓reduceIte]
    have s2 : ∑ r : Fin k, (if i.1 = r.1 + 1 then (24 : ℝ) else 0) =
        if 1 ≤ i.1 ∧ i.1 ≤ k then 24 else 0 := by
      by_cases hi : 1 ≤ i.1 ∧ i.1 ≤ k
      · have htrue : (if 1 ≤ i.1 ∧ i.1 ≤ k then (24 : ℝ) else 0) = 24 :=
          ite_eq_left_iff.mpr fun h => (h hi).elim
        rw [htrue, Finset.sum_eq_single ⟨i.1 - 1, by omega⟩]
        · rw [ite_eq_left_iff]; intro h; exact (h (Nat.sub_add_cancel hi.1).symm).elim
        · intro r _ hne
          rw [ite_eq_right_iff]; intro heq
          exact (hne (Fin.ext (by change r.1 = i.1 - 1; omega))).elim
        · intro h; exact (h (Finset.mem_univ _)).elim
      · have hfalse : (if 1 ≤ i.1 ∧ i.1 ≤ k then (24 : ℝ) else 0) = 0 :=
          ite_eq_right_iff.mpr fun h => (hi h).elim
        rw [hfalse]
        exact Finset.sum_eq_zero fun r _ => by
          have hne' : i.1 ≠ r.1 + 1 := by omega
          simp only [hne', ↓reduceIte]
    have s3 : ∑ r : Fin k, (if i.1 = r.1 + 2 then (12 : ℝ) else 0) =
        if 2 ≤ i.1 then 12 else 0 := by
      by_cases hi : 2 ≤ i.1
      · simp only [hi, ↓reduceIte]
        rw [Finset.sum_eq_single ⟨i.1 - 2, by omega⟩]
        · rw [ite_eq_left_iff]; intro h; exact (h (Nat.sub_add_cancel hi).symm).elim
        · intro r _ hne
          rw [ite_eq_right_iff]; intro heq
          exact (hne (Fin.ext (by change r.1 = i.1 - 2; omega))).elim
        · intro h; exact (h (Finset.mem_univ _)).elim
      · simp only [hi, ↓reduceIte]
        exact Finset.sum_eq_zero fun r _ => by
          have hne' : i.1 ≠ r.1 + 2 := by omega
          simp only [hne', ↓reduceIte]
    rw [s1, s2, s3]
  -- Initial bivariate term quadratic expansion in `t`:
  let c_init_q : ℝ := if i.1 = 0 ∨ i.1 = 1 then 9 else 0
  let c_init_b : ℝ :=
    if i.1 = 0 then 6 * Real.sqrt 2 * x ⟨1, by omega⟩
    else if i.1 = 1 then 6 * Real.sqrt 2 * x ⟨0, by omega⟩
    else 0
  let c_init_c : ℝ :=
    if i.1 = 0 then 9 * x ⟨1, by omega⟩ ^ 2
    else if i.1 = 1 then 9 * x ⟨0, by omega⟩ ^ 2
    else 9 * (x ⟨0, by omega⟩ + 2 * Real.sqrt 2 / 3 * x ⟨1, by omega⟩) ^ 2 +
      x ⟨1, by omega⟩ ^ 2
  have hinit_expand : ∀ t : ℝ,
      9 * (Function.update x i t ⟨0, by omega⟩ +
        2 * Real.sqrt 2 / 3 * Function.update x i t ⟨1, by omega⟩) ^ 2 +
        Function.update x i t ⟨1, by omega⟩ ^ 2 =
      c_init_q * t ^ 2 + 2 * c_init_b * t + c_init_c := by
    intro t
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    by_cases h0 : i = ⟨0, by omega⟩
    · subst h0
      have hne : (⟨1, by omega⟩ : Fin (k + 2)) ≠ ⟨0, by omega⟩ := by
        intro h; injection h with h; omega
      simp only [Function.update_self, Function.update_of_ne hne, c_init_q, c_init_b, c_init_c]
      simp only [true_or, ↓reduceIte]
      linear_combination (4 * x ⟨1, by omega⟩ ^ 2) * hsq
    · by_cases h1 : i = ⟨1, by omega⟩
      · subst h1
        have hne : (⟨0, by omega⟩ : Fin (k + 2)) ≠ ⟨1, by omega⟩ := by
          intro h; injection h with h; omega
        simp only [Function.update_self, Function.update_of_ne hne, c_init_q, c_init_b, c_init_c]
        simp only [or_true, ↓reduceIte, one_ne_zero]
        linear_combination (4 * t ^ 2) * hsq
      · have hv0 : i.1 ≠ 0 := fun h => h0 (Fin.ext h)
        have hv1 : i.1 ≠ 1 := fun h => h1 (Fin.ext h)
        have hne0 : (⟨0, by omega⟩ : Fin (k + 2)) ≠ i := fun h => hv0 (congrArg Fin.val h).symm
        have hne1 : (⟨1, by omega⟩ : Fin (k + 2)) ≠ i := fun h => hv1 (congrArg Fin.val h).symm
        simp only [Function.update_of_ne hne0, Function.update_of_ne hne1,
          c_init_q, c_init_b, c_init_c, hv0, hv1, or_self, ↓reduceIte]
        ring
  have hdiag_eq : c_init_q + ∑ r : Fin k, 12 * a0 r ^ 2 = ar2QuadDiag (k + 1) i := by
    rw [hsum_a0]
    dsimp only [c_init_q]
    unfold ar2QuadDiag
    have haux : ∀ n : ℕ, n ≤ k + 1 →
        (if n = 0 ∨ n = 1 then (9 : ℝ) else 0) +
          ((if n + 2 ≤ k + 1 then (3 : ℝ) else 0) +
            (if 1 ≤ n ∧ n ≤ k then (24 : ℝ) else 0) +
            (if 2 ≤ n then (12 : ℝ) else 0)) =
          if k + 1 = 0 then 1
          else if k + 1 = 1 then 9
          else if n = 0 ∨ n = k + 1 then 12
          else if k + 1 = 2 then 33
          else if n = 1 ∨ n = k + 1 - 1 then 36
          else 39 := by
      intro n hn
      have h0 : ¬ (k + 1 = 0) := by omega
      rw [ite_eq_right_iff.mpr fun h => (h0 h).elim]
      split_ifs <;> first | (exfalso; omega) | norm_num
    have hfin := haux i.1 (by omega)
    simpa only [add_assoc] using hfin
  have hq_ne : ar2QuadDiag (k + 1) i ≠ 0 := (ar2QuadDiag_pos (k + 1) i).ne'
  obtain ⟨μ, hμ⟩ := quad_complete_sq (b := c_init_b + ∑ r : Fin k, 12 * a0 r * b0 r)
    (c := c_init_c + ∑ r : Fin k, 12 * b0 r ^ 2) hq_ne
  refine ⟨μ, fun t => ?_⟩
  have hpoly : ∀ s : ℝ, ar2QuadForm (k + 1) (Function.update x i s) =
      ar2QuadDiag (k + 1) i * s ^ 2 +
        2 * (c_init_b + ∑ r : Fin k, 12 * a0 r * b0 r) * s +
        (c_init_c + ∑ r : Fin k, 12 * b0 r ^ 2) := by
    intro s
    dsimp only [ar2QuadForm]
    rw [hinit_expand s, hkern_expand s, ← hdiag_eq]
    ring
  rw [hpoly t, hpoly μ]
  exact hμ t

/-- Coordinate slicing of `ar2JointDensity (k + 1)`: along any single coordinate `i`, it is a
scaled Gaussian `c * exp (-ar2QuadDiag (k + 1) i / 2 * (t - μ) ^ 2)` where `0 < c` and
`c ≤ (3 / (2π)) * √(6 / π) ^ k`. -/
theorem ar2JointDensity_slice (k : ℕ) (x : Fin (k + 2) → ℝ) (i : Fin (k + 2)) :
    ∃ μ : ℝ, ∀ t : ℝ,
      ar2JointDensity (k + 1) (Function.update x i t) =
        ar2JointDensity (k + 1) (Function.update x i μ) *
          Real.exp (-(ar2QuadDiag (k + 1) i / 2) * (t - μ) ^ 2) := by
  obtain ⟨μ, hμ⟩ := ar2QuadForm_update k x i
  refine ⟨μ, fun t => ?_⟩
  rw [ar2JointDensity_eq_exp_quad (by omega : 1 ≤ k + 1),
    ar2JointDensity_eq_exp_quad (by omega : 1 ≤ k + 1), hμ t]
  rw [mul_assoc (3 / (2 * Real.pi) * Real.sqrt (6 / Real.pi) ^ (k + 1 - 1)), ← Real.exp_add]
  congr 2
  ring

/-- Factorization of `ar2InitDensity` into elementary decaying exponentials
`eA(t) = exp (-3/2 * t^2)` and `eAB(x, y) = exp (-6√2 * x * y)`. -/
theorem ar2InitDensity_eq_factor (x y : ℝ) :
    ar2InitDensity x y =
      (3 / (2 * Real.pi)) *
        Real.exp (-(3 / 2) * x ^ 2) ^ 3 *
        Real.exp (-(3 / 2) * y ^ 2) ^ 3 *
        Real.exp (-6 * Real.sqrt 2 * x * y) := by
  unfold ar2InitDensity
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc (3 / (2 * Real.pi)),
    mul_assoc (3 / (2 * Real.pi)), ← Real.exp_add, ← Real.exp_add]
  congr 2
  push_cast
  ring

/-- Factorization of `ar2Kernel` into elementary decaying exponentials `eA`, `eAB`, and `eAC`. -/
theorem ar2Kernel_eq_factor (x y z : ℝ) :
    ar2Kernel x y z =
      Real.sqrt (6 / Real.pi) *
        Real.exp (-(3 / 2) * x ^ 2) *
        Real.exp (-(3 / 2) * y ^ 2) ^ 8 *
        Real.exp (-(3 / 2) * z ^ 2) ^ 4 *
        Real.exp (-6 * Real.sqrt 2 * x * y) *
        Real.exp (-6 * Real.sqrt 2 * y * z) ^ 2 *
        Real.exp (-6 * x * z) := by
  unfold ar2Kernel
  repeat' rw [← Real.exp_nat_mul]
  have he : ∀ a b c d e f : ℝ,
      Real.exp a * Real.exp b * Real.exp c * Real.exp d * Real.exp e * Real.exp f =
        Real.exp (a + b + c + d + e + f) := by
    intro a b c d e f; simp only [← Real.exp_add]
  have hgroup : Real.sqrt (6 / Real.pi) *
      Real.exp (-(3 / 2) * x ^ 2) *
      Real.exp ((8 : ℕ) * (-(3 / 2) * y ^ 2)) *
      Real.exp ((4 : ℕ) * (-(3 / 2) * z ^ 2)) *
      Real.exp (-6 * Real.sqrt 2 * x * y) *
      Real.exp ((2 : ℕ) * (-6 * Real.sqrt 2 * y * z)) *
      Real.exp (-6 * x * z) =
      Real.sqrt (6 / Real.pi) *
        (Real.exp (-(3 / 2) * x ^ 2) *
          Real.exp ((8 : ℕ) * (-(3 / 2) * y ^ 2)) *
          Real.exp ((4 : ℕ) * (-(3 / 2) * z ^ 2)) *
          Real.exp (-6 * Real.sqrt 2 * x * y) *
          Real.exp ((2 : ℕ) * (-6 * Real.sqrt 2 * y * z)) *
          Real.exp (-6 * x * z)) := by ring
  rw [hgroup, he]
  congr 2
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  push_cast
  linear_combination (-6 * y ^ 2) * hsq

end QuadraticForm

/-! ### Real Fourier derivative bound for Gaussian exponentials -/

section FourierDerivative

/-- Elementary exponential-vs-power bound: for `b > 0` and `m : ℕ`, `|ξ|^m * exp (-b * ξ^2)` is
integrable on `ℝ`. -/
private theorem integrable_abs_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (m : ℕ) :
    Integrable (fun ξ : ℝ => |ξ| ^ m * Real.exp (-b * ξ ^ 2)) := by
  have hb2 : 0 < b / 2 := half_pos hb
  have hdom2 : Integrable (fun ξ : ℝ =>
      (1 + (m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (-(b / 2) * ξ ^ 2)) :=
    (integrable_exp_neg_mul_sq hb2).const_mul _
  refine hdom2.mono' ((by fun_prop : Continuous fun ξ : ℝ =>
      |ξ| ^ m * Real.exp (-b * ξ ^ 2)).aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 : (b / 2 * ξ ^ 2) ^ m / (m.factorial : ℝ) ≤ Real.exp (b / 2 * ξ ^ 2) :=
    Real.pow_div_factorial_le_exp (b / 2 * ξ ^ 2) (by positivity) m
  have h2 : ξ ^ (2 * m) ≤ ((m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (b / 2 * ξ ^ 2) := by
    have hfac : (0 : ℝ) < m.factorial := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hpow : (b / 2) ^ m * ξ ^ (2 * m) = (b / 2 * ξ ^ 2) ^ m := by
      rw [mul_pow, ← pow_mul, mul_comm 2 m]
    have hle : (b / 2 * ξ ^ 2) ^ m ≤ (m.factorial : ℝ) * Real.exp (b / 2 * ξ ^ 2) := by
      simpa [mul_comm] using (div_le_iff₀ hfac).mp h1
    rw [← hpow] at hle
    calc ξ ^ (2 * m) = (b / 2) ^ m * ξ ^ (2 * m) / (b / 2) ^ m := by field_simp
      _ ≤ (m.factorial : ℝ) * Real.exp (b / 2 * ξ ^ 2) / (b / 2) ^ m := by gcongr
      _ = (m.factorial : ℝ) / (b / 2) ^ m * Real.exp (b / 2 * ξ ^ 2) := by ring
  have habs_le : |ξ| ^ m ≤ 1 + ξ ^ (2 * m) := by
    have heq : ξ ^ (2 * m) = (|ξ| ^ m) ^ 2 := by
      rw [pow_mul, ← sq_abs ξ, ← pow_mul, mul_comm 2 m, pow_mul]
    rw [heq]
    by_cases h : |ξ| ^ m ≤ 1
    · linarith [sq_nonneg (|ξ| ^ m)]
    · have hgt : 1 < |ξ| ^ m := lt_of_not_ge h
      have hsq : |ξ| ^ m ≤ (|ξ| ^ m) ^ 2 := by nlinarith
      linarith
  have hexp_ge : (1 : ℝ) ≤ Real.exp (b / 2 * ξ ^ 2) := Real.one_le_exp (by positivity)
  have hcomb : |ξ| ^ m ≤ (1 + (m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (b / 2 * ξ ^ 2) := by
    calc |ξ| ^ m ≤ 1 + ξ ^ (2 * m) := habs_le
      _ ≤ 1 * Real.exp (b / 2 * ξ ^ 2) +
            (m.factorial : ℝ) / (b / 2) ^ m * Real.exp (b / 2 * ξ ^ 2) := by linarith
      _ = (1 + (m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (b / 2 * ξ ^ 2) := by ring
  calc |ξ| ^ m * Real.exp (-b * ξ ^ 2)
      ≤ ((1 + (m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (b / 2 * ξ ^ 2)) *
          Real.exp (-b * ξ ^ 2) := by gcongr
    _ = (1 + (m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (-(b / 2) * ξ ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- For any `b > 0` and `m : ℕ`, `ξ ^ m * exp (-b * ξ ^ 2)` tends to `0` as `|ξ| → ∞`. -/
private theorem tendsto_pow_mul_exp_neg_mul_sq_atTop {b : ℝ} (hb : 0 < b) (m : ℕ) :
    Filter.Tendsto (fun ξ : ℝ => ξ ^ m * Real.exp (-b * ξ ^ 2)) Filter.atTop (nhds 0) := by
  have hev : ∀ᶠ ξ : ℝ in Filter.atTop,
      ‖ξ ^ m * Real.exp (-b * ξ ^ 2)‖ ≤ ((m + 1).factorial : ℝ) / b ^ (m + 1) / ξ := by
    refine Filter.eventually_atTop.mpr ⟨1, fun ξ hξ => ?_⟩
    have hξp : 0 < ξ := by linarith
    have hpow := Real.pow_div_factorial_le_exp (b * ξ ^ 2) (by positivity) (m + 1)
    have hfac : (0 : ℝ) < (m + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h1 : (b * ξ ^ 2) ^ (m + 1) * Real.exp (-b * ξ ^ 2) ≤ (m + 1).factorial := by
      rw [show -b * ξ ^ 2 = -(b * ξ ^ 2) by ring, Real.exp_neg]
      have hmul : (b * ξ ^ 2) ^ (m + 1) ≤ (m + 1).factorial * Real.exp (b * ξ ^ 2) := by
        simpa [mul_comm] using (div_le_iff₀ hfac).mp hpow
      calc (b * ξ ^ 2) ^ (m + 1) * (Real.exp (b * ξ ^ 2))⁻¹
          ≤ (m + 1).factorial * Real.exp (b * ξ ^ 2) * (Real.exp (b * ξ ^ 2))⁻¹ := by gcongr
        _ = (m + 1).factorial := by rw [mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]
    have hsq : ξ ≤ ξ ^ 2 := by nlinarith
    have hle : ξ ^ (m + 1) ≤ (ξ ^ 2) ^ (m + 1) := pow_le_pow_left₀ hξp.le hsq (m + 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, abs_of_pos hξp]
    rw [mul_pow] at h1
    have h2 : ξ ^ (m + 1) * Real.exp (-b * ξ ^ 2) ≤
        ((m + 1).factorial : ℝ) / b ^ (m + 1) := by
      calc ξ ^ (m + 1) * Real.exp (-b * ξ ^ 2)
          ≤ (ξ ^ 2) ^ (m + 1) * Real.exp (-b * ξ ^ 2) := by gcongr
        _ = b ^ (m + 1) * (ξ ^ 2) ^ (m + 1) * Real.exp (-b * ξ ^ 2) / b ^ (m + 1) := by
            field_simp
        _ ≤ (m + 1).factorial / b ^ (m + 1) := by gcongr
    calc ξ ^ m * Real.exp (-b * ξ ^ 2)
        = ξ ^ m * Real.exp (-b * ξ ^ 2) * ξ / ξ := by
            rw [mul_div_cancel_right₀ _ hξp.ne']
      _ = ξ ^ (m + 1) * Real.exp (-b * ξ ^ 2) / ξ := by rw [pow_succ]; ring
      _ ≤ ((m + 1).factorial : ℝ) / b ^ (m + 1) / ξ := by gcongr
  have hlim : Filter.Tendsto (fun ξ : ℝ => ((m + 1).factorial : ℝ) / b ^ (m + 1) / ξ)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  exact squeeze_zero_norm' hev hlim

/-- Exact even moments of the unnormalized Gaussian weight `exp (-ξ ^ 2 / (2 * q))`. -/
theorem integral_gaussian_even_moment {q : ℝ} (hq : 0 < q) (N : ℕ) :
    ∫ ξ : ℝ, ξ ^ (2 * N) * Real.exp (-ξ ^ 2 / (2 * q)) =
      Real.sqrt (2 * Real.pi * q) * q ^ N * ((2 * N).factorial : ℝ) /
        (2 ^ N * (N.factorial : ℝ)) := by
  induction N with
  | zero =>
      have hfn : (fun ξ : ℝ => ξ ^ (2 * 0) * Real.exp (-ξ ^ 2 / (2 * q))) =
          fun ξ : ℝ => Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by
        ext ξ; simp only [mul_zero, pow_zero, one_mul]; congr 1; ring
      rw [hfn, integral_gaussian]
      have harg : Real.pi / (1 / (2 * q)) = 2 * Real.pi * q := by field_simp
      rw [harg]
      simp
  | succ n ih =>
      have hb : 0 < (1 / (2 * q) : ℝ) := by positivity
      have hint_succ : Integrable (fun ξ : ℝ => ξ ^ (2 * (n + 1)) *
          Real.exp (-ξ ^ 2 / (2 * q))) := by
        have h := integrable_abs_pow_mul_exp_neg_mul_sq hb (2 * (n + 1))
        refine h.mono' (by fun_prop) (ae_of_all _ fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
        exact le_of_eq (by congr 2; ring)
      have hint_n : Integrable (fun ξ : ℝ => ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q))) := by
        have h := integrable_abs_pow_mul_exp_neg_mul_sq hb (2 * n)
        refine h.mono' (by fun_prop) (ae_of_all _ fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
        exact le_of_eq (by congr 2; ring)
      have hrec_R : ∀ R : ℝ,
          ∫ ξ in (-R)..R, ξ ^ (2 * n + 2) * Real.exp (-ξ ^ 2 / (2 * q)) =
            (-q * R ^ (2 * n + 1) * Real.exp (-R ^ 2 / (2 * q)) -
              (-q * (-R) ^ (2 * n + 1) * Real.exp (-(-R) ^ 2 / (2 * q)))) +
            (q * (2 * n + 1 : ℝ)) *
              ∫ ξ in (-R)..R, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)) := by
        intro R
        let u : ℝ → ℝ := fun ξ => ξ ^ (2 * n + 1)
        let u' : ℝ → ℝ := fun ξ => (2 * n + 1 : ℝ) * ξ ^ (2 * n)
        let v : ℝ → ℝ := fun ξ => -q * Real.exp (-ξ ^ 2 / (2 * q))
        let v' : ℝ → ℝ := fun ξ => ξ * Real.exp (-ξ ^ 2 / (2 * q))
        have hu : ∀ ξ ∈ Set.uIcc (-R) R, HasDerivAt u (u' ξ) ξ := by
          intro ξ _
          have h := hasDerivAt_pow (2 * n + 1) ξ
          simpa [u, u', Nat.cast_add, Nat.cast_mul] using h
        have hv : ∀ ξ ∈ Set.uIcc (-R) R, HasDerivAt v (v' ξ) ξ := by
          intro ξ _
          have h1 : HasDerivAt (fun t : ℝ => -t ^ 2 / (2 * q)) (-ξ / q) ξ := by
            have hd := ((hasDerivAt_pow 2 ξ).neg).div_const (2 * q)
            convert hd using 1; field_simp; ring
          have h2 := h1.exp.const_mul (-q)
          refine h2.congr_deriv ?_
          dsimp only [v']
          field_simp
        have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
          ((by fun_prop : Continuous u').intervalIntegrable (-R) R)
          ((by fun_prop : Continuous v').intervalIntegrable (-R) R)
        have hL : ∫ ξ in (-R)..R, u ξ * v' ξ =
            ∫ ξ in (-R)..R, ξ ^ (2 * n + 2) * Real.exp (-ξ ^ 2 / (2 * q)) := by
          refine intervalIntegral.integral_congr fun ξ _ => ?_
          dsimp only [u, v']; ring
        have hR : ∫ ξ in (-R)..R, u' ξ * v ξ =
            -(q * (2 * n + 1 : ℝ)) *
              ∫ ξ in (-R)..R, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)) := by
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr fun ξ _ => ?_
          dsimp only [u', v]; ring
        rw [← hL, hibp, hR]
        dsimp only [u, v]
        ring
      have htL : Filter.Tendsto
          (fun R : ℝ => ∫ ξ in (-R)..R, ξ ^ (2 * (n + 1)) * Real.exp (-ξ ^ 2 / (2 * q)))
          Filter.atTop
          (nhds (∫ ξ : ℝ, ξ ^ (2 * (n + 1)) * Real.exp (-ξ ^ 2 / (2 * q)))) :=
        intervalIntegral_tendsto_integral hint_succ Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
      have htN : Filter.Tendsto
          (fun R : ℝ => ∫ ξ in (-R)..R, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)))
          Filter.atTop
          (nhds (∫ ξ : ℝ, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)))) :=
        intervalIntegral_tendsto_integral hint_n Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
      have hbd0 : Filter.Tendsto (fun R : ℝ => R ^ (2 * n + 1) * Real.exp (-R ^ 2 / (2 * q)))
          Filter.atTop (nhds 0) := by
        simpa [show ∀ R : ℝ, -R ^ 2 / (2 * q) = -(1 / (2 * q)) * R ^ 2 by intro R; ring] using
          tendsto_pow_mul_exp_neg_mul_sq_atTop hb (2 * n + 1)
      have hbd : Filter.Tendsto
          (fun R : ℝ =>
            (-q * R ^ (2 * n + 1) * Real.exp (-R ^ 2 / (2 * q)) -
              (-q * (-R) ^ (2 * n + 1) * Real.exp (-(-R) ^ 2 / (2 * q)))))
          Filter.atTop (nhds 0) := by
        have heq : (fun R : ℝ =>
            (-q * R ^ (2 * n + 1) * Real.exp (-R ^ 2 / (2 * q)) -
              (-q * (-R) ^ (2 * n + 1) * Real.exp (-(-R) ^ 2 / (2 * q))))) =
            fun R : ℝ => (-2 * q) * (R ^ (2 * n + 1) * Real.exp (-R ^ 2 / (2 * q))) := by
          ext R
          rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)), neg_sq]
          ring
        rw [heq]
        simpa using hbd0.const_mul (-2 * q)
      have htR : Filter.Tendsto
          (fun R : ℝ =>
            (-q * R ^ (2 * n + 1) * Real.exp (-R ^ 2 / (2 * q)) -
              (-q * (-R) ^ (2 * n + 1) * Real.exp (-(-R) ^ 2 / (2 * q)))) +
            (q * (2 * n + 1 : ℝ)) *
              ∫ ξ in (-R)..R, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)))
          Filter.atTop
          (nhds (0 + (q * (2 * n + 1 : ℝ)) *
            ∫ ξ : ℝ, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)))) :=
        hbd.add (htN.const_mul _)
      have hrec : ∫ ξ : ℝ, ξ ^ (2 * (n + 1)) * Real.exp (-ξ ^ 2 / (2 * q)) =
          (q * (2 * n + 1 : ℝ)) * ∫ ξ : ℝ, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)) := by
        have hfun : (fun R : ℝ =>
            ∫ ξ in (-R)..R, ξ ^ (2 * (n + 1)) * Real.exp (-ξ ^ 2 / (2 * q))) =
            fun R : ℝ =>
              (-q * R ^ (2 * n + 1) * Real.exp (-R ^ 2 / (2 * q)) -
                (-q * (-R) ^ (2 * n + 1) * Real.exp (-(-R) ^ 2 / (2 * q)))) +
              (q * (2 * n + 1 : ℝ)) *
                ∫ ξ in (-R)..R, ξ ^ (2 * n) * Real.exp (-ξ ^ 2 / (2 * q)) := by
          ext R; exact hrec_R R
        have heq := tendsto_nhds_unique (hfun ▸ htL) htR
        simpa using heq
      rw [hrec, ih]
      have hfac_n : (2 * (n + 1)).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, Nat.factorial_succ,
          Nat.factorial_succ (2 * n)]
        ring
      have hfac_cast : ((2 * (n + 1)).factorial : ℝ) =
          (2 * n + 2 : ℝ) * (2 * n + 1 : ℝ) * ((2 * n).factorial : ℝ) := by
        rw [hfac_n]; push_cast; ring
      have hn_cast : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfac_cast, hn_cast, pow_succ, pow_succ]
      have hn_pos : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hn1_pos : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp

/-- Real cosine Fourier representation of the Gaussian `exp (-q / 2 * y ^ 2)`. -/
theorem exp_neg_half_mul_sq_eq_cosine_integral {q : ℝ} (hq : 0 < q) (y : ℝ) :
    Real.exp (-q / 2 * y ^ 2) =
      (Real.sqrt (2 * Real.pi * q))⁻¹ *
        ∫ ξ : ℝ, Real.cos (ξ * y) * Real.exp (-ξ ^ 2 / (2 * q)) := by
  let b : ℂ := ((1 / (2 * q) : ℝ) : ℂ)
  have hb : 0 < b.re := by simpa [b] using (by positivity : (0 : ℝ) < 1 / (2 * q))
  have hf := fourierIntegral_gaussian hb (y : ℂ)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hint_c : Integrable (fun ξ : ℝ =>
      Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) * Complex.exp (-b * (ξ : ℂ) ^ 2)) := by
    have hnorm : ∀ ξ : ℝ, ‖Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
        Complex.exp (-b * (ξ : ℂ) ^ 2)‖ = Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by
      intro ξ
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
      have h1 : (Complex.I * (y : ℂ) * (ξ : ℂ)).re = 0 := by
        simp [mul_assoc, Complex.mul_re]
      have h2 : (-b * (ξ : ℂ) ^ 2).re = -(1 / (2 * q)) * ξ ^ 2 := by
        simp [b, sq]
      rw [h1, Real.exp_zero, one_mul, h2]
    refine (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (2 * q))).mono'
      (by fun_prop) (ae_of_all _ fun ξ => by rw [hnorm])
  have hre := congrArg Complex.re hf
  have hre_int : (∫ ξ : ℝ, Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
      Complex.exp (-b * (ξ : ℂ) ^ 2)).re =
      ∫ ξ : ℝ, (Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
        Complex.exp (-b * (ξ : ℂ) ^ 2)).re :=
    (integral_re hint_c).symm
  rw [hre_int] at hre
  have hL : (∫ ξ : ℝ, (Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) *
      Complex.exp (-b * (ξ : ℂ) ^ 2)).re) =
      ∫ ξ : ℝ, Real.cos (ξ * y) * Real.exp (-ξ ^ 2 / (2 * q)) := by
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    have hmul : Complex.exp (Complex.I * (y : ℂ) * (ξ : ℂ)) * Complex.exp (-b * (ξ : ℂ) ^ 2) =
        Complex.exp (((y * ξ : ℝ) : ℂ) * Complex.I) *
          ((Real.exp (-ξ ^ 2 / (2 * q)) : ℝ) : ℂ) := by
      congr 1
      · congr 1; push_cast; ring
      · rw [Complex.ofReal_exp]; congr 1; simp [b]; ring
    dsimp only
    rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.exp_mul_I]
    simp only [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re, Complex.sin_ofReal_re,
      Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
    rw [mul_comm y ξ]
  have hR : (((Real.pi : ℂ) / b) ^ ((1 : ℂ) / 2) *
      Complex.exp (-(y : ℂ) ^ 2 / (4 * b))).re =
      Real.sqrt (2 * Real.pi * q) * Real.exp (-q / 2 * y ^ 2) := by
    have hdiv : (Real.pi : ℂ) / b = ((2 * Real.pi * q : ℝ) : ℂ) := by
      dsimp only [b]; push_cast; field_simp
    have hpow : ((2 * Real.pi * q : ℝ) : ℂ) ^ ((1 : ℂ) / 2) =
        ((Real.sqrt (2 * Real.pi * q) : ℝ) : ℂ) := by
      rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow (by positivity : 0 ≤ 2 * Real.pi * q), Real.sqrt_eq_rpow]
    have hexp : Complex.exp (-(y : ℂ) ^ 2 / (4 * b)) =
        ((Real.exp (-q / 2 * y ^ 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; dsimp only [b]; push_cast; field_simp; ring
    rw [hdiv, hpow, hexp, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hL, hR] at hre
  calc Real.exp (-q / 2 * y ^ 2)
      = (Real.sqrt (2 * Real.pi * q))⁻¹ *
          (Real.sqrt (2 * Real.pi * q) * Real.exp (-q / 2 * y ^ 2)) := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ = (Real.sqrt (2 * Real.pi * q))⁻¹ *
          ∫ ξ : ℝ, Real.cos (ξ * y) * Real.exp (-ξ ^ 2 / (2 * q)) := by rw [← hre]

/-- Exact formula for all derivatives `iteratedDeriv m` of `y ↦ exp (-q / 2 * y ^ 2)` obtained
by differentiating the real cosine Fourier integral under the integral sign. -/
theorem iteratedDeriv_exp_neg_half_mul_sq_eq {q : ℝ} (hq : 0 < q) (m : ℕ) :
    iteratedDeriv m (fun y : ℝ => Real.exp (-q / 2 * y ^ 2)) =
      fun y : ℝ => (Real.sqrt (2 * Real.pi * q))⁻¹ *
        ∫ ξ : ℝ, ξ ^ m * Real.cos (ξ * y + m * (Real.pi / 2)) *
          Real.exp (-ξ ^ 2 / (2 * q)) := by
  have hb : 0 < (1 / (2 * q) : ℝ) := by positivity
  induction m with
  | zero =>
      ext y
      simp only [iteratedDeriv_zero, pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero]
      exact exp_neg_half_mul_sq_eq_cosine_integral hq y
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      ext y
      let F : ℝ → ℝ → ℝ := fun t ξ =>
        ξ ^ k * Real.cos (ξ * t + k * (Real.pi / 2)) * Real.exp (-ξ ^ 2 / (2 * q))
      let F' : ℝ → ℝ → ℝ := fun t ξ =>
        ξ ^ (k + 1) * Real.cos (ξ * t + (k + 1 : ℕ) * (Real.pi / 2)) *
          Real.exp (-ξ ^ 2 / (2 * q))
      let bound : ℝ → ℝ := fun ξ => |ξ| ^ (k + 1) * Real.exp (-(1 / (2 * q)) * ξ ^ 2)
      have hF_meas : ∀ t : ℝ, AEStronglyMeasurable (F t) volume := fun t =>
        (by fun_prop : Continuous (F t)).aestronglyMeasurable
      have hF_int : Integrable (F y) volume := by
        refine (integrable_abs_pow_mul_exp_neg_mul_sq hb k).mono' (hF_meas y)
          (ae_of_all _ fun ξ => ?_)
        dsimp only [F]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
        have hce : Real.exp (-ξ ^ 2 / (2 * q)) = Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by
          congr 1; ring
        rw [hce]
        calc |ξ| ^ k * |Real.cos (ξ * y + k * (Real.pi / 2))| *
              Real.exp (-(1 / (2 * q)) * ξ ^ 2)
            ≤ |ξ| ^ k * 1 * Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by
              gcongr; exact Real.abs_cos_le_one _
          _ = |ξ| ^ k * Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by rw [mul_one]
      have hF'_meas : AEStronglyMeasurable (F' y) volume :=
        (by fun_prop : Continuous (F' y)).aestronglyMeasurable
      have hbound_int : Integrable bound volume :=
        integrable_abs_pow_mul_exp_neg_mul_sq hb (k + 1)
      have hbound : ∀ᵐ ξ : ℝ, ∀ t ∈ Metric.ball y 1, ‖F' t ξ‖ ≤ bound ξ :=
        ae_of_all _ fun ξ t _ => by
          dsimp only [F', bound]
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
          have hce : Real.exp (-ξ ^ 2 / (2 * q)) = Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by
            congr 1; ring
          rw [hce]
          calc |ξ| ^ (k + 1) * |Real.cos (ξ * t + (k + 1 : ℕ) * (Real.pi / 2))| *
                Real.exp (-(1 / (2 * q)) * ξ ^ 2)
              ≤ |ξ| ^ (k + 1) * 1 * Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by
                gcongr; exact Real.abs_cos_le_one _
            _ = |ξ| ^ (k + 1) * Real.exp (-(1 / (2 * q)) * ξ ^ 2) := by rw [mul_one]
      have hdiff : ∀ᵐ ξ : ℝ, ∀ t ∈ Metric.ball y 1,
          HasDerivAt (fun s => F s ξ) (F' t ξ) t :=
        ae_of_all _ fun ξ t _ => by
          have hd1 : HasDerivAt (fun s : ℝ => ξ * s + k * (Real.pi / 2)) ξ t := by
            simpa using ((hasDerivAt_id t).const_mul ξ).add_const (k * (Real.pi / 2))
          have hd2 : HasDerivAt (fun s : ℝ => Real.cos (ξ * s + k * (Real.pi / 2)))
              (-Real.sin (ξ * t + k * (Real.pi / 2)) * ξ) t := hd1.cos
          have hd3 := (hd2.const_mul (ξ ^ k)).mul_const (Real.exp (-ξ ^ 2 / (2 * q)))
          convert hd3 using 1
          dsimp only [F']
          have hcos : Real.cos (ξ * t + ((k + 1 : ℕ) : ℝ) * (Real.pi / 2)) =
              -Real.sin (ξ * t + k * (Real.pi / 2)) := by
            rw [show ξ * t + ((k + 1 : ℕ) : ℝ) * (Real.pi / 2) =
                (ξ * t + k * (Real.pi / 2)) + Real.pi / 2 by push_cast; ring,
              Real.cos_add_pi_div_two]
          rw [hcos, pow_succ]
          ring
      have hderiv_int := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (Metric.ball_mem_nhds y zero_lt_one)
        (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas hbound hbound_int hdiff).2
      exact (hderiv_int.const_mul (Real.sqrt (2 * Real.pi * q))⁻¹).deriv

/-- Uniform upper bound on the `2 * N`-th derivative of a shifted Gaussian
`exp (-q / 2 * (x - μ)^2)`. -/
theorem abs_iteratedDeriv_exp_neg_half_mul_sq_le {q : ℝ} (hq : 0 < q) (μ : ℝ) (N : ℕ) (x : ℝ) :
    |iteratedDeriv (2 * N) (fun t : ℝ => Real.exp (-q / 2 * (t - μ) ^ 2)) x| ≤
      q ^ N * ((2 * N).factorial : ℝ) / (2 ^ N * (N.factorial : ℝ)) := by
  have hshift : iteratedDeriv (2 * N) (fun t : ℝ => Real.exp (-q / 2 * (t - μ) ^ 2)) x =
      iteratedDeriv (2 * N) (fun t : ℝ => Real.exp (-q / 2 * t ^ 2)) (x - μ) := by
    have hcomp := iteratedDeriv_comp_add_const (2 * N)
      (fun t : ℝ => Real.exp (-q / 2 * t ^ 2)) (-μ)
    simpa [sub_eq_add_neg] using congrFun hcomp x
  rw [hshift, iteratedDeriv_exp_neg_half_mul_sq_eq hq (2 * N)]
  have hinv_nn : 0 ≤ (Real.sqrt (2 * Real.pi * q))⁻¹ := by positivity
  rw [abs_mul, abs_of_nonneg hinv_nn]
  have hb : 0 < (1 / (2 * q) : ℝ) := by positivity
  have hint_pos : Integrable (fun ξ : ℝ => ξ ^ (2 * N) * Real.exp (-ξ ^ 2 / (2 * q))) := by
    have h := integrable_abs_pow_mul_exp_neg_mul_sq hb (2 * N)
    refine h.mono' (by fun_prop) (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    exact le_of_eq (by congr 2; ring)
  have hnorm_le : ‖∫ ξ : ℝ, ξ ^ (2 * N) * Real.cos (ξ * (x - μ) + (2 * N : ℕ) * (Real.pi / 2)) *
        Real.exp (-ξ ^ 2 / (2 * q))‖ ≤
      ∫ ξ : ℝ, ξ ^ (2 * N) * Real.exp (-ξ ^ 2 / (2 * q)) := by
    refine norm_integral_le_of_norm_le hint_pos (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Even.pow_nonneg (even_two_mul N) ξ),
      abs_of_pos (Real.exp_pos _)]
    calc ξ ^ (2 * N) * |Real.cos (ξ * (x - μ) + (2 * N : ℕ) * (Real.pi / 2))| *
          Real.exp (-ξ ^ 2 / (2 * q))
        ≤ ξ ^ (2 * N) * 1 * Real.exp (-ξ ^ 2 / (2 * q)) := by
          gcongr
          · exact Even.pow_nonneg (even_two_mul N) ξ
          · exact Real.abs_cos_le_one _
      _ = ξ ^ (2 * N) * Real.exp (-ξ ^ 2 / (2 * q)) := by rw [mul_one]
  rw [← Real.norm_eq_abs]
  calc (Real.sqrt (2 * Real.pi * q))⁻¹ *
        ‖∫ ξ : ℝ, ξ ^ (2 * N) * Real.cos (ξ * (x - μ) + (2 * N : ℕ) * (Real.pi / 2)) *
          Real.exp (-ξ ^ 2 / (2 * q))‖
      ≤ (Real.sqrt (2 * Real.pi * q))⁻¹ *
          ∫ ξ : ℝ, ξ ^ (2 * N) * Real.exp (-ξ ^ 2 / (2 * q)) := by gcongr
    _ = (Real.sqrt (2 * Real.pi * q))⁻¹ *
          (Real.sqrt (2 * Real.pi * q) * q ^ N * ((2 * N).factorial : ℝ) /
            (2 ^ N * (N.factorial : ℝ))) := by
        rw [integral_gaussian_even_moment hq N]
    _ = q ^ N * ((2 * N).factorial : ℝ) / (2 ^ N * (N.factorial : ℝ)) := by
        have hsqrt : Real.sqrt (2 * Real.pi * q) ≠ 0 := by positivity
        field_simp

/-- Smoothness of a single coordinate slice of `ar2JointDensity (k + 1)`. -/
theorem ar2JointDensity_slice_contDiff (k : ℕ) (x : Fin (k + 2) → ℝ) (i : Fin (k + 2)) (m : ℕ) :
    ContDiff ℝ m (fun t : ℝ => ar2JointDensity (k + 1) (Function.update x i t)) := by
  obtain ⟨μ, hμ⟩ := ar2JointDensity_slice k x i
  have heq : (fun t : ℝ => ar2JointDensity (k + 1) (Function.update x i t)) =
      fun t : ℝ => ar2JointDensity (k + 1) (Function.update x i μ) *
        Real.exp (-(ar2QuadDiag (k + 1) i / 2) * (t - μ) ^ 2) := funext hμ
  rw [heq]
  fun_prop

/-- Uniform `2 * N`-th partial derivative bound on `ar2JointDensity (k + 1)`
along coordinate `i`. -/
theorem abs_iteratedDeriv_ar2JointDensity_le (k : ℕ) (x : Fin (k + 2) → ℝ)
    (i : Fin (k + 2)) (N : ℕ) (t : ℝ) :
    |iteratedDeriv (2 * N) (fun s : ℝ => ar2JointDensity (k + 1) (Function.update x i s)) t| ≤
      (3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ k *
        (ar2QuadDiag (k + 1) i) ^ N * ((2 * N).factorial : ℝ) /
          (2 ^ N * (N.factorial : ℝ)) := by
  obtain ⟨μ, hμ⟩ := ar2JointDensity_slice k x i
  have heq : (fun s : ℝ => ar2JointDensity (k + 1) (Function.update x i s)) =
      fun s : ℝ => ar2JointDensity (k + 1) (Function.update x i μ) *
        Real.exp (-(ar2QuadDiag (k + 1) i / 2) * (s - μ) ^ 2) := funext hμ
  rw [heq, iteratedDeriv_const_mul_field]
  have hneg_eq : (fun s : ℝ => Real.exp (-(ar2QuadDiag (k + 1) i / 2) * (s - μ) ^ 2)) =
      fun s : ℝ => Real.exp (-ar2QuadDiag (k + 1) i / 2 * (s - μ) ^ 2) := by
    ext s; congr 2; ring
  rw [hneg_eq, abs_mul, abs_of_nonneg (ar2JointDensity_nonneg _ _)]
  have hc_le : ar2JointDensity (k + 1) (Function.update x i μ) ≤
      (3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ k := by
    simpa [Nat.add_sub_cancel] using ar2JointDensity_le (by omega : 1 ≤ k + 1)
      (Function.update x i μ)
  have hd_le := abs_iteratedDeriv_exp_neg_half_mul_sq_le (ar2QuadDiag_pos (k + 1) i) μ N t
  calc ar2JointDensity (k + 1) (Function.update x i μ) *
        |iteratedDeriv (2 * N)
          (fun s : ℝ => Real.exp (-ar2QuadDiag (k + 1) i / 2 * (s - μ) ^ 2)) t|
      ≤ ((3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ k) *
          ((ar2QuadDiag (k + 1) i) ^ N * ((2 * N).factorial : ℝ) /
            (2 ^ N * (N.factorial : ℝ))) :=
        mul_le_mul hc_le hd_le (abs_nonneg _) (by positivity)
    _ = (3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ k *
          (ar2QuadDiag (k + 1) i) ^ N * ((2 * N).factorial : ℝ) /
          (2 ^ N * (N.factorial : ℝ)) := by ring

end FourierDerivative

/-! ### Exact window marginals and anisotropic box tail bounds -/

section TailBounds

/-- 1D Gaussian half-line tail bound: for `a > 0` and `L > 0`,
`∫⁻ x in Ioi L, ENNReal.ofReal (exp (-a * x ^ 2))` is at most
`ENNReal.ofReal (exp (-a * L ^ 2) / (2 * a * L))`. -/
theorem lintegral_Ioi_exp_neg_mul_sq_le {a L : ℝ} (ha : 0 < a) (hL : 0 < L) :
    ∫⁻ x in Set.Ioi L, ENNReal.ofReal (Real.exp (-a * x ^ 2)) ≤
      ENNReal.ofReal (Real.exp (-a * L ^ 2) / (2 * a * L)) := by
  have hle : ∀ x ∈ Set.Ioi L,
      Real.exp (-a * x ^ 2) ≤ (x / L) * Real.exp (-a * x ^ 2) := by
    intro x hx
    have hxl : L < x := hx
    have h1 : 1 ≤ x / L := (one_le_div hL).mpr hxl.le
    calc Real.exp (-a * x ^ 2) = 1 * Real.exp (-a * x ^ 2) := (one_mul _).symm
      _ ≤ (x / L) * Real.exp (-a * x ^ 2) := by gcongr
  have hint_exp : IntegrableOn (fun x : ℝ => x * Real.exp (-a * x ^ 2)) (Set.Ioi L) := by
    have hfull : Integrable (fun x : ℝ => x * Real.exp (-a * x ^ 2)) := by
      refine (integrable_abs_pow_mul_exp_neg_mul_sq ha 1).mono' (by fun_prop)
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), pow_one]
    exact hfull.integrableOn
  have hftc : ∫ x in Set.Ioi L, x * Real.exp (-a * x ^ 2) =
      Real.exp (-a * L ^ 2) / (2 * a) := by
    have ht_int : Filter.Tendsto (fun R : ℝ => ∫ x in L..R, x * Real.exp (-a * x ^ 2))
        Filter.atTop (nhds (∫ x in Set.Ioi L, x * Real.exp (-a * x ^ 2))) :=
      intervalIntegral_tendsto_integral_Ioi L hint_exp Filter.tendsto_id
    have hval : ∀ R : ℝ, ∫ x in L..R, x * Real.exp (-a * x ^ 2) =
        Real.exp (-a * L ^ 2) / (2 * a) - Real.exp (-a * R ^ 2) / (2 * a) := by
      intro R
      let F : ℝ → ℝ := fun x => -(Real.exp (-a * x ^ 2) / (2 * a))
      have hd : ∀ x ∈ Set.uIcc L R, HasDerivAt F (x * Real.exp (-a * x ^ 2)) x := by
        intro x _
        have h1 : HasDerivAt (fun t : ℝ => -a * t ^ 2) (-a * (2 * x)) x := by
          simpa using (hasDerivAt_pow 2 x).const_mul (-a)
        have h2 := (h1.exp.div_const (2 * a)).neg
        refine h2.congr_deriv ?_
        field_simp
      have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        ((by fun_prop : Continuous fun x : ℝ => x * Real.exp (-a * x ^ 2)).intervalIntegrable L R)
      rw [hcalc]
      dsimp only [F]
      ring
    have ht0 : Filter.Tendsto (fun R : ℝ => Real.exp (-a * R ^ 2) / (2 * a))
        Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun R : ℝ => R ^ 0 * Real.exp (-a * R ^ 2))
          Filter.atTop (nhds 0) := tendsto_pow_mul_exp_neg_mul_sq_atTop ha 0
      simpa using h0.div_const (2 * a)
    have ht_sub : Filter.Tendsto
        (fun R : ℝ => Real.exp (-a * L ^ 2) / (2 * a) - Real.exp (-a * R ^ 2) / (2 * a))
        Filter.atTop (nhds (Real.exp (-a * L ^ 2) / (2 * a) - 0)) :=
      tendsto_const_nhds.sub ht0
    have heq : (fun R : ℝ => ∫ x in L..R, x * Real.exp (-a * x ^ 2)) =
        fun R : ℝ => Real.exp (-a * L ^ 2) / (2 * a) - Real.exp (-a * R ^ 2) / (2 * a) :=
      funext hval
    have huniq := tendsto_nhds_unique (heq ▸ ht_int) ht_sub
    simpa using huniq
  have h1 : ∫⁻ x in Set.Ioi L, ENNReal.ofReal (Real.exp (-a * x ^ 2)) ≤
      ∫⁻ x in Set.Ioi L, ENNReal.ofReal ((x / L) * Real.exp (-a * x ^ 2)) := by
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => ?_)
    exact ENNReal.ofReal_le_ofReal (hle x hx)
  have h2 : ∫⁻ x in Set.Ioi L, ENNReal.ofReal ((x / L) * Real.exp (-a * x ^ 2)) =
      ENNReal.ofReal (Real.exp (-a * L ^ 2) / (2 * a * L)) := by
    have hrew : (fun x : ℝ => (x / L) * Real.exp (-a * x ^ 2)) =
        fun x : ℝ => L⁻¹ * (x * Real.exp (-a * x ^ 2)) := by
      ext x; ring
    rw [← ofReal_integral_eq_lintegral_ofReal (by
        rw [hrew]; exact hint_exp.const_mul L⁻¹)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun x hx => by
        have hx0 : 0 ≤ x := le_trans hL.le (le_of_lt hx)
        positivity))]
    rw [hrew, integral_const_mul, hftc]
    congr 1; field_simp
  exact h1.trans_eq h2

/-- 1D exponential half-line integral: `∫⁻ x in Ioi 0, ENNReal.ofReal (exp (-c * x)) = c⁻¹`. -/
theorem lintegral_Ioi_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-c * x)) =
      ENNReal.ofReal (1 / c) := by
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le)]
  congr 1
  have hval := integral_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  simp only [mul_zero, Real.exp_zero] at hval
  rw [hval]
  ring

/-- Peeling off the last coordinate from a weighted `lintegral` of `ar2JointDensity (k + 2)`. -/
private theorem lintegral_ar2JointDensity_peel_tail (k : ℕ)
    (g : (Fin (k + 2) → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x : Fin (k + 3) → ℝ,
        g (fun i => x i.castSucc) * ENNReal.ofReal (ar2JointDensity (k + 2) x)
        ∂(Measure.pi fun _ : Fin (k + 3) => volume) =
      ∫⁻ y : Fin (k + 2) → ℝ, g y * ENNReal.ofReal (ar2JointDensity (k + 1) y)
        ∂(Measure.pi fun _ : Fin (k + 2) => volume) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 3) => ℝ) (Fin.last (k + 2))
  have hmp : MeasurePreserving split
      (Measure.pi fun _ : Fin (k + 3) => volume)
      (volume.prod (Measure.pi fun _ : Fin (k + 2) => volume)) :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k + 3) => ℝ) (Fin.last (k + 2))
  let F : ℝ × (Fin (k + 2) → ℝ) → ENNReal := fun p =>
    (g p.2 * ENNReal.ofReal (ar2JointDensity (k + 1) p.2)) *
      ENNReal.ofReal (ar2Kernel (p.2 ⟨k, by omega⟩) (p.2 ⟨k + 1, by omega⟩) p.1)
  have hkern_cont : Continuous fun p : ℝ × (Fin (k + 2) → ℝ) =>
      ar2Kernel (p.2 ⟨k, by omega⟩) (p.2 ⟨k + 1, by omega⟩) p.1 :=
    ar2Kernel_continuous.comp
      (Continuous.prodMk
        ((continuous_apply (⟨k, by omega⟩ : Fin (k + 2))).comp continuous_snd)
        (Continuous.prodMk
          ((continuous_apply (⟨k + 1, by omega⟩ : Fin (k + 2))).comp continuous_snd)
          continuous_fst))
  have hF_meas : Measurable F :=
    ((hg.comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp
        ((ar2JointDensity_continuous (k + 1)).comp continuous_snd).measurable)).mul
      (ENNReal.measurable_ofReal.comp hkern_cont.measurable)
  have h1 := hmp.lintegral_comp_emb split.measurableEmbedding F
  have hrewrite : ∫⁻ x : Fin (k + 3) → ℝ,
      g (fun i => x i.castSucc) * ENNReal.ofReal (ar2JointDensity (k + 2) x)
      ∂(Measure.pi fun _ : Fin (k + 3) => volume) =
      ∫⁻ p : ℝ × (Fin (k + 2) → ℝ), F p
        ∂(volume.prod (Measure.pi fun _ : Fin (k + 2) => volume)) := by
    rw [← h1]
    refine lintegral_congr fun x => ?_
    have hrem : (split x).2 = fun i : Fin (k + 2) => x i.castSucc := by
      ext i
      change x ((Fin.last (k + 2)).succAbove i) = x i.castSucc
      rw [Fin.succAbove_last]
    have hfst : (split x).1 = x ⟨k + 2, by omega⟩ := rfl
    dsimp only [F]
    rw [ar2JointDensity_succ k x, ENNReal.ofReal_mul (ar2JointDensity_nonneg (k + 1) _),
      ← mul_assoc, hrem, hfst]
    rfl
  rw [hrewrite, lintegral_prod_symm F hF_meas.aemeasurable]
  refine lintegral_congr fun y => ?_
  dsimp only [F]
  have hk_meas : Measurable fun z : ℝ =>
      ENNReal.ofReal (ar2Kernel (y ⟨k, by omega⟩) (y ⟨k + 1, by omega⟩) z) :=
    ENNReal.measurable_ofReal.comp
      (ar2Kernel_continuous.comp (Continuous.prodMk continuous_const
        (Continuous.prodMk continuous_const continuous_id))).measurable
  rw [lintegral_const_mul _ hk_meas]
  have hker : ∫⁻ z : ℝ, ENNReal.ofReal (ar2Kernel (y ⟨k, by omega⟩) (y ⟨k + 1, by omega⟩) z) =
      1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (ar2Kernel_integrable _ _)
      (ae_of_all _ fun z => ar2Kernel_nonneg _ _ z),
      ar2Kernel_integral_eq_one, ENNReal.ofReal_one]
  rw [hker, mul_one]

/-- Peeling off the first coordinate from a weighted `lintegral` of `ar2JointDensity (k + 2)` via
time-reversibility. -/
private theorem lintegral_ar2JointDensity_peel_head (k : ℕ)
    (g : (Fin (k + 2) → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x : Fin (k + 3) → ℝ,
        g (fun i => x i.succ) * ENNReal.ofReal (ar2JointDensity (k + 2) x)
        ∂(Measure.pi fun _ : Fin (k + 3) => volume) =
      ∫⁻ y : Fin (k + 2) → ℝ, g y * ENNReal.ofReal (ar2JointDensity (k + 1) y)
        ∂(Measure.pi fun _ : Fin (k + 2) => volume) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 3) => ℝ) 0
  have hmp : MeasurePreserving split
      (Measure.pi fun _ : Fin (k + 3) => volume)
      (volume.prod (Measure.pi fun _ : Fin (k + 2) => volume)) :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (k + 3) => ℝ) 0
  let F : ℝ × (Fin (k + 2) → ℝ) → ENNReal := fun p =>
    (g p.2 * ENNReal.ofReal (ar2JointDensity (k + 1) p.2)) *
      ENNReal.ofReal (ar2Kernel (p.2 ⟨1, by omega⟩) (p.2 ⟨0, by omega⟩) p.1)
  have hkern_cont : Continuous fun p : ℝ × (Fin (k + 2) → ℝ) =>
      ar2Kernel (p.2 ⟨1, by omega⟩) (p.2 ⟨0, by omega⟩) p.1 :=
    ar2Kernel_continuous.comp
      (Continuous.prodMk
        ((continuous_apply (⟨1, by omega⟩ : Fin (k + 2))).comp continuous_snd)
        (Continuous.prodMk
          ((continuous_apply (⟨0, by omega⟩ : Fin (k + 2))).comp continuous_snd)
          continuous_fst))
  have hF_meas : Measurable F :=
    ((hg.comp measurable_snd).mul
      (ENNReal.measurable_ofReal.comp
        ((ar2JointDensity_continuous (k + 1)).comp continuous_snd).measurable)).mul
      (ENNReal.measurable_ofReal.comp hkern_cont.measurable)
  have h1 := hmp.lintegral_comp_emb split.measurableEmbedding F
  have hrewrite : ∫⁻ x : Fin (k + 3) → ℝ,
      g (fun i => x i.succ) * ENNReal.ofReal (ar2JointDensity (k + 2) x)
      ∂(Measure.pi fun _ : Fin (k + 3) => volume) =
      ∫⁻ p : ℝ × (Fin (k + 2) → ℝ), F p
        ∂(volume.prod (Measure.pi fun _ : Fin (k + 2) => volume)) := by
    rw [← h1]
    refine lintegral_congr fun x => ?_
    have hrem : (split x).2 = fun i : Fin (k + 2) => x i.succ := by
      ext i
      change x ((0 : Fin (k + 3)).succAbove i) = x i.succ
      rw [Fin.succAbove_zero]
    have hfst : (split x).1 = x ⟨0, by omega⟩ := rfl
    dsimp only [F]
    rw [ar2JointDensity_succ_head k x, mul_comm (ar2Kernel _ _ _),
      ENNReal.ofReal_mul (ar2JointDensity_nonneg (k + 1) _), ← mul_assoc, hrem, hfst]
    rfl
  rw [hrewrite, lintegral_prod_symm F hF_meas.aemeasurable]
  refine lintegral_congr fun y => ?_
  dsimp only [F]
  have hk_meas : Measurable fun z : ℝ =>
      ENNReal.ofReal (ar2Kernel (y ⟨1, by omega⟩) (y ⟨0, by omega⟩) z) :=
    ENNReal.measurable_ofReal.comp
      (ar2Kernel_continuous.comp (Continuous.prodMk continuous_const
        (Continuous.prodMk continuous_const continuous_id))).measurable
  rw [lintegral_const_mul _ hk_meas]
  have hker : ∫⁻ z : ℝ, ENNReal.ofReal (ar2Kernel (y ⟨1, by omega⟩) (y ⟨0, by omega⟩) z) =
      1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (ar2Kernel_integrable _ _)
      (ae_of_all _ fun z => ar2Kernel_nonneg _ _ z),
      ar2Kernel_integral_eq_one, ENNReal.ofReal_one]
  rw [hker, mul_one]

/-- Stationarity / exact 3-marginal of `ar2JointDensity`: for any `k + 2 ≤ j`, the law of the
consecutive triple `(x_k, x_{k+1}, x_{k+2})` equals `ar2JointDensity 2`. -/
theorem lintegral_ar2JointDensity_triple (j k : ℕ) (hk : k + 2 ≤ j)
    (g : ℝ × ℝ × ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ x : Fin (j + 1) → ℝ,
        g (x ⟨k, by omega⟩, x ⟨k + 1, by omega⟩, x ⟨k + 2, by omega⟩) *
          ENNReal.ofReal (ar2JointDensity j x)
        ∂(Measure.pi fun _ : Fin (j + 1) => volume) =
      ∫⁻ x : Fin 3 → ℝ,
        g (x 0, x 1, x 2) * ENNReal.ofReal (ar2JointDensity 2 x)
        ∂(Measure.pi fun _ : Fin 3 => volume) := by
  induction j generalizing k with
  | zero => omega
  | succ m ih =>
      by_cases htail : k + 2 ≤ m
      · obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
        let g' : (Fin (r + 2) → ℝ) → ENNReal := fun y =>
          g (y ⟨k, by omega⟩, y ⟨k + 1, by omega⟩, y ⟨k + 2, by omega⟩)
        have hg' : Measurable g' := hg.comp
          ((measurable_pi_apply _).prodMk
            ((measurable_pi_apply _).prodMk (measurable_pi_apply _)))
        have hstep := lintegral_ar2JointDensity_peel_tail r g' hg'
        exact hstep.trans (ih k htail)
      · have hkeq : k + 2 = m + 1 := by omega
        by_cases hk0 : k = 0
        · subst hk0
          have hm : m = 1 := by omega
          subst hm
          rfl
        · obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
          let g' : (Fin (r + 2) → ℝ) → ENNReal := fun y =>
            g (y ⟨k - 1, by omega⟩, y ⟨k, by omega⟩, y ⟨k + 1, by omega⟩)
          have hg' : Measurable g' := hg.comp
            ((measurable_pi_apply _).prodMk
              ((measurable_pi_apply _).prodMk (measurable_pi_apply _)))
          have hstep := lintegral_ar2JointDensity_peel_head r g' hg'
          have heq : (∫⁻ x : Fin (r + 3) → ℝ,
              g (x ⟨k, by omega⟩, x ⟨k + 1, by omega⟩, x ⟨k + 2, by omega⟩) *
                ENNReal.ofReal (ar2JointDensity (r + 2) x)
              ∂(Measure.pi fun _ : Fin (r + 3) => volume)) =
              ∫⁻ x : Fin (r + 3) → ℝ,
                g' (fun i => x i.succ) * ENNReal.ofReal (ar2JointDensity (r + 2) x)
                ∂(Measure.pi fun _ : Fin (r + 3) => volume) := by
            refine lintegral_congr fun x => ?_
            have h0 : (⟨k - 1, by omega⟩ : Fin (r + 2)).succ = ⟨k, by omega⟩ :=
              Fin.ext (by change (k - 1) + 1 = k; omega)
            have h1 : (⟨k, by omega⟩ : Fin (r + 2)).succ = ⟨k + 1, by omega⟩ := rfl
            have h2 : (⟨k + 1, by omega⟩ : Fin (r + 2)).succ = ⟨k + 2, by omega⟩ := rfl
            dsimp only [g']
            rw [h0, h1, h2]
          rw [heq, hstep]
          have hfin : (∫⁻ y : Fin (r + 2) → ℝ, g' y * ENNReal.ofReal (ar2JointDensity (r + 1) y)
              ∂(Measure.pi fun _ : Fin (r + 2) => volume)) =
              ∫⁻ y : Fin (r + 2) → ℝ,
                g (y ⟨k - 1, by omega⟩, y ⟨k - 1 + 1, by omega⟩, y ⟨k - 1 + 2, by omega⟩) *
                  ENNReal.ofReal (ar2JointDensity (r + 1) y)
                ∂(Measure.pi fun _ : Fin (r + 2) => volume) := by
            refine lintegral_congr fun y => ?_
            dsimp only [g']
            have e1 : (⟨k, by omega⟩ : Fin (r + 2)) = ⟨k - 1 + 1, by omega⟩ :=
              Fin.ext (by change k = k - 1 + 1; omega)
            have e2 : (⟨k + 1, by omega⟩ : Fin (r + 2)) = ⟨k - 1 + 2, by omega⟩ :=
              Fin.ext (by change k + 1 = k - 1 + 2; omega)
            rw [e1, e2]
          rw [hfin]
          exact ih (k - 1) (by omega)

/-- Upper bound for the bivariate tail `∫_{x > L, y > 0} ar2InitDensity x y`. -/
theorem ar2PairTail_le {L : ℝ} (hL : 0 < L) :
    ∫⁻ x : Fin 2 → ℝ,
        (Set.indicator {x : Fin 2 → ℝ | L < x 0 ∧ 0 < x 1} (fun _ => (1 : ENNReal)) x) *
          ENNReal.ofReal (ar2JointDensity 1 x)
        ∂(Measure.pi fun _ : Fin 2 => volume) ≤
      ENNReal.ofReal ((3 / (2 * Real.pi)) *
        (Real.exp (-(9 / 2) * L ^ 2) / (9 * L)) * (1 / (6 * Real.sqrt 2 * L))) := by
  have hmp : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ))
      (Measure.pi fun _ : Fin 2 => volume) (volume.prod volume) :=
    volume_preserving_finTwoArrow ℝ
  let f : ℝ × ℝ → ENNReal := fun p =>
    (Set.indicator (Set.Ioi L ×ˢ Set.Ioi (0 : ℝ)) (fun _ => (1 : ENNReal)) p) *
      ENNReal.ofReal (ar2InitDensity p.1 p.2)
  have hrewrite := hmp.lintegral_comp_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding f
  have hlhs : (∫⁻ x : Fin 2 → ℝ,
      Set.indicator {x : Fin 2 → ℝ | L < x 0 ∧ 0 < x 1} (fun _ => (1 : ENNReal)) x *
        ENNReal.ofReal (ar2JointDensity 1 x)
      ∂(Measure.pi fun _ : Fin 2 => volume)) =
      ∫⁻ p : ℝ × ℝ, f p ∂(volume.prod volume) := by
    rw [← hrewrite]
    refine lintegral_congr fun x => ?_
    simp only [f, ar2JointDensity, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      MeasurableEquiv.finTwoArrow_apply]
    by_cases hx : L < x 0 ∧ 0 < x 1
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx]
  rw [hlhs]
  have hpt : ∀ p : ℝ × ℝ, f p ≤
      ENNReal.ofReal (3 / (2 * Real.pi)) *
        ((Set.indicator (Set.Ioi L) (fun a => ENNReal.ofReal (Real.exp (-(9 / 2) * a ^ 2))) p.1) *
         (Set.indicator (Set.Ioi (0 : ℝ))
           (fun b => ENNReal.ofReal (Real.exp (-(6 * Real.sqrt 2 * L) * b))) p.2)) := by
    intro ⟨a, b⟩
    dsimp only [f]
    by_cases h : a ∈ Set.Ioi L ∧ b ∈ Set.Ioi (0 : ℝ)
    · have ha : L < a := h.1
      have hb : 0 < b := h.2
      have hprod_mem : (a, b) ∈ Set.Ioi L ×ˢ Set.Ioi (0 : ℝ) := h
      rw [Set.indicator_of_mem hprod_mem, Set.indicator_of_mem h.1, Set.indicator_of_mem h.2,
        one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      unfold ar2InitDensity
      rw [← Real.exp_add]
      gcongr
      have hcross : 6 * Real.sqrt 2 * L * b ≤ 6 * Real.sqrt 2 * a * b := by
        have h0 : 0 ≤ 6 * Real.sqrt 2 * b := by positivity
        nlinarith
      have hsq_b : 0 ≤ (9 / 2) * b ^ 2 := by positivity
      linarith
    · rw [Set.indicator_of_notMem (show (a, b) ∉ Set.Ioi L ×ˢ Set.Ioi (0 : ℝ) from h), zero_mul]
      exact bot_le
  have hmeas_a : Measurable fun a : ℝ =>
      Set.indicator (Set.Ioi L) (fun a => ENNReal.ofReal (Real.exp (-(9 / 2) * a ^ 2))) a :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun a : ℝ =>
      Real.exp (-(9 / 2) * a ^ 2)).measurable).indicator measurableSet_Ioi
  have hmeas_b : Measurable fun b : ℝ =>
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun b => ENNReal.ofReal (Real.exp (-(6 * Real.sqrt 2 * L) * b))) b :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun b : ℝ =>
      Real.exp (-(6 * Real.sqrt 2 * L) * b)).measurable).indicator measurableSet_Ioi
  calc ∫⁻ p : ℝ × ℝ, f p ∂(volume.prod volume)
      ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (3 / (2 * Real.pi)) *
          ((Set.indicator (Set.Ioi L) (fun a => ENNReal.ofReal (Real.exp (-(9 / 2) * a ^ 2))) p.1) *
           (Set.indicator (Set.Ioi (0 : ℝ))
             (fun b => ENNReal.ofReal (Real.exp (-(6 * Real.sqrt 2 * L) * b))) p.2))
          ∂(volume.prod volume) := lintegral_mono hpt
    _ = ENNReal.ofReal (3 / (2 * Real.pi)) *
          ((∫⁻ a in Set.Ioi L, ENNReal.ofReal (Real.exp (-(9 / 2) * a ^ 2))) *
           (∫⁻ b in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(6 * Real.sqrt 2 * L) * b)))) := by
        have hprod_meas : Measurable fun p : ℝ × ℝ =>
            Set.indicator (Set.Ioi L) (fun a => ENNReal.ofReal (Real.exp (-(9 / 2) * a ^ 2))) p.1 *
              Set.indicator (Set.Ioi (0 : ℝ))
                (fun b => ENNReal.ofReal (Real.exp (-(6 * Real.sqrt 2 * L) * b))) p.2 :=
          (hmeas_a.comp measurable_fst).mul (hmeas_b.comp measurable_snd)
        rw [lintegral_const_mul _ hprod_meas,
          lintegral_prod_mul hmeas_a.aemeasurable hmeas_b.aemeasurable,
          lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Ioi]
    _ ≤ ENNReal.ofReal (3 / (2 * Real.pi)) *
          (ENNReal.ofReal (Real.exp (-(9 / 2) * L ^ 2) / (2 * (9 / 2) * L)) *
           ENNReal.ofReal (1 / (6 * Real.sqrt 2 * L))) := by
        gcongr
        · exact lintegral_Ioi_exp_neg_mul_sq_le (by norm_num : (0 : ℝ) < 9 / 2) hL
        · exact le_of_eq (lintegral_Ioi_exp_neg_mul (by positivity))
    _ = ENNReal.ofReal ((3 / (2 * Real.pi)) *
          (Real.exp (-(9 / 2) * L ^ 2) / (9 * L)) * (1 / (6 * Real.sqrt 2 * L))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- Exact expanded formula for the triple density `ar2JointDensity 2`. -/
theorem ar2JointDensity_two_eq (a b c : ℝ) :
    ar2InitDensity a b * ar2Kernel a b c =
      (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi) *
        Real.exp (-6 * a ^ 2 - (33 / 2) * b ^ 2 - 6 * c ^ 2 -
          12 * Real.sqrt 2 * a * b - 12 * Real.sqrt 2 * b * c - 6 * a * c) := by
  unfold ar2InitDensity ar2Kernel
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (3 / (2 * Real.pi)) * Real.exp (-(9 / 2) * (a ^ 2 + b ^ 2) - 6 * Real.sqrt 2 * a * b) *
      (Real.sqrt (6 / Real.pi) * Real.exp (-6 * (c + Real.sqrt 2 * b + a / 2) ^ 2)) =
      (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi) *
        (Real.exp (-(9 / 2) * (a ^ 2 + b ^ 2) - 6 * Real.sqrt 2 * a * b) *
          Real.exp (-6 * (c + Real.sqrt 2 * b + a / 2) ^ 2)) := by ring
  rw [h1, ← Real.exp_add]
  congr 2
  linear_combination (-6 * b ^ 2) * hsq

/-- Endpoint triple tail bound `endTail L` for `a > L, b > 0, c > 0` (and symmetrically
`a > 0, b > 0, c > L`). -/
noncomputable def ar2EndTail (L : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi) *
    (Real.exp (-6 * L ^ 2) / (12 * L)) *
    (1 / (12 * Real.sqrt 2 * L)) * (1 / (6 * L))

/-- Interior triple tail bound `intTail L` for `a > 0, b > L, c > 0`. -/
noncomputable def ar2IntTail (L : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi) *
    (Real.exp (-(33 / 2) * L ^ 2) / (33 * L)) *
    (1 / (12 * Real.sqrt 2 * L)) ^ 2

/-- Pair tail bound `pairTail L` for `j = 1`. -/
noncomputable def ar2PairTail (L : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) *
    (Real.exp (-(9 / 2) * L ^ 2) / (9 * L)) * (1 / (6 * Real.sqrt 2 * L))

/-- Helper: splitting `∫⁻ (Fin 3 → ℝ)` into `∫⁻ a, ∫⁻ b, ∫⁻ c`. -/
private theorem lintegral_fin3_prod_mul {fa fb fc : ℝ → ENNReal}
    (ha : Measurable fa) (hb : Measurable fb) (hc : Measurable fc) :
    ∫⁻ x : Fin 3 → ℝ, fa (x 0) * fb (x 1) * fc (x 2)
        ∂(Measure.pi fun _ : Fin 3 => volume) =
      (∫⁻ a : ℝ, fa a) * (∫⁻ b : ℝ, fb b) * (∫⁻ c : ℝ, fc c) := by
  let s1 := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have hmp1 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let s2 := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hmp2 := volume_preserving_finTwoArrow ℝ
  have h1 := hmp1.lintegral_comp_emb s1.measurableEmbedding
    (fun p : ℝ × (Fin 2 → ℝ) => fa p.1 * (fb (p.2 0) * fc (p.2 1)))
  have heq1 : (∫⁻ x : Fin 3 → ℝ, fa (x 0) * fb (x 1) * fc (x 2)
      ∂(Measure.pi fun _ : Fin 3 => volume)) =
      ∫⁻ p : ℝ × (Fin 2 → ℝ), fa p.1 * (fb (p.2 0) * fc (p.2 1))
        ∂(volume.prod (Measure.pi fun _ : Fin 2 => volume)) := by
    change _ = ∫⁻ p : ℝ × (Fin 2 → ℝ), fa p.1 * (fb (p.2 0) * fc (p.2 1))
      ∂(volume.prod (Measure.pi fun _ : Fin 2 => volume))
    rw [show (∫⁻ p : ℝ × (Fin 2 → ℝ), fa p.1 * (fb (p.2 0) * fc (p.2 1))
        ∂(volume.prod (Measure.pi fun _ : Fin 2 => volume))) =
        ∫⁻ x : Fin 3 → ℝ, fa (s1 x).1 * (fb ((s1 x).2 0) * fc ((s1 x).2 1))
          ∂(Measure.pi fun _ : Fin 3 => volume) from h1.symm]
    refine lintegral_congr fun x => ?_
    rw [mul_assoc]
    rfl
  have hprod_fin2 : AEMeasurable (fun y : Fin 2 → ℝ => fb (y 0) * fc (y 1))
      (Measure.pi fun _ : Fin 2 => volume) :=
    ((hb.comp (measurable_pi_apply 0)).mul (hc.comp (measurable_pi_apply 1))).aemeasurable
  rw [heq1, lintegral_prod_mul (f := fa) (g := fun y : Fin 2 → ℝ => fb (y 0) * fc (y 1))
    ha.aemeasurable hprod_fin2]
  have h2 := hmp2.lintegral_comp_emb s2.measurableEmbedding (fun p : ℝ × ℝ => fb p.1 * fc p.2)
  have heq2 : (∫⁻ y : Fin 2 → ℝ, fb (y 0) * fc (y 1) ∂(Measure.pi fun _ : Fin 2 => volume)) =
      (∫⁻ b : ℝ, fb b) * (∫⁻ c : ℝ, fc c) := by
    calc ∫⁻ y : Fin 2 → ℝ, fb (y 0) * fc (y 1) ∂(Measure.pi fun _ : Fin 2 => volume)
        = ∫⁻ p : ℝ × ℝ, fb p.1 * fc p.2 ∂(volume.prod volume) := h2
      _ = (∫⁻ b : ℝ, fb b) * (∫⁻ c : ℝ, fc c) :=
          lintegral_prod_mul hb.aemeasurable hc.aemeasurable
  rw [heq2, ← mul_assoc]

/-- Triple left-endpoint tail bound: `P(X₀ > L, X₁ > 0, X₂ > 0) ≤ ar2EndTail L`. -/
theorem lintegral_triple_end_left_le {L : ℝ} (hL : 0 < L) :
    ∫⁻ x : Fin 3 → ℝ,
        (Set.indicator {x : Fin 3 → ℝ | L < x 0 ∧ 0 < x 1 ∧ 0 < x 2}
          (fun _ => (1 : ENNReal)) x) *
          ENNReal.ofReal (ar2JointDensity 2 x)
        ∂(Measure.pi fun _ : Fin 3 => volume) ≤
      ENNReal.ofReal (ar2EndTail L) := by
  let fa : ℝ → ENNReal := Set.indicator (Set.Ioi L)
    fun a => ENNReal.ofReal (Real.exp (-6 * a ^ 2))
  let fb : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ))
    fun b => ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * b))
  let fc : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ))
    fun c => ENNReal.ofReal (Real.exp (-(6 * L) * c))
  let C : ℝ := (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi)
  have hpt : ∀ x : Fin 3 → ℝ,
      Set.indicator {x : Fin 3 → ℝ | L < x 0 ∧ 0 < x 1 ∧ 0 < x 2}
        (fun _ => (1 : ENNReal)) x * ENNReal.ofReal (ar2JointDensity 2 x) ≤
      ENNReal.ofReal C * (fa (x 0) * fb (x 1) * fc (x 2)) := by
    intro x
    by_cases hx : L < x 0 ∧ 0 < x 1 ∧ 0 < x 2
    · obtain ⟨ha, hb, hc⟩ := hx
      simp only [Set.indicator_of_mem (show x ∈ {x : Fin 3 → ℝ | L < x 0 ∧ 0 < x 1 ∧ 0 < x 2}
        from ⟨ha, hb, hc⟩), one_mul, fa, fb, fc,
        Set.indicator_of_mem (show x 0 ∈ Set.Ioi L from ha),
        Set.indicator_of_mem (show x 1 ∈ Set.Ioi (0 : ℝ) from hb),
        Set.indicator_of_mem (show x 2 ∈ Set.Ioi (0 : ℝ) from hc)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hd : ar2JointDensity 2 x = ar2InitDensity (x 0) (x 1) * ar2Kernel (x 0) (x 1) (x 2) := by
        simp [ar2JointDensity]
      rw [hd, ar2JointDensity_two_eq, ← Real.exp_add, ← Real.exp_add]
      dsimp only [C]
      gcongr
      have h1 : 12 * Real.sqrt 2 * L * x 1 ≤ 12 * Real.sqrt 2 * x 0 * x 1 := by
        have hpos : 0 ≤ 12 * Real.sqrt 2 * x 1 := by positivity
        nlinarith
      have h2 : 6 * L * x 2 ≤ 6 * x 0 * x 2 := by nlinarith
      have h3 : 0 ≤ 12 * Real.sqrt 2 * x 1 * x 2 := by positivity
      linarith [sq_nonneg (x 1), sq_nonneg (x 2)]
    · rw [Set.indicator_of_notMem hx, zero_mul]; exact bot_le
  have hma : Measurable fa :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun a : ℝ =>
      Real.exp (-6 * a ^ 2)).measurable).indicator measurableSet_Ioi
  have hmb : Measurable fb :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun b : ℝ =>
      Real.exp (-(12 * Real.sqrt 2 * L) * b)).measurable).indicator measurableSet_Ioi
  have hmc : Measurable fc :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun c : ℝ =>
      Real.exp (-(6 * L) * c)).measurable).indicator measurableSet_Ioi
  have hprod_m : Measurable fun x : Fin 3 → ℝ => fa (x 0) * fb (x 1) * fc (x 2) :=
    ((hma.comp (measurable_pi_apply 0)).mul (hmb.comp (measurable_pi_apply 1))).mul
      (hmc.comp (measurable_pi_apply 2))
  calc ∫⁻ x : Fin 3 → ℝ,
          Set.indicator {x : Fin 3 → ℝ | L < x 0 ∧ 0 < x 1 ∧ 0 < x 2}
            (fun _ => (1 : ENNReal)) x * ENNReal.ofReal (ar2JointDensity 2 x)
          ∂(Measure.pi fun _ : Fin 3 => volume)
      ≤ ∫⁻ x : Fin 3 → ℝ, ENNReal.ofReal C * (fa (x 0) * fb (x 1) * fc (x 2))
          ∂(Measure.pi fun _ : Fin 3 => volume) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ((∫⁻ a : ℝ, fa a) * (∫⁻ b : ℝ, fb b) * (∫⁻ c : ℝ, fc c)) := by
        rw [lintegral_const_mul _ hprod_m, lintegral_fin3_prod_mul hma hmb hmc]
    _ = ENNReal.ofReal C *
          ((∫⁻ a in Set.Ioi L, ENNReal.ofReal (Real.exp (-6 * a ^ 2))) *
           (∫⁻ b in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * b))) *
           (∫⁻ c in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(6 * L) * c)))) := by
        simp only [fa, fb, fc, lintegral_indicator measurableSet_Ioi]
    _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal (Real.exp (-6 * L ^ 2) / (2 * 6 * L)) *
           ENNReal.ofReal (1 / (12 * Real.sqrt 2 * L)) *
           ENNReal.ofReal (1 / (6 * L))) := by
        gcongr
        · exact lintegral_Ioi_exp_neg_mul_sq_le (by norm_num : (0 : ℝ) < 6) hL
        · exact le_of_eq (lintegral_Ioi_exp_neg_mul (by positivity))
        · exact le_of_eq (lintegral_Ioi_exp_neg_mul (by positivity))
    _ = ENNReal.ofReal (ar2EndTail L) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; unfold ar2EndTail; dsimp only [C]; ring

/-- Triple right-endpoint tail bound: `P(X₀ > 0, X₁ > 0, X₂ > L) ≤ ar2EndTail L`. -/
theorem lintegral_triple_end_right_le {L : ℝ} (hL : 0 < L) :
    ∫⁻ x : Fin 3 → ℝ,
        (Set.indicator {x : Fin 3 → ℝ | 0 < x 0 ∧ 0 < x 1 ∧ L < x 2}
          (fun _ => (1 : ENNReal)) x) *
          ENNReal.ofReal (ar2JointDensity 2 x)
        ∂(Measure.pi fun _ : Fin 3 => volume) ≤
      ENNReal.ofReal (ar2EndTail L) := by
  let fa : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ))
    fun a => ENNReal.ofReal (Real.exp (-(6 * L) * a))
  let fb : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ))
    fun b => ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * b))
  let fc : ℝ → ENNReal := Set.indicator (Set.Ioi L)
    fun c => ENNReal.ofReal (Real.exp (-6 * c ^ 2))
  let C : ℝ := (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi)
  have hpt : ∀ x : Fin 3 → ℝ,
      Set.indicator {x : Fin 3 → ℝ | 0 < x 0 ∧ 0 < x 1 ∧ L < x 2}
        (fun _ => (1 : ENNReal)) x * ENNReal.ofReal (ar2JointDensity 2 x) ≤
      ENNReal.ofReal C * (fa (x 0) * fb (x 1) * fc (x 2)) := by
    intro x
    by_cases hx : 0 < x 0 ∧ 0 < x 1 ∧ L < x 2
    · obtain ⟨ha, hb, hc⟩ := hx
      simp only [Set.indicator_of_mem (show x ∈ {x : Fin 3 → ℝ | 0 < x 0 ∧ 0 < x 1 ∧ L < x 2}
        from ⟨ha, hb, hc⟩), one_mul, fa, fb, fc,
        Set.indicator_of_mem (show x 0 ∈ Set.Ioi (0 : ℝ) from ha),
        Set.indicator_of_mem (show x 1 ∈ Set.Ioi (0 : ℝ) from hb),
        Set.indicator_of_mem (show x 2 ∈ Set.Ioi L from hc)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hd : ar2JointDensity 2 x = ar2InitDensity (x 0) (x 1) * ar2Kernel (x 0) (x 1) (x 2) := by
        simp [ar2JointDensity]
      rw [hd, ar2JointDensity_two_eq, ← Real.exp_add, ← Real.exp_add]
      dsimp only [C]
      gcongr
      have h1 : 12 * Real.sqrt 2 * L * x 1 ≤ 12 * Real.sqrt 2 * x 1 * x 2 := by
        have hpos : 0 ≤ 12 * Real.sqrt 2 * x 1 := by positivity
        nlinarith
      have h2 : 6 * L * x 0 ≤ 6 * x 0 * x 2 := by nlinarith
      have h3 : 0 ≤ 12 * Real.sqrt 2 * x 0 * x 1 := by positivity
      linarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    · rw [Set.indicator_of_notMem hx, zero_mul]; exact bot_le
  have hma : Measurable fa :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun a : ℝ =>
      Real.exp (-(6 * L) * a)).measurable).indicator measurableSet_Ioi
  have hmb : Measurable fb :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun b : ℝ =>
      Real.exp (-(12 * Real.sqrt 2 * L) * b)).measurable).indicator measurableSet_Ioi
  have hmc : Measurable fc :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun c : ℝ =>
      Real.exp (-6 * c ^ 2)).measurable).indicator measurableSet_Ioi
  have hprod_m : Measurable fun x : Fin 3 → ℝ => fa (x 0) * fb (x 1) * fc (x 2) :=
    ((hma.comp (measurable_pi_apply 0)).mul (hmb.comp (measurable_pi_apply 1))).mul
      (hmc.comp (measurable_pi_apply 2))
  calc ∫⁻ x : Fin 3 → ℝ,
          Set.indicator {x : Fin 3 → ℝ | 0 < x 0 ∧ 0 < x 1 ∧ L < x 2}
            (fun _ => (1 : ENNReal)) x * ENNReal.ofReal (ar2JointDensity 2 x)
          ∂(Measure.pi fun _ : Fin 3 => volume)
      ≤ ∫⁻ x : Fin 3 → ℝ, ENNReal.ofReal C * (fa (x 0) * fb (x 1) * fc (x 2))
          ∂(Measure.pi fun _ : Fin 3 => volume) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ((∫⁻ a : ℝ, fa a) * (∫⁻ b : ℝ, fb b) * (∫⁻ c : ℝ, fc c)) := by
        rw [lintegral_const_mul _ hprod_m, lintegral_fin3_prod_mul hma hmb hmc]
    _ = ENNReal.ofReal C *
          ((∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(6 * L) * a))) *
           (∫⁻ b in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * b))) *
           (∫⁻ c in Set.Ioi L, ENNReal.ofReal (Real.exp (-6 * c ^ 2)))) := by
        simp only [fa, fb, fc, lintegral_indicator measurableSet_Ioi]
    _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal (1 / (6 * L)) *
           ENNReal.ofReal (1 / (12 * Real.sqrt 2 * L)) *
           ENNReal.ofReal (Real.exp (-6 * L ^ 2) / (2 * 6 * L))) := by
        gcongr
        · exact le_of_eq (lintegral_Ioi_exp_neg_mul (by positivity))
        · exact le_of_eq (lintegral_Ioi_exp_neg_mul (by positivity))
        · exact lintegral_Ioi_exp_neg_mul_sq_le (by norm_num : (0 : ℝ) < 6) hL
    _ = ENNReal.ofReal (ar2EndTail L) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; unfold ar2EndTail; dsimp only [C]; ring

/-- Triple interior tail bound: `P(X₀ > 0, X₁ > L, X₂ > 0) ≤ ar2IntTail L`. -/
theorem lintegral_triple_int_le {L : ℝ} (hL : 0 < L) :
    ∫⁻ x : Fin 3 → ℝ,
        (Set.indicator {x : Fin 3 → ℝ | 0 < x 0 ∧ L < x 1 ∧ 0 < x 2}
          (fun _ => (1 : ENNReal)) x) *
          ENNReal.ofReal (ar2JointDensity 2 x)
        ∂(Measure.pi fun _ : Fin 3 => volume) ≤
      ENNReal.ofReal (ar2IntTail L) := by
  let fa : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ))
    fun a => ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * a))
  let fb : ℝ → ENNReal := Set.indicator (Set.Ioi L)
    fun b => ENNReal.ofReal (Real.exp (-(33 / 2) * b ^ 2))
  let fc : ℝ → ENNReal := Set.indicator (Set.Ioi (0 : ℝ))
    fun c => ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * c))
  let C : ℝ := (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi)
  have hpt : ∀ x : Fin 3 → ℝ,
      Set.indicator {x : Fin 3 → ℝ | 0 < x 0 ∧ L < x 1 ∧ 0 < x 2}
        (fun _ => (1 : ENNReal)) x * ENNReal.ofReal (ar2JointDensity 2 x) ≤
      ENNReal.ofReal C * (fa (x 0) * fb (x 1) * fc (x 2)) := by
    intro x
    by_cases hx : 0 < x 0 ∧ L < x 1 ∧ 0 < x 2
    · obtain ⟨ha, hb, hc⟩ := hx
      simp only [Set.indicator_of_mem (show x ∈ {x : Fin 3 → ℝ | 0 < x 0 ∧ L < x 1 ∧ 0 < x 2}
        from ⟨ha, hb, hc⟩), one_mul, fa, fb, fc,
        Set.indicator_of_mem (show x 0 ∈ Set.Ioi (0 : ℝ) from ha),
        Set.indicator_of_mem (show x 1 ∈ Set.Ioi L from hb),
        Set.indicator_of_mem (show x 2 ∈ Set.Ioi (0 : ℝ) from hc)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hd : ar2JointDensity 2 x = ar2InitDensity (x 0) (x 1) * ar2Kernel (x 0) (x 1) (x 2) := by
        simp [ar2JointDensity]
      rw [hd, ar2JointDensity_two_eq, ← Real.exp_add, ← Real.exp_add]
      dsimp only [C]
      gcongr
      have h1 : 12 * Real.sqrt 2 * L * x 0 ≤ 12 * Real.sqrt 2 * x 0 * x 1 := by
        have hpos : 0 ≤ 12 * Real.sqrt 2 * x 0 := by positivity
        nlinarith
      have h2 : 12 * Real.sqrt 2 * L * x 2 ≤ 12 * Real.sqrt 2 * x 1 * x 2 := by
        have hpos : 0 ≤ 12 * Real.sqrt 2 * x 2 := by positivity
        nlinarith
      have h3 : 0 ≤ 6 * x 0 * x 2 := by positivity
      linarith [sq_nonneg (x 0), sq_nonneg (x 2)]
    · rw [Set.indicator_of_notMem hx, zero_mul]; exact bot_le
  have hma : Measurable fa :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun a : ℝ =>
      Real.exp (-(12 * Real.sqrt 2 * L) * a)).measurable).indicator measurableSet_Ioi
  have hmb : Measurable fb :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun b : ℝ =>
      Real.exp (-(33 / 2) * b ^ 2)).measurable).indicator measurableSet_Ioi
  have hmc : Measurable fc :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun c : ℝ =>
      Real.exp (-(12 * Real.sqrt 2 * L) * c)).measurable).indicator measurableSet_Ioi
  have hprod_m : Measurable fun x : Fin 3 → ℝ => fa (x 0) * fb (x 1) * fc (x 2) :=
    ((hma.comp (measurable_pi_apply 0)).mul (hmb.comp (measurable_pi_apply 1))).mul
      (hmc.comp (measurable_pi_apply 2))
  calc ∫⁻ x : Fin 3 → ℝ,
          Set.indicator {x : Fin 3 → ℝ | 0 < x 0 ∧ L < x 1 ∧ 0 < x 2}
            (fun _ => (1 : ENNReal)) x * ENNReal.ofReal (ar2JointDensity 2 x)
          ∂(Measure.pi fun _ : Fin 3 => volume)
      ≤ ∫⁻ x : Fin 3 → ℝ, ENNReal.ofReal C * (fa (x 0) * fb (x 1) * fc (x 2))
          ∂(Measure.pi fun _ : Fin 3 => volume) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ((∫⁻ a : ℝ, fa a) * (∫⁻ b : ℝ, fb b) * (∫⁻ c : ℝ, fc c)) := by
        rw [lintegral_const_mul _ hprod_m, lintegral_fin3_prod_mul hma hmb hmc]
    _ = ENNReal.ofReal C *
          ((∫⁻ a in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * a))) *
           (∫⁻ b in Set.Ioi L, ENNReal.ofReal (Real.exp (-(33 / 2) * b ^ 2))) *
           (∫⁻ c in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(12 * Real.sqrt 2 * L) * c)))) := by
        simp only [fa, fb, fc, lintegral_indicator measurableSet_Ioi]
    _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal (1 / (12 * Real.sqrt 2 * L)) *
           ENNReal.ofReal (Real.exp (-(33 / 2) * L ^ 2) / (2 * (33 / 2) * L)) *
           ENNReal.ofReal (1 / (12 * Real.sqrt 2 * L))) := by
        gcongr
        · exact le_of_eq (lintegral_Ioi_exp_neg_mul (by positivity))
        · exact lintegral_Ioi_exp_neg_mul_sq_le (by norm_num : (0 : ℝ) < 33 / 2) hL
        · exact le_of_eq (lintegral_Ioi_exp_neg_mul (by positivity))
    _ = ENNReal.ofReal (ar2IntTail L) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; unfold ar2IntTail; dsimp only [C]; ring

/-- Coordinatewise cutoff for the anisotropic box `[0, L_end] × [0, L_int]^{j-1} × [0, L_end]`. -/
def ar2BoxBound (L_end L_int : ℝ) (j : ℕ) (i : Fin (j + 1)) : ℝ :=
  if i.1 = 0 ∨ i.1 = j then L_end else L_int

/-- The anisotropic truncation box `∏ i, (0, ar2BoxBound L_end L_int j i]`. -/
def ar2Box (L_end L_int : ℝ) (j : ℕ) : Set (Fin (j + 1) → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioc (0 : ℝ) (ar2BoxBound L_end L_int j i)

/-- The integral of `ar2JointDensity j` over the anisotropic box `ar2Box L_end L_int j`. -/
noncomputable def ar2BoxIntegral (L_end L_int : ℝ) (j : ℕ) : ℝ :=
  ∫ x in ar2Box L_end L_int j, ar2JointDensity j x
    ∂(Measure.pi fun _ : Fin (j + 1) => volume)

/-- Total tail upper bound `tailBound L_end L_int j` for truncating the positive orthant to
`ar2Box L_end L_int j`. -/
noncomputable def ar2TailBound (L_end L_int : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then 2 * ar2PairTail L_end
  else 2 * ar2EndTail L_end + (j - 1 : ℝ) * ar2IntTail L_int

/-- The box integral is nonnegative and at most `ar2OrthantIntegral j`. -/
theorem ar2BoxIntegral_le_orthant (L_end L_int : ℝ) (j : ℕ) :
    ar2BoxIntegral L_end L_int j ≤ ar2OrthantIntegral j := by
  unfold ar2BoxIntegral ar2OrthantIntegral
  refine setIntegral_mono_set (ar2JointDensity_integrable j).integrableOn
    (ae_of_all _ fun x => ar2JointDensity_nonneg j x) ?_
  filter_upwards with x hx i hi
  exact (hx i hi).1

/-- Explicit anisotropic tail truncation error bound for `j ≥ 1`. -/
theorem ar2OrthantIntegral_sub_box_le {L_end L_int : ℝ} (hLe : 0 < L_end) (hLi : 0 < L_int)
    {j : ℕ} (hj : 1 ≤ j) :
    ar2OrthantIntegral j - ar2BoxIntegral L_end L_int j ≤
      ar2TailBound L_end L_int j := by
  let μ : Measure (Fin (j + 1) → ℝ) := Measure.pi fun _ : Fin (j + 1) => volume
  let O : Set (Fin (j + 1) → ℝ) := Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)
  let B : Set (Fin (j + 1) → ℝ) := ar2Box L_end L_int j
  have hO_m : MeasurableSet O := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hB_m : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hsub : B ⊆ O := fun x hx i hi => (hx i hi).1
  have hdiff_int : ar2OrthantIntegral j - ar2BoxIntegral L_end L_int j =
      ∫ x in O \ B, ar2JointDensity j x ∂μ := by
    have h := setIntegral_sdiff hB_m (ar2JointDensity_integrable j).integrableOn hsub
    exact h.symm
  rw [hdiff_int]
  have hj1 : (0 : ℝ) ≤ (j : ℝ) - 1 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hnn : 0 ≤ ar2TailBound L_end L_int j := by
    unfold ar2TailBound ar2PairTail ar2EndTail ar2IntTail
    split_ifs <;> positivity
  refine ENNReal.ofReal_le_ofReal_iff hnn |>.mp ?_
  rw [ofReal_integral_eq_lintegral_ofReal (ar2JointDensity_integrable j).integrableOn
    (ae_of_all _ fun x => ar2JointDensity_nonneg j x)]
  let S_i (i : Fin (j + 1)) : Set (Fin (j + 1) → ℝ) :=
    {x | x ∈ O ∧ ar2BoxBound L_end L_int j i < x i}
  have hcov : O \ B ⊆ ⋃ i : Fin (j + 1), S_i i := by
    intro x ⟨hxO, hxnB⟩
    have hnot : ¬ ∀ i : Fin (j + 1), x i ∈ Set.Ioc 0 (ar2BoxBound L_end L_int j i) :=
      fun h => hxnB fun i _ => h i
    classical
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    refine Set.mem_iUnion.mpr ⟨i, hxO, ?_⟩
    by_contra hle
    exact hi ⟨hxO i (Set.mem_univ i), not_lt.mp hle⟩
  have hunion : ∫⁻ x in O \ B, ENNReal.ofReal (ar2JointDensity j x) ∂μ ≤
      ∑ i : Fin (j + 1), ∫⁻ x in S_i i, ENNReal.ofReal (ar2JointDensity j x) ∂μ := by
    calc ∫⁻ x in O \ B, ENNReal.ofReal (ar2JointDensity j x) ∂μ
        ≤ ∫⁻ x in ⋃ i : Fin (j + 1), S_i i, ENNReal.ofReal (ar2JointDensity j x) ∂μ :=
          lintegral_mono_set hcov
      _ ≤ ∑' i : Fin (j + 1), ∫⁻ x in S_i i, ENNReal.ofReal (ar2JointDensity j x) ∂μ :=
          lintegral_iUnion_le _ _
      _ = ∑ i : Fin (j + 1), ∫⁻ x in S_i i, ENNReal.ofReal (ar2JointDensity j x) ∂μ :=
          tsum_fintype _
  refine hunion.trans ?_
  cases j with
  | zero => omega
  | succ k =>
      cases k with
      | zero =>
          -- `j = 1`
          unfold ar2TailBound
          simp only [↓reduceIte]
          rw [Fin.sum_univ_two]
          have h0 : ∫⁻ x in S_i 0, ENNReal.ofReal (ar2JointDensity 1 x) ∂μ ≤
              ENNReal.ofReal (ar2PairTail L_end) := by
            have hs : MeasurableSet (S_i 0) :=
              hO_m.inter (measurableSet_lt measurable_const (measurable_pi_apply 0))
            rw [← lintegral_indicator hs]
            have hle : ∀ x : Fin 2 → ℝ,
                Set.indicator (S_i 0) (fun x => ENNReal.ofReal (ar2JointDensity 1 x)) x ≤
                Set.indicator {x : Fin 2 → ℝ | L_end < x 0 ∧ 0 < x 1}
                  (fun _ => (1 : ENNReal)) x * ENNReal.ofReal (ar2JointDensity 1 x) := by
              intro x
              by_cases hx : x ∈ S_i 0
              · have h1 : L_end < x 0 := by simpa [S_i, ar2BoxBound] using hx.2
                have h2 : 0 < x 1 := hx.1 1 (Set.mem_univ 1)
                simp [Set.indicator_of_mem hx, Set.indicator_of_mem
                  (show x ∈ {x : Fin 2 → ℝ | L_end < x 0 ∧ 0 < x 1} from ⟨h1, h2⟩)]
              · simp [Set.indicator_of_notMem hx]
            exact (lintegral_mono hle).trans (ar2PairTail_le hLe)
          have h1 : ∫⁻ x in S_i 1, ENNReal.ofReal (ar2JointDensity 1 x) ∂μ ≤
              ENNReal.ofReal (ar2PairTail L_end) := by
            -- Swap coordinates via `(0 ↔ 1)` measure-preserving symmetry
            let sw : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) :=
              MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => ℝ) (Equiv.swap (0 : Fin 2) 1)
            have hs : MeasurableSet (S_i 1) :=
              hO_m.inter (measurableSet_lt measurable_const (measurable_pi_apply 1))
            have hmp_sw : MeasurePreserving sw μ μ :=
              MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin 2 => (volume : Measure ℝ))
                (Equiv.swap (0 : Fin 2) 1)
            have hs0 : MeasurableSet (S_i 0) :=
              hO_m.inter (measurableSet_lt measurable_const (measurable_pi_apply 0))
            have hsw : ∫⁻ x in S_i 1, ENNReal.ofReal (ar2JointDensity 1 x) ∂μ =
                ∫⁻ x in S_i 0, ENNReal.ofReal (ar2JointDensity 1 x) ∂μ := by
              rw [← lintegral_indicator hs, ← lintegral_indicator hs0]
              have he := hmp_sw.lintegral_comp_emb sw.measurableEmbedding
                (Set.indicator (S_i 1) fun x => ENNReal.ofReal (ar2JointDensity 1 x))
              rw [← he]
              refine lintegral_congr fun x => ?_
              have hx0 : sw x 0 = x 1 := by
                change x ((Equiv.swap (0 : Fin 2) 1).symm 0) = x 1; simp
              have hx1 : sw x 1 = x 0 := by
                change x ((Equiv.swap (0 : Fin 2) 1).symm 1) = x 0; simp
              have hdens : ar2JointDensity 1 (sw x) = ar2JointDensity 1 x := by
                simp only [ar2JointDensity, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
                change ar2InitDensity (sw x 0) (sw x 1) = ar2InitDensity (x 0) (x 1)
                rw [hx0, hx1, ar2InitDensity_symm]
              have hmem : sw x ∈ S_i 1 ↔ x ∈ S_i 0 := by
                constructor
                · rintro ⟨hO, hlt⟩
                  refine ⟨fun j _ => ?_, ?_⟩
                  · fin_cases j
                    · simpa [hx1] using hO 1 (Set.mem_univ 1)
                    · simpa [hx0] using hO 0 (Set.mem_univ 0)
                  · simpa [S_i, ar2BoxBound, hx1] using hlt
                · rintro ⟨hO, hlt⟩
                  refine ⟨fun j _ => ?_, ?_⟩
                  · fin_cases j
                    · simpa [hx0] using hO 1 (Set.mem_univ 1)
                    · simpa [hx1] using hO 0 (Set.mem_univ 0)
                  · simpa [S_i, ar2BoxBound, hx1] using hlt
              by_cases h : x ∈ S_i 0
              · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h), hdens]
              · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hm => h (hmem.mp hm))]
            rw [hsw]
            exact h0
          calc (∫⁻ x in S_i 0, ENNReal.ofReal (ar2JointDensity 1 x) ∂μ) +
                ∫⁻ x in S_i 1, ENNReal.ofReal (ar2JointDensity 1 x) ∂μ
              ≤ ENNReal.ofReal (ar2PairTail L_end) + ENNReal.ofReal (ar2PairTail L_end) :=
                add_le_add h0 h1
            _ = ENNReal.ofReal (2 * ar2PairTail L_end) := by
                rw [← ENNReal.ofReal_add (by unfold ar2PairTail; positivity)
                  (by unfold ar2PairTail; positivity), two_mul]
      | succ m =>
          -- `j = m + 2 ≥ 2`
          have hterm : ∀ i : Fin (m + 3),
              ∫⁻ x in S_i i, ENNReal.ofReal (ar2JointDensity (m + 2) x) ∂μ ≤
                if i.1 = 0 ∨ i.1 = m + 2 then ENNReal.ofReal (ar2EndTail L_end)
                else ENNReal.ofReal (ar2IntTail L_int) := by
            intro i
            have hs : MeasurableSet (S_i i) :=
              hO_m.inter (measurableSet_lt measurable_const (measurable_pi_apply i))
            rw [← lintegral_indicator hs]
            by_cases hi0 : i.1 = 0
            · simp only [hi0, true_or, ↓reduceIte]
              let g : ℝ × ℝ × ℝ → ENNReal := fun p =>
                Set.indicator {q : ℝ × ℝ × ℝ | L_end < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2}
                  (fun _ => 1) p
              have hg : Measurable g := measurable_const.indicator
                ((measurableSet_lt measurable_const measurable_fst).inter
                  ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
                    (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))))
              have hmono : ∫⁻ x : Fin (m + 3) → ℝ,
                  Set.indicator (S_i i) (fun x => ENNReal.ofReal (ar2JointDensity (m + 2) x)) x
                  ∂μ ≤
                  ∫⁻ x : Fin (m + 3) → ℝ,
                    g (x ⟨0, by omega⟩, x ⟨1, by omega⟩, x ⟨2, by omega⟩) *
                      ENNReal.ofReal (ar2JointDensity (m + 2) x) ∂μ := by
                refine lintegral_mono fun x => ?_
                by_cases hx : x ∈ S_i i
                · have hxi : i = ⟨0, by omega⟩ := Fin.ext hi0
                  have hlt : L_end < x ⟨0, by omega⟩ := by
                    simpa [S_i, hxi, ar2BoxBound] using hx.2
                  have h1 : 0 < x ⟨1, by omega⟩ := hx.1 ⟨1, by omega⟩ (Set.mem_univ _)
                  have h2 : 0 < x ⟨2, by omega⟩ := hx.1 ⟨2, by omega⟩ (Set.mem_univ _)
                  rw [Set.indicator_of_mem hx]
                  have hm : (x ⟨0, by omega⟩, x ⟨1, by omega⟩, x ⟨2, by omega⟩) ∈
                      {q : ℝ × ℝ × ℝ | L_end < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2} := ⟨hlt, h1, h2⟩
                  simp only [g, Set.indicator_of_mem hm, one_mul, le_refl]
                · rw [Set.indicator_of_notMem hx]; exact bot_le
              refine hmono.trans ?_
              rw [lintegral_ar2JointDensity_triple (m + 2) 0 (by omega) g hg]
              exact lintegral_triple_end_left_le hLe
            · by_cases hil : i.1 = m + 2
              · simp only [hil, or_true, ↓reduceIte]
                let g : ℝ × ℝ × ℝ → ENNReal := fun p =>
                  Set.indicator {q : ℝ × ℝ × ℝ | 0 < q.1 ∧ 0 < q.2.1 ∧ L_end < q.2.2}
                    (fun _ => 1) p
                have hg : Measurable g := measurable_const.indicator
                  ((measurableSet_lt measurable_const measurable_fst).inter
                    ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
                      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))))
                have hmono : ∫⁻ x : Fin (m + 3) → ℝ,
                    Set.indicator (S_i i) (fun x => ENNReal.ofReal (ar2JointDensity (m + 2) x)) x
                    ∂μ ≤
                    ∫⁻ x : Fin (m + 3) → ℝ,
                      g (x ⟨m, by omega⟩, x ⟨m + 1, by omega⟩, x ⟨m + 2, by omega⟩) *
                        ENNReal.ofReal (ar2JointDensity (m + 2) x) ∂μ := by
                  refine lintegral_mono fun x => ?_
                  by_cases hx : x ∈ S_i i
                  · have hxi : i = ⟨m + 2, by omega⟩ := Fin.ext hil
                    have hlt : L_end < x ⟨m + 2, by omega⟩ := by
                      simpa [S_i, hxi, ar2BoxBound] using hx.2
                    have h0 : 0 < x ⟨m, by omega⟩ := hx.1 ⟨m, by omega⟩ (Set.mem_univ _)
                    have h1 : 0 < x ⟨m + 1, by omega⟩ := hx.1 ⟨m + 1, by omega⟩ (Set.mem_univ _)
                    rw [Set.indicator_of_mem hx]
                    have hm : (x ⟨m, by omega⟩, x ⟨m + 1, by omega⟩, x ⟨m + 2, by omega⟩) ∈
                        {q : ℝ × ℝ × ℝ | 0 < q.1 ∧ 0 < q.2.1 ∧ L_end < q.2.2} := ⟨h0, h1, hlt⟩
                    simp only [g, Set.indicator_of_mem hm, one_mul, le_refl]
                  · rw [Set.indicator_of_notMem hx]; exact bot_le
                refine hmono.trans ?_
                rw [lintegral_ar2JointDensity_triple (m + 2) m (by omega) g hg]
                exact lintegral_triple_end_right_le hLe
              · simp only [hi0, hil, or_self, ↓reduceIte]
                let g : ℝ × ℝ × ℝ → ENNReal := fun p =>
                  Set.indicator {q : ℝ × ℝ × ℝ | 0 < q.1 ∧ L_int < q.2.1 ∧ 0 < q.2.2}
                    (fun _ => 1) p
                have hg : Measurable g := measurable_const.indicator
                  ((measurableSet_lt measurable_const measurable_fst).inter
                    ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
                      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))))
                have hk_le : (i.1 - 1) + 2 ≤ m + 2 := by omega
                have hmono : ∫⁻ x : Fin (m + 3) → ℝ,
                    Set.indicator (S_i i) (fun x => ENNReal.ofReal (ar2JointDensity (m + 2) x)) x
                    ∂μ ≤
                    ∫⁻ x : Fin (m + 3) → ℝ,
                      g (x ⟨i.1 - 1, by omega⟩, x ⟨(i.1 - 1) + 1, by omega⟩,
                        x ⟨(i.1 - 1) + 2, by omega⟩) *
                        ENNReal.ofReal (ar2JointDensity (m + 2) x) ∂μ := by
                  refine lintegral_mono fun x => ?_
                  by_cases hx : x ∈ S_i i
                  · have hxi : (⟨(i.1 - 1) + 1, by omega⟩ : Fin (m + 3)) = i :=
                      Fin.ext (by simp; omega)
                    have hlt : L_int < x ⟨(i.1 - 1) + 1, by omega⟩ := by
                      rw [hxi]; simpa [S_i, ar2BoxBound, hi0, hil] using hx.2
                    have h0 : 0 < x ⟨i.1 - 1, by omega⟩ :=
                      hx.1 ⟨i.1 - 1, by omega⟩ (Set.mem_univ _)
                    have h2 : 0 < x ⟨(i.1 - 1) + 2, by omega⟩ :=
                      hx.1 ⟨(i.1 - 1) + 2, by omega⟩ (Set.mem_univ _)
                    rw [Set.indicator_of_mem hx]
                    have hm : (x ⟨i.1 - 1, by omega⟩, x ⟨(i.1 - 1) + 1, by omega⟩,
                        x ⟨(i.1 - 1) + 2, by omega⟩) ∈
                        {q : ℝ × ℝ × ℝ | 0 < q.1 ∧ L_int < q.2.1 ∧ 0 < q.2.2} := ⟨h0, hlt, h2⟩
                    simp only [g, Set.indicator_of_mem hm, one_mul, le_refl]
                  · rw [Set.indicator_of_notMem hx]; exact bot_le
                refine hmono.trans ?_
                rw [lintegral_ar2JointDensity_triple (m + 2) (i.1 - 1) hk_le g hg]
                exact lintegral_triple_int_le hLi
          calc ∑ i : Fin (m + 3), ∫⁻ x in S_i i, ENNReal.ofReal (ar2JointDensity (m + 2) x) ∂μ
              ≤ ∑ i : Fin (m + 3),
                  (if i.1 = 0 ∨ i.1 = m + 2 then ENNReal.ofReal (ar2EndTail L_end)
                   else ENNReal.ofReal (ar2IntTail L_int)) :=
                Finset.sum_le_sum fun i _ => hterm i
            _ = ENNReal.ofReal (ar2EndTail L_end) + ENNReal.ofReal (ar2EndTail L_end) +
                  ((m + 1 : ℕ) : ENNReal) * ENNReal.ofReal (ar2IntTail L_int) := by
                rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
                have h0_eq : (if (0 : Fin (m + 3)).1 = 0 ∨ (0 : Fin (m + 3)).1 = m + 2
                    then ENNReal.ofReal (ar2EndTail L_end)
                    else ENNReal.ofReal (ar2IntTail L_int)) =
                    ENNReal.ofReal (ar2EndTail L_end) := by simp
                have hl_eq : (if (Fin.last (m + 1)).succ.1 = 0 ∨
                    (Fin.last (m + 1)).succ.1 = m + 2
                    then ENNReal.ofReal (ar2EndTail L_end)
                    else ENNReal.ofReal (ar2IntTail L_int)) =
                    ENNReal.ofReal (ar2EndTail L_end) := by simp
                have hmid : ∑ i : Fin (m + 1),
                    (if i.castSucc.succ.1 = 0 ∨ i.castSucc.succ.1 = m + 2
                     then ENNReal.ofReal (ar2EndTail L_end)
                     else ENNReal.ofReal (ar2IntTail L_int)) =
                    ((m + 1 : ℕ) : ENNReal) * ENNReal.ofReal (ar2IntTail L_int) := by
                  have hcongr : ∀ i : Fin (m + 1),
                      (if i.castSucc.succ.1 = 0 ∨ i.castSucc.succ.1 = m + 2
                       then ENNReal.ofReal (ar2EndTail L_end)
                       else ENNReal.ofReal (ar2IntTail L_int)) =
                      ENNReal.ofReal (ar2IntTail L_int) := by
                    intro i
                    have hi1 : i.castSucc.succ.1 ≠ 0 := by simp
                    have hi2 : i.castSucc.succ.1 ≠ m + 2 := by
                      change i.1 + 1 ≠ m + 2; omega
                    exact ite_eq_right_iff.mpr fun h => by rcases h with h | h <;> contradiction
                  simp_rw [hcongr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul]
                rw [h0_eq, hl_eq, hmid]
                ring
            _ = ENNReal.ofReal (ar2TailBound L_end L_int (m + 2)) := by
                unfold ar2TailBound
                have hne : m + 2 ≠ 1 := by omega
                simp only [hne, ↓reduceIte]
                have hnnE : 0 ≤ ar2EndTail L_end := by unfold ar2EndTail; positivity
                have hnnI : 0 ≤ ar2IntTail L_int := by unfold ar2IntTail; positivity
                rw [← ENNReal.ofReal_add hnnE hnnE, ← ENNReal.ofReal_natCast (m + 1),
                  ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
                  ← ENNReal.ofReal_add (by positivity) (by positivity)]
                congr 1; push_cast; ring

end TailBounds

/-! ### Legendre polynomials and Gauss–Legendre quadrature error -/

section GaussLegendre

open Polynomial

/-- Every real polynomial defines a `ContDiff ℝ m` function. -/
private theorem poly_contDiff (p : Polynomial ℝ) (m : ℕ) :
    ContDiff ℝ m (fun t : ℝ => p.eval t) := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simpa only [eval_add] using hf.add hg
  | monomial n a =>
      have : (fun t : ℝ => (Polynomial.monomial n a).eval t) = fun t => a * t ^ n := by
        ext t; simp [eval_monomial]
      rw [this]
      fun_prop

/-- Evaluating a finite sum of polynomials at `x`. -/
private theorem eval_finset_sum_eq {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (x : ℝ) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x :=
  map_sum (Polynomial.evalRingHom x) f s

/-- Extracting the `k`-th coefficient of a finite sum of polynomials. -/
private theorem coeff_finset_sum_eq {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, coeff_add, ih, Finset.sum_insert ha]

/-- `natDegree` of a finite sum of polynomials bounded strictly by `n > 0`. -/
private theorem natDegree_finset_sum_lt {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ)
    {n : ℕ} (hn : 0 < n) (hf : ∀ i ∈ s, (f i).natDegree < n) :
    (∑ i ∈ s, f i).natDegree < n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hn
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (natDegree_add_le _ _).trans_lt
        (max_lt (hf a (Finset.mem_insert_self a s))
          (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Linearity of the interval integral over finite sums. -/
private theorem intervalIntegral_sum_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    ∫ t in a..b, ∑ i ∈ s, f i t = ∑ i ∈ s, ∫ t in a..b, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      simp_rw [Finset.sum_insert hx]
      have hsub : IntervalIntegrable (fun t => ∑ i ∈ s, f i t) volume a b := by
        have h := IntervalIntegrable.sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
        convert h using 1; ext t; simp
      rw [intervalIntegral.integral_add (hf x (Finset.mem_insert_self x s)) hsub,
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Continuity of a finite sum of continuous real-valued functions. -/
private theorem continuous_sum_real {α ι : Type*} [TopologicalSpace α] (s : Finset ι)
    (f : ι → α → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous fun a => ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Every real polynomial defines a continuous function. -/
private theorem poly_continuous (p : Polynomial ℝ) :
    Continuous (fun t : ℝ => p.eval t) :=
  (poly_contDiff p 0).continuous

/-- The `k`-th formal derivative of a real polynomial agrees pointwise with `iteratedDeriv k`. -/
private theorem iteratedDeriv_polynomial_eval (p : Polynomial ℝ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => p.eval t) = fun t : ℝ => (derivative^[k] p).eval t := by
  induction k generalizing p with
  | zero => ext t; rfl
  | succ m ih =>
      rw [iteratedDeriv_succ', Function.iterate_succ_apply]
      have hd : deriv (fun t : ℝ => p.eval t) = fun t : ℝ => p.derivative.eval t :=
        funext fun t => (p.hasDerivAt t).deriv
      rw [hd]
      exact ih p.derivative

/-- `iteratedDeriv k` of any polynomial with `natDegree < k` is zero. -/
private theorem derivative_iterate_eq_zero_of_natDegree_lt {p : Polynomial ℝ} {k : ℕ}
    (hdeg : p.natDegree < k) : derivative^[k] p = 0 := by
  induction k generalizing p with
  | zero => omega
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      by_cases h0 : p.natDegree = 0
      · rw [Polynomial.eq_C_of_natDegree_eq_zero h0, derivative_C]
        clear ih hdeg h0
        induction m with
        | zero => rfl
        | succ n ihn => rw [Function.iterate_succ_apply, derivative_zero, ihn]
      · exact ih (by have := Polynomial.natDegree_derivative_lt h0; omega)

/-- `m`-th formal derivative of a monic polynomial of degree `m` equals `C m!`. -/
private theorem derivative_iterate_monic (p : Polynomial ℝ) (hmon : p.Monic) :
    derivative^[p.natDegree] p = Polynomial.C (p.natDegree.factorial : ℝ) := by
  have hgen : ∀ n : ℕ, ∀ q : Polynomial ℝ, q.natDegree ≤ n →
      derivative^[n] q = Polynomial.C ((n.factorial : ℝ) * q.coeff n) := by
    intro n
    induction n with
    | zero =>
        intro q hq
        simp only [Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one, one_mul]
        exact Polynomial.eq_C_of_natDegree_le_zero hq
    | succ m ih =>
        intro q hq
        rw [Function.iterate_succ_apply]
        have hdq : q.derivative.natDegree ≤ m := by
          have := Polynomial.natDegree_derivative_le q
          omega
        rw [ih q.derivative hdq, coeff_derivative, Nat.factorial_succ]
        push_cast
        congr 1
        ring
  have h := hgen p.natDegree p le_rfl
  change derivative^[p.natDegree] p =
    Polynomial.C ((p.natDegree.factorial : ℝ) * p.leadingCoeff) at h
  rwa [hmon.leadingCoeff, mul_one] at h

/-- Scaled Legendre polynomial `Q_N(X) = 2^N * P_N(X)` with exact integer-valued binomial
coefficients. -/
noncomputable def legendreScaled (N : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (N / 2 + 1),
    Polynomial.C (((-1 : ℝ) ^ k) * (N.choose k : ℝ) *
      ((2 * N - 2 * k).choose N : ℝ)) * Polynomial.X ^ (N - 2 * k)

/-- Formal derivative divisibility: if `(X - C a) ^ (m + 1) ∣ p`, then `(X - C a) ^ m ∣ p'`. -/
private theorem dvd_derivative_of_pow_succ_dvd {p : Polynomial ℝ} {a : ℝ} {m : ℕ}
    (h : (Polynomial.X - Polynomial.C a) ^ (m + 1) ∣ p) :
    (Polynomial.X - Polynomial.C a) ^ m ∣ p.derivative := by
  rcases h with ⟨q, rfl⟩
  rw [derivative_mul, derivative_pow, derivative_X_sub_C, mul_one]
  refine ⟨Polynomial.C (m + 1 : ℝ) * q + (Polynomial.X - Polynomial.C a) * q.derivative, ?_⟩
  rw [pow_succ ((Polynomial.X - Polynomial.C a)) m]
  push_cast
  ring

/-- Iterated derivatives of `(X^2 - 1)^N` remain divisible by `(X - 1)^(N - k)` and
`(X + 1)^(N - k)`. -/
private theorem linear_pow_dvd_iterate_deriv (N k : ℕ) (hk : k ≤ N) :
    (Polynomial.X - Polynomial.C 1) ^ (N - k) ∣
      derivative^[k] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N) ∧
    (Polynomial.X - Polynomial.C (-1)) ^ (N - k) ∣
      derivative^[k] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N) := by
  induction k with
  | zero =>
      simp only [Function.iterate_zero_apply, Nat.sub_zero]
      have hfac : (Polynomial.X ^ 2 - 1 : Polynomial ℝ) =
          (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C (-1)) := by
        simp only [map_one, map_neg]; ring
      rw [hfac, mul_pow]
      exact ⟨dvd_mul_right _ _, dvd_mul_left _ _⟩
  | succ m ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have heq : N - m = (N - (m + 1)) + 1 := by omega
      rw [heq] at h1 h2
      rw [Function.iterate_succ_apply']
      exact ⟨dvd_derivative_of_pow_succ_dvd h1, dvd_derivative_of_pow_succ_dvd h2⟩

/-- Rodrigues formula: `N! * legendreScaled N = derivative^[N] ((X^2 - 1)^N)`. -/
theorem legendreScaled_eq_rodrigues (N : ℕ) :
    Polynomial.C (N.factorial : ℝ) * legendreScaled N =
      derivative^[N] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N) := by
  have hderiv_pow : ∀ (m r : ℕ), derivative^[r] (Polynomial.X ^ m : Polynomial ℝ) =
      Polynomial.C (Nat.descFactorial m r : ℝ) * Polynomial.X ^ (m - r) := by
    intro m r
    induction r with
    | zero => simp
    | succ s ih =>
        rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_C, zero_mul, zero_add,
          derivative_X_pow]
        cases hms : m - s with
        | zero =>
            have hle : m ≤ s := by omega
            have h0 : Nat.descFactorial m (s + 1) = 0 :=
              Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
            rw [Nat.sub_add_eq, hms, Nat.zero_sub, h0]
            simp
        | succ d =>
            have h1 : m - (s + 1) = d := by omega
            have hsub1 : (d + 1) - 1 = d := Nat.add_sub_cancel d 1
            rw [h1, Nat.descFactorial_succ, hms, hsub1]
            simp only [Nat.cast_mul, map_mul, Nat.cast_add, Nat.cast_one, map_add, map_one]
            ring
  have hexp : (Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N =
      ∑ k ∈ Finset.range (N + 1),
        Polynomial.C ((-1 : ℝ) ^ k * (N.choose k : ℝ)) *
          Polynomial.X ^ (2 * (N - k)) := by
    rw [show (Polynomial.X ^ 2 - 1 : Polynomial ℝ) = (-1 : Polynomial ℝ) + Polynomial.X ^ 2 by
      ring, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [← pow_mul, mul_comm 2 (N - k), map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  have hderiv_lin : ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℝ) (r : ℕ),
      derivative^[r] (∑ i ∈ s, f i) = ∑ i ∈ s, derivative^[r] (f i) := by
    intro s f r
    induction r with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Function.iterate_succ_apply']
  have hderiv_C_mul : ∀ (c : ℝ) (p : Polynomial ℝ) (r : ℕ),
      derivative^[r] (Polynomial.C c * p) = Polynomial.C c * derivative^[r] p := by
    intro c p r
    induction r with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_C, zero_mul, zero_add,
          Function.iterate_succ_apply']
  have hrod_sum : derivative^[N] (∑ k ∈ Finset.range (N + 1),
      Polynomial.C ((-1 : ℝ) ^ k * (N.choose k : ℝ)) * Polynomial.X ^ (2 * (N - k))) =
      ∑ k ∈ Finset.range (N + 1),
        derivative^[N] (Polynomial.C ((-1 : ℝ) ^ k * (N.choose k : ℝ)) *
          Polynomial.X ^ (2 * (N - k))) :=
    hderiv_lin (Finset.range (N + 1)) _ N
  rw [hexp, hrod_sum]
  simp_rw [hderiv_C_mul, hderiv_pow]
  unfold legendreScaled
  rw [Finset.mul_sum]
  have hsub : Finset.range (N / 2 + 1) ⊆ Finset.range (N + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ N / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hge : N ≤ 2 * (N - k) := by omega
    have h2 : 2 * (N - k) = 2 * N - 2 * k := by omega
    have hdiff : 2 * (N - k) - N = N - 2 * k := by omega
    have hdesc : Nat.descFactorial (2 * (N - k)) N =
        N.factorial * (2 * N - 2 * k).choose N := by
      rw [h2, ← Nat.descFactorial_eq_factorial_mul_choose]
    rw [hdesc, hdiff]
    simp only [Nat.cast_mul, map_mul]
    ring
  · intro k hk hnk
    have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk_gt : N / 2 < k := by
      simp only [Finset.mem_range] at hnk
      omega
    have hlt : 2 * (N - k) < N := by omega
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
    simp

/-- Degree and leading coefficient of `legendreScaled N`. -/
theorem legendreScaled_coeff_self (N : ℕ) :
    (legendreScaled N).natDegree = N ∧
    (legendreScaled N).coeff N = ((2 * N).choose N : ℝ) := by
  have hterm : ∀ k ∈ Finset.range (N / 2 + 1),
      (Polynomial.C (((-1 : ℝ) ^ k) * (N.choose k : ℝ) * ((2 * N - 2 * k).choose N : ℝ)) *
        Polynomial.X ^ (N - 2 * k)).natDegree ≤ N := by
    intro k _
    exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le (N - 2 * k) |>.trans (by omega))
  have hdeg_le : (legendreScaled N).natDegree ≤ N :=
    natDegree_sum_le_of_forall_le _ _ hterm
  have hcoeff : (legendreScaled N).coeff N = ((2 * N).choose N : ℝ) := by
    unfold legendreScaled
    rw [coeff_finset_sum_eq, Finset.sum_eq_single 0]
    · simp
    · intro k hk hne
      have hk_range : k < N / 2 + 1 := Finset.mem_range.mp hk
      have hne' : N ≠ N - 2 * k := by omega
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right_iff.mpr fun h => (hne' h).elim, mul_zero]
    · intro h; simp at h
  have hpos : (legendreScaled N).coeff N ≠ 0 := by
    rw [hcoeff]
    exact Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hdeg_ge : N ≤ (legendreScaled N).natDegree := le_natDegree_of_ne_zero hpos
  exact ⟨le_antisymm hdeg_le hdeg_ge, hcoeff⟩

/-- Degree `N` of `legendreScaled N`. -/
theorem legendreScaled_natDegree (N : ℕ) : (legendreScaled N).natDegree = N :=
  (legendreScaled_coeff_self N).1

/-- Leading coefficient of `legendreScaled N` is `C(2N, N) > 0`. -/
theorem legendreScaled_leadingCoeff (N : ℕ) :
    (legendreScaled N).leadingCoeff = ((2 * N).choose N : ℝ) := by
  rw [Polynomial.leadingCoeff, legendreScaled_natDegree, (legendreScaled_coeff_self N).2]

/-- Integration by parts reduction for `legendreScaled N` on `[-1, 1]`. -/
private theorem integral_mul_rodrigues_ibp (N : ℕ) (p : Polynomial ℝ) (k : ℕ) (hk : k ≤ N) :
    ∫ t in (-1 : ℝ)..1, p.eval t *
        (derivative^[N] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N)).eval t =
      (-1 : ℝ) ^ k * ∫ t in (-1 : ℝ)..1, (derivative^[k] p).eval t *
        (derivative^[N - k] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N)).eval t := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [ih (by omega)]
      let q : Polynomial ℝ := derivative^[m] p
      let r : Polynomial ℝ := derivative^[N - (m + 1)] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N)
      have hr_deriv : r.derivative =
          derivative^[N - m] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N) := by
        dsimp only [r]
        have hsucc : (N - (m + 1)).succ = N - m := by omega
        rw [← Function.iterate_succ_apply' derivative (N - (m + 1)), hsucc]
      have hdvd := linear_pow_dvd_iterate_deriv N (N - (m + 1)) (by omega)
      have hpos : 1 ≤ N - (N - (m + 1)) := by omega
      have hr1 : r.eval 1 = 0 := by
        obtain ⟨u, hu⟩ := dvd_trans (pow_dvd_pow _ hpos) hdvd.1
        dsimp only [r]; rw [hu, eval_mul, eval_pow, eval_sub, eval_X, eval_C]; simp
      have hrm1 : r.eval (-1) = 0 := by
        obtain ⟨u, hu⟩ := dvd_trans (pow_dvd_pow _ hpos) hdvd.2
        dsimp only [r]; rw [hu, eval_mul, eval_pow, eval_sub, eval_X, eval_C]; simp
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := (-1 : ℝ)) (b := 1)
        (u := fun t => q.eval t) (u' := fun t => q.derivative.eval t)
        (v := fun t => r.eval t) (v' := fun t => r.derivative.eval t)
        (fun t _ => q.hasDerivAt t) (fun t _ => r.hasDerivAt t)
        (poly_continuous q.derivative |>.intervalIntegrable _ _)
        (poly_continuous r.derivative |>.intervalIntegrable _ _)
      have hstep : ∫ t in (-1 : ℝ)..1, q.eval t * r.derivative.eval t =
          -(∫ t in (-1 : ℝ)..1, q.derivative.eval t * r.eval t) := by
        rw [hibp, hr1, hrm1]; ring
      have hlhs : ∫ t in (-1 : ℝ)..1, (derivative^[m] p).eval t *
          (derivative^[N - m] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N)).eval t =
          ∫ t in (-1 : ℝ)..1, q.eval t * r.derivative.eval t := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [hr_deriv]
      rw [hlhs, hstep, pow_succ]
      have hq' : q.derivative = derivative^[m + 1] p :=
        (Function.iterate_succ_apply' derivative m p).symm
      rw [hq']
      ring

/-- Orthogonality of `legendreScaled N` to every polynomial of degree `< N` on `[-1, 1]`. -/
theorem integral_mul_legendreScaled_eq_zero {N : ℕ} {p : Polynomial ℝ}
    (hdeg : p.natDegree < N) :
    ∫ t in (-1 : ℝ)..1, p.eval t * (legendreScaled N).eval t = 0 := by
  have hfac : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hscale : (N.factorial : ℝ) *
      ∫ t in (-1 : ℝ)..1, p.eval t * (legendreScaled N).eval t =
      ∫ t in (-1 : ℝ)..1, p.eval t *
        (derivative^[N] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N)).eval t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hrod := congrArg (fun q : Polynomial ℝ => q.eval t) (legendreScaled_eq_rodrigues N)
    simp only [eval_mul, eval_C] at hrod
    rw [← hrod]
    ring
  have h0 : ∫ t in (-1 : ℝ)..1, p.eval t *
      (derivative^[N] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N)).eval t = 0 := by
    rw [integral_mul_rodrigues_ibp N p N le_rfl,
      derivative_iterate_eq_zero_of_natDegree_lt hdeg]
    simp
  rw [h0] at hscale
  exact (mul_eq_zero.mp hscale).resolve_left hfac

/-- Closed form for `∫_{-1}^1 (1 - t ^ 2) ^ N dt`. -/
private theorem integral_one_sub_sq_pow (N : ℕ) :
    ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ N =
      2 ^ (2 * N + 1) * (N.factorial : ℝ) ^ 2 / ((2 * N + 1).factorial : ℝ) := by
  induction N with
  | zero => simp; norm_num
  | succ n ih =>
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := (-1 : ℝ)) (b := 1)
        (u := fun t : ℝ => (1 - t ^ 2) ^ (n + 1))
        (u' := fun t : ℝ => -(2 * (n + 1 : ℝ)) * t * (1 - t ^ 2) ^ n)
        (v := fun t : ℝ => t) (v' := fun _ => (1 : ℝ))
        (fun t _ => by
          have hd1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (0 - 2 * t ^ 1) t :=
            (hasDerivAt_const t (1 : ℝ)).sub (by simpa using hasDerivAt_pow 2 t)
          have hd2 := (hd1.congr_deriv (by ring : 0 - 2 * t ^ 1 = -(2 * t))).pow (n + 1)
          refine hd2.congr_deriv ?_; push_cast; ring)
        (fun t _ => hasDerivAt_id t)
        ((by fun_prop : Continuous fun t : ℝ =>
          -(2 * (n + 1 : ℝ)) * t * (1 - t ^ 2) ^ n).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      have h1 : (1 - (1 : ℝ) ^ 2) ^ (n + 1) = 0 := by norm_num
      have h2 : (1 - (-1 : ℝ) ^ 2) ^ (n + 1) = 0 := by norm_num
      have hL : ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (n + 1) =
          (2 * (n + 1 : ℝ)) * ∫ t in (-1 : ℝ)..1, t ^ 2 * (1 - t ^ 2) ^ n := by
        have hmul1 : ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (n + 1) * 1 =
            ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (n + 1) := by simp
        rw [← hmul1, hibp, h1, h2]
        simp only [zero_mul, sub_self, zero_sub]
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        refine intervalIntegral.integral_congr fun t _ => by ring
      have hsplit : ∫ t in (-1 : ℝ)..1, t ^ 2 * (1 - t ^ 2) ^ n =
          (∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ n) -
            ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (n + 1) := by
        rw [← intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun t : ℝ => (1 - t ^ 2) ^ n).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun t : ℝ => (1 - t ^ 2) ^ (n + 1)).intervalIntegrable _ _)]
        refine intervalIntegral.integral_congr fun t _ => by rw [pow_succ]; ring
      rw [hsplit] at hL
      have hrel : (2 * n + 3 : ℝ) * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (n + 1) =
          (2 * n + 2 : ℝ) * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ n := by linarith
      have hpos : (2 * n + 3 : ℝ) ≠ 0 := by positivity
      have hfac1 : ((2 * (n + 1) + 1).factorial : ℝ) =
          (2 * n + 3 : ℝ) * (2 * n + 2 : ℝ) * ((2 * n + 1).factorial : ℝ) := by
        have hnat : (2 * (n + 1) + 1).factorial =
            (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
          rw [show 2 * (n + 1) + 1 = (2 * n + 2) + 1 by omega, Nat.factorial_succ,
            Nat.factorial_succ (2 * n + 1)]
          ring
        rw [hnat]; push_cast; ring
      have hfac2 : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      calc ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (n + 1)
          = (2 * n + 2 : ℝ) / (2 * n + 3 : ℝ) * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ n := by
              have hdiv : ((2 * n + 3 : ℝ) * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ (n + 1)) /
                  (2 * n + 3 : ℝ) =
                  ((2 * n + 2 : ℝ) * ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ n) / (2 * n + 3 : ℝ) :=
                congrArg (· / (2 * n + 3 : ℝ)) hrel
              rw [mul_div_cancel_left₀ _ hpos, mul_div_right_comm] at hdiv
              exact hdiv
        _ = (2 * n + 2 : ℝ) / (2 * n + 3 : ℝ) *
              (2 ^ (2 * n + 1) * (n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)) := by
              rw [ih]
        _ = 2 ^ (2 * (n + 1) + 1) * ((n + 1).factorial : ℝ) ^ 2 /
              ((2 * (n + 1) + 1).factorial : ℝ) := by
              rw [hfac1, hfac2, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add]
              have hnz : ((2 * n + 1).factorial : ℝ) ≠ 0 :=
                Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
              field_simp
              ring

/-- Exact `L²` norm squared of `legendreScaled N` on `[-1, 1]`. -/
theorem integral_legendreScaled_sq (N : ℕ) :
    ∫ t in (-1 : ℝ)..1, ((legendreScaled N).eval t) ^ 2 =
      (2 : ℝ) ^ (2 * N + 1) / (2 * N + 1 : ℝ) := by
  have hfac : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hstep := integral_mul_rodrigues_ibp N (legendreScaled N) N le_rfl
  have hdn : derivative^[N] (legendreScaled N) =
      Polynomial.C ((N.factorial : ℝ) * ((2 * N).choose N : ℝ)) := by
    have hmon : (Polynomial.C (((2 * N).choose N : ℝ)⁻¹) * legendreScaled N).Monic := by
      rw [Polynomial.Monic, leadingCoeff_mul, leadingCoeff_C, legendreScaled_leadingCoeff]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
    have hdeg : (Polynomial.C (((2 * N).choose N : ℝ)⁻¹) * legendreScaled N).natDegree = N := by
      rw [natDegree_C_mul (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')),
        legendreScaled_natDegree]
    have hm := derivative_iterate_monic _ hmon
    rw [hdeg] at hm
    have hlin : ∀ (c : ℝ) (p : Polynomial ℝ) (r : ℕ),
        derivative^[r] (Polynomial.C c * p) = Polynomial.C c * derivative^[r] p := by
      intro c p r
      induction r with
      | zero => simp
      | succ m ihm =>
        rw [Function.iterate_succ_apply', ihm, derivative_mul, derivative_C, zero_mul, zero_add,
          Function.iterate_succ_apply']
    rw [hlin] at hm
    have hcb := congrArg (Polynomial.C ((2 * N).choose N : ℝ) * ·) hm
    simp only [← mul_assoc, ← map_mul] at hcb
    have hcpos : ((2 * N).choose N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [mul_inv_cancel₀ hcpos, map_one, one_mul] at hcb
    rw [hcb, mul_comm]
  have hL : (N.factorial : ℝ) * ∫ t in (-1 : ℝ)..1, ((legendreScaled N).eval t) ^ 2 =
      ∫ t in (-1 : ℝ)..1, (legendreScaled N).eval t *
        (derivative^[N] ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N)).eval t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hrod := congrArg (fun q : Polynomial ℝ => q.eval t) (legendreScaled_eq_rodrigues N)
    simp only [eval_mul, eval_C] at hrod
    rw [← hrod]; ring
  rw [hstep, hdn, Nat.sub_self, Function.iterate_zero_apply] at hL
  have hI : ∫ t in (-1 : ℝ)..1,
      (Polynomial.C ((N.factorial : ℝ) * ((2 * N).choose N : ℝ))).eval t *
        ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ N).eval t =
      (-1 : ℝ) ^ N * ((N.factorial : ℝ) * ((2 * N).choose N : ℝ)) *
        ∫ t in (-1 : ℝ)..1, (1 - t ^ 2) ^ N := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [eval_C, eval_pow, eval_sub, eval_X, eval_one]
    have hsign : (t ^ 2 - 1) ^ N = (-1 : ℝ) ^ N * (1 - t ^ 2) ^ N := by
      rw [show t ^ 2 - 1 = (-1 : ℝ) * (1 - t ^ 2) by ring, mul_pow]
    rw [hsign]; ring
  have hsign1 : ((-1 : ℝ) ^ N) * ((-1 : ℝ) ^ N) = 1 := by
    rw [← pow_add, ← two_mul, Even.neg_one_pow (even_two_mul N)]
  rw [hI, ← mul_assoc, ← mul_assoc, hsign1, one_mul, integral_one_sub_sq_pow N] at hL
  have hcomb : ((2 * N).choose N : ℝ) * (N.factorial : ℝ) ^ 2 = ((2 * N).factorial : ℝ) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial (show N ≤ 2 * N by omega)
    rw [show 2 * N - N = N by omega] at hnat
    have := congrArg (Nat.cast (R := ℝ)) hnat
    push_cast at this
    linarith [this, sq (N.factorial : ℝ)]
  have hfac2 : ((2 * N + 1).factorial : ℝ) = (2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h2n_nz : ((2 * N).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc ∫ t in (-1 : ℝ)..1, ((legendreScaled N).eval t) ^ 2
      = ((N.factorial : ℝ) * ∫ t in (-1 : ℝ)..1, ((legendreScaled N).eval t) ^ 2) /
          (N.factorial : ℝ) := by field_simp
    _ = ((N.factorial : ℝ) * ((2 * N).choose N : ℝ) *
          (2 ^ (2 * N + 1) * (N.factorial : ℝ) ^ 2 / ((2 * N + 1).factorial : ℝ))) /
          (N.factorial : ℝ) := by rw [hL]
    _ = (2 : ℝ) ^ (2 * N + 1) * (((2 * N).choose N : ℝ) * (N.factorial : ℝ) ^ 2) /
          ((2 * N + 1).factorial : ℝ) := by field_simp
    _ = (2 : ℝ) ^ (2 * N + 1) / (2 * N + 1 : ℝ) := by
          rw [hcomb, hfac2]; field_simp

/-- Monic Legendre polynomial integral on `[-1, 1]`: for `N` distinct roots `r` of
`legendreScaled N`, `∫_{-1}^1 (∏ k, (t - r k))^2 dt` equals the classical factorial formula. -/
theorem integral_monicLegendre_sq {N : ℕ} {r : Fin N → ℝ}
    (hprod : legendreScaled N =
      Polynomial.C ((2 * N).choose N : ℝ) * ∏ k : Fin N, (Polynomial.X - Polynomial.C (r k))) :
    ∫ t in (-1 : ℝ)..1, (∏ k : Fin N, (t - r k)) ^ 2 =
      2 ^ (2 * N + 1) * (N.factorial : ℝ) ^ 4 /
        ((2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 2) := by
  have hc : ((2 * N).choose N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hval := integral_legendreScaled_sq N
  have heval : ∀ t : ℝ, ((legendreScaled N).eval t) ^ 2 =
      ((2 * N).choose N : ℝ) ^ 2 * (∏ k : Fin N, (t - r k)) ^ 2 := by
    intro t
    rw [hprod, eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    ring
  simp_rw [heval, intervalIntegral.integral_const_mul] at hval
  have hch : ((2 * N).choose N : ℝ) = ((2 * N).factorial : ℝ) / (N.factorial : ℝ) ^ 2 := by
    have hnat := Nat.choose_mul_factorial_mul_factorial (show N ≤ 2 * N by omega)
    rw [show 2 * N - N = N by omega] at hnat
    have := congrArg (Nat.cast (R := ℝ)) hnat
    push_cast at this
    have hnz : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
    field_simp
    linarith [sq (N.factorial : ℝ)]
  calc ∫ t in (-1 : ℝ)..1, (∏ k : Fin N, (t - r k)) ^ 2
      = ((2 : ℝ) ^ (2 * N + 1) / (2 * N + 1 : ℝ)) / ((2 * N).choose N : ℝ) ^ 2 := by
          rw [← hval]; field_simp
    _ = 2 ^ (2 * N + 1) * (N.factorial : ℝ) ^ 4 /
          ((2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 2) := by
          rw [hch]
          have hnz : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
          have hnz2 : ((2 * N).factorial : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * N))
          field_simp

/-- Factorization of a polynomial of degree `N` having `N` strictly increasing roots. -/
theorem eq_leadingCoeff_mul_prod_of_roots {N : ℕ} {p : Polynomial ℝ}
    (hdeg : p.natDegree = N) {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_root : ∀ k : Fin N, p.eval (r k) = 0) :
    p = Polynomial.C p.leadingCoeff * ∏ k : Fin N, (Polynomial.X - Polynomial.C (r k)) := by
  by_cases hpz : p = 0
  · subst hpz; simp
  have hprod_dvd : ∀ s : Finset (Fin N),
      (∏ k ∈ s, (Polynomial.X - Polynomial.C (r k))) ∣ p := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        rcases ih with ⟨q, hq⟩
        have hroot_a : (p.eval (r a)) = 0 := hr_root a
        rw [hq, eval_mul, eval_prod] at hroot_a
        have hne : (∏ k ∈ s, (Polynomial.X - Polynomial.C (r k)).eval (r a)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
          simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
          exact hr_mono.injective.ne fun h => ha (h ▸ hk)
        have hqa : q.eval (r a) = 0 := (mul_eq_zero.mp hroot_a).resolve_left hne
        obtain ⟨q', hq'⟩ := Polynomial.dvd_iff_isRoot.mpr hqa
        refine ⟨q', ?_⟩
        rw [hq, hq']; ring
  rcases hprod_dvd Finset.univ with ⟨c, hc⟩
  have hmon : (∏ k : Fin N, (Polynomial.X - Polynomial.C (r k))).Monic :=
    monic_prod_of_monic _ _ fun k _ => monic_X_sub_C (r k)
  have hdeg_prod : (∏ k : Fin N, (Polynomial.X - Polynomial.C (r k))).natDegree = N := by
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C (r k))]
    simp
  have hc_ne : c ≠ 0 := fun h => hpz (by simpa [h] using hc)
  have hdeg_add : p.natDegree = N + c.natDegree := by
    have hmul_ne : (∏ k : Fin N, (Polynomial.X - Polynomial.C (r k))).leadingCoeff *
        c.leadingCoeff ≠ 0 := by
      rw [hmon.leadingCoeff, one_mul]; exact leadingCoeff_ne_zero.mpr hc_ne
    rw [hc, natDegree_mul' hmul_ne, hdeg_prod]
  have hc0 : c.natDegree = 0 := by omega
  have hlead : p.leadingCoeff = c.coeff 0 := by
    rw [hc, leadingCoeff_mul, hmon.leadingCoeff, one_mul, Polynomial.leadingCoeff, hc0]
  rw [Polynomial.eq_C_of_natDegree_eq_zero hc0] at hc
  rw [hlead, hc, mul_comm]

/-- Divided-difference quotient polynomial `(p(X) - p(r)) / (X - r)` computed explicitly via
`geom_sum₂`. -/
noncomputable def polyQuotAt (p : Polynomial ℝ) (r : ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff j) *
      ∑ i ∈ Finset.range j, Polynomial.C (r ^ (j - 1 - i)) * Polynomial.X ^ i

/-- Pointwise polynomial identity `polyQuotAt p r * (X - C r) = p - C (p.eval r)`. -/
theorem polyQuotAt_mul_X_sub_C (p : Polynomial ℝ) (r : ℝ) :
    polyQuotAt p r * (Polynomial.X - Polynomial.C r) = p - Polynomial.C (p.eval r) := by
  have hgeo : ∀ j : ℕ, (∑ i ∈ Finset.range j, Polynomial.C (r ^ (j - 1 - i)) * Polynomial.X ^ i) *
      (Polynomial.X - Polynomial.C r) = Polynomial.X ^ j - Polynomial.C (r ^ j) := by
    intro j
    have hrev : ∑ i ∈ Finset.range j, Polynomial.C (r ^ (j - 1 - i)) * Polynomial.X ^ i =
        ∑ i ∈ Finset.range j, Polynomial.X ^ i * (Polynomial.C r) ^ (j - 1 - i) := by
      refine Finset.sum_congr rfl fun i _ => by rw [map_pow, mul_comm]
    rw [hrev, geom_sum₂_mul, map_pow]
  unfold polyQuotAt
  rw [Finset.sum_mul]
  calc ∑ j ∈ Finset.range (p.natDegree + 1),
          Polynomial.C (p.coeff j) *
            (∑ i ∈ Finset.range j, Polynomial.C (r ^ (j - 1 - i)) * Polynomial.X ^ i) *
            (Polynomial.X - Polynomial.C r)
      = ∑ j ∈ Finset.range (p.natDegree + 1),
          (Polynomial.C (p.coeff j) * Polynomial.X ^ j -
            Polynomial.C (p.coeff j * r ^ j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_assoc, hgeo j, mul_sub, ← map_mul]
    _ = (∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.C (p.coeff j) * Polynomial.X ^ j) -
          Polynomial.C (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * r ^ j) := by
          rw [Finset.sum_sub_distrib, map_sum]
    _ = p - Polynomial.C (p.eval r) := by
          have hp : p = ∑ j ∈ Finset.range (p.natDegree + 1),
              Polynomial.C (p.coeff j) * Polynomial.X ^ j := by
            conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
          congr 1
          · exact hp.symm
          · congr 1
            conv_rhs => rw [hp]
            rw [eval_finset_sum_eq]
            refine Finset.sum_congr rfl fun j _ => by simp

/-- Cauchy-integral polynomial whose value at `r` equals `∫_{-1}^1 (p(t) - p(r)) / (t - r) dt`. -/
noncomputable def cauchyIntPoly (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff j) *
      ∑ i ∈ Finset.range j,
        if Even i then Polynomial.C (2 / (i + 1 : ℝ)) * Polynomial.X ^ (j - 1 - i)
        else 0

/-- Exact evaluation formula for `cauchyIntPoly p`. -/
theorem cauchyIntPoly_eval (p : Polynomial ℝ) (r : ℝ) :
    (cauchyIntPoly p).eval r = ∫ t in (-1 : ℝ)..1, (polyQuotAt p r).eval t := by
  have hint_pow : ∀ i : ℕ, ∫ t in (-1 : ℝ)..1, t ^ i =
      if Even i then (2 : ℝ) / (i + 1 : ℝ) else 0 := by
    intro i
    rw [integral_pow]
    rcases Nat.even_or_odd i with he | ho
    · have hodd : Odd (i + 1) := he.add_one
      rw [hodd.neg_one_pow, ite_eq_left_iff.mpr fun h => (h he).elim]
      ring
    · have hev : Even (i + 1) := ho.add_one
      have hne : ¬ Even i := Nat.not_even_iff_odd.mpr ho
      rw [hev.neg_one_pow, ite_eq_right_iff.mpr fun h => (hne h).elim]
      norm_num
  unfold polyQuotAt cauchyIntPoly
  simp only [eval_finset_sum_eq, eval_mul, eval_C, eval_pow, eval_X]
  rw [intervalIntegral_sum_eq (Finset.range (p.natDegree + 1)) _ (fun j _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_sum_eq (Finset.range j) _ (fun i _ =>
      (Continuous.intervalIntegrable (by fun_prop) _ _))]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, hint_pow i]
  by_cases he : Even i
  · simp only [he, ↓reduceIte, eval_mul, eval_C, eval_pow, eval_X]; ring
  · simp only [he, ↓reduceIte, eval_zero, mul_zero]

/-- Unshifted Lagrange basis polynomial `ℓ_k(X)` on the node family `r : Fin N → ℝ`. -/
noncomputable def lagrangeBasis {N : ℕ} (r : Fin N → ℝ) (k : Fin N) : Polynomial ℝ :=
  ∏ m ∈ Finset.univ.erase k,
    Polynomial.C ((r k - r m)⁻¹) * (Polynomial.X - Polynomial.C (r m))

/-- Value of `lagrangeBasis r k` at every node `r m`. -/
theorem lagrangeBasis_eval {N : ℕ} {r : Fin N → ℝ} (hr : Function.Injective r) (k m : Fin N) :
    (lagrangeBasis r k).eval (r m) = if m = k then 1 else 0 := by
  unfold lagrangeBasis
  rw [eval_prod]
  by_cases hmk : m = k
  · subst hmk
    rw [ite_eq_left_iff.mpr fun h => (h rfl).elim]
    refine Finset.prod_eq_one fun j hj => ?_
    have hne : r m - r j ≠ 0 := sub_ne_zero.mpr (hr.ne (Finset.ne_of_mem_erase hj).symm)
    simp [inv_mul_cancel₀ hne]
  · rw [ite_eq_right_iff.mpr fun h => (hmk h).elim]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hmk, Finset.mem_univ m⟩) ?_
    simp

/-- Degree of `lagrangeBasis r k` is at most `N - 1` (hence `< N` when `0 < N`). -/
theorem lagrangeBasis_natDegree_le {N : ℕ} (r : Fin N → ℝ) (k : Fin N) :
    (lagrangeBasis r k).natDegree ≤ N - 1 := by
  have hdeg_le : (lagrangeBasis r k).natDegree ≤ N - 1 := by
    unfold lagrangeBasis
    have hprod : (∏ m ∈ Finset.univ.erase k,
        Polynomial.C ((r k - r m)⁻¹) * (Polynomial.X - Polynomial.C (r m))).natDegree ≤
        ∑ m ∈ Finset.univ.erase k,
          (Polynomial.C ((r k - r m)⁻¹) * (Polynomial.X - Polynomial.C (r m))).natDegree :=
      natDegree_prod_le _ _
    have hsum : ∑ m ∈ Finset.univ.erase k,
        (Polynomial.C ((r k - r m)⁻¹) * (Polynomial.X - Polynomial.C (r m))).natDegree ≤
        ∑ _m ∈ Finset.univ.erase k, 1 := by
      refine Finset.sum_le_sum fun m _ => ?_
      exact (natDegree_C_mul_le _ _).trans (by simp)
    exact hprod.trans (hsum.trans_eq (by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]))
  exact hdeg_le

/-- Gauss–Legendre quadrature weight `w_k = ∫_{-1}^1 ℓ_k(t) dt`. -/
noncomputable def gaussWeight {N : ℕ} (r : Fin N → ℝ) (k : Fin N) : ℝ :=
  ∫ t in (-1 : ℝ)..1, (lagrangeBasis r k).eval t

/-- Exact formula expressing `gaussWeight r k` as a single rational ratio evaluated at `r k`. -/
theorem gaussWeight_eq_cauchyInt_div_deriv {N : ℕ} {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_root : ∀ k : Fin N, (legendreScaled N).eval (r k) = 0) (k : Fin N) :
    gaussWeight r k =
      (cauchyIntPoly (legendreScaled N)).eval (r k) /
        (legendreScaled N).derivative.eval (r k) := by
  set p := legendreScaled N
  have hfac : p = Polynomial.C p.leadingCoeff *
      ∏ m : Fin N, (Polynomial.X - Polynomial.C (r m)) :=
    eq_leadingCoeff_mul_prod_of_roots (legendreScaled_natDegree N) hr_mono hr_root
  have hsplit : p = (Polynomial.C p.leadingCoeff *
      ∏ m ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (r m))) *
      (Polynomial.X - Polynomial.C (r k)) := by
    conv_lhs => rw [hfac, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    ring
  have hquot : polyQuotAt p (r k) =
      Polynomial.C p.leadingCoeff *
        ∏ m ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (r m)) := by
    have hmul : polyQuotAt p (r k) * (Polynomial.X - Polynomial.C (r k)) =
        (Polynomial.C p.leadingCoeff *
          ∏ m ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (r m))) *
        (Polynomial.X - Polynomial.C (r k)) := by
      rw [polyQuotAt_mul_X_sub_C, hr_root k, map_zero, sub_zero, ← hsplit]
    exact mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero (r k)) hmul
  have hderiv_val : p.derivative.eval (r k) =
      p.leadingCoeff * ∏ m ∈ Finset.univ.erase k, (r k - r m) := by
    conv_lhs => rw [hsplit]
    rw [derivative_mul, derivative_X_sub_C, mul_one, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, mul_zero, zero_add, eval_mul, eval_C, eval_prod]
    simp [eval_sub, eval_X, eval_C]
  have hlead_ne : p.leadingCoeff ≠ 0 := by
    rw [legendreScaled_leadingCoeff]
    exact Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hprod_ne : (∏ m ∈ Finset.univ.erase k, (r k - r m)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun m hm =>
      sub_ne_zero.mpr (hr_mono.injective.ne (Finset.ne_of_mem_erase hm).symm)
  have hd_ne : p.derivative.eval (r k) ≠ 0 := by
    rw [hderiv_val]; exact mul_ne_zero hlead_ne hprod_ne
  have hlag : ∀ t : ℝ, (lagrangeBasis r k).eval t =
      (polyQuotAt p (r k)).eval t / p.derivative.eval (r k) := by
    intro t
    unfold lagrangeBasis
    rw [hquot, hderiv_val, eval_prod, eval_mul, eval_C, eval_prod]
    simp only [eval_mul, eval_C, eval_sub, eval_X]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    field_simp
  unfold gaussWeight
  rw [cauchyIntPoly_eval p (r k), ← intervalIntegral.integral_div]
  exact intervalIntegral.integral_congr fun t _ => hlag t

/-- Exactness of Gauss–Legendre quadrature on `[-1, 1]` for all polynomials of degree `< 2 * N`. -/
theorem gaussQuad_exact {N : ℕ} (hN : 0 < N) {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_root : ∀ k : Fin N, (legendreScaled N).eval (r k) = 0)
    (f : Polynomial ℝ) (hdeg : f.natDegree < 2 * N) :
    ∫ t in (-1 : ℝ)..1, f.eval t = ∑ k : Fin N, gaussWeight r k * f.eval (r k) := by
  set p := legendreScaled N
  have hfac := eq_leadingCoeff_mul_prod_of_roots (legendreScaled_natDegree N) hr_mono hr_root
  let pMon : Polynomial ℝ := ∏ k : Fin N, (Polynomial.X - Polynomial.C (r k))
  have hmon : pMon.Monic := monic_prod_of_monic _ _ fun k _ => monic_X_sub_C (r k)
  have hdeg_pMon : pMon.natDegree = N := by
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C (r k)]
    simp
  set q := f /ₘ pMon
  set rem := f %ₘ pMon
  have hdiv : rem + pMon * q = f := modByMonic_add_div f pMon
  have hdeg_rem : rem.natDegree < N := by
    by_cases hp1 : pMon.natDegree = 0
    · omega
    · rw [← hdeg_pMon]
      exact natDegree_modByMonic_lt f hmon (fun h => by
        have := congrArg Polynomial.natDegree h; rw [natDegree_one] at this; omega)
  have hdeg_q : q.natDegree < N := by
    by_cases hq : q = 0
    · simpa [hq] using hN
    · have hpq_le : (pMon * q).natDegree ≤ max f.natDegree rem.natDegree := by
        have h : pMon * q = f - rem := by rw [← hdiv]; ring
        rw [h]; exact natDegree_sub_le f rem
      have hmul : (pMon * q).natDegree = N + q.natDegree := by
        rw [hmon.natDegree_mul' hq, hdeg_pMon]
      have hmax : max f.natDegree rem.natDegree < 2 * N := max_lt hdeg (by omega)
      omega
  have hrem_interp : rem = ∑ k : Fin N, Polynomial.C (f.eval (r k)) * lagrangeBasis r k := by
    let diff := rem - ∑ k : Fin N, Polynomial.C (f.eval (r k)) * lagrangeBasis r k
    have hdeg_diff : diff.natDegree < N := by
      refine (natDegree_sub_le _ _).trans_lt (max_lt hdeg_rem ?_)
      refine natDegree_finset_sum_lt _ _ hN fun k _ => ?_
      exact (natDegree_C_mul_le _ _).trans_lt (by
        have := lagrangeBasis_natDegree_le r k; omega)
    have hroots : ∀ k : Fin N, diff.eval (r k) = 0 := by
      intro k
      have hrem_k : rem.eval (r k) = f.eval (r k) := by
        have h := congrArg (fun u : Polynomial ℝ => u.eval (r k)) hdiv
        have hpk : pMon.eval (r k) = 0 := by
          rw [eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
        simpa [hpk] using h
      simp only [diff, eval_sub, eval_finset_sum_eq, eval_mul, eval_C,
        lagrangeBasis_eval hr_mono.injective]
      rw [hrem_k, Finset.sum_eq_single k]
      · simp
      · intro j _ hne; simp [hne.symm]
      · intro h; simp at h
    have hdiff0 : diff = 0 := by
      by_contra hne
      have hcard : N ≤ diff.roots.card := by
        have hmem : ∀ k : Fin N, r k ∈ diff.roots := fun k =>
          (mem_roots hne).mpr (hroots k)
        calc N = (Finset.univ : Finset (Fin N)).card := (Fintype.card_fin N).symm
          _ = ((Finset.univ : Finset (Fin N)).image r).card :=
              (Finset.card_image_of_injective _ hr_mono.injective).symm
          _ ≤ diff.roots.toFinset.card := Finset.card_le_card fun x hx => by
              rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
              exact Multiset.mem_toFinset.mpr (hmem k)
          _ ≤ diff.roots.card := Multiset.toFinset_card_le _
      have hbd := Polynomial.card_roots' diff
      omega
    exact sub_eq_zero.mp hdiff0
  have horth : ∫ t in (-1 : ℝ)..1, pMon.eval t * q.eval t = 0 := by
    have hlead : p.leadingCoeff ≠ 0 := by
      rw [legendreScaled_leadingCoeff]
      exact Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    have h := integral_mul_legendreScaled_eq_zero (N := N) hdeg_q
    have hrew : ∀ t : ℝ, q.eval t * p.eval t = p.leadingCoeff * (pMon.eval t * q.eval t) := by
      intro t
      have hpe : p.eval t = p.leadingCoeff * pMon.eval t := by
        have := congrArg (fun u : Polynomial ℝ => u.eval t) hfac
        simpa [eval_mul, eval_C, p, pMon] using this
      rw [hpe]; ring
    have hcon : ∫ t in (-1 : ℝ)..1, q.eval t * p.eval t =
        p.leadingCoeff * ∫ t in (-1 : ℝ)..1, pMon.eval t * q.eval t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => hrew t
    rw [hcon] at h
    exact (mul_eq_zero.mp h).resolve_left hlead
  calc ∫ t in (-1 : ℝ)..1, f.eval t
      = ∫ t in (-1 : ℝ)..1, (rem.eval t + pMon.eval t * q.eval t) := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [← hdiv, eval_add, eval_mul]
    _ = (∫ t in (-1 : ℝ)..1, rem.eval t) + ∫ t in (-1 : ℝ)..1, pMon.eval t * q.eval t :=
          intervalIntegral.integral_add ((poly_continuous rem).intervalIntegrable _ _)
            (((poly_continuous pMon).mul (poly_continuous q)).intervalIntegrable _ _)
    _ = ∫ t in (-1 : ℝ)..1, rem.eval t := by rw [horth, add_zero]
    _ = ∑ k : Fin N, gaussWeight r k * f.eval (r k) := by
          rw [hrem_interp]
          have hsum_eval : ∀ t : ℝ, (∑ k : Fin N, Polynomial.C (f.eval (r k)) *
              lagrangeBasis r k).eval t =
              ∑ k : Fin N, f.eval (r k) * (lagrangeBasis r k).eval t := fun t => by
            rw [eval_finset_sum_eq]
            refine Finset.sum_congr rfl fun k _ => by simp [eval_mul, eval_C]
          simp_rw [hsum_eval]
          rw [intervalIntegral_sum_eq Finset.univ
            (fun k t => f.eval (r k) * (lagrangeBasis r k).eval t) fun k _ =>
              (continuous_const.mul (poly_continuous (lagrangeBasis r k))).intervalIntegrable
                _ _]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [intervalIntegral.integral_const_mul, mul_comm, gaussWeight]

/-- Positivity of every Gauss–Legendre weight `w_k = ∫_{-1}^1 ℓ_k(t)^2 dt > 0`. -/
theorem gaussWeight_pos {N : ℕ} (hN : 0 < N) {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_root : ∀ k : Fin N, (legendreScaled N).eval (r k) = 0) (k : Fin N) :
    0 < gaussWeight r k := by
  have hdeg : ((lagrangeBasis r k) ^ 2).natDegree < 2 * N := by
    calc ((lagrangeBasis r k) ^ 2).natDegree ≤ 2 * (lagrangeBasis r k).natDegree :=
          natDegree_pow_le
      _ ≤ 2 * (N - 1) := Nat.mul_le_mul_left 2 (lagrangeBasis_natDegree_le r k)
      _ < 2 * N := by omega
  have heq := gaussQuad_exact hN hr_mono hr_root ((lagrangeBasis r k) ^ 2) hdeg
  have hsum : ∑ m : Fin N, gaussWeight r m * ((lagrangeBasis r k) ^ 2).eval (r m) =
      gaussWeight r k := by
    rw [Finset.sum_eq_single k]
    · simp [eval_pow, lagrangeBasis_eval hr_mono.injective]
    · intro m _ hne; simp [eval_pow, lagrangeBasis_eval hr_mono.injective, hne]
    · intro h; simp at h
  rw [hsum] at heq
  rw [← heq]
  have hcont : Continuous fun t : ℝ => ((lagrangeBasis r k).eval t) ^ 2 :=
    (poly_continuous (lagrangeBasis r k)).pow 2
  have hpos_val : ∃ t ∈ Set.Icc (-1 : ℝ) 1, 0 < ((lagrangeBasis r k).eval t) ^ 2 := by
    by_cases h0 : (lagrangeBasis r k).eval 0 = 0
    · -- Since `lagrangeBasis r k ≠ 0`, pick a non-root point in `[-1, 1]`
      by_contra hnone
      push Not at hnone
      have hzero : ∀ t ∈ Set.Icc (-1 : ℝ) 1, (lagrangeBasis r k).eval t = 0 := fun t ht => by
        have hle := hnone t ht
        exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
      have hnz : lagrangeBasis r k ≠ 0 := by
        intro h; have := congrArg (fun p : Polynomial ℝ => p.eval (r k)) h
        simp [lagrangeBasis_eval hr_mono.injective] at this
      have hinf : (Set.Icc (-1 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
      have hsub : Set.Icc (-1 : ℝ) 1 ⊆ (lagrangeBasis r k).roots.toFinset := fun t ht =>
        Multiset.mem_toFinset.mpr ((mem_roots hnz).mpr (hzero t ht))
      exact hinf ((lagrangeBasis r k).roots.toFinset.finite_toSet.subset hsub)
    · exact ⟨0, by norm_num, sq_pos_of_ne_zero h0⟩
  rcases hpos_val with ⟨c, hc, hcp⟩
  have h_le : (-1 : ℝ) ≤ 1 := by norm_num
  have hpos_int := intervalIntegral.integral_pos (by norm_num : (-1 : ℝ) < 1)
    hcont.continuousOn (fun t _ => sq_nonneg _) ⟨c, hc, hcp⟩
  simpa [eval_pow] using hpos_int

/-- Sum of Gauss–Legendre weights on `[-1, 1]` equals `2`. -/
theorem sum_gaussWeight {N : ℕ} (hN : 0 < N) {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_root : ∀ k : Fin N, (legendreScaled N).eval (r k) = 0) :
    ∑ k : Fin N, gaussWeight r k = 2 := by
  have h := gaussQuad_exact hN hr_mono hr_root (1 : Polynomial ℝ) (by simp; omega)
  simp only [eval_one, mul_one, intervalIntegral.integral_const, smul_eq_mul] at h
  linarith [h]

/-- Generalized Rolle's theorem: `m + 1` strictly increasing zeros of a `C^m` function `f`
produce a zero of `iteratedDeriv m f` in `[s 0, s (Fin.last m)]`. -/
private theorem exists_iteratedDeriv_eq_zero_of_zeros {m : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ m f) {s : Fin (m + 1) → ℝ} (hs : StrictMono s)
    (hz : ∀ i : Fin (m + 1), f (s i) = 0) :
    ∃ ξ ∈ Set.Icc (s 0) (s (Fin.last m)), iteratedDeriv m f ξ = 0 := by
  induction m generalizing f with
  | zero =>
      exact ⟨s 0, ⟨le_rfl, le_rfl⟩, by simpa [iteratedDeriv_zero] using hz 0⟩
  | succ k ih =>
      have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
      have hmid : ∀ i : Fin (k + 1), ∃ y ∈ Set.Ioo (s i.castSucc) (s i.succ), deriv f y = 0 := by
        intro i
        have hlt : s i.castSucc < s i.succ := hs Fin.castSucc_lt_succ
        exact exists_deriv_eq_zero hlt hdiff.continuous.continuousOn
          (by rw [hz i.castSucc, hz i.succ])
      choose y hy_mem hy_zero using hmid
      have hy_mono : StrictMono y := by
        intro i j hij
        have hle : i.succ ≤ j.castSucc := by
          change i.1 + 1 ≤ j.1; exact hij
        calc y i < s i.succ := (hy_mem i).2
          _ ≤ s j.castSucc := hs.monotone hle
          _ < y j := (hy_mem j).1
      have hf' : ContDiff ℝ k (deriv f) := by
        have := (contDiff_succ_iff_deriv (n := (k : ℕ))).mp hf
        exact this.2.2
      obtain ⟨ξ, hξ_mem, hξ_zero⟩ := ih hf' hy_mono hy_zero
      refine ⟨ξ, ?_, ?_⟩
      · have hlo : s 0 ≤ y 0 :=
          (hs.monotone (Fin.zero_le _)).trans (hy_mem 0).1.le
        have hhi : y (Fin.last k) ≤ s (Fin.last (k + 1)) :=
          (hy_mem (Fin.last k)).2.le.trans (hs.monotone (Fin.le_last _))
        exact ⟨hlo.trans hξ_mem.1, hξ_mem.2.trans hhi⟩
      · rwa [iteratedDeriv_succ']

/-- Hermite interpolation polynomial matching both `g` and `deriv g` at `N` distinct nodes `x`. -/
noncomputable def hermitePoly {N : ℕ} (x : Fin N → ℝ) (g : ℝ → ℝ) : Polynomial ℝ :=
  ∑ k : Fin N,
    let l := lagrangeBasis x k
    let lp := l.derivative.eval (x k)
    ((1 - Polynomial.C (2 * lp) * (Polynomial.X - Polynomial.C (x k))) *
      Polynomial.C (g (x k)) +
      (Polynomial.X - Polynomial.C (x k)) * Polynomial.C (deriv g (x k))) * l ^ 2

/-- `hermitePoly x g` has degree strictly less than `2 * N` (for `0 < N`). -/
private theorem hermitePoly_natDegree_lt {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) (g : ℝ → ℝ) :
    (hermitePoly x g).natDegree < 2 * N := by
  refine natDegree_finset_sum_lt _ _ (by omega) fun k _ => ?_
  dsimp only
  have hl : (lagrangeBasis x k).natDegree ≤ N - 1 := lagrangeBasis_natDegree_le x k
  have hl2 : ((lagrangeBasis x k) ^ 2).natDegree ≤ 2 * (N - 1) :=
    natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hl)
  have hlin1 : ((1 - Polynomial.C (2 * (lagrangeBasis x k).derivative.eval (x k)) *
      (Polynomial.X - Polynomial.C (x k))) * Polynomial.C (g (x k))).natDegree ≤ 1 := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_C, add_zero]
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hlin2 : ((Polynomial.X - Polynomial.C (x k)) * Polynomial.C (deriv g (x k))).natDegree ≤
      1 := by
    refine (natDegree_mul_le).trans ?_
    rw [natDegree_C, add_zero]; simp
  have hlin := (natDegree_add_le _ _).trans (max_le hlin1 hlin2)
  exact natDegree_mul_le.trans_lt (by omega)

/-- `hermitePoly x g` matches `g` and `deriv g` at every node `x m`. -/
private theorem hermitePoly_spec {N : ℕ} {x : Fin N → ℝ} (hx : Function.Injective x)
    (g : ℝ → ℝ) (m : Fin N) :
    (hermitePoly x g).eval (x m) = g (x m) ∧
    (hermitePoly x g).derivative.eval (x m) = deriv g (x m) := by
  have heval_k : ∀ k : Fin N, (lagrangeBasis x k).eval (x m) = if m = k then 1 else 0 :=
    fun k => lagrangeBasis_eval hx k m
  constructor
  · unfold hermitePoly
    rw [eval_finset_sum_eq, Finset.sum_eq_single m]
    · simp [heval_k m]
    · intro k _ hne; simp [heval_k k, hne.symm]
    · intro h; simp at h
  · unfold hermitePoly
    rw [map_sum, eval_finset_sum_eq, Finset.sum_eq_single m]
    · set l := lagrangeBasis x m
      set lp := l.derivative.eval (x m)
      have hlm : l.eval (x m) = 1 := by simp [l, heval_k m]
      rw [derivative_mul, derivative_pow, derivative_add, derivative_mul, derivative_C, mul_zero,
        add_zero, derivative_sub, derivative_one, zero_sub, derivative_mul, derivative_C,
        zero_mul, zero_add, derivative_X_sub_C, mul_one, derivative_mul, derivative_C, mul_zero,
        add_zero, derivative_X_sub_C]
      simp only [eval_add, eval_mul, eval_neg, eval_sub, eval_X, eval_C, eval_one, eval_pow,
        sub_self, mul_zero, zero_mul, add_zero, sub_zero, hlm, one_pow, mul_one,
        one_mul]
      change -(2 * lp) * g (x m) + deriv g (x m) + g (x m) * (2 * lp) = deriv g (x m)
      ring
    · intro k _ hne
      set l := lagrangeBasis x k
      have hlk : l.eval (x m) = 0 := by simp [l, heval_k k, hne.symm]
      rw [derivative_mul, derivative_pow]
      simp [eval_add, eval_mul, eval_pow, hlk]
    · intro h; simp at h

/-- 1D Gauss–Legendre error theorem on `[a, b]`, specialized via affine shift from `[-1, 1]` to
`[0, L]`. -/
theorem abs_integral_sub_gaussQuad_le {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L)
    {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_range : ∀ k : Fin N, r k ∈ Set.Ioo (-1 : ℝ) 1)
    (hr_root : ∀ k : Fin N, (legendreScaled N).eval (r k) = 0)
    {g : ℝ → ℝ} (hg : ContDiff ℝ (2 * N) g) {M : ℝ} (_hM : 0 ≤ M)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) L, |iteratedDeriv (2 * N) g t| ≤ M) :
    |(∫ t in (0 : ℝ)..L, g t) -
        ∑ k : Fin N, (L / 2 * gaussWeight r k) * g (L / 2 * (r k + 1))| ≤
      M * L ^ (2 * N + 1) * (N.factorial : ℝ) ^ 4 /
        ((2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 3) := by
  let x : Fin N → ℝ := fun k => L / 2 * (r k + 1)
  let w : Fin N → ℝ := fun k => L / 2 * gaussWeight r k
  have hx_mono : StrictMono x := fun i j hij => by
    dsimp only [x]
    have := hr_mono hij
    nlinarith [half_pos hL]
  have hx_mem : ∀ k : Fin N, x k ∈ Set.Ioo (0 : ℝ) L := fun k => by
    have ⟨h1, h2⟩ := hr_range k
    dsimp only [x]; exact ⟨by nlinarith, by nlinarith⟩
  let pMon : Polynomial ℝ := ∏ k : Fin N, (Polynomial.X - Polynomial.C (x k))
  have hpMon_monic : pMon.Monic := monic_prod_of_monic _ _ fun k _ => monic_X_sub_C (x k)
  have hpMon_deg : pMon.natDegree = N := by
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C (x k)]
    simp
  let H : Polynomial ℝ := hermitePoly x g
  have hH_deg : H.natDegree < 2 * N := hermitePoly_natDegree_lt hN x g
  -- Exactness of shifted Gauss–Legendre on polynomials of degree `< 2 * N`
  have hH_int : ∫ t in (0 : ℝ)..L, H.eval t = ∑ k : Fin N, w k * g (x k) := by
    let phi : Polynomial ℝ := Polynomial.C (L / 2) * (Polynomial.X + 1)
    let Hs : Polynomial ℝ := H.comp phi
    have hphi_deg : phi.natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_add_le _ _).trans (by simp)
    have hHs_deg : Hs.natDegree < 2 * N := by
      refine natDegree_comp_le.trans_lt ?_
      have : H.natDegree * phi.natDegree ≤ H.natDegree := by
        simpa using Nat.mul_le_mul_left H.natDegree hphi_deg
      omega
    have hsub : ∫ t in (0 : ℝ)..L, H.eval t =
        (L / 2) * ∫ s in (-1 : ℝ)..1, Hs.eval s := by
      have hc := intervalIntegral.integral_comp_mul_add (fun t => H.eval t)
        (show L / 2 ≠ 0 by positivity) (L / 2) (a := (-1 : ℝ)) (b := 1)
      have ha : L / 2 * (-1) + L / 2 = 0 := by ring
      have hb : L / 2 * 1 + L / 2 = L := by ring
      rw [ha, hb] at hc
      have heq : ∀ s : ℝ, Hs.eval s = H.eval (L / 2 * s + L / 2) := by
        intro s; simp only [Hs, eval_comp, phi, eval_mul, eval_C, eval_add, eval_X, eval_one]
        congr 1; ring
      simp_rw [heq]
      rw [smul_eq_mul] at hc
      rw [hc]
      field_simp
    rw [hsub, gaussQuad_exact hN hr_mono hr_root Hs hHs_deg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk_ev : Hs.eval (r k) = H.eval (x k) := by
      simp only [Hs, eval_comp, phi, eval_mul, eval_C, eval_add, eval_X, eval_one, x]
    rw [hk_ev, (hermitePoly_spec hx_mono.injective g k).1]
    dsimp only [w]
    ring
  -- Pointwise Hermite error bound on `[0, L]`
  have hpt : ∀ u ∈ Set.Icc (0 : ℝ) L,
      |g u - H.eval u| ≤ M / ((2 * N).factorial : ℝ) * (pMon.eval u) ^ 2 := by
    intro u hu
    by_cases hmem : ∃ k : Fin N, x k = u
    · rcases hmem with ⟨k, rfl⟩
      have h1 : g (x k) - H.eval (x k) = 0 := by
        rw [(hermitePoly_spec hx_mono.injective g k).1, sub_self]
      have h2 : pMon.eval (x k) = 0 := by
        rw [eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
      simp [h1, h2]
    · have hp_ne : pMon.eval u ≠ 0 := by
        rw [eval_prod]
        refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
        simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
        exact fun heq => hmem ⟨k, heq.symm⟩
      let K : ℝ := (g u - H.eval u) / (pMon.eval u) ^ 2
      let φ : ℝ → ℝ := fun t => g t - H.eval t - K * (pMon.eval t) ^ 2
      have hφ_cd : ContDiff ℝ (2 * N) φ :=
        (hg.sub (poly_contDiff H (2 * N))).sub
          (contDiff_const.mul ((poly_contDiff pMon (2 * N)).pow 2))
      have hφ_u : φ u = 0 := by
        dsimp only [φ, K]; field_simp; ring
      have hφ_x : ∀ k : Fin N, φ (x k) = 0 := fun k => by
        have hpk : pMon.eval (x k) = 0 := by
          rw [eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
        dsimp only [φ]
        rw [(hermitePoly_spec hx_mono.injective g k).1, hpk]; ring
      have hφ'_x : ∀ k : Fin N, deriv φ (x k) = 0 := fun k => by
        have hpk : pMon.eval (x k) = 0 := by
          rw [eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
        have hdg : HasDerivAt g (deriv g (x k)) (x k) :=
          (hg.differentiable (by
            have hne : N ≠ 0 := by omega
            simp [hne])).differentiableAt.hasDerivAt
        have hdH : HasDerivAt (fun t => H.eval t) (H.derivative.eval (x k)) (x k) :=
          H.hasDerivAt (x k)
        have hdp : HasDerivAt (fun t => (pMon.eval t) ^ 2)
            (2 * pMon.eval (x k) * pMon.derivative.eval (x k)) (x k) := by
          have hd := (pMon.hasDerivAt (x k)).pow 2
          exact hd.congr_deriv (by ring)
        have hdφ : HasDerivAt φ (deriv g (x k) - H.derivative.eval (x k) -
            K * (2 * pMon.eval (x k) * pMon.derivative.eval (x k))) (x k) :=
          (hdg.sub hdH).sub (hdp.const_mul K)
        rw [hdφ.deriv, (hermitePoly_spec hx_mono.injective g k).2, hpk]
        ring
      -- Build strictly increasing zeros `z : Fin (N + 1) → ℝ` of `φ` on `[0, L]`
      let Z : Finset ℝ := insert u (Finset.univ.image x)
      have hu_nmem : u ∉ Finset.univ.image x := by
        simp only [Finset.mem_image, Finset.mem_univ, true_and]; exact hmem
      have hZ_card : Z.card = N + 1 := by
        rw [Finset.card_insert_of_notMem hu_nmem,
          Finset.card_image_of_injective _ hx_mono.injective, Finset.card_univ, Fintype.card_fin]
      let z : Fin (N + 1) → ℝ := Z.orderEmbOfFin hZ_card
      have hz_mono : StrictMono z := (Z.orderEmbOfFin hZ_card).strictMono
      have hz_zero : ∀ i : Fin (N + 1), φ (z i) = 0 := fun i => by
        have hi : z i ∈ Z := Z.orderEmbOfFin_mem hZ_card i
        rcases Finset.mem_insert.mp hi with h | hxm
        · rw [h]; exact hφ_u
        · rcases Finset.mem_image.mp hxm with ⟨k, _, hk⟩; rw [← hk]; exact hφ_x k
      have hz_mem : ∀ i : Fin (N + 1), z i ∈ Set.Icc (0 : ℝ) L := fun i => by
        have hi : z i ∈ Z := Z.orderEmbOfFin_mem hZ_card i
        rcases Finset.mem_insert.mp hi with h | hxm
        · rw [h]; exact hu
        · rcases Finset.mem_image.mp hxm with ⟨k, _, hk⟩
          rw [← hk]; exact Set.Ioo_subset_Icc_self (hx_mem k)
      have hφ_diff : Differentiable ℝ φ :=
        hφ_cd.differentiable (by
          have hne : N ≠ 0 := by omega
          simp [hne])
      have hroll : ∀ i : Fin N, ∃ y ∈ Set.Ioo (z i.castSucc) (z i.succ), deriv φ y = 0 :=
        fun i => exists_deriv_eq_zero (hz_mono Fin.castSucc_lt_succ)
          hφ_diff.continuous.continuousOn (by rw [hz_zero i.castSucc, hz_zero i.succ])
      choose y hy_mem hy_zero using hroll
      have hy_mono : StrictMono y := fun i j hij => by
        have hle : i.succ ≤ j.castSucc := by change i.1 + 1 ≤ j.1; exact hij
        calc y i < z i.succ := (hy_mem i).2
          _ ≤ z j.castSucc := hz_mono.monotone hle
          _ < y j := (hy_mem j).1
      -- Each `y i` is strictly between consecutive elements of `Z`, hence `∉ Z` and `∉ image x`
      have hy_not_Z : ∀ i : Fin N, y i ∉ Z := fun i hyZ => by
        obtain ⟨r, hr⟩ : ∃ r : Fin (N + 1), z r = y i := by
          have hrg := Z.range_orderEmbOfFin hZ_card
          have hmem : y i ∈ Set.range (Z.orderEmbOfFin hZ_card) := by
            simpa [hrg] using hyZ
          exact hmem
        by_cases h1 : r ≤ i.castSucc
        · have : z r ≤ z i.castSucc := hz_mono.monotone h1
          linarith [hr, (hy_mem i).1]
        · have h2 : i.succ ≤ r := by
            have : i.castSucc < r := lt_of_not_ge h1
            change i.1 + 1 ≤ r.1; exact this
          have : z i.succ ≤ z r := hz_mono.monotone h2
          linarith [hr, (hy_mem i).2]
      have hdisj : Disjoint (Finset.univ.image x) (Finset.univ.image y) := by
        rw [Finset.disjoint_left]
        intro t htx hty
        rcases Finset.mem_image.mp hty with ⟨i, _, rfl⟩
        exact hy_not_Z i (Finset.mem_insert_of_mem htx)
      let W : Finset ℝ := Finset.univ.image x ∪ Finset.univ.image y
      have hW_card : W.card = 2 * N := by
        rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ hx_mono.injective,
          Finset.card_image_of_injective _ hy_mono.injective,
          Finset.card_univ, Fintype.card_fin]
        omega
      let w0 : Fin (2 * N - 1 + 1) → ℝ := W.orderEmbOfFin (by omega)
      have hw0_mono : StrictMono w0 := (W.orderEmbOfFin _).strictMono
      have hw0_zero : ∀ j : Fin (2 * N - 1 + 1), deriv φ (w0 j) = 0 := fun j => by
        have hj : w0 j ∈ W := W.orderEmbOfFin_mem _ j
        rcases Finset.mem_union.mp hj with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨k, _, hk⟩; rw [← hk]; exact hφ'_x k
        · rcases Finset.mem_image.mp h2 with ⟨i, _, hi⟩; rw [← hi]; exact hy_zero i
      have hw0_mem : ∀ j : Fin (2 * N - 1 + 1), w0 j ∈ Set.Icc (0 : ℝ) L := fun j => by
        have hj : w0 j ∈ W := W.orderEmbOfFin_mem _ j
        rcases Finset.mem_union.mp hj with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨k, _, hk⟩
          rw [← hk]; exact Set.Ioo_subset_Icc_self (hx_mem k)
        · rcases Finset.mem_image.mp h2 with ⟨i, _, hi⟩
          rw [← hi]
          exact ⟨(hz_mem i.castSucc).1.trans (hy_mem i).1.le,
            (hy_mem i).2.le.trans (hz_mem i.succ).2⟩
      have hφ'_cd : ContDiff ℝ (2 * N - 1) (deriv φ) := by
        have hstep : ContDiff ℝ (((2 * N - 1) + 1 : ℕ)) φ := by
          have heq : (2 * N - 1) + 1 = 2 * N := by omega
          rwa [heq]
        exact ((contDiff_succ_iff_deriv (n := (2 * N - 1 : ℕ))).mp hstep).2.2
      obtain ⟨ξ, hξ_mem, hξ_zero⟩ :=
        exists_iteratedDeriv_eq_zero_of_zeros hφ'_cd hw0_mono hw0_zero
      have hξ_in_Icc : ξ ∈ Set.Icc (0 : ℝ) L :=
        ⟨(hw0_mem 0).1.trans hξ_mem.1, hξ_mem.2.trans (hw0_mem (Fin.last _)).2⟩
      have hφ_deriv2N : iteratedDeriv (2 * N) φ ξ = 0 := by
        have h2n : 2 * N = (2 * N - 1) + 1 := by omega
        rw [h2n, iteratedDeriv_succ']
        exact hξ_zero
      -- Expand `iteratedDeriv (2 * N) φ ξ`
      have hH_d : iteratedDeriv (2 * N) (fun t => H.eval t) ξ = 0 := by
        rw [iteratedDeriv_polynomial_eval, derivative_iterate_eq_zero_of_natDegree_lt hH_deg]
        simp
      have hp2_monic : (pMon ^ 2).Monic := hpMon_monic.pow 2
      have hp2_deg : (pMon ^ 2).natDegree = 2 * N := by
        rw [hpMon_monic.natDegree_pow, hpMon_deg]
      have hp2_d : iteratedDeriv (2 * N) (fun t => (pMon.eval t) ^ 2) ξ =
          ((2 * N).factorial : ℝ) := by
        have heq : (fun t : ℝ => (pMon.eval t) ^ 2) = fun t => (pMon ^ 2).eval t := by
          ext t; simp [eval_pow]
        rw [heq, iteratedDeriv_polynomial_eval, ← hp2_deg, derivative_iterate_monic _ hp2_monic]
        dsimp only
        rw [eval_C, hp2_deg]
      have hsplit : iteratedDeriv (2 * N) φ ξ =
          iteratedDeriv (2 * N) g ξ - iteratedDeriv (2 * N) (fun t => H.eval t) ξ -
            K * iteratedDeriv (2 * N) (fun t => (pMon.eval t) ^ 2) ξ := by
        have hd_H : ContDiff ℝ (2 * N) (fun t : ℝ => H.eval t) := poly_contDiff H (2 * N)
        have hd_p : ContDiff ℝ (2 * N) (fun t : ℝ => K * (pMon.eval t) ^ 2) :=
          contDiff_const.mul ((poly_contDiff pMon (2 * N)).pow 2)
        have hlin : ∀ (m : ℕ) (f₁ f₂ : ℝ → ℝ),
            ContDiff ℝ m f₁ → ContDiff ℝ m f₂ →
              iteratedDeriv m (fun t => f₁ t - f₂ t) ξ =
                iteratedDeriv m f₁ ξ - iteratedDeriv m f₂ ξ := by
          intro m f₁ f₂ hf₁ hf₂
          rw [← Pi.sub_def]
          exact iteratedDeriv_sub hf₁.contDiffAt hf₂.contDiffAt
        have h1 := hlin (2 * N) (fun t => g t - H.eval t) (fun t => K * (pMon.eval t) ^ 2)
          (hg.sub hd_H) hd_p
        have h2 := hlin (2 * N) g (fun t => H.eval t) hg hd_H
        have hcm : iteratedDeriv (2 * N) (fun t => K * (pMon.eval t) ^ 2) ξ =
            K * iteratedDeriv (2 * N) (fun t => (pMon.eval t) ^ 2) ξ :=
          iteratedDeriv_const_mul_field (n := 2 * N) (x := ξ) K _
        dsimp only [φ]
        rw [h1, h2, hcm]
      rw [hsplit, hH_d, hp2_d, sub_zero] at hφ_deriv2N
      have hK_eq : K = iteratedDeriv (2 * N) g ξ / ((2 * N).factorial : ℝ) := by
        have hnz : ((2 * N).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        field_simp
        linarith
      have hK_abs : |K| ≤ M / ((2 * N).factorial : ℝ) := by
        rw [hK_eq, abs_div, abs_of_pos (a := ((2 * N).factorial : ℝ))
          (Nat.cast_pos.mpr (Nat.factorial_pos _))]
        exact div_le_div_of_nonneg_right (hderiv ξ hξ_in_Icc) (by positivity)
      have hgu : g u - H.eval u = K * (pMon.eval u) ^ 2 := by
        dsimp only [K]; field_simp
      rw [hgu, abs_mul, abs_of_nonneg (sq_nonneg (pMon.eval u))]
      exact mul_le_mul_of_nonneg_right hK_abs (sq_nonneg _)
  -- Integrate `|g - H|` over `[0, L]`
  have hp_int : ∫ t in (0 : ℝ)..L, (pMon.eval t) ^ 2 =
      L ^ (2 * N + 1) * (N.factorial : ℝ) ^ 4 /
        ((2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 2) := by
    have haff : ∀ s : ℝ, pMon.eval (L / 2 * (s + 1)) =
        (L / 2) ^ N * ∏ k : Fin N, (s - r k) := by
      intro s
      rw [eval_prod]
      have hpow : (L / 2) ^ N = ∏ _k : Fin N, (L / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [eval_sub, eval_X, eval_C, x]; ring
    have hc := intervalIntegral.integral_comp_mul_add (fun t => (pMon.eval t) ^ 2)
      (show L / 2 ≠ 0 by positivity) (L / 2) (a := (-1 : ℝ)) (b := 1)
    have ha : L / 2 * (-1) + L / 2 = 0 := by ring
    have hb : L / 2 * 1 + L / 2 = L := by ring
    rw [ha, hb] at hc
    have hfac := eq_leadingCoeff_mul_prod_of_roots (legendreScaled_natDegree N) hr_mono hr_root
    rw [legendreScaled_leadingCoeff] at hfac
    have hsq_leg := integral_monicLegendre_sq hfac
    have hint_s : ∫ s in (-1 : ℝ)..1, (pMon.eval (L / 2 * s + L / 2)) ^ 2 =
        (L / 2) ^ (2 * N) * ∫ s in (-1 : ℝ)..1, (∏ k : Fin N, (s - r k)) ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      have h1 : L / 2 * s + L / 2 = L / 2 * (s + 1) := by ring
      rw [h1, haff s, mul_pow, ← pow_mul, mul_comm N 2]
    calc ∫ t in (0 : ℝ)..L, (pMon.eval t) ^ 2
        = (L / 2) * ∫ s in (-1 : ℝ)..1, (pMon.eval (L / 2 * s + L / 2)) ^ 2 := by
            rw [smul_eq_mul] at hc
            rw [hc]; field_simp
      _ = (L / 2) ^ (2 * N + 1) * ∫ s in (-1 : ℝ)..1, (∏ k : Fin N, (s - r k)) ^ 2 := by
            rw [hint_s, pow_succ']; ring
      _ = (L / 2) ^ (2 * N + 1) *
            (2 ^ (2 * N + 1) * (N.factorial : ℝ) ^ 4 /
              ((2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 2)) := by rw [hsq_leg]
      _ = L ^ (2 * N + 1) * (N.factorial : ℝ) ^ 4 /
            ((2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 2) := by
            rw [div_pow]; field_simp
  have hdiff : (∫ t in (0 : ℝ)..L, g t) - ∑ k : Fin N, w k * g (x k) =
      ∫ t in (0 : ℝ)..L, (g t - H.eval t) := by
    rw [← hH_int, intervalIntegral.integral_sub
      (hg.continuous.intervalIntegrable _ _) ((poly_continuous H).intervalIntegrable _ _)]
  rw [hdiff]
  calc |∫ t in (0 : ℝ)..L, (g t - H.eval t)|
      ≤ ∫ t in (0 : ℝ)..L, |g t - H.eval t| :=
        intervalIntegral.abs_integral_le_integral_abs hL.le
    _ ≤ ∫ t in (0 : ℝ)..L, M / ((2 * N).factorial : ℝ) * (pMon.eval t) ^ 2 := by
        refine intervalIntegral.integral_mono_on hL.le
          ((hg.continuous.sub (poly_continuous H)).abs.intervalIntegrable _ _)
          ((continuous_const.mul ((poly_continuous pMon).pow 2)).intervalIntegrable _ _)
          hpt
    _ = M / ((2 * N).factorial : ℝ) * ∫ t in (0 : ℝ)..L, (pMon.eval t) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ = M * L ^ (2 * N + 1) * (N.factorial : ℝ) ^ 4 /
          ((2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 3) := by
        rw [hp_int]
        have hnz : ((2 * N).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        field_simp

/-- Tensor-product quadrature error bound on an anisotropic box `∏ i : Fin n, (0, L i]`. -/
theorem abs_boxIntegral_sub_tensorQuad_le {N : ℕ} :
    ∀ {n : ℕ} (L : Fin n → ℝ) (_hL : ∀ i, 0 < L i)
      (x : (i : Fin n) → Fin N → ℝ) (w : (i : Fin n) → Fin N → ℝ)
      (_hx : ∀ i k, x i k ∈ Set.Icc (0 : ℝ) (L i))
      (_hw_nn : ∀ i k, 0 ≤ w i k)
      (_hw_sum : ∀ i, ∑ k : Fin N, w i k = L i)
      (f : (Fin n → ℝ) → ℝ) (_hf : Continuous f)
      (E : Fin n → ℝ)
      (_hE : ∀ i : Fin n, ∀ y : Fin n → ℝ,
        (∀ j, y j ∈ Set.Icc (0 : ℝ) (L j)) →
          |(∫ t in (0 : ℝ)..L i, f (Function.update y i t)) -
            ∑ k : Fin N, w i k * f (Function.update y i (x i k))| ≤ E i),
      |(∫ y in Set.pi Set.univ (fun i => Set.Ioc (0 : ℝ) (L i)), f y
          ∂(Measure.pi fun _ : Fin n => volume)) -
        ∑ a : Fin n → Fin N, (∏ i : Fin n, w i (a i)) * f (fun i => x i (a i))| ≤
      ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, L j) * E i := by
  intro n
  induction n with
  | zero =>
      intro L _ x w _ _ _ f _ E _
      have huniv : Set.pi Set.univ (fun i : Fin 0 => Set.Ioc (0 : ℝ) (L i)) = Set.univ := by
        ext y; simp
      rw [huniv, Measure.restrict_univ]
      have h0 : ∫ y : Fin 0 → ℝ, f y ∂(Measure.pi fun _ : Fin 0 => volume) = f Fin.elim0 := by
        have h1 : (Measure.pi fun _ : Fin 0 => (volume : Measure ℝ)) Set.univ = 1 := by
          have hu : (Set.univ : Set (Fin 0 → ℝ)) = Set.pi Set.univ fun _ => Set.univ := by
            ext y; simp
          rw [hu, Measure.pi_pi]
          simp
        have hcn : (fun y : Fin 0 → ℝ => f y) = fun _ => f Fin.elim0 :=
          funext fun y => congrArg f (Subsingleton.elim _ _)
        rw [hcn, integral_const, Measure.real, h1, ENNReal.toReal_one, one_smul]
      have hsum : ∑ a : Fin 0 → Fin N,
          (∏ i : Fin 0, w i (a i)) * f (fun i => x i (a i)) = f Fin.elim0 := by
        have hcn : ∀ a : Fin 0 → Fin N,
            (∏ i : Fin 0, w i (a i)) * f (fun i => x i (a i)) = f Fin.elim0 := fun a => by
          rw [Fin.prod_univ_zero, one_mul]; exact congrArg f (Subsingleton.elim _ _)
        rw [Finset.sum_congr rfl fun a _ => hcn a, Finset.sum_const, Finset.card_univ,
          Fintype.card_unique, one_nsmul]
      rw [h0, hsum, sub_self, abs_zero, Fin.sum_univ_zero]
  | succ m ih =>
      intro L hL x w hx hw_nn hw_sum f hf E hE
      let L' : Fin m → ℝ := fun i => L i.succ
      let x' : (i : Fin m) → Fin N → ℝ := fun i => x i.succ
      let w' : (i : Fin m) → Fin N → ℝ := fun i => w i.succ
      let E' : Fin m → ℝ := fun i => E i.succ
      let B0 : Set (Fin (m + 1) → ℝ) := Set.pi Set.univ fun i => Set.Ioc (0 : ℝ) (L i)
      let B' : Set (Fin m → ℝ) := Set.pi Set.univ fun i => Set.Ioc (0 : ℝ) (L' i)
      let μm : Measure (Fin m → ℝ) := Measure.pi fun _ : Fin m => volume
      let μ : Measure (Fin (m + 1) → ℝ) := Measure.pi fun _ : Fin (m + 1) => volume
      let I_tail (t : ℝ) : ℝ := ∫ y in B', f (Fin.cons t y) ∂μm
      let Q_tail (t : ℝ) : ℝ :=
        ∑ b : Fin m → Fin N, (∏ i : Fin m, w' i (b i)) * f (Fin.cons t (fun i => x' i (b i)))
      -- First: split `∫ in B0` by Fubini along coordinate `0`
      have hsplit_int : ∫ z in B0, f z ∂μ = ∫ t in (0 : ℝ)..L 0, I_tail t := by
        let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        have hmp : MeasurePreserving split μ (volume.prod μm) :=
          MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
        have hB0_compact : IsCompact (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (L i)) :=
          isCompact_univ_pi fun _ => isCompact_Icc
        have hIoc_fin : μ B0 < ⊤ := by
          simp only [B0, μ, Measure.pi_pi, Real.volume_Ioc]
          exact ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top
        have hB_prod : split ⁻¹' (Set.Ioc (0 : ℝ) (L 0) ×ˢ B') = B0 := by
          ext z; simp only [Set.mem_preimage, Set.mem_prod, B0, B', L', Set.mem_pi, Set.mem_univ,
            forall_true_left, split]
          constructor
          · rintro ⟨h0, ht⟩ i
            refine Fin.cases h0 (fun j => ht j) i
          · intro h; exact ⟨h 0, fun j => h j.succ⟩
        have hset := hmp.setIntegral_preimage_emb split.measurableEmbedding
          (fun p : ℝ × (Fin m → ℝ) => f (Fin.cons p.1 p.2))
          (Set.Ioc (0 : ℝ) (L 0) ×ˢ B')
        have hcons : ∀ z : Fin (m + 1) → ℝ,
            f (Fin.cons (split z).1 (split z).2) = f z := fun z => by
          congr 1; ext i; refine Fin.cases rfl (fun j => rfl) i
        have hprod_int : IntegrableOn (fun p : ℝ × (Fin m → ℝ) => f (Fin.cons p.1 p.2))
            (Set.Ioc (0 : ℝ) (L 0) ×ˢ B') (volume.prod μm) := by
          have hfin : IsCompact (Set.Icc (0 : ℝ) (L 0) ×ˢ
              Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (L' i)) :=
            isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
          have hcont_cons : Continuous fun p : ℝ × (Fin m → ℝ) => f (Fin.cons p.1 p.2) :=
            hf.comp (continuous_pi fun i => by
              refine Fin.cases continuous_fst (fun j => (continuous_apply j).comp continuous_snd) i)
          exact (hcont_cons.continuousOn.integrableOn_compact hfin).mono_set
            (Set.prod_mono Set.Ioc_subset_Icc_self fun y hy j _ =>
              Set.Ioc_subset_Icc_self (hy j (Set.mem_univ j)))
        rw [hB_prod] at hset
        have heq1 : ∫ z in B0, f z ∂μ =
            ∫ p in Set.Ioc (0 : ℝ) (L 0) ×ˢ B', f (Fin.cons p.1 p.2) ∂(volume.prod μm) := by
          rw [← hset]
          refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
            fun z _ => (hcons z).symm
        have hpi : Integrable (fun p : ℝ × (Fin m → ℝ) => f (Fin.cons p.1 p.2))
            ((volume.restrict (Set.Ioc (0 : ℝ) (L 0))).prod (μm.restrict B')) := by
          rw [Measure.prod_restrict]
          exact hprod_int
        rw [heq1, ← Measure.prod_restrict, integral_prod _ hpi,
          intervalIntegral.integral_of_le (hL 0).le]
      -- Split `∑ a : Fin (m + 1) → Fin N` into `(a 0, a ∘ Fin.succ)`
      have hsplit_sum : ∑ a : Fin (m + 1) → Fin N,
          (∏ i : Fin (m + 1), w i (a i)) * f (fun i => x i (a i)) =
          ∑ k : Fin N, w 0 k * Q_tail (x 0 k) := by
        let e : (Fin N × (Fin m → Fin N)) ≃ (Fin (m + 1) → Fin N) :=
          { toFun := fun p => Fin.cons p.1 p.2
            invFun := fun a => (a 0, fun j => a j.succ)
            left_inv := fun ⟨k, b⟩ => by
              ext
              · simp
              · simp [Fin.cons]
            right_inv := fun a => by
              ext i; refine Fin.cases rfl (fun j => rfl) i }
        rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hp : ∏ i : Fin (m + 1), w i (e (k, b) i) =
            w 0 k * ∏ j : Fin m, w' j (b j) := by
          rw [Fin.prod_univ_succ]; rfl
        have hfn : (fun i => x i (e (k, b) i)) =
            Fin.cons (x 0 k) (fun j => x' j (b j)) := by
          ext i; refine Fin.cases rfl (fun j => rfl) i
        rw [hp, hfn, mul_assoc]
      -- Bound `|I_tail t - Q_tail t|` via induction hypothesis `ih` for `t ∈ [0, L 0]`
      have hIH_pt : ∀ t ∈ Set.Icc (0 : ℝ) (L 0), |I_tail t - Q_tail t| ≤
          ∑ i : Fin m, (∏ j ∈ Finset.univ.erase i, L' j) * E' i := by
        intro t ht
        refine ih L' (fun i => hL i.succ) x' w' (fun i k => hx i.succ k)
          (fun i k => hw_nn i.succ k) (fun i => hw_sum i.succ)
          (fun y => f (Fin.cons t y))
          (hf.comp (continuous_pi fun i =>
            Fin.cases continuous_const (fun j => continuous_apply j) i))
          E' fun i y hy => ?_
        have hupd : ∀ s : ℝ, Fin.cons t (Function.update y i s) =
            Function.update (Fin.cons t y : Fin (m + 1) → ℝ) i.succ s := by
          intro s; ext r
          refine Fin.cases ?_ (fun j => ?_) r
          · rw [Fin.cons_zero, Function.update_of_ne (Fin.succ_ne_zero i).symm, Fin.cons_zero]
          · by_cases hji : j = i
            · subst hji; rw [Fin.cons_succ, Function.update_self, Function.update_self]
            · rw [Fin.cons_succ, Function.update_of_ne hji,
                Function.update_of_ne ((Fin.succ_injective _).ne hji), Fin.cons_succ]
        simp_rw [hupd]
        exact hE i.succ (Fin.cons t y) (fun r => Fin.cases ht hy r)
      -- Compare `I_tail - Q_tail` via `∫_0^{L 0} Q_tail t dt`
      have hI_cont : Continuous I_tail := by
        have hcomp : IsCompact (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (L' i)) :=
          isCompact_univ_pi fun _ => isCompact_Icc
        have hbd : ∀ t0 : ℝ, ContinuousAt I_tail t0 := fun t0 => by
          have hfin : μm B' < ⊤ := by
            simp only [B', μm, Measure.pi_pi, Real.volume_Ioc]
            exact ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top
          have ⟨M, hM⟩ : ∃ M : ℝ, ∀ t ∈ Set.Icc (t0 - 1) (t0 + 1),
              ∀ y ∈ Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (L' i),
                ‖f (Fin.cons t y)‖ ≤ M := by
            have hk : IsCompact (Set.Icc (t0 - 1) (t0 + 1) ×ˢ
                Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (L' i)) :=
              isCompact_Icc.prod hcomp
            have hcf : Continuous fun p : ℝ × (Fin m → ℝ) => ‖f (Fin.cons p.1 p.2)‖ :=
              (hf.comp (continuous_pi fun i =>
                Fin.cases continuous_fst
                  (fun j => (continuous_apply j).comp continuous_snd) i)).norm
            rcases hk.bddAbove_image hcf.continuousOn with ⟨M, hM⟩
            exact ⟨M, fun t ht y hy => hM ⟨(t, y), ⟨ht, hy⟩, rfl⟩⟩
          exact continuousAt_of_dominated (μ := μm.restrict B')
            (bound := fun _ => M)
            (Filter.Eventually.of_forall fun t =>
              (hf.comp (continuous_pi fun i =>
                Fin.cases continuous_const (fun j => continuous_apply j) i)).aestronglyMeasurable)
            (Filter.eventually_of_mem (Icc_mem_nhds (by linarith) (by linarith)) fun t ht =>
              (ae_restrict_iff' (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)).mpr
                (ae_of_all _ fun y hy => hM t ht y fun i _ =>
                  Set.Ioc_subset_Icc_self (hy i (Set.mem_univ i))))
            (integrableOn_const (hs := hfin.ne))
            (ae_of_all _ fun y =>
              (hf.comp (continuous_pi fun i =>
                Fin.cases continuous_id (fun j => continuous_const) i)).continuousAt)
        exact continuous_iff_continuousAt.mpr hbd
      have hQ_cont : Continuous Q_tail := by
        refine continuous_sum_real _ _ fun b _ => continuous_const.mul ?_
        exact hf.comp (continuous_pi fun i =>
          Fin.cases continuous_id (fun _ => continuous_const) i)
      have h1 : |(∫ t in (0 : ℝ)..L 0, I_tail t) - (∫ t in (0 : ℝ)..L 0, Q_tail t)| ≤
          L 0 * ∑ i : Fin m, (∏ j ∈ Finset.univ.erase i, L' j) * E' i := by
        rw [← intervalIntegral.integral_sub (hI_cont.intervalIntegrable _ _)
          (hQ_cont.intervalIntegrable _ _)]
        calc |∫ t in (0 : ℝ)..L 0, (I_tail t - Q_tail t)|
            ≤ ∫ t in (0 : ℝ)..L 0, |I_tail t - Q_tail t| :=
              intervalIntegral.abs_integral_le_integral_abs (hL 0).le
          _ ≤ ∫ _t in (0 : ℝ)..L 0, ∑ i : Fin m, (∏ j ∈ Finset.univ.erase i, L' j) * E' i :=
              intervalIntegral.integral_mono_on (hL 0).le
                ((hI_cont.sub hQ_cont).abs.intervalIntegrable _ _)
                (continuous_const.intervalIntegrable _ _) hIH_pt
          _ = L 0 * ∑ i : Fin m, (∏ j ∈ Finset.univ.erase i, L' j) * E' i := by
              simp [sub_zero, smul_eq_mul]
      have hsum_w' : ∑ b : Fin m → Fin N, ∏ i : Fin m, w' i (b i) = ∏ i : Fin m, L' i := by
        rw [← Fintype.prod_sum (fun i k => w' i k)]
        refine Finset.prod_congr rfl fun i _ => hw_sum i.succ
      have h2 : |(∫ t in (0 : ℝ)..L 0, Q_tail t) - ∑ k : Fin N, w 0 k * Q_tail (x 0 k)| ≤
          (∏ i : Fin m, L' i) * E 0 := by
        have hswap_int : ∫ t in (0 : ℝ)..L 0, Q_tail t =
            ∑ b : Fin m → Fin N, (∏ i : Fin m, w' i (b i)) *
              ∫ t in (0 : ℝ)..L 0, f (Fin.cons t (fun i => x' i (b i))) := by
          have hcont_b : ∀ b : Fin m → Fin N,
              Continuous fun t : ℝ => (∏ i : Fin m, w' i (b i)) *
                f (Fin.cons t (fun i => x' i (b i))) := fun b =>
            continuous_const.mul (hf.comp (continuous_pi fun i =>
              Fin.cases continuous_id (fun j => continuous_const) i))
          unfold Q_tail
          rw [intervalIntegral_sum_eq Finset.univ
            (fun b t => (∏ i : Fin m, w' i (b i)) * f (Fin.cons t (fun i => x' i (b i))))
            (fun b _ => (hcont_b b).intervalIntegrable _ _)]
          refine Finset.sum_congr rfl fun b _ => intervalIntegral.integral_const_mul _ _
        have hswap_sum : ∑ k : Fin N, w 0 k * Q_tail (x 0 k) =
            ∑ b : Fin m → Fin N, (∏ i : Fin m, w' i (b i)) *
              ∑ k : Fin N, w 0 k * f (Fin.cons (x 0 k) (fun i => x' i (b i))) := by
          simp_rw [Q_tail, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [hswap_int, hswap_sum, ← Finset.sum_sub_distrib]
        calc |∑ b : Fin m → Fin N, ((∏ i : Fin m, w' i (b i)) *
                (∫ t in (0 : ℝ)..L 0, f (Fin.cons t (fun i => x' i (b i)))) -
                (∏ i : Fin m, w' i (b i)) *
                  ∑ k : Fin N, w 0 k * f (Fin.cons (x 0 k) (fun i => x' i (b i))))|
            ≤ ∑ b : Fin m → Fin N, |(∏ i : Fin m, w' i (b i)) *
                ((∫ t in (0 : ℝ)..L 0, f (Fin.cons t (fun i => x' i (b i)))) -
                  ∑ k : Fin N, w 0 k * f (Fin.cons (x 0 k) (fun i => x' i (b i))))| := by
                refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
                refine Finset.sum_congr rfl fun b _ => by rw [← mul_sub]
          _ ≤ ∑ b : Fin m → Fin N, (∏ i : Fin m, w' i (b i)) * E 0 := by
                refine Finset.sum_le_sum fun b _ => ?_
                have hwn : 0 ≤ ∏ i : Fin m, w' i (b i) :=
                  Finset.prod_nonneg fun i _ => hw_nn i.succ (b i)
                rw [abs_mul, abs_of_nonneg hwn]
                refine mul_le_mul_of_nonneg_left ?_ hwn
                have hupd0 : ∀ s : ℝ, Fin.cons s (fun i => x' i (b i)) =
                    Function.update (Fin.cons (0 : ℝ) (fun i => x' i (b i)) : Fin (m + 1) → ℝ)
                      (0 : Fin (m + 1)) s :=
                  fun s => by
                    ext r
                    refine Fin.cases ?_ ?_ r
                    · rw [Fin.cons_zero, Function.update_self]
                    · intro j
                      rw [Fin.cons_succ, Function.update_of_ne (Fin.succ_ne_zero j), Fin.cons_succ]
                have hi_eq : ∫ t in (0 : ℝ)..L 0, f (Fin.cons t (fun i => x' i (b i))) =
                    ∫ t in (0 : ℝ)..L 0, f (Function.update
                      (Fin.cons (0 : ℝ) (fun i => x' i (b i)) : Fin (m + 1) → ℝ)
                      (0 : Fin (m + 1)) t) :=
                  intervalIntegral.integral_congr fun t _ => by rw [hupd0 t]
                have hs_eq : ∑ k : Fin N, w 0 k * f (Fin.cons (x 0 k) (fun i => x' i (b i))) =
                    ∑ k : Fin N, w 0 k * f (Function.update
                      (Fin.cons (0 : ℝ) (fun i => x' i (b i)) : Fin (m + 1) → ℝ)
                      (0 : Fin (m + 1)) (x 0 k)) :=
                  Finset.sum_congr rfl fun k _ => by rw [hupd0 (x 0 k)]
                rw [hi_eq, hs_eq]
                exact hE 0 (Fin.cons (0 : ℝ) (fun i => x' i (b i)))
                  (fun r => Fin.cases ⟨le_rfl, (hL 0).le⟩ (fun j => hx j.succ (b j)) r)
          _ = (∏ i : Fin m, L' i) * E 0 := by rw [← Finset.sum_mul, hsum_w']
      rw [hsplit_int, hsplit_sum]
      calc |(∫ t in (0 : ℝ)..L 0, I_tail t) - ∑ k : Fin N, w 0 k * Q_tail (x 0 k)|
          ≤ |(∫ t in (0 : ℝ)..L 0, I_tail t) - ∫ t in (0 : ℝ)..L 0, Q_tail t| +
              |(∫ t in (0 : ℝ)..L 0, Q_tail t) - ∑ k : Fin N, w 0 k * Q_tail (x 0 k)| :=
            abs_sub_le _ _ _
        _ ≤ L 0 * (∑ i : Fin m, (∏ j ∈ Finset.univ.erase i, L' j) * E' i) +
              (∏ i : Fin m, L' i) * E 0 := add_le_add h1 h2
        _ = ∑ i : Fin (m + 1), (∏ j ∈ Finset.univ.erase i, L j) * E i := by
            rw [Fin.sum_univ_succ, add_comm, Finset.mul_sum]
            congr 1
            · have hprod_fin : ∏ i : Fin m, L' i = ∏ j ∈ Finset.univ.erase 0, L j := by
                refine Finset.prod_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_
                · intro j _; exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero j, Finset.mem_univ _⟩
                · intro a _ b _ h; exact Fin.succ_injective _ h
                · intro b hb
                  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Finset.mem_erase.mp hb).1
                  exact ⟨j, Finset.mem_univ j, rfl⟩
                · intro j _; rfl
              rw [hprod_fin]
            · refine Finset.sum_congr rfl fun i _ => ?_
              have hprod_eq : L 0 * ∏ j ∈ Finset.univ.erase i, L' j =
                  ∏ j ∈ Finset.univ.erase i.succ, L j := by
                have hne : (0 : Fin (m + 1)) ∈ Finset.univ.erase i.succ :=
                  Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero i).symm, Finset.mem_univ _⟩
                rw [← Finset.mul_prod_erase _ _ hne]
                congr 1
                refine Finset.prod_bij (fun j _ => j.succ) ?_ ?_ ?_ ?_
                · intro j hj; exact Finset.mem_erase.mpr
                    ⟨Fin.succ_ne_zero j, Finset.mem_erase.mpr
                      ⟨Fin.succ_injective _ |>.ne (Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩⟩
                · intro j1 _ j2 _ h; exact Fin.succ_injective _ h
                · intro b hb
                  have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
                  have hbi : b ≠ i.succ := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
                  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hb0
                  exact ⟨j, Finset.mem_erase.mpr ⟨fun h => hbi (congrArg Fin.succ h),
                    Finset.mem_univ _⟩, rfl⟩
                · intro j _; rfl
              rw [← mul_assoc, hprod_eq]

end GaussLegendre

/-! ### Anisotropic AR(2) quadrature error and factored Markov recurrence -/

section AR2QuadRecurrence

/-- Explicit upper bound on `|ar2BoxIntegral L_end L_int j - ar2TensorQuad L_end L_int r j|`
using the `N`-point shifted Gauss–Legendre rule and the diagonal precision bounds `≤ 12`
at endpoints and `≤ 39` in the interior. -/
noncomputable def ar2QuadErr (N : ℕ) (L_end L_int : ℝ) (j : ℕ) : ℝ :=
  (3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ (j - 1) *
    L_end ^ 2 * L_int ^ (j - 1) *
    ((N.factorial : ℝ) ^ 3 /
      (2 ^ N * (2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 2)) *
    (2 * (12 * L_end ^ 2) ^ N + ((j - 1 : ℕ) : ℝ) * (39 * L_int ^ 2) ^ N)

/-- Nonnegativity of `ar2QuadErr`. -/
theorem ar2QuadErr_nonneg (N : ℕ) {L_end L_int : ℝ} (_hLe : 0 ≤ L_end) (hLi : 0 ≤ L_int)
    (j : ℕ) : 0 ≤ ar2QuadErr N L_end L_int j := by
  unfold ar2QuadErr
  positivity

/-- Tensor-product Gauss–Legendre quadrature sum for `ar2JointDensity j` over the anisotropic
box `ar2Box L_end L_int j`. -/
noncomputable def ar2TensorQuad {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ a : Fin (j + 1) → Fin N,
    (∏ i : Fin (j + 1), ar2BoxBound L_end L_int j i / 2 * gaussWeight r (a i)) *
      ar2JointDensity j (fun i => ar2BoxBound L_end L_int j i / 2 * (r (a i) + 1))

/-- Anisotropic Gauss–Legendre quadrature error bound for `ar2BoxIntegral L_end L_int j`
(`j ≥ 1`). -/
theorem abs_ar2BoxIntegral_sub_tensorQuad_le {N : ℕ} (hN : 0 < N)
    {L_end L_int : ℝ} (hLe : 0 < L_end) (hLi : 0 < L_int)
    {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_range : ∀ k : Fin N, r k ∈ Set.Ioo (-1 : ℝ) 1)
    (hr_root : ∀ k : Fin N, (legendreScaled N).eval (r k) = 0)
    {j : ℕ} (hj : 1 ≤ j) :
    |ar2BoxIntegral L_end L_int j - ar2TensorQuad L_end L_int r j| ≤
      ar2QuadErr N L_end L_int j := by
  cases j with
  | zero => omega
  | succ k =>
      let L : Fin (k + 2) → ℝ := fun i => ar2BoxBound L_end L_int (k + 1) i
      have hL_pos : ∀ i : Fin (k + 2), 0 < L i := fun i => by
        dsimp only [L, ar2BoxBound]; split_ifs <;> assumption
      let x : (i : Fin (k + 2)) → Fin N → ℝ := fun i m => L i / 2 * (r m + 1)
      let w : (i : Fin (k + 2)) → Fin N → ℝ := fun i m => L i / 2 * gaussWeight r m
      have hx_mem : ∀ i m, x i m ∈ Set.Icc (0 : ℝ) (L i) := fun i m => by
        have ⟨h1, h2⟩ := hr_range m
        dsimp only [x]
        exact ⟨by nlinarith [hL_pos i], by nlinarith [hL_pos i]⟩
      have hw_nn : ∀ i m, 0 ≤ w i m := fun i m =>
        mul_nonneg (div_nonneg (hL_pos i).le (by norm_num))
          (gaussWeight_pos hN hr_mono hr_root m).le
      have hw_sum : ∀ i, ∑ m : Fin N, w i m = L i := fun i => by
        dsimp only [w]
        rw [← Finset.mul_sum, sum_gaussWeight hN hr_mono hr_root]
        ring
      let Cj : ℝ := (3 / (2 * Real.pi)) * (Real.sqrt (6 / Real.pi)) ^ k
      have hCj_nn : 0 ≤ Cj := by dsimp only [Cj]; positivity
      let comb : ℝ := (N.factorial : ℝ) ^ 3 /
        (2 ^ N * (2 * N + 1 : ℝ) * ((2 * N).factorial : ℝ) ^ 2)
      let E : Fin (k + 2) → ℝ := fun i =>
        Cj * (ar2QuadDiag (k + 1) i) ^ N * (L i) ^ (2 * N + 1) * comb
      have hE : ∀ i : Fin (k + 2), ∀ y : Fin (k + 2) → ℝ,
          (∀ m, y m ∈ Set.Icc (0 : ℝ) (L m)) →
          |(∫ t in (0 : ℝ)..L i, ar2JointDensity (k + 1) (Function.update y i t)) -
            ∑ m : Fin N, w i m * ar2JointDensity (k + 1) (Function.update y i (x i m))| ≤
            E i := by
        intro i y _
        let M : ℝ := Cj * (ar2QuadDiag (k + 1) i) ^ N * ((2 * N).factorial : ℝ) /
          (2 ^ N * (N.factorial : ℝ))
        have hM_nn : 0 ≤ M := by
          dsimp only [M]
          have := ar2QuadDiag_pos (k + 1) i
          positivity
        have h1 := abs_integral_sub_gaussQuad_le hN (hL_pos i) hr_mono hr_range hr_root
          (g := fun t => ar2JointDensity (k + 1) (Function.update y i t))
          (ar2JointDensity_slice_contDiff k y i (2 * N)) hM_nn
          (fun t _ => abs_iteratedDeriv_ar2JointDensity_le k y i N t)
        refine h1.trans_eq ?_
        have hNfac : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)
        have h2Nfac : ((2 * N).factorial : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * N))
        have h2p : (2 : ℝ) ^ N ≠ 0 := by positivity
        have h2N1 : (2 * N + 1 : ℝ) ≠ 0 := by positivity
        dsimp only [E, M, comb]
        field_simp
      have hmain := abs_boxIntegral_sub_tensorQuad_le L hL_pos x w hx_mem hw_nn hw_sum
        (ar2JointDensity (k + 1)) (ar2JointDensity_continuous (k + 1)) E hE
      have hprod_L : ∏ i : Fin (k + 2), L i = L_end ^ 2 * L_int ^ k := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
        have h0 : L 0 = L_end := by simp [L, ar2BoxBound]
        have hl : L (Fin.last k).succ = L_end := by simp [L, ar2BoxBound]
        have hmid : ∏ i : Fin k, L i.castSucc.succ = L_int ^ k := by
          have hitem : ∀ i : Fin k, L i.castSucc.succ = L_int := fun i => by
            dsimp only [L, ar2BoxBound]
            have h1 : i.castSucc.succ.1 ≠ 0 := by simp
            have h2 : i.castSucc.succ.1 ≠ k + 1 := by change i.1 + 1 ≠ k + 1; omega
            exact ite_eq_right_iff.mpr fun h => by rcases h with h | h <;> contradiction
          rw [Finset.prod_congr rfl fun i _ => hitem i, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
        rw [h0, hl, hmid]; ring
      refine hmain.trans ?_
      have hterm_eq : ∀ i : Fin (k + 2),
          (∏ m ∈ Finset.univ.erase i, L m) * E i =
            Cj * (L_end ^ 2 * L_int ^ k) * comb *
              (ar2QuadDiag (k + 1) i * L i ^ 2) ^ N := fun i => by
        have hmul : (∏ m ∈ Finset.univ.erase i, L m) * L i = L_end ^ 2 * L_int ^ k := by
          rw [mul_comm, Finset.mul_prod_erase Finset.univ L (Finset.mem_univ i), hprod_L]
        dsimp only [E]
        calc (∏ m ∈ Finset.univ.erase i, L m) *
              (Cj * ar2QuadDiag (k + 1) i ^ N * L i ^ (2 * N + 1) * comb)
            = Cj * ((∏ m ∈ Finset.univ.erase i, L m) * L i) * comb *
                (ar2QuadDiag (k + 1) i ^ N * (L i ^ 2) ^ N) := by
                rw [pow_succ, pow_mul]; ring
          _ = Cj * (L_end ^ 2 * L_int ^ k) * comb *
                (ar2QuadDiag (k + 1) i * L i ^ 2) ^ N := by
                rw [hmul, mul_pow]
      rw [Finset.sum_congr rfl fun i _ => hterm_eq i, ← Finset.mul_sum]
      have hdiag_sum : ∑ i : Fin (k + 2), (ar2QuadDiag (k + 1) i * L i ^ 2) ^ N ≤
          2 * (12 * L_end ^ 2) ^ N + (k : ℝ) * (39 * L_int ^ 2) ^ N := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        have h0_le : (ar2QuadDiag (k + 1) 0 * L 0 ^ 2) ^ N ≤ (12 * L_end ^ 2) ^ N := by
          have hL0 : L 0 = L_end := by simp [L, ar2BoxBound]
          rw [hL0]
          gcongr
          · have := ar2QuadDiag_pos (k + 1) 0; positivity
          · exact ar2QuadDiag_zero_le (k + 1)
        have hl_le : (ar2QuadDiag (k + 1) (Fin.last k).succ * L (Fin.last k).succ ^ 2) ^ N ≤
            (12 * L_end ^ 2) ^ N := by
          have hLl : L (Fin.last k).succ = L_end := by simp [L, ar2BoxBound]
          rw [hLl]
          have hlast : (Fin.last k).succ = Fin.last (k + 1) := by ext; simp
          rw [hlast]
          gcongr
          · have := ar2QuadDiag_pos (k + 1) (Fin.last (k + 1)); positivity
          · exact ar2QuadDiag_last_le (k + 1)
        have hmid_le : ∑ i : Fin k,
            (ar2QuadDiag (k + 1) i.castSucc.succ * L i.castSucc.succ ^ 2) ^ N ≤
            (k : ℝ) * (39 * L_int ^ 2) ^ N := by
          calc ∑ i : Fin k, (ar2QuadDiag (k + 1) i.castSucc.succ * L i.castSucc.succ ^ 2) ^ N
              ≤ ∑ _i : Fin k, (39 * L_int ^ 2) ^ N := by
                refine Finset.sum_le_sum fun i _ => ?_
                have hLi_eq : L i.castSucc.succ = L_int := by
                  dsimp only [L, ar2BoxBound]
                  have h1 : i.castSucc.succ.1 ≠ 0 := by simp
                  have h2 : i.castSucc.succ.1 ≠ k + 1 := by change i.1 + 1 ≠ k + 1; omega
                  exact ite_eq_right_iff.mpr fun h => by rcases h with h | h <;> contradiction
                rw [hLi_eq]
                gcongr
                · have := ar2QuadDiag_pos (k + 1) i.castSucc.succ; positivity
                · exact ar2QuadDiag_le (k + 1) i.castSucc.succ
            _ = (k : ℝ) * (39 * L_int ^ 2) ^ N := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        linarith
      have hfac_nn : 0 ≤ Cj * (L_end ^ 2 * L_int ^ k) * comb := by
        dsimp only [Cj, comb]; positivity
      have hmul := mul_le_mul_of_nonneg_left hdiag_sum hfac_nn
      refine hmul.trans_eq ?_
      unfold ar2QuadErr
      simp only [Nat.add_sub_cancel]
      dsimp only [Cj, comb]
      ring

/-- Upper bound reduction for `alternatingWaveSum J`: given quadrature brackets
`qLo j ≤ 2^(j-1) * ar2TensorQuad L_end L_int r j ≤ qHi j` for `j ∈ Finset.Icc 1 J`, even-index
tail truncation errors are dropped (they contribute nonpositively) while odd-index terms add both
quadrature and tail error bounds. -/
theorem alternatingWaveSum_le_of_quad {N : ℕ} (hN : 0 < N)
    {L_end L_int : ℝ} (hLe : 0 < L_end) (hLi : 0 < L_int)
    {r : Fin N → ℝ} (hr_mono : StrictMono r)
    (hr_range : ∀ k : Fin N, r k ∈ Set.Ioo (-1 : ℝ) 1)
    (hr_root : ∀ k : Fin N, (legendreScaled N).eval (r k) = 0)
    (J : ℕ) (qLo qHi : ℕ → ℝ)
    (hlo : ∀ j ∈ Finset.Icc 1 J, Even j →
      qLo j ≤ (2 : ℝ) ^ (j - 1) * ar2TensorQuad L_end L_int r j)
    (hhi : ∀ j ∈ Finset.Icc 1 J, Odd j →
      (2 : ℝ) ^ (j - 1) * ar2TensorQuad L_end L_int r j ≤ qHi j) :
    alternatingWaveSum J ≤
      ∑ j ∈ Finset.Icc 1 J,
        (if Odd j then 3 * qHi j + 3 * (2 : ℝ) ^ (j - 1) * ar2QuadErr N L_end L_int j +
            3 * (2 : ℝ) ^ (j - 1) * ar2TailBound L_end L_int j
         else -(3 * qLo j) + 3 * (2 : ℝ) ^ (j - 1) * ar2QuadErr N L_end L_int j) := by
  unfold alternatingWaveSum altPathProb
  refine Finset.sum_le_sum fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hq := abs_le.mp (abs_ar2BoxIntegral_sub_tensorQuad_le hN hLe hLi
    hr_mono hr_range hr_root hj1)
  have h2_nn : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ (j - 1) := by positivity
  rcases Nat.even_or_odd j with he | ho
  · have hno : ¬ Odd j := Nat.not_odd_iff_even.mpr he
    have hpow : (-1 : ℝ) ^ (j + 1) = -1 := (he.add_one).neg_one_pow
    rw [hpow, ite_eq_right_iff.mpr fun h => (hno h).elim]
    have hbox_le : ar2BoxIntegral L_end L_int j ≤ ar2OrthantIntegral j :=
      ar2BoxIntegral_le_orthant L_end L_int j
    have hq_lo : ar2TensorQuad L_end L_int r j - ar2QuadErr N L_end L_int j ≤
        ar2BoxIntegral L_end L_int j := by linarith [hq.1]
    have hlow := hlo j hj he
    have hmul := mul_le_mul_of_nonneg_left (hq_lo.trans hbox_le) h2_nn
    have hterm : -1 * (3 / 2 : ℝ) * (2 : ℝ) ^ (j - 1) * (2 * ar2OrthantIntegral j) =
        -(3 * (2 : ℝ) ^ (j - 1) * ar2OrthantIntegral j) := by ring
    linarith
  · have hpow : (-1 : ℝ) ^ (j + 1) = 1 := (ho.add_one).neg_one_pow
    rw [hpow, ite_eq_left_iff.mpr fun h => (h ho).elim]
    have htail : ar2OrthantIntegral j - ar2BoxIntegral L_end L_int j ≤
        ar2TailBound L_end L_int j := ar2OrthantIntegral_sub_box_le hLe hLi hj1
    have hq_hi : ar2BoxIntegral L_end L_int j ≤
        ar2TensorQuad L_end L_int r j + ar2QuadErr N L_end L_int j := by linarith [hq.2]
    have hup := hhi j hj ho
    have hmul := mul_le_mul_of_nonneg_left (show ar2OrthantIntegral j ≤
        ar2TensorQuad L_end L_int r j + ar2QuadErr N L_end L_int j +
          ar2TailBound L_end L_int j by linarith) h2_nn
    have hterm : 1 * (3 / 2 : ℝ) * (2 : ℝ) ^ (j - 1) * (2 * ar2OrthantIntegral j) =
        3 * (2 : ℝ) ^ (j - 1) * ar2OrthantIntegral j := by ring
    linarith

/-- Decaying diagonal Gaussian factor `e_A(t) = exp (-(3/2) * t^2)`. -/
private noncomputable def eAFactor (t : ℝ) : ℝ := Real.exp (-(3 / 2) * t ^ 2)

/-- Decaying adjacent cross factor `e_{AB}(x, y) = exp (-6 * √2 * x * y)`. -/
private noncomputable def eABFactor (x y : ℝ) : ℝ := Real.exp (-6 * Real.sqrt 2 * x * y)

/-- Decaying skip-one cross factor `e_{AC}(x, z) = exp (-6 * x * z)`. -/
private noncomputable def eACFactor (x z : ℝ) : ℝ := Real.exp (-6 * x * z)

/-- Shifted quadrature node `x_k = (L / 2) * (r_k + 1)` on `(0, L)`. -/
private noncomputable def shiftNode {N : ℕ} (L : ℝ) (r : Fin N → ℝ) (k : Fin N) : ℝ :=
  L / 2 * (r k + 1)

/-- Shifted quadrature weight `w_k = (L / 2) * gaussWeight r k`. -/
private noncomputable def shiftWeight {N : ℕ} (L : ℝ) (r : Fin N → ℝ) (k : Fin N) : ℝ :=
  L / 2 * gaussWeight r k

/-- Exact `j = 1` tensor quadrature sum factored into `eA` and `eAB`. -/
private theorem ar2TensorQuad_one_eq {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) :
    ar2TensorQuad L_end L_int r 1 =
      (3 / (2 * Real.pi)) * ∑ a : Fin N, ∑ b : Fin N,
        (shiftWeight L_end r a * eAFactor (shiftNode L_end r a) ^ 3) *
        (shiftWeight L_end r b * eAFactor (shiftNode L_end r b) ^ 3) *
          eABFactor (shiftNode L_end r a) (shiftNode L_end r b) := by
  let e : (Fin N × Fin N) ≃ (Fin 2 → Fin N) :=
    { toFun := fun p i => match i with | ⟨0, _⟩ => p.1 | ⟨1, _⟩ => p.2
      invFun := fun a => (a 0, a 1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun a => by ext i; fin_cases i <;> rfl }
  unfold ar2TensorQuad
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hprod : ∏ i : Fin 2, ar2BoxBound L_end L_int 1 i / 2 * gaussWeight r (e (a, b) i) =
      shiftWeight L_end r a * shiftWeight L_end r b := by
    rw [Fin.prod_univ_two]; rfl
  have hd : ar2JointDensity 1 (fun i => ar2BoxBound L_end L_int 1 i / 2 * (r (e (a, b) i) + 1)) =
      ar2InitDensity (shiftNode L_end r a) (shiftNode L_end r b) := by
    simp [ar2JointDensity, e, ar2BoxBound, shiftNode]
  rw [hprod, hd, ar2InitDensity_eq_factor]
  unfold eAFactor eABFactor
  ring

/-- Initial `(end, int)` quadrature transfer matrix `M₁[a, b]`. -/
private noncomputable def ar2InitMat {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) (a b : Fin N) :
    ℝ :=
  shiftWeight L_end r a * shiftWeight L_int r b *
    ar2InitDensity (shiftNode L_end r a) (shiftNode L_int r b)

/-- Factored form of `ar2InitMat`. -/
private theorem ar2InitMat_eq_factor {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) (a b : Fin N) :
    ar2InitMat L_end L_int r a b =
      (3 / (2 * Real.pi)) *
        (shiftWeight L_end r a * eAFactor (shiftNode L_end r a) ^ 3) *
        (shiftWeight L_int r b * eAFactor (shiftNode L_int r b) ^ 3) *
        eABFactor (shiftNode L_end r a) (shiftNode L_int r b) := by
  unfold ar2InitMat eAFactor eABFactor
  rw [ar2InitDensity_eq_factor]; ring

/-- Scaled transition step `M ↦ (b, c) ↦ 2 * w_c * ∑ a, M a b * ar2Kernel (x_a) (x_b) (x_c)`. -/
private noncomputable def ar2StepMat {N : ℕ} (xa xb xc wc : Fin N → ℝ)
    (M : Fin N → Fin N → ℝ) (b c : Fin N) : ℝ :=
  2 * wc c * ∑ a : Fin N, M a b * ar2Kernel (xa a) (xb b) (xc c)

/-- Factored form of `ar2StepMat` using a single inner product against `eACFactor`. -/
private theorem ar2StepMat_eq_factor {N : ℕ} (xa xb xc wc : Fin N → ℝ)
    (M : Fin N → Fin N → ℝ) (b c : Fin N) :
    ar2StepMat xa xb xc wc M b c =
      (2 * Real.sqrt (6 / Real.pi) * wc c) *
        (eAFactor (xb b) ^ 8 * (eAFactor (xc c) ^ 4 * eABFactor (xb b) (xc c) ^ 2)) *
        ∑ a : Fin N, (M a b * (eAFactor (xa a) * eABFactor (xa a) (xb b))) *
          eACFactor (xa a) (xc c) := by
  unfold ar2StepMat eAFactor eABFactor eACFactor
  simp_rw [ar2Kernel_eq_factor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

/-- Exact `j = 2` scaled tensor quadrature sum `2 * ar2TensorQuad 2`. -/
private theorem ar2TensorQuad_two_eq {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) :
    2 * ar2TensorQuad L_end L_int r 2 =
      ∑ b : Fin N, ∑ c : Fin N,
        ar2StepMat (shiftNode L_end r) (shiftNode L_int r) (shiftNode L_end r)
          (shiftWeight L_end r) (ar2InitMat L_end L_int r) b c := by
  let e : ((Fin N × Fin N) × Fin N) ≃ (Fin 3 → Fin N) :=
    { toFun := fun p i => match i with
        | ⟨0, _⟩ => p.1.1
        | ⟨1, _⟩ => p.1.2
        | ⟨2, _⟩ => p.2
      invFun := fun a => ((a 0, a 1), a 2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun a => by ext i; fin_cases i <;> rfl }
  unfold ar2TensorQuad
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Finset.mul_sum]
  simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold ar2StepMat ar2InitMat
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hprod : ∏ i : Fin 3, ar2BoxBound L_end L_int 2 i / 2 *
      gaussWeight r (e ((a, b), c) i) =
      shiftWeight L_end r a * shiftWeight L_int r b * shiftWeight L_end r c := by
    rw [Fin.prod_univ_three]; simp [e, ar2BoxBound, shiftWeight, mul_assoc]
  have hd : ar2JointDensity 2 (fun i => ar2BoxBound L_end L_int 2 i / 2 *
      (r (e ((a, b), c) i) + 1)) =
      ar2InitDensity (shiftNode L_end r a) (shiftNode L_int r b) *
        ar2Kernel (shiftNode L_end r a) (shiftNode L_int r b) (shiftNode L_end r c) := by
    simp [ar2JointDensity, e, ar2BoxBound, shiftNode]
  rw [hprod, hd]; ring

/-- Scaled prefix quadrature state matrix `G_m[b, c]` (`m = k - 2`), carrying weight `2^(m+1)`
and summing over coordinates `0..m` with `x_0 ∈ [0, L_end]` and `x_1..x_{m+2} ∈ [0, L_int]`. -/
private noncomputable def ar2PrefixMat {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) :
    ℕ → Fin N → Fin N → ℝ
  | 0 => ar2StepMat (shiftNode L_end r) (shiftNode L_int r) (shiftNode L_int r)
      (shiftWeight L_int r) (ar2InitMat L_end L_int r)
  | m + 1 => ar2StepMat (shiftNode L_int r) (shiftNode L_int r) (shiftNode L_int r)
      (shiftWeight L_int r) (ar2PrefixMat L_end L_int r m)

/-- Terminal readout matrix `R[a, b] = 2 * ∑ c, w_end c * ar2Kernel (x_a) (x_b) (x_c)`. -/
private noncomputable def ar2ReadoutMat {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ)
    (a b : Fin N) : ℝ :=
  2 * ∑ c : Fin N, shiftWeight L_end r c *
    ar2Kernel (shiftNode L_int r a) (shiftNode L_int r b) (shiftNode L_end r c)

/-- Factored form of `ar2ReadoutMat`. -/
private theorem ar2ReadoutMat_eq_factor {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ)
    (a b : Fin N) :
    ar2ReadoutMat L_end L_int r a b =
      (2 * Real.sqrt (6 / Real.pi) *
        (eAFactor (shiftNode L_int r a) *
          (eAFactor (shiftNode L_int r b) ^ 8 *
            eABFactor (shiftNode L_int r a) (shiftNode L_int r b)))) *
      ∑ c : Fin N, shiftWeight L_end r c *
        (eAFactor (shiftNode L_end r c) ^ 4 *
          (eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2 *
            eACFactor (shiftNode L_int r a) (shiftNode L_end r c))) := by
  unfold ar2ReadoutMat eAFactor eABFactor eACFactor
  simp_rw [ar2Kernel_eq_factor, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => by ring

/-- Exact node selection for prefix coordinates: index `0` uses `L_end`, all later indices
use `L_int`. -/
private def prefixBound (L_end L_int : ℝ) {n : ℕ} (i : Fin n) : ℝ :=
  if i.1 = 0 then L_end else L_int

private theorem snoc_castSucc_fun {n : ℕ} (f : Fin n → ℝ) (y : ℝ) :
    (fun i : Fin n => @Fin.snoc n (fun _ => ℝ) f y i.castSucc) = f := by
  ext i; simp

/-- Explicit sum formula for `ar2PrefixMat L_end L_int r m b c`. -/
private theorem ar2PrefixMat_eq {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) :
    ∀ (m : ℕ) (b c : Fin N),
      ar2PrefixMat L_end L_int r m b c =
        (2 : ℝ) ^ (m + 1) * ∑ p : Fin (m + 1) → Fin N,
          (∏ i : Fin (m + 1),
            shiftWeight (prefixBound L_end L_int i) r (p i)) *
          shiftWeight L_int r b * shiftWeight L_int r c *
          ar2JointDensity (m + 2)
            (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
              shiftNode (prefixBound L_end L_int i) r (p i))
              (shiftNode L_int r b)) (shiftNode L_int r c)) := by
  intro m
  induction m with
  | zero =>
      intro b c
      let e : Fin N ≃ (Fin 1 → Fin N) :=
        { toFun := fun a _ => a
          invFun := fun p => p 0
          left_inv := fun _ => rfl
          right_inv := fun p => by ext i; fin_cases i; rfl }
      rw [← Equiv.sum_comp e]
      simp only [ar2PrefixMat, ar2StepMat, ar2InitMat, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hprod : ∏ i : Fin 1, shiftWeight (prefixBound L_end L_int i) r (e a i) =
          shiftWeight L_end r a := by simp [e, prefixBound]
      have hd : ar2JointDensity 2 (Fin.snoc (Fin.snoc (fun i : Fin 1 =>
            shiftNode (prefixBound L_end L_int i) r (e a i)) (shiftNode L_int r b))
            (shiftNode L_int r c)) =
          ar2InitDensity (shiftNode L_end r a) (shiftNode L_int r b) *
            ar2Kernel (shiftNode L_end r a) (shiftNode L_int r b) (shiftNode L_int r c) := by
        simp [ar2JointDensity, e, prefixBound, Fin.snoc]
      rw [hprod, hd]; ring
  | succ m ih =>
      intro b c
      let e : ((Fin (m + 1) → Fin N) × Fin N) ≃ (Fin (m + 2) → Fin N) :=
        { toFun := fun q => Fin.snoc q.1 q.2
          invFun := fun p => (fun i => p i.castSucc, p (Fin.last (m + 1)))
          left_inv := fun ⟨p, a⟩ => by ext i <;> simp
          right_inv := fun p => by
            ext i; refine Fin.lastCases (by simp) (fun j => by simp) i }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type, Finset.sum_comm]
      change ar2StepMat (shiftNode L_int r) (shiftNode L_int r) (shiftNode L_int r)
        (shiftWeight L_int r) (ar2PrefixMat L_end L_int r m) b c = _
      unfold ar2StepMat
      simp_rw [ih]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      have hprod : ∏ i : Fin (m + 2), shiftWeight (prefixBound L_end L_int i) r (e (p, a) i) =
          (∏ i : Fin (m + 1), shiftWeight (prefixBound L_end L_int i) r (p i)) *
            shiftWeight L_int r a := by
        rw [Fin.prod_univ_castSucc]
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          have hpb : prefixBound L_end L_int i.castSucc = prefixBound L_end L_int i := rfl
          simp [e, hpb]
        · simp [e, prefixBound]
      have hvec : (fun i : Fin (m + 2) =>
            shiftNode (prefixBound L_end L_int i) r (e (p, a) i)) =
          Fin.snoc (fun i : Fin (m + 1) =>
            shiftNode (prefixBound L_end L_int i) r (p i)) (shiftNode L_int r a) := by
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [e, prefixBound]
        · have hpb : prefixBound L_end L_int j.castSucc = prefixBound L_end L_int j := rfl
          simp [e, hpb]
      rw [hvec, hprod, ar2JointDensity_succ (m + 1)]
      have hcast := snoc_castSucc_fun
        (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
          shiftNode (prefixBound L_end L_int i) r (p i))
          (shiftNode L_int r a)) (shiftNode L_int r b)) (shiftNode L_int r c)
      have ha_eq : (Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
            shiftNode (prefixBound L_end L_int i) r (p i))
            (shiftNode L_int r a)) (shiftNode L_int r b)) (shiftNode L_int r c) :
            Fin (m + 4) → ℝ) ⟨m + 1, by omega⟩ = shiftNode L_int r a := by
        have h1 : (⟨m + 1, by omega⟩ : Fin (m + 4)) =
            (Fin.last (m + 1)).castSucc.castSucc := rfl
        rw [h1]; simp
      have hb_eq : (Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
            shiftNode (prefixBound L_end L_int i) r (p i))
            (shiftNode L_int r a)) (shiftNode L_int r b)) (shiftNode L_int r c) :
            Fin (m + 4) → ℝ) ⟨m + 1 + 1, by omega⟩ = shiftNode L_int r b := by
        have h1 : (⟨m + 1 + 1, by omega⟩ : Fin (m + 4)) =
            (Fin.last (m + 2)).castSucc := rfl
        rw [h1]; simp
      have hc_eq : (Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
            shiftNode (prefixBound L_end L_int i) r (p i))
            (shiftNode L_int r a)) (shiftNode L_int r b)) (shiftNode L_int r c) :
            Fin (m + 4) → ℝ) ⟨m + 1 + 2, by omega⟩ = shiftNode L_int r c := by
        have h1 : (⟨m + 1 + 2, by omega⟩ : Fin (m + 4)) = Fin.last (m + 3) := rfl
        rw [h1]; simp
      rw [hcast, ha_eq, hb_eq, hc_eq, pow_succ]
      ring

/-- For every `m : ℕ` (`j = m + 3`), `2^(m + 2) * ar2TensorQuad (m + 3)` equals the Frobenius
inner product of `ar2PrefixMat m` and `ar2ReadoutMat`. -/
private theorem ar2TensorQuad_ge_three_eq {N : ℕ} (L_end L_int : ℝ) (r : Fin N → ℝ) (m : ℕ) :
    (2 : ℝ) ^ (m + 2) * ar2TensorQuad L_end L_int r (m + 3) =
      ∑ a : Fin N, ∑ b : Fin N,
        ar2PrefixMat L_end L_int r m a b * ar2ReadoutMat L_end L_int r a b := by
  let e : (((Fin (m + 1) → Fin N) × Fin N) × Fin N × Fin N) ≃ (Fin (m + 4) → Fin N) :=
    { toFun := fun q => Fin.snoc (Fin.snoc (Fin.snoc q.1.1 q.1.2) q.2.1) q.2.2
      invFun := fun f =>
        (((fun i : Fin (m + 1) => f i.castSucc.castSucc.castSucc),
          f (Fin.last (m + 1)).castSucc.castSucc),
          (f (Fin.last (m + 2)).castSucc, f (Fin.last (m + 3))))
      left_inv := fun ⟨⟨p, a⟩, ⟨b, c⟩⟩ =>
        Prod.ext (Prod.ext (funext fun i => by simp) (by simp))
          (Prod.ext (by simp) (by simp))
      right_inv := fun f => by
        ext i
        refine Fin.lastCases (by simp) (fun j => ?_) i
        refine Fin.lastCases (by simp) (fun k => ?_) j
        refine Fin.lastCases (by simp) (fun l => ?_) k
        simp }
  unfold ar2TensorQuad
  rw [← Equiv.sum_comp e]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  calc (∑ p : Fin (m + 1) → Fin N, (2 : ℝ) ^ (m + 2) *
          ∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
            (∏ i : Fin (m + 4), ar2BoxBound L_end L_int (m + 3) i / 2 *
              gaussWeight r (e ((p, a), (b, c)) i)) *
              ar2JointDensity (m + 3) (fun i => ar2BoxBound L_end L_int (m + 3) i / 2 *
                (r (e ((p, a), (b, c)) i) + 1)))
      = ∑ a : Fin N, ∑ b : Fin N, ∑ p : Fin (m + 1) → Fin N, ∑ c : Fin N,
          (2 : ℝ) ^ (m + 2) *
            ((∏ i : Fin (m + 4), ar2BoxBound L_end L_int (m + 3) i / 2 *
              gaussWeight r (e ((p, a), (b, c)) i)) *
              ar2JointDensity (m + 3) (fun i => ar2BoxBound L_end L_int (m + 3) i / 2 *
                (r (e ((p, a), (b, c)) i) + 1))) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : Fin N, ∑ b : Fin N,
          ar2PrefixMat L_end L_int r m a b * ar2ReadoutMat L_end L_int r a b := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [ar2PrefixMat_eq L_end L_int r m a b]
          unfold ar2ReadoutMat
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          have hprod : ∏ i : Fin (m + 4), ar2BoxBound L_end L_int (m + 3) i / 2 *
              gaussWeight r (e ((p, a), (b, c)) i) =
              (∏ i : Fin (m + 1), shiftWeight (prefixBound L_end L_int i) r (p i)) *
                shiftWeight L_int r a * shiftWeight L_int r b * shiftWeight L_end r c := by
            rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
            have h0 : ∏ i : Fin (m + 1),
                ar2BoxBound L_end L_int (m + 3) i.castSucc.castSucc.castSucc / 2 *
                  gaussWeight r (e ((p, a), (b, c)) i.castSucc.castSucc.castSucc) =
                ∏ i : Fin (m + 1), shiftWeight (prefixBound L_end L_int i) r (p i) := by
              refine Finset.prod_congr rfl fun i _ => ?_
              have hlt : i.1 ≠ m + 3 := by omega
              have hb_eq : ar2BoxBound L_end L_int (m + 3) i.castSucc.castSucc.castSucc =
                  prefixBound L_end L_int i := by
                unfold ar2BoxBound prefixBound
                change (if i.1 = 0 ∨ i.1 = m + 3 then L_end else L_int) =
                  if i.1 = 0 then L_end else L_int
                simp [hlt]
              simp [e, hb_eq, shiftWeight]
            have ha_b : ar2BoxBound L_end L_int (m + 3) (Fin.last (m + 1)).castSucc.castSucc =
                L_int := by
              unfold ar2BoxBound; simp
            have hb_b : ar2BoxBound L_end L_int (m + 3) (Fin.last (m + 2)).castSucc = L_int := by
              unfold ar2BoxBound; simp
            have hc_b : ar2BoxBound L_end L_int (m + 3) (Fin.last (m + 3)) = L_end := by
              unfold ar2BoxBound; simp
            rw [h0, ha_b, hb_b, hc_b]
            simp [e, shiftWeight]
          have hvec : (fun i : Fin (m + 4) =>
                ar2BoxBound L_end L_int (m + 3) i / 2 * (r (e ((p, a), (b, c)) i) + 1)) =
              Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
                shiftNode (prefixBound L_end L_int i) r (p i)) (shiftNode L_int r a))
                (shiftNode L_int r b)) (shiftNode L_end r c) := by
            ext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [e, ar2BoxBound, shiftNode]
            · refine Fin.lastCases ?_ (fun k => ?_) j
              · simp [e, ar2BoxBound, shiftNode]
              · refine Fin.lastCases ?_ (fun l => ?_) k
                · simp [e, ar2BoxBound, shiftNode]
                · have hlt : l.1 ≠ m + 3 := by omega
                  have hb_eq : ar2BoxBound L_end L_int (m + 3) l.castSucc.castSucc.castSucc =
                      prefixBound L_end L_int l := by
                    unfold ar2BoxBound prefixBound
                    change (if l.1 = 0 ∨ l.1 = m + 3 then L_end else L_int) =
                      if l.1 = 0 then L_end else L_int
                    simp [hlt]
                  simp [e, hb_eq, shiftNode]
          rw [hprod, hvec, ar2JointDensity_succ (m + 1)]
          have hcast := snoc_castSucc_fun
            (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
              shiftNode (prefixBound L_end L_int i) r (p i)) (shiftNode L_int r a))
              (shiftNode L_int r b)) (shiftNode L_end r c)
          have ha_eq : (Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
                shiftNode (prefixBound L_end L_int i) r (p i)) (shiftNode L_int r a))
                (shiftNode L_int r b)) (shiftNode L_end r c) : Fin (m + 4) → ℝ)
                ⟨m + 1, by omega⟩ = shiftNode L_int r a := by
            have h1 : (⟨m + 1, by omega⟩ : Fin (m + 4)) =
                (Fin.last (m + 1)).castSucc.castSucc := rfl
            rw [h1]; simp
          have hb_eq : (Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
                shiftNode (prefixBound L_end L_int i) r (p i)) (shiftNode L_int r a))
                (shiftNode L_int r b)) (shiftNode L_end r c) : Fin (m + 4) → ℝ)
                ⟨m + 1 + 1, by omega⟩ = shiftNode L_int r b := by
            have h1 : (⟨m + 1 + 1, by omega⟩ : Fin (m + 4)) =
                (Fin.last (m + 2)).castSucc := rfl
            rw [h1]; simp
          have hc_eq : (Fin.snoc (Fin.snoc (Fin.snoc (fun i : Fin (m + 1) =>
                shiftNode (prefixBound L_end L_int i) r (p i)) (shiftNode L_int r a))
                (shiftNode L_int r b)) (shiftNode L_end r c) : Fin (m + 4) → ℝ)
                ⟨m + 1 + 2, by omega⟩ = shiftNode L_end r c := by
            have h1 : (⟨m + 1 + 2, by omega⟩ : Fin (m + 4)) = Fin.last (m + 3) := rfl
            rw [h1]; simp
          rw [hcast, ha_eq, hb_eq, hc_eq, pow_succ]
          ring

end AR2QuadRecurrence

/-! ### Pure `Nat` fixed-point interval arithmetic and soundness lemmas -/

section FixedPointSoundness

/-- Scale-`s` rounded-down fixed-point multiplication `⌊a * b / s⌋`. -/
private def fpMulDn (s a b : ℕ) : ℕ := Nat.div (Nat.mul a b) s

/-- Scale-`s` rounded-up fixed-point multiplication `⌈a * b / s⌉`. -/
private def fpMulUp (s a b : ℕ) : ℕ := Nat.div (Nat.add (Nat.mul a b) (Nat.sub s 1)) s

/-- Scale-`s` rounded-down fixed-point power `a^k`. -/
private def fpPowDn (s a : ℕ) : ℕ → ℕ
  | 0 => s
  | k + 1 => fpMulDn s (fpPowDn s a k) a

/-- Scale-`s` rounded-up fixed-point power `a^k`. -/
private def fpPowUp (s a : ℕ) : ℕ → ℕ
  | 0 => s
  | k + 1 => fpMulUp s (fpPowUp s a k) a

/-- Apply `k` rounded-down squarings at scale `s`. -/
private def fpSqIterDn (s : ℕ) : ℕ → ℕ → ℕ
  | 0, v => v
  | k + 1, v => fpSqIterDn s k (fpMulDn s v v)

/-- Apply `k` rounded-up squarings at scale `s`. -/
private def fpSqIterUp (s : ℕ) : ℕ → ℕ → ℕ
  | 0, v => v
  | k + 1, v => fpSqIterUp s k (fpMulUp s v v)

/-- Soundness of `Nat.div` rounded down against real division. -/
private theorem natDiv_cast_le {a s : ℕ} (hs : 0 < s) :
    ((Nat.div a s : ℕ) : ℝ) ≤ (a : ℝ) / (s : ℝ) := by
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  rw [le_div_iff₀ hsR]
  exact_mod_cast Nat.div_mul_le_self a s

/-- Soundness of ceiling `Nat.div (a + s - 1) s` against real division. -/
private theorem le_natDivUp_cast {a s : ℕ} (hs : 0 < s) :
    (a : ℝ) / (s : ℝ) ≤ ((Nat.div (Nat.add a (Nat.sub s 1)) s : ℕ) : ℝ) := by
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  rw [div_le_iff₀ hsR]
  have hnat : a ≤ (a + (s - 1)) / s * s := by
    have hlt := Nat.lt_div_mul_add hs (a := a + (s - 1))
    omega
  exact_mod_cast hnat

/-- Soundness of `fpMulDn`. -/
private theorem fpMulDn_le {s a b : ℕ} (hs : 0 < s) :
    (fpMulDn s a b : ℝ) / s ≤ (a : ℝ) / s * ((b : ℝ) / s) := by
  unfold fpMulDn
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have h := natDiv_cast_le (a := a * b) hs
  rw [div_le_iff₀ hsR]
  calc (Nat.div (a * b) s : ℝ) ≤ (a * b : ℕ) / (s : ℝ) := h
    _ = ((a : ℝ) / s * ((b : ℝ) / s)) * s := by push_cast; field_simp

/-- Soundness of `fpMulUp`. -/
private theorem le_fpMulUp {s a b : ℕ} (hs : 0 < s) :
    (a : ℝ) / s * ((b : ℝ) / s) ≤ (fpMulUp s a b : ℝ) / s := by
  unfold fpMulUp
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have h := le_natDivUp_cast (a := a * b) hs
  rw [le_div_iff₀ hsR]
  calc (a : ℝ) / s * ((b : ℝ) / s) * s = (a * b : ℕ) / (s : ℝ) := by push_cast; field_simp
    _ ≤ (Nat.div (Nat.add (a * b) (Nat.sub s 1)) s : ℝ) := h

/-- Soundness of `fpMulDn` lifted to real interval lower bounds. -/
private theorem fpMulDn_le_mul {s a b : ℕ} (hs : 0 < s) {x y : ℝ}
    (hx : (a : ℝ) / s ≤ x) (hy : (b : ℝ) / s ≤ y) :
    (fpMulDn s a b : ℝ) / s ≤ x * y :=
  (fpMulDn_le hs).trans (mul_le_mul hx hy (by positivity)
    ((by positivity : (0 : ℝ) ≤ a / s).trans hx))

/-- Soundness of `fpMulUp` lifted to real interval upper bounds. -/
private theorem mul_le_fpMulUp {s a b : ℕ} (hs : 0 < s) {x y : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ (a : ℝ) / s) (hy : y ≤ (b : ℝ) / s) :
    x * y ≤ (fpMulUp s a b : ℝ) / s :=
  (mul_le_mul hx hy hy0 (hx0.trans hx)).trans (le_fpMulUp hs)

/-- Soundness of `fpPowDn`. -/
private theorem fpPowDn_le {s a k : ℕ} (hs : 0 < s) {x : ℝ} (hx : (a : ℝ) / s ≤ x) :
    (fpPowDn s a k : ℝ) / s ≤ x ^ k := by
  induction k with
  | zero =>
      have hsne : (s : ℝ) ≠ 0 := (Nat.cast_pos.mpr hs).ne'
      simp [fpPowDn, div_self hsne]
  | succ k ih =>
      rw [fpPowDn, pow_succ]
      exact fpMulDn_le_mul hs ih hx

/-- Soundness of `fpPowUp`. -/
private theorem pow_le_fpPowUp {s a k : ℕ} (hs : 0 < s) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ (a : ℝ) / s) :
    x ^ k ≤ (fpPowUp s a k : ℝ) / s := by
  induction k with
  | zero =>
      have hsne : (s : ℝ) ≠ 0 := (Nat.cast_pos.mpr hs).ne'
      simp [fpPowUp, div_self hsne]
  | succ k ih =>
      rw [fpPowUp, pow_succ]
      exact mul_le_fpMulUp hs (pow_nonneg hx0 k) hx0 ih hx

/-- Soundness of `fpSqIterDn`: `k` squarings bound `x ^ (2 ^ k)` from below. -/
private theorem fpSqIterDn_le {s : ℕ} (hs : 0 < s) (k : ℕ) :
    ∀ {v : ℕ} {x : ℝ}, (v : ℝ) / s ≤ x →
      (fpSqIterDn s k v : ℝ) / s ≤ x ^ (2 ^ k) := by
  induction k with
  | zero => intro v x hv; simpa [fpSqIterDn] using hv
  | succ k ih =>
      intro v x hv
      rw [fpSqIterDn, pow_succ', pow_mul]
      exact ih (v := fpMulDn s v v) (x := x ^ 2)
        (by rw [sq]; exact fpMulDn_le_mul hs hv hv)

/-- Soundness of `fpSqIterUp`: `k` squarings bound `x ^ (2 ^ k)` from above. -/
private theorem pow_le_fpSqIterUp {s : ℕ} (hs : 0 < s) (k : ℕ) :
    ∀ {v : ℕ} {x : ℝ}, 0 ≤ x → x ≤ (v : ℝ) / s →
      x ^ (2 ^ k) ≤ (fpSqIterUp s k v : ℝ) / s := by
  induction k with
  | zero => intro v x _ hv; simpa [fpSqIterUp] using hv
  | succ k ih =>
      intro v x hx0 hv
      rw [fpSqIterUp, pow_succ', pow_mul]
      exact ih (v := fpMulUp s v v) (x := x ^ 2) (sq_nonneg x)
        (by rw [sq]; exact mul_le_fpMulUp hs hx0 hx0 hv hv)

/-- Signed Taylor remainder `(-1)^n * (exp (-t) - ∑_{k < n} (-t)^k / k!)`. -/
private noncomputable def expTaylorRem (n : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (Real.exp (-t) - ∑ k ∈ Finset.range n, (-t) ^ k / (k.factorial : ℝ))

/-- The alternating Taylor remainder of `exp (-t)` is nonnegative for all `t ≥ 0`. -/
private theorem expTaylorRem_nonneg (n : ℕ) : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ expTaylorRem n t := by
  induction n with
  | zero =>
      intro t _
      simp [expTaylorRem, (Real.exp_pos (-t)).le]
  | succ n ih =>
      intro t ht
      have h0 : expTaylorRem (n + 1) 0 = 0 := by
        unfold expTaylorRem
        have hsum : ∑ k ∈ Finset.range (n + 1), (0 : ℝ) ^ k / (k.factorial : ℝ) = 1 := by
          rw [Finset.sum_eq_single 0]
          · simp
          · intro k _ hk; simp [zero_pow hk]
          · intro h; simp at h
        rw [neg_zero, Real.exp_zero, hsum, sub_self, mul_zero]
      have hd : ∀ x : ℝ, HasDerivAt (expTaylorRem (n + 1)) (expTaylorRem n x) x := by
        intro x
        have he : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
          have := (hasDerivAt_id x).neg.exp
          simpa using this
        have hs : HasDerivAt
            (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), (-y) ^ k / (k.factorial : ℝ))
            (-∑ k ∈ Finset.range n, (-x) ^ k / (k.factorial : ℝ)) x := by
          have hterm : ∀ k : ℕ, HasDerivAt (fun y : ℝ => (-y) ^ k / (k.factorial : ℝ))
              (if k = 0 then 0 else -((-x) ^ (k - 1) / ((k - 1).factorial : ℝ))) x := fun k => by
            cases k with
            | zero =>
                simpa using hasDerivAt_const x (1 : ℝ)
            | succ m =>
                have hfac : ((m + 1).factorial : ℝ) = (m + 1 : ℝ) * (m.factorial : ℝ) := by
                  rw [Nat.factorial_succ]; push_cast; ring
                have hbase := (((hasDerivAt_id x).neg.pow (m + 1)).div_const
                  ((m + 1).factorial : ℝ))
                refine hbase.congr_deriv ?_
                simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
                  Nat.add_sub_cancel, hfac]
                change (((m + 1 : ℕ) : ℝ) * (-x) ^ m * -1) / ((m + 1 : ℝ) * m.factorial) =
                  -((-x) ^ m / m.factorial)
                push_cast
                have hm : (m + 1 : ℝ) ≠ 0 := by positivity
                field_simp
          have hsum : HasDerivAt
              (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), (-y) ^ k / (k.factorial : ℝ))
              (∑ k ∈ Finset.range (n + 1),
                if k = 0 then (0 : ℝ) else -((-x) ^ (k - 1) / ((k - 1).factorial : ℝ))) x := by
            have := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun k _ => hterm k)
            exact this
          refine hsum.congr_deriv ?_
          rw [Finset.sum_range_succ']
          simp only [↓reduceIte, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            Nat.add_sub_cancel, Finset.sum_neg_distrib]
        have hsub := (he.sub hs).const_mul ((-1 : ℝ) ^ (n + 1))
        refine hsub.congr_deriv ?_
        unfold expTaylorRem
        rw [pow_succ]
        ring
      have hmono : MonotoneOn (expTaylorRem (n + 1)) (Set.Ici (0 : ℝ)) :=
        monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
          (fun x _ => (hd x).continuousAt.continuousWithinAt)
          (fun x _ => (hd x).hasDerivWithinAt)
          (fun x hx => ih (interior_subset hx))
      rw [← h0]
      exact hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) ht ht

/-- Alternating partial-sum bounds for `Real.exp (-t)` (`t ≥ 0`). -/
private theorem exp_neg_ge_taylor (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∑ j ∈ Finset.range m, t ^ (2 * j) / ((2 * j).factorial : ℝ)) -
      (∑ j ∈ Finset.range m, t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) ≤
      Real.exp (-t) := by
  have hr := expTaylorRem_nonneg (2 * m) ht
  unfold expTaylorRem at hr
  have hpow : (-1 : ℝ) ^ (2 * m) = 1 := (even_two_mul m).neg_one_pow
  rw [hpow, one_mul, sub_nonneg] at hr
  refine le_trans ?_ hr
  have hsplit : ∀ k : ℕ, ∑ i ∈ Finset.range (2 * k), (-t) ^ i / (i.factorial : ℝ) =
      (∑ j ∈ Finset.range k, t ^ (2 * j) / ((2 * j).factorial : ℝ)) -
      (∑ j ∈ Finset.range k, t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
          Finset.sum_range_succ, Finset.sum_range_succ]
        have he : (-t) ^ (2 * k) = t ^ (2 * k) := (even_two_mul k).neg_pow t
        have ho : (-t) ^ (2 * k + 1) = -(t ^ (2 * k + 1)) :=
          ((even_two_mul k).add_one).neg_pow t
        rw [he, ho]; ring
  exact (hsplit m).ge

/-- Alternating partial-sum upper bound for `Real.exp (-t)` (`t ≥ 0`). -/
private theorem exp_neg_le_taylor (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤
      (∑ j ∈ Finset.range (m + 1), t ^ (2 * j) / ((2 * j).factorial : ℝ)) -
      (∑ j ∈ Finset.range m, t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
  have hr := expTaylorRem_nonneg (2 * m + 1) ht
  unfold expTaylorRem at hr
  have hpow : (-1 : ℝ) ^ (2 * m + 1) = -1 := ((even_two_mul m).add_one).neg_one_pow
  rw [hpow] at hr
  have hle : Real.exp (-t) ≤ ∑ i ∈ Finset.range (2 * m + 1), (-t) ^ i / (i.factorial : ℝ) := by
    linarith
  refine hle.trans_eq ?_
  rw [Finset.sum_range_succ]
  have hsplit : ∀ k : ℕ, ∑ i ∈ Finset.range (2 * k), (-t) ^ i / (i.factorial : ℝ) =
      (∑ j ∈ Finset.range k, t ^ (2 * j) / ((2 * j).factorial : ℝ)) -
      (∑ j ∈ Finset.range k, t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
          Finset.sum_range_succ, Finset.sum_range_succ]
        have he : (-t) ^ (2 * k) = t ^ (2 * k) := (even_two_mul k).neg_pow t
        have ho : (-t) ^ (2 * k + 1) = -(t ^ (2 * k + 1)) :=
          ((even_two_mul k).add_one).neg_pow t
        rw [he, ho]; ring
  rw [hsplit m, Finset.sum_range_succ, (even_two_mul m).neg_pow t]
  ring

/-- Rounded-down Taylor terms `t^k / k!` at scale `T`: returns `(termDn, termUp)` chain sum for
`exp (-t)` lower bound with `m` pairs (`k = 0..2m-1`). -/
private def expTermDn (T u : ℕ) : ℕ → ℕ
  | 0 => T
  | k + 1 => Nat.div (Nat.mul (expTermDn T u k) u) (Nat.mul T (k + 1))

/-- Rounded-up Taylor term `t^k / k!` at scale `T`. -/
private def expTermUp (T u : ℕ) : ℕ → ℕ
  | 0 => T
  | k + 1 =>
      let den := Nat.mul T (k + 1)
      Nat.div (Nat.add (Nat.mul (expTermUp T u k) u) (Nat.sub den 1)) den

/-- Tail-recursive evaluator for the `2 * m`-term alternating lower bound on `exp (-t)` at scale
`T`, using explicit `Nat` primitives for kernel-fast reduction. -/
private def expLoLoop (T u k rem tDn tUp accEven accOdd : ℕ) : ℕ × ℕ :=
  match rem with
  | 0 => (accEven, accOdd)
  | rem' + 1 =>
      let den1 := Nat.mul T (Nat.add k 1)
      let tUp1 := Nat.div (Nat.add (Nat.mul tUp u) (Nat.sub den1 1)) den1
      let tDn1 := Nat.div (Nat.mul tDn u) den1
      let den2 := Nat.mul T (Nat.add k 2)
      let tDn2 := Nat.div (Nat.mul tDn1 u) den2
      let tUp2 := Nat.div (Nat.add (Nat.mul tUp1 u) (Nat.sub den2 1)) den2
      expLoLoop T u (Nat.add k 2) rem' tDn2 tUp2
        (Nat.add accEven tDn) (Nat.add accOdd tUp1)

/-- Scale-`T` alternating lower bound on `exp (-u / T)` using `m` pairs. -/
private def expStepLoSum (T u m : ℕ) : ℕ :=
  let (eDn, oUp) := expLoLoop T u 0 m T T 0 0
  Nat.sub eDn oUp

/-- Scale-`T` alternating upper bound on `exp (-u / T)` using `m` odd terms and `m + 1` even
terms. -/
private def expHiLoop (T u k rem tDn tUp accEven accOdd : ℕ) : ℕ × ℕ :=
  match rem with
  | 0 => (Nat.add accEven tUp, accOdd)
  | rem' + 1 =>
      let den1 := Nat.mul T (Nat.add k 1)
      let tDn1 := Nat.div (Nat.mul tDn u) den1
      let tUp1 := Nat.div (Nat.add (Nat.mul tUp u) (Nat.sub den1 1)) den1
      let den2 := Nat.mul T (Nat.add k 2)
      let tDn2 := Nat.div (Nat.mul tDn1 u) den2
      let tUp2 := Nat.div (Nat.add (Nat.mul tUp1 u) (Nat.sub den2 1)) den2
      expHiLoop T u (Nat.add k 2) rem' tDn2 tUp2
        (Nat.add accEven tUp) (Nat.add accOdd tDn1)

/-- Scale-`T` alternating upper bound on `exp (-u / T)`. -/
private def expStepHiSum (T u m : ℕ) : ℕ :=
  let (eUp, oDn) := expHiLoop T u 0 m T T 0 0
  Nat.sub eUp oDn

/-- Soundness of `expTermDn`. -/
private theorem expTermDn_le {T u : ℕ} (hT : 0 < T) (k : ℕ) :
    (expTermDn T u k : ℝ) / T ≤ ((u : ℝ) / T) ^ k / (k.factorial : ℝ) := by
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  induction k with
  | zero => simp [expTermDn, div_self hTR.ne']
  | succ k ih =>
      unfold expTermDn
      have hden : 0 < T * (k + 1) := Nat.mul_pos hT (Nat.succ_pos k)
      have hdiv := natDiv_cast_le (a := expTermDn T u k * u) hden
      have hmul : (Nat.div (expTermDn T u k * u) (T * (k + 1)) : ℝ) / T ≤
          ((expTermDn T u k : ℝ) / T) * ((u : ℝ) / T) / (k + 1 : ℝ) := by
        calc (Nat.div (expTermDn T u k * u) (T * (k + 1)) : ℝ) / T
            ≤ ((expTermDn T u k * u : ℕ) / (T * (k + 1) : ℕ)) / T :=
                div_le_div_of_nonneg_right hdiv hTR.le
          _ = ((expTermDn T u k : ℝ) / T) * ((u : ℝ) / T) / (k + 1 : ℝ) := by
                push_cast; field_simp
      refine hmul.trans ?_
      have hstep : ((expTermDn T u k : ℝ) / T) * ((u : ℝ) / T) / (k + 1 : ℝ) ≤
          (((u : ℝ) / T) ^ k / (k.factorial : ℝ)) * ((u : ℝ) / T) / (k + 1 : ℝ) := by
        gcongr
      refine hstep.trans_eq ?_
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have hne1 : (k + 1 : ℝ) ≠ 0 := by positivity
      have hne2 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
      field_simp

/-- Soundness of `expTermUp`. -/
private theorem le_expTermUp {T u : ℕ} (hT : 0 < T) (k : ℕ) :
    ((u : ℝ) / T) ^ k / (k.factorial : ℝ) ≤ (expTermUp T u k : ℝ) / T := by
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  induction k with
  | zero => simp [expTermUp, div_self hTR.ne']
  | succ k ih =>
      unfold expTermUp
      dsimp only
      have hden : 0 < T * (k + 1) := Nat.mul_pos hT (Nat.succ_pos k)
      have hdiv := le_natDivUp_cast (a := expTermUp T u k * u) hden
      have hfac : ((u : ℝ) / T) ^ (k + 1) / ((k + 1).factorial : ℝ) =
          (((u : ℝ) / T) ^ k / (k.factorial : ℝ)) * ((u : ℝ) / T) / (k + 1 : ℝ) := by
        rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
      rw [hfac]
      calc (((u : ℝ) / T) ^ k / (k.factorial : ℝ)) * ((u : ℝ) / T) / (k + 1 : ℝ)
          ≤ ((expTermUp T u k : ℝ) / T) * ((u : ℝ) / T) / (k + 1 : ℝ) := by gcongr
        _ = ((expTermUp T u k * u : ℕ) / (T * (k + 1) : ℕ)) / T := by
              push_cast; field_simp
        _ ≤ (Nat.div (Nat.add (expTermUp T u k * u) (Nat.sub (T * (k + 1)) 1))
              (T * (k + 1)) : ℝ) / T := div_le_div_of_nonneg_right hdiv hTR.le

/-- Exact equivalence of `expLoLoop` with finite sums of `expTermDn`/`expTermUp`. -/
private theorem expLoLoop_eq (T u : ℕ) :
    ∀ (rem k accEven accOdd : ℕ),
      expLoLoop T u k rem (expTermDn T u k) (expTermUp T u k) accEven accOdd =
        (accEven + ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 * j),
         accOdd + ∑ j ∈ Finset.range rem, expTermUp T u (k + 2 * j + 1)) := by
  intro rem
  induction rem with
  | zero => intro k ae ao; simp [expLoLoop]
  | succ rem ih =>
      intro k ae ao
      change expLoLoop T u (k + 2) rem (expTermDn T u (k + 2)) (expTermUp T u (k + 2))
        (ae + expTermDn T u k) (ao + expTermUp T u (k + 1)) = _
      rw [ih]
      ext
      · change ae + expTermDn T u k + ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 + 2 * j) =
          ae + ∑ j ∈ Finset.range (rem + 1), expTermDn T u (k + 2 * j)
        rw [Finset.sum_range_succ', Nat.mul_zero, add_zero]
        have hs : ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 + 2 * j) =
            ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 * (j + 1)) :=
          Finset.sum_congr rfl fun j _ => by congr 1; omega
        rw [hs]; omega
      · change ao + expTermUp T u (k + 1) +
          ∑ j ∈ Finset.range rem, expTermUp T u (k + 2 + 2 * j + 1) =
          ao + ∑ j ∈ Finset.range (rem + 1), expTermUp T u (k + 2 * j + 1)
        rw [Finset.sum_range_succ', Nat.mul_zero, add_zero]
        have hs : ∑ j ∈ Finset.range rem, expTermUp T u (k + 2 + 2 * j + 1) =
            ∑ j ∈ Finset.range rem, expTermUp T u (k + 2 * (j + 1) + 1) :=
          Finset.sum_congr rfl fun j _ => by congr 1; omega
        rw [hs]; omega

/-- Exact equivalence of `expHiLoop` with finite sums of `expTermUp`/`expTermDn`. -/
private theorem expHiLoop_eq (T u : ℕ) :
    ∀ (rem k accEven accOdd : ℕ),
      expHiLoop T u k rem (expTermDn T u k) (expTermUp T u k) accEven accOdd =
        (accEven + ∑ j ∈ Finset.range (rem + 1), expTermUp T u (k + 2 * j),
         accOdd + ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 * j + 1)) := by
  intro rem
  induction rem with
  | zero => intro k ae ao; simp [expHiLoop]
  | succ rem ih =>
      intro k ae ao
      change expHiLoop T u (k + 2) rem (expTermDn T u (k + 2)) (expTermUp T u (k + 2))
        (ae + expTermUp T u k) (ao + expTermDn T u (k + 1)) = _
      rw [ih]
      ext
      · change ae + expTermUp T u k +
          ∑ j ∈ Finset.range (rem + 1), expTermUp T u (k + 2 + 2 * j) =
          ae + ∑ j ∈ Finset.range (rem + 1 + 1), expTermUp T u (k + 2 * j)
        have hs : ∑ j ∈ Finset.range (rem + 1), expTermUp T u (k + 2 + 2 * j) =
            ∑ j ∈ Finset.range (rem + 1), expTermUp T u (k + 2 * (j + 1)) :=
          Finset.sum_congr rfl fun j _ => by congr 1; omega
        rw [hs]
        conv_rhs => rw [Finset.sum_range_succ', Nat.mul_zero, add_zero]
        omega
      · change ao + expTermDn T u (k + 1) +
          ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 + 2 * j + 1) =
          ao + ∑ j ∈ Finset.range (rem + 1), expTermDn T u (k + 2 * j + 1)
        rw [Finset.sum_range_succ', Nat.mul_zero, add_zero]
        have hs : ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 + 2 * j + 1) =
            ∑ j ∈ Finset.range rem, expTermDn T u (k + 2 * (j + 1) + 1) :=
          Finset.sum_congr rfl fun j _ => by congr 1; omega
        rw [hs]; omega

/-- Soundness of `expStepLoSum`: `(expStepLoSum T u m : ℝ) / T ≤ Real.exp (-(u / T))`. -/
private theorem expStepLoSum_le {T u m : ℕ} (hT : 0 < T) :
    (expStepLoSum T u m : ℝ) / T ≤ Real.exp (-((u : ℝ) / T)) := by
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hpair := expLoLoop_eq T u m 0 0 0
  unfold expStepLoSum
  change (Nat.sub (expLoLoop T u 0 m (expTermDn T u 0) (expTermUp T u 0) 0 0).1
    (expLoLoop T u 0 m (expTermDn T u 0) (expTermUp T u 0) 0 0).2 : ℝ) / T ≤ _
  rw [hpair]
  simp only [zero_add]
  set eSum := ∑ j ∈ Finset.range m, expTermDn T u (2 * j)
  set oSum := ∑ j ∈ Finset.range m, expTermUp T u (2 * j + 1)
  by_cases hle : oSum ≤ eSum
  · change ((eSum - oSum : ℕ) : ℝ) / T ≤ _
    rw [Nat.cast_sub hle, sub_div]
    have h1 : (eSum : ℝ) / T ≤
        ∑ j ∈ Finset.range m, ((u : ℝ) / T) ^ (2 * j) / ((2 * j).factorial : ℝ) := by
      dsimp only [eSum]
      rw [Nat.cast_sum, Finset.sum_div]
      exact Finset.sum_le_sum fun j _ => expTermDn_le hT (2 * j)
    have h2 : ∑ j ∈ Finset.range m, ((u : ℝ) / T) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) ≤
        (oSum : ℝ) / T := by
      dsimp only [oSum]
      rw [Nat.cast_sum, Finset.sum_div]
      exact Finset.sum_le_sum fun j _ => le_expTermUp hT (2 * j + 1)
    exact (sub_le_sub h1 h2).trans (exp_neg_ge_taylor m (by positivity))
  · have hzero : Nat.sub eSum oSum = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_le hle)
    rw [hzero, Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le

/-- Soundness of `expStepHiSum`: `Real.exp (-(u / T)) ≤ (expStepHiSum T u m : ℝ) / T`. -/
private theorem le_expStepHiSum {T u m : ℕ} (hT : 0 < T) :
    Real.exp (-((u : ℝ) / T)) ≤ (expStepHiSum T u m : ℝ) / T := by
  have hpair := expHiLoop_eq T u m 0 0 0
  unfold expStepHiSum
  change _ ≤ (Nat.sub (expHiLoop T u 0 m (expTermDn T u 0) (expTermUp T u 0) 0 0).1
    (expHiLoop T u 0 m (expTermDn T u 0) (expTermUp T u 0) 0 0).2 : ℝ) / T
  rw [hpair]
  simp only [zero_add]
  set eSum := ∑ j ∈ Finset.range (m + 1), expTermUp T u (2 * j)
  set oSum := ∑ j ∈ Finset.range m, expTermDn T u (2 * j + 1)
  have h1 : ∑ j ∈ Finset.range (m + 1), ((u : ℝ) / T) ^ (2 * j) / ((2 * j).factorial : ℝ) ≤
      (eSum : ℝ) / T := by
    dsimp only [eSum]
    rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun j _ => le_expTermUp hT (2 * j)
  have h2 : (oSum : ℝ) / T ≤
      ∑ j ∈ Finset.range m, ((u : ℝ) / T) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
    dsimp only [oSum]
    rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun j _ => expTermDn_le hT (2 * j + 1)
  have hdiff : Real.exp (-((u : ℝ) / T)) ≤ ((eSum : ℝ) - (oSum : ℝ)) / T := by
    rw [sub_div]
    exact (exp_neg_le_taylor m (by positivity)).trans (sub_le_sub h1 h2)
  refine hdiff.trans ?_
  have hTR : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  refine div_le_div_of_nonneg_right ?_ hTR
  by_cases hle : oSum ≤ eSum
  · change (eSum : ℝ) - oSum ≤ ((eSum - oSum : ℕ) : ℝ)
    rw [Nat.cast_sub hle]
  · have hlt : eSum < oSum := Nat.lt_of_not_le hle
    have : (eSum : ℝ) < oSum := Nat.cast_lt.mpr hlt
    linarith [Nat.cast_nonneg (α := ℝ) (Nat.sub eSum oSum)]

/-- Scale-`S` lower bound on `exp (-x)` via range reduction `x = 64 * (x / 64)` (`T = S * ratio`,
6 repeated squarings, `m` Taylor pairs). Requires `x ≤ 64 * (tHi / T)`. -/
private def expNeg64Dn (T ratio m tHi : ℕ) : ℕ :=
  Nat.div (fpSqIterDn T 6 (expStepLoSum T tHi m)) ratio

/-- Scale-`S` upper bound on `exp (-x)` via range reduction `x = 64 * (x / 64)`. Requires
`64 * (tLo / T) ≤ x`. -/
private def expNeg64Up (T ratio m tLo : ℕ) : ℕ :=
  Nat.div (Nat.add (fpSqIterUp T 6 (expStepHiSum T tLo m)) (Nat.sub ratio 1)) ratio

/-- Soundness of `expNeg64Dn` against `Real.exp (-x)`. -/
private theorem expNeg64Dn_le {S ratio m tHi : ℕ} (hS : 0 < S) (hr : 0 < ratio) {x : ℝ}
    (hx : x ≤ 64 * ((tHi : ℝ) / (S * ratio : ℕ))) :
    (expNeg64Dn (S * ratio) ratio m tHi : ℝ) / S ≤ Real.exp (-x) := by
  have hT : 0 < S * ratio := Nat.mul_pos hS hr
  have hdiv := natDiv_cast_le (a := fpSqIterDn (S * ratio) 6 (expStepLoSum (S * ratio) tHi m)) hr
  have hsq := fpSqIterDn_le hT 6 (expStepLoSum_le (T := S * ratio) (u := tHi) (m := m) hT)
  have hpow : (Real.exp (-((tHi : ℝ) / (S * ratio : ℕ)))) ^ (2 ^ 6) =
      Real.exp (-(64 * ((tHi : ℝ) / (S * ratio : ℕ)))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (expNeg64Dn (S * ratio) ratio m tHi : ℝ) / S
      ≤ (fpSqIterDn (S * ratio) 6 (expStepLoSum (S * ratio) tHi m) : ℝ) / (ratio : ℝ) / S := by
          exact div_le_div_of_nonneg_right hdiv (Nat.cast_nonneg S)
    _ = (fpSqIterDn (S * ratio) 6 (expStepLoSum (S * ratio) tHi m) : ℝ) / (S * ratio : ℕ) := by
          push_cast; ring
    _ ≤ (Real.exp (-((tHi : ℝ) / (S * ratio : ℕ)))) ^ (2 ^ 6) := hsq
    _ = Real.exp (-(64 * ((tHi : ℝ) / (S * ratio : ℕ)))) := hpow
    _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)

/-- Soundness of `expNeg64Up` against `Real.exp (-x)`. -/
private theorem le_expNeg64Up {S ratio m tLo : ℕ} (hS : 0 < S) (hr : 0 < ratio) {x : ℝ}
    (hx : 64 * ((tLo : ℝ) / (S * ratio : ℕ)) ≤ x) :
    Real.exp (-x) ≤ (expNeg64Up (S * ratio) ratio m tLo : ℝ) / S := by
  have hT : 0 < S * ratio := Nat.mul_pos hS hr
  have hdiv := le_natDivUp_cast
    (a := fpSqIterUp (S * ratio) 6 (expStepHiSum (S * ratio) tLo m)) hr
  have hsq := pow_le_fpSqIterUp hT 6 (Real.exp_pos _).le
    (le_expStepHiSum (T := S * ratio) (u := tLo) (m := m) hT)
  have hpow : (Real.exp (-((tLo : ℝ) / (S * ratio : ℕ)))) ^ (2 ^ 6) =
      Real.exp (-(64 * ((tLo : ℝ) / (S * ratio : ℕ)))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc Real.exp (-x)
      ≤ Real.exp (-(64 * ((tLo : ℝ) / (S * ratio : ℕ)))) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp (-((tLo : ℝ) / (S * ratio : ℕ)))) ^ (2 ^ 6) := hpow.symm
    _ ≤ (fpSqIterUp (S * ratio) 6 (expStepHiSum (S * ratio) tLo m) : ℝ) / (S * ratio : ℕ) := hsq
    _ = (fpSqIterUp (S * ratio) 6 (expStepHiSum (S * ratio) tLo m) : ℝ) / (ratio : ℝ) / S := by
          push_cast; ring
    _ ≤ (expNeg64Up (S * ratio) ratio m tLo : ℝ) / S :=
          div_le_div_of_nonneg_right hdiv (Nat.cast_nonneg S)

/-! #### Pure `Nat` polynomial homogeneous evaluation and Lipschitz bounds -/

open Polynomial in
/-- Real polynomial constructed from a list of natural coefficients `[c₀, c₁, ...]`. -/
private noncomputable def natListPoly (cs : List ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range cs.length, Polynomial.C (cs.getD j 0 : ℝ) * Polynomial.X ^ j

/-- Evaluate `∑_{j} cs[j] * p^j * D^(deg - j)` using Horner's method with pure `Nat` ops. -/
private def evalNatHomRev (p d : ℕ) : List ℕ → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | c :: rest, dPow, acc =>
      evalNatHomRev p d rest (Nat.mul dPow d) (Nat.add (Nat.mul acc p) (Nat.mul c dPow))

/-- Evaluation of `evalNatHomRev` starting from reversed coefficient list `[c_deg, ..., c_0]`. -/
private theorem evalNatHomRev_eq (p d : ℕ) (xs : List ℕ) (acc dp : ℕ) :
    (evalNatHomRev p d xs dp acc : ℝ) =
      (acc : ℝ) * (p : ℝ) ^ xs.length +
      (dp : ℝ) * ∑ j ∈ Finset.range xs.length,
        (xs.getD j 0 : ℝ) * (p : ℝ) ^ (xs.length - 1 - j) * (d : ℝ) ^ j := by
  induction xs generalizing acc dp with
  | nil => simp [evalNatHomRev]
  | cons c rest ih =>
      simp only [evalNatHomRev, List.length_cons]
      rw [ih (Nat.add (Nat.mul acc p) (Nat.mul c dp)) (Nat.mul dp d)]
      push_cast
      rw [Finset.sum_range_succ']
      have h0 : (c :: rest).getD 0 0 = c := rfl
      have hsucc : ∀ j : ℕ, (c :: rest).getD (j + 1) 0 = rest.getD j 0 := fun _ => rfl
      simp_rw [h0, hsucc]
      have hrest : ∑ j ∈ Finset.range rest.length,
          (rest.getD j 0 : ℝ) * (p : ℝ) ^ (rest.length - (j + 1)) * (d : ℝ) ^ (j + 1) =
          (d : ℝ) * ∑ j ∈ Finset.range rest.length,
            (rest.getD j 0 : ℝ) * (p : ℝ) ^ (rest.length - 1 - j) * (d : ℝ) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have heq : rest.length - (j + 1) = rest.length - 1 - j := by omega
        rw [heq, pow_succ]; ring
      rw [hrest, Nat.sub_zero, pow_zero, mul_one, pow_succ]
      change ((acc * p + c * dp : ℕ) : ℝ) * (p : ℝ) ^ rest.length +
        ((dp * d : ℕ) : ℝ) * _ = _
      push_cast; ring

/-- Wrapper `evalHom cs p d = ∑ j, cs[j] * p^j * d^(cs.length - 1 - j)`. -/
private def evalHom (cs : List ℕ) (p d : ℕ) : ℕ :=
  evalNatHomRev p d cs.reverse 1 0

/-- Exact relation between `evalHom cs p d` and `Polynomial.eval (p / d)` of `natListPoly cs`. -/
private theorem evalHom_eq {cs : List ℕ} (hne : cs ≠ []) (p : ℕ) {d : ℕ} (hd : 0 < d) :
    (evalHom cs p d : ℝ) =
      (d : ℝ) ^ (cs.length - 1) * (natListPoly cs).eval ((p : ℝ) / d) := by
  have hlen : 0 < cs.length := List.length_pos_of_ne_nil hne
  have hdR : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  unfold evalHom
  rw [evalNatHomRev_eq p d cs.reverse 0 1, List.length_reverse]
  simp only [Nat.cast_zero, zero_mul, Nat.cast_one, one_mul, zero_add]
  unfold natListPoly
  rw [eval_finset_sum_eq, Finset.mul_sum]
  conv_rhs =>
    arg 2; ext j
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← Finset.sum_range_reflect (fun j => (d : ℝ) ^ (cs.length - 1) *
    ((cs.getD j 0 : ℝ) * ((p : ℝ) / d) ^ j)) cs.length]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < cs.length := Finset.mem_range.mp hj
  have hget : cs.reverse.getD j 0 = cs.getD (cs.length - 1 - j) 0 := by
    have h1 : j < cs.reverse.length := by rwa [List.length_reverse]
    have h2 : cs.length - 1 - j < cs.length := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.getD_some, List.getElem_reverse]
  rw [hget, div_pow]
  have hpow : (d : ℝ) ^ (cs.length - 1) =
      (d : ℝ) ^ (cs.length - 1 - j) * (d : ℝ) ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]
  field_simp

/-- Oddness / evenness parity lemma for `legendreScaled N`. -/
private theorem legendreScaled_eval_neg (N : ℕ) (t : ℝ) :
    (legendreScaled N).eval (-t) = (-1 : ℝ) ^ N * (legendreScaled N).eval t := by
  unfold legendreScaled
  rw [eval_finset_sum_eq, eval_finset_sum_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : 2 * k ≤ N := by
    have := Finset.mem_range.mp hk; omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hneg : (-t) ^ (N - 2 * k) = (-1 : ℝ) ^ (N - 2 * k) * t ^ (N - 2 * k) := by
    rw [show -t = (-1) * t by ring, mul_pow]
  have hsign : (-1 : ℝ) ^ (N - 2 * k) = (-1 : ℝ) ^ N := by
    have : N = (N - 2 * k) + 2 * k := by omega
    conv_rhs => rw [this, pow_add, (even_two_mul k).neg_one_pow, mul_one]
  rw [hneg, hsign]
  ring

/-- Parity of `(legendreScaled N).derivative`: evaluating at `-t` flips by `(-1)^(N+1)`. -/
private theorem legendreScaled_deriv_eval_neg (N : ℕ) (t : ℝ) :
    (legendreScaled N).derivative.eval (-t) =
      (-1 : ℝ) ^ (N + 1) * (legendreScaled N).derivative.eval t := by
  have hd : HasDerivAt (fun x : ℝ => (legendreScaled N).eval (-x))
      (-((legendreScaled N).derivative.eval (-t))) t := by
    have h := ((legendreScaled N).hasDerivAt (-t)).comp t (hasDerivAt_id t).neg
    exact h.congr_deriv (by ring)
  have hd2 : HasDerivAt (fun x : ℝ => (-1 : ℝ) ^ N * (legendreScaled N).eval x)
      ((-1 : ℝ) ^ N * (legendreScaled N).derivative.eval t) t :=
    ((legendreScaled N).hasDerivAt t).const_mul _
  have heq : (fun x : ℝ => (legendreScaled N).eval (-x)) =
      fun x : ℝ => (-1 : ℝ) ^ N * (legendreScaled N).eval x :=
    funext (legendreScaled_eval_neg N)
  rw [heq] at hd
  have := hd.unique hd2
  rw [pow_succ]
  linarith

/-- Parity of `cauchyIntPoly (legendreScaled N)` at `-t`: flips by `(-1)^(N+1)`. -/
private theorem cauchyIntPoly_legendre_eval_neg (N : ℕ) (r : ℝ) :
    (cauchyIntPoly (legendreScaled N)).eval (-r) =
      (-1 : ℝ) ^ (N + 1) * (cauchyIntPoly (legendreScaled N)).eval r := by
  have hq : ∀ s : ℝ, (polyQuotAt (legendreScaled N) (-r)).eval (-s) =
      (-1 : ℝ) ^ (N + 1) * (polyQuotAt (legendreScaled N) r).eval s := by
    intro s
    by_cases hsr : s = r
    · subst hsr
      have hct : Continuous (fun u : ℝ => (polyQuotAt (legendreScaled N) (-s)).eval (-u) -
          (-1 : ℝ) ^ (N + 1) * (polyQuotAt (legendreScaled N) s).eval u) :=
        ((poly_continuous _).comp continuous_neg).sub (continuous_const.mul (poly_continuous _))
      have heq_ne : ∀ u : ℝ, u ≠ s →
          (polyQuotAt (legendreScaled N) (-s)).eval (-u) =
            (-1 : ℝ) ^ (N + 1) * (polyQuotAt (legendreScaled N) s).eval u := by
        intro u hu
        have h1 := congrArg (fun p : Polynomial ℝ => p.eval (-u))
          (polyQuotAt_mul_X_sub_C (legendreScaled N) (-s))
        have h2 := congrArg (fun p : Polynomial ℝ => p.eval u)
          (polyQuotAt_mul_X_sub_C (legendreScaled N) s)
        simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C, legendreScaled_eval_neg] at h1 h2
        have hne : u - s ≠ 0 := sub_ne_zero.mpr hu
        have h3 : (polyQuotAt (legendreScaled N) (-s)).eval (-u) * (-(u - s)) =
            (-1 : ℝ) ^ N * ((legendreScaled N).eval u - (legendreScaled N).eval s) := by
          linear_combination h1
        rw [← h2] at h3
        have h4 : ((polyQuotAt (legendreScaled N) (-s)).eval (-u) -
            (-1 : ℝ) ^ (N + 1) * (polyQuotAt (legendreScaled N) s).eval u) * (u - s) = 0 := by
          rw [pow_succ]; linear_combination -h3
        exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hne)
      have hlim : Filter.Tendsto (fun k : ℕ => s + 1 / (k + 1 : ℝ)) Filter.atTop (nhds s) := by
        have h0 : Filter.Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using tendsto_const_nhds.add h0
      have hzero : Filter.Tendsto
          (fun k : ℕ => (polyQuotAt (legendreScaled N) (-s)).eval (-(s + 1 / (k + 1 : ℝ))) -
            (-1 : ℝ) ^ (N + 1) * (polyQuotAt (legendreScaled N) s).eval (s + 1 / (k + 1 : ℝ)))
          Filter.atTop (nhds 0) := by
        refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => ?_)
        have hne : s + 1 / (k + 1 : ℝ) ≠ s := by
          have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
          linarith
        exact (sub_eq_zero.mpr (heq_ne _ hne)).symm
      exact sub_eq_zero.mp (tendsto_nhds_unique (hct.continuousAt.tendsto.comp hlim) hzero)
    · have h1 := congrArg (fun p : Polynomial ℝ => p.eval (-s))
        (polyQuotAt_mul_X_sub_C (legendreScaled N) (-r))
      have h2 := congrArg (fun p : Polynomial ℝ => p.eval s)
        (polyQuotAt_mul_X_sub_C (legendreScaled N) r)
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, legendreScaled_eval_neg] at h1 h2
      have hne : s - r ≠ 0 := sub_ne_zero.mpr hsr
      have h3 : (polyQuotAt (legendreScaled N) (-r)).eval (-s) * (-(s - r)) =
          (-1 : ℝ) ^ N * ((legendreScaled N).eval s - (legendreScaled N).eval r) := by
        linear_combination h1
      rw [← h2] at h3
      have h4 : ((polyQuotAt (legendreScaled N) (-r)).eval (-s) -
          (-1 : ℝ) ^ (N + 1) * (polyQuotAt (legendreScaled N) r).eval s) * (s - r) = 0 := by
        rw [pow_succ]; linear_combination -h3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hne)
  rw [cauchyIntPoly_eval, cauchyIntPoly_eval]
  have hcomp := intervalIntegral.integral_comp_neg
    (fun t => (polyQuotAt (legendreScaled N) (-r)).eval t) (a := (-1 : ℝ)) (b := 1)
  have hbound : ∫ t in (-1 : ℝ)..1, (polyQuotAt (legendreScaled N) (-r)).eval t =
      ∫ s in (-1 : ℝ)..1, (polyQuotAt (legendreScaled N) (-r)).eval (-s) := by
    simpa using hcomp.symm
  rw [hbound, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun s _ => hq s

/-- Trivial Lipschitz constant bound for a polynomial on `[-1, 1]` via the Mean Value Theorem. -/
private theorem abs_poly_eval_sub_le (p : Polynomial ℝ) (L : ℝ)
    (hL : ∑ j ∈ Finset.range (p.natDegree + 1), (j : ℝ) * |p.coeff j| ≤ L)
    {x y : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    |p.eval x - p.eval y| ≤ L * |x - y| := by
  have hd_bd : ∀ ξ ∈ Set.Icc (-1 : ℝ) 1, |p.derivative.eval ξ| ≤ L := by
    intro ξ hξ
    have hξ_le : |ξ| ≤ 1 := abs_le.mpr hξ
    have hsum : p.derivative = ∑ j ∈ Finset.range (p.natDegree + 1),
        (Polynomial.C (p.coeff j) * Polynomial.X ^ j).derivative := by
      conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
      rw [map_sum]
    rw [hsum, eval_finset_sum_eq]
    calc |∑ j ∈ Finset.range (p.natDegree + 1),
            (Polynomial.C (p.coeff j) * Polynomial.X ^ j).derivative.eval ξ|
        ≤ ∑ j ∈ Finset.range (p.natDegree + 1),
            |(Polynomial.C (p.coeff j) * Polynomial.X ^ j).derivative.eval ξ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (p.natDegree + 1), (j : ℝ) * |p.coeff j| := by
          refine Finset.sum_le_sum fun j _ => ?_
          cases j with
          | zero => simp
          | succ m =>
              rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
                Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
                Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
                Polynomial.eval_X, abs_mul, abs_mul,
                abs_of_nonneg (a := ((m + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _),
                abs_pow, Nat.add_sub_cancel]
              have hp : |ξ| ^ m ≤ 1 := pow_le_one₀ (abs_nonneg ξ) hξ_le
              calc |p.coeff (m + 1)| * (((m + 1 : ℕ) : ℝ) * |ξ| ^ m)
                  ≤ |p.coeff (m + 1)| * (((m + 1 : ℕ) : ℝ) * 1) := by gcongr
                _ = ((m + 1 : ℕ) : ℝ) * |p.coeff (m + 1)| := by ring
      _ ≤ L := hL
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => p.eval t)
      (fun t => p.derivative.eval t) hxy (poly_continuous p).continuousOn
      (fun t _ => p.hasDerivAt t)
    have hξ_mem : ξ ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1.trans hξ.1.le, hξ.2.le.trans hy.2⟩
    have heq : p.eval x - p.eval y = -(p.derivative.eval ξ * (y - x)) := by
      have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
      field_simp at hslope; linarith
    rw [heq, abs_neg, abs_mul, abs_of_pos (sub_pos.mpr hxy), abs_sub_comm x y,
      abs_of_pos (sub_pos.mpr hxy)]
    exact mul_le_mul_of_nonneg_right (hd_bd ξ hξ_mem) (sub_pos.mpr hxy).le
  · simp
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun t => p.eval t)
      (fun t => p.derivative.eval t) hyx (poly_continuous p).continuousOn
      (fun t _ => p.hasDerivAt t)
    have hξ_mem : ξ ∈ Set.Icc (-1 : ℝ) 1 := ⟨hy.1.trans hξ.1.le, hξ.2.le.trans hx.2⟩
    have heq : p.eval x - p.eval y = p.derivative.eval ξ * (x - y) := by
      have hne : x - y ≠ 0 := sub_ne_zero.mpr hyx.ne'
      field_simp at hslope; linarith
    rw [heq, abs_mul, abs_of_pos (sub_pos.mpr hyx)]
    exact mul_le_mul_of_nonneg_right (hd_bd ξ hξ_mem) (sub_pos.mpr hyx).le

/-! #### Fast list-based pure-`Nat` dot products and matrix step checkers -/

/-- Exact tail-recursive inner product `∑ a_i * b_i` over parallel `List ℕ`s. -/
private def dotNatAux : List ℕ → List ℕ → ℕ → ℕ
  | [], _, acc => acc
  | _, [], acc => acc
  | a :: as, b :: bs, acc => dotNatAux as bs (Nat.add acc (Nat.mul a b))

/-- Exact inner product `∑ a_i * b_i`. -/
private def dotNat (as bs : List ℕ) : ℕ := dotNatAux as bs 0

/-- Exact elementwise `List ℕ` accessor `getD` with default `0`. -/
private def vecAt (v : List ℕ) (i : ℕ) : ℕ := v.getD i 0

/-- Exact matrix entry accessor `matAt M a b = (M.getD a []).getD b 0`. -/
private def matAt (M : List (List ℕ)) (a b : ℕ) : ℕ := (M.getD a []).getD b 0

/-- Exact formula connecting `dotNatAux` to `Fin n` sums. -/
private theorem dotNatAux_eq (n : ℕ) (as bs : List ℕ) (ha : as.length = n) (hb : bs.length = n)
    (acc : ℕ) :
    dotNatAux as bs acc = acc + ∑ i : Fin n, as.getD i.1 0 * bs.getD i.1 0 := by
  induction n generalizing as bs acc with
  | zero =>
      cases as with
      | nil => simp [dotNatAux]
      | cons => simp at ha
  | succ n ih =>
      cases as with
      | nil => simp at ha
      | cons a as' =>
          cases bs with
          | nil => simp at hb
          | cons b bs' =>
              change dotNatAux as' bs' (acc + a * b) = _
              rw [ih as' bs' (by simpa using ha) (by simpa using hb) (acc + a * b),
                Fin.sum_univ_succ]
              have h0 : (a :: as').getD (0 : Fin (n + 1)).1 0 *
                  (b :: bs').getD (0 : Fin (n + 1)).1 0 = a * b := rfl
              rw [h0]
              have hrest : ∑ i : Fin n, (a :: as').getD i.succ.1 0 * (b :: bs').getD i.succ.1 0 =
                  ∑ i : Fin n, as'.getD i.1 0 * bs'.getD i.1 0 := rfl
              rw [hrest]
              omega

/-- Exact formula connecting `dotNat` to a `Fin n` sum. -/
private theorem dotNat_eq {n : ℕ} {as bs : List ℕ} (ha : as.length = n) (hb : bs.length = n) :
    dotNat as bs = ∑ i : Fin n, vecAt as i.1 * vecAt bs i.1 := by
  unfold dotNat vecAt
  simpa using dotNatAux_eq n as bs ha hb 0

/-- Tail-recursive list sum of natural numbers. -/
private def sumListNatAux : List ℕ → ℕ → ℕ
  | [], acc => acc
  | a :: as, acc => sumListNatAux as (Nat.add acc a)

/-- Sum of entries in a `List ℕ`. -/
private def sumListNat (as : List ℕ) : ℕ := sumListNatAux as 0

/-- Exact equivalence of `sumListNat` with `Fin n` sum. -/
private theorem sumListNat_eq {n : ℕ} {as : List ℕ} (ha : as.length = n) :
    sumListNat as = ∑ i : Fin n, vecAt as i.1 := by
  have haux : ∀ (m : ℕ) (xs : List ℕ), xs.length = m → ∀ acc : ℕ,
      sumListNatAux xs acc = acc + ∑ i : Fin m, vecAt xs i.1 := by
    intro m
    induction m with
    | zero =>
        intro xs hx acc
        cases xs with
        | nil => simp [sumListNatAux]
        | cons => simp at hx
    | succ m ih =>
        intro xs hx acc
        cases xs with
        | nil => simp at hx
        | cons a xs' =>
            change sumListNatAux xs' (acc + a) = _
            rw [ih xs' (by simpa using hx) (acc + a), Fin.sum_univ_succ]
            have h0 : vecAt (a :: xs') (0 : Fin (m + 1)).1 = a := rfl
            have hr : ∑ i : Fin m, vecAt (a :: xs') i.succ.1 = ∑ i : Fin m, vecAt xs' i.1 := rfl
            rw [h0, hr]; omega
  simpa [sumListNat] using haux n as ha 0

/-- Frobenius inner product `∑_{a, b} M[a][b] * R[a][b]` using `dotNat`. -/
private def frobDotNatAux : List (List ℕ) → List (List ℕ) → ℕ → ℕ
  | [], _, acc => acc
  | _, [], acc => acc
  | r1 :: rs1, r2 :: rs2, acc => frobDotNatAux rs1 rs2 (Nat.add acc (dotNat r1 r2))

/-- Frobenius inner product of two `n × n` `List (List ℕ)` matrices. -/
private def frobDotNat (M R : List (List ℕ)) : ℕ := frobDotNatAux M R 0

/-- Exact formula for `frobDotNat` on `n × n` matrices. -/
private theorem frobDotNat_eq {n : ℕ} {M R : List (List ℕ)}
    (hM : M.length = n) (hR : R.length = n)
    (hMr : ∀ r ∈ M, r.length = n) (hRr : ∀ r ∈ R, r.length = n) :
    frobDotNat M R = ∑ a : Fin n, ∑ b : Fin n, matAt M a.1 b.1 * matAt R a.1 b.1 := by
  have haux : ∀ (m : ℕ) (A B : List (List ℕ)), A.length = m → B.length = m →
      (∀ r ∈ A, r.length = n) → (∀ r ∈ B, r.length = n) → ∀ acc : ℕ,
      frobDotNatAux A B acc =
        acc + ∑ a : Fin m, ∑ b : Fin n, matAt A a.1 b.1 * matAt B a.1 b.1 := by
    intro m
    induction m with
    | zero =>
        intro A B hA _ _ _ acc
        cases A with
        | nil => simp [frobDotNatAux]
        | cons => simp at hA
    | succ m ih =>
        intro A B hA hB hAr hBr acc
        cases A with
        | nil => simp at hA
        | cons rA A' =>
            cases B with
            | nil => simp at hB
            | cons rB B' =>
                change frobDotNatAux A' B' (acc + dotNat rA rB) = _
                rw [ih A' B' (by simpa using hA) (by simpa using hB)
                  (fun r hr => hAr r (List.mem_cons_of_mem _ hr))
                  (fun r hr => hBr r (List.mem_cons_of_mem _ hr)),
                  dotNat_eq (hAr rA (List.mem_cons_self)) (hBr rB (List.mem_cons_self)),
                  Fin.sum_univ_succ]
                change acc + (∑ i : Fin n, vecAt rA i.1 * vecAt rB i.1) +
                    ∑ a : Fin m, ∑ b : Fin n, matAt A' a.1 b.1 * matAt B' a.1 b.1 =
                  acc + ((∑ b : Fin n, vecAt rA b.1 * vecAt rB b.1) +
                    ∑ a : Fin m, ∑ b : Fin n, matAt A' a.1 b.1 * matAt B' a.1 b.1)
                omega
  simpa [frobDotNat] using haux n M R hM hR hMr hRr 0

/-- Scale-`S` check of `v[i] ≤ fn i` on a `List ℕ` indexed with a pure recursive walk. -/
private theorem natBle_real_le {a b : ℕ} (h : Nat.ble a b = true) : (a : ℝ) ≤ (b : ℝ) :=
  Nat.cast_le.mpr (Nat.le_of_ble_eq_true h)

/-- Extract an `a`-th column `List ℕ` from a square matrix using `vecAt`. -/
private def getCol (M : List (List ℕ)) (b : ℕ) : List ℕ :=
  match M with
  | [] => []
  | row :: rest => vecAt row b :: getCol rest b

/-- Length and entries of `getCol M b`. -/
private theorem getCol_length (M : List (List ℕ)) (b : ℕ) : (getCol M b).length = M.length := by
  induction M with
  | nil => rfl
  | cons row rest ih => simp [getCol, ih]

/-- Entry characterization of `getCol M b`. -/
private theorem getCol_getD (M : List (List ℕ)) (a b : ℕ) :
    vecAt (getCol M b) a = matAt M a b := by
  induction M generalizing a with
  | nil => simp [getCol, vecAt, matAt]
  | cons row rest ih =>
      cases a with
      | zero => rfl
      | succ a' => exact ih a'

/-- Build the prescaled column vector `p_b[a] = M[a][b] * (eA_a[a] * eAB_ab[a][b])` rounded down. -/
private def buildPreColDn (s : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ
  | [], _, _ => []
  | m :: ms, e :: es, ab :: abs =>
      fpMulDn s m (fpMulDn s e ab) :: buildPreColDn s ms es abs
  | _, _, _ => []

/-- Build the prescaled column vector `p_b[a]` rounded up. -/
private def buildPreColUp (s : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ
  | [], _, _ => []
  | m :: ms, e :: es, ab :: abs =>
      fpMulUp s m (fpMulUp s e ab) :: buildPreColUp s ms es abs
  | _, _, _ => []

private theorem buildPreColDn_spec {s n : ℕ} (mCol eA abCol : List ℕ)
    (hm : mCol.length = n) (he : eA.length = n) (hab : abCol.length = n) :
    (buildPreColDn s mCol eA abCol).length = n ∧
      ∀ a : Fin n, vecAt (buildPreColDn s mCol eA abCol) a.1 =
        fpMulDn s (vecAt mCol a.1) (fpMulDn s (vecAt eA a.1) (vecAt abCol a.1)) := by
  induction n generalizing mCol eA abCol with
  | zero =>
      cases mCol with
      | nil => exact ⟨rfl, fun a => a.elim0⟩
      | cons => simp at hm
  | succ n ih =>
      cases mCol with
      | nil => simp at hm
      | cons m ms =>
          cases eA with
          | nil => simp at he
          | cons e es =>
              cases abCol with
              | nil => simp at hab
              | cons ab abs =>
                  obtain ⟨hl, hg⟩ := ih ms es abs (by simpa using hm) (by simpa using he)
                    (by simpa using hab)
                  refine ⟨by simp [buildPreColDn, hl], fun a => ?_⟩
                  refine Fin.cases rfl (fun j => hg j) a

private theorem buildPreColUp_spec {s n : ℕ} (mCol eA abCol : List ℕ)
    (hm : mCol.length = n) (he : eA.length = n) (hab : abCol.length = n) :
    (buildPreColUp s mCol eA abCol).length = n ∧
      ∀ a : Fin n, vecAt (buildPreColUp s mCol eA abCol) a.1 =
        fpMulUp s (vecAt mCol a.1) (fpMulUp s (vecAt eA a.1) (vecAt abCol a.1)) := by
  induction n generalizing mCol eA abCol with
  | zero =>
      cases mCol with
      | nil => exact ⟨rfl, fun a => a.elim0⟩
      | cons => simp at hm
  | succ n ih =>
      cases mCol with
      | nil => simp at hm
      | cons m ms =>
          cases eA with
          | nil => simp at he
          | cons e es =>
              cases abCol with
              | nil => simp at hab
              | cons ab abs =>
                  obtain ⟨hl, hg⟩ := ih ms es abs (by simpa using hm) (by simpa using he)
                    (by simpa using hab)
                  refine ⟨by simp [buildPreColUp, hl], fun a => ?_⟩
                  refine Fin.cases rfl (fun j => hg j) a

/-- Check one row `outRow` (`c = 0..n-1`) of `ar2StepMat` from BELOW against a pre-transposed
list of columns `eAC_cols` (`eAC_cols[c][a] = eAC[a][c]`). -/
private def checkStepRowDn (s k2 : ℕ) (eb8 : ℕ) (preCol : List ℕ) :
    List ℕ → List ℕ → List ℕ → List (List ℕ) → List ℕ → Bool
  | [], _, _, _, _ => true
  | o :: os, wc :: wcs, ec :: ecs, acCol :: acCols, bc :: bcs =>
      let dotS := Nat.div (dotNat preCol acCol) s
      let pref := fpMulDn s (fpMulDn s k2 wc)
        (fpMulDn s eb8 (fpMulDn s (fpPowDn s ec 4) (fpMulDn s bc bc)))
      let rhs := fpMulDn s pref dotS
      if Nat.ble o rhs then checkStepRowDn s k2 eb8 preCol os wcs ecs acCols bcs else false
  | _, _, _, _, _ => false

/-- Check one row `outRow` (`c = 0..n-1`) of `ar2StepMat` from ABOVE. -/
private def checkStepRowUp (s k2 : ℕ) (eb8 : ℕ) (preCol : List ℕ) :
    List ℕ → List ℕ → List ℕ → List (List ℕ) → List ℕ → Bool
  | [], _, _, _, _ => true
  | o :: os, wc :: wcs, ec :: ecs, acCol :: acCols, bc :: bcs =>
      let dotS := Nat.div (Nat.add (dotNat preCol acCol) (Nat.sub s 1)) s
      let pref := fpMulUp s (fpMulUp s k2 wc)
        (fpMulUp s eb8 (fpMulUp s (fpPowUp s ec 4) (fpMulUp s bc bc)))
      let lhs := fpMulUp s pref dotS
      if Nat.ble lhs o then checkStepRowUp s k2 eb8 preCol os wcs ecs acCols bcs else false
  | _, _, _, _, _ => false

/-- Check a single transition row `b` of `outMat` from below. -/
private def checkStepAtDn (s k2 : ℕ) (mIn eAB_ab eAB_bc eAC_cols : List (List ℕ))
    (eA_a eA_b wc eA_c : List ℕ) (outRow : List ℕ) (b : ℕ) : Bool :=
  let preCol := buildPreColDn s (getCol mIn b) eA_a (getCol eAB_ab b)
  let eb8 := fpPowDn s (vecAt eA_b b) 8
  checkStepRowDn s k2 eb8 preCol outRow wc eA_c eAC_cols (eAB_bc.getD b [])

/-- Check a single transition row `b` of `outMat` from above. -/
private def checkStepAtUp (s k2 : ℕ) (mIn eAB_ab eAB_bc eAC_cols : List (List ℕ))
    (eA_a eA_b wc eA_c : List ℕ) (outRow : List ℕ) (b : ℕ) : Bool :=
  let preCol := buildPreColUp s (getCol mIn b) eA_a (getCol eAB_ab b)
  let eb8 := fpPowUp s (vecAt eA_b b) 8
  checkStepRowUp s k2 eb8 preCol outRow wc eA_c eAC_cols (eAB_bc.getD b [])

/-- Check all rows `b = start .. start + rem - 1` of `outMat` from below. -/
private def checkStepRowsDn (s k2 : ℕ) (mIn eAB_ab eAB_bc eAC_cols : List (List ℕ))
    (eA_a eA_b wc eA_c : List ℕ) (outMat : List (List ℕ)) : ℕ → ℕ → Bool
  | _, 0 => true
  | b, rem + 1 =>
      if checkStepAtDn s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c (outMat.getD b []) b
      then checkStepRowsDn s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c outMat
        (Nat.add b 1) rem
      else false

/-- Check all rows `b = start .. start + rem - 1` of `outMat` from above. -/
private def checkStepRowsUp (s k2 : ℕ) (mIn eAB_ab eAB_bc eAC_cols : List (List ℕ))
    (eA_a eA_b wc eA_c : List ℕ) (outMat : List (List ℕ)) : ℕ → ℕ → Bool
  | _, 0 => true
  | b, rem + 1 =>
      if checkStepAtUp s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c (outMat.getD b []) b
      then checkStepRowsUp s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c outMat
        (Nat.add b 1) rem
      else false

/-- Soundness of `checkStepRowDn`: entry `c` satisfies the lower bound formula. -/
private theorem checkStepRowDn_spec {s k2 eb8 m : ℕ} {preCol : List ℕ}
    {os wcs ecs bcs : List ℕ} {acCols : List (List ℕ)}
    (ho : os.length = m) (hw : wcs.length = m) (he : ecs.length = m)
    (hac : acCols.length = m) (hbc : bcs.length = m)
    (hchk : checkStepRowDn s k2 eb8 preCol os wcs ecs acCols bcs = true) (c : Fin m) :
    vecAt os c.1 ≤ fpMulDn s
      (fpMulDn s (fpMulDn s k2 (vecAt wcs c.1))
        (fpMulDn s eb8 (fpMulDn s (fpPowDn s (vecAt ecs c.1) 4)
          (fpMulDn s (vecAt bcs c.1) (vecAt bcs c.1)))))
      (Nat.div (dotNat preCol (acCols.getD c.1 [])) s) := by
  induction m generalizing os wcs ecs acCols bcs with
  | zero => exact c.elim0
  | succ m ih =>
      cases os with | nil => simp at ho | cons o os' =>
      cases wcs with | nil => simp at hw | cons w wcs' =>
      cases ecs with | nil => simp at he | cons e ecs' =>
      cases acCols with | nil => simp at hac | cons ac acCols' =>
      cases bcs with | nil => simp at hbc | cons bc bcs' =>
      simp only [checkStepRowDn] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases ?_ (fun j => ih (by simpa using ho) (by simpa using hw)
          (by simpa using he) (by simpa using hac) (by simpa using hbc) hchk j) c
        exact Nat.le_of_ble_eq_true hble
      · simp at hchk

/-- Soundness of `checkStepRowUp`: entry `c` satisfies the upper bound formula. -/
private theorem checkStepRowUp_spec {s k2 eb8 m : ℕ} {preCol : List ℕ}
    {os wcs ecs bcs : List ℕ} {acCols : List (List ℕ)}
    (ho : os.length = m) (hw : wcs.length = m) (he : ecs.length = m)
    (hac : acCols.length = m) (hbc : bcs.length = m)
    (hchk : checkStepRowUp s k2 eb8 preCol os wcs ecs acCols bcs = true) (c : Fin m) :
    fpMulUp s
      (fpMulUp s (fpMulUp s k2 (vecAt wcs c.1))
        (fpMulUp s eb8 (fpMulUp s (fpPowUp s (vecAt ecs c.1) 4)
          (fpMulUp s (vecAt bcs c.1) (vecAt bcs c.1)))))
      (Nat.div (Nat.add (dotNat preCol (acCols.getD c.1 [])) (Nat.sub s 1)) s) ≤
      vecAt os c.1 := by
  induction m generalizing os wcs ecs acCols bcs with
  | zero => exact c.elim0
  | succ m ih =>
      cases os with | nil => simp at ho | cons o os' =>
      cases wcs with | nil => simp at hw | cons w wcs' =>
      cases ecs with | nil => simp at he | cons e ecs' =>
      cases acCols with | nil => simp at hac | cons ac acCols' =>
      cases bcs with | nil => simp at hbc | cons bc bcs' =>
      simp only [checkStepRowUp] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases ?_ (fun j => ih (by simpa using ho) (by simpa using hw)
          (by simpa using he) (by simpa using hac) (by simpa using hbc) hchk j) c
        exact Nat.le_of_ble_eq_true hble
      · simp at hchk

/-- Indexing lemma for `checkStepRowsDn`. -/
private theorem checkStepRowsDn_get {s k2 : ℕ} {mIn eAB_ab eAB_bc eAC_cols : List (List ℕ)}
    {eA_a eA_b wc eA_c : List ℕ} {outMat : List (List ℕ)} {start rem : ℕ}
    (hchk : checkStepRowsDn s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c outMat
      start rem = true) {b : ℕ} (hb1 : start ≤ b) (hb2 : b < start + rem) :
    checkStepAtDn s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c (outMat.getD b []) b =
      true := by
  induction rem generalizing start with
  | zero => omega
  | succ rem ih =>
      simp only [checkStepRowsDn] at hchk
      split at hchk
      · rename_i hcur
        by_cases hbeq : b = start
        · subst hbeq; exact hcur
        · exact ih (start := start + 1) hchk (by omega) (by omega)
      · simp at hchk

/-- Indexing lemma for `checkStepRowsUp`. -/
private theorem checkStepRowsUp_get {s k2 : ℕ} {mIn eAB_ab eAB_bc eAC_cols : List (List ℕ)}
    {eA_a eA_b wc eA_c : List ℕ} {outMat : List (List ℕ)} {start rem : ℕ}
    (hchk : checkStepRowsUp s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c outMat
      start rem = true) {b : ℕ} (hb1 : start ≤ b) (hb2 : b < start + rem) :
    checkStepAtUp s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c (outMat.getD b []) b =
      true := by
  induction rem generalizing start with
  | zero => omega
  | succ rem ih =>
      simp only [checkStepRowsUp] at hchk
      split at hchk
      · rename_i hcur
        by_cases hbeq : b = start
        · subst hbeq; exact hcur
        · exact ih (start := start + 1) hchk (by omega) (by omega)
      · simp at hchk

/-- Full real-number soundness of `checkStepAtDn` for `ar2StepMat`. -/
private theorem checkStepAtDn_sound {n s k2 : ℕ} (hs : 0 < s)
    {xa xb xc wc_r : Fin n → ℝ} {M : Fin n → Fin n → ℝ}
    {mIn eAB_ab eAB_bc eAC_cols : List (List ℕ)}
    {eA_a eA_b wc eA_c : List ℕ} {outRow : List ℕ} (b : Fin n)
    (hmLen : mIn.length = n) (habLen : eAB_ab.length = n)
    (heAaLen : eA_a.length = n) (houtLen : outRow.length = n)
    (hwLen : wc.length = n) (heAcLen : eA_c.length = n)
    (hbcLen : (eAB_bc.getD b.1 []).length = n)
    (hacLen : eAC_cols.length = n) (hacCols : ∀ c : Fin n, (eAC_cols.getD c.1 []).length = n)
    (hk2 : (k2 : ℝ) / s ≤ 2 * Real.sqrt (6 / Real.pi))
    (hM : ∀ a : Fin n, (matAt mIn a.1 b.1 : ℝ) / s ≤ M a b)
    (heAa : ∀ a : Fin n, (vecAt eA_a a.1 : ℝ) / s ≤ eAFactor (xa a))
    (heAb : (vecAt eA_b b.1 : ℝ) / s ≤ eAFactor (xb b))
    (heAc : ∀ c : Fin n, (vecAt eA_c c.1 : ℝ) / s ≤ eAFactor (xc c))
    (hw : ∀ c : Fin n, (vecAt wc c.1 : ℝ) / s ≤ wc_r c)
    (hab : ∀ a : Fin n, (matAt eAB_ab a.1 b.1 : ℝ) / s ≤ eABFactor (xa a) (xb b))
    (hbc : ∀ c : Fin n, (matAt eAB_bc b.1 c.1 : ℝ) / s ≤ eABFactor (xb b) (xc c))
    (hac : ∀ a c : Fin n, (vecAt (eAC_cols.getD c.1 []) a.1 : ℝ) / s ≤
      eACFactor (xa a) (xc c))
    (hchk : checkStepAtDn s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c outRow b.1 = true) :
    ∀ c : Fin n, (vecAt outRow c.1 : ℝ) / s ≤ ar2StepMat xa xb xc wc_r M b c := by
  intro c
  have hpre := buildPreColDn_spec (s := s) (n := n) (getCol mIn b.1) eA_a (getCol eAB_ab b.1)
    (by rw [getCol_length, hmLen]) heAaLen (by rw [getCol_length, habLen])
  have hle_nat := checkStepRowDn_spec houtLen hwLen heAcLen hacLen hbcLen hchk c
  have hle_r : (vecAt outRow c.1 : ℝ) / s ≤
      (fpMulDn s (fpMulDn s (fpMulDn s k2 (vecAt wc c.1))
        (fpMulDn s (fpPowDn s (vecAt eA_b b.1) 8)
          (fpMulDn s (fpPowDn s (vecAt eA_c c.1) 4)
            (fpMulDn s (vecAt (eAB_bc.getD b.1 []) c.1) (vecAt (eAB_bc.getD b.1 []) c.1)))))
        (Nat.div (dotNat (buildPreColDn s (getCol mIn b.1) eA_a (getCol eAB_ab b.1))
          (eAC_cols.getD c.1 [])) s) : ℝ) / s :=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hle_nat) (Nat.cast_nonneg s)
  rw [ar2StepMat_eq_factor]
  refine hle_r.trans (fpMulDn_le_mul hs ?_ ?_)
  · refine fpMulDn_le_mul hs (fpMulDn_le_mul hs hk2 (hw c)) ?_
    refine fpMulDn_le_mul hs (fpPowDn_le hs heAb) ?_
    refine fpMulDn_le_mul hs (fpPowDn_le hs (heAc c)) ?_
    rw [sq]; exact fpMulDn_le_mul hs (hbc c) (hbc c)
  · have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
    have hdot := dotNat_eq hpre.1 (hacCols c)
    have hd_le := natDiv_cast_le (a := dotNat (buildPreColDn s (getCol mIn b.1) eA_a
      (getCol eAB_ab b.1)) (eAC_cols.getD c.1 [])) hs
    calc (Nat.div (dotNat (buildPreColDn s (getCol mIn b.1) eA_a (getCol eAB_ab b.1))
            (eAC_cols.getD c.1 [])) s : ℝ) / s
        ≤ ((dotNat (buildPreColDn s (getCol mIn b.1) eA_a (getCol eAB_ab b.1))
            (eAC_cols.getD c.1 []) : ℕ) : ℝ) / s / s :=
            div_le_div_of_nonneg_right hd_le hsR.le
      _ = ∑ a : Fin n, ((vecAt (buildPreColDn s (getCol mIn b.1) eA_a
              (getCol eAB_ab b.1)) a.1 : ℝ) / s) *
            ((vecAt (eAC_cols.getD c.1 []) a.1 : ℝ) / s) := by
            rw [hdot, Nat.cast_sum, Finset.sum_div, Finset.sum_div]
            refine Finset.sum_congr rfl fun a _ => by push_cast; ring
      _ ≤ ∑ a : Fin n, (M a b * (eAFactor (xa a) * eABFactor (xa a) (xb b))) *
            eACFactor (xa a) (xc c) := by
            refine Finset.sum_le_sum fun a _ => ?_
            have hpa : (vecAt (buildPreColDn s (getCol mIn b.1) eA_a
                (getCol eAB_ab b.1)) a.1 : ℝ) / s ≤
                M a b * (eAFactor (xa a) * eABFactor (xa a) (xb b)) := by
              rw [hpre.2 a, getCol_getD, getCol_getD]
              exact fpMulDn_le_mul hs (hM a) (fpMulDn_le_mul hs (heAa a) (hab a))
            exact mul_le_mul hpa (hac a c) (by positivity)
              ((by positivity : (0 : ℝ) ≤ _).trans hpa)

/-- Full real-number soundness of `checkStepAtUp` for `ar2StepMat`. -/
private theorem checkStepAtUp_sound {n s k2 : ℕ} (hs : 0 < s)
    {xa xb xc wc_r : Fin n → ℝ} {M : Fin n → Fin n → ℝ}
    {mIn eAB_ab eAB_bc eAC_cols : List (List ℕ)}
    {eA_a eA_b wc eA_c : List ℕ} {outRow : List ℕ} (b : Fin n)
    (hmLen : mIn.length = n) (habLen : eAB_ab.length = n)
    (heAaLen : eA_a.length = n) (houtLen : outRow.length = n)
    (hwLen : wc.length = n) (heAcLen : eA_c.length = n)
    (hbcLen : (eAB_bc.getD b.1 []).length = n)
    (hacLen : eAC_cols.length = n) (hacCols : ∀ c : Fin n, (eAC_cols.getD c.1 []).length = n)
    (hM0 : ∀ a : Fin n, 0 ≤ M a b) (hw0 : ∀ c : Fin n, 0 ≤ wc_r c)
    (hk2 : 2 * Real.sqrt (6 / Real.pi) ≤ (k2 : ℝ) / s)
    (hM : ∀ a : Fin n, M a b ≤ (matAt mIn a.1 b.1 : ℝ) / s)
    (heAa : ∀ a : Fin n, eAFactor (xa a) ≤ (vecAt eA_a a.1 : ℝ) / s)
    (heAb : eAFactor (xb b) ≤ (vecAt eA_b b.1 : ℝ) / s)
    (heAc : ∀ c : Fin n, eAFactor (xc c) ≤ (vecAt eA_c c.1 : ℝ) / s)
    (hw : ∀ c : Fin n, wc_r c ≤ (vecAt wc c.1 : ℝ) / s)
    (hab : ∀ a : Fin n, eABFactor (xa a) (xb b) ≤ (matAt eAB_ab a.1 b.1 : ℝ) / s)
    (hbc : ∀ c : Fin n, eABFactor (xb b) (xc c) ≤ (matAt eAB_bc b.1 c.1 : ℝ) / s)
    (hac : ∀ a c : Fin n, eACFactor (xa a) (xc c) ≤
      (vecAt (eAC_cols.getD c.1 []) a.1 : ℝ) / s)
    (hchk : checkStepAtUp s k2 mIn eAB_ab eAB_bc eAC_cols eA_a eA_b wc eA_c outRow b.1 = true) :
    ∀ c : Fin n, ar2StepMat xa xb xc wc_r M b c ≤ (vecAt outRow c.1 : ℝ) / s := by
  intro c
  have hpre := buildPreColUp_spec (s := s) (n := n) (getCol mIn b.1) eA_a (getCol eAB_ab b.1)
    (by rw [getCol_length, hmLen]) heAaLen (by rw [getCol_length, habLen])
  have hle_nat := checkStepRowUp_spec houtLen hwLen heAcLen hacLen hbcLen hchk c
  have heAF_nn : ∀ t : ℝ, 0 ≤ eAFactor t := fun _ => (Real.exp_pos _).le
  have heAB_nn : ∀ x y : ℝ, 0 ≤ eABFactor x y := fun _ _ => (Real.exp_pos _).le
  have heAC_nn : ∀ x z : ℝ, 0 ≤ eACFactor x z := fun _ _ => (Real.exp_pos _).le
  have hdot_le : ∑ a : Fin n, (M a b * (eAFactor (xa a) * eABFactor (xa a) (xb b))) *
        eACFactor (xa a) (xc c) ≤
      (Nat.div (Nat.add (dotNat (buildPreColUp s (getCol mIn b.1) eA_a (getCol eAB_ab b.1))
        (eAC_cols.getD c.1 [])) (Nat.sub s 1)) s : ℝ) / s := by
    have hdot := dotNat_eq hpre.1 (hacCols c)
    have hup := le_natDivUp_cast (a := dotNat (buildPreColUp s (getCol mIn b.1) eA_a
      (getCol eAB_ab b.1)) (eAC_cols.getD c.1 [])) hs
    calc ∑ a : Fin n, (M a b * (eAFactor (xa a) * eABFactor (xa a) (xb b))) *
            eACFactor (xa a) (xc c)
        ≤ ∑ a : Fin n, ((vecAt (buildPreColUp s (getCol mIn b.1) eA_a
              (getCol eAB_ab b.1)) a.1 : ℝ) / s) *
            ((vecAt (eAC_cols.getD c.1 []) a.1 : ℝ) / s) := by
            refine Finset.sum_le_sum fun a _ => ?_
            have hpa : M a b * (eAFactor (xa a) * eABFactor (xa a) (xb b)) ≤
                (vecAt (buildPreColUp s (getCol mIn b.1) eA_a
                  (getCol eAB_ab b.1)) a.1 : ℝ) / s := by
              rw [hpre.2 a, getCol_getD, getCol_getD]
              exact mul_le_fpMulUp hs (hM0 a)
                (mul_nonneg (heAF_nn _) (heAB_nn _ _)) (hM a)
                (mul_le_fpMulUp hs (heAF_nn _) (heAB_nn _ _) (heAa a) (hab a))
            exact mul_le_mul hpa (hac a c) (heAC_nn _ _)
              ((mul_nonneg (hM0 a) (mul_nonneg (heAF_nn _) (heAB_nn _ _))).trans hpa)
      _ = ((dotNat (buildPreColUp s (getCol mIn b.1) eA_a (getCol eAB_ab b.1))
            (eAC_cols.getD c.1 []) : ℕ) : ℝ) / s / s := by
            rw [hdot, Nat.cast_sum, Finset.sum_div, Finset.sum_div]
            refine Finset.sum_congr rfl fun a _ => by push_cast; ring
      _ ≤ (Nat.div (Nat.add (dotNat (buildPreColUp s (getCol mIn b.1) eA_a
            (getCol eAB_ab b.1)) (eAC_cols.getD c.1 [])) (Nat.sub s 1)) s : ℝ) / s :=
            div_le_div_of_nonneg_right hup (Nat.cast_nonneg s)
  have hsum_nn : 0 ≤ ∑ a : Fin n, (M a b * (eAFactor (xa a) * eABFactor (xa a) (xb b))) *
      eACFactor (xa a) (xc c) :=
    Finset.sum_nonneg fun a _ =>
      mul_nonneg (mul_nonneg (hM0 a) (mul_nonneg (heAF_nn _) (heAB_nn _ _))) (heAC_nn _ _)
  have hpref_nn : 0 ≤ (2 * Real.sqrt (6 / Real.pi) * wc_r c) *
      (eAFactor (xb b) ^ 8 * (eAFactor (xc c) ^ 4 * eABFactor (xb b) (xc c) ^ 2)) :=
    mul_nonneg (mul_nonneg (by positivity) (hw0 c))
      (mul_nonneg (pow_nonneg (heAF_nn _) _)
        (mul_nonneg (pow_nonneg (heAF_nn _) _) (sq_nonneg _)))
  rw [ar2StepMat_eq_factor]
  refine (mul_le_fpMulUp hs hpref_nn hsum_nn ?_ hdot_le).trans
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr hle_nat) (Nat.cast_nonneg s))
  refine mul_le_fpMulUp hs (mul_nonneg (by positivity) (hw0 c))
    (mul_nonneg (pow_nonneg (heAF_nn _) _)
      (mul_nonneg (pow_nonneg (heAF_nn _) _) (sq_nonneg _)))
    (mul_le_fpMulUp hs (by positivity) (hw0 c) hk2 (hw c)) ?_
  refine mul_le_fpMulUp hs (pow_nonneg (heAF_nn _) _)
    (mul_nonneg (pow_nonneg (heAF_nn _) _) (sq_nonneg _))
    (pow_le_fpPowUp hs (heAF_nn _) heAb) ?_
  refine mul_le_fpMulUp hs (pow_nonneg (heAF_nn _) _) (sq_nonneg _)
    (pow_le_fpPowUp hs (heAF_nn _) (heAc c)) ?_
  rw [sq]; exact mul_le_fpMulUp hs (heAB_nn _ _) (heAB_nn _ _) (hbc c) (hbc c)

/-- Nonnegativity of `ar2InitMat`, `ar2StepMat`, and `ar2PrefixMat`. -/
private theorem ar2InitMat_nonneg {N : ℕ} {L_end L_int : ℝ} (hLe : 0 ≤ L_end) (hLi : 0 ≤ L_int)
    {r : Fin N → ℝ} (hw : ∀ k, 0 ≤ gaussWeight r k) (a b : Fin N) :
    0 ≤ ar2InitMat L_end L_int r a b := by
  unfold ar2InitMat shiftWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (hw a))
    (mul_nonneg (by linarith) (hw b))) (ar2InitDensity_nonneg _ _)

private theorem ar2StepMat_nonneg {N : ℕ} {xa xb xc wc : Fin N → ℝ}
    {M : Fin N → Fin N → ℝ} (hw : ∀ c, 0 ≤ wc c) (hM : ∀ a b, 0 ≤ M a b) (b c : Fin N) :
    0 ≤ ar2StepMat xa xb xc wc M b c := by
  unfold ar2StepMat
  exact mul_nonneg (mul_nonneg (by norm_num) (hw c))
    (Finset.sum_nonneg fun a _ => mul_nonneg (hM a b) (ar2Kernel_nonneg _ _ _))

private theorem ar2PrefixMat_nonneg {N : ℕ} {L_end L_int : ℝ} (hLe : 0 ≤ L_end) (hLi : 0 ≤ L_int)
    {r : Fin N → ℝ} (hw : ∀ k, 0 ≤ gaussWeight r k) (m : ℕ) (a b : Fin N) :
    0 ≤ ar2PrefixMat L_end L_int r m a b := by
  have hwI : ∀ k, 0 ≤ shiftWeight L_int r k := fun k => mul_nonneg (by linarith) (hw k)
  induction m generalizing a b with
  | zero => exact ar2StepMat_nonneg hwI (ar2InitMat_nonneg hLe hLi hw) a b
  | succ m ih => exact ar2StepMat_nonneg hwI ih a b

private theorem ar2ReadoutMat_nonneg {N : ℕ} {L_end L_int : ℝ} (hLe : 0 ≤ L_end)
    {r : Fin N → ℝ} (hw : ∀ k, 0 ≤ gaussWeight r k) (a b : Fin N) :
    0 ≤ ar2ReadoutMat L_end L_int r a b := by
  unfold ar2ReadoutMat shiftWeight
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun c _ =>
      mul_nonneg (mul_nonneg (by linarith) (hw c)) (ar2Kernel_nonneg _ _ _))

/-- Sum-inner-product checker for one readout entry `R[a, b]`. -/
private def buildReadoutVecDn (s : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ
  | [], _, _ => []
  | w :: ws, ec :: ecs, bc :: bcs =>
      fpMulDn s w (fpMulDn s (fpPowDn s ec 4) (fpMulDn s bc bc)) ::
        buildReadoutVecDn s ws ecs bcs
  | _, _, _ => []

private def buildReadoutVecUp (s : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ
  | [], _, _ => []
  | w :: ws, ec :: ecs, bc :: bcs =>
      fpMulUp s w (fpMulUp s (fpPowUp s ec 4) (fpMulUp s bc bc)) ::
        buildReadoutVecUp s ws ecs bcs
  | _, _, _ => []

private theorem buildReadoutVecDn_spec {s n : ℕ} (wc eAc bcRow : List ℕ)
    (hw : wc.length = n) (he : eAc.length = n) (hbc : bcRow.length = n) :
    (buildReadoutVecDn s wc eAc bcRow).length = n ∧
      ∀ c : Fin n, vecAt (buildReadoutVecDn s wc eAc bcRow) c.1 =
        fpMulDn s (vecAt wc c.1) (fpMulDn s (fpPowDn s (vecAt eAc c.1) 4)
          (fpMulDn s (vecAt bcRow c.1) (vecAt bcRow c.1))) := by
  induction n generalizing wc eAc bcRow with
  | zero =>
      cases wc with | nil => exact ⟨rfl, fun c => c.elim0⟩ | cons => simp at hw
  | succ n ih =>
      cases wc with | nil => simp at hw | cons w ws =>
      cases eAc with | nil => simp at he | cons e es =>
      cases bcRow with | nil => simp at hbc | cons bc bcs =>
      obtain ⟨hl, hg⟩ := ih ws es bcs (by simpa using hw) (by simpa using he)
        (by simpa using hbc)
      exact ⟨by simp [buildReadoutVecDn, hl], fun c => Fin.cases rfl (fun j => hg j) c⟩

private theorem buildReadoutVecUp_spec {s n : ℕ} (wc eAc bcRow : List ℕ)
    (hw : wc.length = n) (he : eAc.length = n) (hbc : bcRow.length = n) :
    (buildReadoutVecUp s wc eAc bcRow).length = n ∧
      ∀ c : Fin n, vecAt (buildReadoutVecUp s wc eAc bcRow) c.1 =
        fpMulUp s (vecAt wc c.1) (fpMulUp s (fpPowUp s (vecAt eAc c.1) 4)
          (fpMulUp s (vecAt bcRow c.1) (vecAt bcRow c.1))) := by
  induction n generalizing wc eAc bcRow with
  | zero =>
      cases wc with | nil => exact ⟨rfl, fun c => c.elim0⟩ | cons => simp at hw
  | succ n ih =>
      cases wc with | nil => simp at hw | cons w ws =>
      cases eAc with | nil => simp at he | cons e es =>
      cases bcRow with | nil => simp at hbc | cons bc bcs =>
      obtain ⟨hl, hg⟩ := ih ws es bcs (by simpa using hw) (by simpa using he)
        (by simpa using hbc)
      exact ⟨by simp [buildReadoutVecUp, hl], fun c => Fin.cases rfl (fun j => hg j) c⟩

/-- Readout matrix checker from below (`R[a, b]`). -/
private def checkReadoutRowDn (s k2 ea : ℕ) (acRow : List ℕ) :
    List ℕ → List ℕ → List ℕ → List (List ℕ) → Bool
  | [], _, _, _ => true
  | r :: rs, eb :: ebs, ab :: abs, rVec :: rVecs =>
      let dotS := Nat.div (dotNat rVec acRow) s
      let pref := fpMulDn s k2 (fpMulDn s ea (fpMulDn s (fpPowDn s eb 8) ab))
      let rhs := fpMulDn s pref dotS
      if Nat.ble r rhs then checkReadoutRowDn s k2 ea acRow rs ebs abs rVecs else false
  | _, _, _, _ => false

/-- Readout matrix checker from above (`R[a, b]`). -/
private def checkReadoutRowUp (s k2 ea : ℕ) (acRow : List ℕ) :
    List ℕ → List ℕ → List ℕ → List (List ℕ) → Bool
  | [], _, _, _ => true
  | r :: rs, eb :: ebs, ab :: abs, rVec :: rVecs =>
      let dotS := Nat.div (Nat.add (dotNat rVec acRow) (Nat.sub s 1)) s
      let pref := fpMulUp s k2 (fpMulUp s ea (fpMulUp s (fpPowUp s eb 8) ab))
      let lhs := fpMulUp s pref dotS
      if Nat.ble lhs r then checkReadoutRowUp s k2 ea acRow rs ebs abs rVecs else false
  | _, _, _, _ => false

private theorem checkReadoutRowDn_spec {s k2 ea m : ℕ} {acRow rs ebs abs : List ℕ}
    {rVecs : List (List ℕ)} (hr : rs.length = m) (heb : ebs.length = m) (hab : abs.length = m)
    (hrv : rVecs.length = m)
    (hchk : checkReadoutRowDn s k2 ea acRow rs ebs abs rVecs = true) (b : Fin m) :
    vecAt rs b.1 ≤ fpMulDn s
      (fpMulDn s k2 (fpMulDn s ea (fpMulDn s (fpPowDn s (vecAt ebs b.1) 8) (vecAt abs b.1))))
      (Nat.div (dotNat (rVecs.getD b.1 []) acRow) s) := by
  induction m generalizing rs ebs abs rVecs with
  | zero => exact b.elim0
  | succ m ih =>
      cases rs with | nil => simp at hr | cons r rs' =>
      cases ebs with | nil => simp at heb | cons eb ebs' =>
      cases abs with | nil => simp at hab | cons ab abs' =>
      cases rVecs with | nil => simp at hrv | cons rv rvs' =>
      simp only [checkReadoutRowDn] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases ?_ (fun j => ih (by simpa using hr) (by simpa using heb)
          (by simpa using hab) (by simpa using hrv) hchk j) b
        exact Nat.le_of_ble_eq_true hble
      · simp at hchk

private theorem checkReadoutRowUp_spec {s k2 ea m : ℕ} {acRow rs ebs abs : List ℕ}
    {rVecs : List (List ℕ)} (hr : rs.length = m) (heb : ebs.length = m) (hab : abs.length = m)
    (hrv : rVecs.length = m)
    (hchk : checkReadoutRowUp s k2 ea acRow rs ebs abs rVecs = true) (b : Fin m) :
    fpMulUp s
      (fpMulUp s k2 (fpMulUp s ea (fpMulUp s (fpPowUp s (vecAt ebs b.1) 8) (vecAt abs b.1))))
      (Nat.div (Nat.add (dotNat (rVecs.getD b.1 []) acRow) (Nat.sub s 1)) s) ≤
      vecAt rs b.1 := by
  induction m generalizing rs ebs abs rVecs with
  | zero => exact b.elim0
  | succ m ih =>
      cases rs with | nil => simp at hr | cons r rs' =>
      cases ebs with | nil => simp at heb | cons eb ebs' =>
      cases abs with | nil => simp at hab | cons ab abs' =>
      cases rVecs with | nil => simp at hrv | cons rv rvs' =>
      simp only [checkReadoutRowUp] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases ?_ (fun j => ih (by simpa using hr) (by simpa using heb)
          (by simpa using hab) (by simpa using hrv) hchk j) b
        exact Nat.le_of_ble_eq_true hble
      · simp at hchk

/-- Check all rows of the readout matrix `outR` against precomputed `buildReadoutVec` rows. -/
private def checkReadoutRowsDn (s k2 : ℕ) (eAi : List ℕ) (eAB_ii eAC_ie rVecs outR : List (List ℕ))
    : ℕ → ℕ → Bool
  | _, 0 => true
  | a, rem + 1 =>
      if checkReadoutRowDn s k2 (vecAt eAi a) (eAC_ie.getD a [])
          (outR.getD a []) eAi (eAB_ii.getD a []) rVecs
      then checkReadoutRowsDn s k2 eAi eAB_ii eAC_ie rVecs outR (Nat.add a 1) rem
      else false

private def checkReadoutRowsUp (s k2 : ℕ) (eAi : List ℕ) (eAB_ii eAC_ie rVecs outR : List (List ℕ))
    : ℕ → ℕ → Bool
  | _, 0 => true
  | a, rem + 1 =>
      if checkReadoutRowUp s k2 (vecAt eAi a) (eAC_ie.getD a [])
          (outR.getD a []) eAi (eAB_ii.getD a []) rVecs
      then checkReadoutRowsUp s k2 eAi eAB_ii eAC_ie rVecs outR (Nat.add a 1) rem
      else false

/-- Map `buildReadoutVecDn` over rows of `eAB_ie`. -/
private def mkReadoutVecsDn (s : ℕ) (wEnd eAe : List ℕ) : List (List ℕ) → List (List ℕ)
  | [] => []
  | bcRow :: rest => buildReadoutVecDn s wEnd eAe bcRow :: mkReadoutVecsDn s wEnd eAe rest

private def mkReadoutVecsUp (s : ℕ) (wEnd eAe : List ℕ) : List (List ℕ) → List (List ℕ)
  | [] => []
  | bcRow :: rest => buildReadoutVecUp s wEnd eAe bcRow :: mkReadoutVecsUp s wEnd eAe rest

private theorem mkReadoutVecsDn_spec {s n : ℕ} (wEnd eAe : List ℕ) (eAB_ie : List (List ℕ))
    (hLen : eAB_ie.length = n) :
    (mkReadoutVecsDn s wEnd eAe eAB_ie).length = n ∧
      ∀ b : Fin n, (mkReadoutVecsDn s wEnd eAe eAB_ie).getD b.1 [] =
        buildReadoutVecDn s wEnd eAe (eAB_ie.getD b.1 []) := by
  induction n generalizing eAB_ie with
  | zero => cases eAB_ie with | nil => exact ⟨rfl, fun b => b.elim0⟩ | cons => simp at hLen
  | succ n ih =>
      cases eAB_ie with | nil => simp at hLen | cons row rest =>
      obtain ⟨hl, hg⟩ := ih rest (by simpa using hLen)
      exact ⟨by simp [mkReadoutVecsDn, hl], fun b => Fin.cases rfl (fun j => hg j) b⟩

private theorem mkReadoutVecsUp_spec {s n : ℕ} (wEnd eAe : List ℕ) (eAB_ie : List (List ℕ))
    (hLen : eAB_ie.length = n) :
    (mkReadoutVecsUp s wEnd eAe eAB_ie).length = n ∧
      ∀ b : Fin n, (mkReadoutVecsUp s wEnd eAe eAB_ie).getD b.1 [] =
        buildReadoutVecUp s wEnd eAe (eAB_ie.getD b.1 []) := by
  induction n generalizing eAB_ie with
  | zero => cases eAB_ie with | nil => exact ⟨rfl, fun b => b.elim0⟩ | cons => simp at hLen
  | succ n ih =>
      cases eAB_ie with | nil => simp at hLen | cons row rest =>
      obtain ⟨hl, hg⟩ := ih rest (by simpa using hLen)
      exact ⟨by simp [mkReadoutVecsUp, hl], fun b => Fin.cases rfl (fun j => hg j) b⟩

/-- Soundness of `checkReadoutRowsDn` against `ar2ReadoutMat`. -/
private theorem checkReadoutRowsDn_sound {n s k2 : ℕ} (hs : 0 < s)
    {L_end L_int : ℝ} {r : Fin n → ℝ}
    {wEnd eAe eAi : List ℕ} {eAB_ii eAB_ie eAC_ie outR : List (List ℕ)}
    (hwLen : wEnd.length = n) (heAeLen : eAe.length = n) (heAiLen : eAi.length = n)
    (hieLen : eAB_ie.length = n) (hieR : ∀ b : Fin n, (eAB_ie.getD b.1 []).length = n)
    (hiiR : ∀ a : Fin n, (eAB_ii.getD a.1 []).length = n)
    (hacR : ∀ a : Fin n, (eAC_ie.getD a.1 []).length = n)
    (houtR : ∀ a : Fin n, (outR.getD a.1 []).length = n)
    (hk2 : (k2 : ℝ) / s ≤ 2 * Real.sqrt (6 / Real.pi))
    (hw : ∀ c : Fin n, (vecAt wEnd c.1 : ℝ) / s ≤ shiftWeight L_end r c)
    (heAe : ∀ c : Fin n, (vecAt eAe c.1 : ℝ) / s ≤ eAFactor (shiftNode L_end r c))
    (heAi : ∀ a : Fin n, (vecAt eAi a.1 : ℝ) / s ≤ eAFactor (shiftNode L_int r a))
    (hii : ∀ a b : Fin n, (matAt eAB_ii a.1 b.1 : ℝ) / s ≤
      eABFactor (shiftNode L_int r a) (shiftNode L_int r b))
    (hie : ∀ b c : Fin n, (matAt eAB_ie b.1 c.1 : ℝ) / s ≤
      eABFactor (shiftNode L_int r b) (shiftNode L_end r c))
    (hac : ∀ a c : Fin n, (matAt eAC_ie a.1 c.1 : ℝ) / s ≤
      eACFactor (shiftNode L_int r a) (shiftNode L_end r c))
    (hchk : ∀ a : Fin n, checkReadoutRowDn s k2 (vecAt eAi a.1) (eAC_ie.getD a.1 [])
      (outR.getD a.1 []) eAi (eAB_ii.getD a.1 [])
      (mkReadoutVecsDn s wEnd eAe eAB_ie) = true) :
    ∀ a b : Fin n, (matAt outR a.1 b.1 : ℝ) / s ≤ ar2ReadoutMat L_end L_int r a b := by
  obtain ⟨hrv_len, hrv_get⟩ := mkReadoutVecsDn_spec (s := s) wEnd eAe eAB_ie hieLen
  intro a b
  have hrow := hchk a
  have hnat := checkReadoutRowDn_spec (houtR a) heAiLen (hiiR a) hrv_len hrow b
  have hrb := buildReadoutVecDn_spec (s := s) wEnd eAe (eAB_ie.getD b.1 []) hwLen heAeLen (hieR b)
  rw [ar2ReadoutMat_eq_factor]
  refine (div_le_div_of_nonneg_right (Nat.cast_le.mpr hnat) (Nat.cast_nonneg s)).trans ?_
  refine fpMulDn_le_mul hs ?_ ?_
  · refine fpMulDn_le_mul hs hk2 (fpMulDn_le_mul hs (heAi a)
      (fpMulDn_le_mul hs (fpPowDn_le hs (heAi b)) (hii a b)))
  · rw [hrv_get b]
    have hdot := dotNat_eq hrb.1 (hacR a)
    have hdv := natDiv_cast_le (a := dotNat (buildReadoutVecDn s wEnd eAe (eAB_ie.getD b.1 []))
      (eAC_ie.getD a.1 [])) hs
    calc (Nat.div (dotNat (buildReadoutVecDn s wEnd eAe (eAB_ie.getD b.1 []))
            (eAC_ie.getD a.1 [])) s : ℝ) / s
        ≤ ((dotNat (buildReadoutVecDn s wEnd eAe (eAB_ie.getD b.1 []))
            (eAC_ie.getD a.1 []) : ℕ) : ℝ) / s / s :=
            div_le_div_of_nonneg_right hdv (Nat.cast_nonneg s)
      _ = ∑ c : Fin n, ((vecAt (buildReadoutVecDn s wEnd eAe (eAB_ie.getD b.1 [])) c.1 : ℝ) / s) *
            ((vecAt (eAC_ie.getD a.1 []) c.1 : ℝ) / s) := by
            rw [hdot, Nat.cast_sum, Finset.sum_div, Finset.sum_div]
            refine Finset.sum_congr rfl fun c _ => by push_cast; ring
      _ ≤ ∑ c : Fin n, shiftWeight L_end r c *
            (eAFactor (shiftNode L_end r c) ^ 4 *
              (eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2 *
                eACFactor (shiftNode L_int r a) (shiftNode L_end r c))) := by
            refine Finset.sum_le_sum fun c _ => ?_
            have h1 : (vecAt (buildReadoutVecDn s wEnd eAe (eAB_ie.getD b.1 [])) c.1 : ℝ) / s ≤
                shiftWeight L_end r c * (eAFactor (shiftNode L_end r c) ^ 4 *
                  eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2) := by
              rw [hrb.2 c]
              refine fpMulDn_le_mul hs (hw c)
                (fpMulDn_le_mul hs (fpPowDn_le hs (heAe c)) ?_)
              rw [sq]; exact fpMulDn_le_mul hs (hie b c) (hie b c)
            calc ((vecAt (buildReadoutVecDn s wEnd eAe (eAB_ie.getD b.1 [])) c.1 : ℝ) / s) *
                  ((vecAt (eAC_ie.getD a.1 []) c.1 : ℝ) / s)
                ≤ (shiftWeight L_end r c * (eAFactor (shiftNode L_end r c) ^ 4 *
                    eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2)) *
                    eACFactor (shiftNode L_int r a) (shiftNode L_end r c) :=
                  mul_le_mul h1 (hac a c) (by positivity)
                    ((by positivity : (0 : ℝ) ≤ _).trans h1)
              _ = _ := by ring

/-- Soundness of `checkReadoutRowsUp` against `ar2ReadoutMat`. -/
private theorem checkReadoutRowsUp_sound {n s k2 : ℕ} (hs : 0 < s)
    {L_end L_int : ℝ} {r : Fin n → ℝ}
    {wEnd eAe eAi : List ℕ} {eAB_ii eAB_ie eAC_ie outR : List (List ℕ)}
    (hwLen : wEnd.length = n) (heAeLen : eAe.length = n) (heAiLen : eAi.length = n)
    (hieLen : eAB_ie.length = n) (hieR : ∀ b : Fin n, (eAB_ie.getD b.1 []).length = n)
    (hiiR : ∀ a : Fin n, (eAB_ii.getD a.1 []).length = n)
    (hacR : ∀ a : Fin n, (eAC_ie.getD a.1 []).length = n)
    (houtR : ∀ a : Fin n, (outR.getD a.1 []).length = n)
    (hw0 : ∀ c : Fin n, 0 ≤ shiftWeight L_end r c)
    (hk2 : 2 * Real.sqrt (6 / Real.pi) ≤ (k2 : ℝ) / s)
    (hw : ∀ c : Fin n, shiftWeight L_end r c ≤ (vecAt wEnd c.1 : ℝ) / s)
    (heAe : ∀ c : Fin n, eAFactor (shiftNode L_end r c) ≤ (vecAt eAe c.1 : ℝ) / s)
    (heAi : ∀ a : Fin n, eAFactor (shiftNode L_int r a) ≤ (vecAt eAi a.1 : ℝ) / s)
    (hii : ∀ a b : Fin n, eABFactor (shiftNode L_int r a) (shiftNode L_int r b) ≤
      (matAt eAB_ii a.1 b.1 : ℝ) / s)
    (hie : ∀ b c : Fin n, eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ≤
      (matAt eAB_ie b.1 c.1 : ℝ) / s)
    (hac : ∀ a c : Fin n, eACFactor (shiftNode L_int r a) (shiftNode L_end r c) ≤
      (matAt eAC_ie a.1 c.1 : ℝ) / s)
    (hchk : ∀ a : Fin n, checkReadoutRowUp s k2 (vecAt eAi a.1) (eAC_ie.getD a.1 [])
      (outR.getD a.1 []) eAi (eAB_ii.getD a.1 [])
      (mkReadoutVecsUp s wEnd eAe eAB_ie) = true) :
    ∀ a b : Fin n, ar2ReadoutMat L_end L_int r a b ≤ (matAt outR a.1 b.1 : ℝ) / s := by
  obtain ⟨hrv_len, hrv_get⟩ := mkReadoutVecsUp_spec (s := s) wEnd eAe eAB_ie hieLen
  have heAF_nn : ∀ t : ℝ, 0 ≤ eAFactor t := fun _ => (Real.exp_pos _).le
  have heAB_nn : ∀ x y : ℝ, 0 ≤ eABFactor x y := fun _ _ => (Real.exp_pos _).le
  have heAC_nn : ∀ x z : ℝ, 0 ≤ eACFactor x z := fun _ _ => (Real.exp_pos _).le
  intro a b
  have hrow := hchk a
  have hnat := checkReadoutRowUp_spec (houtR a) heAiLen (hiiR a) hrv_len hrow b
  have hrb := buildReadoutVecUp_spec (s := s) wEnd eAe (eAB_ie.getD b.1 []) hwLen heAeLen (hieR b)
  rw [ar2ReadoutMat_eq_factor]
  have hsum_nn : 0 ≤ ∑ c : Fin n, shiftWeight L_end r c *
      (eAFactor (shiftNode L_end r c) ^ 4 *
        (eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2 *
          eACFactor (shiftNode L_int r a) (shiftNode L_end r c))) :=
    Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c)
      (mul_nonneg (pow_nonneg (heAF_nn _) _) (mul_nonneg (sq_nonneg _) (heAC_nn _ _)))
  have hpref_nn : 0 ≤ 2 * Real.sqrt (6 / Real.pi) *
      (eAFactor (shiftNode L_int r a) *
        (eAFactor (shiftNode L_int r b) ^ 8 *
          eABFactor (shiftNode L_int r a) (shiftNode L_int r b))) :=
    mul_nonneg (by positivity)
      (mul_nonneg (heAF_nn _) (mul_nonneg (pow_nonneg (heAF_nn _) _) (heAB_nn _ _)))
  refine (mul_le_fpMulUp hs hpref_nn hsum_nn ?_ ?_).trans
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr hnat) (Nat.cast_nonneg s))
  · refine mul_le_fpMulUp hs (by positivity)
      (mul_nonneg (heAF_nn _) (mul_nonneg (pow_nonneg (heAF_nn _) _) (heAB_nn _ _))) hk2
      (mul_le_fpMulUp hs (heAF_nn _) (mul_nonneg (pow_nonneg (heAF_nn _) _) (heAB_nn _ _))
        (heAi a) (mul_le_fpMulUp hs (pow_nonneg (heAF_nn _) _) (heAB_nn _ _)
          (pow_le_fpPowUp hs (heAF_nn _) (heAi b)) (hii a b)))
  · rw [hrv_get b]
    have hdot := dotNat_eq hrb.1 (hacR a)
    have hup := le_natDivUp_cast
      (a := dotNat (buildReadoutVecUp s wEnd eAe (eAB_ie.getD b.1 [])) (eAC_ie.getD a.1 [])) hs
    calc ∑ c : Fin n, shiftWeight L_end r c *
            (eAFactor (shiftNode L_end r c) ^ 4 *
              (eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2 *
                eACFactor (shiftNode L_int r a) (shiftNode L_end r c)))
        ≤ ∑ c : Fin n, ((vecAt (buildReadoutVecUp s wEnd eAe (eAB_ie.getD b.1 [])) c.1 : ℝ) / s) *
            ((vecAt (eAC_ie.getD a.1 []) c.1 : ℝ) / s) := by
            refine Finset.sum_le_sum fun c _ => ?_
            have h1 : shiftWeight L_end r c * (eAFactor (shiftNode L_end r c) ^ 4 *
                eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2) ≤
                (vecAt (buildReadoutVecUp s wEnd eAe (eAB_ie.getD b.1 [])) c.1 : ℝ) / s := by
              rw [hrb.2 c]
              refine mul_le_fpMulUp hs (hw0 c)
                (mul_nonneg (pow_nonneg (heAF_nn _) _) (sq_nonneg _)) (hw c)
                (mul_le_fpMulUp hs (pow_nonneg (heAF_nn _) _) (sq_nonneg _)
                  (pow_le_fpPowUp hs (heAF_nn _) (heAe c)) ?_)
              rw [sq]; exact mul_le_fpMulUp hs (heAB_nn _ _) (heAB_nn _ _) (hie b c) (hie b c)
            calc shiftWeight L_end r c * (eAFactor (shiftNode L_end r c) ^ 4 *
                  (eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2 *
                    eACFactor (shiftNode L_int r a) (shiftNode L_end r c)))
                = (shiftWeight L_end r c * (eAFactor (shiftNode L_end r c) ^ 4 *
                    eABFactor (shiftNode L_int r b) (shiftNode L_end r c) ^ 2)) *
                    eACFactor (shiftNode L_int r a) (shiftNode L_end r c) := by ring
              _ ≤ ((vecAt (buildReadoutVecUp s wEnd eAe (eAB_ie.getD b.1 [])) c.1 : ℝ) / s) *
                    ((vecAt (eAC_ie.getD a.1 []) c.1 : ℝ) / s) :=
                  mul_le_mul h1 (hac a c) (heAC_nn _ _)
                    ((mul_nonneg (hw0 c)
                      (mul_nonneg (pow_nonneg (heAF_nn _) _) (sq_nonneg _))).trans h1)
      _ = ((dotNat (buildReadoutVecUp s wEnd eAe (eAB_ie.getD b.1 []))
            (eAC_ie.getD a.1 []) : ℕ) : ℝ) / s / s := by
            rw [hdot, Nat.cast_sum, Finset.sum_div, Finset.sum_div]
            refine Finset.sum_congr rfl fun c _ => by push_cast; ring
      _ ≤ (Nat.div (Nat.add (dotNat (buildReadoutVecUp s wEnd eAe (eAB_ie.getD b.1 []))
            (eAC_ie.getD a.1 [])) (Nat.sub s 1)) s : ℝ) / s :=
            div_le_div_of_nonneg_right hup (Nat.cast_nonneg s)

/-- Transpose a `List (List ℕ)` into its list of `n` columns `0..n-1`. -/
private def transposeMat (M : List (List ℕ)) : ℕ → List (List ℕ)
  | 0 => []
  | k + 1 => transposeMat M k ++ [getCol M k]

private theorem transposeMat_spec {M : List (List ℕ)} (m : ℕ) :
    (transposeMat M m).length = m ∧
      ∀ c : Fin m, (transposeMat M m).getD c.1 [] = getCol M c.1 := by
  induction m with
  | zero => exact ⟨rfl, fun c => c.elim0⟩
  | succ m ih =>
      obtain ⟨hl, hg⟩ := ih
      refine ⟨by simp [transposeMat, hl], fun c => ?_⟩
      by_cases hlt : c.1 < m
      · have heq : (transposeMat M m ++ [getCol M m]).getD c.1 [] =
            (transposeMat M m).getD c.1 [] := by
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by omega : c.1 < (transposeMat M m).length)]
        rw [transposeMat, heq]
        exact hg ⟨c.1, hlt⟩
      · have hcm : c.1 = m := by omega
        have heq : (transposeMat M m ++ [getCol M m]).getD m [] = getCol M m := by
          simp [List.getD_eq_getElem?_getD, hl]
        simpa [transposeMat, hcm] using heq

/-- Soundness for checking a 2D exponential matrix entry `(a, b) ↦ exp (-coeff * x_a * y_b)`
from below: `coeff * x_hi * y_hi ≤ 64 * (tHi / T)`. -/
private def checkExpPairRowDn (s ratio m coeff den : ℕ) (xa : ℕ) :
    List ℕ → List ℕ → Bool
  | [], [] => true
  | v :: vs, yb :: ybs =>
      let tHi := Nat.div (Nat.add (Nat.mul coeff (Nat.mul xa yb)) (Nat.sub den 1)) den
      if Nat.ble v (expNeg64Dn (Nat.mul s ratio) ratio m tHi)
      then checkExpPairRowDn s ratio m coeff den xa vs ybs
      else false
  | _, _ => false

private def checkExpPairRowUp (s ratio m coeff den : ℕ) (xa : ℕ) :
    List ℕ → List ℕ → Bool
  | [], [] => true
  | v :: vs, yb :: ybs =>
      let tLo := Nat.div (Nat.mul coeff (Nat.mul xa yb)) den
      if Nat.ble (expNeg64Up (Nat.mul s ratio) ratio m tLo) v
      then checkExpPairRowUp s ratio m coeff den xa vs ybs
      else false
  | _, _ => false

private theorem checkExpPairRowDn_spec {s ratio m coeff den n xa : ℕ}
    (hS : 0 < s) (hr : 0 < ratio) (hden : 0 < den)
    {vs ys : List ℕ} (hv : vs.length = n) (hy : ys.length = n)
    (hchk : checkExpPairRowDn s ratio m coeff den xa vs ys = true)
    (b : Fin n) {x : ℝ}
    (hx : x ≤ 64 * ((coeff : ℝ) * xa * (vecAt ys b.1 : ℝ) / den / (s * ratio : ℕ))) :
    (vecAt vs b.1 : ℝ) / s ≤ Real.exp (-x) := by
  induction n generalizing vs ys with
  | zero => exact b.elim0
  | succ n ih =>
      cases vs with | nil => simp at hv | cons v vs' =>
      cases ys with | nil => simp at hy | cons y ys' =>
      simp only [checkExpPairRowDn] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases (fun hx0 => ?_) (fun j hxj =>
          ih (by simpa using hv) (by simpa using hy) hchk j hxj) b hx
        have hv_le : (v : ℝ) ≤ expNeg64Dn (s * ratio) ratio m
            (Nat.div (Nat.add (coeff * (xa * y)) (den - 1)) den) := natBle_real_le hble
        refine (div_le_div_of_nonneg_right hv_le (Nat.cast_nonneg s)).trans
          (expNeg64Dn_le hS hr ?_)
        have hdiv := le_natDivUp_cast (a := coeff * (xa * y)) hden
        have h1 : (coeff : ℝ) * xa * y / den ≤
            (Nat.div (Nat.add (coeff * (xa * y)) (den - 1)) den : ℝ) := by
          simpa [Nat.cast_mul, mul_assoc] using hdiv
        calc x ≤ 64 * ((coeff : ℝ) * xa * y / den / (s * ratio : ℕ)) := hx0
          _ ≤ 64 * ((Nat.div (Nat.add (coeff * (xa * y)) (den - 1)) den : ℝ) /
              (s * ratio : ℕ)) := by gcongr
      · simp at hchk

private theorem checkExpPairRowUp_spec {s ratio m coeff den n xa : ℕ}
    (hS : 0 < s) (hr : 0 < ratio) (hden : 0 < den)
    {vs ys : List ℕ} (hv : vs.length = n) (hy : ys.length = n)
    (hchk : checkExpPairRowUp s ratio m coeff den xa vs ys = true)
    (b : Fin n) {x : ℝ}
    (hx : 64 * ((coeff : ℝ) * xa * (vecAt ys b.1 : ℝ) / den / (s * ratio : ℕ)) ≤ x) :
    Real.exp (-x) ≤ (vecAt vs b.1 : ℝ) / s := by
  induction n generalizing vs ys with
  | zero => exact b.elim0
  | succ n ih =>
      cases vs with | nil => simp at hv | cons v vs' =>
      cases ys with | nil => simp at hy | cons y ys' =>
      simp only [checkExpPairRowUp] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases (fun hx0 => ?_) (fun j hxj =>
          ih (by simpa using hv) (by simpa using hy) hchk j hxj) b hx
        have hv_ge : (expNeg64Up (s * ratio) ratio m
            (Nat.div (coeff * (xa * y)) den) : ℝ) ≤ v := natBle_real_le hble
        refine (le_expNeg64Up hS hr ?_).trans
          (div_le_div_of_nonneg_right hv_ge (Nat.cast_nonneg s))
        have hdiv := natDiv_cast_le (a := coeff * (xa * y)) hden
        have h1 : (Nat.div (coeff * (xa * y)) den : ℝ) ≤ (coeff : ℝ) * xa * y / den := by
          simpa [Nat.cast_mul, mul_assoc] using hdiv
        calc 64 * ((Nat.div (coeff * (xa * y)) den : ℝ) / (s * ratio : ℕ))
            ≤ 64 * ((coeff : ℝ) * xa * y / den / (s * ratio : ℕ)) := by gcongr
          _ ≤ x := hx0
      · simp at hchk

/-- Check 1D `eA` table `exp (-3/2 * x^2)` from below. -/
private def checkExpSqDn (s ratio m coeff den : ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | v :: vs, x :: xs =>
      let tHi := Nat.div (Nat.add (Nat.mul coeff (Nat.mul x x)) (Nat.sub den 1)) den
      if Nat.ble v (expNeg64Dn (Nat.mul s ratio) ratio m tHi)
      then checkExpSqDn s ratio m coeff den vs xs
      else false
  | _, _ => false

/-- Check 1D `eA` table `exp (-3/2 * x^2)` from above. -/
private def checkExpSqUp (s ratio m coeff den : ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | v :: vs, x :: xs =>
      let tLo := Nat.div (Nat.mul coeff (Nat.mul x x)) den
      if Nat.ble (expNeg64Up (Nat.mul s ratio) ratio m tLo) v
      then checkExpSqUp s ratio m coeff den vs xs
      else false
  | _, _ => false

private theorem checkExpSqDn_spec {s ratio m coeff den n : ℕ}
    (hS : 0 < s) (hr : 0 < ratio) (hden : 0 < den)
    {vs xs : List ℕ} (hv : vs.length = n) (hx : xs.length = n)
    (hchk : checkExpSqDn s ratio m coeff den vs xs = true) (a : Fin n) {y : ℝ}
    (hy : y ≤ 64 * ((coeff : ℝ) * (vecAt xs a.1 : ℝ) ^ 2 / den / (s * ratio : ℕ))) :
    (vecAt vs a.1 : ℝ) / s ≤ Real.exp (-y) := by
  induction n generalizing vs xs with
  | zero => exact a.elim0
  | succ n ih =>
      cases vs with | nil => simp at hv | cons v vs' =>
      cases xs with | nil => simp at hx | cons x xs' =>
      simp only [checkExpSqDn] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases (fun hy0 => ?_) (fun j hyj =>
          ih (by simpa using hv) (by simpa using hx) hchk j hyj) a hy
        have hv_le : (v : ℝ) ≤ expNeg64Dn (s * ratio) ratio m
            (Nat.div (Nat.add (coeff * (x * x)) (den - 1)) den) := natBle_real_le hble
        refine (div_le_div_of_nonneg_right hv_le (Nat.cast_nonneg s)).trans
          (expNeg64Dn_le hS hr ?_)
        have hdiv := le_natDivUp_cast (a := coeff * (x * x)) hden
        have h1 : (coeff : ℝ) * (x : ℝ) ^ 2 / den ≤
            (Nat.div (Nat.add (coeff * (x * x)) (den - 1)) den : ℝ) := by
          simpa [Nat.cast_mul, sq, mul_assoc] using hdiv
        calc y ≤ 64 * ((coeff : ℝ) * (x : ℝ) ^ 2 / den / (s * ratio : ℕ)) := hy0
          _ ≤ 64 * ((Nat.div (Nat.add (coeff * (x * x)) (den - 1)) den : ℝ) /
              (s * ratio : ℕ)) := by gcongr
      · simp at hchk

private theorem checkExpSqUp_spec {s ratio m coeff den n : ℕ}
    (hS : 0 < s) (hr : 0 < ratio) (hden : 0 < den)
    {vs xs : List ℕ} (hv : vs.length = n) (hx : xs.length = n)
    (hchk : checkExpSqUp s ratio m coeff den vs xs = true) (a : Fin n) {y : ℝ}
    (hy : 64 * ((coeff : ℝ) * (vecAt xs a.1 : ℝ) ^ 2 / den / (s * ratio : ℕ)) ≤ y) :
    Real.exp (-y) ≤ (vecAt vs a.1 : ℝ) / s := by
  induction n generalizing vs xs with
  | zero => exact a.elim0
  | succ n ih =>
      cases vs with | nil => simp at hv | cons v vs' =>
      cases xs with | nil => simp at hx | cons x xs' =>
      simp only [checkExpSqUp] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases (fun hy0 => ?_) (fun j hyj =>
          ih (by simpa using hv) (by simpa using hx) hchk j hyj) a hy
        have hv_ge : (expNeg64Up (s * ratio) ratio m
            (Nat.div (coeff * (x * x)) den) : ℝ) ≤ v := natBle_real_le hble
        refine (le_expNeg64Up hS hr ?_).trans
          (div_le_div_of_nonneg_right hv_ge (Nat.cast_nonneg s))
        have hdiv := natDiv_cast_le (a := coeff * (x * x)) hden
        have h1 : (Nat.div (coeff * (x * x)) den : ℝ) ≤ (coeff : ℝ) * (x : ℝ) ^ 2 / den := by
          simpa [Nat.cast_mul, sq, mul_assoc] using hdiv
        calc 64 * ((Nat.div (coeff * (x * x)) den : ℝ) / (s * ratio : ℕ))
            ≤ 64 * ((coeff : ℝ) * (x : ℝ) ^ 2 / den / (s * ratio : ℕ)) := by gcongr
          _ ≤ y := hy0
      · simp at hchk

/-- Check `M1` entry `(a, b)` against `c2 * (w_a * eA_a^3) * (w_b * eA_b^3) * eAB[a, b]`. -/
private def checkInitRowDn (s fa : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], [], [], [] => true
  | m :: ms, wb :: wbs, eb :: ebs, ab :: abs =>
      let fb := fpMulDn s wb (fpPowDn s eb 3)
      let rhs := fpMulDn s (fpMulDn s fa fb) ab
      if Nat.ble m rhs then checkInitRowDn s fa ms wbs ebs abs else false
  | _, _, _, _ => false

private def checkInitRowUp (s fa : ℕ) : List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | [], [], [], [] => true
  | m :: ms, wb :: wbs, eb :: ebs, ab :: abs =>
      let fb := fpMulUp s wb (fpPowUp s eb 3)
      let lhs := fpMulUp s (fpMulUp s fa fb) ab
      if Nat.ble lhs m then checkInitRowUp s fa ms wbs ebs abs else false
  | _, _, _, _ => false

private theorem checkInitRowDn_spec {s c2 n wa ea : ℕ} (hs : 0 < s)
    {c2r war ear : ℝ} {wbr ebr abr : Fin n → ℝ}
    {ms wbs ebs abs : List ℕ} (hm : ms.length = n) (hw : wbs.length = n)
    (he : ebs.length = n) (hab : abs.length = n)
    (hc2 : (c2 : ℝ) / s ≤ c2r) (hwa : (wa : ℝ) / s ≤ war) (hea : (ea : ℝ) / s ≤ ear)
    (hwb : ∀ b : Fin n, (vecAt wbs b.1 : ℝ) / s ≤ wbr b)
    (heb : ∀ b : Fin n, (vecAt ebs b.1 : ℝ) / s ≤ ebr b)
    (hlab : ∀ b : Fin n, (vecAt abs b.1 : ℝ) / s ≤ abr b)
    (hchk : checkInitRowDn s (fpMulDn s c2 (fpMulDn s wa (fpPowDn s ea 3)))
      ms wbs ebs abs = true) (b : Fin n) :
    (vecAt ms b.1 : ℝ) / s ≤ c2r * (war * ear ^ 3) * (wbr b * ebr b ^ 3) * abr b := by
  have hfa : (fpMulDn s c2 (fpMulDn s wa (fpPowDn s ea 3)) : ℝ) / s ≤
      c2r * (war * ear ^ 3) :=
    fpMulDn_le_mul hs hc2 (fpMulDn_le_mul hs hwa (fpPowDn_le hs hea))
  induction n generalizing ms wbs ebs abs with
  | zero => exact b.elim0
  | succ n ih =>
      cases ms with | nil => simp at hm | cons m ms' =>
      cases wbs with | nil => simp at hw | cons wb wbs' =>
      cases ebs with | nil => simp at he | cons eb ebs' =>
      cases abs with | nil => simp at hab | cons ab abs' =>
      simp only [checkInitRowDn] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases ?_ (fun j => ih (by simpa using hm) (by simpa using hw)
          (by simpa using he) (by simpa using hab)
          (fun k => hwb k.succ) (fun k => heb k.succ) (fun k => hlab k.succ) hchk j) b
        have hm_le : (m : ℝ) / s ≤ _ :=
          div_le_div_of_nonneg_right (natBle_real_le hble) (Nat.cast_nonneg s)
        exact hm_le.trans (fpMulDn_le_mul hs
          (fpMulDn_le_mul hs hfa (fpMulDn_le_mul hs (hwb 0) (fpPowDn_le hs (heb 0))))
          (hlab 0))
      · simp at hchk

private theorem checkInitRowUp_spec {s c2 n wa ea : ℕ} (hs : 0 < s)
    {c2r war ear : ℝ} {wbr ebr abr : Fin n → ℝ}
    {ms wbs ebs abs : List ℕ} (hm : ms.length = n) (hw : wbs.length = n)
    (he : ebs.length = n) (hab : abs.length = n)
    (hc20 : 0 ≤ c2r) (hwa0 : 0 ≤ war) (hea0 : 0 ≤ ear)
    (hwb0 : ∀ b, 0 ≤ wbr b) (heb0 : ∀ b, 0 ≤ ebr b) (hab0 : ∀ b, 0 ≤ abr b)
    (hc2 : c2r ≤ (c2 : ℝ) / s) (hwa : war ≤ (wa : ℝ) / s) (hea : ear ≤ (ea : ℝ) / s)
    (hwb : ∀ b : Fin n, wbr b ≤ (vecAt wbs b.1 : ℝ) / s)
    (heb : ∀ b : Fin n, ebr b ≤ (vecAt ebs b.1 : ℝ) / s)
    (hlab : ∀ b : Fin n, abr b ≤ (vecAt abs b.1 : ℝ) / s)
    (hchk : checkInitRowUp s (fpMulUp s c2 (fpMulUp s wa (fpPowUp s ea 3)))
      ms wbs ebs abs = true) (b : Fin n) :
    c2r * (war * ear ^ 3) * (wbr b * ebr b ^ 3) * abr b ≤ (vecAt ms b.1 : ℝ) / s := by
  have hfa : c2r * (war * ear ^ 3) ≤
      (fpMulUp s c2 (fpMulUp s wa (fpPowUp s ea 3)) : ℝ) / s :=
    mul_le_fpMulUp hs hc20 (mul_nonneg hwa0 (pow_nonneg hea0 3)) hc2
      (mul_le_fpMulUp hs hwa0 (pow_nonneg hea0 3) hwa (pow_le_fpPowUp hs hea0 hea))
  have hfa0 : 0 ≤ c2r * (war * ear ^ 3) :=
    mul_nonneg hc20 (mul_nonneg hwa0 (pow_nonneg hea0 3))
  induction n generalizing ms wbs ebs abs with
  | zero => exact b.elim0
  | succ n ih =>
      cases ms with | nil => simp at hm | cons m ms' =>
      cases wbs with | nil => simp at hw | cons wb wbs' =>
      cases ebs with | nil => simp at he | cons eb ebs' =>
      cases abs with | nil => simp at hab | cons ab abs' =>
      simp only [checkInitRowUp] at hchk
      split at hchk
      · rename_i hble
        refine Fin.cases ?_ (fun j => ih (by simpa using hm) (by simpa using hw)
          (by simpa using he) (by simpa using hab)
          (fun k => hwb0 k.succ) (fun k => heb0 k.succ) (fun k => hab0 k.succ)
          (fun k => hwb k.succ) (fun k => heb k.succ) (fun k => hlab k.succ) hchk j) b
        have hm_ge : (_ : ℝ) / s ≤ (m : ℝ) / s :=
          div_le_div_of_nonneg_right (natBle_real_le hble) (Nat.cast_nonneg s)
        have hfb0 : 0 ≤ wbr 0 * ebr 0 ^ 3 := mul_nonneg (hwb0 0) (pow_nonneg (heb0 0) 3)
        exact (mul_le_fpMulUp hs (mul_nonneg hfa0 hfb0) (hab0 0)
          (mul_le_fpMulUp hs hfa0 hfb0 hfa
            (mul_le_fpMulUp hs (hwb0 0) (pow_nonneg (heb0 0) 3) (hwb 0)
              (pow_le_fpPowUp hs (heb0 0) (heb 0)))) (hlab 0)).trans hm_ge
      · simp at hchk

/-- Check `M` row-by-row for `ar2InitMat` (`checkInitMatDn` / `checkInitMatUp`). -/
private def checkInitMatDn (s c2 : ℕ) (wa ea wb eb : List ℕ) (eAB mOut : List (List ℕ)) :
    ℕ → ℕ → Bool
  | _, 0 => true
  | a, rem + 1 =>
      let fa := fpMulDn s c2 (fpMulDn s (vecAt wa a) (fpPowDn s (vecAt ea a) 3))
      if checkInitRowDn s fa (mOut.getD a []) wb eb (eAB.getD a [])
      then checkInitMatDn s c2 wa ea wb eb eAB mOut (Nat.add a 1) rem
      else false

private def checkInitMatUp (s c2 : ℕ) (wa ea wb eb : List ℕ) (eAB mOut : List (List ℕ)) :
    ℕ → ℕ → Bool
  | _, 0 => true
  | a, rem + 1 =>
      let fa := fpMulUp s c2 (fpMulUp s (vecAt wa a) (fpPowUp s (vecAt ea a) 3))
      if checkInitRowUp s fa (mOut.getD a []) wb eb (eAB.getD a [])
      then checkInitMatUp s c2 wa ea wb eb eAB mOut (Nat.add a 1) rem
      else false

/-- Upper-bound helper checking a 2D `exp` matrix row range `start .. start + rem - 1`. -/
private def checkExpPairRowsDn (s ratio m coeff den : ℕ) (xs ys : List ℕ)
    (mat : List (List ℕ)) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, rem + 1 =>
      if checkExpPairRowDn s ratio m coeff den (vecAt xs a) (mat.getD a []) ys
      then checkExpPairRowsDn s ratio m coeff den xs ys mat (Nat.add a 1) rem
      else false

private def checkExpPairRowsUp (s ratio m coeff den : ℕ) (xs ys : List ℕ)
    (mat : List (List ℕ)) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, rem + 1 =>
      if checkExpPairRowUp s ratio m coeff den (vecAt xs a) (mat.getD a []) ys
      then checkExpPairRowsUp s ratio m coeff den xs ys mat (Nat.add a 1) rem
      else false

private theorem checkExpPairRowsDn_get {s ratio m coeff den : ℕ} {xs ys : List ℕ}
    {mat : List (List ℕ)} {start rem : ℕ}
    (hchk : checkExpPairRowsDn s ratio m coeff den xs ys mat start rem = true)
    {a : ℕ} (ha1 : start ≤ a) (ha2 : a < start + rem) :
    checkExpPairRowDn s ratio m coeff den (vecAt xs a) (mat.getD a []) ys = true := by
  induction rem generalizing start with
  | zero => omega
  | succ rem ih =>
      simp only [checkExpPairRowsDn] at hchk
      split at hchk
      · rename_i hc
        by_cases heq : a = start
        · subst heq; exact hc
        · exact ih (start := start + 1) hchk (by omega) (by omega)
      · simp at hchk

private theorem checkExpPairRowsUp_get {s ratio m coeff den : ℕ} {xs ys : List ℕ}
    {mat : List (List ℕ)} {start rem : ℕ}
    (hchk : checkExpPairRowsUp s ratio m coeff den xs ys mat start rem = true)
    {a : ℕ} (ha1 : start ≤ a) (ha2 : a < start + rem) :
    checkExpPairRowUp s ratio m coeff den (vecAt xs a) (mat.getD a []) ys = true := by
  induction rem generalizing start with
  | zero => omega
  | succ rem ih =>
      simp only [checkExpPairRowsUp] at hchk
      split at hchk
      · rename_i hc
        by_cases heq : a = start
        · subst heq; exact hc
        · exact ih (start := start + 1) hchk (by omega) (by omega)
      · simp at hchk

/-- Check `sumListNat` of every row summed over a `List (List ℕ)` matrix. -/
private def sumMatNatAux : List (List ℕ) → ℕ → ℕ
  | [], acc => acc
  | r :: rs, acc => sumMatNatAux rs (Nat.add acc (sumListNat r))

private def sumMatNat (M : List (List ℕ)) : ℕ := sumMatNatAux M 0

private theorem sumMatNat_eq {n : ℕ} {M : List (List ℕ)} (hM : M.length = n)
    (hMr : ∀ r ∈ M, r.length = n) :
    sumMatNat M = ∑ a : Fin n, ∑ b : Fin n, matAt M a.1 b.1 := by
  have haux : ∀ (m : ℕ) (A : List (List ℕ)), A.length = m → (∀ r ∈ A, r.length = n) →
      ∀ acc : ℕ, sumMatNatAux A acc = acc + ∑ a : Fin m, ∑ b : Fin n, matAt A a.1 b.1 := by
    intro m
    induction m with
    | zero =>
        intro A hA _ acc; cases A with | nil => simp [sumMatNatAux] | cons => simp at hA
    | succ m ih =>
        intro A hA hAr acc
        cases A with
        | nil => simp at hA
        | cons row rest =>
            change sumMatNatAux rest (acc + sumListNat row) = _
            rw [ih rest (by simpa using hA) (fun r hr => hAr r (List.mem_cons_of_mem _ hr)),
              sumListNat_eq (hAr row List.mem_cons_self), Fin.sum_univ_succ]
            change acc + (∑ i : Fin n, vecAt row i.1) + ∑ a : Fin m, ∑ b : Fin n,
                matAt rest a.1 b.1 =
              acc + ((∑ b : Fin n, vecAt row b.1) + ∑ a : Fin m, ∑ b : Fin n,
                matAt rest a.1 b.1)
            omega
  simpa [sumMatNat] using haux n M hM hMr 0

/-- Soundness of the Frobenius inner product rounded down and rounded up. -/
private theorem frobDotDn_le {n s : ℕ} (hs : 0 < s)
    {M R : List (List ℕ)} {Mr Rr : Fin n → Fin n → ℝ}
    (hM : M.length = n) (hR : R.length = n)
    (hMr : ∀ r ∈ M, r.length = n) (hRr : ∀ r ∈ R, r.length = n)
    (hMb : ∀ a b : Fin n, (matAt M a.1 b.1 : ℝ) / s ≤ Mr a b)
    (hRb : ∀ a b : Fin n, (matAt R a.1 b.1 : ℝ) / s ≤ Rr a b) :
    (Nat.div (frobDotNat M R) s : ℝ) / s ≤ ∑ a : Fin n, ∑ b : Fin n, Mr a b * Rr a b := by
  have hd := natDiv_cast_le (a := frobDotNat M R) hs
  have hf := frobDotNat_eq hM hR hMr hRr
  calc (Nat.div (frobDotNat M R) s : ℝ) / s
      ≤ (frobDotNat M R : ℝ) / s / s :=
        div_le_div_of_nonneg_right hd (Nat.cast_nonneg s)
    _ = ∑ a : Fin n, ∑ b : Fin n,
          ((matAt M a.1 b.1 : ℝ) / s) * ((matAt R a.1 b.1 : ℝ) / s) := by
        rw [hf, Nat.cast_sum, Finset.sum_div, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Nat.cast_sum, Finset.sum_div, Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => by push_cast; ring
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, Mr a b * Rr a b :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          mul_le_mul (hMb a b) (hRb a b) (by positivity)
            ((by positivity : (0 : ℝ) ≤ _).trans (hMb a b))

private theorem le_frobDotUp {n s : ℕ} (hs : 0 < s)
    {M R : List (List ℕ)} {Mr Rr : Fin n → Fin n → ℝ}
    (hM : M.length = n) (hR : R.length = n)
    (hMr : ∀ r ∈ M, r.length = n) (hRr : ∀ r ∈ R, r.length = n)
    (hM0 : ∀ a b : Fin n, 0 ≤ Mr a b) (hR0 : ∀ a b : Fin n, 0 ≤ Rr a b)
    (hMb : ∀ a b : Fin n, Mr a b ≤ (matAt M a.1 b.1 : ℝ) / s)
    (hRb : ∀ a b : Fin n, Rr a b ≤ (matAt R a.1 b.1 : ℝ) / s) :
    ∑ a : Fin n, ∑ b : Fin n, Mr a b * Rr a b ≤
      (Nat.div (Nat.add (frobDotNat M R) (Nat.sub s 1)) s : ℝ) / s := by
  have hd := le_natDivUp_cast (a := frobDotNat M R) hs
  have hf := frobDotNat_eq hM hR hMr hRr
  calc ∑ a : Fin n, ∑ b : Fin n, Mr a b * Rr a b
      ≤ ∑ a : Fin n, ∑ b : Fin n,
          ((matAt M a.1 b.1 : ℝ) / s) * ((matAt R a.1 b.1 : ℝ) / s) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          mul_le_mul (hMb a b) (hRb a b) (hR0 a b) ((hM0 a b).trans (hMb a b))
    _ = (frobDotNat M R : ℝ) / s / s := by
        rw [hf, Nat.cast_sum, Finset.sum_div, Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Nat.cast_sum, Finset.sum_div, Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => by push_cast; ring
    _ ≤ (Nat.div (Nat.add (frobDotNat M R) (Nat.sub s 1)) s : ℝ) / s :=
        div_le_div_of_nonneg_right hd (Nat.cast_nonneg s)

/-- Helper to check all row lengths in a matrix equal `n`. -/
private def checkShape (M : List (List ℕ)) (n : ℕ) : Bool :=
  Nat.beq M.length n && M.all (fun row => Nat.beq row.length n)

private theorem checkShape_spec {M : List (List ℕ)} {n : ℕ} (h : checkShape M n = true) :
    M.length = n ∧ ∀ r ∈ M, r.length = n := by
  unfold checkShape at h
  rw [Bool.and_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun r hr => ?_⟩
  exact Nat.eq_of_beq_eq_true ((List.all_eq_true.mp h.2) r hr)

private theorem checkShape_getD {M : List (List ℕ)} {n : ℕ} (h : checkShape M n = true)
    (a : Fin n) : (M.getD a.1 []).length = n := by
  obtain ⟨hL, hR⟩ := checkShape_spec h
  have ha : a.1 < M.length := by rw [hL]; exact a.isLt
  have hmem : M.getD a.1 [] ∈ M := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, Option.getD_some]
    exact List.getElem_mem ha
  exact hR _ hmem

end FixedPointSoundness

/-! ### Certified `N = 19`, `J = 13` interval quadrature proof -/

section VerifiedCertificate

private theorem fin9_all {P : Fin 9 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) : ∀ i : Fin 9, P i := by
  rintro ⟨v, hv⟩; interval_cases v <;> assumption

private theorem fin19_all {P : Fin 19 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9)
    (h10 : P 10) (h11 : P 11) (h12 : P 12) (h13 : P 13) (h14 : P 14)
    (h15 : P 15) (h16 : P 16) (h17 : P 17) (h18 : P 18) : ∀ i : Fin 19, P i := by
  rintro ⟨v, hv⟩; interval_cases v <;> assumption

private def certS : ℕ := 100000000000000
private def certRatio : ℕ := 10000
private def certT : ℕ := 1000000000000000000
private def certD : ℕ := 10000000000000000000000
private def certM : ℕ := 8
private def s2Lo : ℕ := 1414213562373095048
private def s2Hi : ℕ := 1414213562373095049
private def c2Lo : ℕ := 47746482927568
private def c2Hi : ℕ := 47746482927569
private def k2Lo : ℕ := 276395319577068
private def k2Hi : ℕ := 276395319577069
private def a19LCM : ℕ := 14549535
private def mQpp19 : ℕ := 205544706232320
private def mAp19 : ℕ := 343531183703188684800

private theorem s2_lo_le : (s2Lo : ℝ) / certT ≤ Real.sqrt 2 := by
  refine le_of_sq_le_sq ?_ (Real.sqrt_nonneg 2)
  rw [div_pow, Real.sq_sqrt (by norm_num), div_le_iff₀ (by norm_num [certT])]
  norm_num [s2Lo, certT]

private theorem le_s2_hi : Real.sqrt 2 ≤ (s2Hi : ℝ) / certT := by
  have hsq : Real.sqrt 2 ^ 2 ≤ ((s2Hi : ℝ) / certT) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num), le_div_iff₀ (by norm_num [certT])]
    norm_num [s2Hi, certT]
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

private theorem c2_lo_le : (c2Lo : ℝ) / certS ≤ 3 / (2 * Real.pi) := by
  have hpi := Real.pi_lt_d20
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_le_div_iff₀ (by norm_num [certS]) (by positivity)]
  unfold c2Lo certS; push_cast; nlinarith

private theorem le_c2_hi : 3 / (2 * Real.pi) ≤ (c2Hi : ℝ) / certS := by
  have hpi := Real.pi_gt_d20
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [div_le_div_iff₀ (by positivity) (by norm_num [certS])]
  unfold c2Hi certS; push_cast; nlinarith

private theorem k2_lo_le : (k2Lo : ℝ) / certS ≤ 2 * Real.sqrt (6 / Real.pi) := by
  have hpi := Real.pi_lt_d20
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : ((k2Lo : ℝ) / certS) ^ 2 ≤ (2 * Real.sqrt (6 / Real.pi)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), div_pow]
    rw [show (2 : ℝ) ^ 2 * (6 / Real.pi) = 24 / Real.pi by ring]
    rw [div_le_div_iff₀ (by norm_num [certS]) hpi0]
    unfold k2Lo certS; push_cast; nlinarith
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

private theorem le_k2_hi : 2 * Real.sqrt (6 / Real.pi) ≤ (k2Hi : ℝ) / certS := by
  have hpi := Real.pi_gt_d20
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (2 * Real.sqrt (6 / Real.pi)) ^ 2 ≤ ((k2Hi : ℝ) / certS) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), div_pow]
    rw [show (2 : ℝ) ^ 2 * (6 / Real.pi) = 24 / Real.pi by ring]
    rw [div_le_div_iff₀ hpi0 (by norm_num [certS])]
    unfold k2Hi certS; push_cast; nlinarith
  exact (abs_le_of_sq_le_sq' hsq (by positivity)).2

private def q19Pos : List ℕ :=
  [0, 0, 0, 116396280, 0, 0, 0, 17847429600, 0, 0, 0, 211735414800, 0, 0, 0, 317370445920, 0, 0,
   0, 35345263800]
private def q19Neg : List ℕ :=
  [0, 1847560, 0, 0, 0, 2141691552, 0, 0, 0, 80313433200, 0, 0, 0, 336605018400, 0, 0, 0,
   163352435400, 0, 0]
private def d19Pos : List ℕ :=
  [0, 0, 349188840, 0, 0, 0, 124932007200, 0, 0, 0, 2329089562800, 0, 0, 0, 4760556688800, 0, 0,
   0, 671560012200]
private def d19Neg : List ℕ :=
  [1847560, 0, 0, 0, 10708457760, 0, 0, 0, 722820898800, 0, 0, 0, 4375865239200, 0, 0, 0,
   2776991401800, 0, 0]
private def a19Pos : List ℕ :=
  [0, 0, 768809858760720, 0, 0, 0, 246439002049732800, 0, 0, 0, 4178597949965318880, 0, 0, 0,
   7856419698729201600, 0, 0, 0, 1028514305484666000]
private def a19Neg : List ℕ :=
  [4329327034368, 0, 0, 0, 22267728848312640, 0, 0, 0, 1357599504416126400, 0, 0, 0,
   7520248227592900800, 0, 0, 0, 4410565850546856000, 0, 0]

private def facRec : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => facRec n (Nat.mul (n + 1) acc)

private theorem facRec_eq (n acc : ℕ) : facRec n acc = Nat.factorial n * acc := by
  induction n generalizing acc with
  | zero => simp [facRec]
  | succ n ih =>
      change facRec n ((n + 1) * acc) = _
      rw [ih, Nat.factorial_succ]; ring

private theorem factorial_eq_facRec (n : ℕ) : Nat.factorial n = facRec n 1 := by
  rw [facRec_eq, mul_one]

private def chooseFast (n r : ℕ) : ℕ :=
  Nat.div (facRec n 1) (Nat.mul (facRec r 1) (facRec (Nat.sub n r) 1))

private theorem choose_eq_chooseFast {n r : ℕ} (h : r ≤ n) : Nat.choose n r = chooseFast n r := by
  rw [Nat.choose_eq_factorial_div_factorial h, factorial_eq_facRec, factorial_eq_facRec,
    factorial_eq_facRec]; rfl

private theorem q19_binom_eq (k : Fin 10) :
    Nat.choose 19 k.1 * Nat.choose (38 - 2 * k.1) 19 =
      (if Even k.1 then vecAt q19Pos (19 - 2 * k.1) else vecAt q19Neg (19 - 2 * k.1)) := by
  have h1 : k.1 ≤ 19 := by omega
  have h2 : 19 ≤ 38 - 2 * k.1 := by omega
  rw [choose_eq_chooseFast h1, choose_eq_chooseFast h2]
  fin_cases k
  · have hev : Even (0 : ℕ) := by decide
    change _ = if Even (0 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : ¬ Even (1 : ℕ) := by decide
    change _ = if Even (1 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : Even (2 : ℕ) := by decide
    change _ = if Even (2 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : ¬ Even (3 : ℕ) := by decide
    change _ = if Even (3 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : Even (4 : ℕ) := by decide
    change _ = if Even (4 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : ¬ Even (5 : ℕ) := by decide
    change _ = if Even (5 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : Even (6 : ℕ) := by decide
    change _ = if Even (6 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : ¬ Even (7 : ℕ) := by decide
    change _ = if Even (7 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : Even (8 : ℕ) := by decide
    change _ = if Even (8 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl
  · have hev : ¬ Even (9 : ℕ) := by decide
    change _ = if Even (9 : ℕ) then _ else _
    simp only [hev, ↓reduceIte]
    rfl

private theorem natListPoly_coeff (cs : List ℕ) (m : ℕ) :
    (natListPoly cs).coeff m = if m < cs.length then (cs.getD m 0 : ℝ) else 0 := by
  unfold natListPoly
  rw [coeff_finset_sum_eq]
  by_cases hm : m < cs.length
  · rw [ite_eq_left_iff.mpr fun h => (h hm).elim]
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hjm; simp [hjm.symm]
    · intro h; exact (h (Finset.mem_range.mpr hm)).elim
  · rw [ite_eq_right_iff.mpr fun h => (hm h).elim]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hne : m ≠ j := fun heq => hm (heq ▸ Finset.mem_range.mp hj)
    simp [hne]

private theorem q19_coeff_nat (m : ℕ) :
    (legendreScaled 19).coeff m =
      (if m < 20 then (vecAt q19Pos m : ℝ) - (vecAt q19Neg m : ℝ) else 0) := by
  unfold legendreScaled
  rw [coeff_finset_sum_eq, show 19 / 2 + 1 = 10 by rfl]
  by_cases hm : m < 20
  · rw [ite_eq_left_iff.mpr fun h => (h hm).elim]
    by_cases hodd : Odd m
    · have hklt : (19 - m) / 2 < 10 := by omega
      have hkm : 19 - 2 * ((19 - m) / 2) = m := by rcases hodd with ⟨t, ht⟩; omega
      let k0 : Fin 10 := ⟨(19 - m) / 2, hklt⟩
      rw [Finset.sum_eq_single k0.1]
      · rw [Polynomial.coeff_C_mul_X_pow,
          ite_eq_left_iff.mpr fun h => (h hkm.symm).elim, mul_assoc]
        have hmul : (Nat.choose 19 k0.1 : ℝ) * (Nat.choose (2 * 19 - 2 * k0.1) 19 : ℝ) =
            ((Nat.choose 19 k0.1 * Nat.choose (38 - 2 * k0.1) 19 : ℕ) : ℝ) := by
          push_cast; rfl
        rw [hmul, q19_binom_eq k0, hkm]
        have hdisj : ∀ j : ℕ, j < 10 →
            (if j % 2 = 0 then vecAt q19Neg (19 - 2 * j)
            else vecAt q19Pos (19 - 2 * j)) = 0 := by
          intro j hj; interval_cases j <;> rfl
        have hd0 := hdisj k0.1 k0.isLt
        rw [hkm] at hd0
        rcases Nat.even_or_odd k0.1 with he | ho
        · have hmod : k0.1 % 2 = 0 := Nat.even_iff.mp he
          have hneg0 : vecAt q19Neg m = 0 := by simpa [hmod] using hd0
          simp only [he, ↓reduceIte, he.neg_one_pow, one_mul, hneg0, Nat.cast_zero, sub_zero]
        · have hne : ¬ Even k0.1 := Nat.not_even_iff_odd.mpr ho
          have hmod : ¬ (k0.1 % 2 = 0) := by rwa [← Nat.even_iff]
          have hpos0 : vecAt q19Pos m = 0 := by simpa [hmod] using hd0
          simp only [hne, ↓reduceIte, ho.neg_one_pow, hpos0, Nat.cast_zero, zero_sub]
          ring
      · intro j hj hne
        have hjlt := Finset.mem_range.mp hj
        rw [Polynomial.coeff_C_mul_X_pow]
        exact ite_eq_right_iff.mpr fun h => (hne (by change j = (19 - m) / 2; omega)).elim
      · intro h; exact (h (Finset.mem_range.mpr hklt)).elim
    · have hev : Even m := Nat.not_odd_iff_even.mp hodd
      have hz : ∀ k ∈ Finset.range 10, (Polynomial.C ((-1 : ℝ) ^ k *
          (Nat.choose 19 k : ℝ) * (Nat.choose (2 * 19 - 2 * k) 19 : ℝ)) *
          Polynomial.X ^ (19 - 2 * k)).coeff m = 0 := fun k hk => by
        have hklt : k < 10 := Finset.mem_range.mp hk
        rw [Polynomial.coeff_C_mul_X_pow]
        exact ite_eq_right_iff.mpr fun h => by
          exfalso; rcases hev with ⟨t, ht⟩; omega
      have hp0 : vecAt q19Pos m = 0 ∧ vecAt q19Neg m = 0 := by
        interval_cases m <;> first | (exfalso; revert hodd; decide) | exact ⟨rfl, rfl⟩
      rw [Finset.sum_eq_zero hz, hp0.1, hp0.2]; simp
  · rw [ite_eq_right_iff.mpr fun h => (hm h).elim]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    exact ite_eq_right_iff.mpr fun h => by exfalso; omega

private theorem q19_eq : legendreScaled 19 = natListPoly q19Pos - natListPoly q19Neg := by
  ext m
  rw [Polynomial.coeff_sub, q19_coeff_nat, natListPoly_coeff, natListPoly_coeff]
  change _ = (if m < 20 then (vecAt q19Pos m : ℝ) else 0) -
    (if m < 20 then (vecAt q19Neg m : ℝ) else 0)
  split_ifs <;> ring

private theorem d19_coeff_ok (m : Fin 19) :
    (m.1 + 1) * vecAt q19Pos (m.1 + 1) = vecAt d19Pos m.1 ∧
    (m.1 + 1) * vecAt q19Neg (m.1 + 1) = vecAt d19Neg m.1 := by
  fin_cases m <;> exact ⟨rfl, rfl⟩

private theorem d19_eq :
    (legendreScaled 19).derivative = natListPoly d19Pos - natListPoly d19Neg := by
  ext m
  rw [Polynomial.coeff_sub, Polynomial.coeff_derivative, q19_coeff_nat,
    natListPoly_coeff, natListPoly_coeff]
  by_cases hm : m < 19
  · have hm1 : m + 1 < 20 := by omega
    have ⟨hp, hn⟩ := d19_coeff_ok ⟨m, hm⟩
    have hlp : d19Pos.length = 19 := rfl
    have hln : d19Neg.length = 19 := rfl
    simp only [hm, hm1, hlp, hln, ↓reduceIte]
    have hpR : (vecAt d19Pos m : ℝ) = ((m + 1 : ℕ) : ℝ) * (vecAt q19Pos (m + 1) : ℝ) := by
      exact_mod_cast hp.symm
    have hnR : (vecAt d19Neg m : ℝ) = ((m + 1 : ℕ) : ℝ) * (vecAt q19Neg (m + 1) : ℝ) := by
      exact_mod_cast hn.symm
    change ((vecAt q19Pos (m + 1) : ℝ) - vecAt q19Neg (m + 1)) * (m + 1 : ℝ) =
      (vecAt d19Pos m : ℝ) - vecAt d19Neg m
    rw [hpR, hnR]; push_cast; ring
  · have hm1 : ¬ m + 1 < 20 := by omega
    have hlp : d19Pos.length = 19 := rfl
    have hln : d19Neg.length = 19 := rfl
    simp [hm, hm1, hlp, hln]


private def a19SumAux (q : List ℕ) (m j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | j' + 1 =>
      let cur := if Nat.ble (m + 1) j' && Nat.beq (Nat.mod (Nat.sub (Nat.sub j' 1) m) 2) 0
        then Nat.mul (vecAt q j') (Nat.mul 2 (Nat.div a19LCM (Nat.sub j' m))) else 0
      Nat.add (a19SumAux q m j') cur

private theorem a19SumAux_eq (q : List ℕ) (m k : ℕ) :
    a19SumAux q m k = ∑ j ∈ Finset.range k,
      if m < j ∧ (j - 1 - m) % 2 = 0
      then vecAt q j * (2 * (a19LCM / (j - m))) else 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change a19SumAux q m k + _ = _
      rw [ih, Finset.sum_range_succ]
      congr 1
      by_cases h1 : m < k
      · have hb1 : Nat.ble (m + 1) k = true := Nat.ble_eq_true_of_le (by omega)
        by_cases h2 : (k - 1 - m) % 2 = 0
        · have hb2 : Nat.beq (Nat.mod (Nat.sub (Nat.sub k 1) m) 2) 0 = true :=
            Nat.beq_eq.mpr h2
          simp only [h1, h2, hb1, hb2, Bool.and_self, and_self, ↓reduceIte]; rfl
        · have hb2 : Nat.beq (Nat.mod (Nat.sub (Nat.sub k 1) m) 2) 0 = false := by
            cases h : Nat.beq (Nat.mod (Nat.sub (Nat.sub k 1) m) 2) 0 with
            | false => rfl
            | true => exact (h2 (Nat.eq_of_beq_eq_true h)).elim
          simp only [hb1, hb2, Bool.and_false, Bool.false_eq_true, ↓reduceIte, h2, and_false]
      · have hb1 : Nat.ble (m + 1) k = false := by
          cases h : Nat.ble (m + 1) k with
          | false => rfl
          | true => exact (h1 (Nat.le_of_ble_eq_true h)).elim
        simp [h1, hb1]

private theorem a19_coeff_ok :
    ∀ m : Fin 19, Nat.beq (Nat.add (a19SumAux q19Pos m.1 20) (vecAt a19Neg m.1))
      (Nat.add (a19SumAux q19Neg m.1 20) (vecAt a19Pos m.1)) = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl

private theorem a19_lcm_div (d : ℕ) (hd : d < 20) (ho : d % 2 = 1) :
    a19LCM / d * d = a19LCM := by
  interval_cases d <;> first | (exfalso; omega) | rfl

private theorem a19_eq :
    Polynomial.C (a19LCM : ℝ) * cauchyIntPoly (legendreScaled 19) =
      natListPoly a19Pos - natListPoly a19Neg := by
  ext m
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, natListPoly_coeff, natListPoly_coeff]
  have hlp : a19Pos.length = 19 := rfl
  have hln : a19Neg.length = 19 := rfl
  rw [hlp, hln]
  unfold cauchyIntPoly
  rw [legendreScaled_natDegree 19, coeff_finset_sum_eq, Finset.mul_sum]
  have hterm : ∀ j : ℕ, (a19LCM : ℝ) * (Polynomial.C ((legendreScaled 19).coeff j) *
      ∑ i ∈ Finset.range j, if Even i then
        Polynomial.C (2 / (i + 1 : ℝ)) * Polynomial.X ^ (j - 1 - i) else 0).coeff m =
      (legendreScaled 19).coeff j * ∑ i ∈ Finset.range j,
        if Even i ∧ j - 1 - i = m then (2 * a19LCM : ℝ) / (i + 1 : ℝ) else 0 := by
    intro j
    rw [Polynomial.coeff_C_mul, coeff_finset_sum_eq, ← mul_assoc,
      mul_comm (a19LCM : ℝ) ((legendreScaled 19).coeff j), mul_assoc, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun i _ => ?_
    by_cases he : Even i
    · by_cases hidx : j - 1 - i = m
      · simp only [he, hidx, and_self, ↓reduceIte, Polynomial.coeff_C_mul_X_pow]; ring
      · simp only [he, hidx, and_false, ↓reduceIte, Polynomial.coeff_C_mul_X_pow]
        have hne : m ≠ j - 1 - i := fun h => hidx h.symm
        simp only [hne, ↓reduceIte, mul_zero]
    · simp [he]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  by_cases hm : m < 19
  · rw [ite_eq_left_iff.mpr fun h => (h hm).elim]
    have hm_sum : ∀ j ∈ Finset.range 20,
        (legendreScaled 19).coeff j * ∑ i ∈ Finset.range j,
          (if Even i ∧ j - 1 - i = m then (2 * a19LCM : ℝ) / (i + 1 : ℝ) else 0) =
        (if m < j ∧ (j - 1 - m) % 2 = 0 then
          ((vecAt q19Pos j * (2 * (a19LCM / (j - m))) : ℕ) : ℝ) -
          ((vecAt q19Neg j * (2 * (a19LCM / (j - m))) : ℕ) : ℝ) else 0) := by
      intro j hj
      have hjlt : j < 20 := Finset.mem_range.mp hj
      rw [q19_coeff_nat, ite_eq_left_iff.mpr fun h => (h hjlt).elim]
      by_cases hcond : m < j ∧ (j - 1 - m) % 2 = 0
      · rw [ite_eq_left_iff.mpr fun h => (h hcond).elim]
        have hev : Even (j - 1 - m) := Nat.even_iff.mpr hcond.2
        have hs : ∑ i ∈ Finset.range j,
            (if Even i ∧ j - 1 - i = m then (2 * a19LCM : ℝ) / (i + 1 : ℝ) else 0) =
            (2 * a19LCM : ℝ) / (j - m : ℕ) := by
          rw [Finset.sum_eq_single (j - 1 - m)]
          · have hi1 : j - 1 - (j - 1 - m) = m := by omega
            simp only [hev, hi1, and_self, ↓reduceIte]
            congr 1; exact_mod_cast (show j - 1 - m + 1 = j - m by omega)
          · intro i hi hne; have := Finset.mem_range.mp hi
            exact ite_eq_right_iff.mpr fun h => (hne (by omega)).elim
          · intro h; exact (h (Finset.mem_range.mpr (by omega))).elim
        have hdiv : ((2 * (a19LCM / (j - m)) : ℕ) : ℝ) = (2 * a19LCM : ℝ) / (j - m : ℕ) := by
          have hnz : ((j - m : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (show j - m ≠ 0 by omega)
          rw [eq_div_iff hnz]
          have hmod : a19LCM / (j - m) * (j - m) = a19LCM :=
            a19_lcm_div (j - m) (by omega) (by omega)
          push_cast; rw [mul_assoc, ← Nat.cast_mul, hmod]
        rw [hs, ← hdiv]; push_cast; ring
      · rw [ite_eq_right_iff.mpr fun h => (hcond h).elim]
        have hz : ∑ i ∈ Finset.range j,
            (if Even i ∧ j - 1 - i = m then (2 * a19LCM : ℝ) / (i + 1 : ℝ) else 0) = 0 :=
          Finset.sum_eq_zero fun i hi => by
            have := Finset.mem_range.mp hi
            exact ite_eq_right_iff.mpr fun h => (hcond ⟨by omega, by
              have he := Nat.even_iff.mp h.1; omega⟩).elim
        rw [hz, mul_zero]
    rw [Finset.sum_congr rfl hm_sum]
    have hsp : ∀ j : ℕ, (if m < j ∧ (j - 1 - m) % 2 = 0 then
        ((vecAt q19Pos j * (2 * (a19LCM / (j - m))) : ℕ) : ℝ) -
        ((vecAt q19Neg j * (2 * (a19LCM / (j - m))) : ℕ) : ℝ) else 0) =
      ((if m < j ∧ (j - 1 - m) % 2 = 0 then vecAt q19Pos j * (2 * (a19LCM / (j - m)))
        else 0 : ℕ) : ℝ) -
      ((if m < j ∧ (j - 1 - m) % 2 = 0 then vecAt q19Neg j * (2 * (a19LCM / (j - m)))
        else 0 : ℕ) : ℝ) := fun j => by split_ifs <;> simp
    simp_rw [hsp, Finset.sum_sub_distrib, ← Nat.cast_sum]
    rw [← a19SumAux_eq q19Pos m 20, ← a19SumAux_eq q19Neg m 20]
    have heq : a19SumAux q19Pos m 20 + vecAt a19Neg m =
        a19SumAux q19Neg m 20 + vecAt a19Pos m :=
      Nat.eq_of_beq_eq_true (a19_coeff_ok ⟨m, hm⟩)
    have heqR : (a19SumAux q19Pos m 20 : ℝ) + (vecAt a19Neg m : ℝ) =
        (a19SumAux q19Neg m 20 : ℝ) + (vecAt a19Pos m : ℝ) := by exact_mod_cast heq
    rw [ite_eq_left_iff.mpr fun h => (h hm).elim]
    change _ = (vecAt a19Pos m : ℝ) - (vecAt a19Neg m : ℝ)
    linarith
  · simp only [hm, ↓reduceIte, sub_self]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hz : ∑ i ∈ Finset.range j,
        (if Even i ∧ j - 1 - i = m then (2 * a19LCM : ℝ) / (i + 1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => ite_eq_right_iff.mpr fun h => by
        have := Finset.mem_range.mp hi; exfalso; omega
    rw [hz, mul_zero]

private def lipSumAux (cp cn : List ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => Nat.add (lipSumAux cp cn k) (Nat.mul k (Nat.add (vecAt cp k) (vecAt cn k)))

private theorem lipSumAux_eq (cp cn : List ℕ) (k : ℕ) :
    (lipSumAux cp cn k : ℝ) =
      ∑ j ∈ Finset.range k, (j : ℝ) * ((vecAt cp j : ℝ) + (vecAt cn j : ℝ)) := by
  induction k with
  | zero => simp [lipSumAux]
  | succ k ih =>
      change ((lipSumAux cp cn k + k * (vecAt cp k + vecAt cn k) : ℕ) : ℝ) = _
      rw [Nat.cast_add, ih, Finset.sum_range_succ]; push_cast; ring

private theorem d19_lip_le :
    ∑ j ∈ Finset.range ((legendreScaled 19).derivative.natDegree + 1),
      (j : ℝ) * |(legendreScaled 19).derivative.coeff j| ≤ (mQpp19 : ℝ) := by
  have hdeg : (legendreScaled 19).derivative.natDegree ≤ 18 :=
    (Polynomial.natDegree_derivative_le _).trans (by rw [legendreScaled_natDegree 19])
  have hsub : ∑ j ∈ Finset.range ((legendreScaled 19).derivative.natDegree + 1),
      (j : ℝ) * |(legendreScaled 19).derivative.coeff j| ≤
      ∑ j ∈ Finset.range 19, (j : ℝ) * ((vecAt d19Pos j : ℝ) + (vecAt d19Neg j : ℝ)) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun _ _ _ => by positivity).trans (Finset.sum_le_sum fun j hj => ?_)
    have hjlt := Finset.mem_range.mp hj
    rw [d19_eq, Polynomial.coeff_sub, natListPoly_coeff, natListPoly_coeff]
    have hlp : d19Pos.length = 19 := rfl; have hln : d19Neg.length = 19 := rfl
    simp only [hlp, hln, hjlt, ↓reduceIte]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact (abs_sub _ _).trans_eq (by
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]; rfl)
  refine hsub.trans ?_
  rw [← lipSumAux_eq]
  have hchk : lipSumAux d19Pos d19Neg 19 = mQpp19 := rfl
  rw [hchk]

private theorem a19_lip_le :
    ∑ j ∈ Finset.range ((Polynomial.C (a19LCM : ℝ) *
      cauchyIntPoly (legendreScaled 19)).natDegree + 1),
      (j : ℝ) * |(Polynomial.C (a19LCM : ℝ) *
        cauchyIntPoly (legendreScaled 19)).coeff j| ≤ (mAp19 : ℝ) := by
  have hdeg : (Polynomial.C (a19LCM : ℝ) *
      cauchyIntPoly (legendreScaled 19)).natDegree ≤ 18 := by
    rw [a19_eq]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    all_goals
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
      rw [natListPoly_coeff]; split_ifs with h
      · exfalso; change n < 19 at h; omega
      · rfl
  have hsub : ∑ j ∈ Finset.range ((Polynomial.C (a19LCM : ℝ) *
      cauchyIntPoly (legendreScaled 19)).natDegree + 1),
      (j : ℝ) * |(Polynomial.C (a19LCM : ℝ) *
        cauchyIntPoly (legendreScaled 19)).coeff j| ≤
      ∑ j ∈ Finset.range 19, (j : ℝ) * ((vecAt a19Pos j : ℝ) + (vecAt a19Neg j : ℝ)) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun _ _ _ => by positivity).trans (Finset.sum_le_sum fun j hj => ?_)
    have hjlt := Finset.mem_range.mp hj
    rw [a19_eq, Polynomial.coeff_sub, natListPoly_coeff, natListPoly_coeff]
    have hlp : a19Pos.length = 19 := rfl; have hln : a19Neg.length = 19 := rfl
    simp only [hlp, hln, hjlt, ↓reduceIte]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact (abs_sub _ _).trans_eq (by
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]; rfl)
  refine hsub.trans ?_
  rw [← lipSumAux_eq]
  have hchk : lipSumAux a19Pos a19Neg 19 = mAp19 := rfl
  rw [hchk]

private theorem q19_eval_sign_pos {p : ℕ}
    (h : Nat.ble (Nat.add (evalHom q19Neg p certD) 1) (evalHom q19Pos p certD) = true) :
    0 < (legendreScaled 19).eval ((p : ℝ) / certD) := by
  have hD : 0 < certD := by decide
  have hDR : (0 : ℝ) < (certD : ℝ) ^ 19 := by positivity
  have hlt : (evalHom q19Neg p certD : ℝ) < (evalHom q19Pos p certD : ℝ) := by
    have hle : evalHom q19Neg p certD + 1 ≤ evalHom q19Pos p certD :=
      Nat.le_of_ble_eq_true h
    have : evalHom q19Neg p certD < evalHom q19Pos p certD := by omega
    exact Nat.cast_lt.mpr this
  rw [evalHom_eq (by decide : q19Neg ≠ []) p hD,
    evalHom_eq (by decide : q19Pos ≠ []) p hD] at hlt
  have h1 : q19Neg.length - 1 = 19 := rfl
  have h2 : q19Pos.length - 1 = 19 := rfl
  rw [h1, h2] at hlt
  rw [q19_eq, Polynomial.eval_sub]
  nlinarith

private theorem q19_eval_sign_neg {p : ℕ}
    (h : Nat.ble (Nat.add (evalHom q19Pos p certD) 1) (evalHom q19Neg p certD) = true) :
    (legendreScaled 19).eval ((p : ℝ) / certD) < 0 := by
  have hD : 0 < certD := by decide
  have hDR : (0 : ℝ) < (certD : ℝ) ^ 19 := by positivity
  have hlt : (evalHom q19Pos p certD : ℝ) < (evalHom q19Neg p certD : ℝ) := by
    have hle : evalHom q19Pos p certD + 1 ≤ evalHom q19Neg p certD :=
      Nat.le_of_ble_eq_true h
    have : evalHom q19Pos p certD < evalHom q19Neg p certD := by omega
    exact Nat.cast_lt.mpr this
  rw [evalHom_eq (by decide : q19Pos ≠ []) p hD,
    evalHom_eq (by decide : q19Neg ≠ []) p hD] at hlt
  have h1 : q19Pos.length - 1 = 19 := rfl
  have h2 : q19Neg.length - 1 = 19 := rfl
  rw [h1, h2] at hlt
  rw [q19_eq, Polynomial.eval_sub]
  nlinarith

private theorem exists_q19_root_up {lo hi : ℕ} (h : lo < hi)
    (hlo : (legendreScaled 19).eval ((lo : ℝ) / certD) < 0)
    (hhi : 0 < (legendreScaled 19).eval ((hi : ℝ) / certD)) :
    ∃ r ∈ Set.Ioo ((lo : ℝ) / certD) ((hi : ℝ) / certD),
      (legendreScaled 19).eval r = 0 := by
  have hlt : (lo : ℝ) / certD < (hi : ℝ) / certD := by
    gcongr; norm_num [certD]
  have h0 : (0 : ℝ) ∈ Set.Ioo ((legendreScaled 19).eval ((lo : ℝ) / certD))
      ((legendreScaled 19).eval ((hi : ℝ) / certD)) := ⟨hlo, hhi⟩
  obtain ⟨r, hr, hrv⟩ := intermediate_value_Ioo hlt.le
    (poly_continuous (legendreScaled 19)).continuousOn h0
  exact ⟨r, hr, hrv⟩

private theorem exists_q19_root_dn {lo hi : ℕ} (h : lo < hi)
    (hlo : 0 < (legendreScaled 19).eval ((lo : ℝ) / certD))
    (hhi : (legendreScaled 19).eval ((hi : ℝ) / certD) < 0) :
    ∃ r ∈ Set.Ioo ((lo : ℝ) / certD) ((hi : ℝ) / certD),
      (legendreScaled 19).eval r = 0 := by
  have hlt : (lo : ℝ) / certD < (hi : ℝ) / certD := by
    gcongr; norm_num [certD]
  have hcont : ContinuousOn (fun t : ℝ => -(legendreScaled 19).eval t)
      (Set.Icc ((lo : ℝ) / certD) ((hi : ℝ) / certD)) :=
    (poly_continuous (legendreScaled 19)).neg.continuousOn
  have h0 : (0 : ℝ) ∈ Set.Ioo (-(legendreScaled 19).eval ((lo : ℝ) / certD))
      (-(legendreScaled 19).eval ((hi : ℝ) / certD)) := ⟨by linarith, by linarith⟩
  obtain ⟨r, hr, hrv⟩ := intermediate_value_Ioo hlt.le hcont h0
  exact ⟨r, hr, neg_eq_zero.mp hrv⟩

private def posMidList : List ℕ :=
  [1603586456402253758681, 3165640999636298319901, 4645707413759609457173, 6005453046616810234696,
   7209661773352293786171, 8227146565371428249789, 9031559036148179016427, 9602081521348300308528,
   9924068438435844031890]

private theorem rPos_sign_0_lo :
    Nat.ble (Nat.add (evalHom q19Pos 1603586456402253758680 certD) 1)
      (evalHom q19Neg 1603586456402253758680 certD) = true := rfl
private theorem rPos_sign_0_hi :
    Nat.ble (Nat.add (evalHom q19Neg 1603586456402253758682 certD) 1)
      (evalHom q19Pos 1603586456402253758682 certD) = true := rfl
private theorem rPos_ex_0 :
    ∃ r ∈ Set.Ioo ((1603586456402253758680 : ℝ) / certD)
      ((1603586456402253758682 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_up (by decide) (q19_eval_sign_neg rPos_sign_0_lo)
    (q19_eval_sign_pos rPos_sign_0_hi)
private theorem rPos_sign_1_lo :
    Nat.ble (Nat.add (evalHom q19Neg 3165640999636298319900 certD) 1)
      (evalHom q19Pos 3165640999636298319900 certD) = true := rfl
private theorem rPos_sign_1_hi :
    Nat.ble (Nat.add (evalHom q19Pos 3165640999636298319902 certD) 1)
      (evalHom q19Neg 3165640999636298319902 certD) = true := rfl
private theorem rPos_ex_1 :
    ∃ r ∈ Set.Ioo ((3165640999636298319900 : ℝ) / certD)
      ((3165640999636298319902 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_dn (by decide) (q19_eval_sign_pos rPos_sign_1_lo)
    (q19_eval_sign_neg rPos_sign_1_hi)
private theorem rPos_sign_2_lo :
    Nat.ble (Nat.add (evalHom q19Pos 4645707413759609457172 certD) 1)
      (evalHom q19Neg 4645707413759609457172 certD) = true := rfl
private theorem rPos_sign_2_hi :
    Nat.ble (Nat.add (evalHom q19Neg 4645707413759609457174 certD) 1)
      (evalHom q19Pos 4645707413759609457174 certD) = true := rfl
private theorem rPos_ex_2 :
    ∃ r ∈ Set.Ioo ((4645707413759609457172 : ℝ) / certD)
      ((4645707413759609457174 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_up (by decide) (q19_eval_sign_neg rPos_sign_2_lo)
    (q19_eval_sign_pos rPos_sign_2_hi)
private theorem rPos_sign_3_lo :
    Nat.ble (Nat.add (evalHom q19Neg 6005453046616810234695 certD) 1)
      (evalHom q19Pos 6005453046616810234695 certD) = true := rfl
private theorem rPos_sign_3_hi :
    Nat.ble (Nat.add (evalHom q19Pos 6005453046616810234697 certD) 1)
      (evalHom q19Neg 6005453046616810234697 certD) = true := rfl
private theorem rPos_ex_3 :
    ∃ r ∈ Set.Ioo ((6005453046616810234695 : ℝ) / certD)
      ((6005453046616810234697 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_dn (by decide) (q19_eval_sign_pos rPos_sign_3_lo)
    (q19_eval_sign_neg rPos_sign_3_hi)
private theorem rPos_sign_4_lo :
    Nat.ble (Nat.add (evalHom q19Pos 7209661773352293786170 certD) 1)
      (evalHom q19Neg 7209661773352293786170 certD) = true := rfl
private theorem rPos_sign_4_hi :
    Nat.ble (Nat.add (evalHom q19Neg 7209661773352293786172 certD) 1)
      (evalHom q19Pos 7209661773352293786172 certD) = true := rfl
private theorem rPos_ex_4 :
    ∃ r ∈ Set.Ioo ((7209661773352293786170 : ℝ) / certD)
      ((7209661773352293786172 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_up (by decide) (q19_eval_sign_neg rPos_sign_4_lo)
    (q19_eval_sign_pos rPos_sign_4_hi)
private theorem rPos_sign_5_lo :
    Nat.ble (Nat.add (evalHom q19Neg 8227146565371428249788 certD) 1)
      (evalHom q19Pos 8227146565371428249788 certD) = true := rfl
private theorem rPos_sign_5_hi :
    Nat.ble (Nat.add (evalHom q19Pos 8227146565371428249790 certD) 1)
      (evalHom q19Neg 8227146565371428249790 certD) = true := rfl
private theorem rPos_ex_5 :
    ∃ r ∈ Set.Ioo ((8227146565371428249788 : ℝ) / certD)
      ((8227146565371428249790 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_dn (by decide) (q19_eval_sign_pos rPos_sign_5_lo)
    (q19_eval_sign_neg rPos_sign_5_hi)
private theorem rPos_sign_6_lo :
    Nat.ble (Nat.add (evalHom q19Pos 9031559036148179016426 certD) 1)
      (evalHom q19Neg 9031559036148179016426 certD) = true := rfl
private theorem rPos_sign_6_hi :
    Nat.ble (Nat.add (evalHom q19Neg 9031559036148179016428 certD) 1)
      (evalHom q19Pos 9031559036148179016428 certD) = true := rfl
private theorem rPos_ex_6 :
    ∃ r ∈ Set.Ioo ((9031559036148179016426 : ℝ) / certD)
      ((9031559036148179016428 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_up (by decide) (q19_eval_sign_neg rPos_sign_6_lo)
    (q19_eval_sign_pos rPos_sign_6_hi)
private theorem rPos_sign_7_lo :
    Nat.ble (Nat.add (evalHom q19Neg 9602081521348300308527 certD) 1)
      (evalHom q19Pos 9602081521348300308527 certD) = true := rfl
private theorem rPos_sign_7_hi :
    Nat.ble (Nat.add (evalHom q19Pos 9602081521348300308529 certD) 1)
      (evalHom q19Neg 9602081521348300308529 certD) = true := rfl
private theorem rPos_ex_7 :
    ∃ r ∈ Set.Ioo ((9602081521348300308527 : ℝ) / certD)
      ((9602081521348300308529 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_dn (by decide) (q19_eval_sign_pos rPos_sign_7_lo)
    (q19_eval_sign_neg rPos_sign_7_hi)
private theorem rPos_sign_8_lo :
    Nat.ble (Nat.add (evalHom q19Pos 9924068438435844031889 certD) 1)
      (evalHom q19Neg 9924068438435844031889 certD) = true := rfl
private theorem rPos_sign_8_hi :
    Nat.ble (Nat.add (evalHom q19Neg 9924068438435844031891 certD) 1)
      (evalHom q19Pos 9924068438435844031891 certD) = true := rfl
private theorem rPos_ex_8 :
    ∃ r ∈ Set.Ioo ((9924068438435844031889 : ℝ) / certD)
      ((9924068438435844031891 : ℝ) / certD), (legendreScaled 19).eval r = 0 :=
  exists_q19_root_up (by decide) (q19_eval_sign_neg rPos_sign_8_lo)
    (q19_eval_sign_pos rPos_sign_8_hi)

private noncomputable def rPos19 (k : Fin 9) : ℝ :=
  match k with
  | ⟨0, _⟩ => Classical.choose rPos_ex_0
  | ⟨1, _⟩ => Classical.choose rPos_ex_1
  | ⟨2, _⟩ => Classical.choose rPos_ex_2
  | ⟨3, _⟩ => Classical.choose rPos_ex_3
  | ⟨4, _⟩ => Classical.choose rPos_ex_4
  | ⟨5, _⟩ => Classical.choose rPos_ex_5
  | ⟨6, _⟩ => Classical.choose rPos_ex_6
  | ⟨7, _⟩ => Classical.choose rPos_ex_7
  | ⟨8, _⟩ => Classical.choose rPos_ex_8

private theorem rPos19_spec (k : Fin 9) :
    rPos19 k ∈ Set.Ioo (((vecAt posMidList k.1 - 1 : ℕ) : ℝ) / certD)
      (((vecAt posMidList k.1 + 1 : ℕ) : ℝ) / certD) ∧
    (legendreScaled 19).eval (rPos19 k) = 0 := by
  fin_cases k
  · exact Classical.choose_spec rPos_ex_0
  · exact Classical.choose_spec rPos_ex_1
  · exact Classical.choose_spec rPos_ex_2
  · exact Classical.choose_spec rPos_ex_3
  · exact Classical.choose_spec rPos_ex_4
  · exact Classical.choose_spec rPos_ex_5
  · exact Classical.choose_spec rPos_ex_6
  · exact Classical.choose_spec rPos_ex_7
  · exact Classical.choose_spec rPos_ex_8

/-- The 19 exact Gauss–Legendre nodes on `(-1, 1)`, roots of `legendreScaled 19`. -/
private noncomputable def r19 (k : Fin 19) : ℝ :=
  if h : k.1 < 9 then -rPos19 ⟨8 - k.1, by omega⟩
  else if k.1 = 9 then 0
  else rPos19 ⟨k.1 - 10, by omega⟩

private theorem r19_neg_symm (k : Fin 19) :
    r19 ⟨18 - k.1, by omega⟩ = -r19 k := by
  unfold r19
  by_cases h1 : k.1 < 9
  · have h2 : ¬ (18 - k.1 < 9) := by omega
    have h3 : 18 - k.1 ≠ 9 := by omega
    simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte, neg_neg]
    congr 1; ext; dsimp; omega
  · by_cases h9 : k.1 = 9
    · simp [h9]
    · have h2 : 18 - k.1 < 9 := by omega
      simp only [h1, h9, h2, ↓reduceDIte, ↓reduceIte]
      congr 2; ext; dsimp; omega

private theorem r19_root (k : Fin 19) : (legendreScaled 19).eval (r19 k) = 0 := by
  unfold r19
  by_cases h1 : k.1 < 9
  · simp only [h1, ↓reduceDIte, legendreScaled_eval_neg 19]
    rw [(rPos19_spec ⟨8 - k.1, by omega⟩).2, mul_zero]
  · by_cases h9 : k.1 = 9
    · have hk : k = ⟨9, by omega⟩ := Fin.ext h9
      simp only [hk, show ¬ (9 < 9) by omega, ↓reduceDIte, ↓reduceIte]
      have h := legendreScaled_eval_neg 19 0
      rw [neg_zero, show (-1 : ℝ) ^ 19 = -1 by norm_num] at h
      linarith
    · simp only [h1, h9, ↓reduceDIte, ↓reduceIte]
      exact (rPos19_spec ⟨k.1 - 10, by omega⟩).2

private theorem rPos19_bounds (k : Fin 9) : 0 < rPos19 k ∧ rPos19 k < 1 := by
  have ⟨hl, hr⟩ := (rPos19_spec k).1
  have hlo : (0 : ℝ) ≤ ((vecAt posMidList k.1 - 1 : ℕ) : ℝ) / certD := by positivity
  have hhi : vecAt posMidList k.1 + 1 ≤ certD := by
    fin_cases k <;> decide
  have hhiR : ((vecAt posMidList k.1 + 1 : ℕ) : ℝ) / certD ≤ 1 := by
    rw [div_le_one (by norm_num [certD])]; exact_mod_cast hhi
  exact ⟨hlo.trans_lt hl, hr.trans_le hhiR⟩

private theorem rPos19_mono : StrictMono rPos19 := by
  have hadj : ∀ k : Fin 8, rPos19 k.castSucc < rPos19 k.succ := fun k => by
    have h1 := (rPos19_spec k.castSucc).1.2
    have h2 := (rPos19_spec k.succ).1.1
    have hgap : vecAt posMidList k.1 + 1 ≤ vecAt posMidList (k.1 + 1) - 1 := by
      fin_cases k <;> decide
    have hgapR : ((vecAt posMidList k.1 + 1 : ℕ) : ℝ) / certD ≤
        ((vecAt posMidList (k.1 + 1) - 1 : ℕ) : ℝ) / certD := by
      gcongr
    exact h1.trans_le (hgapR.trans h2.le)
  exact Fin.strictMono_iff_lt_succ.mpr hadj

private theorem r19_strictMono : StrictMono r19 := by
  refine Fin.strictMono_iff_lt_succ.mpr fun k => ?_
  by_cases h1 : k.1 < 8
  · unfold r19
    have h1' : k.castSucc.1 < 9 := by change k.1 < 9; omega
    have h2' : k.succ.1 < 9 := by change k.1 + 1 < 9; omega
    simp only [h1', h2', ↓reduceDIte, neg_lt_neg_iff]
    exact rPos19_mono (show (⟨8 - k.succ.1, by omega⟩ : Fin 9) < ⟨8 - k.castSucc.1, by omega⟩
      from by change 8 - (k.1 + 1) < 8 - k.1; omega)
  · by_cases h8 : k.1 = 8
    · have hk : k = ⟨8, by omega⟩ := Fin.ext h8
      rw [hk]
      have h0 : r19 (⟨8, by omega⟩ : Fin 18).castSucc = -rPos19 0 := rfl
      have h9 : r19 (⟨8, by omega⟩ : Fin 18).succ = 0 := rfl
      rw [h0, h9]; linarith [(rPos19_bounds 0).1]
    · by_cases h9 : k.1 = 9
      · have hk : k = ⟨9, by omega⟩ := Fin.ext h9
        rw [hk]
        have ha : r19 (⟨9, by omega⟩ : Fin 18).castSucc = 0 := rfl
        have hb : r19 (⟨9, by omega⟩ : Fin 18).succ = rPos19 0 := rfl
        rw [ha, hb]; exact (rPos19_bounds 0).1
      · unfold r19
        have hc1 : ¬ (k.castSucc.1 < 9) := by change ¬ (k.1 < 9); omega
        have hc2 : k.castSucc.1 ≠ 9 := by change k.1 ≠ 9; omega
        have hs1 : ¬ (k.succ.1 < 9) := by change ¬ (k.1 + 1 < 9); omega
        have hs2 : k.succ.1 ≠ 9 := by change k.1 + 1 ≠ 9; omega
        simp only [hc1, hc2, hs1, hs2, ↓reduceDIte, ↓reduceIte]
        exact rPos19_mono (by change k.1 - 10 < k.1 + 1 - 10; omega)

private theorem r19_range (k : Fin 19) : r19 k ∈ Set.Ioo (-1 : ℝ) 1 := by
  unfold r19
  by_cases h1 : k.1 < 9
  · simp only [h1, ↓reduceDIte]
    have ⟨ha, hb⟩ := rPos19_bounds ⟨8 - k.1, by omega⟩
    exact ⟨by linarith, by linarith⟩
  · by_cases h9 : k.1 = 9
    · simp [h9]
    · simp only [h1, h9, ↓reduceDIte, ↓reduceIte]
      have ⟨ha, hb⟩ := rPos19_bounds ⟨k.1 - 10, by omega⟩
      exact ⟨by linarith, hb⟩

private theorem gaussWeight_r19_symm (k : Fin 19) :
    gaussWeight r19 ⟨18 - k.1, by omega⟩ = gaussWeight r19 k := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root,
    gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root, r19_neg_symm k,
    cauchyIntPoly_legendre_eval_neg 19, legendreScaled_deriv_eval_neg 19]
  have hp : (-1 : ℝ) ^ (19 + 1) = 1 := by norm_num
  simp [hp]

private def certDPow17 : ℕ := certD ^ 17

private theorem weight_bracket_pos_sign {mid wLo wHi : ℕ} {r : ℝ}
    (hmid : mid + 1 ≤ certD) (hr_mem : r ∈ Set.Icc (-1 : ℝ) 1)
    (hr_dist : |r - (mid : ℝ) / certD| ≤ 1 / (certD : ℝ))
    (ha_sign : Nat.ble (Nat.add (evalHom a19Neg mid certD) (Nat.mul mAp19 certDPow17))
      (evalHom a19Pos mid certD) = true)
    (hd_sign : Nat.ble (Nat.add (evalHom d19Neg mid certD)
      (Nat.add (Nat.mul mQpp19 certDPow17) 1)) (evalHom d19Pos mid certD) = true)
    (hlo : Nat.ble (Nat.mul wLo (Nat.mul a19LCM
      (Nat.add (Nat.sub (evalHom d19Pos mid certD) (evalHom d19Neg mid certD))
        (Nat.mul mQpp19 certDPow17))))
      (Nat.mul (Nat.sub (Nat.sub (evalHom a19Pos mid certD) (evalHom a19Neg mid certD))
        (Nat.mul mAp19 certDPow17)) certS) = true)
    (hhi : Nat.ble (Nat.mul (Nat.add (Nat.sub (evalHom a19Pos mid certD)
        (evalHom a19Neg mid certD)) (Nat.mul mAp19 certDPow17)) certS)
      (Nat.mul wHi (Nat.mul a19LCM
        (Nat.sub (Nat.sub (evalHom d19Pos mid certD) (evalHom d19Neg mid certD))
          (Nat.mul mQpp19 certDPow17)))) = true) :
    (wLo : ℝ) / certS ≤ (cauchyIntPoly (legendreScaled 19)).eval r /
        (legendreScaled 19).derivative.eval r ∧
      (cauchyIntPoly (legendreScaled 19)).eval r /
        (legendreScaled 19).derivative.eval r ≤ (wHi : ℝ) / certS := by
  have hD : 0 < certD := by decide
  have hDR : (0 : ℝ) < certD := Nat.cast_pos.mpr hD
  have hSpos : (0 : ℝ) < certS := by norm_num [certS]
  have hLpos : (0 : ℝ) < a19LCM := by norm_num [a19LCM]
  have hm_mem : (mid : ℝ) / certD ∈ Set.Icc (-1 : ℝ) 1 := by
    have hm0 : (0 : ℝ) ≤ (mid : ℝ) / certD := by positivity
    exact ⟨by linarith, by rw [div_le_one hDR]; exact_mod_cast (show mid ≤ certD by omega)⟩
  have ha_eq : (certD : ℝ) ^ 18 * ((a19LCM : ℝ) *
      (cauchyIntPoly (legendreScaled 19)).eval ((mid : ℝ) / certD)) =
      (evalHom a19Pos mid certD : ℝ) - (evalHom a19Neg mid certD : ℝ) := by
    rw [evalHom_eq (by decide : a19Pos ≠ []) mid hD,
      evalHom_eq (by decide : a19Neg ≠ []) mid hD]
    have h1 : a19Pos.length - 1 = 18 := rfl
    have h2 : a19Neg.length - 1 = 18 := rfl
    rw [h1, h2, ← mul_sub, ← Polynomial.eval_sub, ← a19_eq,
      Polynomial.eval_mul, Polynomial.eval_C]
  have hd_eq : (certD : ℝ) ^ 18 * (legendreScaled 19).derivative.eval ((mid : ℝ) / certD) =
      (evalHom d19Pos mid certD : ℝ) - (evalHom d19Neg mid certD : ℝ) := by
    rw [evalHom_eq (by decide : d19Pos ≠ []) mid hD,
      evalHom_eq (by decide : d19Neg ≠ []) mid hD]
    have h1 : d19Pos.length - 1 = 18 := rfl
    have h2 : d19Neg.length - 1 = 18 := rfl
    rw [h1, h2, ← mul_sub, ← Polynomial.eval_sub, ← d19_eq]
  have ha_lip := abs_poly_eval_sub_le (Polynomial.C (a19LCM : ℝ) *
    cauchyIntPoly (legendreScaled 19)) mAp19 a19_lip_le hr_mem hm_mem
  have hd_lip := abs_poly_eval_sub_le (legendreScaled 19).derivative mQpp19
    d19_lip_le hr_mem hm_mem
  have ha_bd : |(a19LCM : ℝ) * (cauchyIntPoly (legendreScaled 19)).eval r -
      (a19LCM : ℝ) * (cauchyIntPoly (legendreScaled 19)).eval ((mid : ℝ) / certD)| ≤
      (mAp19 : ℝ) / certD := by
    have h1 := ha_lip.trans (mul_le_mul_of_nonneg_left hr_dist (by positivity))
    simpa [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv] using h1
  have hd_bd : |(legendreScaled 19).derivative.eval r -
      (legendreScaled 19).derivative.eval ((mid : ℝ) / certD)| ≤ (mQpp19 : ℝ) / certD :=
    (hd_lip.trans (mul_le_mul_of_nonneg_left hr_dist (by positivity))).trans_eq
      (by ring)
  have hpow : (certD : ℝ) ^ 18 * ((1 : ℝ) / certD) = (certDPow17 : ℝ) := by
    unfold certDPow17; push_cast; field_simp
  have hD18 : (0 : ℝ) < (certD : ℝ) ^ 18 := by positivity
  set aP := evalHom a19Pos mid certD
  set aN := evalHom a19Neg mid certD
  set dP := evalHom d19Pos mid certD
  set dN := evalHom d19Neg mid certD
  set A := (certD : ℝ) ^ 18 * ((a19LCM : ℝ) * (cauchyIntPoly (legendreScaled 19)).eval r)
  set B := (certD : ℝ) ^ 18 * (legendreScaled 19).derivative.eval r
  have ha_abs := abs_le.mp ha_bd
  have hd_abs := abs_le.mp hd_bd
  have hA_lo : ((aP - aN) - mAp19 * certDPow17 : ℕ) ≤ A := by
    have hnat : aN + mAp19 * certDPow17 ≤ aP := Nat.le_of_ble_eq_true ha_sign
    rw [Nat.cast_sub (by omega : mAp19 * certDPow17 ≤ aP - aN),
      Nat.cast_sub (by omega : aN ≤ aP)]
    have hstep := mul_le_mul_of_nonneg_left ha_abs.1 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * -((mAp19 : ℝ) / certD) =
        -((mAp19 : ℝ) * (certDPow17 : ℝ)) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [A]; push_cast; linarith [hstep, hrhs, ha_eq]
  have hA_hi : A ≤ ((aP - aN) + mAp19 * certDPow17 : ℕ) := by
    have hnat : aN + mAp19 * certDPow17 ≤ aP := Nat.le_of_ble_eq_true ha_sign
    push_cast; rw [Nat.cast_sub (by omega : aN ≤ aP)]
    have hstep := mul_le_mul_of_nonneg_left ha_abs.2 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * ((mAp19 : ℝ) / certD) =
        (mAp19 : ℝ) * (certDPow17 : ℝ) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [A]; linarith [hstep, hrhs, ha_eq]
  have hB_lo : ((dP - dN) - mQpp19 * certDPow17 : ℕ) ≤ B ∧
      0 < (((dP - dN) - mQpp19 * certDPow17 : ℕ) : ℝ) := by
    have hnat : dN + (mQpp19 * certDPow17 + 1) ≤ dP := Nat.le_of_ble_eq_true hd_sign
    refine ⟨?_, Nat.cast_pos.mpr (by omega)⟩
    rw [Nat.cast_sub (by omega : mQpp19 * certDPow17 ≤ dP - dN),
      Nat.cast_sub (by omega : dN ≤ dP)]
    have hstep := mul_le_mul_of_nonneg_left hd_abs.1 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * -((mQpp19 : ℝ) / certD) =
        -((mQpp19 : ℝ) * (certDPow17 : ℝ)) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [B]; push_cast; linarith [hstep, hrhs, hd_eq]
  have hB_hi : B ≤ ((dP - dN) + mQpp19 * certDPow17 : ℕ) := by
    have hnat : dN + (mQpp19 * certDPow17 + 1) ≤ dP := Nat.le_of_ble_eq_true hd_sign
    push_cast; rw [Nat.cast_sub (by omega : dN ≤ dP)]
    have hstep := mul_le_mul_of_nonneg_left hd_abs.2 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * ((mQpp19 : ℝ) / certD) =
        (mQpp19 : ℝ) * (certDPow17 : ℝ) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [B]; linarith [hstep, hrhs, hd_eq]
  have hB_pos : 0 < B := hB_lo.2.trans_le hB_lo.1
  have hratio : (cauchyIntPoly (legendreScaled 19)).eval r /
      (legendreScaled 19).derivative.eval r = A / ((a19LCM : ℝ) * B) := by
    dsimp only [A, B]; field_simp
  rw [hratio]
  have hloR : (wLo : ℝ) * ((a19LCM : ℝ) * ((dP - dN + mQpp19 * certDPow17 : ℕ) : ℝ)) ≤
      ((aP - aN - mAp19 * certDPow17 : ℕ) : ℝ) * certS := by
    exact_mod_cast Nat.le_of_ble_eq_true hlo
  have hhiR : ((aP - aN + mAp19 * certDPow17 : ℕ) : ℝ) * certS ≤
      (wHi : ℝ) * ((a19LCM : ℝ) * ((dP - dN - mQpp19 * certDPow17 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_of_ble_eq_true hhi
  constructor
  · rw [div_le_div_iff₀ hSpos (mul_pos hLpos hB_pos)]
    calc (wLo : ℝ) * ((a19LCM : ℝ) * B)
        ≤ (wLo : ℝ) * ((a19LCM : ℝ) * ((dP - dN + mQpp19 * certDPow17 : ℕ) : ℝ)) := by
            gcongr
      _ ≤ ((aP - aN - mAp19 * certDPow17 : ℕ) : ℝ) * certS := hloR
      _ ≤ A * certS := by gcongr
  · rw [div_le_div_iff₀ (mul_pos hLpos hB_pos) hSpos]
    calc A * certS ≤ ((aP - aN + mAp19 * certDPow17 : ℕ) : ℝ) * certS := by gcongr
      _ ≤ (wHi : ℝ) * ((a19LCM : ℝ) * ((dP - dN - mQpp19 * certDPow17 : ℕ) : ℝ)) := hhiR
      _ ≤ (wHi : ℝ) * ((a19LCM : ℝ) * B) := by gcongr; exact hB_lo.1

private theorem weight_bracket_neg_sign {mid wLo wHi : ℕ} {r : ℝ}
    (hmid : mid + 1 ≤ certD) (hr_mem : r ∈ Set.Icc (-1 : ℝ) 1)
    (hr_dist : |r - (mid : ℝ) / certD| ≤ 1 / (certD : ℝ))
    (ha_sign : Nat.ble (Nat.add (evalHom a19Pos mid certD) (Nat.mul mAp19 certDPow17))
      (evalHom a19Neg mid certD) = true)
    (hd_sign : Nat.ble (Nat.add (evalHom d19Pos mid certD)
      (Nat.add (Nat.mul mQpp19 certDPow17) 1)) (evalHom d19Neg mid certD) = true)
    (hlo : Nat.ble (Nat.mul wLo (Nat.mul a19LCM
      (Nat.add (Nat.sub (evalHom d19Neg mid certD) (evalHom d19Pos mid certD))
        (Nat.mul mQpp19 certDPow17))))
      (Nat.mul (Nat.sub (Nat.sub (evalHom a19Neg mid certD) (evalHom a19Pos mid certD))
        (Nat.mul mAp19 certDPow17)) certS) = true)
    (hhi : Nat.ble (Nat.mul (Nat.add (Nat.sub (evalHom a19Neg mid certD)
        (evalHom a19Pos mid certD)) (Nat.mul mAp19 certDPow17)) certS)
      (Nat.mul wHi (Nat.mul a19LCM
        (Nat.sub (Nat.sub (evalHom d19Neg mid certD) (evalHom d19Pos mid certD))
          (Nat.mul mQpp19 certDPow17)))) = true) :
    (wLo : ℝ) / certS ≤ (cauchyIntPoly (legendreScaled 19)).eval r /
        (legendreScaled 19).derivative.eval r ∧
      (cauchyIntPoly (legendreScaled 19)).eval r /
        (legendreScaled 19).derivative.eval r ≤ (wHi : ℝ) / certS := by
  have hD : 0 < certD := by decide
  have hDR : (0 : ℝ) < certD := Nat.cast_pos.mpr hD
  have hSpos : (0 : ℝ) < certS := by norm_num [certS]
  have hLpos : (0 : ℝ) < a19LCM := by norm_num [a19LCM]
  have hm_mem : (mid : ℝ) / certD ∈ Set.Icc (-1 : ℝ) 1 := by
    have hm0 : (0 : ℝ) ≤ (mid : ℝ) / certD := by positivity
    exact ⟨by linarith, by rw [div_le_one hDR]; exact_mod_cast (show mid ≤ certD by omega)⟩
  have ha_eq : (certD : ℝ) ^ 18 * ((a19LCM : ℝ) *
      (cauchyIntPoly (legendreScaled 19)).eval ((mid : ℝ) / certD)) =
      (evalHom a19Pos mid certD : ℝ) - (evalHom a19Neg mid certD : ℝ) := by
    rw [evalHom_eq (by decide : a19Pos ≠ []) mid hD,
      evalHom_eq (by decide : a19Neg ≠ []) mid hD]
    have h1 : a19Pos.length - 1 = 18 := rfl
    have h2 : a19Neg.length - 1 = 18 := rfl
    rw [h1, h2, ← mul_sub, ← Polynomial.eval_sub, ← a19_eq,
      Polynomial.eval_mul, Polynomial.eval_C]
  have hd_eq : (certD : ℝ) ^ 18 * (legendreScaled 19).derivative.eval ((mid : ℝ) / certD) =
      (evalHom d19Pos mid certD : ℝ) - (evalHom d19Neg mid certD : ℝ) := by
    rw [evalHom_eq (by decide : d19Pos ≠ []) mid hD,
      evalHom_eq (by decide : d19Neg ≠ []) mid hD]
    have h1 : d19Pos.length - 1 = 18 := rfl
    have h2 : d19Neg.length - 1 = 18 := rfl
    rw [h1, h2, ← mul_sub, ← Polynomial.eval_sub, ← d19_eq]
  have ha_lip := abs_poly_eval_sub_le (Polynomial.C (a19LCM : ℝ) *
    cauchyIntPoly (legendreScaled 19)) mAp19 a19_lip_le hr_mem hm_mem
  have hd_lip := abs_poly_eval_sub_le (legendreScaled 19).derivative mQpp19
    d19_lip_le hr_mem hm_mem
  have ha_bd : |(a19LCM : ℝ) * (cauchyIntPoly (legendreScaled 19)).eval r -
      (a19LCM : ℝ) * (cauchyIntPoly (legendreScaled 19)).eval ((mid : ℝ) / certD)| ≤
      (mAp19 : ℝ) / certD := by
    have h1 := ha_lip.trans (mul_le_mul_of_nonneg_left hr_dist (by positivity))
    simpa [Polynomial.eval_mul, Polynomial.eval_C, div_eq_mul_inv] using h1
  have hd_bd : |(legendreScaled 19).derivative.eval r -
      (legendreScaled 19).derivative.eval ((mid : ℝ) / certD)| ≤ (mQpp19 : ℝ) / certD :=
    (hd_lip.trans (mul_le_mul_of_nonneg_left hr_dist (by positivity))).trans_eq
      (by ring)
  have hD18 : (0 : ℝ) < (certD : ℝ) ^ 18 := by positivity
  set aP := evalHom a19Pos mid certD
  set aN := evalHom a19Neg mid certD
  set dP := evalHom d19Pos mid certD
  set dN := evalHom d19Neg mid certD
  set A := -((certD : ℝ) ^ 18 * ((a19LCM : ℝ) * (cauchyIntPoly (legendreScaled 19)).eval r))
  set B := -((certD : ℝ) ^ 18 * (legendreScaled 19).derivative.eval r)
  have ha_abs := abs_le.mp ha_bd
  have hd_abs := abs_le.mp hd_bd
  have hA_lo : ((aN - aP) - mAp19 * certDPow17 : ℕ) ≤ A := by
    have hnat : aP + mAp19 * certDPow17 ≤ aN := Nat.le_of_ble_eq_true ha_sign
    rw [Nat.cast_sub (by omega : mAp19 * certDPow17 ≤ aN - aP),
      Nat.cast_sub (by omega : aP ≤ aN)]
    have hstep := mul_le_mul_of_nonneg_left ha_abs.2 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * ((mAp19 : ℝ) / certD) =
        (mAp19 : ℝ) * (certDPow17 : ℝ) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [A]; push_cast; linarith [hstep, hrhs, ha_eq]
  have hA_hi : A ≤ ((aN - aP) + mAp19 * certDPow17 : ℕ) := by
    have hnat : aP + mAp19 * certDPow17 ≤ aN := Nat.le_of_ble_eq_true ha_sign
    push_cast; rw [Nat.cast_sub (by omega : aP ≤ aN)]
    have hstep := mul_le_mul_of_nonneg_left ha_abs.1 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * -((mAp19 : ℝ) / certD) =
        -((mAp19 : ℝ) * (certDPow17 : ℝ)) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [A]; linarith [hstep, hrhs, ha_eq]
  have hB_lo : ((dN - dP) - mQpp19 * certDPow17 : ℕ) ≤ B ∧
      0 < (((dN - dP) - mQpp19 * certDPow17 : ℕ) : ℝ) := by
    have hnat : dP + (mQpp19 * certDPow17 + 1) ≤ dN := Nat.le_of_ble_eq_true hd_sign
    refine ⟨?_, Nat.cast_pos.mpr (by omega)⟩
    rw [Nat.cast_sub (by omega : mQpp19 * certDPow17 ≤ dN - dP),
      Nat.cast_sub (by omega : dP ≤ dN)]
    have hstep := mul_le_mul_of_nonneg_left hd_abs.2 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * ((mQpp19 : ℝ) / certD) =
        (mQpp19 : ℝ) * (certDPow17 : ℝ) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [B]; push_cast; linarith [hstep, hrhs, hd_eq]
  have hB_hi : B ≤ ((dN - dP) + mQpp19 * certDPow17 : ℕ) := by
    have hnat : dP + (mQpp19 * certDPow17 + 1) ≤ dN := Nat.le_of_ble_eq_true hd_sign
    push_cast; rw [Nat.cast_sub (by omega : dP ≤ dN)]
    have hstep := mul_le_mul_of_nonneg_left hd_abs.1 hD18.le
    rw [mul_sub] at hstep
    have hrhs : (certD : ℝ) ^ 18 * -((mQpp19 : ℝ) / certD) =
        -((mQpp19 : ℝ) * (certDPow17 : ℝ)) := by
      unfold certDPow17; push_cast; field_simp
    dsimp only [B]; linarith [hstep, hrhs, hd_eq]
  have hB_pos : 0 < B := hB_lo.2.trans_le hB_lo.1
  have hratio : (cauchyIntPoly (legendreScaled 19)).eval r /
      (legendreScaled 19).derivative.eval r = A / ((a19LCM : ℝ) * B) := by
    dsimp only [A, B]; field_simp
  rw [hratio]
  have hloR : (wLo : ℝ) * ((a19LCM : ℝ) * ((dN - dP + mQpp19 * certDPow17 : ℕ) : ℝ)) ≤
      ((aN - aP - mAp19 * certDPow17 : ℕ) : ℝ) * certS := by
    exact_mod_cast Nat.le_of_ble_eq_true hlo
  have hhiR : ((aN - aP + mAp19 * certDPow17 : ℕ) : ℝ) * certS ≤
      (wHi : ℝ) * ((a19LCM : ℝ) * ((dN - dP - mQpp19 * certDPow17 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_of_ble_eq_true hhi
  constructor
  · rw [div_le_div_iff₀ hSpos (mul_pos hLpos hB_pos)]
    calc (wLo : ℝ) * ((a19LCM : ℝ) * B)
        ≤ (wLo : ℝ) * ((a19LCM : ℝ) * ((dN - dP + mQpp19 * certDPow17 : ℕ) : ℝ)) := by
            gcongr
      _ ≤ ((aN - aP - mAp19 * certDPow17 : ℕ) : ℝ) * certS := hloR
      _ ≤ A * certS := by gcongr
  · rw [div_le_div_iff₀ (mul_pos hLpos hB_pos) hSpos]
    calc A * certS ≤ ((aN - aP + mAp19 * certDPow17 : ℕ) : ℝ) * certS := by gcongr
      _ ≤ (wHi : ℝ) * ((a19LCM : ℝ) * ((dN - dP - mQpp19 * certDPow17 : ℕ) : ℝ)) := hhiR
      _ ≤ (wHi : ℝ) * ((a19LCM : ℝ) * B) := by gcongr; exact hB_lo.1

private def wLo19 : List ℕ :=
  [1946178822972, 4481422676569, 6904454273764, 9149002162244, 11156664554733, 12875396253933,
   14260670217360, 15276604206585, 15896884339395, 16105444984878, 15896884339395, 15276604206585,
   14260670217360, 12875396253933, 11156664554733, 9149002162244, 6904454273764, 4481422676569,
   1946178822972]
private def wHi19 : List ℕ :=
  [1946178822973, 4481422676570, 6904454273765, 9149002162246, 11156664554734, 12875396253934,
   14260670217361, 15276604206587, 15896884339396, 16105444984879, 15896884339396, 15276604206587,
   14260670217361, 12875396253934, 11156664554734, 9149002162246, 6904454273765, 4481422676570,
   1946178822973]

private theorem w19_pos_0 : (15896884339395 : ℝ) / certS ≤ gaussWeight r19 ⟨10, by omega⟩ ∧
    gaussWeight r19 ⟨10, by omega⟩ ≤ (15896884339396 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨10, by omega⟩ = rPos19 ⟨0, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨0, by omega⟩).1
  have hdist : |r19 ⟨10, by omega⟩ - (1603586456402253758681 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((1603586456402253758680 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((1603586456402253758682 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (1603586456402253758680 : ℝ) / certD =
        (1603586456402253758681 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (1603586456402253758682 : ℝ) / certD =
        (1603586456402253758681 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (1603586456402253758680 : ℝ) / certD < rPos19 ⟨0, by omega⟩ := h1
    have hr_hi : rPos19 ⟨0, by omega⟩ < (1603586456402253758682 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_pos_sign (mid := 1603586456402253758681)
    (wLo := 15896884339395) (wHi := 15896884339396)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_1 : (15276604206585 : ℝ) / certS ≤ gaussWeight r19 ⟨11, by omega⟩ ∧
    gaussWeight r19 ⟨11, by omega⟩ ≤ (15276604206587 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨11, by omega⟩ = rPos19 ⟨1, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨1, by omega⟩).1
  have hdist : |r19 ⟨11, by omega⟩ - (3165640999636298319901 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((3165640999636298319900 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((3165640999636298319902 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (3165640999636298319900 : ℝ) / certD =
        (3165640999636298319901 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (3165640999636298319902 : ℝ) / certD =
        (3165640999636298319901 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (3165640999636298319900 : ℝ) / certD < rPos19 ⟨1, by omega⟩ := h1
    have hr_hi : rPos19 ⟨1, by omega⟩ < (3165640999636298319902 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_neg_sign (mid := 3165640999636298319901)
    (wLo := 15276604206585) (wHi := 15276604206587)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_2 : (14260670217360 : ℝ) / certS ≤ gaussWeight r19 ⟨12, by omega⟩ ∧
    gaussWeight r19 ⟨12, by omega⟩ ≤ (14260670217361 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨12, by omega⟩ = rPos19 ⟨2, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨2, by omega⟩).1
  have hdist : |r19 ⟨12, by omega⟩ - (4645707413759609457173 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((4645707413759609457172 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((4645707413759609457174 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (4645707413759609457172 : ℝ) / certD =
        (4645707413759609457173 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (4645707413759609457174 : ℝ) / certD =
        (4645707413759609457173 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (4645707413759609457172 : ℝ) / certD < rPos19 ⟨2, by omega⟩ := h1
    have hr_hi : rPos19 ⟨2, by omega⟩ < (4645707413759609457174 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_pos_sign (mid := 4645707413759609457173)
    (wLo := 14260670217360) (wHi := 14260670217361)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_3 : (12875396253933 : ℝ) / certS ≤ gaussWeight r19 ⟨13, by omega⟩ ∧
    gaussWeight r19 ⟨13, by omega⟩ ≤ (12875396253934 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨13, by omega⟩ = rPos19 ⟨3, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨3, by omega⟩).1
  have hdist : |r19 ⟨13, by omega⟩ - (6005453046616810234696 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((6005453046616810234695 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((6005453046616810234697 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (6005453046616810234695 : ℝ) / certD =
        (6005453046616810234696 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (6005453046616810234697 : ℝ) / certD =
        (6005453046616810234696 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (6005453046616810234695 : ℝ) / certD < rPos19 ⟨3, by omega⟩ := h1
    have hr_hi : rPos19 ⟨3, by omega⟩ < (6005453046616810234697 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_neg_sign (mid := 6005453046616810234696)
    (wLo := 12875396253933) (wHi := 12875396253934)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_4 : (11156664554733 : ℝ) / certS ≤ gaussWeight r19 ⟨14, by omega⟩ ∧
    gaussWeight r19 ⟨14, by omega⟩ ≤ (11156664554734 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨14, by omega⟩ = rPos19 ⟨4, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨4, by omega⟩).1
  have hdist : |r19 ⟨14, by omega⟩ - (7209661773352293786171 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((7209661773352293786170 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((7209661773352293786172 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (7209661773352293786170 : ℝ) / certD =
        (7209661773352293786171 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (7209661773352293786172 : ℝ) / certD =
        (7209661773352293786171 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (7209661773352293786170 : ℝ) / certD < rPos19 ⟨4, by omega⟩ := h1
    have hr_hi : rPos19 ⟨4, by omega⟩ < (7209661773352293786172 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_pos_sign (mid := 7209661773352293786171)
    (wLo := 11156664554733) (wHi := 11156664554734)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_5 : (9149002162244 : ℝ) / certS ≤ gaussWeight r19 ⟨15, by omega⟩ ∧
    gaussWeight r19 ⟨15, by omega⟩ ≤ (9149002162246 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨15, by omega⟩ = rPos19 ⟨5, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨5, by omega⟩).1
  have hdist : |r19 ⟨15, by omega⟩ - (8227146565371428249789 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((8227146565371428249788 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((8227146565371428249790 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (8227146565371428249788 : ℝ) / certD =
        (8227146565371428249789 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (8227146565371428249790 : ℝ) / certD =
        (8227146565371428249789 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (8227146565371428249788 : ℝ) / certD < rPos19 ⟨5, by omega⟩ := h1
    have hr_hi : rPos19 ⟨5, by omega⟩ < (8227146565371428249790 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_neg_sign (mid := 8227146565371428249789)
    (wLo := 9149002162244) (wHi := 9149002162246)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_6 : (6904454273764 : ℝ) / certS ≤ gaussWeight r19 ⟨16, by omega⟩ ∧
    gaussWeight r19 ⟨16, by omega⟩ ≤ (6904454273765 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨16, by omega⟩ = rPos19 ⟨6, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨6, by omega⟩).1
  have hdist : |r19 ⟨16, by omega⟩ - (9031559036148179016427 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((9031559036148179016426 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((9031559036148179016428 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (9031559036148179016426 : ℝ) / certD =
        (9031559036148179016427 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (9031559036148179016428 : ℝ) / certD =
        (9031559036148179016427 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (9031559036148179016426 : ℝ) / certD < rPos19 ⟨6, by omega⟩ := h1
    have hr_hi : rPos19 ⟨6, by omega⟩ < (9031559036148179016428 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_pos_sign (mid := 9031559036148179016427)
    (wLo := 6904454273764) (wHi := 6904454273765)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_7 : (4481422676569 : ℝ) / certS ≤ gaussWeight r19 ⟨17, by omega⟩ ∧
    gaussWeight r19 ⟨17, by omega⟩ ≤ (4481422676570 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨17, by omega⟩ = rPos19 ⟨7, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨7, by omega⟩).1
  have hdist : |r19 ⟨17, by omega⟩ - (9602081521348300308528 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((9602081521348300308527 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((9602081521348300308529 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (9602081521348300308527 : ℝ) / certD =
        (9602081521348300308528 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (9602081521348300308529 : ℝ) / certD =
        (9602081521348300308528 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (9602081521348300308527 : ℝ) / certD < rPos19 ⟨7, by omega⟩ := h1
    have hr_hi : rPos19 ⟨7, by omega⟩ < (9602081521348300308529 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_neg_sign (mid := 9602081521348300308528)
    (wLo := 4481422676569) (wHi := 4481422676570)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl
private theorem w19_pos_8 : (1946178822972 : ℝ) / certS ≤ gaussWeight r19 ⟨18, by omega⟩ ∧
    gaussWeight r19 ⟨18, by omega⟩ ≤ (1946178822973 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hm : r19 ⟨18, by omega⟩ = rPos19 ⟨8, by omega⟩ := rfl
  have hsp := (rPos19_spec ⟨8, by omega⟩).1
  have hdist : |r19 ⟨18, by omega⟩ - (9924068438435844031890 : ℝ) / certD| ≤ 1 / (certD : ℝ) := by
    rw [hm, abs_le]
    have ⟨h1, h2⟩ := hsp
    have hD : (0 : ℝ) < certD := by norm_num [certD]
    change ((9924068438435844031889 : ℕ) : ℝ) / certD < _ at h1
    change _ < ((9924068438435844031891 : ℕ) : ℝ) / certD at h2
    push_cast at h1 h2
    have hl_eq : (9924068438435844031889 : ℝ) / certD =
        (9924068438435844031890 : ℝ) / certD - 1 / certD := by ring
    have hr_eq : (9924068438435844031891 : ℝ) / certD =
        (9924068438435844031890 : ℝ) / certD + 1 / certD := by ring
    have hr_lo : (9924068438435844031889 : ℝ) / certD < rPos19 ⟨8, by omega⟩ := h1
    have hr_hi : rPos19 ⟨8, by omega⟩ < (9924068438435844031891 : ℝ) / certD := h2
    exact ⟨by linarith, by linarith⟩
  exact weight_bracket_pos_sign (mid := 9924068438435844031890)
    (wLo := 1946178822972) (wHi := 1946178822973)
    (by decide) (Set.Ioo_subset_Icc_self (r19_range _)) hdist
    rfl rfl rfl rfl

private theorem w19_mid : (16105444984878 : ℝ) / certS ≤ gaussWeight r19 ⟨9, by omega⟩ ∧
    gaussWeight r19 ⟨9, by omega⟩ ≤ (16105444984879 : ℝ) / certS := by
  rw [gaussWeight_eq_cauchyInt_div_deriv r19_strictMono r19_root]
  have hr0 : r19 ⟨9, by omega⟩ = 0 := by unfold r19; simp
  rw [hr0]
  have ha0 : (a19LCM : ℝ) * (cauchyIntPoly (legendreScaled 19)).eval 0 =
      (-4329327034368 : ℝ) := by
    have h := congrArg (fun p : Polynomial ℝ => p.eval 0) a19_eq
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub] at h
    rw [h, ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero,
      natListPoly_coeff, natListPoly_coeff]
    norm_num [a19Pos, a19Neg]
  have hd0 : (legendreScaled 19).derivative.eval 0 = (-1847560 : ℝ) := by
    rw [d19_eq, Polynomial.eval_sub, ← Polynomial.coeff_zero_eq_eval_zero,
      ← Polynomial.coeff_zero_eq_eval_zero, natListPoly_coeff, natListPoly_coeff]
    norm_num [d19Pos, d19Neg]
  have haL : (a19LCM : ℝ) ≠ 0 := by norm_num [a19LCM]
  have ha_val : (cauchyIntPoly (legendreScaled 19)).eval 0 =
      (-4329327034368 : ℝ) / (a19LCM : ℝ) := by rw [eq_div_iff haL, mul_comm]; exact ha0
  rw [ha_val, hd0]; norm_num [a19LCM, certS]

private theorem w19_bounds (k : Fin 19) :
    (vecAt wLo19 k.1 : ℝ) / certS ≤ gaussWeight r19 k ∧
      gaussWeight r19 k ≤ (vecAt wHi19 k.1 : ℝ) / certS := by
  refine @fin19_all (fun k : Fin 19 => (vecAt wLo19 k.1 : ℝ) / certS ≤ gaussWeight r19 k ∧
      gaussWeight r19 k ≤ (vecAt wHi19 k.1 : ℝ) / certS)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ k
  · have hs : gaussWeight r19 ⟨0, by omega⟩ = gaussWeight r19 ⟨18, by omega⟩ :=
      gaussWeight_r19_symm ⟨18, by omega⟩
    change _ ≤ gaussWeight r19 ⟨0, by omega⟩ ∧ gaussWeight r19 ⟨0, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_8
  · have hs : gaussWeight r19 ⟨1, by omega⟩ = gaussWeight r19 ⟨17, by omega⟩ :=
      gaussWeight_r19_symm ⟨17, by omega⟩
    change _ ≤ gaussWeight r19 ⟨1, by omega⟩ ∧ gaussWeight r19 ⟨1, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_7
  · have hs : gaussWeight r19 ⟨2, by omega⟩ = gaussWeight r19 ⟨16, by omega⟩ :=
      gaussWeight_r19_symm ⟨16, by omega⟩
    change _ ≤ gaussWeight r19 ⟨2, by omega⟩ ∧ gaussWeight r19 ⟨2, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_6
  · have hs : gaussWeight r19 ⟨3, by omega⟩ = gaussWeight r19 ⟨15, by omega⟩ :=
      gaussWeight_r19_symm ⟨15, by omega⟩
    change _ ≤ gaussWeight r19 ⟨3, by omega⟩ ∧ gaussWeight r19 ⟨3, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_5
  · have hs : gaussWeight r19 ⟨4, by omega⟩ = gaussWeight r19 ⟨14, by omega⟩ :=
      gaussWeight_r19_symm ⟨14, by omega⟩
    change _ ≤ gaussWeight r19 ⟨4, by omega⟩ ∧ gaussWeight r19 ⟨4, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_4
  · have hs : gaussWeight r19 ⟨5, by omega⟩ = gaussWeight r19 ⟨13, by omega⟩ :=
      gaussWeight_r19_symm ⟨13, by omega⟩
    change _ ≤ gaussWeight r19 ⟨5, by omega⟩ ∧ gaussWeight r19 ⟨5, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_3
  · have hs : gaussWeight r19 ⟨6, by omega⟩ = gaussWeight r19 ⟨12, by omega⟩ :=
      gaussWeight_r19_symm ⟨12, by omega⟩
    change _ ≤ gaussWeight r19 ⟨6, by omega⟩ ∧ gaussWeight r19 ⟨6, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_2
  · have hs : gaussWeight r19 ⟨7, by omega⟩ = gaussWeight r19 ⟨11, by omega⟩ :=
      gaussWeight_r19_symm ⟨11, by omega⟩
    change _ ≤ gaussWeight r19 ⟨7, by omega⟩ ∧ gaussWeight r19 ⟨7, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_1
  · have hs : gaussWeight r19 ⟨8, by omega⟩ = gaussWeight r19 ⟨10, by omega⟩ :=
      gaussWeight_r19_symm ⟨10, by omega⟩
    change _ ≤ gaussWeight r19 ⟨8, by omega⟩ ∧ gaussWeight r19 ⟨8, by omega⟩ ≤ _
    rw [hs]; exact w19_pos_0
  · exact w19_mid
  · exact w19_pos_0
  · exact w19_pos_1
  · exact w19_pos_2
  · exact w19_pos_3
  · exact w19_pos_4
  · exact w19_pos_5
  · exact w19_pos_6
  · exact w19_pos_7
  · exact w19_pos_8

private def xeLo19 : List ℕ :=
  [6454182732953257, 33823070685394473, 82317481927404783, 150692541943428598, 237178749265055028,
   339536491037571130, 455114869830433196, 580920515030914642, 713695151205808430,
   850000000000000000, 986304848794191569, 1119079484969085357, 1244885130169566803,
   1360463508962428869, 1462821250734944971, 1549307458056571401, 1617682518072595216,
   1666176929314605526, 1693545817267046742]
private def xeHi19 : List ℕ :=
  [6454182732953258, 33823070685394474, 82317481927404784, 150692541943428599, 237178749265055029,
   339536491037571131, 455114869830433197, 580920515030914643, 713695151205808431,
   850000000000000000, 986304848794191570, 1119079484969085358, 1244885130169566804,
   1360463508962428870, 1462821250734944972, 1549307458056571402, 1617682518072595217,
   1666176929314605527, 1693545817267046743]
private def xiLo19 : List ℕ :=
  [3986406982118188, 20890720129214233, 50843150602220601, 93074805318000016, 146492756899004576,
   209713715052617462, 281100360777620503, 358803847519094338, 440811711038881677,
   525000000000000000, 609188288961118322, 691196152480905661, 768899639222379496,
   840286284947382537, 903507243100995423, 956925194681999983, 999156849397779398,
   1029109279870785766, 1046013593017881811]
private def xiHi19 : List ℕ :=
  [3986406982118189, 20890720129214234, 50843150602220602, 93074805318000017, 146492756899004577,
   209713715052617463, 281100360777620504, 358803847519094339, 440811711038881678,
   525000000000000000, 609188288961118323, 691196152480905662, 768899639222379497,
   840286284947382538, 903507243100995424, 956925194681999984, 999156849397779399,
   1029109279870785767, 1046013593017881812]
private def weLo19 : List ℕ :=
  [1654251999526, 3809209275083, 5868786132699, 7776651837907, 9483164871523, 10944086815843,
   12121569684756, 12985113575597, 13512351688485, 13689628237146, 13512351688485, 12985113575597,
   12121569684756, 10944086815843, 9483164871523, 7776651837907, 5868786132699, 3809209275083,
   1654251999526]
private def weHi19 : List ℕ :=
  [1654251999528, 3809209275085, 5868786132701, 7776651837910, 9483164871524, 10944086815844,
   12121569684757, 12985113575599, 13512351688487, 13689628237148, 13512351688487, 12985113575599,
   12121569684757, 10944086815844, 9483164871524, 7776651837910, 5868786132701, 3809209275085,
   1654251999528]
private def wiLo19 : List ℕ :=
  [1021743882060, 2352746905198, 3624838493726, 4803226135178, 5857248891234, 6759583033314,
   7486851864114, 8020217208457, 8345864278182, 8455358617060, 8345864278182, 8020217208457,
   7486851864114, 6759583033314, 5857248891234, 4803226135178, 3624838493726, 2352746905198,
   1021743882060]
private def wiHi19 : List ℕ :=
  [1021743882061, 2352746905200, 3624838493727, 4803226135180, 5857248891236, 6759583033316,
   7486851864115, 8020217208459, 8345864278183, 8455358617062, 8345864278183, 8020217208459,
   7486851864115, 6759583033316, 5857248891236, 4803226135180, 3624838493727, 2352746905200,
   1021743882061]

private def sLo19 : List ℕ :=
  [75931561564155968109, 397918478651699691471, 968440963851820983572, 1772853434628571750210,
   2790338226647706213828, 3994546953383189765303, 5354292586240390542826, 6834359000363701680098,
   8396413543597746241318, 10000000000000000000000, 11603586456402253758680,
   13165640999636298319900, 14645707413759609457172, 16005453046616810234695,
   17209661773352293786170, 18227146565371428249788, 19031559036148179016426,
   19602081521348300308527, 19924068438435844031889]
private def sHi19 : List ℕ :=
  [75931561564155968111, 397918478651699691473, 968440963851820983574, 1772853434628571750212,
   2790338226647706213830, 3994546953383189765305, 5354292586240390542828, 6834359000363701680100,
   8396413543597746241320, 10000000000000000000000, 11603586456402253758682,
   13165640999636298319902, 14645707413759609457174, 16005453046616810234697,
   17209661773352293786172, 18227146565371428249790, 19031559036148179016428,
   19602081521348300308529, 19924068438435844031891]

private theorem sLo_neg_eq : ∀ j : Fin 9,
    vecAt sLo19 j.1 + (vecAt posMidList (8 - j.1) + 1) = certD :=
  fin9_all rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem sHi_neg_eq : ∀ j : Fin 9,
    vecAt sHi19 j.1 + (vecAt posMidList (8 - j.1) - 1) = certD :=
  fin9_all rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem sLo_pos_eq : ∀ j : Fin 9,
    vecAt sLo19 (j.1 + 10) = certD + (vecAt posMidList j.1 - 1) :=
  fin9_all rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem sHi_pos_eq : ∀ j : Fin 9,
    vecAt sHi19 (j.1 + 10) = certD + (vecAt posMidList j.1 + 1) :=
  fin9_all rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem r19_shift_bounds (k : Fin 19) :
    (vecAt sLo19 k.1 : ℝ) / certD ≤ r19 k + 1 ∧
      r19 k + 1 ≤ (vecAt sHi19 k.1 : ℝ) / certD := by
  have hD : (0 : ℝ) < certD := by norm_num [certD]
  by_cases h1 : k.1 < 9
  · have hrk : r19 k = -rPos19 ⟨8 - k.1, by omega⟩ := by unfold r19; simp [h1]
    have ⟨hl, hr⟩ := (rPos19_spec ⟨8 - k.1, by omega⟩).1
    have hloR : (vecAt sLo19 k.1 : ℝ) = certD - (vecAt posMidList (8 - k.1) + 1 : ℕ) := by
      have he : (vecAt sLo19 k.1 : ℝ) + (vecAt posMidList (8 - k.1) + 1 : ℕ) = certD := by
        exact_mod_cast sLo_neg_eq ⟨k.1, h1⟩
      linarith
    have hhiR : (vecAt sHi19 k.1 : ℝ) = certD - (vecAt posMidList (8 - k.1) - 1 : ℕ) := by
      have he : (vecAt sHi19 k.1 : ℝ) + (vecAt posMidList (8 - k.1) - 1 : ℕ) = certD := by
        exact_mod_cast sHi_neg_eq ⟨k.1, h1⟩
      linarith
    rw [hrk, hloR, hhiR, sub_div, sub_div, div_self hD.ne']
    exact ⟨by linarith, by linarith⟩
  · by_cases h9 : k.1 = 9
    · have hk : k = ⟨9, by omega⟩ := Fin.ext h9
      rw [hk]
      have hrk : r19 ⟨9, by omega⟩ = 0 := by unfold r19; simp
      rw [hrk]; change (certD : ℝ) / certD ≤ _ ∧ _ ≤ (certD : ℝ) / certD
      rw [div_self hD.ne']; norm_num
    · have hj : k.1 - 10 < 9 := by omega
      have hke : k.1 = (k.1 - 10) + 10 := by omega
      have hrk : r19 k = rPos19 ⟨k.1 - 10, hj⟩ := by unfold r19; simp [h1, h9]
      have ⟨hl, hr⟩ := (rPos19_spec ⟨k.1 - 10, hj⟩).1
      have hlo_eq : vecAt sLo19 k.1 = certD + (vecAt posMidList (k.1 - 10) - 1) := by
        rw [hke]; exact sLo_pos_eq ⟨k.1 - 10, hj⟩
      have hhi_eq : vecAt sHi19 k.1 = certD + (vecAt posMidList (k.1 - 10) + 1) := by
        rw [hke]; exact sHi_pos_eq ⟨k.1 - 10, hj⟩
      rw [hrk, hlo_eq, hhi_eq, Nat.cast_add, Nat.cast_add]
      rw [add_div, add_div, div_self hD.ne']
      exact ⟨by linarith, by linarith⟩

private theorem xe_bounds (k : Fin 19) :
    (vecAt xeLo19 k.1 : ℝ) / certT ≤ shiftNode (17 / 10) r19 k ∧
      shiftNode (17 / 10) r19 k ≤ (vecAt xeHi19 k.1 : ℝ) / certT := by
  have ⟨hl, hr⟩ := r19_shift_bounds k
  have h1 : Nat.ble (20 * certD * vecAt xeLo19 k.1) (17 * vecAt sLo19 k.1 * certT) = true :=
    by fin_cases k <;> rfl
  have h2 : Nat.ble (17 * vecAt sHi19 k.1 * certT) (20 * certD * vecAt xeHi19 k.1) = true :=
    by fin_cases k <;> rfl
  have h1R : (20 : ℝ) * certD * vecAt xeLo19 k.1 ≤ 17 * vecAt sLo19 k.1 * certT :=
    by exact_mod_cast Nat.le_of_ble_eq_true h1
  have h2R : (17 : ℝ) * vecAt sHi19 k.1 * certT ≤ 20 * certD * vecAt xeHi19 k.1 :=
    by exact_mod_cast Nat.le_of_ble_eq_true h2
  have hT : (0 : ℝ) < certT := by norm_num [certT]
  have hD : (0 : ℝ) < certD := by norm_num [certD]
  unfold shiftNode
  constructor
  · have : (vecAt xeLo19 k.1 : ℝ) / certT ≤ (17 / 20 : ℝ) * (vecAt sLo19 k.1 / certD) := by
      rw [div_le_iff₀ hT]; field_simp; linarith
    exact this.trans (by linarith)
  · have : (17 / 20 : ℝ) * (vecAt sHi19 k.1 / certD) ≤ (vecAt xeHi19 k.1 : ℝ) / certT := by
      rw [le_div_iff₀ hT]; field_simp; linarith
    exact (show (17 / 10 : ℝ) / 2 * (r19 k + 1) ≤ _ by linarith).trans this

private theorem xi_bounds (k : Fin 19) :
    (vecAt xiLo19 k.1 : ℝ) / certT ≤ shiftNode (21 / 20) r19 k ∧
      shiftNode (21 / 20) r19 k ≤ (vecAt xiHi19 k.1 : ℝ) / certT := by
  have ⟨hl, hr⟩ := r19_shift_bounds k
  have h1 : Nat.ble (40 * certD * vecAt xiLo19 k.1) (21 * vecAt sLo19 k.1 * certT) = true :=
    by fin_cases k <;> rfl
  have h2 : Nat.ble (21 * vecAt sHi19 k.1 * certT) (40 * certD * vecAt xiHi19 k.1) = true :=
    by fin_cases k <;> rfl
  have h1R : (40 : ℝ) * certD * vecAt xiLo19 k.1 ≤ 21 * vecAt sLo19 k.1 * certT :=
    by exact_mod_cast Nat.le_of_ble_eq_true h1
  have h2R : (21 : ℝ) * vecAt sHi19 k.1 * certT ≤ 40 * certD * vecAt xiHi19 k.1 :=
    by exact_mod_cast Nat.le_of_ble_eq_true h2
  have hT : (0 : ℝ) < certT := by norm_num [certT]
  have hD : (0 : ℝ) < certD := by norm_num [certD]
  unfold shiftNode
  constructor
  · have : (vecAt xiLo19 k.1 : ℝ) / certT ≤ (21 / 40 : ℝ) * (vecAt sLo19 k.1 / certD) := by
      rw [div_le_iff₀ hT]; field_simp; linarith
    exact this.trans (by linarith)
  · have : (21 / 40 : ℝ) * (vecAt sHi19 k.1 / certD) ≤ (vecAt xiHi19 k.1 : ℝ) / certT := by
      rw [le_div_iff₀ hT]; field_simp; linarith
    exact (show (21 / 20 : ℝ) / 2 * (r19 k + 1) ≤ _ by linarith).trans this

private theorem we_bounds (k : Fin 19) :
    (vecAt weLo19 k.1 : ℝ) / certS ≤ shiftWeight (17 / 10) r19 k ∧
      shiftWeight (17 / 10) r19 k ≤ (vecAt weHi19 k.1 : ℝ) / certS := by
  have ⟨hl, hr⟩ := w19_bounds k
  have h1 : Nat.ble (20 * vecAt weLo19 k.1) (17 * vecAt wLo19 k.1) = true :=
    by fin_cases k <;> rfl
  have h2 : Nat.ble (17 * vecAt wHi19 k.1) (20 * vecAt weHi19 k.1) = true :=
    by fin_cases k <;> rfl
  have h1R : (20 : ℝ) * vecAt weLo19 k.1 ≤ 17 * vecAt wLo19 k.1 :=
    by exact_mod_cast Nat.le_of_ble_eq_true h1
  have h2R : (17 : ℝ) * vecAt wHi19 k.1 ≤ 20 * vecAt weHi19 k.1 :=
    by exact_mod_cast Nat.le_of_ble_eq_true h2
  have hS : (0 : ℝ) < certS := by norm_num [certS]
  unfold shiftWeight
  constructor <;> nlinarith [div_mul_cancel₀ (vecAt wLo19 k.1 : ℝ) hS.ne',
    div_mul_cancel₀ (vecAt wHi19 k.1 : ℝ) hS.ne',
    div_mul_cancel₀ (vecAt weLo19 k.1 : ℝ) hS.ne',
    div_mul_cancel₀ (vecAt weHi19 k.1 : ℝ) hS.ne']

private theorem wi_bounds (k : Fin 19) :
    (vecAt wiLo19 k.1 : ℝ) / certS ≤ shiftWeight (21 / 20) r19 k ∧
      shiftWeight (21 / 20) r19 k ≤ (vecAt wiHi19 k.1 : ℝ) / certS := by
  have ⟨hl, hr⟩ := w19_bounds k
  have h1 : Nat.ble (40 * vecAt wiLo19 k.1) (21 * vecAt wLo19 k.1) = true :=
    by fin_cases k <;> rfl
  have h2 : Nat.ble (21 * vecAt wHi19 k.1) (40 * vecAt wiHi19 k.1) = true :=
    by fin_cases k <;> rfl
  have h1R : (40 : ℝ) * vecAt wiLo19 k.1 ≤ 21 * vecAt wLo19 k.1 :=
    by exact_mod_cast Nat.le_of_ble_eq_true h1
  have h2R : (21 : ℝ) * vecAt wHi19 k.1 ≤ 40 * vecAt wiHi19 k.1 :=
    by exact_mod_cast Nat.le_of_ble_eq_true h2
  have hS : (0 : ℝ) < certS := by norm_num [certS]
  unfold shiftWeight
  constructor <;> nlinarith [div_mul_cancel₀ (vecAt wLo19 k.1 : ℝ) hS.ne',
    div_mul_cancel₀ (vecAt wHi19 k.1 : ℝ) hS.ne',
    div_mul_cancel₀ (vecAt wiLo19 k.1 : ℝ) hS.ne',
    div_mul_cancel₀ (vecAt wiHi19 k.1 : ℝ) hS.ne']

private def denSq19 : ℕ := 128000000000000000000
private def denAB19 : ℕ := 32000000000000000000000000000000000000
private def denAC19 : ℕ := 32000000000000000000
private def cABLo : ℕ := 4242640687119285144
private def cABHi : ℕ := 4242640687119285147

private def eAeLo19 : List ℕ :=
  [99993751724000, 99828547132058, 98988722968941, 96651122793214, 91908135161679, 84119856326059,
   73293788820022, 60278001452993, 46578032886616, 33832442722287, 23242309517053, 15281788807958,
   9782173562538, 6226900812589, 4036593602404, 2730923380444, 1973532515556, 1554185860768,
   1353947003749]
private def eAeHi19 : List ℕ :=
  [99993751724001, 99828547132060, 98988722968942, 96651122793215, 91908135161680, 84119856326060,
   73293788820023, 60278001452994, 46578032886617, 33832442722289, 23242309517054, 15281788807959,
   9782173562539, 6226900812590, 4036593602405, 2730923380445, 1973532515557, 1554185860769,
   1353947003750]
private def eAiLo19 : List ℕ :=
  [99997616312316, 99934558094434, 99612996900213, 98708968335932, 96832239764694, 93615917011367,
   88822861549391, 82439103756274, 74716259997749, 66137286889302, 57311690687897, 48839626616646,
   41196784335229, 34676028433488, 29390814057061, 25320426554095, 22369503300654, 20421153933668,
   19374417898134]
private def eAiHi19 : List ℕ :=
  [99997616312317, 99934558094435, 99612996900215, 98708968335933, 96832239764695, 93615917011368,
   88822861549392, 82439103756275, 74716259997750, 66137286889303, 57311690687898, 48839626616647,
   41196784335230, 34676028433489, 29390814057062, 25320426554096, 22369503300655, 20421153933669,
   19374417898135]

private theorem eAeLo_chk : checkExpSqDn certS certRatio certM 3 denSq19 eAeLo19 xeHi19 = true :=
  rfl
private theorem eAeHi_chk : checkExpSqUp certS certRatio certM 3 denSq19 eAeHi19 xeLo19 = true :=
  rfl
private theorem eAiLo_chk : checkExpSqDn certS certRatio certM 3 denSq19 eAiLo19 xiHi19 = true :=
  rfl
private theorem eAiHi_chk : checkExpSqUp certS certRatio certM 3 denSq19 eAiHi19 xiLo19 = true :=
  rfl

private theorem eAeLo_le (a : Fin 19) :
    (vecAt eAeLo19 a.1 : ℝ) / certS ≤ eAFactor (shiftNode (17 / 10) r19 a) := by
  have hnn : 0 ≤ shiftNode (17 / 10) r19 a :=
    (by positivity : (0 : ℝ) ≤ _).trans (xe_bounds a).1
  have hup := (xe_bounds a).2
  have heq : Real.exp (-(3 / 2 * shiftNode (17 / 10) r19 a ^ 2)) =
      eAFactor (shiftNode (17 / 10) r19 a) := by unfold eAFactor; congr 1; ring
  rw [← heq]
  refine checkExpSqDn_spec (by decide) (by decide) (by decide)
    (rfl : eAeLo19.length = 19) (rfl : xeHi19.length = 19) eAeLo_chk a ?_
  have hsq : shiftNode (17 / 10) r19 a ^ 2 ≤ ((vecAt xeHi19 a.1 : ℝ) / certT) ^ 2 :=
    pow_le_pow_left₀ hnn hup 2
  have hcalc : (3 : ℝ) / 2 * ((vecAt xeHi19 a.1 : ℝ) / certT) ^ 2 =
      64 * ((3 : ℝ) * (vecAt xeHi19 a.1 : ℝ) ^ 2 / denSq19 /
        (certS * certRatio : ℕ)) := by
    unfold denSq19 certT certS certRatio; push_cast; ring
  nlinarith
private theorem eAeHi_ge (a : Fin 19) :
    eAFactor (shiftNode (17 / 10) r19 a) ≤ (vecAt eAeHi19 a.1 : ℝ) / certS := by
  have hlo := (xe_bounds a).1
  have heq : Real.exp (-(3 / 2 * shiftNode (17 / 10) r19 a ^ 2)) =
      eAFactor (shiftNode (17 / 10) r19 a) := by unfold eAFactor; congr 1; ring
  rw [← heq]
  refine checkExpSqUp_spec (by decide) (by decide) (by decide)
    (rfl : eAeHi19.length = 19) (rfl : xeLo19.length = 19) eAeHi_chk a ?_
  have hsq : ((vecAt xeLo19 a.1 : ℝ) / certT) ^ 2 ≤ shiftNode (17 / 10) r19 a ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlo 2
  have hcalc : (3 : ℝ) / 2 * ((vecAt xeLo19 a.1 : ℝ) / certT) ^ 2 =
      64 * ((3 : ℝ) * (vecAt xeLo19 a.1 : ℝ) ^ 2 / denSq19 /
        (certS * certRatio : ℕ)) := by
    unfold denSq19 certT certS certRatio; push_cast; ring
  nlinarith
private theorem eAiLo_le (a : Fin 19) :
    (vecAt eAiLo19 a.1 : ℝ) / certS ≤ eAFactor (shiftNode (21 / 20) r19 a) := by
  have hnn : 0 ≤ shiftNode (21 / 20) r19 a :=
    (by positivity : (0 : ℝ) ≤ _).trans (xi_bounds a).1
  have hup := (xi_bounds a).2
  have heq : Real.exp (-(3 / 2 * shiftNode (21 / 20) r19 a ^ 2)) =
      eAFactor (shiftNode (21 / 20) r19 a) := by unfold eAFactor; congr 1; ring
  rw [← heq]
  refine checkExpSqDn_spec (by decide) (by decide) (by decide)
    (rfl : eAiLo19.length = 19) (rfl : xiHi19.length = 19) eAiLo_chk a ?_
  have hsq : shiftNode (21 / 20) r19 a ^ 2 ≤ ((vecAt xiHi19 a.1 : ℝ) / certT) ^ 2 :=
    pow_le_pow_left₀ hnn hup 2
  have hcalc : (3 : ℝ) / 2 * ((vecAt xiHi19 a.1 : ℝ) / certT) ^ 2 =
      64 * ((3 : ℝ) * (vecAt xiHi19 a.1 : ℝ) ^ 2 / denSq19 /
        (certS * certRatio : ℕ)) := by
    unfold denSq19 certT certS certRatio; push_cast; ring
  nlinarith
private theorem eAiHi_ge (a : Fin 19) :
    eAFactor (shiftNode (21 / 20) r19 a) ≤ (vecAt eAiHi19 a.1 : ℝ) / certS := by
  have hlo := (xi_bounds a).1
  have heq : Real.exp (-(3 / 2 * shiftNode (21 / 20) r19 a ^ 2)) =
      eAFactor (shiftNode (21 / 20) r19 a) := by unfold eAFactor; congr 1; ring
  rw [← heq]
  refine checkExpSqUp_spec (by decide) (by decide) (by decide)
    (rfl : eAiHi19.length = 19) (rfl : xiLo19.length = 19) eAiHi_chk a ?_
  have hsq : ((vecAt xiLo19 a.1 : ℝ) / certT) ^ 2 ≤ shiftNode (21 / 20) r19 a ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlo 2
  have hcalc : (3 : ℝ) / 2 * ((vecAt xiLo19 a.1 : ℝ) / certT) ^ 2 =
      64 * ((3 : ℝ) * (vecAt xiLo19 a.1 : ℝ) ^ 2 / denSq19 /
        (certS * certRatio : ℕ)) := by
    unfold denSq19 certT certS certRatio; push_cast; ring
  nlinarith

/-- 19x19 upper-bound table for `eAB(end, end)` -/
private def eAB_ee_hi : List (List ℕ) := [
  [99964659555276, 99814937523200, 99550198380252, 99178119962005, 98709476972409, 98157691371834,
    97538343450784, 96868631938337, 96166808662587, 95451614337162, 94741738925095, 94055325209610,
    93409528573423, 92820140248172, 92301276017470, 91865127944155, 91521773214042, 91279030029475,
    91142316895826],
  [99814937523200, 99033979959446, 97665190992570, 95767337952572, 93419517934388, 90715097614559,
    87755365424801, 84643388551131, 81478640901162, 78352796066456, 75346871076050, 72529712674761,
    69957667223122, 67675181010293, 65716038652045, 64104952509717, 62859249944013, 61990446652206,
    61505429986416],
  [99550198380252, 97665190992570, 94412407066475, 90009336606367, 84732896429962, 78886362084565,
    72768150594884, 66646648509322, 60743701852676, 55227236101931, 50211750591951, 45764455913065,
    41914595637296, 38663813704438, 35996026761336, 33885902534723, 32305580402276, 31229628247903,
    30638287588420],
  [99178119962005, 95767337952572, 90009336606367, 82474104682189, 73839746871176, 64781205956848,
    55881260070753, 47577756569478, 40148721320681, 33727106442049, 28332601177197, 23908603325846,
    20355978149259, 17559378405382, 15405222216402, 13792422643892, 12637774611404, 11877929712494,
    11469442144992],
  [98709476972409, 93419517934388, 84732896429962, 73839746871176, 62043838740318, 50493435965819,
    40014367394902, 31064048002070, 23779845839678, 18074841988407, 13738521061425, 10516978111935,
    8164565234324, 6470146201321, 5265630230800, 4424445190418, 3855644344413, 3497126940168,
    3309711720965],
  [98157691371834, 90715097614559, 78886362084565, 64781205956848, 50493435965819, 37597752656672,
    26949256989666, 18755776403076, 12793915839559, 8638827971814, 5833190530755, 3979006100454,
    2769254408580, 1984941743941, 1478000997538, 1152021602937, 946036130385, 822678370956,
    760300570272],
  [97538343450784, 87755365424801, 72768150594884, 55881260070753, 40014367394902, 26949256989666,
    17246646485577, 10609865536216, 6353705248292, 3753388819459, 2217277490772, 1327813965404,
    816850257923, 522757552665, 352071731911, 252104687908, 193600187924, 160536367912,
    144434764131],
  [96868631938337, 84643388551131, 66646648509322, 47577756569478, 31064048002070, 18755776403076,
    10609865536216, 5706773370743, 2965872378366, 1514805827074, 773680186132, 402090033135,
    216273871324, 122342932888, 73867922609, 48229190681, 34429888750, 27109461625, 23688129458],
  [96166808662587, 81478640901162, 60743701852676, 40148721320681, 23779845839678, 12793915839559,
    6353705248292, 2965872378366, 1327238862795, 581381354479, 254667256069, 113964539339,
    53197979152, 26419142003, 14213896996, 8418805587, 5564433333, 4148378957, 3514770679],
  [95451614337162, 78352796066456, 55227236101931, 33727106442049, 18074841988407, 8638827971814,
    3753388819459, 1514805827074, 581381354479, 217524105024, 81386745382, 31236172598,
    12606404118, 5477217098, 2617822956, 1402929017, 856764518, 603893399, 495714364],
  [94741738925095, 75346871076050, 50211750591951, 28332601177197, 13738521061425, 5833190530755,
    2217277490772, 773680186132, 254667256069, 81386745382, 26009634792, 8561421687, 2987358304,
    1135536769, 482133579, 233787300, 131917375, 87910782, 69914300],
  [94055325209610, 72529712674761, 45764455913065, 23908603325846, 10516978111935, 3979006100454,
    1327813965404, 402090033135, 113964539339, 31236172598, 8561421687, 2426567182, 734815648,
    245211607, 92773654, 40809514, 21320007, 13452397, 10373666],
  [93409528573423, 69957667223122, 41914595637296, 20355978149259, 8164565234324, 2769254408580,
    816850257923, 216273871324, 53197979152, 12606404118, 2987358304, 734815648, 194553927,
    57387803, 19464775, 7807114, 3791554, 2271680, 1701341],
  [92820140248172, 67675181010293, 38663813704438, 17559378405382, 6470146201321, 1984941743941,
    522757552665, 122342932888, 26419142003, 5477217098, 1135536769, 245211607, 57387803, 15113747,
    4636667, 1708484, 775917, 443293, 323205],
  [92301276017470, 65716038652045, 35996026761336, 15405222216402, 5265630230800, 1478000997538,
    352071731911, 73867922609, 14213896996, 2617822956, 482133579, 92773654, 19464775, 4636667,
    1301459, 444849, 190383, 104282, 74246],
  [91865127944155, 64104952509717, 33885902534723, 13792422643892, 4424445190418, 1152021602937,
    252104687908, 48229190681, 8418805587, 1402929017, 233787300, 40809514, 7807114, 1708484,
    444849, 142703, 58084, 30703, 21425],
  [91521773214042, 62859249944013, 32305580402276, 12637774611404, 3855644344413, 946036130385,
    193600187924, 34429888750, 5564433333, 856764518, 131917375, 21320007, 3791554, 775917, 190383,
    58084, 22722, 11678, 8021],
  [91279030029475, 61990446652206, 31229628247903, 11877929712494, 3497126940168, 822678370956,
    160536367912, 27109461625, 4148378957, 603893399, 87910782, 13452397, 2271680, 443293, 104282,
    30703, 11678, 5883, 3996],
  [91142316895826, 61505429986416, 30638287588420, 11469442144992, 3309711720965, 760300570272,
    144434764131, 23688129458, 3514770679, 495714364, 69914300, 10373666, 1701341, 323205, 74246,
    21425, 8021, 3996, 2697]
]

/-- 19x19 lower-bound table for `eAB(end, int)` -/
private def eAB_ei_lo : List (List ℕ) := [
  [99978170603266, 99885656230944, 99721941955645, 99491567564320, 99200933906735, 98858061353892,
    98472327368873, 98054171228998, 97614777162135, 97165748609970, 96718785591799, 96285375569457,
    95876506173857, 95502405910412, 95172316742624, 94894300432368, 94675078701688, 94519904650844,
    94432441061563],
  [99885656230944, 99402233717423, 98551404942600, 97364130979277, 95882838892964, 94158799398244,
    92249316000911, 90214854890034, 88116339997523, 86012797501725, 83959471470111, 82006464934080,
    80197899071681, 78571534273521, 77158763961207, 75984875124571, 75069465913567, 74426912327786,
    74066704001698],
  [99721941955645, 98551404942600, 96510991792903, 93705664856997, 90273766228772, 86374101792505,
    82172873323329, 77831821503883, 73498789600790, 69301358764664, 65343638347168, 61705845165001,
    58446031304411, 55603221648151, 53201262418339, 51252806689520, 49763019086307, 48732723084221,
    48160697961185],
  [99491567564320, 97364130979277, 93705664856997, 88779729555785, 82918192961206, 76478972937980,
    69807117589280, 63204718972345, 56912675482138, 51104326493058, 45888761408322, 41320525251474,
    37412405446606, 34148630479478, 31496733021316, 29417212683308, 27870803651996, 26823555656908,
    26249985302731],
  [99200933906735, 95882838892964, 90273766228772, 82918192961206, 74466499185691, 65569809806003,
    56794967421404, 48572971993817, 41182939801381, 34764361376206, 29346152259263, 24881343930309,
    21279364647367, 18431665814970, 16229590958502, 14575339605638, 13387730150005, 12604558186315,
    12182958106338],
  [98858061353892, 94158799398244, 86374101792505, 76478972937980, 65569809806003, 54651236030331,
    44491690078201, 35567553988592, 28082989124065, 22034563479395, 17288828677836, 13650699395388,
    10912644290970, 8884007444187, 7404657557555, 6348437604166, 5621152378450, 5156416509454,
    4911303955166],
  [98472327368873, 92249316000911, 82172873323329, 69807117589280, 56794967421404, 44491690078201,
    33771696612823, 25016847024146, 18226076402342, 13167305206111, 9512630286604, 6930446759479,
    5133823401843, 3896860876405, 3052698755938, 2483671183946, 2109916805618, 1879449451843,
    1760676639046],
  [98054171228998, 90214854890034, 77831821503883, 63204718972345, 48572971993817, 35567553988592,
    25016847024146, 17056437525480, 11384906288692, 7518008849751, 4964507887173, 3313731661755,
    2259295786171, 1589101603193, 1163619493411, 894244258718, 726187001316, 626509427231,
    576420731076],
  [97614777162135, 88116339997523, 73498789600790, 56912675482138, 41182939801381, 28082989124065,
    18226076402342, 11384906288692, 6928592605998, 4161270744050, 2499233998878, 1520976437240,
    950076902073, 616607232541, 420469599518, 304258656944, 235598086707, 196514905246,
    177392959434],
  [97165748609970, 86012797501725, 69301358764664, 51104326493058, 34764361376206, 22034563479395,
    13167305206111, 7518008849751, 4161270744050, 2267353682326, 1235414140767, 683810410908,
    390428613925, 233310395532, 147878244191, 100596037039, 74181701663, 59768928230, 52908486728],
  [96718785591799, 83959471470111, 65343638347168, 45888761408322, 29346152259263, 17288828677836,
    9512630286604, 4964507887173, 2499233998878, 1235414140767, 610686354256, 307431901387,
    160444383227, 88279439148, 52008457044, 33259736204, 23357256158, 18178390984, 15780265331],
  [96285375569457, 82006464934080, 61705845165001, 41320525251474, 24881343930309, 13650699395388,
    6930446759479, 3313731661755, 1520976437240, 683810410908, 307431901387, 141108793890,
    67469918505, 34254411772, 18793063565, 11316329480, 7577834430, 5701948967, 4856362404],
  [95876506173857, 80197899071681, 58446031304411, 37412405446606, 21279364647367, 10912644290970,
    5133823401843, 2259295786171, 950076902073, 390428613925, 160444383227, 67469918505,
    29692198317, 13968612786, 7163489375, 4074437362, 2608124096, 1900729374, 1589904645],
  [95502405910412, 78571534273521, 55603221648151, 34148630479478, 18431665814970, 8884007444187,
    3896860876405, 1589101603193, 616607232541, 233310395532, 88279439148, 34254411772,
    13968612786, 6127160631, 2953272981, 1594024120, 978967388, 692792130, 569972454],
  [95172316742624, 77158763961207, 53201262418339, 31496733021316, 16229590958502, 7404657557555,
    3052698755938, 1163619493411, 420469599518, 147878244191, 52008457044, 18793063565, 7163489375,
    2953272981, 1347413817, 694293439, 411042409, 283415311, 229772436],
  [94894300432368, 75984875124571, 51252806689520, 29417212683308, 14575339605638, 6348437604166,
    2483671183946, 894244258718, 304258656944, 100596037039, 33259736204, 11316329480, 4074437362,
    1594024120, 694293439, 344001410, 197444068, 133178644, 106640363],
  [94675078701688, 75069465913567, 49763019086307, 27870803651996, 13387730150005, 5621152378450,
    2109916805618, 726187001316, 235598086707, 74181701663, 23357256158, 7577834430, 2608124096,
    978967388, 411042409, 197444068, 110582616, 73304436, 58124323],
  [94519904650844, 74426912327786, 48732723084221, 26823555656908, 12604558186315, 5156416509454,
    1879449451843, 626509427231, 196514905246, 59768928230, 18178390984, 5701948967, 1900729374,
    692792130, 283415311, 133178644, 73304436, 47997756, 37794417],
  [94432441061563, 74066704001698, 48160697961185, 26249985302731, 12182958106338, 4911303955166,
    1760676639046, 576420731076, 177392959434, 52908486728, 15780265331, 4856362404, 1589904645,
    569972454, 229772436, 106640363, 58124323, 37794417, 29643498]
]

/-- 19x19 upper-bound table for `eAB(end, int)` -/
private def eAB_ei_hi : List (List ℕ) := [
  [99978170603267, 99885656230945, 99721941955646, 99491567564321, 99200933906736, 98858061353894,
    98472327368874, 98054171228999, 97614777162136, 97165748609971, 96718785591800, 96285375569458,
    95876506173859, 95502405910413, 95172316742625, 94894300432369, 94675078701689, 94519904650845,
    94432441061564],
  [99885656230945, 99402233717424, 98551404942601, 97364130979278, 95882838892965, 94158799398245,
    92249316000913, 90214854890036, 88116339997524, 86012797501726, 83959471470112, 82006464934081,
    80197899071682, 78571534273522, 77158763961209, 75984875124572, 75069465913568, 74426912327787,
    74066704001699],
  [99721941955646, 98551404942601, 96510991792905, 93705664856998, 90273766228773, 86374101792506,
    82172873323330, 77831821503884, 73498789600791, 69301358764665, 65343638347169, 61705845165002,
    58446031304412, 55603221648152, 53201262418340, 51252806689521, 49763019086308, 48732723084222,
    48160697961186],
  [99491567564321, 97364130979278, 93705664856998, 88779729555786, 82918192961207, 76478972937981,
    69807117589281, 63204718972346, 56912675482139, 51104326493059, 45888761408323, 41320525251475,
    37412405446607, 34148630479479, 31496733021317, 29417212683309, 27870803651997, 26823555656909,
    26249985302732],
  [99200933906736, 95882838892965, 90273766228773, 82918192961207, 74466499185692, 65569809806004,
    56794967421405, 48572971993818, 41182939801382, 34764361376207, 29346152259265, 24881343930310,
    21279364647369, 18431665814971, 16229590958503, 14575339605639, 13387730150006, 12604558186316,
    12182958106339],
  [98858061353894, 94158799398245, 86374101792506, 76478972937981, 65569809806004, 54651236030332,
    44491690078202, 35567553988593, 28082989124066, 22034563479396, 17288828677837, 13650699395389,
    10912644290971, 8884007444188, 7404657557556, 6348437604167, 5621152378451, 5156416509455,
    4911303955167],
  [98472327368874, 92249316000913, 82172873323330, 69807117589281, 56794967421405, 44491690078202,
    33771696612824, 25016847024147, 18226076402343, 13167305206112, 9512630286605, 6930446759480,
    5133823401844, 3896860876406, 3052698755939, 2483671183947, 2109916805619, 1879449451844,
    1760676639047],
  [98054171228999, 90214854890036, 77831821503884, 63204718972346, 48572971993818, 35567553988593,
    25016847024147, 17056437525481, 11384906288693, 7518008849752, 4964507887174, 3313731661756,
    2259295786172, 1589101603194, 1163619493412, 894244258719, 726187001317, 626509427232,
    576420731077],
  [97614777162136, 88116339997524, 73498789600791, 56912675482139, 41182939801382, 28082989124066,
    18226076402343, 11384906288693, 6928592605999, 4161270744051, 2499233998879, 1520976437241,
    950076902074, 616607232542, 420469599519, 304258656945, 235598086708, 196514905247,
    177392959435],
  [97165748609971, 86012797501726, 69301358764665, 51104326493059, 34764361376207, 22034563479396,
    13167305206112, 7518008849752, 4161270744051, 2267353682327, 1235414140768, 683810410909,
    390428613926, 233310395533, 147878244192, 100596037040, 74181701664, 59768928231, 52908486729],
  [96718785591800, 83959471470112, 65343638347169, 45888761408323, 29346152259265, 17288828677837,
    9512630286605, 4964507887174, 2499233998879, 1235414140768, 610686354257, 307431901388,
    160444383228, 88279439149, 52008457045, 33259736205, 23357256159, 18178390985, 15780265332],
  [96285375569458, 82006464934081, 61705845165002, 41320525251475, 24881343930310, 13650699395389,
    6930446759480, 3313731661756, 1520976437241, 683810410909, 307431901388, 141108793891,
    67469918506, 34254411773, 18793063566, 11316329481, 7577834431, 5701948968, 4856362405],
  [95876506173859, 80197899071682, 58446031304412, 37412405446607, 21279364647369, 10912644290971,
    5133823401844, 2259295786172, 950076902074, 390428613926, 160444383228, 67469918506,
    29692198318, 13968612787, 7163489376, 4074437363, 2608124097, 1900729375, 1589904646],
  [95502405910413, 78571534273522, 55603221648152, 34148630479479, 18431665814971, 8884007444188,
    3896860876406, 1589101603194, 616607232542, 233310395533, 88279439149, 34254411773,
    13968612787, 6127160632, 2953272982, 1594024121, 978967389, 692792131, 569972455],
  [95172316742625, 77158763961209, 53201262418340, 31496733021317, 16229590958503, 7404657557556,
    3052698755939, 1163619493412, 420469599519, 147878244192, 52008457045, 18793063566, 7163489376,
    2953272982, 1347413818, 694293440, 411042410, 283415312, 229772437],
  [94894300432369, 75984875124572, 51252806689521, 29417212683309, 14575339605639, 6348437604167,
    2483671183947, 894244258719, 304258656945, 100596037040, 33259736205, 11316329481, 4074437363,
    1594024121, 694293440, 344001411, 197444069, 133178645, 106640364],
  [94675078701689, 75069465913568, 49763019086308, 27870803651997, 13387730150006, 5621152378451,
    2109916805619, 726187001317, 235598086708, 74181701664, 23357256159, 7577834431, 2608124097,
    978967389, 411042410, 197444069, 110582617, 73304437, 58124324],
  [94519904650845, 74426912327787, 48732723084222, 26823555656909, 12604558186316, 5156416509455,
    1879449451844, 626509427232, 196514905247, 59768928231, 18178390985, 5701948968, 1900729375,
    692792131, 283415312, 133178645, 73304437, 47997757, 37794418],
  [94432441061564, 74066704001699, 48160697961186, 26249985302732, 12182958106339, 4911303955167,
    1760676639047, 576420731077, 177392959435, 52908486729, 15780265332, 4856362405, 1589904646,
    569972455, 229772437, 106640364, 58124324, 37794418, 29643499]
]

/-- 19x19 lower-bound table for `eAB(int, int)` -/
private def eAB_ii_lo : List (List ℕ) := [
  [99986516574579, 99929360460896, 99828166854819, 99685662244301, 99505702442431, 99293137010208,
    99053662193844, 98793653238631, 98519981341290, 98239821646288, 97960458636929, 97689094802303,
    97432667741328, 97197679997786, 96990044994438, 96814951516724, 96676748268153, 96578848424344,
    96523640263994],
  [99929360460896, 99630368320066, 99102785025456, 98363658076954, 97436642561755, 96350787661932,
    95139221974428, 93837757828584, 92483504439975, 91113572319906, 89763932618738, 88468472105436,
    87258260984372, 86161029529131, 85200832485922, 84397868310265, 83768413357529, 83324825561472,
    83075514769689],
  [99828166854819, 99102785025456, 97830414297390, 96064130913612, 93875600747950, 91349775244424,
    88579309849041, 85659110687996, 82681500737291, 79732358376287, 76888408114941, 74215677949310,
    71769005460517, 69592387668548, 67719928518098, 66177135126134, 64982337219993, 64148035502854,
    63681916362244],
  [99685662244301, 98363658076954, 96064130913612, 92912935522115, 89074687235600, 84736415350728,
    80091257492250, 75324024782231, 70600139682993, 66058656501117, 61809312535734, 57932991649723,
    54484674549589, 51497884123028, 48989743710136, 46965969530625, 45425343020662, 44363397865080,
    43775062536459],
  [99505702442431, 97436642561755, 93875600747950, 89074687235600, 83352196624727, 77052674507131,
    70509917155728, 64018072604645, 57813771461955, 52069441889961, 46895864258158, 42350959165480,
    38451708470229, 35186666732523, 32527358468292, 30437679467354, 28881059158401, 27825535727113,
    27246948789700],
  [99293137010208, 96350787661932, 91349775244424, 84736415350728, 77052674507131, 68854036398826,
    60640182424607, 52809228538657, 45638634937976, 39288947642526, 33822690116718, 29230144987390,
    25455421556100, 22418749685436, 20033326769395, 18216741886803, 16897922329058, 16020848861903,
    15546103722138],
  [99053662193844, 95139221974428, 88579309849041, 80091257492250, 70509917155728, 60640182424607,
    51146046885345, 42493266649264, 34943734829326, 28586425343182, 23385700409319, 19230898877374,
    15977456004238, 13475944187953, 11589628053263, 10203157491694, 9225446837348, 8589346191216,
    8249909148256],
  [98793653238631, 93837757828584, 85659110687996, 75324024782231, 64018072604645, 52809228538657,
    42493266649264, 33541160503359, 26130316289675, 20222191564529, 15649907453821, 12192095489109,
    9623572483797, 7743666078612, 6387837293977, 5429038515331, 4774005104512, 4357915631568,
    4139304684732],
  [98519981341290, 92483504439975, 82681500737291, 70600139682993, 57813771461955, 45638634937976,
    34943734829326, 26130316289675, 19227720930549, 14033596437294, 10242598676992, 7536909495529,
    5635969650260, 4315243635846, 3406486447514, 2789538800477, 2381933409634, 2129480604756,
    1999003920662],
  [98239821646288, 91113572319906, 79732358376287, 66058656501117, 52069441889961, 39288947642526,
    28586425343182, 20222191564529, 14033596437294, 9644757536002, 6628475340866, 4599963739412,
    3254039174592, 2367621265263, 1786486364206, 1408162879102, 1166669967157, 1020938434964,
    946880260666],
  [97960458636929, 89763932618738, 76888408114941, 61809312535734, 46895864258158, 33822690116718,
    23385700409319, 15649907453821, 10242598676992, 6628475340866, 4289603325293, 2807472534526,
    1878784238892, 1299029887713, 936898936388, 710842485411, 571434451846, 489469256333,
    448514492029],
  [97689094802303, 88468472105436, 74215677949310, 57932991649723, 42350959165480, 29230144987390,
    19230898877374, 12192095489109, 7536909495529, 4599963739412, 2807472534526, 1735523349764,
    1100295235226, 723898783705, 499626615804, 365243806704, 285110464373, 239177482105,
    216602134012],
  [97432667741328, 87258260984372, 71769005460517, 54484674549589, 38451708470229, 25455421556100,
    15977456004238, 9623572483797, 5635969650260, 3254039174592, 1878784238892, 1100295235226,
    662731973536, 415973113092, 275378425850, 194344024944, 147539608245, 121349782018,
    108677830498],
  [97197679997786, 86161029529131, 69592387668548, 51497884123028, 35186666732523, 22418749685436,
    13475944187953, 7743666078612, 4315243635846, 2367621265263, 1299029887713, 723898783705,
    415973113092, 250042064538, 159311210076, 108851665484, 80549477371, 65059928907, 57672471769],
  [96990044994438, 85200832485922, 67719928518098, 48989743710136, 32527358468292, 20033326769395,
    11589628053263, 6387837293977, 3406486447514, 1786486364206, 936898936388, 499626615804,
    275378425850, 159311210076, 98118435673, 65146973382, 47128424369, 37458947716, 32905784605],
  [96814951516724, 84397868310265, 66177135126134, 46965969530625, 30437679467354, 18216741886803,
    10203157491694, 5429038515331, 2789538800477, 1408162879102, 710842485411, 365243806704,
    194344024944, 108851665484, 65146973382, 42220414353, 29963864260, 23494938127, 20481575035],
  [96676748268153, 83768413357529, 64982337219993, 45425343020662, 28881059158401, 16897922329058,
    9225446837348, 4774005104512, 2381933409634, 1166669967157, 571434451846, 285110464373,
    147539608245, 80549477371, 47128424369, 29963864260, 20945981177, 16248592491, 14079071096],
  [96578848424344, 83324825561472, 64148035502854, 44363397865080, 27825535727113, 16020848861903,
    8589346191216, 4357915631568, 2129480604756, 1020938434964, 489469256333, 239177482105,
    121349782018, 65059928907, 37458947716, 23494938127, 16248592491, 12509060546, 10792376436],
  [96523640263994, 83075514769689, 63681916362244, 43775062536459, 27246948789700, 15546103722138,
    8249909148256, 4139304684732, 1999003920662, 946880260666, 448514492029, 216602134012,
    108677830498, 57672471769, 32905784605, 20481575035, 14079071096, 10792376436, 9288732020]
]

/-- 19x19 upper-bound table for `eAB(int, int)` -/
private def eAB_ii_hi : List (List ℕ) := [
  [99986516574580, 99929360460897, 99828166854820, 99685662244302, 99505702442432, 99293137010209,
    99053662193845, 98793653238632, 98519981341291, 98239821646289, 97960458636930, 97689094802304,
    97432667741329, 97197679997788, 96990044994439, 96814951516725, 96676748268154, 96578848424346,
    96523640263995],
  [99929360460897, 99630368320067, 99102785025458, 98363658076955, 97436642561756, 96350787661933,
    95139221974429, 93837757828585, 92483504439977, 91113572319907, 89763932618739, 88468472105437,
    87258260984373, 86161029529132, 85200832485923, 84397868310266, 83768413357530, 83324825561473,
    83075514769690],
  [99828166854820, 99102785025458, 97830414297391, 96064130913613, 93875600747951, 91349775244425,
    88579309849042, 85659110687998, 82681500737292, 79732358376288, 76888408114942, 74215677949311,
    71769005460518, 69592387668549, 67719928518099, 66177135126135, 64982337219995, 64148035502855,
    63681916362245],
  [99685662244302, 98363658076955, 96064130913613, 92912935522116, 89074687235601, 84736415350729,
    80091257492251, 75324024782232, 70600139682994, 66058656501118, 61809312535735, 57932991649725,
    54484674549590, 51497884123029, 48989743710137, 46965969530626, 45425343020663, 44363397865081,
    43775062536460],
  [99505702442432, 97436642561756, 93875600747951, 89074687235601, 83352196624728, 77052674507132,
    70509917155729, 64018072604646, 57813771461956, 52069441889962, 46895864258159, 42350959165481,
    38451708470230, 35186666732524, 32527358468293, 30437679467355, 28881059158403, 27825535727114,
    27246948789701],
  [99293137010209, 96350787661933, 91349775244425, 84736415350729, 77052674507132, 68854036398827,
    60640182424608, 52809228538658, 45638634937977, 39288947642527, 33822690116719, 29230144987391,
    25455421556101, 22418749685437, 20033326769396, 18216741886804, 16897922329059, 16020848861904,
    15546103722139],
  [99053662193845, 95139221974429, 88579309849042, 80091257492251, 70509917155729, 60640182424608,
    51146046885346, 42493266649265, 34943734829327, 28586425343183, 23385700409320, 19230898877375,
    15977456004239, 13475944187954, 11589628053264, 10203157491695, 9225446837349, 8589346191217,
    8249909148257],
  [98793653238632, 93837757828585, 85659110687998, 75324024782232, 64018072604646, 52809228538658,
    42493266649265, 33541160503360, 26130316289676, 20222191564530, 15649907453822, 12192095489110,
    9623572483798, 7743666078613, 6387837293978, 5429038515332, 4774005104513, 4357915631569,
    4139304684733],
  [98519981341291, 92483504439977, 82681500737292, 70600139682994, 57813771461956, 45638634937977,
    34943734829327, 26130316289676, 19227720930550, 14033596437295, 10242598676993, 7536909495530,
    5635969650261, 4315243635847, 3406486447515, 2789538800478, 2381933409635, 2129480604757,
    1999003920663],
  [98239821646289, 91113572319907, 79732358376288, 66058656501118, 52069441889962, 39288947642527,
    28586425343183, 20222191564530, 14033596437295, 9644757536003, 6628475340867, 4599963739413,
    3254039174593, 2367621265264, 1786486364207, 1408162879103, 1166669967158, 1020938434965,
    946880260667],
  [97960458636930, 89763932618739, 76888408114942, 61809312535735, 46895864258159, 33822690116719,
    23385700409320, 15649907453822, 10242598676993, 6628475340867, 4289603325294, 2807472534527,
    1878784238893, 1299029887714, 936898936389, 710842485412, 571434451847, 489469256334,
    448514492030],
  [97689094802304, 88468472105437, 74215677949311, 57932991649725, 42350959165481, 29230144987391,
    19230898877375, 12192095489110, 7536909495530, 4599963739413, 2807472534527, 1735523349765,
    1100295235227, 723898783706, 499626615805, 365243806705, 285110464374, 239177482106,
    216602134013],
  [97432667741329, 87258260984373, 71769005460518, 54484674549590, 38451708470230, 25455421556101,
    15977456004239, 9623572483798, 5635969650261, 3254039174593, 1878784238893, 1100295235227,
    662731973537, 415973113093, 275378425851, 194344024945, 147539608246, 121349782019,
    108677830499],
  [97197679997788, 86161029529132, 69592387668549, 51497884123029, 35186666732524, 22418749685437,
    13475944187954, 7743666078613, 4315243635847, 2367621265264, 1299029887714, 723898783706,
    415973113093, 250042064539, 159311210077, 108851665485, 80549477372, 65059928908, 57672471770],
  [96990044994439, 85200832485923, 67719928518099, 48989743710137, 32527358468293, 20033326769396,
    11589628053264, 6387837293978, 3406486447515, 1786486364207, 936898936389, 499626615805,
    275378425851, 159311210077, 98118435674, 65146973383, 47128424370, 37458947717, 32905784606],
  [96814951516725, 84397868310266, 66177135126135, 46965969530626, 30437679467355, 18216741886804,
    10203157491695, 5429038515332, 2789538800478, 1408162879103, 710842485412, 365243806705,
    194344024945, 108851665485, 65146973383, 42220414354, 29963864261, 23494938128, 20481575036],
  [96676748268154, 83768413357530, 64982337219995, 45425343020663, 28881059158403, 16897922329059,
    9225446837349, 4774005104513, 2381933409635, 1166669967158, 571434451847, 285110464374,
    147539608246, 80549477372, 47128424370, 29963864261, 20945981178, 16248592492, 14079071097],
  [96578848424346, 83324825561473, 64148035502855, 44363397865081, 27825535727114, 16020848861904,
    8589346191217, 4357915631569, 2129480604757, 1020938434965, 489469256334, 239177482106,
    121349782019, 65059928908, 37458947717, 23494938128, 16248592492, 12509060547, 10792376437],
  [96523640263995, 83075514769690, 63681916362245, 43775062536460, 27246948789701, 15546103722139,
    8249909148257, 4139304684733, 1999003920663, 946880260667, 448514492030, 216602134013,
    108677830499, 57672471770, 32905784606, 20481575036, 14079071097, 10792376437, 9288732021]
]

/-- 19x19 lower-bound table for `eAC(end, end)` -/
private def eAC_ee_lo : List (List ℕ) := [
  [99975009238360, 99869105574306, 99681732306533, 99418141072994, 99085728122866, 98693748165214,
    98253003355096, 97775494977660, 97274051922436, 96761951505180, 96252547046736, 95758914452238,
    95293527315929, 94867967152462, 94492672521728, 94176728291635, 93927694096437, 93751468036575,
    93652156978230],
  [99869105574306, 99315950278238, 98343338104210, 96988157071253, 95300733214254, 93341534993272,
    91177658229450, 88879284234625, 86516402194326, 84156025764346, 81860046104805, 79683772584774,
    77675132373183, 75874439743891, 74314608435668, 73021664565153, 72015418725614, 71310163700877,
    70915190756164],
  [99681732306533, 98343338104210, 96015840110038, 92827450829268, 88945732943059, 84560854959873,
    79868914783798, 75057215948429, 70293030867091, 65716565233253, 61438052859353, 57538331144919,
    54071937220469, 51071703900177, 48553953103306, 46523597356988, 44978692485605, 43914178929743,
    43324557530522],
  [99418141072994, 96988157071253, 92827450829268, 87262492626959, 80698805566678, 73565523441566,
    66265916583119, 59141202748394, 52450977262663, 46369328737586, 40992842455671, 36355612460599,
    32446765372624, 29227205176922, 26643698534023, 24639619873866, 23162487263912, 22168837026099,
    21626985018717],
  [99085728122866, 95300733214254, 88945732943059, 80698805566678, 71353588099605, 61681567622560,
    52326803363337, 43749412271689, 36217058824181, 29831311540865, 24571491367321, 20341008073931,
    17006717228052, 14427440523134, 12471792546801, 11027513257465, 10005057227622, 9337883542275,
    8981183921307],
  [98693748165214, 93341534993272, 84560854959873, 73565523441566, 61681567622560, 50071902053708,
    39567241871782, 30621669334196, 23364479573085, 17699459133729, 13407996212653, 10230364981334,
    7917429641462, 6256420083473, 5078840660203, 4258392232815, 3704679355184, 3356178507768,
    3174171205881],
  [98253003355096, 91177658229450, 79868914783798, 66265916583119, 52326803363337, 39567241871782,
    28858163529179, 20467879393985, 14243355694848, 9816693450726, 6765784157197, 4708229340741,
    3339348680593, 2435536715392, 1841646424231, 1454253940404, 1206570423128, 1056919778121,
    980809410550],
  [97775494977660, 88879284234625, 75057215948429, 59141202748394, 43749412271689, 30621669334196,
    20467879393985, 13201867769678, 8310911226826, 5167947249718, 3213568048912, 2023022745100,
    1304858127301, 872182325672, 610469430080, 451591742046, 355830927624, 300493855298,
    273153092009],
  [97274051922436, 86516402194326, 70293030867091, 52450977262663, 36217058824181, 23364479573085,
    14243355694848, 8310911226826, 4706787297551, 2625640627495, 1464690938624, 829510569491,
    484014360973, 295062797491, 190351975797, 131436801839, 98074995767, 79684181610, 70871815952],
  [96761951505180, 84156025764346, 65716565233253, 46369328737586, 29831311540865, 17699459133729,
    9816693450726, 5167947249718, 2625640627495, 1310187407299, 653779890617, 332161099813,
    174864484753, 96985508386, 57543264227, 37019967486, 26121131500, 20397719909, 17740351610],
  [96252547046736, 81860046104805, 61438052859353, 40992842455671, 24571491367321, 13407996212653,
    6765784157197, 3213568048912, 1464690938624, 653779890617, 291821389826, 133007342265,
    63174960277, 31878599799, 17395287041, 10426896984, 6957058784, 5221450093, 4440694386],
  [95758914452238, 79683772584774, 57538331144919, 36355612460599, 20341008073931, 10230364981334,
    4708229340741, 2023022745100, 829510569491, 332161099813, 133007342265, 54537694396,
    23433649519, 10784658849, 5424067274, 3034772041, 1917521659, 1384610600, 1152174675],
  [95293527315929, 77675132373183, 54071937220469, 32446765372624, 17006717228052, 7917429641462,
    3339348680593, 1304858127301, 484014360973, 174864484753, 63174960277, 23433649519, 9156752095,
    3862059962, 1797971214, 942392490, 565498289, 393659941, 320877911],
  [94867967152462, 75874439743891, 51071703900177, 29227205176922, 14427440523134, 6256420083473,
    2435536715392, 872182325672, 295062797491, 96985508386, 31878599799, 10784658849, 3862059962,
    1503445854, 651965178, 321829910, 184176131, 123970455, 99150315],
  [94492672521728, 74314608435668, 48553953103306, 26643698534023, 12471792546801, 5078840660203,
    1841646424231, 610469430080, 190351975797, 57543264227, 17395287041, 5424067274, 1797971214,
    651965178, 265497300, 124278063, 68196862, 44556882, 35042159],
  [94176728291635, 73021664565153, 46523597356988, 24639619873866, 11027513257465, 4258392232815,
    1454253940404, 451591742046, 131436801839, 37019967486, 10426896984, 3034772041, 942392490,
    321829910, 124278063, 55620906, 29457696, 18768101, 14552193],
  [93927694096437, 72015418725614, 44978692485605, 23162487263912, 10005057227622, 3704679355184,
    1206570423128, 355830927624, 98074995767, 26121131500, 6957058784, 1917521659, 565498289,
    184176131, 68196862, 29457696, 15169705, 9474547, 7264242],
  [93751468036575, 71310163700877, 43914178929743, 22168837026099, 9337883542275, 3356178507768,
    1056919778121, 300493855298, 79684181610, 20397719909, 5221450093, 1384610600, 393659941,
    123970455, 44556882, 18768101, 9474547, 5834609, 4437978],
  [93652156978230, 70915190756164, 43324557530522, 21626985018717, 8981183921307, 3174171205881,
    980809410550, 273153092009, 70871815952, 17740351610, 4440694386, 1152174675, 320877911,
    99150315, 35042159, 14552193, 7264242, 4437978, 3360521]
]

/-- 19x19 lower-bound table for `eAC(end, int)` -/
private def eAC_ei_lo : List (List ℕ) := [
  [99984563792038, 99919133199752, 99803303111552, 99640215699507, 99434311464144, 99191170389277,
    98917339559261, 98620137240581, 98307439903893, 97987459909838, 97668521415761, 97358841391180,
    97066321661732, 96798356768054, 96561661243508, 96362118770780, 96204654557878, 96093130435662,
    96030246424365],
  [99919133199752, 99576944429846, 98973501939175, 98128881467044, 97070855096793, 95833395008932,
    94455055836678, 92977274084366, 91442700494696, 89893668732404, 88370877439691, 86912331618140,
    85552558373834, 84322084983194, 83247146325366, 82349574940228, 81646819803722, 81152034986013,
    80874117092433],
  [99803303111552, 98973501939175, 97520099473385, 95507051681747, 93020202130908, 90160512702061,
    87037002365459, 83759970183454, 80435138413055, 77159145834209, 74016579113619, 71078508896614,
    68402330320001, 66032607928245, 64002589216978, 62336065044741, 61049299765015, 60152805237947,
    59652672809941],
  [99640215699507, 98128881467044, 95507051681747, 91928960653281, 87594480722597, 82727860296959,
    77556896744771, 72295060182546, 67128450960104, 62208315397121, 57648797926942, 53528892496612,
    49897232444496, 46778370559282, 44179433140350, 42096358721418, 40519254195418, 39436651541242,
    38838479798341],
  [99434311464144, 97070855096793, 93020202130908, 87594480722597, 81182554079159, 74197641662846,
    67030248929443, 60013305698103, 53402799211032, 47373221689604, 42024428801641, 37395409353751,
    33480736967196, 30246542652259, 27644142989934, 25620588360579, 24126179924808, 23119422724921,
    22569896650429],
  [99191170389277, 95833395008932, 90160512702061, 82727860296959, 74197641662846, 65231170666673,
    56402145875666, 48144561841636, 40737140386334, 34316635589989, 28908054592148, 24460321855036,
    20879196348524, 18053201654677, 15871548634487, 14235004676646, 13061499351802, 12288320559929,
    11872341798110],
  [98917339559261, 94455055836678, 87037002365459, 77556896744771, 67030248929443, 56402145875666,
    46412669028010, 37539300136285, 30007591482071, 23844613577547, 18947391929214, 15145876310917,
    12250224099791, 10080566755668, 8482224156157, 7330948252528, 6532458393675, 6019429999021,
    5747886055123],
  [98620137240581, 92977274084366, 83759970183454, 72295060182546, 60013305698103, 48144561841636,
    37539300136285, 28632747795980, 21514148505804, 16042967052071, 11963140989029, 8988895989577,
    6856195797456, 5345916173886, 4288662136503, 3560088216041, 3072789917070, 2768168828011,
    2609779290876],
  [98307439903893, 91442700494696, 80435138413055, 67128450960104, 53402799211032, 40737140386334,
    30007591482071, 21514148505804, 15143010939828, 10559547845387, 7363400260496, 5182824254882,
    3715861393462, 2737159497244, 2087981385739, 1661055023678, 1386260444116, 1219387114507,
    1134238169644],
  [97987459909838, 89893668732404, 77159145834209, 62208315397121, 47373221689604, 34316635589989,
    23844613577547, 16042967052071, 10559547845387, 6873477647818, 4474121019840, 2944885121418,
    1981357123754, 1376728637956, 997286933209, 759459481798, 612301943784, 525561984967,
    482150420253],
  [97668521415761, 88370877439691, 74016579113619, 57648797926942, 42024428801641, 28908054592148,
    18947391929214, 11963140989029, 7363400260496, 4474121019840, 2718548251080, 1673286214592,
    1056491520044, 692463023977, 476336251818, 347236362595, 270449663303, 226519861295,
    204956096498],
  [97358841391180, 86912331618140, 71078508896614, 53528892496612, 37395409353751, 24460321855036,
    15145876310917, 8988895989577, 5182824254882, 2944885121418, 1673286214592, 964784595172,
    572588089346, 354547598749, 231909438303, 162012475391, 122010837213, 99782714568,
    89076125541],
  [97066321661732, 85552558373834, 68402330320001, 49897232444496, 33480736967196, 20879196348524,
    12250224099791, 6856195797456, 3715861393462, 1981357123754, 1056491520044, 572588089346,
    320465651883, 188023331277, 117254768188, 78677230369, 57392431419, 45887301636, 40444265164],
  [96798356768054, 84322084983194, 66032607928245, 46778370559282, 30246542652259, 18053201654677,
    10080566755668, 5345916173886, 2737159497244, 1376728637956, 692463023977, 354547598749,
    188023331277, 104988676181, 62664409759, 40518336143, 28703723842, 22477880414, 19580722295],
  [96561661243508, 83247146325366, 64002589216978, 44179433140350, 27644142989934, 15871548634487,
    8482224156157, 4288662136503, 2087981385739, 997286933209, 476336251818, 231909438303,
    117254768188, 62664409759, 35978009067, 22512313002, 15539702991, 11947331182, 10299959780],
  [96362118770780, 82349574940228, 62336065044741, 42096358721418, 25620588360579, 14235004676646,
    7330948252528, 3560088216041, 1661055023678, 759459481798, 347236362595, 162012475391,
    78677230369, 40518336143, 22512313002, 13701391807, 9252728802, 7004027706, 5985533650],
  [96204654557878, 81646819803722, 61049299765015, 40519254195418, 24126179924808, 13061499351802,
    6532458393675, 3072789917070, 1386260444116, 612301943784, 270449663303, 122010837213,
    57392431419, 28703723842, 15539702991, 9252728802, 6141162499, 4591895572, 3897042945],
  [96093130435662, 81152034986013, 60152805237947, 39436651541242, 23119422724921, 12288320559929,
    6019429999021, 2768168828011, 1219387114507, 525561984967, 226519861295, 99782714568,
    45887301636, 22477880414, 11947331182, 7004027706, 4591895572, 3403678048, 2874455216],
  [96030246424365, 80874117092433, 59652672809941, 38838479798341, 22569896650429, 11872341798110,
    5747886055123, 2609779290876, 1134238169644, 482150420253, 204956096498, 89076125541,
    40444265164, 19580722295, 10299959780, 5985533650, 3897042945, 2874455216, 2420789661]
]

/-- 19x19 upper-bound table for `eAC(end, int)` -/
private def eAC_ei_hi : List (List ℕ) := [
  [99984563792039, 99919133199753, 99803303111553, 99640215699508, 99434311464145, 99191170389278,
    98917339559263, 98620137240582, 98307439903894, 97987459909839, 97668521415763, 97358841391181,
    97066321661733, 96798356768055, 96561661243509, 96362118770781, 96204654557880, 96093130435663,
    96030246424366],
  [99919133199753, 99576944429847, 98973501939176, 98128881467046, 97070855096794, 95833395008934,
    94455055836679, 92977274084367, 91442700494697, 89893668732405, 88370877439692, 86912331618141,
    85552558373835, 84322084983195, 83247146325368, 82349574940229, 81646819803723, 81152034986015,
    80874117092434],
  [99803303111553, 98973501939176, 97520099473386, 95507051681748, 93020202130909, 90160512702063,
    87037002365460, 83759970183455, 80435138413056, 77159145834210, 74016579113620, 71078508896615,
    68402330320002, 66032607928246, 64002589216979, 62336065044742, 61049299765016, 60152805237948,
    59652672809942],
  [99640215699508, 98128881467046, 95507051681748, 91928960653282, 87594480722598, 82727860296960,
    77556896744772, 72295060182547, 67128450960105, 62208315397122, 57648797926943, 53528892496613,
    49897232444497, 46778370559283, 44179433140351, 42096358721419, 40519254195419, 39436651541243,
    38838479798342],
  [99434311464145, 97070855096794, 93020202130909, 87594480722598, 81182554079160, 74197641662847,
    67030248929444, 60013305698104, 53402799211033, 47373221689605, 42024428801642, 37395409353752,
    33480736967197, 30246542652260, 27644142989935, 25620588360580, 24126179924809, 23119422724922,
    22569896650430],
  [99191170389278, 95833395008934, 90160512702063, 82727860296960, 74197641662847, 65231170666674,
    56402145875667, 48144561841637, 40737140386335, 34316635589990, 28908054592149, 24460321855037,
    20879196348525, 18053201654678, 15871548634488, 14235004676647, 13061499351803, 12288320559930,
    11872341798111],
  [98917339559263, 94455055836679, 87037002365460, 77556896744772, 67030248929444, 56402145875667,
    46412669028011, 37539300136286, 30007591482072, 23844613577548, 18947391929215, 15145876310918,
    12250224099792, 10080566755669, 8482224156158, 7330948252529, 6532458393676, 6019429999022,
    5747886055124],
  [98620137240582, 92977274084367, 83759970183455, 72295060182547, 60013305698104, 48144561841637,
    37539300136286, 28632747795981, 21514148505805, 16042967052072, 11963140989030, 8988895989578,
    6856195797457, 5345916173887, 4288662136504, 3560088216042, 3072789917071, 2768168828012,
    2609779290877],
  [98307439903894, 91442700494697, 80435138413056, 67128450960105, 53402799211033, 40737140386335,
    30007591482072, 21514148505805, 15143010939829, 10559547845388, 7363400260497, 5182824254883,
    3715861393463, 2737159497245, 2087981385740, 1661055023679, 1386260444117, 1219387114508,
    1134238169645],
  [97987459909839, 89893668732405, 77159145834210, 62208315397122, 47373221689605, 34316635589990,
    23844613577548, 16042967052072, 10559547845388, 6873477647819, 4474121019841, 2944885121419,
    1981357123755, 1376728637957, 997286933210, 759459481799, 612301943785, 525561984968,
    482150420254],
  [97668521415763, 88370877439692, 74016579113620, 57648797926943, 42024428801642, 28908054592149,
    18947391929215, 11963140989030, 7363400260497, 4474121019841, 2718548251081, 1673286214593,
    1056491520045, 692463023978, 476336251819, 347236362596, 270449663304, 226519861296,
    204956096499],
  [97358841391181, 86912331618141, 71078508896615, 53528892496613, 37395409353752, 24460321855037,
    15145876310918, 8988895989578, 5182824254883, 2944885121419, 1673286214593, 964784595173,
    572588089347, 354547598750, 231909438304, 162012475392, 122010837214, 99782714569,
    89076125542],
  [97066321661733, 85552558373835, 68402330320002, 49897232444497, 33480736967197, 20879196348525,
    12250224099792, 6856195797457, 3715861393463, 1981357123755, 1056491520045, 572588089347,
    320465651884, 188023331278, 117254768189, 78677230370, 57392431420, 45887301637, 40444265165],
  [96798356768055, 84322084983195, 66032607928246, 46778370559283, 30246542652260, 18053201654678,
    10080566755669, 5345916173887, 2737159497245, 1376728637957, 692463023978, 354547598750,
    188023331278, 104988676182, 62664409760, 40518336144, 28703723843, 22477880415, 19580722296],
  [96561661243509, 83247146325368, 64002589216979, 44179433140351, 27644142989935, 15871548634488,
    8482224156158, 4288662136504, 2087981385740, 997286933210, 476336251819, 231909438304,
    117254768189, 62664409760, 35978009068, 22512313003, 15539702992, 11947331183, 10299959781],
  [96362118770781, 82349574940229, 62336065044742, 42096358721419, 25620588360580, 14235004676647,
    7330948252529, 3560088216042, 1661055023679, 759459481799, 347236362596, 162012475392,
    78677230370, 40518336144, 22512313003, 13701391808, 9252728803, 7004027707, 5985533651],
  [96204654557880, 81646819803723, 61049299765016, 40519254195419, 24126179924809, 13061499351803,
    6532458393676, 3072789917071, 1386260444117, 612301943785, 270449663304, 122010837214,
    57392431420, 28703723843, 15539702992, 9252728803, 6141162500, 4591895573, 3897042946],
  [96093130435663, 81152034986015, 60152805237948, 39436651541243, 23119422724922, 12288320559930,
    6019429999022, 2768168828012, 1219387114508, 525561984968, 226519861296, 99782714569,
    45887301637, 22477880415, 11947331183, 7004027707, 4591895573, 3403678049, 2874455217],
  [96030246424366, 80874117092434, 59652672809942, 38838479798342, 22569896650430, 11872341798111,
    5747886055124, 2609779290877, 1134238169645, 482150420254, 204956096499, 89076125542,
    40444265165, 19580722296, 10299959781, 5985533651, 3897042946, 2874455217, 2420789662]
]

/-- 19x19 lower-bound table for `eAC(int, int)` -/
private def eAC_ii_lo : List (List ℕ) := [
  [99990465590177, 99950045134049, 99878465019318, 99777627183235, 99650225292531, 99499653393941,
    99329906939310, 99145469151240, 98951185887571, 98752133044089, 98553480620613, 98360357404547,
    98177719895739, 98010228660267, 97862134803305, 97737178724932, 97638502743021, 97568578059954,
    97529136635158],
  [99950045134049, 99738489224229, 99364736368066, 98840139029806, 98180551993681, 97405605742577,
    96537916878916, 95602231461195, 94624548613380, 93631270813996, 92648419492742, 91700944007800,
    90812140531680, 90003186237687, 89292784530362, 88696909578406, 88228633161868, 87898011514236,
    87711965137045],
  [99878465019318, 99364736368066, 98460950722443, 97200600353509, 95629491997550, 93802841619236,
    91782166874033, 89632132527640, 87417601165475, 85201092931806, 83040785150728, 80989105492226,
    79091902969966, 77388127176795, 75909911107341, 74682936220281, 73726956560044, 73056362871881,
    72680594714488],
  [99777627183235, 98840139029806, 97200600353509, 94935021149888, 92144820661204, 88948344893397,
    85472100936966, 81842494096747, 78178869564638, 74588366442386, 71162763538603, 67977210004953,
    65090530682597, 62546688364031, 60376962792072, 58602445558630, 57236523111072, 56287096144877,
    55758235243727],
  [99650225292531, 98180551993681, 95629491997550, 92144820661204, 87918427032911, 83166194098299,
    78108210947820, 72951672191104, 67878262883517, 63036757066679, 58540577980059, 54469385308594,
    50873431784759, 47779422691710, 45196813405181, 43123777473002, 41552377394050, 40472707280554,
    39875802887736],
  [99499653393941, 97405605742577, 93802841619236, 88948344893397, 83166194098299, 76806642884198,
    70208302988016, 63668737113537, 57426428065466, 51654224523301, 46462212625550, 41906892331562,
    38003466791656, 34738647738144, 32082253372685, 29996723539952, 28444329244674, 27392252127203,
    26815760860390],
  [99329906939310, 96537916878916, 91782166874033, 85472100936966, 78108210947820, 70208302988016,
    62244221828984, 54598741884229, 47545930414760, 41252183699061, 35791552401987, 31168166174039,
    27339769217722, 24238481597135, 21786988068104, 19909919626242, 18541103548761, 17627712664191,
    17132228473553],
  [99145469151240, 95602231461195, 89632132527640, 81842494096747, 72951672191104, 63668737113537,
    54598741884229, 46188413658414, 38713197333591, 32295828274624, 26942246979921, 22581865046453,
    19103380186958, 16381988574456, 14297417627546, 12744241673660, 11636680892562, 10910001869228,
    10520102762870],
  [98951185887571, 94624548613380, 87417601165475, 78178869564638, 67878262883517, 57426428065466,
    47545930414760, 38713197333591, 31164524057772, 24943500723403, 19964310290284, 16071476168116,
    13085835589101, 10834353612053, 9166089435819, 7958393768075, 7117310702231, 6575230608290,
    6287728871135],
  [98752133044089, 93631270813996, 85201092931806, 74588366442386, 63036757066679, 51654224523301,
    41252183699061, 32295828274624, 24943500723403, 19133107012798, 14676199143921, 11335079591404,
    8874094681478, 7087044425535, 5807338464064, 4907947464514, 4296609014818, 3909759856730,
    3707016473252],
  [98553480620613, 92648419492742, 83040785150728, 71162763538603, 58540577980059, 46462212625550,
    35791552401987, 26942246979921, 19964310290284, 14676199143921, 10788793511031, 7994538149418,
    6017923416478, 4635827894119, 3679342239931, 3026734918679, 2593795577932, 2324819165737,
    2185522215508],
  [98360357404547, 91700944007800, 80989105492226, 67977210004953, 54469385308594, 41906892331562,
    31168166174039, 22581865046453, 16071476168116, 11335079591404, 7994538149418, 5689699636375,
    4122283891392, 3065940283209, 2358830168828, 1890104482577, 1586435960276, 1401120029173,
    1306258260276],
  [98177719895739, 90812140531680, 79091902969966, 65090530682597, 50873431784759, 38003466791656,
    27339769217722, 19103380186958, 13085835589101, 8874094681478, 6017923416478, 4122283891392,
    2880403114917, 2072167701109, 1547950544186, 1209846587360, 995671534742, 867169917532,
    802112296959],
  [98010228660267, 90003186237687, 77388127176795, 62546688364031, 47779422691710, 34738647738144,
    24238481597135, 16381988574456, 10834353612053, 7087044425535, 4635827894119, 3065940283209,
    2072167701109, 1445830565084, 1051209827577, 803019312504, 649016852091, 558049117915,
    512458744113],
  [97862134803305, 89292784530362, 75909911107341, 60376962792072, 45196813405181, 32082253372685,
    21786988068104, 14297417627546, 9166089435819, 5807338464064, 3679342239931, 2358830168828,
    1547950544186, 1051209827577, 746184907636, 558576955126, 444279008422, 377692108198,
    344619296359],
  [97737178724932, 88696909578406, 74682936220281, 58602445558630, 43123777473002, 29996723539952,
    19909919626242, 12744241673660, 7958393768075, 4907947464514, 3026734918679, 1890104482577,
    1209846587360, 803019312504, 558576955126, 411039984506, 322536171360, 271575959398,
    246456349862],
  [97638502743021, 88228633161868, 73726956560044, 57236523111072, 41552377394050, 28444329244674,
    18541103548761, 11636680892562, 7117310702231, 4296609014818, 2593795577932, 1586435960276,
    995671534742, 649016852091, 444279008422, 322536171360, 250394833688, 209238751237,
    189073454708],
  [97568578059954, 87898011514236, 73056362871881, 56287096144877, 40472707280554, 27392252127203,
    17627712664191, 10910001869228, 6575230608290, 3909759856730, 2324819165737, 1401120029173,
    867169917532, 558049117915, 377692108198, 271575959398, 209238751237, 173908622891,
    156671568257],
  [97529136635158, 87711965137045, 72680594714488, 55758235243727, 39875802887736, 26815760860390,
    17132228473553, 10520102762870, 6287728871135, 3707016473252, 2185522215508, 1306258260276,
    802112296959, 512458744113, 344619296359, 246456349862, 189073454708, 156671568257,
    140901187143]
]

/-- 19x19 upper-bound table for `eAC(int, int)` -/
private def eAC_ii_hi : List (List ℕ) := [
  [99990465590178, 99950045134050, 99878465019319, 99777627183236, 99650225292532, 99499653393942,
    99329906939312, 99145469151241, 98951185887572, 98752133044090, 98553480620614, 98360357404548,
    98177719895740, 98010228660268, 97862134803306, 97737178724933, 97638502743022, 97568578059956,
    97529136635159],
  [99950045134050, 99738489224230, 99364736368067, 98840139029807, 98180551993682, 97405605742578,
    96537916878917, 95602231461196, 94624548613381, 93631270813997, 92648419492743, 91700944007801,
    90812140531681, 90003186237688, 89292784530363, 88696909578407, 88228633161869, 87898011514237,
    87711965137046],
  [99878465019319, 99364736368067, 98460950722444, 97200600353510, 95629491997551, 93802841619237,
    91782166874034, 89632132527641, 87417601165476, 85201092931807, 83040785150729, 80989105492227,
    79091902969967, 77388127176796, 75909911107342, 74682936220282, 73726956560045, 73056362871882,
    72680594714489],
  [99777627183236, 98840139029807, 97200600353510, 94935021149889, 92144820661205, 88948344893398,
    85472100936967, 81842494096748, 78178869564639, 74588366442387, 71162763538604, 67977210004954,
    65090530682599, 62546688364032, 60376962792073, 58602445558631, 57236523111073, 56287096144878,
    55758235243728],
  [99650225292532, 98180551993682, 95629491997551, 92144820661205, 87918427032912, 83166194098301,
    78108210947821, 72951672191106, 67878262883518, 63036757066680, 58540577980060, 54469385308595,
    50873431784760, 47779422691711, 45196813405182, 43123777473004, 41552377394051, 40472707280555,
    39875802887737],
  [99499653393942, 97405605742578, 93802841619237, 88948344893398, 83166194098301, 76806642884199,
    70208302988017, 63668737113538, 57426428065467, 51654224523302, 46462212625551, 41906892331564,
    38003466791657, 34738647738145, 32082253372686, 29996723539953, 28444329244675, 27392252127204,
    26815760860391],
  [99329906939312, 96537916878917, 91782166874034, 85472100936967, 78108210947821, 70208302988017,
    62244221828985, 54598741884230, 47545930414761, 41252183699062, 35791552401988, 31168166174040,
    27339769217723, 24238481597136, 21786988068105, 19909919626243, 18541103548762, 17627712664192,
    17132228473555],
  [99145469151241, 95602231461196, 89632132527641, 81842494096748, 72951672191106, 63668737113538,
    54598741884230, 46188413658415, 38713197333592, 32295828274625, 26942246979922, 22581865046454,
    19103380186959, 16381988574457, 14297417627547, 12744241673661, 11636680892563, 10910001869229,
    10520102762871],
  [98951185887572, 94624548613381, 87417601165476, 78178869564639, 67878262883518, 57426428065467,
    47545930414761, 38713197333592, 31164524057773, 24943500723404, 19964310290285, 16071476168117,
    13085835589102, 10834353612054, 9166089435820, 7958393768076, 7117310702232, 6575230608291,
    6287728871136],
  [98752133044090, 93631270813997, 85201092931807, 74588366442387, 63036757066680, 51654224523302,
    41252183699062, 32295828274625, 24943500723404, 19133107012799, 14676199143922, 11335079591405,
    8874094681479, 7087044425536, 5807338464065, 4907947464515, 4296609014819, 3909759856731,
    3707016473253],
  [98553480620614, 92648419492743, 83040785150729, 71162763538604, 58540577980060, 46462212625551,
    35791552401988, 26942246979922, 19964310290285, 14676199143922, 10788793511032, 7994538149419,
    6017923416479, 4635827894120, 3679342239932, 3026734918680, 2593795577933, 2324819165738,
    2185522215509],
  [98360357404548, 91700944007801, 80989105492227, 67977210004954, 54469385308595, 41906892331564,
    31168166174040, 22581865046454, 16071476168117, 11335079591405, 7994538149419, 5689699636376,
    4122283891393, 3065940283210, 2358830168829, 1890104482578, 1586435960277, 1401120029174,
    1306258260277],
  [98177719895740, 90812140531681, 79091902969967, 65090530682599, 50873431784760, 38003466791657,
    27339769217723, 19103380186959, 13085835589102, 8874094681479, 6017923416479, 4122283891393,
    2880403114918, 2072167701110, 1547950544187, 1209846587361, 995671534743, 867169917533,
    802112296960],
  [98010228660268, 90003186237688, 77388127176796, 62546688364032, 47779422691711, 34738647738145,
    24238481597136, 16381988574457, 10834353612054, 7087044425536, 4635827894120, 3065940283210,
    2072167701110, 1445830565085, 1051209827578, 803019312505, 649016852092, 558049117916,
    512458744114],
  [97862134803306, 89292784530363, 75909911107342, 60376962792073, 45196813405182, 32082253372686,
    21786988068105, 14297417627547, 9166089435820, 5807338464065, 3679342239932, 2358830168829,
    1547950544187, 1051209827578, 746184907637, 558576955127, 444279008423, 377692108199,
    344619296360],
  [97737178724933, 88696909578407, 74682936220282, 58602445558631, 43123777473004, 29996723539953,
    19909919626243, 12744241673661, 7958393768076, 4907947464515, 3026734918680, 1890104482578,
    1209846587361, 803019312505, 558576955127, 411039984507, 322536171361, 271575959399,
    246456349863],
  [97638502743022, 88228633161869, 73726956560045, 57236523111073, 41552377394051, 28444329244675,
    18541103548762, 11636680892563, 7117310702232, 4296609014819, 2593795577933, 1586435960277,
    995671534743, 649016852092, 444279008423, 322536171361, 250394833689, 209238751238,
    189073454709],
  [97568578059956, 87898011514237, 73056362871882, 56287096144878, 40472707280555, 27392252127204,
    17627712664192, 10910001869229, 6575230608291, 3909759856731, 2324819165738, 1401120029174,
    867169917533, 558049117916, 377692108199, 271575959399, 209238751238, 173908622892,
    156671568258],
  [97529136635159, 87711965137046, 72680594714489, 55758235243728, 39875802887737, 26815760860391,
    17132228473555, 10520102762871, 6287728871136, 3707016473253, 2185522215509, 1306258260277,
    802112296960, 512458744114, 344619296360, 246456349863, 189073454709, 156671568258,
    140901187144]
]

/-- Transpose of `eAB_ei_lo` for fast kernel checks -/
private def eAB_ie_lo : List (List ℕ) := [
  [99978170603266, 99885656230944, 99721941955645, 99491567564320, 99200933906735, 98858061353892,
    98472327368873, 98054171228998, 97614777162135, 97165748609970, 96718785591799, 96285375569457,
    95876506173857, 95502405910412, 95172316742624, 94894300432368, 94675078701688, 94519904650844,
    94432441061563],
  [99885656230944, 99402233717423, 98551404942600, 97364130979277, 95882838892964, 94158799398244,
    92249316000911, 90214854890034, 88116339997523, 86012797501725, 83959471470111, 82006464934080,
    80197899071681, 78571534273521, 77158763961207, 75984875124571, 75069465913567, 74426912327786,
    74066704001698],
  [99721941955645, 98551404942600, 96510991792903, 93705664856997, 90273766228772, 86374101792505,
    82172873323329, 77831821503883, 73498789600790, 69301358764664, 65343638347168, 61705845165001,
    58446031304411, 55603221648151, 53201262418339, 51252806689520, 49763019086307, 48732723084221,
    48160697961185],
  [99491567564320, 97364130979277, 93705664856997, 88779729555785, 82918192961206, 76478972937980,
    69807117589280, 63204718972345, 56912675482138, 51104326493058, 45888761408322, 41320525251474,
    37412405446606, 34148630479478, 31496733021316, 29417212683308, 27870803651996, 26823555656908,
    26249985302731],
  [99200933906735, 95882838892964, 90273766228772, 82918192961206, 74466499185691, 65569809806003,
    56794967421404, 48572971993817, 41182939801381, 34764361376206, 29346152259263, 24881343930309,
    21279364647367, 18431665814970, 16229590958502, 14575339605638, 13387730150005, 12604558186315,
    12182958106338],
  [98858061353892, 94158799398244, 86374101792505, 76478972937980, 65569809806003, 54651236030331,
    44491690078201, 35567553988592, 28082989124065, 22034563479395, 17288828677836, 13650699395388,
    10912644290970, 8884007444187, 7404657557555, 6348437604166, 5621152378450, 5156416509454,
    4911303955166],
  [98472327368873, 92249316000911, 82172873323329, 69807117589280, 56794967421404, 44491690078201,
    33771696612823, 25016847024146, 18226076402342, 13167305206111, 9512630286604, 6930446759479,
    5133823401843, 3896860876405, 3052698755938, 2483671183946, 2109916805618, 1879449451843,
    1760676639046],
  [98054171228998, 90214854890034, 77831821503883, 63204718972345, 48572971993817, 35567553988592,
    25016847024146, 17056437525480, 11384906288692, 7518008849751, 4964507887173, 3313731661755,
    2259295786171, 1589101603193, 1163619493411, 894244258718, 726187001316, 626509427231,
    576420731076],
  [97614777162135, 88116339997523, 73498789600790, 56912675482138, 41182939801381, 28082989124065,
    18226076402342, 11384906288692, 6928592605998, 4161270744050, 2499233998878, 1520976437240,
    950076902073, 616607232541, 420469599518, 304258656944, 235598086707, 196514905246,
    177392959434],
  [97165748609970, 86012797501725, 69301358764664, 51104326493058, 34764361376206, 22034563479395,
    13167305206111, 7518008849751, 4161270744050, 2267353682326, 1235414140767, 683810410908,
    390428613925, 233310395532, 147878244191, 100596037039, 74181701663, 59768928230, 52908486728],
  [96718785591799, 83959471470111, 65343638347168, 45888761408322, 29346152259263, 17288828677836,
    9512630286604, 4964507887173, 2499233998878, 1235414140767, 610686354256, 307431901387,
    160444383227, 88279439148, 52008457044, 33259736204, 23357256158, 18178390984, 15780265331],
  [96285375569457, 82006464934080, 61705845165001, 41320525251474, 24881343930309, 13650699395388,
    6930446759479, 3313731661755, 1520976437240, 683810410908, 307431901387, 141108793890,
    67469918505, 34254411772, 18793063565, 11316329480, 7577834430, 5701948967, 4856362404],
  [95876506173857, 80197899071681, 58446031304411, 37412405446606, 21279364647367, 10912644290970,
    5133823401843, 2259295786171, 950076902073, 390428613925, 160444383227, 67469918505,
    29692198317, 13968612786, 7163489375, 4074437362, 2608124096, 1900729374, 1589904645],
  [95502405910412, 78571534273521, 55603221648151, 34148630479478, 18431665814970, 8884007444187,
    3896860876405, 1589101603193, 616607232541, 233310395532, 88279439148, 34254411772,
    13968612786, 6127160631, 2953272981, 1594024120, 978967388, 692792130, 569972454],
  [95172316742624, 77158763961207, 53201262418339, 31496733021316, 16229590958502, 7404657557555,
    3052698755938, 1163619493411, 420469599518, 147878244191, 52008457044, 18793063565, 7163489375,
    2953272981, 1347413817, 694293439, 411042409, 283415311, 229772436],
  [94894300432368, 75984875124571, 51252806689520, 29417212683308, 14575339605638, 6348437604166,
    2483671183946, 894244258718, 304258656944, 100596037039, 33259736204, 11316329480, 4074437362,
    1594024120, 694293439, 344001410, 197444068, 133178644, 106640363],
  [94675078701688, 75069465913567, 49763019086307, 27870803651996, 13387730150005, 5621152378450,
    2109916805618, 726187001316, 235598086707, 74181701663, 23357256158, 7577834430, 2608124096,
    978967388, 411042409, 197444068, 110582616, 73304436, 58124323],
  [94519904650844, 74426912327786, 48732723084221, 26823555656908, 12604558186315, 5156416509454,
    1879449451843, 626509427231, 196514905246, 59768928230, 18178390984, 5701948967, 1900729374,
    692792130, 283415311, 133178644, 73304436, 47997756, 37794417],
  [94432441061563, 74066704001698, 48160697961185, 26249985302731, 12182958106338, 4911303955166,
    1760676639046, 576420731076, 177392959434, 52908486728, 15780265331, 4856362404, 1589904645,
    569972454, 229772436, 106640363, 58124323, 37794417, 29643498]
]

/-- Transpose of `eAB_ei_hi` for fast kernel checks -/
private def eAB_ie_hi : List (List ℕ) := [
  [99978170603267, 99885656230945, 99721941955646, 99491567564321, 99200933906736, 98858061353894,
    98472327368874, 98054171228999, 97614777162136, 97165748609971, 96718785591800, 96285375569458,
    95876506173859, 95502405910413, 95172316742625, 94894300432369, 94675078701689, 94519904650845,
    94432441061564],
  [99885656230945, 99402233717424, 98551404942601, 97364130979278, 95882838892965, 94158799398245,
    92249316000913, 90214854890036, 88116339997524, 86012797501726, 83959471470112, 82006464934081,
    80197899071682, 78571534273522, 77158763961209, 75984875124572, 75069465913568, 74426912327787,
    74066704001699],
  [99721941955646, 98551404942601, 96510991792905, 93705664856998, 90273766228773, 86374101792506,
    82172873323330, 77831821503884, 73498789600791, 69301358764665, 65343638347169, 61705845165002,
    58446031304412, 55603221648152, 53201262418340, 51252806689521, 49763019086308, 48732723084222,
    48160697961186],
  [99491567564321, 97364130979278, 93705664856998, 88779729555786, 82918192961207, 76478972937981,
    69807117589281, 63204718972346, 56912675482139, 51104326493059, 45888761408323, 41320525251475,
    37412405446607, 34148630479479, 31496733021317, 29417212683309, 27870803651997, 26823555656909,
    26249985302732],
  [99200933906736, 95882838892965, 90273766228773, 82918192961207, 74466499185692, 65569809806004,
    56794967421405, 48572971993818, 41182939801382, 34764361376207, 29346152259265, 24881343930310,
    21279364647369, 18431665814971, 16229590958503, 14575339605639, 13387730150006, 12604558186316,
    12182958106339],
  [98858061353894, 94158799398245, 86374101792506, 76478972937981, 65569809806004, 54651236030332,
    44491690078202, 35567553988593, 28082989124066, 22034563479396, 17288828677837, 13650699395389,
    10912644290971, 8884007444188, 7404657557556, 6348437604167, 5621152378451, 5156416509455,
    4911303955167],
  [98472327368874, 92249316000913, 82172873323330, 69807117589281, 56794967421405, 44491690078202,
    33771696612824, 25016847024147, 18226076402343, 13167305206112, 9512630286605, 6930446759480,
    5133823401844, 3896860876406, 3052698755939, 2483671183947, 2109916805619, 1879449451844,
    1760676639047],
  [98054171228999, 90214854890036, 77831821503884, 63204718972346, 48572971993818, 35567553988593,
    25016847024147, 17056437525481, 11384906288693, 7518008849752, 4964507887174, 3313731661756,
    2259295786172, 1589101603194, 1163619493412, 894244258719, 726187001317, 626509427232,
    576420731077],
  [97614777162136, 88116339997524, 73498789600791, 56912675482139, 41182939801382, 28082989124066,
    18226076402343, 11384906288693, 6928592605999, 4161270744051, 2499233998879, 1520976437241,
    950076902074, 616607232542, 420469599519, 304258656945, 235598086708, 196514905247,
    177392959435],
  [97165748609971, 86012797501726, 69301358764665, 51104326493059, 34764361376207, 22034563479396,
    13167305206112, 7518008849752, 4161270744051, 2267353682327, 1235414140768, 683810410909,
    390428613926, 233310395533, 147878244192, 100596037040, 74181701664, 59768928231, 52908486729],
  [96718785591800, 83959471470112, 65343638347169, 45888761408323, 29346152259265, 17288828677837,
    9512630286605, 4964507887174, 2499233998879, 1235414140768, 610686354257, 307431901388,
    160444383228, 88279439149, 52008457045, 33259736205, 23357256159, 18178390985, 15780265332],
  [96285375569458, 82006464934081, 61705845165002, 41320525251475, 24881343930310, 13650699395389,
    6930446759480, 3313731661756, 1520976437241, 683810410909, 307431901388, 141108793891,
    67469918506, 34254411773, 18793063566, 11316329481, 7577834431, 5701948968, 4856362405],
  [95876506173859, 80197899071682, 58446031304412, 37412405446607, 21279364647369, 10912644290971,
    5133823401844, 2259295786172, 950076902074, 390428613926, 160444383228, 67469918506,
    29692198318, 13968612787, 7163489376, 4074437363, 2608124097, 1900729375, 1589904646],
  [95502405910413, 78571534273522, 55603221648152, 34148630479479, 18431665814971, 8884007444188,
    3896860876406, 1589101603194, 616607232542, 233310395533, 88279439149, 34254411773,
    13968612787, 6127160632, 2953272982, 1594024121, 978967389, 692792131, 569972455],
  [95172316742625, 77158763961209, 53201262418340, 31496733021317, 16229590958503, 7404657557556,
    3052698755939, 1163619493412, 420469599519, 147878244192, 52008457045, 18793063566, 7163489376,
    2953272982, 1347413818, 694293440, 411042410, 283415312, 229772437],
  [94894300432369, 75984875124572, 51252806689521, 29417212683309, 14575339605639, 6348437604167,
    2483671183947, 894244258719, 304258656945, 100596037040, 33259736205, 11316329481, 4074437363,
    1594024121, 694293440, 344001411, 197444069, 133178645, 106640364],
  [94675078701689, 75069465913568, 49763019086308, 27870803651997, 13387730150006, 5621152378451,
    2109916805619, 726187001317, 235598086708, 74181701664, 23357256159, 7577834431, 2608124097,
    978967389, 411042410, 197444069, 110582617, 73304437, 58124324],
  [94519904650845, 74426912327787, 48732723084222, 26823555656909, 12604558186316, 5156416509455,
    1879449451844, 626509427232, 196514905247, 59768928231, 18178390985, 5701948968, 1900729375,
    692792131, 283415312, 133178645, 73304437, 47997757, 37794418],
  [94432441061564, 74066704001699, 48160697961186, 26249985302732, 12182958106339, 4911303955167,
    1760676639047, 576420731077, 177392959435, 52908486729, 15780265332, 4856362405, 1589904646,
    569972455, 229772437, 106640364, 58124324, 37794418, 29643499]
]

/-- Transpose of `eAC_ei_lo` for fast kernel checks -/
private def eAC_ie_lo : List (List ℕ) := [
  [99984563792038, 99919133199752, 99803303111552, 99640215699507, 99434311464144, 99191170389277,
    98917339559261, 98620137240581, 98307439903893, 97987459909838, 97668521415761, 97358841391180,
    97066321661732, 96798356768054, 96561661243508, 96362118770780, 96204654557878, 96093130435662,
    96030246424365],
  [99919133199752, 99576944429846, 98973501939175, 98128881467044, 97070855096793, 95833395008932,
    94455055836678, 92977274084366, 91442700494696, 89893668732404, 88370877439691, 86912331618140,
    85552558373834, 84322084983194, 83247146325366, 82349574940228, 81646819803722, 81152034986013,
    80874117092433],
  [99803303111552, 98973501939175, 97520099473385, 95507051681747, 93020202130908, 90160512702061,
    87037002365459, 83759970183454, 80435138413055, 77159145834209, 74016579113619, 71078508896614,
    68402330320001, 66032607928245, 64002589216978, 62336065044741, 61049299765015, 60152805237947,
    59652672809941],
  [99640215699507, 98128881467044, 95507051681747, 91928960653281, 87594480722597, 82727860296959,
    77556896744771, 72295060182546, 67128450960104, 62208315397121, 57648797926942, 53528892496612,
    49897232444496, 46778370559282, 44179433140350, 42096358721418, 40519254195418, 39436651541242,
    38838479798341],
  [99434311464144, 97070855096793, 93020202130908, 87594480722597, 81182554079159, 74197641662846,
    67030248929443, 60013305698103, 53402799211032, 47373221689604, 42024428801641, 37395409353751,
    33480736967196, 30246542652259, 27644142989934, 25620588360579, 24126179924808, 23119422724921,
    22569896650429],
  [99191170389277, 95833395008932, 90160512702061, 82727860296959, 74197641662846, 65231170666673,
    56402145875666, 48144561841636, 40737140386334, 34316635589989, 28908054592148, 24460321855036,
    20879196348524, 18053201654677, 15871548634487, 14235004676646, 13061499351802, 12288320559929,
    11872341798110],
  [98917339559261, 94455055836678, 87037002365459, 77556896744771, 67030248929443, 56402145875666,
    46412669028010, 37539300136285, 30007591482071, 23844613577547, 18947391929214, 15145876310917,
    12250224099791, 10080566755668, 8482224156157, 7330948252528, 6532458393675, 6019429999021,
    5747886055123],
  [98620137240581, 92977274084366, 83759970183454, 72295060182546, 60013305698103, 48144561841636,
    37539300136285, 28632747795980, 21514148505804, 16042967052071, 11963140989029, 8988895989577,
    6856195797456, 5345916173886, 4288662136503, 3560088216041, 3072789917070, 2768168828011,
    2609779290876],
  [98307439903893, 91442700494696, 80435138413055, 67128450960104, 53402799211032, 40737140386334,
    30007591482071, 21514148505804, 15143010939828, 10559547845387, 7363400260496, 5182824254882,
    3715861393462, 2737159497244, 2087981385739, 1661055023678, 1386260444116, 1219387114507,
    1134238169644],
  [97987459909838, 89893668732404, 77159145834209, 62208315397121, 47373221689604, 34316635589989,
    23844613577547, 16042967052071, 10559547845387, 6873477647818, 4474121019840, 2944885121418,
    1981357123754, 1376728637956, 997286933209, 759459481798, 612301943784, 525561984967,
    482150420253],
  [97668521415761, 88370877439691, 74016579113619, 57648797926942, 42024428801641, 28908054592148,
    18947391929214, 11963140989029, 7363400260496, 4474121019840, 2718548251080, 1673286214592,
    1056491520044, 692463023977, 476336251818, 347236362595, 270449663303, 226519861295,
    204956096498],
  [97358841391180, 86912331618140, 71078508896614, 53528892496612, 37395409353751, 24460321855036,
    15145876310917, 8988895989577, 5182824254882, 2944885121418, 1673286214592, 964784595172,
    572588089346, 354547598749, 231909438303, 162012475391, 122010837213, 99782714568,
    89076125541],
  [97066321661732, 85552558373834, 68402330320001, 49897232444496, 33480736967196, 20879196348524,
    12250224099791, 6856195797456, 3715861393462, 1981357123754, 1056491520044, 572588089346,
    320465651883, 188023331277, 117254768188, 78677230369, 57392431419, 45887301636, 40444265164],
  [96798356768054, 84322084983194, 66032607928245, 46778370559282, 30246542652259, 18053201654677,
    10080566755668, 5345916173886, 2737159497244, 1376728637956, 692463023977, 354547598749,
    188023331277, 104988676181, 62664409759, 40518336143, 28703723842, 22477880414, 19580722295],
  [96561661243508, 83247146325366, 64002589216978, 44179433140350, 27644142989934, 15871548634487,
    8482224156157, 4288662136503, 2087981385739, 997286933209, 476336251818, 231909438303,
    117254768188, 62664409759, 35978009067, 22512313002, 15539702991, 11947331182, 10299959780],
  [96362118770780, 82349574940228, 62336065044741, 42096358721418, 25620588360579, 14235004676646,
    7330948252528, 3560088216041, 1661055023678, 759459481798, 347236362595, 162012475391,
    78677230369, 40518336143, 22512313002, 13701391807, 9252728802, 7004027706, 5985533650],
  [96204654557878, 81646819803722, 61049299765015, 40519254195418, 24126179924808, 13061499351802,
    6532458393675, 3072789917070, 1386260444116, 612301943784, 270449663303, 122010837213,
    57392431419, 28703723842, 15539702991, 9252728802, 6141162499, 4591895572, 3897042945],
  [96093130435662, 81152034986013, 60152805237947, 39436651541242, 23119422724921, 12288320559929,
    6019429999021, 2768168828011, 1219387114507, 525561984967, 226519861295, 99782714568,
    45887301636, 22477880414, 11947331182, 7004027706, 4591895572, 3403678048, 2874455216],
  [96030246424365, 80874117092433, 59652672809941, 38838479798341, 22569896650429, 11872341798110,
    5747886055123, 2609779290876, 1134238169644, 482150420253, 204956096498, 89076125541,
    40444265164, 19580722295, 10299959780, 5985533650, 3897042945, 2874455216, 2420789661]
]

/-- Transpose of `eAC_ei_hi` for fast kernel checks -/
private def eAC_ie_hi : List (List ℕ) := [
  [99984563792039, 99919133199753, 99803303111553, 99640215699508, 99434311464145, 99191170389278,
    98917339559263, 98620137240582, 98307439903894, 97987459909839, 97668521415763, 97358841391181,
    97066321661733, 96798356768055, 96561661243509, 96362118770781, 96204654557880, 96093130435663,
    96030246424366],
  [99919133199753, 99576944429847, 98973501939176, 98128881467046, 97070855096794, 95833395008934,
    94455055836679, 92977274084367, 91442700494697, 89893668732405, 88370877439692, 86912331618141,
    85552558373835, 84322084983195, 83247146325368, 82349574940229, 81646819803723, 81152034986015,
    80874117092434],
  [99803303111553, 98973501939176, 97520099473386, 95507051681748, 93020202130909, 90160512702063,
    87037002365460, 83759970183455, 80435138413056, 77159145834210, 74016579113620, 71078508896615,
    68402330320002, 66032607928246, 64002589216979, 62336065044742, 61049299765016, 60152805237948,
    59652672809942],
  [99640215699508, 98128881467046, 95507051681748, 91928960653282, 87594480722598, 82727860296960,
    77556896744772, 72295060182547, 67128450960105, 62208315397122, 57648797926943, 53528892496613,
    49897232444497, 46778370559283, 44179433140351, 42096358721419, 40519254195419, 39436651541243,
    38838479798342],
  [99434311464145, 97070855096794, 93020202130909, 87594480722598, 81182554079160, 74197641662847,
    67030248929444, 60013305698104, 53402799211033, 47373221689605, 42024428801642, 37395409353752,
    33480736967197, 30246542652260, 27644142989935, 25620588360580, 24126179924809, 23119422724922,
    22569896650430],
  [99191170389278, 95833395008934, 90160512702063, 82727860296960, 74197641662847, 65231170666674,
    56402145875667, 48144561841637, 40737140386335, 34316635589990, 28908054592149, 24460321855037,
    20879196348525, 18053201654678, 15871548634488, 14235004676647, 13061499351803, 12288320559930,
    11872341798111],
  [98917339559263, 94455055836679, 87037002365460, 77556896744772, 67030248929444, 56402145875667,
    46412669028011, 37539300136286, 30007591482072, 23844613577548, 18947391929215, 15145876310918,
    12250224099792, 10080566755669, 8482224156158, 7330948252529, 6532458393676, 6019429999022,
    5747886055124],
  [98620137240582, 92977274084367, 83759970183455, 72295060182547, 60013305698104, 48144561841637,
    37539300136286, 28632747795981, 21514148505805, 16042967052072, 11963140989030, 8988895989578,
    6856195797457, 5345916173887, 4288662136504, 3560088216042, 3072789917071, 2768168828012,
    2609779290877],
  [98307439903894, 91442700494697, 80435138413056, 67128450960105, 53402799211033, 40737140386335,
    30007591482072, 21514148505805, 15143010939829, 10559547845388, 7363400260497, 5182824254883,
    3715861393463, 2737159497245, 2087981385740, 1661055023679, 1386260444117, 1219387114508,
    1134238169645],
  [97987459909839, 89893668732405, 77159145834210, 62208315397122, 47373221689605, 34316635589990,
    23844613577548, 16042967052072, 10559547845388, 6873477647819, 4474121019841, 2944885121419,
    1981357123755, 1376728637957, 997286933210, 759459481799, 612301943785, 525561984968,
    482150420254],
  [97668521415763, 88370877439692, 74016579113620, 57648797926943, 42024428801642, 28908054592149,
    18947391929215, 11963140989030, 7363400260497, 4474121019841, 2718548251081, 1673286214593,
    1056491520045, 692463023978, 476336251819, 347236362596, 270449663304, 226519861296,
    204956096499],
  [97358841391181, 86912331618141, 71078508896615, 53528892496613, 37395409353752, 24460321855037,
    15145876310918, 8988895989578, 5182824254883, 2944885121419, 1673286214593, 964784595173,
    572588089347, 354547598750, 231909438304, 162012475392, 122010837214, 99782714569,
    89076125542],
  [97066321661733, 85552558373835, 68402330320002, 49897232444497, 33480736967197, 20879196348525,
    12250224099792, 6856195797457, 3715861393463, 1981357123755, 1056491520045, 572588089347,
    320465651884, 188023331278, 117254768189, 78677230370, 57392431420, 45887301637, 40444265165],
  [96798356768055, 84322084983195, 66032607928246, 46778370559283, 30246542652260, 18053201654678,
    10080566755669, 5345916173887, 2737159497245, 1376728637957, 692463023978, 354547598750,
    188023331278, 104988676182, 62664409760, 40518336144, 28703723843, 22477880415, 19580722296],
  [96561661243509, 83247146325368, 64002589216979, 44179433140351, 27644142989935, 15871548634488,
    8482224156158, 4288662136504, 2087981385740, 997286933210, 476336251819, 231909438304,
    117254768189, 62664409760, 35978009068, 22512313003, 15539702992, 11947331183, 10299959781],
  [96362118770781, 82349574940229, 62336065044742, 42096358721419, 25620588360580, 14235004676647,
    7330948252529, 3560088216042, 1661055023679, 759459481799, 347236362596, 162012475392,
    78677230370, 40518336144, 22512313003, 13701391808, 9252728803, 7004027707, 5985533651],
  [96204654557880, 81646819803723, 61049299765016, 40519254195419, 24126179924809, 13061499351803,
    6532458393676, 3072789917071, 1386260444117, 612301943785, 270449663304, 122010837214,
    57392431420, 28703723843, 15539702992, 9252728803, 6141162500, 4591895573, 3897042946],
  [96093130435663, 81152034986015, 60152805237948, 39436651541243, 23119422724922, 12288320559930,
    6019429999022, 2768168828012, 1219387114508, 525561984968, 226519861296, 99782714569,
    45887301637, 22477880415, 11947331183, 7004027707, 4591895573, 3403678049, 2874455217],
  [96030246424366, 80874117092434, 59652672809942, 38838479798342, 22569896650430, 11872341798111,
    5747886055124, 2609779290877, 1134238169645, 482150420254, 204956096499, 89076125542,
    40444265165, 19580722296, 10299959781, 5985533651, 3897042946, 2874455217, 2420789662]
]

private theorem eAB_ee_hi_shape : checkShape eAB_ee_hi 19 = true := rfl
private theorem eAB_ei_lo_shape : checkShape eAB_ei_lo 19 = true := rfl
private theorem eAB_ei_hi_shape : checkShape eAB_ei_hi 19 = true := rfl
private theorem eAB_ii_lo_shape : checkShape eAB_ii_lo 19 = true := rfl
private theorem eAB_ii_hi_shape : checkShape eAB_ii_hi 19 = true := rfl
private theorem eAC_ee_lo_shape : checkShape eAC_ee_lo 19 = true := rfl
private theorem eAC_ei_lo_shape : checkShape eAC_ei_lo 19 = true := rfl
private theorem eAC_ei_hi_shape : checkShape eAC_ei_hi 19 = true := rfl
private theorem eAC_ii_lo_shape : checkShape eAC_ii_lo 19 = true := rfl
private theorem eAC_ii_hi_shape : checkShape eAC_ii_hi 19 = true := rfl
private theorem eAB_ie_lo_shape : checkShape eAB_ie_lo 19 = true := rfl
private theorem eAB_ie_hi_shape : checkShape eAB_ie_hi 19 = true := rfl
private theorem eAC_ie_lo_shape : checkShape eAC_ie_lo 19 = true := rfl
private theorem eAC_ie_hi_shape : checkShape eAC_ie_hi 19 = true := rfl
private theorem eAB_ie_lo_tr : eAB_ie_lo = transposeMat eAB_ei_lo 19 := rfl
private theorem eAB_ie_hi_tr : eAB_ie_hi = transposeMat eAB_ei_hi 19 := rfl
private theorem eAC_ie_lo_tr : eAC_ie_lo = transposeMat eAC_ei_lo 19 := rfl
private theorem eAC_ie_hi_tr : eAC_ie_hi = transposeMat eAC_ei_hi 19 := rfl
private theorem eAC_ee_lo_tr : eAC_ee_lo = transposeMat eAC_ee_lo 19 := rfl
private theorem eAC_ii_lo_tr : eAC_ii_lo = transposeMat eAC_ii_lo 19 := rfl
private theorem eAC_ii_hi_tr : eAC_ii_hi = transposeMat eAC_ii_hi 19 := rfl

private theorem eAB_ee_hi_chk :
    ∀ a : Fin 19, checkExpPairRowUp certS certRatio certM cABLo denAB19 (vecAt xeLo19 a.1)
    (eAB_ee_hi.getD a.1 []) xeLo19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAB_ee_hi_ge (a b : Fin 19) :
    eABFactor (shiftNode (17 / 10) r19 a) (shiftNode (17 / 10) r19 b) ≤
      (matAt eAB_ee_hi a.1 b.1 : ℝ) / certS := by
  have heq : Real.exp (-(6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a *
      shiftNode (17 / 10) r19 b)) = eABFactor (shiftNode (17 / 10) r19 a)
      (shiftNode (17 / 10) r19 b) := by unfold eABFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowUp_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAB_ee_hi_shape a) (rfl : xeLo19.length = 19) (eAB_ee_hi_chk a) b ?_
  have hm1 : 6 * ((s2Lo : ℝ) / certT) * ((vecAt xeLo19 a.1 : ℝ) / certT) *
      ((vecAt xeLo19 b.1 : ℝ) / certT) ≤
      6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a * shiftNode (17 / 10) r19 b := by
    have h1 := s2_lo_le; have h2 := (xe_bounds a).1; have h3 := (xe_bounds b).1
    have h01 : (6 : ℝ) * ((s2Lo : ℝ) / certT) ≤ 6 * Real.sqrt 2 := by linarith
    have h02 : (6 : ℝ) * ((s2Lo : ℝ) / certT) * ((vecAt xeLo19 a.1 : ℝ) / certT) ≤
        6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a :=
      mul_le_mul h01 h2 (by positivity) (by positivity)
    exact mul_le_mul h02 h3 (by positivity) (mul_nonneg (by positivity)
      ((by positivity : (0 : ℝ) ≤ _).trans h2))
  refine le_trans ?_ hm1
  refine le_of_eq ?_
  unfold cABLo s2Lo denAB19 certT certS certRatio; push_cast; ring
private theorem eAB_ei_lo_chk :
    ∀ a : Fin 19, checkExpPairRowDn certS certRatio certM cABHi denAB19 (vecAt xeHi19 a.1)
    (eAB_ei_lo.getD a.1 []) xiHi19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAB_ei_lo_le (a b : Fin 19) :
    (matAt eAB_ei_lo a.1 b.1 : ℝ) / certS ≤
      eABFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 b) := by
  have heq : Real.exp (-(6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a *
      shiftNode (21 / 20) r19 b)) = eABFactor (shiftNode (17 / 10) r19 a)
      (shiftNode (21 / 20) r19 b) := by unfold eABFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowDn_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAB_ei_lo_shape a) (rfl : xiHi19.length = 19) (eAB_ei_lo_chk a) b ?_
  have ha0 : 0 ≤ shiftNode (17 / 10) r19 a := (by positivity : (0 : ℝ) ≤ _).trans (xe_bounds a).1
  have hb0 : 0 ≤ shiftNode (21 / 20) r19 b := (by positivity : (0 : ℝ) ≤ _).trans (xi_bounds b).1
  have hm1 : 6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a * shiftNode (21 / 20) r19 b ≤
      6 * ((s2Hi : ℝ) / certT) * ((vecAt xeHi19 a.1 : ℝ) / certT) *
        ((vecAt xiHi19 b.1 : ℝ) / certT) := by
    have h1 := le_s2_hi; have h2 := (xe_bounds a).2; have h3 := (xi_bounds b).2
    gcongr
  refine hm1.trans_eq ?_
  unfold cABHi s2Hi denAB19 certT certS certRatio; push_cast; ring
private theorem eAB_ei_hi_chk :
    ∀ a : Fin 19, checkExpPairRowUp certS certRatio certM cABLo denAB19 (vecAt xeLo19 a.1)
    (eAB_ei_hi.getD a.1 []) xiLo19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAB_ei_hi_ge (a b : Fin 19) :
    eABFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 b) ≤
      (matAt eAB_ei_hi a.1 b.1 : ℝ) / certS := by
  have heq : Real.exp (-(6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a *
      shiftNode (21 / 20) r19 b)) = eABFactor (shiftNode (17 / 10) r19 a)
      (shiftNode (21 / 20) r19 b) := by unfold eABFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowUp_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAB_ei_hi_shape a) (rfl : xiLo19.length = 19) (eAB_ei_hi_chk a) b ?_
  have hm1 : 6 * ((s2Lo : ℝ) / certT) * ((vecAt xeLo19 a.1 : ℝ) / certT) *
      ((vecAt xiLo19 b.1 : ℝ) / certT) ≤
      6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a * shiftNode (21 / 20) r19 b := by
    have h1 := s2_lo_le; have h2 := (xe_bounds a).1; have h3 := (xi_bounds b).1
    have h01 : (6 : ℝ) * ((s2Lo : ℝ) / certT) ≤ 6 * Real.sqrt 2 := by linarith
    have h02 : (6 : ℝ) * ((s2Lo : ℝ) / certT) * ((vecAt xeLo19 a.1 : ℝ) / certT) ≤
        6 * Real.sqrt 2 * shiftNode (17 / 10) r19 a :=
      mul_le_mul h01 h2 (by positivity) (by positivity)
    exact mul_le_mul h02 h3 (by positivity) (mul_nonneg (by positivity)
      ((by positivity : (0 : ℝ) ≤ _).trans h2))
  refine le_trans ?_ hm1
  refine le_of_eq ?_
  unfold cABLo s2Lo denAB19 certT certS certRatio; push_cast; ring
private theorem eAB_ii_lo_chk :
    ∀ a : Fin 19, checkExpPairRowDn certS certRatio certM cABHi denAB19 (vecAt xiHi19 a.1)
    (eAB_ii_lo.getD a.1 []) xiHi19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAB_ii_lo_le (a b : Fin 19) :
    (matAt eAB_ii_lo a.1 b.1 : ℝ) / certS ≤
      eABFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 b) := by
  have heq : Real.exp (-(6 * Real.sqrt 2 * shiftNode (21 / 20) r19 a *
      shiftNode (21 / 20) r19 b)) = eABFactor (shiftNode (21 / 20) r19 a)
      (shiftNode (21 / 20) r19 b) := by unfold eABFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowDn_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAB_ii_lo_shape a) (rfl : xiHi19.length = 19) (eAB_ii_lo_chk a) b ?_
  have ha0 : 0 ≤ shiftNode (21 / 20) r19 a := (by positivity : (0 : ℝ) ≤ _).trans (xi_bounds a).1
  have hb0 : 0 ≤ shiftNode (21 / 20) r19 b := (by positivity : (0 : ℝ) ≤ _).trans (xi_bounds b).1
  have hm1 : 6 * Real.sqrt 2 * shiftNode (21 / 20) r19 a * shiftNode (21 / 20) r19 b ≤
      6 * ((s2Hi : ℝ) / certT) * ((vecAt xiHi19 a.1 : ℝ) / certT) *
        ((vecAt xiHi19 b.1 : ℝ) / certT) := by
    have h1 := le_s2_hi; have h2 := (xi_bounds a).2; have h3 := (xi_bounds b).2
    gcongr
  refine hm1.trans_eq ?_
  unfold cABHi s2Hi denAB19 certT certS certRatio; push_cast; ring
private theorem eAB_ii_hi_chk :
    ∀ a : Fin 19, checkExpPairRowUp certS certRatio certM cABLo denAB19 (vecAt xiLo19 a.1)
    (eAB_ii_hi.getD a.1 []) xiLo19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAB_ii_hi_ge (a b : Fin 19) :
    eABFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 b) ≤
      (matAt eAB_ii_hi a.1 b.1 : ℝ) / certS := by
  have heq : Real.exp (-(6 * Real.sqrt 2 * shiftNode (21 / 20) r19 a *
      shiftNode (21 / 20) r19 b)) = eABFactor (shiftNode (21 / 20) r19 a)
      (shiftNode (21 / 20) r19 b) := by unfold eABFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowUp_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAB_ii_hi_shape a) (rfl : xiLo19.length = 19) (eAB_ii_hi_chk a) b ?_
  have hm1 : 6 * ((s2Lo : ℝ) / certT) * ((vecAt xiLo19 a.1 : ℝ) / certT) *
      ((vecAt xiLo19 b.1 : ℝ) / certT) ≤
      6 * Real.sqrt 2 * shiftNode (21 / 20) r19 a * shiftNode (21 / 20) r19 b := by
    have h1 := s2_lo_le; have h2 := (xi_bounds a).1; have h3 := (xi_bounds b).1
    have h01 : (6 : ℝ) * ((s2Lo : ℝ) / certT) ≤ 6 * Real.sqrt 2 := by linarith
    have h02 : (6 : ℝ) * ((s2Lo : ℝ) / certT) * ((vecAt xiLo19 a.1 : ℝ) / certT) ≤
        6 * Real.sqrt 2 * shiftNode (21 / 20) r19 a :=
      mul_le_mul h01 h2 (by positivity) (by positivity)
    exact mul_le_mul h02 h3 (by positivity) (mul_nonneg (by positivity)
      ((by positivity : (0 : ℝ) ≤ _).trans h2))
  refine le_trans ?_ hm1
  refine le_of_eq ?_
  unfold cABLo s2Lo denAB19 certT certS certRatio; push_cast; ring
private theorem eAC_ee_lo_chk :
    ∀ a : Fin 19, checkExpPairRowDn certS certRatio certM 3 denAC19 (vecAt xeHi19 a.1)
    (eAC_ee_lo.getD a.1 []) xeHi19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAC_ee_lo_le (a b : Fin 19) :
    (matAt eAC_ee_lo a.1 b.1 : ℝ) / certS ≤
      eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (17 / 10) r19 b) := by
  have heq : Real.exp (-(6 * shiftNode (17 / 10) r19 a * shiftNode (17 / 10) r19 b)) =
      eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (17 / 10) r19 b) := by
    unfold eACFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowDn_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAC_ee_lo_shape a) (rfl : xeHi19.length = 19) (eAC_ee_lo_chk a) b ?_
  have ha0 : 0 ≤ shiftNode (17 / 10) r19 a := (by positivity : (0 : ℝ) ≤ _).trans (xe_bounds a).1
  have hb0 : 0 ≤ shiftNode (17 / 10) r19 b := (by positivity : (0 : ℝ) ≤ _).trans (xe_bounds b).1
  have hm1 : 6 * shiftNode (17 / 10) r19 a * shiftNode (17 / 10) r19 b ≤
      6 * ((vecAt xeHi19 a.1 : ℝ) / certT) * ((vecAt xeHi19 b.1 : ℝ) / certT) := by
    have h2 := (xe_bounds a).2; have h3 := (xe_bounds b).2; gcongr
  refine hm1.trans_eq ?_
  unfold denAC19 certT certS certRatio; push_cast; ring
private theorem eAC_ei_lo_chk :
    ∀ a : Fin 19, checkExpPairRowDn certS certRatio certM 3 denAC19 (vecAt xeHi19 a.1)
    (eAC_ei_lo.getD a.1 []) xiHi19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAC_ei_lo_le (a b : Fin 19) :
    (matAt eAC_ei_lo a.1 b.1 : ℝ) / certS ≤
      eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 b) := by
  have heq : Real.exp (-(6 * shiftNode (17 / 10) r19 a * shiftNode (21 / 20) r19 b)) =
      eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 b) := by
    unfold eACFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowDn_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAC_ei_lo_shape a) (rfl : xiHi19.length = 19) (eAC_ei_lo_chk a) b ?_
  have ha0 : 0 ≤ shiftNode (17 / 10) r19 a := (by positivity : (0 : ℝ) ≤ _).trans (xe_bounds a).1
  have hb0 : 0 ≤ shiftNode (21 / 20) r19 b := (by positivity : (0 : ℝ) ≤ _).trans (xi_bounds b).1
  have hm1 : 6 * shiftNode (17 / 10) r19 a * shiftNode (21 / 20) r19 b ≤
      6 * ((vecAt xeHi19 a.1 : ℝ) / certT) * ((vecAt xiHi19 b.1 : ℝ) / certT) := by
    have h2 := (xe_bounds a).2; have h3 := (xi_bounds b).2; gcongr
  refine hm1.trans_eq ?_
  unfold denAC19 certT certS certRatio; push_cast; ring
private theorem eAC_ei_hi_chk :
    ∀ a : Fin 19, checkExpPairRowUp certS certRatio certM 3 denAC19 (vecAt xeLo19 a.1)
    (eAC_ei_hi.getD a.1 []) xiLo19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAC_ei_hi_ge (a b : Fin 19) :
    eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 b) ≤
      (matAt eAC_ei_hi a.1 b.1 : ℝ) / certS := by
  have heq : Real.exp (-(6 * shiftNode (17 / 10) r19 a * shiftNode (21 / 20) r19 b)) =
      eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 b) := by
    unfold eACFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowUp_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAC_ei_hi_shape a) (rfl : xiLo19.length = 19) (eAC_ei_hi_chk a) b ?_
  have hm1 : 6 * ((vecAt xeLo19 a.1 : ℝ) / certT) * ((vecAt xiLo19 b.1 : ℝ) / certT) ≤
      6 * shiftNode (17 / 10) r19 a * shiftNode (21 / 20) r19 b := by
    have h2 := (xe_bounds a).1; have h3 := (xi_bounds b).1
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h3
      (by positivity) (mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ _).trans h2))
  exact (le_of_eq (by unfold denAC19 certT certS certRatio; push_cast; ring)).trans hm1
private theorem eAC_ii_lo_chk :
    ∀ a : Fin 19, checkExpPairRowDn certS certRatio certM 3 denAC19 (vecAt xiHi19 a.1)
    (eAC_ii_lo.getD a.1 []) xiHi19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAC_ii_lo_le (a b : Fin 19) :
    (matAt eAC_ii_lo a.1 b.1 : ℝ) / certS ≤
      eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 b) := by
  have heq : Real.exp (-(6 * shiftNode (21 / 20) r19 a * shiftNode (21 / 20) r19 b)) =
      eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 b) := by
    unfold eACFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowDn_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAC_ii_lo_shape a) (rfl : xiHi19.length = 19) (eAC_ii_lo_chk a) b ?_
  have ha0 : 0 ≤ shiftNode (21 / 20) r19 a := (by positivity : (0 : ℝ) ≤ _).trans (xi_bounds a).1
  have hb0 : 0 ≤ shiftNode (21 / 20) r19 b := (by positivity : (0 : ℝ) ≤ _).trans (xi_bounds b).1
  have hm1 : 6 * shiftNode (21 / 20) r19 a * shiftNode (21 / 20) r19 b ≤
      6 * ((vecAt xiHi19 a.1 : ℝ) / certT) * ((vecAt xiHi19 b.1 : ℝ) / certT) := by
    have h2 := (xi_bounds a).2; have h3 := (xi_bounds b).2; gcongr
  refine hm1.trans_eq ?_
  unfold denAC19 certT certS certRatio; push_cast; ring
private theorem eAC_ii_hi_chk :
    ∀ a : Fin 19, checkExpPairRowUp certS certRatio certM 3 denAC19 (vecAt xiLo19 a.1)
    (eAC_ii_hi.getD a.1 []) xiLo19 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem eAC_ii_hi_ge (a b : Fin 19) :
    eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 b) ≤
      (matAt eAC_ii_hi a.1 b.1 : ℝ) / certS := by
  have heq : Real.exp (-(6 * shiftNode (21 / 20) r19 a * shiftNode (21 / 20) r19 b)) =
      eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 b) := by
    unfold eACFactor; congr 1; ring
  rw [← heq]
  refine checkExpPairRowUp_spec (by decide) (by decide) (by decide)
    (checkShape_getD eAC_ii_hi_shape a) (rfl : xiLo19.length = 19) (eAC_ii_hi_chk a) b ?_
  have hm1 : 6 * ((vecAt xiLo19 a.1 : ℝ) / certT) * ((vecAt xiLo19 b.1 : ℝ) / certT) ≤
      6 * shiftNode (21 / 20) r19 a * shiftNode (21 / 20) r19 b := by
    have h2 := (xi_bounds a).1; have h3 := (xi_bounds b).1
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h3
      (by positivity) (mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ _).trans h2))
  exact (le_of_eq (by unfold denAC19 certT certS certRatio; push_cast; ring)).trans hm1

private theorem eAB_ie_lo_le (b c : Fin 19) :
    (matAt eAB_ie_lo b.1 c.1 : ℝ) / certS ≤
      eABFactor (shiftNode (21 / 20) r19 b) (shiftNode (17 / 10) r19 c) := by
  have hm : matAt eAB_ie_lo b.1 c.1 = matAt eAB_ei_lo c.1 b.1 := by
    change vecAt (eAB_ie_lo.getD b.1 []) c.1 = _
    rw [eAB_ie_lo_tr, (transposeMat_spec 19).2 b, getCol_getD]
  rw [hm]; refine (eAB_ei_lo_le c b).trans_eq ?_; unfold eABFactor; congr 1; ring

private theorem eAB_ie_hi_ge (b c : Fin 19) :
    eABFactor (shiftNode (21 / 20) r19 b) (shiftNode (17 / 10) r19 c) ≤
      (matAt eAB_ie_hi b.1 c.1 : ℝ) / certS := by
  have hm : matAt eAB_ie_hi b.1 c.1 = matAt eAB_ei_hi c.1 b.1 := by
    change vecAt (eAB_ie_hi.getD b.1 []) c.1 = _
    rw [eAB_ie_hi_tr, (transposeMat_spec 19).2 b, getCol_getD]
  rw [hm]
  have he : eABFactor (shiftNode (21 / 20) r19 b) (shiftNode (17 / 10) r19 c) =
      eABFactor (shiftNode (17 / 10) r19 c) (shiftNode (21 / 20) r19 b) := by
    unfold eABFactor; congr 1; ring
  rw [he]; exact eAB_ei_hi_ge c b

private theorem eAC_ie_lo_le (a c : Fin 19) :
    (matAt eAC_ie_lo a.1 c.1 : ℝ) / certS ≤
      eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (17 / 10) r19 c) := by
  have hm : matAt eAC_ie_lo a.1 c.1 = matAt eAC_ei_lo c.1 a.1 := by
    change vecAt (eAC_ie_lo.getD a.1 []) c.1 = _
    rw [eAC_ie_lo_tr, (transposeMat_spec 19).2 a, getCol_getD]
  rw [hm]; refine (eAC_ei_lo_le c a).trans_eq ?_; unfold eACFactor; congr 1; ring

private theorem eAC_ie_hi_ge (a c : Fin 19) :
    eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (17 / 10) r19 c) ≤
      (matAt eAC_ie_hi a.1 c.1 : ℝ) / certS := by
  have hm : matAt eAC_ie_hi a.1 c.1 = matAt eAC_ei_hi c.1 a.1 := by
    change vecAt (eAC_ie_hi.getD a.1 []) c.1 = _
    rw [eAC_ie_hi_tr, (transposeMat_spec 19).2 a, getCol_getD]
  rw [hm]
  have he : eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (17 / 10) r19 c) =
      eACFactor (shiftNode (17 / 10) r19 c) (shiftNode (21 / 20) r19 a) := by
    unfold eACFactor; congr 1; ring
  rw [he]; exact eAC_ei_hi_ge c a

private theorem eAC_ee_lo_col_le (a c : Fin 19) :
    (vecAt (eAC_ee_lo.getD c.1 []) a.1 : ℝ) / certS ≤
      eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (17 / 10) r19 c) := by
  have hm : vecAt (eAC_ee_lo.getD c.1 []) a.1 = matAt eAC_ee_lo a.1 c.1 := by
    conv_lhs => rw [eAC_ee_lo_tr, (transposeMat_spec 19).2 c, getCol_getD]
  rw [hm]; exact eAC_ee_lo_le a c

private theorem eAC_ii_lo_col_le (a c : Fin 19) :
    (vecAt (eAC_ii_lo.getD c.1 []) a.1 : ℝ) / certS ≤
      eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 c) := by
  have hm : vecAt (eAC_ii_lo.getD c.1 []) a.1 = matAt eAC_ii_lo a.1 c.1 := by
    conv_lhs => rw [eAC_ii_lo_tr, (transposeMat_spec 19).2 c, getCol_getD]
  rw [hm]; exact eAC_ii_lo_le a c

private theorem eAC_ii_hi_col_ge (a c : Fin 19) :
    eACFactor (shiftNode (21 / 20) r19 a) (shiftNode (21 / 20) r19 c) ≤
      (vecAt (eAC_ii_hi.getD c.1 []) a.1 : ℝ) / certS := by
  have hm : vecAt (eAC_ii_hi.getD c.1 []) a.1 = matAt eAC_ii_hi a.1 c.1 := by
    conv_lhs => rw [eAC_ii_hi_tr, (transposeMat_spec 19).2 c, getCol_getD]
  rw [hm]; exact eAC_ii_hi_ge a c

private theorem eAC_ei_lo_col_le (a c : Fin 19) :
    (vecAt (eAC_ie_lo.getD c.1 []) a.1 : ℝ) / certS ≤
      eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 c) := by
  refine (eAC_ie_lo_le c a).trans_eq ?_; unfold eACFactor; congr 1; ring

private theorem eAC_ei_hi_col_ge (a c : Fin 19) :
    eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 c) ≤
      (vecAt (eAC_ie_hi.getD c.1 []) a.1 : ℝ) / certS := by
  have he : eACFactor (shiftNode (17 / 10) r19 a) (shiftNode (21 / 20) r19 c) =
      eACFactor (shiftNode (21 / 20) r19 c) (shiftNode (17 / 10) r19 a) := by
    unfold eACFactor; congr 1; ring
  rw [he]; exact eAC_ie_hi_ge c a

private theorem gw19_nn (k : Fin 19) : 0 ≤ gaussWeight r19 k :=
  (gaussWeight_pos (by omega) r19_strictMono r19_root k).le
private theorem we19_nn (k : Fin 19) : 0 ≤ shiftWeight (17 / 10) r19 k :=
  mul_nonneg (by norm_num) (gw19_nn k)
private theorem wi19_nn (k : Fin 19) : 0 ≤ shiftWeight (21 / 20) r19 k :=
  mul_nonneg (by norm_num) (gw19_nn k)

/-- j=1 upper-bound integrand matrix -/
private def matJ1Hi : List (List ℕ) := [
  [13056548719, 29871447536, 44751667499, 54990906956, 57389925235, 50496476577, 36761853487,
    21755401221, 10369581233, 3996102712, 1269321913, 344201983, 83698521, 19368646, 4546402,
    1149037, 326039, 103081, 29553],
  [29871447536, 67908445478, 100597160687, 121666566857, 124449528942, 106928910000, 75783477565,
    43556783273, 20130687968, 7515998600, 2312993833, 608169676, 143628541, 32356779, 7416693,
    1837188, 513088, 160403, 45695],
  [44751667499, 100597160687, 146076835759, 171770176546, 169556346692, 139676665765, 94394904629,
    51516628830, 22543557927, 7957778813, 2315373076, 576425880, 129263846, 27768147, 6102388,
    1458772, 396101, 121384, 34192],
  [54990906956, 121666566857, 171770176546, 194126904478, 182246885910, 141474731322, 89409017726,
    45360830721, 18378109761, 5994121702, 1611424576, 371430270, 77430433, 15554616, 3221226,
    732347, 191121, 56943, 15788],
  [57389925235, 124449528942, 169556346692, 182246885910, 160572206238, 115628947091, 67132510070,
    31055382693, 11414054841, 3368393183, 819342185, 171323073, 32565262, 6009884, 1154531, 246341,
    61142, 17580, 4778],
  [50496476577, 106928910000, 139676665765, 141474731322, 115628947091, 76182192150, 40005864401,
    16591047847, 5433683548, 1424501886, 307816168, 57353434, 9773369, 1631397, 286741, 56755,
    13275, 3660, 971],
  [36761853487, 75783477565, 94394904629, 89409017726, 67132510070, 40005864401, 18757148123,
    6875969362, 1976984207, 453437092, 85721665, 14021916, 2112075, 314773, 50042, 9100, 1991, 524,
    136],
  [21755401221, 43556783273, 51516628830, 45360830721, 31055382693, 16591047847, 6875969362,
    2203822362, 549908588, 109046658, 17823539, 2530203, 333222, 43898, 6257, 1038, 211, 53, 14],
  [10369581233, 20130687968, 22543557927, 18378109761, 11414054841, 5433683548, 1976984207,
    549908588, 118151494, 20094101, 2816811, 344314, 39353, 4552, 578, 87, 17, 4, 1],
  [3996102712, 7515998600, 7957778813, 5994121702, 3368393183, 1424501886, 453437092, 109046658,
    20094101, 2918988, 349507, 36641, 3621, 367, 42, 6, 1, 1, 1],
  [1269321913, 2312993833, 2315373076, 1611424576, 819342185, 307816168, 85721665, 17823539,
    2816811, 349507, 35745, 3214, 275, 25, 3, 1, 1, 1, 1],
  [344201983, 608169676, 576425880, 371430270, 171323073, 57353434, 14021916, 2530203, 344314,
    36641, 3214, 249, 19, 2, 1, 1, 1, 1, 1],
  [83698521, 143628541, 129263846, 77430433, 32565262, 9773369, 2112075, 333222, 39353, 3621, 275,
    19, 2, 1, 1, 1, 1, 1, 1],
  [19368646, 32356779, 27768148, 15554616, 6009884, 1631397, 314773, 43898, 4552, 367, 25, 2, 1, 1,
    1, 1, 1, 1, 1],
  [4546402, 7416693, 6102388, 3221226, 1154531, 286741, 50042, 6257, 578, 42, 3, 1, 1, 1, 1, 1, 1,
    1, 1],
  [1149037, 1837188, 1458772, 732347, 246341, 56755, 9100, 1038, 87, 6, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [326039, 513088, 396101, 191121, 61142, 13275, 1991, 211, 17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [103081, 160403, 121384, 56943, 17580, 3660, 524, 53, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [29553, 45695, 34192, 15788, 4778, 971, 136, 14, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matJ1Hi_shape : checkShape matJ1Hi 19 = true := rfl
private theorem matJ1Hi_chk :
    ∀ a : Fin 19, checkInitRowUp certS (fpMulUp certS c2Hi (fpMulUp certS (vecAt weHi19 a.1)
    (fpPowUp certS (vecAt eAeHi19 a.1) 3))) (matJ1Hi.getD a.1 []) weHi19 eAeHi19
    (eAB_ee_hi.getD a.1 []) = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem ar2TensorQuad_one_le : ar2TensorQuad (17 / 10) (21 / 20) r19 1 ≤
    (5408671524016 : ℝ) / certS := by
  rw [ar2TensorQuad_one_eq, Finset.mul_sum]
  have hpt : ∀ a b : Fin 19,
      (3 / (2 * Real.pi)) *
        (shiftWeight (17 / 10) r19 a * eAFactor (shiftNode (17 / 10) r19 a) ^ 3) *
        (shiftWeight (17 / 10) r19 b * eAFactor (shiftNode (17 / 10) r19 b) ^ 3) *
        eABFactor (shiftNode (17 / 10) r19 a) (shiftNode (17 / 10) r19 b) ≤
      (matAt matJ1Hi a.1 b.1 : ℝ) / certS := fun a b =>
    checkInitRowUp_spec (by decide) (checkShape_getD matJ1Hi_shape a)
      (rfl : weHi19.length = 19) (rfl : eAeHi19.length = 19)
      (checkShape_getD eAB_ee_hi_shape a)
      (by positivity) (we19_nn a) (Real.exp_pos _).le we19_nn
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
      le_c2_hi (we_bounds a).2 (eAeHi_ge a)
      (fun k => (we_bounds k).2) eAeHi_ge (fun k => eAB_ee_hi_ge a k) (matJ1Hi_chk a) b
  have hsum : sumMatNat matJ1Hi = 5408671524016 := rfl
  have hms := checkShape_spec matJ1Hi_shape
  calc ∑ a : Fin 19, (3 / (2 * Real.pi)) * ∑ b : Fin 19, _
      ≤ ∑ a : Fin 19, ∑ b : Fin 19, (matAt matJ1Hi a.1 b.1 : ℝ) / certS := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun b _ => ?_
          refine (le_of_eq (by ring)).trans (hpt a b)
    _ = (sumMatNat matJ1Hi : ℝ) / certS := by
          rw [sumMatNat_eq hms.1 hms.2, Nat.cast_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun a _ => by rw [Nat.cast_sum, Finset.sum_div]
    _ = (5408671524016 : ℝ) / certS := by
          have hR : (sumMatNat matJ1Hi : ℝ) = (5408671524016 : ℝ) := by exact_mod_cast hsum
          rw [hR]

/-- Lower bound for initial (end, int) matrix `ar2InitMat` -/
private def matM1Lo : List (List ℕ) := [
  [8066364056, 18521965522, 28215584504, 36295333403, 41661127177, 43295496897, 40798985895,
    34794742985, 26834524458, 18769210403, 11999784806, 7104362423, 3963355582, 2125611618,
    1117637100, 584316108, 303357685, 149555009, 55412901],
  [18465224295, 42233679026, 63891041993, 81384619143, 92264570902, 94486634028, 87574395364,
    73350730178, 55502636452, 38069283384, 23867731631, 13864100497, 7596134688, 4006947602,
    2076128630, 1072046718, 551139427, 269827693, 99584448],
  [27691631941, 62897292981, 93985378119, 117656399253, 130485425781, 130196519088, 117178741446,
    95058278316, 69541445455, 46074405657, 27903014553, 15670262623, 8315551449, 4259462000,
    2150291294, 1086201939, 548796381, 265389393, 97267474],
  [34076267240, 76643626344, 112553052890, 137490104809, 147828507726, 142188932785, 122780099359,
    95211667869, 66417182355, 41906711242, 24169188423, 12942665348, 6565375639, 3226532191,
    1570177632, 768957540, 379107109, 180171936, 65390077],
  [35627331923, 79144316773, 113698514812, 134650897173, 139210213159, 127829022737, 104746597973,
    76725043374, 50395364097, 29892481112, 16207226273, 8172097136, 3915654829, 1826119088,
    848384350, 399504172, 190950668, 88776950, 31822722],
  [31415180621, 68770106172, 96257971797, 109890816918, 108461103193, 94272595861, 72605397513,
    49711446145, 30407205299, 16764557369, 8448566601, 3967112543, 1776788259, 778813291,
    342491648, 153967629, 70941362, 32135164, 11351188],
  [22925929776, 49361371847, 67091410041, 73485955350, 68828013005, 56227615232, 40376453264,
    25616527314, 14458114002, 7339556636, 3405676268, 1475591461, 612395352, 250279123, 103446128,
    44130815, 19508540, 8581208, 2981325],
  [13603189092, 28764976773, 37866707684, 39647522089, 35076153409, 26784692618, 17822546943,
    10407296220, 5381580301, 2497109937, 1059109482, 420420752, 160592758, 60816762, 23496500,
    9468167, 4001011, 1704540, 581609],
  [6501930338, 13489458178, 17168510680, 17140663565, 14278635658, 10153787784, 6234224881,
    3335271032, 1572452278, 663609946, 255990385, 92649136, 32423784, 11330063, 4076419, 1546695,
    623225, 256700, 85936],
  [2512796371, 5112325287, 6285090506, 5975766891, 4679731898, 3093189677, 1748652568, 855109742,
    366670331, 140385914, 49129987, 16172306, 5173255, 1664466, 556629, 198545, 76188, 30312,
    9951],
  [800445912, 1596989877, 1896488265, 1717194052, 1264197551, 776684669, 404281908, 180705881,
    70474788, 24479012, 7771938, 2326817, 680336, 201547, 62648, 21007, 7676, 2950, 949],
  [217661208, 426069170, 489184518, 422355763, 292777140, 167507253, 80453412, 32946779, 11715178,
    3700978, 1068709, 291720, 78146, 21361, 6183, 1952, 680, 252, 79],
  [53067609, 102021482, 113448314, 93632117, 61308206, 32787275, 14592200, 5500033, 1791768,
    517391, 136562, 34152, 8420, 2132, 577, 172, 57, 20, 6],
  [12310113, 23276853, 25134681, 19902742, 12366732, 6216052, 2579438, 900895, 270808, 72001,
    17498, 4037, 922, 217, 55, 15, 5, 1, 0],
  [2895751, 5395693, 5676731, 4333193, 2570401, 1222964, 476976, 155717, 43590, 10772, 2433, 522,
    111, 24, 5, 1, 0, 0, 0],
  [733184, 1349310, 1388727, 1027701, 586185, 266255, 98544, 30388, 8009, 1860, 395, 79, 16, 3, 0,
    0, 0, 0, 0],
  [208338, 379671, 384030, 277315, 153349, 67145, 23843, 7028, 1766, 390, 79, 15, 2, 0, 0, 0, 0, 0,
    0],
  [65935, 119326, 119217, 84606, 45768, 19525, 6732, 1922, 467, 99, 19, 3, 0, 0, 0, 0, 0, 0, 0],
  [18912, 34095, 33827, 23772, 12701, 5339, 1810, 507, 121, 25, 4, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matM1Lo_shape : checkShape matM1Lo 19 = true := rfl
private theorem matM1Lo_chk :
    ∀ a : Fin 19, checkInitRowDn certS (fpMulDn certS c2Lo (fpMulDn certS (vecAt weLo19 a.1)
    (fpPowDn certS (vecAt eAeLo19 a.1) 3))) (matM1Lo.getD a.1 []) wiLo19 eAiLo19
    (eAB_ei_lo.getD a.1 []) = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matM1Lo_le (a b : Fin 19) :
    (matAt matM1Lo a.1 b.1 : ℝ) / certS ≤ ar2InitMat (17 / 10) (21 / 20) r19 a b := by
  rw [ar2InitMat_eq_factor]
  exact checkInitRowDn_spec (by decide) (checkShape_getD matM1Lo_shape a)
    (rfl : wiLo19.length = 19) (rfl : eAiLo19.length = 19)
    (checkShape_getD eAB_ei_lo_shape a)
    c2_lo_le (we_bounds a).1 (eAeLo_le a)
    (fun k => (wi_bounds k).1) eAiLo_le (fun k => eAB_ei_lo_le a k) (matM1Lo_chk a) b

/-- Upper bound for initial (end, int) matrix `ar2InitMat` -/
private def matM1Hi : List (List ℕ) := [
  [8066364058, 18521965524, 28215584506, 36295333405, 41661127178, 43295496899, 40798985898,
    34794742987, 26834524460, 18769210405, 11999784808, 7104362425, 3963355584, 2125611620,
    1117637102, 584316110, 303357687, 149555011, 55412903],
  [18465224297, 42233679028, 63891041996, 81384619145, 92264570905, 94486634031, 87574395366,
    73350730180, 55502636454, 38069283386, 23867731633, 13864100499, 7596134690, 4006947603,
    2076128631, 1072046719, 551139429, 269827695, 99584450],
  [27691631943, 62897292984, 93985378121, 117656399254, 130485425783, 130196519090, 117178741447,
    95058278318, 69541445457, 46074405658, 27903014554, 15670262625, 8315551451, 4259462001,
    2150291296, 1086201941, 548796383, 265389394, 97267476],
  [34076267242, 76643626346, 112553052892, 137490104811, 147828507729, 142188932787, 122780099361,
    95211667871, 66417182356, 41906711244, 24169188424, 12942665349, 6565375640, 3226532193,
    1570177634, 768957541, 379107110, 180171937, 65390078],
  [35627331925, 79144316776, 113698514814, 134650897175, 139210213161, 127829022738, 104746597975,
    76725043376, 50395364098, 29892481113, 16207226274, 8172097137, 3915654830, 1826119089,
    848384351, 399504173, 190950670, 88776952, 31822723],
  [31415180624, 68770106174, 96257971800, 109890816920, 108461103195, 94272595863, 72605397514,
    49711446147, 30407205300, 16764557370, 8448566602, 3967112544, 1776788260, 778813292,
    342491649, 153967630, 70941363, 32135165, 11351189],
  [22925929778, 49361371849, 67091410042, 73485955352, 68828013007, 56227615234, 40376453266,
    25616527315, 14458114003, 7339556637, 3405676269, 1475591462, 612395353, 250279124, 103446129,
    44130816, 19508541, 8581209, 2981326],
  [13603189094, 28764976775, 37866707685, 39647522091, 35076153411, 26784692619, 17822546944,
    10407296221, 5381580302, 2497109938, 1059109483, 420420753, 160592759, 60816763, 23496501,
    9468168, 4001012, 1704541, 581610],
  [6501930340, 13489458180, 17168510682, 17140663567, 14278635659, 10153787785, 6234224882,
    3335271033, 1572452279, 663609947, 255990386, 92649137, 32423785, 11330064, 4076420, 1546696,
    623226, 256701, 85937],
  [2512796373, 5112325289, 6285090508, 5975766892, 4679731899, 3093189678, 1748652569, 855109743,
    366670332, 140385915, 49129988, 16172307, 5173256, 1664467, 556630, 198546, 76189, 30313,
    9952],
  [800445914, 1596989879, 1896488267, 1717194053, 1264197553, 776684670, 404281909, 180705882,
    70474789, 24479013, 7771939, 2326818, 680337, 201548, 62649, 21008, 7677, 2951, 950],
  [217661210, 426069172, 489184520, 422355764, 292777141, 167507254, 80453414, 32946780, 11715179,
    3700979, 1068710, 291721, 78147, 21362, 6184, 1953, 681, 253, 80],
  [53067611, 102021484, 113448315, 93632118, 61308207, 32787276, 14592201, 5500034, 1791769,
    517392, 136563, 34153, 8421, 2133, 578, 173, 58, 21, 7],
  [12310115, 23276855, 25134683, 19902743, 12366733, 6216053, 2579439, 900896, 270809, 72002,
    17499, 4038, 923, 218, 56, 16, 6, 2, 1],
  [2895753, 5395695, 5676733, 4333195, 2570402, 1222965, 476977, 155718, 43591, 10773, 2434, 523,
    112, 25, 6, 2, 1, 1, 1],
  [733186, 1349312, 1388728, 1027702, 586186, 266256, 98545, 30389, 8010, 1861, 396, 80, 17, 4, 1,
    1, 1, 1, 1],
  [208340, 379673, 384032, 277317, 153350, 67146, 23844, 7029, 1767, 391, 80, 16, 3, 1, 1, 1, 1, 1,
    1],
  [65937, 119328, 119219, 84607, 45769, 19526, 6733, 1923, 468, 100, 20, 4, 1, 1, 1, 1, 1, 1, 1],
  [18914, 34096, 33829, 23774, 12702, 5340, 1811, 508, 122, 26, 5, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matM1Hi_shape : checkShape matM1Hi 19 = true := rfl
private theorem matM1Hi_chk :
    ∀ a : Fin 19, checkInitRowUp certS (fpMulUp certS c2Hi (fpMulUp certS (vecAt weHi19 a.1)
    (fpPowUp certS (vecAt eAeHi19 a.1) 3))) (matM1Hi.getD a.1 []) wiHi19 eAiHi19
    (eAB_ei_hi.getD a.1 []) = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matM1Hi_ge (a b : Fin 19) :
    ar2InitMat (17 / 10) (21 / 20) r19 a b ≤ (matAt matM1Hi a.1 b.1 : ℝ) / certS := by
  rw [ar2InitMat_eq_factor]
  exact checkInitRowUp_spec (by decide) (checkShape_getD matM1Hi_shape a)
    (rfl : wiHi19.length = 19) (rfl : eAiHi19.length = 19)
    (checkShape_getD eAB_ei_hi_shape a)
    (by positivity) (we19_nn a) (Real.exp_pos _).le wi19_nn
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    le_c2_hi (we_bounds a).2 (eAeHi_ge a)
    (fun k => (wi_bounds k).2) eAiHi_ge (fun k => eAB_ei_hi_ge a k) (matM1Hi_chk a) b

/-- Lower bound for j=2 scaled matrix -/
private def matG2EndLo : List (List ℕ) := [
  [7868755639, 17315551357, 24125539235, 26547659591, 23761719994, 17072172314, 9610530486,
    4149337281, 1360398794, 341134200, 67248205, 10937420, 1569484, 215490, 30907, 5038, 996, 241,
    59],
  [16847886864, 36834158053, 50727760630, 54903139530, 48107651348, 33691781559, 18418219957,
    7698493295, 2437999312, 589716665, 112095011, 17590714, 2439491, 324543, 45261, 7204, 1397,
    334, 81],
  [22421919474, 48451062915, 65349087221, 68656318765, 57909780868, 38743329911, 20098396151,
    7928650811, 2360350330, 535441162, 95392076, 14046759, 1833314, 230605, 30596, 4668, 875, 204,
    49],
  [23243247720, 49389406097, 64649045071, 65086061099, 51983876557, 32577665414, 15682360519,
    5697294519, 1553314429, 321666093, 52273455, 7033616, 842389, 97879, 12102, 1739, 311, 70, 16],
  [19418130703, 40375197642, 50844307246, 48449610360, 36072317924, 20784875063, 9090856064,
    2972182482, 724246061, 133516941, 19299840, 2315317, 248590, 26114, 2952, 393, 66, 14, 3],
  [12945717767, 26219457889, 31509714151, 28097972676, 19222990190, 10012437721, 3903418621,
    1124830354, 239654324, 38455879, 4834491, 505886, 47693, 4444, 451, 54, 8, 1, 0],
  [6733897955, 13231710919, 15068093551, 12449696280, 7729297691, 3586065435, 1225750887,
    305812263, 55910238, 7660658, 821721, 73622, 5988, 487, 43, 4, 0, 0, 0],
  [2675783301, 5084363473, 5455119451, 4142670013, 2310552557, 943666051, 279087182, 59431016,
    9185672, 1058483, 95423, 7213, 499, 35, 2, 0, 0, 0, 0],
  [803784316, 1473443930, 1483264666, 1029313663, 512020672, 182531943, 46270895, 8325531, 1076459,
    103211, 7737, 488, 28, 1, 0, 0, 0, 0, 0],
  [183759346, 324530948, 305783970, 193263344, 85388675, 26443971, 5715533, 864093, 92923, 7370,
    456, 23, 1, 0, 0, 0, 0, 0, 0],
  [32870233, 55908878, 49280224, 28346210, 11114403, 2987376, 550021, 69806, 6238, 409, 20, 0, 0,
    0, 0, 0, 0, 0, 0],
  [4834211, 7924871, 6543163, 3431771, 1197053, 280083, 44079, 4714, 351, 19, 0, 0, 0, 0, 0, 0, 0,
    0, 0],
  [626571, 991723, 769396, 369590, 115340, 23652, 3206, 291, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [77876, 119334, 87417, 38724, 10906, 1980, 234, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [10174, 15148, 10545, 4347, 1117, 182, 19, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1526, 2218, 1479, 573, 136, 20, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [281, 401, 258, 95, 21, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [65, 91, 57, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [15, 21, 13, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matG2EndLo_shape : checkShape matG2EndLo 19 = true := rfl
private theorem matG2EndLo_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matM1Lo eAB_ei_lo eAB_ie_lo eAC_ee_lo eAeLo19
    eAiLo19 weLo19 eAeLo19 (matG2EndLo.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem ar2TensorQuad_two_ge :
    (1495869861753 : ℝ) / certS ≤ 2 * ar2TensorQuad (17 / 10) (21 / 20) r19 2 := by
  rw [ar2TensorQuad_two_eq]
  have hpt : ∀ b c : Fin 19, (matAt matG2EndLo b.1 c.1 : ℝ) / certS ≤
      ar2StepMat (shiftNode (17 / 10) r19) (shiftNode (21 / 20) r19)
        (shiftNode (17 / 10) r19) (shiftWeight (17 / 10) r19)
        (ar2InitMat (17 / 10) (21 / 20) r19) b c := fun b =>
    checkStepAtDn_sound (by decide) b (checkShape_spec matM1Lo_shape).1
      (checkShape_spec eAB_ei_lo_shape).1 rfl (checkShape_getD matG2EndLo_shape b)
      rfl rfl (checkShape_getD eAB_ie_lo_shape b) (checkShape_spec eAC_ee_lo_shape).1
      (fun c => checkShape_getD eAC_ee_lo_shape c) k2_lo_le (fun a => matM1Lo_le a b)
      eAeLo_le (eAiLo_le b) eAeLo_le (fun c => (we_bounds c).1)
      (fun a => eAB_ei_lo_le a b) (fun c => eAB_ie_lo_le b c)
      eAC_ee_lo_col_le (matG2EndLo_chk b)
  have hsum : sumMatNat matG2EndLo = 1495869861753 := rfl
  have hms := checkShape_spec matG2EndLo_shape
  have hsumR : (sumMatNat matG2EndLo : ℝ) = (1495869861753 : ℝ) := by exact_mod_cast hsum
  calc (1495869861753 : ℝ) / certS = (sumMatNat matG2EndLo : ℝ) / certS := by rw [hsumR]
    _ = ∑ b : Fin 19, ∑ c : Fin 19, (matAt matG2EndLo b.1 c.1 : ℝ) / certS := by
        rw [sumMatNat_eq hms.1 hms.2, Nat.cast_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => by rw [Nat.cast_sum, Finset.sum_div]
    _ ≤ _ := Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => hpt b c

/-- Lower bound for terminal readout matrix `ar2ReadoutMat` -/
private def matRLo : List (List ℕ) := [
  [97891118382674, 91300589169601, 79796302805822, 64345309245164, 46871607124526, 30100161643977,
    16635552741128, 7761800773580, 3027817645668, 991244009615, 277787353095, 69116388638,
    16082596152, 3732396198, 928584055, 266787345, 94984943, 44531598, 28774206],
  [95557034894301, 88982393230303, 77544239590115, 62260952557035, 45094001763777, 28752490902004,
    15757085823822, 7282011589557, 2811261255405, 910335803479, 252287118587, 62084726048,
    14295011409, 3285336309, 810288841, 231090403, 81796040, 38189251, 24618208],
  [91431914599597, 84899089375350, 73600950130698, 58641774445945, 42039974087690, 26465930041094,
    14287513669151, 6491607856682, 2460231712988, 781343528550, 212299545570, 51234327320,
    11578334229, 2615348128, 635183364, 178798779, 62634495, 29028420, 18635069],
  [85657195912033, 79212399192364, 68159334132148, 53711478344411, 37946889106155, 23459967494554,
    12397156683086, 5498648785596, 2030099816555, 627270854823, 165740162568, 38910353879,
    8564315860, 1887871590, 448641837, 123980892, 42800851, 19631280, 12528695],
  [78465165082096, 72178356935933, 61509613961380, 47788742594333, 33135016953185, 20015289460120,
    10292454937206, 4427208086802, 1581051809202, 471778489201, 120314357100, 27275594489,
    5806083222, 1240883581, 286880028, 77448371, 26246331, 11880937, 7526261],
  [70189465536589, 64151757963864, 54032978965602, 41266868036726, 27974167856746, 16434129586638,
    8179938511701, 3392117145817, 1164370641662, 333333794674, 81504062293, 17726481881,
    3626711453, 747199848, 167198849, 43906213, 14556425, 6487348, 4073530],
  [61256925377626, 55571147797883, 46175524873658, 34575677902646, 22837895461077, 12995907405148,
    6232380974584, 2479043064480, 813517179999, 222192569204, 51798157807, 10748799676, 2102635192,
    415598148, 89627601, 22811002, 7377376, 3230441, 2008363],
  [52152539875692, 46918257141007, 38400206721957, 28128461040192, 18052786586482, 9917843385530,
    4565474799851, 1734841514936, 541927348648, 140593067005, 31111194985, 6133311186, 1142453460,
    215825284, 44709050, 10997259, 3461807, 1487042, 914518],
  [43360502884388, 38657160865155, 31125707436189, 22266212225740, 13856040157810, 7331071311331,
    3230524496330, 1169284455359, 346636648389, 85154572634, 17831477112, 3329635862, 588911134,
    106057038, 21055203, 4995650, 1528287, 643300, 391115],
  [35296371824425, 31169591993265, 24669829969682, 17215933324318, 10373886382259, 5278081957551,
    2222902289519, 765090483588, 214881431242, 49900321798, 9871549405, 1743138312, 292310496,
    50115022, 9523430, 2177363, 646834, 266652, 160221],
  [28252053178943, 24707292602872, 19215700798359, 13075873847811, 7626018277643, 3729424473659,
    1500534756174, 490942060853, 130593378883, 28661199271, 5355476463, 894166819, 142148306,
    23198579, 4219528, 929576, 268152, 108259, 64286],
  [22371222076405, 19376208310482, 14810249442482, 9829862712778, 5551139795254, 2611011562739,
    1004455326589, 312710055348, 78874545887, 16380371777, 2894804435, 457601312, 69052238,
    10740246, 1871806, 397708, 111483, 44101, 25889],
  [17659853005305, 15153903419387, 11391170026648, 7381718981086, 4041928003291, 1831653290148,
    675111306313, 200462708993, 48067480602, 9471852327, 1587567316, 238257593, 34218053, 5084823,
    850978, 174707, 47659, 18493, 10738],
  [14022656057090, 11928973690568, 8828807254686, 5595446795272, 2977402961940, 1303536207759,
    461821801951, 131268858813, 30041015355, 5640117318, 900343717, 128814486, 17676965, 2518837,
    406117, 80785, 21493, 8193, 4710],
  [11309140225669, 9546198936266, 6967772548213, 4329094499836, 2245479818449, 953355876455,
    326073232076, 89152929508, 19574306869, 3520529262, 538191947, 73804187, 9727399, 1335452,
    208318, 40295, 10486, 3934, 2242],
  [9354788253100, 7844405264379, 5658243533791, 3456529586939, 1754381293169, 725675215043,
    240896452905, 63731510545, 13510026918, 2343078157, 345313557, 45685663, 5819296, 774167,
    117435, 22184, 5665, 2098, 1186],
  [8009765179952, 6681244070181, 4774062395891, 2877451470126, 1435498452546, 581608920497,
    188552339012, 48598758913, 10019550602, 1688400013, 241721008, 31085144, 3854011, 500109,
    74204, 13757, 3462, 1268, 713],
  [7154558094046, 5945512045027, 4219932294087, 2519230297482, 1241461387440, 495641713193,
    157999721652, 39975990951, 8080595768, 1334112948, 187109498, 23582211, 2868269, 365678, 53413,
    9772, 2433, 884, 495],
  [6705905745064, 5560841459233, 3931942926789, 2334626279227, 1142532679785, 452364571457,
    142838202446, 35763403504, 7148863368, 1166735055, 161744488, 20154766, 2425007, 306098, 44316,
    8047, 1992, 721, 402]
]
private def rVecsLo : List (List ℕ) := mkReadoutVecsDn certS weLo19 eAeLo19 eAB_ie_lo
private theorem matRLo_shape : checkShape matRLo 19 = true := rfl
private theorem matRLo_chk :
    ∀ a : Fin 19, checkReadoutRowDn certS k2Lo (vecAt eAiLo19 a.1) (eAC_ie_lo.getD a.1 [])
    (matRLo.getD a.1 []) eAiLo19 (eAB_ii_lo.getD a.1 []) rVecsLo = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matRLo_le (a b : Fin 19) :
    (matAt matRLo a.1 b.1 : ℝ) / certS ≤ ar2ReadoutMat (17 / 10) (21 / 20) r19 a b :=
  checkReadoutRowsDn_sound (n := 19) (s := certS) (k2 := k2Lo)
    (by decide) rfl rfl rfl (checkShape_spec eAB_ie_lo_shape).1
    (checkShape_getD eAB_ie_lo_shape) (checkShape_getD eAB_ii_lo_shape)
    (checkShape_getD eAC_ie_lo_shape) (checkShape_getD matRLo_shape)
    k2_lo_le (fun c => (we_bounds c).1) eAeLo_le eAiLo_le
    eAB_ii_lo_le eAB_ie_lo_le eAC_ie_lo_le matRLo_chk a b

/-- Upper bound for terminal readout matrix `ar2ReadoutMat` -/
private def matRHi : List (List ℕ) := [
  [97891118382793, 91300589169719, 79796302805942, 64345309245265, 46871607124610, 30100161644034,
    16635552741168, 7761800773602, 3027817645680, 991244009621, 277787353098, 69116388641,
    16082596153, 3732396200, 928584057, 266787346, 94984945, 44531599, 28774207],
  [95557034894414, 88982393230415, 77544239590229, 62260952557130, 45094001763854, 28752490902056,
    15757085823858, 7282011589577, 2811261255416, 910335803484, 252287118590, 62084726050,
    14295011410, 3285336311, 810288843, 231090404, 81796041, 38189253, 24618209],
  [91431914599702, 84899089375453, 73600950130801, 58641774446029, 42039974087759, 26465930041140,
    14287513669182, 6491607856699, 2460231712997, 781343528555, 212299545573, 51234327322,
    11578334230, 2615348130, 635183366, 178798780, 62634497, 29028421, 18635070],
  [85657195912130, 79212399192455, 68159334132239, 53711478344485, 37946889106214, 23459967494593,
    12397156683112, 5498648785610, 2030099816562, 627270854827, 165740162570, 38910353881,
    8564315862, 1887871592, 448641838, 123980894, 42800853, 19631282, 12528696],
  [78465165082179, 72178356936013, 61509613961459, 47788742594397, 33135016953234, 20015289460152,
    10292454937226, 4427208086812, 1581051809208, 471778489204, 120314357102, 27275594490,
    5806083223, 1240883583, 286880029, 77448372, 26246332, 11880938, 7526262],
  [70189465536660, 64151757963935, 54032978965670, 41266868036779, 27974167856785, 16434129586662,
    8179938511717, 3392117145825, 1164370641667, 333333794676, 81504062295, 17726481882,
    3626711455, 747199849, 167198850, 43906214, 14556426, 6487349, 4073532],
  [61256925377688, 55571147797943, 46175524873715, 34575677902688, 22837895461108, 12995907405167,
    6232380974596, 2479043064487, 813517180002, 222192569206, 51798157809, 10748799677, 2102635194,
    415598149, 89627602, 22811004, 7377377, 3230443, 2008364],
  [52152539875744, 46918257141058, 38400206722004, 28128461040227, 18052786586505, 9917843385545,
    4565474799860, 1734841514940, 541927348651, 140593067007, 31111194987, 6133311187, 1142453461,
    215825285, 44709052, 10997260, 3461808, 1487044, 914520],
  [43360502884435, 38657160865197, 31125707436226, 22266212225768, 13856040157829, 7331071311342,
    3230524496336, 1169284455363, 346636648391, 85154572636, 17831477114, 3329635863, 588911135,
    106057039, 21055204, 4995651, 1528289, 643301, 391117],
  [35296371824463, 31169591993299, 24669829969711, 17215933324341, 10373886382274, 5278081957559,
    2222902289524, 765090483591, 214881431244, 49900321799, 9871549406, 1743138314, 292310498,
    50115023, 9523432, 2177365, 646835, 266653, 160222],
  [28252053178973, 24707292602900, 19215700798383, 13075873847829, 7626018277654, 3729424473665,
    1500534756177, 490942060855, 130593378885, 28661199273, 5355476464, 894166820, 142148308,
    23198581, 4219530, 929578, 268153, 108261, 64288],
  [22371222076430, 19376208310504, 14810249442501, 9829862712792, 5551139795262, 2611011562744,
    1004455326592, 312710055350, 78874545889, 16380371778, 2894804436, 457601313, 69052239,
    10740248, 1871807, 397709, 111484, 44103, 25890],
  [17659853005325, 15153903419406, 11391170026663, 7381718981097, 4041928003298, 1831653290151,
    675111306315, 200462708994, 48067480604, 9471852328, 1587567318, 238257595, 34218054, 5084825,
    850979, 174709, 47660, 18494, 10739],
  [14022656057107, 11928973690583, 8828807254698, 5595446795281, 2977402961945, 1303536207762,
    461821801953, 131268858815, 30041015356, 5640117320, 900343718, 128814487, 17676966, 2518838,
    406119, 80787, 21495, 8194, 4711],
  [11309140225683, 9546198936279, 6967772548223, 4329094499843, 2245479818454, 953355876458,
    326073232078, 89152929510, 19574306871, 3520529264, 538191948, 73804189, 9727401, 1335453,
    208320, 40296, 10487, 3936, 2243],
  [9354788253112, 7844405264389, 5658243533800, 3456529586945, 1754381293173, 725675215046,
    240896452906, 63731510546, 13510026919, 2343078158, 345313558, 45685664, 5819297, 774169,
    117436, 22185, 5667, 2099, 1187],
  [8009765179962, 6681244070190, 4774062395898, 2877451470131, 1435498452549, 581608920499,
    188552339014, 48598758914, 10019550603, 1688400014, 241721009, 31085146, 3854013, 500110,
    74205, 13759, 3463, 1269, 714],
  [7154558094056, 5945512045035, 4219932294094, 2519230297487, 1241461387443, 495641713195,
    157999721653, 39975990952, 8080595770, 1334112949, 187109499, 23582213, 2868270, 365679, 53414,
    9773, 2434, 886, 496],
  [6705905745073, 5560841459241, 3931942926795, 2334626279231, 1142532679788, 452364571459,
    142838202447, 35763403505, 7148863370, 1166735056, 161744489, 20154767, 2425008, 306099, 44317,
    8048, 1993, 722, 404]
]
private def rVecsHi : List (List ℕ) := mkReadoutVecsUp certS weHi19 eAeHi19 eAB_ie_hi
private theorem matRHi_shape : checkShape matRHi 19 = true := rfl
private theorem matRHi_chk :
    ∀ a : Fin 19, checkReadoutRowUp certS k2Hi (vecAt eAiHi19 a.1) (eAC_ie_hi.getD a.1 [])
    (matRHi.getD a.1 []) eAiHi19 (eAB_ii_hi.getD a.1 []) rVecsHi = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matRHi_ge (a b : Fin 19) :
    ar2ReadoutMat (17 / 10) (21 / 20) r19 a b ≤ (matAt matRHi a.1 b.1 : ℝ) / certS :=
  checkReadoutRowsUp_sound (n := 19) (s := certS) (k2 := k2Hi)
    (by decide) rfl rfl rfl (checkShape_spec eAB_ie_hi_shape).1
    (checkShape_getD eAB_ie_hi_shape) (checkShape_getD eAB_ii_hi_shape)
    (checkShape_getD eAC_ie_hi_shape) (checkShape_getD matRHi_shape)
    we19_nn le_k2_hi (fun c => (we_bounds c).2) eAeHi_ge eAiHi_ge
    eAB_ii_hi_ge eAB_ie_hi_ge eAC_ie_hi_ge matRHi_chk a b

/-- Lower bound for `ar2PrefixMat 0` -/
private def matGLo0 : List (List ℕ) := [
  [4878070724, 10937811848, 15952911847, 19242070389, 20254934765, 18854392206, 15529291008,
    11293870394, 7254169490, 4137530077, 2121065982, 996073314, 439372880, 187390044, 79567854,
    34448860, 15326813, 6753567, 2346235],
  [10450603319, 23338976367, 33797864273, 40354725496, 41932098718, 38432312059, 31098981818,
    22180385746, 13953225427, 7788414124, 3906534774, 1795660144, 776039717, 324777253, 135602135,
    57876368, 25460035, 11128673, 3848622],
  [13922746669, 30869938701, 44133874889, 51744898043, 52532419989, 46828846014, 36710958239,
    25285474334, 15325771282, 8230950502, 3970965758, 1756868409, 732103566, 296244159, 120037529,
    49947499, 21533725, 9278610, 3182947],
  [14454558740, 31718817701, 44519399704, 50849936903, 49931864033, 42774490988, 32045982885,
    20999534280, 12070155217, 6135863997, 2800721159, 1173601895, 464371247, 179133319, 69562473,
    27919903, 11697907, 4939158, 1675006],
  [12099399060, 26197411715, 35904331581, 39648645360, 37295192644, 30353507694, 21452346538,
    13186445838, 7080796676, 3354984859, 1426685876, 557755097, 206580063, 74975384, 27579187,
    10572473, 4271383, 1757469, 587366],
  [8085547436, 17225166354, 22937268798, 24317042119, 21717687752, 16617109715, 10948408922,
    6231941462, 3084090850, 1343160972, 524760724, 188822298, 64628360, 21809857, 7520505, 2729414,
    1055923, 421288, 138372],
  [4217291971, 8818052981, 11359011491, 11490131068, 9668023501, 6891193434, 4189425723,
    2183769980, 984405336, 389373409, 138105930, 45211431, 14144484, 4393964, 1407758, 480093,
    176803, 68115, 21934],
  [1680853361, 3442536784, 4274544276, 4105061542, 3233802126, 2131458893, 1185782435, 560984817,
    228196424, 81196905, 25898242, 7642767, 2166638, 614672, 181695, 57882, 20197, 7488, 2360],
  [506550914, 1014719165, 1211376435, 1100484431, 807958570, 489836299, 247894932, 105762017,
    38563554, 12260187, 3492933, 923190, 235704, 60727, 16480, 4884, 1609, 573, 176],
  [116196132, 227467598, 260690889, 223563171, 152576346, 84826447, 38920234, 14920747, 4858544,
    1374922, 348595, 82223, 18843, 4395, 1092, 300, 93, 31, 9],
  [20855309, 39889777, 43872156, 35499882, 22508573, 11468292, 4767388, 1641182, 476932, 120063,
    27074, 5696, 1171, 247, 56, 14, 4, 1, 0],
  [3077390, 5753605, 6077680, 4645564, 2740536, 1281938, 483813, 149900, 38971, 8749, 1759, 331,
    61, 11, 2, 0, 0, 0, 0],
  [400131, 732055, 744132, 538766, 296744, 127965, 44053, 12347, 2887, 581, 104, 17, 2, 0, 0, 0, 0,
    0, 0],
  [49877, 89446, 87756, 60438, 31247, 12501, 3954, 1010, 214, 39, 6, 0, 0, 0, 0, 0, 0, 0, 0],
  [6533, 11510, 10942, 7209, 3523, 1318, 386, 91, 17, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [982, 1704, 1578, 1001, 466, 165, 45, 9, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [181, 311, 282, 174, 78, 26, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [42, 71, 63, 38, 16, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [10, 17, 15, 8, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo0_shape : checkShape matGLo0 19 = true := rfl
private theorem matGLo0_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matM1Lo eAB_ei_lo eAB_ii_lo eAC_ie_lo eAeLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo0.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo0_le (b c : Fin 19) :
    (matAt matGLo0 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 0 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matM1Lo_shape).1
    (checkShape_spec eAB_ei_lo_shape).1 rfl (checkShape_getD matGLo0_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ie_lo_shape).1
    (fun c => checkShape_getD eAC_ie_lo_shape c) k2_lo_le (fun a => matM1Lo_le a b)
    eAeLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ei_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ei_lo_col_le (matGLo0_chk b) c

/-- Lower bound for `ar2PrefixMat 1` -/
private def matGLo1 : List (List ℕ) := [
  [1917112756, 4351055296, 6480322321, 8041446237, 8758217160, 8467383616, 7257317610, 5493626678,
    3668530517, 2170519224, 1150790290, 556988389, 252279272, 110059088, 47619893, 20929846,
    9418725, 4182832, 1459439],
  [4103955584, 9272050016, 13698620449, 16806244584, 18042087032, 17146994523, 14414561501,
    10683220653, 6976190440, 4033559652, 2089752240, 988907533, 438426253, 187536709, 79737179,
    34531771, 15359053, 6764518, 2349179],
  [5436249898, 12183213963, 17743389994, 21332368227, 22321059769, 20577993710, 16713279457,
    11930100136, 7486777127, 4155252471, 2066307027, 939443829, 400965753, 165618337, 68267201,
    28798789, 12545899, 5444698, 1875164],
  [5549124217, 12294489961, 17545275598, 20497638055, 20682106095, 18262722804, 14126821410,
    9561407832, 5671958792, 2970921486, 1394093132, 598930051, 242254022, 95234679, 37571058,
    15272348, 6460799, 2746071, 934694],
  [4484968027, 9792901549, 13618512173, 15339808964, 14778481855, 12353634664, 8981394832,
    5681354868, 3137665903, 1526939941, 665613111, 266122706, 100541764, 37120396, 13851702,
    5371750, 2189397, 906305, 303915],
  [2824634492, 6061342195, 8173519588, 8814942350, 8037481661, 6294311357, 4250609628, 2480967838,
    1258467154, 561151645, 224101708, 82262652, 28659389, 9821041, 3430425, 1258030, 490569,
    196800, 64835],
  [1349498255, 2839260575, 3696974322, 3794987410, 3250551741, 2363804027, 1468043736, 782099294,
    360232518, 145462329, 52600550, 17526297, 5570083, 1754155, 568517, 195702, 72587, 28103,
    9074],
  [477903460, 983983660, 1233084414, 1199184128, 959226925, 643249393, 364522078, 175750520,
    72847733, 26394514, 8563177, 2566803, 737896, 211906, 63287, 20331, 7139, 2659, 840],
  [124193388, 249915197, 300715210, 276160460, 205446183, 126429655, 65017911, 28201676, 10453853,
    3376935, 976677, 261740, 67663, 17624, 4827, 1441, 477, 170, 52],
  [23907615, 46986239, 54218764, 46936129, 32403004, 18251480, 8492798, 3303583, 1091498, 313286,
    80502, 19224, 4455, 1049, 263, 72, 22, 7, 2],
  [3521843, 6759441, 7479054, 6102029, 3908352, 2014440, 847915, 295700, 87055, 22195, 5065, 1077,
    223, 47, 10, 2, 0, 0, 0],
  [419995, 787648, 836471, 644097, 383422, 181215, 69162, 21680, 5703, 1295, 263, 50, 9, 1, 0, 0,
    0, 0, 0],
  [43825, 80401, 82123, 59856, 33239, 14468, 5032, 1425, 337, 68, 12, 2, 0, 0, 0, 0, 0, 0, 0],
  [4395, 7902, 7787, 5396, 2810, 1134, 362, 93, 20, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [469, 828, 790, 524, 257, 97, 28, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [58, 102, 95, 60, 28, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [9, 16, 14, 9, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo1_shape : checkShape matGLo1 19 = true := rfl
private theorem matGLo1_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo0 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo1.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo1_le (b c : Fin 19) :
    (matAt matGLo1 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 1 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo0_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo1_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo0_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo1_chk b) c

/-- Lower bound for `ar2PrefixMat 2` -/
private def matGLo2 : List (List ℕ) := [
  [718390614, 1631414006, 2432268484, 3022436947, 3297435693, 3194031451, 2743146778, 2080812196,
    1392365624, 825416640, 438425340, 212550938, 96412735, 42114151, 18241095, 8024158, 3613330,
    1605389, 560278],
  [1556408044, 3518394240, 5203265482, 6392312071, 6873656127, 6544738810, 5512668611, 4093899367,
    2678649767, 1551715159, 805356869, 381724214, 169477631, 72583844, 30893410, 13390225, 5959510,
    2625875, 912135],
  [2104974312, 4720008332, 6880549498, 8282861064, 8680209585, 8016379606, 6523013065, 4665101834,
    2933141440, 1630885717, 812376815, 369917742, 158102722, 65382074, 26977277, 11389702, 4964876,
    2155588, 742564],
  [2210408961, 4899748111, 6998376599, 8185645509, 8271171926, 7315461730, 5668578486, 3843483147,
    2284037406, 1198394567, 563239392, 242332131, 98145773, 38626704, 15253192, 6205105, 2626553,
    1116835, 380229],
  [1848743473, 4038528306, 5620562539, 6337736356, 6113783751, 5118185349, 3726947003, 2361402779,
    1306261774, 636688785, 277951419, 111280327, 42093121, 15557438, 5810565, 2255006, 919600,
    380817, 127728],
  [1209835293, 2597204630, 3504681236, 3783326922, 3453676597, 2708232633, 1831510583, 1070583749,
    543853762, 242852323, 97116926, 35693937, 12449336, 4270352, 1492851, 547841, 213742, 85777,
    28265],
  [601951675, 1266915666, 1650653890, 1695850569, 1454068328, 1058649640, 658315693, 351182010,
    161968360, 65487726, 23710089, 7909099, 2516197, 793127, 257248, 88608, 32881, 12734, 4112],
  [222122610, 457483153, 573607880, 558254566, 446957087, 300039522, 170222036, 82167802, 34098692,
    12369173, 4017385, 1205448, 346862, 99692, 29795, 9577, 3364, 1253, 396],
  [60092164, 120956794, 145612836, 133810801, 99627455, 61366616, 31590293, 13716789, 5089974,
    1645944, 476515, 127820, 33071, 8620, 2362, 705, 234, 83, 25],
  [12017739, 23624427, 27272337, 23622830, 16320017, 9200046, 4284810, 1668297, 551727, 158507,
    40766, 9743, 2259, 532, 133, 37, 11, 3, 1],
  [1833818, 3520377, 3896606, 3180809, 2038605, 1051505, 442952, 154604, 45555, 11624, 2655, 565,
    117, 25, 5, 1, 0, 0, 0],
  [225745, 423436, 449833, 346538, 206407, 97617, 37283, 11695, 3079, 699, 142, 27, 5, 0, 0, 0, 0,
    0, 0],
  [24223, 44447, 45413, 33113, 18398, 8013, 2788, 790, 187, 38, 6, 1, 0, 0, 0, 0, 0, 0, 0],
  [2488, 4474, 4410, 3057, 1593, 643, 205, 53, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [270, 478, 456, 302, 149, 56, 16, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [34, 60, 55, 35, 16, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [5, 9, 8, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo2_shape : checkShape matGLo2 19 = true := rfl
private theorem matGLo2_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo1 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo2.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo2_le (b c : Fin 19) :
    (matAt matGLo2 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 2 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo1_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo2_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo1_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo2_chk b) c

/-- Lower bound for `ar2PrefixMat 3` -/
private def matGLo3 : List (List ℕ) := [
  [287460924, 652511644, 972066978, 1206626873, 1314663638, 1271499216, 1090201356, 825542727,
    551444417, 326345945, 173057643, 83771700, 37946266, 16555162, 7163151, 3148344, 1416788,
    629185, 219528],
  [621970563, 1405414767, 2076873843, 2548835656, 2737267192, 2602474822, 2188594523, 1622628736,
    1059911071, 612986643, 317647167, 150338733, 66658692, 28515116, 12124556, 5250870, 2335495,
    1028611, 357215],
  [839365557, 1881367663, 2740632013, 3296012580, 3450027054, 3181845715, 2585268612, 1846062395,
    1158881938, 643373858, 320007898, 145517463, 62117010, 25659842, 10577584, 4462386, 1944043,
    843692, 290571],
  [879004322, 1947759302, 2780254247, 3249084317, 3279502643, 2896991774, 2241800340, 1517884012,
    900743216, 471946650, 221517368, 95188940, 38508529, 15140480, 5973680, 2428433, 1027374,
    436684, 148639],
  [733004003, 1600716666, 2226532674, 2508700425, 2417754611, 2021831956, 1470506504, 930560601,
    514113771, 250276407, 109131000, 43643370, 16492056, 6089978, 2272822, 881501, 359306, 148742,
    49880],
  [478290523, 1026483649, 1384474590, 1493553113, 1362295074, 1067247997, 721010550, 421002245,
    213634447, 95293702, 38068776, 13978149, 4871019, 1669549, 583259, 213925, 83428, 33470,
    11027],
  [237345625, 499419208, 650421459, 667850223, 572230438, 416281860, 258634431, 137842308,
    63514466, 25656670, 9280842, 3093283, 983348, 309751, 100408, 34569, 12823, 4965, 1603],
  [87385273, 179942674, 225539603, 219396811, 175551581, 117765817, 66762195, 32201347, 13352480,
    4839729, 1570699, 470964, 135429, 38901, 11620, 3733, 1311, 488, 154],
  [23598185, 47491727, 57155671, 52501696, 39069838, 24051476, 12373318, 5369000, 1990946, 643376,
    186141, 49900, 12903, 3361, 921, 275, 91, 32, 10],
  [4712810, 9263102, 10690765, 9256941, 6392479, 3601830, 1676595, 652410, 215634, 61914, 15914,
    3801, 881, 207, 52, 14, 4, 1, 0],
  [718402, 1378947, 1525990, 1245299, 797827, 411341, 173198, 60421, 17794, 4538, 1036, 220, 45, 9,
    2, 0, 0, 0, 0],
  [88371, 165743, 176043, 135583, 80731, 38166, 14571, 4569, 1202, 273, 55, 10, 1, 0, 0, 0, 0, 0,
    0],
  [9477, 17389, 17764, 12950, 7193, 3131, 1089, 308, 73, 14, 2, 0, 0, 0, 0, 0, 0, 0, 0],
  [973, 1750, 1724, 1195, 622, 251, 80, 20, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [105, 187, 178, 118, 58, 22, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [13, 23, 21, 13, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2, 3, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo3_shape : checkShape matGLo3 19 = true := rfl
private theorem matGLo3_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo2 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo3.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo3_le (b c : Fin 19) :
    (matAt matGLo3 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 3 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo2_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo3_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo2_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo3_chk b) c

/-- Lower bound for `ar2PrefixMat 4` -/
private def matGLo4 : List (List ℕ) := [
  [114301712, 259464912, 386558640, 479879435, 522905477, 505803104, 433744792, 328497749,
    219462792, 129898098, 68893491, 33353664, 15110155, 6592967, 2852938, 1254018, 564355, 250636,
    87451],
  [247260087, 558733077, 825728863, 1013461525, 1088503193, 1035030726, 870545075, 645516497,
    421716721, 243929746, 126420831, 59841246, 26536136, 11352759, 4827597, 2090877, 930038,
    409628, 142258],
  [333557033, 747664977, 1089204252, 1310033615, 1371384767, 1264927708, 1027890085, 734081932,
    460888019, 255903915, 127300253, 57894225, 24715974, 10210874, 4209507, 1775993, 773754,
    335812, 115657],
  [349112212, 773610027, 1104316841, 1290628286, 1302826329, 1150985732, 890774701, 603198479,
    357992710, 187593143, 88060416, 37844717, 15311493, 6020567, 2375590, 965788, 408606, 173683,
    59119],
  [290906861, 635291512, 883704121, 995756734, 959731198, 802639225, 583826452, 369492047,
    204156880, 99395907, 43344986, 17335985, 6551506, 2419436, 903007, 350245, 142768, 59103,
    19820],
  [189642063, 407009081, 548975697, 592258191, 540242998, 423267625, 285973684, 166995748,
    84748004, 37805865, 15104255, 5546427, 1932920, 662552, 231476, 84903, 33112, 13284, 4376],
  [94004888, 197807133, 257623048, 264537451, 226673952, 164908928, 102464053, 54613215, 25166246,
    10166614, 3677838, 1225892, 389731, 122770, 39798, 13702, 5083, 1968, 635],
  [34568441, 71183898, 89223861, 86796703, 69453780, 46594153, 26415927, 12741882, 5283799,
    1915270, 621621, 186398, 53602, 15397, 4599, 1477, 519, 193, 61],
  [9323037, 18762972, 22581432, 20743272, 15436902, 9503359, 4889226, 2121616, 786779, 254260,
    73565, 19722, 5100, 1328, 364, 108, 36, 12, 3],
  [1859437, 3654785, 4218140, 3652490, 2522334, 1421248, 661591, 257453, 85096, 24434, 6280, 1500,
    347, 81, 20, 5, 1, 0, 0],
  [283072, 543351, 601298, 490704, 314386, 162094, 68253, 23811, 7012, 1788, 408, 86, 18, 3, 0, 0,
    0, 0, 0],
  [34777, 65226, 69280, 53358, 31771, 15020, 5734, 1798, 473, 107, 21, 4, 0, 0, 0, 0, 0, 0, 0],
  [3725, 6835, 6982, 5090, 2827, 1231, 428, 121, 28, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [382, 687, 677, 469, 244, 98, 31, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [41, 73, 70, 46, 22, 8, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [5, 9, 8, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo4_shape : checkShape matGLo4 19 = true := rfl
private theorem matGLo4_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo3 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo4.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo4_le (b c : Fin 19) :
    (matAt matGLo4 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 4 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo3_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo4_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo3_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo4_chk b) c

/-- Lower bound for `ar2PrefixMat 5` -/
private def matGLo5 : List (List ℕ) := [
  [45387378, 103030440, 153500664, 190562735, 207655045, 200870490, 172260435, 130467077, 87165932,
    51594758, 27365100, 13248823, 6002278, 2619026, 1133343, 498174, 224200, 99570, 34742],
  [98190077, 221882141, 327916358, 402479187, 432293607, 411071265, 345757122, 256391628,
    167507407, 96893413, 50218486, 23771684, 10541683, 4510089, 1917893, 830672, 369494, 162742,
    56518],
  [132476016, 296946550, 432601198, 520320189, 544702853, 502434946, 408296600, 291601110,
    183086234, 101660554, 50573071, 23000579, 9819591, 4056853, 1672502, 705642, 307433, 133428,
    45954],
  [138676920, 307301694, 438675169, 512695481, 517554200, 457248000, 353885991, 239645851,
    142232266, 74534073, 34989031, 15037262, 6084042, 2392334, 943983, 383779, 162371, 69018,
    23493],
  [115578956, 252406863, 351108023, 395635345, 381330224, 318921048, 231984363, 146822527,
    81126805, 39498567, 17225174, 6889446, 2603676, 961543, 358883, 139200, 56741, 23490, 7877],
  [75362262, 161743276, 218162594, 235366798, 214699891, 168216085, 113655167, 66371195, 33683322,
    15026423, 6003524, 2204601, 768315, 263362, 92012, 33749, 13162, 5280, 1739],
  [37365301, 78625329, 102402271, 105152122, 90103132, 65552751, 40731229, 21710178, 10004464,
    4041674, 1462132, 487365, 154944, 48810, 15823, 5447, 2020, 782, 252],
  [13743496, 28300971, 35473521, 34508944, 27614087, 18525653, 10503061, 5066313, 2100937, 761561,
    247177, 74119, 21315, 6122, 1829, 587, 206, 76, 24],
  [3707420, 7461358, 8979889, 8248997, 6138885, 3779312, 1944386, 843755, 312903, 101121, 29258,
    7843, 2028, 528, 144, 43, 14, 5, 1],
  [739585, 1453685, 1677769, 1452794, 1003280, 565321, 263160, 102408, 33849, 9719, 2498, 596, 138,
    32, 8, 2, 0, 0, 0],
  [112613, 216159, 239214, 195217, 125074, 64487, 27154, 9473, 2790, 711, 162, 34, 7, 1, 0, 0, 0,
    0, 0],
  [13837, 25953, 27566, 21231, 12642, 5976, 2281, 715, 188, 42, 8, 1, 0, 0, 0, 0, 0, 0, 0],
  [1482, 2720, 2778, 2025, 1125, 489, 170, 48, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [152, 273, 269, 186, 97, 39, 12, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [16, 29, 27, 18, 9, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo5_shape : checkShape matGLo5 19 = true := rfl
private theorem matGLo5_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo4 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo5.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo5_le (b c : Fin 19) :
    (matAt matGLo5 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 5 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo4_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo5_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo4_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo5_chk b) c

/-- Lower bound for `ar2PrefixMat 6` -/
private def matGLo6 : List (List ℕ) := [
  [18029631, 40927590, 60975993, 75697902, 82486896, 79791150, 68425801, 51823992, 34623601,
    20493997, 10869609, 5262477, 2384106, 1040270, 450158, 197871, 89050, 39548, 13799],
  [39004835, 88139809, 130259958, 159877976, 171719959, 163288409, 137342617, 101843611, 66536459,
    38487147, 19947160, 9442210, 4187167, 1791399, 761779, 329938, 146760, 64640, 22448],
  [52624373, 117957877, 171844095, 206687937, 216372017, 199580373, 162184743, 115829580, 72724715,
    40380799, 20088062, 9135956, 3900367, 1611382, 664314, 280278, 122111, 52997, 18252],
  [55087499, 122071116, 174256676, 203659028, 205587786, 181631088, 140571851, 95192202, 56497082,
    29605966, 13898020, 5972919, 2416613, 950242, 374951, 152437, 64493, 27414, 9331],
  [45912173, 100265022, 139472203, 157159294, 151476007, 126684385, 92150068, 58321212, 32225160,
    15689495, 6842082, 2736568, 1034204, 381932, 142550, 55290, 22538, 9330, 3128],
  [29936758, 64250483, 86662111, 93495892, 85285878, 66820619, 45147075, 26364371, 13379811,
    5968814, 2384713, 875704, 305186, 104610, 36548, 13405, 5228, 2097, 691],
  [14843039, 31233185, 40678261, 41770478, 35792298, 26039860, 16179798, 8623959, 3974064, 1605462,
    580795, 193593, 61547, 19388, 6285, 2164, 802, 310, 100],
  [5459550, 11242437, 14091675, 13708465, 10969489, 7359149, 4172229, 2012530, 834567, 302518,
    98186, 29442, 8466, 2432, 726, 233, 81, 30, 9],
  [1472781, 2964038, 3567271, 3276917, 2438667, 1501324, 772401, 335177, 124298, 40169, 11622,
    3115, 805, 209, 57, 17, 5, 2, 0],
  [293807, 577489, 666508, 577133, 398560, 224577, 104541, 40682, 13446, 3861, 992, 237, 54, 12, 3,
    0, 0, 0, 0],
  [44737, 85873, 95031, 77553, 49687, 25618, 10787, 3763, 1108, 282, 64, 13, 2, 0, 0, 0, 0, 0, 0],
  [5497, 10310, 10951, 8434, 5022, 2374, 906, 284, 74, 16, 3, 0, 0, 0, 0, 0, 0, 0, 0],
  [589, 1080, 1103, 804, 447, 194, 67, 19, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [60, 108, 107, 74, 38, 15, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [6, 11, 11, 7, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo6_shape : checkShape matGLo6 19 = true := rfl
private theorem matGLo6_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo5 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo6.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo6_le (b c : Fin 19) :
    (matAt matGLo6 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 6 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo5_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo6_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo5_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo6_chk b) c

/-- Lower bound for `ar2PrefixMat 7` -/
private def matGLo7 : List (List ℕ) := [
  [7162047, 16257977, 24221955, 30070049, 32766890, 31696037, 27181293, 20586430, 13753790,
    8140982, 4317815, 2090453, 947056, 413234, 178819, 78601, 35374, 15710, 5481],
  [15494153, 35012369, 51744037, 63509398, 68213465, 64864139, 54557516, 40456009, 26430715,
    15288501, 7923740, 3750790, 1663295, 711609, 302606, 131063, 58298, 25677, 8917],
  [20904254, 46857021, 68262521, 82103716, 85950568, 79280331, 64425470, 46011569, 28888804,
    16040667, 7979681, 3629121, 1549362, 640097, 263888, 111336, 48506, 21052, 7250],
  [21882576, 48490682, 69220508, 80900089, 81666250, 72149854, 55839767, 37813474, 22442498,
    11760462, 5520749, 2372639, 959958, 377467, 148942, 60552, 25618, 10889, 3706],
  [18237709, 39828311, 55402591, 62428436, 60170858, 50322871, 36604792, 23166946, 12800805,
    6232340, 2717881, 1087047, 410817, 151714, 56625, 21963, 8952, 3706, 1242],
  [11891695, 25522040, 34424547, 37139108, 33877865, 26542961, 17933640, 10472641, 5314822,
    2370973, 947272, 347853, 121228, 41554, 14518, 5325, 2076, 833, 274],
  [5896007, 12406562, 16158369, 16592223, 14217547, 10343647, 6426997, 3425639, 1578591, 637727,
    230705, 76899, 24447, 7701, 2496, 859, 318, 123, 39],
  [2168642, 4465721, 5597495, 5445276, 4357300, 2923200, 1657292, 799416, 331506, 120166, 39001,
    11695, 3363, 966, 288, 92, 32, 12, 3],
  [585012, 1177364, 1416978, 1301644, 968678, 596350, 306810, 133138, 49373, 15956, 4616, 1237,
    320, 83, 22, 6, 2, 0, 0],
  [116703, 229386, 264745, 229244, 158312, 89204, 41525, 16159, 5341, 1533, 394, 94, 21, 5, 1, 0,
    0, 0, 0],
  [17770, 34109, 37747, 30804, 19736, 10175, 4284, 1494, 440, 112, 25, 5, 1, 0, 0, 0, 0, 0, 0],
  [2183, 4095, 4349, 3350, 1994, 943, 360, 112, 29, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [233, 429, 438, 319, 177, 77, 26, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [24, 43, 42, 29, 15, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [2, 4, 4, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo7_shape : checkShape matGLo7 19 = true := rfl
private theorem matGLo7_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo6 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo7.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo7_le (b c : Fin 19) :
    (matAt matGLo7 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 7 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo6_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo7_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo6_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo7_chk b) c

/-- Lower bound for `ar2PrefixMat 8` -/
private def matGLo8 : List (List ℕ) := [
  [2844997, 6458196, 9621749, 11944805, 13016082, 12590708, 10797307, 8177613, 5463463, 3233870,
    1715181, 830398, 376202, 164150, 71033, 31223, 14051, 6240, 2177],
  [6154783, 13908056, 20554425, 25228016, 27096633, 25766178, 21672054, 16070473, 10499163,
    6073106, 3147576, 1489940, 660717, 282675, 120205, 52062, 23158, 10199, 3542],
  [8303856, 18613149, 27116122, 32614307, 34142412, 31492782, 25591945, 18277335, 11475604,
    6371894, 3169799, 1441610, 615459, 254268, 104825, 44226, 19268, 8362, 2880],
  [8692484, 19262108, 27496686, 32136210, 32440562, 28660338, 22181432, 15020787, 8914919, 4671654,
    2193029, 942493, 381328, 149943, 59165, 24053, 10176, 4325, 1472],
  [7244629, 15821140, 22007768, 24798674, 23901893, 19989945, 14540664, 9202698, 5084916, 2475698,
    1079635, 431812, 163190, 60266, 22493, 8724, 3556, 1472, 493],
  [4723783, 10138218, 13674597, 14752915, 13457440, 10543769, 7123855, 4160091, 2111230, 941832,
    376289, 138179, 48156, 16506, 5767, 2115, 824, 330, 109],
  [2342095, 4928310, 6418657, 6590999, 5647697, 4108852, 2553024, 1360782, 627071, 253327, 91644,
    30547, 9711, 3059, 991, 341, 126, 49, 15],
  [861459, 1773938, 2223518, 2163051, 1730870, 1161196, 658334, 317556, 131686, 47734, 15492, 4645,
    1335, 383, 114, 36, 12, 4, 1],
  [232387, 467689, 562873, 517058, 384792, 236891, 121875, 52887, 19612, 6338, 1833, 491, 127, 33,
    9, 2, 0, 0, 0],
  [46358, 91120, 105166, 91064, 62887, 35435, 16495, 6419, 2121, 609, 156, 37, 8, 2, 0, 0, 0, 0,
    0],
  [7058, 13549, 14994, 12236, 7839, 4042, 1702, 593, 174, 44, 10, 2, 0, 0, 0, 0, 0, 0, 0],
  [867, 1626, 1727, 1330, 792, 374, 143, 44, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [92, 170, 174, 126, 70, 30, 10, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [9, 17, 16, 11, 6, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo8_shape : checkShape matGLo8 19 = true := rfl
private theorem matGLo8_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo7 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo8.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo8_le (b c : Fin 19) :
    (matAt matGLo8 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 8 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo7_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo8_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo7_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo8_chk b) c

/-- Lower bound for `ar2PrefixMat 9` -/
private def matGLo9 : List (List ℕ) := [
  [1130127, 2565409, 3822077, 4744871, 5170418, 5001445, 4289047, 3248418, 2170268, 1284600,
    681326, 329861, 149440, 65206, 28216, 12402, 5581, 2478, 864],
  [2444883, 5524741, 8164898, 10021404, 10763680, 10235179, 8608857, 6383723, 4170614, 2412438,
    1250321, 591853, 262458, 112288, 47749, 20681, 9199, 4051, 1407],
  [3298567, 7393760, 10771423, 12955484, 13562498, 12509977, 10165968, 7260363, 4558489, 2531127,
    1259149, 572655, 244480, 101003, 41640, 17568, 7654, 3321, 1144],
  [3452943, 7651549, 10922597, 12765569, 12886468, 11384837, 8811200, 5966754, 3541301, 1855736,
    871144, 374389, 151476, 59562, 23502, 9554, 4042, 1718, 584],
  [2877807, 6284683, 8742217, 9850858, 9494626, 7940670, 5776035, 3655617, 2019897, 983429, 428867,
    171530, 64824, 23939, 8935, 3465, 1412, 584, 196],
  [1876444, 4027238, 5432005, 5860349, 5345743, 4188336, 2829832, 1652527, 838650, 374127, 149474,
    54889, 19129, 6557, 2290, 840, 327, 131, 43],
  [930358, 1957689, 2549705, 2618165, 2243454, 1632173, 1014146, 540548, 249093, 100630, 36404,
    12134, 3857, 1215, 393, 135, 50, 19, 6],
  [342200, 704667, 883255, 859236, 687559, 461266, 261512, 126143, 52310, 18961, 6154, 1845, 530,
    152, 45, 14, 5, 1, 0],
  [92312, 185782, 223592, 205392, 152852, 94101, 48413, 21008, 7790, 2517, 728, 195, 50, 13, 3, 1,
    0, 0, 0],
  [18415, 36195, 41775, 36173, 24981, 14076, 6552, 2549, 842, 242, 62, 14, 3, 0, 0, 0, 0, 0, 0],
  [2804, 5382, 5956, 4860, 3114, 1605, 676, 235, 69, 17, 4, 0, 0, 0, 0, 0, 0, 0, 0],
  [344, 646, 686, 528, 314, 148, 56, 17, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [36, 67, 69, 50, 28, 12, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [3, 6, 6, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
private theorem matGLo9_shape : checkShape matGLo9 19 = true := rfl
private theorem matGLo9_chk :
    ∀ b : Fin 19, checkStepAtDn certS k2Lo matGLo8 eAB_ii_lo eAB_ii_lo eAC_ii_lo eAiLo19
    eAiLo19 wiLo19 eAiLo19 (matGLo9.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGLo9_le (b c : Fin 19) :
    (matAt matGLo9 b.1 c.1 : ℝ) / certS ≤ ar2PrefixMat (17 / 10) (21 / 20) r19 9 b c :=
  checkStepAtDn_sound (by decide) b (checkShape_spec matGLo8_shape).1
    (checkShape_spec eAB_ii_lo_shape).1 rfl (checkShape_getD matGLo9_shape b)
    rfl rfl (checkShape_getD eAB_ii_lo_shape b) (checkShape_spec eAC_ii_lo_shape).1
    (fun c => checkShape_getD eAC_ii_lo_shape c) k2_lo_le (fun a => matGLo8_le a b)
    eAiLo_le (eAiLo_le b) eAiLo_le (fun c => (wi_bounds c).1)
    (fun a => eAB_ii_lo_le a b) (fun c => eAB_ii_lo_le b c)
    eAC_ii_lo_col_le (matGLo9_chk b) c

/-- Upper bound for `ar2PrefixMat 0` -/
private def matGHi0 : List (List ℕ) := [
  [4878070726, 10937811852, 15952911851, 19242070394, 20254934770, 18854392210, 15529291012,
    11293870397, 7254169493, 4137530078, 2121065983, 996073315, 439372881, 187390045, 79567855,
    34448861, 15326814, 6753568, 2346236],
  [10450603321, 23338976371, 33797864277, 40354725501, 41932098723, 38432312063, 31098981821,
    22180385749, 13953225429, 7788414126, 3906534775, 1795660145, 776039718, 324777254, 135602136,
    57876369, 25460036, 11128674, 3848623],
  [13922746671, 30869938704, 44133874892, 51744898047, 52532419993, 46828846017, 36710958242,
    25285474336, 15325771284, 8230950504, 3970965759, 1756868411, 732103567, 296244160, 120037530,
    49947500, 21533726, 9278611, 3182948],
  [14454558741, 31718817703, 44519399707, 50849936907, 49931864036, 42774490990, 32045982887,
    20999534282, 12070155219, 6135863999, 2800721160, 1173601896, 464371248, 179133320, 69562474,
    27919904, 11697908, 4939159, 1675007],
  [12099399062, 26197411717, 35904331584, 39648645362, 37295192647, 30353507697, 21452346540,
    13186445840, 7080796677, 3354984860, 1426685877, 557755098, 206580064, 74975385, 27579188,
    10572474, 4271384, 1757470, 587367],
  [8085547437, 17225166356, 22937268800, 24317042121, 21717687754, 16617109717, 10948408923,
    6231941463, 3084090851, 1343160973, 524760725, 188822299, 64628361, 21809858, 7520506, 2729415,
    1055924, 421289, 138373],
  [4217291973, 8818052983, 11359011492, 11490131070, 9668023503, 6891193435, 4189425724,
    2183769981, 984405337, 389373410, 138105931, 45211432, 14144485, 4393965, 1407759, 480094,
    176804, 68116, 21935],
  [1680853362, 3442536785, 4274544277, 4105061543, 3233802127, 2131458894, 1185782436, 560984819,
    228196425, 81196906, 25898243, 7642768, 2166639, 614673, 181696, 57883, 20198, 7489, 2361],
  [506550915, 1014719167, 1211376436, 1100484432, 807958571, 489836300, 247894933, 105762018,
    38563555, 12260188, 3492934, 923191, 235705, 60728, 16481, 4885, 1610, 574, 177],
  [116196133, 227467599, 260690890, 223563172, 152576347, 84826448, 38920235, 14920748, 4858545,
    1374923, 348596, 82224, 18844, 4396, 1093, 301, 94, 32, 10],
  [20855310, 39889778, 43872157, 35499883, 22508574, 11468293, 4767389, 1641183, 476933, 120064,
    27075, 5697, 1172, 248, 57, 15, 5, 2, 1],
  [3077391, 5753606, 6077681, 4645565, 2740537, 1281939, 483814, 149901, 38972, 8750, 1760, 332,
    62, 12, 3, 1, 1, 1, 1],
  [400132, 732056, 744133, 538767, 296745, 127966, 44054, 12348, 2888, 582, 105, 18, 3, 1, 1, 1, 1,
    1, 1],
  [49878, 89447, 87757, 60439, 31248, 12502, 3955, 1011, 215, 40, 7, 1, 1, 1, 1, 1, 1, 1, 1],
  [6534, 11511, 10943, 7210, 3524, 1319, 387, 92, 18, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [983, 1705, 1579, 1002, 467, 166, 46, 10, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [182, 312, 283, 175, 79, 27, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [43, 72, 64, 39, 17, 6, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [11, 18, 16, 9, 4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi0_shape : checkShape matGHi0 19 = true := rfl
private theorem matGHi0_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matM1Hi eAB_ei_hi eAB_ii_hi eAC_ie_hi eAeHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi0.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi0_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 0 b c ≤ (matAt matGHi0 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matM1Hi_shape).1
    (checkShape_spec eAB_ei_hi_shape).1 rfl (checkShape_getD matGHi0_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ie_hi_shape).1
    (fun c => checkShape_getD eAC_ie_hi_shape c)
    (fun a => ar2InitMat_nonneg (by norm_num) (by norm_num) gw19_nn a b)
    wi19_nn le_k2_hi (fun a => matM1Hi_ge a b)
    eAeHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ei_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ei_hi_col_ge (matGHi0_chk b) c

/-- Upper bound for `ar2PrefixMat 1` -/
private def matGHi1 : List (List ℕ) := [
  [1917112758, 4351055299, 6480322325, 8041446241, 8758217164, 8467383620, 7257317613, 5493626681,
    3668530519, 2170519226, 1150790292, 556988390, 252279273, 110059089, 47619894, 20929847,
    9418726, 4182833, 1459440],
  [4103955587, 9272050019, 13698620454, 16806244589, 18042087037, 17146994528, 14414561506,
    10683220657, 6976190443, 4033559654, 2089752242, 988907534, 438426254, 187536710, 79737180,
    34531772, 15359054, 6764519, 2349180],
  [5436249901, 12183213966, 17743389999, 21332368232, 22321059775, 20577993715, 16713279460,
    11930100139, 7486777129, 4155252472, 2066307029, 939443830, 400965754, 165618338, 68267202,
    28798790, 12545900, 5444699, 1875165],
  [5549124219, 12294489964, 17545275603, 20497638060, 20682106100, 18262722808, 14126821413,
    9561407835, 5671958793, 2970921488, 1394093133, 598930052, 242254023, 95234680, 37571059,
    15272349, 6460800, 2746072, 934695],
  [4484968029, 9792901552, 13618512177, 15339808968, 14778481859, 12353634667, 8981394835,
    5681354870, 3137665905, 1526939942, 665613112, 266122707, 100541765, 37120397, 13851703,
    5371751, 2189398, 906306, 303916],
  [2824634494, 6061342197, 8173519591, 8814942353, 8037481663, 6294311359, 4250609630, 2480967839,
    1258467156, 561151646, 224101709, 82262653, 28659390, 9821042, 3430426, 1258031, 490570,
    196801, 64836],
  [1349498257, 2839260577, 3696974324, 3794987412, 3250551743, 2363804029, 1468043738, 782099296,
    360232519, 145462330, 52600551, 17526298, 5570084, 1754156, 568518, 195703, 72588, 28104,
    9075],
  [477903462, 983983661, 1233084415, 1199184130, 959226927, 643249394, 364522079, 175750521,
    72847734, 26394515, 8563178, 2566804, 737897, 211907, 63288, 20332, 7140, 2660, 841],
  [124193389, 249915198, 300715211, 276160461, 205446184, 126429656, 65017912, 28201677, 10453854,
    3376936, 976678, 261741, 67664, 17625, 4828, 1442, 478, 171, 53],
  [23907616, 46986240, 54218765, 46936130, 32403005, 18251481, 8492799, 3303584, 1091499, 313287,
    80503, 19225, 4456, 1050, 264, 73, 23, 8, 3],
  [3521844, 6759442, 7479055, 6102030, 3908353, 2014441, 847916, 295701, 87056, 22196, 5066, 1078,
    224, 48, 11, 3, 1, 1, 1],
  [419996, 787649, 836472, 644098, 383423, 181216, 69163, 21681, 5704, 1296, 264, 51, 10, 2, 1, 1,
    1, 1, 1],
  [43826, 80402, 82124, 59857, 33240, 14469, 5033, 1426, 338, 69, 13, 3, 1, 1, 1, 1, 1, 1, 1],
  [4396, 7903, 7788, 5397, 2811, 1135, 363, 94, 21, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [470, 829, 791, 525, 258, 98, 29, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [59, 103, 96, 61, 29, 11, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [10, 17, 15, 10, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi1_shape : checkShape matGHi1 19 = true := rfl
private theorem matGHi1_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi0 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi1.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi1_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 1 b c ≤ (matAt matGHi1 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi0_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi1_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 0 a b)
    wi19_nn le_k2_hi (fun a => matGHi0_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi1_chk b) c

/-- Upper bound for `ar2PrefixMat 2` -/
private def matGHi2 : List (List ℕ) := [
  [718390616, 1631414010, 2432268489, 3022436953, 3297435698, 3194031456, 2743146783, 2080812200,
    1392365627, 825416642, 438425342, 212550939, 96412736, 42114153, 18241096, 8024159, 3613331,
    1605390, 560279],
  [1556408047, 3518394244, 5203265487, 6392312076, 6873656132, 6544738815, 5512668616, 4093899370,
    2678649769, 1551715160, 805356871, 381724215, 169477632, 72583845, 30893411, 13390226, 5959511,
    2625876, 912136],
  [2104974315, 4720008336, 6880549504, 8282861069, 8680209591, 8016379611, 6523013070, 4665101838,
    2933141442, 1630885719, 812376816, 369917743, 158102723, 65382075, 26977278, 11389703, 4964877,
    2155589, 742565],
  [2210408963, 4899748115, 6998376604, 8185645514, 8271171931, 7315461734, 5668578489, 3843483150,
    2284037408, 1198394568, 563239393, 242332132, 98145774, 38626705, 15253193, 6205106, 2626554,
    1116836, 380230],
  [1848743475, 4038528309, 5620562542, 6337736360, 6113783754, 5118185353, 3726947005, 2361402781,
    1306261776, 636688786, 277951421, 111280328, 42093122, 15557439, 5810566, 2255007, 919601,
    380818, 127729],
  [1209835295, 2597204633, 3504681239, 3783326925, 3453676599, 2708232635, 1831510585, 1070583751,
    543853763, 242852324, 97116927, 35693938, 12449337, 4270353, 1492852, 547842, 213743, 85778,
    28266],
  [601951676, 1266915668, 1650653892, 1695850571, 1454068330, 1058649641, 658315694, 351182011,
    161968361, 65487728, 23710090, 7909100, 2516198, 793128, 257249, 88609, 32882, 12735, 4113],
  [222122611, 457483155, 573607881, 558254568, 446957088, 300039523, 170222037, 82167803, 34098693,
    12369174, 4017386, 1205449, 346863, 99693, 29796, 9578, 3365, 1254, 397],
  [60092165, 120956795, 145612838, 133810803, 99627456, 61366617, 31590294, 13716790, 5089975,
    1645945, 476516, 127821, 33072, 8621, 2363, 706, 235, 84, 26],
  [12017740, 23624428, 27272338, 23622831, 16320018, 9200047, 4284811, 1668298, 551728, 158508,
    40767, 9744, 2260, 533, 134, 38, 12, 4, 2],
  [1833819, 3520378, 3896607, 3180810, 2038606, 1051506, 442953, 154605, 45556, 11625, 2656, 566,
    118, 26, 6, 2, 1, 1, 1],
  [225746, 423437, 449834, 346539, 206408, 97618, 37284, 11696, 3080, 700, 143, 28, 6, 1, 1, 1, 1,
    1, 1],
  [24224, 44448, 45414, 33114, 18399, 8014, 2789, 791, 188, 39, 7, 2, 1, 1, 1, 1, 1, 1, 1],
  [2489, 4475, 4411, 3058, 1594, 644, 206, 54, 12, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [271, 479, 457, 303, 150, 57, 17, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [35, 61, 56, 36, 17, 6, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [6, 10, 9, 6, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi2_shape : checkShape matGHi2 19 = true := rfl
private theorem matGHi2_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi1 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi2.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi2_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 2 b c ≤ (matAt matGHi2 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi1_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi2_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 1 a b)
    wi19_nn le_k2_hi (fun a => matGHi1_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi2_chk b) c

/-- Upper bound for `ar2PrefixMat 3` -/
private def matGHi3 : List (List ℕ) := [
  [287460926, 652511647, 972066982, 1206626878, 1314663643, 1271499222, 1090201360, 825542731,
    551444420, 326345947, 173057645, 83771701, 37946267, 16555163, 7163152, 3148345, 1416789,
    629186, 219529],
  [621970566, 1405414771, 2076873849, 2548835662, 2737267198, 2602474828, 2188594528, 1622628740,
    1059911074, 612986645, 317647169, 150338734, 66658693, 28515117, 12124557, 5250871, 2335496,
    1028612, 357216],
  [839365560, 1881367667, 2740632018, 3296012586, 3450027060, 3181845721, 2585268616, 1846062399,
    1158881941, 643373860, 320007899, 145517464, 62117011, 25659843, 10577585, 4462387, 1944044,
    843693, 290572],
  [879004324, 1947759306, 2780254252, 3249084323, 3279502648, 2896991778, 2241800344, 1517884015,
    900743218, 471946651, 221517369, 95188941, 38508530, 15140481, 5973681, 2428434, 1027375,
    436685, 148640],
  [733004005, 1600716669, 2226532678, 2508700429, 2417754614, 2021831960, 1470506506, 930560603,
    514113772, 250276408, 109131001, 43643371, 16492057, 6089979, 2272823, 881502, 359307, 148743,
    49881],
  [478290524, 1026483652, 1384474593, 1493553116, 1362295077, 1067247999, 721010552, 421002247,
    213634448, 95293703, 38068778, 13978150, 4871020, 1669550, 583260, 213926, 83429, 33471,
    11028],
  [237345626, 499419210, 650421462, 667850225, 572230440, 416281862, 258634433, 137842309,
    63514467, 25656671, 9280843, 3093284, 983349, 309752, 100409, 34570, 12824, 4966, 1604],
  [87385274, 179942676, 225539604, 219396813, 175551582, 117765818, 66762197, 32201348, 13352481,
    4839730, 1570700, 470965, 135430, 38902, 11621, 3734, 1312, 489, 155],
  [23598186, 47491728, 57155672, 52501697, 39069839, 24051478, 12373319, 5369001, 1990947, 643377,
    186142, 49901, 12904, 3362, 922, 276, 92, 33, 11],
  [4712811, 9263103, 10690766, 9256942, 6392480, 3601831, 1676596, 652411, 215635, 61915, 15915,
    3802, 882, 208, 53, 15, 5, 2, 1],
  [718403, 1378948, 1525991, 1245300, 797828, 411342, 173199, 60422, 17795, 4539, 1037, 221, 46,
    10, 3, 1, 1, 1, 1],
  [88372, 165744, 176044, 135584, 80732, 38167, 14572, 4570, 1203, 274, 56, 11, 2, 1, 1, 1, 1, 1,
    1],
  [9478, 17390, 17765, 12951, 7194, 3132, 1090, 309, 74, 15, 3, 1, 1, 1, 1, 1, 1, 1, 1],
  [974, 1751, 1725, 1196, 623, 252, 81, 21, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [106, 188, 179, 119, 59, 23, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [14, 24, 22, 14, 7, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 4, 4, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi3_shape : checkShape matGHi3 19 = true := rfl
private theorem matGHi3_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi2 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi3.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi3_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 3 b c ≤ (matAt matGHi3 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi2_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi3_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 2 a b)
    wi19_nn le_k2_hi (fun a => matGHi2_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi3_chk b) c

/-- Upper bound for `ar2PrefixMat 4` -/
private def matGHi4 : List (List ℕ) := [
  [114301714, 259464915, 386558644, 479879440, 522905482, 505803109, 433744796, 328497752,
    219462794, 129898100, 68893492, 33353665, 15110156, 6592968, 2852939, 1254019, 564356, 250637,
    87452],
  [247260090, 558733081, 825728868, 1013461531, 1088503199, 1035030732, 870545080, 645516501,
    421716723, 243929748, 126420832, 59841247, 26536137, 11352760, 4827598, 2090878, 930039,
    409629, 142259],
  [333557036, 747664982, 1089204257, 1310033621, 1371384773, 1264927714, 1027890090, 734081936,
    460888021, 255903917, 127300255, 57894226, 24715975, 10210875, 4209508, 1775994, 773755,
    335813, 115658],
  [349112214, 773610031, 1104316846, 1290628291, 1302826335, 1150985737, 890774705, 603198482,
    357992712, 187593144, 88060417, 37844718, 15311494, 6020568, 2375591, 965789, 408607, 173684,
    59120],
  [290906863, 635291515, 883704125, 995756738, 959731202, 802639228, 583826454, 369492049,
    204156882, 99395909, 43344987, 17335986, 6551507, 2419437, 903008, 350246, 142769, 59104,
    19821],
  [189642065, 407009084, 548975700, 592258195, 540243001, 423267627, 285973686, 166995750,
    84748005, 37805866, 15104256, 5546428, 1932921, 662553, 231477, 84904, 33113, 13285, 4377],
  [94004889, 197807134, 257623051, 264537453, 226673954, 164908930, 102464055, 54613216, 25166248,
    10166615, 3677839, 1225893, 389732, 122771, 39799, 13703, 5084, 1969, 636],
  [34568442, 71183900, 89223863, 86796704, 69453782, 46594154, 26415928, 12741883, 5283800,
    1915271, 621622, 186399, 53603, 15398, 4600, 1478, 520, 194, 62],
  [9323038, 18762973, 22581433, 20743273, 15436903, 9503360, 4889227, 2121617, 786780, 254261,
    73566, 19723, 5101, 1329, 365, 109, 37, 13, 4],
  [1859438, 3654786, 4218141, 3652491, 2522335, 1421249, 661592, 257454, 85097, 24435, 6281, 1501,
    348, 82, 21, 6, 2, 1, 1],
  [283073, 543352, 601299, 490705, 314387, 162095, 68254, 23812, 7013, 1789, 409, 87, 19, 4, 1, 1,
    1, 1, 1],
  [34778, 65227, 69281, 53359, 31772, 15021, 5735, 1799, 474, 108, 22, 5, 1, 1, 1, 1, 1, 1, 1],
  [3726, 6836, 6983, 5091, 2828, 1232, 429, 122, 29, 6, 2, 1, 1, 1, 1, 1, 1, 1, 1],
  [383, 688, 678, 470, 245, 99, 32, 9, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [42, 74, 71, 47, 23, 9, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [6, 10, 9, 6, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi4_shape : checkShape matGHi4 19 = true := rfl
private theorem matGHi4_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi3 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi4.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi4_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 4 b c ≤ (matAt matGHi4 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi3_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi4_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 3 a b)
    wi19_nn le_k2_hi (fun a => matGHi3_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi4_chk b) c

/-- Upper bound for `ar2PrefixMat 5` -/
private def matGHi5 : List (List ℕ) := [
  [45387380, 103030443, 153500669, 190562740, 207655050, 200870494, 172260439, 130467080, 87165934,
    51594760, 27365102, 13248824, 6002279, 2619027, 1133344, 498175, 224201, 99571, 34743],
  [98190079, 221882144, 327916363, 402479193, 432293613, 411071270, 345757126, 256391632,
    167507410, 96893415, 50218488, 23771685, 10541685, 4510090, 1917894, 830673, 369495, 162743,
    56519],
  [132476018, 296946554, 432601203, 520320195, 544702859, 502434952, 408296605, 291601113,
    183086237, 101660555, 50573072, 23000580, 9819592, 4056854, 1672503, 705643, 307434, 133429,
    45955],
  [138676922, 307301698, 438675174, 512695487, 517554205, 457248005, 353885995, 239645854,
    142232268, 74534075, 34989032, 15037263, 6084043, 2392335, 943984, 383780, 162372, 69019,
    23494],
  [115578958, 252406866, 351108027, 395635350, 381330228, 318921052, 231984366, 146822529,
    81126807, 39498568, 17225175, 6889447, 2603677, 961544, 358884, 139201, 56742, 23491, 7878],
  [75362264, 161743278, 218162597, 235366801, 214699894, 168216087, 113655169, 66371197, 33683323,
    15026424, 6003525, 2204602, 768316, 263363, 92013, 33750, 13163, 5281, 1740],
  [37365302, 78625331, 102402273, 105152124, 90103134, 65552752, 40731230, 21710179, 10004465,
    4041675, 1462133, 487366, 154945, 48811, 15824, 5448, 2021, 783, 253],
  [13743497, 28300972, 35473523, 34508946, 27614088, 18525654, 10503063, 5066314, 2100938, 761562,
    247178, 74120, 21316, 6123, 1830, 588, 207, 77, 25],
  [3707422, 7461359, 8979890, 8248998, 6138886, 3779313, 1944387, 843756, 312904, 101122, 29259,
    7844, 2029, 529, 145, 44, 15, 6, 2],
  [739586, 1453686, 1677770, 1452795, 1003281, 565322, 263161, 102409, 33850, 9720, 2499, 597, 139,
    33, 9, 3, 1, 1, 1],
  [112614, 216160, 239215, 195218, 125075, 64488, 27155, 9474, 2791, 712, 163, 35, 8, 2, 1, 1, 1,
    1, 1],
  [13838, 25954, 27567, 21232, 12643, 5977, 2282, 716, 189, 43, 9, 2, 1, 1, 1, 1, 1, 1, 1],
  [1483, 2721, 2779, 2026, 1126, 490, 171, 49, 12, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [153, 274, 270, 187, 98, 40, 13, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [17, 30, 28, 19, 10, 4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 4, 4, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi5_shape : checkShape matGHi5 19 = true := rfl
private theorem matGHi5_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi4 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi5.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi5_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 5 b c ≤ (matAt matGHi5 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi4_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi5_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 4 a b)
    wi19_nn le_k2_hi (fun a => matGHi4_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi5_chk b) c

/-- Upper bound for `ar2PrefixMat 6` -/
private def matGHi6 : List (List ℕ) := [
  [18029633, 40927593, 60975997, 75697907, 82486901, 79791154, 68425805, 51823995, 34623604,
    20493998, 10869611, 5262479, 2384107, 1040271, 450159, 197872, 89051, 39549, 13800],
  [39004838, 88139813, 130259963, 159877981, 171719965, 163288415, 137342622, 101843614, 66536462,
    38487149, 19947161, 9442211, 4187168, 1791400, 761780, 329939, 146761, 64641, 22449],
  [52624375, 117957881, 171844101, 206687943, 216372023, 199580378, 162184748, 115829583, 72724718,
    40380801, 20088063, 9135957, 3900368, 1611383, 664315, 280279, 122112, 52998, 18253],
  [55087501, 122071120, 174256681, 203659034, 205587791, 181631093, 140571855, 95192205, 56497084,
    29605967, 13898021, 5972920, 2416614, 950243, 374952, 152438, 64494, 27415, 9332],
  [45912176, 100265025, 139472207, 157159299, 151476011, 126684389, 92150070, 58321214, 32225162,
    15689496, 6842083, 2736569, 1034205, 381933, 142551, 55291, 22539, 9331, 3129],
  [29936759, 64250485, 86662114, 93495895, 85285881, 66820622, 45147077, 26364372, 13379813,
    5968815, 2384714, 875705, 305187, 104611, 36549, 13406, 5229, 2098, 692],
  [14843041, 31233186, 40678263, 41770480, 35792300, 26039862, 16179799, 8623961, 3974065, 1605463,
    580796, 193594, 61548, 19389, 6286, 2165, 803, 311, 101],
  [5459551, 11242439, 14091676, 13708466, 10969491, 7359150, 4172230, 2012531, 834568, 302519,
    98187, 29443, 8467, 2433, 727, 234, 82, 31, 10],
  [1472782, 2964039, 3567273, 3276918, 2438668, 1501325, 772402, 335178, 124299, 40170, 11623,
    3116, 806, 210, 58, 18, 6, 3, 1],
  [293808, 577490, 666509, 577134, 398561, 224578, 104542, 40683, 13447, 3862, 993, 238, 55, 13, 4,
    1, 1, 1, 1],
  [44738, 85874, 95032, 77554, 49688, 25619, 10788, 3764, 1109, 283, 65, 14, 3, 1, 1, 1, 1, 1, 1],
  [5498, 10311, 10952, 8435, 5023, 2375, 907, 285, 75, 17, 4, 1, 1, 1, 1, 1, 1, 1, 1],
  [590, 1081, 1105, 805, 448, 195, 68, 20, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [61, 109, 108, 75, 39, 16, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [7, 12, 12, 8, 4, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi6_shape : checkShape matGHi6 19 = true := rfl
private theorem matGHi6_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi5 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi6.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi6_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 6 b c ≤ (matAt matGHi6 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi5_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi6_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 5 a b)
    wi19_nn le_k2_hi (fun a => matGHi5_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi6_chk b) c

/-- Upper bound for `ar2PrefixMat 7` -/
private def matGHi7 : List (List ℕ) := [
  [7162049, 16257980, 24221960, 30070054, 32766896, 31696042, 27181297, 20586434, 13753793,
    8140984, 4317817, 2090454, 947057, 413235, 178820, 78602, 35375, 15711, 5482],
  [15494156, 35012373, 51744043, 63509404, 68213470, 64864145, 54557521, 40456012, 26430717,
    15288503, 7923742, 3750792, 1663296, 711610, 302607, 131064, 58299, 25678, 8918],
  [20904256, 46857025, 68262526, 82103722, 85950574, 79280337, 64425474, 46011573, 28888807,
    16040669, 7979682, 3629122, 1549363, 640098, 263889, 111337, 48507, 21053, 7251],
  [21882578, 48490686, 69220513, 80900095, 81666255, 72149859, 55839771, 37813477, 22442500,
    11760463, 5520750, 2372640, 959959, 377468, 148943, 60553, 25619, 10890, 3707],
  [18237712, 39828314, 55402595, 62428441, 60170862, 50322874, 36604795, 23166948, 12800807,
    6232341, 2717882, 1087048, 410818, 151715, 56626, 21964, 8953, 3707, 1243],
  [11891697, 25522043, 34424550, 37139112, 33877868, 26542964, 17933642, 10472642, 5314823,
    2370975, 947273, 347854, 121229, 41555, 14519, 5326, 2077, 834, 275],
  [5896009, 12406564, 16158372, 16592225, 14217549, 10343649, 6426998, 3425641, 1578592, 637728,
    230706, 76900, 24448, 7702, 2497, 860, 319, 124, 40],
  [2168643, 4465722, 5597496, 5445277, 4357301, 2923201, 1657293, 799417, 331507, 120167, 39002,
    11696, 3364, 967, 289, 93, 33, 13, 4],
  [585013, 1177365, 1416979, 1301645, 968679, 596351, 306811, 133139, 49374, 15957, 4617, 1238,
    321, 84, 23, 7, 3, 1, 1],
  [116704, 229387, 264746, 229245, 158314, 89205, 41526, 16160, 5342, 1534, 395, 95, 22, 6, 2, 1,
    1, 1, 1],
  [17771, 34110, 37748, 30805, 19737, 10176, 4285, 1495, 441, 113, 26, 6, 2, 1, 1, 1, 1, 1, 1],
  [2184, 4096, 4350, 3351, 1995, 944, 361, 113, 30, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1],
  [234, 430, 439, 320, 178, 78, 27, 8, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [25, 44, 43, 30, 16, 7, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [3, 5, 5, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi7_shape : checkShape matGHi7 19 = true := rfl
private theorem matGHi7_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi6 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi7.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi7_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 7 b c ≤ (matAt matGHi7 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi6_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi7_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 6 a b)
    wi19_nn le_k2_hi (fun a => matGHi6_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi7_chk b) c

/-- Upper bound for `ar2PrefixMat 8` -/
private def matGHi8 : List (List ℕ) := [
  [2844999, 6458200, 9621754, 11944810, 13016088, 12590713, 10797311, 8177616, 5463466, 3233872,
    1715182, 830399, 376203, 164151, 71034, 31224, 14052, 6241, 2178],
  [6154785, 13908060, 20554429, 25228022, 27096639, 25766184, 21672059, 16070477, 10499166,
    6073108, 3147578, 1489942, 660718, 282676, 120206, 52063, 23159, 10200, 3543],
  [8303858, 18613154, 27116127, 32614313, 34142418, 31492788, 25591950, 18277339, 11475606,
    6371896, 3169800, 1441611, 615460, 254269, 104826, 44227, 19269, 8363, 2881],
  [8692487, 19262112, 27496691, 32136215, 32440567, 28660343, 22181436, 15020789, 8914921, 4671656,
    2193031, 942494, 381329, 149944, 59166, 24054, 10177, 4326, 1473],
  [7244631, 15821143, 22007772, 24798678, 23901897, 19989948, 14540666, 9202700, 5084918, 2475699,
    1079636, 431813, 163191, 60267, 22494, 8725, 3557, 1473, 494],
  [4723785, 10138221, 13674600, 14752918, 13457443, 10543771, 7123857, 4160093, 2111231, 941833,
    376290, 138180, 48157, 16507, 5768, 2116, 825, 331, 110],
  [2342097, 4928312, 6418659, 6591001, 5647699, 4108854, 2553026, 1360783, 627072, 253328, 91645,
    30548, 9712, 3060, 992, 342, 127, 50, 16],
  [861460, 1773939, 2223519, 2163053, 1730871, 1161197, 658335, 317557, 131687, 47735, 15493, 4646,
    1336, 384, 115, 37, 13, 5, 2],
  [232388, 467691, 562874, 517059, 384793, 236892, 121876, 52888, 19613, 6339, 1834, 492, 128, 34,
    10, 3, 1, 1, 1],
  [46359, 91121, 105167, 91065, 62888, 35436, 16496, 6420, 2122, 610, 157, 38, 9, 3, 1, 1, 1, 1,
    1],
  [7059, 13550, 14995, 12237, 7840, 4043, 1703, 594, 175, 45, 11, 3, 1, 1, 1, 1, 1, 1, 1],
  [868, 1627, 1728, 1331, 793, 375, 144, 45, 12, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [93, 171, 175, 127, 71, 31, 11, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [10, 18, 17, 12, 7, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi8_shape : checkShape matGHi8 19 = true := rfl
private theorem matGHi8_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi7 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi8.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi8_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 8 b c ≤ (matAt matGHi8 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi7_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi8_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 7 a b)
    wi19_nn le_k2_hi (fun a => matGHi7_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi8_chk b) c

/-- Upper bound for `ar2PrefixMat 9` -/
private def matGHi9 : List (List ℕ) := [
  [1130129, 2565412, 3822081, 4744876, 5170423, 5001450, 4289051, 3248421, 2170270, 1284601,
    681328, 329862, 149441, 65207, 28217, 12403, 5582, 2479, 865],
  [2444886, 5524745, 8164903, 10021410, 10763686, 10235184, 8608862, 6383727, 4170617, 2412440,
    1250323, 591854, 262459, 112289, 47750, 20682, 9200, 4052, 1408],
  [3298569, 7393764, 10771428, 12955490, 13562504, 12509982, 10165973, 7260366, 4558492, 2531129,
    1259150, 572656, 244481, 101004, 41641, 17569, 7655, 3322, 1145],
  [3452946, 7651553, 10922602, 12765575, 12886473, 11384842, 8811204, 5966757, 3541303, 1855737,
    871145, 374390, 151477, 59563, 23503, 9555, 4043, 1719, 585],
  [2877809, 6284686, 8742222, 9850863, 9494631, 7940674, 5776037, 3655619, 2019899, 983431, 428868,
    171531, 64825, 23940, 8936, 3466, 1413, 585, 197],
  [1876446, 4027241, 5432008, 5860352, 5345746, 4188338, 2829834, 1652528, 838652, 374128, 149475,
    54890, 19130, 6558, 2291, 841, 328, 132, 44],
  [930360, 1957691, 2549707, 2618167, 2243456, 1632175, 1014148, 540549, 249094, 100631, 36405,
    12135, 3858, 1216, 394, 136, 51, 20, 7],
  [342201, 704669, 883257, 859238, 687561, 461267, 261513, 126145, 52311, 18962, 6155, 1846, 531,
    153, 46, 15, 6, 2, 1],
  [92313, 185783, 223593, 205394, 152853, 94102, 48414, 21009, 7791, 2518, 729, 196, 51, 14, 4, 2,
    1, 1, 1],
  [18416, 36197, 41776, 36174, 24982, 14077, 6553, 2550, 843, 243, 63, 15, 4, 1, 1, 1, 1, 1, 1],
  [2805, 5383, 5957, 4861, 3115, 1606, 677, 236, 70, 18, 5, 1, 1, 1, 1, 1, 1, 1, 1],
  [345, 647, 687, 529, 315, 149, 57, 18, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [37, 68, 70, 51, 29, 13, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [4, 7, 7, 5, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi9_shape : checkShape matGHi9 19 = true := rfl
private theorem matGHi9_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi8 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi9.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi9_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 9 b c ≤ (matAt matGHi9 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi8_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi9_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 8 a b)
    wi19_nn le_k2_hi (fun a => matGHi8_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi9_chk b) c

/-- Upper bound for `ar2PrefixMat 10` -/
private def matGHi10 : List (List ℕ) := [
  [448926, 1019068, 1518260, 1884825, 2053866, 1986744, 1703755, 1290382, 862104, 510287, 270646,
    131033, 59363, 25903, 11209, 4927, 2218, 985, 344],
  [971191, 2194614, 3243373, 3980839, 4275696, 4065758, 3419728, 2535830, 1656709, 958302, 496670,
    235105, 104258, 44605, 18968, 8216, 3655, 1610, 559],
  [1310302, 2937050, 4278771, 5146354, 5387480, 4969383, 4038264, 2884060, 1810785, 1005449,
    500177, 227478, 97116, 40123, 16541, 6979, 3041, 1320, 455],
  [1371626, 3039452, 4338822, 5070913, 5118937, 4522439, 3500104, 2370195, 1406724, 737161, 346048,
    148721, 60172, 23661, 9336, 3796, 1606, 683, 233],
  [1143162, 2496487, 3472702, 3913091, 3771584, 3154301, 2294435, 1452134, 802371, 390652, 170361,
    68138, 25751, 9510, 3550, 1377, 562, 233, 78],
  [745387, 1599755, 2157775, 2327928, 2123509, 1663748, 1124105, 656439, 333141, 148616, 59377,
    21804, 7599, 2605, 911, 334, 131, 53, 18],
  [369570, 777660, 1012829, 1040023, 891176, 648354, 402853, 214724, 98949, 39974, 14461, 4821,
    1533, 483, 157, 54, 20, 8, 3],
  [135934, 279918, 350859, 341318, 273122, 183231, 103882, 50109, 20780, 7533, 2445, 734, 211, 61,
    19, 6, 3, 1, 1],
  [36670, 73799, 88819, 81590, 60719, 37381, 19232, 8346, 3095, 1001, 290, 78, 21, 6, 2, 1, 1, 1,
    1],
  [7316, 14379, 16595, 14370, 9924, 5592, 2603, 1013, 335, 97, 25, 6, 2, 1, 1, 1, 1, 1, 1],
  [1114, 2139, 2367, 1931, 1238, 638, 269, 94, 28, 8, 2, 1, 1, 1, 1, 1, 1, 1, 1],
  [137, 257, 273, 211, 126, 60, 23, 8, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [15, 27, 28, 21, 12, 5, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [2, 3, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]
private theorem matGHi10_shape : checkShape matGHi10 19 = true := rfl
private theorem matGHi10_chk :
    ∀ b : Fin 19, checkStepAtUp certS k2Hi matGHi9 eAB_ii_hi eAB_ii_hi eAC_ii_hi eAiHi19
    eAiHi19 wiHi19 eAiHi19 (matGHi10.getD b.1 []) b.1 = true :=
  fin19_all rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
private theorem matGHi10_ge (b c : Fin 19) :
    ar2PrefixMat (17 / 10) (21 / 20) r19 10 b c ≤ (matAt matGHi10 b.1 c.1 : ℝ) / certS :=
  checkStepAtUp_sound (by decide) b (checkShape_spec matGHi9_shape).1
    (checkShape_spec eAB_ii_hi_shape).1 rfl (checkShape_getD matGHi10_shape b)
    rfl rfl (checkShape_getD eAB_ii_hi_shape b) (checkShape_spec eAC_ii_hi_shape).1
    (fun c => checkShape_getD eAC_ii_hi_shape c)
    (fun a => ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 9 a b)
    wi19_nn le_k2_hi (fun a => matGHi9_ge a b)
    eAiHi_ge (eAiHi_ge b) eAiHi_ge (fun c => (wi_bounds c).2)
    (fun a => eAB_ii_hi_ge a b) (fun c => eAB_ii_hi_ge b c)
    eAC_ii_hi_col_ge (matGHi10_chk b) c

private theorem qHi_3_eq : Nat.div (Nat.add (frobDotNat matGHi0 matRHi) (Nat.sub certS 1))
    certS = 618784751781 := rfl
private theorem qHi_3_ge : (2 : ℝ) ^ (3 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 3 ≤
    (618784751781 : ℝ) / certS := by
  change (2 : ℝ) ^ (0 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (0 + 3) ≤ _
  have hqR : ((Nat.div (Nat.add (frobDotNat matGHi0 matRHi) (Nat.sub certS 1)) certS : ℕ) : ℝ) =
      (618784751781 : ℝ) := by exact_mod_cast qHi_3_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGHi0_shape
  have hR := checkShape_spec matRHi_shape
  exact le_frobDotUp (by decide) hG.1 hR.1 hG.2 hR.2
    (ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 0)
    (ar2ReadoutMat_nonneg (by norm_num) gw19_nn) matGHi0_ge matRHi_ge
private theorem qLo_4_eq : Nat.div (frobDotNat matGLo1 matRLo) certS = 246655281050 := rfl
private theorem qLo_4_le : (246655281050 : ℝ) / certS ≤
    (2 : ℝ) ^ (4 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 4 := by
  change _ ≤ (2 : ℝ) ^ (1 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (1 + 3)
  have hqR : ((Nat.div (frobDotNat matGLo1 matRLo) certS : ℕ) : ℝ) =
      (246655281050 : ℝ) := by exact_mod_cast qLo_4_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGLo1_shape
  have hR := checkShape_spec matRLo_shape
  exact frobDotDn_le (by decide) hG.1 hR.1 hG.2 hR.2 matGLo1_le matRLo_le
private theorem qHi_5_eq : Nat.div (Nat.add (frobDotNat matGHi2 matRHi) (Nat.sub certS 1))
    certS = 97791993958 := rfl
private theorem qHi_5_ge : (2 : ℝ) ^ (5 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 5 ≤
    (97791993958 : ℝ) / certS := by
  change (2 : ℝ) ^ (2 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (2 + 3) ≤ _
  have hqR : ((Nat.div (Nat.add (frobDotNat matGHi2 matRHi) (Nat.sub certS 1)) certS : ℕ) : ℝ) =
      (97791993958 : ℝ) := by exact_mod_cast qHi_5_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGHi2_shape
  have hR := checkShape_spec matRHi_shape
  exact le_frobDotUp (by decide) hG.1 hR.1 hG.2 hR.2
    (ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 2)
    (ar2ReadoutMat_nonneg (by norm_num) gw19_nn) matGHi2_ge matRHi_ge
private theorem qLo_6_eq : Nat.div (frobDotNat matGLo3 matRLo) certS = 38851061810 := rfl
private theorem qLo_6_le : (38851061810 : ℝ) / certS ≤
    (2 : ℝ) ^ (6 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 6 := by
  change _ ≤ (2 : ℝ) ^ (3 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (3 + 3)
  have hqR : ((Nat.div (frobDotNat matGLo3 matRLo) certS : ℕ) : ℝ) =
      (38851061810 : ℝ) := by exact_mod_cast qLo_6_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGLo3_shape
  have hR := checkShape_spec matRLo_shape
  exact frobDotDn_le (by decide) hG.1 hR.1 hG.2 hR.2 matGLo3_le matRLo_le
private theorem qHi_7_eq : Nat.div (Nat.add (frobDotNat matGHi4 matRHi) (Nat.sub certS 1))
    certS = 15433694534 := rfl
private theorem qHi_7_ge : (2 : ℝ) ^ (7 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 7 ≤
    (15433694534 : ℝ) / certS := by
  change (2 : ℝ) ^ (4 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (4 + 3) ≤ _
  have hqR : ((Nat.div (Nat.add (frobDotNat matGHi4 matRHi) (Nat.sub certS 1)) certS : ℕ) : ℝ) =
      (15433694534 : ℝ) := by exact_mod_cast qHi_7_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGHi4_shape
  have hR := checkShape_spec matRHi_shape
  exact le_frobDotUp (by decide) hG.1 hR.1 hG.2 hR.2
    (ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 4)
    (ar2ReadoutMat_nonneg (by norm_num) gw19_nn) matGHi4_ge matRHi_ge
private theorem qLo_8_eq : Nat.div (frobDotNat matGLo5 matRLo) certS = 6130712127 := rfl
private theorem qLo_8_le : (6130712127 : ℝ) / certS ≤
    (2 : ℝ) ^ (8 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 8 := by
  change _ ≤ (2 : ℝ) ^ (5 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (5 + 3)
  have hqR : ((Nat.div (frobDotNat matGLo5 matRLo) certS : ℕ) : ℝ) =
      (6130712127 : ℝ) := by exact_mod_cast qLo_8_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGLo5_shape
  have hR := checkShape_spec matRLo_shape
  exact frobDotDn_le (by decide) hG.1 hR.1 hG.2 hR.2 matGLo5_le matRLo_le
private theorem qHi_9_eq : Nat.div (Nat.add (frobDotNat matGHi6 matRHi) (Nat.sub certS 1))
    certS = 2435321952 := rfl
private theorem qHi_9_ge : (2 : ℝ) ^ (9 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 9 ≤
    (2435321952 : ℝ) / certS := by
  change (2 : ℝ) ^ (6 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (6 + 3) ≤ _
  have hqR : ((Nat.div (Nat.add (frobDotNat matGHi6 matRHi) (Nat.sub certS 1)) certS : ℕ) : ℝ) =
      (2435321952 : ℝ) := by exact_mod_cast qHi_9_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGHi6_shape
  have hR := checkShape_spec matRHi_shape
  exact le_frobDotUp (by decide) hG.1 hR.1 hG.2 hR.2
    (ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 6)
    (ar2ReadoutMat_nonneg (by norm_num) gw19_nn) matGHi6_ge matRHi_ge
private theorem qLo_10_eq : Nat.div (frobDotNat matGLo7 matRLo) certS = 967391174 := rfl
private theorem qLo_10_le : (967391174 : ℝ) / certS ≤
    (2 : ℝ) ^ (10 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 10 := by
  change _ ≤ (2 : ℝ) ^ (7 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (7 + 3)
  have hqR : ((Nat.div (frobDotNat matGLo7 matRLo) certS : ℕ) : ℝ) =
      (967391174 : ℝ) := by exact_mod_cast qLo_10_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGLo7_shape
  have hR := checkShape_spec matRLo_shape
  exact frobDotDn_le (by decide) hG.1 hR.1 hG.2 hR.2 matGLo7_le matRLo_le
private theorem qHi_11_eq : Nat.div (Nat.add (frobDotNat matGHi8 matRHi) (Nat.sub certS 1))
    certS = 384280000 := rfl
private theorem qHi_11_ge : (2 : ℝ) ^ (11 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 11 ≤
    (384280000 : ℝ) / certS := by
  change (2 : ℝ) ^ (8 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (8 + 3) ≤ _
  have hqR : ((Nat.div (Nat.add (frobDotNat matGHi8 matRHi) (Nat.sub certS 1)) certS : ℕ) : ℝ) =
      (384280000 : ℝ) := by exact_mod_cast qHi_11_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGHi8_shape
  have hR := checkShape_spec matRHi_shape
  exact le_frobDotUp (by decide) hG.1 hR.1 hG.2 hR.2
    (ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 8)
    (ar2ReadoutMat_nonneg (by norm_num) gw19_nn) matGHi8_ge matRHi_ge
private theorem qLo_12_eq : Nat.div (frobDotNat matGLo9 matRLo) certS = 152648722 := rfl
private theorem qLo_12_le : (152648722 : ℝ) / certS ≤
    (2 : ℝ) ^ (12 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 12 := by
  change _ ≤ (2 : ℝ) ^ (9 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (9 + 3)
  have hqR : ((Nat.div (frobDotNat matGLo9 matRLo) certS : ℕ) : ℝ) =
      (152648722 : ℝ) := by exact_mod_cast qLo_12_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGLo9_shape
  have hR := checkShape_spec matRLo_shape
  exact frobDotDn_le (by decide) hG.1 hR.1 hG.2 hR.2 matGLo9_le matRLo_le
private theorem qHi_13_eq : Nat.div (Nat.add (frobDotNat matGHi10 matRHi) (Nat.sub certS 1))
    certS = 60637223 := rfl
private theorem qHi_13_ge : (2 : ℝ) ^ (13 - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 13 ≤
    (60637223 : ℝ) / certS := by
  change (2 : ℝ) ^ (10 + 2) * ar2TensorQuad (17 / 10) (21 / 20) r19 (10 + 3) ≤ _
  have hqR : ((Nat.div (Nat.add (frobDotNat matGHi10 matRHi) (Nat.sub certS 1)) certS : ℕ) : ℝ) =
      (60637223 : ℝ) := by exact_mod_cast qHi_13_eq
  rw [ar2TensorQuad_ge_three_eq, ← hqR]
  have hG := checkShape_spec matGHi10_shape
  have hR := checkShape_spec matRHi_shape
  exact le_frobDotUp (by decide) hG.1 hR.1 hG.2 hR.2
    (ar2PrefixMat_nonneg (by norm_num) (by norm_num) gw19_nn 10)
    (ar2ReadoutMat_nonneg (by norm_num) gw19_nn) matGHi10_ge matRHi_ge

private theorem exp_pair_tail_le : Real.exp (-(9 / 2) * (17 / 10 : ℝ) ^ 2) ≤
    (2249055967033 : ℝ) / certT := by
  have hchk : fpSqIterUp certT 6 (expStepHiSum certT 203203125000000000 certM) =
      2249055967033 := rfl
  have hT : 0 < certT := by decide
  have hpow : Real.exp (-(203203125000000000 : ℝ) / certT) ^ (2 ^ 6) =
      Real.exp (-(64 * ((203203125000000000 : ℝ) / certT))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc Real.exp (-(9 / 2) * (17 / 10 : ℝ) ^ 2)
      ≤ Real.exp (-(64 * ((203203125000000000 : ℝ) / certT))) := by
          apply Real.exp_le_exp.mpr; norm_num [certT]
    _ = Real.exp (-(203203125000000000 : ℝ) / certT) ^ (2 ^ 6) := hpow.symm
    _ ≤ (fpSqIterUp certT 6 (expStepHiSum certT 203203125000000000 certM) : ℝ) / certT :=
          pow_le_fpSqIterUp hT 6 (Real.exp_pos _).le
            (by
              have hl := le_expStepHiSum (T := certT) (u := 203203125000000000) (m := certM) hT
              simpa [neg_div] using hl)
    _ = (2249055967033 : ℝ) / certT := by
          have hchkR :
              ((fpSqIterUp certT 6 (expStepHiSum certT 203203125000000000 certM) : ℕ) : ℝ) =
              (2249055967033 : ℝ) := by exact_mod_cast hchk
          rw [hchkR]

private theorem exp_end_tail_le : Real.exp (-6 * (17 / 10 : ℝ) ^ 2) ≤
    (29466848064 : ℝ) / certT := by
  have hchk : fpSqIterUp certT 6 (expStepHiSum certT 270937500000000000 certM) = 29466848064 := rfl
  have hT : 0 < certT := by decide
  have hpow : Real.exp (-(270937500000000000 : ℝ) / certT) ^ (2 ^ 6) =
      Real.exp (-(64 * ((270937500000000000 : ℝ) / certT))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc Real.exp (-6 * (17 / 10 : ℝ) ^ 2)
      ≤ Real.exp (-(64 * ((270937500000000000 : ℝ) / certT))) := by
          apply Real.exp_le_exp.mpr; norm_num [certT]
    _ = Real.exp (-(270937500000000000 : ℝ) / certT) ^ (2 ^ 6) := hpow.symm
    _ ≤ (fpSqIterUp certT 6 (expStepHiSum certT 270937500000000000 certM) : ℝ) / certT :=
          pow_le_fpSqIterUp hT 6 (Real.exp_pos _).le
            (by
              have hl := le_expStepHiSum (T := certT) (u := 270937500000000000) (m := certM) hT
              simpa [neg_div] using hl)
    _ = (29466848064 : ℝ) / certT := by
          have hchkR :
              ((fpSqIterUp certT 6 (expStepHiSum certT 270937500000000000 certM) : ℕ) : ℝ) =
              (29466848064 : ℝ) := by exact_mod_cast hchk
          rw [hchkR]

private theorem exp_int_tail_le : Real.exp (-(33 / 2) * (21 / 20 : ℝ) ^ 2) ≤
    (12578837482 : ℝ) / certT := by
  have hchk : fpSqIterUp certT 6 (expStepHiSum certT 284238281250000000 certM) = 12578837482 := rfl
  have hT : 0 < certT := by decide
  have hpow : Real.exp (-(284238281250000000 : ℝ) / certT) ^ (2 ^ 6) =
      Real.exp (-(64 * ((284238281250000000 : ℝ) / certT))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc Real.exp (-(33 / 2) * (21 / 20 : ℝ) ^ 2)
      ≤ Real.exp (-(64 * ((284238281250000000 : ℝ) / certT))) := by
          apply Real.exp_le_exp.mpr; norm_num [certT]
    _ = Real.exp (-(284238281250000000 : ℝ) / certT) ^ (2 ^ 6) := hpow.symm
    _ ≤ (fpSqIterUp certT 6 (expStepHiSum certT 284238281250000000 certM) : ℝ) / certT :=
          pow_le_fpSqIterUp hT 6 (Real.exp_pos _).le
            (by
              have hl := le_expStepHiSum (T := certT) (u := 284238281250000000) (m := certM) hT
              simpa [neg_div] using hl)
    _ = (12578837482 : ℝ) / certT := by
          have hchkR :
              ((fpSqIterUp certT 6 (expStepHiSum certT 284238281250000000 certM) : ℕ) : ℝ) =
              (12578837482 : ℝ) := by exact_mod_cast hchk
          rw [hchkR]

private theorem certPairTail_le : ar2PairTail (17 / 10) ≤ (4866 : ℝ) / 10 ^ 12 := by
  unfold ar2PairTail
  have h1 := le_c2_hi; have h2 := exp_pair_tail_le; have h3 := s2_lo_le
  have hs2 : (0 : ℝ) < (s2Lo : ℝ) / certT := by norm_num [s2Lo, certT]
  calc (3 / (2 * Real.pi)) *
        (Real.exp (-(9 / 2) * (17 / 10 : ℝ) ^ 2) / (9 * (17 / 10))) *
        (1 / (6 * Real.sqrt 2 * (17 / 10)))
      ≤ ((c2Hi : ℝ) / certS) * (((2249055967033 : ℝ) / certT) / (9 * (17 / 10))) *
          (1 / (6 * ((s2Lo : ℝ) / certT) * (17 / 10))) := by gcongr
    _ ≤ (4866 : ℝ) / 10 ^ 12 := by norm_num [c2Hi, s2Lo, certS, certT]

private theorem certEndTail_le : ar2EndTail (17 / 10) ≤ (4 : ℝ) / 10 ^ 12 := by
  unfold ar2EndTail
  have h1 := le_c2_hi; have h2 := exp_end_tail_le; have h3 := s2_lo_le
  have h4 : Real.sqrt (6 / Real.pi) ≤ (k2Hi : ℝ) / (2 * certS) := by
    have h := le_k2_hi
    rw [show (k2Hi : ℝ) / (2 * certS) = ((k2Hi : ℝ) / certS) / 2 by ring]
    linarith
  have hs2 : (0 : ℝ) < (s2Lo : ℝ) / certT := by norm_num [s2Lo, certT]
  calc (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi) *
        (Real.exp (-6 * (17 / 10 : ℝ) ^ 2) / (12 * (17 / 10))) *
        (1 / (12 * Real.sqrt 2 * (17 / 10))) * (1 / (6 * (17 / 10)))
      ≤ ((c2Hi : ℝ) / certS) * ((k2Hi : ℝ) / (2 * certS)) *
          (((29466848064 : ℝ) / certT) / (12 * (17 / 10))) *
          (1 / (12 * ((s2Lo : ℝ) / certT) * (17 / 10))) * (1 / (6 * (17 / 10))) := by
          gcongr
    _ ≤ (4 : ℝ) / 10 ^ 12 := by norm_num [c2Hi, k2Hi, s2Lo, certS, certT]

private theorem certIntTail_le : ar2IntTail (21 / 20) ≤ (1 : ℝ) / 10 ^ 12 := by
  unfold ar2IntTail
  have h1 := le_c2_hi; have h2 := exp_int_tail_le; have h3 := s2_lo_le
  have h4 : Real.sqrt (6 / Real.pi) ≤ (k2Hi : ℝ) / (2 * certS) := by
    have h := le_k2_hi
    rw [show (k2Hi : ℝ) / (2 * certS) = ((k2Hi : ℝ) / certS) / 2 by ring]
    linarith
  have hs2 : (0 : ℝ) < (s2Lo : ℝ) / certT := by norm_num [s2Lo, certT]
  calc (3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi) *
        (Real.exp (-(33 / 2) * (21 / 20 : ℝ) ^ 2) / (33 * (21 / 20))) *
        (1 / (12 * Real.sqrt 2 * (21 / 20))) ^ 2
      ≤ ((c2Hi : ℝ) / certS) * ((k2Hi : ℝ) / (2 * certS)) *
          (((12578837482 : ℝ) / certT) / (33 * (21 / 20))) *
          (1 / (12 * ((s2Lo : ℝ) / certT) * (21 / 20))) ^ 2 := by gcongr
    _ ≤ (1 : ℝ) / 10 ^ 12 := by norm_num [c2Hi, k2Hi, s2Lo, certS, certT]

private theorem fac19_eq : Nat.factorial 19 = 121645100408832000 := by
  rw [factorial_eq_facRec]; rfl
private theorem fac38_eq : Nat.factorial 38 = 523022617466601111760007224100074291200000000 := by
  rw [factorial_eq_facRec]; rfl
private theorem k2_coarse_le : 2 * Real.sqrt (6 / Real.pi) ≤ 2764 / 1000 := by
  refine le_k2_hi.trans ?_; norm_num [k2Hi, certS]
private theorem c2_coarse_le : 3 / (2 * Real.pi) ≤ 478 / 1000 := by
  refine le_c2_hi.trans ?_; norm_num [c2Hi, certS]
private theorem q_end_fac_le :
    ((Nat.factorial 19 : ℝ) ^ 3 / (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
      (12 * (17 / 10 : ℝ) ^ 2) ^ 19 ≤ (59 : ℝ) / 10 ^ 18 := by
  rw [fac19_eq, fac38_eq]
  norm_num
private theorem q_int_fac_le :
    ((Nat.factorial 19 : ℝ) ^ 3 / (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
      (39 * (21 / 20 : ℝ) ^ 2) ^ 19 ≤ (3492 : ℝ) / 10 ^ 18 := by
  rw [fac19_eq, fac38_eq]
  norm_num

private theorem ar2QuadErr_term_le (j : ℕ) :
    3 * (2 : ℝ) ^ (j - 1) * ar2QuadErr 19 (17 / 10) (21 / 20) j ≤
      3 * (478 / 1000 : ℝ) * (2764 / 1000 : ℝ) ^ (j - 1) *
        (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
        (2 * (59 : ℝ) / 10 ^ 18 + ((j - 1 : ℕ) : ℝ) * (3492 : ℝ) / 10 ^ 18) := by
  unfold ar2QuadErr
  have hpow : (2 : ℝ) ^ (j - 1) * Real.sqrt (6 / Real.pi) ^ (j - 1) =
      (2 * Real.sqrt (6 / Real.pi)) ^ (j - 1) := by rw [← mul_pow]
  have hrew : 3 * (2 : ℝ) ^ (j - 1) *
      ((3 / (2 * Real.pi)) * Real.sqrt (6 / Real.pi) ^ (j - 1) *
        (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
        ((Nat.factorial 19 : ℝ) ^ 3 /
          (2 ^ 19 * (2 * (19 : ℕ) + 1 : ℝ) * (Nat.factorial (2 * 19) : ℝ) ^ 2)) *
        (2 * (12 * (17 / 10 : ℝ) ^ 2) ^ 19 +
          ((j - 1 : ℕ) : ℝ) * (39 * (21 / 20 : ℝ) ^ 2) ^ 19)) =
      3 * (3 / (2 * Real.pi)) * (2 * Real.sqrt (6 / Real.pi)) ^ (j - 1) *
        (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
        (2 * (((Nat.factorial 19 : ℝ) ^ 3 / (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
            (12 * (17 / 10 : ℝ) ^ 2) ^ 19) +
          ((j - 1 : ℕ) : ℝ) * (((Nat.factorial 19 : ℝ) ^ 3 /
            (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
            (39 * (21 / 20 : ℝ) ^ 2) ^ 19)) := by
    rw [show 2 * 19 = 38 by rfl, show (2 * (19 : ℕ) + 1 : ℝ) = 39 by norm_num]
    have h := hpow; linear_combination
      3 * (3 / (2 * Real.pi)) * (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
        ((Nat.factorial 19 : ℝ) ^ 3 / (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
        (2 * (12 * (17 / 10 : ℝ) ^ 2) ^ 19 +
          ((j - 1 : ℕ) : ℝ) * (39 * (21 / 20 : ℝ) ^ 2) ^ 19) * h
  rw [hrew]
  have hc := c2_coarse_le; have hk := k2_coarse_le
  have he := q_end_fac_le; have hi := q_int_fac_le
  have hA : 3 * (3 / (2 * Real.pi)) * (2 * Real.sqrt (6 / Real.pi)) ^ (j - 1) *
        (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) ≤
      3 * (478 / 1000 : ℝ) * (2764 / 1000 : ℝ) ^ (j - 1) *
        (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) := by
    gcongr
  have hB : 2 * (((Nat.factorial 19 : ℝ) ^ 3 / (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
        (12 * (17 / 10 : ℝ) ^ 2) ^ 19) +
      ((j - 1 : ℕ) : ℝ) * (((Nat.factorial 19 : ℝ) ^ 3 /
        (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
        (39 * (21 / 20 : ℝ) ^ 2) ^ 19) ≤
      2 * (59 : ℝ) / 10 ^ 18 + ((j - 1 : ℕ) : ℝ) * (3492 : ℝ) / 10 ^ 18 := by
    have h1 : 2 * (((Nat.factorial 19 : ℝ) ^ 3 / (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
        (12 * (17 / 10 : ℝ) ^ 2) ^ 19) ≤ 2 * (59 : ℝ) / 10 ^ 18 := by linarith
    have h2 : ((j - 1 : ℕ) : ℝ) * (((Nat.factorial 19 : ℝ) ^ 3 /
        (2 ^ 19 * 39 * (Nat.factorial 38 : ℝ) ^ 2)) *
        (39 * (21 / 20 : ℝ) ^ 2) ^ 19) ≤ ((j - 1 : ℕ) : ℝ) * ((3492 : ℝ) / 10 ^ 18) :=
      mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)
    linarith
  exact mul_le_mul hA hB (by positivity) (by positivity)

private noncomputable def certQLo (j : ℕ) : ℝ :=
  match j with
  | 2 => (1495869861753 : ℝ) / certS
  | 4 => (246655281050 : ℝ) / certS
  | 6 => (38851061810 : ℝ) / certS
  | 8 => (6130712127 : ℝ) / certS
  | 10 => (967391174 : ℝ) / certS
  | 12 => (152648722 : ℝ) / certS
  | _ => 0

private noncomputable def certQHi (j : ℕ) : ℝ :=
  match j with
  | 1 => (5408671524016 : ℝ) / certS
  | 3 => (618784751781 : ℝ) / certS
  | 5 => (97791993958 : ℝ) / certS
  | 7 => (15433694534 : ℝ) / certS
  | 9 => (2435321952 : ℝ) / certS
  | 11 => (384280000 : ℝ) / certS
  | 13 => (60637223 : ℝ) / certS
  | _ => 0

private theorem cert_qLo_ok : ∀ j ∈ Finset.Icc 1 13, Even j →
    certQLo j ≤ (2 : ℝ) ^ (j - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 j := by
  intro j hj he
  have ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
  interval_cases j
  · exact absurd he (by decide)
  · simpa [certQLo] using ar2TensorQuad_two_ge
  · exact absurd he (by decide)
  · exact qLo_4_le
  · exact absurd he (by decide)
  · exact qLo_6_le
  · exact absurd he (by decide)
  · exact qLo_8_le
  · exact absurd he (by decide)
  · exact qLo_10_le
  · exact absurd he (by decide)
  · exact qLo_12_le
  · exact absurd he (by decide)

private theorem cert_qHi_ok : ∀ j ∈ Finset.Icc 1 13, Odd j →
    (2 : ℝ) ^ (j - 1) * ar2TensorQuad (17 / 10) (21 / 20) r19 j ≤ certQHi j := by
  intro j hj ho
  have ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
  interval_cases j
  · simpa [certQHi] using ar2TensorQuad_one_le
  · exact absurd ho (by decide)
  · exact qHi_3_ge
  · exact absurd ho (by decide)
  · exact qHi_5_ge
  · exact absurd ho (by decide)
  · exact qHi_7_ge
  · exact absurd ho (by decide)
  · exact qHi_9_ge
  · exact absurd ho (by decide)
  · exact qHi_11_ge
  · exact absurd ho (by decide)
  · exact qHi_13_ge

private theorem wave_term_odd_le {j : ℕ} (hj_pos : 1 ≤ j) :
    3 * (2 : ℝ) ^ (j - 1) * ar2TailBound (17 / 10) (21 / 20) j ≤
      if j = 1 then 3 * (2 * (4866 : ℝ) / 10 ^ 12)
      else 3 * (2 : ℝ) ^ (j - 1) * (2 * (4 : ℝ) / 10 ^ 12 +
        (j - 1 : ℝ) * (1 : ℝ) / 10 ^ 12) := by
  unfold ar2TailBound
  split_ifs with hj
  · subst hj; norm_num; linarith [certPairTail_le]
  · have hj1 : (0 : ℝ) ≤ (j : ℝ) - 1 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj_pos
      linarith
    have htail : 2 * ar2EndTail (17 / 10) + ((j : ℝ) - 1) * ar2IntTail (21 / 20) ≤
        2 * (4 : ℝ) / 10 ^ 12 + ((j : ℝ) - 1) * (1 : ℝ) / 10 ^ 12 := by
      have h1 := certEndTail_le; have h2 := certIntTail_le
      nlinarith
    exact mul_le_mul_of_nonneg_left htail (by positivity)

private theorem wave_sum_le_rat (J : ℕ) (hJ : J ≤ 13) :
    alternatingWaveSum J ≤
      ∑ j ∈ Finset.Icc 1 J,
        (if Odd j then
          3 * certQHi j +
          3 * (478 / 1000 : ℝ) * (2764 / 1000 : ℝ) ^ (j - 1) *
            (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
            (2 * (59 : ℝ) / 10 ^ 18 +
              ((j - 1 : ℕ) : ℝ) * (3492 : ℝ) / 10 ^ 18) +
          (if j = 1 then 3 * (2 * (4866 : ℝ) / 10 ^ 12)
           else 3 * (2 : ℝ) ^ (j - 1) * (2 * (4 : ℝ) / 10 ^ 12 +
             ((j : ℝ) - 1) * (1 : ℝ) / 10 ^ 12))
        else -(3 * certQLo j) +
          3 * (478 / 1000 : ℝ) * (2764 / 1000 : ℝ) ^ (j - 1) *
            (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
            (2 * (59 : ℝ) / 10 ^ 18 +
              ((j - 1 : ℕ) : ℝ) * (3492 : ℝ) / 10 ^ 18)) := by
  have hbase := alternatingWaveSum_le_of_quad (by omega : 0 < 19)
    (by norm_num : (0 : ℝ) < 17 / 10) (by norm_num : (0 : ℝ) < 21 / 20)
    r19_strictMono r19_range r19_root J certQLo certQHi
    (fun j hj he => cert_qLo_ok j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
      (Finset.mem_Icc.mp hj).2.trans hJ⟩) he)
    (fun j hj ho => cert_qHi_ok j (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
      (Finset.mem_Icc.mp hj).2.trans hJ⟩) ho)
  refine hbase.trans (Finset.sum_le_sum fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  by_cases ho : Odd j
  · simp only [ho, ↓reduceIte]
    exact add_le_add (add_le_add le_rfl (ar2QuadErr_term_le j)) (wave_term_odd_le hj1)
  · simp only [ho, ↓reduceIte]
    exact add_le_add le_rfl (ar2QuadErr_term_le j)

private theorem term_bound_eq (j : ℕ) (hj : j ∈ Finset.Icc 1 13) :
    (if Odd j then
      3 * certQHi j +
      3 * (478 / 1000 : ℝ) * (2764 / 1000 : ℝ) ^ (j - 1) *
        (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
        (2 * (59 : ℝ) / 10 ^ 18 +
          ((j - 1 : ℕ) : ℝ) * (3492 : ℝ) / 10 ^ 18) +
      (if j = 1 then 3 * (2 * (4866 : ℝ) / 10 ^ 12)
       else 3 * (2 : ℝ) ^ (j - 1) * (2 * (4 : ℝ) / 10 ^ 12 +
         ((j : ℝ) - 1) * (1 : ℝ) / 10 ^ 12))
    else -(3 * certQLo j) +
      3 * (478 / 1000 : ℝ) * (2764 / 1000 : ℝ) ^ (j - 1) *
        (17 / 10 : ℝ) ^ 2 * (21 / 20 : ℝ) ^ (j - 1) *
        (2 * (59 : ℝ) / 10 ^ 18 +
          ((j - 1 : ℕ) : ℝ) * (3492 : ℝ) / 10 ^ 18)) ≤
    (match j with
    | 1 => (1622601750 : ℝ) / 10 ^ 10
    | 2 => -(448760958 : ℝ) / 10 ^ 10
    | 3 => (185635427 : ℝ) / 10 ^ 10
    | 4 => -(73996584 : ℝ) / 10 ^ 10
    | 5 => (29337604 : ℝ) / 10 ^ 10
    | 6 => -(11655318 : ℝ) / 10 ^ 10
    | 7 => (4630136 : ℝ) / 10 ^ 10
    | 8 => -(1839211 : ℝ) / 10 ^ 10
    | 9 => (730726 : ℝ) / 10 ^ 10
    | 10 => -(290198 : ℝ) / 10 ^ 10
    | 11 => (115899 : ℝ) / 10 ^ 10
    | 12 => -(45598 : ℝ) / 10 ^ 10
    | 13 => (21271 : ℝ) / 10 ^ 10
    | _ => 0) := by
  have ⟨h1, h2⟩ := Finset.mem_Icc.mp hj
  interval_cases j
  · have hp : Odd (1 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : ¬ Odd (2 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : Odd (3 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : ¬ Odd (4 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : Odd (5 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : ¬ Odd (6 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : Odd (7 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : ¬ Odd (8 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : Odd (9 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : ¬ Odd (10 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : Odd (11 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : ¬ Odd (12 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]
  · have hp : Odd (13 : ℕ) := by decide
    simp only [hp, ↓reduceIte]; norm_num [certQHi, certQLo, certS]

/-- Certified upper bound `alternatingWaveSum 13 < 130649 / 1000000` (`0.130649`). -/
theorem alternatingWaveSum_13_lt : alternatingWaveSum 13 < (130649 / 1000000 : ℝ) := by
  have h := (wave_sum_le_rat 13 (by decide)).trans
    (Finset.sum_le_sum fun j hj => term_bound_eq j
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
        (Finset.mem_Icc.mp hj).2.trans (by decide : 13 ≤ 13)⟩))
  refine h.trans_lt ?_
  have hset : Finset.Icc 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  rw [hset]; norm_num

end VerifiedCertificate


end Cslib.Circuits.Frontier.CrossingCover

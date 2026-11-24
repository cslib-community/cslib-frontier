/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The stationary AR(2) density and the alternating wave sum

The stationary reversible Gaussian AR(2) chain attached to alternating sign paths on the infinite
3-regular tree has unit marginals, lag-one correlation `-2√2 / 3` and conditional variance `1 / 12`.
This module defines its densities and the truncated alternating wave sum

`alternatingWaveSum J = ∑ j ∈ Icc 1 J, (-1) ^ (j + 1) * (3 / 2) * 2 ^ (j - 1) * altPathProb j`,

and proves the basic facts about the densities. It is the common interface of
`CrossingCover.TreeWave`, which identifies `altPathProb j` with an alternating-sign orthant
probability of the Gaussian wave process, and `CrossingCover.Certificate`, which bounds
`alternatingWaveSum 13` numerically.

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

## Main results

* Positivity, sign symmetry, time-reversibility and pointwise upper bounds of the densities.
* `Cslib.Circuits.Frontier.CrossingCover.ar2JointDensity_continuous`: continuity.
* `Cslib.Circuits.Frontier.CrossingCover.ar2JointDensity_integrable`,
  `Cslib.Circuits.Frontier.CrossingCover.ar2JointDensity_integral_eq_one`: integrability and total
  mass `1`.
-/

public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset MeasureTheory Real
open scoped BigOperators

/-- Stationary bivariate Gaussian density with unit marginals and correlation `-2√2 / 3`. -/
@[expose] noncomputable def ar2InitDensity (x y : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) *
    Real.exp (-(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y)

/-- Gaussian AR(2) transition kernel with conditional mean `-√2 y - x / 2` and variance `1 / 12`. -/
@[expose] noncomputable def ar2Kernel (x y z : ℝ) : ℝ :=
  Real.sqrt (6 / Real.pi) *
    Real.exp (-6 * (z + Real.sqrt 2 * y + x / 2) ^ 2)

/-- Joint density of the first `j + 1` coordinates of the stationary AR(2) process. For `j = 0`
this is the standard 1D Gaussian density; for `j ≥ 1` it is the product of `ar2InitDensity` and
`j - 1` transition factors `ar2Kernel`. -/
@[expose] noncomputable def ar2JointDensity : (j : ℕ) → (Fin (j + 1) → ℝ) → ℝ
  | 0, x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x 0) ^ 2 / 2)
  | k + 1, x =>
      ar2InitDensity (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) *
        ∏ i : Fin k, ar2Kernel (x ⟨i.1, by omega⟩) (x ⟨i.1 + 1, by omega⟩)
          (x ⟨i.1 + 2, by omega⟩)

/-- Positive-orthant integral `∫_{x > 0} ar2JointDensity j x dx` over `Fin (j + 1) → ℝ`. -/
@[expose] noncomputable def ar2OrthantIntegral (j : ℕ) : ℝ :=
  ∫ x in Set.pi Set.univ (fun _ : Fin (j + 1) => Set.Ioi (0 : ℝ)),
    ar2JointDensity j x ∂(Measure.pi fun _ : Fin (j + 1) => volume)

/-- Alternating-sign path probability `2 * ar2OrthantIntegral j` for a path of `j` edges. -/
@[expose] noncomputable def altPathProb (j : ℕ) : ℝ :=
  2 * ar2OrthantIntegral j

/-- Truncated alternating wave sum up to path length `J`. -/
@[expose] noncomputable def alternatingWaveSum (J : ℕ) : ℝ :=
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

end Cslib.Circuits.Frontier.CrossingCover

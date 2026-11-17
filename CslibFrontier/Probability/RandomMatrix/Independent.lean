/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Product
public import Mathlib.Analysis.CStarAlgebra.Matrix
import CslibFrontier.Probability.Concentration.WeightedSum
import CslibFrontier.Probability.RandomMatrix.FiniteNet
import Mathlib.Tactic.Linarith

/-!
# Symmetric matrices with independent centered bounded entries

The strictly upper-triangular entries are independent centered finite random variables whose
oscillation is at most two. Reflecting them across the diagonal gives a symmetric matrix with
zero diagonal. Its operator norm is at most `36 √n` except with probability `2 exp (-n)`.

The argument expands a bilinear form as a weighted sum of the independent entries, bounds the
sum of its squared weights by four, and applies the finite-net union bound. No uniformity or
identical-distribution hypothesis is needed.

## Main results

* `Cslib.Probability.PMF.pi_opNorm_symmetric_gt_le`: the elementary spectral-norm tail bound.
-/

public section

open Finset Real

namespace Cslib.Probability.PMF

private def bilinearCoeff {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 then x p.1 * y p.2 + x p.2 * y p.1 else 0

private theorem inner_eq_sum {n : ℕ} {α : (Fin n × Fin n) → Type*}
    (score : ∀ i, α i → ℝ) (ω : ∀ i, α i) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j =
      (if i < j then score (i, j) (ω (i, j)) else 0) +
      (if j < i then score (j, i) (ω (j, i)) else 0))
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) y =
      ∑ p, bilinearCoeff x y p * score p (ω p) := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, M i j * x j) = _
  simp_rw [hM, add_mul, sum_add_distrib, mul_add, mul_sum]
  rw [sum_add_distrib]
  rw [sum_comm (f := fun i j => y i * ((if j < i then score (j, i) (ω (j, i)) else 0) * x j))]
  rw [← sum_add_distrib, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [bilinearCoeff, hij, ite_true]
    ring
  · simp only [bilinearCoeff, hij, ite_false, zero_mul, mul_zero, add_zero]

private theorem sum_bilinearCoeff_sq_le {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∑ p, bilinearCoeff x y p ^ 2 ≤ 4 := by
  have hprod (u v : EuclideanSpace ℝ (Fin n)) :
      ∑ p : Fin n × Fin n, (u p.1) ^ 2 * (v p.2) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum]
    rw [← sum_mul, ← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hy2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  have hxy : ‖x‖ ^ 2 * ‖y‖ ^ 2 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hx2 hy2 (sq_nonneg ‖y‖) zero_le_one
  calc
    ∑ p, bilinearCoeff x y p ^ 2 ≤
        ∑ p : Fin n × Fin n,
          (2 * ((x p.1) ^ 2 * (y p.2) ^ 2) + 2 * ((y p.1) ^ 2 * (x p.2) ^ 2)) := by
      apply sum_le_sum
      intro p hp
      dsimp only [bilinearCoeff]
      split_ifs
      · nlinarith [sq_nonneg (x p.1 * y p.2 - x p.2 * y p.1)]
      · norm_num only
        positivity
    _ = 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2) + 2 * (‖y‖ ^ 2 * ‖x‖ ^ 2) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hprod, hprod]
    _ ≤ 4 := by nlinarith

/-- A symmetric zero-diagonal matrix whose upper-triangular entries are independent,
centered, and have oscillation at most two has norm at most `36 √n` with failure probability
at most `2 exp (-n)`. The entrywise equality permits any existing matrix representation. -/
theorem pi_opNorm_symmetric_gt_le {n : ℕ} {α : (Fin n × Fin n) → Type*}
    [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hmean : ∀ i, ∑ x, (p i x).toReal * score i x = 0)
    (hosc : ∀ i x y, |score i x - score i y| ≤ 2)
    (M : (∀ i, α i) → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ ω i j, M ω i j =
      (if i < j then score (i, j) (ω (i, j)) else 0) +
      (if j < i then score (j, i) (ω (j, i)) else 0)) :
    ((pi p).toOuterMeasure {ω | 36 * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖}).toReal
      ≤ 2 * exp (-(n : ℝ)) := by
  classical
  have htail (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
      ((pi p).toOuterMeasure {ω | 9 * sqrt n ≤
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) y|}).toReal
        ≤ 2 * exp (-(81 * (n : ℝ)) / 8) := by
    simp_rw [inner_eq_sum score _ _ (hM _) x y]
    convert pi_abs_sum_mul_ge_le_of_centered p score (bilinearCoeff x y) hmean hosc
      (by norm_num : (0 : ℝ) ≤ 4) (sum_bilinearCoeff_sq_le x y hx hy)
      (by positivity : 0 ≤ 9 * sqrt (n : ℝ)) using 1
    rw [mul_pow, sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  have hbound := toOuterMeasure_opNorm_gt_le_of_inner_tail (pi p) M
    (by positivity : 0 ≤ 9 * sqrt (n : ℝ)) (by positivity) htail
  have hsize : (5 : ℝ) ^ n ≤ exp (4 * (n : ℝ)) := by
    have hfive : (5 : ℝ) ≤ exp 4 := by linarith [add_one_le_exp (4 : ℝ)]
    calc
      (5 : ℝ) ^ n ≤ (exp 4) ^ n := by gcongr
      _ = exp (4 * (n : ℝ)) := by rw [← exp_nat_mul]; congr 1; ring
  have h25 : (25 : ℝ) ^ n = (5 : ℝ) ^ n * 5 ^ n := by rw [← mul_pow]; norm_num
  calc
    _ ≤ (25 : ℝ) ^ n * (2 * exp (-(81 * (n : ℝ)) / 8)) := by
      simpa only [show (4 : ℝ) * (9 * sqrt n) = 36 * sqrt n by ring] using hbound
    _ = (5 : ℝ) ^ n * 5 ^ n * (2 * exp (-(81 * (n : ℝ)) / 8)) := by rw [h25]
    _ ≤ exp (4 * (n : ℝ)) * exp (4 * (n : ℝ)) *
        (2 * exp (-(81 * (n : ℝ)) / 8)) := by gcongr
    _ = 2 * exp (8 * (n : ℝ) - 81 * (n : ℝ) / 8) := by
      rw [show exp (4 * (n : ℝ)) * exp (4 * (n : ℝ)) *
          (2 * exp (-(81 * (n : ℝ)) / 8)) =
          2 * (exp (4 * (n : ℝ)) * exp (4 * (n : ℝ)) *
            exp (-(81 * (n : ℝ)) / 8)) by ring, ← exp_add, ← exp_add]
      congr 2
      ring
    _ ≤ 2 * exp (-(n : ℝ)) := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Cslib.Probability.PMF

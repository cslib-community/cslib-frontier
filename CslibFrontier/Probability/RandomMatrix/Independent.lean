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
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.Linarith

/-!
# Symmetric matrices with independent centered bounded entries

The strictly upper-triangular entries are independent centered finite random variables with
oscillation at most `L > 0`. Reflecting them across the diagonal gives a symmetric matrix with
zero diagonal. A single `1 / 16`-net gives an explicit exponential tail at any norm threshold
`c √n`, retaining the dependence on both `c` and `L`.

The argument expands a quadratic form as a weighted sum of the independent entries, bounds
the sum of its squared weights by two, and applies the finite-net union bound. No uniformity or
identical-distribution hypothesis is needed. In particular, `L = 2` gives the signed-noise bound
`5 √n`, while `L = 1` gives `(5 / 2) √n`, both with failure probability at most `2 exp (-n)`.

## Main results

* `Cslib.Probability.PMF.pi_opNorm_symmetric_gt_le`: the elementary spectral-norm tail bound.
-/

public section

open Finset Real

namespace Cslib.Probability.PMF

private def quadraticCoeff {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 then 2 * x p.1 * x p.2 else 0

private theorem inner_eq_sum {n : ℕ} {α : (Fin n × Fin n) → Type*}
    (score : ∀ i, α i → ℝ) (ω : ∀ i, α i) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, M i j =
      (if i < j then score (i, j) (ω (i, j)) else 0) +
      (if j < i then score (j, i) (ω (j, i)) else 0))
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) x =
      ∑ p, quadraticCoeff x p * score p (ω p) := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, x i * ∑ j, M i j * x j) = _
  simp_rw [hM, add_mul, sum_add_distrib, mul_add, mul_sum]
  rw [sum_add_distrib]
  rw [sum_comm (f := fun i j => x i * ((if j < i then score (j, i) (ω (j, i)) else 0) * x j))]
  rw [← sum_add_distrib, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [quadraticCoeff, hij, ite_true]
    ring
  · simp only [quadraticCoeff, hij, ite_false, zero_mul, mul_zero, add_zero]

private theorem sum_quadraticCoeff_sq_le {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : ‖x‖ ≤ 1) : ∑ p, quadraticCoeff x p ^ 2 ≤ 2 := by
  have hswap : (∑ p : Fin n × Fin n, quadraticCoeff x p.swap ^ 2) =
      ∑ p, quadraticCoeff x p ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_comm]
    rfl
  have hpair (p : Fin n × Fin n) :
      quadraticCoeff x p ^ 2 + quadraticCoeff x p.swap ^ 2 ≤
        4 * ((x p.1) ^ 2 * (x p.2) ^ 2) := by
    simp only [quadraticCoeff, Prod.fst_swap, Prod.snd_swap]
    split_ifs with h h' h'
    · exact (lt_asymm h h').elim
    · ring_nf
      exact le_rfl
    · ring_nf
      exact le_rfl
    · norm_num only
      positivity
  have hsum : 2 * (∑ p, quadraticCoeff x p ^ 2) ≤
      4 * (‖x‖ ^ 2 * ‖x‖ ^ 2) := by
    calc
      2 * (∑ p, quadraticCoeff x p ^ 2) =
          ∑ p, (quadraticCoeff x p ^ 2 + quadraticCoeff x p.swap ^ 2) := by
        rw [sum_add_distrib, hswap]
        ring
      _ ≤ ∑ p : Fin n × Fin n, 4 * ((x p.1) ^ 2 * (x p.2) ^ 2) :=
        sum_le_sum fun p _ => hpair p
      _ = 4 * (‖x‖ ^ 2 * ‖x‖ ^ 2) := by
        rw [← mul_sum, Fintype.sum_prod_type]
        simp_rw [← mul_sum]
        rw [← sum_mul, ← EuclideanSpace.real_norm_sq_eq]
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  have hx4 : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hx2 hx2 (sq_nonneg ‖x‖) zero_le_one
  linarith

/-- A symmetric zero-diagonal matrix with independent centered upper-triangular entries of
oscillation at most `L` has an explicit exponential operator-norm tail. The entrywise equality
permits any existing matrix representation. -/
theorem pi_opNorm_symmetric_gt_le {n : ℕ} {α : (Fin n × Fin n) → Type*}
    [∀ i, Fintype (α i)] (p : ∀ i, PMF (α i)) (score : ∀ i, α i → ℝ)
    (hmean : ∀ i, ∑ x, (p i x).toReal * score i x = 0)
    {L : ℝ} (hL : 0 < L) (hosc : ∀ i x y, |score i x - score i y| ≤ L)
    (M : (∀ i, α i) → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ ω i j, M ω i j =
      (if i < j then score (i, j) (ω (i, j)) else 0) +
      (if j < i then score (j, i) (ω (j, i)) else 0))
    {c : ℝ} (hc : 0 ≤ c) :
    ((pi p).toOuterMeasure {ω | c * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖}).toReal
      ≤ 2 * exp (((7 : ℝ) / 2 - 49 * c ^ 2 / (64 * L ^ 2)) * n) := by
  classical
  have hsymm (ω : ∀ i, α i) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)).toLinearMap.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    have htranspose : (M ω).transpose = M ω := by
      ext i j
      simp only [Matrix.transpose_apply, hM]
      ring
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using htranspose
  have htail (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
      ((pi p).toOuterMeasure {ω | 7 * c * sqrt n / 8 ≤
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) x|}).toReal
        ≤ 2 * exp (-((7 * c * sqrt n / 8) ^ 2) / L ^ 2) := by
    simp_rw [inner_eq_sum score _ _ (hM _) x]
    convert pi_abs_sum_mul_ge_le_of_centered p score (quadraticCoeff x) hmean hL hosc
      (by norm_num : (0 : ℝ) ≤ 2) (sum_quadraticCoeff_sq_le x hx)
      (by positivity : 0 ≤ 7 * c * sqrt (n : ℝ) / 8) using 1
    congr 2
    field_simp [hL.ne']
  have hbound := toOuterMeasure_opNorm_gt_le_of_quadratic_tail (pi p) M hsymm
    (q := 16) (by norm_num) (by positivity : 0 ≤ 7 * c * sqrt (n : ℝ) / 8)
    (by positivity) htail
  norm_num only [Nat.cast_ofNat] at hbound
  rw [show (7 * c * sqrt n / 8) / ((7 : ℝ) / 8) = c * sqrt n by ring] at hbound
  have hsize : (33 : ℝ) ^ n ≤ exp ((7 : ℝ) / 2 * n) := by
    have h33 : (33 : ℝ) ≤ exp ((7 : ℝ) / 2) := by
      have hsum := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 2) 10
      norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
      linarith
    calc
      (33 : ℝ) ^ n ≤ (exp ((7 : ℝ) / 2)) ^ n := by gcongr
      _ = exp ((7 : ℝ) / 2 * n) := by rw [← exp_nat_mul]; congr 1; ring
  calc
    _ ≤ (33 : ℝ) ^ n * (2 * exp (-((7 * c * sqrt n / 8) ^ 2) / L ^ 2)) := hbound
    _ ≤ exp ((7 : ℝ) / 2 * n) * (2 * exp (-((7 * c * sqrt n / 8) ^ 2) / L ^ 2)) := by
      gcongr
    _ = 2 * exp (((7 : ℝ) / 2 - 49 * c ^ 2 / (64 * L ^ 2)) * n) := by
      rw [show exp ((7 : ℝ) / 2 * n) * (2 * exp (-((7 * c * sqrt n / 8) ^ 2) / L ^ 2)) =
        2 * (exp ((7 : ℝ) / 2 * n) * exp (-((7 * c * sqrt n / 8) ^ 2) / L ^ 2)) by ring,
        ← exp_add]
      congr 2
      rw [div_pow, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg n)]
      field_simp [hL.ne']
      ring

end Cslib.Probability.PMF

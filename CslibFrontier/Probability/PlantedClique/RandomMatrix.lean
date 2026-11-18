/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PlantedClique.Model
public import Mathlib.Analysis.CStarAlgebra.Matrix
import CslibFrontier.Probability.BitString.Rademacher.Tail
import CslibFrontier.Foundations.Analysis.Normed.FiniteNet
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith

/-!
# The spectral norm of planted-clique noise

For a fixed planted set, each quadratic form of the centered symmetric noise is a sum of
independent signs whose coefficient squares sum to at most two on the unit ball. A single
`1 / 16`-net reduces the operator norm to at most `33 ^ n` such sums. The resulting elementary
bound is `5 √n` except on a set of uniform seeds of density at most `2 exp (-n)`. A parameterized
version retains the tradeoff between the norm constant and its exponential failure probability.

These bounds use an elementary net argument, rather than the sharper asymptotic random-matrix
estimate used in the planted-clique paper.

## Main results

* `Cslib.Probability.PlantedClique.dens_noise_opNorm_gt_le_mul`: the parameterized spectral tail.
* `Cslib.Probability.PlantedClique.dens_noise_opNorm_gt_le`: the bound at `5 √n`.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Probability.PlantedClique

private def quadraticCoeff {n : ℕ} (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 ∧ ¬(p.1 ∈ S ∧ p.2 ∈ S) then -(2 * x p.1 * x p.2) else 0

private theorem inner_noise_eq_sum {n : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) x =
      ∑ p, quadraticCoeff S x p * BitString.signVal (ω p) := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, x i * ∑ j, (upperNoise S ω i j + upperNoise S ω j i) * x j) = _
  simp only [add_mul, sum_add_distrib, mul_add, mul_sum]
  rw [sum_comm (f := fun i j => x i * (upperNoise S ω j i * x j))]
  rw [← sum_add_distrib, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  by_cases h : i < j ∧ ¬(i ∈ S ∧ j ∈ S)
  · simp only [quadraticCoeff, upperNoise, h, true_and, not_false_eq_true, ite_true]
    ring
  · simp only [quadraticCoeff, upperNoise, h, ite_false, zero_mul, mul_zero, add_zero]

private theorem sum_quadraticCoeff_sq_le {n : ℕ} (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    ∑ p, quadraticCoeff S x p ^ 2 ≤ 2 := by
  have hswap : (∑ p : Fin n × Fin n, quadraticCoeff S x p.swap ^ 2) =
      ∑ p, quadraticCoeff S x p ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, sum_comm]
    rfl
  have hpair (p : Fin n × Fin n) :
      quadraticCoeff S x p ^ 2 + quadraticCoeff S x p.swap ^ 2 ≤
        4 * ((x p.1) ^ 2 * (x p.2) ^ 2) := by
    simp only [quadraticCoeff, Prod.fst_swap, Prod.snd_swap]
    split_ifs with h h' h'
    · exact (lt_asymm h.1 h'.1).elim
    · ring_nf
      exact le_rfl
    · ring_nf
      exact le_rfl
    · norm_num only
      positivity
  have hsum : 2 * (∑ p, quadraticCoeff S x p ^ 2) ≤
      4 * (‖x‖ ^ 2 * ‖x‖ ^ 2) := by
    calc
      2 * (∑ p, quadraticCoeff S x p ^ 2) =
          ∑ p, (quadraticCoeff S x p ^ 2 + quadraticCoeff S x p.swap ^ 2) := by
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

private theorem dens_abs_inner_noise_ge_le {n : ℕ} (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (dens ({ω : Coins n | t ≤
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) x|} : Finset _) : ℝ) ≤
      2 * exp (-(t ^ 2) / 4) := by
  simp_rw [inner_noise_eq_sum]
  convert BitString.dens_abs_sum_mul_signVal_ge_le (quadraticCoeff S x)
    (by norm_num : (0 : ℝ) < 2) (sum_quadraticCoeff_sq_le S x hx) ht using 1
  norm_num

private theorem dens_noise_opNorm_gt_le_of_net {n : ℕ} (S : Finset (Fin n))
    {q : ℕ} (hq : 2 < q) {t : ℝ} (ht : 0 ≤ t) :
    (dens ({ω : Coins n | t / (1 - 2 / (q : ℝ)) <
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} : Finset _) : ℝ) ≤
      (2 * q + 1 : ℝ) ^ n * (2 * exp (-(t ^ 2) / 4)) := by
  classical
  obtain ⟨s, hcard, hs, hnet⟩ :=
    NormedSpace.exists_natInverseNet (EuclideanSpace ℝ (Fin n)) q (by omega)
  have hcard' : s.card ≤ (2 * q + 1) ^ n := by
    simpa only [finrank_euclideanSpace_fin] using hcard
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hε : (1 : ℝ) / q < 1 / 2 := (div_lt_iff₀ hqpos).2 (by linarith)
  let D : EuclideanSpace ℝ (Fin n) → Finset (Coins n) :=
    fun x => {ω | t ≤ |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) x|}
  let B : Finset (Coins n) := s.biUnion D
  have hsub : ({ω : Coins n | t / (1 - 2 / (q : ℝ)) <
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} : Finset _) ⊆ B := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_contra hnot
    have hall : ∀ x ∈ s,
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) x| ≤ t := by
      intro x hx
      have hx' : ω ∉ D x := fun hx' => hnot (mem_biUnion.mpr ⟨x, hx, hx'⟩)
      have hlt : |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) x| < t := by
        simpa only [D, mem_filter, mem_univ, true_and, not_le] using hx'
      exact hlt.le
    have hsymm : (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)).toLinearMap.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
        simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
          using noise_transpose S ω)
    have hnorm := (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)).opNorm_le_of_quadratic_net hsymm s
      (by positivity) hε ht hs hnet hall
    have heq : 1 - 2 * ((1 : ℝ) / q) = 1 - 2 / (q : ℝ) := by ring
    rw [heq] at hnorm
    exact (not_lt_of_ge hnorm) hω
  have hunion : (dens B : ℝ) ≤ ∑ x ∈ s, (dens (D x) : ℝ) := by
    have h : dens B ≤ ∑ x ∈ s, dens (D x) := dens_biUnion_le
    simpa only [NNRat.cast_sum] using (NNRat.cast_le (K := ℝ)).2 h
  calc
    (dens ({ω : Coins n | t / (1 - 2 / (q : ℝ)) <
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} : Finset _) : ℝ) ≤ dens B := by
      exact_mod_cast dens_le_dens hsub
    _ ≤ ∑ x ∈ s, (2 * exp (-(t ^ 2) / 4)) :=
      hunion.trans (sum_le_sum fun x hx => dens_abs_inner_noise_ge_le S x (hs x hx) ht)
    _ = (s.card : ℝ) * (2 * exp (-(t ^ 2) / 4)) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (2 * q + 1 : ℝ) ^ n * (2 * exp (-(t ^ 2) / 4)) := by
      gcongr
      exact_mod_cast hcard'

/-- The elementary quadratic-net tail at any nonnegative multiple of `√n`.
For example, the signed-noise constant `9 / 2` gives failure at most `2 exp (-385 n / 1024)`.
The adjacency matrix's centered noise is half of this signed matrix. -/
theorem dens_noise_opNorm_gt_le_mul {n : ℕ} (S : Finset (Fin n)) {c : ℝ} (hc : 0 ≤ c) :
    (dens ({ω : Coins n | c * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
      Finset _) : ℝ) ≤ 2 * exp (((7 : ℝ) / 2 - 49 * c ^ 2 / 256) * n) := by
  have h := dens_noise_opNorm_gt_le_of_net S (q := 16) (by norm_num)
    (t := 7 * c * sqrt n / 8) (by positivity)
  norm_num only [Nat.cast_ofNat] at h
  have hthreshold : (7 * c * sqrt n / 8) / ((7 : ℝ) / 8) = c * sqrt n := by ring
  rw [hthreshold] at h
  have hsize : (33 : ℝ) ^ n ≤ exp ((7 : ℝ) / 2 * n) := by
    have h33 : (33 : ℝ) ≤ exp ((7 : ℝ) / 2) := by
      have hsum := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 2) 10
      norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
      linarith
    calc
      (33 : ℝ) ^ n ≤ (exp ((7 : ℝ) / 2)) ^ n := by gcongr
      _ = exp ((7 : ℝ) / 2 * n) := by rw [← exp_nat_mul]; congr 1; ring
  calc
    (dens ({ω : Coins n | c * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
        Finset _) : ℝ) ≤ (33 : ℝ) ^ n * (2 * exp (-((7 * c * sqrt n / 8) ^ 2) / 4)) := h
    _ ≤ exp ((7 : ℝ) / 2 * n) * (2 * exp (-((7 * c * sqrt n / 8) ^ 2) / 4)) := by
      gcongr
    _ = 2 * exp (((7 : ℝ) / 2 - 49 * c ^ 2 / 256) * n) := by
      rw [show exp ((7 : ℝ) / 2 * n) * (2 * exp (-((7 * c * sqrt n / 8) ^ 2) / 4)) =
        2 * (exp ((7 : ℝ) / 2 * n) * exp (-((7 * c * sqrt n / 8) ^ 2) / 4)) by ring,
        ← exp_add]
      congr 2
      rw [div_pow, mul_pow, mul_pow, sq_sqrt (Nat.cast_nonneg n)]
      ring

/-- The centered symmetric planted-clique noise has norm at most `5 √n`, with failure
density at most `2 exp (-n)` under independent uniform edge coins. -/
theorem dens_noise_opNorm_gt_le {n : ℕ} (S : Finset (Fin n)) :
    (dens ({ω : Coins n | 5 * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
      Finset _) : ℝ) ≤ 2 * exp (-(n : ℝ)) := by
  apply (dens_noise_opNorm_gt_le_mul S (c := 5) (by norm_num)).trans
  gcongr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Cslib.Probability.PlantedClique

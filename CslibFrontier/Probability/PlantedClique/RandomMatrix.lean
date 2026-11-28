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
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith

/-!
# The spectral norm of planted-clique noise

For a fixed planted set, every bilinear form of the centered symmetric noise is a sum of
independent signs. A pair of half-nets of the unit ball reduces its operator norm to at most
`25 ^ n` such sums. The resulting elementary finite bound is `36 √n` except on a set of
uniform seeds of density at most `2 exp (-n)`.

## Main results

* `Cslib.Probability.PlantedClique.dens_noise_opNorm_gt_le`: the spectral-norm tail bound.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Probability.PlantedClique

private def bilinearCoeff {n : ℕ} (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 ∧ ¬(p.1 ∈ S ∧ p.2 ∈ S)
  then -(x p.1 * y p.2 + x p.2 * y p.1) else 0

private theorem inner_noise_eq_sum {n : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) y =
      ∑ p, bilinearCoeff S x y p * BitString.signVal (ω p) := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, (upperNoise S ω i j + upperNoise S ω j i) * x j) = _
  simp only [add_mul, sum_add_distrib, mul_add, mul_sum]
  rw [sum_comm (f := fun i j => y i * (upperNoise S ω j i * x j))]
  rw [← sum_add_distrib, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : i < j ∧ ¬(i ∈ S ∧ j ∈ S)
  · simp only [bilinearCoeff, upperNoise, h, true_and, not_false_eq_true, ite_true]
    ring
  · simp only [bilinearCoeff, upperNoise, h, ite_false, zero_mul, mul_zero, add_zero]

private theorem sum_bilinearCoeff_sq_le {n : ℕ} (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∑ p, bilinearCoeff S x y p ^ 2 ≤ 4 := by
  have hprod (u v : EuclideanSpace ℝ (Fin n)) :
      ∑ p : Fin n × Fin n, (u p.1) ^ 2 * (v p.2) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum]
    rw [← sum_mul, ← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  have hxy : ‖x‖ ^ 2 * ‖y‖ ^ 2 ≤ 1 := by
    simpa only [one_mul] using mul_le_mul
      (by nlinarith [norm_nonneg x] : ‖x‖ ^ 2 ≤ 1)
      (by nlinarith [norm_nonneg y] : ‖y‖ ^ 2 ≤ 1)
      (sq_nonneg _) zero_le_one
  calc
    ∑ p, bilinearCoeff S x y p ^ 2 ≤
        ∑ p : Fin n × Fin n,
          (2 * ((x p.1) ^ 2 * (y p.2) ^ 2) + 2 * ((y p.1) ^ 2 * (x p.2) ^ 2)) := by
      refine sum_le_sum fun p _ => ?_
      dsimp only [bilinearCoeff]
      split_ifs
      · nlinarith [sq_nonneg (x p.1 * y p.2 - x p.2 * y p.1)]
      · rw [zero_pow two_ne_zero]
        positivity
    _ = 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2) + 2 * (‖y‖ ^ 2 * ‖x‖ ^ 2) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hprod, hprod]
    _ ≤ 4 := by nlinarith

private theorem dens_abs_inner_noise_ge_le {n : ℕ} (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    (dens ({ω : Coins n | 9 * sqrt n ≤
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) y|} : Finset _) : ℝ) ≤
      2 * exp (-(81 * (n : ℝ)) / 8) := by
  simp_rw [inner_noise_eq_sum]
  convert BitString.dens_abs_sum_mul_signVal_ge_le (bilinearCoeff S x y)
    (by norm_num : (0 : ℝ) < 4) (sum_bilinearCoeff_sq_le S x y hx hy)
    (by positivity : 0 ≤ 9 * sqrt (n : ℝ)) using 1
  rw [mul_pow, sq_sqrt (Nat.cast_nonneg n)]
  norm_num

/-- The centered symmetric planted-clique noise has norm at most `36 √n`, with failure
density at most `2 exp (-n)` under independent uniform edge coins. -/
theorem dens_noise_opNorm_gt_le {n : ℕ} (S : Finset (Fin n)) :
    (dens ({ω : Coins n | 36 * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
      Finset _) : ℝ) ≤ 2 * exp (-(n : ℝ)) := by
  classical
  obtain ⟨s, hcard, hs, hnet⟩ := NormedSpace.exists_halfNet (EuclideanSpace ℝ (Fin n))
  have hcard' : s.card ≤ 5 ^ n := by simpa only [finrank_euclideanSpace_fin] using hcard
  let D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → Finset (Coins n) :=
    fun x y => {ω | 9 * sqrt n ≤ |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) y|}
  let B : Finset (Coins n) := s.biUnion fun x => s.biUnion (D x)
  have hsub : ({ω : Coins n | 36 * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
      Finset _) ⊆ B := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_contra hnot
    have hall : ∀ x ∈ s, ∀ y ∈ s,
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) x) y| ≤ 9 * sqrt n := by
      intro x hx y hy
      by_contra hgt
      exact hnot (mem_biUnion.mpr ⟨x, hx, mem_biUnion.mpr ⟨y, hy,
        mem_filter.mpr ⟨mem_univ _, le_of_not_ge hgt⟩⟩⟩)
    have hnorm := ContinuousLinearMap.opNorm_le_four_mul_of_halfNet
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)) s s hnet hnet (by positivity) hall
    nlinarith
  have hunion : (dens B : ℝ) ≤ ∑ x ∈ s, ∑ y ∈ s, (dens (D x y) : ℝ) := by
    have h : dens B ≤ ∑ x ∈ s, ∑ y ∈ s, dens (D x y) :=
      dens_biUnion_le.trans (sum_le_sum fun x _ => dens_biUnion_le)
    simpa only [NNRat.cast_sum] using (NNRat.cast_le (K := ℝ)).2 h
  have hsize : (s.card : ℝ) ≤ exp (4 * (n : ℝ)) := by
    have hfive : (5 : ℝ) ≤ exp 4 := by linarith [add_one_le_exp (4 : ℝ)]
    calc
      (s.card : ℝ) ≤ (5 : ℝ) ^ n := by exact_mod_cast hcard'
      _ ≤ (exp 4) ^ n := by gcongr
      _ = exp (4 * (n : ℝ)) := by rw [← exp_natCast_mul]; congr 1; ring
  calc
    (dens ({ω : Coins n | 36 * sqrt n < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖} :
        Finset _) : ℝ) ≤ dens B := by exact_mod_cast dens_le_dens hsub
    _ ≤ ∑ x ∈ s, ∑ y ∈ s, (2 * exp (-(81 * (n : ℝ)) / 8)) :=
      hunion.trans (sum_le_sum fun x hx => sum_le_sum fun y hy =>
        dens_abs_inner_noise_ge_le S x y (hs x hx) (hs y hy))
    _ = (s.card : ℝ) * (s.card : ℝ) * (2 * exp (-(81 * (n : ℝ)) / 8)) := by
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ exp (4 * (n : ℝ)) * exp (4 * (n : ℝ)) *
        (2 * exp (-(81 * (n : ℝ)) / 8)) := by gcongr
    _ = 2 * exp (8 * (n : ℝ) - 81 * (n : ℝ) / 8) := by
      have hr : exp (4 * (n : ℝ)) * exp (4 * (n : ℝ)) * (2 * exp (-(81 * (n : ℝ)) / 8)) =
          2 * (exp (4 * (n : ℝ)) * exp (4 * (n : ℝ)) * exp (-(81 * (n : ℝ)) / 8)) := by ring
      rw [hr, ← exp_add, ← exp_add]
      congr 2
      ring
    _ ≤ 2 * exp (-(n : ℝ)) := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]

end Cslib.Probability.PlantedClique

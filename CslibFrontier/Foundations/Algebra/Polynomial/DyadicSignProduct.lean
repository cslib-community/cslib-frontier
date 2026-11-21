/-
Copyright (c) 2026 lean-canny contributors, Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Samuel Schlesinger, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial approximation)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# A dyadic polynomial product for sign tests

The product of the factors `2 ^ j + x` dominates its reflection for positive
`x` in the dyadic range. One factor uses a power of two within a factor of two
of `x`, and the other factors preserve the comparison. Scaling the input covers
the reciprocal range, while an even power amplifies the comparison.

Adapted from `DyadicSignFactor`, `RationalSignProduct`, and `RationalSignError`
in lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
The integer factors use the common argument `2 ^ B * x`. This scales each
of the original factors by a positive power of two shared by both reflections.
-/

public section

namespace Polynomial

open Finset

private theorem exists_two_pow_interval {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {M : ℕ} {x : R} (hx : 1 ≤ x) (hM : x ≤ (2 : R) ^ M) :
    ∃ j ∈ range (M + 1), (2 : R) ^ j ≤ x ∧ x ≤ 2 * (2 : R) ^ j := by
  induction M with
  | zero =>
    refine ⟨0, mem_range.mpr Nat.zero_lt_one, ?_, ?_⟩
    · simpa only [pow_zero] using hx
    · rw [pow_zero, mul_one] at *
      exact hM.trans (by norm_num)
  | succ M ih =>
    by_cases hle : x ≤ (2 : R) ^ M
    · obtain ⟨j, hj, hj₁, hj₂⟩ := ih hle
      exact ⟨j, mem_range.mpr ((mem_range.mp hj).trans (Nat.lt_succ_self _)), hj₁, hj₂⟩
    · exact ⟨M, mem_range.mpr (by omega), le_of_not_ge hle, by
        simpa only [pow_succ'] using hM⟩

/-- On the positive dyadic range, the product of `2 ^ j + x` dominates the
absolute value of the reflected product by a factor of at least three. -/
theorem three_mul_abs_prod_two_pow_sub_le {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {M : ℕ} {x : R} (hx : 1 ≤ x) (hM : x ≤ (2 : R) ^ M) :
    3 * |∏ j ∈ range (M + 1), ((2 : R) ^ j - x)| ≤
      ∏ j ∈ range (M + 1), ((2 : R) ^ j + x) := by
  obtain ⟨j, hj, hlo, hhi⟩ := exists_two_pow_interval hx hM
  rw [← mul_prod_erase _ (fun k => (2 : R) ^ k - x) hj,
    ← mul_prod_erase _ (fun k => (2 : R) ^ k + x) hj, abs_mul, ← mul_assoc]
  have hnear : 3 * |(2 : R) ^ j - x| ≤ (2 : R) ^ j + x := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith
  have hrest : |∏ k ∈ (range (M + 1)).erase j, ((2 : R) ^ k - x)| ≤
      ∏ k ∈ (range (M + 1)).erase j, ((2 : R) ^ k + x) := by
    rw [abs_prod]
    refine prod_le_prod₀ (fun _ _ => abs_nonneg _) fun k _ => ?_
    have hk : (0 : R) ≤ 2 ^ k := by positivity
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact mul_le_mul hnear hrest (abs_nonneg _) (by positivity)

/-- The integer polynomial obtained by scaling the input to the dyadic product
and raising the result to the even exponent `2 * s`. -/
@[expose] noncomputable def dyadicSignProduct (B s : ℕ) : ℤ[X] :=
  (∏ j ∈ range (2 * B + 1), (C ((2 : ℤ) ^ j) + C ((2 : ℤ) ^ B) * X)) ^ (2 * s)

/-- The product evaluates by casting the integer factors and using the same scale
in every factor. -/
theorem eval₂_dyadicSignProduct {R : Type*} [CommRing R] (B s : ℕ) (x : R) :
    (dyadicSignProduct B s).eval₂ (Int.castRingHom R) x =
      (∏ j ∈ range (2 * B + 1), ((2 : R) ^ j + (2 : R) ^ B * x)) ^ (2 * s) := by
  simp only [dyadicSignProduct, eval₂_finsetProd, eval₂_pow, eval₂_add, eval₂_mul, eval₂_C, eval₂_X,
    Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]

/-- Reflection is exponentially suppressed for positive inputs in the
advertised dyadic range. -/
theorem eval₂_dyadicSignProduct_neg_le (B s : ℕ) {x : ℝ}
    (hx₀ : ((2 : ℝ) ^ B)⁻¹ ≤ x) (hx₁ : x ≤ (2 : ℝ) ^ B) :
    (3 : ℝ) ^ (2 * s) * (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) (-x) ≤
      (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) x := by
  have hlo : 1 ≤ (2 : ℝ) ^ B * x := by
    have h := mul_le_mul_of_nonneg_left hx₀ (show (0 : ℝ) ≤ 2 ^ B by positivity)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  have hhi : (2 : ℝ) ^ B * x ≤ (2 : ℝ) ^ (2 * B) := by
    rw [two_mul, pow_add]
    exact mul_le_mul_of_nonneg_left hx₁ (by positivity)
  rw [eval₂_dyadicSignProduct, eval₂_dyadicSignProduct]
  simp only [mul_neg, ← sub_eq_add_neg]
  rw [← (even_two_mul s).pow_abs (∏ j ∈ range (2 * B + 1),
    ((2 : ℝ) ^ j - (2 : ℝ) ^ B * x)), ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (three_mul_abs_prod_two_pow_sub_le hlo hhi) _

/-- The sum of the two reflected values is at least one at every real input.
This is the denominator of the normalized sign approximation. -/
theorem one_le_eval₂_dyadicSignProduct_add_neg (B s : ℕ) (x : ℝ) :
    1 ≤ (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) x +
      (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) (-x) := by
  simp only [eval₂_dyadicSignProduct]
  let f (y : ℝ) := (∏ j ∈ range (2 * B + 1), ((2 : ℝ) ^ j + (2 : ℝ) ^ B * y)) ^ (2 * s)
  change 1 ≤ f x + f (-x)
  have hnonneg (y : ℝ) : 0 ≤ f y := (even_two_mul s).pow_nonneg _
  have hone (y : ℝ) (hy : 0 ≤ y) : 1 ≤ f y := by
    apply one_le_pow₀ (Finset.one_le_prod₀ fun k _ => ?_)
    exact (one_le_pow₀ (by norm_num)).trans
      (le_add_of_nonneg_right (mul_nonneg (by positivity) hy))
  by_cases hx : 0 ≤ x
  · exact (hone x hx).trans (le_add_of_nonneg_right (hnonneg (-x)))
  · exact (hone (-x) (neg_nonneg.mpr (le_of_not_ge hx))).trans
      (le_add_of_nonneg_left (hnonneg x))

end Polynomial

/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial approximation)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.DyadicSignProduct
public import Mathlib.Basic.Sign.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Rational approximation of the sign on a dyadic interval

The normalized difference of the two reflected evaluations of the integer
sign product is exact at zero. For nonzero inputs of magnitude between
`2 ^ B` and its reciprocal, the error is at most `2 / 3 ^ (2 * s)`.
The denominator is positive everywhere by the sign product bound.

Adapted from `RationalSignProduct` and `RationalSignError` in lean-canny at
commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

/-- Approximate the sign by the difference of the reflected product values
divided by their sum. -/
@[expose] noncomputable def dyadicSignApprox (B s : ℕ) (x : ℝ) : ℝ :=
  let a := (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) x
  let b := (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) (-x)
  (a - b) / (a + b)

/-- The normalized difference is zero at the origin. -/
@[simp]
theorem dyadicSignApprox_zero (B s : ℕ) : dyadicSignApprox B s 0 = 0 := by
  simp only [dyadicSignApprox, neg_zero, sub_self, zero_div]

private theorem dyadicSignApprox_neg (B s : ℕ) (x : ℝ) :
    dyadicSignApprox B s (-x) = -dyadicSignApprox B s x := by
  simp only [dyadicSignApprox, neg_neg, add_comm]
  rw [← neg_div, neg_sub]

private theorem abs_dyadicSignApprox_sub_one_le (B s : ℕ) {x : ℝ}
    (hlo : ((2 : ℝ) ^ B)⁻¹ ≤ x) (hhi : x ≤ (2 : ℝ) ^ B) :
    |dyadicSignApprox B s x - 1| ≤ 2 * ((3 : ℝ) ^ (2 * s))⁻¹ := by
  let a := (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) x
  let b := (dyadicSignProduct B s).eval₂ (Int.castRingHom ℝ) (-x)
  have hb : 0 ≤ b := by
    dsimp only [b]
    rw [eval₂_dyadicSignProduct]
    exact (even_two_mul s).pow_nonneg _
  have hd : 0 < a + b := zero_lt_one.trans_le (one_le_eval₂_dyadicSignProduct_add_neg B s x)
  have hscale : 0 < (3 : ℝ) ^ (2 * s) := by positivity
  have h : (3 : ℝ) ^ (2 * s) * b ≤ a + b :=
    (eval₂_dyadicSignProduct_neg_le B s hlo hhi).trans (le_add_of_nonneg_right hb)
  change |(a - b) / (a + b) - 1| ≤ _
  rw [div_sub_one hd.ne', show a - b - (a + b) = -(2 * b) by ring,
    abs_div, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hb), abs_of_pos hd,
    ← div_eq_mul_inv, div_le_div_iff₀ hd hscale]
  calc
    _ = 2 * ((3 : ℝ) ^ (2 * s) * b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- The normalized ratio approximates the sign with uniform exponential error
for either sign on the dyadic range, and it also accepts zero. -/
theorem abs_dyadicSignApprox_sub_sign_le (B s : ℕ) {x : ℝ}
    (hx : x = 0 ∨ (((2 : ℝ) ^ B)⁻¹ ≤ |x| ∧ |x| ≤ (2 : ℝ) ^ B)) :
    |dyadicSignApprox B s x - (SignType.sign x : ℝ)| ≤ 2 * ((3 : ℝ) ^ (2 * s))⁻¹ := by
  by_cases hzero : x = 0
  · subst x
    rw [dyadicSignApprox_zero, sign_zero, SignType.coe_zero, sub_zero, abs_zero]
    positivity
  obtain ⟨hlo, hhi⟩ := hx.resolve_left hzero
  rcases lt_or_gt_of_ne hzero with hn | hp
  · rw [abs_of_neg hn] at hlo hhi
    have he : dyadicSignApprox B s x - (-1) = -(dyadicSignApprox B s (-x) - 1) := by
      rw [dyadicSignApprox_neg]
      ring
    rw [sign_neg hn, SignType.coe_neg_one, he, abs_neg]
    exact abs_dyadicSignApprox_sub_one_le B s hlo hhi
  · rw [abs_of_pos hp] at hlo hhi
    rw [sign_pos hp, SignType.coe_one]
    exact abs_dyadicSignApprox_sub_one_le B s hlo hhi

/-- For a list of `m` tests, repetition `m + 1` brings the per-test error within
the tolerance of the squared-error score. -/
theorem abs_dyadicSignApprox_sub_sign_le_inv_four_mul_succ (B m : ℕ) {x : ℝ}
    (hx : x = 0 ∨ (((2 : ℝ) ^ B)⁻¹ ≤ |x| ∧ |x| ≤ (2 : ℝ) ^ B)) :
    |dyadicSignApprox B (m + 1) x - (SignType.sign x : ℝ)| ≤ (4 * ((m : ℝ) + 1))⁻¹ := by
  apply (abs_dyadicSignApprox_sub_sign_le B (m + 1) hx).trans
  have h : 8 * ((m : ℝ) + 1) ≤ (3 : ℝ) ^ (2 * (m + 1)) := by
    rw [pow_mul]
    have hbern := one_add_mul_le_pow (a := (8 : ℝ)) (by norm_num) (m + 1)
    norm_num [Nat.cast_succ] at hbern ⊢
    linarith
  rw [← div_eq_mul_inv, ← one_div (4 * ((m : ℝ) + 1)),
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

end Polynomial

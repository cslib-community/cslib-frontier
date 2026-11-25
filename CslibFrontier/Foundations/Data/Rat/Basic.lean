/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth, OpenAI
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Rat/Lemmas.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat

/-!
# Properties of integer quotients `Rat.divInt`

Elementary properties of `Rat.divInt a b`: the reduced numerator magnitude in terms of
`Nat.gcd a.natAbs b.natAbs`, the numerator sign bit, and magnitude bounds on numerator and
denominator.

## Main results

* `Rat.natAbs_num_divInt_of_ne_zero`: numerator magnitude for `b ≠ 0`.
* `Rat.natAbs_num_divInt`: unconditional numerator magnitude.
* `Rat.natAbs_num_divInt_le`: numerator magnitude bound `|num| ≤ |a|`.
* `Rat.den_divInt_le`: denominator bound `den ≤ |b|`.
* `Rat.decide_num_divInt_lt_zero_of_ne_zero`: numerator sign bit for `b ≠ 0`.
* `Rat.decide_num_divInt_lt_zero`: unconditional numerator sign bit.
* `Rat.natAbs_num_add_le`, `Rat.den_add_le`, `Rat.natAbs_num_sub_le`, `Rat.den_sub_le`,
  `Rat.natAbs_num_mul_le`, `Rat.den_mul_le`, `Rat.natAbs_num_inv_le`, `Rat.den_inv_le`,
  `Rat.natAbs_num_div_le`, `Rat.den_div_le`: numerator magnitude and denominator bounds for
  rational arithmetic operations.
-/

public section

namespace Rat

/-- Reduced numerator magnitude of `Rat.divInt a b` for `b ≠ 0`. -/
theorem natAbs_num_divInt_of_ne_zero (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).num.natAbs = a.natAbs / Nat.gcd a.natAbs b.natAbs := by
  rw [Rat.num_divInt,
    Int.natAbs_ediv_of_dvd (dvd_mul_of_dvd_right (Int.gcd_dvd_right b a) b.sign),
    Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hb, Int.natAbs_natCast, one_mul]
  simp only [Int.gcd, Nat.gcd_comm]

/-- Reduced numerator magnitude of `Rat.divInt a b` for arbitrary integers `a, b`. -/
theorem natAbs_num_divInt (a b : ℤ) :
    (Rat.divInt a b).num.natAbs =
      if b = 0 then 0 else a.natAbs / Nat.gcd a.natAbs b.natAbs := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp [hb, natAbs_num_divInt_of_ne_zero a b hb]

/-- Reduced numerator magnitude of `Rat.divInt a b` is bounded by `|a|`. -/
theorem natAbs_num_divInt_le (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hb) ha

/-- Reduced denominator of `Rat.divInt a b` is bounded by `|b|`. -/
theorem den_divInt_le (a b : ℤ) (hb : b ≠ 0) :
    (Rat.divInt a b).den ≤ b.natAbs := by
  simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb

/-- Sign bit of `Rat.divInt a b` for `b ≠ 0`. -/
theorem decide_num_divInt_lt_zero_of_ne_zero (a b : ℤ) (hb : b ≠ 0) :
    decide ((Rat.divInt a b).num < 0) =
      if a = 0 then false else (decide (a < 0) ^^ decide (b < 0)) := by
  simp only [show ((Rat.divInt a b).num < 0) ↔ (a : ℚ) / (b : ℚ) < 0 by
    rw [← Rat.num_neg, Rat.divInt_eq_div]]
  by_cases ha : a = 0
  · simp [ha]
  · simp only [ha, ↓reduceIte]
    rcases lt_or_gt_of_ne ha with hna | hpa <;> rcases lt_or_gt_of_ne hb with hnb | hpb
    · simp only [hna, hnb, not_lt_of_ge (div_pos_of_neg_of_neg
        (Int.cast_lt_zero.mpr hna) (Int.cast_lt_zero.mpr hnb) : (0 : ℚ) < _).le, decide_true,
        decide_false]; rfl
    · simp only [hna, not_lt_of_gt hpb, (div_neg_of_neg_of_pos
        (Int.cast_lt_zero.mpr hna) (Int.cast_pos.mpr hpb) : (a : ℚ) / b < 0), decide_true,
        decide_false]; rfl
    · simp only [not_lt_of_gt hpa, hnb, (div_neg_of_pos_of_neg
        (Int.cast_pos.mpr hpa) (Int.cast_lt_zero.mpr hnb) : (a : ℚ) / b < 0), decide_true,
        decide_false]; rfl
    · simp only [not_lt_of_gt hpa, not_lt_of_gt hpb, not_lt_of_ge (div_pos
        (Int.cast_pos.mpr hpa) (Int.cast_pos.mpr hpb) : (0 : ℚ) < _).le, decide_false]; rfl

/-- Sign bit of `Rat.divInt a b` for arbitrary integers `a, b`. -/
theorem decide_num_divInt_lt_zero (a b : ℤ) :
    decide ((Rat.divInt a b).num < 0) =
      if a = 0 then false else if b = 0 then false else (decide (a < 0) ^^ decide (b < 0)) := by
  by_cases hb : b = 0
  · subst hb; simp
  · simp only [hb, ↓reduceIte, decide_num_divInt_lt_zero_of_ne_zero a b hb]

/-- Reduced numerator magnitude of `a + b` is bounded by `|a.num| * b.den + |b.num| * a.den`. -/
theorem natAbs_num_add_le (a b : ℚ) :
    (a + b).num.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den := by
  rw [Rat.add_def', Rat.mkRat_eq_divInt]
  refine (Rat.natAbs_num_divInt_le _ _
    (Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero a.den_nz b.den_nz))).trans ?_
  simpa [Int.natAbs_mul] using Int.natAbs_add_le (a.num * b.den) (b.num * a.den)

/-- Reduced denominator of `a + b` is bounded by `a.den * b.den`. -/
theorem den_add_le (a b : ℚ) : (a + b).den ≤ a.den * b.den := by
  rw [Rat.add_def', Rat.mkRat_eq_divInt]
  simpa only [Int.natAbs_natCast] using
    Rat.den_divInt_le _ _ (Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero a.den_nz b.den_nz))

/-- Reduced numerator magnitude of `a - b` is bounded by `|a.num| * b.den + |b.num| * a.den`. -/
theorem natAbs_num_sub_le (a b : ℚ) :
    (a - b).num.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den := by
  simpa [sub_eq_add_neg] using natAbs_num_add_le a (-b)

/-- Reduced denominator of `a - b` is bounded by `a.den * b.den`. -/
theorem den_sub_le (a b : ℚ) : (a - b).den ≤ a.den * b.den := by
  simpa [sub_eq_add_neg] using den_add_le a (-b)

/-- Reduced numerator magnitude of `a * b` is bounded by `|a.num| * |b.num|`. -/
theorem natAbs_num_mul_le (a b : ℚ) : (a * b).num.natAbs ≤ a.num.natAbs * b.num.natAbs := by
  rw [Rat.mul_def', Rat.mkRat_eq_divInt]
  simpa only [Int.natAbs_mul] using Rat.natAbs_num_divInt_le (a.num * b.num) _
    (Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero a.den_nz b.den_nz))

/-- Reduced denominator of `a * b` is bounded by `a.den * b.den`. -/
theorem den_mul_le (a b : ℚ) : (a * b).den ≤ a.den * b.den := by
  rw [Rat.mul_def', Rat.mkRat_eq_divInt]
  simpa only [Int.natAbs_natCast] using Rat.den_divInt_le (a.num * b.num) _
    (Int.ofNat_ne_zero.mpr (Nat.mul_ne_zero a.den_nz b.den_nz))

/-- Reduced numerator magnitude of `a⁻¹` is bounded by `a.den`. -/
theorem natAbs_num_inv_le (a : ℚ) : a⁻¹.num.natAbs ≤ a.den := by
  rw [Rat.inv_def]
  by_cases ha : a.num = 0
  · simp [ha]
  · simpa only [Int.natAbs_natCast] using Rat.natAbs_num_divInt_le (a.den : ℤ) a.num ha

/-- Reduced denominator of `a⁻¹` is bounded by `max |a.num| 1`. -/
theorem den_inv_le (a : ℚ) : a⁻¹.den ≤ max a.num.natAbs 1 := by
  rw [Rat.inv_def]
  by_cases ha : a.num = 0
  · simp [ha]
  · exact (Rat.den_divInt_le _ _ ha).trans (le_max_left _ _)

/-- Reduced numerator magnitude of `a / b` is bounded by `|a.num| * b.den`. -/
theorem natAbs_num_div_le (a b : ℚ) : (a / b).num.natAbs ≤ a.num.natAbs * b.den := by
  rw [div_eq_mul_inv]
  exact (natAbs_num_mul_le a b⁻¹).trans (Nat.mul_le_mul_left _ (natAbs_num_inv_le b))

/-- Reduced denominator of `a / b` is bounded by `a.den * max |b.num| 1`. -/
theorem den_div_le (a b : ℚ) : (a / b).den ≤ a.den * max b.num.natAbs 1 := by
  rw [div_eq_mul_inv]
  exact (den_mul_le a b⁻¹).trans (Nat.mul_le_mul_left _ (den_inv_le b))

end Rat

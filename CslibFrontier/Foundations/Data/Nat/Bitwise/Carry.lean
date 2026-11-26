/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Bitwise

/-!
# Bits of successors, predecessors and packed fields

Incrementing a number flips bit `q` exactly when all lower bits are one, and decrementing a
positive number flips it exactly when all lower bits are zero. A number packed from fields of
fixed widths has, in each window of bits, the bits of the corresponding field.

## Main results

* `Nat.testBit_add_one_eq_xor`, `Nat.testBit_sub_one_eq_xor`: the bits of `c + 1` and `c - 1`.
* `Nat.testBit_add_one_eq_ite_forall`, `Nat.testBit_add_one_of_lowest`: lower-bit prefix and
  lowest-zero forms of `Nat.testBit_add_one_eq_xor`.
* `Nat.testBit_sub_two_pow`, `Nat.eq_two_pow_of_testBit`: removing a set bit, and the numbers
  with a single set bit.
* `Nat.testBit_add_four_mul`: the bits of a two-bit tag followed by a payload.
* `Nat.testBit_add_two_pow_mul_add_two_pow_mul`: the bits of three packed fields.
-/

public section

namespace Nat

/-- Bit `q` of `c - 1`, for `1 ≤ c`: bit `q` of `c`, flipped when the lower bits of `c` are
zero. -/
theorem testBit_sub_one_eq_xor {c : ℕ} (hc : 1 ≤ c) (q : ℕ) :
    (c - 1).testBit q = (c.testBit q ^^ decide (c % 2 ^ q = 0)) := by
  induction q generalizing c with
  | zero =>
    simp only [Nat.testBit_zero, pow_zero, Nat.mod_one, decide_true, Bool.xor_true]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Nat.mod_two_not_eq_one]
    omega
  | succ q ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.pow_succ', Nat.mod_mul]
    obtain ⟨d, rfl | rfl⟩ : ∃ d, c = 2 * d ∨ c = 2 * d + 1 := ⟨c / 2, by omega⟩
    · have hd : 1 ≤ d := by omega
      have h₁ : (2 * d - 1) / 2 = d - 1 := by omega
      rw [h₁, Nat.mul_div_right _ Nat.zero_lt_two, ih hd]
      simp
    · simp [Nat.mul_add_div]

/-- Bit `q` of `c + 1`: bit `q` of `c`, flipped when the lower bits of `c` are all one. -/
theorem testBit_add_one_eq_xor (c q : ℕ) :
    (c + 1).testBit q = (c.testBit q ^^ decide (c % 2 ^ q = 2 ^ q - 1)) := by
  induction q generalizing c with
  | zero =>
    simp only [Nat.testBit_zero, pow_zero, Nat.mod_one, Nat.sub_self, decide_true, Bool.xor_true]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Nat.mod_two_not_eq_one]
    omega
  | succ q ih =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.pow_succ', Nat.mod_mul]
    have hq := Nat.one_le_two_pow (n := q)
    obtain ⟨d, rfl | rfl⟩ : ∃ d, c = 2 * d ∨ c = 2 * d + 1 := ⟨c / 2, by omega⟩
    · have hne : ¬ 2 * (d % 2 ^ q) = 2 * 2 ^ q - 1 := by omega
      simp [Nat.mul_add_div, hne]
    · have h₁ : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      have h₂ : (2 * d + 1) / 2 = d := by omega
      rw [h₁, h₂, ih d]
      simp only [Nat.mul_add_mod_self_left, Nat.mod_succ]
      congr 2
      exact propext ⟨fun h => by omega, fun h => by omega⟩

/-- The bits of a tag and a payload. -/
theorem testBit_add_four_mul {tag : ℕ} (htag : tag < 4) (pay i : ℕ) :
    (tag + 4 * pay).testBit i = if i < 2 then tag.testBit i else pay.testBit (i - 2) := by
  rw [Nat.add_comm, show 4 = 2 ^ 2 from rfl, Nat.testBit_two_pow_mul_add _ htag]

/-- The bits of three fields of widths `s` and `cb` and a high field. -/
theorem testBit_add_two_pow_mul_add_two_pow_mul {s cb sl C Tm : ℕ} (hsl : sl < 2 ^ s)
    (hC : C < 2 ^ cb) (q : ℕ) :
    (sl + 2 ^ s * (C + 2 ^ cb * Tm)).testBit q =
      if q < s then sl.testBit q else if q < s + cb then C.testBit (q - s)
      else Tm.testBit (q - s - cb) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hsl, Nat.add_comm C,
    Nat.testBit_two_pow_mul_add _ hC]
  split_ifs <;> first | rfl | omega

/-- Removing a set bit: the bits of `m - 2 ^ a`, when bit `a` of `m` is set, are those of `m`
other than `a`. -/
theorem testBit_sub_two_pow {m a : ℕ} (h : m.testBit a = true) (c : ℕ) :
    (m - 2 ^ a).testBit c = (m.testBit c && decide (c ≠ a)) := by
  have hdm := Nat.div_add_mod m (2 ^ a)
  have hR := Nat.mod_lt m (Nat.two_pow_pos a)
  generalize m / 2 ^ a = Q at hdm
  generalize m % 2 ^ a = R at hdm hR
  subst hdm
  rw [Nat.testBit_two_pow_mul_add _ hR] at h
  have hQ : Q % 2 = 1 := by simpa using h
  obtain ⟨t, rfl⟩ : ∃ t, Q = 2 ^ 1 * t + 1 := ⟨Q / 2, by omega⟩
  have hs : 2 ^ a * (2 ^ 1 * t + 1) + R - 2 ^ a = 2 ^ a * (2 ^ 1 * t + 0) + R := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_zero]
    omega
  rw [hs, Nat.testBit_two_pow_mul_add _ hR, Nat.testBit_two_pow_mul_add _ hR]
  split_ifs with hc
  · simp [show c ≠ a by omega]
  · rw [Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos 1),
      Nat.testBit_two_pow_mul_add _ (by decide : 1 < 2 ^ 1)]
    split_ifs with hc'
    · have : c = a := by omega
      subst this
      simp
    · simp [show c ≠ a by omega]

/-- A natural number whose only set bit is `a` is `2 ^ a`. -/
theorem eq_two_pow_of_testBit {m a : ℕ} (h : ∀ c, m.testBit c = true ↔ c = a) : m = 2 ^ a :=
  Nat.eq_of_testBit_eq fun c => by
    rw [Nat.testBit_two_pow]
    by_cases hc : c = a
    · subst hc
      simpa using (h c).2 rfl
    · rw [decide_eq_false (Ne.symm hc)]
      exact Bool.eq_false_iff.2 fun h' => hc ((h c).1 h')

/-- Bit `q` of `c + 1` flips iff all lower bits `i < q` of `c` are `true`. -/
theorem testBit_add_one_eq_ite_forall (c q : ℕ) :
    (c + 1).testBit q =
      if ∀ i < q, c.testBit i = true then !(c.testBit q) else c.testBit q := by
  have hiff : c % 2 ^ q = 2 ^ q - 1 ↔ ∀ i < q, c.testBit i = true := by
    constructor
    · intro hm i hi
      rw [← Bool.and_true (c.testBit i), Bool.and_comm, ← decide_eq_true hi,
        ← Nat.testBit_mod_two_pow, hm, Nat.testBit_two_pow_sub_one]
    · intro hlow
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < q
      · simp [hi, hlow i hi]
      · simp [hi]
  rw [testBit_add_one_eq_xor]
  by_cases h : ∀ i < q, c.testBit i = true
  · rw [ite_eq_left h, decide_eq_true (hiff.mpr h), Bool.xor_true]
  · rw [ite_eq_right h, decide_eq_false (mt hiff.mp h), Bool.xor_false]

/-- Adding one to `N` complements the bits up to and including its lowest zero bit `j`. -/
theorem testBit_add_one_of_lowest {N j : ℕ} (hj : N.testBit j = false)
    (hlow : ∀ l < j, N.testBit l = true) (l : ℕ) :
    (N + 1).testBit l = if l ≤ j then !N.testBit l else N.testBit l := by
  have hiff : (∀ i < l, N.testBit i = true) ↔ l ≤ j :=
    ⟨fun h => Nat.le_of_not_lt fun hlt => by
      have ht := h j hlt
      rw [hj] at ht
      exact Bool.false_ne_true ht,
     fun h i hi => hlow i (Nat.lt_of_lt_of_le hi h)⟩
  simp only [testBit_add_one_eq_ite_forall, hiff]

end Nat

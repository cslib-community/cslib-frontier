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
* `Nat.testBit_succ_of_lowest`, `Nat.testBit_add_one_of_lowest`,
  `Nat.testBit_add_one_eq_ite_forall`: carry propagation relative to the lowest zero bit or
  lower-bit prefix.
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
    rcases Nat.even_or_odd c with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · have hd : 1 ≤ d := by omega
      have h₁ : (d + d - 1) / 2 = d - 1 := by omega
      have h₂ : (d + d) / 2 = d := by omega
      have h₃ : (d + d) % 2 = 0 := by omega
      rw [h₁, h₂, ih hd, h₃]
      congr 2
      rw [Nat.zero_add, Nat.mul_eq_zero]
      simp
    · have h₁ : (2 * d + 1 - 1) / 2 = d := by omega
      have h₂ : (2 * d + 1) / 2 = d := by omega
      have h₃ : (2 * d + 1) % 2 = 1 := by omega
      rw [h₁, h₂, h₃]
      simp

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
    rcases Nat.even_or_odd c with ⟨d, rfl⟩ | ⟨d, rfl⟩
    · have h₁ : (d + d + 1) / 2 = d := by omega
      have h₂ : (d + d) / 2 = d := by omega
      have h₃ : (d + d) % 2 = 0 := by omega
      rw [h₁, h₂, h₃]
      have : ¬ (2 * (d % 2 ^ q) = 2 * 2 ^ q - 1) := by omega
      simp [this]
    · have h₁ : (2 * d + 1 + 1) / 2 = d + 1 := by omega
      have h₂ : (2 * d + 1) / 2 = d := by omega
      have h₃ : (2 * d + 1) % 2 = 1 := by omega
      rw [h₁, h₂, h₃, ih d]
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

/-- Bit `q` of `c + 1` relative to its lowest zero bit `j`: bits `< j` clear to `false`, bit `j`
sets to `true`, and bits `> j` are unchanged. -/
theorem testBit_succ_of_lowest {N j : ℕ} (hj : N.testBit j = false)
    (hlow : ∀ l < j, N.testBit l = true) (l : ℕ) :
    (N + 1).testBit l = if l < j then false else if l = j then true else N.testBit l := by
  induction j generalizing N l with
  | zero =>
    have h2 : N % 2 = 0 := by
      have := Nat.testBit_zero N
      rw [hj] at this
      rcases Nat.mod_two_eq_zero_or_one N with h | h
      · exact h
      · simp [h] at this
    rcases l with _ | l
    · simp only [Nat.testBit_zero, Nat.lt_irrefl, ↓reduceIte, decide_eq_true_eq]
      omega
    · simp only [Nat.not_lt_zero, ↓reduceIte, Nat.add_one_ne_zero, Nat.testBit_add_one]
      congr 1
      omega
  | succ j ih =>
    have h1 : N % 2 = 1 := by
      have := Nat.testBit_zero N
      rw [hlow 0 (Nat.zero_lt_succ j)] at this
      simpa using this.symm
    have hj' : (N / 2).testBit j = false := by rw [Nat.testBit_div_two]; exact hj
    have hlow' : ∀ l < j, (N / 2).testBit l = true := fun l hl => by
      rw [Nat.testBit_div_two]; exact hlow (l + 1) (by omega)
    rcases l with _ | l
    · simp only [Nat.testBit_zero, Nat.zero_lt_succ, ↓reduceIte, decide_eq_false_iff_not]
      omega
    · rw [Nat.testBit_add_one, show (N + 1) / 2 = N / 2 + 1 by omega, ih hj' hlow' l,
        Nat.testBit_add_one]
      simp only [Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

/-- Adding one to `N` complements the bits up to and including its lowest zero bit `j`. -/
theorem testBit_add_one_of_lowest {N j : ℕ} (hj : N.testBit j = false)
    (hlow : ∀ l < j, N.testBit l = true) (l : ℕ) :
    (N + 1).testBit l = if l ≤ j then !N.testBit l else N.testBit l := by
  rw [testBit_succ_of_lowest hj hlow]
  rcases Nat.lt_trichotomy l j with h | rfl | h
  · simp [h, h.le, hlow l h]
  · simp [hj]
  · simp [show ¬l < j by omega, show l ≠ j by omega, show ¬l ≤ j by omega]

/-- Bit `u` of `k + 1` flips iff all lower bits `j < u` of `k` are `true`. -/
theorem testBit_add_one_eq_ite_forall (k u : ℕ) :
    (k + 1).testBit u =
      if ∀ j < u, k.testBit j = true then !(k.testBit u) else k.testBit u := by
  have hprefix : ∀ m : ℕ,
      (∃ j < m, k.testBit j = false ∧ ∀ l < j, k.testBit l = true) ∨
        (∀ j < m, k.testBit j = true) := by
    intro m
    induction m with
    | zero => exact Or.inr fun _ h => absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      rcases ih with ⟨j, hj, h0, hlow⟩ | hall
      · exact Or.inl ⟨j, Nat.lt_succ_of_lt hj, h0, hlow⟩
      · by_cases hm : k.testBit m = false
        · exact Or.inl ⟨m, Nat.lt_succ_self m, hm, hall⟩
        · refine Or.inr fun j hj => ?_
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
          · exact hall j h
          · exact Bool.eq_true_of_not_eq_false hm
  have hex : ∃ j, k.testBit j = false ∧ ∀ l < j, k.testBit l = true := by
    rcases hprefix (k + u + 2) with ⟨j, _, hj, hlow⟩ | hall
    · exact ⟨j, hj, hlow⟩
    · have hlt : k < 2 ^ (k + u + 1) :=
        Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
      have hfalse := Nat.testBit_lt_two_pow hlt
      have htrue := hall (k + u + 1) (by omega)
      rw [htrue] at hfalse
      contradiction
  rcases hex with ⟨j, hj, hlow⟩
  rw [testBit_add_one_of_lowest hj hlow u]
  rcases Nat.lt_trichotomy u j with hlt | rfl | hgt
  · have hall : ∀ m < u, k.testBit m = true := fun m hm => hlow m (hm.trans hlt)
    rw [ite_eq_left hlt.le, ite_eq_left hall]
  · rw [ite_eq_left (Nat.le_refl u), ite_eq_left hlow]
  · have hnot : ¬ ∀ m < u, k.testBit m = true := fun h => by
      have := h j hgt
      rw [hj] at this
      exact Bool.false_ne_true this
    rw [ite_eq_right (show ¬ u ≤ j by omega), ite_eq_right hnot]

end Nat

/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# A self-delimiting encoding of lists of natural numbers

`NatList.enc` writes a list of natural numbers as one natural number, head in the
low bits. An entry `x` of bit length `n = Nat.size x` takes `2n+1` bits: `n`
ones, a zero, then the `n` bits of `x`. The empty list is `1`, so every code is
positive and no code is a prefix of another.

The code of a list is below `2^(elen l)`, where `elen l = 1 + ∑ (2·size x + 1)`.
The head, the tail and the length of the first entry are read off with
arithmetic (`trailingOnes`, `div`, `mod`), which is what the program terms of
`SumProduct.ListTerm` do.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct.NatList

/-- The code of a list. -/
def enc : List ℕ → ℕ
  | [] => 1
  | x :: l => (2 ^ x.size - 1) + 2 ^ (x.size + 1) * x + 2 ^ (2 * x.size + 1) * enc l

/-- The bit length bound of the code. -/
def elen : List ℕ → ℕ
  | [] => 1
  | x :: l => 2 * x.size + 1 + elen l

@[simp] theorem enc_nil : enc [] = 1 := rfl
theorem enc_cons (x : ℕ) (l : List ℕ) :
    enc (x :: l) = (2 ^ x.size - 1) + 2 ^ (x.size + 1) * x + 2 ^ (2 * x.size + 1) * enc l := rfl
@[simp] theorem elen_nil : elen [] = 1 := rfl
@[simp] theorem elen_cons (x : ℕ) (l : List ℕ) : elen (x :: l) = 2 * x.size + 1 + elen l := rfl

theorem lt_two_pow_size (x : ℕ) : x < 2 ^ x.size := Nat.size_le.mp le_rfl

theorem enc_pos (l : List ℕ) : 1 ≤ enc l := by
  cases l with
  | nil => rfl
  | cons x l =>
    rw [enc_cons]
    have : 1 ≤ 2 ^ (2 * x.size + 1) * enc l :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity)
          (Nat.one_le_iff_ne_zero.mp (enc_pos l)))
    omega

/-- The code is below `2^(elen l)`. -/
theorem enc_lt (l : List ℕ) : enc l < 2 ^ elen l := by
  induction l with
  | nil => simp [enc, elen]
  | cons x l ih =>
    rw [enc_cons, elen_cons]
    set n := x.size
    have hx : x + 1 ≤ 2 ^ n := lt_two_pow_size x
    have hl : enc l + 1 ≤ 2 ^ elen l := ih
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have e2 : 2 ^ (2 * n + 1 + elen l) = 2 ^ (2 * n + 1) * 2 ^ elen l := by ring
    have e3 : 2 ^ (2 * n + 1) = 2 * 2 ^ n * 2 ^ n := by ring
    rw [e1, e2]
    have : 2 * 2 ^ n * x ≤ 2 * 2 ^ n * (2 ^ n - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ (2 * n + 1) * enc l ≤ 2 ^ (2 * n + 1) * (2 ^ elen l - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have : 2 ^ (2 * n + 1) * (2 ^ elen l - 1) + 2 ^ (2 * n + 1) = 2 ^ (2 * n + 1) * 2 ^ elen l := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have : 2 * 2 ^ n * (2 ^ n - 1) + 2 * 2 ^ n = 2 ^ (2 * n + 1) := by
      rw [e3, Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    omega

theorem size_enc_le (l : List ℕ) : (enc l).size ≤ elen l := Nat.size_le.mpr (enc_lt l)

/-! ### Decoding -/

/-- The value above the low `n + 1` bits. -/
theorem enc_cons_div (x : ℕ) (l : List ℕ) :
    enc (x :: l) / 2 ^ (x.size + 1) = x + 2 ^ x.size * enc l := by
  rw [enc_cons]
  have e : 2 ^ (2 * x.size + 1) * enc l = 2 ^ (x.size + 1) * (2 ^ x.size * enc l) := by ring
  rw [e, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (by have := Nat.one_le_two_pow (n := x.size); rw [pow_succ]; omega),
    Nat.zero_add]

theorem enc_cons_head (x : ℕ) (l : List ℕ) :
    enc (x :: l) / 2 ^ (x.size + 1) % 2 ^ x.size = x := by
  rw [enc_cons_div, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_two_pow_size x)]

theorem enc_cons_tail (x : ℕ) (l : List ℕ) :
    enc (x :: l) / 2 ^ (2 * x.size + 1) = enc l := by
  rw [show 2 * x.size + 1 = (x.size + 1) + x.size by ring, pow_add, ← Nat.div_div_eq_div_mul,
    enc_cons_div, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (lt_two_pow_size x),
    Nat.zero_add]

theorem testBit_enc_cons_lt (x : ℕ) (l : List ℕ) {i : ℕ} (hi : i < x.size) :
    (enc (x :: l)).testBit i = true := by
  rw [enc_cons]
  have e : 2 ^ (x.size + 1) * x + 2 ^ (2 * x.size + 1) * enc l =
      2 ^ x.size * (2 * x + 2 ^ (x.size + 1) * enc l) := by ring
  rw [Nat.add_assoc, e, Nat.add_comm,
    Nat.testBit_two_pow_mul_add _ (by have := Nat.one_le_two_pow (n := x.size); omega)]
  simp [hi]

theorem testBit_enc_cons_size (x : ℕ) (l : List ℕ) : (enc (x :: l)).testBit x.size = false := by
  rw [enc_cons]
  have e : 2 ^ (x.size + 1) * x + 2 ^ (2 * x.size + 1) * enc l =
      2 ^ x.size * (2 * (x + 2 ^ x.size * enc l)) := by ring
  rw [Nat.add_assoc, e, Nat.add_comm,
    Nat.testBit_two_pow_mul_add _ (by have := Nat.one_le_two_pow (n := x.size); omega)]
  simp

/-- A cons code is at least `2`; the empty list is `1`. -/
theorem two_le_enc_cons (x : ℕ) (l : List ℕ) : 2 ≤ enc (x :: l) := by
  rw [enc_cons]
  have h1 : 2 ≤ 2 ^ (2 * x.size + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.mul_le_mul h1 (enc_pos l)
  omega

theorem size_lt_enc_cons (x : ℕ) (l : List ℕ) : x.size < enc (x :: l) := by
  have h := Nat.lt_two_pow_self (n := x.size)
  have : 2 ^ (2 * x.size + 1) ≤ 2 ^ (2 * x.size + 1) * enc l :=
      Nat.le_mul_of_pos_right _ (enc_pos l)
  have : 2 ^ x.size ≤ 2 ^ (2 * x.size + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [enc_cons]; omega

theorem le_enc_cons (x : ℕ) (l : List ℕ) : x ≤ enc (x :: l) := by
  rw [enc_cons]
  have : x ≤ 2 ^ (x.size + 1) * x := Nat.le_mul_of_pos_left _ (by positivity)
  omega

theorem enc_le_enc_cons (x : ℕ) (l : List ℕ) : enc l ≤ enc (x :: l) := by
  rw [enc_cons]
  have : enc l ≤ 2 ^ (2 * x.size + 1) * enc l := Nat.le_mul_of_pos_left _ (by positivity)
  omega

theorem two_pow_le_enc_cons (x : ℕ) (l : List ℕ) : 2 ^ (2 * x.size + 1) ≤ enc (x :: l) := by
  rw [enc_cons]
  have := Nat.le_mul_of_pos_right (2 ^ (2 * x.size + 1)) (enc_pos l)
  omega

theorem enc_injective : Function.Injective enc := by
  intro a b h
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y m => have := two_le_enc_cons y m; rw [← h] at this; simp at this
  | cons x l ih =>
    cases b with
    | nil => have := two_le_enc_cons x l; rw [h] at this; simp at this
    | cons y m =>
      -- The first entries have the same size: the first zero bit is at `size`.
      have hs : x.size = y.size := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have h1 := testBit_enc_cons_size x l
          have h2 := testBit_enc_cons_lt y m hlt
          rw [h] at h1; rw [h1] at h2; exact absurd h2 (by simp)
        · have h1 := testBit_enc_cons_size y m
          have h2 := testBit_enc_cons_lt x l hlt
          rw [← h] at h1; rw [h1] at h2; exact absurd h2 (by simp)
      have hx : x = y := by
        have := enc_cons_head x l
        rw [h, hs, enc_cons_head] at this
        exact this.symm
      subst hx
      have := enc_cons_tail x l
      rw [h, enc_cons_tail] at this
      rw [ih this.symm]

end Cslib.Complexity.NtimeDspace.SumProduct.NatList

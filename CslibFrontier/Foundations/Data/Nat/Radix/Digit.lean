/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Nat.Radix

/-!
# Digit sums for fixed-position digits

Lemmas about the fixed-position, zero-padded digits `Cslib.Radix.digit` of
`CslibFrontier/Foundations/Data/Nat/Radix.lean`: a digit is below a positive radix, the first `k`
digits recover `x` modulo `B ^ k`, and the base-`2` digits are the bits of `Nat.testBit`.

## Main results

* `Cslib.Radix.digit_lt`: a digit is below a positive radix.
* `Cslib.Radix.sum_digit_mul_pow`: `∑ i < k, B ^ i * digit B x i = x % B ^ k`.
* `Cslib.Radix.toNat_testBit_eq_digit`: bit `j` of `x` is its base-`2` digit `j`.
* `Nat.sum_two_pow_mul_testBit`: summing the binary place values recovers a bounded natural.
-/

public section

namespace Cslib.Radix

/-- A digit is below a positive radix. -/
theorem digit_lt {B : ℕ} (hB : 0 < B) (x i : ℕ) : digit B x i < B := by
  rw [digit_eq_div_pow_mod]
  exact Nat.mod_lt _ hB

/-- The first `k` base-`B` digits of `x` recover `x` modulo `B ^ k`. -/
theorem sum_digit_mul_pow (B x k : ℕ) :
    ∑ i ∈ Finset.range k, B ^ i * digit B x i = x % B ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, digit_eq_div_pow_mod, Nat.mod_pow_succ]

/-- The bit `j` of `x` is its base-`2` digit `j`. -/
theorem toNat_testBit_eq_digit (x j : ℕ) : (x.testBit j).toNat = digit 2 x j := by
  rw [digit_eq_div_pow_mod, Nat.toNat_testBit]

/-- A natural below `2 ^ w` is the sum of the place values of its first `w` binary digits. -/
theorem _root_.Nat.sum_two_pow_mul_testBit {n w : ℕ} (hn : n < 2 ^ w) :
    (∑ i : Fin w, 2 ^ i.val * (n.testBit i.val).toNat) = n := by
  rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i * (n.testBit i).toNat)]
  simp only [toNat_testBit_eq_digit]
  rw [sum_digit_mul_pow, Nat.mod_eq_of_lt hn]

end Cslib.Radix

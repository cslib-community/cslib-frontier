/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.Bitwise.Packing
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting packed Boolean fields by multiplication

Multiplying packed zero-or-one fields by an all-ones radix word places their sum in
the middle field. A radix larger than the number of fields prevents all carries.
This is an arithmetic identity; a RAM client must separately justify product overflow.

## Main results

* `countPackedFlags`: multiplication, division, and remainder recover the number of set fields.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.BitString

open Finset

private def flagConvolution (n : ℕ) (f : ℕ → Bool) (k : ℕ) : ℕ :=
  ∑ i ∈ range n, if i ≤ k ∧ k - i < n then (f i).toNat else 0

private theorem flagConvolution_eq (n : ℕ) (f : ℕ → Bool) (k : ℕ) :
    flagConvolution n f k =
      ∑ p ∈ range n ×ˢ range n, if p.1 + p.2 = k then (f p.1).toNat else 0 := by
  rw [flagConvolution, sum_product]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ k ∧ k - i < n
  · rw [ite_eq_left h, sum_eq_single (k - i)]
    · simp only [Nat.add_sub_of_le h.1, ite_true]
    · exact fun _ _ _ => ite_eq_right (by omega)
    · simp only [mem_range, h.2, not_true_eq_false, false_implies]
  · rw [ite_eq_right h, eq_comm]
    exact sum_eq_zero fun j hj => ite_eq_right (by have := mem_range.mp hj; omega)

private theorem flagConvolution_le (n : ℕ) (f : ℕ → Bool) (k : ℕ) :
    flagConvolution n f k ≤ n := by
  calc
    flagConvolution n f k ≤ ∑ _i ∈ range n, 1 := sum_le_sum fun i _ => by
      split
      · exact Bool.toNat_le (f i)
      · exact Nat.zero_le 1
    _ = n := by simp

private theorem packRadix_mul_ones (base n : ℕ) (f : ℕ → Bool) :
    packRadix base n (fun i => (f i).toNat) * packRadix base n (fun _ => 1) =
      packRadix base (2 * n) (flagConvolution n f) := by
  rw [packRadix, packRadix, sum_mul_sum]
  simp only [one_mul, mul_assoc, ← pow_add,
    ← sum_product' (range n) (range n) fun i j => (f i).toNat * base ^ (i + j),
    packRadix, flagConvolution_eq, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine (sum_congr rfl fun p hp => ?_).symm
  obtain ⟨hp1, hp2⟩ := mem_product.mp hp
  have hsum : p.1 + p.2 < 2 * n := by
    have := mem_range.mp hp1
    have := mem_range.mp hp2
    omega
  rw [sum_eq_single (p.1 + p.2)]
  · simp
  · exact fun _ _ hk => by simp only [ite_eq_right (Ne.symm hk)]
  · simp only [mem_range, hsum, not_true_eq_false, false_implies]

/-- With fewer fields than the radix, the middle digit of this product counts all set fields.
The product itself can occupy twice the original packed width. -/
theorem countPackedFlags {base n : ℕ} (f : ℕ → Bool) (hn : 0 < n) (hb : n < base) :
    (packRadix base n (fun i => (f i).toNat) * packRadix base n (fun _ => 1)) /
      base ^ (n - 1) % base = ∑ i ∈ range n, (f i).toNat := by
  rw [packRadix_mul_ones, packRadix_field (by omega)
    _ (fun k _ => (flagConvolution_le n f k).trans_lt hb) (by omega)]
  unfold flagConvolution
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_left (by have := mem_range.mp hi; omega)]

end Cslib.BitString

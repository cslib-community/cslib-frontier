/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CslibFrontier.Foundations.Data.Nat.Bitwise.Packing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Bitwise

/-!
# Fixed-width packed `W`-bit word lanes

A natural-number word packs consecutive `W`-bit lanes in little-endian order, with lane `j`
extracted via `(word >>> (j * W)) &&& (2 ^ W - 1)` (`laneGet`). This module provides the shared
pure `Nat` bitwise/radix laws for `laneGet` used by packed SWAR search trees and character tries:
division-and-modulus and bit-level characterizations, lane extensionality, base-`2 ^ W` expansion
of bounded words (`word_eq_sum_laneGet`), and bounded-word digit injectivity
(`eq_of_forall_laneGet_eq_of_lt`). These are pure natural-number identities and make no machine
word-width or runtime claims.

## Main definitions

* `Cslib.DataStructure.laneGet`: extract the `W`-bit lane at index `j` from `word`.

## Main results

* `Cslib.DataStructure.laneGet_eq_div_mod`, `Cslib.DataStructure.laneGet_lt`,
  `Cslib.DataStructure.testBit_laneGet`: arithmetic, range, and bit characterizations of `laneGet`.
* `Cslib.DataStructure.laneGet_sum_mul_pow`, `Cslib.DataStructure.word_eq_sum_laneGet`: lane
  extraction of base-`2 ^ W` sums and base-`2 ^ W` expansion of bounded words.
* `Cslib.DataStructure.eq_of_forall_laneGet_eq`,
  `Cslib.DataStructure.eq_of_forall_laneGet_eq_of_lt`: unbounded and bounded-word lane
  extensionality.
-/

public section

namespace Cslib.DataStructure

open Finset
open scoped BigOperators

/-- Extract the `W`-bit lane at index `j` from `word`. -/
@[expose] def laneGet (W word j : ℕ) : ℕ :=
  (word >>> (j * W)) &&& (2 ^ W - 1)

/-- Division-and-modulus characterization of `laneGet`. -/
theorem laneGet_eq_div_mod (W word j : ℕ) :
    laneGet W word j = (word / 2 ^ (j * W)) % 2 ^ W := by
  unfold laneGet
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

/-- Every extracted `W`-bit lane is strictly less than `2 ^ W`. -/
theorem laneGet_lt (W word j : ℕ) : laneGet W word j < 2 ^ W := by
  rw [laneGet_eq_div_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

/-- Bit `b` of `laneGet W word j` is `word.testBit (j * W + b)` when `b < W`, and `false`
otherwise. -/
theorem testBit_laneGet (W word j b : ℕ) :
    (laneGet W word j).testBit b = (decide (b < W) && word.testBit (j * W + b)) := by
  unfold laneGet
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm,
    Nat.add_comm (j * W) b]

/-- Two words are equal when all of their `W`-bit lanes (`0 < W`) agree. -/
theorem eq_of_forall_laneGet_eq {W a b : ℕ} (hW : 0 < W)
    (h : ∀ k, laneGet W a k = laneGet W b k) : a = b := by
  refine Nat.eq_of_testBit_eq fun t => ?_
  have h1 := congrArg (·.testBit (t % W)) (h (t / W))
  simpa only [testBit_laneGet, Nat.mod_lt t hW, decide_true, Bool.true_and,
    Nat.mul_comm _ W, Nat.div_add_mod] using h1

/-- Extracting lane `k` from a sum of `n` bounded `W`-bit lanes recovers `f k` for `k < n` and `0`
otherwise. -/
theorem laneGet_sum_mul_pow {W n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ W) (k : ℕ) :
    laneGet W (∑ j ∈ range n, f j * 2 ^ (j * W)) k = if k < n then f k else 0 := by
  rw [laneGet_eq_div_mod]
  simp_rw [Nat.pow_mul']
  change BitString.packRadix (2 ^ W) n f / (2 ^ W) ^ k % 2 ^ W = _
  split_ifs with hk
  · exact BitString.packRadix_field (Nat.two_pow_pos W) f hf hk
  · have hfit := (BitString.packRadix_lt f hf).trans_le
      (Nat.pow_le_pow_right (Nat.two_pow_pos W) (Nat.le_of_not_gt hk))
    rw [Nat.div_eq_of_lt hfit, Nat.zero_mod]

/-- Base-`2 ^ W` expansion of any word `< 2 ^ (n * W)` into its first `n` lanes. -/
theorem word_eq_sum_laneGet {W n word : ℕ} (hW : 0 < W) (hw : word < 2 ^ (n * W)) :
    word = ∑ j ∈ range n, laneGet W word j * 2 ^ (j * W) := by
  refine eq_of_forall_laneGet_eq hW fun k => ?_
  rw [laneGet_sum_mul_pow (fun j _ => laneGet_lt W word j)]
  split_ifs with hk
  · rfl
  · refine Nat.eq_of_testBit_eq fun b => ?_
    rw [testBit_laneGet, Nat.zero_testBit]
    by_cases hb : b < W
    · simp only [hb, decide_true, Bool.true_and]
      exact Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right (by decide)
        (by have := Nat.mul_le_mul_right W (Nat.le_of_not_lt hk); omega)))
    · simp [hb]

/-- Words `< 2 ^ (n * W)` are uniquely determined by their first `n` `W`-bit lanes. -/
theorem eq_of_forall_laneGet_eq_of_lt {n W a b : ℕ}
    (ha : a < 2 ^ (n * W)) (hb : b < 2 ^ (n * W))
    (hd : ∀ d < n, laneGet W a d = laneGet W b d) :
    a = b := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp at ha hb; omega
  · rw [word_eq_sum_laneGet hW ha, word_eq_sum_laneGet hW hb]
    exact Finset.sum_congr rfl fun d hd_mem => by rw [hd d (Finset.mem_range.mp hd_mem)]

end Cslib.DataStructure

end

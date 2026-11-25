/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Lex
import Mathlib.Tactic.Ring

/-!
# Binary values, prefixes and the order of words

Facts relating the most-significant-first value `Cslib.BitString.binaryValue` of a word to
concatenation, prefixes and the lexicographic order of words of equal length.

## Main definitions

* `Cslib.BitString.predWord`: the word of the same length whose value is one less.

## Main results

* `Cslib.BitString.binaryValue_append`: the value of a concatenation.
* `Cslib.BitString.binaryValue_lt_iff_lt`, `Cslib.BitString.binaryValue_le_iff_le`: on words of
  equal length, the numeric order is the lexicographic order.
* `Cslib.BitString.isPrefix_iff_binaryValue`: the words with prefix `h` among the words of length
  `N` are those whose values lie in the block `[v(h) 2^(N-|h|), (v(h) + 1) 2^(N-|h|))`.
* `Cslib.BitString.binaryValue_succ_carry`, `Cslib.BitString.exists_carry_cut`,
  `Cslib.BitString.carry_cut_unique`: big-endian `+ 1` carry-cut decomposition before the rightmost
  `false` bit (adapted from *VP ≠ VNP over every field* [AnthropicVPVNP2026], `Nc.Uni.Bin`).
-/

@[expose] public section

namespace Cslib.BitString

/-- The value of a concatenation: the first word is shifted by the length of the second. -/
theorem binaryValue_append (u v : List Bool) :
    binaryValue (u ++ v) = binaryValue u * 2 ^ v.length + binaryValue v := by
  induction v using List.reverseRecOn with
  | nil => simp [binaryValue]
  | append_singleton v b ih =>
    rw [← List.append_assoc, binaryValue_snoc, binaryValue_snoc, ih, List.length_append,
      List.length_singleton, pow_succ]
    ring

/-- The value of a word with a leading bit. -/
theorem binaryValue_cons (b : Bool) (t : List Bool) :
    binaryValue (b :: t) = b.toNat * 2 ^ t.length + binaryValue t := by
  rw [← List.singleton_append, binaryValue_append]
  simp [binaryValue]

/-- Padding a word with `k` ones: the value plus one is multiplied by `2 ^ k`. -/
theorem binaryValue_append_replicate_true (u : List Bool) (k : ℕ) :
    binaryValue (u ++ List.replicate k true) + 1 = (binaryValue u + 1) * 2 ^ k := by
  rw [binaryValue_append, List.length_replicate, add_assoc, binaryValue_replicate_true]
  ring

/-- On words of equal length, the numeric order of `binaryValue` is the strict lexicographic order
(with `false < true`). -/
theorem binaryValue_lt_iff_lt {x y : List Bool} (h : x.length = y.length) :
    binaryValue x < binaryValue y ↔ x < y := by
  induction x generalizing y with
  | nil =>
    obtain rfl : y = [] := List.length_eq_zero_iff.mp h.symm
    simp
  | cons a s ih =>
    obtain ⟨b, t, rfl⟩ := List.exists_cons_of_length_eq_add_one h.symm
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [binaryValue_cons, binaryValue_cons, List.cons_lt_cons_iff, ← ih h, h]
    have hs := binaryValue_lt_two_pow s
    have ht := binaryValue_lt_two_pow t
    rw [h] at hs
    cases a <;> cases b
    all_goals simp only [Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul, zero_add,
      lt_self_iff_false, true_and, false_or, Bool.false_lt_true, Bool.false_eq_true,
      Bool.true_eq_false, false_and, or_false, iff_true, gt_iff_lt, add_lt_add_iff_left]
    all_goals first | omega | exact iff_of_false (by omega) (by decide)

/-- On words of equal length, the numeric order of `binaryValue` is the lexicographic order (with
`false < true`). -/
theorem binaryValue_le_iff_le {x y : List Bool} (h : x.length = y.length) :
    binaryValue x ≤ binaryValue y ↔ x ≤ y := by
  rw [← not_lt, binaryValue_lt_iff_lt h.symm]
  exact List.not_lt

/-- **Prefix blocks.** Among words of length at least `|h|`, the words with prefix `h` are those
whose value lies in `[v(h) 2^(N-|h|), (v(h) + 1) 2^(N-|h|))`, for `N` their length. -/
theorem isPrefix_iff_binaryValue {h r : List Bool} (hlen : h.length ≤ r.length) :
    h <+: r ↔ binaryValue h * 2 ^ (r.length - h.length) ≤ binaryValue r ∧
      binaryValue r < (binaryValue h + 1) * 2 ^ (r.length - h.length) := by
  have hP : 0 < 2 ^ (r.length - h.length) := Nat.two_pow_pos _
  have hdiv : binaryValue r / 2 ^ (r.length - h.length) = binaryValue (r.take h.length) := by
    have hv : binaryValue (r.drop h.length) < 2 ^ (r.length - h.length) :=
      List.length_drop ▸ binaryValue_lt_two_pow (r.drop h.length)
    rw [show binaryValue r = binaryValue (r.take h.length ++ r.drop h.length) from
      congrArg binaryValue (List.take_append_drop h.length r).symm,
      binaryValue_append, List.length_drop, mul_comm, Nat.mul_add_div hP,
      Nat.div_eq_of_lt hv, add_zero]
  rw [← Nat.le_div_iff_mul_le hP, ← Nat.div_lt_iff_lt_mul hP, hdiv, List.prefix_iff_eq_take]
  exact ⟨fun hp => by rw [← hp]; omega,
    fun heq => binaryValue_injective_of_length_eq (by simp [hlen]) (by omega)⟩

/-- The word of the same length as `x` whose value is one less (`x` itself when its value is
`0`). -/
def predWord (x : List Bool) : List Bool :=
  binaryWord x.length (binaryValue x - 1)

theorem length_predWord (x : List Bool) : (predWord x).length = x.length :=
  length_binaryWord (lt_of_le_of_lt (Nat.sub_le _ _) (binaryValue_lt_two_pow x))

@[simp]
theorem binaryValue_predWord (x : List Bool) : binaryValue (predWord x) = binaryValue x - 1 :=
  binaryValue_binaryWord _ _

/-- An all-`false` binary word has value `0`. -/
@[simp]
theorem binaryValue_replicate_false (k : ℕ) :
    binaryValue (List.replicate k false) = 0 := by
  simpa [binaryValue] using binaryValue_replicate_false_append k []

/-- Re-encoding a word's `binaryValue` at its own width recovers the word. -/
@[simp]
theorem binaryWord_binaryValue (w : List Bool) : binaryWord w.length (binaryValue w) = w :=
  binaryValue_injective_of_length_eq (length_binaryWord (binaryValue_lt_two_pow w))
    (binaryValue_binaryWord _ _)

/-- Zero padded to width `L` is `List.replicate L false`. -/
@[simp]
theorem binaryWord_zero (L : ℕ) : binaryWord L 0 = List.replicate L false := by
  have h := binaryWord_binaryValue (List.replicate L false)
  rwa [List.length_replicate, binaryValue_replicate_false] at h

/-- Adding `1` to a big-endian word flips trailing `false :: true^k` to `true :: false^k`. -/
theorem binaryValue_succ_carry (u : List Bool) (k : ℕ) :
    binaryValue (u ++ true :: List.replicate k false) =
      binaryValue (u ++ false :: List.replicate k true) + 1 := by
  have h := binaryValue_append_replicate_true (u ++ [false]) k
  simp only [List.append_assoc, List.singleton_append] at h
  rw [binaryValue_append, binaryValue_cons, binaryValue_replicate_false, List.length_cons,
    List.length_replicate, Bool.toNat_true, one_mul, add_zero, h, binaryValue_snoc,
    Bool.toNat_false, add_zero]
  ring

/-- Every non-maximal big-endian word ends with `false` followed by `true`s. -/
theorem exists_carry_cut {w : List Bool} (h : binaryValue w + 1 < 2 ^ w.length) :
    ∃ u k, w = u ++ false :: List.replicate k true := by
  induction w using List.reverseRecOn with
  | nil => simp [binaryValue] at h
  | append_singleton w b ih =>
    cases b
    · exact ⟨w, 0, rfl⟩
    · rw [binaryValue_snoc, List.length_append, List.length_singleton, pow_succ] at h
      simp only [Bool.toNat_true] at h
      obtain ⟨u, k, rfl⟩ := ih (by omega)
      refine ⟨u, k + 1, ?_⟩
      rw [List.replicate_succ', List.append_assoc]
      rfl

/-- Uniqueness of the decomposition `u ++ false :: true^k` before the rightmost `false`. -/
theorem carry_cut_unique {u u' : List Bool} {k k' : ℕ}
    (h : u ++ false :: List.replicate k true = u' ++ false :: List.replicate k' true) :
    u = u' ∧ k = k' := by
  have h1 := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.singleton_append] at h1
  have key {k k' : ℕ} {a b : List Bool}
      (e : List.replicate k true ++ false :: a = List.replicate k' true ++ false :: b) :
      k = k' ∧ a = b := by
    induction k generalizing k' with
    | zero =>
      cases k' with
      | zero => simpa using e
      | succ _ => simp [List.replicate_succ] at e
    | succ k ih =>
      cases k' with
      | zero => simp [List.replicate_succ] at e
      | succ k' => simpa using ih (by simpa [List.replicate_succ] using e)
  obtain ⟨h2, h3⟩ := key h1
  exact ⟨List.reverse_injective h3, h2⟩

end Cslib.BitString

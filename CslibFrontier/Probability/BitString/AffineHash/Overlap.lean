/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BitString.AffineHash.Word
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.WordCount
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic.Linarith

/-!
# Counting common affine hash hits

For two sets of words of length `n`, count the full seeds whose affine hash to `j` bits
hits zero on both sets. Two independent copies of this test give a constant-factor estimate of
the size of the smaller set after weighting level `j` by `2 ^ j`. Applied to the two preimage
fibers of each sampler output, this estimates their statistical overlap using existential
certificates. This argument is original to the formalization of
[#3205](https://github.com/cslib-community/cslib-frontier/issues/3205).

## Main definitions

* `Cslib.BitString.LinearHash.commonHashHits` collects the full-length seeds that hit both sets.

## Main results

* `Cslib.BitString.LinearHash.commonHashHits_overlap_bounds` bounds the weighted count of
  successful seed pairs above and below in terms of the smaller set's cardinality.
-/

public section

namespace Cslib.BitString.LinearHash

open Finset Probability

variable {n : ℕ}

/-- Full seeds for which the affine hash to `j` bits hits zero on both sets. The first
`j * n + j` bits encode the matrix and offset, with the remaining seed bits ignored. -/
@[expose] def commonHashHits (j : ℕ) (S T : Finset (BitString n)) :
    Finset (BitString (n * n + n)) :=
  univ.filter fun r =>
    let seed := (List.ofFn r).take (j * n + j)
    (∃ x ∈ S, hashZero j n seed (List.ofFn x) = true) ∧
    (∃ x ∈ T, hashZero j n seed (List.ofFn x) = true)

private theorem card_commonHashHits {j : ℕ} (hj : j ≤ n) (S T : Finset (BitString n)) :
    #(commonHashHits j S T) = 2 ^ (n * n + n - (j * n + j)) *
      #{r : (Fin j → BitString n) × BitString j |
        0 ∈ S.image (affineHash r) ∧ 0 ∈ T.image (affineHash r)} := by
  classical
  have hw : j * n + j ≤ n * n + n := Nat.add_le_add (Nat.mul_le_mul_right _ hj) hj
  rw [commonHashHits, card_filter_take hw (fun w =>
    (∃ x ∈ S, hashZero j n w (List.ofFn x) = true) ∧
    (∃ x ∈ T, hashZero j n w (List.ofFn x) = true))]
  congr 1
  simp only [hashZero_ofFn]
  exact card_equiv (affineSeedEquiv j n) fun _ => by simp [mem_image]

private theorem card_commonHashHits_mul_le {j : ℕ} (hj : j ≤ n) (S T : Finset (BitString n)) :
    #(commonHashHits j S T) * 2 ^ j ≤ min #S #T * 2 ^ (n * n + n) := by
  classical
  let E := (Fin j → BitString n) × BitString j
  have hcard : Fintype.card E = 2 ^ (j * n + j) := by
    rw [← Fintype.card_congr (affineSeedEquiv j n), BitString.card]
  let U := univ.filter (fun r : E => 0 ∈ S.image (affineHash r) ∧ 0 ∈ T.image (affineHash r))
  have bound (A : Finset (BitString n)) (ha : ∀ r ∈ U, 0 ∈ A.image (affineHash r)) :
      #U * 2 ^ j ≤ #A * Fintype.card E := by
    have h := (isPairwiseIndependentHash_affineHash j n).card_filter_mem_image_mul_le A 0
    rw [BitString.card] at h
    exact (Nat.mul_le_mul_right _ (card_le_card (fun r hr => mem_filter.mpr
      ⟨mem_univ _, ha r hr⟩))).trans h
  have hsmall : #U * 2 ^ j ≤ min #S #T * Fintype.card E := by
    rcases le_total #S #T with h | h
    · rw [min_eq_left h]
      exact bound _ fun r hr => (mem_filter.mp hr).2.1
    · rw [min_eq_right h]
      exact bound _ fun r hr => (mem_filter.mp hr).2.2
  have hw : j * n + j ≤ n * n + n := Nat.add_le_add (Nat.mul_le_mul_right _ hj) hj
  rw [card_commonHashHits hj, mul_assoc]
  rw [hcard] at hsmall
  calc
    _ ≤ 2 ^ (n * n + n - (j * n + j)) * (min #S #T * 2 ^ (j * n + j)) :=
      Nat.mul_le_mul_left _ hsmall
    _ = _ := by rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hw]

private theorem le_two_mul_card_commonHashHits {j : ℕ} (hj : j ≤ n)
    (S T : Finset (BitString n)) (hm : 4 * 2 ^ j ≤ min #S #T) :
    2 ^ (n * n + n) ≤ 2 * #(commonHashHits j S T) := by
  classical
  let E := (Fin j → BitString n) × BitString j
  let hits (A : Finset (BitString n)) : Finset E := univ.filter fun r => 0 ∈ A.image (affineHash r)
  -- Each set misses zero on at most a quarter of the seeds.
  have hlarge (A : Finset (BitString n)) (hA : 4 * 2 ^ j ≤ #A) :
      3 * Fintype.card E ≤ 4 * #(hits A) := by
    have h := (isPairwiseIndependentHash_affineHash j n).four_mul_card_filter_notMem_image_le
      (by simpa only [BitString.card] using hA) (0 : BitString j)
    have ht := card_filter_add_card_filter_not (s := univ) (fun r : E => 0 ∈ A.image (affineHash r))
    rw [card_univ] at ht
    have h' : 4 * #{r : E | 0 ∉ A.image (affineHash r)} ≤ Fintype.card E := h
    have sum : #(hits A) + #{r : E | 0 ∉ A.image (affineHash r)} = Fintype.card E := ht
    omega
  have hs := hlarge S (hm.trans (min_le_left _ _))
  have ht := hlarge T (hm.trans (min_le_right _ _))
  have hi := card_union_add_card_inter (hits S) (hits T)
  have hu := card_le_univ (hits S ∪ hits T)
  have bound : Fintype.card E ≤ 2 * #(hits S ∩ hits T) := by omega
  have hcard : Fintype.card E = 2 ^ (j * n + j) := by
    rw [← Fintype.card_congr (affineSeedEquiv j n), BitString.card]
  have hw : j * n + j ≤ n * n + n := Nat.add_le_add (Nat.mul_le_mul_right _ hj) hj
  rw [card_commonHashHits hj, filter_and, mul_left_comm]
  simpa only [hcard, ← pow_add, Nat.sub_add_cancel hw, hits] using
    Nat.mul_le_mul_left (2 ^ (n * n + n - (j * n + j))) bound

private theorem card_commonHashHits_zero (S T : Finset (BitString n)) (hs : S.Nonempty)
    (ht : T.Nonempty) : #(commonHashHits 0 S T) = 2 ^ (n * n + n) := by
  rw [card_commonHashHits (Nat.zero_le _) S T]
  have h (s : (Fin 0 → BitString n) × BitString 0) (A : Finset (BitString n)) (ha : A.Nonempty) :
      0 ∈ A.image (affineHash s) := by
    obtain ⟨x, hx⟩ := ha
    exact mem_image.mpr ⟨x, hx, Subsingleton.elim _ _⟩
  have hf : (univ.filter fun r : (Fin 0 → BitString n) × BitString 0 =>
      0 ∈ S.image (affineHash r) ∧ 0 ∈ T.image (affineHash r)) = univ :=
    Finset.filter_true_of_mem fun r _ => ⟨h r S hs, h r T ht⟩
  rw [hf, card_univ, ← Fintype.card_congr (affineSeedEquiv 0 n), BitString.card]
  simp

/-- Summing integer counts whose upper bounds halve at each successive level. -/
private theorem sum_dyadic_tail (m A : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i < m, 2 ^ i * f i ≤ A) : ∑ i ∈ range m, f i ≤ 2 * A := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    have h0 := hf 0 (Nat.zero_lt_succ _)
    have hrest := ih (fun i => 2 * f (i + 1)) fun i hi => by
      simpa only [pow_succ, mul_assoc] using hf (i + 1) (Nat.succ_lt_succ hi)
    rw [← mul_sum] at hrest
    rw [sum_range_succ']
    simp only [pow_zero, one_mul] at h0
    omega

private theorem overlap_upper (n a B : ℕ) (h : ℕ → ℕ) (ha : a ≠ 0) (han : a ≤ 2 ^ n)
    (hB : ∀ j ≤ n, h j ≤ B) (hsmall : ∀ j ≤ n, h j * 2 ^ j ≤ a * B) :
    ∑ j ∈ range (n + 1), 2 ^ j * h j ^ 2 ≤ 4 * B ^ 2 * a := by
  let k := Nat.log 2 a
  have hk : k ≤ n := (Nat.log_mono_right han).trans_eq (Nat.log_pow (by decide) n)
  have hl : 2 ^ k ≤ a := Nat.pow_log_le_self _ ha
  have hu : a ≤ 2 ^ (k + 1) := (Nat.lt_pow_succ_log_self (by decide) a).le
  let f (j : ℕ) := 2 ^ j * h j ^ 2
  -- Up through floor(log₂ a), bound each seed count by the whole seed space.
  have hlow : ∑ j ∈ range (k + 1), f j ≤ 2 * B ^ 2 * a := calc
    _ ≤ ∑ j ∈ range (k + 1), 2 ^ j * B ^ 2 := sum_le_sum fun j hj =>
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hB _ (by have := mem_range.mp hj; omega)) _)
    _ = (∑ j ∈ range (k + 1), 2 ^ j) * B ^ 2 := (sum_mul ..).symm
    _ ≤ 2 ^ (k + 1) * B ^ 2 := by
      gcongr
      simpa only [Nat.geomSum_eq (by decide : 2 ≤ 2), Nat.reduceSub, Nat.div_one] using
        Nat.sub_le (2 ^ (k + 1)) 1
    _ ≤ _ := by rw [pow_succ]; nlinarith [Nat.mul_le_mul_right (B ^ 2) hl]
  -- Above that level, squaring the hit probability leaves a summable geometric tail.
  have hhigh : ∑ i ∈ range (n - k), f (k + 1 + i) ≤ 2 * (a * B ^ 2) := by
    apply sum_dyadic_tail
    intro i hi
    let j := k + 1 + i
    have hj : j ≤ n := by dsimp [j]; omega
    have hsq := Nat.pow_le_pow_left (hsmall j hj) 2
    have hp : (2 : ℕ) ^ j = 2 ^ (k + 1) * 2 ^ i := pow_add ..
    change 2 ^ i * (2 ^ j * h j ^ 2) ≤ a * B ^ 2
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ (k + 1)) _ (by positivity)
    calc
      _ = (h j * 2 ^ j) ^ 2 := by rw [hp]; ring
      _ ≤ (a * B) ^ 2 := hsq
      _ ≤ _ := by nlinarith [Nat.mul_le_mul_right (a * B ^ 2) hu]
  change ∑ j ∈ range (n + 1), f j ≤ _
  rw [show n + 1 = (k + 1) + (n - k) by omega, sum_range_add]
  nlinarith only [hlow, hhigh]

/-- The weighted number of pairs of common hitting seeds estimates the smaller fiber
cardinality up to absolute constants, after dividing by the total number of seed pairs. -/
theorem commonHashHits_overlap_bounds (S T : Finset (BitString n)) :
    (2 ^ (n * n + n)) ^ 2 * min #S #T ≤
      32 * ∑ j ∈ range (n + 1), 2 ^ j * #(commonHashHits j S T) ^ 2 ∧
    (∑ j ∈ range (n + 1), 2 ^ j * #(commonHashHits j S T) ^ 2) ≤
      4 * (2 ^ (n * n + n)) ^ 2 * min #S #T := by
  let a := min #S #T
  let B := 2 ^ (n * n + n)
  let h (j : ℕ) := #(commonHashHits j S T)
  let f (j : ℕ) := 2 ^ j * h j ^ 2
  have hsmall (j : ℕ) (hj : j ≤ n) : h j * 2 ^ j ≤ a * B := card_commonHashHits_mul_le hj S T
  change B ^ 2 * a ≤ 32 * ∑ j ∈ range (n + 1), f j ∧
    (∑ j ∈ range (n + 1), f j) ≤ 4 * B ^ 2 * a
  by_cases ha : a = 0
  · have hempty (j : ℕ) (hj : j ∈ range (n + 1)) : f j = 0 := by
      have hz := hsmall j (by have := mem_range.mp hj; omega)
      rw [ha, zero_mul, Nat.le_zero, mul_eq_zero] at hz
      simp [f, hz.resolve_right (by positivity)]
    simp [ha, sum_eq_zero hempty]
  have han : a ≤ 2 ^ n := (min_le_left _ _).trans
    (by simpa only [BitString.card] using card_le_univ S)
  have hB (j : ℕ) (_ : j ≤ n) : h j ≤ B := by
    simpa only [BitString.card] using card_le_univ (commonHashHits j S T)
  refine ⟨?_, overlap_upper n a B h ha han hB hsmall⟩
  have single (j : ℕ) (hj : j ≤ n) : f j ≤ ∑ i ∈ range (n + 1), f i :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  let k := Nat.log 2 a
  have hk : k ≤ n := (Nat.log_mono_right han).trans_eq (Nat.log_pow (by decide) n)
  have hu : a < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) a
  -- One level suffices for the lower bound: zero for tiny fibers, two below log₂ a otherwise.
  by_cases hk' : k < 2
  · have hu' : a ≤ 3 := by
      have hp : (2 : ℕ) ^ (k + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hs : S.Nonempty := card_pos.mp <|
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero ha) (min_le_left _ _)
    have ht : T.Nonempty := card_pos.mp <|
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero ha) (min_le_right _ _)
    have h0 : h 0 = B := card_commonHashHits_zero S T hs ht
    have hterm := single 0 (Nat.zero_le _)
    simp only [f, pow_zero, one_mul, h0] at hterm
    dsimp only [f] at ⊢
    nlinarith [Nat.mul_le_mul_left (B ^ 2) hu']
  · let j := k - 2
    have hj : j ≤ n := by dsimp [j]; omega
    have hjk : k = j + 2 := by dsimp [j]; omega
    have hl : 4 * 2 ^ j ≤ a := by
      have := Nat.pow_log_le_self 2 ha
      change 2 ^ k ≤ a at this
      simpa only [hjk, pow_add, Nat.reducePow, mul_comm] using this
    have h8 : a ≤ 8 * 2 ^ j := by
      rw [hjk, show j + 2 + 1 = j + 3 by omega, pow_add] at hu
      linarith
    have hb : B ≤ 2 * h j := le_two_mul_card_commonHashHits hj S T hl
    have hterm := single j hj
    dsimp only [f] at hterm ⊢
    nlinarith [Nat.mul_le_mul (Nat.pow_le_pow_left hb 2) h8]

end Cslib.BitString.LinearHash

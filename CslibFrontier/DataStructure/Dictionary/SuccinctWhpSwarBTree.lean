/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.PackedLane
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# SWAR Parallel Word-Lane Rank and Top-Down Split-Only B+-Tree Query-Mapper

This module formalizes the pure word-level SWAR (SIMD Within A Register) lane operations and the
bounded-height top-down split-only B+-tree used as the intra-bucket fingerprint query-mapper in the
with-high-probability succinct dynamic dictionary.

## Original adaptation vs. SOSA 2024 Section 4

In [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024, Section 4, Lemma 4.2,
pp. 363–373; author copy p. 5][BenderFarachColtonKuszmaulKuszmaul2024], each bucket's query-mapper
is a `B = √(log n)` B-tree navigated via exhaustive Four-Russians subtabulation lookup tables. Here
we replace the Four-Russians table with an original **SWAR top-down split-only B+-tree** using only
standard arithmetic and bitwise word operations (`+`, `-`, `*`, `/`, `%`, `&&&`, `|||`, `^^^`,
`<<<`, `>>>`):
1. **SWAR parallel rank (`swarRank_eq_count_lt`)**: packing `m < 2 * tMin` keys into lanes of width
   `W_lane = fpBits + 2` inside a single `< 2 ^ ⌊log₂ n_max⌋` word, borrow-free parallel subtraction
   and multiplication by `swarOnes` count `# { j < m | k_j < q }` in `O(1)` word operations.
2. **Top-down proactive splitting and lazy deletion**: proactive root-to-leaf splitting of full
   (`2 * tMin - 1`-key) nodes via `splitFullNode` (`NodeSplit`) maintains strict separator intervals
   `(s_{j-1}, s_j]` without bottom-up backtracking, while `btreeDelete` removes keys directly from
   leaves via `wordDeleteAt` with zero sibling borrows or merges. The excess-key split potential
   (`BTreeTree.potential`) bounds total allocated nodes after `I` insertions (and arbitrarily many
   deletions) by `1 + 2 * I / (tMin - 2) < nSliceWhp`, and branching `≥ tMin` bounds tree height by
   `hMaxBTree = 42`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.wordTakeLow`, `wordDropLow`, `wordInsertAt`,
  `wordDeleteAt`, `wordUpdateAt`, `swarOnes`, `ltMask`, `swarRank`: pure SWAR lane update and
  parallel-rank operations (built on `Cslib.DataStructure.laneGet` in
  `CslibFrontier/DataStructure/PackedLane.lean`).
* `Cslib.DataStructure.Dictionary.SuccinctWhp.BTreeNode`, `NodeSplit`, `BTreeSlice`,
  `splitFullNode`, `finishLeafInsert`, `btreeLookup`, `btreeInsert`, `btreeDelete`, `btreeUpdate`,
  `hMaxBTree`: pure bounded-depth top-down split-only SWAR B+-tree operations.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.swarRank_eq_count_lt`:
  exact equality between `swarRank` and
  `#((Finset.range m).filter fun j => laneGet W keysWord j < q)`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidSubtree.frame`:
  frame invariance of `ValidSubtree` under updates outside `T.nodeSet`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidSubtree.two_mul_pow_height_sub_one_le_leafCount`:
  branching lower bound `2 * tMin ^ (T.height - 1) ≤ T.leafCount` for every valid subtree of height
  `≥ 1`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Section 4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Finset
open scoped BigOperators

/-! ## Section 1: Pure SWAR word-lane operations and parallel rank -/

/-- Retain the low `j` lanes (`j * W` bits) of `word`. -/
@[expose] def wordTakeLow (W j word : ℕ) : ℕ :=
  word &&& (2 ^ (j * W) - 1)

/-- Drop the low `j` lanes (`j * W` bits) of `word`. -/
@[expose] def wordDropLow (W j word : ℕ) : ℕ :=
  word >>> (j * W)

/-- Insert `W`-bit value `v` at lane `j`, shifting lanes `≥ j` up by one lane. -/
@[expose] def wordInsertAt (W j v word : ℕ) : ℕ :=
  wordTakeLow W j word + ((v + (wordDropLow W j word <<< W)) <<< (j * W))

/-- Delete lane `j`, shifting lanes `≥ j + 1` down by one lane. -/
@[expose] def wordDeleteAt (W j word : ℕ) : ℕ :=
  wordTakeLow W j word + ((word >>> ((j + 1) * W)) <<< (j * W))

/-- Overwrite lane `j` with `W`-bit value `v`. -/
@[expose] def wordUpdateAt (W j v word : ℕ) : ℕ :=
  wordTakeLow W j word + ((v + ((word >>> ((j + 1) * W)) <<< W)) <<< (j * W))

/-- Closed-form mask `∑_{j < n} 2 ^ (j * W) = (2 ^ (n * W) - 1) / (2 ^ W - 1)`. -/
@[expose] def swarOnes (W n : ℕ) : ℕ :=
  (2 ^ (n * W) - 1) / (2 ^ W - 1)

/-- Borrow-free parallel `< q` lane indicator mask across `m` lanes of width `fpBits + 2`. -/
@[expose] def ltMask (fpBits m q keysWord : ℕ) : ℕ :=
  let W := fpBits + 2
  let onesM := swarOnes W m
  (((2 ^ fpBits + q) * onesM - (keysWord + onesM)) >>> fpBits) &&& onesM

/-- Word-parallel SWAR rank `# { j < m | laneGet (fpBits + 2) keysWord j < q }`. -/
@[expose] def swarRank (fpBits capLanes m q keysWord : ℕ) : ℕ :=
  let W := fpBits + 2
  ((ltMask fpBits m q keysWord * swarOnes W capLanes) >>> ((capLanes - 1) * W)) &&& (2 ^ W - 1)

/-- Modulus characterization of `wordTakeLow`. -/
theorem wordTakeLow_eq_mod (W j word : ℕ) :
    wordTakeLow W j word = word % 2 ^ (j * W) :=
  Nat.and_two_pow_sub_one_eq_mod word (j * W)

/-- Retaining the low `j` lanes produces a word `< 2 ^ (j * W)`. -/
theorem wordTakeLow_lt (W j word : ℕ) : wordTakeLow W j word < 2 ^ (j * W) := by
  rw [wordTakeLow_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Division characterization of `wordDropLow`. -/
theorem wordDropLow_eq_div (W j word : ℕ) :
    wordDropLow W j word = word / 2 ^ (j * W) :=
  Nat.shiftRight_eq_div_pow word (j * W)

/-- Dropping the low `a` lanes of a word `< 2 ^ ((a + b) * W)` produces a word `< 2 ^ (b * W)`. -/
theorem wordDropLow_lt {W a b word : ℕ} (hw : word < 2 ^ ((a + b) * W)) :
    wordDropLow W a word < 2 ^ (b * W) := by
  rw [wordDropLow_eq_div]
  exact Nat.div_lt_of_lt_mul (by rwa [← Nat.pow_add, ← Nat.add_mul])

/-- Bit `i * W + b`, for `b < W`, lies below bit `j * W` exactly when lane `i` lies below
lane `j`. -/
private theorem lane_bit_lt_iff {W i j b : ℕ} (hb : b < W) : i * W + b < j * W ↔ i < j :=
  ⟨fun h => lt_of_not_ge fun hij => by have := Nat.mul_le_mul_right W hij; omega,
   fun h => by
     have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h)
     rw [Nat.succ_mul] at this; omega⟩

/-- Lane extraction from `wordTakeLow` returns `laneGet W word i` for `i < j` and `0` otherwise. -/
theorem laneGet_wordTakeLow (W j word i : ℕ) :
    laneGet W (wordTakeLow W j word) i = if i < j then laneGet W word i else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_laneGet, wordTakeLow, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hb : b < W
  · split_ifs with hij <;> simp [testBit_laneGet, hb, hij, lane_bit_lt_iff hb]
  · split_ifs <;> simp [testBit_laneGet, hb]

/-- Lane `i` of `a + c <<< (j * W)`, for `a < 2 ^ (j * W)`. -/
private theorem laneGet_add_shiftLeft {W j a c : ℕ} (ha : a < 2 ^ (j * W)) (i : ℕ) :
    laneGet W (a + c <<< (j * W)) i = if i < j then laneGet W a i else laneGet W c (i - j) := by
  rw [Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt ha]
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < W
  · split_ifs with hij
    · have h := (lane_bit_lt_iff hb).mpr hij
      simp [testBit_laneGet, Nat.testBit_shiftLeft, hb, not_le.mpr h]
    · have hle := Nat.mul_le_mul_right W (not_lt.mp hij)
      have ha0 : a.testBit (i * W + b) = false :=
        Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      have hsub : i * W + b - j * W = (i - j) * W + b := by rw [Nat.sub_mul]; omega
      simp [testBit_laneGet, Nat.testBit_shiftLeft, hb, ha0, hsub, show j * W ≤ i * W + b by omega]
  · split_ifs <;> simp [testBit_laneGet, hb]

/-- Lane `i` of `wordDropLow W j word` equals lane `j + i` of `word`. -/
theorem laneGet_wordDropLow (W j word i : ℕ) :
    laneGet W (wordDropLow W j word) i = laneGet W word (j + i) := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_laneGet, testBit_laneGet, wordDropLow, Nat.testBit_shiftRight]
  congr 2
  ring

/-- Lane extraction after inserting `v < 2 ^ W` at lane `j`. -/
theorem laneGet_wordInsertAt {W j v word : ℕ} (hv : v < 2 ^ W) (i : ℕ) :
    laneGet W (wordInsertAt W j v word) i =
      if i < j then laneGet W word i
      else if i = j then v
      else laneGet W word (i - 1) := by
  have hin := laneGet_add_shiftLeft (W := W) (j := 1) (c := wordDropLow W j word)
    (by rwa [one_mul]) (i - j)
  rw [one_mul] at hin
  rw [wordInsertAt, laneGet_add_shiftLeft (wordTakeLow_lt W j word), laneGet_wordTakeLow, hin,
    laneGet_wordDropLow]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h]
  · simp [laneGet_eq_div_mod, Nat.mod_eq_of_lt hv]
  · simp [show ¬i < j by omega, h.ne', show ¬i - j < 1 by omega,
      show j + (i - j - 1) = i - 1 by omega]

/-- Lane extraction after deleting lane `j`. -/
theorem laneGet_wordDeleteAt (W j word i : ℕ) :
    laneGet W (wordDeleteAt W j word) i =
      if i < j then laneGet W word i else laneGet W word (i + 1) := by
  rw [wordDeleteAt, laneGet_add_shiftLeft (wordTakeLow_lt W j word), laneGet_wordTakeLow,
    show word >>> ((j + 1) * W) = wordDropLow W (j + 1) word from rfl, laneGet_wordDropLow]
  split_ifs with h
  · rfl
  · congr 1
    omega

private theorem wordUpdateAt_eq_wordInsertAt_wordDeleteAt (W j v word : ℕ) :
    wordUpdateAt W j v word = wordInsertAt W j v (wordDeleteAt W j word) := by
  unfold wordUpdateAt wordInsertAt wordDeleteAt
  have hlow : wordTakeLow W j (wordTakeLow W j word +
      ((word >>> ((j + 1) * W)) <<< (j * W))) = wordTakeLow W j word := by
    rw [wordTakeLow_eq_mod, wordTakeLow_eq_mod, Nat.shiftLeft_eq,
      Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hdrop : wordDropLow W j (wordTakeLow W j word +
      ((word >>> ((j + 1) * W)) <<< (j * W))) = word >>> ((j + 1) * W) := by
    rw [wordDropLow_eq_div, Nat.shiftLeft_eq,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (wordTakeLow_lt W j word), Nat.zero_add]
  rw [hlow, hdrop]

/-- Lane extraction after overwriting lane `j` with `v < 2 ^ W`. -/
theorem laneGet_wordUpdateAt {W j v word : ℕ} (hv : v < 2 ^ W) (i : ℕ) :
    laneGet W (wordUpdateAt W j v word) i =
      if i = j then v else laneGet W word i := by
  rw [wordUpdateAt_eq_wordInsertAt_wordDeleteAt, laneGet_wordInsertAt hv]
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · simp [hlt, hlt.ne, laneGet_wordDeleteAt]
  · simp
  · simp [show ¬i < j by omega, hgt.ne', laneGet_wordDeleteAt, show ¬i - 1 < j by omega,
      show i - 1 + 1 = i by omega]

/-- `a + c <<< (j * W) < 2 ^ ((j + n) * W)` when `a < 2 ^ (j * W)` and `c < 2 ^ (n * W)`. -/
private theorem add_shiftLeft_lt {W j n a c : ℕ} (ha : a < 2 ^ (j * W)) (hc : c < 2 ^ (n * W)) :
    a + c <<< (j * W) < 2 ^ ((j + n) * W) := by
  rw [Nat.shiftLeft_eq, Nat.add_mul, Nat.pow_add]
  calc a + c * 2 ^ (j * W) < (c + 1) * 2 ^ (j * W) := by rw [Nat.succ_mul]; omega
    _ ≤ 2 ^ (n * W) * 2 ^ (j * W) := Nat.mul_le_mul_right _ hc
    _ = _ := Nat.mul_comm _ _

/-- Inserting `v < 2 ^ W` at lane `j ≤ m` of a word `< 2 ^ (m * W)` produces a word
`< 2 ^ ((m + 1) * W)`. -/
theorem wordInsertAt_lt {W j m v word : ℕ} (hj : j ≤ m) (hv : v < 2 ^ W)
    (hw : word < 2 ^ (m * W)) :
    wordInsertAt W j v word < 2 ^ ((m + 1) * W) := by
  have hdrop : wordDropLow W j word < 2 ^ ((m - j) * W) :=
    wordDropLow_lt (by rwa [Nat.add_sub_cancel' hj])
  have hmid := add_shiftLeft_lt (j := 1) (by rwa [one_mul]) hdrop
  rw [one_mul] at hmid
  have h := add_shiftLeft_lt (wordTakeLow_lt W j word) hmid
  rwa [show j + (1 + (m - j)) = m + 1 by omega] at h

/-- Deleting lane `j ≤ m` of a word `< 2 ^ ((m + 1) * W)` produces a word `< 2 ^ (m * W)`. -/
theorem wordDeleteAt_lt {W j m word : ℕ} (hj : j ≤ m) (hw : word < 2 ^ ((m + 1) * W)) :
    wordDeleteAt W j word < 2 ^ (m * W) := by
  have hhi : word >>> ((j + 1) * W) < 2 ^ ((m - j) * W) :=
    wordDropLow_lt (by rwa [show j + 1 + (m - j) = m + 1 by omega])
  have h := add_shiftLeft_lt (wordTakeLow_lt W j word) hhi
  rwa [Nat.add_sub_cancel' hj] at h

/-- Overwriting lane `j < m` with `v < 2 ^ W` preserves the `< 2 ^ (m * W)` bound. -/
theorem wordUpdateAt_lt {W j m v word : ℕ} (hj : j < m) (hv : v < 2 ^ W)
    (hw : word < 2 ^ (m * W)) :
    wordUpdateAt W j v word < 2 ^ (m * W) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [wordUpdateAt_eq_wordInsertAt_wordDeleteAt]
  exact wordInsertAt_lt (by omega) hv (wordDeleteAt_lt (by omega) hw)
/-! ### `swarOnes`, `ltMask`, and `swarRank_eq_count_lt` -/

theorem swarOnes_eq_sum {W : ℕ} (hW : 1 ≤ W) (n : ℕ) :
    swarOnes W n = ∑ j ∈ range n, 2 ^ (j * W) := by
  have hpos : 0 < 2 ^ W - 1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hgeom (k : ℕ) : (∑ j ∈ range k, 2 ^ (j * W)) * (2 ^ W - 1) = 2 ^ (k * W) - 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, Nat.add_mul, ih]
      have h1 : 1 ≤ 2 ^ (k * W) := Nat.one_le_two_pow
      have h2 : 2 ^ (k * W) * (2 ^ W - 1) = 2 ^ ((k + 1) * W) - 2 ^ (k * W) := by
        rw [Nat.mul_sub, mul_one, ← Nat.pow_add, Nat.add_mul, one_mul]
      have h3 : 2 ^ (k * W) ≤ 2 ^ ((k + 1) * W) :=
        Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right W (Nat.le_succ k))
      omega
  unfold swarOnes
  rw [← hgeom n, Nat.mul_div_cancel _ hpos]

private theorem ltMask_eq_sum (fpBits m q keysWord : ℕ)
    (hq : q < 2 ^ fpBits) (hkw : keysWord < 2 ^ (m * (fpBits + 2)))
    (hlanes : ∀ j < m, laneGet (fpBits + 2) keysWord j < 2 ^ fpBits) :
    ltMask fpBits m q keysWord =
      ∑ j ∈ range m,
        (if laneGet (fpBits + 2) keysWord j < q then 1 else 0) * 2 ^ (j * (fpBits + 2)) := by
  set W := fpBits + 2
  have hW : 1 ≤ W := by omega
  have hW_pos : 0 < W := by omega
  let d (j : ℕ) : ℕ := (2 ^ fpBits + q) - (laneGet W keysWord j + 1)
  have hd_lt : ∀ j < m, d j < 2 ^ W := fun j hj => by
    have := hlanes j hj
    have := Nat.two_pow_pos fpBits
    dsimp only [d, W]
    rw [Nat.pow_add]
    omega
  have hdiff_eq : (2 ^ fpBits + q) * swarOnes W m - (keysWord + swarOnes W m) =
      ∑ j ∈ range m, d j * 2 ^ (j * W) := by
    have hkw_sum := word_eq_sum_laneGet hW_pos hkw
    have hones := swarOnes_eq_sum hW m
    have hsum_add : (∑ j ∈ range m, d j * 2 ^ (j * W)) + (keysWord + swarOnes W m) =
        (2 ^ fpBits + q) * swarOnes W m := by
      conv_lhs => rw [hkw_sum, hones, ← sum_add_distrib, ← sum_add_distrib]
      rw [hones, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hk : laneGet W keysWord j < 2 ^ fpBits := hlanes j (mem_range.mp hj)
      dsimp only [d]
      have hsub : 2 ^ fpBits + q - (laneGet W keysWord j + 1) +
          (laneGet W keysWord j + 1) = 2 ^ fpBits + q := by omega
      calc (2 ^ fpBits + q - (laneGet W keysWord j + 1)) * 2 ^ (j * W) +
            (laneGet W keysWord j * 2 ^ (j * W) + 2 ^ (j * W))
          = (2 ^ fpBits + q - (laneGet W keysWord j + 1) +
              (laneGet W keysWord j + 1)) * 2 ^ (j * W) := by ring
        _ = (2 ^ fpBits + q) * 2 ^ (j * W) := by rw [hsub]
    omega
  refine eq_of_forall_laneGet_eq hW_pos fun k => ?_
  have h2W : 1 < 2 ^ W := Nat.one_lt_two_pow (by omega)
  rw [laneGet_sum_mul_pow (fun j _ => by split_ifs <;> omega)]
  unfold ltMask
  change laneGet W ((((2 ^ fpBits + q) * swarOnes W m - (keysWord + swarOnes W m)) >>> fpBits) &&&
      swarOnes W m) k = _
  rw [hdiff_eq]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_laneGet]
  by_cases hb : b < W
  · simp only [hb, decide_true, Bool.true_and, Nat.testBit_and, Nat.testBit_shiftRight]
    have h1_tb_succ : ∀ n, (1 : ℕ).testBit (n + 1) = false := fun n => by
      simp [Nat.testBit_succ]
    have hones_tb : (swarOnes W m).testBit (k * W + b) = decide (k < m ∧ b = 0) := by
      have hl := testBit_laneGet W (swarOnes W m) k b
      have hf1 : ∑ j ∈ range m, 2 ^ (j * W) = ∑ j ∈ range m, 1 * 2 ^ (j * W) :=
        sum_congr rfl fun _ _ => (one_mul _).symm
      rw [swarOnes_eq_sum hW m, hf1, laneGet_sum_mul_pow (fun _ _ => h2W)] at hl
      simp only [hb, decide_true, Bool.true_and] at hl
      rw [swarOnes_eq_sum hW m, hf1, ← hl]
      split_ifs with hkm <;> rcases b with _ | b' <;> simp [hkm, h1_tb_succ]
    rw [hones_tb]
    by_cases hkm : k < m
    · rcases b with _ | b'
      · simp only [hkm, and_self, decide_true, Bool.and_true, Nat.add_zero]
        have hfp_lt : fpBits < W := by omega
        have hl_d := testBit_laneGet W (∑ j ∈ range m, d j * 2 ^ (j * W)) k fpBits
        rw [laneGet_sum_mul_pow hd_lt] at hl_d
        simp only [hkm, ↓reduceIte, hfp_lt, decide_true, Bool.true_and] at hl_d
        rw [Nat.add_comm fpBits (k * W), ← hl_d]
        have hk_lt := hlanes k hkm
        by_cases hlt_q : laneGet W keysWord k < q
        · simp only [hlt_q, ↓reduceIte, Nat.testBit_zero]
          have hdiv1 : d k / 2 ^ fpBits = 1 :=
            Nat.div_eq_of_lt_le (by dsimp only [d]; omega) (by dsimp only [d]; omega)
          rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv1]
          rfl
        · simp only [hlt_q, ↓reduceIte, Nat.zero_testBit]
          exact Nat.testBit_lt_two_pow (by dsimp only [d]; omega)
      · simp only [hkm, ↓reduceIte, Nat.succ_ne_zero, and_false, decide_false, Bool.and_false]
        split_ifs <;> simp [h1_tb_succ]
    · simp [hkm]
  · simp only [hb, decide_false, Bool.false_and]
    split_ifs
    · exact (Nat.testBit_lt_two_pow
        (h2W.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm
    all_goals simp

/-- **Exact SWAR parallel rank theorem**:
whenever `m < capLanes`, `capLanes < 2 ^ (fpBits + 2)`, `q < 2 ^ fpBits`,
`keysWord < 2 ^ (m * (fpBits + 2))`, and every lane `j < m` satisfies
`laneGet (fpBits + 2) keysWord j < 2 ^ fpBits`, `swarRank` equals the exact count of lanes `< m`
strictly smaller than `q`. -/
theorem swarRank_eq_count_lt {fpBits capLanes m q keysWord : ℕ}
    (hm : m < capLanes) (hcap : capLanes < 2 ^ (fpBits + 2))
    (hq : q < 2 ^ fpBits) (hkw : keysWord < 2 ^ (m * (fpBits + 2)))
    (hlanes : ∀ j < m, laneGet (fpBits + 2) keysWord j < 2 ^ fpBits) :
    swarRank fpBits capLanes m q keysWord =
      #((range m).filter fun j => laneGet (fpBits + 2) keysWord j < q) := by
  set W := fpBits + 2
  have hW : 1 ≤ W := by omega
  have hcap_pos : 1 ≤ capLanes := by omega
  let b (j : ℕ) : ℕ := if laneGet W keysWord j < q then 1 else 0
  have hlt_eq := ltMask_eq_sum fpBits m q keysWord hq hkw hlanes
  let P := range m ×ˢ range capLanes
  let c (s : ℕ) : ℕ := ∑ p ∈ P.filter (fun p => p.1 + p.2 = s), b p.1
  have hc_lt : ∀ s < 2 * capLanes, c s < 2 ^ W := fun s _ => by
    calc c s ≤ #(P.filter fun p => p.1 + p.2 = s) := by
          rw [card_eq_sum_ones]
          exact sum_le_sum fun p _ => by dsimp only [b]; split_ifs <;> omega
      _ ≤ #(range m) := by
          refine card_le_card_of_injOn Prod.fst (fun p hp => ?_) ?_
          · exact (mem_product.mp (mem_filter.mp hp).1).1
          · rintro ⟨j₁, i₁⟩ h₁ ⟨j₂, i₂⟩ h₂ (rfl : j₁ = j₂)
            have e₁ := (mem_filter.mp h₁).2
            have e₂ := (mem_filter.mp h₂).2
            exact Prod.ext rfl (by omega)
      _ < 2 ^ W := by rw [card_range]; exact hm.trans hcap
  have hprod_eq : ltMask fpBits m q keysWord * swarOnes W capLanes =
      ∑ s ∈ range (2 * capLanes), c s * 2 ^ (s * W) := by
    rw [hlt_eq, swarOnes_eq_sum hW capLanes, sum_mul_sum, ← sum_product']
    have hmaps : ∀ p ∈ P, p.1 + p.2 ∈ range (2 * capLanes) := fun p hp => by
      simp only [P, mem_product, mem_range] at hp ⊢
      omega
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl fun s _ => ?_
    dsimp only [c]
    rw [sum_mul]
    refine sum_congr rfl fun p hp => ?_
    dsimp only [b, W]
    rw [mul_assoc, ← Nat.pow_add, ← Nat.add_mul, (mem_filter.mp hp).2]
  change laneGet W (ltMask fpBits m q keysWord * swarOnes W capLanes) (capLanes - 1) = _
  rw [hprod_eq, laneGet_sum_mul_pow hc_lt]
  have hlt_2cap : capLanes - 1 < 2 * capLanes := by omega
  simp only [hlt_2cap, ↓reduceIte, c]
  have hbij : ∑ p ∈ P.filter (fun p => p.1 + p.2 = capLanes - 1), b p.1 =
      ∑ j ∈ range m, b j := by
    refine sum_nbij' (fun p => p.1) (fun j => (j, capLanes - 1 - j))
      (fun p hp => (mem_product.mp (mem_filter.mp hp).1).1)
      (fun j hj => by
        have hjm : j < m := mem_range.mp hj
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hj, mem_range.mpr (by omega)⟩, by omega⟩)
      (fun p hp => by
        rcases p with ⟨j, i⟩
        have he := (mem_filter.mp hp).2
        exact Prod.ext rfl (by dsimp at he ⊢; omega))
      (fun _ _ => rfl)
      (fun _ _ => rfl)
  rw [hbij]
  dsimp only [b]
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]

/-! ## Section 2: Iterative Top-Down Split-Only SWAR B+-Tree -/

/-- Worst-case height bound `42` for any SWAR B+-tree slice at `whpThreshold c ≤ n_max` with at
most `8 * (slabScale n_max) ^ 12` insertions (`2 * tMin ^ 41 > nSliceWhp n_max` since
`slabScale ≤ tMin ^ 3`). Kept opaque across module boundaries (with `hMaxBTree_eq`) so symbolic
proofs do not unfold 42 recursion steps in the kernel. -/
def hMaxBTree : ℕ := 42

/-- Explicit numerical value `hMaxBTree = 42`. -/
theorem hMaxBTree_eq : hMaxBTree = 42 := by rfl

/-- Packed representation of a single SWAR B+-tree node (`metaWord = isLeafBit + 2 * keyCount`,
`keysWord`, `valsWord`). -/
structure BTreeNode where
  /-- Packed `isLeaf` bit (`metaWord % 2`) and key count (`metaWord / 2`). -/
  metaWord : ℕ
  /-- Packed sorted `W_key`-bit fingerprint lanes. -/
  keysWord : ℕ
  /-- Packed `W_val`-bit value lanes (for leaves) or child node indices (for internal nodes). -/
  valsWord : ℕ
  deriving DecidableEq

/-- Pack `(isLeaf, keyCount)` into `metaWord`. -/
@[expose] def mkNodeMeta (isLeaf : Bool) (cnt : ℕ) : ℕ :=
  (if isLeaf then 1 else 0) + 2 * cnt

/-- Extract `isLeaf` from `metaWord`. -/
@[expose] def metaIsLeaf (metaWord : ℕ) : Bool :=
  metaWord % 2 == 1

/-- Extract `keyCount` from `metaWord`. -/
@[expose] def metaCount (metaWord : ℕ) : ℕ :=
  metaWord / 2

/-- `metaIsLeaf` recovers the `isLeaf` flag packed by `mkNodeMeta`. -/
@[simp]
theorem metaIsLeaf_mkNodeMeta (b : Bool) (cnt : ℕ) :
    metaIsLeaf (mkNodeMeta b cnt) = b := by
  cases b <;> simp [metaIsLeaf, mkNodeMeta, Nat.add_mul_mod_self_left]

/-- `metaCount` recovers the key count packed by `mkNodeMeta`. -/
@[simp]
theorem metaCount_mkNodeMeta (b : Bool) (cnt : ℕ) :
    metaCount (mkNodeMeta b cnt) = cnt := by
  cases b <;> simp only [metaCount, mkNodeMeta, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Pure state of a single SWAR B+-tree slice (`alloc` allocated nodes `0 .. alloc - 1`, `root`
index, and node map `nodes`). -/
structure BTreeSlice where
  /-- Number of allocated nodes (`0` denotes an uninitialized empty slice). -/
  alloc : ℕ
  /-- Root node index (`< alloc` when `0 < alloc`). -/
  root : ℕ
  /-- Node array indexed by `0 .. alloc - 1`. -/
  nodes : ℕ → BTreeNode

/-- Empty initialized 1-leaf `BTreeSlice` (`alloc = 1`, `root = 0`, empty leaf at `0`). -/
@[expose] def emptyBTreeSlice : BTreeSlice where
  alloc := 1
  root := 0
  nodes := fun _ => ⟨mkNodeMeta true 0, 0, 0⟩

/-- Ensure a slice has at least its initial empty root leaf allocated (`alloc = 0 ↦ emptyBTreeSlice`
in 1 node write at index `0`). -/
@[expose] def ensureRootSlice (sl : BTreeSlice) : BTreeSlice :=
  if sl.alloc = 0 then
    { alloc := 1, root := 0, nodes := Function.update sl.nodes 0 ⟨mkNodeMeta true 0, 0, 0⟩ }
  else sl

/-- Bounded root-to-leaf descent finding the leaf node containing interval `q`. -/
@[expose] def descendToLeaf (fpBits W_val tMin : ℕ) (nodes : ℕ → BTreeNode) :
    ℕ → ℕ → ℕ → ℕ
  | 0, cur, _ => cur
  | fuel + 1, cur, q =>
    let nd := nodes cur
    if metaIsLeaf nd.metaWord then cur
    else
      let r := swarRank fpBits (2 * tMin) (metaCount nd.metaWord) q nd.keysWord
      descendToLeaf fpBits W_val tMin nodes fuel (laneGet W_val nd.valsWord r) q

/-- Pure SWAR B+-tree lookup of fingerprint `q < 2 ^ fpBits`. -/
@[expose] def btreeLookup (fpBits W_val tMin : ℕ) (sl : BTreeSlice) (q : ℕ) : Option ℕ :=
  if sl.alloc = 0 then none
  else
    let W_key := fpBits + 2
    let leafIdx := descendToLeaf fpBits W_val tMin sl.nodes hMaxBTree sl.root q
    let nd := sl.nodes leafIdx
    let cnt := metaCount nd.metaWord
    let r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
    if r < cnt && laneGet W_key nd.keysWord r == q then
      some (laneGet W_val nd.valsWord r)
    else none

/-- Pure SWAR B+-tree lazy leaf deletion of fingerprint `q` (`0` node allocations, no borrows). -/
@[expose] def btreeDelete (fpBits W_val tMin : ℕ) (sl : BTreeSlice) (q : ℕ) : BTreeSlice :=
  if sl.alloc = 0 then sl
  else
    let W_key := fpBits + 2
    let leafIdx := descendToLeaf fpBits W_val tMin sl.nodes hMaxBTree sl.root q
    let nd := sl.nodes leafIdx
    let cnt := metaCount nd.metaWord
    let r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
    if r < cnt && laneGet W_key nd.keysWord r == q then
      let nd' : BTreeNode :=
        ⟨mkNodeMeta true (cnt - 1),
          wordDeleteAt W_key r nd.keysWord,
          wordDeleteAt W_val r nd.valsWord⟩
      { sl with nodes := Function.update sl.nodes leafIdx nd' }
    else sl

/-- Pure SWAR B+-tree in-place value update for an existing fingerprint `q`. -/
@[expose] def btreeUpdate (fpBits W_val tMin : ℕ) (sl : BTreeSlice) (q newVal : ℕ) :
    BTreeSlice :=
  if sl.alloc = 0 then sl
  else
    let W_key := fpBits + 2
    let leafIdx := descendToLeaf fpBits W_val tMin sl.nodes hMaxBTree sl.root q
    let nd := sl.nodes leafIdx
    let cnt := metaCount nd.metaWord
    let r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
    if r < cnt && laneGet W_key nd.keysWord r == q then
      let nd' : BTreeNode :=
        ⟨nd.metaWord, nd.keysWord, wordUpdateAt W_val r newVal nd.valsWord⟩
      { sl with nodes := Function.update sl.nodes leafIdx nd' }
    else sl

/-- Output record of splitting a full (`2 * tMin - 1`-key) `BTreeNode` into a left node, promoted
separator key, and right node. -/
structure NodeSplit where
  /-- Left split node covering keys `≤ sep`. -/
  left : BTreeNode
  /-- Promoted separator key `s_{tMin - 1}`. -/
  sep : ℕ
  /-- Right split node covering keys `> sep`. -/
  right : BTreeNode
  deriving DecidableEq

/-- Split a full (`2 * tMin - 1`-key) node `nd` into `⟨left, sep, right⟩` under the
`(s_{j-1}, s_j]` interval convention:
* If `nd` is a leaf: `left` keeps the low `tMin` entries (`0 .. tMin - 1`), `sep` is
  `k_{tMin - 1}`, and `right` keeps the high `tMin - 1` entries (`tMin .. 2 * tMin - 2`).
* If `nd` is internal: `left` keeps `tMin - 1` separators (`0 .. tMin - 2`) and `tMin` children
  (`0 .. tMin - 1`), `sep` is `s_{tMin - 1}`, and `right` keeps `tMin - 1` separators
  (`tMin .. 2 * tMin - 2`) and `tMin` children (`tMin .. 2 * tMin - 1`). -/
@[expose] def splitFullNode (fpBits W_val tMin : ℕ) (nd : BTreeNode) : NodeSplit :=
  let W_key := fpBits + 2
  let sep := laneGet W_key nd.keysWord (tMin - 1)
  if metaIsLeaf nd.metaWord then
    let leftNd : BTreeNode :=
      ⟨mkNodeMeta true tMin,
        wordTakeLow W_key tMin nd.keysWord,
        wordTakeLow W_val tMin nd.valsWord⟩
    let rightNd : BTreeNode :=
      ⟨mkNodeMeta true (tMin - 1),
        wordDropLow W_key tMin nd.keysWord,
        wordDropLow W_val tMin nd.valsWord⟩
    ⟨leftNd, sep, rightNd⟩
  else
    let leftNd : BTreeNode :=
      ⟨mkNodeMeta false (tMin - 1),
        wordTakeLow W_key (tMin - 1) nd.keysWord,
        wordTakeLow W_val tMin nd.valsWord⟩
    let rightNd : BTreeNode :=
      ⟨mkNodeMeta false (tMin - 1),
        wordDropLow W_key tMin nd.keysWord,
        wordDropLow W_val tMin nd.valsWord⟩
    ⟨leftNd, sep, rightNd⟩

/-- Proactive root split if `sl.root` has `2 * tMin - 1` keys: allocates `leftIdx = sl.alloc` and
`rightIdx = sl.alloc + 1`, updating `sl.root` in place to the 1-separator internal root. -/
@[expose] def splitRootIfFull (fpBits W_val tMin : ℕ) (sl : BTreeSlice) : BTreeSlice :=
  let rootNd := sl.nodes sl.root
  if metaCount rootNd.metaWord == 2 * tMin - 1 then
    let W_val' := W_val
    let ⟨leftNd, sep, rightNd⟩ := splitFullNode fpBits W_val' tMin rootNd
    let leftIdx := sl.alloc
    let rightIdx := sl.alloc + 1
    let newVals := leftIdx + (rightIdx <<< W_val')
    let newRootNd : BTreeNode := ⟨mkNodeMeta false 1, sep, newVals⟩
    let nodes1 := Function.update sl.nodes leftIdx leftNd
    let nodes2 := Function.update nodes1 rightIdx rightNd
    let nodes3 := Function.update nodes2 sl.root newRootNd
    { alloc := sl.alloc + 2, root := sl.root, nodes := nodes3 }
  else sl

/-- Bounded top-down proactive-splitting descent from a non-full node `cur` to the target non-full
leaf for `q`. -/
@[expose] def descendSplitToLeaf (fpBits W_val tMin : ℕ) :
    ℕ → BTreeSlice → ℕ → ℕ → BTreeSlice × ℕ
  | 0, sl, cur, _ => (sl, cur)
  | fuel + 1, sl, cur, q =>
    let nd := sl.nodes cur
    if metaIsLeaf nd.metaWord then (sl, cur)
    else
      let W_key := fpBits + 2
      let cnt := metaCount nd.metaWord
      let r := swarRank fpBits (2 * tMin) cnt q nd.keysWord
      let childIdx := laneGet W_val nd.valsWord r
      let childNd := sl.nodes childIdx
      if metaCount childNd.metaWord == 2 * tMin - 1 then
        let ⟨leftNd, sep, rightNd⟩ := splitFullNode fpBits W_val tMin childNd
        let rightIdx := sl.alloc
        let parentNd' : BTreeNode :=
          ⟨mkNodeMeta false (cnt + 1),
            wordInsertAt W_key r sep nd.keysWord,
            wordInsertAt W_val (r + 1) rightIdx nd.valsWord⟩
        let nodes1 := Function.update sl.nodes childIdx leftNd
        let nodes2 := Function.update nodes1 rightIdx rightNd
        let nodes3 := Function.update nodes2 cur parentNd'
        let sl' : BTreeSlice := { sl with alloc := sl.alloc + 1, nodes := nodes3 }
        let nextChild := if sep < q then rightIdx else childIdx
        descendSplitToLeaf fpBits W_val tMin fuel sl' nextChild q
      else
        descendSplitToLeaf fpBits W_val tMin fuel sl childIdx q

/-- Leaf insertion/overwrite post-step of `btreeInsert`. -/
@[expose] def finishLeafInsert (fpBits W_val tMin : ℕ) (sl : BTreeSlice) (leafIdx q val : ℕ) :
    BTreeSlice :=
  let W_key := fpBits + 2
  let leafNd := sl.nodes leafIdx
  let cnt := metaCount leafNd.metaWord
  let r := swarRank fpBits (2 * tMin) cnt q leafNd.keysWord
  if r < cnt && laneGet W_key leafNd.keysWord r == q then
    let leafNd' : BTreeNode :=
      ⟨leafNd.metaWord, leafNd.keysWord, wordUpdateAt W_val r val leafNd.valsWord⟩
    { sl with nodes := Function.update sl.nodes leafIdx leafNd' }
  else
    let leafNd' : BTreeNode :=
      ⟨mkNodeMeta true (cnt + 1),
        wordInsertAt W_key r q leafNd.keysWord,
        wordInsertAt W_val r val leafNd.valsWord⟩
    { sl with nodes := Function.update sl.nodes leafIdx leafNd' }

/-- Pure top-down split-only SWAR B+-tree insertion (or in-place value overwrite if `q` is already
present). -/
@[expose] def btreeInsert (fpBits W_val tMin : ℕ) (sl : BTreeSlice) (q val : ℕ) : BTreeSlice :=
  let sl0 := ensureRootSlice sl
  let sl1 := splitRootIfFull fpBits W_val tMin sl0
  let p := descendSplitToLeaf fpBits W_val tMin hMaxBTree sl1 sl1.root q
  finishLeafInsert fpBits W_val tMin p.1 p.2 q val

/-! ## Section 3: Algebraic spine `BTreeTree`, `ValidSubtree`, and excess-key split potential -/

/-- Pure inductive spine witnessing the tree structure of a `BTreeSlice`. -/
inductive BTreeTree : Type
  | leaf (idx cnt : ℕ) : BTreeTree
  | branch (idx cnt : ℕ) (cs : Fin (cnt + 1) → BTreeTree) : BTreeTree

/-- Root node index of `T`. -/
@[expose] def BTreeTree.rootIdx : BTreeTree → ℕ
  | .leaf idx _ => idx
  | .branch idx _ _ => idx

/-- Height of `T` (`0` for a leaf). -/
@[expose] def BTreeTree.height : BTreeTree → ℕ
  | .leaf _ _ => 0
  | .branch _ _ cs => 1 + univ.sup fun i => (cs i).height

/-- Set of physical slice node indices occupied by `T`. -/
@[expose] def BTreeTree.nodeSet : BTreeTree → Finset ℕ
  | .leaf idx _ => {idx}
  | .branch idx _ cs => insert idx (univ.biUnion fun i => (cs i).nodeSet)

/-- Number of leaves in `T`. -/
@[expose] def BTreeTree.leafCount : BTreeTree → ℕ
  | .leaf _ _ => 1
  | .branch _ _ cs => ∑ i, (cs i).leafCount

/-- Excess-key split potential `∑_{v ∈ T} (keyCount v - (tMin - 1))`. -/
@[expose] def BTreeTree.potential (tMin : ℕ) : BTreeTree → ℕ
  | .leaf _ cnt => cnt - (tMin - 1)
  | .branch _ cnt cs => (cnt - (tMin - 1)) + ∑ i, (cs i).potential tMin

/-- The root index of `T` belongs to `T.nodeSet`. -/
theorem BTreeTree.rootIdx_mem_nodeSet (T : BTreeTree) : T.rootIdx ∈ T.nodeSet := by
  cases T <;> simp [rootIdx, nodeSet]

/-- Left interval endpoint for child `r` of an internal node on `[lo, hi]` with `keysWord`. -/
@[expose] def childLo (W_key lo keysWord r : ℕ) : ℕ :=
  if r = 0 then lo else laneGet W_key keysWord (r - 1) + 1

/-- Right interval endpoint for child `r` of an internal node with `cnt` separators on
`[lo, hi]`. -/
@[expose] def childHi (W_key hi cnt keysWord r : ℕ) : ℕ :=
  if r < cnt then laneGet W_key keysWord r else hi

/-- When the sorted separator keys in `keysWord` start at `≥ lo`, every child `r ≤ cnt` has
`lo ≤ childLo W_key lo keysWord r`. -/
theorem le_childLo {W_key lo cnt keysWord r : ℕ}
    (hr : r ≤ cnt) (hlo0 : lo ≤ laneGet W_key keysWord 0)
    (hmono : ∀ i j, i < j → j < cnt → laneGet W_key keysWord i < laneGet W_key keysWord j) :
    lo ≤ childLo W_key lo keysWord r := by
  unfold childLo
  split_ifs with hr0
  · exact le_rfl
  · rcases eq_or_lt_of_le (Nat.zero_le (r - 1)) with heq0 | hpos
    · rw [← heq0]; exact hlo0.trans (Nat.le_succ _)
    · exact (hlo0.trans (hmono 0 (r - 1) hpos (by omega)).le).trans (Nat.le_succ _)

/-- When the sorted separator keys in `keysWord` end at `≤ hi`, every index `r` has
`childHi W_key hi cnt keysWord r ≤ hi`. -/
theorem childHi_le {W_key hi cnt keysWord r : ℕ}
    (hhi_last : laneGet W_key keysWord (cnt - 1) ≤ hi)
    (hmono : ∀ i j, i < j → j < cnt → laneGet W_key keysWord i < laneGet W_key keysWord j) :
    childHi W_key hi cnt keysWord r ≤ hi := by
  unfold childHi
  split_ifs with hrc
  · rcases eq_or_lt_of_le (by omega : r ≤ cnt - 1) with heq | hlt
    · rwa [heq]
    · exact (hmono r (cnt - 1) hlt (by omega)).le.trans hhi_last
  · exact le_rfl

/-- Structural, ordering, disjointness, equal-depth, and map-refinement invariant for a subtree `T`
covering keys in `[lo, hi]`. -/
@[expose] def ValidSubtree (isRoot : Bool) (fpBits W_val tMin alloc : ℕ) (nodes : ℕ → BTreeNode)
    (lo hi : ℕ) (mapFn : ℕ → Option ℕ) : BTreeTree → Prop
  | .leaf idx cnt =>
    let W_key := fpBits + 2
    let nd := nodes idx
    idx < alloc ∧
    nd.metaWord = mkNodeMeta true cnt ∧
    cnt ≤ 2 * tMin - 1 ∧
    nd.keysWord < 2 ^ (cnt * W_key) ∧
    nd.valsWord < 2 ^ (cnt * W_val) ∧
    (∀ j < cnt, lo ≤ laneGet W_key nd.keysWord j ∧ laneGet W_key nd.keysWord j ≤ hi) ∧
    (∀ i j, i < j → j < cnt → laneGet W_key nd.keysWord i < laneGet W_key nd.keysWord j) ∧
    (∀ q, lo ≤ q → q ≤ hi →
      (∃ r < cnt, laneGet W_key nd.keysWord r = q ∧
        mapFn q = some (laneGet W_val nd.valsWord r)) ∨
      ((∀ r < cnt, laneGet W_key nd.keysWord r ≠ q) ∧ mapFn q = none))
  | .branch idx cnt cs =>
    let W_key := fpBits + 2
    let nd := nodes idx
    idx < alloc ∧
    nd.metaWord = mkNodeMeta false cnt ∧
    (if isRoot then 1 ≤ cnt else tMin - 1 ≤ cnt) ∧
    cnt ≤ 2 * tMin - 1 ∧
    nd.keysWord < 2 ^ (cnt * W_key) ∧
    nd.valsWord < 2 ^ ((cnt + 1) * W_val) ∧
    lo ≤ laneGet W_key nd.keysWord 0 ∧
    laneGet W_key nd.keysWord (cnt - 1) < hi ∧
    (∀ i j, i < j → j < cnt → laneGet W_key nd.keysWord i < laneGet W_key nd.keysWord j) ∧
    (∀ i, idx ∉ (cs i).nodeSet) ∧
    (∀ i j, i ≠ j → Disjoint (cs i).nodeSet (cs j).nodeSet) ∧
    (∀ i : Fin (cnt + 1), (cs i).height = (cs ⟨0, Nat.succ_pos cnt⟩).height) ∧
    (∀ i : Fin (cnt + 1),
      laneGet W_val nd.valsWord i.val = (cs i).rootIdx ∧
      ValidSubtree false fpBits W_val tMin alloc nodes
        (childLo W_key lo nd.keysWord i.val) (childHi W_key hi cnt nd.keysWord i.val)
        mapFn (cs i))

/-- Frame invariance of `ValidSubtree` under updates outside `T.nodeSet` and monotone `alloc`. -/
theorem ValidSubtree.frame {isRoot : Bool} {fpBits W_val tMin alloc alloc' : ℕ}
    {nodes nodes' : ℕ → BTreeNode} {lo hi : ℕ} {mapFn mapFn' : ℕ → Option ℕ} {T : BTreeTree}
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T)
    (halloc : alloc ≤ alloc')
    (hnodes : ∀ v ∈ T.nodeSet, nodes' v = nodes v)
    (hmap : ∀ q, lo ≤ q → q ≤ hi → mapFn' q = mapFn q) :
    ValidSubtree isRoot fpBits W_val tMin alloc' nodes' lo hi mapFn' T := by
  induction T generalizing isRoot lo hi with
  | leaf idx cnt =>
    have hidx : nodes' idx = nodes idx := hnodes idx (by simp [BTreeTree.nodeSet])
    obtain ⟨h1, h2, h4, h5, h6, h7, h8, h9⟩ := hv
    exact ⟨h1.trans_le halloc, hidx ▸ h2, h4, hidx ▸ h5, hidx ▸ h6, hidx ▸ h7, hidx ▸ h8,
      fun q hlo hhi => hmap q hlo hhi ▸ hidx ▸ h9 q hlo hhi⟩
  | branch idx cnt cs ih =>
    have hidx : nodes' idx = nodes idx := hnodes idx (by simp [BTreeTree.nodeSet])
    obtain ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, hht, h13⟩ := hv
    refine ⟨h1.trans_le halloc, hidx ▸ h2, h4, h5, hidx ▸ h6, hidx ▸ h7, hidx ▸ h8, hidx ▸ h9,
      hidx ▸ h10, h11, h12, hht, fun i => ?_⟩
    rw [hidx]
    exact ⟨(h13 i).1, ih i (h13 i).2
      (fun v hv_in => hnodes v (mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ i, hv_in⟩)))
      fun q hqlo hqhi => hmap q ((le_childLo (Nat.le_of_lt_succ i.isLt) h8 h10).trans hqlo)
        (hqhi.trans (childHi_le h9.le h10))⟩

/-- Every node in `T.nodeSet` is strictly below `alloc`, and `T.leafCount ≤ #T.nodeSet ≤ alloc`. -/
theorem ValidSubtree.leafCount_le_card_nodeSet {isRoot : Bool} {fpBits W_val tMin alloc : ℕ}
    {nodes : ℕ → BTreeNode} {lo hi : ℕ} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T) :
    (∀ v ∈ T.nodeSet, v < alloc) ∧ T.leafCount ≤ #T.nodeSet := by
  induction T generalizing isRoot lo hi with
  | leaf idx cnt =>
    exact ⟨fun v hv_in => (mem_singleton.mp hv_in) ▸ hv.1,
      by simp [BTreeTree.leafCount, BTreeTree.nodeSet]⟩
  | branch idx cnt cs ih =>
    obtain ⟨hidx, _, _, _, _, _, _, _, _, hnot, hdisj, _, hcs⟩ := hv
    have hrec := fun i => ih i (hcs i).2
    refine ⟨fun v hv_in => ?_, ?_⟩
    · rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
      rcases hv_in with rfl | ⟨i, _, hvi⟩
      · exact hidx
      · exact (hrec i).1 v hvi
    · rw [BTreeTree.leafCount, BTreeTree.nodeSet,
        card_insert_of_notMem (by
          simpa only [mem_biUnion, not_exists, not_and] using fun i _ => hnot i),
        card_biUnion fun i _ j _ hij => hdisj i j hij]
      exact (sum_le_sum fun i _ => (hrec i).2).trans (Nat.le_succ _)

/-- A valid subtree occupies at most `alloc` physical slice nodes. -/
theorem ValidSubtree.card_nodeSet_le_alloc {isRoot : Bool} {fpBits W_val tMin alloc : ℕ}
    {nodes : ℕ → BTreeNode} {lo hi : ℕ} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T) :
    #T.nodeSet ≤ alloc :=
  card_range alloc ▸ card_le_card fun v hv_in =>
    mem_range.mpr (hv.leafCount_le_card_nodeSet.1 v hv_in)

/-- For any branch whose children all share `(cs 0).height`, `height = 1 + (cs 0).height`. -/
theorem BTreeTree.height_branch_of_eq {idx cnt : ℕ} {cs : Fin (cnt + 1) → BTreeTree}
    (hht : ∀ i : Fin (cnt + 1), (cs i).height = (cs ⟨0, Nat.succ_pos cnt⟩).height) :
    (BTreeTree.branch idx cnt cs).height = 1 + (cs ⟨0, Nat.succ_pos cnt⟩).height := by
  rw [BTreeTree.height]
  exact congrArg (1 + ·) (le_antisymm (Finset.sup_le fun i _ => (hht i).le)
    (Finset.le_sup (f := fun i => (cs i).height) (mem_univ (Fin.mk 0 (Nat.succ_pos cnt)))))

/-- Non-root valid subtrees (`isRoot = false`) have `tMin ^ T.height ≤ T.leafCount`. -/
private theorem ValidSubtree.pow_height_le_leafCount_nonroot {fpBits W_val tMin alloc : ℕ}
    {nodes : ℕ → BTreeNode} {lo hi : ℕ} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht1 : 1 ≤ tMin)
    (hv : ValidSubtree false fpBits W_val tMin alloc nodes lo hi mapFn T) :
    tMin ^ T.height ≤ T.leafCount := by
  induction T generalizing lo hi with
  | leaf idx cnt =>
    simp [BTreeTree.height, BTreeTree.leafCount]
  | branch idx cnt cs ih =>
    obtain ⟨_, _, hdeg, _, _, _, _, _, _, _, _, hht, hcs⟩ := hv
    simp only [Bool.false_eq_true, ↓reduceIte] at hdeg
    rw [BTreeTree.height_branch_of_eq hht, BTreeTree.leafCount, Nat.pow_add, pow_one]
    have hsum := card_nsmul_le_sum univ _ _ fun i _ => hht i ▸ ih i (hcs i).2
    simp only [card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hsum
    exact (Nat.mul_le_mul_right _ (by omega)).trans hsum

/-- Any valid subtree of height `≥ 1` has `2 * tMin ^ (T.height - 1) ≤ T.leafCount`. -/
theorem ValidSubtree.two_mul_pow_height_sub_one_le_leafCount {isRoot : Bool}
    {fpBits W_val tMin alloc : ℕ} {nodes : ℕ → BTreeNode} {lo hi : ℕ}
    {mapFn : ℕ → Option ℕ} {T : BTreeTree} (ht2 : 2 ≤ tMin) (hH : 1 ≤ T.height)
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T) :
    2 * tMin ^ (T.height - 1) ≤ T.leafCount := by
  cases T with
  | leaf idx cnt =>
    simp [BTreeTree.height] at hH
  | branch idx cnt cs =>
    obtain ⟨_, _, hdeg, _, _, _, _, _, _, _, _, hht, hcs⟩ := hv
    have hcnt1 : 1 ≤ cnt := by
      cases isRoot <;> simp only [Bool.false_eq_true, ↓reduceIte] at hdeg <;> omega
    rw [BTreeTree.height_branch_of_eq hht, Nat.add_sub_cancel_left, BTreeTree.leafCount]
    have hsum := card_nsmul_le_sum univ _ _ fun i _ =>
      hht i ▸ pow_height_le_leafCount_nonroot (by omega) (hcs i).2
    simp only [card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hsum
    exact (Nat.mul_le_mul_right _ (by omega)).trans hsum

end Cslib.DataStructure.Dictionary.SuccinctWhp

end

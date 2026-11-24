/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.WordRAM.ExactLog
public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
public import Mathlib.Data.Nat.Bitwise
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Tactic.Ring

/-!
# Overflow-free bit-packed arrays on the `w`-bit Word RAM

This file defines a bit-packed array primitive storing `N` entries of `k` bits each (`0 ≤ k ≤ w`)
across `packedWords N k w = ⌈N * k / w⌉ + 2` contiguous `w`-bit machine words starting at address
`base`.

To avoid intermediate arithmetic overflow `(idx * k ≥ 2^w)` when `idx < N < 2^w` approaches `2^w`
and `k ≤ w` is `Θ(w)` (so that `idx * k` can reach `2^w`), the word and bit offsets of index `idx`
are computed via the Euclidean decomposition `idx = (idx / w) * w + (idx % w)`:
* `wordOffset k w idx = (idx / w) * k + ((idx % w) * k) / w = (idx * k) / w`,
* `bitOffset k w idx = ((idx % w) * k) % w = (idx * k) % w`.
Because `(idx % w) * k ≤ (w - 1) * w < 2^w` holds for every word width `w ≥ 1`
(`pred_mul_self_lt_two_pow`), every intermediate value fits strictly inside `[0, 2^w)`.

Each `k`-bit entry at `(wOff, bOff)` splits into `lowWidth = min k (w - bOff)` low bits at offset
`bOff` of word `base + wOff` and `highWidth = k - lowWidth` high bits at offset `0` of word
`base + wOff + 1`, updated in place via bitwise XOR. Unlike `QuotientFilter`'s single-word
`extractPacked`/`writePackedMem` (which packs `⌊w / k⌋` entries per word without crossing word
boundaries and wastes up to half of each word when `k > w / 2`), allowing entries to straddle
adjacent words achieves the tight `⌈N * k / w⌉ + 2` word bound needed for succinctness. Unlike
`Cslib.BitString.readPackedField`, which is a pure bit-level specification over a tuple of words
with no Word-RAM machine code or memory layout, this module provides `O(1)`-step Word-RAM read and
write programs over `ℕ → ℕ`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.packedWords`, `wordOffset`, `bitOffset`,
  `lowWidth`, `highWidth`: space and index-offset functions.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.readPacked`, `writePacked`: pure bit-packed
  read and write operations on word memory `ℕ → ℕ`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.readPackedCode`, `writePackedCode`:
  `O(1)`-step structured Word-RAM programs over `Basis.exact` implementing `readPacked` and
  `writePacked`.

## Main results

* `div_add_packedWords_le`, `packedWords_add_le`, `div_add_mul_packedWords_le`: ceiling-division
  subadditivity bounds for `packedWords`.
* `pred_mul_self_lt_two_pow`, `mod_mul_lt_two_pow`: `(w - 1) * w < 2 ^ w` and
  `(idx % w) * k < 2 ^ w` for all `w ≥ 1` and `k ≤ w`.
* `wordOffset_eq_mul_div`, `bitOffset_eq_mul_mod`: equivalence of the overflow-free formula with
  `(idx * k) / w` and `(idx * k) % w`.
* `readPacked_writePacked_self`, `readPacked_writePacked_of_ne`,
  `readPacked_writePacked_bounded`, `writePacked_outside`, `readPacked_zero`: exact array laws
  for `readPacked` and `writePacked`.
* `readPackedCode_execWithin`, `writePackedCode_execWithin`: `O(1)`-step execution certificates for
  `readPackedCode` and `writePackedCode`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-! ## Section 1: Overflow-free index arithmetic and word bounds -/

/-- Number of `w`-bit words `(N * k + w - 1) / w + 2` reserved for `N` packed `k`-bit entries.
The `+ 2` slack ensures that for every `idx < N`, both `wordOffset k w idx` and
`wordOffset k w idx + 1` lie strictly inside `[0, packedWords N k w)`. -/
@[expose]
def packedWords (N k w : ℕ) : ℕ :=
  (N * k + w - 1) / w + 2

/-- Adding an auxiliary bit-packed array `packedWords N_aux k_aux w` to an existing word bound
`((B + w - 1) / w) + C₀` increases the bit numerator to `B + N_aux * k_aux` and the additive word
constant by at most `3`. -/
theorem div_add_packedWords_le (B C₀ N_aux k_aux w : ℕ) :
    ((B + w - 1) / w + C₀) + packedWords N_aux k_aux w ≤
      (B + N_aux * k_aux + w - 1) / w + (C₀ + 3) := by
  unfold packedWords
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have h1 := Nat.div_add_mod (B + w - 1) w
    have h2 := Nat.div_add_mod (N_aux * k_aux + w - 1) w
    have h3 := Nat.div_add_mod (B + N_aux * k_aux + w - 1) w
    have hm3 := Nat.mod_lt (B + N_aux * k_aux + w - 1) hw
    have hlt := (Nat.mul_lt_mul_left hw).mp (by
      rw [Nat.left_distrib, Nat.left_distrib, Nat.mul_two]; omega :
      w * ((B + w - 1) / w + (N_aux * k_aux + w - 1) / w) <
        w * ((B + N_aux * k_aux + w - 1) / w + 2))
    omega

/-- Ceiling-division subadditivity for `packedWords`:
`packedWords N₁ k₁ w + packedWords N₂ k₂ w ≤ (N₁ * k₁ + N₂ * k₂ + w - 1) / w + 5`. -/
theorem packedWords_add_le (N₁ k₁ N₂ k₂ w : ℕ) :
    packedWords N₁ k₁ w + packedWords N₂ k₂ w ≤
      (N₁ * k₁ + N₂ * k₂ + w - 1) / w + 5 :=
  div_add_packedWords_le (N₁ * k₁) 2 N₂ k₂ w

/-- Adding `c` copies of `packedWords N_aux k_aux w` increases the bit numerator to
`B + (c * N_aux) * k_aux` and the additive word constant by at most `3 * c`. -/
theorem div_add_mul_packedWords_le (c B C₀ N_aux k_aux w : ℕ) :
    ((B + w - 1) / w + C₀) + c * packedWords N_aux k_aux w ≤
      (B + (c * N_aux) * k_aux + w - 1) / w + (C₀ + 3 * c) := by
  induction c generalizing B C₀ with
  | zero => simp
  | succ c ih =>
    have h1 := div_add_packedWords_le B C₀ N_aux k_aux w
    have h2 := ih (B + N_aux * k_aux) (C₀ + 3)
    rw [show B + N_aux * k_aux + c * N_aux * k_aux = B + (c + 1) * N_aux * k_aux by ring] at h2
    rw [Nat.add_one_mul]; omega

/-- Overflow-free word offset `(idx / w) * k + ((idx % w) * k) / w`, equal to `(idx * k) / w`. -/
@[expose]
def wordOffset (k w idx : ℕ) : ℕ :=
  (idx / w) * k + ((idx % w) * k) / w

/-- Overflow-free bit offset `((idx % w) * k) % w < w`, equal to `(idx * k) % w`. -/
@[expose]
def bitOffset (k w idx : ℕ) : ℕ :=
  ((idx % w) * k) % w

/-- Number of bits `min k (w - bitOffset k w idx)` of entry `idx` stored in word
`base + wordOffset k w idx`. -/
@[expose]
def lowWidth (k w idx : ℕ) : ℕ :=
  min k (w - bitOffset k w idx)

/-- Number of bits `k - lowWidth k w idx` of entry `idx` stored in word
`base + wordOffset k w idx + 1`. -/
@[expose]
def highWidth (k w idx : ℕ) : ℕ :=
  k - lowWidth k w idx

/-- For every `w ≥ 1`, `(w - 1) * w < 2 ^ w`. -/
theorem pred_mul_self_lt_two_pow : ∀ {w : ℕ}, 1 ≤ w → (w - 1) * w < 2 ^ w
  | 1, _ | 2, _ | 3, _ => by decide
  | w + 4, _ => by
    have ih := pred_mul_self_lt_two_pow (w := w + 3) (by omega)
    have h2 : 2 * (w + 3) ≤ 2 ^ (w + 3) := Nat.mul_le_pow (a := 2) (by decide) (w + 3)
    rw [show (w + 4 - 1) * (w + 4) = (w + 3 - 1) * (w + 3) + 2 * (w + 3) by
      change (w + 3) * (w + 4) = (w + 2) * (w + 3) + 2 * (w + 3); ring, Nat.pow_succ]
    omega

/-- Whenever `1 ≤ w` and `k ≤ w`, the product `(idx % w) * k` is strictly less than `2 ^ w`. -/
theorem mod_mul_lt_two_pow {w k : ℕ} (hw : 1 ≤ w) (hkw : k ≤ w) (idx : ℕ) :
    (idx % w) * k < 2 ^ w :=
  (Nat.mul_le_mul (Nat.le_sub_one_of_lt (Nat.mod_lt idx hw)) hkw).trans_lt
    (pred_mul_self_lt_two_pow hw)

/-- `wordOffset k w idx` equals `(idx * k) / w` for every `w > 0`. -/
theorem wordOffset_eq_mul_div {k w idx : ℕ} (hw : 0 < w) :
    wordOffset k w idx = (idx * k) / w := by
  have hdecomp : idx * k = (idx % w) * k + ((idx / w) * k) * w := by
    calc idx * k = (w * (idx / w) + idx % w) * k := by rw [Nat.div_add_mod]
      _ = (idx % w) * k + ((idx / w) * k) * w := by ring
  rw [wordOffset, hdecomp, Nat.add_mul_div_right _ _ hw, Nat.add_comm]

/-- `bitOffset k w idx` equals `(idx * k) % w`. -/
theorem bitOffset_eq_mul_mod (k w idx : ℕ) :
    bitOffset k w idx = (idx * k) % w :=
  Nat.mod_mul_mod idx k w

/-- `bitOffset k w idx < w` whenever `0 < w`. -/
theorem bitOffset_lt {k w idx : ℕ} (hw : 0 < w) :
    bitOffset k w idx < w :=
  Nat.mod_lt _ hw

/-- Fundamental global bit identity: `wordOffset k w idx * w + bitOffset k w idx = idx * k`. -/
theorem wordOffset_mul_add_bitOffset {k w idx : ℕ} :
    wordOffset k w idx * w + bitOffset k w idx = idx * k := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [bitOffset]
  rw [wordOffset_eq_mul_div hw, bitOffset_eq_mul_mod, Nat.mul_comm _ w, Nat.div_add_mod]

/-- For every `idx < N`, `wordOffset k w idx + 1 < packedWords N k w`. -/
theorem wordOffset_add_one_lt_packedWords {N k w idx : ℕ} (hw : 0 < w) (hidx : idx < N) :
    wordOffset k w idx + 1 < packedWords N k w := by
  rw [wordOffset_eq_mul_div hw, packedWords]
  have := Nat.div_le_div_right (c := w)
    (show idx * k ≤ N * k + w - 1 by have := Nat.mul_le_mul_right k hidx.le; omega)
  omega

/-- For every `idx < N`, `wordOffset k w idx < packedWords N k w`. -/
theorem wordOffset_lt_packedWords {N k w idx : ℕ} (hw : 0 < w) (hidx : idx < N) :
    wordOffset k w idx < packedWords N k w :=
  Nat.lt_of_succ_lt (wordOffset_add_one_lt_packedWords hw hidx)

/-- `lowWidth k w idx + highWidth k w idx = k`. -/
theorem lowWidth_add_highWidth (k w idx : ℕ) :
    lowWidth k w idx + highWidth k w idx = k :=
  Nat.add_sub_of_le (Nat.min_le_left _ _)

/-- `bitOffset k w idx + lowWidth k w idx ≤ w` whenever `0 < w`. -/
theorem bitOffset_add_lowWidth_le {k w idx : ℕ} (hw : 0 < w) :
    bitOffset k w idx + lowWidth k w idx ≤ w := by
  have := bitOffset_lt (k := k) (idx := idx) hw; dsimp only [lowWidth]; omega

/-- Whenever `highWidth k w idx > 0` and `0 < w`, `bitOffset k w idx + lowWidth k w idx = w`. -/
theorem bitOffset_add_lowWidth_eq_of_highWidth_pos {k w idx : ℕ} (hw : 0 < w)
    (hh : 0 < highWidth k w idx) :
    bitOffset k w idx + lowWidth k w idx = w := by
  have := bitOffset_lt (k := k) (idx := idx) hw; dsimp only [highWidth, lowWidth] at *; omega

/-- Whenever `k ≤ w`, `highWidth k w idx < w` for `w > 0`. -/
theorem highWidth_lt {k w idx : ℕ} (hw : 0 < w) (hkw : k ≤ w) :
    highWidth k w idx < w := by
  have := bitOffset_lt (k := k) (idx := idx) hw; dsimp only [highWidth, lowWidth]; omega

/-! ## Section 2: Bitwise shift/mask algebra and disjoint-interval non-interference -/

private theorem and_mask_lt (v j : ℕ) : v &&& (2 ^ j - 1) < 2 ^ j :=
  Nat.and_le_right.trans_lt (Nat.sub_lt (Nat.two_pow_pos j) one_pos)

/-- Shifting `x < 2 ^ len` left by `a` and right by `a`, then masking to `len` bits, recovers
`x`. -/
theorem shiftLeft_shiftRight_and_self {x a len : ℕ} (hx : x < 2 ^ len) :
    ((x <<< a) >>> a) &&& (2 ^ len - 1) = x := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.mul_div_cancel _ (by positivity), Nat.mod_eq_of_lt hx]

/-- Shifting `x < 2 ^ len` left by `a`, right by `b`, and masking to `len'` bits gives `0` whenever
the intervals `[a, a + len)` and `[b, b + len')` are disjoint (`a + len ≤ b ∨ b + len' ≤ a`). -/
theorem shiftLeft_shiftRight_and_eq_zero {x a len b len' : ℕ} (hx : x < 2 ^ len)
    (hdisj : a + len ≤ b ∨ b + len' ≤ a) :
    ((x <<< a) >>> b) &&& (2 ^ len' - 1) = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, Nat.zero_testBit]
  by_cases hi : i < len'
  · by_cases ha : a ≤ b + i
    · have h0 := Nat.testBit_lt_two_pow
        (hx.trans_le (Nat.pow_le_pow_right two_pos (by omega : len ≤ b + i - a)))
      simp [hi, ha, h0]
    · simp [ha]
  · simp [hi]

/-- Extracting `len'` bits at offset `b` after XORing a word with `δ <<< a` (`δ < 2 ^ len`) leaves
the extracted bits unchanged whenever `[a, a + len)` and `[b, b + len')` are disjoint. -/
theorem extract_xor_shiftLeft_of_disjoint (word : ℕ) {δ a len b len' : ℕ} (hδ : δ < 2 ^ len)
    (hdisj : a + len ≤ b ∨ b + len' ≤ a) :
    (((word ^^^ (δ <<< a)) >>> b) &&& (2 ^ len' - 1)) =
      ((word >>> b) &&& (2 ^ len' - 1)) := by
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right,
    shiftLeft_shiftRight_and_eq_zero hδ hdisj, Nat.xor_zero]

/-- Extracting `len` bits at offset `a` after replacing the field `old` with `val < 2 ^ len` via
`word ^^^ ((old ^^^ val) <<< a)` returns `val`. -/
theorem extract_xor_shiftLeft_self (word a len : ℕ) {val : ℕ} (hval : val < 2 ^ len) :
    let old := (word >>> a) &&& (2 ^ len - 1)
    (((word ^^^ ((old ^^^ val) <<< a)) >>> a) &&& (2 ^ len - 1)) = val := by
  intro old
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right,
    shiftLeft_shiftRight_and_self (Nat.xor_lt_two_pow (and_mask_lt _ _) hval)]
  change old ^^^ (old ^^^ val) = val
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Recombining the low `k₀` bits `val &&& (2 ^ k₀ - 1)` and high `k₁` bits
`(val >>> k₀) &&& (2 ^ k₁ - 1)` recovers `val` whenever `val < 2 ^ (k₀ + k₁)`. -/
theorem low_xor_high_shiftLeft {val k₀ k₁ : ℕ} (hval : val < 2 ^ (k₀ + k₁)) :
    (val &&& (2 ^ k₀ - 1)) ^^^ (((val >>> k₀) &&& (2 ^ k₁ - 1)) <<< k₀) = val := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hi : i < k₀
  · simp [hi, not_le.mpr hi]
  · by_cases hi' : i - k₀ < k₁
    · simp [hi, show k₀ ≤ i by omega, hi', Nat.add_sub_of_le (by omega : k₀ ≤ i)]
    · have h0 := Nat.testBit_lt_two_pow
        (hval.trans_le (Nat.pow_le_pow_right two_pos (by omega : k₀ + k₁ ≤ i)))
      simp [hi, show k₀ ≤ i by omega, hi', h0]

/-! ## Section 3: Pure bit-slice and bit-packed array read/write and laws -/

/-- Read a `k`-bit field starting at `(base + wOff, bOff)` across at most 2 words. -/
@[expose] def readBitSlice (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) : ℕ :=
  let k₀ := min k (w - bOff)
  let k₁ := k - k₀
  let low := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let high := (mem (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  low ^^^ (high <<< k₀)

/-- Write `val < 2 ^ k` into the `k`-bit field starting at `(base + wOff, bOff)`. -/
@[expose] def writeBitSlice (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) (val : ℕ) : ℕ → ℕ :=
  let k₀ := min k (w - bOff)
  let k₁ := k - k₀
  let old₀ := (mem (base + wOff) >>> bOff) &&& (2 ^ k₀ - 1)
  let val₀ := val &&& (2 ^ k₀ - 1)
  let mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ ((old₀ ^^^ val₀) <<< bOff))
  let old₁ := (mem₁ (base + wOff + 1) >>> 0) &&& (2 ^ k₁ - 1)
  let val₁ := (val >>> k₀) &&& (2 ^ k₁ - 1)
  Function.update mem₁ (base + wOff + 1)
    (mem₁ (base + wOff + 1) ^^^ ((old₁ ^^^ val₁) <<< 0))

/-- Every value returned by `readBitSlice base wOff bOff k w mem` fits in `k` bits (`< 2 ^ k`). -/
theorem readBitSlice_lt (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) :
    readBitSlice base wOff bOff k w mem < 2 ^ k := by
  dsimp only [readBitSlice]
  conv_rhs => rw [← Nat.add_sub_of_le (Nat.min_le_left k (w - bOff))]
  exact Nat.xor_lt_two_pow
    ((and_mask_lt _ _).trans_le (Nat.pow_le_pow_right two_pos (Nat.le_add_right _ _)))
    ((Nat.shiftLeft_lt (and_mask_lt _ _)).trans_eq (by rw [Nat.add_comm]))

/-- Reading a bit-slice from zeroed words returns `0`. -/
theorem readBitSlice_zero {base wOff bOff k w : ℕ} {mem : ℕ → ℕ}
    (h0 : mem (base + wOff) = 0) (h1 : mem (base + wOff + 1) = 0) :
    readBitSlice base wOff bOff k w mem = 0 := by
  simp [readBitSlice, h0, h1]

/-- Reading a bit slice immediately after writing `val < 2 ^ k` returns `val`. -/
theorem readBitSlice_writeBitSlice_self (base wOff bOff k w : ℕ) (mem : ℕ → ℕ) {val : ℕ}
    (hval : val < 2 ^ k) :
    readBitSlice base wOff bOff k w (writeBitSlice base wOff bOff k w mem val) = val := by
  dsimp only [readBitSlice, writeBitSlice]
  rw [Function.update_of_ne (by omega : base + wOff ≠ base + wOff + 1),
    Function.update_self, Function.update_self,
    extract_xor_shiftLeft_self _ _ _ (and_mask_lt _ _),
    extract_xor_shiftLeft_self _ _ _ (and_mask_lt _ _)]
  exact low_xor_high_shiftLeft (by rwa [Nat.add_sub_of_le (Nat.min_le_left _ _)])

/-- Updating word `addr_w` by XORing at `[a, a + len)` preserves extracting `[b, b + len')` from
`addr_r` whenever every overlap `addr_w = addr_r` has disjoint bit intervals
(`a + len ≤ b ∨ b + len' ≤ a`). -/
theorem extract_update_xor_of_disjoint (mem : ℕ → ℕ) (addr_w addr_r : ℕ)
    {δ a len b len' : ℕ} (hδ : δ < 2 ^ len)
    (hdisj : addr_w = addr_r → a + len ≤ b ∨ b + len' ≤ a) :
    (((Function.update mem addr_w (mem addr_w ^^^ (δ <<< a)) addr_r) >>> b) &&&
        (2 ^ len' - 1)) =
      ((mem addr_r >>> b) &&& (2 ^ len' - 1)) := by
  by_cases heq : addr_r = addr_w
  · subst heq
    rw [Function.update_self]
    exact extract_xor_shiftLeft_of_disjoint (mem addr_r) hδ (hdisj rfl)
  · rw [Function.update_of_ne heq]

/-- Non-interference of `writeBitSlice` and `readBitSlice` for disjoint global bit intervals. -/
theorem readBitSlice_writeBitSlice_of_disjoint {base wOff bOff k wOff' bOff' k' w : ℕ}
    (hb : bOff < w) (hb' : bOff' < w)
    (hdisj : (wOff * w + bOff) + k ≤ wOff' * w + bOff' ∨
      (wOff' * w + bOff') + k' ≤ wOff * w + bOff)
    (mem : ℕ → ℕ) (val : ℕ) :
    readBitSlice base wOff' bOff' k' w (writeBitSlice base wOff bOff k w mem val) =
      readBitSlice base wOff' bOff' k' w mem := by
  dsimp only [readBitSlice, writeBitSlice]
  set k₀ := min k (w - bOff); set k₁ := k - k₀
  set k₀' := min k' (w - bOff'); set k₁' := k' - k₀'
  set mem₁ := Function.update mem (base + wOff)
    (mem (base + wOff) ^^^ (((mem (base + wOff) >>> bOff &&& 2 ^ k₀ - 1) ^^^
      (val &&& 2 ^ k₀ - 1)) <<< bOff))
  set mem₂ := Function.update mem₁ (base + wOff + 1)
    (mem₁ (base + wOff + 1) ^^^ (((mem₁ (base + wOff + 1) >>> 0 &&& 2 ^ k₁ - 1) ^^^
      (val >>> k₀ &&& 2 ^ k₁ - 1)) <<< 0))
  have hsum : k₀ + k₁ = k := Nat.add_sub_of_le (Nat.min_le_left _ _)
  have hsum' : k₀' + k₁' = k' := Nat.add_sub_of_le (Nat.min_le_left _ _)
  have hdisj_sub (rOff rb rlen : ℕ) (hlo : wOff' * w + bOff' ≤ rOff * w + rb)
      (hhi : rOff * w + rb + rlen ≤ wOff' * w + bOff' + k') :
      ((mem₂ (base + rOff) >>> rb) &&& (2 ^ rlen - 1)) =
        ((mem (base + rOff) >>> rb) &&& (2 ^ rlen - 1)) := by
    have hloW : (wOff + 1) * w = wOff * w + w := Nat.succ_mul wOff w
    rw [extract_update_xor_of_disjoint mem₁ (base + wOff + 1) (base + rOff)
      (Nat.xor_lt_two_pow (and_mask_lt _ _) (and_mask_lt _ _)) fun he => by
        rcases Nat.eq_zero_or_pos k₁ with hk1 | hk1
        · left; omega
        · have : rOff * w = (wOff + 1) * w := congrArg (· * w) (by omega)
          omega]
    exact extract_update_xor_of_disjoint mem (base + wOff) (base + rOff)
      (Nat.xor_lt_two_pow (and_mask_lt _ _) (and_mask_lt _ _)) fun he => by
        have : rOff * w = wOff * w := congrArg (· * w) (by omega)
        omega
  have hlo' : (wOff' + 1) * w = wOff' * w + w := Nat.succ_mul wOff' w
  rw [hdisj_sub wOff' bOff' k₀' le_rfl (by omega)]
  rcases Nat.eq_zero_or_pos k₁' with hk1' | hk1'
  · simp [hk1']
  · rw [show base + wOff' + 1 = base + (wOff' + 1) by omega,
      hdisj_sub (wOff' + 1) 0 k₁' (by omega) (by omega)]

/-- Read the `k`-bit entry at index `idx` from bit-packed array at `base` on a `w`-bit machine. -/
@[expose]
def readPacked (base k w : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  readBitSlice base (wordOffset k w idx) (bitOffset k w idx) k w mem

/-- Write `val` (`< 2 ^ k`) into the `k`-bit entry at index `idx` of bit-packed array at `base`. -/
@[expose]
def writePacked (base k w : ℕ) (mem : ℕ → ℕ) (idx val : ℕ) : ℕ → ℕ :=
  writeBitSlice base (wordOffset k w idx) (bitOffset k w idx) k w mem val

/-- Every value returned by `readPacked base k w mem idx` fits in `k` bits (`< 2 ^ k`). -/
theorem readPacked_lt (base k w : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    readPacked base k w mem idx < 2 ^ k :=
  readBitSlice_lt _ _ _ _ _ _

/-- Reading from zeroed words returns `0`. -/
theorem readPacked_zero {base k w : ℕ} {mem : ℕ → ℕ} {idx : ℕ}
    (h0 : mem (base + wordOffset k w idx) = 0)
    (h1 : mem (base + wordOffset k w idx + 1) = 0) :
    readPacked base k w mem idx = 0 :=
  readBitSlice_zero h0 h1

/-- Reading index `idx` immediately after writing `val < 2 ^ k` at `idx` returns `val`. -/
theorem readPacked_writePacked_self (base k w : ℕ) (mem : ℕ → ℕ) (idx : ℕ) {val : ℕ}
    (hval : val < 2 ^ k) :
    readPacked base k w (writePacked base k w mem idx val) idx = val :=
  readBitSlice_writeBitSlice_self _ _ _ _ _ _ hval

/-- Reading index `idx' ≠ idx` after writing at `idx` returns the original value at `idx'`. -/
theorem readPacked_writePacked_of_ne {base k w : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {idx idx' : ℕ} (hne : idx' ≠ idx) (val : ℕ) :
    readPacked base k w (writePacked base k w mem idx val) idx' =
      readPacked base k w mem idx' := by
  refine readBitSlice_writeBitSlice_of_disjoint (bitOffset_lt hw) (bitOffset_lt hw) ?_ mem val
  rw [wordOffset_mul_add_bitOffset, wordOffset_mul_add_bitOffset]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inr (Nat.add_one_mul idx' k ▸ Nat.mul_le_mul_right k hlt)
  · exact Or.inl (Nat.add_one_mul idx k ▸ Nat.mul_le_mul_right k hgt)

/-- A packed write updates the bounded logical array and preserves its zero padding. -/
theorem readPacked_writePacked_bounded {base N k w idx val : ℕ}
    (hw : 0 < w) (hidx : idx < N) (hval : val < 2 ^ k) (mem : ℕ → ℕ) :
    (fun j => if j < N then readPacked base k w (writePacked base k w mem idx val) j else 0) =
      Function.update (fun j => if j < N then readPacked base k w mem j else 0) idx val := by
  refine Function.eq_update_iff.mpr ⟨?_, fun j hj => ?_⟩
  · simpa only [hidx, ↓reduceIte] using readPacked_writePacked_self base k w mem idx hval
  · split_ifs
    · exact readPacked_writePacked_of_ne hw mem hj val
    · rfl

/-- Writing at `idx < N` leaves all memory addresses outside `[base, base + packedWords N k w)`
unchanged. -/
theorem writePacked_outside {base N k w : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {idx : ℕ} (hidx : idx < N) (val : ℕ) {addr : ℕ}
    (haddr : ¬(base ≤ addr ∧ addr < base + packedWords N k w)) :
    writePacked base k w mem idx val addr = mem addr := by
  have := wordOffset_add_one_lt_packedWords (N := N) (k := k) hw hidx
  dsimp only [writePacked, writeBitSlice]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- `readPacked` depends only on memory addresses in `[base, base + packedWords N k w)`. -/
theorem readPacked_congr {base N k w : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ addr, base ≤ addr ∧ addr < base + packedWords N k w → mem₁ addr = mem₂ addr)
    {idx : ℕ} (hidx : idx < N) :
    readPacked base k w mem₁ idx = readPacked base k w mem₂ idx := by
  have := wordOffset_add_one_lt_packedWords (N := N) (k := k) hw hidx
  dsimp only [readPacked, readBitSlice]
  rw [h _ ⟨by omega, by omega⟩, h _ ⟨by omega, by omega⟩]

/-- `readPacked` on `[off_r, off_r + packedWords N_r k_r w)` is invariant under `writePacked` on a
disjoint segment `[off_w, off_w + packedWords N_w k_w w)`. -/
theorem readPacked_writePacked_disjoint {off_r N_r k_r off_w N_w k_w w idx_r idx_w val : ℕ}
    {mem : ℕ → ℕ} (hw : 0 < w) (hr : idx_r < N_r) (hw_idx : idx_w < N_w)
    (hdisj : off_r + packedWords N_r k_r w ≤ off_w ∨ off_w + packedWords N_w k_w w ≤ off_r) :
    readPacked off_r k_r w (writePacked off_w k_w w mem idx_w val) idx_r =
      readPacked off_r k_r w mem idx_r :=
  readPacked_congr hw
    (fun _ ⟨ha1, ha2⟩ => writePacked_outside hw mem hw_idx val (by omega)) hr

/-- Updating a single plain word at `addr < off_r` or `off_r + packedWords N_r k_r w ≤ addr`
leaves `readPacked off_r k_r w` unchanged on `0 .. N_r - 1`. -/
theorem readPacked_update_outside {off_r N_r k_r w addr val idx : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hidx : idx < N_r)
    (ha : addr < off_r ∨ off_r + packedWords N_r k_r w ≤ addr) :
    readPacked off_r k_r w (Function.update mem addr val) idx =
      readPacked off_r k_r w mem idx :=
  readPacked_congr hw
    (fun _ ⟨ha1, ha2⟩ => Function.update_of_ne (by omega) val mem) hidx

/-- Reading `idx < N` from a packed segment whose backing words are all `0` returns `0`. -/
theorem readPacked_eq_zero_of_zero_range {arrBase N k w idx : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hidx : idx < N)
    (hz : ∀ a, arrBase ≤ a → a < arrBase + packedWords N k w → mem a = 0) :
    readPacked arrBase k w mem idx = 0 := by
  have hlt := wordOffset_add_one_lt_packedWords (k := k) hw hidx
  exact readPacked_zero (hz _ (by omega) (by omega)) (hz _ (by omega) (by omega))

/-- Whenever `k ≤ w` and `0 < highWidth k w idx`, `lowWidth k w idx < w`. -/
theorem lowWidth_lt_of_highWidth_pos {k w idx : ℕ} (hkw : k ≤ w)
    (hh : 0 < highWidth k w idx) :
    lowWidth k w idx < w := by
  have hsum := lowWidth_add_highWidth k w idx
  omega

/-- If `x < 2 ^ a` and `a + b ≤ w`, then `x <<< b < 2 ^ w`. -/
theorem shiftLeft_lt_two_pow_of_lt {x a b w : ℕ} (hx : x < 2 ^ a) (hab : a + b ≤ w) :
    x <<< b < 2 ^ w :=
  (Nat.shiftLeft_lt hx).trans_le (Nat.pow_le_pow_right two_pos hab)

/-- `writePacked base k w mem idx val` preserves word-boundedness (`< 2 ^ w`) at every memory
address whenever `0 < w` and `k ≤ w`. -/
theorem writePacked_lt_two_pow {base k w : ℕ} (hw : 0 < w) (hkw : k ≤ w) {mem : ℕ → ℕ}
    (hmem : ∀ addr, mem addr < 2 ^ w) (idx val : ℕ) (addr : ℕ) :
    writePacked base k w mem idx val addr < 2 ^ w := by
  have upd_lt {f : ℕ → ℕ} (hf : ∀ a, f a < 2 ^ w) {u d : ℕ} (hd : d < 2 ^ w) (a : ℕ) :
      Function.update f u (f u ^^^ d) a < 2 ^ w := by
    rcases eq_or_ne a u with rfl | hne
    · rw [Function.update_self]; exact Nat.xor_lt_two_pow (hf _) hd
    · rw [Function.update_of_ne hne]; exact hf a
  have h0 := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
  have h1 := lowWidth_add_highWidth k w idx
  refine upd_lt (upd_lt hmem (shiftLeft_lt_two_pow_of_lt
    (Nat.xor_lt_two_pow (and_mask_lt _ _) (and_mask_lt _ _)) (by omega)))
    (shiftLeft_lt_two_pow_of_lt (Nat.xor_lt_two_pow (and_mask_lt _ _) (and_mask_lt _ _))
      (by omega)) addr

/-! ## Section 4: Structured Word-RAM programs (`readPackedCode` and `writePackedCode`) -/

open Cslib.WordRAM Cslib.WordRAM.ExactLog

/-- First half of `addrSetupCode`: given `reg 0 = base + offset`, `reg 1 = idx`, `reg 8 = w`, and
`reg 9 = k`, computes `addr₀` (`reg 3`), `addr₁` (`reg 4`), and `bOff` (`reg 5`) in `10`
deterministic instructions while preserving `reg 0, 1, 2, 8, 9`. -/
@[expose] def offsetSetupCode : Code .exact 10 :=
  .seq (.op (.exactBin .div 3 1 8))
  (.seq (.op (.exactBin .mul 3 3 9))
  (.seq (.op (.exactBin .mod 5 1 8))
  (.seq (.op (.exactBin .mul 5 5 9))
  (.seq (.op (.exactBin .div 4 5 8))
  (.seq (.op (.exactBin .add 3 3 4))
  (.seq (.op (.exactBin .mod 5 5 8))
  (.seq (.op (.exactBin .add 3 0 3))
  (.seq (.op (.const 4 1))
        (.op (.exactBin .add 4 3 4))))))))))

/-- Second half of `addrSetupCode`: given `reg 5 = bOff`, `reg 8 = w`, and `reg 9 = k`, computes
`k₀` (`reg 6`), `mask₀ = 2 ^ k₀ - 1` (`reg 7`), and `mask₁ = 2 ^ k₁ - 1` (`reg 8`) in at most
`15` deterministic instructions without overflowing `< 2 ^ w` even when `k₀ = w`. -/
@[expose] def maskSetupCode : Code .exact 10 :=
  .seq (.op (.exactBin .sub 6 8 5))
  (.seq (.branch (.lt 9 6) (.op (.copy 6 9)) (.op (.copy 6 6)))
  (.seq (.op (.exactBin .sub 8 9 6))
  (.seq (.op (.const 9 1))
  (.seq (.op (.exactBin .shiftLeft 8 9 8))
  (.seq (.op (.exactBin .sub 8 8 9))
  (.seq (.op (.const 7 0))
        (.branch (.eq 6 7)
          (.op (.copy 7 7))
          (.seq (.op (.exactBin .sub 7 6 9))
          (.seq (.op (.exactBin .shiftLeft 7 9 7))
          (.seq (.op (.exactBin .sub 9 7 9))
                (.op (.exactBin .add 7 7 9))))))))))))

/-- Parameter-free address and bit-mask setup subprogram on `Data 10`:
Given `reg 0 = base + offset`, `reg 1 = idx`, `reg 8 = w`, and `reg 9 = k` (preserving
`reg 0, 1, 2`), computes:
* `reg 3 = base + offset + wordOffset k w idx`,
* `reg 4 = base + offset + wordOffset k w idx + 1`,
* `reg 5 = bitOffset k w idx`,
* `reg 6 = lowWidth k w idx`,
* `reg 7 = 2 ^ lowWidth k w idx - 1`,
* `reg 8 = 2 ^ highWidth k w idx - 1`. -/
@[expose] def addrSetupCode : Code .exact 10 :=
  .seq offsetSetupCode maskSetupCode

/-- Read suffix on `Data 10` after `addrSetupCode`: loads the two words at `reg 3` and `reg 4`,
extracts and combines the low and high bit slices into `reg 2`. -/
@[expose] def readPackedFinishCode : Code .exact 10 :=
  .seq (.op (.load 9 3))
  (.seq (.op (.exactBin .shiftRight 9 9 5))
  (.seq (.op (.exactBin .and 9 9 7))
  (.seq (.op (.load 2 4))
  (.seq (.op (.const 7 0))
  (.seq (.op (.exactBin .shiftRight 2 2 7))
  (.seq (.op (.exactBin .and 2 2 8))
  (.seq (.op (.exactBin .shiftLeft 2 2 6))
        (.op (.exactBin .xor 2 9 2)))))))))

/-- Parameter-free structured Word-RAM program on `Data 10` that reads
`readPacked (base + offset) k w mem idx` into `reg 2`, given `reg 0 = base + offset`, `reg 1 = idx`,
`reg 8 = w`, and `reg 9 = k`, preserving `reg 0`, `reg 1`, and `mem`. -/
@[expose] def readPackedCode : Code .exact 10 :=
  .seq addrSetupCode readPackedFinishCode

/-- Write suffix on `Data 10` after `addrSetupCode`: updates the low bit slice at `reg 3` and the
high bit slice at `reg 4` from `reg 2 = val`, preserving `reg 0, 1, 2`. -/
@[expose] def writePackedFinishCode : Code .exact 10 :=
  .seq (.op (.load 9 3))
  (.seq (.op (.exactBin .shiftRight 9 9 5))
  (.seq (.op (.exactBin .and 9 9 7))
  (.seq (.op (.exactBin .and 7 2 7))
  (.seq (.op (.exactBin .xor 9 9 7))
  (.seq (.op (.exactBin .shiftLeft 9 9 5))
  (.seq (.op (.load 7 3))
  (.seq (.op (.exactBin .xor 9 7 9))
  (.seq (.op (.store 3 9))
  (.seq (.op (.const 5 0))
  (.seq (.op (.load 9 4))
  (.seq (.op (.exactBin .shiftRight 9 9 5))
  (.seq (.op (.exactBin .and 9 9 8))
  (.seq (.op (.exactBin .shiftRight 7 2 6))
  (.seq (.op (.exactBin .and 7 7 8))
  (.seq (.op (.exactBin .xor 9 9 7))
  (.seq (.op (.exactBin .shiftLeft 9 9 5))
  (.seq (.op (.load 7 4))
  (.seq (.op (.exactBin .xor 9 7 9))
        (.op (.store 4 9))))))))))))))))))))

/-- Parameter-free structured Word-RAM program on `Data 10` that writes `val` (`reg 2`) at `idx`
(`reg 1`) of the bit-packed array at `base + offset` (`reg 0 = base + offset`, `reg 8 = w`,
`reg 9 = k`), preserving `reg 0, 1, 2`. -/
@[expose] def writePackedCode : Code .exact 10 :=
  .seq addrSetupCode writePackedFinishCode

/-- `offsetSetupCode` executes deterministically in `10` instructions. -/
theorem offsetSetupCode_execWithin {base offset N k w idx : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_idx : Fits w idx)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₁ : Data 10,
      Exec w offsetSetupCode x x₁ 10 ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base + offset ∧
      x₁.regs 1 = idx ∧
      x₁.regs 2 = x.regs 2 ∧
      x₁.regs 3 = base + offset + wordOffset k w idx ∧
      x₁.regs 4 = base + offset + wordOffset k w idx + 1 ∧
      x₁.regs 5 = bitOffset k w idx ∧
      x₁.regs 8 = w ∧
      x₁.regs 9 = k := by
  have hlt1 := wordOffset_add_one_lt_packedWords (N := N) (k := k) hw hidx
  have hfit_w : Fits w w := Nat.lt_two_pow_self
  have hfit_div_w : Fits w (idx / w) := hfit_idx.of_le (Nat.div_le_self idx w)
  have hfit_div_mul : Fits w ((idx / w) * k) :=
    (hfit_end.of_le (by omega : wordOffset k w idx ≤ base + offset + packedWords N k w)).of_le
      (Nat.le_add_right _ _)
  have hfit_mod_w : Fits w (idx % w) := hfit_w.of_le (Nat.mod_lt idx hw).le
  have hfit_mod_mul : Fits w ((idx % w) * k) := mod_mul_lt_two_pow hw hkw idx
  have hfit_mod_div : Fits w (((idx % w) * k) / w) := hfit_mod_mul.of_le (Nat.div_le_self _ _)
  have hbOff_lt := bitOffset_lt (k := k) (idx := idx) hw
  have hwo : (idx / w) * k + ((idx % w) * k) / w = wordOffset k w idx := rfl
  have hbo : ((idx % w) * k) % w = bitOffset k w idx := rfl
  wram_exec [offsetSetupCode, hbase, hr1, hr8, hr9, hwo, hbo]
  wram_simp [hbase, hr1, hr8, hr9]

/-- `addrSetupCode` executes deterministically in at most `25` instructions. -/
theorem addrSetupCode_execWithin {base offset N k w idx : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_idx : Fits w idx)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₁ : Data 10,
      ExecWithin w addrSetupCode x x₁ 25 ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base + offset ∧
      x₁.regs 1 = idx ∧
      x₁.regs 2 = x.regs 2 ∧
      x₁.regs 3 = base + offset + wordOffset k w idx ∧
      x₁.regs 4 = base + offset + wordOffset k w idx + 1 ∧
      x₁.regs 5 = bitOffset k w idx ∧
      x₁.regs 6 = lowWidth k w idx ∧
      x₁.regs 7 = 2 ^ lowWidth k w idx - 1 ∧
      x₁.regs 8 = 2 ^ highWidth k w idx - 1 := by
  obtain ⟨s14, he_off, hmem14, hs14_0, hs14_1, hs14_2, hs14_3, hs14_4, hs14_5, hs14_8, hs14_9⟩ :=
    offsetSetupCode_execWithin hw hkw hidx hbase hr1 hr8 hr9 hfit_idx hfit_end
  have hbOff_lt : bitOffset k w idx < w := bitOffset_lt hw
  have hk0_le_k : lowWidth k w idx ≤ k := Nat.min_le_left _ _
  have hk1_lt_w : highWidth k w idx < w := highWidth_lt hw hkw
  have hk1 : k - lowWidth k w idx = highWidth k w idx := rfl
  have hfit_le (v : ℕ) (hv : v ≤ w) : Fits w v := Nat.lt_two_pow_self.trans_le' hv
  have hfit_pow (v : ℕ) (hv : v < w) : Fits w (2 ^ v) := Nat.pow_lt_pow_right one_lt_two hv
  have hfit_pow_sub (v : ℕ) (hv : v ≤ w) : Fits w (2 ^ v - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos hv)
  have hsum : ¬lowWidth k w idx = 0 →
      2 ^ (lowWidth k w idx - 1) + (2 ^ (lowWidth k w idx - 1) - 1) = 2 ^ lowWidth k w idx - 1 := by
    intro h
    have : 2 ^ lowWidth k w idx = 2 ^ (lowWidth k w idx - 1) * 2 := by
      rw [← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
    have := @Nat.one_le_two_pow (lowWidth k w idx - 1)
    omega
  refine WP.exists_execWithin ?_
  unfold addrSetupCode maskSetupCode
  refine WP.seq (WP.of_execWithin he_off.within ?_)
  wram_exec -split [hs14_5, hs14_8, hfit_le]
  refine WP.cut (fun y t => t ≤ 3 ∧
    y = (s14.set 6 (w - bitOffset k w idx)).set 6 (lowWidth k w idx)) ?_ ?_
  · wram_exec [hs14_9]
    · rw [lowWidth, Nat.min_eq_left hc.le]
    · rw [lowWidth, Nat.min_eq_right (by omega)]
  · rintro y t ⟨ht, rfl⟩
    wram_exec [hs14_9, hk1, hfit_le, hfit_pow, hfit_pow_sub, hsum, Nat.one_shiftLeft,
      Nat.one_le_two_pow]
    all_goals wram_simp [hs14_0, hs14_1, hs14_2, hs14_3, hs14_4, hs14_5, hmem14, hc, pow_zero]

/-- `readPackedCode` executes deterministically in at most `34` instructions, placing
`readPacked (base + offset) k w x.mem idx` into `reg 2` while preserving `reg 0`, `reg 1`, and
`x.mem`. -/
theorem readPackedCode_execWithin {base offset N k w idx : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.Bounded w)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₂ : Data 10,
      ExecWithin w readPackedCode x x₂ 34 ∧
      x₂.mem = x.mem ∧
      x₂.regs 0 = base + offset ∧
      x₂.regs 1 = idx ∧
      x₂.regs 2 = readPacked (base + offset) k w x.mem idx := by
  obtain ⟨x₁, hex₁, hmem₁, hr0, hr1', _, hr3, hr4, hr5, hr6, hr7, hr8'⟩ :=
    addrSetupCode_execWithin hw hkw hidx hbase hr1 hr8 hr9 (hr1 ▸ hx.1 1) hfit_end
  have hsum := lowWidth_add_highWidth k w idx
  have hlow : Fits w ((x.mem (base + offset + wordOffset k w idx) >>> bitOffset k w idx) &&&
      (2 ^ lowWidth k w idx - 1)) := Fits.mono (and_mask_lt _ _) (by omega)
  have hhigh : Fits w ((x.mem (base + offset + wordOffset k w idx + 1) >>> 0) &&&
      (2 ^ highWidth k w idx - 1)) := Fits.mono (and_mask_lt _ _) (by omega)
  have hshl : Fits w (((x.mem (base + offset + wordOffset k w idx + 1) >>> 0) &&&
      (2 ^ highWidth k w idx - 1)) <<< lowWidth k w idx) :=
    shiftLeft_lt_two_pow_of_lt (and_mask_lt _ _) (by omega)
  have hshr0 : Fits w (x.mem (base + offset + wordOffset k w idx) >>> bitOffset k w idx) :=
    (hx.2 _).of_le (Nat.shiftRight_le _ _)
  have hshr1 : Fits w (x.mem (base + offset + wordOffset k w idx + 1) >>> 0) := hx.2 _
  have hread_fit : Fits w (readPacked (base + offset) k w x.mem idx) :=
    Fits.mono (readPacked_lt (base + offset) k w x.mem idx) hkw
  have hread_eq :
      ((x.mem (base + offset + wordOffset k w idx) >>> bitOffset k w idx) &&&
          (2 ^ lowWidth k w idx - 1)) ^^^
        (((x.mem (base + offset + wordOffset k w idx + 1) >>> 0) &&&
          (2 ^ highWidth k w idx - 1)) <<< lowWidth k w idx) =
        readPacked (base + offset) k w x.mem idx := rfl
  unfold readPackedCode readPackedFinishCode
  refine WP.exists_execWithin (WP.seq (WP.of_execWithin hex₁ ?_))
  wram_exec [hr3, hr4, hr5, hr6, hr7, hr8', hmem₁, hshr0, hlow, hshr1, hhigh, hshl,
    hread_eq, hread_fit]
  wram_simp [hr0, hr1', hmem₁]

/-- `writePackedCode` executes deterministically in at most `45` instructions, updating
`x.mem` to `writePacked (base + offset) k w x.mem idx val` while preserving `reg 0 = base + offset`,
`reg 1 = idx`, and `reg 2 = val`. -/
theorem writePackedCode_execWithin {base offset N k w idx val : ℕ} {x : Data 10}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (hx : x.Bounded w)
    (hbase : x.regs 0 = base + offset) (hr1 : x.regs 1 = idx) (hr2 : x.regs 2 = val)
    (hr8 : x.regs 8 = w) (hr9 : x.regs 9 = k)
    (hfit_end : Fits w (base + offset + packedWords N k w)) :
    ∃ x₂ : Data 10,
      ExecWithin w writePackedCode x x₂ 45 ∧
      x₂.mem = writePacked (base + offset) k w x.mem idx val ∧
      x₂.regs 0 = base + offset ∧
      x₂.regs 1 = idx ∧
      x₂.regs 2 = val := by
  obtain ⟨x₁, hex₁, hmem₁, hr0, hr1', hr2', hr3, hr4, hr5, hr6, hr7, hr8'⟩ :=
    addrSetupCode_execWithin hw hkw hidx hbase hr1 hr8 hr9 (hr1 ▸ hx.1 1) hfit_end
  have hsum := lowWidth_add_highWidth k w idx
  have hbo := bitOffset_add_lowWidth_le (k := k) (idx := idx) hw
  have hne : base + offset + wordOffset k w idx + 1 ≠ base + offset + wordOffset k w idx := by omega
  generalize hold₀ :
    (x.mem (base + offset + wordOffset k w idx) >>> bitOffset k w idx) &&&
      (2 ^ lowWidth k w idx - 1) = old₀
  generalize hval₀ : val &&& (2 ^ lowWidth k w idx - 1) = val₀
  generalize hold₁ :
    (x.mem (base + offset + wordOffset k w idx + 1) >>> 0) &&&
      (2 ^ highWidth k w idx - 1) = old₁
  generalize hval₁ : (val >>> lowWidth k w idx) &&& (2 ^ highWidth k w idx - 1) = val₁
  have hδ0 : old₀ ^^^ val₀ < 2 ^ lowWidth k w idx :=
    Nat.xor_lt_two_pow (hold₀ ▸ and_mask_lt _ _) (hval₀ ▸ and_mask_lt _ _)
  have hδ1 : old₁ ^^^ val₁ < 2 ^ highWidth k w idx :=
    Nat.xor_lt_two_pow (hold₁ ▸ and_mask_lt _ _) (hval₁ ▸ and_mask_lt _ _)
  have hsh0 : Fits w ((old₀ ^^^ val₀) <<< bitOffset k w idx) :=
    shiftLeft_lt_two_pow_of_lt hδ0 (by omega)
  have hsh1 : Fits w ((old₁ ^^^ val₁) <<< 0) := Fits.mono hδ1 (by omega)
  have h0_le : lowWidth k w idx ≤ w := by omega
  have h1_le : highWidth k w idx ≤ w := by omega
  unfold writePackedCode writePackedFinishCode
  refine WP.exists_execWithin (WP.seq (WP.of_execWithin hex₁ ?_))
  wram_exec [hr2'.trans hr2, hr3, hr4, hr5, hr6, hr7, hr8', hmem₁, hold₀, hval₀, hold₁, hval₁,
    (hx.2 _).of_le (Nat.shiftRight_le _ _),
    show Fits w (x.mem (base + offset + wordOffset k w idx + 1) >>> 0) from hx.2 _,
    (hr2 ▸ hx.1 2).of_le (Nat.shiftRight_le _ _),
    Fits.mono (hold₀ ▸ and_mask_lt _ _) h0_le, Fits.mono (hval₀ ▸ and_mask_lt _ _) h0_le,
    Fits.mono (hold₁ ▸ and_mask_lt _ _) h1_le, Fits.mono (hval₁ ▸ and_mask_lt _ _) h1_le,
    Fits.mono hδ0 h0_le, Fits.mono hδ1 h1_le, hsh0, hsh1]
  refine ⟨?_, by wram_simp [hr0, hr1', hr2'.trans hr2]⟩
  subst hold₀ hval₀ hold₁ hval₁
  simp only [Data.write_mem, Data.set_mem, hmem₁, writePacked, writeBitSlice,
    Function.update_of_ne hne]
  rfl

end Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

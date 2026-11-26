/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.QuotientFilter.Operations
public import CslibFrontier.DataStructure.ApproximateMembership.QuotientFilter.Probability
public import CslibFrontier.DataStructure.HashFamily.WordRAM.ReducedKWise
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Tactic.WramOmega

/-!
# Bit-Packed Slot Arrays for the Word-RAM Quotient Filter

This file defines the compact bit-packed memory layout and extraction/update laws for the
two-stage quotient filter:

1. **Generic power-of-2 bit-packed array (`slotPackShift`, `packedWords`, `extractPacked`,
   `writePackedMem`)**:
   For `2 ^ b` slots of `d`-bit entries (`0 < d`, `2 * d ≤ w`), each word packs
   `2 ^ p` entries where `p = slotPackShift b d w = min b (Nat.log 2 (w / (2 * d)))`.
   Because `p ≤ b` and `2 ^ p * d ≤ w / 2 < w`, the array occupies `packedWords b d w = 2 ^ (b - p)
   ≤ 4 * (2 ^ b * d) / w + 1` words, no entry ever crosses a word boundary, and every intermediate
   bit-shift mask fits strictly inside a `w`-bit word.
2. **Quotient-filter memory layout and total state extraction (`extractFilterState`, `space_le`)**:
   Packs `ReducedKWise` (`5`-wise quotient hash seed and bit-packed table), the `1`-word remainder
   seed `γ : RemSeed w₀`, three `1`-bit slot arrays (`isFull`, `isOcc`, `isRunStart`), and one
   `f`-bit remainder array (`remAt`, `f = remBits w₀ k = min w₀ (k + 1)`) into
   `space w w₀ n k ≤ 640 * ((n * k + w - 1) / w + 1)` words.
3. **Slot modular arithmetic and memory layout offsets (`add_and_eq_probeSlot_val`,
   `add_sub_and_eq_backSlot_val`, `remSeedOff`, `fullOff`, `occOff`, `runOff`, `remOff`)**:
   Relates bitwise slot masks to `probeSlot` / `backSlot` and base-relative offsets to physical
   array addresses.
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.WordRAM Cslib.WordRAM.ExactLog
open Cslib.Probability
open Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open scoped BigOperators ENNReal

/-! ## Section 1: Generic power-of-2 bit-packed slot array arithmetic -/

/-- Log₂ of the number of `d`-bit entries packed per `w`-bit word in a `2 ^ b`-slot array:
`min b (Nat.log 2 (w / (2 * d)))`. -/
@[expose] def slotPackShift (b d w : ℕ) : ℕ :=
  min b (Nat.log 2 (w / (2 * d)))

/-- Number of `w`-bit words `2 ^ (b - slotPackShift b d w)` used by a `2 ^ b`-slot packed array of
`d`-bit entries. -/
@[expose] def packedWords (b d w : ℕ) : ℕ :=
  2 ^ (b - slotPackShift b d w)

theorem slotPackShift_le (b d w : ℕ) : slotPackShift b d w ≤ b :=
  min_le_left b _

theorem packedWords_pos (b d w : ℕ) : 0 < packedWords b d w :=
  Nat.two_pow_pos _

theorem packedWords_mul_two_pow_slotPackShift (b d w : ℕ) :
    packedWords b d w * 2 ^ slotPackShift b d w = 2 ^ b := by
  rw [packedWords, ← pow_add, Nat.sub_add_cancel (slotPackShift_le b d w)]

/-- Whenever `0 < d` and `2 * d ≤ w`, the total bits `2 ^ (slotPackShift b d w) * d` used per word
is at most `w / 2` (and hence strictly less than `w`). -/
theorem two_pow_slotPackShift_mul_le {b d w : ℕ} (hd : 0 < d) (hdw : 2 * d ≤ w) :
    2 ^ slotPackShift b d w * d ≤ w / 2 := by
  have hpow_le : 2 ^ slotPackShift b d w ≤ w / (2 * d) :=
    (Nat.pow_le_pow_right two_pos (min_le_right b _)).trans
      (Nat.pow_log_le_self 2 (Nat.div_pos hdw (Nat.mul_pos two_pos hd)).ne')
  have hmul : 2 * (2 ^ slotPackShift b d w * d) ≤ w := by
    calc 2 * (2 ^ slotPackShift b d w * d)
        = 2 ^ slotPackShift b d w * (2 * d) := by ring
      _ ≤ w := (Nat.mul_le_mul_right (2 * d) hpow_le).trans (Nat.div_mul_le_self w (2 * d))
  omega

theorem two_pow_slotPackShift_mul_lt {b d w : ℕ} (hd : 0 < d) (hdw : 2 * d ≤ w) :
    2 ^ slotPackShift b d w * d < w :=
  (two_pow_slotPackShift_mul_le hd hdw).trans_lt (Nat.div_lt_self (by omega) one_lt_two)

/-- Word-count upper bound: whenever `0 < d` and `2 * d ≤ w`, `packedWords b d w` is at most
`4 * (2 ^ b * d) / w + 1`. -/
theorem packedWords_le {b d w : ℕ} (hd : 0 < d) (hdw : 2 * d ≤ w) :
    packedWords b d w ≤ 4 * (2 ^ b * d) / w + 1 := by
  dsimp only [packedWords, slotPackShift]
  by_cases hle : b ≤ Nat.log 2 (w / (2 * d))
  · rw [min_eq_left hle, Nat.sub_self, pow_zero]
    exact Nat.le_add_left 1 _
  · push Not at hle
    rw [min_eq_right hle.le]
    set p := Nat.log 2 (w / (2 * d))
    have hw_lt : w < 2 ^ (p + 1) * (2 * d) :=
      (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_pow_succ_log_self one_lt_two _)
    have hpow_split : 2 ^ b = 2 ^ (b - p) * 2 ^ p := by
      rw [← pow_add, Nat.sub_add_cancel hle.le]
    have hmul_le : 2 ^ (b - p) * w ≤ 4 * (2 ^ b * d) := by
      calc 2 ^ (b - p) * w
          ≤ 2 ^ (b - p) * (2 ^ (p + 1) * (2 * d)) := Nat.mul_le_mul_left _ hw_lt.le
        _ = 4 * ((2 ^ (b - p) * 2 ^ p) * d) := by rw [pow_succ]; ring
        _ = 4 * (2 ^ b * d) := by rw [hpow_split]
    exact ((Nat.le_div_iff_mul_le (by omega)).mpr hmul_le).trans (Nat.le_succ _)

theorem shiftRight_lt_packedWords (b d w : ℕ) (q : Fin (2 ^ b)) :
    q.val >>> slotPackShift b d w < packedWords b d w :=
  Nat.shiftRight_eq_div_pow .. ▸ Nat.div_lt_of_lt_mul
    (q.isLt.trans_eq ((packedWords_mul_two_pow_slotPackShift b d w).symm.trans (Nat.mul_comm _ _)))

theorem and_two_pow_slotPackShift_lt (b d w : ℕ) (q : Fin (2 ^ b)) :
    q.val &&& (2 ^ slotPackShift b d w - 1) < 2 ^ slotPackShift b d w :=
  Nat.and_two_pow_sub_one_eq_mod _ _ ▸ Nat.mod_lt _ (Nat.two_pow_pos _)

theorem shiftRight_mul_add_and_eq (x p : ℕ) :
    (x >>> p) * 2 ^ p + (x &&& (2 ^ p - 1)) = x := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod, mul_comm, Nat.div_add_mod]

/-- Extract the `d`-bit value at slot `q : Fin (2 ^ b)` from a packed array starting at `arrBase`.
-/
@[expose] def extractPacked (arrBase b d w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) : Fin (2 ^ d) :=
  let p := slotPackShift b d w
  ⟨getLimb d (mem (arrBase + (q.val >>> p))) (q.val &&& (2 ^ p - 1)), getLimb_lt d _ _⟩

/-- Update the `d`-bit entry at slot `q : Fin (2 ^ b)` in a packed array starting at `arrBase` to
`val`. -/
@[expose] def writePackedMem (arrBase b d w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (val : ℕ) :
    ℕ → ℕ :=
  let p := slotPackShift b d w
  let wIdx := q.val >>> p
  let subIdx := q.val &&& (2 ^ p - 1)
  let sh := subIdx * d
  let oldWord := mem (arrBase + wIdx)
  let oldLimb := (oldWord >>> sh) &&& (2 ^ d - 1)
  let newWord := oldWord ^^^ ((oldLimb ^^^ val) <<< sh)
  Function.update mem (arrBase + wIdx) newWord

theorem writePackedMem_outside (arrBase b d w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (val : ℕ)
    {a : ℕ} (ha : a < arrBase ∨ arrBase + packedWords b d w ≤ a) :
    writePackedMem arrBase b d w mem q val a = mem a :=
  Function.update_of_ne (ha.elim (fun h => (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)).ne)
    fun h => (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (shiftRight_lt_packedWords b d w q) arrBase)
      h).ne') _ _

@[simp]
theorem extractPacked_writePackedMem_self (arrBase b d w : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ b)) (val : Fin (2 ^ d)) :
    extractPacked arrBase b d w (writePackedMem arrBase b d w mem q val.val) q = val := by
  apply Fin.ext
  dsimp only [extractPacked, writePackedMem]
  set p := slotPackShift b d w
  set subIdx := q.val &&& (2 ^ p - 1)
  set oldWord := mem (arrBase + (q.val >>> p))
  set oldLimb := getLimb d oldWord subIdx
  have hdiff_lt : oldLimb ^^^ val.val < 2 ^ d :=
    Nat.xor_lt_two_pow (getLimb_lt d oldWord subIdx) val.isLt
  have hsh := add_zero subIdx ▸ getLimb_shiftLeft_mul_add d (oldLimb ^^^ val.val) subIdx 0
  have h0 : getLimb d (oldLimb ^^^ val.val) 0 = oldLimb ^^^ val.val := by
    simp only [getLimb, zero_mul, Nat.shiftRight_zero, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hdiff_lt]
  rw [Function.update_self]
  change getLimb d (oldWord ^^^ ((oldLimb ^^^ val.val) <<< (subIdx * d))) subIdx = val.val
  rw [getLimb_xor, hsh, h0, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem extractPacked_writePackedMem_of_ne (arrBase b d w : ℕ) (mem : ℕ → ℕ)
    (q q' : Fin (2 ^ b)) (val : Fin (2 ^ d)) (hne : q' ≠ q) :
    extractPacked arrBase b d w (writePackedMem arrBase b d w mem q val.val) q' =
      extractPacked arrBase b d w mem q' := by
  apply Fin.ext
  dsimp only [extractPacked, writePackedMem]
  set p := slotPackShift b d w
  set wIdx := q.val >>> p
  set subIdx := q.val &&& (2 ^ p - 1)
  set wIdx' := q'.val >>> p
  set subIdx' := q'.val &&& (2 ^ p - 1)
  by_cases hw : wIdx' = wIdx
  · have hsub_ne : subIdx' ≠ subIdx := fun hsub => hne <| Fin.ext <| by
      rw [← shiftRight_mul_add_and_eq q'.val p, ← shiftRight_mul_add_and_eq q.val p]
      exact congrArg₂ (· * 2 ^ p + ·) hw hsub
    have hdiff_lt : getLimb d (mem (arrBase + wIdx)) subIdx ^^^ val.val < 2 ^ d :=
      Nat.xor_lt_two_pow (getLimb_lt d _ _) val.isLt
    rw [congrArg (arrBase + ·) hw, Function.update_self]
    exact getLimb_xor_shiftLeft_of_ne hdiff_lt hsub_ne
  · rw [Function.update_of_ne (by omega)]

@[simp]
theorem extractPacked_writePackedMem (arrBase b d w : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ b)) (val : Fin (2 ^ d)) :
    extractPacked arrBase b d w (writePackedMem arrBase b d w mem q val.val) =
      Function.update (extractPacked arrBase b d w mem) q val := by
  ext q'
  rcases eq_or_ne q' q with rfl | h
  · rw [extractPacked_writePackedMem_self, Function.update_self]
  · rw [extractPacked_writePackedMem_of_ne _ _ _ _ _ _ _ _ h, Function.update_of_ne h]

/-- Extract the boolean flag at slot `q : Fin (2 ^ b)` from a `1`-bit packed array at `arrBase`. -/
@[expose] def extractBit (arrBase b w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) : Bool :=
  (extractPacked arrBase b 1 w mem q).val == 1

/-- Update the boolean flag at slot `q : Fin (2 ^ b)` in a `1`-bit packed array at `arrBase`. -/
@[expose] def writeBitMem (arrBase b w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (bval : Bool) :
    ℕ → ℕ :=
  writePackedMem arrBase b 1 w mem q bval.toNat

theorem toNat_lt_two (bval : Bool) : bval.toNat < 2 ^ 1 := by
  cases bval <;> decide

@[simp]
theorem extractBit_writeBitMem (arrBase b w : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ b)) (bval : Bool) :
    extractBit arrBase b w (writeBitMem arrBase b w mem q bval) =
      Function.update (extractBit arrBase b w mem) q bval := by
  ext q'
  dsimp only [extractBit, writeBitMem]
  rw [extractPacked_writePackedMem arrBase b 1 w mem q ⟨bval.toNat, toNat_lt_two bval⟩]
  rcases eq_or_ne q' q with rfl | hq
  · cases bval <;> simp
  · simp [hq, extractBit]

@[simp]
theorem extractPacked_zero (arrBase b d w : ℕ) (q : Fin (2 ^ b)) :
    extractPacked arrBase b d w (fun _ => 0) q = ⟨0, Nat.two_pow_pos d⟩ :=
  Fin.ext (getLimb_zero d _)

@[simp]
theorem extractBit_zero (arrBase b w : ℕ) (q : Fin (2 ^ b)) :
    extractBit arrBase b w (fun _ => 0) q = false := by
  simp [extractBit]

/-- A packed read only depends on the `packedWords b d w` words of its array. -/
private theorem extractPacked_congr {arrBase b d w : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a, arrBase ≤ a → a < arrBase + packedWords b d w → mem₁ a = mem₂ a) :
    extractPacked arrBase b d w mem₁ = extractPacked arrBase b d w mem₂ :=
  funext fun q => Fin.ext (congrArg (getLimb d · _)
    (h _ (Nat.le_add_right _ _) (Nat.add_lt_add_left (shiftRight_lt_packedWords b d w q) arrBase)))

/-- A `1`-bit read only depends on the `packedWords b 1 w` words of its array. -/
private theorem extractBit_congr {arrBase b w : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a, arrBase ≤ a → a < arrBase + packedWords b 1 w → mem₁ a = mem₂ a) :
    extractBit arrBase b w mem₁ = extractBit arrBase b w mem₂ := by
  ext q
  simp only [extractBit, extractPacked_congr h]

/-- Writing a packed array leaves a read of a disjoint packed array unchanged. -/
private theorem extractPacked_writePackedMem_of_disjoint {arr₁ arr₂ b d₁ d₂ w : ℕ}
    (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (val : ℕ)
    (hdisj : arr₁ + packedWords b d₁ w ≤ arr₂ ∨ arr₂ + packedWords b d₂ w ≤ arr₁) :
    extractPacked arr₁ b d₁ w (writePackedMem arr₂ b d₂ w mem q val) =
      extractPacked arr₁ b d₁ w mem :=
  extractPacked_congr fun _ h₁ h₂ => writePackedMem_outside _ _ _ _ _ _ _ (by omega)

/-- Writing a packed array leaves a `1`-bit read of a disjoint packed array unchanged. -/
private theorem extractBit_writePackedMem_of_disjoint {arr₁ arr₂ b d₂ w : ℕ}
    (mem : ℕ → ℕ) (q : Fin (2 ^ b)) (val : ℕ)
    (hdisj : arr₁ + packedWords b 1 w ≤ arr₂ ∨ arr₂ + packedWords b d₂ w ≤ arr₁) :
    extractBit arr₁ b w (writePackedMem arr₂ b d₂ w mem q val) = extractBit arr₁ b w mem :=
  extractBit_congr fun _ h₁ h₂ => writePackedMem_outside _ _ _ _ _ _ _ (by omega)

/-! ## Section 2: Quotient-filter memory layout, `space_le`, and `extractFilterState` -/

/-- Address `base + ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5` storing the
multiply-shift remainder seed `γ : RemSeed w₀`. -/
@[expose, wram_arith] def remSeedAddr (base w w₀ n : ℕ) : ℕ :=
  base + ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5

/-- Base address of the `isFull` `1`-bit packed array (`packedWords (quotBits w₀ n) 1 w` words). -/
@[expose, wram_arith] def fullBase (base w w₀ n : ℕ) : ℕ :=
  remSeedAddr base w w₀ n + 1

/-- Base address of the `isOcc` `1`-bit packed array (`packedWords (quotBits w₀ n) 1 w` words). -/
@[expose, wram_arith] def occBase (base w w₀ n : ℕ) : ℕ :=
  fullBase base w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Base address of the `isRunStart` `1`-bit packed array (`packedWords (quotBits w₀ n) 1 w` words).
-/
@[expose, wram_arith] def runBase (base w w₀ n : ℕ) : ℕ :=
  occBase base w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Base address of the `remAt` `remBits w₀ k`-bit packed array
(`packedWords (quotBits w₀ n) (remBits w₀ k) w` words). -/
@[expose, wram_arith] def remBase (base w w₀ n : ℕ) : ℕ :=
  runBase base w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Total contiguous memory footprint `space w w₀ n k` of the two-stage quotient filter in words. -/
@[expose, wram_arith] def space (w w₀ n k : ℕ) : ℕ :=
  let b := quotBits w₀ n
  let f := remBits w₀ k
  ReducedKWise.space w w₀ b b 5 + 1 + 3 * packedWords b 1 w + packedWords b f w

theorem remBase_add_packedWords_eq (base w w₀ n k : ℕ) :
    remBase base w w₀ n + packedWords (quotBits w₀ n) (remBits w₀ k) w =
      base + space w w₀ n k := by
  wram_omega

/-- Because `effCap w₀ n = min n (2 ^ w₀) ≤ 2 ^ w₀`, the quotient bit-width `quotBits w₀ n` is
always at most `w₀ + 3`. -/
theorem quotBits_le_add_three (w₀ n : ℕ) : quotBits w₀ n ≤ w₀ + 3 := by
  dsimp only [quotBits, tableLog]
  rw [Nat.clog_le_iff_le_pow one_lt_two]
  have h1 : effCap w₀ n ≤ 2 ^ w₀ := min_le_right n (2 ^ w₀)
  have h2 : 8 * effCap w₀ n ≤ 2 ^ (w₀ + 3) := by
    calc 8 * effCap w₀ n ≤ 8 * 2 ^ w₀ := Nat.mul_le_mul_left 8 h1
      _ = 2 ^ (w₀ + 3) := by rw [pow_add]; ring
  have h3 : 8 ≤ 2 ^ (w₀ + 3) := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ (w₀ + 3) := Nat.pow_le_pow_right two_pos (Nat.le_add_left 3 w₀)
  exact max_le h2 h3

theorem two_pow_quotBits_le_sixteen_mul {w₀ n : ℕ} (hn : 1 ≤ n) :
    2 ^ quotBits w₀ n ≤ 16 * n :=
  (tableSize_le_sixteen_mul (effCap w₀ n)).trans
    (Nat.mul_le_mul_left 16 (max_le (min_le_left n (2 ^ w₀)) hn))

theorem remBits_pos {w₀ k : ℕ} (hw₀ : 0 < w₀) : 0 < remBits w₀ k :=
  lt_min hw₀ k.succ_pos

theorem remBits_le_w₀ (w₀ k : ℕ) : remBits w₀ k ≤ w₀ :=
  min_le_left w₀ (k + 1)

theorem remBits_le_two_mul {w₀ k : ℕ} (hk : 1 ≤ k) : remBits w₀ k ≤ 2 * k :=
  (min_le_right w₀ (k + 1)).trans (by omega)

/-- **Compact space bound**: for all `n ≥ 1`, `k ≥ 1`, `0 < w₀`, `2 * w₀ ≤ w`, and
`quotBits w₀ n ≤ w`, the total Word-RAM footprint `space w w₀ n k` is at most
`640 * ((n * k + w - 1) / w + 1)` words. -/
theorem space_le {w w₀ n k : ℕ} (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w) (hb_w : quotBits w₀ n ≤ w)
    (hn : 1 ≤ n) (hk : 1 ≤ k) :
    space w w₀ n k ≤ 640 * ((n * k + w - 1) / w + 1) := by
  set b := quotBits w₀ n
  set f := remBits w₀ k
  have hw2 : 2 ≤ w := by omega
  have hf_pos : 0 < f := remBits_pos hw₀
  have h2f_le : 2 * f ≤ w := by have := remBits_le_w₀ w₀ k; omega
  have hpow_b : 2 ^ b ≤ 16 * n := two_pow_quotBits_le_sixteen_mul hn
  have hmax_b2 : max 8 (2 ^ (b / 2)) ≤ 16 * n :=
    max_le (by omega) ((Nat.pow_le_pow_right two_pos (Nat.div_le_self b 2)).trans hpow_b)
  have hnk : n ≤ n * k := Nat.le_mul_of_pos_right n hk
  have hsp_kwise : ReducedKWise.space w w₀ b b 5 ≤ 272 + (32 * (n * k)) / w := by
    have h1 := ReducedKWise.space_le (k := 5)
      ((Nat.le_mul_of_pos_left w₀ two_pos).trans hw) (Nat.le_mul_of_pos_left b (by decide)) hb_w hw2
    have h3 : 2 * max 8 (2 ^ (b / 2)) / w ≤ (32 * (n * k)) / w := Nat.div_le_div_right (by omega)
    omega
  have hbit_words : packedWords b 1 w ≤ (64 * (n * k)) / w + 1 :=
    (packedWords_le one_pos hw2).trans (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1)
  have hrem_words : packedWords b f w ≤ (128 * (n * k)) / w + 1 := by
    have h1 := packedWords_le (b := b) (d := f) (w := w) hf_pos h2f_le
    have hf2k : f ≤ 2 * k := remBits_le_two_mul hk
    have h2 : 4 * (2 ^ b * f) ≤ 128 * (n * k) := by
      calc 4 * (2 ^ b * f) ≤ 4 * ((16 * n) * (2 * k)) :=
            Nat.mul_le_mul_left 4 (Nat.mul_le_mul hpow_b hf2k)
        _ = 128 * (n * k) := by ring
    exact h1.trans (Nat.add_le_add_right (Nat.div_le_div_right h2) 1)
  have hdiv_bound (c x : ℕ) : (c * x) / w ≤ c * (x / w) + c := by
    refine Nat.div_le_of_le_mul ?_
    calc c * x = w * (c * (x / w)) + c * (x % w) := by
          conv_lhs => rw [← Nat.div_add_mod x w]
          ring
      _ ≤ w * (c * (x / w)) + c * w :=
          Nat.add_le_add_left (Nat.mul_le_mul_left c (Nat.mod_lt x (by omega)).le) _
      _ = w * (c * (x / w) + c) := by ring
  have h32 := hdiv_bound 32 (n * k)
  have h64 := hdiv_bound 64 (n * k)
  have h128 := hdiv_bound 128 (n * k)
  have hceil : (n * k) / w ≤ (n * k + w - 1) / w := Nat.div_le_div_right (by omega)
  change ReducedKWise.space w w₀ b b 5 + 1 + 3 * packedWords b 1 w + packedWords b f w ≤
    640 * ((n * k + w - 1) / w + 1)
  omega

/-- Extract the remainder seed `γ : RemSeed w₀` from `mem (remSeedAddr base w w₀ n)`. -/
@[expose] def extractRemSeed (base w w₀ n : ℕ) (mem : ℕ → ℕ) : RemSeed w₀ :=
  Cslib.WordRAM.wordOfNat (w₀ - 1) (mem (remSeedAddr base w w₀ n))

/-- Extract the full seed `(θ, γ) : FilterSeed w₀ n` from memory at `base`. -/
@[expose] def extractFilterSeed (base w w₀ n : ℕ) (mem : ℕ → ℕ) : FilterSeed w₀ n :=
  (ReducedKWise.extractSeed base w₀ (quotBits w₀ n) (quotBits w₀ n) 5 mem,
   extractRemSeed base w w₀ n mem)

/-- Extract the pure `FilterState (quotBits w₀ n) (remBits w₀ k)` from the 4 bit-packed slot arrays
in `mem`. -/
@[expose] def extractFilterState (base w w₀ n k : ℕ) (mem : ℕ → ℕ) :
    FilterState (quotBits w₀ n) (remBits w₀ k) where
  isFull := extractBit (fullBase base w w₀ n) (quotBits w₀ n) w mem
  isOcc := extractBit (occBase base w w₀ n) (quotBits w₀ n) w mem
  isRunStart := extractBit (runBase base w w₀ n) (quotBits w₀ n) w mem
  remAt := extractPacked (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem

theorem extractFilterState_congr {base w w₀ n k : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ a, fullBase base w w₀ n ≤ a → a < base + space w w₀ n k → mem₁ a = mem₂ a) :
    extractFilterState base w w₀ n k mem₁ = extractFilterState base w w₀ n k mem₂ := by
  dsimp only [extractFilterState]
  rw [FilterState.mk.injEq]
  exact ⟨extractBit_congr fun a h₁ _ => h a h₁ (by wram_omega),
    extractBit_congr fun a _ _ => h a (by wram_omega) (by wram_omega),
    extractBit_congr fun a _ _ => h a (by wram_omega) (by wram_omega),
    extractPacked_congr fun a _ _ => h a (by wram_omega) (by wram_omega)⟩

/-- Zeroed slot arrays `[fullBase, base + space)` represent `FilterState.empty`. -/
theorem extractFilterState_of_zero {base w w₀ n k : ℕ} {mem : ℕ → ℕ}
    (hz : ∀ a, fullBase base w w₀ n ≤ a → a < base + space w w₀ n k → mem a = 0) :
    extractFilterState base w w₀ n k mem =
      FilterState.empty (quotBits w₀ n) (remBits w₀ k) := by
  rw [extractFilterState_congr hz]
  dsimp only [extractFilterState, FilterState.empty]
  congr <;> funext q <;> simp

/-! Each slot-array write changes its own field; the other three arrays are disjoint from it. -/

@[simp]
theorem extractFilterState_writeFull (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) :
    extractFilterState base w w₀ n k
      (writeBitMem (fullBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      (extractFilterState base w w₀ n k mem).setFull q bval := by
  dsimp only [extractFilterState, FilterState.setFull]
  rw [FilterState.mk.injEq]
  exact ⟨extractBit_writeBitMem _ _ _ _ _ _,
    extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractPacked_writePackedMem_of_disjoint _ _ _ (by wram_omega)⟩

@[simp]
theorem extractFilterState_writeOcc (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) :
    extractFilterState base w w₀ n k
      (writeBitMem (occBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      (extractFilterState base w w₀ n k mem).setOcc q bval := by
  dsimp only [extractFilterState, FilterState.setOcc]
  rw [FilterState.mk.injEq]
  exact ⟨extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractBit_writeBitMem _ _ _ _ _ _,
    extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractPacked_writePackedMem_of_disjoint _ _ _ (by wram_omega)⟩

@[simp]
theorem extractFilterState_writeRunStart (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (bval : Bool) :
    extractFilterState base w w₀ n k
      (writeBitMem (runBase base w w₀ n) (quotBits w₀ n) w mem q bval) =
      (extractFilterState base w w₀ n k mem).setRunStart q bval := by
  dsimp only [extractFilterState, FilterState.setRunStart]
  rw [FilterState.mk.injEq]
  exact ⟨extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractBit_writeBitMem _ _ _ _ _ _,
    extractPacked_writePackedMem_of_disjoint _ _ _ (by wram_omega)⟩

@[simp]
theorem extractFilterState_writeRem (base w w₀ n k : ℕ) (mem : ℕ → ℕ)
    (q : Fin (2 ^ quotBits w₀ n)) (r : Fin (2 ^ remBits w₀ k)) :
    extractFilterState base w w₀ n k
      (writePackedMem (remBase base w w₀ n) (quotBits w₀ n) (remBits w₀ k) w mem q r.val) =
      (extractFilterState base w w₀ n k mem).setRem q r := by
  dsimp only [extractFilterState, FilterState.setRem]
  rw [FilterState.mk.injEq]
  exact ⟨extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractBit_writePackedMem_of_disjoint _ _ _ (by wram_omega),
    extractPacked_writePackedMem _ _ _ _ _ _ _⟩

/-! ## Section 3: Slot modular arithmetic and memory layout offsets -/

/-- Bitwise identity `(o.val + d) &&& (2 ^ b - 1) = (probeSlot b o d).val`. -/
theorem add_and_eq_probeSlot_val {b : ℕ} (o : Fin (2 ^ b)) (d : ℕ) :
    (o.val + d) &&& (2 ^ b - 1) = (probeSlot b o d).val :=
  Nat.and_two_pow_sub_one_eq_mod _ b

/-- Bitwise identity `(q.val + 2 ^ b - a) &&& (2 ^ b - 1) = (backSlot b q a).val` for `a ≤ 2 ^ b`.
-/
theorem add_sub_and_eq_backSlot_val {b : ℕ} (q : Fin (2 ^ b)) {a : ℕ} (ha : a ≤ 2 ^ b) :
    (q.val + 2 ^ b - a) &&& (2 ^ b - 1) = (backSlot b q a).val := by
  rw [Nat.and_two_pow_sub_one_eq_mod]
  change (q.val + 2 ^ b - a) % 2 ^ b = (q.val + 2 ^ b * (a + 1) - a) % 2 ^ b
  have h1 : q.val + 2 ^ b * (a + 1) - a = (q.val + 2 ^ b - a) + a * 2 ^ b := by
    rw [mul_add_one, mul_comm (2 ^ b) a]; omega
  rw [h1, Nat.add_mul_mod_self_right]

theorem extractPacked_one_val_eq_toNat (arrBase b w : ℕ) (mem : ℕ → ℕ) (q : Fin (2 ^ b)) :
    (extractPacked arrBase b 1 w mem q).val = (extractBit arrBase b w mem q).toNat := by
  dsimp only [extractBit]
  rcases extractPacked arrBase b 1 w mem q with ⟨_ | _ | v, hv⟩ <;> first | rfl | omega

/-- Offset of `remSeedAddr` from `base`. -/
@[expose, wram_arith] def remSeedOff (w w₀ n : ℕ) : ℕ :=
  ReducedKWise.space w w₀ (quotBits w₀ n) (quotBits w₀ n) 5

/-- Offset of `fullBase` from `base`. -/
@[expose, wram_arith] def fullOff (w w₀ n : ℕ) : ℕ :=
  remSeedOff w w₀ n + 1

/-- Offset of `occBase` from `base`. -/
@[expose, wram_arith] def occOff (w w₀ n : ℕ) : ℕ :=
  fullOff w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Offset of `runBase` from `base`. -/
@[expose, wram_arith] def runOff (w w₀ n : ℕ) : ℕ :=
  occOff w w₀ n + packedWords (quotBits w₀ n) 1 w

/-- Offset of `remBase` from `base`. -/
@[expose, wram_arith] def remOff (w w₀ n : ℕ) : ℕ :=
  runOff w w₀ n + packedWords (quotBits w₀ n) 1 w

theorem base_add_remSeedOff (base w w₀ n : ℕ) :
    base + remSeedOff w w₀ n = remSeedAddr base w w₀ n := rfl

theorem base_add_fullOff (base w w₀ n : ℕ) :
    base + fullOff w w₀ n = fullBase base w w₀ n := by wram_omega

theorem base_add_occOff (base w w₀ n : ℕ) :
    base + occOff w w₀ n = occBase base w w₀ n := by wram_omega

theorem base_add_runOff (base w w₀ n : ℕ) :
    base + runOff w w₀ n = runBase base w w₀ n := by wram_omega

theorem base_add_remOff (base w w₀ n : ℕ) :
    base + remOff w w₀ n = remBase base w w₀ n := by wram_omega

end Cslib.DataStructure.ApproximateMembership.QuotientFilter

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.Params
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Overflow-Free 2-Slice Pair Streams and Deterministic Small-Regime Operations

This module develops two foundational components for the deamortized worst-case WHP resizable
succinct dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Overflow-free 2-slice `(q_bits, v_bits)` dense pair stream (`pairStreamWords`, `pairQuotAt`,
   `pairValAt`, `writePairQuot`, `writePairVal`, `SplitPairCfg`, `splitPairRead`, `slideUpPair`,
   `slideDownPair`):**
   When `V = 2 ^ w` and `U > 2 ^ (w - 1)`, `keyBits U = w` and `valBits V = w`, so the combined
   item width `keyBits U + valBits V = 2 * w` exceeds a single `w`-bit word. Packing each `(q, v)`
   pair as two adjacent slices of widths `q_bits ≤ w` and `v_bits ≤ w` via `ResizableSuccinct.wOffQ`
   and `ResizableSuccinct.wOffV` keeps every bit-slice read/write within `[0, w]` bits while using
   `pairStreamWords n q_bits v_bits w = packedWords n (q_bits + v_bits) w` words (`1 · OPT`),
   and satisfies **strict word disjointness** across a split index `s_split` whenever
   `q_lo + v_lo ≤ q_hi + v_hi` and `A_lo + 2 ≤ A_hi` (`splitPair_word_lt`).
2. **Deterministic small-regime (`N = 0`, `n_t < 2 * whpThreshold c`) Word-RAM operations
   (`SmallArrayRep`, `smallScanGenProg`, `writePairGenProg`, `smallDeleteSwapGenProg`):**
   Below the `c`-only threshold `whpThreshold c`, `query`, `insert`, and `delete` execute in
   `O(n_t + 1) = O(whpThreshold c) = O_c(1)` deterministic instructions via `RealizesBounded .exact`
   (`¬ReadsWidth`), with **zero** failure probability and exact `1 · OPT` space.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.pairStreamWords`, `pairQuotAt`,
  `pairValAt`, `writePairQuot`, `writePairVal`: 2-slice `(q_bits, v_bits)` pair-stream model.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SplitPairCfg`, `splitPairRead`,
  `slideUpPair`, `slideDownPair`: Phase 1 / Phase 3 split-pair array primitives.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.readPairGenProg`,
  `writePairGenProg`, `swapPairGenProg`: `Memory.Prog` pair accessors certified by
  `RealizesBounded .exact`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SmallArrayRep`,
  `smallScanGenProg`, `smallDeleteSwapGenProg`: small-regime representation invariant and
  `RealizesBounded .exact` operations.

## Main results

* `splitPair_word_lt`, `splitPair_slideUpPair`, `splitPair_slideDownPair`: strict word disjointness
  and lossless Phase 1 / Phase 3 sliding for 2-slice `(q_bits, v_bits)` streams (`V ≤ 2 ^ w`).
* `realizesBounded_readPairGen`, `realizesBounded_writePairGen`, `realizesBounded_swapPairGen`,
  `realizesBounded_smallScanGen`, `realizesBounded_smallDeleteSwapGen`: parameter-free
  `RealizesBounded .exact` (`¬ReadsWidth`) certificates.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.WordRAM.Resizable.Randomized

/-! ## Section 1: Overflow-Free 2-Slice `(q_bits, v_bits)` Dense Pair Stream -/

/-- Word footprint `packedWords n (q_bits + v_bits) w = (n * (q_bits + v_bits) + w - 1) / w + 2` of
`n` densely packed `(q, v)` pairs of widths `(q_bits, v_bits)` on a `w`-bit machine. -/
abbrev pairStreamWords (n q_bits v_bits w : ℕ) : ℕ :=
  packedWords n (q_bits + v_bits) w

theorem wOffQ_eq_div {q_bits v_bits w d : ℕ} (hw : 0 < w) :
    wOffQ q_bits v_bits w d = (d * (q_bits + v_bits)) / w := by
  have hid := wOffQ_mul_add_bOffQ (q_bits := q_bits) (v_bits := v_bits) (w := w) (d := d)
  have hb := bOffQ_lt (q_bits := q_bits) (v_bits := v_bits) (d := d) hw
  rw [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb, add_zero]

theorem wOffV_eq_div {q_bits v_bits w d : ℕ} (hw : 0 < w) :
    wOffV q_bits v_bits w d = (d * (q_bits + v_bits) + q_bits) / w := by
  have hid := wOffV_mul_add_bOffV (q_bits := q_bits) (v_bits := v_bits) (w := w) (d := d)
  have hb := bOffV_lt (q_bits := q_bits) (v_bits := v_bits) (d := d) hw
  rw [← hid, Nat.mul_comm _ w, Nat.mul_add_div hw, Nat.div_eq_of_lt hb, add_zero]

theorem wOffQ_le_wOffV (q_bits v_bits w d : ℕ) :
    wOffQ q_bits v_bits w d ≤ wOffV q_bits v_bits w d := by
  unfold wOffV
  exact Nat.le_add_right _ _

theorem wOffV_add_one_lt_pairStreamWords {n q_bits v_bits w d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffV q_bits v_bits w d + 1 < pairStreamWords n q_bits v_bits w := by
  rw [wOffV_eq_div hw]
  have hle : d * (q_bits + v_bits) + q_bits ≤ n * (q_bits + v_bits) := by
    have hsucc : (d + 1) * (q_bits + v_bits) ≤ n * (q_bits + v_bits) :=
      Nat.mul_le_mul_right _ hd
    rw [Nat.add_one_mul] at hsucc
    omega
  have hdiv : (d * (q_bits + v_bits) + q_bits) / w ≤
      (n * (q_bits + v_bits) + w - 1) / w := Nat.div_le_div_right (by omega)
  unfold pairStreamWords packedWords
  omega

theorem wOffQ_add_one_lt_pairStreamWords {n q_bits v_bits w d : ℕ} (hw : 0 < w) (hd : d < n) :
    wOffQ q_bits v_bits w d + 1 < pairStreamWords n q_bits v_bits w :=
  lt_of_le_of_lt (Nat.add_le_add_right (wOffQ_le_wOffV q_bits v_bits w d) 1)
    (wOffV_add_one_lt_pairStreamWords hw hd)

/-- Pure extraction of the `q_bits`-bit first field at slot `d` from `itemBase`. -/
@[expose] def pairQuotAt (itemBase q_bits v_bits w : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  readBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem

/-- Pure extraction of the `v_bits`-bit second field at slot `d` from `itemBase`. -/
@[expose] def pairValAt (itemBase q_bits v_bits w : ℕ) (mem : ℕ → ℕ) (d : ℕ) : ℕ :=
  readBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem

/-- Pure write of `q` into the `q_bits`-bit first field at slot `d` at `itemBase`. -/
@[expose] def writePairQuot (itemBase q_bits v_bits w : ℕ) (mem : ℕ → ℕ) (d q : ℕ) : ℕ → ℕ :=
  writeBitSlice itemBase (wOffQ q_bits v_bits w d) (bOffQ q_bits v_bits w d) q_bits w mem q

/-- Pure write of `v` into the `v_bits`-bit second field at slot `d` at `itemBase`. -/
@[expose] def writePairVal (itemBase q_bits v_bits w : ℕ) (mem : ℕ → ℕ) (d v : ℕ) : ℕ → ℕ :=
  writeBitSlice itemBase (wOffV q_bits v_bits w d) (bOffV q_bits v_bits w d) v_bits w mem v

/-- Pure write of `(q, v)` at slot `d` at `itemBase`. -/
@[expose] def writePair (itemBase q_bits v_bits w : ℕ) (mem : ℕ → ℕ) (d q v : ℕ) : ℕ → ℕ :=
  writePairVal itemBase q_bits v_bits w (writePairQuot itemBase q_bits v_bits w mem d q) d v

theorem pairQuotAt_lt (itemBase q_bits v_bits w : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    pairQuotAt itemBase q_bits v_bits w mem d < 2 ^ q_bits :=
  readBitSlice_lt _ _ _ _ _ _

theorem pairValAt_lt (itemBase q_bits v_bits w : ℕ) (mem : ℕ → ℕ) (d : ℕ) :
    pairValAt itemBase q_bits v_bits w mem d < 2 ^ v_bits :=
  readBitSlice_lt _ _ _ _ _ _

theorem pairQuotAt_writePairQuot_self {itemBase q_bits v_bits w d q : ℕ} (mem : ℕ → ℕ)
    (hq : q < 2 ^ q_bits) :
    pairQuotAt itemBase q_bits v_bits w (writePairQuot itemBase q_bits v_bits w mem d q) d = q :=
  readBitSlice_writeBitSlice_self _ _ _ _ _ _ hq

theorem pairQuotAt_writePairQuot_of_ne {itemBase q_bits v_bits w d d' q : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    pairQuotAt itemBase q_bits v_bits w (writePairQuot itemBase q_bits v_bits w mem d q) d' =
      pairQuotAt itemBase q_bits v_bits w mem d' := by
  refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffQ_lt hw) ?_ mem q
  rw [wOffQ_mul_add_bOffQ, wOffQ_mul_add_bOffQ]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · right
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hlt
    rw [Nat.add_one_mul] at hle; omega
  · left
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hgt
    rw [Nat.add_one_mul] at hle; omega

theorem pairValAt_writePairQuot {itemBase q_bits v_bits w d d' q : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) :
    pairValAt itemBase q_bits v_bits w (writePairQuot itemBase q_bits v_bits w mem d q) d' =
      pairValAt itemBase q_bits v_bits w mem d' := by
  refine readBitSlice_writeBitSlice_of_disjoint (bOffQ_lt hw) (bOffV_lt hw) ?_ mem q
  rw [wOffQ_mul_add_bOffQ, wOffV_mul_add_bOffV]
  rcases lt_trichotomy d d' with hlt | rfl | hgt
  · left
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hlt
    rw [Nat.add_one_mul] at hle; omega
  · left; omega
  · right
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hgt
    rw [Nat.add_one_mul] at hle; omega

theorem pairValAt_writePairVal_self {itemBase q_bits v_bits w d v : ℕ} (mem : ℕ → ℕ)
    (hv : v < 2 ^ v_bits) :
    pairValAt itemBase q_bits v_bits w (writePairVal itemBase q_bits v_bits w mem d v) d = v :=
  readBitSlice_writeBitSlice_self _ _ _ _ _ _ hv

theorem pairValAt_writePairVal_of_ne {itemBase q_bits v_bits w d d' v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    pairValAt itemBase q_bits v_bits w (writePairVal itemBase q_bits v_bits w mem d v) d' =
      pairValAt itemBase q_bits v_bits w mem d' := by
  refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffV_lt hw) ?_ mem v
  rw [wOffV_mul_add_bOffV, wOffV_mul_add_bOffV]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · right
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hlt
    rw [Nat.add_one_mul] at hle; omega
  · left
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hgt
    rw [Nat.add_one_mul] at hle; omega

theorem pairQuotAt_writePairVal {itemBase q_bits v_bits w d d' v : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) :
    pairQuotAt itemBase q_bits v_bits w (writePairVal itemBase q_bits v_bits w mem d v) d' =
      pairQuotAt itemBase q_bits v_bits w mem d' := by
  refine readBitSlice_writeBitSlice_of_disjoint (bOffV_lt hw) (bOffQ_lt hw) ?_ mem v
  rw [wOffV_mul_add_bOffV, wOffQ_mul_add_bOffQ]
  rcases lt_trichotomy d' d with hlt | rfl | hgt
  · right
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hlt
    rw [Nat.add_one_mul] at hle; omega
  · right; omega
  · left
    have hle := Nat.mul_le_mul_right (q_bits + v_bits) hgt
    rw [Nat.add_one_mul] at hle; omega

@[simp] theorem pairQuotAt_writePair_self {itemBase q_bits v_bits w d q v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hq : q < 2 ^ q_bits) :
    pairQuotAt itemBase q_bits v_bits w (writePair itemBase q_bits v_bits w mem d q v) d = q := by
  unfold writePair
  rw [pairQuotAt_writePairVal hw, pairQuotAt_writePairQuot_self mem hq]

@[simp] theorem pairValAt_writePair_self {itemBase q_bits v_bits w d q v : ℕ}
    (mem : ℕ → ℕ) (hv : v < 2 ^ v_bits) :
    pairValAt itemBase q_bits v_bits w (writePair itemBase q_bits v_bits w mem d q v) d = v :=
  pairValAt_writePairVal_self _ hv

theorem pairQuotAt_writePair_of_ne {itemBase q_bits v_bits w d d' q v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    pairQuotAt itemBase q_bits v_bits w (writePair itemBase q_bits v_bits w mem d q v) d' =
      pairQuotAt itemBase q_bits v_bits w mem d' := by
  unfold writePair
  rw [pairQuotAt_writePairVal hw, pairQuotAt_writePairQuot_of_ne hw mem hne]

theorem pairValAt_writePair_of_ne {itemBase q_bits v_bits w d d' q v : ℕ} (hw : 0 < w)
    (mem : ℕ → ℕ) (hne : d' ≠ d) :
    pairValAt itemBase q_bits v_bits w (writePair itemBase q_bits v_bits w mem d q v) d' =
      pairValAt itemBase q_bits v_bits w mem d' := by
  unfold writePair
  rw [pairValAt_writePairVal_of_ne hw _ hne, pairValAt_writePairQuot hw]

private theorem writePair_apply_of_ne {itemBase q_bits v_bits w d q v addr : ℕ}
    (mem : ℕ → ℕ)
    (hneQ0 : addr ≠ itemBase + wOffQ q_bits v_bits w d)
    (hneQ1 : addr ≠ itemBase + wOffQ q_bits v_bits w d + 1)
    (hneV0 : addr ≠ itemBase + wOffV q_bits v_bits w d)
    (hneV1 : addr ≠ itemBase + wOffV q_bits v_bits w d + 1) :
    writePair itemBase q_bits v_bits w mem d q v addr = mem addr := by
  unfold writePair writePairVal writePairQuot writeBitSlice
  dsimp only
  rw [Function.update_of_ne hneV1, Function.update_of_ne hneV0,
    Function.update_of_ne hneQ1, Function.update_of_ne hneQ0]

theorem writePair_outside {itemBase n q_bits v_bits w d q v addr : ℕ} (hw : 0 < w) (hd : d < n)
    (mem : ℕ → ℕ)
    (haddr : ¬(itemBase ≤ addr ∧ addr < itemBase + pairStreamWords n q_bits v_bits w)) :
    writePair itemBase q_bits v_bits w mem d q v addr = mem addr := by
  have hltQ := wOffQ_add_one_lt_pairStreamWords (q_bits := q_bits) (v_bits := v_bits) hw hd
  have hltV := wOffV_add_one_lt_pairStreamWords (q_bits := q_bits) (v_bits := v_bits) hw hd
  exact writePair_apply_of_ne mem (by omega) (by omega) (by omega) (by omega)

/-- **Strict Split-Pair Word Disjointness (`splitPair_word_lt`).**
Whenever `0 < w`, `q_lo + v_lo ≤ q_hi + v_hi`, and `A_lo + 2 ≤ A_hi`, every word accessed by slot
`idx < s_split` at `(A_lo, q_lo, v_lo)` lies strictly below every word accessed by slot
`idx' ≥ s_split` at `(A_hi, q_hi, v_hi)`, across all `V ≤ 2 ^ w` (including `V = 2 ^ w`). -/
theorem splitPair_word_lt {A_lo q_lo v_lo A_hi q_hi v_hi w s_split idx idx' : ℕ}
    (hw : 0 < w) (hsum : q_lo + v_lo ≤ q_hi + v_hi) (hA : A_lo + 2 ≤ A_hi)
    (hlo : idx < s_split) (hhi : s_split ≤ idx') :
    A_lo + wOffV q_lo v_lo w idx + 1 < A_hi + wOffQ q_hi v_hi w idx' := by
  rw [wOffV_eq_div hw, wOffQ_eq_div hw]
  have hbit : idx * (q_lo + v_lo) + q_lo ≤ idx' * (q_hi + v_hi) := by
    calc idx * (q_lo + v_lo) + q_lo
        ≤ idx * (q_lo + v_lo) + (q_lo + v_lo) := Nat.add_le_add_left (Nat.le_add_right _ _) _
      _ = (idx + 1) * (q_lo + v_lo) := by ring
      _ ≤ idx' * (q_lo + v_lo) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ idx' * (q_hi + v_hi) := Nat.mul_le_mul_left _ hsum
  have hdiv : (idx * (q_lo + v_lo) + q_lo) / w ≤ (idx' * (q_hi + v_hi)) / w :=
    Nat.div_le_div_right hbit
  omega

/-- Named configuration for a 2-slice `(q_bits, v_bits)` split pair stream (`0` projection
chains). -/
structure SplitPairCfg where
  /-- Base word address of the low (`< s_split`) pair slice. -/
  baseLo : ℕ
  /-- Quotient bit-width in the low pair slice. -/
  qBitsLo : ℕ
  /-- Value bit-width in the low pair slice. -/
  vBitsLo : ℕ
  /-- Base word address of the high (`≥ s_split`) pair slice. -/
  baseHi : ℕ
  /-- Quotient bit-width in the high pair slice. -/
  qBitsHi : ℕ
  /-- Value bit-width in the high pair slice. -/
  vBitsHi : ℕ
  /-- Machine word bit-width `w`. -/
  w : ℕ

/-- Read `(q, v)` from a split 2-slice pair stream at `s_split`. -/
@[expose] def splitPairRead (cfg : SplitPairCfg) (s_split : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ × ℕ :=
  if idx < s_split then
    (pairQuotAt cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem idx,
      pairValAt cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem idx)
  else
    (pairQuotAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem idx,
      pairValAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem idx)

/-- Phase 1 single-item upward slide for a 2-slice `(q_bits, v_bits)` pair stream. -/
@[expose] def slideUpPair (cfg : SplitPairCfg) (s_split : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let q := pairQuotAt cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem (s_split - 1)
  let v := pairValAt cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem (s_split - 1)
  writePair cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem (s_split - 1) q v

/-- Phase 3 single-item downward slide for a 2-slice `(q_bits, v_bits)` pair stream. -/
@[expose] def slideDownPair (cfg : SplitPairCfg) (s_split : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let q := pairQuotAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem s_split
  let v := pairValAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem s_split
  writePair cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem s_split q v

private theorem readBitSlice_lo_writePair_hi {cfg : SplitPairCfg} {s_split idx idx' q v : ℕ}
    (hw : 0 < cfg.w) (hsum : cfg.qBitsLo + cfg.vBitsLo ≤ cfg.qBitsHi + cfg.vBitsHi)
    (hA : cfg.baseLo + 2 ≤ cfg.baseHi) (hlo : idx < s_split) (hhi : s_split ≤ idx')
    {wOff bOff k : ℕ} (hwo : wOff ≤ wOffV cfg.qBitsLo cfg.vBitsLo cfg.w idx) (mem : ℕ → ℕ) :
    readBitSlice cfg.baseLo wOff bOff k cfg.w
        (writePair cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem idx' q v) =
      readBitSlice cfg.baseLo wOff bOff k cfg.w mem := by
  have hlt := splitPair_word_lt hw hsum hA hlo hhi
  have hleQ := wOffQ_le_wOffV cfg.qBitsHi cfg.vBitsHi cfg.w idx'
  unfold readBitSlice
  dsimp only
  rw [writePair_apply_of_ne mem (by omega) (by omega) (by omega) (by omega),
    writePair_apply_of_ne mem (by omega) (by omega) (by omega) (by omega)]

private theorem readBitSlice_hi_writePair_lo {cfg : SplitPairCfg} {s_split idx idx' q v : ℕ}
    (hw : 0 < cfg.w) (hsum : cfg.qBitsLo + cfg.vBitsLo ≤ cfg.qBitsHi + cfg.vBitsHi)
    (hA : cfg.baseLo + 2 ≤ cfg.baseHi) (hlo : idx < s_split) (hhi : s_split ≤ idx')
    {wOff bOff k : ℕ} (hwo : wOffQ cfg.qBitsHi cfg.vBitsHi cfg.w idx' ≤ wOff) (mem : ℕ → ℕ) :
    readBitSlice cfg.baseHi wOff bOff k cfg.w
        (writePair cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem idx q v) =
      readBitSlice cfg.baseHi wOff bOff k cfg.w mem := by
  have hlt := splitPair_word_lt hw hsum hA hlo hhi
  have hleQ := wOffQ_le_wOffV cfg.qBitsLo cfg.vBitsLo cfg.w idx
  unfold readBitSlice
  dsimp only
  rw [writePair_apply_of_ne mem (by omega) (by omega) (by omega) (by omega),
    writePair_apply_of_ne mem (by omega) (by omega) (by omega) (by omega)]

/-- **Phase 1 Lossless Upward Pair Slide (`splitPair_slideUpPair`).** -/
theorem splitPair_slideUpPair {cfg : SplitPairCfg} {s_split : ℕ}
    (hw : 0 < cfg.w) (hq_le : cfg.qBitsLo ≤ cfg.qBitsHi) (hv_le : cfg.vBitsLo ≤ cfg.vBitsHi)
    (hA : cfg.baseLo + 2 ≤ cfg.baseHi) (hs : 0 < s_split)
    (mem : ℕ → ℕ) (idx : ℕ) :
    splitPairRead cfg (s_split - 1) (slideUpPair cfg s_split mem) idx =
      splitPairRead cfg s_split mem idx := by
  have hsum : cfg.qBitsLo + cfg.vBitsLo ≤ cfg.qBitsHi + cfg.vBitsHi := Nat.add_le_add hq_le hv_le
  unfold splitPairRead slideUpPair
  dsimp only
  by_cases hlt : idx < s_split - 1
  · have hlt' : idx < s_split := by omega
    rw [ite_eq_left hlt, ite_eq_left hlt']
    exact Prod.ext
      (readBitSlice_lo_writePair_hi hw hsum hA hlt le_rfl (wOffQ_le_wOffV ..) mem)
      (readBitSlice_lo_writePair_hi hw hsum hA hlt le_rfl le_rfl mem)
  · by_cases heq : idx = s_split - 1
    · subst idx
      have hlt' : s_split - 1 < s_split := by omega
      rw [ite_eq_right (lt_irrefl _), ite_eq_left hlt']
      have hq_lt : pairQuotAt cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem (s_split - 1) <
          2 ^ cfg.qBitsHi :=
        (pairQuotAt_lt ..).trans_le (Nat.pow_le_pow_right (by decide) hq_le)
      have hv_lt : pairValAt cfg.baseLo cfg.qBitsLo cfg.vBitsLo cfg.w mem (s_split - 1) <
          2 ^ cfg.vBitsHi :=
        (pairValAt_lt ..).trans_le (Nat.pow_le_pow_right (by decide) hv_le)
      exact Prod.ext (pairQuotAt_writePair_self hw mem hq_lt) (pairValAt_writePair_self mem hv_lt)
    · have hgt : ¬(idx < s_split) := by omega
      rw [ite_eq_right hlt, ite_eq_right hgt]
      exact Prod.ext
        (pairQuotAt_writePair_of_ne hw mem heq)
        (pairValAt_writePair_of_ne hw mem heq)

/-- **Phase 3 Lossless Downward Pair Slide (`splitPair_slideDownPair`).** -/
theorem splitPair_slideDownPair {cfg : SplitPairCfg} {s_split : ℕ}
    (hw : 0 < cfg.w) (hsum : cfg.qBitsLo + cfg.vBitsLo ≤ cfg.qBitsHi + cfg.vBitsHi)
    (hA : cfg.baseLo + 2 ≤ cfg.baseHi)
    (mem : ℕ → ℕ)
    (hq_fit : pairQuotAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem s_split < 2 ^ cfg.qBitsLo)
    (hv_fit : pairValAt cfg.baseHi cfg.qBitsHi cfg.vBitsHi cfg.w mem s_split < 2 ^ cfg.vBitsLo)
    (idx : ℕ) :
    splitPairRead cfg (s_split + 1) (slideDownPair cfg s_split mem) idx =
      splitPairRead cfg s_split mem idx := by
  unfold splitPairRead slideDownPair
  dsimp only
  by_cases hlt : idx < s_split
  · have hlt1 : idx < s_split + 1 := by omega
    rw [ite_eq_left hlt1, ite_eq_left hlt]
    exact Prod.ext
      (pairQuotAt_writePair_of_ne hw mem (Nat.ne_of_lt hlt))
      (pairValAt_writePair_of_ne hw mem (Nat.ne_of_lt hlt))
  · by_cases heq : idx = s_split
    · subst idx
      rw [ite_eq_left (Nat.lt_succ_self s_split), ite_eq_right (lt_irrefl _)]
      exact Prod.ext (pairQuotAt_writePair_self hw mem hq_fit)
        (pairValAt_writePair_self mem hv_fit)
    · have hgt1 : ¬(idx < s_split + 1) := by omega
      rw [ite_eq_right hgt1, ite_eq_right hlt]
      exact Prod.ext
        (readBitSlice_hi_writePair_lo hw hsum hA (Nat.lt_succ_self s_split) (by omega) le_rfl mem)
        (readBitSlice_hi_writePair_lo hw hsum hA (Nat.lt_succ_self s_split) (by omega)
          (wOffQ_le_wOffV ..) mem)

/-! ## Section 2: `Memory.Prog` 2-Slice Pair Accessors via `RealizesBounded .exact` -/

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

private theorem bsum_lt_two_pow {w b q_bits : ℕ} (hw : 0 < w) (hb : b < w) (hq : q_bits ≤ w) :
    b + q_bits < 2 ^ w := by
  have h1 : ∀ m, 0 < m → (m - 1) + m < 2 ^ m := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · decide
      · have ih' : (k - 1) + k < 2 ^ k := ih hk
        have h2 : 2 ≤ 2 ^ k := Nat.le_self_pow hk.ne' 2
        calc (k + 1 - 1) + (k + 1) = ((k - 1) + k) + 2 := by omega
          _ < 2 ^ k + 2 ^ k := by omega
          _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
  have hw1 := h1 w hw
  omega

/-- Read `(pairQuotAt, pairValAt)` at index `d` from `(itemBase, (q_bits, v_bits), wVal)` in
`Memory.Prog` (`4` memory reads, `¬ReadsWidth`). -/
def readPairGenProg : ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((itemBase, (q_bits, v_bits)), wVal), d) => do
    let wbQ ← compQOffsetProg (((q_bits, v_bits), wVal), d)
    let wOffQ_v ← pure wbQ.1
    let bOffQ_v ← pure wbQ.2
    let q ← readBitSliceGenProg ((itemBase, (wOffQ_v, bOffQ_v)), (q_bits, wVal))
    let bsum ← pure (bOffQ_v + q_bits)
    let wOffV_v ← pure (wOffQ_v + bsum / wVal)
    let bOffV_v ← pure (bsum % wVal)
    let v ← readBitSliceGenProg ((itemBase, (wOffV_v, bOffV_v)), (v_bits, wVal))
    pure (q, v)

@[simp] theorem clientResult_readPairGenProg (itemBase q_bits v_bits w d : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s
      (readPairGenProg (((itemBase, (q_bits, v_bits)), w), d)) =
      (pairQuotAt itemBase q_bits v_bits w s.mem d,
        pairValAt itemBase q_bits v_bits w s.mem d) := by
  simp [readPairGenProg, pairQuotAt, pairValAt, wOffV, bOffV]

theorem clientState_readPairGenProg (x : ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readPairGenProg x) = s := by
  rcases x with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, d⟩
  unfold StateTransitionSpec.clientState
  simp [readPairGenProg]

/-- Post-execution memory state `r.2.1` extracted from a `StateTransitionSpec.runClient` triple. -/
abbrev runClientState {α β : Type} (r : α × Memory.State × β) : Memory.State := r.2.1

@[simp] theorem runClient_state_readPairGenProg (x : ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    runClientState ((Memory.spec 0).runClient s (readPairGenProg x)) = s :=
  clientState_readPairGenProg x s

@[simp] theorem memoryCost_readPairGenProg (x : ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readPairGenProg x) s = 4 := by
  rcases x with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, d⟩
  simp [readPairGenProg]

/-- Precondition for `readPairGenProg`. -/
@[expose] def ReadPairPre (w : ℕ) : ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ → Memory.State → Prop
  | (((itemBase, (q_bits, v_bits)), wVal), d), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧
      itemBase + wOffV q_bits v_bits w d + 1 < s.frontier

theorem realizesBounded_readPairGen :
    RealizesBounded .exact readPairGenProg
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ReadPairPre (fun _ _ => 0) := by
  have hqo := realizesBounded_compQOffset
  have hrbs := realizesBounded_readBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, idx⟩
    obtain ⟨hw, hwVal, hq, hv, hfr⟩ := h
    subst hwVal
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, clientResult_compQOffsetProg,
      runClient_state_compQOffsetProg, runClient_state_readBitSliceGenProg] at *
    have hleQV := wOffQ_le_wOffV q_bits v_bits w idx
    have hbQ := bOffQ_lt (q_bits := q_bits) (v_bits := v_bits) (d := idx) hw
    have hbV := bOffV_lt (q_bits := q_bits) (v_bits := v_bits) (d := idx) hw
    have hbsum := bsum_lt_two_pow hw hbQ hq)
  · unfold CompQOffsetPre
    exact ⟨hw, rfl, hq, hv, lt_of_le_of_lt (by omega) hmem.1⟩
  · unfold ReadBitSlicePre
    exact ⟨hw, rfl, hq, hbQ, by omega⟩
  all_goals try exact hbsum
  all_goals try exact hw.ne'
  all_goals try (refine lt_of_le_of_lt ?_ hmem.1; unfold wOffV at hfr; omega)
  · unfold ReadBitSlicePre
    refine ⟨hw, rfl, hv, hbV, ?_⟩
    unfold wOffV at hfr; omega

/-- Write `(q, v)` at index `d` into `(itemBase, (q_bits, v_bits), wVal)` in `Memory.Prog`
(`8` memory ops, `¬ReadsWidth`). -/
def writePairGenProg : (((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((itemBase, (q_bits, v_bits)), wVal), d), (q, v)) => do
    let wbQ ← compQOffsetProg (((q_bits, v_bits), wVal), d)
    let wOffQ_v ← pure wbQ.1
    let bOffQ_v ← pure wbQ.2
    writeBitSliceGenProg (((itemBase, (wOffQ_v, bOffQ_v)), (q_bits, wVal)), q)
    let bsum ← pure (bOffQ_v + q_bits)
    let wOffV_v ← pure (wOffQ_v + bsum / wVal)
    let bOffV_v ← pure (bsum % wVal)
    writeBitSliceGenProg (((itemBase, (wOffV_v, bOffV_v)), (v_bits, wVal)), v)

@[simp] theorem clientResult_writePairGenProg
    (x : (((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writePairGenProg x) = () := by
  rcases x with ⟨⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, d⟩, ⟨q, v⟩⟩
  simp [writePairGenProg]

theorem clientState_writePairGenProg (itemBase q_bits v_bits w d q v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
      (writePairGenProg ((((itemBase, (q_bits, v_bits)), w), d), (q, v))) =
      { mem := writePair itemBase q_bits v_bits w s.mem d q v, frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [writePairGenProg, writePair, writePairQuot, writePairVal, wOffV, bOffV]

@[simp] theorem runClient_state_writePairGenProg
    (itemBase q_bits v_bits w d q v : ℕ) (s : Memory.State) :
    runClientState ((Memory.spec 0).runClient s
      (writePairGenProg ((((itemBase, (q_bits, v_bits)), w), d), (q, v)))) =
      { mem := writePair itemBase q_bits v_bits w s.mem d q v, frontier := s.frontier } :=
  clientState_writePairGenProg itemBase q_bits v_bits w d q v s

@[simp] theorem memoryCost_writePairGenProg
    (x : (((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (writePairGenProg x) s = 8 := by
  rcases x with ⟨⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, d⟩, ⟨q, v⟩⟩
  simp [writePairGenProg]

/-- Precondition for `writePairGenProg`. -/
@[expose] def WritePairPre (w : ℕ) : (((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((((itemBase, (q_bits, v_bits)), wVal), d), _qv), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧
      itemBase + wOffV q_bits v_bits w d + 1 < s.frontier

theorem realizesBounded_writePairGen :
    RealizesBounded .exact writePairGenProg
      (WordEncoding.encode (α := (((ℕ × (ℕ × ℕ)) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      WritePairPre (fun _ _ => 0) := by
  have hqo := realizesBounded_compQOffset
  have hwbs := realizesBounded_writeBitSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, idx⟩, ⟨q, v⟩⟩
    obtain ⟨hw, hwVal, hq, hv, hfr⟩ := h
    subst hwVal
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, clientResult_compQOffsetProg,
      runClient_state_compQOffsetProg, runClient_state_writeBitSliceGenProg] at *
    have hleQV := wOffQ_le_wOffV q_bits v_bits w idx
    have hbQ := bOffQ_lt (q_bits := q_bits) (v_bits := v_bits) (d := idx) hw
    have hbV := bOffV_lt (q_bits := q_bits) (v_bits := v_bits) (d := idx) hw
    have hbsum := bsum_lt_two_pow hw hbQ hq)
  · unfold CompQOffsetPre
    exact ⟨hw, rfl, hq, hv, lt_of_le_of_lt (by omega) hmem.1⟩
  · unfold WriteBitSlicePre
    exact ⟨hw, rfl, hq, hbQ, by omega⟩
  all_goals try exact hbsum
  all_goals try exact hw.ne'
  all_goals try (refine lt_of_le_of_lt ?_ hmem.1; unfold wOffV at hfr; omega)
  · unfold WriteBitSlicePre
    refine ⟨hw, rfl, hv, hbV, ?_⟩
    unfold wOffV at hfr; omega

/-- Swap physical slots `p₁` and `p₂` in a 2-slice `(q_bits, v_bits)` pair stream (`O(1)` memory
operations, realizing `PhysSwap.apply ⟨p₁, p₂⟩`). -/
@[expose] def swapPairGenProg : ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (ctx, (p₁, p₂)) =>
    if p₁ = p₂ then
      pure ()
    else do
      let qv₁ ← readPairGenProg (ctx, p₁)
      let qv₂ ← readPairGenProg (ctx, p₂)
      writePairGenProg ((ctx, p₁), qv₂)
      writePairGenProg ((ctx, p₂), qv₁)

/-- Precondition for `swapPairGenProg`. -/
@[expose] def SwapPairPre (w : ℕ) : ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((itemBase, (q_bits, v_bits)), wVal), (p₁, p₂)), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧
      itemBase + wOffV q_bits v_bits w p₁ + 1 < s.frontier ∧
      itemBase + wOffV q_bits v_bits w p₂ + 1 < s.frontier

theorem realizesBounded_swapPairGen :
    RealizesBounded .exact swapPairGenProg
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      SwapPairPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPairGen
  have hwp := realizesBounded_writePairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨p₁, p₂⟩⟩
    obtain ⟨hw, hwVal, hq, hv, hfr₁, hfr₂⟩ := h
    subst hwVal
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, clientResult_readPairGenProg,
      runClient_state_readPairGenProg, runClient_state_writePairGenProg] at *)
  all_goals try exact ⟨hw, rfl, hq, hv, hfr₁⟩
  all_goals exact ⟨hw, rfl, hq, hv, hfr₂⟩

theorem swapPairGenProg_pair_eq {itemBase q_bits v_bits w p₁ p₂ : ℕ} (hw : 0 < w)
    (s : Memory.State) (d : ℕ) :
    let m' := ((Memory.spec 0).clientState s
      (swapPairGenProg (((itemBase, (q_bits, v_bits)), w), (p₁, p₂)))).mem
    let arr := fun p =>
      (pairQuotAt itemBase q_bits v_bits w s.mem p, pairValAt itemBase q_bits v_bits w s.mem p)
    (pairQuotAt itemBase q_bits v_bits w m' d, pairValAt itemBase q_bits v_bits w m' d) =
      (PhysSwap.mk p₁ p₂).apply arr d := by
  dsimp only
  unfold swapPairGenProg
  dsimp only
  by_cases heq : p₁ = p₂
  · rw [ite_eq_left heq]
    simp [StateTransitionSpec.clientState, PhysSwap.apply, heq]
  · rw [ite_eq_right heq]
    unfold StateTransitionSpec.clientState
    simp only [prog_runClient_state_bind, clientResult_readPairGenProg,
      runClient_state_readPairGenProg, runClient_state_writePairGenProg]
    set q₁ := pairQuotAt itemBase q_bits v_bits w s.mem p₁
    set v₁ := pairValAt itemBase q_bits v_bits w s.mem p₁
    set q₂ := pairQuotAt itemBase q_bits v_bits w s.mem p₂
    set v₂ := pairValAt itemBase q_bits v_bits w s.mem p₂
    have hq₁ : q₁ < 2 ^ q_bits := pairQuotAt_lt ..
    have hv₁ : v₁ < 2 ^ v_bits := pairValAt_lt ..
    have hq₂ : q₂ < 2 ^ q_bits := pairQuotAt_lt ..
    have hv₂ : v₂ < 2 ^ v_bits := pairValAt_lt ..
    by_cases hd₂ : d = p₂
    · subst d
      rw [pairQuotAt_writePair_self hw _ hq₁, pairValAt_writePair_self _ hv₁, PhysSwap.apply_p₂]
    · rw [pairQuotAt_writePair_of_ne hw _ hd₂, pairValAt_writePair_of_ne hw _ hd₂]
      by_cases hd₁ : d = p₁
      · subst d
        rw [pairQuotAt_writePair_self hw _ hq₂, pairValAt_writePair_self _ hv₂, PhysSwap.apply_p₁]
      · rw [pairQuotAt_writePair_of_ne hw _ hd₁, pairValAt_writePair_of_ne hw _ hd₁,
          PhysSwap.apply_of_ne _ _ hd₁ hd₂]

/-! ## Section 3: Deterministic Small-Regime (`N = 0`) Representation & `Memory.Prog` Operations -/

/-- Exact representation invariant coupling `s_abs : Dictionary.State U` to a dense `[0, n)`
2-slice `(keyBits U, valBits V)` pair array at `itemBase` (`0` projection chains). -/
structure SmallArrayRep {U : ℕ} (itemBase V w n : ℕ) (s_abs : Dictionary.State U)
    (mem : ℕ → ℕ) : Prop where
  card_eq : n = (Dictionary.dom s_abs).card
  n_le_U : n ≤ U
  key_lt : ∀ i < n, pairQuotAt itemBase (keyBits U) (valBits V) w mem i < U
  val_lt : ∀ i < n, pairValAt itemBase (keyBits U) (valBits V) w mem i < V
  key_inj : ∀ i j, i < n → j < n →
    pairQuotAt itemBase (keyBits U) (valBits V) w mem i =
      pairQuotAt itemBase (keyBits U) (valBits V) w mem j → i = j
  mem_iff : ∀ (u : Fin U) (v : ℕ),
    s_abs u = some v ↔
      ∃ i < n, pairQuotAt itemBase (keyBits U) (valBits V) w mem i = u.val ∧
        pairValAt itemBase (keyBits U) (valBits V) w mem i = v

theorem smallArrayRep_empty {U : ℕ} (itemBase V w : ℕ) (mem : ℕ → ℕ) :
    SmallArrayRep itemBase V w 0 (Dictionary.empty U) mem where
  card_eq := by rw [Dictionary.dom_empty, Finset.card_empty]
  n_le_U := Nat.zero_le U
  key_lt _ hi := absurd hi (Nat.not_lt_zero _)
  val_lt _ hi := absurd hi (Nat.not_lt_zero _)
  key_inj _ _ hi := absurd hi (Nat.not_lt_zero _)
  mem_iff u v := by
    constructor
    · intro h; simp [Dictionary.empty] at h
    · rintro ⟨_, hi, _⟩; exact absurd hi (Nat.not_lt_zero _)

/-- Public tuple abbreviation for small-regime scan context `(pairCtx, (n, target))`. -/
abbrev SmallScanCtx := ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)

/-- Public tuple abbreviation for small-regime scan accumulator `(cur, (found, (idx, val)))`. -/
abbrev SmallScanAcc := ℕ × (ℕ × (ℕ × ℕ))

/-- Single step of `n`-step `iterate` scan over `[0, n)`: reads `(k_cur, v_cur)` at `cur`; if
`found = 0 ∧ k_cur = target`, records `(1, (cur, v_cur))`, advancing `cur ↦ cur + 1`. -/
def smallScanStepProg : SmallScanCtx × SmallScanAcc → Memory.Prog SmallScanAcc
  | ((pairCtx, (_n, target)), (cur, (found, (idx, val)))) => do
    let kv ← readPairGenProg (pairCtx, cur)
    let k_cur ← pure kv.1
    let v_cur ← pure kv.2
    let nxt ← pure (cur + 1)
    if found = 0 then
      if k_cur = target then
        pure (nxt, (1, (cur, v_cur)))
      else
        pure (nxt, (0, (idx, val)))
    else
      pure (nxt, (found, (idx, val)))

private theorem memoryCost_smallScanStepProg_pos (x : SmallScanCtx × SmallScanAcc)
    (s : Memory.State) : 1 ≤ memoryCost (smallScanStepProg x) s := by
  rcases x with ⟨⟨pairCtx, ⟨n, target⟩⟩, ⟨cur, ⟨found, ⟨idx, val⟩⟩⟩⟩
  unfold smallScanStepProg
  rw [memoryCost_bind', memoryCost_readPairGenProg]
  omega

/-- Precondition for `smallScanStepProg` (`cur < n`). -/
@[expose] def SmallScanStepPre (w : ℕ) : SmallScanCtx × SmallScanAcc → Memory.State → Prop
  | ((((itemBase, (q_bits, v_bits)), wVal), (n, _target)), (cur, (found, (idx, val)))), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧ cur < n ∧ n < 2 ^ w ∧
      found < 2 ^ w ∧ idx < 2 ^ w ∧ val < 2 ^ w ∧
      itemBase + pairStreamWords n q_bits v_bits w ≤ s.frontier

private theorem realizesBounded_smallScanStep :
    RealizesBounded .exact smallScanStepProg
      (WordEncoding.encode (α := SmallScanCtx × SmallScanAcc))
      (WordEncoding.encode (α := SmallScanAcc))
      SmallScanStepPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨n, target⟩⟩,
      ⟨cur, ⟨found, ⟨idx, val⟩⟩⟩⟩
    obtain ⟨hw, hwVal, hq, hv, hcur, hn_fit, hf_lt, hi_lt, hv_lt, hfr⟩ := h
    subst hwVal
    dsimp only at *
    try simp only [clientResult_readPairGenProg] at *
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hval_cur : pairValAt itemBase q_bits v_bits w s.mem cur < 2 ^ w :=
      (pairValAt_lt ..).trans_le (Nat.pow_le_pow_right (by decide) hv)
    have hltV := wOffV_add_one_lt_pairStreamWords (q_bits := q_bits) (v_bits := v_bits) hw hcur)
  · unfold ReadPairPre
    exact ⟨hw, rfl, hq, hv, by omega⟩
  all_goals (unfold Fits; omega)

private def smallScanIterProg : (SmallScanCtx × SmallScanAcc) × ℕ → Memory.Prog SmallScanAcc
  | ((ctx, a₀), k) => iterate smallScanStepProg ctx k a₀

private theorem realizesBounded_smallScanIter :
    RealizesBounded .exact smallScanIterProg
      (WordEncoding.encode (α := (SmallScanCtx × SmallScanAcc) × ℕ))
      (WordEncoding.encode (α := SmallScanAcc))
      (fun w ((ctx, a₀), k) s => iterationSafe smallScanStepProg SmallScanStepPre w ctx k a₀ s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := SmallScanCtx))
    (WordEncoding.encode (α := SmallScanAcc))
    realizesBounded_smallScanStep
    memoryCost_smallScanStepProg_pos

/-- Linear scan over `[0, n)` returning `(found, (idx, val))` in `4 * n` memory reads
(`RealizesBounded .exact`, `¬ReadsWidth`). -/
def smallScanGenProg : SmallScanCtx → Memory.Prog (ℕ × (ℕ × ℕ))
  | (pairCtx, (n, target)) => do
    let z0 ← pure 0
    let acc ← smallScanIterProg (((pairCtx, (n, target)), (z0, (z0, (z0, z0)))), n)
    pure acc.2

/-- Precondition for `smallScanGenProg`. -/
@[expose] def SmallScanPre (w : ℕ) : SmallScanCtx → Memory.State → Prop
  | (((itemBase, (q_bits, v_bits)), wVal), (n, _target)), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧ n < 2 ^ w ∧
      itemBase + pairStreamWords n q_bits v_bits w ≤ s.frontier

private theorem smallScan_iter_inv {itemBase q_bits v_bits w n target : ℕ} {s : Memory.State}
    (hw : 0 < w) (hq : q_bits ≤ w) (hv : v_bits ≤ w) (hn_fit : n < 2 ^ w)
    (hfr : itemBase + pairStreamWords n q_bits v_bits w ≤ s.frontier) :
    ∀ k cur found idx val,
      cur + k ≤ n → found < 2 ^ w → idx < 2 ^ w → val < 2 ^ w →
      let ctx : SmallScanCtx := (((itemBase, (q_bits, v_bits)), w), (n, target))
      let a₀ : SmallScanAcc := (cur, (found, (idx, val)))
      let prog := iterate smallScanStepProg ctx k a₀
      iterationSafe smallScanStepProg SmallScanStepPre w ctx k a₀ s ∧
      (Memory.spec 0).clientState s prog = s ∧
      memoryCost prog s = 4 * k ∧
      (found ≠ 0 → ((Memory.spec 0).clientResult s prog).2 = (found, (idx, val))) ∧
      (found = 0 →
        (∃ i, cur ≤ i ∧ i < cur + k ∧
            pairQuotAt itemBase q_bits v_bits w s.mem i = target ∧
            (∀ j, cur ≤ j → j < i → pairQuotAt itemBase q_bits v_bits w s.mem j ≠ target) ∧
            ((Memory.spec 0).clientResult s prog).2 =
              (1, (i, pairValAt itemBase q_bits v_bits w s.mem i))) ∨
        ((∀ j, cur ≤ j → j < cur + k → pairQuotAt itemBase q_bits v_bits w s.mem j ≠ target) ∧
          ((Memory.spec 0).clientResult s prog).2 = (0, (idx, val)))) := by
  intro k
  induction k with
  | zero =>
    intro cur found idx val _ _ _ _
    refine ⟨trivial, rfl, by simp [iterate], fun _ => rfl, fun hf0 => Or.inr ⟨?_, ?_⟩⟩
    · intro j h1 h2; omega
    · subst hf0; rfl
  | succ k ih =>
    intro cur found idx val hck hf_lt hi_lt hv_lt
    set ctx : SmallScanCtx := (((itemBase, (q_bits, v_bits)), w), (n, target))
    set a₀ : SmallScanAcc := (cur, (found, (idx, val)))
    have hcur_n : cur < n := by omega
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hval_cur : pairValAt itemBase q_bits v_bits w s.mem cur < 2 ^ w :=
      (pairValAt_lt ..).trans_le (Nat.pow_le_pow_right (by decide) hv)
    have hpre : SmallScanStepPre w (ctx, a₀) s :=
      ⟨hw, rfl, hq, hv, hcur_n, hn_fit, hf_lt, hi_lt, hv_lt, hfr⟩
    have hst1 : (Memory.spec 0).clientState s (smallScanStepProg (ctx, a₀)) = s := by
      unfold smallScanStepProg
      rw [StateTransitionSpec.clientState_bind, clientState_readPairGenProg,
        clientResult_readPairGenProg]
      simp only [pure_bind]
      split_ifs <;> rfl
    have hcost1 : memoryCost (smallScanStepProg (ctx, a₀)) s = 4 := by
      unfold smallScanStepProg
      rw [memoryCost_bind', memoryCost_readPairGenProg, clientState_readPairGenProg,
        clientResult_readPairGenProg]
      simp only [pure_bind]
      split_ifs <;> simp [memoryCost_pure]
    by_cases hf : found = 0
    · subst found
      by_cases hm : pairQuotAt itemBase q_bits v_bits w s.mem cur = target
      · have hres1 : (Memory.spec 0).clientResult s (smallScanStepProg (ctx, a₀)) =
            (cur + 1, (1, (cur, pairValAt itemBase q_bits v_bits w s.mem cur))) := by
          unfold smallScanStepProg
          rw [prog_clientResult_bind, clientState_readPairGenProg, clientResult_readPairGenProg]
          simp only [pure_bind, ↓reduceIte, hm]; rfl
        obtain ⟨hsafe_k, hst_k, hcost_k, hkeep_k, _⟩ :=
          ih (cur + 1) 1 cur (pairValAt itemBase q_bits v_bits w s.mem cur)
            (by omega) h1_lt (by omega) hval_cur
        refine ⟨?_, ?_, ?_, fun hne => absurd rfl hne, fun _ => Or.inl ⟨cur, le_rfl, by omega,
          hm, fun _ h1 h2 => by omega, ?_⟩⟩
        · unfold iterationSafe
          rw [clientResult_width, clientState_width, hst1, hres1]
          exact ⟨hpre, hsafe_k⟩
        · unfold iterate
          rw [StateTransitionSpec.clientState_bind, hst1, hres1, hst_k]
        · unfold iterate
          rw [memoryCost_bind', hcost1, hst1, hres1, hcost_k]
          ring
        · unfold iterate
          rw [StateTransitionSpec.clientResult_bind, hst1, hres1]
          exact hkeep_k (by decide)
      · have hres1 : (Memory.spec 0).clientResult s (smallScanStepProg (ctx, a₀)) =
            (cur + 1, (0, (idx, val))) := by
          unfold smallScanStepProg
          rw [prog_clientResult_bind, clientState_readPairGenProg, clientResult_readPairGenProg]
          simp only [pure_bind, ↓reduceIte, hm]; rfl
        obtain ⟨hsafe_k, hst_k, hcost_k, _, hzero_k⟩ :=
          ih (cur + 1) 0 idx val (by omega) (Nat.two_pow_pos w) hi_lt hv_lt
        refine ⟨?_, ?_, ?_, fun hne => absurd rfl hne, fun _ => ?_⟩
        · unfold iterationSafe
          rw [clientResult_width, clientState_width, hst1, hres1]
          exact ⟨hpre, hsafe_k⟩
        · unfold iterate
          rw [StateTransitionSpec.clientState_bind, hst1, hres1, hst_k]
        · unfold iterate
          rw [memoryCost_bind', hcost1, hst1, hres1, hcost_k]
          ring
        · have heq_r : (Memory.spec 0).clientResult s (iterate smallScanStepProg ctx (k + 1) a₀) =
              (Memory.spec 0).clientResult s
                (iterate smallScanStepProg ctx k (cur + 1, (0, (idx, val)))) := by
            conv_lhs => unfold iterate
            rw [StateTransitionSpec.clientResult_bind, hst1, hres1]
          rw [heq_r]
          rcases hzero_k rfl with ⟨i, hci, hik, hmi, hfirst, hi_r⟩ | ⟨hall, h0_r⟩
          · refine Or.inl ⟨i, by omega, by omega, hmi, fun j hcj hji => ?_, hi_r⟩
            rcases eq_or_lt_of_le hcj with rfl | hgt
            · exact hm
            · exact hfirst j (by omega) hji
          · refine Or.inr ⟨fun j hcj hjk => ?_, h0_r⟩
            rcases eq_or_lt_of_le hcj with rfl | hgt
            · exact hm
            · exact hall j (by omega) (by omega)
    · have hres1 : (Memory.spec 0).clientResult s (smallScanStepProg (ctx, a₀)) =
          (cur + 1, (found, (idx, val))) := by
        unfold smallScanStepProg
        rw [prog_clientResult_bind, clientState_readPairGenProg, clientResult_readPairGenProg]
        simp only [pure_bind, hf, ↓reduceIte]; rfl
      obtain ⟨hsafe_k, hst_k, hcost_k, hkeep_k, _⟩ :=
        ih (cur + 1) found idx val (by omega) hf_lt hi_lt hv_lt
      refine ⟨?_, ?_, ?_, fun _ => ?_, fun hf0 => absurd hf0 hf⟩
      · unfold iterationSafe
        rw [clientResult_width, clientState_width, hst1, hres1]
        exact ⟨hpre, hsafe_k⟩
      · unfold iterate
        rw [StateTransitionSpec.clientState_bind, hst1, hres1, hst_k]
      · unfold iterate
        rw [memoryCost_bind', hcost1, hst1, hres1, hcost_k]
        ring
      · unfold iterate
        rw [StateTransitionSpec.clientResult_bind, hst1, hres1]
        exact hkeep_k hf

theorem realizesBounded_smallScanGen :
    RealizesBounded .exact smallScanGenProg
      (WordEncoding.encode (α := SmallScanCtx))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      SmallScanPre (fun _ _ => 0) := by
  have hsi := realizesBounded_smallScanIter
  realize
  rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨n, target⟩⟩
  obtain ⟨hw, hwVal, hq, hv, hn_fit, hfr⟩ := h
  subst hwVal
  dsimp only at *
  have hp0 : 0 < 2 ^ w := Nat.two_pow_pos w
  exact (smallScan_iter_inv hw hq hv hn_fit hfr n 0 0 0 0 (by omega) hp0 hp0 hp0).1

/-- Exact specification of `smallScanGenProg` against `SmallArrayRep`. -/
theorem smallScanGenProg_spec {U : ℕ} {itemBase V w n : ℕ} {s_abs : Dictionary.State U}
    {s : Memory.State} (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w) (hn_fit : n < 2 ^ w)
    (hfr : itemBase + pairStreamWords n (keyBits U) (valBits V) w ≤ s.frontier)
    (hrep : SmallArrayRep itemBase V w n s_abs s.mem) (u : Fin U) :
    let prog := smallScanGenProg
      ((((itemBase, (keyBits U, valBits V)), w), (n, u.val)))
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s = 4 * n ∧
    match s_abs u with
    | none => (Memory.spec 0).clientResult s prog = (0, (0, 0))
    | some v =>
      ∃ i < n,
        pairQuotAt itemBase (keyBits U) (valBits V) w s.mem i = u.val ∧
        pairValAt itemBase (keyBits U) (valBits V) w s.mem i = v ∧
        (Memory.spec 0).clientResult s prog = (1, (i, v)) := by
  have hq : keyBits U ≤ w := Nat.clog_le_of_le_pow hU
  have hv : valBits V ≤ w := Nat.clog_le_of_le_pow hV
  have hp0 : 0 < 2 ^ w := Nat.two_pow_pos w
  obtain ⟨_, hst, hcost, _, hzero⟩ := smallScan_iter_inv (target := u.val) hw hq hv hn_fit hfr
    n 0 0 0 0 (by omega) hp0 hp0 hp0
  dsimp only
  unfold smallScanGenProg smallScanIterProg
  simp only [pure_bind]
  have hc_st : (Memory.spec 0).clientState s
      (do let acc ← iterate smallScanStepProg
            ((((itemBase, (keyBits U, valBits V)), w), (n, u.val))) n (0, (0, (0, 0)))
          pure acc.2) = s := by
    rw [StateTransitionSpec.clientState_bind, hst]; rfl
  have hc_cost : memoryCost
      (do let acc ← iterate smallScanStepProg
            ((((itemBase, (keyBits U, valBits V)), w), (n, u.val))) n (0, (0, (0, 0)))
          pure acc.2) s = 4 * n := by
    rw [memoryCost_bind', hst]
    change memoryCost _ s + 0 = 4 * n
    omega
  have hc_res : (Memory.spec 0).clientResult s
      (do let acc ← iterate smallScanStepProg
            ((((itemBase, (keyBits U, valBits V)), w), (n, u.val))) n (0, (0, (0, 0)))
          pure acc.2) =
      ((Memory.spec 0).clientResult s
        (iterate smallScanStepProg
          ((((itemBase, (keyBits U, valBits V)), w), (n, u.val))) n (0, (0, (0, 0))))).2 := by
    rw [prog_clientResult_bind, hst, prog_clientResult_pure]
  refine ⟨hc_st, hc_cost, ?_⟩
  rw [hc_res]
  cases hsu : s_abs u with
  | none =>
    rcases hzero rfl with ⟨i, _, hin, hki, _, _⟩ | ⟨_, h0⟩
    · exfalso
      have hm := (hrep.mem_iff u (pairValAt itemBase (keyBits U) (valBits V) w s.mem i)).mpr
        ⟨i, by omega, hki, rfl⟩
      rw [hsu] at hm; cases hm
    · exact h0
  | some v =>
    obtain ⟨i₀, hi₀, hki₀, hvi₀⟩ := (hrep.mem_iff u v).mp hsu
    rcases hzero rfl with ⟨i, _, hin, hki, _, h1⟩ | ⟨hall, _⟩
    · have hij : i = i₀ := hrep.key_inj i i₀ (by omega) hi₀ (hki.trans hki₀.symm)
      subst i
      rw [hvi₀] at h1
      exact ⟨i₀, hi₀, hki₀, hvi₀, h1⟩
    · exact absurd hki₀ (hall i₀ (Nat.zero_le i₀) (by omega))

/-- Swap-delete slot `idx < n` by copying slot `n - 1` into `idx` when `idx < n - 1` (`O(1)` memory
operations, `RealizesBounded .exact`, `¬ReadsWidth`). -/
def smallDeleteSwapGenProg : ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (pairCtx, (idx, n)) => do
    let last ← pure (n - 1)
    if idx < last then do
      let kv ← readPairGenProg (pairCtx, last)
      writePairGenProg ((pairCtx, idx), kv)
    else
      pure ()

/-- Precondition for `smallDeleteSwapGenProg`. -/
@[expose] def SmallDeleteSwapPre (w : ℕ) :
    ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((itemBase, (q_bits, v_bits)), wVal), (idx, n)), s =>
    0 < w ∧ w = wVal ∧ q_bits ≤ w ∧ v_bits ≤ w ∧ idx < n ∧
      itemBase + pairStreamWords n q_bits v_bits w ≤ s.frontier

theorem realizesBounded_smallDeleteSwapGen :
    RealizesBounded .exact smallDeleteSwapGenProg
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      SmallDeleteSwapPre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPairGen
  have hwp := realizesBounded_writePairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨itemBase, ⟨q_bits, v_bits⟩⟩, wVal⟩, ⟨idx, n⟩⟩
    obtain ⟨hw, hwVal, hq, hv, hidx, hfr⟩ := h
    subst hwVal
    dsimp only at *
    try simp only [StateTransitionSpec.clientState, clientResult_readPairGenProg,
      runClient_state_readPairGenProg] at *
    have hlt_idx := wOffV_add_one_lt_pairStreamWords (q_bits := q_bits) (v_bits := v_bits) hw hidx
    have hlt_last := wOffV_add_one_lt_pairStreamWords (q_bits := q_bits) (v_bits := v_bits) hw
      (show n - 1 < n by omega))
  all_goals try omega
  all_goals exact ⟨hw, rfl, hq, hv, by omega⟩

/-- In-place value overwrite at existing slot `idx < n` preserves `SmallArrayRep`. -/
theorem smallArrayRep_update {U : ℕ} {itemBase V w n idx : ℕ} {s_abs : Dictionary.State U}
    {mem : ℕ → ℕ} (hw : 0 < w) (hrep : SmallArrayRep itemBase V w n s_abs mem)
    (hidx : idx < n) {u : Fin U} {v : ℕ}
    (hk : pairQuotAt itemBase (keyBits U) (valBits V) w mem idx = u.val) (hv : v < V) :
    SmallArrayRep itemBase V w n (Function.update s_abs u (some v))
      (writePair itemBase (keyBits U) (valBits V) w mem idx u.val v) := by
  have hu_pow : u.val < 2 ^ keyBits U :=
    lt_of_lt_of_le u.isLt (Nat.le_pow_clog (by decide) U)
  have hv_pow : v < 2 ^ valBits V :=
    lt_of_lt_of_le hv (Nat.le_pow_clog (by decide) V)
  set m' := writePair itemBase (keyBits U) (valBits V) w mem idx u.val v
  have hq_eq : ∀ i, pairQuotAt itemBase (keyBits U) (valBits V) w m' i =
      pairQuotAt itemBase (keyBits U) (valBits V) w mem i := fun i => by
    by_cases hi : i = idx
    · subst hi; rw [pairQuotAt_writePair_self hw mem hu_pow, hk]
    · exact pairQuotAt_writePair_of_ne hw mem hi
  have hsome : (s_abs u).isSome := by
    rw [(hrep.mem_iff u (pairValAt itemBase (keyBits U) (valBits V) w mem idx)).mpr
      ⟨idx, hidx, hk, rfl⟩]
    rfl
  refine ⟨?_, hrep.n_le_U, fun i hi => hq_eq i ▸ hrep.key_lt i hi, fun i hi => ?_,
    fun i j hi hj heq => hrep.key_inj i j hi hj ((hq_eq i).symm.trans (heq.trans (hq_eq j))),
    fun u' v' => ?_⟩
  · rw [Dictionary.card_dom_insert_eq_of_isSome hsome, hrep.card_eq]
  · by_cases hieq : i = idx
    · subst hieq; rw [pairValAt_writePair_self mem hv_pow]; exact hv
    · rw [pairValAt_writePair_of_ne hw mem hieq]; exact hrep.val_lt i hi
  · by_cases hu' : u' = u
    · subst hu'
      rw [Function.update_self]
      constructor
      · intro h; injection h with hveq; subst hveq
        exact ⟨idx, hidx, by rw [hq_eq, hk], pairValAt_writePair_self mem hv_pow⟩
      · rintro ⟨i, hi, hki, hvi⟩
        rw [hq_eq] at hki
        have hij : i = idx := hrep.key_inj i idx hi hidx (hki.trans hk.symm)
        subst hij
        rw [pairValAt_writePair_self mem hv_pow] at hvi
        exact congrArg some hvi
    · rw [Function.update_of_ne hu', hrep.mem_iff]
      constructor
      · rintro ⟨i, hi, hki, hvi⟩
        have hne_i : i ≠ idx := fun heq => hu' (Fin.ext (by rw [← hki, heq, hk]))
        exact ⟨i, hi, by rw [hq_eq, hki], by rw [pairValAt_writePair_of_ne hw mem hne_i, hvi]⟩
      · rintro ⟨i, hi, hki, hvi⟩
        rw [hq_eq] at hki
        have hne_i : i ≠ idx := fun heq => hu' (Fin.ext (by rw [← hki, heq, hk]))
        rw [pairValAt_writePair_of_ne hw mem hne_i] at hvi
        exact ⟨i, hi, hki, hvi⟩

/-- Appending a new key `u` (`s_abs u = none`) at slot `n` preserves `SmallArrayRep` at `n + 1` and
certifies `n + 1 ≤ U`. -/
theorem smallArrayRep_append {U : ℕ} {itemBase V w n : ℕ} {s_abs : Dictionary.State U}
    {mem : ℕ → ℕ} (hw : 0 < w) (hrep : SmallArrayRep itemBase V w n s_abs mem)
    {u : Fin U} {v : ℕ} (hnone : s_abs u = none) (hv : v < V) :
    n + 1 ≤ U ∧
    SmallArrayRep itemBase V w (n + 1) (Function.update s_abs u (some v))
      (writePair itemBase (keyBits U) (valBits V) w mem n u.val v) := by
  have hu_pow : u.val < 2 ^ keyBits U :=
    lt_of_lt_of_le u.isLt (Nat.le_pow_clog (by decide) U)
  have hv_pow : v < 2 ^ valBits V :=
    lt_of_lt_of_le hv (Nat.le_pow_clog (by decide) V)
  have hcard' : (Dictionary.dom (Function.update s_abs u (some v))).card = n + 1 := by
    rw [Dictionary.card_dom_insert_eq_of_eq_none hnone, hrep.card_eq]
  have hn1_le : n + 1 ≤ U := hcard' ▸ Dynamic.card_dom_le_univ (Function.update s_abs u (some v))
  have hnot_u : ∀ i < n, pairQuotAt itemBase (keyBits U) (valBits V) w mem i ≠ u.val := by
    intro i hi heq
    have hm := (hrep.mem_iff u (pairValAt itemBase (keyBits U) (valBits V) w mem i)).mpr
      ⟨i, hi, heq, rfl⟩
    rw [hnone] at hm; cases hm
  refine ⟨hn1_le, hcard'.symm, hn1_le, fun i hi => ?_, fun i hi => ?_, fun i j hi hj heq => ?_,
    fun u' v' => ?_⟩
  · by_cases hin : i = n
    · subst hin; rw [pairQuotAt_writePair_self hw mem hu_pow]; exact u.isLt
    · rw [pairQuotAt_writePair_of_ne hw mem hin]; exact hrep.key_lt i (by omega)
  · by_cases hin : i = n
    · subst hin; rw [pairValAt_writePair_self mem hv_pow]; exact hv
    · rw [pairValAt_writePair_of_ne hw mem hin]; exact hrep.val_lt i (by omega)
  · by_cases hin : i = n <;> by_cases hjn : j = n
    · omega
    · subst hin
      rw [pairQuotAt_writePair_self hw mem hu_pow, pairQuotAt_writePair_of_ne hw mem hjn] at heq
      exact absurd heq.symm (hnot_u j (by omega))
    · subst hjn
      rw [pairQuotAt_writePair_of_ne hw mem hin, pairQuotAt_writePair_self hw mem hu_pow] at heq
      exact absurd heq (hnot_u i (by omega))
    · rw [pairQuotAt_writePair_of_ne hw mem hin, pairQuotAt_writePair_of_ne hw mem hjn] at heq
      exact hrep.key_inj i j (by omega) (by omega) heq
  · by_cases hu' : u' = u
    · subst hu'
      rw [Function.update_self]
      constructor
      · intro h; injection h with hveq; subst hveq
        exact ⟨n, Nat.lt_succ_self n, pairQuotAt_writePair_self hw mem hu_pow,
          pairValAt_writePair_self mem hv_pow⟩
      · rintro ⟨i, hi, hki, hvi⟩
        by_cases hin : i = n
        · subst hin
          rw [pairValAt_writePair_self mem hv_pow] at hvi
          exact congrArg some hvi
        · rw [pairQuotAt_writePair_of_ne hw mem hin] at hki
          exact absurd hki (hnot_u i (by omega))
    · rw [Function.update_of_ne hu', hrep.mem_iff]
      constructor
      · rintro ⟨i, hi, hki, hvi⟩
        have hin : i ≠ n := Nat.ne_of_lt hi
        exact ⟨i, by omega, by rw [pairQuotAt_writePair_of_ne hw mem hin, hki],
          by rw [pairValAt_writePair_of_ne hw mem hin, hvi]⟩
      · rintro ⟨i, hi, hki, hvi⟩
        by_cases hin : i = n
        · subst hin
          rw [pairQuotAt_writePair_self hw mem hu_pow] at hki
          exact absurd (Fin.ext hki.symm) hu'
        · rw [pairQuotAt_writePair_of_ne hw mem hin] at hki
          rw [pairValAt_writePair_of_ne hw mem hin] at hvi
          exact ⟨i, by omega, hki, hvi⟩

/-- Swap-deleting existing key `u` at slot `idx < n` via `smallDeleteSwapGenProg` preserves
`SmallArrayRep` at `n - 1`. -/
theorem smallArrayRep_deleteSwap {U : ℕ} {itemBase V w n idx : ℕ} {s_abs : Dictionary.State U}
    {s : Memory.State} (hw : 0 < w) (hrep : SmallArrayRep itemBase V w n s_abs s.mem)
    (hidx : idx < n) {u : Fin U}
    (hk : pairQuotAt itemBase (keyBits U) (valBits V) w s.mem idx = u.val) :
    let s' := (Memory.spec 0).clientState s
      (smallDeleteSwapGenProg ((((itemBase, (keyBits U, valBits V)), w), (idx, n))))
    s'.frontier = s.frontier ∧
    SmallArrayRep itemBase V w (n - 1) (Function.update s_abs u none) s'.mem := by
  dsimp only
  have hsome : (s_abs u).isSome := by
    rw [(hrep.mem_iff u (pairValAt itemBase (keyBits U) (valBits V) w s.mem idx)).mpr
      ⟨idx, hidx, hk, rfl⟩]
    rfl
  have hcard' : (Dictionary.dom (Function.update s_abs u none)).card = n - 1 := by
    rw [Dynamic.card_dom_delete_eq_of_isSome hsome, hrep.card_eq]
  unfold smallDeleteSwapGenProg
  simp only [pure_bind]
  by_cases hlt : idx < n - 1
  · rw [ite_eq_left hlt, StateTransitionSpec.clientState_bind, clientState_readPairGenProg,
      clientResult_readPairGenProg, clientState_writePairGenProg]
    dsimp only
    set last := n - 1
    have hlast_lt : last < n := by omega
    set qL := pairQuotAt itemBase (keyBits U) (valBits V) w s.mem last
    set vL := pairValAt itemBase (keyBits U) (valBits V) w s.mem last
    have hqL_pow : qL < 2 ^ keyBits U := pairQuotAt_lt ..
    have hvL_pow : vL < 2 ^ valBits V := pairValAt_lt ..
    set m' := writePair itemBase (keyBits U) (valBits V) w s.mem idx qL vL
    let srcIdx : ℕ → ℕ := fun i => if i = idx then last else i
    have hsrc_lt : ∀ i < last, srcIdx i < n := fun i hi => by
      dsimp only [srcIdx]; split_ifs <;> omega
    have hsrc_ne_idx : ∀ i < last, srcIdx i ≠ idx := fun i hi => by
      dsimp only [srcIdx]; split_ifs with h <;> omega
    have hpair_eq : ∀ i < last,
        pairQuotAt itemBase (keyBits U) (valBits V) w m' i =
          pairQuotAt itemBase (keyBits U) (valBits V) w s.mem (srcIdx i) ∧
        pairValAt itemBase (keyBits U) (valBits V) w m' i =
          pairValAt itemBase (keyBits U) (valBits V) w s.mem (srcIdx i) := fun i _ => by
      dsimp only [srcIdx]
      split_ifs with hi
      · subst hi
        exact ⟨pairQuotAt_writePair_self hw s.mem hqL_pow,
          pairValAt_writePair_self s.mem hvL_pow⟩
      · exact ⟨pairQuotAt_writePair_of_ne hw s.mem hi,
          pairValAt_writePair_of_ne hw s.mem hi⟩
    refine ⟨rfl, hcard'.symm, (Nat.sub_le n 1).trans hrep.n_le_U, fun i hi => ?_, fun i hi => ?_,
      fun i j hi hj heq => ?_, fun u' v' => ?_⟩
    · rw [(hpair_eq i hi).1]; exact hrep.key_lt _ (hsrc_lt i hi)
    · rw [(hpair_eq i hi).2]; exact hrep.val_lt _ (hsrc_lt i hi)
    · rw [(hpair_eq i hi).1, (hpair_eq j hj).1] at heq
      have hse := hrep.key_inj _ _ (hsrc_lt i hi) (hsrc_lt j hj) heq
      dsimp only [srcIdx] at hse
      split_ifs at hse <;> omega
    · by_cases hu' : u' = u
      · subst hu'
        rw [Function.update_self]
        refine ⟨fun h => (by cases h), ?_⟩
        rintro ⟨i, hi, hki, _⟩
        rw [(hpair_eq i hi).1] at hki
        exact False.elim
          (hsrc_ne_idx i hi (hrep.key_inj _ idx (hsrc_lt i hi) hidx (hki.trans hk.symm)))
      · rw [Function.update_of_ne hu', hrep.mem_iff]
        constructor
        · rintro ⟨j, hj, hkj, hvj⟩
          have hj_ne_idx : j ≠ idx := fun heq => hu' (Fin.ext (by rw [← hkj, heq, hk]))
          by_cases hj_last : j = last
          · subst hj_last
            refine ⟨idx, hlt, ?_, ?_⟩
            · rw [(hpair_eq idx hlt).1]; dsimp only [srcIdx]; simp [hkj]
            · rw [(hpair_eq idx hlt).2]; dsimp only [srcIdx]; simp [hvj]
          · have hj_lt : j < last := by omega
            refine ⟨j, hj_lt, ?_, ?_⟩
            · rw [(hpair_eq j hj_lt).1]; dsimp only [srcIdx]; simp [hj_ne_idx, hkj]
            · rw [(hpair_eq j hj_lt).2]; dsimp only [srcIdx]; simp [hj_ne_idx, hvj]
        · rintro ⟨i, hi, hki, hvi⟩
          rw [(hpair_eq i hi).1] at hki
          rw [(hpair_eq i hi).2] at hvi
          exact ⟨srcIdx i, hsrc_lt i hi, hki, hvi⟩
  · have heq_idx : idx = n - 1 := by omega
    subst heq_idx
    rw [ite_eq_right hlt]
    have hst_pure : (Memory.spec 0).clientState s (pure () : Memory.Prog Unit) = s := rfl
    rw [hst_pure]
    refine ⟨rfl, hcard'.symm, (Nat.sub_le n 1).trans hrep.n_le_U,
      fun i hi => hrep.key_lt i (by omega), fun i hi => hrep.val_lt i (by omega),
      fun i j hi hj heq => hrep.key_inj i j (by omega) (by omega) heq, fun u' v' => ?_⟩
    by_cases hu' : u' = u
    · subst hu'
      rw [Function.update_self]
      refine ⟨fun h => (by cases h), ?_⟩
      rintro ⟨i, hi, hki, _⟩
      have hij := hrep.key_inj i (n - 1) (by omega) hidx (hki.trans hk.symm)
      exact False.elim (by omega)
    · rw [Function.update_of_ne hu', hrep.mem_iff]
      constructor
      · rintro ⟨j, hj, hkj, hvj⟩
        have hj_ne : j ≠ n - 1 := fun heq => hu' (Fin.ext (by rw [← hkj, heq, hk]))
        exact ⟨j, by omega, hkj, hvj⟩
      · rintro ⟨i, hi, hki, hvi⟩
        exact ⟨i, by omega, hki, hvi⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

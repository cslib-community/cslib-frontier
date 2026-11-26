/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
public import CslibFrontier.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
public import CslibFrontier.DataStructure.WordRAM.Randomized.HighProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Memory Layout, Runtime Parameter Block, and Representation Invariants for `SuccinctWhp`

This module defines the concrete Word-RAM word layout within
`[base, base + whpSpace c U V w n_max)`,
the 68-word runtime parameter vector `WhpCoreParams` (paired with the two `HashParams` vectors into
the 100-word `WhpParams` input record), and the
concrete memory representation invariants (`SmallMemRep`, `CsrMemRep`, `BTreeSliceMemRep`,
`BufTrieMemRep`, `FastMemRep`, `SeedWhpMemRep`, and `WhpMemRep`) linking Word-RAM memory `x.mem` to
the pure state machine `WhpDictState` of `SuccinctWhpModel`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.WhpCoreParams`, `WhpParams`,
  `mkWhpCoreParams`, `mkWhpParams`: runtime parameter tuples for parameter-free `Realizes .exact`
  subroutines.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.SmallMemRep`, `CsrMemRep`,
  `BTreeSliceMemRep`, `BufTrieMemRep`, `FastMemRep`, `SeedWhpMemRep`, `WhpMemRep`:
  concrete Word-RAM memory representation predicates across `.small`, `.fast`, and `.fallback`
  modes.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.smallOffsets_eq`,
  `largeOffsets_eq`, `largeOffsetChain`: exact segment accounting and adjacent offset chain matching
  `smallSpaceWhp` and `largeSpaceWhp`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fits_mkWhpParams`: every word of
  `mkWhpParams` fits in `w` bits whenever `0 < w`, `n_max ≤ U`, `Fits w U`, `Fits w V`, and
  `Fits w (base + whpSpace c U V w n_max)`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.WhpMemRep.congr_footprint`: frame invariance
  of `WhpMemRep` under memory changes outside `[base, base + whpSpace c U V w n_max)`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
  (memoryCost_bind_of_clientState_eq lt_two_pow_globalPtrBits_of_le_n_max)
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Header slots and segment word offsets -/

/-- Header slot `0`: active regime tag (`0` = `.small`, `1` = `.fast`, `2` = `.fallback`). -/
@[expose] def hdrMode : ℕ := 0
/-- Header slot `1`: `fs.poolFreeTop`. -/
@[expose] def hdrPoolFreeTop : ℕ := 1
/-- Header slot `2`: `fs.curEp` (`0` or `1`). -/
@[expose] def hdrCurEp : ℕ := 2
/-- Header slot `3`: `fs.epochClock`. -/
@[expose] def hdrEpochClock : ℕ := 3
/-- Header slot `4`: `fs.rebStage` (`0 .. 5`). -/
@[expose] def hdrRebStage : ℕ := 4
/-- Header slot `5`: `fs.stageCursor`. -/
@[expose] def hdrStageCursor : ℕ := 5
/-- Header slot `6`: `fs.dirtyCount`. -/
@[expose] def hdrDirtyCount : ℕ := 6
/-- Header slot `7`: `fs.dirtyIdx`. -/
@[expose] def hdrDirtyIdx : ℕ := 7
/-- Header slot `8`: `fs.rebCandSalt`. -/
@[expose] def hdrRebCandSalt : ℕ := 8
/-- Header slot `9`: `fs.rebScanCursor`. -/
@[expose] def hdrRebScanCursor : ℕ := 9
/-- Header slot `10`: `fs.rebInsCount`. -/
@[expose] def hdrRebInsCount : ℕ := 10
/-- Header slot `11`: `fs.rebCollision`. -/
@[expose] def hdrRebCollision : ℕ := 11
/-- Header slot `12`: `(fs.buf 0).nodeAlloc`. -/
@[expose] def hdrBuf0NodeAlloc : ℕ := 12
/-- Header slot `13`: `(fs.buf 0).itemAlloc`. -/
@[expose] def hdrBuf0ItemAlloc : ℕ := 13
/-- Header slot `14`: `(fs.buf 1).nodeAlloc`. -/
@[expose] def hdrBuf1NodeAlloc : ℕ := 14
/-- Header slot `15`: `(fs.buf 1).itemAlloc`. -/
@[expose] def hdrBuf1ItemAlloc : ℕ := 15

/-- Small-regime occupancy array offset (`base + 32`). -/
@[expose] def offSmallPres : ℕ := 32

/-- Small-regime packed keys array offset. -/
@[expose] def offSmallKeys (_U w n_max : ℕ) : ℕ :=
  offSmallPres + packedWords n_max 1 w

/-- Small-regime packed values array offset. -/
@[expose] def offSmallVals (U w n_max : ℕ) : ℕ :=
  offSmallKeys U w n_max + packedWords n_max (keyBits U) w

theorem smallOffsets_eq (U V w n_max : ℕ) :
    offSmallVals U w n_max + packedWords n_max (valBits V) w = smallSpaceWhp U V w n_max := by
  unfold offSmallVals offSmallKeys offSmallPres smallSpaceWhp
  omega

/-- Word count of `θ.1 : BktSeed c U n_max` (`BitPackedDoubleTabulation.space`). -/
@[expose] def bktHashWords (c w n_max : ℕ) : ℕ :=
  BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max)

/-- Word count of `θ.2 : FpSeed c U n_max` (`BitPackedDoubleTabulation.space`). -/
@[expose] def fpHashWords (c w n_max : ℕ) : ℕ :=
  BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)

/-- Large-regime bucket-hash block offset (`base + 32`). -/
@[expose] def offHashBkt : ℕ := 32

/-- Large-regime fingerprint-hash block offset. -/
@[expose] def offHashFp (c w n_max : ℕ) : ℕ :=
  offHashBkt + bktHashWords c w n_max

/-- Large-regime Feistel quotients array offset (`n_max` entries of `quotBitsWhp U n_max` bits). -/
@[expose] def offQuotWhp (c w n_max : ℕ) : ℕ :=
  offHashFp c w n_max + fpHashWords c w n_max

/-- Large-regime values array offset (`n_max` entries of `valBits V` bits). -/
@[expose] def offValWhp (c U w n_max : ℕ) : ℕ :=
  offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w

/-- Start of the 13 auxiliary packed arrays in `largeAuxWordsWhp`. -/
@[expose] def offPermAct (c U V w n_max : ℕ) : ℕ :=
  offValWhp c U w n_max + packedWords n_max (valBits V) w

/-- 2-bit per-coordinate location tag array (`M * totalLocalCoordsWhp n_max` entries). -/
@[expose] def offLocState (c U V w n_max : ℕ) : ℕ :=
  offPermAct c U V w n_max + packedWords n_max (12 * logLogFactor n_max + 4) w

/-- Per-bucket scalar metadata and slice `(alloc, root)` array (`16 * M` entries of
`globalPtrBits n_max` bits). -/
@[expose] def offBktMeta (c U V w n_max : ℕ) : ℕ :=
  offLocState c U V w n_max + packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w

/-- CSR bucket prefix-sum array `fbStart` (`M + 1` entries of `globalPtrBits n_max` bits). -/
@[expose] def offFbStart (c U V w n_max : ℕ) : ℕ :=
  offBktMeta c U V w n_max + packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w

/-- Backyard pointer directory `backPtr` (`M * capBackWhp n_max` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offBackPtr (c U V w n_max : ℕ) : ℕ :=
  offFbStart c U V w n_max + packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w

/-- Auxiliary backyard scratch array (`M * capBackWhp n_max` entries of `12 * logLogFactor + 4`
bits). -/
@[expose] def offBackAux (c U V w n_max : ℕ) : ℕ :=
  offBackPtr c U V w n_max +
    packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w

/-- Backyard free-slot stack `poolFreeStack` (`poolSizeWhp n_max` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offPoolFreeStack (c U V w n_max : ℕ) : ℕ :=
  offBackAux c U V w n_max +
    packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * logLogFactor n_max + 4) w

/-- Backyard reverse owner array `poolOwner` (`poolSizeWhp n_max` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offPoolOwner (c U V w n_max : ℕ) : ℕ :=
  offPoolFreeStack c U V w n_max + packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w

/-- SWAR B+-tree node metadata array (`totalBTreeNodesWhp n_max` entries of `nodeMetaBitsWhp n_max`
bits). -/
@[expose] def offBtMeta (c U V w n_max : ℕ) : ℕ :=
  offPoolOwner c U V w n_max + packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w

/-- SWAR B+-tree node keys-word array (`totalBTreeNodesWhp n_max` entries of `keysWordBitsWhp n_max`
bits). -/
@[expose] def offBtKeys (c U V w n_max : ℕ) : ℕ :=
  offBtMeta c U V w n_max + packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w

/-- SWAR B+-tree node vals-word array (`totalBTreeNodesWhp n_max` entries of `valsWordBitsWhp n_max`
bits). -/
@[expose] def offBtVals (c U V w n_max : ℕ) : ℕ :=
  offBtKeys c U V w n_max + packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w

/-- Total child-pointer entries `maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max` per buffer
trie. -/
@[expose] def trieChildEntriesWhp (c n_max : ℕ) : ℕ :=
  maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max

/-- Epoch buffer `0` `trieChild` array (`trieChildEntriesWhp c n_max` entries of
`globalPtrBits n_max` bits). -/
@[expose] def offTrieChild0 (c U V w n_max : ℕ) : ℕ :=
  offBtVals c U V w n_max + packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w

/-- Epoch buffer `1` `trieChild` array. -/
@[expose] def offTrieChild1 (c U V w n_max : ℕ) : ℕ :=
  offTrieChild0 c U V w n_max + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `0` per-node metadata array (`6 * maxTrieNodesWhp c n_max` entries of
`globalPtrBits n_max` bits; `4 * u + 0..3` store `nodeParent`, `nodeChar`, `nodeLeafItem`,
`nodeActive`). -/
@[expose] def offTrieMeta0 (c U V w n_max : ℕ) : ℕ :=
  offTrieChild1 c U V w n_max + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `1` per-node metadata array. -/
@[expose] def offTrieMeta1 (c U V w n_max : ℕ) : ℕ :=
  offTrieMeta0 c U V w n_max +
    packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `0` item log (`0 .. 3 * qEpoch - 1`) + `dirtyBuckets`
(`3 * qEpoch .. 4 * qEpoch - 1`) array (`6 * qEpochWhp n_max + 6` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offTrieItems0 (c U V w n_max : ℕ) : ℕ :=
  offTrieMeta1 c U V w n_max +
    packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w

/-- Epoch buffer `1` item log array (`6 * qEpochWhp n_max + 6` entries of `globalPtrBits n_max`
bits). -/
@[expose] def offTrieItems1 (c U V w n_max : ℕ) : ℕ :=
  offTrieItems0 c U V w n_max + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w

theorem largeOffsets_eq (c U V w n_max : ℕ) :
    offTrieItems1 c U V w n_max +
      packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w =
      largeSpaceWhp c U V w n_max := by
  dsimp only [offTrieItems1, offTrieItems0, offTrieMeta1, offTrieMeta0, offTrieChild1,
    offTrieChild0, offBtVals, offBtKeys, offBtMeta, offPoolOwner, offPoolFreeStack, offBackAux,
    offBackPtr, offFbStart, offBktMeta, offLocState, offPermAct, offValWhp, offQuotWhp,
    offHashFp, offHashBkt, bktHashWords, fpHashWords, trieChildEntriesWhp, totalLocalCoordsWhp,
    largeSpaceWhp]
  ring

/-- Complete adjacent segment-offset chain for `largeSpaceWhp`, allowing `omega` to discharge
cross-segment disjointness and footprint bounds without unfolding the individual `off*`
definitions. -/
theorem largeOffsetChain (c U V w n_max : ℕ) :
    offHashBkt = 32 ∧
    0 < bktHashWords c w n_max ∧
    bktHashWords c w n_max =
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) ∧
    fpHashWords c w n_max =
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
        (fpBitsWhp n_max) ∧
    offHashFp c w n_max = offHashBkt + bktHashWords c w n_max ∧
    offQuotWhp c w n_max = offHashFp c w n_max + fpHashWords c w n_max ∧
    offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ∧
    offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w ∧
    offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * logLogFactor n_max + 4) w ∧
    offBktMeta c U V w n_max =
      offLocState c U V w n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w ∧
    offFbStart c U V w n_max =
      offBktMeta c U V w n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ∧
    offBackPtr c U V w n_max =
      offFbStart c U V w n_max +
        packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w ∧
    offBackAux c U V w n_max =
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ∧
    offPoolFreeStack c U V w n_max =
      offBackAux c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (12 * logLogFactor n_max + 4) w ∧
    offPoolOwner c U V w n_max =
      offPoolFreeStack c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ∧
    offBtMeta c U V w n_max =
      offPoolOwner c U V w n_max +
        packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ∧
    offBtKeys c U V w n_max =
      offBtMeta c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w ∧
    offBtVals c U V w n_max =
      offBtKeys c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w ∧
    offTrieChild0 c U V w n_max =
      offBtVals c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w ∧
    offTrieChild1 c U V w n_max =
      offTrieChild0 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ∧
    offTrieMeta0 c U V w n_max =
      offTrieChild1 c U V w n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ∧
    offTrieMeta1 c U V w n_max =
      offTrieMeta0 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ∧
    offTrieItems0 c U V w n_max =
      offTrieMeta1 c U V w n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ∧
    offTrieItems1 c U V w n_max =
      offTrieItems0 c U V w n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ∧
    offTrieItems1 c U V w n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w =
      largeSpaceWhp c U V w n_max := by
  have hb_pos : 0 < bktHashWords c w n_max := by
    unfold bktHashWords BitPackedDoubleTabulation.space
    omega
  exact ⟨rfl, hb_pos, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, largeOffsets_eq c U V w n_max⟩

/-! ## Section 2: Threshold, bit-width, and word-fit inequalities -/

theorem keyBits_le_w {U w : ℕ} (hU : Fits w U) : keyBits U ≤ w :=
  Nat.clog_le_of_le_pow hU.le

theorem valBits_le_w {V w : ℕ} (hV : Fits w V) : valBits V ≤ w :=
  Nat.clog_le_of_le_pow hV.le

theorem w0Whp_le_w {U w : ℕ} (hw : 0 < w) (hU : Fits w U) : w0Whp U ≤ w :=
  max_le hw (keyBits_le_w hU)

theorem globalPtrBits_le_w {U w n_max : ℕ} (hnU : n_max ≤ U) (hU : Fits w U) :
    globalPtrBits n_max ≤ w := by
  unfold globalPtrBits
  exact Nat.clog_le_of_le_pow (by dsimp [Fits] at hU; omega)

theorem log_n_max_lt_w {c U w n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (hnU : n_max ≤ U) (hU : Fits w U) :
    Nat.log 2 n_max < w := by
  have hn0 : 0 < n_max := (whpThreshold_pos c).trans_le hth
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (((Nat.pow_log_le_self 2 hn0.ne').trans hnU).trans_lt hU)

theorem two_mul_rIndepWhp_lt_qEpochWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    2 * sMaxWhp c n_max < qEpochWhp n_max := by
  have hbmin : bMinWhp c ≤ slabScale n_max :=
    (bMinWhp_le_log hth).trans (SuccinctWhp.log_le_scaleWhp n_max)
  have hce : cEff c + 4 ≤ slabScale n_max :=
    (cEff_add_four_le_bMinWhp c).trans hbmin
  have hL_ge : 6553600 ≤ slabScale n_max := (le_bMinWhp c).trans hbmin
  calc 2 * sMaxWhp c n_max
      = 2 * (cEff c + 4) * slabScale n_max := by unfold sMaxWhp; ring
    _ ≤ (slabScale n_max * slabScale n_max) * slabScale n_max :=
        Nat.mul_le_mul_right _ (by nlinarith)
    _ = (slabScale n_max) ^ 3 := by ring
    _ < (slabScale n_max) ^ 18 := Nat.pow_lt_pow_right (by omega) (by decide)

theorem globalPtrBits_pos_of_large {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    0 < globalPtrBits n_max := by
  have hn : 1 ≤ n_max := (whpThreshold_pos c).trans_le hth
  exact Nat.clog_pos Nat.one_lt_two (by omega)

theorem large_bounds_lt_n_max {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    1024 ≤ numBucketsWhp n_max ∧
    nSliceWhp n_max < n_max ∧
    totalLocalCoordsWhp n_max < n_max ∧
    8 * (slabScale n_max) ^ 12 < n_max ∧
    sMaxWhp c n_max < n_max ∧
    maxTrieNodesWhp c n_max < n_max ∧
    qEpochWhp n_max < n_max ∧
    2 ^ bCharWhp n_max < n_max := by
  have hlog := log_ge_mul_ell hth
  have hell := one_le_logLogFactor n_max
  have hL2 := two_le_slabScale n_max
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h8t := eight_le_tMinWhp hth
  obtain ⟨_, _, _, _, htm_le, hq6_le⟩ := sublinear_table_bits_le hth
  have hg_pos := globalPtrBits_pos_of_large hth
  have hb_ge : 10 ≤ bWhp n_max := by unfold bWhp; omega
  have hM_ge : 1024 ≤ numBucketsWhp n_max := by
    calc 1024 = 2 ^ 10 := by decide
      _ ≤ 2 ^ bWhp n_max := Nat.pow_le_pow_right (by decide) hb_ge
  have h1024L12 : 1024 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ hM_ge).trans hML12
  have hL12_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (by omega)
  have hnslice : nSliceWhp n_max < n_max := by
    have hd : 32 * (slabScale n_max) ^ 12 / (tMinWhp n_max - 1) ≤ 32 * (slabScale n_max) ^ 12 :=
      Nat.div_le_self _ _
    unfold nSliceWhp
    omega
  have htotLoc : totalLocalCoordsWhp n_max < n_max := by
    have hcf : capFrontWhp n_max ≤ n_max / 1024 :=
      (Nat.sub_le _ _).trans (Nat.div_le_div_left hM_ge (by decide))
    have hcb : capBackWhp n_max ≤ (slabScale n_max) ^ 12 := by
      unfold capBackWhp
      calc 2 * (slabScale n_max) ^ 11 ≤ slabScale n_max * (slabScale n_max) ^ 11 :=
            Nat.mul_le_mul_right _ hL2
        _ = (slabScale n_max) ^ 12 := by ring
    unfold totalLocalCoordsWhp
    omega
  have hpow3 := two_pow_three_mul_bCharWhp_le hth
  have hbc_ge : 320 ≤ bCharWhp n_max := by have := bCharWhp_ge_mul_ell hth; omega
  have hpow_bc_lt : 2 ^ bCharWhp n_max < n_max := by
    calc 2 ^ bCharWhp n_max < 2 ^ (3 * bCharWhp n_max) :=
          Nat.pow_lt_pow_right (by decide) (by omega)
      _ ≤ n_max := hpow3
  have hsMax_lt : sMaxWhp c n_max < n_max :=
    (sMaxWhp_le_pow_bChar hth).trans_lt hpow_bc_lt
  have h6mt : 6 * maxTrieNodesWhp c n_max ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hg_pos).trans htm_le
  have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
  have hmt_pos : 2 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
  exact ⟨hM_ge, hnslice, htotLoc, by omega, hsMax_lt, by omega, by omega, hpow_bc_lt⟩

/-- Convolution width `(4 * tMinWhp n_max) * keyLaneBitsWhp n_max` fits strictly inside
`Nat.log 2 n_max` whenever `whpThreshold c ≤ n_max`. -/
theorem swarConvBits_lt_log {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    (4 * tMinWhp n_max) * keyLaneBitsWhp n_max < Nat.log 2 n_max := by
  have h := log_ge_mul_ell hth
  have h1 := one_le_logLogFactor n_max
  have h8 := eight_le_tMinWhp hth
  have ht : tMinWhp n_max = Nat.log 2 n_max / (160 * logLogFactor n_max) := by
    unfold tMinWhp at h8 ⊢; omega
  have hmul : tMinWhp n_max * (160 * logLogFactor n_max) ≤ Nat.log 2 n_max := by
    rw [ht]; exact Nat.div_mul_le_self _ _
  have hkl : keyLaneBitsWhp n_max ≤ 38 * logLogFactor n_max := by
    unfold keyLaneBitsWhp fpBitsWhp; omega
  calc (4 * tMinWhp n_max) * keyLaneBitsWhp n_max
      ≤ (4 * tMinWhp n_max) * (38 * logLogFactor n_max) := Nat.mul_le_mul_left _ hkl
    _ = 152 * (tMinWhp n_max * logLogFactor n_max) := by ring
    _ < 160 * (tMinWhp n_max * logLogFactor n_max) := by nlinarith
    _ = tMinWhp n_max * (160 * logLogFactor n_max) := by ring
    _ ≤ Nat.log 2 n_max := hmul

private theorem readPacked_eq_of_mem_eq {base space off N k w idx val : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < w)
    (hmem : ∀ a, base ≤ a → a < base + space → mem₂ a = mem₁ a)
    (h : readPacked (base + off) k w mem₁ idx = val)
    (hidx : idx < N)
    (hle : off + packedWords N k w ≤ space) :
    readPacked (base + off) k w mem₂ idx = val :=
  (readPacked_congr hw (hidx := hidx) fun a ⟨ha1, ha2⟩ => hmem a (by omega) (by omega)).trans h

/-! ## Section 4: Concrete memory representation invariants (`WhpMemRep`) -/

/-- Memory representation of `SmallDictState` at `base` (`mem[base] = 0`). -/
@[expose] def SmallMemRep (base U V w n_max : ℕ) (sm : SmallDictState) (mem : ℕ → ℕ) : Prop :=
  mem (base + hdrMode) = 0 ∧
  (∀ i < n_max,
    readPacked (base + offSmallPres) 1 w mem i = sm.present i ∧
    readPacked (base + offSmallKeys U w n_max) (keyBits U) w mem i = sm.keys i ∧
    readPacked (base + offSmallVals U w n_max) (valBits V) w mem i = sm.vals i)

/-- Memory representation of `CsrState` at `base` (`mem[base] = 2`). -/
@[expose] def CsrMemRep (base c U V w n_max : ℕ) (csr : CsrState) (mem : ℕ → ℕ) : Prop :=
  mem (base + hdrMode) = 2 ∧
  (∀ b ≤ numBucketsWhp n_max,
    readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w mem b = csr.fbStart b) ∧
  (∀ i < n_max,
    readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w mem i = csr.qArr i ∧
    readPacked (base + offValWhp c U w n_max) (valBits V) w mem i = csr.vArr i)

/-- Memory representation of a single SWAR B+-tree slice `sIdx = 3 * b + role < 3 * M` on its
allocated prefix `0 .. sl.alloc - 1`. -/
@[expose] def BTreeSliceMemRep (base c U V w n_max sIdx : ℕ) (sl : BTreeSlice)
    (mem : ℕ → ℕ) : Prop :=
  let b := sIdx / 3
  let role := sIdx % 3
  let gBits := globalPtrBits n_max
  sl.alloc ≤ nSliceWhp n_max ∧
  readPacked (base + offBktMeta c U V w n_max) gBits w mem (16 * b + 10 + 2 * role) = sl.alloc ∧
  readPacked (base + offBktMeta c U V w n_max) gBits w mem (16 * b + 11 + 2 * role) = sl.root ∧
  ∀ u < sl.alloc,
    let idx := sIdx * nSliceWhp n_max + u
    readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w mem idx =
      (sl.nodes u).metaWord ∧
    readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w mem idx =
      (sl.nodes u).keysWord ∧
    readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w mem idx =
      (sl.nodes u).valsWord

/-- Memory representation of epoch buffer trie `ep ∈ {0, 1}`. -/
@[expose] def BufTrieMemRep (base c U V w n_max ep : ℕ) (tr : BufTrie) (mem : ℕ → ℕ) : Prop :=
  let offChild := if ep = 0 then offTrieChild0 c U V w n_max else offTrieChild1 c U V w n_max
  let offMeta := if ep = 0 then offTrieMeta0 c U V w n_max else offTrieMeta1 c U V w n_max
  let offItems := if ep = 0 then offTrieItems0 c U V w n_max else offTrieItems1 c U V w n_max
  let hdrNA := if ep = 0 then hdrBuf0NodeAlloc else hdrBuf1NodeAlloc
  let hdrIA := if ep = 0 then hdrBuf0ItemAlloc else hdrBuf1ItemAlloc
  let gBits := globalPtrBits n_max
  let qEp := qEpochWhp n_max
  tr.nodeAlloc ≤ maxTrieNodesWhp c n_max ∧
  tr.itemAlloc ≤ qEp ∧
  mem (base + hdrNA) = tr.nodeAlloc ∧
  mem (base + hdrIA) = tr.itemAlloc ∧
  (∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
    readPacked (base + offChild) gBits w mem (u * 2 ^ bCharWhp n_max + ch) = tr.trieChild u ch) ∧
  (∀ u, 1 ≤ u → u < tr.nodeAlloc →
    readPacked (base + offMeta) gBits w mem (4 * u + 0) = tr.nodeParent u ∧
    readPacked (base + offMeta) gBits w mem (4 * u + 1) = tr.nodeChar u) ∧
  (∀ u < tr.nodeAlloc,
    readPacked (base + offMeta) gBits w mem (4 * u + 2) = tr.nodeLeafItem u ∧
    (tr.nodeLeafItem u ≠ 0 →
      readPacked (base + offMeta) gBits w mem (4 * u + 3) = tr.nodeActive u)) ∧
  (∀ id < tr.itemAlloc,
    readPacked (base + offItems) gBits w mem id = tr.itemLeaf id ∧
    readPacked (base + offItems) gBits w mem (qEp + id) = tr.itemBucket id ∧
    readPacked (base + offItems) gBits w mem (2 * qEp + id) = tr.itemLoc id)

/-- Memory representation of `FastState` at `base` (`mem[base] = 1`). -/
@[expose] def FastMemRep (base c U V w n_max : ℕ) (fs : FastState) (mem : ℕ → ℕ) : Prop :=
  let M := numBucketsWhp n_max
  let gBits := globalPtrBits n_max
  let qEp := qEpochWhp n_max
  fs.dirtyCount ≤ qEp ∧
  mem (base + hdrMode) = 1 ∧
  mem (base + hdrPoolFreeTop) = fs.poolFreeTop ∧
  mem (base + hdrCurEp) = fs.curEp ∧
  mem (base + hdrEpochClock) = fs.epochClock ∧
  mem (base + hdrRebStage) = fs.rebStage ∧
  mem (base + hdrStageCursor) = fs.stageCursor ∧
  mem (base + hdrDirtyCount) = fs.dirtyCount ∧
  mem (base + hdrDirtyIdx) = fs.dirtyIdx ∧
  mem (base + hdrRebCandSalt) = fs.rebCandSalt ∧
  mem (base + hdrRebScanCursor) = fs.rebScanCursor ∧
  mem (base + hdrRebInsCount) = fs.rebInsCount ∧
  mem (base + hdrRebCollision) = fs.rebCollision ∧
  (∀ i < n_max,
    readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w mem i = fs.quotArr i ∧
    readPacked (base + offValWhp c U w n_max) (valBits V) w mem i = fs.valArr i) ∧
  (∀ b < M, ∀ loc < totalLocalCoordsWhp n_max,
    readPacked (base + offLocState c U V w n_max) 2 w mem (b * totalLocalCoordsWhp n_max + loc) =
      fs.locState b loc) ∧
  (∀ b < M,
    let bm := offBktMeta c U V w n_max
    readPacked (base + bm) gBits w mem (16 * b + 0) = fs.bktCount b ∧
    readPacked (base + bm) gBits w mem (16 * b + 1) = fs.bktSalt b ∧
    readPacked (base + bm) gBits w mem (16 * b + 2) = fs.liveRole b ∧
    readPacked (base + bm) gBits w mem (16 * b + 3) = fs.liveInsCount b ∧
    readPacked (base + bm) gBits w mem (16 * b + 4) = fs.overmarsRole b ∧
    readPacked (base + bm) gBits w mem (16 * b + 5) = fs.overmarsActive b ∧
    readPacked (base + bm) gBits w mem (16 * b + 6) = fs.overmarsCursor b ∧
    readPacked (base + bm) gBits w mem (16 * b + 7) = fs.overmarsInsCount b ∧
    readPacked (base + bm) gBits w mem (16 * b + 8) = fs.rebDoneFlag b ∧
    readPacked (base + bm) gBits w mem (16 * b + 9) = fs.rebQueued b) ∧
  (∀ b < M, ∀ k < capBackWhp n_max,
    readPacked (base + offBackPtr c U V w n_max) gBits w mem (b * capBackWhp n_max + k) =
      fs.backPtr b k) ∧
  (∀ j < poolSizeWhp n_max,
    readPacked (base + offPoolFreeStack c U V w n_max) gBits w mem j = fs.poolFreeStack j ∧
    readPacked (base + offPoolOwner c U V w n_max) gBits w mem j = fs.poolOwner j) ∧
  (∀ sIdx < 3 * M, BTreeSliceMemRep base c U V w n_max sIdx (fs.slices sIdx) mem) ∧
  BufTrieMemRep base c U V w n_max 0 (fs.buf 0) mem ∧
  BufTrieMemRep base c U V w n_max 1 (fs.buf 1) mem ∧
  (∀ j < fs.dirtyCount,
    readPacked (base + offTrieItems0 c U V w n_max) gBits w mem (3 * qEp + j) = fs.dirtyBuckets j)

/-- Memory representation of the two static double-tabulation seeds `(θ.1, θ.2)` in the large
regime. -/
@[expose] def SeedWhpMemRep (base c U w n_max : ℕ) (θ : SeedWhp c U n_max)
    (mem : ℕ → ℕ) : Prop :=
  BitPackedDoubleTabulation.SeedRep (base + offHashBkt) w (w0Whp U)
    (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) θ.1 mem ∧
  BitPackedDoubleTabulation.SeedRep (base + offHashFp c w n_max) w (w0Whp U)
    (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max) θ.2 mem

/-- Combined memory representation linking `θ` and `st : WhpDictState` to `mem` across all
capacities `n_max`. -/
@[expose] def WhpMemRep (base c U V w n_max : ℕ) (θ : SeedWhp c U n_max)
    (st : WhpDictState) (mem : ℕ → ℕ) : Prop :=
  match st with
  | .small sm => n_max < whpThreshold c ∧ SmallMemRep base U V w n_max sm mem
  | .fast fs =>
    whpThreshold c ≤ n_max ∧
    SeedWhpMemRep base c U w n_max θ mem ∧
    FastMemRep base c U V w n_max fs mem
  | .fallback csr =>
    whpThreshold c ≤ n_max ∧
    SeedWhpMemRep base c U w n_max θ mem ∧
    CsrMemRep base c U V w n_max csr mem

/-- `SeedWhpMemRep` depends only on `[base + offHashBkt, base + offQuotWhp c w n_max)`. -/
theorem SeedWhpMemRep.congr_hash {base c U w n_max : ℕ} {θ : SeedWhp c U n_max}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w)
    (heq : ∀ a, base + offHashBkt ≤ a → a < base + offQuotWhp c w n_max → mem₁ a = mem₂ a)
    (hseed : SeedWhpMemRep base c U w n_max θ mem₁) :
    SeedWhpMemRep base c U w n_max θ mem₂ := by
  have hch := largeOffsetChain c U 0 w n_max
  exact ⟨BitPackedDoubleTabulation.seedRep_congr_mem hw hseed.1
      (fun a ha1 ha2 => (heq a ha1 (by omega)).symm),
    BitPackedDoubleTabulation.seedRep_congr_mem hw hseed.2
      (fun a ha1 ha2 => (heq a (by omega) (by omega)).symm)⟩

private theorem bufTrieMemRep_congr {base c U V w n_max ep : ℕ} {tr : BufTrie}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w) (hep : ep = 0 ∨ ep = 1)
    (hmem : ∀ a, base ≤ a → a < base + largeSpaceWhp c U V w n_max → mem₂ a = mem₁ a)
    (hrep : BufTrieMemRep base c U V w n_max ep tr mem₁) :
    BufTrieMemRep base c U V w n_max ep tr mem₂ := by
  have hch := largeOffsetChain c U V w n_max
  let rp := @readPacked_eq_of_mem_eq base (largeSpaceWhp c U V w n_max)
  dsimp only [BufTrieMemRep] at hrep ⊢
  obtain ⟨hna, hia, hhdr_na, hhdr_ia, hch, hpar, hleaf, hitems⟩ := hrep
  rcases hep with rfl | rfl
  all_goals
    dsimp only [hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc] at *
    simp +decide only [↓reduceIte] at hhdr_na hhdr_ia hch hpar hleaf hitems ⊢
    refine ⟨hna, hia,
      (hmem _ (by omega) (by omega)).trans hhdr_na,
      (hmem _ (by omega) (by omega)).trans hhdr_ia,
      fun u hu ch hch_lt => ?_, fun u hu1 hu => ?_, fun u hu => ?_, fun id hid => ?_⟩
    · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
        unfold trieChildEntriesWhp
        calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
              Nat.add_lt_add_left hch_lt _
          _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
          _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
      exact rp hw hmem (hch u hu ch hch_lt) hidx (by omega)
    · exact ⟨rp hw hmem (hpar u hu1 hu).1 (show 4 * u + 0 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega),
        rp hw hmem (hpar u hu1 hu).2 (show 4 * u + 1 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega)⟩
    · exact ⟨rp hw hmem (hleaf u hu).1 (show 4 * u + 2 < 6 * maxTrieNodesWhp c n_max by omega)
          (by omega),
        fun hnz => rp hw hmem ((hleaf u hu).2 hnz)
          (show 4 * u + 3 < 6 * maxTrieNodesWhp c n_max by omega) (by omega)⟩
    · exact ⟨rp hw hmem (hitems id hid).1 (show id < 6 * qEpochWhp n_max + 6 by omega) (by omega),
        rp hw hmem (hitems id hid).2.1
          (show qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) (by omega),
        rp hw hmem (hitems id hid).2.2
          (show 2 * qEpochWhp n_max + id < 6 * qEpochWhp n_max + 6 by omega) (by omega)⟩

/-- Pure footprint invariance of `WhpMemRep`: depends only on memory words in
`[base, base + whpSpace c U V w n_max)`. -/
theorem WhpMemRep.congr_footprint {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {st : WhpDictState} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < w)
    (heq : ∀ a ∈ (Block.mk base (whpSpace c U V w n_max)).footprint, mem₂ a = mem₁ a)
    (hrep : WhpMemRep base c U V w n_max θ st mem₁) :
    WhpMemRep base c U V w n_max θ st mem₂ := by
  have hmem : ∀ a, base ≤ a → a < base + whpSpace c U V w n_max → mem₂ a = mem₁ a :=
    fun a h1 h2 => heq a (by simp only [Block.mem_footprint, Block.Owns]; exact ⟨h1, h2⟩)
  -- Shared layout chain for large regime
  have hch := largeOffsetChain c U V w n_max
  cases st with
  | small sm =>
    obtain ⟨hsm, hm0, hfields⟩ := hrep
    rw [whpSpace, ite_eq_left hsm] at hmem
    have hs0 : hdrMode = 0 := rfl
    have hend := smallOffsets_eq U V w n_max
    dsimp only [offSmallVals, offSmallKeys, offSmallPres] at hend
    let rp := @readPacked_eq_of_mem_eq base (smallSpaceWhp U V w n_max)
    refine ⟨hsm, (hmem _ (by omega) (by omega)).trans hm0, fun i hi => ?_⟩
    obtain ⟨hp, hk, hv⟩ := hfields i hi
    exact ⟨rp hw hmem hp hi (by dsimp only [offSmallPres]; omega),
      rp hw hmem hk hi (by dsimp only [offSmallKeys, offSmallPres]; omega),
      rp hw hmem hv hi (by dsimp only [offSmallVals, offSmallKeys, offSmallPres]; omega)⟩
  | fallback csr =>
    obtain ⟨hth, hseed, hm0, hfb, hqv⟩ := hrep
    rw [whpSpace, ite_eq_right (Nat.not_lt.mpr hth)] at hmem
    let rp := @readPacked_eq_of_mem_eq base (largeSpaceWhp c U V w n_max)
    have hs0 : hdrMode = 0 := rfl
    refine ⟨hth,
      hseed.congr_hash hw (fun a ha1 ha2 => (hmem a (by omega) (by omega)).symm),
      (hmem _ (by omega) (by omega)).trans hm0,
      fun b hb => rp hw hmem (hfb b hb) (Nat.lt_add_one_of_le hb) (by omega),
      fun i hi => ⟨rp hw hmem (hqv i hi).1 hi (by omega), rp hw hmem (hqv i hi).2 hi (by omega)⟩⟩
  | fast fs =>
    obtain ⟨hth, hseed, hfast⟩ := hrep
    have hmemL : ∀ a, base ≤ a → a < base + largeSpaceWhp c U V w n_max → mem₂ a = mem₁ a := by
      rwa [whpSpace, ite_eq_right (Nat.not_lt.mpr hth)] at hmem
    have hhdr : ∀ h < 32, mem₂ (base + h) = mem₁ (base + h) :=
      fun h hh => hmemL (base + h) (by omega) (by omega)
    let rp := @readPacked_eq_of_mem_eq base (largeSpaceWhp c U V w n_max)
    dsimp only [FastMemRep] at hfast ⊢
    rcases hfast with ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      hqv, hloc, hbmeta, hbptr, hpool, hslices, hbuf0, hbuf1, hdirty⟩
    refine ⟨hth,
      hseed.congr_hash hw (fun a ha1 ha2 => (hmemL a (by omega) (by omega)).symm),
      hdc_le,
      (hhdr hdrMode (by decide)).trans hm0,
      (hhdr hdrPoolFreeTop (by decide)).trans hm1,
      (hhdr hdrCurEp (by decide)).trans hm2,
      (hhdr hdrEpochClock (by decide)).trans hm3,
      (hhdr hdrRebStage (by decide)).trans hm4,
      (hhdr hdrStageCursor (by decide)).trans hm5,
      (hhdr hdrDirtyCount (by decide)).trans hm6,
      (hhdr hdrDirtyIdx (by decide)).trans hm7,
      (hhdr hdrRebCandSalt (by decide)).trans hm8,
      (hhdr hdrRebScanCursor (by decide)).trans hm9,
      (hhdr hdrRebInsCount (by decide)).trans hm10,
      (hhdr hdrRebCollision (by decide)).trans hm11,
      fun i hi => ⟨rp hw hmemL (hqv i hi).1 hi (by omega),
        rp hw hmemL (hqv i hi).2 hi (by omega)⟩,
      fun b hb loc hloc_lt => ?_,
      fun b hb => ?_,
      fun b hb k hk => ?_,
      fun j hj => ⟨rp hw hmemL (hpool j hj).1 hj (by omega),
        rp hw hmemL (hpool j hj).2 hj (by omega)⟩,
      fun sIdx hsIdx => ?_,
      bufTrieMemRep_congr hw (Or.inl rfl) hmemL hbuf0,
      bufTrieMemRep_congr hw (Or.inr rfl) hmemL hbuf1,
      fun j hj => rp hw hmemL (hdirty j hj)
        (show 3 * qEpochWhp n_max + j < 6 * qEpochWhp n_max + 6 by omega) (by omega)⟩
    · have hidx : b * totalLocalCoordsWhp n_max + loc <
          numBucketsWhp n_max * totalLocalCoordsWhp n_max := by
        calc b * totalLocalCoordsWhp n_max + loc
            < b * totalLocalCoordsWhp n_max + totalLocalCoordsWhp n_max :=
              Nat.add_lt_add_left hloc_lt _
          _ = (b + 1) * totalLocalCoordsWhp n_max := by ring
          _ ≤ numBucketsWhp n_max * totalLocalCoordsWhp n_max := Nat.mul_le_mul_right _ hb
      exact rp hw hmemL (hloc b hb loc hloc_lt) hidx (by omega)
    · have hm := hbmeta b hb
      have hbm_le : offBktMeta c U V w n_max +
          packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
          largeSpaceWhp c U V w n_max := by omega
      exact ⟨rp hw hmemL hm.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.2.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.2.2.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.2.2.1 (hle := hbm_le) (by omega),
        rp hw hmemL hm.2.2.2.2.2.2.2.2.2 (hle := hbm_le) (by omega)⟩
    · have hidx : b * capBackWhp n_max + k < numBucketsWhp n_max * capBackWhp n_max := by
        calc b * capBackWhp n_max + k < b * capBackWhp n_max + capBackWhp n_max :=
              Nat.add_lt_add_left hk _
          _ = (b + 1) * capBackWhp n_max := by ring
          _ ≤ numBucketsWhp n_max * capBackWhp n_max := Nat.mul_le_mul_right _ hb
      exact rp hw hmemL (hbptr b hb k hk) hidx (by omega)
    · obtain ⟨ha_le, halloc_r, hroot_r, hnodes_r⟩ := hslices sIdx hsIdx
      have hb_lt : sIdx / 3 < numBucketsWhp n_max := by omega
      have hrole_lt : sIdx % 3 < 3 := Nat.mod_lt _ (by decide)
      refine ⟨ha_le,
        rp hw hmemL halloc_r
          (show 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max by omega)
          (by omega),
        rp hw hmemL hroot_r
          (show 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max by omega)
          (by omega),
        fun u hu => ?_⟩
      have hu_ns : u < nSliceWhp n_max := hu.trans_le ha_le
      have hidx : sIdx * nSliceWhp n_max + u < totalBTreeNodesWhp n_max := by
        unfold totalBTreeNodesWhp
        calc sIdx * nSliceWhp n_max + u < sIdx * nSliceWhp n_max + nSliceWhp n_max :=
              Nat.add_lt_add_left hu_ns _
          _ = (sIdx + 1) * nSliceWhp n_max := by ring
          _ ≤ (3 * numBucketsWhp n_max) * nSliceWhp n_max := Nat.mul_le_mul_right _ hsIdx
      exact ⟨rp hw hmemL (hnodes_r u hu).1 hidx (by omega),
        rp hw hmemL (hnodes_r u hu).2.1 hidx (by omega),
        rp hw hmemL (hnodes_r u hu).2.2 hidx (by omega)⟩

/-! ## Section 5: Precomputed runtime parameter block `WhpParams` (`68 + 16 + 16 = 100` words) -/

/-- Core 68-word runtime parameter vector for `SuccinctWhp` `Memory.Prog` subroutines. -/
@[expose] def WhpCoreParams : Type := Fin 68 → ℕ

instance : WordEncoding WhpCoreParams := ⟨68, Function.Embedding.refl (Fin 68 → ℕ)⟩

/-- Combined 100-word runtime parameter bundle `(coreParams, (bktHashParams, fpHashParams))`. -/
abbrev WhpParams : Type :=
  WhpCoreParams × BitPackedDoubleTabulation.HashParams × BitPackedDoubleTabulation.HashParams

/-- Construct `WhpCoreParams` for `(c, U, V, w, n_max)`. When `n_max < whpThreshold c`, all
large-regime entries (`10 .. 67`) are `0` so every entry fits in `w` bits for all `w > 0`. -/
@[expose] def mkWhpCoreParams (c U V w n_max : ℕ) : WhpCoreParams := fun i =>
  if n_max < whpThreshold c then
    match i.val with
    | 0 => 1
    | 1 => w
    | 2 => n_max
    | 3 => U
    | 4 => V
    | 5 => keyBits U
    | 6 => valBits V
    | 7 => offSmallPres
    | 8 => offSmallKeys U w n_max
    | 9 => offSmallVals U w n_max
    | _ => 0
  else
    match i.val with
    | 0 => 0
    | 1 => w
    | 2 => n_max
    | 3 => U
    | 4 => V
    | 5 => keyBits U
    | 6 => valBits V
    | 7 => 0
    | 8 => 0
    | 9 => 0
    | 10 => bWhp n_max
    | 11 => numBucketsWhp n_max
    | 12 => numBucketsWhp n_max - 1
    | 13 => quotBitsWhp U n_max
    | 14 => fpBitsWhp n_max
    | 15 => 2 ^ fpBitsWhp n_max
    | 16 => bCharWhp n_max
    | 17 => 2 ^ bCharWhp n_max
    | 18 => 2 ^ bCharWhp n_max - 1
    | 19 => cTabWhp c
    | 20 => sMaxWhp c n_max
    | 21 => 2 * sMaxWhp c n_max
    | 22 => qEpochWhp n_max
    | 23 => deltaWhp n_max
    | 24 => capFrontWhp n_max
    | 25 => capBackWhp n_max
    | 26 => totalLocalCoordsWhp n_max
    | 27 => numBucketsWhp n_max * capFrontWhp n_max
    | 28 => poolSizeWhp n_max
    | 29 => 5 * (slabScale n_max) ^ 12
    | 30 => globalPtrBits n_max
    | 31 => 12 * logLogFactor n_max + 4
    | 32 => trieChildEntriesWhp c n_max
    | 33 => maxTrieNodesWhp c n_max
    | 34 => hMaxBTree
    | 35 => tMinWhp n_max
    | 36 => 2 * tMinWhp n_max
    | 37 => 2 * tMinWhp n_max - 1
    | 38 => keyLaneBitsWhp n_max
    | 39 => 2 ^ keyLaneBitsWhp n_max - 1
    | 40 => swarOnes (keyLaneBitsWhp n_max) (2 * tMinWhp n_max)
    | 41 => valsWordBitsWhp n_max
    | 42 => keysWordBitsWhp n_max
    | 43 => valLaneBitsWhp n_max
    | 44 => 2 ^ valLaneBitsWhp n_max - 1
    | 45 => nodeMetaBitsWhp n_max
    | 46 => nSliceWhp n_max
    | 47 => offHashBkt
    | 48 => offHashFp c w n_max
    | 49 => offQuotWhp c w n_max
    | 50 => offValWhp c U w n_max
    | 51 => offPermAct c U V w n_max
    | 52 => offLocState c U V w n_max
    | 53 => offBktMeta c U V w n_max
    | 54 => offFbStart c U V w n_max
    | 55 => offBackPtr c U V w n_max
    | 56 => offPoolFreeStack c U V w n_max
    | 57 => offPoolOwner c U V w n_max
    | 58 => offBtMeta c U V w n_max
    | 59 => offBtKeys c U V w n_max
    | 60 => offBtVals c U V w n_max
    | 61 => offTrieChild0 c U V w n_max
    | 62 => offTrieChild1 c U V w n_max
    | 63 => offTrieMeta0 c U V w n_max
    | 64 => offTrieMeta1 c U V w n_max
    | 65 => offTrieItems0 c U V w n_max
    | 66 => offTrieItems1 c U V w n_max
    | _ => 0

/-- Construct the full 100-word `WhpParams` bundle for `(c, U, V, w, n_max)`. -/
@[expose] def mkWhpParams (c U V w n_max : ℕ) : WhpParams :=
  if n_max < whpThreshold c then
    (mkWhpCoreParams c U V w n_max, ((fun _ => 0), (fun _ => 0)))
  else
    (mkWhpCoreParams c U V w n_max,
     (BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max),
      BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)))

/-- Bucket-hash runtime parameter block in `WhpParams`. -/
abbrev wpHash1 (wp : WhpParams) : BitPackedDoubleTabulation.HashParams := wp.2.1
/-- Fingerprint-hash runtime parameter block in `WhpParams`. -/
abbrev wpHash2 (wp : WhpParams) : BitPackedDoubleTabulation.HashParams := wp.2.2

/-! ### Named projections on `WhpCoreParams` -/

/-- Small-regime flag (`1` if `n_max < whpThreshold c`, `0` otherwise) in `WhpCoreParams`. -/
@[expose] def wpIsSmall (cp : WhpCoreParams) : ℕ := cp ⟨0, by decide⟩
/-- Word width `w` in `WhpCoreParams`. -/
@[expose] def wpW (cp : WhpCoreParams) : ℕ := cp ⟨1, by decide⟩
/-- Maximum capacity `n_max` in `WhpCoreParams`. -/
@[expose] def wpNMax (cp : WhpCoreParams) : ℕ := cp ⟨2, by decide⟩
/-- Key universe bound `U` in `WhpCoreParams`. -/
@[expose] def wpU (cp : WhpCoreParams) : ℕ := cp ⟨3, by decide⟩
/-- Value universe bound `V` in `WhpCoreParams`. -/
@[expose] def wpV (cp : WhpCoreParams) : ℕ := cp ⟨4, by decide⟩
/-- Small-regime key bit-width `keyBitsWhp U` in `WhpCoreParams`. -/
@[expose] def wpKeyBits (cp : WhpCoreParams) : ℕ := cp ⟨5, by decide⟩
/-- Value bit-width `valBitsWhp V` in `WhpCoreParams`. -/
@[expose] def wpValBits (cp : WhpCoreParams) : ℕ := cp ⟨6, by decide⟩
/-- Small-regime presence bitmap word offset in `WhpCoreParams`. -/
@[expose] def wpOffSmallPres (cp : WhpCoreParams) : ℕ := cp ⟨7, by decide⟩
/-- Small-regime packed key array word offset in `WhpCoreParams`. -/
@[expose] def wpOffSmallKeys (cp : WhpCoreParams) : ℕ := cp ⟨8, by decide⟩
/-- Small-regime packed value array word offset in `WhpCoreParams`. -/
@[expose] def wpOffSmallVals (cp : WhpCoreParams) : ℕ := cp ⟨9, by decide⟩
/-- Bucket index bit-width `bWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpBWhp (cp : WhpCoreParams) : ℕ := cp ⟨10, by decide⟩
/-- Number of buckets `numBucketsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpM (cp : WhpCoreParams) : ℕ := cp ⟨11, by decide⟩
/-- Bucket index bitmask `numBucketsWhp n_max - 1` in `WhpCoreParams`. -/
@[expose] def wpMaskBkt (cp : WhpCoreParams) : ℕ := cp ⟨12, by decide⟩
/-- Feistel quotient bit-width `quotBitsWhp U n_max` in `WhpCoreParams`. -/
@[expose] def wpQuotBits (cp : WhpCoreParams) : ℕ := cp ⟨13, by decide⟩
/-- Bucket fingerprint bit-width `fpBitsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpFpBits (cp : WhpCoreParams) : ℕ := cp ⟨14, by decide⟩
/-- Fingerprint radix `2 ^ fpBitsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpPowFp (cp : WhpCoreParams) : ℕ := cp ⟨15, by decide⟩
/-- Double-tabulation character bit-width `bCharWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpBChar (cp : WhpCoreParams) : ℕ := cp ⟨16, by decide⟩
/-- Character radix `2 ^ bCharWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpPowBChar (cp : WhpCoreParams) : ℕ := cp ⟨17, by decide⟩
/-- Character bitmask `2 ^ bCharWhp n_max - 1` in `WhpCoreParams`. -/
@[expose] def wpMaskBChar (cp : WhpCoreParams) : ℕ := cp ⟨18, by decide⟩
/-- Character chunk count `cTabWhp c` in `WhpCoreParams`. -/
@[expose] def wpCTab (cp : WhpCoreParams) : ℕ := cp ⟨19, by decide⟩
/-- Salt domain bound `sMaxWhp c n_max` in `WhpCoreParams`. -/
@[expose] def wpSMax (cp : WhpCoreParams) : ℕ := cp ⟨20, by decide⟩
/-- Buffer-trie item capacity `2 * sMaxWhp c n_max` in `WhpCoreParams`. -/
@[expose] def wpBufItemCap (cp : WhpCoreParams) : ℕ := cp ⟨21, by decide⟩
/-- Epoch operation length `qEpochWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpQEpoch (cp : WhpCoreParams) : ℕ := cp ⟨22, by decide⟩
/-- Front-yard slack parameter `deltaWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpDelta (cp : WhpCoreParams) : ℕ := cp ⟨23, by decide⟩
/-- Per-bucket front-yard capacity `capFrontWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpCapFront (cp : WhpCoreParams) : ℕ := cp ⟨24, by decide⟩
/-- Per-bucket backyard capacity `capBackWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpCapBack (cp : WhpCoreParams) : ℕ := cp ⟨25, by decide⟩
/-- Total per-bucket local coordinate count `totalLocalCoordsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpTotalLoc (cp : WhpCoreParams) : ℕ := cp ⟨26, by decide⟩
/-- Total front-yard slot count `numBucketsWhp n_max * capFrontWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpFrontTotal (cp : WhpCoreParams) : ℕ := cp ⟨27, by decide⟩
/-- Backyard pool size `poolSizeWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpPoolSize (cp : WhpCoreParams) : ℕ := cp ⟨28, by decide⟩
/-- Overmars local rebuild threshold `5 * (slabScale n_max) ^ 12` in `WhpCoreParams`. -/
@[expose] def wpOvermarsThresh (cp : WhpCoreParams) : ℕ := cp ⟨29, by decide⟩
/-- Global slot pointer bit-width `globalPtrBits n_max` in `WhpCoreParams`. -/
@[expose] def wpGlobalPtrBits (cp : WhpCoreParams) : ℕ := cp ⟨30, by decide⟩
/-- In-place permutation activity bit-width `permActBits n_max` in `WhpCoreParams`. -/
@[expose] def wpPermActBits (cp : WhpCoreParams) : ℕ := cp ⟨31, by decide⟩
/-- Per-trie child-pointer entry count in `WhpCoreParams`. -/
@[expose] def wpTrieChildEntries (cp : WhpCoreParams) : ℕ := cp ⟨32, by decide⟩
/-- Per-trie maximum node count `maxTrieNodesWhp c n_max` in `WhpCoreParams`. -/
@[expose] def wpMaxTrieNodes (cp : WhpCoreParams) : ℕ := cp ⟨33, by decide⟩
/-- Maximum SWAR B+-tree height `hMaxBTreeWhp` in `WhpCoreParams`. -/
@[expose] def wpHMaxBTree (cp : WhpCoreParams) : ℕ := cp ⟨34, by decide⟩
/-- Minimum SWAR B+-tree branching parameter `tMinWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpTMin (cp : WhpCoreParams) : ℕ := cp ⟨35, by decide⟩
/-- SWAR B+-tree node lane capacity `2 * tMinWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpCapLanes (cp : WhpCoreParams) : ℕ := cp ⟨36, by decide⟩
/-- Full-node key count `2 * tMinWhp n_max - 1` in `WhpCoreParams`. -/
@[expose] def wpFullKeys (cp : WhpCoreParams) : ℕ := cp ⟨37, by decide⟩
/-- SWAR key lane bit-width `keyLaneBitsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpWKey (cp : WhpCoreParams) : ℕ := cp ⟨38, by decide⟩
/-- SWAR key lane bitmask `2 ^ keyLaneBitsWhp n_max - 1` in `WhpCoreParams`. -/
@[expose] def wpMaskWKey (cp : WhpCoreParams) : ℕ := cp ⟨39, by decide⟩
/-- Packed SWAR all-ones pattern over `2 * tMinWhp n_max` key lanes in `WhpCoreParams`. -/
@[expose] def wpSwarOnesCap (cp : WhpCoreParams) : ℕ := cp ⟨40, by decide⟩
/-- Packed B+-tree value-word bit-width `valsWordBitsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpValsWordBits (cp : WhpCoreParams) : ℕ := cp ⟨41, by decide⟩
/-- Packed B+-tree key-word bit-width `keysWordBitsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpKeysWordBits (cp : WhpCoreParams) : ℕ := cp ⟨42, by decide⟩
/-- SWAR value lane bit-width `valLaneBitsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpWVal (cp : WhpCoreParams) : ℕ := cp ⟨43, by decide⟩
/-- SWAR value lane bitmask `2 ^ valLaneBitsWhp n_max - 1` in `WhpCoreParams`. -/
@[expose] def wpMaskWVal (cp : WhpCoreParams) : ℕ := cp ⟨44, by decide⟩
/-- B+-tree node metadata bit-width `nodeMetaBitsWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpNodeMetaBits (cp : WhpCoreParams) : ℕ := cp ⟨45, by decide⟩
/-- Per-slice B+-tree node budget `nodesPerSliceWhp n_max` in `WhpCoreParams`. -/
@[expose] def wpNSlice (cp : WhpCoreParams) : ℕ := cp ⟨46, by decide⟩
/-- Word offset `offHashBkt` of the bucket hash seed in `WhpCoreParams`. -/
@[expose] def wpOffHashBkt (cp : WhpCoreParams) : ℕ := cp ⟨47, by decide⟩
/-- Word offset `offHashFp` of the fingerprint hash seed in `WhpCoreParams`. -/
@[expose] def wpOffHashFp (cp : WhpCoreParams) : ℕ := cp ⟨48, by decide⟩
/-- Word offset `offQuotWhp` of the packed quotient array in `WhpCoreParams`. -/
@[expose] def wpOffQuot (cp : WhpCoreParams) : ℕ := cp ⟨49, by decide⟩
/-- Word offset `offValWhp` of the packed value array in `WhpCoreParams`. -/
@[expose] def wpOffVal (cp : WhpCoreParams) : ℕ := cp ⟨50, by decide⟩
/-- Word offset `offPermAct` of the permutation activity array in `WhpCoreParams`. -/
@[expose] def wpOffPermAct (cp : WhpCoreParams) : ℕ := cp ⟨51, by decide⟩
/-- Word offset `offLocState` of the local slot-state array in `WhpCoreParams`. -/
@[expose] def wpOffLocState (cp : WhpCoreParams) : ℕ := cp ⟨52, by decide⟩
/-- Word offset `offBktMeta` of the bucket metadata array in `WhpCoreParams`. -/
@[expose] def wpOffBktMeta (cp : WhpCoreParams) : ℕ := cp ⟨53, by decide⟩
/-- Word offset `offFbStart` of the CSR bucket-prefix array in `WhpCoreParams`. -/
@[expose] def wpOffFbStart (cp : WhpCoreParams) : ℕ := cp ⟨54, by decide⟩
/-- Word offset `offBackPtr` of the backyard pointer array in `WhpCoreParams`. -/
@[expose] def wpOffBackPtr (cp : WhpCoreParams) : ℕ := cp ⟨55, by decide⟩
/-- Word offset `offPoolFreeStack` of the backyard free stack in `WhpCoreParams`. -/
@[expose] def wpOffPoolFreeStack (cp : WhpCoreParams) : ℕ := cp ⟨56, by decide⟩
/-- Word offset `offPoolOwner` of the backyard pool-owner array in `WhpCoreParams`. -/
@[expose] def wpOffPoolOwner (cp : WhpCoreParams) : ℕ := cp ⟨57, by decide⟩
/-- Word offset `offBtMeta` of the B+-tree node metadata array in `WhpCoreParams`. -/
@[expose] def wpOffBtMeta (cp : WhpCoreParams) : ℕ := cp ⟨58, by decide⟩
/-- Word offset `offBtKeys` of the B+-tree packed key-lane array in `WhpCoreParams`. -/
@[expose] def wpOffBtKeys (cp : WhpCoreParams) : ℕ := cp ⟨59, by decide⟩
/-- Word offset `offBtVals` of the B+-tree packed value-lane array in `WhpCoreParams`. -/
@[expose] def wpOffBtVals (cp : WhpCoreParams) : ℕ := cp ⟨60, by decide⟩
/-- Word offset `offTrieChild0` of epoch-`0` `BufTrie` child pointers in `WhpCoreParams`. -/
@[expose] def wpOffTrieChild0 (cp : WhpCoreParams) : ℕ := cp ⟨61, by decide⟩
/-- Word offset `offTrieChild1` of epoch-`1` `BufTrie` child pointers in `WhpCoreParams`. -/
@[expose] def wpOffTrieChild1 (cp : WhpCoreParams) : ℕ := cp ⟨62, by decide⟩
/-- Word offset `offTrieMeta0` of epoch-`0` `BufTrie` node metadata in `WhpCoreParams`. -/
@[expose] def wpOffTrieMeta0 (cp : WhpCoreParams) : ℕ := cp ⟨63, by decide⟩
/-- Word offset `offTrieMeta1` of epoch-`1` `BufTrie` node metadata in `WhpCoreParams`. -/
@[expose] def wpOffTrieMeta1 (cp : WhpCoreParams) : ℕ := cp ⟨64, by decide⟩
/-- Word offset `offTrieItems0` of epoch-`0` `BufTrie` item records in `WhpCoreParams`. -/
@[expose] def wpOffTrieItems0 (cp : WhpCoreParams) : ℕ := cp ⟨65, by decide⟩
/-- Word offset `offTrieItems1` of epoch-`1` `BufTrie` item records in `WhpCoreParams`. -/
@[expose] def wpOffTrieItems1 (cp : WhpCoreParams) : ℕ := cp ⟨66, by decide⟩

/-- Both `HashParams` vectors satisfy `BitPackedDoubleTabulation.HashEnv` in the large regime. -/
theorem hashEnvs_of_large {base c U V w n_max : ℕ}
    (hw : 0 < w) (hth : whpThreshold c ≤ n_max) (hnU : n_max ≤ U)
    (hU : Fits w U) (hfit : Fits w (base + whpSpace c U V w n_max)) :
    BitPackedDoubleTabulation.HashEnv w
      (BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max))
      (base + offHashBkt) ∧
    BitPackedDoubleTabulation.HashEnv w
      (BitPackedDoubleTabulation.mkHashParams w (w0Whp U) (rRedWhp c n_max)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))
      (base + offHashFp c w n_max) := by
  rw [whpSpace, ite_eq_right (Nat.not_lt.mpr hth)] at hfit
  have hlog_w := log_n_max_lt_w hth hnU hU
  have hlog_ge := log_ge_mul_ell hth
  have hell := one_le_logLogFactor n_max
  have hbc_lt : bCharWhp n_max < w := (Nat.div_le_self _ 4).trans_lt hlog_w
  have hb_le : bWhp n_max ≤ w := ((Nat.sub_le _ _).trans_lt hlog_w).le
  have hfp_le : fpBitsWhp n_max ≤ w :=
    ((by dsimp only [fpBitsWhp]; omega : fpBitsWhp n_max ≤ Nat.log 2 n_max).trans_lt hlog_w).le
  obtain ⟨htb1, _, _, _, _, _⟩ := sublinear_table_bits_le hth
  have hbc_pos : 0 < bCharWhp n_max := by have := bCharWhp_ge_mul_ell hth; omega
  have htop_le :
      BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) ≤ n_max :=
    (Nat.le_mul_of_pos_right _ hbc_pos).trans htb1
  have hn_lt_w : n_max < 2 ^ w := hnU.trans_lt hU
  have htop_lt : BitPackedDoubleTabulation.topEntries (cTabWhp c) (dTabWhp c) (bCharWhp n_max) <
      2 ^ w := htop_le.trans_lt hn_lt_w
  have hbot_lt : BitPackedDoubleTabulation.botEntries (dTabWhp c) (bCharWhp n_max) < 2 ^ w :=
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))).trans_lt htop_lt
  have hc1_lt : cTabWhp c + 1 < 2 ^ w := by
    refine (?_ : _ ≤ BitPackedDoubleTabulation.topEntries _ _ _).trans_lt htop_lt
    simpa only [BitPackedDoubleTabulation.topEntries, mul_assoc] using
      Nat.le_mul_of_pos_right (cTabWhp c + 1) (Nat.mul_pos (dTabWhp_pos c) (Nat.two_pow_pos _))
  have hd_lt : dTabWhp c < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans_lt hbot_lt
  have hfit1 : Fits w ((base + offHashBkt) + bktHashWords c w n_max) :=
    hfit.of_le (by dsimp only [largeSpaceWhp, offHashBkt, bktHashWords]; omega)
  have hfit2 : Fits w ((base + offHashFp c w n_max) + fpHashWords c w n_max) :=
    hfit.of_le (by
      dsimp only [largeSpaceWhp, offHashFp, offHashBkt, bktHashWords, fpHashWords]; omega)
  exact ⟨⟨w0Whp U, rRedWhp c n_max, cTabWhp c, dTabWhp c, bCharWhp n_max, bWhp n_max,
      hw, w0Whp_pos U, w0Whp_le_w hw hU, hbc_lt, hb_le, htop_lt, hbot_lt, hc1_lt, hd_lt,
      hfit1, rfl⟩,
    ⟨w0Whp U, rRedWhp c n_max, cTabWhp c, dTabWhp c, bCharWhp n_max, fpBitsWhp n_max,
      hw, w0Whp_pos U, w0Whp_le_w hw hU, hbc_lt, hfp_le, htop_lt, hbot_lt, hc1_lt, hd_lt,
      hfit2, rfl⟩⟩

/-- Every word in the 100-word `WordEncoding.encode (mkWhpParams c U V w n_max)` vector fits in `w`
bits under standard dictionary parameter admissibility. -/
private theorem swarOnes_lt_two_pow (W n : ℕ) : swarOnes W n < 2 ^ (n * W) :=
  (Nat.div_le_self _ _).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one)

theorem ltMask_mul_swarOnes_lt_two_pow {fpBits capLanes m q keysWord : ℕ} (hm : m < capLanes) :
    ltMask fpBits m q keysWord * swarOnes (fpBits + 2) capLanes <
      2 ^ ((2 * capLanes - 1) * (fpBits + 2)) := by
  set W := fpBits + 2
  have hlt_m : ltMask fpBits m q keysWord ≤ swarOnes W m := Nat.and_le_right
  have hm_lt : swarOnes W m < 2 ^ ((capLanes - 1) * W) :=
    (swarOnes_lt_two_pow W m).trans_le (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right W (by omega)))
  have hc_lt : swarOnes W capLanes < 2 ^ (capLanes * W) := swarOnes_lt_two_pow W capLanes
  calc ltMask fpBits m q keysWord * swarOnes W capLanes
      < 2 ^ ((capLanes - 1) * W) * 2 ^ (capLanes * W) :=
        Nat.mul_lt_mul'' (hlt_m.trans_lt hm_lt) hc_lt
    _ = 2 ^ ((2 * capLanes - 1) * W) := by
        rw [← Nat.pow_add, ← Nat.add_mul]
        congr 2
        omega

theorem fits_mkWhpParams {base c U V w n_max : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max)) :
    (∀ i : Fin 68, Fits w (mkWhpCoreParams c U V w n_max i)) ∧
    (∀ j : Fin 16, Fits w (wpHash1 (mkWhpParams c U V w n_max) j) ∧
      Fits w (wpHash2 (mkWhpParams c U V w n_max) j)) := by
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  have hn_lt : n_max < 2 ^ w := hnU.trans_lt hU
  have h0_fit : Fits w 0 := Nat.two_pow_pos w
  have h1_fit : Fits w 1 := Nat.one_lt_two_pow hw.ne'
  by_cases hsm : n_max < whpThreshold c
  · rw [whpSpace, ite_eq_left hsm] at hfit
    have hend := smallOffsets_eq U V w n_max
    dsimp only [offSmallVals, offSmallKeys, offSmallPres] at hend
    refine ⟨fun i => ?_, fun j => ?_⟩
    · dsimp only [mkWhpCoreParams]
      rw [ite_eq_left hsm]
      split
      · exact h1_fit
      · exact hw_lt
      · exact hn_lt
      · exact hU
      · exact hV
      · exact (keyBits_le_w hU).trans_lt hw_lt
      · exact (valBits_le_w hV).trans_lt hw_lt
      all_goals
        try dsimp only [offSmallVals, offSmallKeys, offSmallPres]
        exact hfit.of_le (by omega)
    · rw [mkWhpParams, ite_eq_left hsm]
      exact ⟨h0_fit, h0_fit⟩
  · have hth : whpThreshold c ≤ n_max := Nat.le_of_not_lt hsm
    obtain ⟨henv1, henv2⟩ := hashEnvs_of_large hw hth hnU hU hfit
    rw [whpSpace, ite_eq_right hsm] at hfit
    have hend := largeOffsets_eq c U V w n_max
    have hlog_w := log_n_max_lt_w hth hnU hU
    have hlog_ge := log_ge_mul_ell hth
    have hell := one_le_logLogFactor n_max
    obtain ⟨hM_ge, hns_lt, htl_lt, h8L_lt, hsMax_lt, hmt_lt, hq_lt, hpbc_lt⟩ :=
      large_bounds_lt_n_max hth
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hkw_log := keysWordBitsWhp_lt_log hth
    have hvw_log := valsWordBitsWhp_lt_log hth
    have hM_le_n : numBucketsWhp n_max ≤ n_max := by
      have hL12 : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
      exact (Nat.le_mul_of_pos_right _ hL12).trans (numBucketsWhp_mul_scale_pow12_le hth)
    have hch := largeOffsetChain c U V w n_max
    have hkl_pos : 0 < keyLaneBitsWhp n_max := Nat.succ_pos _
    refine ⟨fun i => ?_, fun j => ?_⟩
    · dsimp only [mkWhpCoreParams]
      rw [ite_eq_right hsm]
      split
      · exact h0_fit
      · exact hw_lt
      · exact hn_lt
      · exact hU
      · exact hV
      · exact (keyBits_le_w hU).trans_lt hw_lt
      · exact (valBits_le_w hV).trans_lt hw_lt
      · exact h0_fit
      · exact h0_fit
      · exact h0_fit
      · exact ((Nat.sub_le _ _).trans_lt hlog_w).trans hw_lt
      · exact hM_le_n.trans_lt hn_lt
      · exact (Nat.sub_le _ _).trans_lt (hM_le_n.trans_lt hn_lt)
      · exact ((Nat.sub_le _ _).trans (keyBits_le_w hU)).trans_lt hw_lt
      · exact (by unfold fpBitsWhp; omega : fpBitsWhp n_max < w).trans hw_lt
      · exact Nat.pow_lt_pow_right (by decide) (by unfold fpBitsWhp; omega : fpBitsWhp n_max < w)
      · exact ((Nat.div_le_self _ 4).trans_lt hlog_w).trans hw_lt
      · exact hpbc_lt.trans hn_lt
      · exact (Nat.sub_le _ _).trans_lt (hpbc_lt.trans hn_lt)
      · have hq_pos : 1 ≤ qEpochWhp n_max := Nat.one_le_pow 18 _ (slabScale_pos n_max)
        have : cTabWhp c < maxTrieNodesWhp c n_max := by
          calc cTabWhp c ≤ (cTabWhp c + 1) * 1 := by omega
            _ ≤ (cTabWhp c + 1) * qEpochWhp n_max := Nat.mul_le_mul_left _ hq_pos
            _ < maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
        exact (this.trans hmt_lt).trans hn_lt
      · exact hsMax_lt.trans hn_lt
      · exact (hrc_lt.trans hq_lt).trans hn_lt
      · exact hq_lt.trans hn_lt
      · exact (Nat.div_le_self _ _).trans_lt hn_lt
      · exact ((Nat.sub_le _ _).trans (Nat.div_le_self _ _)).trans_lt hn_lt
      · exact ((Nat.le_add_left _ _).trans_lt htl_lt).trans hn_lt
      · exact htl_lt.trans hn_lt
      · exact ((Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)).trans_lt hn_lt
      · exact (Nat.sub_le _ _).trans_lt hn_lt
      · exact (Nat.mul_le_mul_right _ (by decide : 5 ≤ 8)).trans_lt (h8L_lt.trans hn_lt)
      · exact (globalPtrBits_le_w hnU hU).trans_lt hw_lt
      · exact (by omega : 12 * logLogFactor n_max + 4 < w).trans hw_lt
      · exact htc_n.trans_lt hn_lt
      · exact hmt_lt.trans hn_lt
      · rw [hMaxBTree_eq]
        exact (by omega : 42 < 1024).trans (hM_ge.trans_lt (hM_le_n.trans_lt hn_lt))
      · have ht : tMinWhp n_max ≤ Nat.log 2 n_max := by
          unfold tMinWhp
          exact max_le (by omega) (Nat.div_le_self _ _)
        exact (ht.trans_lt hlog_w).trans hw_lt
      · exact ((Nat.le_mul_of_pos_right _ hkl_pos).trans_lt
          (by omega : keysWordBitsWhp n_max < w)).trans hw_lt
      · exact (((Nat.sub_le _ _).trans (Nat.le_mul_of_pos_right _ hkl_pos)).trans_lt
          (by omega : keysWordBitsWhp n_max < w)).trans hw_lt
      · exact (by omega : keyLaneBitsWhp n_max < w).trans hw_lt
      · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans
          (Nat.pow_lt_pow_right (by decide) (by omega : keyLaneBitsWhp n_max < w))
      · exact (swarOnes_lt_two_pow (keyLaneBitsWhp n_max) (2 * tMinWhp n_max)).trans
          (Nat.pow_lt_pow_right (by decide) (by
            have : 2 * tMinWhp n_max * keyLaneBitsWhp n_max = keysWordBitsWhp n_max := rfl
            omega))
      · exact (by omega : valsWordBitsWhp n_max < w).trans hw_lt
      · exact (by omega : keysWordBitsWhp n_max < w).trans hw_lt
      · exact (by omega : valLaneBitsWhp n_max < w).trans hw_lt
      · exact (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans
          (Nat.pow_lt_pow_right (by decide) (by omega : valLaneBitsWhp n_max < w))
      · exact (by unfold nodeMetaBitsWhp; omega : nodeMetaBitsWhp n_max < w).trans hw_lt
      · exact hns_lt.trans hn_lt
      all_goals exact hfit.of_le (by omega)
    · rw [mkWhpParams, ite_eq_right hsm]
      exact ⟨BitPackedDoubleTabulation.fits_mkHashParams henv1 j,
        BitPackedDoubleTabulation.fits_mkHashParams henv2 j⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctValidHistory
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpLayout
import CslibFrontier.Tactic.Realize

/-!
# `Memory.Prog` Envelopes, SWAR Word-Lane Subroutines, and B+-Tree Slice Primitives

This module establishes the parameter-free runtime envelopes (`WhpLargeEnv`, `WhpLargeEnvGen`,
`WhpSmallEnv`, `WhpSmallEnvGen`), `Succinct.ValidProg` primitive admissibility lemmas, packed-array
safety projections, SWAR word-lane `Memory.Prog` subroutines (`laneGetGenProg`,
`wordTakeLowGenProg`, `wordDropLowGenProg`, `wordInsertAtGenProg`, `wordDeleteAtGenProg`,
`wordUpdateAtGenProg`, `swarRankGenProg`, `splitFullNodeGenProg`), and packed B+-tree slice/node
accessors (`readSliceHeaderGenProg`, `writeSliceAllocGenProg`, `resetBTreeSliceGenProg`,
`readBTreeNodeGenProg`, `writeBTreeNodeGenProg`), all certified over `Basis.exact` with zero local
work via `realize`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.WhpLargeEnv`,
  `WhpLargeEnvGen`, `WhpSmallEnv`, `WhpSmallEnvGen`: runtime parameter envelopes.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.swarRankGenProg`,
  `splitFullNodeGenProg`, `wordInsertAtGenProg`, `wordDeleteAtGenProg`, `wordUpdateAtGenProg`:
  certified `O(1)` SWAR `Memory.Prog` helpers.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readSliceHeaderGenProg`,
  `writeSliceAllocGenProg`, `resetBTreeSliceGenProg`, `readBTreeNodeGenProg`,
  `writeBTreeNodeGenProg`: packed B+-tree slice header and node `Memory.Prog` accessors.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.totalBTreeNodesWhp_le_n_max`:
  `totalBTreeNodesWhp n_max ≤ n_max` whenever `whpThreshold c ≤ n_max`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_swarRankGen`,
  `realizes_splitFullNodeGen`, `realizes_readBTreeNodeGen`, `realizes_writeBTreeNodeGen`,
  `realizes_resetBTreeSliceGen`: parameter-free `Realizes .exact` certificates.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: `Succinct.ValidProg` Primitive Lemmas and Runtime Envelopes -/

theorem _root_.Cslib.DataStructure.Dictionary.WordRAM.Succinct.ValidProg.validHistory
    {α : Type} {w F : ℕ} {s : Memory.State} {p : Memory.Prog α}
    (hp : ValidProg w F s p) (hwf : Memory.WellFormed w s) (hf : F ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) :=
  hp ⟨hwf, hf⟩

theorem validProg_read {w F addr : ℕ} {s : Memory.State} (ha : addr < F) :
    ValidProg w F s (Memory.read addr) :=
  fun ⟨_, hf⟩ => ⟨ha.trans_le hf, trivial⟩

theorem validProg_write {w F addr val : ℕ} {s : Memory.State}
    (ha : addr < F) (hv : Fits w val) :
    ValidProg w F s (Memory.write addr val) :=
  fun ⟨_, hf⟩ => ⟨⟨ha.trans_le hf, hv⟩, trivial⟩

theorem validProg_readPacked {w F base offset N k idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < N) (ha : base + offset + packedWords N k w ≤ F) :
    ValidProg w F s (readPackedGenProg (((base, offset), (k, w)), idx)) :=
  fun ⟨_, hf⟩ => validHistory_readPackedProg hw hidx (ha.trans hf)

theorem validProg_writePacked {w F base offset N k idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hkw : k ≤ w) (hidx : idx < N)
    (ha : base + offset + packedWords N k w ≤ F) :
    ValidProg w F s (writePackedGenProg ((((base, offset), (k, w)), idx), val)) :=
  fun ⟨hwf, hf⟩ => validHistory_writePackedProg hw hkw hidx hwf (ha.trans hf)

theorem clientResult_pure_whp {α : Type} {w : ℕ} (x : α) (s : Memory.State) :
    (Memory.spec w).clientResult s (pure x) = x := by
  rw [clientResult_width]; rfl

theorem clientState_pure_whp {α : Type} {w : ℕ} (x : α) (s : Memory.State) :
    (Memory.spec w).clientState s (pure x) = s := by
  rw [clientState_width]; rfl

theorem clientResult_memRead {w : ℕ} (addr : ℕ) (s : Memory.State) :
    (Memory.spec w).clientResult s (Memory.read addr) = s.mem addr := by
  rw [clientResult_width]; rfl

theorem clientState_memRead {w : ℕ} (addr : ℕ) (s : Memory.State) :
    (Memory.spec w).clientState s (Memory.read addr) = s := by
  rw [clientState_width]; rfl

theorem clientState_memWrite {w : ℕ} (addr val : ℕ) (s : Memory.State) :
    (Memory.spec w).clientState s (Memory.write addr val) =
      { mem := Function.update s.mem addr val, frontier := s.frontier } := by
  rw [clientState_width]; rfl

theorem memoryCost_memRead_and_write :
    (∀ addr s, memoryCost (Memory.read addr) s = 1) ∧
    (∀ addr val s, memoryCost (Memory.write addr val) s = 1) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem clientResult_readPackedGen {w' : ℕ} (base offset k w idx : ℕ) (s : Memory.State) :
    (Memory.spec w').clientResult s (readPackedGenProg (((base, offset), (k, w)), idx)) =
      readPacked (base + offset) k w s.mem idx := by
  rw [clientResult_width]
  exact clientResult_readPackedProg base offset k w idx s

theorem clientState_readPackedGen {w' : ℕ} (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec w').clientState s (readPackedGenProg d) = s := by
  rcases d with ⟨⟨⟨base, offset⟩, ⟨k, w⟩⟩, idx⟩
  rw [clientState_width]; rfl

theorem memoryCost_readPackedGen (d : ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (readPackedGenProg d) s = 2 := by
  rcases d with ⟨⟨⟨base, offset⟩, ⟨k, w⟩⟩, idx⟩; rfl

theorem clientState_writePackedGen {w' : ℕ} (base offset k w idx val : ℕ) (s : Memory.State) :
    (Memory.spec w').clientState s (writePackedGenProg ((((base, offset), (k, w)), idx), val)) =
      { mem := writePacked (base + offset) k w s.mem idx val, frontier := s.frontier } := by
  rw [clientState_width]; rfl

theorem memoryCost_writePackedGen (d : (((ℕ × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writePackedGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨⟨base, offset⟩, ⟨k, w⟩⟩, idx⟩, val⟩; rfl

theorem mul_add_lt_mul_bound {A B a b : ℕ} (ha : a < A) (hb : b < B) :
    a * B + b < A * B := by
  calc a * B + b < a * B + B := Nat.add_lt_add_left hb _
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ ha

theorem val_lt_two_pow_valBits {V v : ℕ} (hv : v < V) : v < 2 ^ valBits V :=
  hv.trans_le (Nat.le_pow_clog Nat.one_lt_two V)

theorem to_true_exists {w : ℕ} {P : ℕ → Prop} (h : ∃ N, w = w ∧ P N) : ∃ N, True ∧ P N :=
  let ⟨N, _, hP⟩ := h; ⟨N, trivial, hP⟩

/-- Entry admissibility envelope in the small regime (`n_max < whpThreshold c`). -/
@[expose] def WhpSmallEnv (c U V w₀ n_max w base : ℕ) : Prop :=
  0 < c ∧ 0 < w₀ ∧ w = w₀ ∧ n_max < whpThreshold c ∧ n_max ≤ U ∧
  Fits w₀ U ∧ Fits w₀ V ∧ Fits w₀ (base + whpSpace c U V w₀ n_max)

/-- Parameter-free small-regime envelope for `cp : WhpCoreParams`. -/
@[expose] def WhpSmallEnvGen (w : ℕ) (cp : WhpCoreParams) (base : ℕ) : Prop :=
  ∃ c U V w₀ n_max, WhpSmallEnv c U V w₀ n_max w base ∧ cp = mkWhpCoreParams c U V w₀ n_max

/-- Entry admissibility envelope in the large regime (`whpThreshold c ≤ n_max`). -/
@[expose] def WhpLargeEnv (c U V w₀ n_max w base : ℕ) : Prop :=
  0 < c ∧ 0 < w₀ ∧ w = w₀ ∧ whpThreshold c ≤ n_max ∧ n_max ≤ U ∧
  Fits w₀ U ∧ Fits w₀ V ∧ Fits w₀ (base + whpSpace c U V w₀ n_max)

/-- Parameter-free large-regime envelope for `cp : WhpCoreParams`. -/
@[expose] def WhpLargeEnvGen (w : ℕ) (cp : WhpCoreParams) (base : ℕ) : Prop :=
  ∃ c U V w₀ n_max, WhpLargeEnv c U V w₀ n_max w base ∧ cp = mkWhpCoreParams c U V w₀ n_max

section ParamSimp

variable {c U V w n_max : ℕ}

private theorem wp_small_isSmall (h : n_max < whpThreshold c) :
    wpIsSmall (mkWhpCoreParams c U V w n_max) = 1 := by simp [wpIsSmall, mkWhpCoreParams, h]
theorem wp_small_w (h : n_max < whpThreshold c) :
    wpW (mkWhpCoreParams c U V w n_max) = w := by simp [wpW, mkWhpCoreParams, h]
theorem wp_small_nMax (h : n_max < whpThreshold c) :
    wpNMax (mkWhpCoreParams c U V w n_max) = n_max := by simp [wpNMax, mkWhpCoreParams, h]
private theorem wp_small_U (h : n_max < whpThreshold c) :
    wpU (mkWhpCoreParams c U V w n_max) = U := by simp [wpU, mkWhpCoreParams, h]
private theorem wp_small_V (h : n_max < whpThreshold c) :
    wpV (mkWhpCoreParams c U V w n_max) = V := by simp [wpV, mkWhpCoreParams, h]
theorem wp_small_keyBits (h : n_max < whpThreshold c) :
    wpKeyBits (mkWhpCoreParams c U V w n_max) = keyBits U := by
  simp [wpKeyBits, mkWhpCoreParams, h]
theorem wp_small_valBits (h : n_max < whpThreshold c) :
    wpValBits (mkWhpCoreParams c U V w n_max) = valBits V := by
  simp [wpValBits, mkWhpCoreParams, h]
theorem wp_small_offPres (h : n_max < whpThreshold c) :
    wpOffSmallPres (mkWhpCoreParams c U V w n_max) = offSmallPres := by
  simp [wpOffSmallPres, mkWhpCoreParams, h]
theorem wp_small_offKeys (h : n_max < whpThreshold c) :
    wpOffSmallKeys (mkWhpCoreParams c U V w n_max) = offSmallKeys U w n_max := by
  simp [wpOffSmallKeys, mkWhpCoreParams, h]
theorem wp_small_offVals (h : n_max < whpThreshold c) :
    wpOffSmallVals (mkWhpCoreParams c U V w n_max) = offSmallVals U w n_max := by
  simp [wpOffSmallVals, mkWhpCoreParams, h]

private theorem wp_large_isSmall (h : whpThreshold c ≤ n_max) :
    wpIsSmall (mkWhpCoreParams c U V w n_max) = 0 := by
  simp [wpIsSmall, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_w (h : whpThreshold c ≤ n_max) :
    wpW (mkWhpCoreParams c U V w n_max) = w := by simp [wpW, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_nMax (h : whpThreshold c ≤ n_max) :
    wpNMax (mkWhpCoreParams c U V w n_max) = n_max := by
  simp [wpNMax, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_U (h : whpThreshold c ≤ n_max) :
    wpU (mkWhpCoreParams c U V w n_max) = U := by simp [wpU, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_V (h : whpThreshold c ≤ n_max) :
    wpV (mkWhpCoreParams c U V w n_max) = V := by simp [wpV, mkWhpCoreParams, Nat.not_lt.mpr h]
private theorem wp_large_keyBits (h : whpThreshold c ≤ n_max) :
    wpKeyBits (mkWhpCoreParams c U V w n_max) = keyBits U := by
  simp [wpKeyBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_valBits (h : whpThreshold c ≤ n_max) :
    wpValBits (mkWhpCoreParams c U V w n_max) = valBits V := by
  simp [wpValBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_bWhp (h : whpThreshold c ≤ n_max) :
    wpBWhp (mkWhpCoreParams c U V w n_max) = bWhp n_max := by
  simp [wpBWhp, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_M (h : whpThreshold c ≤ n_max) :
    wpM (mkWhpCoreParams c U V w n_max) = numBucketsWhp n_max := by
  simp [wpM, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_maskBkt (h : whpThreshold c ≤ n_max) :
    wpMaskBkt (mkWhpCoreParams c U V w n_max) = numBucketsWhp n_max - 1 := by
  simp [wpMaskBkt, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_quotBits (h : whpThreshold c ≤ n_max) :
    wpQuotBits (mkWhpCoreParams c U V w n_max) = quotBitsWhp U n_max := by
  simp [wpQuotBits, mkWhpCoreParams, Nat.not_lt.mpr h]
private theorem wp_large_fpBits (h : whpThreshold c ≤ n_max) :
    wpFpBits (mkWhpCoreParams c U V w n_max) = fpBitsWhp n_max := by
  simp [wpFpBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_powFp (h : whpThreshold c ≤ n_max) :
    wpPowFp (mkWhpCoreParams c U V w n_max) = 2 ^ fpBitsWhp n_max := by
  simp [wpPowFp, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_bChar (h : whpThreshold c ≤ n_max) :
    wpBChar (mkWhpCoreParams c U V w n_max) = bCharWhp n_max := by
  simp [wpBChar, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_powBChar (h : whpThreshold c ≤ n_max) :
    wpPowBChar (mkWhpCoreParams c U V w n_max) = 2 ^ bCharWhp n_max := by
  simp [wpPowBChar, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_maskBChar (h : whpThreshold c ≤ n_max) :
    wpMaskBChar (mkWhpCoreParams c U V w n_max) = 2 ^ bCharWhp n_max - 1 := by
  simp [wpMaskBChar, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_cTab (h : whpThreshold c ≤ n_max) :
    wpCTab (mkWhpCoreParams c U V w n_max) = cTabWhp c := by
  simp [wpCTab, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_sMax (h : whpThreshold c ≤ n_max) :
    wpSMax (mkWhpCoreParams c U V w n_max) = sMaxWhp c n_max := by
  simp [wpSMax, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_bufItemCap (h : whpThreshold c ≤ n_max) :
    wpBufItemCap (mkWhpCoreParams c U V w n_max) = 2 * sMaxWhp c n_max := by
  simp [wpBufItemCap, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_qEpoch (h : whpThreshold c ≤ n_max) :
    wpQEpoch (mkWhpCoreParams c U V w n_max) = qEpochWhp n_max := by
  simp [wpQEpoch, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_delta (h : whpThreshold c ≤ n_max) :
    wpDelta (mkWhpCoreParams c U V w n_max) = deltaWhp n_max := by
  simp [wpDelta, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_capFront (h : whpThreshold c ≤ n_max) :
    wpCapFront (mkWhpCoreParams c U V w n_max) = capFrontWhp n_max := by
  simp [wpCapFront, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_capBack (h : whpThreshold c ≤ n_max) :
    wpCapBack (mkWhpCoreParams c U V w n_max) = capBackWhp n_max := by
  simp [wpCapBack, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_totalLoc (h : whpThreshold c ≤ n_max) :
    wpTotalLoc (mkWhpCoreParams c U V w n_max) = totalLocalCoordsWhp n_max := by
  simp [wpTotalLoc, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_frontTotal (h : whpThreshold c ≤ n_max) :
    wpFrontTotal (mkWhpCoreParams c U V w n_max) = numBucketsWhp n_max * capFrontWhp n_max := by
  simp [wpFrontTotal, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_poolSize (h : whpThreshold c ≤ n_max) :
    wpPoolSize (mkWhpCoreParams c U V w n_max) = poolSizeWhp n_max := by
  simp [wpPoolSize, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_overmarsThresh (h : whpThreshold c ≤ n_max) :
    wpOvermarsThresh (mkWhpCoreParams c U V w n_max) = 5 * (slabScale n_max) ^ 12 := by
  simp [wpOvermarsThresh, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_globalPtrBits (h : whpThreshold c ≤ n_max) :
    wpGlobalPtrBits (mkWhpCoreParams c U V w n_max) = globalPtrBits n_max := by
  simp [wpGlobalPtrBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_permActBits (h : whpThreshold c ≤ n_max) :
    wpPermActBits (mkWhpCoreParams c U V w n_max) = 12 * logLogFactor n_max + 4 := by
  simp [wpPermActBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_trieChildEntries (h : whpThreshold c ≤ n_max) :
    wpTrieChildEntries (mkWhpCoreParams c U V w n_max) = trieChildEntriesWhp c n_max := by
  simp [wpTrieChildEntries, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_maxTrieNodes (h : whpThreshold c ≤ n_max) :
    wpMaxTrieNodes (mkWhpCoreParams c U V w n_max) = maxTrieNodesWhp c n_max := by
  simp [wpMaxTrieNodes, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_hMaxBTree (h : whpThreshold c ≤ n_max) :
    wpHMaxBTree (mkWhpCoreParams c U V w n_max) = hMaxBTree := by
  simp [wpHMaxBTree, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_tMin (h : whpThreshold c ≤ n_max) :
    wpTMin (mkWhpCoreParams c U V w n_max) = tMinWhp n_max := by
  simp [wpTMin, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_capLanes (h : whpThreshold c ≤ n_max) :
    wpCapLanes (mkWhpCoreParams c U V w n_max) = 2 * tMinWhp n_max := by
  simp [wpCapLanes, mkWhpCoreParams, Nat.not_lt.mpr h]
private theorem wp_large_fullKeys (h : whpThreshold c ≤ n_max) :
    wpFullKeys (mkWhpCoreParams c U V w n_max) = 2 * tMinWhp n_max - 1 := by
  simp [wpFullKeys, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_wKey (h : whpThreshold c ≤ n_max) :
    wpWKey (mkWhpCoreParams c U V w n_max) = keyLaneBitsWhp n_max := by
  simp [wpWKey, mkWhpCoreParams, Nat.not_lt.mpr h]
private theorem wp_large_maskWKey (h : whpThreshold c ≤ n_max) :
    wpMaskWKey (mkWhpCoreParams c U V w n_max) = 2 ^ keyLaneBitsWhp n_max - 1 := by
  simp [wpMaskWKey, mkWhpCoreParams, Nat.not_lt.mpr h]
private theorem wp_large_swarOnesCap (h : whpThreshold c ≤ n_max) :
    wpSwarOnesCap (mkWhpCoreParams c U V w n_max) =
      swarOnes (keyLaneBitsWhp n_max) (2 * tMinWhp n_max) := by
  simp [wpSwarOnesCap, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_valsWordBits (h : whpThreshold c ≤ n_max) :
    wpValsWordBits (mkWhpCoreParams c U V w n_max) = valsWordBitsWhp n_max := by
  simp [wpValsWordBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_keysWordBits (h : whpThreshold c ≤ n_max) :
    wpKeysWordBits (mkWhpCoreParams c U V w n_max) = keysWordBitsWhp n_max := by
  simp [wpKeysWordBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_wVal (h : whpThreshold c ≤ n_max) :
    wpWVal (mkWhpCoreParams c U V w n_max) = valLaneBitsWhp n_max := by
  simp [wpWVal, mkWhpCoreParams, Nat.not_lt.mpr h]
private theorem wp_large_maskWVal (h : whpThreshold c ≤ n_max) :
    wpMaskWVal (mkWhpCoreParams c U V w n_max) = 2 ^ valLaneBitsWhp n_max - 1 := by
  simp [wpMaskWVal, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_nodeMetaBits (h : whpThreshold c ≤ n_max) :
    wpNodeMetaBits (mkWhpCoreParams c U V w n_max) = nodeMetaBitsWhp n_max := by
  simp [wpNodeMetaBits, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_nSlice (h : whpThreshold c ≤ n_max) :
    wpNSlice (mkWhpCoreParams c U V w n_max) = nSliceWhp n_max := by
  simp [wpNSlice, mkWhpCoreParams, Nat.not_lt.mpr h]
private theorem wp_large_offHashBkt (h : whpThreshold c ≤ n_max) :
    wpOffHashBkt (mkWhpCoreParams c U V w n_max) = offHashBkt := by
  simp [wpOffHashBkt, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offHashFp (h : whpThreshold c ≤ n_max) :
    wpOffHashFp (mkWhpCoreParams c U V w n_max) = offHashFp c w n_max := by
  simp [wpOffHashFp, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offQuot (h : whpThreshold c ≤ n_max) :
    wpOffQuot (mkWhpCoreParams c U V w n_max) = offQuotWhp c w n_max := by
  simp [wpOffQuot, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offVal (h : whpThreshold c ≤ n_max) :
    wpOffVal (mkWhpCoreParams c U V w n_max) = offValWhp c U w n_max := by
  simp [wpOffVal, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offPermAct (h : whpThreshold c ≤ n_max) :
    wpOffPermAct (mkWhpCoreParams c U V w n_max) = offPermAct c U V w n_max := by
  simp [wpOffPermAct, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offLocState (h : whpThreshold c ≤ n_max) :
    wpOffLocState (mkWhpCoreParams c U V w n_max) = offLocState c U V w n_max := by
  simp [wpOffLocState, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offBktMeta (h : whpThreshold c ≤ n_max) :
    wpOffBktMeta (mkWhpCoreParams c U V w n_max) = offBktMeta c U V w n_max := by
  simp [wpOffBktMeta, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offFbStart (h : whpThreshold c ≤ n_max) :
    wpOffFbStart (mkWhpCoreParams c U V w n_max) = offFbStart c U V w n_max := by
  simp [wpOffFbStart, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offBackPtr (h : whpThreshold c ≤ n_max) :
    wpOffBackPtr (mkWhpCoreParams c U V w n_max) = offBackPtr c U V w n_max := by
  simp [wpOffBackPtr, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offPoolFreeStack (h : whpThreshold c ≤ n_max) :
    wpOffPoolFreeStack (mkWhpCoreParams c U V w n_max) = offPoolFreeStack c U V w n_max := by
  simp [wpOffPoolFreeStack, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offPoolOwner (h : whpThreshold c ≤ n_max) :
    wpOffPoolOwner (mkWhpCoreParams c U V w n_max) = offPoolOwner c U V w n_max := by
  simp [wpOffPoolOwner, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offBtMeta (h : whpThreshold c ≤ n_max) :
    wpOffBtMeta (mkWhpCoreParams c U V w n_max) = offBtMeta c U V w n_max := by
  simp [wpOffBtMeta, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offBtKeys (h : whpThreshold c ≤ n_max) :
    wpOffBtKeys (mkWhpCoreParams c U V w n_max) = offBtKeys c U V w n_max := by
  simp [wpOffBtKeys, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offBtVals (h : whpThreshold c ≤ n_max) :
    wpOffBtVals (mkWhpCoreParams c U V w n_max) = offBtVals c U V w n_max := by
  simp [wpOffBtVals, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offTrieChild0 (h : whpThreshold c ≤ n_max) :
    wpOffTrieChild0 (mkWhpCoreParams c U V w n_max) = offTrieChild0 c U V w n_max := by
  simp [wpOffTrieChild0, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offTrieChild1 (h : whpThreshold c ≤ n_max) :
    wpOffTrieChild1 (mkWhpCoreParams c U V w n_max) = offTrieChild1 c U V w n_max := by
  simp [wpOffTrieChild1, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offTrieMeta0 (h : whpThreshold c ≤ n_max) :
    wpOffTrieMeta0 (mkWhpCoreParams c U V w n_max) = offTrieMeta0 c U V w n_max := by
  simp [wpOffTrieMeta0, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offTrieMeta1 (h : whpThreshold c ≤ n_max) :
    wpOffTrieMeta1 (mkWhpCoreParams c U V w n_max) = offTrieMeta1 c U V w n_max := by
  simp [wpOffTrieMeta1, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offTrieItems0 (h : whpThreshold c ≤ n_max) :
    wpOffTrieItems0 (mkWhpCoreParams c U V w n_max) = offTrieItems0 c U V w n_max := by
  simp [wpOffTrieItems0, mkWhpCoreParams, Nat.not_lt.mpr h]
theorem wp_large_offTrieItems1 (h : whpThreshold c ≤ n_max) :
    wpOffTrieItems1 (mkWhpCoreParams c U V w n_max) = offTrieItems1 c U V w n_max := by
  simp [wpOffTrieItems1, mkWhpCoreParams, Nat.not_lt.mpr h]

end ParamSimp

/-- When `whpThreshold c ≤ n_max`, `16 * numBucketsWhp n_max ≤ n_max`. -/
theorem sixteen_mul_numBuckets_le_n_max {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    16 * numBucketsWhp n_max ≤ n_max := by
  have hL12 : 16 ≤ (slabScale n_max) ^ 12 := by
    calc 16 ≤ (2 ^ 1) ^ 12 := by decide
      _ ≤ (slabScale n_max) ^ 12 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (one_le_logLogFactor n_max)) 12
  calc 16 * numBucketsWhp n_max
      = numBucketsWhp n_max * 16 := Nat.mul_comm _ _
    _ ≤ numBucketsWhp n_max * (slabScale n_max) ^ 12 := Nat.mul_le_mul_left _ hL12
    _ ≤ n_max := numBucketsWhp_mul_scale_pow12_le hth

/-- When `whpThreshold c ≤ n_max`, `totalBTreeNodesWhp n_max ≤ n_max`. -/
theorem totalBTreeNodesWhp_le_n_max {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    totalBTreeNodesWhp n_max ≤ n_max := by
  have hm_ge : 6553600 ≤ Nat.log 2 n_max := (le_bMinWhp c).trans (bMinWhp_le_log hth)
  set m := Nat.log 2 n_max
  set q := m / 1024
  have hq_ge : 6400 ≤ q := by omega
  have hm_lt_pow : m < 2 ^ (Nat.log 2 q + 11) := by
    have hq_lt := Nat.lt_pow_succ_log_self Nat.one_lt_two q
    have hm_lt : m < (q + 1) * 1024 := by dsimp only [q]; omega
    exact hm_lt.trans_le
      ((Nat.mul_le_mul_right 1024 hq_lt).trans_eq (by rw [Nat.pow_add, Nat.pow_succ]; ring))
  have hlog_m : Nat.log 2 m ≤ Nat.log 2 q + 10 :=
    Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega : m ≠ 0) hm_lt_pow)
  have hn4 : 4 ≤ n_max :=
    not_lt.mp fun h => absurd (hm_ge.trans (Nat.log_mono_right (Nat.le_of_lt_succ h))) (by decide)
  have hell : logLogFactor n_max ≤ Nat.log 2 q + 12 := by
    unfold logLogFactor
    rw [max_eq_left hn4]
    have hcl1 : Nat.clog 2 n_max ≤ m + 1 :=
      (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
        (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
    have hlt2 := Nat.lt_pow_succ_log_self Nat.one_lt_two m
    have hcl2 : Nat.clog 2 (Nat.clog 2 n_max) ≤ Nat.log 2 m + 2 :=
      (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (by rw [Nat.pow_succ]; omega)
    omega
  have hsq := Nat.mul_log_le_add_sq Nat.one_lt_two 80 q
  have h80_ell : 80 * logLogFactor n_max ≤ 3 * q := by
    calc 80 * logLogFactor n_max ≤ 80 * (Nat.log 2 q + 12) := Nat.mul_le_mul_left 80 hell
      _ = 80 * Nat.log 2 q + 960 := by ring
      _ ≤ (q + 80 ^ 2) + 960 := Nat.add_le_add_right hsq 960
      _ ≤ 3 * q := by omega
  have h25600 : 160 * (160 * logLogFactor n_max) ≤ m := by
    calc 160 * (160 * logLogFactor n_max) = 320 * (80 * logLogFactor n_max) := by ring
      _ ≤ 320 * (3 * q) := Nat.mul_le_mul_left 320 h80_ell
      _ = 960 * q := by ring
      _ ≤ 1024 * q := Nat.mul_le_mul_right q (by decide)
      _ ≤ m := Nat.mul_div_le m 1024
  have ht160 : 160 ≤ tMinWhp n_max :=
    ((Nat.le_div_iff_mul_le (by have := one_le_logLogFactor n_max; positivity)).mpr h25600).trans
      (le_max_right 2 _)
  have hns_div : 32 * (slabScale n_max) ^ 12 / (tMinWhp n_max - 1) ≤
    (slabScale n_max) ^ 12 / 4 := by
    calc 32 * (slabScale n_max) ^ 12 / (tMinWhp n_max - 1)
        ≤ 32 * (slabScale n_max) ^ 12 / 128 := Nat.div_le_div_left (by omega) (by decide)
      _ = 32 * (slabScale n_max) ^ 12 / (32 * 4) := rfl
      _ = (slabScale n_max) ^ 12 / 4 := Nat.mul_div_mul_left _ 4 (by decide)
  have h4096 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by decide
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left (two_le_slabScale n_max) 12
  have h3ns : 3 * nSliceWhp n_max ≤ (slabScale n_max) ^ 12 := by
    dsimp only [nSliceWhp]; omega
  calc totalBTreeNodesWhp n_max
      = numBucketsWhp n_max * (3 * nSliceWhp n_max) := by unfold totalBTreeNodesWhp; ring
    _ ≤ numBucketsWhp n_max * (slabScale n_max) ^ 12 := Nat.mul_le_mul_left _ h3ns
    _ ≤ n_max := numBucketsWhp_mul_scale_pow12_le hth

namespace WhpLargeEnv

variable {c U V w₀ n_max w base : ℕ}

theorem fits_largeSpace (h : WhpLargeEnv c U V w₀ n_max w base) :
    Fits w (base + largeSpaceWhp c U V w₀ n_max) := by
  rcases h with ⟨_, _, rfl, hth, _, _, _, hfit⟩
  rwa [whpSpace, ite_eq_right (Nat.not_lt.mpr hth)] at hfit

theorem log_lt_w (h : WhpLargeEnv c U V w₀ n_max w base) :
    Nat.log 2 n_max < w := by
  rcases h with ⟨_, _, rfl, hth, hnU, hU, _, _⟩
  exact log_n_max_lt_w hth hnU hU

theorem two_le_w (h : WhpLargeEnv c U V w₀ n_max w base) : 2 ≤ w := by
  have := (le_bMinWhp c).trans ((bMinWhp_le_log h.2.2.2.1).trans h.log_lt_w.le)
  omega

theorem three_le_w (h : WhpLargeEnv c U V w₀ n_max w base) : 3 ≤ w := by
  have h1 := log_ge_mul_ell h.2.2.2.1
  have h2 := one_le_logLogFactor n_max
  exact Nat.succ_le_of_lt ((by omega : 2 ≤ Nat.log 2 n_max).trans_lt h.log_lt_w)

theorem keysWordBits_lt_w (h : WhpLargeEnv c U V w₀ n_max w base) :
    keysWordBitsWhp n_max < w :=
  ((Nat.le_add_right _ _).trans_lt (keysWordBitsWhp_lt_log h.2.2.2.1)).trans h.log_lt_w

theorem valsWordBits_lt_w (h : WhpLargeEnv c U V w₀ n_max w base) :
    valsWordBitsWhp n_max < w :=
  ((Nat.le_add_right _ _).trans_lt (valsWordBitsWhp_lt_log h.2.2.2.1)).trans h.log_lt_w

theorem fits_of_le_n_max (h : WhpLargeEnv c U V w₀ n_max w base) {x : ℕ} (hx : x ≤ n_max) :
    Fits w x := by
  rcases h with ⟨_, _, rfl, _, hnU, hU, _, _⟩
  exact (hx.trans hnU).trans_lt hU

theorem numBuckets_le_n_max (h : WhpLargeEnv c U V w₀ n_max w base) :
    numBucketsWhp n_max ≤ n_max := by
  have hL12 : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
  exact (Nat.le_mul_of_pos_right _ hL12).trans (numBucketsWhp_mul_scale_pow12_le h.2.2.2.1)

theorem fits_const (h : WhpLargeEnv c U V w₀ n_max w base) {K : ℕ} (hK : K ≤ 1024) :
    Fits w K := by
  have hM := (large_bounds_lt_n_max h.2.2.2.1).1
  exact h.fits_of_le_n_max ((hK.trans hM).trans h.numBuckets_le_n_max)

theorem fits_hdr_addr (h : WhpLargeEnv c U V w₀ n_max w base) {off : ℕ} (hoff : off < 32) :
    Fits w (base + off) :=
  h.fits_largeSpace.of_le (Nat.add_le_add_left (hoff.le.trans
    (headerWords_le_largeSpaceWhp c U V w₀ n_max)) base)

/-- Helper producing the `Realizes` precondition of `readPackedGenProg` / `writePackedGenProg`
for any array segment inside `largeSpaceWhp`. -/
theorem packed_safe_of_le (h : WhpLargeEnv c U V w₀ n_max w base)
    {off N k idx : ℕ} (hk : k ≤ w₀) (hidx : idx < N)
    (hend : off + packedWords N k w₀ ≤ largeSpaceWhp c U V w₀ n_max) :
    ∃ N', w = w₀ ∧ 0 < w ∧ k ≤ w ∧ idx < N' ∧ Fits w (base + off + packedWords N' k w) := by
  obtain rfl := h.2.2.1
  exact ⟨N, rfl, h.2.1, hk, hidx, h.fits_largeSpace.of_le (by omega)⟩

/-- Full offset bound ladder for `largeSpaceWhp` segments. -/
theorem seg_end_le (c U V w₀ n_max : ℕ) :
    offQuotWhp c w₀ n_max + packedWords n_max (quotBitsWhp U n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offValWhp c U w₀ n_max + packedWords n_max (valBits V) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offPermAct c U V w₀ n_max + packedWords n_max (12 * logLogFactor n_max + 4) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offLocState c U V w₀ n_max +
        packedWords (numBucketsWhp n_max * totalLocalCoordsWhp n_max) 2 w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offBktMeta c U V w₀ n_max +
        packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offFbStart c U V w₀ n_max +
        packedWords (numBucketsWhp n_max + 1) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offBackPtr c U V w₀ n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offPoolFreeStack c U V w₀ n_max + packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offPoolOwner c U V w₀ n_max + packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offBtMeta c U V w₀ n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offBtKeys c U V w₀ n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offBtVals c U V w₀ n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offTrieChild0 c U V w₀ n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offTrieChild1 c U V w₀ n_max +
        packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offTrieMeta0 c U V w₀ n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offTrieMeta1 c U V w₀ n_max +
        packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offTrieItems0 c U V w₀ n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max ∧
    offTrieItems1 c U V w₀ n_max +
        packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w₀ ≤
      largeSpaceWhp c U V w₀ n_max := by
  have hch := largeOffsetChain c U V w₀ n_max
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem quot_safe (h : WhpLargeEnv c U V w₀ n_max w base) {idx : ℕ}
    (hidx : idx < n_max) :
    ∃ N, w = w₀ ∧ 0 < w ∧ quotBitsWhp U n_max ≤ w ∧ idx < N ∧
      Fits w (base + offQuotWhp c w₀ n_max + packedWords N (quotBitsWhp U n_max) w) :=
  h.packed_safe_of_le ((Nat.sub_le _ _).trans (keyBits_le_w h.2.2.2.2.2.1)) hidx
    (seg_end_le c U V w₀ n_max).1

theorem val_safe (h : WhpLargeEnv c U V w₀ n_max w base) {idx : ℕ}
    (hidx : idx < n_max) :
    ∃ N, w = w₀ ∧ 0 < w ∧ valBits V ≤ w ∧ idx < N ∧
      Fits w (base + offValWhp c U w₀ n_max + packedWords N (valBits V) w) :=
  h.packed_safe_of_le (valBits_le_w h.2.2.2.2.2.2.1) hidx
    (seg_end_le c U V w₀ n_max).2.1

theorem fbStart_safe (h : WhpLargeEnv c U V w₀ n_max w base) {idx : ℕ}
    (hidx : idx < numBucketsWhp n_max + 1) :
    ∃ N, w = w₀ ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offFbStart c U V w₀ n_max + packedWords N (globalPtrBits n_max) w) :=
  h.packed_safe_of_le (globalPtrBits_le_w h.2.2.2.2.1 h.2.2.2.2.2.1) hidx
    (seg_end_le c U V w₀ n_max).2.2.2.2.2.1

theorem bktMeta_safe (h : WhpLargeEnv c U V w₀ n_max w base) {idx : ℕ}
    (hidx : idx < 16 * numBucketsWhp n_max) :
    ∃ N, w = w₀ ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offBktMeta c U V w₀ n_max + packedWords N (globalPtrBits n_max) w) :=
  h.packed_safe_of_le (globalPtrBits_le_w h.2.2.2.2.1 h.2.2.2.2.2.1) hidx
    (seg_end_le c U V w₀ n_max).2.2.2.2.1

theorem btMeta_safe (h : WhpLargeEnv c U V w₀ n_max w base) {idx : ℕ}
    (hidx : idx < totalBTreeNodesWhp n_max) :
    ∃ N, w = w₀ ∧ 0 < w ∧ nodeMetaBitsWhp n_max ≤ w ∧ idx < N ∧
      Fits w (base + offBtMeta c U V w₀ n_max + packedWords N (nodeMetaBitsWhp n_max) w) := by
  have hnm : nodeMetaBitsWhp n_max ≤ w₀ := by
    have h1 := log_ge_mul_ell h.2.2.2.1
    have h2 := one_le_logLogFactor n_max
    have h3 := log_n_max_lt_w h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    unfold nodeMetaBitsWhp
    omega
  exact h.packed_safe_of_le hnm hidx (seg_end_le c U V w₀ n_max).2.2.2.2.2.2.2.2.2.1

theorem btKeys_safe (h : WhpLargeEnv c U V w₀ n_max w base) {idx : ℕ}
    (hidx : idx < totalBTreeNodesWhp n_max) :
    ∃ N, w = w₀ ∧ 0 < w ∧ keysWordBitsWhp n_max ≤ w ∧ idx < N ∧
      Fits w (base + offBtKeys c U V w₀ n_max + packedWords N (keysWordBitsWhp n_max) w) :=
  h.packed_safe_of_le (h.2.2.1 ▸ h.keysWordBits_lt_w.le) hidx
    (seg_end_le c U V w₀ n_max).2.2.2.2.2.2.2.2.2.2.1

theorem btVals_safe (h : WhpLargeEnv c U V w₀ n_max w base) {idx : ℕ}
    (hidx : idx < totalBTreeNodesWhp n_max) :
    ∃ N, w = w₀ ∧ 0 < w ∧ valsWordBitsWhp n_max ≤ w ∧ idx < N ∧
      Fits w (base + offBtVals c U V w₀ n_max + packedWords N (valsWordBitsWhp n_max) w) :=
  h.packed_safe_of_le (h.2.2.1 ▸ h.valsWordBits_lt_w.le) hidx
    (seg_end_le c U V w₀ n_max).2.2.2.2.2.2.2.2.2.2.2.1

end WhpLargeEnv

/-! ## Section 2: Certified SWAR Word-Lane `Memory.Prog` Subroutines -/

/-- Parameter-free `laneGet` (`d = ((W, word), j)`). -/
@[expose] def laneGetGenProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, word), j) => do
    let sh ← pure (j * W)
    let msk ← pure ((1 <<< W) - 1)
    pure ((word >>> sh) &&& msk)

@[simp]
theorem clientResult_laneGetGenProg (W word j : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (laneGetGenProg ((W, word), j)) = laneGet W word j := by
  simp only [laneGetGenProg, pure_bind, StateTransitionSpec.clientResult_pure, Nat.one_shiftLeft]
  rfl

theorem clientState_laneGetGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (laneGetGenProg d) = s := rfl

@[simp]
theorem memoryCost_laneGetGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (laneGetGenProg d) s = 0 := rfl

theorem realizes_laneGetGen :
    Realizes .exact laneGetGenProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w ((W, _), j) _ => W < w ∧ Fits w (j * W))
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨⟨W, _⟩, _⟩
    simp only [Fits, Nat.one_shiftLeft]
  · exact h.2
  · exact Nat.two_pow_pos _
  · exact Nat.pow_lt_pow_right (by decide) h.1

/-- Parameter-free `wordTakeLow` (`d = ((W, j), word)`). -/
@[expose] def wordTakeLowGenProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, j), word) => do
    let sh ← pure (j * W)
    let msk ← pure ((1 <<< sh) - 1)
    pure (word &&& msk)

@[simp]
private theorem clientResult_wordTakeLowGenProg (W j word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordTakeLowGenProg ((W, j), word)) =
      wordTakeLow W j word := by
  simp only [wordTakeLowGenProg, pure_bind, StateTransitionSpec.clientResult_pure,
    Nat.one_shiftLeft]
  rfl

private theorem clientState_wordTakeLowGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (wordTakeLowGenProg d) = s := rfl

@[simp]
private theorem memoryCost_wordTakeLowGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordTakeLowGenProg d) s = 0 := rfl

private theorem realizes_wordTakeLowGen :
    Realizes .exact wordTakeLowGenProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w ((W, j), _) _ => j * W < w)
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨⟨W, j⟩, _⟩
    simp only [Fits, Nat.one_shiftLeft]
  · exact h.trans Nat.lt_two_pow_self
  · exact Nat.two_pow_pos _
  · exact Nat.pow_lt_pow_right (by decide) h

/-- Parameter-free `wordDropLow` (`d = ((W, j), word)`). -/
@[expose] def wordDropLowGenProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, j), word) => do
    let sh ← pure (j * W)
    pure (word >>> sh)

@[simp]
private theorem clientResult_wordDropLowGenProg (W j word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordDropLowGenProg ((W, j), word)) = wordDropLow W j word :=
  rfl

private theorem clientState_wordDropLowGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (wordDropLowGenProg d) = s := rfl

@[simp]
private theorem memoryCost_wordDropLowGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordDropLowGenProg d) s = 0 := rfl

private theorem realizes_wordDropLowGen :
    Realizes .exact wordDropLowGenProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w ((W, j), _) _ => Fits w (j * W))
      (fun _ _ => 0) := by
  realize
  exact h

/-- Parameter-free `wordInsertAt` (`d = (((W, j), v), word)`). -/
@[expose] def wordInsertAtGenProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((W, j), v), word) => do
    let sh ← pure (j * W)
    let low ← pure (word &&& ((1 <<< sh) - 1))
    let hi ← pure (word >>> sh)
    pure (low + ((v + (hi <<< W)) <<< sh))

@[simp]
theorem clientResult_wordInsertAtGenProg (W j v word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordInsertAtGenProg (((W, j), v), word)) =
      wordInsertAt W j v word := by
  simp only [wordInsertAtGenProg, pure_bind, StateTransitionSpec.clientResult_pure,
    Nat.one_shiftLeft]
  rfl

theorem clientState_wordInsertAtGenProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (wordInsertAtGenProg d) = s := rfl

@[simp]
theorem memoryCost_wordInsertAtGenProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordInsertAtGenProg d) s = 0 := rfl

theorem realizes_wordInsertAtGen :
    Realizes .exact wordInsertAtGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w (((W, j), v), word) _ => ∃ m, j ≤ m ∧ (m + 1) * W < w ∧
        v < 2 ^ W ∧ word < 2 ^ (m * W))
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨⟨⟨W, j⟩, v⟩, word⟩
    obtain ⟨m, hj, hmW, hv, hword⟩ := h
    have hsh : j * W < w := (Nat.mul_le_mul_right _ (hj.trans (Nat.le_succ m))).trans_lt hmW
    simp only [Fits, Nat.one_shiftLeft]
  · exact hsh.trans Nat.lt_two_pow_self
  · exact Nat.two_pow_pos _
  · exact Nat.pow_lt_pow_right (by decide) hsh
  · exact (wordInsertAt_lt hj hv hword).trans (Nat.pow_lt_pow_right (by decide) hmW)

/-- Parameter-free `wordDeleteAt` (`d = ((W, j), word)`). -/
@[expose] def wordDeleteAtGenProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, j), word) => do
    let sh ← pure (j * W)
    let sh1 ← pure ((j + 1) * W)
    let low ← pure (word &&& ((1 <<< sh) - 1))
    pure (low + ((word >>> sh1) <<< sh))

@[simp]
theorem clientResult_wordDeleteAtGenProg (W j word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordDeleteAtGenProg ((W, j), word)) =
      wordDeleteAt W j word := by
  simp only [wordDeleteAtGenProg, pure_bind, StateTransitionSpec.clientResult_pure,
    Nat.one_shiftLeft]
  rfl

theorem clientState_wordDeleteAtGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (wordDeleteAtGenProg d) = s := rfl

@[simp]
theorem memoryCost_wordDeleteAtGenProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordDeleteAtGenProg d) s = 0 := rfl

theorem realizes_wordDeleteAtGen :
    Realizes .exact wordDeleteAtGenProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w ((W, j), word) _ => ∃ m, 0 < W ∧ j ≤ m ∧ (m + 1) * W < w ∧
        word < 2 ^ ((m + 1) * W))
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨⟨W, j⟩, word⟩
    obtain ⟨m, hW, hj, hmW, hword⟩ := h
    have hsh1 : (j + 1) * W < w := (Nat.mul_le_mul_right _ (Nat.succ_le_succ hj)).trans_lt hmW
    have hsh : j * W < w := (Nat.mul_le_mul_right _ (Nat.le_succ j)).trans_lt hsh1
    simp only [Fits, Nat.one_shiftLeft]
  · exact hsh.trans Nat.lt_two_pow_self
  · exact hsh1.trans Nat.lt_two_pow_self
  · exact ((Nat.le_mul_of_pos_right _ hW).trans_lt hsh1).trans Nat.lt_two_pow_self
  · exact Nat.two_pow_pos _
  · exact Nat.pow_lt_pow_right (by decide) hsh
  · exact (wordDeleteAt_lt hj hword).trans (Nat.pow_lt_pow_right (by decide)
      ((Nat.mul_le_mul_right _ (Nat.le_succ m)).trans_lt hmW))

/-- Parameter-free `wordUpdateAt` (`d = (((W, j), v), word)`). -/
@[expose] def wordUpdateAtGenProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((W, j), v), word) => do
    let sh ← pure (j * W)
    let sh1 ← pure ((j + 1) * W)
    let low ← pure (word &&& ((1 <<< sh) - 1))
    let hi ← pure (word >>> sh1)
    pure (low + ((v + (hi <<< W)) <<< sh))

@[simp]
theorem clientResult_wordUpdateAtGenProg (W j v word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordUpdateAtGenProg (((W, j), v), word)) =
      wordUpdateAt W j v word := by
  simp only [wordUpdateAtGenProg, pure_bind, StateTransitionSpec.clientResult_pure,
    Nat.one_shiftLeft]
  rfl

theorem clientState_wordUpdateAtGenProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (wordUpdateAtGenProg d) = s := rfl

@[simp]
theorem memoryCost_wordUpdateAtGenProg (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordUpdateAtGenProg d) s = 0 := rfl

theorem realizes_wordUpdateAtGen :
    Realizes .exact wordUpdateAtGenProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w (((W, j), v), word) _ => ∃ m, 0 < W ∧ j < m ∧ m * W < w ∧
        v < 2 ^ W ∧ word < 2 ^ (m * W))
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨⟨⟨W, j⟩, v⟩, word⟩
    obtain ⟨m, hW, hj, hmW, hv, hword⟩ := h
    have hsh1 : (j + 1) * W < w := (Nat.mul_le_mul_right _ hj).trans_lt hmW
    have hsh : j * W < w := (Nat.mul_le_mul_right _ (Nat.le_succ j)).trans_lt hsh1
    simp only [Fits, Nat.one_shiftLeft]
  · exact hsh.trans Nat.lt_two_pow_self
  · exact hsh1.trans Nat.lt_two_pow_self
  · exact ((Nat.le_mul_of_pos_right _ hW).trans_lt hsh1).trans Nat.lt_two_pow_self
  · exact Nat.two_pow_pos _
  · exact Nat.pow_lt_pow_right (by decide) hsh
  · exact (wordUpdateAt_lt hj hv hword).trans (Nat.pow_lt_pow_right (by decide) hmW)

/-- Borrow-free subtraction definedness and upper bound for `swarRank`. -/
private theorem swarRank_lhs_bounds {fpBits m q keysWord : ℕ}
    (hq : q < 2 ^ fpBits) (hkw : keysWord < 2 ^ (m * (fpBits + 2)))
    (hlanes : ∀ j < m, laneGet (fpBits + 2) keysWord j < 2 ^ fpBits) :
    let W := fpBits + 2
    let onesM := swarOnes W m
    keysWord + onesM ≤ (2 ^ fpBits + q) * onesM ∧
      (2 ^ fpBits + q) * onesM < 2 ^ (m * W) := by
  set W := fpBits + 2
  have hW : 1 ≤ W := by omega
  have hW_pos : 0 < W := by omega
  have hkw_sum := word_eq_sum_laneGet hW_pos hkw
  have hones := swarOnes_eq_sum hW m
  refine ⟨?_, ?_⟩
  · rw [hkw_sum, hones, ← sum_add_distrib, mul_sum]
    refine sum_le_sum fun j hj => ?_
    have hk := hlanes j (mem_range.mp hj)
    calc laneGet W keysWord j * 2 ^ (j * W) + 2 ^ (j * W)
        = (laneGet W keysWord j + 1) * 2 ^ (j * W) := by ring
      _ ≤ (2 ^ fpBits + q) * 2 ^ (j * W) := Nat.mul_le_mul_right _ (by omega)
  · have h2W : 2 ^ fpBits + q ≤ 2 ^ W - 1 := by
      dsimp only [W]
      rw [Nat.pow_add]
      have : 0 < 2 ^ fpBits := Nat.two_pow_pos fpBits
      omega
    calc (2 ^ fpBits + q) * swarOnes W m
        ≤ (2 ^ W - 1) * ((2 ^ (m * W) - 1) / (2 ^ W - 1)) := Nat.mul_le_mul_right _ h2W
      _ ≤ 2 ^ (m * W) - 1 := Nat.mul_div_le _ _
      _ < 2 ^ (m * W) := Nat.sub_lt (Nat.two_pow_pos _) one_pos

/-- Precondition for `swarRankGenProg` (`d = (cp, ((m, q), keysWord))`). -/
@[expose] def SwarRankGenPre (w : ℕ) : WhpCoreParams × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (cp, ((m, q), kw)), _ =>
    (∃ base, WhpLargeEnvGen w cp base) ∧
    m < wpCapLanes cp ∧
    q < wpPowFp cp ∧
    kw < 2 ^ (m * wpWKey cp) ∧
    (∀ j < m, laneGet (wpWKey cp) kw j < wpPowFp cp)

/-- Parameter-free `swarRank` (`d = (cp, ((m, q), keysWord))`). -/
@[expose] def swarRankGenProg : WhpCoreParams × ((ℕ × ℕ) × ℕ) → Memory.Prog ℕ
  | (cp, ((m, q), kw)) => do
    let mW ← pure (m * wpWKey cp)
    let onesM ← pure (((1 <<< mW) - 1) / wpMaskWKey cp)
    let lhs ← pure ((wpPowFp cp + q) * onesM)
    let rhs ← pure (kw + onesM)
    let ltm ← pure (((lhs - rhs) >>> wpFpBits cp) &&& onesM)
    let prod ← pure (ltm * wpSwarOnesCap cp)
    let sh ← pure ((wpCapLanes cp - 1) * wpWKey cp)
    pure ((prod >>> sh) &&& wpMaskWKey cp)

theorem clientResult_swarRankGenProg {c U V w n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (m q keysWord : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s
      (swarRankGenProg (mkWhpCoreParams c U V w n_max, ((m, q), keysWord))) =
      swarRank (fpBitsWhp n_max) (2 * tMinWhp n_max) m q keysWord := by
  simp only [swarRankGenProg, wp_large_wKey hth, wp_large_maskWKey hth, wp_large_powFp hth,
    wp_large_fpBits hth, wp_large_swarOnesCap hth, wp_large_capLanes hth, pure_bind,
    StateTransitionSpec.clientResult_pure, Nat.one_shiftLeft]
  rfl

theorem clientState_swarRankGenProg (d : WhpCoreParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (swarRankGenProg d) = s := rfl

@[simp]
theorem memoryCost_swarRankGenProg (d : WhpCoreParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (swarRankGenProg d) s = 0 := rfl

theorem realizes_swarRankGen :
    Realizes .exact swarRankGenProg
      (WordEncoding.encode (α := WhpCoreParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := ℕ))
      SwarRankGenPre
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨cp, ⟨⟨m, q⟩, kw⟩⟩
    obtain ⟨⟨base, c, U, V, w₀, n_max, henv, rfl⟩, hm, hq, hkw, hlanes⟩ := h
    have hth := henv.2.2.2.1
    have hlog := henv.log_lt_w
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hconv_lt : 4 * tMinWhp n_max * keyLaneBitsWhp n_max < w :=
      (swarConvBits_lt_log hth).trans hlog
    simp only [wp_large_wKey hth, wp_large_maskWKey hth, wp_large_powFp hth, wp_large_fpBits hth,
      wp_large_swarOnesCap hth, wp_large_capLanes hth, Fits, Nat.one_shiftLeft]
      at hm hq hkw hlanes ⊢
    have hmW : m * keyLaneBitsWhp n_max < w := (Nat.mul_le_mul_right _ hm.le).trans_lt hkw_lt
  · exact hmW.trans Nat.lt_two_pow_self
  · exact Nat.two_pow_pos _
  · have hkl : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    have hpow : 4 ≤ 2 ^ keyLaneBitsWhp n_max :=
      (by decide : 4 = 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hkl)
    omega
  · exact Nat.pow_lt_pow_right (by decide) hmW
  · exact (swarRank_lhs_bounds hq hkw hlanes).2.trans (Nat.pow_lt_pow_right (by decide) hmW)
  · have hkl_lt : keyLaneBitsWhp n_max < w :=
      (Nat.le_mul_of_pos_left _ (by have := eight_le_tMinWhp hth; omega)).trans_lt hkw_lt
    have hsum : 2 ^ fpBitsWhp n_max + q < 2 ^ keyLaneBitsWhp n_max := by
      rw [keyLaneBitsWhp, Nat.pow_add]; omega
    exact hsum.trans (Nat.pow_lt_pow_right (by decide) hkl_lt)
  · have hones_lt : swarOnes (keyLaneBitsWhp n_max) m < 2 ^ (m * keyLaneBitsWhp n_max) :=
      (Nat.div_le_self _ _).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one)
    have hmW1 : m * keyLaneBitsWhp n_max + 1 ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max := by
      have hkl : 1 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
      calc m * keyLaneBitsWhp n_max + 1
          ≤ m * keyLaneBitsWhp n_max + keyLaneBitsWhp n_max := Nat.add_le_add_left hkl _
        _ = (m + 1) * keyLaneBitsWhp n_max := by ring
        _ ≤ 2 * tMinWhp n_max * keyLaneBitsWhp n_max := Nat.mul_le_mul_right _ hm
    have hsum : kw + swarOnes (keyLaneBitsWhp n_max) m < 2 ^ (m * keyLaneBitsWhp n_max + 1) := by
      rw [Nat.pow_succ]; omega
    exact hsum.trans (Nat.pow_lt_pow_right (by decide) (hmW1.trans_lt hkw_lt))
  · exact (swarRank_lhs_bounds hq hkw hlanes).1
  · have hexp : (2 * (2 * tMinWhp n_max) - 1) * (fpBitsWhp n_max + 2) < w :=
      (Nat.mul_le_mul_right (keyLaneBitsWhp n_max) (by omega)).trans_lt hconv_lt
    exact (ltMask_mul_swarOnes_lt_two_pow
      (fpBits := fpBitsWhp n_max) (capLanes := 2 * tMinWhp n_max) (q := q) (keysWord := kw)
      hm).trans (Nat.pow_lt_pow_right (by decide) hexp)
  · exact Nat.le_of_lt (by have := eight_le_tMinWhp hth; omega)
  · have hsh : (2 * tMinWhp n_max - 1) * keyLaneBitsWhp n_max < w :=
      (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans_lt hkw_lt
    exact hsh.trans Nat.lt_two_pow_self

/-- Parameter-free `splitFullNode` (`d = (cp, (metaW, (keysW, valsW)))`), returning
`((leftMeta, (leftKeys, leftVals)), (sep, (rightMeta, (rightKeys, rightVals))))`. -/
@[expose] def splitFullNodeGenProg :
    WhpCoreParams × (ℕ × (ℕ × ℕ)) →
      Memory.Prog ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))))
  | (cp, (metaW, (keysW, valsW))) => do
    let tm1 ← pure (wpTMin cp - 1)
    let sep ← laneGetGenProg ((wpWKey cp, keysW), tm1)
    let isLf ← pure (metaW % 2)
    let z1 ← pure 1
    if isLf = z1 then do
      let lMeta ← pure (1 + 2 * wpTMin cp)
      let lKeys ← wordTakeLowGenProg ((wpWKey cp, wpTMin cp), keysW)
      let lVals ← wordTakeLowGenProg ((wpWVal cp, wpTMin cp), valsW)
      let rMeta ← pure (1 + 2 * tm1)
      let rKeys ← wordDropLowGenProg ((wpWKey cp, wpTMin cp), keysW)
      let rVals ← wordDropLowGenProg ((wpWVal cp, wpTMin cp), valsW)
      pure ((lMeta, (lKeys, lVals)), (sep, (rMeta, (rKeys, rVals))))
    else do
      let lMeta ← pure (2 * tm1)
      let lKeys ← wordTakeLowGenProg ((wpWKey cp, tm1), keysW)
      let lVals ← wordTakeLowGenProg ((wpWVal cp, wpTMin cp), valsW)
      let rMeta ← pure (2 * tm1)
      let rKeys ← wordDropLowGenProg ((wpWKey cp, wpTMin cp), keysW)
      let rVals ← wordDropLowGenProg ((wpWVal cp, wpTMin cp), valsW)
      pure ((lMeta, (lKeys, lVals)), (sep, (rMeta, (rKeys, rVals))))

theorem clientResult_splitFullNodeGenProg {c U V w n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    (nd : BTreeNode) (s : Memory.State) :
    let out := splitFullNode (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max) nd
    (Memory.spec 0).clientResult s
      (splitFullNodeGenProg
        (mkWhpCoreParams c U V w n_max, (nd.metaWord, (nd.keysWord, nd.valsWord)))) =
      ((out.left.metaWord, (out.left.keysWord, out.left.valsWord)),
       (out.sep, (out.right.metaWord, (out.right.keysWord, out.right.valsWord)))) := by
  have hmod : (nd.metaWord % 2 = 1) ↔ (metaIsLeaf nd.metaWord = true) := by
    rcases Nat.mod_two_eq_zero_or_one nd.metaWord with h | h <;> simp [metaIsLeaf, h]
  unfold splitFullNodeGenProg splitFullNode
  simp only [wp_large_tMin hth, wp_large_wKey hth, wp_large_wVal hth, pure_bind]
  rw [clientResult_bind, clientState_laneGetGenProg, clientResult_laneGetGenProg]
  cases h : metaIsLeaf nd.metaWord <;>
    simp only [hmod, h, Bool.false_eq_true, ↓reduceIte, client_simps,
      clientResult_wordTakeLowGenProg, clientResult_wordDropLowGenProg, mkNodeMeta, Nat.zero_add,
      keyLaneBitsWhp]

theorem clientState_splitFullNodeGenProg (d : WhpCoreParams × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec 0).clientState s (splitFullNodeGenProg d) = s := by
  unfold splitFullNodeGenProg
  simp only [pure_bind]
  rw [clientState_bind, clientState_laneGetGenProg]
  split_ifs <;> rfl

theorem memoryCost_splitFullNodeGenProg (d : WhpCoreParams × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (splitFullNodeGenProg d) s = 0 := by
  unfold splitFullNodeGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, clientState_laneGetGenProg, memoryCost_laneGetGenProg]
  split_ifs <;> rfl

theorem realizes_splitFullNodeGen :
    Realizes .exact splitFullNodeGenProg
      (WordEncoding.encode (α := WhpCoreParams × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))))
      (fun w d _ => ∃ base, WhpLargeEnvGen w d.1 base)
      (fun _ _ => 0) := by
  realize [realizes_laneGetGen, realizes_wordTakeLowGen, realizes_wordDropLowGen]
  all_goals
    rcases d with ⟨cp, ⟨mW, ⟨kW, vW⟩⟩⟩
    obtain ⟨base, c, U, V, w₀, n_max, henv, rfl⟩ := h
    have hth := henv.2.2.2.1
    have ht8 := eight_le_tMinWhp hth
    have hkw_lt : 2 * tMinWhp n_max * keyLaneBitsWhp n_max < w := henv.keysWordBits_lt_w
    have hvw_lt : 2 * tMinWhp n_max * valLaneBitsWhp n_max < w := henv.valsWordBits_lt_w
    have hkl_ge2 : 2 ≤ keyLaneBitsWhp n_max := by unfold keyLaneBitsWhp fpBitsWhp; omega
    have hkl_lt : keyLaneBitsWhp n_max < w :=
      (Nat.le_mul_of_pos_left _ (by omega)).trans_lt hkw_lt
    have htk_lt : tMinWhp n_max * keyLaneBitsWhp n_max < w :=
      (Nat.mul_le_mul_right _ (by omega : tMinWhp n_max ≤ 2 * tMinWhp n_max)).trans_lt hkw_lt
    have htm1k_lt : (tMinWhp n_max - 1) * keyLaneBitsWhp n_max < w :=
      (Nat.mul_le_mul_right _ (by omega : tMinWhp n_max - 1 ≤ 2 * tMinWhp n_max)).trans_lt hkw_lt
    have htv_lt : tMinWhp n_max * valLaneBitsWhp n_max < w :=
      (Nat.mul_le_mul_right _ (by omega : tMinWhp n_max ≤ 2 * tMinWhp n_max)).trans_lt hvw_lt
    have h1_2t_lt : 1 + 2 * tMinWhp n_max < w := by
      have := Nat.mul_le_mul_left (2 * tMinWhp n_max) hkl_ge2
      omega
    try simp only [wp_large_tMin hth, wp_large_wKey hth, wp_large_wVal hth]
    first
    | omega
    | exact henv.fits_const (by decide)
    | exact (show _ < w by omega).trans Nat.lt_two_pow_self

/-! ## Section 3: Packed B+-Tree Slice Header and Node `Memory.Prog` Primitives -/

/-- Read `(alloc, root)` of slice `sIdx = d.2` at `base = d.1.2`. -/
@[expose] def readSliceHeaderGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), sIdx) => do
    let b ← pure (sIdx / 3)
    let role ← pure (sIdx % 3)
    let idxAlloc ← pure (16 * b + 10 + 2 * role)
    let idxRoot ← pure (16 * b + 11 + 2 * role)
    let alloc ← readPackedGenProg (((base, wpOffBktMeta cp),
      (wpGlobalPtrBits cp, wpW cp)), idxAlloc)
    let root ← readPackedGenProg (((base, wpOffBktMeta cp),
      (wpGlobalPtrBits cp, wpW cp)), idxRoot)
    pure (alloc, root)

theorem readSliceHeaderGenProg_spec {c U V w n_max base sIdx : ℕ} {sl : BTreeSlice}
    {s : Memory.State} (hth : whpThreshold c ≤ n_max) (hw : 0 < w)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem) :
    let prog := readSliceHeaderGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (sl.alloc, sl.root) ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  have hidxA : 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max := by omega
  have hidxR : 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max := by omega
  have hba_le : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  unfold readSliceHeaderGenProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  refine ⟨rfl, ?_, rfl, validProg_bind (validProg_readPacked hw hidxA hba_le)
    (validProg_bind (validProg_readPacked hw hidxR hba_le) (validProg_pure _))⟩
  dsimp only [readPackedGenProg]
  rw [clientResult_bind, clientState_readPackedProg,
    clientResult_bind, clientState_readPackedProg,
    clientResult_readPackedProg, clientResult_readPackedProg,
    StateTransitionSpec.clientResult_pure, hrep.2.1, hrep.2.2.1]

theorem realizes_readSliceHeaderGen :
    Realizes .exact readSliceHeaderGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), sIdx) _ => WhpLargeEnvGen w cp base ∧ sIdx < 3 * wpM cp)
      (fun _ _ => 0) := by
  realize [realizes_readPackedGen]
  all_goals
    rcases d with ⟨⟨cp, base⟩, sIdx⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx⟩ := h
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    simp only [wp_large_M hth, wp_large_offBktMeta hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hsIdx ⊢
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)

/-- Write `alloc := d.2` (`≤ wpNSlice`) for slice `sIdx = d.1.2`. -/
@[expose] def writeSliceAllocGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), sIdx), newAlloc) => do
    let b ← pure (sIdx / 3)
    let role ← pure (sIdx % 3)
    let idxAlloc ← pure (16 * b + 10 + 2 * role)
    writePackedGenProg ((((base, wpOffBktMeta cp),
      (wpGlobalPtrBits cp, wpW cp)), idxAlloc), newAlloc)

theorem writeSliceAllocGenProg_spec {c U V w n_max base sIdx newAlloc : ℕ}
    {s : Memory.State} (hth : whpThreshold c ≤ n_max) (hw : 0 < w)
    (hnU : n_max ≤ U) (hU : Fits w U)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max) :
    let prog := writeSliceAllocGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), newAlloc)
    let idxA := 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)
    (Memory.spec 0).clientState s prog =
      { mem := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w
          s.mem idxA newAlloc,
        frontier := s.frontier } ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  have hba_le : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hidxA : 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) < 16 * numBucketsWhp n_max := by omega
  unfold writeSliceAllocGenProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  exact ⟨rfl, rfl, validProg_writePacked hw (globalPtrBits_le_w hnU hU) hidxA hba_le⟩

/-- Reset slice `sIdx = d.2` to `zeroBTreeSlice` (`alloc := 0`, `root := 0`). -/
@[expose] def resetBTreeSliceGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), sIdx) => do
    let b ← pure (sIdx / 3)
    let role ← pure (sIdx % 3)
    let idxAlloc ← pure (16 * b + 10 + 2 * role)
    let idxRoot ← pure (16 * b + 11 + 2 * role)
    let z0 ← pure 0
    writePackedGenProg ((((base, wpOffBktMeta cp),
      (wpGlobalPtrBits cp, wpW cp)), idxAlloc), z0)
    writePackedGenProg ((((base, wpOffBktMeta cp),
      (wpGlobalPtrBits cp, wpW cp)), idxRoot), z0)

/-- Node `v` of B-tree slice `sIdx` indexes inside the packed node arrays. -/
private theorem sliceNodeIdx_lt {n_max sIdx v : ℕ} (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hv : v < nSliceWhp n_max) : sIdx * nSliceWhp n_max + v < totalBTreeNodesWhp n_max :=
  calc sIdx * nSliceWhp n_max + v < (sIdx + 1) * nSliceWhp n_max := by
        rw [Nat.add_one_mul]; omega
    _ ≤ totalBTreeNodesWhp n_max := Nat.mul_le_mul_right _ hsIdx

/-- The three packed B-tree node arrays end inside the large-regime region. -/
private theorem btNodeSegs_le (c U V w n_max base : ℕ) :
    base + offBtMeta c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (nodeMetaBitsWhp n_max) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offBtKeys c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (keysWordBitsWhp n_max) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offBtVals c U V w n_max +
        packedWords (totalBTreeNodesWhp n_max) (valsWordBitsWhp n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.2
  omega

theorem resetBTreeSliceGenProg_spec {c U V w n_max base sIdx : ℕ}
    {s : Memory.State} (hth : whpThreshold c ≤ n_max) (hw : 0 < w)
    (hnU : n_max ≤ U) (hU : Fits w U)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max) :
    let prog := resetBTreeSliceGenProg ((mkWhpCoreParams c U V w n_max, base), sIdx)
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl',
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s'.mem) ∧
    (∀ idx < 16 * numBucketsWhp n_max,
      idx ≠ 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3) →
      idx ≠ 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3) →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
    (∀ a, a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hch := largeOffsetChain c U V w n_max
  have hba_le : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by omega
  have hgk : globalPtrBits n_max ≤ w := globalPtrBits_le_w hnU hU
  have h0_lt : 0 < 2 ^ globalPtrBits n_max := Nat.two_pow_pos _
  set idxA := 16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)
  set idxR := 16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)
  have hidxA : idxA < 16 * numBucketsWhp n_max := by omega
  have hidxR : idxR < 16 * numBucketsWhp n_max := by omega
  have hAR_ne : idxA ≠ idxR := by omega
  unfold resetBTreeSliceGenProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  set mem₁ := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idxA 0
  set mem₂ := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₁ idxR 0
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg ((((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w)), idxA), 0)
        >>= fun _ => writePackedGenProg
          ((((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w)), idxR), 0)) =
      { mem := mem₂, frontier := s.frontier } := rfl
  have hout : ∀ a, a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a →
      mem₂ a = s.mem a := fun a ha =>
    (writePacked_outside hw _ hidxR _ (by omega)).trans
      (writePacked_outside hw _ hidxA _ (by omega))
  have hother_bm : ∀ idx < 16 * numBucketsWhp n_max, idx ≠ idxA → idx ≠ idxR →
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₂ idx =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx :=
    fun idx _ h1 h2 =>
      (readPacked_writePacked_of_ne hw mem₁ h2 0).trans
        (readPacked_writePacked_of_ne hw s.mem h1 0)
  refine ⟨rfl, rfl, ?_, ?_, ?_, hother_bm, hout⟩
  · exact validProg_bind (validProg_writePacked hw hgk hidxA hba_le)
      (validProg_writePacked hw hgk hidxR hba_le)
  · rw [hs'_eq]
    refine ⟨Nat.zero_le _, ?_, readPacked_writePacked_self _ _ _ mem₁ idxR h0_lt,
      fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
    exact (readPacked_writePacked_of_ne hw mem₁ hAR_ne 0).trans
      (readPacked_writePacked_self _ _ _ s.mem idxA h0_lt)
  · intro sIdx' hsIdx' hne sl' hrep'
    rw [hs'_eq]
    refine ⟨hrep'.1,
      (hother_bm _ (by omega) (by omega) (by omega)).trans hrep'.2.1,
      (hother_bm _ (by omega) (by omega) (by omega)).trans hrep'.2.2.1,
      fun u hu => ?_⟩
    have hidx_n := sliceNodeIdx_lt hsIdx' (hu.trans_le hrep'.1)
    exact ⟨(readPacked_congr hw (hidx := hidx_n) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))).trans
        (hrep'.2.2.2 u hu).1,
      (readPacked_congr hw (hidx := hidx_n) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))).trans
        (hrep'.2.2.2 u hu).2.1,
      (readPacked_congr hw (hidx := hidx_n) fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega))).trans
        (hrep'.2.2.2 u hu).2.2⟩

theorem realizes_resetBTreeSliceGen :
    Realizes .exact resetBTreeSliceGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), sIdx) _ => WhpLargeEnvGen w cp base ∧ sIdx < 3 * wpM cp)
      (fun _ _ => 0) := by
  realize [realizes_writePackedGen]
  all_goals
    rcases d with ⟨⟨cp, base⟩, sIdx⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx⟩ := h
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    simp only [wp_large_M hth, wp_large_offBktMeta hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at hsIdx ⊢
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)

/-- Read `(metaWord, (keysWord, valsWord))` of node `u = d.2` in slice `sIdx = d.1.2`. -/
@[expose] def readBTreeNodeGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (((cp, base), sIdx), u) => do
    let idx ← pure (sIdx * wpNSlice cp + u)
    let mW ← readPackedGenProg (((base, wpOffBtMeta cp),
      (wpNodeMetaBits cp, wpW cp)), idx)
    let kW ← readPackedGenProg (((base, wpOffBtKeys cp),
      (wpKeysWordBits cp, wpW cp)), idx)
    let vW ← readPackedGenProg (((base, wpOffBtVals cp),
      (wpValsWordBits cp, wpW cp)), idx)
    pure (mW, (kW, vW))

theorem memoryCost_readBTreeNodeGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readBTreeNodeGenProg d) s = 6 := rfl

theorem readBTreeNodeGenProg_spec {c U V w n_max base sIdx u : ℕ} {sl : BTreeSlice}
    {s : Memory.State} (hth : whpThreshold c ≤ n_max) (hw : 0 < w)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max) (hu : u < sl.alloc)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem) :
    let prog := readBTreeNodeGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), u)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      ((sl.nodes u).metaWord, ((sl.nodes u).keysWord, (sl.nodes u).valsWord)) ∧
    memoryCost prog s = 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hu_ns : u < nSliceWhp n_max := hu.trans_le hrep.1
  have hidx := sliceNodeIdx_lt hsIdx hu_ns
  obtain ⟨hsegM, hsegK, hsegV⟩ := btNodeSegs_le c U V w n_max base
  obtain ⟨hndM, hndK, hndV⟩ := hrep.2.2.2 u hu
  unfold readBTreeNodeGenProg
  simp only [wp_large_nSlice hth, wp_large_offBtMeta hth, wp_large_offBtKeys hth,
    wp_large_offBtVals hth, wp_large_nodeMetaBits hth, wp_large_keysWordBits hth,
    wp_large_valsWordBits hth, wp_large_w hth, pure_bind]
  refine ⟨rfl, ?_, rfl, ?_⟩
  · dsimp only [readPackedGenProg]
    rw [clientResult_bind, clientState_readPackedProg,
      clientResult_bind, clientState_readPackedProg,
      clientResult_bind, clientState_readPackedProg,
      clientResult_readPackedProg, clientResult_readPackedProg, clientResult_readPackedProg,
      StateTransitionSpec.clientResult_pure, hndM, hndK, hndV]
  · exact validProg_bind (validProg_readPacked hw hidx hsegM)
      (validProg_bind (validProg_readPacked hw hidx hsegK)
        (validProg_bind (validProg_readPacked hw hidx hsegV) (validProg_pure _)))

theorem realizes_readBTreeNodeGen :
    Realizes .exact readBTreeNodeGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (((cp, base), sIdx), u) _ => WhpLargeEnvGen w cp base ∧
        sIdx < 3 * wpM cp ∧ u < wpNSlice cp)
      (fun _ _ => 0) := by
  realize [realizes_readPackedGen]
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, u⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx, hu⟩ := h
    have hth := henv.2.2.2.1
    simp only [wp_large_M hth, wp_large_nSlice hth, wp_large_offBtMeta hth,
      wp_large_offBtKeys hth, wp_large_offBtVals hth, wp_large_nodeMetaBits hth,
      wp_large_keysWordBits hth, wp_large_valsWordBits hth, wp_large_w hth] at hsIdx hu ⊢
    have hidx := sliceNodeIdx_lt hsIdx hu
    have htot_le := totalBTreeNodesWhp_le_n_max hth
    first
    | exact henv.fits_of_le_n_max (hidx.le.trans htot_le)
    | exact henv.btMeta_safe hidx
    | exact henv.btKeys_safe hidx
    | exact henv.btVals_safe hidx

/-- Write `(metaWord, (keysWord, valsWord)) = d.2` to node `u = d.1.2` in slice `sIdx = d.1.1.2`. -/
@[expose] def writeBTreeNodeGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((((cp, base), sIdx), u), (mW, (kW, vW))) => do
    let idx ← pure (sIdx * wpNSlice cp + u)
    writePackedGenProg ((((base, wpOffBtMeta cp),
      (wpNodeMetaBits cp, wpW cp)), idx), mW)
    writePackedGenProg ((((base, wpOffBtKeys cp),
      (wpKeysWordBits cp, wpW cp)), idx), kW)
    writePackedGenProg ((((base, wpOffBtVals cp),
      (wpValsWordBits cp, wpW cp)), idx), vW)

theorem memoryCost_writeBTreeNodeGenProg
    (d : (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (writeBTreeNodeGenProg d) s = 12 := rfl

theorem writeBTreeNodeGenProg_spec {c U V w n_max base sIdx u : ℕ} {nd : BTreeNode}
    {s : Memory.State} (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max) (hu : u < nSliceWhp n_max)
    (hm_lt : nd.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk_lt : nd.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv_lt : nd.valsWord < 2 ^ valsWordBitsWhp n_max) :
    let prog := writeBTreeNodeGenProg
      ((((mkWhpCoreParams c U V w n_max, base), sIdx), u),
        (nd.metaWord, (nd.keysWord, nd.valsWord)))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ sl : BTreeSlice, sl.alloc ≤ nSliceWhp n_max →
      (∀ v < sl.alloc, v ≠ u →
        let idx_v := sIdx * nSliceWhp n_max + v
        readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem idx_v =
          (sl.nodes v).metaWord ∧
        readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem idx_v =
          (sl.nodes v).keysWord ∧
        readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem idx_v =
          (sl.nodes v).valsWord) →
      ∀ v < sl.alloc,
        let idx_v := sIdx * nSliceWhp n_max + v
        let nd_v := Function.update sl.nodes u nd v
        readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s'.mem idx_v =
          nd_v.metaWord ∧
        readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s'.mem idx_v =
          nd_v.keysWord ∧
        readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s'.mem idx_v =
          nd_v.valsWord) ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl',
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl' s'.mem) ∧
    (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hnm_le : nodeMetaBitsWhp n_max ≤ w := by
    have h1 := log_ge_mul_ell hth
    have h2 := one_le_logLogFactor n_max
    have h3 := henv.log_lt_w
    unfold nodeMetaBitsWhp; omega
  have hkw_le : keysWordBitsWhp n_max ≤ w := henv.keysWordBits_lt_w.le
  have hvw_le : valsWordBitsWhp n_max ≤ w := henv.valsWordBits_lt_w.le
  set idx := sIdx * nSliceWhp n_max + u
  have hidx : idx < totalBTreeNodesWhp n_max := sliceNodeIdx_lt hsIdx hu
  unfold writeBTreeNodeGenProg
  simp only [wp_large_nSlice hth, wp_large_offBtMeta hth, wp_large_offBtKeys hth,
    wp_large_offBtVals hth, wp_large_nodeMetaBits hth, wp_large_keysWordBits hth,
    wp_large_valsWordBits hth, wp_large_w hth, pure_bind]
  set mem₁ := writePacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w
    s.mem idx nd.metaWord
  set mem₂ := writePacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w
    mem₁ idx nd.keysWord
  set mem₃ := writePacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w
    mem₂ idx nd.valsWord
  have hout : ∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      mem₃ a = s.mem a := fun a ha =>
    (writePacked_outside hw _ hidx _ (by omega)).trans
      ((writePacked_outside hw _ hidx _ (by omega)).trans
        (writePacked_outside hw _ hidx _ (by omega)))
  have hrM : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w mem₃ i =
        readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w mem₁ i :=
    fun i hi =>
      (readPacked_writePacked_disjoint hw hi hidx (Or.inl (by omega))).trans
        (readPacked_writePacked_disjoint hw hi hidx (Or.inl (by omega)))
  have hrK : ∀ i < totalBTreeNodesWhp n_max,
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w mem₃ i =
        readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w mem₂ i :=
    fun i hi => readPacked_writePacked_disjoint hw hi hidx (Or.inl (by omega))
  have hnode_ne {i : ℕ} (hi : i < totalBTreeNodesWhp n_max) (hne_i : i ≠ idx) :
      readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w mem₃ i =
        readPacked (base + offBtMeta c U V w n_max) (nodeMetaBitsWhp n_max) w s.mem i ∧
      readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w mem₃ i =
        readPacked (base + offBtKeys c U V w n_max) (keysWordBitsWhp n_max) w s.mem i ∧
      readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w mem₃ i =
        readPacked (base + offBtVals c U V w n_max) (valsWordBitsWhp n_max) w s.mem i :=
    ⟨(hrM i hi).trans (readPacked_writePacked_of_ne hw s.mem hne_i _),
      (hrK i hi).trans ((readPacked_writePacked_of_ne hw mem₁ hne_i _).trans
        (readPacked_writePacked_disjoint hw hi hidx (Or.inr (by omega)))),
      (readPacked_writePacked_of_ne hw mem₂ hne_i _).trans
        ((readPacked_writePacked_disjoint hw hi hidx (Or.inr (by omega))).trans
          (readPacked_writePacked_disjoint hw hi hidx (Or.inr (by omega))))⟩
  obtain ⟨hsegM, hsegK, hsegV⟩ := btNodeSegs_le c U V w n_max base
  have hs'_eq : (Memory.spec 0).clientState s
      (writePackedGenProg
        ((((base, offBtMeta c U V w n_max), (nodeMetaBitsWhp n_max, w)), idx), nd.metaWord) >>=
        fun _ => writePackedGenProg
          ((((base, offBtKeys c U V w n_max), (keysWordBitsWhp n_max, w)), idx), nd.keysWord) >>=
          fun _ => writePackedGenProg
            ((((base, offBtVals c U V w n_max), (valsWordBitsWhp n_max, w)), idx), nd.valsWord)) =
      { mem := mem₃, frontier := s.frontier } := rfl
  rw [hs'_eq]
  refine ⟨rfl, rfl, ?_, ?_, ?_, hout⟩
  · exact validProg_bind (validProg_writePacked hw hnm_le hidx hsegM)
      (validProg_bind (validProg_writePacked hw hkw_le hidx hsegK)
        (validProg_writePacked hw hvw_le hidx hsegV))
  · intro sl ha_le hprev v hv
    have hidx_v := sliceNodeIdx_lt hsIdx (hv.trans_le ha_le)
    dsimp only
    by_cases hvu : v = u
    · subst hvu
      rw [Function.update_self, hrM _ hidx_v, hrK _ hidx_v]
      exact ⟨readPacked_writePacked_self _ _ _ s.mem idx hm_lt,
        readPacked_writePacked_self _ _ _ mem₁ idx hk_lt,
        readPacked_writePacked_self _ _ _ mem₂ idx hv_lt⟩
    · rw [Function.update_of_ne hvu]
      obtain ⟨e1, e2, e3⟩ := hnode_ne hidx_v (by dsimp only [idx]; omega)
      obtain ⟨p1, p2, p3⟩ := hprev v hv hvu
      exact ⟨e1.trans p1, e2.trans p2, e3.trans p3⟩
  · intro sIdx' hsIdx' hne sl' hrep'
    dsimp only at hrep' ⊢
    have hbm_eq : ∀ i < 16 * numBucketsWhp n_max,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem₃ i =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
      fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hout a (Or.inl (by omega))
    refine ⟨hrep'.1,
      (hbm_eq _ (by omega)).trans hrep'.2.1,
      (hbm_eq _ (by omega)).trans hrep'.2.2.1,
      fun v hv => ?_⟩
    have hv_ns : v < nSliceWhp n_max := hv.trans_le hrep'.1
    have hne_idx : sIdx' * nSliceWhp n_max + v ≠ idx := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := Nat.add_one_mul sIdx' (nSliceWhp n_max) ▸ Nat.mul_le_mul_right _ hlt
        omega
      · have := Nat.add_one_mul sIdx (nSliceWhp n_max) ▸ Nat.mul_le_mul_right _ hgt
        omega
    obtain ⟨e1, e2, e3⟩ := hnode_ne (sliceNodeIdx_lt hsIdx' hv_ns) hne_idx
    obtain ⟨p1, p2, p3⟩ := hrep'.2.2.2 v hv
    exact ⟨e1.trans p1, e2.trans p2, e3.trans p3⟩

/-- Writing an updated node `nd'` at an already-allocated index `u < sl.alloc` preserves
`BTreeSliceMemRep` for `{ sl with nodes := Function.update sl.nodes u nd' }` and frames all other
slices and non-B+-tree memory words. -/
theorem writeBTreeNodeGenProg_inPlace_sliceRep {c U V w n_max base sIdx u : ℕ}
    {sl : BTreeSlice} {nd' : BTreeNode} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hu : u < sl.alloc)
    (hm_lt : nd'.metaWord < 2 ^ nodeMetaBitsWhp n_max)
    (hk_lt : nd'.keysWord < 2 ^ keysWordBitsWhp n_max)
    (hv_lt : nd'.valsWord < 2 ^ valsWordBitsWhp n_max) :
    let prog := writeBTreeNodeGenProg
      ((((mkWhpCoreParams c U V w n_max, base), sIdx), u),
        (nd'.metaWord, (nd'.keysWord, nd'.valsWord)))
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BTreeSliceMemRep base c U V w n_max sIdx { sl with nodes := Function.update sl.nodes u nd' }
      s'.mem ∧
    (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ sIdx → ∀ sl₂,
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
      BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
    (∀ a, a < base + offBtMeta c U V w n_max ∨ base + offTrieChild0 c U V w n_max ≤ a →
      s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hoff := largeOffsetChain c U V w n_max
  obtain ⟨hwn_fr, hwn_mc, hwn_vp, hwn_up, hwn_other, hwn_out⟩ :=
    writeBTreeNodeGenProg_spec (nd := nd') henv hsIdx (hu.trans_le hrep.1) hm_lt hk_lt hv_lt
      (s := s)
  dsimp only at hwn_fr hwn_mc hwn_vp hwn_up hwn_other hwn_out ⊢
  have hbm_eq : ∀ i < 16 * numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w
        ((Memory.spec 0).clientState s
          (writeBTreeNodeGenProg
            ((((mkWhpCoreParams c U V w n_max, base), sIdx), u),
              (nd'.metaWord, (nd'.keysWord, nd'.valsWord))))).mem i =
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem i :=
    fun i hi => readPacked_congr hw (hidx := hi) fun a ⟨_, ha2⟩ => hwn_out a (Or.inl (by omega))
  exact ⟨hwn_fr, hwn_mc, hwn_vp,
    ⟨hrep.1, (hbm_eq _ (by omega)).trans hrep.2.1, (hbm_eq _ (by omega)).trans hrep.2.2.1,
      hwn_up sl hrep.1 fun v hv _ => hrep.2.2.2 v hv⟩,
    hwn_other, hwn_out⟩

theorem realizes_writeBTreeNodeGen :
    Realizes .exact writeBTreeNodeGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), sIdx), u), _) _ => WhpLargeEnvGen w cp base ∧
        sIdx < 3 * wpM cp ∧ u < wpNSlice cp)
      (fun _ _ => 0) := by
  realize [realizes_writePackedGen]
  all_goals
    rcases d with ⟨⟨⟨⟨cp, base⟩, sIdx⟩, u⟩, ⟨mW, ⟨kW, vW⟩⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx, hu⟩ := h
    have hth := henv.2.2.2.1
    simp only [wp_large_M hth, wp_large_nSlice hth, wp_large_offBtMeta hth,
      wp_large_offBtKeys hth, wp_large_offBtVals hth, wp_large_nodeMetaBits hth,
      wp_large_keysWordBits hth, wp_large_valsWordBits hth, wp_large_w hth] at hsIdx hu ⊢
    have hidx := sliceNodeIdx_lt hsIdx hu
    have htot_le := totalBTreeNodesWhp_le_n_max hth
  · exact henv.fits_of_le_n_max (hidx.le.trans htot_le)
  · exact henv.btMeta_safe hidx
  · exact henv.btKeys_safe hidx
  · exact henv.btVals_safe hidx

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

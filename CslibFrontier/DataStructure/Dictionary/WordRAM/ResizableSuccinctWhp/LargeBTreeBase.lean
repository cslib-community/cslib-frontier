/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bit-Packed SWAR B+-Tree Layout and Lookup/Delete/Update `Memory.Prog` Primitives

This module couples the pure 3-role split-only SWAR B+-tree `BTreeSlice`
(`Cslib.DataStructure.Dictionary.SuccinctWhp`) to bit-packed Word-RAM memory inside a large epoch's
metadata region (`offBktMeta`, `offBTreeMeta`, `offBTreeKeys`, `offBTreeVals`), and certifies
overflow- and underflow-free `RealizesBounded .exact` (`¬ReadsWidth`) implementations for SWAR lane
updates, parallel `swarRank`, slice reset, lookup, deletion, update, and root-split preparation.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.BTreeEpochLayout`,
  `epochBTreeLayout`, `extractBTreeSlice`, `BTreeSliceCtx`: named memory layout, pure `BTreeSlice`
  extractor, and tuple slice context.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.resetBTreeSliceBoundedProg`,
  `btreeLookupBoundedProg`, `btreeDeleteBoundedProg`, `btreeUpdateBoundedProg`: `Memory.Prog`
  primitives for slice reset, lookup, deletion, and in-place value update.

## Main results

* `valid_epochBTreeLayout`, `extractBTreeSlice_congr_entries`: layout validity and slice-entry
  frame invariance.
* `realizesBounded_resetBTreeSlice`, `resetBTreeSliceBoundedProg_spec`,
  `realizesBounded_btreeLookup`, `realizesBounded_btreeDelete`, `realizesBounded_btreeUpdate`:
  parameter-free `RealizesBounded .exact` certificates (`¬ReadsWidth`) and reset refinement.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Section 4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Finset

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: `BTreeEpochLayout`, `extractBTreeSlice`, and Frame Invariance -/

/-- Named memory layout descriptor for the `3 * numBuckets` SWAR B+-tree slices of an epoch. -/
structure BTreeEpochLayout where
  /-- Base word address of the enclosing epoch metadata region. -/
  metaBase : ℕ
  /-- Word offset of the `16 * numBuckets`-entry bucket scalar table (`ptrB` bits). -/
  offBkt : ℕ
  /-- Word offset of the `totalNodes`-entry `metaWord` array (`wMeta` bits). -/
  offMeta : ℕ
  /-- Word offset of the `totalNodes`-entry `keysWord` array (`wKeys` bits). -/
  offKeys : ℕ
  /-- Word offset of the `totalNodes`-entry `valsWord` array (`wVals` bits). -/
  offVals : ℕ
  /-- Scalar pointer width `globalPtrBits N`. -/
  ptrB : ℕ
  /-- Machine word width `w`. -/
  w : ℕ
  /-- Node metadata width `nodeMetaBitsWhp N`. -/
  wMeta : ℕ
  /-- Packed keys-word width `keysWordBitsWhp N = 2 * tMin * (fpBits + 2)`. -/
  wKeys : ℕ
  /-- Packed vals-word width `valsWordBitsWhp N = 2 * tMin * wValLane`. -/
  wVals : ℕ
  /-- Fingerprint bit-width `fpBitsWhp N`. -/
  fpBits : ℕ
  /-- Value/child lane bit-width `valLaneBitsWhp N`. -/
  wValLane : ℕ
  /-- Minimum internal branching parameter `tMinWhp N`. -/
  tMin : ℕ
  /-- Node capacity per slice `nSliceWhp N`. -/
  nSlice : ℕ
  /-- Number of buckets `numBucketsWhp N`. -/
  numBuckets : ℕ

/-- Concrete `BTreeEpochLayout` for a large epoch `(c, w, N)` at `metaBase`. -/
@[expose] def epochBTreeLayout (c w N metaBase : ℕ) : BTreeEpochLayout where
  metaBase := metaBase
  offBkt := offBktMeta c w N
  offMeta := offBTreeMeta c w N
  offKeys := offBTreeKeys c w N
  offVals := offBTreeVals c w N
  ptrB := globalPtrBits N
  w := w
  wMeta := nodeMetaBitsWhp N
  wKeys := keysWordBitsWhp N
  wVals := valsWordBitsWhp N
  fpBits := fpBitsWhp N
  wValLane := valLaneBitsWhp N
  tMin := tMinWhp N
  nSlice := nSliceWhp N
  numBuckets := numBucketsWhp N

/-- Total nodes `3 * numBuckets * nSlice` across all slices. -/
@[expose] def BTreeEpochLayout.totalNodes (L : BTreeEpochLayout) : ℕ :=
  3 * L.numBuckets * L.nSlice

/-- Static parameter and frontier-safety invariant for `BTreeEpochLayout`. -/
@[expose] def BTreeEpochLayout.Valid (L : BTreeEpochLayout) (w_mach frontier : ℕ) : Prop :=
  0 < w_mach ∧ w_mach = L.w ∧ L.ptrB ≤ w_mach ∧
  8 ≤ L.tMin ∧ 1 ≤ L.fpBits ∧ 1 ≤ L.wValLane ∧
  L.wMeta < w_mach ∧
  L.wKeys = 2 * L.tMin * (L.fpBits + 2) ∧
  L.wVals = 2 * L.tMin * L.wValLane ∧
  4 * L.tMin * (L.fpBits + 2) < w_mach ∧
  4 * L.tMin * L.wValLane < w_mach ∧
  4 * L.tMin ≤ 2 ^ L.wMeta ∧
  2 * L.tMin < 2 ^ (L.fpBits + 2) ∧
  L.nSlice < 2 ^ L.wValLane ∧
  64 ≤ L.nSlice ∧
  L.nSlice < 2 ^ L.ptrB ∧
  16 * L.numBuckets < 2 ^ w_mach ∧
  L.totalNodes < 2 ^ w_mach ∧
  L.offBkt + packedWords (16 * L.numBuckets) L.ptrB L.w ≤ L.offMeta ∧
  L.offMeta + packedWords L.totalNodes L.wMeta L.w ≤ L.offKeys ∧
  L.offKeys + packedWords L.totalNodes L.wKeys L.w ≤ L.offVals ∧
  L.metaBase + L.offVals + packedWords L.totalNodes L.wVals L.w ≤ frontier

/-- `epochBTreeLayout` satisfies `BTreeEpochLayout.Valid` whenever `whpThreshold c ≤ N ≤ U < 2 ^ w`
and `metaBase + epochMetaWordsWhp c w N ≤ frontier`. -/
theorem valid_epochBTreeLayout {c U w N metaBase frontier : ℕ}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hfr : metaBase + epochMetaWordsWhp c w N ≤ frontier) :
    (epochBTreeLayout c w N metaBase).Valid w frontier := by
  obtain ⟨hptr_lt, hptr_w, hlog_w, _, _, _, hnm_w, _, _, _, _, hbt_le, _, _, _, _, _, _, h8MK,
    _⟩ := largeEpoch_param_bounds hth hNU hU
  have h8 := eight_le_tMinWhp hth
  have hell := Dynamic.one_le_logLogFactor N
  have hL2 := two_le_slabScale N
  have ht_L := tMinWhp_le_slabScale N
  have h4key := (four_mul_tMin_mul_keyLane_lt_log hth).trans hlog_w
  have hval_lt_key : valLaneBitsWhp N < keyLaneBitsWhp N := by
    unfold valLaneBitsWhp keyLaneBitsWhp fpBitsWhp; omega
  have h4val : 4 * tMinWhp N * valLaneBitsWhp N < w :=
    (Nat.mul_le_mul_left _ hval_lt_key.le).trans_lt h4key
  have hmeta_cap : 4 * tMinWhp N ≤ 2 ^ nodeMetaBitsWhp N := by
    calc 4 * tMinWhp N ≤ 4 * slabScale N := Nat.mul_le_mul_left 4 ht_L
      _ = 2 ^ 2 * 2 ^ Dynamic.logLogFactor N := rfl
      _ = 2 ^ (Dynamic.logLogFactor N + 2) := by rw [← Nat.pow_add, add_comm]
      _ ≤ 2 ^ nodeMetaBitsWhp N := by
          unfold nodeMetaBitsWhp; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hkey_cap : 2 * tMinWhp N < 2 ^ (fpBitsWhp N + 2) := by
    have hpow : slabScale N ≤ 2 ^ fpBitsWhp N := by
      unfold slabScale fpBitsWhp; exact Nat.pow_le_pow_right (by decide) (by omega)
    have hfp_pos : 0 < 2 ^ fpBitsWhp N := Nat.two_pow_pos _
    calc 2 * tMinWhp N ≤ 2 * 2 ^ fpBitsWhp N := Nat.mul_le_mul_left 2 (ht_L.trans hpow)
      _ < 4 * 2 ^ fpBitsWhp N := by omega
      _ = 2 ^ (fpBitsWhp N + 2) := by rw [Nat.pow_add]; ring
  have hns_val : nSliceWhp N < 2 ^ valLaneBitsWhp N := by
    have hL12 : 4096 ≤ slabScale N ^ 12 := by
      calc 4096 = 2 ^ 12 := by decide
        _ ≤ slabScale N ^ 12 := Nat.pow_le_pow_left hL2 12
    have hdiv_le : 32 * slabScale N ^ 12 / (tMinWhp N - 1) ≤ 32 * slabScale N ^ 12 :=
      Nat.div_le_self _ _
    unfold nSliceWhp; rw [two_pow_valLaneBitsWhp]; omega
  have hM_pos : 1 ≤ numBucketsWhp N := Nat.one_le_two_pow
  have hns_le_N : nSliceWhp N ≤ N := by
    have : 1 * nSliceWhp N ≤ 3 * numBucketsWhp N * nSliceWhp N :=
      Nat.mul_le_mul_right _ (by omega)
    unfold totalBTreeNodesWhp at hbt_le; omega
  have h16M_le_N : 16 * numBucketsWhp N ≤ N := by
    have hK4 : 4 ≤ slabSizeWhp N := by
      unfold slabSizeWhp
      calc 4 = 2 ^ 2 := by decide
        _ ≤ slabScale N ^ 2 := Nat.pow_le_pow_left hL2 2
    nlinarith
  have hN_w : N < 2 ^ w := lt_of_le_of_lt hNU hU
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
  refine ⟨by omega, rfl, hptr_w, h8,
    by dsimp only [epochBTreeLayout]; unfold fpBitsWhp; omega,
    by dsimp only [epochBTreeLayout]; unfold valLaneBitsWhp; omega,
    hnm_w, rfl, rfl, h4key, h4val, hmeta_cap, hkey_cap, hns_val, sixty_four_le_nSliceWhp N,
    lt_of_le_of_lt hns_le_N hptr_lt, lt_of_le_of_lt h16M_le_N hN_w,
    lt_of_le_of_lt hbt_le hN_w, ?_, ?_, ?_, ?_⟩
  · dsimp only [epochBTreeLayout, offBTreeMeta, offTailOwner, offSlabOwner, offTailDir, offSlabDir]
    omega
  · dsimp only [epochBTreeLayout, BTreeEpochLayout.totalNodes, totalBTreeNodesWhp, offBTreeKeys]
    omega
  · dsimp only [epochBTreeLayout, BTreeEpochLayout.totalNodes, totalBTreeNodesWhp, offBTreeVals]
    omega
  · dsimp only [epochBTreeLayout, BTreeEpochLayout.totalNodes, totalBTreeNodesWhp]
    unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
      totalBTreeNodesWhp at hend
    omega

private theorem BTreeEpochLayout.Valid.six_le_w {L : BTreeEpochLayout} {w fr : ℕ}
    (hv : L.Valid w fr) : 6 ≤ w := by
  have h8 := hv.2.2.2.1
  have h4k := hv.2.2.2.2.2.2.2.2.2.1
  nlinarith

private theorem fits_hMaxBTree {w : ℕ} (hw : 6 ≤ w) : Fits w hMaxBTree := by
  rw [Fits, hMaxBTree_eq]
  exact (by decide : 42 < 2 ^ 6).trans_le (Nat.pow_le_pow_right (by decide) hw)

private theorem metaWord_shiftRight_bound {mw wm w : ℕ}
    (hw : 2 ≤ w) (hwm : wm < w) (hmw : mw < 2 ^ wm) :
    mw >>> 1 + 1 < 2 ^ w ∧ 2 * (mw >>> 1 + 1) < 2 ^ w ∧
      1 + 2 * (mw >>> 1 + 1) < 2 ^ w := by
  have h1 : mw < 2 ^ (w - 1) := hmw.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by
    conv_lhs => rw [show w - 1 = (w - 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have hpow2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    conv_lhs => rw [show w = (w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have h2pos : 2 ≤ 2 ^ (w - 1) :=
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.shiftRight_eq_div_pow, pow_one]
  omega

/-- Pure extraction of slice `(b, role)` (`b < numBuckets`, `role < 3`) from bit-packed memory. -/
@[expose] def extractBTreeSlice (L : BTreeEpochLayout) (b role : ℕ) (mem : ℕ → ℕ) :
    BTreeSlice where
  alloc := readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem (16 * b + 6 + 2 * role)
  root := readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem (16 * b + 7 + 2 * role)
  nodes := fun u =>
    if u < L.nSlice then
      let idx := (3 * b + role) * L.nSlice + u
      ⟨readPacked (L.metaBase + L.offMeta) L.wMeta L.w mem idx,
       readPacked (L.metaBase + L.offKeys) L.wKeys L.w mem idx,
       readPacked (L.metaBase + L.offVals) L.wVals L.w mem idx⟩
    else
      ⟨0, 0, 0⟩

/-- Word-interval predicate for the four packed arrays touched by SWAR B+-tree operations. -/
@[expose] def BTreeEpochLayout.OwnsAddr (L : BTreeEpochLayout) (addr : ℕ) : Prop :=
  (L.metaBase + L.offBkt ≤ addr ∧
    addr < L.metaBase + L.offBkt + packedWords (16 * L.numBuckets) L.ptrB L.w) ∨
  (L.metaBase + L.offMeta ≤ addr ∧
    addr < L.metaBase + L.offMeta + packedWords L.totalNodes L.wMeta L.w) ∨
  (L.metaBase + L.offKeys ≤ addr ∧
    addr < L.metaBase + L.offKeys + packedWords L.totalNodes L.wKeys L.w) ∨
  (L.metaBase + L.offVals ≤ addr ∧
    addr < L.metaBase + L.offVals + packedWords L.totalNodes L.wVals L.w)

/-- Frame invariance of `extractBTreeSlice L b role` when memory agrees on `L`'s `alloc`/`root`
entries and `(b, role)`'s `nSlice` node entries. -/
theorem extractBTreeSlice_congr_entries {L : BTreeEpochLayout} {b role : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (ha : readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem₁ (16 * b + 6 + 2 * role) =
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem₂ (16 * b + 6 + 2 * role))
    (hr : readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem₁ (16 * b + 7 + 2 * role) =
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem₂ (16 * b + 7 + 2 * role))
    (hnd : ∀ u < L.nSlice,
      let idx := (3 * b + role) * L.nSlice + u
      readPacked (L.metaBase + L.offMeta) L.wMeta L.w mem₁ idx =
        readPacked (L.metaBase + L.offMeta) L.wMeta L.w mem₂ idx ∧
      readPacked (L.metaBase + L.offKeys) L.wKeys L.w mem₁ idx =
        readPacked (L.metaBase + L.offKeys) L.wKeys L.w mem₂ idx ∧
      readPacked (L.metaBase + L.offVals) L.wVals L.w mem₁ idx =
        readPacked (L.metaBase + L.offVals) L.wVals L.w mem₂ idx) :
    extractBTreeSlice L b role mem₁ = extractBTreeSlice L b role mem₂ := by
  unfold extractBTreeSlice
  congr 1
  ext u
  by_cases hu : u < L.nSlice
  · obtain ⟨hm, hk, hv⟩ := hnd u hu
    simp [hu, hm, hk, hv]
  · simp [hu]

/-- Writing a node `nd` at `u < L.nSlice` of `(b, role)` updates `(extractBTreeSlice L b role)`
nodes by `Function.update`, preserves all other `(b', role') ≠ (b, role)` slices and `offBkt`,
and modifies only node-array words. -/
private theorem extractBTreeSlice_writeNode {L : BTreeEpochLayout} {mem : ℕ → ℕ}
    {b role u : ℕ} {nd : BTreeNode} {frontier : ℕ}
    (hvL : L.Valid L.w frontier)
    (hb : b < L.numBuckets) (hrole : role < 3) (hu : u < L.nSlice)
    (hmeta : nd.metaWord < 2 ^ L.wMeta)
    (hkeys : nd.keysWord < 2 ^ L.wKeys)
    (hvals : nd.valsWord < 2 ^ L.wVals) :
    let idx := (3 * b + role) * L.nSlice + u
    let m1 := writePacked (L.metaBase + L.offMeta) L.wMeta L.w mem idx nd.metaWord
    let m2 := writePacked (L.metaBase + L.offKeys) L.wKeys L.w m1 idx nd.keysWord
    let m3 := writePacked (L.metaBase + L.offVals) L.wVals L.w m2 idx nd.valsWord
    extractBTreeSlice L b role m3 =
      { (extractBTreeSlice L b role mem) with
        nodes := Function.update (extractBTreeSlice L b role mem).nodes u nd } ∧
    (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice L b' role' m3 = extractBTreeSlice L b' role' mem) ∧
    (∀ slot < 16 * L.numBuckets,
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w m3 slot =
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem slot) ∧
    (∀ addr, ¬L.OwnsAddr addr → m3 addr = mem addr) := by
  intro idx m1 m2 m3
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, _, h64, _, _, _, hd0, hd1, hd2, _⟩ := hvL
  have hidx_tot : idx < L.totalNodes := by
    dsimp only [idx, BTreeEpochLayout.totalNodes]
    have hbr : 3 * b + role + 1 ≤ 3 * L.numBuckets := by omega
    calc (3 * b + role) * L.nSlice + u
        < (3 * b + role) * L.nSlice + L.nSlice := Nat.add_lt_add_left hu _
      _ = (3 * b + role + 1) * L.nSlice := by ring
      _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul_right _ hbr
  have hout1 : ∀ addr, ¬(L.metaBase + L.offMeta ≤ addr ∧
      addr < L.metaBase + L.offMeta + packedWords L.totalNodes L.wMeta L.w) →
      m1 addr = mem addr := fun addr ha => writePacked_outside hw mem hidx_tot _ ha
  have hout2 : ∀ addr, ¬(L.metaBase + L.offKeys ≤ addr ∧
      addr < L.metaBase + L.offKeys + packedWords L.totalNodes L.wKeys L.w) →
      m2 addr = m1 addr := fun addr ha => writePacked_outside hw m1 hidx_tot _ ha
  have hout3 : ∀ addr, ¬(L.metaBase + L.offVals ≤ addr ∧
      addr < L.metaBase + L.offVals + packedWords L.totalNodes L.wVals L.w) →
      m3 addr = m2 addr := fun addr ha => writePacked_outside hw m2 hidx_tot _ ha
  have hbkt_eq : ∀ slot < 16 * L.numBuckets,
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w m3 slot =
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem slot := fun slot hs =>
    readPacked_congr hw (fun addr ha => by
      rw [hout3 addr (by omega), hout2 addr (by omega), hout1 addr (by omega)]) hs
  have hm_read : ∀ j < L.totalNodes,
      readPacked (L.metaBase + L.offMeta) L.wMeta L.w m3 j =
        if j = idx then nd.metaWord else readPacked (L.metaBase + L.offMeta) L.wMeta L.w mem j := by
    intro j hj
    have h31 : readPacked (L.metaBase + L.offMeta) L.wMeta L.w m3 j =
        readPacked (L.metaBase + L.offMeta) L.wMeta L.w m1 j :=
      readPacked_congr hw (fun addr ha => by rw [hout3 addr (by omega), hout2 addr (by omega)]) hj
    rw [h31]
    by_cases hje : j = idx
    · subst hje; simp [m1, readPacked_writePacked_self _ _ _ mem idx hmeta]
    · simp [hje, m1, readPacked_writePacked_of_ne hw mem hje]
  have hk_read : ∀ j < L.totalNodes,
      readPacked (L.metaBase + L.offKeys) L.wKeys L.w m3 j =
        if j = idx then nd.keysWord else readPacked (L.metaBase + L.offKeys) L.wKeys L.w mem j := by
    intro j hj
    have h32 : readPacked (L.metaBase + L.offKeys) L.wKeys L.w m3 j =
        readPacked (L.metaBase + L.offKeys) L.wKeys L.w m2 j :=
      readPacked_congr hw (fun addr ha => hout3 addr (by omega)) hj
    have h10 : readPacked (L.metaBase + L.offKeys) L.wKeys L.w m1 j =
        readPacked (L.metaBase + L.offKeys) L.wKeys L.w mem j :=
      readPacked_congr hw (fun addr ha => hout1 addr (by omega)) hj
    rw [h32]
    by_cases hje : j = idx
    · subst hje; simp [m2, readPacked_writePacked_self _ _ _ m1 idx hkeys]
    · simp [hje, m2, readPacked_writePacked_of_ne hw m1 hje, h10]
  have hv_read : ∀ j < L.totalNodes,
      readPacked (L.metaBase + L.offVals) L.wVals L.w m3 j =
        if j = idx then nd.valsWord else readPacked (L.metaBase + L.offVals) L.wVals L.w mem j := by
    intro j hj
    have h20 : readPacked (L.metaBase + L.offVals) L.wVals L.w m2 j =
        readPacked (L.metaBase + L.offVals) L.wVals L.w mem j :=
      readPacked_congr hw (fun addr ha => by rw [hout2 addr (by omega), hout1 addr (by omega)]) hj
    by_cases hje : j = idx
    · subst hje; simp [m3, readPacked_writePacked_self _ _ _ m2 idx hvals]
    · simp [hje, m3, readPacked_writePacked_of_ne hw m2 hje, h20]
  refine ⟨?_, ?_, hbkt_eq, fun addr ha => ?_⟩
  · unfold extractBTreeSlice
    have ha_self := hbkt_eq (16 * b + 6 + 2 * role) (by omega)
    have hr_self := hbkt_eq (16 * b + 7 + 2 * role) (by omega)
    congr 1
    ext u'
    by_cases hue : u' = u
    · subst hue
      simp only [hu, ↓reduceIte, Function.update_self]
      rw [hm_read idx hidx_tot, hk_read idx hidx_tot, hv_read idx hidx_tot]
      simp [idx]
    · simp only [Function.update_of_ne hue]
      by_cases hu' : u' < L.nSlice
      · have hj_tot : (3 * b + role) * L.nSlice + u' < L.totalNodes := by
          dsimp only [BTreeEpochLayout.totalNodes]
          have hbr : 3 * b + role + 1 ≤ 3 * L.numBuckets := by omega
          calc (3 * b + role) * L.nSlice + u'
              < (3 * b + role + 1) * L.nSlice := by ring_nf; omega
            _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul_right _ hbr
        have hne_j : (3 * b + role) * L.nSlice + u' ≠ idx := by dsimp [idx]; omega
        simp [hu', hm_read _ hj_tot, hk_read _ hj_tot, hv_read _ hj_tot, hne_j]
      · simp [hu']
  · intro b' role' hb' hrole' hne_br
    refine extractBTreeSlice_congr_entries
      (hbkt_eq _ (by omega)) (hbkt_eq _ (by omega)) fun u' hu' => ?_
    dsimp only
    have hj_tot : (3 * b' + role') * L.nSlice + u' < L.totalNodes := by
      dsimp only [BTreeEpochLayout.totalNodes]
      have hbr : 3 * b' + role' + 1 ≤ 3 * L.numBuckets := by omega
      calc (3 * b' + role') * L.nSlice + u'
          < (3 * b' + role' + 1) * L.nSlice := by ring_nf; omega
        _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul_right _ hbr
    have hbr_ne : 3 * b' + role' ≠ 3 * b + role := by omega
    have hne_j : (3 * b' + role') * L.nSlice + u' ≠ idx := by
      intro heq
      have hns_pos : 0 < L.nSlice := by omega
      have hd_l : ((3 * b' + role') * L.nSlice + u') / L.nSlice = 3 * b' + role' := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hns_pos, Nat.div_eq_of_lt hu', zero_add]
      have hd_r : idx / L.nSlice = 3 * b + role := by
        dsimp only [idx]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hns_pos, Nat.div_eq_of_lt hu, zero_add]
      exact hbr_ne (by rw [← hd_l, heq, hd_r])
    simp [hm_read _ hj_tot, hk_read _ hj_tot, hv_read _ hj_tot, hne_j]
  · rw [hout3 addr (fun h => ha (Or.inr (Or.inr (Or.inr h)))),
      hout2 addr (fun h => ha (Or.inr (Or.inr (Or.inl h)))),
      hout1 addr (fun h => ha (Or.inr (Or.inl h)))]

/-- Writing `alloc` or `root` (`isRoot < 2`) of `(b, role)` updates `(extractBTreeSlice L b role)`
and leaves all other slices and non-`(6 + 2 * role + isRoot)` bucket slots unchanged. -/
private theorem extractBTreeSlice_writeHdr {L : BTreeEpochLayout} {mem : ℕ → ℕ}
    {b role isRoot val frontier : ℕ}
    (hvL : L.Valid L.w frontier)
    (hb : b < L.numBuckets) (hrole : role < 3) (his : isRoot < 2) (hval : val < 2 ^ L.ptrB) :
    let slot := 16 * b + 6 + 2 * role + isRoot
    let mem' := writePacked (L.metaBase + L.offBkt) L.ptrB L.w mem slot val
    extractBTreeSlice L b role mem' =
      (if isRoot = 0 then { (extractBTreeSlice L b role mem) with alloc := val }
       else { (extractBTreeSlice L b role mem) with root := val }) ∧
    (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice L b' role' mem' = extractBTreeSlice L b' role' mem) ∧
    (∀ slot' < 16 * L.numBuckets, slot' ≠ slot →
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem' slot' =
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w mem slot') ∧
    (∀ addr, ¬L.OwnsAddr addr → mem' addr = mem addr) := by
  intro slot mem'
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hd0, hd1, hd2, _⟩ := hvL
  have hslot_lt : slot < 16 * L.numBuckets := by dsimp [slot]; omega
  have houtB : ∀ addr, ¬(L.metaBase + L.offBkt ≤ addr ∧
      addr < L.metaBase + L.offBkt + packedWords (16 * L.numBuckets) L.ptrB L.w) →
      mem' addr = mem addr := fun addr ha => writePacked_outside hw mem hslot_lt val ha
  have hnd_eq : ∀ j < L.totalNodes,
      readPacked (L.metaBase + L.offMeta) L.wMeta L.w mem' j =
        readPacked (L.metaBase + L.offMeta) L.wMeta L.w mem j ∧
      readPacked (L.metaBase + L.offKeys) L.wKeys L.w mem' j =
        readPacked (L.metaBase + L.offKeys) L.wKeys L.w mem j ∧
      readPacked (L.metaBase + L.offVals) L.wVals L.w mem' j =
        readPacked (L.metaBase + L.offVals) L.wVals L.w mem j := fun j hj =>
    ⟨readPacked_congr hw (fun addr ha => houtB addr (by omega)) hj,
     readPacked_congr hw (fun addr ha => houtB addr (by omega)) hj,
     readPacked_congr hw (fun addr ha => houtB addr (by omega)) hj⟩
  have hnodes_slice : ∀ b' role', b' < L.numBuckets → role' < 3 →
      (extractBTreeSlice L b' role' mem').nodes = (extractBTreeSlice L b' role' mem).nodes := by
    intro b' role' hb' hr'
    ext u'
    dsimp only [extractBTreeSlice]
    by_cases hu' : u' < L.nSlice
    · have hj_tot : (3 * b' + role') * L.nSlice + u' < L.totalNodes := by
        dsimp only [BTreeEpochLayout.totalNodes]
        have hbr : 3 * b' + role' + 1 ≤ 3 * L.numBuckets := by omega
        calc (3 * b' + role') * L.nSlice + u'
            < (3 * b' + role' + 1) * L.nSlice := by ring_nf; omega
          _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul_right _ hbr
      obtain ⟨e1, e2, e3⟩ := hnd_eq _ hj_tot
      simp [hu', e1, e2, e3]
    · simp [hu']
  refine ⟨?_, ?_, fun s' _ hne => readPacked_writePacked_of_ne hw mem hne val,
    fun addr ha => houtB addr fun h => ha (Or.inl h)⟩
  · have hnd_self := hnodes_slice b role hb hrole
    rcases isRoot with _ | _ | _ <;> try omega
    · simp only [↓reduceIte]
      have ha_s : (extractBTreeSlice L b role mem').alloc = val := by
        dsimp only [extractBTreeSlice, mem', slot]
        simpa only [Nat.add_zero] using readPacked_writePacked_self _ _ _ mem _ hval
      have hr_s : (extractBTreeSlice L b role mem').root =
          (extractBTreeSlice L b role mem).root :=
        readPacked_writePacked_of_ne hw mem (by dsimp [slot]; omega) val
      dsimp only [extractBTreeSlice] at ha_s hr_s hnd_self ⊢
      congr 1
    · simp only [Nat.succ_ne_zero, ↓reduceIte]
      have ha_s : (extractBTreeSlice L b role mem').alloc =
          (extractBTreeSlice L b role mem).alloc :=
        readPacked_writePacked_of_ne hw mem (by dsimp [slot]; omega) val
      have hr_s : (extractBTreeSlice L b role mem').root = val := by
        dsimp only [extractBTreeSlice, mem', slot]
        have heq_s : 16 * b + 6 + 2 * role + 1 = 16 * b + 7 + 2 * role := by omega
        rw [heq_s]
        exact readPacked_writePacked_self _ _ _ mem _ hval
      dsimp only [extractBTreeSlice] at ha_s hr_s hnd_self ⊢
      congr 1
  · intro b' role' hb' hrole' hne_br
    refine extractBTreeSlice_congr_entries
      (readPacked_writePacked_of_ne hw mem (by dsimp [slot]; omega) val)
      (readPacked_writePacked_of_ne hw mem (by dsimp [slot]; omega) val) fun u' hu' => ?_
    have hj_tot : (3 * b' + role') * L.nSlice + u' < L.totalNodes := by
      dsimp only [BTreeEpochLayout.totalNodes]
      have hbr : 3 * b' + role' + 1 ≤ 3 * L.numBuckets := by omega
      calc (3 * b' + role') * L.nSlice + u'
          < (3 * b' + role' + 1) * L.nSlice := by ring_nf; omega
        _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul_right _ hbr
    exact hnd_eq _ hj_tot

/-! ## Section 2: Overflow- and Underflow-Free SWAR Lane and Rank `Memory.Prog` Primitives -/

private def laneGetBoundedProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, word), j) => do
    let sh ← pure (j * W)
    let mask ← pure ((1 <<< W) - 1)
    pure ((word >>> sh) &&& mask)

private def LaneGetPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((W, _word), j), _s => W < w ∧ j * W < 2 ^ w

private theorem realizesBounded_laneGet :
    RealizesBounded .exact laneGetBoundedProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      LaneGetPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨W, word⟩, j⟩
    obtain ⟨hW, hjW⟩ := h
    try dsimp only [Fits] at *
    try simp only [Nat.shiftLeft_eq 1, one_mul] at *
    have hpow_W : 2 ^ W < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hW)
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow_W
  all_goals exact hjW

@[simp] private theorem clientResult_laneGetBoundedProg (W word j : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (laneGetBoundedProg ((W, word), j)) = laneGet W word j := by
  simp [laneGetBoundedProg, laneGet, Nat.shiftLeft_eq]

@[simp] private theorem runClient_state_laneGetBoundedProg
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (laneGetBoundedProg d))) = s := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

@[simp] private theorem memoryCost_laneGetBoundedProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (laneGetBoundedProg d) s = 0 := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

private def wordTakeLowBoundedProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, j), word) => do
    let sh ← pure (j * W)
    let mask ← pure ((1 <<< sh) - 1)
    pure (word &&& mask)

private def WordTakeDropPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((W, j), _word), _s => j * W < w

private theorem realizesBounded_wordTakeLow :
    RealizesBounded .exact wordTakeLowBoundedProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      WordTakeDropPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨W, j⟩, word⟩
    have hjW : j * W < w := h
    try dsimp only [Fits] at *
    try simp only [Nat.shiftLeft_eq 1, one_mul] at *
    have hpow : 2 ^ (j * W) < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hjW
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self)
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow
  all_goals omega

@[simp] private theorem clientResult_wordTakeLowBoundedProg (W j word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordTakeLowBoundedProg ((W, j), word)) =
      wordTakeLow W j word := by
  simp [wordTakeLowBoundedProg, wordTakeLow, Nat.shiftLeft_eq]

@[simp] private theorem runClient_state_wordTakeLowBoundedProg
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (wordTakeLowBoundedProg d))) = s := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

@[simp] private theorem memoryCost_wordTakeLowBoundedProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordTakeLowBoundedProg d) s = 0 := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

private def wordDropLowBoundedProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, j), word) => do
    let sh ← pure (j * W)
    pure (word >>> sh)

private theorem realizesBounded_wordDropLow :
    RealizesBounded .exact wordDropLowBoundedProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      WordTakeDropPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨W, j⟩, word⟩
    have hjW : j * W < w := h
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    dsimp only [Fits] at *
    exact hjW.trans hw_lt)

@[simp] private theorem clientResult_wordDropLowBoundedProg (W j word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordDropLowBoundedProg ((W, j), word)) =
      wordDropLow W j word := rfl

@[simp] private theorem runClient_state_wordDropLowBoundedProg
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (wordDropLowBoundedProg d))) = s := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

@[simp] private theorem memoryCost_wordDropLowBoundedProg (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordDropLowBoundedProg d) s = 0 := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

private def wordInsertAtBoundedProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((W, j), v), word) => do
    let low ← wordTakeLowBoundedProg ((W, j), word)
    let drop ← wordDropLowBoundedProg ((W, j), word)
    let sh ← pure (j * W)
    let hi1 ← pure (v + (drop <<< W))
    let hi2 ← pure (hi1 <<< sh)
    pure (low + hi2)

private def WordInsertAtPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((W, j), v), word), _s =>
    ∃ cap, j ≤ cap ∧ (cap + 1) * W < w ∧ v < 2 ^ W ∧ word < 2 ^ (cap * W)

private theorem realizesBounded_wordInsertAt :
    RealizesBounded .exact wordInsertAtBoundedProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      WordInsertAtPre (fun _ _ => 0) := by
  have htk := realizesBounded_wordTakeLow
  have hdr := realizesBounded_wordDropLow
  realize
  all_goals (
    rcases d with ⟨⟨⟨W, j⟩, v⟩, word⟩
    obtain ⟨cap, hj, hcapW, hv, hword⟩ := h
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, clientResult_wordTakeLowBoundedProg,
      runClient_state_wordTakeLowBoundedProg, clientResult_wordDropLowBoundedProg] at *
    have hjW_lt : j * W < w := by
      have : j * W ≤ (cap + 1) * W := Nat.mul_le_mul_right W (by omega)
      omega
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hdrop : wordDropLow W j word < 2 ^ ((cap - j) * W) :=
      wordDropLow_lt (by rwa [Nat.add_sub_cancel' hj])
    have hhi1_lt : v + (wordDropLow W j word <<< W) < 2 ^ ((cap - j + 1) * W) := by
      rw [Nat.shiftLeft_eq]
      have hle : wordDropLow W j word + 1 ≤ 2 ^ ((cap - j) * W) := hdrop
      calc v + wordDropLow W j word * 2 ^ W
          < (wordDropLow W j word + 1) * 2 ^ W := by ring_nf; omega
        _ ≤ 2 ^ ((cap - j) * W) * 2 ^ W := Nat.mul_le_mul_right _ hle
        _ = 2 ^ ((cap - j + 1) * W) := by rw [← Nat.pow_add, Nat.add_one_mul]
    have hpow_cap : 2 ^ ((cap + 1) * W) < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hcapW
    have hpow_sub : 2 ^ ((cap - j + 1) * W) ≤ 2 ^ ((cap + 1) * W) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right W (by omega))
    have hins_lt : wordInsertAt W j v word < 2 ^ ((cap + 1) * W) :=
      wordInsertAt_lt hj hv hword)
  all_goals try exact hjW_lt
  all_goals try exact hjW_lt.trans hw_lt
  all_goals try exact hhi1_lt.trans_le (hpow_sub.trans hpow_cap.le)
  all_goals try (
    have hle_ins : ((v + (wordDropLow W j word <<< W)) <<< (j * W)) ≤ wordInsertAt W j v word :=
      Nat.le_add_left _ _
    exact hle_ins.trans_lt (hins_lt.trans hpow_cap))
  all_goals exact hins_lt.trans hpow_cap

@[simp] private theorem clientResult_wordInsertAtBoundedProg (W j v word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordInsertAtBoundedProg (((W, j), v), word)) =
      wordInsertAt W j v word := by
  simp [wordInsertAtBoundedProg, wordInsertAt]

@[simp] private theorem runClient_state_wordInsertAtBoundedProg
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (wordInsertAtBoundedProg d))) = s := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl

@[simp] private theorem memoryCost_wordInsertAtBoundedProg
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordInsertAtBoundedProg d) s = 0 := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl

private def wordDeleteAtBoundedProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((W, j), word) => do
    let low ← wordTakeLowBoundedProg ((W, j), word)
    let sh0 ← pure (j * W)
    let sh1 ← pure ((j + 1) * W)
    let hi ← pure ((word >>> sh1) <<< sh0)
    pure (low + hi)

private def WordDeleteAtPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((W, j), word), _s =>
    ∃ cap, 1 ≤ W ∧ j ≤ cap ∧ (cap + 1) * W < w ∧ word < 2 ^ ((cap + 1) * W)

private theorem realizesBounded_wordDeleteAt :
    RealizesBounded .exact wordDeleteAtBoundedProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      WordDeleteAtPre (fun _ _ => 0) := by
  have htk := realizesBounded_wordTakeLow
  realize
  all_goals (
    rcases d with ⟨⟨W, j⟩, word⟩
    obtain ⟨cap, hW1, hj, hcapW, hword⟩ := h
    try dsimp only [Fits] at *
    try simp only [clientResult_wordTakeLowBoundedProg] at *
    have hj1W_lt : (j + 1) * W < w :=
      (Nat.mul_le_mul_right W (by omega)).trans_lt hcapW
    have hjW_lt : j * W < w := (Nat.mul_le_mul_right W (by omega)).trans_lt hj1W_lt
    have hj1_lt_w : j + 1 < w := by
      have : (j + 1) * 1 ≤ (j + 1) * W := Nat.mul_le_mul_left (j + 1) hW1
      omega
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hdel_lt : wordDeleteAt W j word < 2 ^ (cap * W) := wordDeleteAt_lt hj hword
    have hpow_w : 2 ^ (cap * W) < 2 ^ w :=
      Nat.pow_lt_pow_right Nat.one_lt_two
        ((Nat.mul_le_mul_right W (by omega)).trans_lt hcapW))
  all_goals try exact hjW_lt
  all_goals try exact hj1_lt_w.trans hw_lt
  all_goals try exact hjW_lt.trans hw_lt
  all_goals try exact hj1W_lt.trans hw_lt
  all_goals try (
    have hle : ((word >>> ((j + 1) * W)) <<< (j * W)) ≤ wordDeleteAt W j word :=
      Nat.le_add_left _ _
    exact hle.trans_lt (hdel_lt.trans hpow_w))
  all_goals exact hdel_lt.trans hpow_w

@[simp] private theorem clientResult_wordDeleteAtBoundedProg (W j word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordDeleteAtBoundedProg ((W, j), word)) =
      wordDeleteAt W j word := by
  simp [wordDeleteAtBoundedProg, wordDeleteAt]

@[simp] private theorem runClient_state_wordDeleteAtBoundedProg
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (wordDeleteAtBoundedProg d))) = s := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

@[simp] private theorem memoryCost_wordDeleteAtBoundedProg
    (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordDeleteAtBoundedProg d) s = 0 := by
  rcases d with ⟨⟨_, _⟩, _⟩; rfl

private def wordUpdateAtBoundedProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((W, j), v), word) => do
    let d ← wordDeleteAtBoundedProg ((W, j), word)
    wordInsertAtBoundedProg (((W, j), v), d)

private def WordUpdateAtPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((W, j), v), word), _s =>
    ∃ cap, 1 ≤ W ∧ j ≤ cap ∧ (cap + 1) * W < w ∧ v < 2 ^ W ∧ word < 2 ^ ((cap + 1) * W)

private theorem realizesBounded_wordUpdateAt :
    RealizesBounded .exact wordUpdateAtBoundedProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      WordUpdateAtPre (fun _ _ => 0) := by
  have hdel := realizesBounded_wordDeleteAt
  have hins := realizesBounded_wordInsertAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨W, j⟩, v⟩, word⟩
    obtain ⟨cap, hW1, hj, hcapW, hv, hword⟩ := h
    try simp only [StateTransitionSpec.clientState, clientResult_wordDeleteAtBoundedProg,
      runClient_state_wordDeleteAtBoundedProg] at *)
  · exact ⟨cap, hW1, hj, hcapW, hword⟩
  · exact ⟨cap, hj, hcapW, hv, wordDeleteAt_lt hj hword⟩

@[simp] private theorem clientResult_wordUpdateAtBoundedProg (W j v word : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (wordUpdateAtBoundedProg (((W, j), v), word)) =
      wordUpdateAt W j v word := by
  simp only [wordUpdateAtBoundedProg, prog_clientResult_bind,
    runClient_state_wordDeleteAtBoundedProg, clientResult_wordDeleteAtBoundedProg,
    clientResult_wordInsertAtBoundedProg]
  unfold wordUpdateAt wordInsertAt wordDeleteAt
  have hlow : wordTakeLow W j (wordTakeLow W j word + ((word >>> ((j + 1) * W)) <<< (j * W))) =
      wordTakeLow W j word := by
    rw [wordTakeLow_eq_mod, wordTakeLow_eq_mod, Nat.shiftLeft_eq,
      Nat.add_mul_mod_self_right, Nat.mod_mod]
  have hdrop : wordDropLow W j (wordTakeLow W j word + ((word >>> ((j + 1) * W)) <<< (j * W))) =
      word >>> ((j + 1) * W) := by
    rw [wordDropLow_eq_div, Nat.shiftLeft_eq, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (wordTakeLow_lt W j word), Nat.zero_add]
  rw [hlow, hdrop]

@[simp] private theorem runClient_state_wordUpdateAtBoundedProg
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (wordUpdateAtBoundedProg d))) = s := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl

@[simp] private theorem memoryCost_wordUpdateAtBoundedProg
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (wordUpdateAtBoundedProg d) s = 0 := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩; rfl

private def swarOnesBoundedProg : ℕ × ℕ → Memory.Prog ℕ
  | (W, n) => do
    let sh ← pure (n * W)
    let num ← pure ((1 <<< sh) - 1)
    let den ← pure ((1 <<< W) - 1)
    pure (num / den)

private def SwarOnesPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (W, n), _s => 2 ≤ W ∧ W < w ∧ n * W < w

private theorem realizesBounded_swarOnes :
    RealizesBounded .exact swarOnesBoundedProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      SwarOnesPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨W, n⟩
    obtain ⟨hW2, hWw, hnW⟩ := h
    try dsimp only [Fits] at *
    try simp only [Nat.shiftLeft_eq 1, one_mul] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow_nW : 2 ^ (n * W) < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hnW
    have hpow_W : 2 ^ W < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two hWw
    have hW_ge4 : 4 ≤ 2 ^ W := by
      calc 4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW2)
  all_goals try exact hnW.trans hw_lt
  all_goals try exact Nat.one_le_two_pow
  all_goals try exact hpow_nW
  all_goals try exact hpow_W
  all_goals omega

@[simp] private theorem clientResult_swarOnesBoundedProg (W n : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (swarOnesBoundedProg (W, n)) = swarOnes W n := by
  simp [swarOnesBoundedProg, swarOnes, Nat.shiftLeft_eq]

@[simp] private theorem runClient_state_swarOnesBoundedProg (d : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (swarOnesBoundedProg d))) = s := by
  rcases d with ⟨_, _⟩; rfl

@[simp] private theorem memoryCost_swarOnesBoundedProg (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (swarOnesBoundedProg d) s = 0 := by
  rcases d with ⟨_, _⟩; rfl

/-- Borrow-free `ltMask` in `Memory.Prog` using `subClampProg`. -/
private def ltMaskBoundedProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((fpBits, m), (q, keysWord)) => do
    let W ← pure (fpBits + 2)
    let onesM ← swarOnesBoundedProg (W, m)
    let qBiased ← pure ((1 <<< fpBits) + q)
    let lhs ← pure (qBiased * onesM)
    let rhs ← pure (keysWord + onesM)
    let diff ← subClampProg (lhs, rhs)
    pure ((diff >>> fpBits) &&& onesM)

private def LtMaskPre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((fpBits, m), (q, keysWord)), _s =>
    ∃ cap, m < cap ∧ 2 * cap * (fpBits + 2) < w ∧ q < 2 ^ fpBits ∧
      keysWord < 2 ^ (cap * (fpBits + 2))

private theorem realizesBounded_ltMask :
    RealizesBounded .exact ltMaskBoundedProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      LtMaskPre (fun _ _ => 0) := by
  have hso := realizesBounded_swarOnes
  have hsc := realizesBounded_subClamp
  realize
  all_goals (
    rcases d with ⟨⟨fpBits, m⟩, ⟨q, keysWord⟩⟩
    obtain ⟨cap, hm_cap, h2cap, hq, hkw⟩ := h
    try dsimp only [Fits] at *
    try simp only [Nat.shiftLeft_eq 1, one_mul, clientResult_swarOnesBoundedProg] at *
    set W := fpBits + 2
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hcap1 : 1 ≤ cap := by omega
    have hWw : W < w := by
      calc W = 1 * W := (one_mul W).symm
        _ ≤ (2 * cap) * W := Nat.mul_le_mul_right W (by omega)
        _ < w := h2cap
    have hfp_w : fpBits < w := by dsimp [W] at hWw; omega
    have hmW : m * W < w := (Nat.mul_le_mul_right W (by omega)).trans_lt h2cap
    have hones_lt : swarOnes W m < 2 ^ (m * W) := by
      unfold swarOnes
      exact (Nat.div_le_self _ _).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one)
    have hqb_lt : 2 ^ fpBits + q < 2 ^ W := by
      dsimp only [W]; rw [Nat.pow_add]
      have : 0 < 2 ^ fpBits := Nat.two_pow_pos fpBits
      omega
    have hlhs_lt : (2 ^ fpBits + q) * swarOnes W m < 2 ^ (cap * W) := by
      calc (2 ^ fpBits + q) * swarOnes W m
          < 2 ^ W * 2 ^ (m * W) := Nat.mul_lt_mul'' hqb_lt hones_lt
        _ = 2 ^ ((m + 1) * W) := by rw [← Nat.pow_add, Nat.add_one_mul, add_comm]
        _ ≤ 2 ^ (cap * W) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right W hm_cap)
    have hcapW_pos : 1 ≤ cap * W := Nat.mul_pos hcap1 (by dsimp [W]; omega)
    have hpow_cap_lt : 2 ^ (cap * W + 1) ≤ 2 ^ (2 * cap * W) :=
      Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_assoc]; omega)
    have hpow_2cap_w : 2 ^ (2 * cap * W) < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two h2cap
    have hrhs_lt : keysWord + swarOnes W m < 2 ^ (cap * W + 1) := by
      have hm_le : 2 ^ (m * W) ≤ 2 ^ (cap * W) :=
        Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right W hm_cap.le)
      rw [Nat.pow_succ]; omega)
  all_goals try exact hWw.trans hw_lt
  all_goals try (unfold SwarOnesPre; exact ⟨by dsimp [W]; omega, hWw, hmW⟩)
  all_goals try exact hqb_lt.trans (Nat.pow_lt_pow_right Nat.one_lt_two hWw)
  all_goals try (
    exact hlhs_lt.trans_le
      ((Nat.pow_le_pow_right (by decide) (Nat.le_succ _)).trans (hpow_cap_lt.trans hpow_2cap_w.le)))
  all_goals exact hrhs_lt.trans_le (hpow_cap_lt.trans hpow_2cap_w.le)

@[simp] private theorem clientResult_ltMaskBoundedProg (fpBits m q kw : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (ltMaskBoundedProg ((fpBits, m), (q, kw))) =
      ltMask fpBits m q kw := by
  simp [ltMaskBoundedProg, ltMask, Nat.shiftLeft_eq]

@[simp] private theorem runClient_state_ltMaskBoundedProg
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (ltMaskBoundedProg d))) = s := by
  rcases d with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold ltMaskBoundedProg; simp

@[simp] private theorem memoryCost_ltMaskBoundedProg
    (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (ltMaskBoundedProg d) s = 0 := by
  rcases d with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold ltMaskBoundedProg; simp

private theorem mul_three_bounds {tm x w : ℕ} (htm : 2 ≤ tm) (hx : 1 ≤ x)
    (h4 : 4 * tm * x < w) :
    x < w ∧ 2 * x < w ∧ 2 * tm < w ∧ 4 * tm < w ∧
    (tm - 1) * x < w ∧ tm * x < w ∧ (2 * tm - 1) * x < w ∧
    2 * tm * x < w ∧ (2 * tm + 1) * x < w := by
  have h4tm : 4 * tm < w := by
    calc 4 * tm = 4 * tm * 1 := (mul_one _).symm
      _ ≤ 4 * tm * x := Nat.mul_le_mul_left (4 * tm) hx
      _ < w := h4
  have h2x : 2 * x < w :=
    (Nat.mul_le_mul_right x (by omega : 2 ≤ 4 * tm)).trans_lt h4
  refine ⟨by omega, h2x, by omega, h4tm, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (Nat.mul_le_mul_right x (by omega)).trans_lt h4

private theorem idx_mul_lt_of_four_mul {r tm x w : ℕ} (hr : r ≤ 2 * tm)
    (h4 : 4 * tm * x < w) : r * x < w :=
  (Nat.mul_le_mul_right x (by omega : r ≤ 4 * tm)).trans_lt h4

private def swarRankInnerProg : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((fpBits, tMin), m_c), (q, keysWord)) => do
    let cap ← pure (2 * tMin)
    let maxM ← pure (cap - 1)
    let W ← pure (fpBits + 2)
    let ltM ← ltMaskBoundedProg ((fpBits, m_c), (q, keysWord))
    let onesCap ← swarOnesBoundedProg (W, cap)
    let prod ← pure (ltM * onesCap)
    let r_raw ← laneGetBoundedProg ((W, prod), maxM)
    if r_raw < cap then pure r_raw else pure maxM

private def SwarRankInnerPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((fpBits, tMin), m_c), (q, keysWord)), _s =>
    2 ≤ tMin ∧ m_c < 2 * tMin ∧ 4 * tMin * (fpBits + 2) < w ∧ q < 2 ^ fpBits ∧
      keysWord < 2 ^ (2 * tMin * (fpBits + 2))

private theorem ltMask_mul_swarOnes_lt {fpBits tMin m' q kw w : ℕ}
    (hm' : m' < 2 * tMin) (h4t : 4 * tMin * (fpBits + 2) < w) :
    ltMask fpBits m' q kw * swarOnes (fpBits + 2) (2 * tMin) < 2 ^ w := by
  set W := fpBits + 2
  have hltM_lt : ltMask fpBits m' q kw < 2 ^ (m' * W) := by
    unfold ltMask swarOnes
    exact Nat.and_le_right.trans_lt
      ((Nat.div_le_self _ _).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one))
  have hcap_lt : swarOnes W (2 * tMin) < 2 ^ (2 * tMin * W) := by
    unfold swarOnes
    exact (Nat.div_le_self _ _).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one)
  have hprod_lt : ltMask fpBits m' q kw * swarOnes W (2 * tMin) < 2 ^ (4 * tMin * W) := by
    calc _ < 2 ^ (m' * W) * 2 ^ (2 * tMin * W) := Nat.mul_lt_mul'' hltM_lt hcap_lt
      _ = 2 ^ ((m' + 2 * tMin) * W) := by rw [← Nat.pow_add, Nat.add_mul]
      _ ≤ 2 ^ (4 * tMin * W) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right W (by omega))
  exact hprod_lt.trans (Nat.pow_lt_pow_right Nat.one_lt_two h4t)

private theorem realizesBounded_swarRankInner :
    RealizesBounded .exact swarRankInnerProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      SwarRankInnerPre (fun _ _ => 0) := by
  have hlt := realizesBounded_ltMask
  have hso := realizesBounded_swarOnes
  have hlg := realizesBounded_laneGet
  realize
  all_goals (
    rcases d with ⟨⟨⟨fpBits, tMin⟩, m_c⟩, ⟨q, keysWord⟩⟩
    obtain ⟨ht2, hmc, h4t, hq, hkw⟩ := h
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, clientResult_ltMaskBoundedProg,
      runClient_state_ltMaskBoundedProg, clientResult_swarOnesBoundedProg,
      runClient_state_swarOnesBoundedProg] at *
    set W := fpBits + 2
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    obtain ⟨hWw, _, h2t_w, _, _, _, h2tm1_W, h2tm_W, _⟩ :=
      mul_three_bounds ht2 (by dsimp [W]; omega) h4t
    have h2_lt : 2 < 2 ^ w := (by omega : 2 < w).trans hw_lt
    have h2t_fits : 2 * tMin < 2 ^ w := h2t_w.trans hw_lt
    have hW_fits : W < 2 ^ w := hWw.trans hw_lt)
  all_goals try omega
  all_goals try (unfold LtMaskPre; exact ⟨2 * tMin, hmc, by rw [← Nat.mul_assoc]; exact h4t,
    hq, hkw⟩)
  all_goals try (unfold SwarOnesPre; exact ⟨by dsimp [W]; omega, hWw, h2tm_W⟩)
  all_goals try exact ltMask_mul_swarOnes_lt hmc h4t
  all_goals (unfold LaneGetPre; exact ⟨hWw, h2tm1_W.trans hw_lt⟩)

/-- Clamped SWAR rank returning `min (swarRank fpBits (2 * tMin) (min m (2 * tMin - 1)) q kw)
(2 * tMin - 1)`, which is `< 2 * tMin` unconditionally and equals `swarRank` on every valid node. -/
private def swarRankClampedProg : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((fpBits, tMin), m), (q, keysWord)) => do
    let cap ← pure (2 * tMin)
    let maxM ← pure (cap - 1)
    if m < cap then
      swarRankInnerProg (((fpBits, tMin), m), (q, keysWord))
    else
      swarRankInnerProg (((fpBits, tMin), maxM), (q, keysWord))

private def SwarRankClampedPre (w : ℕ) : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | (((fpBits, tMin), _m), (q, keysWord)), _s =>
    2 ≤ tMin ∧ 4 * tMin * (fpBits + 2) < w ∧ q < 2 ^ fpBits ∧
      keysWord < 2 ^ (2 * tMin * (fpBits + 2))

private theorem realizesBounded_swarRankClamped :
    RealizesBounded .exact swarRankClampedProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      SwarRankClampedPre (fun _ _ => 0) := by
  have hin := realizesBounded_swarRankInner
  realize
  all_goals (
    rcases d with ⟨⟨⟨fpBits, tMin⟩, m⟩, ⟨q, keysWord⟩⟩
    obtain ⟨ht2, h4t, hq, hkw⟩ := h
    try dsimp only at *
    try dsimp only [Fits] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    obtain ⟨_, _, h2t_w, _⟩ := mul_three_bounds ht2 (by omega) h4t
    have h2_lt : 2 < 2 ^ w := (by omega : 2 < w).trans hw_lt
    have h2t_fits : 2 * tMin < 2 ^ w := h2t_w.trans hw_lt)
  all_goals try omega
  all_goals (unfold SwarRankInnerPre; exact ⟨ht2, by omega, h4t, hq, hkw⟩)

private theorem swarRankClampedProg_lt {fpBits tMin m q kw : ℕ} (ht : 1 ≤ tMin) (s : Memory.State) :
    (Memory.spec 0).clientResult s (swarRankClampedProg (((fpBits, tMin), m), (q, kw))) <
      2 * tMin := by
  unfold swarRankClampedProg swarRankInnerProg
  simp only [pure_bind]
  split_ifs with hmc <;>
    simp only [prog_clientResult_bind, StateTransitionSpec.clientState,
      runClient_state_ltMaskBoundedProg, runClient_state_swarOnesBoundedProg,
      runClient_state_laneGetBoundedProg] <;>
    (split_ifs with hr
     · simpa only [prog_clientResult_pure] using hr
     · simp only [prog_clientResult_pure]; omega)

private theorem swarRankClampedProg_eq_swarRank {fpBits tMin m q kw : ℕ}
    (hm : m < 2 * tMin) (hcap : 2 * tMin < 2 ^ (fpBits + 2))
    (hq : q < 2 ^ fpBits) (hkw : kw < 2 ^ (m * (fpBits + 2)))
    (hlanes : ∀ j < m, laneGet (fpBits + 2) kw j < 2 ^ fpBits) (s : Memory.State) :
    (Memory.spec 0).clientResult s (swarRankClampedProg (((fpBits, tMin), m), (q, kw))) =
      swarRank fpBits (2 * tMin) m q kw ∧
    swarRank fpBits (2 * tMin) m q kw ≤ m := by
  have hcnt := swarRank_eq_count_lt hm hcap hq hkw hlanes
  have hr_le : swarRank fpBits (2 * tMin) m q kw ≤ m := by
    rw [hcnt]
    exact (card_filter_le _ _).trans (by rw [card_range])
  have hr_lt : swarRank fpBits (2 * tMin) m q kw < 2 * tMin := hr_le.trans_lt hm
  refine ⟨?_, hr_le⟩
  unfold swarRankClampedProg swarRankInnerProg
  simp only [pure_bind, hm, ↓reduceIte, prog_clientResult_bind,
    StateTransitionSpec.clientState, runClient_state_ltMaskBoundedProg,
    clientResult_ltMaskBoundedProg, runClient_state_swarOnesBoundedProg,
    clientResult_swarOnesBoundedProg, runClient_state_laneGetBoundedProg,
    clientResult_laneGetBoundedProg]
  have hrank_def : laneGet (fpBits + 2)
      (ltMask fpBits m q kw * swarOnes (fpBits + 2) (2 * tMin)) (2 * tMin - 1) =
      swarRank fpBits (2 * tMin) m q kw := rfl
  rw [hrank_def, ite_eq_left hr_lt, prog_clientResult_pure]

@[simp] private theorem runClient_state_swarRankClampedProg
    (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (swarRankClampedProg d))) = s := by
  rcases d with ⟨⟨⟨fpBits, tMin⟩, m⟩, ⟨q, kw⟩⟩
  unfold swarRankClampedProg swarRankInnerProg
  simp only [pure_bind]
  split_ifs <;>
    simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
      runClient_state_ltMaskBoundedProg, runClient_state_swarOnesBoundedProg,
      runClient_state_laneGetBoundedProg] <;>
    split_ifs <;> rfl

@[simp] private theorem memoryCost_swarRankClampedProg
    (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (swarRankClampedProg d) s = 0 := by
  rcases d with ⟨⟨⟨fpBits, tMin⟩, m⟩, ⟨q, kw⟩⟩
  unfold swarRankClampedProg swarRankInnerProg
  simp only [pure_bind]
  split_ifs <;>
    simp only [Realization.memoryCost_bind', StateTransitionSpec.clientState,
      memoryCost_ltMaskBoundedProg, runClient_state_ltMaskBoundedProg,
      memoryCost_swarOnesBoundedProg, runClient_state_swarOnesBoundedProg,
      memoryCost_laneGetBoundedProg, runClient_state_laneGetBoundedProg, zero_add] <;>
    split_ifs <;> rfl

/-! ## Section 3: `BTreeSlice` Node Read/Write and Tree Operations in `Memory.Prog` -/

/-- Tuple context for a single `(b, role)` slice:
`((((mb, ob), (om, ok, ov)), ((pb, wv), (wm, wk, wvl))), (((fp, wvL), (tm, ns)), (nb, br)))`
where `nb = numBuckets` and `br = (b, role)`. -/
abbrev BTreeSliceCtx :=
  (((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) ×
    (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)))

/-- Pack `(L, b, role)` into `BTreeSliceCtx`. -/
@[expose] def BTreeEpochLayout.toSliceCtx (L : BTreeEpochLayout) (b role : ℕ) : BTreeSliceCtx :=
  ((((L.metaBase, L.offBkt), (L.offMeta, (L.offKeys, L.offVals))),
    ((L.ptrB, L.w), (L.wMeta, (L.wKeys, L.wVals)))),
   (((L.fpBits, L.wValLane), (L.tMin, L.nSlice)), (L.numBuckets, (b, role))))

/-- Unpack `BTreeSliceCtx` to `(L, b, role)`. -/
@[expose] def unpackSliceCtx : BTreeSliceCtx → BTreeEpochLayout × (ℕ × ℕ)
  | ((((mb, ob), (om, (ok, ov))), ((pb, wv), (wm, (wk, wvl)))),
     (((fp, wvL), (tm, ns)), (nb, (b, role)))) =>
    (⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩, (b, role))

@[simp] theorem unpackSliceCtx_toSliceCtx (L : BTreeEpochLayout) (b role : ℕ) :
    unpackSliceCtx (L.toSliceCtx b role) = (L, (b, role)) := by
  cases L; rfl

/-- Precondition certifying valid `BTreeEpochLayout` and `(b < numBuckets, role < 3)`. -/
@[expose] def BTreeSlicePre (w : ℕ) (ctx : BTreeSliceCtx) (s : Memory.State) : Prop :=
  match unpackSliceCtx ctx with
  | (L, (b, role)) => L.Valid w s.frontier ∧ b < L.numBuckets ∧ role < 3

/-- Slim header context `(((mb, ob), (pb, wv)), hdrBase)` (5 words) for `(alloc, root)`. -/
private abbrev SliceHdrCtx := ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- Slim node-array context `((((mb, om), (ok, ov)), ((wv, wm), (wk, wvl))), (ns, nodeBase))`
(10 words, depth 4) for `(metaWord, keysWord, valsWord)` reads and writes. -/
private abbrev SliceNodeCtx := (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) × (ℕ × ℕ)

/-- Slim split-parameter context `((fp, wvL), tm)` (3 words). -/
private abbrev SplitParams := (ℕ × ℕ) × ℕ

private abbrev ctxMbOb (c : BTreeSliceCtx) : ℕ × ℕ := c.1.1.1
private abbrev ctxPbWv (c : BTreeSliceCtx) : ℕ × ℕ := c.1.2.1
private abbrev ctxMb (c : BTreeSliceCtx) : ℕ := c.1.1.1.1
private abbrev ctxOm (c : BTreeSliceCtx) : ℕ := c.1.1.2.1
private abbrev ctxOkOv (c : BTreeSliceCtx) : ℕ × ℕ := c.1.1.2.2
private abbrev ctxWv (c : BTreeSliceCtx) : ℕ := c.1.2.1.2
private abbrev ctxWm (c : BTreeSliceCtx) : ℕ := c.1.2.2.1
private abbrev ctxWkWvl (c : BTreeSliceCtx) : ℕ × ℕ := c.1.2.2.2
private abbrev ctxFpWvL (c : BTreeSliceCtx) : ℕ × ℕ := c.2.1.1
private abbrev ctxFp (c : BTreeSliceCtx) : ℕ := c.2.1.1.1
private abbrev ctxWvL (c : BTreeSliceCtx) : ℕ := c.2.1.1.2
private abbrev ctxTm (c : BTreeSliceCtx) : ℕ := c.2.1.2.1
private abbrev ctxNs (c : BTreeSliceCtx) : ℕ := c.2.1.2.2
private abbrev ctxB (c : BTreeSliceCtx) : ℕ := c.2.2.2.1
private abbrev ctxRole (c : BTreeSliceCtx) : ℕ := c.2.2.2.2

private abbrev ctxHdrAt (c : BTreeSliceCtx) (hdrBase : ℕ) : SliceHdrCtx :=
  ((ctxMbOb c, ctxPbWv c), hdrBase)

private abbrev ctxNodeAt (c : BTreeSliceCtx) (nodeBase : ℕ) : SliceNodeCtx :=
  ((((ctxMb c, ctxOm c), ctxOkOv c), ((ctxWv c, ctxWm c), ctxWkWvl c)), (ctxNs c, nodeBase))

private abbrev ctxSplitParams (c : BTreeSliceCtx) : SplitParams :=
  (ctxFpWvL c, ctxTm c)

private def BTreeEpochLayout.toHdrCtx (L : BTreeEpochLayout) (b role : ℕ) : SliceHdrCtx :=
  (((L.metaBase, L.offBkt), (L.ptrB, L.w)), 16 * b + 6 + 2 * role)

private def BTreeEpochLayout.toNodeCtx (L : BTreeEpochLayout) (b role : ℕ) :
    SliceNodeCtx :=
  ((((L.metaBase, L.offMeta), (L.offKeys, L.offVals)),
    ((L.w, L.wMeta), (L.wKeys, L.wVals))),
   (L.nSlice, (3 * b + role) * L.nSlice))

private theorem extractBTreeSlice_node_bounds (L : BTreeEpochLayout) (b role u : ℕ)
    (mem : ℕ → ℕ) :
    let nd := (extractBTreeSlice L b role mem).nodes u
    nd.metaWord < 2 ^ L.wMeta ∧ nd.keysWord < 2 ^ L.wKeys ∧ nd.valsWord < 2 ^ L.wVals := by
  dsimp only [extractBTreeSlice]
  by_cases hu : u < L.nSlice
  · simp only [hu, ↓reduceIte]
    exact ⟨readPacked_lt _ _ _ _ _, readPacked_lt _ _ _ _ _, readPacked_lt _ _ _ _ _⟩
  · simp only [hu, ↓reduceIte]
    exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _⟩

private def SliceHdrPre (w : ℕ) : SliceHdrCtx → ℕ → Prop
  | (((mb, ob), (pb, wv)), hdrBase), frontier =>
    ∃ cap, 6 ≤ w ∧ w = wv ∧ pb ≤ w ∧ hdrBase + 1 < cap ∧ cap < 2 ^ w ∧
      mb + ob + packedWords cap pb wv ≤ frontier

private def SliceNodePre (w : ℕ) : SliceNodeCtx → ℕ → Prop
  | ((((mb, om), (ok, ov)), ((wv, wm), (wk, wvl))), (ns, nodeBase)), frontier =>
    ∃ tot, 6 ≤ w ∧ w = wv ∧ 1 ≤ ns ∧ wm ≤ w ∧ wk ≤ w ∧ wvl ≤ w ∧
      nodeBase + ns ≤ tot ∧ tot < 2 ^ w ∧
      mb + om + packedWords tot wm wv ≤ frontier ∧
      mb + ok + packedWords tot wk wv ≤ frontier ∧
      mb + ov + packedWords tot wvl wv ≤ frontier

private def SplitParamsPre (w : ℕ) : SplitParams → Prop
  | ((fp, wvL), tm) => 6 ≤ w ∧ 8 ≤ tm ∧ 4 * tm * (fp + 2) < w ∧ 4 * tm * wvL < w

private theorem BTreeEpochLayout.Valid.hdr_facts {L : BTreeEpochLayout} {w fr b role : ℕ}
    (hv : L.Valid w fr) (hb : b < L.numBuckets) (hrole : role < 3) :
    Fits w 16 ∧ Fits w 6 ∧ Fits w 2 ∧ Fits w 1 ∧ Fits w 0 ∧
    Fits w (16 * b) ∧ Fits w (16 * b + 6) ∧ Fits w (2 * role) ∧
    Fits w (16 * b + 6 + 2 * role) ∧
    SliceHdrPre w (L.toHdrCtx b role) fr := by
  have hw6 := hv.six_le_w
  dsimp only [BTreeEpochLayout.Valid] at hv
  obtain ⟨_, hwv, hpb, _, _, _, _, _, _, _, _, _, _, _, _, _, h16b, _, hd0, hd1, hd2, hfr⟩ := hv
  have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
  have hsl1 : 16 * b + 6 + 2 * role + 1 < 16 * L.numBuckets := by omega
  have hsl_w : 16 * b + 6 + 2 * role + 1 < 2 ^ w := hsl1.trans h16b
  dsimp only [Fits, BTreeEpochLayout.toHdrCtx, SliceHdrPre]
  refine ⟨by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega,
    ⟨16 * L.numBuckets, hw6, hwv, hpb, hsl1, h16b, by omega⟩⟩

private theorem BTreeEpochLayout.Valid.node_facts {L : BTreeEpochLayout} {w fr b role : ℕ}
    (hv : L.Valid w fr) (hb : b < L.numBuckets) (hrole : role < 3) :
    Fits w 3 ∧ Fits w 2 ∧ Fits w 1 ∧ Fits w 0 ∧
    Fits w (3 * b) ∧ Fits w (3 * b + role) ∧ Fits w ((3 * b + role) * L.nSlice) ∧
    SliceNodePre w (L.toNodeCtx b role) fr := by
  have hw6 := hv.six_le_w
  dsimp only [BTreeEpochLayout.Valid] at hv
  obtain ⟨_, hwv, _, _, _, _, hwm, hwk, hwvl, h4k, h4v, _, _, _, h64, _, _, htot,
    _, hd1, hd2, hfr⟩ := hv
  dsimp only [BTreeEpochLayout.totalNodes] at htot hd1 hd2 hfr
  have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
  have hbr : 3 * b + role + 1 ≤ 3 * L.numBuckets := by omega
  have hnb_tot : (3 * b + role) * L.nSlice + L.nSlice ≤ 3 * L.numBuckets * L.nSlice := by
    calc (3 * b + role) * L.nSlice + L.nSlice = (3 * b + role + 1) * L.nSlice := by ring
      _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul_right _ hbr
  have hbr_tot : 3 * b + role < 3 * L.numBuckets * L.nSlice := by
    calc 3 * b + role < (3 * b + role + 1) * 1 := by omega
      _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul hbr (by omega)
  have hbr_w : 3 * b + role < 2 ^ w := hbr_tot.trans htot
  have hnb_w : (3 * b + role) * L.nSlice < 2 ^ w :=
    (by omega : (3 * b + role) * L.nSlice < (3 * b + role) * L.nSlice + L.nSlice).trans
      (lt_of_le_of_lt hnb_tot htot)
  dsimp only [Fits, BTreeEpochLayout.toNodeCtx, SliceNodePre]
  refine ⟨by omega, by omega, by omega, by omega, by omega, hbr_w, hnb_w,
    ⟨3 * L.numBuckets * L.nSlice, hw6, hwv, by omega, hwm.le,
      by rw [hwk]; nlinarith, by rw [hwvl]; nlinarith, hnb_tot, htot,
      by omega, by omega, hfr⟩⟩

private theorem BTreeEpochLayout.Valid.split_facts {L : BTreeEpochLayout} {w fr : ℕ}
    (hv : L.Valid w fr) : SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) := by
  have hw6 := hv.six_le_w
  dsimp only [BTreeEpochLayout.Valid] at hv
  exact ⟨hw6, hv.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Read node `u` of `(b, role)` via `SliceNodeCtx` (11 words). Always issues packed reads so loop
bodies starting with `readSliceNodeAtProg` satisfy `1 ≤ memoryCost`. -/
private def readSliceNodeAtProg : SliceNodeCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (((((mb, om), (ok, ov)), ((wv, wm), (wk, wvl))), (ns, nodeBase)), u) =>
    if u < ns then do
      let idx ← pure (nodeBase + u)
      let mw ← readPackedCompGenProg (((mb, om), (wm, wv)), idx)
      let kw ← readPackedCompGenProg (((mb, ok), (wk, wv)), idx)
      let vw ← readPackedCompGenProg (((mb, ov), (wvl, wv)), idx)
      pure (mw, (kw, vw))
    else do
      let _ ← readPackedCompGenProg (((mb, om), (wm, wv)), nodeBase)
      pure (0, (0, 0))

private theorem realizesBounded_readSliceNodeAt :
    RealizesBounded .exact readSliceNodeAtProg
      (WordEncoding.encode (α := SliceNodeCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (nctx, _) s => SliceNodePre w nctx s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, om⟩, ⟨ok, ov⟩⟩, ⟨⟨wv, wm⟩, ⟨wk, wvl⟩⟩⟩, ⟨ns, nodeBase⟩⟩, u⟩
    obtain ⟨tot, hw6, rfl, hns1, hwm, hwk, hwvl, hnb_tot, htot, hfr1, hfr2, hfr3⟩ := h
    try dsimp only at *
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg] at *
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6)
  all_goals try omega
  all_goals try (
    have hidx : nodeBase + u < tot := by omega
    unfold ReadPackedCompPre
    exact ⟨tot, by omega, rfl, by assumption, hidx, by assumption⟩)
  all_goals (
    have hidx0 : nodeBase < tot := by omega
    unfold ReadPackedCompPre
    exact ⟨tot, by omega, rfl, hwm, hidx0, hfr1⟩)

@[simp] private theorem runClient_state_readSliceNodeAtProg
    (d : SliceNodeCtx × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readSliceNodeAtProg d))) = s := by
  rcases d with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨ns, _⟩⟩, u⟩
  unfold readSliceNodeAtProg
  dsimp only
  by_cases hu : u < ns <;> simp [hu]

private theorem readSliceNodeAtProg_spec (L : BTreeEpochLayout) (b role u : ℕ) (s : Memory.State) :
    let nd := (extractBTreeSlice L b role s.mem).nodes u
    (Memory.spec 0).clientResult s (readSliceNodeAtProg (L.toNodeCtx b role, u)) =
      (nd.metaWord, (nd.keysWord, nd.valsWord)) ∧
    (Memory.spec 0).clientState s (readSliceNodeAtProg (L.toNodeCtx b role, u)) = s ∧
    memoryCost (readSliceNodeAtProg (L.toNodeCtx b role, u)) s ≤ 6 := by
  unfold readSliceNodeAtProg extractBTreeSlice
  dsimp only [BTreeEpochLayout.toNodeCtx]
  by_cases hu : u < L.nSlice
  · refine ⟨by simp [hu], ?_, by simp [hu]⟩
    unfold StateTransitionSpec.clientState; simp [hu]
  · refine ⟨by simp [hu], ?_, by simp [hu]⟩
    unfold StateTransitionSpec.clientState; simp [hu]

/-- Write `(metaWord, (keysWord, valsWord))` at node `u` via `SliceNodeCtx` (14 words). -/
private def writeSliceNodeAtProg : (SliceNodeCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((((((mb, om), (ok, ov)), ((wv, wm), (wk, wvl))), (ns, nodeBase)), u), (mw, (kw, vw))) =>
    if u < ns then do
      let idx ← pure (nodeBase + u)
      writePackedCompGenProg ((((mb, om), (wm, wv)), idx), mw)
      writePackedCompGenProg ((((mb, ok), (wk, wv)), idx), kw)
      writePackedCompGenProg ((((mb, ov), (wvl, wv)), idx), vw)
    else pure ()

private theorem realizesBounded_writeSliceNodeAt :
    RealizesBounded .exact writeSliceNodeAtProg
      (WordEncoding.encode (α := (SliceNodeCtx × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((nctx, _), _) s => SliceNodePre w nctx s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, om⟩, ⟨ok, ov⟩⟩, ⟨⟨wv, wm⟩, ⟨wk, wvl⟩⟩⟩, ⟨ns, nodeBase⟩⟩, u⟩,
      ⟨mw, ⟨kw, vw⟩⟩⟩
    obtain ⟨tot, hw6, rfl, hns1, hwm, hwk, hwvl, hnb_tot, htot, hfr1, hfr2, hfr3⟩ := h
    try dsimp only at *
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_writePackedCompGenProg] at *
    have hidx : nodeBase + u < tot := by omega)
  all_goals try exact hidx.trans htot
  all_goals (
    unfold WritePackedCompPre
    refine ⟨tot, by omega, rfl, by assumption, hidx, ?_⟩
    (try dsimp only); assumption)

@[simp] private theorem runClient_frontier_writeSliceNodeAtProg
    (d : (SliceNodeCtx × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (writeSliceNodeAtProg d)))).frontier =
      s.frontier := by
  rcases d with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨ns, _⟩⟩, u⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold writeSliceNodeAtProg
  dsimp only
  by_cases hu : u < ns <;> simp [hu]

/-- Write two nodes `(u1, nd1)` and `(u2, nd2)` sequentially via `SliceNodeCtx` (18 words). -/
private def writeTwoNodesAtProg :
    SliceNodeCtx × ((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))) → Memory.Prog Unit
  | (nctx, ((u1, nd1), (u2, nd2))) => do
    writeSliceNodeAtProg ((nctx, u1), nd1)
    writeSliceNodeAtProg ((nctx, u2), nd2)

private theorem realizesBounded_writeTwoNodesAt :
    RealizesBounded .exact writeTwoNodesAtProg
      (WordEncoding.encode (α := SliceNodeCtx × ((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := Unit))
      (fun w (nctx, _) s => SliceNodePre w nctx s.frontier) (fun _ _ => 0) := by
  have hwn := realizesBounded_writeSliceNodeAt
  realize
  all_goals (
    rcases d with ⟨nctx, ⟨⟨u1, nd1⟩, ⟨u2, nd2⟩⟩⟩
    try simp only [StateTransitionSpec.clientState, runClient_frontier_writeSliceNodeAtProg] at *
    exact h)

@[simp] private theorem runClient_frontier_writeTwoNodesAtProg
    (d : SliceNodeCtx × ((ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ))))) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (writeTwoNodesAtProg d)))).frontier =
      s.frontier := by
  rcases d with ⟨_, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  unfold writeTwoNodesAtProg
  simp

/-- Read `(alloc, root)` via `SliceHdrCtx` (5 words). -/
private def readSliceHdrAtProg : SliceHdrCtx → Memory.Prog (ℕ × ℕ)
  | (((mb, ob), (pb, wv)), hdrBase) => do
    let al ← readPackedCompGenProg (((mb, ob), (pb, wv)), hdrBase)
    let rt ← readPackedCompGenProg (((mb, ob), (pb, wv)), hdrBase + 1)
    pure (al, rt)

private theorem realizesBounded_readSliceHdrAt :
    RealizesBounded .exact readSliceHdrAtProg
      (WordEncoding.encode (α := SliceHdrCtx))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w hctx s => SliceHdrPre w hctx s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨mb, ob⟩, ⟨pb, wv⟩⟩, hdrBase⟩
    obtain ⟨cap, hw6, rfl, hpb, hsl, hcap, hfr⟩ := h
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readPackedCompGenProg] at *
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6)
  all_goals try exact hsl.trans hcap
  all_goals (unfold ReadPackedCompPre; exact ⟨cap, by omega, rfl, hpb, by omega, hfr⟩)

@[simp] private theorem runClient_state_readSliceHdrAtProg
    (hctx : SliceHdrCtx) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readSliceHdrAtProg hctx))) = s := by
  rcases hctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩
  unfold readSliceHdrAtProg; simp

private theorem readSliceHdrAtProg_spec (L : BTreeEpochLayout) (b role : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readSliceHdrAtProg (L.toHdrCtx b role)) =
      ((extractBTreeSlice L b role s.mem).alloc, (extractBTreeSlice L b role s.mem).root) ∧
    (Memory.spec 0).clientState s (readSliceHdrAtProg (L.toHdrCtx b role)) = s ∧
    memoryCost (readSliceHdrAtProg (L.toHdrCtx b role)) s = 4 := by
  have hslot : 16 * b + 6 + 2 * role + 1 = 16 * b + 7 + 2 * role := by omega
  unfold readSliceHdrAtProg extractBTreeSlice StateTransitionSpec.clientState
  dsimp only [BTreeEpochLayout.toHdrCtx]
  simp [hslot]

/-- Write `alloc` or `root` (`isRoot < 2`) via `SliceHdrCtx` (7 words). -/
private def writeSliceHdrAtProg : SliceHdrCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((((mb, ob), (pb, wv)), hdrBase), (isRoot, val)) =>
    if isRoot < 2 then do
      let slot ← pure (hdrBase + isRoot)
      writePackedCompGenProg ((((mb, ob), (pb, wv)), slot), val)
    else pure ()

private theorem realizesBounded_writeSliceHdrAt :
    RealizesBounded .exact writeSliceHdrAtProg
      (WordEncoding.encode (α := SliceHdrCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (hctx, _) s => SliceHdrPre w hctx s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, ob⟩, ⟨pb, wv⟩⟩, hdrBase⟩, ⟨isRoot, val⟩⟩
    obtain ⟨cap, hw6, rfl, hpb, hsl, hcap, hfr⟩ := h
    try dsimp only at *
    try dsimp only [Fits] at *
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6)
  all_goals try omega
  all_goals (
    unfold WritePackedCompPre
    exact ⟨cap, by omega, rfl, hpb, by omega, hfr⟩)

@[simp] private theorem runClient_frontier_writeSliceHdrAtProg
    (d : SliceHdrCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (writeSliceHdrAtProg d)))).frontier =
      s.frontier := by
  rcases d with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩, ⟨isRoot, _⟩⟩
  unfold writeSliceHdrAtProg
  dsimp only
  by_cases hi : isRoot < 2 <;> simp [hi]

/-- Reset `(b, role)` to `alloc = 0, root = 0` (`ValidWhpSlice N 0 _ (fun _ => none)`) in `O(1)`. -/
def resetBTreeSliceBoundedProg : BTreeSliceCtx → Memory.Prog Unit
  | ctx => do
    let hdrBase ← pure (16 * ctxB ctx + 6 + 2 * ctxRole ctx)
    writeSliceHdrAtProg (ctxHdrAt ctx hdrBase, (0, 0))
    writeSliceHdrAtProg (ctxHdrAt ctx hdrBase, (1, 0))

theorem realizesBounded_resetBTreeSlice :
    RealizesBounded .exact resetBTreeSliceBoundedProg
      (WordEncoding.encode (α := BTreeSliceCtx))
      (WordEncoding.encode (α := Unit))
      BTreeSlicePre (fun _ _ => 0) := by
  have hwh := realizesBounded_writeSliceHdrAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    dsimp only [BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨hvL, hb, hrole⟩ := h
    obtain ⟨hf16, hf6, hf2, hf1, hf0, hfb, hfb6, hfr2, hfhb, hhdr⟩ := hvL.hdr_facts hb hrole
    dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr
    try simp only [StateTransitionSpec.clientState, runClient_frontier_writeSliceHdrAtProg] at *)
  all_goals assumption

theorem resetBTreeSliceBoundedProg_spec {L : BTreeEpochLayout} {b role : ℕ} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier) (hb : b < L.numBuckets) (hrole : role < 3) (N insCount : ℕ) :
    let s' := (Memory.spec 0).clientState s (resetBTreeSliceBoundedProg (L.toSliceCtx b role))
    s'.frontier = s.frontier ∧
    memoryCost (resetBTreeSliceBoundedProg (L.toSliceCtx b role)) s = 8 ∧
    ValidWhpSlice N insCount (extractBTreeSlice L b role s'.mem) (fun _ => none) ∧
    (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice L b' role' s'.mem = extractBTreeSlice L b' role' s.mem) ∧
    (∀ slot < 16 * L.numBuckets,
      slot ≠ 16 * b + 6 + 2 * role → slot ≠ 16 * b + 7 + 2 * role →
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w s'.mem slot =
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w s.mem slot) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  obtain ⟨he1, ho1, hb1, ha1⟩ := extractBTreeSlice_writeHdr (mem := s.mem) (isRoot := 0) (val := 0)
    hvL hb hrole (by decide) (Nat.two_pow_pos _)
  set m1 := writePacked (L.metaBase + L.offBkt) L.ptrB L.w s.mem (16 * b + 6 + 2 * role + 0) 0
  obtain ⟨he2, ho2, hb2, ha2⟩ := extractBTreeSlice_writeHdr (mem := m1) (isRoot := 1) (val := 0)
    hvL hb hrole (by decide) (Nat.two_pow_pos _)
  set m2 := writePacked (L.metaBase + L.offBkt) L.ptrB L.w m1 (16 * b + 6 + 2 * role + 1) 0
  have hst : (Memory.spec 0).clientState s (resetBTreeSliceBoundedProg (L.toSliceCtx b role)) =
      ⟨m2, s.frontier⟩ := by
    unfold resetBTreeSliceBoundedProg writeSliceHdrAtProg StateTransitionSpec.clientState
    dsimp only [BTreeEpochLayout.toSliceCtx]
    simp [m1, m2]
  have hcost : memoryCost (resetBTreeSliceBoundedProg (L.toSliceCtx b role)) s = 8 := by
    unfold resetBTreeSliceBoundedProg writeSliceHdrAtProg
    dsimp only [BTreeEpochLayout.toSliceCtx]; simp
  simp only [↓reduceIte] at he1
  simp only [Nat.succ_ne_zero, ↓reduceIte] at he2
  refine ⟨by rw [hst], hcost, ?_, ?_, ?_, ?_⟩
  · rw [hst]
    have hsl_eq : extractBTreeSlice L b role m2 =
        ⟨0, 0, (extractBTreeSlice L b role s.mem).nodes⟩ := by
      dsimp only [m2, m1] at he2 he1 ⊢
      rw [he2, he1]
    rw [hsl_eq]
    exact validWhpSlice_zero N insCount _
  · intro b' role' hb' hr' hne
    rw [hst]; exact (ho2 b' role' hb' hr' hne).trans (ho1 b' role' hb' hr' hne)
  · intro slot hsl hne0 hne1
    rw [hst]
    exact (hb2 slot hsl (by omega)).trans (hb1 slot hsl (by omega))
  · intro addr ha
    rw [hst]; exact (ha2 addr ha).trans (ha1 addr ha)

private def descendBranchNextProg : (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog ℕ
  | ((ctx, q), nd) => do
    let cnt ← pure (nd.1 >>> 1)
    let r ← swarRankClampedProg (((ctxFp ctx, ctxTm ctx), cnt), (q, nd.2.1))
    laneGetBoundedProg ((ctxWvL ctx, nd.2.2), r)

private def DescendBranchNextPre (w : ℕ) :
    (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((ctx, q), nd), _s =>
    let L := (unpackSliceCtx ctx).1
    SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧ 1 ≤ L.wValLane ∧
      q < 2 ^ L.fpBits ∧ nd.2.1 < 2 ^ (2 * L.tMin * (L.fpBits + 2))

private theorem realizesBounded_descendBranchNext :
    RealizesBounded .exact descendBranchNextProg
      (WordEncoding.encode (α := (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ))
      DescendBranchNextPre (fun _ _ => 0) := by
  have hsr := realizesBounded_swarRankClamped
  have hlg := realizesBounded_laneGet
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, q⟩, ⟨mw, ⟨kw, vw⟩⟩⟩
    dsimp only [DescendBranchNextPre, unpackSliceCtx] at h
    obtain ⟨⟨hw6, h8, h4k, h4v⟩, hwvL1, hq, hkw⟩ := h
    try dsimp only [ctxFp, ctxTm, ctxWvL, Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_swarRankClampedProg] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hwvL_w, _⟩ := mul_three_bounds (by omega) hwvL1 h4v
    have hr_lt := swarRankClampedProg_lt (fpBits := fp) (tMin := tm) (m := mw >>> 1) (q := q)
      (kw := kw) (by omega) s)
  all_goals try omega
  all_goals try (unfold SwarRankClampedPre; exact ⟨by omega, h4k, hq, hkw⟩)
  all_goals (
    unfold LaneGetPre
    exact ⟨hwvL_w, (idx_mul_lt_of_four_mul hr_lt.le h4v).trans hw_lt⟩)

/-- One step of `descendToLeaf` in `Memory.Prog` (3 input `FVar`s, `ctx` packed). -/
private def descendStepProg : (BTreeSliceCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, q), cur) => do
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let nd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, cur)
    if nd.1 % 2 = 1 then pure cur
    else descendBranchNextProg ((ctx, q), nd)

private def DescendStepPre (w : ℕ) : (BTreeSliceCtx × ℕ) × ℕ → Memory.State → Prop
  | ((ctx, q), _cur), s =>
    BTreeSlicePre w ctx s ∧ q < 2 ^ (unpackSliceCtx ctx).1.fpBits

private theorem realizesBounded_descendStep :
    RealizesBounded .exact descendStepProg
      (WordEncoding.encode (α := (BTreeSliceCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      DescendStepPre (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hbn := realizesBounded_descendBranchNext
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, q⟩, cur⟩
    dsimp only [DescendStepPre, BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨⟨hvL, hb, hrole⟩, hq⟩ := h
    obtain ⟨hf3, hf2, hf1, hf0, hfb, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hwvL1 : 1 ≤ wvL := hvL.2.2.2.2.2.1
    have hwk : wk = 2 * tm * (fp + 2) := hvL.2.2.2.2.2.2.2.1
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    set L0 : BTreeEpochLayout :=
      ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩
    have hrn_spec := readSliceNodeAtProg_spec L0 b role cur s
    dsimp only [L0, BTreeEpochLayout.toNodeCtx, StateTransitionSpec.clientResult] at hrn_spec
    try dsimp only [ctxNodeAt, ctxB, ctxRole, ctxNs, ctxMb, ctxOm, ctxOkOv,
      ctxWv, ctxWm, ctxWkWvl] at *
    try simp only [StateTransitionSpec.clientState, hrn_spec.1,
      runClient_state_readSliceNodeAtProg] at *
    have hkw_lt : ((extractBTreeSlice L0 b role s.mem).nodes cur).keysWord <
        2 ^ (2 * tm * (fp + 2)) := hwk ▸ (extractBTreeSlice_node_bounds L0 b role cur s.mem).2.1)
  all_goals try assumption
  all_goals try decide
  all_goals (
    unfold DescendBranchNextPre
    dsimp only [unpackSliceCtx]
    exact ⟨hsp, hwvL1, hq, hkw_lt⟩)

private theorem memoryCost_descendStepProg_pos (x : (BTreeSliceCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (descendStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩,
    ⟨⟨⟨_, _⟩, ⟨_, ns⟩⟩, ⟨_, ⟨_, _⟩⟩⟩⟩, _⟩, cur⟩
  unfold descendStepProg readSliceNodeAtProg
  simp only [Realization.memoryCost_bind', pure_bind]
  by_cases hu : cur < ns <;>
    simp only [hu, ↓reduceIte, Realization.memoryCost_bind',
      memoryCost_readPackedCompGenProg, runClient_state_readPackedCompGenProg] <;>
    omega

private def descendLoopProg : ((BTreeSliceCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cq, cur), fuel) => iterate descendStepProg cq fuel cur

private theorem realizesBounded_descendLoop :
    RealizesBounded .exact descendLoopProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cq, cur), fuel) s => iterationSafe descendStepProg DescendStepPre w cq fuel cur s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BTreeSliceCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_descendStep
    memoryCost_descendStepProg_pos

/-- Precondition for `btreeLookupBoundedProg` and `btreeDeleteBoundedProg`. -/
@[expose] def BTreeKeyOpPre (w : ℕ) : BTreeSliceCtx × ℕ → Memory.State → Prop
  | (ctx, q), s => BTreeSlicePre w ctx s ∧ q < 2 ^ (unpackSliceCtx ctx).1.fpBits

private theorem descend_iter_state_safe {w : ℕ} {ctx : BTreeSliceCtx} {q : ℕ} {s : Memory.State}
    (hpre : BTreeKeyOpPre w (ctx, q) s) :
    ∀ m cur,
      iterationSafe descendStepProg DescendStepPre w (ctx, q) m cur s ∧
      (Memory.spec 0).clientState s (iterate descendStepProg (ctx, q) m cur) = s ∧
      memoryCost (iterate descendStepProg (ctx, q) m cur) s ≤ 6 * m := by
  intro m
  induction m with
  | zero => intro _; exact ⟨trivial, rfl, Nat.zero_le _⟩
  | succ m ih =>
    intro cur
    have hst1 : (Memory.spec 0).clientState s (descendStepProg ((ctx, q), cur)) = s := by
      rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
        ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
      unfold descendStepProg descendBranchNextProg StateTransitionSpec.clientState
      simp only [pure_bind, prog_runClient_state_bind, runClient_state_readSliceNodeAtProg]
      split_ifs <;> simp
    have hc1 : memoryCost (descendStepProg ((ctx, q), cur)) s ≤ 6 := by
      rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
        ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
      unfold descendStepProg descendBranchNextProg
      have hrn := readSliceNodeAtProg_spec
        ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩ b role cur s
      dsimp only [BTreeEpochLayout.toNodeCtx] at hrn
      simp only [pure_bind]
      rw [Realization.memoryCost_bind', hrn.2.1]
      split_ifs
      · simp only [memoryCost_pure]; have := hrn.2.2; omega
      · simp only [Realization.memoryCost_bind', StateTransitionSpec.clientState,
          memoryCost_swarRankClampedProg, runClient_state_swarRankClampedProg,
          memoryCost_laneGetBoundedProg]
        have := hrn.2.2; omega
    obtain ⟨hsm, hstm, hcm⟩ := ih ((Memory.spec 0).clientResult s (descendStepProg ((ctx, q), cur)))
    refine ⟨⟨hpre, ?_⟩, ?_, ?_⟩
    · rwa [hst1]
    · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1, hstm]
    · unfold iterate; rw [Realization.memoryCost_bind', hst1]; omega

@[simp] private theorem runClient_state_descendLoopProg
    (d : ((BTreeSliceCtx × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (descendLoopProg d))) = s := by
  rcases d with ⟨⟨⟨ctx, q⟩, cur⟩, fuel⟩
  dsimp only [descendLoopProg]
  induction fuel generalizing cur with
  | zero => rfl
  | succ m ih =>
    unfold iterate
    rw [prog_runClient_state_bind]
    have hst1 : (Memory.spec 0).clientState s (descendStepProg ((ctx, q), cur)) = s := by
      rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩,
        ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩⟩
      unfold descendStepProg descendBranchNextProg StateTransitionSpec.clientState
      simp only [pure_bind, prog_runClient_state_bind, runClient_state_readSliceNodeAtProg]
      split_ifs <;> simp
    rw [hst1]
    exact ih _

private def btreeLookupHitProg :
    (BTreeSliceCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog (ℕ × ℕ)
  | ((ctx, q), ((r, kAt), nd)) =>
    if kAt = q then do
      let vAt ← laneGetBoundedProg ((ctxWvL ctx, nd.2.2), r)
      pure (1, vAt)
    else pure (0, 0)

private def BTreeLookupHitPre (w : ℕ) :
    (BTreeSliceCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | ((ctx, _q), ((r, _kAt), _nd)), _s =>
    let L := (unpackSliceCtx ctx).1
    SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧ 1 ≤ L.wValLane ∧ r < 2 * L.tMin

private theorem realizesBounded_btreeLookupHit :
    RealizesBounded .exact btreeLookupHitProg
      (WordEncoding.encode (α := (BTreeSliceCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ × ℕ))
      BTreeLookupHitPre (fun _ _ => 0) := by
  have hlg := realizesBounded_laneGet
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, q⟩, ⟨⟨r, kAt⟩, ⟨mw, ⟨kw, vw⟩⟩⟩⟩
    dsimp only [BTreeLookupHitPre, unpackSliceCtx] at h
    obtain ⟨⟨hw6, h8, h4k, h4v⟩, hwvL1, hr_lt⟩ := h
    try dsimp only at *
    try dsimp only [Fits] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hwvL_w, _⟩ := mul_three_bounds (by omega) hwvL1 h4v)
  all_goals try omega
  all_goals (
    unfold LaneGetPre
    exact ⟨hwvL_w, (idx_mul_lt_of_four_mul hr_lt.le h4v).trans hw_lt⟩)

private def btreeLookupRankProg :
    (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × ℕ)
  | ((ctx, q), nd) => do
    let cnt ← pure (nd.1 >>> 1)
    let fp ← pure (ctxFp ctx)
    let r ← swarRankClampedProg (((fp, ctxTm ctx), cnt), (q, nd.2.1))
    let kAt ← laneGetBoundedProg ((fp + 2, nd.2.1), r)
    if r < cnt then btreeLookupHitProg ((ctx, q), ((r, kAt), nd))
    else pure (0, 0)

private theorem realizesBounded_btreeLookupRank :
    RealizesBounded .exact btreeLookupRankProg
      (WordEncoding.encode (α := (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × ℕ))
      DescendBranchNextPre (fun _ _ => 0) := by
  have hsr := realizesBounded_swarRankClamped
  have hlg := realizesBounded_laneGet
  have hhit := realizesBounded_btreeLookupHit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, q⟩, ⟨mw, ⟨kw, vw⟩⟩⟩
    dsimp only [DescendBranchNextPre, unpackSliceCtx] at h
    obtain ⟨hsp, hwvL1, hq, hkw⟩ := h
    have ⟨hw6, h8, h4k, h4v⟩ := hsp
    try dsimp only [ctxFp, ctxTm, ctxWvL, Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _⟩ := mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have hr_lt := swarRankClampedProg_lt (fpBits := fp) (tMin := tm) (m := mw >>> 1) (q := q)
      (kw := kw) (by omega) s)
  all_goals try omega
  all_goals try (unfold SwarRankClampedPre; exact ⟨by omega, h4k, hq, hkw⟩)
  all_goals try (
    unfold LaneGetPre
    exact ⟨hfp2_w, (idx_mul_lt_of_four_mul hr_lt.le h4k).trans hw_lt⟩)
  all_goals (
    unfold BTreeLookupHitPre
    dsimp only [unpackSliceCtx]
    exact ⟨hsp, hwvL1, hr_lt⟩)

private def btreeLookupLeafProg : BTreeSliceCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (ctx, (leafIdx, q)) => do
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let nd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, leafIdx)
    btreeLookupRankProg ((ctx, q), nd)

private theorem realizesBounded_btreeLookupLeaf :
    RealizesBounded .exact btreeLookupLeafProg
      (WordEncoding.encode (α := BTreeSliceCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, (_leafIdx, q)) s => BTreeKeyOpPre w (ctx, q) s) (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hrk := realizesBounded_btreeLookupRank
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨leafIdx, q⟩⟩
    dsimp only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨⟨hvL, hb, hrole⟩, hq⟩ := h
    obtain ⟨hf3, _, _, _, hfb3, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hwvL1 : 1 ≤ wvL := hvL.2.2.2.2.2.1
    have hwk : wk = 2 * tm * (fp + 2) := hvL.2.2.2.2.2.2.2.1
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceNodeAtProg])
  all_goals try assumption
  all_goals (
    set L0 : BTreeEpochLayout :=
      ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩
    have hrn_spec := readSliceNodeAtProg_spec L0 b role leafIdx s
    dsimp only [L0, BTreeEpochLayout.toNodeCtx] at hrn_spec
    dsimp only [ctxNodeAt, ctxB, ctxRole, ctxNs, ctxMb, ctxOm, ctxOkOv, ctxWv, ctxWm, ctxWkWvl]
    rw [hrn_spec.1]
    have hkw_lt : ((extractBTreeSlice L0 b role s.mem).nodes leafIdx).keysWord <
        2 ^ (2 * tm * (fp + 2)) :=
      hwk ▸ (extractBTreeSlice_node_bounds L0 b role leafIdx s.mem).2.1
    unfold DescendBranchNextPre
    dsimp only [unpackSliceCtx]
    exact ⟨hsp, hwvL1, hq, hkw_lt⟩)

private def btreeLookupNonEmptyProg : ((BTreeSliceCtx × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((ctx, q), rt), fuel) => do
    let leafIdx ← descendLoopProg (((ctx, q), rt), fuel)
    btreeLookupLeafProg (ctx, (leafIdx, q))

private theorem realizesBounded_btreeLookupNonEmpty :
    RealizesBounded .exact btreeLookupNonEmptyProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (cqr, _fuel) s => BTreeKeyOpPre w cqr.1 s) (fun _ _ => 0) := by
  have hdl := realizesBounded_descendLoop
  have hlf := realizesBounded_btreeLookupLeaf
  realize
  all_goals (
    rcases d with ⟨⟨⟨ctx, q⟩, rt⟩, fuel⟩
    have hpre : BTreeKeyOpPre w (ctx, q) s := h
    obtain ⟨hds_safe, _, _⟩ := descend_iter_state_safe hpre fuel rt)
  all_goals try exact hds_safe
  all_goals (
    simp only [StateTransitionSpec.clientState, runClient_state_descendLoopProg]
    exact hpre)

/-- `btreeLookup` in `Memory.Prog`, returning `(foundFlag, val)` (`RealizesBounded .exact`,
`¬ReadsWidth`). -/
def btreeLookupBoundedProg : BTreeSliceCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (ctx, q) => do
    let hdrBase ← pure (16 * ctxB ctx + 6 + 2 * ctxRole ctx)
    let hdr ← readSliceHdrAtProg (ctxHdrAt ctx hdrBase)
    if hdr.1 = 0 then pure (0, 0)
    else btreeLookupNonEmptyProg (((ctx, q), hdr.2), hMaxBTree)

theorem realizesBounded_btreeLookup :
    RealizesBounded .exact btreeLookupBoundedProg
      (WordEncoding.encode (α := BTreeSliceCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      BTreeKeyOpPre (fun _ _ => 0) := by
  have hrh := realizesBounded_readSliceHdrAt
  have hne := realizesBounded_btreeLookupNonEmpty
  realize
  all_goals (
    rcases d with ⟨ctx, q⟩
    have hpre : BTreeKeyOpPre w (ctx, q) s := h
    rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    have hpre_u := hpre
    dsimp only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx] at hpre_u
    obtain ⟨⟨hvL, hb, hrole⟩, _⟩ := hpre_u
    have hmax := fits_hMaxBTree hvL.six_le_w
    obtain ⟨hf16, hf6, hf2, hf1, hf0, hfb16, hfb6, hfr2, hfhb, hhdr⟩ := hvL.hdr_facts hb hrole
    dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceHdrAtProg] at *)
  all_goals assumption

private def btreeDeleteHitProg :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × (ℕ × ℕ)))) → Memory.Prog Unit
  | (((ctx, q), (nodeBase, leafIdx)), ((cnt, r), (kAt, nd))) =>
    if kAt = q then do
      let mw' ← pure (1 + 2 * (cnt - 1))
      let kw' ← wordDeleteAtBoundedProg ((ctxFp ctx + 2, r), nd.2.1)
      let vw' ← wordDeleteAtBoundedProg ((ctxWvL ctx, r), nd.2.2)
      writeSliceNodeAtProg ((ctxNodeAt ctx nodeBase, leafIdx), (mw', (kw', vw')))
    else pure ()

private def BTreeDeleteHitPre (w : ℕ) :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × (ℕ × ℕ)))) → Memory.State → Prop
  | (((ctx, _q), (nodeBase, _leafIdx)), ((cnt, r), (_kAt, nd))), s =>
    let L := (unpackSliceCtx ctx).1
    SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧ 1 ≤ L.wValLane ∧
      1 ≤ cnt ∧ r < 2 * L.tMin ∧
      cnt + 1 < 2 ^ w ∧ 2 * (cnt + 1) < 2 ^ w ∧ 1 + 2 * (cnt + 1) < 2 ^ w ∧
      nd.2.1 < 2 ^ (2 * L.tMin * (L.fpBits + 2)) ∧ nd.2.2 < 2 ^ (2 * L.tMin * L.wValLane)

private theorem realizesBounded_btreeDeleteHit :
    RealizesBounded .exact btreeDeleteHitProg
      (WordEncoding.encode
        (α := ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := Unit))
      BTreeDeleteHitPre (fun _ _ => 0) := by
  have hwd := realizesBounded_wordDeleteAt
  have hwn := realizesBounded_writeSliceNodeAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, q⟩, ⟨nodeBase, leafIdx⟩⟩,
      ⟨⟨cnt, r⟩, ⟨kAt, ⟨mw, ⟨kw, vw⟩⟩⟩⟩⟩
    dsimp only [BTreeDeleteHitPre, unpackSliceCtx] at h
    obtain ⟨hnode, ⟨hw6, h8, h4k, h4v⟩, hwvL1, hcnt1, hr_lt, hc1, h2c, h12c, hkw, hvw⟩ := h
    try dsimp only [ctxFp, ctxWvL] at *
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_wordDeleteAtBoundedProg] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _, _, _, _, _, _, _, h2t1_fp⟩ :=
      mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    obtain ⟨_, _, _, _, _, _, _, _, h2t1_wv⟩ := mul_three_bounds (by omega) hwvL1 h4v
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt)
  all_goals try assumption
  all_goals try omega
  all_goals try (
    unfold WordDeleteAtPre
    exact ⟨2 * tm, by omega, hr_lt.le, h2t1_fp,
      hkw.trans (Nat.pow_lt_pow_right Nat.one_lt_two (by rw [Nat.add_one_mul (2 * tm)]; omega))⟩)
  all_goals (
    unfold WordDeleteAtPre
    exact ⟨2 * tm, hwvL1, hr_lt.le, h2t1_wv,
      hvw.trans (Nat.pow_lt_pow_right Nat.one_lt_two (by rw [Nat.add_one_mul (2 * tm)]; omega))⟩)

private def btreeDeleteRankProg :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (((ctx, q), nl), nd) => do
    let cnt ← pure (nd.1 >>> 1)
    let fp ← pure (ctxFp ctx)
    let r ← swarRankClampedProg (((fp, ctxTm ctx), cnt), (q, nd.2.1))
    let kAt ← laneGetBoundedProg ((fp + 2, nd.2.1), r)
    if r < cnt then btreeDeleteHitProg (((ctx, q), nl), ((cnt, r), (kAt, nd)))
    else pure ()

private def BTreeDeleteRankPre (w : ℕ) :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (((ctx, q), (nodeBase, _leafIdx)), nd), s =>
    let L := (unpackSliceCtx ctx).1
    SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧ 1 ≤ L.wValLane ∧
      q < 2 ^ L.fpBits ∧ nd.1 >>> 1 + 1 < 2 ^ w ∧
      2 * (nd.1 >>> 1 + 1) < 2 ^ w ∧ 1 + 2 * (nd.1 >>> 1 + 1) < 2 ^ w ∧
      nd.2.1 < 2 ^ (2 * L.tMin * (L.fpBits + 2)) ∧ nd.2.2 < 2 ^ (2 * L.tMin * L.wValLane)

private theorem realizesBounded_btreeDeleteRank :
    RealizesBounded .exact btreeDeleteRankProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      BTreeDeleteRankPre (fun _ _ => 0) := by
  have hsr := realizesBounded_swarRankClamped
  have hlg := realizesBounded_laneGet
  have hhit := realizesBounded_btreeDeleteHit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, q⟩, ⟨nodeBase, leafIdx⟩⟩, ⟨mw, ⟨kw, vw⟩⟩⟩
    dsimp only [BTreeDeleteRankPre, unpackSliceCtx] at h
    obtain ⟨hnode, hsp, hwvL1, hq, hc1, h2c, h12c, hkw, hvw⟩ := h
    have ⟨hw6, h8, h4k, h4v⟩ := hsp
    try dsimp only [ctxFp, ctxTm, ctxWvL, Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _⟩ := mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have hr_lt := swarRankClampedProg_lt (fpBits := fp) (tMin := tm) (m := mw >>> 1) (q := q)
      (kw := kw) (by omega) s)
  all_goals try omega
  all_goals try (unfold SwarRankClampedPre; exact ⟨by omega, h4k, hq, hkw⟩)
  all_goals try (
    unfold LaneGetPre
    exact ⟨hfp2_w, (idx_mul_lt_of_four_mul hr_lt.le h4k).trans hw_lt⟩)
  all_goals (
    unfold BTreeDeleteHitPre
    dsimp only [unpackSliceCtx]
    exact ⟨hnode, hsp, hwvL1, by omega, hr_lt, hc1, h2c, h12c, hkw, hvw⟩)

private def btreeDeleteLeafProg : BTreeSliceCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (ctx, (leafIdx, q)) => do
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let nd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, leafIdx)
    btreeDeleteRankProg (((ctx, q), (nodeBase, leafIdx)), nd)

private theorem realizesBounded_btreeDeleteLeaf :
    RealizesBounded .exact btreeDeleteLeafProg
      (WordEncoding.encode (α := BTreeSliceCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, (_leafIdx, q)) s => BTreeKeyOpPre w (ctx, q) s) (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hrk := realizesBounded_btreeDeleteRank
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨leafIdx, q⟩⟩
    dsimp only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨⟨hvL, hb, hrole⟩, hq⟩ := h
    obtain ⟨hf3, _, _, _, hfb3, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hwvL1 : 1 ≤ wvL := hvL.2.2.2.2.2.1
    have hwm : wm < w := hvL.2.2.2.2.2.2.1
    have hwk : wk = 2 * tm * (fp + 2) := hvL.2.2.2.2.2.2.2.1
    have hwvl : wvl = 2 * tm * wvL := hvL.2.2.2.2.2.2.2.2.1
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceNodeAtProg])
  all_goals try assumption
  all_goals (
    set L0 : BTreeEpochLayout :=
      ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩
    have hrn_spec := readSliceNodeAtProg_spec L0 b role leafIdx s
    dsimp only [L0, BTreeEpochLayout.toNodeCtx] at hrn_spec
    dsimp only [ctxNodeAt, ctxB, ctxRole, ctxNs, ctxMb, ctxOm, ctxOkOv, ctxWv, ctxWm, ctxWkWvl]
    rw [hrn_spec.1]
    obtain ⟨hmw_lt, hkw_raw, hvw_raw⟩ := extractBTreeSlice_node_bounds L0 b role leafIdx s.mem
    obtain ⟨hc1, h2c, h12c⟩ := metaWord_shiftRight_bound (le_trans (by decide) hsp.1) hwm hmw_lt
    unfold BTreeDeleteRankPre
    dsimp only [unpackSliceCtx]
    exact ⟨hnode, hsp, hwvL1, hq, hc1, h2c, h12c, hwk ▸ hkw_raw, hwvl ▸ hvw_raw⟩)

private def btreeDeleteNonEmptyProg : ((BTreeSliceCtx × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((ctx, q), rt), fuel) => do
    let leafIdx ← descendLoopProg (((ctx, q), rt), fuel)
    btreeDeleteLeafProg (ctx, (leafIdx, q))

private theorem realizesBounded_btreeDeleteNonEmpty :
    RealizesBounded .exact btreeDeleteNonEmptyProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cqr, _fuel) s => BTreeKeyOpPre w cqr.1 s) (fun _ _ => 0) := by
  have hdl := realizesBounded_descendLoop
  have hlf := realizesBounded_btreeDeleteLeaf
  realize
  all_goals (
    rcases d with ⟨⟨⟨ctx, q⟩, rt⟩, fuel⟩
    have hpre : BTreeKeyOpPre w (ctx, q) s := h
    obtain ⟨hds_safe, _, _⟩ := descend_iter_state_safe hpre fuel rt)
  all_goals try exact hds_safe
  all_goals (
    simp only [StateTransitionSpec.clientState, runClient_state_descendLoopProg]
    exact hpre)

/-- `btreeDelete` in `Memory.Prog` (`RealizesBounded .exact`, `¬ReadsWidth`). -/
def btreeDeleteBoundedProg : BTreeSliceCtx × ℕ → Memory.Prog Unit
  | (ctx, q) => do
    let hdrBase ← pure (16 * ctxB ctx + 6 + 2 * ctxRole ctx)
    let hdr ← readSliceHdrAtProg (ctxHdrAt ctx hdrBase)
    if hdr.1 = 0 then pure ()
    else btreeDeleteNonEmptyProg (((ctx, q), hdr.2), hMaxBTree)

theorem realizesBounded_btreeDelete :
    RealizesBounded .exact btreeDeleteBoundedProg
      (WordEncoding.encode (α := BTreeSliceCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      BTreeKeyOpPre (fun _ _ => 0) := by
  have hrh := realizesBounded_readSliceHdrAt
  have hne := realizesBounded_btreeDeleteNonEmpty
  realize
  all_goals (
    rcases d with ⟨ctx, q⟩
    have hpre : BTreeKeyOpPre w (ctx, q) s := h
    rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    have hpre_u := hpre
    dsimp only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx] at hpre_u
    obtain ⟨⟨hvL, hb, hrole⟩, _⟩ := hpre_u
    have hmax := fits_hMaxBTree hvL.six_le_w
    obtain ⟨hf16, hf6, hf2, hf1, hf0, hfb16, hfb6, hfr2, hfhb, hhdr⟩ := hvL.hdr_facts hb hrole
    dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceHdrAtProg] at *)
  all_goals assumption

/-- Precondition for `btreeUpdateBoundedProg` and `btreeInsertBoundedProg`. -/
@[expose] def BTreeKeyValOpPre (w : ℕ) : BTreeSliceCtx × (ℕ × ℕ) → Memory.State → Prop
  | (ctx, (q, val)), s =>
    let L := (unpackSliceCtx ctx).1
    BTreeSlicePre w ctx s ∧ q < 2 ^ L.fpBits ∧ val < 2 ^ L.wValLane

private def btreeUpdateHitProg :
    ((BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog Unit
  | (((ctx, (q, newVal)), (nodeBase, leafIdx)), ((r, kAt), nd)) =>
    if kAt = q then do
      let vw' ← wordUpdateAtBoundedProg (((ctxWvL ctx, r), newVal), nd.2.2)
      writeSliceNodeAtProg ((ctxNodeAt ctx nodeBase, leafIdx), (nd.1, (nd.2.1, vw')))
    else pure ()

private def BTreeUpdateHitPre (w : ℕ) :
    ((BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | (((ctx, (_q, newVal)), (nodeBase, _leafIdx)), ((r, _kAt), nd)), s =>
    let L := (unpackSliceCtx ctx).1
    SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧ 1 ≤ L.wValLane ∧
      r < 2 * L.tMin ∧ newVal < 2 ^ L.wValLane ∧ nd.2.2 < 2 ^ (2 * L.tMin * L.wValLane)

private theorem realizesBounded_btreeUpdateHit :
    RealizesBounded .exact btreeUpdateHitProg
      (WordEncoding.encode
        (α := ((BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := Unit))
      BTreeUpdateHitPre (fun _ _ => 0) := by
  have hwu := realizesBounded_wordUpdateAt
  have hwn := realizesBounded_writeSliceNodeAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨q, newVal⟩⟩, ⟨nodeBase, leafIdx⟩⟩,
      ⟨⟨r, kAt⟩, ⟨mw, ⟨kw, vw⟩⟩⟩⟩
    dsimp only [BTreeUpdateHitPre, unpackSliceCtx] at h
    obtain ⟨hnode, ⟨hw6, h8, h4k, h4v⟩, hwvL1, hr_lt, hval, hvw⟩ := h
    try dsimp only [ctxWvL] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_wordUpdateAtBoundedProg] at *
    obtain ⟨_, _, _, _, _, _, _, _, h2t1_wv⟩ := mul_three_bounds (by omega) hwvL1 h4v)
  all_goals try assumption
  all_goals (
    unfold WordUpdateAtPre
    exact ⟨2 * tm, hwvL1, hr_lt.le, h2t1_wv, hval,
      hvw.trans (Nat.pow_lt_pow_right Nat.one_lt_two (by rw [Nat.add_one_mul (2 * tm)]; omega))⟩)

private def btreeUpdateRankProg :
    ((BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (((ctx, (q, newVal)), nl), nd) => do
    let cnt ← pure (nd.1 >>> 1)
    let fp ← pure (ctxFp ctx)
    let r ← swarRankClampedProg (((fp, ctxTm ctx), cnt), (q, nd.2.1))
    let kAt ← laneGetBoundedProg ((fp + 2, nd.2.1), r)
    if r < cnt then btreeUpdateHitProg (((ctx, (q, newVal)), nl), ((r, kAt), nd))
    else pure ()

private def BTreeUpdateRankPre (w : ℕ) :
    ((BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (((ctx, (q, newVal)), (nodeBase, _leafIdx)), nd), s =>
    let L := (unpackSliceCtx ctx).1
    SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧ 1 ≤ L.wValLane ∧
      q < 2 ^ L.fpBits ∧ newVal < 2 ^ L.wValLane ∧
      nd.2.1 < 2 ^ (2 * L.tMin * (L.fpBits + 2)) ∧ nd.2.2 < 2 ^ (2 * L.tMin * L.wValLane)

private theorem realizesBounded_btreeUpdateRank :
    RealizesBounded .exact btreeUpdateRankProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      BTreeUpdateRankPre (fun _ _ => 0) := by
  have hsr := realizesBounded_swarRankClamped
  have hlg := realizesBounded_laneGet
  have hhit := realizesBounded_btreeUpdateHit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨q, newVal⟩⟩, ⟨nodeBase, leafIdx⟩⟩,
      ⟨mw, ⟨kw, vw⟩⟩⟩
    dsimp only [BTreeUpdateRankPre, unpackSliceCtx] at h
    obtain ⟨hnode, hsp, hwvL1, hq, hval, hkw, hvw⟩ := h
    have ⟨hw6, h8, h4k, h4v⟩ := hsp
    try dsimp only [ctxFp, ctxTm, ctxWvL, Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _⟩ := mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have hr_lt := swarRankClampedProg_lt (fpBits := fp) (tMin := tm) (m := mw >>> 1) (q := q)
      (kw := kw) (by omega) s)
  all_goals try omega
  all_goals try (unfold SwarRankClampedPre; exact ⟨by omega, h4k, hq, hkw⟩)
  all_goals try (
    unfold LaneGetPre
    exact ⟨hfp2_w, (idx_mul_lt_of_four_mul hr_lt.le h4k).trans hw_lt⟩)
  all_goals (
    unfold BTreeUpdateHitPre
    dsimp only [unpackSliceCtx]
    exact ⟨hnode, hsp, hwvL1, hr_lt, hval, hvw⟩)

private def btreeUpdateLeafProg : BTreeSliceCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (ctx, (leafIdx, (q, newVal))) => do
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let nd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, leafIdx)
    btreeUpdateRankProg (((ctx, (q, newVal)), (nodeBase, leafIdx)), nd)

private theorem realizesBounded_btreeUpdateLeaf :
    RealizesBounded .exact btreeUpdateLeafProg
      (WordEncoding.encode (α := BTreeSliceCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, (_leafIdx, qv)) s => BTreeKeyValOpPre w (ctx, qv) s) (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hrk := realizesBounded_btreeUpdateRank
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨leafIdx, ⟨q, newVal⟩⟩⟩
    dsimp only [BTreeKeyValOpPre, BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨⟨hvL, hb, hrole⟩, hq, hval⟩ := h
    obtain ⟨hf3, _, _, _, hfb3, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hwvL1 : 1 ≤ wvL := hvL.2.2.2.2.2.1
    have hwk : wk = 2 * tm * (fp + 2) := hvL.2.2.2.2.2.2.2.1
    have hwvl : wvl = 2 * tm * wvL := hvL.2.2.2.2.2.2.2.2.1
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceNodeAtProg])
  all_goals try assumption
  all_goals (
    set L0 : BTreeEpochLayout :=
      ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩
    have hrn_spec := readSliceNodeAtProg_spec L0 b role leafIdx s
    dsimp only [L0, BTreeEpochLayout.toNodeCtx] at hrn_spec
    dsimp only [ctxNodeAt, ctxB, ctxRole, ctxNs, ctxMb, ctxOm, ctxOkOv, ctxWv, ctxWm, ctxWkWvl]
    rw [hrn_spec.1]
    obtain ⟨_, hkw_raw, hvw_raw⟩ := extractBTreeSlice_node_bounds L0 b role leafIdx s.mem
    unfold BTreeUpdateRankPre
    dsimp only [unpackSliceCtx]
    exact ⟨hnode, hsp, hwvL1, hq, hval, hwk ▸ hkw_raw, hwvl ▸ hvw_raw⟩)

private def btreeUpdateNonEmptyProg : (BTreeSliceCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((ctx, (q, newVal)), rt) => do
    let leafIdx ← descendLoopProg (((ctx, q), rt), hMaxBTree)
    btreeUpdateLeafProg (ctx, (leafIdx, (q, newVal)))

private theorem realizesBounded_btreeUpdateNonEmpty :
    RealizesBounded .exact btreeUpdateNonEmptyProg
      (WordEncoding.encode (α := (BTreeSliceCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cqv, _rt) s => BTreeKeyValOpPre w cqv s) (fun _ _ => 0) := by
  have hdl := realizesBounded_descendLoop
  have hlf := realizesBounded_btreeUpdateLeaf
  realize
  all_goals (
    rcases d with ⟨⟨ctx, ⟨q, newVal⟩⟩, rt⟩
    obtain ⟨hslice, hq, hval⟩ := h
    have hpre : BTreeKeyOpPre w (ctx, q) s := ⟨hslice, hq⟩
    obtain ⟨hds_safe, _, _⟩ := descend_iter_state_safe hpre hMaxBTree rt
    have hmax := fits_hMaxBTree hslice.1.six_le_w)
  all_goals try exact hmax
  all_goals try exact hds_safe
  all_goals (
    simp only [StateTransitionSpec.clientState, runClient_state_descendLoopProg]
    exact ⟨hslice, hq, hval⟩)

/-- `btreeUpdate` in `Memory.Prog` (`RealizesBounded .exact`, `¬ReadsWidth`). -/
def btreeUpdateBoundedProg : BTreeSliceCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (ctx, (q, newVal)) => do
    let hdrBase ← pure (16 * ctxB ctx + 6 + 2 * ctxRole ctx)
    let hdr ← readSliceHdrAtProg (ctxHdrAt ctx hdrBase)
    if hdr.1 = 0 then pure ()
    else btreeUpdateNonEmptyProg ((ctx, (q, newVal)), hdr.2)

theorem realizesBounded_btreeUpdate :
    RealizesBounded .exact btreeUpdateBoundedProg
      (WordEncoding.encode (α := BTreeSliceCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      BTreeKeyValOpPre (fun _ _ => 0) := by
  have hrh := realizesBounded_readSliceHdrAt
  have hne := realizesBounded_btreeUpdateNonEmpty
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨q, newVal⟩⟩
    have hpre : BTreeKeyValOpPre w (ctx, (q, newVal)) s := h
    rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    have hpre_u := hpre
    dsimp only [BTreeKeyValOpPre, BTreeSlicePre, unpackSliceCtx] at hpre_u
    obtain ⟨⟨hvL, hb, hrole⟩, _, _⟩ := hpre_u
    obtain ⟨hf16, hf6, hf2, hf1, hf0, hfb16, hfb6, hfr2, hfhb, hhdr⟩ := hvL.hdr_facts hb hrole
    dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceHdrAtProg] at *)
  all_goals assumption

private def splitFullLeafProg :
    (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) →
      Memory.Prog (((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × (ℕ × ℕ)))
  | ((((fp, wvL), tm), sep), ((kw, vw), (rKw, rVw))) => do
    let lKw ← wordTakeLowBoundedProg ((fp + 2, tm), kw)
    let lVw ← wordTakeLowBoundedProg ((wvL, tm), vw)
    pure (((1 + 2 * tm, (lKw, lVw)), sep), (1 + 2 * (tm - 1), (rKw, rVw)))

private theorem realizesBounded_splitFullLeaf :
    RealizesBounded .exact splitFullLeafProg
      (WordEncoding.encode (α := (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × (ℕ × ℕ))))
      (fun w ((spP, _), _) _ => SplitParamsPre w spP) (fun _ _ => 0) := by
  have htk := realizesBounded_wordTakeLow
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨fp, wvL⟩, tm⟩, sep⟩, ⟨⟨kw, vw⟩, ⟨rKw, rVw⟩⟩⟩
    obtain ⟨hw6, h8, h4k, h4v⟩ := h
    try dsimp only [Fits, WordTakeDropPre] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _, _, h4tm_w, _, htm_fp, _⟩ :=
      mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have htm_wv := idx_mul_lt_of_four_mul (by omega : tm ≤ 2 * tm) h4v
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have h4tm_fits : 4 * tm < 2 ^ w := h4tm_w.trans hw_lt)
  all_goals omega

private def splitFullBranchProg :
    (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) →
      Memory.Prog (((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × (ℕ × ℕ)))
  | ((((fp, wvL), tm), sep), ((kw, vw), (rKw, rVw))) => do
    let lKw ← wordTakeLowBoundedProg ((fp + 2, tm - 1), kw)
    let lVw ← wordTakeLowBoundedProg ((wvL, tm), vw)
    pure (((2 * (tm - 1), (lKw, lVw)), sep), (2 * (tm - 1), (rKw, rVw)))

private theorem realizesBounded_splitFullBranch :
    RealizesBounded .exact splitFullBranchProg
      (WordEncoding.encode (α := (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × (ℕ × ℕ))))
      (fun w ((spP, _), _) _ => SplitParamsPre w spP) (fun _ _ => 0) := by
  have htk := realizesBounded_wordTakeLow
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨fp, wvL⟩, tm⟩, sep⟩, ⟨⟨kw, vw⟩, ⟨rKw, rVw⟩⟩⟩
    obtain ⟨hw6, h8, h4k, h4v⟩ := h
    try dsimp only [Fits, WordTakeDropPre] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _, _, h4tm_w, htm1_fp, _⟩ :=
      mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have htm_wv := idx_mul_lt_of_four_mul (by omega : tm ≤ 2 * tm) h4v
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have h4tm_fits : 4 * tm < 2 ^ w := h4tm_w.trans hw_lt)
  all_goals omega

/-- Pure `splitFullNode` via `SplitParams` (6 words total): returns `((leftNd, sep), rightNd)`. -/
private def splitFullNodeAtProg :
    SplitParams × (ℕ × (ℕ × ℕ)) →
      Memory.Prog (((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × (ℕ × ℕ)))
  | (((fp, wvL), tm), (mw, (kw, vw))) => do
    let wk ← pure (fp + 2)
    let tm1 ← pure (tm - 1)
    let sep ← laneGetBoundedProg ((wk, kw), tm1)
    let rKw ← wordDropLowBoundedProg ((wk, tm), kw)
    let rVw ← wordDropLowBoundedProg ((wvL, tm), vw)
    if mw % 2 = 1 then
      splitFullLeafProg (((((fp, wvL), tm), sep), ((kw, vw), (rKw, rVw))))
    else
      splitFullBranchProg (((((fp, wvL), tm), sep), ((kw, vw), (rKw, rVw))))

private theorem realizesBounded_splitFullNodeAt :
    RealizesBounded .exact splitFullNodeAtProg
      (WordEncoding.encode (α := SplitParams × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × ℕ) × (ℕ × (ℕ × ℕ))))
      (fun w (spP, _) _ => SplitParamsPre w spP) (fun _ _ => 0) := by
  have hlg := realizesBounded_laneGet
  have hdr := realizesBounded_wordDropLow
  have hlf := realizesBounded_splitFullLeaf
  have hbr := realizesBounded_splitFullBranch
  realize
  all_goals (
    rcases d with ⟨⟨⟨fp, wvL⟩, tm⟩, ⟨mw, ⟨kw, vw⟩⟩⟩
    have hsp : SplitParamsPre w ((fp, wvL), tm) := h
    obtain ⟨hw6, h8, h4k, h4v⟩ := hsp
    try dsimp only [Fits, WordTakeDropPre] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _, _, h4tm_w, htm1_fp, htm_fp, _⟩ :=
      mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have htm_wv := idx_mul_lt_of_four_mul (by omega : tm ≤ 2 * tm) h4v
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have h4tm_fits : 4 * tm < 2 ^ w := h4tm_w.trans hw_lt)
  all_goals try (unfold LaneGetPre; exact ⟨hfp2_w, htm1_fp.trans hw_lt⟩)
  all_goals omega

@[simp] private theorem runClient_state_splitFullNodeAtProg
    (d : SplitParams × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (splitFullNodeAtProg d))) = s := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold splitFullNodeAtProg splitFullLeafProg splitFullBranchProg
  simp only [pure_bind, prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_laneGetBoundedProg, runClient_state_wordDropLowBoundedProg]
  split_ifs <;> simp

private theorem splitFullNodeAtProg_spec (L : BTreeEpochLayout) (nd : BTreeNode)
    (s : Memory.State) :
    let sp := splitFullNode L.fpBits L.wValLane L.tMin nd
    let arg := (((L.fpBits, L.wValLane), L.tMin), (nd.metaWord, (nd.keysWord, nd.valsWord)))
    (Memory.spec 0).clientResult s (splitFullNodeAtProg arg) =
      (((sp.left.metaWord, (sp.left.keysWord, sp.left.valsWord)), sp.sep),
       (sp.right.metaWord, (sp.right.keysWord, sp.right.valsWord))) ∧
    (Memory.spec 0).clientState s (splitFullNodeAtProg arg) = s ∧
    memoryCost (splitFullNodeAtProg arg) s = 0 := by
  unfold splitFullNodeAtProg splitFullLeafProg splitFullBranchProg splitFullNode metaIsLeaf
    mkNodeMeta
  by_cases hl : nd.metaWord % 2 = 1
  · refine ⟨by simp [hl], ?_, by simp [hl]⟩
    unfold StateTransitionSpec.clientState; simp [hl]
  · refine ⟨by simp [hl], ?_, by simp [hl]⟩
    unfold StateTransitionSpec.clientState; simp [hl]

/-- Initialize an empty slice (`alloc = 0`) to a single empty leaf at `0` (15 words, 4 binds). -/
private def initEmptyRootAtProg : SliceNodeCtx × SliceHdrCtx → Memory.Prog ℕ
  | (nctx, hctx) => do
    writeSliceNodeAtProg ((nctx, 0), (1, (0, 0)))
    writeSliceHdrAtProg (hctx, (0, 1))
    writeSliceHdrAtProg (hctx, (1, 0))
    pure 0

private theorem realizesBounded_initEmptyRootAt :
    RealizesBounded .exact initEmptyRootAtProg
      (WordEncoding.encode (α := SliceNodeCtx × SliceHdrCtx))
      (WordEncoding.encode (α := ℕ))
      (fun w (nctx, hctx) s => SliceNodePre w nctx s.frontier ∧ SliceHdrPre w hctx s.frontier)
      (fun _ _ => 0) := by
  have hwn := realizesBounded_writeSliceNodeAt
  have hwh := realizesBounded_writeSliceHdrAt
  realize
  all_goals (
    rcases d with ⟨nctx, hctx⟩
    obtain ⟨hn, hh⟩ := h
    have hw6 : 6 ≤ w := by
      rcases hctx with ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, _⟩
      obtain ⟨_, hw6, _⟩ := hh; exact hw6
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_frontier_writeSliceNodeAtProg,
      runClient_frontier_writeSliceHdrAtProg] at *)
  all_goals try assumption
  all_goals omega

@[simp] private theorem runClient_frontier_initEmptyRootAtProg
    (d : SliceNodeCtx × SliceHdrCtx) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (initEmptyRootAtProg d)))).frontier =
      s.frontier := by
  rcases d with ⟨_, _⟩
  unfold initEmptyRootAtProg; simp

/-- Pure word computation of `((leftNd, rightNd), newRootNd)` for root splitting (7 words). -/
private def computeRootSplitProg :
    (SplitParams × ℕ) × (ℕ × (ℕ × ℕ)) →
      Memory.Prog (((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × ℕ)))
  | ((spP, al), rootNd) => do
    let wvL ← pure spP.1.2
    let sp ← splitFullNodeAtProg (spP, rootNd)
    let rIdx ← pure (al + 1)
    let sh ← pure (rIdx <<< wvL)
    let newVals ← pure (al + sh)
    pure ((sp.1.1, sp.2), (2, (sp.1.2, newVals)))

private def ComputeRootSplitPre (w : ℕ) :
    (SplitParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((spP, al), _rootNd), _s => SplitParamsPre w spP ∧ al + 1 < 2 ^ spP.1.2

private theorem realizesBounded_computeRootSplit :
    RealizesBounded .exact computeRootSplitProg
      (WordEncoding.encode (α := (SplitParams × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × ℕ))))
      ComputeRootSplitPre (fun _ _ => 0) := by
  have hsp := realizesBounded_splitFullNodeAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨fp, wvL⟩, tm⟩, al⟩, rootNd⟩
    obtain ⟨⟨hw6, h8, h4k, h4v⟩, hal1⟩ := h
    try dsimp only [Fits] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    have hwvL1 : 1 ≤ wvL := by
      by_contra h0
      have hwvL0 : wvL = 0 := by omega
      rw [hwvL0] at hal1; omega
    obtain ⟨hwvL_w, h2wvL, _⟩ := mul_three_bounds (by omega) hwvL1 h4v
    have h2wvL_pow : 2 ^ (2 * wvL) < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two h2wvL)
  all_goals try (unfold SplitParamsPre; exact ⟨hw6, h8, h4k, h4v⟩)
  all_goals try exact hal1.trans (Nat.pow_lt_pow_right Nat.one_lt_two hwvL_w)
  all_goals try (
    have hsh : (al + 1) <<< wvL < 2 ^ (2 * wvL) := by
      rw [Nat.shiftLeft_eq]
      calc (al + 1) * 2 ^ wvL < 2 ^ wvL * 2 ^ wvL :=
            Nat.mul_lt_mul_of_pos_right hal1 (Nat.two_pow_pos wvL)
        _ = 2 ^ (2 * wvL) := by rw [← Nat.pow_add, Nat.two_mul]
    exact hsh.trans h2wvL_pow)
  all_goals try (
    have hsum : al + ((al + 1) <<< wvL) < 2 ^ (2 * wvL) := by
      rw [Nat.shiftLeft_eq]
      have hle : (al + 1) + 1 ≤ 2 ^ wvL := hal1
      calc al + (al + 1) * 2 ^ wvL < ((al + 1) + 1) * 2 ^ wvL := by ring_nf; omega
        _ ≤ 2 ^ wvL * 2 ^ wvL := Nat.mul_le_mul_right _ hle
        _ = 2 ^ (2 * wvL) := by rw [← Nat.pow_add, Nat.two_mul]
    exact hsum.trans h2wvL_pow)
  all_goals omega

@[simp] private theorem runClient_state_computeRootSplitProg
    (d : (SplitParams × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (computeRootSplitProg d))) = s := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold computeRootSplitProg; simp

private def execRootSplitProg :
    (BTreeSliceCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog ℕ
  | ((ctx, (hdrBase, nodeBase)), ((al, rt), rootNd)) =>
    if al < ctxNs ctx - 1 then do
      let res ← computeRootSplitProg ((ctxSplitParams ctx, al), rootNd)
      writeTwoNodesAtProg (ctxNodeAt ctx nodeBase, ((al, res.1.1), (al + 1, res.1.2)))
      writeSliceNodeAtProg ((ctxNodeAt ctx nodeBase, rt), res.2)
      writeSliceHdrAtProg (ctxHdrAt ctx hdrBase, (0, al + 2))
      pure rt
    else pure rt

private def ExecRootSplitPre (w : ℕ) :
    (BTreeSliceCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | ((ctx, (hdrBase, nodeBase)), _args), s =>
    let L := (unpackSliceCtx ctx).1
    SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier ∧
      SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧
      1 ≤ L.nSlice ∧ L.nSlice < 2 ^ L.wValLane ∧ L.nSlice < 2 ^ w

private theorem realizesBounded_execRootSplit :
    RealizesBounded .exact execRootSplitProg
      (WordEncoding.encode (α := (BTreeSliceCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ))
      ExecRootSplitPre (fun _ _ => 0) := by
  have hcr := realizesBounded_computeRootSplit
  have hw2 := realizesBounded_writeTwoNodesAt
  have hwn := realizesBounded_writeSliceNodeAt
  have hwh := realizesBounded_writeSliceHdrAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨hdrBase, nodeBase⟩⟩,
      ⟨⟨al, rt⟩, ⟨mw, ⟨kw, vw⟩⟩⟩⟩
    dsimp only [ExecRootSplitPre, unpackSliceCtx] at h
    obtain ⟨hnode, hhdr, hsp, hns1, hns_val, hns_w⟩ := h
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hsp.1
    try dsimp only [ctxNs] at *
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_computeRootSplitProg,
      runClient_frontier_writeTwoNodesAtProg, runClient_frontier_writeSliceNodeAtProg] at *)
  all_goals try assumption
  all_goals try omega
  all_goals (
    unfold ComputeRootSplitPre
    dsimp only [ctxSplitParams, ctxFpWvL, ctxTm]
    exact ⟨hsp, (by omega : al + 1 < ns).trans hns_val⟩)

private def prepareNonEmptyRootProg :
    (BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((ctx, (hdrBase, nodeBase)), hdr) => do
    let rt ← pure hdr.2
    let rootNd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, rt)
    if (rootNd.1 >>> 1) = 2 * ctxTm ctx - 1 then
      execRootSplitProg ((ctx, (hdrBase, nodeBase)), ((hdr.1, rt), rootNd))
    else pure rt

private def PrepareNonEmptyPre (w : ℕ) :
    (BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | ((ctx, (hdrBase, nodeBase)), _hdr), s =>
    let L := (unpackSliceCtx ctx).1
    SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier ∧
      SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧
      1 ≤ L.nSlice ∧ L.nSlice < 2 ^ L.wValLane ∧ L.nSlice < 2 ^ w

private theorem realizesBounded_prepareNonEmptyRoot :
    RealizesBounded .exact prepareNonEmptyRootProg
      (WordEncoding.encode (α := (BTreeSliceCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      PrepareNonEmptyPre (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hex := realizesBounded_execRootSplit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨hdrBase, nodeBase⟩⟩, ⟨al, rt⟩⟩
    dsimp only [PrepareNonEmptyPre, unpackSliceCtx] at h
    obtain ⟨hnode, hhdr, hsp, hns1, hns_val, hns_w⟩ := h
    have ⟨hw6, h8, h4k, h4v⟩ := hsp
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨_, _, h2t_w, _⟩ := mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have h2t_fits : 2 * tm < 2 ^ w := h2t_w.trans hw_lt
    try dsimp only [ctxTm, Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceNodeAtProg] at *)
  all_goals try assumption
  all_goals try omega
  all_goals (
    unfold ExecRootSplitPre
    dsimp only [unpackSliceCtx]
    exact ⟨hnode, hhdr, hsp, hns1, hns_val, hns_w⟩)

/-- `ensureRootSlice` followed by `splitRootIfFull` in `Memory.Prog`, returning `sl1.root`. -/
private def prepareRootBoundedProg : BTreeSliceCtx → Memory.Prog ℕ
  | ctx => do
    let hdrBase ← pure (16 * ctxB ctx + 6 + 2 * ctxRole ctx)
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let hdr ← readSliceHdrAtProg (ctxHdrAt ctx hdrBase)
    if hdr.1 = 0 then
      initEmptyRootAtProg (ctxNodeAt ctx nodeBase, ctxHdrAt ctx hdrBase)
    else
      prepareNonEmptyRootProg ((ctx, (hdrBase, nodeBase)), hdr)

private theorem realizesBounded_prepareRoot :
    RealizesBounded .exact prepareRootBoundedProg
      (WordEncoding.encode (α := BTreeSliceCtx))
      (WordEncoding.encode (α := ℕ))
      BTreeSlicePre (fun _ _ => 0) := by
  have hrh := realizesBounded_readSliceHdrAt
  have hie := realizesBounded_initEmptyRootAt
  have hpne := realizesBounded_prepareNonEmptyRoot
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    dsimp only [BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨hvL, hb, hrole⟩ := h
    obtain ⟨hf16, hf6, hf2, hf1, hf0, hfb16, hfb6, hfr2, hfhb, hhdr⟩ := hvL.hdr_facts hb hrole
    obtain ⟨hf3, _, _, _, hfb3, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hpb : pb ≤ w := hvL.2.2.1
    have hns_val : ns < 2 ^ wvL := hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hns64 : 64 ≤ ns := hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hns_pb : ns < 2 ^ pb := hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hns_w : ns < 2 ^ w := hns_pb.trans_le (Nat.pow_le_pow_right (by decide) hpb)
    try dsimp only [ctxNodeAt, ctxHdrAt, ctxMbOb, ctxPbWv, ctxMb, ctxOm, ctxOkOv,
      ctxWv, ctxWm, ctxWkWvl, ctxNs, ctxB, ctxRole] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceHdrAtProg] at *)
  all_goals try assumption
  all_goals (
    unfold PrepareNonEmptyPre
    dsimp only [unpackSliceCtx]
    exact ⟨hnode, hhdr, hsp, by omega, hns_val, hns_w⟩)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

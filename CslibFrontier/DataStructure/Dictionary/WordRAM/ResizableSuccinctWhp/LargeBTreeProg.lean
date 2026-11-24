/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeBase
-- Private B+-tree step helpers shared across the LargeBTreeBase/LargeBTreeProg split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeBase
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bit-Packed SWAR B+-Tree Insertion and Exact `ValidWhpSlice` Refinement

This module builds on `LargeBTreeBase` to define and certify the top-down proactive-splitting
insertion primitive `btreeInsertBoundedProg` (`RealizesBounded .exact`, `¬ReadsWidth`), and proves
exact `extractBTreeSlice` functional refinement under `ValidWhpSlice` together with memory-frame
preservation across all other `(b', role') ≠ (b, role)` slices and bucket metadata slots for
lookup, deletion, update, and insertion.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.btreeInsertBoundedProg`:
  top-down proactive-splitting SWAR B+-tree insertion in `Memory.Prog`.

## Main results

* `realizesBounded_btreeInsert`: parameter-free `RealizesBounded .exact` certificate
  (`¬ReadsWidth`) for `btreeInsertBoundedProg`.
* `btreeLookupBoundedProg_spec`, `btreeDeleteBoundedProg_spec`, `btreeUpdateBoundedProg_spec`,
  `btreeInsertBoundedProg_spec`: exact `ValidWhpSlice` refinement and non-interference theorems.
* `runClient_state_btreeLookupBoundedProg`, `clientState_btreeLookupBoundedProg`,
  `btreeDeleteBoundedProg_frame`, `btreeUpdateBoundedProg_frame`, `btreeInsertBoundedProg_frame`:
  unconditional read-state and memory-frame preservation lemmas.

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

/-- Pure word computation `((leftNd, rightNd), (parentNd', sep))` for child splitting (12 words). -/
private def computeChildSplitProg :
    ((SplitParams × (ℕ × ℕ)) × ℕ) × ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) →
      Memory.Prog (((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ((ℕ × (ℕ × ℕ)) × ℕ))
  | ((((spP, (r, cnt)), al), (nd, childNd))) => do
    let fp ← pure spP.1.1
    let wvL ← pure spP.1.2
    let sp ← splitFullNodeAtProg (spP, childNd)
    let sep ← pure sp.1.2
    let pKw ← wordInsertAtBoundedProg (((fp + 2, r), sep), nd.2.1)
    let pVw ← wordInsertAtBoundedProg (((wvL, r + 1), al), nd.2.2)
    pure ((sp.1.1, sp.2), ((2 * (cnt + 1), (pKw, pVw)), sep))

private def ComputeChildSplitPre (w : ℕ) :
    ((SplitParams × (ℕ × ℕ)) × ℕ) × ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | ((((((fp, wvL), tm), (r, cnt)), al), (nd, _childNd))), _s =>
    SplitParamsPre w ((fp, wvL), tm) ∧ 1 ≤ wvL ∧ r < 2 * tm ∧ cnt + 1 < 2 ^ w ∧
      2 * (cnt + 1) < 2 ^ w ∧ al < 2 ^ wvL ∧
      nd.2.1 < 2 ^ (2 * tm * (fp + 2)) ∧ nd.2.2 < 2 ^ (2 * tm * wvL)

private theorem realizesBounded_computeChildSplit :
    RealizesBounded .exact computeChildSplitProg
      (WordEncoding.encode (α := ((SplitParams × (ℕ × ℕ)) × ℕ) × ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ((ℕ × (ℕ × ℕ)) × ℕ)))
      ComputeChildSplitPre (fun _ _ => 0) := by
  have hsp := realizesBounded_splitFullNodeAt
  have hwi := realizesBounded_wordInsertAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨fp, wvL⟩, tm⟩, ⟨r, cnt⟩⟩, al⟩, ⟨⟨mw, ⟨kw, vw⟩⟩, ⟨cmw, ⟨ckw, cvw⟩⟩⟩⟩
    obtain ⟨hspP, hwvL1, hr_lt, hcnt1, h2cnt, hal, hkw, hvw⟩ := h
    have ⟨hw6, h8, h4k, h4v⟩ := hspP
    try dsimp only at *
    try dsimp only [Fits] at *
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    obtain ⟨hfp2_w, _, h2t_w, _, _, _, _, _, h2t1_fp⟩ :=
      mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    obtain ⟨_, _, _, _, _, _, _, _, h2t1_wv⟩ := mul_three_bounds (by omega) hwvL1 h4v
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have hr1_w : r + 1 < 2 ^ w := (by omega : r + 1 ≤ 2 * tm).trans_lt (h2t_w.trans hw_lt)
    try simp only [StateTransitionSpec.clientState, runClient_state_splitFullNodeAtProg,
      runClient_state_wordInsertAtBoundedProg] at *)
  all_goals try exact hspP
  all_goals try assumption
  all_goals try omega
  all_goals try (
    unfold WordInsertAtPre
    exact ⟨2 * tm, by omega, h2t1_wv, hal, hvw⟩)
  all_goals (
    set L0 : BTreeEpochLayout :=
      ⟨0, 0, 0, 0, 0, 0, w, 0, 0, 0, fp, wvL, tm, 0, 0⟩
    have hsp_s := splitFullNodeAtProg_spec L0 ⟨cmw, ckw, cvw⟩ s
    dsimp only [L0] at hsp_s
    simp only [hsp_s.1] at *
    unfold WordInsertAtPre
    refine ⟨2 * tm, by omega, h2t1_fp, ?_, hkw⟩
    dsimp only [splitFullNode]; split_ifs <;> exact laneGet_lt _ _ _)

@[simp] private theorem runClient_state_computeChildSplitProg
    (d : ((SplitParams × (ℕ × ℕ)) × ℕ) × ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)))) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (computeChildSplitProg d))) = s := by
  rcases d with ⟨⟨⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩, _⟩, ⟨⟨_, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩⟩
  unfold computeChildSplitProg; simp

private def finishChildSplitWritesProg :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) ×
      ((ℕ × (ℕ × ℕ)) × (((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ((ℕ × (ℕ × ℕ)) × ℕ))) →
      Memory.Prog ℕ
  | (((ctx, q), (hdrBase, nodeBase)), ((al, (cur, childIdx)), res)) => do
    writeTwoNodesAtProg (ctxNodeAt ctx nodeBase, ((childIdx, res.1.1), (al, res.1.2)))
    writeSliceNodeAtProg ((ctxNodeAt ctx nodeBase, cur), res.2.1)
    writeSliceHdrAtProg (ctxHdrAt ctx hdrBase, (0, al + 1))
    if res.2.2 < q then pure al else pure childIdx

private def FinishChildWritesPre (w : ℕ) :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) ×
      ((ℕ × (ℕ × ℕ)) × (((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ((ℕ × (ℕ × ℕ)) × ℕ))) →
      Memory.State → Prop
  | (((ctx, _q), (hdrBase, nodeBase)), ((al, _cc), _res)), s =>
    SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier ∧ al + 1 < 2 ^ w

private theorem realizesBounded_finishChildSplitWrites :
    RealizesBounded .exact finishChildSplitWritesProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) ×
        ((ℕ × (ℕ × ℕ)) × (((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ((ℕ × (ℕ × ℕ)) × ℕ)))))
      (WordEncoding.encode (α := ℕ))
      FinishChildWritesPre (fun _ _ => 0) := by
  have hw2 := realizesBounded_writeTwoNodesAt
  have hwn := realizesBounded_writeSliceNodeAt
  have hwh := realizesBounded_writeSliceHdrAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨ctx, q⟩, ⟨hdrBase, nodeBase⟩⟩, ⟨⟨al, ⟨cur, childIdx⟩⟩, res⟩⟩
    obtain ⟨hnode, hhdr, hal1⟩ := h
    have hw6 : 6 ≤ w := by
      rcases hhdr with ⟨_, hw6, _⟩; exact hw6
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    try dsimp only at *
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_frontier_writeTwoNodesAtProg,
      runClient_frontier_writeSliceNodeAtProg] at *)
  all_goals assumption

private def splitChildBodyProg :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.Prog ℕ
  | (((ctx, q), (hdrBase, al)), (cur, (r, childIdx))) => do
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let nd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, cur)
    let childNd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, childIdx)
    let cnt ← pure (nd.1 >>> 1)
    let res ← computeChildSplitProg (((ctxSplitParams ctx, (r, cnt)), al), (nd, childNd))
    finishChildSplitWritesProg (((ctx, q), (hdrBase, nodeBase)), ((al, (cur, childIdx)), res))

private def SplitChildBodyPre (w : ℕ) :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (((ctx, _q), (hdrBase, al)), (_cur, (r, _childIdx))), s =>
    let L := (unpackSliceCtx ctx).1
    BTreeSlicePre w ctx s ∧ SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier ∧
      r < 2 * L.tMin ∧ al < L.nSlice

private theorem realizesBounded_splitChildBody :
    RealizesBounded .exact splitChildBodyProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ))
      SplitChildBodyPre (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hcc := realizesBounded_computeChildSplit
  have hfw := realizesBounded_finishChildSplitWrites
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, q⟩, ⟨hdrBase, al⟩⟩, ⟨cur, ⟨r, childIdx⟩⟩⟩
    dsimp only [SplitChildBodyPre, BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨⟨hvL, hb, hrole⟩, hhdr, hr_lt, hal_ns⟩ := h
    obtain ⟨hf3, _, _, _, hfb3, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hpb : pb ≤ w := hvL.2.2.1
    have hwvL1 : 1 ≤ wvL := hvL.2.2.2.2.2.1
    have hwm : wm < w := hvL.2.2.2.2.2.2.1
    have hwk : wk = 2 * tm * (fp + 2) := hvL.2.2.2.2.2.2.2.1
    have hwvl : wvl = 2 * tm * wvL := hvL.2.2.2.2.2.2.2.2.1
    have hns_val : ns < 2 ^ wvL := hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hns_pb : ns < 2 ^ pb := hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hns_w : ns < 2 ^ w := hns_pb.trans_le (Nat.pow_le_pow_right (by decide) hpb)
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hsp.1
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceNodeAtProg,
      runClient_state_computeChildSplitProg] at *)
  all_goals try assumption
  all_goals try (
    unfold FinishChildWritesPre
    dsimp only [ctxNodeAt, ctxHdrAt, ctxMb, ctxOm, ctxOkOv, ctxWv, ctxWm,
      ctxWkWvl, ctxNs, ctxMbOb, ctxPbWv]
    exact ⟨hnode, hhdr, (by omega : al + 1 ≤ ns).trans_lt hns_w⟩)
  all_goals (
    set L0 : BTreeEpochLayout :=
      ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩
    have hrn_cur := readSliceNodeAtProg_spec L0 b role cur s
    dsimp only [L0, BTreeEpochLayout.toNodeCtx] at hrn_cur
    simp only [hrn_cur.1] at *
    set nd0 := (extractBTreeSlice L0 b role s.mem).nodes cur
    obtain ⟨hmw_lt, hkw_raw, hvw_raw⟩ := extractBTreeSlice_node_bounds L0 b role cur s.mem
    obtain ⟨hc1, h2c, _⟩ := metaWord_shiftRight_bound (le_trans (by decide) hsp.1) hwm hmw_lt
    unfold ComputeChildSplitPre
    dsimp only [ctxSplitParams, ctxFpWvL, ctxTm]
    exact ⟨hsp, hwvL1, hr_lt, hc1, h2c, hal_ns.trans hns_val, hwk ▸ hkw_raw, hwvl ▸ hvw_raw⟩)

/-- Proactive child-split step of `descendSplitToLeaf` when child `childIdx` is full. -/
private def splitChildAndStepProg :
    (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog ℕ
  | ((ctx, q), (cur, (r, childIdx))) => do
    let hdrBase ← pure (16 * ctxB ctx + 6 + 2 * ctxRole ctx)
    let hdr ← readSliceHdrAtProg (ctxHdrAt ctx hdrBase)
    if hdr.1 < ctxNs ctx then
      splitChildBodyProg (((ctx, q), (hdrBase, hdr.1)), (cur, (r, childIdx)))
    else pure childIdx

private def SplitChildStepPre (w : ℕ) :
    (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((ctx, q), (_cur, (r, _childIdx))), s =>
    let L := (unpackSliceCtx ctx).1
    BTreeSlicePre w ctx s ∧ q < 2 ^ L.fpBits ∧ r < 2 * L.tMin

private theorem realizesBounded_splitChildAndStep :
    RealizesBounded .exact splitChildAndStepProg
      (WordEncoding.encode (α := (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ))
      SplitChildStepPre (fun _ _ => 0) := by
  have hrh := realizesBounded_readSliceHdrAt
  have hbd := realizesBounded_splitChildBody
  realize
  all_goals (
    rcases d with ⟨⟨ctx, q⟩, ⟨cur, ⟨r, childIdx⟩⟩⟩
    obtain ⟨hslice, hq, hr_lt⟩ := h
    have hslice_u := hslice
    rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    dsimp only [BTreeSlicePre, unpackSliceCtx] at hslice_u hr_lt
    obtain ⟨hvL, hb, hrole⟩ := hslice_u
    obtain ⟨hf16, hf6, hf2, hf1, hf0, hfb16, hfb6, hfr2, hfhb, hhdr⟩ := hvL.hdr_facts hb hrole
    dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr
    try dsimp only [ctxNs] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceHdrAtProg] at *)
  all_goals try assumption
  all_goals (
    unfold SplitChildBodyPre
    dsimp only [unpackSliceCtx, ctxHdrAt, ctxMbOb, ctxPbWv]
    exact ⟨hslice, hhdr, hr_lt, by assumption⟩)

private def descendSplitBranchProg :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.Prog ℕ
  | (((ctx, q), (nodeBase, cur)), nd) => do
    let cnt ← pure (nd.1 >>> 1)
    let r ← swarRankClampedProg (((ctxFp ctx, ctxTm ctx), cnt), (q, nd.2.1))
    let childIdx ← laneGetBoundedProg ((ctxWvL ctx, nd.2.2), r)
    let childNd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, childIdx)
    if (childNd.1 >>> 1) = 2 * ctxTm ctx - 1 then
      splitChildAndStepProg ((ctx, q), (cur, (r, childIdx)))
    else
      pure childIdx

private def DescendSplitBranchPre (w : ℕ) :
    ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (((ctx, q), (nodeBase, _cur)), nd), s =>
    let L := (unpackSliceCtx ctx).1
    BTreeSlicePre w ctx s ∧ SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier ∧
      SplitParamsPre w ((L.fpBits, L.wValLane), L.tMin) ∧ 1 ≤ L.wValLane ∧
      q < 2 ^ L.fpBits ∧ nd.2.1 < 2 ^ (2 * L.tMin * (L.fpBits + 2))

private theorem realizesBounded_descendSplitBranch :
    RealizesBounded .exact descendSplitBranchProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ))
      DescendSplitBranchPre (fun _ _ => 0) := by
  have hsr := realizesBounded_swarRankClamped
  have hlg := realizesBounded_laneGet
  have hrn := realizesBounded_readSliceNodeAt
  have hsc := realizesBounded_splitChildAndStep
  realize
  all_goals (
    rcases d with ⟨⟨⟨ctx, q⟩, ⟨nodeBase, cur⟩⟩, ⟨mw, ⟨kw, vw⟩⟩⟩
    obtain ⟨hslice, hnode, hsp, hwvL1, hq, hkw⟩ := h
    rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    dsimp only [unpackSliceCtx] at hsp hwvL1 hq hkw
    have ⟨hw6, h8, h4k, h4v⟩ := hsp
    try dsimp only [ctxFp, ctxTm, ctxWvL, Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg, runClient_state_readSliceNodeAtProg] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hwvL_w, _, h2t_w, _⟩ := mul_three_bounds (by omega) hwvL1 h4v
    have h2t_fits : 2 * tm < 2 ^ w := h2t_w.trans hw_lt
    have hr_lt := swarRankClampedProg_lt (fpBits := fp) (tMin := tm) (m := mw >>> 1) (q := q)
      (kw := kw) (by omega) s)
  all_goals try assumption
  all_goals try omega
  all_goals try (unfold SwarRankClampedPre; exact ⟨by omega, h4k, hq, hkw⟩)
  all_goals try (
    unfold LaneGetPre
    exact ⟨hwvL_w, (idx_mul_lt_of_four_mul hr_lt.le h4v).trans hw_lt⟩)
  all_goals (
    unfold SplitChildStepPre
    dsimp only [unpackSliceCtx]
    exact ⟨hslice, hq, hr_lt⟩)

/-- Single step of `descendSplitToLeaf` in `Memory.Prog` (3 input `FVar`s, `ctx` packed). -/
private def descendSplitStepProg : (BTreeSliceCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, q), cur) => do
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let nd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, cur)
    if nd.1 % 2 = 1 then pure cur
    else descendSplitBranchProg (((ctx, q), (nodeBase, cur)), nd)

private theorem realizesBounded_descendSplitStep :
    RealizesBounded .exact descendSplitStepProg
      (WordEncoding.encode (α := (BTreeSliceCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      DescendStepPre (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hbr := realizesBounded_descendSplitBranch
  realize
  all_goals (
    rcases d with ⟨⟨ctx, q⟩, cur⟩
    have hslice0 : BTreeSlicePre w ctx s := h.1
    rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
    have hpre_u := h
    dsimp only [DescendStepPre, BTreeSlicePre, unpackSliceCtx] at hpre_u
    obtain ⟨⟨hvL, hb, hrole⟩, hq⟩ := hpre_u
    obtain ⟨hf3, hf2, hf1, hf0, hfb3, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hwvL1 : 1 ≤ wvL := hvL.2.2.2.2.2.1
    have hwk : wk = 2 * tm * (fp + 2) := hvL.2.2.2.2.2.2.2.1
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceNodeAtProg] at *)
  all_goals try assumption
  all_goals try decide
  all_goals (
    set L0 : BTreeEpochLayout :=
      ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩
    have hrn_cur := readSliceNodeAtProg_spec L0 b role cur s
    dsimp only [L0, BTreeEpochLayout.toNodeCtx] at hrn_cur
    dsimp only [ctxNodeAt, ctxB, ctxRole, ctxNs, ctxMb, ctxOm, ctxOkOv, ctxWv, ctxWm, ctxWkWvl]
    rw [hrn_cur.1]
    have hkw_lt : ((extractBTreeSlice L0 b role s.mem).nodes cur).keysWord <
        2 ^ (2 * tm * (fp + 2)) :=
      hwk ▸ (extractBTreeSlice_node_bounds L0 b role cur s.mem).2.1
    unfold DescendSplitBranchPre
    dsimp only [unpackSliceCtx]
    exact ⟨hslice0, hnode, hsp, hwvL1, hq, hkw_lt⟩)

private theorem memoryCost_descendSplitStepProg_pos
    (x : (BTreeSliceCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (descendSplitStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩,
    ⟨⟨⟨_, _⟩, ⟨_, ns⟩⟩, ⟨_, ⟨_, _⟩⟩⟩⟩, _⟩, cur⟩
  unfold descendSplitStepProg readSliceNodeAtProg
  simp only [Realization.memoryCost_bind', pure_bind]
  by_cases hu : cur < ns <;>
    simp only [hu, ↓reduceIte, Realization.memoryCost_bind',
      memoryCost_readPackedCompGenProg, runClient_state_readPackedCompGenProg] <;>
    omega

private def descendSplitLoopProg : ((BTreeSliceCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cq, cur), fuel) => iterate descendSplitStepProg cq fuel cur

private theorem realizesBounded_descendSplitLoop :
    RealizesBounded .exact descendSplitLoopProg
      (WordEncoding.encode (α := ((BTreeSliceCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cq, cur), fuel) s =>
        iterationSafe descendSplitStepProg DescendStepPre w cq fuel cur s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BTreeSliceCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_descendSplitStep
    memoryCost_descendSplitStepProg_pos

private def leafInsertShiftProg :
    (SplitParams × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((((fp, wvL), _tm), (q, val)), ((cnt, r), (_mw, (kw, vw)))) => do
    let kw' ← wordInsertAtBoundedProg (((fp + 2, r), q), kw)
    let vw' ← wordInsertAtBoundedProg (((wvL, r), val), vw)
    pure (1 + 2 * (cnt + 1), (kw', vw'))

private def LeafInsertShiftPre (w : ℕ) :
    (SplitParams × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | ((((fp, wvL), tm), (q, val)), ((cnt, r), (_mw, (kw, vw)))), _s =>
    SplitParamsPre w ((fp, wvL), tm) ∧ 1 ≤ wvL ∧ r < 2 * tm ∧
      cnt + 1 < 2 ^ w ∧ 2 * (cnt + 1) < 2 ^ w ∧ 1 + 2 * (cnt + 1) < 2 ^ w ∧
      q < 2 ^ fp ∧ val < 2 ^ wvL ∧ kw < 2 ^ (2 * tm * (fp + 2)) ∧ vw < 2 ^ (2 * tm * wvL)

private theorem realizesBounded_leafInsertShift :
    RealizesBounded .exact leafInsertShiftProg
      (WordEncoding.encode (α := (SplitParams × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      LeafInsertShiftPre (fun _ _ => 0) := by
  have hwi := realizesBounded_wordInsertAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨fp, wvL⟩, tm⟩, ⟨q, val⟩⟩, ⟨⟨cnt, r⟩, ⟨mw, ⟨kw, vw⟩⟩⟩⟩
    obtain ⟨⟨hw6, h8, h4k, h4v⟩, hwvL1, hr_lt, hc1, h2c, h12c, hq, hval, hkw, hvw⟩ := h
    try dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_wordInsertAtBoundedProg] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _, _, _, _, _, _, _, h2t1_fp⟩ :=
      mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    obtain ⟨_, _, _, _, _, _, _, _, h2t1_wv⟩ := mul_three_bounds (by omega) hwvL1 h4v
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt)
  all_goals try omega
  all_goals try (
    unfold WordInsertAtPre
    exact ⟨2 * tm, by omega, h2t1_fp,
      hq.trans (Nat.pow_lt_pow_right Nat.one_lt_two (by omega)), hkw⟩)
  all_goals (
    unfold WordInsertAtPre
    exact ⟨2 * tm, by omega, h2t1_wv, hval, hvw⟩)

private def leafInsertHitOrShiftProg :
    (SplitParams × (ℕ × ℕ)) × (((ℕ × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((spP, qv), (((cnt, r), kAt), nd)) =>
    if kAt = qv.1 then do
      let vw' ← wordUpdateAtBoundedProg (((spP.1.2, r), qv.2), nd.2.2)
      pure (nd.1, (nd.2.1, vw'))
    else
      leafInsertShiftProg ((spP, qv), ((cnt, r), nd))

private def LeafInsertHitPre (w : ℕ) :
    (SplitParams × (ℕ × ℕ)) × (((ℕ × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.State → Prop
  | ((spP, qv), (((cnt, r), _kAt), nd)), s =>
    LeafInsertShiftPre w ((spP, qv), ((cnt, r), nd)) s

private theorem realizesBounded_leafInsertHitOrShift :
    RealizesBounded .exact leafInsertHitOrShiftProg
      (WordEncoding.encode (α := (SplitParams × (ℕ × ℕ)) × (((ℕ × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      LeafInsertHitPre (fun _ _ => 0) := by
  have hwu := realizesBounded_wordUpdateAt
  have hsh := realizesBounded_leafInsertShift
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨fp, wvL⟩, tm⟩, ⟨q, val⟩⟩, ⟨⟨⟨cnt, r⟩, kAt⟩, ⟨mw, ⟨kw, vw⟩⟩⟩⟩
    have hsh0 : LeafInsertShiftPre w
        (((((fp, wvL), tm), (q, val)), ((cnt, r), (mw, (kw, vw))))) s := h
    obtain ⟨⟨hw6, h8, h4k, h4v⟩, hwvL1, hr_lt, hc1, h2c, h12c, hq, hval, hkw, hvw⟩ := h
    try dsimp only at *
    obtain ⟨_, _, _, _, _, _, _, _, h2t1_wv⟩ := mul_three_bounds (by omega) hwvL1 h4v)
  all_goals try exact hsh0
  all_goals (
    unfold WordUpdateAtPre
    exact ⟨2 * tm, hwvL1, hr_lt.le, h2t1_wv, hval,
      hvw.trans (Nat.pow_lt_pow_right Nat.one_lt_two (by rw [Nat.add_one_mul (2 * tm)]; omega))⟩)

/-- Pure word computation `(mw', (kw', vw'))` for `finishLeafInsert` (8 words, zero memory ops). -/
private def computeLeafInsertNodeProg :
    (SplitParams × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((((fp, wvL), tm), (q, val)), nd) => do
    let cnt ← pure (nd.1 >>> 1)
    let r ← swarRankClampedProg (((fp, tm), cnt), (q, nd.2.1))
    let kAt ← laneGetBoundedProg ((fp + 2, nd.2.1), r)
    if r < cnt then
      leafInsertHitOrShiftProg ((((fp, wvL), tm), (q, val)), (((cnt, r), kAt), nd))
    else
      leafInsertShiftProg ((((fp, wvL), tm), (q, val)), ((cnt, r), nd))

private def ComputeLeafInsertPre (w : ℕ) :
    (SplitParams × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((((fp, wvL), tm), (q, val)), (mw, (kw, vw))), _s =>
    SplitParamsPre w ((fp, wvL), tm) ∧ 1 ≤ wvL ∧
      mw >>> 1 + 1 < 2 ^ w ∧ 2 * (mw >>> 1 + 1) < 2 ^ w ∧ 1 + 2 * (mw >>> 1 + 1) < 2 ^ w ∧
      q < 2 ^ fp ∧ val < 2 ^ wvL ∧
      kw < 2 ^ (2 * tm * (fp + 2)) ∧ vw < 2 ^ (2 * tm * wvL)

private theorem realizesBounded_computeLeafInsertNode :
    RealizesBounded .exact computeLeafInsertNodeProg
      (WordEncoding.encode (α := (SplitParams × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      ComputeLeafInsertPre (fun _ _ => 0) := by
  have hsr := realizesBounded_swarRankClamped
  have hlg := realizesBounded_laneGet
  have hhs := realizesBounded_leafInsertHitOrShift
  have hsh := realizesBounded_leafInsertShift
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨fp, wvL⟩, tm⟩, ⟨q, val⟩⟩, ⟨mw, ⟨kw, vw⟩⟩⟩
    obtain ⟨hsp, hwvL1, hc1, h2c, h12c, hq, hval, hkw, hvw⟩ := h
    have ⟨hw6, h8, h4k, h4v⟩ := hsp
    try dsimp only [Fits] at *
    have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
    have hpow6 : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw6
    obtain ⟨hfp2_w, _⟩ := mul_three_bounds (by omega) (by omega : 1 ≤ fp + 2) h4k
    have hfp2_fits : fp + 2 < 2 ^ w := hfp2_w.trans hw_lt
    have hr_lt := swarRankClampedProg_lt (fpBits := fp) (tMin := tm)
      (m := mw >>> 1) (q := q) (kw := kw) (by omega) s
    try simp only [StateTransitionSpec.clientState, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg] at *)
  all_goals try omega
  all_goals try (unfold SwarRankClampedPre; exact ⟨by omega, h4k, hq, hkw⟩)
  all_goals try (
    unfold LaneGetPre
    exact ⟨hfp2_w, (idx_mul_lt_of_four_mul hr_lt.le h4k).trans hw_lt⟩)
  all_goals (
    try unfold LeafInsertHitPre
    unfold LeafInsertShiftPre
    exact ⟨hsp, hwvL1, hr_lt, hc1, h2c, h12c, hq, hval, hkw, hvw⟩)

@[simp] private theorem runClient_state_computeLeafInsertNodeProg
    (d : (SplitParams × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (computeLeafInsertNodeProg d))) = s := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold computeLeafInsertNodeProg leafInsertHitOrShiftProg leafInsertShiftProg
  simp only [pure_bind, prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_swarRankClampedProg, runClient_state_laneGetBoundedProg]
  repeat (split_ifs <;> simp)

/-- `finishLeafInsert` tail of `btreeInsert` in `Memory.Prog` (4 straight-line binds). -/
private def finishLeafInsertBoundedProg :
    BTreeSliceCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (ctx, (leafIdx, (q, val))) => do
    let nodeBase ← pure ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)
    let nd ← readSliceNodeAtProg (ctxNodeAt ctx nodeBase, leafIdx)
    let nd' ← computeLeafInsertNodeProg ((ctxSplitParams ctx, (q, val)), nd)
    writeSliceNodeAtProg ((ctxNodeAt ctx nodeBase, leafIdx), nd')

private def FinishLeafInsertPre (w : ℕ) :
    BTreeSliceCtx × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (ctx, (_leafIdx, (q, val))), s => BTreeKeyValOpPre w (ctx, (q, val)) s

private theorem realizesBounded_finishLeafInsert :
    RealizesBounded .exact finishLeafInsertBoundedProg
      (WordEncoding.encode (α := BTreeSliceCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      FinishLeafInsertPre (fun _ _ => 0) := by
  have hrn := realizesBounded_readSliceNodeAt
  have hcl := realizesBounded_computeLeafInsertNode
  have hwn := realizesBounded_writeSliceNodeAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
      ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩, ⟨leafIdx, ⟨q, val⟩⟩⟩
    dsimp only [FinishLeafInsertPre, BTreeKeyValOpPre, BTreeSlicePre, unpackSliceCtx] at h
    obtain ⟨⟨hvL, hb, hrole⟩, hq, hval⟩ := h
    obtain ⟨hf3, hf2, hf1, hf0, hfb3, hfbr, hfnb, hnode⟩ := hvL.node_facts hb hrole
    have hsp := hvL.split_facts
    dsimp only [BTreeEpochLayout.toNodeCtx] at hnode
    dsimp only [BTreeEpochLayout.Valid] at hvL
    have hwvL1 : 1 ≤ wvL := hvL.2.2.2.2.2.1
    have hwm : wm < w := hvL.2.2.2.2.2.2.1
    have hwk : wk = 2 * tm * (fp + 2) := hvL.2.2.2.2.2.2.2.1
    have hwvl : wvl = 2 * tm * wvL := hvL.2.2.2.2.2.2.2.2.1
    try simp only [StateTransitionSpec.clientState, runClient_state_readSliceNodeAtProg,
      runClient_state_computeLeafInsertNodeProg] at *)
  all_goals try assumption
  all_goals (
    set L0 : BTreeEpochLayout :=
      ⟨mb, ob, om, ok, ov, pb, wv, wm, wk, wvl, fp, wvL, tm, ns, nb⟩
    have hrn_lf := readSliceNodeAtProg_spec L0 b role leafIdx s
    dsimp only [L0, BTreeEpochLayout.toNodeCtx] at hrn_lf
    simp only [hrn_lf.1] at *
    set nd0 := (extractBTreeSlice L0 b role s.mem).nodes leafIdx
    obtain ⟨hmw_lt, hkw_raw, hvw_raw⟩ := extractBTreeSlice_node_bounds L0 b role leafIdx s.mem
    have hkw_lt : nd0.keysWord < 2 ^ (2 * tm * (fp + 2)) := hwk ▸ hkw_raw
    have hvw_lt : nd0.valsWord < 2 ^ (2 * tm * wvL) := hwvl ▸ hvw_raw
    obtain ⟨hc1, h2c, h12c⟩ := metaWord_shiftRight_bound (le_trans (by decide) hsp.1)
      hwm hmw_lt
    unfold ComputeLeafInsertPre
    dsimp only [ctxSplitParams, ctxFpWvL, ctxTm]
    exact ⟨hsp, hwvL1, hc1, h2c, h12c, hq, hval, hkw_lt, hvw_lt⟩)

/-- `btreeInsert` in `Memory.Prog` (`RealizesBounded .exact`, `¬ReadsWidth`). -/
def btreeInsertBoundedProg : BTreeSliceCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (ctx, (q, val)) => do
    let rt ← prepareRootBoundedProg ctx
    let leafIdx ← descendSplitLoopProg (((ctx, q), rt), hMaxBTree)
    finishLeafInsertBoundedProg (ctx, (leafIdx, (q, val)))

@[simp] private theorem runClient_frontier_prepareRoot (ctx : BTreeSliceCtx) (s : Memory.State) :
    (Prod.fst (Prod.snd ((Memory.spec 0).runClient s (prepareRootBoundedProg ctx)))).frontier =
      s.frontier := by
  rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩,
    ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩⟩
  unfold prepareRootBoundedProg prepareNonEmptyRootProg execRootSplitProg
  simp only [pure_bind, prog_runClient_state_bind, StateTransitionSpec.clientState,
    runClient_state_readSliceHdrAtProg]
  repeat (split_ifs <;> simp only [prog_runClient_state_bind,
    prog_runClient_state_pure, StateTransitionSpec.clientState,
    runClient_frontier_initEmptyRootAtProg,
    runClient_state_readSliceNodeAtProg, runClient_state_computeRootSplitProg,
    runClient_frontier_writeTwoNodesAtProg,
    runClient_frontier_writeSliceNodeAtProg, runClient_frontier_writeSliceHdrAtProg])

private theorem frontier_descendSplitStep (d : (BTreeSliceCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (descendSplitStepProg d)).frontier = s.frontier := by
  rcases d with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩,
    ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩⟩, _⟩, _⟩
  unfold descendSplitStepProg descendSplitBranchProg splitChildAndStepProg
    splitChildBodyProg finishChildSplitWritesProg StateTransitionSpec.clientState
  simp only [pure_bind, prog_runClient_state_bind, runClient_state_readSliceNodeAtProg]
  repeat (split_ifs <;> simp only [prog_runClient_state_bind,
    prog_runClient_state_pure, StateTransitionSpec.clientState,
    runClient_state_readSliceHdrAtProg, runClient_state_readSliceNodeAtProg,
    runClient_state_computeChildSplitProg, runClient_state_swarRankClampedProg,
    runClient_state_laneGetBoundedProg, runClient_frontier_writeTwoNodesAtProg,
    runClient_frontier_writeSliceNodeAtProg, runClient_frontier_writeSliceHdrAtProg])

private theorem descendSplit_iter_safe {w : ℕ} {ctx : BTreeSliceCtx} {q : ℕ} :
    ∀ m cur (s : Memory.State),
      DescendStepPre w ((ctx, q), cur) s →
      iterationSafe descendSplitStepProg DescendStepPre w (ctx, q) m cur s ∧
      ((Memory.spec 0).clientState s
        (iterate descendSplitStepProg (ctx, q) m cur)).frontier = s.frontier := by
  intro m
  induction m with
  | zero => intro _ _ _; exact ⟨trivial, rfl⟩
  | succ m ih =>
    intro cur s hpre
    have hfr1 := frontier_descendSplitStep ((ctx, q), cur) s
    set s₁ := (Memory.spec 0).clientState s (descendSplitStepProg ((ctx, q), cur))
    set nxt := (Memory.spec 0).clientResult s (descendSplitStepProg ((ctx, q), cur))
    have hpre₁ : DescendStepPre w ((ctx, q), nxt) s₁ := by
      dsimp only [DescendStepPre, BTreeSlicePre] at hpre ⊢
      rwa [hfr1]
    obtain ⟨hs_m, hfr_m⟩ := ih nxt s₁ hpre₁
    refine ⟨⟨hpre, hs_m⟩, ?_⟩
    unfold iterate; rw [StateTransitionSpec.clientState_bind]; exact hfr_m.trans hfr1

theorem realizesBounded_btreeInsert :
    RealizesBounded .exact btreeInsertBoundedProg
      (WordEncoding.encode (α := BTreeSliceCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      BTreeKeyValOpPre (fun _ _ => 0) := by
  have hpr := realizesBounded_prepareRoot
  have hdl := realizesBounded_descendSplitLoop
  have hfl := realizesBounded_finishLeafInsert
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨q, val⟩⟩
    obtain ⟨hslice, hq, hval⟩ := h
    have hfr1 : ((Memory.spec 0).clientState s (prepareRootBoundedProg ctx)).frontier =
        s.frontier := runClient_frontier_prepareRoot ctx s
    set s₁ := (Memory.spec 0).clientState s (prepareRootBoundedProg ctx)
    set rt := (Memory.spec 0).clientResult s (prepareRootBoundedProg ctx)
    have hpre1 : DescendStepPre w ((ctx, q), rt) s₁ := by
      dsimp only [DescendStepPre, BTreeSlicePre] at hslice ⊢
      exact ⟨by rwa [hfr1], hq⟩
    obtain ⟨hs_it, hfr2⟩ := descendSplit_iter_safe hMaxBTree rt s₁ hpre1
    have hw6 : 6 ≤ w := hslice.1.six_le_w
    have hmax := fits_hMaxBTree hw6)
  all_goals try exact hslice
  all_goals try exact hmax
  all_goals try exact hs_it
  all_goals (
    dsimp only [FinishLeafInsertPre, BTreeKeyValOpPre, BTreeSlicePre, descendSplitLoopProg]
      at hslice ⊢
    change _ ∧ _ ∧ _
    have hfr2' : (Prod.fst (Prod.snd ((Memory.spec 0).runClient s₁
        (iterate descendSplitStepProg (ctx, q) hMaxBTree rt)))).frontier = s.frontier :=
      hfr2.trans hfr1
    simp only [StateTransitionSpec.clientState] at s₁ rt hfr2' ⊢
    rw [hfr2']
    exact ⟨hslice, hq, hval⟩)

/-! ## Section 4: Width-Spine Helper (`RawTreeValid`) and Exact `ValidWhpSlice` Refinement -/

local macro "dsimp_slice_ctx" : tactic =>
  `(tactic| dsimp only [BTreeEpochLayout.toSliceCtx, ctxHdrAt, ctxNodeAt, ctxSplitParams,
    ctxMbOb, ctxPbWv, ctxMb, ctxOm, ctxOkOv, ctxWv, ctxWm, ctxWkWvl, ctxFpWvL, ctxFp, ctxWvL,
    ctxTm, ctxNs, ctxB, ctxRole])

/-- Lightweight width-and-index projection of `ValidSubtree` along `BTreeTree`, sufficient to prove
literal `extractBTreeSlice = btree*` equality without re-proving key sortedness or intervals. -/
private def RawTreeValid (wMeta fpBits W_val tMin alloc : ℕ) (nodes : ℕ → BTreeNode) :
    BTreeTree → Prop
  | .leaf idx cnt =>
    let nd := nodes idx
    idx < alloc ∧ nd.metaWord = mkNodeMeta true cnt ∧ cnt ≤ 2 * tMin - 1 ∧
    nd.metaWord < 2 ^ wMeta ∧
    nd.keysWord < 2 ^ (cnt * (fpBits + 2)) ∧ nd.valsWord < 2 ^ (cnt * W_val) ∧
    ∀ j < cnt, laneGet (fpBits + 2) nd.keysWord j < 2 ^ fpBits
  | .branch idx cnt cs =>
    let nd := nodes idx
    idx < alloc ∧ nd.metaWord = mkNodeMeta false cnt ∧ cnt ≤ 2 * tMin - 1 ∧
    nd.metaWord < 2 ^ wMeta ∧
    nd.keysWord < 2 ^ (cnt * (fpBits + 2)) ∧ nd.valsWord < 2 ^ ((cnt + 1) * W_val) ∧
    (∀ j < cnt, laneGet (fpBits + 2) nd.keysWord j < 2 ^ fpBits) ∧
    (∀ i, idx ∉ (cs i).nodeSet) ∧
    (∀ i j, i ≠ j → Disjoint (cs i).nodeSet (cs j).nodeSet) ∧
    (∀ i : Fin (cnt + 1),
      laneGet W_val nd.valsWord i.val = (cs i).rootIdx ∧
      RawTreeValid wMeta fpBits W_val tMin alloc nodes (cs i))

private theorem rawTreeValid_of_validSubtree {isRoot : Bool}
    {wMeta fpBits W_val tMin alloc lo hi : ℕ}
    {nodes : ℕ → BTreeNode} {mapFn : ℕ → Option ℕ} {T : BTreeTree}
    (ht1 : 1 ≤ tMin) (hmeta_cap : 4 * tMin ≤ 2 ^ wMeta) (hhi : hi < 2 ^ fpBits)
    (hv : ValidSubtree isRoot fpBits W_val tMin alloc nodes lo hi mapFn T) :
    RawTreeValid wMeta fpBits W_val tMin alloc nodes T := by
  induction T generalizing isRoot lo hi with
  | leaf idx cnt =>
    obtain ⟨hidx, hmw, hcnt, hkw, hvw, hbnd, _, _⟩ := hv
    refine ⟨hidx, hmw, hcnt, ?_, hkw, hvw, fun j hj => (hbnd j hj).2.trans_lt hhi⟩
    rw [hmw]; unfold mkNodeMeta; simp only [↓reduceIte]; omega
  | branch idx cnt cs ih =>
    obtain ⟨hidx, hmw, _, hcnt, hkw, hvw, _, hlast, hmono, hnot, hdisj, _, hcs⟩ := hv
    refine ⟨hidx, hmw, hcnt, ?_, hkw, hvw, fun j hj => ?_, hnot, hdisj, fun i => ⟨(hcs i).1, ?_⟩⟩
    · rw [hmw]; unfold mkNodeMeta; simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · rcases eq_or_lt_of_le (by omega : j ≤ cnt - 1) with rfl | hlt
      · exact hlast.trans hhi
      · exact (hmono j (cnt - 1) hlt (by omega)).trans (hlast.trans hhi)
    · exact ih i ((childHi_le hlast.le hmono).trans_lt hhi) (hcs i).2

private theorem RawTreeValid.nodeSet_lt {wMeta fpBits W_val tMin alloc : ℕ} {nodes : ℕ → BTreeNode}
    {T : BTreeTree} (hr : RawTreeValid wMeta fpBits W_val tMin alloc nodes T) :
    ∀ v ∈ T.nodeSet, v < alloc := by
  induction T with
  | leaf idx _ =>
    intro v hv; rw [BTreeTree.nodeSet, mem_singleton] at hv; subst hv; exact hr.1
  | branch idx _ cs ih =>
    intro v hv; rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv
    rcases hv with rfl | ⟨i, _, hvi⟩
    · exact hr.1
    · exact ih i (hr.2.2.2.2.2.2.2.2.2 i).2 v hvi

private theorem RawTreeValid.frame {wMeta fpBits W_val tMin alloc alloc' : ℕ}
    {nodes nodes' : ℕ → BTreeNode} {T : BTreeTree}
    (hr : RawTreeValid wMeta fpBits W_val tMin alloc nodes T) (hal : alloc ≤ alloc')
    (hnd : ∀ v ∈ T.nodeSet, nodes' v = nodes v) :
    RawTreeValid wMeta fpBits W_val tMin alloc' nodes' T := by
  induction T with
  | leaf idx cnt =>
    have heq := hnd idx (by simp [BTreeTree.nodeSet])
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    refine ⟨h1.trans_le hal, ?_, h3, ?_, ?_, ?_, ?_⟩ <;> simpa only [heq]
  | branch idx cnt cs ih =>
    have heq := hnd idx (by simp [BTreeTree.nodeSet])
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hr
    refine ⟨h1.trans_le hal, ?_, h3, ?_, ?_, ?_, ?_, h8, h9, fun i => ?_⟩
    · simpa only [heq] using h2
    · simpa only [heq] using h4
    · simpa only [heq] using h5
    · simpa only [heq] using h6
    · simpa only [heq] using h7
    · rw [heq]
      refine ⟨(h10 i).1, ih i (h10 i).2 fun v hvi => ?_⟩
      exact hnd v (mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ i, hvi⟩))

/-- `descendStepProg` iterated `fuel ≥ T.height` times reaches the exact leaf of `descendToLeaf` and
guarantees `RawTreeValid` at that leaf. -/
private theorem descend_iter_spec {L : BTreeEpochLayout} {b role q : ℕ} {s : Memory.State}
    {frontier : ℕ} (hvL : L.Valid L.w frontier) (hq : q < 2 ^ L.fpBits) :
    let sl := extractBTreeSlice L b role s.mem
    ∀ (fuel : ℕ) {T : BTreeTree},
      RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes T →
      T.height ≤ fuel →
      let leafIdx := descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes fuel T.rootIdx q
      (Memory.spec 0).clientResult s
          (iterate descendStepProg (L.toSliceCtx b role, q) fuel T.rootIdx) = leafIdx ∧
        ∃ cnt, RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes
          (.leaf leafIdx cnt) := by
  intro sl fuel
  have h8 := hvL.2.2.2.1
  have hcap := hvL.2.2.2.2.2.2.2.2.2.2.2.2.1
  induction fuel with
  | zero =>
    intro T hr hht
    cases T with
    | leaf idx cnt =>
      exact ⟨rfl, cnt, hr⟩
    | branch idx cnt cs =>
      simp [BTreeTree.height] at hht
  | succ fuel ih =>
    intro T hr hht
    have hst1 : ∀ cur,
        (Memory.spec 0).clientState s (descendStepProg ((L.toSliceCtx b role, q), cur)) = s := by
      intro cur
      unfold descendStepProg descendBranchNextProg StateTransitionSpec.clientState
      dsimp_slice_ctx
      simp only [pure_bind, prog_runClient_state_bind, runClient_state_readSliceNodeAtProg]
      split_ifs <;> simp
    cases T with
    | leaf idx cnt =>
      have hmw := hr.2.1
      have hstep_res : (Memory.spec 0).clientResult s
          (descendStepProg ((L.toSliceCtx b role, q), idx)) = idx := by
        unfold descendStepProg descendBranchNextProg
        dsimp_slice_ctx
        simp only [pure_bind]
        obtain ⟨hr_rn, hst_rn, _⟩ := readSliceNodeAtProg_spec L b role idx s
        dsimp only [BTreeEpochLayout.toNodeCtx] at hr_rn hst_rn
        change _ = ((sl.nodes idx).metaWord,
          ((sl.nodes idx).keysWord, (sl.nodes idx).valsWord)) at hr_rn
        rw [prog_clientResult_bind, hst_rn, hr_rn]
        have hl : (sl.nodes idx).metaWord % 2 = 1 := by
          rw [hmw]; unfold mkNodeMeta; simp only [↓reduceIte]; omega
        simp [hl]
      have hdesc_eq : descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes (fuel + 1) idx q =
          descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes fuel idx q := by
        cases fuel <;> dsimp only [descendToLeaf] <;> rw [hmw, metaIsLeaf_mkNodeMeta] <;> rfl
      obtain ⟨hrec, cnt', hr'⟩ := ih (T := .leaf idx cnt) hr (Nat.zero_le fuel)
      dsimp only [BTreeTree.rootIdx] at hrec hr'
      unfold iterate
      dsimp only [BTreeTree.rootIdx]
      rw [prog_clientResult_bind, hst1, hstep_res, hdesc_eq]
      exact ⟨hrec, cnt', hr'⟩
    | branch idx cnt cs =>
      obtain ⟨hidx, hmw, hcnt, _, hkw, _, hlanes, _, _, hcs⟩ := hr
      have hcnt_lt : cnt < 2 * L.tMin := by omega
      have hkw_cap : (sl.nodes idx).keysWord < 2 ^ (cnt * (L.fpBits + 2)) := hkw
      obtain ⟨hrank_eq, hrank_le⟩ := swarRankClampedProg_eq_swarRank hcnt_lt hcap hq hkw_cap
        hlanes s
      set r := swarRank L.fpBits (2 * L.tMin) cnt q (sl.nodes idx).keysWord
      let r_fin : Fin (cnt + 1) := ⟨r, Nat.lt_succ_of_le hrank_le⟩
      have hstep_res : (Memory.spec 0).clientResult s
          (descendStepProg ((L.toSliceCtx b role, q), idx)) = (cs r_fin).rootIdx := by
        unfold descendStepProg descendBranchNextProg
        dsimp_slice_ctx
        simp only [pure_bind]
        obtain ⟨hr_rn, hst_rn, _⟩ := readSliceNodeAtProg_spec L b role idx s
        dsimp only [BTreeEpochLayout.toNodeCtx] at hr_rn hst_rn
        change _ = ((sl.nodes idx).metaWord,
          ((sl.nodes idx).keysWord, (sl.nodes idx).valsWord)) at hr_rn
        rw [prog_clientResult_bind, hst_rn, hr_rn]
        have hl : (sl.nodes idx).metaWord % 2 ≠ 1 := by
          rw [hmw]; unfold mkNodeMeta; simp only [Bool.false_eq_true, ↓reduceIte]; omega
        have hcnt_sh : (sl.nodes idx).metaWord >>> 1 = cnt := by
          rw [Nat.shiftRight_eq_div_pow, pow_one, hmw]; exact metaCount_mkNodeMeta false cnt
        simp [hl, hcnt_sh, hrank_eq, r, (hcs r_fin).1, r_fin]
      have hht_c : (cs r_fin).height ≤ fuel := by
        dsimp only [BTreeTree.height] at hht
        have hle := Finset.le_sup (f := fun i => (cs i).height) (mem_univ r_fin)
        omega
      obtain ⟨hrec, cnt', hr'⟩ := ih (hcs r_fin).2 hht_c
      have hdesc_eq : descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes (fuel + 1) idx q =
          descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes fuel (cs r_fin).rootIdx q := by
        dsimp only [descendToLeaf]
        rw [hmw, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
        simp [r, (hcs r_fin).1, r_fin]
      unfold iterate
      dsimp only [BTreeTree.rootIdx]
      rw [prog_clientResult_bind, hst1, hstep_res, hdesc_eq]
      exact ⟨hrec, cnt', hr'⟩

/-- Exact `ValidWhpSlice` refinement for `btreeLookupBoundedProg`. -/
theorem btreeLookupBoundedProg_spec {c N b role q : ℕ} {s : Memory.State}
    {insCount : ℕ} {mapFn : ℕ → Option ℕ} {L : BTreeEpochLayout}
    (hth : whpThreshold c ≤ N)
    (hL_eq : L = epochBTreeLayout c L.w N L.metaBase)
    (hvL' : L.Valid L.w s.frontier)
    (hb : b < L.numBuckets) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale N ^ 12)
    (hv : ValidWhpSlice N insCount (extractBTreeSlice L b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp N) :
    (Memory.spec 0).clientState s (btreeLookupBoundedProg (L.toSliceCtx b role, q)) = s ∧
    memoryCost (btreeLookupBoundedProg (L.toSliceCtx b role, q)) s ≤ 6 * hMaxBTree + 16 ∧
    (Memory.spec 0).clientResult s (btreeLookupBoundedProg (L.toSliceCtx b role, q)) =
      match mapFn q with
      | none => (0, 0)
      | some v => (1, v) := by
  have hfp_eq : L.fpBits = fpBitsWhp N := by rw [hL_eq]; rfl
  have hwv_eq : L.wValLane = valLaneBitsWhp N := by rw [hL_eq]; rfl
  have htm_eq : L.tMin = tMinWhp N := by rw [hL_eq]; rfl
  set sl := extractBTreeSlice L b role s.mem
  obtain ⟨hhdr_res, hhdr_st, hhdr_cost⟩ := readSliceHdrAtProg_spec L b role s
  change _ = (sl.alloc, sl.root) at hhdr_res
  dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr_res hhdr_st hhdr_cost
  obtain ⟨_, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, _, _, hT⟩⟩ := hv.alloc_and_height_lt hth hins
  · refine ⟨?_, ?_, ?_⟩
    · unfold btreeLookupBoundedProg; dsimp_slice_ctx; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]; simp [h0]
    · unfold btreeLookupBoundedProg; dsimp_slice_ctx; simp only [pure_bind]
      rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]; simp [h0]
    · unfold btreeLookupBoundedProg; dsimp_slice_ctx; simp only [pure_bind]
      rw [prog_clientResult_bind, hhdr_st, hhdr_res]; simp [h0]
  · rw [← hv.lookup_eq hth hins hq]
    have hhi : 2 ^ L.fpBits - 1 < 2 ^ L.fpBits := Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one
    have hraw : RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes T :=
      rawTreeValid_of_validSubtree (by have := hvL'.2.2.2.1; omega)
        hvL'.2.2.2.2.2.2.2.2.2.2.2.1 hhi (by simpa only [hfp_eq, hwv_eq, htm_eq] using hT)
    obtain ⟨hdesc_res, cnt_l, hraw_l⟩ := descend_iter_spec hvL' (hfp_eq ▸ hq) hMaxBTree hraw
      hht_lt.le
    rw [hrt] at hdesc_res hraw_l
    obtain ⟨_, hds_st, hds_cost⟩ := descend_iter_state_safe
      (w := L.w) (ctx := L.toSliceCtx b role) (q := q) (s := s)
      (by simpa only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx_toSliceCtx, hfp_eq] using
        ⟨⟨hvL', hb, hrole⟩, hq⟩)
      hMaxBTree sl.root
    dsimp only [BTreeEpochLayout.toSliceCtx] at hds_st hdesc_res hds_cost
    set leafIdx := descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes hMaxBTree sl.root q
    change RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes (.leaf leafIdx cnt_l)
      at hraw_l
    obtain ⟨_, hmw_l, hcnt_l, _, hkw_l, _, hlanes_l⟩ := hraw_l
    have hcnt_lt : cnt_l < 2 * L.tMin := by have := hvL'.2.2.2.1; omega
    obtain ⟨hrank_eq, _⟩ := swarRankClampedProg_eq_swarRank hcnt_lt
      hvL'.2.2.2.2.2.2.2.2.2.2.2.2.1 (hfp_eq ▸ hq) hkw_l hlanes_l s
    obtain ⟨hrn_res, hrn_st, hrn_cost⟩ := readSliceNodeAtProg_spec L b role leafIdx s
    change _ = ((sl.nodes leafIdx).metaWord,
      ((sl.nodes leafIdx).keysWord, (sl.nodes leafIdx).valsWord)) at hrn_res
    dsimp only [BTreeEpochLayout.toNodeCtx] at hrn_res hrn_st hrn_cost
    have hcnt_sh : (sl.nodes leafIdx).metaWord >>> 1 = cnt_l := by
      rw [Nat.shiftRight_eq_div_pow, pow_one, hmw_l]; exact metaCount_mkNodeMeta true cnt_l
    have hmc_eq : metaCount (sl.nodes leafIdx).metaWord = cnt_l := by
      rw [hmw_l, metaCount_mkNodeMeta]
    have ha_nz : sl.alloc ≠ 0 := by omega
    set r := swarRank L.fpBits (2 * L.tMin) cnt_l q (sl.nodes leafIdx).keysWord
    change _ = r at hrank_eq
    refine ⟨?_, ?_, ?_⟩
    · unfold btreeLookupBoundedProg btreeLookupNonEmptyProg btreeLookupLeafProg
        btreeLookupRankProg btreeLookupHitProg descendLoopProg
      dsimp_slice_ctx; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]
      simp only [ha_nz, ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, hds_st, hdesc_res,
        StateTransitionSpec.clientState_bind, hrn_st, hrn_res]
      simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_swarRankClampedProg, runClient_state_laneGetBoundedProg]
      split_ifs <;> simp
    · unfold btreeLookupBoundedProg btreeLookupNonEmptyProg btreeLookupLeafProg
        btreeLookupRankProg btreeLookupHitProg descendLoopProg
      dsimp_slice_ctx; simp only [pure_bind]
      rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]
      simp only [ha_nz, ↓reduceIte]
      rw [Realization.memoryCost_bind', hds_st, hdesc_res,
        Realization.memoryCost_bind', hrn_st, hrn_res]
      simp only [Realization.memoryCost_bind', StateTransitionSpec.clientState,
        runClient_state_swarRankClampedProg, runClient_state_laneGetBoundedProg,
        memoryCost_swarRankClampedProg, memoryCost_laneGetBoundedProg]
      split_ifs <;> simp <;> omega
    · unfold btreeLookupBoundedProg btreeLookupNonEmptyProg btreeLookupLeafProg
        btreeLookupRankProg btreeLookupHitProg descendLoopProg
      dsimp_slice_ctx; simp only [pure_bind]
      rw [prog_clientResult_bind, hhdr_st, hhdr_res]
      simp only [ha_nz, ↓reduceIte]
      rw [prog_clientResult_bind, hds_st, hdesc_res, prog_clientResult_bind, hrn_st, hrn_res]
      simp only [hcnt_sh, prog_clientResult_bind, StateTransitionSpec.clientState,
        runClient_state_swarRankClampedProg, hrank_eq,
        runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg]
      have hbt_rhs : btreeLookup (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N)
          (extractBTreeSlice L b role s.mem) q =
          (if r < cnt_l && laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r == q then
            some (laneGet L.wValLane (sl.nodes leafIdx).valsWord r) else none) := by
        change btreeLookup (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N) sl q = _
        unfold btreeLookup
        rw [← hfp_eq, ← hwv_eq, ← htm_eq]
        simp only [ha_nz, ↓reduceIte, leafIdx, hmc_eq, r]
      rw [hbt_rhs]
      by_cases hrc : r < cnt_l
      · by_cases hkq : laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r = q <;> simp [hrc, hkq]
      · simp [hrc]

/-- Exact `ValidWhpSlice` refinement and frame preservation for `btreeDeleteBoundedProg`. -/
theorem btreeDeleteBoundedProg_spec {c N b role q : ℕ} {s : Memory.State}
    {insCount : ℕ} {mapFn : ℕ → Option ℕ} {L : BTreeEpochLayout}
    (hth : whpThreshold c ≤ N)
    (hL_eq : L = epochBTreeLayout c L.w N L.metaBase)
    (hvL : L.Valid L.w s.frontier)
    (hb : b < L.numBuckets) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale N ^ 12)
    (hv : ValidWhpSlice N insCount (extractBTreeSlice L b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp N) :
    let s' := (Memory.spec 0).clientState s (btreeDeleteBoundedProg (L.toSliceCtx b role, q))
    s'.frontier = s.frontier ∧
    memoryCost (btreeDeleteBoundedProg (L.toSliceCtx b role, q)) s ≤ 6 * hMaxBTree + 28 ∧
    extractBTreeSlice L b role s'.mem =
      btreeDelete (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N)
        (extractBTreeSlice L b role s.mem) q ∧
    ValidWhpSlice N insCount (extractBTreeSlice L b role s'.mem) (Function.update mapFn q none) ∧
    (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice L b' role' s'.mem = extractBTreeSlice L b' role' s.mem) ∧
    (∀ slot < 16 * L.numBuckets,
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w s'.mem slot =
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w s.mem slot) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  have hfp_eq : L.fpBits = fpBitsWhp N := by rw [hL_eq]; rfl
  have hwv_eq : L.wValLane = valLaneBitsWhp N := by rw [hL_eq]; rfl
  have htm_eq : L.tMin = tMinWhp N := by rw [hL_eq]; rfl
  set sl := extractBTreeSlice L b role s.mem
  obtain ⟨hhdr_res, hhdr_st, hhdr_cost⟩ := readSliceHdrAtProg_spec L b role s
  change _ = (sl.alloc, sl.root) at hhdr_res
  dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr_res hhdr_st hhdr_cost
  obtain ⟨halloc_ns, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, _, _, hT⟩⟩ :=
    hv.alloc_and_height_lt hth hins
  · have hst_eq : (Memory.spec 0).clientState s (btreeDeleteBoundedProg (L.toSliceCtx b role, q)) =
        s := by
      unfold btreeDeleteBoundedProg; dsimp_slice_ctx; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]; simp [h0]
    have hc_eq : memoryCost (btreeDeleteBoundedProg (L.toSliceCtx b role, q)) s = 4 := by
      unfold btreeDeleteBoundedProg; dsimp_slice_ctx; simp only [pure_bind]
      rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]; simp [h0]
    refine ⟨by rw [hst_eq], by rw [hc_eq]; omega, ?_, ?_,
      fun _ _ _ _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq]⟩
    · rw [hst_eq]; simp [btreeDelete, h0, sl]
    · rw [hst_eq]; simpa [btreeDelete, h0, sl] using hv.delete_spec hth hins hq
  · have hns_eq : L.nSlice = nSliceWhp N := by rw [hL_eq]; rfl
    have hhi : 2 ^ L.fpBits - 1 < 2 ^ L.fpBits := Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one
    have hraw : RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes T :=
      rawTreeValid_of_validSubtree (by have := hvL.2.2.2.1; omega)
        hvL.2.2.2.2.2.2.2.2.2.2.2.1 hhi (by simpa only [hfp_eq, hwv_eq, htm_eq] using hT)
    obtain ⟨hdesc_res, cnt_l, hraw_l⟩ := descend_iter_spec hvL (hfp_eq ▸ hq) hMaxBTree hraw
      hht_lt.le
    rw [hrt] at hdesc_res hraw_l
    obtain ⟨_, hds_st, hds_cost⟩ := descend_iter_state_safe
      (w := L.w) (ctx := L.toSliceCtx b role) (q := q) (s := s)
      (by simpa only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx_toSliceCtx, hfp_eq] using
        ⟨⟨hvL, hb, hrole⟩, hq⟩)
      hMaxBTree sl.root
    dsimp only [BTreeEpochLayout.toSliceCtx] at hds_st hdesc_res hds_cost
    set leafIdx := descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes hMaxBTree sl.root q
    change RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes (.leaf leafIdx cnt_l)
      at hraw_l
    change sl.alloc + hMaxBTree + 4 < nSliceWhp N at halloc_ns
    obtain ⟨hleaf_al, hmw_l, hcnt_l, _, hkw_l, hvw_l, hlanes_l⟩ := hraw_l
    have hleaf_ns : leafIdx < L.nSlice := hleaf_al.trans (by rw [hns_eq]; omega)
    have hcnt_lt : cnt_l < 2 * L.tMin := by have := hvL.2.2.2.1; omega
    obtain ⟨hrank_eq, _⟩ := swarRankClampedProg_eq_swarRank hcnt_lt
      hvL.2.2.2.2.2.2.2.2.2.2.2.2.1 (hfp_eq ▸ hq) hkw_l hlanes_l s
    obtain ⟨hrn_res, hrn_st, hrn_cost⟩ := readSliceNodeAtProg_spec L b role leafIdx s
    change _ = ((sl.nodes leafIdx).metaWord,
      ((sl.nodes leafIdx).keysWord, (sl.nodes leafIdx).valsWord)) at hrn_res
    dsimp only [BTreeEpochLayout.toNodeCtx] at hrn_res hrn_st hrn_cost
    have hcnt_sh : (sl.nodes leafIdx).metaWord >>> 1 = cnt_l := by
      rw [Nat.shiftRight_eq_div_pow, pow_one, hmw_l]; exact metaCount_mkNodeMeta true cnt_l
    have hmc_eq : metaCount (sl.nodes leafIdx).metaWord = cnt_l := by
      rw [hmw_l, metaCount_mkNodeMeta]
    have ha_nz : sl.alloc ≠ 0 := by omega
    set r := swarRank L.fpBits (2 * L.tMin) cnt_l q (sl.nodes leafIdx).keysWord
    change _ = r at hrank_eq
    by_cases hhit : r < cnt_l ∧ laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r = q
    · obtain ⟨hrc, hkq⟩ := hhit
      set nd' : BTreeNode :=
        ⟨mkNodeMeta true (cnt_l - 1),
          wordDeleteAt (L.fpBits + 2) r (sl.nodes leafIdx).keysWord,
          wordDeleteAt L.wValLane r (sl.nodes leafIdx).valsWord⟩
      have hnd'_meta : nd'.metaWord < 2 ^ L.wMeta := by
        dsimp only [nd', mkNodeMeta]; simp only [↓reduceIte]
        have := hvL.2.2.2.1; have := hvL.2.2.2.2.2.2.2.2.2.2.2.1; omega
      have hnd'_keys : nd'.keysWord < 2 ^ L.wKeys := by
        rw [hvL.2.2.2.2.2.2.2.1]
        have hd_lt : nd'.keysWord < 2 ^ ((cnt_l - 1) * (L.fpBits + 2)) :=
          wordDeleteAt_lt (m := cnt_l - 1) (by omega)
            (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ cnt_l)] using hkw_l)
        exact hd_lt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      have hnd'_vals : nd'.valsWord < 2 ^ L.wVals := by
        rw [hvL.2.2.2.2.2.2.2.2.1]
        have hd_lt : nd'.valsWord < 2 ^ ((cnt_l - 1) * L.wValLane) :=
          wordDeleteAt_lt (m := cnt_l - 1) (by omega)
            (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ cnt_l)] using hvw_l)
        exact hd_lt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      obtain ⟨he_w, ho_w, hb_w, ha_w⟩ := extractBTreeSlice_writeNode (mem := s.mem) (nd := nd')
        hvL hb hrole hleaf_ns hnd'_meta hnd'_keys hnd'_vals
      set idx := (3 * b + role) * L.nSlice + leafIdx
      set m3 := writePacked (L.metaBase + L.offVals) L.wVals L.w
        (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
          (writePacked (L.metaBase + L.offMeta) L.wMeta L.w s.mem idx nd'.metaWord)
          idx nd'.keysWord) idx nd'.valsWord
      have hst_eq : (Memory.spec 0).clientState s
          (btreeDeleteBoundedProg (L.toSliceCtx b role, q)) = ⟨m3, s.frontier⟩ := by
        unfold btreeDeleteBoundedProg btreeDeleteNonEmptyProg btreeDeleteLeafProg
          btreeDeleteRankProg btreeDeleteHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]
        simp only [ha_nz, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hds_st, hdesc_res,
          StateTransitionSpec.clientState_bind, hrn_st, hrn_res]
        simp only [hcnt_sh, StateTransitionSpec.clientState, prog_runClient_state_bind,
          runClient_state_swarRankClampedProg, hrank_eq,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg, hrc, hkq, ↓reduceIte,
          runClient_state_wordDeleteAtBoundedProg, clientResult_wordDeleteAtBoundedProg]
        unfold writeSliceNodeAtProg
        simp [hleaf_ns, idx, m3, nd', mkNodeMeta]
      have hc_le : memoryCost (btreeDeleteBoundedProg (L.toSliceCtx b role, q)) s ≤
          6 * hMaxBTree + 28 := by
        unfold btreeDeleteBoundedProg btreeDeleteNonEmptyProg btreeDeleteLeafProg
          btreeDeleteRankProg btreeDeleteHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]
        simp only [ha_nz, ↓reduceIte]
        rw [Realization.memoryCost_bind', hds_st, hdesc_res,
          Realization.memoryCost_bind', hrn_st, hrn_res]
        simp only [hcnt_sh, Realization.memoryCost_bind',
          StateTransitionSpec.clientState,
          runClient_state_swarRankClampedProg, hrank_eq, memoryCost_swarRankClampedProg,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg,
          memoryCost_laneGetBoundedProg, hrc, hkq, ↓reduceIte,
          memoryCost_wordDeleteAtBoundedProg, runClient_state_wordDeleteAtBoundedProg,
          clientResult_wordDeleteAtBoundedProg]
        unfold writeSliceNodeAtProg
        simp only [hleaf_ns, ↓reduceIte, pure_bind, Realization.memoryCost_bind',
          StateTransitionSpec.clientState, memoryCost_writePackedCompGenProg,
          runClient_state_writePackedCompGenProg]
        omega
      have hext_del : extractBTreeSlice L b role m3 =
          btreeDelete (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N) sl q := by
        rw [he_w]
        unfold btreeDelete
        rw [← hfp_eq, ← hwv_eq, ← htm_eq]
        change { sl with nodes := Function.update sl.nodes leafIdx nd' } = _
        have hbeq : (laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r == q) = true :=
          beq_iff_eq.mpr hkq
        simp only [ha_nz, ↓reduceIte, leafIdx, hmc_eq, r, hrc, hbeq]
        rfl
      refine ⟨by rw [hst_eq], hc_le, by rw [hst_eq]; exact hext_del, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq, hext_del]; exact hv.delete_spec hth hins hq
      · intro b' role' hb' hr' hne; rw [hst_eq]; exact ho_w b' role' hb' hr' hne
      · intro slot hsl; rw [hst_eq]; exact hb_w slot hsl
      · intro addr ha; rw [hst_eq]; exact ha_w addr ha
    · have hst_eq : (Memory.spec 0).clientState s
          (btreeDeleteBoundedProg (L.toSliceCtx b role, q)) = s := by
        unfold btreeDeleteBoundedProg btreeDeleteNonEmptyProg btreeDeleteLeafProg
          btreeDeleteRankProg btreeDeleteHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]
        simp only [ha_nz, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hds_st, hdesc_res,
          StateTransitionSpec.clientState_bind, hrn_st, hrn_res]
        simp only [hcnt_sh, StateTransitionSpec.clientState, prog_runClient_state_bind,
          runClient_state_swarRankClampedProg, hrank_eq,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg]
        by_cases hrc : r < cnt_l
        · have hkq : laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun h => hhit ⟨hrc, h⟩
          simp [hrc, hkq]
        · simp [hrc]
      have hc_le : memoryCost (btreeDeleteBoundedProg (L.toSliceCtx b role, q)) s ≤
          6 * hMaxBTree + 28 := by
        unfold btreeDeleteBoundedProg btreeDeleteNonEmptyProg btreeDeleteLeafProg
          btreeDeleteRankProg btreeDeleteHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]
        simp only [ha_nz, ↓reduceIte]
        rw [Realization.memoryCost_bind', hds_st, hdesc_res,
          Realization.memoryCost_bind', hrn_st, hrn_res]
        simp only [hcnt_sh, Realization.memoryCost_bind',
          StateTransitionSpec.clientState,
          runClient_state_swarRankClampedProg, hrank_eq, memoryCost_swarRankClampedProg,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg,
          memoryCost_laneGetBoundedProg]
        by_cases hrc : r < cnt_l
        · have hkq : laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun h => hhit ⟨hrc, h⟩
          simp only [hrc, hkq, ↓reduceIte, memoryCost_pure]; omega
        · simp only [hrc, ↓reduceIte, memoryCost_pure]; omega
      have hdel_noop : btreeDelete (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N) sl q = sl := by
        unfold btreeDelete
        rw [← hfp_eq, ← hwv_eq, ← htm_eq]
        by_cases hrc : r < cnt_l
        · have hkq : (laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r == q) = false :=
            beq_eq_false_iff_ne.mpr fun h => hhit ⟨hrc, h⟩
          simp [ha_nz, leafIdx, hmc_eq, r, hrc, hkq]
        · simp [ha_nz, leafIdx, hmc_eq, r, hrc]
      refine ⟨by rw [hst_eq], hc_le, by rw [hst_eq, hdel_noop], ?_,
        fun _ _ _ _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq]⟩
      rw [hst_eq]; dsimp only [sl] at hdel_noop; rw [← hdel_noop]; exact hv.delete_spec hth hins hq

/-- Exact `ValidWhpSlice` refinement and frame preservation for `btreeUpdateBoundedProg`. -/
theorem btreeUpdateBoundedProg_spec {c N b role q newVal : ℕ} {s : Memory.State}
    {insCount : ℕ} {mapFn : ℕ → Option ℕ} {L : BTreeEpochLayout}
    (hth : whpThreshold c ≤ N)
    (hL_eq : L = epochBTreeLayout c L.w N L.metaBase)
    (hvL : L.Valid L.w s.frontier)
    (hb : b < L.numBuckets) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale N ^ 12)
    (hv : ValidWhpSlice N insCount (extractBTreeSlice L b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp N) (hval : newVal < 2 ^ valLaneBitsWhp N) :
    let s' := (Memory.spec 0).clientState s
      (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal)))
    s'.frontier = s.frontier ∧
    memoryCost (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal))) s ≤
      6 * hMaxBTree + 28 ∧
    extractBTreeSlice L b role s'.mem =
      btreeUpdate (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N)
        (extractBTreeSlice L b role s.mem) q newVal ∧
    ValidWhpSlice N insCount (extractBTreeSlice L b role s'.mem)
      (if (mapFn q).isSome then Function.update mapFn q (some newVal) else mapFn) ∧
    (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice L b' role' s'.mem = extractBTreeSlice L b' role' s.mem) ∧
    (∀ slot < 16 * L.numBuckets,
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w s'.mem slot =
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w s.mem slot) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  have hfp_eq : L.fpBits = fpBitsWhp N := by rw [hL_eq]; rfl
  have hwv_eq : L.wValLane = valLaneBitsWhp N := by rw [hL_eq]; rfl
  have htm_eq : L.tMin = tMinWhp N := by rw [hL_eq]; rfl
  set sl := extractBTreeSlice L b role s.mem
  obtain ⟨hhdr_res, hhdr_st, hhdr_cost⟩ := readSliceHdrAtProg_spec L b role s
  change _ = (sl.alloc, sl.root) at hhdr_res
  dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr_res hhdr_st hhdr_cost
  obtain ⟨halloc_ns, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, _, _, hT⟩⟩ :=
    hv.alloc_and_height_lt hth hins
  · have hst_eq : (Memory.spec 0).clientState s
        (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal))) = s := by
      unfold btreeUpdateBoundedProg; dsimp_slice_ctx; simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]; simp [h0]
    have hc_eq : memoryCost (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal))) s = 4 := by
      unfold btreeUpdateBoundedProg; dsimp_slice_ctx; simp only [pure_bind]
      rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]; simp [h0]
    refine ⟨by rw [hst_eq], by rw [hc_eq]; omega, ?_, ?_,
      fun _ _ _ _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq]⟩
    · rw [hst_eq]; simp [btreeUpdate, h0, sl]
    · rw [hst_eq]; simpa [btreeUpdate, h0, sl] using hv.update_spec hth hins hq hval
  · have hns_eq : L.nSlice = nSliceWhp N := by rw [hL_eq]; rfl
    have hhi : 2 ^ L.fpBits - 1 < 2 ^ L.fpBits := Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one
    have hraw : RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes T :=
      rawTreeValid_of_validSubtree (by have := hvL.2.2.2.1; omega)
        hvL.2.2.2.2.2.2.2.2.2.2.2.1 hhi (by simpa only [hfp_eq, hwv_eq, htm_eq] using hT)
    obtain ⟨hdesc_res, cnt_l, hraw_l⟩ := descend_iter_spec hvL (hfp_eq ▸ hq) hMaxBTree hraw
      hht_lt.le
    rw [hrt] at hdesc_res hraw_l
    obtain ⟨_, hds_st, hds_cost⟩ := descend_iter_state_safe
      (w := L.w) (ctx := L.toSliceCtx b role) (q := q) (s := s)
      (by simpa only [BTreeKeyOpPre, BTreeSlicePre, unpackSliceCtx_toSliceCtx, hfp_eq] using
        ⟨⟨hvL, hb, hrole⟩, hq⟩)
      hMaxBTree sl.root
    dsimp only [BTreeEpochLayout.toSliceCtx] at hds_st hdesc_res hds_cost
    set leafIdx := descendToLeaf L.fpBits L.wValLane L.tMin sl.nodes hMaxBTree sl.root q
    change RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes (.leaf leafIdx cnt_l)
      at hraw_l
    change sl.alloc + hMaxBTree + 4 < nSliceWhp N at halloc_ns
    obtain ⟨hleaf_al, hmw_l, hcnt_l, hmeta_lt_l, hkw_l, hvw_l, hlanes_l⟩ := hraw_l
    have hleaf_ns : leafIdx < L.nSlice := hleaf_al.trans (by rw [hns_eq]; omega)
    have hcnt_lt : cnt_l < 2 * L.tMin := by have := hvL.2.2.2.1; omega
    obtain ⟨hrank_eq, _⟩ := swarRankClampedProg_eq_swarRank hcnt_lt
      hvL.2.2.2.2.2.2.2.2.2.2.2.2.1 (hfp_eq ▸ hq) hkw_l hlanes_l s
    obtain ⟨hrn_res, hrn_st, hrn_cost⟩ := readSliceNodeAtProg_spec L b role leafIdx s
    change _ = ((sl.nodes leafIdx).metaWord,
      ((sl.nodes leafIdx).keysWord, (sl.nodes leafIdx).valsWord)) at hrn_res
    dsimp only [BTreeEpochLayout.toNodeCtx] at hrn_res hrn_st hrn_cost
    have hcnt_sh : (sl.nodes leafIdx).metaWord >>> 1 = cnt_l := by
      rw [Nat.shiftRight_eq_div_pow, pow_one, hmw_l]; exact metaCount_mkNodeMeta true cnt_l
    have hmc_eq : metaCount (sl.nodes leafIdx).metaWord = cnt_l := by
      rw [hmw_l, metaCount_mkNodeMeta]
    have ha_nz : sl.alloc ≠ 0 := by omega
    set r := swarRank L.fpBits (2 * L.tMin) cnt_l q (sl.nodes leafIdx).keysWord
    change _ = r at hrank_eq
    by_cases hhit : r < cnt_l ∧ laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r = q
    · obtain ⟨hrc, hkq⟩ := hhit
      set nd' : BTreeNode :=
        ⟨(sl.nodes leafIdx).metaWord, (sl.nodes leafIdx).keysWord,
          wordUpdateAt L.wValLane r newVal (sl.nodes leafIdx).valsWord⟩
      have hnd'_keys : nd'.keysWord < 2 ^ L.wKeys := by
        rw [hvL.2.2.2.2.2.2.2.1]
        exact hkw_l.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      have hnd'_vals : nd'.valsWord < 2 ^ L.wVals := by
        rw [hvL.2.2.2.2.2.2.2.2.1]
        have hd_lt : wordDeleteAt L.wValLane r (sl.nodes leafIdx).valsWord <
            2 ^ ((cnt_l - 1) * L.wValLane) :=
          wordDeleteAt_lt (m := cnt_l - 1) (by omega)
            (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ cnt_l)] using hvw_l)
        have hu_eq : wordUpdateAt L.wValLane r newVal (sl.nodes leafIdx).valsWord =
            wordInsertAt L.wValLane r newVal
              (wordDeleteAt L.wValLane r (sl.nodes leafIdx).valsWord) := by
          rw [← clientResult_wordUpdateAtBoundedProg (s := s)]
          simp [wordUpdateAtBoundedProg]
        have hu_lt : nd'.valsWord < 2 ^ (cnt_l * L.wValLane) := by
          dsimp only [nd']; rw [hu_eq]
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ cnt_l)] using
            wordInsertAt_lt (by omega) (hwv_eq ▸ hval) hd_lt
        exact hu_lt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      obtain ⟨he_w, ho_w, hb_w, ha_w⟩ := extractBTreeSlice_writeNode (mem := s.mem) (nd := nd')
        hvL hb hrole hleaf_ns hmeta_lt_l hnd'_keys hnd'_vals
      set idx := (3 * b + role) * L.nSlice + leafIdx
      set m3 := writePacked (L.metaBase + L.offVals) L.wVals L.w
        (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
          (writePacked (L.metaBase + L.offMeta) L.wMeta L.w s.mem idx nd'.metaWord)
          idx nd'.keysWord) idx nd'.valsWord
      have hst_eq : (Memory.spec 0).clientState s
          (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal))) = ⟨m3, s.frontier⟩ := by
        unfold btreeUpdateBoundedProg btreeUpdateNonEmptyProg btreeUpdateLeafProg
          btreeUpdateRankProg btreeUpdateHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]
        simp only [ha_nz, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hds_st, hdesc_res,
          StateTransitionSpec.clientState_bind, hrn_st, hrn_res]
        simp only [hcnt_sh, StateTransitionSpec.clientState, prog_runClient_state_bind,
          runClient_state_swarRankClampedProg, hrank_eq,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg, hrc, hkq, ↓reduceIte,
          runClient_state_wordUpdateAtBoundedProg, clientResult_wordUpdateAtBoundedProg]
        unfold writeSliceNodeAtProg
        simp [hleaf_ns, idx, m3, nd']
      have hc_le : memoryCost (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal))) s ≤
          6 * hMaxBTree + 28 := by
        unfold btreeUpdateBoundedProg btreeUpdateNonEmptyProg btreeUpdateLeafProg
          btreeUpdateRankProg btreeUpdateHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]
        simp only [ha_nz, ↓reduceIte]
        rw [Realization.memoryCost_bind', hds_st, hdesc_res,
          Realization.memoryCost_bind', hrn_st, hrn_res]
        simp only [hcnt_sh, Realization.memoryCost_bind',
          StateTransitionSpec.clientState,
          runClient_state_swarRankClampedProg, hrank_eq, memoryCost_swarRankClampedProg,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg,
          memoryCost_laneGetBoundedProg, hrc, hkq, ↓reduceIte,
          memoryCost_wordUpdateAtBoundedProg, runClient_state_wordUpdateAtBoundedProg,
          clientResult_wordUpdateAtBoundedProg]
        unfold writeSliceNodeAtProg
        simp only [hleaf_ns, ↓reduceIte, pure_bind, Realization.memoryCost_bind',
          StateTransitionSpec.clientState, memoryCost_writePackedCompGenProg,
          runClient_state_writePackedCompGenProg]
        omega
      have hext_upd : extractBTreeSlice L b role m3 =
          btreeUpdate (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N) sl q newVal := by
        rw [he_w]
        unfold btreeUpdate
        rw [← hfp_eq, ← hwv_eq, ← htm_eq]
        change { sl with nodes := Function.update sl.nodes leafIdx nd' } = _
        have hbeq : (laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r == q) = true :=
          beq_iff_eq.mpr hkq
        simp only [ha_nz, ↓reduceIte, leafIdx, hmc_eq, r, hrc, hbeq]
        rfl
      refine ⟨by rw [hst_eq], hc_le, by rw [hst_eq]; exact hext_upd, ?_, ?_, ?_, ?_⟩
      · rw [hst_eq, hext_upd]; exact hv.update_spec hth hins hq hval
      · intro b' role' hb' hr' hne; rw [hst_eq]; exact ho_w b' role' hb' hr' hne
      · intro slot hsl; rw [hst_eq]; exact hb_w slot hsl
      · intro addr ha; rw [hst_eq]; exact ha_w addr ha
    · have hst_eq : (Memory.spec 0).clientState s
          (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal))) = s := by
        unfold btreeUpdateBoundedProg btreeUpdateNonEmptyProg btreeUpdateLeafProg
          btreeUpdateRankProg btreeUpdateHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hhdr_st, hhdr_res]
        simp only [ha_nz, ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, hds_st, hdesc_res,
          StateTransitionSpec.clientState_bind, hrn_st, hrn_res]
        simp only [hcnt_sh, StateTransitionSpec.clientState, prog_runClient_state_bind,
          runClient_state_swarRankClampedProg, hrank_eq,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg]
        by_cases hrc : r < cnt_l
        · have hkq : laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun h => hhit ⟨hrc, h⟩
          simp [hrc, hkq]
        · simp [hrc]
      have hc_le : memoryCost (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal))) s ≤
          6 * hMaxBTree + 28 := by
        unfold btreeUpdateBoundedProg btreeUpdateNonEmptyProg btreeUpdateLeafProg
          btreeUpdateRankProg btreeUpdateHitProg descendLoopProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_cost]
        simp only [ha_nz, ↓reduceIte]
        rw [Realization.memoryCost_bind', hds_st, hdesc_res,
          Realization.memoryCost_bind', hrn_st, hrn_res]
        simp only [hcnt_sh, Realization.memoryCost_bind',
          StateTransitionSpec.clientState,
          runClient_state_swarRankClampedProg, hrank_eq, memoryCost_swarRankClampedProg,
          runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg,
          memoryCost_laneGetBoundedProg]
        by_cases hrc : r < cnt_l
        · have hkq : laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r ≠ q :=
            fun h => hhit ⟨hrc, h⟩
          simp only [hrc, hkq, ↓reduceIte, memoryCost_pure]; omega
        · simp only [hrc, ↓reduceIte, memoryCost_pure]; omega
      have hupd_noop :
          btreeUpdate (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N) sl q newVal = sl := by
        unfold btreeUpdate
        rw [← hfp_eq, ← hwv_eq, ← htm_eq]
        by_cases hrc : r < cnt_l
        · have hkq : (laneGet (L.fpBits + 2) (sl.nodes leafIdx).keysWord r == q) = false :=
            beq_eq_false_iff_ne.mpr fun h => hhit ⟨hrc, h⟩
          simp [ha_nz, leafIdx, hmc_eq, r, hrc, hkq]
        · simp [ha_nz, leafIdx, hmc_eq, r, hrc]
      refine ⟨by rw [hst_eq], hc_le, by rw [hst_eq, hupd_noop], ?_,
        fun _ _ _ _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq], fun _ _ => by rw [hst_eq]⟩
      rw [hst_eq]; dsimp only [sl] at hupd_noop; rw [← hupd_noop]
      exact hv.update_spec hth hins hq hval

/-- Width bounds and `RawTreeValid` preservation across `splitFullNode`. -/
private theorem splitFullNode_raw_spec {L : BTreeEpochLayout} {alloc alloc' leftIdx rightIdx : ℕ}
    {nodes nodes' : ℕ → BTreeNode} {T : BTreeTree} {frontier : ℕ}
    (hvL : L.Valid L.w frontier)
    (hr : RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin alloc nodes T)
    (hfull : metaCount (nodes T.rootIdx).metaWord = 2 * L.tMin - 1)
    (hal_le : alloc ≤ alloc') (hl_lt : leftIdx < alloc') (hr_lt : rightIdx < alloc')
    (hl_not : ∀ v ∈ T.nodeSet.erase T.rootIdx, v ≠ leftIdx)
    (hr_not : ∀ v ∈ T.nodeSet.erase T.rootIdx, v ≠ rightIdx)
    (hl_eq : nodes' leftIdx = (splitFullNode L.fpBits L.wValLane L.tMin (nodes T.rootIdx)).left)
    (hr_eq : nodes' rightIdx = (splitFullNode L.fpBits L.wValLane L.tMin (nodes T.rootIdx)).right)
    (her : ∀ v ∈ T.nodeSet.erase T.rootIdx, nodes' v = nodes v) :
    let sp := splitFullNode L.fpBits L.wValLane L.tMin (nodes T.rootIdx)
    sp.left.metaWord < 2 ^ L.wMeta ∧ sp.left.keysWord < 2 ^ L.wKeys ∧
      sp.left.valsWord < 2 ^ L.wVals ∧
    sp.right.metaWord < 2 ^ L.wMeta ∧ sp.right.keysWord < 2 ^ L.wKeys ∧
      sp.right.valsWord < 2 ^ L.wVals ∧
    ∃ leftT rightT : BTreeTree,
      leftT.rootIdx = leftIdx ∧ rightT.rootIdx = rightIdx ∧
      leftT.height ≤ T.height ∧ rightT.height ≤ T.height ∧
      metaCount (nodes' leftIdx).metaWord < 2 * L.tMin - 1 ∧
      metaCount (nodes' rightIdx).metaWord < 2 * L.tMin - 1 ∧
      leftT.nodeSet ⊆ insert leftIdx (T.nodeSet.erase T.rootIdx) ∧
      rightT.nodeSet ⊆ insert rightIdx (T.nodeSet.erase T.rootIdx) ∧
      (leftIdx ≠ rightIdx → Disjoint leftT.nodeSet rightT.nodeSet) ∧
      RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin alloc' nodes' leftT ∧
      RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin alloc' nodes' rightT := by
  intro sp
  have h8 := hvL.2.2.2.1
  have hm_cap := hvL.2.2.2.2.2.2.2.2.2.2.2.1
  have hwk_def := hvL.2.2.2.2.2.2.2.1
  have hwv_def := hvL.2.2.2.2.2.2.2.2.1
  have h2t_eq : L.tMin + (L.tMin - 1) = 2 * L.tMin - 1 := by omega
  have h2t_eq2 : L.tMin + L.tMin = 2 * L.tMin - 1 + 1 := by omega
  cases T with
  | leaf cidx cnt =>
    obtain ⟨_, hmw, _, _, hkw, hvw, hlanes⟩ := hr
    dsimp only [BTreeTree.rootIdx, sp] at hfull hl_eq hr_eq hl_not hr_not her ⊢
    rw [hmw, metaCount_mkNodeMeta] at hfull; subst hfull
    have hsp_def : splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx) =
        ⟨⟨mkNodeMeta true L.tMin, wordTakeLow (L.fpBits + 2) L.tMin (nodes cidx).keysWord,
          wordTakeLow L.wValLane L.tMin (nodes cidx).valsWord⟩,
         laneGet (L.fpBits + 2) (nodes cidx).keysWord (L.tMin - 1),
         ⟨mkNodeMeta true (L.tMin - 1), wordDropLow (L.fpBits + 2) L.tMin (nodes cidx).keysWord,
          wordDropLow L.wValLane L.tMin (nodes cidx).valsWord⟩⟩ := by
      dsimp only [splitFullNode]; rw [hmw, metaIsLeaf_mkNodeMeta]; rfl
    have hlm : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).left.metaWord <
        2 ^ L.wMeta := by rw [hsp_def]; dsimp [mkNodeMeta]; omega
    have hrm : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).right.metaWord <
        2 ^ L.wMeta := by rw [hsp_def]; dsimp [mkNodeMeta]; omega
    have hlk_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).left.keysWord <
        2 ^ (L.tMin * (L.fpBits + 2)) := by
      rw [hsp_def]; exact wordTakeLow_lt _ _ _
    have hlv_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).left.valsWord <
        2 ^ (L.tMin * L.wValLane) := by
      rw [hsp_def]; exact wordTakeLow_lt _ _ _
    have hrk_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).right.keysWord <
        2 ^ ((L.tMin - 1) * (L.fpBits + 2)) := by
      rw [hsp_def]; exact wordDropLow_lt (by simpa only [h2t_eq] using hkw)
    have hrv_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).right.valsWord <
        2 ^ ((L.tMin - 1) * L.wValLane) := by
      rw [hsp_def]; exact wordDropLow_lt (by simpa only [h2t_eq] using hvw)
    refine ⟨hlm, hwk_def ▸ hlk_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      hwv_def ▸ hlv_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      hrm, hwk_def ▸ hrk_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      hwv_def ▸ hrv_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      .leaf leftIdx L.tMin, .leaf rightIdx (L.tMin - 1), rfl, rfl, le_rfl, le_rfl,
      by rw [hl_eq, hsp_def]; dsimp; rw [metaCount_mkNodeMeta]; omega,
      by rw [hr_eq, hsp_def]; dsimp; rw [metaCount_mkNodeMeta]; omega,
      by simp [BTreeTree.nodeSet], by simp [BTreeTree.nodeSet],
      fun hne => by simp [BTreeTree.nodeSet, hne], ?_, ?_⟩
    · refine ⟨hl_lt, by rw [hl_eq, hsp_def], by omega, by rw [hl_eq]; exact hlm,
        by rw [hl_eq]; exact hlk_t, by rw [hl_eq]; exact hlv_t, fun j hj => ?_⟩
      rw [hl_eq, hsp_def]; dsimp only
      rw [laneGet_wordTakeLow, ite_eq_left hj]
      exact hlanes j (by omega)
    · refine ⟨hr_lt, by rw [hr_eq, hsp_def], by omega, by rw [hr_eq]; exact hrm,
        by rw [hr_eq]; exact hrk_t, by rw [hr_eq]; exact hrv_t, fun j hj => ?_⟩
      rw [hr_eq, hsp_def]; dsimp only
      rw [laneGet_wordDropLow]
      exact hlanes (L.tMin + j) (by omega)
  | branch cidx cnt cs =>
    obtain ⟨_, hmw, _, _, hkw, hvw, hlanes, hnot, hdisj, hcs⟩ := hr
    dsimp only [BTreeTree.rootIdx, sp] at hfull hl_eq hr_eq hl_not hr_not her ⊢
    rw [hmw, metaCount_mkNodeMeta] at hfull; subst hfull
    have hsp_def : splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx) =
        ⟨⟨mkNodeMeta false (L.tMin - 1),
          wordTakeLow (L.fpBits + 2) (L.tMin - 1) (nodes cidx).keysWord,
          wordTakeLow L.wValLane L.tMin (nodes cidx).valsWord⟩,
         laneGet (L.fpBits + 2) (nodes cidx).keysWord (L.tMin - 1),
         ⟨mkNodeMeta false (L.tMin - 1),
          wordDropLow (L.fpBits + 2) L.tMin (nodes cidx).keysWord,
          wordDropLow L.wValLane L.tMin (nodes cidx).valsWord⟩⟩ := by
      dsimp only [splitFullNode]; rw [hmw, metaIsLeaf_mkNodeMeta]; rfl
    have hlm : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).left.metaWord <
        2 ^ L.wMeta := by rw [hsp_def]; dsimp [mkNodeMeta]; omega
    have hrm : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).right.metaWord <
        2 ^ L.wMeta := by rw [hsp_def]; dsimp [mkNodeMeta]; omega
    have hlk_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).left.keysWord <
        2 ^ ((L.tMin - 1) * (L.fpBits + 2)) := by
      rw [hsp_def]; exact wordTakeLow_lt _ _ _
    have hlv_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).left.valsWord <
        2 ^ (((L.tMin - 1) + 1) * L.wValLane) := by
      rw [hsp_def, Nat.sub_add_cancel (by omega)]; exact wordTakeLow_lt _ _ _
    have hrk_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).right.keysWord <
        2 ^ ((L.tMin - 1) * (L.fpBits + 2)) := by
      rw [hsp_def]; exact wordDropLow_lt (by simpa only [h2t_eq] using hkw)
    have hrv_t : (splitFullNode L.fpBits L.wValLane L.tMin (nodes cidx)).right.valsWord <
        2 ^ (((L.tMin - 1) + 1) * L.wValLane) := by
      rw [hsp_def, Nat.sub_add_cancel (by omega)]
      exact wordDropLow_lt (by simpa only [h2t_eq2] using hvw)
    let csL : Fin (L.tMin - 1 + 1) → BTreeTree := fun i => cs ⟨i.val, by omega⟩
    let csR : Fin (L.tMin - 1 + 1) → BTreeTree := fun i => cs ⟨L.tMin + i.val, by omega⟩
    have hin_er : ∀ k : Fin (2 * L.tMin - 1 + 1), ∀ v ∈ (cs k).nodeSet,
        v ∈ (BTreeTree.branch cidx (2 * L.tMin - 1) cs).nodeSet.erase cidx := by
      intro k v hvk
      exact mem_erase.mpr ⟨fun heq => hnot k (heq ▸ hvk),
        mem_insert_of_mem (mem_biUnion.mpr ⟨k, mem_univ k, hvk⟩)⟩
    refine ⟨hlm, hwk_def ▸ hlk_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      hwv_def ▸ hlv_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      hrm, hwk_def ▸ hrk_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      hwv_def ▸ hrv_t.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))),
      .branch leftIdx (L.tMin - 1) csL, .branch rightIdx (L.tMin - 1) csR,
      rfl, rfl, ?_, ?_,
      by rw [hl_eq, hsp_def]; dsimp; rw [metaCount_mkNodeMeta]; omega,
      by rw [hr_eq, hsp_def]; dsimp; rw [metaCount_mkNodeMeta]; omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [BTreeTree.height]
      exact Nat.add_le_add_left (Finset.sup_le fun i _ =>
        Finset.le_sup (f := fun k : Fin (2 * L.tMin - 1 + 1) => (cs k).height)
          (mem_univ (⟨i.val, by omega⟩ : Fin (2 * L.tMin - 1 + 1)))) 1
    · dsimp only [BTreeTree.height]
      exact Nat.add_le_add_left (Finset.sup_le fun i _ =>
        Finset.le_sup (f := fun k : Fin (2 * L.tMin - 1 + 1) => (cs k).height)
          (mem_univ (⟨L.tMin + i.val, by omega⟩ : Fin (2 * L.tMin - 1 + 1)))) 1
    · intro v hv_in
      rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
      rcases hv_in with rfl | ⟨i, _, hvi⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (hin_er ⟨i.val, by omega⟩ v hvi)
    · intro v hv_in
      rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hv_in
      rcases hv_in with rfl | ⟨i, _, hvi⟩
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (hin_er ⟨L.tMin + i.val, by omega⟩ v hvi)
    · intro hne_lr
      rw [Finset.disjoint_left]
      intro v hvl hvr
      rw [BTreeTree.nodeSet, mem_insert, mem_biUnion] at hvl hvr
      rcases hvl with rfl | ⟨i, _, hvi⟩
      · rcases hvr with heq | ⟨j, _, hvj⟩
        · exact hne_lr heq
        · exact (hl_not _ (hin_er _ _ hvj)).symm rfl
      · rcases hvr with rfl | ⟨j, _, hvj⟩
        · exact hr_not _ (hin_er _ _ hvi) rfl
        · exact Finset.disjoint_left.mp
            (hdisj ⟨i.val, by omega⟩ ⟨L.tMin + j.val, by omega⟩
              (Fin.ne_of_val_ne (by dsimp; omega))) hvi hvj
    · refine ⟨hl_lt, by rw [hl_eq, hsp_def], by omega, by rw [hl_eq]; exact hlm,
        by rw [hl_eq]; exact hlk_t, by rw [hl_eq]; exact hlv_t, fun j hj => ?_,
        fun i hmem => hl_not _ (hin_er _ _ hmem) rfl,
        fun i j hij => hdisj ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
          (Fin.ne_of_val_ne (by dsimp; exact Fin.val_ne_of_ne hij)),
        fun i => ?_⟩
      · rw [hl_eq, hsp_def]; dsimp only
        rw [laneGet_wordTakeLow, ite_eq_left hj]; exact hlanes j (by omega)
      · rw [hl_eq, hsp_def]; dsimp only
        rw [laneGet_wordTakeLow, ite_eq_left (by omega : i.val < L.tMin)]
        exact ⟨(hcs ⟨i.val, by omega⟩).1,
          (hcs ⟨i.val, by omega⟩).2.frame hal_le fun v hvi => her v (hin_er _ v hvi)⟩
    · refine ⟨hr_lt, by rw [hr_eq, hsp_def], by omega, by rw [hr_eq]; exact hrm,
        by rw [hr_eq]; exact hrk_t, by rw [hr_eq]; exact hrv_t, fun j hj => ?_,
        fun i hmem => hr_not _ (hin_er _ _ hmem) rfl,
        fun i j hij => hdisj ⟨L.tMin + i.val, by omega⟩ ⟨L.tMin + j.val, by omega⟩
          (Fin.ne_of_val_ne (by have := Fin.val_ne_of_ne hij; dsimp; omega)),
        fun i => ?_⟩
      · rw [hr_eq, hsp_def]; dsimp only
        rw [laneGet_wordDropLow]; exact hlanes (L.tMin + j) (by omega)
      · rw [hr_eq, hsp_def]; dsimp only
        rw [laneGet_wordDropLow]
        exact ⟨(hcs ⟨L.tMin + i.val, by omega⟩).1,
          (hcs ⟨L.tMin + i.val, by omega⟩).2.frame hal_le fun v hvi => her v (hin_er _ v hvi)⟩

/-- Exact `extractBTreeSlice` refinement along `descendSplitStepProg` iterated `fuel` times. -/
private theorem descendSplit_iter_spec {L : BTreeEpochLayout} {b role q : ℕ}
    (hb : b < L.numBuckets) (hrole : role < 3) (hq : q < 2 ^ L.fpBits) :
    ∀ (fuel : ℕ) (s : Memory.State) {T : BTreeTree},
      L.Valid L.w s.frontier →
      RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin
        (extractBTreeSlice L b role s.mem).alloc (extractBTreeSlice L b role s.mem).nodes T →
      metaCount ((extractBTreeSlice L b role s.mem).nodes T.rootIdx).metaWord < 2 * L.tMin - 1 →
      T.height ≤ fuel →
      (extractBTreeSlice L b role s.mem).alloc + fuel < L.nSlice →
      let sl := extractBTreeSlice L b role s.mem
      let p_pure := descendSplitToLeaf L.fpBits L.wValLane L.tMin fuel sl T.rootIdx q
      let s' := (Memory.spec 0).clientState s
        (iterate descendSplitStepProg (L.toSliceCtx b role, q) fuel T.rootIdx)
      let leaf_prog := (Memory.spec 0).clientResult s
        (iterate descendSplitStepProg (L.toSliceCtx b role, q) fuel T.rootIdx)
      s'.frontier = s.frontier ∧
      memoryCost (iterate descendSplitStepProg (L.toSliceCtx b role, q) fuel T.rootIdx) s ≤
        72 * fuel ∧
      extractBTreeSlice L b role s'.mem = p_pure.1 ∧
      leaf_prog = p_pure.2 ∧
      p_pure.1.alloc ≤ sl.alloc + fuel ∧
      (∃ cnt, RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin p_pure.1.alloc p_pure.1.nodes
        (.leaf p_pure.2 cnt) ∧ cnt < 2 * L.tMin - 1) ∧
      (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
        extractBTreeSlice L b' role' s'.mem = extractBTreeSlice L b' role' s.mem) ∧
      (∀ slot < 16 * L.numBuckets, slot ≠ 16 * b + 6 + 2 * role →
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w s'.mem slot =
          readPacked (L.metaBase + L.offBkt) L.ptrB L.w s.mem slot) ∧
      (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s T hvL hr hnf hht _
    cases T with
    | leaf idx cnt =>
      dsimp only [BTreeTree.rootIdx] at hnf ⊢
      have hcnt_lt : cnt < 2 * L.tMin - 1 := by
        rw [hr.2.1, metaCount_mkNodeMeta] at hnf; exact hnf
      exact ⟨rfl, Nat.zero_le _, rfl, rfl, le_rfl, ⟨cnt, hr, hcnt_lt⟩,
        fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
    | branch _ _ _ => simp [BTreeTree.height] at hht
  | succ fuel ih =>
    intro s T hvL hr hnf hht hal_ns
    set sl := extractBTreeSlice L b role s.mem with hsl_def
    cases T with
    | leaf idx cnt =>
      dsimp only [BTreeTree.rootIdx] at hnf ⊢
      have hmw := hr.2.1
      have hcnt_lt : cnt < 2 * L.tMin - 1 := by rw [hmw, metaCount_mkNodeMeta] at hnf; exact hnf
      have hl : (sl.nodes idx).metaWord % 2 = 1 := by
        rw [hmw]; unfold mkNodeMeta; simp only [↓reduceIte]; omega
      obtain ⟨hr_rn, hst_rn, hc_rn⟩ := readSliceNodeAtProg_spec L b role idx s
      change _ = ((sl.nodes idx).metaWord,
        ((sl.nodes idx).keysWord, (sl.nodes idx).valsWord)) at hr_rn
      dsimp only [BTreeEpochLayout.toNodeCtx] at hr_rn hst_rn hc_rn
      have hstep_st : (Memory.spec 0).clientState s
          (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) = s := by
        unfold descendSplitStepProg; dsimp_slice_ctx; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, hst_rn, hr_rn]
        simp [hl]
      have hstep_res : (Memory.spec 0).clientResult s
          (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) = idx := by
        unfold descendSplitStepProg; dsimp_slice_ctx; simp only [pure_bind]
        rw [prog_clientResult_bind, hst_rn, hr_rn]; simp [hl]
      have hleaf_iter : ∀ f,
          (Memory.spec 0).clientState s
            (iterate descendSplitStepProg (L.toSliceCtx b role, q) f idx) = s ∧
          (Memory.spec 0).clientResult s
            (iterate descendSplitStepProg (L.toSliceCtx b role, q) f idx) = idx ∧
          memoryCost (iterate descendSplitStepProg (L.toSliceCtx b role, q) f idx) s ≤
            6 * f := by
        have hstep_cost :
            memoryCost (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) s ≤ 6 := by
          unfold descendSplitStepProg; dsimp_slice_ctx
          simp only [pure_bind]
          rw [Realization.memoryCost_bind', hst_rn, hr_rn]
          simp only [hl, ↓reduceIte, memoryCost_pure, add_zero]; exact hc_rn
        intro f; induction f with
        | zero => exact ⟨rfl, rfl, Nat.zero_le _⟩
        | succ f ihf =>
          unfold iterate
          rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', hstep_st, hstep_res]
          exact ⟨ihf.1, ihf.2.1, by have := ihf.2.2; omega⟩
      have hpure_eq : descendSplitToLeaf L.fpBits L.wValLane L.tMin (fuel + 1) sl idx q =
          (sl, idx) := by dsimp only [descendSplitToLeaf]; rw [hmw, metaIsLeaf_mkNodeMeta]; rfl
      obtain ⟨hi_st, hi_res, hi_cost⟩ := hleaf_iter (fuel + 1)
      change (let sl0 := extractBTreeSlice L b role s.mem
        let p_pure := descendSplitToLeaf L.fpBits L.wValLane L.tMin (fuel + 1) sl0 idx q
        let s' := (Memory.spec 0).clientState s
          (iterate descendSplitStepProg (L.toSliceCtx b role, q) (fuel + 1) idx)
        let leaf_prog := (Memory.spec 0).clientResult s
          (iterate descendSplitStepProg (L.toSliceCtx b role, q) (fuel + 1) idx)
        s'.frontier = s.frontier ∧ _ ∧ extractBTreeSlice L b role s'.mem = p_pure.1 ∧
          leaf_prog = p_pure.2 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
      dsimp only
      rw [show extractBTreeSlice L b role s.mem = sl from rfl, hpure_eq, hi_st, hi_res]
      exact ⟨rfl, by omega, rfl, rfl, Nat.le_add_right _ _, ⟨cnt, hr, hcnt_lt⟩,
        fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
    | branch idx cnt cs =>
      obtain ⟨hidx_al, hmw, _, hmw_lt, hkw, hvw, hlanes, hnot, hdisj, hcs⟩ := hr
      have hcnt_lt : cnt < 2 * L.tMin - 1 := by
        dsimp only [BTreeTree.rootIdx] at hnf; rw [hmw, metaCount_mkNodeMeta] at hnf; exact hnf
      have hcnt_2t : cnt < 2 * L.tMin := by omega
      obtain ⟨hrank_eq, hrank_le⟩ := swarRankClampedProg_eq_swarRank hcnt_2t
        hvL.2.2.2.2.2.2.2.2.2.2.2.2.1 hq hkw hlanes s
      set r := swarRank L.fpBits (2 * L.tMin) cnt q (sl.nodes idx).keysWord
      change _ = r at hrank_eq
      let r_fin : Fin (cnt + 1) := ⟨r, Nat.lt_succ_of_le hrank_le⟩
      set childIdx := (cs r_fin).rootIdx with hchildIdx_def
      have hval_r : laneGet L.wValLane (sl.nodes idx).valsWord r = childIdx := (hcs r_fin).1
      have hht_c : (cs r_fin).height ≤ fuel := by
        dsimp only [BTreeTree.height] at hht
        have hle := Finset.le_sup (f := fun i => (cs i).height) (mem_univ r_fin)
        omega
      have hl_idx : (sl.nodes idx).metaWord % 2 ≠ 1 := by
        rw [hmw]; unfold mkNodeMeta; simp only [Bool.false_eq_true, ↓reduceIte]; omega
      have hcnt_sh : (sl.nodes idx).metaWord >>> 1 = cnt := by
        rw [Nat.shiftRight_eq_div_pow, pow_one, hmw]; exact metaCount_mkNodeMeta false cnt
      have hch_mc_eq :
          (sl.nodes childIdx).metaWord >>> 1 = metaCount (sl.nodes childIdx).metaWord :=
        Nat.shiftRight_eq_div_pow _ 1
      obtain ⟨hrn_i_res, hrn_i_st, hrn_i_c⟩ := readSliceNodeAtProg_spec L b role idx s
      obtain ⟨hrn_c_res, hrn_c_st, hrn_c_c⟩ := readSliceNodeAtProg_spec L b role childIdx s
      change _ = ((sl.nodes idx).metaWord,
        ((sl.nodes idx).keysWord, (sl.nodes idx).valsWord)) at hrn_i_res
      change _ = ((sl.nodes childIdx).metaWord,
        ((sl.nodes childIdx).keysWord, (sl.nodes childIdx).valsWord)) at hrn_c_res
      dsimp only [BTreeEpochLayout.toNodeCtx] at hrn_i_res hrn_i_st hrn_i_c
      dsimp only [BTreeEpochLayout.toNodeCtx] at hrn_c_res hrn_c_st hrn_c_c
      have hch_cnt_le : metaCount (sl.nodes childIdx).metaWord ≤ 2 * L.tMin - 1 := by
        have hrc := (hcs r_fin).2
        cases hc_eq : cs r_fin with
        | leaf cidx ccnt =>
          rw [hc_eq] at hrc; have : childIdx = cidx := by dsimp [childIdx]; rw [hc_eq]; rfl
          rw [this, hrc.2.1, metaCount_mkNodeMeta]; exact hrc.2.2.1
        | branch cidx ccnt _ =>
          rw [hc_eq] at hrc; have : childIdx = cidx := by dsimp [childIdx]; rw [hc_eq]; rfl
          rw [this, hrc.2.1, metaCount_mkNodeMeta]; exact hrc.2.2.1
      by_cases hfull_c : metaCount (sl.nodes childIdx).metaWord = 2 * L.tMin - 1
      · -- Full child `childIdx`: split into `(childIdx, rightIdx = sl.alloc)` and update `idx`!
        have hsh_c : (sl.nodes childIdx).metaWord >>> 1 = 2 * L.tMin - 1 :=
          hch_mc_eq.trans hfull_c
        set sp := splitFullNode L.fpBits L.wValLane L.tMin (sl.nodes childIdx)
        set rightIdx := sl.alloc
        set parentNd' : BTreeNode :=
          ⟨mkNodeMeta false (cnt + 1),
            wordInsertAt (L.fpBits + 2) r sp.sep (sl.nodes idx).keysWord,
            wordInsertAt L.wValLane (r + 1) rightIdx (sl.nodes idx).valsWord⟩
        have hch_al : childIdx < sl.alloc :=
          (hcs r_fin).2.nodeSet_lt childIdx (cs r_fin).rootIdx_mem_nodeSet
        have hch_ns : childIdx < L.nSlice := by omega
        have hr_ns : rightIdx < L.nSlice := by dsimp [rightIdx]; omega
        have hidx_ns : idx < L.nSlice := by omega
        have hch_ne_idx : childIdx ≠ idx := fun heq =>
          hnot r_fin (heq ▸ (cs r_fin).rootIdx_mem_nodeSet)
        have hidx_ne_r : idx ≠ rightIdx := by dsimp [rightIdx]; omega
        have hlr_ne : childIdx ≠ rightIdx := by dsimp [rightIdx]; omega
        set nodes1 := Function.update sl.nodes childIdx sp.left
        set nodes2 := Function.update nodes1 rightIdx sp.right
        set nodes3 := Function.update nodes2 idx parentNd'
        set sl_mid : BTreeSlice := { sl with alloc := sl.alloc + 1, nodes := nodes3 }
        have hl_eq3 : nodes3 childIdx = sp.left := by
          dsimp only [nodes3, nodes2, nodes1]
          rw [Function.update_of_ne hch_ne_idx, Function.update_of_ne hlr_ne, Function.update_self]
        have hr_eq3 : nodes3 rightIdx = sp.right := by
          dsimp only [nodes3, nodes2]
          rw [Function.update_of_ne hidx_ne_r.symm, Function.update_self]
        have her3 : ∀ v ∈ (cs r_fin).nodeSet.erase childIdx, nodes3 v = sl.nodes v := by
          intro v hv_er
          obtain ⟨hne_c, hv_in⟩ := mem_erase.mp hv_er
          have hv_lt : v < sl.alloc := (hcs r_fin).2.nodeSet_lt v hv_in
          have hne_r : v ≠ rightIdx := by dsimp [rightIdx]; omega
          have hne_i : v ≠ idx := fun heq => hnot r_fin (heq ▸ hv_in)
          dsimp only [nodes3, nodes2, nodes1]
          rw [Function.update_of_ne hne_i, Function.update_of_ne hne_r, Function.update_of_ne hne_c]
        obtain ⟨hlm, hlk, hlv, hrm, hrk, hrv, leftT, rightT, hrtL, hrtR, hhtL, hhtR,
          hnfL, hnfR, _, _, _, hrawL, hrawR⟩ :=
          splitFullNode_raw_spec (alloc' := sl_mid.alloc) (nodes' := nodes3)
            (leftIdx := childIdx) (rightIdx := rightIdx) hvL (hcs r_fin).2 hfull_c
            (by dsimp [sl_mid]; omega) (by dsimp [sl_mid]; omega)
            (by dsimp [sl_mid, rightIdx]; omega)
            (fun v hv => (mem_erase.mp hv).1)
            (fun v hv => by
              have := (hcs r_fin).2.nodeSet_lt v (mem_erase.mp hv).2; dsimp [rightIdx]; omega)
            hl_eq3 hr_eq3 her3
        have hpm : parentNd'.metaWord < 2 ^ L.wMeta := by
          dsimp only [parentNd', mkNodeMeta]; simp only [Bool.false_eq_true, ↓reduceIte]
          have := hvL.2.2.2.2.2.2.2.2.2.2.2.1; omega
        have hpk : parentNd'.keysWord < 2 ^ L.wKeys := by
          rw [hvL.2.2.2.2.2.2.2.1]
          have hsep_lt : sp.sep < 2 ^ (L.fpBits + 2) := by
            dsimp only [sp, splitFullNode]; split_ifs <;> exact laneGet_lt _ _ _
          exact (wordInsertAt_lt hrank_le hsep_lt hkw).trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        have hpv : parentNd'.valsWord < 2 ^ L.wVals := by
          rw [hvL.2.2.2.2.2.2.2.2.1]
          have hr_val : rightIdx < 2 ^ L.wValLane := hr_ns.trans hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          exact (wordInsertAt_lt (Nat.succ_le_succ hrank_le) hr_val hvw).trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        have hal1_pb : rightIdx + 1 < 2 ^ L.ptrB :=
          (by dsimp [rightIdx]; omega : rightIdx + 1 ≤ L.nSlice).trans_lt
            hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        obtain ⟨he1, ho1, hb1, ha1⟩ := extractBTreeSlice_writeNode (mem := s.mem) (u := childIdx)
          (nd := sp.left) hvL hb hrole hch_ns hlm hlk hlv
        set m1 := writePacked (L.metaBase + L.offVals) L.wVals L.w
          (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
            (writePacked (L.metaBase + L.offMeta) L.wMeta L.w s.mem
              ((3 * b + role) * L.nSlice + childIdx) sp.left.metaWord)
            ((3 * b + role) * L.nSlice + childIdx) sp.left.keysWord)
          ((3 * b + role) * L.nSlice + childIdx) sp.left.valsWord with hm1_def
        obtain ⟨he2, ho2, hb2, ha2⟩ := extractBTreeSlice_writeNode (mem := m1) (u := rightIdx)
          (nd := sp.right) hvL hb hrole hr_ns hrm hrk hrv
        set m2 := writePacked (L.metaBase + L.offVals) L.wVals L.w
          (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
            (writePacked (L.metaBase + L.offMeta) L.wMeta L.w m1
              ((3 * b + role) * L.nSlice + rightIdx) sp.right.metaWord)
            ((3 * b + role) * L.nSlice + rightIdx) sp.right.keysWord)
          ((3 * b + role) * L.nSlice + rightIdx) sp.right.valsWord with hm2_def
        obtain ⟨he3, ho3, hb3, ha3⟩ := extractBTreeSlice_writeNode (mem := m2) (u := idx)
          (nd := parentNd') hvL hb hrole hidx_ns hpm hpk hpv
        set m3 := writePacked (L.metaBase + L.offVals) L.wVals L.w
          (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
            (writePacked (L.metaBase + L.offMeta) L.wMeta L.w m2
              ((3 * b + role) * L.nSlice + idx) parentNd'.metaWord)
            ((3 * b + role) * L.nSlice + idx) parentNd'.keysWord)
          ((3 * b + role) * L.nSlice + idx) parentNd'.valsWord with hm3_def
        obtain ⟨he4, ho4, hb4, ha4⟩ := extractBTreeSlice_writeHdr (mem := m3) (isRoot := 0)
          (val := rightIdx + 1) hvL hb hrole (by decide) hal1_pb
        set m4 := writePacked (L.metaBase + L.offBkt) L.ptrB L.w m3
          (16 * b + 6 + 2 * role + 0) (rightIdx + 1) with hm4_def
        simp only [↓reduceIte] at he4
        have hm4_sl : extractBTreeSlice L b role m4 = sl_mid := by
          rw [hm4_def, he4, hm3_def, he3, hm2_def, he2, hm1_def, he1]
        set nextChild := if sp.sep < q then rightIdx else childIdx
        have hstep_run :
            (Memory.spec 0).clientState s (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) =
              ⟨m4, s.frontier⟩ ∧
            (Memory.spec 0).clientResult s (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) =
              nextChild ∧
            memoryCost (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) s ≤ 72 := by
          obtain ⟨hhdr_res, hhdr_st, hhdr_c⟩ := readSliceHdrAtProg_spec L b role s
          change _ = (sl.alloc, sl.root) at hhdr_res
          dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr_res hhdr_st hhdr_c
          obtain ⟨hsp_r, hsp_st, hsp_c⟩ := splitFullNodeAtProg_spec L (sl.nodes childIdx) s
          change _ = (((sp.left.metaWord, (sp.left.keysWord, sp.left.valsWord)), sp.sep),
            (sp.right.metaWord, (sp.right.keysWord, sp.right.valsWord))) at hsp_r
          dsimp only at hsp_st hsp_c
          have hp_mw : 2 * (cnt + 1) = mkNodeMeta false (cnt + 1) := by
            simp [mkNodeMeta]
          unfold descendSplitStepProg descendSplitBranchProg splitChildAndStepProg
            splitChildBodyProg finishChildSplitWritesProg computeChildSplitProg
          dsimp_slice_ctx; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', hrn_i_st, hrn_i_res]
          simp only [hl_idx, ↓reduceIte, hcnt_sh, StateTransitionSpec.clientState,
            prog_runClient_state_bind, prog_clientResult_bind,
            Realization.memoryCost_bind',
            runClient_state_swarRankClampedProg, hrank_eq, memoryCost_swarRankClampedProg,
            runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg,
            memoryCost_laneGetBoundedProg, hval_r,
            runClient_state_readSliceNodeAtProg, hrn_c_res, hsh_c,
            runClient_state_readSliceHdrAtProg, hhdr_res, hhdr_c]
          have hal_lt : sl.alloc < L.nSlice := hr_ns
          simp only [hal_lt, ↓reduceIte, bind_assoc, pure_bind,
            prog_runClient_state_bind, prog_clientResult_bind, Realization.memoryCost_bind',
            runClient_state_readSliceNodeAtProg, hrn_i_res, hcnt_sh, hrn_c_res,
            runClient_state_splitFullNodeAtProg, hsp_r, hsp_c,
            runClient_state_wordInsertAtBoundedProg, clientResult_wordInsertAtBoundedProg,
            memoryCost_wordInsertAtBoundedProg, hp_mw]
          unfold writeTwoNodesAtProg writeSliceNodeAtProg writeSliceHdrAtProg
          dsimp only [rightIdx] at hr_ns hm2_def hm4_def nextChild ⊢
          simp only [hch_ns, hr_ns, hidx_ns, Nat.zero_lt_succ, ↓reduceIte, bind_assoc, pure_bind,
            prog_runClient_state_bind,
            Realization.memoryCost_bind',
            runClient_state_writePackedCompGenProg,
            memoryCost_writePackedCompGenProg, hm1_def, hm2_def, hm3_def, hm4_def,
            parentNd', nextChild]
          refine ⟨?_, ?_, ?_⟩
          · split_ifs <;> simp [rightIdx]
          · split_ifs <;> simp [rightIdx]
          · split_ifs <;> simp only [memoryCost_pure] <;> omega
        let nextT : BTreeTree := if sp.sep < q then rightT else leftT
        have hnext_rt : nextT.rootIdx = nextChild := by
          dsimp only [nextT, nextChild]; split_ifs <;> simp [hrtR, hrtL]
        have hnext_raw : RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl_mid.alloc sl_mid.nodes
            nextT := by
          dsimp only [nextT]
          split_ifs
          · exact hrawR
          · exact hrawL
        have hnext_nf : metaCount (sl_mid.nodes nextT.rootIdx).metaWord < 2 * L.tMin - 1 := by
          rw [hnext_rt]; dsimp only [nextChild]
          split_ifs
          · exact hnfR
          · exact hnfL
        have hnext_ht : nextT.height ≤ fuel := by
          dsimp only [nextT]
          split_ifs
          · exact hhtR.trans hht_c
          · exact hhtL.trans hht_c
        obtain ⟨hfr_rec, hc_rec, hext_rec, hlf_rec, hal_rec, hcnt_rec, ho_rec, hb_rec, ha_rec⟩ :=
          ih ⟨m4, s.frontier⟩ (T := nextT) hvL (by rw [hm4_sl]; exact hnext_raw)
            (by rw [hm4_sl]; exact hnext_nf) hnext_ht
            (by rw [hm4_sl]; dsimp only [sl_mid]; omega)
        dsimp only at hfr_rec hal_rec
        rw [hnext_rt] at hfr_rec hc_rec ho_rec hb_rec ha_rec
        rw [hm4_sl, hnext_rt] at hext_rec hlf_rec hal_rec hcnt_rec
        have hpure_eq : descendSplitToLeaf L.fpBits L.wValLane L.tMin (fuel + 1) sl idx q =
            descendSplitToLeaf L.fpBits L.wValLane L.tMin fuel sl_mid nextChild q := by
          dsimp only [descendSplitToLeaf]
          rw [hmw, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
          simp only [Bool.false_eq_true, ↓reduceIte, r, hval_r, childIdx, hfull_c,
            beq_self_eq_true]
          rfl
        unfold iterate
        dsimp only [BTreeTree.rootIdx]
        rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
          Realization.memoryCost_bind', hstep_run.1, hstep_run.2.1]
        change (let sl0 := extractBTreeSlice L b role s.mem
          let p_pure := descendSplitToLeaf L.fpBits L.wValLane L.tMin (fuel + 1) sl0 idx q
          let s' := (Memory.spec 0).clientState ⟨m4, s.frontier⟩
            (iterate descendSplitStepProg (L.toSliceCtx b role, q) fuel nextChild)
          let leaf_prog := (Memory.spec 0).clientResult ⟨m4, s.frontier⟩
            (iterate descendSplitStepProg (L.toSliceCtx b role, q) fuel nextChild)
          s'.frontier = s.frontier ∧ _ ∧ extractBTreeSlice L b role s'.mem = p_pure.1 ∧
            leaf_prog = p_pure.2 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
        dsimp only
        rw [← hsl_def, hpure_eq]
        refine ⟨hfr_rec, by have := hstep_run.2.2; omega, hext_rec, hlf_rec,
          by dsimp only [sl_mid] at hal_rec ⊢; omega, hcnt_rec, ?_, ?_, ?_⟩
        · intro b' role' hb' hr' hne
          exact (ho_rec b' role' hb' hr' hne).trans
            ((ho4 b' role' hb' hr' hne).trans ((ho3 b' role' hb' hr' hne).trans
              ((ho2 b' role' hb' hr' hne).trans (ho1 b' role' hb' hr' hne))))
        · intro slot hsl hne0
          exact (hb_rec slot hsl hne0).trans
            ((hb4 slot hsl (by omega)).trans ((hb3 slot hsl).trans
              ((hb2 slot hsl).trans (hb1 slot hsl))))
        · intro addr ha
          exact (ha_rec addr ha).trans ((ha4 addr ha).trans ((ha3 addr ha).trans
            ((ha2 addr ha).trans (ha1 addr ha))))
      · -- Non-full child `childIdx`: zero writes!
        have hsh_c : (sl.nodes childIdx).metaWord >>> 1 ≠ 2 * L.tMin - 1 := by
          rw [hch_mc_eq]; exact hfull_c
        have hnf_c : metaCount (sl.nodes (cs r_fin).rootIdx).metaWord < 2 * L.tMin - 1 := by
          dsimp only [childIdx] at hch_cnt_le hfull_c; omega
        have hstep_run :
            (Memory.spec 0).clientState s (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) =
              s ∧
            (Memory.spec 0).clientResult s (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) =
              childIdx ∧
            memoryCost (descendSplitStepProg ((L.toSliceCtx b role, q), idx)) s ≤ 72 := by
          unfold descendSplitStepProg descendSplitBranchProg
          dsimp_slice_ctx; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', hrn_i_st, hrn_i_res]
          simp only [hl_idx, ↓reduceIte, hcnt_sh,
            prog_runClient_state_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', StateTransitionSpec.clientState,
            runClient_state_swarRankClampedProg, hrank_eq, memoryCost_swarRankClampedProg,
            runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg,
            memoryCost_laneGetBoundedProg, hval_r,
            runClient_state_readSliceNodeAtProg, hrn_c_res, hsh_c,
            prog_runClient_state_pure, prog_clientResult_pure, memoryCost_pure]
          exact ⟨trivial, trivial, by omega⟩
        obtain ⟨hfr_rec, hc_rec, hext_rec, hlf_rec, hal_rec, hcnt_rec, ho_rec, hb_rec, ha_rec⟩ :=
          ih s (T := cs r_fin) hvL (hcs r_fin).2 hnf_c hht_c (by rw [← hsl_def]; omega)
        rw [← hchildIdx_def] at hfr_rec hc_rec hext_rec hlf_rec hal_rec
        rw [← hchildIdx_def] at hcnt_rec ho_rec hb_rec ha_rec
        have hpure_eq : descendSplitToLeaf L.fpBits L.wValLane L.tMin (fuel + 1) sl idx q =
            descendSplitToLeaf L.fpBits L.wValLane L.tMin fuel sl childIdx q := by
          dsimp only [descendSplitToLeaf]
          rw [hmw, metaIsLeaf_mkNodeMeta, metaCount_mkNodeMeta]
          simp [r, hval_r, childIdx, hfull_c]
        unfold iterate
        dsimp only [BTreeTree.rootIdx]
        rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
          Realization.memoryCost_bind', hstep_run.1, hstep_run.2.1]
        change (let sl0 := extractBTreeSlice L b role s.mem
          let p_pure := descendSplitToLeaf L.fpBits L.wValLane L.tMin (fuel + 1) sl0 idx q
          let s' := (Memory.spec 0).clientState s
            (iterate descendSplitStepProg (L.toSliceCtx b role, q) fuel childIdx)
          let leaf_prog := (Memory.spec 0).clientResult s
            (iterate descendSplitStepProg (L.toSliceCtx b role, q) fuel childIdx)
          s'.frontier = s.frontier ∧ _ ∧ extractBTreeSlice L b role s'.mem = p_pure.1 ∧
            leaf_prog = p_pure.2 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
        dsimp only
        rw [show extractBTreeSlice L b role s.mem = sl from rfl, hpure_eq]
        exact ⟨hfr_rec, by have := hstep_run.2.2; omega, hext_rec, hlf_rec,
          by rw [← hsl_def] at hal_rec; omega, hcnt_rec, ho_rec, hb_rec, ha_rec⟩

/-- Exact `ValidWhpSlice` refinement and frame preservation for `btreeInsertBoundedProg`. -/
theorem btreeInsertBoundedProg_spec {c N b role q val : ℕ} {s : Memory.State}
    {insCount : ℕ} {mapFn : ℕ → Option ℕ} {L : BTreeEpochLayout}
    (hth : whpThreshold c ≤ N)
    (hL_eq : L = epochBTreeLayout c L.w N L.metaBase)
    (hvL : L.Valid L.w s.frontier)
    (hb : b < L.numBuckets) (hrole : role < 3)
    (hins : insCount ≤ 8 * slabScale N ^ 12)
    (hv : ValidWhpSlice N insCount (extractBTreeSlice L b role s.mem) mapFn)
    (hq : q < 2 ^ fpBitsWhp N) (hval : val < 2 ^ valLaneBitsWhp N) :
    let s' := (Memory.spec 0).clientState s
      (btreeInsertBoundedProg (L.toSliceCtx b role, (q, val)))
    s'.frontier = s.frontier ∧
    memoryCost (btreeInsertBoundedProg (L.toSliceCtx b role, (q, val))) s ≤
      72 * hMaxBTree + 96 ∧
    extractBTreeSlice L b role s'.mem =
      btreeInsert (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N)
        (extractBTreeSlice L b role s.mem) q val ∧
    (extractBTreeSlice L b role s'.mem).alloc < nSliceWhp N ∧
    ValidWhpSlice N (insCount + 1) (extractBTreeSlice L b role s'.mem)
      (Function.update mapFn q (some val)) ∧
    (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
      extractBTreeSlice L b' role' s'.mem = extractBTreeSlice L b' role' s.mem) ∧
    (∀ slot < 16 * L.numBuckets,
      slot ≠ 16 * b + 6 + 2 * role → slot ≠ 16 * b + 7 + 2 * role →
      readPacked (L.metaBase + L.offBkt) L.ptrB L.w s'.mem slot =
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w s.mem slot) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) := by
  have hfp_eq : L.fpBits = fpBitsWhp N := by rw [hL_eq]; rfl
  have hwv_eq : L.wValLane = valLaneBitsWhp N := by rw [hL_eq]; rfl
  have htm_eq : L.tMin = tMinWhp N := by rw [hL_eq]; rfl
  have hns_eq : L.nSlice = nSliceWhp N := by rw [hL_eq]; rfl
  set sl := extractBTreeSlice L b role s.mem
  have h8 := hvL.2.2.2.1
  have h1_pb : 1 < 2 ^ L.ptrB := lt_of_le_of_lt
    (by have := hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega : 1 ≤ L.nSlice)
    hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  set sl1 := splitRootIfFull L.fpBits L.wValLane L.tMin (ensureRootSlice sl)
  have hprep :
      let s₁ := (Memory.spec 0).clientState s (prepareRootBoundedProg (L.toSliceCtx b role))
      let rt₁ := (Memory.spec 0).clientResult s (prepareRootBoundedProg (L.toSliceCtx b role))
      s₁.frontier = s.frontier ∧
      memoryCost (prepareRootBoundedProg (L.toSliceCtx b role)) s ≤ 64 ∧
      extractBTreeSlice L b role s₁.mem = sl1 ∧
      rt₁ = sl1.root ∧
      sl1.alloc + hMaxBTree < L.nSlice ∧
      (∃ T1 : BTreeTree,
        T1.rootIdx = sl1.root ∧ T1.height ≤ hMaxBTree ∧
        metaCount (sl1.nodes sl1.root).metaWord < 2 * L.tMin - 1 ∧
        RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl1.alloc sl1.nodes T1) ∧
      (∀ b' role', b' < L.numBuckets → role' < 3 → (b' ≠ b ∨ role' ≠ role) →
        extractBTreeSlice L b' role' s₁.mem = extractBTreeSlice L b' role' s.mem) ∧
      (∀ slot < 16 * L.numBuckets,
        slot ≠ 16 * b + 6 + 2 * role → slot ≠ 16 * b + 7 + 2 * role →
        readPacked (L.metaBase + L.offBkt) L.ptrB L.w s₁.mem slot =
          readPacked (L.metaBase + L.offBkt) L.ptrB L.w s.mem slot) ∧
      (∀ addr, ¬L.OwnsAddr addr → s₁.mem addr = s.mem addr) := by
    obtain ⟨hhdr_res, hhdr_st, hhdr_c⟩ := readSliceHdrAtProg_spec L b role s
    change _ = (sl.alloc, sl.root) at hhdr_res
    dsimp only [BTreeEpochLayout.toHdrCtx] at hhdr_res hhdr_st hhdr_c
    obtain ⟨halloc_ns, ⟨h0, rfl⟩ | ⟨ha_pos, T, hrt, hht_lt, _, _, hT⟩⟩ :=
      hv.alloc_and_height_lt hth hins
    · have h0_ns : 0 < L.nSlice := by have := hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
      have h1_wm : 1 < 2 ^ L.wMeta :=
        lt_of_lt_of_le (by omega : 1 < 4 * L.tMin) hvL.2.2.2.2.2.2.2.2.2.2.2.1
      obtain ⟨he1, ho1, hb1, ha1⟩ := extractBTreeSlice_writeNode (mem := s.mem) (u := 0)
        (nd := ⟨1, 0, 0⟩) hvL hb hrole h0_ns h1_wm (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      set m1 := writePacked (L.metaBase + L.offVals) L.wVals L.w
        (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
          (writePacked (L.metaBase + L.offMeta) L.wMeta L.w s.mem
            ((3 * b + role) * L.nSlice + 0) 1)
          ((3 * b + role) * L.nSlice + 0) 0)
        ((3 * b + role) * L.nSlice + 0) 0 with hm1_def
      obtain ⟨he2, ho2, hb2, ha2⟩ := extractBTreeSlice_writeHdr (mem := m1) (isRoot := 0)
        (val := 1) hvL hb hrole (by decide) h1_pb
      set m2 := writePacked (L.metaBase + L.offBkt) L.ptrB L.w m1
        (16 * b + 6 + 2 * role + 0) 1 with hm2_def
      obtain ⟨he3, ho3, hb3, ha3⟩ := extractBTreeSlice_writeHdr (mem := m2) (isRoot := 1)
        (val := 0) hvL hb hrole (by decide) (Nat.two_pow_pos _)
      set m3 := writePacked (L.metaBase + L.offBkt) L.ptrB L.w m2
        (16 * b + 6 + 2 * role + 1) 0 with hm3_def
      simp only [↓reduceIte] at he2
      simp only [Nat.succ_ne_zero, ↓reduceIte] at he3
      have hsl1_eq : sl1 = ⟨1, 0, Function.update sl.nodes 0 ⟨mkNodeMeta true 0, 0, 0⟩⟩ := by
        have hens : ensureRootSlice sl =
            ⟨1, 0, Function.update sl.nodes 0 ⟨mkNodeMeta true 0, 0, 0⟩⟩ := by
          simp [ensureRootSlice, h0]
        dsimp only [sl1]; rw [hens]
        unfold splitRootIfFull
        have hne_f : (0 == 2 * L.tMin - 1) = false := beq_eq_false_iff_ne.mpr (by omega)
        simp [metaCount_mkNodeMeta, hne_f]
      have hm3_eq : extractBTreeSlice L b role m3 = sl1 := by
        rw [hm3_def, he3, hm2_def, he2, hm1_def, he1, hsl1_eq]; rfl
      have hpr_run :
          (Memory.spec 0).clientState s (prepareRootBoundedProg (L.toSliceCtx b role)) =
            ⟨m3, s.frontier⟩ ∧
          (Memory.spec 0).clientResult s (prepareRootBoundedProg (L.toSliceCtx b role)) = 0 ∧
          memoryCost (prepareRootBoundedProg (L.toSliceCtx b role)) s ≤ 64 := by
        unfold prepareRootBoundedProg initEmptyRootAtProg
        dsimp_slice_ctx; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
          Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_c]
        simp only [h0, ↓reduceIte]
        unfold writeSliceNodeAtProg writeSliceHdrAtProg
        simp [h0_ns, StateTransitionSpec.clientState, hm1_def, hm2_def, hm3_def]
      refine ⟨by rw [hpr_run.1], hpr_run.2.2, by rw [hpr_run.1]; exact hm3_eq,
        by rw [hpr_run.2.1, hsl1_eq],
        by rw [hsl1_eq, hns_eq, hMaxBTree_eq]; dsimp only; have := sixty_four_le_nSliceWhp N; omega,
        ⟨.leaf 0 0, by simp [hsl1_eq, BTreeTree.rootIdx], Nat.zero_le _,
          by simp [hsl1_eq, metaCount_mkNodeMeta]; omega,
          by
            dsimp only [RawTreeValid]
            rw [hsl1_eq]; dsimp only
            rw [Function.update_self]
            exact ⟨Nat.zero_lt_one, rfl, by omega, h1_wm, Nat.two_pow_pos _, Nat.two_pow_pos _,
              fun _ hj => absurd hj (Nat.not_lt_zero _)⟩⟩,
        fun b' r' hb' hr' hne => by
          rw [hpr_run.1]
          exact (ho3 b' r' hb' hr' hne).trans ((ho2 b' r' hb' hr' hne).trans
            (ho1 b' r' hb' hr' hne)),
        fun slot hsl hne0 hne1 => by
          rw [hpr_run.1]
          exact (hb3 slot hsl (by omega)).trans ((hb2 slot hsl (by omega)).trans (hb1 slot hsl)),
        fun addr ha => by
          rw [hpr_run.1]; exact (ha3 addr ha).trans ((ha2 addr ha).trans (ha1 addr ha))⟩
    · change sl.alloc + hMaxBTree + 4 < nSliceWhp N at halloc_ns
      have ha_nz : sl.alloc ≠ 0 := by omega
      have hens : ensureRootSlice sl = sl := by simp [ensureRootSlice, ha_nz]
      have hhi : 2 ^ L.fpBits - 1 < 2 ^ L.fpBits := Nat.sub_lt (Nat.two_pow_pos _) Nat.zero_lt_one
      have hraw : RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl.alloc sl.nodes T :=
        rawTreeValid_of_validSubtree (by omega) hvL.2.2.2.2.2.2.2.2.2.2.2.1 hhi
          (by simpa only [hfp_eq, hwv_eq, htm_eq] using hT)
      obtain ⟨hrn_res, hrn_st, hrn_c⟩ := readSliceNodeAtProg_spec L b role sl.root s
      change _ = ((sl.nodes sl.root).metaWord,
        ((sl.nodes sl.root).keysWord, (sl.nodes sl.root).valsWord)) at hrn_res
      dsimp only [BTreeEpochLayout.toNodeCtx] at hrn_res hrn_st hrn_c
      have hmc_sh : (sl.nodes sl.root).metaWord >>> 1 = metaCount (sl.nodes sl.root).metaWord :=
        Nat.shiftRight_eq_div_pow _ 1
      have hcnt_rt_le : metaCount (sl.nodes sl.root).metaWord ≤ 2 * L.tMin - 1 := by
        cases hT_eq : T with
        | leaf ridx rcnt =>
          rw [hT_eq] at hraw hrt; dsimp [BTreeTree.rootIdx] at hrt; subst hrt
          rw [hraw.2.1, metaCount_mkNodeMeta]; exact hraw.2.2.1
        | branch ridx rcnt _ =>
          rw [hT_eq] at hraw hrt; dsimp [BTreeTree.rootIdx] at hrt; subst hrt
          rw [hraw.2.1, metaCount_mkNodeMeta]; exact hraw.2.2.1
      by_cases hfull_rt : metaCount (sl.nodes sl.root).metaWord = 2 * L.tMin - 1
      · have hsh_rt : (sl.nodes sl.root).metaWord >>> 1 = 2 * L.tMin - 1 :=
          hmc_sh.trans hfull_rt
        have hal1_ns : sl.alloc + 1 < L.nSlice := by rw [hns_eq]; omega
        have hal0_ns : sl.alloc < L.nSlice := by omega
        have hrt_al : sl.root < sl.alloc := hrt ▸ hraw.nodeSet_lt T.rootIdx T.rootIdx_mem_nodeSet
        have hrt_ns : sl.root < L.nSlice := by omega
        set sp := splitFullNode L.fpBits L.wValLane L.tMin (sl.nodes sl.root)
        set leftIdx := sl.alloc
        set rightIdx := sl.alloc + 1
        set newVals := leftIdx + (rightIdx <<< L.wValLane)
        set newRootNd : BTreeNode := ⟨mkNodeMeta false 1, sp.sep, newVals⟩
        set nodes1 := Function.update sl.nodes leftIdx sp.left
        set nodes2 := Function.update nodes1 rightIdx sp.right
        set nodes3 := Function.update nodes2 sl.root newRootNd
        have hl_ne_rt : leftIdx ≠ sl.root := by dsimp [leftIdx]; omega
        have hr_ne_rt : rightIdx ≠ sl.root := by dsimp [rightIdx]; omega
        have hlr_ne : leftIdx ≠ rightIdx := by dsimp [leftIdx, rightIdx]; omega
        have hl_eq3 : nodes3 leftIdx = sp.left := by
          dsimp only [nodes3, nodes2, nodes1]
          rw [Function.update_of_ne hl_ne_rt, Function.update_of_ne hlr_ne, Function.update_self]
        have hr_eq3 : nodes3 rightIdx = sp.right := by
          dsimp only [nodes3, nodes2]
          rw [Function.update_of_ne hr_ne_rt, Function.update_self]
        have her3 : ∀ v ∈ T.nodeSet.erase T.rootIdx, nodes3 v = sl.nodes v := by
          intro v hv_er
          obtain ⟨hne_rt, hv_in⟩ := mem_erase.mp hv_er
          rw [hrt] at hne_rt
          have hv_lt : v < sl.alloc := hraw.nodeSet_lt v hv_in
          dsimp only [nodes3, nodes2, nodes1]
          rw [Function.update_of_ne hne_rt, Function.update_of_ne (by dsimp [rightIdx]; omega),
            Function.update_of_ne (by dsimp [leftIdx]; omega)]
        obtain ⟨hlm, hlk, hlv, hrm, hrk, hrv, leftT, rightT, hrtL, hrtR, hhtL, hhtR,
          _, _, hsubL, hsubR, hdisjLR, hrawL, hrawR⟩ :=
          splitFullNode_raw_spec (alloc' := sl.alloc + 2) (nodes' := nodes3)
            (leftIdx := leftIdx) (rightIdx := rightIdx) hvL hraw (hrt.symm ▸ hfull_rt)
            (by omega) (by dsimp [leftIdx]; omega) (by dsimp [rightIdx]; omega)
            (fun v hv => by have := hraw.nodeSet_lt v (mem_erase.mp hv).2; dsimp [leftIdx]; omega)
            (fun v hv => by have := hraw.nodeSet_lt v (mem_erase.mp hv).2; dsimp [rightIdx]; omega)
            (by simpa only [hrt] using hl_eq3) (by simpa only [hrt] using hr_eq3) her3
        rw [hrt] at hlm hlk hlv hrm hrk hrv
        have hnrm : newRootNd.metaWord < 2 ^ L.wMeta := by
          dsimp only [newRootNd, mkNodeMeta]; simp only [Bool.false_eq_true, ↓reduceIte]
          have := hvL.2.2.2.2.2.2.2.2.2.2.2.1; omega
        have hsep_fp : sp.sep < 2 ^ L.fpBits := by
          dsimp only [sp, splitFullNode]
          cases hT_eq : T with
          | leaf ridx rcnt =>
            rw [hT_eq] at hraw hrt; dsimp [BTreeTree.rootIdx] at hrt; subst hrt
            rw [hraw.2.1, metaCount_mkNodeMeta] at hfull_rt
            split_ifs <;> exact hraw.2.2.2.2.2.2 (L.tMin - 1) (by omega)
          | branch ridx rcnt _ =>
            rw [hT_eq] at hraw hrt; dsimp [BTreeTree.rootIdx] at hrt; subst hrt
            rw [hraw.2.1, metaCount_mkNodeMeta] at hfull_rt
            split_ifs <;> exact hraw.2.2.2.2.2.2.1 (L.tMin - 1) (by omega)
        have hnrk_1 : sp.sep < 2 ^ (1 * (L.fpBits + 2)) := by
          rw [one_mul]; exact hsep_fp.trans (Nat.pow_lt_pow_right Nat.one_lt_two (by omega))
        have hnrk : newRootNd.keysWord < 2 ^ L.wKeys := by
          rw [hvL.2.2.2.2.2.2.2.1]
          exact hnrk_1.trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        have hr_val : rightIdx < 2 ^ L.wValLane :=
          hal1_ns.trans hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hl_val : leftIdx < 2 ^ L.wValLane := by dsimp [leftIdx, rightIdx] at hr_val ⊢; omega
        have hnrv_2 : newVals < 2 ^ (2 * L.wValLane) := by
          dsimp only [newVals]; rw [Nat.shiftLeft_eq]
          have hle : rightIdx + 1 ≤ 2 ^ L.wValLane := hr_val
          calc leftIdx + rightIdx * 2 ^ L.wValLane
              < (rightIdx + 1) * 2 ^ L.wValLane := by ring_nf; omega
            _ ≤ 2 ^ L.wValLane * 2 ^ L.wValLane := Nat.mul_le_mul_right _ hle
            _ = 2 ^ (2 * L.wValLane) := by rw [← Nat.pow_add, Nat.two_mul]
        have hnrv : newRootNd.valsWord < 2 ^ L.wVals := by
          rw [hvL.2.2.2.2.2.2.2.2.1]
          exact hnrv_2.trans_le
            (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
        have hal2_ns : sl.alloc + 2 ≤ L.nSlice := by rw [hns_eq]; omega
        have hal2_pb : sl.alloc + 2 < 2 ^ L.ptrB :=
          hal2_ns.trans_lt hvL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        obtain ⟨he1, ho1, hb1, ha1⟩ := extractBTreeSlice_writeNode (mem := s.mem) (u := leftIdx)
          (nd := sp.left) hvL hb hrole hal0_ns hlm hlk hlv
        set m1 := writePacked (L.metaBase + L.offVals) L.wVals L.w
          (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
            (writePacked (L.metaBase + L.offMeta) L.wMeta L.w s.mem
              ((3 * b + role) * L.nSlice + leftIdx) sp.left.metaWord)
            ((3 * b + role) * L.nSlice + leftIdx) sp.left.keysWord)
          ((3 * b + role) * L.nSlice + leftIdx) sp.left.valsWord with hm1_def
        obtain ⟨he2, ho2, hb2, ha2⟩ := extractBTreeSlice_writeNode (mem := m1) (u := rightIdx)
          (nd := sp.right) hvL hb hrole hal1_ns hrm hrk hrv
        set m2 := writePacked (L.metaBase + L.offVals) L.wVals L.w
          (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
            (writePacked (L.metaBase + L.offMeta) L.wMeta L.w m1
              ((3 * b + role) * L.nSlice + rightIdx) sp.right.metaWord)
            ((3 * b + role) * L.nSlice + rightIdx) sp.right.keysWord)
          ((3 * b + role) * L.nSlice + rightIdx) sp.right.valsWord with hm2_def
        obtain ⟨he3, ho3, hb3, ha3⟩ := extractBTreeSlice_writeNode (mem := m2) (u := sl.root)
          (nd := newRootNd) hvL hb hrole hrt_ns hnrm hnrk hnrv
        set m3 := writePacked (L.metaBase + L.offVals) L.wVals L.w
          (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
            (writePacked (L.metaBase + L.offMeta) L.wMeta L.w m2
              ((3 * b + role) * L.nSlice + sl.root) newRootNd.metaWord)
            ((3 * b + role) * L.nSlice + sl.root) newRootNd.keysWord)
          ((3 * b + role) * L.nSlice + sl.root) newRootNd.valsWord with hm3_def
        obtain ⟨he4, ho4, hb4, ha4⟩ := extractBTreeSlice_writeHdr (mem := m3) (isRoot := 0)
          (val := sl.alloc + 2) hvL hb hrole (by decide) hal2_pb
        set m4 := writePacked (L.metaBase + L.offBkt) L.ptrB L.w m3
          (16 * b + 6 + 2 * role + 0) (sl.alloc + 2) with hm4_def
        simp only [↓reduceIte] at he4
        have hsl1_eq : sl1 = ⟨sl.alloc + 2, sl.root, nodes3⟩ := by
          dsimp only [sl1]; rw [hens]; unfold splitRootIfFull
          simp [hfull_rt, sp, leftIdx, rightIdx, newVals, newRootNd, nodes1, nodes2, nodes3]
        have hm4_eq : extractBTreeSlice L b role m4 = sl1 := by
          rw [hm4_def, he4, hm3_def, he3, hm2_def, he2, hm1_def, he1, hsl1_eq]
        obtain ⟨hsp_r, hsp_st, hsp_c⟩ := splitFullNodeAtProg_spec L (sl.nodes sl.root) s
        dsimp only at hsp_r hsp_st hsp_c
        have hpr_run :
            (Memory.spec 0).clientState s (prepareRootBoundedProg (L.toSliceCtx b role)) =
              ⟨m4, s.frontier⟩ ∧
            (Memory.spec 0).clientResult s (prepareRootBoundedProg (L.toSliceCtx b role)) =
              sl.root ∧
            memoryCost (prepareRootBoundedProg (L.toSliceCtx b role)) s ≤ 64 := by
          have hal_sub : leftIdx < L.nSlice - 1 := by dsimp only [leftIdx]; omega
          unfold prepareRootBoundedProg prepareNonEmptyRootProg execRootSplitProg
            computeRootSplitProg
          dsimp_slice_ctx; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_c]
          simp only [ha_nz, ↓reduceIte]
          rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', hrn_st, hrn_res]
          simp only [hsh_rt, hal_sub, ↓reduceIte, bind_assoc, pure_bind,
            prog_runClient_state_bind, prog_clientResult_bind, Realization.memoryCost_bind',
            StateTransitionSpec.clientState, runClient_state_splitFullNodeAtProg,
            hsp_r, hsp_c, leftIdx]
          unfold writeTwoNodesAtProg writeSliceNodeAtProg writeSliceHdrAtProg
          have hmk2 : mkNodeMeta false 1 = 2 := rfl
          simp only [hal0_ns, hal1_ns, hrt_ns, Nat.zero_lt_succ, ↓reduceIte, bind_assoc, pure_bind,
            prog_runClient_state_bind,
            Realization.memoryCost_bind', StateTransitionSpec.clientState,
            runClient_state_writePackedCompGenProg,
            memoryCost_writePackedCompGenProg, hm1_def, hm2_def, hm3_def, hm4_def,
            newRootNd, hmk2, prog_runClient_state_pure, prog_clientResult_pure, memoryCost_pure,
            leftIdx, rightIdx, sp, newVals]
          refine ⟨trivial, trivial, ?_⟩
          omega
        let cs1 : Fin 2 → BTreeTree := fun i => if i.val = 0 then leftT else rightT
        have hT1_ht : (BTreeTree.branch sl.root 1 cs1).height ≤ hMaxBTree := by
          dsimp only [BTreeTree.height]
          have hsup : univ.sup (fun i : Fin (1 + 1) => (cs1 i).height) ≤ T.height := by
            refine Finset.sup_le fun i _ => ?_
            dsimp only [cs1]
            split_ifs
            · exact hhtL
            · exact hhtR
          rw [Nat.add_comm]
          exact Nat.succ_le_of_lt (lt_of_le_of_lt hsup hht_lt)
        have hT1_raw : RawTreeValid L.wMeta L.fpBits L.wValLane L.tMin sl1.alloc sl1.nodes
            (.branch sl.root 1 cs1) := by
          rw [hsl1_eq]
          dsimp only [RawTreeValid, nodes3]
          rw [Function.update_self]
          refine ⟨by omega, rfl, by omega, hnrm, hnrk_1, hnrv_2, ?_, ?_, ?_, ?_⟩
          · intro j hj
            have hj0 : j = 0 := by omega
            subst hj0
            dsimp only [newRootNd]
            rw [laneGet_eq_div_mod, zero_mul, pow_zero, Nat.div_one,
              Nat.mod_eq_of_lt (hsep_fp.trans (Nat.pow_lt_pow_right Nat.one_lt_two (by omega)))]
            exact hsep_fp
          · intro i hmem
            dsimp only [cs1] at hmem
            split_ifs at hmem
            · rcases mem_insert.mp (hsubL hmem) with heq | her
              · exact hl_ne_rt heq.symm
              · exact (mem_erase.mp her).1 hrt.symm
            · rcases mem_insert.mp (hsubR hmem) with heq | her
              · exact hr_ne_rt heq.symm
              · exact (mem_erase.mp her).1 hrt.symm
          · intro i j hij
            fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
            · exact hdisjLR hlr_ne
            · exact (hdisjLR hlr_ne).symm
          · intro i; fin_cases i
            · dsimp only [cs1]; simp only [↓reduceIte]
              have hl0 : laneGet L.wValLane newVals 0 = leftIdx := by
                dsimp only [newVals]
                rw [laneGet_eq_div_mod, zero_mul, pow_zero, Nat.div_one, Nat.shiftLeft_eq,
                  Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl_val]
              exact ⟨hl0.trans hrtL.symm, hrawL⟩
            · dsimp only [cs1]; simp only [Nat.one_ne_zero, ↓reduceIte]
              have hl1 : laneGet L.wValLane newVals 1 = rightIdx := by
                dsimp only [newVals]
                rw [laneGet_eq_div_mod, one_mul, Nat.shiftLeft_eq,
                  Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hl_val,
                  zero_add, Nat.mod_eq_of_lt hr_val]
              exact ⟨hl1.trans hrtR.symm, hrawR⟩
        refine ⟨by rw [hpr_run.1], hpr_run.2.2, by rw [hpr_run.1]; exact hm4_eq,
          by rw [hpr_run.2.1, hsl1_eq],
          by rw [hsl1_eq, hns_eq]; dsimp only; omega,
          ⟨.branch sl.root 1 cs1, by simp [hsl1_eq, BTreeTree.rootIdx], hT1_ht,
            by rw [hsl1_eq]; dsimp only [nodes3]; rw [Function.update_self]; dsimp only [newRootNd]
               rw [metaCount_mkNodeMeta]; omega,
            hT1_raw⟩,
          fun b' r' hb' hr' hne => by
            rw [hpr_run.1]
            exact (ho4 b' r' hb' hr' hne).trans ((ho3 b' r' hb' hr' hne).trans
              ((ho2 b' r' hb' hr' hne).trans (ho1 b' r' hb' hr' hne))),
          fun slot hsl hne0 hne1 => by
            rw [hpr_run.1]
            exact (hb4 slot hsl (by omega)).trans ((hb3 slot hsl).trans
              ((hb2 slot hsl).trans (hb1 slot hsl))),
          fun addr ha => by
            rw [hpr_run.1]
            exact (ha4 addr ha).trans ((ha3 addr ha).trans ((ha2 addr ha).trans (ha1 addr ha)))⟩
      · have hsh_rt : (sl.nodes sl.root).metaWord >>> 1 ≠ 2 * L.tMin - 1 := by
          rw [hmc_sh]; exact hfull_rt
        have hsl1_eq : sl1 = sl := by
          dsimp only [sl1]; rw [hens]; unfold splitRootIfFull; simp [hfull_rt]
        have hpr_run :
            (Memory.spec 0).clientState s (prepareRootBoundedProg (L.toSliceCtx b role)) = s ∧
            (Memory.spec 0).clientResult s (prepareRootBoundedProg (L.toSliceCtx b role)) =
              sl.root ∧
            memoryCost (prepareRootBoundedProg (L.toSliceCtx b role)) s ≤ 64 := by
          unfold prepareRootBoundedProg prepareNonEmptyRootProg
          dsimp_slice_ctx; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', hhdr_st, hhdr_res, hhdr_c]
          simp only [ha_nz, ↓reduceIte]
          rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
            Realization.memoryCost_bind', hrn_st, hrn_res]
          simp only [hsh_rt, ↓reduceIte, memoryCost_pure]
          exact ⟨rfl, rfl, by omega⟩
        refine ⟨by rw [hpr_run.1], hpr_run.2.2, by rw [hpr_run.1, hsl1_eq],
          by rw [hpr_run.2.1, hsl1_eq],
          by rw [hsl1_eq, hns_eq]; omega,
          ⟨T, by rw [hsl1_eq]; exact hrt, hht_lt.le, by rw [hsl1_eq]; omega,
            by rw [hsl1_eq]; exact hraw⟩,
          fun _ _ _ _ _ => by rw [hpr_run.1],
          fun _ _ _ _ => by rw [hpr_run.1],
          fun _ _ => by rw [hpr_run.1]⟩
  obtain ⟨hfr1, hc1, hext1, hrt1, hal1_ns, ⟨T1, hT1_rt, hT1_ht, hT1_nf, hT1_raw⟩,
    ho1, hb1, ha1⟩ := hprep
  set s₁ := (Memory.spec 0).clientState s (prepareRootBoundedProg (L.toSliceCtx b role))
  have hvL₁ : L.Valid L.w s₁.frontier := by rwa [hfr1]
  obtain ⟨hfr2, hc2, hext2, hlf2, hal2_le, ⟨cnt_l, hraw_l, hcnt_l_lt⟩, ho2, hb2, ha2⟩ :=
    descendSplit_iter_spec hb hrole (hfp_eq ▸ hq) hMaxBTree s₁ hvL₁
      (by rw [hext1]; exact hT1_raw) (by rw [hext1, hT1_rt]; exact hT1_nf)
      hT1_ht (by rw [hext1]; exact hal1_ns)
  rw [hT1_rt] at hc2 hfr2 ho2 hb2 ha2
  rw [hext1, hT1_rt] at hext2 hlf2 hal2_le hraw_l
  set p_pure := descendSplitToLeaf L.fpBits L.wValLane L.tMin hMaxBTree sl1 sl1.root q
  set s₂ := (Memory.spec 0).clientState s₁
    (iterate descendSplitStepProg (L.toSliceCtx b role, q) hMaxBTree sl1.root)
  set leafIdx := p_pure.2
  obtain ⟨hlf_al, hmw_l, _, hmw_lt_l, hkw_l, hvw_l, hlanes_l⟩ := hraw_l
  have hlf_ns : leafIdx < L.nSlice := hlf_al.trans (lt_of_le_of_lt hal2_le hal1_ns)
  have hcnt_2t : cnt_l < 2 * L.tMin := by omega
  obtain ⟨hrank_eq, hrank_le⟩ := swarRankClampedProg_eq_swarRank hcnt_2t
    hvL.2.2.2.2.2.2.2.2.2.2.2.2.1 (hfp_eq ▸ hq) hkw_l hlanes_l s₂
  obtain ⟨hrn_res, hrn_st, hrn_c⟩ := readSliceNodeAtProg_spec L b role leafIdx s₂
  rw [hext2] at hrn_res
  dsimp only [BTreeEpochLayout.toNodeCtx] at hrn_res hrn_st hrn_c
  have hcnt_sh : (p_pure.1.nodes leafIdx).metaWord >>> 1 = cnt_l := by
    rw [Nat.shiftRight_eq_div_pow, pow_one, hmw_l]; exact metaCount_mkNodeMeta true cnt_l
  have hmc_eq : metaCount (p_pure.1.nodes leafIdx).metaWord = cnt_l := by
    rw [hmw_l, metaCount_mkNodeMeta]
  set r := swarRank L.fpBits (2 * L.tMin) cnt_l q (p_pure.1.nodes leafIdx).keysWord
  change _ = r at hrank_eq
  let leafNd' : BTreeNode :=
    if r < cnt_l && laneGet (L.fpBits + 2) (p_pure.1.nodes leafIdx).keysWord r == q then
      ⟨(p_pure.1.nodes leafIdx).metaWord, (p_pure.1.nodes leafIdx).keysWord,
        wordUpdateAt L.wValLane r val (p_pure.1.nodes leafIdx).valsWord⟩
    else
      ⟨mkNodeMeta true (cnt_l + 1),
        wordInsertAt (L.fpBits + 2) r q (p_pure.1.nodes leafIdx).keysWord,
        wordInsertAt L.wValLane r val (p_pure.1.nodes leafIdx).valsWord⟩
  have hnd'_fits : leafNd'.metaWord < 2 ^ L.wMeta ∧ leafNd'.keysWord < 2 ^ L.wKeys ∧
      leafNd'.valsWord < 2 ^ L.wVals := by
    dsimp only [leafNd']
    split_ifs with hhit
    · have hrc : r < cnt_l := (Bool.and_eq_true _ _).mp hhit |>.1 |> of_decide_eq_true
      refine ⟨hmw_lt_l, ?_, ?_⟩
      · rw [hvL.2.2.2.2.2.2.2.1]
        exact hkw_l.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      · rw [hvL.2.2.2.2.2.2.2.2.1]
        have hd_lt : wordDeleteAt L.wValLane r (p_pure.1.nodes leafIdx).valsWord <
            2 ^ ((cnt_l - 1) * L.wValLane) :=
          wordDeleteAt_lt (m := cnt_l - 1) (by omega)
            (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ cnt_l)] using hvw_l)
        have hu_eq : wordUpdateAt L.wValLane r val (p_pure.1.nodes leafIdx).valsWord =
            wordInsertAt L.wValLane r val
              (wordDeleteAt L.wValLane r (p_pure.1.nodes leafIdx).valsWord) := by
          rw [← clientResult_wordUpdateAtBoundedProg (s := s₂)]; simp [wordUpdateAtBoundedProg]
        have hu_lt : wordUpdateAt L.wValLane r val (p_pure.1.nodes leafIdx).valsWord <
            2 ^ (cnt_l * L.wValLane) := by
          rw [hu_eq]
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ cnt_l)] using
            wordInsertAt_lt (by omega) (hwv_eq ▸ hval) hd_lt
        exact hu_lt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
    · refine ⟨?_, ?_, ?_⟩
      · dsimp only [mkNodeMeta]; simp only [↓reduceIte]
        have := hvL.2.2.2.2.2.2.2.2.2.2.2.1; omega
      · rw [hvL.2.2.2.2.2.2.2.1]
        have hq_wk : q < 2 ^ (L.fpBits + 2) :=
          (hfp_eq ▸ hq).trans (Nat.pow_lt_pow_right Nat.one_lt_two (by omega))
        exact (wordInsertAt_lt hrank_le hq_wk hkw_l).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
      · rw [hvL.2.2.2.2.2.2.2.2.1]
        exact (wordInsertAt_lt hrank_le (hwv_eq ▸ hval) hvw_l).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  have hvL₂ : L.Valid L.w s₂.frontier := by rwa [hfr2, hfr1]
  obtain ⟨he3, ho3, hb3, ha3⟩ := extractBTreeSlice_writeNode (mem := s₂.mem) (u := leafIdx)
    (nd := leafNd') hvL₂ hb hrole hlf_ns hnd'_fits.1 hnd'_fits.2.1 hnd'_fits.2.2
  set idx := (3 * b + role) * L.nSlice + leafIdx
  set m_fin := writePacked (L.metaBase + L.offVals) L.wVals L.w
    (writePacked (L.metaBase + L.offKeys) L.wKeys L.w
      (writePacked (L.metaBase + L.offMeta) L.wMeta L.w s₂.mem idx leafNd'.metaWord)
      idx leafNd'.keysWord) idx leafNd'.valsWord
  have hfin_run :
      (Memory.spec 0).clientState s₂
        (finishLeafInsertBoundedProg (L.toSliceCtx b role, (leafIdx, (q, val)))) =
        ⟨m_fin, s₂.frontier⟩ ∧
      memoryCost (finishLeafInsertBoundedProg (L.toSliceCtx b role, (leafIdx, (q, val)))) s₂ ≤
        32 := by
    unfold finishLeafInsertBoundedProg computeLeafInsertNodeProg
      leafInsertHitOrShiftProg leafInsertShiftProg
    dsimp_slice_ctx; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hrn_st, hrn_res]
    simp only [bind_assoc, hcnt_sh, prog_runClient_state_bind,
      Realization.memoryCost_bind', StateTransitionSpec.clientState,
      runClient_state_swarRankClampedProg, hrank_eq, memoryCost_swarRankClampedProg,
      runClient_state_laneGetBoundedProg, clientResult_laneGetBoundedProg,
      memoryCost_laneGetBoundedProg]
    have hmk_t : 1 + 2 * (cnt_l + 1) = mkNodeMeta true (cnt_l + 1) := rfl
    by_cases hrc : r < cnt_l
    · by_cases hkq : laneGet (L.fpBits + 2) (p_pure.1.nodes leafIdx).keysWord r = q
      · have hh : (r < cnt_l && laneGet (L.fpBits + 2) (p_pure.1.nodes leafIdx).keysWord r == q) =
            true := by simp [hrc, hkq]
        simp only [hrc, hkq, ↓reduceIte,
          prog_runClient_state_bind, prog_clientResult_bind, Realization.memoryCost_bind',
          StateTransitionSpec.clientState,
          runClient_state_wordUpdateAtBoundedProg, clientResult_wordUpdateAtBoundedProg,
          memoryCost_wordUpdateAtBoundedProg,
          prog_runClient_state_pure, prog_clientResult_pure, memoryCost_pure]
        unfold writeSliceNodeAtProg
        simp only [hlf_ns, ↓reduceIte, pure_bind,
          prog_runClient_state_bind, Realization.memoryCost_bind', StateTransitionSpec.clientState,
          runClient_state_writePackedCompGenProg, memoryCost_writePackedCompGenProg,
          idx, m_fin, leafNd', hh]
        exact ⟨trivial, by omega⟩
      · have hbeq : (laneGet (L.fpBits + 2) (p_pure.1.nodes leafIdx).keysWord r == q) = false :=
          beq_eq_false_iff_ne.mpr hkq
        have hh : (r < cnt_l && laneGet (L.fpBits + 2) (p_pure.1.nodes leafIdx).keysWord r == q) =
            false := by simp [hrc, hbeq]
        simp only [hrc, hkq, ↓reduceIte,
          prog_runClient_state_bind, prog_clientResult_bind, Realization.memoryCost_bind',
          StateTransitionSpec.clientState,
          runClient_state_wordInsertAtBoundedProg, clientResult_wordInsertAtBoundedProg,
          memoryCost_wordInsertAtBoundedProg, hmk_t,
          prog_runClient_state_pure, prog_clientResult_pure, memoryCost_pure]
        unfold writeSliceNodeAtProg
        simp only [hlf_ns, ↓reduceIte, pure_bind,
          prog_runClient_state_bind, Realization.memoryCost_bind', StateTransitionSpec.clientState,
          runClient_state_writePackedCompGenProg, memoryCost_writePackedCompGenProg,
          idx, m_fin, leafNd', hh]
        exact ⟨rfl, by omega⟩
    · have hh : (r < cnt_l && laneGet (L.fpBits + 2) (p_pure.1.nodes leafIdx).keysWord r == q) =
          false := by simp [hrc]
      simp only [hrc, ↓reduceIte,
        prog_runClient_state_bind, prog_clientResult_bind, Realization.memoryCost_bind',
        StateTransitionSpec.clientState,
        runClient_state_wordInsertAtBoundedProg, clientResult_wordInsertAtBoundedProg,
        memoryCost_wordInsertAtBoundedProg, hmk_t,
        prog_runClient_state_pure, prog_clientResult_pure, memoryCost_pure]
      unfold writeSliceNodeAtProg
      simp only [hlf_ns, ↓reduceIte, pure_bind,
        prog_runClient_state_bind, Realization.memoryCost_bind', StateTransitionSpec.clientState,
        runClient_state_writePackedCompGenProg, memoryCost_writePackedCompGenProg,
        idx, m_fin, leafNd', hh]
      exact ⟨rfl, by omega⟩
  have hext_fin : extractBTreeSlice L b role m_fin =
      btreeInsert (fpBitsWhp N) (valLaneBitsWhp N) (tMinWhp N) sl q val := by
    rw [he3, hext2]
    unfold btreeInsert finishLeafInsert
    rw [← hfp_eq, ← hwv_eq, ← htm_eq]
    dsimp only [sl1, p_pure, leafIdx, r, leafNd']
    rw [hmc_eq]
    split_ifs <;> rfl
  have hst_tot : (Memory.spec 0).clientState s
      (btreeInsertBoundedProg (L.toSliceCtx b role, (q, val))) = ⟨m_fin, s₂.frontier⟩ := by
    unfold btreeInsertBoundedProg descendSplitLoopProg
    rw [StateTransitionSpec.clientState_bind, hrt1,
      StateTransitionSpec.clientState_bind, hlf2]
    exact hfin_run.1
  have hc_tot : memoryCost (btreeInsertBoundedProg (L.toSliceCtx b role, (q, val))) s ≤
      72 * hMaxBTree + 96 := by
    unfold btreeInsertBoundedProg descendSplitLoopProg
    rw [Realization.memoryCost_bind', hrt1, Realization.memoryCost_bind', hlf2]
    change memoryCost (prepareRootBoundedProg (L.toSliceCtx b role)) s +
      (memoryCost (iterate descendSplitStepProg (L.toSliceCtx b role, q) hMaxBTree sl1.root) s₁ +
        memoryCost (finishLeafInsertBoundedProg (L.toSliceCtx b role, (leafIdx, (q, val)))) s₂) ≤ _
    have := hfin_run.2
    omega
  obtain ⟨hal_spec, hv_spec⟩ := hv.insert_spec hth hins hq hval
  dsimp only
  rw [hst_tot]
  refine ⟨hfr2.trans hfr1, hc_tot, hext_fin,
    by rw [hext_fin]; exact hal_spec, by rw [hext_fin]; exact hv_spec,
    fun b' r' hb' hr' hne => (ho3 b' r' hb' hr' hne).trans
      ((ho2 b' r' hb' hr' hne).trans (ho1 b' r' hb' hr' hne)),
    fun slot hsl hne0 hne1 => (hb3 slot hsl).trans
      ((hb2 slot hsl hne0).trans (hb1 slot hsl hne0 hne1)),
    fun addr ha => (ha3 addr ha).trans ((ha2 addr ha).trans (ha1 addr ha))⟩

/-! ## Section 5: Unconditional Read-State and Frame Preservation Lemmas -/

@[simp] theorem runClient_state_btreeLookupBoundedProg (x : BTreeSliceCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (btreeLookupBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩,
    ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩⟩, q⟩
  unfold btreeLookupBoundedProg btreeLookupNonEmptyProg btreeLookupLeafProg
    btreeLookupRankProg btreeLookupHitProg
  simp only [pure_bind, prog_runClient_state_bind, runClient_state_readSliceHdrAtProg]
  split_ifs
  · rfl
  · simp only [prog_runClient_state_bind, runClient_state_descendLoopProg,
      runClient_state_readSliceNodeAtProg, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg]
    repeat (split_ifs <;> simp)

theorem clientState_btreeLookupBoundedProg (x : BTreeSliceCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (btreeLookupBoundedProg x) = s :=
  runClient_state_btreeLookupBoundedProg x s

private theorem writeSliceNodeAtProg_outside {L : BTreeEpochLayout} {b role u : ℕ}
    {nd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hw : 0 < L.w) (hb : b < L.numBuckets) (hrole : role < 3) :
    ∀ addr, ¬L.OwnsAddr addr →
      ((Memory.spec 0).clientState s
        (writeSliceNodeAtProg ((L.toNodeCtx b role, u), nd))).mem addr = s.mem addr := by
  rcases nd with ⟨mw, ⟨kw, vw⟩⟩
  intro addr ha
  unfold writeSliceNodeAtProg; dsimp only [BTreeEpochLayout.toNodeCtx]
  by_cases hu : u < L.nSlice
  · have htot : (3 * b + role) * L.nSlice + u < L.totalNodes := by
      unfold BTreeEpochLayout.totalNodes
      calc (3 * b + role) * L.nSlice + u
          < (3 * b + role + 1) * L.nSlice := by ring_nf; omega
        _ ≤ (3 * L.numBuckets) * L.nSlice := Nat.mul_le_mul_right _ (by omega)
    simp only [hu, ↓reduceIte, pure_bind, StateTransitionSpec.clientState,
      prog_runClient_state_bind, runClient_state_writePackedCompGenProg]
    rw [writePacked_outside hw _ htot _ (fun h => ha (Or.inr (Or.inr (Or.inr h))))]
    rw [writePacked_outside hw _ htot _ (fun h => ha (Or.inr (Or.inr (Or.inl h))))]
    exact writePacked_outside hw _ htot _ (fun h => ha (Or.inr (Or.inl h)))
  · simp [hu]

private theorem writeTwoNodesAtProg_outside {L : BTreeEpochLayout} {b role : ℕ}
    {nds : (ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))} {s : Memory.State}
    (hw : 0 < L.w) (hb : b < L.numBuckets) (hrole : role < 3) :
    ∀ addr, ¬L.OwnsAddr addr →
      ((Memory.spec 0).clientState s
        (writeTwoNodesAtProg (L.toNodeCtx b role, nds))).mem addr = s.mem addr := by
  rcases nds with ⟨⟨u1, nd1⟩, ⟨u2, nd2⟩⟩
  intro addr ha; unfold writeTwoNodesAtProg; rw [StateTransitionSpec.clientState_bind]
  exact (writeSliceNodeAtProg_outside hw hb hrole addr ha).trans
    (writeSliceNodeAtProg_outside hw hb hrole addr ha)

private theorem writeSliceHdrAtProg_outside {L : BTreeEpochLayout} {b role : ℕ}
    {iv : ℕ × ℕ} {s : Memory.State}
    (hw : 0 < L.w) (hb : b < L.numBuckets) (hrole : role < 3) :
    ∀ addr, ¬L.OwnsAddr addr →
      ((Memory.spec 0).clientState s
        (writeSliceHdrAtProg (L.toHdrCtx b role, iv))).mem addr = s.mem addr := by
  rcases iv with ⟨isRoot, val⟩
  intro addr ha
  unfold writeSliceHdrAtProg; dsimp only [BTreeEpochLayout.toHdrCtx]
  by_cases hi : isRoot < 2
  · have hsl : 16 * b + 6 + 2 * role + isRoot < 16 * L.numBuckets := by omega
    simp only [hi, ↓reduceIte, pure_bind, StateTransitionSpec.clientState,
      runClient_state_writePackedCompGenProg]
    exact writePacked_outside hw _ hsl _ (fun h => ha (Or.inl h))
  · simp [hi]

theorem btreeDeleteBoundedProg_frame {L : BTreeEpochLayout} {b role : ℕ}
    (hw : 0 < L.w) (hb : b < L.numBuckets) (hrole : role < 3) (q : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s (btreeDeleteBoundedProg (L.toSliceCtx b role, q))
    s'.frontier = s.frontier ∧ ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
  dsimp only
  unfold btreeDeleteBoundedProg btreeDeleteNonEmptyProg btreeDeleteLeafProg
    btreeDeleteRankProg btreeDeleteHitProg
  dsimp_slice_ctx
  simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_bind,
    runClient_state_readSliceHdrAtProg]
  split_ifs
  · exact ⟨rfl, fun _ _ => rfl⟩
  · simp only [prog_runClient_state_bind, runClient_state_descendLoopProg,
      runClient_state_readSliceNodeAtProg, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg]
    split_ifs
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_wordDeleteAtBoundedProg]
      exact ⟨runClient_frontier_writeSliceNodeAtProg _ s,
        fun addr ha => writeSliceNodeAtProg_outside hw hb hrole addr ha⟩
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_pure]
      exact ⟨trivial, fun _ _ => trivial⟩
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_pure]
      exact ⟨trivial, fun _ _ => trivial⟩

theorem btreeUpdateBoundedProg_frame {L : BTreeEpochLayout} {b role : ℕ}
    (hw : 0 < L.w) (hb : b < L.numBuckets) (hrole : role < 3) (q newVal : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (btreeUpdateBoundedProg (L.toSliceCtx b role, (q, newVal)))
    s'.frontier = s.frontier ∧ ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
  dsimp only
  unfold btreeUpdateBoundedProg btreeUpdateNonEmptyProg btreeUpdateLeafProg
    btreeUpdateRankProg btreeUpdateHitProg
  dsimp_slice_ctx
  simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_bind,
    runClient_state_readSliceHdrAtProg]
  split_ifs
  · exact ⟨rfl, fun _ _ => rfl⟩
  · simp only [prog_runClient_state_bind, runClient_state_descendLoopProg,
      runClient_state_readSliceNodeAtProg, runClient_state_swarRankClampedProg,
      runClient_state_laneGetBoundedProg]
    split_ifs
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_wordUpdateAtBoundedProg]
      exact ⟨runClient_frontier_writeSliceNodeAtProg _ s,
        fun addr ha => writeSliceNodeAtProg_outside hw hb hrole addr ha⟩
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_pure]
      exact ⟨trivial, fun _ _ => trivial⟩
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_pure]
      exact ⟨trivial, fun _ _ => trivial⟩

theorem btreeInsertBoundedProg_frame {L : BTreeEpochLayout} {b role : ℕ}
    (hw : 0 < L.w) (hb : b < L.numBuckets) (hrole : role < 3) (q val : ℕ) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (btreeInsertBoundedProg (L.toSliceCtx b role, (q, val)))
    s'.frontier = s.frontier ∧ ∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr := by
  set s₁ := (Memory.spec 0).clientState s (prepareRootBoundedProg (L.toSliceCtx b role))
  have hprep : s₁.frontier = s.frontier ∧ ∀ addr, ¬L.OwnsAddr addr → s₁.mem addr = s.mem addr := by
    dsimp only [s₁]
    refine ⟨runClient_frontier_prepareRoot _ s, fun addr ha => ?_⟩
    unfold prepareRootBoundedProg prepareNonEmptyRootProg execRootSplitProg initEmptyRootAtProg
    dsimp_slice_ctx
    simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_bind,
      runClient_state_readSliceHdrAtProg]
    split_ifs
    · simp only [prog_runClient_state_bind, prog_runClient_state_pure]
      exact (writeSliceHdrAtProg_outside hw hb hrole addr ha).trans
        ((writeSliceHdrAtProg_outside hw hb hrole addr ha).trans
          (writeSliceNodeAtProg_outside hw hb hrole addr ha))
    · simp only [prog_runClient_state_bind, runClient_state_readSliceNodeAtProg]
      split_ifs
      · simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
          runClient_state_computeRootSplitProg, prog_runClient_state_pure]
        exact (writeSliceHdrAtProg_outside hw hb hrole addr ha).trans
          ((writeSliceNodeAtProg_outside hw hb hrole addr ha).trans
            (writeTwoNodesAtProg_outside hw hb hrole addr ha))
      · simp only [StateTransitionSpec.clientState, prog_runClient_state_pure]
    · simp only [prog_runClient_state_bind, StateTransitionSpec.clientState,
        runClient_state_readSliceNodeAtProg]
      split_ifs <;> rfl
  have hstep : ∀ cur (s₀ : Memory.State),
      let s₁ := (Memory.spec 0).clientState s₀
        (descendSplitStepProg ((L.toSliceCtx b role, q), cur))
      s₁.frontier = s₀.frontier ∧ ∀ addr, ¬L.OwnsAddr addr → s₁.mem addr = s₀.mem addr := by
    intro cur s₀; dsimp only
    refine ⟨frontier_descendSplitStep _ s₀, fun addr ha => ?_⟩
    unfold descendSplitStepProg descendSplitBranchProg splitChildAndStepProg
      splitChildBodyProg finishChildSplitWritesProg
    dsimp_slice_ctx
    simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_bind,
      runClient_state_readSliceNodeAtProg]
    split_ifs
    · rfl
    · simp only [prog_runClient_state_bind, runClient_state_swarRankClampedProg,
        runClient_state_laneGetBoundedProg, runClient_state_readSliceNodeAtProg]
      split_ifs
      · simp only [prog_runClient_state_bind, runClient_state_readSliceHdrAtProg]
        split_ifs
        · simp only [prog_runClient_state_bind, runClient_state_readSliceNodeAtProg,
            runClient_state_computeChildSplitProg]
          split_ifs <;> simp only [prog_runClient_state_pure] <;>
            exact (writeSliceHdrAtProg_outside hw hb hrole addr ha).trans
              ((writeSliceNodeAtProg_outside hw hb hrole addr ha).trans
                (writeTwoNodesAtProg_outside hw hb hrole addr ha))
        · rfl
      · rfl
  have hloop : ∀ m cur (s₀ : Memory.State),
      let s₁ := (Memory.spec 0).clientState s₀
        (iterate descendSplitStepProg (L.toSliceCtx b role, q) m cur)
      s₁.frontier = s₀.frontier ∧ ∀ addr, ¬L.OwnsAddr addr → s₁.mem addr = s₀.mem addr := by
    intro m; induction m with
    | zero => intro _ _; exact ⟨rfl, fun _ _ => rfl⟩
    | succ m ih =>
      intro cur s₀
      obtain ⟨hfr1, ho1⟩ := hstep cur s₀
      obtain ⟨hfrm, hom⟩ := ih _ _
      unfold iterate; rw [StateTransitionSpec.clientState_bind]
      exact ⟨hfrm.trans hfr1, fun addr ha => (hom addr ha).trans (ho1 addr ha)⟩
  dsimp only
  unfold btreeInsertBoundedProg descendSplitLoopProg
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  obtain ⟨hfr1, ho1⟩ := hprep
  set rt := (Memory.spec 0).clientResult s (prepareRootBoundedProg (L.toSliceCtx b role))
  obtain ⟨hfr2, ho2⟩ := hloop hMaxBTree rt s₁
  set s₂ := (Memory.spec 0).clientState s₁
    (iterate descendSplitStepProg (L.toSliceCtx b role, q) hMaxBTree rt)
  set leafIdx := (Memory.spec 0).clientResult s₁
    (iterate descendSplitStepProg (L.toSliceCtx b role, q) hMaxBTree rt)
  set s₃ := (Memory.spec 0).clientState s₂
    (finishLeafInsertBoundedProg (L.toSliceCtx b role, (leafIdx, (q, val))))
  have hfin : s₃.frontier = s₂.frontier ∧ ∀ addr, ¬L.OwnsAddr addr → s₃.mem addr = s₂.mem addr := by
    dsimp only [s₃]; unfold finishLeafInsertBoundedProg; dsimp_slice_ctx
    simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_bind,
      runClient_state_readSliceNodeAtProg, runClient_state_computeLeafInsertNodeProg]
    exact ⟨runClient_frontier_writeSliceNodeAtProg _ s₂,
      fun addr ha => writeSliceNodeAtProg_outside hw hb hrole addr ha⟩
  exact ⟨hfin.1.trans (hfr2.trans hfr1),
    fun addr ha => (hfin.2 addr ha).trans ((ho2 addr ha).trans (ho1 addr ha))⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolOps
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SplitPairProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bit-Packed `Memory.Prog` Realization of `BlockPoolState` Metadata (`LargeBlockPoolMetaProg`)

This module couples the pure deamortized `M`-bucket `BlockPoolState`
(`LargeBlockPoolState`, `LargeBlockPoolBalanced`, `LargeBlockPoolOps`) to bit-packed Word-RAM
memory inside a large epoch's metadata region (`offBktMeta` slots `0..4`, `offSlabDir`,
`offTailDir`, `offSlabOwner`, `offTailOwner`, and header scalars `+1`, `+10..16`), certifies
parameter-free (`¬ReadsWidth`) `RealizesBounded .exact` implementations for low-level table
accessors and `(toPhys, ownerOf)` lookups, and proves exact `extractBlockPool` field-update
refinement together with frame preservation (`BpMetaProg`) outside `BpMetaLayout.OwnsMetaAddr`
and on `offBktMeta` slots `5..15`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.BpMetaLayout`,
  `epochBpMetaLayout`, `extractBlockPool`, `BpMetaProg`.
* `bpInitZeroedProg`, `bpReadBktCountProg`, `bpToPhysProg`, `bpOwnerOfProg`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]
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

/-! ## Section 1: `BpMetaLayout`, `extractBlockPool`, and `BpMetaProg` Frame Calculus -/

private theorem BlockPoolState.ext_fields {a b : BlockPoolState}
    (hM : a.M = b.M) (hK : a.K = b.K) (hms : a.maxSlabs = b.maxSlabs)
    (hns : a.nSide = b.nSide)
    (hq : ∀ x, a.q x = b.q x) (hr : ∀ x, a.r x = b.r x) (hhd : ∀ x, a.head x = b.head x)
    (hac : ∀ x, a.actCode x = b.actCode x) (hab : ∀ x, a.actBlk x = b.actBlk x)
    (hsl : ∀ x y, a.slabOf x y = b.slabOf x y) (htr : ∀ x y, a.tailRing x y = b.tailRing x y)
    (hbt : ∀ x, a.blkTag x = b.blkTag x) (hbm1 : ∀ x, a.blkMeta1 x = b.blkMeta1 x)
    (hbm2 : ∀ x, a.blkMeta2 x = b.blkMeta2 x)
    (hul : a.unresLen = b.unresLen) (hus : ∀ x, a.unresStack x = b.unresStack x)
    (hthw : a.tbHighWater = b.tbHighWater) (hftt : a.freeTbTop = b.freeTbTop)
    (hfts : ∀ x, a.freeTbStack x = b.freeTbStack x)
    (htpb : ∀ x, a.tbPhysBlk x = b.tbPhysBlk x)
    (htob : ∀ x, a.tailOwnerBkt x = b.tailOwnerBkt x)
    (htor : ∀ x, a.tailOwnerRing x = b.tailOwnerRing x)
    (htsa : a.topSwapAct = b.topSwapAct) (htss : a.topSwapSrc = b.topSwapSrc)
    (htsd : a.topSwapDst = b.topSwapDst) (htsc : a.topSwapCur = b.topSwapCur) :
    a = b := by
  cases a; cases b; dsimp only at *
  subst hM hK hms hns hul hthw hftt htsa htss htsd htsc
  congr <;> [ext x; ext x; ext x; ext x; ext x; ext x y; ext x y; ext x; ext x; ext x;
    ext x; ext x; ext x; ext x; ext x] <;> apply_assumption

/-- Named memory layout descriptor for the metadata tables of a `BlockPoolState` (`0` projection
chains, independent of `SlotIoLayout`). -/
structure BpMetaLayout where
  /-- Base word address of the enclosing epoch metadata region. -/
  metaBase : ℕ
  /-- Word offset of the `16 * M`-entry per-bucket scalar table (`slots 0..4` owned here). -/
  offBktMeta : ℕ
  /-- Word offset of the `M * maxSlabs`-entry per-bucket slab directory. -/
  offSlabDir : ℕ
  /-- Word offset of the `8 * M * K`-entry tail ring & free-tb / tb-phys directory. -/
  offTailDir : ℕ
  /-- Word offset of the `4 * maxBlocks`-entry physical block owner/unres directory. -/
  offSlabOwner : ℕ
  /-- Word offset of the `16 * maxTail`-entry global tail-owner directory. -/
  offTailOwner : ℕ
  /-- Bit-width `globalPtrBits N` of each packed pointer entry. -/
  ptrB : ℕ
  /-- Machine word bit-width `w`. -/
  w : ℕ
  /-- Number of buckets `numBucketsWhp N`. -/
  M : ℕ
  /-- Full-slab item count `slabSizeWhp N = L ^ 2`. -/
  K : ℕ
  /-- Per-bucket full-slab capacity `maxSlabsPerBktWhp N = 4 * L ^ 10`. -/
  maxSlabs : ℕ
  /-- Physical block directory capacity `N / K + 4`. -/
  maxBlocks : ℕ
  /-- Tail-owner directory sizing unit `maxTailWhp N = M * K + 4`. -/
  maxTail : ℕ
  /-- Upper item capacity `N` (`nSide ≤ nCap < 2 ^ ptrB`). -/
  nCap : ℕ

/-- Concrete `BpMetaLayout` for a large epoch `(c, w, N)` at `metaBase`. -/
@[expose] def epochBpMetaLayout (c w N metaBase : ℕ) : BpMetaLayout where
  metaBase := metaBase
  offBktMeta := offBktMeta c w N
  offSlabDir := offSlabDir c w N
  offTailDir := offTailDir c w N
  offSlabOwner := offSlabOwner c w N
  offTailOwner := offTailOwner c w N
  ptrB := globalPtrBits N
  w := w
  M := numBucketsWhp N
  K := slabSizeWhp N
  maxSlabs := maxSlabsPerBktWhp N
  maxBlocks := N / slabSizeWhp N + 4
  maxTail := maxTailWhp N
  nCap := N

/-- Register-tuple encoding of `BpMetaLayout` for `RealizesBounded` primitives. -/
abbrev BpMetaCtx :=
  (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) × (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ))

/-- Pack `BpMetaLayout` into `BpMetaCtx`. -/
@[expose] def BpMetaLayout.toCtx (mp : BpMetaLayout) : BpMetaCtx :=
  ((((mp.metaBase, mp.offBktMeta), (mp.offSlabDir, mp.offTailDir)),
    ((mp.offSlabOwner, mp.offTailOwner), (mp.ptrB, mp.w))),
   (((mp.M, mp.K), (mp.maxSlabs, mp.maxBlocks)), (mp.maxTail, mp.nCap)))

/-- Unpack `BpMetaCtx` into `BpMetaLayout`. -/
@[expose] def BpMetaLayout.ofCtx : BpMetaCtx → BpMetaLayout
  | ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))), (((m, k), (ms, mbk)), (mt, nc))) =>
    ⟨mb, obm, osd, otd, oso, oto, pb, wv, m, k, ms, mbk, mt, nc⟩

@[simp] theorem BpMetaLayout.ofCtx_toCtx (mp : BpMetaLayout) :
    BpMetaLayout.ofCtx mp.toCtx = mp := by
  cases mp; rfl

@[simp] theorem BpMetaLayout.toCtx_ofCtx (ctx : BpMetaCtx) :
    (BpMetaLayout.ofCtx ctx).toCtx = ctx := by
  rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩; rfl

theorem BpMetaLayout.fold_toCtx (mp : BpMetaLayout) :
    ((((mp.metaBase, mp.offBktMeta), (mp.offSlabDir, mp.offTailDir)),
      ((mp.offSlabOwner, mp.offTailOwner), (mp.ptrB, mp.w))),
     (((mp.M, mp.K), (mp.maxSlabs, mp.maxBlocks)), (mp.maxTail, mp.nCap))) = mp.toCtx :=
  rfl

/-- Word-address footprint owned by `BpMetaLayout` (scalars `+1` and `+10..16`, plus the five
packed block-pool tables). -/
@[expose] def BpMetaLayout.OwnsMetaAddr (mp : BpMetaLayout) (addr : ℕ) : Prop :=
  addr = mp.metaBase + 1 ∨
  (mp.metaBase + 10 ≤ addr ∧ addr < mp.metaBase + 17) ∨
  (mp.metaBase + mp.offBktMeta ≤ addr ∧
    addr < mp.metaBase + mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w) ∨
  (mp.metaBase + mp.offSlabDir ≤ addr ∧
    addr < mp.metaBase + mp.offSlabDir + packedWords (mp.M * mp.maxSlabs) mp.ptrB mp.w) ∨
  (mp.metaBase + mp.offTailDir ≤ addr ∧
    addr < mp.metaBase + mp.offTailDir + packedWords (8 * mp.M * mp.K) mp.ptrB mp.w) ∨
  (mp.metaBase + mp.offSlabOwner ≤ addr ∧
    addr < mp.metaBase + mp.offSlabOwner + packedWords (4 * mp.maxBlocks) mp.ptrB mp.w) ∨
  (mp.metaBase + mp.offTailOwner ≤ addr ∧
    addr < mp.metaBase + mp.offTailOwner + packedWords (16 * mp.maxTail) mp.ptrB mp.w)

/-- Frontier-only static validity structure for `BpMetaLayout` (independent of `s.mem`, named
fields, `0` projection chains). -/
structure BpMetaLayout.Valid (mp : BpMetaLayout) (w_mach frontier : ℕ) : Prop where
  w_mach_pos : 0 < w_mach
  w_eq : w_mach = mp.w
  ptrB_le : mp.ptrB ≤ w_mach
  M_ge : 2 ≤ mp.M
  K_ge : 64 ≤ mp.K
  maxBlocks_ge : 4 ≤ mp.maxBlocks
  nCap_lt_ptrB : mp.nCap < 2 ^ mp.ptrB
  sixteen_M_le : 16 * mp.M ≤ mp.nCap
  M_maxSlabs_le : mp.M * mp.maxSlabs ≤ mp.nCap
  maxSlabs_K_le : mp.maxSlabs * mp.K + 6 * mp.K ≤ mp.nCap
  eight_MK_le : 8 * mp.M * mp.K ≤ mp.nCap
  twelve_K_le : 12 * mp.K ≤ mp.nCap
  four_maxBlocks_le : 4 * mp.maxBlocks ≤ mp.nCap
  div_K_add_two_le : mp.nCap / mp.K + 2 ≤ mp.maxBlocks
  sixteen_MK_le_maxTail : 16 * mp.M * mp.K ≤ 16 * mp.maxTail
  sixteen_maxTail_le : 16 * mp.maxTail ≤ mp.nCap
  offBktMeta_ge : 32 ≤ mp.offBktMeta
  offSlabDir_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offSlabDir
  offTailDir_ge : mp.offSlabDir + packedWords (mp.M * mp.maxSlabs) mp.ptrB mp.w ≤ mp.offTailDir
  offSlabOwner_ge : mp.offTailDir + packedWords (8 * mp.M * mp.K) mp.ptrB mp.w ≤ mp.offSlabOwner
  offTailOwner_ge : mp.offSlabOwner + packedWords (4 * mp.maxBlocks) mp.ptrB mp.w ≤ mp.offTailOwner
  frontier_ge :
    mp.metaBase + mp.offTailOwner + packedWords (16 * mp.maxTail) mp.ptrB mp.w ≤ frontier

theorem BpMetaLayout.Valid.w_pos {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) :
    0 < mp.w :=
  hv.w_eq ▸ hv.w_mach_pos

theorem BpMetaLayout.Valid.nCap_lt_two_pow_w {mp : BpMetaLayout} {w fr : ℕ}
    (hv : mp.Valid w fr) : mp.nCap < 2 ^ w :=
  lt_of_lt_of_le hv.nCap_lt_ptrB (Nat.pow_le_pow_right (by decide) hv.ptrB_le)

/-- `epochBpMetaLayout c w N metaBase` satisfies `BpMetaLayout.Valid` whenever
`whpThreshold c ≤ N ≤ U`, `Fits w U`, and `metaBase + epochMetaWordsWhp c w N ≤ frontier`. -/
theorem valid_epochBpMetaLayout {c U w N metaBase frontier : ℕ}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hfr : metaBase + epochMetaWordsWhp c w N ≤ frontier) :
    (epochBpMetaLayout c w N metaBase).Valid w frontier := by
  obtain ⟨hptr_lt, hptr_w, hlog_w, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmb4, h8MK,
    h16mt⟩ := largeEpoch_param_bounds hth hNU hU
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hL2 := two_le_slabScale N
  have hbmin := le_bMinWhp c
  have hbm := bMinWhp_le_log hth
  have hlog_ge : 6553600 ≤ Nat.log 2 N := hbmin.trans hbm
  have h320 : 320 * Dynamic.logLogFactor N ≤ bCharWhp N :=
    (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
  have hbw_ge4 : 4 ≤ bWhp N := by
    have hlt_pow : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
    have hcl_le : Nat.clog 2 N ≤ Nat.log 2 N + 1 :=
      (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hlt_pow.le
    unfold bCharWhp at h320
    unfold bWhp
    omega
  have hM16 : 16 ≤ numBucketsWhp N := by
    unfold numBucketsWhp
    calc 16 = 2 ^ 4 := by decide
      _ ≤ 2 ^ bWhp N := Nat.pow_le_pow_right (by decide) hbw_ge4
  have hK64 : 64 ≤ slabSizeWhp N := by
    have hll_ge3 : 3 ≤ Dynamic.logLogFactor N := by
      unfold Dynamic.logLogFactor
      have hn4 : 4 ≤ N := four_le_of_whpThreshold_le hth
      rw [max_eq_left hn4]
      have hcl_ge : 6553600 ≤ Nat.clog 2 N := hlog_ge.trans (Nat.log_le_clog 2 N)
      have hlt_cl : 2 ^ 2 < Nat.clog 2 N := by omega
      have h2 : 2 < Nat.clog 2 (Nat.clog 2 N) :=
        (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr hlt_cl
      omega
    unfold slabSizeWhp slabScale
    calc 64 = (2 ^ 3) ^ 2 := by decide
      _ ≤ (2 ^ Dynamic.logLogFactor N) ^ 2 :=
        Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hll_ge3) 2
  have hL10_pos : 1 ≤ slabScale N ^ 10 := Nat.one_le_pow 10 _ (by omega)
  have hK_le_L12 : slabSizeWhp N ≤ slabScale N ^ 12 := by
    unfold slabSizeWhp
    calc slabScale N ^ 2 ≤ slabScale N ^ 2 * slabScale N ^ 10 :=
          Nat.le_mul_of_pos_right _ hL10_pos
      _ = slabScale N ^ (2 + 10) := (pow_add (slabScale N) 2 10).symm
  have h16_L12 : 16 ≤ slabScale N ^ 12 :=
    le_trans (by decide : 16 ≤ 2 ^ 12) (Nat.pow_le_pow_left hL2 12)
  have h16M : 16 * numBucketsWhp N ≤ N := by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left _ h16_L12).trans hML12
  have hMms : numBucketsWhp N * maxSlabsPerBktWhp N ≤ N := by
    unfold maxSlabsPerBktWhp
    have h4L2 : 4 ≤ slabScale N ^ 2 :=
      le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_left hL2 2)
    calc numBucketsWhp N * (4 * slabScale N ^ 10)
        ≤ numBucketsWhp N * (slabScale N ^ 2 * slabScale N ^ 10) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4L2)
      _ = numBucketsWhp N * slabScale N ^ (2 + 10) := by rw [← pow_add]
      _ ≤ N := hML12
  have hmsK : maxSlabsPerBktWhp N * slabSizeWhp N + 6 * slabSizeWhp N ≤ N := by
    have h1 : maxSlabsPerBktWhp N * slabSizeWhp N = 4 * slabScale N ^ 12 := by
      unfold maxSlabsPerBktWhp slabSizeWhp
      rw [Nat.mul_assoc, ← pow_add, show 10 + 2 = 12 from rfl]
    have h2 : 6 * slabSizeWhp N ≤ 6 * slabScale N ^ 12 := Nat.mul_le_mul_left 6 hK_le_L12
    have h3 : 10 * slabScale N ^ 12 ≤ numBucketsWhp N * slabScale N ^ 12 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h12K : 12 * slabSizeWhp N ≤ N :=
    (Nat.mul_le_mul_left 12 hK_le_L12).trans
      ((Nat.mul_le_mul_right _ (by omega : 12 ≤ numBucketsWhp N)).trans hML12)
  have hoff32 : 32 ≤ offBktMeta c w N := by
    unfold offBktMeta offFpHash offBktHash; omega
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
  refine
    { w_mach_pos := by omega
      w_eq := rfl
      ptrB_le := hptr_w
      M_ge := by dsimp only [epochBpMetaLayout]; omega
      K_ge := hK64
      maxBlocks_ge := Nat.le_add_left 4 _
      nCap_lt_ptrB := hptr_lt
      sixteen_M_le := h16M
      M_maxSlabs_le := hMms
      maxSlabs_K_le := hmsK
      eight_MK_le := h8MK
      twelve_K_le := h12K
      four_maxBlocks_le := hmb4
      div_K_add_two_le := by dsimp only [epochBpMetaLayout]; omega
      sixteen_MK_le_maxTail := by
        dsimp only [epochBpMetaLayout]; unfold maxTailWhp; rw [Nat.mul_assoc]; omega
      sixteen_maxTail_le := h16mt
      offBktMeta_ge := hoff32
      offSlabDir_ge := le_rfl
      offTailDir_ge := le_rfl
      offSlabOwner_ge := le_rfl
      offTailOwner_ge := le_rfl
      frontier_ge := ?_ }
  dsimp only [epochBpMetaLayout]
  unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals
    offBTreeKeys offBTreeMeta at hend
  omega

/-- Pure extraction of `BlockPoolState` from bit-packed memory according to `mp : BpMetaLayout`. -/
@[expose] def extractBlockPool (mp : BpMetaLayout) (mem : ℕ → ℕ) : BlockPoolState where
  M := mp.M
  K := mp.K
  maxSlabs := mp.maxSlabs
  nSide := mem (mp.metaBase + 1)
  q := fun b =>
    if b < mp.M then readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem (16 * b) else 0
  r := fun b =>
    if b < mp.M then readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem (16 * b + 1) else 0
  head := fun b =>
    if b < mp.M then readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem (16 * b + 2) else 0
  actCode := fun b =>
    if b < mp.M then readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem (16 * b + 3) else 0
  actBlk := fun b =>
    if b < mp.M then readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem (16 * b + 4) else 0
  slabOf := fun b v =>
    if b < mp.M ∧ v < mp.maxSlabs then
      readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w mem (b * mp.maxSlabs + v)
    else 0
  tailRing := fun b rk =>
    if b < mp.M ∧ rk < 6 * mp.K then
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem (6 * mp.K * b + rk)
    else 0
  blkTag := fun P =>
    if P < mp.maxBlocks then
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem (4 * P)
    else 0
  blkMeta1 := fun P =>
    if P < mp.maxBlocks then
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem (4 * P + 1)
    else 0
  blkMeta2 := fun P =>
    if P < mp.maxBlocks then
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem (4 * P + 2)
    else 0
  unresLen := mem (mp.metaBase + 10)
  unresStack := fun i =>
    if i < mp.maxBlocks then
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem (4 * i + 3)
    else 0
  tbHighWater := mem (mp.metaBase + 11)
  freeTbTop := mem (mp.metaBase + 12)
  freeTbStack := fun i =>
    if i < 8 * mp.M then
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem (6 * mp.M * mp.K + i)
    else 0
  tbPhysBlk := fun tb =>
    if tb < 8 * mp.M then
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem (7 * mp.M * mp.K + tb)
    else 0
  tailOwnerBkt := fun t =>
    if t < 8 * mp.M * mp.K then
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w mem t
    else 0
  tailOwnerRing := fun t =>
    if t < 8 * mp.M * mp.K then
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w mem (8 * mp.M * mp.K + t)
    else 0
  topSwapAct := mem (mp.metaBase + 13)
  topSwapSrc := mem (mp.metaBase + 14)
  topSwapDst := mem (mp.metaBase + 15)
  topSwapCur := mem (mp.metaBase + 16)

private theorem slab_idx_lt {M maxSlabs b v : ℕ} (hb : b < M) (hv : v < maxSlabs) :
    b * maxSlabs + v < M * maxSlabs := by
  calc b * maxSlabs + v < b * maxSlabs + maxSlabs := Nat.add_lt_add_left hv _
    _ = (b + 1) * maxSlabs := by ring
    _ ≤ M * maxSlabs := Nat.mul_le_mul_right _ hb

private theorem ring_idx_lt_6MK {M K b rk : ℕ} (hb : b < M) (hrk : rk < 6 * K) :
    6 * K * b + rk < 6 * M * K := by
  calc 6 * K * b + rk < 6 * K * b + 6 * K := Nat.add_lt_add_left hrk _
    _ = (6 * K) * (b + 1) := by ring
    _ ≤ (6 * K) * M := Nat.mul_le_mul_left _ hb
    _ = 6 * M * K := by ring

private theorem ring_idx_lt_8MK {M K b rk : ℕ} (hb : b < M) (hrk : rk < 6 * K) :
    6 * K * b + rk < 8 * M * K :=
  (ring_idx_lt_6MK hb hrk).trans_le
    (Nat.mul_le_mul_right K (Nat.mul_le_mul_right M (by decide)))

private theorem tailOwner_idx_lt {M K maxTail t : ℕ}
    (h16le : 16 * M * K ≤ 16 * maxTail) (ht : t < 8 * M * K) (isRing : ℕ) :
    (if isRing = 0 then 0 else 8 * M * K) + t < 16 * maxTail := by
  have hadd : 8 * M * K + 8 * M * K = 16 * M * K := by ring
  split_ifs <;> omega

private theorem freeTb_idx_lt_8MK {M K i : ℕ} (hK : 64 ≤ K) (hi : i < 8 * M) :
    6 * M * K + i < 8 * M * K := by
  have h1 : i < M * K := lt_of_lt_of_le hi (by
    rw [Nat.mul_comm 8 M]
    exact Nat.mul_le_mul_left M (by omega : 8 ≤ K))
  have h2 : 6 * M * K + M * K ≤ 8 * M * K := by
    have : 6 * (M * K) + M * K ≤ 8 * (M * K) := by omega
    simpa only [Nat.mul_assoc] using this
  omega

private theorem tbPhys_idx_lt_8MK {M K tb : ℕ} (hK : 64 ≤ K) (htb : tb < 8 * M) :
    7 * M * K + tb < 8 * M * K := by
  have h1 : tb < M * K := lt_of_lt_of_le htb (by
    rw [Nat.mul_comm 8 M]
    exact Nat.mul_le_mul_left M (by omega : 8 ≤ K))
  have h2 : 7 * M * K + M * K = 8 * M * K := by ring
  omega

private theorem tailOwner_lt_16mt {M K maxTail t : ℕ}
    (h16le : 16 * M * K ≤ 16 * maxTail) (ht : t < 8 * M * K) :
    t < 16 * maxTail ∧ 8 * M * K + t < 16 * maxTail := by
  have hadd : 8 * M * K + 8 * M * K = 16 * M * K := by ring
  exact ⟨by omega, by omega⟩

private theorem six_MK_le_seven_MK (M K : ℕ) : 6 * M * K ≤ 7 * M * K :=
  Nat.mul_le_mul_right K (Nat.mul_le_mul_right M (by decide))

private theorem freeTb_idx_lt_7MK {M K i : ℕ} (hK : 64 ≤ K) (hi : i < 8 * M) :
    6 * M * K + i < 7 * M * K := by
  have h1 : i < M * K := lt_of_lt_of_le hi (by
    rw [Nat.mul_comm 8 M]; exact Nat.mul_le_mul_left M (by omega : 8 ≤ K))
  have h2 : 6 * M * K + M * K = 7 * M * K := by ring
  omega

/-- `extractBlockPool mp` depends only on addresses in `mp.OwnsMetaAddr`. -/
theorem extractBlockPool_congr {mp : BpMetaLayout} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < mp.w) (hK : 64 ≤ mp.K) (hmt : mp.M * mp.K ≤ mp.maxTail)
    (heq : ∀ addr, mp.OwnsMetaAddr addr → mem₁ addr = mem₂ addr) :
    extractBlockPool mp mem₁ = extractBlockPool mp mem₂ := by
  have h16le : 16 * mp.M * mp.K ≤ 16 * mp.maxTail := by
    rw [Nat.mul_assoc 16 mp.M mp.K]; exact Nat.mul_le_mul_left 16 hmt
  have hs1 : mem₁ (mp.metaBase + 1) = mem₂ (mp.metaBase + 1) := heq _ (Or.inl rfl)
  have hs : ∀ k, 10 ≤ k → k < 17 → mem₁ (mp.metaBase + k) = mem₂ (mp.metaBase + k) :=
    fun k h1 h2 => heq _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have hbm : ∀ idx < 16 * mp.M,
      readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem₁ idx =
        readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun a ha => heq a (Or.inr (Or.inr (Or.inl ha)))) hidx
  have hsd : ∀ idx < mp.M * mp.maxSlabs,
      readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w mem₁ idx =
        readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun a ha => heq a (Or.inr (Or.inr (Or.inr (Or.inl ha))))) hidx
  have htd : ∀ idx < 8 * mp.M * mp.K,
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem₁ idx =
        readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun a ha => heq a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))) hidx
  have hso : ∀ idx < 4 * mp.maxBlocks,
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem₁ idx =
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw
      (fun a ha => heq a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))) hidx
  have hto : ∀ idx < 16 * mp.maxTail,
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w mem₁ idx =
        readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw
      (fun a ha => heq a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha))))))) hidx
  refine BlockPoolState.ext_fields rfl rfl rfl hs1
    (fun b => by dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
    (fun b => by dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
    (fun b => by dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
    (fun b => by dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
    (fun b => by dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
    (fun b v => by
      dsimp only [extractBlockPool]
      split_ifs with hbv <;> [exact hsd _ (slab_idx_lt hbv.1 hbv.2); rfl])
    (fun b rk => by
      dsimp only [extractBlockPool]
      split_ifs with hbrk <;>
        [exact htd _ (ring_idx_lt_8MK hbrk.1 hbrk.2); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (hs 10 (by decide) (by decide))
    (fun i => by dsimp only [extractBlockPool]; split_ifs with hi <;> [exact hso _ (by omega); rfl])
    (hs 11 (by decide) (by decide))
    (hs 12 (by decide) (by decide))
    (fun i => by
      dsimp only [extractBlockPool]
      split_ifs with hi <;> [exact htd _ (freeTb_idx_lt_8MK hK hi); rfl])
    (fun tb => by
      dsimp only [extractBlockPool]
      split_ifs with htb <;> [exact htd _ (tbPhys_idx_lt_8MK hK htb); rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl])
    (hs 13 (by decide) (by decide))
    (hs 14 (by decide) (by decide))
    (hs 15 (by decide) (by decide))
    (hs 16 (by decide) (by decide))

/-- Compositional frame certificate for `BlockPoolState` metadata programs: bundles
`BoundedFrameProg mp.OwnsMetaAddr C p` together with exact preservation of `offBktMeta` slots
`5..15` (so SWAR B+-tree `(alloc, root)` slots `6..11` and per-bucket salt/role/compaction slots
`5, 12..15` are untouched). -/
structure BpMetaProg {α : Type} (mp : BpMetaLayout) (C : ℕ) (p : Memory.Prog α) : Prop where
  frame : BoundedFrameProg mp.OwnsMetaAddr C p
  bkt_other : ∀ s b slot, b < mp.M → 5 ≤ slot → slot < 16 →
    readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w
      ((Memory.spec 0).clientState s p).mem (16 * b + slot) =
    readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w s.mem (16 * b + slot)

namespace BpMetaProg

theorem pure_prog {α : Type} {mp : BpMetaLayout} (x : α) :
    BpMetaProg mp 0 (pure x : Memory.Prog α) :=
  ⟨BoundedFrameProg.pure_prog x, fun _ _ _ _ _ _ => rfl⟩

theorem read_prog (mp : BpMetaLayout) (a : ℕ) :
    BpMetaProg mp 1 (Memory.read a) :=
  ⟨BoundedFrameProg.read_prog _ a, fun _ _ _ _ _ _ => rfl⟩

theorem readOnly_prog {α : Type} (mp : BpMetaLayout) {C : ℕ} {p : Memory.Prog α}
    (hst : ∀ s, (Memory.spec 0).clientState s p = s) (hcost : ∀ s, memoryCost p s ≤ C) :
    BpMetaProg mp C p :=
  ⟨BoundedFrameProg.readOnly_of_state_eq _ hst hcost, fun s _ _ _ _ _ => by rw [hst]⟩

theorem mono {α : Type} {mp : BpMetaLayout} {C₁ C₂ : ℕ} {p : Memory.Prog α}
    (hp : BpMetaProg mp C₁ p) (hC : C₁ ≤ C₂) :
    BpMetaProg mp C₂ p :=
  ⟨hp.frame.mono (fun _ h => h) hC, hp.bkt_other⟩

theorem bind_prog {α β : Type} {mp : BpMetaLayout} {C₁ C₂ : ℕ} {p : Memory.Prog α}
    {q : α → Memory.Prog β} (hp : BpMetaProg mp C₁ p)
    (hq : ∀ x, BpMetaProg mp C₂ (q x)) :
    BpMetaProg mp (C₁ + C₂) (p >>= q) where
  frame := BoundedFrameProg.bind_prog hp.frame (fun x => (hq x).frame)
  bkt_other s b slot hb hlo hhi := by
    rw [StateTransitionSpec.clientState_bind]
    exact ((hq _).bkt_other _ b slot hb hlo hhi).trans (hp.bkt_other s b slot hb hlo hhi)

theorem ite_prog {α : Type} {mp : BpMetaLayout} {C : ℕ} (P : Prop) [Decidable P]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : P → BpMetaProg mp C p₁) (h₂ : ¬P → BpMetaProg mp C p₂) :
    BpMetaProg mp C (if P then p₁ else p₂) := by
  by_cases hP : P
  · rw [ite_eq_left hP]; exact h₁ hP
  · rw [ite_eq_right hP]; exact h₂ hP

theorem iterate_prog {δ σ : Type} {mp : BpMetaLayout} {C : ℕ} {body : δ × σ → Memory.Prog σ}
    (d : δ) (hb : ∀ a, BpMetaProg mp C (body (d, a))) (fuel : ℕ) (a₀ : σ) :
    BpMetaProg mp (C * fuel) (iterate body d fuel a₀) := by
  induction fuel generalizing a₀ with
  | zero =>
    unfold iterate
    simpa only [Nat.mul_zero] using pure_prog (mp := mp) a₀
  | succ k ih =>
    unfold iterate
    exact (bind_prog (hb a₀) (fun a₁ => ih a₁)).mono (by rw [Nat.mul_succ]; omega)

end BpMetaProg

/-! ## Section 2: `CoreValid` Bounds and `bpInitZeroedProg` -/

/-- In any `CoreValid` state, `unresStack` injects `Finset.range unresLen` into
`Finset.range B_full`, so `unresLen ≤ B_full`. -/
theorem BlockPoolState.CoreValid.unresLen_le_B_full {bp : BlockPoolState} (hv : bp.CoreValid) :
    bp.unresLen ≤ bp.B_full := by
  have hinj : Set.InjOn bp.unresStack ↑(Finset.range bp.unresLen) := fun i hi j hj heq => by
    have hi' := (hv.unres_fwd i (mem_range.mp hi)).2.2
    have hj' := (hv.unres_fwd j (mem_range.mp hj)).2.2
    exact hi'.symm.trans ((congrArg bp.blkMeta1 heq).trans hj')
  have hmaps : Set.MapsTo bp.unresStack ↑(Finset.range bp.unresLen) ↑(Finset.range bp.B_full) :=
    fun i hi => mem_range.mpr (hv.unres_fwd i (mem_range.mp hi)).1
  simpa using Finset.card_le_card_of_injOn bp.unresStack hmaps hinj

/-- In any `CoreValid` state, `bp.blkMeta2 bp.B_full` is active (`blkTag = 0`), so
`freeTbStack` injects `range freeTbTop` into `(range tbHighWater).erase (blkMeta2 B_full)`,
giving `freeTbTop < tbHighWater ≤ 8 * M`. -/
theorem BlockPoolState.CoreValid.freeTbTop_lt_tbHighWater {bp : BlockPoolState}
    (hv : bp.CoreValid) : bp.freeTbTop < bp.tbHighWater := by
  obtain ⟨htb₀_lt, _⟩ := hv.tb_fwd bp.B_full le_rfl (Or.inl hv.blkTag_top)
  set S := (Finset.range bp.tbHighWater).erase (bp.blkMeta2 bp.B_full)
  have hinj : Set.InjOn bp.freeTbStack ↑(Finset.range bp.freeTbTop) := fun i hi j hj heq =>
    hv.freeTb_inj i (mem_range.mp hi) j (mem_range.mp hj) heq
  have hmaps : Set.MapsTo bp.freeTbStack ↑(Finset.range bp.freeTbTop) ↑S := fun i hi => by
    obtain ⟨h1, h2⟩ := hv.freeTb_valid i (mem_range.mp hi)
    exact mem_erase.mpr ⟨(h2 bp.B_full le_rfl (Or.inl hv.blkTag_top)).symm, mem_range.mpr h1⟩
  have hcard : bp.freeTbTop ≤ S.card := by
    simpa using Finset.card_le_card_of_injOn bp.freeTbStack hmaps hinj
  have herase : S.card + 1 = bp.tbHighWater := by
    simpa using Finset.card_erase_add_one (mem_range.mpr htb₀_lt)
  omega

/-- When `bp.freeTbTop = 0`, `tbHighWater ≤ unresLen + actBucketCount + 1 < 8 * M`. -/
theorem BlockPoolState.CoreValid.tbHighWater_lt_of_freeTbTop_zero {bp : BlockPoolState}
    (hv : bp.CoreValid) (hz : bp.freeTbTop = 0) : bp.tbHighWater < 8 * bp.M := by
  have hsup := hv.tbHighWater_supply
  obtain ⟨hcard, hlt⟩ := hv.tail_block_card_lt
  rw [hz, zero_add, hcard] at hsup
  exact lt_of_le_of_lt hsup hlt

/-- `O(1)` initializer turning a Phase-1 zeroed metadata slice into `BlockPoolState.empty` by
writing `tbHighWater := 1` at `metaBase + 11` (`¬ReadsWidth`). -/
@[expose] def bpInitZeroedProg : BpMetaCtx → Memory.Prog Unit
  | ((((mb, _), _), _), _) => do
    let o1 ← pure 1
    Memory.write (mb + 11) o1

theorem realizesBounded_bpInitZeroed :
    RealizesBounded .exact bpInitZeroedProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have ho32 := hv0.offBktMeta_ge
    have hd1 := hv0.offSlabDir_ge
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    have hfr_w := hmem.1
    have h12K := hv0.twelve_K_le
    have hK64 := hv0.K_ge
    dsimp only [Fits] at *
    omega)

theorem bpInitZeroedProg_frame {mp : BpMetaLayout} (ho32 : 32 ≤ mp.offBktMeta)
    (hw : 0 < mp.w) :
    BpMetaProg mp 1 (bpInitZeroedProg mp.toCtx) where
  frame := by
    unfold bpInitZeroedProg; dsimp only [BpMetaLayout.toCtx]; simp only [pure_bind]
    exact BoundedFrameProg.write_prog (Or.inr (Or.inl ⟨by omega, by omega⟩)) 1
  bkt_other s b slot hb _ hhi := by
    unfold bpInitZeroedProg; dsimp only [BpMetaLayout.toCtx]; simp only [pure_bind]
    change readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w
      (Function.update s.mem (mp.metaBase + 11) 1) (16 * b + slot) = _
    refine readPacked_congr hw (fun addr ha => ?_) (by omega : 16 * b + slot < 16 * mp.M)
    exact Function.update_of_ne (by omega : addr ≠ mp.metaBase + 11) 1 s.mem

private theorem readPacked_of_zero {base k w : ℕ} (hw : 0 < w) {mem : ℕ → ℕ} {n idx : ℕ}
    (hidx : idx < n)
    (hz : ∀ addr, base ≤ addr → addr < base + packedWords n k w → mem addr = 0) :
    readPacked base k w mem idx = 0 := by
  have hcongr : readPacked base k w mem idx = readPacked base k w (fun _ => 0) idx :=
    readPacked_congr hw (fun addr ha => hz addr ha.1 ha.2) hidx
  rw [hcongr]
  unfold readPacked readBitSlice; dsimp only
  simp

theorem bpInitZeroedProg_spec {mp : BpMetaLayout} {s : Memory.State}
    (hv : mp.Valid mp.w s.frontier)
    (hzero : ∀ addr, mp.OwnsMetaAddr addr → s.mem addr = 0) :
    let s' := (Memory.spec 0).clientState s (bpInitZeroedProg mp.toCtx)
    extractBlockPool mp s'.mem = BlockPoolState.empty mp.M mp.K mp.maxSlabs ∧
    (extractBlockPool mp s'.mem).Balanced := by
  dsimp only
  have hw := hv.w_pos
  have hM2 := hv.M_ge
  have hK64 := hv.K_ge
  have h16le := hv.sixteen_MK_le_maxTail
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  set m' := Function.update s.mem (mp.metaBase + 11) 1
  have hm'_eq : ((Memory.spec 0).clientState s (bpInitZeroedProg mp.toCtx)).mem = m' := rfl
  rw [hm'_eq]
  have hm'_z : ∀ addr, mp.OwnsMetaAddr addr → addr ≠ mp.metaBase + 11 → m' addr = 0 :=
    fun addr ha hne => (Function.update_of_ne hne 1 s.mem).trans (hzero addr ha)
  have hemp : extractBlockPool mp m' = BlockPoolState.empty mp.M mp.K mp.maxSlabs := by
    refine BlockPoolState.ext_fields rfl rfl rfl
      (hm'_z _ (Or.inl rfl) (by omega))
      (fun b => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hb
        · exact readPacked_of_zero hw (n := 16 * mp.M) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))) (by omega)
        · rfl)
      (fun b => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hb
        · exact readPacked_of_zero hw (n := 16 * mp.M) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))) (by omega)
        · rfl)
      (fun b => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hb
        · exact readPacked_of_zero hw (n := 16 * mp.M) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))) (by omega)
        · rfl)
      (fun b => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hb
        · exact readPacked_of_zero hw (n := 16 * mp.M) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))) (by omega)
        · rfl)
      (fun b => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hb
        · exact readPacked_of_zero hw (n := 16 * mp.M) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))) (by omega)
        · rfl)
      (fun b v => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hbv
        · exact readPacked_of_zero hw (slab_idx_lt hbv.1 hbv.2) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))) (by omega)
        · rfl)
      (fun b rk => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hbrk
        · exact readPacked_of_zero hw (ring_idx_lt_8MK hbrk.1 hbrk.2)
            fun a h1 h2 =>
              hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))) (by omega)
        · rfl)
      (fun P => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hP
        · exact readPacked_of_zero hw (n := 4 * mp.maxBlocks) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))) (by omega)
        · rfl)
      (fun P => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hP
        · exact readPacked_of_zero hw (n := 4 * mp.maxBlocks) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))) (by omega)
        · rfl)
      (fun P => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hP
        · exact readPacked_of_zero hw (n := 4 * mp.maxBlocks) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))) (by omega)
        · rfl)
      (hm'_z _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by omega))
      (fun i => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hi
        · exact readPacked_of_zero hw (n := 4 * mp.maxBlocks) (by omega) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))) (by omega)
        · rfl)
      (Function.update_self (mp.metaBase + 11) 1 s.mem)
      (hm'_z _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by omega))
      (fun i => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with hi
        · refine readPacked_of_zero hw (n := 8 * mp.M * mp.K)
            (freeTb_idx_lt_8MK hK64 hi) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))) (by omega)
        · rfl)
      (fun tb => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with htb
        · refine readPacked_of_zero hw (n := 8 * mp.M * mp.K)
            (tbPhys_idx_lt_8MK hK64 htb) fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))) (by omega)
        · rfl)
      (fun t => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with ht
        · refine readPacked_of_zero hw (n := 16 * mp.maxTail)
            (tailOwner_lt_16mt h16le ht).1 fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))) (by omega)
        · rfl)
      (fun t => by
        dsimp only [extractBlockPool, BlockPoolState.empty]
        split_ifs with ht
        · refine readPacked_of_zero hw (n := 16 * mp.maxTail)
            (tailOwner_lt_16mt h16le ht).2 fun a h1 h2 =>
            hm'_z a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))) (by omega)
        · rfl)
      (hm'_z _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by omega))
      (hm'_z _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by omega))
      (hm'_z _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by omega))
      (hm'_z _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) (by omega))
  exact ⟨hemp, hemp ▸ BlockPoolState.empty_balanced (by omega) hK64⟩

/-! ## Section 3: Guarded Low-Level Table Accessors and Exact Field-Update Lemmas -/

/-- Read header scalar `k ∈ {1, 10..16}` at `metaBase + k` (`¬ReadsWidth`). -/
@[expose] def bpReadScalarProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (((((mb, _), _), _), _), k) =>
    if k = 1 ∨ (10 ≤ k ∧ k < 17) then
      Memory.read (mb + k)
    else
      pure 0

@[simp] theorem runClient_state_bpReadScalarProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpReadScalarProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩
  unfold bpReadScalarProg; dsimp only; split_ifs <;> rfl

theorem clientState_bpReadScalarProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadScalarProg x) = s :=
  runClient_state_bpReadScalarProg x s

theorem realizesBounded_bpReadScalar :
    RealizesBounded .exact bpReadScalarProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, idx⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have ho32 := hv0.offBktMeta_ge
    have hd1 := hv0.offSlabDir_ge
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    have hfr_w := hmem.1
    have h12K := hv0.twelve_K_le
    have hK64 := hv0.K_ge
    dsimp only [Fits] at *
    omega)

theorem bpReadScalarProg_frame (mp : BpMetaLayout) (k : ℕ) :
    BpMetaProg mp 1 (bpReadScalarProg (mp.toCtx, k)) :=
  BpMetaProg.readOnly_prog mp (fun s => clientState_bpReadScalarProg _ s) (fun s => by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; split_ifs <;> simp)

/-- Write `val ≤ nCap` to header scalar `k ∈ {1, 10..16}` at `metaBase + k` (`¬ReadsWidth`). -/
@[expose] def bpWriteScalarProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((((((mb, _), _), _), (_, (_, nc))), k), val) =>
    if (k = 1 ∨ (10 ≤ k ∧ k < 17)) ∧ val ≤ nc then
      Memory.write (mb + k) val
    else
      pure ()

@[simp] theorem runClient_frontier_bpWriteScalarProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpWriteScalarProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩, _⟩
  unfold bpWriteScalarProg; dsimp only; split_ifs <;> rfl

theorem frontier_bpWriteScalarProg (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (bpWriteScalarProg x)).frontier = s.frontier :=
  runClient_frontier_bpWriteScalarProg x s

theorem realizesBounded_bpWriteScalar :
    RealizesBounded .exact bpWriteScalarProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, idx⟩, val⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have ho32 := hv0.offBktMeta_ge
    have hd1 := hv0.offSlabDir_ge
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    have hfr_w := hmem.1
    have h12K := hv0.twelve_K_le
    have hK64 := hv0.K_ge
    dsimp only [Fits] at *
    omega)

theorem bpWriteScalarProg_frame {mp : BpMetaLayout} (hw : 0 < mp.w) (ho32 : 32 ≤ mp.offBktMeta)
    (k val : ℕ) :
    BpMetaProg mp 1 (bpWriteScalarProg ((mp.toCtx, k), val)) := by
  unfold bpWriteScalarProg; dsimp only [BpMetaLayout.toCtx]
  refine BpMetaProg.ite_prog ((k = 1 ∨ (10 ≤ k ∧ k < 17)) ∧ val ≤ mp.nCap)
    (fun hk => ⟨BoundedFrameProg.write_prog ?_ val, fun s b slot hb _ hhi => ?_⟩)
    (fun _ => (BpMetaProg.pure_prog ()).mono (by decide))
  · rcases hk.1 with rfl | h10
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · change readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w
      (Function.update s.mem (mp.metaBase + k) val) (16 * b + slot) = _
    refine readPacked_congr hw (fun addr ha => ?_) (by omega : 16 * b + slot < 16 * mp.M)
    rcases hk.1 with rfl | h10
    · exact Function.update_of_ne (by omega : addr ≠ mp.metaBase + 1) val s.mem
    · exact Function.update_of_ne (by omega : addr ≠ mp.metaBase + k) val s.mem

/-- Read bucket scalar slot `slot < 5` of `b < M` from `offBktMeta` (`¬ReadsWidth`). -/
@[expose] def bpReadBktMetaProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, obm), _), (_, (pb, wv))), (((m, _), _), _)), (b, slot)) =>
    if b < m ∧ slot < 5 then do
      let idx ← pure (16 * b + slot)
      readPackedCompGenProg (((mb, obm), (pb, wv)), idx)
    else
      pure 0

@[simp] theorem runClient_state_bpReadBktMetaProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpReadBktMetaProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpReadBktMetaProg; dsimp only; split_ifs <;> simp

theorem clientState_bpReadBktMetaProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadBktMetaProg x) = s :=
  runClient_state_bpReadBktMetaProg x s

theorem realizesBounded_bpReadBktMeta :
    RealizesBounded .exact bpReadBktMetaProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨b, slot⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have hd1 := hv0.offSlabDir_ge
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  · exact ⟨16 * m, hw, rfl, hpb, by omega, by omega⟩

theorem bpReadBktMetaProg_frame (mp : BpMetaLayout) (b slot : ℕ) :
    BpMetaProg mp 2 (bpReadBktMetaProg (mp.toCtx, (b, slot))) :=
  BpMetaProg.readOnly_prog mp (fun s => clientState_bpReadBktMetaProg _ s) (fun s => by
    unfold bpReadBktMetaProg; dsimp only [BpMetaLayout.toCtx]; split_ifs <;> simp)

/-- Write `val ≤ nCap` to bucket scalar slot `slot < 5` of `b < M` in `offBktMeta`. -/
@[expose] def bpWriteBktMetaProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((((mb, obm), _), (_, (pb, wv))), (((m, _), _), (_, nc))), (b, slot)), val) =>
    if b < m ∧ slot < 5 ∧ val ≤ nc then do
      let idx ← pure (16 * b + slot)
      writePackedCompGenProg ((((mb, obm), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_bpWriteBktMetaProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpWriteBktMetaProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold bpWriteBktMetaProg; dsimp only; split_ifs <;> simp

theorem frontier_bpWriteBktMetaProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (bpWriteBktMetaProg x)).frontier = s.frontier :=
  runClient_frontier_bpWriteBktMetaProg x s

theorem realizesBounded_bpWriteBktMeta :
    RealizesBounded .exact bpWriteBktMetaProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨b, slot⟩⟩, val⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have hd1 := hv0.offSlabDir_ge
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  · exact ⟨16 * m, hw, rfl, hpb, by omega, by omega⟩

theorem bpWriteBktMetaProg_frame {mp : BpMetaLayout} (hw : 0 < mp.w) (b slot val : ℕ) :
    BpMetaProg mp 4 (bpWriteBktMetaProg ((mp.toCtx, (b, slot)), val)) := by
  unfold bpWriteBktMetaProg; dsimp only [BpMetaLayout.toCtx]
  refine BpMetaProg.ite_prog (b < mp.M ∧ slot < 5 ∧ val ≤ mp.nCap)
    (fun hcond => ?_)
    (fun _ => (BpMetaProg.pure_prog ()).mono (by decide))
  simp only [pure_bind]
  refine ⟨BoundedFrameProg.writePackedComp_prog hw (nMax := 16 * mp.M) (by omega)
    (fun addr h1 h2 => Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))), fun s b' sl' hb' hlo hhi => ?_⟩
  rw [clientState_writePackedCompGenProg]
  exact readPacked_writePacked_of_ne hw s.mem (by omega) val

/-- Read `slabOf b v` from `offSlabDir` (`¬ReadsWidth`). -/
@[expose] def bpReadSlabOfProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, _), (osd, _)), (_, (pb, wv))), (((m, _), (ms, _)), _)), (b, v)) =>
    if b < m ∧ v < ms then do
      let idx ← pure (b * ms + v)
      readPackedCompGenProg (((mb, osd), (pb, wv)), idx)
    else
      pure 0

@[simp] theorem runClient_state_bpReadSlabOfProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpReadSlabOfProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpReadSlabOfProg; dsimp only; split_ifs <;> simp

theorem clientState_bpReadSlabOfProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadSlabOfProg x) = s :=
  runClient_state_bpReadSlabOfProg x s

theorem realizesBounded_bpReadSlabOf :
    RealizesBounded .exact bpReadSlabOfProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨b, v⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have hMms := hv0.M_maxSlabs_le
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  all_goals (
    first
    | exact ⟨m * ms, hw, rfl, hpb, slab_idx_lt ‹b < m› ‹v < ms›, by omega⟩
    | (have hbms := slab_idx_lt ‹b < m› ‹v < ms›; omega))

theorem bpReadSlabOfProg_frame (mp : BpMetaLayout) (b v : ℕ) :
    BpMetaProg mp 2 (bpReadSlabOfProg (mp.toCtx, (b, v))) :=
  BpMetaProg.readOnly_prog mp (fun s => clientState_bpReadSlabOfProg _ s) (fun s => by
    unfold bpReadSlabOfProg; dsimp only [BpMetaLayout.toCtx]; split_ifs <;> simp)

/-- Write `val < maxBlocks` to `slabOf b v` in `offSlabDir` (`¬ReadsWidth`). -/
@[expose] def bpWriteSlabOfProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((((mb, _), (osd, _)), (_, (pb, wv))), (((m, _), (ms, mbk)), _)), (b, v)), val) =>
    if b < m ∧ v < ms ∧ val < mbk then do
      let idx ← pure (b * ms + v)
      writePackedCompGenProg ((((mb, osd), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_bpWriteSlabOfProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpWriteSlabOfProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold bpWriteSlabOfProg; dsimp only; split_ifs <;> simp

theorem frontier_bpWriteSlabOfProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (bpWriteSlabOfProg x)).frontier = s.frontier :=
  runClient_frontier_bpWriteSlabOfProg x s

theorem realizesBounded_bpWriteSlabOf :
    RealizesBounded .exact bpWriteSlabOfProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨b, v⟩⟩, val⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have hMms := hv0.M_maxSlabs_le
    have hmb4 := hv0.four_maxBlocks_le
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  all_goals (
    first
    | exact ⟨m * ms, hw, rfl, hpb, slab_idx_lt ‹b < m› ‹v < ms›, by omega⟩
    | (have hbms := slab_idx_lt ‹b < m› ‹v < ms›; omega))

theorem bpWriteSlabOfProg_frame {mp : BpMetaLayout} (hw : 0 < mp.w)
    (hd1 : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offSlabDir)
    (b v val : ℕ) :
    BpMetaProg mp 4 (bpWriteSlabOfProg ((mp.toCtx, (b, v)), val)) := by
  unfold bpWriteSlabOfProg; dsimp only [BpMetaLayout.toCtx]
  refine BpMetaProg.ite_prog (b < mp.M ∧ v < mp.maxSlabs ∧ val < mp.maxBlocks)
    (fun hcond => ?_)
    (fun _ => (BpMetaProg.pure_prog ()).mono (by decide))
  simp only [pure_bind]
  have hbms := slab_idx_lt hcond.1 hcond.2.1
  refine ⟨BoundedFrameProg.writePackedComp_prog hw hbms
    (fun addr h1 h2 => Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))),
    fun s b' sl' hb' _ hhi => ?_⟩
  rw [clientState_writePackedCompGenProg]
  exact readPacked_congr hw
    (fun addr ha => writePacked_outside hw s.mem hbms val (by omega))
    (by omega : 16 * b' + sl' < 16 * mp.M)

/-- Read an entry `idx < 8 * M * K` from `offTailDir` (`tailRing`, `freeTbStack`, `tbPhysBlk`). -/
@[expose] def bpReadTailDirRawProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (((((mb, _), (_, otd)), (_, (pb, wv))), (((m, k), _), _)), idx) =>
    if idx < 8 * m * k then
      readPackedCompGenProg (((mb, otd), (pb, wv)), idx)
    else
      pure 0

@[simp] theorem runClient_state_bpReadTailDirRawProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpReadTailDirRawProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩
  unfold bpReadTailDirRawProg; dsimp only; split_ifs <;> simp

theorem clientState_bpReadTailDirRawProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadTailDirRawProg x) = s :=
  runClient_state_bpReadTailDirRawProg x s

theorem realizesBounded_bpReadTailDirRaw :
    RealizesBounded .exact bpReadTailDirRawProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, idx⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have h8MK := hv0.eight_MK_le
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  · exact ⟨8 * m * k, hw, rfl, hpb, ‹idx < 8 * m * k›, by omega⟩

theorem bpReadTailDirRawProg_frame (mp : BpMetaLayout) (idx : ℕ) :
    BpMetaProg mp 2 (bpReadTailDirRawProg (mp.toCtx, idx)) :=
  BpMetaProg.readOnly_prog mp (fun s => clientState_bpReadTailDirRawProg _ s) (fun s => by
    unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx]; split_ifs <;> simp)

/-- Write `val ≤ nCap` at `idx < 8 * M * K` in `offTailDir` (`¬ReadsWidth`). -/
@[expose] def bpWriteTailDirRawProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((((((mb, _), (_, otd)), (_, (pb, wv))), (((m, k), _), (_, nc))), idx), val) =>
    if idx < 8 * m * k ∧ val ≤ nc then
      writePackedCompGenProg ((((mb, otd), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_bpWriteTailDirRawProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpWriteTailDirRawProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩, _⟩
  unfold bpWriteTailDirRawProg; dsimp only; split_ifs <;> simp

theorem frontier_bpWriteTailDirRawProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (bpWriteTailDirRawProg x)).frontier = s.frontier :=
  runClient_frontier_bpWriteTailDirRawProg x s

theorem realizesBounded_bpWriteTailDirRaw :
    RealizesBounded .exact bpWriteTailDirRawProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, idx⟩, val⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have h8MK := hv0.eight_MK_le
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  · exact ⟨8 * m * k, hw, rfl, hpb, ‹idx < 8 * m * k›, by omega⟩

theorem bpWriteTailDirRawProg_frame {mp : BpMetaLayout} (hw : 0 < mp.w)
    (hobm_otd : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir)
    (idx val : ℕ) :
    BpMetaProg mp 4 (bpWriteTailDirRawProg ((mp.toCtx, idx), val)) := by
  unfold bpWriteTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
  refine BpMetaProg.ite_prog (idx < 8 * mp.M * mp.K ∧ val ≤ mp.nCap)
    (fun hcond => ?_)
    (fun _ => (BpMetaProg.pure_prog ()).mono (by decide))
  refine ⟨BoundedFrameProg.writePackedComp_prog hw hcond.1
    (fun addr h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))),
    fun s b' sl' hb' _ hhi => ?_⟩
  rw [clientState_writePackedCompGenProg]
  exact readPacked_congr hw
    (fun addr ha => writePacked_outside hw s.mem hcond.1 val (by omega))
    (by omega : 16 * b' + sl' < 16 * mp.M)

/-- Read lane `lane < 4` of block `P < maxBlocks` from `offSlabOwner` (`¬ReadsWidth`). -/
@[expose] def bpReadSlabOwnerProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, _), _), ((oso, _), (pb, wv))), ((_, (_, mbk)), _)), (P, lane)) =>
    if P < mbk ∧ lane < 4 then do
      let idx ← pure (4 * P + lane)
      readPackedCompGenProg (((mb, oso), (pb, wv)), idx)
    else
      pure 0

@[simp] theorem runClient_state_bpReadSlabOwnerProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpReadSlabOwnerProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpReadSlabOwnerProg; dsimp only; split_ifs <;> simp

theorem clientState_bpReadSlabOwnerProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadSlabOwnerProg x) = s :=
  runClient_state_bpReadSlabOwnerProg x s

theorem realizesBounded_bpReadSlabOwner :
    RealizesBounded .exact bpReadSlabOwnerProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨P, lane⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have hmb4 := hv0.four_maxBlocks_le
    have hmb_ge4 := hv0.maxBlocks_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  · exact ⟨4 * mbk, hw, rfl, hpb, by omega, by omega⟩

theorem bpReadSlabOwnerProg_frame (mp : BpMetaLayout) (P lane : ℕ) :
    BpMetaProg mp 2 (bpReadSlabOwnerProg (mp.toCtx, (P, lane))) :=
  BpMetaProg.readOnly_prog mp (fun s => clientState_bpReadSlabOwnerProg _ s) (fun s => by
    unfold bpReadSlabOwnerProg; dsimp only [BpMetaLayout.toCtx]; split_ifs <;> simp)

/-- Write `val ≤ nCap` to lane `lane < 4` of block `P < maxBlocks` in `offSlabOwner`. -/
@[expose] def bpWriteSlabOwnerProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((((mb, _), _), ((oso, _), (pb, wv))), ((_, (_, mbk)), (_, nc))), (P, lane)), val) =>
    if P < mbk ∧ lane < 4 ∧ val ≤ nc then do
      let idx ← pure (4 * P + lane)
      writePackedCompGenProg ((((mb, oso), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_bpWriteSlabOwnerProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpWriteSlabOwnerProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold bpWriteSlabOwnerProg; dsimp only; split_ifs <;> simp

theorem frontier_bpWriteSlabOwnerProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (bpWriteSlabOwnerProg x)).frontier = s.frontier :=
  runClient_frontier_bpWriteSlabOwnerProg x s

theorem realizesBounded_bpWriteSlabOwner :
    RealizesBounded .exact bpWriteSlabOwnerProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨P, lane⟩⟩, val⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have hmb4 := hv0.four_maxBlocks_le
    have hmb_ge4 := hv0.maxBlocks_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    dsimp only [Fits] at *
    try omega)
  · exact ⟨4 * mbk, hw, rfl, hpb, by omega, by omega⟩

theorem bpWriteSlabOwnerProg_frame {mp : BpMetaLayout} (hw : 0 < mp.w)
    (hobm_oso : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offSlabOwner)
    (P lane val : ℕ) :
    BpMetaProg mp 4 (bpWriteSlabOwnerProg ((mp.toCtx, (P, lane)), val)) := by
  unfold bpWriteSlabOwnerProg; dsimp only [BpMetaLayout.toCtx]
  refine BpMetaProg.ite_prog (P < mp.maxBlocks ∧ lane < 4 ∧ val ≤ mp.nCap)
    (fun hcond => ?_)
    (fun _ => (BpMetaProg.pure_prog ()).mono (by decide))
  simp only [pure_bind]
  refine ⟨BoundedFrameProg.writePackedComp_prog hw (nMax := 4 * mp.maxBlocks) (by omega)
    (fun addr h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))),
    fun s b' sl' hb' _ hhi => ?_⟩
  rw [clientState_writePackedCompGenProg]
  exact readPacked_congr hw
    (fun addr ha => writePacked_outside hw s.mem (N := 4 * mp.maxBlocks) (by omega) val (by omega))
    (by omega : 16 * b' + sl' < 16 * mp.M)

/-- Read `tailOwnerBkt t` (`isRing = 0`) or `tailOwnerRing t` (`isRing ≠ 0`) from `offTailOwner`. -/
@[expose] def bpReadTailOwnerProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, _), _), ((_, oto), (pb, wv))), (((m, k), _), _)), (t, isRing)) =>
    if t < 8 * m * k then do
      let baseIdx ← pure (if isRing = 0 then 0 else 8 * m * k)
      let idx ← pure (baseIdx + t)
      readPackedCompGenProg (((mb, oto), (pb, wv)), idx)
    else
      pure 0

@[simp] theorem runClient_state_bpReadTailOwnerProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpReadTailOwnerProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpReadTailOwnerProg; dsimp only; split_ifs <;> simp

theorem clientState_bpReadTailOwnerProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadTailOwnerProg x) = s :=
  runClient_state_bpReadTailOwnerProg x s

theorem realizesBounded_bpReadTailOwner :
    RealizesBounded .exact bpReadTailOwnerProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨t, isRing⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have h8MK := hv0.eight_MK_le
    have h16le := hv0.sixteen_MK_le_maxTail
    have h16mt := hv0.sixteen_maxTail_le
    have hfr := hv0.frontier_ge
    have hadd8 : 8 * m * k + 8 * m * k = 16 * m * k := by ring
    dsimp only [Fits] at *
    (try split_ifs at *) <;> try omega)
  all_goals exact ⟨16 * mt, hw, rfl, hpb, by omega, by omega⟩

theorem bpReadTailOwnerProg_frame (mp : BpMetaLayout) (t isRing : ℕ) :
    BpMetaProg mp 2 (bpReadTailOwnerProg (mp.toCtx, (t, isRing))) :=
  BpMetaProg.readOnly_prog mp (fun s => clientState_bpReadTailOwnerProg _ s) (fun s => by
    unfold bpReadTailOwnerProg; dsimp only [BpMetaLayout.toCtx]; split_ifs <;> simp)

/-- Write `val ≤ nCap` to `tailOwnerBkt t` (`isRing = 0`) or `tailOwnerRing t` (`isRing ≠ 0`). -/
@[expose] def bpWriteTailOwnerProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((((mb, _), _), ((_, oto), (pb, wv))), (((m, k), _), (_, nc))), (t, isRing)), val) =>
    if t < 8 * m * k ∧ val ≤ nc then do
      let baseIdx ← pure (if isRing = 0 then 0 else 8 * m * k)
      let idx ← pure (baseIdx + t)
      writePackedCompGenProg ((((mb, oto), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_bpWriteTailOwnerProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpWriteTailOwnerProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold bpWriteTailOwnerProg; dsimp only; split_ifs <;> simp

theorem frontier_bpWriteTailOwnerProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (bpWriteTailOwnerProg x)).frontier = s.frontier :=
  runClient_frontier_bpWriteTailOwnerProg x s

theorem realizesBounded_bpWriteTailOwner :
    RealizesBounded .exact bpWriteTailOwnerProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨t, isRing⟩⟩, val⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hw := hv0.w_mach_pos
    have hwv := hv0.w_eq; subst hwv
    have hpb := hv0.ptrB_le
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have h8MK := hv0.eight_MK_le
    have h16le := hv0.sixteen_MK_le_maxTail
    have h16mt := hv0.sixteen_maxTail_le
    have hfr := hv0.frontier_ge
    have hadd8 : 8 * m * k + 8 * m * k = 16 * m * k := by ring
    dsimp only [Fits] at *
    (try split_ifs at *) <;> try omega)
  all_goals exact ⟨16 * mt, hw, rfl, hpb, by omega, by omega⟩

theorem bpWriteTailOwnerProg_frame {mp : BpMetaLayout} (hw : 0 < mp.w)
    (hobm_oto : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailOwner)
    (h16_le : 16 * mp.M * mp.K ≤ 16 * mp.maxTail)
    (t isRing val : ℕ) :
    BpMetaProg mp 4 (bpWriteTailOwnerProg ((mp.toCtx, (t, isRing)), val)) := by
  unfold bpWriteTailOwnerProg; dsimp only [BpMetaLayout.toCtx]
  refine BpMetaProg.ite_prog (t < 8 * mp.M * mp.K ∧ val ≤ mp.nCap)
    (fun hcond => ?_)
    (fun _ => (BpMetaProg.pure_prog ()).mono (by decide))
  simp only [pure_bind]
  have h16 := tailOwner_idx_lt h16_le hcond.1 isRing
  refine ⟨BoundedFrameProg.writePackedComp_prog hw h16
    (fun addr h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))),
    fun s b' sl' hb' _ hhi => ?_⟩
  rw [clientState_writePackedCompGenProg]
  exact readPacked_congr hw
    (fun addr ha => writePacked_outside hw s.mem h16 val (by omega))
    (by omega : 16 * b' + sl' < 16 * mp.M)

/-! ### Section 3.5: Read Result Specs, Exact Field-Update Lemmas, and Arithmetic Gadgets -/

theorem clientResult_bpReadScalar {mp : BpMetaLayout} {k : ℕ} (s : Memory.State)
    (hk : k = 1 ∨ (10 ≤ k ∧ k < 17)) :
    (Memory.spec 0).clientResult s (bpReadScalarProg (mp.toCtx, k)) = s.mem (mp.metaBase + k) := by
  unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left hk]; rfl

theorem clientResult_bpReadBktMeta_q {mp : BpMetaLayout} {b : ℕ} (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadBktMetaProg (mp.toCtx, (b, 0))) =
      (extractBlockPool mp s.mem).q b := by
  unfold bpReadBktMetaProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hb : b < mp.M <;> simp [hb]

theorem clientResult_bpReadBktMeta_r {mp : BpMetaLayout} {b : ℕ} (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadBktMetaProg (mp.toCtx, (b, 1))) =
      (extractBlockPool mp s.mem).r b := by
  unfold bpReadBktMetaProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hb : b < mp.M <;> simp [hb]

theorem clientResult_bpReadBktMeta_head {mp : BpMetaLayout} {b : ℕ} (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadBktMetaProg (mp.toCtx, (b, 2))) =
      (extractBlockPool mp s.mem).head b := by
  unfold bpReadBktMetaProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hb : b < mp.M <;> simp [hb]

theorem clientResult_bpReadBktMeta_actCode {mp : BpMetaLayout} {b : ℕ} (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadBktMetaProg (mp.toCtx, (b, 3))) =
      (extractBlockPool mp s.mem).actCode b := by
  unfold bpReadBktMetaProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hb : b < mp.M <;> simp [hb]

theorem clientResult_bpReadBktMeta_actBlk {mp : BpMetaLayout} {b : ℕ} (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadBktMetaProg (mp.toCtx, (b, 4))) =
      (extractBlockPool mp s.mem).actBlk b := by
  unfold bpReadBktMetaProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hb : b < mp.M <;> simp [hb]

theorem clientResult_bpReadSlabOf {mp : BpMetaLayout} (b v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadSlabOfProg (mp.toCtx, (b, v))) =
      (extractBlockPool mp s.mem).slabOf b v := by
  unfold bpReadSlabOfProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hbv : b < mp.M ∧ v < mp.maxSlabs <;> simp [hbv]

theorem clientResult_bpReadTailDir_ring {mp : BpMetaLayout} {b rk : ℕ}
    (hb : b < mp.M) (hrk : rk < 6 * mp.K) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadTailDirRawProg (mp.toCtx, 6 * mp.K * b + rk)) =
      (extractBlockPool mp s.mem).tailRing b rk := by
  unfold bpReadTailDirRawProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  have hlt : 6 * mp.K * b + rk < 8 * mp.M * mp.K :=
    ring_idx_lt_8MK hb hrk
  simp [hlt, hb, hrk]

theorem clientResult_bpReadTailDir_freeTb {mp : BpMetaLayout} (hK : 64 ≤ mp.K) {i : ℕ}
    (hi : i < 8 * mp.M) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadTailDirRawProg (mp.toCtx, 6 * mp.M * mp.K + i)) =
      (extractBlockPool mp s.mem).freeTbStack i := by
  unfold bpReadTailDirRawProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  have hlt : 6 * mp.M * mp.K + i < 8 * mp.M * mp.K := freeTb_idx_lt_8MK hK hi
  simp [hlt, hi]

theorem clientResult_bpReadTailDir_tbPhys {mp : BpMetaLayout} (hK : 64 ≤ mp.K) {tb : ℕ}
    (htb : tb < 8 * mp.M) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadTailDirRawProg (mp.toCtx, 7 * mp.M * mp.K + tb)) =
      (extractBlockPool mp s.mem).tbPhysBlk tb := by
  unfold bpReadTailDirRawProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  have hlt : 7 * mp.M * mp.K + tb < 8 * mp.M * mp.K := tbPhys_idx_lt_8MK hK htb
  simp [hlt, htb]

theorem clientResult_bpReadSlabOwner_tag {mp : BpMetaLayout} (P : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadSlabOwnerProg (mp.toCtx, (P, 0))) =
      (extractBlockPool mp s.mem).blkTag P := by
  unfold bpReadSlabOwnerProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hP : P < mp.maxBlocks <;> simp [hP]

theorem clientResult_bpReadSlabOwner_m1 {mp : BpMetaLayout} (P : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadSlabOwnerProg (mp.toCtx, (P, 1))) =
      (extractBlockPool mp s.mem).blkMeta1 P := by
  unfold bpReadSlabOwnerProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hP : P < mp.maxBlocks <;> simp [hP]

theorem clientResult_bpReadSlabOwner_m2 {mp : BpMetaLayout} (P : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadSlabOwnerProg (mp.toCtx, (P, 2))) =
      (extractBlockPool mp s.mem).blkMeta2 P := by
  unfold bpReadSlabOwnerProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hP : P < mp.maxBlocks <;> simp [hP]

theorem clientResult_bpReadSlabOwner_unres {mp : BpMetaLayout} (i : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadSlabOwnerProg (mp.toCtx, (i, 3))) =
      (extractBlockPool mp s.mem).unresStack i := by
  unfold bpReadSlabOwnerProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases hi : i < mp.maxBlocks <;> simp [hi]

theorem clientResult_bpReadTailOwner_bkt {mp : BpMetaLayout} (t : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadTailOwnerProg (mp.toCtx, (t, 0))) =
      (extractBlockPool mp s.mem).tailOwnerBkt t := by
  unfold bpReadTailOwnerProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases ht : t < 8 * mp.M * mp.K <;> simp [ht]

theorem clientResult_bpReadTailOwner_ring {mp : BpMetaLayout} (t : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadTailOwnerProg (mp.toCtx, (t, 1))) =
      (extractBlockPool mp s.mem).tailOwnerRing t := by
  unfold bpReadTailOwnerProg extractBlockPool; dsimp only [BpMetaLayout.toCtx]
  by_cases ht : t < 8 * mp.M * mp.K <;> simp [ht]

/-- Disjointness helper: writing a header scalar `< 32` leaves all five packed tables unchanged. -/
private theorem scalar_write_preserves_tables {mp : BpMetaLayout} {w fr : ℕ}
    (hv : mp.Valid w fr) (mem : ℕ → ℕ) {k : ℕ} (hk : k < 32) (val : ℕ) :
    let m' := Function.update mem (mp.metaBase + k) val
    (∀ idx < 16 * mp.M,
      readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w m' idx =
        readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem idx) ∧
    (∀ idx < mp.M * mp.maxSlabs,
      readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w m' idx =
        readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w mem idx) ∧
    (∀ idx < 8 * mp.M * mp.K,
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w m' idx =
        readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem idx) ∧
    (∀ idx < 4 * mp.maxBlocks,
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w m' idx =
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem idx) ∧
    (∀ idx < 16 * mp.maxTail,
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w m' idx =
        readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w mem idx) := by
  have hw := hv.w_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  refine ⟨fun idx hidx => readPacked_congr hw
      (fun a ha => Function.update_of_ne (by omega : a ≠ mp.metaBase + k) val mem) hidx,
    fun idx hidx => readPacked_congr hw
      (fun a ha => Function.update_of_ne (by omega : a ≠ mp.metaBase + k) val mem) hidx,
    fun idx hidx => readPacked_congr hw
      (fun a ha => Function.update_of_ne (by omega : a ≠ mp.metaBase + k) val mem) hidx,
    fun idx hidx => readPacked_congr hw
      (fun a ha => Function.update_of_ne (by omega : a ≠ mp.metaBase + k) val mem) hidx,
    fun idx hidx => readPacked_congr hw
      (fun a ha => Function.update_of_ne (by omega : a ≠ mp.metaBase + k) val mem) hidx⟩

/-- Exact `extractBlockPool` update for `bpWriteScalarProg`. -/
theorem extractBlockPool_writeScalar {mp : BpMetaLayout} {w fr k val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hk : k = 1 ∨ (10 ≤ k ∧ k < 17)) (hval : val ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, k), val))
    extractBlockPool mp s'.mem =
      if k = 1 then { bp with nSide := val }
      else if k = 10 then { bp with unresLen := val }
      else if k = 11 then { bp with tbHighWater := val }
      else if k = 12 then { bp with freeTbTop := val }
      else if k = 13 then { bp with topSwapAct := val }
      else if k = 14 then { bp with topSwapSrc := val }
      else if k = 15 then { bp with topSwapDst := val }
      else { bp with topSwapCur := val } := by
  dsimp only
  have hk32 : k < 32 := by rcases hk with rfl | h10 <;> omega
  obtain ⟨hbm, hsd, htd, hso, hto⟩ := scalar_write_preserves_tables hv s.mem hk32 val
  have hK64 := hv.K_ge
  have h16le := hv.sixteen_MK_le_maxTail
  have hs'_mem : ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, k), val))).mem =
      Function.update s.mem (mp.metaBase + k) val := by
    unfold bpWriteScalarProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hk, hval⟩]; rfl
  rw [hs'_mem]
  have hsc_upd : ∀ j,
      Function.update s.mem (mp.metaBase + k) val (mp.metaBase + j) =
      if j = k then val else s.mem (mp.metaBase + j) := fun j => by
    by_cases hj : j = k
    · subst hj; simp
    · rw [ite_eq_right hj]
      exact Function.update_of_ne (by omega : mp.metaBase + j ≠ mp.metaBase + k) val s.mem
  rcases (by rcases hk with rfl | h10 <;> omega :
      k = 1 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (
    repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
    refine BlockPoolState.ext_fields rfl rfl rfl
      (by dsimp only [extractBlockPool]; rw [hsc_upd 1]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
      (fun b => by
        dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
      (fun b => by
        dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
      (fun b => by
        dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
      (fun b => by
        dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
      (fun b => by
        dsimp only [extractBlockPool]; split_ifs with hb <;> [exact hbm _ (by omega); rfl])
      (fun b v => by
        dsimp only [extractBlockPool]
        split_ifs with hbv <;> [exact hsd _ (slab_idx_lt hbv.1 hbv.2); rfl])
      (fun b rk => by
        dsimp only [extractBlockPool]
        split_ifs with hbrk <;>
          [exact htd _ (ring_idx_lt_8MK hbrk.1 hbrk.2); rfl])
      (fun P => by
        dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
      (fun P => by
        dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
      (fun P => by
        dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
      (by dsimp only [extractBlockPool]; rw [hsc_upd 10]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
      (fun i => by
        dsimp only [extractBlockPool]; split_ifs with hi <;> [exact hso _ (by omega); rfl])
      (by dsimp only [extractBlockPool]; rw [hsc_upd 11]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
      (by dsimp only [extractBlockPool]; rw [hsc_upd 12]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
      (fun i => by
        dsimp only [extractBlockPool]
        split_ifs with hi <;> [exact htd _ (freeTb_idx_lt_8MK hK64 hi); rfl])
      (fun tb => by
        dsimp only [extractBlockPool]
        split_ifs with htb <;> [exact htd _ (tbPhys_idx_lt_8MK hK64 htb); rfl])
      (fun t => by
        dsimp only [extractBlockPool]
        split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl])
      (fun t => by
        dsimp only [extractBlockPool]
        split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl])
      (by dsimp only [extractBlockPool]; rw [hsc_upd 13]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
      (by dsimp only [extractBlockPool]; rw [hsc_upd 14]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
      (by dsimp only [extractBlockPool]; rw [hsc_upd 15]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
      (by dsimp only [extractBlockPool]; rw [hsc_upd 16]
          first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)]))

/-- Exact `extractBlockPool` update for `bpWriteBktMetaProg` (`slot < 5`). -/
theorem extractBlockPool_writeBktMeta {mp : BpMetaLayout} {w fr b slot val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hslot : slot < 5) (hval : val ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpWriteBktMetaProg ((mp.toCtx, (b, slot)), val))
    extractBlockPool mp s'.mem =
      if slot = 0 then { bp with q := BlockPoolState.set1 bp.q b val }
      else if slot = 1 then { bp with r := BlockPoolState.set1 bp.r b val }
      else if slot = 2 then { bp with head := BlockPoolState.set1 bp.head b val }
      else if slot = 3 then { bp with actCode := BlockPoolState.set1 bp.actCode b val }
      else { bp with actBlk := BlockPoolState.set1 bp.actBlk b val } := by
  dsimp only
  have hw := hv.w_pos
  have hK64 := hv.K_ge
  have hnc_pb := hv.nCap_lt_ptrB
  have h16le := hv.sixteen_MK_le_maxTail
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hval_pb : val < 2 ^ mp.ptrB := lt_of_le_of_lt hval hnc_pb
  have hidx : 16 * b + slot < 16 * mp.M := by omega
  set m' := writePacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w s.mem (16 * b + slot) val
  have hs'_mem : ((Memory.spec 0).clientState s
      (bpWriteBktMetaProg ((mp.toCtx, (b, slot)), val))).mem = m' := by
    unfold bpWriteBktMetaProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hb, hslot, hval⟩, pure_bind]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hs'_mem]
  have hout : ∀ addr, ¬(mp.metaBase + mp.offBktMeta ≤ addr ∧
      addr < mp.metaBase + mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w) →
      m' addr = s.mem addr := fun addr ha => writePacked_outside hw s.mem hidx val ha
  have hsc : ∀ k < 32, m' (mp.metaBase + k) = s.mem (mp.metaBase + k) :=
    fun k hk => hout _ (by omega)
  have hsd_f : ∀ b' v, (extractBlockPool mp m').slabOf b' v =
      (extractBlockPool mp s.mem).slabOf b' v := fun b' v => by
    dsimp only [extractBlockPool]
    split_ifs with hbv
    · exact readPacked_congr hw (fun a ha => hout a (by omega)) (slab_idx_lt hbv.1 hbv.2)
    · rfl
  have htd : ∀ i < 8 * mp.M * mp.K,
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have htr_f : ∀ b' rk, (extractBlockPool mp m').tailRing b' rk =
      (extractBlockPool mp s.mem).tailRing b' rk := fun b' rk => by
    dsimp only [extractBlockPool]
    split_ifs with hbrk <;> [exact htd _ (ring_idx_lt_8MK hbrk.1 hbrk.2); rfl]
  have hso : ∀ i < 4 * mp.maxBlocks,
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have hbt_f : ∀ P, (extractBlockPool mp m').blkTag P = (extractBlockPool mp s.mem).blkTag P :=
    fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl]
  have hbm1_f : ∀ P, (extractBlockPool mp m').blkMeta1 P = (extractBlockPool mp s.mem).blkMeta1 P :=
    fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl]
  have hbm2_f : ∀ P, (extractBlockPool mp m').blkMeta2 P = (extractBlockPool mp s.mem).blkMeta2 P :=
    fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl]
  have hus_f : ∀ i, (extractBlockPool mp m').unresStack i =
      (extractBlockPool mp s.mem).unresStack i :=
    fun i => by dsimp only [extractBlockPool]; split_ifs with hi <;> [exact hso _ (by omega); rfl]
  have hfts_f : ∀ i, (extractBlockPool mp m').freeTbStack i =
      (extractBlockPool mp s.mem).freeTbStack i := fun i => by
    dsimp only [extractBlockPool]
    split_ifs with hi <;> [exact htd _ (freeTb_idx_lt_8MK hK64 hi); rfl]
  have htpb_f : ∀ tb, (extractBlockPool mp m').tbPhysBlk tb =
      (extractBlockPool mp s.mem).tbPhysBlk tb := fun tb => by
    dsimp only [extractBlockPool]
    split_ifs with htb <;> [exact htd _ (tbPhys_idx_lt_8MK hK64 htb); rfl]
  have hto : ∀ i < 16 * mp.maxTail,
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have htob_f : ∀ t, (extractBlockPool mp m').tailOwnerBkt t =
      (extractBlockPool mp s.mem).tailOwnerBkt t := fun t => by
    dsimp only [extractBlockPool]
    split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl]
  have htor_f : ∀ t, (extractBlockPool mp m').tailOwnerRing t =
      (extractBlockPool mp s.mem).tailOwnerRing t := fun t => by
    dsimp only [extractBlockPool]
    split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl]
  have hslot_upd : ∀ (sl : ℕ), sl < 5 → ∀ b',
      (if b' < mp.M then readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w m' (16 * b' + sl)
       else 0) =
      (if sl = slot then
        BlockPoolState.set1
          (fun x => if x < mp.M then
            readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w s.mem (16 * x + sl) else 0)
          b val b'
       else if b' < mp.M then
        readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w s.mem (16 * b' + sl)
       else 0) := fun sl hsl b' => by
    by_cases hsl_eq : sl = slot
    · subst hsl_eq; rw [ite_eq_left rfl]
      by_cases hb_eq : b' = b
      · subst hb_eq; rw [ite_eq_left hb, BlockPoolState.set1_self]
        exact readPacked_writePacked_self _ _ _ s.mem (16 * b' + sl) hval_pb
      · rw [BlockPoolState.set1_of_ne _ _ _ _ hb_eq]
        split_ifs with hb' <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl]
    · rw [ite_eq_right hsl_eq]
      split_ifs with hb' <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl]
  rcases (by omega : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4) with
    rfl | rfl | rfl | rfl | rfl
  all_goals (
    repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
    exact BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
      (fun b' => by dsimp only [extractBlockPool]; simpa using hslot_upd 0 (by decide) b')
      (fun b' => by dsimp only [extractBlockPool]; simpa using hslot_upd 1 (by decide) b')
      (fun b' => by dsimp only [extractBlockPool]; simpa using hslot_upd 2 (by decide) b')
      (fun b' => by dsimp only [extractBlockPool]; simpa using hslot_upd 3 (by decide) b')
      (fun b' => by dsimp only [extractBlockPool]; simpa using hslot_upd 4 (by decide) b')
      hsd_f htr_f hbt_f hbm1_f hbm2_f (hsc 10 (by decide)) hus_f
      (hsc 11 (by decide)) (hsc 12 (by decide)) hfts_f htpb_f htob_f htor_f
      (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide)))

/-- Exact `extractBlockPool` update for `bpWriteSlabOfProg`. -/
theorem extractBlockPool_writeSlabOf {mp : BpMetaLayout} {w fr b v val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hv_lt : v < mp.maxSlabs) (hval : val < mp.maxBlocks) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpWriteSlabOfProg ((mp.toCtx, (b, v)), val))
    extractBlockPool mp s'.mem =
      { bp with slabOf := BlockPoolState.set2 bp.slabOf b v val } := by
  dsimp only
  have hw := hv.w_pos
  have hK64 := hv.K_ge
  have hnc_pb := hv.nCap_lt_ptrB
  have hmb4 := hv.four_maxBlocks_le
  have h16le := hv.sixteen_MK_le_maxTail
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hval_pb : val < 2 ^ mp.ptrB := lt_of_le_of_lt (by omega : val ≤ mp.nCap) hnc_pb
  have hidx := slab_idx_lt hb hv_lt
  set m' := writePacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w s.mem (b * mp.maxSlabs + v) val
  have hs'_mem : ((Memory.spec 0).clientState s
      (bpWriteSlabOfProg ((mp.toCtx, (b, v)), val))).mem = m' := by
    unfold bpWriteSlabOfProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hb, hv_lt, hval⟩, pure_bind]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hs'_mem]
  have hout : ∀ addr, ¬(mp.metaBase + mp.offSlabDir ≤ addr ∧
      addr < mp.metaBase + mp.offSlabDir + packedWords (mp.M * mp.maxSlabs) mp.ptrB mp.w) →
      m' addr = s.mem addr := fun addr ha => writePacked_outside hw s.mem hidx val ha
  have hsc : ∀ k < 32, m' (mp.metaBase + k) = s.mem (mp.metaBase + k) :=
    fun k hk => hout _ (by omega)
  have hbm : ∀ i < 16 * mp.M,
      readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have htd : ∀ i < 8 * mp.M * mp.K,
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have hso : ∀ i < 4 * mp.maxBlocks,
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have hto : ∀ i < 16 * mp.maxTail,
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  refine BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' v' => by
      dsimp only [extractBlockPool]
      by_cases heq : b' = b ∧ v' = v
      · obtain ⟨rfl, rfl⟩ := heq
        rw [ite_eq_left ⟨hb, hv_lt⟩, BlockPoolState.set2_self]
        exact readPacked_writePacked_self _ _ _ s.mem (b' * mp.maxSlabs + v') hval_pb
      · rw [BlockPoolState.set2_of_ne _ _ _ _ _ _ heq]
        split_ifs with hbv'
        · refine readPacked_writePacked_of_ne hw s.mem (fun h_eq => heq ?_) val
          have hms_pos : 0 < mp.maxSlabs := Nat.zero_lt_of_lt hv_lt
          have hd_l : (b' * mp.maxSlabs + v') / mp.maxSlabs = b' := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hms_pos, Nat.div_eq_of_lt hbv'.2, zero_add]
          have hd_r : (b * mp.maxSlabs + v) / mp.maxSlabs = b := by
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hms_pos, Nat.div_eq_of_lt hv_lt, zero_add]
          have hb_eq : b' = b := hd_l.symm.trans ((congrArg (· / mp.maxSlabs) h_eq).trans hd_r)
          subst hb_eq
          exact ⟨rfl, Nat.add_left_cancel h_eq⟩
        · rfl)
    (fun b' rk => by
      dsimp only [extractBlockPool]
      split_ifs with hbrk <;>
        [exact htd _ (ring_idx_lt_8MK hbrk.1 hbrk.2); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (hsc 10 (by decide))
    (fun i => by dsimp only [extractBlockPool]; split_ifs with hi <;> [exact hso _ (by omega); rfl])
    (hsc 11 (by decide)) (hsc 12 (by decide))
    (fun i => by
      dsimp only [extractBlockPool]
      split_ifs with hi <;> [exact htd _ (freeTb_idx_lt_8MK hK64 hi); rfl])
    (fun tb => by
      dsimp only [extractBlockPool]
      split_ifs with htb <;> [exact htd _ (tbPhys_idx_lt_8MK hK64 htb); rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl])
    (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide))

/-- Helper: writing at `idx < 8 * M * K` in `offTailDir` leaves scalars and the other four tables
unchanged. -/
private theorem tailDir_write_preserves_other {mp : BpMetaLayout} {w fr : ℕ}
    (hv : mp.Valid w fr) (mem : ℕ → ℕ) {idx : ℕ} (hidx : idx < 8 * mp.M * mp.K) (val : ℕ) :
    let m' := writePacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem idx val
    (∀ k < 32, m' (mp.metaBase + k) = mem (mp.metaBase + k)) ∧
    (∀ i < 16 * mp.M,
      readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w mem i) ∧
    (∀ i < mp.M * mp.maxSlabs,
      readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w mem i) ∧
    (∀ i < 4 * mp.maxBlocks,
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem i) ∧
    (∀ i < 16 * mp.maxTail,
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w mem i) := by
  have hw := hv.w_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hout : ∀ addr, ¬(mp.metaBase + mp.offTailDir ≤ addr ∧
      addr < mp.metaBase + mp.offTailDir + packedWords (8 * mp.M * mp.K) mp.ptrB mp.w) →
      writePacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem idx val addr = mem addr :=
    fun addr ha => writePacked_outside hw mem hidx val ha
  exact ⟨fun k hk => hout _ (by omega),
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi,
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi,
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi,
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi⟩

/-- Exact `extractBlockPool` update for `tailRing b rk := val`. -/
theorem extractBlockPool_writeTailRing {mp : BpMetaLayout} {w fr b rk val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hrk : rk < 6 * mp.K) (hval : val ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s
      (bpWriteTailDirRawProg ((mp.toCtx, 6 * mp.K * b + rk), val))
    extractBlockPool mp s'.mem =
      { bp with tailRing := BlockPoolState.set2 bp.tailRing b rk val } := by
  dsimp only
  have hw := hv.w_pos
  have hK64 := hv.K_ge
  have hnc_pb := hv.nCap_lt_ptrB
  have h16le := hv.sixteen_MK_le_maxTail
  have hval_pb : val < 2 ^ mp.ptrB := lt_of_le_of_lt hval hnc_pb
  have hidx6 := ring_idx_lt_6MK hb hrk
  have hidx : 6 * mp.K * b + rk < 8 * mp.M * mp.K := ring_idx_lt_8MK hb hrk
  obtain ⟨hsc, hbm, hsd, hso, hto⟩ := tailDir_write_preserves_other hv s.mem hidx val
  have hs'_mem : ((Memory.spec 0).clientState s
      (bpWriteTailDirRawProg ((mp.toCtx, 6 * mp.K * b + rk), val))).mem =
      writePacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem (6 * mp.K * b + rk) val := by
    unfold bpWriteTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hidx, hval⟩]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hs'_mem]
  refine BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' v => by
      dsimp only [extractBlockPool]
      split_ifs with hbv <;> [exact hsd _ (slab_idx_lt hbv.1 hbv.2); rfl])
    (fun b' rk' => by
      dsimp only [extractBlockPool]
      by_cases heq : b' = b ∧ rk' = rk
      · obtain ⟨rfl, rfl⟩ := heq
        rw [ite_eq_left ⟨hb, hrk⟩, BlockPoolState.set2_self]
        exact readPacked_writePacked_self _ _ _ s.mem (6 * mp.K * b' + rk') hval_pb
      · rw [BlockPoolState.set2_of_ne _ _ _ _ _ _ heq]
        split_ifs with hbrk'
        · refine readPacked_writePacked_of_ne hw s.mem (fun h_eq => heq ?_) val
          have h6K : 0 < 6 * mp.K := by omega
          have hd_l : (6 * mp.K * b' + rk') / (6 * mp.K) = b' := by
            rw [Nat.mul_comm (6 * mp.K) b', Nat.add_comm, Nat.add_mul_div_right _ _ h6K,
              Nat.div_eq_of_lt hbrk'.2, zero_add]
          have hd_r : (6 * mp.K * b + rk) / (6 * mp.K) = b := by
            rw [Nat.mul_comm (6 * mp.K) b, Nat.add_comm, Nat.add_mul_div_right _ _ h6K,
              Nat.div_eq_of_lt hrk, zero_add]
          have hb_eq : b' = b := hd_l.symm.trans ((congrArg (· / (6 * mp.K)) h_eq).trans hd_r)
          subst hb_eq
          exact ⟨rfl, Nat.add_left_cancel h_eq⟩
        · rfl)
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (hsc 10 (by decide))
    (fun i => by dsimp only [extractBlockPool]; split_ifs with hi <;> [exact hso _ (by omega); rfl])
    (hsc 11 (by decide)) (hsc 12 (by decide))
    (fun i => by
      dsimp only [extractBlockPool]
      split_ifs with hi <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl])
    (fun tb => by
      dsimp only [extractBlockPool]
      split_ifs with htb
      · have h67 := six_MK_le_seven_MK mp.M mp.K
        exact readPacked_writePacked_of_ne hw s.mem (by omega) val
      · rfl)
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl])
    (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide))

/-- Exact `extractBlockPool` update for `freeTbStack i := val`. -/
theorem extractBlockPool_writeFreeTbStack {mp : BpMetaLayout} {w fr i val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hi : i < 8 * mp.M) (hval : val ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s
      (bpWriteTailDirRawProg ((mp.toCtx, 6 * mp.M * mp.K + i), val))
    extractBlockPool mp s'.mem =
      { bp with freeTbStack := BlockPoolState.set1 bp.freeTbStack i val } := by
  dsimp only
  have hw := hv.w_pos
  have hK64 := hv.K_ge
  have hnc_pb := hv.nCap_lt_ptrB
  have h16le := hv.sixteen_MK_le_maxTail
  have hval_pb : val < 2 ^ mp.ptrB := lt_of_le_of_lt hval hnc_pb
  have hidx7 := freeTb_idx_lt_7MK hK64 hi
  have hidx : 6 * mp.M * mp.K + i < 8 * mp.M * mp.K := freeTb_idx_lt_8MK hK64 hi
  obtain ⟨hsc, hbm, hsd, hso, hto⟩ := tailDir_write_preserves_other hv s.mem hidx val
  have hs'_mem : ((Memory.spec 0).clientState s
      (bpWriteTailDirRawProg ((mp.toCtx, 6 * mp.M * mp.K + i), val))).mem =
      writePacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem (6 * mp.M * mp.K + i) val := by
    unfold bpWriteTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hidx, hval⟩]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hs'_mem]
  refine BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' v => by
      dsimp only [extractBlockPool]
      split_ifs with hbv <;> [exact hsd _ (slab_idx_lt hbv.1 hbv.2); rfl])
    (fun b' rk => by
      dsimp only [extractBlockPool]
      split_ifs with hbrk
      · have hlt6 := ring_idx_lt_6MK hbrk.1 hbrk.2
        have h67 := six_MK_le_seven_MK mp.M mp.K
        exact readPacked_writePacked_of_ne hw s.mem (by omega) val
      · rfl)
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (hsc 10 (by decide))
    (fun j => by dsimp only [extractBlockPool]; split_ifs with hj <;> [exact hso _ (by omega); rfl])
    (hsc 11 (by decide)) (hsc 12 (by decide))
    (fun j => by
      dsimp only [extractBlockPool]
      by_cases heq : j = i
      · subst heq; rw [ite_eq_left hi, BlockPoolState.set1_self]
        exact readPacked_writePacked_self _ _ _ s.mem (6 * mp.M * mp.K + j) hval_pb
      · rw [BlockPoolState.set1_of_ne _ _ _ _ heq]
        split_ifs with hj <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl])
    (fun tb => by
      dsimp only [extractBlockPool]
      split_ifs with htb <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl])
    (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide))

/-- Exact `extractBlockPool` update for `tbPhysBlk tb := val`. -/
theorem extractBlockPool_writeTbPhysBlk {mp : BpMetaLayout} {w fr tb val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (htb : tb < 8 * mp.M) (hval : val ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s
      (bpWriteTailDirRawProg ((mp.toCtx, 7 * mp.M * mp.K + tb), val))
    extractBlockPool mp s'.mem =
      { bp with tbPhysBlk := BlockPoolState.set1 bp.tbPhysBlk tb val } := by
  dsimp only
  have hw := hv.w_pos
  have hK64 := hv.K_ge
  have hnc_pb := hv.nCap_lt_ptrB
  have h16le := hv.sixteen_MK_le_maxTail
  have hval_pb : val < 2 ^ mp.ptrB := lt_of_le_of_lt hval hnc_pb
  have hidx : 7 * mp.M * mp.K + tb < 8 * mp.M * mp.K := tbPhys_idx_lt_8MK hK64 htb
  obtain ⟨hsc, hbm, hsd, hso, hto⟩ := tailDir_write_preserves_other hv s.mem hidx val
  have hs'_mem : ((Memory.spec 0).clientState s
      (bpWriteTailDirRawProg ((mp.toCtx, 7 * mp.M * mp.K + tb), val))).mem =
      writePacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem (7 * mp.M * mp.K + tb) val := by
    unfold bpWriteTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hidx, hval⟩]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hs'_mem]
  refine BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
    (fun b' v => by
      dsimp only [extractBlockPool]
      split_ifs with hbv <;> [exact hsd _ (slab_idx_lt hbv.1 hbv.2); rfl])
    (fun b' rk => by
      dsimp only [extractBlockPool]
      split_ifs with hbrk
      · have hlt6 := ring_idx_lt_6MK hbrk.1 hbrk.2
        have h67 := six_MK_le_seven_MK mp.M mp.K
        exact readPacked_writePacked_of_ne hw s.mem (by omega) val
      · rfl)
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (fun P => by dsimp only [extractBlockPool]; split_ifs with hP <;> [exact hso _ (by omega); rfl])
    (hsc 10 (by decide))
    (fun j => by dsimp only [extractBlockPool]; split_ifs with hj <;> [exact hso _ (by omega); rfl])
    (hsc 11 (by decide)) (hsc 12 (by decide))
    (fun j => by
      dsimp only [extractBlockPool]
      split_ifs with hj
      · have hlt7 := freeTb_idx_lt_7MK hK64 hj
        exact readPacked_writePacked_of_ne hw s.mem (by omega) val
      · rfl)
    (fun tb' => by
      dsimp only [extractBlockPool]
      by_cases heq : tb' = tb
      · subst heq; rw [ite_eq_left htb, BlockPoolState.set1_self]
        exact readPacked_writePacked_self _ _ _ s.mem (7 * mp.M * mp.K + tb') hval_pb
      · rw [BlockPoolState.set1_of_ne _ _ _ _ heq]
        split_ifs with htb' <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl])
    (fun t => by
      dsimp only [extractBlockPool]
      split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl])
    (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide))

/-- Exact `extractBlockPool` update for `bpWriteSlabOwnerProg` (`lane < 4`). -/
theorem extractBlockPool_writeSlabOwner {mp : BpMetaLayout} {w fr P lane val : ℕ}
    {s : Memory.State} (hv : mp.Valid w fr) (hP : P < mp.maxBlocks) (hlane : lane < 4)
    (hval : val ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (P, lane)), val))
    extractBlockPool mp s'.mem =
      if lane = 0 then { bp with blkTag := BlockPoolState.set1 bp.blkTag P val }
      else if lane = 1 then { bp with blkMeta1 := BlockPoolState.set1 bp.blkMeta1 P val }
      else if lane = 2 then { bp with blkMeta2 := BlockPoolState.set1 bp.blkMeta2 P val }
      else { bp with unresStack := BlockPoolState.set1 bp.unresStack P val } := by
  dsimp only
  have hw := hv.w_pos
  have hK64 := hv.K_ge
  have hnc_pb := hv.nCap_lt_ptrB
  have h16le := hv.sixteen_MK_le_maxTail
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hval_pb : val < 2 ^ mp.ptrB := lt_of_le_of_lt hval hnc_pb
  have hidx : 4 * P + lane < 4 * mp.maxBlocks := by omega
  set m' := writePacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem (4 * P + lane) val
  have hs'_mem : ((Memory.spec 0).clientState s
      (bpWriteSlabOwnerProg ((mp.toCtx, (P, lane)), val))).mem = m' := by
    unfold bpWriteSlabOwnerProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hP, hlane, hval⟩, pure_bind]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hs'_mem]
  have hout : ∀ addr, ¬(mp.metaBase + mp.offSlabOwner ≤ addr ∧
      addr < mp.metaBase + mp.offSlabOwner + packedWords (4 * mp.maxBlocks) mp.ptrB mp.w) →
      m' addr = s.mem addr := fun addr ha => writePacked_outside hw s.mem hidx val ha
  have hsc : ∀ k < 32, m' (mp.metaBase + k) = s.mem (mp.metaBase + k) :=
    fun k hk => hout _ (by omega)
  have hbm : ∀ i < 16 * mp.M,
      readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have hq_f : ∀ b', (extractBlockPool mp m').q b' = (extractBlockPool mp s.mem).q b' :=
    fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl]
  have hr_f : ∀ b', (extractBlockPool mp m').r b' = (extractBlockPool mp s.mem).r b' :=
    fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl]
  have hhd_f : ∀ b', (extractBlockPool mp m').head b' = (extractBlockPool mp s.mem).head b' :=
    fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl]
  have hac_f : ∀ b', (extractBlockPool mp m').actCode b' = (extractBlockPool mp s.mem).actCode b' :=
    fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl]
  have hab_f : ∀ b', (extractBlockPool mp m').actBlk b' = (extractBlockPool mp s.mem).actBlk b' :=
    fun b' => by
      dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl]
  have hsd_f : ∀ b' v, (extractBlockPool mp m').slabOf b' v =
      (extractBlockPool mp s.mem).slabOf b' v := fun b' v => by
    dsimp only [extractBlockPool]
    split_ifs with hbv
    · exact readPacked_congr hw (fun a ha => hout a (by omega)) (slab_idx_lt hbv.1 hbv.2)
    · rfl
  have htd : ∀ i < 8 * mp.M * mp.K,
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have htr_f : ∀ b' rk, (extractBlockPool mp m').tailRing b' rk =
      (extractBlockPool mp s.mem).tailRing b' rk := fun b' rk => by
    dsimp only [extractBlockPool]
    split_ifs with hbrk <;> [exact htd _ (ring_idx_lt_8MK hbrk.1 hbrk.2); rfl]
  have hfts_f : ∀ i, (extractBlockPool mp m').freeTbStack i =
      (extractBlockPool mp s.mem).freeTbStack i := fun i => by
    dsimp only [extractBlockPool]
    split_ifs with hi <;> [exact htd _ (freeTb_idx_lt_8MK hK64 hi); rfl]
  have htpb_f : ∀ tb, (extractBlockPool mp m').tbPhysBlk tb =
      (extractBlockPool mp s.mem).tbPhysBlk tb := fun tb => by
    dsimp only [extractBlockPool]
    split_ifs with htb <;> [exact htd _ (tbPhys_idx_lt_8MK hK64 htb); rfl]
  have hto : ∀ i < 16 * mp.maxTail,
      readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have htob_f : ∀ t, (extractBlockPool mp m').tailOwnerBkt t =
      (extractBlockPool mp s.mem).tailOwnerBkt t := fun t => by
    dsimp only [extractBlockPool]
    split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).1; rfl]
  have htor_f : ∀ t, (extractBlockPool mp m').tailOwnerRing t =
      (extractBlockPool mp s.mem).tailOwnerRing t := fun t => by
    dsimp only [extractBlockPool]
    split_ifs with ht <;> [exact hto _ (tailOwner_lt_16mt h16le ht).2; rfl]
  have hlane_upd : ∀ (ln : ℕ), ln < 4 → ∀ Q,
      (if Q < mp.maxBlocks then
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w m' (4 * Q + ln)
       else 0) =
      (if ln = lane then
        BlockPoolState.set1
          (fun x => if x < mp.maxBlocks then
            readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem (4 * x + ln) else 0)
          P val Q
       else if Q < mp.maxBlocks then
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem (4 * Q + ln)
       else 0) := fun ln hln Q => by
    by_cases hln_eq : ln = lane
    · subst hln_eq; rw [ite_eq_left rfl]
      by_cases hQ_eq : Q = P
      · subst hQ_eq; rw [ite_eq_left hP, BlockPoolState.set1_self]
        exact readPacked_writePacked_self _ _ _ s.mem (4 * Q + ln) hval_pb
      · rw [BlockPoolState.set1_of_ne _ _ _ _ hQ_eq]
        split_ifs with hQ <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl]
    · rw [ite_eq_right hln_eq]
      split_ifs with hQ <;> [exact readPacked_writePacked_of_ne hw s.mem (by omega) val; rfl]
  rcases (by omega : lane = 0 ∨ lane = 1 ∨ lane = 2 ∨ lane = 3) with rfl | rfl | rfl | rfl
  all_goals (
    repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])
    exact BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
      hq_f hr_f hhd_f hac_f hab_f hsd_f htr_f
      (fun Q => by dsimp only [extractBlockPool]; simpa using hlane_upd 0 (by decide) Q)
      (fun Q => by dsimp only [extractBlockPool]; simpa using hlane_upd 1 (by decide) Q)
      (fun Q => by dsimp only [extractBlockPool]; simpa using hlane_upd 2 (by decide) Q)
      (hsc 10 (by decide))
      (fun Q => by dsimp only [extractBlockPool]; simpa using hlane_upd 3 (by decide) Q)
      (hsc 11 (by decide)) (hsc 12 (by decide)) hfts_f htpb_f htob_f htor_f
      (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide)))

/-- Exact `extractBlockPool` update for `bpWriteTailOwnerProg`. -/
theorem extractBlockPool_writeTailOwner {mp : BpMetaLayout} {w fr t isRing val : ℕ}
    {s : Memory.State} (hv : mp.Valid w fr) (ht : t < 8 * mp.M * mp.K) (hval : val ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s
      (bpWriteTailOwnerProg ((mp.toCtx, (t, isRing)), val))
    extractBlockPool mp s'.mem =
      if isRing = 0 then { bp with tailOwnerBkt := BlockPoolState.set1 bp.tailOwnerBkt t val }
      else { bp with tailOwnerRing := BlockPoolState.set1 bp.tailOwnerRing t val } := by
  dsimp only
  have hw := hv.w_pos
  have hK64 := hv.K_ge
  have hnc_pb := hv.nCap_lt_ptrB
  have h16le := hv.sixteen_MK_le_maxTail
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have hval_pb : val < 2 ^ mp.ptrB := lt_of_le_of_lt hval hnc_pb
  set idx := (if isRing = 0 then 0 else 8 * mp.M * mp.K) + t
  have hidx : idx < 16 * mp.maxTail := tailOwner_idx_lt h16le ht isRing
  set m' := writePacked (mp.metaBase + mp.offTailOwner) mp.ptrB mp.w s.mem idx val
  have hs'_mem : ((Memory.spec 0).clientState s
      (bpWriteTailOwnerProg ((mp.toCtx, (t, isRing)), val))).mem = m' := by
    unfold bpWriteTailOwnerProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨ht, hval⟩, pure_bind, pure_bind]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hs'_mem]
  have hout : ∀ addr, ¬(mp.metaBase + mp.offTailOwner ≤ addr ∧
      addr < mp.metaBase + mp.offTailOwner + packedWords (16 * mp.maxTail) mp.ptrB mp.w) →
      m' addr = s.mem addr := fun addr ha => writePacked_outside hw s.mem hidx val ha
  have hsc : ∀ k < 32, m' (mp.metaBase + k) = s.mem (mp.metaBase + k) :=
    fun k hk => hout _ (by omega)
  have hbm : ∀ i < 16 * mp.M,
      readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offBktMeta) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have hsd : ∀ i < mp.M * mp.maxSlabs,
      readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offSlabDir) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have htd : ∀ i < 8 * mp.M * mp.K,
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  have hso : ∀ i < 4 * mp.maxBlocks,
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w m' i =
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem i :=
    fun i hi => readPacked_congr hw (fun a ha => hout a (by omega)) hi
  by_cases hir : isRing = 0
  · rw [ite_eq_left hir]
    have hidx0 : idx = t := by simp [idx, hir]
    refine BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' v => by
        dsimp only [extractBlockPool]
        split_ifs with hbv <;> [exact hsd _ (slab_idx_lt hbv.1 hbv.2); rfl])
      (fun b' rk => by
        dsimp only [extractBlockPool]
        split_ifs with hbrk <;>
          [exact htd _ (ring_idx_lt_8MK hbrk.1 hbrk.2); rfl])
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (hsc 10 (by decide))
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (hsc 11 (by decide)) (hsc 12 (by decide))
      (fun i => by
        dsimp only [extractBlockPool]
        split_ifs with hi <;> [exact htd _ (freeTb_idx_lt_8MK hK64 hi); rfl])
      (fun tb => by
        dsimp only [extractBlockPool]
        split_ifs with htb <;> [exact htd _ (tbPhys_idx_lt_8MK hK64 htb); rfl])
      (fun t' => by
        dsimp only [extractBlockPool]
        by_cases heq : t' = t
        · subst heq; rw [ite_eq_left ht, BlockPoolState.set1_self]
          dsimp only [m']; rw [hidx0]
          exact readPacked_writePacked_self _ _ _ s.mem t' hval_pb
        · rw [BlockPoolState.set1_of_ne _ _ _ _ heq]
          split_ifs with ht'
          · dsimp only [m']; rw [hidx0]
            exact readPacked_writePacked_of_ne hw s.mem heq val
          · rfl)
      (fun t' => by
        dsimp only [extractBlockPool]
        split_ifs with ht'
        · dsimp only [m']; rw [hidx0]
          exact readPacked_writePacked_of_ne hw s.mem (by omega) val
        · rfl)
      (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide))
  · rw [ite_eq_right hir]
    have hidx1 : idx = 8 * mp.M * mp.K + t := by simp [idx, hir]
    refine BlockPoolState.ext_fields rfl rfl rfl (hsc 1 (by decide))
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' => by
        dsimp only [extractBlockPool]; split_ifs with hb' <;> [exact hbm _ (by omega); rfl])
      (fun b' v => by
        dsimp only [extractBlockPool]
        split_ifs with hbv <;> [exact hsd _ (slab_idx_lt hbv.1 hbv.2); rfl])
      (fun b' rk => by
        dsimp only [extractBlockPool]
        split_ifs with hbrk <;>
          [exact htd _ (ring_idx_lt_8MK hbrk.1 hbrk.2); rfl])
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (hsc 10 (by decide))
      (fun Q => by
        dsimp only [extractBlockPool]; split_ifs with hQ <;> [exact hso _ (by omega); rfl])
      (hsc 11 (by decide)) (hsc 12 (by decide))
      (fun i => by
        dsimp only [extractBlockPool]
        split_ifs with hi <;> [exact htd _ (freeTb_idx_lt_8MK hK64 hi); rfl])
      (fun tb => by
        dsimp only [extractBlockPool]
        split_ifs with htb <;> [exact htd _ (tbPhys_idx_lt_8MK hK64 htb); rfl])
      (fun t' => by
        dsimp only [extractBlockPool]
        split_ifs with ht'
        · dsimp only [m']; rw [hidx1]
          exact readPacked_writePacked_of_ne hw s.mem (by omega) val
        · rfl)
      (fun t' => by
        dsimp only [extractBlockPool]
        by_cases heq : t' = t
        · subst heq; rw [ite_eq_left ht, BlockPoolState.set1_self]
          dsimp only [m']; rw [hidx1]
          exact readPacked_writePacked_self _ _ _ s.mem (8 * mp.M * mp.K + t') hval_pb
        · rw [BlockPoolState.set1_of_ne _ _ _ _ heq]
          split_ifs with ht'
          · dsimp only [m']; rw [hidx1]
            exact readPacked_writePacked_of_ne hw s.mem (by omega) val
          · rfl)
      (hsc 13 (by decide)) (hsc 14 (by decide)) (hsc 15 (by decide)) (hsc 16 (by decide))

/-! ### Guarded Arithmetic Gadgets (`0` Overflow at `U = 2 ^ w - 1`) -/

/-- Compute `P * K + off` safely under `P * K + off ≤ nCap < 2 ^ w` (`¬ReadsWidth`). -/
@[expose] def bpBlkSlotProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((_, _), (((_, k), _), (_, nc))), (P, off)) =>
    if off < k ∧ (P < nc / k ∨ (P = nc / k ∧ off ≤ nc % k)) then
      pure (P * k + off)
    else
      pure 0

@[simp] theorem runClient_state_bpBlkSlotProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpBlkSlotProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpBlkSlotProg; dsimp only; split_ifs <;> rfl

theorem clientState_bpBlkSlotProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpBlkSlotProg x) = s :=
  runClient_state_bpBlkSlotProg x s

theorem realizesBounded_bpBlkSlot :
    RealizesBounded .exact bpBlkSlotProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨P, off⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hK64 := hv0.K_ge
    have h12K := hv0.twelve_K_le
    dsimp only [Fits] at *
    try omega)
  all_goals (
    first
    | (have h1 : (P + 1) * k ≤ (nc / k) * k := Nat.mul_le_mul_right k ‹P < nc / k›
       have h2 : (nc / k) * k ≤ nc := Nat.div_mul_le_self nc k
       rw [Nat.add_one_mul] at h1; omega)
    | (have h2 : (nc / k) * k + nc % k = nc := by rw [Nat.mul_comm]; exact Nat.div_add_mod nc k
       have hp_eq : P = nc / k := ‹P = nc / k›
       subst hp_eq; omega))

theorem clientResult_bpBlkSlot {mp : BpMetaLayout} {P off : ℕ} (hK : 0 < mp.K)
    (hoff : off < mp.K) (hle : P * mp.K + off ≤ mp.nCap) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpBlkSlotProg (mp.toCtx, (P, off))) = P * mp.K + off := by
  unfold bpBlkSlotProg; dsimp only [BpMetaLayout.toCtx]
  have hcond : off < mp.K ∧ (P < mp.nCap / mp.K ∨ (P = mp.nCap / mp.K ∧ off ≤ mp.nCap % mp.K)) := by
    refine ⟨hoff, ?_⟩
    have hdiv_le : P ≤ mp.nCap / mp.K := by
      have h1 : (P * mp.K + off) / mp.K ≤ mp.nCap / mp.K := Nat.div_le_div_right hle
      rwa [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add] at h1
    by_cases hlt : P < mp.nCap / mp.K
    · exact Or.inl hlt
    · have heq : P = mp.nCap / mp.K := by omega
      subst heq
      have h2 : (mp.nCap / mp.K) * mp.K + mp.nCap % mp.K = mp.nCap := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod mp.nCap mp.K
      exact Or.inr ⟨rfl, by omega⟩
  rw [ite_eq_left hcond]; rfl

/-- Compute `tb * K + off < 8 * M * K ≤ nCap` safely (`¬ReadsWidth`). -/
@[expose] def bpTbSlotProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((_, _), (((m, k), _), _)), (tb, off)) =>
    if tb < 8 * m ∧ off < k then
      pure (tb * k + off)
    else
      pure 0

@[simp] theorem runClient_state_bpTbSlotProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpTbSlotProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpTbSlotProg; dsimp only; split_ifs <;> rfl

theorem clientState_bpTbSlotProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpTbSlotProg x) = s :=
  runClient_state_bpTbSlotProg x s

theorem realizesBounded_bpTbSlot :
    RealizesBounded .exact bpTbSlotProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨tb, off⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have h8MK := hv0.eight_MK_le
    dsimp only [Fits] at *
    try omega)
  all_goals (
    have h1 : (tb + 1) * k ≤ (8 * m) * k := Nat.mul_le_mul_right k ‹tb < 8 * m›
    rw [Nat.add_one_mul] at h1; omega)

theorem clientResult_bpTbSlot {mp : BpMetaLayout} {tb off : ℕ}
    (htb : tb < 8 * mp.M) (hoff : off < mp.K) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpTbSlotProg (mp.toCtx, (tb, off))) = tb * mp.K + off := by
  unfold bpTbSlotProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left ⟨htb, hoff⟩]; rfl

/-- Compute `6 * K * b + rk < 6 * M * K ≤ nCap` safely (`¬ReadsWidth`). -/
@[expose] def bpTailRingIdxProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((_, _), (((m, k), _), _)), (b, rk)) =>
    if b < m ∧ rk < 6 * k then
      pure (6 * k * b + rk)
    else
      pure 0

@[simp] theorem runClient_state_bpTailRingIdxProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpTailRingIdxProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpTailRingIdxProg; dsimp only; split_ifs <;> rfl

theorem clientState_bpTailRingIdxProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpTailRingIdxProg x) = s :=
  runClient_state_bpTailRingIdxProg x s

theorem realizesBounded_bpTailRingIdx :
    RealizesBounded .exact bpTailRingIdxProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨b, rk⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have h12K := hv0.twelve_K_le
    have hK64 := hv0.K_ge
    have h8MK := hv0.eight_MK_le
    dsimp only [Fits] at *
    try omega)
  all_goals (
    have hlt8 := ring_idx_lt_8MK ‹b < m› ‹rk < 6 * k›
    omega)

theorem clientResult_bpTailRingIdx {mp : BpMetaLayout} {b rk : ℕ}
    (hb : b < mp.M) (hrk : rk < 6 * mp.K) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpTailRingIdxProg (mp.toCtx, (b, rk))) =
      6 * mp.K * b + rk := by
  unfold bpTailRingIdxProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left ⟨hb, hrk⟩]; rfl

/-- Compute `(hd + x) % (6 * K)` safely under `hd < 6 * K ∧ x < 6 * K` (`¬ReadsWidth`). -/
@[expose] def bpRingAddProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((_, _), (((_, k), _), _)), (hd, x)) =>
    if hd < 6 * k ∧ x < 6 * k then
      pure ((hd + x) % (6 * k))
    else
      pure 0

@[simp] theorem runClient_state_bpRingAddProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpRingAddProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpRingAddProg; dsimp only; split_ifs <;> rfl

theorem clientState_bpRingAddProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpRingAddProg x) = s :=
  runClient_state_bpRingAddProg x s

theorem realizesBounded_bpRingAdd :
    RealizesBounded .exact bpRingAddProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨hd, x⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have h12K := hv0.twelve_K_le
    have hK64 := hv0.K_ge
    dsimp only [Fits] at *
    omega)

theorem clientResult_bpRingAdd {mp : BpMetaLayout} {hd x : ℕ}
    (hhd : hd < 6 * mp.K) (hx : x < 6 * mp.K) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpRingAddProg (mp.toCtx, (hd, x))) =
      (hd + x) % (6 * mp.K) := by
  unfold bpRingAddProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left ⟨hhd, hx⟩]; rfl

/-- Compute `(rk + 6 * K - hd) % (6 * K)` safely under `hd < 6 * K ∧ rk < 6 * K` (`¬ReadsWidth`). -/
@[expose] def bpRingDiffProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((_, _), (((_, k), _), _)), (hd, rk)) =>
    if hd < 6 * k ∧ rk < 6 * k then
      pure ((rk + 6 * k - hd) % (6 * k))
    else
      pure 0

@[simp] theorem runClient_state_bpRingDiffProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpRingDiffProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpRingDiffProg; dsimp only; split_ifs <;> rfl

theorem clientState_bpRingDiffProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpRingDiffProg x) = s :=
  runClient_state_bpRingDiffProg x s

theorem realizesBounded_bpRingDiff :
    RealizesBounded .exact bpRingDiffProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨hd, rk⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have h12K := hv0.twelve_K_le
    have hK64 := hv0.K_ge
    dsimp only [Fits] at *
    omega)

theorem clientResult_bpRingDiff {mp : BpMetaLayout} {hd rk : ℕ}
    (hhd : hd < 6 * mp.K) (hrk : rk < 6 * mp.K) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpRingDiffProg (mp.toCtx, (hd, rk))) =
      (rk + 6 * mp.K - hd) % (6 * mp.K) := by
  unfold bpRingDiffProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left ⟨hhd, hrk⟩]; rfl

/-- Compute `qv * K + x` safely under `qv ≤ maxSlabs ∧ x ≤ 6 * K` (`¬ReadsWidth`). -/
@[expose] def bpBktLocProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((_, _), (((_, k), (ms, _)), _)), (qv, x)) =>
    if qv ≤ ms ∧ x ≤ 6 * k then
      pure (qv * k + x)
    else
      pure 0

@[simp] theorem runClient_state_bpBktLocProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpBktLocProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, ⟨_, _⟩⟩
  unfold bpBktLocProg; dsimp only; split_ifs <;> rfl

theorem clientState_bpBktLocProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpBktLocProg x) = s :=
  runClient_state_bpBktLocProg x s

theorem realizesBounded_bpBktLoc :
    RealizesBounded .exact bpBktLocProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨qv, x⟩⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have hK64 := hv0.K_ge
    have hmsK := hv0.maxSlabs_K_le
    have h12K := hv0.twelve_K_le
    dsimp only [Fits] at *
    have hms_le : ms ≤ ms * k := Nat.le_mul_of_pos_right _ (by omega)
    try omega)
  all_goals (
    have hmul : qv * k ≤ ms * k := Nat.mul_le_mul_right k (by omega : qv ≤ ms)
    omega)

theorem clientResult_bpBktLoc {mp : BpMetaLayout} {qv x : ℕ}
    (hqv : qv ≤ mp.maxSlabs) (hx : x ≤ 6 * mp.K) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpBktLocProg (mp.toCtx, (qv, x))) = qv * mp.K + x := by
  unfold bpBktLocProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left ⟨hqv, hx⟩]; rfl

/-- Read `bp.bktCount b = bp.q b * K + bp.r b` (`O(1)`, `¬ReadsWidth`). -/
@[expose] def bpReadBktCountProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (ctx, b) => do
    let qv ← bpReadBktMetaProg (ctx, (b, 0))
    let rv ← bpReadBktMetaProg (ctx, (b, 1))
    bpBktLocProg (ctx, (qv, rv))

@[simp] theorem runClient_state_bpReadBktCountProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpReadBktCountProg x)) = s := by
  rcases x with ⟨ctx, b⟩
  unfold bpReadBktCountProg
  simp

theorem clientState_bpReadBktCountProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadBktCountProg x) = s :=
  runClient_state_bpReadBktCountProg x s

theorem realizesBounded_bpReadBktCount :
    RealizesBounded .exact bpReadBktCountProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrb := realizesBounded_bpReadBktMeta
  have hbl := realizesBounded_bpBktLoc
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    have hw := hv0.w_mach_pos
    have hpow : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    dsimp only [Fits] at *
    try simp only [runClient_state_bpReadBktMetaProg] at *
    first | exact hv0 | omega)

theorem bpBlkSlotProg_frame (mp : BpMetaLayout) (P off : ℕ) :
    BpMetaProg mp 0 (bpBlkSlotProg (mp.toCtx, (P, off))) := by
  unfold bpBlkSlotProg; dsimp only [BpMetaLayout.toCtx]
  exact BpMetaProg.ite_prog _ (fun _ => BpMetaProg.pure_prog _) (fun _ => BpMetaProg.pure_prog _)

theorem bpTbSlotProg_frame (mp : BpMetaLayout) (tb off : ℕ) :
    BpMetaProg mp 0 (bpTbSlotProg (mp.toCtx, (tb, off))) := by
  unfold bpTbSlotProg; dsimp only [BpMetaLayout.toCtx]
  exact BpMetaProg.ite_prog _ (fun _ => BpMetaProg.pure_prog _) (fun _ => BpMetaProg.pure_prog _)

theorem bpTailRingIdxProg_frame (mp : BpMetaLayout) (b rk : ℕ) :
    BpMetaProg mp 0 (bpTailRingIdxProg (mp.toCtx, (b, rk))) := by
  unfold bpTailRingIdxProg; dsimp only [BpMetaLayout.toCtx]
  exact BpMetaProg.ite_prog _ (fun _ => BpMetaProg.pure_prog _) (fun _ => BpMetaProg.pure_prog _)

theorem bpRingAddProg_frame (mp : BpMetaLayout) (hd x : ℕ) :
    BpMetaProg mp 0 (bpRingAddProg (mp.toCtx, (hd, x))) := by
  unfold bpRingAddProg; dsimp only [BpMetaLayout.toCtx]
  exact BpMetaProg.ite_prog _ (fun _ => BpMetaProg.pure_prog _) (fun _ => BpMetaProg.pure_prog _)

theorem bpRingDiffProg_frame (mp : BpMetaLayout) (hd rk : ℕ) :
    BpMetaProg mp 0 (bpRingDiffProg (mp.toCtx, (hd, rk))) := by
  unfold bpRingDiffProg; dsimp only [BpMetaLayout.toCtx]
  exact BpMetaProg.ite_prog _ (fun _ => BpMetaProg.pure_prog _) (fun _ => BpMetaProg.pure_prog _)

theorem bpBktLocProg_frame (mp : BpMetaLayout) (qv x : ℕ) :
    BpMetaProg mp 0 (bpBktLocProg (mp.toCtx, (qv, x))) := by
  unfold bpBktLocProg; dsimp only [BpMetaLayout.toCtx]
  exact BpMetaProg.ite_prog _ (fun _ => BpMetaProg.pure_prog _) (fun _ => BpMetaProg.pure_prog _)

theorem bpReadBktCountProg_frame (mp : BpMetaLayout) (b : ℕ) :
    BpMetaProg mp 4 (bpReadBktCountProg (mp.toCtx, b)) := by
  unfold bpReadBktCountProg
  exact BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 0) fun qv =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 1) fun rv =>
    bpBktLocProg_frame mp qv rv

theorem bpReadBktCountProg_spec {mp : BpMetaLayout} {b : ℕ} {s : Memory.State}
    (hv : (extractBlockPool mp s.mem).CoreValid) (hb : b < mp.M) :
    (Memory.spec 0).clientResult s (bpReadBktCountProg (mp.toCtx, b)) =
      (extractBlockPool mp s.mem).bktCount b := by
  obtain ⟨hq_le, hr_lt, _, _, _⟩ := hv.bkt_bounds b hb
  unfold bpReadBktCountProg
  simp only [prog_clientResult_bind, runClient_state_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_q, clientResult_bpReadBktMeta_r]
  exact clientResult_bpBktLoc hq_le hr_lt.le s

/-! ## Section 4: Read-Only `(toPhys, ownerOf)` Lookup Programs -/

/-- Return `(x / K, x % K)` safely under `0 < K` (`¬ReadsWidth`). -/
@[expose] def bpDivModKProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (((_, _), (((_, k), _), _)), x) => pure (x / k, x % k)

@[simp] theorem runClient_state_bpDivModKProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpDivModKProg x)) = s := by
  rcases x with ⟨⟨⟨_, _⟩, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩, _⟩; rfl

theorem clientState_bpDivModKProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpDivModKProg x) = s :=
  runClient_state_bpDivModKProg x s

theorem realizesBounded_bpDivModK :
    RealizesBounded .exact bpDivModKProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, x⟩
    have hv0 := h
    have hK64 := hv0.K_ge
    dsimp only [BpMetaLayout.ofCtx, Fits] at *
    omega)

theorem bpDivModKProg_frame (mp : BpMetaLayout) (x : ℕ) :
    BpMetaProg mp 0 (bpDivModKProg (mp.toCtx, x)) :=
  BpMetaProg.pure_prog (x / mp.K, x % mp.K)

theorem clientResult_bpDivModK (mp : BpMetaLayout) (x : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpDivModKProg (mp.toCtx, x)) = (x / mp.K, x % mp.K) :=
  rfl

/-- Compute `bp.actCur b` (`O(1)`, `¬ReadsWidth`). -/
@[expose] def bpActCurProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))), (((m, k), (ms, mbk)), (mt, nc))), b) => do
    let ctx : BpMetaCtx :=
      ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))), (((m, k), (ms, mbk)), (mt, nc)))
    let ac ← bpReadBktMetaProg (ctx, (b, 3))
    if ac = 0 then pure 0
    else if ac ≤ k then pure (ac - 1)
    else pure (ac - k)

@[simp] theorem runClient_state_bpActCurProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpActCurProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩
  unfold bpActCurProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpReadBktMetaProg]
  split_ifs <;> rfl

theorem clientState_bpActCurProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpActCurProg x) = s :=
  runClient_state_bpActCurProg x s

theorem realizesBounded_bpActCur :
    RealizesBounded .exact bpActCurProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrb := realizesBounded_bpReadBktMeta
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, b⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have h12K := hv0.twelve_K_le
    have hK64 := hv0.K_ge
    dsimp only [Fits] at *
    first | exact h | omega)

theorem bpActCurProg_frame (mp : BpMetaLayout) (b : ℕ) :
    BpMetaProg mp 2 (bpActCurProg (mp.toCtx, b)) := by
  unfold bpActCurProg; dsimp only [BpMetaLayout.toCtx]; rw [BpMetaLayout.fold_toCtx]
  have hf := BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 3) fun ac =>
    BpMetaProg.ite_prog (ac = 0)
      (fun _ => BpMetaProg.pure_prog 0)
      (fun _ => BpMetaProg.ite_prog (ac ≤ mp.K)
        (fun _ => BpMetaProg.pure_prog (ac - 1))
        (fun _ => BpMetaProg.pure_prog (ac - mp.K)))
  exact hf.mono (by decide)

theorem bpActCurProg_spec {mp : BpMetaLayout} (b : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpActCurProg (mp.toCtx, b)) =
      (extractBlockPool mp s.mem).actCur b := by
  unfold bpActCurProg BlockPoolState.actCur
  dsimp only [BpMetaLayout.toCtx]; rw [BpMetaLayout.fold_toCtx]
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_actCode]
  by_cases h0 : (extractBlockPool mp s.mem).actCode b = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hK : (extractBlockPool mp s.mem).actCode b ≤ mp.K
    · have hK' : (extractBlockPool mp s.mem).actCode b ≤ (extractBlockPool mp s.mem).K := hK
      rw [ite_eq_left hK, ite_eq_left hK']; rfl
    · have hK' : ¬(extractBlockPool mp s.mem).actCode b ≤ (extractBlockPool mp s.mem).K := hK
      rw [ite_eq_right hK, ite_eq_right hK']; rfl

/-- Compute `bp.effBlk P off` (`O(1)`, `¬ReadsWidth`). -/
@[expose] def bpEffBlkProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (ctx, (P, off)) => do
    let tsa ← bpReadScalarProg (ctx, 13)
    let tsc ← bpReadScalarProg (ctx, 16)
    if tsa = 1 ∧ off < tsc then do
      let tss ← bpReadScalarProg (ctx, 14)
      let tsd ← bpReadScalarProg (ctx, 15)
      if P = tss then pure tsd
      else if P = tsd then pure tss
      else pure P
    else
      pure P

@[simp] theorem runClient_state_bpEffBlkProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpEffBlkProg x)) = s := by
  rcases x with ⟨ctx, ⟨P, off⟩⟩
  unfold bpEffBlkProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg]
  split_ifs
  · simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg]
    split_ifs <;> rfl
  · rfl

theorem clientState_bpEffBlkProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpEffBlkProg x) = s :=
  runClient_state_bpEffBlkProg x s

theorem realizesBounded_bpEffBlk :
    RealizesBounded .exact bpEffBlkProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨P, off⟩⟩
    have hv0 := h
    have hpow : 16 < 2 ^ w := lt_of_le_of_lt
      (by have := hv0.K_ge; have := hv0.twelve_K_le; omega) hv0.nCap_lt_two_pow_w
    dsimp only [Fits] at *
    try simp only [runClient_state_bpReadScalarProg] at *
    first | exact hv0 | omega)

theorem bpEffBlkProg_frame (mp : BpMetaLayout) (P off : ℕ) :
    BpMetaProg mp 4 (bpEffBlkProg (mp.toCtx, (P, off))) := by
  unfold bpEffBlkProg; dsimp only
  have hin : BpMetaProg mp 2 (do
      let tss ← bpReadScalarProg (mp.toCtx, 14)
      let tsd ← bpReadScalarProg (mp.toCtx, 15)
      if P = tss then pure tsd else if P = tsd then pure tss else pure P) :=
    (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 14) fun tss =>
      BpMetaProg.bind_prog (bpReadScalarProg_frame mp 15) fun tsd =>
      BpMetaProg.ite_prog (P = tss)
        (fun _ => BpMetaProg.pure_prog tsd)
        (fun _ => BpMetaProg.ite_prog (P = tsd)
          (fun _ => BpMetaProg.pure_prog tss)
          (fun _ => BpMetaProg.pure_prog P))).mono (by decide)
  exact (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 13) fun tsa =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 16) fun tsc =>
    BpMetaProg.ite_prog (tsa = 1 ∧ off < tsc)
      (fun _ => hin)
      (fun _ => (BpMetaProg.pure_prog P).mono (C₂ := 2) (by decide))).mono (by decide)

theorem bpEffBlkProg_spec {mp : BpMetaLayout} (P off : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpEffBlkProg (mp.toCtx, (P, off))) =
      (extractBlockPool mp s.mem).effBlk P off := by
  unfold bpEffBlkProg BlockPoolState.effBlk; dsimp only
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 13 = 1 ∨ 10 ≤ 13 ∧ 13 < 17),
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 16 = 1 ∨ 10 ≤ 16 ∧ 16 < 17)]
  by_cases hc : s.mem (mp.metaBase + 13) = 1 ∧ off < s.mem (mp.metaBase + 16)
  · have hc' : (extractBlockPool mp s.mem).topSwapAct = 1 ∧
        off < (extractBlockPool mp s.mem).topSwapCur := hc
    rw [ite_eq_left hc, ite_eq_left hc',
      StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 14 = 1 ∨ 10 ≤ 14 ∧ 14 < 17),
      StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 15 = 1 ∨ 10 ≤ 15 ∧ 15 < 17)]
    by_cases h1 : P = s.mem (mp.metaBase + 14)
    · have h1' : P = (extractBlockPool mp s.mem).topSwapSrc := h1
      rw [ite_eq_left h1, ite_eq_left h1']; rfl
    · have h1' : P ≠ (extractBlockPool mp s.mem).topSwapSrc := h1
      rw [ite_eq_right h1, ite_eq_right h1']
      by_cases h2 : P = s.mem (mp.metaBase + 15)
      · have h2' : P = (extractBlockPool mp s.mem).topSwapDst := h2
        rw [ite_eq_left h2, ite_eq_left h2']; rfl
      · have h2' : P ≠ (extractBlockPool mp s.mem).topSwapDst := h2
        rw [ite_eq_right h2, ite_eq_right h2']; rfl
  · have hc' : ¬((extractBlockPool mp s.mem).topSwapAct = 1 ∧
        off < (extractBlockPool mp s.mem).topSwapCur) := hc
    rw [ite_eq_right hc, ite_eq_right hc']; rfl

/-- Compute `bp.physOfTail tIdx` (`O(1)`, `¬ReadsWidth`). -/
@[expose] def bpPhysOfTailProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))), (((m, k), (ms, mbk)), (mt, nc))),
      tIdx) => do
    let ctx : BpMetaCtx :=
      ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))), (((m, k), (ms, mbk)), (mt, nc)))
    let tb ← pure (tIdx / k)
    let off ← pure (tIdx % k)
    if tb < 8 * m then do
      let idx_tb ← pure (7 * m * k + tb)
      let P ← bpReadTailDirRawProg (ctx, idx_tb)
      let E ← bpEffBlkProg (ctx, (P, off))
      bpBlkSlotProg (ctx, (E, off))
    else
      pure 0

@[simp] theorem runClient_state_bpPhysOfTailProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpPhysOfTailProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩
  unfold bpPhysOfTailProg; dsimp only
  simp only [pure_bind]
  split_ifs <;> simp

theorem clientState_bpPhysOfTailProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpPhysOfTailProg x) = s :=
  runClient_state_bpPhysOfTailProg x s

theorem realizesBounded_bpPhysOfTail :
    RealizesBounded .exact bpPhysOfTailProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrtd := realizesBounded_bpReadTailDirRaw
  have heb := realizesBounded_bpEffBlk
  have hbs := realizesBounded_bpBlkSlot
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, tIdx⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    dsimp only [BpMetaLayout.ofCtx] at hv0 hnc_w
    have h16M := hv0.sixteen_M_le
    have hM2 := hv0.M_ge
    have hK64 := hv0.K_ge
    have h12K := hv0.twelve_K_le
    have h8MK := hv0.eight_MK_le
    dsimp only [Fits] at *
    try simp only [runClient_state_bpReadTailDirRawProg, runClient_state_bpEffBlkProg] at *
    try (have h78 := tbPhys_idx_lt_8MK hK64 ‹tIdx / k < 8 * m›)
    first | exact h | omega)

theorem bpPhysOfTailProg_frame (mp : BpMetaLayout) (tIdx : ℕ) :
    BpMetaProg mp 6 (bpPhysOfTailProg (mp.toCtx, tIdx)) := by
  unfold bpPhysOfTailProg; dsimp only [BpMetaLayout.toCtx]; rw [BpMetaLayout.fold_toCtx]
  simp only [pure_bind]
  exact BpMetaProg.ite_prog (tIdx / mp.K < 8 * mp.M)
    (fun _ => BpMetaProg.mono
      (BpMetaProg.bind_prog
        (bpReadTailDirRawProg_frame mp (7 * mp.M * mp.K + tIdx / mp.K)) fun P =>
        BpMetaProg.bind_prog (bpEffBlkProg_frame mp P (tIdx % mp.K)) fun E =>
        bpBlkSlotProg_frame mp E (tIdx % mp.K))
      (by decide))
    (fun _ => (BpMetaProg.pure_prog 0).mono (C₂ := 6) (by decide))

theorem bpPhysOfTailProg_spec {mp : BpMetaLayout} {tIdx : ℕ} {s : Memory.State}
    (hK64 : 64 ≤ mp.K) (ht : tIdx < 8 * mp.M * mp.K)
    (hp_le : (extractBlockPool mp s.mem).physOfTail tIdx ≤ mp.nCap) :
    (Memory.spec 0).clientResult s (bpPhysOfTailProg (mp.toCtx, tIdx)) =
      (extractBlockPool mp s.mem).physOfTail tIdx := by
  have hK : 0 < mp.K := by omega
  have htb : tIdx / mp.K < 8 * mp.M := (Nat.div_lt_iff_lt_mul hK).mpr ht
  have hoff : tIdx % mp.K < mp.K := Nat.mod_lt tIdx hK
  unfold bpPhysOfTailProg; dsimp only [BpMetaLayout.toCtx]; rw [BpMetaLayout.fold_toCtx]
  simp only [pure_bind, ite_eq_left htb]
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadTailDirRawProg,
    clientResult_bpReadTailDir_tbPhys hK64 htb s,
    StateTransitionSpec.clientResult_bind, clientState_bpEffBlkProg, bpEffBlkProg_spec]
  exact clientResult_bpBlkSlot hK hoff hp_le s

/-- Remainder-branch sub-program of `bpToPhysProg` (`k_rem = loc - q * K`, `¬ReadsWidth`). -/
@[expose] def bpToPhysRemProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (ctx, (b, k_rem)) => do
    let acur ← bpActCurProg (ctx, b)
    if k_rem < acur then do
      let P_act ← bpReadBktMetaProg (ctx, (b, 4))
      let E ← bpEffBlkProg (ctx, (P_act, k_rem))
      bpBlkSlotProg (ctx, (E, k_rem))
    else do
      let hd ← bpReadBktMetaProg (ctx, (b, 2))
      let rk ← bpRingAddProg (ctx, (hd, k_rem))
      let tr_idx ← bpTailRingIdxProg (ctx, (b, rk))
      let tIdx ← bpReadTailDirRawProg (ctx, tr_idx)
      bpPhysOfTailProg (ctx, tIdx)

@[simp] theorem runClient_state_bpToPhysRemProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpToPhysRemProg x)) = s := by
  rcases x with ⟨ctx, ⟨b, k_rem⟩⟩
  unfold bpToPhysRemProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpActCurProg]
  split_ifs <;> simp

theorem clientState_bpToPhysRemProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpToPhysRemProg x) = s :=
  runClient_state_bpToPhysRemProg x s

theorem realizesBounded_bpToPhysRem :
    RealizesBounded .exact bpToPhysRemProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hac := realizesBounded_bpActCur
  have hrb := realizesBounded_bpReadBktMeta
  have heb := realizesBounded_bpEffBlk
  have hbs := realizesBounded_bpBlkSlot
  have hra := realizesBounded_bpRingAdd
  have htri := realizesBounded_bpTailRingIdx
  have hrtd := realizesBounded_bpReadTailDirRaw
  have hpot := realizesBounded_bpPhysOfTail
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨b, k_rem⟩⟩
    have hv0 := h
    have hpow : 16 < 2 ^ w := lt_of_le_of_lt
      (by have := hv0.K_ge; have := hv0.twelve_K_le; omega) hv0.nCap_lt_two_pow_w
    dsimp only [Fits] at *
    try simp only [runClient_state_bpActCurProg, runClient_state_bpReadBktMetaProg,
      runClient_state_bpEffBlkProg, runClient_state_bpRingAddProg,
      runClient_state_bpTailRingIdxProg, runClient_state_bpReadTailDirRawProg] at *
    first | exact hv0 | omega)

theorem bpToPhysRemProg_frame (mp : BpMetaLayout) (b k_rem : ℕ) :
    BpMetaProg mp 12 (bpToPhysRemProg (mp.toCtx, (b, k_rem))) := by
  unfold bpToPhysRemProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpActCurProg_frame mp b) fun acur =>
    BpMetaProg.ite_prog (k_rem < acur)
      (fun _ => (BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 4) fun P_act =>
          BpMetaProg.bind_prog (bpEffBlkProg_frame mp P_act k_rem) fun E =>
          bpBlkSlotProg_frame mp E k_rem).mono (C₂ := 10) (by decide))
      (fun _ => (BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
          BpMetaProg.bind_prog (bpRingAddProg_frame mp hd k_rem) fun rk =>
          BpMetaProg.bind_prog (bpTailRingIdxProg_frame mp b rk) fun tr_idx =>
          BpMetaProg.bind_prog (bpReadTailDirRawProg_frame mp tr_idx) fun tIdx =>
          bpPhysOfTailProg_frame mp tIdx).mono (C₂ := 10) (by decide))
  exact hf.mono (by decide)

/-- Compute `bp.toPhys b loc` (`O(1)`, `¬ReadsWidth`). -/
@[expose] def bpToPhysProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (ctx, (b, loc)) => do
    let qv ← bpReadBktMetaProg (ctx, (b, 0))
    let qk ← bpBktLocProg (ctx, (qv, 0))
    if loc < qk then do
      let dm ← bpDivModKProg (ctx, loc)
      let P ← bpReadSlabOfProg (ctx, (b, dm.1))
      let E ← bpEffBlkProg (ctx, (P, dm.2))
      bpBlkSlotProg (ctx, (E, dm.2))
    else do
      let k_rem ← pure (loc - qk)
      bpToPhysRemProg (ctx, (b, k_rem))

@[simp] theorem runClient_state_bpToPhysProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpToPhysProg x)) = s := by
  rcases x with ⟨ctx, ⟨b, loc⟩⟩
  unfold bpToPhysProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpReadBktMetaProg,
    runClient_state_bpBktLocProg]
  split_ifs <;> simp

theorem clientState_bpToPhysProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpToPhysProg x) = s :=
  runClient_state_bpToPhysProg x s

theorem realizesBounded_bpToPhys :
    RealizesBounded .exact bpToPhysProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrb := realizesBounded_bpReadBktMeta
  have hbl := realizesBounded_bpBktLoc
  have hdm := realizesBounded_bpDivModK
  have hrs := realizesBounded_bpReadSlabOf
  have heb := realizesBounded_bpEffBlk
  have hbs := realizesBounded_bpBlkSlot
  have hrem := realizesBounded_bpToPhysRem
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨b, loc⟩⟩
    have hv0 := h
    have hpow : 16 < 2 ^ w := lt_of_le_of_lt
      (by have := hv0.K_ge; have := hv0.twelve_K_le; omega) hv0.nCap_lt_two_pow_w
    dsimp only [Fits] at *
    try simp only [runClient_state_bpReadBktMetaProg, runClient_state_bpBktLocProg,
      runClient_state_bpDivModKProg, runClient_state_bpReadSlabOfProg,
      runClient_state_bpEffBlkProg] at *
    first | exact hv0 | omega)

theorem bpToPhysProg_frame (mp : BpMetaLayout) (b loc : ℕ) :
    BpMetaProg mp 24 (bpToPhysProg (mp.toCtx, (b, loc))) := by
  unfold bpToPhysProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 0) fun qv =>
    BpMetaProg.bind_prog (bpBktLocProg_frame mp qv 0) fun qk =>
    BpMetaProg.ite_prog (loc < qk)
      (fun _ => (BpMetaProg.bind_prog (bpDivModKProg_frame mp loc) fun dm =>
          BpMetaProg.bind_prog (bpReadSlabOfProg_frame mp b dm.1) fun P =>
          BpMetaProg.bind_prog (bpEffBlkProg_frame mp P dm.2) fun E =>
          bpBlkSlotProg_frame mp E dm.2).mono (C₂ := 12) (by decide))
      (fun _ => by simpa only [pure_bind] using bpToPhysRemProg_frame mp b (loc - qk))
  exact hf.mono (by decide)

theorem bpToPhysProg_spec {mp : BpMetaLayout} {b loc : ℕ} {s : Memory.State}
    (hv : (extractBlockPool mp s.mem).CoreValid)
    (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap)
    (hb : b < mp.M) (hloc : loc < (extractBlockPool mp s.mem).bktCount b) :
    (Memory.spec 0).clientResult s (bpToPhysProg (mp.toCtx, (b, loc))) =
      (extractBlockPool mp s.mem).toPhys b loc := by
  set bp := extractBlockPool mp s.mem
  have hK_eq : bp.K = mp.K := rfl
  have hK64 : 64 ≤ mp.K := hv.K_ge
  have hK : 0 < mp.K := hv.K_pos
  obtain ⟨hq_le, hr_lt, hhd_lt, hc_le, _⟩ := hv.bkt_bounds b hb
  rw [hK_eq] at hr_lt hhd_lt hc_le
  have htp_le : bp.toPhys b loc ≤ mp.nCap := (hv.toPhys_lt hb hloc).le.trans hn_le
  unfold bpToPhysProg
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_q, StateTransitionSpec.clientResult_bind,
    clientState_bpBktLocProg, clientResult_bpBktLoc hq_le (Nat.zero_le _) s, add_zero]
  by_cases hslab : loc < bp.q b * mp.K
  · have hslab' : loc < bp.q b * bp.K := hslab
    rw [ite_eq_left hslab, StateTransitionSpec.clientResult_bind, clientState_bpDivModKProg,
      clientResult_bpDivModK]
    dsimp only
    rw [StateTransitionSpec.clientResult_bind,
      clientState_bpReadSlabOfProg, clientResult_bpReadSlabOf b (loc / mp.K) s,
      StateTransitionSpec.clientResult_bind, clientState_bpEffBlkProg, bpEffBlkProg_spec]
    have htp_eq : bp.toPhys b loc =
        (extractBlockPool mp s.mem).effBlk
          ((extractBlockPool mp s.mem).slabOf b (loc / mp.K)) (loc % mp.K) * mp.K + loc % mp.K := by
      unfold BlockPoolState.toPhys; dsimp only; rw [ite_eq_left hslab']; rfl
    exact (clientResult_bpBlkSlot hK (Nat.mod_lt loc hK) (htp_eq ▸ htp_le) s).trans htp_eq.symm
  · have hslab' : ¬(loc < bp.q b * bp.K) := hslab
    rw [ite_eq_right hslab, pure_bind]
    unfold bpToPhysRemProg
    rw [StateTransitionSpec.clientResult_bind, clientState_bpActCurProg, bpActCurProg_spec]
    set k_rem := loc - bp.q b * mp.K
    have hk_lt_r : k_rem < bp.r b := by
      unfold BlockPoolState.bktCount at hloc; rw [hK_eq] at hloc; omega
    by_cases hact : k_rem < bp.actCur b
    · have hact' : loc - bp.q b * bp.K < bp.actCur b := hact
      rw [ite_eq_left hact, StateTransitionSpec.clientResult_bind,
        clientState_bpReadBktMetaProg, clientResult_bpReadBktMeta_actBlk,
        StateTransitionSpec.clientResult_bind, clientState_bpEffBlkProg, bpEffBlkProg_spec]
      have hk_lt_K : k_rem < mp.K := hact.trans_le (hK_eq ▸ BlockPoolState.actCur_le_K hc_le)
      have htp_eq : bp.toPhys b loc =
          (extractBlockPool mp s.mem).effBlk
            ((extractBlockPool mp s.mem).actBlk b) k_rem * mp.K + k_rem := by
        unfold BlockPoolState.toPhys; dsimp only; rw [ite_eq_right hslab', ite_eq_left hact']; rfl
      exact (clientResult_bpBlkSlot hK hk_lt_K (htp_eq ▸ htp_le) s).trans htp_eq.symm
    · have hact' : ¬(loc - bp.q b * bp.K < bp.actCur b) := hact
      rw [ite_eq_right hact]
      have hk_ge : bp.actCur b ≤ k_rem := Nat.le_of_not_lt hact
      have htf := hv.tail_fwd b hb k_rem hk_ge hk_lt_r
      dsimp only at htf
      have hrk_lt : (bp.head b + k_rem) % (6 * mp.K) < 6 * mp.K := Nat.mod_lt _ (by omega)
      have htp_eq : bp.toPhys b loc =
          (extractBlockPool mp s.mem).physOfTail
            ((extractBlockPool mp s.mem).tailRing b ((bp.head b + k_rem) % (6 * mp.K))) := by
        unfold BlockPoolState.toPhys; dsimp only; rw [ite_eq_right hslab', ite_eq_right hact']; rfl
      rw [StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
        clientResult_bpReadBktMeta_head, StateTransitionSpec.clientResult_bind,
        clientState_bpRingAddProg, clientResult_bpRingAdd hhd_lt (hk_lt_r.trans hr_lt) s,
        StateTransitionSpec.clientResult_bind, clientState_bpTailRingIdxProg,
        clientResult_bpTailRingIdx hb hrk_lt s, StateTransitionSpec.clientResult_bind,
        clientState_bpReadTailDirRawProg, clientResult_bpReadTailDir_ring hb hrk_lt s]
      have htf1 : (extractBlockPool mp s.mem).tailRing b ((bp.head b + k_rem) % (6 * mp.K)) <
          8 * mp.M * mp.K := htf.1
      exact (bpPhysOfTailProg_spec hK64 htf1 (htp_eq ▸ htp_le)).trans htp_eq.symm

/-- Compute `bp.ownerOfTail tIdx` (`O(1)`, `¬ReadsWidth`). -/
@[expose] def bpOwnerOfTailProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (ctx, tIdx) => do
    let b ← bpReadTailOwnerProg (ctx, (tIdx, 0))
    let rk ← bpReadTailOwnerProg (ctx, (tIdx, 1))
    let qv ← bpReadBktMetaProg (ctx, (b, 0))
    let hd ← bpReadBktMetaProg (ctx, (b, 2))
    let k_off ← bpRingDiffProg (ctx, (hd, rk))
    let loc ← bpBktLocProg (ctx, (qv, k_off))
    pure (b, loc)

@[simp] theorem runClient_state_bpOwnerOfTailProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpOwnerOfTailProg x)) = s := by
  rcases x with ⟨ctx, tIdx⟩
  unfold bpOwnerOfTailProg
  simp

theorem clientState_bpOwnerOfTailProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpOwnerOfTailProg x) = s :=
  runClient_state_bpOwnerOfTailProg x s

theorem realizesBounded_bpOwnerOfTail :
    RealizesBounded .exact bpOwnerOfTailProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrto := realizesBounded_bpReadTailOwner
  have hrb := realizesBounded_bpReadBktMeta
  have hrd := realizesBounded_bpRingDiff
  have hbl := realizesBounded_bpBktLoc
  realize
  all_goals (
    rcases d with ⟨ctx, tIdx⟩
    have hv0 := h
    have hpow : 4 < 2 ^ w := lt_of_le_of_lt
      (by have := hv0.K_ge; have := hv0.twelve_K_le; omega) hv0.nCap_lt_two_pow_w
    dsimp only [Fits] at *
    try simp only [runClient_state_bpReadTailOwnerProg, runClient_state_bpReadBktMetaProg,
      runClient_state_bpRingDiffProg] at *
    first | exact hv0 | omega)

theorem bpOwnerOfTailProg_frame (mp : BpMetaLayout) (tIdx : ℕ) :
    BpMetaProg mp 8 (bpOwnerOfTailProg (mp.toCtx, tIdx)) := by
  unfold bpOwnerOfTailProg; dsimp only
  exact (BpMetaProg.bind_prog (bpReadTailOwnerProg_frame mp tIdx 0) fun b =>
    BpMetaProg.bind_prog (bpReadTailOwnerProg_frame mp tIdx 1) fun rk =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 0) fun qv =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
    BpMetaProg.bind_prog (bpRingDiffProg_frame mp hd rk) fun k_off =>
    BpMetaProg.bind_prog (bpBktLocProg_frame mp qv k_off) fun loc =>
    BpMetaProg.pure_prog (b, loc)).mono (by decide)

theorem bpOwnerOfTailProg_spec {mp : BpMetaLayout} {tIdx : ℕ} {s : Memory.State}
    (hv : (extractBlockPool mp s.mem).CoreValid)
    (hb : (extractBlockPool mp s.mem).tailOwnerBkt tIdx < mp.M)
    (hrk : (extractBlockPool mp s.mem).tailOwnerRing tIdx < 6 * mp.K) :
    (Memory.spec 0).clientResult s (bpOwnerOfTailProg (mp.toCtx, tIdx)) =
      (extractBlockPool mp s.mem).ownerOfTail tIdx := by
  have hK : 0 < mp.K := hv.K_pos
  obtain ⟨hq_le, _, hhd_lt, _, _⟩ := hv.bkt_bounds _ hb
  have hk_lt : ((extractBlockPool mp s.mem).tailOwnerRing tIdx + 6 * mp.K -
      (extractBlockPool mp s.mem).head ((extractBlockPool mp s.mem).tailOwnerBkt tIdx)) %
      (6 * mp.K) < 6 * mp.K := Nat.mod_lt _ (by omega)
  unfold bpOwnerOfTailProg BlockPoolState.ownerOfTail
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadTailOwnerProg,
    clientResult_bpReadTailOwner_bkt, StateTransitionSpec.clientResult_bind,
    clientState_bpReadTailOwnerProg, clientResult_bpReadTailOwner_ring,
    StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_q, StateTransitionSpec.clientResult_bind,
    clientState_bpReadBktMetaProg, clientResult_bpReadBktMeta_head,
    StateTransitionSpec.clientResult_bind, clientState_bpRingDiffProg,
    clientResult_bpRingDiff hhd_lt hrk s, StateTransitionSpec.clientResult_bind,
    clientState_bpBktLocProg, clientResult_bpBktLoc hq_le hk_lt.le s]
  rfl

/-- Active-block (`tag ≠ 1`) sub-program of `bpOwnerOfProg` (`¬ReadsWidth`). -/
@[expose] def bpOwnerOfNonSlabProg : BpMetaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog (ℕ × ℕ)
  | (ctx, ((P, off), tag)) =>
    if tag = 2 then do
      let b ← bpReadSlabOwnerProg (ctx, (P, 1))
      let acur ← bpActCurProg (ctx, b)
      if off < acur then do
        let qv ← bpReadBktMetaProg (ctx, (b, 0))
        let loc ← bpBktLocProg (ctx, (qv, off))
        pure (b, loc)
      else do
        let tb ← bpReadSlabOwnerProg (ctx, (P, 2))
        let tIdx ← bpTbSlotProg (ctx, (tb, off))
        bpOwnerOfTailProg (ctx, tIdx)
    else do
      let tb ← bpReadSlabOwnerProg (ctx, (P, 2))
      let tIdx ← bpTbSlotProg (ctx, (tb, off))
      bpOwnerOfTailProg (ctx, tIdx)

@[simp] theorem runClient_state_bpOwnerOfNonSlabProg
    (x : BpMetaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpOwnerOfNonSlabProg x)) = s := by
  rcases x with ⟨ctx, ⟨⟨P, off⟩, tag⟩⟩
  unfold bpOwnerOfNonSlabProg; dsimp only
  split_ifs
  · simp only [prog_runClient_state_bind, runClient_state_bpReadSlabOwnerProg,
      runClient_state_bpActCurProg]
    split_ifs <;> simp
  · simp

theorem clientState_bpOwnerOfNonSlabProg
    (x : BpMetaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpOwnerOfNonSlabProg x) = s :=
  runClient_state_bpOwnerOfNonSlabProg x s

theorem realizesBounded_bpOwnerOfNonSlab :
    RealizesBounded .exact bpOwnerOfNonSlabProg
      (WordEncoding.encode (α := BpMetaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  have hac := realizesBounded_bpActCur
  have hrb := realizesBounded_bpReadBktMeta
  have hbl := realizesBounded_bpBktLoc
  have hts := realizesBounded_bpTbSlot
  have hoot := realizesBounded_bpOwnerOfTail
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨⟨P, off⟩, tag⟩⟩
    have hv0 := h
    have hpow : 4 < 2 ^ w := lt_of_le_of_lt
      (by have := hv0.K_ge; have := hv0.twelve_K_le; omega) hv0.nCap_lt_two_pow_w
    dsimp only [Fits] at *
    try simp only [runClient_state_bpReadSlabOwnerProg, runClient_state_bpActCurProg,
      runClient_state_bpReadBktMetaProg, runClient_state_bpTbSlotProg] at *
    first | exact hv0 | omega)

theorem bpOwnerOfNonSlabProg_frame (mp : BpMetaLayout) (P off tag : ℕ) :
    BpMetaProg mp 16 (bpOwnerOfNonSlabProg (mp.toCtx, ((P, off), tag))) := by
  unfold bpOwnerOfNonSlabProg; dsimp only
  refine BpMetaProg.ite_prog (tag = 2) (fun _ => ?_) (fun _ => ?_)
  · have hf := BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 1) fun b =>
      BpMetaProg.bind_prog (bpActCurProg_frame mp b) fun acur =>
      BpMetaProg.ite_prog (off < acur)
        (fun _ => (BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 0) fun qv =>
          BpMetaProg.bind_prog (bpBktLocProg_frame mp qv off) fun loc =>
          BpMetaProg.pure_prog (b, loc)).mono (C₂ := 10) (by decide))
        (fun _ => (BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 2) fun tb =>
          BpMetaProg.bind_prog (bpTbSlotProg_frame mp tb off) fun tIdx =>
          bpOwnerOfTailProg_frame mp tIdx).mono (C₂ := 10) (by decide))
    exact hf.mono (by decide)
  · exact (BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 2) fun tb =>
      BpMetaProg.bind_prog (bpTbSlotProg_frame mp tb off) fun tIdx =>
      bpOwnerOfTailProg_frame mp tIdx).mono (by decide)

/-- Compute `bp.ownerOf p` (`O(1)`, `¬ReadsWidth`). -/
@[expose] def bpOwnerOfProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (ctx, p) => do
    let dm ← bpDivModKProg (ctx, p)
    let P ← bpEffBlkProg (ctx, (dm.1, dm.2))
    let tag ← bpReadSlabOwnerProg (ctx, (P, 0))
    if tag = 1 then do
      let b ← bpReadSlabOwnerProg (ctx, (P, 1))
      let vp ← bpReadSlabOwnerProg (ctx, (P, 2))
      let loc ← bpBktLocProg (ctx, (vp, dm.2))
      pure (b, loc)
    else
      bpOwnerOfNonSlabProg (ctx, ((P, dm.2), tag))

@[simp] theorem runClient_state_bpOwnerOfProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (bpOwnerOfProg x)) = s := by
  rcases x with ⟨ctx, p⟩
  unfold bpOwnerOfProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpDivModKProg,
    runClient_state_bpEffBlkProg, runClient_state_bpReadSlabOwnerProg]
  split_ifs <;> simp

theorem clientState_bpOwnerOfProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpOwnerOfProg x) = s :=
  runClient_state_bpOwnerOfProg x s

theorem realizesBounded_bpOwnerOf :
    RealizesBounded .exact bpOwnerOfProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hdm := realizesBounded_bpDivModK
  have heb := realizesBounded_bpEffBlk
  have hrso := realizesBounded_bpReadSlabOwner
  have hbl := realizesBounded_bpBktLoc
  have hns := realizesBounded_bpOwnerOfNonSlab
  realize
  all_goals (
    rcases d with ⟨ctx, p⟩
    have hv0 := h
    have hpow : 4 < 2 ^ w := lt_of_le_of_lt
      (by have := hv0.K_ge; have := hv0.twelve_K_le; omega) hv0.nCap_lt_two_pow_w
    dsimp only [Fits] at *
    try simp only [runClient_state_bpDivModKProg, runClient_state_bpEffBlkProg,
      runClient_state_bpReadSlabOwnerProg] at *
    first | exact hv0 | omega)

theorem bpOwnerOfProg_frame (mp : BpMetaLayout) (p : ℕ) :
    BpMetaProg mp 24 (bpOwnerOfProg (mp.toCtx, p)) := by
  unfold bpOwnerOfProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpDivModKProg_frame mp p) fun dm =>
    BpMetaProg.bind_prog (bpEffBlkProg_frame mp dm.1 dm.2) fun P =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 0) fun tag =>
    BpMetaProg.ite_prog (tag = 1)
      (fun _ => (BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 1) fun b =>
          BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 2) fun vp =>
          BpMetaProg.bind_prog (bpBktLocProg_frame mp vp dm.2) fun loc =>
          BpMetaProg.pure_prog (b, loc)).mono (C₂ := 16) (by decide))
      (fun _ => bpOwnerOfNonSlabProg_frame mp P dm.2 tag)
  exact hf.mono (by decide)

theorem bpOwnerOfProg_spec {mp : BpMetaLayout} {p : ℕ} {s : Memory.State}
    (hv : (extractBlockPool mp s.mem).CoreValid) (hp : p < (extractBlockPool mp s.mem).nSide) :
    (Memory.spec 0).clientResult s (bpOwnerOfProg (mp.toCtx, p)) =
      (extractBlockPool mp s.mem).ownerOf p := by
  set bp := extractBlockPool mp s.mem
  have hK : 0 < mp.K := hv.K_pos
  have hoff : p % mp.K < mp.K := Nat.mod_lt p hK
  have hn_eq : bp.B_full * mp.K + bp.rem = bp.nSide := hv.nSide_eq
  have hP_or : p / mp.K < bp.B_full ∨ (p / mp.K = bp.B_full ∧ p % mp.K < bp.rem) := by
    by_cases hlt : p / mp.K < bp.B_full
    · exact Or.inl hlt
    · have hle : p / mp.K ≤ bp.B_full := Nat.div_le_div_right hp.le
      have heq : p / mp.K = bp.B_full := by omega
      have hp_dm := Nat.div_add_mod p mp.K
      rw [heq, Nat.mul_comm] at hp_dm
      exact Or.inr ⟨heq, by omega⟩
  set P := bp.effBlk (p / mp.K) (p % mp.K)
  have hP_lt_or : P < bp.B_full ∨ (P = bp.B_full ∧ p % mp.K < bp.rem) := by
    rcases hP_or with hlt | ⟨heq, hrem⟩
    · exact Or.inl (hv.effBlk_lt_B_full hlt _)
    · dsimp only [P]; rw [heq, hv.effBlk_B_full]; exact Or.inr ⟨rfl, hrem⟩
  unfold bpOwnerOfProg BlockPoolState.ownerOf
  rw [StateTransitionSpec.clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK,
    StateTransitionSpec.clientResult_bind, clientState_bpEffBlkProg, bpEffBlkProg_spec,
    StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
    clientResult_bpReadSlabOwner_tag]
  dsimp only
  have hK_eq : bp.K = mp.K := rfl
  have hP_def : bp.effBlk (p / bp.K) (p % bp.K) = P := rfl
  by_cases ht1 : bp.blkTag P = 1
  · have ht1' : (extractBlockPool mp s.mem).blkTag
        ((extractBlockPool mp s.mem).effBlk (p / mp.K) (p % mp.K)) = 1 := ht1
    have ht1'' : bp.blkTag (bp.effBlk (p / bp.K) (p % bp.K)) = 1 := ht1
    rw [ite_eq_left ht1', ite_eq_left ht1'']
    have hP_lt : P < bp.B_full := by
      rcases hP_lt_or with h1 | ⟨hP_eq, _⟩
      · exact h1
      · rw [hP_eq, hv.blkTag_top] at ht1; exact absurd ht1 (by decide)
    obtain ⟨hb_P, hvp_P, _⟩ := hv.slab_bwd P hP_lt ht1
    have hvp_le : bp.blkMeta2 P ≤ mp.maxSlabs :=
      hvp_P.le.trans (hv.bkt_bounds _ hb_P).1
    rw [StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_m1, StateTransitionSpec.clientResult_bind,
      clientState_bpReadSlabOwnerProg, clientResult_bpReadSlabOwner_m2,
      StateTransitionSpec.clientResult_bind, clientState_bpBktLocProg,
      clientResult_bpBktLoc hvp_le (hoff.le.trans (by omega)) s]
    rfl
  · have ht1' : (extractBlockPool mp s.mem).blkTag
        ((extractBlockPool mp s.mem).effBlk (p / mp.K) (p % mp.K)) ≠ 1 := ht1
    have ht1'' : bp.blkTag (bp.effBlk (p / bp.K) (p % bp.K)) ≠ 1 := ht1
    rw [ite_eq_right ht1', ite_eq_right ht1'']
    unfold bpOwnerOfNonSlabProg; dsimp only
    by_cases ht2 : bp.blkTag P = 2
    · have ht2' : (extractBlockPool mp s.mem).blkTag
          ((extractBlockPool mp s.mem).effBlk (p / mp.K) (p % mp.K)) = 2 := ht2
      have ht2'' : bp.blkTag (bp.effBlk (p / bp.K) (p % bp.K)) = 2 := ht2
      rw [ite_eq_left ht2', ite_eq_left ht2'']
      have hP_lt : P < bp.B_full := by
        rcases hP_lt_or with h1 | ⟨hP_eq, _⟩
        · exact h1
        · rw [hP_eq, hv.blkTag_top] at ht2; exact absurd ht2 (by decide)
      obtain ⟨hb_P, _, _⟩ := hv.act_bwd P hP_lt ht2
      rw [StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m1, StateTransitionSpec.clientResult_bind,
        clientState_bpActCurProg, bpActCurProg_spec]
      by_cases hact : p % mp.K < bp.actCur (bp.blkMeta1 P)
      · have hact' : p % mp.K < (extractBlockPool mp s.mem).actCur
            ((extractBlockPool mp s.mem).blkMeta1
              ((extractBlockPool mp s.mem).effBlk (p / mp.K) (p % mp.K))) := hact
        have hact'' : p % bp.K < bp.actCur (bp.blkMeta1 (bp.effBlk (p / bp.K) (p % bp.K))) := hact
        rw [ite_eq_left hact', ite_eq_left hact'']
        have hq_le := (hv.bkt_bounds _ hb_P).1
        rw [StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
          clientResult_bpReadBktMeta_q, StateTransitionSpec.clientResult_bind,
          clientState_bpBktLocProg, clientResult_bpBktLoc hq_le (hoff.le.trans (by omega)) s]
        rfl
      · have hact' : ¬(p % mp.K < (extractBlockPool mp s.mem).actCur
            ((extractBlockPool mp s.mem).blkMeta1
              ((extractBlockPool mp s.mem).effBlk (p / mp.K) (p % mp.K)))) := hact
        have hact'' : ¬(p % bp.K < bp.actCur (bp.blkMeta1 (bp.effBlk (p / bp.K) (p % bp.K)))) :=
          hact
        rw [ite_eq_right hact', ite_eq_right hact'']
        obtain ⟨htb_lt, _⟩ := hv.tb_fwd P hP_lt.le (Or.inr ht2)
        have htb_8M : bp.blkMeta2 P < 8 * mp.M := htb_lt.trans_le hv.tbHighWater_le_max
        obtain ⟨hbo, hrko, _, _, _⟩ := hv.tail_bwd P hP_lt.le (p % mp.K) hoff (Or.inl hP_lt)
          (Or.inr ⟨ht2, Nat.le_of_not_lt hact⟩)
        rw [StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
          clientResult_bpReadSlabOwner_m2, StateTransitionSpec.clientResult_bind,
          clientState_bpTbSlotProg, clientResult_bpTbSlot htb_8M hoff s]
        exact bpOwnerOfTailProg_spec hv hbo hrko
    · have ht2' : (extractBlockPool mp s.mem).blkTag
          ((extractBlockPool mp s.mem).effBlk (p / mp.K) (p % mp.K)) ≠ 2 := ht2
      have ht2'' : bp.blkTag (bp.effBlk (p / bp.K) (p % bp.K)) ≠ 2 := ht2
      rw [ite_eq_right ht2', ite_eq_right ht2'']
      have ht0 : bp.blkTag P = 0 := by
        rcases hP_lt_or with h1 | ⟨hP_eq, _⟩
        · have := hv.blkTag_lt P h1; omega
        · rw [hP_eq]; exact hv.blkTag_top
      have hP_le : P ≤ bp.B_full := by
        rcases hP_lt_or with h1 | ⟨hP_eq, _⟩ <;> omega
      obtain ⟨htb_lt, _⟩ := hv.tb_fwd P hP_le (Or.inl ht0)
      have htb_8M : bp.blkMeta2 P < 8 * mp.M := htb_lt.trans_le hv.tbHighWater_le_max
      obtain ⟨hbo, hrko, _, _, _⟩ := hv.tail_bwd P hP_le (p % mp.K) hoff
        (hP_lt_or.imp id And.right) (Or.inl ht0)
      rw [StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m2, StateTransitionSpec.clientResult_bind,
        clientState_bpTbSlotProg, clientResult_bpTbSlot htb_8M hoff s]
      exact bpOwnerOfTailProg_spec hv hbo hrko

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

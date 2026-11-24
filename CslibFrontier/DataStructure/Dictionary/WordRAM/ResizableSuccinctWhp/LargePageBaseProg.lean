/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.PageUnperm
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.Params
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SplitPairProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bit-Packed `PageArenaLayout` Initialization and Virtual Read/Write (`LargePageBaseProg`)

This module couples `PageUnpermState` (`Cslib.DataStructure.WordRAM.Resizable.Randomized`) to words
`[metaBase + 18, metaBase + 32)` and `[metaBase + offPageDir, metaBase + offEpochEnd)` of the
hosting large epoch (`N_pg = max N_src N_dst ≥ whpThreshold c`) for the deamortized worst-case WHP
resizable succinct dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]), certifying parameter-free (`¬ReadsWidth`)
`RealizesBounded .exact` `Memory.Prog` primitives for Phase-1 incremental initialization and `O(1)`
virtual-to-physical translation, read, and write.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.PageArenaLayout`,
  `epochPageArenaLayout`, `PageArenaCtx`, `extractPagePair`, `extractPageUnperm`, `arenaPairAt`:
  named memory layout, tuple context, and pure arena extractors.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.pageInitScalarsProg`,
  `pageInitDirBatchProg`, `pageInitTailBatchProg`: Phase-1 incremental initialization primitives.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.pageToPhysBoundedProg`,
  `pageReadVirtBoundedProg`, `pageWriteVirtBoundedProg`: `O(1)` virtual-to-physical translation and
  virtual slot read/write primitives.

## Main results

* `valid_epochPageArenaLayout`, `valid_extractPageUnperm_of_init`: layout validity and Phase-1
  initialization transfer theorem.
* `realizesBounded_pageToPhys`, `pageToPhysBoundedProg_spec`, `realizesBounded_pageReadVirt`,
  `pageReadVirtBoundedProg_spec`, `realizesBounded_pageWriteVirt`, `pageWriteVirtBoundedProg_spec`:
  `RealizesBounded .exact` certificates (`¬ReadsWidth`) and exact `InvWithSlack` refinement.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
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
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 2: Bit-Packed `PageArenaLayout` and `RealizesBounded .exact` Operations -/

/-- Named address, bit-width, and capacity descriptor coupling `PageUnpermState` to words
`[metaBase + 18, metaBase + 32)`, `[metaBase + offDir, metaBase + offTail)`,
`[metaBase + offTail, metaBase + offEpochEnd)`, and physical pair arena `itemBase`
(`0` projection chains). -/
structure PageArenaLayout where
  /-- Epoch metadata base word (`scalars` live at `metaBase + 18 .. metaBase + 31`). -/
  metaBase : ℕ
  /-- Relative word offset of `offPageDir` (`4 * maxPages` entries of `ptrB` bits). -/
  offDir : ℕ
  /-- Relative word offset of `offPageTail` (`16 * pgB` entries of `ptrB` bits). -/
  offTail : ℕ
  /-- Entry bit-width `globalPtrBits N_pg ≤ w`. -/
  ptrB : ℕ
  /-- Machine word width `w`. -/
  w : ℕ
  /-- Page size `pageSizeWhp N_pg` (`32 ≤ pgB`). -/
  pgB : ℕ
  /-- Directory page capacity `N_pg / pgB + 4` (`4 ≤ maxPages`). -/
  maxPages : ℕ
  /-- Base word of the shared `1 · OPT` physical `(qBits, vBits)` pair stream. -/
  itemBase : ℕ
  /-- Quotient bit-width `qBits ≤ w` of the shared pair stream. -/
  qBits : ℕ
  /-- Value bit-width `vBits ≤ w` (`V ≤ 2 ^ w`). -/
  vBits : ℕ
  /-- Current physical pair capacity `nCap` (`itemBase + pairStreamWords nCap ... ≤ frontier`). -/
  nCap : ℕ

/-- Canonical `PageArenaLayout` hosted in epoch `N` (`whpThreshold c ≤ N`). -/
@[expose] def epochPageArenaLayout (c w N metaBase itemBase qBits vBits nCap : ℕ) :
    PageArenaLayout where
  metaBase := metaBase
  offDir := offPageDir c w N
  offTail := offPageTail c w N
  ptrB := globalPtrBits N
  w := w
  pgB := pageSizeWhp N
  maxPages := N / pageSizeWhp N + 4
  itemBase := itemBase
  qBits := qBits
  vBits := vBits
  nCap := nCap

/-- Tuple encoding of `PageArenaLayout` for `RealizesBounded` `Memory.Prog` primitives. -/
abbrev PageArenaCtx :=
  (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) × ((ℕ × ℕ) × ℕ)

/-- Pack `PageArenaLayout` into `PageArenaCtx`. -/
abbrev PageArenaLayout.toCtx (L : PageArenaLayout) : PageArenaCtx :=
  ((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB), (L.maxPages, L.itemBase))),
    ((L.qBits, L.vBits), L.nCap))

/-- Unpack `PageArenaCtx` into `PageArenaLayout`. -/
abbrev PageArenaLayout.ofCtx : PageArenaCtx → PageArenaLayout
  | ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)) =>
    ⟨mb, od, ot, pb, wv, pg, mp, ib, qb, vb, nc⟩

@[simp] theorem PageArenaLayout.ofCtx_toCtx (L : PageArenaLayout) :
    PageArenaLayout.ofCtx L.toCtx = L := by
  cases L; rfl

/-- Metadata word-interval predicate owned by `PageUnpermState` inside `L`. -/
@[expose] def PageArenaLayout.OwnsMetaAddr (L : PageArenaLayout) (addr : ℕ) : Prop :=
  (L.metaBase + 18 ≤ addr ∧ addr < L.metaBase + 32) ∨
  (L.metaBase + L.offDir ≤ addr ∧
    addr < L.metaBase + L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w) ∨
  (L.metaBase + L.offTail ≤ addr ∧
    addr < L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w)

/-- Physical pair-stream word-interval predicate for `[0, L.nCap)` at `L.itemBase`. -/
@[expose] def PageArenaLayout.OwnsItemAddr (L : PageArenaLayout) (addr : ℕ) : Prop :=
  L.itemBase ≤ addr ∧ addr < L.itemBase + pairStreamWords L.nCap L.qBits L.vBits L.w

/-- Frontier-only static validity predicate for `PageArenaLayout` (independent of `s.mem`). -/
@[expose] def PageArenaLayout.Valid (L : PageArenaLayout) (w_mach frontier : ℕ) : Prop :=
  0 < w_mach ∧ w_mach = L.w ∧ L.ptrB ≤ w_mach ∧ L.qBits ≤ w_mach ∧ L.vBits ≤ w_mach ∧
  32 ≤ L.pgB ∧ 16 * L.pgB < 2 ^ L.ptrB ∧ 4 ≤ L.maxPages ∧ 4 * L.maxPages < 2 ^ L.ptrB ∧
  L.nCap ≤ (L.maxPages - 2) * L.pgB ∧ L.nCap < 2 ^ w_mach ∧
  32 ≤ L.offDir ∧
  L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail ∧
  L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase ∧
  L.itemBase + pairStreamWords L.nCap L.qBits L.vBits L.w ≤ frontier

/-- `epochPageArenaLayout` satisfies `PageArenaLayout.Valid` whenever `whpThreshold c ≤ N ≤ U`,
`Fits w U`, `nCap ≤ N + 1`, and `Fits w nCap`. -/
theorem valid_epochPageArenaLayout {c U w N metaBase itemBase qBits vBits nCap frontier : ℕ}
    (hth : whpThreshold c ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hq : qBits ≤ w) (hv : vBits ≤ w) (hnc_N : nCap ≤ N + 1) (hnc_w : Fits w nCap)
    (hmeta_ib : metaBase + epochMetaWordsWhp c w N ≤ itemBase)
    (hib_fr : itemBase + pairStreamWords nCap qBits vBits w ≤ frontier) :
    (epochPageArenaLayout c w N metaBase itemBase qBits vBits nCap).Valid w frontier := by
  obtain ⟨hptr_lt, hptr_w, hlog_w, _, _, _, _, _, _, _, _, _, _, _, _,
    hpg16, hmp4, _, _, _⟩ := largeEpoch_param_bounds hth hNU hU
  have hw_pos : 0 < w := by omega
  have hpg32 : 32 ≤ pageSizeWhp N := le_max_left 32 _
  have hdiv_mod := Nat.div_add_mod N (pageSizeWhp N)
  have hmod_lt : N % pageSizeWhp N < pageSizeWhp N := Nat.mod_lt N (by omega)
  have hnc_mp : nCap ≤ (N / pageSizeWhp N + 4 - 2) * pageSizeWhp N := by
    rw [Nat.add_sub_assoc (by decide : 2 ≤ 4)]
    change nCap ≤ (N / pageSizeWhp N + 2) * pageSizeWhp N
    have h1 : (N / pageSizeWhp N + 2) * pageSizeWhp N =
        pageSizeWhp N * (N / pageSizeWhp N) + 2 * pageSizeWhp N := by ring
    omega
  have hoff32 : 32 ≤ offPageDir c w N := by
    unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
      offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash offBktHash
    omega
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
  unfold PageArenaLayout.Valid
  dsimp only [epochPageArenaLayout]
  refine ⟨hw_pos, rfl, hptr_w, hq, hv, hpg32, lt_of_le_of_lt hpg16 hptr_lt,
    Nat.le_add_left 4 _, lt_of_le_of_lt hmp4 hptr_lt, hnc_mp, hnc_w, hoff32,
    by unfold offPageTail; omega, ?_, hib_fr⟩
  unfold offEpochEnd at hend
  omega

/-- Decode `(jobKind, jobSide, jobCur)` words into `PageJob`. -/
@[expose] def decodePageJob (kind sideNat cur : ℕ) : PageJob :=
  let s := decide (sideNat ≠ 0)
  if kind = 1 then .promote s cur
  else if kind = 2 then .demoteSwap s cur
  else if kind = 3 then .demoteBuild s cur
  else .idle

/-- Encode the variant tag (`0..3`) of `PageJob`. -/
def encodePageJobKind : PageJob → ℕ
  | .idle => 0
  | .promote _ _ => 1
  | .demoteSwap _ _ => 2
  | .demoteBuild _ _ => 3

/-- Encode the active virtual side bit (`0` or `1`) of `PageJob`. -/
def encodePageJobSide : PageJob → ℕ
  | .idle => 0
  | .promote s _ | .demoteSwap s _ | .demoteBuild s _ => if s then 1 else 0

/-- Encode the intra-page progress cursor of `PageJob`. -/
def encodePageJobCur : PageJob → ℕ
  | .idle => 0
  | .promote _ cur | .demoteSwap _ cur | .demoteBuild _ cur => cur

/-- Encode `PageJob` into canonical `(jobKind, (jobSide, jobCur))` words (`0` projection chains). -/
def encodePageJob (j : PageJob) : ℕ × (ℕ × ℕ) :=
  (encodePageJobKind j, (encodePageJobSide j, encodePageJobCur j))

@[simp] theorem decodePageJob_encodePageJob (j : PageJob) :
    decodePageJob (encodePageJobKind j) (encodePageJobSide j) (encodePageJobCur j) = j := by
  cases j with
  | idle => rfl
  | promote s _ | demoteSwap s _ | demoteBuild s _ => cases s <;> rfl

theorem swapTailSlots_meta_eq (st : PagePairState) (p₁ p₂ : ℕ) :
    (st.swapTailSlots p₁ p₂).1.pageSize = st.pageSize ∧
    (st.swapTailSlots p₁ p₂).1.fullPages = st.fullPages ∧
    (st.swapTailSlots p₁ p₂).1.tailCount = st.tailCount ∧
    (st.swapTailSlots p₁ p₂).1.tailHead = st.tailHead := by
  unfold PagePairState.swapTailSlots
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Extract `PagePairState` from memory words according to `L`. -/
@[expose] def extractPagePair (L : PageArenaLayout) (mem : ℕ → ℕ) : PagePairState where
  pageSize := mem (L.metaBase + 20)
  fullPages := fun side => if side then mem (L.metaBase + 22) else mem (L.metaBase + 21)
  tailCount := fun side => if side then mem (L.metaBase + 24) else mem (L.metaBase + 23)
  tailHead := fun side => if side then mem (L.metaBase + 26) else mem (L.metaBase + 25)
  pageOf := fun side vp =>
    if vp < L.maxPages then
      readPacked (L.metaBase + L.offDir) L.ptrB L.w mem
        (4 * vp + Bool.rec 0 1 side)
    else 0
  ownerSide := fun P =>
    if P < L.maxPages then
      decide (readPacked (L.metaBase + L.offDir) L.ptrB L.w mem (4 * P + 2) ≠ 0)
    else false
  ownerVp := fun P =>
    if P < L.maxPages then
      readPacked (L.metaBase + L.offDir) L.ptrB L.w mem (4 * P + 3)
    else 0
  tailRes := fun side k =>
    if k < 4 * L.pgB then
      readPacked (L.metaBase + L.offTail) L.ptrB L.w mem
        (4 * L.pgB * Bool.rec 0 1 side + k)
    else 0
  tailOwnerSide := fun res =>
    if res < 8 * L.pgB then
      decide (readPacked (L.metaBase + L.offTail) L.ptrB L.w mem (8 * L.pgB + res) % 2 = 1)
    else false
  tailOwnerRing := fun res =>
    if res < 8 * L.pgB then
      readPacked (L.metaBase + L.offTail) L.ptrB L.w mem (8 * L.pgB + res) / 2
    else 0
  job := decodePageJob (mem (L.metaBase + 27)) (mem (L.metaBase + 28)) (mem (L.metaBase + 29))

/-- Extract `PageUnpermState` from memory words according to `L`. -/
@[expose] def extractPageUnperm (L : PageArenaLayout) (mem : ℕ → ℕ) : PageUnpermState where
  st := extractPagePair L mem
  cleanPhase := mem (L.metaBase + 18)
  cleanVp := mem (L.metaBase + 19)
  cleanOff := mem (L.metaBase + 30)

/-- Read physical pair `(q, v)` at slot `p` in `L`'s shared item stream. -/
@[expose] def arenaPairAt (L : PageArenaLayout) (mem : ℕ → ℕ) (p : ℕ) : ℕ × ℕ :=
  (pairQuotAt L.itemBase L.qBits L.vBits L.w mem p,
   pairValAt L.itemBase L.qBits L.vBits L.w mem p)

/-- Frame theorem: `extractPageUnperm L` depends only on `L.OwnsMetaAddr`. -/
theorem extractPageUnperm_congr {L : PageArenaLayout} {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < L.w)
    (heq : ∀ addr, L.OwnsMetaAddr addr → mem₁ addr = mem₂ addr) :
    extractPageUnperm L mem₁ = extractPageUnperm L mem₂ := by
  have hs : ∀ k, 18 ≤ k → k < 32 → mem₁ (L.metaBase + k) = mem₂ (L.metaBase + k) :=
    fun k hlo hhi => heq (L.metaBase + k) (Or.inl ⟨by omega, by omega⟩)
  have hd : ∀ idx < 4 * L.maxPages,
      readPacked (L.metaBase + L.offDir) L.ptrB L.w mem₁ idx =
        readPacked (L.metaBase + L.offDir) L.ptrB L.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun addr ha => heq addr (Or.inr (Or.inl ha))) hidx
  have ht : ∀ idx < 16 * L.pgB,
      readPacked (L.metaBase + L.offTail) L.ptrB L.w mem₁ idx =
        readPacked (L.metaBase + L.offTail) L.ptrB L.w mem₂ idx := fun idx hidx =>
    readPacked_congr hw (fun addr ha => heq addr (Or.inr (Or.inr ha))) hidx
  unfold extractPageUnperm extractPagePair
  congr 1
  · congr 1
    · exact hs 20 (by decide) (by decide)
    · ext side; cases side <;> [exact hs 21 (by decide) (by decide);
        exact hs 22 (by decide) (by decide)]
    · ext side; cases side <;> [exact hs 23 (by decide) (by decide);
        exact hs 24 (by decide) (by decide)]
    · ext side; cases side <;> [exact hs 25 (by decide) (by decide);
        exact hs 26 (by decide) (by decide)]
    · ext side vp; split_ifs with hvp
      · cases side <;> (dsimp only; exact hd _ (by omega))
      · rfl
    · ext P; split_ifs with hP
      · rw [hd (4 * P + 2) (by omega)]
      · rfl
    · ext P; split_ifs with hP
      · exact hd (4 * P + 3) (by omega)
      · rfl
    · ext side k; split_ifs with hk
      · cases side <;> (dsimp only; exact ht _ (by omega))
      · rfl
    · ext res; split_ifs with hr
      · rw [ht (8 * L.pgB + res) (by omega)]
      · rfl
    · ext res; split_ifs with hr
      · rw [ht (8 * L.pgB + res) (by omega)]
      · rfl
    · rw [hs 27 (by decide) (by decide), hs 28 (by decide) (by decide),
        hs 29 (by decide) (by decide)]
  · exact hs 18 (by decide) (by decide)
  · exact hs 19 (by decide) (by decide)
  · exact hs 30 (by decide) (by decide)

/-- Frame theorem: for `p < L.nCap`, `arenaPairAt L mem p` depends only on `L.OwnsItemAddr`. -/
theorem arenaPairAt_congr {L : PageArenaLayout} {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < L.w)
    (heq : ∀ addr, L.OwnsItemAddr addr → mem₁ addr = mem₂ addr) {p : ℕ} (hp : p < L.nCap) :
    arenaPairAt L mem₁ p = arenaPairAt L mem₂ p := by
  have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := L.qBits) (v_bits := L.vBits) hw hp
  have hle := wOffQ_le_wOffV L.qBits L.vBits L.w p
  unfold arenaPairAt pairQuotAt pairValAt readBitSlice
  dsimp only
  rw [heq _ ⟨by omega, by omega⟩, heq _ ⟨by omega, by omega⟩,
    heq _ ⟨by omega, by omega⟩, heq _ ⟨by omega, by omega⟩]

/-- Any write strictly below `L.itemBase` leaves `arenaPairAt L` unchanged for all `p`. -/
theorem arenaPairAt_of_lt_itemBase {L : PageArenaLayout} {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ addr, L.itemBase ≤ addr → mem₁ addr = mem₂ addr) :
    arenaPairAt L mem₁ = arenaPairAt L mem₂ := by
  ext p : 1
  unfold arenaPairAt pairQuotAt pairValAt readBitSlice
  dsimp only
  rw [heq _ (by omega), heq _ (by omega), heq _ (by omega), heq _ (by omega)]

/-- `writePair` at `L.itemBase` preserves `extractPageUnperm L` whenever `L` separates metadata
below `L.itemBase`. -/
theorem extractPageUnperm_writePair {L : PageArenaLayout} (hw : 0 < L.w)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (mem : ℕ → ℕ) (d q v : ℕ) :
    extractPageUnperm L (writePair L.itemBase L.qBits L.vBits L.w mem d q v) =
      extractPageUnperm L mem := by
  refine extractPageUnperm_congr hw (fun addr ha => ?_)
  have hlt_ib : addr < L.itemBase := by
    rcases ha with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩ <;> omega
  exact writePair_ne_of_lt mem (by omega) (wOffQ_le_wOffV L.qBits L.vBits L.w d)

/-- `swapPairGenProg` at `L.itemBase` preserves `extractPageUnperm L` and applies `PhysSwap` to
`arenaPairAt L`. -/
theorem swapPairGenProg_arena_eq {L : PageArenaLayout} (hw : 0 < L.w)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (s : Memory.State) (p₁ p₂ : ℕ) :
    let m' := ((Memory.spec 0).clientState s
      (swapPairGenProg (((L.itemBase, (L.qBits, L.vBits)), L.w), (p₁, p₂)))).mem
    extractPageUnperm L m' = extractPageUnperm L s.mem ∧
    arenaPairAt L m' = (PhysSwap.mk p₁ p₂).apply (arenaPairAt L s.mem) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · unfold swapPairGenProg; dsimp only
    split_ifs with heq
    · rfl
    · unfold StateTransitionSpec.clientState
      simp only [prog_runClient_state_bind, clientResult_readPairGenProg,
        runClient_state_readPairGenProg, runClient_state_writePairGenProg]
      rw [extractPageUnperm_writePair hw hm_ib ho1 ho2,
        extractPageUnperm_writePair hw hm_ib ho1 ho2]
  · ext d : 1
    exact swapPairGenProg_pair_eq hw s d

/-! ### Elementary Field-Update Lemmas on `extractPagePair` and `extractPageUnperm` -/

theorem writePacked_dir_preserves_other {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) {idx : ℕ} (hidx : idx < 4 * L.maxPages) (val : ℕ) :
    let m' := writePacked (L.metaBase + L.offDir) L.ptrB L.w mem idx val
    (∀ k < 32, m' (L.metaBase + k) = mem (L.metaBase + k)) ∧
    (∀ t < 16 * L.pgB,
      readPacked (L.metaBase + L.offTail) L.ptrB L.w m' t =
        readPacked (L.metaBase + L.offTail) L.ptrB L.w mem t) ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  set m' := writePacked (L.metaBase + L.offDir) L.ptrB L.w mem idx val
  have hout : ∀ addr, ¬(L.metaBase + L.offDir ≤ addr ∧
      addr < L.metaBase + L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w) →
      m' addr = mem addr := fun addr ha => writePacked_outside hw mem hidx val ha
  refine ⟨fun k hk => hout _ (by omega),
    fun t ht => readPacked_congr hw (fun addr ha => hout addr (by omega)) ht,
    arenaPairAt_of_lt_itemBase (fun addr ha => hout addr (by omega))⟩

theorem writePacked_tail_preserves_other {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) {idx : ℕ} (hidx : idx < 16 * L.pgB) (val : ℕ) :
    let m' := writePacked (L.metaBase + L.offTail) L.ptrB L.w mem idx val
    (∀ k < 32, m' (L.metaBase + k) = mem (L.metaBase + k)) ∧
    (∀ d < 4 * L.maxPages,
      readPacked (L.metaBase + L.offDir) L.ptrB L.w m' d =
        readPacked (L.metaBase + L.offDir) L.ptrB L.w mem d) ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  set m' := writePacked (L.metaBase + L.offTail) L.ptrB L.w mem idx val
  have hout : ∀ addr, ¬(L.metaBase + L.offTail ≤ addr ∧
      addr < L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w) →
      m' addr = mem addr := fun addr ha => writePacked_outside hw mem hidx val ha
  refine ⟨fun k hk => hout _ (by omega),
    fun d hd => readPacked_congr hw (fun addr ha => hout addr (by omega)) hd,
    arenaPairAt_of_lt_itemBase (fun addr ha => hout addr (by omega))⟩

theorem extractPageUnperm_writePageOf {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) (side : Bool) {vp val : ℕ} (hvp : vp < L.maxPages) (hval : val < 2 ^ L.ptrB) :
    let idx := 4 * vp + if side then 1 else 0
    let m' := writePacked (L.metaBase + L.offDir) L.ptrB L.w mem idx val
    let u := extractPageUnperm L mem
    extractPageUnperm L m' =
      { u with st := { u.st with pageOf := PagePairState.set2 u.st.pageOf side vp val } } ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  set idx := 4 * vp + if side then 1 else 0
  have hidx_m : idx = 4 * vp + Bool.rec 0 1 side := by
    dsimp only [idx]; cases side <;> rfl
  have hidx : idx < 4 * L.maxPages := by rw [hidx_m]; cases side <;> dsimp only <;> omega
  obtain ⟨hsc, htl, har⟩ := writePacked_dir_preserves_other hw ho1 ho2 hm_ib mem hidx val
  refine ⟨?_, har⟩
  unfold extractPageUnperm extractPagePair; dsimp only
  congr 1
  · congr 1
    · exact hsc 20 (by decide)
    · ext s; cases s <;> [exact hsc 21 (by decide); exact hsc 22 (by decide)]
    · ext s; cases s <;> [exact hsc 23 (by decide); exact hsc 24 (by decide)]
    · ext s; cases s <;> [exact hsc 25 (by decide); exact hsc 26 (by decide)]
    · ext s' vp'
      by_cases heq : s' = side ∧ vp' = vp
      · obtain ⟨rfl, rfl⟩ := heq
        simp only [hvp, ↓reduceIte, PagePairState.set2_self, ← hidx_m]
        exact readPacked_writePacked_self _ _ _ mem idx hval
      · rw [PagePairState.set2_of_ne _ _ _ _ _ _ heq]
        split_ifs with hvp'
        · refine readPacked_writePacked_of_ne hw mem ?_ val
          rw [hidx_m]
          cases s' <;> cases side <;> simp at heq ⊢ <;> omega
        · rfl
    · ext P; split_ifs with hP
      · rw [readPacked_writePacked_of_ne hw mem
          (by rw [hidx_m]; cases side <;> dsimp only <;> omega) val]
      · rfl
    · ext P; split_ifs with hP
      · exact readPacked_writePacked_of_ne hw mem
          (by rw [hidx_m]; cases side <;> dsimp only <;> omega) val
      · rfl
    · ext s k; split_ifs with hk
      · cases s <;> (dsimp only; exact htl _ (by omega))
      · rfl
    · ext res; split_ifs with hr
      · rw [htl (8 * L.pgB + res) (by omega)]
      · rfl
    · ext res; split_ifs with hr
      · rw [htl (8 * L.pgB + res) (by omega)]
      · rfl
    · rw [hsc 27 (by decide), hsc 28 (by decide), hsc 29 (by decide)]
  · exact hsc 18 (by decide)
  · exact hsc 19 (by decide)
  · exact hsc 30 (by decide)

theorem extractPageUnperm_writeOwnerSide {L : PageArenaLayout} (hw : 0 < L.w)
    (hptr1 : 1 < 2 ^ L.ptrB) (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) {P : ℕ} (hP : P < L.maxPages) (side : Bool) :
    let val := if side then 1 else 0
    let m' := writePacked (L.metaBase + L.offDir) L.ptrB L.w mem (4 * P + 2) val
    let u := extractPageUnperm L mem
    extractPageUnperm L m' =
      { u with st := { u.st with ownerSide := Function.update u.st.ownerSide P side } } ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  set val := if side then 1 else 0
  have hval : val < 2 ^ L.ptrB := by
    dsimp only [val]; cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hidx : 4 * P + 2 < 4 * L.maxPages := by omega
  obtain ⟨hsc, htl, har⟩ := writePacked_dir_preserves_other hw ho1 ho2 hm_ib mem hidx val
  refine ⟨?_, har⟩
  unfold extractPageUnperm extractPagePair; dsimp only
  congr 1
  · congr 1
    · exact hsc 20 (by decide)
    · ext s; cases s <;> [exact hsc 21 (by decide); exact hsc 22 (by decide)]
    · ext s; cases s <;> [exact hsc 23 (by decide); exact hsc 24 (by decide)]
    · ext s; cases s <;> [exact hsc 25 (by decide); exact hsc 26 (by decide)]
    · ext s vp; split_ifs with hvp
      · exact readPacked_writePacked_of_ne hw mem (by cases s <;> dsimp only <;> omega) val
      · rfl
    · ext P'
      by_cases heq : P' = P
      · subst heq
        simp only [hP, ↓reduceIte, Function.update_self]
        rw [readPacked_writePacked_self _ _ _ mem (4 * P' + 2) hval]
        dsimp only [val]; cases side <;> rfl
      · rw [Function.update_of_ne heq]
        split_ifs with hP'
        · rw [readPacked_writePacked_of_ne hw mem (by omega) val]
        · rfl
    · ext P'; split_ifs with hP'
      · exact readPacked_writePacked_of_ne hw mem (by omega) val
      · rfl
    · ext s k; split_ifs with hk
      · cases s <;> (dsimp only; exact htl _ (by omega))
      · rfl
    · ext res; split_ifs with hr
      · rw [htl (8 * L.pgB + res) (by omega)]
      · rfl
    · ext res; split_ifs with hr
      · rw [htl (8 * L.pgB + res) (by omega)]
      · rfl
    · rw [hsc 27 (by decide), hsc 28 (by decide), hsc 29 (by decide)]
  · exact hsc 18 (by decide)
  · exact hsc 19 (by decide)
  · exact hsc 30 (by decide)

theorem extractPageUnperm_writeOwnerVp {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) {P vp : ℕ} (hP : P < L.maxPages) (hvp : vp < 2 ^ L.ptrB) :
    let m' := writePacked (L.metaBase + L.offDir) L.ptrB L.w mem (4 * P + 3) vp
    let u := extractPageUnperm L mem
    extractPageUnperm L m' =
      { u with st := { u.st with ownerVp := Function.update u.st.ownerVp P vp } } ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  have hidx : 4 * P + 3 < 4 * L.maxPages := by omega
  obtain ⟨hsc, htl, har⟩ := writePacked_dir_preserves_other hw ho1 ho2 hm_ib mem hidx vp
  refine ⟨?_, har⟩
  unfold extractPageUnperm extractPagePair; dsimp only
  congr 1
  · congr 1
    · exact hsc 20 (by decide)
    · ext s; cases s <;> [exact hsc 21 (by decide); exact hsc 22 (by decide)]
    · ext s; cases s <;> [exact hsc 23 (by decide); exact hsc 24 (by decide)]
    · ext s; cases s <;> [exact hsc 25 (by decide); exact hsc 26 (by decide)]
    · ext s q; split_ifs with hq
      · exact readPacked_writePacked_of_ne hw mem (by cases s <;> dsimp only <;> omega) vp
      · rfl
    · ext P'; split_ifs with hP'
      · rw [readPacked_writePacked_of_ne hw mem (by omega) vp]
      · rfl
    · ext P'
      by_cases heq : P' = P
      · subst heq
        simp only [hP, ↓reduceIte, Function.update_self]
        exact readPacked_writePacked_self _ _ _ mem (4 * P' + 3) hvp
      · rw [Function.update_of_ne heq]
        split_ifs with hP'
        · exact readPacked_writePacked_of_ne hw mem (by omega) vp
        · rfl
    · ext s k; split_ifs with hk
      · cases s <;> (dsimp only; exact htl _ (by omega))
      · rfl
    · ext res; split_ifs with hr
      · rw [htl (8 * L.pgB + res) (by omega)]
      · rfl
    · ext res; split_ifs with hr
      · rw [htl (8 * L.pgB + res) (by omega)]
      · rfl
    · rw [hsc 27 (by decide), hsc 28 (by decide), hsc 29 (by decide)]
  · exact hsc 18 (by decide)
  · exact hsc 19 (by decide)
  · exact hsc 30 (by decide)

theorem extractPageUnperm_writeTailRes {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) (side : Bool) {k val : ℕ} (hk : k < 4 * L.pgB) (hval : val < 2 ^ L.ptrB) :
    let idx := (if side then 4 * L.pgB else 0) + k
    let m' := writePacked (L.metaBase + L.offTail) L.ptrB L.w mem idx val
    let u := extractPageUnperm L mem
    extractPageUnperm L m' =
      { u with st := { u.st with tailRes := PagePairState.set2 u.st.tailRes side k val } } ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  set idx := (if side then 4 * L.pgB else 0) + k
  have hidx_eq : idx = 4 * L.pgB * Bool.rec 0 1 side + k := by
    dsimp only [idx]; cases side <;> simp
  have hidx : idx < 16 * L.pgB := by rw [hidx_eq]; cases side <;> dsimp only <;> omega
  obtain ⟨hsc, hdir, har⟩ := writePacked_tail_preserves_other hw ho1 ho2 hm_ib mem hidx val
  refine ⟨?_, har⟩
  unfold extractPageUnperm extractPagePair; dsimp only
  congr 1
  · congr 1
    · exact hsc 20 (by decide)
    · ext s; cases s <;> [exact hsc 21 (by decide); exact hsc 22 (by decide)]
    · ext s; cases s <;> [exact hsc 23 (by decide); exact hsc 24 (by decide)]
    · ext s; cases s <;> [exact hsc 25 (by decide); exact hsc 26 (by decide)]
    · ext s vp; split_ifs with hvp
      · cases s <;> (dsimp only; exact hdir _ (by omega))
      · rfl
    · ext P; split_ifs with hP
      · rw [hdir (4 * P + 2) (by omega)]
      · rfl
    · ext P; split_ifs with hP
      · exact hdir (4 * P + 3) (by omega)
      · rfl
    · ext s' k'
      by_cases heq : s' = side ∧ k' = k
      · obtain ⟨rfl, rfl⟩ := heq
        simp only [hk, ↓reduceIte, PagePairState.set2_self]
        rw [← hidx_eq]
        exact readPacked_writePacked_self _ _ _ mem idx hval
      · rw [PagePairState.set2_of_ne _ _ _ _ _ _ heq]
        split_ifs with hk'
        · refine readPacked_writePacked_of_ne hw mem ?_ val
          rw [hidx_eq]
          cases s' <;> cases side <;> simp at heq ⊢ <;> omega
        · rfl
    · ext res; split_ifs with hr
      · rw [readPacked_writePacked_of_ne hw mem
          (by rw [hidx_eq]; cases side <;> dsimp only <;> omega) val]
      · rfl
    · ext res; split_ifs with hr
      · rw [readPacked_writePacked_of_ne hw mem
          (by rw [hidx_eq]; cases side <;> dsimp only <;> omega) val]
      · rfl
    · rw [hsc 27 (by decide), hsc 28 (by decide), hsc 29 (by decide)]
  · exact hsc 18 (by decide)
  · exact hsc 19 (by decide)
  · exact hsc 30 (by decide)

theorem extractPageUnperm_writeTailOwner {L : PageArenaLayout} (hw : 0 < L.w)
    (hpg16 : 16 * L.pgB < 2 ^ L.ptrB) (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) {res k : ℕ} (hr : res < 8 * L.pgB) (hk : k < 8 * L.pgB) (side : Bool) :
    let val := (if side then 1 else 0) + 2 * k
    let m' := writePacked (L.metaBase + L.offTail) L.ptrB L.w mem (8 * L.pgB + res) val
    let u := extractPageUnperm L mem
    extractPageUnperm L m' =
      { u with
        st :=
          { u.st with
            tailOwnerSide := Function.update u.st.tailOwnerSide res side
            tailOwnerRing := Function.update u.st.tailOwnerRing res k } } ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  set val := (if side then 1 else 0) + 2 * k
  have hval : val < 2 ^ L.ptrB := by dsimp only [val]; cases side <;> simp <;> omega
  have hidx : 8 * L.pgB + res < 16 * L.pgB := by omega
  obtain ⟨hsc, hdir, har⟩ := writePacked_tail_preserves_other hw ho1 ho2 hm_ib mem hidx val
  refine ⟨?_, har⟩
  unfold extractPageUnperm extractPagePair; dsimp only
  congr 1
  · congr 1
    · exact hsc 20 (by decide)
    · ext s; cases s <;> [exact hsc 21 (by decide); exact hsc 22 (by decide)]
    · ext s; cases s <;> [exact hsc 23 (by decide); exact hsc 24 (by decide)]
    · ext s; cases s <;> [exact hsc 25 (by decide); exact hsc 26 (by decide)]
    · ext s vp; split_ifs with hvp
      · cases s <;> (dsimp only; exact hdir _ (by omega))
      · rfl
    · ext P; split_ifs with hP
      · rw [hdir (4 * P + 2) (by omega)]
      · rfl
    · ext P; split_ifs with hP
      · exact hdir (4 * P + 3) (by omega)
      · rfl
    · ext s k'; split_ifs with hk'
      · exact readPacked_writePacked_of_ne hw mem (by cases s <;> dsimp only <;> omega) val
      · rfl
    · ext r'
      by_cases heq : r' = res
      · subst heq
        simp only [hr, ↓reduceIte, Function.update_self]
        rw [readPacked_writePacked_self _ _ _ mem (8 * L.pgB + r') hval]
        dsimp only [val]
        cases side <;>
          [simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_false_iff_not];
           simp only [↓reduceIte, decide_eq_true_eq]] <;> omega
      · rw [Function.update_of_ne heq]
        split_ifs with hr'
        · rw [readPacked_writePacked_of_ne hw mem (by omega) val]
        · rfl
    · ext r'
      by_cases heq : r' = res
      · subst heq
        simp only [hr, ↓reduceIte, Function.update_self]
        rw [readPacked_writePacked_self _ _ _ mem (8 * L.pgB + r') hval]
        dsimp only [val]
        cases side <;>
          [simp only [Bool.false_eq_true, ↓reduceIte]; simp only [↓reduceIte]] <;> omega
      · rw [Function.update_of_ne heq]
        split_ifs with hr'
        · rw [readPacked_writePacked_of_ne hw mem (by omega) val]
        · rfl
    · rw [hsc 27 (by decide), hsc 28 (by decide), hsc 29 (by decide)]
  · exact hsc 18 (by decide)
  · exact hsc 19 (by decide)
  · exact hsc 30 (by decide)

theorem scalar_update_preserves_packed {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) {off : ℕ} (hoff : off < 32) (val : ℕ) :
    let m' := Function.update mem (L.metaBase + off) val
    (∀ d < 4 * L.maxPages,
      readPacked (L.metaBase + L.offDir) L.ptrB L.w m' d =
        readPacked (L.metaBase + L.offDir) L.ptrB L.w mem d) ∧
    (∀ t < 16 * L.pgB,
      readPacked (L.metaBase + L.offTail) L.ptrB L.w m' t =
        readPacked (L.metaBase + L.offTail) L.ptrB L.w mem t) ∧
    arenaPairAt L m' = arenaPairAt L mem := by
  dsimp only
  refine ⟨fun d hd => readPacked_congr hw
      (fun addr ha => Function.update_of_ne (by omega : addr ≠ L.metaBase + off) val mem) hd,
    fun t ht => readPacked_congr hw
      (fun addr ha => Function.update_of_ne (by omega : addr ≠ L.metaBase + off) val mem) ht,
    arenaPairAt_of_lt_itemBase
      (fun addr ha => Function.update_of_ne (by omega : addr ≠ L.metaBase + off) val mem)⟩

/-! ### Guarded Low-Level `Memory.Prog` Sub-Primitives (`¬ReadsWidth`) -/

/-- Write `(jobKind, (jobSide, jobCur))` to scalar words `mb + 27 .. mb + 29`. -/
def pageWriteJobProg : ℕ × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (mb, (jk, (js, jc))) => do
    Memory.write (mb + 27) jk
    Memory.write (mb + 28) js
    Memory.write (mb + 29) jc

@[simp] theorem memoryCost_pageWriteJobProg
    (x : ℕ × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (pageWriteJobProg x) s = 3 := by
  rcases x with ⟨_, _, _, _⟩; simp [pageWriteJobProg]

@[simp] theorem runClient_frontier_pageWriteJobProg
    (x : ℕ × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageWriteJobProg x))).frontier =
      s.frontier := by
  rcases x with ⟨_, _, _, _⟩; simp [pageWriteJobProg]

theorem realizesBounded_pageWriteJob :
    RealizesBounded .exact pageWriteJobProg
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (mb, _) s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨mb, jk, js, jc⟩
    obtain ⟨hw32, hfr⟩ := h
    have := hmem.1
    dsimp only [Fits] at *
    omega)

theorem extractPageUnperm_pageWriteJobProg {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (s : Memory.State) (j : PageJob) :
    let m' := ((Memory.spec 0).clientState s
      (pageWriteJobProg (L.metaBase, encodePageJob j))).mem
    let u := extractPageUnperm L s.mem
    extractPageUnperm L m' = { u with st := { u.st with job := j } } ∧
    arenaPairAt L m' = arenaPairAt L s.mem := by
  dsimp only [encodePageJob]
  unfold pageWriteJobProg StateTransitionSpec.clientState
  simp only [prog_runClient_state_bind, prog_runClient_state_write]
  obtain ⟨hd1, ht1, ha1⟩ := scalar_update_preserves_packed hw ho1 ho2 hm_ib s.mem
    (by decide : 27 < 32) (encodePageJobKind j)
  obtain ⟨hd2, ht2, ha2⟩ := scalar_update_preserves_packed hw ho1 ho2 hm_ib _
    (by decide : 28 < 32) (encodePageJobSide j)
  obtain ⟨hd3, ht3, ha3⟩ := scalar_update_preserves_packed hw ho1 ho2 hm_ib _
    (by decide : 29 < 32) (encodePageJobCur j)
  refine ⟨?_, ha3.trans (ha2.trans ha1)⟩
  have hne : ∀ k < 27, Function.update (Function.update (Function.update s.mem (L.metaBase + 27)
      (encodePageJobKind j)) (L.metaBase + 28) (encodePageJobSide j))
      (L.metaBase + 29) (encodePageJobCur j) (L.metaBase + k) = s.mem (L.metaBase + k) :=
    fun k hk => by
      rw [Function.update_of_ne (by omega : L.metaBase + k ≠ L.metaBase + 29),
        Function.update_of_ne (by omega : L.metaBase + k ≠ L.metaBase + 28),
        Function.update_of_ne (by omega : L.metaBase + k ≠ L.metaBase + 27)]
  unfold extractPageUnperm extractPagePair; dsimp only
  congr 1
  · congr 1
    · exact hne 20 (by decide)
    · ext side; cases side <;> [exact hne 21 (by decide); exact hne 22 (by decide)]
    · ext side; cases side <;> [exact hne 23 (by decide); exact hne 24 (by decide)]
    · ext side; cases side <;> [exact hne 25 (by decide); exact hne 26 (by decide)]
    · ext side vp; split_ifs with hvp
      · cases side
        · dsimp only; exact (hd3 _ (by omega)).trans ((hd2 _ (by omega)).trans (hd1 _ (by omega)))
        · dsimp only; exact (hd3 _ (by omega)).trans ((hd2 _ (by omega)).trans (hd1 _ (by omega)))
      · rfl
    · ext P; split_ifs with hP
      · rw [hd3 _ (by omega), hd2 _ (by omega), hd1 _ (by omega)]
      · rfl
    · ext P; split_ifs with hP
      · exact (hd3 _ (by omega)).trans ((hd2 _ (by omega)).trans (hd1 _ (by omega)))
      · rfl
    · ext side k; split_ifs with hk
      · cases side
        · dsimp only; exact (ht3 _ (by omega)).trans ((ht2 _ (by omega)).trans (ht1 _ (by omega)))
        · dsimp only; exact (ht3 _ (by omega)).trans ((ht2 _ (by omega)).trans (ht1 _ (by omega)))
      · rfl
    · ext res; split_ifs with hr
      · rw [ht3 _ (by omega), ht2 _ (by omega), ht1 _ (by omega)]
      · rfl
    · ext res; split_ifs with hr
      · rw [ht3 _ (by omega), ht2 _ (by omega), ht1 _ (by omega)]
      · rfl
    · rw [Function.update_of_ne (by omega : L.metaBase + 27 ≠ L.metaBase + 29),
        Function.update_of_ne (by omega : L.metaBase + 27 ≠ L.metaBase + 28),
        Function.update_self,
        Function.update_of_ne (by omega : L.metaBase + 28 ≠ L.metaBase + 29),
        Function.update_self, Function.update_self, decodePageJob_encodePageJob]
  · exact hne 18 (by decide)
  · exact hne 19 (by decide)
  · rw [Function.update_of_ne (by omega : L.metaBase + 30 ≠ L.metaBase + 29),
      Function.update_of_ne (by omega : L.metaBase + 30 ≠ L.metaBase + 28),
      Function.update_of_ne (by omega : L.metaBase + 30 ≠ L.metaBase + 27)]

/-- Read `(fullPages false, fullPages true)` from scalar words `mb + 21` and `mb + 22`. -/
def pageReadFullPagesProg (mb : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let q0 ← Memory.read (mb + 21)
  let q1 ← Memory.read (mb + 22)
  pure (q0, q1)

@[simp] theorem runClient_state_pageReadFullPagesProg (mb : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadFullPagesProg mb)) = s := by
  simp [pageReadFullPagesProg]

@[simp] theorem memoryCost_pageReadFullPagesProg (mb : ℕ) (s : Memory.State) :
    memoryCost (pageReadFullPagesProg mb) s = 2 := by
  simp [pageReadFullPagesProg]

theorem realizesBounded_pageReadFullPages :
    RealizesBounded .exact pageReadFullPagesProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w mb s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    obtain ⟨hw32, hfr⟩ := h
    have := hmem.1
    have := hmem.2 (d + 21)
    have := hmem.2 (d + 22)
    dsimp only [Fits] at *
    omega)

theorem pageReadFullPagesProg_eq (L : PageArenaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pageReadFullPagesProg L.metaBase) =
      ((extractPagePair L s.mem).fullPages false, (extractPagePair L s.mem).fullPages true) := by
  simp [pageReadFullPagesProg, extractPagePair]

/-- Read `(tailCount false, tailCount true)` from scalar words `mb + 23` and `mb + 24`. -/
def pageReadTailCountsProg (mb : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let r0 ← Memory.read (mb + 23)
  let r1 ← Memory.read (mb + 24)
  pure (r0, r1)

@[simp] theorem runClient_state_pageReadTailCountsProg (mb : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadTailCountsProg mb)) = s := by
  simp [pageReadTailCountsProg]

@[simp] theorem memoryCost_pageReadTailCountsProg (mb : ℕ) (s : Memory.State) :
    memoryCost (pageReadTailCountsProg mb) s = 2 := by
  simp [pageReadTailCountsProg]

theorem realizesBounded_pageReadTailCounts :
    RealizesBounded .exact pageReadTailCountsProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w mb s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    obtain ⟨hw32, hfr⟩ := h
    have := hmem.1
    have := hmem.2 (d + 23)
    have := hmem.2 (d + 24)
    dsimp only [Fits] at *
    omega)

theorem pageReadTailCountsProg_eq (L : PageArenaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pageReadTailCountsProg L.metaBase) =
      ((extractPagePair L s.mem).tailCount false, (extractPagePair L s.mem).tailCount true) := by
  simp [pageReadTailCountsProg, extractPagePair]

/-- Read `(cleanVp, cleanOff)` from scalar words `mb + 19` and `mb + 30`. -/
def pageReadCleanPosProg (mb : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let cvp ← Memory.read (mb + 19)
  let coff ← Memory.read (mb + 30)
  pure (cvp, coff)

@[simp] theorem runClient_state_pageReadCleanPosProg (mb : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadCleanPosProg mb)) = s := by
  simp [pageReadCleanPosProg]

@[simp] theorem memoryCost_pageReadCleanPosProg (mb : ℕ) (s : Memory.State) :
    memoryCost (pageReadCleanPosProg mb) s = 2 := by
  simp [pageReadCleanPosProg]

theorem realizesBounded_pageReadCleanPos :
    RealizesBounded .exact pageReadCleanPosProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w mb s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    obtain ⟨hw32, hfr⟩ := h
    have := hmem.1
    have := hmem.2 (d + 19)
    have := hmem.2 (d + 30)
    dsimp only [Fits] at *
    omega)

theorem pageReadCleanPosProg_eq (L : PageArenaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pageReadCleanPosProg L.metaBase) =
      ((extractPageUnperm L s.mem).cleanVp, (extractPageUnperm L s.mem).cleanOff) := by
  simp [pageReadCleanPosProg, extractPageUnperm]

/-- Read `(jobSide, jobCur)` from scalar words `mb + 28` and `mb + 29`. -/
def pageReadJobArgsProg (mb : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let js ← Memory.read (mb + 28)
  let jc ← Memory.read (mb + 29)
  pure (js, jc)

@[simp] theorem runClient_state_pageReadJobArgsProg (mb : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadJobArgsProg mb)) = s := by
  simp [pageReadJobArgsProg]

@[simp] theorem memoryCost_pageReadJobArgsProg (mb : ℕ) (s : Memory.State) :
    memoryCost (pageReadJobArgsProg mb) s = 2 := by
  simp [pageReadJobArgsProg]

theorem realizesBounded_pageReadJobArgs :
    RealizesBounded .exact pageReadJobArgsProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w mb s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    obtain ⟨hw32, hfr⟩ := h
    have := hmem.1
    have := hmem.2 (d + 28)
    have := hmem.2 (d + 29)
    dsimp only [Fits] at *
    omega)

theorem pageReadJobArgsProg_eq (L : PageArenaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (pageReadJobArgsProg L.metaBase) =
      (s.mem (L.metaBase + 28), s.mem (L.metaBase + 29)) := by
  simp [pageReadJobArgsProg]

/-- Write `(cleanPhase, (cleanVp, cleanOff))` to words `mb + 18`, `mb + 19`, and `mb + 30`. -/
def pageWriteCleanProg : ℕ × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (mb, (ph, (cvp, coff))) => do
    Memory.write (mb + 18) ph
    Memory.write (mb + 19) cvp
    Memory.write (mb + 30) coff

@[simp] theorem runClient_frontier_pageWriteCleanProg
    (x : ℕ × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageWriteCleanProg x))).frontier =
      s.frontier := by
  rcases x with ⟨_, _, _, _⟩; simp [pageWriteCleanProg]

theorem realizesBounded_pageWriteClean :
    RealizesBounded .exact pageWriteCleanProg
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (mb, _) s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨mb, ph, cvp, coff⟩
    obtain ⟨hw32, hfr⟩ := h
    have := hmem.1
    dsimp only [Fits] at *
    omega)

/-- Read `pageOf side vp` from the packed `offDir` page directory. -/
def pageReadPageOfProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, od), (_ot, pb)), ((wv, _pg), (mp, _ib))), _), (sideBit, vp)) =>
    if vp < mp then do
      let idx ← pure (4 * vp + if sideBit = 0 then 0 else 1)
      readPackedCompGenProg (((mb, od), (pb, wv)), idx)
    else
      pure 0

@[simp] theorem runClient_state_pageReadPageOfProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadPageOfProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageReadPageOfProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageReadPageOfProg_le
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (pageReadPageOfProg x) s ≤ 2 := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageReadPageOfProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageReadPageOf :
    RealizesBounded .exact pageReadPageOfProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, vp⟩⟩
    obtain ⟨hw, hwv, hpb, _, _, _, _, hmp_ge4, hmp4, _, _, _, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    dsimp only [Fits] at *
    (try split_ifs at *) <;> try omega)
  all_goals exact ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩

theorem pageReadPageOfProg_eq {L : PageArenaLayout} (side : Bool) {vp : ℕ}
    (hvp : vp < L.maxPages) (s : Memory.State) :
    (Memory.spec 0).clientResult s
      (pageReadPageOfProg (L.toCtx, (if side then 1 else 0, vp))) =
      (extractPagePair L s.mem).pageOf side vp := by
  unfold pageReadPageOfProg extractPagePair
  dsimp only [PageArenaLayout.toCtx]
  rw [ite_eq_left hvp, ite_eq_left hvp]
  cases side <;> simp

/-- Write `pageOf side vp := val` into the packed `offDir` page directory. -/
@[expose] def pageWritePageOfProg : (PageArenaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((((mb, od), (_ot, pb)), ((wv, _pg), (mp, _ib))), _), (sideBit, vp)), val) =>
    if vp < mp then do
      let idx ← pure (4 * vp + if sideBit = 0 then 0 else 1)
      writePackedCompGenProg ((((mb, od), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_pageWritePageOfProg
    (x : (PageArenaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageWritePageOfProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold pageWritePageOfProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageWritePageOfProg_le
    (x : (PageArenaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (pageWritePageOfProg x) s ≤ 4 := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold pageWritePageOfProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageWritePageOf :
    RealizesBounded .exact pageWritePageOfProg
      (WordEncoding.encode (α := (PageArenaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, vp⟩⟩,
      val⟩
    obtain ⟨hw, hwv, hpb, _, _, _, _, hmp_ge4, hmp4, _, _, _, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    try dsimp only [Fits] at *
    (try split_ifs at *) <;> try omega)
  all_goals exact ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩

/-- Read `(ownerSide P, ownerVp P)` of physical page `P` from `offDir`. -/
@[expose] def pageReadOwnerProg : PageArenaCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (((((mb, od), (_ot, pb)), ((wv, _pg), (mp, _ib))), _), P) =>
    if P < mp then do
      let idxS ← pure (4 * P + 2)
      let idxV ← pure (4 * P + 3)
      let sRaw ← readPackedCompGenProg (((mb, od), (pb, wv)), idxS)
      let vRaw ← readPackedCompGenProg (((mb, od), (pb, wv)), idxV)
      pure (if sRaw = 0 then 0 else 1, vRaw)
    else
      pure (0, 0)

@[simp] theorem runClient_state_pageReadOwnerProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadOwnerProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageReadOwnerProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageReadOwnerProg_le (x : PageArenaCtx × ℕ) (s : Memory.State) :
    memoryCost (pageReadOwnerProg x) s ≤ 4 := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageReadOwnerProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageReadOwner :
    RealizesBounded .exact pageReadOwnerProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, P⟩
    obtain ⟨hw, hwv, hpb, _, _, _, _, hmp_ge4, hmp4, _, _, _, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_state_readPackedCompGenProg] at *
    dsimp only [Fits] at *
    try omega)
  all_goals exact ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩

/-- Write `(ownerSide P, ownerVp P)` of physical page `P` into `offDir`. -/
def pageWriteOwnerProg : (PageArenaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((((mb, od), (_ot, pb)), ((wv, _pg), (mp, _ib))), _), P), (sideBit, vp)) =>
    if P < mp then do
      let idxS ← pure (4 * P + 2)
      let idxV ← pure (4 * P + 3)
      let sVal ← pure (if sideBit = 0 then 0 else 1)
      writePackedCompGenProg ((((mb, od), (pb, wv)), idxS), sVal)
      writePackedCompGenProg ((((mb, od), (pb, wv)), idxV), vp)
    else
      pure ()

@[simp] theorem runClient_frontier_pageWriteOwnerProg
    (x : (PageArenaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageWriteOwnerProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, ⟨_, _⟩⟩
  unfold pageWriteOwnerProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageWriteOwnerProg_le
    (x : (PageArenaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (pageWriteOwnerProg x) s ≤ 8 := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, ⟨_, _⟩⟩
  unfold pageWriteOwnerProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageWriteOwner :
    RealizesBounded .exact pageWriteOwnerProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, P⟩,
      ⟨sb, vp⟩⟩
    obtain ⟨hw, hwv, hpb, _, _, _, _, hmp_ge4, hmp4, _, _, _, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_state_writePackedCompGenProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> try omega)
  all_goals (
    refine ⟨4 * mp, hw, rfl, hpb, by omega, ?_⟩
    (try change mb + od + packedWords (4 * mp) pb w ≤ s.frontier)
    omega)

/-- Read `tailRes side k` from the packed `offTail` tail ring table. -/
def pageReadTailResProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, _od), (ot, pb)), ((wv, pg), _)), _), (sideBit, k)) =>
    if k < 4 * pg then do
      let idx ← pure ((if sideBit = 0 then 0 else 4 * pg) + k)
      readPackedCompGenProg (((mb, ot), (pb, wv)), idx)
    else
      pure 0

@[simp] theorem runClient_state_pageReadTailResProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadTailResProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageReadTailResProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageReadTailResProg_le
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (pageReadTailResProg x) s ≤ 2 := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageReadTailResProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageReadTailRes :
    RealizesBounded .exact pageReadTailResProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, k⟩⟩
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, _, _, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits] at *
    (try split_ifs at *) <;> try omega)
  all_goals exact ⟨16 * pg, hw, rfl, hpb, by omega, by omega⟩

/-- Write `tailRes side k := val` into the packed `offTail` tail ring table. -/
@[expose] def pageWriteTailResProg : (PageArenaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((((mb, _od), (ot, pb)), ((wv, pg), _)), _), (sideBit, k)), val) =>
    if k < 4 * pg then do
      let idx ← pure ((if sideBit = 0 then 0 else 4 * pg) + k)
      writePackedCompGenProg ((((mb, ot), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_pageWriteTailResProg
    (x : (PageArenaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageWriteTailResProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold pageWriteTailResProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageWriteTailResProg_le
    (x : (PageArenaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (pageWriteTailResProg x) s ≤ 4 := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩, _⟩
  unfold pageWriteTailResProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageWriteTailRes :
    RealizesBounded .exact pageWriteTailResProg
      (WordEncoding.encode (α := (PageArenaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, k⟩⟩,
      val⟩
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, _, _, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits] at *
    (try split_ifs at *) <;> try omega)
  all_goals exact ⟨16 * pg, hw, rfl, hpb, by omega, by omega⟩

/-- Read `(tailOwnerSide res, tailOwnerRing res)` of tail residue `res` from `offTail`. -/
def pageReadTailOwnerProg : PageArenaCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (((((mb, _od), (ot, pb)), ((wv, pg), _)), _), res) =>
    if res < 8 * pg then do
      let idx ← pure (8 * pg + res)
      let enc ← readPackedCompGenProg (((mb, ot), (pb, wv)), idx)
      pure (enc % 2, enc / 2)
    else
      pure (0, 0)

@[simp] theorem runClient_state_pageReadTailOwnerProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadTailOwnerProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageReadTailOwnerProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageReadTailOwnerProg_le
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    memoryCost (pageReadTailOwnerProg x) s ≤ 2 := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageReadTailOwnerProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageReadTailOwner :
    RealizesBounded .exact pageReadTailOwnerProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, res⟩
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, _, _, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits] at *
    try omega)
  all_goals exact ⟨16 * pg, hw, rfl, hpb, by omega, by omega⟩

/-- Write `(tailOwnerSide res, tailOwnerRing res)` of tail residue `res` into `offTail`. -/
@[expose] def pageWriteTailOwnerProg : (PageArenaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((((mb, _od), (ot, pb)), ((wv, pg), _)), _), res), (sideBit, k)) =>
    if res < 8 * pg ∧ k < 8 * pg then do
      let idx ← pure (8 * pg + res)
      let val ← pure ((if sideBit = 0 then 0 else 1) + 2 * k)
      writePackedCompGenProg ((((mb, ot), (pb, wv)), idx), val)
    else
      pure ()

@[simp] theorem runClient_frontier_pageWriteTailOwnerProg
    (x : (PageArenaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageWriteTailOwnerProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, ⟨_, _⟩⟩
  unfold pageWriteTailOwnerProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageWriteTailOwnerProg_le
    (x : (PageArenaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (pageWriteTailOwnerProg x) s ≤ 4 := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, ⟨_, _⟩⟩
  unfold pageWriteTailOwnerProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageWriteTailOwner :
    RealizesBounded .exact pageWriteTailOwnerProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, res⟩,
      ⟨sb, k⟩⟩
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, _, _, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits] at *
    (try split_ifs at *) <;> try omega)
  all_goals exact ⟨16 * pg, hw, rfl, hpb, by omega, by omega⟩

/-- Swap physical pair slots `p₁` and `p₂` in the shared `itemBase` pair stream. -/
@[expose] def pageSwapPhysProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((_m1, ((wv, _pg), (_mp, ib))), ((qb, vb), nc)), (p₁, p₂)) =>
    if p₁ < nc ∧ p₂ < nc then
      swapPairGenProg (((ib, (qb, vb)), wv), (p₁, p₂))
    else
      pure ()

@[simp] theorem runClient_frontier_pageSwapPhysProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageSwapPhysProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageSwapPhysProg swapPairGenProg; dsimp only; split_ifs <;> simp

theorem memoryCost_pageSwapPhysProg_le
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (pageSwapPhysProg x) s ≤ 24 := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageSwapPhysProg swapPairGenProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageSwapPhys :
    RealizesBounded .exact pageSwapPhysProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hsw := realizesBounded_swapPairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨p₁, p₂⟩⟩
    obtain ⟨hw, hwv, _, hqb, hvb, _, _, _, _, _, _, _, _, _, hib_fr⟩ := h
    subst hwv
    dsimp only [Fits] at *
    have hp1 : p₁ < nc := by omega
    have hp2 : p₂ < nc := by omega
    have hlt1 := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hp1
    have hlt2 := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw hp2)
  all_goals (dsimp only [SwapPairPre]; exact ⟨hw, rfl, hqb, hvb, by omega, by omega⟩)

theorem extractPageUnperm_writeScalar {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (mem : ℕ → ℕ) (off val : ℕ) :
    let m' := Function.update mem (L.metaBase + off) val
    let u := extractPageUnperm L mem
    (off = 18 → extractPageUnperm L m' = { u with cleanPhase := val } ∧
      arenaPairAt L m' = arenaPairAt L mem) ∧
    (off = 19 → extractPageUnperm L m' = { u with cleanVp := val } ∧
      arenaPairAt L m' = arenaPairAt L mem) ∧
    (off = 30 → extractPageUnperm L m' = { u with cleanOff := val } ∧
      arenaPairAt L m' = arenaPairAt L mem) ∧
    (∀ side : Bool, off = (if side then 22 else 21) →
      extractPageUnperm L m' =
        { u with st := { u.st with fullPages := Function.update u.st.fullPages side val } } ∧
      arenaPairAt L m' = arenaPairAt L mem) ∧
    (∀ side : Bool, off = (if side then 24 else 23) →
      extractPageUnperm L m' =
        { u with st := { u.st with tailCount := Function.update u.st.tailCount side val } } ∧
      arenaPairAt L m' = arenaPairAt L mem) ∧
    (∀ side : Bool, off = (if side then 26 else 25) →
      extractPageUnperm L m' =
        { u with st := { u.st with tailHead := Function.update u.st.tailHead side val } } ∧
      arenaPairAt L m' = arenaPairAt L mem) := by
  dsimp only
  have prove_sc : ∀ hoff : off < 32,
      (∀ d < 4 * L.maxPages,
        readPacked (L.metaBase + L.offDir) L.ptrB L.w (Function.update mem (L.metaBase + off) val)
          d = readPacked (L.metaBase + L.offDir) L.ptrB L.w mem d) ∧
      (∀ t < 16 * L.pgB,
        readPacked (L.metaBase + L.offTail) L.ptrB L.w (Function.update mem (L.metaBase + off) val)
          t = readPacked (L.metaBase + L.offTail) L.ptrB L.w mem t) ∧
      arenaPairAt L (Function.update mem (L.metaBase + off) val) = arenaPairAt L mem :=
    fun hoff => scalar_update_preserves_packed hw ho1 ho2 hm_ib mem hoff val
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun side h => ?_, fun side h => ?_,
    fun side h => ?_⟩
  · subst h; obtain ⟨hd, ht, ha⟩ := prove_sc (by decide)
    refine ⟨?_, ha⟩; unfold extractPageUnperm extractPagePair; dsimp only
    congr 1
    · congr 1
      · exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s vp; split_ifs
        · cases s <;> (dsimp only; exact hd _ (by omega))
        · rfl
      · ext P; split_ifs <;> [rw [hd _ (by omega)]; rfl]
      · ext P; split_ifs <;> [exact hd _ (by omega); rfl]
      · ext s k; split_ifs
        · cases s <;> (dsimp only; exact ht _ (by omega))
        · rfl
      · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
      · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
      · rw [Function.update_of_ne (by omega : L.metaBase + 27 ≠ L.metaBase + 18),
          Function.update_of_ne (by omega : L.metaBase + 28 ≠ L.metaBase + 18),
          Function.update_of_ne (by omega : L.metaBase + 29 ≠ L.metaBase + 18)]
    · exact Function.update_self ..
    · exact Function.update_of_ne (by omega) ..
    · exact Function.update_of_ne (by omega) ..
  · subst h; obtain ⟨hd, ht, ha⟩ := prove_sc (by decide)
    refine ⟨?_, ha⟩; unfold extractPageUnperm extractPagePair; dsimp only
    congr 1
    · congr 1
      · exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s vp; split_ifs
        · cases s <;> (dsimp only; exact hd _ (by omega))
        · rfl
      · ext P; split_ifs <;> [rw [hd _ (by omega)]; rfl]
      · ext P; split_ifs <;> [exact hd _ (by omega); rfl]
      · ext s k; split_ifs
        · cases s <;> (dsimp only; exact ht _ (by omega))
        · rfl
      · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
      · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
      · rw [Function.update_of_ne (by omega : L.metaBase + 27 ≠ L.metaBase + 19),
          Function.update_of_ne (by omega : L.metaBase + 28 ≠ L.metaBase + 19),
          Function.update_of_ne (by omega : L.metaBase + 29 ≠ L.metaBase + 19)]
    · exact Function.update_of_ne (by omega) ..
    · exact Function.update_self ..
    · exact Function.update_of_ne (by omega) ..
  · subst h; obtain ⟨hd, ht, ha⟩ := prove_sc (by decide)
    refine ⟨?_, ha⟩; unfold extractPageUnperm extractPagePair; dsimp only
    congr 1
    · congr 1
      · exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
      · ext s vp; split_ifs
        · cases s <;> (dsimp only; exact hd _ (by omega))
        · rfl
      · ext P; split_ifs <;> [rw [hd _ (by omega)]; rfl]
      · ext P; split_ifs <;> [exact hd _ (by omega); rfl]
      · ext s k; split_ifs
        · cases s <;> (dsimp only; exact ht _ (by omega))
        · rfl
      · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
      · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
      · rw [Function.update_of_ne (by omega : L.metaBase + 27 ≠ L.metaBase + 30),
          Function.update_of_ne (by omega : L.metaBase + 28 ≠ L.metaBase + 30),
          Function.update_of_ne (by omega : L.metaBase + 29 ≠ L.metaBase + 30)]
    · exact Function.update_of_ne (by omega) ..
    · exact Function.update_of_ne (by omega) ..
    · exact Function.update_self ..
  · cases side <;> (
      simp only [Bool.false_eq_true, ↓reduceIte] at h; subst h
      obtain ⟨hd, ht, ha⟩ := prove_sc (by decide)
      refine ⟨?_, ha⟩; unfold extractPageUnperm extractPagePair; dsimp only
      congr 1
      · congr 1
        · exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
            Function.update_self, Function.update_of_ne (by decide : false ≠ true),
            Function.update_of_ne (by decide : true ≠ false)]
          all_goals try exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
        · ext s vp; split_ifs
          · cases s <;> (dsimp only; exact hd _ (by omega))
          · rfl
        · ext P; split_ifs <;> [rw [hd _ (by omega)]; rfl]
        · ext P; split_ifs <;> [exact hd _ (by omega); rfl]
        · ext s k; split_ifs
          · cases s <;> (dsimp only; exact ht _ (by omega))
          · rfl
        · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
        · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
      · exact Function.update_of_ne (by omega) ..
      · exact Function.update_of_ne (by omega) ..
      · exact Function.update_of_ne (by omega) ..)
  · cases side <;> (
      simp only [Bool.false_eq_true, ↓reduceIte] at h; subst h
      obtain ⟨hd, ht, ha⟩ := prove_sc (by decide)
      refine ⟨?_, ha⟩; unfold extractPageUnperm extractPagePair; dsimp only
      congr 1
      · congr 1
        · exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
            Function.update_self, Function.update_of_ne (by decide : false ≠ true),
            Function.update_of_ne (by decide : true ≠ false)]
          all_goals try exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
        · ext s vp; split_ifs
          · cases s <;> (dsimp only; exact hd _ (by omega))
          · rfl
        · ext P; split_ifs <;> [rw [hd _ (by omega)]; rfl]
        · ext P; split_ifs <;> [exact hd _ (by omega); rfl]
        · ext s k; split_ifs
          · cases s <;> (dsimp only; exact ht _ (by omega))
          · rfl
        · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
        · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
      · exact Function.update_of_ne (by omega) ..
      · exact Function.update_of_ne (by omega) ..
      · exact Function.update_of_ne (by omega) ..)
  · cases side <;> (
      simp only [Bool.false_eq_true, ↓reduceIte] at h; subst h
      obtain ⟨hd, ht, ha⟩ := prove_sc (by decide)
      refine ⟨?_, ha⟩; unfold extractPageUnperm extractPagePair; dsimp only
      congr 1
      · congr 1
        · exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> exact Function.update_of_ne (by omega) ..
        · ext s; cases s <;> simp only [Bool.false_eq_true, ↓reduceIte,
            Function.update_self, Function.update_of_ne (by decide : false ≠ true),
            Function.update_of_ne (by decide : true ≠ false)]
          all_goals try exact Function.update_of_ne (by omega) ..
        · ext s vp; split_ifs
          · cases s <;> (dsimp only; exact hd _ (by omega))
          · rfl
        · ext P; split_ifs <;> [rw [hd _ (by omega)]; rfl]
        · ext P; split_ifs <;> [exact hd _ (by omega); rfl]
        · ext s k; split_ifs
          · cases s <;> (dsimp only; exact ht _ (by omega))
          · rfl
        · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
        · ext r; split_ifs <;> [rw [ht _ (by omega)]; rfl]
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
      · exact Function.update_of_ne (by omega) ..
      · exact Function.update_of_ne (by omega) ..
      · exact Function.update_of_ne (by omega) ..)

theorem extractPageUnperm_pageWriteCleanProg {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (s : Memory.State) (ph cvp coff : ℕ) :
    let m' := ((Memory.spec 0).clientState s
      (pageWriteCleanProg (L.metaBase, (ph, (cvp, coff))))).mem
    let u := extractPageUnperm L s.mem
    extractPageUnperm L m' = { u with cleanPhase := ph, cleanVp := cvp, cleanOff := coff } ∧
    arenaPairAt L m' = arenaPairAt L s.mem := by
  dsimp only
  unfold pageWriteCleanProg StateTransitionSpec.clientState
  simp only [prog_runClient_state_bind, prog_runClient_state_write]
  obtain ⟨hsc18, _, _, _, _, _⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib s.mem 18 ph
  obtain ⟨hu1, ha1⟩ := hsc18 rfl
  obtain ⟨_, hsc19, _, _, _, _⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib _ 19 cvp
  obtain ⟨hu2, ha2⟩ := hsc19 rfl
  obtain ⟨_, _, hsc30, _, _, _⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib _ 30 coff
  obtain ⟨hu3, ha3⟩ := hsc30 rfl
  rw [hu3, hu2, hu1, ha3, ha2, ha1]
  exact ⟨rfl, rfl⟩

/-! ### Phase-1 Incremental Initialization Primitives (`RealizesBounded .exact`, `¬ReadsWidth`) -/

/-- Initialize the `[metaBase + 18, metaBase + 31)` scalar words of `PageUnpermState` to
`ofPagePair (initFromSrc pgB n_0)` (`14` memory writes, `¬ReadsWidth`). -/
def pageInitScalarsProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, _od), _o2), ((_wv, pg), (_mp, _ib))), ((_qb, _vb), nc)), n_0) =>
    if n_0 ≤ nc then do
      let base_r ← pure (pg + pg / 2)
      let q_0 ← pure (if n_0 < pg + base_r then 0 else (n_0 - base_r) / pg)
      let r_0 ← pure (n_0 - q_0 * pg)
      Memory.write (mb + 18) 0
      Memory.write (mb + 19) 0
      Memory.write (mb + 20) pg
      Memory.write (mb + 21) q_0
      Memory.write (mb + 22) 0
      Memory.write (mb + 23) r_0
      Memory.write (mb + 24) 0
      Memory.write (mb + 25) 0
      Memory.write (mb + 26) 0
      pageWriteJobProg (mb, (0, (0, 0)))
      Memory.write (mb + 30) 0
      Memory.write (mb + 31) 0
    else
      pure ()

/-- Precondition for `pageInitScalarsProg`. -/
@[expose] def PageInitScalarsPre (w : ℕ) : PageArenaCtx × ℕ → Memory.State → Prop
  | (ctx, _n_0), s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier

theorem realizesBounded_pageInitScalars :
    RealizesBounded .exact pageInitScalarsProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      PageInitScalarsPre (fun _ _ => 0) := by
  have hwj := realizesBounded_pageWriteJob
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, n_0⟩
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    have hpg2 : pg / 2 ≤ pg := Nat.div_le_self pg 2
    have hq_le : (n_0 - (pg + pg / 2)) / pg ≤ n_0 - (pg + pg / 2) := Nat.div_le_self _ pg
    have hq_mul : ((n_0 - (pg + pg / 2)) / pg) * pg ≤ n_0 - (pg + pg / 2) :=
      Nat.div_mul_le_self _ _
    have hq_n0 : ((n_0 - (pg + pg / 2)) / pg) * pg ≤ n_0 := hq_mul.trans (Nat.sub_le _ _)
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> omega)

/-- Single-step directory initialization (`cur ↦ min maxPages (cur + 1)`, `1 ≤ memoryCost`). -/
def pageInitDirStepProg : PageArenaCtx × ℕ → Memory.Prog ℕ
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), cur) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if cur < mp then do
      let z0 ← pure 0
      let o1 ← pure 1
      pageWritePageOfProg ((ctx, (z0, cur)), cur)
      pageWritePageOfProg ((ctx, (o1, cur)), z0)
      pageWriteOwnerProg ((ctx, cur), (z0, cur))
      let _ ← Memory.read mb
      pure (cur + 1)
    else do
      let _ ← Memory.read mb
      pure cur

theorem memoryCost_pageInitDirStepProg_pos (x : PageArenaCtx × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (pageInitDirStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageInitDirStepProg; dsimp only
  split_ifs <;>
    simp only [pure_bind, Realization.memoryCost_bind', StateTransitionSpec.clientState,
      prog_memoryCost_read, prog_runClient_state_read, memoryCost_pure] <;>
    omega

theorem realizesBounded_pageInitDirStep :
    RealizesBounded .exact pageInitDirStepProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwp := realizesBounded_pageWritePageOf
  have hwo := realizesBounded_pageWriteOwner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, cur⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, _, _, hmp_ge4, hmp4, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageWritePageOfProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    first | exact hv0 | omega)

/-- Batched Phase-1 directory initializer parameterized explicitly by `fuel : ℕ` (`¬ReadsWidth`). -/
def pageInitDirBatchProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, cur), fuel) => iterate pageInitDirStepProg ctx fuel cur

theorem realizesBounded_pageInitDirBatch :
    RealizesBounded .exact pageInitDirBatchProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, cur), fuel) s =>
        iterationSafe pageInitDirStepProg
          (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
          w ctx fuel cur s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := PageArenaCtx))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_pageInitDirStep
    memoryCost_pageInitDirStepProg_pos

/-- Initialize both sides' `tailRes` entries at ring index `cur < 4 * pgB` during Phase 1. -/
def pageInitTailResSubProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), qb_mod), cur) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if cur < 4 * pg then do
      let z0 ← pure 0
      let o1 ← pure 1
      let res_v ← pure ((qb_mod + cur) % (8 * pg))
      pageWriteTailResProg ((ctx, (z0, cur)), res_v)
      pageWriteTailResProg ((ctx, (o1, cur)), res_v)
    else
      pure ()

@[simp] theorem runClient_frontier_pageInitTailResSubProg
    (x : (PageArenaCtx × ℕ) × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageInitTailResSubProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, _⟩
  unfold pageInitTailResSubProg; dsimp only
  split_ifs <;> simp

theorem realizesBounded_pageInitTailResSub :
    RealizesBounded .exact pageInitTailResSubProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, qb_mod), _) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        qb_mod < 8 * (PageArenaLayout.ofCtx ctx).pgB)
      (fun _ _ => 0) := by
  have hwtr := realizesBounded_pageWriteTailRes
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, qbm⟩, cur⟩
    obtain ⟨hv0, hqbm⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_frontier_pageWriteTailResProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hmod8 : (qbm + cur) % (8 * pg) < 8 * pg := Nat.mod_lt _ (by omega)
    first | exact hv0 | omega)

/-- Single-step tail initialization (`cur ↦ min (8 * pgB) (cur + 1)`, `1 ≤ memoryCost`). -/
def pageInitTailStepProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), n_0), cur) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if n_0 ≤ nc ∧ cur < 8 * pg then do
      let z0 ← pure 0
      let qb_mod ← pure (((if n_0 < pg + (pg + pg / 2) then 0
        else (n_0 - (pg + pg / 2)) / pg) * pg) % (8 * pg))
      pageInitTailResSubProg ((ctx, qb_mod), cur)
      let ring_v ← pure ((cur + 8 * pg - qb_mod) % (8 * pg))
      pageWriteTailOwnerProg ((ctx, cur), (z0, ring_v))
      let _ ← Memory.read mb
      pure (cur + 1)
    else do
      let _ ← Memory.read mb
      pure cur

theorem memoryCost_pageInitTailStepProg_pos
    (x : (PageArenaCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (pageInitTailStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, _⟩
  unfold pageInitTailStepProg; dsimp only
  split_ifs <;>
    simp only [pure_bind, Realization.memoryCost_bind', StateTransitionSpec.clientState,
      prog_memoryCost_read, prog_runClient_state_read, memoryCost_pure] <;>
    omega

theorem realizesBounded_pageInitTailStep :
    RealizesBounded .exact pageInitTailStepProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsub := realizesBounded_pageInitTailResSub
  have hwto := realizesBounded_pageWriteTailOwner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, n_0⟩, cur⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageInitTailResSubProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hpg2 : pg / 2 ≤ pg := Nat.div_le_self pg 2
    have hq_mul : ((n_0 - (pg + pg / 2)) / pg) * pg ≤ n_0 - (pg + pg / 2) :=
      Nat.div_mul_le_self _ _
    have hq_n0 : ((n_0 - (pg + pg / 2)) / pg) * pg ≤ n_0 := hq_mul.trans (Nat.sub_le _ _)
    have hmod8 : ∀ x : ℕ, x % (8 * pg) < 8 * pg := fun x => Nat.mod_lt x (by omega)
    have h1 := hmod8 ((if n_0 < pg + (pg + pg / 2) then 0
      else (n_0 - (pg + pg / 2)) / pg) * pg)
    have h2 := hmod8 (cur + 8 * pg - ((if n_0 < pg + (pg + pg / 2) then 0
      else (n_0 - (pg + pg / 2)) / pg) * pg) % (8 * pg))
    (try split_ifs at *) <;> first | exact hv0 | omega)

/-- Batched Phase-1 tail initializer parameterized explicitly by `fuel : ℕ` (`¬ReadsWidth`). -/
def pageInitTailBatchProg : ((PageArenaCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((ctx, n_0), cur), fuel) => iterate pageInitTailStepProg (ctx, n_0) fuel cur

theorem realizesBounded_pageInitTailBatch :
    RealizesBounded .exact pageInitTailBatchProg
      (WordEncoding.encode (α := ((PageArenaCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((ctx, n_0), cur), fuel) s =>
        iterationSafe pageInitTailStepProg
          (fun w' ((c', _), _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
          w (ctx, n_0) fuel cur s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := PageArenaCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_pageInitTailStep
    memoryCost_pageInitTailStepProg_pos

/-- Transfer theorem: once scalars, directory `[0, L.maxPages)`, and tail `[0, 8 * L.pgB)` agree
with `initFromSrc L.pgB n_0` (`32 ≤ L.pgB`, `n_0 ≤ L.nCap ≤ (L.maxPages - 2) * L.pgB`),
`extractPageUnperm L mem` satisfies `Valid`, `cleanPhase = 0`, `virtLen false = n_0`,
`virtLen true = 0`, and identity physical mapping `toPhys false idx = idx` on `[0, n_0)`. -/
theorem valid_extractPageUnperm_of_init {L : PageArenaLayout} {mem : ℕ → ℕ} {n_0 : ℕ}
    (hpg32 : 32 ≤ L.pgB) (hmp4 : 4 ≤ L.maxPages)
    (hn0_mp : n_0 ≤ (L.maxPages - 2) * L.pgB)
    (hc_ph : (extractPageUnperm L mem).cleanPhase = 0)
    (hc_vp : (extractPageUnperm L mem).cleanVp = 0)
    (hc_off : (extractPageUnperm L mem).cleanOff = 0)
    (hps : (extractPagePair L mem).pageSize = (PagePairState.initFromSrc L.pgB n_0).pageSize)
    (hfp : (extractPagePair L mem).fullPages = (PagePairState.initFromSrc L.pgB n_0).fullPages)
    (htc : (extractPagePair L mem).tailCount = (PagePairState.initFromSrc L.pgB n_0).tailCount)
    (hth : (extractPagePair L mem).tailHead = (PagePairState.initFromSrc L.pgB n_0).tailHead)
    (hjob : (extractPagePair L mem).job = .idle)
    (hpo : ∀ side vp, vp < L.maxPages →
      (extractPagePair L mem).pageOf side vp =
        if side then 0 else vp)
    (hos : ∀ P < L.maxPages, (extractPagePair L mem).ownerSide P = false)
    (hov : ∀ P < L.maxPages, (extractPagePair L mem).ownerVp P = P)
    (htr : ∀ side k, k < 4 * L.pgB →
      (extractPagePair L mem).tailRes side k =
        (PagePairState.initFromSrc L.pgB n_0).tailRes side k)
    (htos : ∀ res < 8 * L.pgB,
      (extractPagePair L mem).tailOwnerSide res = false)
    (htor : ∀ res < 8 * L.pgB,
      (extractPagePair L mem).tailOwnerRing res =
        (PagePairState.initFromSrc L.pgB n_0).tailOwnerRing res) :
    let u := extractPageUnperm L mem
    u.Valid ∧ u.cleanPhase = 0 ∧ u.st.pageSize = L.pgB ∧
    u.st.virtLen false = n_0 ∧ u.st.virtLen true = 0 ∧
    ∀ idx < n_0, u.toPhys false idx = idx := by
  dsimp only
  set st := extractPagePair L mem
  set st₀ := PagePairState.initFromSrc L.pgB n_0
  obtain ⟨hwb₀, hv₀, hvl₀_f, hvl₀_t, hid₀⟩ := PagePairState.wellBalanced_initFromSrc L.pgB n_0
  have hps₀ : st₀.pageSize = L.pgB := max_eq_left hpg32
  have hps_B : st.pageSize = L.pgB := hps.trans hps₀
  have hvl_eq : st.virtLen = st₀.virtLen := by
    ext s; unfold PagePairState.virtLen; rw [hps, hfp, htc]
  have htp_eq : st.totalPages = st₀.totalPages := by unfold PagePairState.totalPages; rw [hfp]
  have hti_eq : st.totalItems = st₀.totalItems := by unfold PagePairState.totalItems; rw [hvl_eq]
  have hq0_lt : st₀.fullPages false < L.maxPages := by
    have h1 : st₀.fullPages false * L.pgB ≤ n_0 := by
      have hv_eq : st₀.fullPages false * L.pgB + st₀.tailCount false = n_0 := by
        unfold PagePairState.virtLen at hvl₀_f; rwa [hps₀] at hvl₀_f
      omega
    have h2 : st₀.fullPages false * L.pgB < L.maxPages * L.pgB := by
      have : (L.maxPages - 2) * L.pgB < L.maxPages * L.pgB :=
        Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      omega
    exact (Nat.mul_lt_mul_right (by omega)).mp h2
  have hqf0_t : st₀.fullPages true = 0 := by simp [st₀, PagePairState.initFromSrc]
  have htotP_lt : st₀.totalPages < L.maxPages := by
    unfold PagePairState.totalPages; rw [hqf0_t]; omega
  have hrs_eq : ∀ s t, st.ringSlot s t = st₀.ringSlot s t := fun s t => by
    unfold PagePairState.ringSlot; rw [hth, hps]
  have htailPhys_eq : ∀ s t, st.tailPhys s t = st₀.tailPhys s t := fun s t => by
    unfold PagePairState.tailPhys
    rw [htp_eq, hps, hrs_eq]
    have hrs_lt : st₀.ringSlot s t < 4 * L.pgB := by
      unfold PagePairState.ringSlot; rw [hps₀]; exact Nat.mod_lt _ (by omega)
    rw [htr s _ hrs_lt]
  have hv_st : st.Valid := by
    refine ⟨hps ▸ hv₀.pageSize_pos, fun s => ?_, ?_, fun s => ?_, fun s vp hvp => ?_,
      fun s vp hvp => ?_, fun P hP => ?_, fun s t ht => ?_, fun s t ht => ?_,
      fun s t ht => ?_, fun p hlo hhi => ?_⟩
    · rw [htc, hps]; exact hv₀.tailCount_lt s
    · rw [htc, hps]; exact hv₀.tailSum_lt
    · rw [hth, hps]; exact hv₀.tailHead_lt s
    · rw [hfp] at hvp; rw [htp_eq]
      cases s
      · rw [hpo false vp (hvp.trans hq0_lt)]; exact hv₀.page_lt false vp hvp
      · rw [hqf0_t] at hvp; exact absurd hvp (Nat.not_lt_zero _)
    · rw [hfp] at hvp
      cases s
      · have hvp_m : vp < L.maxPages := hvp.trans hq0_lt
        rw [hpo false vp hvp_m]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨hos vp hvp_m, hov vp hvp_m⟩
      · rw [hqf0_t] at hvp; exact absurd hvp (Nat.not_lt_zero _)
    · rw [htp_eq] at hP
      have hPm : P < L.maxPages := hP.trans htotP_lt
      rw [hos P hPm, hov P hPm, hfp, hpo false P hPm]
      exact hv₀.pageOf_owner P hP
    · rw [htc] at ht; rw [hps, hrs_eq]
      have hrs_lt : st₀.ringSlot s t < 4 * L.pgB := by
        unfold PagePairState.ringSlot; rw [hps₀]; exact Nat.mod_lt _ (by omega)
      rw [htr s _ hrs_lt]; exact hv₀.tailRes_lt s t ht
    · rw [htc] at ht; rw [hti_eq, htailPhys_eq]; exact hv₀.tail_lt s t ht
    · rw [htc] at ht
      have hrs_lt : st₀.ringSlot s t < 4 * L.pgB := by
        unfold PagePairState.ringSlot; rw [hps₀]; exact Nat.mod_lt _ (by omega)
      have hres_lt : st₀.tailRes s (st₀.ringSlot s t) < 8 * L.pgB := by
        rw [← hps₀]; exact hv₀.tailRes_lt s t ht
      dsimp only
      rw [hrs_eq, htr s _ hrs_lt, htor _ hres_lt, htos _ hres_lt]
      exact hv₀.owner_tail s t ht
    · rw [htp_eq, hps] at hlo; rw [hti_eq] at hhi
      have hmod_lt : p % (8 * st.pageSize) < 8 * L.pgB := by
        rw [hps_B]; exact Nat.mod_lt _ (by omega)
      dsimp only
      rw [htos _ hmod_lt, htor _ hmod_lt, hps, hth, htc]
      obtain ⟨h1, h2, h3⟩ := hv₀.tail_owner p hlo hhi
      refine ⟨h1, h2, ?_⟩
      rw [htailPhys_eq]
      exact h3
  have hphi_eq : st.phi = st₀.phi := by unfold PagePairState.phi; rw [hps, hfp, htc]
  have hwb_st : st.WellBalanced := by
    refine ⟨hv_st, hps ▸ hwb₀.pageSize_ge, ?_, ?_, ?_⟩
    · unfold PagePairState.JobValid; rw [hjob]; trivial
    · have hp₀ := hwb₀.pot_bound
      have hj₀ : st₀.job = .idle := rfl
      rw [ite_eq_left hj₀] at hp₀
      rw [ite_eq_left hjob, hphi_eq, hps]
      exact hp₀
    · unfold PagePairState.ActiveSideBound; rw [hjob]; trivial
  set u := extractPageUnperm L mem
  have hu_eq : u = PageUnpermState.ofPagePair st := by
    rcases hu : u with ⟨st_u, ph_u, vp_u, off_u⟩
    have h1 : st_u = st := congrArg PageUnpermState.st hu.symm
    have h2 : ph_u = 0 := (congrArg PageUnpermState.cleanPhase hu.symm).trans hc_ph
    have h3 : vp_u = 0 := (congrArg PageUnpermState.cleanVp hu.symm).trans hc_vp
    have h4 : off_u = 0 := (congrArg PageUnpermState.cleanOff hu.symm).trans hc_off
    subst h1; subst h2; subst h3; subst h4; rfl
  refine ⟨hu_eq ▸ PageUnpermState.valid_ofPagePair hwb_st, hc_ph, hps_B,
    by change st.virtLen false = n_0; rw [hvl_eq, hvl₀_f],
    by change st.virtLen true = 0; rw [hvl_eq, hvl₀_t],
    fun idx hidx => ?_⟩
  rw [hu_eq, PageUnpermState.toPhys_of_not_cleanSwap _ (by simp [PageUnpermState.ofPagePair])]
  change st.toPhys false idx = idx
  conv_rhs => rw [← hid₀ idx hidx]
  unfold PagePairState.toPhys PagePairState.effPage
  rw [hjob, show st₀.job = .idle from rfl]
  dsimp only
  rw [hfp, hps]
  split_ifs with hlt
  · have hvp : idx / st₀.pageSize < st₀.fullPages false :=
      (Nat.div_lt_iff_lt_mul hv₀.pageSize_pos).mpr hlt
    rw [hpo false _ (hvp.trans hq0_lt)]
    simp [st₀, PagePairState.initFromSrc]
  · exact htailPhys_eq false _

/-! ### `O(1)` Virtual-to-Physical Translation and Read/Write (`¬ReadsWidth`) -/

/-- Translate tail offset `(sideBit, t)` to `st.tailPhys side t` in `Memory.Prog`
(`¬ReadsWidth`). -/
def pageTailPhysInnerProg : (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, k)),
      (base, tsum)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let res ← pageReadTailResProg (ctx, (sideBit, k))
    if res < 8 * pg then do
      let off ← pure ((res + 8 * pg - base % (8 * pg)) % (8 * pg))
      if off < tsum then
        pure (base + off)
      else
        pure 0
    else
      pure 0

@[simp] theorem runClient_state_pageTailPhysInnerProg
    (x : (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageTailPhysInnerProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩
  unfold pageTailPhysInnerProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    runClient_state_pageReadTailResProg]
  split_ifs
  · simp only [pure_bind]; split_ifs <;> simp
  · simp

theorem realizesBounded_pageTailPhysInner :
    RealizesBounded .exact pageTailPhysInnerProg
      (WordEncoding.encode (α := (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, _), (base, tsum)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        base + tsum ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hrtr := realizesBounded_pageReadTailRes
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨sb, k⟩⟩, ⟨base, tsum⟩⟩
    obtain ⟨hv0, hbt⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hm8 : ∀ x : ℕ, x % (8 * pg) < 8 * pg := fun x => Nat.mod_lt x (by omega)
    have h1 := hm8 base
    have h2 := hm8 ((Memory.spec 0).clientResult s
      (pageReadTailResProg (((((mb, od), (ot, pb)), ((w, pg), (mp, ib))), ((qb, vb), nc)),
        (sb, k))) + 8 * pg - base % (8 * pg))
    first | exact hv0 | omega)

/-- Guarded ring-slot dispatch helper for `pageTailPhysBoundedProg` (`¬ReadsWidth`). -/
def pageTailPhysDispatchProg :
    ((PageArenaCtx × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog ℕ
  | (((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, t)), base),
      (tc, th)) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if tc.1 ≤ nc - base then
      if tc.2 ≤ nc - base - tc.1 ∧ th < 4 * pg ∧ t < 4 * pg then do
        let k ← pure ((th + t) % (4 * pg))
        let tsum_w ← pure (tc.1 + tc.2)
        pageTailPhysInnerProg ((ctx, (sideBit, k)), (base, tsum_w))
      else
        pure 0
    else
      pure 0

@[simp] theorem runClient_state_pageTailPhysDispatchProg
    (x : ((PageArenaCtx × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageTailPhysDispatchProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩, _⟩,
    ⟨⟨_, _⟩, _⟩⟩
  unfold pageTailPhysDispatchProg; dsimp only
  split_ifs <;> simp

theorem realizesBounded_pageTailPhysDispatch :
    RealizesBounded .exact pageTailPhysDispatchProg
      (WordEncoding.encode (α := ((PageArenaCtx × (ℕ × ℕ)) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (((ctx, _), base), _) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        base ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hin := realizesBounded_pageTailPhysInner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨sb, t⟩⟩, base⟩, ⟨⟨tc1, tc2⟩, th⟩⟩
    obtain ⟨hv0, hbase⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hsb_w : Fits w sb := hwords 11
    try dsimp only [Fits] at *
    have hm1 : (th + t) % (4 * pg) < 4 * pg := Nat.mod_lt _ (by omega)
    first | exact hv0 | omega)

/-- Translate tail offset `(sideBit, t)` to `st.tailPhys side t` in `O(1)` (`¬ReadsWidth`). -/
def pageTailPhysBoundedProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, t)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let fp ← pageReadFullPagesProg mb
    let tc ← pageReadTailCountsProg mb
    let th ← Memory.read (mb + if sideBit = 0 then 25 else 26)
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then do
        let base ← pure ((fp.1 + fp.2) * pg)
        pageTailPhysDispatchProg (((ctx, (sideBit, t)), base), (tc, th))
      else
        pure 0
    else
      pure 0

@[simp] theorem runClient_state_pageTailPhysBoundedProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageTailPhysBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageTailPhysBoundedProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg,
    prog_runClient_state_read]
  split_ifs <;> simp

theorem realizesBounded_pageTailPhys :
    RealizesBounded .exact pageTailPhysBoundedProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have hrtc := realizesBounded_pageReadTailCounts
  have hdsp := realizesBounded_pageTailPhysDispatch
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, t⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadTailCountsProg] at *
    try simp only [runClient_state_pageReadFullPagesProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    set fp_v := (Memory.spec 0).clientResult s (pageReadFullPagesProg mb)
    have hq0_mul : fp_v.1 * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    try (
      have hq1_mul : fp_v.2 * pg ≤ ((nc - fp_v.1 * pg) / pg) * pg :=
        Nat.mul_le_mul_right pg (by omega)
      have hdiv1 : ((nc - fp_v.1 * pg) / pg) * pg ≤ nc - fp_v.1 * pg :=
        Nat.div_mul_le_self _ pg
      have hsum_mul : (fp_v.1 + fp_v.2) * pg = fp_v.1 * pg + fp_v.2 * pg := Nat.add_mul ..
      have hsum_le : fp_v.1 + fp_v.2 ≤ nc := by
        have := Nat.le_mul_of_pos_right (fp_v.1 + fp_v.2) (by omega : 0 < pg)
        omega)
    omega)

theorem pageTailPhysBoundedProg_eq {L : PageArenaLayout} {s : Memory.State}
    (hv : (extractPagePair L s.mem).Valid)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap)
    (side : Bool) {t : ℕ} (ht : t < (extractPagePair L s.mem).tailCount side) :
    (Memory.spec 0).clientResult s
      (pageTailPhysBoundedProg (L.toCtx, (if side then 1 else 0, t))) =
      (extractPagePair L s.mem).tailPhys side t := by
  set st := extractPagePair L s.mem
  have hB : 0 < L.pgB := hps ▸ hv.pageSize_pos
  have htot_eq := st.totalItems_eq
  rw [hps] at htot_eq
  have hqb_le : (st.fullPages false + st.fullPages true) * L.pgB ≤ L.nCap := by
    change st.totalPages * L.pgB ≤ L.nCap; omega
  have hq0_le : st.fullPages false ≤ L.nCap / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hq1_le : st.fullPages true ≤ (L.nCap - st.fullPages false * L.pgB) / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hth_lt : st.tailHead side < 4 * L.pgB := hps ▸ hv.tailHead_lt side
  have ht_lt4 : t < 4 * L.pgB := ht.trans (hps ▸ hv.tailCount_lt side)
  have hk_lt : st.ringSlot side t < 4 * L.pgB := by
    unfold PagePairState.ringSlot; rw [hps]; exact Nat.mod_lt _ (by omega)
  have hres_lt : st.tailRes side (st.ringSlot side t) < 8 * L.pgB :=
    hps ▸ hv.tailRes_lt side t ht
  have htp_lt : st.tailPhys side t < st.totalItems := hv.tail_lt side t ht
  unfold pageTailPhysBoundedProg pageTailPhysDispatchProg pageTailPhysInnerProg
  dsimp only [PageArenaLayout.toCtx]
  simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
    runClient_state_pageReadFullPagesProg, pageReadFullPagesProg_eq L s,
    runClient_state_pageReadTailCountsProg, pageReadTailCountsProg_eq L s,
    prog_clientResult_read, prog_runClient_state_read, pure_bind]
  have hth_r : s.mem (L.metaBase + if (if side then 1 else 0) = 0 then 25 else 26) =
      st.tailHead side := by cases side <;> rfl
  have hq0_le' : (extractPagePair L s.mem).fullPages false ≤ L.nCap / L.pgB := hq0_le
  have hq1_le' : (extractPagePair L s.mem).fullPages true ≤
      (L.nCap - (extractPagePair L s.mem).fullPages false * L.pgB) / L.pgB := hq1_le
  simp only [hth_r]
  rw [ite_eq_left hq0_le', ite_eq_left hq1_le']
  have hc2a : (extractPagePair L s.mem).tailCount false ≤
      L.nCap - ((extractPagePair L s.mem).fullPages false +
        (extractPagePair L s.mem).fullPages true) * L.pgB := by
    change st.tailCount false ≤ L.nCap - st.totalPages * L.pgB; omega
  have hc2b : (extractPagePair L s.mem).tailCount true ≤
        L.nCap - ((extractPagePair L s.mem).fullPages false +
          (extractPagePair L s.mem).fullPages true) * L.pgB -
          (extractPagePair L s.mem).tailCount false ∧
      st.tailHead side < 4 * L.pgB ∧ t < 4 * L.pgB :=
    ⟨by change st.tailCount true ≤ L.nCap - st.totalPages * L.pgB - st.tailCount false; omega,
      hth_lt, ht_lt4⟩
  rw [ite_eq_left hc2a, ite_eq_left hc2b]
  simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
    runClient_state_pageReadTailResProg]
  have hrs_r : ((extractPagePair L s.mem).tailHead side + t) % (4 * L.pgB) =
      st.ringSlot side t := by
    change (st.tailHead side + t) % (4 * L.pgB) = st.ringSlot side t
    unfold PagePairState.ringSlot; rw [hps]
  have hth_st : st.tailHead side = (extractPagePair L s.mem).tailHead side := rfl
  rw [hth_st, hrs_r]
  have hrtr_eq : (Memory.spec 0).clientResult s
      (pageReadTailResProg (L.toCtx, (if side then 1 else 0, st.ringSlot side t))) =
      st.tailRes side (st.ringSlot side t) := by
    set k0 := st.ringSlot side t
    have hk0 : k0 < 4 * L.pgB := hk_lt
    unfold pageReadTailResProg
    dsimp only [PageArenaLayout.toCtx]
    rw [ite_eq_left hk0]
    change _ = if k0 < 4 * L.pgB then
      readPacked (L.metaBase + L.offTail) L.ptrB L.w s.mem (4 * L.pgB * Bool.rec 0 1 side + k0)
      else 0
    rw [ite_eq_left hk0]
    cases side <;> simp
  dsimp only [PageArenaLayout.toCtx] at hrtr_eq
  rw [hrtr_eq, ite_eq_left hres_lt]
  have htp_def : st.tailPhys side t =
      ((extractPagePair L s.mem).fullPages false +
        (extractPagePair L s.mem).fullPages true) * L.pgB +
        (st.tailRes side (st.ringSlot side t) + 8 * L.pgB -
          (((extractPagePair L s.mem).fullPages false +
            (extractPagePair L s.mem).fullPages true) * L.pgB) % (8 * L.pgB)) % (8 * L.pgB) := by
    unfold PagePairState.tailPhys physOfRes PagePairState.totalPages
    rw [hps]
  have hoff_lt : (st.tailRes side (st.ringSlot side t) + 8 * L.pgB -
      (((extractPagePair L s.mem).fullPages false +
        (extractPagePair L s.mem).fullPages true) * L.pgB) % (8 * L.pgB)) % (8 * L.pgB) <
      (extractPagePair L s.mem).tailCount false +
        (extractPagePair L s.mem).tailCount true := by
    change (st.tailRes side (st.ringSlot side t) + 8 * L.pgB -
      (st.totalPages * L.pgB) % (8 * L.pgB)) % (8 * L.pgB) <
      st.tailCount false + st.tailCount true
    have htp_def' : st.tailPhys side t = st.totalPages * L.pgB +
        (st.tailRes side (st.ringSlot side t) + 8 * L.pgB -
          (st.totalPages * L.pgB) % (8 * L.pgB)) % (8 * L.pgB) := by
      unfold PagePairState.tailPhys physOfRes; rw [hps]
    omega
  rw [ite_eq_left hoff_lt, prog_clientResult_pure, htp_def]

/-- Compute `(extractPageUnperm L s.mem).effCleanPage pRaw u_off` in `O(1)` (`¬ReadsWidth`). -/
def pageEffDemoteInnerProg :
    PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog ℕ
  | (ctx, ((sb, qm1), (pRaw, pLast))) => do
    let pDem ← pageReadPageOfProg (ctx, (sb, qm1))
    pure (if pRaw = pDem then pLast else if pRaw = pLast then pDem else pRaw)

@[simp] theorem runClient_state_pageEffDemoteInnerProg
    (x : PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageEffDemoteInnerProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  unfold pageEffDemoteInnerProg; dsimp only; simp

theorem realizesBounded_pageEffDemoteInner :
    RealizesBounded .exact pageEffDemoteInnerProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrpo := realizesBounded_pageReadPageOf
  realize
  exact h

/-- Guarded active-`demoteSwap` check for `pageEffDemoteBoundedProg` (`¬ReadsWidth`). -/
def pageEffDemoteCheckProg :
    (PageArenaCtx × (ℕ × ℕ)) × ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) → Memory.Prog ℕ
  | ((ctx, (pRaw, u_off)), ((jk, ja), fp)) => do
    let qj ← pure (if ja.1 = 0 then fp.1 else fp.2)
    if jk = 2 ∧ u_off < ja.2 ∧ 0 < qj then do
      let sb ← pure (if ja.1 = 0 then 0 else 1)
      let qm1 ← pure (qj - 1)
      let pLast ← pure (fp.1 + fp.2 - 1)
      pageEffDemoteInnerProg (ctx, ((sb, qm1), (pRaw, pLast)))
    else
      pure pRaw

@[simp] theorem runClient_state_pageEffDemoteCheckProg
    (x : (PageArenaCtx × (ℕ × ℕ)) × ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ))) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageEffDemoteCheckProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩,
    ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩
  unfold pageEffDemoteCheckProg; dsimp only
  simp only [pure_bind]
  split_ifs <;> simp

theorem realizesBounded_pageEffDemoteCheck :
    RealizesBounded .exact pageEffDemoteCheckProg
      (WordEncoding.encode (α := (PageArenaCtx × (ℕ × ℕ)) × ((ℕ × (ℕ × ℕ)) × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, _), (_, fp)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        fp.1 + fp.2 ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hin := realizesBounded_pageEffDemoteInner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨pRaw, uo⟩⟩, ⟨⟨jk, ⟨ja1, ja2⟩⟩, ⟨fp1, fp2⟩⟩⟩
    obtain ⟨hv0, hfp⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hpR : Fits w pRaw := hwords 11
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> first | exact hv0 | omega)

/-- Compute `st.effPage pRaw u_off` during active `demoteSwap` jobs (`¬ReadsWidth`). -/
def pageEffDemoteBoundedProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (pRaw, u_off)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let jk ← Memory.read (mb + 27)
    let ja ← pageReadJobArgsProg mb
    let fp ← pageReadFullPagesProg mb
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then
        pageEffDemoteCheckProg ((ctx, (pRaw, u_off)), ((jk, ja), fp))
      else
        pure pRaw
    else
      pure pRaw

@[simp] theorem runClient_state_pageEffDemoteBoundedProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageEffDemoteBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageEffDemoteBoundedProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read, runClient_state_pageReadJobArgsProg,
    runClient_state_pageReadFullPagesProg]
  split_ifs <;> simp

theorem realizesBounded_pageEffDemote :
    RealizesBounded .exact pageEffDemoteBoundedProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrja := realizesBounded_pageReadJobArgs
  have hrfp := realizesBounded_pageReadFullPages
  have hchk := realizesBounded_pageEffDemoteCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨pRaw, uo⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadFullPagesProg] at *
    try simp only [runClient_state_pageReadJobArgsProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    set fp_v := (Memory.spec 0).clientResult s (pageReadFullPagesProg mb)
    have hq0_mul : fp_v.1 * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    try (
      have hq1_mul : fp_v.2 * pg ≤ ((nc - fp_v.1 * pg) / pg) * pg :=
        Nat.mul_le_mul_right pg (by omega)
      have hdiv1 : ((nc - fp_v.1 * pg) / pg) * pg ≤ nc - fp_v.1 * pg :=
        Nat.div_mul_le_self _ pg
      have hsum_mul : (fp_v.1 + fp_v.2) * pg = fp_v.1 * pg + fp_v.2 * pg := Nat.add_mul ..
      have hsum_le : fp_v.1 + fp_v.2 ≤ nc := by
        have := Nat.le_mul_of_pos_right (fp_v.1 + fp_v.2) (by omega : 0 < pg)
        omega)
    omega)

/-- Compute `u.effCleanPage pRaw u_off` across `cleanPhase = 2` and `demoteSwap` (`¬ReadsWidth`). -/
def pageEffPageBoundedProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (pRaw, u_off)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let ph ← Memory.read (mb + 18)
    let co ← pageReadCleanPosProg mb
    if ph = 2 ∧ 0 < co.2 then
      if u_off < co.2 then do
        let o1 ← pure 1
        let pCur ← pageReadPageOfProg (ctx, (o1, co.1))
        pure (if pRaw = pCur then co.1 else if pRaw = co.1 then pCur else pRaw)
      else
        pure pRaw
    else
      pageEffDemoteBoundedProg (ctx, (pRaw, u_off))

@[simp] theorem runClient_state_pageEffPageBoundedProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageEffPageBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageEffPageBoundedProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    prog_runClient_state_read, runClient_state_pageReadCleanPosProg]
  split_ifs <;> simp

theorem realizesBounded_pageEffPage :
    RealizesBounded .exact pageEffPageBoundedProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrcp := realizesBounded_pageReadCleanPos
  have hrpo := realizesBounded_pageReadPageOf
  have hed := realizesBounded_pageEffDemote
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨pRaw, uo⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadCleanPosProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

/-- Translate a full-page virtual index `idx < fullPages side * pgB` to its physical slot. -/
def pageFullPhysBoundedProg : PageArenaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog ℕ
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), ((sideBit, idx), Q)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let vp ← pure (idx / pg)
    let u_off ← pure (idx % pg)
    let pRaw ← pageReadPageOfProg (ctx, (sideBit, vp))
    let effP ← pageEffPageBoundedProg (ctx, (pRaw, u_off))
    if effP < Q then
      pure (effP * pg + u_off)
    else
      pure 0

@[simp] theorem runClient_state_pageFullPhysBoundedProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageFullPhysBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageFullPhysBoundedProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadPageOfProg, runClient_state_pageEffPageBoundedProg]
  split_ifs <;> simp

theorem realizesBounded_pageFullPhys :
    RealizesBounded .exact pageFullPhysBoundedProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, (_, Q)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        Q * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hrpo := realizesBounded_pageReadPageOf
  have heff := realizesBounded_pageEffPage
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, idx⟩, Q⟩⟩
    obtain ⟨hv0, hQ_nc⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try simp only [runClient_state_pageReadPageOfProg] at *
    have hsb_w : Fits w sb := hwords 11
    have hidx_w : Fits w idx := hwords 12
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hm_pg : idx % pg < pg := Nat.mod_lt idx (by omega)
    have hdiv_idx : idx / pg ≤ idx := Nat.div_le_self idx pg
    (try exact hv0); try omega)
  all_goals (
    have hlt_mul : ∀ {x y : ℕ}, x < y → x * pg + pg ≤ y * pg := fun hx => by
      rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right pg hx
    have := hlt_mul ‹_ < Q›
    omega)

/-- Translate `(sideBit, idx)` to `(extractPageUnperm L s.mem).toPhys side idx` in `O(1)`
(`RealizesBounded .exact`, `¬ReadsWidth`). -/
def pageToPhysBoundedProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, idx)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let fp ← pageReadFullPagesProg mb
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then do
        let qs ← pure (if sideBit = 0 then fp.1 else fp.2)
        if idx < qs * pg then do
          let Q ← pure (fp.1 + fp.2)
          pageFullPhysBoundedProg (ctx, ((sideBit, idx), Q))
        else do
          let tOff ← pure (idx - qs * pg)
          pageTailPhysBoundedProg (ctx, (sideBit, tOff))
      else
        pure 0
    else
      pure 0

@[simp] theorem runClient_state_pageToPhysBoundedProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageToPhysBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageToPhysBoundedProg; dsimp only
  simp only [pure_bind, StateTransitionSpec.clientState, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg]
  split_ifs <;> simp

theorem realizesBounded_pageToPhys :
    RealizesBounded .exact pageToPhysBoundedProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have hfp := realizesBounded_pageFullPhys
  have htp := realizesBounded_pageTailPhys
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, idx⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadFullPagesProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    set fp_v := (Memory.spec 0).clientResult s (pageReadFullPagesProg mb)
    have hq0_mul : fp_v.1 * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    try (
      have hq1_mul : fp_v.2 * pg ≤ ((nc - fp_v.1 * pg) / pg) * pg :=
        Nat.mul_le_mul_right pg (by omega)
      have hdiv1 : ((nc - fp_v.1 * pg) / pg) * pg ≤ nc - fp_v.1 * pg :=
        Nat.div_mul_le_self _ pg
      have hsum_mul : (fp_v.1 + fp_v.2) * pg = fp_v.1 * pg + fp_v.2 * pg := Nat.add_mul ..
      have hsum_le : fp_v.1 + fp_v.2 ≤ nc := by
        have := Nat.le_mul_of_pos_right (fp_v.1 + fp_v.2) (by omega : 0 < pg)
        omega)
    (try split_ifs at *) <;> omega)

theorem pageToPhysBoundedProg_spec {L : PageArenaLayout} {s : Memory.State} {slack : ℕ}
    (hi : (extractPageUnperm L s.mem).InvWithSlack slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hmp : (extractPagePair L s.mem).totalPages < L.maxPages)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap)
    (side : Bool) {idx : ℕ} (hidx : idx < (extractPagePair L s.mem).virtLen side) :
    (Memory.spec 0).clientResult s
      (pageToPhysBoundedProg (L.toCtx, (if side then 1 else 0, idx))) =
      (extractPageUnperm L s.mem).toPhys side idx ∧
    (Memory.spec 0).clientState s
      (pageToPhysBoundedProg (L.toCtx, (if side then 1 else 0, idx))) = s := by
  refine ⟨?_, by simpa only [StateTransitionSpec.clientState] using
    runClient_state_pageToPhysBoundedProg (L.toCtx, (if side then 1 else 0, idx)) s⟩
  set u := extractPageUnperm L s.mem
  set st := extractPagePair L s.mem
  have hv := hi.valid
  have hB : 0 < L.pgB := hps ▸ hv.pageSize_pos
  have htot_eq := st.totalItems_eq; rw [hps] at htot_eq
  have hqb_le : (st.fullPages false + st.fullPages true) * L.pgB ≤ L.nCap := by
    change st.totalPages * L.pgB ≤ L.nCap; omega
  have hq0_le : st.fullPages false ≤ L.nCap / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hq1_le : st.fullPages true ≤ (L.nCap - st.fullPages false * L.pgB) / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  unfold pageToPhysBoundedProg pageFullPhysBoundedProg
  dsimp only [PageArenaLayout.toCtx]
  simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
    runClient_state_pageReadFullPagesProg, pageReadFullPagesProg_eq L s, pure_bind]
  have hq0_le' : (extractPagePair L s.mem).fullPages false ≤ L.nCap / L.pgB := hq0_le
  have hq1_le' : (extractPagePair L s.mem).fullPages true ≤
      (L.nCap - (extractPagePair L s.mem).fullPages false * L.pgB) / L.pgB := hq1_le
  rw [ite_eq_left hq0_le', ite_eq_left hq1_le']
  have hqs_eq : (if (if side then 1 else 0) = 0 then (extractPagePair L s.mem).fullPages false
      else (extractPagePair L s.mem).fullPages true) = st.fullPages side := by
    cases side <;> rfl
  rw [hqs_eq]
  have hust : u.st = st := rfl
  by_cases hlt : idx < st.fullPages side * L.pgB
  · rw [ite_eq_left hlt]
    have hvp_lt : idx / L.pgB < st.fullPages side := (Nat.div_lt_iff_lt_mul hB).mpr hlt
    have hvp_mp : idx / L.pgB < L.maxPages :=
      (hvp_lt.trans_le (by unfold PagePairState.totalPages; cases side <;> omega)).trans hmp
    have hpOF := pageReadPageOfProg_eq side hvp_mp s
    dsimp only [PageArenaLayout.toCtx] at hpOF
    simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
      runClient_state_pageReadPageOfProg, hpOF, runClient_state_pageEffPageBoundedProg]
    have hp_s := hv.page_lt side (idx / L.pgB) hvp_lt
    set pRaw := st.pageOf side (idx / L.pgB)
    have heff_eq : (Memory.spec 0).clientResult s
        (pageEffPageBoundedProg
          (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
            (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)),
          (pRaw, idx % L.pgB))) =
        u.effCleanPage pRaw (idx % L.pgB) ∧
        u.effCleanPage pRaw (idx % L.pgB) <
          (extractPagePair L s.mem).fullPages false +
            (extractPagePair L s.mem).fullPages true := by
      unfold pageEffPageBoundedProg pageEffDemoteBoundedProg pageEffDemoteCheckProg
        pageEffDemoteInnerProg PageUnpermState.effCleanPage
      dsimp only
      have hph_r : s.mem (L.metaBase + 18) = u.cleanPhase := rfl
      simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
        prog_clientResult_read, prog_runClient_state_read, hph_r,
        runClient_state_pageReadCleanPosProg, pageReadCleanPosProg_eq L s]
      by_cases hcs : u.cleanPhase = 2 ∧ 0 < u.cleanOff
      · have hcs' : u.cleanPhase = 2 ∧ 0 < (extractPageUnperm L s.mem).cleanOff := hcs
        rw [ite_eq_left hcs', ite_eq_left hcs]
        obtain ⟨_, hcvp_lt, _, _, _⟩ := hi.phase2_pos hcs.1 hcs.2
        obtain ⟨hf0, _⟩ := hi.src_empty (by omega)
        rw [hust] at hcvp_lt hf0
        have hcvp_mp : u.cleanVp < L.maxPages :=
          (hcvp_lt.trans_le (by unfold PagePairState.totalPages; omega)).trans hmp
        have hp_c := hv.page_lt true u.cleanVp hcvp_lt
        by_cases hu_lt : idx % L.pgB < u.cleanOff
        · have hu_lt' : idx % L.pgB < (extractPageUnperm L s.mem).cleanOff := hu_lt
          rw [ite_eq_left hu_lt', ite_eq_left hu_lt]
          have hpCur_eq := pageReadPageOfProg_eq true hcvp_mp s
          simp only [↓reduceIte, PageArenaLayout.toCtx] at hpCur_eq
          have hcvp_u : (extractPageUnperm L s.mem).cleanVp = u.cleanVp := rfl
          rw [hcvp_u]
          simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
            prog_runClient_state_pure, prog_clientResult_pure,
            runClient_state_pageReadPageOfProg, hpCur_eq]
          refine ⟨rfl, ?_⟩
          split_ifs
          · exact hcvp_lt.trans_le (Nat.le_add_left _ _)
          · exact hp_c
          · exact hp_s
        · have hu_lt' : ¬(idx % L.pgB < (extractPageUnperm L s.mem).cleanOff) := hu_lt
          rw [ite_eq_right hu_lt', ite_eq_right hu_lt, prog_clientResult_pure]
          exact ⟨rfl, hp_s⟩
      · have hcs' : ¬(u.cleanPhase = 2 ∧ 0 < (extractPageUnperm L s.mem).cleanOff) := hcs
        rw [ite_eq_right hcs', ite_eq_right hcs]
        have hja_eq : (Memory.spec 0).clientResult s (pageReadJobArgsProg L.metaBase) =
            (s.mem (L.metaBase + 28), s.mem (L.metaBase + 29)) := by
          simp [pageReadJobArgsProg]
        simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
          prog_clientResult_read, prog_runClient_state_read,
          runClient_state_pageReadJobArgsProg, hja_eq,
          runClient_state_pageReadFullPagesProg, pageReadFullPagesProg_eq L s]
        set jk := s.mem (L.metaBase + 27)
        set js := s.mem (L.metaBase + 28)
        set jcur := s.mem (L.metaBase + 29)
        have hj_eq : st.job = decodePageJob jk js jcur := rfl
        rw [ite_eq_left hq0_le', ite_eq_left hq1_le']
        simp only [pure_bind]
        by_cases hjk2 : s.mem (L.metaBase + 27) = 2 ∧ idx % L.pgB < s.mem (L.metaBase + 29) ∧
            0 < (if s.mem (L.metaBase + 28) = 0 then (extractPagePair L s.mem).fullPages false
              else (extractPagePair L s.mem).fullPages true)
        · rw [ite_eq_left hjk2]
          set sj := decide (js ≠ 0)
          have hqj_eq : (if s.mem (L.metaBase + 28) = 0 then
              (extractPagePair L s.mem).fullPages false
              else (extractPagePair L s.mem).fullPages true) = st.fullPages sj := by
            dsimp only [sj, js]; by_cases hz : s.mem (L.metaBase + 28) = 0 <;> simp [hz, st]
          have hsb_eq : (if s.mem (L.metaBase + 28) = 0 then 0 else 1) =
              (if sj then 1 else 0) := by
            dsimp only [sj, js]; by_cases hz : s.mem (L.metaBase + 28) = 0 <;> simp [hz]
          have hqj_pos : 0 < st.fullPages sj := hqj_eq ▸ hjk2.2.2
          have hqm1_mp : st.fullPages sj - 1 < L.maxPages :=
            ((Nat.sub_lt hqj_pos Nat.one_pos).trans_le
              (by unfold PagePairState.totalPages; cases sj <;> omega)).trans hmp
          have hpDem_eq := pageReadPageOfProg_eq sj hqm1_mp s
          dsimp only [PageArenaLayout.toCtx] at hpDem_eq
          rw [hsb_eq, hqj_eq]
          simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
            runClient_state_pageReadPageOfProg, prog_clientResult_pure, hpDem_eq]
          have hj_ds : st.job = .demoteSwap sj jcur := by
            rw [hj_eq]; unfold decodePageJob
            simp only [jk, js, hjk2.1, Nat.reduceEqDiff, ↓reduceIte, sj]
          rw [hust]
          unfold PagePairState.effPage
          have hc_eff : idx % L.pgB < jcur ∧ 0 < st.fullPages sj := ⟨hjk2.2.1, hqj_pos⟩
          rw [hj_ds]
          dsimp only
          rw [ite_eq_left hc_eff]
          refine ⟨rfl, ?_⟩
          have hQ_pos : 0 < st.totalPages := by
            unfold PagePairState.totalPages
            rcases Bool.eq_false_or_eq_true sj with hsj | hsj <;> (rw [hsj] at hqj_pos; omega)
          split_ifs
          · exact Nat.sub_lt hQ_pos Nat.one_pos
          · exact hv.page_lt sj (st.fullPages sj - 1) (Nat.sub_lt hqj_pos Nat.one_pos)
          · exact hp_s
        · rw [ite_eq_right hjk2, prog_clientResult_pure, hust]
          have heff_id : st.effPage pRaw (idx % L.pgB) = pRaw := by
            unfold PagePairState.effPage
            rw [hj_eq]; unfold decodePageJob; dsimp only [jk, js, jcur]
            by_cases h1 : s.mem (L.metaBase + 27) = 1
            · simp [h1]
            · by_cases h2 : s.mem (L.metaBase + 27) = 2
              · simp only [h2, Nat.reduceEqDiff, ↓reduceIte]
                by_cases hc_and : idx % L.pgB < s.mem (L.metaBase + 29) ∧
                    0 < st.fullPages (decide (s.mem (L.metaBase + 28) ≠ 0))
                · exfalso; apply hjk2
                  refine ⟨h2, hc_and.1, ?_⟩
                  have hq_pos := hc_and.2
                  split_ifs with hz <;> simpa [hz, st] using hq_pos
                · rw [ite_eq_right hc_and]
              · by_cases h3 : s.mem (L.metaBase + 27) = 3 <;> simp [h1, h2, h3]
          rw [heff_id]
          exact ⟨rfl, hp_s⟩
    rw [heff_eq.1, ite_eq_left heff_eq.2, prog_clientResult_pure]
    unfold PageUnpermState.toPhys
    rw [hust, hps, ite_eq_left hlt]
  · rw [ite_eq_right hlt]
    change _ = u.toPhys side idx
    unfold PageUnpermState.toPhys
    rw [hust, hps, ite_eq_right hlt]
    have ht_lt : idx - st.fullPages side * L.pgB < st.tailCount side := by
      unfold PagePairState.virtLen at hidx; rw [hps] at hidx; omega
    exact pageTailPhysBoundedProg_eq hv hps hti side ht_lt

/-- Read `(q, v)` at virtual coordinate `(sideBit, idx)` in `O(1)` (`RealizesBounded .exact`,
`¬ReadsWidth`). -/
def pageReadVirtBoundedProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, idx)) => do
    let p ← pageToPhysBoundedProg
      (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, idx))
    if p < nc then
      readPairGenProg (((ib, (qb, vb)), wv), p)
    else
      pure (0, 0)

@[simp] theorem runClient_state_pageReadVirtBoundedProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageReadVirtBoundedProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageReadVirtBoundedProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    runClient_state_pageToPhysBoundedProg]
  split_ifs <;> [exact clientState_readPairGenProg ..; rfl]

theorem realizesBounded_pageReadVirt :
    RealizesBounded .exact pageReadVirtBoundedProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have htp := realizesBounded_pageToPhys
  have hrp := realizesBounded_readPairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, idx⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, _, hqb, hvb, _, _, _, _, _, _, _, _, _, hib_fr⟩ := h
    subst hwv
    try simp only [runClient_state_pageToPhysBoundedProg] at *
    try exact hv0)
  all_goals (
    have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw ‹_ < nc›
    exact ⟨hw, rfl, hqb, hvb, by omega⟩)

theorem pageReadVirtBoundedProg_spec {L : PageArenaLayout} {s : Memory.State} {slack : ℕ}
    (hi : (extractPageUnperm L s.mem).InvWithSlack slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hmp : (extractPagePair L s.mem).totalPages < L.maxPages)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap)
    (side : Bool) {idx : ℕ} (hidx : idx < (extractPagePair L s.mem).virtLen side) :
    (Memory.spec 0).clientResult s
      (pageReadVirtBoundedProg (L.toCtx, (if side then 1 else 0, idx))) =
      (extractPageUnperm L s.mem).virtAt (arenaPairAt L s.mem) side idx ∧
    (Memory.spec 0).clientState s
      (pageReadVirtBoundedProg (L.toCtx, (if side then 1 else 0, idx))) = s := by
  obtain ⟨hres, hst⟩ := pageToPhysBoundedProg_spec hi hps hmp hti side hidx
  have hp_lt : (extractPageUnperm L s.mem).toPhys side idx < L.nCap :=
    (hi.toPhys_lt hidx).trans_le hti
  unfold pageReadVirtBoundedProg
  dsimp only [PageArenaLayout.toCtx] at hres hst ⊢
  rw [prog_clientResult_bind, StateTransitionSpec.clientState_bind, hst, hres, ite_eq_left hp_lt]
  exact ⟨clientResult_readPairGenProg .., clientState_readPairGenProg ..⟩

/-- Write `(q, v)` at virtual coordinate `(sideBit, idx)` in `O(1)` (`RealizesBounded .exact`,
`¬ReadsWidth`). -/
def pageWriteVirtBoundedProg : (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, idx)), qv) => do
    let p ← pageToPhysBoundedProg
      (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sideBit, idx))
    if p < nc then
      writePairGenProg ((((ib, (qb, vb)), wv), p), qv)
    else
      pure ()

theorem realizesBounded_pageWriteVirt :
    RealizesBounded .exact pageWriteVirtBoundedProg
      (WordEncoding.encode (α := (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have htp := realizesBounded_pageToPhys
  have hwp := realizesBounded_writePairGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, idx⟩⟩,
      qv⟩
    have hv0 := h
    obtain ⟨hw, hwv, _, hqb, hvb, _, _, _, _, _, _, _, _, _, hib_fr⟩ := h
    subst hwv
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_state_pageToPhysBoundedProg] at *
    try exact hv0)
  all_goals (
    have hlt := wOffV_add_one_lt_pairStreamWords (q_bits := qb) (v_bits := vb) hw ‹_ < nc›
    exact ⟨hw, rfl, hqb, hvb, by omega⟩)

theorem pageWriteVirtBoundedProg_spec {L : PageArenaLayout} {s : Memory.State} {slack : ℕ}
    (hvL : L.Valid L.w s.frontier)
    (hi : (extractPageUnperm L s.mem).InvWithSlack slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hmp : (extractPagePair L s.mem).totalPages < L.maxPages)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap)
    (side : Bool) {idx q v : ℕ} (hidx : idx < (extractPagePair L s.mem).virtLen side)
    (hq : q < 2 ^ L.qBits) (hv_lt : v < 2 ^ L.vBits) :
    let s' := (Memory.spec 0).clientState s
      (pageWriteVirtBoundedProg ((L.toCtx, (if side then 1 else 0, idx)), (q, v)))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = extractPageUnperm L s.mem ∧
    ∀ (s₂ : Bool) (idx₂ : ℕ), idx₂ < (extractPagePair L s.mem).virtLen s₂ →
      (extractPageUnperm L s'.mem).virtAt (arenaPairAt L s'.mem) s₂ idx₂ =
        if s₂ = side ∧ idx₂ = idx then (q, v)
        else (extractPageUnperm L s.mem).virtAt (arenaPairAt L s.mem) s₂ idx₂ := by
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hvL
  obtain ⟨hres, hst⟩ := pageToPhysBoundedProg_spec hi hps hmp hti side hidx
  set u := extractPageUnperm L s.mem
  have hp_lt : u.toPhys side idx < L.nCap := (hi.toPhys_lt hidx).trans_le hti
  have hs'_eq : (Memory.spec 0).clientState s
      (pageWriteVirtBoundedProg ((L.toCtx, (if side then 1 else 0, idx)), (q, v))) =
      { mem := writePair L.itemBase L.qBits L.vBits L.w s.mem (u.toPhys side idx) q v
        frontier := s.frontier } := by
    unfold pageWriteVirtBoundedProg
    dsimp only [PageArenaLayout.toCtx] at hres hst ⊢
    rw [StateTransitionSpec.clientState_bind, hst, hres, ite_eq_left hp_lt]
    exact clientState_writePairGenProg ..
  dsimp only
  rw [hs'_eq]
  have hu_pres := extractPageUnperm_writePair hw hm_ib ho1 ho2 s.mem (u.toPhys side idx) q v
  refine ⟨rfl, hu_pres, fun s₂ idx₂ hidx₂ => ?_⟩
  rw [hu_pres]
  by_cases heq : s₂ = side ∧ idx₂ = idx
  · obtain ⟨rfl, rfl⟩ := heq
    have hself : s₂ = s₂ ∧ idx₂ = idx₂ := ⟨rfl, rfl⟩
    rw [ite_eq_left hself]
    unfold PageUnpermState.virtAt arenaPairAt
    exact Prod.ext (pairQuotAt_writePair_self hw s.mem hq) (pairValAt_writePair_self s.mem hv_lt)
  · rw [ite_eq_right heq]
    have hp_ne : u.toPhys s₂ idx₂ ≠ u.toPhys side idx := fun hp =>
      heq (hi.toPhys_inj hidx₂ hidx hp)
    unfold PageUnpermState.virtAt arenaPairAt
    exact Prod.ext (pairQuotAt_writePair_of_ne hw s.mem hp_ne)
      (pairValAt_writePair_of_ne hw s.mem hp_ne)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

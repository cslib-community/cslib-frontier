/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigrateSlotRw
-- Retain private `import all` solely to access private metadata confinement helpers in
-- `MigrateSlotRw` and unfold unexposed `Memory.Prog` bodies in the large-epoch modules.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigrateSlotRw
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochCtx
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochSubEpoch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFast
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch
import Mathlib.Tactic.Ring

/-!
# Phase-`8` Source-Slot Draining Congruence (`MigrateSlotCongr`)

This module lifts `MigrateSlotRw` and `MigratePoolCongr` to the unified `pBase`-addressed source
epoch operations (`epochDeleteProg`, `epochPopAnyProg`) on `EpochSlotInv` during Phase `8`:

* Deleting from or popping any element out of a draining source slot (`io.sideBit = 0`) returns
  identical `(u, v)` pairs and preserves `SlotStateCoupled` across any two states agreeing on
  `SlotSrcMetaRegion` and `slotIoPairAt io`.

## Main definitions

* `SlotSrcMetaRegion`: non-item metadata + `pBase` parameter-table envelope of an epoch slot.

## Main results

* `epochDelete_src_coupled`, `epochPopAny_src_coupled`: Phase-`8` source-slot `SlotCoupledStep`
  theorems on `EpochSlotInv`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_clientResult_read prog_runClient_state_read

/-- Non-item metadata + `pBase` parameter-table envelope of an epoch slot (disjoint from
`io.OwnsAddr`). -/
@[expose] def SlotSrcMetaRegion (c w pBase metaBase nCap addr : ℕ) : Prop :=
  (pBase ≤ addr ∧ addr < pBase + 64) ∨
  slotOwnsNonPageMeta c w metaBase nCap addr

private theorem fastReadMeta_sub_slotSrcMeta {c U V w pBase metaBase nCap : ℕ}
    {io : SlotIoLayout} (hne : nCap ≠ 0) (addr : ℕ)
    (ha : FastReadMeta ⟨c, U, V, w, nCap, metaBase, pBase, io⟩ addr) :
    SlotSrcMetaRegion c w pBase metaBase nCap addr := by
  rcases ha with hp | h0 | h32
  · exact Or.inl hp
  · exact Or.inr (Or.inl ⟨h0.1, by simp only [hne, ↓reduceIte]; exact h0.2⟩)
  · exact Or.inr (Or.inr ⟨hne, h32⟩)

/-- Lift `EpochSlotInv` from `s₁` to a coupled state `s₂` via `EpochSlotInv.transfer_io`. -/
private theorem epochSlotInv_of_coupled {c U V w pBase metaBase : ℕ} {M : ℕ → Prop}
    {io : SlotIoLayout} {draining : Bool} {sl : SlotLatent c U V} {s₁ s₂ : Memory.State}
    (h₁ : EpochSlotInv c U V w s₁.frontier pBase metaBase io 0 draining sl s₁.mem)
    (hsub : ∀ addr, SlotSrcMetaRegion c w pBase metaBase sl.nCap addr → M addr)
    (hc : SlotStateCoupled M io (s₁.mem (metaBase + 1)) s₁ s₂) :
    EpochSlotInv c U V w s₂.frontier pBase metaBase io 0 draining sl s₂.mem := by
  have hp_eq : ∀ a, pBase ≤ a → a < pBase + 64 → s₂.mem a = s₁.mem a :=
    fun a h1 h2 => (hc.mem_eq a (hsub a (Or.inl ⟨h1, h2⟩))).symm
  have hm_eq : ∀ a, slotOwnsNonPageMeta c w metaBase sl.nCap a → s₂.mem a = s₁.mem a :=
    fun a ha => (hc.mem_eq a (hsub a (Or.inr ha))).symm
  have hraw := h₁; unfold EpochSlotInv at hraw
  have hs₁_fr : EpochSlotInv c U V w s₁.frontier pBase metaBase io 0 draining sl s₂.mem := by
    refine h₁.transfer_io h₁.io_valid ?_ ⟨fun h0 => ?_, fun h0 => ?_⟩ ?_
      ⟨fun h0 => ?_, fun h0 => ?_⟩ (fun a h1 h2 => ?_) (fun a ha => ?_) hm_eq hc.inv₂
      (fun p hp => (hc.pair_eq p hp).symm)
    · by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw; obtain ⟨_, _, hv, _, _, _⟩ := hraw; exact hv.w_eq.symm
      · rw [ite_eq_right h0] at hraw; obtain ⟨hv, _⟩ := hraw; exact hv.w_eq_io.symm
    · rw [ite_eq_left h0] at hraw; obtain ⟨_, _, hv, _, _, _⟩ := hraw; exact hv.qBits_eq
    · rw [ite_eq_right h0] at hraw; obtain ⟨hv, _⟩ := hraw; exact hv.qBits_le
    · by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw; obtain ⟨_, _, hv, _, _, _⟩ := hraw; exact hv.vBits_eq
      · rw [ite_eq_right h0] at hraw; obtain ⟨hv, _⟩ := hraw; exact hv.vBits_eq
    · rw [ite_eq_left h0] at hraw; obtain ⟨_, _, _, hpt, _, _⟩ := hraw; exact hpt.congr hp_eq
    · rw [ite_eq_right h0] at hraw; obtain ⟨_, ⟨hpt, _⟩, _⟩ := hraw
      exact hpt.congr fun a h1 h2 => hp_eq a h1 (by dsimp only at h1 h2; omega)
    · by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw; obtain ⟨_, _, _, _, hdisj, _⟩ := hraw
        exact fun hia => hdisj a h1 h2 (Or.inr (Or.inr hia))
      · rw [ite_eq_right h0] at hraw; obtain ⟨hv, _⟩ := hraw; exact hv.disj_pBase_io a h1 h2
    · unfold slotOwnsNonPageMeta at ha
      by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw ha
        obtain ⟨_, _, hv, _, _, _⟩ := hraw
        rcases ha with ⟨h1, h2⟩ | ⟨hne, _⟩
        · have hd := hv.disjoint_hdr a; dsimp only at hd; exact hd (by omega)
        · exact absurd h0 hne
      · rw [ite_eq_right h0] at hraw ha; obtain ⟨hv, _⟩ := hraw
        exact hv.disj_fast_io a (ha.imp id And.right)
  exact hc.fr_eq ▸ hs₁_fr

private theorem extractBlockPool_eq_of_coupled {M : ℕ → Prop} {w fr : ℕ} {fl : FastEpochLayout}
    {s₁ s₂ : Memory.State} (hv : fl.Valid w fr)
    (hRM : ∀ addr, FastReadMeta fl addr → M addr)
    (hmem : ∀ addr, M addr → s₁.mem addr = s₂.mem addr) :
    extractBlockPool fl.mp s₂.mem = extractBlockPool fl.mp s₁.mem := by
  obtain ⟨_, _, hbmM⟩ := bpMetaConf_fast hv
  have hmv := hv.mp_valid
  have h16 := hmv.sixteen_MK_le_maxTail
  rw [Nat.mul_assoc] at h16
  have hmk_le : fl.mp.M * fl.mp.K ≤ fl.mp.maxTail :=
    Nat.le_of_mul_le_mul_left h16 (by decide : 0 < 16)
  have hw_mp : 0 < fl.mp.w := by
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout]
    exact hv.w_eq ▸ hv.w_pos
  exact extractBlockPool_congr (mp := fl.mp) hw_mp hmv.K_ge hmk_le
    fun addr ha => (hmem addr (hRM addr (writeMeta_sub_readMeta addr
      (hbmM addr (by rwa [BpMetaLayout.ofCtx_toCtx]))))).symm

private theorem fastSwapLastDown_coupled {M : ℕ → Prop} {w : ℕ} {fl : FastEpochLayout}
    {b delLoc lastLoc : ℕ} {s₁ s₂ : Memory.State}
    (hr : FastLayoutReady w fl s₁)
    (hRM : ∀ addr, FastReadMeta fl addr → M addr)
    (hcv : (extractBlockPool fl.mp s₁.mem).CoreValid)
    (hn_le : (extractBlockPool fl.mp s₁.mem).nSide ≤ fl.mp.nCap)
    (hb : b < fl.mp.M)
    (hlast : lastLoc < (extractBlockPool fl.mp s₁.mem).bktCount b)
    (hc : SlotStateCoupled M fl.io (extractBlockPool fl.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M fl.io (extractBlockPool fl.mp s₁.mem).nSide s₁ s₂
      (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) := by
  have htr := FastTableReady.of_ready hr
  have hbm : BpMetaConf M fl.mp.toCtx := by
    obtain ⟨h1, h2, h3⟩ := bpMetaConf_fast htr.valid
    exact ⟨h1, h2, fun addr ha => hRM addr (writeMeta_sub_readMeta addr (h3 addr ha))⟩
  unfold fastSwapLastDownProg
  refine SlotCoupledStep.ite_prog (fun hdl => ?_) (fun _ => SlotCoupledStep.pure_prog hc ())
  have hdel : delLoc < (extractBlockPool fl.mp s₁.mem).bktCount b := lt_trans hdl hlast
  have hrdAt : SlotCoupledStep M fl.io (extractBlockPool fl.mp s₁.mem).nSide s₁ s₂
      (fastBpReadAtProg (fl.pBase, (b, lastLoc))) := by
    unfold fastBpReadAtProg
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_rwConfined hc (rw_loadBlockPoolCtx (W := FastWriteMeta fl) htr)
        writeMeta_sub_readMeta hRM)
      (clientState_loadBlockPoolCtxProg _ s₁) (clientResult_loadBlockPoolCtxProg htr.pt)
      fun hc_l => ?_
    have hcs := bpReadAtRaw_coupled (bpL := fl.bpL) hbm hcv hn_le hb hlast hc_l
    unfold bpReadAtRawProg at hcs
    exact hcs
  have htp_lt := hcv.toPhys_lt hb hlast
  obtain ⟨hpair_r, _⟩ := slotIoReadProg_spec hc.inv₁ htp_lt
  unfold slotIoReadProg at hpair_r
  have hrd_res : (Memory.spec 0).clientResult s₁ (fastBpReadAtProg (fl.pBase, (b, lastLoc))) =
      slotIoPairAt fl.io s₁.mem ((extractBlockPool fl.mp s₁.mem).toPhys b lastLoc) := by
    unfold fastBpReadAtProg; dsimp only
    rw [StateTransitionSpec.clientResult_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg htr.pt]
    dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
    rw [StateTransitionSpec.clientResult_bind, clientState_bpToPhysProg,
      bpToPhysProg_spec hcv hn_le hb hlast]
    exact hpair_r
  obtain ⟨hq_lt, hv_lt⟩ :=
    slotIoPairAt_bounds (io := fl.io) s₁.mem ((extractBlockPool fl.mp s₁.mem).toPhys b lastLoc)
  refine SlotCoupledStep.bind_readOnly_eq hrdAt (clientState_fastBpReadAtProg _ s₁) hrd_res
    fun hc1 => ?_
  refine SlotCoupledStep.bind_readOnly
    (SlotCoupledStep.of_rwConfined hc1 (rw_fastFeistelRecon htr) writeMeta_sub_readMeta hRM)
    (clientState_fastFeistelReconProg _ s₁) fun hc2 => ?_
  set qv := slotIoPairAt fl.io s₁.mem ((extractBlockPool fl.mp s₁.mem).toPhys b lastLoc)
  have hqv_eta : (qv.1, qv.2) = qv := Prod.eta qv
  have htr_w : FastTableReady w fl
      ((Memory.spec 0).clientState s₁ (fastBpWriteAtProg ((fl.pBase, (b, delLoc)), qv))) := by
    rw [← hqv_eta]
    exact FastTableReady.of_ready
      (fastBpWriteAtProg_ready (b := b) (loc := delLoc) (q := qv.1) (v := qv.2) hr).2.1
  refine SlotCoupledStep.bind_prog (n₂ := (extractBlockPool fl.mp s₁.mem).nSide) ?_ fun hc3 =>
    SlotCoupledStep.of_rwConfined hc3
      (rw_fastRelocLast (b := b) (delLoc := delLoc) (lastLoc := lastLoc) htr_w)
      writeMeta_sub_readMeta hRM
  unfold fastBpWriteAtProg
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_rwConfined hc2 (rw_loadBlockPoolCtx (W := FastWriteMeta fl) htr)
      writeMeta_sub_readMeta hRM)
    (clientState_loadBlockPoolCtxProg _ s₁) (clientResult_loadBlockPoolCtxProg htr.pt)
    fun hc_l => ?_
  rw [← hqv_eta]
  exact bpWriteAtRaw_coupled (bpL := fl.bpL) hbm hcv hn_le hb hdel hq_lt hv_lt hc_l

private theorem fastRemoveAt_coupled {M : ℕ → Prop} {w : ℕ} {fl : FastEpochLayout}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {b delLoc : ℕ} {s₁ s₂ : Memory.State} (u : Fin fl.U)
    (hv : fl.Valid w s₁.frontier)
    (hinv : FastEpochInv fl 0 seeds s₁.mem s_abs)
    (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s₁.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s₁.mem b delLoc = u.val)
    (hRM : ∀ addr, FastReadMeta fl addr → M addr)
    (hc : SlotStateCoupled M fl.io (extractBlockPool fl.mp s₁.mem).nSide s₁ s₂) :
    SlotCoupledStep M fl.io ((extractBlockPool fl.mp s₁.mem).nSide - 1) s₁ s₂
      (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val))) := by
  have hr0 := hinv.ready hv rfl
  have htr0 := FastTableReady.of_ready hr0
  obtain ⟨hbal0, _, _⟩ := hinv.bp_inv
  have hcv0 := hbal0.core
  set bp := extractBlockPool fl.mp s₁.mem
  set cnt := bp.bktCount b
  set lastLoc := cnt - 1
  have hcnt_pos : 0 < cnt := Nat.zero_lt_of_lt hdel
  have hlast_eq : cnt = lastLoc + 1 := by omega
  have hdel_le : delLoc ≤ lastLoc := by omega
  have hlast_lt : lastLoc < cnt := by omega
  have hm11_r : (Memory.spec 0).clientResult s₁ (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := htr0.pt 11 (by decide)
  obtain ⟨hcnt_r, _⟩ := fastReadBktCntProg_spec hr0 hcv0 hb
  obtain ⟨uLast, vLast, huL, hvL, _, hqL, _⟩ := hinv.bktSlot_refines hb hlast_lt
  have hne_last : ∀ loc' < lastLoc, loc' ≠ delLoc →
      fastKeyAt fl seeds.bkt s₁.mem b loc' ≠ uLast.val := fun loc' hl' _ heq => by
    have hloc'_lt : loc' < cnt := lt_trans hl' hlast_lt
    obtain ⟨u', _, hu', _, _, hq_u', _⟩ := hinv.bktSlot_refines hb hloc'_lt
    have hu_e : u' = uLast := Fin.ext (hu'.trans heq)
    have hq_e : (slotIoPairAt fl.io s₁.mem (bp.toPhys b loc')).1 =
        (slotIoPairAt fl.io s₁.mem (bp.toPhys b lastLoc)).1 := by
      change (bpPairAt fl.bpL s₁.mem b loc').1 = (bpPairAt fl.bpL s₁.mem b lastLoc).1
      rw [← hq_u', hu_e, hqL]
    have hp1 := hcv0.toPhys_lt hb hloc'_lt
    have hp2 := hcv0.toPhys_lt hb hlast_lt
    have how1 : (bp.ownerOf (bp.toPhys b loc')).1 = b :=
      congrArg Prod.fst (hcv0.ownerOf_toPhys hb hloc'_lt)
    have how2 : (bp.ownerOf (bp.toPhys b lastLoc)).1 = b :=
      congrArg Prod.fst (hcv0.ownerOf_toPhys hb hlast_lt)
    have hpe := hinv.refines.slot_inj _ hp1 _ hp2 (how1.trans how2.symm) hq_e
    have hle : ((extractBlockPool fl.bpL.mp s₁.mem).ownerOf
        ((extractBlockPool fl.bpL.mp s₁.mem).toPhys b loc')).2 =
        ((extractBlockPool fl.bpL.mp s₁.mem).ownerOf
        ((extractBlockPool fl.bpL.mp s₁.mem).toPhys b lastLoc)).2 :=
      congrArg (fun x => ((extractBlockPool fl.bpL.mp s₁.mem).ownerOf x).2) hpe
    rw [hcv0.ownerOf_toPhys hb hloc'_lt, hcv0.ownerOf_toPhys hb hlast_lt] at hle
    exact (Nat.ne_of_lt hl') hle
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have seed_bkt_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s₁.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt m := fun m hm =>
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
        (by dsimp only [FastEpochLayout.bktHashBase] at h2
            unfold offBktMeta offFpHash offBktHash at *; omega))
  have seed_fp_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s₁.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp m := fun m hm =>
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.N := Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  obtain ⟨_, hr1, _, hbp1, _, _, _, hoi1, hof1, _, _, ht1⟩ :=
    fastUnindexAtProg_spec u hv (hinv.toGen 0) hb hdel hk_u
  generalize hs1_def : (Memory.spec 0).clientState s₁
    (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val)) = stA₁
    at hr1 hbp1 hoi1 hof1 ht1
  have hbp_inv1 : fl.bpL.StateInv 0 stA₁.mem := bpStateInv_congr_io hv hinv.bp_inv hbp1 hoi1
  have ⟨hbal1, hn_le1, _⟩ := hbp_inv1
  have hpair1_eq : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
      bpPairAt fl.bpL stA₁.mem b' loc' = bpPairAt fl.bpL s₁.mem b' loc' := fun b' hb' loc' hl' =>
    bpPairAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb' hl'
  have hkey1_eq : ∀ b' < numBucketsWhp fl.N, ∀ loc' < bp.bktCount b',
      fastKeyAt fl seeds.bkt stA₁.mem b' loc' = fastKeyAt fl seeds.bkt s₁.mem b' loc' :=
    fun b' hb' loc' hl' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb' hl'
  have hlast_ref1 : ∃ (uLast' : Fin fl.U) (vLast' : Fin fl.V),
      uLast'.val = fastKeyAt fl seeds.bkt stA₁.mem b lastLoc ∧
      vLast'.val = (bpPairAt fl.bpL stA₁.mem b lastLoc).2 ∧
      keyQuotient (bWhp fl.N) uLast'.val = (bpPairAt fl.bpL stA₁.mem b lastLoc).1 ∧
      ∀ loc' < lastLoc, loc' ≠ delLoc → fastKeyAt fl seeds.bkt stA₁.mem b loc' ≠ uLast'.val :=
    ⟨uLast, vLast,
      huL.trans (hkey1_eq b hb lastLoc hlast_lt).symm,
      hvL.trans (congrArg Prod.snd (hpair1_eq b hb lastLoc hlast_lt)).symm,
      hqL.trans (congrArg Prod.fst (hpair1_eq b hb lastLoc hlast_lt)).symm,
      fun loc' hl' hne => by
        rw [hkey1_eq b hb loc' (lt_trans hl' hlast_lt)]; exact hne_last loc' hl' hne⟩
  obtain ⟨_, hr2, _, hbp2, hbp_inv2, _⟩ :=
    fastSwapLastDownProg_spec (Nat.zero_le 1) hr1 hbp_inv1 (seed_bkt_of stA₁.mem hof1)
      (seed_fp_of stA₁.mem hof1) hb (by rw [hbp1]; exact hinv.bkt_le_capMax b hb)
      (by rw [hbp1]; exact hlast_eq) hdel_le hlast_ref1 ht1
  generalize hs2_def : (Memory.spec 0).clientState stA₁
    (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) = stA₂
    at hr2 hbp2 hbp_inv2
  obtain ⟨hbal2, hn_le2, _⟩ := hbp_inv2
  have hbp12 : extractBlockPool fl.mp stA₂.mem = bp := hbp2.trans hbp1
  obtain ⟨_, hr3, _⟩ := fastBpPopBktBackProg_ready (b := b) hr2
  generalize hs3_def : (Memory.spec 0).clientState stA₂ (fastBpPopBktBackProg (fl.pBase, b)) = stA₃
    at hr3
  have htr3 := FastTableReady.of_ready hr3
  have hbm : BpMetaConf M fl.mp.toCtx := by
    obtain ⟨h1, h2, h3⟩ := bpMetaConf_fast hv
    exact ⟨h1, h2, fun addr ha => hRM addr (writeMeta_sub_readMeta addr (h3 addr ha))⟩
  unfold fastRemoveAtProg
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_rwConfined hc
      (rw_readParam (W := FastWriteMeta fl) (pBase_in_readMeta (by decide)))
      writeMeta_sub_readMeta hRM) rfl hm11_r fun hc_a => ?_
  rw [ite_eq_left hb]
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_rwConfined hc_a (rw_fastReadBktCnt htr0) writeMeta_sub_readMeta hRM)
    (clientState_fastReadBktCntProg _ s₁) hcnt_r fun hc_b => ?_
  rw [ite_eq_left hdel]; simp only [pure_bind]
  have hs1_cs := SlotCoupledStep.of_rwConfined hc_b
    (rw_fastUnindexAt (b := b) (delLoc := delLoc) (u_val := u.val) htr0)
    writeMeta_sub_readMeta hRM
  refine SlotCoupledStep.bind_prog hs1_cs fun hc1 => ?_
  rw [hs1_def] at hc1 ⊢
  have hns_stA₁ : (extractBlockPool fl.mp stA₁.mem).nSide = bp.nSide :=
    congrArg BlockPoolState.nSide hbp1
  have hs2_cs := (fastSwapLastDown_coupled (delLoc := delLoc) hr1 hRM
    hbal1.core hn_le1 hb (by rw [hbp1]; exact hlast_lt)
    (hc1.cast_n hns_stA₁.symm)).cast_n hns_stA₁
  refine SlotCoupledStep.bind_prog hs2_cs fun hc2 => ?_
  rw [hs2_def] at hc2 ⊢
  have htr2 := FastTableReady.of_ready hr2
  have hns_stA₂ : (extractBlockPool fl.mp stA₂.mem).nSide = bp.nSide :=
    congrArg BlockPoolState.nSide hbp12
  refine SlotCoupledStep.bind_prog (n₂ := bp.nSide - 1) ?_ fun hc3 => by
    rw [hs3_def] at hc3 ⊢
    have hs4_rw := rw_fastPromoteShadowIfDone (b := b) (cnt := cnt) htr3
    have hs4_cs := SlotCoupledStep.of_rwConfined hc3 hs4_rw writeMeta_sub_readMeta hRM
    exact SlotCoupledStep.bind_prog hs4_cs fun hc4 =>
      SlotCoupledStep.of_rwConfined hc4
        (rw_fastClampTryPos (b := b) (cnt := cnt) (lastLoc := lastLoc) (htr3.step_meta hs4_rw))
        writeMeta_sub_readMeta hRM
  unfold fastBpPopBktBackProg
  refine SlotCoupledStep.bind_readOnly_eq
    (SlotCoupledStep.of_rwConfined hc2
      (rw_loadBlockPoolCtx (W := FastWriteMeta fl) htr2) writeMeta_sub_readMeta hRM)
    (clientState_loadBlockPoolCtxProg _ stA₂) (clientResult_loadBlockPoolCtxProg htr2.pt)
    fun hc2_l => ?_
  have hv_bp2 : fl.bpL.Valid fl.mp.w stA₂.frontier := by
    have h := htr2.valid.bp_valid; rwa [htr2.valid.w_eq] at h
  exact (bpPopBktBackRaw_coupled hv_bp2 hbm hbal2 hn_le2 hb
    (by dsimp only [FastEpochLayout.bpL]; rw [hbp12]; exact hcnt_pos)
    (hc2_l.cast_n hns_stA₂.symm)).cast_n (congrArg (· - 1) hns_stA₂)

/-- Phase-`8` source-slot coupling theorem for `epochDeleteProg`: deleting `u` from a draining
source slot (`io.sideBit = 0`) preserves `SlotStateCoupled`. -/
theorem epochDelete_src_coupled {M : ℕ → Prop} {c U V w pBase metaBase : ℕ}
    {io : SlotIoLayout} {sl : SlotLatent c U V} {s₁ s₂ : Memory.State}
    (h : EpochSlotInv c U V w s₁.frontier pBase metaBase io 0 true sl s₁.mem)
    (hsub : ∀ addr, SlotSrcMetaRegion c w pBase metaBase sl.nCap addr → M addr)
    (hc : SlotStateCoupled M io (s₁.mem (metaBase + 1)) s₁ s₂)
    (u : Fin U) :
    let s₁' := (Memory.spec 0).clientState s₁ (epochDeleteProg (pBase, u.val))
    SlotCoupledStep M io (s₁'.mem (metaBase + 1)) s₁ s₂ (epochDeleteProg (pBase, u.val)) := by
  dsimp only
  have hp_in : ∀ k < 64, M (pBase + k) :=
    fun k hk => hsub (pBase + k) (Or.inl ⟨Nat.le_add_right _ _, by omega⟩)
  by_cases h0 : sl.nCap = 0
  · have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_left h0] at hraw
    obtain ⟨_, _, _, hpt, _, _⟩ := hraw
    have ⟨hm0, hm1, _⟩ := hpt
    have hm_mb0 : M metaBase :=
      hsub metaBase (Or.inr (Or.inl ⟨le_rfl, by simp only [h0, ↓reduceIte]; omega⟩))
    have hm_mb1 : M (metaBase + 1) :=
      hsub (metaBase + 1) (Or.inr (Or.inl ⟨by omega, by simp only [h0, ↓reduceIte]; omega⟩))
    have hm0_r : (Memory.spec 0).clientResult s₁ (Memory.read pBase) = 0 := hm0
    have hm1_r : (Memory.spec 0).clientResult s₁ (Memory.read (pBase + 1)) = metaBase := hm1
    have hst_eq : (Memory.spec 0).clientState s₁ (epochDeleteProg (pBase, u.val)) =
        (Memory.spec 0).clientState s₁ (smallEpochDeleteRawProg ((io.toCtx, metaBase), u.val)) := by
      unfold epochDeleteProg
      rw [StateTransitionSpec.clientState_bind]
      change (Memory.spec 0).clientState s₁ _ = _
      rw [hm0_r, ite_eq_left rfl, StateTransitionSpec.clientState_bind]
      change (Memory.spec 0).clientState s₁ _ = _
      rw [hm1_r, StateTransitionSpec.clientState_bind, clientState_loadSmallIoCtxProg,
        clientResult_loadSmallIoCtxProg hpt]
    rw [hst_eq]
    unfold epochDeleteProg
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc (ConfinedTo.read_prog (by simpa using hp_in 0 (by decide))))
      rfl hm0 fun hc1 => ?_
    rw [ite_eq_left rfl]
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc1 (ConfinedTo.read_prog (hp_in 1 (by decide))))
      rfl hm1 fun hc2 => ?_
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc2 (cf_loadSmallIoCtx hp_in))
      (clientState_loadSmallIoCtxProg pBase s₁) (clientResult_loadSmallIoCtxProg hpt)
      fun hc3 => ?_
    exact smallEpochDeleteRaw_coupled hc3 hm_mb0 hm_mb1 rfl
  · have h₂ := epochSlotInv_of_coupled h hsub hc
    set fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    have hRM : ∀ addr, FastReadMeta fl addr → M addr :=
      fun addr ha => hsub addr (fastReadMeta_sub_slotSrcMeta h0 addr ha)
    have hraw₁ := h; unfold EpochSlotInv at hraw₁; rw [ite_eq_right h0] at hraw₁
    have hraw₂ := h₂; unfold EpochSlotInv at hraw₂; rw [ite_eq_right h0] at hraw₂
    obtain ⟨hv₁, ⟨hpt₁, hmode₁⟩, _⟩ := hraw₁
    obtain ⟨hv₂, ⟨hpt₂, hmode₂⟩, _⟩ := hraw₂
    have htr₁ : FastTableReady w fl s₁ := ⟨hv₁, hpt₁⟩
    have hm0 : (Memory.spec 0).clientResult s₁ (Memory.read pBase) = sl.nCap := by
      change s₁.mem pBase = sl.nCap
      simpa [FastEpochLayout.paramWord] using hpt₁ 0 (by decide)
    have hst_lg₁ : (Memory.spec 0).clientState s₁ (epochDeleteProg (pBase, u.val)) =
        (Memory.spec 0).clientState s₁ (largeEpochDeleteProg (pBase, u.val)) := by
      unfold epochDeleteProg
      rw [StateTransitionSpec.clientState_bind]
      change (Memory.spec 0).clientState s₁ _ = _
      rw [hm0, ite_eq_right h0]
    rw [hst_lg₁]
    unfold epochDeleteProg
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc (ConfinedTo.read_prog (by simpa using hp_in 0 (by decide))))
      rfl hm0 fun hc1 => ?_
    rw [ite_eq_right h0]
    rcases hmode₁ with ⟨hm2_0, hfast₁⟩ | ⟨hm2_1, hfb₁⟩
    · have hm2_r : (Memory.spec 0).clientResult s₁ (fastReadMetaProg (fl.pBase, 2)) = 0 :=
        (clientResult_fastReadMetaProg hpt₁ (by decide)).trans hm2_0
      have hst_f₁ : (Memory.spec 0).clientState s₁ (largeEpochDeleteProg (pBase, u.val)) =
          (Memory.spec 0).clientState s₁ (fastDeleteProg (pBase, u.val)) := by
        unfold largeEpochDeleteProg
        rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2_r,
          ite_eq_left rfl]
      rw [hst_f₁]
      unfold largeEpochDeleteProg
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc1 (rw_fastReadMeta (off := 2) htr₁)
          writeMeta_sub_readMeta hRM)
        (clientState_fastReadMetaProg _ s₁) hm2_r fun hc2 => ?_
      rw [ite_eq_left rfl]
      have hs₂_ro : (Memory.spec 0).clientState
          ((Memory.spec 0).clientState s₂ (Memory.read pBase))
          (fastReadMetaProg (pBase, 2)) = s₂ := by
        change (Memory.spec 0).clientState s₂ (fastReadMetaProg (pBase, 2)) = s₂
        exact clientState_fastReadMetaProg (pBase, 2) s₂
      rw [hs₂_ro] at hc2 ⊢
      have hm2_s₂ : s₂.mem (metaBase + 2) = 0 :=
        (hc.mem_eq (metaBase + 2) (hRM (metaBase + 2)
          (Or.inr (Or.inl ⟨by dsimp [fl]; omega, by dsimp [fl]; omega⟩)))).symm.trans hm2_0
      have hfast₂ : FastEpochInv fl 0 sl.seeds s₂.mem sl.s_abs := by
        rcases hmode₂ with ⟨_, hf₂⟩ | ⟨h1, _⟩
        · exact hf₂
        · exact absurd (hm2_s₂.symm.trans h1) Nat.zero_ne_one
      have hpr₁ := fastProbeProg_spec hv₁ hfast₁ u
      have hpr₂ := fastProbeProg_spec hv₂ hfast₂ u
      dsimp only at hpr₁ hpr₂
      obtain ⟨hst_p₁, _, hb_p₁, hcase₁⟩ := hpr₁
      obtain ⟨hst_p₂, _, hb_p₂, hcase₂⟩ := hpr₂
      rcases hres₁ : (Memory.spec 0).clientResult s₁ (fastProbeProg (fl.pBase, u.val)) with
        ⟨⟨hit₁, _⟩, ⟨b₁, ⟨loc₁, _⟩⟩⟩
      rcases hres₂ : (Memory.spec 0).clientResult s₂ (fastProbeProg (fl.pBase, u.val)) with
        ⟨⟨hit₂, _⟩, ⟨b₂, ⟨loc₂, _⟩⟩⟩
      rw [hres₁] at hb_p₁ hcase₁
      rw [hres₂] at hb_p₂ hcase₂
      dsimp only at hb_p₁ hb_p₂ hcase₁ hcase₂
      cases hsu : sl.s_abs u with
      | none =>
        rw [hsu] at hcase₁ hcase₂
        obtain ⟨hh1, _⟩ := hcase₁
        obtain ⟨hh2, _⟩ := hcase₂
        have hd₁ : (Memory.spec 0).clientState s₁ (fastDeleteProg (pBase, u.val)) = s₁ := by
          unfold fastDeleteProg
          rw [StateTransitionSpec.clientState_bind, hst_p₁, hres₁]; dsimp only
          rw [ite_eq_left hh1]; rfl
        have hd₂ : (Memory.spec 0).clientState s₂ (fastDeleteProg (pBase, u.val)) = s₂ := by
          unfold fastDeleteProg
          rw [StateTransitionSpec.clientState_bind, hst_p₂, hres₂]; dsimp only
          rw [ite_eq_left hh2]; rfl
        rw [hd₁]
        exact ⟨Subsingleton.elim _ _, by rw [hd₁, hd₂]; exact hc2⟩
      | some v =>
        rw [hsu] at hcase₁ hcase₂
        obtain ⟨hh1, hloc₁, _, hkey₁, hbp_p₁⟩ := hcase₁
        obtain ⟨hh2, hloc₂, _, _, hbp_p₂⟩ := hcase₂
        have hnz₁ : hit₁ ≠ 0 := by rcases hh1 with rfl | rfl | rfl <;> decide
        have hnz₂ : hit₂ ≠ 0 := by rcases hh2 with rfl | rfl | rfl <;> decide
        set b := epochBucket c U sl.nCap sl.seeds.bkt u
        have hb_lt : b < numBucketsWhp sl.nCap := epochBucket_lt c U sl.nCap sl.seeds.bkt u
        have hbp_eq := extractBlockPool_eq_of_coupled hv₁ hRM hc.mem_eq
        have hloc₂_s₁ : loc₂ < (extractBlockPool fl.mp s₁.mem).bktCount b := hbp_eq ▸ hloc₂
        obtain ⟨hbal₁, _, _⟩ := hfast₁.bp_inv
        have hcv₁ := hbal₁.core
        have hloc_eq : loc₁ = loc₂ := by
          have hp₁ := hcv₁.toPhys_lt hb_lt hloc₁
          have hp₂ := hcv₁.toPhys_lt hb_lt hloc₂_s₁
          have hpr_s₁ : bpPairAt fl.bpL s₁.mem b loc₂ = (keyQuotient (bWhp sl.nCap) u.val, v.val) :=
            by
              unfold bpPairAt; dsimp only [FastEpochLayout.bpL]
              have htp_eq : (extractBlockPool fl.mp s₂.mem).toPhys b loc₂ =
                  (extractBlockPool fl.mp s₁.mem).toPhys b loc₂ := by rw [hbp_eq]
              exact (hc.pair_eq _ hp₂).trans (htp_eq ▸ hbp_p₂)
          have hq_eq : (slotIoPairAt fl.io s₁.mem
              ((extractBlockPool fl.mp s₁.mem).toPhys b loc₁)).1 =
              (slotIoPairAt fl.io s₁.mem ((extractBlockPool fl.mp s₁.mem).toPhys b loc₂)).1 :=
            (congrArg Prod.fst hbp_p₁).trans (congrArg Prod.fst hpr_s₁).symm
          have how₁ : ((extractBlockPool fl.mp s₁.mem).ownerOf
              ((extractBlockPool fl.mp s₁.mem).toPhys b loc₁)).1 = b :=
            congrArg Prod.fst (hcv₁.ownerOf_toPhys hb_lt hloc₁)
          have how₂ : ((extractBlockPool fl.mp s₁.mem).ownerOf
              ((extractBlockPool fl.mp s₁.mem).toPhys b loc₂)).1 = b :=
            congrArg Prod.fst (hcv₁.ownerOf_toPhys hb_lt hloc₂_s₁)
          have hpe := hfast₁.refines.slot_inj _ hp₁ _ hp₂ (how₁.trans how₂.symm) hq_eq
          have hle : ((extractBlockPool fl.bpL.mp s₁.mem).ownerOf
              ((extractBlockPool fl.bpL.mp s₁.mem).toPhys b loc₁)).2 =
              ((extractBlockPool fl.bpL.mp s₁.mem).ownerOf
              ((extractBlockPool fl.bpL.mp s₁.mem).toPhys b loc₂)).2 :=
            congrArg (fun x => ((extractBlockPool fl.bpL.mp s₁.mem).ownerOf x).2) hpe
          rwa [hcv₁.ownerOf_toPhys hb_lt hloc₁, hcv₁.ownerOf_toPhys hb_lt hloc₂_s₁] at hle
        have hd₁ : (Memory.spec 0).clientState s₁ (fastDeleteProg (pBase, u.val)) =
            (Memory.spec 0).clientState s₁ (fastRemoveAtProg ((fl.pBase, b), (loc₁, u.val))) := by
          unfold fastDeleteProg
          rw [StateTransitionSpec.clientState_bind, hst_p₁, hres₁]; dsimp only
          rw [ite_eq_right hnz₁, hb_p₁]
        have hd₂ : (Memory.spec 0).clientState s₂ (fastDeleteProg (pBase, u.val)) =
            (Memory.spec 0).clientState s₂ (fastRemoveAtProg ((fl.pBase, b), (loc₁, u.val))) := by
          unfold fastDeleteProg
          rw [StateTransitionSpec.clientState_bind, hst_p₂, hres₂]; dsimp only
          rw [ite_eq_right hnz₂, hb_p₂, ← hloc_eq]
        obtain ⟨_, _, _, hns_rem, _⟩ :=
          fastRemoveAtProg_spec u (by decide) hv₁ (hfast₁.toGen 0) hb_lt hloc₁ hkey₁
        have hrm_cs := fastRemoveAt_coupled u hv₁ hfast₁ hb_lt hloc₁ hkey₁ hRM hc2
        rw [hd₁]
        exact ⟨Subsingleton.elim _ _, by rw [hd₁, hd₂]; exact hrm_cs.coupled.cast_n hns_rem.symm⟩
    · have hm2_r : (Memory.spec 0).clientResult s₁ (fastReadMetaProg (fl.pBase, 2)) = 1 :=
        (clientResult_fastReadMetaProg hpt₁ (by decide)).trans hm2_1
      have hu46 : (Memory.spec 0).clientResult s₁ (Memory.read (fl.pBase + 46)) = U - 1 :=
        hpt₁ 46 (by decide)
      have hu_le : u.val ≤ U - 1 := Nat.le_pred_of_lt u.isLt
      have hst_fb₁ : (Memory.spec 0).clientState s₁ (largeEpochDeleteProg (pBase, u.val)) =
          (Memory.spec 0).clientState s₁
            (fallbackDeleteProg ((fl.fbL.feistelCtx, fl.bpL.toCtx), u.val)) := by
        unfold largeEpochDeleteProg fastFallbackDeleteProg
        rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2_r,
          ite_eq_right Nat.one_ne_zero, StateTransitionSpec.clientState_bind]
        change (Memory.spec 0).clientState s₁ _ = _
        rw [hu46, ite_eq_left hu_le,
          StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
          clientResult_loadFeistelCtx hpt₁,
          StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
          clientResult_loadBlockPoolCtxProg hpt₁]
        rfl
      rw [hst_fb₁]
      unfold largeEpochDeleteProg fastFallbackDeleteProg
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc1 (rw_fastReadMeta (off := 2) htr₁)
          writeMeta_sub_readMeta hRM)
        (clientState_fastReadMetaProg _ s₁) hm2_r fun hc2 => ?_
      rw [ite_eq_right Nat.one_ne_zero]
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_confinedTo hc2 (ConfinedTo.read_prog (hp_in 46 (by decide))))
        rfl hu46 fun hc3 => ?_
      rw [ite_eq_left hu_le]
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc3 (rw_loadHashStaticCtx (W := FastWriteMeta fl))
          writeMeta_sub_readMeta hRM)
        (clientState_loadHashStaticCtxProg _ s₁) (clientResult_loadFeistelCtx hpt₁) fun hc4 => ?_
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc4 (rw_loadBlockPoolCtx (W := FastWriteMeta fl) htr₁)
          writeMeta_sub_readMeta hRM)
        (clientState_loadBlockPoolCtxProg _ s₁) (clientResult_loadBlockPoolCtxProg hpt₁)
        fun hc5 => ?_
      have hbm : BpMetaConf M fl.fbL.bpL.mp.toCtx := by
        obtain ⟨h1, h2, h3⟩ := bpMetaConf_fast hv₁
        exact ⟨h1, h2, fun addr ha => hRM addr (writeMeta_sub_readMeta addr (h3 addr ha))⟩
      have hfc : FeistelConf M fl.fbL.feistelCtx := by
        obtain ⟨h1, h2, h3⟩ := feistelConf_bkt hv₁
        exact ⟨h1, h2, fun addr ha1 ha2 => hRM addr (h3 addr ha1 ha2)⟩
      exact fallbackDelete_coupled hv₁.fb_valid hfc hbm hfb₁ hc5

/-- Phase-`8` source-slot coupling theorem for `epochPopAnyProg`: popping from a non-empty draining
source slot (`io.sideBit = 0`) returns the identical `(u, v)` pair and transitions
`SlotStateCoupled` from `n` to `n - 1`. -/
theorem epochPopAny_src_coupled {M : ℕ → Prop} {c U V w pBase metaBase : ℕ}
    {io : SlotIoLayout} {sl : SlotLatent c U V} {s₁ s₂ : Memory.State}
    (h : EpochSlotInv c U V w s₁.frontier pBase metaBase io 0 true sl s₁.mem)
    (hpos : 0 < (EpochUpdate.liveDom sl.s_abs).card)
    (hsub : ∀ addr, SlotSrcMetaRegion c w pBase metaBase sl.nCap addr → M addr)
    (hc : SlotStateCoupled M io (s₁.mem (metaBase + 1)) s₁ s₂) :
    SlotCoupledStep M io (s₁.mem (metaBase + 1) - 1) s₁ s₂ (epochPopAnyProg pBase) := by
  have hm_ns := h.mem_nSide_eq
  have hpos_m : 0 < s₁.mem (metaBase + 1) := hm_ns.symm ▸ hpos
  have hp_in : ∀ k < 64, M (pBase + k) :=
    fun k hk => hsub (pBase + k) (Or.inl ⟨Nat.le_add_right _ _, by omega⟩)
  unfold epochPopAnyProg
  by_cases h0 : sl.nCap = 0
  · have hraw := h; unfold EpochSlotInv at hraw; rw [ite_eq_left h0] at hraw
    obtain ⟨_, _, _, hpt, _, _⟩ := hraw
    have ⟨hm0, hm1, _⟩ := hpt
    have hm_mb1 : M (metaBase + 1) :=
      hsub (metaBase + 1) (Or.inr (Or.inl ⟨by omega, by simp only [h0, ↓reduceIte]; omega⟩))
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc (ConfinedTo.read_prog (by simpa using hp_in 0 (by decide))))
      rfl hm0 fun hc1 => ?_
    rw [ite_eq_left rfl]
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc1 (ConfinedTo.read_prog (hp_in 1 (by decide))))
      rfl hm1 fun hc2 => ?_
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc2 (cf_loadSmallIoCtx hp_in))
      (clientState_loadSmallIoCtxProg pBase s₁) (clientResult_loadSmallIoCtxProg hpt)
      fun hc3 => ?_
    exact smallEpochPopAnyRaw_coupled hc3 hm_mb1 rfl hpos_m
  · have h₂ := epochSlotInv_of_coupled h hsub hc
    set fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    have hRM : ∀ addr, FastReadMeta fl addr → M addr :=
      fun addr ha => hsub addr (fastReadMeta_sub_slotSrcMeta h0 addr ha)
    have hraw₁ := h; unfold EpochSlotInv at hraw₁; rw [ite_eq_right h0] at hraw₁
    have hraw₂ := h₂; unfold EpochSlotInv at hraw₂; rw [ite_eq_right h0] at hraw₂
    obtain ⟨hv₁, ⟨hpt₁, hmode₁⟩, _⟩ := hraw₁
    obtain ⟨hv₂, ⟨hpt₂, hmode₂⟩, _⟩ := hraw₂
    have htr₁ : FastTableReady w fl s₁ := ⟨hv₁, hpt₁⟩
    have hm0 : (Memory.spec 0).clientResult s₁ (Memory.read pBase) = sl.nCap := by
      change s₁.mem pBase = sl.nCap
      simpa [FastEpochLayout.paramWord] using hpt₁ 0 (by decide)
    refine SlotCoupledStep.bind_readOnly_eq
      (SlotCoupledStep.of_confinedTo hc (ConfinedTo.read_prog (by simpa using hp_in 0 (by decide))))
      rfl hm0 fun hc1 => ?_
    rw [ite_eq_right h0]
    unfold largeEpochPopAnyProg
    rcases hmode₁ with ⟨hm2_0, hfast₁⟩ | ⟨hm2_1, hfb₁⟩
    · have hm2_r : (Memory.spec 0).clientResult s₁ (fastReadMetaProg (fl.pBase, 2)) = 0 :=
        (clientResult_fastReadMetaProg hpt₁ (by decide)).trans hm2_0
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc1 (rw_fastReadMeta (off := 2) htr₁)
          writeMeta_sub_readMeta hRM)
        (clientState_fastReadMetaProg _ s₁) hm2_r fun hc2 => ?_
      rw [ite_eq_left rfl]
      have hs₂_ro : (Memory.spec 0).clientState
          ((Memory.spec 0).clientState s₂ (Memory.read pBase))
          (fastReadMetaProg (pBase, 2)) = s₂ := by
        change (Memory.spec 0).clientState s₂ (fastReadMetaProg (pBase, 2)) = s₂
        exact clientState_fastReadMetaProg (pBase, 2) s₂
      rw [hs₂_ro] at hc2 ⊢
      have hm2_s₂ : s₂.mem (metaBase + 2) = 0 :=
        (hc.mem_eq (metaBase + 2) (hRM (metaBase + 2)
          (Or.inr (Or.inl ⟨by dsimp [fl]; omega, by dsimp [fl]; omega⟩)))).symm.trans hm2_0
      have hfast₂ : FastEpochInv fl 0 sl.seeds s₂.mem sl.s_abs := by
        rcases hmode₂ with ⟨_, hf₂⟩ | ⟨h1, _⟩
        · exact hf₂
        · exact absurd (hm2_s₂.symm.trans h1) Nat.zero_ne_one
      have hr₁ := hfast₁.ready hv₁ rfl
      have hr₂ := hfast₂.ready hv₂ rfl
      obtain ⟨hbal₁, _, _⟩ := hfast₁.bp_inv
      obtain ⟨hbal₂, _, _⟩ := hfast₂.bp_inv
      have hcv₁ := hbal₁.core
      have hcv₂ := hbal₂.core
      have hbp_eq := extractBlockPool_eq_of_coupled hv₁ hRM hc.mem_eq
      obtain ⟨_, hres_o₁, hb₁, hl₁⟩ := fastBpOwnerOfZeroProg_spec hr₁ hcv₁ hpos_m
      obtain ⟨_, hres_o₂, _, _⟩ :=
        fastBpOwnerOfZeroProg_spec hr₂ hcv₂ (hbp_eq ▸ hpos_m)
      rw [hres_o₁] at hb₁ hl₁
      set b := ((extractBlockPool fl.mp s₁.mem).ownerOf 0).1
      have hcnt_pos : 0 < (extractBlockPool fl.mp s₁.mem).bktCount b :=
        Nat.zero_lt_of_lt hl₁
      have hb_lt : b < numBucketsWhp sl.nCap := hb₁
      set lastLoc := (extractBlockPool fl.mp s₁.mem).bktCount b - 1
      have hlast_lt : lastLoc < (extractBlockPool fl.mp s₁.mem).bktCount b := by omega
      obtain ⟨hcnt_r₁, _⟩ := fastReadBktCntProg_spec hr₁ hcv₁ hb_lt
      obtain ⟨hcnt_r₂, _⟩ := fastReadBktCntProg_spec hr₂ hcv₂ hb_lt
      obtain ⟨_, hread_r₁, _⟩ := fastBpReadAtProg_spec hr₁ hfast₁.bp_inv hb_lt hlast_lt
      obtain ⟨_, hread_r₂, _⟩ :=
        fastBpReadAtProg_spec hr₂ hfast₂.bp_inv hb_lt (hbp_eq ▸ hlast_lt)
      have hpair_eq : bpPairAt fl.bpL s₂.mem b lastLoc = bpPairAt fl.bpL s₁.mem b lastLoc := by
        unfold bpPairAt; dsimp only [FastEpochLayout.bpL]
        have htp_eq : (extractBlockPool fl.mp s₂.mem).toPhys b lastLoc =
            (extractBlockPool fl.mp s₁.mem).toPhys b lastLoc := by rw [hbp_eq]
        rw [htp_eq]
        exact (hc.pair_eq _ (hcv₁.toPhys_lt hb_lt hlast_lt)).symm
      obtain ⟨u, v, hu, hv_eq, _, hq_u, _⟩ := hfast₁.bktSlot_refines hb_lt hlast_lt
      have hq_lt : (bpPairAt fl.bpL s₁.mem b lastLoc).1 < 2 ^ quotBitsWhp U sl.nCap :=
        hq_u ▸ keyQuotient_bWhp_lt hv₁.N_le_U u
      obtain ⟨hrec_r₁, _⟩ := fastFeistelReconProg_spec hr₁ hq_lt hfast₁.seed_bkt (bkt := b)
      obtain ⟨hrec_r₂, _⟩ :=
        fastFeistelReconProg_spec hr₂ (hpair_eq.symm ▸ hq_lt) hfast₂.seed_bkt (bkt := b)
      have hrec_val₁ : (Memory.spec 0).clientResult s₁
          (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s₁.mem b lastLoc).1))) = u.val := by
        rw [hrec_r₁]; exact hu.symm
      have hrec_val₂ : (Memory.spec 0).clientResult s₂
          (fastFeistelReconProg (fl.pBase, (b, (bpPairAt fl.bpL s₂.mem b lastLoc).1))) = u.val := by
        rw [hrec_r₂, hpair_eq]; exact hu.symm
      have how_b₂ : ((Memory.spec 0).clientResult s₂ (fastBpOwnerOfZeroProg fl.pBase)).1 = b := by
        rw [hres_o₂, hbp_eq]
      have hcnt_r₂' : (Memory.spec 0).clientResult s₂ (fastReadBktCntProg (fl.pBase, b)) =
          (extractBlockPool fl.mp s₁.mem).bktCount b := by
        rw [hcnt_r₂, hbp_eq]
      have hpop₁ : (Memory.spec 0).clientResult s₁ (fastPopAnyProg fl.pBase) = (u.val, v.val) ∧
          (Memory.spec 0).clientState s₁ (fastPopAnyProg fl.pBase) =
            (Memory.spec 0).clientState s₁ (fastRemoveAtProg ((fl.pBase, b), (lastLoc, u.val))) :=
        by
          unfold fastPopAnyProg
          have how_b₁ : ((Memory.spec 0).clientResult s₁ (fastBpOwnerOfZeroProg fl.pBase)).1 = b :=
            by rw [hres_o₁]
          rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastBpOwnerOfZeroProg, how_b₁, pure_bind,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastReadBktCntProg, hcnt_r₁, ite_eq_left hcnt_pos, pure_bind,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastBpReadAtProg, hread_r₁,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastFeistelReconProg, hrec_val₁,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            prog_clientResult_pure, StateTransitionSpec.clientState_pure, hv_eq]
          exact ⟨rfl, rfl⟩
      have hpop₂ : (Memory.spec 0).clientResult s₂ (fastPopAnyProg fl.pBase) = (u.val, v.val) ∧
          (Memory.spec 0).clientState s₂ (fastPopAnyProg fl.pBase) =
            (Memory.spec 0).clientState s₂ (fastRemoveAtProg ((fl.pBase, b), (lastLoc, u.val))) :=
        by
          unfold fastPopAnyProg
          rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastBpOwnerOfZeroProg, how_b₂, pure_bind,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastReadBktCntProg, hcnt_r₂', ite_eq_left hcnt_pos, pure_bind,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastBpReadAtProg, hread_r₂,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            clientState_fastFeistelReconProg, hrec_val₂,
            StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
            prog_clientResult_pure, StateTransitionSpec.clientState_pure, hpair_eq, hv_eq]
          exact ⟨rfl, rfl⟩
      have hrm_cs := fastRemoveAt_coupled u hv₁ hfast₁ hb_lt hlast_lt hu.symm hRM hc2
      exact ⟨hpop₁.1.trans hpop₂.1.symm, by rw [hpop₁.2, hpop₂.2]; exact hrm_cs.coupled⟩
    · have hm2_r : (Memory.spec 0).clientResult s₁ (fastReadMetaProg (fl.pBase, 2)) = 1 :=
        (clientResult_fastReadMetaProg hpt₁ (by decide)).trans hm2_1
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc1 (rw_fastReadMeta (off := 2) htr₁)
          writeMeta_sub_readMeta hRM)
        (clientState_fastReadMetaProg _ s₁) hm2_r fun hc2 => ?_
      rw [ite_eq_right Nat.one_ne_zero]
      unfold fastFallbackPopAnyProg
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc2 (rw_loadHashStaticCtx (W := FastWriteMeta fl))
          writeMeta_sub_readMeta hRM)
        (clientState_loadHashStaticCtxProg _ s₁) (clientResult_loadFeistelCtx hpt₁) fun hc3 => ?_
      refine SlotCoupledStep.bind_readOnly_eq
        (SlotCoupledStep.of_rwConfined hc3 (rw_loadBlockPoolCtx (W := FastWriteMeta fl) htr₁)
          writeMeta_sub_readMeta hRM)
        (clientState_loadBlockPoolCtxProg _ s₁) (clientResult_loadBlockPoolCtxProg hpt₁)
        fun hc4 => ?_
      have hbm : BpMetaConf M fl.fbL.bpL.mp.toCtx := by
        obtain ⟨h1, h2, h3⟩ := bpMetaConf_fast hv₁
        exact ⟨h1, h2, fun addr ha => hRM addr (writeMeta_sub_readMeta addr (h3 addr ha))⟩
      have hfc : FeistelConf M fl.fbL.feistelCtx := by
        obtain ⟨h1, h2, h3⟩ := feistelConf_bkt hv₁
        exact ⟨h1, h2, fun addr ha1 ha2 => hRM addr (h3 addr ha1 ha2)⟩
      exact fallbackPopAny_coupled hv₁.fb_valid hfc hbm hfb₁ hpos_m hc4

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

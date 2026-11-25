/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvBase
-- Retain private `import all` solely to unfold unexposed `Memory.Prog` bodies of the epoch stack
-- without modifying existing upstream modules or invalidating cached `.olean` artifacts.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeFallbackBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochSubEpoch
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemove
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFast
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch

/-!
# Paged `PageUnpermState` Frame and `unpermRank` Preservation (`DualEpochPagedFrame`)

When an active epoch operates in shared paged mode (`io.usePaged ≠ 0`, used during Phase `8`
`migrate` and Phase `9` `unperm` with `unpermDone = 0`), user mutations (`epochInsertProg` and
`epochDeleteProg`) and background migration steps (`epochPopAnyProg` + `epochInsertProg`) invoke at
most one `slotIoAppendProg` or `slotIoPopBackProg` on `io.side` while all non-length-changing steps
preserve `extractPageUnperm io.pgL` identically.

This module proves `PagedUnpermStep io.side (extractPageUnperm io.pgL s.mem)
(extractPageUnperm io.pgL s'.mem)` across `EpochSlotInv` operations:
1. `cleanPhase = 0` is preserved (`ph = 8`).
2. When `io.side = true` and `cleanPhase ∈ {1, 2, 3}` (`ph = 9`, `unpermDone = 0`),
   `0 < cleanPhase ∧ cleanPhase < 4` is preserved and `unpermRank` grows by at most `64`
   (`unpermRank_appendSlot_le` and `unpermRank_popBackSlot_le`).

## Main definitions

* `PagedUnpermStep`: post-state `PageUnpermState` relation after at most one `appendSlot` or
  `popBackSlot` on `side`.

## Main results

* `EpochSlotInv.insert_paged_unperm`
* `EpochSlotInv.delete_paged_unperm`
* `EpochSlotInv.popAny_paged_unperm`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open EpochUpdate

/-! ## Section 1: Pure `PagedUnpermStep` Combinators -/

/-- Post-state `PageUnpermState` relation across at most one `appendSlot` or `popBackSlot` on
`side`: preserves `cleanPhase = 0`, and on `side = true` with `cleanPhase ∈ {1, 2, 3}` keeps
`cleanPhase ∈ {1, 2, 3}` while increasing `unpermRank` by at most `64`. -/
@[expose] def PagedUnpermStep (side : Bool) (u u' : PageUnpermState) : Prop :=
  (u.cleanPhase = 0 → u'.cleanPhase = 0) ∧
  (side = true → 0 < u.cleanPhase → u.cleanPhase < 4 →
    0 < u'.cleanPhase ∧ u'.cleanPhase < 4 ∧ u'.unpermRank ≤ u.unpermRank + 64)

theorem PagedUnpermStep.of_eq {side : Bool} {u u' : PageUnpermState} (heq : u' = u) :
    PagedUnpermStep side u u' := by
  subst heq
  exact ⟨id, fun _ h0 h4 => ⟨h0, h4, Nat.le_add_right _ _⟩⟩

private theorem PagedUnpermStep.congr_ends {side : Bool} {u u₁ u₂ u' : PageUnpermState}
    (h₁ : u₁ = u) (h₂ : u' = u₂) (h : PagedUnpermStep side u₁ u₂) :
    PagedUnpermStep side u u' := by
  subst h₁; subst h₂; exact h

private theorem PagedUnpermStep.of_appendSlot {side : Bool} {u : PageUnpermState}
    (hv : u.Valid) :
    PagedUnpermStep side u (u.appendSlot side).1 := by
  refine ⟨fun hp0 => ?_, fun hsd h0 h4 => ?_⟩
  · unfold PageUnpermState.appendSlot
    rcases u.st.stepAppend side with ⟨st', sws⟩
    rw [ite_eq_left hp0]
  · subst hsd
    have hrk := unpermRank_appendSlot_le hv h0 h4
    refine ⟨?_, ?_, hrk⟩
    · unfold PageUnpermState.appendSlot
      rcases u.st.stepAppend true with ⟨st', sws⟩
      rw [ite_eq_right (Nat.pos_iff_ne_zero.mp h0)]
      split_ifs
      · dsimp only; split_ifs <;> decide
      · exact h0
    · unfold PageUnpermState.appendSlot
      rcases u.st.stepAppend true with ⟨st', sws⟩
      rw [ite_eq_right (Nat.pos_iff_ne_zero.mp h0)]
      split_ifs
      · dsimp only; split_ifs <;> decide
      · exact h4

private theorem PagedUnpermStep.of_popBackSlot {side : Bool} {u : PageUnpermState}
    (hv : u.Valid) (hpos : 0 < u.st.virtLen side) :
    PagedUnpermStep side u (u.popBackSlot side).1 := by
  refine ⟨fun hp0 => ?_, fun hsd h0 h4 => ?_⟩
  · unfold PageUnpermState.popBackSlot
    rcases u.st.stepPopBack side with ⟨st', sws⟩
    rw [ite_eq_left hp0]
  · subst hsd
    have hrk := unpermRank_popBackSlot_le hv hpos h0 h4
    refine ⟨?_, ?_, hrk⟩
    · unfold PageUnpermState.popBackSlot
      rcases u.st.stepPopBack true with ⟨st1, sw1⟩
      rcases u.st.rawPopBack true with ⟨st2, sw2⟩
      rw [ite_eq_right (Nat.pos_iff_ne_zero.mp h0)]
      split_ifs
      · dsimp only; split_ifs <;> decide
      · dsimp only; decide
      · dsimp only; exact h0
    · unfold PageUnpermState.popBackSlot
      rcases u.st.stepPopBack true with ⟨st1, sw1⟩
      rcases u.st.rawPopBack true with ⟨st2, sw2⟩
      rw [ite_eq_right (Nat.pos_iff_ne_zero.mp h0)]
      split_ifs
      · dsimp only; split_ifs <;> decide
      · dsimp only; decide
      · dsimp only; exact h4

/-! ## Section 2: `SlotIoLayout` Append and PopBack `PageUnpermState` Lemmas -/

private theorem extractPageUnperm_eq_of_io_outside {io : SlotIoLayout} {m₁ m₂ : ℕ → ℕ}
    (hw : 0 < io.pgL.w) (hup : io.usePaged ≠ 0)
    (hout : ∀ addr, io.OwnsAddr addr → m₂ addr = m₁ addr) :
    extractPageUnperm io.pgL m₂ = extractPageUnperm io.pgL m₁ :=
  extractPageUnperm_congr hw fun a ha =>
    hout a (by unfold SlotIoLayout.OwnsAddr; rw [ite_eq_right hup]; exact Or.inl ha)

private theorem slotIoAppendRawProg_paged_unperm {io : SlotIoLayout} {nSide q v : ℕ}
    {s : Memory.State}
    (hvIo : io.Valid io.pgL.w s.frontier)
    (hinv : io.StateInv nSide 0 s.mem)
    (hup : io.usePaged ≠ 0)
    (hcap : (extractPagePair io.pgL s.mem).totalItems + 1 ≤ io.pgL.nCap)
    (hq : q < 2 ^ io.pgL.qBits) (hv : v < 2 ^ io.pgL.vBits) :
    let s' := (Memory.spec 0).clientState s (slotIoAppendRawProg ((io.toCtx, nSide), (q, v)))
    PagedUnpermStep io.side (extractPageUnperm io.pgL s.mem) (extractPageUnperm io.pgL s'.mem) := by
  dsimp only
  have hvL : io.pgL.Valid io.pgL.w s.frontier := by
    unfold SlotIoLayout.Valid at hvIo; rwa [ite_eq_right hup] at hvIo
  unfold SlotIoLayout.StateInv at hinv; rw [ite_eq_right hup] at hinv
  obtain ⟨hi, hps, _, _, hvl, hcs, hph⟩ := hinv
  have hsb_eq : (if io.sideBit = 0 then 0 else 1) = if io.side then 1 else 0 := by
    unfold SlotIoLayout.side
    by_cases hz : io.sideBit = 0 <;> simp [hz]
  unfold slotIoAppendRawProg; dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
  simp only [hup, ↓reduceIte, pure_bind]
  rw [StateTransitionSpec.clientState_bind, hsb_eq]
  obtain ⟨hfr_ap, hu_ap, _⟩ := pageAppendBoundedProg_spec hvL hi hps hcap hcs hph
  obtain ⟨hi_ap, _, hps_ap, hvl_ap, _, hti_ap, _, _, _⟩ :=
    PageUnpermState.appendSlot_spec.{0} hi hcs hph
  set s₁ := (Memory.spec 0).clientState s
    (pageAppendBoundedProg ((io.pgL.toCtx, if io.side then 1 else 0), 16))
  have hst_ap : extractPagePair io.pgL s₁.mem =
      ((extractPageUnperm io.pgL s.mem).appendSlot io.side).1.st :=
    congrArg PageUnpermState.st hu_ap
  have hps₁ : (extractPagePair io.pgL s₁.mem).pageSize = io.pgL.pgB :=
    hst_ap.symm ▸ hps_ap.trans hps
  have hti₁ : (extractPagePair io.pgL s₁.mem).totalItems ≤ io.pgL.nCap := by
    rw [hst_ap, hti_ap]; exact hcap
  have hmp₁ : (extractPagePair io.pgL s₁.mem).totalPages < io.pgL.maxPages := by
    obtain ⟨_, _, _, _, _, hpg32, _, _, _, hnc_mp, _, _, _, _, _⟩ := hvL
    have hti_eq := (extractPagePair io.pgL s₁.mem).totalItems_eq
    rw [hps₁] at hti_eq
    have hle : (extractPagePair io.pgL s₁.mem).totalPages * io.pgL.pgB ≤
        (io.pgL.maxPages - 2) * io.pgL.pgB := by omega
    have htp_le := (Nat.mul_le_mul_right_iff (by omega : 0 < io.pgL.pgB)).mp hle
    omega
  have hidx₁ : nSide < (extractPagePair io.pgL s₁.mem).virtLen io.side := by
    rw [hst_ap, hvl_ap, hvl]; omega
  obtain ⟨_, hu_wv, _⟩ := pageWriteVirtBoundedProg_spec (hfr_ap.symm ▸ hvL)
    (hu_ap.symm ▸ hi_ap) hps₁ hmp₁ hti₁ io.side hidx₁ hq hv
  dsimp only [PageArenaLayout.toCtx] at hu_wv
  exact PagedUnpermStep.congr_ends rfl (hu_wv.trans hu_ap) (PagedUnpermStep.of_appendSlot hi)

private theorem slotIoPopBackRawProg_paged_unperm {io : SlotIoLayout} {nSide : ℕ}
    {s : Memory.State}
    (hvIo : io.Valid io.pgL.w s.frontier)
    (hinv : io.StateInv nSide 0 s.mem)
    (hup : io.usePaged ≠ 0) (hpos : 0 < nSide) :
    let s' := (Memory.spec 0).clientState s (slotIoPopBackRawProg io.toCtx)
    PagedUnpermStep io.side (extractPageUnperm io.pgL s.mem) (extractPageUnperm io.pgL s'.mem) := by
  dsimp only
  have hvL : io.pgL.Valid io.pgL.w s.frontier := by
    unfold SlotIoLayout.Valid at hvIo; rwa [ite_eq_right hup] at hvIo
  unfold SlotIoLayout.StateInv at hinv; rw [ite_eq_right hup] at hinv
  obtain ⟨hi, hps, _, hti, hvl, hcs, hph⟩ := hinv
  have hsb_eq : (if io.sideBit = 0 then 0 else 1) = if io.side then 1 else 0 := by
    unfold SlotIoLayout.side
    by_cases hz : io.sideBit = 0 <;> simp [hz]
  unfold slotIoPopBackRawProg; dsimp only [SlotIoLayout.toCtx]
  simp only [hup, ↓reduceIte, pure_bind, hsb_eq]
  have hpos_vl : 0 < (extractPagePair io.pgL s.mem).virtLen io.side := hvl.symm ▸ hpos
  obtain ⟨_, hu_pb, _⟩ := pagePopBackBoundedProg_spec hvL hi hps hti hpos_vl hcs hph
  exact PagedUnpermStep.congr_ends rfl hu_pb (PagedUnpermStep.of_popBackSlot hi hpos_vl)

/-! ## Section 3: Small-Regime Paged `PageUnpermState` Preservation -/

private theorem smallEpochInsertProg_paged_unperm {L : SmallEpochLayout} {w : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hinv : L.StateInv 0 s.mem s_abs)
    (hup : L.io.usePaged ≠ 0) (u : Fin L.U) (v : Fin L.V)
    (hcap_new : s_abs u = none →
      s.mem (L.metaBase + 1) < L.io.pgL.nCap ∧
      (extractPagePair L.io.pgL s.mem).totalItems + 1 ≤ L.io.pgL.nCap) :
    let s' := (Memory.spec 0).clientState s (smallEpochInsertProg L u.val v.val)
    PagedUnpermStep L.io.side
      (extractPageUnperm L.io.pgL s.mem) (extractPageUnperm L.io.pgL s'.mem) := by
  dsimp only
  have hvIo : L.io.Valid L.io.pgL.w s.frontier := hv.w_eq ▸ hv.io_valid
  obtain ⟨hsc_st, _, hsc_res⟩ := smallEpochScanRawProg_spec hv hinv u
  obtain ⟨_, _, hio_inv, _⟩ := hinv
  have hq_u : u.val < 2 ^ L.io.pgL.qBits := by
    rw [hv.qBits_eq]; exact u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two L.U)
  have hv_v : v.val < 2 ^ L.io.pgL.vBits := by
    rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two L.V)
  unfold smallEpochInsertProg smallEpochInsertRawProg
  rw [StateTransitionSpec.clientState_bind, hsc_st]
  cases hs_u : s_abs u with
  | some v_old =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hidx_lt, _, _⟩ := hsc_res
    rw [ite_eq_left hr1]
    obtain ⟨_, _, hpart⟩ := slotIoWriteProg_spec hvIo hio_inv hidx_lt hq_u hv_v
    unfold slotIoWriteProg at hpart
    exact PagedUnpermStep.of_eq (hpart hup).1
  | none =>
    rw [hs_u] at hsc_res
    obtain ⟨hn_lt, hpg_cap⟩ := hcap_new hs_u
    have hr_ne1 : Prod.fst ((Memory.spec 0).clientResult s
        (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))) ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1, StateTransitionSpec.clientState_bind]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
    have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) =
        s.mem (L.metaBase + 1) := rfl
    rw [hr0, hr0_v]
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    rw [ite_eq_left hn_lt, StateTransitionSpec.clientState_bind]
    have hstep := slotIoAppendRawProg_paged_unperm hvIo hio_inv hup hpg_cap hq_u hv_v
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx] at hstep
    set s₁ := (Memory.spec 0).clientState s
      (slotIoAppendRawProg ((L.io.toCtx, s.mem (L.metaBase + 1)), (u.val, v.val)))
    have hu_fin : extractPageUnperm L.io.pgL
        ((Memory.spec 0).clientState s₁
          (Memory.write (L.metaBase + 1) (s.mem (L.metaBase + 1) + 1))).mem =
        extractPageUnperm L.io.pgL s₁.mem :=
      extractPageUnperm_eq_of_io_outside hvIo.w_pos hup fun addr hia =>
        Function.update_of_ne (fun heq => hv.disjoint_hdr addr (Or.inr heq) hia) _ s₁.mem
    exact PagedUnpermStep.congr_ends rfl hu_fin hstep

private theorem smallEpochDeleteProg_paged_unperm {L : SmallEpochLayout} {w : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hinv : L.StateInv 0 s.mem s_abs)
    (hup : L.io.usePaged ≠ 0) (u : Fin L.U) :
    let s' := (Memory.spec 0).clientState s (smallEpochDeleteProg L u.val)
    PagedUnpermStep L.io.side
      (extractPageUnperm L.io.pgL s.mem) (extractPageUnperm L.io.pgL s'.mem) := by
  dsimp only
  have hvIo : L.io.Valid L.io.pgL.w s.frontier := hv.w_eq ▸ hv.io_valid
  obtain ⟨hsc_st, _, hsc_res⟩ := smallEpochScanRawProg_spec hv hinv u
  obtain ⟨_, _, hio_inv, _⟩ := hinv
  unfold smallEpochDeleteProg smallEpochDeleteRawProg
  rw [StateTransitionSpec.clientState_bind, hsc_st]
  cases hs_u : s_abs u with
  | none =>
    rw [hs_u] at hsc_res
    have hr_ne1 : Prod.fst ((Memory.spec 0).clientResult s
        (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))) ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1, StateTransitionSpec.clientState_pure]
    exact PagedUnpermStep.of_eq rfl
  | some _ =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hidx_lt, _, _⟩ := hsc_res
    set idx := Prod.fst (Prod.snd ((Memory.spec 0).clientResult s
      (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))))
    set nSide := s.mem (L.metaBase + 1)
    have hpos : 0 < nSide := Nat.zero_lt_of_lt hidx_lt
    have hlast_lt : nSide - 1 < nSide := Nat.sub_lt hpos Nat.one_pos
    rw [ite_eq_left hr1, StateTransitionSpec.clientState_bind]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
    have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) = nSide := rfl
    rw [hr0, hr0_v, ite_eq_left hpos]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    obtain ⟨hio₁, _, hpart₁⟩ := slotIoSwapProg_spec hvIo hio_inv hidx_lt hlast_lt
    have hswf := slotIoSwapProg_frame (io := L.io) hvIo.w_pos idx (nSide - 1)
    unfold slotIoSwapProg at hio₁ hpart₁ hswf
    set s₁ := (Memory.spec 0).clientState s (slotIoSwapRawProg (L.io.toCtx, (idx, nSide - 1)))
    have hfr₁ : s₁.frontier = s.frontier := hswf.frontier_eq s
    have hstep := slotIoPopBackRawProg_paged_unperm (hfr₁.symm ▸ hvIo) hio₁ hup hpos
    set s₂ := (Memory.spec 0).clientState s₁ (slotIoPopBackRawProg L.io.toCtx)
    have hu_fin : extractPageUnperm L.io.pgL
        ((Memory.spec 0).clientState s₂ (Memory.write (L.metaBase + 1) (nSide - 1))).mem =
        extractPageUnperm L.io.pgL s₂.mem :=
      extractPageUnperm_eq_of_io_outside hvIo.w_pos hup fun addr hia =>
        Function.update_of_ne (fun heq => hv.disjoint_hdr addr (Or.inr heq) hia) _ s₂.mem
    exact PagedUnpermStep.congr_ends (hpart₁ hup).1 hu_fin hstep

private theorem smallEpochPopAnyProg_paged_unperm {L : SmallEpochLayout} {w : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hinv : L.StateInv 0 s.mem s_abs)
    (hup : L.io.usePaged ≠ 0) (hpos : 0 < s.mem (L.metaBase + 1)) :
    let s' := (Memory.spec 0).clientState s (smallEpochPopAnyProg L)
    PagedUnpermStep L.io.side
      (extractPageUnperm L.io.pgL s.mem) (extractPageUnperm L.io.pgL s'.mem) := by
  dsimp only
  have hvIo : L.io.Valid L.io.pgL.w s.frontier := hv.w_eq ▸ hv.io_valid
  obtain ⟨_, _, hio_inv, _⟩ := hinv
  set nSide := s.mem (L.metaBase + 1)
  have hlast_lt : nSide - 1 < nSide := Nat.sub_lt hpos Nat.one_pos
  obtain ⟨_, hr_st⟩ := slotIoReadProg_spec hio_inv hlast_lt
  unfold slotIoReadProg at hr_st
  unfold smallEpochPopAnyProg smallEpochPopAnyRawProg
  rw [StateTransitionSpec.clientState_bind]
  have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
  have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) = nSide := rfl
  rw [hr0, hr0_v, ite_eq_left hpos]
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, hr_st, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have hstep := slotIoPopBackRawProg_paged_unperm hvIo hio_inv hup hpos
  set s₂ := (Memory.spec 0).clientState s (slotIoPopBackRawProg L.io.toCtx)
  have hu_fin : extractPageUnperm L.io.pgL
      ((Memory.spec 0).clientState s₂ (Memory.write (L.metaBase + 1) (nSide - 1))).mem =
      extractPageUnperm L.io.pgL s₂.mem :=
    extractPageUnperm_eq_of_io_outside hvIo.w_pos hup fun addr hia =>
      Function.update_of_ne (fun heq => hv.disjoint_hdr addr (Or.inr heq) hia) _ s₂.mem
  exact PagedUnpermStep.congr_ends rfl hu_fin hstep

/-! ## Section 4: `BlockPool` and `FallbackPool` Paged `PageUnpermState` Preservation -/

private theorem bpAppendProg_paged_unperm {bpL : BlockPoolLayout} {b q v : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier) (hinv : bpL.StateInv 0 s.mem)
    (hup : bpL.io.usePaged ≠ 0) (hb : b < bpL.mp.M)
    (hn_lt : (extractBlockPool bpL.mp s.mem).nSide < bpL.mp.nCap)
    (hbkt_lt : (extractBlockPool bpL.mp s.mem).bktCount b < bpL.mp.maxSlabs * bpL.mp.K)
    (hcap : (extractPagePair bpL.io.pgL s.mem).totalItems + 1 ≤ bpL.io.pgL.nCap)
    (hq : q < 2 ^ bpL.io.pgL.qBits) (hval : v < 2 ^ bpL.io.pgL.vBits) :
    let s' := (Memory.spec 0).clientState s (bpAppendProg bpL b q v)
    PagedUnpermStep bpL.io.side
      (extractPageUnperm bpL.io.pgL s.mem) (extractPageUnperm bpL.io.pgL s'.mem) := by
  dsimp only
  set bp₀ := extractBlockPool bpL.mp s.mem
  obtain ⟨hbal₀, _, hio₀⟩ := hinv
  have hvIo : bpL.io.Valid bpL.io.pgL.w s.frontier := hv.w_eq_io ▸ hv.io_valid
  have hns_res : (Memory.spec 0).clientResult s (bpReadScalarProg (bpL.mp.toCtx, 1)) =
      bp₀.nSide := by
    unfold bpReadScalarProg; dsimp only [BpMetaLayout.toCtx]; rw [ite_eq_left (Or.inl rfl)]; rfl
  unfold bpAppendProg bpAppendRawProg; dsimp only [BlockPoolLayout.toCtx]
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg, hns_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  have hcap_io : if bpL.io.usePaged = 0 then bp₀.nSide + 1 ≤ bpL.io.pgL.nCap
      else (extractPagePair bpL.io.pgL s.mem).totalItems + 1 ≤ bpL.io.pgL.nCap := by
    rw [ite_eq_right hup]; exact hcap
  have hstep := slotIoAppendRawProg_paged_unperm hvIo hio₀ hup hcap hq hval
  obtain ⟨hio₁, _, _⟩ := slotIoAppendProg_spec hvIo hio₀ hcap_io hq hval
  unfold slotIoAppendProg at hio₁
  set s₁ := (Memory.spec 0).clientState s (slotIoAppendRawProg ((bpL.io.toCtx, bp₀.nSide), (q, v)))
  have hfr₁ : s₁.frontier = s.frontier :=
    frontier_slotIoAppendRawProg ((bpL.io.toCtx, bp₀.nSide), (q, v)) s hvIo.w_pos
  have hex₁ : extractBlockPool bpL.mp s₁.mem = bp₀ := by
    have h := io_preserves_meta s hv (slotIoAppendProg_frame hvIo.w_pos bp₀.nSide q v)
    unfold slotIoAppendProg at h; exact h
  set s₂ := (Memory.spec 0).clientState s₁ (bpRawPostAppendMetaProg (bpL.mp.toCtx, b))
  have hfr₂ : s₂.frontier = s.frontier :=
    (runClient_frontier_bpRawPostAppendMetaProg _ s₁).trans hfr₁
  have hex₂ : extractBlockPool bpL.mp s₂.mem = bp₀.rawPostAppend b := by
    have h := bpRawPostAppendMetaProg_spec (hfr₁.symm ▸ hv.mp_valid) (hex₁ ▸ hbal₀.core) hb
      (hex₁ ▸ hn_lt)
    rwa [hex₁] at h
  obtain ⟨hio₂, _, hpart₂⟩ := meta_preserves_io (hfr₁.symm ▸ hv)
    (bpRawPostAppendMetaProg_frame (hfr₁.symm ▸ hv.mp_valid) b) hio₁
  obtain ⟨hsi_rpa, _, _, hn_rpa, _, _, _, _, _⟩ := hbal₀.rawPostAppend_spec hb hbkt_lt
  have hns_s₂ : (extractBlockPool bpL.mp s₂.mem).nSide = bp₀.nSide + 1 :=
    (congrArg BlockPoolState.nSide hex₂).trans hn_rpa
  obtain ⟨_, _, _, _, _, _, hpart₃⟩ := bpRunBktTicks16Prog_spec (hfr₂.symm ▸ hv)
    (hex₂.symm ▸ hsi_rpa) hb (by rw [hns_s₂]; omega) (hns_s₂.symm ▸ hio₂)
  dsimp only [BlockPoolLayout.toCtx] at hpart₃
  exact PagedUnpermStep.congr_ends rfl ((hpart₃ hup).1.trans (hpart₂ hup).1) hstep

private theorem bpPopBktBackProg_paged_unperm {bpL : BlockPoolLayout} {b : ℕ} {s : Memory.State}
    (hv : bpL.Valid bpL.mp.w s.frontier) (hinv : bpL.StateInv 0 s.mem)
    (hup : bpL.io.usePaged ≠ 0) (hb : b < bpL.mp.M)
    (hcnt : 0 < (extractBlockPool bpL.mp s.mem).bktCount b) :
    let s' := (Memory.spec 0).clientState s (bpPopBktBackProg bpL b)
    PagedUnpermStep bpL.io.side
      (extractPageUnperm bpL.io.pgL s.mem) (extractPageUnperm bpL.io.pgL s'.mem) := by
  dsimp only
  set bp₀ := extractBlockPool bpL.mp s.mem
  obtain ⟨hbal₀, hns_le₀, hio₀⟩ := hinv
  have hvIo : bpL.io.Valid bpL.io.pgL.w s.frontier := hv.w_eq_io ▸ hv.io_valid
  have hprep_pure := hbal₀.prepPopBktBack_spec.{0} hb hcnt
  dsimp only at hprep_pure
  set bp₁ := (bp₀.prepPopBktBack b).1
  set osw := (bp₀.prepPopBktBack b).2
  obtain ⟨hbal₁, hM₁, _, hn₁, hbc₁, hn_pos, htp_end, hsw_lt, _⟩ := hprep_pure
  unfold bpPopBktBackProg bpPopBktBackRawProg bpPopBktPrepAndShrinkProg BlockPoolLayout.toCtx
  dsimp only
  repeat rw [StateTransitionSpec.clientState_bind]
  set s₁ := (Memory.spec 0).clientState s (bpPrepPopMetaProg (bpL.mp.toCtx, b))
  have hfr₁ : s₁.frontier = s.frontier := runClient_frontier_bpPrepPopMetaProg _ s
  obtain ⟨hex₁, hres₁⟩ := bpPrepPopMetaProg_spec hv.mp_valid hbal₀ hb hcnt hns_le₀
  rw [hres₁]
  obtain ⟨hio₁, _, hpart₁⟩ := meta_preserves_io hv (bpPrepPopMetaProg_frame hv.mp_valid b) hio₀
  set s₂ := (Memory.spec 0).clientState s₁ (bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw))
  have hfr₂ : s₂.frontier = s.frontier :=
    (frontier_bpExecOptSwapProg (bpL.io.toCtx, encodeOptSwap osw) s₁
      (by rw [SlotIoLayout.ofCtx_toCtx]; exact hvIo.w_pos)).trans hfr₁
  obtain ⟨hex₂_rel, hio₂, _, hpart₂⟩ := bpExecOptSwapProg_spec (hfr₁.symm ▸ hv) hio₁ hsw_lt
  have hex₂ : extractBlockPool bpL.mp s₂.mem = bp₁ := hex₂_rel.trans hex₁
  have hu_s₂ : extractPageUnperm bpL.io.pgL s₂.mem = extractPageUnperm bpL.io.pgL s.mem :=
    (hpart₂ hup).1.trans (hpart₁ hup).1
  set s₃ := (Memory.spec 0).clientState s₂ (slotIoPopBackRawProg bpL.io.toCtx)
  have hfr₃ : s₃.frontier = s.frontier :=
    (frontier_slotIoPopBackRawProg bpL.io.toCtx s₂
      (by rw [SlotIoLayout.ofCtx_toCtx]; exact hvIo.w_pos)).trans hfr₂
  have hex₃ : extractBlockPool bpL.mp s₃.mem = bp₁ := by
    have h := io_preserves_meta s₂ (hfr₂.symm ▸ hv) (slotIoPopBackProg_frame hvIo.w_pos)
    unfold slotIoPopBackProg at h; exact h.trans hex₂
  have hstep := slotIoPopBackRawProg_paged_unperm (hfr₂.symm ▸ hvIo) hio₂ hup hn_pos
  obtain ⟨hio₃, _, _⟩ := slotIoPopBackProg_spec (hfr₂.symm ▸ hvIo) hio₂ hn_pos
  unfold slotIoPopBackProg at hio₃
  set s₄ := (Memory.spec 0).clientState s₃ (bpCommitPopMetaProg (bpL.mp.toCtx, b))
  have hfr₄ : s₄.frontier = s.frontier :=
    (runClient_frontier_bpCommitPopMetaProg _ s₃).trans hfr₃
  have hex₄ : extractBlockPool bpL.mp s₄.mem = bp₁.commitPopBktBack b := by
    have h := bpCommitPopMetaProg_spec (hfr₃.symm ▸ hv.mp_valid) (hex₃ ▸ hbal₁) hb
      (by rw [hex₃, hn₁]; exact hn_pos) (by rw [hex₃, hn₁]; exact hns_le₀)
    rwa [hex₃] at h
  obtain ⟨hio₄, _, hpart₄⟩ := meta_preserves_io (hfr₃.symm ▸ hv)
    (bpCommitPopMetaProg_frame (hfr₃.symm ▸ hv.mp_valid) b) hio₃
  have htp_end₁ : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1 := by rwa [hbc₁ b, hn₁]
  have hcnt₁ : 0 < bp₁.bktCount b := by rwa [hbc₁ b]
  have hb₁ : b < bp₁.M := hM₁.symm ▸ hb
  obtain ⟨hsi₄, _, _, hn_cp, _, _, _, _⟩ :=
    hbal₁.commitPopBktBack_spec hb₁ hcnt₁ (hn₁.symm ▸ hn_pos) htp_end₁
  have hns_s₄ : (extractBlockPool bpL.mp s₄.mem).nSide = bp₀.nSide - 1 :=
    (congrArg BlockPoolState.nSide hex₄).trans (hn_cp.trans (congrArg (· - 1) hn₁))
  obtain ⟨hfr₅_rel, hex₅, hsi₅, hn₅, hio₅, _, hpart₅⟩ :=
    bpRunBktTicks16Prog_spec (hfr₄.symm ▸ hv) (hex₄.symm ▸ hsi₄) hb
      (by rw [hns_s₄]; exact (Nat.sub_le _ 1).trans hns_le₀) (hns_s₄.symm ▸ hio₄)
  dsimp only [BlockPoolLayout.toCtx] at hfr₅_rel hex₅ hio₅ hpart₅
  set s₅ := (Memory.spec 0).clientState s₄
    (bpRunBktTicks16Prog ((bpL.mp.toCtx, bpL.io.toCtx), b))
  have hfr₅ : s₅.frontier = s.frontier := hfr₅_rel.trans hfr₄
  rw [hex₄] at hex₅ hsi₅ hn₅ hio₅
  rw [Nat.sub_self] at hsi₅
  obtain ⟨_, _, _, _, _, _, hpart₆⟩ :=
    bpRunTopClean16Prog_spec (b₀ := b) (hfr₅.symm ▸ hv) (hex₅.symm ▸ hsi₅)
      (by rw [hex₅, hn₅, hn_cp, hn₁]; exact (Nat.sub_le _ 1).trans hns_le₀)
      (hex₅.symm ▸ hio₅)
  dsimp only [BlockPoolLayout.toCtx] at hpart₆
  exact PagedUnpermStep.congr_ends hu_s₂
    ((hpart₆ hup).1.trans ((hpart₅ hup).1.trans (hpart₄ hup).1)) hstep

private theorem fallbackInsertProg_paged_unperm {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv 0 θ_bkt s.mem s_abs)
    (hup : fl.bpL.io.usePaged ≠ 0) (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : s_abs u = none →
      (extractFallback fl.bpL.mp s.mem).nSide < fl.N ∧
      fl.bpL.io.AppendCap (extractFallback fl.bpL.mp s.mem).nSide s.mem) :
    let s' := (Memory.spec 0).clientState s (fallbackInsertProg ((fl.toCtx, u.val), v.val))
    PagedUnpermStep fl.bpL.io.side
      (extractPageUnperm fl.bpL.io.pgL s.mem) (extractPageUnperm fl.bpL.io.pgL s'.mem) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  set fb := extractFallback mp s.mem
  have hmv : mp.Valid w s.frontier := hv.bp_valid.mp_valid
  have hiov : io.Valid io.pgL.w s.frontier :=
    hv.bp_valid.w_eq_io ▸ hmv.w_eq.symm ▸ hv.bp_valid.io_valid
  have hdisj := hv.bp_valid.disjoint
  obtain ⟨hfs_res, hfs_st, _⟩ := feistelSplitBoundedProg_spec hv.N_le_U hinv.seed_bkt u
  change (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = _
    at hfs_res
  change (Memory.spec 0).clientState s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = s
    at hfs_st
  obtain ⟨hsc_st, hsc_res⟩ := fbScanProg_spec hv hinv u
  set bkt := epochBucket fl.c fl.U fl.N θ_bkt u
  set q_u := keyQuotient (bWhp fl.N) u.val
  have hq_u : q_u < 2 ^ io.pgL.qBits :=
    (keyQuotient_bWhp_lt hv.N_le_U u).trans_le (Nat.pow_le_pow_right Nat.one_lt_two.le hv.qBits_le)
  have hv_v : v.val < 2 ^ io.pgL.vBits := by
    rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.V)
  have hctx : fl.toCtx = (fl.feistelCtx, (mp.toCtx, io.toCtx)) := rfl
  unfold fallbackInsertProg; rw [hctx]
  rw [StateTransitionSpec.clientState_bind, hfs_st, hfs_res,
    StateTransitionSpec.clientState_bind, hsc_st]
  dsimp only
  cases hs_u : s_abs u with
  | some _ =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hhit_lt, _, _, _⟩ := hsc_res
    rw [ite_eq_left hr1]
    obtain ⟨_, _, hpart'⟩ := slotIoWriteProg_spec hiov hinv.io_inv hhit_lt hq_u hv_v
    unfold slotIoWriteProg at hpart'
    exact PagedUnpermStep.of_eq (hpart' hup).1
  | none =>
    rw [hs_u] at hsc_res
    obtain ⟨hns_lt, hpg_cap⟩ := hcap_new hs_u
    have hr_ne1 : Prod.fst ((Memory.spec 0).clientResult s
        (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u)))) ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1]
    obtain ⟨hfr₁, hns₁, _, _, hval₁, hio₁, _, _, _, hpg₁⟩ :=
      fbMaybePromoteProg_spec hmv hiov hdisj hinv.fb_valid hinv.nSide_le hinv.io_inv hinv.refines
    set s₁ := (Memory.spec 0).clientState s (fbMaybePromoteProg (mp.toCtx, io.toCtx))
    set fb₁ := extractFallback mp s₁.mem
    set fb0 := fb₁.fullBlocks
    set t := fb.nSide - fb0 * mp.K
    have hK : 0 < mp.K := by have := hmv.K_ge; omega
    have hfb1_K : fb₁.K = mp.K := rfl
    have hbl_le₁ : fb0 * mp.K ≤ fb.nSide := by
      have hb := hval₁.blocks_le; rwa [hfb1_K, hns₁] at hb
    have hfb0_div : fb0 ≤ mp.nCap / mp.K :=
      (Nat.le_div_iff_mul_le hK).mpr (hbl_le₁.trans hns_lt.le)
    have hns_lt_cap : fb.nSide < mp.nCap := hns_lt
    have hcap₁ : (extractPagePair io.pgL s₁.mem).totalItems + 1 ≤ io.pgL.nCap := by
      have hst₁ : extractPagePair io.pgL s₁.mem = extractPagePair io.pgL s.mem :=
        congrArg PageUnpermState.st (hpg₁ hup).1
      rw [hst₁]
      unfold SlotIoLayout.AppendCap at hpg_cap
      rwa [ite_eq_right hup] at hpg_cap
    have hstep := slotIoAppendRawProg_paged_unperm (hfr₁.symm ▸ hiov) hio₁ hup hcap₁ hq_u hv_v
    set s₂ := (Memory.spec 0).clientState s₁
      (slotIoAppendRawProg ((io.toCtx, fb.nSide), (q_u, v.val)))
    set s₃ := (Memory.spec 0).clientState s₂ (bpWriteTailDirRawProg ((mp.toCtx, t), bkt))
    have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
      have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
    have hwf_td := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge t bkt
    set s₄ := (Memory.spec 0).clientState s₃ (bpWriteScalarProg ((mp.toCtx, 1), fb.nSide + 1))
    have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 1 (fb.nSide + 1)
    have hnc_eq : Prod.snd (Prod.snd (Prod.snd mp.toCtx)) = mp.nCap := rfl
    have hk_eq : Prod.snd (Prod.fst (Prod.fst (Prod.snd mp.toCtx))) = mp.K := rfl
    have hst_tot : (Memory.spec 0).clientState s
        (fbInsertNewProg (((mp.toCtx, io.toCtx), (bkt, q_u)), v.val)) = s₄ := by
      unfold fbInsertNewProg
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_bpReadScalarProg, clientResult_bpReadScalar s₁ (Or.inl rfl),
        StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s₁ (Or.inr ⟨le_rfl, by omega⟩)]
      unfold fbInsertNewCheckProg; dsimp only
      have hs1_ns : s₁.mem (mp.metaBase + 1) = fb.nSide := hns₁
      have hs1_fb : s₁.mem (mp.metaBase + 10) = fb0 := rfl
      rw [hs1_ns, hs1_fb, hnc_eq, hk_eq, ite_eq_left hns_lt_cap, ite_eq_left hfb0_div,
        ite_eq_left hbl_le₁]
      simp only [pure_bind]
      unfold fbInsertNewCommitProg
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    rw [hst_tot]
    have hu₄ : extractPageUnperm io.pgL s₄.mem = extractPageUnperm io.pgL s₂.mem :=
      extractPageUnperm_eq_of_io_outside hiov.w_pos hup fun a hia =>
        (hwf_sc.frame.mem_outside s₃ a (fun hma => hdisj a hma hia)).trans
          (hwf_td.frame.mem_outside s₂ a (fun hma => hdisj a hma hia))
    exact PagedUnpermStep.congr_ends (hpg₁ hup).1 hu₄ hstep

private theorem fbPopTailAtProg_paged_unperm {mp : BpMetaLayout} {io : SlotIoLayout}
    {w p : ℕ} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).Valid)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractFallback mp s.mem).nSide 0 s.mem)
    (hup : io.usePaged ≠ 0)
    (hp_ge : (extractFallback mp s.mem).fullBlocks * mp.K ≤ p)
    (hp_lt : p < (extractFallback mp s.mem).nSide) :
    let s' := (Memory.spec 0).clientState s (fbPopTailAtProg ((mp.toCtx, io.toCtx), p))
    PagedUnpermStep io.side
      (extractPageUnperm io.pgL s.mem) (extractPageUnperm io.pgL s'.mem) := by
  dsimp only
  set fb := extractFallback mp s.mem
  set fb0 := fb.fullBlocks
  set fbBase := fb0 * mp.K
  set last := fb.nSide - 1
  set t₁ := p - fbBase
  set t₂ := last - fbBase
  have hpos : 0 < fb.nSide := Nat.zero_lt_of_lt hp_lt
  have hfb_K : fb.K = mp.K := rfl
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  have hbl_le : fbBase ≤ fb.nSide := by
    dsimp only [fbBase, fb0]; rw [← hfb_K]; exact hfb.blocks_le
  have hfb_div : fb0 ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hbl_le.trans hns_le)
  have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
    have := hmv.M_ge; have := hmv.K_ge; nlinarith
  have hfb0_def : fb.fullBlocks = fb0 := rfl
  have ht₁_lt : t₁ < fb.tailLen := by
    dsimp only [t₁, fbBase]; unfold FallbackState.tailLen; rw [hfb_K, hfb0_def]; omega
  have ht₂_lt : t₂ < fb.tailLen := by
    dsimp only [t₂, last, fbBase]; unfold FallbackState.tailLen; rw [hfb_K, hfb0_def]; omega
  obtain ⟨hfr_sw, _, hio_sw, _, _, hpg_sw⟩ :=
    fbSwapTailSlotsProg_spec hmv hiov hdisj hfb h6lt8 hns_le hio ht₁_lt ht₂_lt
  set s₁ := (Memory.spec 0).clientState s
    (fbSwapTailSlotsProg (((mp.toCtx, io.toCtx), fbBase), (t₁, t₂)))
  have hstep := slotIoPopBackRawProg_paged_unperm (hfr_sw.symm ▸ hiov) hio_sw hup hpos
  set s₂ := (Memory.spec 0).clientState s₁ (slotIoPopBackRawProg io.toCtx)
  set s₃ := (Memory.spec 0).clientState s₂ (bpWriteScalarProg ((mp.toCtx, 1), last))
  have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 1 last
  have hnc_eq : Prod.snd (Prod.snd (Prod.snd mp.toCtx)) = mp.nCap := rfl
  have hk_eq : Prod.snd (Prod.fst (Prod.fst (Prod.snd mp.toCtx))) = mp.K := rfl
  have hst_tot :
      (Memory.spec 0).clientState s (fbPopTailAtProg ((mp.toCtx, io.toCtx), p)) = s₃ := by
    unfold fbPopTailAtProg
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl),
      StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩)]
    unfold fbPopTailCheckProg; dsimp only
    have hns_mem : s.mem (mp.metaBase + 1) = fb.nSide := rfl
    have hfb_mem : s.mem (mp.metaBase + 10) = fb0 := rfl
    rw [hns_mem, hfb_mem, hnc_eq, hk_eq, ite_eq_left hns_le, ite_eq_left hfb_div]
    simp only [pure_bind]
    unfold fbPopTailInnerProg; dsimp only
    rw [ite_eq_left hp_ge, ite_eq_left hp_lt]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind]
    unfold fbPopBackAndDecProg
    rw [StateTransitionSpec.clientState_bind]
  rw [hst_tot]
  have hu₃ : extractPageUnperm io.pgL s₃.mem = extractPageUnperm io.pgL s₂.mem :=
    extractPageUnperm_eq_of_io_outside hiov.w_pos hup fun a hia =>
      hwf_sc.frame.mem_outside s₂ a (fun hma => hdisj a hma hia)
  exact PagedUnpermStep.congr_ends (hpg_sw hup).1 hu₃ hstep

private theorem fbDeleteSlotProg_paged_unperm {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits w hitP : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).Valid)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractFallback mp s.mem).nSide 0 s.mem)
    (href : PoolItemsRefines U V bBits hBkt (extractFallback mp s.mem).nSide
      (extractFallback mp s.mem).owner (slotIoPairAt io s.mem) s_abs)
    (hup : io.usePaged ≠ 0) (hp_lt : hitP < (extractFallback mp s.mem).nSide) :
    let s' := (Memory.spec 0).clientState s (fbDeleteSlotProg ((mp.toCtx, io.toCtx), hitP))
    PagedUnpermStep io.side
      (extractPageUnperm io.pgL s.mem) (extractPageUnperm io.pgL s'.mem) := by
  dsimp only
  set fb := extractFallback mp s.mem
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  unfold fbDeleteSlotProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩),
    StateTransitionSpec.clientState_bind, clientState_bpDivModKProg, clientResult_bpDivModK]
  dsimp only
  have hfb_mem : s.mem (mp.metaBase + 10) = fb.fullBlocks := rfl
  rw [hfb_mem]
  by_cases hlt_blk : hitP / mp.K < fb.fullBlocks
  · rw [ite_eq_left hlt_blk]
    have hoff_lt : hitP % mp.K < mp.K := Nat.mod_lt hitP hK
    obtain ⟨hfr₁, hns₁, hblk_le₁, htl_plus₁, hval₁, hio₁, href₁, _, _, hpg₁⟩ :=
      fbMaybePromoteProg_spec hmv hiov hdisj hfb hns_le hio href
    set s₁ := (Memory.spec 0).clientState s (fbMaybePromoteProg (mp.toCtx, io.toCtx))
    set fb1 := (extractFallback mp s₁.mem).fullBlocks
    have hblk_lt₁ : hitP / mp.K < fb1 := lt_of_lt_of_le hlt_blk hblk_le₁
    have hfb1_div : fb1 ≤ mp.nCap / mp.K :=
      (Nat.le_div_iff_mul_le hK).mpr ((hval₁.blocks_le).trans (hns₁.symm ▸ hns_le))
    obtain ⟨hfr₂, hns₂, hblk₂, hval₂, hio₂, _, _, _, hpg₂⟩ :=
      fbDemoteBlkProg_spec (hfr₁.symm ▸ hmv) (hfr₁.symm ▸ hiov) hdisj hval₁
        (hns₁.symm ▸ hns_le) htl_plus₁ hblk_lt₁ (hns₁.symm ▸ hio₁) (hns₁.symm ▸ href₁)
    set s₂ := (Memory.spec 0).clientState s₁ (fbDemoteBlkProg ((mp.toCtx, io.toCtx), hitP / mp.K))
    set lastSlot := (fb1 - 1) * mp.K + hitP % mp.K
    have hpos_fb1 : 1 ≤ fb1 := Nat.one_le_of_lt hblk_lt₁
    have hls_ge : (extractFallback mp s₂.mem).fullBlocks * mp.K ≤ lastSlot := by
      rw [hblk₂]; exact Nat.le_add_right _ _
    have hls_lt : lastSlot < (extractFallback mp s₂.mem).nSide := by
      have hns_def : (extractFallback mp s.mem).nSide = fb.nSide := rfl
      rw [hns₂, hns₁, hns_def]
      have h1 : (fb1 - 1) * mp.K + mp.K = fb1 * mp.K := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hpos_fb1]
      have h2 : fb1 * mp.K ≤ fb.nSide := by
        have hb := hval₁.blocks_le
        have hK1 : (extractFallback mp s₁.mem).K = mp.K := rfl
        rw [hK1, hns₁, hns_def] at hb; exact hb
      exact (Nat.add_lt_add_left hoff_lt _).trans_le (h1.le.trans h2)
    have hstep := fbPopTailAtProg_paged_unperm ((hfr₂.trans hfr₁).symm ▸ hmv)
      ((hfr₂.trans hfr₁).symm ▸ hiov) hdisj hval₂ ((hns₂.trans hns₁).symm ▸ hns_le)
      (hns₂.symm ▸ hio₂) hup hls_ge hls_lt
    have hst_dp : (Memory.spec 0).clientState s
        (fbDemoteAndPopProg ((mp.toCtx, io.toCtx), (hitP / mp.K, hitP % mp.K))) =
        (Memory.spec 0).clientState s₂ (fbPopTailAtProg ((mp.toCtx, io.toCtx), lastSlot)) := by
      have hk_eq : Prod.snd (Prod.fst (Prod.fst (Prod.snd mp.toCtx))) = mp.K := rfl
      have hnc_eq : Prod.snd (Prod.snd (Prod.snd mp.toCtx)) = mp.nCap := rfl
      unfold fbDemoteAndPopProg; dsimp only
      rw [hk_eq, ite_eq_left hoff_lt, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s₁ (Or.inr ⟨le_rfl, by omega⟩)]
      unfold fbDemotePopRunProg; dsimp only
      have hfb1_eq : s₁.mem (mp.metaBase + 10) = fb1 := rfl
      rw [hfb1_eq, hnc_eq, hk_eq, ite_eq_left hblk_lt₁, ite_eq_left hfb1_div]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind]
    rw [hst_dp]
    exact PagedUnpermStep.congr_ends ((hpg₂ hup).1.trans (hpg₁ hup).1) rfl hstep
  · rw [ite_eq_right hlt_blk]
    have hp_ge : fb.fullBlocks * mp.K ≤ hitP := by
      by_contra hlt; exact hlt_blk ((Nat.div_lt_iff_lt_mul hK).mpr (Nat.lt_of_not_le hlt))
    exact fbPopTailAtProg_paged_unperm hmv hiov hdisj hfb hns_le hio hup hp_ge hp_lt

private theorem fallbackDeleteProg_paged_unperm {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv 0 θ_bkt s.mem s_abs)
    (hup : fl.bpL.io.usePaged ≠ 0) (u : Fin fl.U) :
    let s' := (Memory.spec 0).clientState s (fallbackDeleteProg (fl.toCtx, u.val))
    PagedUnpermStep fl.bpL.io.side
      (extractPageUnperm fl.bpL.io.pgL s.mem) (extractPageUnperm fl.bpL.io.pgL s'.mem) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  have hmv : mp.Valid w s.frontier := hv.bp_valid.mp_valid
  have hiov : io.Valid io.pgL.w s.frontier :=
    hv.bp_valid.w_eq_io ▸ hmv.w_eq.symm ▸ hv.bp_valid.io_valid
  obtain ⟨hfs_res, hfs_st, _⟩ := feistelSplitBoundedProg_spec hv.N_le_U hinv.seed_bkt u
  change (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = _
    at hfs_res
  change (Memory.spec 0).clientState s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = s
    at hfs_st
  obtain ⟨hsc_st, hsc_res⟩ := fbScanProg_spec hv hinv u
  set bkt := epochBucket fl.c fl.U fl.N θ_bkt u
  set q_u := keyQuotient (bWhp fl.N) u.val
  have hctx : fl.toCtx = (fl.feistelCtx, (mp.toCtx, io.toCtx)) := rfl
  unfold fallbackDeleteProg; rw [hctx]
  rw [StateTransitionSpec.clientState_bind, hfs_st, hfs_res,
    StateTransitionSpec.clientState_bind, hsc_st]
  cases hs_u : s_abs u with
  | none =>
    rw [hs_u] at hsc_res
    have hr_ne1 : Prod.fst ((Memory.spec 0).clientResult s
        (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u)))) ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1, StateTransitionSpec.clientState_pure]
    exact PagedUnpermStep.of_eq rfl
  | some _ =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hhit_lt, _, _, _⟩ := hsc_res
    rw [ite_eq_left hr1]
    exact fbDeleteSlotProg_paged_unperm hmv hiov hv.bp_valid.disjoint hinv.fb_valid
      hinv.nSide_le hinv.io_inv hinv.refines hup hhit_lt

private theorem fallbackPopAnyProg_paged_unperm {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv 0 θ_bkt s.mem s_abs)
    (hup : fl.bpL.io.usePaged ≠ 0) (hpos : 0 < (extractFallback fl.bpL.mp s.mem).nSide) :
    let s' := (Memory.spec 0).clientState s (fallbackPopAnyProg fl.toCtx)
    PagedUnpermStep fl.bpL.io.side
      (extractPageUnperm fl.bpL.io.pgL s.mem) (extractPageUnperm fl.bpL.io.pgL s'.mem) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  set fb := extractFallback mp s.mem
  set last := fb.nSide - 1
  have hlast_lt : last < fb.nSide := Nat.sub_lt hpos Nat.one_pos
  have hmv : mp.Valid w s.frontier := hv.bp_valid.mp_valid
  have hiov : io.Valid io.pgL.w s.frontier :=
    hv.bp_valid.w_eq_io ▸ hmv.w_eq.symm ▸ hv.bp_valid.io_valid
  have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
    have := hmv.M_ge; have := hmv.K_ge; nlinarith
  have how_r := fbOwnerOfProg_spec hmv hinv.fb_valid h6lt8 hinv.nSide_le hlast_lt
  obtain ⟨hpr_r, hpr_s⟩ := slotIoReadProg_spec hinv.io_inv hlast_lt
  unfold slotIoReadProg at hpr_r hpr_s
  obtain ⟨hu_lt, _, _, hkq_u, _⟩ := hinv.refines.slot_key_val hlast_lt
  let u_top : Fin fl.U :=
    ⟨feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (fb.owner last) (Prod.fst (slotIoPairAt io s.mem last)), hu_lt⟩
  have hbw_pos : 1 ≤ bWhp fl.N := by
    have hM_ge : 2 ≤ 2 ^ bWhp fl.N := by
      have h1 := hmv.M_ge; dsimp only [mp] at h1; rw [hv.mp_eq] at h1; exact h1
    by_contra hz
    have h0 : bWhp fl.N = 0 := by omega
    rw [h0] at hM_ge; omega
  have hle : bWhp fl.N ≤ keyBits fl.U := by
    unfold bWhp keyBits
    exact (Nat.sub_le _ _).trans ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
  have hrw_eq : redWidthWhp fl.U = keyBits fl.U := max_eq_right (by omega)
  have hqLim_eq : redWidthWhp fl.U - bWhp fl.N = quotBitsWhp fl.U fl.N := by
    rw [hrw_eq]; rfl
  have hbw_le_rw : bWhp fl.N ≤ redWidthWhp fl.U := hrw_eq ▸ hle
  have hq_qb : Prod.fst (slotIoPairAt io s.mem last) < 2 ^ quotBitsWhp fl.U fl.N := by
    rw [← hkq_u]; exact keyQuotient_bWhp_lt hv.N_le_U u_top
  have hqb_lt_wv : redWidthWhp fl.U - bWhp fl.N < mp.w := by
    have hsum : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ w := by
      unfold quotBitsWhp; rw [Nat.sub_add_cancel hle]
      exact Nat.clog_le_of_le_pow hv.fits_U.le
    rw [hqLim_eq, hmv.w_eq.symm]; omega
  have hq_sh : Prod.fst (slotIoPairAt io s.mem last) < 1 <<< (redWidthWhp fl.U - bWhp fl.N) := by
    rwa [hqLim_eq, Nat.shiftLeft_eq, one_mul]
  obtain ⟨_, hrec_s, _⟩ := feistelReconBoundedProg_spec hq_qb hinv.seed_bkt (bkt := fb.owner last)
  change (Memory.spec 0).clientState s
    (feistelReconBoundedProg
      (fl.feistelCtx, (fb.owner last, Prod.fst (slotIoPairAt io s.mem last)))) = s
    at hrec_s
  have hctx : fl.toCtx = (fl.feistelCtx, (mp.toCtx, io.toCtx)) := rfl
  have hns_mem : s.mem (mp.metaBase + 1) = fb.nSide := rfl
  have hst_tot : (Memory.spec 0).clientState s (fallbackPopAnyProg fl.toCtx) =
      (Memory.spec 0).clientState s (fbDeleteSlotProg ((mp.toCtx, io.toCtx), last)) := by
    unfold fallbackPopAnyProg; rw [hctx]
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl), hns_mem, ite_eq_left hpos]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, state_fbOwnerOfProg, how_r,
      StateTransitionSpec.clientState_bind, hpr_s, hpr_r]
    change (Memory.spec 0).clientState s
      (if bWhp fl.N ≤ redWidthWhp fl.U then
        let qLim := pure (redWidthWhp fl.U - bWhp fl.N)
        qLim >>= fun ql =>
          if ql < mp.w then
            if Prod.fst (slotIoPairAt io s.mem last) < 1 <<< ql then _ else _
          else _
       else _) = _
    have hfb_ow : (extractFallback mp s.mem).owner last = fb.owner last := rfl
    rw [ite_eq_left hbw_le_rw]; simp only [pure_bind]
    rw [ite_eq_left hqb_lt_wv, ite_eq_left hq_sh, StateTransitionSpec.clientState_bind,
      hfb_ow, hrec_s, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  rw [hst_tot]
  exact fbDeleteSlotProg_paged_unperm hmv hiov hv.bp_valid.disjoint hinv.fb_valid
    hinv.nSide_le hinv.io_inv hinv.refines hup hlast_lt

/-! ## Section 5: Large-Epoch Fast/Fallback Paged `PageUnpermState` Preservation -/

private theorem fastRemoveAtProg_paged_unperm {slackCur : ℕ} {fl : FastEpochLayout}
    {w b delLoc : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State} (u : Fin fl.U)
    (hslack : slackCur ≤ 1) (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInvGen slackCur fl 0 seeds s.mem s_abs)
    (hup : fl.io.usePaged ≠ 0) (hb : b < numBucketsWhp fl.N)
    (hdel : delLoc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hk_u : fastKeyAt fl seeds.bkt s.mem b delLoc = u.val) :
    let s' := (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val)))
    PagedUnpermStep fl.io.side
      (extractPageUnperm fl.io.pgL s.mem) (extractPageUnperm fl.io.pgL s'.mem) := by
  dsimp only
  have hr0 := hinv.ready hv rfl
  have hpt := hinv.param_table
  set bp := extractBlockPool fl.mp s.mem
  set cnt := bp.bktCount b
  set lastLoc := cnt - 1
  have hcnt_pos : 0 < cnt := Nat.zero_lt_of_lt hdel
  have hlast_lt : lastLoc < cnt := Nat.sub_lt hcnt_pos Nat.one_pos
  have hlast_eq : cnt = lastLoc + 1 := (Nat.sub_add_cancel hcnt_pos).symm
  have hdel_le : delLoc ≤ lastLoc := Nat.le_pred_of_lt hdel
  have hm11_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 11)) =
      numBucketsWhp fl.N := hpt 11 (by decide)
  obtain ⟨hcnt_r, _⟩ := fastReadBktCntProg_spec hr0 hinv.bp_inv.1.core hb
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have seed_bkt_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt m := fun m hm =>
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
        (by dsimp only [FastEpochLayout.bktHashBase] at h2
            unfold offBktMeta offFpHash offBktHash at *; omega))
  have seed_fp_of : ∀ m : ℕ → ℕ, (∀ a, ¬fl.OwnsFastAddr a → m a = s.mem a) →
      BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
        (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp m := fun m hm =>
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hm a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  obtain ⟨uLast, vLast, huL, hvL, _, hqL, _⟩ := hinv.bktSlot_refines hb hlast_lt
  have hne_last : ∀ loc'' < lastLoc, loc'' ≠ delLoc →
      fastKeyAt fl seeds.bkt s.mem b loc'' ≠ uLast.val := fun loc'' hl'' _ heq => by
    have hcv : bp.CoreValid := hinv.bp_inv.1.core
    have hloc''_lt : loc'' < cnt := lt_trans hl'' hlast_lt
    obtain ⟨u'', _, hu'', _, _, hq_u'', _⟩ := hinv.bktSlot_refines hb hloc''_lt
    have hu_e : u'' = uLast := Fin.ext (hu''.trans heq)
    have hq_e : Prod.fst (slotIoPairAt fl.io s.mem (bp.toPhys b loc'')) =
        Prod.fst (slotIoPairAt fl.io s.mem (bp.toPhys b lastLoc)) := by
      change Prod.fst (bpPairAt fl.bpL s.mem b loc'') =
        Prod.fst (bpPairAt fl.bpL s.mem b lastLoc)
      rw [← hq_u'', hu_e, hqL]
    have hp1 := hcv.toPhys_lt hb hloc''_lt
    have hp2 := hcv.toPhys_lt hb hlast_lt
    have how1 : Prod.fst (bp.ownerOf (bp.toPhys b loc'')) = b := by
      rw [hcv.ownerOf_toPhys hb hloc''_lt]
    have how2 : Prod.fst (bp.ownerOf (bp.toPhys b lastLoc)) = b := by
      rw [hcv.ownerOf_toPhys hb hlast_lt]
    have hpe := hinv.refines.slot_inj _ hp1 _ hp2 (how1.trans how2.symm) hq_e
    have hle := congrArg (fun x => Prod.snd (bp.ownerOf x)) hpe
    rw [hcv.ownerOf_toPhys hb hloc''_lt, hcv.ownerOf_toPhys hb hlast_lt] at hle
    exact (Nat.ne_of_lt hl'') hle
  obtain ⟨hfr1, hr1, _, hbp1, _, _, _, hoi1, hof1, _, _, ht1⟩ :=
    fastUnindexAtProg_spec u hv hinv hb hdel hk_u
  generalize hs1_def : (Memory.spec 0).clientState s
    (fastUnindexAtProg ((fl.pBase, (b, delLoc)), u.val)) = s1 at hfr1 hr1 hbp1 hoi1 hof1 ht1
  have hbp_inv1 : fl.bpL.StateInv 0 s1.mem := bpStateInv_congr_io hv hinv.bp_inv hbp1 hoi1
  have hke1 : ∀ b'' < numBucketsWhp fl.N, ∀ loc'' < bp.bktCount b'',
      fastKeyAt fl seeds.bkt s1.mem b'' loc'' = fastKeyAt fl seeds.bkt s.mem b'' loc'' :=
    fun b'' hb'' loc'' hl'' => fastKeyAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb'' hl''
  have hpair1 : ∀ b'' < numBucketsWhp fl.N, ∀ loc'' < bp.bktCount b'',
      bpPairAt fl.bpL s1.mem b'' loc'' = bpPairAt fl.bpL s.mem b'' loc'' :=
    fun b'' hb'' loc'' hl'' => bpPairAt_eq_of_fixed_pool hv hinv.bp_inv hbp1 hoi1 hb'' hl''
  have hlast_ref1 : ∃ (uLast' : Fin fl.U) (vLast' : Fin fl.V),
      uLast'.val = fastKeyAt fl seeds.bkt s1.mem b lastLoc ∧
      vLast'.val = Prod.snd (bpPairAt fl.bpL s1.mem b lastLoc) ∧
      keyQuotient (bWhp fl.N) uLast'.val = Prod.fst (bpPairAt fl.bpL s1.mem b lastLoc) ∧
      ∀ loc'' < lastLoc, loc'' ≠ delLoc → fastKeyAt fl seeds.bkt s1.mem b loc'' ≠ uLast'.val :=
    ⟨uLast, vLast,
      huL.trans (hke1 b hb lastLoc hlast_lt).symm,
      hvL.trans (congrArg Prod.snd (hpair1 b hb lastLoc hlast_lt)).symm,
      hqL.trans (congrArg Prod.fst (hpair1 b hb lastLoc hlast_lt)).symm,
      fun loc'' hl'' hne => by
        rw [hke1 b hb loc'' (lt_trans hl'' hlast_lt)]; exact hne_last loc'' hl'' hne⟩
  obtain ⟨hfr2, hr2, _, hbp2, hbp_inv2, _, _, _, _, hpart2, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, ht2⟩ :=
    fastSwapLastDownProg_spec hslack hr1 hbp_inv1 (seed_bkt_of s1.mem hof1)
      (seed_fp_of s1.mem hof1) hb (by rw [hbp1]; exact hinv.bkt_le_capMax b hb)
      (by rw [hbp1]; exact hlast_eq) hdel_le hlast_ref1 ht1
  generalize hs2_def : (Memory.spec 0).clientState s1
    (fastSwapLastDownProg ((fl.pBase, b), (delLoc, lastLoc))) = s2
    at hfr2 hr2 hbp2 hbp_inv2 hpart2 ht2
  have hbp12 : extractBlockPool fl.mp s2.mem = bp := hbp2.trans hbp1
  have hv2 : fl.Valid w s2.frontier := (hfr2.trans hfr1).symm ▸ hv
  have hbp_step : (Memory.spec 0).clientState s2 (fastBpPopBktBackProg (fl.pBase, b)) =
      (Memory.spec 0).clientState s2 (bpPopBktBackProg fl.bpL b) := by
    obtain ⟨_, hpt2, _, _⟩ := hr2
    unfold fastBpPopBktBackProg bpPopBktBackProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hpt2]
  have hbp_v2 : fl.bpL.Valid fl.bpL.mp.w s2.frontier := by
    change fl.bpL.Valid fl.w s2.frontier; exact hv.w_eq ▸ hv2.bp_valid
  have hstep := bpPopBktBackProg_paged_unperm hbp_v2 hbp_inv2 hup hb
    (show 0 < (extractBlockPool fl.bpL.mp s2.mem).bktCount b by
      change 0 < (extractBlockPool fl.mp s2.mem).bktCount b; rw [hbp12]; exact hcnt_pos)
  rw [← hbp_step] at hstep
  obtain ⟨_, hr3, _, _, _, _, _, _, hfm3, _, _, _, _, _, _⟩ :=
    fastBpPopBktBackProg_spec hr2 hbp_inv2 hb (by rw [hbp12]; exact hcnt_pos)
  generalize hs3_def : (Memory.spec 0).clientState s2 (fastBpPopBktBackProg (fl.pBase, b)) = s3
    at hr3 hfm3 hstep
  rcases ht2 with ⟨_, _, _, ht2w⟩
  have hrl3_lt : (extractFastMeta fl s3.mem).curRole b < 3 := by
    obtain ⟨_, hrl_b, _⟩ := ht2w.bkt_meta_bounds b hb
    rw [hfm3]; exact hrl_b
  have hsh3_ins : (extractFastMeta fl s3.mem).shadowCode b = cnt →
      (extractFastMeta fl s3.mem).shadowIns b ≤ 5 * slabScale fl.N ^ 12 := fun heq => by
    have h2 : (extractFastMeta fl s2.mem).shadowCode b = cnt := by rwa [hfm3] at heq
    have hnz : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 := by rw [h2]; exact hcnt_pos.ne'
    obtain ⟨_, _, hbd, _⟩ := ht2w.shadow b hb hnz
    have hmul : 4 * (extractFastMeta fl s2.mem).shadowIns b ≤ 4 * (5 * slabScale fl.N ^ 12) :=
      (Nat.le_add_right _ _).trans (hbd.trans (by rw [← Nat.mul_assoc]))
    have hres := Nat.le_of_mul_le_mul_left hmul (by decide : 0 < 4)
    rwa [hfm3]
  obtain ⟨_, hr4, _, _, _, _, _, _, hoi4, _, _, _⟩ :=
    fastPromoteShadowIfDoneProg_spec hr3 hb hcnt_pos hrl3_lt hsh3_ins
  generalize hs4_def : (Memory.spec 0).clientState s3
    (fastPromoteShadowIfDoneProg ((fl.pBase, b), cnt)) = s4 at hr4 hoi4
  obtain ⟨_, _, _, _, _, _, _, _, hoi5, _, _⟩ :=
    fastClampTryPosProg_spec (b := b) (cnt := cnt) (lastLoc := lastLoc) hr4
  have hseq : (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (delLoc, u.val))) =
      (Memory.spec 0).clientState s4 (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc))) := by
    unfold fastRemoveAtProg; dsimp only
    rw [StateTransitionSpec.clientState_bind,
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 11)) = s from rfl,
      hm11_r, ite_eq_left hb,
      StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg, hcnt_r,
      ite_eq_left hdel, pure_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      hs1_def, hs2_def, hs3_def, hs4_def]
  rw [hseq]
  have hu1 : extractPageUnperm fl.io.pgL s1.mem = extractPageUnperm fl.io.pgL s.mem :=
    extractPageUnperm_eq_of_io_outside hv.io_valid.w_pos hup hoi1
  have hu5 : extractPageUnperm fl.io.pgL
      ((Memory.spec 0).clientState s4
        (fastClampTryPosProg ((fl.pBase, b), (cnt, lastLoc)))).mem =
      extractPageUnperm fl.io.pgL s3.mem :=
    extractPageUnperm_eq_of_io_outside hv.io_valid.w_pos hup fun a ha =>
      (hoi5 a ha).trans (hoi4 a ha)
  exact PagedUnpermStep.congr_ends ((hpart2 hup).1.trans hu1) hu5 hstep

private theorem largeEpochInsertProg_paged_unperm {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs) (hup : fl.io.usePaged ≠ 0)
    (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : s_abs u = none →
      (s.mem (fl.metaBase + 2) = 0 →
        (extractBlockPool fl.mp s.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem) ∧
      (s.mem (fl.metaBase + 2) = 1 →
        (extractFallback fl.mp s.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractFallback fl.mp s.mem).nSide s.mem)) :
    let s' := (Memory.spec 0).clientState s (largeEpochInsertProg ((fl.pBase, u.val), v.val))
    PagedUnpermStep fl.io.side
      (extractPageUnperm fl.io.pgL s.mem) (extractPageUnperm fl.io.pgL s'.mem) := by
  dsimp only
  obtain ⟨hpt_top, hdisj_mode⟩ := hinv
  have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
      s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hpt_top (by decide)
  unfold largeEpochInsertProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2]
  have hfb_call : ∀ {st : Memory.State} (hv_st : fl.Valid w st.frontier)
      (hpt_st : fl.ParamTable st.mem) (hfb_st : fl.fbL.StateInv 0 seeds.bkt st.mem s_abs),
      (s_abs u = none → (extractFallback fl.mp st.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractFallback fl.mp st.mem).nSide st.mem) →
      PagedUnpermStep fl.io.side (extractPageUnperm fl.io.pgL st.mem)
        (extractPageUnperm fl.io.pgL
          ((Memory.spec 0).clientState st
            (fastFallbackInsertProg ((fl.pBase, u.val), v.val))).mem) := by
    intro st hv_st hpt_st hfb_st hcap_st
    have hum : st.mem (fl.pBase + 46) = fl.U - 1 := hpt_st 46 (by decide)
    have hle_u : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
    have hst_eq : (Memory.spec 0).clientState st
        (fastFallbackInsertProg ((fl.pBase, u.val), v.val)) =
        (Memory.spec 0).clientState st (fallbackInsertProg ((fl.fbL.toCtx, u.val), v.val)) := by
      unfold fastFallbackInsertProg; dsimp only
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState st (Memory.read (fl.pBase + 46)) = st from rfl,
        prog_clientResult_read, hum, ite_eq_left hle_u,
        StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
        clientResult_loadFeistelCtx hpt_st,
        StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
        clientResult_loadBlockPoolCtxProg hpt_st]
      rfl
    rw [hst_eq]
    exact fallbackInsertProg_paged_unperm hv_st.fb_valid hfb_st hup u v hcap_st
  rcases hdisj_mode with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · rw [hm0, ite_eq_left rfl]
    have hr := hf.ready hv rfl
    set b := epochBucket fl.c fl.U fl.N seeds.bkt u
    have hb : b < numBucketsWhp fl.N := epochBucket_lt fl.c fl.U fl.N seeds.bkt u
    obtain ⟨hpr_st, _, hpr_b, hpr_res⟩ :=
      fastProbeProg_spec (slack := 0) (seeds := seeds) (s_abs := s_abs) hv hf u
    have hfb_path : s_abs u = none →
        let s1 := (Memory.spec 0).clientState s (fastEnterFallbackProg fl.pBase)
        let s2 := (Memory.spec 0).clientState s1
          (fastFallbackInsertProg ((fl.pBase, u.val), v.val))
        PagedUnpermStep fl.io.side
          (extractPageUnperm fl.io.pgL s.mem) (extractPageUnperm fl.io.pgL s2.mem) := by
      intro habs
      dsimp only
      obtain ⟨hbd_ok, hns_ok, hio_ok⟩ := hf.bp_inv
      obtain ⟨hfr_e, hpt_e, hns_e, hfb_e, _, hpg_e⟩ :=
        fastEnterFallbackProg_spec hr hf.hdr_N hf.seed_bkt hbd_ok.core
          hns_ok hio_ok hf.refines
      set s1 := (Memory.spec 0).clientState s (fastEnterFallbackProg fl.pBase)
      have hv1 : fl.Valid w s1.frontier := hfr_e.symm ▸ hv
      have hcap1 : s_abs u = none → (extractFallback fl.mp s1.mem).nSide < fl.N ∧
          fl.io.AppendCap (extractFallback fl.mp s1.mem).nSide s1.mem := fun _ => by
        obtain ⟨hn_lt, hcap0⟩ := (hcap_new habs).1 hm0
        refine ⟨hns_e ▸ hn_lt, ?_⟩
        unfold SlotIoLayout.AppendCap at hcap0 ⊢
        rw [ite_eq_right hup] at hcap0 ⊢
        have hpe : extractPagePair fl.io.pgL s1.mem = extractPagePair fl.io.pgL s.mem :=
          congrArg PageUnpermState.st (hpg_e hup).1
        rwa [hpe]
      exact PagedUnpermStep.congr_ends (hpg_e hup).1 rfl (hfb_call hv1 hpt_e hfb_e hcap1)
    unfold fastInsertProg
    rw [StateTransitionSpec.clientState_bind, hpr_st]; dsimp only
    cases hsu : s_abs u with
    | some _ =>
      rw [hsu] at hpr_res
      obtain ⟨hpr_tag, hpr_loc, _, _, hpr_pair⟩ := hpr_res
      have hnz : Prod.fst (Prod.fst ((Memory.spec 0).clientResult s
          (fastProbeProg (fl.pBase, u.val)))) ≠ 0 := by
        rcases hpr_tag with h | h | h <;> omega
      obtain ⟨hfs_r, _⟩ := fastFeistelSplitProg_spec hr hf.seed_bkt u
      obtain ⟨_, _, _, _, _, _, _, _, hpg'⟩ :=
        fastInsertOverwrite_spec hv hf u v hb rfl hpr_loc (congrArg Prod.fst hpr_pair)
      rw [ite_eq_left hnz, StateTransitionSpec.clientState_bind, clientState_fastFeistelSplitProg,
        hfs_r, hpr_b]
      exact PagedUnpermStep.of_eq (hpg' hup).1
    | none =>
      rw [hsu] at hpr_res
      obtain ⟨hpr_tag, _⟩ := hpr_res
      have hnz0 : ¬Prod.fst (Prod.fst ((Memory.spec 0).clientResult s
          (fastProbeProg (fl.pBase, u.val)))) ≠ 0 := by
        rw [hpr_tag]; exact fun h => h rfl
      rw [ite_eq_right hnz0, StateTransitionSpec.clientState_bind,
        clientState_fastCheckRKeyFreeProg]
      obtain ⟨_, _, hck_free, _⟩ := fastCheckRKeyFreeProg_spec hv hf u hsu
      by_cases hcoll : (Memory.spec 0).clientResult s
          (fastCheckRKeyFreeProg (fl.pBase, u.val)) ≠ 0
      · rw [ite_eq_left hcoll, StateTransitionSpec.clientState_bind]
        exact hfb_path hsu
      · have hcoll0 : (Memory.spec 0).clientResult s
            (fastCheckRKeyFreeProg (fl.pBase, u.val)) = 0 := by omega
        rw [ite_eq_right hcoll, hpr_b]
        obtain ⟨hcnt_r, _⟩ := fastReadBktCntProg_spec hr hf.bp_inv.1.core hb
        have hm25_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 25)) =
            capMaxWhp fl.N := hf.param_table 25 (by decide)
        rw [StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg, hcnt_r,
          StateTransitionSpec.clientState_bind,
          show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 25)) = s from rfl, hm25_r]
        by_cases hovf : capMaxWhp fl.N ≤ (extractBlockPool fl.mp s.mem).bktCount b
        · rw [ite_eq_left hovf, StateTransitionSpec.clientState_bind]
          exact hfb_path hsu
        · have hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N := by omega
          obtain ⟨hcur_none, hold_none⟩ := hck_free hcoll0
          obtain ⟨hn_lt, hpg_cap⟩ := (hcap_new hsu).1 hm0
          rw [ite_eq_right hovf, StateTransitionSpec.clientState_bind]
          -- Trace `fastInsertNewStepProg` (`drainTrySteps5` -> `fastShadowSteps8` -> `fastBpAppend`
          -- -> `fastBufInsert`) followed by `advanceSubEpochProg`.
          obtain ⟨hfr_ns, _, hinv_ns, _, _, _, _, _, _⟩ :=
            fastInsertNewStepProg_spec hv hf u v rfl hsu hn_lt hcnt_lt hpg_cap hcur_none hold_none
          obtain ⟨hfr1, _, hinv1, hbp1, _, hoi1, hof1, _, _, _⟩ :=
            drainTrySteps5Prog_spec hv (hf.toGen 0) hb hcnt_lt
          generalize hs1_def : (Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase) = s1
            at hfr1 hinv1 hbp1 hoi1 hof1
          have hv1 : fl.Valid w s1.frontier := hfr1.symm ▸ hv
          obtain ⟨hfr2, _, hinv2, hbp2, hcr2, _, _, _, _, _, _, _, _, _, hoi2, hof2, _, _⟩ :=
            fastShadowSteps8Prog_spec (b := b) hv1 hinv1
          generalize hs2_def : (Memory.spec 0).clientState s1
            (fastShadowSteps8Prog (fl.pBase, b)) = s2
            at hfr2 hinv2 hbp2 hcr2 hoi2 hof2
          have hv2 : fl.Valid w s2.frontier := hfr2.symm ▸ hv1
          have hbp12 : extractBlockPool fl.mp s2.mem = extractBlockPool fl.mp s.mem :=
            hbp2.trans hbp1
          have hoi12 : ∀ a, fl.io.OwnsAddr a → s2.mem a = s.mem a :=
            fun a ha => (hoi2 a ha).trans (hoi1 a ha)
          have hu2 : extractPageUnperm fl.io.pgL s2.mem = extractPageUnperm fl.io.pgL s.mem :=
            extractPageUnperm_eq_of_io_outside hv.io_valid.w_pos hup hoi12
          have hr2 := hinv2.ready hv2 rfl
          obtain ⟨hfs_r, _⟩ := fastFeistelSplitProg_spec hr2 hinv2.seed_bkt u
          have hq_lt : keyQuotient (bWhp fl.N) u.val < 2 ^ fl.io.pgL.qBits :=
            (keyQuotient_bWhp_lt hv.N_le_U u).trans_le
              (Nat.pow_le_pow_right Nat.one_lt_two.le hv.qBits_le)
          have hv_lt : v.val < 2 ^ fl.io.pgL.vBits := by
            rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.V)
          have hcap2 : (extractPagePair fl.io.pgL s2.mem).totalItems + 1 ≤ fl.io.pgL.nCap := by
            have hpe : extractPagePair fl.io.pgL s2.mem = extractPagePair fl.io.pgL s.mem :=
              congrArg PageUnpermState.st hu2
            rw [hpe]
            unfold SlotIoLayout.AppendCap at hpg_cap
            rwa [ite_eq_right hup] at hpg_cap
          have hcap_io2 : fl.io.AppendCap (extractBlockPool fl.mp s2.mem).nSide s2.mem := by
            unfold SlotIoLayout.AppendCap; rw [ite_eq_right hup]; exact hcap2
          have hbkt_ms : (extractBlockPool fl.mp s2.mem).bktCount b <
              fl.mp.maxSlabs * fl.mp.K := by
            have hcap_eq : fl.mp.maxSlabs * fl.mp.K = capMaxWhp fl.N := by
              change maxSlabsPerBktWhp fl.N * slabSizeWhp fl.N = capMaxWhp fl.N
              unfold maxSlabsPerBktWhp slabSizeWhp capMaxWhp; ring
            rw [hbp12, hcap_eq]
            exact hcnt_lt
          have hbp_ap_eq : (Memory.spec 0).clientState s2
              (fastBpAppendProg ((fl.pBase, b), (keyQuotient (bWhp fl.N) u.val, v.val))) =
              (Memory.spec 0).clientState s2
                (bpAppendProg fl.bpL b (keyQuotient (bWhp fl.N) u.val) v.val) := by
            obtain ⟨_, hpt2, _, _⟩ := hr2
            unfold fastBpAppendProg bpAppendProg
            rw [StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
              clientResult_loadBlockPoolCtxProg hpt2]
          have hbp_v2 : fl.bpL.Valid fl.bpL.mp.w s2.frontier := by
            change fl.bpL.Valid fl.w s2.frontier; exact hv.w_eq ▸ hv2.bp_valid
          have hstep := bpAppendProg_paged_unperm hbp_v2 hinv2.bp_inv
            hup hb
            (show (extractBlockPool fl.bpL.mp s2.mem).nSide < fl.bpL.mp.nCap by
              change (extractBlockPool fl.mp s2.mem).nSide < fl.N; rw [hbp12]; exact hn_lt)
            (show (extractBlockPool fl.bpL.mp s2.mem).bktCount b <
                fl.bpL.mp.maxSlabs * fl.bpL.mp.K from hbkt_ms)
            hcap2 hq_lt hv_lt
          rw [← hbp_ap_eq] at hstep
          obtain ⟨hfr3, hr3, _, _, _, _, _, _, _, hfm3, _, _, _, _, hof3, _⟩ :=
            fastBpAppendProg_spec hr2 hinv2.bp_inv hb (by rw [hbp12]; exact hn_lt)
              (by rw [hbp12]; exact hcnt_lt) hcap_io2 hq_lt hv_lt
          generalize hs3_def : (Memory.spec 0).clientState s2
            (fastBpAppendProg ((fl.pBase, b), (keyQuotient (bWhp fl.N) u.val, v.val))) = s3
            at hfr3 hr3 hfm3 hof3 hstep
          have hv3 : fl.Valid w s3.frontier := hfr3.symm ▸ hv2
          have hof13 : ∀ a, ¬fl.OwnsFastAddr a → s3.mem a = s.mem a :=
            fun a ha => (hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha))
          have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
          have hsf3 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
              (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s3.mem :=
            hf.seed_fp.congr_on hw_pos fun a h1 h2 =>
              hof13 a (hv.not_ownsFast_seeds
                (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
                    have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
                      unfold offFpHash; exact Nat.le_add_right _ _
                    omega)
                (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
          obtain ⟨hrk_r, _⟩ := fastRKeyProg_spec hr3 hsf3 u
          have hrole_lt : (extractFastMeta fl s1.mem).curBufRole < 2 := hinv1.role_lt
          have hpt3 := And.left (And.right hr3)
          have hcr2_r : (Memory.spec 0).clientResult s3 (fastReadMetaProg (fl.pBase, 3)) =
              (extractFastMeta fl s1.mem).curBufRole :=
            (clientResult_fastReadMetaProg hpt3 (by decide)).trans (by
              change (extractFastMeta fl s3.mem).curBufRole =
                (extractFastMeta fl s1.mem).curBufRole
              rw [hfm3, hcr2])
          set cnt := (extractBlockPool fl.mp s.mem).bktCount b
          set rk := rKeyOf fl.c fl.U fl.N seeds.fp u
          obtain ⟨_, _, _, hbi_out_fn⟩ := fastBufInsertProg_ready
            (role := (extractFastMeta fl s1.mem).curBufRole) (rk := rk) (b := b) (loc := cnt) hr3
          generalize hs4_def : (Memory.spec 0).clientState s3
            (fastBufInsertProg ((fl.pBase, (extractFastMeta fl s1.mem).curBufRole),
              (rk, (b, cnt)))) = s4 at hbi_out_fn
          obtain ⟨_, _, _, _, _, _, hoi4, _⟩ :=
            fastTrieMod_frame hv3 hrole_lt (hbi_out_fn hrole_lt)
          have hs'_ns : (Memory.spec 0).clientState s
              (fastInsertNewStepProg ((fl.pBase, u.val), ((b, cnt), v.val))) = s4 := by
            unfold fastInsertNewStepProg; dsimp only
            rw [StateTransitionSpec.clientState_bind, hs1_def,
              StateTransitionSpec.clientState_bind, hs2_def,
              StateTransitionSpec.clientState_bind, clientState_fastFeistelSplitProg, hfs_r,
              StateTransitionSpec.clientState_bind, hs3_def,
              StateTransitionSpec.clientState_bind, clientState_fastRKeyProg, hrk_r,
              StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hcr2_r, hs4_def]
          rw [hs'_ns] at hfr_ns hinv_ns ⊢
          obtain ⟨_, _, _, hpg_adv, _⟩ := advanceSubEpochProg_spec (hfr_ns.symm ▸ hv) hinv_ns
          have hu4 : extractPageUnperm fl.io.pgL s4.mem = extractPageUnperm fl.io.pgL s3.mem :=
            extractPageUnperm_eq_of_io_outside hv.io_valid.w_pos hup hoi4
          exact PagedUnpermStep.congr_ends hu2 ((hpg_adv hup).1.trans hu4) hstep
  · have hnz : s.mem (fl.metaBase + 2) ≠ 0 := by rw [hm1]; exact Nat.one_ne_zero
    rw [ite_eq_right hnz]
    exact hfb_call hv hpt_top hfb fun h => (hcap_new h).2 hm1

private theorem largeEpochDeleteProg_paged_unperm {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs) (hup : fl.io.usePaged ≠ 0) (u : Fin fl.U) :
    let s' := (Memory.spec 0).clientState s (largeEpochDeleteProg (fl.pBase, u.val))
    PagedUnpermStep fl.io.side
      (extractPageUnperm fl.io.pgL s.mem) (extractPageUnperm fl.io.pgL s'.mem) := by
  dsimp only
  obtain ⟨hpt_top, hdisj_mode⟩ := hinv
  have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
      s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hpt_top (by decide)
  unfold largeEpochDeleteProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2]
  rcases hdisj_mode with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · rw [hm0, ite_eq_left rfl]
    set b := epochBucket fl.c fl.U fl.N seeds.bkt u
    have hb : b < numBucketsWhp fl.N := epochBucket_lt fl.c fl.U fl.N seeds.bkt u
    obtain ⟨hpr_st, _, hpr_b, hpr_res⟩ :=
      fastProbeProg_spec (slack := 0) (seeds := seeds) (s_abs := s_abs) hv hf u
    unfold fastDeleteProg
    rw [StateTransitionSpec.clientState_bind, hpr_st]; dsimp only
    cases hsu : s_abs u with
    | none =>
      rw [hsu] at hpr_res
      obtain ⟨hpr_tag, _⟩ := hpr_res
      rw [ite_eq_left hpr_tag, StateTransitionSpec.clientState_pure]
      exact PagedUnpermStep.of_eq rfl
    | some _ =>
      rw [hsu] at hpr_res
      obtain ⟨hpr_tag, hpr_loc, _, hpr_ku, _⟩ := hpr_res
      have hnz : Prod.fst (Prod.fst ((Memory.spec 0).clientResult s
          (fastProbeProg (fl.pBase, u.val)))) ≠ 0 := by
        rcases hpr_tag with h | h | h <;> omega
      rw [ite_eq_right hnz, hpr_b]
      exact fastRemoveAtProg_paged_unperm u (by decide) hv (hf.toGen 0) hup hb hpr_loc hpr_ku
  · have hnz : s.mem (fl.metaBase + 2) ≠ 0 := by rw [hm1]; exact Nat.one_ne_zero
    rw [ite_eq_right hnz]
    have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt_top 46 (by decide)
    have hle_u : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
    have hst_eq : (Memory.spec 0).clientState s (fastFallbackDeleteProg (fl.pBase, u.val)) =
        (Memory.spec 0).clientState s (fallbackDeleteProg (fl.fbL.toCtx, u.val)) := by
      unfold fastFallbackDeleteProg; dsimp only
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 46)) = s from rfl,
        prog_clientResult_read, hum, ite_eq_left hle_u,
        StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
        clientResult_loadFeistelCtx hpt_top,
        StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
        clientResult_loadBlockPoolCtxProg hpt_top]
      rfl
    rw [hst_eq]
    exact fallbackDeleteProg_paged_unperm hv.fb_valid hfb hup u

private theorem largeEpochPopAnyProg_paged_unperm {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs) (hup : fl.io.usePaged ≠ 0)
    (hpos : (s.mem (fl.metaBase + 2) = 0 → 0 < (extractBlockPool fl.mp s.mem).nSide) ∧
      (s.mem (fl.metaBase + 2) = 1 → 0 < (extractFallback fl.mp s.mem).nSide)) :
    let s' := (Memory.spec 0).clientState s (largeEpochPopAnyProg fl.pBase)
    PagedUnpermStep fl.io.side
      (extractPageUnperm fl.io.pgL s.mem) (extractPageUnperm fl.io.pgL s'.mem) := by
  dsimp only
  obtain ⟨hpt_top, hdisj_mode⟩ := hinv
  have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
      s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hpt_top (by decide)
  unfold largeEpochPopAnyProg
  rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2]
  rcases hdisj_mode with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · rw [hm0, ite_eq_left rfl]
    have hr := hf.ready hv rfl
    set bp := extractBlockPool fl.mp s.mem
    obtain ⟨_, _, hb, hl_lt⟩ := fastBpOwnerOfZeroProg_spec hr hf.bp_inv.1.core (hpos.1 hm0)
    set b := Prod.fst ((Memory.spec 0).clientResult s (fastBpOwnerOfZeroProg fl.pBase))
    have hcnt_pos : 0 < bp.bktCount b := Nat.zero_lt_of_lt hl_lt
    set lastLoc := bp.bktCount b - 1
    have hlast_lt : lastLoc < bp.bktCount b := by omega
    obtain ⟨hcnt_r, _⟩ := fastReadBktCntProg_spec hr hf.bp_inv.1.core hb
    obtain ⟨_, hread_r, _⟩ := fastBpReadAtProg_spec hr hf.bp_inv hb hlast_lt
    obtain ⟨u, _, hu, _, _, hq_u, _⟩ := hf.bktSlot_refines hb hlast_lt
    have hq_lt : Prod.fst (bpPairAt fl.bpL s.mem b lastLoc) < 2 ^ quotBitsWhp fl.U fl.N :=
      hq_u ▸ keyQuotient_bWhp_lt hv.N_le_U u
    obtain ⟨hrec_r, _⟩ := fastFeistelReconProg_spec hr hq_lt hf.seed_bkt (bkt := b)
    have hrec_val : (Memory.spec 0).clientResult s
        (fastFeistelReconProg (fl.pBase, (b, Prod.fst (bpPairAt fl.bpL s.mem b lastLoc)))) =
        u.val := hrec_r.trans hu.symm
    have hst_eq : (Memory.spec 0).clientState s (fastPopAnyProg fl.pBase) =
        (Memory.spec 0).clientState s (fastRemoveAtProg ((fl.pBase, b), (lastLoc, u.val))) := by
      unfold fastPopAnyProg
      rw [StateTransitionSpec.clientState_bind, clientState_fastBpOwnerOfZeroProg, pure_bind,
        StateTransitionSpec.clientState_bind, clientState_fastReadBktCntProg, hcnt_r,
        ite_eq_left hcnt_pos, pure_bind,
        StateTransitionSpec.clientState_bind, clientState_fastBpReadAtProg, hread_r,
        StateTransitionSpec.clientState_bind, clientState_fastFeistelReconProg, hrec_val,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    rw [hst_eq]
    exact fastRemoveAtProg_paged_unperm u (by decide) hv (hf.toGen 0) hup hb hlast_lt hu.symm
  · have hnz : s.mem (fl.metaBase + 2) ≠ 0 := by rw [hm1]; exact Nat.one_ne_zero
    rw [ite_eq_right hnz]
    have hst_eq : (Memory.spec 0).clientState s (fastFallbackPopAnyProg fl.pBase) =
        (Memory.spec 0).clientState s (fallbackPopAnyProg fl.fbL.toCtx) := by
      unfold fastFallbackPopAnyProg
      rw [StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
        clientResult_loadFeistelCtx hpt_top,
        StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
        clientResult_loadBlockPoolCtxProg hpt_top]
      rfl
    rw [hst_eq]
    exact fallbackPopAnyProg_paged_unperm hv.fb_valid hfb hup (hpos.2 hm1)

/-! ## Section 6: Uniform `EpochSlotInv` Paged `PageUnpermState` Theorems -/

/-- `epochInsertProg` preserves `PagedUnpermStep` on any active paged (`io.usePaged ≠ 0`)
`EpochSlotInv` slot. -/
theorem EpochSlotInv.insert_paged_unperm {c U V w pBase metaBase : ℕ} {io : SlotIoLayout}
    {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io 0 false sl s.mem)
    (hup : io.usePaged ≠ 0) (u : Fin U) (v : Fin V)
    (hcap_n : sl.s_abs u = none → sl.nCap ≠ 0 → (liveDom sl.s_abs).card < sl.nCap)
    (hcap_io : sl.s_abs u = none →
      (liveDom sl.s_abs).card < io.pgL.nCap ∧
      (extractPagePair io.pgL s.mem).totalItems + 1 ≤ io.pgL.nCap) :
    let s' := (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))
    PagedUnpermStep io.side
      (extractPageUnperm io.pgL s.mem) (extractPageUnperm io.pgL s'.mem) := by
  dsimp only
  have hm_ns := h.mem_nSide_eq
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨_, _, hv, hpt, _, hst⟩ := h
    have hp0 := hpt.1
    have hp1 := hpt.2.1
    have hstep : (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val)) =
        (Memory.spec 0).clientState s (smallEpochInsertProg ⟨metaBase, U, V, io⟩ u.val v.val) := by
      unfold epochInsertProg
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read pBase) = s from rfl,
        prog_clientResult_read, hp0, ite_eq_left rfl,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read (pBase + 1)) = s from rfl,
        prog_clientResult_read, hp1,
        StateTransitionSpec.clientState_bind, clientState_loadSmallIoCtxProg,
        clientResult_loadSmallIoCtxProg hpt]
      rfl
    rw [hstep]
    exact smallEpochInsertProg_paged_unperm hv hst hup u v fun hnone =>
      ⟨hm_ns.symm ▸ (hcap_io hnone).1, (hcap_io hnone).2⟩
  · rw [ite_eq_right h0] at h
    obtain ⟨hv, hinv, _, _, _⟩ := h
    have hpt := hinv.1
    have hN_pos : 0 < sl.nCap := lt_of_lt_of_le (whpThreshold_pos c) hv.thresh_le
    have hm0 : s.mem pBase = sl.nCap := hpt 0 (by decide)
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    have hstep : (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val)) =
        (Memory.spec 0).clientState s (largeEpochInsertProg ((fl.pBase, u.val), v.val)) := by
      unfold epochInsertProg
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read pBase) = s from rfl,
        prog_clientResult_read, hm0, ite_eq_right hN_pos.ne']
    rw [hstep]
    have happ : sl.s_abs u = none → io.AppendCap (s.mem (metaBase + 1)) s.mem := fun hnone => by
      unfold SlotIoLayout.AppendCap
      rw [ite_eq_right hup]; exact (hcap_io hnone).2
    exact largeEpochInsertProg_paged_unperm hv hinv hup u v fun hnone =>
      ⟨fun _ => ⟨show s.mem (metaBase + 1) < sl.nCap from hm_ns.symm ▸ hcap_n hnone h0, happ hnone⟩,
       fun _ => ⟨show s.mem (metaBase + 1) < sl.nCap from hm_ns.symm ▸ hcap_n hnone h0, happ hnone⟩⟩

/-- `epochDeleteProg` preserves `PagedUnpermStep` on any paged (`io.usePaged ≠ 0`) `EpochSlotInv`
slot (`draining = false` or `draining = true`). -/
theorem EpochSlotInv.delete_paged_unperm {c U V w pBase metaBase : ℕ} {io : SlotIoLayout}
    {draining : Bool} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io 0 draining sl s.mem)
    (hup : io.usePaged ≠ 0) (u : Fin U) :
    let s' := (Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val))
    PagedUnpermStep io.side
      (extractPageUnperm io.pgL s.mem) (extractPageUnperm io.pgL s'.mem) := by
  dsimp only
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨_, _, hv, hpt, _, hst⟩ := h
    have hp0 := hpt.1
    have hp1 := hpt.2.1
    have hstep : (Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val)) =
        (Memory.spec 0).clientState s (smallEpochDeleteProg ⟨metaBase, U, V, io⟩ u.val) := by
      unfold epochDeleteProg
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read pBase) = s from rfl,
        prog_clientResult_read, hp0, ite_eq_left rfl,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read (pBase + 1)) = s from rfl,
        prog_clientResult_read, hp1,
        StateTransitionSpec.clientState_bind, clientState_loadSmallIoCtxProg,
        clientResult_loadSmallIoCtxProg hpt]
      rfl
    rw [hstep]
    exact smallEpochDeleteProg_paged_unperm hv hst hup u
  · rw [ite_eq_right h0] at h
    obtain ⟨hv, hinv, _, _, _⟩ := h
    have hpt := hinv.1
    have hN_pos : 0 < sl.nCap := lt_of_lt_of_le (whpThreshold_pos c) hv.thresh_le
    have hm0 : s.mem pBase = sl.nCap := hpt 0 (by decide)
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    have hstep : (Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val)) =
        (Memory.spec 0).clientState s (largeEpochDeleteProg (fl.pBase, u.val)) := by
      unfold epochDeleteProg
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read pBase) = s from rfl,
        prog_clientResult_read, hm0, ite_eq_right hN_pos.ne']
    rw [hstep]
    exact largeEpochDeleteProg_paged_unperm hv hinv hup u

/-- `epochPopAnyProg` preserves `PagedUnpermStep` on any draining (`draining = true`) paged
(`io.usePaged ≠ 0`) `EpochSlotInv` slot with `0 < (liveDom sl.s_abs).card`. -/
theorem EpochSlotInv.popAny_paged_unperm {c U V w pBase metaBase : ℕ} {io : SlotIoLayout}
    {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io 0 true sl s.mem)
    (hup : io.usePaged ≠ 0) (hpos : 0 < (liveDom sl.s_abs).card) :
    let s' := (Memory.spec 0).clientState s (epochPopAnyProg pBase)
    PagedUnpermStep io.side
      (extractPageUnperm io.pgL s.mem) (extractPageUnperm io.pgL s'.mem) := by
  dsimp only
  have hm_ns := h.mem_nSide_eq
  unfold EpochSlotInv at h
  by_cases h0 : sl.nCap = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨_, _, hv, hpt, _, hst⟩ := h
    have hp0 := hpt.1
    have hp1 := hpt.2.1
    have hstep : (Memory.spec 0).clientState s (epochPopAnyProg pBase) =
        (Memory.spec 0).clientState s (smallEpochPopAnyProg ⟨metaBase, U, V, io⟩) := by
      unfold epochPopAnyProg
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read pBase) = s from rfl,
        prog_clientResult_read, hp0, ite_eq_left rfl,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read (pBase + 1)) = s from rfl,
        prog_clientResult_read, hp1,
        StateTransitionSpec.clientState_bind, clientState_loadSmallIoCtxProg,
        clientResult_loadSmallIoCtxProg hpt]
      rfl
    rw [hstep]
    exact smallEpochPopAnyProg_paged_unperm hv hst hup (hm_ns.symm ▸ hpos)
  · rw [ite_eq_right h0] at h
    obtain ⟨hv, hinv, _, _, _⟩ := h
    have hpt := hinv.1
    have hN_pos : 0 < sl.nCap := lt_of_lt_of_le (whpThreshold_pos c) hv.thresh_le
    have hm0 : s.mem pBase = sl.nCap := hpt 0 (by decide)
    let fl : FastEpochLayout := ⟨c, U, V, w, sl.nCap, metaBase, pBase, io⟩
    have hstep : (Memory.spec 0).clientState s (epochPopAnyProg pBase) =
        (Memory.spec 0).clientState s (largeEpochPopAnyProg fl.pBase) := by
      unfold epochPopAnyProg
      rw [StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read pBase) = s from rfl,
        prog_clientResult_read, hm0, ite_eq_right hN_pos.ne']
    rw [hstep]
    exact largeEpochPopAnyProg_paged_unperm hv hinv hup
      ⟨fun _ => show 0 < s.mem (metaBase + 1) from hm_ns.symm ▸ hpos,
       fun _ => show 0 < s.mem (metaBase + 1) from hm_ns.symm ▸ hpos⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

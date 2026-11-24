/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochPagedFrame
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvQuery

/-!
# Foreground Mutation Building Blocks (`DualEpochInvFGCore`)

Per-slot foreground updates (`SlotLatent.applyFG`, `DualLatent.applyFG`), mutation specifications
(`singleSlotMutate_raw`, `dualPagedMutate_raw`), partner paged-slot framing
(`EpochSlotInv.partner_paged_frame`), and countdown budget step preservation (`remBudget_fg_step`;
`prepGrowProg` and `syncLiveCountsProg` evaluations live in `DualEpochCtrlEval.lean`) for
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024].
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
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open EpochUpdate

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 4: Foreground `DualLatent.applyFG`, Per-Slot Mutation, and Framing -/

/-- Foreground `SlotLatent` update for `insert u v` (`opTag = 1`) or `delete u` (`opTag ≠ 1`). -/
@[expose] def SlotLatent.applyFG {c U V : ℕ} (draining : Bool) (opTag : ℕ)
    (u : Fin U) (v : Fin V) (sl : SlotLatent c U V) : SlotLatent c U V :=
  if opTag = 1 then
    if draining then
      ⟨sl.nCap, Function.update sl.s_abs u none, sl.seeds, sl.evs⟩
    else
      ⟨sl.nCap, Function.update sl.s_abs u (some v), sl.seeds,
        sl.evs ++ [EpochUpdate.insert u v]⟩
  else
    ⟨sl.nCap, Function.update sl.s_abs u none, sl.seeds,
      if draining then sl.evs else sl.evs ++ [EpochUpdate.delete u]⟩

@[simp] theorem SlotLatent.applyFG_nCap {c U V : ℕ} (draining : Bool) (opTag : ℕ)
    (u : Fin U) (v : Fin V) (sl : SlotLatent c U V) :
    (sl.applyFG draining opTag u v).nCap = sl.nCap := by
  unfold SlotLatent.applyFG; split_ifs <;> rfl

/-- Foreground `DualLatent` update across `userMutateProg` at phase `ph`. -/
@[expose] def DualLatent.applyFG {c U V : ℕ} (ph opTag : ℕ) (u : Fin U) (v : Fin V)
    (L : DualLatent c U V) : DualLatent c U V :=
  if ph ≤ 7 then
    { L with slotSrc := L.slotSrc.applyFG false opTag u v }
  else if ph = 8 then
    { L with
      slotSrc := L.slotSrc.applyFG true opTag u v
      slotDst := L.slotDst.applyFG false opTag u v }
  else
    { L with slotDst := L.slotDst.applyFG false opTag u v }

/-- Fresh insertions (`s_dict u = none`) satisfy strict capacity headroom `< N`. -/
theorem cap_lt_on_insert_none {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) {u : Fin U} (hnone : s_dict u = none) :
    let nLive := (Dictionary.dom s_dict).card
    let ph := s.mem (base + hdrPhase)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    nLive + 1 ≤ U ∧
    (nSrc ≠ 0 → nLive < nSrc) ∧
    (ph ≠ 0 → nDst ≠ 0 → nLive < nDst) := by
  dsimp only
  classical
  have hlt_U : (Dictionary.dom s_dict).card < U := by
    have hsub : Dictionary.dom s_dict ⊆ Finset.univ.erase u := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨fun hxu => ?_, Finset.mem_univ x⟩
      subst hxu
      unfold Dictionary.dom at hx
      simp [hnone] at hx
    calc (Dictionary.dom s_dict).card
        ≤ (Finset.univ.erase u).card := Finset.card_le_card hsub
      _ = U - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin U]
      _ < U := Nat.sub_lt (Nat.zero_lt_of_lt u.isLt) Nat.one_pos
  have hsched := h.sched
  set nLive := (Dictionary.dom s_dict).card
  set ph := s.mem (base + hdrPhase)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  refine ⟨by omega, fun hnS => ?_, fun hph0 hnD => ?_⟩
  · by_cases hp0 : ph = 0
    · rw [ite_eq_left hp0] at hsched
      have hidle : DualIdleSafe c U nSrc nLive := hsched.safe_fr.1
      simp only [DualIdleSafe, hnS, ↓reduceIte] at hidle
      have hth_big := whpThreshold_ge_pow20 c
      by_cases hlt : nSrc < U
      · have := hidle.2.2.2.2 hlt; omega
      · omega
    · rw [ite_eq_right hp0] at hsched
      have hel : 16 * (L.elapsed + 2) ≤ max (whpThreshold c) nSrc := hsched.budget.2.2
      have hd_hi := hsched.drift_hi; have hd_lo := hsched.drift_lo
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hd_hi hd_lo
      have har := active_rebuild_safe (nSrc := nSrc) (nDst := nDst)
        hsched.post_trig hsched.trig_cap
        (nCur := nLive + 1) (d := L.elapsed + 1)
        (by omega) (by omega) (by omega) (by omega)
      have hs_c := har.2.1
      simp only [EpochCapSafe, hnS, ↓reduceIte] at hs_c
      omega
  · rw [ite_eq_right hph0] at hsched
    have hel : 16 * (L.elapsed + 2) ≤ max (whpThreshold c) nSrc := hsched.budget.2.2
    have hd_hi := hsched.drift_hi; have hd_lo := hsched.drift_lo
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hd_hi hd_lo
    have har := active_rebuild_safe (nSrc := nSrc) (nDst := nDst)
      hsched.post_trig hsched.trig_cap
      (nCur := nLive + 1) (d := L.elapsed + 1)
      (by omega) (by omega) (by omega) (by omega)
    have hd_c := har.2.2.1
    simp only [EpochCapSafe, hnD, ↓reduceIte] at hd_c
    omega

/-- Address range classification for `slotOwnsAddr` relative to `base`. -/
theorem slotOwnsAddr_bounds {c w base pad pBase metaBase nCap : ℕ} {io : SlotIoLayout}
    (hsm_m : nCap = 0 → metaBase = base + hdrSmallMeta0 ∨ metaBase = base + hdrSmallMeta1)
    (hlg_m : nCap ≠ 0 → metaBase = base + 192 ∨ metaBase = base + 192 + pad)
    (hpg_mb : io.usePaged ≠ 0 →
      base + 192 ≤ io.pgL.metaBase ∧ base + 192 ≤ io.pgL.itemBase)
    (hsp_mb : io.usePaged = 0 → io.sideBit ≠ 0 → io.pgL.metaBase = base + hdrSplit ∧
      base + 192 ≤ io.pgL.offDir ∧ base + 192 ≤ io.pgL.itemBase)
    (hdir_ib : io.usePaged = 0 → io.sideBit = 0 → base + 192 ≤ io.pgL.itemBase) :
    ∀ addr, slotOwnsAddr c w metaBase nCap io addr →
      base ≤ addr ∧
      (addr < base + 48 → addr = base + hdrSplit ∧ io.usePaged = 0 ∧ io.sideBit ≠ 0) ∧
      ¬(base + 64 ≤ addr ∧ addr < base + 192) := by
  let _ := pBase
  intro addr ha
  have hio_b : io.OwnsAddr addr →
      base ≤ addr ∧
      (addr < base + 48 → addr = base + hdrSplit ∧ io.usePaged = 0 ∧ io.sideBit ≠ 0) ∧
      ¬(base + 64 ≤ addr ∧ addr < base + 192) := by
    intro hio
    unfold SlotIoLayout.OwnsAddr at hio
    by_cases hup : io.usePaged = 0
    · rw [ite_eq_left hup] at hio
      by_cases hsb : io.sideBit = 0
      · rw [ite_eq_left hsb] at hio
        have hib := hdir_ib hup hsb
        unfold PageArenaLayout.OwnsItemAddr at hio
        exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
      · rw [ite_eq_right hsb] at hio
        obtain ⟨hm_eq, hod, hib⟩ := hsp_mb hup hsb
        rcases hio with rfl | ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [hm_eq]; unfold hdrSplit
          exact ⟨by omega, fun _ => ⟨rfl, hup, hsb⟩, by omega⟩
        · exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
        · exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
    · rw [ite_eq_right hup] at hio
      obtain ⟨hmb, hib⟩ := hpg_mb hup
      unfold PageArenaLayout.OwnsAddr PageArenaLayout.OwnsMetaAddr
        PageArenaLayout.OwnsItemAddr at hio
      rcases hio with (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩) | ⟨h1, _⟩ <;>
        exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
  unfold slotOwnsAddr at ha
  by_cases h0 : nCap = 0
  · rw [ite_eq_left h0] at ha
    have hsm := hsm_m h0
    rcases ha with rfl | rfl | hio
    · rcases hsm with rfl | rfl <;> simp only [hdrSmallMeta0, hdrSmallMeta1] <;>
        exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
    · rcases hsm with rfl | rfl <;> simp only [hdrSmallMeta0, hdrSmallMeta1] <;>
        exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
    · exact hio_b hio
  · rw [ite_eq_right h0] at ha
    have hlg := hlg_m h0
    rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩ | hio
    · dsimp only at h1
      rcases hlg with rfl | rfl <;>
        exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
    · dsimp only at h1
      rcases hlg with rfl | rfl <;>
        exact ⟨by omega, fun h => absurd h (by omega), by omega⟩
    · exact hio_b hio

/-- Unified single-slot foreground mutation (`epochInsertProg` when `opTag = 1`, `epochDeleteProg`
when `opTag ≠ 1`) on an active (`draining = false`) `EpochSlotInv` slot. -/
theorem singleSlotMutate_raw {c U V w pBase metaBase opTag v_val : ℕ}
    {io : SlotIoLayout} {sl : SlotLatent c U V} {s : Memory.State}
    (h : EpochSlotInv c U V w s.frontier pBase metaBase io 0 false sl s.mem)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hcap_n : opTag = 1 → sl.s_abs u = none → sl.nCap ≠ 0 → (liveDom sl.s_abs).card < sl.nCap)
    (hcap_io : opTag = 1 → sl.s_abs u = none →
      (liveDom sl.s_abs).card < io.pgL.nCap ∧
      (io.usePaged ≠ 0 → (extractPagePair io.pgL s.mem).totalItems + 1 ≤ io.pgL.nCap)) :
    let prog : Memory.Prog Unit :=
      if opTag = 1 then epochInsertProg ((pBase, u.val), v_val)
      else epochDeleteProg (pBase, u.val)
    let s' := (Memory.spec 0).clientState s prog
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    let sl' := sl.applyFG false opTag u v
    (if opTag = 1 then EpochInsertProgPre w pBase s else EpochProgPre w pBase s) ∧
    s'.frontier = s.frontier ∧
    EpochSlotInv c U V w s'.frontier pBase metaBase io slack' false sl' s'.mem ∧
    toDictState sl'.s_abs =
      (if opTag = 1 then Function.update (toDictState sl.s_abs) u (some v.val)
       else Function.update (toDictState sl.s_abs) u none) ∧
    (∀ addr, ¬slotOwnsAddr c w metaBase sl.nCap io addr → s'.mem addr = s.mem addr) ∧
    (io.usePaged = 0 → io.sideBit ≠ 0 →
      s'.mem io.pgL.metaBase = s.mem io.pgL.metaBase ∧
      (SplitHiQuotBounded io (s.mem (metaBase + 1)) s.mem →
        SplitHiQuotBounded io (s'.mem (metaBase + 1)) s'.mem)) ∧
    (io.usePaged ≠ 0 →
      PagedUnpermStep io.side (extractPageUnperm io.pgL s.mem)
        (extractPageUnperm io.pgL s'.mem)) ∧
    ((sl.nCap = 0 → (liveDom sl.s_abs).card ≤ 2 * whpThreshold c) →
      sl'.GoodCovers →
      memoryCost prog s ≤ epochStepCost c) := by
  dsimp only
  by_cases hop1 : opTag = 1
  · rw [ite_eq_left hop1, ite_eq_left hop1, hv_eq hop1]
    have hsp := h.insert_spec u v (hcap_n hop1) (hcap_io hop1)
    have hpg : io.usePaged ≠ 0 →
        PagedUnpermStep io.side (extractPageUnperm io.pgL s.mem)
          (extractPageUnperm io.pgL
            ((Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))).mem) :=
      fun hup => h.insert_paged_unperm hup u v (hcap_n hop1) fun hnone =>
        ⟨(hcap_io hop1 hnone).1, (hcap_io hop1 hnone).2 hup⟩
    have hsl'_eq : sl.applyFG false opTag u v =
        ⟨sl.nCap, Function.update sl.s_abs u (some v), sl.seeds,
          sl.evs ++ [EpochUpdate.insert u v]⟩ := by
      unfold SlotLatent.applyFG; rw [ite_eq_left hop1]; rfl
    rw [hsl'_eq, ite_eq_left hop1]
    exact ⟨h.epochInsertProgPre, hsp.1, hsp.2.1, toDictState_insert sl.s_abs u v,
      hsp.2.2.1, hsp.2.2.2.1, hpg, hsp.2.2.2.2.2⟩
  · rw [ite_eq_right hop1, ite_eq_right hop1]
    have hsp := h.delete_spec u
    have hpg : io.usePaged ≠ 0 →
        PagedUnpermStep io.side (extractPageUnperm io.pgL s.mem)
          (extractPageUnperm io.pgL
            ((Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val))).mem) :=
      fun hup => h.delete_paged_unperm hup u
    have hsl'_eq : sl.applyFG false opTag u v =
        ⟨sl.nCap, Function.update sl.s_abs u none, sl.seeds,
          sl.evs ++ [EpochUpdate.delete u]⟩ := by
      unfold SlotLatent.applyFG; rw [ite_eq_right hop1]; rfl
    rw [hsl'_eq, ite_eq_right hop1]
    exact ⟨h.epochProgPre, hsp.1, hsp.2.1, toDictState_delete sl.s_abs u,
      hsp.2.2.1, hsp.2.2.2.1, hpg, hsp.2.2.2.2.2⟩

/-- Non-interference of a partner paged slot `A` (`pagedSlotIo sbA pgHost`) on slot `B`'s
64-word `ParamTable` `[pB, pB + 64)` and non-page metadata `slotOwnsNonPageMeta`. -/
theorem not_paged_slotOwnsAddr_partner {c U V w fr mbA sbA pB mbB sbB : ℕ}
    {pgHost : PageArenaLayout} {drB : Bool} {slA slB : SlotLatent c U V} {m : ℕ → ℕ}
    (hB : EpochSlotInv c U V w fr pB mbB (pagedSlotIo sbB pgHost) 0 drB slB m)
    (hpm : pB + 64 ≤ mbA ∨
      mbA + (if slA.nCap = 0 then 2 else offPageDir c w slA.nCap) ≤ pB)
    (hmm :
      mbA + (if slA.nCap = 0 then 2 else offPageDir c w slA.nCap) ≤ mbB ∨
      mbB + (if slB.nCap = 0 then 2 else offPageDir c w slB.nCap) ≤ mbA) :
    (∀ a, pB ≤ a → a < pB + 64 →
      ¬slotOwnsAddr c w mbA slA.nCap (pagedSlotIo sbA pgHost) a) ∧
    (∀ a, slotOwnsNonPageMeta c w mbB slB.nCap a →
      ¬slotOwnsAddr c w mbA slA.nCap (pagedSlotIo sbA pgHost) a) := by
  have hrawB := hB; unfold EpochSlotInv at hrawB
  have hio_eq : ∀ a, (pagedSlotIo sbA pgHost).OwnsAddr a ↔ (pagedSlotIo sbB pgHost).OwnsAddr a :=
    fun _ => Iff.rfl
  refine ⟨fun a h1 h2 ha => ?_, fun a hmB ha => ?_⟩
  · have hn_ioB : ¬(pagedSlotIo sbB pgHost).OwnsAddr a := by
      by_cases hb0 : slB.nCap = 0
      · rw [ite_eq_left hb0] at hrawB
        exact fun hia => hrawB.2.2.2.2.1 a h1 h2 (Or.inr (Or.inr hia))
      · rw [ite_eq_right hb0] at hrawB; exact hrawB.1.disj_pBase_io a h1 h2
    unfold slotOwnsAddr at ha
    by_cases ha0 : slA.nCap = 0
    · rw [ite_eq_left ha0] at ha hpm
      rcases ha with h | h | hia
      · dsimp only at h; omega
      · dsimp only at h; omega
      · exact hn_ioB ((hio_eq a).mp hia)
    · rw [ite_eq_right ha0] at ha hpm
      have h32 : 32 ≤ offPageDir c w slA.nCap := by
        unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
          offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
          offBktHash
        omega
      rcases ha with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | hia
      · dsimp only at hlo hhi; omega
      · dsimp only at hlo hhi; omega
      · exact hn_ioB ((hio_eq a).mp hia)
  · have hn_ioB : ¬(pagedSlotIo sbB pgHost).OwnsAddr a := by
      unfold slotOwnsNonPageMeta at hmB
      by_cases hb0 : slB.nCap = 0
      · rw [ite_eq_left hb0] at hrawB hmB
        rcases hmB with ⟨h1, h2⟩ | ⟨hne, _⟩
        · exact hrawB.2.2.1.disjoint_hdr a (by dsimp only; omega)
        · exact absurd hb0 hne
      · rw [ite_eq_right hb0] at hrawB hmB
        exact hrawB.1.disj_fast_io a (hmB.imp id And.right)
    have hmB_lt :
        mbB ≤ a ∧ a < mbB + (if slB.nCap = 0 then 2 else offPageDir c w slB.nCap) := by
      unfold slotOwnsNonPageMeta at hmB
      by_cases hb0 : slB.nCap = 0
      · simp only [hb0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at hmB ⊢
        omega
      · simp only [hb0, ↓reduceIte, ne_eq, not_false_eq_true, true_and] at hmB ⊢
        have h32 : 32 ≤ offPageDir c w slB.nCap := by
          unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
            offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
            offBktHash
          omega
        rcases hmB with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    unfold slotOwnsAddr at ha
    by_cases ha0 : slA.nCap = 0
    · rw [ite_eq_left ha0] at ha hmm
      rcases ha with h | h | hia
      · dsimp only at h; omega
      · dsimp only at h; omega
      · exact hn_ioB ((hio_eq a).mp hia)
    · rw [ite_eq_right ha0] at ha hmm
      have h32 : 32 ≤ offPageDir c w slA.nCap := by
        unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
          offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
          offBktHash
        omega
      rcases ha with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ | hia
      · dsimp only at hlo hhi; omega
      · dsimp only at hlo hhi; omega
      · exact hn_ioB ((hio_eq a).mp hia)

/-- Frame transport for a paged `EpochSlotInv` (`pagedSlotIo sb pgHost`, `cleanPhase = 0`) across
a mutation executed on the partner side `pagedSlotIo sb' pgHost`. -/
theorem EpochSlotInv.partner_paged_frame {c U V w fr pB mb sb sb' nP : ℕ}
    {pgHost : PageArenaLayout} {dr : Bool} {sl : SlotLatent c U V} {m₁ m₂ : ℕ → ℕ}
    (h : EpochSlotInv c U V w fr pB mb (pagedSlotIo sb pgHost) 0 dr sl m₁)
    (hpartner : (pagedSlotIo sb' pgHost).StateInv nP 0 m₂)
    (hcp2 : (extractPageUnperm pgHost m₂).cleanPhase = 0)
    (hp_out : ∀ a, pB ≤ a → a < pB + 64 → m₂ a = m₁ a)
    (hm_out : ∀ a, slotOwnsNonPageMeta c w mb sl.nCap a → m₂ a = m₁ a)
    (hvl : (extractPagePair pgHost m₂).virtLen (pagedSlotIo sb pgHost).side =
      (extractPagePair pgHost m₁).virtLen (pagedSlotIo sb pgHost).side)
    (hpair : ∀ idx < (extractPagePair pgHost m₁).virtLen (pagedSlotIo sb pgHost).side,
      slotIoPairAt (pagedSlotIo sb pgHost) m₂ idx =
        slotIoPairAt (pagedSlotIo sb pgHost) m₁ idx) :
    EpochSlotInv c U V w fr pB mb (pagedSlotIo sb pgHost) 0 dr sl m₂ := by
  have hup : (pagedSlotIo sb pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hup' : (pagedSlotIo sb' pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hraw := h; unfold EpochSlotInv at hraw
  have hio₁ := h.io_stateInv
  unfold SlotIoLayout.StateInv at hio₁ hpartner
  rw [ite_eq_right hup] at hio₁
  rw [ite_eq_right hup'] at hpartner
  have hvl₁ : (extractPagePair pgHost m₁).virtLen (pagedSlotIo sb pgHost).side = m₁ (mb + 1) :=
    hio₁.2.2.2.2.1
  have hio₂ : (pagedSlotIo sb pgHost).StateInv (m₁ (mb + 1)) 0 m₂ := by
    unfold SlotIoLayout.StateInv; rw [ite_eq_right hup]
    exact ⟨hpartner.1, hpartner.2.1, hpartner.2.2.1, hpartner.2.2.2.1,
      hvl.trans hvl₁, fun hp => absurd hcp2 hp.ne', hpartner.2.2.2.2.2.2⟩
  exact h.transfer_io h.io_valid
    (by by_cases h0 : sl.nCap = 0
        · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.w_eq.symm
        · rw [ite_eq_right h0] at hraw; exact hraw.1.w_eq_io.symm)
    ⟨fun h0 => by rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.qBits_eq,
     fun h0 => by rw [ite_eq_right h0] at hraw; exact hraw.1.qBits_le⟩
    (by by_cases h0 : sl.nCap = 0
        · rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.vBits_eq
        · rw [ite_eq_right h0] at hraw; exact hraw.1.vBits_eq)
    ⟨fun h0 => by
      rw [ite_eq_left h0] at hraw
      exact hraw.2.2.2.1.congr fun a h1 h2 => hp_out a h1 h2,
     fun h0 => by
      rw [ite_eq_right h0] at hraw
      exact hraw.2.1.1.congr fun a h1 h2 => hp_out a h1 (by dsimp only at h1 h2; omega)⟩
    (fun a h1 h2 => by
      by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw
        exact fun hia => hraw.2.2.2.2.1 a h1 h2 (Or.inr (Or.inr hia))
      · rw [ite_eq_right h0] at hraw; exact hraw.1.disj_pBase_io a h1 h2)
    (fun a ha => by
      unfold slotOwnsNonPageMeta at ha
      by_cases h0 : sl.nCap = 0
      · rw [ite_eq_left h0] at hraw ha
        rcases ha with ⟨h1, h2⟩ | ⟨hne, _⟩
        · exact hraw.2.2.1.disjoint_hdr a (by dsimp only; omega)
        · exact absurd h0 hne
      · rw [ite_eq_right h0] at hraw ha
        exact hraw.1.disj_fast_io a (ha.imp id And.right))
    hm_out hio₂ (fun p hp => hpair p (hvl₁.symm ▸ hp))

/-- Dual-slot paged foreground mutation in Phase `8` (`epochDeleteProg` on `pSrc` followed by
`epochInsertProg` or `epochDeleteProg` on `pDst`). -/
theorem dualPagedMutate_raw {c U V w pSrc mbSrc pDst mbDst opTag v_val : ℕ}
    {pgHost : PageArenaLayout} {slSrc slDst : SlotLatent c U V} {s : Memory.State}
    (hs : EpochSlotInv c U V w s.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc s.mem)
    (hd : EpochSlotInv c U V w s.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst s.mem)
    (hdj : DisjointOpt slDst.s_abs slSrc.s_abs)
    (hcp0 : (extractPageUnperm pgHost s.mem).cleanPhase = 0)
    (_hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc)
    (hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ pDst)
    (hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if slDst.nCap = 0 then 2 else offPageDir c w slDst.nCap) ≤ pSrc)
    (hmm_disj :
      mbSrc + (if slSrc.nCap = 0 then 2 else offPageDir c w slSrc.nCap) ≤ mbDst ∨
      mbDst + (if slDst.nCap = 0 then 2 else offPageDir c w slDst.nCap) ≤ mbSrc)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hcap_d : opTag = 1 → (orOpt slDst.s_abs slSrc.s_abs) u = none →
      (slDst.nCap ≠ 0 →
        (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card < slDst.nCap) ∧
      (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card + 1 ≤ pgHost.nCap)
    (hcap_ov : opTag = 1 →
      (slDst.nCap ≠ 0 →
        (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ slDst.nCap) ∧
      (liveDom slDst.s_abs).card + (liveDom slSrc.s_abs).card ≤ pgHost.nCap) :
    let prog : Memory.Prog Unit :=
      if opTag = 1 then
        epochDeleteProg (pSrc, u.val) >>= fun _ => epochInsertProg ((pDst, u.val), v_val)
      else
        epochDeleteProg (pSrc, u.val) >>= fun _ => epochDeleteProg (pDst, u.val)
    let s1 := (Memory.spec 0).clientState s (epochDeleteProg (pSrc, u.val))
    let s' := (Memory.spec 0).clientState s prog
    let slSrc' := slSrc.applyFG true opTag u v
    let slDst' := slDst.applyFG false opTag u v
    EpochProgPre w pSrc s ∧
    (if opTag = 1 then EpochInsertProgPre w pDst s1 else EpochProgPre w pDst s1) ∧
    s'.frontier = s.frontier ∧
    (extractPageUnperm pgHost s'.mem).cleanPhase = 0 ∧
    DisjointOpt slDst'.s_abs slSrc'.s_abs ∧
    toDictState (orOpt slDst'.s_abs slSrc'.s_abs) =
      (if opTag = 1 then
         Function.update (toDictState (orOpt slDst.s_abs slSrc.s_abs)) u (some v.val)
       else Function.update (toDictState (orOpt slDst.s_abs slSrc.s_abs)) u none) ∧
    EpochSlotInv c U V w s'.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true slSrc' s'.mem ∧
    EpochSlotInv c U V w s'.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false slDst' s'.mem ∧
    (∀ addr,
      ¬slotOwnsAddr c w mbSrc slSrc.nCap (pagedSlotIo 0 pgHost) addr →
      ¬slotOwnsAddr c w mbDst slDst.nCap (pagedSlotIo 1 pgHost) addr →
      s'.mem addr = s.mem addr) ∧
    ((slSrc.nCap = 0 → (liveDom slSrc.s_abs).card ≤ 2 * whpThreshold c) →
      (slDst.nCap = 0 → (liveDom slDst.s_abs).card ≤ 2 * whpThreshold c) →
      slSrc.GoodCovers → slDst'.GoodCovers →
      memoryCost prog s ≤ 2 * epochStepCost c + 4) := by
  dsimp only
  have hup0 : (pagedSlotIo 0 pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hup1 : (pagedSlotIo 1 pgHost).usePaged ≠ 0 := Nat.one_ne_zero
  have hsp_s := hs.delete_spec u
  set s1 := (Memory.spec 0).clientState s (epochDeleteProg (pSrc, u.val))
  have hfr1 : s1.frontier = s.frontier := hsp_s.1
  have hsl_s1 : EpochSlotInv c U V w s1.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
      ⟨slSrc.nCap, Function.update slSrc.s_abs u none, slSrc.seeds, slSrc.evs⟩ s1.mem := by
    have hslk0 : (if (pagedSlotIo 0 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 0 pgHost).pgL s.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp0)
    simpa only [hslk0, ↓reduceIte] using hsp_s.2.1
  have hcp1 : (extractPageUnperm pgHost s1.mem).cleanPhase = 0 :=
    (hs.delete_paged_unperm hup0 u).1 hcp0
  have hout_s1 := hsp_s.2.2.1
  have hpg_s1 := hsp_s.2.2.2.2.1 hup0
  obtain ⟨hno_s_pDst, hno_s_mDst⟩ :=
    not_paged_slotOwnsAddr_partner (sbA := 0) (slA := slSrc) hd hpm_s hmm_disj
  obtain ⟨hno_d_pSrc, hno_d_mSrc⟩ :=
    not_paged_slotOwnsAddr_partner (sbA := 1) (slA := slDst) hs hpm_d hmm_disj.symm
  have hsl_d1 : EpochSlotInv c U V w s1.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
      slDst s1.mem :=
    (hfr1 ▸ hd).partner_paged_frame hsl_s1.io_stateInv hcp1
      (fun a h1 h2 => hout_s1 a (hno_s_pDst a h1 h2))
      (fun a ha => hout_s1 a (hno_s_mDst a ha))
      hpg_s1.1 hpg_s1.2
  by_cases hop1 : opTag = 1
  · rw [ite_eq_left hop1, ite_eq_left hop1, hv_eq hop1]
    have hti_s1 : (extractPagePair pgHost s1.mem).totalItems =
        (liveDom (Function.update slSrc.s_abs u none)).card + (liveDom slDst.s_abs).card := by
      have hi0 := hsl_s1.io_stateInv; have hi1 := hsl_d1.io_stateInv
      unfold SlotIoLayout.StateInv at hi0 hi1
      rw [ite_eq_right hup0] at hi0; rw [ite_eq_right hup1] at hi1
      have hns0 := hsl_s1.mem_nSide_eq; have hns1 := hsl_d1.mem_nSide_eq
      have hvl0 : (extractPagePair pgHost s1.mem).virtLen false = s1.mem (mbSrc + 1) :=
        hi0.2.2.2.2.1
      have hvl1 : (extractPagePair pgHost s1.mem).virtLen true = s1.mem (mbDst + 1) :=
        hi1.2.2.2.2.1
      dsimp only at hns0
      unfold PagePairState.totalItems
      rw [hvl0, hvl1, hns0, hns1]
    have hcap_n1 : slDst.s_abs u = none → slDst.nCap ≠ 0 →
        (liveDom slDst.s_abs).card < slDst.nCap := fun hd_none hne_d => by
      by_cases hs_none : slSrc.s_abs u = none
      · have hor : (orOpt slDst.s_abs slSrc.s_abs) u = none := by
          simp only [orOpt, Option.or, hd_none, hs_none]
        have := (hcap_d hop1 hor).1 hne_d; omega
      · have hcard_lt : (liveDom (Function.update slSrc.s_abs u none)).card <
            (liveDom slSrc.s_abs).card := by
          rw [liveDom_delete_card, ite_eq_right hs_none]
          have hpos : 0 < (liveDom slSrc.s_abs).card :=
            Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hs_none⟩
          omega
        have := (hcap_ov hop1).1 hne_d; omega
    have hcap_io1 : slDst.s_abs u = none →
        (liveDom slDst.s_abs).card < (pagedSlotIo 1 pgHost).pgL.nCap ∧
        ((pagedSlotIo 1 pgHost).usePaged ≠ 0 →
          (extractPagePair (pagedSlotIo 1 pgHost).pgL s1.mem).totalItems + 1 ≤
            (pagedSlotIo 1 pgHost).pgL.nCap) := by
      intro hd_none
      dsimp only [pagedSlotIo]
      rw [hti_s1]
      by_cases hs_none : slSrc.s_abs u = none
      · have hor : (orOpt slDst.s_abs slSrc.s_abs) u = none := by
          simp only [orOpt, Option.or, hd_none, hs_none]
        have hc := (hcap_d hop1 hor).2
        rw [liveDom_delete_card, ite_eq_left hs_none]
        exact ⟨by omega, fun _ => by omega⟩
      · have hcard_lt : (liveDom (Function.update slSrc.s_abs u none)).card <
            (liveDom slSrc.s_abs).card := by
          rw [liveDom_delete_card, ite_eq_right hs_none]
          have hpos : 0 < (liveDom slSrc.s_abs).card :=
            Finset.card_pos.mpr ⟨u, (mem_liveDom_iff _ _).mpr hs_none⟩
          omega
        have hc := (hcap_ov hop1).2
        exact ⟨by omega, fun _ => by omega⟩
    have hsp_d := hsl_d1.insert_spec u v hcap_n1 hcap_io1
    set s2 := (Memory.spec 0).clientState s1 (epochInsertProg ((pDst, u.val), v.val))
    have hst_tot : (Memory.spec 0).clientState s
        (epochDeleteProg (pSrc, u.val) >>= fun _ => epochInsertProg ((pDst, u.val), v.val)) = s2 :=
      StateTransitionSpec.clientState_bind ..
    rw [hst_tot]
    have hfr2 : s2.frontier = s1.frontier := hsp_d.1
    have hslk0 : (if (pagedSlotIo 1 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 1 pgHost).pgL s1.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp1)
    have hsl_d2 : EpochSlotInv c U V w s2.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        (slDst.applyFG false opTag u v) s2.mem := by
      have heq_d : slDst.applyFG false opTag u v =
          ⟨slDst.nCap, Function.update slDst.s_abs u (some v), slDst.seeds,
            slDst.evs ++ [EpochUpdate.insert u v]⟩ := by
        unfold SlotLatent.applyFG; rw [ite_eq_left hop1]; rfl
      rw [heq_d]; simpa only [hslk0] using hsp_d.2.1
    have hcp2 : (extractPageUnperm pgHost s2.mem).cleanPhase = 0 :=
      (hsl_d1.insert_paged_unperm hup1 u v hcap_n1
        (fun hnone => ⟨(hcap_io1 hnone).1, (hcap_io1 hnone).2 hup1⟩)).1 hcp1
    have hout_d2 := hsp_d.2.2.1
    have hpg_d2 := hsp_d.2.2.2.2.1 hup1
    have hsl_s2 : EpochSlotInv c U V w s2.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        (slSrc.applyFG true opTag u v) s2.mem := by
      have heq_s : slSrc.applyFG true opTag u v =
          ⟨slSrc.nCap, Function.update slSrc.s_abs u none, slSrc.seeds, slSrc.evs⟩ := by
        unfold SlotLatent.applyFG; rw [ite_eq_left hop1]; rfl
      rw [heq_s]
      exact (hfr2 ▸ hsl_s1).partner_paged_frame hsl_d2.io_stateInv hcp2
        (fun a h1 h2 => hout_d2 a (hno_d_pSrc a h1 h2))
        (fun a ha => hout_d2 a (hno_d_mSrc a ha))
        hpg_d2.1 hpg_d2.2
    obtain ⟨hor_eq, hdj'⟩ := orOpt_insert_dst_delete_src slDst.s_abs slSrc.s_abs hdj u v
    have heq_s_abs : (slSrc.applyFG true opTag u v).s_abs = Function.update slSrc.s_abs u none := by
      unfold SlotLatent.applyFG; rw [ite_eq_left hop1]; rfl
    have heq_d_abs : (slDst.applyFG false opTag u v).s_abs =
        Function.update slDst.s_abs u (some v) := by
      unfold SlotLatent.applyFG; rw [ite_eq_left hop1]; rfl
    refine ⟨hs.epochProgPre, hsl_d1.epochInsertProgPre, hfr2.trans hfr1, hcp2,
      by rw [heq_d_abs, heq_s_abs]; exact hdj',
      by rw [heq_d_abs, heq_s_abs, hor_eq, ite_eq_left hop1, toDictState_insert],
      hsl_s2, hsl_d2, fun a ha_s ha_d => (hout_d2 a ha_d).trans (hout_s1 a ha_s),
      fun hsm_s hsm_d hgc_s hgc_d => ?_⟩
    rw [Realization.memoryCost_bind']
    have hc1 := hsp_s.2.2.2.2.2 hsm_s hgc_s
    have heq_d_gc : (⟨slDst.nCap, Function.update slDst.s_abs u (some v), slDst.seeds,
        slDst.evs ++ [EpochUpdate.insert u v]⟩ : SlotLatent c U V).GoodCovers =
        (slDst.applyFG false opTag u v).GoodCovers := by
      unfold SlotLatent.applyFG; rw [ite_eq_left hop1]; rfl
    have hc2 := hsp_d.2.2.2.2.2 hsm_d (heq_d_gc.symm ▸ hgc_d)
    change memoryCost (epochDeleteProg (pSrc, u.val)) s +
      memoryCost (epochInsertProg ((pDst, u.val), v.val)) s1 ≤ 2 * epochStepCost c + 4
    omega
  · rw [ite_eq_right hop1, ite_eq_right hop1]
    have hsp_d := hsl_d1.delete_spec u
    set s2 := (Memory.spec 0).clientState s1 (epochDeleteProg (pDst, u.val))
    have hst_tot : (Memory.spec 0).clientState s
        (epochDeleteProg (pSrc, u.val) >>= fun _ => epochDeleteProg (pDst, u.val)) = s2 :=
      StateTransitionSpec.clientState_bind ..
    rw [hst_tot]
    have hfr2 : s2.frontier = s1.frontier := hsp_d.1
    have hslk0 : (if (pagedSlotIo 1 pgHost).usePaged = 0 ∨
        (extractPageUnperm (pagedSlotIo 1 pgHost).pgL s1.mem).cleanPhase = 0
        then 0 else 24) = 0 := ite_eq_left (Or.inr hcp1)
    have hsl_d2 : EpochSlotInv c U V w s2.frontier pDst mbDst (pagedSlotIo 1 pgHost) 0 false
        (slDst.applyFG false opTag u v) s2.mem := by
      have heq_d : slDst.applyFG false opTag u v =
          ⟨slDst.nCap, Function.update slDst.s_abs u none, slDst.seeds,
            slDst.evs ++ [EpochUpdate.delete u]⟩ := by
        unfold SlotLatent.applyFG; rw [ite_eq_right hop1]; rfl
      rw [heq_d]; simpa only [hslk0, Bool.false_eq_true, ↓reduceIte] using hsp_d.2.1
    have hcp2 : (extractPageUnperm pgHost s2.mem).cleanPhase = 0 :=
      (hsl_d1.delete_paged_unperm hup1 u).1 hcp1
    have hout_d2 := hsp_d.2.2.1
    have hpg_d2 := hsp_d.2.2.2.2.1 hup1
    have hsl_s2 : EpochSlotInv c U V w s2.frontier pSrc mbSrc (pagedSlotIo 0 pgHost) 0 true
        (slSrc.applyFG true opTag u v) s2.mem := by
      have heq_s : slSrc.applyFG true opTag u v =
          ⟨slSrc.nCap, Function.update slSrc.s_abs u none, slSrc.seeds, slSrc.evs⟩ := by
        unfold SlotLatent.applyFG; rw [ite_eq_right hop1]; rfl
      rw [heq_s]
      exact (hfr2 ▸ hsl_s1).partner_paged_frame hsl_d2.io_stateInv hcp2
        (fun a h1 h2 => hout_d2 a (hno_d_pSrc a h1 h2))
        (fun a ha => hout_d2 a (hno_d_mSrc a ha))
        hpg_d2.1 hpg_d2.2
    obtain ⟨hor_eq, hdj'⟩ := orOpt_delete_both slDst.s_abs slSrc.s_abs hdj u
    have heq_s_abs : (slSrc.applyFG true opTag u v).s_abs = Function.update slSrc.s_abs u none := by
      unfold SlotLatent.applyFG; rw [ite_eq_right hop1]
    have heq_d_abs :
        (slDst.applyFG false opTag u v).s_abs = Function.update slDst.s_abs u none := by
      unfold SlotLatent.applyFG; rw [ite_eq_right hop1]
    refine ⟨hs.epochProgPre, hsl_d1.epochProgPre, hfr2.trans hfr1, hcp2,
      by rw [heq_d_abs, heq_s_abs]; exact hdj',
      by rw [heq_d_abs, heq_s_abs, hor_eq, ite_eq_right hop1, toDictState_delete],
      hsl_s2, hsl_d2, fun a ha_s ha_d => (hout_d2 a ha_d).trans (hout_s1 a ha_s),
      fun hsm_s hsm_d hgc_s hgc_d => ?_⟩
    rw [Realization.memoryCost_bind']
    have hc1 := hsp_s.2.2.2.2.2 hsm_s hgc_s
    have heq_d_gc : (⟨slDst.nCap, Function.update slDst.s_abs u none, slDst.seeds,
        slDst.evs ++ [EpochUpdate.delete u]⟩ : SlotLatent c U V).GoodCovers =
        (slDst.applyFG false opTag u v).GoodCovers := by
      unfold SlotLatent.applyFG; rw [ite_eq_right hop1]; rfl
    have hc2 := hsp_d.2.2.2.2.2 hsm_d (heq_d_gc.symm ▸ hgc_d)
    change memoryCost (epochDeleteProg (pSrc, u.val)) s +
      memoryCost (epochDeleteProg (pDst, u.val)) s1 ≤ 2 * epochStepCost c + 4
    omega


/-- Foreground mutations never increase the mid-step `remRebuildBudget` (`remB' ≤ remB`). -/
theorem remBudget_fg_step {nRef stg ph logSub logK growDiff growDiff' sp sp'
    slideRem slideRem' mDst offBM maxPg pgB cur rem shrinkDiff shrinkDiff' : ℕ}
    (_hph0 : ph ≠ 0) (h2_le : 2 ≤ remRebuildBudget nRef stg ph logSub logK
      growDiff sp slideRem mDst offBM maxPg pgB cur rem shrinkDiff)
    (hg : ph = 2 → growDiff' ≤ growDiff)
    (hsp3 : ph = 3 → sp' ≤ sp)
    (hsl10 : ph = 10 → slideRem' ≤ slideRem + 1)
    (hsh11 : ph = 11 → shrinkDiff' ≤ shrinkDiff + 2)
    (hph_le11 : ph ≤ 11) :
    let remB := remRebuildBudget nRef stg ph logSub logK
      growDiff sp slideRem mDst offBM maxPg pgB cur rem shrinkDiff
    let remB' := remRebuildBudget nRef stg ph logSub logK
      growDiff' sp' (slideRem' - 1) mDst offBM maxPg pgB cur rem (shrinkDiff' - 2)
    2 ≤ remB' ∧ remB' ≤ remB := by
  dsimp only
  have hf_ge1 : ∀ p, p ≠ 0 → p ≤ 10 → 1 ≤ futureRebuildBudget nRef stg p := by
    intro p hp0 hle10
    unfold futureRebuildBudget maxTailPhasesBudget
    dsimp only
    split_ifs <;> omega
  unfold remRebuildBudget at h2_le ⊢
  dsimp only at h2_le ⊢
  by_cases hp1 : ph = 1
  · subst hp1; have hf := hf_ge1 1 (by decide) (by decide)
    simp only [↓reduceIte] at h2_le ⊢; omega
  · simp only [hp1, ↓reduceIte] at h2_le ⊢
    by_cases hp2 : ph = 2
    · subst hp2; have hf := hf_ge1 2 (by decide) (by decide)
      have hdiv := Nat.div_le_div_right (c := 1022) (hg rfl)
      simp only [↓reduceIte] at h2_le ⊢; omega
    · simp only [hp2, ↓reduceIte] at h2_le ⊢
      by_cases hp3 : ph = 3
      · subst hp3; have hf := hf_ge1 3 (by decide) (by decide)
        have hdiv := Nat.div_le_div_right (c := 1024) (hsp3 rfl)
        simp only [↓reduceIte] at h2_le ⊢; omega
      · simp only [hp3, ↓reduceIte] at h2_le ⊢
        by_cases hp4 : ph = 4
        · subst hp4; have hf := hf_ge1 4 (by decide) (by decide)
          simp only [↓reduceIte] at h2_le ⊢; omega
        · simp only [hp4, ↓reduceIte] at h2_le ⊢
          by_cases hp5 : ph = 5
          · subst hp5; have hf := hf_ge1 5 (by decide) (by decide)
            simp only [↓reduceIte] at h2_le ⊢; omega
          · simp only [hp5, ↓reduceIte] at h2_le ⊢
            by_cases hp6 : ph = 6
            · subst hp6; have hf := hf_ge1 6 (by decide) (by decide)
              simp only [↓reduceIte] at h2_le ⊢; omega
            · simp only [hp6, ↓reduceIte] at h2_le ⊢
              by_cases hp7 : ph = 7
              · subst hp7; have hf := hf_ge1 7 (by decide) (by decide)
                simp only [↓reduceIte] at h2_le ⊢; omega
              · simp only [hp7, ↓reduceIte] at h2_le ⊢
                by_cases hp8 : ph = 8
                · subst hp8; simp only [↓reduceIte] at h2_le ⊢; omega
                · simp only [hp8, ↓reduceIte] at h2_le ⊢
                  by_cases hp9 : ph = 9
                  · subst hp9; simp only [↓reduceIte] at h2_le ⊢; omega
                  · simp only [hp9, ↓reduceIte] at h2_le ⊢
                    by_cases hp10 : ph = 10
                    · subst hp10; have hf := hf_ge1 10 (by decide) (by decide)
                      have hle : slideRem' - 1 ≤ slideRem := by have := hsl10 rfl; omega
                      have hdiv := Nat.div_le_div_right (c := 1023) hle
                      simp only [↓reduceIte] at h2_le ⊢; omega
                    · simp only [hp10, ↓reduceIte] at h2_le ⊢
                      have heq11 : ph = 11 := by omega
                      subst heq11
                      have hle : shrinkDiff' - 2 ≤ shrinkDiff := by have := hsh11 rfl; omega
                      have hdiv := Nat.div_le_div_right (c := 1022) hle
                      omega

/-- Transports `EpochSlotInv` across synchronized `nCap` updates (`s ↦ s_grow` and `s_raw ↦ m3`)
where only `hdrLive`, `p0 + 60`, and `p1 + 60` change. -/
theorem EpochSlotInv.lift_sync {c U V w base fr₁ fr₂ pB mb slack nc' : ℕ}
    {io0 : SlotIoLayout} {dr : Bool} {sl : SlotLatent c U V} {m₁ m₂ : ℕ → ℕ}
    (hsl : EpochSlotInv c U V w fr₁ pB mb io0 slack dr sl m₁)
    (hfr_le : fr₁ ≤ fr₂) (hnc_w : nc' < 2 ^ w)
    (hpB : pB = base + hdrPBase0 ∨ pB = base + hdrPBase1)
    (hmb_pos : (sl.nCap = 0 ∧ (mb = base + hdrSmallMeta0 ∨ mb = base + hdrSmallMeta1)) ∨
      (sl.nCap ≠ 0 ∧ base + 192 ≤ mb))
    (hio_pos : (io0.usePaged = 0 → io0.sideBit ≠ 0 →
        io0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io0.pgL.offDir) ∧
      (io0.usePaged ≠ 0 → base + 192 ≤ io0.pgL.metaBase) ∧
      base + 192 ≤ io0.pgL.itemBase)
    (hfd : io0.usePaged = 0 → io0.sideBit = 0 →
      io0.pgL.itemBase + pairStreamWords nc' io0.pgL.qBits io0.pgL.vBits io0.pgL.w ≤ fr₂)
    (hfs : io0.usePaged = 0 → io0.sideBit ≠ 0 →
      io0.pgL.itemBase + pairStreamWords nc' io0.pgL.offTail io0.pgL.vBits io0.pgL.w ≤ fr₂)
    (hfp : io0.usePaged ≠ 0 →
      nc' ≤ (io0.pgL.maxPages - 2) * io0.pgL.pgB ∧
      io0.pgL.itemBase + pairStreamWords nc' io0.pgL.qBits io0.pgL.vBits io0.pgL.w ≤ fr₂)
    (hm_ib : mb + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io0.pgL.itemBase ∧
      (io0.usePaged = 0 → io0.sideBit ≠ 0 →
        mb + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ io0.pgL.offDir))
    (hnc_ge : m₁ (mb + 1) ≤ nc')
    (hpg_t : io0.usePaged ≠ 0 → (extractPagePair io0.pgL m₁).totalItems ≤ nc')
    (hm_p60 : m₂ (pB + 60) = nc')
    (hm_p_rest : ∀ a, pB ≤ a → a < pB + 64 → a ≠ pB + 60 → m₂ a = m₁ a)
    (hm_out : ∀ a, (a = base + hdrSplit ∨ (base + 48 ≤ a ∧ a < base + 64) ∨ base + 192 ≤ a) →
      m₂ a = m₁ a) :
    EpochSlotInv c U V w fr₂ pB mb (io0.withNCap nc') slack dr sl m₂ := by
  have hp_le192 : pB + 64 ≤ base + 192 ∧ base + 64 ≤ pB := by
    rcases hpB with rfl | rfl <;> simp only [hdrPBase0, hdrPBase1] <;> omega
  have hpm : pB + 64 ≤ mb ∨ mb + (if sl.nCap = 0 then 2 else offPageDir c w sl.nCap) ≤ pB := by
    rcases hmb_pos with ⟨hc0, rfl | rfl⟩ | ⟨_, h192⟩
    · rw [ite_eq_left hc0]; unfold hdrSmallMeta0; omega
    · rw [ite_eq_left hc0]; unfold hdrSmallMeta1; omega
    · exact Or.inl (by omega)
  have hp_ib : pB + 64 ≤ io0.pgL.itemBase ∧
      (io0.usePaged = 0 → io0.sideBit ≠ 0 → pB + 64 ≤ io0.pgL.offDir) :=
    ⟨by omega, fun hup hsb => by have := (hio_pos.1 hup hsb).2; omega⟩
  have hupd := (hsl.mono_frontier hfr_le).lift_nCap hnc_w hfd hfs hfp hp_ib hm_ib hpm hnc_ge hpg_t
  refine hupd.congr_mem (fun a ha1 ha2 => ?_) (fun a ha => ?_) (fun a ha => ?_)
  · by_cases ha60 : a = pB + 60
    · subst ha60; rw [hm_p60, Function.update_self]
    · rw [Function.update_of_ne ha60]; exact hm_p_rest a ha1 ha2 ha60
  · have hout_a : (base + 48 ≤ a ∧ a < base + 64) ∨ base + 192 ≤ a := by
      unfold slotOwnsNonPageMeta at ha
      rcases hmb_pos with ⟨hc0, rfl | rfl⟩ | ⟨_, h192⟩
      · simp only [hc0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
          hdrSmallMeta0] at ha; omega
      · simp only [hc0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false,
          hdrSmallMeta1] at ha; omega
      · right; rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> omega
    rw [Function.update_of_ne (by rcases hout_a with _ | _ <;> omega)]
    exact hm_out a (Or.inr hout_a)
  · have hout_a : a = base + hdrSplit ∨ base + 192 ≤ a := by
      unfold SlotIoLayout.OwnsAddr at ha
      simp only [SlotIoLayout.withNCap] at ha
      by_cases hup : io0.usePaged = 0
      · simp only [hup, ↓reduceIte] at ha
        by_cases hsb : io0.sideBit = 0
        · simp only [hsb, ↓reduceIte] at ha
          unfold PageArenaLayout.OwnsItemAddr at ha; dsimp only at ha
          exact Or.inr (by have := hio_pos.2.2; omega)
        · simp only [hsb, ↓reduceIte] at ha
          obtain ⟨hm_eq, hod⟩ := hio_pos.1 hup hsb
          have hib := hio_pos.2.2
          rcases ha with rfl | ⟨h1, _⟩ | ⟨h1, _⟩
          · exact Or.inl hm_eq
          · exact Or.inr (by omega)
          · exact Or.inr (by omega)
      · simp only [hup, ↓reduceIte] at ha
        have hmb_pg := hio_pos.2.1 hup
        have hib := hio_pos.2.2
        unfold PageArenaLayout.OwnsAddr PageArenaLayout.OwnsMetaAddr
          PageArenaLayout.OwnsItemAddr at ha
        dsimp only at ha
        rcases ha with (⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩) | ⟨h1, _⟩ <;>
          exact Or.inr (by omega)
    rw [Function.update_of_ne
      (by unfold hdrSplit at hout_a; rcases hout_a with rfl | _ <;> omega)]
    exact hm_out a (hout_a.imp id Or.inr)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

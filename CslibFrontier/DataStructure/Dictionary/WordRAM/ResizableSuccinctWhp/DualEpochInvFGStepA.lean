/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvFGSetup

/-!
# Foreground Mutation Regime `ph ≤ 7` (`fgStep_le7`)
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

/-- `FGStepOut` parameterized by opaque `s_prep`, `k_grow`, `s_mid` so tactics never unfold
`(Memory.spec 0).clientState` in `whnf`. -/
@[expose] def FGStepOutAux (c U V w base opTag v_val : ℕ) (u : Fin U) (v : Fin V)
    (s_dict : Dictionary.State U) (L : DualLatent c U V)
    (s s_prep : Memory.State) (k_grow : ℕ) (s_mid : Memory.State) : Prop :=
  let nLive := (Dictionary.dom s_dict).card
  let s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  let nLive' := (Dictionary.dom s_dict').card
  let ph := s.mem (base + hdrPhase)
  let stg := s.mem (base + hdrStage)
  let nSrc := s.mem (base + hdrNSrc)
  let nDst := s.mem (base + hdrNDst)
  let pad := s.mem (base + hdrPad)
  let ibLo := s.mem (base + hdrItemLo)
  let ibHi := s.mem (base + hdrItemHi)
  let qLo := s.mem (base + hdrQLo)
  let qHi := s.mem (base + hdrQHi)
  let sp := s.mem (base + hdrSplit)
  let cur := s.mem (base + hdrCur)
  let uDone := s.mem (base + hdrUnpermDone)
  let vB := valBits V
  let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
  let pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
    else base + hdrPBase0
  let nHost := if nDst = 0 then nSrc else nDst
  let mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  let pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
  let pgHost_fin := hostPageLayout c w nHost mbHost ibHi qHi vB nLive'
  let capSrc := if stg = 0 then nSrc else nDst
  let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  let mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  let L_mid := L.applyFG ph opTag u v
  let slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
  UserMutatePre w ((base, opTag), (u.val, v_val)) s_grow ∧
  s_mid.frontier = s_grow.frontier ∧
  s_mid.mem (base + hdrLive) = nLive' ∧
  (∀ addr, addr < base + 48 → addr ≠ base + hdrLive → addr ≠ base + hdrSplit →
    s_mid.mem addr = s.mem addr) ∧
  (ph ≠ 3 → ph ≠ 10 → s_mid.mem (base + hdrSplit) = sp) ∧
  ((ph = 3 ∨ ph = 10) →
    s_mid.mem (base + hdrSplit) ≤ nLive' ∧
    s_mid.mem (base + hdrSplit) ≤ sp ∧
    nLive' - s_mid.mem (base + hdrSplit) ≤ (nLive - sp) + 1 ∧
    SplitHiQuotBounded (splitSlotIo w vB base ibLo qLo ibHi qHi nLive') nLive' s_mid.mem) ∧
  (ph = 4 → ∀ off < cur, s_mid.mem (mbDst + off) = 0) ∧
  (ph = 5 →
    ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
       io := directSlotIo w vB base ibHi qHi nLive' } : FastEpochLayout).ParamTable
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update s_mid.mem
          (pDst + 48) 0) (pDst + 49) 0) (pDst + 50) (base + hdrSplit)) (pDst + 51) ibHi)
          (pDst + 52) qHi) (pDst + 53) 1) (pDst + 54) w) (pDst + 55) 32) (pDst + 56) 4)
          (pDst + 57) ibHi) (pDst + 58) qHi) (pDst + 59) vB) (pDst + 60) nLive') ∧
    (∀ k, 1 ≤ k → k < 32 → s_mid.mem (mbDst + k) = 0) ∧
    (∀ off, offBktMeta c w nDst ≤ off → off < offPageDir c w nDst →
      s_mid.mem (mbDst + off) = 0)) ∧
  ((ph = 6 ∨ ph = 7) →
    extractPagePair pgHost_fin s_mid.mem = extractPagePair pgHost s.mem ∧
    (0 < nDst →
      EpochSlotInv c U V w s_mid.frontier pDst mbDst
        (directSlotIo w vB base ibHi qHi nLive') 0 false L_mid.slotDst s_mid.mem)) ∧
  (ph = 9 → uDone = 0 →
    0 < (extractPageUnperm pgHost_fin s_mid.mem).cleanPhase ∧
    (extractPageUnperm pgHost_fin s_mid.mem).cleanPhase < 4 ∧
    (extractPageUnperm pgHost_fin s_mid.mem).unpermRank ≤ L.unpermBound + 64) ∧
  (ph ≤ 7 →
    L_mid.slotSrc.nCap = capSrc ∧
    toDictState L_mid.slotSrc.s_abs = s_dict' ∧
    EpochSlotInv c U V w s_mid.frontier pSrc mbSrc
      (activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive')
      0 false L_mid.slotSrc s_mid.mem ∧
    (0 < ph → 0 < capSrc → L_mid.slotSrc.evs.length ≤ 2 * capSrc + L.elapsed + 1)) ∧
  (ph = 8 →
    L_mid.slotSrc.nCap = capSrc ∧ L_mid.slotDst.nCap = nDst ∧
    DisjointOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs ∧
    toDictState (orOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs) = s_dict' ∧
    (extractPageUnperm pgHost_fin s_mid.mem).cleanPhase = 0 ∧
    EpochSlotInv c U V w s_mid.frontier pSrc mbSrc (pagedSlotIo 0 pgHost_fin) 0 true
      L_mid.slotSrc s_mid.mem ∧
    EpochSlotInv c U V w s_mid.frontier pDst mbDst (pagedSlotIo 1 pgHost_fin) 0 false
      L_mid.slotDst s_mid.mem ∧
    (0 < capSrc → L_mid.slotSrc.evs.length ≤ 3 * capSrc) ∧
    (0 < nDst →
      L_mid.slotDst.evs.length + (liveDom L_mid.slotSrc.s_abs).card ≤
        nDst + L.elapsed + 1)) ∧
  (9 ≤ ph →
    L_mid.slotDst.nCap = nDst ∧
    toDictState L_mid.slotDst.s_abs = s_dict' ∧
    EpochSlotInv c U V w s_mid.frontier pDst mbDst
      (activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive' uDone)
      slackDst' false L_mid.slotDst s_mid.mem ∧
    (0 < nDst → L_mid.slotDst.evs.length ≤ nDst + L.elapsed + 1)) ∧
  ((ph ≤ 7 → L_mid.slotSrc.GoodCovers) →
    (ph = 8 → L_mid.slotSrc.GoodCovers ∧ L_mid.slotDst.GoodCovers) →
    (9 ≤ ph → L_mid.slotDst.GoodCovers) →
    memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow ≤
      2 * epochStepCost c + 80)


private theorem paramTable_ph5Mask_congr {c U V w nDst mbDst pDst base ibHi qHi nLive nLive' : ℕ}
    {m0 m1 : ℕ → ℕ}
    (hpt : ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
              io := directSlotIo w (valBits V) base ibHi qHi nLive } : FastEpochLayout).ParamTable
      (dualPh5MaskMem V w base pDst ibHi qHi nLive m0))
    (heq : ∀ k < 63, ¬(48 ≤ k ∧ k ≤ 60) → m1 (pDst + k) = m0 (pDst + k)) :
    ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
       io := directSlotIo w (valBits V) base ibHi qHi nLive' } : FastEpochLayout).ParamTable
      (dualPh5MaskMem V w base pDst ibHi qHi nLive' m1) := by
  intro k hk
  unfold dualPh5MaskMem at hpt ⊢
  dsimp only
  by_cases hk60 : k = 60
  · subst hk60; exact Function.update_self ..
  · have hpw_eq :
        ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
           io := directSlotIo w (valBits V) base ibHi qHi nLive' } :
          FastEpochLayout).paramWord k =
        ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
           io := directSlotIo w (valBits V) base ibHi qHi nLive } :
          FastEpochLayout).paramWord k := by
      interval_cases k <;> first | rfl | exact absurd rfl hk60
    have hpt_k := hpt k hk; dsimp only at hpt_k
    rw [hpw_eq, ← hpt_k]
    by_cases hk48 : 48 ≤ k ∧ k < 60
    · obtain ⟨_, _⟩ := hk48
      interval_cases k <;> (
        repeat (first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)]))
    · iterate 13 rw [Function.update_of_ne (by omega)]
      iterate 13 rw [Function.update_of_ne (by omega)]
      exact heq k hk (by omega)

private theorem paramTable_direct_withNCap {c U V w N mbDst pDst vB base ibHi qHi nLive nLive' : ℕ}
    {m0 m1 : ℕ → ℕ}
    (hpt : ({ c := c, U := U, V := V, w := w, N := N, metaBase := mbDst, pBase := pDst,
              io := directSlotIo w vB base ibHi qHi nLive } : FastEpochLayout).ParamTable m0)
    (h60 : m1 (pDst + 60) = nLive')
    (heq : ∀ k < 63, k ≠ 60 → m1 (pDst + k) = m0 (pDst + k)) :
    ({ c := c, U := U, V := V, w := w, N := N, metaBase := mbDst, pBase := pDst,
       io := directSlotIo w vB base ibHi qHi nLive' } : FastEpochLayout).ParamTable m1 := by
  intro k hk
  dsimp only
  by_cases hk60 : k = 60
  · subst hk60; exact h60
  · have hpw_eq :
        ({ c := c, U := U, V := V, w := w, N := N, metaBase := mbDst, pBase := pDst,
           io := directSlotIo w vB base ibHi qHi nLive' } : FastEpochLayout).paramWord k =
        ({ c := c, U := U, V := V, w := w, N := N, metaBase := mbDst, pBase := pDst,
           io := directSlotIo w vB base ibHi qHi nLive } : FastEpochLayout).paramWord k := by
      interval_cases k <;> first | rfl | exact absurd rfl hk60
    have hpt_k := hpt k hk; dsimp only at hpt_k
    rw [hpw_eq, ← hpt_k]
    exact heq k hk hk60

private theorem fgStep_le7_ph47 {c U V w base opTag k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep s_mid : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (_hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hle7 : s.mem (base + hdrPhase) ≤ 7)
    (hs_mid_fr : s_mid.frontier = s.frontier + k_grow)
    (hm_out_192 :
      let nLive := (Dictionary.dom s_dict).card
      let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
      let stg := s.mem (base + hdrStage)
      let ph := s.mem (base + hdrPhase)
      let nSrc := s.mem (base + hdrNSrc)
      let nDst := s.mem (base + hdrNDst)
      let pad := s.mem (base + hdrPad)
      let ibLo := s.mem (base + hdrItemLo)
      let ibHi := s.mem (base + hdrItemHi)
      let qLo := s.mem (base + hdrQLo)
      let qHi := s.mem (base + hdrQHi)
      let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
        else base + 192 + pad
      let io_sal := activeSrcIo c w (valBits V) base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
      ∀ addr, base + 192 ≤ addr → ¬slotOwnsAddr c w mbSrc L.slotSrc.nCap io_sal addr →
        s_mid.mem addr = s.mem addr)
    (hm_pDst :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      let nLive' := (Dictionary.dom s_dict').card
      let ph := s.mem (base + hdrPhase)
      let stg := s.mem (base + hdrStage)
      let pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
        else base + hdrPBase0
      4 ≤ ph → s_mid.mem (pDst + 60) = nLive' ∧
        ∀ k < 63, k ≠ 60 → s_mid.mem (pDst + k) = s.mem (pDst + k)) :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let cur := s.mem (base + hdrCur)
    let vB := valBits V
    let pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
      else base + hdrPBase0
    let nHost := if nDst = 0 then nSrc else nDst
    let mbHost := if nDst = 0 then base + 192
      else if stg = 0 then base + 192 + pad else base + 192
    let pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
    let pgHost_fin := hostPageLayout c w nHost mbHost ibHi qHi vB nLive'
    let mbDst := if ph < 10 then
        (if nDst = 0 then base + hdrSmallMeta1
         else if stg = 0 then base + 192 + pad else base + 192)
      else
        (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
    let L_mid := L.applyFG ph opTag u v
    (ph = 4 → ∀ off < cur, s_mid.mem (mbDst + off) = 0) ∧
    (ph = 5 →
      ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
         io := directSlotIo w vB base ibHi qHi nLive' } : FastEpochLayout).ParamTable
        (dualPh5MaskMem V w base pDst ibHi qHi nLive' s_mid.mem) ∧
      (∀ k, 1 ≤ k → k < 32 → s_mid.mem (mbDst + k) = 0) ∧
      (∀ off, offBktMeta c w nDst ≤ off → off < offPageDir c w nDst →
        s_mid.mem (mbDst + off) = 0)) ∧
    ((ph = 6 ∨ ph = 7) →
      extractPagePair pgHost_fin s_mid.mem = extractPagePair pgHost s.mem ∧
      (0 < nDst →
        EpochSlotInv c U V w s_mid.frontier pDst mbDst
          (directSlotIo w vB base ibHi qHi nLive') 0 false L_mid.slotDst s_mid.mem)) := by
  have hw11 := h.hw11; have hUw := h.U_lt; have hmSrc_eq := h.mSrc_eq
  have hph4_inv := h.ph4_inv; have hph5_inv := h.ph5_inv
  have hsl_le7 := h.sl_le7; have hsl_67 := h.sl_67
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost, dualPh5MaskMem] at hph4_inv hph5_inv hsl_le7 hsl_67
  have hsrc_safe := hsetup.src_safe; have hdst_safe := hsetup.dst_safe
  have hcard_step := hsetup.card_step
  have hibLo_ge := hsetup.ibLo_ge; have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hod_le_nSrc := hsetup.od_le_nSrc; have hod_le_nDst := hsetup.od_le_nDst
  have hge2_all := hsetup.ge2_sched; have hnDst0_all := hsetup.nDst0_sched
  have hfr_n' := hsetup.fr_n'
  dsimp only at hcard_step hfr_n' hm_out_192 hm_pDst ⊢
  rw [← hk_grow_def] at hfr_n'
  clear hk_grow_def
  set nLive := (Dictionary.dom s_dict).card
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set nLive' := (Dictionary.dom s_dict').card
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qLo := s.mem (base + hdrQLo)
  set qHi := s.mem (base + hdrQHi)
  set cur := s.mem (base + hdrCur)
  set vB := valBits V
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pDst := if ph < 10 then (if stg = 0 then p1 else p0) else p0
  set nHost := if nDst = 0 then nSrc else nDst
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
  set pgHost_fin := hostPageLayout c w nHost mbHost ibHi qHi vB nLive'
  set capSrc := if stg = 0 then nSrc else nDst
  set mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  set mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  set L_mid := L.applyFG ph opTag u v
  set io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
  have hcap_s := (hsl_le7 hle7).1
  have hdisj_dst_47 : 4 ≤ ph → 0 < nDst →
      ∀ addr, mbDst ≤ addr → addr < mbDst + mDst →
        ¬slotOwnsAddr c w mbSrc L.slotSrc.nCap io_sal addr := by
    intro hge4 hd_pos addr had1 had2 hown
    have hge2 := hge2_all (by omega) (by omega)
    have hmD := hge2.1; have hp_eq := hge2.2.1; have hibH := hge2.2.2.2.2.1
    have hp_ge : mSrc ≤ pad ∧ mDst ≤ pad := by
      rw [hp_eq, hmSrc_eq, hmD]; exact ⟨le_max_left _ _, le_max_right _ _⟩
    have hio_al_eq : io_sal = directSlotIo w vB base ibHi qHi nAlloc := by
      dsimp only [io_sal, activeSrcIo]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    have hn_io : ¬io_sal.OwnsAddr addr := by
      rw [hio_al_eq]
      simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo, ↓reduceIte]
      rw [hibH, ite_eq_right hd_pos.ne']
      dsimp only [mbDst] at had1 had2
      rw [ite_eq_left (by omega : ph < 10), ite_eq_right hd_pos.ne'] at had1 had2
      split_ifs at had1 had2 <;> omega
    unfold slotOwnsAddr at hown; rw [hcap_s] at hown
    dsimp only [mbDst] at had1 had2
    rw [ite_eq_left (by omega : ph < 10), ite_eq_right hd_pos.ne'] at had1 had2
    by_cases hst0 : stg = 0
    · rw [ite_eq_left hst0] at had1 had2
      dsimp only [capSrc, mbSrc] at hown
      simp only [hst0, ↓reduceIte] at hown
      by_cases hnS0 : nSrc = 0
      · simp only [hnS0, ↓reduceIte, SmallEpochLayout.OwnsAddr] at hown
        rcases hown with rfl | rfl | hio
        · unfold hdrSmallMeta0 at had1; omega
        · unfold hdrSmallMeta0 at had1; omega
        · exact hn_io hio
      · simp only [hnS0, ↓reduceIte, FastEpochLayout.OwnsFastAddr] at hown
        have hod := hod_le_nSrc hnS0
        have h32 : 32 ≤ epochMetaWordsWhp c w nSrc :=
          thirtyTwo_le_epochMetaWordsWhp (by
            simp only [EpochCapSafe, hnS0, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1)
        rcases hown with ⟨_, hhi⟩ | ⟨_, hhi⟩ | hio
        · omega
        · omega
        · exact hn_io hio
    · rw [ite_eq_right hst0] at had1 had2
      dsimp only [capSrc, mbSrc] at hown
      simp only [hst0, hd_pos.ne', ↓reduceIte, FastEpochLayout.OwnsFastAddr] at hown
      rcases hown with ⟨hlo, _⟩ | ⟨hlo, _⟩ | hio
      · omega
      · omega
      · exact hn_io hio
  refine ⟨?_, ?_, ?_⟩
  · intro hp4 off hoff
    obtain ⟨hd_pos, _, hz4⟩ := hph4_inv hp4
    have hmb_ge : base + 192 ≤ mbDst := by
      dsimp only [mbDst]; rw [ite_eq_left (by omega : ph < 10), ite_eq_right hd_pos.ne']
      split_ifs <;> omega
    rw [hm_out_192 (mbDst + off) (by omega)
      (hdisj_dst_47 (by omega) hd_pos _ (Nat.le_add_right _ _) (by omega))]
    exact hz4 off hoff
  · intro hp5
    obtain ⟨hd_pos, _, _, hpt5, hzh5, hzt5⟩ := hph5_inv hp5
    have hmb_ge : base + 192 ≤ mbDst := by
      dsimp only [mbDst]; rw [ite_eq_left (by omega : ph < 10), ite_eq_right hd_pos.ne']
      split_ifs <;> omega
    have hod_le := hod_le_nDst (by omega) hd_pos.ne'
    have hmD_eq := (hge2_all (by omega) (by omega)).1
    have hpt5' :
        ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
           io := directSlotIo w vB base ibHi qHi nLive' } : FastEpochLayout).ParamTable
          (dualPh5MaskMem V w base pDst ibHi qHi nLive' s_mid.mem) :=
      paramTable_ph5Mask_congr hpt5 fun k hk hk_out =>
        (hm_pDst (by omega)).2 k hk (by omega)
    have h32_m : 32 ≤ mDst := by
      rw [hmD_eq]
      exact thirtyTwo_le_epochMetaWordsWhp (by
        have hds := hdst_safe; rw [ite_eq_right (by omega : ph ≠ 0)] at hds
        simp only [EpochCapSafe, hd_pos.ne', ↓reduceIte] at hds; exact hds.1)
    refine ⟨hpt5', fun k hk1 hk2 => ?_, fun off ho1 ho2 => ?_⟩
    · rw [hm_out_192 (mbDst + k) (by omega)
        (hdisj_dst_47 (by omega) hd_pos _ (Nat.le_add_right _ _) (by omega))]
      exact hzh5 k hk1 hk2
    · rw [hm_out_192 (mbDst + off) (by omega)
        (hdisj_dst_47 (by omega) hd_pos _ (Nat.le_add_right _ _) (by rw [hmD_eq]; omega))]
      exact hzt5 off ho1 ho2
  · intro hp67
    have hio_al_eq : io_sal = directSlotIo w vB base ibHi qHi nAlloc := by
      dsimp only [io_sal, activeSrcIo]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    have hge2 := hge2_all (by omega) (by omega)
    have hmD := hge2.1; have hp_eq := hge2.2.1; have hibH := hge2.2.2.2.2.1
    have hp_ge : mSrc ≤ pad ∧ mDst ≤ pad := by
      rw [hp_eq, hmSrc_eq, hmD]; exact ⟨le_max_left _ _, le_max_right _ _⟩
    have hnHost_th : whpThreshold c ≤ nHost := by
      dsimp only [nHost]
      by_cases hd0 : nDst = 0
      · rw [ite_eq_left hd0]
        have hs_nz := (hnDst0_all (by omega) hd0).1.ne'
        simp only [EpochCapSafe, hs_nz, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1
      · rw [ite_eq_right hd0]
        have hds := hdst_safe; rw [ite_eq_right (by omega : ph ≠ 0)] at hds
        simp only [EpochCapSafe, hd0, ↓reduceIte] at hds; exact hds.1
    have hpg_meta_unch : ∀ addr, pgHost.OwnsMetaAddr addr → s_mid.mem addr = s.mem addr := by
      intro addr hpm
      have hmbH_192 : base + 192 ≤ mbHost := by
        dsimp only [mbHost]; split_ifs <;> omega
      have hmH_ibH : mbHost + epochMetaWordsWhp c w nHost ≤ ibHi := by
        dsimp only [mbHost, nHost]; rw [hibH]
        by_cases hd0 : nDst = 0
        · simp only [hd0, ↓reduceIte, ← hmSrc_eq]; omega
        · simp only [hd0, ↓reduceIte, ← hmD]; split_ifs <;> omega
      have hend_H := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hnHost_th
      have ha_bounds : mbHost ≤ addr ∧ addr < ibHi ∧
          ¬(mbHost ≤ addr ∧ addr < mbHost + 18) ∧
          ¬(mbHost + 32 ≤ addr ∧ addr < mbHost + offPageDir c w nHost) := by
        unfold PageArenaLayout.OwnsMetaAddr at hpm
        dsimp only [pgHost, hostPageLayout, epochPageArenaLayout] at hpm
        unfold offEpochEnd offPageTail at hend_H
        unfold offPageTail at hpm
        have h32_od : 32 ≤ offPageDir c w nHost := by
          unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
            offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
            offBktHash
          omega
        rcases hpm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          exact ⟨by omega, by omega, by omega, by omega⟩
      refine hm_out_192 addr (by omega) fun hown => ?_
      have hn_io : ¬io_sal.OwnsAddr addr := by
        rw [hio_al_eq]
        simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo, ↓reduceIte]
        omega
      by_cases hd0 : nDst = 0
      · unfold slotOwnsAddr at hown; rw [hcap_s] at hown
        have hst0 := (hnDst0_all (by omega) hd0).2.1
        have hs_pos := (hnDst0_all (by omega) hd0).1
        dsimp only [capSrc, mbSrc] at hown
        simp only [hst0, hs_pos.ne', ↓reduceIte, FastEpochLayout.OwnsFastAddr] at hown
        dsimp only [mbHost, nHost] at ha_bounds
        simp only [hd0, ↓reduceIte] at ha_bounds
        rcases hown with ⟨h1, h2⟩ | ⟨h1, h2⟩ | hio
        · exact ha_bounds.2.2.1 ⟨by omega, h2⟩
        · have h32_b : 32 ≤ offBktMeta c w nSrc := by
            unfold offBktMeta offFpHash offBktHash; omega
          exact ha_bounds.2.2.2 ⟨by omega, h2⟩
        · exact hn_io hio
      · have hdisj := hdisj_dst_47 (by omega) (Nat.pos_of_ne_zero hd0) addr
        have hmbH_eq : mbHost = mbDst ∧ nHost = nDst := by
          dsimp only [mbHost, mbDst, nHost]
          rw [ite_eq_right hd0, ite_eq_left (by omega : ph < 10), ite_eq_right hd0,
            ite_eq_right hd0]
          exact ⟨rfl, rfl⟩
        have ha_lt_mD : addr < mbDst + mDst := by
          unfold PageArenaLayout.OwnsMetaAddr at hpm
          dsimp only [pgHost, hostPageLayout, epochPageArenaLayout] at hpm
          rw [hmbH_eq.1, hmbH_eq.2] at hpm
          rw [hmbH_eq.2, ← hmD] at hend_H
          unfold offEpochEnd offPageTail at hend_H
          unfold offPageTail at hpm
          have h32_od : 32 ≤ offPageDir c w nDst := by
            unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
              offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash
              offBktHash
            omega
          rcases hpm with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
        exact hdisj (hmbH_eq.1 ▸ ha_bounds.1) ha_lt_mD hown
    have hpg_eq : extractPagePair pgHost_fin s_mid.mem = extractPagePair pgHost s.mem := by
      have hu_eq : extractPageUnperm pgHost s_mid.mem = extractPageUnperm pgHost s.mem :=
        extractPageUnperm_congr
          (by dsimp only [pgHost, hostPageLayout, epochPageArenaLayout]; omega)
          hpg_meta_unch
      exact congrArg PageUnpermState.st hu_eq
    refine ⟨hpg_eq, fun hd_pos => ?_⟩
    obtain ⟨hd_cap, hd_abs, _, hsl_d0⟩ := (hsl_67 hp67).2 hd_pos
    have hLmid_dst : L_mid.slotDst = L.slotDst := by
      dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_left hle7]
    rw [hLmid_dst]
    have hpDst_or : pDst = p0 ∨ pDst = p1 := by
      dsimp only [pDst]; rw [ite_eq_left (by omega : ph < 10)]; split_ifs <;> simp
    have hns_d0 : s.mem (mbDst + 1) = 0 := by
      rw [hsl_d0.mem_nSide_eq, hd_abs]
      have hempty : liveDom (fun _ : Fin U => (none : Option (Fin V))) = ∅ := by
        classical ext x; simp [liveDom]
      simp [hempty]
    have hqb_pt :
        quotBitsWhp U L.slotDst.nCap ≤ qHi ∧
        ({ c := c, U := U, V := V, w := w, N := L.slotDst.nCap, metaBase := mbDst, pBase := pDst,
           io := directSlotIo w vB base ibHi qHi nLive } : FastEpochLayout).ParamTable s.mem := by
      have hraw_d := hsl_d0; unfold EpochSlotInv at hraw_d
      rw [ite_eq_right (hd_cap ▸ hd_pos.ne')] at hraw_d
      exact ⟨hraw_d.1.qBits_le, hraw_d.2.1.1⟩
    have hsl_d_fr := hsl_d0.mono_frontier
      ((Nat.le_add_right s.frontier k_grow).trans hs_mid_fr.symm.le)
    clear hph4_inv hph5_inv hsl_le7 hsl_67 hsl_d0
    refine hsl_d_fr.transfer_io
      (hsl_d_fr.io_valid.with_nCap (lt_of_le_of_lt hcard_step.2.2.2.2.2.1 hUw)
        (fun _ _ => by rw [hs_mid_fr]; exact hfr_n'.2 ⟨by omega, by omega⟩)
        (fun _ hsb => absurd rfl hsb) (fun hup => absurd rfl hup))
      rfl
      ⟨fun h0 => absurd (hd_cap ▸ h0) hd_pos.ne', fun _ => hqb_pt.1⟩
      rfl
      ⟨fun h0 => absurd (hd_cap ▸ h0) hd_pos.ne', fun _ =>
        paramTable_direct_withNCap hqb_pt.2 (hm_pDst (by omega)).1 (hm_pDst (by omega)).2⟩
      (fun a h1 h2 => by
        clear hsl_d_fr hqb_pt
        simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo, ↓reduceIte]
        have : pDst + 64 ≤ base + 192 := by
          rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] <;>
            dsimp only [p0, p1, hdrPBase0, hdrPBase1] <;> omega
        have := hibLo_ge.trans hibHi_ge_ibLo.1
        omega)
      (fun a ha => by
        clear hsl_d_fr hqb_pt
        unfold slotOwnsNonPageMeta at ha; rw [hd_cap] at ha
        simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo, ↓reduceIte]
        have hod_d := hod_le_nDst (by omega) hd_pos.ne'
        have hmD_ibH : mbDst + offPageDir c w nDst ≤ ibHi := by
          dsimp only [mbDst]; rw [ite_eq_left (by omega : ph < 10), ite_eq_right hd_pos.ne',
            hibH, ite_eq_right hd_pos.ne', hmD]
          split_ifs <;> omega
        have h32 : 32 ≤ offPageDir c w nDst := by
          unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
            offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta
            offFpHash offBktHash
          omega
        rcases ha with ⟨_, h2⟩ | ⟨_, _, h2⟩
        · rw [ite_eq_right hd_pos.ne'] at h2; omega
        · omega)
      (fun a ha => by
        clear hsl_d_fr hqb_pt
        unfold slotOwnsNonPageMeta at ha; rw [hd_cap] at ha
        have hmbD_192 : base + 192 ≤ mbDst := by
          dsimp only [mbDst]; rw [ite_eq_left (by omega : ph < 10), ite_eq_right hd_pos.ne']
          split_ifs <;> omega
        have hod_d := hod_le_nDst (by omega) hd_pos.ne'
        have ha_b : mbDst ≤ a ∧ a < mbDst + mDst := by
          rw [hmD]
          have h32 : 32 ≤ epochMetaWordsWhp c w nDst :=
            thirtyTwo_le_epochMetaWordsWhp (by
              have hds := hdst_safe; rw [ite_eq_right (by omega : ph ≠ 0)] at hds
              simp only [EpochCapSafe, hd_pos.ne', ↓reduceIte] at hds; exact hds.1)
          rcases ha with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
          · rw [ite_eq_right hd_pos.ne'] at h2; omega
          · omega
        exact hm_out_192 a (by omega) (hdisj_dst_47 (by omega) hd_pos a ha_b.1 ha_b.2))
      (by simp only [SlotIoLayout.StateInv, directSlotIo, ↓reduceIte]
          rw [hns_d0]; exact ⟨Nat.zero_le _, Or.inl trivial⟩)
      (fun p hp => absurd (hns_d0 ▸ hp) (Nat.not_lt_zero _))

private theorem fgStep_le7_grow {c U V w base opTag k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hle7 : s.mem (base + hdrPhase) ≤ 7) :
    let nLive := (Dictionary.dom s_dict).card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qLo := s.mem (base + hdrQLo)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
    let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
      else base + 192 + pad
    let io_s0 := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive
    let io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
    ((io_s0.usePaged = 0 → io_s0.sideBit ≠ 0 →
        io_s0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io_s0.pgL.offDir) ∧
      (io_s0.usePaged ≠ 0 → base + 192 ≤ io_s0.pgL.metaBase) ∧
      base + 192 ≤ io_s0.pgL.itemBase) ∧
    (mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
        io_s0.pgL.itemBase ∧
      (io_s0.usePaged = 0 → io_s0.sideBit ≠ 0 →
        mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
          io_s0.pgL.offDir)) ∧
    EpochSlotInv c U V w s_grow.frontier pSrc mbSrc io_sal 0 false L.slotSrc s_grow.mem := by
  have hsl_le7 := h.sl_le7
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc] at hsl_le7
  have hibLo_ge := hsetup.ibLo_ge
  have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hfr_bounds := hsetup.fr_bounds
  have hmbSrc_info := hsetup.mbSrc_info
  have hlift_grow := @FGSetup.lift_grow_slot c U V w base opTag u v s_dict L s hsetup
  dsimp only at hfr_bounds hmbSrc_info hlift_grow ⊢
  rw [← hk_grow_def] at hfr_bounds
  rw [← hs_prep_def, ← hk_grow_def] at hlift_grow
  clear hs_prep_def hk_grow_def
  set nLive := (Dictionary.dom s_dict).card
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qLo := s.mem (base + hdrQLo)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  set pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
  set mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  obtain ⟨_, _, hsl_s, _⟩ := hsl_le7 hle7
  obtain ⟨_, hpos_s, hm_lo_s, hm_hi_s⟩ := hmbSrc_info (by omega)
  have hpSrc_or : pSrc = base + hdrPBase0 ∨ pSrc = base + hdrPBase1 := by
    dsimp only [pSrc]; split_ifs <;> simp
  set io_s0 := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive
  set io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
  have hup_s0 : io_s0.usePaged = 0 := by
    dsimp only [io_s0, activeSrcIo]; split_ifs <;> first | rfl | omega
  have hio_pos_s :
      (io_s0.usePaged = 0 → io_s0.sideBit ≠ 0 →
        io_s0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io_s0.pgL.offDir) ∧
      (io_s0.usePaged ≠ 0 → base + 192 ≤ io_s0.pgL.metaBase) ∧
      base + 192 ≤ io_s0.pgL.itemBase := by
    dsimp only [io_s0, activeSrcIo]
    by_cases hplt3 : ph < 3
    · rw [ite_eq_left hplt3]; dsimp only [directSlotIo]
      exact ⟨fun _ h => absurd rfl h, fun h => absurd rfl h, hibLo_ge⟩
    · rw [ite_eq_right hplt3]
      by_cases hp3 : ph = 3
      · rw [ite_eq_left hp3]; dsimp only [splitSlotIo]
        exact ⟨fun _ _ => ⟨rfl, hibLo_ge⟩, fun h => absurd rfl h,
          hibLo_ge.trans hibHi_ge_ibLo.1⟩
      · rw [ite_eq_right hp3, ite_eq_left (by omega : ph < 8)]; dsimp only [directSlotIo]
        exact ⟨fun _ h => absurd rfl h, fun h => absurd rfl h,
          hibLo_ge.trans hibHi_ge_ibLo.1⟩
  have hm_ib_s :
      mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
        io_s0.pgL.itemBase ∧
      (io_s0.usePaged = 0 → io_s0.sideBit ≠ 0 →
        mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
          io_s0.pgL.offDir) := by
    dsimp only [io_s0, activeSrcIo]
    by_cases hplt3 : ph < 3
    · rw [ite_eq_left hplt3]; dsimp only [directSlotIo]
      exact ⟨hm_lo_s (by omega), fun _ h => absurd rfl h⟩
    · rw [ite_eq_right hplt3]
      by_cases hp3 : ph = 3
      · rw [ite_eq_left hp3]; dsimp only [splitSlotIo]
        exact ⟨hm_hi_s (by omega), fun _ _ => hm_lo_s (by omega)⟩
      · rw [ite_eq_right hp3, ite_eq_left (by omega : ph < 8)]; dsimp only [directSlotIo]
        exact ⟨hm_hi_s (by omega), fun _ h => absurd rfl h⟩
  have hsl_grow : EpochSlotInv c U V w s_grow.frontier pSrc mbSrc io_sal 0 false
      L.slotSrc s_grow.mem := by
    have hio_eq0 : io_s0.withNCap nAlloc = io_sal :=
      activeSrcIo_withNCap c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive nAlloc
    rw [← hio_eq0]
    refine hlift_grow hsl_s
      (by dsimp only [io_s0, activeSrcIo]; split_ifs <;> rfl)
      hpSrc_or hpos_s hio_pos_s (fun _ hsb => ?_) (fun _ hsb => ?_)
      (fun hup => absurd hup_s0 hup) hm_ib_s
    · dsimp only [io_s0, activeSrcIo] at hsb ⊢
      by_cases hplt3 : ph < 3
      · rw [ite_eq_left hplt3]; exact hfr_bounds.2.2.1 (Or.inl (by omega))
      · rw [ite_eq_right hplt3] at hsb ⊢
        by_cases hp3 : ph = 3
        · rw [ite_eq_left hp3] at hsb; dsimp only [splitSlotIo] at hsb; omega
        · rw [ite_eq_right hp3, ite_eq_left (by omega : ph < 8)]
          exact hfr_bounds.2.2.2.1 ⟨by omega, by omega⟩
    · dsimp only [io_s0, activeSrcIo] at hsb ⊢
      by_cases hplt3 : ph < 3
      · rw [ite_eq_left hplt3] at hsb; exact absurd rfl hsb
      · rw [ite_eq_right hplt3] at hsb ⊢
        by_cases hp3 : ph = 3
        · rw [ite_eq_left hp3]; exact hfr_bounds.2.2.2.1 ⟨by omega, by omega⟩
        · rw [ite_eq_right hp3, ite_eq_left (by omega : ph < 8)] at hsb; exact absurd rfl hsb
  exact ⟨hio_pos_s, hm_ib_s, hsl_grow⟩

private theorem fgStep_le7_ph3 {c U V w base nLive nLive' nAlloc ph stg nSrc nDst pad
    ibLo ibHi qLo qHi pSrc mbSrc fr_mid : ℕ}
    {slSrc slSrc' : SlotLatent c U V} {m0 m_grow m_raw m_mid : ℕ → ℕ}
    (hcard_diff : nLive' ≤ nLive + 1)
    (hph3_inv : ph = 3 →
      m0 (base + hdrSplit) ≤ nLive ∧
      SplitHiQuotBounded (splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive) nLive m0)
    (hibLo_192 : base + 192 ≤ ibLo)
    (hibHi_192 : base + 192 ≤ ibHi)
    (hgrow_sp : m_grow (base + hdrSplit) = m0 (base + hdrSplit))
    (hgrow_ge192 : ∀ addr, base + 192 ≤ addr → m_grow addr = m0 addr)
    (hns_grow : m_grow (mbSrc + 1) = nLive)
    (hpSrc_or : pSrc = base + hdrPBase0 ∨ pSrc = base + hdrPBase1)
    (hpos_s : (slSrc'.nCap = 0 ∧ (mbSrc = base + hdrSmallMeta0 ∨ mbSrc = base + hdrSmallMeta1)) ∨
      (slSrc'.nCap ≠ 0 ∧ base + 192 ≤ mbSrc))
    (hs_raw_sp : m_raw (base + hdrSplit) = m0 (base + hdrSplit))
    (hns_m_eq : m_raw (mbSrc + 1) = nLive')
    (hhi_pres :
      let io_sal := activeSrcIo c w (valBits V) base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
      io_sal.usePaged = 0 → io_sal.sideBit ≠ 0 →
        SplitHiQuotBounded io_sal (m_grow (mbSrc + 1)) m_grow →
        SplitHiQuotBounded io_sal nLive' m_raw)
    (hsl_m3 :
      let m3 := Function.update
        (Function.update (Function.update m_raw (base + hdrLive) nLive')
          (base + hdrPBase0 + 60) nLive')
        (base + hdrPBase1 + 60) nLive'
      EpochSlotInv c U V w fr_mid pSrc mbSrc
        (activeSrcIo c w (valBits V) base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive') 0 false
        slSrc' m3)
    (hs_mid_mem :
      let m3 := Function.update
        (Function.update (Function.update m_raw (base + hdrLive) nLive')
          (base + hdrPBase0 + 60) nLive')
        (base + hdrPBase1 + 60) nLive'
      m_mid =
        if ph = 3 ∧ nLive' < m0 (base + hdrSplit) then
          Function.update m3 (base + hdrSplit) nLive'
        else m3) :
    let _ := slSrc
    EpochSlotInv c U V w fr_mid pSrc mbSrc
      (activeSrcIo c w (valBits V) base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive') 0 false
      slSrc' m_mid ∧
    (ph = 3 →
      m_mid (base + hdrSplit) ≤ nLive' ∧
      m_mid (base + hdrSplit) ≤ m0 (base + hdrSplit) ∧
      nLive' - m_mid (base + hdrSplit) ≤ (nLive - m0 (base + hdrSplit)) + 1 ∧
      SplitHiQuotBounded (splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive') nLive' m_mid) :=
  by
  dsimp only at hhi_pres hsl_m3 hs_mid_mem ⊢
  set sp := m0 (base + hdrSplit)
  set vB := valBits V
  set m3 := Function.update
    (Function.update (Function.update m_raw (base + hdrLive) nLive')
      (base + hdrPBase0 + 60) nLive')
    (base + hdrPBase1 + 60) nLive'
  set io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
  set io_sfin := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive'
  have hm3_sp : m3 (base + hdrSplit) = sp := by
    dsimp only [m3]; unfold hdrPBase0 hdrPBase1 hdrLive hdrSplit
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hs_raw_sp
  by_cases hp3 : ph = 3
  · obtain ⟨_, hhi0⟩ := hph3_inv hp3
    have hio_al_sp : io_sal = splitSlotIo w vB base ibLo qLo ibHi qHi nAlloc := by
      dsimp only [io_sal, activeSrcIo]; rw [ite_eq_right (by omega), ite_eq_left hp3]
    have hio_fin_sp : io_sfin = splitSlotIo w vB base ibLo qLo ibHi qHi nLive' := by
      dsimp only [io_sfin, activeSrcIo]; rw [ite_eq_right (by omega), ite_eq_left hp3]
    have hhi_grow : SplitHiQuotBounded io_sal (m_grow (mbSrc + 1)) m_grow := by
      rw [hio_al_sp, hns_grow]
      intro idx hge hlt
      have hge0 : m0 (base + hdrSplit) ≤ idx := by
        dsimp only [splitSlotIo] at hge; rwa [hgrow_sp] at hge
      have hlt0 := hhi0 idx hge0 hlt
      dsimp only [splitSlotIo] at hlt0 ⊢
      have hq_eq : pairQuotAt ibHi qHi vB w m_grow idx = pairQuotAt ibHi qHi vB w m0 idx := by
        unfold pairQuotAt readBitSlice
        rw [hgrow_ge192 _ (by omega), hgrow_ge192 _ (by omega)]
      rwa [hq_eq]
    have hhi_raw : SplitHiQuotBounded io_sal nLive' m_raw :=
      hhi_pres (by rw [hio_al_sp]; rfl) (by rw [hio_al_sp]; exact Nat.one_ne_zero) hhi_grow
    have hhi_m3 : SplitHiQuotBounded
        (splitSlotIo w vB base ibLo qLo ibHi qHi nLive') nLive' m3 := by
      intro idx hge hlt
      dsimp only [splitSlotIo] at hge ⊢; rw [hm3_sp] at hge
      have hge_raw : m_raw io_sal.pgL.metaBase ≤ idx := by
        rw [hio_al_sp]; dsimp only [splitSlotIo]; rwa [hs_raw_sp]
      have hlt_raw := hhi_raw idx hge_raw hlt
      rw [hio_al_sp] at hlt_raw; dsimp only [splitSlotIo] at hlt_raw
      have hq_eq : pairQuotAt ibHi qHi vB w m3 idx = pairQuotAt ibHi qHi vB w m_raw idx := by
        unfold pairQuotAt readBitSlice; dsimp only [m3]
        unfold hdrPBase0 hdrPBase1 hdrLive
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rwa [hq_eq]
    by_cases hlt_sp : nLive' < sp
    · rw [hs_mid_mem, ite_eq_left ⟨hp3, hlt_sp⟩]
      have hm3_ns : m3 (mbSrc + 1) = nLive' := by
        dsimp only [m3]; unfold hdrPBase0 hdrPBase1 hdrLive
        have hmb_b : base + 48 ≤ mbSrc ∧ mbSrc + 1 ≠ base + 64 + 60 ∧
            mbSrc + 1 ≠ base + 128 + 60 := by
          clear hsl_m3
          rcases hpos_s with ⟨_, hm_e | hm_e⟩ | ⟨_, h192⟩ <;> (try rw [hm_e]) <;>
            (try dsimp only [hdrSmallMeta0, hdrSmallMeta1]) <;>
            exact ⟨by omega, by omega, by omega⟩
        rw [Function.update_of_ne hmb_b.2.2, Function.update_of_ne hmb_b.2.1,
          Function.update_of_ne (by omega)]
        exact hns_m_eq
      have hsl_m3' : EpochSlotInv c U V w fr_mid pSrc mbSrc
        (splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive') 0 false slSrc' m3 := by
        rwa [← hio_fin_sp]
      have hp_ge48 : base + 48 ≤ pSrc := by
        clear hsl_m3 hsl_m3'
        rcases hpSrc_or with hp_e | hp_e <;> rw [hp_e] <;>
          (try dsimp only [hdrPBase0, hdrPBase1]) <;> omega
      have hmb_ge48 : base + 48 ≤ mbSrc := by
        clear hsl_m3 hsl_m3'
        rcases hpos_s with ⟨_, hm_e | hm_e⟩ | ⟨_, h192⟩ <;> (try rw [hm_e]) <;>
          (try dsimp only [hdrSmallMeta0, hdrSmallMeta1]) <;> omega
      have hcl := hsl_m3'.clamp_split_cursor hp_ge48 hmb_ge48
        (by clear hsl_m3 hsl_m3'; omega) hm3_ns (by rwa [hm3_sp])
      rw [hio_fin_sp]
      exact ⟨hcl.1, fun _ => ⟨by rw [Function.update_self],
        by clear hsl_m3 hsl_m3' hcl; rw [Function.update_self]; omega,
        by clear hsl_m3 hsl_m3' hcl; rw [Function.update_self]; omega, hcl.2⟩⟩
    · rw [hs_mid_mem, ite_eq_right (fun h => hlt_sp h.2)]
      exact ⟨hsl_m3, fun _ => ⟨by clear hsl_m3; rw [hm3_sp]; omega, by rw [hm3_sp],
        by clear hsl_m3; rw [hm3_sp]; omega, hhi_m3⟩⟩
  · rw [hs_mid_mem, ite_eq_right (fun h => hp3 h.1)]
    exact ⟨hsl_m3, fun h => absurd h hp3⟩

private theorem fgStep_le7_raw_step {c U V w base opTag v_val k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep s_raw : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hs_raw_def :
      s_raw =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateRawProg ((base, opTag), (u.val, v_val))))
    (hle7 : s.mem (base + hdrPhase) ≤ 7) :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibLo := s.mem (base + hdrItemLo)
    let ibHi := s.mem (base + hdrItemHi)
    let qLo := s.mem (base + hdrQLo)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
    let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
      else base + 192 + pad
    let L_mid := L.applyFG ph opTag u v
    let io_s0 := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive
    let io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
    UserMutateRawPre w ((base, opTag), (u.val, v_val)) s_grow ∧
    s_raw.frontier = s_grow.frontier ∧
    EpochSlotInv c U V w s_raw.frontier pSrc mbSrc io_sal 0 false L_mid.slotSrc s_raw.mem ∧
    toDictState L_mid.slotSrc.s_abs = s_dict' ∧
    (∀ addr, ¬slotOwnsAddr c w mbSrc L.slotSrc.nCap io_sal addr →
      s_raw.mem addr = s_grow.mem addr) ∧
    (io_sal.usePaged = 0 → io_sal.sideBit ≠ 0 →
      s_raw.mem io_sal.pgL.metaBase = s_grow.mem io_sal.pgL.metaBase) ∧
    (io_sal.usePaged = 0 → io_sal.sideBit ≠ 0 →
      SplitHiQuotBounded io_sal (s_grow.mem (mbSrc + 1)) s_grow.mem →
      SplitHiQuotBounded io_sal nLive' s_raw.mem) ∧
    (L_mid.slotSrc.GoodCovers →
      memoryCost (userMutateRawProg ((base, opTag), (u.val, v_val))) s_grow ≤
        epochStepCost c + 2) ∧
    s_grow.mem (mbSrc + 1) = nLive ∧
    ((io_s0.usePaged = 0 → io_s0.sideBit ≠ 0 →
        io_s0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io_s0.pgL.offDir) ∧
      (io_s0.usePaged ≠ 0 → base + 192 ≤ io_s0.pgL.metaBase) ∧
      base + 192 ≤ io_s0.pgL.itemBase) ∧
    (mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
        io_s0.pgL.itemBase ∧
      (io_s0.usePaged = 0 → io_s0.sideBit ≠ 0 →
        mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
          io_s0.pgL.offDir)) := by
  have hb192 := h.base_fr; have hsl_le7 := h.sl_le7
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc] at hsl_le7
  have hgrow_info := fgStep_le7_grow h u v hsetup hs_prep_def hk_grow_def hle7
  have hstg0_le3 := hsetup.stg0_le3
  have hsm_src := hsetup.sm_src
  have hgrow_low0 := hsetup.grow_low
  dsimp only at hgrow_info hsm_src ⊢
  rw [← hs_prep_def] at hgrow_low0
  clear hs_prep_def hk_grow_def
  set nLive := (Dictionary.dom s_dict).card
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set nLive' := (Dictionary.dom s_dict').card
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qLo := s.mem (base + hdrQLo)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hgrow_low : ∀ off < 60, s_grow.mem (base + off) = s.mem (base + off) := hgrow_low0
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pSrc := if stg = 0 then p0 else p1
  set capSrc := if stg = 0 then nSrc else nDst
  set mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  set L_mid := L.applyFG ph opTag u v
  have hs_grow_ph : s_grow.mem (base + hdrPhase) = ph := hgrow_low hdrPhase (by decide)
  have hs_grow_stg : s_grow.mem (base + hdrStage) = stg := hgrow_low hdrStage (by decide)
  obtain ⟨hcap_s, hdict_s, _, _⟩ := hsl_le7 hle7
  set io_s0 := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive
  set io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
  obtain ⟨hio_pos_s, hm_ib_s, hsl_grow⟩ := hgrow_info
  have hcap_n_s : opTag = 1 → L.slotSrc.s_abs u = none → L.slotSrc.nCap ≠ 0 →
      (liveDom L.slotSrc.s_abs).card < L.slotSrc.nCap := fun _ hnone_s hne_c => by
    have hnone_d : s_dict u = none := by rw [← hdict_s]; simp [toDictState, hnone_s]
    have hcap := cap_lt_on_insert_none h hnone_d
    have hcard_eq : (liveDom L.slotSrc.s_abs).card = nLive := by
      rw [← dom_toDictState_card, hdict_s]
    rw [hcard_eq]; rw [hcap_s] at hne_c ⊢
    dsimp only [capSrc] at hne_c ⊢
    by_cases hst0 : stg = 0
    · rw [ite_eq_left hst0] at hne_c ⊢; exact hcap.2.1 hne_c
    · rw [ite_eq_right hst0] at hne_c ⊢
      have hp_nz : ph ≠ 0 := fun hp0 => hst0 (hsetup.stg0_le3 (by omega))
      exact hcap.2.2 hp_nz hne_c
  have hup_al : io_sal.usePaged = 0 := by
    dsimp only [io_sal, activeSrcIo]; split_ifs <;> first | rfl | omega
  have hcap_io_s : opTag = 1 → L.slotSrc.s_abs u = none →
      (liveDom L.slotSrc.s_abs).card < io_sal.pgL.nCap ∧
      (io_sal.usePaged ≠ 0 →
        (extractPagePair io_sal.pgL s_grow.mem).totalItems + 1 ≤ io_sal.pgL.nCap) := by
    intro hop1 hnone_s
    have hnone_d : s_dict u = none := by rw [← hdict_s]; simp [toDictState, hnone_s]
    have hltU := (cap_lt_on_insert_none h hnone_d).1
    have hcard_eq : (liveDom L.slotSrc.s_abs).card = nLive := by
      rw [← dom_toDictState_card, hdict_s]
    have hnc_al : io_sal.pgL.nCap = nAlloc := by
      dsimp only [io_sal, activeSrcIo]; split_ifs <;> rfl
    rw [hnc_al, hcard_eq]
    dsimp only [nAlloc]; rw [ite_eq_left hop1, min_eq_left hltU]
    exact ⟨Nat.lt_succ_self _, fun hup => absurd hup_al hup⟩
  have hmut := singleSlotMutate_raw hsl_grow u v hv_eq hcap_n_s hcap_io_s
  have hum_disp := userMutateRawProg_eval (opTag := opTag) (u_val := u.val) (v_val := v_val)
      s_grow hs_grow_ph hs_grow_stg
  have hs_raw_prog :
      s_raw = (Memory.spec 0).clientState s_grow
        (if opTag = 1 then epochInsertProg ((pSrc, u.val), v_val)
         else epochDeleteProg (pSrc, u.val)) ∧
      memoryCost (userMutateRawProg ((base, opTag), (u.val, v_val))) s_grow =
        2 + memoryCost
          (if opTag = 1 then epochInsertProg ((pSrc, u.val), v_val)
           else epochDeleteProg (pSrc, u.val)) s_grow := by
    rw [hs_raw_def, hum_disp.1, hum_disp.2]; clear hs_raw_def
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, ite_eq_left hop1, ite_eq_right (by omega : ph ≠ 8),
        ite_eq_right (by omega : ph ≠ 9)]
      by_cases h3 : 3 < ph
      · rw [ite_eq_left h3, ite_eq_left (by omega : ph < 8)]; exact ⟨rfl, rfl⟩
      · rw [ite_eq_right h3]
        have hp0_eq : base + hdrPBase0 = pSrc := by
          dsimp only [pSrc, p0]; rw [ite_eq_left (hstg0_le3 (by omega))]
        rw [hp0_eq]; exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hop1, ite_eq_right hop1, ite_eq_right (by omega : ph ≠ 8),
        ite_eq_right (by omega : ph ≠ 9)]
      by_cases h3 : 3 < ph
      · rw [ite_eq_left h3, ite_eq_left (by omega : ph < 8)]; exact ⟨rfl, rfl⟩
      · rw [ite_eq_right h3]
        have hp0_eq : base + hdrPBase0 = pSrc := by
          dsimp only [pSrc, p0]; rw [ite_eq_left (hstg0_le3 (by omega))]
        rw [hp0_eq]; exact ⟨rfl, rfl⟩
  clear hs_raw_def
  have hs_raw_fr : s_raw.frontier = s_grow.frontier := by rw [hs_raw_prog.1]; exact hmut.2.1
  have hslk_zero : (if io_sal.usePaged = 0 ∨
      (extractPageUnperm io_sal.pgL s_grow.mem).cleanPhase = 0 then 0 else 24) = 0 :=
    ite_eq_left (Or.inl hup_al)
  have hLmid_src : L_mid.slotSrc = L.slotSrc.applyFG false opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_left hle7]
  have hsl_raw : EpochSlotInv c U V w s_raw.frontier pSrc mbSrc io_sal 0 false
      L_mid.slotSrc s_raw.mem := by
    have hmut_sl := hmut.2.2.1
    rw [hslk_zero] at hmut_sl
    rw [hLmid_src, hs_raw_prog.1]; exact hmut_sl
  have hdict'_s : toDictState L_mid.slotSrc.s_abs = s_dict' := by
    rw [hLmid_src, hmut.2.2.2.1, hdict_s]
  have hout_raw : ∀ addr, ¬slotOwnsAddr c w mbSrc L.slotSrc.nCap io_sal addr →
      s_raw.mem addr = s_grow.mem addr := by
    rw [hs_raw_prog.1]; exact hmut.2.2.2.2.1
  have hsp_raw : io_sal.usePaged = 0 → io_sal.sideBit ≠ 0 →
      s_raw.mem io_sal.pgL.metaBase = s_grow.mem io_sal.pgL.metaBase := fun hup hsb => by
    rw [hs_raw_prog.1]; exact (hmut.2.2.2.2.2.1 hup hsb).1
  have hns_m_eq : s_raw.mem (mbSrc + 1) = nLive' := by
    rw [hsl_raw.mem_nSide_eq, ← dom_toDictState_card, hdict'_s]
  have hns_grow : s_grow.mem (mbSrc + 1) = nLive := by
    rw [hsl_grow.mem_nSide_eq, ← dom_toDictState_card, hdict_s]
  refine ⟨⟨by dsimp only [s_grow]; omega, ?_⟩, hs_raw_fr, hsl_raw, hdict'_s, hout_raw,
    hsp_raw, fun hup hsb hhi => ?_, fun hgc => ?_, hns_grow, hio_pos_s, hm_ib_s⟩
  · have hpSrc_def : (if stg = 0 then base + hdrPBase0 else base + hdrPBase1) = pSrc := rfl
    dsimp (config := { iota := false, proj := false }) only
    rw [hs_grow_ph, hs_grow_stg, hpSrc_def]
    by_cases hop1 : opTag = 1
    · have hm1 := hmut.1; rw [ite_eq_left hop1] at hm1 ⊢
      rw [ite_eq_right (by omega : ph ≠ 8), ite_eq_right (by omega : ph ≠ 9)]
      by_cases h47 : 4 ≤ ph ∧ ph ≤ 7
      · rw [ite_eq_left h47]; exact hm1
      · rw [ite_eq_right h47]
        have hp0_eq : base + hdrPBase0 = pSrc := by
          dsimp only [pSrc, p0]; rw [ite_eq_left (hstg0_le3 (by omega))]
        rwa [hp0_eq]
    · have hm1 := hmut.1; rw [ite_eq_right hop1] at hm1 ⊢
      rw [ite_eq_right (by omega : ph ≠ 8), ite_eq_right (by omega : ph ≠ 9)]
      by_cases h47 : 4 ≤ ph ∧ ph ≤ 7
      · rw [ite_eq_left h47]; exact hm1
      · rw [ite_eq_right h47]
        have hp0_eq : base + hdrPBase0 = pSrc := by
          dsimp only [pSrc, p0]; rw [ite_eq_left (hstg0_le3 (by omega))]
        rwa [hp0_eq]
  · have hh := (hmut.2.2.2.2.2.1 hup hsb).2 hhi
    rwa [← hs_raw_prog.1, hns_m_eq] at hh
  · rw [hs_raw_prog.2]
    have hc_raw := hmut.2.2.2.2.2.2.2 (hsm_src (by omega)) (by rw [← hLmid_src]; exact hgc)
    omega

private theorem fgStep_le7_raw_lt48 {c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi
    nAlloc nCapSrc : ℕ} {m0 m_grow m_raw : ℕ → ℕ}
    (hle7 : ph ≤ 7)
    (hibLo_192 : base + 192 ≤ ibLo)
    (hibHi_192 : base + 192 ≤ ibHi)
    (hcap_s : nCapSrc = if stg = 0 then nSrc else nDst)
    (hpos_s :
      let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
        else base + 192 + pad
      (nCapSrc = 0 ∧ (mbSrc = base + hdrSmallMeta0 ∨ mbSrc = base + hdrSmallMeta1)) ∨
      (nCapSrc ≠ 0 ∧ base + 192 ≤ mbSrc))
    (hgrow_below : ∀ addr < base, m_grow addr = m0 addr)
    (hgrow_low : ∀ off < 60, m_grow (base + off) = m0 (base + off))
    (hout_raw :
      let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
        else base + 192 + pad
      let io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
      ∀ addr, ¬slotOwnsAddr c w mbSrc nCapSrc io_sal addr → m_raw addr = m_grow addr)
    (hsp_raw :
      let io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
      io_sal.usePaged = 0 → io_sal.sideBit ≠ 0 →
        m_raw io_sal.pgL.metaBase = m_grow io_sal.pgL.metaBase) :
    let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
      else base + 192 + pad
    let io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
    (∀ addr < base + 48, m_raw addr = m0 addr) ∧
    (∀ addr, slotOwnsAddr c w mbSrc nCapSrc io_sal addr →
      base + 48 ≤ addr ∨ addr = base + hdrSplit) ∧
    (∀ addr, slotOwnsAddr c w mbSrc nCapSrc io_sal addr → base + 192 ≤ addr ∨ addr < base + 64) :=
  by
  dsimp only at hpos_s hout_raw hsp_raw ⊢
  set mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  set io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
  have hup_al : io_sal.usePaged = 0 := by
    dsimp only [io_sal, activeSrcIo]; split_ifs <;> first | rfl | omega
  have howns_b := slotOwnsAddr_bounds
    (c := c) (w := w) (base := base) (pad := pad)
    (pBase := if stg = 0 then base + hdrPBase0 else base + hdrPBase1)
    (metaBase := mbSrc) (nCap := nCapSrc) (io := io_sal)
    (fun h0 => by rcases hpos_s with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
    (fun hne => by
      rw [hcap_s] at hne; dsimp only [mbSrc]
      by_cases hst0 : stg = 0
      · rw [ite_eq_left hst0] at hne ⊢; rw [ite_eq_right hne]; exact Or.inl rfl
      · rw [ite_eq_right hst0]; exact Or.inr rfl)
    (fun hup => absurd hup_al hup)
    (fun _ hsb => by
      dsimp only [io_sal, activeSrcIo] at hsb ⊢
      split_ifs at hsb ⊢ <;>
        (first | exact absurd rfl hsb | omega | exact ⟨rfl, hibLo_192, hibHi_192⟩))
    (fun _ hsb => by
      dsimp only [io_sal, activeSrcIo] at hsb ⊢
      split_ifs at hsb ⊢ <;> (first | exact hibLo_192 | exact hibHi_192))
  refine ⟨fun addr hlt48 => ?_,
    fun addr ha => by by_cases h48 : addr < base + 48
                      · exact Or.inr ((howns_b addr ha).2.1 h48).1
                      · exact Or.inl (by omega),
    fun addr ha => by by_cases h192 : base + 192 ≤ addr
                      · exact Or.inl h192
                      · have hb := (howns_b addr ha).2.2
                        exact Or.inr (by omega)⟩
  by_cases hsp_eq : addr = base + hdrSplit
  · subst hsp_eq
    by_cases hp3 : ph = 3
    · have hsp_pres := hsp_raw hup_al
        (by dsimp only [io_sal, activeSrcIo]
            rw [ite_eq_right (by omega), ite_eq_left hp3]; exact Nat.one_ne_zero)
      dsimp only [io_sal, activeSrcIo] at hsp_pres
      rw [ite_eq_right (by omega : ¬(ph < 3)), ite_eq_left hp3] at hsp_pres
      dsimp only [splitSlotIo] at hsp_pres
      rw [hsp_pres]; exact hgrow_low hdrSplit (by decide)
    · rw [hout_raw (base + hdrSplit) (fun ha => by
        obtain ⟨_, h2, _⟩ := howns_b _ ha
        obtain ⟨_, _, hsb⟩ := h2 (by unfold hdrSplit; omega)
        dsimp only [io_sal, activeSrcIo] at hsb
        split_ifs at hsb <;> exact absurd rfl hsb)]
      exact hgrow_low hdrSplit (by decide)
  · rw [hout_raw addr (fun ha => hsp_eq ((howns_b addr ha).2.1 hlt48).1)]
    by_cases hge_b : base ≤ addr
    · have := hgrow_low (addr - base) (by omega)
      rwa [Nat.add_sub_of_le hge_b] at this
    · exact hgrow_below addr (by omega)

private theorem fgStep_le7_raw_aux {c U V w base opTag v_val k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep s_raw s_mid : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hs_raw_def :
      s_raw =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateRawProg ((base, opTag), (u.val, v_val))))
    (hs_mid_def :
      s_mid =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateProg ((base, opTag), (u.val, v_val))))
    (hle7 : s.mem (base + hdrPhase) ≤ 7) :
    FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid := by
  have hUw := h.U_lt; have hb192 := h.base_fr
  have hph3_inv := h.ph3_inv; have hsl_le7 := h.sl_le7
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc] at hsl_le7
  have hraw_step :=
    fgStep_le7_raw_step h u v hv_eq hsetup hs_prep_def hk_grow_def hs_raw_def hle7
  have hcard_step := hsetup.card_step
  have hstg0_le3 := hsetup.stg0_le3
  have hibLo_ge := hsetup.ibLo_ge
  have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hmbSrc_info := hsetup.mbSrc_info
  have hfr_n' := hsetup.fr_n'
  have hgrow_below0 := hsetup.grow_below
  have hgrow_low0 := hsetup.grow_low
  have hgrow_ge1920 := hsetup.grow_ge192
  have hgrow_p_rest0 := hsetup.grow_p_rest
  dsimp only [FGStepOutAux] at hraw_step hcard_step hmbSrc_info hfr_n' ⊢
  rw [← hk_grow_def] at hfr_n'
  rw [← hs_prep_def] at hgrow_below0 hgrow_low0 hgrow_ge1920 hgrow_p_rest0
  set nLive := (Dictionary.dom s_dict).card
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set nLive' := (Dictionary.dom s_dict').card
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qLo := s.mem (base + hdrQLo)
  set qHi := s.mem (base + hdrQHi)
  set sp := s.mem (base + hdrSplit)
  set vB := valBits V
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hgrow_low : ∀ off < 60, s_grow.mem (base + off) = s.mem (base + off) := hgrow_low0
  have hgrow_ge192 : ∀ addr, base + 192 ≤ addr → s_grow.mem addr = s.mem addr := hgrow_ge1920
  have hgrow_p_rest : ∀ pB, (pB = base + hdrPBase0 ∨ pB = base + hdrPBase1) →
      ∀ a, pB ≤ a → a < pB + 64 → a ≠ pB + 60 → s_grow.mem a = s.mem a := hgrow_p_rest0
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pSrc := if stg = 0 then p0 else p1
  set pDst := if ph < 10 then (if stg = 0 then p1 else p0) else p0
  set capSrc := if stg = 0 then nSrc else nDst
  set mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  set L_mid := L.applyFG ph opTag u v
  have hs_mid_eq : s_mid = (Memory.spec 0).clientState s_raw (syncLiveCountsProg base) := by
    rw [hs_mid_def, hs_raw_def]; exact (userMutateProg_eval base opTag u.val v_val s_grow).1
  have hmc_um_eq : memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow =
      memoryCost (userMutateRawProg ((base, opTag), (u.val, v_val))) s_grow +
        memoryCost (syncLiveCountsProg base) s_raw := by
    rw [hs_raw_def]; exact (userMutateProg_eval base opTag u.val v_val s_grow).2
  have hsync_pre_eq : SyncLivePre w base
      ((Memory.spec 0).clientState s_grow (userMutateRawProg ((base, opTag), (u.val, v_val)))) ↔
      SyncLivePre w base s_raw := by rw [hs_raw_def]
  clear hs_mid_def hs_raw_def
  obtain ⟨hcap_s, _, _, hlen_s⟩ := hsl_le7 hle7
  obtain ⟨_, hpos_s, _, _⟩ := hmbSrc_info (by omega)
  have hpSrc_or : pSrc = p0 ∨ pSrc = p1 := by dsimp only [pSrc]; split_ifs <;> simp
  set io_s0 := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive
  set io_sal := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
  set io_sfin := activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive'
  obtain ⟨hraw_pre, hs_raw_fr, hsl_raw, hdict'_s, hout_raw, hsp_raw,
    hhi_pres, hmc_raw, hns_grow, hio_pos_s, hm_ib_s⟩ := hraw_step
  obtain ⟨hs_raw_lt48, _, howns_ge192_or⟩ := fgStep_le7_raw_lt48 hle7 hibLo_ge
    (hibLo_ge.trans hibHi_ge_ibLo.1) hcap_s hpos_s hgrow_below0 hgrow_low hout_raw hsp_raw
  have hup_al : io_sal.usePaged = 0 := by
    dsimp only [io_sal, activeSrcIo]; split_ifs <;> first | rfl | omega
  have hLmid_src : L_mid.slotSrc = L.slotSrc.applyFG false opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_left hle7]
  have hsync_ev := syncLiveCountsProg_eval (base := base) s_raw
  have hs_raw_ph : s_raw.mem (base + hdrPhase) = ph :=
    hs_raw_lt48 (base + hdrPhase) (by unfold hdrPhase; omega)
  have hs_raw_stg : s_raw.mem (base + hdrStage) = stg :=
    hs_raw_lt48 (base + hdrStage) (by unfold hdrStage; omega)
  have hns_raw_eq : (Memory.spec 0).clientResult s_raw (epochReadNSideProg pSrc) = nLive' := by
    rw [hsl_raw.readNSide_eq, ← dom_toDictState_card, hdict'_s]
  have hnL'_sync :
      (if s_raw.mem (base + hdrPhase) = 8 then
         (Memory.spec 0).clientResult s_raw
           (epochReadNSideProg (if s_raw.mem (base + hdrStage) = 0 then p0 else p1)) +
         (Memory.spec 0).clientResult s_raw
           (epochReadNSideProg (if s_raw.mem (base + hdrStage) = 0 then p1 else p0))
       else if s_raw.mem (base + hdrPhase) = 9 then
         (Memory.spec 0).clientResult s_raw
           (epochReadNSideProg (if s_raw.mem (base + hdrStage) = 0 then p1 else p0))
       else if 4 ≤ s_raw.mem (base + hdrPhase) ∧ s_raw.mem (base + hdrPhase) ≤ 7 then
         (Memory.spec 0).clientResult s_raw
           (epochReadNSideProg (if s_raw.mem (base + hdrStage) = 0 then p0 else p1))
       else (Memory.spec 0).clientResult s_raw (epochReadNSideProg p0)) = nLive' := by
    rw [hs_raw_ph, hs_raw_stg, ite_eq_right (by omega : ph ≠ 8),
      ite_eq_right (by omega : ph ≠ 9)]
    by_cases h47 : 4 ≤ ph ∧ ph ≤ 7
    · rw [ite_eq_left h47]; exact hns_raw_eq
    · rw [ite_eq_right h47]
      have hp0_eq : p0 = pSrc := by dsimp only [pSrc]; rw [ite_eq_left (hstg0_le3 (by omega))]
      rw [hp0_eq]; exact hns_raw_eq
  set m3 := Function.update
    (Function.update (Function.update s_raw.mem (base + hdrLive) nLive') (p0 + 60) nLive')
    (p1 + 60) nLive'
  have hs_mid_fr : s_mid.frontier = s_grow.frontier := by
    rw [hs_mid_eq, hsync_ev.1]; exact hs_raw_fr
  have hns_m_eq : s_raw.mem (mbSrc + 1) = nLive' := by
    rw [hsl_raw.mem_nSide_eq, ← dom_toDictState_card, hdict'_s]
  have hsl_m3 : EpochSlotInv c U V w s_mid.frontier pSrc mbSrc io_sfin 0 false
      L_mid.slotSrc m3 := by
    have hio_eq : io_sal.withNCap nLive' = io_sfin :=
      activeSrcIo_withNCap c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc nLive'
    rw [← hio_eq]
    refine EpochSlotInv.lift_sync (base := base)
      (by rw [hs_mid_fr]; dsimp only [s_grow]; rw [← hs_raw_fr]; exact hsl_raw) le_rfl
      (lt_of_le_of_lt hcard_step.2.2.2.2.2.1 hUw) hpSrc_or
      (by rw [hLmid_src, SlotLatent.applyFG_nCap]; exact hpos_s)
      (by dsimp only [io_sal, io_s0] at hio_pos_s ⊢
          unfold activeSrcIo at hio_pos_s ⊢; split_ifs at hio_pos_s ⊢ <;> exact hio_pos_s)
      (fun _ hsb => by
        rw [hs_mid_fr]
        dsimp only [io_sal, activeSrcIo] at hsb ⊢
        by_cases hplt3 : ph < 3
        · rw [ite_eq_left hplt3]; exact hfr_n'.1 (Or.inl (by omega))
        · rw [ite_eq_right hplt3] at hsb ⊢
          by_cases hp3 : ph = 3
          · rw [ite_eq_left hp3] at hsb; dsimp only [splitSlotIo] at hsb; omega
          · rw [ite_eq_right hp3, ite_eq_left (by omega : ph < 8)]
            exact hfr_n'.2 ⟨by omega, by omega⟩)
      (fun _ hsb => by
        rw [hs_mid_fr]
        dsimp only [io_sal, activeSrcIo] at hsb ⊢
        by_cases hplt3 : ph < 3
        · rw [ite_eq_left hplt3] at hsb; exact absurd rfl hsb
        · rw [ite_eq_right hplt3] at hsb ⊢
          by_cases hp3 : ph = 3
          · rw [ite_eq_left hp3]; exact hfr_n'.2 ⟨by omega, by omega⟩
          · rw [ite_eq_right hp3, ite_eq_left (by omega : ph < 8)] at hsb; exact absurd rfl hsb)
      (fun hup => absurd hup_al hup)
      (by rw [hLmid_src, SlotLatent.applyFG_nCap]
          dsimp only [io_sal, io_s0] at hm_ib_s ⊢
          unfold activeSrcIo at hm_ib_s ⊢; split_ifs at hm_ib_s ⊢ <;> exact hm_ib_s)
      hns_m_eq.le (fun hup => absurd hup_al hup)
      (by dsimp only [m3]
          rcases hpSrc_or with hp_e | hp_e <;> rw [hp_e] <;>
            dsimp only [p0, p1, hdrPBase0, hdrPBase1]
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_self])
      (fun a ha1 ha2 hne => by
        dsimp only [m3]
        rcases hpSrc_or with hp_e | hp_e <;> rw [hp_e] at ha1 ha2 hne <;>
          dsimp only [p0, p1, hdrPBase0, hdrPBase1, hdrLive] at ha1 ha2 hne ⊢ <;>
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)])
      (fun a ha => by
        dsimp only [m3]
        dsimp only [p0, p1, hdrPBase0, hdrPBase1, hdrLive, hdrSplit] at ha ⊢
        rw [Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega),
          Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega),
          Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega)])
  have hm3_sp : m3 (base + hdrSplit) = sp := by
    dsimp only [m3]; unfold p0 p1 hdrPBase0 hdrPBase1 hdrLive hdrSplit
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hs_raw_lt48 (base + hdrSplit) (by unfold hdrSplit; omega)
  have hs_mid_mem : s_mid.mem =
      if ph = 3 ∧ nLive' < sp then Function.update m3 (base + hdrSplit) nLive' else m3 := by
    dsimp only [p0, p1] at hnL'_sync
    rw [hs_mid_eq, hsync_ev.1]; dsimp only
    rw [hnL'_sync, hs_raw_ph]
    have hm3_sp' : Function.update
        (Function.update (Function.update s_raw.mem (base + hdrLive) nLive')
          (base + hdrPBase0 + 60) nLive')
        (base + hdrPBase1 + 60) nLive' (base + hdrSplit) = sp := hm3_sp
    rw [hm3_sp']
    change (if (ph = 3 ∨ ph = 10) ∧ nLive' < sp then Function.update m3 (base + hdrSplit) nLive'
      else m3) = _
    by_cases hp3 : ph = 3
    · simp only [hp3, true_or, true_and]
    · have hn10 : ph ≠ 10 := by omega
      simp only [hp3, hn10, or_self, false_and, ↓reduceIte]
  have hm_out_192 : ∀ addr, base + 192 ≤ addr →
      ¬slotOwnsAddr c w mbSrc L.slotSrc.nCap io_sal addr → s_mid.mem addr = s.mem addr := by
    intro addr h192 hnot
    rw [hs_mid_mem]
    have hm3_a : m3 addr = s.mem addr := by
      dsimp only [m3]; unfold p0 p1 hdrPBase0 hdrPBase1 hdrLive
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hout_raw addr hnot, hgrow_ge192 addr h192]
    split_ifs
    · rw [Function.update_of_ne (by unfold hdrSplit; omega)]; exact hm3_a
    · exact hm3_a
  have hm_pDst : 4 ≤ ph →
      s_mid.mem (pDst + 60) = nLive' ∧
      ∀ k < 63, k ≠ 60 → s_mid.mem (pDst + k) = s.mem (pDst + k) := fun _ => by
    have hpDst_or : pDst = p0 ∨ pDst = p1 := by
      dsimp only [pDst]; rw [ite_eq_left (by omega : ph < 10)]; split_ifs <;> simp
    rw [hs_mid_mem, ite_eq_right (by omega : ¬(ph = 3 ∧ nLive' < sp))]
    dsimp only [m3]
    refine ⟨?_, fun k hk hk60 => ?_⟩
    · rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] <;>
        dsimp only [p0, p1, hdrPBase0, hdrPBase1]
      · rw [Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_self]
    · rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] <;>
        dsimp only [p0, p1, hdrPBase0, hdrPBase1, hdrLive] at hk60 hk ⊢
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          hout_raw _ (fun ho => by rcases howns_ge192_or _ ho with h1 | h2 <;> omega)]
        exact hgrow_p_rest (base + 64) (Or.inl rfl) _ (by omega) (by omega) (by omega)
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega),
          hout_raw _ (fun ho => by rcases howns_ge192_or _ ho with h1 | h2 <;> omega)]
        exact hgrow_p_rest (base + 128) (Or.inr rfl) _ (by omega) (by omega) (by omega)
  have hph47 :=
    fgStep_le7_ph47 h u v hsetup hs_prep_def hk_grow_def hle7 hs_mid_fr hm_out_192 hm_pDst
  clear hs_prep_def hk_grow_def
  have hsl_and_sp := fgStep_le7_ph3 (slSrc := L.slotSrc) hcard_step.2.2.2.2.1 hph3_inv hibLo_ge
    (hibLo_ge.trans hibHi_ge_ibLo.1) (hgrow_low hdrSplit (by decide)) hgrow_ge192 hns_grow
    hpSrc_or (by rw [hLmid_src, SlotLatent.applyFG_nCap]; exact hpos_s)
    (hs_raw_lt48 (base + hdrSplit) (by unfold hdrSplit; omega)) hns_m_eq hhi_pres
    hsl_m3 hs_mid_mem
  refine ⟨⟨hraw_pre,
      hsync_pre_eq.mpr ⟨by rw [hs_raw_fr]; omega, ?_⟩⟩,
    hs_mid_fr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h9 => absurd h9 (by omega),
    fun _ => ?_, fun h8 => absurd h8 (by omega), fun h9 => absurd h9 (by omega),
    fun hgc_s _ _ => ?_⟩
  · have hpSrc_def : (if stg = 0 then base + hdrPBase0 else base + hdrPBase1) = pSrc := rfl
    dsimp (config := { iota := false, proj := false }) only
    rw [hs_raw_ph, hs_raw_stg, hpSrc_def, ite_eq_right (by omega : ph ≠ 8),
      ite_eq_right (by omega : ph ≠ 9)]
    by_cases h47 : 4 ≤ ph ∧ ph ≤ 7
    · rw [ite_eq_left h47]; exact hsl_raw.epochProgPre
    · rw [ite_eq_right h47]
      have hp0_eq : base + hdrPBase0 = pSrc := by
        dsimp only [pSrc, p0]; rw [ite_eq_left (hstg0_le3 (by omega))]
      rw [hp0_eq]; exact hsl_raw.epochProgPre
  · rw [hs_mid_mem]
    have hm3_l : m3 (base + hdrLive) = nLive' := by
      dsimp only [m3]; unfold p0 p1 hdrPBase0 hdrPBase1 hdrLive
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]
    split_ifs
    · rw [Function.update_of_ne (by unfold hdrLive hdrSplit; omega)]; exact hm3_l
    · exact hm3_l
  · intro addr ha48 hne_l hne_s
    rw [hs_mid_mem]
    have hm3_a : m3 addr = s.mem addr := by
      dsimp only [m3]; unfold p0 p1 hdrPBase0 hdrPBase1
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne hne_l]
      exact hs_raw_lt48 addr ha48
    split_ifs
    · rw [Function.update_of_ne hne_s]; exact hm3_a
    · exact hm3_a
  · intro hn3 _
    rw [hs_mid_mem, ite_eq_right (fun h => hn3 h.1), hm3_sp]
  · rintro (hp3 | hp10)
    · exact hsl_and_sp.2 hp3
    · omega
  · exact hph47.1
  · exact hph47.2.1
  · exact hph47.2.2
  · refine ⟨by rw [hLmid_src, SlotLatent.applyFG_nCap]; exact hcap_s,
      hdict'_s, hsl_and_sp.1, fun hp_pos hc_pos => ?_⟩
    have hl0 := hlen_s hp_pos hc_pos
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl0
    rw [hLmid_src]; unfold SlotLatent.applyFG
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
      omega
    · rw [ite_eq_right hop1]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
      omega
  · rw [hmc_um_eq]
    have hc_raw := hmc_raw (hgc_s hle7)
    have hc_sync := hsync_ev.2
    omega

/-- Auxiliary opaque-state version of `fgStep_le7`. -/
theorem fgStep_le7_aux {c U V w base opTag v_val k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep s_mid : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hs_mid_def :
      s_mid =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateProg ((base, opTag), (u.val, v_val))))
    (hle7 : s.mem (base + hdrPhase) ≤ 7) :
    FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid :=
  fgStep_le7_raw_aux h u v hv_eq hsetup hs_prep_def hk_grow_def rfl hs_mid_def hle7

/-- Proves `FGStepOut` for foreground mutations in phases `ph ≤ 7`. -/
theorem fgStep_le7 {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hle7 : s.mem (base + hdrPhase) ≤ 7) :
    FGStepOut c U V w base opTag v_val u v s_dict L s :=
  fgStep_le7_aux h u v hv_eq hsetup rfl rfl rfl hle7

/-- Preserves `pDst_pre` (`2 ≤ ph ≤ 5`) and `hdrSmallMeta1` (`ph ∈ {6, 7}, nDst = 0`) across
foreground mutations in `ph ≤ 7`. -/
theorem fgStep_le7_extra {c U V w base opTag v_val k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep s_mid : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hs_mid_def :
      s_mid =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateProg ((base, opTag), (u.val, v_val))))
    (hle7 : s.mem (base + hdrPhase) ≤ 7) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nDst := s.mem (base + hdrNDst)
    let mbDst := dualMbDst base s.mem
    let pDst := dualPDst base s.mem
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    ((2 ≤ ph ∧ ph ≤ 5) → (ph = 5 ∨ stg = 0) → 0 < nDst →
      ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
         io := directSlotIo w (valBits V) base ibHi qHi nLive' } : FastEpochLayout).ParamTable
        (dualPh5MaskMem V w base pDst ibHi qHi nLive' s_mid.mem)) ∧
    ((ph = 6 ∨ ph = 7) → nDst = 0 →
      s_mid.mem (base + hdrSmallMeta1) = 0 ∧ s_mid.mem (base + hdrSmallMeta1 + 1) = 0) := by
  dsimp only
  have hpDst_pre := h.pDst_pre; have hsl_le7 := h.sl_le7; have hsl_67 := h.sl_67
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc] at hsl_le7
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  set s_raw :=
    (Memory.spec 0).clientState s_grow (userMutateRawProg ((base, opTag), (u.val, v_val)))
  have hraw_step :=
    fgStep_le7_raw_step h u v hv_eq hsetup hs_prep_def hk_grow_def rfl hle7
  have hgrow_low := hsetup.grow_low; have hgrow_p_rest := hsetup.grow_p_rest
  have hgrow_below := hsetup.grow_below
  dsimp only at hgrow_low hgrow_p_rest hgrow_below
  rw [← hs_prep_def] at hgrow_low hgrow_p_rest hgrow_below
  have hmbSrc_info := hsetup.mbSrc_info; dsimp only at hmbSrc_info
  obtain ⟨hcap_s, _, _, _⟩ := hsl_le7 hle7
  obtain ⟨_, hpos_s, _, _⟩ := hmbSrc_info (by omega)
  obtain ⟨_, _, _, _, hout_raw, hsp_raw, _, _, _, _, _⟩ := hraw_step
  obtain ⟨hs_raw_lt48, _, howns_ge192_or⟩ := fgStep_le7_raw_lt48 hle7 hsetup.ibLo_ge
    (hsetup.ibLo_ge.trans hsetup.ibHi_ge_ibLo.1) hcap_s hpos_s hgrow_below hgrow_low
    hout_raw hsp_raw
  have hs_mid_eq : s_mid = (Memory.spec 0).clientState s_raw (syncLiveCountsProg base) := by
    rw [hs_mid_def]; exact (userMutateProg_eval base opTag u.val v_val s_grow).1
  have hsync_ev := syncLiveCountsProg_eval (base := base) s_raw
  set nL_sync :=
    if s_raw.mem (base + hdrPhase) = 8 then
      (Memory.spec 0).clientResult s_raw
        (epochReadNSideProg
          (if s_raw.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1)) +
      (Memory.spec 0).clientResult s_raw
        (epochReadNSideProg
          (if s_raw.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0))
    else if s_raw.mem (base + hdrPhase) = 9 then
      (Memory.spec 0).clientResult s_raw
        (epochReadNSideProg
          (if s_raw.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0))
    else if 4 ≤ s_raw.mem (base + hdrPhase) ∧ s_raw.mem (base + hdrPhase) ≤ 7 then
      (Memory.spec 0).clientResult s_raw
        (epochReadNSideProg
          (if s_raw.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1))
    else (Memory.spec 0).clientResult s_raw (epochReadNSideProg (base + hdrPBase0))
  set m3 := Function.update
    (Function.update (Function.update s_raw.mem (base + hdrLive) nL_sync)
      (base + hdrPBase0 + 60) nL_sync)
    (base + hdrPBase1 + 60) nL_sync
  have hs_mid_mem : s_mid.mem =
      if (s_raw.mem (base + hdrPhase) = 3 ∨ s_raw.mem (base + hdrPhase) = 10) ∧
          nL_sync < m3 (base + hdrSplit) then
        Function.update m3 (base + hdrSplit) nL_sync
      else m3 := by
    rw [hs_mid_eq, hsync_ev.1]
  have hs_mid_unch : ∀ addr, addr ≠ base + hdrSplit → addr ≠ base + hdrLive →
      addr ≠ base + hdrPBase0 + 60 → addr ≠ base + hdrPBase1 + 60 →
      s_mid.mem addr = s_raw.mem addr := fun addr hsp hlv hp0 hp1 => by
    rw [hs_mid_mem]
    by_cases hc : (s_raw.mem (base + hdrPhase) = 3 ∨ s_raw.mem (base + hdrPhase) = 10) ∧
        nL_sync < m3 (base + hdrSplit)
    · rw [ite_eq_left hc, Function.update_of_ne hsp]
      dsimp only [m3]
      rw [Function.update_of_ne hp1, Function.update_of_ne hp0, Function.update_of_ne hlv]
    · rw [ite_eq_right hc]
      dsimp only [m3]
      rw [Function.update_of_ne hp1, Function.update_of_ne hp0, Function.update_of_ne hlv]
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nDst := s.mem (base + hdrNDst)
  refine ⟨fun hp25 h5_st hd_pos => ?_, fun hp67 hd0 => ?_⟩
  · have hpDst_or : dualPDst base s.mem = base + hdrPBase0 ∨
        dualPDst base s.mem = base + hdrPBase1 := by
      unfold dualPDst; rw [ite_eq_left (by change ph < 10; omega)]; split_ifs <;> simp
    refine paramTable_ph5Mask_congr (hpDst_pre hp25 h5_st hd_pos) fun k hk hk_out => ?_
    have hk60 : k ≠ 60 := by omega
    rcases hpDst_or with hp_e | hp_e <;> rw [hp_e]
    · rw [hs_mid_unch _
        (by dsimp only [hdrPBase0, hdrSplit]; omega)
        (by dsimp only [hdrPBase0, hdrLive]; omega)
        (by dsimp only [hdrPBase0]; omega)
        (by dsimp only [hdrPBase0, hdrPBase1]; omega),
        hout_raw _ (fun ho => by
          rcases howns_ge192_or _ ho with h1 | h1 <;> dsimp only [hdrPBase0] at h1 <;> omega)]
      exact hgrow_p_rest (base + 64) (Or.inl rfl) _
        (by dsimp only [hdrPBase0]; omega) (by dsimp only [hdrPBase0]; omega)
        (by dsimp only [hdrPBase0]; omega)
    · rw [hs_mid_unch _
        (by dsimp only [hdrPBase1, hdrSplit]; omega)
        (by dsimp only [hdrPBase1, hdrLive]; omega)
        (by dsimp only [hdrPBase0, hdrPBase1]; omega)
        (by dsimp only [hdrPBase1]; omega),
        hout_raw _ (fun ho => by
          rcases howns_ge192_or _ ho with h1 | h1 <;> dsimp only [hdrPBase1] at h1 <;> omega)]
      exact hgrow_p_rest (base + 128) (Or.inr rfl) _
        (by dsimp only [hdrPBase1]; omega) (by dsimp only [hdrPBase1]; omega)
        (by dsimp only [hdrPBase1]; omega)
  · obtain ⟨hsm0, hsm1⟩ := (hsl_67 hp67).1 hd0
    have hsm_unch : ∀ off, (off = hdrSmallMeta1 ∨ off = hdrSmallMeta1 + 1) →
        s_mid.mem (base + off) = s.mem (base + off) := fun off hoff => by
      rw [hs_mid_unch _
        (by unfold hdrSmallMeta1 hdrSplit at *; rcases hoff with rfl | rfl <;> omega)
        (by unfold hdrSmallMeta1 hdrLive at *; rcases hoff with rfl | rfl <;> omega)
        (by unfold hdrSmallMeta1 hdrPBase0 at *; rcases hoff with rfl | rfl <;> omega)
        (by unfold hdrSmallMeta1 hdrPBase1 at *; rcases hoff with rfl | rfl <;> omega)]
      have hnot : ¬slotOwnsAddr c w
          (if stg = 0 then if s.mem (base + hdrNSrc) = 0 then base + hdrSmallMeta0 else base + 192
           else base + 192 + s.mem (base + hdrPad)) L.slotSrc.nCap
          (activeSrcIo c w (valBits V) base stg ph (s.mem (base + hdrNSrc)) nDst
            (s.mem (base + hdrPad)) (s.mem (base + hdrItemLo)) (s.mem (base + hdrQLo))
            (s.mem (base + hdrItemHi)) (s.mem (base + hdrQHi))
            (if opTag = 1 then min ((Dictionary.dom s_dict).card + 1) U
             else (Dictionary.dom s_dict).card)) (base + off) := by
        obtain ⟨hs_pos, hst0, _⟩ := hsetup.nDst0_sched (by rcases hp67 with h | h <;> omega) hd0
        have hnc_ne : L.slotSrc.nCap ≠ 0 := by
          rw [hcap_s, ite_eq_left hst0]; omega
        unfold slotOwnsAddr; rw [ite_eq_right hnc_ne]
        dsimp only [FastEpochLayout.OwnsFastAddr, activeSrcIo]
        rw [ite_eq_left hst0, ite_eq_right hs_pos.ne',
          ite_eq_right (by rcases hp67 with h | h <;> omega),
          ite_eq_right (by rcases hp67 with h | h <;> omega),
          ite_eq_left (by rcases hp67 with h | h <;> omega)]
        simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo, ↓reduceIte]
        have hibH : base + 192 ≤ s.mem (base + hdrItemHi) :=
          hsetup.ibLo_ge.trans hsetup.ibHi_ge_ibLo.1
        unfold hdrSmallMeta1 at hoff
        rcases hoff with rfl | rfl <;> omega
      rw [hout_raw _ hnot]
      exact hgrow_low off
        (by unfold hdrSmallMeta1 at hoff; rcases hoff with rfl | rfl <;> omega)
    exact ⟨(hsm_unch hdrSmallMeta1 (Or.inl rfl)).trans hsm0,
      (hsm_unch (hdrSmallMeta1 + 1) (Or.inr rfl)).trans hsm1⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

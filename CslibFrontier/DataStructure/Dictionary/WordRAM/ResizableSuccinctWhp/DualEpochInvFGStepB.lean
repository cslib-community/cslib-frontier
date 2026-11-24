/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvFGStepA

/-!
# Foreground Mutation Regimes `ph = 8` and `9 ≤ ph` (`DualEpochInvFGStepB`)

Proves foreground mutation preservation for Phase `8` (`fgStep_eq8`) and Phases `9..11`
(`fgStep_ge9`) of [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `fgStep_eq8`, `fgStep_ge9`
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

private theorem extractPageUnperm_host_congr {c w nHost mbHost ibHi qHi vB nc₁ nc₂ base : ℕ}
    {m₁ m₂ : ℕ → ℕ} (hw : 11 ≤ w) (hmb : base + 192 ≤ mbHost)
    (heq : ∀ addr, base + 192 ≤ addr → m₁ addr = m₂ addr) :
    extractPageUnperm (hostPageLayout c w nHost mbHost ibHi qHi vB nc₁) m₁ =
      extractPageUnperm (hostPageLayout c w nHost mbHost ibHi qHi vB nc₂) m₂ := by
  have hc : extractPageUnperm (hostPageLayout c w nHost mbHost ibHi qHi vB nc₁) m₁ =
      extractPageUnperm (hostPageLayout c w nHost mbHost ibHi qHi vB nc₁) m₂ :=
    extractPageUnperm_congr (show 0 < w by omega) fun addr ha => by
      have hmb_eq : (hostPageLayout c w nHost mbHost ibHi qHi vB nc₁).metaBase = mbHost := rfl
      have hge : mbHost ≤ addr := by
        rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [hmb_eq] at h1
        · exact le_trans (by omega) h1
        · exact le_trans (Nat.le_add_right _ _) h1
        · exact le_trans (Nat.le_add_right _ _) h1
      exact heq addr (hmb.trans hge)
  exact hc

private theorem virtLen_false_zero_of_cleanPhase {L : PageArenaLayout} {slack : ℕ} {m : ℕ → ℕ}
    (hinv : (extractPageUnperm L m).InvWithSlack slack)
    (hcp : 0 < (extractPageUnperm L m).cleanPhase) :
    (extractPagePair L m).virtLen false = 0 := by
  obtain ⟨hf0, ht0⟩ := hinv.src_empty hcp
  change (extractPagePair L m).fullPages false = 0 at hf0
  change (extractPagePair L m).tailCount false = 0 at ht0
  simp [PagePairState.virtLen, hf0, ht0]

private theorem fgStep_eq8_grow {c U V w base opTag k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (h8 : s.mem (base + hdrPhase) = 8) :
    let nLive := (Dictionary.dom s_dict).card
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
    let pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
    let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
      else base + 192 + pad
    let mbDst := if nDst = 0 then base + hdrSmallMeta1
      else if stg = 0 then base + 192 + pad else base + 192
    let nHost := if nDst = 0 then nSrc else nDst
    let mbHost := if nDst = 0 then base + 192
      else if stg = 0 then base + 192 + pad else base + 192
    let pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
    EpochSlotInv c U V w s_grow.frontier pSrc mbSrc (pagedSlotIo 0 pgHost_al) 0 true
      L.slotSrc s_grow.mem ∧
    EpochSlotInv c U V w s_grow.frontier pDst mbDst (pagedSlotIo 1 pgHost_al) 0 false
      L.slotDst s_grow.mem ∧
    (extractPageUnperm pgHost_al s_grow.mem).cleanPhase = 0 ∧
    (pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc) ∧
    (pDst + 64 ≤ mbSrc ∨
      mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ pDst) ∧
    (pSrc + 64 ≤ mbDst ∨
      mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ pSrc) ∧
    (mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ mbDst ∨
      mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ mbSrc) := by
  have hw11 := h.hw11; have hmSrc_eq := h.mSrc_eq; have hsl_8 := h.sl_8
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost] at hsl_8
  have hibLo_ge := hsetup.ibLo_ge; have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hfr_bounds := hsetup.fr_bounds
  have hod_le_nSrc := hsetup.od_le_nSrc; have hod_le_nDst := hsetup.od_le_nDst
  have hpgHost_cap := hsetup.pgHost_cap
  have hmbSrc_info := hsetup.mbSrc_info; have hmbDst_info := hsetup.mbDst_info
  have hge2_all := hsetup.ge2_sched; have hnDst0_all := hsetup.nDst0_sched
  have hgrow_ge1920 := hsetup.grow_ge192
  have hlift_grow := @FGSetup.lift_grow_slot c U V w base opTag u v s_dict L s hsetup
  dsimp only at hfr_bounds hpgHost_cap hmbSrc_info hmbDst_info hlift_grow ⊢
  rw [← hk_grow_def] at hfr_bounds
  rw [← hs_prep_def, ← hk_grow_def] at hlift_grow
  rw [← hs_prep_def] at hgrow_ge1920
  clear hs_prep_def hk_grow_def
  set nLive := (Dictionary.dom s_dict).card
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hgrow_ge192 : ∀ addr, base + 192 ≤ addr → s_grow.mem addr = s.mem addr := hgrow_ge1920
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pSrc := if stg = 0 then p0 else p1
  set pDst := if stg = 0 then p1 else p0
  set nHost := if nDst = 0 then nSrc else nDst
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
  set pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
  set capSrc := if stg = 0 then nSrc else nDst
  set mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  set mbDst := if nDst = 0 then base + hdrSmallMeta1
    else if stg = 0 then base + 192 + pad else base + 192
  obtain ⟨hcap_s, hcap_d, _, _, hcp0, hsl_s, hsl_d, _, _⟩ := hsl_8 h8
  rw [ite_eq_left (by omega : ph < 10), ite_eq_left (by omega : ph < 10)] at hsl_d
  obtain ⟨_, hpos_s, _, hm_hi_s⟩ := hmbSrc_info (by omega)
  obtain ⟨_, hpos_d0, hm_hi_d0, _⟩ := hmbDst_info (by omega)
  rw [ite_eq_left (by omega : ph < 10)] at hpos_d0 hm_hi_d0
  have hpSrc_or : pSrc = p0 ∨ pSrc = p1 := by dsimp only [pSrc]; split_ifs <;> simp
  have hpDst_or : pDst = p0 ∨ pDst = p1 := by dsimp only [pDst]; split_ifs <;> simp
  have hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc := by
    dsimp only [pSrc, pDst]; unfold p0 p1 hdrPBase0 hdrPBase1; split_ifs <;> omega
  have hmbHost_192 : base + 192 ≤ mbHost := by dsimp only [mbHost]; split_ifs <;> omega
  have hibHi_192 : base + 192 ≤ ibHi := hibLo_ge.trans hibHi_ge_ibLo.1
  have hpg_cap := hpgHost_cap (by omega) (by omega)
  have hcp_grow : (extractPageUnperm pgHost_al s_grow.mem).cleanPhase = 0 := by
    rw [extractPageUnperm_host_congr hw11 hmbHost_192 hgrow_ge192]
    exact hcp0
  have hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ pDst := by
    have hp_b : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
      rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] <;>
        dsimp only [p0, p1, hdrPBase0, hdrPBase1] <;> omega
    rcases hpos_s with ⟨hc0, hm_e | hm_e⟩ | ⟨_, h192⟩
    · rw [hm_e, ite_eq_left hc0]; unfold hdrSmallMeta0; omega
    · rw [hm_e, ite_eq_left hc0]; unfold hdrSmallMeta1; omega
    · exact Or.inl (by omega)
  have hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ pSrc := by
    have hp_b : base + 64 ≤ pSrc ∧ pSrc + 64 ≤ base + 192 := by
      rcases hpSrc_or with hp_e | hp_e <;> rw [hp_e] <;>
        dsimp only [p0, p1, hdrPBase0, hdrPBase1] <;> omega
    rcases hpos_d0 with ⟨hc0, hm_e | hm_e⟩ | ⟨_, h192⟩
    · rw [hm_e, ite_eq_left hc0]; unfold hdrSmallMeta0; omega
    · rw [hm_e, ite_eq_left hc0]; unfold hdrSmallMeta1; omega
    · exact Or.inl (by omega)
  have hmm_disj :
      mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ mbDst ∨
      mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ mbSrc := by
    have hge2 := hge2_all (by omega) (by omega)
    have hmD := hge2.1; have hp_eq := hge2.2.1
    have hp_ge : mSrc ≤ pad ∧ mDst ≤ pad := by
      rw [hp_eq, hmSrc_eq, hmD]; exact ⟨le_max_left _ _, le_max_right _ _⟩
    by_cases hd0 : nDst = 0
    · have hst0 := (hnDst0_all (by omega) hd0).2.1
      have hs_pos := (hnDst0_all (by omega) hd0).1
      simp only [hcap_s, hcap_d, capSrc, mbSrc, mbDst, hd0, hst0, hs_pos.ne', ↓reduceIte]
      unfold hdrSmallMeta1; exact Or.inr (by omega)
    · have hod_d := hod_le_nDst (by omega) hd0
      by_cases hst0 : stg = 0
      · by_cases hs0 : nSrc = 0
        · simp only [hcap_s, hcap_d, capSrc, mbSrc, mbDst, hd0, hst0, hs0, ↓reduceIte]
          unfold hdrSmallMeta0; exact Or.inl (by omega)
        · have hod_s := hod_le_nSrc hs0
          simp only [hcap_s, hcap_d, capSrc, mbSrc, mbDst, hd0, hst0, hs0, ↓reduceIte]
          exact Or.inl (by omega)
      · simp only [hcap_s, hcap_d, capSrc, mbSrc, mbDst, hd0, hst0, ↓reduceIte]
        exact Or.inr (by omega)
  exact ⟨hlift_grow (io0 := pagedSlotIo 0 pgHost) hsl_s rfl hpSrc_or hpos_s
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_cap.1, hfr_bounds.2.2.2.1 ⟨by omega, by omega⟩⟩)
      ⟨hm_hi_s (by omega), fun hup => absurd hup Nat.one_ne_zero⟩,
    hlift_grow (io0 := pagedSlotIo 1 pgHost) hsl_d rfl hpDst_or hpos_d0
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_cap.1, hfr_bounds.2.2.2.1 ⟨by omega, by omega⟩⟩)
      ⟨hm_hi_d0 (by omega), fun hup => absurd hup Nat.one_ne_zero⟩,
    hcp_grow, hp_disj, hpm_s, hpm_d, hmm_disj⟩

private theorem fgStep_eq8_raw_step {c U V w base opTag v_val k_grow : ℕ}
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
    (h8 : s.mem (base + hdrPhase) = 8) :
    let nLive := (Dictionary.dom s_dict).card
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let ph := s.mem (base + hdrPhase)
    let stg := s.mem (base + hdrStage)
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := s.mem (base + hdrNDst)
    let pad := s.mem (base + hdrPad)
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
    let pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
      else base + hdrPBase0
    let nHost := if nDst = 0 then nSrc else nDst
    let mbHost := if nDst = 0 then base + 192
      else if stg = 0 then base + 192 + pad else base + 192
    let pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
    let mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
      else base + 192 + pad
    let mbDst := if ph < 10 then
        (if nDst = 0 then base + hdrSmallMeta1
         else if stg = 0 then base + 192 + pad else base + 192)
      else
        (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
    let L_mid := L.applyFG ph opTag u v
    UserMutateRawPre w ((base, opTag), (u.val, v_val)) s_grow ∧
    s_raw.frontier = s_grow.frontier ∧
    EpochSlotInv c U V w s_raw.frontier pSrc mbSrc (pagedSlotIo 0 pgHost_al) 0 true
      L_mid.slotSrc s_raw.mem ∧
    EpochSlotInv c U V w s_raw.frontier pDst mbDst (pagedSlotIo 1 pgHost_al) 0 false
      L_mid.slotDst s_raw.mem ∧
    (extractPageUnperm pgHost_al s_raw.mem).cleanPhase = 0 ∧
    DisjointOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs ∧
    toDictState (orOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs) = s_dict' ∧
    (∀ addr < base + 48, s_raw.mem addr = s.mem addr) ∧
    (L_mid.slotSrc.GoodCovers ∧ L_mid.slotDst.GoodCovers →
      memoryCost (userMutateRawProg ((base, opTag), (u.val, v_val))) s_grow ≤
        2 * epochStepCost c + 6) := by
  have hnL_U := h.live_le; have hb192 := h.base_fr; have hsl_8 := h.sl_8
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost] at hsl_8
  have hgrow8 := fgStep_eq8_grow h u v hsetup hs_prep_def hk_grow_def h8
  have hdst_safe := hsetup.dst_safe
  have hibLo_ge := hsetup.ibLo_ge; have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hsm_src := hsetup.sm_src; have hsm_dst := hsetup.sm_dst
  have hmbSrc_info := hsetup.mbSrc_info; have hmbDst_info := hsetup.mbDst_info
  have hgrow_below0 := hsetup.grow_below; have hgrow_low0 := hsetup.grow_low
  dsimp only at hgrow8 hsm_src hsm_dst hmbSrc_info hmbDst_info ⊢
  rw [← hs_prep_def] at hgrow_below0 hgrow_low0
  clear hs_prep_def hk_grow_def
  set nLive := (Dictionary.dom s_dict).card
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set pad := s.mem (base + hdrPad)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hgrow_below : ∀ addr < base, s_grow.mem addr = s.mem addr := hgrow_below0
  have hgrow_low : ∀ off < 60, s_grow.mem (base + off) = s.mem (base + off) := hgrow_low0
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pSrc := if stg = 0 then p0 else p1
  set pDst := if ph < 10 then (if stg = 0 then p1 else p0) else p0
  set nHost := if nDst = 0 then nSrc else nDst
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
  set capSrc := if stg = 0 then nSrc else nDst
  set mbSrc := if stg = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192)
    else base + 192 + pad
  set mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  set L_mid := L.applyFG ph opTag u v
  have hs_grow_ph : s_grow.mem (base + hdrPhase) = ph := hgrow_low hdrPhase (by decide)
  have hs_grow_stg : s_grow.mem (base + hdrStage) = stg := hgrow_low hdrStage (by decide)
  have hle7 : ¬(ph ≤ 7) := by omega
  obtain ⟨hcap_s, hcap_d, hdj, hdict_or, _, _, _, _, _⟩ := hsl_8 h8
  obtain ⟨_, hpos_s, _, _⟩ := hmbSrc_info (by omega)
  obtain ⟨_, hpos_d, _, _⟩ := hmbDst_info (by omega)
  have hpDst_eq : pDst = (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) := by
    dsimp only [pDst, p0, p1]; rw [ite_eq_left (by omega)]
  have hmbDst_eq : mbDst = (if nDst = 0 then base + hdrSmallMeta1
      else if stg = 0 then base + 192 + pad else base + 192) := by
    dsimp only [mbDst]; rw [ite_eq_left (by omega)]
  have hmbHost_192 : base + 192 ≤ mbHost := by dsimp only [mbHost]; split_ifs <;> omega
  have hibHi_192 : base + 192 ≤ ibHi := hibLo_ge.trans hibHi_ge_ibLo.1
  obtain ⟨hsl_s_grow, hsl_d_grow0, hcp_grow, hp_disj0, hpm_s0, hpm_d0, hmm_disj0⟩ := hgrow8
  have hsl_d_grow : EpochSlotInv c U V w s_grow.frontier pDst mbDst
      (pagedSlotIo 1 pgHost_al) 0 false L.slotDst s_grow.mem := by
    rwa [hpDst_eq, hmbDst_eq]
  have hp_disj : pSrc + 64 ≤ pDst ∨ pDst + 64 ≤ pSrc := by rwa [hpDst_eq]
  have hpm_s : pDst + 64 ≤ mbSrc ∨
      mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ pDst := by
    rwa [hpDst_eq]
  have hpm_d : pSrc + 64 ≤ mbDst ∨
      mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ pSrc := by
    rwa [hmbDst_eq]
  have hmm_disj :
      mbSrc + (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤ mbDst ∨
      mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤ mbSrc := by
    rwa [hmbDst_eq]
  clear hsl_d_grow0 hp_disj0 hpm_s0 hpm_d0 hmm_disj0
  have hsum_card :
      (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card = nLive := by
    dsimp only [nLive]; rw [← hdict_or, dom_toDictState_card, liveDom_orOpt_card hdj]
  have hcap_d_8 : opTag = 1 → (orOpt L.slotDst.s_abs L.slotSrc.s_abs) u = none →
      (L.slotDst.nCap ≠ 0 →
        (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card < L.slotDst.nCap) ∧
      (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card + 1 ≤
        pgHost_al.nCap := by
    intro hop1 hor_none
    have hnone_d : s_dict u = none := by rw [← hdict_or]; simp [toDictState, hor_none]
    have hcap := cap_lt_on_insert_none h hnone_d
    rw [hsum_card, hcap_d]
    dsimp only [pgHost_al, hostPageLayout, epochPageArenaLayout, nAlloc]
    rw [ite_eq_left hop1, min_eq_left hcap.1]
    exact ⟨hcap.2.2 (by omega), le_rfl⟩
  have hcap_ov_8 : opTag = 1 →
      (L.slotDst.nCap ≠ 0 →
        (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card ≤ L.slotDst.nCap) ∧
      (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card ≤ pgHost_al.nCap := by
    intro hop1
    rw [hsum_card, hcap_d]
    dsimp only [pgHost_al, hostPageLayout, epochPageArenaLayout, nAlloc]
    rw [ite_eq_left hop1]
    refine ⟨fun hd_nz => ?_, le_min (Nat.le_succ _) hnL_U⟩
    have hds := hdst_safe; rw [ite_eq_right (by omega : ph ≠ 0)] at hds
    simp only [EpochCapSafe, hd_nz, ↓reduceIte] at hds; exact hds.2.2.2
  have hmut8 := dualPagedMutate_raw hsl_s_grow hsl_d_grow hdj hcp_grow hp_disj
    hpm_s hpm_d hmm_disj u v hv_eq hcap_d_8 hcap_ov_8
  have hum_disp := userMutateRawProg_eval (opTag := opTag) (u_val := u.val) (v_val := v_val)
      s_grow hs_grow_ph hs_grow_stg
  have hs_raw_prog :
      s_raw = (Memory.spec 0).clientState s_grow
        (if opTag = 1 then
           epochDeleteProg (pSrc, u.val) >>= fun _ => epochInsertProg ((pDst, u.val), v_val)
         else
           epochDeleteProg (pSrc, u.val) >>= fun _ => epochDeleteProg (pDst, u.val)) ∧
      memoryCost (userMutateRawProg ((base, opTag), (u.val, v_val))) s_grow =
        2 + memoryCost
          (if opTag = 1 then
             epochDeleteProg (pSrc, u.val) >>= fun _ => epochInsertProg ((pDst, u.val), v_val)
           else
             epochDeleteProg (pSrc, u.val) >>= fun _ => epochDeleteProg (pDst, u.val))
          s_grow := by
    rw [hs_raw_def, hum_disp.1, hum_disp.2, ← hpDst_eq]; clear hs_raw_def
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, ite_eq_left hop1, ite_eq_left h8]; exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hop1, ite_eq_right hop1, ite_eq_left h8]; exact ⟨rfl, rfl⟩
  clear hs_raw_def
  have hs_raw_fr : s_raw.frontier = s_grow.frontier := by rw [hs_raw_prog.1]; exact hmut8.2.2.1
  have hLmid_s8 : L_mid.slotSrc = L.slotSrc.applyFG true opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_right hle7, ite_eq_left h8]
  have hLmid_d8 : L_mid.slotDst = L.slotDst.applyFG false opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_right hle7, ite_eq_left h8]
  have hsl_s_raw : EpochSlotInv c U V w s_raw.frontier pSrc mbSrc
      (pagedSlotIo 0 pgHost_al) 0 true L_mid.slotSrc s_raw.mem := by
    rw [hLmid_s8, hs_raw_prog.1]; exact hmut8.2.2.2.2.2.2.1
  have hsl_d_raw : EpochSlotInv c U V w s_raw.frontier pDst mbDst
      (pagedSlotIo 1 pgHost_al) 0 false L_mid.slotDst s_raw.mem := by
    rw [hLmid_d8, hs_raw_prog.1]; exact hmut8.2.2.2.2.2.2.2.1
  have hcp_raw : (extractPageUnperm pgHost_al s_raw.mem).cleanPhase = 0 := by
    rw [hs_raw_prog.1]; exact hmut8.2.2.2.1
  have hdj' : DisjointOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs := by
    rw [hLmid_d8, hLmid_s8]; exact hmut8.2.2.2.2.1
  have hdict'_8 : toDictState (orOpt L_mid.slotDst.s_abs L_mid.slotSrc.s_abs) = s_dict' := by
    rw [hLmid_d8, hLmid_s8, hmut8.2.2.2.2.2.1, hdict_or]
  have hout_raw8 : ∀ addr,
      ¬slotOwnsAddr c w mbSrc L.slotSrc.nCap (pagedSlotIo 0 pgHost_al) addr →
      ¬slotOwnsAddr c w mbDst L.slotDst.nCap (pagedSlotIo 1 pgHost_al) addr →
      s_raw.mem addr = s_grow.mem addr := by
    rw [hs_raw_prog.1]; exact hmut8.2.2.2.2.2.2.2.2.1
  have howns_bs := slotOwnsAddr_bounds
    (c := c) (w := w) (base := base) (pad := pad) (pBase := pSrc)
    (metaBase := mbSrc) (nCap := L.slotSrc.nCap) (io := pagedSlotIo 0 pgHost_al)
    (fun h0 => by rcases hpos_s with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
    (fun hne => by
      rw [hcap_s] at hne; dsimp only [capSrc, mbSrc] at hne ⊢
      by_cases hst0 : stg = 0
      · rw [ite_eq_left hst0] at hne ⊢; rw [ite_eq_right hne]; exact Or.inl rfl
      · rw [ite_eq_right hst0]; exact Or.inr rfl)
    (fun _ => ⟨hmbHost_192, hibHi_192⟩)
    (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
  have howns_bd := slotOwnsAddr_bounds
    (c := c) (w := w) (base := base) (pad := pad) (pBase := pDst)
    (metaBase := mbDst) (nCap := L.slotDst.nCap) (io := pagedSlotIo 1 pgHost_al)
    (fun h0 => by rcases hpos_d with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
    (fun hne => by
      rw [hcap_d] at hne; dsimp only [mbDst]
      rw [ite_eq_left (by omega : ph < 10), ite_eq_right hne]
      split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl])
    (fun _ => ⟨hmbHost_192, hibHi_192⟩)
    (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
  have hs_raw_lt48 : ∀ addr < base + 48, s_raw.mem addr = s.mem addr := by
    intro addr hlt48
    rw [hout_raw8 addr
      (fun ha => absurd ((howns_bs addr ha).2.1 hlt48).2.1 Nat.one_ne_zero)
      (fun ha => absurd ((howns_bd addr ha).2.1 hlt48).2.1 Nat.one_ne_zero)]
    by_cases hge_b : base ≤ addr
    · have := hgrow_low (addr - base) (by omega)
      rwa [Nat.add_sub_of_le hge_b] at this
    · exact hgrow_below addr (by omega)
  refine ⟨⟨by dsimp only [s_grow]; omega, ?_⟩, hs_raw_fr, hsl_s_raw, hsl_d_raw, hcp_raw,
    hdj', hdict'_8, hs_raw_lt48, fun ⟨hg_s', hgc_d'⟩ => ?_⟩
  · have hpSrc_def : (if stg = 0 then base + hdrPBase0 else base + hdrPBase1) = pSrc := rfl
    dsimp (config := { iota := false, proj := false }) only
    rw [hs_grow_ph, hs_grow_stg, hpSrc_def, ← hpDst_eq]
    by_cases hop1 : opTag = 1
    · have hm2 := hmut8.2.1; rw [ite_eq_left hop1] at hm2
      rw [ite_eq_left hop1, ite_eq_left h8]; exact ⟨hmut8.1, hm2⟩
    · have hm2 := hmut8.2.1; rw [ite_eq_right hop1] at hm2
      rw [ite_eq_right hop1, ite_eq_left h8]; exact ⟨hmut8.1, hm2⟩
  · have hg_s0 : L.slotSrc.GoodCovers := by
      rw [hLmid_s8] at hg_s'; unfold SlotLatent.applyFG at hg_s'
      simp only [↓reduceIte] at hg_s'
      split_ifs at hg_s' <;> exact hg_s'
    rw [hs_raw_prog.2]
    have hc_raw := hmut8.2.2.2.2.2.2.2.2.2 (hsm_src (by omega)) (hsm_dst (by omega))
      hg_s0 (by rw [← hLmid_d8]; exact hgc_d')
    omega

private theorem fgStep_eq8_raw_aux {c U V w base opTag v_val k_grow : ℕ}
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
    (h8 : s.mem (base + hdrPhase) = 8) :
    FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid := by
  have hUw := h.U_lt; have hb192 := h.base_fr; have hsl_8 := h.sl_8
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost] at hsl_8
  have hraw8 := fgStep_eq8_raw_step h u v hv_eq hsetup hs_prep_def hk_grow_def hs_raw_def h8
  have hcard_step := hsetup.card_step
  have hibLo_ge := hsetup.ibLo_ge; have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hpgHost_cap := hsetup.pgHost_cap
  have hmbSrc_info := hsetup.mbSrc_info; have hmbDst_info := hsetup.mbDst_info
  have hfr_n' := hsetup.fr_n'
  dsimp only [FGStepOutAux] at hraw8 hcard_step hpgHost_cap hmbSrc_info hmbDst_info hfr_n' ⊢
  rw [← hk_grow_def] at hfr_n'
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
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pSrc := if stg = 0 then p0 else p1
  set pDst := if ph < 10 then (if stg = 0 then p1 else p0) else p0
  set nHost := if nDst = 0 then nSrc else nDst
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
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
  have hle7 : ¬(ph ≤ 7) := by omega
  obtain ⟨hcap_s, hcap_d, _, _, _, _, _, hlen_s, hlen_d⟩ := hsl_8 h8
  obtain ⟨_, hpos_s, _, hm_hi_s⟩ := hmbSrc_info (by omega)
  obtain ⟨_, hpos_d, hm_hi_d, _⟩ := hmbDst_info (by omega)
  have hpSrc_or : pSrc = p0 ∨ pSrc = p1 := by dsimp only [pSrc]; split_ifs <;> simp
  have hpDst_eq : pDst = (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) := by
    dsimp only [pDst, p0, p1]; rw [ite_eq_left (by omega)]
  have hpDst_or : pDst = p0 ∨ pDst = p1 := by
    dsimp only [pDst]; rw [ite_eq_left (by omega)]; split_ifs <;> simp
  have hmbHost_192 : base + 192 ≤ mbHost := by dsimp only [mbHost]; split_ifs <;> omega
  have hibHi_192 : base + 192 ≤ ibHi := hibLo_ge.trans hibHi_ge_ibLo.1
  have hpg_cap := hpgHost_cap (by omega) (by omega)
  obtain ⟨hraw_pre, hs_raw_fr, hsl_s_raw, hsl_d_raw, hcp_raw, hdj', hdict'_8,
    hs_raw_lt48, hmc_raw8⟩ := hraw8
  have hLmid_s8 : L_mid.slotSrc = L.slotSrc.applyFG true opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_right hle7, ite_eq_left h8]
  have hLmid_d8 : L_mid.slotDst = L.slotDst.applyFG false opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_right hle7, ite_eq_left h8]
  have hsync_ev := syncLiveCountsProg_eval (base := base) s_raw
  have hs_raw_ph : s_raw.mem (base + hdrPhase) = ph :=
    hs_raw_lt48 (base + hdrPhase) (by unfold hdrPhase; omega)
  have hs_raw_stg : s_raw.mem (base + hdrStage) = stg :=
    hs_raw_lt48 (base + hdrStage) (by unfold hdrStage; omega)
  have hns_s_raw : (Memory.spec 0).clientResult s_raw (epochReadNSideProg pSrc) =
      (liveDom L_mid.slotSrc.s_abs).card := hsl_s_raw.readNSide_eq
  have hns_d_raw : (Memory.spec 0).clientResult s_raw (epochReadNSideProg pDst) =
      (liveDom L_mid.slotDst.s_abs).card := hsl_d_raw.readNSide_eq
  have hsum_card' : (liveDom L_mid.slotSrc.s_abs).card +
      (liveDom L_mid.slotDst.s_abs).card = nLive' := by
    rw [add_comm, ← liveDom_orOpt_card hdj', ← dom_toDictState_card, hdict'_8]
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
    dsimp only [p0, p1] at hns_s_raw ⊢
    rw [hs_raw_ph, hs_raw_stg, ite_eq_left h8, ← hpDst_eq]
    dsimp only [pSrc, p0, p1] at hns_s_raw
    rw [hns_s_raw, hns_d_raw, hsum_card']
  have hs_mid_fr : s_mid.frontier = s_grow.frontier := by
    rw [hs_mid_eq, hsync_ev.1]; exact hs_raw_fr
  have hs_mid_mem : s_mid.mem =
      Function.update
        (Function.update (Function.update s_raw.mem (base + hdrLive) nLive') (p0 + 60) nLive')
        (p1 + 60) nLive' := by
    dsimp only [p0, p1] at hnL'_sync ⊢
    rw [hs_mid_eq, hsync_ev.1]; dsimp only
    rw [hnL'_sync, hs_raw_ph, ite_eq_right (by omega : ¬((ph = 3 ∨ ph = 10) ∧ _))]
  have hti_raw : (extractPagePair pgHost_al s_raw.mem).totalItems = nLive' := by
    have hi0 := hsl_s_raw.io_stateInv; have hi1 := hsl_d_raw.io_stateInv
    unfold SlotIoLayout.StateInv at hi0 hi1
    simp only [pagedSlotIo, one_ne_zero, ↓reduceIte] at hi0 hi1
    have hv0 : (extractPagePair pgHost_al s_raw.mem).virtLen false = s_raw.mem (mbSrc + 1) :=
      hi0.2.2.2.2.1
    have hv1 : (extractPagePair pgHost_al s_raw.mem).virtLen true = s_raw.mem (mbDst + 1) :=
      hi1.2.2.2.2.1
    rw [hsl_s_raw.mem_nSide_eq] at hv0; rw [hsl_d_raw.mem_nSide_eq] at hv1
    unfold PagePairState.totalItems
    omega
  have hsl_s_mid : EpochSlotInv c U V w s_mid.frontier pSrc mbSrc
      (pagedSlotIo 0 pgHost_fin) 0 true L_mid.slotSrc s_mid.mem := by
    change EpochSlotInv c U V w s_mid.frontier pSrc mbSrc
      ((pagedSlotIo 0 pgHost_al).withNCap nLive') 0 true L_mid.slotSrc s_mid.mem
    refine EpochSlotInv.lift_sync (base := base)
      (by rw [hs_mid_fr]; dsimp only [s_grow]; rw [← hs_raw_fr]; exact hsl_s_raw) le_rfl
      (lt_of_le_of_lt hcard_step.2.2.2.2.2.1 hUw) hpSrc_or
      (by rw [hLmid_s8, SlotLatent.applyFG_nCap]; exact hpos_s)
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_cap.2, by rw [hs_mid_fr]; exact hfr_n'.2 ⟨by omega, by omega⟩⟩)
      ⟨by rw [hLmid_s8, SlotLatent.applyFG_nCap]; exact hm_hi_s (by omega),
       fun hup => absurd hup Nat.one_ne_zero⟩
      (by rw [hsl_s_raw.mem_nSide_eq]; omega) (fun _ => hti_raw.le)
      (by rw [hs_mid_mem]; rcases hpSrc_or with hp_e | hp_e <;> rw [hp_e] <;>
          dsimp only [p0, p1, hdrPBase0, hdrPBase1]
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_self])
      (fun a ha1 ha2 hne => by
        rw [hs_mid_mem]; rcases hpSrc_or with hp_e | hp_e <;> rw [hp_e] at ha1 ha2 hne <;>
          dsimp only [p0, p1, hdrPBase0, hdrPBase1, hdrLive] at ha1 ha2 hne ⊢ <;>
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)])
      (fun a ha => by
        rw [hs_mid_mem]
        dsimp only [p0, p1, hdrPBase0, hdrPBase1, hdrLive, hdrSplit] at ha ⊢
        rw [Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega),
          Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega),
          Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega)])
  have hsl_d_mid : EpochSlotInv c U V w s_mid.frontier pDst mbDst
      (pagedSlotIo 1 pgHost_fin) 0 false L_mid.slotDst s_mid.mem := by
    change EpochSlotInv c U V w s_mid.frontier pDst mbDst
      ((pagedSlotIo 1 pgHost_al).withNCap nLive') 0 false L_mid.slotDst s_mid.mem
    refine EpochSlotInv.lift_sync (base := base)
      (by rw [hs_mid_fr]; dsimp only [s_grow]; rw [← hs_raw_fr]; exact hsl_d_raw) le_rfl
      (lt_of_le_of_lt hcard_step.2.2.2.2.2.1 hUw) hpDst_or
      (by rw [hLmid_d8, SlotLatent.applyFG_nCap]; exact hpos_d)
      ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      (fun hup => absurd hup Nat.one_ne_zero) (fun hup => absurd hup Nat.one_ne_zero)
      (fun _ => ⟨hpg_cap.2, by rw [hs_mid_fr]; exact hfr_n'.2 ⟨by omega, by omega⟩⟩)
      ⟨by rw [hLmid_d8, SlotLatent.applyFG_nCap]; exact hm_hi_d (by omega),
       fun hup => absurd hup Nat.one_ne_zero⟩
      (by rw [hsl_d_raw.mem_nSide_eq]; omega) (fun _ => hti_raw.le)
      (by rw [hs_mid_mem]; rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] <;>
          dsimp only [p0, p1, hdrPBase0, hdrPBase1]
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_self])
      (fun a ha1 ha2 hne => by
        rw [hs_mid_mem]; rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] at ha1 ha2 hne <;>
          dsimp only [p0, p1, hdrPBase0, hdrPBase1, hdrLive] at ha1 ha2 hne ⊢ <;>
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)])
      (fun a ha => by
        rw [hs_mid_mem]
        dsimp only [p0, p1, hdrPBase0, hdrPBase1, hdrLive, hdrSplit] at ha ⊢
        rw [Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega),
          Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega),
          Function.update_of_ne (by rcases ha with rfl | _ | _ <;> omega)])
  have hcp_mid : (extractPageUnperm pgHost_fin s_mid.mem).cleanPhase = 0 := by
    have hu_eq : extractPageUnperm pgHost_fin s_mid.mem =
        extractPageUnperm pgHost_al s_raw.mem :=
      extractPageUnperm_host_congr h.hw11 hmbHost_192 fun a h192 => by
        rw [hs_mid_mem]; unfold p0 p1 hdrPBase0 hdrPBase1 hdrLive
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
    rw [hu_eq]; exact hcp_raw
  refine ⟨⟨hraw_pre,
      hsync_pre_eq.mpr ⟨by rw [hs_raw_fr]; omega, ?_⟩⟩,
    hs_mid_fr, ?_, ?_, ?_, fun h => absurd h8 (by rcases h with h | h <;> omega),
    fun h => absurd h8 (by omega), fun h => absurd h8 (by omega),
    fun h => absurd h8 (by rcases h with h | h <;> omega),
    fun h => absurd h8 (by omega), fun h => absurd h8 (by omega),
    fun _ => ?_, fun h => absurd h8 (by omega), fun _ hg8 _ => ?_⟩
  · have hpSrc_def : (if stg = 0 then base + hdrPBase0 else base + hdrPBase1) = pSrc := rfl
    dsimp (config := { iota := false, proj := false }) only
    rw [hs_raw_ph, hs_raw_stg, hpSrc_def, ite_eq_left h8, ← hpDst_eq, hns_s_raw, hns_d_raw,
      hsum_card']
    exact ⟨hsl_s_raw.epochProgPre, hsl_d_raw.epochProgPre,
      lt_of_le_of_lt hcard_step.2.2.2.2.2.1 hUw⟩
  · rw [hs_mid_mem]; unfold p0 p1 hdrPBase0 hdrPBase1 hdrLive
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · intro addr ha48 hne_l _
    rw [hs_mid_mem]; unfold p0 p1 hdrPBase0 hdrPBase1
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne hne_l]
    exact hs_raw_lt48 addr ha48
  · intro _ _
    rw [hs_mid_mem]; unfold p0 p1 hdrPBase0 hdrPBase1 hdrLive hdrSplit
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hs_raw_lt48 (base + hdrSplit) (by unfold hdrSplit; omega)
  · refine ⟨by rw [hLmid_s8, SlotLatent.applyFG_nCap]; exact hcap_s,
      by rw [hLmid_d8, SlotLatent.applyFG_nCap]; exact hcap_d,
      hdj', hdict'_8, hcp_mid, hsl_s_mid, hsl_d_mid,
      fun hc_pos => ?_, fun hd_pos => ?_⟩
    · have hl0 := hlen_s hc_pos
      rw [hLmid_s8]; unfold SlotLatent.applyFG; simp only [↓reduceIte]; split_ifs <;> exact hl0
    · have hl0 := hlen_d hd_pos
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl0
      have hcard_le :
          (liveDom L_mid.slotSrc.s_abs).card ≤ (liveDom L.slotSrc.s_abs).card := by
        have hs_del : L_mid.slotSrc.s_abs = Function.update L.slotSrc.s_abs u none := by
          rw [hLmid_s8]; unfold SlotLatent.applyFG; simp only [↓reduceIte]; split_ifs <;> rfl
        rw [hs_del, liveDom_delete_card]; split_ifs <;> omega
      rw [hLmid_d8]; unfold SlotLatent.applyFG
      by_cases hop1 : opTag = 1
      · rw [ite_eq_left hop1]
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
        omega
      · rw [ite_eq_right hop1]
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
        omega
  · rw [hmc_um_eq]
    have hc_raw := hmc_raw8 (hg8 h8)
    have hc_sync := hsync_ev.2
    omega

/-- Auxiliary opaque-state version of `fgStep_eq8`. -/
theorem fgStep_eq8_aux {c U V w base opTag v_val k_grow : ℕ}
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
    (h8 : s.mem (base + hdrPhase) = 8) :
    FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid :=
  fgStep_eq8_raw_aux h u v hv_eq hsetup hs_prep_def hk_grow_def rfl hs_mid_def h8

private theorem fgStep_ge9_grow {c U V w base opTag k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hge9 : 9 ≤ s.mem (base + hdrPhase)) :
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
    let uDone := s.mem (base + hdrUnpermDone)
    let vB := valBits V
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
      else base + hdrPBase0
    let mbDst := if ph < 10 then
        (if nDst = 0 then base + hdrSmallMeta1
         else if stg = 0 then base + 192 + pad else base + 192)
      else
        (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
    let io_d0 := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive uDone
    let io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
    ((io_d0.usePaged = 0 → io_d0.sideBit ≠ 0 →
        io_d0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io_d0.pgL.offDir) ∧
      (io_d0.usePaged ≠ 0 → base + 192 ≤ io_d0.pgL.metaBase) ∧
      base + 192 ≤ io_d0.pgL.itemBase) ∧
    (mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
        io_d0.pgL.itemBase ∧
      (io_d0.usePaged = 0 → io_d0.sideBit ≠ 0 →
        mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
          io_d0.pgL.offDir)) ∧
    EpochSlotInv c U V w s_grow.frontier pDst mbDst io_dal 0 false L.slotDst s_grow.mem ∧
    (io_dal.usePaged ≠ 0 → (extractPagePair io_dal.pgL s_grow.mem).totalItems = nLive) := by
  have hw11 := h.hw11; have hph_le := h.ph_le; have hph9_inv := h.ph9_inv; have hsl_ge9 := h.sl_ge9
  dsimp only [dualMbDst, dualPDst, dualNHost, dualMbHost, dualPgHost] at hph9_inv hsl_ge9
  have hibLo_ge := hsetup.ibLo_ge; have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hfr_bounds := hsetup.fr_bounds; have hpgHost_cap := hsetup.pgHost_cap
  have hmbDst_info := hsetup.mbDst_info; have hgrow_ge192 := hsetup.grow_ge192
  have hlift_grow := @FGSetup.lift_grow_slot c U V w base opTag u v s_dict L s hsetup
  dsimp only at hfr_bounds hpgHost_cap hmbDst_info hlift_grow ⊢
  rw [← hk_grow_def] at hfr_bounds
  rw [← hs_prep_def, ← hk_grow_def] at hlift_grow
  rw [← hs_prep_def] at hgrow_ge192
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
  set uDone := s.mem (base + hdrUnpermDone)
  set vB := valBits V
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  set pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
    else base + hdrPBase0
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set nHost := if nDst = 0 then nSrc else nDst
  set pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
  set pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
  set mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  set io_d0 := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive uDone
  set io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
  obtain ⟨_, hdict_d, hsl_d, _⟩ := hsl_ge9 hge9
  obtain ⟨_, hpos_d, hm_hi_d, hm_lo_d⟩ := hmbDst_info (by omega)
  have hpDst_or : pDst = base + hdrPBase0 ∨ pDst = base + hdrPBase1 := by
    dsimp only [pDst]; split_ifs <;> simp
  have hslk0 : (if false ∧ ph = 9 ∧ uDone = 0 then 24 else 0) = 0 := rfl
  have hsl_d0 : EpochSlotInv c U V w s.frontier pDst mbDst io_d0 0 false L.slotDst s.mem :=
    hslk0 ▸ hsl_d
  have hmbHost_192 : base + 192 ≤ mbHost := by dsimp only [mbHost]; split_ifs <;> omega
  have hibHi_192 : base + 192 ≤ ibHi := hibLo_ge.trans hibHi_ge_ibLo.1
  have hio_pos_d :
      (io_d0.usePaged = 0 → io_d0.sideBit ≠ 0 →
        io_d0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io_d0.pgL.offDir) ∧
      (io_d0.usePaged ≠ 0 → base + 192 ≤ io_d0.pgL.metaBase) ∧
      base + 192 ≤ io_d0.pgL.itemBase := by
    dsimp only [io_d0, activeDstIo]
    rw [ite_eq_right (by omega : ¬(ph < 8)), ite_eq_right (by omega : ph ≠ 8)]
    by_cases hp9 : ph = 9
    · rw [ite_eq_left hp9]
      by_cases hud0 : uDone = 0
      · rw [ite_eq_left hud0]; dsimp only [pagedSlotIo, hostPageLayout, epochPageArenaLayout]
        exact ⟨fun hup => absurd hup Nat.one_ne_zero, fun _ => hmbHost_192, hibHi_192⟩
      · rw [ite_eq_right hud0]; dsimp only [directSlotIo]
        exact ⟨fun _ hsb => absurd rfl hsb, fun hup => absurd rfl hup, hibHi_192⟩
    · rw [ite_eq_right hp9]
      by_cases hp10 : ph = 10
      · rw [ite_eq_left hp10]; dsimp only [splitSlotIo]
        exact ⟨fun _ _ => ⟨rfl, hibLo_ge⟩, fun hup => absurd rfl hup, hibHi_192⟩
      · rw [ite_eq_right hp10]; dsimp only [directSlotIo]
        exact ⟨fun _ hsb => absurd rfl hsb, fun hup => absurd rfl hup, hibLo_ge⟩
  have hm_ib_d :
      mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
        io_d0.pgL.itemBase ∧
      (io_d0.usePaged = 0 → io_d0.sideBit ≠ 0 →
        mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
          io_d0.pgL.offDir) := by
    dsimp only [io_d0, activeDstIo]
    rw [ite_eq_right (by omega : ¬(ph < 8)), ite_eq_right (by omega : ph ≠ 8)]
    by_cases hp9 : ph = 9
    · rw [ite_eq_left hp9]
      by_cases hud0 : uDone = 0
      · rw [ite_eq_left hud0]
        exact ⟨hm_hi_d (by omega), fun hup => absurd hup Nat.one_ne_zero⟩
      · rw [ite_eq_right hud0]
        exact ⟨hm_hi_d (by omega), fun _ hsb => absurd rfl hsb⟩
    · rw [ite_eq_right hp9]
      by_cases hp10 : ph = 10
      · rw [ite_eq_left hp10]; dsimp only [splitSlotIo]
        exact ⟨hm_hi_d (by omega), fun _ _ => hm_lo_d (by omega)⟩
      · rw [ite_eq_right hp10]; dsimp only [directSlotIo]
        exact ⟨hm_lo_d (by omega), fun _ hsb => absurd rfl hsb⟩
  have hsl_grow : EpochSlotInv c U V w s_grow.frontier pDst mbDst io_dal 0 false
      L.slotDst s_grow.mem := by
    have hio_eq0 : io_d0.withNCap nAlloc = io_dal :=
      activeDstIo_withNCap c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive nAlloc uDone
    rw [← hio_eq0]
    refine hlift_grow hsl_d0
      (by dsimp only [io_d0, activeDstIo]; split_ifs <;> rfl)
      hpDst_or hpos_d hio_pos_d (fun hup hsb => ?_) (fun hup hsb => ?_)
      (fun hup => ?_) hm_ib_d
    · dsimp only [io_d0, activeDstIo] at hup hsb ⊢
      rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hup hsb ⊢
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9] at hup hsb ⊢
        by_cases hud0 : uDone = 0
        · rw [ite_eq_left hud0] at hup; exact absurd hup Nat.one_ne_zero
        · rw [ite_eq_right hud0]; exact hfr_bounds.2.2.2.1 ⟨by omega, by omega⟩
      · rw [ite_eq_right hp9] at hup hsb ⊢
        by_cases hp10 : ph = 10
        · rw [ite_eq_left hp10] at hsb; dsimp only [splitSlotIo] at hsb; omega
        · rw [ite_eq_right hp10]; exact hfr_bounds.2.2.1 (Or.inr (by omega))
    · dsimp only [io_d0, activeDstIo] at hup hsb ⊢
      rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hup hsb ⊢
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9] at hup hsb
        by_cases hud0 : uDone = 0
        · rw [ite_eq_left hud0] at hup; exact absurd hup Nat.one_ne_zero
        · rw [ite_eq_right hud0] at hsb; exact absurd rfl hsb
      · rw [ite_eq_right hp9] at hsb ⊢
        by_cases hp10 : ph = 10
        · rw [ite_eq_left hp10]; exact hfr_bounds.2.2.2.1 ⟨by omega, by omega⟩
        · rw [ite_eq_right hp10] at hsb; exact absurd rfl hsb
    · dsimp only [io_d0, activeDstIo] at hup ⊢
      rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hup ⊢
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9] at hup ⊢
        by_cases hud0 : uDone = 0
        · rw [ite_eq_left hud0]
          exact ⟨(hpgHost_cap (by omega) (by omega)).1,
            hfr_bounds.2.2.2.1 ⟨by omega, by omega⟩⟩
        · rw [ite_eq_right hud0] at hup; exact absurd rfl hup
      · rw [ite_eq_right hp9] at hup
        split_ifs at hup <;> exact absurd rfl hup
  have hti_ph9 : io_dal.usePaged ≠ 0 →
      (extractPagePair io_dal.pgL s_grow.mem).totalItems = nLive := by
    intro hup
    have hp9_ud : ph = 9 ∧ uDone = 0 := by
      dsimp only [io_dal, activeDstIo] at hup
      rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hup
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9] at hup
        by_cases hud0 : uDone = 0
        · exact ⟨hp9, hud0⟩
        · rw [ite_eq_right hud0] at hup; exact absurd rfl hup
      · rw [ite_eq_right hp9] at hup
        split_ifs at hup <;> exact absurd rfl hup
    have hcp_gt := ((hph9_inv hp9_ud.1).2.2.2 hp9_ud.2).1
    have hio_g := hsl_grow.io_stateInv
    unfold SlotIoLayout.StateInv at hio_g; rw [ite_eq_right hup] at hio_g
    have hpg_eq_g : io_dal.pgL = pgHost_al ∧ io_dal.side = true := by
      dsimp only [io_dal, activeDstIo]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp9_ud.1,
        ite_eq_left hp9_ud.2]
      exact ⟨rfl, rfl⟩
    have hu_eq_g : extractPageUnperm pgHost_al s_grow.mem = extractPageUnperm pgHost s.mem :=
      extractPageUnperm_host_congr hw11 hmbHost_192 hgrow_ge192
    have hcp_g : 0 < (extractPageUnperm io_dal.pgL s_grow.mem).cleanPhase := by
      rw [hpg_eq_g.1, hu_eq_g]; exact hcp_gt
    have hvl_f0 : (extractPagePair io_dal.pgL s_grow.mem).virtLen false = 0 :=
      virtLen_false_zero_of_cleanPhase hio_g.1 hcp_g
    have hvl_t : (extractPagePair io_dal.pgL s_grow.mem).virtLen true = nLive := by
      have hvt : (extractPagePair io_dal.pgL s_grow.mem).virtLen io_dal.side =
          s_grow.mem (mbDst + 1) := hio_g.2.2.2.2.1
      rw [hpg_eq_g.2, hsl_grow.mem_nSide_eq, ← dom_toDictState_card, hdict_d] at hvt
      exact hvt
    unfold PagePairState.totalItems; omega
  exact ⟨hio_pos_d, hm_ib_d, hsl_grow, hti_ph9⟩

private theorem fgStep_ge9_ph10 {c U V w base nLive nLive' nAlloc ph stg nSrc nDst pad
    ibLo ibHi qLo qHi uDone pDst mbDst fr_mid : ℕ}
    {slDst' : SlotLatent c U V} {m0 m_grow m_raw m_mid : ℕ → ℕ}
    (_hge9 : 9 ≤ ph)
    (hcard_diff : nLive' ≤ nLive + 1)
    (hph10_inv : ph = 10 →
      m0 (base + hdrSplit) ≤ nLive ∧
      SplitHiQuotBounded (splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive) nLive m0)
    (hibLo_192 : base + 192 ≤ ibLo)
    (hibHi_192 : base + 192 ≤ ibHi)
    (hgrow_sp : m_grow (base + hdrSplit) = m0 (base + hdrSplit))
    (hgrow_ge192 : ∀ addr, base + 192 ≤ addr → m_grow addr = m0 addr)
    (hns_grow : m_grow (mbDst + 1) = nLive)
    (hpDst_or : pDst = base + hdrPBase0 ∨ pDst = base + hdrPBase1)
    (hpos_d : (slDst'.nCap = 0 ∧ (mbDst = base + hdrSmallMeta0 ∨ mbDst = base + hdrSmallMeta1)) ∨
      (slDst'.nCap ≠ 0 ∧ base + 192 ≤ mbDst))
    (hs_raw_sp : m_raw (base + hdrSplit) = m0 (base + hdrSplit))
    (hns_m_eq : m_raw (mbDst + 1) = nLive')
    (hhi_pres :
      let io_dal :=
        activeDstIo c w (valBits V) base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
      io_dal.usePaged = 0 → io_dal.sideBit ≠ 0 →
        SplitHiQuotBounded io_dal (m_grow (mbDst + 1)) m_grow →
        SplitHiQuotBounded io_dal nLive' m_raw)
    (hsl_m3 :
      let m3 := Function.update
        (Function.update (Function.update m_raw (base + hdrLive) nLive')
          (base + hdrPBase0 + 60) nLive')
        (base + hdrPBase1 + 60) nLive'
      let slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
      EpochSlotInv c U V w fr_mid pDst mbDst
        (activeDstIo c w (valBits V) base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive' uDone)
        slackDst' false slDst' m3)
    (hs_mid_mem :
      let m3 := Function.update
        (Function.update (Function.update m_raw (base + hdrLive) nLive')
          (base + hdrPBase0 + 60) nLive')
        (base + hdrPBase1 + 60) nLive'
      m_mid =
        if ph = 10 ∧ nLive' < m0 (base + hdrSplit) then
          Function.update m3 (base + hdrSplit) nLive'
        else m3) :
    let slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
    EpochSlotInv c U V w fr_mid pDst mbDst
      (activeDstIo c w (valBits V) base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive' uDone)
      slackDst' false slDst' m_mid ∧
    (ph = 10 →
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
  set slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
  set io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
  set io_dfin := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive' uDone
  have hm3_sp : m3 (base + hdrSplit) = sp := by
    dsimp only [m3]; unfold hdrPBase0 hdrPBase1 hdrLive hdrSplit
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hs_raw_sp
  by_cases hp10 : ph = 10
  · obtain ⟨_, hhi0⟩ := hph10_inv hp10
    have hslk10 : slackDst' = 0 := by
      dsimp only [slackDst']; rw [ite_eq_right (fun h => by omega)]
    have hio_al_sp : io_dal = splitSlotIo w vB base ibLo qLo ibHi qHi nAlloc := by
      dsimp only [io_dal, activeDstIo]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left hp10]
    have hio_fin_sp : io_dfin = splitSlotIo w vB base ibLo qLo ibHi qHi nLive' := by
      dsimp only [io_dfin, activeDstIo]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left hp10]
    have hhi_grow : SplitHiQuotBounded io_dal (m_grow (mbDst + 1)) m_grow := by
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
    have hhi_raw : SplitHiQuotBounded io_dal nLive' m_raw :=
      hhi_pres (by rw [hio_al_sp]; rfl) (by rw [hio_al_sp]; exact Nat.one_ne_zero) hhi_grow
    have hhi_m3 : SplitHiQuotBounded
        (splitSlotIo w vB base ibLo qLo ibHi qHi nLive') nLive' m3 := by
      intro idx hge hlt
      dsimp only [splitSlotIo] at hge ⊢; rw [hm3_sp] at hge
      have hge_raw : m_raw io_dal.pgL.metaBase ≤ idx := by
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
    · rw [hs_mid_mem, ite_eq_left ⟨hp10, hlt_sp⟩]
      have hm3_ns : m3 (mbDst + 1) = nLive' := by
        dsimp only [m3]; unfold hdrPBase0 hdrPBase1 hdrLive
        have hmb_ge : base + 48 ≤ mbDst ∧ mbDst + 1 ≠ base + 64 + 60 ∧
            mbDst + 1 ≠ base + 128 + 60 := by
          clear hsl_m3
          rcases hpos_d with ⟨_, hm_e | hm_e⟩ | ⟨_, h192⟩ <;> (try rw [hm_e]) <;>
            (try dsimp only [hdrSmallMeta0, hdrSmallMeta1]) <;>
            exact ⟨by omega, by omega, by omega⟩
        rw [Function.update_of_ne hmb_ge.2.2, Function.update_of_ne hmb_ge.2.1,
          Function.update_of_ne (by omega)]
        exact hns_m_eq
      have hsl_m3' : EpochSlotInv c U V w fr_mid pDst mbDst
        (splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive') 0 false slDst' m3 := by
        rwa [← hslk10, ← hio_fin_sp]
      have hp_ge48 : base + 48 ≤ pDst := by
        clear hsl_m3 hsl_m3'
        rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] <;>
          (try dsimp only [hdrPBase0, hdrPBase1]) <;> omega
      have hmb_ge48 : base + 48 ≤ mbDst := by
        clear hsl_m3 hsl_m3'
        rcases hpos_d with ⟨_, hm_e | hm_e⟩ | ⟨_, h192⟩ <;> (try rw [hm_e]) <;>
          (try dsimp only [hdrSmallMeta0, hdrSmallMeta1]) <;> omega
      have hcl := hsl_m3'.clamp_split_cursor hp_ge48 hmb_ge48
        (by clear hsl_m3 hsl_m3'; omega) hm3_ns (by rwa [hm3_sp])
      rw [hio_fin_sp, hslk10]
      exact ⟨hcl.1, fun _ => ⟨by rw [Function.update_self],
        by clear hsl_m3 hsl_m3' hcl; rw [Function.update_self]; omega,
        by clear hsl_m3 hsl_m3' hcl; rw [Function.update_self]; omega, hcl.2⟩⟩
    · rw [hs_mid_mem, ite_eq_right (fun h => hlt_sp h.2)]
      exact ⟨hsl_m3, fun _ => ⟨by clear hsl_m3; rw [hm3_sp]; omega, by rw [hm3_sp],
        by clear hsl_m3; rw [hm3_sp]; omega, hhi_m3⟩⟩
  · rw [hs_mid_mem, ite_eq_right (fun h => hp10 h.1)]
    exact ⟨hsl_m3, fun h => absurd h hp10⟩

private theorem fgStep_ge9_raw_step {c U V w base opTag v_val k_grow : ℕ}
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
    (hge9_in : 9 ≤ s.mem (base + hdrPhase)) :
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
    let uDone := s.mem (base + hdrUnpermDone)
    let vB := valBits V
    let nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
      else base + hdrPBase0
    let mbDst := if ph < 10 then
        (if nDst = 0 then base + hdrSmallMeta1
         else if stg = 0 then base + 192 + pad else base + 192)
      else
        (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
    let L_mid := L.applyFG ph opTag u v
    let slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
    let io_d0 := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive uDone
    let io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
    UserMutateRawPre w ((base, opTag), (u.val, v_val)) s_grow ∧
    s_raw.frontier = s_grow.frontier ∧
    EpochSlotInv c U V w s_raw.frontier pDst mbDst io_dal slackDst' false L_mid.slotDst s_raw.mem ∧
    toDictState L_mid.slotDst.s_abs = s_dict' ∧
    (∀ addr, ¬slotOwnsAddr c w mbDst L.slotDst.nCap io_dal addr →
      s_raw.mem addr = s_grow.mem addr) ∧
    (io_dal.usePaged = 0 → io_dal.sideBit ≠ 0 →
      s_raw.mem io_dal.pgL.metaBase = s_grow.mem io_dal.pgL.metaBase) ∧
    (io_dal.usePaged = 0 → io_dal.sideBit ≠ 0 →
      SplitHiQuotBounded io_dal (s_grow.mem (mbDst + 1)) s_grow.mem →
      SplitHiQuotBounded io_dal nLive' s_raw.mem) ∧
    (io_dal.usePaged ≠ 0 →
      PagedUnpermStep io_dal.side (extractPageUnperm io_dal.pgL s_grow.mem)
        (extractPageUnperm io_dal.pgL s_raw.mem)) ∧
    (L_mid.slotDst.GoodCovers →
      memoryCost (userMutateRawProg ((base, opTag), (u.val, v_val))) s_grow ≤
        epochStepCost c + 2) ∧
    s_grow.mem (mbDst + 1) = nLive ∧
    ((io_d0.usePaged = 0 → io_d0.sideBit ≠ 0 →
        io_d0.pgL.metaBase = base + hdrSplit ∧ base + 192 ≤ io_d0.pgL.offDir) ∧
      (io_d0.usePaged ≠ 0 → base + 192 ≤ io_d0.pgL.metaBase) ∧
      base + 192 ≤ io_d0.pgL.itemBase) ∧
    (mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
        io_d0.pgL.itemBase ∧
      (io_d0.usePaged = 0 → io_d0.sideBit ≠ 0 →
        mbDst + (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
          io_d0.pgL.offDir)) := by
  have hw11 := h.hw11; have hb192 := h.base_fr; have hph9_inv := h.ph9_inv; have hsl_ge9 := h.sl_ge9
  dsimp only [dualMbDst, dualPDst, dualNHost, dualMbHost, dualPgHost] at hph9_inv hsl_ge9
  have hgrow_info := fgStep_ge9_grow h u v hsetup hs_prep_def hk_grow_def hge9_in
  have hsm_dst := hsetup.sm_dst
  have hgrow_low0 := hsetup.grow_low
  have hgrow_ge1920 := hsetup.grow_ge192
  have hibLo_ge := hsetup.ibLo_ge; have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  dsimp only at hgrow_info hsm_dst ⊢
  rw [← hs_prep_def] at hgrow_low0 hgrow_ge1920
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
  set uDone := s.mem (base + hdrUnpermDone)
  set vB := valBits V
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hgrow_low : ∀ off < 60, s_grow.mem (base + off) = s.mem (base + off) := hgrow_low0
  have hgrow_ge192 : ∀ addr, base + 192 ≤ addr → s_grow.mem addr = s.mem addr := hgrow_ge1920
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pDst := if ph < 10 then (if stg = 0 then p1 else p0) else p0
  set nHost := if nDst = 0 then nSrc else nDst
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
  set pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
  set mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  set L_mid := L.applyFG ph opTag u v
  set slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
  have hs_grow_ph : s_grow.mem (base + hdrPhase) = ph := hgrow_low hdrPhase (by decide)
  have hs_grow_stg : s_grow.mem (base + hdrStage) = stg := hgrow_low hdrStage (by decide)
  have hle7 : ¬(ph ≤ 7) := by omega
  have h8 : ph ≠ 8 := by omega
  have hge9 : 9 ≤ ph := by omega
  have hmbHost_192 : base + 192 ≤ mbHost := by dsimp only [mbHost]; split_ifs <;> omega
  obtain ⟨hcap_d, hdict_d, _, _⟩ := hsl_ge9 hge9
  set io_d0 := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive uDone
  set io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
  obtain ⟨hio_pos_d, hm_ib_d, hsl_grow, hti_ph9⟩ := hgrow_info
  have hcap_n_d : opTag = 1 → L.slotDst.s_abs u = none → L.slotDst.nCap ≠ 0 →
      (liveDom L.slotDst.s_abs).card < L.slotDst.nCap := fun _ hnone_d hne_c => by
    have hnone_s : s_dict u = none := by rw [← hdict_d]; simp [toDictState, hnone_d]
    have hcap := cap_lt_on_insert_none h hnone_s
    have hcard_eq : (liveDom L.slotDst.s_abs).card = nLive := by
      rw [← dom_toDictState_card, hdict_d]
    rw [hcard_eq]; rw [hcap_d] at hne_c ⊢
    exact hcap.2.2 (by omega) hne_c
  have hcap_io_d : opTag = 1 → L.slotDst.s_abs u = none →
      (liveDom L.slotDst.s_abs).card < io_dal.pgL.nCap ∧
      (io_dal.usePaged ≠ 0 →
        (extractPagePair io_dal.pgL s_grow.mem).totalItems + 1 ≤ io_dal.pgL.nCap) := by
    intro hop1 hnone_d
    have hnone_s : s_dict u = none := by rw [← hdict_d]; simp [toDictState, hnone_d]
    have hltU := (cap_lt_on_insert_none h hnone_s).1
    have hcard_eq : (liveDom L.slotDst.s_abs).card = nLive := by
      rw [← dom_toDictState_card, hdict_d]
    have hnc_al : io_dal.pgL.nCap = nAlloc := by
      dsimp only [io_dal, activeDstIo]; split_ifs <;> rfl
    rw [hnc_al, hcard_eq]
    dsimp only [nAlloc]; rw [ite_eq_left hop1, min_eq_left hltU]
    exact ⟨Nat.lt_succ_self _, fun hup => by rw [hti_ph9 hup]⟩
  have hmut := singleSlotMutate_raw hsl_grow u v hv_eq hcap_n_d hcap_io_d
  have hum_disp := userMutateRawProg_eval (opTag := opTag) (u_val := u.val) (v_val := v_val)
      s_grow hs_grow_ph hs_grow_stg
  have hp9_pDst : ph = 9 → pDst = (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) :=
    fun hp9 => by unfold pDst p0 p1; exact ite_eq_left (by omega : ph < 10)
  have hp10_pDst : ph ≠ 9 → pDst = base + hdrPBase0 :=
    fun hp9 => by unfold pDst p0; exact ite_eq_right (by omega : ¬(ph < 10))
  have hs_raw_prog :
      s_raw = (Memory.spec 0).clientState s_grow
        (if opTag = 1 then epochInsertProg ((pDst, u.val), v_val)
         else epochDeleteProg (pDst, u.val)) ∧
      memoryCost (userMutateRawProg ((base, opTag), (u.val, v_val))) s_grow =
        2 + memoryCost
          (if opTag = 1 then epochInsertProg ((pDst, u.val), v_val)
           else epochDeleteProg (pDst, u.val)) s_grow := by
    rw [hs_raw_def, hum_disp.1, hum_disp.2]; clear hs_raw_def
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, ite_eq_left hop1, ite_eq_right (by omega : ph ≠ 8)]
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9, hp9_pDst hp9]; exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hp9, ite_eq_left (by omega : 3 < ph),
          ite_eq_right (by omega : ¬(ph < 8)), hp10_pDst hp9]; exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hop1, ite_eq_right hop1, ite_eq_right (by omega : ph ≠ 8)]
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9, hp9_pDst hp9]; exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hp9, ite_eq_left (by omega : 3 < ph),
          ite_eq_right (by omega : ¬(ph < 8)), hp10_pDst hp9]; exact ⟨rfl, rfl⟩
  clear hs_raw_def
  have hs_raw_fr : s_raw.frontier = s_grow.frontier := by rw [hs_raw_prog.1]; exact hmut.2.1
  have hslk_eq : (if io_dal.usePaged = 0 ∨
      (extractPageUnperm io_dal.pgL s_grow.mem).cleanPhase = 0 then 0 else 24) =
      slackDst' := by
    dsimp only [slackDst']
    by_cases hp9 : ph = 9
    · by_cases hud0 : uDone = 0
      · have hio_eq : io_dal = pagedSlotIo 1 pgHost_al := by
          unfold io_dal activeDstIo
          rw [ite_eq_right (by omega : ¬(ph < 8)), ite_eq_right (by omega : ph ≠ 8),
            ite_eq_left hp9, ite_eq_left hud0]
        have hcp_gt := ((hph9_inv hp9).2.2.2 hud0).1
        have hu_eq_g : extractPageUnperm pgHost_al s_grow.mem =
            extractPageUnperm pgHost s.mem :=
          extractPageUnperm_host_congr hw11 hmbHost_192 hgrow_ge192
        rw [hio_eq]
        simp only [pagedSlotIo, hu_eq_g, hp9, hud0, one_ne_zero, false_or, true_and, ↓reduceIte,
          ite_eq_right_iff]
        intro hc0; omega
      · have hio_eq : io_dal = directSlotIo w vB base ibHi qHi nAlloc := by
          unfold io_dal activeDstIo
          rw [ite_eq_right (by omega : ¬(ph < 8)), ite_eq_right (by omega : ph ≠ 8),
            ite_eq_left hp9, ite_eq_right hud0]
        rw [hio_eq]
        simp only [directSlotIo, hud0, and_false, true_or, ↓reduceIte]
    · have hup0 : io_dal.usePaged = 0 := by
        unfold io_dal activeDstIo
        rw [ite_eq_right (by omega : ¬(ph < 8)), ite_eq_right (by omega : ph ≠ 8),
          ite_eq_right hp9]
        split_ifs <;> rfl
      rw [ite_eq_left (Or.inl hup0), ite_eq_right (fun h => hp9 h.2.1)]
  have hLmid_dst : L_mid.slotDst = L.slotDst.applyFG false opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_right hle7, ite_eq_right h8]
  have hsl_raw : EpochSlotInv c U V w s_raw.frontier pDst mbDst io_dal slackDst' false
      L_mid.slotDst s_raw.mem := by
    rw [hLmid_dst, hs_raw_prog.1, ← hslk_eq]; exact hmut.2.2.1
  have hdict'_d : toDictState L_mid.slotDst.s_abs = s_dict' := by
    rw [hLmid_dst, hmut.2.2.2.1, hdict_d]
  have hout_raw : ∀ addr, ¬slotOwnsAddr c w mbDst L.slotDst.nCap io_dal addr →
      s_raw.mem addr = s_grow.mem addr := by
    rw [hs_raw_prog.1]; exact hmut.2.2.2.2.1
  have hsp_raw : io_dal.usePaged = 0 → io_dal.sideBit ≠ 0 →
      s_raw.mem io_dal.pgL.metaBase = s_grow.mem io_dal.pgL.metaBase := fun hup hsb => by
    rw [hs_raw_prog.1]; exact (hmut.2.2.2.2.2.1 hup hsb).1
  have hns_m_eq : s_raw.mem (mbDst + 1) = nLive' := by
    rw [hsl_raw.mem_nSide_eq, ← dom_toDictState_card, hdict'_d]
  have hns_grow : s_grow.mem (mbDst + 1) = nLive := by
    rw [hsl_grow.mem_nSide_eq, ← dom_toDictState_card, hdict_d]
  refine ⟨⟨by dsimp only [s_grow]; omega, ?_⟩, hs_raw_fr, hsl_raw, hdict'_d, hout_raw, hsp_raw,
    fun hup hsb hhi => ?_, fun hup => ?_, fun hgc => ?_, hns_grow, hio_pos_d, hm_ib_d⟩
  · dsimp (config := { iota := false, proj := false }) only; rw [hs_grow_ph, hs_grow_stg]
    by_cases hop1 : opTag = 1
    · have hm1 := hmut.1; rw [ite_eq_left hop1] at hm1 ⊢
      rw [ite_eq_right (by omega : ph ≠ 8)]
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9, ← hp9_pDst hp9]; exact hm1
      · rw [ite_eq_right hp9, ite_eq_right (by omega : ¬(4 ≤ ph ∧ ph ≤ 7)), ← hp10_pDst hp9]
        exact hm1
    · have hm1 := hmut.1; rw [ite_eq_right hop1] at hm1 ⊢
      rw [ite_eq_right (by omega : ph ≠ 8)]
      by_cases hp9 : ph = 9
      · rw [ite_eq_left hp9, ← hp9_pDst hp9]; exact hm1
      · rw [ite_eq_right hp9, ite_eq_right (by omega : ¬(4 ≤ ph ∧ ph ≤ 7)), ← hp10_pDst hp9]
        exact hm1
  · have hh := (hmut.2.2.2.2.2.1 hup hsb).2 hhi
    rwa [← hs_raw_prog.1, hns_m_eq] at hh
  · have hp_s := hmut.2.2.2.2.2.2.1 hup
    rwa [← hs_raw_prog.1] at hp_s
  · rw [hs_raw_prog.2]
    have hc_raw := hmut.2.2.2.2.2.2.2 (hsm_dst (by omega)) (by rw [← hLmid_dst]; exact hgc)
    omega

private theorem fgStep_ge9_raw_lt48 {c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi
    nAlloc uDone nCapDst : ℕ} {m0 m_grow m_raw : ℕ → ℕ}
    (hge9 : 9 ≤ ph)
    (hibLo_192 : base + 192 ≤ ibLo)
    (hibHi_192 : base + 192 ≤ ibHi)
    (hcap_d : nCapDst = nDst)
    (hpos_d :
      let mbDst := if ph < 10 then
          (if nDst = 0 then base + hdrSmallMeta1
           else if stg = 0 then base + 192 + pad else base + 192)
        else
          (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
      (nCapDst = 0 ∧ (mbDst = base + hdrSmallMeta0 ∨ mbDst = base + hdrSmallMeta1)) ∨
      (nCapDst ≠ 0 ∧ base + 192 ≤ mbDst))
    (hgrow_below : ∀ addr < base, m_grow addr = m0 addr)
    (hgrow_low : ∀ off < 60, m_grow (base + off) = m0 (base + off))
    (hout_raw :
      let mbDst := if ph < 10 then
          (if nDst = 0 then base + hdrSmallMeta1
           else if stg = 0 then base + 192 + pad else base + 192)
        else
          (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
      let io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
      ∀ addr, ¬slotOwnsAddr c w mbDst nCapDst io_dal addr → m_raw addr = m_grow addr)
    (hsp_raw :
      let io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
      io_dal.usePaged = 0 → io_dal.sideBit ≠ 0 →
        m_raw io_dal.pgL.metaBase = m_grow io_dal.pgL.metaBase) :
    ∀ addr < base + 48, m_raw addr = m0 addr := by
  dsimp only at hpos_d hout_raw hsp_raw
  set pDst := if ph < 10 then (if stg = 0 then base + hdrPBase1 else base + hdrPBase0)
    else base + hdrPBase0
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  set io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
  have hmbHost_192 : base + 192 ≤ mbHost := by dsimp only [mbHost]; split_ifs <;> omega
  have howns_b := slotOwnsAddr_bounds
    (c := c) (w := w) (base := base) (pad := pad) (pBase := pDst)
    (metaBase := mbDst) (nCap := nCapDst) (io := io_dal)
    (fun h0 => by rcases hpos_d with ⟨_, h⟩ | ⟨hne, _⟩ <;> [exact h; exact absurd h0 hne])
    (fun hne => by
      rw [hcap_d] at hne; dsimp only [mbDst]
      split_ifs <;> first | exact Or.inr rfl | exact Or.inl rfl)
    (fun hup => by
      dsimp only [io_dal, activeDstIo] at hup ⊢
      split_ifs at hup ⊢ <;>
        (first
          | exact absurd rfl hup
          | omega
          | exact ⟨by dsimp only [pagedSlotIo, hostPageLayout, epochPageArenaLayout]; omega,
              hibHi_192⟩))
    (fun hup hsb => by
      dsimp only [io_dal, activeDstIo] at hup hsb ⊢
      split_ifs at hup hsb ⊢ <;>
        (first
          | exact absurd hup Nat.one_ne_zero
          | exact absurd rfl hsb
          | omega
          | exact ⟨rfl, hibLo_192, hibHi_192⟩))
    (fun hup hsb => by
      dsimp only [io_dal, activeDstIo] at hup hsb ⊢
      split_ifs at hup hsb ⊢ <;>
        (first | exact absurd hup Nat.one_ne_zero | exact hibHi_192 | exact hibLo_192))
  intro addr hlt48
  by_cases hsp_eq : addr = base + hdrSplit
  · subst hsp_eq
    by_cases hp10 : ph = 10
    · have hup10 : io_dal.usePaged = 0 := by
        dsimp only [io_dal, activeDstIo]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left hp10]
        rfl
      have hsp_pres := hsp_raw hup10
        (by dsimp only [io_dal, activeDstIo]
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_left hp10]; exact Nat.one_ne_zero)
      dsimp only [io_dal, activeDstIo] at hsp_pres
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left hp10] at hsp_pres
      dsimp only [splitSlotIo] at hsp_pres
      rw [hsp_pres]; exact hgrow_low hdrSplit (by decide)
    · rw [hout_raw (base + hdrSplit) (fun ha => by
        obtain ⟨_, h2, _⟩ := howns_b _ ha
        obtain ⟨_, hup, hsb⟩ := h2 (by unfold hdrSplit; omega)
        dsimp only [io_dal, activeDstIo] at hup hsb
        split_ifs at hup hsb <;>
          (first | exact absurd hup Nat.one_ne_zero | exact absurd rfl hsb))]
      exact hgrow_low hdrSplit (by decide)
  · rw [hout_raw addr (fun ha => hsp_eq ((howns_b addr ha).2.1 hlt48).1)]
    by_cases hge_b : base ≤ addr
    · have := hgrow_low (addr - base) (by omega)
      rwa [Nat.add_sub_of_le hge_b] at this
    · exact hgrow_below addr (by omega)

private theorem fgStep_ge9_raw_aux {c U V w base opTag v_val k_grow : ℕ}
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
    (hge9_in : 9 ≤ s.mem (base + hdrPhase)) :
    FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid := by
  have hw11 := h.hw11; have hUw := h.U_lt; have hb192 := h.base_fr; have hph_le := h.ph_le
  have hph9_inv := h.ph9_inv; have hph10_inv := h.ph10_inv; have hsl_ge9 := h.sl_ge9
  dsimp only [dualMbDst, dualPDst, dualNHost, dualMbHost, dualPgHost] at hph9_inv hsl_ge9
  have hraw9 := fgStep_ge9_raw_step h u v hv_eq hsetup hs_prep_def hk_grow_def hs_raw_def hge9_in
  have hcard_step := hsetup.card_step
  have hibLo_ge := hsetup.ibLo_ge; have hibHi_ge_ibLo := hsetup.ibHi_ge_ibLo
  have hpgHost_cap := hsetup.pgHost_cap
  have hmbDst_info := hsetup.mbDst_info; have hfr_n' := hsetup.fr_n'
  have hgrow_below0 := hsetup.grow_below
  have hgrow_low0 := hsetup.grow_low; have hgrow_ge1920 := hsetup.grow_ge192
  dsimp only [FGStepOutAux] at hraw9 hcard_step hpgHost_cap hmbDst_info hfr_n' ⊢
  rw [← hk_grow_def] at hfr_n'
  rw [← hs_prep_def] at hgrow_below0 hgrow_low0 hgrow_ge1920
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
  set sp := s.mem (base + hdrSplit)
  set uDone := s.mem (base + hdrUnpermDone)
  set vB := valBits V
  set nAlloc := if opTag = 1 then min (nLive + 1) U else nLive
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  have hgrow_low : ∀ off < 60, s_grow.mem (base + off) = s.mem (base + off) := hgrow_low0
  have hgrow_ge192 : ∀ addr, base + 192 ≤ addr → s_grow.mem addr = s.mem addr := hgrow_ge1920
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pDst := if ph < 10 then (if stg = 0 then p1 else p0) else p0
  set nHost := if nDst = 0 then nSrc else nDst
  set mbHost := if nDst = 0 then base + 192
    else if stg = 0 then base + 192 + pad else base + 192
  set pgHost := hostPageLayout c w nHost mbHost ibHi qHi vB nLive
  set pgHost_al := hostPageLayout c w nHost mbHost ibHi qHi vB nAlloc
  set pgHost_fin := hostPageLayout c w nHost mbHost ibHi qHi vB nLive'
  set mbDst := if ph < 10 then
      (if nDst = 0 then base + hdrSmallMeta1
       else if stg = 0 then base + 192 + pad else base + 192)
    else
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192)
  set L_mid := L.applyFG ph opTag u v
  set slackDst' := if true ∧ ph = 9 ∧ uDone = 0 then 24 else 0
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
  have hle7 : ¬(ph ≤ 7) := by omega
  have h8 : ph ≠ 8 := by omega
  have hge9 : 9 ≤ ph := by omega
  have hmbHost_192 : base + 192 ≤ mbHost := by dsimp only [mbHost]; split_ifs <;> omega
  obtain ⟨hcap_d, _, _, hlen_d⟩ := hsl_ge9 hge9
  obtain ⟨_, hpos_d, _, _⟩ := hmbDst_info (by omega)
  have hpDst_or : pDst = p0 ∨ pDst = p1 := by dsimp only [pDst]; split_ifs <;> simp
  have hp9_pDst : ph = 9 → pDst = (if stg = 0 then p1 else p0) :=
    fun hp9 => by unfold pDst; exact ite_eq_left (by omega : ph < 10)
  have hp10_pDst : ph ≠ 9 → pDst = p0 :=
    fun hp9 => by unfold pDst; exact ite_eq_right (by omega : ¬(ph < 10))
  set io_d0 := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive uDone
  set io_dal := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc uDone
  set io_dfin := activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive' uDone
  have hio_al_eq : io_dal = io_d0.withNCap nAlloc :=
    (activeDstIo_withNCap c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi
      nLive nAlloc uDone).symm
  have hibHi_192 : base + 192 ≤ ibHi := hibLo_ge.trans hibHi_ge_ibLo.1
  obtain ⟨hraw_pre, hs_raw_fr, hsl_raw, hdict'_d, hout_raw, hsp_raw, hhi_pres, hp_step_fn,
    hmc_raw9, hns_grow, hio_pos_d, hm_ib_d⟩ := hraw9
  have hs_raw_lt48 := fgStep_ge9_raw_lt48 hge9 hibLo_ge hibHi_192 hcap_d hpos_d hgrow_below0
    hgrow_low hout_raw hsp_raw
  have hLmid_dst : L_mid.slotDst = L.slotDst.applyFG false opTag u v := by
    dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_right hle7, ite_eq_right h8]
  have hsync_ev := syncLiveCountsProg_eval (base := base) s_raw
  have hs_raw_ph : s_raw.mem (base + hdrPhase) = ph :=
    hs_raw_lt48 (base + hdrPhase) (by unfold hdrPhase; omega)
  have hs_raw_stg : s_raw.mem (base + hdrStage) = stg :=
    hs_raw_lt48 (base + hdrStage) (by unfold hdrStage; omega)
  have hns_raw_eq :
      (Memory.spec 0).clientResult s_raw (epochReadNSideProg pDst) = nLive' := by
    rw [hsl_raw.readNSide_eq, ← dom_toDictState_card, hdict'_d]
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
    rw [hs_raw_ph, hs_raw_stg, ite_eq_right (by omega : ph ≠ 8)]
    by_cases hp9 : ph = 9
    · rw [ite_eq_left hp9, ← hp9_pDst hp9]; exact hns_raw_eq
    · rw [ite_eq_right hp9, ite_eq_right (by omega : ¬(4 ≤ ph ∧ ph ≤ 7)), ← hp10_pDst hp9]
      exact hns_raw_eq
  set m3 := Function.update
    (Function.update (Function.update s_raw.mem (base + hdrLive) nLive') (p0 + 60) nLive')
    (p1 + 60) nLive'
  have hs_mid_fr : s_mid.frontier = s_grow.frontier := by
    rw [hs_mid_eq, hsync_ev.1]; exact hs_raw_fr
  have hns_m_eq : s_raw.mem (mbDst + 1) = nLive' := by
    rw [hsl_raw.mem_nSide_eq, ← dom_toDictState_card, hdict'_d]
  have hti_raw9 : io_dal.usePaged ≠ 0 →
      (extractPagePair io_dal.pgL s_raw.mem).totalItems = nLive' := by
    intro hup
    have hp9_ud : ph = 9 ∧ uDone = 0 := by
      dsimp only [io_dal, activeDstIo] at hup
      split_ifs at hup <;> first | exact absurd rfl hup | omega
    have hcp_gt := ((hph9_inv hp9_ud.1).2.2.2 hp9_ud.2).1
    have hcp_lt := ((hph9_inv hp9_ud.1).2.2.2 hp9_ud.2).2.1
    have hpg_eq_d : io_dal.pgL = pgHost_al ∧ io_dal.side = true := by
      dsimp only [io_dal, activeDstIo]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp9_ud.1,
        ite_eq_left hp9_ud.2]
      exact ⟨rfl, rfl⟩
    have hu_eq_g : extractPageUnperm pgHost_al s_grow.mem = extractPageUnperm pgHost s.mem :=
      extractPageUnperm_host_congr hw11 hmbHost_192 hgrow_ge192
    have hp_step := hp_step_fn hup
    have hcp_raw_gt : 0 < (extractPageUnperm io_dal.pgL s_raw.mem).cleanPhase := by
      refine (hp_step.2 hpg_eq_d.2 ?_ ?_).1
      · rw [hpg_eq_d.1, hu_eq_g]; exact hcp_gt
      · rw [hpg_eq_d.1, hu_eq_g]; exact hcp_lt
    have hio_r := hsl_raw.io_stateInv
    unfold SlotIoLayout.StateInv at hio_r; rw [ite_eq_right hup] at hio_r
    have hvl_f0 : (extractPagePair io_dal.pgL s_raw.mem).virtLen false = 0 :=
      virtLen_false_zero_of_cleanPhase hio_r.1 hcp_raw_gt
    have hvl_t : (extractPagePair io_dal.pgL s_raw.mem).virtLen true = nLive' := by
      have hvt : (extractPagePair io_dal.pgL s_raw.mem).virtLen io_dal.side =
          s_raw.mem (mbDst + 1) := hio_r.2.2.2.2.1
      rw [hpg_eq_d.2, hns_m_eq] at hvt
      exact hvt
    unfold PagePairState.totalItems; omega
  have hsl_m3 : EpochSlotInv c U V w s_mid.frontier pDst mbDst io_dfin slackDst' false
      L_mid.slotDst m3 := by
    have hio_eq : io_dal.withNCap nLive' = io_dfin :=
      activeDstIo_withNCap c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nAlloc
        nLive' uDone
    rw [← hio_eq]
    refine EpochSlotInv.lift_sync (base := base)
      (by rw [hs_mid_fr]; dsimp only [s_grow]; rw [← hs_raw_fr]; exact hsl_raw) le_rfl
      (lt_of_le_of_lt hcard_step.2.2.2.2.2.1 hUw) hpDst_or
      (by rw [hLmid_dst, SlotLatent.applyFG_nCap]; exact hpos_d)
      (by rw [hio_al_eq]; exact hio_pos_d)
      (fun hup hsb => by
        rw [hs_mid_fr]
        dsimp only [io_dal, activeDstIo] at hup hsb ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hup hsb ⊢
        by_cases hp9 : ph = 9
        · rw [ite_eq_left hp9] at hup hsb ⊢
          by_cases hud0 : uDone = 0
          · rw [ite_eq_left hud0] at hup; exact absurd hup Nat.one_ne_zero
          · rw [ite_eq_right hud0]; exact hfr_n'.2 ⟨by omega, by omega⟩
        · rw [ite_eq_right hp9] at hup hsb ⊢
          by_cases hp10 : ph = 10
          · rw [ite_eq_left hp10] at hsb; dsimp only [splitSlotIo] at hsb; omega
          · rw [ite_eq_right hp10]; exact hfr_n'.1 (Or.inr (by omega)))
      (fun hup hsb => by
        rw [hs_mid_fr]
        dsimp only [io_dal, activeDstIo] at hup hsb ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hup hsb ⊢
        by_cases hp9 : ph = 9
        · rw [ite_eq_left hp9] at hup hsb
          by_cases hud0 : uDone = 0
          · rw [ite_eq_left hud0] at hup; exact absurd hup Nat.one_ne_zero
          · rw [ite_eq_right hud0] at hsb; exact absurd rfl hsb
        · rw [ite_eq_right hp9] at hsb ⊢
          by_cases hp10 : ph = 10
          · rw [ite_eq_left hp10]; exact hfr_n'.2 ⟨by omega, by omega⟩
          · rw [ite_eq_right hp10] at hsb; exact absurd rfl hsb)
      (fun hup => by
        rw [hs_mid_fr]
        dsimp only [io_dal, activeDstIo] at hup ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega)] at hup ⊢
        by_cases hp9 : ph = 9
        · rw [ite_eq_left hp9] at hup ⊢
          by_cases hud0 : uDone = 0
          · rw [ite_eq_left hud0]
            exact ⟨(hpgHost_cap (by omega) (by omega)).2,
              hfr_n'.2 ⟨by omega, by omega⟩⟩
          · rw [ite_eq_right hud0] at hup; exact absurd rfl hup
        · rw [ite_eq_right hp9] at hup
          split_ifs at hup <;> exact absurd rfl hup)
      (by rw [hLmid_dst, SlotLatent.applyFG_nCap, hio_al_eq]; exact hm_ib_d)
      hns_m_eq.le (fun hup => (hti_raw9 hup).le)
      (by dsimp only [m3]
          rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] <;>
            dsimp only [p0, p1, hdrPBase0, hdrPBase1]
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [Function.update_self])
      (fun a ha1 ha2 hne => by
        dsimp only [m3]
        rcases hpDst_or with hp_e | hp_e <;> rw [hp_e] at ha1 ha2 hne <;>
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
      if ph = 10 ∧ nLive' < sp then Function.update m3 (base + hdrSplit) nLive' else m3 := by
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
    have hn3 : ph ≠ 3 := by omega
    by_cases hp10 : ph = 10
    · simp only [hp10, or_true, true_and]
    · simp only [hn3, hp10, or_self, false_and, ↓reduceIte]
  have hsl_and_sp := fgStep_ge9_ph10 hge9 hcard_step.2.2.2.2.1 hph10_inv hibLo_ge hibHi_192
    (hgrow_low hdrSplit (by decide)) hgrow_ge192 hns_grow hpDst_or
    (by rw [hLmid_dst, SlotLatent.applyFG_nCap]; exact hpos_d)
    (hs_raw_lt48 (base + hdrSplit) (by unfold hdrSplit; omega)) hns_m_eq hhi_pres
    hsl_m3 hs_mid_mem
  refine ⟨⟨hraw_pre,
      hsync_pre_eq.mpr ⟨by rw [hs_raw_fr]; omega, ?_⟩⟩,
    hs_mid_fr, ?_, ?_, ?_, ?_, fun h => absurd h (by omega),
    fun h => absurd h (by omega), fun h => absurd h (by rcases h with h | h <;> omega),
    ?_, fun h => absurd h (by omega), fun h => absurd h (by omega),
    fun _ => ?_, fun _ _ hgc_d => ?_⟩
  · dsimp (config := { iota := false, proj := false }) only
    rw [hs_raw_ph, hs_raw_stg, ite_eq_right (by omega : ph ≠ 8)]
    by_cases hp9 : ph = 9
    · have hm_pre : EpochProgPre w (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) s_raw :=
        hp9_pDst hp9 ▸ hsl_raw.epochProgPre
      rw [ite_eq_left hp9]; exact hm_pre
    · have hp10_raw : pDst = base + hdrPBase0 := hp10_pDst hp9
      have hm_pre : EpochProgPre w (base + hdrPBase0) s_raw :=
        hp10_raw ▸ hsl_raw.epochProgPre
      rw [ite_eq_right hp9, ite_eq_right (by omega : ¬(4 ≤ ph ∧ ph ≤ 7))]; exact hm_pre
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
  · intro _ hn10
    rw [hs_mid_mem, ite_eq_right (fun h => hn10 h.1), hm3_sp]
  · rintro (hp3 | hp10)
    · omega
    · exact hsl_and_sp.2 hp10
  · intro hp9 hud0
    obtain ⟨hcp_gt, hcp_lt, hrk_le, _⟩ := (hph9_inv hp9).2.2.2 hud0
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hrk_le
    have hup9 : io_dal.usePaged ≠ 0 ∧ io_dal.pgL = pgHost_al ∧ io_dal.side = true := by
      dsimp only [io_dal, activeDstIo]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp9, ite_eq_left hud0]
      exact ⟨Nat.one_ne_zero, rfl, rfl⟩
    have hu_eq_g : extractPageUnperm pgHost_al s_grow.mem = extractPageUnperm pgHost s.mem :=
      extractPageUnperm_host_congr hw11 hmbHost_192 hgrow_ge192
    have hu_eq_m : extractPageUnperm pgHost_fin s_mid.mem =
        extractPageUnperm pgHost_al s_raw.mem := by
      rw [hs_mid_mem, ite_eq_right (by omega : ¬(ph = 10 ∧ nLive' < sp))]
      exact extractPageUnperm_host_congr hw11 hmbHost_192 fun a h192 => by
        dsimp only [m3]; unfold p0 p1 hdrPBase0 hdrPBase1 hdrLive
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
    have hp_st := (hp_step_fn hup9.1).2 hup9.2.2
    rw [hup9.2.1, hu_eq_g] at hp_st
    obtain ⟨h1, h2, h3⟩ := hp_st hcp_gt hcp_lt
    rw [hu_eq_m]
    exact ⟨h1, h2, by omega⟩
  · refine ⟨by rw [hLmid_dst, SlotLatent.applyFG_nCap]; exact hcap_d,
      hdict'_d, hsl_and_sp.1, fun hd_pos => ?_⟩
    have hl0 := hlen_d hd_pos
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl0
    rw [hLmid_dst]; unfold SlotLatent.applyFG
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
      omega
    · rw [ite_eq_right hop1]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_singleton]
      omega
  · rw [hmc_um_eq]
    have hc_raw := hmc_raw9 (hgc_d hge9)
    have hc_sync := hsync_ev.2
    omega

/-- Auxiliary opaque-state version of `fgStep_ge9`. -/
theorem fgStep_ge9_aux {c U V w base opTag v_val k_grow : ℕ}
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
    (hge9_in : 9 ≤ s.mem (base + hdrPhase)) :
    FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid :=
  fgStep_ge9_raw_aux h u v hv_eq hsetup hs_prep_def hk_grow_def rfl hs_mid_def hge9_in

/-- Proves `FGStepOut` in Phase `8` (`migrate`). -/
theorem fgStep_eq8 {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (h8 : s.mem (base + hdrPhase) = 8) :
    FGStepOut c U V w base opTag v_val u v s_dict L s :=
  fgStep_eq8_aux h u v hv_eq hsetup rfl rfl rfl h8

/-- Proves `FGStepOut` in Phases `9..11`. -/
theorem fgStep_ge9 {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hge9_in : 9 ≤ s.mem (base + hdrPhase)) :
    FGStepOut c U V w base opTag v_val u v s_dict L s :=
  fgStep_ge9_aux h u v hv_eq hsetup rfl rfl rfl hge9_in

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

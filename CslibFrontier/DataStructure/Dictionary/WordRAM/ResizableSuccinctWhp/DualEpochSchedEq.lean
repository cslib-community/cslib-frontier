/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInv
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Global Schedule Determinism (`DualEpochSchedEq`)

This module establishes the global schedule-determinism relation (`SchedEq`) across all 12 phases
(`0..11`) of `DualEpochInv`: every foreground operation, background tick, and post-shrink step
preserves equality of `frontier` and root header words `[0..47] \ {hdrUnpermDone}` across all
states in the distribution's support, keeping `k_grow`, `rArgs`, `k_sh`, and phase transitions
deterministic.

## Main definitions

* `SchedEq`: agreement on `frontier` and root header offsets `[0..47] \ {hdrUnpermDone}`.

## Main results

* `schedEq_foreground`, `schedEq_mutate_step`

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
open Cslib.DataStructure.HashFamily Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.Probability
open EpochUpdate
open scoped ENNReal

/-! ## Global Deterministic Schedule Congruence (`SchedEq`) -/

/-- Two `Memory.State`s share the exact deterministic schedule state at `base` when they have the
same `frontier` and identical root header words `[0..47]` apart from `hdrUnpermDone = 28` (which
records whether a particular seed's Phase-`9` unpermutation finished early, without affecting
`finishUnpermProg` or `rem`). -/
@[expose] def SchedEq (base : ℕ) (s₁ s₂ : Memory.State) : Prop :=
  s₁.frontier = s₂.frontier ∧
  ∀ off < 48, off ≠ hdrUnpermDone → s₁.mem (base + off) = s₂.mem (base + off)

theorem SchedEq.refl (base : ℕ) (s : Memory.State) : SchedEq base s s :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem SchedEq.symm {base : ℕ} {s₁ s₂ : Memory.State} (h : SchedEq base s₁ s₂) :
    SchedEq base s₂ s₁ :=
  ⟨h.1.symm, fun off hoff hne => (h.2 off hoff hne).symm⟩

theorem SchedEq.trans {base : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h₁ : SchedEq base s₁ s₂) (h₂ : SchedEq base s₂ s₃) :
    SchedEq base s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, fun off hoff hne => (h₁.2 off hoff hne).trans (h₂.2 off hoff hne)⟩

theorem SchedEq.capSrc_eq {base : ℕ} {s₁ s₂ : Memory.State} (h : SchedEq base s₁ s₂) :
    dualCapSrc base s₁.mem = dualCapSrc base s₂.mem := by
  unfold dualCapSrc
  rw [h.2 hdrStage (by decide) (by decide), h.2 hdrNSrc (by decide) (by decide),
    h.2 hdrNDst (by decide) (by decide)]

theorem SchedEq.mbDst_eq {base : ℕ} {s₁ s₂ : Memory.State} (h : SchedEq base s₁ s₂) :
    dualMbDst base s₁.mem = dualMbDst base s₂.mem := by
  unfold dualMbDst
  rw [h.2 hdrPhase (by decide) (by decide), h.2 hdrNDst (by decide) (by decide),
    h.2 hdrStage (by decide) (by decide), h.2 hdrPad (by decide) (by decide)]

theorem SchedEq.pDst_eq {base : ℕ} {s₁ s₂ : Memory.State} (h : SchedEq base s₁ s₂) :
    dualPDst base s₁.mem = dualPDst base s₂.mem := by
  unfold dualPDst
  rw [h.2 hdrPhase (by decide) (by decide), h.2 hdrStage (by decide) (by decide)]

theorem SchedEq.pSrc_eq {base : ℕ} {s₁ s₂ : Memory.State} (h : SchedEq base s₁ s₂) :
    dualPSrc base s₁.mem = dualPSrc base s₂.mem := by
  unfold dualPSrc; rw [h.2 hdrStage (by decide) (by decide)]

theorem SchedEq.mbSrc_eq {base : ℕ} {s₁ s₂ : Memory.State} (h : SchedEq base s₁ s₂) :
    dualMbSrc base s₁.mem = dualMbSrc base s₂.mem := by
  unfold dualMbSrc
  rw [h.2 hdrStage (by decide) (by decide), h.2 hdrNSrc (by decide) (by decide),
    h.2 hdrPad (by decide) (by decide)]

theorem SchedEq.pgHost_eq {c V w base nc : ℕ} {s₁ s₂ : Memory.State} (h : SchedEq base s₁ s₂) :
    dualPgHost c V w base nc s₁.mem = dualPgHost c V w base nc s₂.mem := by
  unfold dualPgHost dualNHost dualMbHost
  rw [h.2 hdrNDst (by decide) (by decide), h.2 hdrNSrc (by decide) (by decide),
    h.2 hdrStage (by decide) (by decide), h.2 hdrPad (by decide) (by decide),
    h.2 hdrItemHi (by decide) (by decide), h.2 hdrQHi (by decide) (by decide)]

private theorem userMutate_hdrSplit_slide {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hslide : s.mem (base + hdrPhase) = 3 ∨ s.mem (base + hdrPhase) = 10) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_mid := (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
    s_mid.mem (base + hdrSplit) =
      if nLive' < s.mem (base + hdrSplit) then nLive' else s.mem (base + hdrSplit) := by
  dsimp only
  have hsetup := fgSetup_of_dualStateInv h hop_nz u v
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val)
    else Function.update s_dict u none
  set nLive := (Dictionary.dom s_dict).card
  set nLive' := (Dictionary.dom s_dict').card
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
  obtain ⟨s_prep, hs_prep_def⟩ : ∃ sp_s,
      (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)) = sp_s :=
    ⟨_, rfl⟩
  obtain ⟨k_grow, hk_grow_def⟩ : ∃ kg,
      (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)) = kg :=
    ⟨_, rfl⟩
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  obtain ⟨s_raw, hs_raw_def⟩ : ∃ sr,
      (Memory.spec 0).clientState s_grow (userMutateRawProg ((base, opTag), (u.val, v_val))) = sr :=
    ⟨_, rfl⟩
  obtain ⟨s_mid, hs_mid_def⟩ : ∃ sm,
      (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val))) = sm :=
    ⟨_, rfl⟩
  rw [hs_prep_def, hk_grow_def]
  change ((Memory.spec 0).clientState s_grow
    (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrSplit) = _
  rw [hs_mid_def]
  have hstep_all : FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid := by
    rcases hslide with hp3 | hp10
    · exact fgStep_le7_aux h u v hv_eq hsetup hs_prep_def.symm hk_grow_def.symm hs_mid_def.symm
        (by clear *- hp3; omega)
    · exact fgStep_ge9_aux h u v hv_eq hsetup hs_prep_def.symm hk_grow_def.symm hs_mid_def.symm
        (by clear *- hp10; omega)
  have hs_mid_live : s_mid.mem (base + hdrLive) = nLive' := hstep_all.2.2.1
  have hgrow_low : ∀ off < 60, s_grow.mem (base + off) = s.mem (base + off) := by
    have hg := hsetup.grow_low; dsimp only at hg; rwa [hs_prep_def] at hg
  have hs_grow_ph : s_grow.mem (base + hdrPhase) = ph := hgrow_low hdrPhase (by decide)
  have hs_grow_stg : s_grow.mem (base + hdrStage) = stg := hgrow_low hdrStage (by decide)
  have hdisp := (userMutateRawProg_eval (opTag := opTag) (u_val := u.val) (v_val := v_val)
    s_grow hs_grow_ph hs_grow_stg).1
  have hp0_act :
      (if opTag = 1 then
         if ph = 8 then
           epochDeleteProg (if stg = 0 then base + hdrPBase0 else base + hdrPBase1, u.val) >>=
             fun _ => epochInsertProg
               ((if stg = 0 then base + hdrPBase1 else base + hdrPBase0, u.val), v_val)
         else if ph = 9 then
           epochInsertProg ((if stg = 0 then base + hdrPBase1 else base + hdrPBase0, u.val), v_val)
         else if 3 < ph then
           if ph < 8 then
             epochInsertProg
               ((if stg = 0 then base + hdrPBase0 else base + hdrPBase1, u.val), v_val)
           else epochInsertProg ((base + hdrPBase0, u.val), v_val)
         else epochInsertProg ((base + hdrPBase0, u.val), v_val)
       else
         if ph = 8 then
           epochDeleteProg (if stg = 0 then base + hdrPBase0 else base + hdrPBase1, u.val) >>=
             fun _ => epochDeleteProg
               (if stg = 0 then base + hdrPBase1 else base + hdrPBase0, u.val)
         else if ph = 9 then
           epochDeleteProg (if stg = 0 then base + hdrPBase1 else base + hdrPBase0, u.val)
         else if 3 < ph then
           if ph < 8 then
             epochDeleteProg (if stg = 0 then base + hdrPBase0 else base + hdrPBase1, u.val)
           else epochDeleteProg (base + hdrPBase0, u.val)
         else epochDeleteProg (base + hdrPBase0, u.val)) =
      (if opTag = 1 then epochInsertProg ((base + hdrPBase0, u.val), v_val)
       else epochDeleteProg (base + hdrPBase0, u.val)) := by
    rcases hslide with hp3 | hp10
    · by_cases hop1 : opTag = 1 <;> simp [hop1, hp3]
    · by_cases hop1 : opTag = 1 <;> simp [hop1, hp10]
  rw [hp0_act] at hdisp
  set io_al := splitSlotIo w vB base ibLo qLo ibHi qHi nAlloc
  -- Certify `EpochSlotInv` on `(base + hdrPBase0)` with `io_al` at `s_grow`
  have hslot_grow : ∃ (mb : ℕ) (sl : SlotLatent c U V),
      base + 48 ≤ mb ∧
      toDictState sl.s_abs = s_dict ∧
      (sl.nCap = if ph = 3 then dualCapSrc base s.mem else nDst) ∧
      EpochSlotInv c U V w s_grow.frontier (base + hdrPBase0) mb io_al 0 false sl s_grow.mem := by
    have hlift := @FGSetup.lift_grow_slot c U V w base opTag u v s_dict L s hsetup
    dsimp only at hlift
    rw [hs_prep_def, hk_grow_def] at hlift
    have hibLo_ge := hsetup.ibLo_ge
    have hibHi_ge := hibLo_ge.trans hsetup.ibHi_ge_ibLo.1
    have hfr_b := hsetup.fr_bounds; dsimp only at hfr_b; rw [hk_grow_def] at hfr_b
    set io_0 := splitSlotIo w vB base ibLo qLo ibHi qHi nLive
    have hwith : io_0.withNCap nAlloc = io_al := rfl
    rcases hslide with hp3 | hp10
    · have hsched := h.sched; rw [ite_eq_right (by clear *- hp3; omega)] at hsched
      have hst0 : stg = 0 := by
        have hs_le := h.stg_le
        by_cases h1 : stg = 1
        · have h4 := (hsched.stg_one h1).2.1; clear *- hp3 h4; omega
        · clear *- hs_le h1; omega
      obtain ⟨hcap_s, hdict_s, hsl_s, _⟩ := h.sl_le7 (by clear *- hp3; omega)
      have hpS0 : dualPSrc base s.mem = base + hdrPBase0 := by
        unfold dualPSrc; exact ite_eq_left hst0
      have hio_s : activeSrcIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive = io_0 := by
        unfold activeSrcIo; rw [hp3]; simp only [Nat.reduceLT, ↓reduceIte]; rfl
      rw [hpS0, hio_s] at hsl_s
      obtain ⟨_, hpos_s, hm_lo_s, hm_hi_s⟩ := hsetup.mbSrc_info (by clear *- hp3; omega)
      have hmb_ge : base + 48 ≤ dualMbSrc base s.mem := by
        unfold dualMbSrc; dsimp only [hdrSmallMeta0]; split_ifs <;> omega
      have hmbS_eq : dualMbSrc base s.mem =
          (if stg = 0 then if nSrc = 0 then base + hdrSmallMeta0 else base + 192
           else base + 192 + pad) := rfl
      refine ⟨dualMbSrc base s.mem, L.slotSrc, hmb_ge, hdict_s,
        by rw [ite_eq_left hp3]; exact hcap_s, ?_⟩
      rw [← hwith, hmbS_eq]
      exact hlift hsl_s rfl (Or.inl rfl) hpos_s
        ⟨fun _ _ => ⟨rfl, hibLo_ge⟩, fun hup => absurd rfl hup, hibHi_ge⟩
        (fun _ hsb => absurd hsb Nat.one_ne_zero)
        (fun _ _ => hfr_b.2.2.2.1 ⟨by clear *- hp3; omega, by clear *- hp3; omega⟩)
        (fun hup => absurd rfl hup)
        ⟨hm_hi_s (by clear *- hp3; omega), fun _ _ => hm_lo_s (by clear *- hp3; omega)⟩
    · obtain ⟨hcap_d, hdict_d, hsl_d, _⟩ := h.sl_ge9 (by clear *- hp10; omega)
      have hpD0 : dualPDst base s.mem = base + hdrPBase0 := by
        unfold dualPDst
        change (if ph < 10 then _ else _) = _
        rw [hp10, ite_eq_right (by decide : ¬(10 < 10))]
      have hio_d : activeDstIo c w vB base stg ph nSrc nDst pad ibLo qLo ibHi qHi nLive
          (s.mem (base + hdrUnpermDone)) = io_0 := by
        unfold activeDstIo; rw [hp10]; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
      have hslk0 : (if false ∧ ph = 9 ∧ s.mem (base + hdrUnpermDone) = 0 then 24 else 0) = 0 := rfl
      rw [hpD0, hio_d, hslk0] at hsl_d
      obtain ⟨_, hpos_d, hm_hi_d, hm_lo_d⟩ := hsetup.mbDst_info (by clear *- hp10; omega)
      have hmb_ge : base + 48 ≤ dualMbDst base s.mem := by
        unfold dualMbDst; dsimp only [hdrSmallMeta0, hdrSmallMeta1]; split_ifs <;> omega
      have hmbD_eq : dualMbDst base s.mem =
          (if ph < 10 then
             if nDst = 0 then base + hdrSmallMeta1
             else if stg = 0 then base + 192 + pad else base + 192
           else if nDst = 0 then base + hdrSmallMeta0 else base + 192) := rfl
      refine ⟨dualMbDst base s.mem, L.slotDst, hmb_ge, hdict_d,
        by rw [ite_eq_right (by clear *- hp10; omega)]; exact hcap_d, ?_⟩
      rw [← hwith, hmbD_eq]
      exact hlift hsl_d rfl (Or.inl rfl) hpos_d
        ⟨fun _ _ => ⟨rfl, hibLo_ge⟩, fun hup => absurd rfl hup, hibHi_ge⟩
        (fun _ hsb => absurd hsb Nat.one_ne_zero)
        (fun _ _ => hfr_b.2.2.2.1 ⟨by clear *- hp10; omega, by clear *- hp10; omega⟩)
        (fun hup => absurd rfl hup)
        ⟨hm_hi_d (by clear *- hp10; omega), fun _ _ => hm_lo_d (by clear *- hp10; omega)⟩
  obtain ⟨mb0, sl0, hmb_ge48, hdict0, hcap0, hsl_g⟩ := hslot_grow
  have hcap_ins : opTag = 1 →
      (sl0.s_abs u = none → sl0.nCap ≠ 0 → (liveDom sl0.s_abs).card < sl0.nCap) ∧
      (sl0.s_abs u = none →
        (liveDom sl0.s_abs).card < io_al.pgL.nCap ∧
        (io_al.usePaged ≠ 0 →
          (extractPagePair io_al.pgL s_grow.mem).totalItems + 1 ≤ io_al.pgL.nCap)) :=
    fun hop1 => by
      refine ⟨fun hnone hne_c => ?_, fun hnone => ?_⟩
      · have hsd_n : s_dict u = none := by rw [← hdict0]; simp [toDictState, hnone]
        have hc_lt := cap_lt_on_insert_none h hsd_n
        have hcd_eq : (liveDom sl0.s_abs).card = nLive := by
          rw [← dom_toDictState_card (V := V), hdict0]
        rw [hcd_eq]
        rcases hslide with hp3 | hp10
        · have hst0 : stg = 0 := by
            have hs_le := h.stg_le
            by_cases h1 : stg = 1
            · have hsched := h.sched; rw [ite_eq_right (by clear *- hp3; omega)] at hsched
              have h4 := (hsched.stg_one h1).2.1; clear *- hp3 h4; omega
            · clear *- hs_le h1; omega
          have hcs_eq : dualCapSrc base s.mem = nSrc := by unfold dualCapSrc; exact ite_eq_left hst0
          rw [hcap0, ite_eq_left hp3, hcs_eq] at hne_c ⊢
          exact hc_lt.2.1 hne_c
        · rw [hcap0, ite_eq_right (by clear *- hp10; omega)] at hne_c ⊢
          exact hc_lt.2.2 (by clear *- hp10; omega) hne_c
      · have hsd_n : s_dict u = none := by rw [← hdict0]; simp [toDictState, hnone]
        have hc_lt := cap_lt_on_insert_none h hsd_n
        have hcd_eq : (liveDom sl0.s_abs).card = nLive := by
          rw [← dom_toDictState_card (V := V), hdict0]
        dsimp only [io_al, splitSlotIo, nAlloc]
        rw [hcd_eq, ite_eq_left hop1, min_eq_left hc_lt.1]
        exact ⟨Nat.lt_succ_self _, fun hup => absurd rfl hup⟩
  have hs_raw_sp : s_raw.mem (base + hdrSplit) = s.mem (base + hdrSplit) := by
    have hgrow_sp : s_grow.mem (base + hdrSplit) = s.mem (base + hdrSplit) :=
      hgrow_low hdrSplit (by decide)
    rw [← hs_raw_def, hdisp]
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, hv_eq hop1]
      obtain ⟨hcap_n, hcap_io⟩ := hcap_ins hop1
      have hins_sp := ((hsl_g.insert_spec u v hcap_n hcap_io).2.2.2.1 rfl Nat.one_ne_zero).1
      dsimp only [io_al, splitSlotIo] at hins_sp
      exact hins_sp.trans hgrow_sp
    · rw [ite_eq_right hop1]
      have hdel_sp := ((hsl_g.delete_spec u).2.2.2.1 rfl Nat.one_ne_zero).1
      dsimp only [io_al, splitSlotIo] at hdel_sp
      exact hdel_sp.trans hgrow_sp
  have hs_raw_ph : s_raw.mem (base + hdrPhase) = ph := by
    have hnot : ¬slotOwnsAddr c w mb0 sl0.nCap io_al (base + hdrPhase) := by
      unfold slotOwnsAddr
      have hibLo_ge := hsetup.ibLo_ge
      have hibHi_ge := hibLo_ge.trans hsetup.ibHi_ge_ibLo.1
      by_cases h0 : sl0.nCap = 0
      · rw [ite_eq_left h0]
        simp only [SmallEpochLayout.OwnsAddr, io_al, splitSlotIo, SlotIoLayout.OwnsAddr,
          one_ne_zero, ↓reduceIte]
        dsimp only [hdrPhase, hdrSplit]; omega
      · rw [ite_eq_right h0]
        simp only [FastEpochLayout.OwnsFastAddr, io_al, splitSlotIo, SlotIoLayout.OwnsAddr,
          one_ne_zero, ↓reduceIte]
        dsimp only [hdrPhase, hdrSplit]; omega
    rw [← hs_raw_def, hdisp]
    by_cases hop1 : opTag = 1
    · rw [ite_eq_left hop1, hv_eq hop1]
      obtain ⟨hcap_n, hcap_io⟩ := hcap_ins hop1
      exact ((hsl_g.insert_spec u v hcap_n hcap_io).2.2.1 _ hnot).trans hs_grow_ph
    · rw [ite_eq_right hop1]
      exact ((hsl_g.delete_spec u).2.2.1 _ hnot).trans hs_grow_ph
  have hs_mid_sync : s_mid = (Memory.spec 0).clientState s_raw (syncLiveCountsProg base) := by
    rw [← hs_mid_def, ← hs_raw_def]
    exact (userMutateProg_eval base opTag u.val v_val s_grow).1
  have hsync := (syncLiveCountsProg_eval (base := base) s_raw).1
  dsimp only at hsync
  rw [hs_mid_sync, hsync] at hs_mid_live ⊢
  dsimp only at hs_mid_live ⊢
  -- Evaluate `hs_mid_live` at `base + hdrLive` to identify `syncLiveCountsProg`'s `nLive'`!
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
  have hm3_live : m3 (base + hdrLive) = nL_sync := by
    dsimp only [m3]; unfold hdrPBase0 hdrPBase1 hdrLive
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hm3_sp : m3 (base + hdrSplit) = s.mem (base + hdrSplit) := by
    dsimp only [m3]; unfold hdrPBase0 hdrPBase1 hdrLive hdrSplit
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hs_raw_sp
  have hnL_eq : nL_sync = nLive' := by
    rw [← hm3_live]
    by_cases hc : (s_raw.mem (base + hdrPhase) = 3 ∨ s_raw.mem (base + hdrPhase) = 10) ∧
        nL_sync < m3 (base + hdrSplit)
    · rw [ite_eq_left hc, Function.update_of_ne (by unfold hdrLive hdrSplit; omega)] at hs_mid_live
      exact hs_mid_live
    · rw [ite_eq_right hc] at hs_mid_live; exact hs_mid_live
  rw [hs_raw_ph, hm3_sp, hnL_eq]
  by_cases hlt : nLive' < s.mem (base + hdrSplit)
  · rw [ite_eq_left ⟨hslide, hlt⟩, ite_eq_left hlt]; exact Function.update_self ..
  · rw [ite_eq_right (fun h => hlt h.2), ite_eq_right hlt]; exact hm3_sp

/-- Foreground `prepGrowProg` + `growZero` + `userMutateProg` preserves `SchedEq` and produces
identical `k_grow` across any two resting `DualStateInv` states sharing `s_dict` and `SchedEq`. -/
theorem schedEq_foreground {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V} {s₁ s₂ : Memory.State}
    (h₁ : DualStateInv c U V w base s_dict L₁ s₁)
    (h₂ : DualStateInv c U V w base s_dict L₂ s₂)
    (hsch : SchedEq base s₁ s₂)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val) :
    let k_grow₁ :=
      (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
    let k_grow₂ :=
      (Memory.spec 0).clientResult s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
    let s_prep₁ :=
      (Memory.spec 0).clientState s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
    let s_prep₂ :=
      (Memory.spec 0).clientState s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
    let s_grow₁ : Memory.State := { mem := s_prep₁.mem, frontier := s₁.frontier + k_grow₁ }
    let s_grow₂ : Memory.State := { mem := s_prep₂.mem, frontier := s₂.frontier + k_grow₂ }
    let s_mid₁ :=
      (Memory.spec 0).clientState s_grow₁ (userMutateProg ((base, opTag), (u.val, v_val)))
    let s_mid₂ :=
      (Memory.spec 0).clientState s_grow₂ (userMutateProg ((base, opTag), (u.val, v_val)))
    k_grow₁ = k_grow₂ ∧
    SchedEq base s_grow₁ s_grow₂ ∧
    SchedEq base s_mid₁ s_mid₂ := by
  dsimp only
  have hw_pos : 0 < w := by have := h₁.hw11; omega
  have hu1_1 : s₁.mem (base + hdrU1) + 1 ≤ 2 ^ w := by
    have := h₁.hdr.1; have := h₁.U_pos; have := h₁.U_lt; omega
  have hnL_1 : s₁.mem (base + hdrLive) ≤ s₁.mem (base + hdrU1) + 1 := by
    rw [h₁.live_eq, h₁.hdr.1]; have := h₁.U_pos; have := h₁.live_le; omega
  have hu1_2 : s₂.mem (base + hdrU1) + 1 ≤ 2 ^ w := by
    have := h₂.hdr.1; have := h₂.U_pos; have := h₂.U_lt; omega
  have hnL_2 : s₂.mem (base + hdrLive) ≤ s₂.mem (base + hdrU1) + 1 := by
    rw [h₂.live_eq, h₂.hdr.1]; have := h₂.U_pos; have := h₂.live_le; omega
  obtain ⟨hst_p₁, hkg₁, _⟩ := prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos
    h₁.hdr.2.2.1 hu1_1 hnL_1
  obtain ⟨hst_p₂, hkg₂, _⟩ := prepGrowProg_eval (opTag := opTag) (u_val := u.val) hop_nz hw_pos
    h₂.hdr.2.2.1 hu1_2 hnL_2
  have hkg_eq :
      (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val)) =
      (Memory.spec 0).clientResult s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val)) := by
    rw [hkg₁, hkg₂, hsch.1,
      hsch.2 hdrLive (by decide) (by decide),
      hsch.2 hdrU1 (by decide) (by decide),
      hsch.2 hdrPhase (by decide) (by decide),
      hsch.2 hdrItemLo (by decide) (by decide),
      hsch.2 hdrItemHi (by decide) (by decide),
      hsch.2 hdrQLo (by decide) (by decide),
      hsch.2 hdrQHi (by decide) (by decide),
      hsch.2 hdrValBits (by decide) (by decide)]
  set k_grow :=
    (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
  set s_prep₁ :=
    (Memory.spec 0).clientState s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
  set s_prep₂ :=
    (Memory.spec 0).clientState s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
  set s_grow₁ : Memory.State := { mem := s_prep₁.mem, frontier := s₁.frontier + k_grow }
  set s_grow₂ : Memory.State := { mem := s_prep₂.mem, frontier := s₂.frontier + k_grow }
  have hsetup₁ := fgSetup_of_dualStateInv h₁ hop_nz u v
  have hsetup₂ := fgSetup_of_dualStateInv h₂ hop_nz u v
  have hlow₁ := hsetup₁.grow_low
  have hlow₂ := hsetup₂.grow_low
  dsimp only at hlow₁ hlow₂
  have hsch_grow : SchedEq base s_grow₁ s_grow₂ :=
    ⟨by dsimp only [s_grow₁, s_grow₂]; rw [hsch.1],
     fun off hoff hne =>
       (hlow₁ off (by omega)).trans ((hsch.2 off hoff hne).trans (hlow₂ off (by omega)).symm)⟩
  set s_mid₁ :=
    (Memory.spec 0).clientState s_grow₁ (userMutateProg ((base, opTag), (u.val, v_val)))
  set s_mid₂ :=
    (Memory.spec 0).clientState s_grow₂ (userMutateProg ((base, opTag), (u.val, v_val)))
  have hstep₁ : FGStepOutAux c U V w base opTag v_val u v s_dict L₁ s₁ s_prep₁ k_grow s_mid₁ := by
    by_cases hle7 : s₁.mem (base + hdrPhase) ≤ 7
    · exact fgStep_le7_aux h₁ u v hv_eq hsetup₁ rfl rfl rfl hle7
    · by_cases h8 : s₁.mem (base + hdrPhase) = 8
      · exact fgStep_eq8_aux h₁ u v hv_eq hsetup₁ rfl rfl rfl h8
      · exact fgStep_ge9_aux h₁ u v hv_eq hsetup₁ rfl rfl rfl (by omega)
  have hstep₂ : FGStepOutAux c U V w base opTag v_val u v s_dict L₂ s₂ s_prep₂
      ((Memory.spec 0).clientResult s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val)))
      ((Memory.spec 0).clientState
        { mem := s_prep₂.mem
          frontier := s₂.frontier +
            (Memory.spec 0).clientResult s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val)) }
        (userMutateProg ((base, opTag), (u.val, v_val)))) := by
    by_cases hle7 : s₂.mem (base + hdrPhase) ≤ 7
    · exact fgStep_le7_aux h₂ u v hv_eq hsetup₂ rfl rfl rfl hle7
    · by_cases h8 : s₂.mem (base + hdrPhase) = 8
      · exact fgStep_eq8_aux h₂ u v hv_eq hsetup₂ rfl rfl rfl h8
      · exact fgStep_ge9_aux h₂ u v hv_eq hsetup₂ rfl rfl rfl (by omega)
  rw [← hkg_eq] at hstep₂ ⊢
  refine ⟨rfl, hsch_grow, ?_⟩
  refine ⟨hstep₁.2.1.trans (hsch_grow.1.trans hstep₂.2.1.symm), fun off hoff hne_ud => ?_⟩
  by_cases hlv : off = hdrLive
  · subst hlv; exact hstep₁.2.2.1.trans hstep₂.2.2.1.symm
  · by_cases hsp : off = hdrSplit
    · subst hsp
      have hph_eq := hsch.2 hdrPhase (by decide) (by decide)
      by_cases hsl : s₁.mem (base + hdrPhase) = 3 ∨ s₁.mem (base + hdrPhase) = 10
      · have hsl₂ : s₂.mem (base + hdrPhase) = 3 ∨ s₂.mem (base + hdrPhase) = 10 :=
          hph_eq ▸ hsl
        have h1 := userMutate_hdrSplit_slide h₁ hop_nz u v hv_eq hsl
        have h2 := userMutate_hdrSplit_slide h₂ hop_nz u v hv_eq hsl₂
        dsimp only at h1 h2
        rw [← hkg_eq] at h2
        rw [h1, h2, hsch.2 hdrSplit (by decide) (by decide)]
      · have hn3_1 : s₁.mem (base + hdrPhase) ≠ 3 := fun h => hsl (Or.inl h)
        have hn10_1 : s₁.mem (base + hdrPhase) ≠ 10 := fun h => hsl (Or.inr h)
        have hn3_2 : s₂.mem (base + hdrPhase) ≠ 3 := by rw [← hph_eq]; exact hn3_1
        have hn10_2 : s₂.mem (base + hdrPhase) ≠ 10 := by rw [← hph_eq]; exact hn10_1
        exact (hstep₁.2.2.2.2.1 hn3_1 hn10_1).trans
          ((hsch.2 hdrSplit (by decide) (by decide)).trans (hstep₂.2.2.2.2.1 hn3_2 hn10_2).symm)
    · exact (hstep₁.2.2.2.1 (base + off) (by omega) (base_add_ne hlv) (base_add_ne hsp)).trans
        ((hsch.2 off hoff hne_ud).trans
          (hstep₂.2.2.2.1 (base + off) (by omega) (base_add_ne hlv) (base_add_ne hsp)).symm)

private theorem dualPh5MaskMem_lt48 (V w base pDst ibHi qHi nLive : ℕ) (m : ℕ → ℕ)
    {k : ℕ} (hk : k < 48) :
    dualPh5MaskMem V w base pDst ibHi qHi nLive m (pDst + k) = m (pDst + k) := by
  unfold dualPh5MaskMem
  repeat rw [Function.update_of_ne (by omega)]

/-- Background tick `bgTickProg` preserves `SchedEq` and produces identical `rArgs` across any two
`DualMidInv` states sharing `s_dict` and `SchedEq`. -/
private theorem schedEq_bgTick {c U V w base : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V} {s₁ s₂ : Memory.State}
    (h₁ : DualMidInv c U V w base s_dict L₁ s₁)
    (h₂ : DualMidInv c U V w base s_dict L₂ s₂)
    (hsch : SchedEq base s₁ s₂)
    (hsucc_fits :
      base + Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w
        (Dictionary.dom s_dict).card < 2 ^ w) :
    let s_t₁ := (Memory.spec 0).clientState s₁ (bgTickProg (base, s₁.frontier))
    let s_t₂ := (Memory.spec 0).clientState s₂ (bgTickProg (base, s₂.frontier))
    let r₁ := (Memory.spec 0).clientResult s₁ (bgTickProg (base, s₁.frontier))
    let r₂ := (Memory.spec 0).clientResult s₂ (bgTickProg (base, s₂.frontier))
    r₁ = r₂ ∧ SchedEq base s_t₁ s_t₂ := by
  dsimp only
  obtain ⟨_, hpost₁⟩ := bgTickProg_spec h₁ hsucc_fits
  obtain ⟨_, hpost₂⟩ := bgTickProg_spec h₂ hsucc_fits
  have hfr_eq : ((Memory.spec 0).clientState s₁ (bgTickProg (base, s₁.frontier))).frontier =
      ((Memory.spec 0).clientState s₂ (bgTickProg (base, s₂.frontier))).frontier :=
    hpost₁.1.trans (hsch.1.trans hpost₂.1.symm)
  have hw_pos : 0 < w := by have := h₁.hw11; omega
  have hph_eq := hsch.2 hdrPhase (by decide) (by decide)
  have hph_le : s₁.mem (base + hdrPhase) ≤ 11 := h₁.ph_le
  have hr_eq : (Memory.spec 0).clientResult s₁ (bgTickProg (base, s₁.frontier)) =
      (Memory.spec 0).clientResult s₂ (bgTickProg (base, s₂.frontier)) := by
    by_cases hp5 : s₁.mem (base + hdrPhase) = 5
    · have hp5_2 : s₂.mem (base + hdrPhase) = 5 := hph_eq.symm.trans hp5
      have hb₁ := hpost₁.2.2.2; rw [ite_eq_right (not_not.mpr hp5)] at hb₁
      have hb₂ := hpost₂.2.2.2; rw [ite_eq_right (not_not.mpr hp5_2)] at hb₂
      dsimp only at hb₁ hb₂
      rw [hb₁.2.2.2.2.2.1, hb₂.2.2.2.2.2.1, hsch.mbDst_eq,
        hsch.2 hdrCur (by decide) (by decide), hsch.2 hdrNDst (by decide) (by decide)]
    · have hp5_2 : s₂.mem (base + hdrPhase) ≠ 5 := by rw [← hph_eq]; exact hp5
      have hb₁ := hpost₁.2.2.2; rw [ite_eq_left hp5] at hb₁
      have hb₂ := hpost₂.2.2.2; rw [ite_eq_left hp5_2] at hb₂
      exact hb₁.1.trans hb₂.1.symm
  refine ⟨hr_eq, hfr_eq, fun off hoff hne_ud => ?_⟩
  have hbgev₁ := (bgTickProg_eval base s₁.frontier s₁).1
  have hbgev₂ := (bgTickProg_eval base s₂.frontier s₂).1
  dsimp only at hbgev₁ hbgev₂
  rw [← hph_eq] at hbgev₂
  rw [hbgev₁, hbgev₂]
  -- Helper updating identical header constants preserves `SchedEq`
  have hupd_eq : ∀ {m₁ m₂ : ℕ → ℕ} (o v : ℕ),
      (∀ k < 48, k ≠ hdrUnpermDone → m₁ (base + k) = m₂ (base + k)) →
      ∀ k < 48, k ≠ hdrUnpermDone →
        Function.update m₁ (base + o) v (base + k) = Function.update m₂ (base + o) v (base + k) :=
    fun o v hm k hk hne => by
      by_cases hko : k = o
      · subst hko; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (base_add_ne hko), Function.update_of_ne (base_add_ne hko)]
        exact hm k hk hne
  interval_cases hph_val : s₁.mem (base + hdrPhase)
  · -- `ph = 0` (`tickIdleProg`)
    simp only [↓reduceIte]
    rw [(tickIdleProg_eval base s₁).1, (tickIdleProg_eval base s₂).1]
    dsimp only
    have hnS_eq := hsch.2 hdrNSrc (by decide) (by decide)
    have hops_eq := hsch.2 hdrEpochOps (by decide) (by decide)
    have hmS_eq := hsch.2 hdrMSrc (by decide) (by decide)
    have hkb_eq := hsch.2 hdrKeyBits (by decide) (by decide)
    rw [← hnS_eq, ← hops_eq, ← hmS_eq, ← hkb_eq]
    set ops' := if s₁.mem (base + hdrNSrc) = 0 then 0 else s₁.mem (base + hdrEpochOps) + 1
    set s1_1 : Memory.State :=
      { mem := Function.update s₁.mem (base + hdrEpochOps) ops', frontier := s₁.frontier }
    set s1_2 : Memory.State :=
      { mem := Function.update s₂.mem (base + hdrEpochOps) ops', frontier := s₂.frontier }
    have hs1_hdr : ∀ k < 48, k ≠ hdrUnpermDone → s1_1.mem (base + k) = s1_2.mem (base + k) :=
      hupd_eq hdrEpochOps ops' hsch.2
    have hhdr1_1 : RootStaticHeader c U V w base s1_1.mem := by
      have heq : ∀ j < 10, s1_1.mem (base + j) = s₁.mem (base + j) := fun j hj => by
        dsimp only [s1_1]
        exact Function.update_of_ne (base_add_ne (by dsimp only [hdrEpochOps]; omega)) _ _
      exact ⟨(heq 0 (by decide)).trans h₁.hdr.1, (heq 1 (by decide)).trans h₁.hdr.2.1,
        (heq 2 (by decide)).trans h₁.hdr.2.2.1, (heq 3 (by decide)).trans h₁.hdr.2.2.2.1,
        (heq 4 (by decide)).trans h₁.hdr.2.2.2.2.1, (heq 5 (by decide)).trans h₁.hdr.2.2.2.2.2.1,
        (heq 6 (by decide)).trans h₁.hdr.2.2.2.2.2.2.1,
        (heq 7 (by decide)).trans h₁.hdr.2.2.2.2.2.2.2.1,
        (heq 8 (by decide)).trans h₁.hdr.2.2.2.2.2.2.2.2.1,
        (heq 9 (by decide)).trans h₁.hdr.2.2.2.2.2.2.2.2.2⟩
    have hhdr1_2 : RootStaticHeader c U V w base s1_2.mem := by
      have heq : ∀ j < 10, s1_2.mem (base + j) = s₂.mem (base + j) := fun j hj => by
        dsimp only [s1_2]
        exact Function.update_of_ne (base_add_ne (by dsimp only [hdrEpochOps]; omega)) _ _
      exact ⟨(heq 0 (by decide)).trans h₂.hdr.1, (heq 1 (by decide)).trans h₂.hdr.2.1,
        (heq 2 (by decide)).trans h₂.hdr.2.2.1, (heq 3 (by decide)).trans h₂.hdr.2.2.2.1,
        (heq 4 (by decide)).trans h₂.hdr.2.2.2.2.1, (heq 5 (by decide)).trans h₂.hdr.2.2.2.2.2.1,
        (heq 6 (by decide)).trans h₂.hdr.2.2.2.2.2.2.1,
        (heq 7 (by decide)).trans h₂.hdr.2.2.2.2.2.2.2.1,
        (heq 8 (by decide)).trans h₂.hdr.2.2.2.2.2.2.2.2.1,
        (heq 9 (by decide)).trans h₂.hdr.2.2.2.2.2.2.2.2.2⟩
    have htr₁ := (checkTriggerProg_spec (s := s1_1) h₁.U_pos hhdr1_1
      (by
        dsimp only [s1_1]
        rw [Function.update_of_ne (base_add_ne (by decide))]
        exact h₁.nSrc_bounds)).2.2
    have htr₂ := (checkTriggerProg_spec (s := s1_2) h₂.U_pos hhdr1_2
      (by
        dsimp only [s1_2]
        rw [Function.update_of_ne (base_add_ne (by decide))]
        exact h₂.nSrc_bounds)).2.2
    have htr_eq : (Memory.spec 0).clientResult s1_1 (checkTriggerProg base) =
        (Memory.spec 0).clientResult s1_2 (checkTriggerProg base) := by
      rw [htr₁, htr₂,
        hs1_hdr hdrNSrc (by decide) (by decide),
        hs1_hdr hdrLive (by decide) (by decide),
        hs1_hdr hdrEpochOps (by decide) (by decide)]
    change (if ((Memory.spec 0).clientResult s1_1 (checkTriggerProg base)).1 = 0 then s1_1.mem
      else _) (base + off) =
      (if ((Memory.spec 0).clientResult s1_2 (checkTriggerProg base)).1 = 0 then s1_2.mem
      else _) (base + off)
    rw [← htr_eq]
    set tr := (Memory.spec 0).clientResult s1_1 (checkTriggerProg base)
    have hmb : ∀ k < 48, k ≠ hdrUnpermDone →
        Function.update (Function.update (Function.update s1_1.mem (base + hdrNDst) tr.2)
          (base + hdrStage) 0) (base + hdrEpochOps) 0 (base + k) =
        Function.update (Function.update (Function.update s1_2.mem (base + hdrNDst) tr.2)
          (base + hdrStage) 0) (base + hdrEpochOps) 0 (base + k) :=
      hupd_eq hdrEpochOps 0 (hupd_eq hdrStage 0 (hupd_eq hdrNDst tr.2 hs1_hdr))
    by_cases htr1 : tr.1 = 0
    · rw [ite_eq_left htr1, ite_eq_left htr1]
      exact hs1_hdr off hoff hne_ud
    · rw [ite_eq_right htr1, ite_eq_right htr1]
      by_cases htr2 : tr.2 = 0
      · rw [ite_eq_left htr2, ite_eq_left htr2]
        exact hupd_eq hdrPhase 2 (hupd_eq hdrQHi _ (hupd_eq hdrItemHi _
          (hupd_eq hdrPad _ (hupd_eq hdrMDst 0 hmb)))) off hoff hne_ud
      · rw [ite_eq_right htr2, ite_eq_right htr2]
        exact hupd_eq hdrPhase 1 (hupd_eq hdrLogK 0 (hupd_eq hdrLogAcc tr.2
          (hupd_eq hdrLogSub 0 hmb))) off hoff hne_ud
  · -- `ph = 1` (`tickLogProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    rw [(tickLogProg_eval base s₁).1, (tickLogProg_eval base s₂).1,
      ← hsch.2 hdrLogSub (by decide) (by decide)]
    have hp1_1 : s₁.mem (base + hdrPhase) = 1 := hph_val
    have hp1_2 : s₂.mem (base + hdrPhase) = 1 := hph_eq.symm
    have hsched₁ := h₁.sched; rw [ite_eq_right (by rw [hp1_1]; decide)] at hsched₁
    have hsched₂ := h₂.sched; rw [ite_eq_right (by rw [hp1_2]; decide)] at hsched₂
    have hnD_pos₁ : 0 < s₁.mem (base + hdrNDst) := (hsched₁.ph1 hp1_1).2.1
    have hth_d₁ : whpThreshold c ≤ s₁.mem (base + hdrNDst) ∧ s₁.mem (base + hdrNDst) ≤ U :=
      hsched₁.nDst_bounds.resolve_left hnD_pos₁.ne'
    have hnD_ge2 : 2 ≤ s₁.mem (base + hdrNDst) :=
      (by decide : 2 ≤ 2 ^ 20).trans ((whpThreshold_ge_pow20 c).trans hth_d₁.1)
    have hnD_eq := hsch.2 hdrNDst (by decide) (by decide)
    by_cases hsub2 : s₁.mem (base + hdrLogSub) < 2
    · rw [ite_eq_left hsub2, ite_eq_left hsub2]
      have hlog_inv : ∀ {st : Memory.State} {L : DualLatent c U V},
          DualMidInv c U V w base s_dict L st → st.mem (base + hdrPhase) = 1 →
          ¬(1 < st.mem (base + hdrLogAcc)) → st.mem (base + hdrLogSub) = 0 →
          st.mem (base + hdrLogK) = Nat.log 2 (st.mem (base + hdrNDst)) := by
        intro st L hm hp1 hna hs0
        obtain ⟨_, h0, _, _⟩ := hm.ph1_inv hp1
        obtain ⟨h1_acc, hlo, hhi⟩ := h0 hs0
        have hacc1 : st.mem (base + hdrLogAcc) = 1 := by omega
        rw [hacc1, one_mul] at hlo
        rw [hacc1] at hhi
        have hhi' : st.mem (base + hdrNDst) < 2 ^ (st.mem (base + hdrLogK) + 1) := by
          rw [Nat.pow_succ]; omega
        exact le_antisymm (Nat.le_log_of_pow_le Nat.one_lt_two hlo)
          (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hhi'))
      rw [(tickLogShiftProg_eval s₁ hnD_ge2 (hlog_inv h₁ hp1_1)).1,
        (tickLogShiftProg_eval s₂ (hnD_eq ▸ hnD_ge2) (hlog_inv h₂ hp1_2)).1,
        ← hsch.2 hdrLogSub (by decide) (by decide),
        ← hsch.2 hdrLogAcc (by decide) (by decide),
        ← hsch.2 hdrLogK (by decide) (by decide), ← hnD_eq]
      split_ifs <;> dsimp only
      · exact hupd_eq hdrLogK _ (hupd_eq hdrLogAcc _ hsch.2) off hoff hne_ud
      · exact hupd_eq hdrLogK 0 (hupd_eq hdrLogAcc _ (hupd_eq hdrLogSub 1
          (hupd_eq hdrPgB _ (hupd_eq hdrPtrB _ (hupd_eq hdrClogN _
            (hupd_eq hdrLogN _ hsch.2)))))) off hoff hne_ud
      · exact hupd_eq hdrLogSub 2 (hupd_eq hdrEll _ hsch.2) off hoff hne_ud
    · rw [ite_eq_right hsub2, ite_eq_right hsub2,
        (tickLogFinishProg_eval base s₁).1, (tickLogFinishProg_eval base s₂).1]
      dsimp only
      have hsub_eq2 : s₁.mem (base + hdrLogSub) = 2 := by
        have := (h₁.ph1_inv hp1_1).1; omega
      obtain ⟨hlog_e₁, hell_e₁, _, hpg_e₁⟩ := (h₁.ph1_inv hp1_1).2.2.2 hsub_eq2
      have hlog_eq := hsch.2 hdrLogN (by decide) (by decide)
      have hell_eq := hsch.2 hdrEll (by decide) (by decide)
      have hpg_eq := hsch.2 hdrPgB (by decide) (by decide)
      have hptr_eq := hsch.2 hdrPtrB (by decide) (by decide)
      have hmS_eq := hsch.2 hdrMSrc (by decide) (by decide)
      have hkb_eq := hsch.2 hdrKeyBits (by decide) (by decide)
      have hqL_eq := hsch.2 hdrQLo (by decide) (by decide)
      let fl1 : FastEpochLayout :=
        { c := c, U := U, V := V, w := w, N := s₁.mem (base + hdrNDst),
          metaBase := base + 192, pBase := base + hdrPBase1,
          io := directSlotIo w (valBits V) base 0 0 0 }
      have hwlp₁ := writeLargeParamTableProg_spec (base := base) (fl := fl1) (s := s₁)
        (Or.inl (by dsimp only [fl1, hdrPBase1]; omega)) hth_d₁.1 hth_d₁.2 hw_pos h₁.hdr
      have hwlp₂ := writeLargeParamTableProg_spec (base := base) (fl := fl1) (s := s₂)
        (Or.inl (by dsimp only [fl1, hdrPBase1]; omega)) hth_d₁.1 hth_d₁.2 hw_pos h₂.hdr
      dsimp only [fl1] at hwlp₁ hwlp₂
      rw [← hnD_eq, ← hlog_eq, ← hell_eq, ← hpg_eq, ← hptr_eq, ← hmS_eq, ← hkb_eq, ← hqL_eq,
        hlog_e₁, hell_e₁, hpg_e₁, hwlp₁.1, hwlp₂.1]
      set s1_1 := (Memory.spec 0).clientState s₁
        (writeLargeParamTableProg ((base, base + hdrPBase1),
          ((s₁.mem (base + hdrNDst), base + 192),
            ((Nat.log 2 (s₁.mem (base + hdrNDst)), Dynamic.logLogFactor (s₁.mem (base + hdrNDst))),
              pageSizeWhp (s₁.mem (base + hdrNDst))))))
      set s1_2 := (Memory.spec 0).clientState s₂
        (writeLargeParamTableProg ((base, base + hdrPBase1),
          ((s₁.mem (base + hdrNDst), base + 192),
            ((Nat.log 2 (s₁.mem (base + hdrNDst)), Dynamic.logLogFactor (s₁.mem (base + hdrNDst))),
              pageSizeWhp (s₁.mem (base + hdrNDst))))))
      have h30_1 : s1_1.mem (base + hdrPBase1 + 30) = offFpHash c w (s₁.mem (base + hdrNDst)) :=
        hwlp₁.2.2.2.1 30 (by decide)
      have h30_2 : s1_2.mem (base + hdrPBase1 + 30) = offFpHash c w (s₁.mem (base + hdrNDst)) :=
        hwlp₂.2.2.2.1 30 (by decide)
      rw [h30_1, h30_2]
      have hs1_hdr : ∀ k < 48, k ≠ hdrUnpermDone → s1_1.mem (base + k) = s1_2.mem (base + k) :=
        fun k hk hne =>
          (hwlp₁.2.2.2.2.2.2 (base + k) (by dsimp only [hdrPBase1]; omega)).trans
            ((hsch.2 k hk hne).trans
              (hwlp₂.2.2.2.2.2.2 (base + k) (by dsimp only [hdrPBase1]; omega)).symm)
      have hp1_out : ∀ {m₁ m₂ : ℕ → ℕ} (j v : ℕ),
          (∀ k < 48, k ≠ hdrUnpermDone → m₁ (base + k) = m₂ (base + k)) →
          ∀ k < 48, k ≠ hdrUnpermDone →
            Function.update m₁ (base + hdrPBase1 + j) v (base + k) =
              Function.update m₂ (base + hdrPBase1 + j) v (base + k) :=
        fun j v hm k hk hne => by
          rw [Function.update_of_ne (by dsimp only [hdrPBase1]; omega),
            Function.update_of_ne (by dsimp only [hdrPBase1]; omega)]
          exact hm k hk hne
      exact hupd_eq hdrPhase 2 (hupd_eq hdrDstMp _ (hupd_eq hdrDstPg _ (hupd_eq hdrDstPb _
        (hupd_eq hdrDstOt _ (hupd_eq hdrDstOd _ (hupd_eq hdrQHi _ (hupd_eq hdrItemHi _
          (hupd_eq hdrPad _ (hupd_eq hdrMDst _
            (hp1_out 62 _ (hp1_out 61 _ (hp1_out 1 _ hs1_hdr)))))))))))) off hoff hne_ud
  · -- `ph = 2` (`tickGrowPreProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hw₁ : 0 < s₁.mem (base + hdrW) := h₁.hdr.2.2.1 ▸ hw_pos
    have hw₂ : 0 < s₂.mem (base + hdrW) := h₂.hdr.2.2.1 ▸ hw_pos
    rw [(tickGrowPreProg_eval hw₁).1, (tickGrowPreProg_eval hw₂).1]
    rw [← hsch.1,
      ← hsch.2 hdrItemHi (by decide) (by decide),
      ← hsch.2 hdrLive (by decide) (by decide),
      ← hsch.2 hdrQHi (by decide) (by decide),
      ← hsch.2 hdrValBits (by decide) (by decide),
      ← hsch.2 hdrW (by decide) (by decide)]
    split_ifs
    · exact hsch.2 off hoff hne_ud
    · dsimp only
      by_cases hph_o : off = hdrPhase
      · subst hph_o; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (base_add_ne hph_o), Function.update_of_ne (base_add_ne hph_o)]
        rw [(setSplitSlotIoProg_eval _ _ _ _).1, (setSplitSlotIoProg_eval _ _ _ _).1,
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + off)
            (by dsimp only [hdrPBase0]; omega),
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + off)
            (by dsimp only [hdrPBase0]; omega)]
        exact hupd_eq hdrSplit _ hsch.2 off hoff hne_ud
  · -- `ph = 3` (`tickSlideUpProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp3_1 : s₁.mem (base + hdrPhase) = 3 := hph_val
    have hp3_2 : s₂.mem (base + hdrPhase) = 3 := hph_eq.symm
    rw [(tickSlideUpProg_eval base s₁).1, (tickSlideUpProg_eval base s₂).1]
    let cfg : SplitPairCfg :=
      { baseLo := s₁.mem (base + hdrItemLo), qBitsLo := s₁.mem (base + hdrQLo),
        vBitsLo := valBits V, baseHi := s₁.mem (base + hdrItemHi),
        qBitsHi := s₁.mem (base + hdrQHi), vBitsHi := valBits V, w := w }
    have hctx₁ : (Memory.spec 0).clientResult s₁ (loadSplitPairCtxProg base) = cfg.toCtx := by
      rw [(loadSplitPairCtxProg_eval base s₁).2.1]
      dsimp only [cfg, SplitPairCfg.toCtx]; rw [h₁.hdr.2.2.2.2.1, h₁.hdr.2.2.1]
    have hctx₂ : (Memory.spec 0).clientResult s₂ (loadSplitPairCtxProg base) = cfg.toCtx := by
      rw [(loadSplitPairCtxProg_eval base s₂).2.1]
      dsimp only [cfg, SplitPairCfg.toCtx]
      rw [h₂.hdr.2.2.2.2.1, h₂.hdr.2.2.1,
        ← hsch.2 hdrItemLo (by decide) (by decide),
        ← hsch.2 hdrQLo (by decide) (by decide),
        ← hsch.2 hdrItemHi (by decide) (by decide),
        ← hsch.2 hdrQHi (by decide) (by decide)]
    have hsched₁ := h₁.sched; rw [ite_eq_right (by rw [hp3_1]; decide)] at hsched₁
    obtain ⟨_, hpad_e, _, _, hibHi_e, hqHi_e⟩ := hsched₁.ge2 (by rw [hp3_1]; decide)
    have hibLo_e := hsched₁.ibLo_eq; rw [hp3_1, ite_eq_left (by decide : 3 < 10)] at hibLo_e
    have hqLo_e := hsched₁.qLo_eq; rw [hp3_1, ite_eq_left (by decide : 3 < 10)] at hqLo_e
    have hq_le : cfg.qBitsLo ≤ cfg.qBitsHi := by
      dsimp only [cfg]; rw [hqHi_e, hqLo_e]; exact le_max_left _ _
    have hibLo_192 : base + 192 ≤ cfg.baseLo := by dsimp only [cfg]; omega
    have hib_le : cfg.baseLo + 4 ≤ cfg.baseHi := by
      dsimp only [cfg]
      have hm_le : s₁.mem (base + hdrMSrc) ≤ s₁.mem (base + hdrPad) := by
        rw [hpad_e]; exact le_max_left _ _
      rw [hibHi_e, hibLo_e]; split_ifs <;> omega
    obtain ⟨_, hvb_w, hqLo_w, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h₁
    have hcfg_v₁ : cfg.Valid w (Dictionary.dom s_dict).card s₁.frontier :=
      ⟨hw_pos, rfl, hqLo_w, hvb_w, hqHi_w, hvb_w,
        by dsimp only [cfg] at hq_le hib_le ⊢; omega,
        by dsimp only [cfg] at hib_le ⊢; omega,
        lt_of_le_of_lt h₁.live_le h₁.U_lt,
        (hsched₁.ph3_10 ⟨by rw [hp3_1], by rw [hp3_1]; decide⟩).1⟩
    have hsp_eq := hsch.2 hdrSplit (by decide) (by decide)
    obtain ⟨_, hres_sb₁, _, _, _, hout_sb₁⟩ := slideUpBatchProg_spec (cfg := cfg)
      (n_tot := (Dictionary.dom s_dict).card) (s_split := s₁.mem (base + hdrSplit)) (s := s₁)
      hcfg_v₁ hq_le le_rfl (h₁.ph3_inv hp3_1).1 itemBatchWhp
    obtain ⟨_, hres_sb₂, _, _, _, hout_sb₂⟩ := slideUpBatchProg_spec (cfg := cfg)
      (n_tot := (Dictionary.dom s_dict).card) (s_split := s₁.mem (base + hdrSplit)) (s := s₂)
      (hsch.1 ▸ hcfg_v₁) hq_le le_rfl (hsp_eq ▸ (h₂.ph3_inv hp3_2).1) itemBatchWhp
    simp only [hctx₁, hctx₂, ← hsp_eq, hres_sb₁, hres_sb₂,
      ← hsch.2 hdrNDst (by decide) (by decide),
      ← hsch.2 hdrItemHi (by decide) (by decide),
      ← hsch.2 hdrQHi (by decide) (by decide),
      ← hsch.2 hdrLive (by decide) (by decide)]
    set s2_su₁ :=
      (Memory.spec 0).clientState s₁
        (slideUpBatchProg ((cfg.toCtx, s₁.mem (base + hdrSplit)), itemBatchWhp))
    set s2_su₂ :=
      (Memory.spec 0).clientState s₂
        (slideUpBatchProg ((cfg.toCtx, s₁.mem (base + hdrSplit)), itemBatchWhp))
    have hs2_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
        s2_su₁.mem (base + k) = s2_su₂.mem (base + k) := fun k hk hne =>
      (hout_sb₁ (base + k) (by omega)).trans
        ((hsch.2 k hk hne).trans (hout_sb₂ (base + k) (by omega)).symm)
    set s3_su₁ : Memory.State :=
      { mem := Function.update s2_su₁.mem (base + hdrSplit)
          (s₁.mem (base + hdrSplit) - itemBatchWhp)
        frontier := s2_su₁.frontier }
    set s3_su₂ : Memory.State :=
      { mem := Function.update s2_su₂.mem (base + hdrSplit)
          (s₁.mem (base + hdrSplit) - itemBatchWhp)
        frontier := s2_su₂.frontier }
    have hs3_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
        s3_su₁.mem (base + k) = s3_su₂.mem (base + k) :=
      hupd_eq hdrSplit (s₁.mem (base + hdrSplit) - itemBatchWhp) hs2_hdr
    have hs4_hdr : ∀ (st₁ st₂ : Memory.State) (x : (ℕ × ℕ) × ℕ),
        (∀ k < 48, k ≠ hdrUnpermDone → st₁.mem (base + k) = st₂.mem (base + k)) →
        ∀ k < 48, k ≠ hdrUnpermDone →
          ((Memory.spec 0).clientState st₁ (setDirectSlotIoProg ((base, base + hdrPBase0), x))).mem
            (base + k) =
          ((Memory.spec 0).clientState st₂ (setDirectSlotIoProg ((base, base + hdrPBase0), x))).mem
            (base + k) :=
      fun st₁ st₂ x hst k hk hne => by
        rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1, (setDirectSlotIoProg_eval _ _ _ _ _ _).1,
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + k)
            (by dsimp only [hdrPBase0]; omega),
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + k)
            (by dsimp only [hdrPBase0]; omega)]
        exact hst k hk hne
    have hsm1_hdr : ∀ {m₁ m₂ : ℕ → ℕ},
        (∀ k < 48, k ≠ hdrUnpermDone → m₁ (base + k) = m₂ (base + k)) →
        ∀ k < 48, k ≠ hdrUnpermDone →
          Function.update (Function.update m₁ (base + hdrSmallMeta1) 0)
            (base + hdrSmallMeta1 + 1) 0 (base + k) =
          Function.update (Function.update m₂ (base + hdrSmallMeta1) 0)
            (base + hdrSmallMeta1 + 1) 0 (base + k) := fun hm k hk hne => by
      rw [Function.update_of_ne (by dsimp only [hdrSmallMeta1]; omega),
        Function.update_of_ne (by dsimp only [hdrSmallMeta1]; omega),
        Function.update_of_ne (by dsimp only [hdrSmallMeta1]; omega),
        Function.update_of_ne (by dsimp only [hdrSmallMeta1]; omega)]
      exact hm k hk hne
    by_cases hc1 : s₁.mem (base + hdrSplit) - itemBatchWhp = 0
    · rw [ite_eq_left hc1, ite_eq_left hc1]
      by_cases hc2 : s₁.mem (base + hdrNDst) = 0
      · rw [ite_eq_left hc2, ite_eq_left hc2]
        dsimp only
        exact hupd_eq hdrPhase 6
          (hsm1_hdr (hupd_eq hdrCur 0 (hs4_hdr s3_su₁ s3_su₂ _ hs3_hdr))) off hoff hne_ud
      · rw [ite_eq_right hc2, ite_eq_right hc2]
        dsimp only
        exact hupd_eq hdrPhase 4 (hupd_eq hdrCur 0 (hs4_hdr s3_su₁ s3_su₂ _ hs3_hdr))
          off hoff hne_ud
    · rw [ite_eq_right hc1, ite_eq_right hc1]
      exact hs3_hdr off hoff hne_ud
  · -- `ph = 4` (`tickZeroMetaProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp4_1 : s₁.mem (base + hdrPhase) = 4 := hph_val
    have hp4_2 : s₂.mem (base + hdrPhase) = 4 := hph_eq.symm
    rw [(tickZeroMetaProg_eval base s₁).1, (tickZeroMetaProg_eval base s₂).1]
    dsimp only
    obtain ⟨hd_pos, hcur_le, _⟩ := h₁.ph4_inv hp4_1
    have hsched₁ := h₁.sched; rw [ite_eq_right (by rw [hp4_1]; decide)] at hsched₁
    obtain ⟨hmD_e, hpad_e, _, _, hibHi_e, _⟩ := hsched₁.ge2 (by rw [hp4_1]; decide)
    have hfr_hi := (hsched₁.ph3_10 ⟨by rw [hp4_1]; decide, by rw [hp4_1]; decide⟩).1
    have hth_d : whpThreshold c ≤ s₁.mem (base + hdrNDst) :=
      (hsched₁.nDst_bounds.resolve_left hd_pos.ne').1
    have hm32 : 32 ≤ s₁.mem (base + hdrMDst) := by
      have ho := epochMeta_offsets_le (w := w) hth_d
      exact (ho.1.trans (ho.2.1.trans (ho.2.2.1.trans ho.2.2.2))).trans hmD_e.symm.le
    have hmD_pad : s₁.mem (base + hdrMDst) ≤ s₁.mem (base + hdrPad) := by
      rw [hpad_e]; exact le_max_right _ _
    set metaDst := if s₁.mem (base + hdrStage) = 0 then base + 192 + s₁.mem (base + hdrPad)
      else base + 192
    have hmd_fr : metaDst + s₁.mem (base + hdrMDst) ≤ s₁.frontier := by
      rw [ite_eq_right hd_pos.ne'] at hibHi_e
      dsimp only [metaDst] at *; split_ifs <;> omega
    have hmd_lt : metaDst < s₁.frontier := by omega
    obtain ⟨_, hres_zb₁, _, _, hmem_zb₁⟩ :=
      zeroWordsBatchProg_spec hw_pos hcur_le hmd_lt hmd_fr bulkBatchWhp (s := s₁)
    obtain ⟨_, hres_zb₂, _, _, hmem_zb₂⟩ :=
      zeroWordsBatchProg_spec hw_pos hcur_le (hsch.1 ▸ hmd_lt) (hsch.1 ▸ hmd_fr) bulkBatchWhp
        (s := s₂)
    rw [← hsch.2 hdrStage (by decide) (by decide),
      ← hsch.2 hdrPad (by decide) (by decide),
      ← hsch.2 hdrMDst (by decide) (by decide),
      ← hsch.2 hdrCur (by decide) (by decide),
      ← hsch.2 hdrNDst (by decide) (by decide),
      ← hsch.2 hdrLogN (by decide) (by decide),
      ← hsch.2 hdrEll (by decide) (by decide),
      ← hsch.2 hdrPgB (by decide) (by decide),
      hres_zb₁, hres_zb₂]
    have hs1_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
        ((Memory.spec 0).clientState s₁
          (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
            bulkBatchWhp))).mem (base + k) =
        ((Memory.spec 0).clientState s₂
          (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
            bulkBatchWhp))).mem (base + k) := fun k hk hne => by
      have hmd_192 : base + 192 ≤ metaDst := by dsimp only [metaDst]; split_ifs <;> omega
      rw [hmem_zb₁, ite_eq_right (by omega), hmem_zb₂, ite_eq_right (by omega)]
      exact hsch.2 k hk hne
    by_cases hlt : min (s₁.mem (base + hdrMDst)) (s₁.mem (base + hdrCur) + bulkBatchWhp) <
        s₁.mem (base + hdrMDst)
    · rw [ite_eq_left hlt, ite_eq_left hlt]; dsimp only
      exact hupd_eq hdrCur _ hs1_hdr off hoff hne_ud
    · rw [ite_eq_right hlt, ite_eq_right hlt]; dsimp only
      by_cases hst0 : s₁.mem (base + hdrStage) = 0
      · rw [ite_eq_left hst0, ite_eq_left hst0]
        exact hupd_eq hdrPhase 5 (hupd_eq hdrCur 32 hs1_hdr) off hoff hne_ud
      · rw [ite_eq_right hst0, ite_eq_right hst0]
        have hhdr_s1_1 : RootStaticHeader c U V w base
            ((Memory.spec 0).clientState s₁
              (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
                bulkBatchWhp))).mem := by
          have heq : ∀ j < 10,
              ((Memory.spec 0).clientState s₁
                (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
                  bulkBatchWhp))).mem (base + j) = s₁.mem (base + j) := fun j hj => by
            have hmd_192 : base + 192 ≤ metaDst := by
              dsimp only [metaDst]; split_ifs; all_goals omega
            rw [hmem_zb₁, ite_eq_right (by omega)]
          exact ⟨(heq 0 (by decide)).trans h₁.hdr.1, (heq 1 (by decide)).trans h₁.hdr.2.1,
            (heq 2 (by decide)).trans h₁.hdr.2.2.1, (heq 3 (by decide)).trans h₁.hdr.2.2.2.1,
            (heq 4 (by decide)).trans h₁.hdr.2.2.2.2.1,
            (heq 5 (by decide)).trans h₁.hdr.2.2.2.2.2.1,
            (heq 6 (by decide)).trans h₁.hdr.2.2.2.2.2.2.1,
            (heq 7 (by decide)).trans h₁.hdr.2.2.2.2.2.2.2.1,
            (heq 8 (by decide)).trans h₁.hdr.2.2.2.2.2.2.2.2.1,
            (heq 9 (by decide)).trans h₁.hdr.2.2.2.2.2.2.2.2.2⟩
        have hhdr_s1_2 : RootStaticHeader c U V w base
            ((Memory.spec 0).clientState s₂
              (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
                bulkBatchWhp))).mem := by
          have heq : ∀ j < 10,
              ((Memory.spec 0).clientState s₂
                (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
                  bulkBatchWhp))).mem (base + j) = s₂.mem (base + j) := fun j hj => by
            have hmd_192 : base + 192 ≤ metaDst := by
              dsimp only [metaDst]; split_ifs; all_goals omega
            rw [hmem_zb₂, ite_eq_right (by omega)]
          exact ⟨(heq 0 (by decide)).trans h₂.hdr.1, (heq 1 (by decide)).trans h₂.hdr.2.1,
            (heq 2 (by decide)).trans h₂.hdr.2.2.1, (heq 3 (by decide)).trans h₂.hdr.2.2.2.1,
            (heq 4 (by decide)).trans h₂.hdr.2.2.2.2.1,
            (heq 5 (by decide)).trans h₂.hdr.2.2.2.2.2.1,
            (heq 6 (by decide)).trans h₂.hdr.2.2.2.2.2.2.1,
            (heq 7 (by decide)).trans h₂.hdr.2.2.2.2.2.2.2.1,
            (heq 8 (by decide)).trans h₂.hdr.2.2.2.2.2.2.2.2.1,
            (heq 9 (by decide)).trans h₂.hdr.2.2.2.2.2.2.2.2.2⟩
        obtain ⟨hlog_e, hell_e, hpg_e⟩ :=
          (hsched₁.ge2 (by rw [hp4_1]; decide)).2.2.2.1 hd_pos
        have hth_d_full := hsched₁.nDst_bounds.resolve_left hd_pos.ne'
        let fl0 : FastEpochLayout :=
          { c := c, U := U, V := V, w := w, N := s₁.mem (base + hdrNDst),
            metaBase := base + 192, pBase := base + hdrPBase0,
            io := directSlotIo w (valBits V) base 0 0 0 }
        have hwlp₁ := (writeLargeParamTableProg_spec (base := base) (fl := fl0)
          (s := (Memory.spec 0).clientState s₁
            (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
              bulkBatchWhp)))
          (Or.inl (by dsimp only [fl0, hdrPBase0]; omega)) hth_d_full.1 hth_d_full.2 hw_pos
          hhdr_s1_1).2.2.2.2.2.2
        have hwlp₂ := (writeLargeParamTableProg_spec (base := base) (fl := fl0)
          (s := (Memory.spec 0).clientState s₂
            (zeroWordsBatchProg (((metaDst, s₁.mem (base + hdrMDst)), s₁.mem (base + hdrCur)),
              bulkBatchWhp)))
          (Or.inl (by dsimp only [fl0, hdrPBase0]; omega)) hth_d_full.1 hth_d_full.2 hw_pos
          hhdr_s1_2).2.2.2.2.2.2
        dsimp only [fl0] at hwlp₁ hwlp₂
        rw [hlog_e, hell_e, hpg_e]
        exact hupd_eq hdrPhase 5 (hupd_eq hdrCur 32 fun k hk hne =>
          (hwlp₁ (base + k) (by dsimp only [hdrPBase0]; omega)).trans
            ((hs1_hdr k hk hne).trans
              (hwlp₂ (base + k) (by dsimp only [hdrPBase0]; omega)).symm)) off hoff hne_ud
  · -- `ph = 5` (`tickRandPrepProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp5_1 : s₁.mem (base + hdrPhase) = 5 := hph_val
    have hp5_2 : s₂.mem (base + hdrPhase) = 5 := hph_eq.symm
    rw [(tickRandPrepProg_eval base s₁).1, (tickRandPrepProg_eval base s₂).1]
    dsimp only
    have hp31_1 : s₁.mem (dualPDst base s₁.mem + 31) = offBktMeta c w (s₁.mem (base + hdrNDst)) :=
      by
        have h31 := (h₁.ph5_inv hp5_1).2.2.2.1 31 (by decide)
        dsimp only [FastEpochLayout.paramWord] at h31
        rwa [dualPh5MaskMem_lt48 _ _ _ _ _ _ _ _ (by decide : 31 < 48)] at h31
    have hp31_2 : s₂.mem (dualPDst base s₂.mem + 31) = offBktMeta c w (s₂.mem (base + hdrNDst)) :=
      by
        have h31 := (h₂.ph5_inv hp5_2).2.2.2.1 31 (by decide)
        dsimp only [FastEpochLayout.paramWord] at h31
        rwa [dualPh5MaskMem_lt48 _ _ _ _ _ _ _ _ (by decide : 31 < 48)] at h31
    have hpD_if₁ : (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
        dualPDst base s₁.mem := by
      unfold dualPDst; rw [hp5_1, ite_eq_left (by decide : 5 < 10)]
    have hpD_if₂ : (if s₂.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
        dualPDst base s₂.mem := by
      unfold dualPDst; rw [hp5_2, ite_eq_left (by decide : 5 < 10)]
    rw [hpD_if₁, hpD_if₂, hp31_1, hp31_2,
      ← hsch.2 hdrCur (by decide) (by decide),
      ← hsch.2 hdrNDst (by decide) (by decide)]
    exact hupd_eq hdrCur _ hsch.2 off hoff hne_ud
  · -- `ph = 6` (`tickInitDirProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp6_1 : s₁.mem (base + hdrPhase) = 6 := hph_val
    have hp6_2 : s₂.mem (base + hdrPhase) = 6 := hph_eq.symm
    obtain ⟨_, _, _, _, _, hctx₁, _, _, hv_m₁⟩ :=
      dualPgHost_eval_valid h₁ (by rw [hp6_1]; decide) (by rw [hp6_1]; decide)
    obtain ⟨_, _, _, _, _, hctx₂, _, _, hv_m₂⟩ :=
      dualPgHost_eval_valid h₂ (by rw [hp6_2]; decide) (by rw [hp6_2]; decide)
    set pgM := hostPageLayout c w (dualNHost base s₁.mem) (dualMbHost base s₁.mem)
      (s₁.mem (base + hdrItemHi)) 0 0 (dualNHost base s₁.mem)
    have hpgM_eq : hostPageLayout c w (dualNHost base s₂.mem) (dualMbHost base s₂.mem)
        (s₂.mem (base + hdrItemHi)) 0 0 (dualNHost base s₂.mem) = pgM := by
      dsimp only [pgM]; unfold dualNHost dualMbHost
      rw [hsch.2 hdrNDst (by decide) (by decide), hsch.2 hdrNSrc (by decide) (by decide),
        hsch.2 hdrStage (by decide) (by decide), hsch.2 hdrPad (by decide) (by decide),
        hsch.2 hdrItemHi (by decide) (by decide)]
    rw [hpgM_eq] at hctx₂ hv_m₂
    rw [(tickInitDirProg_eval base s₁).1, (tickInitDirProg_eval base s₂).1]
    simp only [hctx₁, hctx₂,
      ← hsch.2 hdrCur (by decide) (by decide),
      ← hsch.2 hdrLive (by decide) (by decide)]
    have hcur_le : s₁.mem (base + hdrCur) ≤ pgM.maxPages := (h₁.ph6_inv hp6_1).1
    obtain ⟨_, hres_d₁, _, _, hout_d₁, _⟩ :=
      pageInitDirBatchProg_spec (L := pgM) hv_m₁ hcur_le bulkBatchWhp (s := s₁)
    obtain ⟨_, hres_d₂, _, _, hout_d₂, _⟩ :=
      pageInitDirBatchProg_spec (L := pgM) hv_m₂ hcur_le bulkBatchWhp (s := s₂)
    rw [hres_d₁, hres_d₂]
    have hmb_192 : base + 192 ≤ pgM.metaBase := by
      change base + 192 ≤ dualMbHost base s₁.mem
      unfold dualMbHost; split_ifs <;> omega
    have hs2_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
        ((Memory.spec 0).clientState s₁
          (pageInitDirBatchProg ((pgM.toCtx, s₁.mem (base + hdrCur)), bulkBatchWhp))).mem
          (base + k) =
        ((Memory.spec 0).clientState s₂
          (pageInitDirBatchProg ((pgM.toCtx, s₁.mem (base + hdrCur)), bulkBatchWhp))).mem
          (base + k) := fun k hk hne =>
      (hout_d₁ (base + k) (by omega)).trans
        ((hsch.2 k hk hne).trans (hout_d₂ (base + k) (by omega)).symm)
    by_cases hlt_d : min pgM.maxPages (s₁.mem (base + hdrCur) + bulkBatchWhp) < pgM.maxPages
    · rw [ite_eq_left hlt_d, ite_eq_left hlt_d]; dsimp only
      exact hupd_eq hdrCur _ hs2_hdr off hoff hne_ud
    · rw [ite_eq_right hlt_d, ite_eq_right hlt_d]; dsimp only
      exact hupd_eq hdrPhase 7 (hupd_eq hdrCur 0 (hupd_eq hdrQSnap _
        (hupd_eq hdrNSnap _ hs2_hdr))) off hoff hne_ud
  · -- `ph = 7` (`tickInitTailProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp7_1 : s₁.mem (base + hdrPhase) = 7 := hph_val
    have hp7_2 : s₂.mem (base + hdrPhase) = 7 := hph_eq.symm
    obtain ⟨_, _, _, _, hctx0_1, hctx1_1, _, _, hv_m₁⟩ :=
      dualPgHost_eval_valid h₁ (by rw [hp7_1]; decide) (by rw [hp7_1]; decide)
    obtain ⟨_, _, _, _, hctx0_2, hctx1_2, _, _, hv_m₂⟩ :=
      dualPgHost_eval_valid h₂ (by rw [hp7_2]; decide) (by rw [hp7_2]; decide)
    set pgM := hostPageLayout c w (dualNHost base s₁.mem) (dualMbHost base s₁.mem)
      (s₁.mem (base + hdrItemHi)) 0 0 (dualNHost base s₁.mem)
    set pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s₁.mem
    have hpgM_eq : hostPageLayout c w (dualNHost base s₂.mem) (dualMbHost base s₂.mem)
        (s₂.mem (base + hdrItemHi)) 0 0 (dualNHost base s₂.mem) = pgM := by
      dsimp only [pgM]; unfold dualNHost dualMbHost
      rw [hsch.2 hdrNDst (by decide) (by decide), hsch.2 hdrNSrc (by decide) (by decide),
        hsch.2 hdrStage (by decide) (by decide), hsch.2 hdrPad (by decide) (by decide),
        hsch.2 hdrItemHi (by decide) (by decide)]
    rw [hpgM_eq] at hctx1_2 hv_m₂
    rw [← hsch.pgHost_eq] at hctx0_2
    rw [(tickInitTailProg_eval base s₁).1, (tickInitTailProg_eval base s₂).1]
    simp only [hctx1_1, hctx1_2,
      ← hsch.2 hdrCur (by decide) (by decide),
      ← hsch.2 hdrNSnap (by decide) (by decide)]
    obtain ⟨hnS_le, _, _, ⟨_, _, hcur_lt8, _, _⟩, _⟩ := h₁.ph7_inv hp7_1
    obtain ⟨_, hres_t₁, _, _, hout_t₁, _⟩ :=
      pageInitTailBatchProg_spec (L := pgM) hv_m₁ hnS_le hcur_lt8.le tailBatchWhp (s := s₁)
    obtain ⟨_, hres_t₂, _, _, hout_t₂, _⟩ :=
      pageInitTailBatchProg_spec (L := pgM) hv_m₂ hnS_le hcur_lt8.le tailBatchWhp (s := s₂)
    rw [hres_t₁, hres_t₂]
    have hmb_192 : base + 192 ≤ pgM.metaBase := by
      change base + 192 ≤ dualMbHost base s₁.mem
      unfold dualMbHost; split_ifs <;> omega
    set s2_1 := (Memory.spec 0).clientState s₁
      (pageInitTailBatchProg
        (((pgM.toCtx, s₁.mem (base + hdrNSnap)), s₁.mem (base + hdrCur)), tailBatchWhp))
    set s2_2 := (Memory.spec 0).clientState s₂
      (pageInitTailBatchProg
        (((pgM.toCtx, s₁.mem (base + hdrNSnap)), s₁.mem (base + hdrCur)), tailBatchWhp))
    have hs2_out1 : ∀ k < 48, s2_1.mem (base + k) = s₁.mem (base + k) :=
      fun k hk => hout_t₁ (base + k) (by omega)
    have hs2_out2 : ∀ k < 48, s2_2.mem (base + k) = s₂.mem (base + k) :=
      fun k hk => hout_t₂ (base + k) (by omega)
    have hs2_hdr : ∀ k < 48, k ≠ hdrUnpermDone → s2_1.mem (base + k) = s2_2.mem (base + k) :=
      fun k hk hne => (hs2_out1 k hk).trans ((hsch.2 k hk hne).trans (hs2_out2 k hk).symm)
    by_cases hlt_t : min (8 * pgM.pgB) (s₁.mem (base + hdrCur) + tailBatchWhp) < 8 * pgM.pgB
    · rw [ite_eq_left hlt_t, ite_eq_left hlt_t]; dsimp only
      exact hupd_eq hdrCur _ hs2_hdr off hoff hne_ud
    · rw [ite_eq_right hlt_t, ite_eq_right hlt_t]
      rw [(finishInitTailProg_eval base s2_1).1, (finishInitTailProg_eval base s2_2).1]
      have hctx_s2_1 : (Memory.spec 0).clientResult s2_1 (loadHostCtxProg (base, 0)) =
          pgH.toCtx := by
        rw [← hctx0_1, (loadHostCtxProg_eval base 0 s2_1).2.1,
          (loadHostCtxProg_eval base 0 s₁).2.1]
        simp only [↓reduceIte]
        have hod : ∀ j ≤ 4,
            s2_1.mem (base + (if s₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + j) =
            s₁.mem (base + (if s₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + j) :=
          fun j hj => by
            rw [Nat.add_assoc]
            exact hs2_out1 _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> omega)
        rw [hs2_out1 hdrStage (by decide), hs2_out1 hdrNDst (by decide),
          hs2_out1 hdrPad (by decide), hs2_out1 hdrW (by decide),
          hs2_out1 hdrItemHi (by decide), hs2_out1 hdrQHi (by decide),
          hs2_out1 hdrValBits (by decide), hs2_out1 hdrLive (by decide),
          show s2_1.mem (base + if s₁.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) = _ by
            simpa only [Nat.add_zero] using hod 0 (by decide),
          hod 1 (by decide), hod 2 (by decide), hod 3 (by decide), hod 4 (by decide)]
      have hctx_s2_2 : (Memory.spec 0).clientResult s2_2 (loadHostCtxProg (base, 0)) =
          pgH.toCtx := by
        rw [← hctx0_2, (loadHostCtxProg_eval base 0 s2_2).2.1,
          (loadHostCtxProg_eval base 0 s₂).2.1]
        simp only [↓reduceIte]
        have hod : ∀ j ≤ 4,
            s2_2.mem (base + (if s₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + j) =
            s₂.mem (base + (if s₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + j) :=
          fun j hj => by
            rw [Nat.add_assoc]
            exact hs2_out2 _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> omega)
        rw [hs2_out2 hdrStage (by decide), hs2_out2 hdrNDst (by decide),
          hs2_out2 hdrPad (by decide), hs2_out2 hdrW (by decide),
          hs2_out2 hdrItemHi (by decide), hs2_out2 hdrQHi (by decide),
          hs2_out2 hdrValBits (by decide), hs2_out2 hdrLive (by decide),
          show s2_2.mem (base + if s₂.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) = _ by
            simpa only [Nat.add_zero] using hod 0 (by decide),
          hod 1 (by decide), hod 2 (by decide), hod 3 (by decide), hod 4 (by decide)]
      simp only [hctx_s2_1, hctx_s2_2,
        ← hs2_hdr hdrStage (by decide) (by decide),
        ← hs2_hdr hdrNDst (by decide) (by decide),
        ← hs2_hdr hdrLive (by decide) (by decide),
        ← hs2_hdr hdrQSnap (by decide) (by decide)]
      have hmbH_192 : base + 192 ≤ pgH.metaBase := hmb_192
      set pSrc := if s2_1.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1
      set pDst := if s2_1.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
      have hpS_64 : base + 64 ≤ pSrc := by
        dsimp only [pSrc, hdrPBase0, hdrPBase1]; split_ifs <;> omega
      have hpD_64 : base + 64 ≤ pDst := by
        dsimp only [pDst, hdrPBase0, hdrPBase1]; split_ifs <;> omega
      have h4_hdr : ∀ (st : Memory.State) (s2_st : Memory.State),
          (∀ k < 48, s2_st.mem (base + k) = st.mem (base + k)) →
          ∀ k < 48,
            ((Memory.spec 0).clientState
              ((Memory.spec 0).clientState
                ((Memory.spec 0).clientState s2_st
                  (pageInitScalarsBandProg ((pgH.metaBase, pgH.pgB),
                    (s2_1.mem (base + hdrQSnap),
                      s2_1.mem (base + hdrLive) - s2_1.mem (base + hdrQSnap) * pgH.pgB))))
                (setSlotIoProg (pSrc, ((1, 0), pgH.toCtx))))
              (if s2_1.mem (base + hdrNDst) = 0 then
                 writeSmallParamTableProg ((pDst, base + hdrSmallMeta1), ((1, 1), pgH.toCtx))
               else setSlotIoProg (pDst, ((1, 1), pgH.toCtx)))).mem (base + k) =
            st.mem (base + k) := fun st s2_st heq_s2 k hk => by
        have h_s4 : ∀ s3_st : Memory.State,
            ((Memory.spec 0).clientState s3_st
              (if s2_1.mem (base + hdrNDst) = 0 then
                 writeSmallParamTableProg ((pDst, base + hdrSmallMeta1), ((1, 1), pgH.toCtx))
               else setSlotIoProg (pDst, ((1, 1), pgH.toCtx)))).mem (base + k) =
            s3_st.mem (base + k) := fun s3_st => by
          by_cases hd0 : s2_1.mem (base + hdrNDst) = 0
          · rw [ite_eq_left hd0]
            exact (writeSmallParamTableProg_spec pDst
              ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3_st).2.2.2 (base + k) (by omega)
          · rw [ite_eq_right hd0]
            exact (setSlotIoProg_frame pDst ((1, 1), pgH.toCtx)).mem_outside s3_st (base + k)
              (by omega)
        have hps_out := (pageInitScalarsBandProg_spec pgH.metaBase pgH.pgB
          (s2_1.mem (base + hdrQSnap))
          (s2_1.mem (base + hdrLive) - s2_1.mem (base + hdrQSnap) * pgH.pgB)
          s2_st).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (base + k) (by omega)
        rw [h_s4,
          (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside _ (base + k) (by omega),
          hps_out]
        exact heq_s2 k hk
      exact hupd_eq hdrPhase 8 (hupd_eq hdrRem _ fun k hk hne =>
        (h4_hdr s₁ s2_1 hs2_out1 k hk).trans
          ((hsch.2 k hk hne).trans (h4_hdr s₂ s2_2 hs2_out2 k hk).symm)) off hoff hne_ud
  · -- `ph = 8` (`tickMigrateProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp8_1 : s₁.mem (base + hdrPhase) = 8 := hph_val
    have hp8_2 : s₂.mem (base + hdrPhase) = 8 := hph_eq.symm
    rw [(tickMigrateProg_eval base s₁).1, (tickMigrateProg_eval base s₂).1]
    -- Extract `hout_s1` on `< base + 48` for both `s₁` and `s₂` via `migrateBatchProg_spec`
    have hmb_pres : ∀ {st : Memory.State} {L : DualLatent c U V},
        DualMidInv c U V w base s_dict L st → st.mem (base + hdrPhase) = 8 →
        let pS := if st.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1
        let pD := if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
        let pgH_st := dualPgHost c V w base (Dictionary.dom s_dict).card st.mem
        let s1_st := (Memory.spec 0).clientState st (migrateBatchProg (((pS, pD), 0), itemBatchWhp))
        (∀ k < 48, s1_st.mem (base + k) = st.mem (base + k)) ∧
        (Memory.spec 0).clientResult s1_st (loadHostCtxProg (base, 0)) = pgH_st.toCtx := by
      intro st L hm hp8
      dsimp only
      obtain ⟨hcap_s, hcap_d, hdj, hdict_or, _, hsl_s, hsl_d, _, _⟩ := hm.sl_8 hp8
      have h8_10 : st.mem (base + hdrPhase) < 10 := by rw [hp8]; decide
      have hpD_e : dualPDst base st.mem =
          (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) := by
        unfold dualPDst; rw [ite_eq_left h8_10]
      rw [hpD_e] at hsl_d
      have hsched := hm.sched; rw [ite_eq_right (by rw [hp8]; decide)] at hsched
      obtain ⟨hmD_e, hpad_e, _, _, hibHi_e, _⟩ := hsched.ge2 (by rw [hp8]; decide)
      obtain ⟨_, _, _, _, hctx0_st, _, _, _, _⟩ :=
        dualPgHost_eval_valid hm (by rw [hp8]; decide) (by rw [hp8]; decide)
      obtain ⟨_, hdst_safe⟩ := dualCoreInv_cap_safe hm
      rw [ite_eq_right (by rw [hp8]; decide)] at hdst_safe
      have hsum_card : (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card =
          (Dictionary.dom s_dict).card := by
        rw [← hdict_or, dom_toDictState_card, liveDom_orOpt_card hdj]
      have hp_disj :
          (if st.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) + 64 ≤
            (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) ∨
          (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) + 64 ≤
            (if st.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) := by
        dsimp only [hdrPBase0, hdrPBase1]
        split_ifs <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
      have hpm_s :
          (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) + 64 ≤
            dualMbSrc base st.mem ∨
          dualMbSrc base st.mem +
            (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
            (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) := by
        rw [hcap_s]; unfold dualMbSrc dualCapSrc
        dsimp only [hdrPBase0, hdrPBase1, hdrSmallMeta0]
        by_cases hst0 : st.mem (base + hdrStage) = 0
        · simp only [hst0, ↓reduceIte]
          split_ifs <;> [exact Or.inr (by omega); exact Or.inl (by omega)]
        · simp only [hst0, ↓reduceIte]; exact Or.inl (by omega)
      have hpm_d :
          (if st.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) + 64 ≤
            dualMbDst base st.mem ∨
          dualMbDst base st.mem +
            (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
            (if st.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1) := by
        rw [hcap_d]; unfold dualMbDst; rw [ite_eq_left h8_10]
        dsimp only [hdrPBase0, hdrPBase1, hdrSmallMeta1]
        split_ifs <;> first | exact Or.inr (by omega) | exact Or.inl (by omega)
      have hmm_disj :
          dualMbSrc base st.mem +
            (if L.slotSrc.nCap = 0 then 2 else offPageDir c w L.slotSrc.nCap) ≤
            dualMbDst base st.mem ∨
          dualMbDst base st.mem +
            (if L.slotDst.nCap = 0 then 2 else offPageDir c w L.slotDst.nCap) ≤
            dualMbSrc base st.mem := by
        rw [hcap_s, hcap_d]; unfold dualMbSrc dualMbDst dualCapSrc
        rw [ite_eq_left h8_10]; dsimp only [hdrSmallMeta0, hdrSmallMeta1]
        by_cases hd0 : st.mem (base + hdrNDst) = 0
        · obtain ⟨hs_pos, hst0, _⟩ := hsched.nDst_zero hd0
          simp only [hd0, hst0, hs_pos.ne', ↓reduceIte]; exact Or.inr (by omega)
        · simp only [hd0, ↓reduceIte]
          by_cases hst0 : st.mem (base + hdrStage) = 0
          · simp only [hst0, ↓reduceIte]
            by_cases hs0 : st.mem (base + hdrNSrc) = 0
            · simp only [hs0, ↓reduceIte]; exact Or.inl (by omega)
            · have hth_s := (hm.nSrc_bounds.resolve_left hs0).1
              have hod_s := (epochMeta_offsets_le (w := w) hth_s).2.2.2
              have hmS_p : st.mem (base + hdrMSrc) ≤ st.mem (base + hdrPad) := by
                rw [hpad_e]; exact le_max_left _ _
              rw [← hm.mSrc_eq] at hod_s; simp only [hs0, ↓reduceIte]; exact Or.inl (by omega)
          · simp only [hst0, ↓reduceIte]
            have hth_d := (hsched.nDst_bounds.resolve_left hd0).1
            have hod_d := (epochMeta_offsets_le (w := w) hth_d).2.2.2
            have hmD_p : st.mem (base + hdrMDst) ≤ st.mem (base + hdrPad) := by
              rw [hpad_e]; exact le_max_right _ _
            rw [← hmD_e] at hod_d; exact Or.inr (by omega)
      have hcap_d_m : L.slotDst.nCap ≠ 0 →
          (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card ≤ L.slotDst.nCap := by
        intro hne
        rw [hcap_d] at hne
        rw [hsum_card, hcap_d]
        unfold EpochCapSafe at hdst_safe; rw [ite_eq_right hne] at hdst_safe
        exact hdst_safe.2.2.2
      have hcap_pg_m :
          (liveDom L.slotDst.s_abs).card + (liveDom L.slotSrc.s_abs).card ≤
            (dualPgHost c V w base (Dictionary.dom s_dict).card st.mem).nCap := by
        rw [hsum_card]; exact le_rfl
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hout_mb, _⟩ :=
        migrateBatchProg_spec hsl_s hsl_d hdj hp_disj hpm_s hpm_d hmm_disj hcap_d_m hcap_pg_m
          itemBatchWhp
      have hmb_ge192 : base + 192 ≤
          (dualPgHost c V w base (Dictionary.dom s_dict).card st.mem).metaBase := by
        change base + 192 ≤ dualMbHost base st.mem; unfold dualMbHost; split_ifs <;> omega
      have hibHi_ge : base + 196 ≤ st.mem (base + hdrItemHi) := by
        rw [hibHi_e]; split_ifs <;> omega
      have hhdr_mb : ∀ k < 48,
          ((Memory.spec 0).clientState st
            (migrateBatchProg
              ((((if st.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1),
                 (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)),
                0), itemBatchWhp))).mem (base + k) = st.mem (base + k) := fun k hk => by
        refine hout_mb (base + k) (fun hs_o => ?_) (fun hd_o => ?_)
        · unfold slotOwnsAddr at hs_o
          by_cases hc0 : L.slotSrc.nCap = 0
          · rw [ite_eq_left hc0] at hs_o
            have hmb_s : dualMbSrc base st.mem = base + hdrSmallMeta0 := by
              rw [hcap_s] at hc0; unfold dualMbSrc dualCapSrc at *
              by_cases hs_z : st.mem (base + hdrStage) = 0
              · rw [ite_eq_left hs_z] at hc0 ⊢; exact ite_eq_left hc0
              · rw [ite_eq_right hs_z] at hc0
                exact absurd hc0 (fun hd0 => hs_z (hsched.nDst_zero hd0).2.1)
            rw [hmb_s] at hs_o
            simp only [SmallEpochLayout.OwnsAddr, pagedSlotIo, SlotIoLayout.OwnsAddr,
              PageArenaLayout.OwnsAddr, PageArenaLayout.OwnsMetaAddr,
              PageArenaLayout.OwnsItemAddr, one_ne_zero, ↓reduceIte, hdrSmallMeta0] at hs_o
            rcases hs_o with h | h | ((⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;>
              (try change st.mem (base + hdrItemHi) ≤ _ at h) <;> omega
          · rw [ite_eq_right hc0] at hs_o
            have hmb_s : base + 192 ≤ dualMbSrc base st.mem := by
              rw [hcap_s] at hc0; unfold dualMbSrc dualCapSrc at *
              by_cases hs_z : st.mem (base + hdrStage) = 0
              · rw [ite_eq_left hs_z] at hc0 ⊢; rw [ite_eq_right hc0]
              · rw [ite_eq_right hs_z]; omega
            simp only [FastEpochLayout.OwnsFastAddr, pagedSlotIo, SlotIoLayout.OwnsAddr,
              PageArenaLayout.OwnsAddr, PageArenaLayout.OwnsMetaAddr,
              PageArenaLayout.OwnsItemAddr, one_ne_zero, ↓reduceIte] at hs_o
            rcases hs_o with ⟨h, _⟩ | ⟨h, _⟩ | ((⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;>
              (try change st.mem (base + hdrItemHi) ≤ _ at h) <;> omega
        · unfold slotOwnsAddr at hd_o
          by_cases hc0 : L.slotDst.nCap = 0
          · rw [ite_eq_left hc0] at hd_o
            have hmb_d : dualMbDst base st.mem = base + hdrSmallMeta1 := by
              rw [hcap_d] at hc0; unfold dualMbDst; rw [ite_eq_left h8_10, ite_eq_left hc0]
            rw [hmb_d] at hd_o
            simp only [SmallEpochLayout.OwnsAddr, pagedSlotIo, SlotIoLayout.OwnsAddr,
              PageArenaLayout.OwnsAddr, PageArenaLayout.OwnsMetaAddr,
              PageArenaLayout.OwnsItemAddr, one_ne_zero, ↓reduceIte, hdrSmallMeta1] at hd_o
            rcases hd_o with h | h | ((⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;>
              (try change st.mem (base + hdrItemHi) ≤ _ at h) <;> omega
          · rw [ite_eq_right hc0] at hd_o
            have hmb_d : base + 192 ≤ dualMbDst base st.mem := by
              rw [hcap_d] at hc0; unfold dualMbDst; rw [ite_eq_left h8_10, ite_eq_right hc0]
              split_ifs <;> omega
            simp only [FastEpochLayout.OwnsFastAddr, pagedSlotIo, SlotIoLayout.OwnsAddr,
              PageArenaLayout.OwnsAddr, PageArenaLayout.OwnsMetaAddr,
              PageArenaLayout.OwnsItemAddr, one_ne_zero, ↓reduceIte] at hd_o
            rcases hd_o with ⟨h, _⟩ | ⟨h, _⟩ | ((⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;>
              (try change st.mem (base + hdrItemHi) ≤ _ at h) <;> omega
      refine ⟨hhdr_mb, ?_⟩
      set s1_mb := (Memory.spec 0).clientState st
        (migrateBatchProg
          ((((if st.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1),
             (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)),
            0), itemBatchWhp))
      rw [← hctx0_st, (loadHostCtxProg_eval base 0 s1_mb).2.1,
        (loadHostCtxProg_eval base 0 st).2.1]
      simp only [↓reduceIte]
      have hod : ∀ j ≤ 4,
          s1_mb.mem (base + (if st.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + j) =
          st.mem (base + (if st.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + j) :=
        fun j hj => by
          rw [Nat.add_assoc]
          exact hhdr_mb _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> omega)
      rw [hhdr_mb hdrStage (by decide), hhdr_mb hdrNDst (by decide),
        hhdr_mb hdrPad (by decide), hhdr_mb hdrW (by decide),
        hhdr_mb hdrItemHi (by decide), hhdr_mb hdrQHi (by decide),
        hhdr_mb hdrValBits (by decide), hhdr_mb hdrLive (by decide),
        show s1_mb.mem (base + if st.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) = _ by
          simpa only [Nat.add_zero] using hod 0 (by decide),
        hod 1 (by decide), hod 2 (by decide), hod 3 (by decide), hod 4 (by decide)]
    obtain ⟨hhdr_mb₁, hctx_mb₁⟩ := hmb_pres h₁ hp8_1
    obtain ⟨hhdr_mb₂, hctx_mb₂⟩ := hmb_pres h₂ hp8_2
    rw [← hsch.pgHost_eq] at hctx_mb₂
    set pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s₁.mem
    have hs1_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
        ((Memory.spec 0).clientState s₁
          (migrateBatchProg
            ((((if s₁.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1),
               (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)), 0),
              itemBatchWhp))).mem (base + k) =
        ((Memory.spec 0).clientState s₂
          (migrateBatchProg
            ((((if s₁.mem (base + hdrStage) = 0 then base + hdrPBase0 else base + hdrPBase1),
               (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0)), 0),
              itemBatchWhp))).mem (base + k) := fun k hk hne =>
      (hhdr_mb₁ k hk).trans ((hsch.2 k hk hne).trans
        (by rw [← hsch.2 hdrStage (by decide) (by decide)] at hhdr_mb₂; exact (hhdr_mb₂ k hk).symm))
    rw [← hsch.2 hdrStage (by decide) (by decide)] at hctx_mb₂
    simp only [← hsch.2 hdrStage (by decide) (by decide),
      ← hsch.2 hdrRem (by decide) (by decide),
      ← hsch.2 hdrThresh (by decide) (by decide),
      ← hsch.2 hdrNSrc (by decide) (by decide),
      hctx_mb₁, hctx_mb₂]
    by_cases hr1 : 1 < s₁.mem (base + hdrRem)
    · rw [ite_eq_left hr1, ite_eq_left hr1]; dsimp only
      exact hupd_eq hdrRem _ hs1_hdr off hoff hne_ud
    · rw [ite_eq_right hr1, ite_eq_right hr1]; dsimp only
      have hbu_frm := pageBeginUnpermBoundedProg_frame pgH
      have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) h₁
        (by rw [hp8_1]; decide) (by rw [hp8_1]; decide)
      have hibHi_ge : base + 196 ≤ s₁.mem (base + hdrItemHi) := by
        have hsched₁ := h₁.sched; rw [ite_eq_right (by rw [hp8_1]; decide)] at hsched₁
        obtain ⟨_, _, _, _, hibHi_e, _⟩ := hsched₁.ge2 (by rw [hp8_1]; decide)
        rw [hibHi_e]; split_ifs <;> omega
      have hno_pg : ∀ k < 48, ¬pgH.OwnsAddr (base + k) := fun k hk hpg => by
        rcases hpg with h_m | h_i
        · have h210 := (hdisj_pg (base + k) h_m).1; omega
        · have hi1 : s₁.mem (base + hdrItemHi) ≤ base + k := h_i.1; omega
      have hs3_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
          ((Memory.spec 0).clientState _ (pageBeginUnpermBoundedProg pgH.toCtx)).mem (base + k) =
          ((Memory.spec 0).clientState _ (pageBeginUnpermBoundedProg pgH.toCtx)).mem (base + k) :=
        fun k hk hne =>
          (hbu_frm.mem_outside _ (base + k) (hno_pg k hk)).trans
            ((hs1_hdr k hk hne).trans (hbu_frm.mem_outside _ (base + k) (hno_pg k hk)).symm)
      exact hupd_eq hdrPhase 9 (hupd_eq hdrRem _ (hupd_eq hdrUnpermDone 0 hs3_hdr)) off hoff hne_ud
  · -- `ph = 9` (`tickUnpermProg`): `hdrUnpermDone` may differ, but `off ≠ hdrUnpermDone`!
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp9_1 : s₁.mem (base + hdrPhase) = 9 := hph_val
    have hp9_2 : s₂.mem (base + hdrPhase) = 9 := hph_eq.symm
    rw [(tickUnpermProg_eval base s₁).1, (tickUnpermProg_eval base s₂).1]
    dsimp only
    have hs1_pres : ∀ {st : Memory.State} {L : DualLatent c U V},
        DualMidInv c U V w base s_dict L st → st.mem (base + hdrPhase) = 9 →
        ∀ k < 48, k ≠ hdrUnpermDone →
          (if st.mem (base + hdrUnpermDone) = 0 then
             (Memory.spec 0).clientState st (stepUnpermBatchProg base)
           else st).mem (base + k) = st.mem (base + k) := by
      intro st L hm hp9 k hk hne
      by_cases hd0 : st.mem (base + hdrUnpermDone) = 0
      · rw [ite_eq_left hd0]
        obtain ⟨_, _, _, _, hctx, _, _, hv_pg, _⟩ :=
          dualPgHost_eval_valid hm (by rw [hp9]; decide) (by rw [hp9]; decide)
        have hdisj := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) hm
          (by rw [hp9]; decide) (by rw [hp9])
        have hsched := hm.sched; rw [ite_eq_right (by rw [hp9]; decide)] at hsched
        obtain ⟨_, _, _, _, hibHi_e, _⟩ := hsched.ge2 (by rw [hp9]; decide)
        have hibHi_ge : base + 196 ≤ st.mem (base + hdrItemHi) := by
          rw [hibHi_e]; split_ifs <;> omega
        set pgH_st := dualPgHost c V w base (Dictionary.dom s_dict).card st.mem
        have hub_frm := pageRunUnpermBatchProg_frame (L := pgH_st) hw_pos itemBatchWhp
        rw [(stepUnpermBatchProg_eval base st).1]
        simp only [hctx]
        have hs2_k : ((Memory.spec 0).clientState st
            (pageRunUnpermBatchProg (pgH_st.toCtx, itemBatchWhp))).mem (base + k) =
            st.mem (base + k) :=
          hub_frm.mem_outside st (base + k) fun hpg => by
            rcases hpg with h_m | h_i
            · have h210 := (hdisj (base + k) h_m).1; omega
            · have hi1 : st.mem (base + hdrItemHi) ≤ base + k := h_i.1
              omega
        by_cases hc4 : ((Memory.spec 0).clientState st
            (pageRunUnpermBatchProg (pgH_st.toCtx, itemBatchWhp))).mem (pgH_st.metaBase + 18) = 4
        · rw [ite_eq_left hc4]; dsimp only
          rw [Function.update_of_ne (base_add_ne hne), (setDirectSlotIoProg_eval _ _ _ _ _ _).1,
            (setSlotIoProg_frame _ _).mem_outside _ (base + k)
              (by dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega)]
          exact hs2_k
        · rw [ite_eq_right hc4]
          exact hs2_k
      · rw [ite_eq_right hd0]
    set s1_1 := if s₁.mem (base + hdrUnpermDone) = 0 then
      (Memory.spec 0).clientState s₁ (stepUnpermBatchProg base) else s₁
    set s1_2 := if s₂.mem (base + hdrUnpermDone) = 0 then
      (Memory.spec 0).clientState s₂ (stepUnpermBatchProg base) else s₂
    have hs1_hdr : ∀ k < 48, k ≠ hdrUnpermDone → s1_1.mem (base + k) = s1_2.mem (base + k) :=
      fun k hk hne =>
        (hs1_pres h₁ hp9_1 k hk hne).trans ((hsch.2 k hk hne).trans
          (hs1_pres h₂ hp9_2 k hk hne).symm)
    rw [← hsch.2 hdrRem (by decide) (by decide)]
    by_cases hr1 : 1 < s₁.mem (base + hdrRem)
    · rw [ite_eq_left hr1, ite_eq_left hr1]; dsimp only
      exact hupd_eq hdrRem _ hs1_hdr off hoff hne_ud
    · rw [ite_eq_right hr1, ite_eq_right hr1]
      rw [(finishUnpermProg_eval base s1_1).1, (finishUnpermProg_eval base s1_2).1]
      dsimp only
      rw [← hs1_hdr hdrStage (by decide) (by decide),
        ← hs1_hdr hdrNDst (by decide) (by decide),
        ← hs1_hdr hdrMDst (by decide) (by decide),
        ← hs1_hdr hdrLive (by decide) (by decide),
        ← hs1_hdr hdrKeyBits (by decide) (by decide),
        ← hs1_hdr hdrLogN (by decide) (by decide),
        ← hs1_hdr hdrEll (by decide) (by decide)]
      by_cases hc : s1_1.mem (base + hdrStage) = 0 ∧ 0 < s1_1.mem (base + hdrNDst)
      · rw [ite_eq_left hc, ite_eq_left hc]; dsimp only
        exact hupd_eq hdrPhase 4 (hupd_eq hdrCur 0 (hupd_eq hdrStage 1 hs1_hdr)) off hoff hne_ud
      · rw [ite_eq_right hc, ite_eq_right hc]; dsimp only
        by_cases hph_o : off = hdrPhase
        · subst hph_o; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne (base_add_ne hph_o), Function.update_of_ne (base_add_ne hph_o),
            (setSplitSlotIoProg_eval _ _ _ _).1, (setSplitSlotIoProg_eval _ _ _ _).1,
            (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + off)
              (by dsimp only [hdrPBase0]; omega),
            (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + off)
              (by dsimp only [hdrPBase0]; omega)]
          have hsm_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
              (if s1_1.mem (base + hdrStage) = 0 then
                 Function.update (Function.update (Function.update
                   (Function.update s1_1.mem (base + hdrSmallMeta0) 0)
                   (base + hdrSmallMeta0 + 1) (s1_1.mem (base + hdrLive)))
                   (base + hdrPBase0) 0)
                   (base + hdrPBase0 + 1) (base + hdrSmallMeta0)
               else s1_1.mem) (base + k) =
              (if s1_1.mem (base + hdrStage) = 0 then
                 Function.update (Function.update (Function.update
                   (Function.update s1_2.mem (base + hdrSmallMeta0) 0)
                   (base + hdrSmallMeta0 + 1) (s1_1.mem (base + hdrLive)))
                   (base + hdrPBase0) 0)
                   (base + hdrPBase0 + 1) (base + hdrSmallMeta0)
               else s1_2.mem) (base + k) := fun k hk hne => by
            by_cases hs0 : s1_1.mem (base + hdrStage) = 0
            · rw [ite_eq_left hs0, ite_eq_left hs0]
              iterate 4 rw [Function.update_of_ne
                (by dsimp only [hdrSmallMeta0, hdrPBase0]; omega)]
              symm
              iterate 4 rw [Function.update_of_ne
                (by dsimp only [hdrSmallMeta0, hdrPBase0]; omega)]
              exact (hs1_hdr k hk hne).symm
            · rw [ite_eq_right hs0, ite_eq_right hs0]
              exact hs1_hdr k hk hne
          exact hupd_eq hdrSplit 0 (hupd_eq hdrQLo _ (hupd_eq hdrItemLo _ hsm_hdr))
            off hoff hne_ud
  · -- `ph = 10` (`tickSlideDownProg`)
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    have hp10_1 : s₁.mem (base + hdrPhase) = 10 := hph_val
    have hp10_2 : s₂.mem (base + hdrPhase) = 10 := hph_eq.symm
    rw [(tickSlideDownProg_eval base s₁).1, (tickSlideDownProg_eval base s₂).1]
    let cfgOf : Memory.State → SplitPairCfg := fun st =>
      { baseLo := st.mem (base + hdrItemLo), qBitsLo := st.mem (base + hdrQLo),
        vBitsLo := valBits V, baseHi := st.mem (base + hdrItemHi),
        qBitsHi := st.mem (base + hdrQHi), vBitsHi := valBits V, w := w }
    have hcfg_eq : cfgOf s₂ = cfgOf s₁ := by
      dsimp only [cfgOf]
      rw [hsch.2 hdrItemLo (by decide) (by decide),
        hsch.2 hdrQLo (by decide) (by decide),
        hsch.2 hdrItemHi (by decide) (by decide),
        hsch.2 hdrQHi (by decide) (by decide)]
    have hsd_step : ∀ {st : Memory.State} {L : DualLatent c U V},
        DualMidInv c U V w base s_dict L st → st.mem (base + hdrPhase) = 10 →
        (Memory.spec 0).clientResult st (loadSplitPairCtxProg base) = (cfgOf st).toCtx ∧
        (Memory.spec 0).clientResult st
          (slideDownBatchProg
            ((((cfgOf st).toCtx, (Dictionary.dom s_dict).card), st.mem (base + hdrSplit)),
              itemBatchWhp)) =
          min (Dictionary.dom s_dict).card (st.mem (base + hdrSplit) + itemBatchWhp) ∧
        ∀ k < 48,
          ((Memory.spec 0).clientState st
            (slideDownBatchProg
              ((((cfgOf st).toCtx, (Dictionary.dom s_dict).card), st.mem (base + hdrSplit)),
                itemBatchWhp))).mem (base + k) = st.mem (base + k) := by
      intro st L hm hp10
      have hctx : (Memory.spec 0).clientResult st (loadSplitPairCtxProg base) =
          (cfgOf st).toCtx := by
        rw [(loadSplitPairCtxProg_eval base st).2.1]
        dsimp only [cfgOf, SplitPairCfg.toCtx]; rw [hm.hdr.2.2.2.2.1, hm.hdr.2.2.1]
      have hsched := hm.sched; rw [ite_eq_right (by rw [hp10]; decide)] at hsched
      obtain ⟨hmD_e, _, _, _, hibHi_e, hqHi_e⟩ := hsched.ge2 (by rw [hp10]; decide)
      have hibLo_e := hsched.ibLo_eq; rw [hp10, ite_eq_right (by decide : ¬(10 < 10))] at hibLo_e
      have hqLo_e := hsched.qLo_eq; rw [hp10, ite_eq_right (by decide : ¬(10 < 10))] at hqLo_e
      obtain ⟨_, hvb_w, hqLo_w, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits hm
      obtain ⟨hsp_le, hhi_quot⟩ := hm.ph10_inv hp10
      obtain ⟨_, hdict_d, hsl_d, _⟩ := hm.sl_ge9 (by rw [hp10]; decide)
      have hfr_hi_lo := (hsched.ph3_10 ⟨by rw [hp10]; decide, by rw [hp10]⟩).1
      have hq_le : st.mem (base + hdrQLo) ≤ st.mem (base + hdrQHi) := by
        rw [hqHi_e, hqLo_e]; exact le_max_right _ _
      have hib_le : st.mem (base + hdrItemLo) + 4 ≤ st.mem (base + hdrItemHi) := by
        rw [hibHi_e, hibLo_e]
        by_cases hdz : st.mem (base + hdrNDst) = 0
        · rw [ite_eq_left hdz]
          have hm0 : st.mem (base + hdrMDst) = 0 := by
            rw [hmD_e, hdz]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
          rw [hm0]; omega
        · rw [ite_eq_right hdz]; omega
      have hcfg_v : (cfgOf st).Valid w (Dictionary.dom s_dict).card st.frontier :=
        ⟨hw_pos, rfl, hqLo_w, hvb_w, hqHi_w, hvb_w,
          by dsimp only [cfgOf]; omega, by dsimp only [cfgOf]; omega,
          lt_of_le_of_lt hm.live_le hm.U_lt, hfr_hi_lo⟩
      set io_sp := splitSlotIo w (valBits V) base (st.mem (base + hdrItemLo))
        (st.mem (base + hdrQLo)) (st.mem (base + hdrItemHi)) (st.mem (base + hdrQHi))
        (Dictionary.dom s_dict).card
      have hpD_s : dualPDst base st.mem = base + hdrPBase0 := by
        unfold dualPDst; rw [hp10, ite_eq_right (by decide : ¬(10 < 10))]
      have hio_d10 : activeDstIo c w (valBits V) base (st.mem (base + hdrStage))
          (st.mem (base + hdrPhase)) (st.mem (base + hdrNSrc)) (st.mem (base + hdrNDst))
          (st.mem (base + hdrPad)) (st.mem (base + hdrItemLo)) (st.mem (base + hdrQLo))
          (st.mem (base + hdrItemHi)) (st.mem (base + hdrQHi)) (Dictionary.dom s_dict).card
          (st.mem (base + hdrUnpermDone)) = io_sp := by
        rw [hp10]; unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
      have hsl_d0 : EpochSlotInv c U V w st.frontier (base + hdrPBase0) (dualMbDst base st.mem)
          io_sp 0 false L.slotDst st.mem := by
        rw [hpD_s, hio_d10] at hsl_d
        simpa only [hp10, Nat.reduceEqDiff, false_and, and_false, ↓reduceIte] using hsl_d
      have hns_d : st.mem (dualMbDst base st.mem + 1) = (Dictionary.dom s_dict).card := by
        rw [hsl_d0.mem_nSide_eq, ← dom_toDictState_card, hdict_d]
      have hfit : ∀ d, st.mem (base + hdrSplit) ≤ d →
          d < min (Dictionary.dom s_dict).card (st.mem (base + hdrSplit) + itemBatchWhp) →
          (splitPairRead (cfgOf st) (st.mem (base + hdrSplit)) st.mem d).1 <
            2 ^ (cfgOf st).qBitsLo ∧
          (splitPairRead (cfgOf st) (st.mem (base + hdrSplit)) st.mem d).2 <
            2 ^ (cfgOf st).vBitsLo := fun d hd_lo hd_hi => by
        have hd_lt : d < (Dictionary.dom s_dict).card := lt_of_lt_of_le hd_hi (min_le_left _ _)
        have hq_b := hhi_quot d hd_lo hd_lt
        have hv_b : (slotIoPairAt io_sp st.mem d).2 < V :=
          (hsl_d0.slot_pair_bounds (hns_d.symm ▸ hd_lt)).2
        have hv_pow : V ≤ 2 ^ valBits V := Nat.le_pow_clog (by decide : 1 < 2) V
        unfold slotIoPairAt at hv_b
        dsimp only [io_sp, splitSlotIo, SlotIoLayout.splitCfg] at hv_b
        simp only [↓reduceIte, one_ne_zero] at hv_b
        change (splitPairRead (cfgOf st) (st.mem (base + hdrSplit)) st.mem d).2 < V at hv_b
        unfold splitPairRead at hv_b ⊢
        rw [ite_eq_right (Nat.not_lt.mpr hd_lo)] at hv_b ⊢
        exact ⟨hq_b, lt_of_lt_of_le hv_b hv_pow⟩
      obtain ⟨_, hres_sb, _, _, _, hout_sb⟩ :=
        slideDownBatchProg_spec (cfg := cfgOf st) (n_tot := (Dictionary.dom s_dict).card)
          (s_split := st.mem (base + hdrSplit)) (s := st) hcfg_v hsp_le itemBatchWhp hfit
      refine ⟨hctx, hres_sb, fun k hk => ?_⟩
      have hibLo_192 : base + 192 ≤ (cfgOf st).baseLo := by
        dsimp only [cfgOf]; rw [hibLo_e]; omega
      exact hout_sb (base + k) (by omega)
    obtain ⟨hctx₁, hres_sd₁, hout_sd₁⟩ := hsd_step h₁ hp10_1
    obtain ⟨hctx₂, hres_sd₂, hout_sd₂⟩ := hsd_step h₂ hp10_2
    rw [hcfg_eq, (hsch.2 hdrSplit (by decide) (by decide)).symm] at *
    simp only [hctx₁, hctx₂, h₁.live_eq, h₂.live_eq,
      ← hsch.2 hdrItemLo (by decide) (by decide),
      ← hsch.2 hdrQLo (by decide) (by decide),
      hres_sd₁, hres_sd₂]
    have hs2_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
        ((Memory.spec 0).clientState s₁
          (slideDownBatchProg
            ((((cfgOf s₁).toCtx, (Dictionary.dom s_dict).card), s₁.mem (base + hdrSplit)),
              itemBatchWhp))).mem (base + k) =
        ((Memory.spec 0).clientState s₂
          (slideDownBatchProg
            ((((cfgOf s₁).toCtx, (Dictionary.dom s_dict).card), s₁.mem (base + hdrSplit)),
              itemBatchWhp))).mem (base + k) := fun k hk hne =>
      (hout_sd₁ k hk).trans ((hsch.2 k hk hne).trans (hout_sd₂ k hk).symm)
    have hs3_hdr := hupd_eq hdrSplit
      (min (Dictionary.dom s_dict).card (s₁.mem (base + hdrSplit) + itemBatchWhp)) hs2_hdr
    by_cases hc_sd : (Dictionary.dom s_dict).card ≤
        min (Dictionary.dom s_dict).card (s₁.mem (base + hdrSplit) + itemBatchWhp)
    · rw [ite_eq_left hc_sd, ite_eq_left hc_sd]
      dsimp only
      by_cases hph_o : off = hdrPhase
      · subst hph_o; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (base_add_ne hph_o), Function.update_of_ne (base_add_ne hph_o),
          (setDirectSlotIoProg_eval _ _ _ _ _ _).1, (setDirectSlotIoProg_eval _ _ _ _ _ _).1,
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + off)
            (by dsimp only [hdrPBase0]; omega),
          (setSlotIoProg_frame (base + hdrPBase0) _).mem_outside _ (base + off)
            (by dsimp only [hdrPBase0]; omega)]
        exact hs3_hdr off hoff hne_ud
    · rw [ite_eq_right hc_sd, ite_eq_right hc_sd]
      exact hs3_hdr off hoff hne_ud
  · -- `ph = 11`: no-op!
    simp only [Nat.reduceEqDiff, ↓reduceIte]
    exact hsch.2 off hoff hne_ud

/-- Clearing trailing words `[fr - k_sh, fr)` above `base + 192` preserves `SchedEq`. -/
private theorem SchedEq.clear_shrink {base k_sh : ℕ} {s₁ s₂ : Memory.State}
    (hsch : SchedEq base s₁ s₂) (hb192 : base + 192 ≤ s₁.frontier - k_sh) :
    SchedEq base
      { mem := clear s₁.mem (s₁.frontier - k_sh) k_sh, frontier := s₁.frontier - k_sh }
      { mem := clear s₂.mem (s₂.frontier - k_sh) k_sh, frontier := s₂.frontier - k_sh } := by
  refine ⟨by dsimp only; rw [hsch.1], fun off hoff hne => ?_⟩
  dsimp only
  have hn1 : ¬(Block.mk (s₁.frontier - k_sh) k_sh).Owns (base + off) := by
    simp only [Block.Owns]; omega
  have hn2 : ¬(Block.mk (s₂.frontier - k_sh) k_sh).Owns (base + off) := by
    rw [← hsch.1]; exact hn1
  rw [clear_of_not_owns hn1, clear_of_not_owns hn2]
  exact hsch.2 off hoff hne

/-- `calcPostShrinkProg` + `clear` preserves `SchedEq` and produces identical `k_sh` across any two
`DualPreShrinkInv` states sharing `s_dict` and `SchedEq`. -/
private theorem schedEq_calcPostShrink {c U V w base : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V} {s₁ s₂ : Memory.State}
    (hpre₁ : DualPreShrinkInv c U V w base s_dict L₁ s₁)
    (hpre₂ : DualPreShrinkInv c U V w base s_dict L₂ s₂)
    (hsch : SchedEq base s₁ s₂) :
    let s_ps₁ := (Memory.spec 0).clientState s₁ (calcPostShrinkProg (base, s₁.frontier))
    let s_ps₂ := (Memory.spec 0).clientState s₂ (calcPostShrinkProg (base, s₂.frontier))
    let k_sh₁ := (Memory.spec 0).clientResult s₁ (calcPostShrinkProg (base, s₁.frontier))
    let k_sh₂ := (Memory.spec 0).clientResult s₂ (calcPostShrinkProg (base, s₂.frontier))
    k_sh₁ = k_sh₂ ∧
    SchedEq base
      { mem := clear s_ps₁.mem (s₁.frontier - k_sh₁) k_sh₁, frontier := s₁.frontier - k_sh₁ }
      { mem := clear s_ps₂.mem (s₂.frontier - k_sh₂) k_sh₂, frontier := s₂.frontier - k_sh₂ } := by
  dsimp only
  obtain ⟨hfr_ps₁, _, _, _, _, L_post₁, _, hinv_post₁, _⟩ := calcPostShrinkProg_spec hpre₁
  obtain ⟨hfr_ps₂, _, _, _, _, _, _, _, _⟩ := calcPostShrinkProg_spec hpre₂
  have hb192 : base + 192 ≤
      s₁.frontier - (Memory.spec 0).clientResult s₁ (calcPostShrinkProg (base, s₁.frontier)) :=
    hinv_post₁.base_fr
  -- Extract `hdrW` and `hdrValBits` and `hdrLive` from `DualPreShrinkInv`
  have hhdr_vals : ∀ {st : Memory.State} {L : DualLatent c U V},
      DualPreShrinkInv c U V w base s_dict L st →
      11 ≤ w ∧ st.mem (base + hdrW) = w ∧ st.mem (base + hdrValBits) = valBits V ∧
      st.mem (base + hdrLive) = (Dictionary.dom s_dict).card := by
    intro st L hp
    obtain ⟨_, _, _, hbr⟩ := hp
    have from_c : ∀ {isMid : Bool} {fr' : ℕ} {L' : DualLatent c U V},
        DualCoreInv isMid c U V w base s_dict L' { mem := st.mem, frontier := fr' } →
        11 ≤ w ∧ st.mem (base + hdrW) = w ∧ st.mem (base + hdrValBits) = valBits V ∧
        st.mem (base + hdrLive) = (Dictionary.dom s_dict).card :=
      fun hc => ⟨hc.hw11, hc.hdr.2.2.1, hc.hdr.2.2.2.2.1, hc.live_eq⟩
    by_cases hlt2 : st.mem (base + hdrPhase) < 2
    · rw [ite_eq_left hlt2] at hbr; exact from_c hbr.2.2
    · rw [ite_eq_right hlt2] at hbr
      by_cases hp2 : st.mem (base + hdrPhase) = 2
      · rw [ite_eq_left hp2] at hbr; exact from_c hbr.2
      · rw [ite_eq_right hp2] at hbr
        by_cases hle10 : st.mem (base + hdrPhase) ≤ 10
        · rw [ite_eq_left hle10] at hbr; exact from_c hbr.2.2
        · rw [ite_eq_right hle10] at hbr
          by_cases hb : bulkBatchWhp < st.frontier -
              (st.mem (base + hdrItemLo) +
                pairStreamWords (Dictionary.dom s_dict).card (st.mem (base + hdrQLo))
                  (valBits V) w)
          · exact from_c (hbr.2.2.1 hb)
          · exact from_c (hbr.2.2.2 (Nat.not_lt.mp hb)).1
  obtain ⟨hw11, hw_1, hvb_1, hlv_1⟩ := hhdr_vals hpre₁
  obtain ⟨_, hw_2, hvb_2, hlv_2⟩ := hhdr_vals hpre₂
  have hw_pos : 0 < w := by omega
  obtain ⟨hst_c₁, hres_c₁, _⟩ := calcPostShrinkProg_eval (curFr := s₁.frontier) (hw_1 ▸ hw_pos)
  obtain ⟨hst_c₂, hres_c₂, _⟩ := calcPostShrinkProg_eval (curFr := s₂.frontier) (hw_2 ▸ hw_pos)
  dsimp only at hst_c₁ hres_c₁ hst_c₂ hres_c₂
  have hk_eq : (Memory.spec 0).clientResult s₁ (calcPostShrinkProg (base, s₁.frontier)) =
      (Memory.spec 0).clientResult s₂ (calcPostShrinkProg (base, s₂.frontier)) := by
    rw [hres_c₁, hres_c₂, hw_1, hw_2, hvb_1, hvb_2, hlv_1, hlv_2, hsch.1,
      hsch.2 hdrPhase (by decide) (by decide),
      hsch.2 hdrItemLo (by decide) (by decide),
      hsch.2 hdrItemHi (by decide) (by decide),
      hsch.2 hdrQLo (by decide) (by decide),
      hsch.2 hdrQHi (by decide) (by decide)]
  rw [← hk_eq]
  refine ⟨rfl, ?_⟩
  have hsch_ps : SchedEq base
      ((Memory.spec 0).clientState s₁ (calcPostShrinkProg (base, s₁.frontier)))
      ((Memory.spec 0).clientState s₂ (calcPostShrinkProg (base, s₂.frontier))) := by
    refine ⟨hfr_ps₁.trans (hsch.1.trans hfr_ps₂.symm), fun off hoff hne_ud => ?_⟩
    rw [hst_c₁, hst_c₂, hw_1, hw_2, hvb_1, hvb_2, hlv_1, hlv_2, ← hsch.1,
      ← hsch.2 hdrPhase (by decide) (by decide),
      ← hsch.2 hdrItemLo (by decide) (by decide),
      ← hsch.2 hdrQLo (by decide) (by decide)]
    split_ifs with hc11
    · rw [(finishShrinkPostProg_eval base s₁).1, (finishShrinkPostProg_eval base s₂).1]
      dsimp only
      rw [← hsch.2 hdrNDst (by decide) (by decide),
        ← hsch.2 hdrMDst (by decide) (by decide),
        ← hsch.2 hdrItemLo (by decide) (by decide),
        ← hsch.2 hdrQLo (by decide) (by decide)]
      have hupd_eq : ∀ {m₁ m₂ : ℕ → ℕ} (o v : ℕ),
          (∀ k < 48, k ≠ hdrUnpermDone → m₁ (base + k) = m₂ (base + k)) →
          ∀ k < 48, k ≠ hdrUnpermDone →
            Function.update m₁ (base + o) v (base + k) =
              Function.update m₂ (base + o) v (base + k) :=
        fun o v hm k hk hne => by
          by_cases hko : k = o
          · subst hko; rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne (base_add_ne hko), Function.update_of_ne (base_add_ne hko)]
            exact hm k hk hne
      have hs1_hdr : ∀ k < 48, k ≠ hdrUnpermDone →
          (if 0 < s₁.mem (base + hdrNDst) then
             (Memory.spec 0).clientState s₁ (copyDstToSrcHostProg base)
           else s₁).mem (base + k) =
          (if 0 < s₁.mem (base + hdrNDst) then
             (Memory.spec 0).clientState s₂ (copyDstToSrcHostProg base)
           else s₂).mem (base + k) := fun k hk hne => by
        split_ifs
        · have hcp₁ := copyDstToSrcHostProg_spec base s₁
          have hcp₂ := copyDstToSrcHostProg_spec base s₂
          dsimp only at hcp₁ hcp₂
          by_cases h38 : 38 ≤ k ∧ k < 43
          · obtain ⟨hlo, hhi⟩ := h38
            interval_cases k
            · exact hcp₁.2.2.1.trans
                ((hsch.2 hdrDstOd (by decide) (by decide)).trans hcp₂.2.2.1.symm)
            · exact hcp₁.2.2.2.1.trans
                ((hsch.2 hdrDstOt (by decide) (by decide)).trans hcp₂.2.2.2.1.symm)
            · exact hcp₁.2.2.2.2.1.trans
                ((hsch.2 hdrDstPb (by decide) (by decide)).trans hcp₂.2.2.2.2.1.symm)
            · exact hcp₁.2.2.2.2.2.1.trans
                ((hsch.2 hdrDstPg (by decide) (by decide)).trans hcp₂.2.2.2.2.2.1.symm)
            · exact hcp₁.2.2.2.2.2.2.1.trans
                ((hsch.2 hdrDstMp (by decide) (by decide)).trans hcp₂.2.2.2.2.2.2.1.symm)
          · exact (hcp₁.2.2.2.2.2.2.2 (base + k) (by omega)).trans
              ((hsch.2 k hk hne).trans (hcp₂.2.2.2.2.2.2.2 (base + k) (by omega)).symm)
        · exact hsch.2 k hk hne
      exact hupd_eq hdrPhase 0 (hupd_eq hdrQHi _ (hupd_eq hdrItemHi _
        (hupd_eq hdrEpochOps 0 (hupd_eq hdrStage 0 (hupd_eq hdrMDst 0
          (hupd_eq hdrNDst 0 (hupd_eq hdrMSrc _ (hupd_eq hdrNSrc _ hs1_hdr))))))))
        off hoff hne_ud
    · exact hsch.2 off hoff hne_ud
  have hclr := hsch_ps.clear_shrink
    (k_sh := (Memory.spec 0).clientResult s₁ (calcPostShrinkProg (base, s₁.frontier)))
    (hfr_ps₁.symm ▸ hb192)
  rwa [hfr_ps₁, hfr_ps₂] at hclr

/-- `postRandShrinkProg` + `clear` preserves `SchedEq` and produces identical `k_sh` on
`DualPreShrinkInv` states (`opTag ≠ 0`). -/
private theorem schedEq_postShrink_pre {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V} {s₁ s₂ : Memory.State}
    (hop_nz : opTag ≠ 0)
    (hpre₁ : DualPreShrinkInv c U V w base s_dict L₁ s₁)
    (hpre₂ : DualPreShrinkInv c U V w base s_dict L₂ s₂)
    (hsch : SchedEq base s₁ s₂) :
    let s_ps₁ := (Memory.spec 0).clientState s₁ (postRandShrinkProg ((base, s₁.frontier), opTag))
    let s_ps₂ := (Memory.spec 0).clientState s₂ (postRandShrinkProg ((base, s₂.frontier), opTag))
    let k_sh₁ := (Memory.spec 0).clientResult s₁ (postRandShrinkProg ((base, s₁.frontier), opTag))
    let k_sh₂ := (Memory.spec 0).clientResult s₂ (postRandShrinkProg ((base, s₂.frontier), opTag))
    k_sh₁ = k_sh₂ ∧
    SchedEq base
      { mem := clear s_ps₁.mem (s₁.frontier - k_sh₁) k_sh₁, frontier := s₁.frontier - k_sh₁ }
      { mem := clear s_ps₂.mem (s₂.frontier - k_sh₂) k_sh₂, frontier := s₂.frontier - k_sh₂ } := by
  dsimp only
  have hnot_rf : ∀ {st : Memory.State} {L : DualLatent c U V},
      DualPreShrinkInv c U V w base s_dict L st →
      ¬(st.mem (base + hdrPhase) = 5 ∧
        st.mem ((if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) +
          31) ≤ st.mem (base + hdrCur)) := by
    rintro st L hp ⟨hp5, hle⟩
    have hpD : (if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
        dualPDst base st.mem := by
      unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
    rw [hpD] at hle
    exact absurd (lt_of_lt_of_le (hp.2.2.1 hp5) hle) (Nat.lt_irrefl _)
  obtain ⟨hst₁, hres₁, _⟩ := postRandShrinkProg_eval base s₁.frontier opTag s₁
  obtain ⟨hst₂, hres₂, _⟩ := postRandShrinkProg_eval base s₂.frontier opTag s₂
  dsimp only at hst₁ hres₁ hst₂ hres₂
  rw [ite_eq_right hop_nz, ite_eq_right (hnot_rf hpre₁)] at hst₁ hres₁
  rw [ite_eq_right hop_nz, ite_eq_right (hnot_rf hpre₂)] at hst₂ hres₂
  rw [hst₁, hst₂, hres₁, hres₂]
  exact schedEq_calcPostShrink hpre₁ hpre₂ hsch

/-- `postRandShrinkProg` + `clear` preserves `SchedEq` and produces identical `k_sh` at `ph = 5`
completion (`endOff = offBM`). -/
private theorem schedEq_postShrink_rf {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V} {s₁ s₂ : Memory.State}
    (hop_nz : opTag ≠ 0)
    (h₁ : DualMidInv c U V w base s_dict L₁ s₁)
    (h₂ : DualMidInv c U V w base s_dict L₂ s₂)
    (hp5_1 : s₁.mem (base + hdrPhase) = 5)
    (hdone_1 : s₁.mem (dualPDst base s₁.mem + 31) ≤ s₁.mem (base + hdrCur))
    (hsch : SchedEq base s₁ s₂) :
    let s_ps₁ := (Memory.spec 0).clientState s₁ (postRandShrinkProg ((base, s₁.frontier), opTag))
    let s_ps₂ := (Memory.spec 0).clientState s₂ (postRandShrinkProg ((base, s₂.frontier), opTag))
    let k_sh₁ := (Memory.spec 0).clientResult s₁ (postRandShrinkProg ((base, s₁.frontier), opTag))
    let k_sh₂ := (Memory.spec 0).clientResult s₂ (postRandShrinkProg ((base, s₂.frontier), opTag))
    k_sh₁ = k_sh₂ ∧
    SchedEq base
      { mem := clear s_ps₁.mem (s₁.frontier - k_sh₁) k_sh₁, frontier := s₁.frontier - k_sh₁ }
      { mem := clear s_ps₂.mem (s₂.frontier - k_sh₂) k_sh₂, frontier := s₂.frontier - k_sh₂ } := by
  dsimp only
  have hp5_2 : s₂.mem (base + hdrPhase) = 5 :=
    (hsch.2 hdrPhase (by decide) (by decide)).symm.trans hp5_1
  have hp31_eq : ∀ {st : Memory.State} {L : DualLatent c U V},
      DualMidInv c U V w base s_dict L st → st.mem (base + hdrPhase) = 5 →
      st.mem (dualPDst base st.mem + 31) = offBktMeta c w (st.mem (base + hdrNDst)) := by
    intro st L hm hp5
    have h31 := (hm.ph5_inv hp5).2.2.2.1 31 (by decide)
    dsimp only [FastEpochLayout.paramWord] at h31
    rwa [dualPh5MaskMem_lt48 _ _ _ _ _ _ _ _ (by decide : 31 < 48)] at h31
  have hdone_2 : s₂.mem (dualPDst base s₂.mem + 31) ≤ s₂.mem (base + hdrCur) := by
    rw [hp31_eq h₂ hp5_2, ← hsch.2 hdrNDst (by decide) (by decide), ← hp31_eq h₁ hp5_1,
      ← hsch.2 hdrCur (by decide) (by decide)]
    exact hdone_1
  obtain ⟨hpre_rf₁, hfr_rf₁, _, _, _, hpre_sh₁⟩ := finishRandFillProg_spec h₁ hp5_1 hdone_1
  obtain ⟨hpre_rf₂, hfr_rf₂, _, _, _, hpre_sh₂⟩ := finishRandFillProg_spec h₂ hp5_2 hdone_2
  -- Show `SchedEq base s_rf₁ s_rf₂`
  have hrf_hdr : ∀ {st : Memory.State} {L : DualLatent c U V},
      DualMidInv c U V w base s_dict L st → st.mem (base + hdrPhase) = 5 →
      FinishRandFillPre w base st →
      ∀ k < 48, k ≠ hdrPhase → k ≠ hdrCur →
        ((Memory.spec 0).clientState st (finishRandFillProg base)).mem (base + k) =
          st.mem (base + k) := by
    intro st L hm hp5 hprf k hk hph hc
    rw [(finishRandFillProg_eval base st).1]
    dsimp only
    rw [Function.update_of_ne (base_add_ne hph), Function.update_of_ne (base_add_ne hc)]
    -- Extract `FastLayoutReady` from `FinishRandFillPre`!
    obtain ⟨_, _, _, _, _, _, hepre⟩ := hprf
    dsimp only at hepre
    set pD := if st.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0
    set md := if st.mem (base + hdrStage) = 0 then base + 192 + st.mem (base + hdrPad)
      else base + 192
    set mask_st := ((1 : ℕ) <<< (st.mem (base + hdrRedW) - 1)) - 1
    set s1_st : Memory.State :=
      { mem := Function.update
          (Function.update st.mem (md + 32) (st.mem (md + 32) &&& mask_st))
          (md + st.mem (pD + 30)) (st.mem (md + st.mem (pD + 30)) &&& mask_st)
        frontier := st.frontier }
    set s2_st := (Memory.spec 0).clientState s1_st
      (setDirectSlotIoProg
        ((base, pD), ((st.mem (base + hdrItemHi), st.mem (base + hdrQHi)),
          st.mem (base + hdrLive))))
    have hd_pos : 0 < st.mem (base + hdrNDst) := (hm.ph5_inv hp5).1
    have hpD_0 : s2_st.mem pD = st.mem (base + hdrNDst) := by
      dsimp only [s2_st]
      rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1,
        (setSlotIoProg_frame pD _).mem_outside _ pD (by omega)]
      dsimp only [s1_st, md]
      rw [Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega),
        Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega)]
      have hpD_d : pD = dualPDst base st.mem := by
        dsimp only [pD]; unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
      rw [hpD_d]
      have h0 := (hm.ph5_inv hp5).2.2.2.1 0 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h0
      rw [dualPh5MaskMem_lt48 _ _ _ _ _ _ _ _ (by decide : 0 < 48)] at h0
      simpa only [Nat.add_zero] using h0
    unfold EpochProgPre at hepre
    rcases hepre with ⟨hz, _⟩ | ⟨_, fl_st, hpB_e, hr_s2⟩
    · exact absurd (hpD_0.symm.trans hz) hd_pos.ne'
    · have hmconf := epochInitZeroedProg_meta_confine hr_s2
      have hmb_fl : fl_st.metaBase = md := by
        have h1 := hr_s2.2.1 1 (by decide)
        dsimp only [FastEpochLayout.paramWord, s2_st] at h1
        rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1,
          (setSlotIoProg_frame pD _).mem_outside _ (fl_st.pBase + 1)
            (by rw [hpB_e]; omega)] at h1
        dsimp only [s1_st, md] at h1 ⊢
        rw [hpB_e] at h1
        rw [Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega),
          Function.update_of_ne (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega)]
          at h1
        have hpD_d : pD = dualPDst base st.mem := by
          dsimp only [pD]; unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
        have h1' := (hm.ph5_inv hp5).2.2.2.1 1 (by decide)
        dsimp only [FastEpochLayout.paramWord] at h1'
        rw [dualPh5MaskMem_lt48 _ _ _ _ _ _ _ _ (by decide : 1 < 48)] at h1'
        rw [← hpD_d] at h1'
        have hmb_d : dualMbDst base st.mem = md := by
          unfold dualMbDst; rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
        exact h1.symm.trans (h1'.trans hmb_d)
      have hmd_192 : base + 192 ≤ fl_st.metaBase := by
        rw [hmb_fl]; dsimp only [md]; split_ifs <;> omega
      rw [← hpB_e, hmconf (base + k) (by omega)]
      dsimp only [s2_st]
      rw [(setDirectSlotIoProg_eval _ _ _ _ _ _).1,
        (setSlotIoProg_frame pD _).mem_outside _ (base + k)
          (by dsimp only [pD, hdrPBase0, hdrPBase1]; split_ifs <;> omega)]
      dsimp only [s1_st, md]
      have hmd_lo : base + 192 ≤ md := by dsimp only [md]; split_ifs <;> omega
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  set s_rf₁ := (Memory.spec 0).clientState s₁ (finishRandFillProg base)
  set s_rf₂ := (Memory.spec 0).clientState s₂ (finishRandFillProg base)
  have hsch_rf : SchedEq base s_rf₁ s_rf₂ := by
    refine ⟨hfr_rf₁.trans (hsch.1.trans hfr_rf₂.symm), fun off hoff hne_ud => ?_⟩
    by_cases hph_o : off = hdrPhase
    · subst hph_o
      dsimp only [s_rf₁, s_rf₂]
      rw [(finishRandFillProg_eval base s₁).1, (finishRandFillProg_eval base s₂).1]
      dsimp only; rw [Function.update_self, Function.update_self]
    · by_cases hc_o : off = hdrCur
      · subst hc_o
        dsimp only [s_rf₁, s_rf₂]
        rw [(finishRandFillProg_eval base s₁).1, (finishRandFillProg_eval base s₂).1]
        dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)), Function.update_self,
          Function.update_of_ne (base_add_ne (by decide)), Function.update_self]
      · exact (hrf_hdr h₁ hp5_1 hpre_rf₁ off hoff hph_o hc_o).trans
          ((hsch.2 off hoff hne_ud).trans (hrf_hdr h₂ hp5_2 hpre_rf₂ off hoff hph_o hc_o).symm)
  have hpD₁ : (if s₁.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
      dualPDst base s₁.mem := by
    unfold dualPDst; rw [hp5_1, ite_eq_left (by decide : 5 < 10)]
  have hpD₂ : (if s₂.mem (base + hdrStage) = 0 then base + hdrPBase1 else base + hdrPBase0) =
      dualPDst base s₂.mem := by
    unfold dualPDst; rw [hp5_2, ite_eq_left (by decide : 5 < 10)]
  obtain ⟨hst₁, hres₁, _⟩ := postRandShrinkProg_eval base s₁.frontier opTag s₁
  obtain ⟨hst₂, hres₂, _⟩ := postRandShrinkProg_eval base s₂.frontier opTag s₂
  dsimp only at hst₁ hres₁ hst₂ hres₂
  rw [ite_eq_right hop_nz, hpD₁, ite_eq_left ⟨hp5_1, hdone_1⟩] at hst₁ hres₁
  rw [ite_eq_right hop_nz, hpD₂, ite_eq_left ⟨hp5_2, hdone_2⟩] at hst₂ hres₂
  rw [hst₁, hst₂, hres₁, hres₂, ← hfr_rf₁, ← hfr_rf₂]
  exact schedEq_calcPostShrink hpre_sh₁ hpre_sh₂ hsch_rf

/-- End-to-end single-mutation `SchedEq` theorem across all 12 phases (`0..11`), including
arbitrary `writeWords` random batches in Phase `5`. -/
theorem schedEq_mutate_step {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L₁ L₂ : DualLatent c U V} {s₁ s₂ : Memory.State}
    (h₁ : DualStateInv c U V w base s_dict L₁ s₁)
    (h₂ : DualStateInv c U V w base s_dict L₂ s₂)
    (hsch : SchedEq base s₁ s₂)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hsucc_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w
        (Dictionary.dom s_dict').card < 2 ^ w)
    (hpad_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s₁.mem (base + hdrNSrc))
        (if s₁.mem (base + hdrPhase) = 0 then s₁.mem (base + hdrNSrc)
         else s₁.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w) :
    let k_grow₁ :=
      (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
    let k_grow₂ :=
      (Memory.spec 0).clientResult s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
    let s_prep₁ :=
      (Memory.spec 0).clientState s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
    let s_prep₂ :=
      (Memory.spec 0).clientState s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
    let s_grow₁ : Memory.State := { mem := s_prep₁.mem, frontier := s₁.frontier + k_grow₁ }
    let s_grow₂ : Memory.State := { mem := s_prep₂.mem, frontier := s₂.frontier + k_grow₂ }
    let s_tick₁ :=
      (Memory.spec 0).clientState s_grow₁ (stepOpProg (((base, s_grow₁.frontier), opTag),
        (u.val, v_val)))
    let s_tick₂ :=
      (Memory.spec 0).clientState s_grow₂ (stepOpProg (((base, s_grow₂.frontier), opTag),
        (u.val, v_val)))
    let res₁ :=
      (Memory.spec 0).clientResult s_grow₁ (stepOpProg (((base, s_grow₁.frontier), opTag),
        (u.val, v_val)))
    let res₂ :=
      (Memory.spec 0).clientResult s_grow₂ (stepOpProg (((base, s_grow₂.frontier), opTag),
        (u.val, v_val)))
    k_grow₁ = k_grow₂ ∧
    res₁.2 = res₂.2 ∧
    SchedEq base s_tick₁ s_tick₂ ∧
    (s₁.mem (base + hdrPhase) ≠ 5 →
      let s_ps₁ := (Memory.spec 0).clientState s_tick₁
        (postRandShrinkProg ((base, s_tick₁.frontier), opTag))
      let s_ps₂ := (Memory.spec 0).clientState s_tick₂
        (postRandShrinkProg ((base, s_tick₂.frontier), opTag))
      let k_sh₁ := (Memory.spec 0).clientResult s_tick₁
        (postRandShrinkProg ((base, s_tick₁.frontier), opTag))
      let k_sh₂ := (Memory.spec 0).clientResult s_tick₂
        (postRandShrinkProg ((base, s_tick₂.frontier), opTag))
      k_sh₁ = k_sh₂ ∧
      SchedEq base
        { mem := clear s_ps₁.mem (s_tick₁.frontier - k_sh₁) k_sh₁
          frontier := s_tick₁.frontier - k_sh₁ }
        { mem := clear s_ps₂.mem (s_tick₂.frontier - k_sh₂) k_sh₂
          frontier := s_tick₂.frontier - k_sh₂ }) ∧
    (s₁.mem (base + hdrPhase) = 5 →
      let cur := s₁.mem (base + hdrCur)
      let nDst := s₁.mem (base + hdrNDst)
      let offBM := offBktMeta c w nDst
      let endOff := cur + min bulkBatchWhp (offBM - cur)
      let metaDst := dualMbDst base s₁.mem
      ∀ ws₁ ws₂ : Fin (endOff - cur) → Fin (2 ^ w),
        let s_r₁ : Memory.State :=
          { mem := writeWords s_tick₁.mem (metaDst + cur) ws₁, frontier := s_tick₁.frontier }
        let s_r₂ : Memory.State :=
          { mem := writeWords s_tick₂.mem (metaDst + cur) ws₂, frontier := s_tick₂.frontier }
        let s_ps₁ := (Memory.spec 0).clientState s_r₁
          (postRandShrinkProg ((base, s_r₁.frontier), opTag))
        let s_ps₂ := (Memory.spec 0).clientState s_r₂
          (postRandShrinkProg ((base, s_r₂.frontier), opTag))
        let k_sh₁ := (Memory.spec 0).clientResult s_r₁
          (postRandShrinkProg ((base, s_r₁.frontier), opTag))
        let k_sh₂ := (Memory.spec 0).clientResult s_r₂
          (postRandShrinkProg ((base, s_r₂.frontier), opTag))
        k_sh₁ = k_sh₂ ∧
        SchedEq base
          { mem := clear s_ps₁.mem (s_r₁.frontier - k_sh₁) k_sh₁
            frontier := s_r₁.frontier - k_sh₁ }
          { mem := clear s_ps₂.mem (s_r₂.frontier - k_sh₂) k_sh₂
            frontier := s_r₂.frontier - k_sh₂ }) := by
  dsimp only
  have hpad₂ :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s₂.mem (base + hdrNSrc))
        (if s₂.mem (base + hdrPhase) = 0 then s₂.mem (base + hdrNSrc)
         else s₂.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w := by
    dsimp only at hpad_fits' ⊢
    rwa [← hsch.2 hdrNSrc (by decide) (by decide),
      ← hsch.2 hdrPhase (by decide) (by decide),
      ← hsch.2 hdrNDst (by decide) (by decide)]
  obtain ⟨hkg_eq, _, hsch_mid⟩ := schedEq_foreground h₁ h₂ hsch hop_nz u v hv_eq
  have hm_sp₁ := stepOpProg_mutate_spec h₁ hop_nz u v hv_eq hsucc_fits' hpad_fits'
  have hm_sp₂ := stepOpProg_mutate_spec h₂ hop_nz u v hv_eq hsucc_fits' hpad₂
  dsimp only at hm_sp₁ hm_sp₂
  set k_grow := (Memory.spec 0).clientResult s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
  rw [← hkg_eq] at hm_sp₂ hsch_mid ⊢
  set s_prep₁ :=
    (Memory.spec 0).clientState s₁ (prepGrowProg (((base, s₁.frontier), opTag), u.val))
  set s_prep₂ :=
    (Memory.spec 0).clientState s₂ (prepGrowProg (((base, s₂.frontier), opTag), u.val))
  set s_grow₁ : Memory.State := { mem := s_prep₁.mem, frontier := s₁.frontier + k_grow }
  set s_grow₂ : Memory.State := { mem := s_prep₂.mem, frontier := s₂.frontier + k_grow }
  set s_mid₁ :=
    (Memory.spec 0).clientState s_grow₁ (userMutateProg ((base, opTag), (u.val, v_val)))
  set s_mid₂ :=
    (Memory.spec 0).clientState s_grow₂ (userMutateProg ((base, opTag), (u.val, v_val)))
  have hmid₁ := hm_sp₁.2.2.2.2.2.2.2.2.2.2.1
  have hmid₂ := hm_sp₂.2.2.2.2.2.2.2.2.2.2.1
  have hpt₁ := hm_sp₁.2.2.2.2.2.2.2.2.2.2.2.1
  have hpt₂ := hm_sp₂.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hr_bg, hsch_bg⟩ := schedEq_bgTick hmid₁ hmid₂ hsch_mid hsucc_fits'
  obtain ⟨hst_so₁, hres_so₁, _⟩ :=
    stepOpProg_eval base s_grow₁.frontier opTag u.val v_val s_grow₁
  obtain ⟨hst_so₂, hres_so₂, _⟩ :=
    stepOpProg_eval base s_grow₂.frontier opTag u.val v_val s_grow₂
  rw [ite_eq_right hop_nz] at hst_so₁ hres_so₁ hst_so₂ hres_so₂
  have hfr_m₁ : s_mid₁.frontier = s_grow₁.frontier :=
    (prepGrow_userMutate_spec h₁ hop_nz u v hv_eq hpad_fits').2.2.2.2.2.2.2.1
  have hfr_m₂ : s_mid₂.frontier = s_grow₂.frontier := by
    have hf := (prepGrow_userMutate_spec h₂ hop_nz u v hv_eq hpad₂).2.2.2.2.2.2.2.1
    dsimp only at hf; rwa [← hkg_eq] at hf
  have htick_eq₁ : (Memory.spec 0).clientState s_grow₁
      (stepOpProg (((base, s_grow₁.frontier), opTag), (u.val, v_val))) =
      (Memory.spec 0).clientState s_mid₁ (bgTickProg (base, s_mid₁.frontier)) := by
    rw [hst_so₁, hfr_m₁]
  have htick_eq₂ : (Memory.spec 0).clientState s_grow₂
      (stepOpProg (((base, s_grow₂.frontier), opTag), (u.val, v_val))) =
      (Memory.spec 0).clientState s_mid₂ (bgTickProg (base, s_mid₂.frontier)) := by
    rw [hst_so₂, hfr_m₂]
  have hres2_eq :
      ((Memory.spec 0).clientResult s_grow₁
        (stepOpProg (((base, s_grow₁.frontier), opTag), (u.val, v_val)))).2 =
      ((Memory.spec 0).clientResult s_grow₂
        (stepOpProg (((base, s_grow₂.frontier), opTag), (u.val, v_val)))).2 := by
    rw [hres_so₁, hres_so₂]; dsimp only
    rw [← hfr_m₁, ← hfr_m₂]; exact hr_bg
  have hsch_tick : SchedEq base
      ((Memory.spec 0).clientState s_grow₁
        (stepOpProg (((base, s_grow₁.frontier), opTag), (u.val, v_val))))
      ((Memory.spec 0).clientState s_grow₂
        (stepOpProg (((base, s_grow₂.frontier), opTag), (u.val, v_val)))) := by
    rw [htick_eq₁, htick_eq₂]; exact hsch_bg
  -- Relate `s_mid.mem` header fields back to `s.mem`
  have hsetup₁ := fgSetup_of_dualStateInv h₁ hop_nz u v
  have hstep₁ : FGStepOutAux c U V w base opTag v_val u v s_dict L₁ s₁ s_prep₁ k_grow s_mid₁ := by
    by_cases hle7 : s₁.mem (base + hdrPhase) ≤ 7
    · exact fgStep_le7_aux h₁ u v hv_eq hsetup₁ rfl rfl rfl hle7
    · by_cases h8 : s₁.mem (base + hdrPhase) = 8
      · exact fgStep_eq8_aux h₁ u v hv_eq hsetup₁ rfl rfl rfl h8
      · exact fgStep_ge9_aux h₁ u v hv_eq hsetup₁ rfl rfl rfl (by omega)
  have hph_m₁ : s_mid₁.mem (base + hdrPhase) = s₁.mem (base + hdrPhase) :=
    hstep₁.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hph_m₂ : s_mid₂.mem (base + hdrPhase) = s₁.mem (base + hdrPhase) :=
    (hsch_mid.2 hdrPhase (by decide) (by decide)).symm.trans hph_m₁
  refine ⟨rfl, hres2_eq, hsch_tick, fun hne5 => ?_, fun hp5 => ?_⟩
  · have hb₁ := hpt₁.2.2.2; rw [ite_eq_left (hph_m₁.symm ▸ hne5)] at hb₁
    have hb₂ := hpt₂.2.2.2; rw [ite_eq_left (hph_m₂.symm ▸ hne5)] at hb₂
    obtain ⟨_, _, _, hpre₁, _⟩ := hb₁
    obtain ⟨_, _, _, hpre₂, _⟩ := hb₂
    exact schedEq_postShrink_pre hop_nz hpre₁ hpre₂ hsch_tick
  · intro ws₁ ws₂
    have hb₁ := hpt₁.2.2.2; rw [ite_eq_right (not_not.mpr (hph_m₁.trans hp5))] at hb₁
    have hb₂ := hpt₂.2.2.2; rw [ite_eq_right (not_not.mpr (hph_m₂.trans hp5))] at hb₂
    dsimp only at hb₁ hb₂
    have hcur_m₁ : s_mid₁.mem (base + hdrCur) = s₁.mem (base + hdrCur) :=
      hstep₁.2.2.2.1 (base + hdrCur) (by dsimp only [hdrCur]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hnD_m₁ : s_mid₁.mem (base + hdrNDst) = s₁.mem (base + hdrNDst) :=
      hstep₁.2.2.2.1 (base + hdrNDst) (by dsimp only [hdrNDst]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hst_m₁ : s_mid₁.mem (base + hdrStage) = s₁.mem (base + hdrStage) :=
      hstep₁.2.2.2.1 (base + hdrStage) (by dsimp only [hdrStage]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hpad_m₁ : s_mid₁.mem (base + hdrPad) = s₁.mem (base + hdrPad) :=
      hstep₁.2.2.2.1 (base + hdrPad) (by dsimp only [hdrPad]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    have hmbD_m₁ : dualMbDst base s_mid₁.mem = dualMbDst base s₁.mem := by
      unfold dualMbDst; rw [hph_m₁, hnD_m₁, hst_m₁, hpad_m₁]
    have hcur_m₂ : s_mid₂.mem (base + hdrCur) = s₁.mem (base + hdrCur) :=
      (hsch_mid.2 hdrCur (by decide) (by decide)).symm.trans hcur_m₁
    have hnD_m₂ : s_mid₂.mem (base + hdrNDst) = s₁.mem (base + hdrNDst) :=
      (hsch_mid.2 hdrNDst (by decide) (by decide)).symm.trans hnD_m₁
    have hmbD_m₂ : dualMbDst base s_mid₂.mem = dualMbDst base s₁.mem :=
      hsch_mid.mbDst_eq.symm.trans hmbD_m₁
    rw [hcur_m₁, hnD_m₁, hmbD_m₁] at hb₁
    rw [hcur_m₂, hnD_m₂, hmbD_m₂] at hb₂
    let cur := s₁.mem (base + hdrCur)
    let nDst := s₁.mem (base + hdrNDst)
    let offBM := offBktMeta c w nDst
    let endOff := cur + min bulkBatchWhp (offBM - cur)
    let metaDst := dualMbDst base s₁.mem
    have hr₁ := hb₁.2.2.2.2.2.2.2.2.2 ws₁
    have hr₂ := hb₂.2.2.2.2.2.2.2.2.2 ws₂
    have hmd_192 : base + 192 ≤ metaDst := by
      dsimp only [metaDst]; unfold dualMbDst
      rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hb₁.1.ne']
      split_ifs <;> omega
    let s_r₁ : Memory.State :=
      { mem := writeWords
          ((Memory.spec 0).clientState s_grow₁
            (stepOpProg (((base, s₁.frontier + k_grow), opTag), (u.val, v_val)))).mem
          (metaDst + cur) ws₁
        frontier :=
          ((Memory.spec 0).clientState s_grow₁
            (stepOpProg (((base, s₁.frontier + k_grow), opTag), (u.val, v_val)))).frontier }
    let s_r₂ : Memory.State :=
      { mem := writeWords
          ((Memory.spec 0).clientState s_grow₂
            (stepOpProg (((base, s₂.frontier + k_grow), opTag), (u.val, v_val)))).mem
          (metaDst + cur) ws₂
        frontier :=
          ((Memory.spec 0).clientState s_grow₂
            (stepOpProg (((base, s₂.frontier + k_grow), opTag), (u.val, v_val)))).frontier }
    have hsch_r : SchedEq base s_r₁ s_r₂ := by
      refine ⟨hsch_tick.1, fun off hoff hne_ud => ?_⟩
      dsimp only [s_r₁, s_r₂]
      rw [writeWords_apply_out _ _ _ (by omega), writeWords_apply_out _ _ _ (by omega)]
      exact hsch_tick.2 off hoff hne_ud
    by_cases hlt : endOff < offBM
    · exact schedEq_postShrink_pre hop_nz (hr₁.2.2.2.2.2.2.1 hlt) (hr₂.2.2.2.2.2.2.1 hlt) hsch_r
    · have heq_bm : endOff = offBM := le_antisymm hb₁.2.2.2.1 (Nat.not_lt.mp hlt)
      have hp_r₁_5 : s_r₁.mem (base + hdrPhase) = 5 := hr₁.2.2.1
      have hpD_r₁ : dualPDst base s_r₁.mem = dualPDst base s_mid₁.mem := by
        unfold dualPDst
        have hp_r₁ : s_r₁.mem (base + hdrPhase) = s_mid₁.mem (base + hdrPhase) :=
          hp_r₁_5.trans (hp5.symm.trans hph_m₁.symm)
        have hs_r₁ : s_r₁.mem (base + hdrStage) = s_mid₁.mem (base + hdrStage) := hr₁.2.2.2.1
        rw [hp_r₁, hs_r₁]
      have hd_r₁ : s_r₁.mem (dualPDst base s_r₁.mem + 31) ≤ s_r₁.mem (base + hdrCur) := by
        rw [hpD_r₁]
        have h31 : s_r₁.mem (dualPDst base s_mid₁.mem + 31) = offBM := hr₁.2.2.2.2.2.1
        have hc_r : s_r₁.mem (base + hdrCur) = endOff := hr₁.2.2.2.2.1
        rw [h31, hc_r, heq_bm]
      exact schedEq_postShrink_rf hop_nz (hr₁.2.2.2.2.2.2.2 heq_bm)
        (hr₂.2.2.2.2.2.2.2 heq_bm) hp_r₁_5 hd_r₁ hsch_r

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

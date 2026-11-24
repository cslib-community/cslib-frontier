/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvFGStepB

/-!
# Full Foreground Mutation Specification (`prepGrow_userMutate_spec`)

Assembles `prepGrow_userMutate_spec` (`DualStateInv → DualMidInv`) across all 12 phases (`0..11`).
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

private theorem hostCacheValid_congr {c w N off0 base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hoff : off0 = hdrSrcOd ∨ off0 = hdrDstOd)
    (heq : ∀ off < 48, off ≠ hdrLive → off ≠ hdrSplit → m₁ (base + off) = m₂ (base + off))
    (hc : HostCacheValid c w N off0 base m₂) :
    HostCacheValid c w N off0 base m₁ := fun hN => by
  obtain ⟨c0, c1, c2, c3, c4⟩ := hc hN
  have h0 : m₁ (base + off0) = m₂ (base + off0) :=
    heq off0 (by rcases hoff with rfl | rfl <;> decide)
      (by rcases hoff with rfl | rfl <;> decide) (by rcases hoff with rfl | rfl <;> decide)
  have hstep : ∀ k ≤ 4, m₁ (base + off0 + k) = m₂ (base + off0 + k) := fun k hk => by
    rw [Nat.add_assoc]
    rcases hoff with rfl | rfl
    · exact heq (hdrSrcOd + k) (by unfold hdrSrcOd; omega)
        (by unfold hdrSrcOd hdrLive; omega) (by unfold hdrSrcOd hdrSplit; omega)
    · exact heq (hdrDstOd + k) (by unfold hdrDstOd; omega)
        (by unfold hdrDstOd hdrLive; omega) (by unfold hdrDstOd hdrSplit; omega)
  exact ⟨h0.trans c0, (hstep 1 (by decide)).trans c1, (hstep 2 (by decide)).trans c2,
    (hstep 3 (by decide)).trans c3, (hstep 4 (by decide)).trans c4⟩

private theorem dualMidInv_sched_aux {c U V w base opTag k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_mid : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (u : Fin U) (v : Fin V)
    (hsetup : FGSetup c U V w base opTag u v s_dict L s)
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hs_mid_fr : s_mid.frontier = s.frontier + k_grow)
    (hhdr_eq : ∀ off < 48, off ≠ hdrLive → off ≠ hdrSplit →
      s_mid.mem (base + off) = s.mem (base + off))
    (hs_mid_sp_clamp :
      let nLive := (Dictionary.dom s_dict).card
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      let nLive' := (Dictionary.dom s_dict').card
      let ph := s.mem (base + hdrPhase)
      let ibLo := s.mem (base + hdrItemLo)
      let ibHi := s.mem (base + hdrItemHi)
      let qLo := s.mem (base + hdrQLo)
      let qHi := s.mem (base + hdrQHi)
      let sp := s.mem (base + hdrSplit)
      (ph = 3 ∨ ph = 10) →
        s_mid.mem (base + hdrSplit) ≤ nLive' ∧
        s_mid.mem (base + hdrSplit) ≤ sp ∧
        nLive' - s_mid.mem (base + hdrSplit) ≤ (nLive - sp) + 1 ∧
        SplitHiQuotBounded (splitSlotIo w (valBits V) base ibLo qLo ibHi qHi nLive')
          nLive' s_mid.mem) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let nLive' := (Dictionary.dom s_dict').card
    let ph := s.mem (base + hdrPhase)
    let L_mid := L.applyFG ph opTag u v
    if s_mid.mem (base + hdrPhase) = 0 then
      DualIdleSched true c U V w base nLive' L_mid s_mid
    else
      DualActiveSched true c U V w base nLive' L_mid s_mid := by
  dsimp only at hs_mid_sp_clamp ⊢
  obtain ⟨_, _, hqLo_w, _, _, _, _, _⟩ := dualCoreInv_ib_fits h
  have hw11 := h.hw11; have hph_le := h.ph_le; have hmSrc_eq := h.mSrc_eq; have hsched := h.sched
  have hsrc_safe := hsetup.src_safe; have hcard_step := hsetup.card_step
  have hfr_bounds := hsetup.fr_bounds; have hfr_n' := hsetup.fr_n'
  dsimp only at hcard_step hfr_bounds hfr_n'
  rw [← hk_grow_def] at hfr_bounds hfr_n'
  clear hk_grow_def
  have hw_pos : 0 < w := by omega
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
  set rem := s.mem (base + hdrRem)
  set vB := valBits V
  set L_mid := L.applyFG ph opTag u v
  have hLmid_scalars : L_mid.nTrig = L.nTrig ∧ L_mid.trigOps = L.trigOps ∧
      L_mid.elapsed = L.elapsed ∧ L_mid.unpermBound = L.unpermBound := by
    dsimp only [L_mid, DualLatent.applyFG]; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hph_m : s_mid.mem (base + hdrPhase) = ph :=
    hhdr_eq hdrPhase (by decide) (by decide) (by decide)
  have hstg_m : s_mid.mem (base + hdrStage) = stg :=
    hhdr_eq hdrStage (by decide) (by decide) (by decide)
  have hnS_m : s_mid.mem (base + hdrNSrc) = nSrc :=
    hhdr_eq hdrNSrc (by decide) (by decide) (by decide)
  have hnD_m : s_mid.mem (base + hdrNDst) = nDst :=
    hhdr_eq hdrNDst (by decide) (by decide) (by decide)
  have hcur_m : s_mid.mem (base + hdrCur) = cur :=
    hhdr_eq hdrCur (by decide) (by decide) (by decide)
  have hrem_m : s_mid.mem (base + hdrRem) = rem :=
    hhdr_eq hdrRem (by decide) (by decide) (by decide)
  have hops_m : s_mid.mem (base + hdrEpochOps) = s.mem (base + hdrEpochOps) :=
    hhdr_eq hdrEpochOps (by decide) (by decide) (by decide)
  have hmS_m : s_mid.mem (base + hdrMSrc) = mSrc :=
    hhdr_eq hdrMSrc (by decide) (by decide) (by decide)
  have hmD_m : s_mid.mem (base + hdrMDst) = mDst :=
    hhdr_eq hdrMDst (by decide) (by decide) (by decide)
  have hpad_m : s_mid.mem (base + hdrPad) = pad :=
    hhdr_eq hdrPad (by decide) (by decide) (by decide)
  have hibL_m : s_mid.mem (base + hdrItemLo) = ibLo :=
    hhdr_eq hdrItemLo (by decide) (by decide) (by decide)
  have hibH_m : s_mid.mem (base + hdrItemHi) = ibHi :=
    hhdr_eq hdrItemHi (by decide) (by decide) (by decide)
  have hqL_m : s_mid.mem (base + hdrQLo) = qLo :=
    hhdr_eq hdrQLo (by decide) (by decide) (by decide)
  have hqH_m : s_mid.mem (base + hdrQHi) = qHi :=
    hhdr_eq hdrQHi (by decide) (by decide) (by decide)
  have hlsub_m : s_mid.mem (base + hdrLogSub) = s.mem (base + hdrLogSub) :=
    hhdr_eq hdrLogSub (by decide) (by decide) (by decide)
  have hlk_m : s_mid.mem (base + hdrLogK) = s.mem (base + hdrLogK) :=
    hhdr_eq hdrLogK (by decide) (by decide) (by decide)
  have hpgH_m : ∀ nc, dualPgHost c V w base nc s_mid.mem =
      hostPageLayout c w (if nDst = 0 then nSrc else nDst)
        (if nDst = 0 then base + 192 else if stg = 0 then base + 192 + pad else base + 192)
        ibHi qHi vB nc := fun nc => by
    unfold dualPgHost dualNHost dualMbHost; rw [hnD_m, hnS_m, hstg_m, hpad_m, hibH_m, hqH_m]
  rw [hph_m]
  by_cases hp0 : ph = 0
  · rw [ite_eq_left hp0] at hsched ⊢
    have hst0 := hsched.stg_zero; have hd0 := hsched.nDst_zero
    have hmD0 := hsched.mDst_zero
    have hibL0 := hsched.ibLo_eq; have hibH0 := hsched.ibHi_eq
    have hqL0 := hsched.qLo_eq; have hqH0 := hsched.qHi_eq
    have hel0 := hsched.elapsed_zero; have hops0 := hsched.ops_evs
    obtain ⟨hidle, hsm_lt, _⟩ := hsched.safe_fr
    have hpost_n' : DualPostUpdateSafe c U nSrc nLive' := by
      refine dualPostUpdateSafe_of_idle hidle ?_
        ⟨hcard_step.2.2.2.2.1, hcard_step.2.2.2.1⟩ hcard_step.2.2.2.2.2.1
      by_cases hs0 : nSrc = 0
      · left
        have hlt := hsm_lt hs0
        rw [hs0]; unfold dualTriggerCap; simp only [↓reduceIte]
        split_ifs with hc
        · exact absurd hc.2 (Nat.not_le_of_gt hlt)
        · rfl
      · exact Or.inr hs0
    have hfr_pad_n' : s_mid.frontier ≤ base + dualPaddedWords c U V w nSrc nSrc nLive' := by
      have hhi := hfr_bounds.2.2.2.2.1 (by omega)
      rw [← hs_mid_fr] at hhi
      have hpw2 := pairStreamWords_succ_le_add_two (n := nLive') hw_pos
        (show qLo + vB ≤ 2 * w by omega)
      have hq_ib : qLo + vB = epochItemBitsWhp c U V nSrc := by
        change s.mem (base + hdrQLo) + vB = epochItemBitsWhp c U V nSrc
        rw [hqL0]; unfold epochItemBitsWhp
        by_cases hs0 : nSrc = 0
        · have hlt0 : nSrc < whpThreshold c := hs0 ▸ whpThreshold_pos c
          rw [ite_eq_left hs0, ite_eq_left hlt0]
        · simp only [EpochCapSafe, hs0, ↓reduceIte] at hsrc_safe
          rw [ite_eq_right hs0, ite_eq_right (Nat.not_lt.mpr hsrc_safe.1)]
      change s_mid.frontier ≤ s.mem (base + hdrItemLo) + pairStreamWords (nLive' + 1) qLo vB w
        at hhi
      rw [hibL0] at hhi
      change s_mid.frontier ≤ base + 192 + mSrc + pairStreamWords (nLive' + 1) qLo vB w at hhi
      rw [hmSrc_eq] at hhi
      unfold pairStreamWords at hhi hpw2
      unfold dualPaddedWords rootHdrWhp
      rw [hq_ib] at hhi hpw2
      rw [Nat.max_self, Nat.max_self]
      omega
    refine DualIdleSched.mk (by rw [hstg_m]; exact hst0) (by rw [hnD_m]; exact hd0)
      (by rw [hmD_m]; exact hmD0)
      (by rw [hibL_m, hmS_m]; exact hibL0) (by rw [hibH_m, hibL_m]; exact hibH0)
      (by rw [hqL_m, hnS_m]; exact hqL0) (by rw [hqH_m, hqL_m]; exact hqH0)
      (by rw [hLmid_scalars.2.2.1]; exact hel0)
      (by rw [hnS_m, hibL_m, hqL_m]; exact
        ⟨hpost_n', hfr_pad_n', by rw [hs_mid_fr]; exact hfr_n'.1 (Or.inl (by omega)),
          by rw [hs_mid_fr]; exact hfr_bounds.2.2.2.2.1 (by omega)⟩) ?_
    rw [hnS_m, hops_m]; intro hs_pos
    obtain ⟨ho1, ho2⟩ := hops0 hs_pos
    simp only [Bool.false_eq_true, ↓reduceIte] at ho1 ho2 ⊢
    have hLmid_s0 : L_mid.slotSrc = L.slotSrc.applyFG false opTag u v := by
      dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_left (by omega)]
    rw [hLmid_s0]; unfold SlotLatent.applyFG
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> (dsimp only; rw [List.length_append, List.length_singleton]; omega)
  · rw [ite_eq_right hp0] at hsched ⊢
    have hd_b := hsched.nDst_bounds; have hd0_i := hsched.nDst_zero
    have hst1_i := hsched.stg_one; have hpost := hsched.post_trig
    have htrig := hsched.trig_cap; have hd_hi := hsched.drift_hi
    have hd_lo := hsched.drift_lo; have hibL_e := hsched.ibLo_eq
    have hqL_e := hsched.qLo_eq; have h1_i := hsched.ph1
    have hge2_i := hsched.ge2; have h2_i := hsched.ph2
    have h3_10_i := hsched.ph3_10; have h11_i := hsched.ph11
    have hrem_b := hsched.budget
    simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.sub_zero, add_zero]
      at hd_hi hd_lo hrem_b
    have hge2_m : 2 ≤ ph →
        mDst = epochMetaWordsWhp c w nDst ∧ pad = max mSrc mDst ∧
        HostCacheValid c w nDst hdrDstOd base s_mid.mem ∧
        (0 < nDst →
          s_mid.mem (base + hdrLogN) = Nat.log 2 nDst ∧
          s_mid.mem (base + hdrEll) = Dynamic.logLogFactor nDst ∧
          s_mid.mem (base + hdrPgB) = pageSizeWhp nDst) ∧
        ibHi = (if nDst = 0 then base + 196 + mSrc else base + 192 + pad + mDst + 4) ∧
        qHi = max (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc)
          (if nDst = 0 then keyBits U else quotBitsWhp U nDst) := fun h2 => by
      obtain ⟨e1, e2, hc_d, hsc_d, e3, e4⟩ := hge2_i h2
      refine ⟨e1, e2, hostCacheValid_congr (Or.inr rfl) hhdr_eq hc_d, fun hd_pos => ?_, e3, e4⟩
      obtain ⟨l0, l1, l2⟩ := hsc_d hd_pos
      exact ⟨(hhdr_eq hdrLogN (by decide) (by decide) (by decide)).trans l0,
        (hhdr_eq hdrEll (by decide) (by decide) (by decide)).trans l1,
        (hhdr_eq hdrPgB (by decide) (by decide) (by decide)).trans l2⟩
    have hbud := remBudget_fg_step hp0 hrem_b.1
      hfr_bounds.2.2.2.2.2.2.1
      (fun hp3 => (hs_mid_sp_clamp (Or.inl hp3)).2.1)
      (fun hp10 => (hs_mid_sp_clamp (Or.inr hp10)).2.2.1)
      hfr_bounds.2.2.2.2.2.2.2
      hph_le
    refine
      { nDst_bounds := by rw [hnD_m]; exact hd_b
        nDst_zero := by rw [hnD_m, hnS_m, hstg_m, hph_m]; exact hd0_i
        stg_one := by rw [hstg_m, hnD_m, hph_m]; exact hst1_i
        post_trig := by rw [hnS_m, hLmid_scalars.1]; exact hpost
        trig_cap := by rw [hnS_m, hLmid_scalars.1, hLmid_scalars.2.1, hnD_m]; exact htrig
        drift_hi := by rw [hLmid_scalars.1, hLmid_scalars.2.2.1]; simp only [↓reduceIte]; omega
        drift_lo := by rw [hLmid_scalars.1, hLmid_scalars.2.2.1]; simp only [↓reduceIte]; omega
        ibLo_eq := by rw [hibL_m, hph_m, hmS_m, hmD_m]; exact hibL_e
        qLo_eq := by rw [hqL_m, hph_m, hnS_m, hnD_m]; exact hqL_e
        ph1 := by
          rw [hph_m, hstg_m, hnD_m, hmD_m, hibH_m, hibL_m, hqH_m, hqL_m]
          exact fun hp1 => ⟨(h1_i hp1).1, (h1_i hp1).2.1, (h1_i hp1).2.2.1,
            (h1_i hp1).2.2.2.1, (h1_i hp1).2.2.2.2.1,
            by rw [hs_mid_fr]; exact hfr_n'.1 (Or.inl (by omega)),
            by rw [hs_mid_fr]; exact hfr_bounds.2.2.2.2.1 (by omega)⟩
        ge2 := by rw [hph_m, hmD_m, hnD_m, hpad_m, hmS_m, hibH_m, hqH_m, hnS_m]; exact hge2_m
        ph2 := by
          rw [hph_m, hstg_m, hibL_m, hqL_m, hibH_m, hqH_m]
          exact fun hp2 => ⟨(h2_i hp2).1, by rw [hs_mid_fr]; exact hfr_n'.1 (Or.inl (by omega)),
            by rw [hs_mid_fr]; exact hfr_bounds.2.2.2.2.2.1 (by omega)⟩
        ph3_10 := by
          rw [hph_m, hibH_m, hqH_m]
          exact fun h3_10 => ⟨by rw [hs_mid_fr]; exact hfr_n'.2 h3_10,
            by rw [hs_mid_fr]; exact hfr_bounds.2.2.2.2.2.1 (by omega)⟩
        ph11 := by
          rw [hph_m, hibL_m, hqL_m, hibH_m, hqH_m]
          exact fun hp11 => ⟨by simp only [↓reduceIte, add_zero, hs_mid_fr]
                                exact hfr_n'.1 (Or.inr hp11),
            by rw [hs_mid_fr]; exact hfr_bounds.2.2.2.2.2.1 (by omega)⟩
        budget := by
          dsimp only [dualPgHost, dualNHost, dualMbHost, hostPageLayout, epochPageArenaLayout]
            at hrem_b hbud ⊢
          rw [hnS_m, hibH_m, hqH_m, hibL_m, hqL_m, hnD_m, hstg_m, hph_m,
            hlsub_m, hlk_m, hmD_m, hcur_m, hrem_m, hs_mid_fr, hLmid_scalars.2.2.1]
          simp only [true_and, ↓reduceIte]
          dsimp only [ph, stg, nSrc, nDst, mDst, ibLo, ibHi, qLo, qHi, cur, rem, vB]
            at hrem_b hbud ⊢
          exact ⟨hbud.1, by have := hrem_b.2.1; have := hbud.2; omega, hrem_b.2.2⟩ }

private theorem prepGrow_userMutate_spec_aux {c U V w base opTag v_val k_grow : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s s_prep s_mid : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hs_prep_def :
      s_prep = (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hk_grow_def :
      k_grow = (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val)))
    (hs_mid_def :
      s_mid =
        (Memory.spec 0).clientState { mem := s_prep.mem, frontier := s.frontier + k_grow }
          (userMutateProg ((base, opTag), (u.val, v_val))))
    (hpad_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
         else s.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let ph := s.mem (base + hdrPhase)
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let L_mid := L.applyFG ph opTag u v
    PrepGrowPre w (((base, s.frontier), opTag), u.val) s ∧
    s_prep.frontier = s.frontier ∧
    k_grow ≤ bulkBatchWhp ∧
    memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s ≤ 40 ∧
    s_grow.frontier ≤ base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
      (if ph = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst))
      (Dictionary.dom s_dict).card ∧
    Memory.WellFormed w s_grow ∧
    UserMutatePre w ((base, opTag), (u.val, v_val)) s_grow ∧
    s_mid.frontier = s_grow.frontier ∧
    (∀ addr < base, s_grow.mem addr = s.mem addr) ∧
    (∀ addr < base, s_mid.mem addr = s.mem addr) ∧
    DualMidInv c U V w base s_dict' L_mid s_mid ∧
    ((ph ≤ 7 → L_mid.slotSrc.GoodCovers) →
      (ph = 8 → L_mid.slotSrc.GoodCovers ∧ L_mid.slotDst.GoodCovers) →
      (9 ≤ ph → L_mid.slotDst.GoodCovers) →
      memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow ≤
        2 * epochStepCost c + 80) := by
  dsimp only at hpad_fits' ⊢
  have hsetup := fgSetup_of_dualStateInv h hop_nz u v
  have hcard_step := hsetup.card_step
  dsimp only at hcard_step
  have hpre_pg := hsetup.pre_pg
  have hs_prep_fr := hsetup.s_prep_fr
  have hmc_pg := hsetup.mc_pg
  have hfr_bounds := hsetup.fr_bounds
  have hwf_grow := hsetup.wf_grow
  have hgrow_below := hsetup.grow_below
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hb192 := h.base_fr; have hhdr := h.hdr
  have hph_le := h.ph_le; have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq
  have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hph1_inv := h.ph1_inv; have hph4_inv := h.ph4_inv; have hph5_inv := h.ph5_inv
  have hph6_inv := h.ph6_inv; have hph7_inv := h.ph7_inv; have hph8_inv := h.ph8_inv
  have hph9_inv := h.ph9_inv; have hsl_67 := h.sl_67
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost, dualPh5MaskMem] at hph4_inv hph5_inv hph6_inv hph7_inv hph9_inv hsl_67
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
  set sp := s.mem (base + hdrSplit)
  set cur := s.mem (base + hdrCur)
  set rem := s.mem (base + hdrRem)
  set uDone := s.mem (base + hdrUnpermDone)
  set vB := valBits V
  have hstep_all : FGStepOutAux c U V w base opTag v_val u v s_dict L s s_prep k_grow s_mid := by
    by_cases hle7 : ph ≤ 7
    · exact fgStep_le7_aux h u v hv_eq hsetup hs_prep_def hk_grow_def hs_mid_def hle7
    · by_cases h8 : ph = 8
      · exact fgStep_eq8_aux h u v hv_eq hsetup hs_prep_def hk_grow_def hs_mid_def h8
      · exact fgStep_ge9_aux h u v hv_eq hsetup hs_prep_def hk_grow_def hs_mid_def (by omega)
  have hextra_le7 := fun hle7 : ph ≤ 7 =>
    fgStep_le7_extra h u v hv_eq hsetup hs_prep_def hk_grow_def hs_mid_def hle7
  dsimp only [dualMbDst, dualPDst, dualPh5MaskMem] at hextra_le7
  dsimp only [FGStepOutAux] at hstep_all
  dsimp only at hs_prep_fr hfr_bounds hwf_grow hgrow_below
  rw [← hs_prep_def] at hs_prep_fr hgrow_below
  rw [← hk_grow_def] at hfr_bounds
  rw [← hs_prep_def, ← hk_grow_def] at hwf_grow
  clear hs_prep_def
  set s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
  set L_mid := L.applyFG ph opTag u v
  obtain ⟨hpre_um, hs_mid_fr, hs_mid_live, hs_mid_hdr, _hs_mid_sp_pres, hs_mid_sp_clamp,
    hs_mid_4, hs_mid_5, hs_mid_67, hs_mid_9, hs_mid_le7, hs_mid_8, hs_mid_ge9, hmc_um⟩ := hstep_all
  have hwf_mid : Memory.WellFormed w s_mid := by
    rw [hs_mid_def]; exact wf_step hwf_grow (validHistory_userMutateProg hwf_grow hpre_um)
  clear hs_mid_def
  have hhdr_eq : ∀ off < 48, off ≠ hdrLive → off ≠ hdrSplit →
      s_mid.mem (base + off) = s.mem (base + off) := fun off hoff hnl hns =>
    hs_mid_hdr (base + off) (by omega) (by omega) (by omega)
  have hsched_mid := dualMidInv_sched_aux h u v hsetup hk_grow_def hs_mid_fr
    hhdr_eq hs_mid_sp_clamp
  clear hk_grow_def
  have hLmid_scalars : L_mid.nTrig = L.nTrig ∧ L_mid.trigOps = L.trigOps ∧
      L_mid.elapsed = L.elapsed ∧ L_mid.unpermBound = L.unpermBound := by
    dsimp only [L_mid, DualLatent.applyFG]; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨hpre_pg, hs_prep_fr, hfr_bounds.1, hmc_pg, hfr_bounds.2.1, hwf_grow, hpre_um,
    hs_mid_fr, hgrow_below,
    fun addr ha => hs_mid_hdr addr (by omega) (by unfold hdrLive; omega)
      (by unfold hdrSplit; omega),
    ?_, hmc_um⟩
  -- Assemble `DualMidInv c U V w base s_dict' L_mid s_mid`:
  unfold DualMidInv
  have hhdr_mid : RootStaticHeader c U V w base s_mid.mem :=
    ⟨(hhdr_eq hdrU1 (by decide) (by decide) (by decide)).trans hhdr.1,
     (hhdr_eq hdrV1 (by decide) (by decide) (by decide)).trans hhdr.2.1,
     (hhdr_eq hdrW (by decide) (by decide) (by decide)).trans hhdr.2.2.1,
     (hhdr_eq hdrKeyBits (by decide) (by decide) (by decide)).trans hhdr.2.2.2.1,
     (hhdr_eq hdrValBits (by decide) (by decide) (by decide)).trans hhdr.2.2.2.2.1,
     (hhdr_eq hdrThresh (by decide) (by decide) (by decide)).trans hhdr.2.2.2.2.2.1,
     (hhdr_eq hdrCTab (by decide) (by decide) (by decide)).trans hhdr.2.2.2.2.2.2.1,
     (hhdr_eq hdrDTab (by decide) (by decide) (by decide)).trans hhdr.2.2.2.2.2.2.2.1,
     (hhdr_eq hdrRedW (by decide) (by decide) (by decide)).trans hhdr.2.2.2.2.2.2.2.2.1,
     (hhdr_eq hdrCEff (by decide) (by decide) (by decide)).trans hhdr.2.2.2.2.2.2.2.2.2⟩
  have hph_m : s_mid.mem (base + hdrPhase) = ph :=
    hhdr_eq hdrPhase (by decide) (by decide) (by decide)
  have hstg_m : s_mid.mem (base + hdrStage) = stg :=
    hhdr_eq hdrStage (by decide) (by decide) (by decide)
  have hnS_m : s_mid.mem (base + hdrNSrc) = nSrc :=
    hhdr_eq hdrNSrc (by decide) (by decide) (by decide)
  have hnD_m : s_mid.mem (base + hdrNDst) = nDst :=
    hhdr_eq hdrNDst (by decide) (by decide) (by decide)
  have hcur_m : s_mid.mem (base + hdrCur) = cur :=
    hhdr_eq hdrCur (by decide) (by decide) (by decide)
  have hrem_m : s_mid.mem (base + hdrRem) = rem :=
    hhdr_eq hdrRem (by decide) (by decide) (by decide)
  have hmS_m : s_mid.mem (base + hdrMSrc) = mSrc :=
    hhdr_eq hdrMSrc (by decide) (by decide) (by decide)
  have hmD_m : s_mid.mem (base + hdrMDst) = mDst :=
    hhdr_eq hdrMDst (by decide) (by decide) (by decide)
  have hpad_m : s_mid.mem (base + hdrPad) = pad :=
    hhdr_eq hdrPad (by decide) (by decide) (by decide)
  have hibL_m : s_mid.mem (base + hdrItemLo) = ibLo :=
    hhdr_eq hdrItemLo (by decide) (by decide) (by decide)
  have hibH_m : s_mid.mem (base + hdrItemHi) = ibHi :=
    hhdr_eq hdrItemHi (by decide) (by decide) (by decide)
  have hqL_m : s_mid.mem (base + hdrQLo) = qLo :=
    hhdr_eq hdrQLo (by decide) (by decide) (by decide)
  have hqH_m : s_mid.mem (base + hdrQHi) = qHi :=
    hhdr_eq hdrQHi (by decide) (by decide) (by decide)
  have hlsub_m : s_mid.mem (base + hdrLogSub) = s.mem (base + hdrLogSub) :=
    hhdr_eq hdrLogSub (by decide) (by decide) (by decide)
  have hlacc_m : s_mid.mem (base + hdrLogAcc) = s.mem (base + hdrLogAcc) :=
    hhdr_eq hdrLogAcc (by decide) (by decide) (by decide)
  have hlk_m : s_mid.mem (base + hdrLogK) = s.mem (base + hdrLogK) :=
    hhdr_eq hdrLogK (by decide) (by decide) (by decide)
  have hud_m : s_mid.mem (base + hdrUnpermDone) = uDone :=
    hhdr_eq hdrUnpermDone (by decide) (by decide) (by decide)
  have hcache_s_m : HostCacheValid c w nSrc hdrSrcOd base s_mid.mem :=
    hostCacheValid_congr (Or.inl rfl) hhdr_eq hcache_s
  have hcapSrc_m : dualCapSrc base s_mid.mem = if stg = 0 then nSrc else nDst := by
    unfold dualCapSrc; rw [hstg_m, hnS_m, hnD_m]
  have hmbSrc_m : dualMbSrc base s_mid.mem =
      (if stg = 0 then if nSrc = 0 then base + hdrSmallMeta0 else base + 192
       else base + 192 + pad) := by
    unfold dualMbSrc; rw [hstg_m, hnS_m, hpad_m]
  have hpSrc_m : dualPSrc base s_mid.mem =
      if stg = 0 then base + hdrPBase0 else base + hdrPBase1 := by
    unfold dualPSrc; rw [hstg_m]
  have hmbDst_m : dualMbDst base s_mid.mem =
      (if ph < 10 then
         if nDst = 0 then base + hdrSmallMeta1
         else if stg = 0 then base + 192 + pad else base + 192
       else if nDst = 0 then base + hdrSmallMeta0 else base + 192) := by
    unfold dualMbDst; rw [hph_m, hnD_m, hstg_m, hpad_m]
  have hpDst_m : dualPDst base s_mid.mem =
      (if ph < 10 then if stg = 0 then base + hdrPBase1 else base + hdrPBase0
       else base + hdrPBase0) := by
    unfold dualPDst; rw [hph_m, hstg_m]
  have hpgH_m : ∀ nc, dualPgHost c V w base nc s_mid.mem =
      hostPageLayout c w (if nDst = 0 then nSrc else nDst)
        (if nDst = 0 then base + 192 else if stg = 0 then base + 192 + pad else base + 192)
        ibHi qHi vB nc := fun nc => by
    unfold dualPgHost dualNHost dualMbHost; rw [hnD_m, hnS_m, hstg_m, hpad_m, hibH_m, hqH_m]
  refine
    { hw11 := hw11
      U_pos := hU0
      U_lt := hUw
      V_pos := hV0
      V_le := hVw
      wf := hwf_mid
      base_fr := by rw [hs_mid_fr]; omega
      hdr := hhdr_mid
      live_eq := hs_mid_live
      live_le := hcard_step.2.2.2.2.2.1
      ph_le := hph_m ▸ hph_le
      stg_le := hstg_m ▸ hstg_le
      mSrc_eq := by rw [hmS_m, hnS_m]; exact hmSrc_eq
      cache_src := hnS_m.symm ▸ hcache_s_m
      nSrc_bounds := hnS_m.symm ▸ hnSrc_b
      sched := hsched_mid
      pad_fits := by rw [hnS_m, hph_m, hnD_m]; exact hpad_fits'
      ph1_inv := ?_
      ph3_inv := ?_
      ph4_inv := by
        rw [hph_m, hnD_m, hcur_m, hmD_m, hmbDst_m]
        exact fun hp4 => ⟨(hph4_inv hp4).1, (hph4_inv hp4).2.1, hs_mid_4 hp4⟩
      pDst_pre := by
        dsimp only [dualPh5MaskMem]
        rw [hph_m, hstg_m, hnD_m, hmbDst_m, hpDst_m, hibH_m, hqH_m]
        intro hp25 h5_st hd_pos
        exact (hextra_le7 (by omega)).1 hp25 h5_st hd_pos
      ph5_inv := ?_
      ph6_inv := ?_
      ph7_inv := ?_
      ph8_inv := ?_
      ph9_inv := ?_
      ph10_inv := ?_
      sl_le7 := by
        rw [hph_m, hcapSrc_m, hpSrc_m, hmbSrc_m, hstg_m, hnS_m, hnD_m, hpad_m,
          hibL_m, hqL_m, hibH_m, hqH_m, hLmid_scalars.2.2.1]
        exact hs_mid_le7
      sl_67 := ?_
      sl_8 := by
        rw [hph_m, hpgH_m, hcapSrc_m, hnD_m, hpSrc_m, hmbSrc_m, hpDst_m, hmbDst_m,
          hLmid_scalars.2.2.1]
        exact hs_mid_8
      sl_ge9 := by
        rw [hph_m, hnD_m, hpDst_m, hmbDst_m, hstg_m, hnS_m, hpad_m, hibL_m, hqL_m, hibH_m, hqH_m,
          hud_m, hLmid_scalars.2.2.1]
        exact hs_mid_ge9 }
  all_goals
    try dsimp only [dualPh5MaskMem]
    try rw [hph_m]
    try rw [hnS_m]
    try rw [hnD_m]
    try rw [hibL_m]
    try rw [hibH_m]
    try rw [hqL_m]
    try rw [hqH_m]
    try rw [hcur_m]
    try rw [hrem_m]
    try rw [hud_m]
    try rw [hmbDst_m]
    try rw [hpDst_m]
    try rw [hpgH_m]
    try rw [hLmid_scalars.2.2.2]
  · -- `ph = 1` log2Calc invariant:
    intro hp1
    obtain ⟨hs2, hsub0, hsub1, hsub2⟩ := hph1_inv hp1
    rw [hlsub_m, hlacc_m, hlk_m]
    refine ⟨hs2, hsub0, fun h1 => ?_, fun h2 => ?_⟩
    · obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hsub1 h1
      exact ⟨(hhdr_eq hdrLogN (by decide) (by decide) (by decide)).trans e0,
        (hhdr_eq hdrClogN (by decide) (by decide) (by decide)).trans e1,
        (hhdr_eq hdrPtrB (by decide) (by decide) (by decide)).trans e2,
        (hhdr_eq hdrPgB (by decide) (by decide) (by decide)).trans e3, e4, e5, e6⟩
    · obtain ⟨e0, e1, e2, e3⟩ := hsub2 h2
      exact ⟨(hhdr_eq hdrLogN (by decide) (by decide) (by decide)).trans e0,
        (hhdr_eq hdrEll (by decide) (by decide) (by decide)).trans e1,
        (hhdr_eq hdrPtrB (by decide) (by decide) (by decide)).trans e2,
        (hhdr_eq hdrPgB (by decide) (by decide) (by decide)).trans e3⟩
  · -- `ph = 3`:
    intro hp3
    obtain ⟨h1, _, _, h4⟩ := hs_mid_sp_clamp (Or.inl hp3)
    exact ⟨h1, h4⟩
  · -- `ph = 5`:
    intro hp5
    obtain ⟨hd_pos, hc32, hc_ob, _⟩ := hph5_inv hp5
    obtain ⟨hpt', hzh', hzt'⟩ := hs_mid_5 hp5
    exact ⟨hd_pos, hc32, hc_ob, hpt', hzh', hzt'⟩
  · -- `ph = 6`:
    intro hp6
    obtain ⟨hc_mp, hvp⟩ := hph6_inv hp6
    rw [(hs_mid_67 (Or.inl hp6)).1]
    exact ⟨hc_mp, hvp⟩
  · -- `ph = 7`:
    intro hp7
    obtain ⟨hns_h, hq_sn, hdir, ⟨k, hk_eq, hk_lt, hsn_le, hn_le⟩, htail⟩ := hph7_inv hp7
    have hns_m : s_mid.mem (base + hdrNSnap) = s.mem (base + hdrNSnap) :=
      hhdr_eq hdrNSnap (by decide) (by decide) (by decide)
    have hqs_m : s_mid.mem (base + hdrQSnap) = s.mem (base + hdrQSnap) :=
      hhdr_eq hdrQSnap (by decide) (by decide) (by decide)
    have hnH_m : dualNHost base s_mid.mem = (if nDst = 0 then nSrc else nDst) := by
      unfold dualNHost; rw [hnD_m, hnS_m]
    rw [hns_m, hqs_m, hnH_m, (hs_mid_67 (Or.inr hp7)).1]
    simp only [Bool.false_eq_true, ↓reduceIte] at hsn_le hn_le ⊢
    refine ⟨hns_h, hq_sn, hdir, ⟨k, hk_eq, hk_lt, ?_, ?_⟩, htail⟩
    · have := hcard_step.2.2.2.1; omega
    · have := hcard_step.2.2.2.2.1; omega
  · -- `ph = 8`:
    intro hp8
    obtain ⟨hr1, hr2, hcd⟩ := hph8_inv hp8
    have hLmid_s8 : L_mid.slotSrc = L.slotSrc.applyFG true opTag u v := by
      dsimp only [L_mid, DualLatent.applyFG]; rw [ite_eq_right (by omega), ite_eq_left hp8]
    have hle_cd : (liveDom L_mid.slotSrc.s_abs).card ≤ (liveDom L.slotSrc.s_abs).card := by
      rw [hLmid_s8]; unfold SlotLatent.applyFG
      simp only [↓reduceIte]
      split_ifs <;> (dsimp only; rw [liveDom_delete_card]; split_ifs <;> omega)
    exact ⟨hr1, hr2, hle_cd.trans hcd⟩
  · -- `ph = 9`:
    intro hp9
    obtain ⟨hr1, hr2, hud_le, h_ud0⟩ := hph9_inv hp9
    refine ⟨hr1, hr2, hud_le, fun hud0 => ?_⟩
    obtain ⟨hc1, hc2, hc3⟩ := hs_mid_9 hp9 hud0
    exact ⟨hc1, hc2, hc3, (h_ud0 hud0).2.2.2⟩
  · -- `ph = 10`:
    intro hp10
    obtain ⟨h1, _, _, h4⟩ := hs_mid_sp_clamp (Or.inr hp10)
    exact ⟨h1, h4⟩
  · -- `(ph = 6 ∨ ph = 7)` `slotDst`:
    intro hp67
    refine ⟨fun hd0 => (hextra_le7 (by rcases hp67 with h6 | h7 <;> omega)).2 hp67 hd0,
      fun hd_pos => ?_⟩
    obtain ⟨hd_cap, hd_abs, hd_evs, _⟩ := (hsl_67 hp67).2 hd_pos
    have hLmid_d67 : L_mid.slotDst = L.slotDst := by
      dsimp only [L_mid, DualLatent.applyFG]
      rw [ite_eq_left (by rcases hp67 with h | h <;> omega)]
    rw [hLmid_d67]
    exact ⟨hd_cap, hd_abs, hd_evs, hLmid_d67 ▸ (hs_mid_67 hp67).2 hd_pos⟩


/-- Full foreground mutation specification (`prepGrowProg` + `growZero` + `userMutateProg`) for
`opTag = 1` (`insert u v`) and `opTag = 2` (`delete u`) across all 12 phases `0..11`. -/
theorem prepGrow_userMutate_spec {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) (hv_eq : opTag = 1 → v_val = v.val)
    (hpad_fits' :
      let s_dict' :=
        if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none
      base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
        (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
         else s.mem (base + hdrNDst)) (Dictionary.dom s_dict').card < 2 ^ w) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none
    let ph := s.mem (base + hdrPhase)
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_mid := (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
    let L_mid := L.applyFG ph opTag u v
    PrepGrowPre w (((base, s.frontier), opTag), u.val) s ∧
    s_prep.frontier = s.frontier ∧
    k_grow ≤ bulkBatchWhp ∧
    memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s ≤ 40 ∧
    s_grow.frontier ≤ base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
      (if ph = 0 then s.mem (base + hdrNSrc) else s.mem (base + hdrNDst))
      (Dictionary.dom s_dict).card ∧
    Memory.WellFormed w s_grow ∧
    UserMutatePre w ((base, opTag), (u.val, v_val)) s_grow ∧
    s_mid.frontier = s_grow.frontier ∧
    (∀ addr < base, s_grow.mem addr = s.mem addr) ∧
    (∀ addr < base, s_mid.mem addr = s.mem addr) ∧
    DualMidInv c U V w base s_dict' L_mid s_mid ∧
    ((ph ≤ 7 → L_mid.slotSrc.GoodCovers) →
      (ph = 8 → L_mid.slotSrc.GoodCovers ∧ L_mid.slotDst.GoodCovers) →
      (9 ≤ ph → L_mid.slotDst.GoodCovers) →
      memoryCost (userMutateProg ((base, opTag), (u.val, v_val))) s_grow ≤
        2 * epochStepCost c + 80) :=
  prepGrow_userMutate_spec_aux h hop_nz u v hv_eq rfl rfl rfl hpad_fits'

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

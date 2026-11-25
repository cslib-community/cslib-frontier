/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvTickCore

/-!
# Background Tick Phases `2..3` (`DualEpochInvTickA1`)

Proves `BgTickPre` and `DualPostTickInv` for background tick phases:
* Phase `2` (`tickGrowPreProg`, `tickPhase2_spec`): frontier growth wait and `2 → 3` `SplitPair`
  transition.
* Phase `3` (`tickSlideUpProg`, `tickPhase3_spec`): upward `slideUpBatchProg` batches and `3 → 4` /
  `3 → 6` completion via `SplitHiQuotBounded`.

## Main results

* `tickPhase2_spec`, `tickPhase3_spec`

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
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

/-! ## Section 1: Offset, `ParamTable`, and `SplitPair` Helpers -/

theorem epochMeta_offsets_le {c w N : ℕ} (hth : whpThreshold c ≤ N) :
    32 ≤ offFpHash c w N ∧
    offFpHash c w N ≤ offBktMeta c w N ∧
    offBktMeta c w N ≤ offPageDir c w N ∧
    offPageDir c w N ≤ epochMetaWordsWhp c w N := by
  have heq := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) hth
  rw [← heq]
  unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
    offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
    offBktMeta offFpHash offBktHash
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem epochMetaWordsWhp_zero_eq (c w : ℕ) : epochMetaWordsWhp c w 0 = 0 := by
  unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]

attribute [local irreducible] epochMetaWordsWhp

theorem fastParamTable_mask_congr {c U V w base nDst mbDst pDst ibHi qHi nLive : ℕ}
    {m₁ m₂ : ℕ → ℕ}
    (hpt :
      ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
         io := directSlotIo w (valBits V) base ibHi qHi nLive } : FastEpochLayout).ParamTable
        (dualPh5MaskMem V w base pDst ibHi qHi nLive m₁))
    (heq : ∀ k, (k < 48 ∨ k = 61 ∨ k = 62) → m₂ (pDst + k) = m₁ (pDst + k)) :
    ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := mbDst, pBase := pDst,
       io := directSlotIo w (valBits V) base ibHi qHi nLive } : FastEpochLayout).ParamTable
      (dualPh5MaskMem V w base pDst ibHi qHi nLive m₂) := by
  intro k hk
  rw [← hpt k hk]
  dsimp only
  by_cases h48 : k < 48
  · unfold dualPh5MaskMem
    iterate 13 rw [Function.update_of_ne (by clear *- h48; omega)]
    iterate 13 rw [Function.update_of_ne (by clear *- h48; omega)]
    exact heq k (Or.inl h48)
  · by_cases h61 : k = 61
    · subst h61; unfold dualPh5MaskMem
      iterate 13 rw [Function.update_of_ne (by omega)]
      iterate 13 rw [Function.update_of_ne (by omega)]
      exact heq 61 (Or.inr (Or.inl rfl))
    · by_cases h62 : k = 62
      · subst h62; unfold dualPh5MaskMem
        iterate 13 rw [Function.update_of_ne (by omega)]
        iterate 13 rw [Function.update_of_ne (by omega)]
        exact heq 62 (Or.inr (Or.inr rfl))
      · have hk61 : k < 61 := by clear *- hk h61 h62; omega
        unfold dualPh5MaskMem
        interval_cases k
        · iterate 12 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 12 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 11 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 11 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 10 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 10 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 9 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 9 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 8 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 8 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 7 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 7 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 6 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 6 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 5 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 5 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 4 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 4 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 3 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 3 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · iterate 2 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
          iterate 2 rw [Function.update_of_ne (by omega)]
          rw [Function.update_self]
        · rw [Function.update_of_ne (by omega), Function.update_self,
            Function.update_of_ne (by omega), Function.update_self]
        · rw [Function.update_self, Function.update_self]

theorem two_le_maxTailPhasesBudget (nRef : ℕ) : 2 ≤ maxTailPhasesBudget nRef := by
  unfold maxTailPhasesBudget; omega

theorem active_nLive_le_two_nRef {c U trigOps nSrc nDst nTrig nLive d : ℕ}
    (hpost : DualPostUpdateSafe c U nSrc nTrig)
    (htrig : dualTriggerCap c U nSrc nTrig trigOps = some nDst)
    (hd_hi : nLive ≤ nTrig + d) (hd_lo : nTrig ≤ nLive + d)
    (hd_le : 16 * d ≤ max (whpThreshold c) nSrc) (hnU : nLive ≤ U) :
    nDst ≤ 2 * max (whpThreshold c) nSrc ∧
    nLive ≤ 2 * max (whpThreshold c) nSrc := by
  have har := active_rebuild_safe hpost htrig hd_hi hd_lo hd_le hnU
  have hnt_le : nTrig ≤ max (whpThreshold c) nSrc := by
    by_cases h0 : nSrc = 0
    · subst h0; simp only [DualPostUpdateSafe, ↓reduceIte] at hpost
      exact hpost.2.trans (le_max_left _ _)
    · simp only [DualPostUpdateSafe, h0, ↓reduceIte] at hpost
      have hs_pos : 1 ≤ nSrc := Nat.pos_of_ne_zero h0
      have hnt_s : nTrig ≤ nSrc := by
        by_cases hlt : nSrc < U
        · have h16 := hpost.2.2.2.2 hlt; clear *- hs_pos h16; omega
        · have hnU' := hpost.2.2.1; clear *- hlt hnU'; omega
      exact hnt_s.trans (le_max_right _ _)
  have hnD := har.1
  refine ⟨hnD, ?_⟩
  generalize max (whpThreshold c) nSrc = nRef at hd_le hnt_le ⊢
  clear *- hd_hi hd_le hnt_le
  omega

/-! ## Section 2: Phase `2` (`tickGrowPreProg`) Specification -/

/-- Phase `2` (`growPre`) background tick specification. -/
theorem tickPhase2_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp2 : s.mem (base + hdrPhase) = 2) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb192 := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp2; omega)] at hsched
  obtain ⟨hst0, hfr_lo, hfr_hi_mid⟩ := hsched.ph2 hp2
  simp only [↓reduceIte] at hfr_hi_mid
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hlog_d, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp2; omega)
  obtain ⟨hvb_eq, hvb_w, hqLo_w, hqHi_w, _, hpad_hi_s, _, hfit_hi1⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by clear *- hp2; omega)] at hpad_hi_s
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hw_eq : s.mem (base + hdrW) = w := hhdr.2.2.1
  set nLive := (Dictionary.dom s_dict).card
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  have hibLo_eq : ibLo = base + 192 + mSrc := by
    have hib := hsched.ibLo_eq; rwa [ite_eq_left (by clear *- hp2; omega)] at hib
  have hqLo_eq : qLo = (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) := by
    have hq := hsched.qLo_eq; rwa [ite_eq_left (by clear *- hp2; omega)] at hq
  have hqLo_le_qHi : qLo ≤ qHi := by
    rw [hqHi_eq, ← hqLo_eq]; exact le_max_left _ _
  have hibLo_le_ibHi : ibLo + 4 ≤ ibHi := by
    have hm_le : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
    rw [hibHi_eq, hibLo_eq]
    split_ifs <;> (clear *- hm_le; omega)
  have hfit_hi0 : Fits w hiFr := by
    have hmono := pairStreamWords_mono_n (qb := qHi) (vb := vB) (w := w) (Nat.le_add_right nLive 1)
    unfold Fits at hfit_hi1 ⊢
    dsimp only [hiFr]; clear *- hmono hfit_hi1; omega
  have hpre_grow : TickGrowPrePre w (base, s.frontier) s :=
    ⟨hw11, hw_eq, hb192, hqHi_w, hvb_eq ▸ hvb_w, by rw [hlive_eq, hvb_eq]; exact hfit_hi0⟩
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, ?_⟩
    dsimp only; rw [ite_eq_right (by clear *- hp2; omega), ite_eq_right (by clear *- hp2; omega),
      ite_eq_left hp2]
    exact hpre_grow
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  simp only [hp2, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
    show (2 : ℕ) ≠ 5 by decide, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_gr, hmc_gr⟩ := tickGrowPreProg_eval (base := base) (newFr := s.frontier) (s := s)
    (by rw [hw_eq]; exact hw_pos)
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hwf_tick : Memory.WellFormed w s_tick :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive :=
    hfr_hi_mid.trans hpad_hi_s
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
  have hrem_b := hsched.budget
  dsimp only at hrem_b
  obtain ⟨hcap_s, hdict_s, hsl_s, hlen_s⟩ := h.sl_le7 (by clear *- hp2; omega)
  have hcap_eq : dualCapSrc base s.mem = nSrc := by
    unfold dualCapSrc; rw [ite_eq_left hst0]
  have hio_s : activeSrcIo c w vB base (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
      nSrc nDst pad ibLo qLo ibHi qHi nLive = directSlotIo w vB base ibLo qLo nLive := by
    unfold activeSrcIo; rw [ite_eq_left (by clear *- hp2; omega)]
  rw [hio_s] at hsl_s
  have hcond_eq : (s.frontier < s.mem (base + hdrItemHi) +
      pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
        (s.mem (base + hdrValBits)) (s.mem (base + hdrW))) = (s.frontier < hiFr) := by
    rw [hlive_eq, hvb_eq, hw_eq]
  by_cases hlt : s.frontier < hiFr
  · -- Stays in `ph = 2` (`s_tick = s`):
    have hlt_raw : s.frontier < s.mem (base + hdrItemHi) +
        pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
          (s.mem (base + hdrValBits)) (s.mem (base + hdrW)) := by rwa [hcond_eq]
    have hs_tick_eq : s_tick = s := by
      rw [hst_bg, hst_gr, ite_eq_left hlt_raw]
    refine ⟨hpre_bg, by rw [hs_tick_eq], hwf_tick,
      fun addr _ => by rw [hs_tick_eq], ?_⟩
    rw [ite_eq_left (by clear *- hp2; omega)]
    refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
        (fun ⟨h9, _⟩ => by rw [hp2] at h9; cases h9) rfl rfl, ?_,
      fun _ _ => by unfold itemBatchWhp; clear *- hmc_bg hmc_gr; omega⟩
    rw [hs_tick_eq]
    refine ⟨hwf, ?_, fun h5 => absurd (hp2.symm.trans h5) (by decide), ?_⟩
    · rw [ite_eq_right (by clear *- hp2; omega)]; exact hfr_le_pad
    · rw [hp2, ite_eq_right (by decide : ¬(2 < 2)), ite_eq_left rfl]
      refine ⟨hlt, ?_⟩
      exact
        { h with
          ph7_inv := fun h7 => absurd (hp2.symm.trans h7) (by decide)
          ph9_inv := fun h9 => absurd (hp2.symm.trans h9) (by decide)
          sl_8 := fun h8 => absurd (hp2.symm.trans h8) (by decide)
          sl_ge9 := fun h9 => by clear *- hp2 h9; omega
          sched := by
            rw [ite_eq_right (by clear *- hp2; omega)]
            refine
              { hsched with
                drift_hi := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                drift_lo := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                ph1 := fun h1 => absurd (hp2.symm.trans h1) (by decide)
                ph2 := fun _ => by
                  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  exact ⟨hst0, hfr_lo, hlt.le⟩
                ph3_10 := fun h3 => by clear *- hp2 h3; omega
                ph11 := fun h11 => absurd (hp2.symm.trans h11) (by decide)
                budget := by
                  dsimp only [L']
                  rw [hst0, hp2]
                  unfold remRebuildBudget futureRebuildBudget
                  dsimp only
                  simp only [show (2 : ℕ) ≠ 1 by decide, Bool.false_eq_true, false_and,
                    ↓reduceIte, add_zero]
                  have hrb := hrem_b.2.1
                  rw [hst0, hp2] at hrb
                  unfold remRebuildBudget futureRebuildBudget at hrb
                  dsimp only [nLive] at hrb
                  have hlt_exp : s.frontier <
                      s.mem (base + hdrItemHi) +
                        pairStreamWords (Dictionary.dom s_dict).card
                          (s.mem (base + hdrQHi)) (valBits V) w := hlt
                  simp only [show (2 : ℕ) ≠ 1 by decide, hlt_exp, and_self, ↓reduceIte] at hrb
                  have hdiv_add :
                      (s.mem (base + hdrItemHi) +
                        pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQHi))
                          (valBits V) w - s.frontier + 1022) / 1022 =
                        (s.mem (base + hdrItemHi) +
                          pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQHi))
                            (valBits V) w - s.frontier) / 1022 + 1 :=
                    Nat.add_div_right _ (by decide : 0 < 1022)
                  rw [hdiv_add] at hrb
                  have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                  dsimp only [nSrc] at hf2
                  generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef at hrb hf2 ⊢
                  clear *- hrb hf2
                  omega }
          sl_le7 := fun _ => by
            refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
              dsimp only [L']
              have hl := hlen_s (by clear *- hp2; omega) hs_p
              simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
              exact hl⟩
            rw [hio_s]; exact hsl_s }
  · -- Transitions `2 → 3` (`hiFr ≤ s.frontier`):
    have hge_hi : hiFr ≤ s.frontier := Nat.le_of_not_lt hlt
    have hlt_raw : ¬(s.frontier < s.mem (base + hdrItemHi) +
        pairStreamWords (s.mem (base + hdrLive)) (s.mem (base + hdrQHi))
          (s.mem (base + hdrValBits)) (s.mem (base + hdrW))) := by rwa [hcond_eq]
    have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
      (show qHi + vB ≤ 2 * w by clear *- hqHi_w hvb_w; omega)
    have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
      unfold bulkBatchWhp; clear *- hfr_hi_mid hpw2; omega
    set s_sp : Memory.State :=
      { mem := Function.update s.mem (base + hdrSplit) nLive, frontier := s.frontier }
    set io_sp := splitSlotIo w vB base ibLo qLo ibHi qHi nLive
    have hs_io_eq : (Memory.spec 0).clientState s_sp
        (setSplitSlotIoProg ((base, base + hdrPBase0), s.mem (base + hdrLive))) =
        (Memory.spec 0).clientState s_sp (setSlotIoProg (base + hdrPBase0, io_sp.toCtx)) := by
      have hev := (setSplitSlotIoProg_eval base (base + hdrPBase0) (s.mem (base + hdrLive)) s_sp).1
      have hw_sp : s_sp.mem (base + hdrW) = w :=
        (Function.update_of_ne (base_add_ne (by decide)) _ _).trans hw_eq
      have hvb_sp : s_sp.mem (base + hdrValBits) = vB :=
        (Function.update_of_ne (base_add_ne (by decide)) _ _).trans hvb_eq
      have hil_sp : s_sp.mem (base + hdrItemLo) = ibLo :=
        Function.update_of_ne (base_add_ne (by decide)) _ _
      have hql_sp : s_sp.mem (base + hdrQLo) = qLo :=
        Function.update_of_ne (base_add_ne (by decide)) _ _
      have hih_sp : s_sp.mem (base + hdrItemHi) = ibHi :=
        Function.update_of_ne (base_add_ne (by decide)) _ _
      have hqh_sp : s_sp.mem (base + hdrQHi) = qHi :=
        Function.update_of_ne (base_add_ne (by decide)) _ _
      rw [hlive_eq] at hev ⊢
      rw [hev, hw_sp, hvb_sp, hil_sp, hql_sp, hih_sp, hqh_sp]
    set s_io := (Memory.spec 0).clientState s_sp (setSlotIoProg (base + hdrPBase0, io_sp.toCtx))
    have hfr_io : s_io.frontier = s.frontier := runClient_frontier_setSlotIoProg _ s_sp
    have hs_tick_eq : s_tick =
        { mem := Function.update s_io.mem (base + hdrPhase) 3, frontier := s.frontier } := by
      rw [hst_bg, hst_gr, ite_eq_right hlt_raw]
      have hsp_eq :
          Memory.State.mk (Function.update s.mem (base + hdrSplit) (s.mem (base + hdrLive)))
            s.frontier = s_sp := by rw [hlive_eq]
      rw [hsp_eq, hs_io_eq, hfr_io]
    have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
    have hframe_io := setSlotIoProg_frame (base + hdrPBase0) io_sp.toCtx
    have hvals_io := setSlotIoProg_mem_vals (base + hdrPBase0) io_sp s_sp
    have hout_t : ∀ a, a ≠ base + hdrPhase →
        ¬(base + hdrPBase0 + 48 ≤ a ∧ a < base + hdrPBase0 + 61) →
        a ≠ base + hdrSplit → s_tick.mem a = s.mem a := by
      intro a hp hp0 hsp
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne hp, hframe_io.mem_outside s_sp a hp0]
      exact Function.update_of_ne hsp _ _
    have hout_off : ∀ off < 112, off ≠ hdrPhase → off ≠ hdrSplit →
        s_tick.mem (base + off) = s.mem (base + off) :=
      fun off hoff hp hsp =>
        hout_t (base + off) (base_add_ne hp)
          (by dsimp only [hdrPBase0]; clear *- hoff; omega) (base_add_ne hsp)
    have hph_t : s_tick.mem (base + hdrPhase) = 3 := by
      rw [hs_tick_eq]; exact Function.update_self ..
    have hsp_t : s_tick.mem (base + hdrSplit) = nLive := by
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (base_add_ne (by decide)),
        hframe_io.mem_outside s_sp (base + hdrSplit) (by dsimp only [hdrPBase0, hdrSplit]; omega)]
      exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = 0 :=
      (hout_off hdrStage (by decide) (by decide) (by decide)).trans hst0
    have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
      hout_off hdrNSrc (by decide) (by decide) (by decide)
    have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
      hout_off hdrNDst (by decide) (by decide) (by decide)
    have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
      hout_off hdrMSrc (by decide) (by decide) (by decide)
    have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
      hout_off hdrMDst (by decide) (by decide) (by decide)
    have hpad_t : s_tick.mem (base + hdrPad) = pad :=
      hout_off hdrPad (by decide) (by decide) (by decide)
    have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
      hout_off hdrItemLo (by decide) (by decide) (by decide)
    have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
      hout_off hdrItemHi (by decide) (by decide) (by decide)
    have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
      hout_off hdrQLo (by decide) (by decide) (by decide)
    have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
      hout_off hdrQHi (by decide) (by decide) (by decide)
    have hnLive_w : nLive < 2 ^ w := lt_of_le_of_lt hlive_le hUw
    have hv_sp_hi : io_sp.Valid w hiFr := by
      unfold SlotIoLayout.Valid; dsimp only [io_sp, splitSlotIo]
      simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
      exact ⟨hw_pos, trivial, hqLo_w, hvb_w, hnLive_w, hqLo_le_qHi, hqHi_w,
        by dsimp only [hdrSplit]; clear *- hibLo_eq; omega,
        by clear *- hibLo_le_ibHi; omega, le_rfl⟩
    have hv_sp_fr : io_sp.Valid w s.frontier := by
      unfold SlotIoLayout.Valid; dsimp only [io_sp, splitSlotIo]
      simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
      exact ⟨hw_pos, trivial, hqLo_w, hvb_w, hnLive_w, hqLo_le_qHi, hqHi_w,
        by dsimp only [hdrSplit]; clear *- hibLo_eq; omega,
        by clear *- hibLo_le_ibHi; omega, hge_hi⟩
    have hcnt_le : s.mem (dualMbSrc base s.mem + 1) ≤ nLive := by
      have hsi := hsl_s.io_stateInv
      unfold SlotIoLayout.StateInv at hsi; dsimp only [directSlotIo] at hsi
      simp only [↓reduceIte] at hsi; exact hsi.1
    have hdisj_m_sp : ∀ a, slotOwnsNonPageMeta c w (dualMbSrc base s.mem) L.slotSrc.nCap a →
        ¬io_sp.OwnsAddr a := by
      intro a ha hown
      rw [hcap_s, hcap_eq] at ha
      unfold slotOwnsNonPageMeta dualMbSrc at ha; rw [ite_eq_left hst0] at ha
      unfold SlotIoLayout.OwnsAddr at hown; dsimp only [io_sp, splitSlotIo] at hown
      simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at hown
      by_cases h0 : nSrc = 0
      · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, h0, ↓reduceIte,
          ne_eq, not_true_eq_false, false_and, or_false] at ha
        dsimp only [hdrSmallMeta0, hdrSplit, ibLo, ibHi] at ha hown hibLo_eq hibLo_le_ibHi
        clear *- ha hown hibLo_eq hibLo_le_ibHi; omega
      · have hth_s : whpThreshold c ≤ nSrc := by
          rcases hnSrc_b with hz | ⟨hth, _⟩
          · exact absurd hz h0
          · exact hth
        have hod_le : offPageDir c w nSrc ≤ mSrc :=
          (epochMeta_offsets_le hth_s).2.2.2.trans hmSrc_eq.symm.le
        have hmS_ge : 32 ≤ mSrc :=
          (epochMeta_offsets_le hth_s).1.trans
            ((epochMeta_offsets_le hth_s).2.1.trans
              ((epochMeta_offsets_le hth_s).2.2.1.trans hod_le))
        simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, h0, ↓reduceIte] at ha
        dsimp only [hdrSplit, mSrc, ibLo, ibHi] at ha hown hibLo_eq hibLo_le_ibHi hod_le hmS_ge
        rcases ha with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
        · clear *- h1 h2 hmS_ge hown hibLo_eq hibLo_le_ibHi; omega
        · clear *- h1 h2 hod_le hown hibLo_eq hibLo_le_ibHi; omega
    have hsl_t_fr : EpochSlotInv c U V w s.frontier (dualPSrc base s.mem) (dualMbSrc base s.mem)
        io_sp 0 false L.slotSrc s_tick.mem := by
      have hpS_eq : dualPSrc base s.mem = base + hdrPBase0 := by
        unfold dualPSrc; rw [ite_eq_left hst0]
      rw [hpS_eq] at hsl_s ⊢
      refine hsl_s.set_slotIo hv_sp_fr rfl
        ⟨fun h0 => by
          rw [hcap_s, hcap_eq] at h0; dsimp only [io_sp, splitSlotIo]
          rw [hqLo_eq, ite_eq_left h0],
         fun h0 => by
          rw [hcap_s, hcap_eq] at h0 ⊢; dsimp only [io_sp, splitSlotIo]
          rw [hqLo_eq, ite_eq_right h0]⟩
        rfl
        (fun k hk => by
          apply hout_t
          · dsimp only [hdrPBase0, hdrPhase]; clear *- hk; omega
          · clear *- hk; omega
          · dsimp only [hdrPBase0, hdrSplit]; clear *- hk; omega)
        (by
          have hne_ph : ∀ j < 13, base + hdrPBase0 + (48 + j) ≠ base + hdrPhase := by
            intro j hj; dsimp only [hdrPBase0, hdrPhase]; clear *- hj; omega
          have hrw : ∀ j < 13, s_tick.mem (base + hdrPBase0 + (48 + j)) =
              s_io.mem (base + hdrPBase0 + (48 + j)) := fun j hj => by
            rw [hs_tick_eq]; exact Function.update_of_ne (hne_ph j hj) _ _
          exact ⟨(hrw 0 (by decide)).trans hvals_io.1,
            (hrw 1 (by decide)).trans hvals_io.2.1,
            (hrw 2 (by decide)).trans hvals_io.2.2.1,
            (hrw 3 (by decide)).trans hvals_io.2.2.2.1,
            (hrw 4 (by decide)).trans hvals_io.2.2.2.2.1,
            (hrw 5 (by decide)).trans hvals_io.2.2.2.2.2.1,
            (hrw 6 (by decide)).trans hvals_io.2.2.2.2.2.2.1,
            (hrw 7 (by decide)).trans hvals_io.2.2.2.2.2.2.2.1,
            (hrw 8 (by decide)).trans hvals_io.2.2.2.2.2.2.2.2.1,
            (hrw 9 (by decide)).trans hvals_io.2.2.2.2.2.2.2.2.2.1,
            (hrw 10 (by decide)).trans hvals_io.2.2.2.2.2.2.2.2.2.2.1,
            (hrw 11 (by decide)).trans hvals_io.2.2.2.2.2.2.2.2.2.2.2.1,
            (hrw 12 (by decide)).trans hvals_io.2.2.2.2.2.2.2.2.2.2.2.2⟩)
        (fun a h1 h2 hown => by
          unfold SlotIoLayout.OwnsAddr at hown; dsimp only [io_sp, splitSlotIo, hdrSplit,
            hdrPBase0] at h1 h2 hown
          simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at hown
          clear *- h1 h2 hown hibLo_eq hibLo_le_ibHi; omega)
        hdisj_m_sp
        (fun a ha => by
          have ha_r := slotOwnsNonPageMeta_src_range hcap_s (fun hne => absurd hst0 hne) ha
          rcases ha_r with ⟨h1, h2⟩ | h192
          · apply hout_t <;> (dsimp only [hdrPhase, hdrPBase0, hdrSplit]; clear *- h1 h2; omega)
          · apply hout_t <;> (dsimp only [hdrPhase, hdrPBase0, hdrSplit]; clear *- h192; omega))
        (by
          unfold SlotIoLayout.StateInv; dsimp only [io_sp, splitSlotIo]
          simp only [↓reduceIte]; exact ⟨hcnt_le, Or.inr hqHi_w⟩)
        (fun p hp => by
          have hp_lt : p < nLive := lt_of_lt_of_le hp hcnt_le
          unfold slotIoPairAt
          dsimp only [io_sp, splitSlotIo, directSlotIo, SlotIoLayout.splitCfg, arenaPairAt]
          simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
          rw [hsp_t]
          unfold splitPairRead; dsimp only
          rw [ite_eq_left hp_lt]
          have hlo_eq : ∀ a, ibLo ≤ a → a < ibLo + pairStreamWords nLive qLo vB w →
              s_tick.mem a = s.mem a := fun a h1 _ => by
            apply hout_t <;>
              (dsimp only [hdrPhase, hdrPBase0, hdrSplit]; clear *- h1 hibLo_eq; omega)
          have hq_eq :
              pairQuotAt ibLo qLo vB w s_tick.mem p = pairQuotAt ibLo qLo vB w s.mem p := by
            have hlt_q := wOffQ_add_one_lt_pairStreamWords (q_bits := qLo) (v_bits := vB)
              hw_pos hp_lt
            unfold pairQuotAt readBitSlice; dsimp only
            rw [hlo_eq _ (Nat.le_add_right _ _) (by clear *- hlt_q; omega),
              hlo_eq _ (by omega) (by clear *- hlt_q; omega)]
          have hv_eq : pairValAt ibLo qLo vB w s_tick.mem p = pairValAt ibLo qLo vB w s.mem p := by
            have hlt_v := wOffV_add_one_lt_pairStreamWords (q_bits := qLo) (v_bits := vB)
              hw_pos hp_lt
            unfold pairValAt readBitSlice; dsimp only
            rw [hlo_eq _ (Nat.le_add_right _ _) (by clear *- hlt_v; omega),
              hlo_eq _ (by omega) (by clear *- hlt_v; omega)]
          rw [hq_eq, hv_eq, Nat.mod_eq_of_lt (pairQuotAt_lt ..)])
    have hsl_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem) (dualMbSrc base s_tick.mem)
        io_sp 0 false L.slotSrc s_tick.mem := by
      have hpS_t : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
        unfold dualPSrc; rw [hst_t, hst0]
      have hmS_t_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
        unfold dualMbSrc; rw [hst_t, hnS_t, hst0]; rfl
      rw [hpS_t, hmS_t_mb]
      refine hsl_t_fr.at_exact_frontier
        (by unfold dualPSrc; rw [ite_eq_left hst0]; dsimp only [hiFr, hdrPBase0]
            clear *- hibLo_eq hibLo_le_ibHi; omega)
        (by unfold dualMbSrc; rw [ite_eq_left hst0, hcap_s, hcap_eq]
            change (if nSrc = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) + 2
              else (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) +
                epochMetaWordsWhp c w nSrc) ≤ hiFr
            rw [← hmSrc_eq]
            by_cases h0 : nSrc = 0
            · rw [ite_eq_left h0, ite_eq_left h0]; dsimp only [hdrSmallMeta0, hiFr]
              clear *- hibLo_eq hibLo_le_ibHi; omega
            · rw [ite_eq_right h0, ite_eq_right h0]; dsimp only [hiFr]
              clear *- hibLo_eq hibLo_le_ibHi; omega)
        (by dsimp only [io_sp, splitSlotIo]; exact le_rfl)
    refine ⟨hpre_bg, hfr_tick, hwf_tick,
      fun addr hlt_b => hout_t addr (by dsimp only [hdrPhase]; clear *- hlt_b; omega)
        (by dsimp only [hdrPBase0]; clear *- hlt_b; omega)
        (by dsimp only [hdrSplit]; clear *- hlt_b; omega), ?_⟩
    rw [ite_eq_left (by clear *- hp2; omega)]
    refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
        (fun ⟨h9, _⟩ => by rw [hp2] at h9; cases h9) rfl rfl, ?_,
      fun _ _ => by unfold itemBatchWhp; clear *- hmc_bg hmc_gr; omega⟩
    refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
    · rw [hnS_t, hph_t, ite_eq_right (by decide : 3 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
    · rw [hph_t, ite_eq_right (by decide : ¬(3 < 2)), ite_eq_right (by decide : 3 ≠ 2),
        ite_eq_left (by decide : 3 ≤ 10), hibH_t, hqH_t, hfr_tick]
      refine ⟨hge_hi, hdiff_le, ?_⟩
      exact
        { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
          wf := ⟨lt_of_le_of_lt hge_hi hwf.1, fun a => hwf_tick.2 a⟩
          base_fr := by dsimp only [hiFr]; clear *- hibLo_eq hibLo_le_ibHi; omega
          hdr := rootStaticHeader_congr hhdr fun off hoff =>
            hout_off off (by clear *- hoff; omega) (by dsimp only [hdrPhase]; clear *- hoff; omega)
              (by dsimp only [hdrSplit]; clear *- hoff; omega)
          live_eq := (hout_off hdrLive (by decide) (by decide) (by decide)).trans hlive_eq
          live_le := hlive_le
          ph_le := by dsimp only; rw [hph_t]; decide
          stg_le := by dsimp only; rw [hst_t]; decide
          mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
          cache_src := by
            dsimp only; rw [hnS_t]
            exact hostCacheValid_congr_mem hcache_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
          nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
          sched := by
            dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
            refine
              { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                nDst_zero := fun hz => by
                  dsimp only at hz ⊢
                  obtain ⟨hs_p, _, _, _, _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                  rw [hnS_t, hst_t, hph_t]
                  exact ⟨hs_p, rfl, by decide, by decide, by decide⟩
                stg_one := fun h1 => by
                  dsimp only at h1; exact absurd (hst_t.symm.trans h1) (by decide)
                post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                drift_hi := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                drift_lo := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                ibLo_eq := by
                  dsimp only; rw [hibL_t, hph_t, ite_eq_left (by decide : 3 < 10), hmS_t]
                  exact hibLo_eq
                qLo_eq := by
                  dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 3 < 10), hnS_t]
                  exact hqLo_eq
                ph1 := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
                ge2 := fun _ => by
                  dsimp only
                  rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                  refine ⟨hmDst_eq, hpad_eq, ?_, fun hd_p => ?_, hibHi_eq, hqHi_eq⟩
                  · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                      rw [Nat.add_assoc]
                      exact hout_off (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrSplit]; clear *- hk; omega)
                  · obtain ⟨e1, e2, e3⟩ := hlog_d hd_p
                    exact ⟨(hout_off hdrLogN (by decide) (by decide) (by decide)).trans e1,
                      (hout_off hdrEll (by decide) (by decide) (by decide)).trans e2,
                      (hout_off hdrPgB (by decide) (by decide) (by decide)).trans e3⟩
                ph2 := fun h2 => by dsimp only at h2; exact absurd (hph_t.symm.trans h2) (by decide)
                ph3_10 := fun _ => by
                  dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                ph11 := fun h11 => by
                  dsimp only at h11; exact absurd (hph_t.symm.trans h11) (by decide)
                budget := by
                  dsimp only [L']
                  rw [hnS_t, hst_t, hph_t, hsp_t]
                  unfold remRebuildBudget futureRebuildBudget
                  dsimp only
                  simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
                  have hrb := hrem_b.2.1
                  rw [hst0, hp2] at hrb
                  unfold remRebuildBudget futureRebuildBudget at hrb
                  dsimp only at hrb
                  simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte] at hrb
                  have hd_hi' : nLive ≤ L.nTrig + (L.elapsed + 1) := by
                    have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                  have hd_lo' : L.nTrig ≤ nLive + (L.elapsed + 1) := by
                    have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                  have hel_le' : 16 * (L.elapsed + 1) ≤ max (whpThreshold c) nSrc := by
                    have hel := hrem_b.2.2; clear *- hel; omega
                  have hnL_2R := (active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap
                    hd_hi' hd_lo' hel_le' hlive_le).2
                  have hdiv_nL : nLive / 1024 ≤ (2 * max (whpThreshold c) nSrc + 512) / 1024 :=
                    Nat.div_le_div_right (by clear *- hnL_2R; omega)
                  have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                  change nLive / 1024 ≤ (2 * max (whpThreshold c) nSrc + 512) / 1024 at hdiv_nL
                  generalize max (whpThreshold c) nSrc = nRef at hrb hdiv_nL hf2 ⊢
                  clear *- hrb hdiv_nL hf2
                  omega }
          pad_fits := by
            dsimp only
            rw [hnS_t, hph_t, ite_eq_right (by decide : 3 ≠ 0), hnD_t]
            have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp2; omega)] at hp
          ph1_inv := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
          ph3_inv := fun _ => by
            dsimp only
            rw [hsp_t, hibL_t, hqL_t, hibH_t, hqH_t]
            refine ⟨le_rfl, fun idx hlo hhi => ?_⟩
            dsimp only [splitSlotIo] at hlo
            rw [hsp_t] at hlo
            exact absurd (lt_of_le_of_lt hlo hhi) (Nat.lt_irrefl _)
          ph4_inv := fun h4 => by dsimp only at h4; exact absurd (hph_t.symm.trans h4) (by decide)
          pDst_pre := fun _ _ hd_p => by
            dsimp only at hd_p ⊢
            rw [hnD_t] at hd_p
            have hmbD : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
              unfold dualMbDst
              rw [hph_t, hp2, ite_eq_left (by decide : 3 < 10), ite_eq_left (by decide : 2 < 10),
                hnD_t, hst_t, hpad_t, hst0]
            have hpD : dualPDst base s_tick.mem = base + hdrPBase1 := by
              unfold dualPDst
              rw [hph_t, ite_eq_left (by decide : 3 < 10), hst_t, ite_eq_left rfl]
            have hpD_s : dualPDst base s.mem = base + hdrPBase1 := by
              unfold dualPDst
              rw [hp2, ite_eq_left (by decide : 2 < 10), hst0, ite_eq_left rfl]
            have hpt_s := h.pDst_pre ⟨by clear *- hp2; omega, by clear *- hp2; omega⟩
              (Or.inr hst0) hd_p
            dsimp only at hpt_s
            rw [hpD_s] at hpt_s
            rw [hnD_t, hmbD, hpD, hibH_t, hqH_t]
            exact fastParamTable_mask_congr hpt_s fun k hk => by
              apply hout_t <;>
                (dsimp only [hdrPBase1, hdrPBase0, hdrPhase, hdrSplit]; clear *- hk; omega)
          ph5_inv := fun h5 => by dsimp only at h5; exact absurd (hph_t.symm.trans h5) (by decide)
          ph6_inv := fun h6 => by dsimp only at h6; exact absurd (hph_t.symm.trans h6) (by decide)
          ph7_inv := fun h7 => by dsimp only at h7; exact absurd (hph_t.symm.trans h7) (by decide)
          ph8_inv := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
          ph9_inv := fun h9 => by dsimp only at h9; exact absurd (hph_t.symm.trans h9) (by decide)
          ph10_inv := fun h10 => by
            dsimp only at h10; exact absurd (hph_t.symm.trans h10) (by decide)
          sl_le7 := fun _ => by
            dsimp only
            have hcap_t : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
              unfold dualCapSrc; simp only [hst_t, hnS_t, hst0, ↓reduceIte]; rfl
            rw [hcap_t, hph_t]
            refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
              dsimp only [L']
              have hl := hlen_s (by clear *- hp2; omega) hs_p
              simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
              exact hl⟩
            unfold activeSrcIo
            rw [ite_eq_right (by decide : ¬(3 < 3)), ite_eq_left rfl,
              hibL_t, hqL_t, hibH_t, hqH_t]
            exact hsl_hi
          sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; clear *- h67; omega
          sl_8 := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
          sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; clear *- h9; omega }

/-! ## Section 3: Phase `3` (`tickSlideUpProg`) Specification -/

/-- Phase `3` (`slideUp`) background tick specification. -/
theorem tickPhase3_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp3 : s.mem (base + hdrPhase) = 3) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb192 := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp3; omega)] at hsched
  have hst0 : s.mem (base + hdrStage) = 0 := by
    have hs_le := h.stg_le
    by_cases h1 : s.mem (base + hdrStage) = 1
    · have h4 := (hsched.stg_one h1).2.1; clear *- hp3 h4; omega
    · clear *- hs_le h1; omega
  obtain ⟨hfr_hi_lo, hfr_hi_mid⟩ := hsched.ph3_10 ⟨by clear *- hp3; omega, by clear *- hp3; omega⟩
  simp only [↓reduceIte] at hfr_hi_mid
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hlog_d, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp3; omega)
  obtain ⟨hvb_eq, hvb_w, hqLo_w, hqHi_w, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by clear *- hp3; omega)] at hpad_hi_s
  obtain ⟨hsp_le, hhi_quot⟩ := h.ph3_inv hp3
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hw_eq : s.mem (base + hdrW) = w := hhdr.2.2.1
  set nLive := (Dictionary.dom s_dict).card
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set sp := s.mem (base + hdrSplit)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  have hibLo_eq : ibLo = base + 192 + mSrc := by
    have hib := hsched.ibLo_eq; rwa [ite_eq_left (by clear *- hp3; omega)] at hib
  have hqLo_eq : qLo = (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) := by
    have hq := hsched.qLo_eq; rwa [ite_eq_left (by clear *- hp3; omega)] at hq
  have hqLo_le_qHi : qLo ≤ qHi := by
    rw [hqHi_eq, ← hqLo_eq]; exact le_max_left _ _
  have hibLo_le_ibHi : ibLo + 4 ≤ ibHi := by
    have hm_le : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
    rw [hibHi_eq, hibLo_eq]
    split_ifs <;> (clear *- hm_le; omega)
  have hnLive_w : nLive < 2 ^ w := lt_of_le_of_lt hlive_le hUw
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show qHi + vB ≤ 2 * w by clear *- hqHi_w hvb_w; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    unfold bulkBatchWhp; clear *- hfr_hi_mid hpw2; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive :=
    hfr_hi_mid.trans hpad_hi_s
  let cfg : SplitPairCfg :=
    { baseLo := ibLo, qBitsLo := qLo, vBitsLo := vB,
      baseHi := ibHi, qBitsHi := qHi, vBitsHi := vB, w := w }
  have hctx_eq : (Memory.spec 0).clientResult s (loadSplitPairCtxProg base) = cfg.toCtx := by
    rw [(loadSplitPairCtxProg_eval base s).2.1]
    dsimp only [cfg, SplitPairCfg.toCtx]; rw [hvb_eq, hw_eq]
  have hcfg_v : cfg.Valid w nLive s.frontier :=
    ⟨hw_pos, rfl, hqLo_w, hvb_w, hqHi_w, hvb_w,
      by dsimp only [cfg]; clear *- hqLo_le_qHi; omega,
      by dsimp only [cfg]; clear *- hibLo_le_ibHi; omega,
      hnLive_w, hfr_hi_lo⟩
  obtain ⟨hsafe_sb, hres_sb, hfr_sb, hmc_sb, hread_sb, hout_sb⟩ :=
    slideUpBatchProg_spec (cfg := cfg) (n_tot := nLive) (s_split := sp) (s := s)
      hcfg_v hqLo_le_qHi le_rfl hsp_le itemBatchWhp
  have hpre_slide : TickSlideUpPre w base s := by
    refine ⟨hw11, hb192, ?_⟩
    dsimp only; rw [hctx_eq]
    exact ⟨⟨nLive, hsp_le, by simpa only [SplitPairCfg.ofCtx_toCtx] using hcfg_v⟩, hsafe_sb⟩
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, ?_⟩
    dsimp only
    rw [ite_eq_right (by clear *- hp3; omega), ite_eq_right (by clear *- hp3; omega),
      ite_eq_right (by clear *- hp3; omega), ite_eq_left hp3]
    exact hpre_slide
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  simp only [hp3, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
    show (3 : ℕ) ≠ 2 by decide, show (3 : ℕ) ≠ 5 by decide, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_sl, hmc_sl⟩ := tickSlideUpProg_eval base s
  dsimp only at hst_sl hmc_sl
  rw [hctx_eq] at hst_sl hmc_sl
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hwf_tick : Memory.WellFormed w s_tick :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  set s2 := (Memory.spec 0).clientState s (slideUpBatchProg ((cfg.toCtx, sp), itemBatchWhp))
  set sp' := sp - itemBatchWhp
  set s3 : Memory.State :=
    { mem := Function.update s2.mem (base + hdrSplit) sp', frontier := s.frontier }
  have hs3_eq_raw :
      ({ mem := Function.update s2.mem (base + hdrSplit)
          ((Memory.spec 0).clientResult s (slideUpBatchProg ((cfg.toCtx, sp), itemBatchWhp))),
         frontier := s2.frontier } : Memory.State) = s3 := by
    rw [hres_sb, hfr_sb]
  have hout_s3 : ∀ a, a ≠ base + hdrSplit → ¬(ibHi ≤ a ∧ a < hiFr) → s3.mem a = s.mem a := by
    intro a hsp ha
    dsimp only [s3]
    rw [Function.update_of_ne hsp]
    exact hout_sb a ha
  have hs3_read : ∀ idx, splitPairRead cfg sp' s3.mem idx = splitPairRead cfg sp s.mem idx := by
    intro idx
    have heq_s2 : splitPairRead cfg sp' s3.mem idx = splitPairRead cfg sp' s2.mem idx := by
      unfold splitPairRead
      by_cases hlt_i : idx < sp'
      · rw [ite_eq_left hlt_i, ite_eq_left hlt_i]
        unfold pairQuotAt pairValAt readBitSlice; dsimp only [cfg, s3]
        iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrSplit]; clear *- hibLo_eq; omega)]
      · rw [ite_eq_right hlt_i, ite_eq_right hlt_i]
        unfold pairQuotAt pairValAt readBitSlice; dsimp only [cfg, s3]
        iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrSplit]; clear *- hibLo_eq hibLo_le_ibHi; omega)]
    exact heq_s2.trans (hread_sb idx)
  set io_sp := splitSlotIo w vB base ibLo qLo ibHi qHi nLive
  have hs3_hiQuot : SplitHiQuotBounded io_sp nLive s3.mem := by
    intro idx hlo hhi
    dsimp only [io_sp, splitSlotIo] at hlo ⊢
    have hsp3 : s3.mem (base + hdrSplit) = sp' := Function.update_self ..
    rw [hsp3] at hlo
    have hrd := congrArg Prod.fst (hs3_read idx)
    unfold splitPairRead at hrd
    rw [ite_eq_right (Nat.not_lt.mpr hlo)] at hrd
    dsimp only [cfg] at hrd
    rw [hrd]
    by_cases hlt_old : idx < sp
    · rw [ite_eq_left hlt_old]; exact pairQuotAt_lt ..
    · rw [ite_eq_right hlt_old]
      exact hhi_quot idx (Nat.le_of_not_lt hlt_old) hhi
  obtain ⟨hcap_s, hdict_s, hsl_s, hlen_s⟩ := h.sl_le7 (by clear *- hp3; omega)
  have hcap_eq : dualCapSrc base s.mem = nSrc := by
    unfold dualCapSrc; rw [ite_eq_left hst0]
  have hio_s : activeSrcIo c w vB base (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
      nSrc nDst pad ibLo qLo ibHi qHi nLive = io_sp := by
    unfold activeSrcIo
    rw [ite_eq_right (by clear *- hp3; omega), ite_eq_left hp3]
  rw [hio_s] at hsl_s
  have hcnt_le : s.mem (dualMbSrc base s.mem + 1) ≤ nLive := by
    have hsi := hsl_s.io_stateInv
    unfold SlotIoLayout.StateInv at hsi; dsimp only [io_sp, splitSlotIo] at hsi
    simp only [↓reduceIte] at hsi; exact hsi.1
  have hrem_b := hsched.budget
  dsimp only at hrem_b
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
  have hs3_pair : ∀ p < s.mem (dualMbSrc base s.mem + 1),
      slotIoPairAt io_sp s3.mem p = slotIoPairAt io_sp s.mem p := by
    intro p _
    unfold slotIoPairAt
    dsimp only [io_sp, splitSlotIo, SlotIoLayout.splitCfg]
    simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
    have hsp3 : s3.mem (base + hdrSplit) = sp' := Function.update_self ..
    rw [hsp3]
    change (let q := splitPairRead cfg sp' s3.mem p; (q.1 % 2 ^ qLo, q.2)) =
      (let q := splitPairRead cfg sp s.mem p; (q.1 % 2 ^ qLo, q.2))
    rw [hs3_read p]
  have hm_s3 : ∀ a, slotOwnsNonPageMeta c w (dualMbSrc base s.mem) L.slotSrc.nCap a →
      s3.mem a = s.mem a := by
    intro a ha
    rw [hcap_s, hcap_eq] at ha
    unfold slotOwnsNonPageMeta dualMbSrc at ha; rw [ite_eq_left hst0] at ha
    by_cases h0 : nSrc = 0
    · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, h0, ↓reduceIte,
        ne_eq, not_true_eq_false, false_and, or_false] at ha
      apply hout_s3
      · dsimp only [hdrSmallMeta0, hdrSplit] at ha ⊢; clear *- ha; omega
      · dsimp only [hdrSmallMeta0, ibLo, ibHi] at ha hibLo_eq hibLo_le_ibHi ⊢
        clear *- ha hibLo_eq hibLo_le_ibHi; omega
    · have hth_s : whpThreshold c ≤ nSrc := by
        rcases hnSrc_b with hz | ⟨hth, _⟩
        · exact absurd hz h0
        · exact hth
      have hod_le : offPageDir c w nSrc ≤ mSrc :=
        (epochMeta_offsets_le hth_s).2.2.2.trans hmSrc_eq.symm.le
      have hmS_ge : 32 ≤ mSrc :=
        (epochMeta_offsets_le hth_s).1.trans
          ((epochMeta_offsets_le hth_s).2.1.trans
            ((epochMeta_offsets_le hth_s).2.2.1.trans hod_le))
      simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, h0, ↓reduceIte] at ha
      dsimp only [mSrc, ibLo, ibHi, hiFr] at ha hibLo_eq hibLo_le_ibHi hod_le hmS_ge ⊢
      rcases ha with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
      · apply hout_s3
        · dsimp only [hdrSplit]; clear *- h1; omega
        · clear *- h1 h2 hmS_ge hibLo_eq hibLo_le_ibHi; omega
      · apply hout_s3
        · dsimp only [hdrSplit]; clear *- h1; omega
        · clear *- h1 h2 hod_le hibLo_eq hibLo_le_ibHi; omega
  have hdisj_m_sp : ∀ a, slotOwnsNonPageMeta c w (dualMbSrc base s.mem) L.slotSrc.nCap a →
      ¬io_sp.OwnsAddr a := by
    intro a ha hown
    rw [hcap_s, hcap_eq] at ha
    unfold slotOwnsNonPageMeta dualMbSrc at ha; rw [ite_eq_left hst0] at ha
    unfold SlotIoLayout.OwnsAddr at hown; dsimp only [io_sp, splitSlotIo] at hown
    simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at hown
    by_cases h0 : nSrc = 0
    · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, h0, ↓reduceIte,
        ne_eq, not_true_eq_false, false_and, or_false] at ha
      dsimp only [hdrSmallMeta0, hdrSplit, ibLo, ibHi] at ha hown hibLo_eq hibLo_le_ibHi
      clear *- ha hown hibLo_eq hibLo_le_ibHi; omega
    · have hth_s : whpThreshold c ≤ nSrc := by
        rcases hnSrc_b with hz | ⟨hth, _⟩
        · exact absurd hz h0
        · exact hth
      have hod_le : offPageDir c w nSrc ≤ mSrc :=
        (epochMeta_offsets_le hth_s).2.2.2.trans hmSrc_eq.symm.le
      have hmS_ge : 32 ≤ mSrc :=
        (epochMeta_offsets_le hth_s).1.trans
          ((epochMeta_offsets_le hth_s).2.1.trans
            ((epochMeta_offsets_le hth_s).2.2.1.trans hod_le))
      simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, h0, ↓reduceIte] at ha
      dsimp only [hdrSplit, mSrc, ibLo, ibHi] at ha hown hibLo_eq hibLo_le_ibHi hod_le hmS_ge
      rcases ha with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
      · clear *- h1 h2 hmS_ge hown hibLo_eq hibLo_le_ibHi; omega
      · clear *- h1 h2 hod_le hown hibLo_eq hibLo_le_ibHi; omega
  by_cases hsp0 : sp' = 0
  · -- Completion (`sp' = 0`): switches `pBase0` to `directSlotIo w vB base ibHi qHi nLive`
    have hsp0_raw : (Memory.spec 0).clientResult s
        (slideUpBatchProg ((cfg.toCtx, sp), itemBatchWhp)) = 0 := hres_sb.trans hsp0
    set io_dir := directSlotIo w vB base ibHi qHi nLive
    have hs4_eq : (Memory.spec 0).clientState s3
        (setDirectSlotIoProg ((base, base + hdrPBase0), ((ibHi, qHi), s.mem (base + hdrLive)))) =
        (Memory.spec 0).clientState s3 (setSlotIoProg (base + hdrPBase0, io_dir.toCtx)) := by
      have hev := (setDirectSlotIoProg_eval base (base + hdrPBase0) ibHi qHi
        (s.mem (base + hdrLive)) s3).1
      have hw_s3 : s3.mem (base + hdrW) = w :=
        (hout_s3 (base + hdrW) (base_add_ne (by decide))
          (by dsimp only [hdrW]; clear *- hibLo_eq hibLo_le_ibHi; omega)).trans hw_eq
      have hvb_s3 : s3.mem (base + hdrValBits) = vB :=
        (hout_s3 (base + hdrValBits) (base_add_ne (by decide))
          (by dsimp only [hdrValBits]; clear *- hibLo_eq hibLo_le_ibHi; omega)).trans hvb_eq
      rw [hlive_eq] at hev ⊢
      rw [hev, hw_s3, hvb_s3]
    set s4 := (Memory.spec 0).clientState s3 (setSlotIoProg (base + hdrPBase0, io_dir.toCtx))
    have hfr_s4 : s4.frontier = s.frontier := runClient_frontier_setSlotIoProg _ s3
    have hframe_s4 := setSlotIoProg_frame (base + hdrPBase0) io_dir.toCtx
    have hvals_s4 := setSlotIoProg_mem_vals (base + hdrPBase0) io_dir s3
    have hq_dir_valid :
        (L.slotSrc.nCap = 0 → io_dir.pgL.qBits = keyBits U) ∧
        (L.slotSrc.nCap ≠ 0 → quotBitsWhp U L.slotSrc.nCap ≤ io_dir.pgL.qBits) := by
      rw [hcap_s, hcap_eq]; dsimp only [io_dir, directSlotIo]
      refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · have hqD_le : (if nDst = 0 then keyBits U else quotBitsWhp U nDst) ≤ keyBits U := by
          split_ifs
          · exact le_rfl
          · exact Nat.sub_le _ _
        rw [hqHi_eq, ite_eq_left h0]
        exact max_eq_left hqD_le
      · have hqL0 : quotBitsWhp U nSrc = qLo := by rw [hqLo_eq, ite_eq_right h0]
        rw [hqL0]; exact hqLo_le_qHi
    have hv_dir_fr : io_dir.Valid w s.frontier := by
      unfold SlotIoLayout.Valid; dsimp only [io_dir, directSlotIo]
      simp only [↓reduceIte]
      exact ⟨hw_pos, trivial, hqHi_w, hvb_w, hnLive_w, hfr_hi_lo⟩
    have hdisj_m_dir : ∀ a, slotOwnsNonPageMeta c w (dualMbSrc base s.mem) L.slotSrc.nCap a →
        ¬io_dir.OwnsAddr a := by
      intro a ha hown
      apply hdisj_m_sp a ha
      unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hown ⊢
      dsimp only [io_dir, directSlotIo, io_sp, splitSlotIo] at hown ⊢
      simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at hown ⊢
      exact Or.inr (Or.inr hown)
    have hpair_dir_s3 : ∀ p < s.mem (dualMbSrc base s.mem + 1),
        slotIoPairAt io_dir s3.mem p = slotIoPairAt io_sp s.mem p := by
      intro p hp
      have hp_lt : p < nLive := lt_of_lt_of_le hp hcnt_le
      rw [← hs3_pair p hp]
      have hsp3 : s3.mem (base + hdrSplit) = 0 :=
        (Function.update_self (base + hdrSplit) sp' s2.mem).trans hsp0
      have hq_lt := hs3_hiQuot p (by dsimp only [io_sp, splitSlotIo]; rw [hsp3]; omega) hp_lt
      dsimp only [io_sp, splitSlotIo] at hq_lt
      unfold slotIoPairAt
      dsimp only [io_dir, directSlotIo, io_sp, splitSlotIo, SlotIoLayout.splitCfg, arenaPairAt]
      simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide]
      rw [hsp3]
      unfold splitPairRead; dsimp only
      rw [ite_eq_right (Nat.not_lt_zero p), Nat.mod_eq_of_lt hq_lt]
    by_cases hd0 : nDst = 0
    · -- `3 → 6` (`nDst = 0`, shrinking large `nSrc > 0` to small):
      have hs_pos : 0 < nSrc := (hsched.nDst_zero hd0).1
      have hs_tick_eq : s_tick =
          { mem := Function.update (Function.update (Function.update
              (Function.update s4.mem (base + hdrCur) 0)
              (base + hdrSmallMeta1) 0)
              (base + hdrSmallMeta1 + 1) 0)
              (base + hdrPhase) 6,
            frontier := s.frontier } := by
        rw [hst_bg, hst_sl, hs3_eq_raw, ite_eq_left hsp0_raw, hs4_eq,
          ite_eq_left hd0, hfr_s4]
      have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
      have hout_t : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrSmallMeta1 + 1 →
          a ≠ base + hdrSmallMeta1 → a ≠ base + hdrCur →
          ¬(base + hdrPBase0 + 48 ≤ a ∧ a < base + hdrPBase0 + 61) →
          a ≠ base + hdrSplit → ¬(ibHi ≤ a ∧ a < hiFr) →
          s_tick.mem a = s.mem a := by
        intro a h1 h2 h3 h4 hp0 hsp hhi
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
          Function.update_of_ne h4, hframe_s4.mem_outside s3 a hp0]
        exact hout_s3 a hsp hhi
      have hout_off : ∀ off < 112, off ≠ hdrPhase → off ≠ hdrSmallMeta1 + 1 →
          off ≠ hdrSmallMeta1 → off ≠ hdrCur → off ≠ hdrSplit →
          s_tick.mem (base + off) = s.mem (base + off) :=
        fun off hoff h1 h2 h3 h4 hsp =>
          hout_t (base + off) (base_add_ne h1)
            (by rw [Nat.add_assoc]; exact base_add_ne h2)
            (base_add_ne h3) (base_add_ne h4)
            (by dsimp only [hdrPBase0]; clear *- hoff; omega) (base_add_ne hsp)
            (by clear *- hoff hibLo_eq hibLo_le_ibHi; omega)
      have hph_t : s_tick.mem (base + hdrPhase) = 6 := by
        rw [hs_tick_eq]; exact Function.update_self ..
      have hsm1_1_t : s_tick.mem (base + hdrSmallMeta1 + 1) = 0 := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (by rw [Nat.add_assoc]; exact base_add_ne (by decide))]
        exact Function.update_self ..
      have hsm1_0_t : s_tick.mem (base + hdrSmallMeta1) = 0 := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (by dsimp only [hdrSmallMeta1]; omega)]
        exact Function.update_self ..
      have hcur_t : s_tick.mem (base + hdrCur) = 0 := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (by rw [Nat.add_assoc]; exact base_add_ne (by decide)),
          Function.update_of_ne (base_add_ne (by decide))]
        exact Function.update_self ..
      have hst_t : s_tick.mem (base + hdrStage) = 0 :=
        (hout_off hdrStage (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hst0
      have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
        hout_off hdrNSrc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hnD_t : s_tick.mem (base + hdrNDst) = 0 :=
        (hout_off hdrNDst (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans hd0
      have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
        hout_off hdrMSrc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
        hout_off hdrMDst (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hpad_t : s_tick.mem (base + hdrPad) = pad :=
        hout_off hdrPad (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
        hout_off hdrItemLo (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
        hout_off hdrItemHi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
        hout_off hdrQLo (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
        hout_off hdrQHi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hsl_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
          (dualMbSrc base s_tick.mem) io_dir 0 false L.slotSrc s_tick.mem := by
        have hpS_eq : dualPSrc base s.mem = base + hdrPBase0 := by
          unfold dualPSrc; rw [ite_eq_left hst0]
        have hpS_t : dualPSrc base s_tick.mem = base + hdrPBase0 := by
          unfold dualPSrc; rw [hst_t, ite_eq_left rfl]
        have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
          unfold dualMbSrc; rw [hst_t, hnS_t, hst0]; rfl
        rw [hpS_eq] at hsl_s
        rw [hpS_t, hmS_mb]
        have hsl_fr : EpochSlotInv c U V w s.frontier (base + hdrPBase0) (dualMbSrc base s.mem)
            io_dir 0 false L.slotSrc s_tick.mem :=
          hsl_s.set_slotIo hv_dir_fr rfl hq_dir_valid rfl
            (fun k hk => by
              apply hout_t
              · dsimp only [hdrPBase0, hdrPhase]; clear *- hk; omega
              · dsimp only [hdrPBase0, hdrSmallMeta1]; clear *- hk; omega
              · dsimp only [hdrPBase0, hdrSmallMeta1]; clear *- hk; omega
              · dsimp only [hdrPBase0, hdrCur]; clear *- hk; omega
              · clear *- hk; omega
              · dsimp only [hdrPBase0, hdrSplit]; clear *- hk; omega
              · dsimp only [hdrPBase0]; clear *- hk hibLo_eq hibLo_le_ibHi; omega)
            (by
              have hrw : ∀ j < 13, s_tick.mem (base + hdrPBase0 + (48 + j)) =
                  s4.mem (base + hdrPBase0 + (48 + j)) := fun j hj => by
                rw [hs_tick_eq]; dsimp only
                iterate 4 rw [Function.update_of_ne
                  (by dsimp only [hdrPBase0, hdrPhase, hdrSmallMeta1, hdrCur]; clear *- hj; omega)]
              exact ⟨(hrw 0 (by decide)).trans hvals_s4.1,
                (hrw 1 (by decide)).trans hvals_s4.2.1,
                (hrw 2 (by decide)).trans hvals_s4.2.2.1,
                (hrw 3 (by decide)).trans hvals_s4.2.2.2.1,
                (hrw 4 (by decide)).trans hvals_s4.2.2.2.2.1,
                (hrw 5 (by decide)).trans hvals_s4.2.2.2.2.2.1,
                (hrw 6 (by decide)).trans hvals_s4.2.2.2.2.2.2.1,
                (hrw 7 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.1,
                (hrw 8 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.1,
                (hrw 9 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.1,
                (hrw 10 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.2.1,
                (hrw 11 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.2.2.1,
                (hrw 12 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.2.2.2⟩)
            (fun a h1 h2 hown => by
              unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hown
              dsimp only [io_dir, directSlotIo, hdrPBase0] at h1 h2 hown
              simp only [↓reduceIte] at hown
              clear *- h1 h2 hown hibLo_eq hibLo_le_ibHi; omega)
            hdisj_m_dir
            (fun a ha => by
              have ha192 : base + 192 ≤ a := by
                unfold slotOwnsNonPageMeta dualMbSrc at ha
                rw [ite_eq_left hst0, ite_eq_right hs_pos.ne'] at ha
                rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> (clear *- h1; omega)
              rw [hs_tick_eq]; dsimp only
              iterate 4 rw [Function.update_of_ne
                (by dsimp only [hdrPhase, hdrSmallMeta1, hdrCur]; clear *- ha192; omega)]
              rw [hframe_s4.mem_outside s3 a (by dsimp only [hdrPBase0]; clear *- ha192; omega)]
              exact hm_s3 a ha)
            (by
              unfold SlotIoLayout.StateInv; dsimp only [io_dir, directSlotIo]
              simp only [↓reduceIte]; exact ⟨hcnt_le, Or.inl trivial⟩)
            (fun p hp => by
              have hp_lt : p < nLive := lt_of_lt_of_le hp hcnt_le
              rw [← hpair_dir_s3 p hp]
              have hhi_eq : ∀ a, ibHi ≤ a → a < hiFr → s_tick.mem a = s3.mem a := fun a h1 _ => by
                have ha192 : base + 192 ≤ a := by clear *- h1 hibLo_eq hibLo_le_ibHi; omega
                rw [hs_tick_eq]; dsimp only
                iterate 4 rw [Function.update_of_ne
                  (by dsimp only [hdrPhase, hdrSmallMeta1, hdrCur]; clear *- ha192; omega)]
                exact hframe_s4.mem_outside s3 a (by dsimp only [hdrPBase0]; clear *- ha192; omega)
              unfold slotIoPairAt; dsimp only [io_dir, directSlotIo, arenaPairAt]
              simp only [↓reduceIte]
              have hlt_q := wOffQ_add_one_lt_pairStreamWords (q_bits := qHi) (v_bits := vB)
                hw_pos hp_lt
              have hlt_v := wOffV_add_one_lt_pairStreamWords (q_bits := qHi) (v_bits := vB)
                hw_pos hp_lt
              unfold pairQuotAt pairValAt readBitSlice; dsimp only
              rw [hhi_eq _ (Nat.le_add_right _ _) (by dsimp only [hiFr]; clear *- hlt_q; omega),
                hhi_eq _ (by omega) (by dsimp only [hiFr]; clear *- hlt_q; omega),
                hhi_eq _ (Nat.le_add_right _ _) (by dsimp only [hiFr]; clear *- hlt_v; omega),
                hhi_eq _ (by omega) (by dsimp only [hiFr]; clear *- hlt_v; omega)])
        refine hsl_fr.at_exact_frontier
          (by dsimp only [hiFr, hdrPBase0]; clear *- hibLo_eq hibLo_le_ibHi; omega)
          (by unfold dualMbSrc
              rw [ite_eq_left hst0, ite_eq_right hs_pos.ne', hcap_s, hcap_eq,
                ite_eq_right hs_pos.ne', ← hmSrc_eq]
              dsimp only [hiFr]; clear *- hibLo_eq hibLo_le_ibHi; omega)
          (by dsimp only [io_dir, directSlotIo]; exact le_rfl)
      refine ⟨hpre_bg, hfr_tick, hwf_tick,
        fun addr hlt_b => hout_t addr
          (by dsimp only [hdrPhase]; clear *- hlt_b; omega)
          (by dsimp only [hdrSmallMeta1]; clear *- hlt_b; omega)
          (by dsimp only [hdrSmallMeta1]; clear *- hlt_b; omega)
          (by dsimp only [hdrCur]; clear *- hlt_b; omega)
          (by dsimp only [hdrPBase0]; clear *- hlt_b; omega)
          (by dsimp only [hdrSplit]; clear *- hlt_b; omega)
          (by clear *- hlt_b hibLo_eq hibLo_le_ibHi; omega), ?_⟩
      rw [ite_eq_left (by clear *- hp3; omega)]
      refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
          (fun ⟨h9, _⟩ => by rw [hp3] at h9; cases h9) rfl rfl, ?_,
        fun _ _ => by
          unfold itemBatchWhp at hmc_sl hmc_sb ⊢
          unfold epochStepCost
          dsimp only [sp] at hmc_sb
          clear *- hmc_bg hmc_sl hmc_sb; omega⟩
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hnS_t, hph_t, ite_eq_right (by decide : 6 ≠ 0), hnD_t, ← hd0, hfr_tick]
        exact hfr_le_pad
      · rw [hph_t, ite_eq_right (by decide : ¬(6 < 2)), ite_eq_right (by decide : 6 ≠ 2),
          ite_eq_left (by decide : 6 ≤ 10), hibH_t, hqH_t, hfr_tick]
        refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, fun a => hwf_tick.2 a⟩
            base_fr := by dsimp only [hiFr]; clear *- hibLo_eq hibLo_le_ibHi; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_off off (by clear *- hoff; omega)
                (by dsimp only [hdrPhase]; clear *- hoff; omega)
                (by dsimp only [hdrSmallMeta1]; clear *- hoff; omega)
                (by dsimp only [hdrSmallMeta1]; clear *- hoff; omega)
                (by dsimp only [hdrCur]; clear *- hoff; omega)
                (by dsimp only [hdrSplit]; clear *- hoff; omega)
            live_eq := (hout_off hdrLive (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide)).trans hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]; decide
            stg_le := by dsimp only; rw [hst_t]; decide
            mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [Nat.add_assoc]
                exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrSmallMeta1]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrSmallMeta1]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
            nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := Or.inl hnD_t
                  nDst_zero := fun _ => by
                    dsimp only; rw [hnS_t, hst_t, hph_t]
                    exact ⟨hs_pos, rfl, by decide, by decide, by decide⟩
                  stg_one := fun h1 => by
                    dsimp only at h1; exact absurd (hst_t.symm.trans h1) (by decide)
                  post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t, ← hd0]; exact hsched.trig_cap
                  drift_hi := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                  drift_lo := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                  ibLo_eq := by
                    dsimp only; rw [hibL_t, hph_t, ite_eq_left (by decide : 6 < 10), hmS_t]
                    exact hibLo_eq
                  qLo_eq := by
                    dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 6 < 10), hnS_t]
                    exact hqLo_eq
                  ph1 := fun h1 => by
                    dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
                  ge2 := fun _ => by
                    dsimp only
                    rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    exact ⟨hd0 ▸ hmDst_eq, hpad_eq,
                      fun hz => absurd hz (Nat.lt_irrefl 0),
                      fun hz => absurd hz (Nat.lt_irrefl 0),
                      hd0 ▸ hibHi_eq, hd0 ▸ hqHi_eq⟩
                  ph2 := fun h2 => by
                    dsimp only at h2; exact absurd (hph_t.symm.trans h2) (by decide)
                  ph3_10 := fun _ => by
                    dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                  ph11 := fun h11 => by
                    dsimp only at h11; exact absurd (hph_t.symm.trans h11) (by decide)
                  budget := by
                    dsimp only [L']
                    rw [hnS_t, hst_t, hph_t, hcur_t, hnD_t]
                    unfold dualPgHost hostPageLayout dualNHost epochPageArenaLayout
                      remRebuildBudget futureRebuildBudget
                    dsimp only
                    rw [hnD_t, ite_eq_left rfl, hnS_t]
                    simp only [show (6 : ℕ) ≠ 1 by decide, show (6 : ℕ) ≠ 2 by decide,
                      show (6 : ℕ) ≠ 3 by decide, show (6 : ℕ) ≠ 4 by decide,
                      show (6 : ℕ) ≠ 5 by decide, show 4 ≤ 6 by decide, show 6 ≤ 9 by decide,
                      and_self, ↓reduceIte, Nat.sub_zero]
                    have hrb := hrem_b.2.1
                    rw [hst0, hp3] at hrb
                    unfold remRebuildBudget futureRebuildBudget at hrb
                    dsimp only at hrb
                    simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide,
                      ↓reduceIte] at hrb
                    have hpg32 : 32 ≤ pageSizeWhp nSrc := le_max_left 32 _
                    have hmp_le : nSrc / pageSizeWhp nSrc + 4 ≤
                        max (whpThreshold c) nSrc / 16 + 16 := by
                      have hd1 : nSrc / pageSizeWhp nSrc ≤ nSrc / 32 :=
                        Nat.div_le_div_left hpg32 (by decide)
                      have hd2 : nSrc ≤ max (whpThreshold c) nSrc := le_max_right _ _
                      generalize max (whpThreshold c) nSrc = nRef at hd2 ⊢
                      clear *- hd1 hd2; omega
                    have hdiv_mp := Nat.div_le_div_right (c := 1024) hmp_le
                    unfold maxStageBudget at hrb ⊢
                    dsimp only at hrb ⊢
                    have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                    dsimp only [nSrc] at hdiv_mp hf2 ⊢
                    generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
                      at hrb hdiv_mp hf2 ⊢
                    generalize (s.mem (base + hdrNSrc) / pageSizeWhp (s.mem (base + hdrNSrc)) + 4) /
                        1024 = qmp at hdiv_mp ⊢
                    generalize 8 * max 32 (Nat.log 2 (2 * nRef) + 4) / 128 = qt at hrb ⊢
                    generalize max 32 (Nat.log 2 (2 * nRef) + 4) / 8 = qu at hrb ⊢
                    clear *- hrb hdiv_mp hf2
                    omega }
            pad_fits := by
              dsimp only
              rw [hnS_t, hph_t, ite_eq_right (by decide : 6 ≠ 0), hnD_t, ← hd0]
              have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp3; omega)] at hp
            ph1_inv := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
            ph3_inv := fun h3 => by dsimp only at h3; exact absurd (hph_t.symm.trans h3) (by decide)
            ph4_inv := fun h4 => by dsimp only at h4; exact absurd (hph_t.symm.trans h4) (by decide)
            pDst_pre := fun h25 _ _ => by dsimp only at h25; rw [hph_t] at h25; clear *- h25; omega
            ph5_inv := fun h5 => by dsimp only at h5; exact absurd (hph_t.symm.trans h5) (by decide)
            ph6_inv := fun _ => by
              dsimp only; rw [hcur_t]
              exact ⟨Nat.zero_le _, fun _ hvp => absurd hvp (Nat.not_lt_zero _)⟩
            ph7_inv := fun h7 => by dsimp only at h7; exact absurd (hph_t.symm.trans h7) (by decide)
            ph8_inv := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
            ph9_inv := fun h9 => by dsimp only at h9; exact absurd (hph_t.symm.trans h9) (by decide)
            ph10_inv := fun h10 => by
              dsimp only at h10; exact absurd (hph_t.symm.trans h10) (by decide)
            sl_le7 := fun _ => by
              dsimp only
              have hcap_t : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
                unfold dualCapSrc; simp only [hst_t, hnS_t, hst0, ↓reduceIte]; rfl
              rw [hcap_t, hph_t]
              refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
                dsimp only [L']
                have hl := hlen_s (by clear *- hp3; omega) hs_p
                simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
                exact hl⟩
              unfold activeSrcIo
              rw [ite_eq_right (by decide : ¬(6 < 3)), ite_eq_right (by decide : 6 ≠ 3),
                ite_eq_left (by decide : 6 < 8), hibH_t, hqH_t]
              exact hsl_hi
            sl_67 := fun _ => by
              dsimp only
              rw [hnD_t, hsm1_0_t, hsm1_1_t]
              exact ⟨fun _ => ⟨rfl, rfl⟩, fun hp => absurd hp (Nat.lt_irrefl 0)⟩
            sl_8 := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
            sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; clear *- h9; omega }
    · -- `3 → 4` (`nDst ≠ 0`, Stage-A `zeroMeta`):
      have hd_pos : 0 < nDst := Nat.pos_of_ne_zero hd0
      have hth_d : whpThreshold c ≤ nDst ∧ nDst ≤ U := by
        rcases hsched.nDst_bounds with hz | hb
        · exact absurd hz hd0
        · exact hb
      have hnDst_w : nDst < 2 ^ w := lt_of_le_of_lt hth_d.2 hUw
      have hs_tick_eq : s_tick =
          { mem := Function.update (Function.update s4.mem (base + hdrCur) 0) (base + hdrPhase) 4,
            frontier := s.frontier } := by
        rw [hst_bg, hst_sl, hs3_eq_raw, ite_eq_left hsp0_raw, hs4_eq,
          ite_eq_right hd0, hfr_s4]
      have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
      have hout_t : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrCur →
          ¬(base + hdrPBase0 + 48 ≤ a ∧ a < base + hdrPBase0 + 61) →
          a ≠ base + hdrSplit → ¬(ibHi ≤ a ∧ a < hiFr) →
          s_tick.mem a = s.mem a := by
        intro a h1 h2 hp0 hsp hhi
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne h1, Function.update_of_ne h2, hframe_s4.mem_outside s3 a hp0]
        exact hout_s3 a hsp hhi
      have hout_off : ∀ off < 112, off ≠ hdrPhase → off ≠ hdrCur → off ≠ hdrSplit →
          s_tick.mem (base + off) = s.mem (base + off) :=
        fun off hoff h1 h2 hsp =>
          hout_t (base + off) (base_add_ne h1) (base_add_ne h2)
            (by dsimp only [hdrPBase0]; clear *- hoff; omega) (base_add_ne hsp)
            (by clear *- hoff hibLo_eq hibLo_le_ibHi; omega)
      have hph_t : s_tick.mem (base + hdrPhase) = 4 := by
        rw [hs_tick_eq]; exact Function.update_self ..
      have hcur_t : s_tick.mem (base + hdrCur) = 0 := by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
      have hst_t : s_tick.mem (base + hdrStage) = 0 :=
        (hout_off hdrStage (by decide) (by decide) (by decide) (by decide)).trans hst0
      have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
        hout_off hdrNSrc (by decide) (by decide) (by decide) (by decide)
      have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
        hout_off hdrNDst (by decide) (by decide) (by decide) (by decide)
      have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
        hout_off hdrMSrc (by decide) (by decide) (by decide) (by decide)
      have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
        hout_off hdrMDst (by decide) (by decide) (by decide) (by decide)
      have hpad_t : s_tick.mem (base + hdrPad) = pad :=
        hout_off hdrPad (by decide) (by decide) (by decide) (by decide)
      have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
        hout_off hdrItemLo (by decide) (by decide) (by decide) (by decide)
      have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
        hout_off hdrItemHi (by decide) (by decide) (by decide) (by decide)
      have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
        hout_off hdrQLo (by decide) (by decide) (by decide) (by decide)
      have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
        hout_off hdrQHi (by decide) (by decide) (by decide) (by decide)
      have hsl_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
          (dualMbSrc base s_tick.mem) io_dir 0 false L.slotSrc s_tick.mem := by
        have hpS_eq : dualPSrc base s.mem = base + hdrPBase0 := by
          unfold dualPSrc; rw [ite_eq_left hst0]
        have hpS_t : dualPSrc base s_tick.mem = base + hdrPBase0 := by
          unfold dualPSrc; rw [hst_t, ite_eq_left rfl]
        have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
          unfold dualMbSrc; rw [hst_t, hnS_t, hst0]; rfl
        rw [hpS_eq] at hsl_s
        rw [hpS_t, hmS_mb]
        have hsl_fr : EpochSlotInv c U V w s.frontier (base + hdrPBase0) (dualMbSrc base s.mem)
            io_dir 0 false L.slotSrc s_tick.mem :=
          hsl_s.set_slotIo hv_dir_fr rfl hq_dir_valid rfl
            (fun k hk => by
              apply hout_t
              · dsimp only [hdrPBase0, hdrPhase]; clear *- hk; omega
              · dsimp only [hdrPBase0, hdrCur]; clear *- hk; omega
              · clear *- hk; omega
              · dsimp only [hdrPBase0, hdrSplit]; clear *- hk; omega
              · dsimp only [hdrPBase0]; clear *- hk hibLo_eq hibLo_le_ibHi; omega)
            (by
              have hrw : ∀ j < 13, s_tick.mem (base + hdrPBase0 + (48 + j)) =
                  s4.mem (base + hdrPBase0 + (48 + j)) := fun j hj => by
                rw [hs_tick_eq]; dsimp only
                iterate 2 rw [Function.update_of_ne
                  (by dsimp only [hdrPBase0, hdrPhase, hdrCur]; clear *- hj; omega)]
              exact ⟨(hrw 0 (by decide)).trans hvals_s4.1,
                (hrw 1 (by decide)).trans hvals_s4.2.1,
                (hrw 2 (by decide)).trans hvals_s4.2.2.1,
                (hrw 3 (by decide)).trans hvals_s4.2.2.2.1,
                (hrw 4 (by decide)).trans hvals_s4.2.2.2.2.1,
                (hrw 5 (by decide)).trans hvals_s4.2.2.2.2.2.1,
                (hrw 6 (by decide)).trans hvals_s4.2.2.2.2.2.2.1,
                (hrw 7 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.1,
                (hrw 8 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.1,
                (hrw 9 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.1,
                (hrw 10 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.2.1,
                (hrw 11 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.2.2.1,
                (hrw 12 (by decide)).trans hvals_s4.2.2.2.2.2.2.2.2.2.2.2.2⟩)
            (fun a h1 h2 hown => by
              unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hown
              dsimp only [io_dir, directSlotIo, hdrPBase0] at h1 h2 hown
              simp only [↓reduceIte] at hown
              clear *- h1 h2 hown hibLo_eq hibLo_le_ibHi; omega)
            hdisj_m_dir
            (fun a ha => by
              have ha_r := slotOwnsNonPageMeta_src_range hcap_s (fun hne => absurd hst0 hne) ha
              rw [hs_tick_eq]; dsimp only
              rcases ha_r with ⟨h1, h2⟩ | h192
              · iterate 2 rw [Function.update_of_ne
                  (by dsimp only [hdrPhase, hdrCur]; clear *- h1 h2; omega)]
                rw [hframe_s4.mem_outside s3 a
                  (by dsimp only [hdrPBase0]; clear *- h1 h2; omega)]
                exact hm_s3 a ha
              · iterate 2 rw [Function.update_of_ne
                  (by dsimp only [hdrPhase, hdrCur]; clear *- h192; omega)]
                rw [hframe_s4.mem_outside s3 a
                  (by dsimp only [hdrPBase0]; clear *- h192; omega)]
                exact hm_s3 a ha)
            (by
              unfold SlotIoLayout.StateInv; dsimp only [io_dir, directSlotIo]
              simp only [↓reduceIte]; exact ⟨hcnt_le, Or.inl trivial⟩)
            (fun p hp => by
              have hp_lt : p < nLive := lt_of_lt_of_le hp hcnt_le
              rw [← hpair_dir_s3 p hp]
              have hhi_eq : ∀ a, ibHi ≤ a → a < hiFr → s_tick.mem a = s3.mem a := fun a h1 _ => by
                have ha192 : base + 192 ≤ a := by clear *- h1 hibLo_eq hibLo_le_ibHi; omega
                rw [hs_tick_eq]; dsimp only
                iterate 2 rw [Function.update_of_ne
                  (by dsimp only [hdrPhase, hdrCur]; clear *- ha192; omega)]
                exact hframe_s4.mem_outside s3 a (by dsimp only [hdrPBase0]; clear *- ha192; omega)
              unfold slotIoPairAt; dsimp only [io_dir, directSlotIo, arenaPairAt]
              simp only [↓reduceIte]
              have hlt_q := wOffQ_add_one_lt_pairStreamWords (q_bits := qHi) (v_bits := vB)
                hw_pos hp_lt
              have hlt_v := wOffV_add_one_lt_pairStreamWords (q_bits := qHi) (v_bits := vB)
                hw_pos hp_lt
              unfold pairQuotAt pairValAt readBitSlice; dsimp only
              rw [hhi_eq _ (Nat.le_add_right _ _) (by dsimp only [hiFr]; clear *- hlt_q; omega),
                hhi_eq _ (by omega) (by dsimp only [hiFr]; clear *- hlt_q; omega),
                hhi_eq _ (Nat.le_add_right _ _) (by dsimp only [hiFr]; clear *- hlt_v; omega),
                hhi_eq _ (by omega) (by dsimp only [hiFr]; clear *- hlt_v; omega)])
        refine hsl_fr.at_exact_frontier
          (by dsimp only [hiFr, hdrPBase0]; clear *- hibLo_eq hibLo_le_ibHi; omega)
          (by unfold dualMbSrc; rw [ite_eq_left hst0, hcap_s, hcap_eq]
              change (if nSrc = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) + 2
                else (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) +
                  epochMetaWordsWhp c w nSrc) ≤ hiFr
              rw [← hmSrc_eq]
              by_cases h0 : nSrc = 0
              · rw [ite_eq_left h0, ite_eq_left h0]; dsimp only [hdrSmallMeta0, hiFr]
                clear *- hibLo_eq hibLo_le_ibHi; omega
              · rw [ite_eq_right h0, ite_eq_right h0]; dsimp only [hiFr]
                clear *- hibLo_eq hibLo_le_ibHi; omega)
          (by dsimp only [io_dir, directSlotIo]; exact le_rfl)
      refine ⟨hpre_bg, hfr_tick, hwf_tick,
        fun addr hlt_b => hout_t addr
          (by dsimp only [hdrPhase]; clear *- hlt_b; omega)
          (by dsimp only [hdrCur]; clear *- hlt_b; omega)
          (by dsimp only [hdrPBase0]; clear *- hlt_b; omega)
          (by dsimp only [hdrSplit]; clear *- hlt_b; omega)
          (by clear *- hlt_b hibLo_eq hibLo_le_ibHi; omega), ?_⟩
      rw [ite_eq_left (by clear *- hp3; omega)]
      refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
          (fun ⟨h9, _⟩ => by rw [hp3] at h9; cases h9) rfl rfl, ?_,
        fun _ _ => by
          unfold itemBatchWhp at hmc_sl hmc_sb ⊢
          unfold epochStepCost
          dsimp only [sp] at hmc_sb
          clear *- hmc_bg hmc_sl hmc_sb; omega⟩
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hnS_t, hph_t, ite_eq_right (by decide : 4 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
      · rw [hph_t, ite_eq_right (by decide : ¬(4 < 2)), ite_eq_right (by decide : 4 ≠ 2),
          ite_eq_left (by decide : 4 ≤ 10), hibH_t, hqH_t, hfr_tick]
        refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, fun a => hwf_tick.2 a⟩
            base_fr := by dsimp only [hiFr]; clear *- hibLo_eq hibLo_le_ibHi; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_off off (by clear *- hoff; omega)
                (by dsimp only [hdrPhase]; clear *- hoff; omega)
                (by dsimp only [hdrCur]; clear *- hoff; omega)
                (by dsimp only [hdrSplit]; clear *- hoff; omega)
            live_eq := (hout_off hdrLive (by decide) (by decide) (by decide)
              (by decide)).trans hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]; decide
            stg_le := by dsimp only; rw [hst_t]; decide
            mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [Nat.add_assoc]
                exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
            nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                  nDst_zero := fun hz => absurd (hnD_t.symm.trans hz) hd0
                  stg_one := fun h1 => by
                    dsimp only at h1; exact absurd (hst_t.symm.trans h1) (by decide)
                  post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                  drift_lo := by
                    dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                  ibLo_eq := by
                    dsimp only; rw [hibL_t, hph_t, ite_eq_left (by decide : 4 < 10), hmS_t]
                    exact hibLo_eq
                  qLo_eq := by
                    dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 4 < 10), hnS_t]
                    exact hqLo_eq
                  ph1 := fun h1 => by
                    dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
                  ge2 := fun _ => by
                    dsimp only
                    rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    refine ⟨hmDst_eq, hpad_eq, ?_, fun hd_p => ?_, hibHi_eq, hqHi_eq⟩
                    · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                        rw [Nat.add_assoc]
                        exact hout_off (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrSplit]; clear *- hk; omega)
                    · obtain ⟨e1, e2, e3⟩ := hlog_d hd_p
                      exact ⟨(hout_off hdrLogN (by decide) (by decide) (by decide)
                          (by decide)).trans e1,
                        (hout_off hdrEll (by decide) (by decide) (by decide) (by decide)).trans e2,
                        (hout_off hdrPgB (by decide) (by decide) (by decide) (by decide)).trans e3⟩
                  ph2 := fun h2 => by
                    dsimp only at h2; exact absurd (hph_t.symm.trans h2) (by decide)
                  ph3_10 := fun _ => by
                    dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                  ph11 := fun h11 => by
                    dsimp only at h11; exact absurd (hph_t.symm.trans h11) (by decide)
                  budget := by
                    dsimp only [L']
                    rw [hnS_t, hst_t, hph_t, hmD_t, hcur_t]
                    unfold remRebuildBudget futureRebuildBudget
                    dsimp only
                    simp only [show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide,
                      show (4 : ℕ) ≠ 3 by decide, le_rfl, show 4 ≤ 9 by decide,
                      and_self, ↓reduceIte, Nat.sub_zero]
                    have hrb := hrem_b.2.1
                    rw [hst0, hp3] at hrb
                    unfold remRebuildBudget futureRebuildBudget at hrb
                    dsimp only at hrb
                    simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide,
                      ↓reduceIte] at hrb
                    have hd_hi' : nLive ≤ L.nTrig + (L.elapsed + 1) := by
                      have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                    have hd_lo' : L.nTrig ≤ nLive + (L.elapsed + 1) := by
                      have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                    have hel_le' : 16 * (L.elapsed + 1) ≤ max (whpThreshold c) nSrc := by
                      have hel := hrem_b.2.2; clear *- hel; omega
                    have hnD_2R := (active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap
                      hd_hi' hd_lo' hel_le' hlive_le).1
                    have hmD_le : mDst ≤ 2 * max (whpThreshold c) nSrc + 512 := by
                      have h1 : mDst ≤ nDst + 120 :=
                        hmDst_eq.trans_le (epochMetaWordsWhp_le_self hth_d.1 hnDst_w)
                      generalize max (whpThreshold c) nSrc = nRef at hnD_2R ⊢
                      clear *- h1 hnD_2R; omega
                    have hdiv_mD := Nat.div_le_div_right (c := 1024) hmD_le
                    unfold maxStageBudget at hrb ⊢
                    dsimp only at hrb ⊢
                    have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                    generalize max (whpThreshold c) nSrc = nRef at hrb hdiv_mD hf2 ⊢
                    clear *- hrb hdiv_mD hf2
                    omega }
            pad_fits := by
              dsimp only
              rw [hnS_t, hph_t, ite_eq_right (by decide : 4 ≠ 0), hnD_t]
              have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp3; omega)] at hp
            ph1_inv := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
            ph3_inv := fun h3 => by dsimp only at h3; exact absurd (hph_t.symm.trans h3) (by decide)
            ph4_inv := fun _ => by
              dsimp only; rw [hnD_t, hcur_t, hmD_t]
              exact ⟨hd_pos, Nat.zero_le _, fun _ hoff => absurd hoff (Nat.not_lt_zero _)⟩
            pDst_pre := fun _ _ _ => by
              dsimp only
              have hmbD : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
                unfold dualMbDst
                rw [hph_t, hp3, ite_eq_left (by decide : 4 < 10), ite_eq_left (by decide : 3 < 10),
                  hnD_t, hst_t, hpad_t, hst0]
              have hpD : dualPDst base s_tick.mem = base + hdrPBase1 := by
                unfold dualPDst
                rw [hph_t, ite_eq_left (by decide : 4 < 10), hst_t, ite_eq_left rfl]
              have hpD_s : dualPDst base s.mem = base + hdrPBase1 := by
                unfold dualPDst
                rw [hp3, ite_eq_left (by decide : 3 < 10), hst0, ite_eq_left rfl]
              have hpt_s := h.pDst_pre ⟨by clear *- hp3; omega, by clear *- hp3; omega⟩
                (Or.inr hst0) hd_pos
              dsimp only at hpt_s; rw [hpD_s] at hpt_s
              rw [hnD_t, hmbD, hpD, hibH_t, hqH_t]
              exact fastParamTable_mask_congr hpt_s fun k hk => by
                apply hout_t <;>
                  (dsimp only [hdrPBase1, hdrPBase0, hdrPhase, hdrCur, hdrSplit]
                   clear *- hk hibLo_eq hibLo_le_ibHi; omega)
            ph5_inv := fun h5 => by dsimp only at h5; exact absurd (hph_t.symm.trans h5) (by decide)
            ph6_inv := fun h6 => by dsimp only at h6; exact absurd (hph_t.symm.trans h6) (by decide)
            ph7_inv := fun h7 => by dsimp only at h7; exact absurd (hph_t.symm.trans h7) (by decide)
            ph8_inv := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
            ph9_inv := fun h9 => by dsimp only at h9; exact absurd (hph_t.symm.trans h9) (by decide)
            ph10_inv := fun h10 => by
              dsimp only at h10; exact absurd (hph_t.symm.trans h10) (by decide)
            sl_le7 := fun _ => by
              dsimp only
              have hcap_t : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
                unfold dualCapSrc; simp only [hst_t, hnS_t, hst0, ↓reduceIte]; rfl
              rw [hcap_t, hph_t]
              refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
                dsimp only [L']
                have hl := hlen_s (by clear *- hp3; omega) hs_p
                simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
                exact hl⟩
              unfold activeSrcIo
              rw [ite_eq_right (by decide : ¬(4 < 3)), ite_eq_right (by decide : 4 ≠ 3),
                ite_eq_left (by decide : 4 < 8), hibH_t, hqH_t]
              exact hsl_hi
            sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; clear *- h67; omega
            sl_8 := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
            sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; clear *- h9; omega }
  · -- Stays in `ph = 3` (`sp' ≠ 0`, so `1024 < sp` and `s_tick = s3`):
    have hsp_gt : itemBatchWhp < sp := by dsimp only [sp'] at hsp0; clear *- hsp0; omega
    have hsp0_raw : (Memory.spec 0).clientResult s
        (slideUpBatchProg ((cfg.toCtx, sp), itemBatchWhp)) ≠ 0 := hres_sb ▸ hsp0
    have hs_tick_eq : s_tick = s3 := by
      rw [hst_bg, hst_sl, hs3_eq_raw, ite_eq_right hsp0_raw]
    have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
    have hout_off : ∀ off < 192, off ≠ hdrSplit →
        s_tick.mem (base + off) = s.mem (base + off) :=
      fun off hoff hsp => by
        rw [hs_tick_eq]
        exact hout_s3 (base + off) (base_add_ne hsp)
          (by clear *- hoff hibLo_eq hibLo_le_ibHi; omega)
    have hph_t : s_tick.mem (base + hdrPhase) = 3 :=
      (hout_off hdrPhase (by decide) (by decide)).trans hp3
    have hsp_t : s_tick.mem (base + hdrSplit) = sp' := by
      rw [hs_tick_eq]; exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = 0 :=
      (hout_off hdrStage (by decide) (by decide)).trans hst0
    have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
      hout_off hdrNSrc (by decide) (by decide)
    have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
      hout_off hdrNDst (by decide) (by decide)
    have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
      hout_off hdrMSrc (by decide) (by decide)
    have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
      hout_off hdrMDst (by decide) (by decide)
    have hpad_t : s_tick.mem (base + hdrPad) = pad :=
      hout_off hdrPad (by decide) (by decide)
    have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
      hout_off hdrItemLo (by decide) (by decide)
    have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
      hout_off hdrItemHi (by decide) (by decide)
    have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
      hout_off hdrQLo (by decide) (by decide)
    have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
      hout_off hdrQHi (by decide) (by decide)
    have hsl_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
        (dualMbSrc base s_tick.mem) io_sp 0 false L.slotSrc s_tick.mem := by
      have hpS_eq : dualPSrc base s.mem = base + hdrPBase0 := by
        unfold dualPSrc; rw [ite_eq_left hst0]
      have hpS_t : dualPSrc base s_tick.mem = base + hdrPBase0 := by
        unfold dualPSrc; rw [hst_t, ite_eq_left rfl]
      have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
        unfold dualMbSrc; rw [hst_t, hnS_t, hst0]; rfl
      rw [hpS_eq] at hsl_s
      rw [hpS_t, hmS_mb, hs_tick_eq]
      have hv_sp_fr := hsl_s.io_valid
      have hsl_s3 : EpochSlotInv c U V w s.frontier (base + hdrPBase0) (dualMbSrc base s.mem)
          io_sp 0 false L.slotSrc s3.mem := by
        have hraw := hsl_s; unfold EpochSlotInv at hraw
        refine hsl_s.transfer_io hv_sp_fr rfl
          ⟨fun h0 => by
            rw [hcap_s, hcap_eq] at h0; dsimp only [io_sp, splitSlotIo]
            rw [hqLo_eq, ite_eq_left h0],
           fun h0 => by
            rw [hcap_s, hcap_eq] at h0 ⊢; dsimp only [io_sp, splitSlotIo]
            rw [hqLo_eq, ite_eq_right h0]⟩
          rfl
          ⟨fun h0 => by
            rw [ite_eq_left h0] at hraw
            have hpt := hraw.2.2.2.1
            have hrw : ∀ k < 64, s3.mem (base + hdrPBase0 + k) = s.mem (base + hdrPBase0 + k) :=
              fun k hk => hout_s3 _ (by dsimp only [hdrPBase0, hdrSplit]; clear *- hk; omega)
                (by dsimp only [hdrPBase0]; clear *- hk hibLo_eq hibLo_le_ibHi; omega)
            exact ⟨(hrw 0 (by decide)).trans hpt.1, (hrw 1 (by decide)).trans hpt.2.1,
              (hrw 48 (by decide)).trans hpt.2.2.1, (hrw 49 (by decide)).trans hpt.2.2.2.1,
              (hrw 50 (by decide)).trans hpt.2.2.2.2.1,
              (hrw 51 (by decide)).trans hpt.2.2.2.2.2.1,
              (hrw 52 (by decide)).trans hpt.2.2.2.2.2.2.1,
              (hrw 53 (by decide)).trans hpt.2.2.2.2.2.2.2.1,
              (hrw 54 (by decide)).trans hpt.2.2.2.2.2.2.2.2.1,
              (hrw 55 (by decide)).trans hpt.2.2.2.2.2.2.2.2.2.1,
              (hrw 56 (by decide)).trans hpt.2.2.2.2.2.2.2.2.2.2.1,
              (hrw 57 (by decide)).trans hpt.2.2.2.2.2.2.2.2.2.2.2.1,
              (hrw 58 (by decide)).trans hpt.2.2.2.2.2.2.2.2.2.2.2.2.1,
              (hrw 59 (by decide)).trans hpt.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
              (hrw 60 (by decide)).trans hpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
           fun h0 => by
            rw [ite_eq_right h0] at hraw
            intro k hk
            exact (hout_s3 (base + hdrPBase0 + k)
              (by dsimp only [hdrPBase0, hdrSplit]; clear *- hk; omega)
              (by dsimp only [hdrPBase0]; clear *- hk hibLo_eq hibLo_le_ibHi; omega)).trans
              (hraw.2.1.1 k hk)⟩
          (fun a h1 h2 hown => by
            unfold SlotIoLayout.OwnsAddr at hown
            dsimp only [io_sp, splitSlotIo, hdrSplit, hdrPBase0] at h1 h2 hown
            simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by decide] at hown
            clear *- h1 h2 hown hibLo_eq hibLo_le_ibHi; omega)
          hdisj_m_sp hm_s3
          (by
            unfold SlotIoLayout.StateInv; dsimp only [io_sp, splitSlotIo]
            simp only [↓reduceIte]; exact ⟨hcnt_le, Or.inr hqHi_w⟩)
          hs3_pair
      refine hsl_s3.at_exact_frontier
        (by dsimp only [hiFr, hdrPBase0]; clear *- hibLo_eq hibLo_le_ibHi; omega)
        (by unfold dualMbSrc; rw [ite_eq_left hst0, hcap_s, hcap_eq]
            change (if nSrc = 0 then (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) + 2
              else (if nSrc = 0 then base + hdrSmallMeta0 else base + 192) +
                epochMetaWordsWhp c w nSrc) ≤ hiFr
            rw [← hmSrc_eq]
            by_cases h0 : nSrc = 0
            · rw [ite_eq_left h0, ite_eq_left h0]; dsimp only [hdrSmallMeta0, hiFr]
              clear *- hibLo_eq hibLo_le_ibHi; omega
            · rw [ite_eq_right h0, ite_eq_right h0]; dsimp only [hiFr]
              clear *- hibLo_eq hibLo_le_ibHi; omega)
        (by dsimp only [io_sp, splitSlotIo]; exact le_rfl)
    refine ⟨hpre_bg, hfr_tick, hwf_tick,
      fun addr hlt_b => by
        rw [hs_tick_eq]
        exact hout_s3 addr (by dsimp only [hdrSplit]; clear *- hlt_b; omega)
          (by clear *- hlt_b hibLo_eq hibLo_le_ibHi; omega), ?_⟩
    rw [ite_eq_left (by clear *- hp3; omega)]
    refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
        (fun ⟨h9, _⟩ => by rw [hp3] at h9; cases h9) rfl rfl, ?_,
      fun _ _ => by
        unfold itemBatchWhp at hmc_sl hmc_sb ⊢
        unfold epochStepCost
        dsimp only [sp] at hmc_sb
        clear *- hmc_bg hmc_sl hmc_sb; omega⟩
    refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
    · rw [hnS_t, hph_t, ite_eq_right (by decide : 3 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
    · rw [hph_t, ite_eq_right (by decide : ¬(3 < 2)), ite_eq_right (by decide : 3 ≠ 2),
        ite_eq_left (by decide : 3 ≤ 10), hibH_t, hqH_t, hfr_tick]
      refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
      exact
        { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
          wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, fun a => hwf_tick.2 a⟩
          base_fr := by dsimp only [hiFr]; clear *- hibLo_eq hibLo_le_ibHi; omega
          hdr := rootStaticHeader_congr hhdr fun off hoff =>
            hout_off off (by clear *- hoff; omega) (by dsimp only [hdrSplit]; clear *- hoff; omega)
          live_eq := (hout_off hdrLive (by decide) (by decide)).trans hlive_eq
          live_le := hlive_le
          ph_le := by dsimp only; rw [hph_t]; decide
          stg_le := by dsimp only; rw [hst_t]; decide
          mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
          cache_src := by
            dsimp only; rw [hnS_t]
            exact hostCacheValid_congr_mem hcache_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
          nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
          sched := by
            dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
            refine
              { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                nDst_zero := fun hz => by
                  dsimp only at hz ⊢
                  obtain ⟨hs_p, _, _, _, _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                  rw [hnS_t, hst_t, hph_t]
                  exact ⟨hs_p, rfl, by decide, by decide, by decide⟩
                stg_one := fun h1 => by
                  dsimp only at h1; exact absurd (hst_t.symm.trans h1) (by decide)
                post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                drift_hi := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                drift_lo := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                ibLo_eq := by
                  dsimp only; rw [hibL_t, hph_t, ite_eq_left (by decide : 3 < 10), hmS_t]
                  exact hibLo_eq
                qLo_eq := by
                  dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 3 < 10), hnS_t]
                  exact hqLo_eq
                ph1 := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
                ge2 := fun _ => by
                  dsimp only
                  rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                  refine ⟨hmDst_eq, hpad_eq, ?_, fun hd_p => ?_, hibHi_eq, hqHi_eq⟩
                  · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                      rw [Nat.add_assoc]
                      exact hout_off (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrSplit]; clear *- hk; omega)
                  · obtain ⟨e1, e2, e3⟩ := hlog_d hd_p
                    exact ⟨(hout_off hdrLogN (by decide) (by decide)).trans e1,
                      (hout_off hdrEll (by decide) (by decide)).trans e2,
                      (hout_off hdrPgB (by decide) (by decide)).trans e3⟩
                ph2 := fun h2 => by dsimp only at h2; exact absurd (hph_t.symm.trans h2) (by decide)
                ph3_10 := fun _ => by
                  dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                ph11 := fun h11 => by
                  dsimp only at h11; exact absurd (hph_t.symm.trans h11) (by decide)
                budget := by
                  dsimp only [L']
                  rw [hnS_t, hst_t, hph_t, hsp_t]
                  unfold remRebuildBudget futureRebuildBudget
                  dsimp only
                  simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
                  have hrb := hrem_b.2.1
                  rw [hst0, hp3] at hrb
                  unfold remRebuildBudget futureRebuildBudget at hrb
                  dsimp only at hrb
                  simp only [show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
                    at hrb
                  have hdiv_sp : sp / 1024 = sp' / 1024 + 1 := by
                    have heq_sp : sp = sp' + 1024 := by
                      dsimp only [sp', itemBatchWhp] at hsp_gt ⊢; clear *- hsp_gt; omega
                    rw [heq_sp]; exact Nat.add_div_right _ (by decide : 0 < 1024)
                  rw [hdiv_sp] at hrb
                  have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                  generalize max (whpThreshold c) nSrc = nRef at hrb hf2 ⊢
                  clear *- hrb hf2
                  omega }
          pad_fits := by
            dsimp only
            rw [hnS_t, hph_t, ite_eq_right (by decide : 3 ≠ 0), hnD_t]
            have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp3; omega)] at hp
          ph1_inv := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
          ph3_inv := fun _ => by
            dsimp only; rw [hsp_t, hibL_t, hqL_t, hibH_t, hqH_t, hs_tick_eq]
            exact ⟨Nat.sub_le_of_le_add (by clear *- hsp_le; omega), hs3_hiQuot⟩
          ph4_inv := fun h4 => by dsimp only at h4; exact absurd (hph_t.symm.trans h4) (by decide)
          pDst_pre := fun _ _ hd_p => by
            dsimp only at hd_p ⊢
            rw [hnD_t] at hd_p
            have hmbD : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
              unfold dualMbDst
              simp only [hph_t, hp3, hnD_t, hst_t, hpad_t, hst0, ↓reduceIte]; rfl
            have hpD : dualPDst base s_tick.mem = base + hdrPBase1 := by
              unfold dualPDst
              rw [hph_t, ite_eq_left (by decide : 3 < 10), hst_t, ite_eq_left rfl]
            have hpD_s : dualPDst base s.mem = base + hdrPBase1 := by
              unfold dualPDst
              rw [hp3, ite_eq_left (by decide : 3 < 10), hst0, ite_eq_left rfl]
            have hpt_s := h.pDst_pre ⟨by clear *- hp3; omega, by clear *- hp3; omega⟩
              (Or.inr hst0) hd_p
            dsimp only at hpt_s; rw [hpD_s] at hpt_s
            rw [hnD_t, hmbD, hpD, hibH_t, hqH_t]
            exact fastParamTable_mask_congr hpt_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_off (hdrPBase1 + k) (by dsimp only [hdrPBase1]; clear *- hk; omega)
                (by dsimp only [hdrPBase1, hdrSplit]; clear *- hk; omega)
          ph5_inv := fun h5 => by dsimp only at h5; exact absurd (hph_t.symm.trans h5) (by decide)
          ph6_inv := fun h6 => by dsimp only at h6; exact absurd (hph_t.symm.trans h6) (by decide)
          ph7_inv := fun h7 => by dsimp only at h7; exact absurd (hph_t.symm.trans h7) (by decide)
          ph8_inv := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
          ph9_inv := fun h9 => by dsimp only at h9; exact absurd (hph_t.symm.trans h9) (by decide)
          ph10_inv := fun h10 => by
            dsimp only at h10; exact absurd (hph_t.symm.trans h10) (by decide)
          sl_le7 := fun _ => by
            dsimp only
            have hcap_t : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
              unfold dualCapSrc; simp only [hst_t, hnS_t, hst0, ↓reduceIte]; rfl
            rw [hcap_t, hph_t]
            refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
              dsimp only [L']
              have hl := hlen_s (by clear *- hp3; omega) hs_p
              simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
              exact hl⟩
            unfold activeSrcIo
            rw [ite_eq_right (by decide : ¬(3 < 3)), ite_eq_left rfl,
              hibL_t, hqL_t, hibH_t, hqH_t]
            exact hsl_hi
          sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; clear *- h67; omega
          sl_8 := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
          sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; clear *- h9; omega }


end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

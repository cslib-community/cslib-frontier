/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvTickC1

/-!
# Background Tick Phases `10..11` and Unified `bgTickProg_spec` (`DualEpochInvTickC`)

Completes the 12-phase (`0..11`) background tick invariant proofs (`tickPhase10_spec`,
`tickPhase11_spec`) and assembles the unified `bgTickProg_spec` dispatcher for
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `tickPhase10_spec`: Phase `10` (`tickSlideDownProg`, `10 → 10` and `10 → 11`).
* `tickPhase11_spec`: Phase `11` (`shrinkPost` pass-through to `DualPreShrinkInv`).
* `bgTickProg_spec`: unified `0..11` background tick specification.

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
open EpochUpdate

attribute [local irreducible] epochMetaWordsWhp

/-! ## Section 3: Phase `10` (`tickSlideDownProg`) and Phase `11` (`shrinkPost`) -/

/-- Phase `10` (`slideDown`) background tick specification (`10 → 10` and `10 → 11`). -/
theorem tickPhase10_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp10 : s.mem (base + hdrPhase) = 10) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hw_pos : 0 < w := by clear *- hw11; omega
  have hU0 := h.U_pos; have hUw := h.U_lt; have hV0 := h.V_pos; have hVw := h.V_le
  have hwf := h.wf; have hb192 := h.base_fr; have hhdr := h.hdr
  have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq
  have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  have hvb_eq := hhdr.2.2.2.2.1; have hw_eq := hhdr.2.2.1
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp10; omega)] at hsched
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp10; omega)
  obtain ⟨hfr_hi_lo, hfr_hi_mid⟩ :=
    hsched.ph3_10 ⟨by clear *- hp10; omega, by clear *- hp10; omega⟩
  simp only [↓reduceIte] at hfr_hi_mid
  obtain ⟨_, hvb_w, hqLo_w, hqHi_w, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  obtain ⟨hsp_le, hhi_quot⟩ := h.ph10_inv hp10
  obtain ⟨hcap_d, hdict_d, hsl_d, hevs_d⟩ := h.sl_ge9 (by clear *- hp10; omega)
  have hbud_old := hsched.budget; dsimp only at hbud_old
  obtain ⟨_, hb_tot, hb_el2⟩ := hbud_old
  set stg := s.mem (base + hdrStage)
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
  set nLive := (Dictionary.dom s_dict).card
  set loFr := ibLo + pairStreamWords nLive qLo vB w
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  have hibLo_eq : ibLo = base + 192 + mDst := by
    have hib := hsched.ibLo_eq; rwa [hp10, ite_eq_right (by decide : ¬(10 < 10))] at hib
  have hqLo_eq : qLo = (if nDst = 0 then keyBits U else quotBitsWhp U nDst) := by
    have hq := hsched.qLo_eq; rwa [hp10, ite_eq_right (by decide : ¬(10 < 10))] at hq
  have hqLo_le_qHi : qLo ≤ qHi := by
    rw [hqHi_eq, ← hqLo_eq]; exact le_max_right _ _
  have hibLo_le_ibHi : ibLo + 4 ≤ ibHi := by
    rw [hibHi_eq, hibLo_eq]
    by_cases hdz : nDst = 0
    · rw [ite_eq_left hdz]
      have hm0 : mDst = 0 := by
        rw [hmDst_eq, hdz]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
      rw [hm0]; omega
    · rw [ite_eq_right hdz]; omega
  have hloFr_lt_hiFr : loFr < hiFr := by
    have hpw_le := pairStreamWords_mono_q (n := nLive) (vb := vB) (w := w) hqLo_le_qHi
    dsimp only [loFr, hiFr]; clear *- hibLo_le_ibHi hpw_le; omega
  have hloFr_le_fr : loFr ≤ s.frontier := hloFr_lt_hiFr.le.trans hfr_hi_lo
  have hnLive_w : nLive < 2 ^ w := lt_of_le_of_lt hlive_le hUw
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show qHi + vB ≤ 2 * w by clear *- hqHi_w hvb_w; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    dsimp only [hiFr, ibHi, qHi, vB, nLive] at hfr_hi_mid hpw2 ⊢
    unfold bulkBatchWhp; clear *- hfr_hi_mid hpw2; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
    rw [ite_eq_right (by clear *- hp10; omega)] at hpad_hi_s
    exact hfr_hi_mid.trans hpad_hi_s
  set io_sp := splitSlotIo w vB base ibLo qLo ibHi qHi nLive
  have hpD_s : dualPDst base s.mem = base + hdrPBase0 := by
    unfold dualPDst; rw [hp10, ite_eq_right (by decide : ¬(10 < 10))]
  have hmbD_s : dualMbDst base s.mem =
      (if nDst = 0 then base + hdrSmallMeta0 else base + 192) := by
    unfold dualMbDst; rw [hp10, ite_eq_right (by decide : ¬(10 < 10))]
  have hio_d10 : activeDstIo c w vB base stg (s.mem (base + hdrPhase)) nSrc nDst pad
      ibLo qLo ibHi qHi nLive (s.mem (base + hdrUnpermDone)) = io_sp := by
    rw [hp10]; unfold activeDstIo
    simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
  have hsl_d0 : EpochSlotInv c U V w s.frontier (base + hdrPBase0) (dualMbDst base s.mem)
      io_sp 0 false L.slotDst s.mem := by
    rw [hpD_s, hio_d10] at hsl_d
    simpa only [hp10, Nat.reduceEqDiff, false_and, and_false, ↓reduceIte] using hsl_d
  have hns_d : s.mem (dualMbDst base s.mem + 1) = nLive := by
    rw [hsl_d0.mem_nSide_eq, ← dom_toDictState_card, hdict_d]
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
  have hfit_sd : ∀ d, sp ≤ d → d < min nLive (sp + itemBatchWhp) →
      (splitPairRead cfg sp s.mem d).1 < 2 ^ cfg.qBitsLo ∧
      (splitPairRead cfg sp s.mem d).2 < 2 ^ cfg.vBitsLo := fun d hd_lo hd_hi => by
    have hd_lt : d < nLive := lt_of_lt_of_le hd_hi (min_le_left _ _)
    have hq_b : pairQuotAt ibHi qHi vB w s.mem d < 2 ^ qLo := hhi_quot d hd_lo hd_lt
    have hv_b : (slotIoPairAt io_sp s.mem d).2 < V :=
      (hsl_d0.slot_pair_bounds (hns_d.symm ▸ hd_lt)).2
    have hv_pow : V ≤ 2 ^ vB := Nat.le_pow_clog (by decide : 1 < 2) V
    unfold slotIoPairAt at hv_b
    dsimp only [io_sp, splitSlotIo, SlotIoLayout.splitCfg] at hv_b
    simp only [↓reduceIte, one_ne_zero] at hv_b
    change (splitPairRead cfg sp s.mem d).2 < V at hv_b
    unfold splitPairRead at hv_b ⊢
    rw [ite_eq_right (Nat.not_lt.mpr hd_lo)] at hv_b ⊢
    exact ⟨hq_b, lt_of_lt_of_le hv_b hv_pow⟩
  obtain ⟨hsafe_sb, hres_sb, hfr_sb, hmc_sb, hread_sb, hout_sb⟩ :=
    slideDownBatchProg_spec (cfg := cfg) (n_tot := nLive) (s_split := sp) (s := s)
      hcfg_v hsp_le itemBatchWhp hfit_sd
  set sp' := min nLive (sp + itemBatchWhp)
  have hsp'_w : Fits w sp' := lt_of_le_of_lt (min_le_left _ _) hnLive_w
  have hpre_sd : TickSlideDownPre w base s := by
    refine ⟨hw11, hb192, ?_⟩
    dsimp only; rw [hctx_eq, hlive_eq]
    exact ⟨⟨hsp_le, by simpa only [SplitPairCfg.ofCtx_toCtx] using hcfg_v⟩,
      hsafe_sb, hres_sb.symm ▸ hsp'_w⟩
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, ?_⟩
    dsimp only; simp only [hp10, Nat.reduceEqDiff, ↓reduceIte]
    exact hpre_sd
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  simp only [hp10, Nat.reduceEqDiff, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_sd, hmc_sd⟩ := tickSlideDownProg_eval base s
  dsimp only at hst_sd hmc_sd
  rw [hctx_eq, hlive_eq] at hst_sd hmc_sd
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hwf_tick : Memory.WellFormed w s_tick :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  obtain ⟨s2, hs2_def⟩ : ∃ s2, (Memory.spec 0).clientState s
      (slideDownBatchProg (((cfg.toCtx, nLive), sp), itemBatchWhp)) = s2 := ⟨_, rfl⟩
  rw [hs2_def] at hfr_sb hread_sb hout_sb hst_sd
  clear hs2_def
  set s3 : Memory.State :=
    { mem := Function.update s2.mem (base + hdrSplit) sp', frontier := s.frontier }
  have hs3_eq_raw :
      ({ mem := Function.update s2.mem (base + hdrSplit)
          ((Memory.spec 0).clientResult s
            (slideDownBatchProg (((cfg.toCtx, nLive), sp), itemBatchWhp))),
         frontier := s2.frontier } : Memory.State) = s3 := by
    rw [hres_sb, hfr_sb]
  have hout_s3 : ∀ a, a ≠ base + hdrSplit → ¬(ibLo ≤ a ∧ a < loFr) → s3.mem a = s.mem a :=
    fun a hsp ha => by
      dsimp only [s3]; rw [Function.update_of_ne hsp]; exact hout_sb a ha
  have hs3_read : ∀ idx, splitPairRead cfg sp' s3.mem idx = splitPairRead cfg sp s.mem idx := by
    intro idx
    have heq_s2 : splitPairRead cfg sp' s3.mem idx = splitPairRead cfg sp' s2.mem idx := by
      unfold splitPairRead
      by_cases hlt_i : idx < sp'
      · rw [ite_eq_left hlt_i, ite_eq_left hlt_i]
        unfold pairQuotAt pairValAt readBitSlice; dsimp only [cfg, s3]
        iterate 4 rw [Function.update_of_ne (by dsimp only [hdrSplit]; clear *- hibLo_eq; omega)]
      · rw [ite_eq_right hlt_i, ite_eq_right hlt_i]
        unfold pairQuotAt pairValAt readBitSlice; dsimp only [cfg, s3]
        iterate 4 rw [Function.update_of_ne
          (by dsimp only [hdrSplit]; clear *- hibLo_eq hibLo_le_ibHi; omega)]
    exact heq_s2.trans (hread_sb idx)
  have hs3_hiQuot : SplitHiQuotBounded io_sp nLive s3.mem := by
    intro idx hlo hhi
    dsimp only [io_sp, splitSlotIo] at hlo ⊢
    have hsp3 : s3.mem (base + hdrSplit) = sp' := Function.update_self ..
    rw [hsp3] at hlo
    have hrd := congrArg Prod.fst (hs3_read idx)
    unfold splitPairRead at hrd
    have hsp_le_idx : sp ≤ idx := le_trans (by
      dsimp only [sp']; exact le_min hsp_le (Nat.le_add_right _ _)) hlo
    rw [ite_eq_right (Nat.not_lt.mpr hlo), ite_eq_right (Nat.not_lt.mpr hsp_le_idx)] at hrd
    dsimp only [cfg] at hrd
    rw [hrd]; exact hhi_quot idx hsp_le_idx hhi
  have hs3_pair : ∀ p < nLive,
      slotIoPairAt io_sp s3.mem p = slotIoPairAt io_sp s.mem p := fun p _ => by
    unfold slotIoPairAt; dsimp only [io_sp, splitSlotIo, SlotIoLayout.splitCfg]
    simp only [↓reduceIte, one_ne_zero]
    have hsp3 : s3.mem (base + hdrSplit) = sp' := Function.update_self ..
    rw [hsp3]
    change (let qv := splitPairRead cfg sp' s3.mem p; (qv.1 % 2 ^ qLo, qv.2)) =
      (let qv := splitPairRead cfg sp s.mem p; (qv.1 % 2 ^ qLo, qv.2))
    rw [hs3_read p]
  have hm_s3_d : ∀ a, slotOwnsNonPageMeta c w (dualMbDst base s.mem) L.slotDst.nCap a →
      s3.mem a = s.mem a := fun a ha => by
    rw [hcap_d, hmbD_s] at ha
    unfold slotOwnsNonPageMeta at ha
    by_cases hdz : nDst = 0
    · simp only [hdz, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at ha
      exact hout_s3 a (by dsimp only [hdrSmallMeta0, hdrSplit] at ha ⊢; clear *- ha; omega)
        (by dsimp only [hdrSmallMeta0, loFr] at ha hibLo_eq ⊢; clear *- ha hibLo_eq; omega)
    · have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hdz).1
      have hod_le : offPageDir c w nDst ≤ mDst :=
        (epochMeta_offsets_le (w := w) hth_d).2.2.2.trans hmDst_eq.symm.le
      have h32 : 32 ≤ offPageDir c w nDst :=
        (epochMeta_offsets_le (w := w) hth_d).1.trans
          ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
            (epochMeta_offsets_le (w := w) hth_d).2.2.1)
      simp only [hdz, ↓reduceIte] at ha
      rcases ha with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
        exact hout_s3 a (by dsimp only [hdrSplit]; clear *- g1; omega)
          (by dsimp only [loFr]; clear *- g1 g2 hod_le h32 hibLo_eq; omega)
  have hmc_all : memoryCost (bgTickProg (base, s.frontier)) s ≤
      itemBatchWhp * (2 * epochStepCost c + 20) + 20000 := by
    dsimp only [sp, nLive] at hmc_sb hmc_sd
    unfold itemBatchWhp at hmc_sb hmc_sd ⊢
    clear *- hmc_bg hmc_sd hmc_sb; omega
  have hd_hi' : nLive ≤ L.nTrig + (L.elapsed + 1) := by
    have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
  have hd_lo' : L.nTrig ≤ nLive + (L.elapsed + 1) := by
    have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
  have hel_le' : 16 * (L.elapsed + 1) ≤ max (whpThreshold c) nSrc := by
    clear *- hb_el2; omega
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
  by_cases hdone : nLive ≤ sp'
  · -- Branch `10 → 11` (`nLive ≤ sp'`, `sp' = nLive`, switches `pBase0` to `directSlotIo` at `lo`)
    have hsp'_eq : sp' = nLive := le_antisymm (min_le_left _ _) hdone
    have hdone_raw : nLive ≤ (Memory.spec 0).clientResult s
        (slideDownBatchProg (((cfg.toCtx, nLive), sp), itemBatchWhp)) := hres_sb.symm ▸ hdone
    rw [hs3_eq_raw, ite_eq_left hdone_raw] at hst_sd
    set io_lo := directSlotIo w vB base ibLo qLo nLive
    have hs4_eq : (Memory.spec 0).clientState s3
        (setDirectSlotIoProg ((base, base + hdrPBase0), ((ibLo, qLo), nLive))) =
        (Memory.spec 0).clientState s3 (setSlotIoProg (base + hdrPBase0, io_lo.toCtx)) := by
      have hev := (setDirectSlotIoProg_eval base (base + hdrPBase0) ibLo qLo nLive s3).1
      have hw_s3 : s3.mem (base + hdrW) = w :=
        (hout_s3 (base + hdrW) (base_add_ne (by decide))
          (by dsimp only [hdrW, loFr]; clear *- hibLo_eq; omega)).trans hw_eq
      have hvb_s3 : s3.mem (base + hdrValBits) = vB :=
        (hout_s3 (base + hdrValBits) (base_add_ne (by decide))
          (by dsimp only [hdrValBits, loFr]; clear *- hibLo_eq; omega)).trans hvb_eq
      rw [hev, hw_s3, hvb_s3]
    set s4 := (Memory.spec 0).clientState s3 (setSlotIoProg (base + hdrPBase0, io_lo.toCtx))
    rw [hs4_eq] at hst_sd
    have hfr_s4 : s4.frontier = s.frontier := runClient_frontier_setSlotIoProg _ s3
    have hfrm_s4 := setSlotIoProg_frame (base + hdrPBase0) io_lo.toCtx
    have hvals_s4 := setSlotIoProg_mem_vals (base + hdrPBase0) io_lo s3
    have hs_tick_eq : s_tick =
        { mem := Function.update s4.mem (base + hdrPhase) 11, frontier := s.frontier } := by
      rw [hst_bg, hst_sd, hfr_s4]
    have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
    have hout_t : ∀ a, a ≠ base + hdrPhase →
        ¬(base + hdrPBase0 + 48 ≤ a ∧ a < base + hdrPBase0 + 61) →
        a ≠ base + hdrSplit → ¬(ibLo ≤ a ∧ a < loFr) → s_tick.mem a = s.mem a :=
      fun a hph hp0 hsp hlo => by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne hph, hfrm_s4.mem_outside s3 a hp0]
        exact hout_s3 a hsp hlo
    have hout_hdr : ∀ off < 48, off ≠ hdrPhase → off ≠ hdrSplit →
        s_tick.mem (base + off) = s.mem (base + off) :=
      fun off hoff hph hsp =>
        hout_t (base + off) (base_add_ne hph)
          (by dsimp only [hdrPBase0]; clear *- hoff; omega) (base_add_ne hsp)
          (by clear *- hoff hibLo_eq; omega)
    have hph_t : s_tick.mem (base + hdrPhase) = 11 := by
      rw [hs_tick_eq]; exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = stg :=
      hout_hdr hdrStage (by decide) (by decide) (by decide)
    have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
      hout_hdr hdrNSrc (by decide) (by decide) (by decide)
    have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
      hout_hdr hdrNDst (by decide) (by decide) (by decide)
    have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
      hout_hdr hdrMSrc (by decide) (by decide) (by decide)
    have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
      hout_hdr hdrMDst (by decide) (by decide) (by decide)
    have hpad_t : s_tick.mem (base + hdrPad) = pad :=
      hout_hdr hdrPad (by decide) (by decide) (by decide)
    have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
      hout_hdr hdrItemLo (by decide) (by decide) (by decide)
    have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
      hout_hdr hdrItemHi (by decide) (by decide) (by decide)
    have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
      hout_hdr hdrQLo (by decide) (by decide) (by decide)
    have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
      hout_hdr hdrQHi (by decide) (by decide) (by decide)
    have hv_lo_fr : io_lo.Valid w s.frontier := by
      unfold SlotIoLayout.Valid; dsimp only [io_lo, directSlotIo]
      simp only [↓reduceIte]
      exact ⟨hw_pos, trivial, hqLo_w, hvb_w, hnLive_w, hloFr_le_fr⟩
    have hq_lo_d :
        (L.slotDst.nCap = 0 → io_lo.pgL.qBits = keyBits U) ∧
        (L.slotDst.nCap ≠ 0 → quotBitsWhp U L.slotDst.nCap ≤ io_lo.pgL.qBits) := by
      rw [hcap_d]; dsimp only [io_lo, directSlotIo]
      exact ⟨fun h0 => by rw [hqLo_eq, ite_eq_left h0],
        fun h0 => by rw [hqLo_eq, ite_eq_right h0]⟩
    have hsl_lo_fr : EpochSlotInv c U V w s.frontier (base + hdrPBase0)
        (dualMbDst base s.mem) io_lo 0 false L.slotDst s_tick.mem := by
      refine hsl_d0.set_slotIo (io₂ := io_lo) hv_lo_fr rfl hq_lo_d
        rfl
        (fun k hk => by
          have hk_out :
              ¬(base + hdrPBase0 + 48 ≤ base + hdrPBase0 + k ∧
                base + hdrPBase0 + k < base + hdrPBase0 + 61) := by
            rcases hk with hlt | rfl | rfl <;> omega
          refine hout_t (base + hdrPBase0 + k)
            (by dsimp only [hdrPBase0, hdrPhase]; omega) hk_out
            (by dsimp only [hdrPBase0, hdrSplit]; omega) ?_
          have hk64 : k < 64 := by rcases hk with hlt | rfl | rfl <;> omega
          dsimp only [hdrPBase0]; clear *- hk64 hibLo_eq; omega)
        (by
          have hrw : ∀ j < 13, s_tick.mem (base + hdrPBase0 + (48 + j)) =
              s4.mem (base + hdrPBase0 + (48 + j)) := fun j _ => by
            rw [hs_tick_eq]; dsimp only
            exact Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; omega) _ _
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
        (fun a h1 h2 hia => by
          unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hia
          dsimp only [io_lo, directSlotIo, hdrPBase0] at h1 h2 hia
          simp only [↓reduceIte] at hia
          clear *- h1 h2 hia hibLo_eq; omega)
        (fun a ha hia => by
          rw [hcap_d, hmbD_s] at ha
          unfold slotOwnsNonPageMeta at ha
          unfold SlotIoLayout.OwnsAddr PageArenaLayout.OwnsItemAddr at hia
          dsimp only [io_lo, directSlotIo] at hia; simp only [↓reduceIte] at hia
          by_cases hdz : nDst = 0
          · simp only [hdz, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at ha
            dsimp only [hdrSmallMeta0] at ha; clear *- ha hia hibLo_eq; omega
          · have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hdz).1
            have hod_le : offPageDir c w nDst ≤ mDst :=
              (epochMeta_offsets_le (w := w) hth_d).2.2.2.trans hmDst_eq.symm.le
            have h32 : 32 ≤ offPageDir c w nDst :=
              (epochMeta_offsets_le (w := w) hth_d).1.trans
                ((epochMeta_offsets_le (w := w) hth_d).2.1.trans
                  (epochMeta_offsets_le (w := w) hth_d).2.2.1)
            simp only [hdz, ↓reduceIte] at ha
            rcases ha with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
              (clear *- g1 g2 hia hod_le h32 hibLo_eq; omega))
        (fun a ha => by
          have ha_r : (base + 48 ≤ a ∧ a < base + 50) ∨ base + 192 ≤ a := by
            rw [hcap_d, hmbD_s] at ha; unfold slotOwnsNonPageMeta at ha
            by_cases hdz : nDst = 0
            · simp only [hdz, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at ha
              dsimp only [hdrSmallMeta0] at ha; exact Or.inl ha
            · simp only [hdz, ↓reduceIte] at ha
              rcases ha with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;> exact Or.inr (by clear *- g1; omega)
          rw [hs_tick_eq]; dsimp only
          rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- ha_r; omega),
            hfrm_s4.mem_outside s3 a (by dsimp only [hdrPBase0]; clear *- ha_r; omega)]
          exact hm_s3_d a ha)
        (by
          unfold SlotIoLayout.StateInv; dsimp only [io_lo, directSlotIo]
          simp only [↓reduceIte]; rw [hns_d]; exact ⟨le_rfl, Or.inl trivial⟩)
        (fun p hp => by
          rw [hns_d] at hp
          have hlo_eq : ∀ a, ibLo ≤ a → a < loFr → s_tick.mem a = s3.mem a := fun a h1 _ => by
            have ha192 : base + 192 ≤ a := by clear *- h1 hibLo_eq; omega
            rw [hs_tick_eq]; dsimp only
            rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- ha192; omega)]
            exact hfrm_s4.mem_outside s3 a (by dsimp only [hdrPBase0]; clear *- ha192; omega)
          have hlt_q := wOffQ_add_one_lt_pairStreamWords (q_bits := qLo) (v_bits := vB) hw_pos hp
          have hlt_v := wOffV_add_one_lt_pairStreamWords (q_bits := qLo) (v_bits := vB) hw_pos hp
          have hs_t_s3 : slotIoPairAt io_lo s_tick.mem p =
              splitPairRead cfg sp' s3.mem p := by
            unfold slotIoPairAt splitPairRead; dsimp only [io_lo, directSlotIo, arenaPairAt, cfg]
            simp only [↓reduceIte]
            rw [ite_eq_left (hsp'_eq.symm ▸ hp)]
            unfold pairQuotAt pairValAt readBitSlice; dsimp only
            rw [hlo_eq _ (Nat.le_add_right _ _) (by dsimp only [loFr]; clear *- hlt_q; omega),
              hlo_eq _ (by omega) (by dsimp only [loFr]; clear *- hlt_q; omega),
              hlo_eq _ (Nat.le_add_right _ _) (by dsimp only [loFr]; clear *- hlt_v; omega),
              hlo_eq _ (by omega) (by dsimp only [loFr]; clear *- hlt_v; omega)]
          have hs3_sp_p : splitPairRead cfg sp s.mem p = slotIoPairAt io_sp s.mem p := by
            unfold slotIoPairAt; dsimp only [io_sp, splitSlotIo, SlotIoLayout.splitCfg]
            simp only [↓reduceIte, one_ne_zero]
            change splitPairRead cfg sp s.mem p =
              (let qv := splitPairRead cfg sp s.mem p; (qv.1 % 2 ^ qLo, qv.2))
            unfold splitPairRead
            by_cases hlt_p : p < sp
            · rw [ite_eq_left hlt_p]; dsimp only [cfg]
              have hq_lt2 : pairQuotAt ibLo qLo vB w s.mem p < 2 ^ qLo :=
                pairQuotAt_lt ibLo qLo vB w s.mem p
              rw [Nat.mod_eq_of_lt hq_lt2]
            · rw [ite_eq_right hlt_p]; dsimp only [cfg]
              have hhq := hhi_quot p (Nat.le_of_not_lt hlt_p) hp
              dsimp only [io_sp, splitSlotIo] at hhq
              rw [Nat.mod_eq_of_lt hhq]
          exact hs_t_s3.trans ((hs3_read p).trans hs3_sp_p))
    -- Bound `s.frontier - loFr ≤ 9 * nRef` for Phase `11` budget:
    obtain ⟨hnD_2R, hnL_2R⟩ := active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap
      hd_hi' hd_lo' hel_le' hlive_le
    have hdiff_9R : s.frontier - loFr ≤ 9 * max (whpThreshold c) nSrc := by
      have hth_big := whpThreshold_ge_pow20 c
      have hmS_le : mSrc ≤ max (whpThreshold c) nSrc + 120 := by
        by_cases hs0 : nSrc = 0
        · have hm0 : mSrc = 0 := by
            rw [hmSrc_eq, hs0]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
          rw [hm0]; omega
        · obtain ⟨hth_s, hsU⟩ := hnSrc_b.resolve_left hs0
          have h1 := hmSrc_eq.trans_le (epochMetaWordsWhp_le_self hth_s (lt_of_le_of_lt hsU hUw))
          have h2 : nSrc ≤ max (whpThreshold c) nSrc := le_max_right _ _
          clear *- h1 h2; omega
      have hmD_le : mDst ≤ 2 * max (whpThreshold c) nSrc + 120 := by
        by_cases hd0 : nDst = 0
        · have hm0 : mDst = 0 := by
            rw [hmDst_eq, hd0]; unfold epochMetaWordsWhp; rw [ite_eq_left (whpThreshold_pos c)]
          rw [hm0]; omega
        · obtain ⟨hth_d, hdU⟩ := hsched.nDst_bounds.resolve_left hd0
          have h1 := hmDst_eq.trans_le (epochMetaWordsWhp_le_self hth_d (lt_of_le_of_lt hdU hUw))
          generalize max (whpThreshold c) nSrc = nRef at hnD_2R ⊢
          clear *- h1 hnD_2R; omega
      have hib_diff : ibHi ≤ ibLo + mSrc + mDst + 4 := by
        rw [hibHi_eq, hibLo_eq, hpad_eq]
        have hmx : max mSrc mDst ≤ mSrc + mDst :=
          Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
        split_ifs <;> (clear *- hmx; omega)
      have hpw_2n : pairStreamWords (nLive + 1) qHi vB w ≤ 2 * (nLive + 1) + 3 :=
        pairStreamWords_le_two_mul_add_three hw_pos (by clear *- hqHi_w hvb_w; omega)
      have hnRef_big : 2 ^ 20 ≤ max (whpThreshold c) nSrc := hth_big.trans (le_max_left _ _)
      have hibLo_le_loFr : ibLo ≤ loFr := Nat.le_add_right _ _
      dsimp only [loFr, ibHi, ibLo, mSrc, mDst, nLive, nSrc]
        at hfr_hi_mid hib_diff hpw_2n hmS_le hmD_le hnL_2R hnRef_big hibLo_le_loFr ⊢
      generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
        at hmS_le hmD_le hnL_2R hnRef_big ⊢
      clear *- hfr_hi_mid hib_diff hpw_2n hmS_le hmD_le hnL_2R hnRef_big hibLo_le_loFr
      omega
    refine ⟨hpre_bg, hfr_tick, hwf_tick,
      fun addr hlt_b => hout_t addr
        (by dsimp only [hdrPhase]; clear *- hlt_b; omega)
        (by dsimp only [hdrPBase0]; clear *- hlt_b; omega)
        (by dsimp only [hdrSplit]; clear *- hlt_b; omega)
        (by clear *- hlt_b hibLo_eq; omega), ?_⟩
    rw [ite_eq_left (by clear *- hp10; omega)]
    refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
      (fun ⟨h9, _⟩ => by rw [hp10] at h9; cases h9) rfl rfl, ?_, fun _ _ => hmc_all⟩
    refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
    · rw [hnS_t, hph_t, ite_eq_right (by decide : 11 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
    · rw [hph_t, ite_eq_right (by decide : ¬(11 < 2)), ite_eq_right (by decide : 11 ≠ 2),
        ite_eq_right (by decide : ¬(11 ≤ 10)), hibL_t, hqL_t, hfr_tick, hnS_t]
      refine ⟨rfl, hloFr_le_fr, fun hgt_b => ?_, fun hle_b => ?_⟩
      · -- `bulkBatchWhp < s.frontier - loFr`: resting `DualStateInv` at `s.frontier - bulkBatchWhp`
        set fr' := s.frontier - bulkBatchWhp
        have hlo1_le : loFr + 1 ≤ fr' := by
          dsimp only [fr', loFr, ibLo, nLive, qLo, vB] at hgt_b ⊢; clear *- hgt_b; omega
        have hfr'_le_hi : fr' ≤ hiFr := by dsimp only [fr']; clear *- hdiff_le; omega
        have hsl_fr' : EpochSlotInv c U V w fr' (base + hdrPBase0) (dualMbDst base s.mem)
            io_lo 0 false L.slotDst s_tick.mem :=
          hsl_lo_fr.at_exact_frontier (fr₂ := fr')
            (by dsimp only [hdrPBase0]; clear *- hlo1_le hibLo_eq; omega)
            (by
              rw [hcap_d, hmbD_s, ← hmDst_eq]
              by_cases hdz : nDst = 0
              · rw [ite_eq_left hdz, ite_eq_left hdz]; dsimp only [hdrSmallMeta0]
                clear *- hlo1_le hibLo_eq; omega
              · rw [ite_eq_right hdz, ite_eq_right hdz]
                clear *- hlo1_le hibLo_eq; omega)
            (by
              dsimp only [io_lo, directSlotIo]
              simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
              clear *- hlo1_le; omega)
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt (Nat.sub_le _ _) hwf.1, hwf_tick.2⟩
            base_fr := by
              dsimp only [fr', loFr, ibLo] at hlo1_le hibLo_eq ⊢
              clear *- hlo1_le hibLo_eq; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_hdr off (by clear *- hoff; omega)
                (by dsimp only [hdrPhase]; clear *- hoff; omega)
                (by dsimp only [hdrSplit]; clear *- hoff; omega)
            live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)).trans hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]
            stg_le := by dsimp only; rw [hst_t]; exact hstg_le
            mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [Nat.add_assoc]
                exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
            nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                  nDst_zero := fun hz => by
                    dsimp only at hz ⊢
                    obtain ⟨h1', h2', _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                    rw [hnS_t, hst_t, hph_t]; exact ⟨h1', h2', by decide, by decide, by decide⟩
                  stg_one := fun hs_o => by
                    dsimp only at hs_o ⊢; rw [hnD_t, hph_t]
                    exact ⟨(hsched.stg_one (hst_t.symm.trans hs_o)).1, by decide, by decide⟩
                  post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := by dsimp only [L']; simpa using hd_hi'
                  drift_lo := by dsimp only [L']; simpa using hd_lo'
                  ibLo_eq := by
                    dsimp only; rw [hibL_t, hph_t, ite_eq_right (by decide : ¬(11 < 10)), hmD_t]
                    exact hibLo_eq
                  qLo_eq := by
                    dsimp only; rw [hqL_t, hph_t, ite_eq_right (by decide : ¬(11 < 10)), hnD_t]
                    exact hqLo_eq
                  ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
                  ge2 := fun _ => by
                    dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                    · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                        rw [Nat.add_assoc]
                        exact hout_hdr (hdrDstOd + k)
                          (by dsimp only [hdrDstOd]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrSplit]; clear *- hk; omega)
                    · obtain ⟨hl, he, hp⟩ := hd_logs hd
                      exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)).trans hl,
                        (hout_hdr hdrEll (by decide) (by decide) (by decide)).trans he,
                        (hout_hdr hdrPgB (by decide) (by decide) (by decide)).trans hp⟩
                  ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
                  ph3_10 := fun ⟨_, h10⟩ => absurd (hph_t ▸ h10) (by decide)
                  ph11 := fun _ => by
                    dsimp only [loFr, hiFr]; rw [hibL_t, hqL_t, hibH_t, hqH_t]
                    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                    exact ⟨hlo1_le, hfr'_le_hi⟩
                  budget := by
                    dsimp only [L']
                    rw [hnS_t, hst_t, hph_t, hibL_t, hqL_t]
                    unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                    dsimp only at hb_tot ⊢
                    simp only [show s.mem (base + hdrPhase) = 10 from hp10,
                      Bool.false_eq_true, Nat.sub_zero, Nat.reduceEqDiff, Nat.reduceLeDiff,
                      and_false, ↓reduceIte] at hb_tot ⊢
                    have hsh_le : fr' - loFr ≤ 9 * max (whpThreshold c) nSrc := by
                      dsimp only [fr']; clear *- hdiff_9R; omega
                    have hdiv_sh := Nat.div_le_div_right (c := 1022) hsh_le
                    dsimp only [fr', loFr, ibLo, nLive, qLo, vB, nSrc] at hb_tot hdiv_sh ⊢
                    generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
                      at hb_tot hdiv_sh ⊢
                    generalize ((Dictionary.dom s_dict).card - s.mem (base + hdrSplit) - 1) / 1023 =
                      qsd at hb_tot
                    refine ⟨trivial, ?_, ?_⟩ <;> (clear *- hb_tot hdiv_sh; omega) }
            pad_fits := by
              dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 11 ≠ 0)]
              simpa only [hp10, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
            ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
            ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
            ph4_inv := fun hp4 => absurd (hph_t.symm.trans hp4) (by decide)
            pDst_pre := fun ⟨_, hp5⟩ => absurd (hph_t ▸ hp5) (by decide)
            ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
            ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
            ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
            ph8_inv := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
            ph9_inv := fun hp9 => absurd (hph_t.symm.trans hp9) (by decide)
            ph10_inv := fun hp10' => absurd (hph_t.symm.trans hp10') (by decide)
            sl_le7 := fun hp7 => absurd (hph_t ▸ hp7) (by decide)
            sl_67 := fun h67 => by
              dsimp only at h67
              rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›) (by decide)
            sl_8 := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
            sl_ge9 := fun _ => by
              dsimp only [L']
              have hpD11 : dualPDst base s_tick.mem = base + hdrPBase0 := by
                unfold dualPDst; rw [hph_t, ite_eq_right (by decide : ¬(11 < 10))]
              have hmbD11 : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
                rw [hmbD_s]; unfold dualMbDst
                rw [hph_t, ite_eq_right (by decide : ¬(11 < 10)), hnD_t]
              have hio11 : activeDstIo c w vB base stg 11 nSrc nDst pad ibLo qLo ibHi qHi nLive
                  (s_tick.mem (base + hdrUnpermDone)) = io_lo := by
                unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
              rw [hnD_t, hst_t, hph_t, hnS_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t,
                hpD11, hmbD11, hio11]
              simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero]
              exact ⟨hcap_d, hdict_d, hsl_fr', fun hd_pos => by
                have he := hevs_d hd_pos; simp only [↓reduceIte] at he; exact he⟩ }
      · -- `s.frontier - loFr ≤ bulkBatchWhp`: `DualMidInv` at `s_tick` with `{L' with elapsed - 1}`
        have hL_sub : ({ L' with elapsed := L'.elapsed - 1 } : DualLatent c U V) = L := by
          dsimp only [L']; cases L; rfl
        rw [hL_sub]
        refine ⟨?_, Nat.le_add_left 1 _, hel_le'⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := hwf_tick
            base_fr := hfr_tick ▸ hb192
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_hdr off (by clear *- hoff; omega)
                (by dsimp only [hdrPhase]; clear *- hoff; omega)
                (by dsimp only [hdrSplit]; clear *- hoff; omega)
            live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)).trans hlive_eq
            live_le := hlive_le
            ph_le := by rw [hph_t]
            stg_le := by rw [hst_t]; exact hstg_le
            mSrc_eq := by rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [Nat.add_assoc]
                exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
            nSrc_bounds := by rw [hnS_t]; exact hnSrc_b
            sched := by
              rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := by rw [hnD_t]; exact hsched.nDst_bounds
                  nDst_zero := fun hz => by
                    obtain ⟨h1', h2', _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                    rw [hnS_t, hst_t, hph_t]; exact ⟨h1', h2', by decide, by decide, by decide⟩
                  stg_one := fun hs_o => by
                    rw [hnD_t, hph_t]
                    exact ⟨(hsched.stg_one (hst_t.symm.trans hs_o)).1, by decide, by decide⟩
                  post_trig := by rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := hsched.drift_hi
                  drift_lo := hsched.drift_lo
                  ibLo_eq := by
                    rw [hibL_t, hph_t, ite_eq_right (by decide : ¬(11 < 10)), hmD_t]
                    exact hibLo_eq
                  qLo_eq := by
                    rw [hqL_t, hph_t, ite_eq_right (by decide : ¬(11 < 10)), hnD_t]
                    exact hqLo_eq
                  ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
                  ge2 := fun _ => by
                    rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                    · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                        rw [Nat.add_assoc]
                        exact hout_hdr (hdrDstOd + k)
                          (by dsimp only [hdrDstOd]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrSplit]; clear *- hk; omega)
                    · obtain ⟨hl, he, hp⟩ := hd_logs hd
                      exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)).trans hl,
                        (hout_hdr hdrEll (by decide) (by decide) (by decide)).trans he,
                        (hout_hdr hdrPgB (by decide) (by decide) (by decide)).trans hp⟩
                  ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
                  ph3_10 := fun ⟨_, h10⟩ => absurd (hph_t ▸ h10) (by decide)
                  ph11 := fun _ => by
                    rw [hibL_t, hqL_t, hibH_t, hqH_t, hfr_tick]
                    simp only [↓reduceIte]
                    exact ⟨hloFr_le_fr, hfr_hi_mid⟩
                  budget := by
                    dsimp only
                    rw [hnS_t, hst_t, hph_t, hibL_t, hqL_t, hfr_tick]
                    unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                    dsimp only at hb_tot ⊢
                    simp only [show s.mem (base + hdrPhase) = 10 from hp10,
                      Nat.reduceEqDiff, Nat.reduceLeDiff, and_false, ↓reduceIte] at hb_tot ⊢
                    have hdiv_le1 : (s.frontier - loFr - 2) / 1022 ≤ 1 := by
                      dsimp only [loFr, ibLo, nLive, qLo, vB] at hle_b ⊢
                      unfold bulkBatchWhp at hle_b; clear *- hle_b; omega
                    dsimp only [loFr, ibLo, nLive, qLo, vB, nSrc] at hb_tot hb_el2 hdiv_le1 ⊢
                    generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
                      at hb_tot hb_el2 ⊢
                    generalize (s.frontier -
                      (s.mem (base + hdrItemLo) +
                        pairStreamWords (Dictionary.dom s_dict).card
                          (s.mem (base + hdrQLo)) (valBits V) w) - 2) / 1022 = qsh at hdiv_le1 ⊢
                    refine ⟨trivial, ?_, hb_el2⟩
                    clear *- hb_tot hdiv_le1; omega }
            pad_fits := by
              rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 11 ≠ 0)]
              simpa only [hp10, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
            ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
            ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
            ph4_inv := fun hp4 => absurd (hph_t.symm.trans hp4) (by decide)
            pDst_pre := fun ⟨_, hp5⟩ => absurd (hph_t ▸ hp5) (by decide)
            ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
            ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
            ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
            ph8_inv := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
            ph9_inv := fun hp9 => absurd (hph_t.symm.trans hp9) (by decide)
            ph10_inv := fun hp10' => absurd (hph_t.symm.trans hp10') (by decide)
            sl_le7 := fun hp7 => absurd (hph_t ▸ hp7) (by decide)
            sl_67 := fun h67 => by
              rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›) (by decide)
            sl_8 := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
            sl_ge9 := fun _ => by
              have hpD11 : dualPDst base s_tick.mem = base + hdrPBase0 := by
                unfold dualPDst; rw [hph_t, ite_eq_right (by decide : ¬(11 < 10))]
              have hmbD11 : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
                rw [hmbD_s]; unfold dualMbDst
                rw [hph_t, ite_eq_right (by decide : ¬(11 < 10)), hnD_t]
              have hio11 : activeDstIo c w vB base stg 11 nSrc nDst pad ibLo qLo ibHi qHi nLive
                  (s_tick.mem (base + hdrUnpermDone)) = io_lo := by
                unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
              rw [hnD_t, hst_t, hph_t, hnS_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t,
                hpD11, hmbD11, hio11, hfr_tick]
              simp only [Nat.reduceEqDiff, false_and, and_false, ↓reduceIte]
              exact ⟨hcap_d, hdict_d, hsl_lo_fr, hevs_d⟩ }
  · -- Branch `10 → 10` (`sp' < nLive`: stays in Phase `10` with `s_tick = s3`)
    have hsp'_lt : sp' < nLive := Nat.lt_of_not_ge hdone
    have hsp'_eq_add : sp' = sp + itemBatchWhp := min_eq_right (by clear *- hsp'_lt; omega)
    have hdone_raw : ¬(nLive ≤ (Memory.spec 0).clientResult s
        (slideDownBatchProg (((cfg.toCtx, nLive), sp), itemBatchWhp))) := by
      rwa [hres_sb]
    rw [hs3_eq_raw, ite_eq_right hdone_raw] at hst_sd
    have hs_tick_eq : s_tick = s3 := hst_bg.trans hst_sd
    have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
    have hout_hdr : ∀ off < 48, off ≠ hdrSplit → s_tick.mem (base + off) = s.mem (base + off) :=
      fun off hoff hsp => by
        rw [hs_tick_eq]
        exact hout_s3 (base + off) (base_add_ne hsp) (by clear *- hoff hibLo_eq; omega)
    have hph_t : s_tick.mem (base + hdrPhase) = 10 :=
      (hout_hdr hdrPhase (by decide) (by decide)).trans hp10
    have hsp_t : s_tick.mem (base + hdrSplit) = sp' := by
      rw [hs_tick_eq]; exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = stg :=
      hout_hdr hdrStage (by decide) (by decide)
    have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
      hout_hdr hdrNSrc (by decide) (by decide)
    have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
      hout_hdr hdrNDst (by decide) (by decide)
    have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
      hout_hdr hdrMSrc (by decide) (by decide)
    have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
      hout_hdr hdrMDst (by decide) (by decide)
    have hpad_t : s_tick.mem (base + hdrPad) = pad :=
      hout_hdr hdrPad (by decide) (by decide)
    have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
      hout_hdr hdrItemLo (by decide) (by decide)
    have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
      hout_hdr hdrItemHi (by decide) (by decide)
    have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
      hout_hdr hdrQLo (by decide) (by decide)
    have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
      hout_hdr hdrQHi (by decide) (by decide)
    have hsl_hi : EpochSlotInv c U V w hiFr (base + hdrPBase0) (dualMbDst base s.mem)
        io_sp 0 false L.slotDst s_tick.mem := by
      rw [hs_tick_eq]
      have hraw := hsl_d0; unfold EpochSlotInv at hraw
      have hp_s3 : ∀ a, base + hdrPBase0 ≤ a → a < base + hdrPBase0 + 64 → s3.mem a = s.mem a :=
        fun a h1 h2 => hout_s3 a
          (by dsimp only [hdrPBase0, hdrSplit] at h1 h2 ⊢; omega)
          (by dsimp only [hdrPBase0, loFr] at h1 h2; clear *- h1 h2 hibLo_eq; omega)
      have hsl_s3 := hsl_d0.transfer_io (slack₂ := 0) (io₂ := io_sp) hsl_d0.io_valid rfl
        ⟨fun h0 => by rw [ite_eq_left h0] at hraw; exact hraw.2.2.1.qBits_eq,
         fun h0 => by rw [ite_eq_right h0] at hraw; exact hraw.1.qBits_le⟩
        rfl
        ⟨fun h0 => by rw [ite_eq_left h0] at hraw; exact hraw.2.2.2.1.congr hp_s3,
         fun h0 => by
          rw [ite_eq_right h0] at hraw
          exact hraw.2.1.1.congr fun a hlo hhi => hp_s3 a hlo (by dsimp only at hlo hhi; omega)⟩
        (fun a hlo hhi => by
          by_cases h0 : L.slotDst.nCap = 0
          · rw [ite_eq_left h0] at hraw
            exact fun hia => hraw.2.2.2.2.1 a hlo hhi (Or.inr (Or.inr hia))
          · rw [ite_eq_right h0] at hraw; exact hraw.1.disj_pBase_io a hlo hhi)
        (fun a ha => by
          unfold slotOwnsNonPageMeta at ha
          by_cases h0 : L.slotDst.nCap = 0
          · rw [ite_eq_left h0] at hraw ha
            rcases ha with ⟨g1, g2⟩ | ⟨hne, _⟩
            · exact hraw.2.2.1.disjoint_hdr a (by dsimp only; omega)
            · exact absurd h0 hne
          · rw [ite_eq_right h0] at hraw ha
            exact hraw.1.disj_fast_io a (ha.imp id And.right))
        hm_s3_d
        (by
          unfold SlotIoLayout.StateInv; dsimp only [io_sp, splitSlotIo]
          simp only [↓reduceIte, one_ne_zero]
          rw [hns_d]; exact ⟨le_rfl, Or.inr hqHi_w⟩)
        (fun p hp => hs3_pair p (hns_d ▸ hp))
      exact hsl_s3.at_exact_frontier (fr₂ := hiFr)
        (by dsimp only [hdrPBase0, hiFr]; clear *- hibLo_eq hibLo_le_ibHi; omega)
        (by
          rw [hcap_d, hmbD_s, ← hmDst_eq]
          by_cases hdz : nDst = 0
          · rw [ite_eq_left hdz, ite_eq_left hdz]; dsimp only [hdrSmallMeta0, hiFr]
            clear *- hibLo_eq hibLo_le_ibHi; omega
          · rw [ite_eq_right hdz, ite_eq_right hdz]; dsimp only [hiFr]
            clear *- hibLo_eq hibLo_le_ibHi; omega)
        (by dsimp only [io_sp, splitSlotIo, hiFr]; exact le_rfl)
    refine ⟨hpre_bg, hfr_tick, hwf_tick,
      fun addr hlt_b => by
        rw [hs_tick_eq]
        exact hout_s3 addr (by dsimp only [hdrSplit]; clear *- hlt_b; omega)
          (by clear *- hlt_b hibLo_eq; omega), ?_⟩
    rw [ite_eq_left (by clear *- hp10; omega)]
    refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
      (fun ⟨h9, _⟩ => by rw [hp10] at h9; cases h9) rfl rfl, ?_, fun _ _ => hmc_all⟩
    refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
    · rw [hnS_t, hph_t, ite_eq_right (by decide : 10 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
    · rw [hph_t, ite_eq_right (by decide : ¬(10 < 2)), ite_eq_right (by decide : 10 ≠ 2),
        ite_eq_left (by decide : 10 ≤ 10), hibH_t, hqH_t, hfr_tick]
      refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
      exact
        { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
          wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
          base_fr := by dsimp only [hiFr]; clear *- hibLo_eq hibLo_le_ibHi; omega
          hdr := rootStaticHeader_congr hhdr fun off hoff =>
            hout_hdr off (by clear *- hoff; omega)
              (by dsimp only [hdrSplit]; clear *- hoff; omega)
          live_eq := (hout_hdr hdrLive (by decide) (by decide)).trans hlive_eq
          live_le := hlive_le
          ph_le := by dsimp only; rw [hph_t]; decide
          stg_le := by dsimp only; rw [hst_t]; exact hstg_le
          mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
          cache_src := by
            dsimp only; rw [hnS_t]
            exact hostCacheValid_congr_mem hcache_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrSplit]; clear *- hk; omega)
          nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
          sched := by
            dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
            refine
              { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                nDst_zero := fun hz => by
                  dsimp only at hz ⊢
                  obtain ⟨h1', h2', _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                  rw [hnS_t, hst_t, hph_t]; exact ⟨h1', h2', by decide, by decide, by decide⟩
                stg_one := fun hs_o => by
                  dsimp only at hs_o ⊢; rw [hnD_t, hph_t]
                  exact ⟨(hsched.stg_one (hst_t.symm.trans hs_o)).1, by decide, by decide⟩
                post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
                trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                drift_hi := by dsimp only [L']; simpa using hd_hi'
                drift_lo := by dsimp only [L']; simpa using hd_lo'
                ibLo_eq := by
                  dsimp only; rw [hibL_t, hph_t, ite_eq_right (by decide : ¬(10 < 10)), hmD_t]
                  exact hibLo_eq
                qLo_eq := by
                  dsimp only; rw [hqL_t, hph_t, ite_eq_right (by decide : ¬(10 < 10)), hnD_t]
                  exact hqLo_eq
                ph1 := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
                ge2 := fun _ => by
                  dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                  refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                  · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                      rw [Nat.add_assoc]
                      exact hout_hdr (hdrDstOd + k)
                        (by dsimp only [hdrDstOd]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrSplit]; clear *- hk; omega)
                  · obtain ⟨hl, he, hp⟩ := hd_logs hd
                    exact ⟨(hout_hdr hdrLogN (by decide) (by decide)).trans hl,
                      (hout_hdr hdrEll (by decide) (by decide)).trans he,
                      (hout_hdr hdrPgB (by decide) (by decide)).trans hp⟩
                ph2 := fun hp2 => absurd (hph_t.symm.trans hp2) (by decide)
                ph3_10 := fun _ => by
                  dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                ph11 := fun hp11 => absurd (hph_t.symm.trans hp11) (by decide)
                budget := by
                  dsimp only [L']
                  rw [hnS_t, hst_t, hph_t, hsp_t]
                  unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                  simp only [show s.mem (base + hdrPhase) = 10 from hp10,
                    Bool.false_eq_true, Nat.sub_zero, Nat.reduceEqDiff, Nat.reduceLeDiff,
                    and_false, ↓reduceIte] at hb_tot ⊢
                  have hstep_div :
                      (nLive - sp') / 1023 + 1 ≤ (nLive - sp - 1) / 1023 + 1 - 1 := by
                    rw [hsp'_eq_add]; unfold itemBatchWhp at hsp'_eq_add ⊢
                    have hle_num : (nLive - (sp + 1024)) + 1023 ≤ nLive - sp - 1 := by
                      clear *- hsp'_lt hsp'_eq_add; omega
                    have hd := Nat.div_le_div_right (c := 1023) hle_num
                    rw [Nat.add_div_right _ (by decide : 0 < 1023)] at hd
                    clear *- hd; omega
                  dsimp only [nLive, sp, nSrc] at hb_tot hstep_div ⊢
                  generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef at hb_tot ⊢
                  generalize ((Dictionary.dom s_dict).card - sp') / 1023 = q1 at hstep_div ⊢
                  generalize ((Dictionary.dom s_dict).card - s.mem (base + hdrSplit) - 1) / 1023 =
                    q0 at hb_tot hstep_div
                  refine ⟨?_, ?_, ?_⟩ <;> (clear *- hb_tot hstep_div; omega) }
          pad_fits := by
            dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 10 ≠ 0)]
            simpa only [hp10, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
          ph1_inv := fun hp1 => absurd (hph_t.symm.trans hp1) (by decide)
          ph3_inv := fun hp3 => absurd (hph_t.symm.trans hp3) (by decide)
          ph4_inv := fun hp4 => absurd (hph_t.symm.trans hp4) (by decide)
          pDst_pre := fun ⟨_, hp5⟩ => absurd (hph_t ▸ hp5) (by decide)
          ph5_inv := fun hp5 => absurd (hph_t.symm.trans hp5) (by decide)
          ph6_inv := fun hp6 => absurd (hph_t.symm.trans hp6) (by decide)
          ph7_inv := fun hp7 => absurd (hph_t.symm.trans hp7) (by decide)
          ph8_inv := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
          ph9_inv := fun hp9 => absurd (hph_t.symm.trans hp9) (by decide)
          ph10_inv := fun _ => by
            dsimp only; rw [hsp_t, hibL_t, hqL_t, hibH_t, hqH_t, hs_tick_eq]
            exact ⟨hsp'_lt.le, hs3_hiQuot⟩
          sl_le7 := fun hp7 => absurd (hph_t ▸ hp7) (by decide)
          sl_67 := fun h67 => by
            dsimp only at h67
            rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›) (by decide)
          sl_8 := fun hp8 => absurd (hph_t.symm.trans hp8) (by decide)
          sl_ge9 := fun _ => by
            dsimp only [L']
            have hpD10 : dualPDst base s_tick.mem = base + hdrPBase0 := by
              unfold dualPDst; rw [hph_t, ite_eq_right (by decide : ¬(10 < 10))]
            have hmbD10 : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
              rw [hmbD_s]; unfold dualMbDst
              rw [hph_t, ite_eq_right (by decide : ¬(10 < 10)), hnD_t]
            have hio10 : activeDstIo c w vB base stg 10 nSrc nDst pad ibLo qLo ibHi qHi nLive
                (s_tick.mem (base + hdrUnpermDone)) = io_sp := by
              unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]; rfl
            rw [hnD_t, hst_t, hph_t, hnS_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t,
              hpD10, hmbD10, hio10]
            simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero]
            exact ⟨hcap_d, hdict_d, hsl_hi, fun hd_pos => by
              have he := hevs_d hd_pos; simp only [↓reduceIte] at he; exact he⟩ }

/-- Phase `11` (`shrinkPost`) background tick pass-through specification. -/
theorem tickPhase11_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp11 : s.mem (base + hdrPhase) = 11) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hw_pos : 0 < w := by clear *- hw11; omega
  have hwf := h.wf; have hb192 := h.base_fr
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp11; omega)] at hsched
  obtain ⟨hfr_lo11, hfr_hi11⟩ := hsched.ph11 hp11
  simp only [↓reduceIte, add_zero] at hfr_lo11 hfr_hi11
  obtain ⟨_, _, _, _, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by clear *- hp11; omega)] at hpad_hi_s
  have hfr_le_pad := hfr_hi11.trans hpad_hi_s
  have hbud_old := hsched.budget; dsimp only at hbud_old
  obtain ⟨_, hb_tot, hb_el2⟩ := hbud_old
  set nLive := (Dictionary.dom s_dict).card
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set vB := valBits V
  set loFr := ibLo + pairStreamWords nLive qLo vB w
  have hibLo_eq : ibLo = base + 192 + s.mem (base + hdrMDst) := by
    have hib := hsched.ibLo_eq; rwa [hp11, ite_eq_right (by decide : ¬(11 < 10))] at hib
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, ?_⟩
    dsimp only; simp only [hp11, Nat.reduceEqDiff, ↓reduceIte]
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  simp only [hp11, Nat.reduceEqDiff, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
  refine ⟨hpre_bg, by rw [hst_bg], by rw [hst_bg]; exact hwf,
    fun _ _ => by rw [hst_bg], ?_⟩
  rw [ite_eq_left (by clear *- hp11; omega), hst_bg]
  refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
    (fun ⟨h9, _⟩ => by rw [hp11] at h9; cases h9) rfl rfl, ?_,
    fun _ _ => by clear *- hmc_bg; omega⟩
  refine ⟨hwf, ?_, fun h5 => absurd (hp11.symm.trans h5) (by decide), ?_⟩
  · rw [ite_eq_right (by clear *- hp11; omega)]; exact hfr_le_pad
  · rw [hp11, ite_eq_right (by decide : ¬(11 < 2)), ite_eq_right (by decide : 11 ≠ 2),
      ite_eq_right (by decide : ¬(11 ≤ 10))]
    refine ⟨rfl, hfr_lo11, fun hgt_b => ?_, fun _ => ?_⟩
    · set fr' := s.frontier - bulkBatchWhp
      dsimp only [loFr, ibLo, nLive, qLo, vB] at hgt_b hfr_hi11 hibLo_eq ⊢
      have hlo1_le : s.mem (base + hdrItemLo) +
          pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQLo)) (valBits V) w + 1 ≤
          fr' := by dsimp only [fr']; clear *- hgt_b; omega
      obtain ⟨hcap_d, hdict_d, hsl_d, hevs_d⟩ := h.sl_ge9 (by clear *- hp11; omega)
      have hpD11 : dualPDst base s.mem = base + hdrPBase0 := by
        unfold dualPDst; rw [hp11, ite_eq_right (by decide : ¬(11 < 10))]
      have hmbD11 : dualMbDst base s.mem =
          (if nDst = 0 then base + hdrSmallMeta0 else base + 192) := by
        unfold dualMbDst; rw [hp11, ite_eq_right (by decide : ¬(11 < 10))]
      have hio11 : activeDstIo c w vB base (s.mem (base + hdrStage)) (s.mem (base + hdrPhase))
          nSrc nDst (s.mem (base + hdrPad)) ibLo qLo (s.mem (base + hdrItemHi))
          (s.mem (base + hdrQHi)) nLive (s.mem (base + hdrUnpermDone)) =
          directSlotIo w vB base ibLo qLo nLive := by
        rw [hp11]; unfold activeDstIo; simp only [Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte]
      have hsl_d0 : EpochSlotInv c U V w s.frontier (base + hdrPBase0) (dualMbDst base s.mem)
          (directSlotIo w vB base ibLo qLo nLive) 0 false L.slotDst s.mem := by
        rw [hpD11, hio11] at hsl_d
        simpa only [hp11, Nat.reduceEqDiff, false_and, and_false, ↓reduceIte] using hsl_d
      have hmDst_eq := (hsched.ge2 (by clear *- hp11; omega)).1
      have hsl_fr' := hsl_d0.at_exact_frontier (fr₂ := fr')
        (by dsimp only [hdrPBase0]; clear *- hlo1_le hibLo_eq; omega)
        (by
          rw [hcap_d, hmbD11, ← hmDst_eq]
          by_cases hdz : nDst = 0
          · rw [ite_eq_left hdz, ite_eq_left hdz]; dsimp only [hdrSmallMeta0]
            clear *- hlo1_le hibLo_eq; omega
          · rw [ite_eq_right hdz, ite_eq_right hdz]; clear *- hlo1_le hibLo_eq; omega)
        (by
          dsimp only [directSlotIo, ibLo, nLive, qLo, vB]
          simp only [ne_eq, not_true_eq_false, and_false, ↓reduceIte]
          clear *- hlo1_le; omega)
      exact
        { h with
          wf := ⟨lt_of_le_of_lt (Nat.sub_le _ _) hwf.1, hwf.2⟩
          base_fr := by dsimp only; clear *- hlo1_le hibLo_eq; omega
          ph7_inv := fun hp7 => absurd (hp11.symm.trans hp7) (by decide)
          ph9_inv := fun hp9 => absurd (hp11.symm.trans hp9) (by decide)
          sl_le7 := fun hp7 => absurd (hp11 ▸ hp7) (by decide)
          sl_67 := fun h67 => by
            dsimp only at h67
            rcases h67 with h6 | h7 <;> exact absurd (hp11.symm.trans ‹_›) (by decide)
          sl_8 := fun hp8 => absurd (hp11.symm.trans hp8) (by decide)
          sched := by
            dsimp only; rw [ite_eq_right (by clear *- hp11; omega)]
            refine
              { hsched with
                drift_hi := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  simpa only [↓reduceIte] using hsched.drift_hi
                drift_lo := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  simpa only [↓reduceIte] using hsched.drift_lo
                ph1 := fun hp1 => absurd (hp11.symm.trans hp1) (by decide)
                ph2 := fun hp2 => absurd (hp11.symm.trans hp2) (by decide)
                ph3_10 := fun ⟨_, h10⟩ => absurd (hp11 ▸ h10) (by decide)
                ph11 := fun _ => by
                  dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hpw2' := pairStreamWords_succ_le_add_two (n := nLive)
                    (qb := s.mem (base + hdrQHi)) (vb := vB) hw_pos
                    (by
                      have hqHw := (dualCoreInv_ib_fits h).2.2.2.1
                      have hvbw := (dualCoreInv_ib_fits h).2.1
                      clear *- hqHw hvbw; omega)
                  refine ⟨hlo1_le, ?_⟩
                  dsimp only [fr', nLive, vB] at hpw2' ⊢; unfold bulkBatchWhp at hgt_b ⊢
                  clear *- hfr_hi11 hpw2' hgt_b; omega
                budget := by
                  dsimp only [L', loFr, ibLo, nLive, qLo, vB] at hb_tot ⊢
                  unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                  dsimp only at hb_tot ⊢
                  simp only [hp11, Bool.false_eq_true, Nat.sub_zero, Nat.reduceEqDiff,
                    Nat.reduceLeDiff, and_false, ↓reduceIte] at hb_tot ⊢
                  set loRaw := s.mem (base + hdrItemLo) +
                    pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQLo))
                      (valBits V) w
                  have hstep_sh : (fr' - loRaw) / 1022 + 1 ≤ (s.frontier - loRaw - 2) / 1022 := by
                    dsimp only [fr', loRaw]; unfold bulkBatchWhp at hgt_b ⊢
                    have hle_num : (s.frontier - 1024 -
                        (s.mem (base + hdrItemLo) +
                          pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQLo))
                            (valBits V) w)) + 1022 ≤
                        s.frontier -
                          (s.mem (base + hdrItemLo) +
                            pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQLo))
                              (valBits V) w) - 2 := by
                      clear *- hgt_b; omega
                    have hd := Nat.div_le_div_right (c := 1022) hle_num
                    rwa [Nat.add_div_right _ (by decide : 0 < 1022)] at hd
                  dsimp only [loRaw] at hstep_sh
                  generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef at hb_tot hb_el2 ⊢
                  generalize (fr' -
                    (s.mem (base + hdrItemLo) +
                      pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQLo))
                        (valBits V) w)) / 1022 = q1 at hstep_sh ⊢
                  generalize (s.frontier -
                    (s.mem (base + hdrItemLo) +
                      pairStreamWords (Dictionary.dom s_dict).card (s.mem (base + hdrQLo))
                        (valBits V) w) - 2) / 1022 = q0 at hb_tot hstep_sh
                  refine ⟨trivial, ?_, ?_⟩ <;> (clear *- hb_tot hb_el2 hstep_sh; omega) }
          sl_ge9 := fun _ => by
            dsimp only [L']
            rw [hpD11, hio11]
            simp only [Bool.false_eq_true, false_and, ↓reduceIte, add_zero]
            exact ⟨hcap_d, hdict_d, hsl_fr', fun hd_pos => by
              have he := hevs_d hd_pos; simp only [↓reduceIte] at he; exact he⟩ }
    · have hL_sub : ({ L' with elapsed := L'.elapsed - 1 } : DualLatent c U V) = L := by
        dsimp only [L']; cases L; rfl
      rw [hL_sub]
      dsimp only [L']
      exact ⟨h, Nat.le_add_left 1 _, by clear *- hb_el2; omega⟩

/-- Unified 12-phase (`0..11`) background tick specification. -/
theorem bgTickProg_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hsucc_fits : base + Dynamic.succinctWords (whpResizableSpaceFactor c)
      whpResizableSpaceConst U V w (Dictionary.dom s_dict).card < 2 ^ w) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  set ph := s.mem (base + hdrPhase) with hph_def
  have hph_le : ph ≤ 11 := h.ph_le
  interval_cases ph
  · exact tickPhase0_spec h hph_def.symm hsucc_fits
  · exact tickPhase1_spec h hph_def.symm
  · exact tickPhase2_spec h hph_def.symm
  · exact tickPhase3_spec h hph_def.symm
  · exact tickPhase4_spec h hph_def.symm
  · exact tickPhase5_spec h hph_def.symm
  · exact tickPhase6_spec h hph_def.symm
  · exact tickPhase7_spec h hph_def.symm
  · exact tickPhase8_spec h hph_def.symm
  · exact tickPhase9_spec h hph_def.symm
  · exact tickPhase10_spec h hph_def.symm
  · exact tickPhase11_spec h hph_def.symm

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvTickA1

/-!
# Background Tick Phases `4..5` (`DualEpochInvTickA2`)

Proves `BgTickPre` and `DualPostTickInv` for background tick phases:
* Phase `4` (`tickZeroMetaProg`, `tickPhase4_spec`): incremental destination metadata zeroing and
  Stage-B `writeLargeParamTableProg` setup (`4 → 5`).
* Phase `5` (`tickRandPrepProg`, `tickPhase5_spec`): uniform random word-fill range preparation and
  post-`writeWords` invariant preservation across `[metaDst + cur, metaDst + endOff)`.

## Main results

* `tickPhase4_spec`, `tickPhase5_spec`

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

attribute [local irreducible] epochMetaWordsWhp

/-! ## Section 4: Phase `4` (`tickZeroMetaProg`) Specification -/

/-- Phase `4` (`zeroMeta`) background tick specification. -/
theorem tickPhase4_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp4 : s.mem (base + hdrPhase) = 4) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb192 := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hstg_le := h.stg_le
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp4; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_mid⟩ := hsched.ph3_10 ⟨by clear *- hp4; omega, by clear *- hp4; omega⟩
  simp only [↓reduceIte] at hfr_hi_mid
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hlog_d, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp4; omega)
  obtain ⟨_, hvb_w, _, hqHi_w, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by clear *- hp4; omega)] at hpad_hi_s
  obtain ⟨hd_pos, hcur_le, hzero_pre⟩ := h.ph4_inv hp4
  have hth_d : whpThreshold c ≤ s.mem (base + hdrNDst) ∧ s.mem (base + hdrNDst) ≤ U := by
    rcases hsched.nDst_bounds with hz | hb
    · exact absurd hz hd_pos.ne'
    · exact hb
  obtain ⟨hlog_e, hell_e, hpg_e⟩ := hlog_d hd_pos
  obtain ⟨hoff32_fp, hoffFp_bm, hoffBm_od, hoffOd_m⟩ := epochMeta_offsets_le (w := w) hth_d.1
  have hw_pos : 0 < w := by clear *- hw11; omega
  set nLive := (Dictionary.dom s_dict).card
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set cur := s.mem (base + hdrCur)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set metaDst := if stg = 0 then base + 192 + pad else base + 192
  have hm32 : 32 ≤ mDst := by
    have hle := hoff32_fp.trans (hoffFp_bm.trans (hoffBm_od.trans hoffOd_m))
    exact hle.trans hmDst_eq.symm.le
  have hibHi_val : ibHi = base + 192 + pad + mDst + 4 := by
    rw [hibHi_eq, ite_eq_right hd_pos.ne']
  have hmDst_pad : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
  have hmSrc_pad : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
  have hmd_end_lt : metaDst + mDst < ibHi := by
    dsimp only [metaDst]; split_ifs <;> (clear *- hibHi_val hmDst_pad; omega)
  have hmd_fr : metaDst + mDst ≤ s.frontier :=
    (hmd_end_lt.le.trans (Nat.le_add_right _ _)).trans hfr_hi_lo
  have hmd_lt : metaDst < s.frontier := by clear *- hm32 hmd_fr; omega
  have hmbDst_eq : dualMbDst base s.mem = metaDst := by
    unfold dualMbDst
    rw [hp4, ite_eq_left (by decide : 4 < 10), ite_eq_right hd_pos.ne']
  obtain ⟨hsafe_zb, hres_zb, hfr_zb, hmc_zb, hmem_zb⟩ :=
    zeroWordsBatchProg_spec hw_pos hcur_le hmd_lt hmd_fr bulkBatchWhp
  set s1 := (Memory.spec 0).clientState s
    (zeroWordsBatchProg (((metaDst, mDst), cur), bulkBatchWhp))
  set cur' := min mDst (cur + bulkBatchWhp)
  have hhdr_s1 : RootStaticHeader c U V w base s1.mem :=
    rootStaticHeader_congr hhdr fun off hoff => by
      rw [hmem_zb, ite_eq_right]
      dsimp only [metaDst]; split_ifs <;> (clear *- hoff; omega)
  have hred_w : redWidthWhp U ≤ w :=
    max_le (by clear *- hw11; omega) (Nat.clog_le_of_le_pow hUw.le)
  have hwlp_pre_s1 : WriteLargeParamPre w
      ((base, base + hdrPBase0), ((nDst, base + 192),
        ((s.mem (base + hdrLogN), s.mem (base + hdrEll)), s.mem (base + hdrPgB)))) s1 := by
    refine ⟨c, U, V, Or.inl (by dsimp only [hdrPBase0]; omega), hth_d.1, hth_d.2, hUw, hV0, hVw,
      hlog_e, hell_e, hpg_e, ?_, hred_w,
      by rw [hfr_zb]; clear *- hb192; omega,
      by rw [hfr_zb]; dsimp only [hdrPBase0]; clear *- hb192; omega, hhdr_s1⟩
    have hf := hwf.1
    unfold Fits at hf ⊢
    rw [← hmDst_eq]
    clear *- hmDst_pad hibHi_val hfr_hi_lo hf; omega
  have hpre_zm : TickZeroMetaPre w base s :=
    ⟨hw11, hb192, hcur_le, hmd_lt, hmd_fr, fun _ => hwlp_pre_s1⟩
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, ?_⟩
    dsimp only
    iterate 4 rw [ite_eq_right (by clear *- hp4; omega)]
    rw [ite_eq_left hp4]
    exact hpre_zm
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  simp only [hp4, show (4 : ℕ) ≠ 0 by decide, show (4 : ℕ) ≠ 1 by decide,
    show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide,
    show (4 : ℕ) ≠ 5 by decide, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_zm, hmc_zm⟩ := tickZeroMetaProg_eval base s
  dsimp only at hst_zm hmc_zm
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hwf_tick : Memory.WellFormed w s_tick :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show qHi + vB ≤ 2 * w by clear *- hqHi_w hvb_w; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    unfold bulkBatchWhp; clear *- hfr_hi_mid hpw2; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive :=
    hfr_hi_mid.trans hpad_hi_s
  obtain ⟨hcap_s, hdict_s, hsl_s, hlen_s⟩ := h.sl_le7 (by clear *- hp4; omega)
  have hio_s : activeSrcIo c w vB base stg (s.mem (base + hdrPhase))
      nSrc nDst pad ibLo qLo ibHi qHi nLive = directSlotIo w vB base ibHi qHi nLive := by
    unfold activeSrcIo
    rw [ite_eq_right (by clear *- hp4; omega), ite_eq_right (by clear *- hp4; omega),
      ite_eq_left (by clear *- hp4; omega)]
  rw [hio_s] at hsl_s
  have hdisj_src_meta : ∀ a, slotOwnsNonPageMeta c w (dualMbSrc base s.mem) L.slotSrc.nCap a →
      ¬(metaDst ≤ a ∧ a < metaDst + mDst) := by
    intro a ha hmd
    unfold slotOwnsNonPageMeta dualMbSrc at ha
    rw [hcap_s] at ha; unfold dualCapSrc at ha
    by_cases hst0 : stg = 0
    · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
      have hmd_eq : metaDst = base + 192 + pad := ite_eq_left hst0
      by_cases hs0 : nSrc = 0
      · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte,
          ne_eq, not_true_eq_false, false_and, or_false] at ha
        dsimp only [hdrSmallMeta0] at ha
        clear *- ha hmd hmd_eq; omega
      · have hth_s : whpThreshold c ≤ nSrc := by
          rcases hnSrc_b with hz | ⟨hth, _⟩
          · exact absurd hz hs0
          · exact hth
        have hod_le : offPageDir c w nSrc ≤ mSrc :=
          (epochMeta_offsets_le hth_s).2.2.2.trans hmSrc_eq.symm.le
        have hmS_ge : 32 ≤ mSrc :=
          (epochMeta_offsets_le hth_s).1.trans
            ((epochMeta_offsets_le hth_s).2.1.trans
              ((epochMeta_offsets_le hth_s).2.2.1.trans hod_le))
        simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte] at ha
        dsimp only [mSrc, pad, mDst] at ha hmSrc_pad hod_le hmS_ge hmd hmd_eq
        rcases ha with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
        · clear *- h1 h2 hmS_ge hmSrc_pad hmd hmd_eq; omega
        · clear *- h1 h2 hod_le hmSrc_pad hmd hmd_eq; omega
    · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
      have hmd_eq : metaDst = base + 192 := ite_eq_right hst0
      dsimp only [mDst, pad] at ha hmDst_pad hmd
      rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> (clear *- h1 hmDst_pad hmd hmd_eq; omega)
  have hrem_b := hsched.budget
  dsimp only at hrem_b
  set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
  by_cases hlt : cur' < mDst
  · -- Stays in `ph = 4` (`cur' < mDst`, so `cur' = cur + 1024`):
    have hlt_raw : (Memory.spec 0).clientResult s
        (zeroWordsBatchProg (((metaDst, mDst), cur), bulkBatchWhp)) < mDst := hres_zb ▸ hlt
    have hcur'_eq : cur' = cur + bulkBatchWhp :=
      min_eq_right (by dsimp only [cur'] at hlt; clear *- hlt; omega)
    have hs_tick_eq : s_tick =
        { mem := Function.update s1.mem (base + hdrCur) cur', frontier := s.frontier } := by
      rw [hst_bg, hst_zm, ite_eq_left hlt_raw, hres_zb, hfr_zb]
    have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
    have hout_t : ∀ a, a ≠ base + hdrCur → ¬(metaDst ≤ a ∧ a < metaDst + mDst) →
        s_tick.mem a = s.mem a := by
      intro a hc hmd
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne hc, hmem_zb, ite_eq_right]
      have hc_le : cur' ≤ mDst := min_le_left _ _
      clear *- hmd hc_le; omega
    have hout_off : ∀ off < 192, off ≠ hdrCur → s_tick.mem (base + off) = s.mem (base + off) :=
      fun off hoff hc =>
        hout_t (base + off) (base_add_ne hc)
          (by dsimp only [metaDst]; split_ifs <;> (clear *- hoff; omega))
    have hph_t : s_tick.mem (base + hdrPhase) = 4 :=
      (hout_off hdrPhase (by decide) (by decide)).trans hp4
    have hcur_t : s_tick.mem (base + hdrCur) = cur' := by
      rw [hs_tick_eq]; exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = stg :=
      hout_off hdrStage (by decide) (by decide)
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
        (dualMbSrc base s_tick.mem) (directSlotIo w vB base ibHi qHi nLive) 0 false
        L.slotSrc s_tick.mem := by
      have hpS_t : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
        unfold dualPSrc; rw [hst_t]
      have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
        unfold dualMbSrc; rw [hst_t, hnS_t, hpad_t]
      rw [hpS_t, hmS_mb]
      have hsl_t_fr : EpochSlotInv c U V w s.frontier (dualPSrc base s.mem)
          (dualMbSrc base s.mem) (directSlotIo w vB base ibHi qHi nLive) 0 false
          L.slotSrc s_tick.mem :=
        hsl_s.congr_mem
          (fun a h1 h2 => by
            have hp_lt : a < base + 192 := by
              unfold dualPSrc at h2; split_ifs at h2 <;>
                (dsimp only [hdrPBase0, hdrPBase1] at h2; clear *- h2; omega)
            have hp_ge : base + 64 ≤ a := by
              unfold dualPSrc at h1; split_ifs at h1 <;>
                (dsimp only [hdrPBase0, hdrPBase1] at h1; clear *- h1; omega)
            exact hout_t a (by dsimp only [hdrCur]; clear *- hp_ge; omega)
              (by dsimp only [metaDst]; split_ifs <;> (clear *- hp_lt; omega)))
          (fun a ha => by
            have ha_r := slotOwnsNonPageMeta_src_range hcap_s (fun _ => hd_pos.ne') ha
            have ha48 : base + 48 ≤ a := by
              rcases ha_r with ⟨h1, _⟩ | h192
              · clear *- h1; omega
              · clear *- h192; omega
            exact hout_t a (by dsimp only [hdrCur]; clear *- ha48; omega)
              (hdisj_src_meta a ha))
          (fun a ha => by
            simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
              ↓reduceIte] at ha
            have ha1 := ha.1
            exact hout_t a (by dsimp only [hdrCur]; clear *- ha1 hibHi_val; omega)
              (by clear *- ha1 hmd_end_lt; omega))
      refine hsl_t_fr.at_exact_frontier
        (by unfold dualPSrc; dsimp only [hiFr, hdrPBase0, hdrPBase1]
            split_ifs <;> (clear *- hibHi_val; omega))
        (by unfold dualMbSrc; rw [hcap_s]; unfold dualCapSrc
            by_cases hst0 : stg = 0
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [← hmSrc_eq]
              by_cases hs0 : nSrc = 0
              · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                clear *- hibHi_val; omega
              · rw [ite_eq_right hs0, ite_eq_right hs0]; dsimp only [hiFr]
                clear *- hmSrc_pad hibHi_val; omega
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [ite_eq_right hd_pos.ne', ← hmDst_eq]
              dsimp only [hiFr]; clear *- hibHi_val; omega)
        (by dsimp only [directSlotIo]; exact le_rfl)
    refine ⟨hpre_bg, hfr_tick, hwf_tick,
      fun addr hlt_b => hout_t addr (by dsimp only [hdrCur]; clear *- hlt_b; omega)
        (by dsimp only [metaDst]; split_ifs <;> (clear *- hlt_b; omega)), ?_⟩
    rw [ite_eq_left (by clear *- hp4; omega)]
    refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
        (fun ⟨h9, _⟩ => by rw [hp4] at h9; cases h9) rfl rfl, ?_,
      fun _ _ => by
        rw [ite_eq_left hlt_raw] at hmc_zm
        unfold bulkBatchWhp at hmc_zm hmc_zb
        unfold itemBatchWhp epochStepCost
        dsimp only [metaDst, stg, pad, mDst, cur] at hmc_zb
        clear *- hmc_bg hmc_zm hmc_zb; omega⟩
    refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
    · rw [hnS_t, hph_t, ite_eq_right (by decide : 4 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
    · rw [hph_t, ite_eq_right (by decide : ¬(4 < 2)), ite_eq_right (by decide : 4 ≠ 2),
        ite_eq_left (by decide : 4 ≤ 10), hibH_t, hqH_t, hfr_tick]
      refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
      exact
        { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
          wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, fun a => hwf_tick.2 a⟩
          base_fr := by dsimp only [hiFr]; clear *- hibHi_val; omega
          hdr := rootStaticHeader_congr hhdr fun off hoff =>
            hout_off off (by clear *- hoff; omega) (by dsimp only [hdrCur]; clear *- hoff; omega)
          live_eq := (hout_off hdrLive (by decide) (by decide)).trans hlive_eq
          live_le := hlive_le
          ph_le := by dsimp only; rw [hph_t]; decide
          stg_le := by dsimp only; rw [hst_t]; exact hstg_le
          mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
          cache_src := by
            dsimp only; rw [hnS_t]
            exact hostCacheValid_congr_mem hcache_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
          nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
          sched := by
            dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
            refine
              { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                nDst_zero := fun hz => absurd (hnD_t.symm.trans hz) hd_pos.ne'
                stg_one := fun h1 => by
                  dsimp only at h1 ⊢; rw [hnD_t, hph_t]
                  exact ⟨hd_pos, by decide, by decide⟩
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
                  have hib := hsched.ibLo_eq; rwa [ite_eq_left (by clear *- hp4; omega)] at hib
                qLo_eq := by
                  dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 4 < 10), hnS_t]
                  have hq := hsched.qLo_eq; rwa [ite_eq_left (by clear *- hp4; omega)] at hq
                ph1 := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
                ge2 := fun _ => by
                  dsimp only
                  rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                  refine ⟨hmDst_eq, hpad_eq, ?_, fun _ => ?_, hibHi_eq, hqHi_eq⟩
                  · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                      rw [Nat.add_assoc]
                      exact hout_off (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                  · exact ⟨(hout_off hdrLogN (by decide) (by decide)).trans hlog_e,
                      (hout_off hdrEll (by decide) (by decide)).trans hell_e,
                      (hout_off hdrPgB (by decide) (by decide)).trans hpg_e⟩
                ph2 := fun h2 => by dsimp only at h2; exact absurd (hph_t.symm.trans h2) (by decide)
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
                    and_self, ↓reduceIte]
                  have hrb := hrem_b.2.1
                  rw [hp4] at hrb
                  unfold remRebuildBudget futureRebuildBudget at hrb
                  dsimp only at hrb
                  simp only [show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide,
                    show (4 : ℕ) ≠ 3 by decide, le_rfl, show 4 ≤ 9 by decide,
                    and_self, ↓reduceIte] at hrb
                  have hdiv_c : (mDst - cur) / 1024 = (mDst - cur') / 1024 + 1 := by
                    have heq_c : mDst - cur = (mDst - cur') + 1024 := by
                      dsimp only [bulkBatchWhp] at hcur'_eq
                      clear *- hlt hcur'_eq; omega
                    rw [heq_c]; exact Nat.add_div_right _ (by decide : 0 < 1024)
                  dsimp only [mDst, cur] at hdiv_c
                  rw [hdiv_c] at hrb
                  have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                  dsimp only [nSrc] at hf2 ⊢
                  generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef at hrb hf2 ⊢
                  by_cases hst0 : s.mem (base + hdrStage) = 0
                  · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                      at hrb ⊢
                    clear *- hrb hf2; omega
                  · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                      at hrb ⊢
                    clear *- hrb hf2; omega }
          pad_fits := by
            dsimp only
            rw [hnS_t, hph_t, ite_eq_right (by decide : 4 ≠ 0), hnD_t]
            have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp4; omega)] at hp
          ph1_inv := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
          ph3_inv := fun h3 => by dsimp only at h3; exact absurd (hph_t.symm.trans h3) (by decide)
          ph4_inv := fun _ => by
            dsimp only
            have hmbD_t : dualMbDst base s_tick.mem = metaDst := by
              unfold dualMbDst
              rw [hph_t, ite_eq_left (by decide : 4 < 10), hnD_t, ite_eq_right hd_pos.ne',
                hst_t, hpad_t]
            rw [hnD_t, hcur_t, hmD_t, hmbD_t]
            refine ⟨hd_pos, hlt.le, fun off hoff => ?_⟩
            rw [hs_tick_eq]; dsimp only
            rw [Function.update_of_ne (by dsimp only [metaDst, hdrCur]; split_ifs <;> omega),
              hmem_zb]
            by_cases hge : cur ≤ off
            · rw [ite_eq_left ⟨by clear *- hge; omega, by clear *- hoff; omega⟩]
            · rw [ite_eq_right (by clear *- hge; omega), ← hmbDst_eq]
              exact hzero_pre off (Nat.lt_of_not_le hge)
          pDst_pre := fun _ hst_or _ => by
            dsimp only at hst_or ⊢
            have hst0 : stg = 0 := by
              rcases hst_or with h5 | hs0
              · exact absurd (hph_t.symm.trans h5) (by decide)
              · exact hst_t.symm.trans hs0
            have hmbD : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
              unfold dualMbDst
              simp only [hph_t, hp4, hnD_t, hst_t, hpad_t]; rfl
            have hpD : dualPDst base s_tick.mem = base + hdrPBase1 := by
              unfold dualPDst
              rw [hph_t, ite_eq_left (by decide : 4 < 10), hst_t, hst0, ite_eq_left rfl]
            have hpD_s : dualPDst base s.mem = base + hdrPBase1 := by
              unfold dualPDst
              rw [hp4, ite_eq_left (by decide : 4 < 10), ite_eq_left hst0]
            have hpt_s := h.pDst_pre ⟨by clear *- hp4; omega, by clear *- hp4; omega⟩
              (Or.inr hst0) hd_pos
            dsimp only at hpt_s; rw [hpD_s] at hpt_s
            rw [hnD_t, hmbD, hpD, hibH_t, hqH_t]
            exact fastParamTable_mask_congr hpt_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_off (hdrPBase1 + k) (by dsimp only [hdrPBase1]; clear *- hk; omega)
                (by dsimp only [hdrPBase1, hdrCur]; clear *- hk; omega)
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
              unfold dualCapSrc; rw [hst_t, hnS_t, hnD_t]
            rw [hcap_t, hph_t]
            refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
              dsimp only [L']
              have hl := hlen_s (by clear *- hp4; omega) hs_p
              simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
              exact hl⟩
            unfold activeSrcIo
            rw [ite_eq_right (by decide : ¬(4 < 3)), ite_eq_right (by decide : 4 ≠ 3),
              ite_eq_left (by decide : 4 < 8), hibH_t, hqH_t]
            exact hsl_hi
          sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; clear *- h67; omega
          sl_8 := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
          sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; clear *- h9; omega }
  · -- Completion (`cur' = mDst`): zeroes remainder, runs `optWriteStageBTableProg`, enters `ph = 5`
    have hcur'_eq : cur' = mDst := le_antisymm (min_le_left _ _) (Nat.le_of_not_lt hlt)
    have hlt_raw : ¬((Memory.spec 0).clientResult s
        (zeroWordsBatchProg (((metaDst, mDst), cur), bulkBatchWhp)) < mDst) := hres_zb ▸ hlt
    have hs1_zero : ∀ off < mDst, s1.mem (metaDst + off) = 0 := by
      intro off hoff
      rw [hmem_zb]
      by_cases hge : cur ≤ off
      · rw [ite_eq_left ⟨by clear *- hge; omega, by rw [hcur'_eq]; clear *- hoff; omega⟩]
      · rw [ite_eq_right (by clear *- hge; omega), ← hmbDst_eq]
        exact hzero_pre off (Nat.lt_of_not_le hge)
    set wlp := writeLargeParamTableProg
      ((base, base + hdrPBase0), ((nDst, base + 192),
        ((s.mem (base + hdrLogN), s.mem (base + hdrEll)), s.mem (base + hdrPgB))))
    set s2 := if stg = 0 then s1 else (Memory.spec 0).clientState s1 wlp
    let flB : FastEpochLayout := ⟨c, U, V, w, nDst, base + 192, base + hdrPBase0,
      directSlotIo w vB base ibHi qHi nLive⟩
    have hwlp_sp := writeLargeParamTableProg_spec (fl := flB) (s := s1)
      (Or.inl (by dsimp only [flB, hdrPBase0]; omega)) hth_d.1 hth_d.2 hw_pos hhdr_s1
    dsimp only [flB] at hwlp_sp
    rw [← hlog_e, ← hell_e, ← hpg_e] at hwlp_sp
    obtain ⟨_, hwlp_fr, hwlp_mc, hwlp_k48, hwlp_61, hwlp_62, hwlp_out⟩ := hwlp_sp
    have hfr_s2 : s2.frontier = s.frontier := by
      dsimp only [s2]; split_ifs
      · exact hfr_zb
      · exact hwlp_fr.trans hfr_zb
    have hs_tick_eq : s_tick =
        { mem := Function.update (Function.update s2.mem (base + hdrCur) 32) (base + hdrPhase) 5,
          frontier := s.frontier } := by
      rw [hst_bg, hst_zm, ite_eq_right hlt_raw, hfr_s2]
    have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
    have hout_s2_s1 : ∀ a,
        (stg ≠ 0 → ¬(base + hdrPBase0 ≤ a ∧ a < base + hdrPBase0 + 48 ∨
          a = base + hdrPBase0 + 61 ∨ a = base + hdrPBase0 + 62)) →
        s2.mem a = s1.mem a := by
      intro a hnot
      dsimp only [s2]
      by_cases hst0 : stg = 0
      · rw [ite_eq_left hst0]
      · rw [ite_eq_right hst0]; exact hwlp_out a (hnot hst0)
    have hout_off : ∀ off < 64, off ≠ hdrPhase → off ≠ hdrCur →
        s_tick.mem (base + off) = s.mem (base + off) := by
      intro off hoff hp hc
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (base_add_ne hp), Function.update_of_ne (base_add_ne hc),
        hout_s2_s1 (base + off) (fun _ => by dsimp only [hdrPBase0]; clear *- hoff; omega),
        hmem_zb, ite_eq_right (by dsimp only [metaDst]; split_ifs <;> (clear *- hoff; omega))]
    have hph_t : s_tick.mem (base + hdrPhase) = 5 := by
      rw [hs_tick_eq]; exact Function.update_self ..
    have hcur_t : s_tick.mem (base + hdrCur) = 32 := by
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = stg :=
      hout_off hdrStage (by decide) (by decide) (by decide)
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
    have hmbD_t : dualMbDst base s_tick.mem = metaDst := by
      unfold dualMbDst
      rw [hph_t, ite_eq_left (by decide : 5 < 10), hnD_t, ite_eq_right hd_pos.ne', hst_t, hpad_t]
    have hpD_t_val : dualPDst base s_tick.mem =
        (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) := by
      unfold dualPDst; rw [hph_t, ite_eq_left (by decide : 5 < 10), hst_t]
    have hpDst_pt :
        ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := metaDst,
           pBase := dualPDst base s_tick.mem,
           io := directSlotIo w vB base ibHi qHi nLive } : FastEpochLayout).ParamTable
          (dualPh5MaskMem V w base (dualPDst base s_tick.mem) ibHi qHi nLive s_tick.mem) := by
      rw [hpD_t_val]
      by_cases hst0 : stg = 0
      · rw [ite_eq_left hst0]
        have hmd_eq : metaDst = base + 192 + pad := ite_eq_left hst0
        have hpD_s : dualPDst base s.mem = base + hdrPBase1 := by
          unfold dualPDst; rw [hp4, ite_eq_left (by decide : 4 < 10), ite_eq_left hst0]
        have hpt_s := h.pDst_pre ⟨by clear *- hp4; omega, by clear *- hp4; omega⟩
          (Or.inr hst0) hd_pos
        dsimp only at hpt_s; rw [hpD_s, hmbDst_eq] at hpt_s
        exact fastParamTable_mask_congr hpt_s fun k hk => by
          rw [hs_tick_eq]; dsimp only
          rw [Function.update_of_ne (by dsimp only [hdrPBase1, hdrPhase]; clear *- hk; omega),
            Function.update_of_ne (by dsimp only [hdrPBase1, hdrCur]; clear *- hk; omega),
            hout_s2_s1 _ (fun hne => absurd hst0 hne), hmem_zb,
            ite_eq_right (by dsimp only [hdrPBase1]; clear *- hk hmd_eq; omega)]
      · rw [ite_eq_right hst0]
        have hmd_eq : metaDst = base + 192 := ite_eq_right hst0
        rw [hmd_eq, dualPh5MaskMem_eq_setSlotIo]
        have hs2_eq : s2 = (Memory.spec 0).clientState s1 wlp := ite_eq_right hst0
        refine paramTable_of_writeLarge_and_setSlotIo (fl := flB)
          (fun k hk => by
            rw [hs_tick_eq]; dsimp only [flB]
            rw [Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; clear *- hk; omega),
              Function.update_of_ne (by dsimp only [hdrPBase0, hdrCur]; clear *- hk; omega),
              hs2_eq]
            exact hwlp_k48 k hk)
          (by
            rw [hs_tick_eq]; dsimp only [flB]
            rw [Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; omega),
              Function.update_of_ne (by dsimp only [hdrPBase0, hdrCur]; omega), hs2_eq]
            exact hwlp_61)
          (by
            rw [hs_tick_eq]; dsimp only [flB]
            rw [Function.update_of_ne (by dsimp only [hdrPBase0, hdrPhase]; omega),
              Function.update_of_ne (by dsimp only [hdrPBase0, hdrCur]; omega), hs2_eq]
            exact hwlp_62)
    have hpDst_31 : s_tick.mem (dualPDst base s_tick.mem + 31) = offBktMeta c w nDst := by
      have h31 := hpDst_pt 31 (by decide)
      dsimp only [FastEpochLayout.paramWord] at h31
      unfold dualPh5MaskMem at h31
      iterate 13 rw [Function.update_of_ne (by omega)] at h31
      exact h31
    have hzero_t : ∀ off < mDst, s_tick.mem (metaDst + off) = 0 := by
      intro off hoff
      have ha192 : base + 192 ≤ metaDst + off := by
        dsimp only [metaDst]; split_ifs <;> omega
      rw [hs_tick_eq]; dsimp only
      rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- ha192; omega),
        Function.update_of_ne (by dsimp only [hdrCur]; clear *- ha192; omega),
        hout_s2_s1 _ (fun _ => by dsimp only [hdrPBase0]; clear *- ha192; omega)]
      exact hs1_zero off hoff
    have hsl_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
        (dualMbSrc base s_tick.mem) (directSlotIo w vB base ibHi qHi nLive) 0 false
        L.slotSrc s_tick.mem := by
      have hpS_t : dualPSrc base s_tick.mem = dualPSrc base s.mem := by
        unfold dualPSrc; rw [hst_t]
      have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
        unfold dualMbSrc; rw [hst_t, hnS_t, hpad_t]
      rw [hpS_t, hmS_mb]
      have hsl_t_fr : EpochSlotInv c U V w s.frontier (dualPSrc base s.mem)
          (dualMbSrc base s.mem) (directSlotIo w vB base ibHi qHi nLive) 0 false
          L.slotSrc s_tick.mem :=
        hsl_s.congr_mem
          (fun a h1 h2 => by
            rw [hs_tick_eq]; dsimp only
            by_cases hst0 : stg = 0
            · unfold dualPSrc at h1 h2; rw [ite_eq_left hst0] at h1 h2
              rw [Function.update_of_ne
                  (by dsimp only [hdrPBase0, hdrPhase] at h1 ⊢; clear *- h1; omega),
                Function.update_of_ne
                  (by dsimp only [hdrPBase0, hdrCur] at h1 ⊢; clear *- h1; omega),
                hout_s2_s1 a (fun hne => absurd hst0 hne), hmem_zb,
                ite_eq_right (by
                  dsimp only [hdrPBase0, metaDst] at h2 ⊢
                  rw [ite_eq_left hst0]; clear *- h2; omega)]
            · unfold dualPSrc at h1 h2; rw [ite_eq_right hst0] at h1 h2
              rw [Function.update_of_ne
                  (by dsimp only [hdrPBase1, hdrPhase] at h1 ⊢; clear *- h1; omega),
                Function.update_of_ne
                  (by dsimp only [hdrPBase1, hdrCur] at h1 ⊢; clear *- h1; omega),
                hout_s2_s1 a (fun _ => by
                  dsimp only [hdrPBase0, hdrPBase1] at h1 ⊢; clear *- h1; omega),
                hmem_zb,
                ite_eq_right (by
                  dsimp only [hdrPBase1, metaDst] at h2 ⊢
                  rw [ite_eq_right hst0]; clear *- h2; omega)])
          (fun a ha => by
            have ha_b := slotOwnsNonPageMeta_src_range hcap_s (fun _ => hd_pos.ne') ha
            have hnot_md := hdisj_src_meta a ha
            have hc_le : cur' ≤ mDst := min_le_left _ _
            rw [hs_tick_eq]; dsimp only
            rcases ha_b with ⟨h1, h2⟩ | h192
            · rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- h1; omega),
                Function.update_of_ne (by dsimp only [hdrCur]; clear *- h1; omega),
                hout_s2_s1 a (fun _ => by dsimp only [hdrPBase0]; clear *- h2; omega),
                hmem_zb, ite_eq_right (by clear *- hnot_md hc_le; omega)]
            · rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- h192; omega),
                Function.update_of_ne (by dsimp only [hdrCur]; clear *- h192; omega),
                hout_s2_s1 a (fun _ => by dsimp only [hdrPBase0]; clear *- h192; omega),
                hmem_zb, ite_eq_right (by clear *- hnot_md hc_le; omega)])
          (fun a ha => by
            simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
              ↓reduceIte] at ha
            have ha1 := ha.1
            have hc_le : cur' ≤ mDst := min_le_left _ _
            rw [hs_tick_eq]; dsimp only
            rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- ha1 hibHi_val; omega),
              Function.update_of_ne (by dsimp only [hdrCur]; clear *- ha1 hibHi_val; omega),
              hout_s2_s1 a (fun _ => by dsimp only [hdrPBase0]; clear *- ha1 hibHi_val; omega),
              hmem_zb, ite_eq_right (by clear *- ha1 hmd_end_lt hc_le; omega)])
      refine hsl_t_fr.at_exact_frontier
        (by unfold dualPSrc; dsimp only [hiFr, hdrPBase0, hdrPBase1]
            split_ifs <;> (clear *- hibHi_val; omega))
        (by unfold dualMbSrc; rw [hcap_s]; unfold dualCapSrc
            by_cases hst0 : stg = 0
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [← hmSrc_eq]
              by_cases hs0 : nSrc = 0
              · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                clear *- hibHi_val; omega
              · rw [ite_eq_right hs0, ite_eq_right hs0]; dsimp only [hiFr]
                clear *- hmSrc_pad hibHi_val; omega
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [ite_eq_right hd_pos.ne', ← hmDst_eq]
              dsimp only [hiFr]; clear *- hibHi_val; omega)
        (by dsimp only [directSlotIo]; exact le_rfl)
    refine ⟨hpre_bg, hfr_tick, hwf_tick,
      fun addr hlt_b => by
        rw [hs_tick_eq]; dsimp only
        rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- hlt_b; omega),
          Function.update_of_ne (by dsimp only [hdrCur]; clear *- hlt_b; omega),
          hout_s2_s1 addr (fun _ => by dsimp only [hdrPBase0]; clear *- hlt_b; omega),
          hmem_zb, ite_eq_right (by dsimp only [metaDst]; split_ifs <;> (clear *- hlt_b; omega))],
      ?_⟩
    rw [ite_eq_left (by clear *- hp4; omega)]
    refine ⟨hres_bg, L', preservesEpochSeeds_of_eq_slots
        (fun ⟨h9, _⟩ => by rw [hp4] at h9; cases h9) rfl rfl, ?_,
      fun _ _ => by
        rw [ite_eq_right hlt_raw] at hmc_zm
        dsimp only [metaDst, stg, pad, mDst, cur, s1, wlp, nDst] at hmc_zm hmc_zb hwlp_mc
        unfold bulkBatchWhp at hmc_zm hmc_zb hwlp_mc
        unfold itemBatchWhp epochStepCost
        by_cases hst0 : s.mem (base + hdrStage) = 0
        · simp only [hst0, ↓reduceIte] at hmc_zm hmc_zb
          clear *- hmc_bg hmc_zm hmc_zb; omega
        · simp only [hst0, ↓reduceIte] at hmc_zm hmc_zb hwlp_mc
          clear *- hmc_bg hmc_zm hmc_zb hwlp_mc; omega⟩
    have hoff32_bm : 32 < offBktMeta c w nDst := by
      have hsp := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
        (bCharWhp nDst) (bWhp nDst)
      have heq_fp : 32 + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c)
          (bCharWhp nDst) (bWhp nDst) = offFpHash c w nDst := rfl
      clear *- hsp heq_fp hoffFp_bm; omega
    refine ⟨hwf_tick, ?_, fun _ => by rw [hcur_t, hpDst_31]; exact hoff32_bm, ?_⟩
    · rw [hnS_t, hph_t, ite_eq_right (by decide : 5 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
    · rw [hph_t, ite_eq_right (by decide : ¬(5 < 2)), ite_eq_right (by decide : 5 ≠ 2),
        ite_eq_left (by decide : 5 ≤ 10), hibH_t, hqH_t, hfr_tick]
      refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
      exact
        { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
          wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, fun a => hwf_tick.2 a⟩
          base_fr := by dsimp only [hiFr]; clear *- hibHi_val; omega
          hdr := rootStaticHeader_congr hhdr fun off hoff =>
            hout_off off (by clear *- hoff; omega)
              (by dsimp only [hdrPhase]; clear *- hoff; omega)
              (by dsimp only [hdrCur]; clear *- hoff; omega)
          live_eq := (hout_off hdrLive (by decide) (by decide) (by decide)).trans hlive_eq
          live_le := hlive_le
          ph_le := by dsimp only; rw [hph_t]; decide
          stg_le := by dsimp only; rw [hst_t]; exact hstg_le
          mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
          cache_src := by
            dsimp only; rw [hnS_t]
            exact hostCacheValid_congr_mem hcache_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
          nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
          sched := by
            dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
            refine
              { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                nDst_zero := fun hz => absurd (hnD_t.symm.trans hz) hd_pos.ne'
                stg_one := fun _ => by
                  dsimp only; rw [hnD_t, hph_t]; exact ⟨hd_pos, by decide, by decide⟩
                post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
                trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                drift_hi := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                drift_lo := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                ibLo_eq := by
                  dsimp only; rw [hibL_t, hph_t, ite_eq_left (by decide : 5 < 10), hmS_t]
                  have hib := hsched.ibLo_eq; rwa [ite_eq_left (by clear *- hp4; omega)] at hib
                qLo_eq := by
                  dsimp only; rw [hqL_t, hph_t, ite_eq_left (by decide : 5 < 10), hnS_t]
                  have hq := hsched.qLo_eq; rwa [ite_eq_left (by clear *- hp4; omega)] at hq
                ph1 := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
                ge2 := fun _ => by
                  dsimp only
                  rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                  refine ⟨hmDst_eq, hpad_eq, ?_, fun _ => ?_, hibHi_eq, hqHi_eq⟩
                  · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                      rw [Nat.add_assoc]
                      exact hout_off (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                  · exact ⟨(hout_off hdrLogN (by decide) (by decide) (by decide)).trans hlog_e,
                      (hout_off hdrEll (by decide) (by decide) (by decide)).trans hell_e,
                      (hout_off hdrPgB (by decide) (by decide) (by decide)).trans hpg_e⟩
                ph2 := fun h2 => by dsimp only at h2; exact absurd (hph_t.symm.trans h2) (by decide)
                ph3_10 := fun _ => by
                  dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                ph11 := fun h11 => by
                  dsimp only at h11; exact absurd (hph_t.symm.trans h11) (by decide)
                budget := by
                  dsimp only [L']
                  rw [hnS_t, hst_t, hph_t, hnD_t, ite_eq_left hd_pos, hcur_t]
                  unfold remRebuildBudget futureRebuildBudget
                  dsimp only
                  simp only [show (5 : ℕ) ≠ 1 by decide, show (5 : ℕ) ≠ 2 by decide,
                    show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
                    show 4 ≤ 5 by decide, show 5 ≤ 9 by decide, and_self, ↓reduceIte]
                  have hrb := hrem_b.2.1
                  rw [hp4] at hrb
                  unfold remRebuildBudget futureRebuildBudget at hrb
                  dsimp only at hrb
                  simp only [show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide,
                    show (4 : ℕ) ≠ 3 by decide, le_rfl, show 4 ≤ 9 by decide,
                    and_self, ↓reduceIte] at hrb
                  have hd_hi' : nLive ≤ L.nTrig + (L.elapsed + 1) := by
                    have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                  have hd_lo' : L.nTrig ≤ nLive + (L.elapsed + 1) := by
                    have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                  have hel_le' : 16 * (L.elapsed + 1) ≤ max (whpThreshold c) nSrc := by
                    have hel := hrem_b.2.2; clear *- hel; omega
                  have hnD_2R := (active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap
                    hd_hi' hd_lo' hel_le' hlive_le).1
                  have hnDst_w : nDst < 2 ^ w := lt_of_le_of_lt hth_d.2 hUw
                  have hbm_le : offBktMeta c w nDst - 32 ≤
                      2 * max (whpThreshold c) nSrc + 512 := by
                    have h1 : offBktMeta c w nDst ≤ epochMetaWordsWhp c w nDst :=
                      hoffBm_od.trans hoffOd_m
                    have h2 := epochMetaWordsWhp_le_self (w := w) hth_d.1 hnDst_w
                    generalize max (whpThreshold c) nSrc = nRef at hnD_2R ⊢
                    clear *- h1 h2 hnD_2R; omega
                  have hdiv_bm := Nat.div_le_div_right (c := 1024) hbm_le
                  have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                  dsimp only [nDst, nSrc] at hdiv_bm hf2 ⊢
                  generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef
                    at hrb hdiv_bm hf2 ⊢
                  by_cases hst0 : s.mem (base + hdrStage) = 0
                  · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                      at hrb ⊢
                    clear *- hrb hdiv_bm hf2; omega
                  · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                      at hrb ⊢
                    clear *- hrb hdiv_bm hf2; omega }
          pad_fits := by
            dsimp only
            rw [hnS_t, hph_t, ite_eq_right (by decide : 5 ≠ 0), hnD_t]
            have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp4; omega)] at hp
          ph1_inv := fun h1 => by dsimp only at h1; exact absurd (hph_t.symm.trans h1) (by decide)
          ph3_inv := fun h3 => by dsimp only at h3; exact absurd (hph_t.symm.trans h3) (by decide)
          ph4_inv := fun h4 => by dsimp only at h4; exact absurd (hph_t.symm.trans h4) (by decide)
          pDst_pre := fun _ _ _ => by
            dsimp only; rw [hnD_t, hmbD_t, hibH_t, hqH_t]; exact hpDst_pt
          ph5_inv := fun _ => by
            dsimp only; rw [hnD_t, hmbD_t, hibH_t, hqH_t, hcur_t]
            refine ⟨hd_pos, le_rfl, hoff32_bm.le, hpDst_pt,
              fun k _ hk => hzero_t k (by clear *- hk hm32; omega),
              fun off _ hoff => hzero_t off (hoff.trans_le (hoffOd_m.trans hmDst_eq.symm.le))⟩
          ph6_inv := fun h6 => by dsimp only at h6; exact absurd (hph_t.symm.trans h6) (by decide)
          ph7_inv := fun h7 => by dsimp only at h7; exact absurd (hph_t.symm.trans h7) (by decide)
          ph8_inv := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
          ph9_inv := fun h9 => by dsimp only at h9; exact absurd (hph_t.symm.trans h9) (by decide)
          ph10_inv := fun h10 => by
            dsimp only at h10; exact absurd (hph_t.symm.trans h10) (by decide)
          sl_le7 := fun _ => by
            dsimp only
            have hcap_t : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
              unfold dualCapSrc; rw [hst_t, hnS_t, hnD_t]
            rw [hcap_t, hph_t]
            refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
              dsimp only [L']
              have hl := hlen_s (by clear *- hp4; omega) hs_p
              simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
              exact hl⟩
            unfold activeSrcIo
            rw [ite_eq_right (by decide : ¬(5 < 3)), ite_eq_right (by decide : 5 ≠ 3),
              ite_eq_left (by decide : 5 < 8), hibH_t, hqH_t]
            exact hsl_hi
          sl_67 := fun h67 => by dsimp only at h67; rw [hph_t] at h67; clear *- h67; omega
          sl_8 := fun h8 => by dsimp only at h8; exact absurd (hph_t.symm.trans h8) (by decide)
          sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_t] at h9; clear *- h9; omega }

/-! ## Section 5: Phase `5` (`tickRandPrepProg`) Specification -/

/-- Phase `5` (`randFill`) background tick specification. -/
theorem tickPhase5_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp5 : s.mem (base + hdrPhase) = 5) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb192 := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hstg_le := h.stg_le
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp5; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_mid⟩ := hsched.ph3_10 ⟨by clear *- hp5; omega, by clear *- hp5; omega⟩
  simp only [↓reduceIte] at hfr_hi_mid
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hlog_d, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp5; omega)
  obtain ⟨_, hvb_w, _, hqHi_w, _, hpad_hi_s, _, _⟩ := dualCoreInv_ib_fits h
  rw [ite_eq_right (by clear *- hp5; omega)] at hpad_hi_s
  obtain ⟨hd_pos, hcur_ge32, hcur_le_bm, hpt_s, hz_hdr, hz_post⟩ := h.ph5_inv hp5
  have hth_d : whpThreshold c ≤ s.mem (base + hdrNDst) ∧ s.mem (base + hdrNDst) ≤ U := by
    rcases hsched.nDst_bounds with hz | hb
    · exact absurd hz hd_pos.ne'
    · exact hb
  obtain ⟨_, _, hoffBm_od, hoffOd_m⟩ := epochMeta_offsets_le (w := w) hth_d.1
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hw_eq : s.mem (base + hdrW) = w := hhdr.2.2.1
  set nLive := (Dictionary.dom s_dict).card
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set cur := s.mem (base + hdrCur)
  set ibLo := s.mem (base + hdrItemLo)
  set qLo := s.mem (base + hdrQLo)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set offBM := offBktMeta c w nDst
  set pDst := dualPDst base s.mem
  set metaDst := dualMbDst base s.mem
  have hpDst_if : pDst = (if stg = 0 then base + hdrPBase1 else base + hdrPBase0) := by
    dsimp only [pDst]; unfold dualPDst; rw [hp5, ite_eq_left (by decide : 5 < 10)]
  have hmetaDst_if : metaDst = (if stg = 0 then base + 192 + pad else base + 192) := by
    dsimp only [metaDst]; unfold dualMbDst
    rw [hp5, ite_eq_left (by decide : 5 < 10), ite_eq_right hd_pos.ne']
  have hpDst_31 : s.mem (pDst + 31) = offBM := by
    have h31 := hpt_s 31 (by decide)
    dsimp only [FastEpochLayout.paramWord] at h31
    unfold dualPh5MaskMem at h31
    iterate 13 rw [Function.update_of_ne (by omega)] at h31
    exact h31
  have hibHi_val : ibHi = base + 192 + pad + mDst + 4 := by
    rw [hibHi_eq, ite_eq_right hd_pos.ne']
  have hmDst_pad : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
  have hmSrc_pad : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
  have hbm_le_m : offBM ≤ mDst := (hoffBm_od.trans hoffOd_m).trans hmDst_eq.symm.le
  have hmd_end_lt : metaDst + mDst < ibHi := by
    rw [hmetaDst_if]; split_ifs <;> (clear *- hibHi_val hmDst_pad; omega)
  have hmd_bm_fr : metaDst + offBM ≤ s.frontier :=
    (Nat.add_le_add_left hbm_le_m metaDst).trans
      ((hmd_end_lt.le.trans (Nat.le_add_right _ _)).trans hfr_hi_lo)
  have hpre_rp : TickRandPrepPre w base s := by
    refine ⟨hw11, hw_eq, hb192, ?_⟩
    dsimp only
    rw [← hpDst_if, ← hmetaDst_if, hpDst_31]
    exact ⟨hcur_le_bm, hmd_bm_fr⟩
  have hpre_bg : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb192; omega, ?_⟩
    dsimp only
    iterate 5 rw [ite_eq_right (by clear *- hp5; omega)]
    rw [ite_eq_left hp5]
    exact hpre_rp
  have hbgev := bgTickProg_eval base s.frontier s
  dsimp only at hbgev
  simp only [hp5, show (5 : ℕ) ≠ 0 by decide, show (5 : ℕ) ≠ 1 by decide,
    show (5 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 3 by decide,
    show (5 : ℕ) ≠ 4 by decide, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  obtain ⟨hst_rp, hres_rp, hmc_rp⟩ := tickRandPrepProg_eval base s
  dsimp only at hst_rp hres_rp
  rw [← hpDst_if, hpDst_31] at hst_rp
  rw [← hpDst_if, ← hmetaDst_if, hpDst_31, hw_eq] at hres_rp
  set endOff := cur + min bulkBatchWhp (offBM - cur)
  set s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
  have hs_tick_eq : s_tick =
      { mem := Function.update s.mem (base + hdrCur) endOff, frontier := s.frontier } :=
    hst_bg.trans hst_rp
  have hwf_tick : Memory.WellFormed w s_tick :=
    wf_step hwf (validHistory_bgTickProg hwf hpre_bg)
  have hfr_tick : s_tick.frontier = s.frontier := by rw [hs_tick_eq]
  have hmask_eq : (((1 : ℕ) <<< (w - 1)) - 1) * 2 + 1 = 2 ^ w - 1 := by
    rw [shift_one_eq]
    have hp1 : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
    have hpow : 2 ^ (w - 1) * 2 = 2 ^ w := by
      rw [← Nat.pow_succ, show (w - 1).succ = w by clear *- hw11; omega]
    clear *- hp1 hpow; omega
  have hrArgs_eq : (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier)) =
      (metaDst + cur, (metaDst + endOff, 2 ^ w - 1)) := by
    rw [hres_bg, hres_rp, hmask_eq]
  have hend_le_bm : endOff ≤ offBM := by dsimp only [endOff]; clear *- hcur_le_bm; omega
  have hend_fr : metaDst + endOff ≤ s_tick.frontier := by
    rw [hfr_tick]; exact (Nat.add_le_add_left hend_le_bm metaDst).trans hmd_bm_fr
  have hpw2 := pairStreamWords_succ_le_add_two (n := nLive) hw_pos
    (show qHi + vB ≤ 2 * w by clear *- hqHi_w hvb_w; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    unfold bulkBatchWhp; clear *- hfr_hi_mid hpw2; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive :=
    hfr_hi_mid.trans hpad_hi_s
  obtain ⟨hcap_s, hdict_s, hsl_s, hlen_s⟩ := h.sl_le7 (by clear *- hp5; omega)
  have hio_s : activeSrcIo c w vB base stg (s.mem (base + hdrPhase))
      nSrc nDst pad ibLo qLo ibHi qHi nLive = directSlotIo w vB base ibHi qHi nLive := by
    unfold activeSrcIo
    rw [ite_eq_right (by clear *- hp5; omega), ite_eq_right (by clear *- hp5; omega),
      ite_eq_left (by clear *- hp5; omega)]
  rw [hio_s] at hsl_s
  have hdisj_src_rand : ∀ a, slotOwnsNonPageMeta c w (dualMbSrc base s.mem) L.slotSrc.nCap a →
      ¬(metaDst + cur ≤ a ∧ a < metaDst + cur + (endOff - cur)) := by
    intro a ha hr
    unfold slotOwnsNonPageMeta dualMbSrc at ha
    rw [hcap_s] at ha; unfold dualCapSrc at ha
    by_cases hst0 : stg = 0
    · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
      have hmd_eq : metaDst = base + 192 + pad := by rw [hmetaDst_if, ite_eq_left hst0]
      by_cases hs0 : nSrc = 0
      · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte,
          ne_eq, not_true_eq_false, false_and, or_false] at ha
        dsimp only [hdrSmallMeta0] at ha
        clear *- ha hr hmd_eq; omega
      · have hth_s : whpThreshold c ≤ nSrc := by
          rcases hnSrc_b with hz | ⟨hth, _⟩
          · exact absurd hz hs0
          · exact hth
        have hod_le : offPageDir c w nSrc ≤ mSrc :=
          (epochMeta_offsets_le hth_s).2.2.2.trans hmSrc_eq.symm.le
        have hmS_ge : 32 ≤ mSrc :=
          (epochMeta_offsets_le hth_s).1.trans
            ((epochMeta_offsets_le hth_s).2.1.trans
              ((epochMeta_offsets_le hth_s).2.2.1.trans hod_le))
        simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte] at ha
        dsimp only [mSrc, pad] at ha hmSrc_pad hod_le hmS_ge hr hmd_eq
        rcases ha with ⟨h1, h2⟩ | ⟨_, h1, h2⟩
        · clear *- h1 h2 hmS_ge hmSrc_pad hr hmd_eq; omega
        · clear *- h1 h2 hod_le hmSrc_pad hr hmd_eq; omega
    · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
      have hmd_eq : metaDst = base + 192 := by rw [hmetaDst_if, ite_eq_right hst0]
      dsimp only [pad, mDst, offBM] at ha hend_le_bm hbm_le_m hmDst_pad hr
      rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;>
        (clear *- h1 hend_le_bm hbm_le_m hmDst_pad hr hmd_eq; omega)
  have hrem_b := hsched.budget
  dsimp only at hrem_b
  refine ⟨hpre_bg, hfr_tick, hwf_tick,
    fun addr hlt_b => by
      rw [hs_tick_eq]; exact Function.update_of_ne (by dsimp only [hdrCur]; clear *- hlt_b; omega)
        _ _,
    ?_⟩
  rw [ite_eq_right (not_not.mpr hp5)]
  refine ⟨hd_pos, hcur_ge32, Nat.le_add_right _ _, hend_le_bm,
    by dsimp only [endOff, bulkBatchWhp]; omega, hrArgs_eq, hend_fr,
    by clear *- hmc_bg hmc_rp; omega,
    fun off _ _ => by
      rw [hs_tick_eq]
      refine Function.update_of_ne ?_ _ _
      change metaDst + off ≠ base + hdrCur
      rw [hmetaDst_if]; dsimp only [hdrCur]; split_ifs <;> omega,
    fun words => ?_⟩
  set s_rand : Memory.State :=
    { mem := writeWords s_tick.mem (metaDst + cur) words, frontier := s_tick.frontier }
  have hwf_rand : Memory.WellFormed w s_rand := by
    refine ⟨hwf_tick.1, fun a => ?_⟩
    dsimp only [s_rand]; unfold writeWords
    by_cases hin : metaDst + cur ≤ a ∧ a < metaDst + cur + (endOff - cur)
    · rw [dite_eq_left hin]; exact (words _).isLt
    · rw [dite_eq_right hin]; exact hwf_tick.2 a
  have hout_r : ∀ a, a ≠ base + hdrCur →
      ¬(metaDst + cur ≤ a ∧ a < metaDst + cur + (endOff - cur)) →
      s_rand.mem a = s.mem a := by
    intro a hc hin
    dsimp only [s_rand]
    rw [writeWords_apply_out _ _ _ hin, hs_tick_eq]
    exact Function.update_of_ne hc _ _
  have hout_off : ∀ off < 192, off ≠ hdrCur → s_rand.mem (base + off) = s.mem (base + off) :=
    fun off hoff hc =>
      hout_r (base + off) (base_add_ne hc)
        (by rw [hmetaDst_if]; split_ifs <;> (clear *- hoff; omega))
  have hph_r : s_rand.mem (base + hdrPhase) = 5 :=
    (hout_off hdrPhase (by decide) (by decide)).trans hp5
  have hst_r : s_rand.mem (base + hdrStage) = stg :=
    hout_off hdrStage (by decide) (by decide)
  have hcur_r : s_rand.mem (base + hdrCur) = endOff := by
    dsimp only [s_rand]
    rw [writeWords_apply_out _ _ _
      (by rw [hmetaDst_if]; dsimp only [hdrCur]; split_ifs <;> omega), hs_tick_eq]
    exact Function.update_self ..
  have hnS_r : s_rand.mem (base + hdrNSrc) = nSrc :=
    hout_off hdrNSrc (by decide) (by decide)
  have hnD_r : s_rand.mem (base + hdrNDst) = nDst :=
    hout_off hdrNDst (by decide) (by decide)
  have hmS_r : s_rand.mem (base + hdrMSrc) = mSrc :=
    hout_off hdrMSrc (by decide) (by decide)
  have hmD_r : s_rand.mem (base + hdrMDst) = mDst :=
    hout_off hdrMDst (by decide) (by decide)
  have hpad_r : s_rand.mem (base + hdrPad) = pad :=
    hout_off hdrPad (by decide) (by decide)
  have hibL_r : s_rand.mem (base + hdrItemLo) = ibLo :=
    hout_off hdrItemLo (by decide) (by decide)
  have hibH_r : s_rand.mem (base + hdrItemHi) = ibHi :=
    hout_off hdrItemHi (by decide) (by decide)
  have hqL_r : s_rand.mem (base + hdrQLo) = qLo :=
    hout_off hdrQLo (by decide) (by decide)
  have hqH_r : s_rand.mem (base + hdrQHi) = qHi :=
    hout_off hdrQHi (by decide) (by decide)
  have hpD_r : dualPDst base s_rand.mem = pDst := by
    dsimp only [pDst]; unfold dualPDst; simp only [hph_r, hp5, hst_r]; rfl
  have hmbD_r : dualMbDst base s_rand.mem = metaDst := by
    dsimp only [metaDst]; unfold dualMbDst
    simp only [hph_r, hp5, hnD_r, hst_r, hpad_r]; rfl
  have hpD31_r : s_rand.mem (pDst + 31) = offBM := by
    have hp_lt : pDst + 31 < base + 192 := by
      rw [hpDst_if]; dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega
    have hp_ge : base + 64 ≤ pDst + 31 := by
      rw [hpDst_if]; dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega
    exact (hout_r (pDst + 31) (by dsimp only [hdrCur]; clear *- hp_ge; omega)
      (by rw [hmetaDst_if]; split_ifs <;> (clear *- hp_lt; omega))).trans hpDst_31
  have hpt_r :
      ({ c := c, U := U, V := V, w := w, N := nDst, metaBase := metaDst, pBase := pDst,
         io := directSlotIo w vB base ibHi qHi nLive } : FastEpochLayout).ParamTable
        (dualPh5MaskMem V w base pDst ibHi qHi nLive s_rand.mem) :=
    fastParamTable_mask_congr hpt_s fun k hk => by
      have hp_lt : pDst + k < base + 192 := by
        rw [hpDst_if]; dsimp only [hdrPBase0, hdrPBase1]
        rcases hk with h48 | rfl | rfl
        · split_ifs <;> (clear *- h48; omega)
        · split_ifs <;> omega
        · split_ifs <;> omega
      have hp_ge : base + 64 ≤ pDst + k := by
        rw [hpDst_if]; dsimp only [hdrPBase0, hdrPBase1]; split_ifs <;> omega
      exact hout_r (pDst + k) (by dsimp only [hdrCur]; clear *- hp_ge; omega)
        (by rw [hmetaDst_if]; split_ifs <;> (clear *- hp_lt; omega))
  have hz_hdr_r : ∀ k, 1 ≤ k → k < 32 → s_rand.mem (metaDst + k) = 0 := fun k hk1 hk32 =>
    (hout_r (metaDst + k)
      (by rw [hmetaDst_if]; dsimp only [hdrCur]; split_ifs <;> (clear *- hk1; omega))
      (by clear *- hk32 hcur_ge32; omega)).trans (hz_hdr k hk1 hk32)
  have hz_post_r : ∀ off, offBM ≤ off → off < offPageDir c w nDst →
      s_rand.mem (metaDst + off) = 0 := fun off hlo hhi =>
    (hout_r (metaDst + off)
      (by rw [hmetaDst_if]; dsimp only [hdrCur]; split_ifs <;> omega)
      (by clear *- hlo hend_le_bm hcur_le_bm; omega)).trans (hz_post off hlo hhi)
  have hsl_r_fr : EpochSlotInv c U V w s.frontier (dualPSrc base s_rand.mem)
      (dualMbSrc base s_rand.mem) (directSlotIo w vB base ibHi qHi nLive) 0 false
      L.slotSrc s_rand.mem := by
    have hpS_r : dualPSrc base s_rand.mem = dualPSrc base s.mem := by
      unfold dualPSrc; rw [hst_r]
    have hmS_mb : dualMbSrc base s_rand.mem = dualMbSrc base s.mem := by
      unfold dualMbSrc; rw [hst_r, hnS_r, hpad_r]
    rw [hpS_r, hmS_mb]
    exact hsl_s.congr_mem
      (fun a h1 h2 => by
        have hp_lt : a < base + 192 := by
          unfold dualPSrc at h2; split_ifs at h2 <;>
            (dsimp only [hdrPBase0, hdrPBase1] at h2; clear *- h2; omega)
        have hp_ge : base + 64 ≤ a := by
          unfold dualPSrc at h1; split_ifs at h1 <;>
            (dsimp only [hdrPBase0, hdrPBase1] at h1; clear *- h1; omega)
        exact hout_r a (by dsimp only [hdrCur]; clear *- hp_ge; omega)
          (by rw [hmetaDst_if]; split_ifs <;> (clear *- hp_lt; omega)))
      (fun a ha => by
        have ha_r := slotOwnsNonPageMeta_src_range hcap_s (fun _ => hd_pos.ne') ha
        have ha48 : base + 48 ≤ a := by
          rcases ha_r with ⟨h1, _⟩ | h192
          · clear *- h1; omega
          · clear *- h192; omega
        exact hout_r a (by dsimp only [hdrCur]; clear *- ha48; omega)
          (hdisj_src_rand a ha))
      (fun a ha => by
        simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
          ↓reduceIte] at ha
        have ha1 := ha.1
        exact hout_r a (by dsimp only [hdrCur]; clear *- ha1 hibHi_val; omega)
          (by clear *- ha1 hend_le_bm hbm_le_m hmd_end_lt hcur_le_bm; omega))
  refine ⟨hwf_rand,
    fun addr hlt_b => hout_r addr (by dsimp only [hdrCur]; clear *- hlt_b; omega)
      (by rw [hmetaDst_if]; split_ifs <;> (clear *- hlt_b; omega)),
    hph_r, hst_r, hcur_r, hpD31_r, fun hlt_bm => ?_, fun heq_bm => ?_⟩
  · -- `endOff < offBM`: `DualPreShrinkInv` with `L.elapsed + 1`
    set L' : DualLatent c U V := { L with elapsed := L.elapsed + 1 }
    have hend_step : endOff = cur + bulkBatchWhp := by
      have hlt_bm' : endOff < offBM := hlt_bm
      dsimp only [endOff] at hlt_bm' ⊢
      rw [min_eq_left (by clear *- hlt_bm'; omega)]
    have hsl_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_rand.mem)
        (dualMbSrc base s_rand.mem) (directSlotIo w vB base ibHi qHi nLive) 0 false
        L.slotSrc s_rand.mem :=
      hsl_r_fr.at_exact_frontier
        (by unfold dualPSrc; dsimp only [hiFr, hdrPBase0, hdrPBase1]
            split_ifs <;> (clear *- hibHi_val; omega))
        (by unfold dualMbSrc; rw [hst_r, hnS_r, hpad_r, hcap_s]; unfold dualCapSrc
            by_cases hst0 : stg = 0
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [← hmSrc_eq]
              by_cases hs0 : nSrc = 0
              · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                clear *- hibHi_val; omega
              · rw [ite_eq_right hs0, ite_eq_right hs0]
                dsimp only [hiFr, mSrc, pad, mDst] at hmSrc_pad hibHi_val ⊢
                clear *- hmSrc_pad hibHi_val; omega
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [ite_eq_right hd_pos.ne', ← hmDst_eq]
              dsimp only [hiFr, pad, mDst] at hibHi_val ⊢
              clear *- hibHi_val; omega)
        (by dsimp only [directSlotIo]; exact le_rfl)
    have hfr_r : s_rand.frontier = s.frontier := hfr_tick
    refine ⟨hwf_rand, ?_, fun _ => by rw [hcur_r, hpD_r, hpD31_r]; exact hlt_bm, ?_⟩
    · rw [hnS_r, hph_r, ite_eq_right (by decide : 5 ≠ 0), hnD_r, hfr_r]
      exact hfr_le_pad
    · rw [hph_r, ite_eq_right (by decide : ¬(5 < 2)), ite_eq_right (by decide : 5 ≠ 2),
        ite_eq_left (by decide : 5 ≤ 10), hibH_r, hqH_r, hfr_r]
      refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
      exact
        { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
          wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, fun a => hwf_rand.2 a⟩
          base_fr := by dsimp only [hiFr]; clear *- hibHi_val; omega
          hdr := rootStaticHeader_congr hhdr fun off hoff =>
            hout_off off (by clear *- hoff; omega) (by dsimp only [hdrCur]; clear *- hoff; omega)
          live_eq := (hout_off hdrLive (by decide) (by decide)).trans hlive_eq
          live_le := hlive_le
          ph_le := by dsimp only; rw [hph_r]; decide
          stg_le := by dsimp only; rw [hst_r]; exact hstg_le
          mSrc_eq := by dsimp only; rw [hmS_r, hnS_r]; exact hmSrc_eq
          cache_src := by
            dsimp only; rw [hnS_r]
            exact hostCacheValid_congr_mem hcache_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
          nSrc_bounds := by dsimp only; rw [hnS_r]; exact hnSrc_b
          sched := by
            dsimp only; rw [ite_eq_right (by rw [hph_r]; decide)]
            refine
              { nDst_bounds := by dsimp only; rw [hnD_r]; exact hsched.nDst_bounds
                nDst_zero := fun hz => absurd (hnD_r.symm.trans hz) hd_pos.ne'
                stg_one := fun _ => by
                  dsimp only; rw [hnD_r, hph_r]; exact ⟨hd_pos, by decide, by decide⟩
                post_trig := by dsimp only [L']; rw [hnS_r]; exact hsched.post_trig
                trig_cap := by dsimp only [L']; rw [hnS_r, hnD_r]; exact hsched.trig_cap
                drift_hi := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_hi; simp only [↓reduceIte] at hd; exact hd
                drift_lo := by
                  dsimp only [L']; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  have hd := hsched.drift_lo; simp only [↓reduceIte] at hd; exact hd
                ibLo_eq := by
                  dsimp only; rw [hibL_r, hph_r, ite_eq_left (by decide : 5 < 10), hmS_r]
                  have hib := hsched.ibLo_eq; rwa [ite_eq_left (by clear *- hp5; omega)] at hib
                qLo_eq := by
                  dsimp only; rw [hqL_r, hph_r, ite_eq_left (by decide : 5 < 10), hnS_r]
                  have hq := hsched.qLo_eq; rwa [ite_eq_left (by clear *- hp5; omega)] at hq
                ph1 := fun h1 => by dsimp only at h1; exact absurd (hph_r.symm.trans h1) (by decide)
                ge2 := fun _ => by
                  dsimp only
                  rw [hmD_r, hnD_r, hpad_r, hmS_r, hibH_r, hqH_r, hnS_r]
                  obtain ⟨e1, e2, e3⟩ := hlog_d hd_pos
                  refine ⟨hmDst_eq, hpad_eq, ?_, fun _ => ?_, hibHi_eq, hqHi_eq⟩
                  · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                      rw [Nat.add_assoc]
                      exact hout_off (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                  · exact ⟨(hout_off hdrLogN (by decide) (by decide)).trans e1,
                      (hout_off hdrEll (by decide) (by decide)).trans e2,
                      (hout_off hdrPgB (by decide) (by decide)).trans e3⟩
                ph2 := fun h2 => by dsimp only at h2; exact absurd (hph_r.symm.trans h2) (by decide)
                ph3_10 := fun _ => by
                  dsimp only; simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  rw [hibH_r, hqH_r]; exact ⟨le_rfl, le_rfl⟩
                ph11 := fun h11 => by
                  dsimp only at h11; exact absurd (hph_r.symm.trans h11) (by decide)
                budget := by
                  dsimp only [L']
                  rw [hnS_r, hst_r, hph_r, hnD_r, ite_eq_left hd_pos, hcur_r]
                  unfold remRebuildBudget futureRebuildBudget
                  dsimp only
                  simp only [show (5 : ℕ) ≠ 1 by decide, show (5 : ℕ) ≠ 2 by decide,
                    show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
                    show 4 ≤ 5 by decide, show 5 ≤ 9 by decide, and_self, ↓reduceIte]
                  have hrb := hrem_b.2.1
                  rw [hp5, ite_eq_left hd_pos] at hrb
                  unfold remRebuildBudget futureRebuildBudget at hrb
                  dsimp only at hrb
                  simp only [show (5 : ℕ) ≠ 1 by decide, show (5 : ℕ) ≠ 2 by decide,
                    show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
                    show 4 ≤ 5 by decide, show 5 ≤ 9 by decide, and_self, ↓reduceIte] at hrb
                  have hdiv_c : (offBM - cur) / 1024 = (offBM - endOff) / 1024 + 1 := by
                    have heq_c : offBM - cur = (offBM - endOff) + 1024 := by
                      dsimp only [bulkBatchWhp] at hend_step
                      clear *- hlt_bm hend_step; omega
                    rw [heq_c]; exact Nat.add_div_right _ (by decide : 0 < 1024)
                  dsimp only [offBM, nDst, cur] at hdiv_c
                  rw [hdiv_c] at hrb
                  have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                  dsimp only [nDst, nSrc] at hf2 ⊢
                  generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef at hrb hf2 ⊢
                  by_cases hst0 : s.mem (base + hdrStage) = 0
                  · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                      at hrb ⊢
                    clear *- hrb hf2; omega
                  · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                      at hrb ⊢
                    clear *- hrb hf2; omega }
          pad_fits := by
            dsimp only
            rw [hnS_r, hph_r, ite_eq_right (by decide : 5 ≠ 0), hnD_r]
            have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp5; omega)] at hp
          ph1_inv := fun h1 => by dsimp only at h1; exact absurd (hph_r.symm.trans h1) (by decide)
          ph3_inv := fun h3 => by dsimp only at h3; exact absurd (hph_r.symm.trans h3) (by decide)
          ph4_inv := fun h4 => by dsimp only at h4; exact absurd (hph_r.symm.trans h4) (by decide)
          pDst_pre := fun _ _ _ => by
            dsimp only; rw [hnD_r, hmbD_r, hpD_r, hibH_r, hqH_r]; exact hpt_r
          ph5_inv := fun _ => by
            dsimp only; rw [hnD_r, hmbD_r, hpD_r, hibH_r, hqH_r, hcur_r]
            exact ⟨hd_pos, hcur_ge32.trans (Nat.le_add_right _ _), hend_le_bm, hpt_r,
              hz_hdr_r, hz_post_r⟩
          ph6_inv := fun h6 => by dsimp only at h6; exact absurd (hph_r.symm.trans h6) (by decide)
          ph7_inv := fun h7 => by dsimp only at h7; exact absurd (hph_r.symm.trans h7) (by decide)
          ph8_inv := fun h8 => by dsimp only at h8; exact absurd (hph_r.symm.trans h8) (by decide)
          ph9_inv := fun h9 => by dsimp only at h9; exact absurd (hph_r.symm.trans h9) (by decide)
          ph10_inv := fun h10 => by
            dsimp only at h10; exact absurd (hph_r.symm.trans h10) (by decide)
          sl_le7 := fun _ => by
            dsimp only
            have hcap_r : dualCapSrc base s_rand.mem = dualCapSrc base s.mem := by
              unfold dualCapSrc; rw [hst_r, hnS_r, hnD_r]
            rw [hcap_r, hph_r]
            refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => by
              dsimp only [L']
              have hl := hlen_s (by clear *- hp5; omega) hs_p
              simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hl ⊢
              exact hl⟩
            unfold activeSrcIo
            rw [ite_eq_right (by decide : ¬(5 < 3)), ite_eq_right (by decide : 5 ≠ 3),
              ite_eq_left (by decide : 5 < 8), hibH_r, hqH_r]
            exact hsl_hi
          sl_67 := fun h67 => by dsimp only at h67; rw [hph_r] at h67; clear *- h67; omega
          sl_8 := fun h8 => by dsimp only at h8; exact absurd (hph_r.symm.trans h8) (by decide)
          sl_ge9 := fun h9 => by dsimp only at h9; rw [hph_r] at h9; clear *- h9; omega }
  · -- `endOff = offBM`: `DualMidInv` on `s_rand` with `L` (feeding `finishRandFillProg`)
    have hfr_r : s_rand.frontier = s.frontier := hfr_tick
    have heq_bm' : endOff = offBktMeta c w nDst := heq_bm
    exact
      { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
        wf := hwf_rand
        base_fr := by rw [hfr_r]; exact hb192
        hdr := rootStaticHeader_congr hhdr fun off hoff =>
          hout_off off (by clear *- hoff; omega) (by dsimp only [hdrCur]; clear *- hoff; omega)
        live_eq := (hout_off hdrLive (by decide) (by decide)).trans hlive_eq
        live_le := hlive_le
        ph_le := by rw [hph_r]; decide
        stg_le := by rw [hst_r]; exact hstg_le
        mSrc_eq := by rw [hmS_r, hnS_r]; exact hmSrc_eq
        cache_src := by
          rw [hnS_r]
          exact hostCacheValid_congr_mem hcache_s fun k hk => by
            rw [Nat.add_assoc]
            exact hout_off (hdrSrcOd + k) (by dsimp only [hdrSrcOd]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
        nSrc_bounds := hnS_r.symm ▸ hnSrc_b
        sched := by
          rw [ite_eq_right (by rw [hph_r]; decide)]
          refine
            { nDst_bounds := hnD_r.symm ▸ hsched.nDst_bounds
              nDst_zero := fun hz => absurd (hnD_r.symm.trans hz) hd_pos.ne'
              stg_one := fun _ => by rw [hnD_r, hph_r]; exact ⟨hd_pos, by decide, by decide⟩
              post_trig := hnS_r.symm ▸ hsched.post_trig
              trig_cap := by rw [hnS_r, hnD_r]; exact hsched.trig_cap
              drift_hi := hsched.drift_hi
              drift_lo := hsched.drift_lo
              ibLo_eq := by
                rw [hibL_r, hph_r, ite_eq_left (by decide : 5 < 10), hmS_r]
                have hib := hsched.ibLo_eq; rwa [ite_eq_left (by clear *- hp5; omega)] at hib
              qLo_eq := by
                rw [hqL_r, hph_r, ite_eq_left (by decide : 5 < 10), hnS_r]
                have hq := hsched.qLo_eq; rwa [ite_eq_left (by clear *- hp5; omega)] at hq
              ph1 := fun h1 => absurd (hph_r.symm.trans h1) (by decide)
              ge2 := fun _ => by
                rw [hmD_r, hnD_r, hpad_r, hmS_r, hibH_r, hqH_r, hnS_r]
                obtain ⟨e1, e2, e3⟩ := hlog_d hd_pos
                refine ⟨hmDst_eq, hpad_eq, ?_, fun _ => ?_, hibHi_eq, hqHi_eq⟩
                · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                    rw [Nat.add_assoc]
                    exact hout_off (hdrDstOd + k) (by dsimp only [hdrDstOd]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                · exact ⟨(hout_off hdrLogN (by decide) (by decide)).trans e1,
                    (hout_off hdrEll (by decide) (by decide)).trans e2,
                    (hout_off hdrPgB (by decide) (by decide)).trans e3⟩
              ph2 := fun h2 => absurd (hph_r.symm.trans h2) (by decide)
              ph3_10 := fun _ => by
                simp only [↓reduceIte]; rw [hibH_r, hqH_r, hfr_r]
                exact ⟨hfr_hi_lo, hfr_hi_mid⟩
              ph11 := fun h11 => absurd (hph_r.symm.trans h11) (by decide)
              budget := by
                dsimp only
                rw [hnS_r, hst_r, hph_r, hnD_r, ite_eq_left hd_pos, hcur_r, heq_bm']
                unfold remRebuildBudget futureRebuildBudget
                dsimp only
                simp only [show (5 : ℕ) ≠ 1 by decide, show (5 : ℕ) ≠ 2 by decide,
                  show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
                  show 4 ≤ 5 by decide, show 5 ≤ 9 by decide, and_self, ↓reduceIte,
                  Nat.sub_self, Nat.zero_div, zero_add]
                have hrb := hrem_b.2.1
                have hel2 := hrem_b.2.2
                rw [hp5, ite_eq_left hd_pos] at hrb
                unfold remRebuildBudget futureRebuildBudget at hrb
                dsimp only at hrb
                simp only [show (5 : ℕ) ≠ 1 by decide, show (5 : ℕ) ≠ 2 by decide,
                  show (5 : ℕ) ≠ 3 by decide, show (5 : ℕ) ≠ 4 by decide,
                  show 4 ≤ 5 by decide, show 5 ≤ 9 by decide, and_self, ↓reduceIte] at hrb
                have hf2 := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                dsimp only [nSrc] at hf2 ⊢
                generalize max (whpThreshold c) (s.mem (base + hdrNSrc)) = nRef at hrb hel2 hf2 ⊢
                by_cases hst0 : s.mem (base + hdrStage) = 0
                · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                    at hrb ⊢
                  clear *- hrb hel2 hf2; omega
                · simp only [show stg = s.mem (base + hdrStage) from rfl, hst0, ↓reduceIte]
                    at hrb ⊢
                  clear *- hrb hel2 hf2; omega }
        pad_fits := by
          rw [hnS_r, hph_r, ite_eq_right (by decide : 5 ≠ 0), hnD_r]
          have hp := h.pad_fits; rwa [ite_eq_right (by clear *- hp5; omega)] at hp
        ph1_inv := fun h1 => absurd (hph_r.symm.trans h1) (by decide)
        ph3_inv := fun h3 => absurd (hph_r.symm.trans h3) (by decide)
        ph4_inv := fun h4 => absurd (hph_r.symm.trans h4) (by decide)
        pDst_pre := fun _ _ _ => by
          dsimp only; rw [hnD_r, hmbD_r, hpD_r, hibH_r, hqH_r]; exact hpt_r
        ph5_inv := fun _ => by
          dsimp only; rw [hnD_r, hmbD_r, hpD_r, hibH_r, hqH_r, hcur_r, heq_bm']
          exact ⟨hd_pos, hcur_ge32.trans hcur_le_bm, le_rfl, hpt_r, hz_hdr_r, hz_post_r⟩
        ph6_inv := fun h6 => absurd (hph_r.symm.trans h6) (by decide)
        ph7_inv := fun h7 => absurd (hph_r.symm.trans h7) (by decide)
        ph8_inv := fun h8 => absurd (hph_r.symm.trans h8) (by decide)
        ph9_inv := fun h9 => absurd (hph_r.symm.trans h9) (by decide)
        ph10_inv := fun h10 => absurd (hph_r.symm.trans h10) (by decide)
        sl_le7 := fun _ => by
          have hcap_r : dualCapSrc base s_rand.mem = dualCapSrc base s.mem := by
            unfold dualCapSrc; rw [hst_r, hnS_r, hnD_r]
          rw [hcap_r, hph_r, hfr_r]
          refine ⟨hcap_s, hdict_s, ?_, fun _ hs_p => hlen_s (by clear *- hp5; omega) hs_p⟩
          unfold activeSrcIo
          rw [ite_eq_right (by decide : ¬(5 < 3)), ite_eq_right (by decide : 5 ≠ 3),
            ite_eq_left (by decide : 5 < 8), hibH_r, hqH_r]
          exact hsl_r_fr
        sl_67 := fun h67 => by rw [hph_r] at h67; clear *- h67; omega
        sl_8 := fun h8 => absurd (hph_r.symm.trans h8) (by decide)
        sl_ge9 := fun h9 => by rw [hph_r] at h9; clear *- h9; omega }

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

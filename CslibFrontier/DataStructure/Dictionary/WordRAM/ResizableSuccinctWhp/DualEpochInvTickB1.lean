/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvTickA2

/-!
# Background Tick Phases `6..7` (`DualEpochInvTickB1`)

Proves shared host page-arena coupling (`dualPgHost_eval_valid`, `disjoint_pgHost_nonPageMeta`) and
`BgTickPre` / `DualPostTickInv` for background tick phases:
* Phase `6` (`tickInitDirProg`, `tickPhase6_spec`): incremental page-directory initialization
  (`6 → 6` and `6 → 7`).
* Phase `7` (`tickInitTailProg` + `finishInitTailProg`, `tickPhase7_spec`): incremental tail-ring
  initialization (`7 → 7`) and band-stable paged slot activation (`7 → 8`).

## Main results

* `dualPgHost_eval_valid`, `disjoint_pgHost_nonPageMeta`, `tickPhase6_spec`, `tickPhase7_spec`

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

private theorem offEpochEnd_le_epochMetaWordsWhp {c w N : ℕ} (hth : whpThreshold c ≤ N) :
    offEpochEnd c w N = epochMetaWordsWhp c w N :=
  offEpochEnd_eq_epochMetaWordsWhp hth

private theorem four_le_whpThreshold (c : ℕ) : 4 ≤ whpThreshold c :=
  (by decide : 4 ≤ 2 ^ 20).trans (whpThreshold_ge_pow20 c)

attribute [local irreducible] epochMetaWordsWhp

/-! ## Section 1: Shared Host Page-Arena Helpers (`dualPgHost_eval_valid`,
`disjoint_pgHost_nonPageMeta`, `pageSizeWhp_host_le_ref`, `active_elapsed_lt_capSrc`) -/

/-- Bounds `pageSizeWhp nHost` against the reference page size `max 32 (Nat.log 2 (2 * nRef) + 4)`.
-/
theorem pageSizeWhp_host_le_ref {c nHost nRef : ℕ}
    (hth : whpThreshold c ≤ nHost) (hle : nHost ≤ 2 * nRef) :
    pageSizeWhp nHost ≤ max 32 (Nat.log 2 (2 * nRef) + 4) := by
  have h4 : 4 ≤ nHost := (four_le_whpThreshold c).trans hth
  have hp2 : nHost + 2 ≤ 4 * nRef := by clear *- h4 hle; omega
  have hpow : 2 * nRef < 2 ^ (Nat.log 2 (2 * nRef) + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * nRef)
  have hpow2 : nHost + 2 ≤ 2 ^ (Nat.log 2 (2 * nRef) + 4) := by
    have h4n : 4 * nRef < 2 ^ (Nat.log 2 (2 * nRef) + 2) := by
      rw [Nat.pow_succ]
      clear *- hpow; omega
    have h2_4 : 2 ^ (Nat.log 2 (2 * nRef) + 2) ≤ 2 ^ (Nat.log 2 (2 * nRef) + 4) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    clear *- hp2 h4n h2_4; omega
  unfold pageSizeWhp
  exact max_le (le_max_left _ _)
    (((Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hpow2).trans (le_max_right _ _))

/-- In any active phase (`1 ≤ ph`), `dualNHost ≤ 2 * max (whpThreshold c) nSrc`. -/
theorem dualNHost_le_two_nRef {isMid : Bool} {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s)
    (hp1 : 1 ≤ s.mem (base + hdrPhase)) :
    dualNHost base s.mem ≤ 2 * max (whpThreshold c) (s.mem (base + hdrNSrc)) := by
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp1; omega)] at hsched
  have hb_el := hsched.budget.2.2
  have hnD_le := (active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap hsched.drift_hi
    hsched.drift_lo
    (by clear *- hb_el; cases isMid <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)
    h.live_le).1
  unfold dualNHost
  by_cases hd0 : s.mem (base + hdrNDst) = 0
  · rw [ite_eq_left hd0]
    exact (le_max_right _ _).trans (Nat.le_mul_of_pos_left _ (by decide))
  · rw [ite_eq_right hd0]; exact hnD_le

/-- In any active phase (`1 ≤ ph`) with `0 < dualCapSrc`, `L.elapsed + 1 ≤ dualCapSrc`. -/
theorem active_elapsed_lt_capSrc {isMid : Bool} {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s)
    (hp1 : 1 ≤ s.mem (base + hdrPhase))
    (hcap_pos : 0 < dualCapSrc base s.mem) :
    L.elapsed + 1 ≤ dualCapSrc base s.mem := by
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp1; omega)] at hsched
  have hpost := hsched.post_trig
  have htrig := hsched.trig_cap
  have hb_el := hsched.budget.2.2
  have hnSrc_b := h.nSrc_bounds
  have hnt_U : L.nTrig ≤ U := by
    by_cases hs0 : s.mem (base + hdrNSrc) = 0
    · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost; exact hpost.1
    · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost; exact hpost.2.2.1
  have hdst_safe := (active_rebuild_safe hpost htrig (Nat.le_add_right _ 0)
    (Nat.le_add_right _ 0) (Nat.zero_le _) hnt_U).2.2.1
  unfold dualCapSrc at hcap_pos ⊢
  by_cases hst0 : s.mem (base + hdrStage) = 0
  · rw [ite_eq_left hst0] at hcap_pos ⊢
    have hth_s : whpThreshold c ≤ s.mem (base + hdrNSrc) := by
      rcases hnSrc_b with hz | ⟨hth, _⟩
      · exact absurd hz hcap_pos.ne'
      · exact hth
    have hm : max (whpThreshold c) (s.mem (base + hdrNSrc)) = s.mem (base + hdrNSrc) :=
      max_eq_right hth_s
    rw [hm] at hb_el; clear *- hb_el; omega
  · rw [ite_eq_right hst0] at hcap_pos ⊢
    simp only [EpochCapSafe, hcap_pos.ne', ↓reduceIte] at hdst_safe
    obtain ⟨hth_d, _, _, hnt_d⟩ := hdst_safe
    by_cases hs0 : s.mem (base + hdrNSrc) = 0
    · rw [hs0, max_eq_left (Nat.zero_le _)] at hb_el
      clear *- hb_el hth_d; omega
    · have hth_s : whpThreshold c ≤ s.mem (base + hdrNSrc) := by
        rcases hnSrc_b with hz | ⟨hth, _⟩
        · exact absurd hz hs0
        · exact hth
      rw [max_eq_right hth_s] at hb_el
      simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost
      have h27 := hpost.2.2.2.1
      clear *- hb_el h27 hnt_d hcap_pos; omega

/-- Evaluates `loadHostCtxProg` (`metaOnly ∈ {0, 1}`) and certifies `PageArenaLayout.Valid` on the
shared host arena in active phases `3..10`. -/
theorem dualPgHost_eval_valid {isMid : Bool} {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s)
    (hp3 : 3 ≤ s.mem (base + hdrPhase)) (hp10 : s.mem (base + hdrPhase) ≤ 10) :
    let nLive := (Dictionary.dom s_dict).card
    let nHost := dualNHost base s.mem
    let mbHost := dualMbHost base s.mem
    let ibHi := s.mem (base + hdrItemHi)
    let qHi := s.mem (base + hdrQHi)
    let vB := valBits V
    let hiFr := ibHi + pairStreamWords nLive qHi vB w
    let pgH := dualPgHost c V w base nLive s.mem
    let pgM := hostPageLayout c w nHost mbHost ibHi 0 0 nHost
    (whpThreshold c ≤ nHost ∧ nHost ≤ U) ∧
    nLive ≤ nHost ∧
    Fits w (base + 192 + s.mem (base + hdrPad)) ∧
    mbHost + epochMetaWordsWhp c w nHost ≤ ibHi ∧
    (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0)) = pgH.toCtx ∧
    (Memory.spec 0).clientResult s (loadHostCtxProg (base, 1)) = pgM.toCtx ∧
    pgH.Valid w hiFr ∧ pgH.Valid w s.frontier ∧ pgM.Valid w s.frontier := by
  dsimp only
  have hw11 := h.hw11; have hUw := h.U_lt; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src; have hnSrc_b := h.nSrc_bounds
  have hw_eq : s.mem (base + hdrW) = w := h.hdr.2.2.1
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp3; omega)] at hsched
  obtain ⟨hfr_hi_lo, _⟩ := hsched.ph3_10 ⟨hp3, hp10⟩
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, _, hibHi_eq, _⟩ :=
    hsched.ge2 (by clear *- hp3; omega)
  obtain ⟨hvb_eq, hvb_w, _, hqHi_w, _, _, _, hfit_hi1⟩ := dualCoreInv_ib_fits h
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  rw [ite_eq_right (by clear *- hp3; omega)] at hdst_safe
  set nLive := (Dictionary.dom s_dict).card
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  set mSrc := s.mem (base + hdrMSrc)
  set mDst := s.mem (base + hdrMDst)
  set pad := s.mem (base + hdrPad)
  set ibHi := s.mem (base + hdrItemHi)
  set qHi := s.mem (base + hdrQHi)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set nHost := dualNHost base s.mem
  set mbHost := dualMbHost base s.mem
  have hmS_pad : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
  have hmD_pad : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
  have hpad_fits : Fits w (base + 192 + pad) := by
    have hib_ge : base + 192 + pad ≤ ibHi := by
      rw [hibHi_eq]
      by_cases hd0 : nDst = 0
      · rw [ite_eq_left hd0]
        have hmD0 : mDst = 0 := by rw [hmDst_eq, hd0, epochMetaWordsWhp_zero_eq]
        have hp_eq : pad = mSrc := by rw [hpad_eq, hmD0, Nat.max_zero]
        clear *- hp_eq; omega
      · rw [ite_eq_right hd0]; omega
    unfold Fits at hfit_hi1 ⊢
    clear *- hib_ge hfit_hi1; omega
  have hhost : (whpThreshold c ≤ nHost ∧ nHost ≤ U) ∧ nLive ≤ nHost ∧
      mbHost + epochMetaWordsWhp c w nHost ≤ ibHi ∧
      s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd)) = offPageDir c w nHost ∧
      s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 1) = offPageTail c w nHost ∧
      s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 2) = globalPtrBits nHost ∧
      s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 3) = pageSizeWhp nHost ∧
      s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 4) =
        nHost / pageSizeWhp nHost + 4 := by
    dsimp only [nHost, mbHost]; unfold dualNHost dualMbHost
    by_cases hd0 : nDst = 0
    · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte]
      have hs_pos : 0 < nSrc := (hsched.nDst_zero hd0).1
      have hth_s : whpThreshold c ≤ nSrc ∧ nSrc ≤ U := by
        rcases hnSrc_b with hz | hb
        · exact absurd hz hs_pos.ne'
        · exact hb
      have hnL_s : nLive ≤ nSrc := by
        simp only [EpochCapSafe, hs_pos.ne', ↓reduceIte] at hsrc_safe
        exact hsrc_safe.2.2.2
      have hib0 : ibHi = base + 196 + mSrc := by rw [hibHi_eq, ite_eq_left hd0]
      have hc_s := hcache_s hs_pos
      exact ⟨hth_s, hnL_s, by rw [← hmSrc_eq, hib0]; omega,
        hc_s.1, hc_s.2.1, hc_s.2.2.1, hc_s.2.2.2.1, hc_s.2.2.2.2⟩
    · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte]
      have hd_pos : 0 < nDst := Nat.pos_of_ne_zero hd0
      have hth_d : whpThreshold c ≤ nDst ∧ nDst ≤ U := by
        rcases hsched.nDst_bounds with hz | hb
        · exact absurd hz hd0
        · exact hb
      have hnL_d : nLive ≤ nDst := by
        simp only [EpochCapSafe, hd0, ↓reduceIte] at hdst_safe
        exact hdst_safe.2.2.2
      have hib1 : ibHi = base + 192 + pad + mDst + 4 := by rw [hibHi_eq, ite_eq_right hd0]
      have hc_d := hcache_d hd_pos
      refine ⟨hth_d, hnL_d, ?_, hc_d.1, hc_d.2.1, hc_d.2.2.1, hc_d.2.2.2.1, hc_d.2.2.2.2⟩
      rw [← hmDst_eq, hib1]
      split_ifs <;> (clear *- hmD_pad; omega)
  obtain ⟨hth_h, hnL_h, hmb_ib, hc0, hc1, hc2, hc3, hc4⟩ := hhost
  have hctx0 : (Memory.spec 0).clientResult s (loadHostCtxProg (base, 0)) =
      (dualPgHost c V w base nLive s.mem).toCtx := by
    rw [(loadHostCtxProg_eval base 0 s).2.1]
    simp only [↓reduceIte]
    dsimp only [dualPgHost, hostPageLayout, epochPageArenaLayout, PageArenaLayout.toCtx]
    change ((((mbHost, s.mem (base + if nDst = 0 then hdrSrcOd else hdrDstOd)),
        (s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 1),
          s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 2))),
        ((s.mem (base + hdrW), s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 3)),
          (s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 4), ibHi))),
        ((qHi, s.mem (base + hdrValBits)), s.mem (base + hdrLive))) = _
    rw [hc0, hc1, hc2, hc3, hc4, hw_eq, hvb_eq, hlive_eq]
  have hctx1 : (Memory.spec 0).clientResult s (loadHostCtxProg (base, 1)) =
      (hostPageLayout c w nHost mbHost ibHi 0 0 nHost).toCtx := by
    rw [(loadHostCtxProg_eval base 1 s).2.1]
    simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
    dsimp only [hostPageLayout, epochPageArenaLayout, PageArenaLayout.toCtx]
    change ((((mbHost, s.mem (base + if nDst = 0 then hdrSrcOd else hdrDstOd)),
        (s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 1),
          s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 2))),
        ((s.mem (base + hdrW), s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 3)),
          (s.mem (base + (if nDst = 0 then hdrSrcOd else hdrDstOd) + 4), ibHi))),
        ((0, 0), nHost)) = _
    rw [hc0, hc1, hc2, hc3, hc4, hw_eq]
  have hnL_w : Fits w nLive := lt_of_le_of_lt hlive_le hUw
  have hnH_w : Fits w nHost := lt_of_le_of_lt hth_h.2 hUw
  have hv_hi : (dualPgHost c V w base nLive s.mem).Valid w hiFr :=
    valid_epochPageArenaLayout hth_h.1 hth_h.2 hUw hqHi_w hvb_w
      (Nat.le_succ_of_le hnL_h) hnL_w hmb_ib le_rfl
  have hv_fr : (dualPgHost c V w base nLive s.mem).Valid w s.frontier :=
    valid_epochPageArenaLayout hth_h.1 hth_h.2 hUw hqHi_w hvb_w
      (Nat.le_succ_of_le hnL_h) hnL_w hmb_ib hfr_hi_lo
  have hpw0 : pairStreamWords nHost 0 0 w = 2 := by
    unfold pairStreamWords packedWords
    simp [Nat.div_eq_of_lt (show w - 1 < w by clear *- hw_pos; omega)]
  have hpw_ge2 : 2 ≤ pairStreamWords nLive qHi vB w := Nat.le_add_left 2 _
  have hv_m : (hostPageLayout c w nHost mbHost ibHi 0 0 nHost).Valid w s.frontier :=
    valid_epochPageArenaLayout hth_h.1 hth_h.2 hUw (Nat.zero_le w) (Nat.zero_le w)
      (Nat.le_succ nHost) hnH_w hmb_ib
      (by rw [hpw0]; dsimp only [hiFr] at hfr_hi_lo; clear *- hpw_ge2 hfr_hi_lo; omega)
  exact ⟨hth_h, hnL_h, hpad_fits, hmb_ib, hctx0, hctx1, hv_hi, hv_fr, hv_m⟩

/-- Exact address bounds for `(hostPageLayout ...).OwnsMetaAddr`. -/
theorem pgHost_ownsMeta_bounds {c w nHost mbHost ibHi qHi vB nc a : ℕ}
    (hth : whpThreshold c ≤ nHost)
    (ha : (hostPageLayout c w nHost mbHost ibHi qHi vB nc).OwnsMetaAddr a) :
    (mbHost + 18 ≤ a ∧ a < mbHost + 32) ∨
    (mbHost + offPageDir c w nHost ≤ a ∧ a < mbHost + epochMetaWordsWhp c w nHost) := by
  have hend := offEpochEnd_le_epochMetaWordsWhp (c := c) (w := w) hth
  unfold PageArenaLayout.OwnsMetaAddr hostPageLayout epochPageArenaLayout at ha
  dsimp only at ha
  rcases ha with h1 | h2 | h3
  · exact Or.inl h1
  · refine Or.inr ⟨h2.1, ?_⟩
    unfold offEpochEnd offPageTail at hend
    have h2' := h2.2
    clear *- h2' hend; omega
  · refine Or.inr ⟨?_, ?_⟩
    · unfold offPageTail at h3; clear *- h3; omega
    · unfold offEpochEnd at hend; clear *- h3 hend; omega

/-- Every address in `(dualPgHost ...).OwnsMetaAddr` lies in `[base + 210, ibHi)` and is disjoint
from `slotOwnsNonPageMeta` for both `slotSrc` and `slotDst` (`ph < 10`). -/
theorem disjoint_pgHost_nonPageMeta {isMid : Bool} {c U V w base nc : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualCoreInv isMid c U V w base s_dict L s)
    (hp3 : 3 ≤ s.mem (base + hdrPhase)) (hp9 : s.mem (base + hdrPhase) ≤ 9) :
    let pgH := dualPgHost c V w base nc s.mem
    ∀ a, pgH.OwnsMetaAddr a →
      base + 210 ≤ a ∧ a < s.mem (base + hdrItemHi) ∧
      ¬slotOwnsNonPageMeta c w (dualMbSrc base s.mem) (dualCapSrc base s.mem) a ∧
      ¬slotOwnsNonPageMeta c w (dualMbDst base s.mem) (s.mem (base + hdrNDst)) a := by
  dsimp only
  have hpgv := dualPgHost_eval_valid h hp3 (by clear *- hp9; omega)
  dsimp only at hpgv
  have hth_h := hpgv.1
  have hmb_ib := hpgv.2.2.2.1
  have hmSrc_eq := h.mSrc_eq; have hnSrc_b := h.nSrc_bounds
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp3; omega)] at hsched
  obtain ⟨hmDst_eq, hpad_eq, _, _, _, _⟩ := hsched.ge2 (by clear *- hp3; omega)
  have hmS_pad : s.mem (base + hdrMSrc) ≤ s.mem (base + hdrPad) := by
    rw [hpad_eq]; exact le_max_left _ _
  have hmD_pad : s.mem (base + hdrMDst) ≤ s.mem (base + hdrPad) := by
    rw [hpad_eq]; exact le_max_right _ _
  have h32_od : 32 ≤ offPageDir c w (dualNHost base s.mem) :=
    (epochMeta_offsets_le hth_h.1).1.trans
      ((epochMeta_offsets_le hth_h.1).2.1.trans (epochMeta_offsets_le hth_h.1).2.2.1)
  intro a ha
  have hb := pgHost_ownsMeta_bounds hth_h.1 ha
  have hmb_ge : base + 192 ≤ dualMbHost base s.mem := by
    unfold dualMbHost; split_ifs <;> (clear *-; omega)
  have ha210 : base + 210 ≤ a := by
    rcases hb with ⟨h1, _⟩ | ⟨h1, _⟩ <;> (clear *- hmb_ge h1 h32_od; omega)
  have ha_ib : a < s.mem (base + hdrItemHi) := by
    rcases hb with ⟨_, h2⟩ | ⟨_, h2⟩
    · have hm32 : 32 ≤ epochMetaWordsWhp c w (dualNHost base s.mem) :=
        h32_od.trans (epochMeta_offsets_le hth_h.1).2.2.2
      clear *- h2 hm32 hmb_ib; omega
    · exact lt_of_lt_of_le h2 hmb_ib
  refine ⟨ha210, ha_ib, ?_, ?_⟩
  · intro hs_own
    unfold slotOwnsNonPageMeta dualMbSrc dualCapSrc at hs_own
    have h32_s : s.mem (base + hdrNDst) = 0 → 32 ≤ offPageDir c w (s.mem (base + hdrNSrc)) :=
      fun hd0 => by simpa only [dualNHost, hd0, ↓reduceIte] using h32_od
    unfold dualMbHost dualNHost at hb
    by_cases hd0 : s.mem (base + hdrNDst) = 0
    · obtain ⟨hs_pos, hst0, _, _, _⟩ := hsched.nDst_zero hd0
      have h32_s0 := h32_s hd0
      simp only [hd0, hst0, hs_pos.ne', ↓reduceIte] at hb hs_own
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs_own with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
        (clear *- h1 h2 g1 g2 h32_s0; omega)
    · simp only [hd0, ↓reduceIte] at hb
      by_cases hst0 : s.mem (base + hdrStage) = 0
      · simp only [hst0, ↓reduceIte] at hb hs_own
        by_cases hs0 : s.mem (base + hdrNSrc) = 0
        · simp only [hs0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at hs_own
          dsimp only [hdrSmallMeta0] at hs_own; clear *- ha210 hs_own; omega
        · have hth_s : whpThreshold c ≤ s.mem (base + hdrNSrc) := by
            rcases hnSrc_b with hz | ⟨hth, _⟩
            · exact absurd hz hs0
            · exact hth
          have hod_s : offPageDir c w (s.mem (base + hdrNSrc)) ≤ s.mem (base + hdrPad) :=
            (epochMeta_offsets_le hth_s).2.2.2.trans (hmSrc_eq.symm.le.trans hmS_pad)
          have hmS32 : 32 ≤ s.mem (base + hdrPad) :=
            (epochMeta_offsets_le hth_s).1.trans
              ((epochMeta_offsets_le hth_s).2.1.trans
                ((epochMeta_offsets_le hth_s).2.2.1.trans hod_s))
          simp only [hs0, ↓reduceIte] at hs_own
          rcases hb with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases hs_own with ⟨_, g2⟩ | ⟨_, _, g2⟩ <;>
            (clear *- h1 g2 hod_s hmS32; omega)
      · simp only [hst0, hd0, ↓reduceIte] at hb hs_own
        have hmD_le : epochMetaWordsWhp c w (s.mem (base + hdrNDst)) ≤ s.mem (base + hdrPad) :=
          hmDst_eq.symm.le.trans hmD_pad
        have hmD32 : 32 ≤ s.mem (base + hdrPad) := by
          have hth_d : whpThreshold c ≤ s.mem (base + hdrNDst) := by
            simpa only [dualNHost, hd0, ↓reduceIte] using hth_h.1
          have ho := epochMeta_offsets_le (c := c) (w := w) hth_d
          exact (ho.1.trans (ho.2.1.trans (ho.2.2.1.trans ho.2.2.2))).trans hmD_le
        rcases hb with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rcases hs_own with ⟨g1, _⟩ | ⟨_, g1, _⟩ <;>
          (clear *- h2 g1 hmD_le hmD32; omega)
  · intro hd_own
    unfold slotOwnsNonPageMeta dualMbDst at hd_own
    rw [ite_eq_left (by clear *- hp9; omega)] at hd_own
    have h32_d : s.mem (base + hdrNDst) ≠ 0 → 32 ≤ offPageDir c w (s.mem (base + hdrNDst)) :=
      fun hd0 => by simpa only [dualNHost, hd0, ↓reduceIte] using h32_od
    unfold dualMbHost dualNHost at hb
    by_cases hd0 : s.mem (base + hdrNDst) = 0
    · simp only [hd0, ↓reduceIte, ne_eq, not_true_eq_false, false_and, or_false] at hd_own
      dsimp only [hdrSmallMeta1] at hd_own; clear *- ha210 hd_own; omega
    · have h32_d0 := h32_d hd0
      simp only [hd0, ↓reduceIte] at hb hd_own
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hd_own with ⟨g1, g2⟩ | ⟨_, g1, g2⟩ <;>
        (clear *- h1 h2 g1 g2 h32_d0; omega)

/-! ## Section 2: Phase `6` (`tickInitDirProg`) Specification -/

/-- Phase `6` (`initDir`) background tick specification. -/
theorem tickPhase6_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp6 : s.mem (base + hdrPhase) = 6) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb_fr := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src
  have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  obtain ⟨hth_h, hnL_h, hpad_w, hmb_ib, hctx0, hctx1, hv_hi, hv_fr, hv_m⟩ :=
    dualPgHost_eval_valid h (by clear *- hp6; omega) (by clear *- hp6; omega)
  have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) h
    (by clear *- hp6; omega) (by clear *- hp6; omega)
  have hnH_ref := dualNHost_le_two_nRef h (by clear *- hp6; omega)
  have hpgB_ref := pageSizeWhp_host_le_ref hth_h.1 hnH_ref
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp6; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_hi⟩ := hsched.ph3_10 ⟨by clear *- hp6; omega, by clear *- hp6; omega⟩
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp6; omega)
  obtain ⟨hb_ge2, hb_tot, hb_el⟩ := hsched.budget
  obtain ⟨hcur_le, hdir_pre⟩ := h.ph6_inv hp6
  obtain ⟨hcap_s, hdict_s, hsl_s, hevs_s⟩ := h.sl_le7 (by clear *- hp6; omega)
  have hsl_67 := h.sl_67 (Or.inl hp6)
  obtain ⟨hvb_eq, hvb_w, _, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h
  have hw_pos : 0 < w := by clear *- hw11; omega
  set nLive := (Dictionary.dom s_dict).card
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
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set nHost := dualNHost base s.mem
  set mbHost := dualMbHost base s.mem
  set pgH := dualPgHost c V w base nLive s.mem
  set pgM := hostPageLayout c w nHost mbHost ibHi 0 0 nHost
  have hm_ofCtx : PageArenaLayout.ofCtx pgM.toCtx = pgM := PageArenaLayout.ofCtx_toCtx pgM
  have hpre_dir : TickInitDirPre w base s := by
    refine ⟨hw11, hb_fr, hpad_w, ?_⟩
    rw [hctx1, hm_ofCtx]; exact hv_m
  have hpre : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb_fr; omega, ?_⟩
    simp only [hp6, Nat.reduceEqDiff, ↓reduceIte]
    exact hpre_dir
  have hwf_tick : Memory.WellFormed w
      ((Memory.spec 0).clientState s (bgTickProg (base, s.frontier))) :=
    wf_step hwf (validHistory_bgTickProg hwf hpre)
  have hbgev := bgTickProg_eval base s.frontier s
  simp only [hp6, Nat.reduceEqDiff, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  have htdev := tickInitDirProg_eval base s
  change _ ∧ _ at htdev
  rw [hctx1, hm_ofCtx, hlive_eq] at htdev
  obtain ⟨hst_td, hmc_td⟩ := htdev
  have hmp_eq : pgM.maxPages = pgH.maxPages := rfl
  have hpgB_eq : pgM.pgB = pgH.pgB := rfl
  have hmw_eq : pgM.w = w := rfl
  have hcur_le_m : cur ≤ pgM.maxPages := hmp_eq ▸ hcur_le
  have hdb_sp := pageInitDirBatchProg_spec (L := pgM) (cur := cur) (s := s)
    (hmw_eq ▸ hv_m) hcur_le_m bulkBatchWhp
  dsimp only at hdb_sp
  obtain ⟨_, hcur'_eq, hfr_s2, hmc_db, hout_s2, _, _, _, _, _, _, _, _, _, _, _, _,
    hpo_s2, how_s2⟩ := hdb_sp
  set db := pageInitDirBatchProg ((pgM.toCtx, cur), bulkBatchWhp)
  have hmc_tot : memoryCost (bgTickProg (base, s.frontier)) s ≤
      itemBatchWhp * (2 * epochStepCost c + 20) + 20000 := by
    dsimp only [db, cur, bulkBatchWhp, itemBatchWhp] at hmc_td hmc_db ⊢
    clear *- hmc_bg hmc_td hmc_db; omega
  obtain ⟨s2, hs2_def⟩ : ∃ s2, (Memory.spec 0).clientState s db = s2 := ⟨_, rfl⟩
  obtain ⟨cur', hcur'_def⟩ : ∃ cur', (Memory.spec 0).clientResult s db = cur' := ⟨_, rfl⟩
  rw [hs2_def] at hst_td hfr_s2 hout_s2 hpo_s2 how_s2
  rw [hcur'_def] at hst_td hcur'_eq
  clear hs2_def hcur'_def
  have hs2_pg : ∀ a, ¬pgH.OwnsMetaAddr a → s2.mem a = s.mem a := fun a ha =>
    hout_s2 a (fun hdir => ha (Or.inr (Or.inl hdir)))
  have hibHi_ge : base + 196 ≤ ibHi := by
    rw [hibHi_eq]; split_ifs <;> (clear *-; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    have hle1 : s.frontier ≤ ibHi + pairStreamWords (nLive + 1) qHi vB w := hfr_hi_hi
    have hstep := pairStreamWords_succ_le_add_two (n := nLive) (qb := qHi) (vb := vB) (w := w)
      hw_pos (by clear *- hqHi_w hvb_w; omega)
    dsimp only [hiFr, bulkBatchWhp]; clear *- hle1 hstep; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
    have hib_pad := (dualCoreInv_ib_fits h).2.2.2.2.2.1
    rw [ite_eq_right (by clear *- hp6; omega)] at hib_pad
    exact hfr_hi_hi.trans hib_pad
  have hio_src_eq : activeSrcIo c w vB base stg 6 nSrc nDst pad ibLo qLo ibHi qHi nLive =
      directSlotIo w vB base ibHi qHi nLive := rfl
  rw [hp6, hio_src_eq] at hsl_s
  have hdir_s2 : ∀ vp < cur',
      (extractPagePair pgH s2.mem).pageOf false vp = vp ∧
      (extractPagePair pgH s2.mem).pageOf true vp = 0 ∧
      (extractPagePair pgH s2.mem).ownerSide vp = false ∧
      (extractPagePair pgH s2.mem).ownerVp vp = vp := fun vp hvp => by
    have hvp_mp : vp < pgM.maxPages := lt_of_lt_of_le hvp (hcur'_eq ▸ min_le_left _ _)
    have hp_eq : extractPagePair pgH s2.mem = (extractPageUnperm pgM s2.mem).st := rfl
    have hp0_eq : (extractPageUnperm pgM s.mem).st = extractPagePair pgH s.mem := rfl
    rw [hp_eq]
    have hpo_f := hpo_s2 false vp hvp_mp
    have hpo_t := hpo_s2 true vp hvp_mp
    obtain ⟨hos, hov⟩ := how_s2 vp hvp_mp
    rw [hp0_eq] at hpo_f hpo_t hos hov
    rw [← hcur'_eq] at hpo_f hpo_t hos hov
    by_cases hge : cur ≤ vp
    · have hcond : cur ≤ vp ∧ vp < cur' := ⟨hge, hvp⟩
      simp only [hpo_f, hpo_t, hos, hov, hcond, and_self, Bool.false_eq_true, ↓reduceIte]
    · have hncond : ¬(cur ≤ vp ∧ vp < cur') := by clear *- hge; omega
      simp only [hpo_f, hpo_t, hos, hov, hncond, ↓reduceIte]
      exact hdir_pre vp (Nat.lt_of_not_le hge)
  obtain ⟨s_tick, hs_tick_def⟩ :
      ∃ s_tick, (Memory.spec 0).clientState s (bgTickProg (base, s.frontier)) = s_tick := ⟨_, rfl⟩
  rw [hs_tick_def] at hwf_tick hst_bg ⊢
  clear hs_tick_def
  have hfr_tick : s_tick.frontier = s.frontier := by
    rw [hst_bg, hst_td]
    split_ifs <;> exact hfr_s2
  have h6_10 : s.mem (base + hdrPhase) < 10 := by clear *- hp6; omega
  -- Prove common slot preservation under any header write in `[base + 11, base + 40)` on `s2.mem`
  have hsl_pres : ∀ (m' : ℕ → ℕ),
      (∀ a, ¬(base + 11 ≤ a ∧ a < base + 40) → m' a = s2.mem a) →
      m' (base + hdrStage) = stg → m' (base + hdrNSrc) = nSrc →
      m' (base + hdrNDst) = nDst → m' (base + hdrPad) = pad →
      m' (base + hdrPhase) < 10 →
      EpochSlotInv c U V w hiFr (dualPSrc base m') (dualMbSrc base m')
        (directSlotIo w vB base ibHi qHi nLive) 0 false L.slotSrc m' ∧
      ((nDst = 0 → m' (base + hdrSmallMeta1) = 0 ∧ m' (base + hdrSmallMeta1 + 1) = 0) ∧
       (0 < nDst →
         EpochSlotInv c U V w hiFr (dualPDst base m') (dualMbDst base m')
           (directSlotIo w vB base ibHi qHi nLive) 0 false L.slotDst m')) := by
    intro m' hm_out hst_m hnS_m hnD_m hpad_m hph_lt10
    have hpS_eq : dualPSrc base m' = dualPSrc base s.mem := by unfold dualPSrc; rw [hst_m]
    have hmS_mb : dualMbSrc base m' = dualMbSrc base s.mem := by
      unfold dualMbSrc; rw [hst_m, hnS_m, hpad_m]
    have hpD_eq : dualPDst base m' = dualPDst base s.mem := by
      unfold dualPDst; rw [ite_eq_left hph_lt10, ite_eq_left h6_10, hst_m]
    have hmD_mb : dualMbDst base m' = dualMbDst base s.mem := by
      unfold dualMbDst
      rw [ite_eq_left hph_lt10, ite_eq_left h6_10, hnD_m, hst_m, hpad_m]
    have hm_ge48 : ∀ a, base + 48 ≤ a → ¬pgH.OwnsMetaAddr a → m' a = s.mem a := fun a h48 hpg =>
      (hm_out a (by clear *- h48; omega)).trans (hs2_pg a hpg)
    have hsl_s_m' : EpochSlotInv c U V w hiFr (dualPSrc base m') (dualMbSrc base m')
        (directSlotIo w vB base ibHi qHi nLive) 0 false L.slotSrc m' := by
      rw [hpS_eq, hmS_mb]
      refine (hsl_s.congr_mem
        (fun a h1 h2 => hm_ge48 a (by
          unfold dualPSrc at h1; dsimp only [hdrPBase0, hdrPBase1] at h1
          split_ifs at h1 <;> (clear *- h1; omega))
          (fun hpg => by
            have ha210 := (hdisj_pg a hpg).1
            unfold dualPSrc at h2; dsimp only [hdrPBase0, hdrPBase1] at h2
            split_ifs at h2 <;> (clear *- h2 ha210; omega)))
        (fun a ha => by
          have hr := slotOwnsNonPageMeta_src_range hcap_s
            (fun hst_nz hd0 => hst_nz (hsched.nDst_zero hd0).2.1) ha
          exact hm_ge48 a (by rcases hr with ⟨h1, _⟩ | h1 <;> (clear *- h1; omega))
            (fun hpg => (hdisj_pg a hpg).2.2.1 (hcap_s ▸ ha)))
        (fun a ha => by
          simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
            ↓reduceIte] at ha
          have ha1 := ha.1
          exact hm_ge48 a (by clear *- ha1 hibHi_ge; omega)
            (fun hpg => absurd ha1 (Nat.not_le_of_gt (hdisj_pg a hpg).2.1)))).at_exact_frontier
        (by unfold dualPSrc; dsimp only [hiFr, hdrPBase0, hdrPBase1]
            split_ifs <;> (clear *- hibHi_ge; omega))
        (by unfold dualMbSrc; rw [hcap_s]; unfold dualCapSrc
            by_cases hst0 : stg = 0
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [← hmSrc_eq]
              by_cases hs0 : nSrc = 0
              · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                clear *- hibHi_ge; omega
              · rw [ite_eq_right hs0, ite_eq_right hs0]
                have hmS_p : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
                dsimp only [hiFr]; rw [hibHi_eq]; split_ifs <;> (clear *- hmS_p; omega)
            · have hd_nz : nDst ≠ 0 := fun hd0 => hst0 (hsched.nDst_zero hd0).2.1
              simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              dsimp only [hiFr]; rw [← hmDst_eq, hibHi_eq]
              simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_nz, ↓reduceIte]
              dsimp only [pad, mDst]; clear *-; omega)
        (by dsimp only [directSlotIo]; exact le_rfl)
    refine ⟨hsl_s_m', ⟨fun hd0 => ?_, fun hd_pos => ?_⟩⟩
    · obtain ⟨hz0, hz1⟩ := hsl_67.1 hd0
      have hsm0 := hm_ge48 (base + hdrSmallMeta1) (by unfold hdrSmallMeta1; clear *-; omega)
        (fun hpg => by
          have ha210 := (hdisj_pg _ hpg).1; unfold hdrSmallMeta1 at ha210; clear *- ha210; omega)
      have hsm1 := hm_ge48 (base + hdrSmallMeta1 + 1) (by unfold hdrSmallMeta1; clear *-; omega)
        (fun hpg => by
          have ha210 := (hdisj_pg _ hpg).1; unfold hdrSmallMeta1 at ha210; clear *- ha210; omega)
      exact ⟨hsm0.trans hz0, hsm1.trans hz1⟩
    · obtain ⟨hd_cap, _, _, hsl_d⟩ := hsl_67.2 hd_pos
      rw [hpD_eq, hmD_mb]
      refine (hsl_d.congr_mem
        (fun a h1 h2 => hm_ge48 a (by
          unfold dualPDst at h1; rw [ite_eq_left h6_10] at h1
          dsimp only [hdrPBase0, hdrPBase1] at h1
          split_ifs at h1 <;> (clear *- h1; omega))
          (fun hpg => by
            have ha210 := (hdisj_pg a hpg).1
            unfold dualPDst at h2; rw [ite_eq_left h6_10] at h2
            dsimp only [hdrPBase0, hdrPBase1] at h2
            split_ifs at h2 <;> (clear *- h2 ha210; omega)))
        (fun a ha => by
          have ha48 : base + 48 ≤ a := by
            rw [hd_cap] at ha
            unfold slotOwnsNonPageMeta dualMbDst at ha
            rw [ite_eq_left h6_10] at ha
            simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_pos.ne', ↓reduceIte] at ha
            rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;> (split_ifs at h1 <;> (clear *- h1; omega))
          exact hm_ge48 a ha48 (fun hpg => (hdisj_pg a hpg).2.2.2 (hd_cap ▸ ha)))
        (fun a ha => by
          simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
            ↓reduceIte] at ha
          have ha1 := ha.1
          exact hm_ge48 a (by clear *- ha1 hibHi_ge; omega)
            (fun hpg => absurd ha1 (Nat.not_le_of_gt (hdisj_pg a hpg).2.1)))).at_exact_frontier
        (by unfold dualPDst; rw [ite_eq_left h6_10]
            dsimp only [hiFr, hdrPBase0, hdrPBase1]; split_ifs <;> (clear *- hibHi_ge; omega))
        (by unfold dualMbDst; rw [ite_eq_left h6_10, hd_cap]
            simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_pos.ne', ↓reduceIte]
            have hmD_p : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
            dsimp only [hiFr]; rw [← hmDst_eq, hibHi_eq, ite_eq_right hd_pos.ne']
            dsimp only [pad, mDst]; split_ifs <;> (clear *- hmD_p; omega))
        (by dsimp only [directSlotIo]; exact le_rfl)
  refine ⟨hpre, hfr_tick, hwf_tick, fun addr hlt_b => ?_, ?_⟩
  · rw [hst_bg, hst_td]
    have hs2_lt : s2.mem addr = s.mem addr :=
      hs2_pg addr (fun hpg => by have := (hdisj_pg addr hpg).1; clear *- hlt_b this; omega)
    by_cases hlt_c : cur' < pgM.maxPages
    · rw [ite_eq_left hlt_c]; dsimp only
      rw [Function.update_of_ne (by dsimp only [hdrCur]; clear *- hlt_b; omega)]
      exact hs2_lt
    · rw [ite_eq_right hlt_c]; dsimp only
      iterate 4 rw [Function.update_of_ne
        (by dsimp only [hdrNSnap, hdrQSnap, hdrCur, hdrPhase]; clear *- hlt_b; omega)]
      exact hs2_lt
  · rw [ite_eq_left (by clear *- hp6; omega)]
    refine ⟨hres_bg, ⟨{ L with elapsed := L.elapsed + 1 }, preservesEpochSeeds_of_eq_slots
      (fun ⟨h9, _⟩ => by rw [hp6] at h9; cases h9) rfl rfl,
      ?_, fun _ _ => hmc_tot⟩⟩
    by_cases hlt_mp : cur' < pgM.maxPages
    · -- `6 → 6`: `cur' = cur + bulkBatchWhp < pgM.maxPages`
      have hcur'_step : cur' = cur + bulkBatchWhp := by
        rw [hcur'_eq, min_eq_right (by rw [hcur'_eq] at hlt_mp; clear *- hlt_mp; omega)]
      have hm_eq : s_tick.mem = Function.update s2.mem (base + hdrCur) cur' := by
        rw [hst_bg, hst_td, ite_eq_left hlt_mp]
      have hout_hdr : ∀ off, off ≠ hdrCur → off < 192 →
          s_tick.mem (base + off) = s.mem (base + off) := fun off hne h192 => by
        rw [hm_eq, Function.update_of_ne (base_add_ne hne)]
        exact hs2_pg (base + off) (fun hpg => by
          have := (hdisj_pg _ hpg).1; clear *- h192 this; omega)
      have hph_t : s_tick.mem (base + hdrPhase) = 6 :=
        (hout_hdr hdrPhase (by decide) (by decide)).trans hp6
      have hcur_t : s_tick.mem (base + hdrCur) = cur' := by
        rw [hm_eq]; exact Function.update_self ..
      have hst_t : s_tick.mem (base + hdrStage) = stg := hout_hdr hdrStage (by decide) (by decide)
      have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc := hout_hdr hdrNSrc (by decide) (by decide)
      have hnD_t : s_tick.mem (base + hdrNDst) = nDst := hout_hdr hdrNDst (by decide) (by decide)
      have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc := hout_hdr hdrMSrc (by decide) (by decide)
      have hmD_t : s_tick.mem (base + hdrMDst) = mDst := hout_hdr hdrMDst (by decide) (by decide)
      have hpad_t : s_tick.mem (base + hdrPad) = pad := hout_hdr hdrPad (by decide) (by decide)
      have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
        hout_hdr hdrItemLo (by decide) (by decide)
      have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
        hout_hdr hdrItemHi (by decide) (by decide)
      have hqL_t : s_tick.mem (base + hdrQLo) = qLo := hout_hdr hdrQLo (by decide) (by decide)
      have hqH_t : s_tick.mem (base + hdrQHi) = qHi := hout_hdr hdrQHi (by decide) (by decide)
      have hpgH_t : dualPgHost c V w base nLive s_tick.mem = pgH := by
        dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
        rw [hnD_t, hnS_t, hst_t, hpad_t, hibH_t, hqH_t]
      obtain ⟨hsl_s_hi, hsl_67_hi⟩ := hsl_pres s_tick.mem
        (fun a ha => by
          rw [hm_eq, Function.update_of_ne (fun he => ha
            ⟨by dsimp only [hdrCur] at he; clear *- he; omega,
             by dsimp only [hdrCur] at he; clear *- he; omega⟩)])
        hst_t hnS_t hnD_t hpad_t (by rw [hph_t]; decide)
      have hu_t : extractPageUnperm pgH s_tick.mem = extractPageUnperm pgH s2.mem :=
        extractPageUnperm_congr hw_pos fun a ha => by
          have ha210 := (hdisj_pg a ha).1
          rw [hm_eq, Function.update_of_ne (by dsimp only [hdrCur]; clear *- ha210; omega)]
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hnS_t, hph_t, ite_eq_right (by decide : 6 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
      · rw [hph_t, ite_eq_right (by decide : ¬(6 < 2)), ite_eq_right (by decide : 6 ≠ 2),
          ite_eq_left (by decide : 6 ≤ 10), hibH_t, hqH_t, hfr_tick]
        refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
            base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_hdr off (by dsimp only [hdrCur]; clear *- hoff; omega) (by clear *- hoff; omega)
            live_eq := (hout_hdr hdrLive (by decide) (by decide)).trans hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]; decide
            stg_le := by dsimp only; rw [hst_t]; exact hstg_le
            mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [Nat.add_assoc]
                exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd]; clear *- hk; omega)
            nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                  nDst_zero := fun hz => by
                    dsimp only at hz ⊢
                    obtain ⟨h1, h2, _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                    rw [hnS_t, hst_t, hph_t]
                    exact ⟨h1, h2, by decide, by decide, by decide⟩
                  stg_one := fun hs1 => by
                    dsimp only at hs1 ⊢; rw [hnD_t, hph_t]
                    exact ⟨(hsched.stg_one (hst_t.symm.trans hs1)).1, by decide, by decide⟩
                  post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := by dsimp only; simpa using hsched.drift_hi
                  drift_lo := by dsimp only; simpa using hsched.drift_lo
                  ibLo_eq := by
                    dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                    simpa only [hp6, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
                  qLo_eq := by
                    dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                    simpa only [hp6, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
                  ph1 := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
                  ge2 := fun _ => by
                    dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                    · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                        rw [Nat.add_assoc]
                        exact hout_hdr (hdrDstOd + k)
                          (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd]; clear *- hk; omega)
                    · obtain ⟨hl, he, hp⟩ := hd_logs hd
                      exact ⟨(hout_hdr hdrLogN (by decide) (by decide)).trans hl,
                        (hout_hdr hdrEll (by decide) (by decide)).trans he,
                        (hout_hdr hdrPgB (by decide) (by decide)).trans hp⟩
                  ph2 := fun h2 => absurd (hph_t.symm.trans h2) (by decide)
                  ph3_10 := fun _ => by
                    dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                  ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
                  budget := by
                    dsimp only
                    rw [hnS_t, hpgH_t, hst_t, hph_t, hnD_t, hmD_t, hcur_t, hcur'_step]
                    unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                    simp only [hp6, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
                      ↓reduceIte] at hb_tot ⊢
                    have h2t := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                    dsimp only [bulkBatchWhp] at hcur'_step ⊢
                    rw [← hmp_eq] at *
                    generalize max (whpThreshold c) nSrc = nRef at hb_tot h2t ⊢
                    have hdiv_step : (pgM.maxPages - (cur + 1024)) / 1024 + 1 ≤
                        (pgM.maxPages - cur) / 1024 := by
                      have hlt' : cur + 1024 < pgM.maxPages := hcur'_step ▸ hlt_mp
                      clear *- hlt'; omega
                    refine ⟨by clear *- h2t; omega, ?_, ?_⟩
                    · clear *- hb_tot hdiv_step; omega
                    · clear *- hb_tot h2t hdiv_step; omega }
            pad_fits := by
              dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 6 ≠ 0)]
              simpa only [hp6, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
            ph1_inv := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
            ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
            ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
            pDst_pre := fun ⟨_, h5⟩ => absurd (hph_t ▸ h5) (by decide)
            ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
            ph6_inv := fun _ => by
              dsimp only; rw [hpgH_t, hcur_t]
              refine ⟨hmp_eq ▸ hlt_mp.le, fun vp hvp => ?_⟩
              have hp_eq : extractPagePair pgH s_tick.mem = (extractPageUnperm pgH s_tick.mem).st :=
                rfl
              rw [hp_eq, hu_t]; exact hdir_s2 vp hvp
            ph7_inv := fun h7 => absurd (hph_t.symm.trans h7) (by decide)
            ph8_inv := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
            ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
            sl_le7 := fun _ => by
              dsimp only; rw [hst_t, hph_t, hnS_t, hnD_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t]
              have hcap_eq : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
                unfold dualCapSrc; rw [hst_t, hnS_t, hnD_t]
              rw [hcap_eq]
              exact ⟨hcap_s, hdict_s, hsl_s_hi, fun _ hc => hevs_s (by clear *- hp6; omega) hc⟩
            sl_67 := fun _ => by
              dsimp only; rw [hnD_t, hibH_t, hqH_t]
              exact ⟨hsl_67_hi.1, fun hd =>
                ⟨(hsl_67.2 hd).1, (hsl_67.2 hd).2.1, (hsl_67.2 hd).2.2.1, hsl_67_hi.2 hd⟩⟩
            sl_8 := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            sl_ge9 := fun h9 => absurd (hph_t ▸ h9) (by decide) }
    · -- `6 → 7`: `cur' = pgM.maxPages`
      have hcur'_mp : cur' = pgH.maxPages := by
        rw [← hmp_eq]; have := hcur'_eq ▸ min_le_left pgM.maxPages (cur + bulkBatchWhp)
        clear *- hlt_mp this; omega
      set qSnap := if nLive < pgH.pgB + (pgH.pgB + pgH.pgB / 2) then 0
        else (nLive - (pgH.pgB + pgH.pgB / 2)) / pgH.pgB
      have hm_eq : s_tick.mem =
          Function.update (Function.update (Function.update
            (Function.update s2.mem (base + hdrNSnap) nLive)
            (base + hdrQSnap) qSnap)
            (base + hdrCur) 0)
            (base + hdrPhase) 7 := by
        rw [hst_bg, hst_td, ite_eq_right hlt_mp, hpgB_eq]
      have hout_hdr : ∀ off, off ≠ hdrNSnap → off ≠ hdrQSnap → off ≠ hdrCur → off ≠ hdrPhase →
          off < 192 → s_tick.mem (base + off) = s.mem (base + off) :=
        fun off h1 h2 h3 h4 h192 => by
          rw [hm_eq, Function.update_of_ne (base_add_ne h4),
            Function.update_of_ne (base_add_ne h3),
            Function.update_of_ne (base_add_ne h2),
            Function.update_of_ne (base_add_ne h1)]
          exact hs2_pg (base + off) (fun hpg => by
            have := (hdisj_pg _ hpg).1; clear *- h192 this; omega)
      have hph_t : s_tick.mem (base + hdrPhase) = 7 := by rw [hm_eq]; exact Function.update_self ..
      have hcur_t : s_tick.mem (base + hdrCur) = 0 := by
        rw [hm_eq, Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
      have hqs_t : s_tick.mem (base + hdrQSnap) = qSnap := by
        rw [hm_eq, Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
      have hns_t : s_tick.mem (base + hdrNSnap) = nLive := by
        rw [hm_eq, Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (base_add_ne (by decide)),
          Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
      have hst_t : s_tick.mem (base + hdrStage) = stg :=
        hout_hdr hdrStage (by decide) (by decide) (by decide) (by decide) (by decide)
      have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc :=
        hout_hdr hdrNSrc (by decide) (by decide) (by decide) (by decide) (by decide)
      have hnD_t : s_tick.mem (base + hdrNDst) = nDst :=
        hout_hdr hdrNDst (by decide) (by decide) (by decide) (by decide) (by decide)
      have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc :=
        hout_hdr hdrMSrc (by decide) (by decide) (by decide) (by decide) (by decide)
      have hmD_t : s_tick.mem (base + hdrMDst) = mDst :=
        hout_hdr hdrMDst (by decide) (by decide) (by decide) (by decide) (by decide)
      have hpad_t : s_tick.mem (base + hdrPad) = pad :=
        hout_hdr hdrPad (by decide) (by decide) (by decide) (by decide) (by decide)
      have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
        hout_hdr hdrItemLo (by decide) (by decide) (by decide) (by decide) (by decide)
      have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
        hout_hdr hdrItemHi (by decide) (by decide) (by decide) (by decide) (by decide)
      have hqL_t : s_tick.mem (base + hdrQLo) = qLo :=
        hout_hdr hdrQLo (by decide) (by decide) (by decide) (by decide) (by decide)
      have hqH_t : s_tick.mem (base + hdrQHi) = qHi :=
        hout_hdr hdrQHi (by decide) (by decide) (by decide) (by decide) (by decide)
      have hpgH_t : dualPgHost c V w base nLive s_tick.mem = pgH := by
        dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
        rw [hnD_t, hnS_t, hst_t, hpad_t, hibH_t, hqH_t]
      obtain ⟨hsl_s_hi, hsl_67_hi⟩ := hsl_pres s_tick.mem
        (fun a ha => by
          rw [hm_eq]
          iterate 4 rw [Function.update_of_ne (fun he => ha
            ⟨by dsimp only [hdrNSnap, hdrQSnap, hdrCur, hdrPhase] at he; clear *- he; omega,
             by dsimp only [hdrNSnap, hdrQSnap, hdrCur, hdrPhase] at he; clear *- he; omega⟩)])
        hst_t hnS_t hnD_t hpad_t (by rw [hph_t]; decide)
      have hu_t : extractPageUnperm pgH s_tick.mem = extractPageUnperm pgH s2.mem :=
        extractPageUnperm_congr hw_pos fun a ha => by
          have ha210 := (hdisj_pg a ha).1
          rw [hm_eq]
          iterate 4 rw [Function.update_of_ne (by
            dsimp only [hdrNSnap, hdrQSnap, hdrCur, hdrPhase]; clear *- ha210; omega)]
      refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
      · rw [hnS_t, hph_t, ite_eq_right (by decide : 7 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
      · rw [hph_t, ite_eq_right (by decide : ¬(7 < 2)), ite_eq_right (by decide : 7 ≠ 2),
          ite_eq_left (by decide : 7 ≤ 10), hibH_t, hqH_t, hfr_tick]
        refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
        exact
          { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
            wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
            base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
            hdr := rootStaticHeader_congr hhdr fun off hoff =>
              hout_hdr off (by dsimp only [hdrNSnap]; clear *- hoff; omega)
                (by dsimp only [hdrQSnap]; clear *- hoff; omega)
                (by dsimp only [hdrCur]; clear *- hoff; omega)
                (by dsimp only [hdrPhase]; clear *- hoff; omega)
                (by clear *- hoff; omega)
            live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide) (by decide)
              (by decide)).trans hlive_eq
            live_le := hlive_le
            ph_le := by dsimp only; rw [hph_t]; decide
            stg_le := by dsimp only; rw [hst_t]; exact hstg_le
            mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
            cache_src := by
              dsimp only; rw [hnS_t]
              exact hostCacheValid_congr_mem hcache_s fun k hk => by
                rw [Nat.add_assoc]
                exact hout_hdr (hdrSrcOd + k)
                  (by dsimp only [hdrSrcOd, hdrNSnap]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrQSnap]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
                  (by dsimp only [hdrSrcOd]; clear *- hk; omega)
            nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
            sched := by
              dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
              refine
                { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                  nDst_zero := fun hz => by
                    dsimp only at hz ⊢
                    obtain ⟨h1, h2, _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                    rw [hnS_t, hst_t, hph_t]
                    exact ⟨h1, h2, by decide, by decide, by decide⟩
                  stg_one := fun hs1 => by
                    dsimp only at hs1 ⊢; rw [hnD_t, hph_t]
                    exact ⟨(hsched.stg_one (hst_t.symm.trans hs1)).1, by decide, by decide⟩
                  post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
                  trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                  drift_hi := by dsimp only; simpa using hsched.drift_hi
                  drift_lo := by dsimp only; simpa using hsched.drift_lo
                  ibLo_eq := by
                    dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                    simpa only [hp6, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
                  qLo_eq := by
                    dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                    simpa only [hp6, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
                  ph1 := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
                  ge2 := fun _ => by
                    dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                    refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                    · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                        rw [Nat.add_assoc]
                        exact hout_hdr (hdrDstOd + k)
                          (by dsimp only [hdrDstOd, hdrNSnap]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrQSnap]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                          (by dsimp only [hdrDstOd]; clear *- hk; omega)
                    · obtain ⟨hl, he, hp⟩ := hd_logs hd
                      exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide) (by decide)
                          (by decide)).trans hl,
                        (hout_hdr hdrEll (by decide) (by decide) (by decide) (by decide)
                          (by decide)).trans he,
                        (hout_hdr hdrPgB (by decide) (by decide) (by decide) (by decide)
                          (by decide)).trans hp⟩
                  ph2 := fun h2 => absurd (hph_t.symm.trans h2) (by decide)
                  ph3_10 := fun _ => by
                    dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                  ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
                  budget := by
                    dsimp only
                    rw [hnS_t, hpgH_t, hst_t, hph_t, hnD_t, hmD_t, hcur_t]
                    unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                    simp only [hp6, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
                      ↓reduceIte] at hb_tot ⊢
                    have h2t := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                    have hpgH_eq_b : pgH.pgB = pageSizeWhp nHost := rfl
                    have htail_le : (8 * pgH.pgB - 0) / 128 ≤
                        (8 * max 32 (Nat.log 2 (2 * max (whpThreshold c) nSrc) + 4)) / 128 := by
                      rw [Nat.sub_zero, hpgH_eq_b]
                      exact Nat.div_le_div_right (Nat.mul_le_mul_left 8 hpgB_ref)
                    generalize max (whpThreshold c) nSrc = nRef at hb_tot h2t htail_le ⊢
                    refine ⟨by clear *- h2t; omega, ?_, ?_⟩ <;>
                      (clear *- hb_tot h2t htail_le; omega) }
            pad_fits := by
              dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 7 ≠ 0)]
              simpa only [hp6, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
            ph1_inv := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
            ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
            ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
            pDst_pre := fun ⟨_, h5⟩ => absurd (hph_t ▸ h5) (by decide)
            ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
            ph6_inv := fun h6 => absurd (hph_t.symm.trans h6) (by decide)
            ph7_inv := fun _ => by
              dsimp only; rw [hpgH_t, hns_t, hqs_t, hcur_t]
              have hnH_t : dualNHost base s_tick.mem = nHost := by
                dsimp only [nHost]; unfold dualNHost; rw [hnD_t, hnS_t]
              rw [hnH_t]
              have hpg32 : 32 ≤ pgH.pgB := hv_fr.2.2.2.2.2.1
              refine ⟨hnL_h, rfl, fun vp hvp => ?_,
                ⟨0, rfl, by clear *- hpg32; omega, le_rfl, le_rfl⟩,
                fun _ hlt0 => absurd hlt0 (Nat.not_lt_zero _)⟩
              have hp_eq : extractPagePair pgH s_tick.mem = (extractPageUnperm pgH s_tick.mem).st :=
                rfl
              rw [hp_eq, hu_t]; exact hdir_s2 vp (hcur'_mp ▸ hvp)
            ph8_inv := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
            ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
            sl_le7 := fun _ => by
              dsimp only; rw [hst_t, hph_t, hnS_t, hnD_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t]
              have hcap_eq : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
                unfold dualCapSrc; rw [hst_t, hnS_t, hnD_t]
              rw [hcap_eq]
              exact ⟨hcap_s, hdict_s, hsl_s_hi, fun _ hc => hevs_s (by clear *- hp6; omega) hc⟩
            sl_67 := fun _ => by
              dsimp only; rw [hnD_t, hibH_t, hqH_t]
              exact ⟨hsl_67_hi.1, fun hd =>
                ⟨(hsl_67.2 hd).1, (hsl_67.2 hd).2.1, (hsl_67.2 hd).2.2.1, hsl_67_hi.2 hd⟩⟩
            sl_8 := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
            sl_ge9 := fun h9 => absurd (hph_t ▸ h9) (by decide) }

/-! ## Section 3: Phase `7` (`tickInitTailProg` + `finishInitTailProg`) Specification -/

/-- Helper certifying `extractPageUnperm pgH sb.mem` after `pageInitScalarsBandProg` at the end
of Phase `7`. -/
private theorem band_unperm_valid_of_tailDone {pgH : PageArenaLayout} {qSnap nLive : ℕ}
    {s2 sb : Memory.State}
    (hw_pos : 0 < pgH.w) (hpg32 : 32 ≤ pgH.pgB) (hmp4 : 4 ≤ pgH.maxPages)
    (h32_od : 32 ≤ pgH.offDir) (hod_ot : pgH.offDir ≤ pgH.offTail)
    (hq_lt_mp : qSnap < pgH.maxPages)
    (hq_mul : qSnap * pgH.pgB ≤ nLive)
    (hr_hi : 4 * (nLive - qSnap * pgH.pgB) ≤ 11 * pgH.pgB)
    (hr_lo : 0 < qSnap → 5 * pgH.pgB ≤ 4 * (nLive - qSnap * pgH.pgB))
    (hsb_def : (Memory.spec 0).clientState s2
      (pageInitScalarsBandProg ((pgH.metaBase, pgH.pgB), (qSnap, nLive - qSnap * pgH.pgB))) = sb)
    (hdir_s2 : ∀ vp < pgH.maxPages,
      (extractPagePair pgH s2.mem).pageOf false vp = vp ∧
      (extractPagePair pgH s2.mem).pageOf true vp = 0 ∧
      (extractPagePair pgH s2.mem).ownerSide vp = false ∧
      (extractPagePair pgH s2.mem).ownerVp vp = vp)
    (htail_s2 : ∀ idx < 8 * pgH.pgB,
      (idx < 4 * pgH.pgB →
        (extractPagePair pgH s2.mem).tailRes false idx =
          (qSnap * pgH.pgB + idx) % (8 * pgH.pgB) ∧
        (extractPagePair pgH s2.mem).tailRes true idx =
          (qSnap * pgH.pgB + idx) % (8 * pgH.pgB)) ∧
      (extractPagePair pgH s2.mem).tailOwnerSide idx = false ∧
      (extractPagePair pgH s2.mem).tailOwnerRing idx =
        (idx + 8 * pgH.pgB - (qSnap * pgH.pgB) % (8 * pgH.pgB)) % (8 * pgH.pgB)) :
    let u := extractPageUnperm pgH sb.mem
    u.Valid ∧ u.cleanPhase = 0 ∧ u.st.pageSize = pgH.pgB ∧
    u.st.totalPages = qSnap ∧ u.st.virtLen false = nLive ∧ u.st.virtLen true = 0 ∧
    (∀ idx < nLive, u.toPhys false idx = idx) ∧
    (∀ addr, ¬(pgH.metaBase + 18 ≤ addr ∧ addr < pgH.metaBase + 32) → sb.mem addr = s2.mem addr) :=
  by
  dsimp only
  have hsb_sp := pageInitScalarsBandProg_spec pgH.metaBase pgH.pgB qSnap
    (nLive - qSnap * pgH.pgB) s2
  dsimp only at hsb_sp
  rw [hsb_def] at hsb_sp
  have hdir_eq : ∀ idx < 4 * pgH.maxPages,
      readPacked (pgH.metaBase + pgH.offDir) pgH.ptrB pgH.w sb.mem idx =
        readPacked (pgH.metaBase + pgH.offDir) pgH.ptrB pgH.w s2.mem idx :=
    fun idx hidx => readPacked_congr hw_pos
      (fun a ha => hsb_sp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a
        (by have ha1 := ha.1; clear *- ha1 h32_od; omega)) hidx
  have htail_eq : ∀ idx < 16 * pgH.pgB,
      readPacked (pgH.metaBase + pgH.offTail) pgH.ptrB pgH.w sb.mem idx =
        readPacked (pgH.metaBase + pgH.offTail) pgH.ptrB pgH.w s2.mem idx :=
    fun idx hidx => readPacked_congr hw_pos
      (fun a ha => hsb_sp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a
        (by have ha1 := ha.1; clear *- ha1 h32_od hod_ot; omega)) hidx
  have hpo_b : ∀ side vp, vp < pgH.maxPages →
      (extractPagePair pgH sb.mem).pageOf side vp = if side then 0 else vp :=
    fun side vp hvp => by
      have hp_s2 : (extractPagePair pgH sb.mem).pageOf side vp =
          (extractPagePair pgH s2.mem).pageOf side vp := by
        unfold extractPagePair; dsimp only; rw [ite_eq_left hvp, ite_eq_left hvp]
        cases side <;> exact hdir_eq _ (by dsimp only; clear *- hvp; omega)
      rw [hp_s2]
      cases side <;> [exact (hdir_s2 vp hvp).1; exact (hdir_s2 vp hvp).2.1]
  have hos_b : ∀ P < pgH.maxPages, (extractPagePair pgH sb.mem).ownerSide P = false :=
    fun P hP => by
      have ho_s2 : (extractPagePair pgH sb.mem).ownerSide P =
          (extractPagePair pgH s2.mem).ownerSide P := by
        unfold extractPagePair; dsimp only; rw [ite_eq_left hP, ite_eq_left hP]
        rw [hdir_eq (4 * P + 2) (by clear *- hP; omega)]
      exact ho_s2.trans (hdir_s2 P hP).2.2.1
  have hov_b : ∀ P < pgH.maxPages, (extractPagePair pgH sb.mem).ownerVp P = P :=
    fun P hP => by
      have ho_s2 : (extractPagePair pgH sb.mem).ownerVp P =
          (extractPagePair pgH s2.mem).ownerVp P := by
        unfold extractPagePair; dsimp only; rw [ite_eq_left hP, ite_eq_left hP]
        exact hdir_eq (4 * P + 3) (by clear *- hP; omega)
      exact ho_s2.trans (hdir_s2 P hP).2.2.2
  have htr_b : ∀ side j, j < 4 * pgH.pgB →
      (extractPagePair pgH sb.mem).tailRes side j = (qSnap * pgH.pgB + j) % (8 * pgH.pgB) :=
    fun side j hj => by
      have hj8 : j < 8 * pgH.pgB := by clear *- hj; omega
      have ht_s2 : (extractPagePair pgH sb.mem).tailRes side j =
          (extractPagePair pgH s2.mem).tailRes side j := by
        unfold extractPagePair; dsimp only; rw [ite_eq_left hj, ite_eq_left hj]
        cases side <;> exact htail_eq _ (by dsimp only; clear *- hj; omega)
      rw [ht_s2]
      cases side <;> [exact ((htail_s2 j hj8).1 hj).1; exact ((htail_s2 j hj8).1 hj).2]
  have htos_b : ∀ res < 8 * pgH.pgB, (extractPagePair pgH sb.mem).tailOwnerSide res = false :=
    fun res hres => by
      have ht_s2 : (extractPagePair pgH sb.mem).tailOwnerSide res =
          (extractPagePair pgH s2.mem).tailOwnerSide res := by
        unfold extractPagePair; dsimp only; rw [ite_eq_left hres, ite_eq_left hres]
        rw [htail_eq (8 * pgH.pgB + res) (by clear *- hres; omega)]
      exact ht_s2.trans (htail_s2 res hres).2.1
  have htor_b : ∀ res < 8 * pgH.pgB,
      (extractPagePair pgH sb.mem).tailOwnerRing res =
        (res + 8 * pgH.pgB - (qSnap * pgH.pgB) % (8 * pgH.pgB)) % (8 * pgH.pgB) :=
    fun res hres => by
      have ht_s2 : (extractPagePair pgH sb.mem).tailOwnerRing res =
          (extractPagePair pgH s2.mem).tailOwnerRing res := by
        unfold extractPagePair; dsimp only; rw [ite_eq_left hres, ite_eq_left hres]
        rw [htail_eq (8 * pgH.pgB + res) (by clear *- hres; omega)]
      exact ht_s2.trans (htail_s2 res hres).2.2
  have hv_b := valid_extractPageUnperm_of_band (L := pgH) (mem := sb.mem)
    (q₀ := qSnap) (r_cur := nLive - qSnap * pgH.pgB)
    hpg32 hmp4 hr_hi hr_lo hq_lt_mp
    hsb_sp.2.2.1 hsb_sp.2.2.2.1
    hsb_sp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hsb_sp.2.2.2.2.1
    (by funext b; unfold extractPagePair; dsimp only
        cases b <;> [exact hsb_sp.2.2.2.2.2.1; exact hsb_sp.2.2.2.2.2.2.1])
    (by funext b; unfold extractPagePair; dsimp only
        cases b <;> [exact hsb_sp.2.2.2.2.2.2.2.1; exact hsb_sp.2.2.2.2.2.2.2.2.1])
    (by funext b; unfold extractPagePair; dsimp only
        cases b <;> [exact hsb_sp.2.2.2.2.2.2.2.2.2.1; exact hsb_sp.2.2.2.2.2.2.2.2.2.2.1])
    (by unfold extractPagePair; dsimp only
        rw [hsb_sp.2.2.2.2.2.2.2.2.2.2.2.1, hsb_sp.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hsb_sp.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; rfl)
    hpo_b hos_b hov_b htr_b htos_b htor_b
  dsimp only at hv_b
  have hadd : qSnap * pgH.pgB + (nLive - qSnap * pgH.pgB) = nLive := Nat.add_sub_of_le hq_mul
  rw [hadd] at hv_b
  exact ⟨hv_b.1, hv_b.2.1, hv_b.2.2.1, hv_b.2.2.2.1, hv_b.2.2.2.2.1, hv_b.2.2.2.2.2.1,
    hv_b.2.2.2.2.2.2, hsb_sp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Helper proving `DualPreShrinkInv` for the `7 → 8` (`finishInitTailProg`) branch of Phase `7`.
-/
private theorem tickPhase7_finish_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s s2 s_tick : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp7 : s.mem (base + hdrPhase) = 7)
    (hwf_tick : Memory.WellFormed w s_tick)
    (hfr_tick : s_tick.frontier = s.frontier)
    (hs2_pg : ∀ a, ¬(dualPgHost c V w base (Dictionary.dom s_dict).card s.mem).OwnsMetaAddr a →
      s2.mem a = s.mem a)
    (hctx0_s2 : (Memory.spec 0).clientResult s2 (loadHostCtxProg (base, 0)) =
      (dualPgHost c V w base (Dictionary.dom s_dict).card s.mem).toCtx)
    (hst_tick : s_tick = (Memory.spec 0).clientState s2 (finishInitTailProg base))
    (hband :
      let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
      let qSnap := s.mem (base + hdrQSnap)
      let nLive := (Dictionary.dom s_dict).card
      qSnap * pgH.pgB ≤ nLive ∧
      4 * (nLive - qSnap * pgH.pgB) ≤ 11 * pgH.pgB ∧
      (0 < qSnap → 5 * pgH.pgB ≤ 4 * (nLive - qSnap * pgH.pgB)))
    (hdir_s2 :
      let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
      ∀ vp < pgH.maxPages,
        (extractPagePair pgH s2.mem).pageOf false vp = vp ∧
        (extractPagePair pgH s2.mem).pageOf true vp = 0 ∧
        (extractPagePair pgH s2.mem).ownerSide vp = false ∧
        (extractPagePair pgH s2.mem).ownerVp vp = vp)
    (htail_s2 :
      let pgH := dualPgHost c V w base (Dictionary.dom s_dict).card s.mem
      let qSnap := s.mem (base + hdrQSnap)
      ∀ idx < 8 * pgH.pgB,
        (idx < 4 * pgH.pgB →
          (extractPagePair pgH s2.mem).tailRes false idx =
            (qSnap * pgH.pgB + idx) % (8 * pgH.pgB) ∧
          (extractPagePair pgH s2.mem).tailRes true idx =
            (qSnap * pgH.pgB + idx) % (8 * pgH.pgB)) ∧
        (extractPagePair pgH s2.mem).tailOwnerSide idx = false ∧
        (extractPagePair pgH s2.mem).tailOwnerRing idx =
          (idx + 8 * pgH.pgB - (qSnap * pgH.pgB) % (8 * pgH.pgB)) % (8 * pgH.pgB)) :
    let slotDst' : SlotLatent c U V :=
      if s.mem (base + hdrNDst) = 0 then SlotLatent.emptySmall c U V else L.slotDst
    DualPreShrinkInv c U V w base s_dict { L with slotDst := slotDst', elapsed := L.elapsed + 1 }
      s_tick := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src
  have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  obtain ⟨hth_h, hnL_h, _, hmb_ib, _, _, hv_hi, hv_fr, _⟩ :=
    dualPgHost_eval_valid h (by clear *- hp7; omega) (by clear *- hp7; omega)
  have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) h
    (by clear *- hp7; omega) (by clear *- hp7; omega)
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp7; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_hi⟩ := hsched.ph3_10 ⟨by clear *- hp7; omega, by clear *- hp7; omega⟩
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp7; omega)
  obtain ⟨_, hb_tot, hb_el⟩ := hsched.budget
  obtain ⟨hcap_s, hdict_s, hsl_s, hevs_s⟩ := h.sl_le7 (by clear *- hp7; omega)
  have hsl_67 := h.sl_67 (Or.inr hp7)
  obtain ⟨_, hvb_w, _, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h
  have hw_pos : 0 < w := by clear *- hw11; omega
  have hel_cap := active_elapsed_lt_capSrc h (by clear *- hp7; omega)
  have hnL_ref := (active_nLive_le_two_nRef hsched.post_trig hsched.trig_cap hsched.drift_hi
    hsched.drift_lo (by clear *- hb_el; simp only [↓reduceIte]; omega) hlive_le).2
  set nLive := (Dictionary.dom s_dict).card
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
  set qSnap := s.mem (base + hdrQSnap)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set nHost := dualNHost base s.mem
  set mbHost := dualMbHost base s.mem
  set pgH := dualPgHost c V w base nLive s.mem
  have hh_ofCtx : PageArenaLayout.ofCtx pgH.toCtx = pgH := PageArenaLayout.ofCtx_toCtx pgH
  have hpg32 : 32 ≤ pgH.pgB := hv_fr.2.2.2.2.2.1
  have hmp4 : 4 ≤ pgH.maxPages := hv_fr.2.2.2.2.2.2.2.1
  have h32_od : 32 ≤ pgH.offDir := hv_fr.2.2.2.2.2.2.2.2.2.2.2.1
  have hs2_hdr : ∀ off < 192, s2.mem (base + off) = s.mem (base + off) := fun off h192 =>
    hs2_pg (base + off) (fun hpg => by have := (hdisj_pg _ hpg).1; clear *- h192 this; omega)
  have hf_ev := finishInitTailProg_eval base s2
  change _ ∧ _ at hf_ev
  rw [hctx0_s2, hh_ofCtx, hs2_hdr hdrStage (by decide), hs2_hdr hdrNDst (by decide),
    hs2_hdr hdrLive (by decide), hlive_eq, hs2_hdr hdrQSnap (by decide)] at hf_ev
  obtain ⟨hst_fin, _⟩ := hf_ev
  have hibHi_ge : base + 196 ≤ ibHi := by rw [hibHi_eq]; split_ifs <;> (clear *-; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    have hle1 : s.frontier ≤ ibHi + pairStreamWords (nLive + 1) qHi vB w := hfr_hi_hi
    have hstep := pairStreamWords_succ_le_add_two (n := nLive) (qb := qHi) (vb := vB) (w := w)
      hw_pos (by clear *- hqHi_w hvb_w; omega)
    dsimp only [hiFr, bulkBatchWhp]; clear *- hle1 hstep; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
    have hib_pad := (dualCoreInv_ib_fits h).2.2.2.2.2.1
    rw [ite_eq_right (by clear *- hp7; omega)] at hib_pad
    exact hfr_hi_hi.trans hib_pad
  have hio_src_eq : activeSrcIo c w vB base stg 7 nSrc nDst pad ibLo qLo ibHi qHi nLive =
      directSlotIo w vB base ibHi qHi nLive := rfl
  rw [hp7, hio_src_eq] at hsl_s
  obtain ⟨hq_mul, hr_hi, hr_lo⟩ := hband
  have hq_lt_mp : qSnap < pgH.maxPages := by
    have hle_div : qSnap ≤ nHost / pgH.pgB :=
      (Nat.le_div_iff_mul_le (by clear *- hpg32; omega)).mpr (hq_mul.trans hnL_h)
    have hmp_def : pgH.maxPages = nHost / pgH.pgB + 4 := rfl
    rw [hmp_def]; clear *- hle_div; omega
  set slotDst' : SlotLatent c U V := if nDst = 0 then SlotLatent.emptySmall c U V else L.slotDst
  set L' : DualLatent c U V := { L with slotDst := slotDst', elapsed := L.elapsed + 1 }
  have h7_10 : s.mem (base + hdrPhase) < 10 := by clear *- hp7; omega
  set pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
  set pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
  obtain ⟨sb, hsb_def⟩ : ∃ sb, (Memory.spec 0).clientState s2
    (pageInitScalarsBandProg ((pgH.metaBase, pgH.pgB), (qSnap, nLive - qSnap * pgH.pgB))) = sb :=
    ⟨_, rfl⟩
  obtain ⟨s3, hs3_def⟩ : ∃ s3,
    (Memory.spec 0).clientState sb (setSlotIoProg (pSrc, ((1, 0), pgH.toCtx))) = s3 := ⟨_, rfl⟩
  obtain ⟨s4, hs4_def⟩ : ∃ s4, (Memory.spec 0).clientState s3
    (if nDst = 0 then writeSmallParamTableProg ((pDst, base + hdrSmallMeta1), ((1, 1), pgH.toCtx))
     else setSlotIoProg (pDst, ((1, 1), pgH.toCtx))) = s4 := ⟨_, rfl⟩
  set rem8 := nLive / itemBatchWhp + 1
  have hm_eq : s_tick.mem =
      Function.update (Function.update s4.mem (base + hdrRem) rem8) (base + hdrPhase) 8 := by
    rw [hst_tick, hst_fin]
    dsimp only [stg, nDst, qSnap, pSrc, pDst, rem8]
    rw [hsb_def, hs3_def, hs4_def]
  have hmb_ge192 : base + 192 ≤ pgH.metaBase := by
    change base + 192 ≤ mbHost; dsimp only [mbHost]; unfold dualMbHost
    split_ifs <;> (clear *-; omega)
  have hm32_ib : pgH.metaBase + 32 ≤ ibHi := by
    have h32 := (epochMeta_offsets_le (w := w) hth_h.1).1.trans
      ((epochMeta_offsets_le (w := w) hth_h.1).2.1.trans
        ((epochMeta_offsets_le (w := w) hth_h.1).2.2.1.trans
          (epochMeta_offsets_le (w := w) hth_h.1).2.2.2))
    change mbHost + 32 ≤ ibHi; clear *- h32 hmb_ib; omega
  obtain ⟨hu_v, hu_cph, hu_ps, hu_tp, hu_vlf, hu_vlt, hu_id, hsb_out⟩ :=
    band_unperm_valid_of_tailDone (pgH := pgH) hw_pos hpg32 hmp4 h32_od (Nat.le_add_right _ _)
      hq_lt_mp hq_mul hr_hi hr_lo hsb_def hdir_s2 htail_s2
  clear hsb_def
  have hpS_rng : base + 64 ≤ pSrc ∧ pSrc + 64 ≤ base + 192 := by
    dsimp only [pSrc, hdrPBase0, hdrPBase1]; split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
  have hpD_rng : base + 64 ≤ pDst ∧ pDst + 64 ≤ base + 192 := by
    dsimp only [pDst, hdrPBase0, hdrPBase1]; split_ifs <;> (clear *-; exact ⟨by omega, by omega⟩)
  have hpSD_disj : pDst + 64 ≤ pSrc ∨ pSrc + 64 ≤ pDst := by
    dsimp only [pSrc, pDst, hdrPBase0, hdrPBase1]
    split_ifs <;> [exact Or.inr (by clear *-; omega); exact Or.inl (by clear *-; omega)]
  have h4_s3_out : ∀ a, ¬(pDst ≤ a ∧ a < pDst + 61) → s4.mem a = s3.mem a := fun a ha => by
    rw [← hs4_def]
    by_cases hd0 : nDst = 0
    · rw [ite_eq_left hd0]
      exact (writeSmallParamTableProg_spec pDst
        ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3).2.2.2 a ha
    · rw [ite_eq_right hd0]
      exact (setSlotIoProg_frame pDst ((1, 1), pgH.toCtx)).mem_outside s3 a
        (by clear *- ha; omega)
  have htick_sb_out : ∀ a, a ≠ base + hdrPhase → a ≠ base + hdrRem →
      ¬(base + 64 ≤ a ∧ a < base + 192) → s_tick.mem a = sb.mem a := fun a h1 h2 h64 => by
    rw [hm_eq, Function.update_of_ne h1, Function.update_of_ne h2,
      h4_s3_out a (by clear *- h64 hpD_rng; omega), ← hs3_def]
    exact (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb a
      (by clear *- h64 hpS_rng; omega)
  have hout_hdr : ∀ off, off ≠ hdrPhase → off ≠ hdrRem → off < 64 →
      s_tick.mem (base + off) = s.mem (base + off) := fun off h1 h2 h64 => by
    rw [htick_sb_out (base + off) (base_add_ne h1) (base_add_ne h2) (by clear *- h64; omega),
      hsb_out (base + off) (by clear *- h64 hmb_ge192; omega)]
    exact hs2_hdr off (by clear *- h64; omega)
  have hph_t : s_tick.mem (base + hdrPhase) = 8 := by rw [hm_eq]; exact Function.update_self ..
  have hrem_t : s_tick.mem (base + hdrRem) = rem8 := by
    rw [hm_eq, Function.update_of_ne (base_add_ne (by decide))]; exact Function.update_self ..
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
  have hpgH_t : dualPgHost c V w base nLive s_tick.mem = pgH := by
    dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
    rw [hnD_t, hnS_t, hst_t, hpad_t, hibH_t, hqH_t]
  have hu_tick_eq : extractPageUnperm pgH s_tick.mem = extractPageUnperm pgH sb.mem :=
    extractPageUnperm_congr hw_pos fun a ha => by
      have ha210 := (hdisj_pg a ha).1
      exact htick_sb_out a (by dsimp only [hdrPhase]; clear *- ha210; omega)
        (by dsimp only [hdrRem]; clear *- ha210; omega) (by clear *- ha210; omega)
  have har_tick_eq : arenaPairAt pgH s_tick.mem = arenaPairAt pgH s.mem := by
    funext p
    have hitem : ∀ a, ibHi ≤ a → s_tick.mem a = s.mem a := fun a ha => by
      rw [htick_sb_out a (by dsimp only [hdrPhase]; clear *- ha hibHi_ge; omega)
          (by dsimp only [hdrRem]; clear *- ha hibHi_ge; omega) (by clear *- ha hibHi_ge; omega),
        hsb_out a (by clear *- ha hm32_ib; omega)]
      exact hs2_pg a (fun hpg => absurd ha (Nat.not_le_of_gt (hdisj_pg a hpg).2.1))
    unfold arenaPairAt pairQuotAt pairValAt readBitSlice
    change ( _, _ ) = ( _, _ )
    have hib_pg : pgH.itemBase = ibHi := rfl
    rw [hib_pg, hitem _ (Nat.le_add_right _ _), hitem _ (by clear *-; omega),
      hitem _ (Nat.le_add_right _ _), hitem _ (by clear *-; omega)]
  rw [← hu_tick_eq] at hu_v hu_cph hu_ps hu_tp hu_vlf hu_vlt hu_id
  have hti_eq : (extractPageUnperm pgH s_tick.mem).st.totalItems = nLive := by
    unfold PagePairState.totalItems; rw [hu_vlf, hu_vlt, Nat.add_zero]
  have hio0_inv : (pagedSlotIo 0 pgH).StateInv nLive 0 s_tick.mem := by
    unfold SlotIoLayout.StateInv pagedSlotIo SlotIoLayout.side
    simp only [Nat.reduceEqDiff, ne_eq, not_true_eq_false, decide_false, ↓reduceIte]
    exact ⟨hu_v, hu_ps, hu_tp ▸ hq_lt_mp, hti_eq.le, hu_vlf,
      fun h0 => absurd (hu_cph ▸ h0) (Nat.lt_irrefl 0), by rw [hu_cph]; decide⟩
  have hio1_inv : (pagedSlotIo 1 pgH).StateInv 0 0 s_tick.mem := by
    unfold SlotIoLayout.StateInv pagedSlotIo SlotIoLayout.side
    simp only [ne_eq, one_ne_zero, not_false_eq_true, decide_true, ↓reduceIte]
    exact ⟨hu_v, hu_ps, hu_tp ▸ hq_lt_mp, hti_eq.le, hu_vlt,
      fun _ => trivial, by rw [hu_cph]; decide⟩
  have hown_pg_ge : ∀ a, pgH.OwnsAddr a → base + 210 ≤ a := fun a ha => by
    rcases ha with hm | hi
    · exact (hdisj_pg a hm).1
    · have hi1 := hi.1; change ibHi ≤ a at hi1
      have h210 : base + 210 ≤ ibHi := by clear *- hmb_ge192 hm32_ib; omega
      clear *- hi1 h210; omega
  have hnSide_s : s.mem (dualMbSrc base s.mem + 1) = nLive := by
    rw [hsl_s.mem_nSide_eq, ← dom_toDictState_card (V := V), hdict_s]
  have hpS_vals := setSlotIoProg_mem_vals pSrc (pagedSlotIo 0 pgH) sb
  dsimp only at hpS_vals
  rw [show (pagedSlotIo 0 pgH).toCtx = ((1, 0), pgH.toCtx) from rfl, hs3_def] at hpS_vals
  have hpS_tick_s3 : ∀ k < 64, s_tick.mem (pSrc + k) = s3.mem (pSrc + k) := fun k hk => by
    rw [hm_eq, Function.update_of_ne (by dsimp only [hdrPhase]; clear *- hpS_rng; omega),
      Function.update_of_ne (by dsimp only [hdrRem]; clear *- hpS_rng; omega)]
    exact h4_s3_out (pSrc + k) (by clear *- hpSD_disj hk; omega)
  have hm_nonpg_eq : ∀ a,
      (slotOwnsNonPageMeta c w (dualMbSrc base s.mem) (dualCapSrc base s.mem) a ∨
       slotOwnsNonPageMeta c w (dualMbDst base s.mem) nDst a) →
      s_tick.mem a = s.mem a := fun a ha => by
    have hn_pg : ¬pgH.OwnsMetaAddr a := fun hpg => by
      rcases ha with hs | hd
      · exact (hdisj_pg a hpg).2.2.1 hs
      · exact (hdisj_pg a hpg).2.2.2 hd
    have ha48 : base + 48 ≤ a ∧ ¬(base + 64 ≤ a ∧ a < base + 192) := by
      rcases ha with hs | hd
      · rcases slotOwnsNonPageMeta_src_range rfl
          (fun hst_nz hd0 => hst_nz (hsched.nDst_zero hd0).2.1) hs with
          ⟨h1, h2⟩ | h192
        · exact ⟨h1, by clear *- h2; omega⟩
        · exact ⟨by clear *- h192; omega, by clear *- h192; omega⟩
      · unfold slotOwnsNonPageMeta dualMbDst at hd
        rw [ite_eq_left h7_10] at hd
        by_cases hd0 : nDst = 0
        · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte, ne_eq,
            not_true_eq_false, false_and, or_false] at hd
          dsimp only [hdrSmallMeta1] at hd; clear *- hd; exact ⟨by omega, by omega⟩
        · simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte] at hd
          rcases hd with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;>
            (split_ifs at h1 <;> (clear *- h1; exact ⟨by omega, by omega⟩))
    rw [htick_sb_out a (by dsimp only [hdrPhase]; clear *- ha48; omega)
        (by dsimp only [hdrRem]; clear *- ha48; omega) ha48.2,
      hsb_out a (fun h18 => hn_pg (Or.inl h18))]
    exact hs2_pg a hn_pg
  have hsl_src_8 : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
      (dualMbSrc base s_tick.mem) (pagedSlotIo 0 pgH) 0 true L.slotSrc s_tick.mem := by
    have hpS_eq : dualPSrc base s_tick.mem = pSrc := by unfold dualPSrc; rw [hst_t]
    have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
      unfold dualMbSrc; rw [hst_t, hnS_t, hpad_t]
    have hpS_old : dualPSrc base s.mem = pSrc := rfl
    rw [hpS_old] at hsl_s
    rw [hpS_eq, hmS_mb]
    have hsl_s_hi : EpochSlotInv c U V w hiFr pSrc (dualMbSrc base s.mem)
        (directSlotIo w vB base ibHi qHi nLive) 0 true L.slotSrc s.mem :=
      hsl_s.enter_draining.at_exact_frontier (fr₂ := hiFr)
        (by dsimp only [hiFr]; clear *- hpS_rng hibHi_ge; omega)
        (by unfold dualMbSrc; rw [hcap_s]; unfold dualCapSrc
            by_cases hst0 : stg = 0
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [← hmSrc_eq]
              by_cases hs0 : nSrc = 0
              · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                clear *- hibHi_ge; omega
              · rw [ite_eq_right hs0, ite_eq_right hs0]
                have hmS_p : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
                dsimp only [hiFr]; rw [hibHi_eq]
                dsimp only [pad, mSrc, mDst]; split_ifs <;> (clear *- hmS_p; omega)
            · have hd_nz : nDst ≠ 0 := fun hd0 => hst0 (hsched.nDst_zero hd0).2.1
              simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              dsimp only [hiFr]; rw [← hmDst_eq, hibHi_eq]
              simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_nz, ↓reduceIte]
              dsimp only [pad, mDst]; clear *-; omega)
        (by dsimp only [directSlotIo]; exact le_rfl)
    refine hsl_s_hi.set_slotIo (io₂ := pagedSlotIo 0 pgH)
      (show (pagedSlotIo 0 pgH).Valid w hiFr from hv_hi) rfl
      ⟨fun hc0 => by
        have hs0 : nSrc = 0 := by
          rw [hcap_s] at hc0; unfold dualCapSrc at hc0
          by_cases hst0 : stg = 0
          · rwa [ite_eq_left hst0] at hc0
          · rw [ite_eq_right hst0] at hc0
            exact absurd hc0 (fun hd0 => hst0 (hsched.nDst_zero hd0).2.1)
        change qHi = keyBits U; rw [hqHi_eq, ite_eq_left hs0]
        have hle_kb : (if nDst = 0 then keyBits U else quotBitsWhp U nDst) ≤ keyBits U := by
          split_ifs <;> [exact le_rfl; exact Nat.sub_le _ _]
        exact max_eq_left hle_kb,
       fun hcn => by
        change quotBitsWhp U L.slotSrc.nCap ≤ qHi
        rw [hcap_s] at hcn ⊢; unfold dualCapSrc at hcn ⊢; rw [hqHi_eq]
        by_cases hst0 : stg = 0
        · rw [ite_eq_left hst0] at hcn ⊢; rw [ite_eq_right hcn]; exact le_max_left _ _
        · rw [ite_eq_right hst0] at hcn ⊢; rw [ite_eq_right hcn]; exact le_max_right _ _⟩
      rfl
      (fun k hk => by
        have hk64 : k < 64 ∧ ¬(48 ≤ k ∧ k < 61) := by
          rcases hk with h1 | rfl | rfl
          · clear *- h1; exact ⟨by omega, by omega⟩
          · decide
          · decide
        rw [hpS_tick_s3 k hk64.1, ← hs3_def,
          (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb (pSrc + k)
            (by have h2 := hk64.2; clear *- h2; generalize pSrc = p; omega),
          hsb_out (pSrc + k)
            (by have h1 := hk64.1; clear *- h1 hpS_rng hmb_ge192; omega)]
        exact hs2_pg (pSrc + k) (fun hpg => by
          have h1 := hk64.1; have := (hdisj_pg _ hpg).1; clear *- h1 hpS_rng this; omega))
      ⟨(hpS_tick_s3 48 (by decide)).trans hpS_vals.1,
       (hpS_tick_s3 49 (by decide)).trans hpS_vals.2.1,
       (hpS_tick_s3 50 (by decide)).trans hpS_vals.2.2.1,
       (hpS_tick_s3 51 (by decide)).trans hpS_vals.2.2.2.1,
       (hpS_tick_s3 52 (by decide)).trans hpS_vals.2.2.2.2.1,
       (hpS_tick_s3 53 (by decide)).trans hpS_vals.2.2.2.2.2.1,
       (hpS_tick_s3 54 (by decide)).trans hpS_vals.2.2.2.2.2.2.1,
       (hpS_tick_s3 55 (by decide)).trans hpS_vals.2.2.2.2.2.2.2.1,
       (hpS_tick_s3 56 (by decide)).trans hpS_vals.2.2.2.2.2.2.2.2.1,
       (hpS_tick_s3 57 (by decide)).trans hpS_vals.2.2.2.2.2.2.2.2.2.1,
       (hpS_tick_s3 58 (by decide)).trans hpS_vals.2.2.2.2.2.2.2.2.2.2.1,
       (hpS_tick_s3 59 (by decide)).trans hpS_vals.2.2.2.2.2.2.2.2.2.2.2.1,
       (hpS_tick_s3 60 (by decide)).trans hpS_vals.2.2.2.2.2.2.2.2.2.2.2.2⟩
      (fun a _ h2 ha => by
        have := hown_pg_ge a
          (by simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte] using ha)
        clear *- h2 hpS_rng this; omega)
      (fun a ha hia => by
        rcases (show pgH.OwnsAddr a by
          simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte]
            using hia) with hm | hi
        · exact (hdisj_pg a hm).2.2.1 (hcap_s ▸ ha)
        · have hi1 : ibHi ≤ a := hi.1
          unfold slotOwnsNonPageMeta dualMbSrc at ha
          rw [hcap_s] at ha; unfold dualCapSrc at ha
          by_cases hst0 : stg = 0
          · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte] at ha
            by_cases hs0 : nSrc = 0
            · simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte, ne_eq,
                not_true_eq_false, false_and, or_false] at ha
              dsimp only [hdrSmallMeta0] at ha; clear *- ha hi1 hibHi_ge; omega
            · have hth_s : whpThreshold c ≤ nSrc := (hnSrc_b.resolve_left hs0).1
              have h32_s : 32 ≤ offPageDir c w nSrc :=
                (epochMeta_offsets_le (c := c) (w := w) hth_s).1.trans
                  ((epochMeta_offsets_le (c := c) (w := w) hth_s).2.1.trans
                    (epochMeta_offsets_le (c := c) (w := w) hth_s).2.2.1)
              have hod_s := (epochMeta_offsets_le (c := c) (w := w) hth_s).2.2.2
              have hmS_p : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
              rw [← hmSrc_eq] at hod_s
              simp only [show s.mem (base + hdrNSrc) = nSrc from rfl, hs0, ↓reduceIte] at ha
              rw [hibHi_eq] at hi1
              dsimp only [pad, mSrc, mDst, nSrc] at hmS_p hod_s h32_s hi1 ha
              rcases ha with ⟨_, g2⟩ | ⟨_, _, g2⟩ <;>
                (split_ifs at hi1 <;> (clear *- g2 h32_s hod_s hmS_p hi1; omega))
          · have hd_nz : nDst ≠ 0 := fun hd0 => hst0 (hsched.nDst_zero hd0).2.1
            have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hd_nz).1
            have h32_d : 32 ≤ offPageDir c w nDst :=
              (epochMeta_offsets_le (c := c) (w := w) hth_d).1.trans
                ((epochMeta_offsets_le (c := c) (w := w) hth_d).2.1.trans
                  (epochMeta_offsets_le (c := c) (w := w) hth_d).2.2.1)
            have hod_d := (epochMeta_offsets_le (c := c) (w := w) hth_d).2.2.2
            rw [← hmDst_eq] at hod_d
            simp only [show s.mem (base + hdrStage) = stg from rfl,
              show s.mem (base + hdrNDst) = nDst from rfl, hst0, hd_nz, ↓reduceIte] at ha
            rw [hibHi_eq, ite_eq_right hd_nz] at hi1
            dsimp only [pad, mDst, nDst] at h32_d hod_d hi1 ha
            rcases ha with ⟨_, g2⟩ | ⟨_, _, g2⟩ <;>
              (clear *- g2 h32_d hod_d hi1; omega))
      (fun a ha => hm_nonpg_eq a (Or.inl (hcap_s ▸ ha)))
      (hnSide_s.symm ▸ hio0_inv)
      (fun p hp => by
        have hp_lt : p < nLive := hnSide_s ▸ hp
        unfold slotIoPairAt pagedSlotIo directSlotIo SlotIoLayout.side PageUnpermState.virtAt
        simp only [Nat.reduceEqDiff, ne_eq, not_true_eq_false, decide_false, ↓reduceIte]
        rw [hu_id p hp_lt, har_tick_eq]
        rfl)
  have hsl_dst_8 : EpochSlotInv c U V w hiFr (dualPDst base s_tick.mem)
      (dualMbDst base s_tick.mem) (pagedSlotIo 1 pgH) 0 false slotDst' s_tick.mem := by
    have hpD_eq : dualPDst base s_tick.mem = pDst := by
      unfold dualPDst; rw [ite_eq_left (by rw [hph_t]; decide), hst_t]
    have hmD_mb : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
      unfold dualMbDst
      rw [ite_eq_left (by rw [hph_t]; decide), hnD_t, hst_t, hpad_t, ite_eq_left h7_10]
    have hpD_tick_s4 : ∀ k < 64, s_tick.mem (pDst + k) = s4.mem (pDst + k) := fun k _ => by
      rw [hm_eq, Function.update_of_ne (by dsimp only [hdrPhase]; clear *- hpD_rng; omega),
        Function.update_of_ne (by dsimp only [hdrRem]; clear *- hpD_rng; omega)]
    rw [hpD_eq, hmD_mb]
    by_cases hd0 : nDst = 0
    · dsimp only [slotDst']; rw [ite_eq_left hd0]
      unfold EpochSlotInv; dsimp only [SlotLatent.emptySmall]; simp only [↓reduceIte]
      have hmb_sm : dualMbDst base s.mem = base + hdrSmallMeta1 := by
        unfold dualMbDst; rw [ite_eq_left h7_10, ite_eq_left hd0]
      rw [hmb_sm]
      have hqHi_kb : qHi = keyBits U := by
        rw [hqHi_eq, ite_eq_left hd0]
        have hle_kb : (if nSrc = 0 then keyBits U else quotBitsWhp U nSrc) ≤ keyBits U := by
          split_ifs <;> [exact le_rfl; exact Nat.sub_le _ _]
        exact max_eq_right hle_kb
      have hwsm := writeSmallParamTableProg_spec pDst
        ⟨base + hdrSmallMeta1, U, V, pagedSlotIo 1 pgH⟩ s3
      have hs4_wsm : s4 = (Memory.spec 0).clientState s3
          (writeSmallParamTableProg ((pDst, base + hdrSmallMeta1), ((1, 1), pgH.toCtx))) :=
        hs4_def.symm.trans (congrArg ((Memory.spec 0).clientState s3) (ite_eq_left hd0))
      rw [show (pagedSlotIo 1 pgH).toCtx = ((1, 1), pgH.toCtx) from rfl, ← hs4_wsm] at hwsm
      obtain ⟨hz0, hz1⟩ := hsl_67.1 hd0
      have hm0_t : s_tick.mem (base + hdrSmallMeta1) = 0 :=
        (hm_nonpg_eq (base + hdrSmallMeta1) (Or.inr (by
          rw [hmb_sm, hd0]; exact Or.inl ⟨le_rfl, by simp⟩))).trans hz0
      have hm1_t : s_tick.mem (base + hdrSmallMeta1 + 1) = 0 :=
        (hm_nonpg_eq (base + hdrSmallMeta1 + 1) (Or.inr (by
          rw [hmb_sm, hd0]; exact Or.inl ⟨by clear *-; omega, by simp⟩))).trans hz1
      refine ⟨by clear *- hw11; omega,
        by dsimp only [hiFr]; clear *- hpD_rng hibHi_ge; omega,
        { io_valid := show (pagedSlotIo 1 pgH).Valid w hiFr from hv_hi
          w_eq := rfl
          qBits_eq := hqHi_kb
          vBits_eq := rfl
          hdr_frontier := by dsimp only [hiFr, hdrSmallMeta1]; clear *- hibHi_ge; omega
          disjoint_hdr := fun addr hsm hia => by
            have h210 := hown_pg_ge addr
              (by simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte]
                using hia)
            dsimp only [hdrSmallMeta1] at hsm; rcases hsm with hsm | hsm <;>
              (clear *- hsm h210; omega) },
        hwsm.2.2.1.congr (fun a h1 h2 => by
          have heq : pDst + (a - pDst) = a := Nat.add_sub_of_le h1
          rw [← heq]
          exact hpD_tick_s4 (a - pDst) (by clear *- h1 h2; omega)),
        fun a h1 h2 ha => by
          unfold SmallEpochLayout.OwnsAddr at ha; dsimp only at ha
          rcases ha with ha0 | ha1 | hia
          · dsimp only [hdrSmallMeta1] at ha0; clear *- h1 ha0 hpD_rng; omega
          · dsimp only [hdrSmallMeta1] at ha1; clear *- h1 ha1 hpD_rng; omega
          · have h210 := hown_pg_ge a
              (by simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte]
                using hia)
            clear *- h2 hpD_rng h210; omega,
        ⟨hm0_t, by rw [hm1_t]; exact Nat.zero_le _, by rw [hm1_t]; exact hio1_inv,
         by rw [hm1_t]; exact PoolItemsRefines.empty ..⟩⟩
    · have hd_pos : 0 < nDst := Nat.pos_of_ne_zero hd0
      dsimp only [slotDst']; rw [ite_eq_right hd0]
      obtain ⟨hd_cap, hs_abs_d, _, hsl_d⟩ := hsl_67.2 hd_pos
      have hnSide_d : s.mem (dualMbDst base s.mem + 1) = 0 := by
        rw [hsl_d.mem_nSide_eq, hs_abs_d, ← dom_toDictState_card (V := V), toDictState_empty,
          Dictionary.dom_empty, Finset.card_empty]
      have hs4_set : s4 = (Memory.spec 0).clientState s3
          (setSlotIoProg (pDst, ((1, 1), pgH.toCtx))) :=
        hs4_def.symm.trans (congrArg ((Memory.spec 0).clientState s3) (ite_eq_right hd0))
      have hpD_vals := setSlotIoProg_mem_vals pDst (pagedSlotIo 1 pgH) s3
      dsimp only at hpD_vals
      rw [show (pagedSlotIo 1 pgH).toCtx = ((1, 1), pgH.toCtx) from rfl, ← hs4_set] at hpD_vals
      have hpD_old : dualPDst base s.mem = pDst := by
        unfold dualPDst; rw [ite_eq_left h7_10]
      rw [hpD_old] at hsl_d
      have hsl_d_hi : EpochSlotInv c U V w hiFr pDst (dualMbDst base s.mem)
          (directSlotIo w vB base ibHi qHi nLive) 0 false L.slotDst s.mem :=
        hsl_d.at_exact_frontier (fr₂ := hiFr)
          (by dsimp only [hiFr]; clear *- hpD_rng hibHi_ge; omega)
          (by unfold dualMbDst; rw [ite_eq_left h7_10, hd_cap]
              simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte]
              have hmD_p : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
              dsimp only [hiFr]; rw [← hmDst_eq, hibHi_eq, ite_eq_right hd0]
              dsimp only [pad, mDst]; split_ifs <;> (clear *- hmD_p; omega))
          (by dsimp only [directSlotIo]; exact le_rfl)
      exact hsl_d_hi.set_slotIo (io₂ := pagedSlotIo 1 pgH)
        (show (pagedSlotIo 1 pgH).Valid w hiFr from hv_hi) rfl
        ⟨fun hc0 => absurd (hd_cap ▸ hc0) hd0,
         fun _ => by
          change quotBitsWhp U L.slotDst.nCap ≤ qHi
          rw [hd_cap, hqHi_eq, ite_eq_right hd0]; exact le_max_right _ _⟩
        rfl
        (fun k hk => by
          have hk64 : k < 64 ∧ ¬(48 ≤ k ∧ k < 61) := by
            rcases hk with h1 | rfl | rfl
            · clear *- h1; exact ⟨by omega, by omega⟩
            · decide
            · decide
          rw [hpD_tick_s4 k hk64.1, hs4_set,
            (setSlotIoProg_frame pDst ((1, 1), pgH.toCtx)).mem_outside s3 (pDst + k)
              (by have h2 := hk64.2; clear *- h2; generalize pDst = p; omega),
            ← hs3_def,
            (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb (pDst + k)
              (by have h1 := hk64.1; clear *- h1 hpSD_disj; omega),
            hsb_out (pDst + k)
              (by have h1 := hk64.1; clear *- h1 hpD_rng hmb_ge192; omega)]
          exact hs2_pg (pDst + k) (fun hpg => by
            have h1 := hk64.1; have := (hdisj_pg _ hpg).1; clear *- h1 hpD_rng this; omega))
        ⟨(hpD_tick_s4 48 (by decide)).trans hpD_vals.1,
         (hpD_tick_s4 49 (by decide)).trans hpD_vals.2.1,
         (hpD_tick_s4 50 (by decide)).trans hpD_vals.2.2.1,
         (hpD_tick_s4 51 (by decide)).trans hpD_vals.2.2.2.1,
         (hpD_tick_s4 52 (by decide)).trans hpD_vals.2.2.2.2.1,
         (hpD_tick_s4 53 (by decide)).trans hpD_vals.2.2.2.2.2.1,
         (hpD_tick_s4 54 (by decide)).trans hpD_vals.2.2.2.2.2.2.1,
         (hpD_tick_s4 55 (by decide)).trans hpD_vals.2.2.2.2.2.2.2.1,
         (hpD_tick_s4 56 (by decide)).trans hpD_vals.2.2.2.2.2.2.2.2.1,
         (hpD_tick_s4 57 (by decide)).trans hpD_vals.2.2.2.2.2.2.2.2.2.1,
         (hpD_tick_s4 58 (by decide)).trans hpD_vals.2.2.2.2.2.2.2.2.2.2.1,
         (hpD_tick_s4 59 (by decide)).trans hpD_vals.2.2.2.2.2.2.2.2.2.2.2.1,
         (hpD_tick_s4 60 (by decide)).trans hpD_vals.2.2.2.2.2.2.2.2.2.2.2.2⟩
        (fun a _ h2 ha => by
          have := hown_pg_ge a
            (by simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte] using ha)
          clear *- h2 hpD_rng this; omega)
        (fun a ha hia => by
          rcases (show pgH.OwnsAddr a by
            simpa only [SlotIoLayout.OwnsAddr, pagedSlotIo, one_ne_zero, ↓reduceIte]
              using hia) with hm | hi
          · exact (hdisj_pg a hm).2.2.2 (hd_cap ▸ ha)
          · have hi1 : ibHi ≤ a := hi.1
            have hth_d : whpThreshold c ≤ nDst := (hsched.nDst_bounds.resolve_left hd0).1
            have h32_d : 32 ≤ offPageDir c w nDst :=
              (epochMeta_offsets_le (c := c) (w := w) hth_d).1.trans
                ((epochMeta_offsets_le (c := c) (w := w) hth_d).2.1.trans
                  (epochMeta_offsets_le (c := c) (w := w) hth_d).2.2.1)
            have hod_d := (epochMeta_offsets_le (c := c) (w := w) hth_d).2.2.2
            have hmD_p : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
            rw [← hmDst_eq] at hod_d
            rw [hd_cap] at ha; unfold slotOwnsNonPageMeta dualMbDst at ha
            rw [ite_eq_left h7_10] at ha
            simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd0, ↓reduceIte] at ha
            rw [hibHi_eq, ite_eq_right hd0] at hi1
            dsimp only [pad, mDst, nDst] at h32_d hod_d hmD_p hi1 ha
            rcases ha with ⟨_, g2⟩ | ⟨_, _, g2⟩ <;>
              (split_ifs at g2 <;> (clear *- g2 h32_d hod_d hmD_p hi1; omega)))
        (fun a ha => hm_nonpg_eq a (Or.inr (hd_cap ▸ ha)))
        (hnSide_d.symm ▸ hio1_inv)
        (fun p hp => absurd (hnSide_d ▸ hp) (Nat.not_lt_zero p))
  clear hs3_def hs4_def
  refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
  · rw [hnS_t, hph_t, ite_eq_right (by decide : 8 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
  · rw [hph_t, ite_eq_right (by decide : ¬(8 < 2)), ite_eq_right (by decide : 8 ≠ 2),
      ite_eq_left (by decide : 8 ≤ 10), hibH_t, hqH_t, hfr_tick]
    refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
    exact
      { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
        wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
        base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
        hdr := rootStaticHeader_congr hhdr fun off hoff =>
          hout_hdr off (by dsimp only [hdrPhase]; clear *- hoff; omega)
            (by dsimp only [hdrRem]; clear *- hoff; omega) (by clear *- hoff; omega)
        live_eq := (hout_hdr hdrLive (by decide) (by decide) (by decide)).trans hlive_eq
        live_le := hlive_le
        ph_le := by dsimp only; rw [hph_t]; decide
        stg_le := by dsimp only; rw [hst_t]; exact hstg_le
        mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
        cache_src := by
          dsimp only; rw [hnS_t]
          exact hostCacheValid_congr_mem hcache_s fun k hk => by
            rw [Nat.add_assoc]
            exact hout_hdr (hdrSrcOd + k)
              (by dsimp only [hdrSrcOd, hdrPhase]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd, hdrRem]; clear *- hk; omega)
              (by dsimp only [hdrSrcOd]; clear *- hk; omega)
        nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
        sched := by
          dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
          refine
            { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
              nDst_zero := fun hz => by
                dsimp only at hz ⊢
                obtain ⟨h1, h2, _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                rw [hnS_t, hst_t, hph_t]
                exact ⟨h1, h2, by decide, by decide, by decide⟩
              stg_one := fun hs1 => by
                dsimp only at hs1 ⊢; rw [hnD_t, hph_t]
                exact ⟨(hsched.stg_one (hst_t.symm.trans hs1)).1, by decide, by decide⟩
              post_trig := by dsimp only [L']; rw [hnS_t]; exact hsched.post_trig
              trig_cap := by dsimp only [L']; rw [hnS_t, hnD_t]; exact hsched.trig_cap
              drift_hi := by
                dsimp only [L']; have hd := hsched.drift_hi
                simp only [↓reduceIte] at hd ⊢; exact hd
              drift_lo := by
                dsimp only [L']; have hd := hsched.drift_lo
                simp only [↓reduceIte] at hd ⊢; exact hd
              ibLo_eq := by
                dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                simpa only [hp7, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
              qLo_eq := by
                dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                simpa only [hp7, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
              ph1 := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
              ge2 := fun _ => by
                dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                    rw [Nat.add_assoc]
                    exact hout_hdr (hdrDstOd + k)
                      (by dsimp only [hdrDstOd, hdrPhase]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd, hdrRem]; clear *- hk; omega)
                      (by dsimp only [hdrDstOd]; clear *- hk; omega)
                · obtain ⟨hl, he, hp⟩ := hd_logs hd
                  exact ⟨(hout_hdr hdrLogN (by decide) (by decide) (by decide)).trans hl,
                    (hout_hdr hdrEll (by decide) (by decide) (by decide)).trans he,
                    (hout_hdr hdrPgB (by decide) (by decide) (by decide)).trans hp⟩
              ph2 := fun h2 => absurd (hph_t.symm.trans h2) (by decide)
              ph3_10 := fun _ => by dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
              ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
              budget := by
                dsimp only [L']
                rw [hnS_t, hpgH_t, hst_t, hph_t, hnD_t, hmD_t, hrem_t]
                unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                simp only [hp7, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
                  ↓reduceIte] at hb_tot ⊢
                have h2t := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                dsimp only [rem8, itemBatchWhp]
                generalize max (whpThreshold c) nSrc = nRef at hb_tot h2t hnL_ref ⊢
                have hmig_le : nLive / 1024 + 1 ≤ (2 * nRef + 512) / 1024 + 1 := by
                  clear *- hnL_ref; omega
                refine ⟨by clear *- h2t; omega, ?_, ?_⟩ <;>
                  (clear *- hb_tot h2t hmig_le; omega) }
        pad_fits := by
          dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 8 ≠ 0)]
          simpa only [hp7, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
        ph1_inv := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
        ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
        ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
        pDst_pre := fun ⟨_, h5⟩ => absurd (hph_t ▸ h5) (by decide)
        ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
        ph6_inv := fun h6 => absurd (hph_t.symm.trans h6) (by decide)
        ph7_inv := fun h7 => absurd (hph_t.symm.trans h7) (by decide)
        ph8_inv := fun _ => by
          dsimp only [L']; rw [hrem_t, hnS_t]; dsimp only [rem8, itemBatchWhp]
          have hcd_eq : (liveDom L.slotSrc.s_abs).card = nLive := by
            rw [← dom_toDictState_card, hdict_s]
          rw [hcd_eq]
          refine ⟨Nat.le_add_left 1 _, ?_, ?_⟩
          · generalize max (whpThreshold c) nSrc = nRef at hnL_ref ⊢
            clear *- hnL_ref; omega
          · have := Nat.div_add_mod nLive 1024; clear *- this; omega
        ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
        ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
        sl_le7 := fun h7 => absurd (hph_t ▸ h7) (by decide)
        sl_67 := fun h67 => by
          dsimp only at h67; rcases h67 with h6 | h7 <;> exact absurd (hph_t.symm.trans ‹_›)
            (by decide)
        sl_8 := fun _ => by
          dsimp only [L']; rw [hpgH_t, hnD_t]
          have hcap_eq : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
            unfold dualCapSrc; rw [hst_t, hnS_t, hnD_t]
          rw [hcap_eq]
          have hd_abs : slotDst'.s_abs = (fun _ => none) := by
            dsimp only [slotDst']
            by_cases hd0 : nDst = 0
            · rw [ite_eq_left hd0]; rfl
            · rw [ite_eq_right hd0]; exact (hsl_67.2 (Nat.pos_of_ne_zero hd0)).2.1
          have hd_cap : slotDst'.nCap = nDst := by
            dsimp only [slotDst']
            by_cases hd0 : nDst = 0
            · rw [ite_eq_left hd0, hd0]; rfl
            · rw [ite_eq_right hd0]; exact (hsl_67.2 (Nat.pos_of_ne_zero hd0)).1
          have hor_eq : orOpt slotDst'.s_abs L.slotSrc.s_abs = L.slotSrc.s_abs := by
            rw [hd_abs]; funext _; rfl
          refine ⟨hcap_s, hd_cap, fun x => Or.inl (by rw [hd_abs]),
            by rw [hor_eq]; exact hdict_s, hu_cph, hsl_src_8, hsl_dst_8,
            fun hc_pos => ?_, fun hd_pos => ?_⟩
          · have h1 := hevs_s (by clear *- hp7; omega) hc_pos
            have h2 := hel_cap hc_pos
            simp only [↓reduceIte] at h1
            clear *- h1 h2; omega
          · dsimp only [slotDst']
            rw [ite_eq_right hd_pos.ne', (hsl_67.2 hd_pos).2.2.1, List.length_nil, Nat.zero_add,
              ← dom_toDictState_card (V := V), hdict_s]
            have hd_safe := (dualCoreInv_cap_safe h).2
            rw [ite_eq_right (by clear *- hp7; omega)] at hd_safe
            unfold EpochCapSafe at hd_safe
            rw [ite_eq_right hd_pos.ne'] at hd_safe
            have hnL_d : nLive ≤ nDst := hd_safe.2.2.2
            simp only [Bool.false_eq_true, ↓reduceIte]
            clear *- hnL_d; omega
        sl_ge9 := fun h9 => absurd (hph_t ▸ h9) (by decide) }

/-- Phase `7` (`initTail`) background tick specification. -/
theorem tickPhase7_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualMidInv c U V w base s_dict L s)
    (hp7 : s.mem (base + hdrPhase) = 7) :
    let s_tick := (Memory.spec 0).clientState s (bgTickProg (base, s.frontier))
    let rArgs := (Memory.spec 0).clientResult s (bgTickProg (base, s.frontier))
    BgTickPre w (base, s.frontier) s ∧
    DualPostTickInv c U V w base s_dict L s s_tick rArgs := by
  dsimp only
  have hw11 := h.hw11; have hU0 := h.U_pos; have hUw := h.U_lt
  have hV0 := h.V_pos; have hVw := h.V_le; have hwf := h.wf; have hb_fr := h.base_fr
  have hhdr := h.hdr; have hlive_eq := h.live_eq; have hlive_le := h.live_le
  have hstg_le := h.stg_le; have hmSrc_eq := h.mSrc_eq; have hcache_s := h.cache_src
  have hnSrc_b := h.nSrc_bounds; have hpad_fits := h.pad_fits
  obtain ⟨_, _, hpad_w, _, hctx0, hctx1, _, hv_fr, hv_m⟩ :=
    dualPgHost_eval_valid h (by clear *- hp7; omega) (by clear *- hp7; omega)
  have hdisj_pg := disjoint_pgHost_nonPageMeta (nc := (Dictionary.dom s_dict).card) h
    (by clear *- hp7; omega) (by clear *- hp7; omega)
  have hsched := h.sched; rw [ite_eq_right (by clear *- hp7; omega)] at hsched
  obtain ⟨hfr_hi_lo, hfr_hi_hi⟩ := hsched.ph3_10 ⟨by clear *- hp7; omega, by clear *- hp7; omega⟩
  obtain ⟨hmDst_eq, hpad_eq, hcache_d, hd_logs, hibHi_eq, hqHi_eq⟩ :=
    hsched.ge2 (by clear *- hp7; omega)
  obtain ⟨_, hb_tot, _⟩ := hsched.budget
  obtain ⟨hns_h, hqSnap_eq, hdir_pre, ⟨k_t, hcur_k, hcur_lt8, hns_le, hnl_le⟩, htail_pre⟩ :=
    h.ph7_inv hp7
  obtain ⟨hcap_s, hdict_s, hsl_s, hevs_s⟩ := h.sl_le7 (by clear *- hp7; omega)
  have hsl_67 := h.sl_67 (Or.inr hp7)
  obtain ⟨_, hvb_w, _, hqHi_w, _, _, _, _⟩ := dualCoreInv_ib_fits h
  have hw_pos : 0 < w := by clear *- hw11; omega
  set nLive := (Dictionary.dom s_dict).card
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
  set nSnap := s.mem (base + hdrNSnap)
  set qSnap := s.mem (base + hdrQSnap)
  set vB := valBits V
  set hiFr := ibHi + pairStreamWords nLive qHi vB w
  set nHost := dualNHost base s.mem
  set mbHost := dualMbHost base s.mem
  set pgH := dualPgHost c V w base nLive s.mem
  set pgM := hostPageLayout c w nHost mbHost ibHi 0 0 nHost
  have hm_ofCtx : PageArenaLayout.ofCtx pgM.toCtx = pgM := PageArenaLayout.ofCtx_toCtx pgM
  have hh_ofCtx : PageArenaLayout.ofCtx pgH.toCtx = pgH := PageArenaLayout.ofCtx_toCtx pgH
  have hpgB_eq : pgM.pgB = pgH.pgB := rfl
  have hmw_eq : pgM.w = w := rfl
  have hpg32 : 32 ≤ pgH.pgB := hv_fr.2.2.2.2.2.1
  have htb_sp := pageInitTailBatchProg_spec (L := pgM) (n_0 := nSnap) (cur := cur) (s := s)
    (hmw_eq ▸ hv_m) hns_h (hpgB_eq ▸ hcur_lt8.le) tailBatchWhp
  dsimp only at htb_sp
  obtain ⟨_, hcur'_eq, hfr_s2, hmc_tb, hout_s2, _, _, _, _, _, _, _, _, _,
    hpo_s2, hos_s2, hov_s2, htr_s2, hto_s2⟩ := htb_sp
  have httev := tickInitTailProg_eval base s
  change _ ∧ _ at httev
  rw [hctx1, hm_ofCtx] at httev
  obtain ⟨hst_tt, hmc_tt⟩ := httev
  set tb := pageInitTailBatchProg (((pgM.toCtx, nSnap), cur), tailBatchWhp)
  obtain ⟨s2, hs2_def⟩ : ∃ s2, (Memory.spec 0).clientState s tb = s2 := ⟨_, rfl⟩
  obtain ⟨cur', hcur'_def⟩ : ∃ cur', (Memory.spec 0).clientResult s tb = cur' := ⟨_, rfl⟩
  rw [hs2_def] at hst_tt hfr_s2 hout_s2 hpo_s2 hos_s2 hov_s2 htr_s2 hto_s2
  rw [hcur'_def] at hst_tt hcur'_eq
  have hs2_pg : ∀ a, ¬pgH.OwnsMetaAddr a → s2.mem a = s.mem a := fun a ha =>
    hout_s2 a (fun htl => ha (Or.inr (Or.inr htl)))
  have hs2_hdr : ∀ off < 192, s2.mem (base + off) = s.mem (base + off) := fun off h192 =>
    hs2_pg (base + off) (fun hpg => by have := (hdisj_pg _ hpg).1; clear *- h192 this; omega)
  have hctx0_s2 : (Memory.spec 0).clientResult s2 (loadHostCtxProg (base, 0)) = pgH.toCtx := by
    rw [← hctx0, (loadHostCtxProg_eval base 0 s2).2.1, (loadHostCtxProg_eval base 0 s).2.1]
    simp only [↓reduceIte]
    have h_od : ∀ k ≤ 4,
        s2.mem (base + (if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) =
          s.mem (base + (if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) + k) :=
      fun k hk => by
        rw [Nat.add_assoc]
        exact hs2_hdr _ (by dsimp only [hdrSrcOd, hdrDstOd]; split_ifs <;> (clear *- hk; omega))
    rw [hs2_hdr hdrStage (by decide), hs2_hdr hdrNDst (by decide), hs2_hdr hdrPad (by decide),
      hs2_hdr hdrW (by decide), hs2_hdr hdrItemHi (by decide), hs2_hdr hdrQHi (by decide),
      hs2_hdr hdrValBits (by decide), hs2_hdr hdrLive (by decide),
      show s2.mem (base + if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) =
        s.mem (base + if s.mem (base + hdrNDst) = 0 then hdrSrcOd else hdrDstOd) by
        simpa only [Nat.add_zero] using h_od 0 (by decide),
      h_od 1 (by decide), h_od 2 (by decide), h_od 3 (by decide), h_od 4 (by decide)]
  have hband_done : ¬(cur' < 8 * pgM.pgB) →
      qSnap * pgH.pgB ≤ nLive ∧
      4 * (nLive - qSnap * pgH.pgB) ≤ 11 * pgH.pgB ∧
      (0 < qSnap → 5 * pgH.pgB ≤ 4 * (nLive - qSnap * pgH.pgB)) := fun _ => by
    have hk_le : k_t + 1 ≤ pgH.pgB / 8 := by
      rw [hcur_k] at hcur_lt8
      clear *- hcur_lt8 hpg32; omega
    have h1 : nSnap ≤ nLive + pgH.pgB / 8 := by
      simp only [↓reduceIte] at hns_le; clear *- hns_le hk_le; omega
    have h2 : nLive ≤ nSnap + pgH.pgB / 8 := by
      simp only [↓reduceIte] at hnl_le; clear *- hnl_le hk_le; omega
    simpa only [← hqSnap_eq] using snap_band_of_drift hpg32 h1 h2
  have hpre_tail : TickInitTailPre w base s := by
    refine ⟨hw11, hb_fr, hpad_w, ?_⟩
    change (PageArenaLayout.ofCtx
      ((Memory.spec 0).clientResult s (loadHostCtxProg (base, 1)))).Valid w s.frontier ∧ _
    rw [hctx1, hm_ofCtx, hs2_def, hcur'_def]
    refine ⟨hv_m, fun hnlt => ?_⟩
    refine ⟨hw11, hfr_s2 ▸ hb_fr, hs2_hdr hdrPad (by decide) ▸ hpad_w, ?_⟩
    change (PageArenaLayout.ofCtx
      ((Memory.spec 0).clientResult s2 (loadHostCtxProg (base, 0)))).Valid w s2.frontier ∧ _
    rw [hctx0_s2, hh_ofCtx, hfr_s2, hs2_hdr hdrQSnap (by decide),
      hs2_hdr hdrLive (by decide), hlive_eq]
    exact ⟨hv_fr, (hband_done hnlt).1⟩
  have hpre : BgTickPre w (base, s.frontier) s := by
    refine ⟨by clear *- hw11; omega, by clear *- hb_fr; omega, ?_⟩
    simp only [hp7, Nat.reduceEqDiff, ↓reduceIte]
    exact hpre_tail
  have hwf_tick : Memory.WellFormed w
      ((Memory.spec 0).clientState s (bgTickProg (base, s.frontier))) :=
    wf_step hwf (validHistory_bgTickProg hwf hpre)
  have hbgev := bgTickProg_eval base s.frontier s
  simp only [hp7, Nat.reduceEqDiff, ↓reduceIte] at hbgev
  obtain ⟨hst_bg, hres_bg, hmc_bg⟩ := hbgev
  have hmc_tot : memoryCost (bgTickProg (base, s.frontier)) s ≤
      itemBatchWhp * (2 * epochStepCost c + 20) + 20000 := by
    dsimp only [tb, nSnap, cur, tailBatchWhp, itemBatchWhp] at hmc_tt hmc_tb ⊢
    clear *- hmc_bg hmc_tt hmc_tb; omega
  clear hs2_def hcur'_def
  have hibHi_ge : base + 196 ≤ ibHi := by
    rw [hibHi_eq]; split_ifs <;> (clear *-; omega)
  have hdiff_le : s.frontier - hiFr ≤ bulkBatchWhp := by
    have hle1 : s.frontier ≤ ibHi + pairStreamWords (nLive + 1) qHi vB w := hfr_hi_hi
    have hstep := pairStreamWords_succ_le_add_two (n := nLive) (qb := qHi) (vb := vB) (w := w)
      hw_pos (by clear *- hqHi_w hvb_w; omega)
    dsimp only [hiFr, bulkBatchWhp]; clear *- hle1 hstep; omega
  have hfr_le_pad : s.frontier ≤ base + dualPaddedWords c U V w nSrc nDst nLive := by
    have hib_pad := (dualCoreInv_ib_fits h).2.2.2.2.2.1
    rw [ite_eq_right (by clear *- hp7; omega)] at hib_pad
    exact hfr_hi_hi.trans hib_pad
  have hio_src_eq : activeSrcIo c w vB base stg 7 nSrc nDst pad ibLo qLo ibHi qHi nLive =
      directSlotIo w vB base ibHi qHi nLive := rfl
  rw [hp7, hio_src_eq] at hsl_s
  have hdir_s2 : ∀ vp < pgH.maxPages,
      (extractPagePair pgH s2.mem).pageOf false vp = vp ∧
      (extractPagePair pgH s2.mem).pageOf true vp = 0 ∧
      (extractPagePair pgH s2.mem).ownerSide vp = false ∧
      (extractPagePair pgH s2.mem).ownerVp vp = vp := fun vp hvp => by
    have hp_eq : extractPagePair pgH s2.mem = (extractPageUnperm pgM s2.mem).st := rfl
    have hp0_eq : (extractPageUnperm pgM s.mem).st = extractPagePair pgH s.mem := rfl
    rw [hp_eq, hpo_s2, hos_s2, hov_s2, hp0_eq]
    exact hdir_pre vp hvp
  have htail_s2 : ∀ idx < cur',
      (idx < 4 * pgH.pgB →
        (extractPagePair pgH s2.mem).tailRes false idx = (qSnap * pgH.pgB + idx) % (8 * pgH.pgB) ∧
        (extractPagePair pgH s2.mem).tailRes true idx = (qSnap * pgH.pgB + idx) % (8 * pgH.pgB)) ∧
      (extractPagePair pgH s2.mem).tailOwnerSide idx = false ∧
      (extractPagePair pgH s2.mem).tailOwnerRing idx =
        (idx + 8 * pgH.pgB - (qSnap * pgH.pgB) % (8 * pgH.pgB)) % (8 * pgH.pgB) :=
    fun idx hidx => by
    have hidx8 : idx < 8 * pgM.pgB := lt_of_lt_of_le hidx (hcur'_eq ▸ min_le_left _ _)
    have hp_eq : extractPagePair pgH s2.mem = (extractPageUnperm pgM s2.mem).st := rfl
    have hp0_eq : (extractPageUnperm pgM s.mem).st = extractPagePair pgH s.mem := rfl
    obtain ⟨htos, htor⟩ := hto_s2 idx hidx8
    rw [hp_eq]
    rw [hp0_eq, ← hcur'_eq] at htos htor
    rw [hpgB_eq, ← hqSnap_eq] at htor
    by_cases hge : cur ≤ idx
    · have hcond : cur ≤ idx ∧ idx < cur' := ⟨hge, hidx⟩
      simp only [htos, htor, hcond, and_self, and_true, ↓reduceIte]
      intro h4
      have hf := htr_s2 false idx (hpgB_eq ▸ h4)
      have ht := htr_s2 true idx (hpgB_eq ▸ h4)
      rw [hp0_eq, ← hcur'_eq, hpgB_eq, ← hqSnap_eq, ite_eq_left hcond] at hf ht
      exact ⟨hf, ht⟩
    · have hncond : ¬(cur ≤ idx ∧ idx < cur') := by clear *- hge; omega
      have hpre_i := htail_pre idx (Nat.lt_of_not_le hge)
      simp only [htos, htor, hncond, ↓reduceIte]
      refine ⟨fun h4 => ?_, hpre_i.2.1, hpre_i.2.2⟩
      have hf := htr_s2 false idx (hpgB_eq ▸ h4)
      have ht := htr_s2 true idx (hpgB_eq ▸ h4)
      rw [hp0_eq, ← hcur'_eq, hpgB_eq, ← hqSnap_eq, ite_eq_right hncond] at hf ht
      exact ⟨hf.trans (hpre_i.1 h4).1, ht.trans (hpre_i.1 h4).2⟩
  obtain ⟨s_tick, hs_tick_def⟩ :
      ∃ s_tick, (Memory.spec 0).clientState s (bgTickProg (base, s.frontier)) = s_tick := ⟨_, rfl⟩
  rw [hs_tick_def] at hwf_tick hst_bg ⊢
  clear hs_tick_def
  have hf_ev := finishInitTailProg_eval base s2
  change _ ∧ _ at hf_ev
  rw [hctx0_s2, hh_ofCtx, hs2_hdr hdrStage (by decide), hs2_hdr hdrNDst (by decide),
    hs2_hdr hdrLive (by decide), hlive_eq, hs2_hdr hdrQSnap (by decide)] at hf_ev
  obtain ⟨hst_fin, _⟩ := hf_ev
  have hfr_fin :
      ((Memory.spec 0).clientState s2 (finishInitTailProg base)).frontier = s.frontier := by
    rw [hst_fin]; dsimp only
    set pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
    set pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
    set sb := (Memory.spec 0).clientState s2
      (pageInitScalarsBandProg ((pgH.metaBase, pgH.pgB), (qSnap, nLive - qSnap * pgH.pgB)))
    set s3 := (Memory.spec 0).clientState sb (setSlotIoProg (pSrc, ((1, 0), pgH.toCtx)))
    have hfr_b : sb.frontier = s.frontier :=
      (pageInitScalarsBandProg_spec _ _ _ _ s2).1.trans hfr_s2
    have hfr_3 : s3.frontier = s.frontier :=
      (runClient_frontier_setSlotIoProg _ _).trans hfr_b
    by_cases hd0 : nDst = 0
    · rw [ite_eq_left hd0]
      exact (writeSmallParamTableProg_spec pDst
        ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3).1.trans hfr_3
    · rw [ite_eq_right hd0]
      exact (runClient_frontier_setSlotIoProg _ _).trans hfr_3
  have hfr_tick : s_tick.frontier = s.frontier := by
    rw [hst_bg, hst_tt]
    split_ifs
    · exact hfr_s2
    · exact hfr_fin
  have hlt_b_tick : ∀ addr < base, s_tick.mem addr = s.mem addr := fun addr hlt_b => by
    have hs2_lt : s2.mem addr = s.mem addr :=
      hs2_pg addr (fun hpg => by have := (hdisj_pg addr hpg).1; clear *- hlt_b this; omega)
    rw [hst_bg, hst_tt]
    split_ifs with hlt8
    · dsimp only
      exact (Function.update_of_ne (by dsimp only [hdrCur]; clear *- hlt_b; omega) _ _).trans hs2_lt
    · rw [hst_fin]; dsimp only
      rw [Function.update_of_ne (by dsimp only [hdrPhase]; clear *- hlt_b; omega),
        Function.update_of_ne (by dsimp only [hdrRem]; clear *- hlt_b; omega)]
      set pSrc := if stg = 0 then base + hdrPBase0 else base + hdrPBase1
      set pDst := if stg = 0 then base + hdrPBase1 else base + hdrPBase0
      set sb := (Memory.spec 0).clientState s2
        (pageInitScalarsBandProg ((pgH.metaBase, pgH.pgB), (qSnap, nLive - qSnap * pgH.pgB)))
      set s3 := (Memory.spec 0).clientState sb (setSlotIoProg (pSrc, ((1, 0), pgH.toCtx)))
      have hmb_ge : base + 192 ≤ pgH.metaBase := by
        change base + 192 ≤ mbHost; dsimp only [mbHost]; unfold dualMbHost
        split_ifs <;> (clear *-; omega)
      have hb_lt : sb.mem addr = s2.mem addr :=
        (pageInitScalarsBandProg_spec _ _ _ _ s2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 addr
          (by clear *- hlt_b hmb_ge; omega)
      have hpS_ge : base + 64 ≤ pSrc := by
        dsimp only [pSrc, hdrPBase0, hdrPBase1]; split_ifs <;> (clear *-; omega)
      have hpD_ge : base + 64 ≤ pDst := by
        dsimp only [pDst, hdrPBase0, hdrPBase1]; split_ifs <;> (clear *-; omega)
      have h3_lt : s3.mem addr = sb.mem addr :=
        (setSlotIoProg_frame pSrc ((1, 0), pgH.toCtx)).mem_outside sb addr
          (by clear *- hlt_b hpS_ge; omega)
      have h4_lt : ((Memory.spec 0).clientState s3
          (if nDst = 0 then
            writeSmallParamTableProg ((pDst, base + hdrSmallMeta1), ((1, 1), pgH.toCtx))
           else setSlotIoProg (pDst, ((1, 1), pgH.toCtx)))).mem addr = s3.mem addr := by
        by_cases hd0 : nDst = 0
        · rw [ite_eq_left hd0]
          exact (writeSmallParamTableProg_spec pDst
            ⟨base + hdrSmallMeta1, 0, 0, ⟨1, 1, pgH⟩⟩ s3).2.2.2
            addr (by clear *- hlt_b hpD_ge; omega)
        · rw [ite_eq_right hd0]
          exact (setSlotIoProg_frame pDst ((1, 1), pgH.toCtx)).mem_outside s3 addr
            (by clear *- hlt_b hpD_ge; omega)
      exact ((h4_lt.trans h3_lt).trans hb_lt).trans hs2_lt
  refine ⟨hpre, hfr_tick, hwf_tick, hlt_b_tick, ?_⟩
  rw [ite_eq_left (by clear *- hp7; omega)]
  refine ⟨hres_bg, ?_⟩
  by_cases hlt8 : cur' < 8 * pgM.pgB
  · -- `7 → 7`: `cur' = cur + 128 = 128 * (k_t + 1) < 8 * pgH.pgB`
    refine ⟨{ L with elapsed := L.elapsed + 1 }, preservesEpochSeeds_of_eq_slots
      (fun ⟨h9, _⟩ => by rw [hp7] at h9; cases h9) rfl rfl,
      ?_, fun _ _ => hmc_tot⟩
    have hcur'_step : cur' = cur + 128 := by
      rw [hcur'_eq]; unfold tailBatchWhp at hcur'_eq hlt8 ⊢
      exact min_eq_right (by rw [hcur'_eq] at hlt8; clear *- hlt8; omega)
    have hm_eq : s_tick.mem = Function.update s2.mem (base + hdrCur) cur' := by
      rw [hst_bg, hst_tt, ite_eq_left hlt8]
    have hout_hdr : ∀ off, off ≠ hdrCur → off < 192 →
        s_tick.mem (base + off) = s.mem (base + off) := fun off hne h192 => by
      rw [hm_eq, Function.update_of_ne (base_add_ne hne)]; exact hs2_hdr off h192
    have hph_t : s_tick.mem (base + hdrPhase) = 7 :=
      (hout_hdr hdrPhase (by decide) (by decide)).trans hp7
    have hcur_t : s_tick.mem (base + hdrCur) = cur' := by rw [hm_eq]; exact Function.update_self ..
    have hst_t : s_tick.mem (base + hdrStage) = stg := hout_hdr hdrStage (by decide) (by decide)
    have hnS_t : s_tick.mem (base + hdrNSrc) = nSrc := hout_hdr hdrNSrc (by decide) (by decide)
    have hnD_t : s_tick.mem (base + hdrNDst) = nDst := hout_hdr hdrNDst (by decide) (by decide)
    have hmS_t : s_tick.mem (base + hdrMSrc) = mSrc := hout_hdr hdrMSrc (by decide) (by decide)
    have hmD_t : s_tick.mem (base + hdrMDst) = mDst := hout_hdr hdrMDst (by decide) (by decide)
    have hpad_t : s_tick.mem (base + hdrPad) = pad := hout_hdr hdrPad (by decide) (by decide)
    have hibL_t : s_tick.mem (base + hdrItemLo) = ibLo :=
      hout_hdr hdrItemLo (by decide) (by decide)
    have hibH_t : s_tick.mem (base + hdrItemHi) = ibHi :=
      hout_hdr hdrItemHi (by decide) (by decide)
    have hqL_t : s_tick.mem (base + hdrQLo) = qLo := hout_hdr hdrQLo (by decide) (by decide)
    have hqH_t : s_tick.mem (base + hdrQHi) = qHi := hout_hdr hdrQHi (by decide) (by decide)
    have hns_t : s_tick.mem (base + hdrNSnap) = nSnap :=
      hout_hdr hdrNSnap (by decide) (by decide)
    have hqs_t : s_tick.mem (base + hdrQSnap) = qSnap :=
      hout_hdr hdrQSnap (by decide) (by decide)
    have hpgH_t : dualPgHost c V w base nLive s_tick.mem = pgH := by
      dsimp only [pgH]; unfold dualPgHost dualNHost dualMbHost
      rw [hnD_t, hnS_t, hst_t, hpad_t, hibH_t, hqH_t]
    have hm_ge48 : ∀ a, base + 48 ≤ a → ¬pgH.OwnsMetaAddr a → s_tick.mem a = s.mem a :=
      fun a h48 hpg => by
        rw [hm_eq, Function.update_of_ne (by dsimp only [hdrCur]; clear *- h48; omega)]
        exact hs2_pg a hpg
    have hu_t : extractPageUnperm pgH s_tick.mem = extractPageUnperm pgH s2.mem :=
      extractPageUnperm_congr hw_pos fun a ha => by
        have ha210 := (hdisj_pg a ha).1
        rw [hm_eq]; exact Function.update_of_ne (by dsimp only [hdrCur]; clear *- ha210; omega) _ _
    have hpS_eq : dualPSrc base s_tick.mem = dualPSrc base s.mem := by unfold dualPSrc; rw [hst_t]
    have hmS_mb : dualMbSrc base s_tick.mem = dualMbSrc base s.mem := by
      unfold dualMbSrc; rw [hst_t, hnS_t, hpad_t]
    have h7_10 : s.mem (base + hdrPhase) < 10 := by clear *- hp7; omega
    have hsl_s_hi : EpochSlotInv c U V w hiFr (dualPSrc base s_tick.mem)
        (dualMbSrc base s_tick.mem) (directSlotIo w vB base ibHi qHi nLive) 0 false
        L.slotSrc s_tick.mem := by
      rw [hpS_eq, hmS_mb]
      refine (hsl_s.congr_mem
        (fun a h1 h2 => hm_ge48 a (by
          unfold dualPSrc at h1; dsimp only [hdrPBase0, hdrPBase1] at h1
          split_ifs at h1 <;> (clear *- h1; omega))
          (fun hpg => by
            have ha210 := (hdisj_pg a hpg).1
            unfold dualPSrc at h2; dsimp only [hdrPBase0, hdrPBase1] at h2
            split_ifs at h2 <;> (clear *- h2 ha210; omega)))
        (fun a ha => by
          have hr := slotOwnsNonPageMeta_src_range hcap_s
            (fun hst_nz hd0 => hst_nz (hsched.nDst_zero hd0).2.1) ha
          exact hm_ge48 a (by rcases hr with ⟨h1, _⟩ | h1 <;> (clear *- h1; omega))
            (fun hpg => (hdisj_pg a hpg).2.2.1 (hcap_s ▸ ha)))
        (fun a ha => by
          simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
            ↓reduceIte] at ha
          have ha1 := ha.1
          exact hm_ge48 a (by clear *- ha1 hibHi_ge; omega)
            (fun hpg => absurd ha1 (Nat.not_le_of_gt (hdisj_pg a hpg).2.1)))).at_exact_frontier
        (by unfold dualPSrc; dsimp only [hiFr, hdrPBase0, hdrPBase1]
            split_ifs <;> (clear *- hibHi_ge; omega))
        (by unfold dualMbSrc; rw [hcap_s]; unfold dualCapSrc
            by_cases hst0 : stg = 0
            · simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              rw [← hmSrc_eq]
              by_cases hs0 : nSrc = 0
              · rw [ite_eq_left hs0, ite_eq_left hs0]; dsimp only [hdrSmallMeta0, hiFr]
                clear *- hibHi_ge; omega
              · rw [ite_eq_right hs0, ite_eq_right hs0]
                have hmS_p : mSrc ≤ pad := by rw [hpad_eq]; exact le_max_left _ _
                dsimp only [hiFr]; rw [hibHi_eq]; split_ifs <;> (clear *- hmS_p; omega)
            · have hd_nz : nDst ≠ 0 := fun hd0 => hst0 (hsched.nDst_zero hd0).2.1
              simp only [show s.mem (base + hdrStage) = stg from rfl, hst0, ↓reduceIte]
              dsimp only [hiFr]; rw [← hmDst_eq, hibHi_eq]
              simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_nz, ↓reduceIte]
              dsimp only [pad, mDst]; clear *-; omega)
        (by dsimp only [directSlotIo]; exact le_rfl)
    refine ⟨hwf_tick, ?_, fun h5 => absurd (hph_t.symm.trans h5) (by decide), ?_⟩
    · rw [hnS_t, hph_t, ite_eq_right (by decide : 7 ≠ 0), hnD_t, hfr_tick]; exact hfr_le_pad
    · rw [hph_t, ite_eq_right (by decide : ¬(7 < 2)), ite_eq_right (by decide : 7 ≠ 2),
        ite_eq_left (by decide : 7 ≤ 10), hibH_t, hqH_t, hfr_tick]
      refine ⟨hfr_hi_lo, hdiff_le, ?_⟩
      exact
        { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
          wf := ⟨lt_of_le_of_lt hfr_hi_lo hwf.1, hwf_tick.2⟩
          base_fr := by dsimp only [hiFr]; clear *- hibHi_ge; omega
          hdr := rootStaticHeader_congr hhdr fun off hoff =>
            hout_hdr off (by dsimp only [hdrCur]; clear *- hoff; omega) (by clear *- hoff; omega)
          live_eq := (hout_hdr hdrLive (by decide) (by decide)).trans hlive_eq
          live_le := hlive_le
          ph_le := by dsimp only; rw [hph_t]; decide
          stg_le := by dsimp only; rw [hst_t]; exact hstg_le
          mSrc_eq := by dsimp only; rw [hmS_t, hnS_t]; exact hmSrc_eq
          cache_src := by
            dsimp only; rw [hnS_t]
            exact hostCacheValid_congr_mem hcache_s fun k hk => by
              rw [Nat.add_assoc]
              exact hout_hdr (hdrSrcOd + k) (by dsimp only [hdrSrcOd, hdrCur]; clear *- hk; omega)
                (by dsimp only [hdrSrcOd]; clear *- hk; omega)
          nSrc_bounds := by dsimp only; rw [hnS_t]; exact hnSrc_b
          sched := by
            dsimp only; rw [ite_eq_right (by rw [hph_t]; decide)]
            refine
              { nDst_bounds := by dsimp only; rw [hnD_t]; exact hsched.nDst_bounds
                nDst_zero := fun hz => by
                  dsimp only at hz ⊢
                  obtain ⟨h1, h2, _⟩ := hsched.nDst_zero (hnD_t.symm.trans hz)
                  rw [hnS_t, hst_t, hph_t]
                  exact ⟨h1, h2, by decide, by decide, by decide⟩
                stg_one := fun hs1 => by
                  dsimp only at hs1 ⊢; rw [hnD_t, hph_t]
                  exact ⟨(hsched.stg_one (hst_t.symm.trans hs1)).1, by decide, by decide⟩
                post_trig := by dsimp only; rw [hnS_t]; exact hsched.post_trig
                trig_cap := by dsimp only; rw [hnS_t, hnD_t]; exact hsched.trig_cap
                drift_hi := by dsimp only; simpa using hsched.drift_hi
                drift_lo := by dsimp only; simpa using hsched.drift_lo
                ibLo_eq := by
                  dsimp only; rw [hibL_t, hph_t, hmS_t, hmD_t]
                  simpa only [hp7, Nat.reduceLT, ↓reduceIte] using hsched.ibLo_eq
                qLo_eq := by
                  dsimp only; rw [hqL_t, hph_t, hnS_t, hnD_t]
                  simpa only [hp7, Nat.reduceLT, ↓reduceIte] using hsched.qLo_eq
                ph1 := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
                ge2 := fun _ => by
                  dsimp only; rw [hmD_t, hnD_t, hpad_t, hmS_t, hibH_t, hqH_t, hnS_t]
                  refine ⟨hmDst_eq, hpad_eq, ?_, fun hd => ?_, hibHi_eq, hqHi_eq⟩
                  · exact hostCacheValid_congr_mem hcache_d fun k hk => by
                      rw [Nat.add_assoc]
                      exact hout_hdr (hdrDstOd + k)
                        (by dsimp only [hdrDstOd, hdrCur]; clear *- hk; omega)
                        (by dsimp only [hdrDstOd]; clear *- hk; omega)
                  · obtain ⟨hl, he, hp⟩ := hd_logs hd
                    exact ⟨(hout_hdr hdrLogN (by decide) (by decide)).trans hl,
                      (hout_hdr hdrEll (by decide) (by decide)).trans he,
                      (hout_hdr hdrPgB (by decide) (by decide)).trans hp⟩
                ph2 := fun h2 => absurd (hph_t.symm.trans h2) (by decide)
                ph3_10 := fun _ => by dsimp only [hiFr]; rw [hibH_t, hqH_t]; exact ⟨le_rfl, le_rfl⟩
                ph11 := fun h11 => absurd (hph_t.symm.trans h11) (by decide)
                budget := by
                  dsimp only
                  rw [hnS_t, hpgH_t, hst_t, hph_t, hnD_t, hmD_t, hcur_t, hcur'_step]
                  unfold remRebuildBudget futureRebuildBudget at hb_tot ⊢
                  simp only [hp7, Nat.reduceEqDiff, Nat.reduceLeDiff, and_self,
                    ↓reduceIte] at hb_tot ⊢
                  have h2t := two_le_maxTailPhasesBudget (max (whpThreshold c) nSrc)
                  have hlt8' : cur + 128 < 8 * pgH.pgB := hpgB_eq ▸ (hcur'_step ▸ hlt8)
                  have hdiv_step : (8 * pgH.pgB - (cur + 128)) / 128 + 1 ≤
                      (8 * pgH.pgB - cur) / 128 := by clear *- hlt8'; omega
                  generalize max (whpThreshold c) nSrc = nRef at hb_tot h2t ⊢
                  refine ⟨by clear *- h2t; omega, ?_, ?_⟩
                  · clear *- hb_tot hdiv_step; omega
                  · clear *- hb_tot h2t hdiv_step; omega }
          pad_fits := by
            dsimp only; rw [hnS_t, hph_t, hnD_t, ite_eq_right (by decide : 7 ≠ 0)]
            simpa only [hp7, Nat.reduceEqDiff, ↓reduceIte] using hpad_fits
          ph1_inv := fun h1 => absurd (hph_t.symm.trans h1) (by decide)
          ph3_inv := fun h3 => absurd (hph_t.symm.trans h3) (by decide)
          ph4_inv := fun h4 => absurd (hph_t.symm.trans h4) (by decide)
          pDst_pre := fun ⟨_, h5⟩ => absurd (hph_t ▸ h5) (by decide)
          ph5_inv := fun h5 => absurd (hph_t.symm.trans h5) (by decide)
          ph6_inv := fun h6 => absurd (hph_t.symm.trans h6) (by decide)
          ph7_inv := fun _ => by
            dsimp only; rw [hpgH_t, hns_t, hqs_t, hcur_t]
            have hnH_t : dualNHost base s_tick.mem = nHost := by
              dsimp only [nHost]; unfold dualNHost; rw [hnD_t, hnS_t]
            rw [hnH_t]
            have hp_eq : extractPagePair pgH s_tick.mem = (extractPageUnperm pgH s_tick.mem).st :=
              rfl
            refine ⟨hns_h, hqSnap_eq, fun vp hvp => by rw [hp_eq, hu_t]; exact hdir_s2 vp hvp,
              ⟨k_t + 1, by rw [hcur'_step, hcur_k]; ring, hpgB_eq ▸ hlt8,
                by simp only [Bool.false_eq_true, ↓reduceIte] at hns_le ⊢; clear *- hns_le; omega,
                by simp only [Bool.false_eq_true, ↓reduceIte] at hnl_le ⊢; clear *- hnl_le; omega⟩,
              fun idx hidx => by rw [hp_eq, hu_t]; exact htail_s2 idx hidx⟩
          ph8_inv := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
          ph9_inv := fun h9 => absurd (hph_t.symm.trans h9) (by decide)
          ph10_inv := fun h10 => absurd (hph_t.symm.trans h10) (by decide)
          sl_le7 := fun _ => by
            dsimp only; rw [hst_t, hph_t, hnS_t, hnD_t, hpad_t, hibL_t, hqL_t, hibH_t, hqH_t]
            have hcap_eq : dualCapSrc base s_tick.mem = dualCapSrc base s.mem := by
              unfold dualCapSrc; rw [hst_t, hnS_t, hnD_t]
            rw [hcap_eq]
            exact ⟨hcap_s, hdict_s, hsl_s_hi, fun _ hc => hevs_s (by clear *- hp7; omega) hc⟩
          sl_67 := fun _ => by
            dsimp only; rw [hnD_t, hibH_t, hqH_t]
            refine ⟨fun hd0 => ?_, fun hd_pos => ?_⟩
            · obtain ⟨hz0, hz1⟩ := hsl_67.1 hd0
              exact ⟨(hm_ge48 (base + hdrSmallMeta1) (by unfold hdrSmallMeta1; clear *-; omega)
                  (fun hpg => by
                    have ha210 := (hdisj_pg _ hpg).1
                    unfold hdrSmallMeta1 at ha210; clear *- ha210; omega)).trans hz0,
                (hm_ge48 (base + hdrSmallMeta1 + 1) (by unfold hdrSmallMeta1; clear *-; omega)
                  (fun hpg => by
                    have ha210 := (hdisj_pg _ hpg).1
                    unfold hdrSmallMeta1 at ha210; clear *- ha210; omega)).trans hz1⟩
            · obtain ⟨hd_cap, hs_abs_d, hevs_d, hsl_d⟩ := hsl_67.2 hd_pos
              have hpD_eq : dualPDst base s_tick.mem = dualPDst base s.mem := by
                unfold dualPDst
                rw [ite_eq_left (by rw [hph_t]; decide), ite_eq_left h7_10, hst_t]
              have hmD_mb : dualMbDst base s_tick.mem = dualMbDst base s.mem := by
                unfold dualMbDst
                rw [ite_eq_left (by rw [hph_t]; decide), ite_eq_left h7_10, hnD_t, hst_t, hpad_t]
              refine ⟨hd_cap, hs_abs_d, hevs_d, ?_⟩
              rw [hpD_eq, hmD_mb]
              exact (hsl_d.congr_mem
                (fun a h1 h2 => hm_ge48 a (by
                  unfold dualPDst at h1; rw [ite_eq_left h7_10] at h1
                  dsimp only [hdrPBase0, hdrPBase1] at h1; split_ifs at h1 <;> (clear *- h1; omega))
                  (fun hpg => by
                    have ha210 := (hdisj_pg a hpg).1
                    unfold dualPDst at h2; rw [ite_eq_left h7_10] at h2
                    dsimp only [hdrPBase0, hdrPBase1] at h2
                    split_ifs at h2 <;> (clear *- h2 ha210; omega)))
                (fun a ha => by
                  have ha48 : base + 48 ≤ a := by
                    rw [hd_cap] at ha; unfold slotOwnsNonPageMeta dualMbDst at ha
                    rw [ite_eq_left h7_10] at ha
                    simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_pos.ne',
                      ↓reduceIte] at ha
                    rcases ha with ⟨h1, _⟩ | ⟨_, h1, _⟩ <;>
                      (split_ifs at h1 <;> (clear *- h1; omega))
                  exact hm_ge48 a ha48 (fun hpg => (hdisj_pg a hpg).2.2.2 (hd_cap ▸ ha)))
                (fun a ha => by
                  simp only [SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr, directSlotIo,
                    ↓reduceIte] at ha
                  have ha1 := ha.1
                  exact hm_ge48 a (by clear *- ha1 hibHi_ge; omega)
                    (fun hpg => absurd ha1
                      (Nat.not_le_of_gt (hdisj_pg a hpg).2.1)))).at_exact_frontier
                (by unfold dualPDst; rw [ite_eq_left h7_10]
                    dsimp only [hiFr, hdrPBase0, hdrPBase1]
                    split_ifs <;> (clear *- hibHi_ge; omega))
                (by unfold dualMbDst; rw [ite_eq_left h7_10, hd_cap]
                    simp only [show s.mem (base + hdrNDst) = nDst from rfl, hd_pos.ne', ↓reduceIte]
                    have hmD_p : mDst ≤ pad := by rw [hpad_eq]; exact le_max_right _ _
                    rw [← hmDst_eq, hibHi_eq, ite_eq_right hd_pos.ne']
                    dsimp only [pad, mDst]; split_ifs <;> (clear *- hmD_p; omega))
                (by dsimp only [directSlotIo]; exact le_rfl)
          sl_8 := fun h8 => absurd (hph_t.symm.trans h8) (by decide)
          sl_ge9 := fun h9 => absurd (hph_t ▸ h9) (by decide) }
  · -- `7 → 8`: `cur' = 8 * pgH.pgB`, running `finishInitTailProg`
    have hcur'_8 : cur' = 8 * pgH.pgB := by
      rw [← hpgB_eq]; have := hcur'_eq ▸ min_le_left (8 * pgM.pgB) (cur + tailBatchWhp)
      clear *- hlt8 this; omega
    set slotDst' : SlotLatent c U V := if nDst = 0 then SlotLatent.emptySmall c U V else L.slotDst
    set L' : DualLatent c U V := { L with slotDst := slotDst', elapsed := L.elapsed + 1 }
    have hpres_L' : PreservesEpochSeeds (s.mem (base + hdrPhase) = 8)
        (s.mem (base + hdrPhase) = 9 ∧ s_tick.mem (base + hdrPhase) = 4) L L' := by
      refine ⟨⟨fun _ => ⟨rfl, HEq.rfl, rfl⟩, fun ⟨h9, _⟩ => by rw [hp7] at h9; cases h9⟩, ?_⟩
      dsimp only [L', slotDst']
      by_cases hd0 : nDst = 0
      · rw [ite_eq_left hd0]; exact Or.inl rfl
      · rw [ite_eq_right hd0]
        exact Or.inr ⟨rfl, HEq.rfl, ⟨[], (List.append_nil _).symm⟩, fun _ => rfl⟩
    refine ⟨L', hpres_L', ?_, fun _ _ => hmc_tot⟩
    exact tickPhase7_finish_spec h hp7 hwf_tick hfr_tick hs2_pg hctx0_s2
      (by rw [hst_bg, hst_tt, ite_eq_right hlt8])
      (hband_done hlt8) hdir_s2 (fun idx hidx => htail_s2 idx (hcur'_8 ▸ hidx))

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

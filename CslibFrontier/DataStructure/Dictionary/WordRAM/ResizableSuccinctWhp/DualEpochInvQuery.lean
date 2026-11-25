/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochInvSpace
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochCtrlEval

/-!
# Read-Only Foreground Query Specification (`userQueryProg_spec`)

Proves `evs_len_le_four_mul_of_dualStateInv` and `userQueryProg_spec` across all 12 phases `0..11`.
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

/-! ## Section 3: Read-Only `userQueryProg_spec` Across All 12 Phases -/

/-- Every active slot in `DualStateInv` has at most `4 * N` recorded history events. -/
theorem evs_len_le_four_mul_of_dualStateInv {c U V w base : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) :
    let ph := s.mem (base + hdrPhase)
    (ph ≤ 8 → L.slotSrc.nCap ≠ 0 → L.slotSrc.evs.length ≤ 4 * L.slotSrc.nCap) ∧
    (8 ≤ ph → L.slotDst.nCap ≠ 0 → L.slotDst.evs.length ≤ 4 * L.slotDst.nCap) := by
  dsimp only
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  have hph_le := h.ph_le; have hstg_le := h.stg_le; have hsched := h.sched
  have hsl_le7 := h.sl_le7; have hsl_8 := h.sl_8; have hsl_ge9 := h.sl_ge9
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost] at hsl_le7 hsl_8 hsl_ge9
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set nSrc := s.mem (base + hdrNSrc)
  set nDst := s.mem (base + hdrNDst)
  by_cases hph0 : ph = 0
  · rw [ite_eq_left hph0] at hsched hdst_safe
    have hst0 : stg = 0 := hsched.stg_zero
    have hops0 := hsched.ops_evs
    obtain ⟨hcap_s, _, _, _⟩ := hsl_le7 (by omega)
    refine ⟨fun _ hne => ?_, fun h8 => absurd hph0 (by omega)⟩
    have hnS_pos : 0 < nSrc := by
      rw [hcap_s, ite_eq_left hst0] at hne; omega
    obtain ⟨ho1, ho2⟩ := hops0 hnS_pos
    simp only [Bool.false_eq_true, ↓reduceIte] at ho1 ho2
    rw [hcap_s, ite_eq_left hst0]
    change L.slotSrc.evs.length ≤ 4 * nSrc
    change 4 * s.mem (base + hdrEpochOps) < nSrc + 0 at ho1
    change 2 * L.slotSrc.evs.length ≤ 3 * nSrc + 2 * s.mem (base + hdrEpochOps) + 0 at ho2
    omega
  · rw [ite_eq_right hph0] at hsched hdst_safe
    have hpost : DualPostUpdateSafe c U nSrc L.nTrig := hsched.post_trig
    have htrig : dualTriggerCap c U nSrc L.nTrig L.trigOps = some nDst := hsched.trig_cap
    have hel16 : 16 * (L.elapsed + 2) ≤ max (whpThreshold c) nSrc := hsched.budget.2.2
    have hel_nSrc : nSrc ≠ 0 → L.elapsed ≤ nSrc := fun hne => by
      have hth : whpThreshold c ≤ nSrc := by
        simp only [EpochCapSafe, hne, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1
      rw [max_eq_right hth] at hel16; omega
    have hel_nDst : nDst ≠ 0 → L.elapsed ≤ nDst := fun hne => by
      have htrigU : L.nTrig ≤ U := by
        by_cases hs0 : nSrc = 0
        · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost; exact hpost.1
        · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost; exact hpost.2.2.1
      have har := active_rebuild_safe (nCur := L.nTrig) (d := 0) hpost htrig
        le_rfl le_rfl (Nat.zero_le _) htrigU
      have hd_idle := har.2.2.2
      simp only [DualIdleSafe, hne, ↓reduceIte] at hd_idle
      obtain ⟨hth_d, hd_U, _, _, hd_hi⟩ := hd_idle
      by_cases hs0 : nSrc = 0
      · rw [hs0, max_eq_left (Nat.zero_le _)] at hel16; omega
      · simp only [DualPostUpdateSafe, hs0, ↓reduceIte] at hpost
        obtain ⟨hth_s, hs_U, _, hs_lo, _⟩ := hpost
        rw [max_eq_right hth_s] at hel16
        by_cases hd_lt : nDst < U
        · have := hd_hi hd_lt
          have := whpThreshold_ge_pow20 c
          omega
        · omega
    refine ⟨fun hle8 hne => ?_, fun hge8 hne => ?_⟩
    · by_cases h8 : ph = 8
      · obtain ⟨hcap_s, _, _, _, _, _, _, hlen_s, _⟩ := hsl_8 h8
        have h3 := hlen_s (by omega)
        rw [hcap_s]; omega
      · obtain ⟨hcap_s, _, _, hlen_s⟩ := hsl_le7 (by omega)
        have hlen := hlen_s (by omega) (by omega)
        simp only [Bool.false_eq_true, ↓reduceIte] at hlen
        rw [hcap_s] at hne ⊢
        by_cases hst0 : stg = 0
        · rw [ite_eq_left hst0] at hne hlen ⊢
          have := hel_nSrc hne; omega
        · rw [ite_eq_right hst0] at hne hlen ⊢
          have := hel_nDst hne; omega
    · by_cases h8 : ph = 8
      · obtain ⟨_, hcap_d, _, _, _, _, _, _, hlen_d⟩ := hsl_8 h8
        rw [hcap_d] at hne ⊢
        have hlen := hlen_d (by omega)
        simp only [Bool.false_eq_true, ↓reduceIte] at hlen
        have := hel_nDst hne; omega
      · obtain ⟨hcap_d, _, _, hlen_d⟩ := hsl_ge9 (by omega)
        rw [hcap_d] at hne ⊢
        have hlen := hlen_d (by omega)
        simp only [Bool.false_eq_true, ↓reduceIte] at hlen
        have := hel_nDst hne; omega

/-- Full specification of `userQueryProg` (`opTag = 0`) across all 12 phases `0..11`. -/
theorem userQueryProg_spec {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s) (u : Fin U) :
    let ph := s.mem (base + hdrPhase)
    PrepGrowPre w (((base, s.frontier), 0), u.val) s ∧
    UserQueryPre w (base, u.val) s ∧
    (Memory.spec 0).clientState s (userQueryProg (base, u.val)) = s ∧
    (Memory.spec 0).clientResult s (userQueryProg (base, u.val)) =
      (match s_dict u with | none => (0, 0) | some v => (1, v)) ∧
    (L.ActiveGood ph →
      memoryCost (userQueryProg (base, u.val)) s ≤ 2 * epochStepCost c + 30) := by
  dsimp only
  obtain ⟨hsrc_safe, hdst_safe⟩ := dualCoreInv_cap_safe h
  have hb192 := h.base_fr; have hph_le := h.ph_le; have hstg_le := h.stg_le
  have hsched := h.sched; have hsl_le7 := h.sl_le7; have hsl_8 := h.sl_8
  have hsl_ge9 := h.sl_ge9
  dsimp only [dualCapSrc, dualMbSrc, dualPSrc, dualMbDst, dualPDst, dualNHost, dualMbHost,
    dualPgHost] at hsl_le7 hsl_8 hsl_ge9
  have huq_eval := userQueryProg_eval base u.val s
  dsimp only at huq_eval
  set ph := s.mem (base + hdrPhase)
  set stg := s.mem (base + hdrStage)
  set p0 := base + hdrPBase0
  set p1 := base + hdrPBase1
  set pSrc := if stg = 0 then p0 else p1
  set pDst := if stg = 0 then p1 else p0
  have hstg0_le3 : ph ≤ 3 → stg = 0 := fun hle3 => by
    by_cases hp0 : ph = 0
    · rw [ite_eq_left hp0] at hsched; exact hsched.stg_zero
    · rw [ite_eq_right hp0] at hsched
      by_cases hs1 : stg = 1
      · have := hsched.stg_one hs1; omega
      · omega
  have hpSrc_le3 : ph ≤ 3 → pSrc = p0 := fun hle3 => by
    dsimp only [pSrc]; exact ite_eq_left (hstg0_le3 hle3)
  have hpDst_lt10 : ph < 10 → (if ph < 10 then pDst else p0) = pDst := fun hlt =>
    ite_eq_left hlt
  have hpDst_ge10 : 10 ≤ ph → (if ph < 10 then pDst else p0) = p0 := fun hge =>
    ite_eq_right (by omega)
  have hsm_src : ph ≤ 8 → L.slotSrc.nCap = 0 →
      (liveDom L.slotSrc.s_abs).card ≤ 2 * whpThreshold c := by
    intro hle8 h0
    by_cases hle7 : ph ≤ 7
    · obtain ⟨hcap, hdict, _, _⟩ := hsl_le7 hle7
      have hcard : (liveDom L.slotSrc.s_abs).card = (Dictionary.dom s_dict).card := by
        rw [← dom_toDictState_card, hdict]
      rw [hcard]
      by_cases hst0 : stg = 0
      · rw [hcap, ite_eq_left hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hsrc_safe; exact hsrc_safe.1.le
      · have hph_nz : ph ≠ 0 := by
          intro hp0; rw [ite_eq_left hp0] at hsched; exact hst0 hsched.stg_zero
        rw [ite_eq_right hph_nz] at hdst_safe
        rw [hcap, ite_eq_right hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hdst_safe; exact hdst_safe.1.le
    · have h8 : ph = 8 := by omega
      obtain ⟨hcap, _, hdj, hdict, _, _⟩ := hsl_8 h8
      have hle_tot : (liveDom L.slotSrc.s_abs).card ≤ (Dictionary.dom s_dict).card := by
        rw [← hdict, dom_toDictState_card, liveDom_orOpt_card hdj]; omega
      by_cases hst0 : stg = 0
      · rw [hcap, ite_eq_left hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hsrc_safe; exact hle_tot.trans hsrc_safe.1.le
      · rw [ite_eq_right (by omega : ph ≠ 0)] at hdst_safe
        rw [hcap, ite_eq_right hst0] at h0
        simp only [EpochCapSafe, h0, ↓reduceIte] at hdst_safe; exact hle_tot.trans hdst_safe.1.le
  have hsm_dst : 8 ≤ ph → L.slotDst.nCap = 0 →
      (liveDom L.slotDst.s_abs).card ≤ 2 * whpThreshold c := by
    intro hge8 h0
    by_cases h8 : ph = 8
    · obtain ⟨_, hcap, hdj, hdict, _, _⟩ := hsl_8 h8
      have hle_tot : (liveDom L.slotDst.s_abs).card ≤ (Dictionary.dom s_dict).card := by
        rw [← hdict, dom_toDictState_card, liveDom_orOpt_card hdj]; omega
      have hd0 : s.mem (base + hdrNDst) = 0 := hcap ▸ h0
      rw [ite_eq_right (by omega : ph ≠ 0), hd0] at hdst_safe
      simp only [EpochCapSafe, ↓reduceIte] at hdst_safe; exact hle_tot.trans hdst_safe.1.le
    · obtain ⟨hcap, hdict, _, _⟩ := hsl_ge9 (by omega)
      have hcard : (liveDom L.slotDst.s_abs).card = (Dictionary.dom s_dict).card := by
        rw [← dom_toDictState_card, hdict]
      have hd0 : s.mem (base + hdrNDst) = 0 := hcap ▸ h0
      rw [ite_eq_right (by omega : ph ≠ 0), hd0] at hdst_safe
      simp only [EpochCapSafe, ↓reduceIte] at hdst_safe; exact hcard ▸ hdst_safe.1.le
  refine ⟨Or.inl rfl, ⟨hb192, ?_⟩, ?_, ?_, fun hgood => ?_⟩
  · -- `UserQueryPre`:
    dsimp only
    change (if ph = 8 then
        EpochProgPre w pDst s ∧
        EpochProgPre w pSrc ((Memory.spec 0).clientState s (epochQueryProg (pDst, u.val)))
      else if ph = 9 then EpochProgPre w pDst s
      else if 4 ≤ ph ∧ ph ≤ 7 then EpochProgPre w pSrc s
      else EpochProgPre w p0 s)
    by_cases h8 : ph = 8
    · rw [ite_eq_left h8]
      obtain ⟨_, _, _, _, _, hsl_s, hsl_d, _, _⟩ := hsl_8 h8
      rw [hpDst_lt10 (by omega)] at hsl_d
      obtain ⟨hst_d, _, _⟩ := hsl_d.query_spec u
      exact ⟨hsl_d.epochProgPre, hst_d.symm ▸ hsl_s.epochProgPre⟩
    · rw [ite_eq_right h8]
      by_cases h9 : ph = 9
      · rw [ite_eq_left h9]
        have hsl_d := (hsl_ge9 (by omega)).2.2.1
        rw [hpDst_lt10 (by omega)] at hsl_d
        exact hsl_d.epochProgPre
      · rw [ite_eq_right h9]
        by_cases h47 : 4 ≤ ph ∧ ph ≤ 7
        · rw [ite_eq_left h47]
          exact (hsl_le7 h47.2).2.2.1.epochProgPre
        · rw [ite_eq_right h47]
          by_cases hle3 : ph ≤ 3
          · have hsl_s := (hsl_le7 (by omega)).2.2.1
            rw [hpSrc_le3 hle3] at hsl_s
            exact hsl_s.epochProgPre
          · have hsl_d := (hsl_ge9 (by omega)).2.2.1
            rw [hpDst_ge10 (by omega)] at hsl_d
            exact hsl_d.epochProgPre
  · -- `clientState = s`:
    rw [huq_eval.1]
    by_cases h8 : ph = 8
    · rw [ite_eq_left h8]
      obtain ⟨_, _, _, _, _, hsl_s, hsl_d, _, _⟩ := hsl_8 h8
      rw [hpDst_lt10 (by omega)] at hsl_d
      rw [StateTransitionSpec.clientState_bind, (hsl_d.query_spec u).1]
      split_ifs
      · exact (hsl_s.query_spec u).1
      · rfl
    · rw [ite_eq_right h8]
      by_cases h9 : ph = 9
      · rw [ite_eq_left h9]
        have hsl_d := (hsl_ge9 (by omega)).2.2.1
        rw [hpDst_lt10 (by omega)] at hsl_d
        exact (hsl_d.query_spec u).1
      · rw [ite_eq_right h9]
        by_cases h3 : 3 < ph
        · rw [ite_eq_left h3]
          by_cases hlt8 : ph < 8
          · rw [ite_eq_left hlt8]; exact ((hsl_le7 (by omega)).2.2.1.query_spec u).1
          · rw [ite_eq_right hlt8]
            have hsl_d := (hsl_ge9 (by omega)).2.2.1
            rw [hpDst_ge10 (by omega)] at hsl_d
            exact (hsl_d.query_spec u).1
        · rw [ite_eq_right h3]
          have hsl_s := (hsl_le7 (by omega)).2.2.1
          rw [hpSrc_le3 (by omega)] at hsl_s
          exact (hsl_s.query_spec u).1
  · -- `clientResult = match s_dict u ...`:
    rw [huq_eval.2.1]
    by_cases h8 : ph = 8
    · rw [ite_eq_left h8]
      obtain ⟨_, _, _, hdict, _, hsl_s, hsl_d, _, _⟩ := hsl_8 h8
      rw [hpDst_lt10 (by omega)] at hsl_d
      obtain ⟨hst_d, hres_d, _⟩ := hsl_d.query_spec u
      obtain ⟨_, hres_s, _⟩ := hsl_s.query_spec u
      rw [prog_clientResult_bind, hst_d, hres_d, ← hdict]
      unfold toDictState orOpt
      cases hd : L.slotDst.s_abs u
      · dsimp only [Option.or, Option.map]
        rw [ite_eq_left rfl, hres_s]
        cases L.slotSrc.s_abs u <;> rfl
      · dsimp only [Option.or, Option.map]
        rw [ite_eq_right Nat.one_ne_zero]; rfl
    · rw [ite_eq_right h8]
      by_cases h9 : ph = 9
      · rw [ite_eq_left h9]
        obtain ⟨_, hdict, hsl_d, _⟩ := hsl_ge9 (by omega)
        rw [hpDst_lt10 (by omega)] at hsl_d
        rw [(hsl_d.query_spec u).2.1, ← hdict]
        unfold toDictState; cases L.slotDst.s_abs u <;> rfl
      · rw [ite_eq_right h9]
        by_cases h3 : 3 < ph
        · rw [ite_eq_left h3]
          by_cases hlt8 : ph < 8
          · rw [ite_eq_left hlt8]
            obtain ⟨_, hdict, hsl_s, _⟩ := hsl_le7 (by omega)
            rw [(hsl_s.query_spec u).2.1, ← hdict]
            unfold toDictState; cases L.slotSrc.s_abs u <;> rfl
          · rw [ite_eq_right hlt8]
            obtain ⟨_, hdict, hsl_d, _⟩ := hsl_ge9 (by omega)
            rw [hpDst_ge10 (by omega)] at hsl_d
            rw [(hsl_d.query_spec u).2.1, ← hdict]
            unfold toDictState; cases L.slotDst.s_abs u <;> rfl
        · rw [ite_eq_right h3]
          obtain ⟨_, hdict, hsl_s, _⟩ := hsl_le7 (by omega)
          rw [hpSrc_le3 (by omega)] at hsl_s
          rw [(hsl_s.query_spec u).2.1, ← hdict]
          unfold toDictState; cases L.slotSrc.s_abs u <;> rfl
  · -- `memoryCost ≤ 2 * epochStepCost c + 30`:
    rw [huq_eval.2.2]
    by_cases h8 : ph = 8
    · rw [ite_eq_left h8]
      obtain ⟨_, _, _, _, _, hsl_s, hsl_d, _, _⟩ := hsl_8 h8
      rw [hpDst_lt10 (by omega)] at hsl_d
      obtain ⟨hst_d, _, hc_d⟩ := hsl_d.query_spec u
      obtain ⟨_, _, hc_s⟩ := hsl_s.query_spec u
      have hcd := hc_d (hsm_dst (by omega)) (hgood.2 (by omega))
      have hcs := hc_s (hsm_src (by omega)) (hgood.1 (by omega))
      rw [Realization.memoryCost_bind', hst_d]
      split_ifs
      · omega
      · simp only [memoryCost_pure]; omega
    · rw [ite_eq_right h8]
      by_cases h9 : ph = 9
      · rw [ite_eq_left h9]
        obtain ⟨_, _, hsl_d, _⟩ := hsl_ge9 (by omega)
        rw [hpDst_lt10 (by omega)] at hsl_d
        have hcd := (hsl_d.query_spec u).2.2 (hsm_dst (by omega)) (hgood.2 (by omega))
        omega
      · rw [ite_eq_right h9]
        by_cases h3 : 3 < ph
        · rw [ite_eq_left h3]
          by_cases hlt8 : ph < 8
          · rw [ite_eq_left hlt8]
            have hcs := ((hsl_le7 (by omega)).2.2.1.query_spec u).2.2 (hsm_src (by omega))
              (hgood.1 (by omega))
            omega
          · rw [ite_eq_right hlt8]
            have hsl_d := (hsl_ge9 (by omega)).2.2.1
            rw [hpDst_ge10 (by omega)] at hsl_d
            have hcd := (hsl_d.query_spec u).2.2 (hsm_dst (by omega)) (hgood.2 (by omega))
            omega
        · rw [ite_eq_right h3]
          have hsl_s := (hsl_le7 (by omega)).2.2.1
          rw [hpSrc_le3 (by omega)] at hsl_s
          have hcs := (hsl_s.query_spec u).2.2 (hsm_src (by omega)) (hgood.1 (by omega))
          omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

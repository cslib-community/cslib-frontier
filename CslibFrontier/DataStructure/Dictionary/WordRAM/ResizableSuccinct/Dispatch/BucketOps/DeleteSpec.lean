/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeletePrep
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeleteFinish
-- Reads private `compDispatch_spec` and unfolds `compFeistelCoordsProg`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.CoordsDelta
-- Reads private `compDeletePrepBodyGenProg_spec` and unfolds `compDeletePrepWithHashGenProg`.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeletePrep
-- Reads private `compDeleteFinishGenProg` and `compDeleteFoundGenProg_effect`, and unfolds finish.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps.DeleteFinish
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Dictionary-Level Two-Phase Deletion Specification (`DictStateInv`)

Establishes `DictStateInv`, `FixedCoupled`, and amortized `memoryCost` bounds for two-phase
compacted deletion (`compDeleteWithHashGenProg_dict_spec`).

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.compDeleteWithHashGenProg_dict_spec`:
  dictionary-level two-phase deletion specification.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-- Dictionary-level specification of two-phase compacted deletion (`compDeletePrepWithHashGenProg`
on `s` followed by `compDeleteFinishWithHashGenProg` on `s_mid`, allowing the intermediate second
hash evaluation to overwrite limb scratch below `metaBase + offCompLM U w N`). -/
theorem compDeleteWithHashGenProg_dict_spec {metaBase itemBase U V w N m_items : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s s_mid : Memory.State}
    (henv : CompEpochEnv U V w N metaBase itemBase m_items s)
    (hfit_off : Fits w (metaBase + offCompItems U w N))
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hm_items : totalSlots N (compGmAt metaBase U w N s.mem) ≤ m_items)
    (hmid_fr : s_mid.frontier = s.frontier)
    (hmid_out : ∀ a, metaBase + offCompLM U w N ≤ a → s_mid.mem a = s.mem a)
    (u : Fin U) :
    let q := keyQuotient (bucketBits N) u.val
    let h_q := hValOfSeed U N θ q
    let d_prep := ((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q))
    let prog_prep := compDeletePrepWithHashGenProg d_prep
    ∃ found j_del phys_del q_last : ℕ,
      let prep := (((found, j_del), phys_del), q_last)
      let h_q_last := hValOfSeed U N θ q_last
      let d_fin :=
        ((((mkCompParams U V w N, (metaBase, itemBase)), (u.val, h_q)),
          ((found, j_del), phys_del)), h_q_last)
      let prog_fin := compDeleteFinishWithHashGenProg d_fin
      let s' := (Memory.spec 0).clientState s_mid prog_fin
      let gm₀ := compGmAt metaBase U w N s.mem
      let gm' := compGmAt metaBase U w N s'.mem
      (Memory.spec 0).clientResult s prog_prep = prep ∧
      (found = 1 ↔ (s_abs u).isSome) ∧
      CompQueryWithHashPre w d_prep s ∧
      (Memory.spec 0).clientState s prog_prep = s ∧
      q_last < 2 ^ quotientBits U N ∧
      CompDeleteFinishWithHashPre w d_fin s_mid ∧
      CompOpFrame metaBase itemBase U V w N m_items s_mid s' ∧
      (∃ s_fix' : Memory.State,
        DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs u none) s_fix' ∧
        FixedCoupled metaBase itemBase U V w N s_fix' s') ∧
      memoryCost prog_prep s + memoryCost prog_fin s_mid + 98 * slotPotential N gm' ≤
        98 * slotPotential N gm₀ + 354 +
          12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
  intro q h_q d_prep prog_prep
  obtain ⟨L, hb_inv⟩ := hinv.hbucket
  set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
  set m := mOfSeed U N θ q
  obtain ⟨hb_eq, hq_eq, hm_eq, hb_lt, hm_lt, hslot, hpre_prep⟩ :=
    compDispatch_spec henv hfit_off hinv hcpl hm_items u
  have hwf := ghostDictParamsWf henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  have hg_env := ghostDictEnvGen henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V
  obtain ⟨found, j_del, phys_del, q_last, hres_fix_prep, _, _, hq_last_lt, _, _, _, hinv_fix', _⟩ :=
    deleteWithHashProg_dict_spec (w := ghostW w) hwf hg_env θ hinv u
  have hchain : IsDLChain N (lmHead N (compLmAt metaBase U w N s.mem) b m)
      (lmPrev N (compLmAt metaBase U w N s.mem) b)
      (lmNext N (compLmAt metaBase U w N s.mem) b) (L b m) := by
    rw [hcpl.lm_eq]; exact hb_inv.hchains.1 b hb_lt m hm_lt
  have hc_lt : ∀ j ∈ L b m, j < bCount N (compGmAt metaBase U w N s.mem) b := fun j hj => by
    rw [hcpl.gm_eq]; exact ((hb_inv.hchain_mem b hb_lt m hm_lt j).mp hj).1
  obtain ⟨hst_dp, hres_dp, hcost_dp⟩ := compDeletePrepBodyGenProg_spec (q_target := q)
    henv hcpl hslot hm_items hb_lt hm_lt hchain hc_lt
  have hc_res : (Memory.spec 0).clientResult s
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s
  have hc_res_mid : (Memory.spec 0).clientResult s_mid
      (compFeistelCoordsProg (mkCompParams U V w N, (u.val, h_q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u.val h_q s_mid
  have hfix_prep_eq : (Memory.spec 0).clientResult s_fix
      (deletePrepWithHashProg U V (ghostW w) N ((0, u.val), h_q)) =
      (Memory.spec 0).clientResult s_fix
        (deletePrepProg U V (ghostW w) N (hashSpace U (ghostW w) N) (((0, b), q), m)) := by
    change (Memory.spec 0).clientResult s_fix
      (deletePrepProg U V (ghostW w) N (hashSpace U (ghostW w) N)
        (((0, (h_q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
          u.val >>> bucketBits N), h_q >>> bucketBits N)) = _
    rw [and_mask_xor_eq_feistelBucket (bucketBits N) u.val h_q,
      Nat.shiftRight_eq_div_pow u.val (bucketBits N)]
    rfl
  obtain ⟨hlen_pr, hovf_pr, _⟩ := chain_and_overflow_le_probeExcess θ hb_inv u
  have henv_mid : CompEpochEnv U V w N metaBase itemBase m_items s_mid :=
    henv.of_mem_eq hmid_fr.ge
  have h0_off : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1_off : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2_off : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3_off : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have h_it : metaBase + offCompItems U w N ≤ itemBase := henv.meta_le_item
  have hlm_mid : compLmAt metaBase U w N s_mid.mem = compLmAt metaBase U w N s.mem :=
    compLmAt_congr henv.pos_w fun a ha => hmid_out a ha.1
  have hgm_mid : compGmAt metaBase U w N s_mid.mem = compGmAt metaBase U w N s.mem :=
    compGmAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have htd_mid : compTDAt metaBase U w N s_mid.mem = compTDAt metaBase U w N s.mem :=
    compTDAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have hdt_mid : compDTAt metaBase U w N s_mid.mem = compDTAt metaBase U w N s.mem :=
    compDTAt_congr henv.pos_w fun a ha => hmid_out a (by omega)
  have hcpl_mid : FixedCoupled metaBase itemBase U V w N s_fix s_mid :=
    ⟨hgm_mid.trans hcpl.gm_eq, hlm_mid.trans hcpl.lm_eq,
      by simpa only [hgm_mid, htd_mid, hdt_mid] using hcpl.win_inv,
      fun i => htd_mid.symm ▸ hcpl.td_lt i, fun i => hdt_mid.symm ▸ hcpl.dt_lt i,
      fun d hd => by
        rw [hgm_mid, compQuotAt_congr henv.pos_w fun a ha => hmid_out a (by omega), hdt_mid]
        exact hcpl.quot_eq d (by simpa only [epochTotalSlots, hgm_mid] using hd),
      fun d hd => by
        rw [hgm_mid, compValAt_congr henv.pos_w fun a ha => hmid_out a (by omega), hdt_mid]
        exact hcpl.val_eq d (by simpa only [epochTotalSlots, hgm_mid] using hd)⟩
  refine ⟨found, j_del, phys_del, q_last, ?_⟩
  intro prep h_q_last d_fin prog_fin s' gm₀ gm'
  set m_last := mOfSeed U N θ q_last
  have hm_last_lt : m_last < numMicroPerBucket N := mOfSeed_lt U N θ q_last
  have hprep_comp_res : (Memory.spec 0).clientResult s prog_prep = prep := by
    dsimp only [prog_prep, d_prep, compDeletePrepWithHashGenProg]
    rw [StateTransitionSpec.clientResult_bind, clientState_compFeistelCoordsProg, hc_res]
    exact (hres_dp.trans hfix_prep_eq.symm).trans hres_fix_prep
  have hprep_comp_st : (Memory.spec 0).clientState s prog_prep = s := by
    dsimp only [prog_prep, d_prep, compDeletePrepWithHashGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res]
    exact hst_dp
  have hgm_eq : compGmAt metaBase U w N s.mem =
      gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem := hcpl.gm_eq
  have hprep_comp_cost : memoryCost prog_prep s ≤
      42 + 12 * probeExcess N (qStage1 U N θ.1) (polyStage2 U N) θ.2 (Dictionary.dom s_abs) u := by
    dsimp only [prog_prep, d_prep, compDeletePrepWithHashGenProg]
    rw [memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s) _,
      memoryCost_compFeistelCoordsProg, hc_res, zero_add]
    rw [hgm_eq] at hcost_dp
    dsimp only [b, q, m, probeExcess] at hcost_dp hlen_pr hovf_pr ⊢; omega
  have hfit_hq_last : Fits w h_q_last :=
    (fits_compFeistelCoords (s := s_mid) henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V hfit_off
      (u.isLt.trans henv.lt_pow_U) (hValOfSeed_lt U N θ q_last)).2.1
  have hprep_spec_fix := deletePrepProg_bucket_spec hb_inv hg_env hb_lt (q_target := q) (m := m)
    rfl hm_lt
  dsimp only at hprep_spec_fix
  rw [← hfix_prep_eq, hres_fix_prep] at hprep_spec_fix
  dsimp only [deletePrepFound, deletePrepIdx, deletePrepPhys] at hprep_spec_fix
  have hbm_eq := bucketMapOfState_feistelBucket henv.le_U (hValOfSeed U N θ) s_abs u
  let gm_mid := compGmAt metaBase U w N s_mid.mem
  obtain ⟨hfound_iff, hfound_slot⟩ : (found = 1 ↔ (s_abs u).isSome) ∧
      (found = 1 →
        j_del < bCount N gm_mid b ∧ phys_del = slotOf N gm_mid b j_del ∧
        (j_del < effBucketCap N → j_del ∈ L b m) ∧
        (bCount N gm_mid b - 1 < effBucketCap N → bCount N gm_mid b - 1 ∈ L b m_last)) := by
    have hbr := hprep_spec_fix.2.2.2
    by_cases hex : ∃ j < bCount N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b,
        quotAt 0 U (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem
          (slotOf N (gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix.mem) b j) = q
    · rw [ite_eq_left hex] at hbr
      obtain ⟨hf1, hj_lt_fix, hq_del, hphys_eq_fix, hq_last_eq⟩ := hbr
      refine ⟨⟨fun _ => hbm_eq.symm ▸ (hb_inv.hmap_dom b hb_lt q).mpr hex, fun _ => hf1⟩,
        fun _ => ?_⟩
      dsimp only [gm_mid]
      rw [hgm_mid, hgm_eq]
      exact ⟨hj_lt_fix, hphys_eq_fix,
        fun hj_cap => (hb_inv.hchain_mem b hb_lt m hm_lt j_del).mpr
          ⟨hj_lt_fix, hj_cap, by rw [hq_del]⟩,
        fun hj_cap => (hb_inv.hchain_mem b hb_lt m_last hm_last_lt _).mpr
          ⟨by omega, hj_cap, congrArg (mOfSeed U N θ) hq_last_eq.symm⟩⟩
    · rw [ite_eq_right hex] at hbr
      exact ⟨⟨by omega, fun hs => (hex ((hb_inv.hmap_dom b hb_lt q).mp (hbm_eq ▸ hs))).elim⟩,
        by omega⟩
  have hslot_mid : SlotStoreInv N (compGmAt metaBase U w N s_mid.mem) := hgm_mid.symm ▸ hslot
  have hm_items_mid : totalSlots N (compGmAt metaBase U w N s_mid.mem) ≤ m_items :=
    hgm_mid.symm ▸ hm_items
  have hpre_fin : CompDeleteFinishWithHashPre w d_fin s_mid := by
    refine ⟨fits_compFeistelCoords henv.pos_w henv.le_U henv.lt_pow_U henv.le_pow_V hfit_off
        (u.isLt.trans henv.lt_pow_U) (hValOfSeed_lt U N θ q),
      hfit_hq_last, fits_const_of_offCompItems hfit_off (by decide), ?_⟩
    rw [hb_eq, hm_eq, cpBucketBits_mk]
    intro hf1
    obtain ⟨hj_lt, hphys_eq, hmem_del, hmem_last⟩ := hfound_slot hf1
    exact ⟨U, V, N, m_items, s_fix, L, rfl, henv_mid, hcpl_mid, hslot_mid, hm_items_mid,
      hb_lt, hm_lt, hm_last_lt, hj_lt, hphys_eq, hb_inv.hchains, hmem_del, hmem_last⟩
  unfold deleteFinishWithHashProg deleteFinishWithHashGenProg at hinv_fix'
  simp only [p_bucketBits_mk, p_bucketMask_mk, pure_bind, and_mask_xor_eq_feistelBucket,
    deleteFinishGenProg, deleteFoundGenProg_mk] at hinv_fix'
  set df_prog := compDeleteFinishGenProg
    ((((((mkCompParams U V w N, (metaBase, itemBase)), b), (found, j_del)), phys_del), m), m_last)
  have hs'_eq : s' = (Memory.spec 0).clientState s_mid df_prog := by
    dsimp only [s', prog_fin, d_fin, compDeleteFinishWithHashGenProg]
    rw [StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res_mid]
    simp only [pure_bind, cpBucketBits_mk]; rfl
  have hcost_fin_eq : memoryCost prog_fin s_mid = memoryCost df_prog s_mid := by
    dsimp only [prog_fin, d_fin, compDeleteFinishWithHashGenProg]
    rw [memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s_mid) _,
      memoryCost_compFeistelCoordsProg, hc_res_mid, zero_add]
    simp only [pure_bind, cpBucketBits_mk]; rfl
  refine ⟨hprep_comp_res, hfound_iff, hpre_prep, hprep_comp_st, hq_last_lt, hpre_fin, ?_⟩
  dsimp only [gm', gm₀]
  rw [hs'_eq, hcost_fin_eq]
  dsimp only [df_prog, compDeleteFinishGenProg]
  by_cases hf1 : found = 1
  · obtain ⟨hj_lt, hphys_eq, hmem_del, hmem_last⟩ := hfound_slot hf1
    obtain ⟨hfr_fd, hcpl_fd, hcost_fd⟩ := compDeleteFoundGenProg_effect
      henv_mid hcpl_mid hslot_mid hm_items_mid hb_lt hm_lt hm_last_lt hj_lt
      hb_inv.hchains hmem_del hmem_last
    rw [← hphys_eq] at hfr_fd hcpl_fd hcost_fd
    rw [hgm_mid] at hcost_fd
    simp only [hf1, ↓reduceIte, pure_bind] at hinv_fix' ⊢
    dsimp only [b, m, q] at hcost_fd ⊢
    exact ⟨hfr_fd, ⟨_, hinv_fix', hcpl_fd⟩, by omega⟩
  · simp only [hf1, ↓reduceIte, pure_bind, prog_runClient_state_pure,
      memoryCost_pure] at hinv_fix' ⊢
    rw [hgm_mid]
    exact ⟨CompOpFrame.refl s_mid, ⟨s_fix, hinv_fix', hcpl_mid⟩, by omega⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

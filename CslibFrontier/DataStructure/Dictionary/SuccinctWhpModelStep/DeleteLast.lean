/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.Invariants
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.MapRel
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.DeleteHelpers

/-!
# Fast-Mode Deletion Without Relocation (`fastDelete_afterDel_last_spec`)

This module proves `fastDelete_afterDel_last_spec`: when `fastFindLoc` locates key `u` at the
terminal bucket coordinate `loc_del = fs.bktCount b - 1`, `fastDeleteRemove` followed by
`fastDeleteShrink` preserves `CoreFastInv` (on `Function.update dict u none`), `OvermarsBucketInv`
on all other buckets, `PreOvermarsBucketInv` on bucket `b`, and `ValidEpochStagePreTick`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.fastDelete_afterDel_last_spec`: invariant
  preservation for fast-mode deletion at the last occupied bucket coordinate.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp.ModelStepAux

/-- Intermediate `fsAfterDel` invariant when `fastFindLoc` finds `loc_del = loc_last`. -/
theorem fastDelete_afterDel_last_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) {loc_del : ℕ}
    (hld_lt : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val))
    (hq_del : fs.quotArr
      (fs.physSlot n_max (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc_del) =
      keyQuotient (bWhp n_max) u.val)
    (hnot_lt : ¬(loc_del <
      fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) - 1)) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let loc_last := fs.bktCount b - 1
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let fsA := fastDeleteShrink n_max b loc_last fs1
    CoreFastInv c U V n_max θ fsA (Function.update dict u none) ∧
    (∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fsA b') ∧
    PreOvermarsBucketInv c U n_max θ fsA b ∧
    ValidEpochStagePreTick c U n_max θ fsA := by
  intro b loc_last
  set st_del := fs.locState b loc_del
  set rKey_u := fpReducedKey c U n_max θ.2 u
  set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set buf1 :=
    if st_del = 2 then
      Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
    else if st_del = 3 then
      Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
    else fs.buf
  set lIdx := fs.liveSliceIdx b
  set slices1 :=
    if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update fs.slices lIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices lIdx) fp_live_u)
    else fs.slices
  set omIdx := fs.overmarsSliceIdx b
  set slices2 :=
    if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update slices1 omIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices1 omIdx) fp_live_u)
    else slices1
  set rebActiveB : Bool :=
    decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  set rIdx := fs.rebSliceIdx b
  set slices3 :=
    if rebActiveB && decide (loc_del < fs.rebScanCursor ∧
        (st_del = 1 ∨ st_del = 2 + fs.oldEp)) then
      Function.update slices2 rIdx
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices2 rIdx) (fpOfSalt c U n_max θ.2 fs.rebCandSalt u))
    else slices2
  set fs1_loc : FastState := { fs with buf := buf1, slices := slices3 }
  have hfs1_eq : fastDeleteRemove c U n_max θ fs u b loc_del = fs1_loc := rfl
  let fsA := fastDeleteShrink n_max b loc_last fs1_loc
  have hfsA_eq : fastDeleteShrink n_max b loc_last fs1_loc = fsA := rfl
  dsimp only
  rw [hfs1_eq, hfsA_eq]
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hcnt : fs.bktCount b = loc_last + 1 := by
    dsimp only [b, loc_last] at hld_lt ⊢; omega
  have heq_ll : loc_del = loc_last := by
    dsimp only [b, loc_last] at hld_lt hnot_lt ⊢; omega
  have hkv_del : fs.keyValAt c U n_max θ.1 b loc_del = u.val := by
    dsimp only [FastState.keyValAt, b]
    rw [hq_del]
    exact feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u := by
    dsimp only [FastState.rKeyAt, rKey_u]; simp [hkv_del, u.isLt]
  have hs_b : fs.bktSalt b < sMaxWhp c n_max := hv.bktSalt_lt b hb
  have hfp_live_del : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_del = fp_live_u := by
    dsimp only [FastState.fpAt, fp_live_u, fpOfSalt]; simp [hs_b, hkv_del, u.isLt]
  have hsl2_eq : slices2 = slices1 := by
    dsimp only [slices2]
    refine ite_eq_right fun ⟨_, hlt_c, _⟩ => ?_
    rcases hv.overmars_valid b hb with ⟨_, _⟩ | ⟨_, _, hcur_lt, _⟩ <;> omega
  have hsl3_eq : slices3 = slices1 := by
    dsimp only [slices3]
    rw [hsl2_eq]
    refine ite_eq_right fun hcond => ?_
    simp only [rebActiveB, Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨hs2, _, hdb, hcs, _⟩, hlt_r, _⟩ := hcond
    have hstg := hv.stage_valid
    dsimp only [ValidEpochStage] at hstg
    simp only [hs2, Nat.reduceEqDiff, ↓reduceIte] at hstg
    obtain ⟨hcur_or, _⟩ := hstg.2.2.2.2.2.2 hcs
    rw [hdb] at hcur_or
    rcases hcur_or with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩ <;> omega
  obtain ⟨hlr_b, hor_b, hro_ne⟩ := hv.roles_valid b hb
  have hl_ne_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ r < 3, 3 * b' + r ≠ lIdx := by
    intro b' _ hbb r hr heq
    exact hbb (sliceIdx_inj hr hlr_b heq).1
  have hsl_other {idx : ℕ} (hne : idx ≠ lIdx) : fsA.slices idx = fs.slices idx := by
    change slices3 idx = fs.slices idx
    rw [hsl3_eq]
    dsimp only [slices1]
    split
    · exact Function.update_of_ne hne _ _
    · rfl
  have hcntA_b : fsA.bktCount b = loc_last := Function.update_self _ _ _
  have hcntA_other {b' : ℕ} (hbb : b' ≠ b) : fsA.bktCount b' = fs.bktCount b' :=
    Function.update_of_ne hbb _ _
  have hfp_eq : ∀ salt b', fsA.fpAt c U n_max θ salt b' = fs.fpAt c U n_max θ salt b' :=
    fun salt b' => fpAt_eq_of_fields rfl rfl salt b'
  have hrk_eq : fsA.rKeyAt c U n_max θ = fs.rKeyAt c U n_max θ := rKeyAt_eq_of_fields rfl rfl
  have hls_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
      fsA.locState b' loc = fs.locState b' loc := by
    intro b' _ loc hloc
    dsimp only [fsA, fastDeleteShrink, fs1_loc] at hloc ⊢
    by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self] at hloc ⊢
      exact Function.update_of_ne (Nat.ne_of_lt hloc) _ _
    · simp [hbb]
  have hcnt_lt_orig : ∀ {b' loc}, loc < fsA.bktCount b' → loc < fs.bktCount b' :=
    fun hloc => lt_of_lt_update_le (by omega) hloc
  have hpool := pool_release_last (fs' := fsA) hv.toCore hb hcnt rfl rfl rfl
    (by dsimp only [fsA, fastDeleteShrink, fs1_loc]; split_ifs <;> rfl)
    (by dsimp only [fsA, fastDeleteShrink, fs1_loc]; split_ifs <;> rfl)
  obtain ⟨hq_inj, hdict_map⟩ := dict_map_after_delete (fs' := fsA) hv.toCore rfl hcnt
    (hcnt ▸ hld_lt) hq_del rfl
    (fun _ _ _ _ _ => ⟨rfl, rfl⟩)
    (fun loc' hloc' => ⟨loc', by omega, by omega, rfl, rfl,
      fun l₂ hl₂ heq => hv.quot_inj b hb loc' (by omega) l₂ (by omega) heq⟩)
    (fun loc hloc hne => ⟨loc, by omega, rfl, rfl⟩)
  have hpres_eq : loc_del = loc_last →
      ∀ b' < numBucketsWhp n_max, ∀ loc < fsA.bktCount b',
        fsA.locState b' loc = fs.locState b' loc ∧
        fsA.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc :=
    fun _ b' hb' loc hloc => ⟨hls_pres b' hb' loc hloc, congrFun (congrFun hrk_eq b') loc⟩
  have hbuf_cur := buf_valid_after_delete (ep := fs.curEp) (fs' := fsA) hv.toCore hb hcnt
    (hcnt ▸ hld_lt) hrk_del hv.bufCur_valid rfl hpres_eq (fun hlt => absurd hlt hnot_lt)
  have hb_old_eq : fsA.buf fs.oldEp =
      (let tr1 :=
        if fs.locState b loc_del = 2 + fs.oldEp then
          bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
        else fs.buf fs.oldEp
      if loc_del < loc_last then
        if fs.locState b loc_last = 2 + fs.oldEp then
          bufInsert (cTabWhp c) (bCharWhp n_max) tr1
            (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else tr1
      else tr1) := by
    dsimp only
    rw [ite_eq_right hnot_lt]
    exact buf_del_at_ep fs.buf (FastState.oldEp_or hv.curEp_or)
  have hlive_b : ∃ liveMap',
      ValidWhpSlice n_max (fsA.liveInsCount b) (fsA.slices (fsA.liveSliceIdx b)) liveMap' ∧
      SliceMapRel (fsA.fpAt c U n_max θ (fsA.bktSalt b) b)
        (fun loc => inLiveTree fsA.rebStage fsA.oldEp (fsA.rebDoneFlag b) (fsA.locState b loc) =
          true)
        (fsA.bktCount b) liveMap' := by
    obtain ⟨lm0, hvl0, hrl0⟩ := hv.live_valid b hb
    rw [hcnt] at hrl0
    rw [hfp_eq]
    dsimp only [fsA, fastDeleteShrink, fs1_loc, FastState.liveSliceIdx, FastState.oldEp]
    rw [hsl3_eq]
    simp only [Function.update_self]
    by_cases hinL : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
    · dsimp only [slices1, lIdx, FastState.liveSliceIdx]
      rw [ite_eq_left hinL, Function.update_self]
      have hfp_lt : fp_live_u < 2 ^ fpBitsWhp n_max :=
        hfp_live_del ▸ fpAt_lt θ fs (fs.bktSalt b) b loc_del
      have hvd := hvl0.delete_spec hv.hth (hv.liveInsCount_le hb) hfp_lt
      have hinL_ll : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
          (fs.locState b loc_last) = true := heq_ll ▸ hinL
      have hfp_ll : fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last = fp_live_u :=
        heq_ll ▸ hfp_live_del
      have hrld := sliceMapRel_delete_last hrl0 hinL_ll fun loc hlt hpl heq =>
        Nat.ne_of_lt hlt (hv.live_fp_inj b hb loc (by omega) loc_last (by omega) hpl hinL_ll heq)
      rw [hfp_ll] at hrld
      refine ⟨_, hvd, hrld.congr (fun _ _ => rfl) fun loc hlt => ?_⟩
      rw [Function.update_of_ne (Nat.ne_of_lt hlt)]; exact Iff.rfl
    · dsimp only [slices1, lIdx, FastState.liveSliceIdx]
      rw [ite_eq_right hinL]
      have hninL_ll : ¬(inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
          (fs.locState b loc_last) = true) := heq_ll ▸ hinL
      have hrls := sliceMapRel_skip_last hrl0 hninL_ll
      refine ⟨lm0, hvl0, hrls.congr (fun _ _ => rfl) fun loc hlt => ?_⟩
      rw [Function.update_of_ne (Nat.ne_of_lt hlt)]; exact Iff.rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine
      { hth := hv.hth
        curEp_or := hv.curEp_or
        epochClock_lt := hv.epochClock_lt
        rebStage_le := hv.rebStage_le
        rebCollision_zero := hv.rebCollision_zero
        qv_global := hv.qv_global
        bktCount_le := fun b' hb' => by
          rcases eq_or_ne b' b with rfl | hbb
          · rw [hcntA_b]
            exact Nat.le_of_lt ((heq_ll ▸ hld_lt).trans_le (hv.bktCount_le b hb))
          · rw [hcntA_other hbb]
            exact hv.bktCount_le b' hb'
        bktCount_ge_zero := fun b' hge =>
          hcntA_other ((hb.trans_le hge).ne') ▸ hv.bktCount_ge_zero b' hge
        locState_active := fun b' hb' loc hloc => by
          rw [hls_pres b' hb' loc hloc]
          exact hv.locState_active b' hb' loc (hcnt_lt_orig hloc)
        locState_inactive := fun b' loc hna => by
          dsimp only [fsA, fastDeleteShrink, fs1_loc] at hna ⊢
          by_cases hbb : b' = b
          · subst hbb
            rw [Function.update_self] at hna ⊢
            by_cases hll : loc = loc_last
            · subst hll; simp
            · rw [Function.update_of_ne hll]
              exact hv.locState_inactive b loc fun ⟨_, hlt⟩ => hna ⟨hb, by omega⟩
          · simp only [Function.update_of_ne hbb] at hna ⊢
            exact hv.locState_inactive b' loc hna
        active_item := fun b' hb' loc hloc => hv.active_item b' hb' loc (hcnt_lt_orig hloc)
        quot_inj := hq_inj
        dict_map := hdict_map
        poolFreeTop_le := hpool.1
        backPtr_valid := hpool.2.1
        freeStack_lt := hpool.2.2.1
        backPtr_inj := hpool.2.2.2.1
        freeStack_inj := hpool.2.2.2.2.1
        back_free_disj := hpool.2.2.2.2.2.1
        pool_conservation := hpool.2.2.2.2.2.2
        roles_valid := hv.roles_valid
        bktSalt_lt := hv.bktSalt_lt
        live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
          rw [hls_pres b' hb' l₁ hl₁] at hin₁
          rw [hls_pres b' hb' l₂ hl₂] at hin₂
          rw [hfp_eq] at hfeq
          exact hv.live_fp_inj b' hb' l₁ (hcnt_lt_orig hl₁) l₂ (hcnt_lt_orig hl₂) hin₁ hin₂ hfeq
        live_valid := fun b' hb' => by
          by_cases hbb : b' = b
          · subst hbb; exact hlive_b
          · obtain ⟨lm, hvl, hrl⟩ := hv.live_valid b' hb'
            refine ⟨lm, ?_, ?_⟩
            · change ValidWhpSlice n_max (fs.liveInsCount b') (fsA.slices (fs.liveSliceIdx b')) lm
              have hne : fs.liveSliceIdx b' ≠ lIdx :=
                hl_ne_other b' hb' hbb _ (hv.roles_valid b' hb').1
              rwa [hsl_other hne]
            · rw [hfp_eq]
              dsimp only [fsA, fastDeleteShrink, fs1_loc, FastState.oldEp]
              simp only [Function.update_of_ne hbb]
              exact hrl
        rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ hst₁ hst₂ hrkeq => by
          rw [hls_pres b₁ hb₁ l₁ hl₁] at hst₁
          rw [hls_pres b₂ hb₂ l₂ hl₂] at hst₂
          rw [hrk_eq] at hrkeq
          exact hv.rKey_buf_inj b₁ hb₁ l₁ (hcnt_lt_orig hl₁) b₂ hb₂ l₂ (hcnt_lt_orig hl₂)
            hst₁ hst₂ hrkeq
        bufCur_valid := by
          have hb1 : fsA.buf fsA.curEp =
              if st_del = 2 + fs.curEp then
                bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey_u
              else fs.buf fs.curEp := buf_del_at_ep fs.buf hv.curEp_or
          obtain ⟨hia_eq, hna_eq, hmap_cur, _⟩ := hbuf_cur
          dsimp only [st_del] at hb1 ⊢
          rw [ite_eq_right hnot_lt, ← hb1] at hia_eq hna_eq hmap_cur
          exact ⟨hia_eq ▸ hv.bufCur_valid.1,
            hna_eq ▸ hia_eq ▸ hv.bufCur_valid.2.1, hmap_cur⟩
        bufOld_valid := bufOld_valid_after_delete hv.toCore hb hcnt (hcnt ▸ hld_lt) hrk_del rfl
          rfl rfl hb_old_eq hpres_eq (fun hlt => absurd hlt hnot_lt) }
  · intro b' hb' hbb
    refine OvermarsBucketInv.of_eq_on (hv.overmars_valid b' hb') (hfp_eq _ _) rfl rfl rfl ?_ ?_
      rfl rfl rfl rfl ?_
    · dsimp only [fsA, fastDeleteShrink, fs1_loc]; exact Function.update_of_ne hbb _ _
    · exact hcntA_other hbb
    · exact hsl_other (hl_ne_other b' hb' hbb _ (hv.roles_valid b' hb').2.1)
  · rcases hv.overmars_valid b hb with
      ⟨ha0, hlic⟩ | ⟨ha1, h16, hcur_lt, hlin, hins, omM, hv_om, hr_om⟩
    · exact Or.inl ⟨ha0, hlic.le⟩
    · have hcur_le : fs.overmarsCursor b ≤ loc_last := by omega
      dsimp only [PreOvermarsBucketInv]
      have hoa_eq : fsA.overmarsActive b = fs.overmarsActive b := rfl
      have hoc_eq : fsA.overmarsCursor b = fs.overmarsCursor b := rfl
      have hlic_eq : fsA.liveInsCount b = fs.liveInsCount b := rfl
      have hoi_eq : fsA.overmarsInsCount b = fs.overmarsInsCount b := rfl
      rw [hoa_eq, hoc_eq, hlic_eq, hoi_eq]
      refine Or.inr ⟨ha1, h16, ?_, by omega, by omega, omM, ?_, ?_⟩
      · exact hcntA_b ▸ hcur_le
      · have hne : fs.overmarsSliceIdx b ≠ lIdx := fun heq =>
          hro_ne (Nat.add_left_cancel heq.symm)
        change ValidWhpSlice n_max (fs.overmarsInsCount b) (fsA.slices (fs.overmarsSliceIdx b)) omM
        rw [hsl_other hne]
        exact hv_om
      · rw [hfp_eq]
        dsimp only [fsA, fastDeleteShrink, fs1_loc, FastState.oldEp]
        simp only [Function.update_self, Nat.min_eq_right hcur_le]
        refine hr_om.congr (fun _ _ => rfl) fun loc hlt => ?_
        rw [Function.update_of_ne (by omega : loc ≠ loc_last)]; exact Iff.rfl
  · refine preTick_after_delete_of_stage2 hv.toCore hv.stage_valid.toPreTick hb hcnt
      (hcnt ▸ hld_lt) hrk_del rfl rfl rfl rfl rfl rfl rfl rfl rfl hb_old_eq hpres_eq
      (fun hlt => absurd hlt hnot_lt) fun hs2 => ?_
    have hstg_full := hv.stage_valid
    dsimp only [ValidEpochStage] at hstg_full
    simp only [hs2, Nat.reduceEqDiff, ↓reduceIte] at hstg_full
    rcases hstg_full with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
    refine ⟨hd1, hd2, hd3, hd4, hd5, fun b' hb' loc hloc hst_old => ?_, fun hcs => ?_⟩
    · rw [hls_pres b' hb' loc hloc] at hst_old
      exact hd6 b' hb' loc (hcnt_lt_orig hloc) hst_old
    · dsimp only
      obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hcs
      have hdb_eq_fs : fsA.dirtyBuckets fsA.dirtyIdx = fs.dirtyBuckets fs.dirtyIdx := rfl
      rw [hdb_eq_fs]
      set bc := fs.dirtyBuckets fs.dirtyIdx
      have hbc : bc < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
      have hne_rl : 3 * bc + (3 - fs.liveRole bc - fs.overmarsRole bc) ≠ lIdx := by
        by_cases hbb : bc = b
        · rw [hbb]; dsimp only [lIdx, FastState.liveSliceIdx]; omega
        · exact hl_ne_other bc hbc hbb _
            (rebRole_props (hv.roles_valid bc hbc).1 (hv.roles_valid bc hbc).2.1
              (hv.roles_valid bc hbc).2.2).1
      have hsl_bc : fsA.slices (fsA.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) :=
        hsl_other hne_rl
      have hfp_bc : FastState.fpAt c U n_max θ fsA fs.rebCandSalt bc =
          fs.fpAt c U n_max θ fs.rebCandSalt bc := hfp_eq _ _
      have hrc_eq : fsA.rebScanCursor = fs.rebScanCursor := rfl
      have hri_eq : fsA.rebInsCount = fs.rebInsCount := rfl
      have hcs_eq : fsA.rebCandSalt = fs.rebCandSalt := rfl
      rw [hrc_eq, hri_eq, hcs_eq, hsl_bc, hfp_bc]
      -- The scanned prefix `min count cursor` is unchanged and lies below the new count.
      have hcnt_bc : fsA.bktCount bc ≤ fs.bktCount bc ∧ fs.rebScanCursor ≤ fsA.bktCount bc := by
        dsimp only [fsA, fastDeleteShrink, fs1_loc]
        by_cases hbb : bc = b
        · rw [hbb] at hcur_r ⊢; rw [Function.update_self]
          rcases hcur_r with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩ <;> omega
        · rw [Function.update_of_ne hbb]
          rcases hcur_r with ⟨hc0, _⟩ | ⟨_, hc_lt, _⟩ <;> omega
      have hpre : ∀ l < min (fs.bktCount bc) fs.rebScanCursor, l < fsA.bktCount bc :=
        fun l hl => by omega
      rw [show min (fsA.bktCount bc) fs.rebScanCursor = min (fs.bktCount bc) fs.rebScanCursor by
        omega]
      refine ⟨?_, ?_, rm, hvr, ?_⟩
      · rcases hcur_r with ⟨hc0, hi0⟩ | ⟨h16, _, hins⟩
        · exact Or.inl ⟨hc0, hi0⟩
        · exact Or.inr ⟨h16, hcnt_bc.2, by omega⟩
      · intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
        rw [hls_pres bc hbc l₁ (hpre l₁ hl₁)] at hp₁
        rw [hls_pres bc hbc l₂ (hpre l₂ hl₂)] at hp₂
        exact hinj_r l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
      · refine hrr.congr (fun _ _ => rfl) fun loc hlt => ?_
        rw [hls_pres bc hbc loc (hpre loc hlt)]

end Cslib.DataStructure.Dictionary.SuccinctWhp

end

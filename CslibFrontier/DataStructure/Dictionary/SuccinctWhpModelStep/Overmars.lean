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
import Mathlib.Tactic.NormNum

/-!
# Per-Bucket Shadow-Rebuild Step Preservation (`overmarsStep_spec`)

This module proves `overmarsStep_spec` for `SuccinctWhpModel`: advancing the per-bucket Overmars
shadow B+-tree scan by `16` coordinates (and swapping `liveRole` / `overmarsRole` upon completion)
restores `OvermarsBucketInv` on bucket `b` while preserving `CoreFastInv`, `OvermarsBucketInv` on
all other buckets, `ValidEpochStage`, and `ValidEpochStagePreTick`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.overmarsStep_spec`: background per-bucket shadow
  rebuild preserves `CoreFastInv`, `OvermarsBucketInv`, and `ValidEpochStage` /
  `ValidEpochStagePreTick`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient

private theorem ValidEpochStage.of_rebSlice_eq {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState}
    (h : ValidEpochStage c U n_max θ fs)
    (hq : fs'.quotArr = fs.quotArr) (hbp : fs'.backPtr = fs.backPtr)
    (hcnt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hep : fs'.curEp = fs.curEp) (hst : fs'.rebStage = fs.rebStage)
    (hsc : fs'.stageCursor = fs.stageCursor) (hdc : fs'.dirtyCount = fs.dirtyCount)
    (hdb : fs'.dirtyBuckets = fs.dirtyBuckets) (hdi : fs'.dirtyIdx = fs.dirtyIdx)
    (hdn : fs'.rebDoneFlag = fs.rebDoneFlag) (hrq : fs'.rebQueued = fs.rebQueued)
    (hcs : fs'.rebCandSalt = fs.rebCandSalt) (hrc : fs'.rebScanCursor = fs.rebScanCursor)
    (hri : fs'.rebInsCount = fs.rebInsCount) (hbuf : fs'.buf = fs.buf)
    (hsl : ∀ bc < numBucketsWhp n_max,
      fs'.slices (fs'.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc)) :
    ValidEpochStage c U n_max θ fs' := by
  have hold : fs'.oldEp = fs.oldEp := by dsimp only [FastState.oldEp]; rw [hep]
  dsimp only [ValidEpochStage] at h ⊢
  rw [hst, hold, hbuf, hsc, hdc, hdb, hdi, hdn, hrq, hcnt, hls, hcs, hrc, hri]
  split_ifs at h ⊢ with hs0 hs1 hs2 hs3
  · exact h
  · exact h
  · rcases h with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
    refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun hlt => ?_⟩
    obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hlt
    have hbc : fs.dirtyBuckets fs.dirtyIdx < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
    rw [fpAt_eq_of_fields hq hbp fs.rebCandSalt (fs.dirtyBuckets fs.dirtyIdx)]
    refine ⟨hcur_r, hinj_r, rm, ?_, hrr⟩
    rwa [hsl _ hbc]
  · exact h

private theorem ValidEpochStagePreTick.of_rebSlice_eq {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState}
    (h : ValidEpochStagePreTick c U n_max θ fs)
    (hq : fs'.quotArr = fs.quotArr) (hbp : fs'.backPtr = fs.backPtr)
    (hcnt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hep : fs'.curEp = fs.curEp) (hst : fs'.rebStage = fs.rebStage)
    (hsc : fs'.stageCursor = fs.stageCursor) (hdc : fs'.dirtyCount = fs.dirtyCount)
    (hdb : fs'.dirtyBuckets = fs.dirtyBuckets) (hdi : fs'.dirtyIdx = fs.dirtyIdx)
    (hdn : fs'.rebDoneFlag = fs.rebDoneFlag) (hrq : fs'.rebQueued = fs.rebQueued)
    (hcs : fs'.rebCandSalt = fs.rebCandSalt) (hrc : fs'.rebScanCursor = fs.rebScanCursor)
    (hri : fs'.rebInsCount = fs.rebInsCount) (hbuf : fs'.buf = fs.buf)
    (hsl : ∀ bc < numBucketsWhp n_max,
      fs'.slices (fs'.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc)) :
    ValidEpochStagePreTick c U n_max θ fs' := by
  have hold : fs'.oldEp = fs.oldEp := by dsimp only [FastState.oldEp]; rw [hep]
  dsimp only [ValidEpochStagePreTick] at h ⊢
  rw [hst, hold, hbuf, hsc, hdc, hdb, hdi, hdn, hrq, hcnt, hls, hcs, hrc, hri]
  split_ifs at h ⊢ with hs0 hs1 hs2 hs3
  · exact h
  · exact h
  · rcases h with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
    refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun hlt => ?_⟩
    obtain ⟨hcur_r, hinj_r, rm, hvr, hrr⟩ := hreb hlt
    have hbc : fs.dirtyBuckets fs.dirtyIdx < numBucketsWhp n_max := hd3 fs.dirtyIdx hd2
    rw [fpAt_eq_of_fields hq hbp fs.rebCandSalt (fs.dirtyBuckets fs.dirtyIdx)]
    refine ⟨hcur_r, hinj_r, rm, ?_, hrr⟩
    rwa [hsl _ hbc]
  · exact h

/-- Bounded-fuel invariant for `overmarsScanSteps` over `rem` coordinates of bucket `b`. -/
private theorem overmarsScanSteps_spec {c U n_max b : ℕ} (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) (rem : ℕ) (fs : FastState)
    (hcnt_le : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12)
    (hinj : ∀ l₁ < fs.bktCount b, ∀ l₂ < fs.bktCount b,
      inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₁) = true →
      inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b l₂) = true →
      fs.fpAt c U n_max θ (fs.bktSalt b) b l₁ = fs.fpAt c U n_max θ (fs.bktSalt b) b l₂ →
      l₁ = l₂)
    (hins_ub : fs.overmarsInsCount b + rem ≤ 8 * (slabScale n_max) ^ 12)
    (hom : ∃ omMap,
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (min (fs.bktCount b) (fs.overmarsCursor b)) omMap) :
    ∃ sl' cur' ins' omMap',
      overmarsScanSteps c U n_max θ b rem fs =
        { fs with
          slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl'
          overmarsCursor := Function.update fs.overmarsCursor b cur'
          overmarsInsCount := Function.update fs.overmarsInsCount b ins' } ∧
      cur' = fs.overmarsCursor b + rem ∧
      ins' ≤ fs.overmarsInsCount b + rem ∧
      ValidWhpSlice n_max ins' sl' omMap' ∧
      SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
        (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
        (min (fs.bktCount b) cur') omMap' := by
  induction rem generalizing fs with
  | zero =>
    obtain ⟨omMap, hv, hrel⟩ := hom
    refine ⟨fs.slices (fs.overmarsSliceIdx b), fs.overmarsCursor b, fs.overmarsInsCount b, omMap,
      ?_, by omega, by omega, hv, hrel⟩
    cases fs
    simp [overmarsScanSteps, Function.update_eq_self]
  | succ rem ih =>
    obtain ⟨omMap, hv, hrel⟩ := hom
    dsimp only [overmarsScanSteps]
    set cur := fs.overmarsCursor b
    set omIdx := fs.overmarsSliceIdx b
    by_cases hcond : cur < fs.bktCount b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) = true
    · rw [ite_eq_left hcond]
      obtain ⟨hcur_lt, hlive_cur⟩ := hcond
      have hmin_eq : min (fs.bktCount b) cur = cur := Nat.min_eq_right hcur_lt.le
      rw [hmin_eq] at hrel
      have hfp_lt : fs.fpAt c U n_max θ (fs.bktSalt b) b cur < 2 ^ fpBitsWhp n_max :=
        fpAt_lt θ fs (fs.bktSalt b) b cur
      have hval_lt : cur < 2 ^ valLaneBitsWhp n_max := by
        rw [two_pow_valLaneBitsWhp]; omega
      have hins1 := hv.insert_spec hth (by omega) hfp_lt hval_lt
      have hfresh : ∀ loc < cur,
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true →
          fs.fpAt c U n_max θ (fs.bktSalt b) b loc ≠
            fs.fpAt c U n_max θ (fs.bktSalt b) b cur :=
        fun loc hlt hpl heq =>
          Nat.ne_of_lt hlt (hinj loc (hlt.trans hcur_lt) cur hcur_lt hpl hlive_cur heq)
      have hrel1 := hrel.step_true hlive_cur hfresh
      have hmin1 : min (fs.bktCount b) (cur + 1) = cur + 1 :=
        Nat.min_eq_right (Nat.succ_le_of_lt hcur_lt)
      set sl1 := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices omIdx) (fs.fpAt c U n_max θ (fs.bktSalt b) b cur) cur
      let fs1 : FastState :=
        { fs with
          slices := Function.update fs.slices omIdx sl1
          overmarsCursor := Function.update fs.overmarsCursor b (cur + 1)
          overmarsInsCount := Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1) }
      have hfs1_om : ∃ omMap1,
          ValidWhpSlice n_max (fs1.overmarsInsCount b) (fs1.slices (fs1.overmarsSliceIdx b))
            omMap1 ∧
          SliceMapRel (fs1.fpAt c U n_max θ (fs1.bktSalt b) b)
            (fun loc =>
              inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) (fs1.locState b loc) = true)
            (min (fs1.bktCount b) (fs1.overmarsCursor b)) omMap1 := by
        refine ⟨Function.update omMap (fs.fpAt c U n_max θ (fs.bktSalt b) b cur) (some cur),
          ?_, ?_⟩
        · dsimp only [fs1, FastState.overmarsSliceIdx, omIdx]
          simpa only [Function.update_self] using hins1.2
        · rw [fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl,
            show fs1.oldEp = fs.oldEp from rfl]
          dsimp only [fs1]
          simpa only [Function.update_self, hmin1] using hrel1
      obtain ⟨sl', cur', ins', omMap', heq', hcur', hins', hv', hrel'⟩ :=
        ih fs1 hcnt_le hinj
          (by dsimp only [fs1]; rw [Function.update_self]; omega) hfs1_om
      rw [fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl,
        show fs1.oldEp = fs.oldEp from rfl] at hrel'
      dsimp only [fs1, FastState.overmarsSliceIdx] at heq' hcur' hins' hrel'
      rw [Function.update_self] at hcur' hins'
      refine ⟨sl', cur', ins', omMap', ?_, by omega, by omega, hv', hrel'⟩
      rw [heq']
      dsimp only [omIdx, FastState.overmarsSliceIdx]
      rw [Function.update_idem, Function.update_idem, Function.update_idem]
    · rw [ite_eq_right hcond]
      let fs1 : FastState :=
        { fs with overmarsCursor := Function.update fs.overmarsCursor b (cur + 1) }
      have hrel1 : SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
          (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
          (min (fs.bktCount b) (cur + 1)) omMap := by
        by_cases hcur_lt : cur < fs.bktCount b
        · have hnot_live : ¬(inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b)
              (fs.locState b cur) = true) := fun hl => hcond ⟨hcur_lt, hl⟩
          rw [Nat.min_eq_right hcur_lt.le] at hrel
          rw [Nat.min_eq_right (Nat.succ_le_of_lt hcur_lt)]
          exact hrel.step_false hnot_live
        · have hge : fs.bktCount b ≤ cur := Nat.not_lt.mp hcur_lt
          rw [Nat.min_eq_left hge] at hrel
          rw [Nat.min_eq_left (hge.trans (Nat.le_succ cur))]
          exact hrel
      have hfs1_om : ∃ omMap1,
          ValidWhpSlice n_max (fs1.overmarsInsCount b) (fs1.slices (fs1.overmarsSliceIdx b))
            omMap1 ∧
          SliceMapRel (fs1.fpAt c U n_max θ (fs1.bktSalt b) b)
            (fun loc =>
              inLiveTree fs1.rebStage fs1.oldEp (fs1.rebDoneFlag b) (fs1.locState b loc) = true)
            (min (fs1.bktCount b) (fs1.overmarsCursor b)) omMap1 := by
        refine ⟨omMap, hv, ?_⟩
        rw [fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl,
          show fs1.oldEp = fs.oldEp from rfl]
        dsimp only [fs1]
        simpa only [Function.update_self] using hrel1
      obtain ⟨sl', cur', ins', omMap', heq', hcur', hins', hv', hrel'⟩ :=
        ih fs1 hcnt_le hinj (by dsimp only [fs1]; omega) hfs1_om
      rw [fpAt_eq_of_fields (fs₁ := fs1) (fs₂ := fs) rfl rfl,
        show fs1.oldEp = fs.oldEp from rfl] at hrel'
      dsimp only [fs1, FastState.overmarsSliceIdx] at heq' hcur' hins' hrel'
      rw [Function.update_self] at hcur'
      refine ⟨sl', cur', ins', omMap', ?_, by omega, by omega, hv', hrel'⟩
      rw [heq']
      dsimp only [omIdx, FastState.overmarsSliceIdx]
      rw [Function.update_idem]

private theorem overmarsStep_post_scan {c U V n_max b cur1 ins1 : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    {sl1 : BTreeSlice} {omMap1 : ℕ → Option ℕ}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hom_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fs b')
    (hins_lt5 : ins1 < 5 * (slabScale n_max) ^ 12)
    (h16_cur : 16 ≤ cur1)
    (hlin_cur : 16 * (fs.liveInsCount b - 5 * (slabScale n_max) ^ 12) ≤ cur1)
    (hins_cur : 16 * ins1 + 16 ≤ 17 * cur1)
    (hv1 : ValidWhpSlice n_max ins1 sl1 omMap1)
    (hrel1 : SliceMapRel (fs.fpAt c U n_max θ (fs.bktSalt b) b)
      (fun loc => inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) = true)
      (min (fs.bktCount b) cur1) omMap1) :
    let fs1 : FastState :=
      { fs with
        overmarsActive := Function.update fs.overmarsActive b 1
        overmarsCursor := Function.update fs.overmarsCursor b cur1
        overmarsInsCount := Function.update fs.overmarsInsCount b ins1
        slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl1 }
    let fs' : FastState :=
      if fs1.bktCount b ≤ fs1.overmarsCursor b then
        { fs1 with
          liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
          overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
          liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
          overmarsActive := Function.update fs1.overmarsActive b 0
          overmarsCursor := Function.update fs1.overmarsCursor b 0
          overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
      else fs1
    CoreFastInv c U V n_max θ fs' dict ∧
    (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b') ∧
    (ValidEpochStage c U n_max θ fs → ValidEpochStage c U n_max θ fs') ∧
    (ValidEpochStagePreTick c U n_max θ fs → ValidEpochStagePreTick c U n_max θ fs') ∧
    fs'.curEp = fs.curEp ∧
    fs'.epochClock = fs.epochClock ∧
    fs'.rebStage = fs.rebStage ∧
    fs'.buf = fs.buf := by
  obtain ⟨hlr_lt, hor_lt, hro_ne⟩ := hc.roles_valid b hb
  dsimp only
  set fs1 : FastState :=
    { fs with
      overmarsActive := Function.update fs.overmarsActive b 1
      overmarsCursor := Function.update fs.overmarsCursor b cur1
      overmarsInsCount := Function.update fs.overmarsInsCount b ins1
      slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl1 }
  have hne_lo : fs.overmarsSliceIdx b ≠ fs.liveSliceIdx b := by
    dsimp only [FastState.overmarsSliceIdx, FastState.liveSliceIdx]; omega
  have hne_reb_all : ∀ b' < numBucketsWhp n_max, fs.overmarsSliceIdx b ≠ fs.rebSliceIdx b' := by
    intro b' hb'
    obtain ⟨hlr', hor', hne'⟩ := hc.roles_valid b' hb'
    dsimp only [FastState.overmarsSliceIdx, FastState.rebSliceIdx, FastState.rebRole]
    by_cases hbb : b' = b
    · subst hbb; omega
    · intro heq
      have hrr : 3 - fs.liveRole b' - fs.overmarsRole b' < 3 := by omega
      exact hbb (sliceIdx_inj hor_lt hrr heq).1.symm
  have hne_other : ∀ b' < numBucketsWhp n_max, b' ≠ b →
      3 * b' + fs.liveRole b' ≠ fs.overmarsSliceIdx b ∧
        3 * b' + fs.overmarsRole b' ≠ 3 * b + fs.overmarsRole b := by
    intro b' hb' hbb
    dsimp only [FastState.overmarsSliceIdx]
    exact ⟨fun heq => hbb (sliceIdx_inj (hc.roles_valid b' hb').1 hor_lt heq).1,
      fun heq => hbb (sliceIdx_inj (hc.roles_valid b' hb').2.1 hor_lt heq).1⟩
  by_cases hdone : fs1.bktCount b ≤ fs1.overmarsCursor b
  · rw [ite_eq_left hdone]
    dsimp only [fs1] at hdone
    rw [Function.update_self] at hdone
    rw [Nat.min_eq_left hdone] at hrel1
    set fsSwap : FastState :=
      { fs1 with
        liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
        overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
        liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
        overmarsActive := Function.update fs1.overmarsActive b 0
        overmarsCursor := Function.update fs1.overmarsCursor b 0
        overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
    have hreb_eq : ∀ bc < numBucketsWhp n_max,
        fsSwap.slices (fsSwap.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
      intro bc hbc
      have hridx_eq : fsSwap.rebSliceIdx bc = fs.rebSliceIdx bc := by
        dsimp only [FastState.rebSliceIdx, FastState.rebRole, fsSwap, fs1]
        by_cases hbb : bc = b
        · subst hbb; simp only [Function.update_self]; omega
        · simp [hbb]
      rw [hridx_eq]
      dsimp only [fsSwap, fs1]
      exact Function.update_of_ne (hne_reb_all bc hbc).symm _ _
    refine ⟨?_, ?_,
      fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl hreb_eq,
      fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl hreb_eq,
      rfl, rfl, rfl, rfl⟩
    · refine { hc with
        roles_valid := fun b' hb' => by
          by_cases hbb : b' = b
          · subst hbb; dsimp only [fsSwap, fs1]; simp [hor_lt, hlr_lt, Ne.symm hro_ne]
          · dsimp only [fsSwap, fs1]; simp [hbb, hc.roles_valid b' hb']
        live_valid := fun b' hb' => by
          by_cases hbb : b' = b
          · subst hbb
            refine ⟨omMap1, ?_, hrel1⟩
            dsimp only [FastState.liveSliceIdx, fsSwap, fs1, FastState.overmarsSliceIdx]
            simp only [Function.update_self]
            exact hv1
          · obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b' hb'
            refine ⟨lm, ?_, hrl⟩
            dsimp only [FastState.liveSliceIdx, fsSwap, fs1]
            simp only [Function.update_of_ne hbb, Function.update_of_ne (hne_other b' hb' hbb).1]
            exact hvl }
    · intro b' hb'
      by_cases hbb : b' = b
      · subst hbb
        left
        dsimp only [fsSwap, fs1]
        simp only [Function.update_self]
        exact ⟨trivial, hins_lt5⟩
      · refine (hom_other b' hb' hbb).of_eq_on (fpAt_eq_of_fields rfl rfl _ _) rfl rfl rfl rfl
          rfl ?_ ?_ ?_ ?_ ?_ <;> dsimp only [FastState.overmarsSliceIdx, fsSwap, fs1] <;>
          simp only [Function.update_of_ne hbb, Function.update_of_ne (hne_other b' hb' hbb).2]
  · rw [ite_eq_right hdone]
    dsimp only [fs1] at hdone
    rw [Function.update_self] at hdone
    have hcur_lt_b : cur1 < fs.bktCount b := Nat.lt_of_not_le hdone
    rw [Nat.min_eq_right hcur_lt_b.le] at hrel1
    have hreb_eq : ∀ bc < numBucketsWhp n_max,
        fs1.slices (fs1.rebSliceIdx bc) = fs.slices (fs.rebSliceIdx bc) := by
      intro bc hbc
      dsimp only [fs1, FastState.rebSliceIdx, FastState.rebRole]
      exact Function.update_of_ne (hne_reb_all bc hbc).symm _ _
    refine ⟨?_, ?_,
      fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl hreb_eq,
      fun hst => hst.of_rebSlice_eq rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl hreb_eq,
      rfl, rfl, rfl, rfl⟩
    · refine { hc with
        live_valid := fun b' hb' => by
          obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b' hb'
          refine ⟨lm, ?_, hrl⟩
          have hne_s : fs.liveSliceIdx b' ≠ fs.overmarsSliceIdx b := by
            by_cases hbb : b' = b
            · subst hbb; exact hne_lo.symm
            · exact (hne_other b' hb' hbb).1
          dsimp only [fs1, FastState.liveSliceIdx] at hne_s ⊢
          rwa [Function.update_of_ne hne_s] }
    · intro b' hb'
      by_cases hbb : b' = b
      · subst hbb
        right
        dsimp only [fs1, FastState.overmarsSliceIdx]
        simp only [Function.update_self]
        exact ⟨trivial, h16_cur, hcur_lt_b, hlin_cur, hins_cur, omMap1, hv1, hrel1⟩
      · refine (hom_other b' hb' hbb).of_eq_on (fpAt_eq_of_fields rfl rfl _ _) rfl rfl rfl rfl
          rfl rfl ?_ ?_ ?_ ?_ <;> dsimp only [FastState.overmarsSliceIdx, fs1] <;>
          simp only [Function.update_of_ne hbb, Function.update_of_ne (hne_other b' hb' hbb).2]

/-- `overmarsStep` on bucket `b < numBucketsWhp n_max` restores `OvermarsBucketInv` on `b` while
preserving `CoreFastInv`, `OvermarsBucketInv` on all `b' ≠ b`, `ValidEpochStage`, and
`ValidEpochStagePreTick`. -/
theorem overmarsStep_spec {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hom_other : ∀ b' < numBucketsWhp n_max, b' ≠ b → OvermarsBucketInv c U n_max θ fs b')
    (hom_b : PreOvermarsBucketInv c U n_max θ fs b) :
    let fs' := overmarsStep c U n_max θ b fs
    CoreFastInv c U V n_max θ fs' dict ∧
    (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b') ∧
    (ValidEpochStage c U n_max θ fs → ValidEpochStage c U n_max θ fs') ∧
    (ValidEpochStagePreTick c U n_max θ fs → ValidEpochStagePreTick c U n_max θ fs') ∧
    fs'.curEp = fs.curEp ∧
    fs'.epochClock = fs.epochClock ∧
    fs'.rebStage = fs.rebStage ∧
    fs'.buf = fs.buf := by
  have hL2 : 2 ≤ slabScale n_max := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  unfold overmarsStep overmarsAfterActivate
  dsimp only
  rcases hom_b with ⟨ha0, hlic_le⟩ | ⟨ha1, h16, hcur_le, hlin, hins_le, omMap0, hv0, hrel0⟩
  · by_cases htrig : 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b
    · have hcond0 : fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b :=
        ⟨ha0, htrig⟩
      rw [ite_eq_left hcond0]
      set fs0 : FastState :=
        { fs with
          overmarsActive := Function.update fs.overmarsActive b 1
          overmarsCursor := Function.update fs.overmarsCursor b 0
          overmarsInsCount := Function.update fs.overmarsInsCount b 0
          slices := Function.update fs.slices (fs.overmarsSliceIdx b)
            (resetBTreeSlice (fs.slices (fs.overmarsSliceIdx b))) }
      have ha0_1 : fs0.overmarsActive b = 1 := by dsimp only [fs0]; simp
      rw [ite_eq_left ha0_1]
      have hom0 : ∃ omMap,
          ValidWhpSlice n_max (fs0.overmarsInsCount b) (fs0.slices (fs0.overmarsSliceIdx b))
            omMap ∧
          SliceMapRel (fs0.fpAt c U n_max θ (fs0.bktSalt b) b)
            (fun loc =>
              inLiveTree fs0.rebStage fs0.oldEp (fs0.rebDoneFlag b) (fs0.locState b loc) = true)
            (min (fs0.bktCount b) (fs0.overmarsCursor b)) omMap := by
        refine ⟨fun _ => none, ?_, ?_⟩
        · dsimp only [fs0, FastState.overmarsSliceIdx]
          rw [Function.update_self, Function.update_self]
          exact validWhpSlice_zero _ 0 _
        · dsimp only [fs0]
          rw [Function.update_self, Nat.min_zero]
          exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)
      obtain ⟨sl1, cur1, ins1, omMap1, hscan_eq, hcur1, hins1, hv1, hrel1⟩ :=
        overmarsScanSteps_spec hc.hth θ 16 fs0 hcnt_3L (hc.live_fp_inj b hb)
          (by dsimp only [fs0]; rw [Function.update_self]; omega) hom0
      rw [hscan_eq]
      have hfp0 : fs0.fpAt c U n_max θ (fs0.bktSalt b) b =
          fs.fpAt c U n_max θ (fs.bktSalt b) b := fpAt_eq_of_fields rfl rfl _ _
      have hold0 : fs0.oldEp = fs.oldEp := rfl
      rw [hfp0, hold0] at hrel1
      dsimp only [fs0] at hcur1 hins1 hrel1
      rw [Function.update_self] at hcur1 hins1
      have hfs1_eq :
          ({ fs0 with
              slices := Function.update fs0.slices (fs0.overmarsSliceIdx b) sl1
              overmarsCursor := Function.update fs0.overmarsCursor b cur1
              overmarsInsCount := Function.update fs0.overmarsInsCount b ins1 } : FastState) =
            { fs with
              overmarsActive := Function.update fs.overmarsActive b 1
              overmarsCursor := Function.update fs.overmarsCursor b cur1
              overmarsInsCount := Function.update fs.overmarsInsCount b ins1
              slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl1 } := by
        dsimp only [fs0, FastState.overmarsSliceIdx]
        rw [Function.update_idem, Function.update_idem, Function.update_idem]
      rw [hfs1_eq]
      exact overmarsStep_post_scan hc hb hom_other (by omega) (by omega) (by omega) (by omega)
        hv1 hrel1
    · have hncond0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b) :=
        fun ⟨_, h⟩ => htrig h
      rw [ite_eq_right hncond0, ite_eq_right (by omega : ¬(fs.overmarsActive b = 1))]
      refine ⟨hc, fun b' hb' => ?_, id, id, rfl, rfl, rfl, rfl⟩
      by_cases hbb : b' = b
      · subst hbb; exact Or.inl ⟨ha0, Nat.lt_of_not_le htrig⟩
      · exact hom_other b' hb' hbb
  · have hncond0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b) :=
      by omega
    rw [ite_eq_right hncond0, ite_eq_left ha1]
    have hins_ub : fs.overmarsInsCount b + 16 ≤ 8 * (slabScale n_max) ^ 12 := by omega
    obtain ⟨sl1, cur1, ins1, omMap1, hscan_eq, hcur1, hins1, hv1, hrel1⟩ :=
      overmarsScanSteps_spec hc.hth θ 16 fs hcnt_3L (hc.live_fp_inj b hb) hins_ub
        ⟨omMap0, hv0, hrel0⟩
    rw [hscan_eq]
    have hfs1_eq :
        ({ fs with
            slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl1
            overmarsCursor := Function.update fs.overmarsCursor b cur1
            overmarsInsCount := Function.update fs.overmarsInsCount b ins1 } : FastState) =
          { fs with
            overmarsActive := Function.update fs.overmarsActive b 1
            overmarsCursor := Function.update fs.overmarsCursor b cur1
            overmarsInsCount := Function.update fs.overmarsInsCount b ins1
            slices := Function.update fs.slices (fs.overmarsSliceIdx b) sl1 } := by
      have hact : Function.update fs.overmarsActive b 1 = fs.overmarsActive :=
        Function.update_eq_self_iff.mpr ha1.symm
      rw [hact]
    rw [hfs1_eq]
    exact overmarsStep_post_scan hc hb hom_other (by omega) (by omega) (by omega) (by omega)
      hv1 hrel1

end Cslib.DataStructure.Dictionary.SuccinctWhp

end

/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
-- `import all`: reads private invariant-transfer helper `step_of_inLiveTree_eq` from `Common`.
import all CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Common
import Mathlib.Tactic.Linarith

/-!
# Epoch Rebuild Stage 2 (Candidate-Salt Scanning and Live-Slice Swap)

Internal correctness proofs for `rebScanSteps` and `epochTickStage2`
[BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.epochTickStage2_spec`: Stage 2 preserves
  `CoreFastInv` and `OvermarsBucketInv` and restores `ValidEpochStage`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-- Specification of `rebScanSteps c U n_max θ b rem fs` starting from `fs.rebCollision = 0`. -/
private theorem rebScanSteps_spec {c U n_max b : ℕ} (hth : whpThreshold c ≤ n_max)
    (θ : SeedWhp c U n_max) (rem : ℕ) (fs : FastState)
    (hcoll0 : fs.rebCollision = 0)
    (hcnt_le : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12)
    (hins_ub : fs.rebInsCount + rem ≤ 8 * (slabScale n_max) ^ 12)
    (hinj0 : ∀ l₁ < min (fs.bktCount b) fs.rebScanCursor,
      ∀ l₂ < min (fs.bktCount b) fs.rebScanCursor,
        (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
        (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
        fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
        l₁ = l₂)
    (hreb0 : ∃ rebMap,
      ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rebMap ∧
      SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) fs.rebScanCursor) rebMap) :
    (∃ sl' cur' ins',
      rebScanSteps c U n_max θ b rem fs =
        { fs with
          slices := Function.update fs.slices (fs.rebSliceIdx b) sl'
          rebScanCursor := cur'
          rebInsCount := ins'
          rebCollision := 1 }) ∨
    (∃ sl' ins' rebMap',
      rebScanSteps c U n_max θ b rem fs =
        { fs with
          slices := Function.update fs.slices (fs.rebSliceIdx b) sl'
          rebScanCursor := fs.rebScanCursor + rem
          rebInsCount := ins' } ∧
      ins' ≤ fs.rebInsCount + rem ∧
      (∀ l₁ < min (fs.bktCount b) (fs.rebScanCursor + rem),
       ∀ l₂ < min (fs.bktCount b) (fs.rebScanCursor + rem),
        (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
        (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
        fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
        l₁ = l₂) ∧
      ValidWhpSlice n_max ins' sl' rebMap' ∧
      SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
        (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
        (min (fs.bktCount b) (fs.rebScanCursor + rem)) rebMap') := by
  induction rem generalizing fs with
  | zero =>
    obtain ⟨rm, hvr, hrr⟩ := hreb0
    right
    refine ⟨fs.slices (fs.rebSliceIdx b), fs.rebInsCount, rm, ?_, le_rfl, ?_, hvr, ?_⟩
    · dsimp only [rebScanSteps]; simp
    · simpa using hinj0
    · simpa using hrr
  | succ rem ih =>
    obtain ⟨rm0, hvr0, hrr0⟩ := hreb0
    dsimp only [rebScanSteps]
    rw [ite_eq_right (by omega : ¬(fs.rebCollision ≠ 0))]
    set cur := fs.rebScanCursor
    set rIdx := fs.rebSliceIdx b
    by_cases hact : cur < fs.bktCount b ∧ (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)
    · rw [ite_eq_left hact]
      set fp := fs.fpAt c U n_max θ fs.rebCandSalt b cur
      have hfp_lt : fp < 2 ^ fpBitsWhp n_max := fpAt_lt θ fs _ b cur
      have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
        rw [two_pow_valLaneBitsWhp n_max]; omega
      cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp with
      | some _ =>
        dsimp only
        have hstop : ∀ r (s : FastState), s.rebCollision ≠ 0 →
            rebScanSteps c U n_max θ b r s = s := by
          intro r s hs; cases r with
          | zero => rfl
          | succ r' => dsimp only [rebScanSteps]; exact ite_eq_left hs
        rw [hstop rem { fs with rebCollision := 1 } (show (1 : ℕ) ≠ 0 by decide)]
        left
        refine ⟨fs.slices rIdx, cur, fs.rebInsCount, ?_⟩
        dsimp only [cur, rIdx]
        rw [Function.update_eq_self]
      | none =>
        dsimp only
        have hrm0_none : rm0 fp = none :=
          (hvr0.lookup_eq hth (by omega) hfp_lt).symm.trans hlk
        have hmin0 : min (fs.bktCount b) cur = cur := Nat.min_eq_right hact.1.le
        have hmin1 : min (fs.bktCount b) (cur + 1) = cur + 1 :=
          Nat.min_eq_right (Nat.succ_le_of_lt hact.1)
        rw [hmin0] at hrr0 hinj0
        have hno_coll : ∀ loc < cur,
            (fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp) →
            fs.fpAt c U n_max θ fs.rebCandSalt b loc ≠ fp :=
          (hrr0.1 fp).mp hrm0_none
        set sl1 := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices rIdx) fp cur
        have hv1 := (hvr0.insert_spec hth (by omega) hfp_lt hcur_val).2
        have hr1 := hrr0.step_true hact.2 hno_coll
        have hinj1 : ∀ l₁ < cur + 1, ∀ l₂ < cur + 1,
            (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
            (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
            fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
            l₁ = l₂ := by
          intro l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl₁ with hl1' | rfl <;>
            rcases Nat.lt_succ_iff_lt_or_eq.mp hl₂ with hl2' | rfl
          · exact hinj0 l₁ hl1' l₂ hl2' hp₁ hp₂ hfeq
          · exact absurd hfeq (hno_coll l₁ hl1' hp₁)
          · exact absurd hfeq.symm (hno_coll l₂ hl2' hp₂)
          · rfl
        set fs1 : FastState :=
          { fs with
            slices := Function.update fs.slices rIdx sl1
            rebScanCursor := cur + 1
            rebInsCount := fs.rebInsCount + 1 }
        have hfp1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b =
            fs.fpAt c U n_max θ fs.rebCandSalt b := fpAt_eq_of_fields rfl rfl _ _
        have hr1_idx : fs1.rebSliceIdx b = rIdx := rfl
        rcases ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega)
          (by dsimp only [fs1]; rw [hfp1, hmin1]; exact hinj1)
          ⟨Function.update rm0 fp (some cur),
            by rw [hr1_idx]; dsimp only [fs1]; rw [Function.update_self]; exact hv1,
            by dsimp only [fs1]; rw [hfp1, hmin1]; exact hr1⟩ with
          ⟨sl', cur', ins', heq⟩ | ⟨sl', ins', rm', heq, hins', hinj', hv', hr'⟩
        · left
          refine ⟨sl', cur', ins', ?_⟩
          rw [heq, hr1_idx]; dsimp only [fs1]; rw [Function.update_idem]
        · right
          dsimp only [fs1] at hins' hinj' hr'
          rw [hfp1] at hinj' hr'
          have hadd : cur + 1 + rem = cur + (rem + 1) := by omega
          rw [hadd] at hinj' hr'
          refine ⟨sl', ins', rm', ?_, by omega, hinj', hv', hr'⟩
          rw [heq, hr1_idx]; dsimp only [fs1]
          rw [Function.update_idem, hadd]
    · rw [ite_eq_right hact]
      set fs1 : FastState := { fs with rebScanCursor := cur + 1 }
      have hfp1 : fs1.fpAt c U n_max θ fs1.rebCandSalt b =
          fs.fpAt c U n_max θ fs.rebCandSalt b := fpAt_eq_of_fields rfl rfl _ _
      have hr1_idx : fs1.rebSliceIdx b = rIdx := rfl
      have hstep_min :
          (∀ l₁ < min (fs.bktCount b) (cur + 1), ∀ l₂ < min (fs.bktCount b) (cur + 1),
            (fs.locState b l₁ = 1 ∨ fs.locState b l₁ = 2 + fs.oldEp) →
            (fs.locState b l₂ = 1 ∨ fs.locState b l₂ = 2 + fs.oldEp) →
            fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fs.fpAt c U n_max θ fs.rebCandSalt b l₂ →
            l₁ = l₂) ∧
          SliceMapRel (fs.fpAt c U n_max θ fs.rebCandSalt b)
            (fun loc => fs.locState b loc = 1 ∨ fs.locState b loc = 2 + fs.oldEp)
            (min (fs.bktCount b) (cur + 1)) rm0 := by
        by_cases hlt_b : cur < fs.bktCount b
        · have hnp : ¬(fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp) :=
            fun hp => hact ⟨hlt_b, hp⟩
          have hm0 : min (fs.bktCount b) cur = cur := Nat.min_eq_right hlt_b.le
          have hm1 : min (fs.bktCount b) (cur + 1) = cur + 1 :=
            Nat.min_eq_right (Nat.succ_le_of_lt hlt_b)
          rw [hm0] at hinj0 hrr0; rw [hm1]
          refine ⟨fun l₁ hl₁ l₂ hl₂ hp₁ hp₂ hfeq => ?_, hrr0.step_false hnp⟩
          have hl1' : l₁ < cur := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl₁)
            (fun h => hnp (h ▸ hp₁))
          have hl2' : l₂ < cur := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl₂)
            (fun h => hnp (h ▸ hp₂))
          exact hinj0 l₁ hl1' l₂ hl2' hp₁ hp₂ hfeq
        · have hm0 : min (fs.bktCount b) cur = fs.bktCount b := Nat.min_eq_left (by omega)
          have hm1 : min (fs.bktCount b) (cur + 1) = fs.bktCount b := Nat.min_eq_left (by omega)
          rw [hm0] at hinj0 hrr0; rw [hm1]
          exact ⟨hinj0, hrr0⟩
      rcases ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega)
        (by dsimp only [fs1]; rw [hfp1]; exact hstep_min.1)
        ⟨rm0, hvr0, by dsimp only [fs1]; rw [hfp1]; exact hstep_min.2⟩ with
        ⟨sl', cur', ins', heq⟩ | ⟨sl', ins', rm', heq, hins', hinj', hv', hr'⟩
      · left; rw [heq, hr1_idx]; exact ⟨sl', cur', ins', rfl⟩
      · right
        dsimp only [fs1] at hins' hinj' hr'
        rw [hfp1] at hinj' hr'
        have hadd : cur + 1 + rem = cur + (rem + 1) := by omega
        rw [hadd] at hinj' hr'
        refine ⟨sl', ins', rm', ?_, by omega, hinj', hv', hr'⟩
        rw [heq, hr1_idx]; dsimp only [fs1, cur, rIdx]; rw [hadd]


/-- Slice indices `3 * b' + r'` and `3 * b + r` with roles `< 3` differ unless the buckets and the
roles both agree. -/
private theorem sliceIdx_ne {b b' r r' : ℕ} (hr' : r' < 3) (hr : r < 3)
    (hne : b' = b → r' ≠ r) : 3 * b' + r' ≠ 3 * b + r := fun heq =>
  hne (sliceIdx_inj hr' hr heq).1 (sliceIdx_inj hr' hr heq).2

/-- Stage-2 tick scans 16 coordinates under `rebCandSalt` and swaps collision-free slices. -/
theorem epochTickStage2_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs2 : fs.rebStage = 2)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage2 c U n_max θ fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  have hL2 : 2 ≤ slabScale n_max := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
    ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2] at hpre
  rcases hpre with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  unfold epochTickStage2 epochTickStage2PostScan; dsimp only
  rw [ite_eq_left hd2]
  set b := fs.dirtyBuckets fs.dirtyIdx
  have hb : b < numBucketsWhp n_max := hd3 _ hd2
  obtain ⟨hlr_b, hor_b, hne_b⟩ := hc.roles_valid b hb
  have hrr_b : fs.rebRole b < 3 ∧ fs.rebRole b ≠ fs.liveRole b ∧
      fs.rebRole b ≠ fs.overmarsRole b := by
    dsimp only [FastState.rebRole]; omega
  set rIdx := fs.rebSliceIdx b
  have hne_live_r : ∀ b' < numBucketsWhp n_max, fs.liveSliceIdx b' ≠ rIdx := fun b' hb' =>
    sliceIdx_ne (hc.roles_valid b' hb').1 hrr_b.1 fun h => h ▸ hrr_b.2.1.symm
  have hne_om_r : ∀ b' < numBucketsWhp n_max, fs.overmarsSliceIdx b' ≠ rIdx := fun b' hb' =>
    sliceIdx_ne (hc.roles_valid b' hb').2.1 hrr_b.1 fun h => h ▸ hrr_b.2.2.symm
  by_cases hcs_lt : fs.rebCandSalt < sMaxWhp c n_max
  · rw [ite_eq_left hcs_lt]
    obtain ⟨hcur_r, hinj_r, rm0, hvr0, hrr0⟩ := hreb hcs_lt
    have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
      (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
    have hins_ub : fs.rebInsCount + 16 ≤ 8 * (slabScale n_max) ^ 12 := by
      rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hc_le, hins_le⟩ <;> omega
    rcases rebScanSteps_spec hc.hth θ 16 fs hc.rebCollision_zero hcnt_3L hins_ub hinj_r
      ⟨rm0, hvr0, hrr0⟩ with
      ⟨sl_c, cur_c, ins_c, hscan_c⟩ | ⟨sl', ins', rm', hscan_ok, hins_le', hinj', hv', hrr'⟩
    · -- Fingerprint collision detected during the 16-step scan: reset `rIdx` and bump `rebCandSalt`
      rw [hscan_c]
      dsimp only
      rw [ite_eq_left (by decide)]
      have hreset_ne : ∀ i ≠ rIdx, Function.update (Function.update fs.slices rIdx sl_c) rIdx
          (resetBTreeSlice (Function.update fs.slices rIdx sl_c rIdx)) i = fs.slices i :=
        fun i hi => by rw [Function.update_idem]; exact Function.update_of_ne hi _ _
      refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
        hc.rebStage_le rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun b' hb' => hreset_ne _ (hne_live_r b' hb'))
        (fun b' hb' => hreset_ne _ (hne_om_r b' hb'))
        (fun _ _ _ _ => rfl)
        (by dsimp only [FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]; exact hbo)
        ?_ rfl
      dsimp only [ValidEpochStage]
      rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
        ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2]
      refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun _ => ⟨Or.inl ⟨rfl, rfl⟩,
        fun _ hl => absurd (hl.trans_le (Nat.min_le_right _ _)) (Nat.not_lt_zero _),
        fun _ => none, ?_,
        by
          rw [Nat.min_zero]
          exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
      change ValidWhpSlice n_max 0
        (Function.update (Function.update fs.slices rIdx sl_c) rIdx
          (resetBTreeSlice (Function.update fs.slices rIdx sl_c rIdx)) rIdx) (fun _ => none)
      rw [Function.update_idem, Function.update_self, Function.update_self]
      exact validWhpSlice_zero _ 0 _
    · -- Clean 16-step scan (`rebCollision = 0`)
      rw [hscan_ok]
      dsimp only
      have hc0_scan : ¬(({ fs with
          slices := Function.update fs.slices rIdx sl'
          rebScanCursor := fs.rebScanCursor + 16
          rebInsCount := ins' } : FastState).rebCollision ≠ 0) :=
        fun h => h hc.rebCollision_zero
      rw [ite_eq_right hc0_scan]
      by_cases hdone_b : fs.bktCount b ≤ fs.rebScanCursor + 16
      · -- Bucket `b` finished scanning: swap `rebRole b` into `liveRole b` and advance `dirtyIdx`
        rw [ite_eq_left hdone_b]
        have hmin_full : min (fs.bktCount b) (fs.rebScanCursor + 16) = fs.bktCount b :=
          Nat.min_eq_left hdone_b
        rw [hmin_full] at hinj' hrr'
        have hins'_lt5 : ins' < 5 * (slabScale n_max) ^ 12 := by
          rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hc_le, hins_le⟩ <;> omega
        set fsScan : FastState :=
          { fs with
            slices := Function.update fs.slices rIdx sl'
            rebScanCursor := fs.rebScanCursor + 16
            rebInsCount := ins' }
        set fsSw : FastState := epochTickStage2Swap b fsScan
        have hinL_sw_b : ∀ st, (inLiveTree 2 fs.oldEp 1 st = true) ↔
            (st = 1 ∨ st = 2 + fs.oldEp) := by
          intro st; simp [inLiveTree]
        have hst_sw : fsSw.rebStage = 2 := hs2
        have hold_sw : fsSw.oldEp = fs.oldEp := rfl
        have hls_sw : fsSw.locState = fs.locState := rfl
        have hfp_sw : ∀ s, fsSw.fpAt c U n_max θ s = fs.fpAt c U n_max θ s :=
          fun s => by funext b0; exact fpAt_eq_of_fields rfl rfl s b0
        have hsw_b : fsSw.rebDoneFlag b = 1 ∧ fsSw.bktSalt b = fs.rebCandSalt ∧
            fsSw.liveInsCount b = ins' := by
          dsimp only [fsSw, epochTickStage2Swap, fsScan]; simp
        have hsw_o : ∀ b' ≠ b, fsSw.rebDoneFlag b' = fs.rebDoneFlag b' ∧
            fsSw.bktSalt b' = fs.bktSalt b' ∧ fsSw.liveInsCount b' = fs.liveInsCount b' :=
          fun b' hbb => by
            dsimp only [fsSw, epochTickStage2Swap, fsScan]
            exact ⟨Function.update_of_ne hbb _ _, Function.update_of_ne hbb _ _,
              Function.update_of_ne hbb _ _⟩
        have hSw_core : CoreFastInv c U V n_max θ fsSw dict :=
          { hth := hc.hth
            curEp_or := hc.curEp_or
            epochClock_lt := hc.epochClock_lt
            rebStage_le := hc.rebStage_le
            rebCollision_zero := rfl
            qv_global := hc.qv_global
            bktCount_le := hc.bktCount_le
            bktCount_ge_zero := hc.bktCount_ge_zero
            locState_active := hc.locState_active
            locState_inactive := hc.locState_inactive
            active_item := hc.active_item
            quot_inj := hc.quot_inj
            dict_map := hc.dict_map
            poolFreeTop_le := hc.poolFreeTop_le
            backPtr_valid := hc.backPtr_valid
            freeStack_lt := hc.freeStack_lt
            backPtr_inj := hc.backPtr_inj
            freeStack_inj := hc.freeStack_inj
            back_free_disj := hc.back_free_disj
            pool_conservation := hc.pool_conservation
            roles_valid := fun b' hb' => by
              dsimp only [fsSw, epochTickStage2Swap, fsScan]
              by_cases hbb : b' = b
              · subst hbb
                rw [Function.update_self]
                exact ⟨hrr_b.1, hor_b, hrr_b.2.2⟩
              · rw [Function.update_of_ne hbb]
                exact hc.roles_valid b' hb'
            bktSalt_lt := fun b' hb' => by
              dsimp only [fsSw, epochTickStage2Swap, fsScan]
              by_cases hbb : b' = b
              · subst hbb; simp [hcs_lt]
              · simp [hbb, hc.bktSalt_lt b' hb']
            live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
              rw [hst_sw, hold_sw, hls_sw] at hin₁ hin₂
              rw [hfp_sw] at hfeq
              by_cases hbb : b' = b
              · subst hbb
                rw [hsw_b.1] at hin₁ hin₂
                rw [hsw_b.2.1] at hfeq
                exact hinj' l₁ hl₁ l₂ hl₂ ((hinL_sw_b _).mp hin₁) ((hinL_sw_b _).mp hin₂) hfeq
              · rw [(hsw_o b' hbb).1, ← hs2] at hin₁ hin₂; rw [(hsw_o b' hbb).2.1] at hfeq
                exact hc.live_fp_inj b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
            live_valid := fun b' hb' => by
              have hbkt_eq : fsSw.bktCount = fs.bktCount := rfl
              rw [hst_sw, hold_sw, hls_sw, hbkt_eq, hfp_sw]
              by_cases hbb : b' = b
              · subst hbb
                have hl_idx : fsSw.liveSliceIdx b = rIdx := by
                  change 3 * b + Function.update fs.liveRole b (fs.rebRole b) b =
                    3 * b + fs.rebRole b
                  rw [Function.update_self]
                have hsl_b : fsSw.slices (fsSw.liveSliceIdx b) = sl' := by
                  rw [hl_idx]
                  change Function.update (Function.update fs.slices rIdx sl')
                    (fs.overmarsSliceIdx b) _ rIdx = sl'
                  rw [Function.update_of_ne (hne_om_r b hb).symm, Function.update_self]
                rw [hsw_b.1, hsw_b.2.1, hsw_b.2.2, hsl_b]
                exact ⟨rm', hv', hrr'.congr (fun _ _ => rfl)
                  (fun loc _ => hinL_sw_b (fs.locState b loc))⟩
              · have hl_idx : fsSw.liveSliceIdx b' = fs.liveSliceIdx b' := by
                  dsimp only [fsSw, epochTickStage2Swap, fsScan, FastState.liveSliceIdx]
                  rw [Function.update_of_ne hbb]
                have hsl_o :
                    fsSw.slices (fsSw.liveSliceIdx b') = fs.slices (fs.liveSliceIdx b') := by
                  rw [hl_idx]
                  change Function.update (Function.update fs.slices rIdx sl')
                    (fs.overmarsSliceIdx b) _ (fs.liveSliceIdx b') = _
                  have hne_om_b : fs.liveSliceIdx b' ≠ fs.overmarsSliceIdx b :=
                    sliceIdx_ne (hc.roles_valid b' hb').1 hor_b fun h => absurd h hbb
                  rw [Function.update_of_ne hne_om_b, Function.update_of_ne (hne_live_r b' hb')]
                obtain ⟨hdf_o, hbs_o, hlic_o⟩ := hsw_o b' hbb
                rw [hdf_o, hbs_o, hlic_o, hsl_o, ← hs2]
                exact hc.live_valid b' hb'
            rKey_buf_inj := hc.rKey_buf_inj
            bufCur_valid := hc.bufCur_valid
            bufOld_valid := by
              have hst_sw : fsSw.rebStage = fs.rebStage := rfl
              rw [hst_sw, ite_eq_left (by omega : fs.rebStage ≤ 3)]
              exact hbo }
        have hSw_om : ∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fsSw b' := by
          intro b' hb'
          by_cases hbb : b' = b
          · subst hbb
            left
            dsimp only [fsSw, epochTickStage2Swap, fsScan]
            simp [hins'_lt5]
          · have hne_om2 : fs.overmarsSliceIdx b' ≠ fs.overmarsSliceIdx b :=
              sliceIdx_ne (hc.roles_valid b' hb').2.1 hor_b fun h => absurd h hbb
            have hu_ne : ∀ (f : ℕ → ℕ) v, Function.update f b v b' = f b' :=
              fun _ _ => Function.update_of_ne hbb _ _
            refine (hom b' hb').of_eq_on
              (by dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  rw [Function.update_of_ne hbb]; exact fpAt_eq_of_fields rfl rfl _ _)
              rfl rfl (hu_ne _ _) rfl rfl (hu_ne _ _) (hu_ne _ _) (hu_ne _ _) (hu_ne _ _)
              (by
                have ho_idx : fsSw.overmarsSliceIdx b' = fs.overmarsSliceIdx b' := rfl
                rw [ho_idx]
                change Function.update (Function.update fs.slices rIdx sl')
                  (fs.overmarsSliceIdx b) _ (fs.overmarsSliceIdx b') = _
                rw [Function.update_of_ne hne_om2, Function.update_of_ne (hne_om_r b' hb')])
        have hd5_Sw : ∀ j < fs.dirtyCount,
            (j < fs.dirtyIdx + 1 → fsSw.rebDoneFlag (fs.dirtyBuckets j) = 1) ∧
            (fs.dirtyIdx + 1 ≤ j → fsSw.rebDoneFlag (fs.dirtyBuckets j) = 0) := by
          intro j hj
          dsimp only [fsSw, epochTickStage2Swap, fsScan]
          by_cases hjd : j = fs.dirtyIdx
          · subst hjd
            change (fs.dirtyIdx < fs.dirtyIdx + 1 → Function.update fs.rebDoneFlag b 1 b = 1) ∧
              (fs.dirtyIdx + 1 ≤ fs.dirtyIdx → Function.update fs.rebDoneFlag b 1 b = 0)
            rw [Function.update_self]; exact ⟨fun _ => rfl, fun h => by omega⟩
          · have hdb_ne : fs.dirtyBuckets j ≠ b := fun heq => hjd (hd4 j hj fs.dirtyIdx hd2 heq)
            rw [Function.update_of_ne hdb_ne]
            exact ⟨fun hlt => (hd5 j hj).1 (by omega), fun hge => (hd5 j hj).2 (by omega)⟩
        dsimp only [epochTickStage2AfterSwap]
        have hdc_sw : fsSw.dirtyCount = fs.dirtyCount := rfl
        by_cases hall_done : fsSw.dirtyCount ≤ fs.dirtyIdx + 1
        · rw [ite_eq_left hall_done]
          refine step_of_inLiveTree_eq hSw_core hSw_om rfl hc.epochClock_lt
            (show 3 ≤ 5 by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
            (fun b' hb' loc hloc => by
              change inLiveTree 3 fsSw.oldEp (fsSw.rebDoneFlag b') (fsSw.locState b' loc) =
                inLiveTree fsSw.rebStage fsSw.oldEp (fsSw.rebDoneFlag b') (fsSw.locState b' loc)
              rw [hst_sw, hold_sw, hls_sw]
              by_cases hst : fs.locState b' loc = 2 + fs.oldEp
              · obtain ⟨j, hj, hdb_j⟩ := hd6 b' hb' loc hloc hst
                have hdf1 : fsSw.rebDoneFlag b' = 1 :=
                  hdb_j ▸ (hd5_Sw j hj).1 (by rw [hdc_sw] at hall_done; omega)
                simp [inLiveTree, hst, hdf1]
              · simp [inLiveTree, beq_false_of_ne hst])
            (by
              dsimp only [FastState.oldEp]
              simp only [show (3 : ℕ) ≤ 3 by decide, ↓reduceIte]
              exact hbo) ?_ rfl
          dsimp only [ValidEpochStage]
          simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
            ↓reduceIte]
          exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        · rw [ite_eq_right hall_done]
          have hnxt_lt : fs.dirtyIdx + 1 < fs.dirtyCount := by rw [hdc_sw] at hall_done; omega
          set bNext := fsSw.dirtyBuckets (fs.dirtyIdx + 1)
          have hbNext : bNext < numBucketsWhp n_max := hd3 _ hnxt_lt
          set rIdxNext := fsSw.rebSliceIdx bNext
          obtain ⟨hlr_n, hor_n, hne_n⟩ := hSw_core.roles_valid bNext hbNext
          have hrr_n : fsSw.rebRole bNext < 3 ∧ fsSw.rebRole bNext ≠ fsSw.liveRole bNext ∧
              fsSw.rebRole bNext ≠ fsSw.overmarsRole bNext := by
            dsimp only [FastState.rebRole]; omega
          have hne_live_n : ∀ b' < numBucketsWhp n_max, fsSw.liveSliceIdx b' ≠ rIdxNext :=
            fun b' hb' => sliceIdx_ne (hSw_core.roles_valid b' hb').1 hrr_n.1
              fun h => h ▸ hrr_n.2.1.symm
          have hne_om_n : ∀ b' < numBucketsWhp n_max, fsSw.overmarsSliceIdx b' ≠ rIdxNext :=
            fun b' hb' => sliceIdx_ne (hSw_core.roles_valid b' hb').2.1 hrr_n.1
              fun h => h ▸ hrr_n.2.2.symm
          refine step_of_inLiveTree_eq hSw_core hSw_om rfl hc.epochClock_lt
            hc.rebStage_le rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            (fun b' hb' => Function.update_of_ne (hne_live_n b' hb') _ _)
            (fun b' hb' => Function.update_of_ne (hne_om_n b' hb') _ _)
            (fun _ _ _ _ => rfl)
            (by
              have hst_sw : ({ fsSw with
                  slices := Function.update fsSw.slices rIdxNext
                    (resetBTreeSlice (fsSw.slices rIdxNext)) } : FastState).rebStage =
                  fs.rebStage := rfl
              rw [hst_sw, ite_eq_left (by omega : fs.rebStage ≤ 3)]
              exact hbo) ?_ rfl
          dsimp only [ValidEpochStage]
          have hs2_sw : fsSw.rebStage = 2 := hs2
          rw [ite_eq_right (by rw [hs2_sw]; decide), ite_eq_right (by rw [hs2_sw]; decide),
            ite_eq_left hs2_sw]
          refine ⟨hd1, hnxt_lt, hd3, hd4, hd5_Sw, hd6, fun _ => ⟨Or.inl ⟨rfl, rfl⟩,
            fun _ hl => absurd (hl.trans_le (Nat.min_le_right _ _)) (Nat.not_lt_zero _),
            fun _ => none, ?_,
            by
              change SliceMapRel _ _ (min _ 0) _
              rw [Nat.min_zero]
              exact SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
          change ValidWhpSlice n_max 0
            (Function.update fsSw.slices rIdxNext (resetBTreeSlice (fsSw.slices rIdxNext)) rIdxNext)
            (fun _ => none)
          rw [Function.update_self]
          exact validWhpSlice_zero _ 0 _
      · -- Bucket `b` still scanning (`fs.rebScanCursor + 16 < fs.bktCount b`)
        rw [ite_eq_right hdone_b]
        have hcur_lt_b : fs.rebScanCursor + 16 < fs.bktCount b := Nat.lt_of_not_le hdone_b
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl
          (fun b' hb' => Function.update_of_ne (hne_live_r b' hb') _ _)
          (fun b' hb' => Function.update_of_ne (hne_om_r b' hb') _ _)
          (fun _ _ _ _ => rfl)
          (by
            dsimp only [FastState.oldEp]
            rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
            exact hbo)
          ?_ rfl
        dsimp only [ValidEpochStage]
        rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
          ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2]
        have hfp_eq : ({ fs with
            slices := Function.update fs.slices rIdx sl'
            rebScanCursor := fs.rebScanCursor + 16
            rebInsCount := ins' } : FastState).fpAt c U n_max θ fs.rebCandSalt b =
            fs.fpAt c U n_max θ fs.rebCandSalt b := fpAt_eq_of_fields rfl rfl _ _
        refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun _ => ⟨?_, ?_, rm', ?_, ?_⟩⟩
        · right
          refine ⟨by omega, hcur_lt_b, ?_⟩
          rcases hcur_r with ⟨hc0, hi0⟩ | ⟨_, _, hins_le⟩ <;> omega
        · rw [hfp_eq]; exact hinj'
        · change ValidWhpSlice n_max ins' (Function.update fs.slices rIdx sl' rIdx) rm'
          rw [Function.update_self]; exact hv'
        · rw [hfp_eq]; exact hrr'
  · -- Exhausted `sMaxWhp`: `epochTickStage2` is a no-op (`fs1 = fs`), vacuous in `ValidEpochStage`
    rw [ite_eq_right hcs_lt]
    refine ⟨hc, hom, ?_, rfl⟩
    dsimp only [ValidEpochStage]
    rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
      ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2]
    exact ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun h => absurd h hcs_lt⟩


end Cslib.DataStructure.Dictionary.SuccinctWhp

end

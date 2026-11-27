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
    exact Or.inr ⟨fs.slices (fs.rebSliceIdx b), fs.rebInsCount, rm,
      by simp [rebScanSteps], le_rfl, by simpa using hinj0, hvr, by simpa using hrr⟩
  | succ rem ih =>
    obtain ⟨rm0, hvr0, hrr0⟩ := hreb0
    dsimp only [rebScanSteps]
    rw [ite_eq_right (not_not.mpr hcoll0)]
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
        cases rem <;> exact Or.inl ⟨fs.slices rIdx, cur, fs.rebInsCount,
          by simp [rebScanSteps, cur, rIdx]⟩
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
        · exact Or.inl ⟨sl', cur', ins',
            by simpa only [hr1_idx, fs1, Function.update_idem] using heq⟩
        · dsimp only [fs1] at hins' hinj' hr'
          have hadd : cur + 1 + rem = cur + (rem + 1) := by omega
          rw [hfp1, hadd] at hinj' hr'
          exact Or.inr ⟨sl', ins', rm',
            by simpa only [hr1_idx, fs1, Function.update_idem, hadd] using heq,
            by omega, hinj', hv', hr'⟩
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
          have hlt {l} (hl : l < cur + 1) hp : l < cur :=
            Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl) fun h => hnp (h ▸ hp)
          exact ⟨fun l₁ hl₁ l₂ hl₂ hp₁ hp₂ => hinj0 l₁ (hlt hl₁ hp₁) l₂ (hlt hl₂ hp₂) hp₁ hp₂,
            hrr0.step_false hnp⟩
        · have hm0 : min (fs.bktCount b) cur = fs.bktCount b := Nat.min_eq_left (by omega)
          have hm1 : min (fs.bktCount b) (cur + 1) = fs.bktCount b := Nat.min_eq_left (by omega)
          rw [hm0] at hinj0 hrr0; rw [hm1]
          exact ⟨hinj0, hrr0⟩
      rcases ih fs1 hcoll0 hcnt_le (by dsimp only [fs1]; omega)
        (by dsimp only [fs1]; rw [hfp1]; exact hstep_min.1)
        ⟨rm0, hvr0, by dsimp only [fs1]; rw [hfp1]; exact hstep_min.2⟩ with
        ⟨sl', cur', ins', heq⟩ | ⟨sl', ins', rm', heq, hins', hinj', hv', hr'⟩
      · exact Or.inl ⟨sl', cur', ins', by simpa only [hr1_idx] using heq⟩
      · dsimp only [fs1] at hins' hinj' hr'
        have hadd : cur + 1 + rem = cur + (rem + 1) := by omega
        rw [hfp1, hadd] at hinj' hr'
        exact Or.inr ⟨sl', ins', rm',
          by simpa only [hr1_idx, fs1, cur, rIdx, hadd] using heq,
          by omega, hinj', hv', hr'⟩


/-- Slice indices `3 * b' + r'` and `3 * b + r` with roles `< 3` differ unless the buckets and the
roles both agree. -/
private theorem sliceIdx_ne {b b' r r' : ℕ} (hr' : r' < 3) (hr : r < 3)
    (hne : b' = b → r' ≠ r) : 3 * b' + r' ≠ 3 * b + r := fun heq =>
  hne (sliceIdx_inj hr' hr heq).1 (sliceIdx_inj hr' hr heq).2

private theorem rebSlice_disjoint {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) :
    (fs.rebRole b < 3 ∧ fs.rebRole b ≠ fs.liveRole b ∧ fs.rebRole b ≠ fs.overmarsRole b) ∧
    (∀ b' < numBucketsWhp n_max, fs.liveSliceIdx b' ≠ fs.rebSliceIdx b) ∧
    (∀ b' < numBucketsWhp n_max, fs.overmarsSliceIdx b' ≠ fs.rebSliceIdx b) := by
  obtain ⟨_, _, _⟩ := hc.roles_valid b hb
  have hrr : fs.rebRole b < 3 ∧ fs.rebRole b ≠ fs.liveRole b ∧
      fs.rebRole b ≠ fs.overmarsRole b := by
    dsimp only [FastState.rebRole]; omega
  exact ⟨hrr,
    fun b' hb' => sliceIdx_ne (hc.roles_valid b' hb').1 hrr.1 fun h => h ▸ hrr.2.1.symm,
    fun b' hb' => sliceIdx_ne (hc.roles_valid b' hb').2.1 hrr.1 fun h => h ▸ hrr.2.2.symm⟩

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
  simp only [ValidEpochStagePreTick, hs2, Nat.reduceEqDiff, ↓reduceIte] at hpre
  rcases hpre with ⟨hd1, hd2, hd3, hd4, hd5, hd6, hreb⟩
  have reset_step {s0 : FastState} (dIdx1 salt1 : ℕ) (sl0 : BTreeSlice)
      (hc0 : CoreFastInv c U V n_max θ s0 dict)
      (hom0 : ∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ s0 b')
      (hs2_0 : s0.rebStage = 2) (hclk0 : s0.epochClock = fs.epochClock)
      (hdc0 : s0.dirtyCount = fs.dirtyCount) (hdb0 : s0.dirtyBuckets = fs.dirtyBuckets)
      (hbkt0 : s0.bktCount = fs.bktCount) (hls0 : s0.locState = fs.locState)
      (hoe0 : s0.oldEp = fs.oldEp) (hd2' : dIdx1 < fs.dirtyCount)
      (hd5' : ∀ j < fs.dirtyCount,
        (j < dIdx1 → s0.rebDoneFlag (fs.dirtyBuckets j) = 1) ∧
        (dIdx1 ≤ j → s0.rebDoneFlag (fs.dirtyBuckets j) = 0)) :
      let s1 : FastState :=
        { s0 with
          dirtyIdx := dIdx1
          slices := Function.update s0.slices (s0.rebSliceIdx (s0.dirtyBuckets dIdx1))
            (resetBTreeSlice sl0)
          rebScanCursor := 0, rebInsCount := 0, rebCandSalt := salt1, rebCollision := 0 }
      CoreFastInv c U V n_max θ s1 dict ∧
      (∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ s1 b') ∧
      ValidEpochStage c U n_max θ s1 ∧ s1.epochClock = fs.epochClock := by
    intro s1
    obtain ⟨_, hne_live, hne_om⟩ := rebSlice_disjoint hc0 (hdb0 ▸ hd3 dIdx1 hd2')
    refine step_of_inLiveTree_eq hc0 hom0 rfl hc0.epochClock_lt hc0.rebStage_le rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun b' hb' => Function.update_of_ne (hne_live b' hb') _ _)
      (fun b' hb' => Function.update_of_ne (hne_om b' hb') _ _)
      (fun _ _ _ _ => rfl) hc0.bufOld_valid ?_ hclk0
    dsimp only [ValidEpochStage, s1, FastState.rebSliceIdx, FastState.rebRole,
      FastState.oldEp] at hoe0 ⊢
    simp only [hs2_0, Nat.reduceEqDiff, ↓reduceIte, hdc0, hdb0, hbkt0, hls0, hoe0,
      Function.update_self, Nat.min_zero]
    exact ⟨hd1, hd2', hd3, hd4, hd5', hd6, fun _ => ⟨Or.inl ⟨trivial, trivial⟩,
      fun _ hl => absurd hl (Nat.not_lt_zero _), fun _ => none,
      validWhpSlice_zero _ 0 _,
      SliceMapRel.empty_of_not _ _ 0 fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩
  unfold epochTickStage2 epochTickStage2PostScan; dsimp only
  rw [ite_eq_left hd2]
  set b := fs.dirtyBuckets fs.dirtyIdx
  have hb : b < numBucketsWhp n_max := hd3 _ hd2
  obtain ⟨_, hor_b, _⟩ := hc.roles_valid b hb
  obtain ⟨hrr_b, hne_live_r, hne_om_r⟩ := rebSlice_disjoint hc hb
  set rIdx := fs.rebSliceIdx b
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
      dsimp only [FastState.rebSliceIdx, FastState.rebRole, rIdx, b]
      rw [ite_eq_left (by decide)]
      simpa only [Function.update_idem, Function.update_self, FastState.rebSliceIdx,
        FastState.rebRole] using
        reset_step fs.dirtyIdx (fs.rebCandSalt + 1) sl_c
          hc hom hs2 rfl rfl rfl rfl rfl rfl hd2 hd5
    · -- Clean 16-step scan (`rebCollision = 0`)
      rw [hscan_ok]
      dsimp only
      rw [ite_eq_right (not_not.mpr hc.rebCollision_zero)]
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
            (st = 1 ∨ st = 2 + fs.oldEp) := fun st => by simp [inLiveTree]
        have hst_sw : fsSw.rebStage = 2 := hs2
        have hfp_sw : ∀ s, fsSw.fpAt c U n_max θ s = fs.fpAt c U n_max θ s :=
          fun s => by funext b0; exact fpAt_eq_of_fields rfl rfl s b0
        have hsw_b : fsSw.rebDoneFlag b = 1 ∧ fsSw.bktSalt b = fs.rebCandSalt ∧
            fsSw.liveInsCount b = ins' := by simp [fsSw, epochTickStage2Swap, fsScan]
        have hsw_o (b') (hbb : b' ≠ b) : fsSw.rebDoneFlag b' = fs.rebDoneFlag b' ∧
            fsSw.bktSalt b' = fs.bktSalt b' ∧ fsSw.liveInsCount b' = fs.liveInsCount b' := by
          simp [fsSw, epochTickStage2Swap, fsScan, hbb]
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
              rcases eq_or_ne b' b with rfl | hbb
              · simpa only [fsSw, epochTickStage2Swap, Function.update_self] using
                  ⟨hrr_b.1, hor_b, hrr_b.2.2⟩
              · simpa only [fsSw, epochTickStage2Swap, Function.update_of_ne hbb] using
                  hc.roles_valid b' hb'
            bktSalt_lt := fun b' hb' => by
              by_cases hbb : b' = b <;>
                simp [fsSw, epochTickStage2Swap, fsScan, hbb, hcs_lt, hc.bktSalt_lt b' hb']
            live_fp_inj := fun b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
              rw [hst_sw] at hin₁ hin₂
              rw [hfp_sw] at hfeq
              rcases eq_or_ne b' b with rfl | hbb
              · exact hinj' l₁ hl₁ l₂ hl₂ ((hinL_sw_b _).mp (hsw_b.1 ▸ hin₁))
                  ((hinL_sw_b _).mp (hsw_b.1 ▸ hin₂)) (hsw_b.2.1 ▸ hfeq)
              · rw [(hsw_o b' hbb).1, ← hs2] at hin₁ hin₂; rw [(hsw_o b' hbb).2.1] at hfeq
                exact hc.live_fp_inj b' hb' l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
            live_valid := fun b' hb' => by
              rw [hst_sw, hfp_sw]
              rcases eq_or_ne b' b with rfl | hbb
              · have hl_idx : fsSw.liveSliceIdx b = rIdx := by
                  simp [fsSw, epochTickStage2Swap, fsScan, FastState.liveSliceIdx,
                    FastState.rebRole, rIdx, FastState.rebSliceIdx]
                have hsl_b : fsSw.slices (fsSw.liveSliceIdx b) = sl' :=
                  hl_idx ▸ (Function.update_of_ne (hne_om_r b hb).symm _ _).trans
                    (Function.update_self ..)
                rw [hsw_b.1, hsw_b.2.1, hsw_b.2.2, hsl_b]
                exact ⟨rm', hv', hrr'.congr (fun _ _ => rfl)
                  (fun loc _ => hinL_sw_b (fs.locState b loc))⟩
              · have hl_idx : fsSw.liveSliceIdx b' = fs.liveSliceIdx b' := by
                  simp [fsSw, epochTickStage2Swap, fsScan, FastState.liveSliceIdx, hbb]
                have hsl_o :
                    fsSw.slices (fsSw.liveSliceIdx b') = fs.slices (fs.liveSliceIdx b') := by
                  rw [hl_idx]
                  exact (Function.update_of_ne
                    (sliceIdx_ne (hc.roles_valid b' hb').1 hor_b fun h => absurd h hbb) _ _).trans
                      (Function.update_of_ne (hne_live_r b' hb') _ _)
                obtain ⟨hdf_o, hbs_o, hlic_o⟩ := hsw_o b' hbb
                rw [hdf_o, hbs_o, hlic_o, hsl_o, ← hs2]
                exact hc.live_valid b' hb'
            rKey_buf_inj := hc.rKey_buf_inj
            bufCur_valid := hc.bufCur_valid
            bufOld_valid := hc.bufOld_valid }
        have hSw_om : ∀ b' < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fsSw b' := by
          intro b' hb'
          by_cases hbb : b' = b
          · subst hbb
            exact .inl (by simp [fsSw, epochTickStage2Swap, fsScan, hins'_lt5])
          · have hne_om2 : fs.overmarsSliceIdx b' ≠ fs.overmarsSliceIdx b :=
              sliceIdx_ne (hc.roles_valid b' hb').2.1 hor_b fun h => absurd h hbb
            have hu_ne : ∀ (f : ℕ → ℕ) v, Function.update f b v b' = f b' :=
              fun _ _ => Function.update_of_ne hbb _ _
            refine (hom b' hb').of_eq_on
              (by dsimp only [fsSw, epochTickStage2Swap, fsScan]
                  rw [Function.update_of_ne hbb]; exact fpAt_eq_of_fields rfl rfl _ _)
              rfl rfl (hu_ne _ _) rfl rfl (hu_ne _ _) (hu_ne _ _) (hu_ne _ _) (hu_ne _ _)
              (by
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
          have hbo := hc.bufOld_valid
          simp only [hs2, Nat.reduceLeDiff, ↓reduceIte] at hbo
          refine step_of_inLiveTree_eq hSw_core hSw_om rfl hc.epochClock_lt
            (Nat.le_add_left 3 2) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
            rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
            (fun b' hb' loc hloc => by
              change inLiveTree 3 fs.oldEp (fsSw.rebDoneFlag b') (fs.locState b' loc) =
                inLiveTree fsSw.rebStage fs.oldEp (fsSw.rebDoneFlag b') (fs.locState b' loc)
              rw [hst_sw]
              by_cases hst : fs.locState b' loc = 2 + fs.oldEp
              · obtain ⟨j, hj, hdb_j⟩ := hd6 b' hb' loc hloc hst
                have hdf1 : fsSw.rebDoneFlag b' = 1 :=
                  hdb_j ▸ (hd5_Sw j hj).1 (by rw [hdc_sw] at hall_done; omega)
                simp [inLiveTree, hst, hdf1]
              · simp [inLiveTree, beq_false_of_ne hst])
            (by
              simp only [FastState.oldEp, le_refl, ↓reduceIte]
              exact hbo) ?_ rfl
          simp only [ValidEpochStage, Nat.reduceEqDiff, ↓reduceIte]
          exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
        · rw [ite_eq_right hall_done]
          exact reset_step (fs.dirtyIdx + 1) 0
            (fsSw.slices (fsSw.rebSliceIdx (fsSw.dirtyBuckets (fs.dirtyIdx + 1))))
            hSw_core hSw_om hst_sw rfl rfl rfl rfl rfl rfl
            (by rw [hdc_sw] at hall_done; omega) hd5_Sw
      · -- Bucket `b` still scanning (`fs.rebScanCursor + 16 < fs.bktCount b`)
        rw [ite_eq_right hdone_b]
        have hcur_lt_b : fs.rebScanCursor + 16 < fs.bktCount b := Nat.lt_of_not_le hdone_b
        refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
          hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl rfl rfl
          (fun b' hb' => Function.update_of_ne (hne_live_r b' hb') _ _)
          (fun b' hb' => Function.update_of_ne (hne_om_r b' hb') _ _)
          (fun _ _ _ _ => rfl) hc.bufOld_valid ?_ rfl
        simp only [ValidEpochStage, hs2, Nat.reduceEqDiff, ↓reduceIte]
        have hfp_eq : ({ fs with
            slices := Function.update fs.slices rIdx sl'
            rebScanCursor := fs.rebScanCursor + 16
            rebInsCount := ins' } : FastState).fpAt c U n_max θ fs.rebCandSalt b =
            fs.fpAt c U n_max θ fs.rebCandSalt b := fpAt_eq_of_fields rfl rfl _ _
        refine ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun _ =>
          ⟨Or.inr ⟨by omega, hcur_lt_b,
            by rcases hcur_r with ⟨_, _⟩ | ⟨_, _, _⟩ <;> omega⟩,
           hfp_eq ▸ hinj', rm', ?_, hfp_eq ▸ hrr'⟩⟩
        change ValidWhpSlice n_max ins' (Function.update fs.slices rIdx sl' rIdx) rm'
        rwa [Function.update_self]
  · -- Exhausted `sMaxWhp`: `epochTickStage2` is a no-op (`fs1 = fs`), vacuous in `ValidEpochStage`
    rw [ite_eq_right hcs_lt]
    refine ⟨hc, hom, ?_, rfl⟩
    simp only [ValidEpochStage, hs2, Nat.reduceEqDiff, ↓reduceIte]
    exact ⟨hd1, hd2, hd3, hd4, hd5, hd6, fun h => absurd h hcs_lt⟩


end Cslib.DataStructure.Dictionary.SuccinctWhp

end

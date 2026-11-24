/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.WorkPotential
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpFastProb.ScanMeta

/-!
# Stage-by-Stage `epochTick` Work Decrease for `SuccinctWhpFastProb`

Internal proof that Stages `0 .. 4` strictly decrease `stageWorkRemaining` and that `epochTick`
always returns `some fs'` under bounded remaining work and collision-free trailing-window salts
(not re-exported by `SuccinctWhpFastProb`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset

private theorem tickStage0_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs0 : fs.rebStage = 0) :
    let fs1 := epochTickStage0 fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  have hia_le : (fs.buf fs.oldEp).itemAlloc ≤ 2 * sMaxWhp c n_max := hbo.1
  dsimp only [epochTickStage0]
  by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
  · rw [ite_eq_left hlt]
    cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩; dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, show ¬(1 = 0) by decide, ↓reduceIte, Nat.min_zero]
        unfold stage1Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs0] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, ↓reduceIte]; omega
    | none =>
      dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, show ¬(1 = 0) by decide, ↓reduceIte, Nat.min_zero]
        unfold stage1Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs0] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [hs0, ↓reduceIte]; omega
  · rw [ite_eq_right hlt]
    refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [hs0, show ¬(1 = 0) by decide, ↓reduceIte, Nat.min_zero]
    unfold stage1Max; omega

private theorem tickStage1Fin_props {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} (s : FastState) (sc₀ : ℕ)
    (hdc_le : s.dirtyCount ≤ 2 * sMaxWhp c n_max)
    (hd_lt : ∀ j < s.dirtyCount, s.dirtyBuckets j < numBucketsWhp n_max)
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))) :
    let f := epochTickStage1Finish s
    f.epochClock = s.epochClock ∧
    f.buf f.curEp = s.buf s.curEp ∧
    stageWorkRemaining c n_max f <
      (2 * sMaxWhp c n_max + 1 - min (2 * sMaxWhp c n_max) sc₀) + stage2Max c n_max ∧
    SaltBoundAt c U n_max θ W_keys f := by
  dsimp only [epochTickStage1Finish]
  by_cases hdc0 : s.dirtyCount = 0
  · rw [ite_eq_left hdc0]
    refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
      ↓reduceIte, Nat.min_zero]
    unfold stage2Max stage3Max; omega
  · rw [ite_eq_right hdc0]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · dsimp only [stageWorkRemaining]
      simp only [show ¬(2 = 0) by decide, show ¬(2 = 1) by decide, ↓reduceIte,
        Nat.sub_zero, Nat.min_zero]
      have hs_pos : 0 < sMaxWhp c n_max := sMaxWhp_pos c n_max
      have hb_eq : (sMaxWhp c n_max - 1) * (3 * (slabScale n_max) ^ 12 + 1) +
          3 * (slabScale n_max) ^ 12 + 1 = bktWorkUnit c n_max := by
        have := bktWorkUnit_eq c n_max; omega
      have htot_dc : (s.dirtyCount - 1) * bktWorkUnit c n_max + bktWorkUnit c n_max ≤
          (2 * sMaxWhp c n_max) * bktWorkUnit c n_max := by
        calc (s.dirtyCount - 1) * bktWorkUnit c n_max + bktWorkUnit c n_max
            = s.dirtyCount * bktWorkUnit c n_max := by
                cases hdc_eq : s.dirtyCount with
                | zero => exact absurd hdc_eq hdc0
                | succ d => simp [Nat.succ_mul]
          _ ≤ (2 * sMaxWhp c n_max) * bktWorkUnit c n_max := Nat.mul_le_mul_right _ hdc_le
      unfold stage2Max; omega
    · intro _ hdi
      obtain ⟨s_opt, hs_opt⟩ := hsalt_all ⟨s.dirtyBuckets 0, hd_lt 0 hdi⟩
      exact ⟨s_opt, hs_opt, Nat.zero_le _⟩

private theorem tickStage1_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs1 : fs.rebStage = 1)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))) :
    let fs1 := epochTickStage1 fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_le, _, oldMap, hv_o, hrel_o⟩ := hbo
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right hs0, ite_eq_left hs1] at hpre
  obtain ⟨hsc_le, hdc_sc, hd_props, _, _, _⟩ := hpre
  have hrem_eq : stageWorkRemaining c n_max fs =
      (2 * sMaxWhp c n_max + 1 - min (2 * sMaxWhp c n_max) fs.stageCursor) +
        stage2Max c n_max := by
    dsimp only [stageWorkRemaining]; rw [ite_eq_right hs0, ite_eq_left hs1]
  rw [hrem_eq]
  dsimp only [epochTickStage1]
  by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
  · rw [ite_eq_left hlt]
    cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩; dsimp only
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
      by_cases hq0 : fs.rebQueued b₀ = 0
      · rw [ite_eq_left hq0]
        by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
        · rw [ite_eq_left hdone]
          refine tickStage1Fin_props _ fs.stageCursor (by dsimp only; omega) (fun j hj => ?_)
            hsalt_all
          dsimp only at hj ⊢
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · rw [Function.update_of_ne (by omega)]; exact (hd_props j hj').1
          · simp [hb₀]
        · rw [ite_eq_right hdone]
          refine ⟨rfl, rfl, ?_, by intro h; rw [hs1] at h; cases h⟩
          dsimp only [stageWorkRemaining]
          rw [ite_eq_right hs0, ite_eq_left hs1]; omega
      · rw [ite_eq_right hq0]
        by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
        · rw [ite_eq_left hdone]
          exact tickStage1Fin_props _ fs.stageCursor (by dsimp only; omega)
            (fun j hj => (hd_props j hj).1) hsalt_all
        · rw [ite_eq_right hdone]
          refine ⟨rfl, rfl, ?_, by intro h; rw [hs1] at h; cases h⟩
          dsimp only [stageWorkRemaining]
          rw [ite_eq_right hs0, ite_eq_left hs1]; omega
    | none =>
      dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        exact tickStage1Fin_props _ fs.stageCursor (by dsimp only; omega)
          (fun j hj => (hd_props j hj).1) hsalt_all
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs1] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        rw [ite_eq_right hs0, ite_eq_left hs1]; omega
  · rw [ite_eq_right hlt]
    exact tickStage1Fin_props fs fs.stageCursor (hdc_sc.trans (hsc_le.trans hia_le))
      (fun j hj => (hd_props j hj).1) hsalt_all

private theorem tickStage2_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs2 : fs.rebStage = 2)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U)))
    (hsalt_cur : SaltBoundAt c U n_max θ W_keys fs) :
    let fs1 := epochTickStage2 c U n_max θ fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hs1 : ¬(fs.rebStage = 1) := by omega
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2] at hpre
  obtain ⟨_, hd2, hd3, _, _, _, hreb⟩ := hpre
  set b := fs.dirtyBuckets fs.dirtyIdx
  have hb : b < numBucketsWhp n_max := hd3 _ hd2
  obtain ⟨s_opt, hs_opt_inj, hc_le_s_opt⟩ := hsalt_cur hs2 hd2
  have hcs_lt : fs.rebCandSalt < sMaxWhp c n_max := hc_le_s_opt.trans_lt s_opt.isLt
  obtain ⟨hcur_r, _, rm0, hvr0, hrr0⟩ := hreb hcs_lt
  have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  have hrem_fs : stageWorkRemaining c n_max fs =
      (fs.dirtyCount - 1 - fs.dirtyIdx) * bktWorkUnit c n_max +
      (sMaxWhp c n_max - 1 - fs.rebCandSalt) * (3 * (slabScale n_max) ^ 12 + 1) +
      (3 * (slabScale n_max) ^ 12 - min (3 * (slabScale n_max) ^ 12) fs.rebScanCursor) +
      1 + stage3Max c n_max := by
    dsimp only [stageWorkRemaining]; rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2]
  rw [hrem_fs]
  unfold epochTickStage2 epochTickStage2PostScan; dsimp only
  rw [ite_eq_left hd2, ite_eq_left hcs_lt]
  set fsScan := rebScanSteps c U n_max θ b 16 fs
  obtain ⟨hm_clk, hm_ep, hm_buf, hm_stg, hm_dc, hm_di, hm_db, hm_cs, hm_cnt⟩ :=
    rebScanSteps_meta c U n_max b θ 16 fs
  by_cases hcoll_nz : fsScan.rebCollision ≠ 0
  · rw [ite_eq_left hcoll_nz]
    have hne_s_opt : fs.rebCandSalt ≠ s_opt.val := by
      intro heq_s; apply hcoll_nz
      have hins_ub : fs.rebInsCount + 16 ≤ 8 * (slabScale n_max) ^ 12 := by
        have hL2 := two_le_slabScale n_max
        have : 4096 ≤ (slabScale n_max) ^ 12 := by
          calc 4096 = 2 ^ 12 := by norm_num
            _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
        rcases hcur_r with ⟨_, hi0⟩ | ⟨_, hc_le, hins_le⟩ <;> omega
      refine rebScanSteps_rebCollision_eq_zero_of_inj hc.hth θ 16 fs hc.rebCollision_zero
        hcnt_3L hins_ub (fun l₁ hl₁ l₂ hl₂ _ _ hfp_eq => ?_) ⟨rm0, hvr0, hrr0⟩
      obtain ⟨hm₁, hfb₁⟩ := hc.mem_dom_of_loc hb hl₁
      obtain ⟨hm₂, hfb₂⟩ := hc.mem_dom_of_loc hb hl₂
      let u₁ : Fin U := ⟨fs.keyValAt c U n_max θ.1 b l₁, (hc.active_item b hb l₁ hl₁).1⟩
      let u₂ : Fin U := ⟨fs.keyValAt c U n_max θ.1 b l₂, (hc.active_item b hb l₂ hl₂).1⟩
      have hw₁ : u₁ ∈ W_keys.filter
          (fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b) :=
        mem_filter.mpr ⟨hdom_sub hm₁, hfb₁⟩
      have hw₂ : u₂ ∈ W_keys.filter
          (fun u => feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b) :=
        mem_filter.mpr ⟨hdom_sub hm₂, hfb₂⟩
      have hf₁ : fs.fpAt c U n_max θ fs.rebCandSalt b l₁ = fpHash c U n_max θ.2 s_opt u₁ := by
        dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₁.isLt, u₁]
      have hf₂ : fs.fpAt c U n_max θ fs.rebCandSalt b l₂ = fpHash c U n_max θ.2 s_opt u₂ := by
        dsimp only [FastState.fpAt]; simp [heq_s, s_opt.isLt, u₂.isLt, u₂]
      have hu_eq : u₁ = u₂ := hs_opt_inj hw₁ hw₂ (hf₁.symm.trans (hfp_eq.trans hf₂))
      have hkv_eq : fs.keyValAt c U n_max θ.1 b l₁ = fs.keyValAt c U n_max θ.1 b l₂ :=
        congrArg Fin.val hu_eq
      have hq₁ := (hc.active_item b hb l₁ hl₁).2.2.1
      have hq₂ := (hc.active_item b hb l₂ hl₂).2.2.1
      exact hc.quot_inj b hb l₁ hl₁ l₂ hl₂ (hq₁.symm.trans (hkv_eq ▸ hq₂))
    have hlt_s_opt : fs.rebCandSalt < s_opt.val := Nat.lt_of_le_of_ne hc_le_s_opt hne_s_opt
    refine ⟨hm_clk, by dsimp only; rw [hm_buf, hm_ep], ?_, ?_⟩
    · dsimp only [stageWorkRemaining]
      rw [hm_stg, hm_dc, hm_di, hm_cs, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2,
        Nat.min_zero]
      have hs_lt_max : fs.rebCandSalt + 1 ≤ sMaxWhp c n_max - 1 := by have := s_opt.isLt; omega
      have hsub1 : sMaxWhp c n_max - 1 - fs.rebCandSalt =
          (sMaxWhp c n_max - 1 - (fs.rebCandSalt + 1)) + 1 := by omega
      rw [hsub1, Nat.add_mul, one_mul]; omega
    · intro _ _
      refine ⟨s_opt, ?_, ?_⟩
      · dsimp only; rw [hm_db, hm_di]; exact hs_opt_inj
      · dsimp only; rw [hm_cs]; omega
  · rw [ite_eq_right hcoll_nz]
    have hm_cur := rebScanSteps_cursor_of_zero c U n_max b θ 16 fs
      (Classical.not_not.mp hcoll_nz)
    by_cases hdone_b : fsScan.bktCount b ≤ fsScan.rebScanCursor
    · rw [ite_eq_left hdone_b]
      unfold epochTickStage2AfterSwap epochTickStage2Swap; dsimp only
      by_cases hall_done : fsScan.dirtyCount ≤ fsScan.dirtyIdx + 1
      · rw [ite_eq_left hall_done]
        refine ⟨hm_clk, by dsimp only; rw [hm_buf, hm_ep], ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [show ¬(3 = 0) by decide, show ¬(3 = 1) by decide, show ¬(3 = 2) by decide,
          ↓reduceIte, Nat.min_zero]
        unfold stage3Max; omega
      · rw [ite_eq_right hall_done]
        refine ⟨hm_clk, by dsimp only; rw [hm_buf, hm_ep], ?_, ?_⟩
        · dsimp only [stageWorkRemaining]
          rw [hm_stg, hm_dc, hm_di, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2,
            Nat.min_zero]
          have hnxt_lt : fs.dirtyIdx + 1 < fs.dirtyCount := by rw [hm_dc, hm_di] at hall_done; omega
          have hsub_d : fs.dirtyCount - 1 - fs.dirtyIdx =
              (fs.dirtyCount - 1 - (fs.dirtyIdx + 1)) + 1 := by omega
          have hb_eq : (sMaxWhp c n_max - 1 - 0) * (3 * (slabScale n_max) ^ 12 + 1) +
              (3 * (slabScale n_max) ^ 12 - 0) + 1 = bktWorkUnit c n_max := by
            have := bktWorkUnit_eq c n_max; omega
          rw [hsub_d, Nat.add_mul, one_mul]; omega
        · intro _ hdi'
          dsimp only at hdi' ⊢
          rw [hm_db, hm_di]; rw [hm_dc, hm_di] at hdi'
          obtain ⟨s_opt', hs_opt'⟩ := hsalt_all ⟨fs.dirtyBuckets (fs.dirtyIdx + 1), hd3 _ hdi'⟩
          exact ⟨s_opt', hs_opt', Nat.zero_le _⟩
    · rw [ite_eq_right hdone_b]
      refine ⟨hm_clk, by rw [hm_buf, hm_ep], ?_, ?_⟩
      · dsimp only [stageWorkRemaining]
        rw [hm_stg, hm_dc, hm_di, hm_cs, hm_cur, ite_eq_right hs0, ite_eq_right hs1,
          ite_eq_left hs2]
        have hlt_3L : fs.rebScanCursor + 16 < 3 * (slabScale n_max) ^ 12 := by
          rw [hm_cnt, hm_cur] at hdone_b; omega
        omega
      · intro _ _; rw [hm_db, hm_di, hm_cs]; exact ⟨s_opt, hs_opt_inj, hc_le_s_opt⟩

private theorem tickStage3_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs3 : fs.rebStage = 3) :
    let fs1 := epochTickStage3 c U n_max θ fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hs1 : ¬(fs.rebStage = 1) := by omega
  have hs2 : ¬(fs.rebStage = 2) := by omega
  have hne_ep : fs.curEp ≠ fs.oldEp := by
    dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_le, hna_le, _, hv_o, _⟩ := hbo
  have hmul_le : cTabWhp c * (fs.buf fs.oldEp).itemAlloc ≤ cTabWhp c * (2 * sMaxWhp c n_max) :=
    Nat.mul_le_mul_left _ hia_le
  have hrem_fs : stageWorkRemaining c n_max fs =
      (2 * sMaxWhp c n_max + 1 - min (2 * sMaxWhp c n_max) fs.stageCursor) +
        stage4Max c n_max := by
    dsimp only [stageWorkRemaining]
    rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_left hs3]
  rw [hrem_fs]
  dsimp only [epochTickStage3]
  by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
  · rw [ite_eq_left hlt]
    cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩; dsimp only
      obtain ⟨_, hna_eq, hia_eq, _, _⟩ :=
        hv_o.delete_spec (rKey := fs.rKeyAt c U n_max θ b₀ loc₀)
          (by
            dsimp only [FastState.rKeyAt]
            split_ifs with hu
            · exact fpReducedKey_lt c U n_max θ.2 ⟨_, hu⟩
            · exact Nat.two_pow_pos _)
      set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp)
        (fs.rKeyAt c U n_max θ b₀ loc₀)
      have hbuf_o' : Function.update fs.buf fs.oldEp tr' fs.oldEp = tr' :=
        Function.update_self _ _ _
      by_cases hdone : (Function.update fs.buf fs.oldEp tr' fs.oldEp).itemAlloc ≤
          fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
          show ¬(4 = 3) by decide, ↓reduceIte]
        change (Function.update fs.buf fs.oldEp tr' fs.oldEp).nodeAlloc < _
        rw [hbuf_o', hna_eq]; unfold stage4Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; rw [hs3] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_left hs3]
        rw [hbuf_o', hia_eq] at hdone; omega
    | none =>
      dsimp only
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
        dsimp only [stageWorkRemaining]
        simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
          show ¬(4 = 3) by decide, ↓reduceIte]
        change (fs.buf fs.oldEp).nodeAlloc < _
        unfold stage4Max; omega
      · rw [ite_eq_right hdone]
        refine ⟨rfl, rfl, ?_, by intro h; rw [hs3] at h; cases h⟩
        dsimp only [stageWorkRemaining]
        rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_left hs3]; omega
  · rw [ite_eq_right hlt]
    refine ⟨rfl, rfl, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
      show ¬(4 = 3) by decide, ↓reduceIte]
    change (fs.buf fs.oldEp).nodeAlloc < _
    unfold stage4Max; omega

private theorem tickStage4_props {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hs4 : fs.rebStage = 4) :
    let fs1 := epochTickStage4 fs
    fs1.epochClock = fs.epochClock ∧
    fs1.buf fs1.curEp = fs.buf fs.curEp ∧
    stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
    SaltBoundAt c U n_max θ W_keys fs1 := by
  have hs0 : ¬(fs.rebStage = 0) := by omega
  have hs1 : ¬(fs.rebStage = 1) := by omega
  have hs2 : ¬(fs.rebStage = 2) := by omega
  have hs3 : ¬(fs.rebStage = 3) := by omega
  have hne_ep : fs.curEp ≠ fs.oldEp := by
    dsimp only [FastState.oldEp]; rcases hc.curEp_or with h | h <;> omega
  have hbo := hc.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
  obtain ⟨_, hclr, _⟩ := hbo
  have h1_le : 1 ≤ (fs.buf fs.oldEp).nodeAlloc := hclr.bounds.1
  have hrem_fs : stageWorkRemaining c n_max fs = (fs.buf fs.oldEp).nodeAlloc := by
    dsimp only [stageWorkRemaining]
    rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_right hs3, ite_eq_left hs4]
  rw [hrem_fs]
  dsimp only [epochTickStage4]
  by_cases hle8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
  · rw [decide_eq_true hle8, ite_eq_left rfl]
    refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(5 = 0) by decide, show ¬(5 = 1) by decide, show ¬(5 = 2) by decide,
      show ¬(5 = 3) by decide, show ¬(5 = 4) by decide, ↓reduceIte]
    omega
  · rw [decide_eq_false hle8, ite_eq_right Bool.false_ne_true]
    refine ⟨rfl, Function.update_of_ne hne_ep _ _, ?_, by intro h; cases h⟩
    dsimp only [stageWorkRemaining]
    simp only [show ¬(4 = 0) by decide, show ¬(4 = 1) by decide, show ¬(4 = 2) by decide,
      show ¬(4 = 3) by decide, ↓reduceIte]
    change (Function.update fs.buf fs.oldEp (bufClearSteps 8 (fs.buf fs.oldEp)) fs.oldEp).nodeAlloc
      < _
    rw [Function.update_self, hclr.clearSteps_nodeAlloc_eq 8]; omega

/-- Under bounded remaining rebuild work and collision-free window salts `< sMaxWhp c n_max`,
`epochTick` always returns `some fs'`, preserves the work bound and Stage-2 salt invariant, and
either leaves `fs'.buf fs'.curEp` untouched or rolls over to `itemAlloc = 0`. -/
theorem epochTick_some_of_work_bound {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hdom_sub : (Dictionary.dom dict : Set (Fin U)) ⊆ (W_keys : Set (Fin U)))
    (hsalt_all : ∀ b : Fin (numBucketsWhp n_max),
      ∃ salt : Fin (sMaxWhp c n_max),
        Set.InjOn (fpHash c U n_max θ.2 salt)
          (W_keys.filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U)))
    (hsalt_cur : SaltBoundAt c U n_max θ W_keys fs)
    (hwork : fs.epochClock + stageWorkRemaining c n_max fs + 1 ≤ qEpochWhp n_max) :
    ∃ fs',
      epochTick c U n_max θ fs = some fs' ∧
      ValidFastState c U V n_max θ fs' dict ∧
      fs'.epochClock + stageWorkRemaining c n_max fs' + 1 ≤ qEpochWhp n_max ∧
      SaltBoundAt c U n_max θ W_keys fs' ∧
      (fs'.buf fs'.curEp = fs.buf fs.curEp ∨ (fs'.buf fs'.curEp).itemAlloc = 0) := by
  set fs1 := epochTickStage c U n_max θ fs
  have h1 :
      (fs.rebStage < 5 ∧ fs1.epochClock = fs.epochClock ∧ fs1.buf fs1.curEp = fs.buf fs.curEp ∧
       stageWorkRemaining c n_max fs1 < stageWorkRemaining c n_max fs ∧
       SaltBoundAt c U n_max θ W_keys fs1) ∨
      (fs.rebStage = 5 ∧ fs1 = fs) := by
    dsimp only [fs1, epochTickStage]
    by_cases hs0 : fs.rebStage = 0
    · rw [ite_eq_left hs0]; exact Or.inl ⟨by omega, tickStage0_props hc hs0⟩
    rw [ite_eq_right hs0]
    by_cases hs1 : fs.rebStage = 1
    · rw [ite_eq_left hs1]; exact Or.inl ⟨by omega, tickStage1_props hc hs1 hpre hsalt_all⟩
    rw [ite_eq_right hs1]
    by_cases hs2 : fs.rebStage = 2
    · rw [ite_eq_left hs2]
      exact Or.inl ⟨by omega, tickStage2_props hc hs2 hpre hdom_sub hsalt_all hsalt_cur⟩
    rw [ite_eq_right hs2]
    by_cases hs3 : fs.rebStage = 3
    · rw [ite_eq_left hs3]; exact Or.inl ⟨by omega, tickStage3_props hc hs3⟩
    rw [ite_eq_right hs3]
    by_cases hs4 : fs.rebStage = 4
    · rw [ite_eq_left hs4]; exact Or.inl ⟨by omega, tickStage4_props hc hs4⟩
    rw [ite_eq_right hs4]
    exact Or.inr ⟨by have := hc.rebStage_le; omega, rfl⟩
  rcases h1 with ⟨_, hclk1, hbuf1, hw_lt, hsalt1⟩ | ⟨hs5, hfs1_eq⟩
  · have hno_roll : ¬(qEpochWhp n_max ≤ fs1.epochClock + 1) := by omega
    have htick_some :
        epochTick c U n_max θ fs = some { fs1 with epochClock := fs1.epochClock + 1 } := by
      unfold epochTick epochTickRollover; dsimp only; exact ite_eq_right hno_roll
    have hv' := epochTick_spec hc hom hpre htick_some
    refine ⟨{ fs1 with epochClock := fs1.epochClock + 1 }, htick_some, hv', ?_, hsalt1,
      Or.inl hbuf1⟩
    have hw_eq : stageWorkRemaining c n_max { fs1 with epochClock := fs1.epochClock + 1 } =
        stageWorkRemaining c n_max fs1 := rfl
    rw [hw_eq]; dsimp only; omega
  · have hw0 : stageWorkRemaining c n_max fs = 0 := by
      dsimp only [stageWorkRemaining]; simp [hs5]
    change epochTickStage c U n_max θ fs = fs at hfs1_eq
    by_cases hroll : qEpochWhp n_max ≤ fs.epochClock + 1
    · have htick_some : epochTick c U n_max θ fs =
          some { fs with
            curEp := 1 - fs.curEp, epochClock := 0, rebStage := 0, stageCursor := 0 } := by
        unfold epochTick; rw [hfs1_eq]; unfold epochTickRollover; dsimp only
        rw [ite_eq_left hroll, ite_eq_left hs5]
      have hv' := epochTick_spec hc hom hpre htick_some
      set fs' : FastState :=
        { fs with curEp := 1 - fs.curEp, epochClock := 0, rebStage := 0, stageCursor := 0 }
      have hbo5 := hc.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)),
        ite_eq_right (by omega : ¬(fs.rebStage = 4))] at hbo5
      refine ⟨fs', htick_some, hv', ?_, (fun h => by cases h),
        Or.inr hbo5.2.2.2⟩
      have hw_le := stageWorkRemaining_le_max hv'.toCore hv'.stage_valid
      have hmax_le := stageWorkMax_add_one_le_qEpoch hc.hth
      have hclk0 : fs'.epochClock = 0 := rfl
      omega
    · have htick_some :
          epochTick c U n_max θ fs = some { fs with epochClock := fs.epochClock + 1 } := by
        unfold epochTick; rw [hfs1_eq]; unfold epochTickRollover; dsimp only
        exact ite_eq_right hroll
      have hv' := epochTick_spec hc hom hpre htick_some
      refine ⟨{ fs with epochClock := fs.epochClock + 1 }, htick_some, hv', ?_, hsalt_cur,
        Or.inl rfl⟩
      have hw_eq : stageWorkRemaining c n_max { fs with epochClock := fs.epochClock + 1 } = 0 := hw0
      rw [hw_eq]; dsimp only; omega

end Cslib.DataStructure.Dictionary.SuccinctWhp

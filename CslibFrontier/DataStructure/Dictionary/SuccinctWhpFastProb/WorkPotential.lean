/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Epoch Rebuild Potential and Clean-Window Invariant for `SuccinctWhpFastProb`

Internal definitions and potential bounds (`stageWorkRemaining`, `stageWorkMax_add_one_le_qEpoch`,
`stageWorkRemaining_le_max`, `SaltBoundAt`, and `CleanWindowFast`) used across the deterministic
`SuccinctWhpFastProb` fast-path proof submodules (not re-exported by `SuccinctWhpFastProb`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset

/-- Maximum Stage-4 remaining work `1 + cTabWhp c * (2 * sMaxWhp c n_max)`. -/
@[expose] def stage4Max (c n_max : ℕ) : ℕ :=
  1 + cTabWhp c * (2 * sMaxWhp c n_max)

/-- Maximum Stage-3 remaining work. -/
@[expose] def stage3Max (c n_max : ℕ) : ℕ :=
  (2 * sMaxWhp c n_max + 2) + stage4Max c n_max

/-- Per-dirty-bucket Stage-2 work budget `sMaxWhp c n_max * (3 * L ^ 12 + 1)`. -/
@[expose] def bktWorkUnit (c n_max : ℕ) : ℕ :=
  sMaxWhp c n_max * (3 * (slabScale n_max) ^ 12 + 1)

/-- Maximum Stage-2 remaining work across `≤ 2 * sMaxWhp c n_max` dirty buckets. -/
@[expose] def stage2Max (c n_max : ℕ) : ℕ :=
  (2 * sMaxWhp c n_max) * bktWorkUnit c n_max + 1 + stage3Max c n_max

/-- Maximum Stage-1 remaining work. -/
@[expose] def stage1Max (c n_max : ℕ) : ℕ :=
  (2 * sMaxWhp c n_max + 2) + stage2Max c n_max

/-- Maximum Stage-0..4 remaining background rebuild work per epoch. -/
@[expose] def stageWorkMax (c n_max : ℕ) : ℕ :=
  (2 * sMaxWhp c n_max + 2) + stage1Max c n_max

/-- Monotone remaining-work potential for `epochTick` across Stages `0 .. 5`. -/
@[expose] def stageWorkRemaining (c n_max : ℕ) (fs : FastState) : ℕ :=
  let r2 := 2 * sMaxWhp c n_max
  let L12_3 := 3 * (slabScale n_max) ^ 12
  if fs.rebStage = 0 then
    (r2 + 1 - min r2 fs.stageCursor) + stage1Max c n_max
  else if fs.rebStage = 1 then
    (r2 + 1 - min r2 fs.stageCursor) + stage2Max c n_max
  else if fs.rebStage = 2 then
    (fs.dirtyCount - 1 - fs.dirtyIdx) * bktWorkUnit c n_max +
    (sMaxWhp c n_max - 1 - fs.rebCandSalt) * (L12_3 + 1) +
    (L12_3 - min L12_3 fs.rebScanCursor) + 1 + stage3Max c n_max
  else if fs.rebStage = 3 then
    (r2 + 1 - min r2 fs.stageCursor) + stage4Max c n_max
  else if fs.rebStage = 4 then
    (fs.buf fs.oldEp).nodeAlloc
  else 0

/-- `stageWorkMax c n_max + 1 ≤ qEpochWhp n_max` whenever `whpThreshold c ≤ n_max`. -/
theorem stageWorkMax_add_one_le_qEpoch {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    stageWorkMax c n_max + 1 ≤ qEpochWhp n_max := by
  set L := slabScale n_max
  obtain ⟨hL_big, hL_c⟩ := cEff_add_four_le_scaleWhp hth
  have hr_le : sMaxWhp c n_max ≤ L ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right L hL_c
  have hL4 : stage4Max c n_max ≤ 19 * L ^ 3 := by
    have : cTabWhp c * (2 * sMaxWhp c n_max) ≤ (9 * L) * (2 * L ^ 2) :=
      Nat.mul_le_mul (by unfold cTabWhp; omega) (Nat.mul_le_mul_left 2 hr_le)
    have := Nat.one_le_pow 3 L (by omega)
    unfold stage4Max; nlinarith
  have hbu : bktWorkUnit c n_max ≤ 4 * L ^ 14 := by
    have : sMaxWhp c n_max * (3 * L ^ 12 + 1) ≤ L ^ 2 * (4 * L ^ 12) :=
      Nat.mul_le_mul hr_le (by have := Nat.one_le_pow 12 L (by omega); omega)
    unfold bktWorkUnit; nlinarith
  have h2r_bu : (2 * sMaxWhp c n_max) * bktWorkUnit c n_max ≤ 8 * L ^ 16 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr_le) hbu
    nlinarith
  have := Nat.pow_le_pow_right (n := L) (by omega) (by decide : 3 ≤ 16)
  have := Nat.pow_le_pow_right (n := L) (by omega) (by decide : 2 ≤ 16)
  have : 2 ≤ L ^ 16 := (show 2 ≤ L by omega).trans (Nat.le_self_pow (by decide) L)
  calc stageWorkMax c n_max + 1
      ≤ 40 * L ^ 16 := by unfold stageWorkMax stage1Max stage2Max stage3Max; omega
    _ ≤ L ^ 2 * L ^ 16 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = qEpochWhp n_max := by unfold qEpochWhp; ring

/-- Closed-form rewrite splitting the last bucket's Stage-2 work off `bktWorkUnit`. -/
theorem bktWorkUnit_eq (c n_max : ℕ) :
    (sMaxWhp c n_max - 1) * (3 * (slabScale n_max) ^ 12 + 1) +
      (3 * (slabScale n_max) ^ 12 + 1) = bktWorkUnit c n_max := by
  unfold bktWorkUnit
  cases hsm : sMaxWhp c n_max with
  | zero => have := sMaxWhp_pos c n_max; omega
  | succ k => simp [Nat.succ_mul]

/-- Every valid `FastState` has `stageWorkRemaining c n_max fs ≤ stageWorkMax c n_max`. -/
theorem stageWorkRemaining_le_max {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hstg : ValidEpochStage c U n_max θ fs) :
    stageWorkRemaining c n_max fs ≤ stageWorkMax c n_max := by
  dsimp only [stageWorkRemaining]
  unfold stageWorkMax stage1Max stage2Max stage3Max
  split_ifs with hs0 hs1 hs2 hs3 hs4 <;> try omega
  · dsimp only [ValidEpochStage] at hstg
    rw [ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2] at hstg
    obtain ⟨hdc_le, hdi_lt, _⟩ := hstg
    have := sMaxWhp_pos c n_max
    have := bktWorkUnit_eq c n_max
    have := Nat.mul_le_mul_right (3 * slabScale n_max ^ 12 + 1)
      (Nat.sub_le (sMaxWhp c n_max - 1) fs.rebCandSalt)
    have := Nat.mul_le_mul_right (bktWorkUnit c n_max)
      (show fs.dirtyCount - 1 - fs.dirtyIdx + 1 ≤ 2 * sMaxWhp c n_max by omega)
    rw [add_one_mul] at this
    omega
  · have hbo := hc.bufOld_valid
    rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
    have : (fs.buf fs.oldEp).nodeAlloc ≤ stage4Max c n_max := hbo.2.2
    omega

/-- Active Stage-2 salt search bound: candidate salt has not yet passed the collision-free salt. -/
@[expose] def SaltBoundAt (c U n_max : ℕ) (θ : SeedWhp c U n_max) (W_keys : Finset (Fin U))
    (fs : FastState) : Prop :=
  fs.rebStage = 2 → fs.dirtyIdx < fs.dirtyCount →
    ∃ s_opt : Fin (sMaxWhp c n_max),
      Set.InjOn (fpHash c U n_max θ.2 s_opt)
        (W_keys.filter (fun u =>
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val =
            fs.dirtyBuckets fs.dirtyIdx) : Set (Fin U)) ∧
      fs.rebCandSalt ≤ s_opt.val

theorem stageWorkRemaining_eq_of_meta (c n_max : ℕ) {s₁ s₂ : FastState}
    (h1 : s₁.rebStage = s₂.rebStage) (h2 : s₁.stageCursor = s₂.stageCursor)
    (h3 : s₁.dirtyCount = s₂.dirtyCount) (h4 : s₁.dirtyIdx = s₂.dirtyIdx)
    (h5 : s₁.rebCandSalt = s₂.rebCandSalt) (h6 : s₁.rebScanCursor = s₂.rebScanCursor)
    (h7 : (s₁.buf s₁.oldEp).nodeAlloc = (s₂.buf s₂.oldEp).nodeAlloc) :
    stageWorkRemaining c n_max s₁ = stageWorkRemaining c n_max s₂ := by
  dsimp only [stageWorkRemaining]
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- Clean-epoch fast-mode invariant along the trailing window `(W_keys, BadIns)`. -/
structure CleanWindowFast (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (W_keys BadIns : Finset (Fin U)) (fs : FastState) (dict : State U) : Prop where
  valid : ValidFastState c U V n_max θ fs dict
  buf_alloc :
    (fs.buf fs.curEp).itemAlloc ≤
      #(BadIns.filter fun u =>
        bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
          (fpReducedKey c U n_max θ.2 u))
  work_le : fs.epochClock + stageWorkRemaining c n_max fs + 1 ≤ qEpochWhp n_max
  salt_bound : SaltBoundAt c U n_max θ W_keys fs

theorem CleanWindowFast.of_clean_fast {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys BadIns : Finset (Fin U)} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict)
    (hia0 : (fs.buf fs.curEp).itemAlloc = 0)
    (hclk0 : fs.epochClock = 0)
    (hno2 : fs.rebStage ≠ 2) :
    CleanWindowFast c U V n_max θ W_keys BadIns fs dict :=
  { valid := hv
    buf_alloc := by rw [hia0]; exact Nat.zero_le _
    work_le := by
      have hw := stageWorkRemaining_le_max hv.toCore hv.stage_valid
      have hm := stageWorkMax_add_one_le_qEpoch hv.hth
      omega
    salt_bound := fun hs2 => absurd hs2 hno2 }

end Cslib.DataStructure.Dictionary.SuccinctWhp

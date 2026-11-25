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
# Epoch Clock Progression, Rollover Reset, and `trySelfHeal` Entry for `SuccinctWhpFastProb`

Internal transition lemmas tracking `epochClock`, rollover clean-epoch initialization
(`epochTick_clean_or_clock`), and `trySelfHeal` clean entry (`trySelfHeal_clean`)
(not re-exported by `SuccinctWhpFastProb`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset

private theorem tickStage_epochClock (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) :
    (epochTickStage c U n_max θ fs).epochClock = fs.epochClock := by
  dsimp only [epochTickStage]
  by_cases hs0 : fs.rebStage = 0
  · rw [ite_eq_left hs0]; dsimp only [epochTickStage0]
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt]
      cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · dsimp only; split_ifs <;> rfl
      · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
    · rw [ite_eq_right hlt]
  rw [ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1]; dsimp only [epochTickStage1, epochTickStage1Finish]
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt]
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · dsimp only; split_ifs <;> rfl
        · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
      · rw [ite_eq_right hdone]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · rfl
        · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
    · rw [ite_eq_right hlt]; split_ifs <;> rfl
  rw [ite_eq_right hs1]
  by_cases hs2 : fs.rebStage = 2
  · rw [ite_eq_left hs2]
    unfold epochTickStage2 epochTickStage2PostScan epochTickStage2AfterSwap epochTickStage2Swap
    dsimp only
    by_cases hd : fs.dirtyIdx < fs.dirtyCount
    · rw [ite_eq_left hd]
      by_cases hcs : fs.rebCandSalt < sMaxWhp c n_max
      · rw [ite_eq_left hcs]
        have hm := (rebScanSteps_meta c U n_max (fs.dirtyBuckets fs.dirtyIdx) θ 16 fs).1
        split_ifs <;> exact hm
      · rw [ite_eq_right hcs]
    · rw [ite_eq_right hd]
  rw [ite_eq_right hs2]
  by_cases hs3 : fs.rebStage = 3
  · rw [ite_eq_left hs3]; dsimp only [epochTickStage3]
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt]
      cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · dsimp only; split_ifs <;> rfl
      · rename_i p; rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> rfl
    · rw [ite_eq_right hlt]
  rw [ite_eq_right hs3]
  by_cases hs4 : fs.rebStage = 4
  · rw [ite_eq_left hs4]; rfl
  rw [ite_eq_right hs4]

private theorem tickStage_rollover_itemAlloc_zero {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    (hs5 : (epochTickStage c U n_max θ fs).rebStage = 5) :
    let fs1 := epochTickStage c U n_max θ fs
    (fs1.buf (1 - fs1.curEp)).itemAlloc = 0 := by
  dsimp only [epochTickStage] at hs5 ⊢
  by_cases h0 : fs.rebStage = 0
  · rw [ite_eq_left h0] at hs5; dsimp only [epochTickStage0] at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt] at hs5
      cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
      · rename_i p; rcases p with ⟨_, _⟩
        rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
    · rw [ite_eq_right hlt] at hs5; cases hs5
  rw [ite_eq_right h0] at hs5 ⊢
  by_cases h1 : fs.rebStage = 1
  · rw [ite_eq_left h1] at hs5; dsimp only [epochTickStage1, epochTickStage1Finish] at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt] at hs5
      by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone] at hs5
        cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · rw [hchk] at hs5; dsimp only at hs5; split_ifs at hs5 <;> cases hs5
        · rename_i p; rcases p with ⟨_, _⟩
          rw [hchk] at hs5; dsimp only at hs5; split_ifs at hs5 <;> cases hs5
      · rw [ite_eq_right hdone] at hs5
        cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
        · rw [hchk] at hs5; exact absurd hs5 hne5
        · rename_i p; rcases p with ⟨_, _⟩
          rw [hchk] at hs5; dsimp only at hs5
          split_ifs at hs5 <;> exact absurd hs5 hne5
    · rw [ite_eq_right hlt] at hs5; split_ifs at hs5 <;> cases hs5
  rw [ite_eq_right h1] at hs5 ⊢
  by_cases h2 : fs.rebStage = 2
  · rw [ite_eq_left h2] at hs5
    unfold epochTickStage2 epochTickStage2PostScan epochTickStage2AfterSwap
      epochTickStage2Swap at hs5
    dsimp only at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hd : fs.dirtyIdx < fs.dirtyCount
    · rw [ite_eq_left hd] at hs5
      by_cases hcs : fs.rebCandSalt < sMaxWhp c n_max
      · rw [ite_eq_left hcs] at hs5
        have hm := (rebScanSteps_meta c U n_max (fs.dirtyBuckets fs.dirtyIdx) θ 16 fs).2.2.2.1
        have hne5' :
            (rebScanSteps c U n_max θ (fs.dirtyBuckets fs.dirtyIdx) 16 fs).rebStage ≠ 5 := by
          omega
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5'
      · rw [ite_eq_right hcs] at hs5; exact absurd hs5 hne5
    · rw [ite_eq_right hd] at hs5; cases hs5
  rw [ite_eq_right h2] at hs5 ⊢
  by_cases h3 : fs.rebStage = 3
  · rw [ite_eq_left h3] at hs5; dsimp only [epochTickStage3] at hs5
    have hne5 : fs.rebStage ≠ 5 := by omega
    by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
    · rw [ite_eq_left hlt] at hs5
      cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor
      · rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
      · rename_i p; rcases p with ⟨_, _⟩
        rw [hchk] at hs5; dsimp only at hs5
        split_ifs at hs5 <;> first | cases hs5 | exact absurd hs5 hne5
    · rw [ite_eq_right hlt] at hs5; cases hs5
  rw [ite_eq_right h3] at hs5 ⊢
  by_cases h4 : fs.rebStage = 4
  · rw [ite_eq_left h4] at hs5 ⊢; dsimp only [epochTickStage4] at hs5 ⊢
    by_cases hle8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
    · have hbo := hc.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left h4] at hbo
      have hia0 := (hbo.2.1.clearSteps_spec (cTabWhp c) (bCharWhp n_max) 8 hle8).2.2
      change (Function.update fs.buf fs.oldEp (bufClearSteps 8 (fs.buf fs.oldEp))
        fs.oldEp).itemAlloc = 0
      rw [Function.update_self]; exact hia0
    · rw [decide_eq_false hle8, ite_eq_right Bool.false_ne_true] at hs5; cases hs5
  rw [ite_eq_right h4] at hs5 ⊢
  have hbo := hc.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_right h4] at hbo
  exact hbo.2.2.2

theorem epochTick_clean_or_clock {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {W_keys BadIns : Finset (Fin U)} {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hv' : ValidFastState c U V n_max θ fs' dict)
    (htick : epochTick c U n_max θ fs = some fs') :
    CleanWindowFast c U V n_max θ W_keys BadIns fs' dict ∨
    (fs'.epochClock = fs.epochClock + 1 ∧ fs.epochClock + 1 < qEpochWhp n_max) := by
  unfold epochTick at htick
  have hclk1 := tickStage_epochClock c U n_max θ fs
  dsimp only [epochTickRollover] at htick
  split_ifs at htick with hroll hs5 <;> cases htick
  · exact Or.inl (CleanWindowFast.of_clean_fast hv'
      (tickStage_rollover_itemAlloc_zero hc hs5) rfl (fun h => by cases h))
  · exact Or.inr ⟨congrArg (· + 1) hclk1, by omega⟩

theorem fastDelete_epochClock (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (u : Fin U) :
    (fastDelete c U n_max θ fs u).epochClock = fs.epochClock := by
  dsimp only [fastDelete]
  refine (overmarsStep_meta c U n_max _ θ _).1.trans ?_
  cases fastFindLoc c U n_max θ fs u with
  | none => rfl
  | some loc_del =>
    dsimp only [fastDeleteShrink, fastDeleteMoveLast, fastDeleteRemove]
    by_cases hlt : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
        - 1 <;> [rw [ite_eq_left hlt]; rw [ite_eq_right hlt]]

theorem fastInsert_epochClock {c U n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs1 : FastState} {u : Fin U} {v : ℕ}
    (hins : fastInsert c U n_max θ fs u v = some fs1) :
    fs1.epochClock = fs.epochClock := by
  unfold fastInsert fastInsertAlloc fastInsertFresh at hins
  dsimp only at hins
  cases hfl : fastFindLoc c U n_max θ fs u with
  | some loc =>
    rw [hfl] at hins; dsimp only at hins
    injection hins with h1; rw [← h1]
    exact (overmarsStep_meta c U n_max _ θ _).1
  | none =>
    rw [hfl] at hins; dsimp only at hins
    set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    by_cases hg1 : totalLocalCoordsWhp n_max ≤ fs.bktCount b ∨
        (capFrontWhp n_max ≤ fs.bktCount b ∧ fs.poolFreeTop = 0)
    · rw [ite_eq_left hg1] at hins; cases hins
    rw [ite_eq_right hg1] at hins
    by_cases hg2 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
          (fpReducedKey c U n_max θ.2 u)).isSome = true ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp)
            (fpReducedKey c U n_max θ.2 u)).isSome = true)
    · rw [ite_eq_left hg2] at hins; cases hins
    rw [ite_eq_right hg2] at hins
    by_cases hg3 : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true ∧
        (!bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
          (fpReducedKey c U n_max θ.2 u)) = true ∧
        2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
    · rw [ite_eq_left hg3] at hins; cases hins
    rw [ite_eq_right hg3] at hins
    injection hins with h1; rw [← h1]
    refine (overmarsStep_meta c U n_max _ θ _).1.trans ?_
    by_cases hfpc : (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)).isSome = true
    · rw [ite_eq_left hfpc]
    · rw [ite_eq_right hfpc]

theorem trySelfHeal_clean {c U V n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    {θ : SeedWhp c U n_max} {W_keys BadIns : Finset (Fin U)}
    {csr : CsrState} {dict : State U}
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    (hgood : GoodSeedOnState c U n_max θ dict) :
    ∃ fs', trySelfHeal c U n_max θ csr = .fast fs' ∧
      CleanWindowFast c U V n_max θ W_keys BadIns fs' dict := by
  obtain ⟨hv, hclean⟩ := trySelfHeal_spec hth hcsr hqv
  obtain ⟨fs', hst', hb0, _, hep0, hclk0, hstg5⟩ := hclean hgood
  rw [hst'] at hv
  refine ⟨fs', hst', CleanWindowFast.of_clean_fast hv ?_ hclk0 (by omega)⟩
  rw [hep0, hb0]; rfl

end Cslib.DataStructure.Dictionary.SuccinctWhp

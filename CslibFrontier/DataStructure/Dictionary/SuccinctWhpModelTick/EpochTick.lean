/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Stage01
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Stage2
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Stage34
import Mathlib.Tactic.Positivity

/-!
# Global Epoch-Tick and Rollover Specification (`epochTick_spec`)

Combines Stages `0 .. 5` (`Stage01`, `Stage2`, `Stage34`) with epoch rollover (`epochTickRollover`)
to prove `epochTick_spec` [BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.epochTick_spec`: restores full `ValidFastState` from
  `CoreFastInv` + `OvermarsBucketInv` + `ValidEpochStagePreTick` whenever `epochTick` returns
  `some fs'`.

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

/-- `epochTick` restores full `ValidFastState` from `CoreFastInv` + `OvermarsBucketInv` +
`ValidEpochStagePreTick` whenever `epochTick` returns `some fs'`. -/
theorem epochTick_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (htick : epochTick c U n_max θ fs = some fs') :
    ValidFastState c U V n_max θ fs' dict := by
  unfold epochTick at htick
  set fs1 := epochTickStage c U n_max θ fs
  have hst1 :
      CoreFastInv c U V n_max θ fs1 dict ∧
      (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
      ValidEpochStage c U n_max θ fs1 ∧
      fs1.epochClock = fs.epochClock := by
    dsimp only [fs1, epochTickStage]
    by_cases hs0 : fs.rebStage = 0
    · rw [ite_eq_left hs0]; exact epochTickStage0_spec hc hom hs0 hpre
    rw [ite_eq_right hs0]
    by_cases hs1 : fs.rebStage = 1
    · rw [ite_eq_left hs1]; exact epochTickStage1_spec hc hom hs1 hpre
    rw [ite_eq_right hs1]
    by_cases hs2 : fs.rebStage = 2
    · rw [ite_eq_left hs2]; exact epochTickStage2_spec hc hom hs2 hpre
    rw [ite_eq_right hs2]
    by_cases hs3 : fs.rebStage = 3
    · rw [ite_eq_left hs3]; exact epochTickStage3_spec hc hom hs3 hpre
    rw [ite_eq_right hs3]
    by_cases hs4 : fs.rebStage = 4
    · rw [ite_eq_left hs4]; exact epochTickStage4_spec hc hom hs4
    rw [ite_eq_right hs4]
    have hs5 : fs.rebStage = 5 := by have := hc.rebStage_le; omega
    exact ⟨hc, hom, by simp [ValidEpochStage, hs5], rfl⟩
  obtain ⟨hc1, hom1, hstg1, _⟩ := hst1
  dsimp only [epochTickRollover] at htick
  by_cases hroll : qEpochWhp n_max ≤ fs1.epochClock + 1
  · rw [ite_eq_left hroll] at htick
    by_cases hs5 : fs1.rebStage = 5
    · rw [ite_eq_left hs5] at htick
      injection htick with hfs'
      rw [← hfs']
      have hq_pos : 0 < qEpochWhp n_max := by
        unfold qEpochWhp; have := slabScale_pos n_max; positivity
      have hbo1 := hc1.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs1.rebStage ≤ 3)),
        ite_eq_right (by omega : ¬(fs1.rebStage = 4))] at hbo1
      obtain ⟨hno_old1, hv_old1, hna1, hia0⟩ := hbo1
      have hcur'_or : (1 - fs1.curEp) = 0 ∨ (1 - fs1.curEp) = 1 :=
        FastState.oldEp_or hc1.curEp_or
      have hold'_eq : ({ fs1 with
          curEp := 1 - fs1.curEp
          epochClock := 0
          rebStage := 0
          stageCursor := 0 } : FastState).oldEp = fs1.curEp := by
        dsimp only [FastState.oldEp]
        rcases hc1.curEp_or with h | h <;> simp [h]
      have hinL_roll : ∀ (df : ℕ → ℕ) b st,
          inLiveTree 0 fs1.curEp (df b) st = inLiveTree 5 fs1.oldEp (df b) st := by
        intro _ _ _; simp [inLiveTree]
      refine CoreFastInv.toValidFastState ?_ ?_ ?_
      · exact
          { hth := hc1.hth
            curEp_or := hcur'_or
            epochClock_lt := hq_pos
            rebStage_le := Nat.zero_le 5
            rebCollision_zero := hc1.rebCollision_zero
            qv_global := hc1.qv_global
            bktCount_le := hc1.bktCount_le
            bktCount_ge_zero := hc1.bktCount_ge_zero
            locState_active := hc1.locState_active
            locState_inactive := hc1.locState_inactive
            active_item := hc1.active_item
            quot_inj := hc1.quot_inj
            dict_map := hc1.dict_map
            poolFreeTop_le := hc1.poolFreeTop_le
            backPtr_valid := hc1.backPtr_valid
            freeStack_lt := hc1.freeStack_lt
            backPtr_inj := hc1.backPtr_inj
            freeStack_inj := hc1.freeStack_inj
            back_free_disj := hc1.back_free_disj
            pool_conservation := hc1.pool_conservation
            roles_valid := hc1.roles_valid
            bktSalt_lt := hc1.bktSalt_lt
            live_fp_inj := fun b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
              rw [hold'_eq, hinL_roll, ← hs5] at hin₁ hin₂
              exact hc1.live_fp_inj b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
            live_valid := fun b hb => by
              obtain ⟨lm, hvl, hrl⟩ := hc1.live_valid b hb
              refine ⟨lm, hvl, hrl.congr (fun _ _ => rfl) fun loc _ => ?_⟩
              rw [hold'_eq, hinL_roll, hs5]
            rKey_buf_inj := hc1.rKey_buf_inj
            bufCur_valid := by
              change (fs1.buf fs1.oldEp).itemAlloc ≤ 2 * sMaxWhp c n_max ∧
                (fs1.buf fs1.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs1.buf fs1.oldEp).itemAlloc ∧
                ∃ curMap,
                  ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf fs1.oldEp) curMap ∧
                  BufMapRel (numBucketsWhp n_max) (2 + fs1.oldEp) fs1.bktCount fs1.locState
                    (fs1.rKeyAt c U n_max θ) curMap
              rw [hna1, hia0]
              exact ⟨Nat.zero_le _, by omega, fun _ => none, hv_old1,
                BufMapRel.empty_of_not _ _ _ _ _ hno_old1⟩
            bufOld_valid := by
              rw [hold'_eq, ite_eq_left (Nat.zero_le 3)]
              exact hc1.bufCur_valid }
      · intro b hb
        rcases hom1 b hb with ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
        · exact Or.inl ⟨ha0, hlt5⟩
        · refine Or.inr ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO,
            hrO.congr (fun _ _ => rfl) fun loc _ => ?_⟩
          rw [hold'_eq, hinL_roll, hs5]
      · dsimp only [ValidEpochStage]
        simp only [↓reduceIte]
        exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · rw [ite_eq_right hs5] at htick; cases htick
  · rw [ite_eq_right hroll] at htick
    injection htick with hfs'
    rw [← hfs']
    exact CoreFastInv.toValidFastState
      { hc1 with epochClock_lt := Nat.lt_of_not_le hroll } hom1 hstg1


end Cslib.DataStructure.Dictionary.SuccinctWhp

end

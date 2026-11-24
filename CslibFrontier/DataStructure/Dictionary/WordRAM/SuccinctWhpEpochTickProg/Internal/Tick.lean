/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Stage0
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Stage1
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Stage2
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Stage3
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Stage4
import CslibFrontier.Tactic.Realize

/-!
# Combined Stage Dispatcher, Epoch Rollover, and `epochTickGenProg`

Dispatches Stages `0 .. 5` via `epochTickStageAllGenProg`, executes epoch-clock rollover via
`epochTickRolloverGenProg`, and proves `realizes_epochTickGen`, `epochTickGenProg_fastStep`, and
`epochTick_isSome_iff`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

attribute [local simp] clientResult_pure_whp clientState_pure_whp

private theorem stage1Finish_preserve (fs0 s0 : FastState) (h1 : s0.curEp = fs0.curEp)
    (h2 : s0.epochClock = fs0.epochClock) (_h3 : s0.rebStage ≤ 3) :
    (epochTickStage1Finish s0).curEp = fs0.curEp ∧
    (epochTickStage1Finish s0).epochClock = fs0.epochClock ∧
    (epochTickStage1Finish s0).rebStage ≤ 3 := by
  dsimp only [epochTickStage1Finish]
  split_ifs <;> exact ⟨h1, h2, by dsimp only; omega⟩

private theorem stage1CursorTail_preserve (fs sMid : FastState)
    (h1 : sMid.curEp = fs.curEp) (h2 : sMid.epochClock = fs.epochClock)
    (h3 : sMid.rebStage ≤ 3) :
    let fsW : FastState := { sMid with stageCursor := fs.stageCursor + 1 }
    let out := if (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1 then
      epochTickStage1Finish fsW else fsW
    out.curEp = fs.curEp ∧ out.epochClock = fs.epochClock ∧ out.rebStage ≤ 3 := by
  dsimp only
  by_cases hd : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
  · rw [ite_eq_left hd]; exact stage1Finish_preserve fs _ h1 h2 h3
  · rw [ite_eq_right hd]; exact ⟨h1, h2, h3⟩

private theorem tickStageAllPure_clk_and_stage5 (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    {fs : FastState} (hst_le : fs.rebStage ≤ 5) :
    let fs1 := epochTickStage c U n_max θ fs
    fs1.curEp = fs.curEp ∧
    fs1.epochClock = fs.epochClock ∧
    (fs1.rebStage = 5 ↔
      fs.rebStage = 5 ∨ (fs.rebStage = 4 ∧ (fs.buf fs.oldEp).nodeAlloc ≤ 8)) := by
  dsimp only [epochTickStage]
  by_cases hs0 : fs.rebStage = 0
  · rw [ite_eq_left hs0]
    have hclk : (epochTickStage0 fs).curEp = fs.curEp ∧
        (epochTickStage0 fs).epochClock = fs.epochClock ∧
        (epochTickStage0 fs).rebStage ≤ 1 := by
      dsimp only [epochTickStage0]
      by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
      · rw [ite_eq_left hlt]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor <;>
          (dsimp only; split_ifs <;> exact ⟨rfl, rfl, by dsimp only; omega⟩)
      · rw [ite_eq_right hlt]; exact ⟨rfl, rfl, by dsimp only; omega⟩
    exact ⟨hclk.1, hclk.2.1, by omega⟩
  rw [ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1]
    have hclk : (epochTickStage1 fs).curEp = fs.curEp ∧
        (epochTickStage1 fs).epochClock = fs.epochClock ∧
        (epochTickStage1 fs).rebStage ≤ 3 := by
      dsimp only [epochTickStage1]
      by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
      · rw [ite_eq_left hlt]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
        | none => exact stage1CursorTail_preserve fs fs rfl rfl (by omega)
        | some p =>
          rcases p with ⟨b, _⟩; dsimp only
          by_cases hq : fs.rebQueued b = 0
          · rw [ite_eq_left hq]
            exact stage1CursorTail_preserve fs
              { fs with
                rebQueued := Function.update fs.rebQueued b 1
                dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b
                dirtyCount := fs.dirtyCount + 1 } rfl rfl (by dsimp only; omega)
          · rw [ite_eq_right hq]
            exact stage1CursorTail_preserve fs fs rfl rfl (by omega)
      · rw [ite_eq_right hlt]; exact stage1Finish_preserve fs fs rfl rfl (by omega)
    exact ⟨hclk.1, hclk.2.1, by omega⟩
  rw [ite_eq_right hs1]
  by_cases hs2 : fs.rebStage = 2
  · rw [ite_eq_left hs2]
    have hclk : (epochTickStage2 c U n_max θ fs).curEp = fs.curEp ∧
        (epochTickStage2 c U n_max θ fs).epochClock = fs.epochClock ∧
        (epochTickStage2 c U n_max θ fs).rebStage ≤ 3 := by
      dsimp only [epochTickStage2]
      by_cases h1 : fs.dirtyIdx < fs.dirtyCount
      · rw [ite_eq_left h1]
        by_cases h2 : fs.rebCandSalt < sMaxWhp c n_max
        · rw [ite_eq_left h2]
          set b := fs.dirtyBuckets fs.dirtyIdx
          have hp := rebScanSteps_preserved θ b 16 fs
          unfold epochTickStage2PostScan epochTickStage2AfterSwap epochTickStage2Swap
          dsimp only
          split_ifs
          · exact ⟨hp.curEp, hp.epochClock, by rw [hp.rebStage]; omega⟩
          · exact ⟨hp.curEp, hp.epochClock, le_rfl⟩
          · exact ⟨hp.curEp, hp.epochClock, by rw [hp.rebStage]; omega⟩
          · exact ⟨hp.curEp, hp.epochClock, by rw [hp.rebStage]; omega⟩
        · rw [ite_eq_right h2]; exact ⟨rfl, rfl, by omega⟩
      · rw [ite_eq_right h1]; exact ⟨rfl, rfl, le_rfl⟩
    exact ⟨hclk.1, hclk.2.1, by omega⟩
  rw [ite_eq_right hs2]
  by_cases hs3 : fs.rebStage = 3
  · rw [ite_eq_left hs3]
    have hclk : (epochTickStage3 c U n_max θ fs).curEp = fs.curEp ∧
        (epochTickStage3 c U n_max θ fs).epochClock = fs.epochClock ∧
        (epochTickStage3 c U n_max θ fs).rebStage ≤ 4 := by
      dsimp only [epochTickStage3]
      by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
      · rw [ite_eq_left hlt]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor <;>
          dsimp only <;> split_ifs <;> exact ⟨rfl, rfl, by dsimp only; omega⟩
      · rw [ite_eq_right hlt]; exact ⟨rfl, rfl, by dsimp only; omega⟩
    exact ⟨hclk.1, hclk.2.1, by omega⟩
  rw [ite_eq_right hs3]
  by_cases hs4 : fs.rebStage = 4
  · rw [ite_eq_left hs4]
    dsimp only [epochTickStage4]
    refine ⟨rfl, rfl, ?_⟩
    by_cases h8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
    · rw [decide_eq_true h8]; simp [hs4, h8]
    · rw [decide_eq_false h8]; simp [hs4, h8]
  rw [ite_eq_right hs4]
  have hs5 : fs.rebStage = 5 := by omega
  exact ⟨rfl, rfl, by simp [hs5]⟩

/-- For every `fs` with `fs.rebStage ≤ 5`, `(epochTick c U n_max θ fs).isSome` equals
`epochTickWillSucceed n_max fs`. -/
theorem epochTick_isSome_iff {c U n_max : ℕ} (θ : SeedWhp c U n_max) {fs : FastState}
    (hst_le : fs.rebStage ≤ 5) :
    (epochTick c U n_max θ fs).isSome = epochTickWillSucceed n_max fs := by
  unfold epochTick
  obtain ⟨_, hclk, hs5_iff⟩ := tickStageAllPure_clk_and_stage5 c U n_max θ hst_le
  dsimp only [epochTickRollover, epochTickWillSucceed]
  rw [hclk]
  by_cases hlt : fs.epochClock + 1 < qEpochWhp n_max
  · rw [ite_eq_right (Nat.not_le.mpr hlt), decide_eq_true (Or.inl hlt)]; rfl
  · rw [ite_eq_left (Nat.le_of_not_lt hlt)]
    by_cases hs5 : (epochTickStage c U n_max θ fs).rebStage = 5
    · rw [ite_eq_left hs5, decide_eq_true (Or.inr (hs5_iff.mp hs5))]; rfl
    · rw [ite_eq_right hs5, decide_eq_false (fun h => h.elim hlt (fun h' => hs5 (hs5_iff.mpr h')))]
      rfl

/-- Dispatch Stages `0 .. 5` of `epochTick` (`d = (wp, base)`). -/
@[irreducible] private def epochTickStageAllGenProg :
    WhpParams × ℕ → Memory.Prog Unit
  | (wp, base) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let z3 ← pure 3
    let z4 ← pure 4
    let stg ← readHdrProg (base, hdrRebStage)
    if stg = z0 then
      epochTickStage0GenProg (wp.1, base)
    else if stg = z1 then
      epochTickStage1GenProg (wp.1, base)
    else if stg = z2 then
      epochTickStage2GenProg (wp, base)
    else if stg = z3 then
      epochTickStage3GenProg (wp, base)
    else if stg = z4 then
      epochTickStage4GenProg (wp.1, base)
    else
      pure ()

private theorem realizes_epochTickStageAllGen :
    Realizes .exact epochTickStageAllGenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (wp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          ValidEpochStagePreTick c U n_max θ fs)
      (fun _ _ => 0) := by
  unfold epochTickStageAllGenProg
  have hrh := realizes_readHdr
  have hs0 := realizes_epochTickStage0Gen
  have hs1 := realizes_epochTickStage1Gen
  have hs2 := realizes_epochTickStage2Gen
  have hs3 := realizes_epochTickStage3Gen
  have hs4 := realizes_epochTickStage4Gen
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hcore, hpre⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hh := fastMemHdrs hrep
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    rw [hh.rebStage] at hst_res
    simp only [hcp_eq] at *
    simp only [hst_st, hst_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrRebStage]; omega)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hrep, hcore, by assumption⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hcore, hpre, by assumption⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hcore, by assumption⟩
  )

private theorem epochTickStageAllGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStageAllGenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2 * cTabWhp c + 32 * hashEvalCostWhp c + 43950 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage c U n_max θ fs) s s' := by
  have hth := henv.2.2.2.1
  have hh := fastMemHdrs hrep
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (by dsimp [hdrRebStage]; omega) (s := s)
  rw [hh.rebStage] at hst_res
  dsimp only
  unfold epochTickStageAllGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  dsimp only [epochTickStage]
  by_cases hs0 : fs.rebStage = 0
  · rw [ite_eq_left hs0]
    obtain ⟨hmc0, hvp0, hstep0⟩ :=
      epochTickStage0GenProg_fastStep henv hcore hs0 hseed hrep (s := s)
    rw [clientState_bind, hst_st, hst_res, ite_eq_left hs0]
    refine ⟨?_, ?_, hstep0⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_left hs0]
      dsimp only [cp] at hmc0 ⊢; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res, ite_eq_left hs0]; exact hvp0
  rw [ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1]
    obtain ⟨hmc1, hvp1, hstep1⟩ :=
      epochTickStage1GenProg_fastStep henv hcore hpre hs1 hseed hrep (s := s)
    rw [clientState_bind, hst_st, hst_res, ite_eq_right hs0, ite_eq_left hs1]
    refine ⟨?_, ?_, hstep1⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_right hs0, ite_eq_left hs1]
      dsimp only [cp] at hmc1 ⊢; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res, ite_eq_right hs0, ite_eq_left hs1]
      exact hvp1
  rw [ite_eq_right hs1]
  by_cases hs2 : fs.rebStage = 2
  · rw [ite_eq_left hs2]
    obtain ⟨hmc2, hvp2, hstep2⟩ :=
      epochTickStage2GenProg_fastStep henv hcore hpre hs2 hseed hrep (s := s)
    rw [clientState_bind, hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2]
    refine ⟨?_, ?_, hstep2⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2]; omega
    · refine validProg_bind hst_vp ?_
      rw [hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1, ite_eq_left hs2]; exact hvp2
  rw [ite_eq_right hs2]
  by_cases hs3 : fs.rebStage = 3
  · rw [ite_eq_left hs3]
    obtain ⟨hmc3, hvp3, hstep3⟩ :=
      epochTickStage3GenProg_fastStep henv hcore hs3 hseed hrep (s := s)
    rw [clientState_bind, hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1,
      ite_eq_right hs2, ite_eq_left hs3]
    refine ⟨?_, ?_, hstep3⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2,
        ite_eq_left hs3]; omega
    · refine validProg_bind hst_vp ?_
      rw [hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2, ite_eq_left hs3]
      exact hvp3
  rw [ite_eq_right hs3]
  by_cases hs4 : fs.rebStage = 4
  · rw [ite_eq_left hs4]
    obtain ⟨hmc4, hvp4, hstep4⟩ :=
      epochTickStage4GenProg_fastStep henv hcore hs4 hseed hrep (s := s)
    rw [clientState_bind, hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1,
      ite_eq_right hs2, ite_eq_right hs3, ite_eq_left hs4]
    refine ⟨?_, ?_, hstep4⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2,
        ite_eq_right hs3, ite_eq_left hs4]
      dsimp only [cp] at hmc4 ⊢; omega
    · refine validProg_bind hst_vp ?_
      rw [hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2,
        ite_eq_right hs3, ite_eq_left hs4]
      exact hvp4
  rw [ite_eq_right hs4]
  rw [clientState_bind, hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1,
    ite_eq_right hs2, ite_eq_right hs3, ite_eq_right hs4]
  refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst_st, hst_res, hst_mc, ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2,
      ite_eq_right hs3, ite_eq_right hs4, memoryCost_pure]; omega
  · refine validProg_bind hst_vp ?_
    rw [hst_st, hst_res, ite_eq_right hs0, ite_eq_right hs1, ite_eq_right hs2,
      ite_eq_right hs3, ite_eq_right hs4]
    exact validProg_pure _

/-- Execute the epoch-clock increment / rollover of `epochTick` when rollover is known to succeed
(`d = (cp, base)`). -/
@[irreducible] private def epochTickRolloverGenProg :
    WhpCoreParams × ℕ → Memory.Prog Unit
  | (cp, base) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let clk ← readHdrProg (base, hdrEpochClock)
    let nextClk ← pure (clk + z1)
    let qEp ← pure (wpQEpoch cp)
    if qEp ≤ nextClk then
      let cur ← readHdrProg (base, hdrCurEp)
      let newCur ← pure (z1 - cur)
      writeHdrProg ((base, hdrCurEp), newCur)
      writeHdrProg ((base, hdrEpochClock), z0)
      writeHdrProg ((base, hdrRebStage), z0)
      writeHdrProg ((base, hdrStageCursor), z0)
    else
      writeHdrProg ((base, hdrEpochClock), nextClk)

private theorem realizes_epochTickRolloverGen :
    Realizes .exact epochTickRolloverGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs1 : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs1 s.mem ∧
          (fs1.curEp = 0 ∨ fs1.curEp = 1) ∧
          fs1.epochClock < qEpochWhp n_max)
      (fun _ _ => 0) := by
  unfold epochTickRolloverGenProg
  have hrh := realizes_readHdr
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs1, henv, rfl, hrep, hce_or, hclk_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hh := fastMemHdrs hrep
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨hck_st, hck_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrEpochClock)
      (by dsimp [hdrEpochClock]; omega) (s := s)
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hh.epochClock] at hck_res
    rw [hh.curEp] at hce_res
    simp only [hck_st, hck_res, hce_st, hce_res] at *
    first
    | (rcases hce_or with h01 | h01 <;> omega)
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr
        (by dsimp [hdrEpochClock, hdrCurEp, hdrRebStage, hdrStageCursor]; omega)
    | exact henv.fits_of_le_n_max (by omega)
  )

private theorem epochTickRolloverGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs1 : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (_hce_or : fs1.curEp = 0 ∨ fs1.curEp = 1)
    (hclk_lt : fs1.epochClock < qEpochWhp n_max)
    (hroll_ok : qEpochWhp n_max ≤ fs1.epochClock + 1 → fs1.rebStage = 5)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs1 s.mem) :
    let prog := epochTickRolloverGenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    ∃ fs',
      epochTickRollover n_max fs1 = some fs' ∧
      memoryCost prog s ≤ 10 ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      FastStateStep base c U V w n_max θ fs' s s' := by
  have _ := hclk_lt
  have hth := henv.2.2.2.1
  have hh := fastMemHdrs hrep
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  have hq_cp : wpQEpoch cp = qEpochWhp n_max := wp_large_qEpoch hth
  obtain ⟨hck_st, hck_res, hck_mc, hck_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrEpochClock)
    (by dsimp [hdrEpochClock]; omega) (s := s)
  rw [hh.epochClock] at hck_res
  dsimp only
  unfold epochTickRolloverGenProg; simp only [pure_bind, hq_cp]
  dsimp only [epochTickRollover]
  by_cases hroll : qEpochWhp n_max ≤ fs1.epochClock + 1
  · rw [ite_eq_left hroll, ite_eq_left (hroll_ok hroll)]
    obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hh.curEp] at hce_res
    have hfit_new : Fits w (1 - fs1.curEp) :=
      (henv.fits_const (by decide)).of_le (Nat.sub_le 1 _)
    have hw1 := writeHdrStep (fs := fs1) henv (by dsimp [hdrCurEp]; decide) hfit_new
      (fun h6 => by dsimp [hdrCurEp] at h6; omega) hseed hrep (hdrOff := hdrCurEp)
      (val := 1 - fs1.curEp) (s := s)
    set sc1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrCurEp), 1 - fs1.curEp))
    set fs2 : FastState := { fs1 with curEp := 1 - fs1.curEp }
    have hw2 := writeHdrZeroStep (fs := fs2) henv (by dsimp [hdrEpochClock]; decide)
      hw1.2.2.2.1 hw1.2.2.2.2.1 (hdrOff := hdrEpochClock) (s := sc1)
    set sc2 := (Memory.spec 0).clientState sc1 (writeHdrProg ((base, hdrEpochClock), 0))
    set fs3 : FastState := { fs2 with epochClock := 0 }
    have hw3 := writeHdrZeroStep (fs := fs3) henv (by dsimp [hdrRebStage]; decide)
      hw2.2.2.2.1 hw2.2.2.2.2.1 (hdrOff := hdrRebStage) (s := sc2)
    set sc3 := (Memory.spec 0).clientState sc2 (writeHdrProg ((base, hdrRebStage), 0))
    set fs4 : FastState := { fs3 with rebStage := 0 }
    have hw4 := writeHdrZeroStep (fs := fs4) henv (by dsimp [hdrStageCursor]; decide)
      hw3.2.2.2.1 hw3.2.2.2.2.1 (hdrOff := hdrStageCursor) (s := sc3)
    have hwc := seqUnitProg_fastStep hw1 (seqUnitProg_fastStep hw2 (seqUnitProg_fastStep hw3 hw4))
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hck_st, hck_res, hck_mc, ite_eq_left hroll]; simp only [memoryCost_bind]
      rw [hce_st, hce_res, hce_mc]
      have hwm := hwc.1
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind] at hwm; omega
    · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_left hroll]
      refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
      exact hwc.2.1
    · rw [clientState_bind, hck_st, hck_res, ite_eq_left hroll,
        clientState_bind, hce_st, hce_res]
      exact hwc.2.2
  · rw [ite_eq_right hroll]
    have hw := writeHdrStep (fs := fs1) henv (by dsimp [hdrEpochClock]; decide)
      (henv.fits_of_le_n_max (by omega)) (fun h6 => by dsimp [hdrEpochClock] at h6; omega)
      hseed hrep (hdrOff := hdrEpochClock) (val := fs1.epochClock + 1) (s := s)
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hck_st, hck_res, hck_mc, ite_eq_right hroll]; have hwm := hw.1; omega
    · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_right hroll]; exact hw.2.1
    · rw [clientState_bind, hck_st, hck_res, ite_eq_right hroll]; exact hw.2.2

/-- Execute `epochTick` when `epochTickWillSucceed n_max fs` holds (`d = (wp, base)`). -/
@[irreducible] def epochTickGenProg : WhpParams × ℕ → Memory.Prog Unit
  | (wp, base) => do
    epochTickStageAllGenProg (wp, base)
    epochTickRolloverGenProg (wp.1, base)

/-- `Realizes .exact` certificate for `epochTickGenProg`. -/
theorem realizes_epochTickGen :
    Realizes .exact epochTickGenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (wp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          ValidEpochStagePreTick c U n_max θ fs)
      (fun _ _ => 0) := by
  unfold epochTickGenProg
  have hsa := realizes_epochTickStageAllGen
  have hro := realizes_epochTickRolloverGen
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hcore, hpre⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨_, _, hsa_step⟩ :=
      epochTickStageAllGenProg_fastStep henv hcore hpre hseed hrep (s := s)
    set fs1 := epochTickStage c U n_max θ fs
    obtain ⟨hce1, hclk_eq, _⟩ := tickStageAllPure_clk_and_stage5 c U n_max θ hcore.rebStage_le
    simp only [hcp_eq] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hcore, hpre⟩
    | exact ⟨c, U, V, w, n_max, fs1, henv, rfl, hsa_step.2.2.1,
        hce1 ▸ hcore.curEp_or, hclk_eq ▸ hcore.epochClock_lt⟩
  )

/-- `FastStateStep` specification for `epochTickGenProg`. -/
theorem epochTickGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hok : epochTickWillSucceed n_max fs = true)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickGenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    ∃ fs',
      epochTick c U n_max θ fs = some fs' ∧
      memoryCost prog s ≤ 2 * cTabWhp c + 32 * hashEvalCostWhp c + 43960 ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      FastStateStep base c U V w n_max θ fs' s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hsa_mc, hsa_vp, hsa_step⟩ :=
    epochTickStageAllGenProg_fastStep henv hcore hpre hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (epochTickStageAllGenProg (mkWhpParams c U V w n_max, base))
  set fs1 := epochTickStage c U n_max θ fs
  obtain ⟨hce1, hclk_eq, hs5_iff⟩ :=
    tickStageAllPure_clk_and_stage5 c U n_max θ hcore.rebStage_le
  have hroll_ok : qEpochWhp n_max ≤ fs1.epochClock + 1 → fs1.rebStage = 5 := by
    intro hge
    rw [hclk_eq] at hge
    dsimp only [epochTickWillSucceed] at hok
    have hdisj := of_decide_eq_true hok
    rcases hdisj with hlt | h54
    · omega
    · exact hs5_iff.mpr h54
  obtain ⟨fs', hro_eq, hro_mc, hro_vp, hro_step⟩ :=
    epochTickRolloverGenProg_fastStep (fs1 := fs1) henv (hce1 ▸ hcore.curEp_or)
      (hclk_eq ▸ hcore.epochClock_lt) hroll_ok hsa_step.2.1 hsa_step.2.2.1 (s := s1)
  unfold epochTick
  refine ⟨fs', hro_eq, ?_, ?_, ?_⟩
  · unfold epochTickGenProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1] at hsa_mc hro_mc ⊢; omega
  · unfold epochTickGenProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
    exact validProg_bind hsa_vp hro_vp
  · unfold epochTickGenProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1,
      clientState_bind]
    exact hsa_step.trans hro_step

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end

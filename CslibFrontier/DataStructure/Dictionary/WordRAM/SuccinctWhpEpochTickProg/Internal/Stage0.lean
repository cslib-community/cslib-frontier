/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Common
import CslibFrontier.Tactic.Realize

/-!
# Stage 0 of `epochTick`

Implements and verifies `epochTickStage0GenProg`, which clears per-bucket rebuild queue/done
flags (`rebQueued`, `rebDoneFlag`) across entries of `buf oldEp` and transitions to Stage 1.
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

/-- Transition to Stage 1 (`rebStage := 1, stageCursor := 0, dirtyCount := 0`). -/
@[irreducible] private def tickToStage1Prog (base : ℕ) : Memory.Prog Unit := do
  let z0 ← pure 0
  let z1 ← pure 1
  writeHdrProg ((base, hdrRebStage), z1)
  writeHdrProg ((base, hdrStageCursor), z0)
  writeHdrProg ((base, hdrDirtyCount), z0)

private theorem realizes_tickToStage1 :
    Realizes .exact tickToStage1Prog
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w base _ => 0 < w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold tickToStage1Prog
  realize [realizes_writeHdr]
  all_goals first
    | exact Nat.one_lt_two_pow h.1.ne'
    | exact h.2.of_le (by dsimp [hdrRebStage, hdrStageCursor, hdrDirtyCount]; omega)

private theorem tickToStage1Prog_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := tickToStage1Prog base
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 3 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with rebStage := 1, stageCursor := 0, dirtyCount := 0 } s s' := by
  have h1 := writeHdrStep (fs := fs) henv (by dsimp [hdrRebStage]; decide)
    (henv.fits_const (by decide)) (fun h => by dsimp [hdrRebStage] at h; omega) hseed hrep
    (hdrOff := hdrRebStage) (val := 1) (s := s)
  have h2 := writeHdrZeroStep henv (by decide)
    h1.2.2.2.1 h1.2.2.2.2.1 (hdrOff := hdrStageCursor)
  have h3 := writeHdrZeroStep henv (by decide)
    h2.2.2.2.1 h2.2.2.2.2.1 (hdrOff := hdrDirtyCount)
  unfold tickToStage1Prog
  simp only [pure_bind]
  exact seqUnitProg_fastStep h1 (seqUnitProg_fastStep h2 h3)

/-- Stage 0 `some (b, _)` helper: clear `rebQueued b := 0` and `rebDoneFlag b := 0`
(`d = ((cp, base), b)`). -/
@[irreducible] private def stage0ClearBucketFlagsProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let f9 ← pure 9
    let f8 ← pure 8
    writeBktFieldGenProg ((((cp, base), b), f9), z0)
    writeBktFieldGenProg ((((cp, base), b), f8), z0)

private theorem realizes_stage0ClearBucketFlags :
    Realizes .exact stage0ClearBucketFlagsProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold stage0ClearBucketFlagsProg
  realize [realizes_writeBktFieldGen]
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, _, n_max, henv, rfl⟩, hb⟩ := h
    cases henv.2.2.1
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem stage0ClearBucketFlagsProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage0ClearBucketFlagsProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 10 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        rebQueued := Function.update fs.rebQueued b 0
        rebDoneFlag := Function.update fs.rebDoneFlag b 0 } s s' := by
  have hw1 := writeBktFieldGenProg_fastStep henv hb (by decide : 9 < 10) (Nat.zero_le _)
    hseed hrep (s := s)
  simp only [setBktField] at hw1
  have hw2 := writeBktFieldGenProg_fastStep henv hb (by decide : 8 < 10) (Nat.zero_le _)
    hw1.2.2.2.1 hw1.2.2.2.2.1
  simp only [setBktField] at hw2
  unfold stage0ClearBucketFlagsProg; simp only [pure_bind]
  have hseq := seqUnitProg_fastStep ⟨hw1.1.le, hw1.2⟩ ⟨hw2.1.le, hw2.2⟩
  exact ⟨by have := hseq.1; omega, hseq.2.1, hseq.2.2⟩

/-- Execute Stage 0 of `epochTick` (`d = (cp, base)`). -/
@[irreducible] def epochTickStage0GenProg :
    WhpCoreParams × ℕ → Memory.Prog Unit
  | (cp, base) => do
    let z1 ← pure 1
    let oldEp ← readOldEpProg base
    let allocs ← readBufAllocsProg (base, oldEp)
    let ia ← pure allocs.2
    let sc ← readHdrProg (base, hdrStageCursor)
    if sc < ia then
      let cs ← bufCheckSlotGenProg (((cp, base), oldEp), sc)
      let nextCur ← pure (sc + 1)
      if cs.1 = z1 then
        stage0ClearBucketFlagsProg ((cp, base), slotCheckBucket cs)
        if ia ≤ nextCur then
          tickToStage1Prog base
        else
          writeHdrProg ((base, hdrStageCursor), nextCur)
      else
        if ia ≤ nextCur then
          tickToStage1Prog base
        else
          writeHdrProg ((base, hdrStageCursor), nextCur)
    else
      tickToStage1Prog base

/-- `Realizes .exact` certificate for `epochTickStage0GenProg`. -/
theorem realizes_epochTickStage0Gen :
    Realizes .exact epochTickStage0GenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          fs.rebStage = 0)
      (fun _ _ => 0) := by
  unfold epochTickStage0GenProg
  realize [realizes_readOldEp, realizes_readBufAllocs, realizes_readHdr,
    realizes_bufCheckSlotGen, realizes_stage0ClearBucketFlags,
    realizes_tickToStage1, realizes_writeHdr]
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, _, n_max, θ, fs, dict, henv, rfl, hrep, hcore, hs0⟩ := h
    cases henv.2.2.1
    have hth := henv.2.2.2.1
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
    have hbo := hcore.bufOld_valid
    rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
    obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    have hr := stageCursorReads_spec henv hcore.curEp_or hold_or hrep (s := s)
    obtain ⟨hcs_st, hcs_res, _, _⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    simp only [hr.ro_st, hr.ro_res, hr.ra_st, hr.ra_res, hr.sc_st, hr.sc_res, hcs_st] at *
    first
    | exact henv.two_le_w
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrCurEp, hdrStageCursor]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, oldMap, henv, rfl, hold_or,
        hrep.buf_rep hold_or, hv_o⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]
       cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
       | none =>
         rw [hchk] at hcs_res
         simp only [hcs_res, zero_ne_one] at *
       | some p =>
         obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
         rw [hchk] at hcs_res
         simp only [hcs_res] at *
         exact ((hrel_o.2 k p.1 p.2).mp hmk).1)
  )

private theorem stage0Tail_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs fsMid : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcur1_fit : Fits w (fs.stageCursor + 1))
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fsMid s.mem) :
    let ia := (fs.buf fs.oldEp).itemAlloc
    let nextCur := fs.stageCursor + 1
    let prog := if ia ≤ nextCur then tickToStage1Prog base else
      writeHdrProg ((base, hdrStageCursor), nextCur)
    let fsOut := if ia ≤ nextCur then
      { fsMid with rebStage := 1, stageCursor := 0, dirtyCount := 0 }
      else { fsMid with stageCursor := nextCur }
    memoryCost prog s ≤ 3 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s ((Memory.spec 0).clientState s prog) := by
  dsimp only
  by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
  · rw [ite_eq_left hdone, ite_eq_left hdone]
    exact tickToStage1Prog_fastStep (fs := fsMid) henv hseed hrep (s := s)
  · rw [ite_eq_right hdone, ite_eq_right hdone]
    have hw := writeHdrStep (fs := fsMid) henv (by dsimp [hdrStageCursor]; decide) hcur1_fit
      (fun h => by dsimp [hdrStageCursor] at h; omega) hseed hrep
      (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s)
    exact ⟨by omega, hw.2.1, hw.2.2⟩

/-- `FastStateStep` specification for `epochTickStage0GenProg`. -/
theorem epochTickStage0GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hs0 : fs.rebStage = 0)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage0GenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 30 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage0 fs) s s' := by
  have hth := henv.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hc.curEp_or with h | h <;> simp [FastState.oldEp, h]
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  have hr := stageCursorReads_spec henv hc.curEp_or hold_or hrep (s := s)
  dsimp only
  unfold epochTickStage0GenProg; simp only [pure_bind]
  dsimp only [epochTickStage0]
  set oldTr := fs.buf fs.oldEp
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    have hcur1_fit : Fits w (fs.stageCursor + 1) := henv.fits_of_le_n_max (by omega)
    set kSlot : ℕ × (ℕ × ℕ) → Memory.Prog Unit := fun cs =>
      let nextCur := fs.stageCursor + 1
      let tail := if oldTr.itemAlloc ≤ nextCur then tickToStage1Prog base
        else writeHdrProg ((base, hdrStageCursor), nextCur)
      if cs.1 = 1 then
        stage0ClearBucketFlagsProg ((cp, base), slotCheckBucket cs) >>= fun _ => tail
      else tail
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some p =>
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      obtain ⟨hcf_mc, hcf_vp, hcf_step⟩ :=
        stage0ClearBucketFlagsProg_fastStep henv (((hrel_o.2 k p.1 p.2).mp hmk).1)
          hseed hrep (s := s)
      have htail := stage0Tail_fastStep (fs := fs) henv hcur1_fit hcf_step.2.1 hcf_step.2.2.1
      refine stageSlotCheckSeq_fastStep (kSlot := kSlot) (midCost := 10) (tailCost := 3)
        hr hlt rfl hcs_st hcs_res hcs_mc hcs_vp ?_ hcf_mc hcf_vp hcf_step
        htail.1 htail.2.1 htail.2.2 (by omega)
      simp [kSlot, slotCheckBucket, cp, oldTr]
    | none =>
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      have htail := stage0Tail_fastStep (fs := fs) (fsMid := fs) henv hcur1_fit hseed hrep (s := s)
      refine stageSlotCheckSeq_fastStep (kSlot := kSlot) (fsMid := fs) (pMid := pure ())
        (midCost := 0) (tailCost := 3) hr hlt rfl hcs_st hcs_res hcs_mc hcs_vp ?_
        (by simp) (validProg_pure ()) (FastStateStep.refl hseed hrep)
        htail.1 htail.2.1 htail.2.2 (by omega)
      simp [kSlot, cp, oldTr, zero_ne_one]
  · rw [ite_eq_right hlt]
    obtain ⟨ht1_mc, ht1_vp, ht1_step⟩ :=
      tickToStage1Prog_fastStep (fs := fs) henv hseed hrep (s := s)
    exact stageCursorPrefix_ge_fastStep (tailCost := 3) hr hlt rfl ht1_mc ht1_vp ht1_step (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end

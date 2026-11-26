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
# Stage 1 of `epochTick`

Implements and verifies `epochTickStage1GenProg`, which scans `buf oldEp` to collect unique dirty
buckets (`rebQueued`, `dirtyBuckets`, `dirtyCount`) and then enters either Stage 2 (if nonempty)
or Stage 3 (if empty).
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

/-- Enter Stage 2 on `dirtyBuckets 0` (`d = (cp, base)`). -/
@[irreducible] private def stage1EnterStage2Prog :
    WhpCoreParams × ℕ → Memory.Prog Unit
  | (cp, base) => do
    let z0 ← pure 0
    let z2 ← pure 2
    let b0 ← readDirtyBucketGenProg ((cp, base), z0)
    let rIdx0 ← readRebSliceIdxGenProg ((cp, base), b0)
    resetBTreeSliceGenProg ((cp, base), rIdx0)
    writeHdrProg ((base, hdrRebStage), z2)
    writeHdrProg ((base, hdrDirtyIdx), z0)
    resetRebScanHdrsProg (base, z0)

private theorem realizes_stage1EnterStage2 :
    Realizes .exact stage1EnterStage2Prog
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          0 < fs.dirtyCount ∧
          fs.dirtyBuckets 0 < numBucketsWhp n_max ∧
          fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max)
      (fun _ _ => 0) := by
  unfold stage1EnterStage2Prog
  have hrd := realizes_readDirtyBucketGen
  have hrs := realizes_readRebSliceIdxGen
  have hrb := realizes_resetBTreeSliceGen
  have hwh := realizes_writeHdr
  have hzh := realizes_resetRebScanHdrs
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hdc0, hb0, hr0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hd_st, hd_res, _, _⟩ := readDirtyBucketGenProg_spec henv hdc0 hrep (s := s)
    obtain ⟨hr_st, hr_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb0 hrep (s := s)
    simp only [hd_st, hd_res, hr_st, hr_res] at *
    first
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrRebStage, hdrDirtyIdx]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_qEpoch hth]; exact hdc0.trans_le hrep.1)
    | (rw [wp_large_M hth]; exact hb0)
    | (rw [wp_large_M hth]; exact hr0)
  )

private theorem stage1EnterStage2Prog_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hdc0 : 0 < fs.dirtyCount)
    (hb0 : fs.dirtyBuckets 0 < numBucketsWhp n_max)
    (hr0 : fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage1EnterStage2Prog (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    let b0 := fs.dirtyBuckets 0
    let rIdx0 := fs.rebSliceIdx b0
    memoryCost prog s ≤ 20 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        rebStage := 2
        dirtyIdx := 0
        rebCandSalt := 0
        rebScanCursor := 0
        rebInsCount := 0
        rebCollision := 0
        slices := Function.update fs.slices rIdx0 (resetBTreeSlice (fs.slices rIdx0)) } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  set b0 := fs.dirtyBuckets 0
  set rIdx0 := fs.rebSliceIdx b0
  obtain ⟨hd_st, hd_res, hd_mc, hd_vp⟩ := readDirtyBucketGenProg_spec henv hdc0 hrep (s := s)
  obtain ⟨hr_st, hr_res, hr_mc, hr_vp⟩ := readRebSliceIdxGenProg_spec henv hb0 hrep (s := s)
  obtain ⟨hrs_mc, hrs_vp, hrs_step⟩ :=
    resetBTreeSliceGenProg_fastStep henv hr0 hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s (resetBTreeSliceGenProg ((cp, base), rIdx0))
  set fs1 : FastState :=
    { fs with slices := Function.update fs.slices rIdx0 (resetBTreeSlice (fs.slices rIdx0)) }
  have hw1 := writeHdrStep (fs := fs1) henv (by dsimp [hdrRebStage]; decide)
    (henv.fits_const (by decide)) (fun h => by dsimp [hdrRebStage] at h; omega)
    hrs_step.2.1 hrs_step.2.2.1 (hdrOff := hdrRebStage) (val := 2) (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebStage), 2))
  set fs2 : FastState := { fs1 with rebStage := 2 }
  have hw2 := writeHdrZeroStep (fs := fs2) henv (by dsimp [hdrDirtyIdx]; decide)
    hw1.2.2.2.1 hw1.2.2.2.2.1 (hdrOff := hdrDirtyIdx) (s := s2)
  set s3 := (Memory.spec 0).clientState s2 (writeHdrProg ((base, hdrDirtyIdx), 0))
  set fs3 : FastState := { fs2 with dirtyIdx := 0 }
  obtain ⟨hzh_mc, hzh_vp, hzh_step⟩ :=
    resetRebScanHdrsProg_fastStep (fs := fs3) henv (Nat.two_pow_pos w)
      hw2.2.2.2.1 hw2.2.2.2.2.1 (cand := 0) (s := s3)
  have hseq := seqUnitProg_fastStep (c₁ := 8) (c₂ := 6) ⟨le_of_eq hrs_mc, hrs_vp, hrs_step⟩
    (seqUnitProg_fastStep hw1 (seqUnitProg_fastStep hw2 ⟨hzh_mc, hzh_vp, hzh_step⟩))
  dsimp only
  unfold stage1EnterStage2Prog; simp only [pure_bind]
  rw [clientState_bind, hd_st, hd_res, clientState_bind, hr_st, hr_res]
  refine ⟨?_, ?_, hseq.2.2⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hd_st, hd_res, hd_mc, hr_st, hr_res, hr_mc]
    have hmc := hseq.1
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind] at hmc
    dsimp only [s1, cp, b0, rIdx0] at hmc ⊢; omega
  · refine validProg_bind hd_vp ?_; rw [hd_st, hd_res]
    refine validProg_bind hr_vp ?_; rw [hr_st, hr_res]
    exact hseq.2.1

/-- Finish Stage 1 (`dirtyCount = 0` → Stage 3, else → Stage 2 on `dirtyBuckets 0`). -/
@[irreducible] private def stage1FinishGenProg :
    WhpCoreParams × ℕ → Memory.Prog Unit
  | (cp, base) => do
    let z0 ← pure 0
    let dc ← readHdrProg (base, hdrDirtyCount)
    if dc = z0 then
      tickToStage3Prog base
    else
      stage1EnterStage2Prog (cp, base)

private theorem realizes_stage1FinishGen :
    Realizes .exact stage1FinishGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (0 < fs.dirtyCount →
            fs.dirtyBuckets 0 < numBucketsWhp n_max ∧
            fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max))
      (fun _ _ => 0) := by
  unfold stage1FinishGenProg
  have hrh := realizes_readHdr
  have ht3 := realizes_tickToStage3
  have he2 := realizes_stage1EnterStage2
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hpos_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hh := fastMemHdrs hrep
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hdc_st, hdc_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
      (by dsimp [hdrDirtyCount]; omega) (s := s)
    rw [hh.dirtyCount] at hdc_res
    simp only [hdc_st, hdc_res] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrDirtyCount]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | (have hdc0 : 0 < fs.dirtyCount := by omega
       obtain ⟨hb0, hr0⟩ := hpos_fn hdc0
       exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hdc0, hb0, hr0⟩)
  )

private theorem stage1FinishGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hpos_fn : 0 < fs.dirtyCount →
      fs.dirtyBuckets 0 < numBucketsWhp n_max ∧
      fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage1FinishGenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 21 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage1Finish fs) s s' := by
  have hh := fastMemHdrs hrep
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hdc_st, hdc_res, hdc_mc, hdc_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
    (by dsimp [hdrDirtyCount]; omega) (s := s)
  rw [hh.dirtyCount] at hdc_res
  dsimp only
  unfold stage1FinishGenProg; simp only [pure_bind]
  dsimp only [epochTickStage1Finish]
  by_cases hdc0 : fs.dirtyCount = 0
  · obtain ⟨ht3_mc, ht3_vp, ht3_step⟩ := tickToStage3Prog_fastStep henv hseed hrep (s := s)
    rw [ite_eq_left hdc0, clientState_bind, hdc_st, hdc_res, ite_eq_left hdc0]
    refine ⟨?_, validProg_bind hdc_vp (by rwa [hdc_st, hdc_res, ite_eq_left hdc0]), ht3_step⟩
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hdc_st, hdc_res, hdc_mc, ite_eq_left hdc0]; omega
  · obtain ⟨hb0, hr0⟩ := hpos_fn (Nat.pos_of_ne_zero hdc0)
    obtain ⟨he2_mc, he2_vp, he2_step⟩ :=
      stage1EnterStage2Prog_fastStep henv (Nat.pos_of_ne_zero hdc0) hb0 hr0 hseed hrep (s := s)
    rw [ite_eq_right hdc0, clientState_bind, hdc_st, hdc_res, ite_eq_right hdc0]
    refine ⟨?_, validProg_bind hdc_vp (by rwa [hdc_st, hdc_res, ite_eq_right hdc0]), he2_step⟩
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hdc_st, hdc_res, hdc_mc, ite_eq_right hdc0]
    dsimp only [cp] at he2_mc ⊢; omega

/-- Stage 1 `some (b, _)` helper: queue bucket `b` if `rebQueued b = 0` (`d = ((cp, base), b)`). -/
@[irreducible] private def stage1QueueBucketProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let f9 ← pure 9
    let rq ← readBktFieldGenProg (((cp, base), b), f9)
    if rq = z0 then
      writeBktFieldGenProg ((((cp, base), b), f9), z1)
      pushDirtyBucketGenProg ((cp, base), b)
    else
      pure ()

private theorem realizes_stage1QueueBucket :
    Realizes .exact stage1QueueBucketProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.dirtyCount < qEpochWhp n_max)
      (fun _ _ => 0) := by
  unfold stage1QueueBucketProg
  have hrb := realizes_readBktFieldGen
  have hwb := realizes_writeBktFieldGen
  have hpd := realizes_pushDirtyBucketGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hdc_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨h9_st, _, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 9 < 10) hrep (s := s)
    obtain ⟨_, _, hw9_step⟩ :=
      writeBktFieldGenProg_fastStep henv hb (by decide : 9 < 10)
        (by have := henv.numBuckets_le_n_max; omega : 1 ≤ n_max) hseed hrep (s := s)
    have hh1 := fastMemHdrs hw9_step.2.2.1
    simp only [h9_st] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | (rw [wp_large_qEpoch hth, hh1.dirtyCount]; dsimp only [setBktField]; exact hdc_lt)
  )

private theorem stage1QueueBucketProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hdc_lt : fs.dirtyCount < qEpochWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage1QueueBucketProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    let fs' :=
      if fs.rebQueued b = 0 then
        { fs with
          rebQueued := Function.update fs.rebQueued b 1
          dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b
          dirtyCount := fs.dirtyCount + 1 }
      else fs
    memoryCost prog s ≤ 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs' s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨h9_st, h9_res, h9_mc, h9_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 9 < 10) hrep (s := s)
  simp only [getBktField] at h9_res
  dsimp only
  unfold stage1QueueBucketProg; simp only [pure_bind]
  by_cases hrq0 : fs.rebQueued b = 0
  · rw [ite_eq_left hrq0]
    obtain ⟨hw_mc, hw_vp, hw_step⟩ :=
      writeBktFieldGenProg_fastStep henv hb (by decide : 9 < 10)
        (by have := henv.numBuckets_le_n_max; omega : 1 ≤ n_max) hseed hrep (s := s)
    simp only [setBktField] at hw_step
    set s1 := (Memory.spec 0).clientState s (writeBktFieldGenProg ((((cp, base), b), 9), 1))
    set fs1 : FastState := { fs with rebQueued := Function.update fs.rebQueued b 1 }
    obtain ⟨hpd_mc, hpd_vp, hpd_step⟩ :=
      pushDirtyBucketGenProg_fastStep (fs := fs1) henv hdc_lt hb hw_step.2.1 hw_step.2.2.1 (s := s1)
    rw [clientState_bind, h9_st, h9_res, ite_eq_left hrq0, clientState_bind]
    refine ⟨?_, ?_, hw_step.trans hpd_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h9_st, h9_res, h9_mc, ite_eq_left hrq0]; simp only [memoryCost_bind]
      dsimp only [s1, cp] at hw_mc hpd_mc ⊢; omega
    · refine validProg_bind h9_vp ?_; rw [h9_st, h9_res, ite_eq_left hrq0]
      exact validProg_bind hw_vp hpd_vp
  · rw [ite_eq_right hrq0, clientState_bind, h9_st, h9_res, ite_eq_right hrq0]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h9_st, h9_res, h9_mc, ite_eq_right hrq0, memoryCost_pure]; omega
    · refine validProg_bind h9_vp ?_
      rw [h9_st, h9_res, ite_eq_right hrq0]
      exact validProg_pure _

/-- Execute Stage 1 of `epochTick` (`d = (cp, base)`). -/
@[irreducible] def epochTickStage1GenProg :
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
        stage1QueueBucketProg ((cp, base), slotCheckBucket cs)
        writeHdrProg ((base, hdrStageCursor), nextCur)
        if ia ≤ nextCur then
          stage1FinishGenProg (cp, base)
        else
          pure ()
      else
        writeHdrProg ((base, hdrStageCursor), nextCur)
        if ia ≤ nextCur then
          stage1FinishGenProg (cp, base)
        else
          pure ()
    else
      stage1FinishGenProg (cp, base)

private theorem stage1_unpack_pre {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hth : whpThreshold c ≤ n_max)
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) (hs1 : fs.rebStage = 1) :
    (fs.oldEp = 0 ∨ fs.oldEp = 1) ∧ (fs.buf fs.oldEp).itemAlloc < n_max ∧
    fs.stageCursor ≤ (fs.buf fs.oldEp).itemAlloc ∧ fs.dirtyCount < qEpochWhp n_max ∧
    (0 < fs.dirtyCount → fs.dirtyBuckets 0 < numBucketsWhp n_max ∧
      fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max) ∧
    ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap ∧
      ∀ k b loc, oldMap k = some (b, loc) → b < numBucketsWhp n_max := by
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hc.curEp_or with h | h <;> simp [FastState.oldEp, h]
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)), ite_eq_left hs1] at hpre
  obtain ⟨hsc_le, hdc_le_sc, hd_bnds, _⟩ := hpre
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  exact ⟨hold_or, by omega, hsc_le, by omega,
    fun hpos => ⟨(hd_bnds 0 hpos).1, rebSliceIdx_lt_of_core hc (hd_bnds 0 hpos).1⟩,
    oldMap, hv_o, fun k b loc hmk => ((hrel_o.2 k b loc).mp hmk).1⟩

private theorem stage1_dirtyZero_bounds_after_queue {c U V n_max b₀ : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hb₀ : b₀ < numBucketsWhp n_max)
    (hpos_init : 0 < fs.dirtyCount → fs.dirtyBuckets 0 < numBucketsWhp n_max ∧
      fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max)
    {fs_q : FastState}
    (hfs_q : fs_q = if fs.rebQueued b₀ = 0 then
      { fs with
        rebQueued := Function.update fs.rebQueued b₀ 1
        dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
        dirtyCount := fs.dirtyCount + 1 } else fs) :
    0 < fs_q.dirtyCount → fs_q.dirtyBuckets 0 < numBucketsWhp n_max ∧
      fs_q.rebSliceIdx (fs_q.dirtyBuckets 0) < 3 * numBucketsWhp n_max := by
  subst hfs_q
  split_ifs with hrq0
  · intro _
    have hb_z : Function.update fs.dirtyBuckets fs.dirtyCount b₀ 0 < numBucketsWhp n_max := by
      rcases eq_or_ne fs.dirtyCount 0 with hdc0 | hdc0
      · simpa only [hdc0, Function.update_self] using hb₀
      · simpa only [Function.update_of_ne (Ne.symm hdc0)] using
          (hpos_init (Nat.pos_of_ne_zero hdc0)).1
    exact ⟨hb_z, rebSliceIdx_lt_of_core hc hb_z⟩
  · exact hpos_init

/-- `Realizes .exact` certificate for `epochTickStage1GenProg`. -/
theorem realizes_epochTickStage1Gen :
    Realizes .exact epochTickStage1GenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          ValidEpochStagePreTick c U n_max θ fs ∧
          fs.rebStage = 1)
      (fun _ _ => 0) := by
  unfold epochTickStage1GenProg
  have hro := realizes_readOldEp
  have hra := realizes_readBufAllocs
  have hrh := realizes_readHdr
  have hcs := realizes_bufCheckSlotGen
  have hqb := realizes_stage1QueueBucket
  have hwh := realizes_writeHdr
  have hfn := realizes_stage1FinishGen
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hcore, hpre, hs1⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hold_or, hia_lt, hsc_le, hdc_lt_q, hpos_init, oldMap, hv_o, hrel_o⟩ :=
      stage1_unpack_pre hth hcore hpre hs1
    have hr := stageCursorReads_spec henv hcore.curEp_or hold_or hrep (s := s)
    obtain ⟨hcs_st, hcs_res, _, _⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    simp only [hr.ro_st, hr.ro_res, hr.ra_st, hr.ra_res, hr.sc_st, hr.sc_res, hcs_st] at *
    first
    | exact h2w
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrCurEp, hdrStageCursor]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, oldMap, henv, rfl, hold_or,
        hrep.buf_rep hold_or, hv_o⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hpos_init⟩
    | (have hw := writeHdrStep (fs := fs) henv (by dsimp [hdrStageCursor]; decide)
         (henv.fits_of_le_n_max (by omega)) (fun h6 => by dsimp [hdrStageCursor] at h6; omega)
         hseed hrep (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s)
       exact ⟨c, U, V, w, n_max, { fs with stageCursor := fs.stageCursor + 1 },
         henv, rfl, hw.2.2.2.2.1, hpos_init⟩)
    | (rcases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with _ | ⟨b₀, loc₀⟩
       · rw [hchk] at hcs_res
         simp only [hcs_res] at *
         cases (by assumption : (0 : ℕ) = 1)
       · rw [hchk] at hcs_res
         obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
         have hb₀ : b₀ < numBucketsWhp n_max := hrel_o k b₀ loc₀ hmk
         simp only [hcs_res] at *
         first
         | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb₀, hdc_lt_q⟩
         | (obtain ⟨_, _, hqb_step⟩ :=
              stage1QueueBucketProg_fastStep henv hb₀ hdc_lt_q hseed hrep (s := s)
            set s_q := (Memory.spec 0).clientState s
              (stage1QueueBucketProg ((mkWhpCoreParams c U V w n_max, base), b₀))
            set fs_q : FastState :=
              if fs.rebQueued b₀ = 0 then
                { fs with
                  rebQueued := Function.update fs.rebQueued b₀ 1
                  dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
                  dirtyCount := fs.dirtyCount + 1 }
              else fs
            have hw := writeHdrStep (fs := fs_q) henv (by dsimp [hdrStageCursor]; decide)
              (henv.fits_of_le_n_max (by omega)) (fun h6 => by dsimp [hdrStageCursor] at h6; omega)
              hqb_step.2.1 hqb_step.2.2.1 (hdrOff := hdrStageCursor)
              (val := fs.stageCursor + 1) (s := s_q)
            exact ⟨c, U, V, w, n_max, { fs_q with stageCursor := fs.stageCursor + 1 },
              henv, rfl, hw.2.2.2.2.1,
              stage1_dirtyZero_bounds_after_queue (fs_q := fs_q) hcore hb₀ hpos_init rfl⟩))
  )

private theorem stage1BumpAndFinish_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs fsMid : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcur1_fit : Fits w (fs.stageCursor + 1))
    (hpos_fn : 0 < fsMid.dirtyCount →
      fsMid.dirtyBuckets 0 < numBucketsWhp n_max ∧
      fsMid.rebSliceIdx (fsMid.dirtyBuckets 0) < 3 * numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fsMid s.mem) :
    let cp := mkWhpCoreParams c U V w n_max
    let ia := (fs.buf fs.oldEp).itemAlloc
    let nextCur := fs.stageCursor + 1
    let prog := writeHdrProg ((base, hdrStageCursor), nextCur) >>= fun _ =>
      if ia ≤ nextCur then stage1FinishGenProg (cp, base) else pure ()
    let fsW : FastState := { fsMid with stageCursor := nextCur }
    let fsOut := if ia ≤ nextCur then epochTickStage1Finish fsW else fsW
    memoryCost prog s ≤ 22 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s ((Memory.spec 0).clientState s prog) := by
  have hw := writeHdrStep (fs := fsMid) henv (by dsimp [hdrStageCursor]; decide) hcur1_fit
    (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hseed hrep
    (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s)
  set sW := (Memory.spec 0).clientState s
    (writeHdrProg ((base, hdrStageCursor), fs.stageCursor + 1))
  set fsW : FastState := { fsMid with stageCursor := fs.stageCursor + 1 }
  dsimp only
  by_cases hdone : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
  · rw [ite_eq_left hdone, ite_eq_left hdone]
    obtain ⟨hfn_mc, hfn_vp, hfn_step⟩ :=
      stage1FinishGenProg_fastStep (fs := fsW) henv hpos_fn hw.2.2.2.1 hw.2.2.2.2.1 (s := sW)
    exact seqUnitProg_fastStep (c₁ := 1) (c₂ := 21) hw ⟨hfn_mc, hfn_vp, hfn_step⟩
  · rw [ite_eq_right hdone, ite_eq_right hdone]
    refine ⟨?_, validProg_bind hw.2.1 (validProg_pure _), ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
      have := hw.1; omega
    · rw [clientState_bind, clientState_pure_whp]; exact hw.2.2

/-- `FastStateStep` specification for `epochTickStage1GenProg`. -/
theorem epochTickStage1GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hs1 : fs.rebStage = 1)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage1GenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 52 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage1 fs) s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hold_or, hia_lt, _, hdc_lt_q, hpos_init, oldMap, hv_o, hrel_o⟩ :=
    stage1_unpack_pre hth hc hpre hs1
  have hr := stageCursorReads_spec henv hc.curEp_or hold_or hrep (s := s)
  dsimp only
  unfold epochTickStage1GenProg; simp only [pure_bind]
  dsimp only [epochTickStage1]
  set oldTr := fs.buf fs.oldEp
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    have hcur1_fit : Fits w (fs.stageCursor + 1) := henv.fits_of_le_n_max (by omega)
    set kSlot : ℕ × (ℕ × ℕ) → Memory.Prog Unit := fun cs =>
      let nextCur := fs.stageCursor + 1
      let tail := writeHdrProg ((base, hdrStageCursor), nextCur) >>= fun _ =>
        if oldTr.itemAlloc ≤ nextCur then stage1FinishGenProg (cp, base) else pure ()
      if cs.1 = 1 then
        stage1QueueBucketProg ((cp, base), slotCheckBucket cs) >>= fun _ => tail
      else tail
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      have hb₀ : b₀ < numBucketsWhp n_max := hrel_o k b₀ loc₀ hmk
      obtain ⟨hqb_mc, hqb_vp, hqb_step⟩ :=
        stage1QueueBucketProg_fastStep henv hb₀ hdc_lt_q hseed hrep (s := s)
      set fs_q : FastState :=
        if fs.rebQueued b₀ = 0 then
          { fs with
            rebQueued := Function.update fs.rebQueued b₀ 1
            dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
            dirtyCount := fs.dirtyCount + 1 }
        else fs
      have hbf := stage1BumpAndFinish_fastStep (fs := fs) (fsMid := fs_q) henv hcur1_fit
        (stage1_dirtyZero_bounds_after_queue hc hb₀ hpos_init rfl)
        hqb_step.2.1 hqb_step.2.2.1
        (s := (Memory.spec 0).clientState s (stage1QueueBucketProg ((cp, base), b₀)))
      refine stageSlotCheckSeq_fastStep (kSlot := kSlot) (midCost := 12) (tailCost := 22)
        hr hlt rfl hcs_st hcs_res hcs_mc hcs_vp ?_ hqb_mc hqb_vp hqb_step
        hbf.1 hbf.2.1
        (by simpa only [fs_q,
          apply_ite (fun f : FastState => { f with stageCursor := fs.stageCursor + 1 })]
          using hbf.2.2)
        (by omega)
      dsimp only [kSlot, slotCheckBucket, cp, oldTr]
      simp
    | none =>
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      have hbf := stage1BumpAndFinish_fastStep (fs := fs) (fsMid := fs) henv hcur1_fit hpos_init
        hseed hrep (s := s)
      refine stageSlotCheckSeq_fastStep (kSlot := kSlot) (fsMid := fs) (pMid := pure ())
        (midCost := 0) (tailCost := 22) hr hlt rfl hcs_st hcs_res hcs_mc hcs_vp ?_
        (by simp) (validProg_pure ()) (FastStateStep.refl hseed hrep)
        hbf.1 hbf.2.1 hbf.2.2 (by omega)
      dsimp only [kSlot, cp, oldTr]
      simp [zero_ne_one, pure_bind]
  · rw [ite_eq_right hlt]
    obtain ⟨hfn_mc, hfn_vp, hfn_step⟩ :=
      stage1FinishGenProg_fastStep (fs := fs) henv hpos_init hseed hrep (s := s)
    exact stageCursorPrefix_ge_fastStep (tailCost := 21)
      hr hlt rfl hfn_mc hfn_vp hfn_step (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end

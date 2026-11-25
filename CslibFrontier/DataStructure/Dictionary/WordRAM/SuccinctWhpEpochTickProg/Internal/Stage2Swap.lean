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
# Stage 2 Post-Scan Collision Recovery and Bucket-Role Swap

Implements and verifies `stage2PostScanGenProg` (handling collision salt-increment reset vs
completed-bucket live/rebuild role swap, slice reset, and transition to the next dirty bucket or
Stage 3).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Stage 2 collision recovery: reset `rebSlice[b]` and advance `rebCandSalt := cand + 1`
(`d = ((cp, base), b)`). -/
@[irreducible] private def stage2CollisionResetProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let rIdx ← readRebSliceIdxGenProg ((cp, base), b)
    resetBTreeSliceGenProg ((cp, base), rIdx)
    let cand ← readHdrProg (base, hdrRebCandSalt)
    let cand1 ← pure (cand + 1)
    resetRebScanHdrsProg (base, cand1)

private theorem realizes_stage2CollisionReset :
    Realizes .exact stage2CollisionResetProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          fs.rebCandSalt < sMaxWhp c n_max)
      (fun _ _ => 0) := by
  unfold stage2CollisionResetProg
  have hrs := realizes_readRebSliceIdxGen
  have hrb := realizes_resetBTreeSliceGen
  have hrh := realizes_readHdr
  have hzh := realizes_resetRebScanHdrs
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hrIdx, hcand_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨_, _, hrb_step⟩ := resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
    set s1 := (Memory.spec 0).clientState s
      (resetBTreeSliceGenProg ((mkWhpCoreParams c U V w n_max, base), fs.rebSliceIdx b))
    obtain ⟨hcd_st, hcd_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s1)
    have hh1 := fastMemHdrs hrb_step.2.2.1
    rw [hh1.rebCandSalt] at hcd_res
    dsimp only at hcd_res
    dsimp only [s1] at hcd_st hcd_res
    simp only [hrs_st, hrs_res, hcd_st, hcd_res] at *
    first
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrRebCandSalt]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | (rw [wp_large_M hth]; exact hrIdx)
  )

private theorem stage2CollisionResetProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max)
    (hcand_lt : fs.rebCandSalt < sMaxWhp c n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage2CollisionResetProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    let rIdx := fs.rebSliceIdx b
    memoryCost prog s ≤ 20 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        rebCandSalt := fs.rebCandSalt + 1
        rebScanCursor := 0
        rebInsCount := 0
        rebCollision := 0
        slices := Function.update fs.slices rIdx (resetBTreeSlice (fs.slices rIdx)) } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  set rIdx := fs.rebSliceIdx b
  obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
  obtain ⟨hrb_mc, hrb_vp, hrb_step⟩ :=
    resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s (resetBTreeSliceGenProg ((cp, base), rIdx))
  set fs1 : FastState :=
    { fs with slices := Function.update fs.slices rIdx (resetBTreeSlice (fs.slices rIdx)) }
  obtain ⟨hcd_st, hcd_res, hcd_mc, hcd_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
    (by dsimp [hdrRebCandSalt]; omega) (s := s1)
  have hh1 := fastMemHdrs hrb_step.2.2.1
  rw [hh1.rebCandSalt] at hcd_res; dsimp only [fs1] at hcd_res
  obtain ⟨hzh_mc, hzh_vp, hzh_step⟩ :=
    resetRebScanHdrsProg_fastStep (fs := fs1) henv (henv.fits_of_le_n_max (by omega))
      hrb_step.2.1 hrb_step.2.2.1 (cand := fs.rebCandSalt + 1) (s := s1)
  dsimp only
  unfold stage2CollisionResetProg; simp only [pure_bind]
  rw [clientState_bind, hrs_st, hrs_res, clientState_bind, clientState_bind, hcd_st, hcd_res]
  refine ⟨?_, ?_, hrb_step.trans hzh_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrs_st, hrs_res, hrs_mc]
    dsimp only [s1, cp, rIdx] at hcd_st hcd_res hcd_mc hrb_mc hzh_mc ⊢
    rw [hcd_st, hcd_res, hcd_mc]; omega
  · refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
    refine validProg_bind hrb_vp ?_
    refine validProg_bind hcd_vp ?_; rw [hcd_st, hcd_res]; exact hzh_vp

@[irreducible] private def stage2SwapRolesProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), b) => do
    let ro ← readRebAndOmRoleGenProg ((cp, base), b)
    let f2 ← pure 2
    writeBktFieldGenProg ((((cp, base), b), f2), ro.1)
    pure ro.2

private theorem realizes_stage2SwapRoles :
    Realizes .exact stage2SwapRolesProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold stage2SwapRolesProg
  have hro := realizes_readRebAndOmRoleGen
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    simp only [wp_large_M hth] at *
    first
    | decide
    | exact hb
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

private theorem stage2SwapRolesProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrv : fs.liveRole b < 3 ∧ fs.overmarsRole b < 3 ∧ fs.liveRole b ≠ fs.overmarsRole b)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage2SwapRolesProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec 0).clientResult s prog = fs.overmarsRole b ∧
    memoryCost prog s ≤ 10 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with liveRole := Function.update fs.liveRole b (fs.rebRole b) } s s' := by
  have hth := henv.2.2.2.1
  have h3_le : 3 ≤ n_max := by
    have := henv.numBuckets_le_n_max; have := (large_bounds_lt_n_max hth).1; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ :=
    readRebAndOmRoleGenProg_spec henv hb hrep (s := s)
  have hcond : fs.liveRole b ≤ 3 ∧ fs.overmarsRole b ≤ 3 - fs.liveRole b := ⟨by omega, by omega⟩
  rw [ite_eq_left hcond] at hro_res
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 2 < 10)
      (by dsimp [FastState.rebRole]; omega) hseed hrep (val := fs.rebRole b) (s := s)
  simp only [setBktField] at hw1_step
  dsimp only
  unfold stage2SwapRolesProg; simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientResult_bind, hro_st, hro_res, clientResult_bind]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hro_st, hro_res, hro_mc, memoryCost_pure]
    dsimp only [cp] at hw1_mc ⊢; omega
  · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
    exact validProg_bind hw1_vp (validProg_pure _)
  · rw [clientState_bind, hro_st, hro_res, clientState_bind, clientState_pure_whp]
    exact hw1_step

@[irreducible] private def stage2SwapCountsProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let f1 ← pure 1
    let f3 ← pure 3
    let cand ← readHdrProg (base, hdrRebCandSalt)
    let ins ← readHdrProg (base, hdrRebInsCount)
    writeBktFieldGenProg ((((cp, base), b), f1), cand)
    writeBktFieldGenProg ((((cp, base), b), f3), ins)

private theorem realizes_stage2SwapCounts :
    Realizes .exact stage2SwapCountsProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold stage2SwapCountsProg
  have hrh := realizes_readHdr
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    rw [wp_large_M hth] at hb
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrRebCandSalt, hdrRebInsCount]; omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
  )

private theorem stage2SwapCountsProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hcand_le : fs.rebCandSalt ≤ n_max)
    (hins_le : fs.rebInsCount ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage2SwapCountsProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 14 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        bktSalt := Function.update fs.bktSalt b fs.rebCandSalt
        liveInsCount := Function.update fs.liveInsCount b fs.rebInsCount } s s' := by
  have hh := fastMemHdrs hrep
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hcd_st, hcd_res, hcd_mc, hcd_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
    (by dsimp [hdrRebCandSalt]; omega) (s := s)
  obtain ⟨hin_st, hin_res, hin_mc, hin_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebInsCount)
    (by dsimp [hdrRebInsCount]; omega) (s := s)
  rw [hh.rebCandSalt] at hcd_res
  rw [hh.rebInsCount] at hin_res
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 1 < 10) hcand_le
      hseed hrep (val := fs.rebCandSalt) (s := s)
  simp only [setBktField] at hw1_step
  set s1 := (Memory.spec 0).clientState s
    (writeBktFieldGenProg ((((cp, base), b), 1), fs.rebCandSalt))
  set fs1 : FastState := { fs with bktSalt := Function.update fs.bktSalt b fs.rebCandSalt }
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ :=
    writeBktFieldGenProg_fastStep (fs := fs1) henv hb (by decide : 3 < 10) hins_le
      hw1_step.2.1 hw1_step.2.2.1 (val := fs.rebInsCount) (s := s1)
  simp only [setBktField] at hw2_step
  dsimp only
  unfold stage2SwapCountsProg; simp only [pure_bind]
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hcd_st, hcd_res, hcd_mc, hin_st, hin_res, hin_mc]
    dsimp only [s1, cp] at hw1_mc hw2_mc ⊢; omega
  · refine validProg_bind hcd_vp ?_; rw [hcd_st, hcd_res]
    refine validProg_bind hin_vp ?_; rw [hin_st, hin_res]
    exact validProg_bind hw1_vp hw2_vp
  · rw [clientState_bind, hcd_st, hcd_res, clientState_bind, hin_st, hin_res,
      clientState_bind]
    exact hw1_step.trans hw2_step

@[irreducible] private def stage2SwapClearOmProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let f8 ← pure 8
    let bm ← mkBktMetaRtProg (cp, base)
    setOvermarsActRtProg ((bm, b), z0)
    writeBktFieldGenProg ((((cp, base), b), f8), z1)

private theorem realizes_stage2SwapClearOm :
    Realizes .exact stage2SwapClearOmProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold stage2SwapClearOmProg
  have hmb := realizes_mkBktMetaRt
  have hsa := realizes_setOvermarsActRt
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    rw [wp_large_M hth] at hb
    obtain ⟨hmb_st, hmb_res, _, _⟩ :=
      mkBktMetaRtProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
    simp only [hmb_st, hmb_res] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | exact ⟨c, U, V, w, n_max, base, henv, rfl, hb⟩
  )

private theorem stage2SwapClearOmProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage2SwapClearOmProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 16 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        overmarsActive := Function.update fs.overmarsActive b 0
        overmarsCursor := Function.update fs.overmarsCursor b 0
        overmarsInsCount := Function.update fs.overmarsInsCount b 0
        rebDoneFlag := Function.update fs.rebDoneFlag b 1 } s s' := by
  have hth := henv.2.2.2.1
  have h1_le : 1 ≤ n_max := by have := (large_bounds_lt_n_max hth).2.1; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hmb_st, hmb_res, hmb_mc, hmb_vp⟩ :=
    mkBktMetaRtProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hsa_mc, hsa_vp, hsa_step⟩ :=
    setOvermarsActRtProg_fastStep henv hb (Nat.zero_le _) hseed hrep (actVal := 0) (s := s)
  set s1 := (Memory.spec 0).clientState s
    (setOvermarsActRtProg ((mkBktMetaRt c U V w n_max base, b), 0))
  set fs1 : FastState :=
    { fs with
      overmarsActive := Function.update fs.overmarsActive b 0
      overmarsCursor := Function.update fs.overmarsCursor b 0
      overmarsInsCount := Function.update fs.overmarsInsCount b 0 }
  obtain ⟨hw8_mc, hw8_vp, hw8_step⟩ :=
    writeBktFieldGenProg_fastStep (fs := fs1) henv hb (by decide : 8 < 10) h1_le
      hsa_step.2.1 hsa_step.2.2.1 (val := 1) (s := s1)
  simp only [setBktField] at hw8_step
  dsimp only
  unfold stage2SwapClearOmProg; simp only [pure_bind]
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hmb_st, hmb_res, hmb_mc]
    dsimp only [s1, cp] at hsa_mc hw8_mc ⊢; omega
  · refine validProg_bind hmb_vp ?_; rw [hmb_st, hmb_res]
    exact validProg_bind hsa_vp hw8_vp
  · rw [clientState_bind, hmb_st, hmb_res, clientState_bind]
    exact hsa_step.trans hw8_step

/-- Stage 2 bucket-swap scalar metadata updates (`d = ((cp, base), b)`), returning `omRole`. -/
@[irreducible] private def stage2SwapScalarsProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | d => do
    let omRole ← stage2SwapRolesProg d
    stage2SwapCountsProg d
    stage2SwapClearOmProg d
    pure omRole

private theorem realizes_stage2SwapScalars :
    Realizes .exact stage2SwapScalarsProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold stage2SwapScalarsProg
  have h1 := realizes_stage2SwapRoles
  have h2 := realizes_stage2SwapCounts
  have h3 := realizes_stage2SwapClearOm
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    first | exact h.1 | exact h.2
  )

private theorem stage2SwapScalarsProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrv : fs.liveRole b < 3 ∧ fs.overmarsRole b < 3 ∧ fs.liveRole b ≠ fs.overmarsRole b)
    (hcand_le : fs.rebCandSalt ≤ n_max)
    (hins_le : fs.rebInsCount ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage2SwapScalarsProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec 0).clientResult s prog = fs.overmarsRole b ∧
    memoryCost prog s ≤ 40 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        liveRole := Function.update fs.liveRole b (fs.rebRole b)
        bktSalt := Function.update fs.bktSalt b fs.rebCandSalt
        liveInsCount := Function.update fs.liveInsCount b fs.rebInsCount
        overmarsActive := Function.update fs.overmarsActive b 0
        overmarsCursor := Function.update fs.overmarsCursor b 0
        overmarsInsCount := Function.update fs.overmarsInsCount b 0
        rebDoneFlag := Function.update fs.rebDoneFlag b 1 } s s' := by
  set d := ((mkWhpCoreParams c U V w n_max, base), b)
  obtain ⟨h1_res, h1_mc, h1_vp, h1_step⟩ :=
    stage2SwapRolesProg_fastStep henv hb hrv hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s (stage2SwapRolesProg d)
  set fs1 : FastState := { fs with liveRole := Function.update fs.liveRole b (fs.rebRole b) }
  obtain ⟨h2_mc, h2_vp, h2_step⟩ :=
    stage2SwapCountsProg_fastStep (fs := fs1) henv hb hcand_le hins_le
      h1_step.2.1 h1_step.2.2.1 (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (stage2SwapCountsProg d)
  set fs2 : FastState :=
    { fs1 with
      bktSalt := Function.update fs.bktSalt b fs.rebCandSalt
      liveInsCount := Function.update fs.liveInsCount b fs.rebInsCount }
  obtain ⟨h3_mc, h3_vp, h3_step⟩ :=
    stage2SwapClearOmProg_fastStep (fs := fs2) henv hb h2_step.2.1 h2_step.2.2.1 (s := s2)
  dsimp only
  unfold stage2SwapScalarsProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientResult_bind, h1_res, clientResult_bind, clientResult_bind]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    dsimp only [s1, s2, d] at h1_mc h2_mc h3_mc ⊢; omega
  · refine validProg_bind h1_vp ?_
    refine validProg_bind h2_vp ?_
    exact validProg_bind h3_vp (validProg_pure _)
  · rw [clientState_bind, clientState_bind, clientState_bind, clientState_pure_whp]
    exact (h1_step.trans h2_step).trans h3_step

@[irreducible] private def stage2SwapPreAdvanceProg :
    (WhpCoreParams × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((cp, base), (b, omRole)) => do
    let z0 ← pure 0
    let z3 ← pure 3
    let omIdx ← pure (z3 * b + omRole)
    resetBTreeSliceGenProg ((cp, base), omIdx)
    let di ← readHdrProg (base, hdrDirtyIdx)
    let nextIdx ← pure (di + 1)
    writeHdrProg ((base, hdrDirtyIdx), nextIdx)
    resetRebScanHdrsProg (base, z0)
    pure nextIdx

private theorem realizes_stage2SwapPreAdvance :
    Realizes .exact stage2SwapPreAdvanceProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), (b, omRole)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          omRole < 3 ∧
          fs.dirtyIdx < fs.dirtyCount)
      (fun _ _ => 0) := by
  unfold stage2SwapPreAdvanceProg
  have hrb := realizes_resetBTreeSliceGen
  have hrh := realizes_readHdr
  have hwh := realizes_writeHdr
  have hzh := realizes_resetRebScanHdrs
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, ⟨b, omRole⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hom_lt, hdi_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have h3M_le := (large_index_bounds hth).2.2.2.2.1
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    have hdc_le := hrep.1
    have homIdx_lt : 3 * b + omRole < 3 * numBucketsWhp n_max := by omega
    obtain ⟨_, _, hrs1_step⟩ := resetBTreeSliceGenProg_fastStep henv homIdx_lt hseed hrep (s := s)
    obtain ⟨hdi_st, hdi_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyIdx)
      (by dsimp [hdrDirtyIdx]; omega)
      (s := (Memory.spec 0).clientState s
        (resetBTreeSliceGenProg ((mkWhpCoreParams c U V w n_max, base), 3 * b + omRole)))
    have hh1 := fastMemHdrs hrs1_step.2.2.1
    rw [hh1.dirtyIdx] at hdi_res
    dsimp only at hdi_res
    simp only [hdi_st, hdi_res] at *
    first
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrDirtyIdx]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact homIdx_lt)
  )

private theorem stage2SwapPreAdvanceProg_fastStep {c U V w n_max base b omRole : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hom_lt : omRole < 3)
    (hdi_lt : fs.dirtyIdx < fs.dirtyCount)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage2SwapPreAdvanceProg ((mkWhpCoreParams c U V w n_max, base), (b, omRole))
    let s' := (Memory.spec 0).clientState s prog
    let omIdx := 3 * b + omRole
    let nextIdx := fs.dirtyIdx + 1
    (Memory.spec 0).clientResult s prog = nextIdx ∧
    memoryCost prog s ≤ 16 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices omIdx (resetBTreeSlice (fs.slices omIdx))
        dirtyIdx := nextIdx
        rebCandSalt := 0
        rebScanCursor := 0
        rebInsCount := 0
        rebCollision := 0 } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  have hdc_le := hrep.1
  set cp := mkWhpCoreParams c U V w n_max
  set omIdx := 3 * b + omRole
  have homIdx_lt : omIdx < 3 * numBucketsWhp n_max := by omega
  obtain ⟨hrs1_mc, hrs1_vp, hrs1_step⟩ :=
    resetBTreeSliceGenProg_fastStep henv homIdx_lt hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s (resetBTreeSliceGenProg ((cp, base), omIdx))
  set fs1 : FastState :=
    { fs with slices := Function.update fs.slices omIdx (resetBTreeSlice (fs.slices omIdx)) }
  obtain ⟨hdi_st, hdi_res, hdi_mc, hdi_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyIdx)
    (by dsimp [hdrDirtyIdx]; omega) (s := s1)
  have hh1 := fastMemHdrs hrs1_step.2.2.1
  rw [hh1.dirtyIdx] at hdi_res; dsimp only [fs1] at hdi_res
  have hw := writeHdrStep (fs := fs1) henv (by dsimp [hdrDirtyIdx]; decide)
    (henv.fits_of_le_n_max (by omega)) (fun h6 => by dsimp [hdrDirtyIdx] at h6; omega)
    hrs1_step.2.1 hrs1_step.2.2.1 (hdrOff := hdrDirtyIdx) (val := fs.dirtyIdx + 1) (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrDirtyIdx), fs.dirtyIdx + 1))
  set fs2 : FastState := { fs1 with dirtyIdx := fs.dirtyIdx + 1 }
  obtain ⟨hzh_mc, hzh_vp, hzh_step⟩ := resetRebScanHdrsProg_fastStep (fs := fs2) henv
    (Nat.two_pow_pos w) hw.2.2.2.1 hw.2.2.2.2.1 (cand := 0) (s := s2)
  dsimp only
  unfold stage2SwapPreAdvanceProg; simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientResult_bind, clientResult_bind, hdi_st, hdi_res,
      clientResult_bind, clientResult_bind]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    have hwm := hw.1
    dsimp only [s1, s2, cp, omIdx] at hdi_st hdi_res hdi_mc hrs1_mc hwm hzh_mc ⊢
    rw [hdi_st, hdi_res, hdi_mc]; omega
  · refine validProg_bind hrs1_vp ?_
    refine validProg_bind hdi_vp ?_; rw [hdi_st, hdi_res]
    refine validProg_bind hw.2.1 ?_
    exact validProg_bind hzh_vp (validProg_pure _)
  · rw [clientState_bind, clientState_bind, hdi_st, hdi_res,
      clientState_bind, clientState_bind, clientState_pure_whp]
    exact (hrs1_step.trans hw.2.2).trans hzh_step

@[irreducible] private def stage2SwapAdvanceNextProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), nextIdx) => do
    let dc ← readHdrProg (base, hdrDirtyCount)
    if dc ≤ nextIdx then
      tickToStage3Prog base
    else
      let bNext ← readDirtyBucketGenProg ((cp, base), nextIdx)
      let rIdxNext ← readRebSliceIdxGenProg ((cp, base), bNext)
      resetBTreeSliceGenProg ((cp, base), rIdxNext)

private theorem realizes_stage2SwapAdvanceNext :
    Realizes .exact stage2SwapAdvanceNextProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), nextIdx) s =>
        ∃ (c U V w₀ n_max : ℕ) (fsSw : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fsSw s.mem ∧
          (nextIdx < fsSw.dirtyCount →
            fsSw.dirtyBuckets nextIdx < numBucketsWhp n_max ∧
            fsSw.rebSliceIdx (fsSw.dirtyBuckets nextIdx) < 3 * numBucketsWhp n_max))
      (fun _ _ => 0) := by
  unfold stage2SwapAdvanceNextProg
  have hrh := realizes_readHdr
  have ht3 := realizes_tickToStage3
  have hrd := realizes_readDirtyBucketGen
  have hrs := realizes_readRebSliceIdxGen
  have hrb := realizes_resetBTreeSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, nextIdx⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fsSw, henv, rfl, hrep, hnxt_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hdc_le := hrep.1
    obtain ⟨hdc_st, hdc_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
      (by dsimp [hdrDirtyCount]; omega) (s := s)
    rw [(fastMemHdrs hrep).dirtyCount] at hdc_res
    simp only [hdc_st, hdc_res] at *
    first
    | exact h2w
    | exact henv.fits_const (by dsimp [hdrDirtyCount]; omega)
    | exact henv.fits_hdr_addr (by dsimp [hdrDirtyCount]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | (have hlt_nxt : nextIdx < fsSw.dirtyCount := by omega
       obtain ⟨hbN, hrN⟩ := hnxt_fn hlt_nxt
       obtain ⟨hrd_st, hrd_res, _, _⟩ := readDirtyBucketGenProg_spec henv hlt_nxt hrep (s := s)
       obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hbN hrep (s := s)
       simp only [hrd_st, hrd_res, hrs_st, hrs_res] at *
       first
       | exact ⟨c, U, V, w, n_max, henv, rfl⟩
       | (rw [wp_large_qEpoch hth]; omega)
       | (rw [wp_large_M hth]; exact hbN)
       | (rw [wp_large_M hth]; exact hrN))
  )

private theorem stage2SwapAdvanceNextProg_fastStep {c U V w n_max base nextIdx : ℕ}
    {θ : SeedWhp c U n_max} {fsSw : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hnxt_fn : nextIdx < fsSw.dirtyCount →
      fsSw.dirtyBuckets nextIdx < numBucketsWhp n_max ∧
      fsSw.rebSliceIdx (fsSw.dirtyBuckets nextIdx) < 3 * numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fsSw s.mem) :
    let prog := stage2SwapAdvanceNextProg ((mkWhpCoreParams c U V w n_max, base), nextIdx)
    let s' := (Memory.spec 0).clientState s prog
    let fsOut : FastState :=
      if fsSw.dirtyCount ≤ nextIdx then
        { fsSw with rebStage := 3, stageCursor := 0 }
      else
        let bNext := fsSw.dirtyBuckets nextIdx
        let rIdxNext := fsSw.rebSliceIdx bNext
        { fsSw with
          slices := Function.update fsSw.slices rIdxNext
            (resetBTreeSlice (fsSw.slices rIdxNext)) }
    memoryCost prog s ≤ 16 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s s' := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hdc_st, hdc_res, hdc_mc, hdc_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
    (by dsimp [hdrDirtyCount]; omega) (s := s)
  rw [(fastMemHdrs hrep).dirtyCount] at hdc_res
  dsimp only
  unfold stage2SwapAdvanceNextProg
  by_cases hall : fsSw.dirtyCount ≤ nextIdx
  · obtain ⟨ht3_mc, ht3_vp, ht3_step⟩ := tickToStage3Prog_fastStep henv hseed hrep (s := s)
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hdc_st, hdc_res, hdc_mc, ite_eq_left hall]; omega
    · refine validProg_bind hdc_vp ?_; rw [hdc_st, hdc_res, ite_eq_left hall]; exact ht3_vp
    · rw [ite_eq_left hall, clientState_bind, hdc_st, hdc_res, ite_eq_left hall]
      exact ht3_step
  · have hlt_nxt : nextIdx < fsSw.dirtyCount := Nat.lt_of_not_le hall
    obtain ⟨hbN, hrN⟩ := hnxt_fn hlt_nxt
    obtain ⟨hrd_st, hrd_res, hrd_mc, hrd_vp⟩ :=
      readDirtyBucketGenProg_spec henv hlt_nxt hrep (s := s)
    obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ :=
      readRebSliceIdxGenProg_spec henv hbN hrep (s := s)
    obtain ⟨hrb_mc, hrb_vp, hrb_step⟩ :=
      resetBTreeSliceGenProg_fastStep henv hrN hseed hrep (s := s)
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hdc_st, hdc_res, hdc_mc, ite_eq_right hall]
      simp only [memoryCost_bind]
      dsimp only [cp] at hrd_st hrd_res hrd_mc hrs_st hrs_res hrs_mc hrb_mc ⊢
      rw [hrd_st, hrd_res, hrd_mc, hrs_st, hrs_res, hrs_mc]; omega
    · refine validProg_bind hdc_vp ?_; rw [hdc_st, hdc_res, ite_eq_right hall]
      refine validProg_bind hrd_vp ?_; rw [hrd_st, hrd_res]
      refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
      exact hrb_vp
    · rw [ite_eq_right hall, clientState_bind, hdc_st, hdc_res, ite_eq_right hall,
        clientState_bind, hrd_st, hrd_res, clientState_bind, hrs_st, hrs_res]
      exact hrb_step

/-- Stage 2 post-swap slice reset and dirty-bucket advance (`d = ((cp, base), (b, omRole))`). -/
@[irreducible] private def stage2SwapFinishProg :
    (WhpCoreParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (cp_base, b_om) => do
    let nextIdx ← stage2SwapPreAdvanceProg (cp_base, b_om)
    stage2SwapAdvanceNextProg (cp_base, nextIdx)

private theorem realizes_stage2SwapFinish :
    Realizes .exact stage2SwapFinishProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), (b, omRole)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          omRole < 3 ∧
          fs.dirtyIdx < fs.dirtyCount ∧
          (fs.dirtyIdx + 1 < fs.dirtyCount →
            fs.dirtyBuckets (fs.dirtyIdx + 1) < numBucketsWhp n_max ∧
            fs.rebSliceIdx (fs.dirtyBuckets (fs.dirtyIdx + 1)) < 3 * numBucketsWhp n_max))
      (fun _ _ => 0) := by
  unfold stage2SwapFinishProg
  have hpa := realizes_stage2SwapPreAdvance
  have han := realizes_stage2SwapAdvanceNext
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, ⟨b, omRole⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hom_lt, hdi_lt, hnxt_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    obtain ⟨hpa_res, _, _, hpa_step⟩ :=
      stage2SwapPreAdvanceProg_fastStep henv hb hom_lt hdi_lt hseed hrep (s := s)
    simp only [hpa_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hom_lt, hdi_lt⟩
    | exact ⟨c, U, V, w, n_max, _, henv, rfl, hpa_step.2.2.1, hnxt_fn⟩
  )

private theorem stage2SwapFinishProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hom_lt : fs.overmarsRole b < 3)
    (hdi_lt : fs.dirtyIdx < fs.dirtyCount)
    (hnxt_fn : fs.dirtyIdx + 1 < fs.dirtyCount →
      fs.dirtyBuckets (fs.dirtyIdx + 1) < numBucketsWhp n_max ∧
      fs.rebSliceIdx (fs.dirtyBuckets (fs.dirtyIdx + 1)) < 3 * numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage2SwapFinishProg ((mkWhpCoreParams c U V w n_max, base), (b, fs.overmarsRole b))
    let s' := (Memory.spec 0).clientState s prog
    let omIdx := fs.overmarsSliceIdx b
    let nextIdx := fs.dirtyIdx + 1
    let fsSwapped : FastState :=
      { fs with
        slices := Function.update fs.slices omIdx (resetBTreeSlice (fs.slices omIdx))
        dirtyIdx := nextIdx
        rebCandSalt := 0
        rebScanCursor := 0
        rebInsCount := 0
        rebCollision := 0 }
    let fsOut : FastState :=
      if fsSwapped.dirtyCount ≤ nextIdx then
        { fsSwapped with rebStage := 3, stageCursor := 0 }
      else
        let bNext := fsSwapped.dirtyBuckets nextIdx
        let rIdxNext := fsSwapped.rebSliceIdx bNext
        { fsSwapped with
          slices := Function.update fsSwapped.slices rIdxNext
            (resetBTreeSlice (fsSwapped.slices rIdxNext)) }
    memoryCost prog s ≤ 32 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  set fsSwapped : FastState :=
    { fs with
      slices := Function.update fs.slices (fs.overmarsSliceIdx b)
        (resetBTreeSlice (fs.slices (fs.overmarsSliceIdx b)))
      dirtyIdx := fs.dirtyIdx + 1
      rebCandSalt := 0
      rebScanCursor := 0
      rebInsCount := 0
      rebCollision := 0 }
  obtain ⟨hpa_res, hpa_mc, hpa_vp, hpa_step⟩ :=
    stage2SwapPreAdvanceProg_fastStep henv hb hom_lt hdi_lt hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (stage2SwapPreAdvanceProg ((cp, base), (b, fs.overmarsRole b)))
  obtain ⟨han_mc, han_vp, han_step⟩ :=
    stage2SwapAdvanceNextProg_fastStep (fsSw := fsSwapped) henv hnxt_fn
      hpa_step.2.1 hpa_step.2.2.1 (s := s1)
  dsimp only
  unfold stage2SwapFinishProg
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [cp, s1] at hpa_res hpa_mc han_mc ⊢
    rw [hpa_res]; omega
  · refine validProg_bind hpa_vp ?_; rw [hpa_res]; exact han_vp
  · rw [clientState_bind, hpa_res]
    exact hpa_step.trans han_step

/-- Post-scan phase of Stage 2 (`d = ((cp, base), b)`). -/
@[irreducible] def stage2PostScanGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let coll ← readHdrProg (base, hdrRebCollision)
    if coll = z0 then
      let cnt ← readBktFieldGenProg (((cp, base), b), z0)
      let cur ← readHdrProg (base, hdrRebScanCursor)
      if cnt ≤ cur then
        let omRole ← stage2SwapScalarsProg ((cp, base), b)
        stage2SwapFinishProg ((cp, base), (b, omRole))
      else
        pure ()
    else
      stage2CollisionResetProg ((cp, base), b)

/-- `Realizes .exact` certificate for `stage2PostScanGenProg`. -/
theorem realizes_stage2PostScanGen :
    Realizes .exact stage2PostScanGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fsScan : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fsScan s.mem ∧
          b < numBucketsWhp n_max ∧
          fsScan.liveRole b < 3 ∧
          fsScan.overmarsRole b < 3 ∧
          fsScan.liveRole b ≠ fsScan.overmarsRole b ∧
          fsScan.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          fsScan.rebCandSalt < sMaxWhp c n_max ∧
          fsScan.rebInsCount ≤ n_max ∧
          fsScan.dirtyIdx < fsScan.dirtyCount ∧
          (fsScan.dirtyIdx + 1 < fsScan.dirtyCount →
            fsScan.dirtyBuckets (fsScan.dirtyIdx + 1) < numBucketsWhp n_max ∧
            ({ fsScan with
                liveRole := Function.update fsScan.liveRole b (fsScan.rebRole b) } :
              FastState).rebSliceIdx (fsScan.dirtyBuckets (fsScan.dirtyIdx + 1)) <
              3 * numBucketsWhp n_max))
      (fun _ _ => 0) := by
  unfold stage2PostScanGenProg
  have hrh := realizes_readHdr
  have hrb := realizes_readBktFieldGen
  have hss := realizes_stage2SwapScalars
  have hsf := realizes_stage2SwapFinish
  have hcr := realizes_stage2CollisionReset
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fsScan, henv, rfl, hseed, hrep, hb, hlr_lt, hom_lt, hne_lr,
      hrIdx, hcand_lt, hins_le, hdi_lt, hnxt_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hh := fastMemHdrs hrep
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    have hcand_le : fsScan.rebCandSalt ≤ n_max := by omega
    obtain ⟨hcl_st, hcl_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCollision)
      (by dsimp [hdrRebCollision]; omega) (s := s)
    rw [hh.rebCollision] at hcl_res
    obtain ⟨h0_st, h0_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at h0_res
    obtain ⟨hcr_st, hcr_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    rw [hh.rebScanCursor] at hcr_res
    obtain ⟨hss_res, _, _, hss_step⟩ :=
      stage2SwapScalarsProg_fastStep henv hb ⟨hlr_lt, hom_lt, hne_lr⟩ hcand_le hins_le
        hseed hrep (s := s)
    simp only [hcl_st, hcl_res, h0_st, h0_res, hcr_st, hcr_res, hss_res] at *
    first
    | exact (by decide : 0 < 10)
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrRebCollision, hdrRebScanCursor]; omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | exact ⟨c, U, V, w, n_max, θ, fsScan, henv, rfl, hseed, hrep, hb, hrIdx, hcand_lt⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hss_step.2.1, hss_step.2.2.1,
        hb, hom_lt, hdi_lt, hnxt_fn⟩
  )

/-- `FastStateStep` specification for `stage2PostScanGenProg`. -/
theorem stage2PostScanGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fsScan : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrv : fsScan.liveRole b < 3 ∧ fsScan.overmarsRole b < 3 ∧
      fsScan.liveRole b ≠ fsScan.overmarsRole b)
    (hrIdx : fsScan.rebSliceIdx b < 3 * numBucketsWhp n_max)
    (hcand_lt : fsScan.rebCandSalt < sMaxWhp c n_max)
    (hins_le : fsScan.rebInsCount ≤ n_max)
    (hdi_lt : fsScan.dirtyIdx < fsScan.dirtyCount)
    (hnxt_fn : fsScan.dirtyIdx + 1 < fsScan.dirtyCount →
      fsScan.dirtyBuckets (fsScan.dirtyIdx + 1) < numBucketsWhp n_max ∧
      ({ fsScan with liveRole := Function.update fsScan.liveRole b (fsScan.rebRole b) } :
        FastState).rebSliceIdx (fsScan.dirtyBuckets (fsScan.dirtyIdx + 1)) <
        3 * numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fsScan s.mem) :
    let prog := stage2PostScanGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 76 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage2PostScan b fsScan) s s' := by
  have hth := henv.2.2.2.1
  have hh := fastMemHdrs hrep
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  have hcand_le : fsScan.rebCandSalt ≤ n_max := by omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hcl_st, hcl_res, hcl_mc, hcl_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCollision)
    (by dsimp [hdrRebCollision]; omega) (s := s)
  rw [hh.rebCollision] at hcl_res
  dsimp only
  unfold stage2PostScanGenProg; simp only [pure_bind]
  unfold epochTickStage2PostScan epochTickStage2AfterSwap epochTickStage2Swap; dsimp only
  by_cases hcnz : fsScan.rebCollision ≠ 0
  · rw [ite_eq_left hcnz]
    have hcnz' : ¬(fsScan.rebCollision = 0) := hcnz
    obtain ⟨hcr_mc, hcr_vp, hcr_step⟩ :=
      stage2CollisionResetProg_fastStep henv hb hrIdx hcand_lt hseed hrep (s := s)
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hcl_st, hcl_res, hcl_mc, ite_eq_right hcnz']
      dsimp only [cp] at hcr_mc ⊢; omega
    · refine validProg_bind hcl_vp ?_; rw [hcl_st, hcl_res, ite_eq_right hcnz']
      exact hcr_vp
    · rw [clientState_bind, hcl_st, hcl_res, ite_eq_right hcnz']
      exact hcr_step
  · rw [ite_eq_right hcnz]
    have hc0 : fsScan.rebCollision = 0 := Classical.not_not.mp hcnz
    obtain ⟨h0_st, h0_res, h0_mc, h0_vp⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at h0_res
    obtain ⟨hcr_st, hcr_res, hcr_mc, hcr_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    rw [hh.rebScanCursor] at hcr_res
    by_cases hdone_b : fsScan.bktCount b ≤ fsScan.rebScanCursor
    · rw [ite_eq_left hdone_b]
      obtain ⟨hss_res, hss_mc, hss_vp, hss_step⟩ :=
        stage2SwapScalarsProg_fastStep henv hb hrv hcand_le hins_le hseed hrep (s := s)
      set sSc := (Memory.spec 0).clientState s (stage2SwapScalarsProg ((cp, base), b))
      set fsSc : FastState :=
        { fsScan with
          liveRole := Function.update fsScan.liveRole b (fsScan.rebRole b)
          bktSalt := Function.update fsScan.bktSalt b fsScan.rebCandSalt
          liveInsCount := Function.update fsScan.liveInsCount b fsScan.rebInsCount
          overmarsActive := Function.update fsScan.overmarsActive b 0
          overmarsCursor := Function.update fsScan.overmarsCursor b 0
          overmarsInsCount := Function.update fsScan.overmarsInsCount b 0
          rebDoneFlag := Function.update fsScan.rebDoneFlag b 1 }
      obtain ⟨hsf_mc, hsf_vp, hsf_step⟩ :=
        stage2SwapFinishProg_fastStep (fs := fsSc) henv hb hrv.2.1 hdi_lt hnxt_fn
          hss_step.2.1 hss_step.2.2.1 (s := sSc)
      refine ⟨?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hcl_st, hcl_res, hcl_mc, ite_eq_left hc0]; simp only [memoryCost_bind]
        rw [h0_st, h0_res, h0_mc, hcr_st, hcr_res, hcr_mc, ite_eq_left hdone_b]
        simp only [memoryCost_bind]
        dsimp only [cp, sSc, fsSc] at hss_res hss_mc hsf_mc ⊢
        rw [hss_res]; omega
      · refine validProg_bind hcl_vp ?_; rw [hcl_st, hcl_res, ite_eq_left hc0]
        refine validProg_bind h0_vp ?_; rw [h0_st, h0_res]
        refine validProg_bind hcr_vp ?_; rw [hcr_st, hcr_res, ite_eq_left hdone_b]
        refine validProg_bind hss_vp ?_; rw [hss_res]; exact hsf_vp
      · rw [clientState_bind, hcl_st, hcl_res, ite_eq_left hc0,
          clientState_bind, h0_st, h0_res, clientState_bind, hcr_st, hcr_res,
          ite_eq_left hdone_b, clientState_bind, hss_res]
        exact hss_step.trans hsf_step
    · rw [ite_eq_right hdone_b]
      refine ⟨?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hcl_st, hcl_res, hcl_mc, ite_eq_left hc0]; simp only [memoryCost_bind]
        rw [h0_st, h0_res, h0_mc, hcr_st, hcr_res, hcr_mc, ite_eq_right hdone_b,
          memoryCost_pure]; omega
      · refine validProg_bind hcl_vp ?_; rw [hcl_st, hcl_res, ite_eq_left hc0]
        refine validProg_bind h0_vp ?_; rw [h0_st, h0_res]
        refine validProg_bind hcr_vp ?_; rw [hcr_st, hcr_res, ite_eq_right hdone_b]
        exact validProg_pure _
      · rw [clientState_bind, hcl_st, hcl_res, ite_eq_left hc0,
          clientState_bind, h0_st, h0_res, clientState_bind, hcr_st, hcr_res,
          ite_eq_right hdone_b, clientState_pure_whp]
        exact FastStateStep.refl hseed hrep

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end

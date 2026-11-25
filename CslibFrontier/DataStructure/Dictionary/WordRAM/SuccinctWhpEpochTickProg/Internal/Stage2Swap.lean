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

private theorem readHdr_large_spec {c U V w n_max base hdrOff val : ℕ} {s : Memory.State}
    (_henv : WhpLargeEnv c U V w n_max w base)
    (hoff : hdrOff < 32) (hval : s.mem (base + hdrOff) = val) :
    let prog := readHdrProg (base, hdrOff)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = val ∧
    memoryCost prog s = 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h := readHdrProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max) (base := base)
    (hdrOff := hdrOff) (by dsimp only [largeSpaceWhp]; omega) (s := s)
  exact ⟨h.1, h.2.1.trans hval, h.2.2⟩

private theorem bindRead_fastStep {α : Type} {c U V w n_max base c₁ c₂ : ℕ} {v : α}
    {θ : SeedWhp c U n_max} {fs' : FastState} {s : Memory.State}
    {p : Memory.Prog α} {k : α → Memory.Prog Unit}
    (hst : (Memory.spec 0).clientState s p = s)
    (hres : (Memory.spec 0).clientResult s p = v)
    (hmc : memoryCost p s ≤ c₁)
    (hvp : ValidProg w (base + largeSpaceWhp c U V w n_max) s p)
    (hk : memoryCost (k v) s ≤ c₂ ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (k v) ∧
      FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s (k v))) :
    memoryCost (p >>= k) s ≤ c₁ + c₂ ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s (p >>= k) ∧
    FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s (p >>= k)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst, hres]
    have := hk.1
    omega
  · refine validProg_bind hvp ?_
    rw [hst, hres]
    exact hk.2.1
  · rw [clientState_bind, hst, hres]
    exact hk.2.2

private theorem weakenCost {c U V w n_max base c₁ c₂ : ℕ}
    {θ : SeedWhp c U n_max} {fs' : FastState} {s : Memory.State} {p : Memory.Prog Unit}
    (h : memoryCost p s ≤ c₁ ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
      FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p))
    (hc : c₁ ≤ c₂ := by omega) :
    memoryCost p s ≤ c₂ ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
    FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p) :=
  ⟨le_trans h.1 hc, h.2⟩

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
  have hrs := realizes_readRebSliceIdxGen; have hrb := realizes_resetBTreeSliceGen
  have hrh := realizes_readHdr; have hzh := realizes_resetRebScanHdrs
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩; dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hrIdx, hcand_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨_, _, hrb_step⟩ := resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
    obtain ⟨hcd_st, hcd_res, _, _⟩ :=
      readHdr_large_spec henv (by decide) (fastMemHdrs hrb_step.2.2.1).rebCandSalt
    dsimp only at hcd_res
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
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
  have hrb := resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
  obtain ⟨hcd_st, hcd_res, hcd_mc, hcd_vp⟩ :=
    readHdr_large_spec henv (by decide) (fastMemHdrs hrb.2.2.2.2.1).rebCandSalt
  dsimp only at hcd_res
  have hzh := resetRebScanHdrsProg_fastStep henv (henv.fits_of_le_n_max (by omega))
    hrb.2.2.2.1 hrb.2.2.2.2.1 (cand := fs.rebCandSalt + 1)
  dsimp only
  unfold stage2CollisionResetProg
  simp only [pure_bind]
  exact weakenCost (bindRead_fastStep hrs_st hrs_res hrs_mc.le hrs_vp
    (seqUnitProg_fastStep ⟨hrb.1.le, hrb.2⟩
      (bindRead_fastStep hcd_st hcd_res hcd_mc.le hcd_vp hzh)))

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
  have hro := realizes_readRebAndOmRoleGen; have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩; dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    simp only [wp_large_M henv.2.2.2.1] at *
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
  have h3_le : 3 ≤ n_max := by
    have := henv.numBuckets_le_n_max
    have := (large_bounds_lt_n_max henv.2.2.2.1).1
    omega
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readRebAndOmRoleGenProg_spec henv hb hrep (s := s)
  rw [ite_eq_left ⟨by omega, by omega⟩] at hro_res
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 2 < 10)
      (by dsimp [FastState.rebRole]; omega) hseed hrep (val := fs.rebRole b) (s := s)
  simp only [setBktField] at hw1_step
  dsimp only
  unfold stage2SwapRolesProg
  simp only [pure_bind]
  refine ⟨by rw [clientResult_bind, hro_st, hro_res, clientResult_bind]; rfl, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hro_st, hro_res, hro_mc]
    simp only [memoryCost_pure]
    omega
  · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
    exact validProg_bind hw1_vp (validProg_pure _)
  · rw [clientState_bind, hro_st, hro_res, clientState_bind, clientState_pure_whp]; exact hw1_step

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
  have hrh := realizes_readHdr; have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩; dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1; rw [wp_large_M hth] at hb
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
  obtain ⟨hcd_st, hcd_res, hcd_mc, hcd_vp⟩ := readHdr_large_spec henv (by decide) hh.rebCandSalt
  obtain ⟨hin_st, hin_res, hin_mc, hin_vp⟩ := readHdr_large_spec henv (by decide) hh.rebInsCount
  have hw1 := writeBktFieldGenProg_fastStep henv hb (by decide : 1 < 10) hcand_le hseed hrep
    (val := fs.rebCandSalt) (s := s)
  simp only [setBktField] at hw1
  have hw2 := writeBktFieldGenProg_fastStep henv hb (by decide : 3 < 10) hins_le
    hw1.2.2.2.1 hw1.2.2.2.2.1 (val := fs.rebInsCount)
  simp only [setBktField] at hw2
  dsimp only
  unfold stage2SwapCountsProg
  simp only [pure_bind]
  exact weakenCost (bindRead_fastStep hcd_st hcd_res hcd_mc.le hcd_vp
    (bindRead_fastStep hin_st hin_res hin_mc.le hin_vp
      (seqUnitProg_fastStep ⟨hw1.1.le, hw1.2⟩ ⟨hw2.1.le, hw2.2⟩)))

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
  have hmb := realizes_mkBktMetaRt; have hsa := realizes_setOvermarsActRt
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩; dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1; rw [wp_large_M hth] at hb
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
  obtain ⟨hmb_st, hmb_res, hmb_mc, hmb_vp⟩ :=
    mkBktMetaRtProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  have hsa :=
    setOvermarsActRtProg_fastStep henv hb (Nat.zero_le _) hseed hrep (actVal := 0) (s := s)
  have hw8 := writeBktFieldGenProg_fastStep henv hb (by decide : 8 < 10) h1_le
    hsa.2.2.2.1 hsa.2.2.2.2.1 (val := 1)
  simp only [setBktField] at hw8
  dsimp only
  unfold stage2SwapClearOmProg
  simp only [pure_bind]
  exact weakenCost (bindRead_fastStep hmb_st hmb_res (le_of_eq hmb_mc) hmb_vp
    (seqUnitProg_fastStep ⟨hsa.1.le, hsa.2⟩ ⟨hw8.1.le, hw8.2⟩))

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
  have h1 := realizes_stage2SwapRoles; have h2 := realizes_stage2SwapCounts
  have h3 := realizes_stage2SwapClearOm
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    first | exact h.1 | exact h.2)

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
  obtain ⟨h1_res, h1_mc, h1_vp, h1_step⟩ :=
    stage2SwapRolesProg_fastStep henv hb hrv hseed hrep (s := s)
  obtain ⟨h2_mc, h2_vp, h2_step⟩ :=
    stage2SwapCountsProg_fastStep henv hb (by exact hcand_le) (by exact hins_le)
      h1_step.2.1 h1_step.2.2.1
  obtain ⟨h3_mc, h3_vp, h3_step⟩ :=
    stage2SwapClearOmProg_fastStep henv hb h2_step.2.1 h2_step.2.2.1
  dsimp only; unfold stage2SwapScalarsProg
  refine ⟨by rw [clientResult_bind, h1_res, clientResult_bind, clientResult_bind]; rfl, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]; omega
  · exact validProg_bind h1_vp (validProg_bind h2_vp (validProg_bind h3_vp (validProg_pure _)))
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
  have hrb := realizes_resetBTreeSliceGen; have hrh := realizes_readHdr
  have hwh := realizes_writeHdr; have hzh := realizes_resetRebScanHdrs
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, ⟨b, omRole⟩⟩; dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hom_lt, hdi_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have h3M_le := (large_index_bounds hth).2.2.2.2.1
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    have hdc_le := hrep.1
    have homIdx_lt : 3 * b + omRole < 3 * numBucketsWhp n_max := by omega
    obtain ⟨_, _, hrs1_step⟩ := resetBTreeSliceGenProg_fastStep henv homIdx_lt hseed hrep (s := s)
    obtain ⟨hdi_st, hdi_res, _, _⟩ :=
      readHdr_large_spec henv (by decide) (fastMemHdrs hrs1_step.2.2.1).dirtyIdx
    dsimp only at hdi_res; simp only [hdi_st, hdi_res] at *
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
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  have hdc_le := hrep.1
  have homIdx_lt : 3 * b + omRole < 3 * numBucketsWhp n_max := by omega
  obtain ⟨hrs1_mc, hrs1_vp, hrs1_step⟩ :=
    resetBTreeSliceGenProg_fastStep henv homIdx_lt hseed hrep (s := s)
  obtain ⟨hdi_st, hdi_res, hdi_mc, hdi_vp⟩ :=
    readHdr_large_spec henv (by decide) (fastMemHdrs hrs1_step.2.2.1).dirtyIdx
  dsimp only at hdi_res
  have hw := writeHdrStep henv (by dsimp [hdrDirtyIdx]; decide)
    (henv.fits_of_le_n_max (by omega)) (fun _ => by dsimp; omega)
    hrs1_step.2.1 hrs1_step.2.2.1 (hdrOff := hdrDirtyIdx) (val := fs.dirtyIdx + 1)
  obtain ⟨hzh_mc, hzh_vp, hzh_step⟩ := resetRebScanHdrsProg_fastStep henv
    (Nat.two_pow_pos w) hw.2.2.2.1 hw.2.2.2.2.1 (cand := 0)
  dsimp only
  unfold stage2SwapPreAdvanceProg
  simp only [pure_bind]
  refine ⟨by rw [clientResult_bind, clientResult_bind, hdi_st, hdi_res,
      clientResult_bind, clientResult_bind]; rfl, ?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    have := hw.1
    rw [hdi_st, hdi_res, hdi_mc]
    omega
  · refine validProg_bind hrs1_vp (validProg_bind hdi_vp ?_); rw [hdi_st, hdi_res]
    exact validProg_bind hw.2.1 (validProg_bind hzh_vp (validProg_pure _))
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
  have hrh := realizes_readHdr; have ht3 := realizes_tickToStage3
  have hrd := realizes_readDirtyBucketGen; have hrs := realizes_readRebSliceIdxGen
  have hrb := realizes_resetBTreeSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, nextIdx⟩; dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fsSw, henv, rfl, hrep, hnxt_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hdc_le := hrep.1
    obtain ⟨hdc_st, hdc_res, _, _⟩ :=
      readHdr_large_spec henv (by decide) (fastMemHdrs hrep).dirtyCount
    simp only [hdc_st, hdc_res] at *
    first
    | exact henv.two_le_w
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
  obtain ⟨hdc_st, hdc_res, hdc_mc, hdc_vp⟩ :=
    readHdr_large_spec henv (by decide) (fastMemHdrs hrep).dirtyCount
  dsimp only; unfold stage2SwapAdvanceNextProg
  by_cases hall : fsSw.dirtyCount ≤ nextIdx
  · rw [ite_eq_left hall]
    exact weakenCost (bindRead_fastStep hdc_st hdc_res hdc_mc.le hdc_vp
      (by rw [ite_eq_left hall]; exact tickToStage3Prog_fastStep henv hseed hrep (s := s)))
  · rw [ite_eq_right hall]
    have hlt_nxt : nextIdx < fsSw.dirtyCount := Nat.lt_of_not_le hall
    obtain ⟨hbN, hrN⟩ := hnxt_fn hlt_nxt
    obtain ⟨hrd_st, hrd_res, hrd_mc, hrd_vp⟩ :=
      readDirtyBucketGenProg_spec henv hlt_nxt hrep (s := s)
    obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ :=
      readRebSliceIdxGenProg_spec henv hbN hrep (s := s)
    have hrb := resetBTreeSliceGenProg_fastStep henv hrN hseed hrep (s := s)
    exact weakenCost (bindRead_fastStep hdc_st hdc_res hdc_mc.le hdc_vp (by
      rw [ite_eq_right hall]
      exact bindRead_fastStep hrd_st hrd_res hrd_mc.le hrd_vp
        (bindRead_fastStep hrs_st hrs_res hrs_mc.le hrs_vp ⟨hrb.1.le, hrb.2⟩)))

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
  have hpa := realizes_stage2SwapPreAdvance; have han := realizes_stage2SwapAdvanceNext
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, ⟨b, omRole⟩⟩; dsimp only at *
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
  obtain ⟨hpa_res, hpa_mc, hpa_vp, hpa_step⟩ :=
    stage2SwapPreAdvanceProg_fastStep henv hb hom_lt hdi_lt hseed hrep (s := s)
  obtain ⟨han_mc, han_vp, han_step⟩ :=
    stage2SwapAdvanceNextProg_fastStep henv (by exact hnxt_fn) hpa_step.2.1 hpa_step.2.2.1
  dsimp only
  unfold stage2SwapFinishProg
  refine ⟨?_, ?_, by rw [clientState_bind, hpa_res]; exact hpa_step.trans han_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hpa_res]
    omega
  · refine validProg_bind hpa_vp ?_
    rw [hpa_res]
    exact han_vp

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
  have hrh := realizes_readHdr; have hrb := realizes_readBktFieldGen
  have hss := realizes_stage2SwapScalars; have hsf := realizes_stage2SwapFinish
  have hcr := realizes_stage2CollisionReset
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩; dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fsScan, henv, rfl, hseed, hrep, hb, hlr_lt, hom_lt, hne_lr,
      hrIdx, hcand_lt, hins_le, hdi_lt, hnxt_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hh := fastMemHdrs hrep
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨hcl_st, hcl_res, _, _⟩ := readHdr_large_spec henv (by decide) hh.rebCollision
    obtain ⟨h0_st, h0_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at h0_res
    obtain ⟨hcr_st, hcr_res, _, _⟩ := readHdr_large_spec henv (by decide) hh.rebScanCursor
    obtain ⟨hss_res, _, _, hss_step⟩ :=
      stage2SwapScalarsProg_fastStep henv hb ⟨hlr_lt, hom_lt, hne_lr⟩ (by omega) hins_le
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
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  obtain ⟨hcl_st, hcl_res, hcl_mc, hcl_vp⟩ :=
    readHdr_large_spec henv (by decide) hh.rebCollision
  dsimp only
  unfold stage2PostScanGenProg
  simp only [pure_bind]
  unfold epochTickStage2PostScan epochTickStage2AfterSwap epochTickStage2Swap; dsimp only
  by_cases hcnz : fsScan.rebCollision ≠ 0
  · rw [ite_eq_left hcnz]
    exact weakenCost (bindRead_fastStep hcl_st hcl_res hcl_mc.le hcl_vp (by
      rw [ite_eq_right hcnz]
      exact stage2CollisionResetProg_fastStep henv hb hrIdx hcand_lt hseed hrep (s := s)))
  · rw [ite_eq_right hcnz]
    have hc0 : fsScan.rebCollision = 0 := Classical.not_not.mp hcnz
    obtain ⟨h0_st, h0_res, h0_mc, h0_vp⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at h0_res
    obtain ⟨hcr_st, hcr_res, hcr_mc, hcr_vp⟩ :=
      readHdr_large_spec henv (by decide) hh.rebScanCursor
    by_cases hdone_b : fsScan.bktCount b ≤ fsScan.rebScanCursor
    · rw [ite_eq_left hdone_b]
      obtain ⟨hss_res, hss_mc, hss_vp, hss_step⟩ :=
        stage2SwapScalarsProg_fastStep henv hb hrv (by omega) hins_le hseed hrep (s := s)
      obtain ⟨hsf_mc, hsf_vp, hsf_step⟩ :=
        stage2SwapFinishProg_fastStep henv hb (by exact hrv.2.1) (by exact hdi_lt)
          (by exact hnxt_fn) hss_step.2.1 hss_step.2.2.1
      exact weakenCost (bindRead_fastStep hcl_st hcl_res hcl_mc.le hcl_vp (by
        rw [ite_eq_left hc0]
        exact bindRead_fastStep h0_st h0_res h0_mc.le h0_vp
          (bindRead_fastStep (c₂ := 72) hcr_st hcr_res hcr_mc.le hcr_vp (by
            rw [ite_eq_left hdone_b]
            refine ⟨?_, ?_, ?_⟩
            · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
              rw [hss_res]
              exact Nat.add_le_add hss_mc hsf_mc
            · refine validProg_bind hss_vp ?_
              rw [hss_res]
              exact hsf_vp
            · rw [clientState_bind, hss_res]
              exact hss_step.trans hsf_step))))
    · rw [ite_eq_right hdone_b]
      exact weakenCost (bindRead_fastStep hcl_st hcl_res hcl_mc.le hcl_vp (by
        rw [ite_eq_left hc0]
        exact bindRead_fastStep h0_st h0_res h0_mc.le h0_vp
          (bindRead_fastStep (c₂ := 0) hcr_st hcr_res hcr_mc.le hcr_vp (by
            rw [ite_eq_right hdone_b]
            exact ⟨by simp [memoryCost_pure], validProg_pure _, FastStateStep.refl hseed hrep⟩))))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end

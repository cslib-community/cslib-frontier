/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSmallCsrProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg
import CslibFrontier.Tactic.Realize

/-!
# Global Epoch Ticks and Fast-Mode Step `Memory.Prog` Subroutines

This module implements the parameter-free `Memory.Prog` subroutines and `Realizes .exact`
certificates for the global deamortized epoch-rebuild tick (`epochTick`) and combined fast-mode
operation dispatcher (`fastStepPure`) of `SuccinctWhpModel`:

1. `rebScanLoopGenProg`: `16`-coordinate Stage-2 candidate-salt scan loop via `Realizes.iterate₀`,
   refining `rebScanSteps c U n_max θ b 16 fs` in `O_c(1)` worst-case `memoryCost`.
2. `epochTickGenProg`: Stage `0 .. 5` deamortization (`epochTickStage0..4`) and epoch rollover,
   refining `epochTick c U n_max θ fs = some fs'` whenever `epochTickWillSucceed n_max fs` holds.
3. `checkEpochTickOkGenProg` and `fastStepPureGenProg`: `O(1)` read-only rollover pre-check and
   combined `fastQuery` / `fastDelete` / `fastInsert` + `epochTick` execution, guaranteeing
   `clientState s prog = s` whenever `fastStepPure c U n_max θ fs op = none`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastStepPureGenProg`, `fastOpCostWhp`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastStepPureGen`,
  `fastStepPureGenProg_spec`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

private structure FastMemHdrs (base c U V w n_max : ℕ) (fs : FastState) (mem : ℕ → ℕ) : Prop where
  dc_le : fs.dirtyCount ≤ qEpochWhp n_max
  mode : mem (base + hdrMode) = 1
  poolFreeTop : mem (base + hdrPoolFreeTop) = fs.poolFreeTop
  curEp : mem (base + hdrCurEp) = fs.curEp
  epochClock : mem (base + hdrEpochClock) = fs.epochClock
  rebStage : mem (base + hdrRebStage) = fs.rebStage
  stageCursor : mem (base + hdrStageCursor) = fs.stageCursor
  dirtyCount : mem (base + hdrDirtyCount) = fs.dirtyCount
  dirtyIdx : mem (base + hdrDirtyIdx) = fs.dirtyIdx
  rebCandSalt : mem (base + hdrRebCandSalt) = fs.rebCandSalt
  rebScanCursor : mem (base + hdrRebScanCursor) = fs.rebScanCursor
  rebInsCount : mem (base + hdrRebInsCount) = fs.rebInsCount
  rebCollision : mem (base + hdrRebCollision) = fs.rebCollision
  bktCount_read : ∀ b < numBucketsWhp n_max,
    readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w mem (16 * b) =
      fs.bktCount b

private theorem FastMemRep.hdrs {base c U V w n_max : ℕ} {fs : FastState} {mem : ℕ → ℕ}
    (hrep : FastMemRep base c U V w n_max fs mem) :
    FastMemHdrs base c U V w n_max fs mem := by
  rcases hrep with ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    _, _, hbmeta, _⟩
  exact ⟨hdc_le, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    fun b hb => (hbmeta b hb).1⟩

/-- Read `(tr.nodeAlloc, tr.itemAlloc)` for buffer `ep ∈ {0, 1}` (`d = (base, ep)`). -/
@[irreducible] private def readBufAllocsProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (base, ep) => do
    let z0 ← pure 0
    if ep = z0 then
      let na ← readHdrProg (base, hdrBuf0NodeAlloc)
      let ia ← readHdrProg (base, hdrBuf0ItemAlloc)
      pure (na, ia)
    else
      let na ← readHdrProg (base, hdrBuf1NodeAlloc)
      let ia ← readHdrProg (base, hdrBuf1ItemAlloc)
      pure (na, ia)

private theorem realizes_readBufAllocs :
    Realizes .exact readBufAllocsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (base, _) _ => 0 < w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold readBufAllocsProg
  have hrh := realizes_readHdr
  realize
  all_goals (
    obtain ⟨_hw, hfit32⟩ := h
    exact hfit32.of_le (by dsimp [hdrBuf0NodeAlloc, hdrBuf0ItemAlloc,
      hdrBuf1NodeAlloc, hdrBuf1ItemAlloc]; omega)
  )

private theorem readBufAllocsProg_spec {c U V w n_max base ep : ℕ}
    {fs : FastState} {s : Memory.State}
    (_henv : WhpLargeEnv c U V w n_max w base)
    (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readBufAllocsProg (base, ep)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = ((fs.buf ep).nodeAlloc, (fs.buf ep).itemAlloc) ∧
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  unfold readBufAllocsProg; simp only [pure_bind]
  rcases hep with rfl | rfl
  · simp only [↓reduceIte]
    obtain ⟨hn_st, hn_res, hn_mc, hn_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf0NodeAlloc)
      (by dsimp [hdrBuf0NodeAlloc]; omega) (s := s)
    obtain ⟨hi_st, hi_res, hi_mc, hi_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf0ItemAlloc)
      (by dsimp [hdrBuf0ItemAlloc]; omega) (s := s)
    have hb0 := hrep.buf_rep (Or.inl rfl)
    have hna0 : s.mem (base + hdrBuf0NodeAlloc) = (fs.buf 0).nodeAlloc := hb0.2.2.1
    have hia0 : s.mem (base + hdrBuf0ItemAlloc) = (fs.buf 0).itemAlloc := hb0.2.2.2.1
    rw [hna0] at hn_res
    rw [hia0] at hi_res
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hn_st, clientState_bind, hi_st]; rfl
    · rw [clientResult_bind, hn_st, hn_res, clientResult_bind, hi_st, hi_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
      rw [hn_st, hn_mc, hi_mc]
    · refine validProg_bind hn_vp ?_; rw [hn_st]
      refine validProg_bind hi_vp ?_; rw [hi_st]; exact validProg_pure _
  · simp only [one_ne_zero, ↓reduceIte]
    obtain ⟨hn_st, hn_res, hn_mc, hn_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf1NodeAlloc)
      (by dsimp [hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega) (s := s)
    obtain ⟨hi_st, hi_res, hi_mc, hi_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf1ItemAlloc)
      (by dsimp [hdrBuf1ItemAlloc]; omega) (s := s)
    have hb1 := hrep.buf_rep (Or.inr rfl)
    have hna1 : s.mem (base + hdrBuf1NodeAlloc) = (fs.buf 1).nodeAlloc := hb1.2.2.1
    have hia1 : s.mem (base + hdrBuf1ItemAlloc) = (fs.buf 1).itemAlloc := hb1.2.2.2.1
    rw [hna1] at hn_res
    rw [hia1] at hi_res
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hn_st, clientState_bind, hi_st]; rfl
    · rw [clientResult_bind, hn_st, hn_res, clientResult_bind, hi_st, hi_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
      rw [hn_st, hn_mc, hi_mc]
    · refine validProg_bind hn_vp ?_; rw [hn_st]
      refine validProg_bind hi_vp ?_; rw [hi_st]; exact validProg_pure _

private theorem bufClearStepsGenProg_fastStep {c U V w n_max base ep k : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hclr : ClearableBufTrie (fs.buf ep))
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := bufClearStepsGenProg (((mkWhpCoreParams c U V w n_max, base), ep), k)
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufClearSteps k (fs.buf ep)
    memoryCost prog s ≤ 15 * k ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := Function.update fs.buf ep tr' } s s' := by
  obtain ⟨hfr, hmc, hvp, hrep_tr', hbfr⟩ :=
    bufClearStepsGenProg_spec henv hep (hrep.buf_rep hep) hclr (k := k) (s := s)
  exact ⟨hmc, hvp, fastStep_of_bufEpFrame henv.2.1 hep hfr hseed hrep hrep_tr' hbfr⟩

/-! ## Section 1: Stage-2 Candidate-Salt Scan Loop (`rebScanLoopGenProg`) -/

/-- Precondition for `rebScanOneProg` (`p = (((wp, base), b), ())`). -/
private def RebScanOnePre (w : ℕ) :
    ((WhpParams × ℕ) × ℕ) × Unit → Memory.State → Prop
  | (((wp, base), b), _), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      b < numBucketsWhp n_max ∧
      (fs.curEp = 0 ∨ fs.curEp = 1) ∧
      fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max) ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) ∧
      (fs.rebCollision = 0 →
        fs.rebScanCursor < n_max ∧
        fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
        ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)

/-- Commit a non-colliding Stage-2 insertion into `rIdx` (`d = ((((cp, base), rIdx), fp), cur)`). -/
@[irreducible] private def rebScanCommitNoneProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), rIdx), fp), cur) => do
    btreeInsertGenProg ((((cp, base), rIdx), fp), cur)
    let ins ← readHdrProg (base, hdrRebInsCount)
    let cur1 ← pure (cur + 1)
    let ins1 ← pure (ins + 1)
    writeHdrProg ((base, hdrRebScanCursor), cur1)
    writeHdrProg ((base, hdrRebInsCount), ins1)

private theorem realizes_rebScanCommitNone :
    Realizes .exact rebScanCommitNoneProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), rIdx), fp), cur) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (rm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          rIdx < 3 * numBucketsWhp n_max ∧
          fp < 2 ^ fpBitsWhp n_max ∧
          cur < totalLocalCoordsWhp n_max ∧
          fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max fs.rebInsCount (fs.slices rIdx) rm)
      (fun _ _ => 0) := by
  unfold rebScanCommitNoneProg
  have hbi := realizes_btreeInsertGen
  have hrh := realizes_readHdr
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, rIdx⟩, fp⟩, cur⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hrIdx, hfp_lt,
      hcur_tl, hins_lt, hv_r⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have htl_lt := (large_bounds_lt_n_max hth).2.2.1
    have h8L_lt := (large_bounds_lt_n_max hth).2.2.2.1
    have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
      have htl3 := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
      rw [two_pow_valLaneBitsWhp]; omega
    obtain ⟨_, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp_lt hcur_val (s := s)
    set s1 := (Memory.spec 0).clientState s
      (btreeInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), rIdx), fp), cur))
    obtain ⟨hi_st, hi_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebInsCount)
      (by dsimp [hdrRebInsCount]; omega) (s := s1)
    have hh1 := hbi_step.2.2.1.hdrs
    rw [hh1.rebInsCount] at hi_res
    simp only [hi_st, hi_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices rIdx, rm, henv, rfl,
        hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp_lt, hcur_val⟩
  )

private theorem rebScanCommitNoneProg_fastStep {c U V w n_max base rIdx fp cur : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {rm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrIdx : rIdx < 3 * numBucketsWhp n_max)
    (hfp_lt : fp < 2 ^ fpBitsWhp n_max)
    (hcur_tl : cur < totalLocalCoordsWhp n_max)
    (hins_lt : fs.rebInsCount < 8 * (slabScale n_max) ^ 12)
    (hv_r : ValidWhpSlice n_max fs.rebInsCount (fs.slices rIdx) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := rebScanCommitNoneProg ((((mkWhpCoreParams c U V w n_max, base), rIdx), fp), cur)
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices rIdx) fp cur
    memoryCost prog s ≤ 2445 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices rIdx sl'
        rebScanCursor := cur + 1
        rebInsCount := fs.rebInsCount + 1 } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have htl_lt := (large_bounds_lt_n_max hth).2.2.1
  have h8L_lt := (large_bounds_lt_n_max hth).2.2.2.1
  have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
    have htl3 := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
    rw [two_pow_valLaneBitsWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    btreeInsertGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp_lt hcur_val (s := s)
  set s1 := (Memory.spec 0).clientState s (btreeInsertGenProg ((((cp, base), rIdx), fp), cur))
  set sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    (fs.slices rIdx) fp cur
  set fs1 : FastState := { fs with slices := Function.update fs.slices rIdx sl' }
  obtain ⟨hi_st, hi_res, hi_mc, hi_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebInsCount)
    (by dsimp [hdrRebInsCount]; omega) (s := s1)
  have hh1 := hbi_step.2.2.1.hdrs
  rw [hh1.rebInsCount] at hi_res
  dsimp only [fs1] at hi_res
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
    (by dsimp [hdrRebScanCursor]; decide) (henv.fits_of_le_n_max (by omega))
    (fun h => by dsimp [hdrRebScanCursor] at h; omega)
    hbi_step.2.1 hbi_step.2.2.1 (hdrOff := hdrRebScanCursor) (val := cur + 1) (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebScanCursor), cur + 1))
  set fs2 : FastState := { fs1 with rebScanCursor := cur + 1 }
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ := writeHdrProg_fastStep (fs := fs2) henv
    (by dsimp [hdrRebInsCount]; decide) (henv.fits_of_le_n_max (by omega))
    (fun h => by dsimp [hdrRebInsCount] at h; omega)
    hw1_step.2.1 hw1_step.2.2.1 (hdrOff := hdrRebInsCount) (val := fs.rebInsCount + 1) (s := s2)
  dsimp only
  unfold rebScanCommitNoneProg; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (btreeInsertGenProg ((((cp, base), rIdx), fp), cur) >>= fun _ =>
        readHdrProg (base, hdrRebInsCount) >>= fun ins =>
        writeHdrProg ((base, hdrRebScanCursor), cur + 1) >>= fun _ =>
        writeHdrProg ((base, hdrRebInsCount), ins + 1)) =
      (Memory.spec 0).clientState s2
        (writeHdrProg ((base, hdrRebInsCount), fs.rebInsCount + 1)) := by
    rw [clientState_bind, clientState_bind, hi_st, hi_res, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, (hbi_step.trans hw1_step).trans hw2_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hi_st, hi_res, hi_mc]
    dsimp only [s1, s2, cp] at hbi_mc hw1_mc hw2_mc ⊢
    omega
  · refine validProg_bind hbi_vp ?_
    refine validProg_bind hi_vp ?_; rw [hi_st, hi_res]
    exact validProg_bind hw1_vp hw2_vp

/-- Lookup and insert coordinate `cur` into `rebSlice[b]` (`d = (((wp, base), b), cur)`). -/
@[irreducible] private def rebScanInsertCoordProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), cur) => do
    let z1 ← pure 1
    let cand ← readHdrProg (base, hdrRebCandSalt)
    let fp ← fpAtGenProg ((((wp, base), cand), b), cur)
    let rIdx ← readRebSliceIdxGenProg ((wp.1, base), b)
    let lk ← btreeLookupGenProg (((wp.1, base), rIdx), fp)
    if lk.1 = z1 then
      writeHdrProg ((base, hdrRebCollision), z1)
    else
      rebScanCommitNoneProg ((((wp.1, base), rIdx), fp), cur)

private theorem realizes_rebScanInsertCoord :
    Realizes .exact rebScanInsertCoordProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), cur) s =>
        RebScanOnePre w (((wp, base), b), ()) s ∧
        s.mem (base + hdrRebCollision) = 0 ∧
        cur < readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b))
      (fun _ _ => 0) := by
  unfold rebScanInsertCoordProg
  have hrh := realizes_readHdr
  have hfp := realizes_fpAtGen
  have hrs := realizes_readRebSliceIdxGen
  have hbl := realizes_btreeLookupGen
  have hwh := realizes_writeHdr
  have hcn := realizes_rebScanCommitNone
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, cur⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hb, hce_or, hrIdx,
      hcnt_le, hq_all, hbp_v, hcoll_fn⟩, hmc0, hcur_lt0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hh := hrep.hdrs
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rw [hcp_eq, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth] at hcur_lt0
    rw [hh.bktCount_read b hb] at hcur_lt0
    have hcoll0 : fs.rebCollision = 0 := hh.rebCollision.symm.trans hmc0
    obtain ⟨_, hins_lt, rm, hv_r⟩ := hcoll_fn hcoll0
    have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt0.trans_le hcnt_le
    have hbp_cur : capFrontWhp n_max ≤ cur → fs.backPtr b (cur - capFrontWhp n_max) <
        poolSizeWhp n_max := fun hcf => hbp_v _ (by omega)
    obtain ⟨hcs_st, hcs_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s)
    rw [hh.rebCandSalt] at hcs_res
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpAtGenProg_spec henv hseed hrep hb hcur_tot hbp_cur (salt := fs.rebCandSalt) (s := s)
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    have hfp_lt := fpAt_lt θ fs fs.rebCandSalt b cur
    obtain ⟨hbl_st, _, _, _⟩ :=
      btreeLookupGenProg_spec henv hrIdx hins_lt.le (hrep.slice_rep hrIdx) hv_r hfp_lt (s := s)
    simp only [hcp_eq] at *
    simp only [hcs_st, hcs_res, hfp_st, hfp_res, hrs_st, hrs_res, hbl_st, wp_large_M hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, fun p _ => hq_all p,
        hb, hcur_tot, hbp_cur⟩
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices (fs.rebSliceIdx b), rm,
        henv, rfl, hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp_lt⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hrIdx, hfp_lt,
        hcur_tot, hins_lt, hv_r⟩
  )

/-- In-bounds branch (`cur < bktCount b`) of `rebScanOneProg` (`d = (((wp, base), b), cur)`). -/
@[irreducible] private def rebScanInBoundsProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), cur) => do
    let z1 ← pure 1
    let z2 ← pure 2
    let st ← readFastLocGenProg (((wp.1, base), b), cur)
    let oldEp ← readOldEpProg base
    let tagOld ← pure (z2 + oldEp)
    if st = z1 ∨ st = tagOld then
      rebScanInsertCoordProg (((wp, base), b), cur)
    else
      let cur1 ← pure (cur + 1)
      writeHdrProg ((base, hdrRebScanCursor), cur1)

private theorem realizes_rebScanInBounds :
    Realizes .exact rebScanInBoundsProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), cur) s =>
        RebScanOnePre w (((wp, base), b), ()) s ∧
        s.mem (base + hdrRebCollision) = 0 ∧
        cur = s.mem (base + hdrRebScanCursor) ∧
        cur < readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b))
      (fun _ _ => 0) := by
  unfold rebScanInBoundsProg
  have hrl := realizes_readFastLocGen
  have hro := realizes_readOldEp
  have hic := realizes_rebScanInsertCoord
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, cur⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hb, hce_or, hrIdx,
      hcnt_le, hq_all, hbp_v, hcoll_fn⟩, hmc0, hcur_eq0, hcur_lt0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hh := hrep.hdrs
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rw [hcp_eq, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth] at hcur_lt0
    have hbm0 := hh.bktCount_read b hb
    rw [hbm0] at hcur_lt0
    have hcoll0 : fs.rebCollision = 0 := hh.rebCollision.symm.trans hmc0
    obtain ⟨hcur_n, hins_lt, rm, hv_r⟩ := hcoll_fn hcoll0
    rw [hh.rebScanCursor] at hcur_eq0
    have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt0.trans_le hcnt_le
    obtain ⟨hrl_st, _, _, _⟩ := readFastLocGenProg_spec henv hb hcur_tot hrep (s := s)
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce_or
      hh.curEp (s := s)
    have hfit_old : Fits w (2 + fs.oldEp) := by
      have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
      have hold : fs.oldEp ≤ 1 := by rcases hce_or with hc | hc <;> simp [FastState.oldEp, hc]
      change 2 + fs.oldEp < 2 ^ w; omega
    simp only [hcp_eq] at *
    simp only [hrl_st, hro_st, hro_res] at *
    try simp only [wp_large_M hth, wp_large_totalLoc hth, wp_large_offBktMeta hth,
      wp_large_globalPtrBits hth, wp_large_w hth] at *
    first
    | exact h2w
    | exact hb
    | exact hcur_tot
    | exact hmc0
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrCurEp, hdrRebScanCursor]; decide)
    | exact hfit_old
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hce_or, hrIdx,
        hcnt_le, hq_all, hbp_v, hcoll_fn⟩
    | (rw [hbm0]; exact hcur_lt0)
  )

/-- Single coordinate step of Stage-2 candidate-salt scan (`p = (((wp, base), b), ())`). -/
private def rebScanOneProg : ((WhpParams × ℕ) × ℕ) × Unit → Memory.Prog Unit
  | (((wp, base), b), _) => do
    let z0 ← pure 0
    let addrC ← pure (base + hdrRebCollision)
    let coll ← Memory.read addrC
    if coll = z0 then
      let cur ← readHdrProg (base, hdrRebScanCursor)
      let cnt ← readBktFieldGenProg (((wp.1, base), b), z0)
      if cur < cnt then
        rebScanInBoundsProg (((wp, base), b), cur)
      else
        let cur1 ← pure (cur + 1)
        writeHdrProg ((base, hdrRebScanCursor), cur1)
    else
      pure ()

private theorem memoryCost_rebScanOneProg_pos (p : ((WhpParams × ℕ) × ℕ) × Unit)
    (s : Memory.State) :
    1 ≤ memoryCost (rebScanOneProg p) s := by
  rcases p with ⟨⟨⟨wp, base⟩, b⟩, ⟨⟩⟩
  unfold rebScanOneProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 1 ≤ 1 + _
  omega

private theorem realizes_rebScanOne :
    Realizes .exact rebScanOneProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × Unit))
      (WordEncoding.encode (α := Unit))
      RebScanOnePre
      (fun _ _ => 0) := by
  unfold rebScanOneProg
  have hrh := realizes_readHdr
  have hrb := realizes_readBktFieldGen
  have hib := realizes_rebScanInBounds
  have hwh := realizes_writeHdr
  have hcs_m : ∀ a (s' : Memory.State), (Memory.spec 0).clientState s' (Memory.read a) = s' :=
    fun _ _ => rfl
  have hcr_m : ∀ a (s' : Memory.State),
      (Memory.spec 0).clientResult s' (Memory.read a) = s'.mem a :=
    fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, ⟨⟩⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hb, hce_or, hrIdx,
      hcnt_le, hq_all, hbp_v, hcoll_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hh := hrep.hdrs
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hcur_st, hcur_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    rw [hh.rebScanCursor] at hcur_res
    obtain ⟨h0_st, h0_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at h0_res
    have hbm0 := hh.bktCount_read b hb
    simp only [hcp_eq] at *
    simp only [hcs_m, hcr_m, hcur_st, hcur_res, h0_st, h0_res] at *
    try simp only [wp_large_M hth, wp_large_offBktMeta hth, wp_large_globalPtrBits hth,
      wp_large_w hth] at *
    first
    | exact (by decide : 0 < 10)
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrRebCollision, hdrRebScanCursor]; decide)
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hce_or, hrIdx,
        hcnt_le, hq_all, hbp_v, hcoll_fn⟩
    | exact hh.rebScanCursor.symm
    | (rw [hbm0]; exact (by assumption : fs.rebScanCursor < fs.bktCount b))
    | exact (by assumption : s.mem (base + hdrRebCollision) = 0)
    | (have hmc0 : s.mem (base + hdrRebCollision) = 0 := by assumption
       have hcoll0 : fs.rebCollision = 0 := hh.rebCollision.symm.trans hmc0
       have hcur_n := (hcoll_fn hcoll0).1
       exact henv.fits_of_le_n_max (by omega))
  )

private theorem rebScanOneProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (_hq_all : ∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (hcoll_fn : fs.rebCollision = 0 →
      fs.rebScanCursor < n_max ∧
      fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := rebScanOneProg (((mkWhpParams c U V w n_max, base), b), ())
    let s' := (Memory.spec 0).clientState s prog
    let fs1 := rebScanSteps c U n_max θ b 1 fs
    memoryCost prog s ≤ 2 * hashEvalCostWhp c + 2740 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs1 s s' ∧
    fs1.curEp = fs.curEp ∧
    fs1.rebSliceIdx b = fs.rebSliceIdx b ∧
    fs1.bktCount b = fs.bktCount b ∧
    fs1.quotArr = fs.quotArr ∧
    fs1.backPtr = fs.backPtr ∧
    (fs1.rebCollision = 0 →
      fs.rebCollision = 0 ∧
      fs1.rebScanCursor = fs.rebScanCursor + 1 ∧
      fs1.rebInsCount ≤ fs.rebInsCount + 1 ∧
      ∃ rm1, ValidWhpSlice n_max fs1.rebInsCount (fs1.slices (fs1.rebSliceIdx b)) rm1) := by
  have hth := henv.2.2.2.1
  have hh := hrep.hdrs
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hc_st : (Memory.spec 0).clientState s (Memory.read (base + hdrRebCollision)) = s := rfl
  have hc_res : (Memory.spec 0).clientResult s (Memory.read (base + hdrRebCollision)) =
      fs.rebCollision := hh.rebCollision
  have hc_mc : memoryCost (Memory.read (base + hdrRebCollision)) s = 1 := rfl
  have hc_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (Memory.read (base + hdrRebCollision)) :=
    validProg_read (by dsimp [hdrRebCollision]; omega)
  dsimp only
  unfold rebScanOneProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  dsimp only [rebScanSteps]
  by_cases hcnz : fs.rebCollision ≠ 0
  · rw [ite_eq_left hcnz]
    have hcnz' : ¬(fs.rebCollision = 0) := hcnz
    have hs'_eq : (Memory.spec 0).clientState s
        (Memory.read (base + hdrRebCollision) >>= fun coll =>
          if coll = 0 then
            readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
            readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
            if cur < cnt then
              rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
            else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
          else pure ()) = s := by
      rw [clientState_bind, hc_st, hc_res, ite_eq_right hcnz']; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep, rfl, rfl, rfl, rfl, rfl,
      fun h0 => absurd h0 hcnz⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hc_st, hc_res, hc_mc, ite_eq_right hcnz', memoryCost_pure]; omega
    · refine validProg_bind hc_vp ?_; rw [hc_st, hc_res, ite_eq_right hcnz']
      exact validProg_pure _
  · rw [ite_eq_right hcnz]
    have hc0 : fs.rebCollision = 0 := Classical.not_not.mp hcnz
    obtain ⟨hcur_n, hins_lt, rm, hv_r⟩ := hcoll_fn hc0
    obtain ⟨hcur_st, hcur_res, hcur_mc, hcur_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    rw [hh.rebScanCursor] at hcur_res
    obtain ⟨h0_st, h0_res, h0_mc, h0_vp⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at h0_res
    set cur := fs.rebScanCursor
    by_cases hcur_lt : cur < fs.bktCount b
    · have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt.trans_le hcnt_le
      have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
        have htl3 := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
        rw [two_pow_valLaneBitsWhp]; omega
      obtain ⟨hrl_st, hrl_res, hrl_mc, hrl_vp⟩ :=
        readFastLocGenProg_spec henv hb hcur_tot hrep (s := s)
      obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
        (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce_or
        hh.curEp (s := s)
      by_cases hst_act : fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp
      · have hcond : cur < fs.bktCount b ∧
            (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp) := ⟨hcur_lt, hst_act⟩
        rw [ite_eq_left hcond]
        obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ := readHdrProg_spec (w := w)
          (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
          (by dsimp [hdrRebCandSalt]; omega) (s := s)
        rw [hh.rebCandSalt] at hcs_res
        have hbp_cur : capFrontWhp n_max ≤ cur → fs.backPtr b (cur - capFrontWhp n_max) <
            poolSizeWhp n_max := fun hcf => hbp_v _ (by omega)
        obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
          fpAtGenProg_spec henv hseed hrep hb hcur_tot hbp_cur (salt := fs.rebCandSalt) (s := s)
        obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ :=
          readRebSliceIdxGenProg_spec henv hb hrep (s := s)
        set fp := fs.fpAt c U n_max θ fs.rebCandSalt b cur
        have hfp_lt := fpAt_lt θ fs fs.rebCandSalt b cur
        obtain ⟨hbl_st, hbl_res, hbl_mc, hbl_vp⟩ :=
          btreeLookupGenProg_spec henv hrIdx hins_lt.le (hrep.slice_rep hrIdx) hv_r hfp_lt (s := s)
        have hlk_eq := hv_r.lookup_eq hth hins_lt.le hfp_lt
        cases hlk : btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.rebSliceIdx b)) fp with
        | some v_old =>
          have hrm_some : rm fp = some v_old := hlk_eq.symm.trans hlk
          rw [hrm_some] at hbl_res
          dsimp only at hbl_res ⊢
          obtain ⟨hwc_mc, hwc_vp, hwc_step⟩ := writeHdrProg_fastStep (fs := fs) henv
            (by dsimp [hdrRebCollision]; decide) (henv.fits_const (by decide))
            (fun h => by dsimp [hdrRebCollision] at h; omega)
            hseed hrep (hdrOff := hdrRebCollision) (val := 1) (s := s)
          have hs'_eq : (Memory.spec 0).clientState s
              (Memory.read (base + hdrRebCollision) >>= fun coll =>
                if coll = 0 then
                  readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
                  readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
                  if cur < cnt then
                    rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
                  else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
                else pure ()) =
              (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebCollision), 1)) := by
            rw [clientState_bind, hc_st, hc_res, ite_eq_left hc0,
              clientState_bind, hcur_st, hcur_res, clientState_bind, h0_st, h0_res,
              ite_eq_left hcur_lt]
            unfold rebScanInBoundsProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            rw [clientState_bind, hrl_st, hrl_res, clientState_bind, hro_st, hro_res,
              ite_eq_left hst_act]
            unfold rebScanInsertCoordProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            rw [clientState_bind, hcs_st, hcs_res, clientState_bind, hfp_st, hfp_res,
              clientState_bind, hrs_st, hrs_res, clientState_bind, hbl_st, hbl_res]
            rfl
          rw [hs'_eq]
          refine ⟨?_, ?_, hwc_step, rfl, rfl, rfl, rfl, rfl, fun h0 => by cases h0⟩
          · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hc_st, hc_res, hc_mc, ite_eq_left hc0]
            simp only [memoryCost_bind]
            rw [hcur_st, hcur_res, hcur_mc, h0_st, h0_res, h0_mc, ite_eq_left hcur_lt]
            unfold rebScanInBoundsProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hrl_st, hrl_res, hrl_mc, hro_st, hro_res, ite_eq_left hst_act]
            unfold rebScanInsertCoordProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hcs_st, hcs_res, hcs_mc, hfp_st, hfp_res, hrs_st, hrs_res, hbl_st, hbl_res]
            simp only [↓reduceIte]
            dsimp only [cp, cur, fp] at hro_mc hfp_mc hrs_mc hbl_mc hwc_mc ⊢
            omega
          · refine validProg_bind hc_vp ?_; rw [hc_st, hc_res, ite_eq_left hc0]
            refine validProg_bind hcur_vp ?_; rw [hcur_st, hcur_res]
            refine validProg_bind h0_vp ?_; rw [h0_st, h0_res, ite_eq_left hcur_lt]
            unfold rebScanInBoundsProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            refine validProg_bind hrl_vp ?_; rw [hrl_st, hrl_res]
            refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_left hst_act]
            unfold rebScanInsertCoordProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]
            refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
            refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
            refine validProg_bind hbl_vp ?_; rw [hbl_st, hbl_res]
            exact hwc_vp
        | none =>
          have hrm_none : rm fp = none := hlk_eq.symm.trans hlk
          rw [hrm_none] at hbl_res
          dsimp only at hbl_res ⊢
          obtain ⟨hcn_mc, hcn_vp, hcn_step⟩ :=
            rebScanCommitNoneProg_fastStep henv hrIdx hfp_lt hcur_tot hins_lt hv_r hseed hrep
              (s := s)
          have hv_r1 := (hv_r.insert_spec hth hins_lt.le hfp_lt hcur_val).2
          have hs'_eq : (Memory.spec 0).clientState s
              (Memory.read (base + hdrRebCollision) >>= fun coll =>
                if coll = 0 then
                  readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
                  readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
                  if cur < cnt then
                    rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
                  else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
                else pure ()) =
              (Memory.spec 0).clientState s
                (rebScanCommitNoneProg
                  ((((cp, base), fs.rebSliceIdx b), fp), cur)) := by
            rw [clientState_bind, hc_st, hc_res, ite_eq_left hc0,
              clientState_bind, hcur_st, hcur_res, clientState_bind, h0_st, h0_res,
              ite_eq_left hcur_lt]
            unfold rebScanInBoundsProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            rw [clientState_bind, hrl_st, hrl_res, clientState_bind, hro_st, hro_res,
              ite_eq_left hst_act]
            unfold rebScanInsertCoordProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            rw [clientState_bind, hcs_st, hcs_res, clientState_bind, hfp_st, hfp_res,
              clientState_bind, hrs_st, hrs_res, clientState_bind, hbl_st, hbl_res]
            rfl
          rw [hs'_eq]
          refine ⟨?_, ?_, hcn_step, rfl, rfl, rfl, rfl, rfl,
            fun _ => ⟨hc0, rfl, le_rfl, Function.update rm fp (some cur), ?_⟩⟩
          · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hc_st, hc_res, hc_mc, ite_eq_left hc0]
            simp only [memoryCost_bind]
            rw [hcur_st, hcur_res, hcur_mc, h0_st, h0_res, h0_mc, ite_eq_left hcur_lt]
            unfold rebScanInBoundsProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hrl_st, hrl_res, hrl_mc, hro_st, hro_res, ite_eq_left hst_act]
            unfold rebScanInsertCoordProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hcs_st, hcs_res, hcs_mc, hfp_st, hfp_res, hrs_st, hrs_res, hbl_st, hbl_res]
            simp only [zero_ne_one, ↓reduceIte]
            dsimp only [cp, cur, fp] at hro_mc hfp_mc hrs_mc hbl_mc hcn_mc ⊢
            omega
          · refine validProg_bind hc_vp ?_; rw [hc_st, hc_res, ite_eq_left hc0]
            refine validProg_bind hcur_vp ?_; rw [hcur_st, hcur_res]
            refine validProg_bind h0_vp ?_; rw [h0_st, h0_res, ite_eq_left hcur_lt]
            unfold rebScanInBoundsProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            refine validProg_bind hrl_vp ?_; rw [hrl_st, hrl_res]
            refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_left hst_act]
            unfold rebScanInsertCoordProg; dsimp only
            rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
            simp only [pure_bind]
            refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]
            refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
            refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
            refine validProg_bind hbl_vp ?_; rw [hbl_st, hbl_res]
            exact hcn_vp
          · change ValidWhpSlice n_max (fs.rebInsCount + 1)
              (Function.update fs.slices (fs.rebSliceIdx b) _ (fs.rebSliceIdx b)) _
            rw [Function.update_self]; exact hv_r1
      · have hncond : ¬(cur < fs.bktCount b ∧
            (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)) := fun h => hst_act h.2
        rw [ite_eq_right hncond]
        obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs) henv
          (by dsimp [hdrRebScanCursor]; decide) (henv.fits_of_le_n_max (by omega))
          (fun h => by dsimp [hdrRebScanCursor] at h; omega)
          hseed hrep (hdrOff := hdrRebScanCursor) (val := cur + 1) (s := s)
        have hs'_eq : (Memory.spec 0).clientState s
            (Memory.read (base + hdrRebCollision) >>= fun coll =>
              if coll = 0 then
                readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
                readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
                if cur < cnt then
                  rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
                else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
              else pure ()) =
            (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebScanCursor), cur + 1)) := by
          rw [clientState_bind, hc_st, hc_res, ite_eq_left hc0,
            clientState_bind, hcur_st, hcur_res, clientState_bind, h0_st, h0_res,
            ite_eq_left hcur_lt]
          unfold rebScanInBoundsProg; dsimp only
          rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
          simp only [pure_bind]
          rw [clientState_bind, hrl_st, hrl_res, clientState_bind, hro_st, hro_res,
            ite_eq_right hst_act]
        rw [hs'_eq]
        refine ⟨?_, ?_, hw_step, rfl, rfl, rfl, rfl, rfl,
          fun _ => ⟨hc0, rfl, Nat.le_succ _, rm, hv_r⟩⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hc_st, hc_res, hc_mc, ite_eq_left hc0]
          simp only [memoryCost_bind]
          rw [hcur_st, hcur_res, hcur_mc, h0_st, h0_res, h0_mc, ite_eq_left hcur_lt]
          unfold rebScanInBoundsProg; dsimp only
          rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hrl_st, hrl_res, hrl_mc, hro_st, hro_res, ite_eq_right hst_act]
          dsimp only [cp, cur] at hro_mc hw_mc ⊢; omega
        · refine validProg_bind hc_vp ?_; rw [hc_st, hc_res, ite_eq_left hc0]
          refine validProg_bind hcur_vp ?_; rw [hcur_st, hcur_res]
          refine validProg_bind h0_vp ?_; rw [h0_st, h0_res, ite_eq_left hcur_lt]
          unfold rebScanInBoundsProg; dsimp only
          rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
          simp only [pure_bind]
          refine validProg_bind hrl_vp ?_; rw [hrl_st, hrl_res]
          refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_right hst_act]
          exact hw_vp
    · have hncond : ¬(cur < fs.bktCount b ∧
          (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)) := fun h => hcur_lt h.1
      rw [ite_eq_right hncond]
      obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs) henv
        (by dsimp [hdrRebScanCursor]; decide) (henv.fits_of_le_n_max (by omega))
        (fun h => by dsimp [hdrRebScanCursor] at h; omega)
        hseed hrep (hdrOff := hdrRebScanCursor) (val := cur + 1) (s := s)
      have hs'_eq : (Memory.spec 0).clientState s
          (Memory.read (base + hdrRebCollision) >>= fun coll =>
            if coll = 0 then
              readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
              readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
              if cur < cnt then
                rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
              else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
            else pure ()) =
          (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebScanCursor), cur + 1)) := by
        rw [clientState_bind, hc_st, hc_res, ite_eq_left hc0,
          clientState_bind, hcur_st, hcur_res, clientState_bind, h0_st, h0_res,
          ite_eq_right hcur_lt]
      rw [hs'_eq]
      refine ⟨?_, ?_, hw_step, rfl, rfl, rfl, rfl, rfl,
        fun _ => ⟨hc0, rfl, Nat.le_succ _, rm, hv_r⟩⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hc_st, hc_res, hc_mc, ite_eq_left hc0]
        simp only [memoryCost_bind]
        rw [hcur_st, hcur_res, hcur_mc, h0_st, h0_res, h0_mc, ite_eq_right hcur_lt]
        dsimp only [cp, cur] at hw_mc ⊢; omega
      · refine validProg_bind hc_vp ?_; rw [hc_st, hc_res, ite_eq_left hc0]
        refine validProg_bind hcur_vp ?_; rw [hcur_st, hcur_res]
        refine validProg_bind h0_vp ?_; rw [h0_st, h0_res, ite_eq_right hcur_lt]
        exact hw_vp

/-- Parameter-free `iterate` wrapper for `rebScanOneProg` (`p = ((((wp, base), b), ()), k)`). -/
@[irreducible] private def rebScanLoopGenProg (p : (((WhpParams × ℕ) × ℕ) × Unit) × ℕ) :
    Memory.Prog Unit :=
  iterate rebScanOneProg p.1.1 p.2 p.1.2

private theorem realizes_rebScanLoopGen :
    Realizes .exact rebScanLoopGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × Unit) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w p s => iterationSafe rebScanOneProg RebScanOnePre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold rebScanLoopGenProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
    (WordEncoding.encode (α := Unit))
    realizes_rebScanOne
    memoryCost_rebScanOneProg_pos

private theorem rebScanSteps_one_trans {c U n_max : ℕ} (θ : SeedWhp c U n_max) (b k : ℕ)
    (fs : FastState) :
    rebScanSteps c U n_max θ b (k + 1) fs =
      rebScanSteps c U n_max θ b k (rebScanSteps c U n_max θ b 1 fs) := by
  dsimp only [rebScanSteps]
  by_cases hc : fs.rebCollision ≠ 0
  · rw [ite_eq_left hc, ite_eq_left hc]
    cases k with
    | zero => rfl
    | succ k' => dsimp only [rebScanSteps]; exact (ite_eq_left hc).symm
  · rw [ite_eq_right hc, ite_eq_right hc]

private theorem rebScanLoop_spec {c U V w n_max base b : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hb : b < numBucketsWhp n_max)
    (θ : SeedWhp c U n_max) :
    let d := ((mkWhpParams c U V w n_max, base), b)
    ∀ k (fs : FastState) (s : Memory.State),
      (fs.curEp = 0 ∨ fs.curEp = 1) →
      fs.rebSliceIdx b < 3 * numBucketsWhp n_max →
      fs.bktCount b ≤ totalLocalCoordsWhp n_max →
      (∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max) →
      (∀ idx < fs.bktCount b - capFrontWhp n_max, fs.backPtr b idx < poolSizeWhp n_max) →
      (fs.rebCollision = 0 →
        fs.rebScanCursor + k ≤ n_max ∧
        fs.rebInsCount + k ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm) →
      SeedWhpMemRep base c U w n_max θ s.mem →
      FastMemRep base c U V w n_max fs s.mem →
      let prog := rebScanLoopGenProg ((d, ()), k)
      let s' := (Memory.spec 0).clientState s prog
      iterationSafe rebScanOneProg RebScanOnePre w d k () s ∧
      memoryCost prog s ≤ k * (2 * hashEvalCostWhp c + 2740) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      FastStateStep base c U V w n_max θ (rebScanSteps c U n_max θ b k fs) s s' := by
  intro d k
  induction k with
  | zero =>
    intro fs s _ _ _ _ _ _ hseed hrep
    unfold rebScanLoopGenProg iterate
    exact ⟨trivial, Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩
  | succ k ih =>
    intro fs s hce hrIdx hcnt hq_all hbp_v hcoll_k hseed hrep
    have hcoll1 : fs.rebCollision = 0 →
        fs.rebScanCursor < n_max ∧
        fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
        ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm := by
      intro hc0
      obtain ⟨h1, h2, rm, hv⟩ := hcoll_k hc0
      exact ⟨by omega, by omega, rm, hv⟩
    have hpre : RebScanOnePre w (d, ()) s :=
      ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hce, hrIdx,
        hcnt, hq_all, hbp_v, hcoll1⟩
    obtain ⟨hmc1, hvp1, hstep1, hce1, hrIdx1, hcnt1, hq1, hbp1, hnext1⟩ :=
      rebScanOneProg_fastStep henv hb hce hrIdx hcnt hq_all hbp_v hcoll1 hseed hrep (s := s)
    set fs1 := rebScanSteps c U n_max θ b 1 fs
    set s1 := (Memory.spec 0).clientState s (rebScanOneProg (d, ()))
    have hcoll_rem : fs1.rebCollision = 0 →
        fs1.rebScanCursor + k ≤ n_max ∧
        fs1.rebInsCount + k ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ rm1, ValidWhpSlice n_max fs1.rebInsCount (fs1.slices (fs1.rebSliceIdx b)) rm1 := by
      intro hc1
      obtain ⟨hc0, hcur1, hins1, rm1, hv1⟩ := hnext1 hc1
      obtain ⟨hcur_k, hins_k, _⟩ := hcoll_k hc0
      exact ⟨by omega, by omega, rm1, hv1⟩
    obtain ⟨hsafe_k, hmc_k, hvp_k, hstep_k⟩ :=
      ih fs1 s1 (hce1 ▸ hce) (hrIdx1 ▸ hrIdx) (hcnt1 ▸ hcnt) (hq1 ▸ hq_all)
        (by rw [hcnt1, hbp1]; exact hbp_v) hcoll_rem hstep1.2.1 hstep1.2.2.1
    have hu_eq : (Memory.spec 0).clientResult s (rebScanOneProg (d, ())) = () := rfl
    dsimp only
    have hst_all : (Memory.spec 0).clientState s (rebScanLoopGenProg ((d, ()), k + 1)) =
        (Memory.spec 0).clientState s1 (rebScanLoopGenProg ((d, ()), k)) := by
      unfold rebScanLoopGenProg
      change (Memory.spec 0).clientState s
        (rebScanOneProg (d, ()) >>= fun u => iterate rebScanOneProg d k u) = _
      rw [clientState_bind, hu_eq]
    rw [hst_all, rebScanSteps_one_trans]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, hstep1.trans hstep_k⟩
    · rw [clientState_width, clientResult_width]; exact hsafe_k
    · have hmc_eq : memoryCost (rebScanLoopGenProg ((d, ()), k + 1)) s =
          memoryCost (rebScanOneProg (d, ())) s +
            memoryCost (rebScanLoopGenProg ((d, ()), k)) s1 := by
        unfold rebScanLoopGenProg
        change memoryCost (rebScanOneProg (d, ()) >>= fun u => iterate rebScanOneProg d k u) s = _
        simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rfl
      rw [hmc_eq]
      have hmc_k' : memoryCost (rebScanLoopGenProg ((d, ()), k)) s1 ≤
          k * (2 * hashEvalCostWhp c + 2740) := hmc_k
      dsimp only [d, s1] at hmc1 hmc_k' ⊢
      have hk_mul : (k + 1) * (2 * hashEvalCostWhp c + 2740) =
          (2 * hashEvalCostWhp c + 2740) + k * (2 * hashEvalCostWhp c + 2740) := by ring
      rw [hk_mul]; omega
    · have hvp_k' : ValidProg w (base + largeSpaceWhp c U V w n_max) s1
          (iterate rebScanOneProg d k ()) := by
        unfold rebScanLoopGenProg at hvp_k
        exact hvp_k
      unfold rebScanLoopGenProg
      exact validProg_bind hvp1 hvp_k'

/-! ## Section 2: Stage `0 .. 5` Deamortization and Rollover (`epochTickGenProg`) -/

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
  have hwh := realizes_writeHdr
  realize
  all_goals (
    obtain ⟨hw, hfit32⟩ := h
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | exact hfit32.of_le (by dsimp [hdrRebStage, hdrStageCursor, hdrDirtyCount]; omega)
  )

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
  obtain ⟨hmc1, hvp1, hst1⟩ := writeHdrProg_fastStep (fs := fs) henv
    (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
    (fun h => by dsimp [hdrRebStage] at h; omega) hseed hrep
    (hdrOff := hdrRebStage) (val := 1) (s := s)
  set s1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebStage), 1))
  set fs1 : FastState := { fs with rebStage := 1 }
  obtain ⟨hmc2, hvp2, hst2⟩ := writeHdrProg_fastStep (fs := fs1) henv
    (by dsimp [hdrStageCursor]; decide) (Nat.two_pow_pos w)
    (fun h => by dsimp [hdrStageCursor] at h; omega) hst1.2.1 hst1.2.2.1
    (hdrOff := hdrStageCursor) (val := 0) (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrStageCursor), 0))
  set fs2 : FastState := { fs1 with stageCursor := 0 }
  obtain ⟨hmc3, hvp3, hst3⟩ := writeHdrProg_fastStep (fs := fs2) henv
    (by dsimp [hdrDirtyCount]; decide) (Nat.two_pow_pos w)
    (fun _ => Nat.zero_le _) hst2.2.1 hst2.2.2.1
    (hdrOff := hdrDirtyCount) (val := 0) (s := s2)
  dsimp only
  unfold tickToStage1Prog; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (writeHdrProg ((base, hdrRebStage), 1) >>= fun _ =>
        writeHdrProg ((base, hdrStageCursor), 0) >>= fun _ =>
        writeHdrProg ((base, hdrDirtyCount), 0)) =
      (Memory.spec 0).clientState s2 (writeHdrProg ((base, hdrDirtyCount), 0)) := by
    rw [clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, validProg_bind hvp1 (validProg_bind hvp2 hvp3), (hst1.trans hst2).trans hst3⟩
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  dsimp only [s1, s2] at hmc1 hmc2 hmc3 ⊢; omega

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
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    rw [wp_large_M hth] at hb
    try simp only [wp_large_M hth] at *
    first
    | decide
    | exact hb
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

private theorem stage0ClearBucketFlagsProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage0ClearBucketFlagsProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        rebQueued := Function.update fs.rebQueued b 0
        rebDoneFlag := Function.update fs.rebDoneFlag b 0 } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hmc1, hvp1, hst1⟩ := writeBktFieldGenProg_fastStep (fs := fs) henv hb
    (by decide : 9 < 10) (Nat.zero_le _) hseed hrep (val := 0) (s := s)
  simp only [setBktField] at hst1
  set s1 := (Memory.spec 0).clientState s (writeBktFieldGenProg ((((cp, base), b), 9), 0))
  set fs1 : FastState := { fs with rebQueued := Function.update fs.rebQueued b 0 }
  obtain ⟨hmc2, hvp2, hst2⟩ := writeBktFieldGenProg_fastStep (fs := fs1) henv hb
    (by decide : 8 < 10) (Nat.zero_le _) hst1.2.1 hst1.2.2.1 (val := 0) (s := s1)
  simp only [setBktField] at hst2
  dsimp only
  unfold stage0ClearBucketFlagsProg; simp only [pure_bind]
  rw [clientState_bind]
  refine ⟨?_, validProg_bind hvp1 hvp2, hst1.trans hst2⟩
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  dsimp only [s1, cp] at hmc1 hmc2 ⊢; omega

/-- Execute Stage 0 of `epochTick` (`d = (cp, base)`). -/
@[irreducible] private def epochTickStage0GenProg :
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
        stage0ClearBucketFlagsProg ((cp, base), cs.2.1)
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

private theorem realizes_epochTickStage0Gen :
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
  have hro := realizes_readOldEp
  have hra := realizes_readBufAllocs
  have hrh := realizes_readHdr
  have hcs := realizes_bufCheckSlotGen
  have hcf := realizes_stage0ClearBucketFlags
  have ht1 := realizes_tickToStage1
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, rfl, hrep, hcore, hs0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hh := hrep.hdrs
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
    have hbo := hcore.bufOld_valid
    rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
    obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hcore.curEp_or
      hh.curEp (s := s)
    obtain ⟨hra_st, hra_res, _, _⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
    obtain ⟨hsc_st, hsc_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrStageCursor)
      (by dsimp [hdrStageCursor]; omega) (s := s)
    rw [hh.stageCursor] at hsc_res
    obtain ⟨hcs_st, hcs_res, _, _⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    simp only [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res, hcs_st] at *
    first
    | exact h2w
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
         have hhit : ((Memory.spec 0).clientResult s
           (bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), fs.oldEp),
             fs.stageCursor))).1 = 1 := by assumption
         rw [hchk] at hcs_res; rw [hcs_res] at hhit; cases hhit
       | some p =>
         rcases p with ⟨b₀, loc₀⟩
         rw [hchk] at hcs_res
         obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
         have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
         simp only [hcs_res] at *
         exact hb₀)
  )

private theorem epochTickStage0GenProg_fastStep {c U V w n_max base : ℕ}
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
  have hh := hrep.hdrs
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hc.curEp_or with h | h <;> simp [FastState.oldEp, h]
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hc.curEp_or
    hh.curEp (s := s)
  obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
  obtain ⟨hsc_st, hsc_res, hsc_mc, hsc_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrStageCursor)
    (by dsimp [hdrStageCursor]; omega) (s := s)
  rw [hh.stageCursor] at hsc_res
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
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
      obtain ⟨hcf_mc, hcf_vp, hcf_step⟩ :=
        stage0ClearBucketFlagsProg_fastStep henv hb₀ hseed hrep (s := s)
      set s_cf := (Memory.spec 0).clientState s (stage0ClearBucketFlagsProg ((cp, base), b₀))
      set fs_cf : FastState :=
        { fs with
          rebQueued := Function.update fs.rebQueued b₀ 0
          rebDoneFlag := Function.update fs.rebDoneFlag b₀ 0 }
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        obtain ⟨ht1_mc, ht1_vp, ht1_step⟩ :=
          tickToStage1Prog_fastStep (fs := fs_cf) henv hcf_step.2.1 hcf_step.2.2.1 (s := s_cf)
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage0ClearBucketFlagsProg ((cp, base), cs.2.1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
                else
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
              else tickToStage1Prog base) =
            (Memory.spec 0).clientState s_cf (tickToStage1Prog base) := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]; rw [clientState_bind, ite_eq_left hdone]
        rw [hs'_eq]
        refine ⟨?_, ?_, hcf_step.trans ht1_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte, memoryCost_bind]
          rw [ite_eq_left hdone]
          dsimp only [s_cf, cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hcf_mc ht1_mc ⊢; omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]
          refine validProg_bind hcf_vp ?_; rw [ite_eq_left hdone]; exact ht1_vp
      · rw [ite_eq_right hdone]
        obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs_cf) henv
          (by dsimp [hdrStageCursor]; decide) hcur1_fit
          (fun h => by dsimp [hdrStageCursor] at h; omega) hcf_step.2.1 hcf_step.2.2.1
          (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s_cf)
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage0ClearBucketFlagsProg ((cp, base), cs.2.1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
                else
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
              else tickToStage1Prog base) =
            (Memory.spec 0).clientState s_cf
              (writeHdrProg ((base, hdrStageCursor), fs.stageCursor + 1)) := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]; rw [clientState_bind, ite_eq_right hdone]
        rw [hs'_eq]
        refine ⟨?_, ?_, hcf_step.trans hw_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte, memoryCost_bind]
          rw [ite_eq_right hdone]
          dsimp only [s_cf, cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hcf_mc hw_mc ⊢; omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]
          refine validProg_bind hcf_vp ?_; rw [ite_eq_right hdone]; exact hw_vp
    | none =>
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        obtain ⟨ht1_mc, ht1_vp, ht1_step⟩ :=
          tickToStage1Prog_fastStep (fs := fs) henv hseed hrep (s := s)
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage0ClearBucketFlagsProg ((cp, base), cs.2.1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
                else
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
              else tickToStage1Prog base) =
            (Memory.spec 0).clientState s (tickToStage1Prog base) := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [ite_eq_left hdone]
        rw [hs'_eq]
        refine ⟨?_, ?_, ht1_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [ite_eq_left hdone]
          dsimp only [cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc ht1_mc ⊢; omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [ite_eq_left hdone]; exact ht1_vp
      · rw [ite_eq_right hdone]
        obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs) henv
          (by dsimp [hdrStageCursor]; decide) hcur1_fit
          (fun h => by dsimp [hdrStageCursor] at h; omega) hseed hrep
          (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s)
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage0ClearBucketFlagsProg ((cp, base), cs.2.1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
                else
                  if allocs.2 ≤ sc + 1 then tickToStage1Prog base
                  else writeHdrProg ((base, hdrStageCursor), sc + 1)
              else tickToStage1Prog base) =
            (Memory.spec 0).clientState s
              (writeHdrProg ((base, hdrStageCursor), fs.stageCursor + 1)) := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [ite_eq_right hdone]
        rw [hs'_eq]
        refine ⟨?_, ?_, hw_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [ite_eq_right hdone]
          dsimp only [cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hw_mc ⊢; omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [ite_eq_right hdone]; exact hw_vp
  · rw [ite_eq_right hlt]
    obtain ⟨ht1_mc, ht1_vp, ht1_step⟩ :=
      tickToStage1Prog_fastStep (fs := fs) henv hseed hrep (s := s)
    have hs'_eq : (Memory.spec 0).clientState s
        (readOldEpProg base >>= fun oldEp =>
          readBufAllocsProg (base, oldEp) >>= fun allocs =>
          readHdrProg (base, hdrStageCursor) >>= fun sc =>
          if sc < allocs.2 then
            bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
            if cs.1 = 1 then
              stage0ClearBucketFlagsProg ((cp, base), cs.2.1) >>= fun _ =>
              if allocs.2 ≤ sc + 1 then tickToStage1Prog base
              else writeHdrProg ((base, hdrStageCursor), sc + 1)
            else
              if allocs.2 ≤ sc + 1 then tickToStage1Prog base
              else writeHdrProg ((base, hdrStageCursor), sc + 1)
          else tickToStage1Prog base) =
        (Memory.spec 0).clientState s (tickToStage1Prog base) := by
      rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
        clientState_bind, hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]
    rw [hs'_eq]
    refine ⟨?_, ?_, ht1_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]; omega
    · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
      refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
      refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]; exact ht1_vp


/-! ### Stage 1 (`epochTickStage1GenProg`) -/

private theorem rebRole_lt_of_core {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hcore : CoreFastInv c U V n_max θ fs dict)
    {b : ℕ} (hb : b < numBucketsWhp n_max) :
    fs.rebRole b < 3 := by
  have ⟨h1, h2, h3⟩ := hcore.roles_valid b hb
  dsimp only [FastState.rebRole]; omega

private theorem rebSliceIdx_lt_of_core {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hcore : CoreFastInv c U V n_max θ fs dict)
    {b : ℕ} (hb : b < numBucketsWhp n_max) :
    fs.rebSliceIdx b < 3 * numBucketsWhp n_max := by
  have hr := rebRole_lt_of_core hcore hb
  dsimp only [FastState.rebSliceIdx]; omega

/-- Transition to Stage 3 (`rebStage := 3, stageCursor := 0`). -/
@[irreducible] private def tickToStage3Prog (base : ℕ) : Memory.Prog Unit := do
  let z0 ← pure 0
  let z3 ← pure 3
  writeHdrProg ((base, hdrRebStage), z3)
  writeHdrProg ((base, hdrStageCursor), z0)

private theorem realizes_tickToStage3 :
    Realizes .exact tickToStage3Prog
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w base _ => 2 ≤ w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold tickToStage3Prog
  have hwh := realizes_writeHdr
  realize
  all_goals (
    obtain ⟨h2w, hfit32⟩ := h
    have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
    first
    | (change 3 < 2 ^ w; omega)
    | exact hfit32.of_le (by dsimp [hdrRebStage, hdrStageCursor]; omega)
  )

private theorem tickToStage3Prog_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := tickToStage3Prog base
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with rebStage := 3, stageCursor := 0 } s s' := by
  obtain ⟨hmc1, hvp1, hst1⟩ := writeHdrProg_fastStep (fs := fs) henv
    (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
    (fun h => by dsimp [hdrRebStage] at h; omega) hseed hrep
    (hdrOff := hdrRebStage) (val := 3) (s := s)
  set s1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebStage), 3))
  set fs1 : FastState := { fs with rebStage := 3 }
  obtain ⟨hmc2, hvp2, hst2⟩ := writeHdrProg_fastStep (fs := fs1) henv
    (by dsimp [hdrStageCursor]; decide) (Nat.two_pow_pos w)
    (fun h => by dsimp [hdrStageCursor] at h; omega) hst1.2.1 hst1.2.2.1
    (hdrOff := hdrStageCursor) (val := 0) (s := s1)
  dsimp only
  unfold tickToStage3Prog; simp only [pure_bind]
  rw [clientState_bind]
  refine ⟨?_, validProg_bind hvp1 hvp2, hst1.trans hst2⟩
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  dsimp only [s1] at hmc1 hmc2 ⊢; omega

/-- Set `(rebCandSalt, rebScanCursor, rebInsCount, rebCollision) := (cand, 0, 0, 0)`
(`d = (base, cand)`). -/
@[irreducible] private def resetRebScanHdrsProg : ℕ × ℕ → Memory.Prog Unit
  | (base, cand) => do
    let z0 ← pure 0
    writeHdrProg ((base, hdrRebCandSalt), cand)
    writeHdrProg ((base, hdrRebScanCursor), z0)
    writeHdrProg ((base, hdrRebInsCount), z0)
    writeHdrProg ((base, hdrRebCollision), z0)

private theorem realizes_resetRebScanHdrs :
    Realizes .exact resetRebScanHdrsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (base, _) _ => 0 < w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold resetRebScanHdrsProg
  have hwh := realizes_writeHdr
  realize
  all_goals (
    obtain ⟨_, hfit32⟩ := h
    exact hfit32.of_le
      (by dsimp [hdrRebCandSalt, hdrRebScanCursor, hdrRebInsCount, hdrRebCollision]; omega)
  )

private theorem resetRebScanHdrsProg_fastStep {c U V w n_max base cand : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcand : Fits w cand)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := resetRebScanHdrsProg (base, cand)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        rebCandSalt := cand
        rebScanCursor := 0
        rebInsCount := 0
        rebCollision := 0 } s s' := by
  obtain ⟨hmc1, hvp1, hst1⟩ := writeHdrProg_fastStep (fs := fs) henv
    (by dsimp [hdrRebCandSalt]; decide) hcand
    (fun h => by dsimp [hdrRebCandSalt] at h; omega) hseed hrep
    (hdrOff := hdrRebCandSalt) (val := cand) (s := s)
  set s1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebCandSalt), cand))
  set fs1 : FastState := { fs with rebCandSalt := cand }
  obtain ⟨hmc2, hvp2, hst2⟩ := writeHdrProg_fastStep (fs := fs1) henv
    (by dsimp [hdrRebScanCursor]; decide) (Nat.two_pow_pos w)
    (fun h => by dsimp [hdrRebScanCursor] at h; omega) hst1.2.1 hst1.2.2.1
    (hdrOff := hdrRebScanCursor) (val := 0) (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebScanCursor), 0))
  set fs2 : FastState := { fs1 with rebScanCursor := 0 }
  obtain ⟨hmc3, hvp3, hst3⟩ := writeHdrProg_fastStep (fs := fs2) henv
    (by dsimp [hdrRebInsCount]; decide) (Nat.two_pow_pos w)
    (fun h => by dsimp [hdrRebInsCount] at h; omega) hst2.2.1 hst2.2.2.1
    (hdrOff := hdrRebInsCount) (val := 0) (s := s2)
  set s3 := (Memory.spec 0).clientState s2 (writeHdrProg ((base, hdrRebInsCount), 0))
  set fs3 : FastState := { fs2 with rebInsCount := 0 }
  obtain ⟨hmc4, hvp4, hst4⟩ := writeHdrProg_fastStep (fs := fs3) henv
    (by dsimp [hdrRebCollision]; decide) (Nat.two_pow_pos w)
    (fun h => by dsimp [hdrRebCollision] at h; omega) hst3.2.1 hst3.2.2.1
    (hdrOff := hdrRebCollision) (val := 0) (s := s3)
  dsimp only
  unfold resetRebScanHdrsProg; simp only [pure_bind]
  rw [clientState_bind, clientState_bind, clientState_bind]
  refine ⟨?_, validProg_bind hvp1 (validProg_bind hvp2 (validProg_bind hvp3 hvp4)),
    ((hst1.trans hst2).trans hst3).trans hst4⟩
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  dsimp only [s1, s2, s3] at hmc1 hmc2 hmc3 hmc4 ⊢; omega

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
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
    (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
    (fun h => by dsimp [hdrRebStage] at h; omega) hrs_step.2.1 hrs_step.2.2.1
    (hdrOff := hdrRebStage) (val := 2) (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebStage), 2))
  set fs2 : FastState := { fs1 with rebStage := 2 }
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ := writeHdrProg_fastStep (fs := fs2) henv
    (by dsimp [hdrDirtyIdx]; decide) (Nat.two_pow_pos w)
    (fun h => by dsimp [hdrDirtyIdx] at h; omega) hw1_step.2.1 hw1_step.2.2.1
    (hdrOff := hdrDirtyIdx) (val := 0) (s := s2)
  set s3 := (Memory.spec 0).clientState s2 (writeHdrProg ((base, hdrDirtyIdx), 0))
  set fs3 : FastState := { fs2 with dirtyIdx := 0 }
  obtain ⟨hzh_mc, hzh_vp, hzh_step⟩ :=
    resetRebScanHdrsProg_fastStep (fs := fs3) henv (Nat.two_pow_pos w)
      hw2_step.2.1 hw2_step.2.2.1 (cand := 0) (s := s3)
  dsimp only
  unfold stage1EnterStage2Prog; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (readDirtyBucketGenProg ((cp, base), 0) >>= fun b0' =>
        readRebSliceIdxGenProg ((cp, base), b0') >>= fun rIdx0' =>
        resetBTreeSliceGenProg ((cp, base), rIdx0') >>= fun _ =>
        writeHdrProg ((base, hdrRebStage), 2) >>= fun _ =>
        writeHdrProg ((base, hdrDirtyIdx), 0) >>= fun _ =>
        resetRebScanHdrsProg (base, 0)) =
      (Memory.spec 0).clientState s3 (resetRebScanHdrsProg (base, 0)) := by
    rw [clientState_bind, hd_st, hd_res, clientState_bind, hr_st, hr_res,
      clientState_bind, clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, ((hrs_step.trans hw1_step).trans hw2_step).trans hzh_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hd_st, hd_res, hd_mc, hr_st, hr_res, hr_mc]
    dsimp only [s1, s2, s3, cp, b0, rIdx0] at hrs_mc hw1_mc hw2_mc hzh_mc ⊢; omega
  · refine validProg_bind hd_vp ?_; rw [hd_st, hd_res]
    refine validProg_bind hr_vp ?_; rw [hr_st, hr_res]
    exact validProg_bind hrs_vp (validProg_bind hw1_vp (validProg_bind hw2_vp hzh_vp))

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
    have hh := hrep.hdrs
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
  have hh := hrep.hdrs
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
  · rw [ite_eq_left hdc0]
    obtain ⟨ht3_mc, ht3_vp, ht3_step⟩ := tickToStage3Prog_fastStep henv hseed hrep (s := s)
    have hs'_eq : (Memory.spec 0).clientState s
        (readHdrProg (base, hdrDirtyCount) >>= fun dc =>
          if dc = 0 then tickToStage3Prog base else stage1EnterStage2Prog (cp, base)) =
        (Memory.spec 0).clientState s (tickToStage3Prog base) := by
      rw [clientState_bind, hdc_st, hdc_res, ite_eq_left hdc0]
    rw [hs'_eq]
    refine ⟨?_, ?_, ht3_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hdc_st, hdc_res, hdc_mc, ite_eq_left hdc0]; omega
    · refine validProg_bind hdc_vp ?_; rw [hdc_st, hdc_res, ite_eq_left hdc0]; exact ht3_vp
  · rw [ite_eq_right hdc0]
    obtain ⟨hb0, hr0⟩ := hpos_fn (Nat.pos_of_ne_zero hdc0)
    obtain ⟨he2_mc, he2_vp, he2_step⟩ :=
      stage1EnterStage2Prog_fastStep henv (Nat.pos_of_ne_zero hdc0) hb0 hr0 hseed hrep (s := s)
    have hs'_eq : (Memory.spec 0).clientState s
        (readHdrProg (base, hdrDirtyCount) >>= fun dc =>
          if dc = 0 then tickToStage3Prog base else stage1EnterStage2Prog (cp, base)) =
        (Memory.spec 0).clientState s (stage1EnterStage2Prog (cp, base)) := by
      rw [clientState_bind, hdc_st, hdc_res, ite_eq_right hdc0]
    rw [hs'_eq]
    refine ⟨?_, ?_, he2_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hdc_st, hdc_res, hdc_mc, ite_eq_right hdc0]
      dsimp only [cp] at he2_mc ⊢; omega
    · refine validProg_bind hdc_vp ?_; rw [hdc_st, hdc_res, ite_eq_right hdc0]; exact he2_vp

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
    have hh1 := hw9_step.2.2.1.hdrs
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
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 9) >>= fun rq =>
          if rq = 0 then
            writeBktFieldGenProg ((((cp, base), b), 9), 1) >>= fun _ =>
            pushDirtyBucketGenProg ((cp, base), b)
          else pure ()) =
        (Memory.spec 0).clientState s1 (pushDirtyBucketGenProg ((cp, base), b)) := by
      rw [clientState_bind, h9_st, h9_res, ite_eq_left hrq0, clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, hw_step.trans hpd_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h9_st, h9_res, h9_mc, ite_eq_left hrq0]
      simp only [memoryCost_bind]
      dsimp only [s1, cp] at hw_mc hpd_mc ⊢; omega
    · refine validProg_bind h9_vp ?_; rw [h9_st, h9_res, ite_eq_left hrq0]
      exact validProg_bind hw_vp hpd_vp
  · rw [ite_eq_right hrq0]
    have hs'_eq : (Memory.spec 0).clientState s
        (readBktFieldGenProg (((cp, base), b), 9) >>= fun rq =>
          if rq = 0 then
            writeBktFieldGenProg ((((cp, base), b), 9), 1) >>= fun _ =>
            pushDirtyBucketGenProg ((cp, base), b)
          else pure ()) = s := by
      rw [clientState_bind, h9_st, h9_res, ite_eq_right hrq0]; rfl
    rw [hs'_eq]
    refine ⟨?_, ?_, FastStateStep.refl hseed hrep⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [h9_st, h9_res, h9_mc, ite_eq_right hrq0, memoryCost_pure]; omega
    · refine validProg_bind h9_vp ?_; rw [h9_st, h9_res, ite_eq_right hrq0]
      exact validProg_pure _

/-- Execute Stage 1 of `epochTick` (`d = (cp, base)`). -/
@[irreducible] private def epochTickStage1GenProg :
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
        stage1QueueBucketProg ((cp, base), cs.2.1)
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

private theorem realizes_epochTickStage1Gen :
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
    have hh := hrep.hdrs
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
    have hbo := hcore.bufOld_valid
    rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
    obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
    dsimp only [ValidEpochStagePreTick] at hpre
    rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)), ite_eq_left hs1] at hpre
    obtain ⟨hsc_le, hdc_le_sc, hd_bnds, _⟩ := hpre
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    have hdc_lt_q : fs.dirtyCount < qEpochWhp n_max := by omega
    have hpos_init : 0 < fs.dirtyCount →
        fs.dirtyBuckets 0 < numBucketsWhp n_max ∧
        fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max := fun hpos =>
      ⟨(hd_bnds 0 hpos).1, rebSliceIdx_lt_of_core hcore (hd_bnds 0 hpos).1⟩
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hcore.curEp_or
      hh.curEp (s := s)
    obtain ⟨hra_st, hra_res, _, _⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
    obtain ⟨hsc_st, hsc_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrStageCursor)
      (by dsimp [hdrStageCursor]; omega) (s := s)
    rw [hh.stageCursor] at hsc_res
    obtain ⟨hcs_st, hcs_res, _, _⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    simp only [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res, hcs_st] at *
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
    | (obtain ⟨_, _, hwsc_step⟩ := writeHdrProg_fastStep (fs := fs) henv
         (by dsimp [hdrStageCursor]; decide) (henv.fits_of_le_n_max (by omega))
         (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hseed hrep
         (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s)
       exact ⟨c, U, V, w, n_max, { fs with stageCursor := fs.stageCursor + 1 },
         henv, rfl, hwsc_step.2.2.1, hpos_init⟩)
    | (cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
       | none =>
         rw [hchk] at hcs_res
         simp only [hcs_res] at *
         have hhit : (0 : ℕ) = 1 := by assumption
         cases hhit
       | some p =>
         rcases p with ⟨b₀, loc₀⟩
         rw [hchk] at hcs_res
         obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
         have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
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
            obtain ⟨_, _, hw_step⟩ := writeHdrProg_fastStep (fs := fs_q) henv
              (by dsimp [hdrStageCursor]; decide) (henv.fits_of_le_n_max (by omega))
              (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hqb_step.2.1 hqb_step.2.2.1
              (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s_q)
            have hpos_q : 0 < fs_q.dirtyCount →
                fs_q.dirtyBuckets 0 < numBucketsWhp n_max ∧
                fs_q.rebSliceIdx (fs_q.dirtyBuckets 0) < 3 * numBucketsWhp n_max := by
              dsimp only [fs_q]
              by_cases hrq0 : fs.rebQueued b₀ = 0
              · rw [ite_eq_left hrq0]; intro _
                have hb_z : Function.update fs.dirtyBuckets fs.dirtyCount b₀ 0 <
                    numBucketsWhp n_max := by
                  by_cases hdc0 : fs.dirtyCount = 0
                  · rw [hdc0, Function.update_self]; exact hb₀
                  · rw [Function.update_of_ne (Ne.symm hdc0)]
                    exact (hd_bnds 0 (Nat.pos_of_ne_zero hdc0)).1
                exact ⟨hb_z, rebSliceIdx_lt_of_core hcore hb_z⟩
              · rw [ite_eq_right hrq0]; exact hpos_init
            exact ⟨c, U, V, w, n_max, { fs_q with stageCursor := fs.stageCursor + 1 },
              henv, rfl, hw_step.2.2.1, hpos_q⟩))
  )

private theorem epochTickStage1GenProg_fastStep {c U V w n_max base : ℕ}
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
  have hh := hrep.hdrs
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
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
  have hdc_lt_q : fs.dirtyCount < qEpochWhp n_max := by omega
  have hpos_init : 0 < fs.dirtyCount →
      fs.dirtyBuckets 0 < numBucketsWhp n_max ∧
      fs.rebSliceIdx (fs.dirtyBuckets 0) < 3 * numBucketsWhp n_max := fun hpos =>
    ⟨(hd_bnds 0 hpos).1, rebSliceIdx_lt_of_core hc (hd_bnds 0 hpos).1⟩
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hc.curEp_or
    hh.curEp (s := s)
  obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
  obtain ⟨hsc_st, hsc_res, hsc_mc, hsc_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrStageCursor)
    (by dsimp [hdrStageCursor]; omega) (s := s)
  rw [hh.stageCursor] at hsc_res
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
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      have hb₀ : b₀ < numBucketsWhp n_max := ((hrel_o.2 k b₀ loc₀).mp hmk).1
      obtain ⟨hqb_mc, hqb_vp, hqb_step⟩ :=
        stage1QueueBucketProg_fastStep henv hb₀ hdc_lt_q hseed hrep (s := s)
      set s_q := (Memory.spec 0).clientState s (stage1QueueBucketProg ((cp, base), b₀))
      set fs_q : FastState :=
        if fs.rebQueued b₀ = 0 then
          { fs with
            rebQueued := Function.update fs.rebQueued b₀ 1
            dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
            dirtyCount := fs.dirtyCount + 1 }
        else fs
      obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs_q) henv
        (by dsimp [hdrStageCursor]; decide) hcur1_fit
        (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hqb_step.2.1 hqb_step.2.2.1
        (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s_q)
      set s_w := (Memory.spec 0).clientState s_q
        (writeHdrProg ((base, hdrStageCursor), fs.stageCursor + 1))
      set fs_w : FastState := { fs_q with stageCursor := fs.stageCursor + 1 }
      have hfs_w_eq : fs_w =
          (if fs.rebQueued b₀ = 0 then
            { fs with
              rebQueued := Function.update fs.rebQueued b₀ 1
              dirtyBuckets := Function.update fs.dirtyBuckets fs.dirtyCount b₀
              dirtyCount := fs.dirtyCount + 1
              stageCursor := fs.stageCursor + 1 }
           else { fs with stageCursor := fs.stageCursor + 1 }) := by
        dsimp only [fs_w, fs_q]; split_ifs <;> rfl
      have hpos_w : 0 < fs_w.dirtyCount →
          fs_w.dirtyBuckets 0 < numBucketsWhp n_max ∧
          fs_w.rebSliceIdx (fs_w.dirtyBuckets 0) < 3 * numBucketsWhp n_max := by
        dsimp only [fs_w, fs_q]
        by_cases hrq0 : fs.rebQueued b₀ = 0
        · rw [ite_eq_left hrq0]; intro _
          have hb_z : Function.update fs.dirtyBuckets fs.dirtyCount b₀ 0 <
              numBucketsWhp n_max := by
            by_cases hdc0 : fs.dirtyCount = 0
            · rw [hdc0, Function.update_self]; exact hb₀
            · rw [Function.update_of_ne (Ne.symm hdc0)]
              exact (hd_bnds 0 (Nat.pos_of_ne_zero hdc0)).1
          exact ⟨hb_z, rebSliceIdx_lt_of_core hc hb_z⟩
        · rw [ite_eq_right hrq0]; exact hpos_init
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone, ← hfs_w_eq]
        obtain ⟨hfn_mc, hfn_vp, hfn_step⟩ :=
          stage1FinishGenProg_fastStep (fs := fs_w) henv hpos_w hw_step.2.1 hw_step.2.2.1 (s := s_w)
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage1QueueBucketProg ((cp, base), cs.2.1) >>= fun _ =>
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
                else
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
              else stage1FinishGenProg (cp, base)) =
            (Memory.spec 0).clientState s_w (stage1FinishGenProg (cp, base)) := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]; rw [clientState_bind, clientState_bind, ite_eq_left hdone]
        rw [hs'_eq]
        refine ⟨?_, ?_, (hqb_step.trans hw_step).trans hfn_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]; simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only; simp only [↓reduceIte, memoryCost_bind]
          rw [ite_eq_left hdone]
          dsimp only [s_q, s_w, cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hqb_mc hw_mc hfn_mc ⊢
          omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]
          refine validProg_bind hqb_vp ?_; refine validProg_bind hw_vp ?_
          rw [ite_eq_left hdone]; exact hfn_vp
      · rw [ite_eq_right hdone, ← hfs_w_eq]
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage1QueueBucketProg ((cp, base), cs.2.1) >>= fun _ =>
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
                else
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
              else stage1FinishGenProg (cp, base)) = s_w := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]
          rw [clientState_bind, clientState_bind, ite_eq_right hdone]
          rfl
        rw [hs'_eq]
        refine ⟨?_, ?_, hqb_step.trans hw_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]; simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only; simp only [↓reduceIte, memoryCost_bind]
          rw [ite_eq_right hdone, memoryCost_pure]
          dsimp only [s_q, cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hqb_mc hw_mc ⊢; omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [↓reduceIte]
          refine validProg_bind hqb_vp ?_; refine validProg_bind hw_vp ?_
          rw [ite_eq_right hdone]; exact validProg_pure _
    | none =>
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs) henv
        (by dsimp [hdrStageCursor]; decide) hcur1_fit
        (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hseed hrep
        (hdrOff := hdrStageCursor) (val := fs.stageCursor + 1) (s := s)
      set s_w := (Memory.spec 0).clientState s
        (writeHdrProg ((base, hdrStageCursor), fs.stageCursor + 1))
      set fs_w : FastState := { fs with stageCursor := fs.stageCursor + 1 }
      by_cases hdone : oldTr.itemAlloc ≤ fs.stageCursor + 1
      · rw [ite_eq_left hdone]
        obtain ⟨hfn_mc, hfn_vp, hfn_step⟩ :=
          stage1FinishGenProg_fastStep (fs := fs_w) henv hpos_init hw_step.2.1 hw_step.2.2.1
            (s := s_w)
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage1QueueBucketProg ((cp, base), cs.2.1) >>= fun _ =>
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
                else
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
              else stage1FinishGenProg (cp, base)) =
            (Memory.spec 0).clientState s_w (stage1FinishGenProg (cp, base)) := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [clientState_bind, ite_eq_left hdone]
        rw [hs'_eq]
        refine ⟨?_, ?_, hw_step.trans hfn_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]; simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only; simp only [zero_ne_one, ↓reduceIte, memoryCost_bind]
          rw [ite_eq_left hdone]
          dsimp only [s_w, cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hw_mc hfn_mc ⊢; omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]
          refine validProg_bind hw_vp ?_; rw [ite_eq_left hdone]; exact hfn_vp
      · rw [ite_eq_right hdone]
        have hs'_eq : (Memory.spec 0).clientState s
            (readOldEpProg base >>= fun oldEp =>
              readBufAllocsProg (base, oldEp) >>= fun allocs =>
              readHdrProg (base, hdrStageCursor) >>= fun sc =>
              if sc < allocs.2 then
                bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
                if cs.1 = 1 then
                  stage1QueueBucketProg ((cp, base), cs.2.1) >>= fun _ =>
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
                else
                  writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
                  if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
              else stage1FinishGenProg (cp, base)) = s_w := by
          rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
            clientState_bind, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]; rw [clientState_bind, ite_eq_right hdone]; rfl
        rw [hs'_eq]
        refine ⟨?_, ?_, hw_step⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]; simp only [memoryCost_bind]
          rw [hcs_st, hcs_res]; dsimp only; simp only [zero_ne_one, ↓reduceIte, memoryCost_bind]
          rw [ite_eq_right hdone, memoryCost_pure]
          dsimp only [cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hw_mc ⊢; omega
        · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
          refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
          refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
          rw [ite_eq_left hlt]
          refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
          simp only [zero_ne_one, ↓reduceIte]
          refine validProg_bind hw_vp ?_; rw [ite_eq_right hdone]; exact validProg_pure _
  · rw [ite_eq_right hlt]
    obtain ⟨hfn_mc, hfn_vp, hfn_step⟩ :=
      stage1FinishGenProg_fastStep (fs := fs) henv hpos_init hseed hrep (s := s)
    have hs'_eq : (Memory.spec 0).clientState s
        (readOldEpProg base >>= fun oldEp =>
          readBufAllocsProg (base, oldEp) >>= fun allocs =>
          readHdrProg (base, hdrStageCursor) >>= fun sc =>
          if sc < allocs.2 then
            bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
            if cs.1 = 1 then
              stage1QueueBucketProg ((cp, base), cs.2.1) >>= fun _ =>
              writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
              if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
            else
              writeHdrProg ((base, hdrStageCursor), sc + 1) >>= fun _ =>
              if allocs.2 ≤ sc + 1 then stage1FinishGenProg (cp, base) else pure ()
          else stage1FinishGenProg (cp, base)) =
        (Memory.spec 0).clientState s (stage1FinishGenProg (cp, base)) := by
      rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
        clientState_bind, hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]
    rw [hs'_eq]
    refine ⟨?_, ?_, hfn_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]
      dsimp only [cp, oldTr] at hro_mc hra_mc hsc_mc hfn_mc ⊢; omega
    · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
      refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
      refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]; exact hfn_vp


/-! ### Stage 2 (`epochTickStage2GenProg`) -/

private structure RebScanPreserved (fs fs' : FastState) (k : ℕ) : Prop where
  curEp : fs'.curEp = fs.curEp
  epochClock : fs'.epochClock = fs.epochClock
  rebStage : fs'.rebStage = fs.rebStage
  stageCursor : fs'.stageCursor = fs.stageCursor
  dirtyCount : fs'.dirtyCount = fs.dirtyCount
  dirtyIdx : fs'.dirtyIdx = fs.dirtyIdx
  dirtyBuckets : fs'.dirtyBuckets = fs.dirtyBuckets
  rebCandSalt : fs'.rebCandSalt = fs.rebCandSalt
  bktCount : fs'.bktCount = fs.bktCount
  liveRole : fs'.liveRole = fs.liveRole
  overmarsRole : fs'.overmarsRole = fs.overmarsRole
  rebInsCount_le : fs'.rebInsCount ≤ fs.rebInsCount + k

private theorem rebScanSteps_preserved {c U n_max : ℕ} (θ : SeedWhp c U n_max) (b : ℕ) :
    ∀ k (fs : FastState),
      RebScanPreserved fs (rebScanSteps c U n_max θ b k fs) k
  | 0, _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl⟩
  | k + 1, fs => by
    dsimp only [rebScanSteps]
    by_cases hcnz : fs.rebCollision ≠ 0
    · rw [ite_eq_left hcnz]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_add_right _ _⟩
    · rw [ite_eq_right hcnz]
      have h1 : ∀ fs1 : FastState,
          RebScanPreserved fs fs1 1 →
            RebScanPreserved fs (rebScanSteps c U n_max θ b k fs1) (k + 1) := by
        intro fs1 hp1
        have hpk := rebScanSteps_preserved θ b k fs1
        exact ⟨hpk.curEp.trans hp1.curEp,
          hpk.epochClock.trans hp1.epochClock,
          hpk.rebStage.trans hp1.rebStage,
          hpk.stageCursor.trans hp1.stageCursor,
          hpk.dirtyCount.trans hp1.dirtyCount,
          hpk.dirtyIdx.trans hp1.dirtyIdx,
          hpk.dirtyBuckets.trans hp1.dirtyBuckets,
          hpk.rebCandSalt.trans hp1.rebCandSalt,
          hpk.bktCount.trans hp1.bktCount,
          hpk.liveRole.trans hp1.liveRole,
          hpk.overmarsRole.trans hp1.overmarsRole,
          by have := hpk.rebInsCount_le; have := hp1.rebInsCount_le; omega⟩
      apply h1
      split_ifs with hact
      · cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.rebSliceIdx b)) (fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor)
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl⟩
        · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_succ _⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_succ _⟩

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
    have hh1 := hrb_step.2.2.1.hdrs
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
  have hh1 := hrb_step.2.2.1.hdrs
  rw [hh1.rebCandSalt] at hcd_res; dsimp only [fs1] at hcd_res
  obtain ⟨hzh_mc, hzh_vp, hzh_step⟩ :=
    resetRebScanHdrsProg_fastStep (fs := fs1) henv (henv.fits_of_le_n_max (by omega))
      hrb_step.2.1 hrb_step.2.2.1 (cand := fs.rebCandSalt + 1) (s := s1)
  dsimp only
  unfold stage2CollisionResetProg; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (readRebSliceIdxGenProg ((cp, base), b) >>= fun rIdx' =>
        resetBTreeSliceGenProg ((cp, base), rIdx') >>= fun _ =>
        readHdrProg (base, hdrRebCandSalt) >>= fun cand =>
        resetRebScanHdrsProg (base, cand + 1)) =
      (Memory.spec 0).clientState s1 (resetRebScanHdrsProg (base, fs.rebCandSalt + 1)) := by
    rw [clientState_bind, hrs_st, hrs_res, clientState_bind,
      clientState_bind, hcd_st, hcd_res]
  rw [hs'_eq]
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
    rw [hro_st, hro_res, hro_mc]
    simp only [memoryCost_pure]
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
  have hh := hrep.hdrs
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
    have hh1 := hrs1_step.2.2.1.hdrs
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
  have hh1 := hrs1_step.2.2.1.hdrs
  rw [hh1.dirtyIdx] at hdi_res; dsimp only [fs1] at hdi_res
  obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
    (by dsimp [hdrDirtyIdx]; decide) (henv.fits_of_le_n_max (by omega))
    (fun h6 => by dsimp [hdrDirtyIdx] at h6; omega) hrs1_step.2.1 hrs1_step.2.2.1
    (hdrOff := hdrDirtyIdx) (val := fs.dirtyIdx + 1) (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrDirtyIdx), fs.dirtyIdx + 1))
  set fs2 : FastState := { fs1 with dirtyIdx := fs.dirtyIdx + 1 }
  obtain ⟨hzh_mc, hzh_vp, hzh_step⟩ := resetRebScanHdrsProg_fastStep (fs := fs2) henv
    (Nat.two_pow_pos w) hw_step.2.1 hw_step.2.2.1 (cand := 0) (s := s2)
  dsimp only
  unfold stage2SwapPreAdvanceProg; simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientResult_bind, clientResult_bind, hdi_st, hdi_res,
      clientResult_bind, clientResult_bind]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    dsimp only [s1, s2, cp, omIdx] at hdi_st hdi_res hdi_mc hrs1_mc hw_mc hzh_mc ⊢
    rw [hdi_st, hdi_res, hdi_mc]; omega
  · refine validProg_bind hrs1_vp ?_
    refine validProg_bind hdi_vp ?_; rw [hdi_st, hdi_res]
    refine validProg_bind hw_vp ?_
    exact validProg_bind hzh_vp (validProg_pure _)
  · rw [clientState_bind, clientState_bind, hdi_st, hdi_res,
      clientState_bind, clientState_bind, clientState_pure_whp]
    exact (hrs1_step.trans hw_step).trans hzh_step

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
    rw [hrep.hdrs.dirtyCount] at hdc_res
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
  rw [hrep.hdrs.dirtyCount] at hdc_res
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
@[irreducible] private def stage2PostScanGenProg :
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

private theorem realizes_stage2PostScanGen :
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
    have hh := hrep.hdrs
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

private theorem stage2PostScanGenProg_fastStep {c U V w n_max base b : ℕ}
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
  have hh := hrep.hdrs
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
        rw [hcl_st, hcl_res, hcl_mc, ite_eq_left hc0]
        simp only [memoryCost_bind]
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
        rw [hcl_st, hcl_res, hcl_mc, ite_eq_left hc0]
        simp only [memoryCost_bind]
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

/-- Execute Stage 2 of `epochTick` (`d = (wp, base)`). -/
@[irreducible] private def epochTickStage2GenProg :
    WhpParams × ℕ → Memory.Prog Unit
  | (wp, base) => do
    let c16 ← pure 16
    let di ← readHdrProg (base, hdrDirtyIdx)
    let dc ← readHdrProg (base, hdrDirtyCount)
    if di < dc then
      let b ← readDirtyBucketGenProg ((wp.1, base), di)
      let cand ← readHdrProg (base, hdrRebCandSalt)
      let smax ← pure (wpSMax wp.1)
      if cand < smax then
        rebScanLoopGenProg ((((wp, base), b), ()), c16)
        stage2PostScanGenProg ((wp.1, base), b)
      else
        pure ()
    else
      tickToStage3Prog base

private theorem realizes_epochTickStage2Gen :
    Realizes .exact epochTickStage2GenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (wp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          ValidEpochStagePreTick c U n_max θ fs ∧
          fs.rebStage = 2)
      (fun _ _ => 0) := by
  unfold epochTickStage2GenProg
  have hrh := realizes_readHdr
  have hrd := realizes_readDirtyBucketGen
  have hsl := realizes_rebScanLoopGen
  have hps := realizes_stage2PostScanGen
  have ht3 := realizes_tickToStage3
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hcore, hpre, hs2⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hh := hrep.hdrs
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    dsimp only [ValidEpochStagePreTick] at hpre
    rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
      ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2] at hpre
    obtain ⟨_, _, hd3, _, _, _, hreb_fn⟩ := hpre
    obtain ⟨hdi_st, hdi_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyIdx)
      (by dsimp [hdrDirtyIdx]; omega) (s := s)
    obtain ⟨hdc_st, hdc_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
      (by dsimp [hdrDirtyCount]; omega) (s := s)
    rw [hh.dirtyIdx] at hdi_res
    rw [hh.dirtyCount] at hdc_res
    simp only [hcp_eq] at *
    simp only [hdi_st, hdi_res, hdc_st, hdc_res, wp_large_sMax hth] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrDirtyIdx, hdrDirtyCount]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | (have hdi_lt : fs.dirtyIdx < fs.dirtyCount := by assumption
       have hb : fs.dirtyBuckets fs.dirtyIdx < numBucketsWhp n_max := hd3 _ hdi_lt
       obtain ⟨hrd_st, hrd_res, _, _⟩ := readDirtyBucketGenProg_spec henv hdi_lt hrep (s := s)
       obtain ⟨hcd_st, hcd_res, _, _⟩ := readHdrProg_spec (w := w)
         (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
         (by dsimp [hdrRebCandSalt]; omega) (s := s)
       rw [hh.rebCandSalt] at hcd_res
       simp only [hrd_st, hrd_res, hcd_st, hcd_res] at *
       first
       | exact henv.fits_hdr_addr (by dsimp [hdrRebCandSalt]; omega)
       | exact ⟨c, U, V, w, n_max, henv, rfl⟩
       | (rw [wp_large_qEpoch hth]; exact hdi_lt.trans_le hrep.1)
       | (have hcs_lt : fs.rebCandSalt < sMaxWhp c n_max := by assumption
          set b := fs.dirtyBuckets fs.dirtyIdx
          obtain ⟨hcur_r, _, rm0, hvr0, _⟩ := hreb_fn hcs_lt
          have hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max := hcore.bktCount_le b hb
          have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
            hcnt_le.trans totalLocalCoordsWhp_le_three_mul
          have h2tl := (large_index_bounds hth).2.2.1
          have h4096 : 4096 ≤ (slabScale n_max) ^ 12 :=
            Nat.pow_le_pow_left (two_le_slabScale n_max) 12
          have hcur16 : fs.rebScanCursor + 16 ≤ n_max := by
            rcases hcur_r with ⟨h0, _⟩ | ⟨_, hle, _⟩ <;> omega
          have hins16 : fs.rebInsCount + 16 ≤ 8 * (slabScale n_max) ^ 12 := by
            rcases hcur_r with ⟨_, hi0⟩ | ⟨_, _, hins_le⟩ <;> omega
          have hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max :=
            rebSliceIdx_lt_of_core hcore hb
          obtain ⟨hsafe16, _, _, hscan_step⟩ := rebScanLoop_spec henv hb θ 16 fs s
            hcore.curEp_or hrIdx hcnt_le (fun p => (hcore.qv_global p).1)
            (fun idx hidx => (hcore.backPtr_valid b hb idx hidx).1)
            (fun _ => ⟨hcur16, hins16, rm0, hvr0⟩) hseed hrep
          have hpres := rebScanSteps_preserved θ b 16 fs
          set fsScan := rebScanSteps c U n_max θ b 16 fs
          have hrIdxS : fsScan.rebSliceIdx b < 3 * numBucketsWhp n_max := by
            dsimp only [FastState.rebSliceIdx, FastState.rebRole]
            rw [hpres.liveRole, hpres.overmarsRole]; exact hrIdx
          have h8L_lt := (large_bounds_lt_n_max hth).2.2.2.1
          have hcandS_lt : fsScan.rebCandSalt < sMaxWhp c n_max := hpres.rebCandSalt ▸ hcs_lt
          have hinsS_le : fsScan.rebInsCount ≤ n_max := by
            have := hpres.rebInsCount_le; omega
          have hrv := hcore.roles_valid b hb
          have hdiS : fsScan.dirtyIdx < fsScan.dirtyCount := by
            rw [hpres.dirtyIdx, hpres.dirtyCount]; exact hdi_lt
          have hnxtS : fsScan.dirtyIdx + 1 < fsScan.dirtyCount →
              fsScan.dirtyBuckets (fsScan.dirtyIdx + 1) < numBucketsWhp n_max ∧
              ({ fsScan with liveRole := Function.update fsScan.liveRole b (fsScan.rebRole b) } :
                FastState).rebSliceIdx (fsScan.dirtyBuckets (fsScan.dirtyIdx + 1)) <
                3 * numBucketsWhp n_max := by
            intro hlt_n
            rw [hpres.dirtyIdx, hpres.dirtyCount] at hlt_n
            have hbN : fs.dirtyBuckets (fs.dirtyIdx + 1) < numBucketsWhp n_max := hd3 _ hlt_n
            rw [hpres.dirtyBuckets, hpres.dirtyIdx]
            refine ⟨hbN, ?_⟩
            dsimp only [FastState.rebSliceIdx, FastState.rebRole]
            rw [hpres.liveRole, hpres.overmarsRole]
            by_cases hbb : fs.dirtyBuckets (fs.dirtyIdx + 1) = b
            · rw [hbb, Function.update_self]
              have := hrv.1; have := hrv.2.1; have := hrv.2.2; omega
            · rw [Function.update_of_ne hbb]
              exact rebSliceIdx_lt_of_core hcore hbN
          first
          | exact hsafe16
          | exact ⟨c, U, V, w, n_max, θ, fsScan, henv, rfl, hscan_step.2.1, hscan_step.2.2.1,
              hb, hpres.liveRole ▸ hrv.1, hpres.overmarsRole ▸ hrv.2.1,
              by rw [hpres.liveRole, hpres.overmarsRole]; exact hrv.2.2,
              hrIdxS, hcandS_lt, hinsS_le, hdiS, hnxtS⟩))
  )

private theorem epochTickStage2GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hpre : ValidEpochStagePreTick c U n_max θ fs)
    (hs2 : fs.rebStage = 2)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage2GenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 32 * hashEvalCostWhp c + 43930 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage2 c U n_max θ fs) s s' := by
  have hth := henv.2.2.2.1
  have hh := hrep.hdrs
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hsmax_cp : wpSMax cp = sMaxWhp c n_max := wp_large_sMax hth
  dsimp only [ValidEpochStagePreTick] at hpre
  rw [ite_eq_right (by omega : ¬(fs.rebStage = 0)),
    ite_eq_right (by omega : ¬(fs.rebStage = 1)), ite_eq_left hs2] at hpre
  obtain ⟨_, _, hd3, _, _, _, hreb_fn⟩ := hpre
  obtain ⟨hdi_st, hdi_res, hdi_mc, hdi_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyIdx)
    (by dsimp [hdrDirtyIdx]; omega) (s := s)
  obtain ⟨hdc_st, hdc_res, hdc_mc, hdc_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrDirtyCount)
    (by dsimp [hdrDirtyCount]; omega) (s := s)
  rw [hh.dirtyIdx] at hdi_res
  rw [hh.dirtyCount] at hdc_res
  dsimp only
  unfold epochTickStage2GenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind, hsmax_cp]
  dsimp only [epochTickStage2]
  by_cases hdi_lt : fs.dirtyIdx < fs.dirtyCount
  · rw [ite_eq_left hdi_lt]
    set b := fs.dirtyBuckets fs.dirtyIdx
    have hb : b < numBucketsWhp n_max := hd3 _ hdi_lt
    obtain ⟨hrd_st, hrd_res, hrd_mc, hrd_vp⟩ :=
      readDirtyBucketGenProg_spec henv hdi_lt hrep (s := s)
    obtain ⟨hcd_st, hcd_res, hcd_mc, hcd_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s)
    rw [hh.rebCandSalt] at hcd_res
    by_cases hcs_lt : fs.rebCandSalt < sMaxWhp c n_max
    · rw [ite_eq_left hcs_lt]
      obtain ⟨hcur_r, _, rm0, hvr0, _⟩ := hreb_fn hcs_lt
      have hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max := hcore.bktCount_le b hb
      have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
        hcnt_le.trans totalLocalCoordsWhp_le_three_mul
      have h2tl := (large_index_bounds hth).2.2.1
      have h4096 : 4096 ≤ (slabScale n_max) ^ 12 :=
        Nat.pow_le_pow_left (two_le_slabScale n_max) 12
      have hcur16 : fs.rebScanCursor + 16 ≤ n_max := by
        rcases hcur_r with ⟨h0, _⟩ | ⟨_, hle, _⟩ <;> omega
      have hins16 : fs.rebInsCount + 16 ≤ 8 * (slabScale n_max) ^ 12 := by
        rcases hcur_r with ⟨_, hi0⟩ | ⟨_, _, hins_le⟩ <;> omega
      have hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max :=
        rebSliceIdx_lt_of_core hcore hb
      obtain ⟨_, hscan_mc, hscan_vp, hscan_step⟩ := rebScanLoop_spec henv hb θ 16 fs s
        hcore.curEp_or hrIdx hcnt_le (fun p => (hcore.qv_global p).1)
        (fun idx hidx => (hcore.backPtr_valid b hb idx hidx).1)
        (fun _ => ⟨hcur16, hins16, rm0, hvr0⟩) hseed hrep
      set sScan := (Memory.spec 0).clientState s
        (rebScanLoopGenProg ((((mkWhpParams c U V w n_max, base), b), ()), 16))
      have hpres := rebScanSteps_preserved θ b 16 fs
      set fsScan := rebScanSteps c U n_max θ b 16 fs
      have hrIdxS : fsScan.rebSliceIdx b < 3 * numBucketsWhp n_max := by
        dsimp only [FastState.rebSliceIdx, FastState.rebRole]
        rw [hpres.liveRole, hpres.overmarsRole]; exact hrIdx
      have h8L_lt := (large_bounds_lt_n_max hth).2.2.2.1
      have hcandS_lt : fsScan.rebCandSalt < sMaxWhp c n_max := hpres.rebCandSalt ▸ hcs_lt
      have hinsS_le : fsScan.rebInsCount ≤ n_max := by
        have := hpres.rebInsCount_le; omega
      have hrv := hcore.roles_valid b hb
      have hdiS : fsScan.dirtyIdx < fsScan.dirtyCount := by
        rw [hpres.dirtyIdx, hpres.dirtyCount]; exact hdi_lt
      have hnxtS : fsScan.dirtyIdx + 1 < fsScan.dirtyCount →
          fsScan.dirtyBuckets (fsScan.dirtyIdx + 1) < numBucketsWhp n_max ∧
          ({ fsScan with liveRole := Function.update fsScan.liveRole b (fsScan.rebRole b) } :
            FastState).rebSliceIdx (fsScan.dirtyBuckets (fsScan.dirtyIdx + 1)) <
            3 * numBucketsWhp n_max := by
        intro hlt_n
        rw [hpres.dirtyIdx, hpres.dirtyCount] at hlt_n
        have hbN : fs.dirtyBuckets (fs.dirtyIdx + 1) < numBucketsWhp n_max := hd3 _ hlt_n
        rw [hpres.dirtyBuckets, hpres.dirtyIdx]
        refine ⟨hbN, ?_⟩
        dsimp only [FastState.rebSliceIdx, FastState.rebRole]
        rw [hpres.liveRole, hpres.overmarsRole]
        by_cases hbb : fs.dirtyBuckets (fs.dirtyIdx + 1) = b
        · rw [hbb, Function.update_self]
          have := hrv.1; have := hrv.2.1; have := hrv.2.2; omega
        · rw [Function.update_of_ne hbb]
          exact rebSliceIdx_lt_of_core hcore hbN
      have hrvS : fsScan.liveRole b < 3 ∧ fsScan.overmarsRole b < 3 ∧
          fsScan.liveRole b ≠ fsScan.overmarsRole b :=
        ⟨hpres.liveRole ▸ hrv.1, hpres.overmarsRole ▸ hrv.2.1,
         by rw [hpres.liveRole, hpres.overmarsRole]; exact hrv.2.2⟩
      obtain ⟨hps_mc, hps_vp, hps_step⟩ :=
        stage2PostScanGenProg_fastStep (fsScan := fsScan) henv hb hrvS
          hrIdxS hcandS_lt hinsS_le hdiS hnxtS
          hscan_step.2.1 hscan_step.2.2.1 (s := sScan)
      refine ⟨?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hdi_st, hdi_res, hdi_mc, hdc_st, hdc_res, hdc_mc, ite_eq_left hdi_lt]
        simp only [memoryCost_bind]
        rw [hrd_st, hrd_res, hrd_mc, hcd_st, hcd_res, hcd_mc, ite_eq_left hcs_lt]
        simp only [memoryCost_bind]
        dsimp only [sScan, cp, b] at hscan_mc hps_mc ⊢; omega
      · refine validProg_bind hdi_vp ?_; rw [hdi_st, hdi_res]
        refine validProg_bind hdc_vp ?_; rw [hdc_st, hdc_res, ite_eq_left hdi_lt]
        refine validProg_bind hrd_vp ?_; rw [hrd_st, hrd_res]
        refine validProg_bind hcd_vp ?_; rw [hcd_st, hcd_res, ite_eq_left hcs_lt]
        exact validProg_bind hscan_vp hps_vp
      · rw [clientState_bind, hdi_st, hdi_res, clientState_bind, hdc_st, hdc_res,
          ite_eq_left hdi_lt, clientState_bind, hrd_st, hrd_res,
          clientState_bind, hcd_st, hcd_res, ite_eq_left hcs_lt, clientState_bind]
        exact hscan_step.trans hps_step
    · rw [ite_eq_right hcs_lt]
      refine ⟨?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hdi_st, hdi_res, hdi_mc, hdc_st, hdc_res, hdc_mc, ite_eq_left hdi_lt]
        simp only [memoryCost_bind]
        rw [hrd_st, hrd_res, hrd_mc, hcd_st, hcd_res, hcd_mc, ite_eq_right hcs_lt,
          memoryCost_pure]; omega
      · refine validProg_bind hdi_vp ?_; rw [hdi_st, hdi_res]
        refine validProg_bind hdc_vp ?_; rw [hdc_st, hdc_res, ite_eq_left hdi_lt]
        refine validProg_bind hrd_vp ?_; rw [hrd_st, hrd_res]
        refine validProg_bind hcd_vp ?_; rw [hcd_st, hcd_res, ite_eq_right hcs_lt]
        exact validProg_pure _
      · rw [clientState_bind, hdi_st, hdi_res, clientState_bind, hdc_st, hdc_res,
          ite_eq_left hdi_lt, clientState_bind, hrd_st, hrd_res,
          clientState_bind, hcd_st, hcd_res, ite_eq_right hcs_lt, clientState_pure_whp]
        exact FastStateStep.refl hseed hrep
  · rw [ite_eq_right hdi_lt]
    obtain ⟨ht3_mc, ht3_vp, ht3_step⟩ := tickToStage3Prog_fastStep henv hseed hrep (s := s)
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hdi_st, hdi_res, hdi_mc, hdc_st, hdc_res, hdc_mc, ite_eq_right hdi_lt]; omega
    · refine validProg_bind hdi_vp ?_; rw [hdi_st, hdi_res]
      refine validProg_bind hdc_vp ?_; rw [hdc_st, hdc_res, ite_eq_right hdi_lt]
      exact ht3_vp
    · rw [clientState_bind, hdi_st, hdi_res, clientState_bind, hdc_st, hdc_res,
        ite_eq_right hdi_lt]
      exact ht3_step

/-! ### Stage 3 (`epochTickStage3GenProg`) -/

private theorem bufDelete_allocs (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) :
    (bufDelete cTab bChar tr rKey).nodeAlloc = tr.nodeAlloc ∧
    (bufDelete cTab bChar tr rKey).itemAlloc = tr.itemAlloc := by
  dsimp only [bufDelete]
  cases bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => exact ⟨rfl, rfl⟩
  | some _ => dsimp only; split_ifs <;> exact ⟨rfl, rfl⟩

/-- Stage 3 `some (b, loc)` helper: delete `rKeyAt b loc` from `buf oldEp` and set
`locState b loc := 1` (`d = (((wp, base), oldEp), (b, loc))`). -/
@[irreducible] private def stage3ClearActiveProg :
    ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((wp, base), oldEp), (b, loc)) => do
    let z1 ← pure 1
    let rKey ← rKeyAtGenProg (((wp, base), b), loc)
    bufDeleteGenProg (((wp.1, base), oldEp), rKey)
    writeFastLocGenProg ((((wp.1, base), b), loc), z1)

private theorem realizes_stage3ClearActive :
    Realizes .exact stage3ClearActiveProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), oldEp), (b, loc)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
            (oldMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (oldEp = 0 ∨ oldEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) oldMap ∧
          (∀ p, fs.quotArr p < 2 ^ quotBitsWhp U n_max) ∧
          b < numBucketsWhp n_max ∧
          loc < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max))
      (fun _ _ => 0) := by
  unfold stage3ClearActiveProg
  have hrk := realizes_rKeyAtGen
  have hbd := realizes_bufDeleteGen
  have hwl := realizes_writeFastLocGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, oldEp⟩, ⟨b, loc⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, oldMap, henv, heq_wp, hseed, hrep, hold_or, hv_o,
      hq_all, hb, hloc, hbp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrk_st, hrk_res, _, _⟩ :=
      rKeyAtGenProg_spec henv hseed hrep hb hloc hbp (s := s)
    simp only [hcp_eq] at *
    simp only [hrk_st, hrk_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | (rw [wp_large_totalLoc hth]; exact hloc)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, fun p _ => hq_all p, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, fs.buf oldEp, oldMap, henv, rfl, hold_or,
        hrep.buf_rep hold_or, hv_o⟩
  )

private theorem stage3ClearActiveProg_fastStep {c U V w n_max base oldEp b loc : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {oldMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hold_or : oldEp = 0 ∨ oldEp = 1)
    (hv_o : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) oldMap)
    (hb : b < numBucketsWhp n_max)
    (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), oldEp), (b, loc))
    let s' := (Memory.spec 0).clientState s prog
    let rKey := fs.rKeyAt c U n_max θ b loc
    let tr' := bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) rKey
    memoryCost prog s ≤ 2 * cTabWhp c + hashEvalCostWhp c + 17 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        buf := Function.update fs.buf oldEp tr'
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) loc 1) } s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    rKeyAtGenProg_spec henv hseed hrep hb hloc hbp (s := s)
  set rKey := fs.rKeyAt c U n_max θ b loc
  obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
    bufDeleteGenProg_fastStep henv hold_or hseed hrep hv_o (rKey := rKey) (s := s)
  set s1 := (Memory.spec 0).clientState s (bufDeleteGenProg (((cp, base), oldEp), rKey))
  set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf oldEp) rKey
  set fs1 : FastState := { fs with buf := Function.update fs.buf oldEp tr' }
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ :=
    writeFastLocGenProg_fastStep (fs := fs1) henv hb hloc (by decide : 1 < 4)
      hbd_step.2.1 hbd_step.2.2.1 (s := s1)
  dsimp only
  unfold stage3ClearActiveProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (rKeyAtGenProg (((mkWhpParams c U V w n_max, base), b), loc) >>= fun rk =>
        bufDeleteGenProg (((cp, base), oldEp), rk) >>= fun _ =>
        writeFastLocGenProg ((((cp, base), b), loc), 1)) =
      (Memory.spec 0).clientState s1 (writeFastLocGenProg ((((cp, base), b), loc), 1)) := by
    rw [clientState_bind, hrk_st, hrk_res, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hbd_step.trans hwl_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrk_st, hrk_res]
    dsimp only [s1, cp, rKey] at hrk_mc hbd_mc hwl_mc ⊢; omega
  · refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
    exact validProg_bind hbd_vp hwl_vp

/-- Advance Stage 3 cursor and transition to Stage 4 if `ia ≤ nextCur`
(`d = ((base, ia), nextCur)`). -/
@[irreducible] private def stage3AdvanceProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, ia), nextCur) => do
    let z4 ← pure 4
    writeHdrProg ((base, hdrStageCursor), nextCur)
    if ia ≤ nextCur then
      writeHdrProg ((base, hdrRebStage), z4)
    else
      pure ()

private theorem realizes_stage3Advance :
    Realizes .exact stage3AdvanceProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((base, _), _) _ => 3 ≤ w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold stage3AdvanceProg
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨base, ia⟩, nextCur⟩
    obtain ⟨h3w, hfit32⟩ := h
    have h8 : 8 ≤ 2 ^ w := (by decide : 8 ≤ 2 ^ 3).trans (Nat.pow_le_pow_right two_pos h3w)
    first
    | (change 4 < 2 ^ w; omega)
    | exact hfit32.of_le (by dsimp [hdrStageCursor, hdrRebStage]; omega)
  )

private theorem stage3AdvanceProg_fastStep {c U V w n_max base ia nextCur : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcur_fit : Fits w nextCur)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := stage3AdvanceProg ((base, ia), nextCur)
    let s' := (Memory.spec 0).clientState s prog
    let fs1 : FastState := { fs with stageCursor := nextCur }
    let fsOut : FastState := if ia ≤ nextCur then { fs1 with rebStage := 4 } else fs1
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s s' := by
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ := writeHdrProg_fastStep (fs := fs) henv
    (by dsimp [hdrStageCursor]; decide) hcur_fit
    (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hseed hrep
    (hdrOff := hdrStageCursor) (val := nextCur) (s := s)
  set s1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrStageCursor), nextCur))
  set fs1 : FastState := { fs with stageCursor := nextCur }
  dsimp only
  unfold stage3AdvanceProg; simp only [pure_bind]
  by_cases hdone : ia ≤ nextCur
  · rw [ite_eq_left hdone]
    obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
      (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
      (fun h6 => by dsimp [hdrRebStage] at h6; omega) hw1_step.2.1 hw1_step.2.2.1
      (hdrOff := hdrRebStage) (val := 4) (s := s1)
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1] at hw1_mc hw2_mc ⊢; omega
    · exact validProg_bind hw1_vp hw2_vp
    · rw [ite_eq_left hdone, clientState_bind]
      exact hw1_step.trans hw2_step
  · rw [ite_eq_right hdone]
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
      omega
    · exact validProg_bind hw1_vp (validProg_pure _)
    · rw [ite_eq_right hdone, clientState_bind, clientState_pure_whp]
      exact hw1_step

/-- Execute Stage 3 of `epochTick` (`d = (wp, base)`). -/
@[irreducible] private def epochTickStage3GenProg :
    WhpParams × ℕ → Memory.Prog Unit
  | (wp, base) => do
    let z1 ← pure 1
    let z4 ← pure 4
    let oldEp ← readOldEpProg base
    let allocs ← readBufAllocsProg (base, oldEp)
    let ia ← pure allocs.2
    let sc ← readHdrProg (base, hdrStageCursor)
    if sc < ia then
      let cs ← bufCheckSlotGenProg (((wp.1, base), oldEp), sc)
      let nextCur ← pure (sc + 1)
      if cs.1 = z1 then
        stage3ClearActiveProg (((wp, base), oldEp), cs.2)
        stage3AdvanceProg ((base, ia), nextCur)
      else
        stage3AdvanceProg ((base, ia), nextCur)
    else
      writeHdrProg ((base, hdrRebStage), z4)

private theorem realizes_epochTickStage3Gen :
    Realizes .exact epochTickStage3GenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (wp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          fs.rebStage = 3)
      (fun _ _ => 0) := by
  unfold epochTickStage3GenProg
  have hro := realizes_readOldEp
  have hra := realizes_readBufAllocs
  have hrh := realizes_readHdr
  have hcs := realizes_bufCheckSlotGen
  have hca := realizes_stage3ClearActive
  have had := realizes_stage3Advance
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hcore, hs3⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hh := hrep.hdrs
    have h2w := henv.two_le_w
    have h3w := henv.three_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
    have hbo := hcore.bufOld_valid
    rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
    obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
    have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hcore.curEp_or
      hh.curEp (s := s)
    obtain ⟨hra_st, hra_res, _, _⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
    obtain ⟨hsc_st, hsc_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrStageCursor)
      (by dsimp [hdrStageCursor]; omega) (s := s)
    rw [hh.stageCursor] at hsc_res
    obtain ⟨hcs_st, hcs_res, _, _⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    simp only [hcp_eq] at *
    simp only [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res, hcs_st] at *
    first
    | exact h3w
    | exact h2w
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrCurEp, hdrStageCursor, hdrRebStage]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, oldMap, henv, rfl, hold_or,
        hrep.buf_rep hold_or, hv_o⟩
    | (cases hchk : bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
       | none =>
         rw [hchk] at hcs_res
         have hhit : ((Memory.spec 0).clientResult s
           (bufCheckSlotGenProg (((mkWhpCoreParams c U V w n_max, base), fs.oldEp),
             fs.stageCursor))).1 = 1 := by assumption
         rw [hcs_res] at hhit; cases hhit
       | some p =>
         rcases p with ⟨b₀, loc₀⟩
         rw [hchk] at hcs_res
         obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
         obtain ⟨hb₀, hloc_b, _, _⟩ := (hrel_o.2 k b₀ loc₀).mp hmk
         have hloc₀ : loc₀ < totalLocalCoordsWhp n_max :=
           hloc_b.trans_le (hcore.bktCount_le b₀ hb₀)
         have hbp₀ : capFrontWhp n_max ≤ loc₀ →
             fs.backPtr b₀ (loc₀ - capFrontWhp n_max) < poolSizeWhp n_max :=
           fun hcf => (hcore.backPtr_valid b₀ hb₀ _ (by omega)).1
         rw [hcs_res]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, oldMap, henv, rfl, hseed, hrep, hold_or, hv_o,
           fun idx => (hcore.qv_global idx).1, hb₀, hloc₀, hbp₀⟩)
  )

private theorem epochTickStage3GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hs3 : fs.rebStage = 3)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage3GenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2 * cTabWhp c + hashEvalCostWhp c + 40 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage3 c U n_max θ fs) s s' := by
  have hth := henv.2.2.2.1
  have hh := hrep.hdrs
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
  have hbo := hcore.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, _, oldMap, hv_o, hrel_o⟩ := hbo
  have hrc_lt := two_mul_rIndepWhp_lt_qEpochWhp hth
  have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hcore.curEp_or
    hh.curEp (s := s)
  obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
  obtain ⟨hsc_st, hsc_res, hsc_mc, hsc_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrStageCursor)
    (by dsimp [hdrStageCursor]; omega) (s := s)
  rw [hh.stageCursor] at hsc_res
  dsimp only
  unfold epochTickStage3GenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  dsimp only [epochTickStage3]
  set oldTr := fs.buf fs.oldEp
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ :=
      bufCheckSlotGenProg_spec henv hold_or (hrep.buf_rep hold_or) hv_o
        (id := fs.stageCursor) (s := s)
    have hcur1_fit : Fits w (fs.stageCursor + 1) := henv.fits_of_le_n_max (by omega)
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some p =>
      rcases p with ⟨b₀, loc₀⟩
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨_, k, _, _, hmk⟩ := hv_o.checkSlot_some hchk
      obtain ⟨hb₀, hloc_b, _, _⟩ := (hrel_o.2 k b₀ loc₀).mp hmk
      have hloc₀ : loc₀ < totalLocalCoordsWhp n_max := hloc_b.trans_le (hcore.bktCount_le b₀ hb₀)
      have hbp₀ : capFrontWhp n_max ≤ loc₀ →
          fs.backPtr b₀ (loc₀ - capFrontWhp n_max) < poolSizeWhp n_max :=
        fun hcf => (hcore.backPtr_valid b₀ hb₀ _ (by omega)).1
      obtain ⟨hca_mc, hca_vp, hca_step⟩ :=
        stage3ClearActiveProg_fastStep henv hold_or hv_o hb₀ hloc₀ hbp₀ hseed hrep (s := s)
      set s_ca := (Memory.spec 0).clientState s
        (stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), fs.oldEp), (b₀, loc₀)))
      set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) oldTr (fs.rKeyAt c U n_max θ b₀ loc₀)
      set fs_ca : FastState :=
        { fs with
          buf := Function.update fs.buf fs.oldEp tr'
          locState := Function.update fs.locState b₀ (Function.update (fs.locState b₀) loc₀ 1) }
      have hia_eq : (Function.update fs.buf fs.oldEp tr' fs.oldEp).itemAlloc = oldTr.itemAlloc := by
        rw [Function.update_self]; exact (bufDelete_allocs _ _ _ _).2
      rw [hia_eq]
      obtain ⟨had_mc, had_vp, had_step⟩ :=
        stage3AdvanceProg_fastStep (fs := fs_ca) henv hcur1_fit hca_step.2.1 hca_step.2.2.1
          (ia := oldTr.itemAlloc) (nextCur := fs.stageCursor + 1) (s := s_ca)
      have hs'_eq : (Memory.spec 0).clientState s
          (readOldEpProg base >>= fun oldEp =>
            readBufAllocsProg (base, oldEp) >>= fun allocs =>
            readHdrProg (base, hdrStageCursor) >>= fun sc =>
            if sc < allocs.2 then
              bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
              if cs.1 = 1 then
                stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), oldEp), cs.2) >>=
                  fun _ =>
                stage3AdvanceProg ((base, allocs.2), sc + 1)
              else stage3AdvanceProg ((base, allocs.2), sc + 1)
            else writeHdrProg ((base, hdrRebStage), 4)) =
          (Memory.spec 0).clientState s_ca
            (stage3AdvanceProg ((base, oldTr.itemAlloc), fs.stageCursor + 1)) := by
        rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
          clientState_bind, hsc_st, hsc_res]; dsimp only
        rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
        simp only [↓reduceIte]; rw [clientState_bind]
      rw [hs'_eq]
      refine ⟨?_, ?_, hca_step.trans had_step⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
        rw [ite_eq_left hlt]; simp only [memoryCost_bind]
        rw [hcs_st, hcs_res]; dsimp only; simp only [↓reduceIte, memoryCost_bind]
        dsimp only [s_ca, cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc hca_mc had_mc ⊢; omega
      · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
        refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
        refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
        rw [ite_eq_left hlt]
        refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
        simp only [↓reduceIte]
        exact validProg_bind hca_vp had_vp
    | none =>
      rw [hchk] at hcs_res; dsimp only at hcs_res ⊢
      obtain ⟨had_mc, had_vp, had_step⟩ :=
        stage3AdvanceProg_fastStep (fs := fs) henv hcur1_fit hseed hrep
          (ia := oldTr.itemAlloc) (nextCur := fs.stageCursor + 1) (s := s)
      have hs'_eq : (Memory.spec 0).clientState s
          (readOldEpProg base >>= fun oldEp =>
            readBufAllocsProg (base, oldEp) >>= fun allocs =>
            readHdrProg (base, hdrStageCursor) >>= fun sc =>
            if sc < allocs.2 then
              bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
              if cs.1 = 1 then
                stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), oldEp), cs.2) >>=
                  fun _ =>
                stage3AdvanceProg ((base, allocs.2), sc + 1)
              else stage3AdvanceProg ((base, allocs.2), sc + 1)
            else writeHdrProg ((base, hdrRebStage), 4)) =
          (Memory.spec 0).clientState s
            (stage3AdvanceProg ((base, oldTr.itemAlloc), fs.stageCursor + 1)) := by
        rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
          clientState_bind, hsc_st, hsc_res]; dsimp only
        rw [ite_eq_left hlt, clientState_bind, hcs_st, hcs_res]; dsimp only
        simp only [zero_ne_one, ↓reduceIte]
      rw [hs'_eq]
      refine ⟨?_, ?_, had_step⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
        rw [ite_eq_left hlt]; simp only [memoryCost_bind]
        rw [hcs_st, hcs_res]; dsimp only; simp only [zero_ne_one, ↓reduceIte]
        dsimp only [cp, oldTr] at hro_mc hra_mc hsc_mc hcs_mc had_mc ⊢; omega
      · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
        refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
        refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
        rw [ite_eq_left hlt]
        refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; dsimp only
        simp only [zero_ne_one, ↓reduceIte]; exact had_vp
  · rw [ite_eq_right hlt]
    obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs) henv
      (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
      (fun h6 => by dsimp [hdrRebStage] at h6; omega) hseed hrep
      (hdrOff := hdrRebStage) (val := 4) (s := s)
    have hs'_eq : (Memory.spec 0).clientState s
        (readOldEpProg base >>= fun oldEp =>
          readBufAllocsProg (base, oldEp) >>= fun allocs =>
          readHdrProg (base, hdrStageCursor) >>= fun sc =>
          if sc < allocs.2 then
            bufCheckSlotGenProg (((cp, base), oldEp), sc) >>= fun cs =>
            if cs.1 = 1 then
              stage3ClearActiveProg (((mkWhpParams c U V w n_max, base), oldEp), cs.2) >>=
                fun _ =>
              stage3AdvanceProg ((base, allocs.2), sc + 1)
            else stage3AdvanceProg ((base, allocs.2), sc + 1)
          else writeHdrProg ((base, hdrRebStage), 4)) =
        (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebStage), 4)) := by
      rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
        clientState_bind, hsc_st, hsc_res]; dsimp only; rw [ite_eq_right hlt]
    rw [hs'_eq]
    refine ⟨?_, ?_, hw_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hro_st, hro_res, hra_st, hra_res, hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]; omega
    · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
      refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
      refine validProg_bind hsc_vp ?_; rw [hsc_st, hsc_res]; dsimp only
      rw [ite_eq_right hlt]; exact hw_vp

/-! ### Stage 4 (`epochTickStage4GenProg`) -/

/-- Execute Stage 4 of `epochTick` (`d = (cp, base)`). -/
@[irreducible] private def epochTickStage4GenProg :
    WhpCoreParams × ℕ → Memory.Prog Unit
  | (cp, base) => do
    let c8 ← pure 8
    let z4 ← pure 4
    let z5 ← pure 5
    let oldEp ← readOldEpProg base
    let allocs ← readBufAllocsProg (base, oldEp)
    bufClearStepsGenProg (((cp, base), oldEp), c8)
    if allocs.1 ≤ c8 then
      writeHdrProg ((base, hdrRebStage), z5)
    else
      writeHdrProg ((base, hdrRebStage), z4)

private theorem realizes_epochTickStage4Gen :
    Realizes .exact epochTickStage4GenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          CoreFastInv c U V n_max θ fs dict ∧
          fs.rebStage = 4)
      (fun _ _ => 0) := by
  unfold epochTickStage4GenProg
  have hro := realizes_readOldEp
  have hra := realizes_readBufAllocs
  have hcl := realizes_bufClearStepsGen
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, rfl, hrep, hcore, hs4⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hh := hrep.hdrs
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
    have hbo := hcore.bufOld_valid
    rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
    obtain ⟨_, hclr, _⟩ := hbo
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hcore.curEp_or
      hh.curEp (s := s)
    obtain ⟨hra_st, hra_res, _, _⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
    simp only [hro_st, hro_res, hra_st, hra_res] at *
    first
    | exact h2w
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrCurEp, hdrRebStage]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, henv, rfl, hold_or, hrep.buf_rep hold_or, hclr⟩
  )

private theorem epochTickStage4GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hcore : CoreFastInv c U V n_max θ fs dict)
    (hs4 : fs.rebStage = 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage4GenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 130 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage4 fs) s s' := by
  have hh := hrep.hdrs
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hcore.curEp_or with h01 | h01 <;> simp [FastState.oldEp, h01]
  have hbo := hcore.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
  obtain ⟨_, hclr, _⟩ := hbo
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hcore.curEp_or
    hh.curEp (s := s)
  obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ := readBufAllocsProg_spec henv hold_or hrep (s := s)
  obtain ⟨hcl_mc, hcl_vp, hcl_step⟩ :=
    bufClearStepsGenProg_fastStep henv hold_or hclr hseed hrep (k := 8) (s := s)
  set s1 := (Memory.spec 0).clientState s (bufClearStepsGenProg (((cp, base), fs.oldEp), 8))
  set fs1 : FastState :=
    { fs with buf := Function.update fs.buf fs.oldEp (bufClearSteps 8 (fs.buf fs.oldEp)) }
  dsimp only
  unfold epochTickStage4GenProg; simp only [pure_bind]
  dsimp only [epochTickStage4]
  by_cases hle8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
  · rw [ite_eq_left (decide_eq_true hle8)]
    obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
      (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
      (fun h6 => by dsimp [hdrRebStage] at h6; omega) hcl_step.2.1 hcl_step.2.2.1
      (hdrOff := hdrRebStage) (val := 5) (s := s1)
    have hs'_eq : (Memory.spec 0).clientState s
        (readOldEpProg base >>= fun oldEp =>
          readBufAllocsProg (base, oldEp) >>= fun allocs =>
          bufClearStepsGenProg (((cp, base), oldEp), 8) >>= fun _ =>
          if allocs.1 ≤ 8 then writeHdrProg ((base, hdrRebStage), 5)
          else writeHdrProg ((base, hdrRebStage), 4)) =
        (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebStage), 5)) := by
      rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
        clientState_bind]; dsimp only; rw [ite_eq_left hle8]
    rw [hs'_eq]
    refine ⟨?_, ?_, hcl_step.trans hw_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hro_st, hro_res, hra_st, hra_res]; dsimp only
      dsimp only [s1, cp] at hcl_mc hw_mc ⊢
      rw [ite_eq_left hle8]; omega
    · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
      refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
      refine validProg_bind hcl_vp ?_; dsimp only; rw [ite_eq_left hle8]; exact hw_vp
  · rw [ite_eq_right (by simp [hle8])]
    obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
      (by dsimp [hdrRebStage]; decide) (henv.fits_const (by decide))
      (fun h6 => by dsimp [hdrRebStage] at h6; omega) hcl_step.2.1 hcl_step.2.2.1
      (hdrOff := hdrRebStage) (val := 4) (s := s1)
    have hs'_eq : (Memory.spec 0).clientState s
        (readOldEpProg base >>= fun oldEp =>
          readBufAllocsProg (base, oldEp) >>= fun allocs =>
          bufClearStepsGenProg (((cp, base), oldEp), 8) >>= fun _ =>
          if allocs.1 ≤ 8 then writeHdrProg ((base, hdrRebStage), 5)
          else writeHdrProg ((base, hdrRebStage), 4)) =
        (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebStage), 4)) := by
      rw [clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res,
        clientState_bind]; dsimp only; rw [ite_eq_right hle8]
    rw [hs'_eq]
    refine ⟨?_, ?_, hcl_step.trans hw_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hro_st, hro_res, hra_st, hra_res]; dsimp only
      dsimp only [s1, cp] at hcl_mc hw_mc ⊢
      rw [ite_eq_right hle8]; omega
    · refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
      refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]
      refine validProg_bind hcl_vp ?_; dsimp only; rw [ite_eq_right hle8]; exact hw_vp

/-! ### Combined Stage Dispatcher, Rollover, and `epochTickGenProg` -/

/-- Exact read-only rollover pre-condition guaranteeing `(epochTick c U n_max θ fs).isSome`. -/
private def epochTickWillSucceed (n_max : ℕ) (fs : FastState) : Bool :=
  decide (fs.epochClock + 1 < qEpochWhp n_max ∨ fs.rebStage = 5 ∨
    (fs.rebStage = 4 ∧ (fs.buf fs.oldEp).nodeAlloc ≤ 8))

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
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
        | none => dsimp only; split_ifs <;> exact ⟨rfl, rfl, by dsimp only; omega⟩
        | some p =>
          rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> exact ⟨rfl, rfl, by dsimp only; omega⟩
      · rw [ite_eq_right hlt]; exact ⟨rfl, rfl, by dsimp only; omega⟩
    exact ⟨hclk.1, hclk.2.1, by omega⟩
  rw [ite_eq_right hs0]
  by_cases hs1 : fs.rebStage = 1
  · rw [ite_eq_left hs1]
    have hfin : ∀ s0 : FastState, s0.curEp = fs.curEp → s0.epochClock = fs.epochClock →
        s0.rebStage ≤ 3 →
        (epochTickStage1Finish s0).curEp = fs.curEp ∧
        (epochTickStage1Finish s0).epochClock = fs.epochClock ∧
        (epochTickStage1Finish s0).rebStage ≤ 3 := by
      intro s0 h1 h2 h3
      dsimp only [epochTickStage1Finish]
      split_ifs <;> exact ⟨h1, h2, by dsimp only; omega⟩
    have hclk : (epochTickStage1 fs).curEp = fs.curEp ∧
        (epochTickStage1 fs).epochClock = fs.epochClock ∧
        (epochTickStage1 fs).rebStage ≤ 3 := by
      dsimp only [epochTickStage1]
      by_cases hlt : fs.stageCursor < (fs.buf fs.oldEp).itemAlloc
      · rw [ite_eq_left hlt]
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
        | none =>
          dsimp only
          by_cases hd : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
          · rw [ite_eq_left hd]; exact hfin _ rfl rfl (by dsimp only; omega)
          · rw [ite_eq_right hd]; exact ⟨rfl, rfl, by dsimp only; omega⟩
        | some p =>
          rcases p with ⟨b, _⟩; dsimp only
          by_cases hq : fs.rebQueued b = 0
          · rw [ite_eq_left hq]
            by_cases hd : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
            · rw [ite_eq_left hd]; exact hfin _ rfl rfl (by dsimp only; omega)
            · rw [ite_eq_right hd]; exact ⟨rfl, rfl, by dsimp only; omega⟩
          · rw [ite_eq_right hq]
            by_cases hd : (fs.buf fs.oldEp).itemAlloc ≤ fs.stageCursor + 1
            · rw [ite_eq_left hd]; exact hfin _ rfl rfl (by dsimp only; omega)
            · rw [ite_eq_right hd]; exact ⟨rfl, rfl, by dsimp only; omega⟩
      · rw [ite_eq_right hlt]; exact hfin fs rfl rfl (by omega)
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
          set fsScan := rebScanSteps c U n_max θ b 16 fs
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
        cases bufCheckSlot (fs.buf fs.oldEp) fs.stageCursor with
        | none => dsimp only; split_ifs <;> exact ⟨rfl, rfl, by dsimp only; omega⟩
        | some p =>
          rcases p with ⟨_, _⟩; dsimp only; split_ifs <;> exact ⟨rfl, rfl, by dsimp only; omega⟩
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
private theorem epochTick_isSome_iff {c U n_max : ℕ} (θ : SeedWhp c U n_max) {fs : FastState}
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
    have hh := hrep.hdrs
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
  have hh := hrep.hdrs
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
    have hh := hrep.hdrs
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
  have hh := hrep.hdrs
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
    obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
      (by dsimp [hdrCurEp]; decide) hfit_new
      (fun h6 => by dsimp [hdrCurEp] at h6; omega) hseed hrep
      (hdrOff := hdrCurEp) (val := 1 - fs1.curEp) (s := s)
    set s1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrCurEp), 1 - fs1.curEp))
    set f1 : FastState := { fs1 with curEp := 1 - fs1.curEp }
    obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ := writeHdrProg_fastStep (fs := f1) henv
      (by dsimp [hdrEpochClock]; decide) (Nat.two_pow_pos w)
      (fun h6 => by dsimp [hdrEpochClock] at h6; omega) hw1_step.2.1 hw1_step.2.2.1
      (hdrOff := hdrEpochClock) (val := 0) (s := s1)
    set s2 := (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrEpochClock), 0))
    set f2 : FastState := { f1 with epochClock := 0 }
    obtain ⟨hw3_mc, hw3_vp, hw3_step⟩ := writeHdrProg_fastStep (fs := f2) henv
      (by dsimp [hdrRebStage]; decide) (Nat.two_pow_pos w)
      (fun h6 => by dsimp [hdrRebStage] at h6; omega) hw2_step.2.1 hw2_step.2.2.1
      (hdrOff := hdrRebStage) (val := 0) (s := s2)
    set s3 := (Memory.spec 0).clientState s2 (writeHdrProg ((base, hdrRebStage), 0))
    set f3 : FastState := { f2 with rebStage := 0 }
    obtain ⟨hw4_mc, hw4_vp, hw4_step⟩ := writeHdrProg_fastStep (fs := f3) henv
      (by dsimp [hdrStageCursor]; decide) (Nat.two_pow_pos w)
      (fun h6 => by dsimp [hdrStageCursor] at h6; omega) hw3_step.2.1 hw3_step.2.2.1
      (hdrOff := hdrStageCursor) (val := 0) (s := s3)
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hck_st, hck_res, hck_mc, ite_eq_left hroll]
      simp only [memoryCost_bind]
      rw [hce_st, hce_res, hce_mc]
      dsimp only [s1, s2, s3] at hw1_mc hw2_mc hw3_mc hw4_mc ⊢; omega
    · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_left hroll]
      refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
      exact validProg_bind hw1_vp (validProg_bind hw2_vp (validProg_bind hw3_vp hw4_vp))
    · have hs'_eq : (Memory.spec 0).clientState s
          (readHdrProg (base, hdrEpochClock) >>= fun clk =>
            if qEpochWhp n_max ≤ clk + 1 then
              readHdrProg (base, hdrCurEp) >>= fun cur =>
              writeHdrProg ((base, hdrCurEp), 1 - cur) >>= fun _ =>
              writeHdrProg ((base, hdrEpochClock), 0) >>= fun _ =>
              writeHdrProg ((base, hdrRebStage), 0) >>= fun _ =>
              writeHdrProg ((base, hdrStageCursor), 0)
            else writeHdrProg ((base, hdrEpochClock), clk + 1)) =
          (Memory.spec 0).clientState s3 (writeHdrProg ((base, hdrStageCursor), 0)) := by
        rw [clientState_bind, hck_st, hck_res, ite_eq_left hroll,
          clientState_bind, hce_st, hce_res, clientState_bind,
          clientState_bind, clientState_bind]
      rw [hs'_eq]
      exact ((hw1_step.trans hw2_step).trans hw3_step).trans hw4_step
  · rw [ite_eq_right hroll]
    obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrProg_fastStep (fs := fs1) henv
      (by dsimp [hdrEpochClock]; decide) (henv.fits_of_le_n_max (by omega))
      (fun h6 => by dsimp [hdrEpochClock] at h6; omega) hseed hrep
      (hdrOff := hdrEpochClock) (val := fs1.epochClock + 1) (s := s)
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hck_st, hck_res, hck_mc, ite_eq_right hroll]; omega
    · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_right hroll]; exact hw_vp
    · rw [clientState_bind, hck_st, hck_res, ite_eq_right hroll]; exact hw_step

/-- Execute `epochTick` when `epochTickWillSucceed n_max fs` holds (`d = (wp, base)`). -/
@[irreducible] private def epochTickGenProg : WhpParams × ℕ → Memory.Prog Unit
  | (wp, base) => do
    epochTickStageAllGenProg (wp, base)
    epochTickRolloverGenProg (wp.1, base)

private theorem realizes_epochTickGen :
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

private theorem epochTickGenProg_fastStep {c U V w n_max base : ℕ}
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

/-! ## Section 3: `checkEpochTickOkGenProg` and `fastStepPureGenProg` -/

private theorem overmarsScanSteps_tickFields {c U n_max : ℕ} (θ : SeedWhp c U n_max) (b : ℕ) :
    ∀ k (fs : FastState),
      let fs' := overmarsScanSteps c U n_max θ b k fs
      fs'.epochClock = fs.epochClock ∧
      fs'.rebStage = fs.rebStage ∧
      fs'.curEp = fs.curEp ∧
      fs'.buf = fs.buf
  | 0, _ => ⟨rfl, rfl, rfl, rfl⟩
  | k + 1, fs => by
    dsimp only [overmarsScanSteps]
    split_ifs
    · exact overmarsScanSteps_tickFields θ b k _
    · exact overmarsScanSteps_tickFields θ b k _

private theorem epochTickWillSucceed_eq_of_fields {n_max : ℕ} {fs₁ fs₂ : FastState}
    (h1 : fs₁.epochClock = fs₂.epochClock) (h2 : fs₁.rebStage = fs₂.rebStage)
    (_h3 : fs₁.curEp = fs₂.curEp) (h4 : fs₁.buf fs₁.oldEp = fs₂.buf fs₂.oldEp) :
    epochTickWillSucceed n_max fs₁ = epochTickWillSucceed n_max fs₂ := by
  unfold epochTickWillSucceed
  rw [h1, h2, h4]

private theorem overmarsStep_epochTickWillSucceed {c U n_max b : ℕ} (θ : SeedWhp c U n_max)
    (fs : FastState) :
    epochTickWillSucceed n_max (overmarsStep c U n_max θ b fs) = epochTickWillSucceed n_max fs := by
  have h :
      (overmarsStep c U n_max θ b fs).epochClock = fs.epochClock ∧
      (overmarsStep c U n_max θ b fs).rebStage = fs.rebStage ∧
      (overmarsStep c U n_max θ b fs).curEp = fs.curEp ∧
      (overmarsStep c U n_max θ b fs).buf = fs.buf := by
    unfold overmarsStep overmarsAfterActivate
    generalize (16 : ℕ) = k
    dsimp only
    split_ifs <;> first | exact overmarsScanSteps_tickFields θ b k _ | exact ⟨rfl, rfl, rfl, rfl⟩
  exact epochTickWillSucceed_eq_of_fields h.1 h.2.1 h.2.2.1
    (by unfold FastState.oldEp; rw [h.2.2.1, h.2.2.2])

private theorem epochTickWillSucceed_fastInsert {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs1 : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict)
    {u : Fin U} {v : ℕ} (hins : fastInsert c U n_max θ fs u v = some fs1) :
    epochTickWillSucceed n_max fs1 = epochTickWillSucceed n_max fs := by
  unfold fastInsert fastInsertAlloc fastInsertFresh at hins
  dsimp only at hins
  cases hfl : fastFindLoc c U n_max θ fs u with
  | some loc =>
    rw [hfl] at hins; injection hins with hfs1; rw [← hfs1]
    rw [overmarsStep_epochTickWillSucceed]; rfl
  | none =>
    rw [hfl] at hins; dsimp only at hins
    have hne : 1 - fs.curEp ≠ fs.curEp := by
      rcases hv.curEp_or with h01 | h01 <;> simp [h01]
    split_ifs at hins
    · injection hins with hfs1
      rw [← hfs1, overmarsStep_epochTickWillSucceed]
      refine epochTickWillSucceed_eq_of_fields rfl rfl rfl ?_
      dsimp only [FastState.oldEp]; exact Function.update_of_ne hne _ _
    · injection hins with hfs1
      rw [← hfs1, overmarsStep_epochTickWillSucceed]
      refine epochTickWillSucceed_eq_of_fields rfl rfl rfl ?_
      dsimp only [FastState.oldEp]; exact Function.update_of_ne hne _ _
    · injection hins with hfs1
      rw [← hfs1, overmarsStep_epochTickWillSucceed]
      exact epochTickWillSucceed_eq_of_fields rfl rfl rfl rfl
    · injection hins with hfs1
      rw [← hfs1, overmarsStep_epochTickWillSucceed]
      exact epochTickWillSucceed_eq_of_fields rfl rfl rfl rfl

private theorem epochTickWillSucceed_fastDelete {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) (u : Fin U) :
    epochTickWillSucceed n_max (fastDelete c U n_max θ fs u) = epochTickWillSucceed n_max fs := by
  dsimp only [fastDelete]
  rw [overmarsStep_epochTickWillSucceed]
  cases hfl : fastFindLoc c U n_max θ fs u with
  | none => rfl
  | some loc_del =>
    dsimp only
    have hspec := hv.fastFindLoc_spec u
    rw [hfl] at hspec
    set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
    have hld_lt : loc_del < fs.bktCount b := hspec.1
    by_cases hs4 : fs.rebStage = 4
    · have hbo := hv.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
      obtain ⟨hno_old, _, _⟩ := hbo
      have hrem_buf : (fastDeleteRemove c U n_max θ fs u b loc_del).buf fs.oldEp =
          fs.buf fs.oldEp := by
        have hne_d := hno_old b hb loc_del hld_lt
        dsimp only [fastDeleteRemove]
        rcases hv.curEp_or with hce | hce
        · have ho : fs.oldEp = 1 := by unfold FastState.oldEp; omega
          rw [ho] at hne_d ⊢
          by_cases h2 : fs.locState b loc_del = 2
          · rw [ite_eq_left h2]; exact Function.update_of_ne (by decide) _ _
          · rw [ite_eq_right h2]
            have h3 : fs.locState b loc_del ≠ 3 := hne_d
            rw [ite_eq_right h3]
        · have ho : fs.oldEp = 0 := by unfold FastState.oldEp; omega
          rw [ho] at hne_d ⊢
          have h2 : fs.locState b loc_del ≠ 2 := hne_d
          rw [ite_eq_right h2]
          by_cases h3 : fs.locState b loc_del = 3
          · rw [ite_eq_left h3]; exact Function.update_of_ne (by decide) _ _
          · rw [ite_eq_right h3]
      set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
      have hmv_buf : (if loc_del < fs.bktCount b - 1 then
            fastDeleteMoveLast c U n_max θ b loc_del (fs.bktCount b - 1)
              (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
                fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
                fs.rebCollision = 0)) fs1
          else fs1).buf fs.oldEp = fs.buf fs.oldEp := by
        split_ifs with hlt_l
        · have hll_lt : fs.bktCount b - 1 < fs.bktCount b := by omega
          have hne_l := hno_old b hb (fs.bktCount b - 1) hll_lt
          dsimp only [fastDeleteMoveLast]
          have hls1 : fs1.locState = fs.locState := rfl
          rw [hls1]
          rcases hv.curEp_or with hce | hce
          · have ho : fs.oldEp = 1 := by unfold FastState.oldEp; omega
            rw [ho] at hne_l hrem_buf ⊢
            by_cases h2 : fs.locState b (fs.bktCount b - 1) = 2
            · rw [ite_eq_left h2]; exact (Function.update_of_ne (by decide) _ _).trans hrem_buf
            · rw [ite_eq_right h2]
              have h3 : fs.locState b (fs.bktCount b - 1) ≠ 3 := hne_l
              rw [ite_eq_right h3]; exact hrem_buf
          · have ho : fs.oldEp = 0 := by unfold FastState.oldEp; omega
            rw [ho] at hne_l hrem_buf ⊢
            have h2 : fs.locState b (fs.bktCount b - 1) ≠ 2 := hne_l
            rw [ite_eq_right h2]
            by_cases h3 : fs.locState b (fs.bktCount b - 1) = 3
            · rw [ite_eq_left h3]; exact (Function.update_of_ne (by decide) _ _).trans hrem_buf
            · rw [ite_eq_right h3]; exact hrem_buf
        · exact hrem_buf
      set fs2 := if loc_del < fs.bktCount b - 1 then
        fastDeleteMoveLast c U n_max θ b loc_del (fs.bktCount b - 1)
          (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
            fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebCollision = 0)) fs1
        else fs1
      have hclk2 :
          (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).epochClock = fs.epochClock := by
        dsimp only [fastDeleteShrink, fs2, fs1]; split_ifs <;> rfl
      have hstg2 : (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).rebStage = fs.rebStage := by
        dsimp only [fastDeleteShrink, fs2, fs1]; split_ifs <;> rfl
      have hce2 : (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).curEp = fs.curEp := by
        dsimp only [fastDeleteShrink, fs2, fs1]; split_ifs <;> rfl
      have hold2 : (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).oldEp = fs.oldEp := by
        unfold FastState.oldEp; rw [hce2]
      exact epochTickWillSucceed_eq_of_fields hclk2 hstg2 hce2 (by rw [hold2]; exact hmv_buf)
    · set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
      set fs2 := if loc_del < fs.bktCount b - 1 then
        fastDeleteMoveLast c U n_max θ b loc_del (fs.bktCount b - 1)
          (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
            fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebCollision = 0)) fs1
        else fs1
      have hclk2 :
          (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).epochClock = fs.epochClock := by
        dsimp only [fastDeleteShrink, fs2, fs1]; split_ifs <;> rfl
      have hstg2 : (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).rebStage = fs.rebStage := by
        dsimp only [fastDeleteShrink, fs2, fs1]; split_ifs <;> rfl
      unfold epochTickWillSucceed
      rw [hclk2, hstg2]
      simp [hs4]

/-- Read-only `O(1)` check returning `1` iff `epochTickWillSucceed n_max fs = true`
(`d = (cp, base)`). -/
@[irreducible] private def checkEpochTickOkGenProg : WhpCoreParams × ℕ → Memory.Prog ℕ
  | (cp, base) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z4 ← pure 4
    let z5 ← pure 5
    let c8 ← pure 8
    let clk ← readHdrProg (base, hdrEpochClock)
    let nextClk ← pure (clk + z1)
    let qEp ← pure (wpQEpoch cp)
    if nextClk < qEp then
      pure z1
    else
      let stg ← readHdrProg (base, hdrRebStage)
      if stg = z5 then
        pure z1
      else if stg = z4 then
        let oldEp ← readOldEpProg base
        let allocs ← readBufAllocsProg (base, oldEp)
        if allocs.1 ≤ c8 then
          pure z1
        else
          pure z0
      else
        pure z0

private theorem realizes_checkEpochTickOkGen :
    Realizes .exact checkEpochTickOkGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          fs.epochClock < qEpochWhp n_max)
      (fun _ _ => 0) := by
  unfold checkEpochTickOkGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hra := realizes_readBufAllocs
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce_or, hclk_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hh := hrep.hdrs
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    obtain ⟨hck_st, hck_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrEpochClock)
      (by dsimp [hdrEpochClock]; omega) (s := s)
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce_or
      hh.curEp (s := s)
    rw [hh.epochClock] at hck_res
    rw [hh.rebStage] at hst_res
    simp only [hck_st, hck_res, hst_st, hst_res, hro_st, hro_res] at *
    first
    | exact h2w
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrEpochClock, hdrRebStage, hdrCurEp]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
  )

private theorem checkEpochTickOkGenProg_spec {c U V w n_max base : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := checkEpochTickOkGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if epochTickWillSucceed n_max fs then 1 else 0) ∧
    memoryCost prog s ≤ 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hh := hrep.hdrs
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hce_or with h01 | h01 <;> simp [FastState.oldEp, h01]
  obtain ⟨hck_st, hck_res, hck_mc, hck_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrEpochClock)
    (by dsimp [hdrEpochClock]; omega) (s := s)
  rw [hh.epochClock] at hck_res
  dsimp only
  unfold checkEpochTickOkGenProg; simp only [pure_bind, wp_large_qEpoch hth]
  unfold epochTickWillSucceed
  by_cases hlt : fs.epochClock + 1 < qEpochWhp n_max
  · rw [decide_eq_true (Or.inl hlt)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hck_st, hck_res, ite_eq_left hlt]; rfl
    · rw [clientResult_bind, hck_st, hck_res, ite_eq_left hlt]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hck_st, hck_res, hck_mc, ite_eq_left hlt, memoryCost_pure]; omega
    · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_left hlt]
      exact validProg_pure _
  · obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    rw [hh.rebStage] at hst_res
    by_cases hs5 : fs.rebStage = 5
    · rw [decide_eq_true (Or.inr (Or.inl hs5))]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hck_st, hck_res, ite_eq_right hlt,
          clientState_bind, hst_st, hst_res, ite_eq_left hs5]; rfl
      · rw [clientResult_bind, hck_st, hck_res, ite_eq_right hlt,
          clientResult_bind, hst_st, hst_res, ite_eq_left hs5]; rfl
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hck_st, hck_res, hck_mc, ite_eq_right hlt]
        simp only [memoryCost_bind]
        rw [hst_st, hst_res, hst_mc, ite_eq_left hs5, memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_right hlt]
        refine validProg_bind hst_vp ?_; rw [hst_st, hst_res, ite_eq_left hs5]
        exact validProg_pure _
    · by_cases hs4 : fs.rebStage = 4
      · obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
          (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce_or
          hh.curEp (s := s)
        obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ :=
          readBufAllocsProg_spec henv hold_or hrep (s := s)
        by_cases h8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
        · rw [decide_eq_true (Or.inr (Or.inr ⟨hs4, h8⟩))]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [clientState_bind, hck_st, hck_res, ite_eq_right hlt,
              clientState_bind, hst_st, hst_res, ite_eq_right hs5, ite_eq_left hs4,
              clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res]
            dsimp only; rw [ite_eq_left h8]; rfl
          · rw [clientResult_bind, hck_st, hck_res, ite_eq_right hlt,
              clientResult_bind, hst_st, hst_res, ite_eq_right hs5, ite_eq_left hs4,
              clientResult_bind, hro_st, hro_res, clientResult_bind, hra_st, hra_res]
            dsimp only; rw [ite_eq_left h8]; rfl
          · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hck_st, hck_res, hck_mc, ite_eq_right hlt]; simp only [memoryCost_bind]
            rw [hst_st, hst_res, hst_mc, ite_eq_right hs5, ite_eq_left hs4]
            simp only [memoryCost_bind]
            rw [hro_st, hro_res, hro_mc, hra_st, hra_res]; dsimp only
            rw [ite_eq_left h8, memoryCost_pure]; omega
          · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_right hlt]
            refine validProg_bind hst_vp ?_
            rw [hst_st, hst_res, ite_eq_right hs5, ite_eq_left hs4]
            refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
            refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]; dsimp only
            rw [ite_eq_left h8]; exact validProg_pure _
        · rw [decide_eq_false (by intro h; rcases h with h1 | h2 | ⟨_, h3⟩ <;> omega)]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [clientState_bind, hck_st, hck_res, ite_eq_right hlt,
              clientState_bind, hst_st, hst_res, ite_eq_right hs5, ite_eq_left hs4,
              clientState_bind, hro_st, hro_res, clientState_bind, hra_st, hra_res]
            dsimp only; rw [ite_eq_right h8]; rfl
          · rw [clientResult_bind, hck_st, hck_res, ite_eq_right hlt,
              clientResult_bind, hst_st, hst_res, ite_eq_right hs5, ite_eq_left hs4,
              clientResult_bind, hro_st, hro_res, clientResult_bind, hra_st, hra_res]
            dsimp only; rw [ite_eq_right h8]; rfl
          · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
            rw [hck_st, hck_res, hck_mc, ite_eq_right hlt]; simp only [memoryCost_bind]
            rw [hst_st, hst_res, hst_mc, ite_eq_right hs5, ite_eq_left hs4]
            simp only [memoryCost_bind]
            rw [hro_st, hro_res, hro_mc, hra_st, hra_res]; dsimp only
            rw [ite_eq_right h8, memoryCost_pure]; omega
          · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_right hlt]
            refine validProg_bind hst_vp ?_
            rw [hst_st, hst_res, ite_eq_right hs5, ite_eq_left hs4]
            refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
            refine validProg_bind hra_vp ?_; rw [hra_st, hra_res]; dsimp only
            rw [ite_eq_right h8]; exact validProg_pure _
      · rw [decide_eq_false (by intro h; rcases h with h1 | h2 | ⟨h3, _⟩ <;> omega)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [clientState_bind, hck_st, hck_res, ite_eq_right hlt,
            clientState_bind, hst_st, hst_res, ite_eq_right hs5, ite_eq_right hs4]; rfl
        · rw [clientResult_bind, hck_st, hck_res, ite_eq_right hlt,
            clientResult_bind, hst_st, hst_res, ite_eq_right hs5, ite_eq_right hs4]; rfl
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hck_st, hck_res, hck_mc, ite_eq_right hlt]; simp only [memoryCost_bind]
          rw [hst_st, hst_res, hst_mc, ite_eq_right hs5, ite_eq_right hs4, memoryCost_pure]
          omega
        · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res, ite_eq_right hlt]
          refine validProg_bind hst_vp ?_
          rw [hst_st, hst_res, ite_eq_right hs5, ite_eq_right hs4]
          exact validProg_pure _

/-- `c`-only worst-case `memoryCost` bound for a fast-mode operation (`fastStepPureGenProg`). -/
@[expose] def fastOpCostWhp (c : ℕ) : ℕ :=
  32 * cTabWhp c + 73 * hashEvalCostWhp c + 90000

@[irreducible] private def fastStepQueryProg :
    (WhpParams × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), u_val) => do
    let z1 ← pure 1
    let res ← fastQueryGenProg ((wp, base), u_val)
    epochTickGenProg (wp, base)
    pure (z1, res)

private theorem realizes_fastStepQuery :
    Realizes .exact fastStepQueryProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (u : Fin U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val = u.val)
      (fun _ _ => 0) := by
  unfold fastStepQueryProg
  have hfq := realizes_fastQueryGen
  have het := realizes_epochTickGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hseed, hrep, hv, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hfq_st, _, _, _⟩ := fastQueryGenProg_spec henv hseed hrep hv u (s := s)
    simp only [hfq_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_U hth]; exact u.isLt)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv.toCore,
        hv.stage_valid.toPreTick⟩
  )

@[irreducible] private def fastStepInsertProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (((wp, base), u_val), v_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let insOk ← fastInsertGenProg (((wp, base), u_val), v_val)
    if insOk = z1 then
      epochTickGenProg (wp, base)
      pure (z1, (z0, z0))
    else
      pure (z0, (z0, z0))

private theorem realizes_fastStepInsert :
    Realizes .exact fastStepInsertProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (((wp, base), u_val), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (u : Fin U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          Dynamic.valid V n_max dict (.insert u v_val) ∧
          u_val = u.val)
      (fun _ _ => 0) := by
  unfold fastStepInsertProg
  have hfi := realizes_fastInsertGen
  have het := realizes_epochTickGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, u_val⟩, v_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hseed, hrep, hv, hval_op, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hnU := henv.2.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨_, _, hfi_m⟩ := fastInsertGenProg_spec henv hseed hrep hv u hval_op.2 (s := s)
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_U hth]; exact u.isLt)
    | (rw [hcp_eq, wp_large_V hth]; exact hval_op.2)
    | (cases hins : fastInsert c U n_max θ fs u v_val with
       | none =>
         rw [hins] at hfi_m
         have hhit : (Memory.spec 0).clientResult s
           (fastInsertGenProg (((mkWhpParams c U V w n_max, base), u.val), v_val)) = 1 :=
             by assumption
         rw [hfi_m.1] at hhit; cases hhit
       | some fs1 =>
         rw [hins] at hfi_m
         obtain ⟨hcore1, _, hst1, _⟩ := hv.fastInsert_spec hnU hval_op hins
         exact ⟨c, U, V, w, n_max, θ, fs1, (Dynamic.step dict (.insert u v_val)).1,
           henv, rfl, hfi_m.2.2.1, hfi_m.2.2.2.1, hcore1, hst1.toPreTick⟩)
  )

@[irreducible] private def fastStepDeleteProg :
    (WhpParams × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), u_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    fastDeleteGenProg ((wp, base), u_val)
    epochTickGenProg (wp, base)
    pure (z1, (z0, z0))

private theorem realizes_fastStepDelete :
    Realizes .exact fastStepDeleteProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (u : Fin U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val = u.val)
      (fun _ _ => 0) := by
  unfold fastStepDeleteProg
  have hfd := realizes_fastDeleteGen
  have het := realizes_epochTickGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hseed, hrep, hv, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨_, _, hfd_step⟩ := fastDeleteGenProg_fastStep henv hseed hrep hv u (s := s)
    obtain ⟨hcore1, _, hpre1, _⟩ := hv.fastDelete_spec u
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_U hth]; exact u.isLt)
    | exact ⟨c, U, V, w, n_max, θ, fastDelete c U n_max θ fs u,
        (Dynamic.step dict (.delete u)).1, henv, rfl,
        hfd_step.2.1, hfd_step.2.2.1, hcore1, hpre1⟩
  )

/-- Combined fast-mode operation dispatcher (`d = ((wp, base), (opTag, (u_val, v_val)))`),
returning `(1, encodeOptRes res)` when `fastStepPure = some (fs', res)` and `(0, (0, 0))` without
mutating memory when `fastStepPure = none`. -/
@[irreducible] def fastStepPureGenProg :
    (WhpParams × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), (opTag, (u_val, v_val))) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let tickOk ← checkEpochTickOkGenProg (wp.1, base)
    if tickOk = z1 then
      if opTag = z0 then
        fastStepQueryProg ((wp, base), u_val)
      else if opTag = z1 then
        fastStepInsertProg (((wp, base), u_val), v_val)
      else
        fastStepDeleteProg ((wp, base), u_val)
    else
      pure (z0, (z0, z0))

theorem realizes_fastStepPureGen :
    Realizes .exact fastStepPureGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), (opTag, (u_val, v_val))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (op : Dynamic.Op U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          Dynamic.valid V n_max dict op ∧
          encodeOpWhp op = (opTag, (u_val, v_val)))
      (fun _ _ => 0) := by
  unfold fastStepPureGenProg
  have hck := realizes_checkEpochTickOkGen
  have hsq := realizes_fastStepQuery
  have hsi := realizes_fastStepInsert
  have hsd := realizes_fastStepDelete
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨opTag, ⟨u_val, v_val⟩⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, op, henv, heq_wp, hseed, hrep, hv, hval_op,
      hop_enc⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hck_st, hck_res, _, _⟩ :=
      checkEpochTickOkGenProg_spec henv hv.curEp_or hrep (s := s)
    simp only [hcp_eq] at *
    simp only [hck_st, hck_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hv.curEp_or, hv.epochClock_lt⟩
    | (cases op with
       | query u =>
         dsimp only [encodeOpWhp] at hop_enc
         rcases Prod.mk.inj hop_enc with ⟨rfl, hp2⟩
         rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hseed, hrep, hv, rfl⟩
       | insert u v =>
         dsimp only [encodeOpWhp] at hop_enc
         rcases Prod.mk.inj hop_enc with ⟨rfl, hp2⟩
         rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hseed, hrep, hv, hval_op, rfl⟩
       | delete u =>
         dsimp only [encodeOpWhp] at hop_enc
         rcases Prod.mk.inj hop_enc with ⟨rfl, hp2⟩
         rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hseed, hrep, hv, rfl⟩)
  )

theorem fastStepPureGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    {op : Dynamic.Op U} (hval_op : Dynamic.valid V n_max dict op) :
    let prog := fastStepPureGenProg ((mkWhpParams c U V w n_max, base), encodeOpWhp op)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ fastOpCostWhp c ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    match fastStepPure c U n_max θ fs op with
    | some (fs', res) =>
      (Memory.spec 0).clientResult s prog = (1, encodeOptRes res) ∧
      FastStateStep base c U V w n_max θ fs' s s'
    | none =>
      (Memory.spec 0).clientResult s prog = (0, (0, 0)) ∧
      s' = s := by
  have hth := henv.2.2.2.1
  have hnU := henv.2.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hck_st, hck_res, hck_mc, hck_vp⟩ :=
    checkEpochTickOkGenProg_spec henv hv.curEp_or hrep (s := s)
  dsimp only [fastOpCostWhp]
  cases op with
  | query u =>
    dsimp only [encodeOpWhp, fastStepPure]
    unfold fastStepPureGenProg fastStepQueryProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [pure_bind]
    by_cases hok : epochTickWillSucceed n_max fs = true
    · rw [hok] at hck_res; simp only [↓reduceIte] at hck_res
      obtain ⟨hfq_st, hfq_res, hfq_mc, hfq_vp⟩ :=
        fastQueryGenProg_spec henv hseed hrep hv u (s := s)
      obtain ⟨fs', het_eq, het_mc, het_vp, het_step⟩ :=
        epochTickGenProg_fastStep henv hv.toCore hv.stage_valid.toPreTick hok hseed hrep (s := s)
      rw [het_eq]
      have hres_eq : (Memory.spec 0).clientResult s
          (fastQueryGenProg ((mkWhpParams c U V w n_max, base), u.val)) =
          encodeOptRes (fastQuery c U n_max θ fs u) := by
        refine hfq_res.trans ?_
        cases fastQuery c U n_max θ fs u <;> rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [cp] at hck_st hck_res hck_mc ⊢
        rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
        rw [hfq_st, hres_eq, memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
        refine validProg_bind hfq_vp ?_; rw [hfq_st, hres_eq]
        exact validProg_bind het_vp (validProg_pure _)
      · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientResult_bind, hfq_st, hres_eq, clientResult_bind]; rfl
      · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientState_bind, hfq_st, clientState_bind, clientState_pure_whp]
        exact het_step
    · have hnot : epochTickWillSucceed n_max fs = false := Bool.eq_false_iff.mpr hok
      rw [hnot] at hck_res; simp only [Bool.false_eq_true, ↓reduceIte] at hck_res
      have hnone : epochTick c U n_max θ fs = none := by
        have his := epochTick_isSome_iff θ hv.rebStage_le
        rw [hnot] at his
        cases h : epochTick c U n_max θ fs with
        | none => rfl
        | some _ => rw [h] at his; cases his
      rw [hnone]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [cp] at hck_st hck_res hck_mc ⊢
        rw [hck_st, hck_res]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]
        simp only [zero_ne_one, ↓reduceIte]; exact validProg_pure _
      · rw [clientResult_bind, hck_st, hck_res]; rfl
      · rw [clientState_bind, hck_st, hck_res]; rfl
  | insert u v =>
    dsimp only [encodeOpWhp, fastStepPure]
    unfold fastStepPureGenProg fastStepInsertProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [pure_bind, one_ne_zero, ↓reduceIte]
    by_cases hok : epochTickWillSucceed n_max fs = true
    · rw [hok] at hck_res; simp only [↓reduceIte] at hck_res
      obtain ⟨hfi_mc, hfi_vp, hfi_m⟩ :=
        fastInsertGenProg_spec henv hseed hrep hv u hval_op.2 (s := s)
      set progIns := fastInsertGenProg (((mkWhpParams c U V w n_max, base), u.val), v)
      set s1 := (Memory.spec 0).clientState s progIns
      cases hins : fastInsert c U n_max θ fs u v with
      | none =>
        rw [hins] at hfi_m
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          dsimp only [cp] at hck_st hck_res hck_mc ⊢
          rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
          dsimp only [progIns] at hfi_m hfi_mc ⊢
          rw [hfi_m.1]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
        · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
          refine validProg_bind hfi_vp ?_; dsimp only [progIns] at hfi_m
          rw [hfi_m.1]; simp only [zero_ne_one, ↓reduceIte]; exact validProg_pure _
        · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientResult_bind]; dsimp only [progIns] at hfi_m; rw [hfi_m.1]; rfl
        · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientState_bind]; dsimp only [progIns, s1] at hfi_m
          rw [hfi_m.1, hfi_m.2]; rfl
      | some fs1 =>
        rw [hins] at hfi_m; dsimp only
        obtain ⟨hcore1, _, hst1, _⟩ := hv.fastInsert_spec hnU hval_op hins
        have hok1 : epochTickWillSucceed n_max fs1 = true :=
          (epochTickWillSucceed_fastInsert hv hins).trans hok
        obtain ⟨fs', het_eq, het_mc, het_vp, het_step⟩ :=
          epochTickGenProg_fastStep henv hcore1 hst1.toPreTick hok1
            hfi_m.2.2.1 hfi_m.2.2.2.1 (s := s1)
        rw [het_eq]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          dsimp only [cp] at hck_st hck_res hck_mc ⊢
          rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
          dsimp only [progIns, s1] at hfi_m hfi_mc het_mc ⊢
          rw [hfi_m.1]; simp only [↓reduceIte, memoryCost_bind, memoryCost_pure]; omega
        · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
          refine validProg_bind hfi_vp ?_; dsimp only [progIns] at hfi_m
          rw [hfi_m.1]; simp only [↓reduceIte]
          exact validProg_bind het_vp (validProg_pure _)
        · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientResult_bind]; dsimp only [progIns] at hfi_m; rw [hfi_m.1]
          simp only [↓reduceIte]; rw [clientResult_bind]; rfl
        · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
          rw [clientState_bind]; dsimp only [progIns] at hfi_m; rw [hfi_m.1]
          simp only [↓reduceIte]; rw [clientState_bind, clientState_pure_whp]
          exact hfi_m.2.trans het_step
    · have hnot : epochTickWillSucceed n_max fs = false := Bool.eq_false_iff.mpr hok
      rw [hnot] at hck_res; simp only [Bool.false_eq_true, ↓reduceIte] at hck_res
      refine ⟨?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [cp] at hck_st hck_res hck_mc ⊢
        rw [hck_st, hck_res]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]
        simp only [zero_ne_one, ↓reduceIte]; exact validProg_pure _
      · cases hins : fastInsert c U n_max θ fs u v with
        | none =>
          dsimp only
          exact ⟨by rw [clientResult_bind, hck_st, hck_res]; rfl,
                 by rw [clientState_bind, hck_st, hck_res]; rfl⟩
        | some fs1 =>
          obtain ⟨hcore1, _, _, _⟩ := hv.fastInsert_spec hnU hval_op hins
          have hnot1 : epochTickWillSucceed n_max fs1 = false :=
            (epochTickWillSucceed_fastInsert hv hins).trans hnot
          have his1 := epochTick_isSome_iff θ hcore1.rebStage_le
          rw [hnot1] at his1
          have hnone1 : epochTick c U n_max θ fs1 = none := by
            cases h : epochTick c U n_max θ fs1 with
            | none => rfl
            | some _ => rw [h] at his1; cases his1
          dsimp only; rw [hnone1]; dsimp only
          exact ⟨by rw [clientResult_bind, hck_st, hck_res]; rfl,
                 by rw [clientState_bind, hck_st, hck_res]; rfl⟩
  | delete u =>
    dsimp only [encodeOpWhp, fastStepPure]
    unfold fastStepPureGenProg fastStepDeleteProg; dsimp only
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [pure_bind, show ¬((2 : ℕ) = 0) by decide, show ¬((2 : ℕ) = 1) by decide,
      ↓reduceIte]
    obtain ⟨hcore1, _, hpre1, _⟩ := hv.fastDelete_spec u
    by_cases hok : epochTickWillSucceed n_max fs = true
    · rw [hok] at hck_res; simp only [↓reduceIte] at hck_res
      obtain ⟨hfd_mc, hfd_vp, hfd_step⟩ := fastDeleteGenProg_fastStep henv hseed hrep hv u (s := s)
      set s1 := (Memory.spec 0).clientState s
        (fastDeleteGenProg ((mkWhpParams c U V w n_max, base), u.val))
      have hok1 : epochTickWillSucceed n_max (fastDelete c U n_max θ fs u) = true :=
        (epochTickWillSucceed_fastDelete hv u).trans hok
      obtain ⟨fs', het_eq, het_mc, het_vp, het_step⟩ :=
        epochTickGenProg_fastStep henv hcore1 hpre1 hok1 hfd_step.2.1 hfd_step.2.2.1 (s := s1)
      rw [het_eq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [cp] at hck_st hck_res hck_mc ⊢
        rw [hck_st, hck_res]; simp only [↓reduceIte, memoryCost_bind]
        dsimp only [s1] at hfd_mc het_mc ⊢
        rw [memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]; simp only [↓reduceIte]
        refine validProg_bind hfd_vp ?_
        exact validProg_bind het_vp (validProg_pure _)
      · rw [clientResult_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientResult_bind, clientResult_bind]; rfl
      · rw [clientState_bind, hck_st, hck_res]; simp only [↓reduceIte]
        rw [clientState_bind, clientState_bind, clientState_pure_whp]
        exact hfd_step.trans het_step
    · have hnot : epochTickWillSucceed n_max fs = false := Bool.eq_false_iff.mpr hok
      rw [hnot] at hck_res; simp only [Bool.false_eq_true, ↓reduceIte] at hck_res
      have hnot1 : epochTickWillSucceed n_max (fastDelete c U n_max θ fs u) = false :=
        (epochTickWillSucceed_fastDelete hv u).trans hnot
      have his1 := epochTick_isSome_iff θ hcore1.rebStage_le
      rw [hnot1] at his1
      have hnone1 : epochTick c U n_max θ (fastDelete c U n_max θ fs u) = none := by
        cases h : epochTick c U n_max θ (fastDelete c U n_max θ fs u) with
        | none => rfl
        | some _ => rw [h] at his1; cases his1
      rw [hnone1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        dsimp only [cp] at hck_st hck_res hck_mc ⊢
        rw [hck_st, hck_res]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
      · refine validProg_bind hck_vp ?_; rw [hck_st, hck_res]
        simp only [zero_ne_one, ↓reduceIte]; exact validProg_pure _
      · rw [clientResult_bind, hck_st, hck_res]; rfl
      · rw [clientState_bind, hck_st, hck_res]; rfl

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

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
# Stage-2 Candidate-Salt Scan Loop (`rebScanLoopGenProg`)

Implements and verifies `rebScanOneProg` and its `Realizes.iterate₀` wrapper `rebScanLoopGenProg`,
refining `rebScanSteps c U n_max θ b k fs` in `O_c(1)` per iteration.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Precondition for `rebScanOneProg` (`p = (((wp, base), b), ())`). -/
def RebScanOnePre (w : ℕ) :
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
    have hh1 := fastMemHdrs hbi_step.2.2.1
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
  have hh1 := fastMemHdrs hbi_step.2.2.1
  rw [hh1.rebInsCount] at hi_res
  dsimp only [fs1] at hi_res
  have hw1 := writeHdrStep (fs := fs1) henv (by dsimp [hdrRebScanCursor]; decide)
    (henv.fits_of_le_n_max (by omega)) (fun h => by dsimp [hdrRebScanCursor] at h; omega)
    hbi_step.2.1 hbi_step.2.2.1 (hdrOff := hdrRebScanCursor) (val := cur + 1) (s := s1)
  have hw2 := thenWriteHdr (hdrOff := hdrRebInsCount) (val := fs.rebInsCount + 1) henv
    (by dsimp [hdrRebInsCount]; decide) (henv.fits_of_le_n_max (by omega))
    (fun h => by dsimp [hdrRebInsCount] at h; omega) hw1
  dsimp only
  unfold rebScanCommitNoneProg; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (btreeInsertGenProg ((((cp, base), rIdx), fp), cur) >>= fun _ =>
        readHdrProg (base, hdrRebInsCount) >>= fun ins =>
        writeHdrProg ((base, hdrRebScanCursor), cur + 1) >>= fun _ =>
        writeHdrProg ((base, hdrRebInsCount), ins + 1)) =
      (Memory.spec 0).clientState s1
        (writeHdrProg ((base, hdrRebScanCursor), cur + 1) >>= fun _ =>
          writeHdrProg ((base, hdrRebInsCount), fs.rebInsCount + 1)) := by
    rw [clientState_bind, clientState_bind, hi_st, hi_res]
  rw [hs'_eq]
  refine ⟨?_, ?_, hbi_step.trans hw2.2.2⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hi_st, hi_res, hi_mc]
    have hwm := hw2.1
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind] at hwm
    dsimp only [s1, cp] at hbi_mc hwm ⊢; omega
  · refine validProg_bind hbi_vp ?_
    refine validProg_bind hi_vp ?_; rw [hi_st, hi_res]; exact hw2.2.1

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
    have hh := fastMemHdrs hrep
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
    have hh := fastMemHdrs hrep
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
def rebScanOneProg : ((WhpParams × ℕ) × ℕ) × Unit → Memory.Prog Unit
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
    have hh := fastMemHdrs hrep
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

private theorem rebScanOne_inBounds_insert_lift {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs fsOut : FastState} {s : Memory.State}
    {pTail : Memory.Prog Unit} {lkFlag cTail : ℕ}
    (hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max)
    (hc0 : fs.rebCollision = 0) (hcur_lt : fs.rebScanCursor < fs.bktCount b)
    (hst_act : fs.locState b fs.rebScanCursor = 1 ∨ fs.locState b fs.rebScanCursor = 2 + fs.oldEp)
    (hc_st : (Memory.spec 0).clientState s (Memory.read (base + hdrRebCollision)) = s)
    (hc_res : (Memory.spec 0).clientResult s (Memory.read (base + hdrRebCollision)) =
      fs.rebCollision)
    (hc_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (Memory.read (base + hdrRebCollision)))
    (hcur_st : (Memory.spec 0).clientState s (readHdrProg (base, hdrRebScanCursor)) = s)
    (hcur_res : (Memory.spec 0).clientResult s (readHdrProg (base, hdrRebScanCursor)) =
      fs.rebScanCursor)
    (hcur_mc : memoryCost (readHdrProg (base, hdrRebScanCursor)) s = 1)
    (hcur_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readHdrProg (base, hdrRebScanCursor)))
    (h0_st : (Memory.spec 0).clientState s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)) = s)
    (h0_res : (Memory.spec 0).clientResult s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)) = fs.bktCount b)
    (h0_mc : memoryCost
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)) s ≤ 2)
    (h0_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)))
    (hrl_st : (Memory.spec 0).clientState s
      (readFastLocGenProg (((mkWhpCoreParams c U V w n_max, base), b), fs.rebScanCursor)) = s)
    (hrl_res : (Memory.spec 0).clientResult s
      (readFastLocGenProg (((mkWhpCoreParams c U V w n_max, base), b), fs.rebScanCursor)) =
      fs.locState b fs.rebScanCursor)
    (hrl_mc : memoryCost
      (readFastLocGenProg (((mkWhpCoreParams c U V w n_max, base), b), fs.rebScanCursor)) s = 2)
    (hrl_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readFastLocGenProg (((mkWhpCoreParams c U V w n_max, base), b), fs.rebScanCursor)))
    (hro_st : (Memory.spec 0).clientState s (readOldEpProg base) = s)
    (hro_res : (Memory.spec 0).clientResult s (readOldEpProg base) = fs.oldEp)
    (hro_mc : memoryCost (readOldEpProg base) s = 1)
    (hro_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s (readOldEpProg base))
    (hcs_st : (Memory.spec 0).clientState s (readHdrProg (base, hdrRebCandSalt)) = s)
    (hcs_res : (Memory.spec 0).clientResult s (readHdrProg (base, hdrRebCandSalt)) = fs.rebCandSalt)
    (hcs_mc : memoryCost (readHdrProg (base, hdrRebCandSalt)) s = 1)
    (hcs_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readHdrProg (base, hdrRebCandSalt)))
    (hfp_st : (Memory.spec 0).clientState s (fpAtGenProg
      ((((mkWhpParams c U V w n_max, base), fs.rebCandSalt), b), fs.rebScanCursor)) = s)
    (hfp_res : (Memory.spec 0).clientResult s (fpAtGenProg
      ((((mkWhpParams c U V w n_max, base), fs.rebCandSalt), b), fs.rebScanCursor)) =
      fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor)
    (hfp_mc : memoryCost (fpAtGenProg
      ((((mkWhpParams c U V w n_max, base), fs.rebCandSalt), b), fs.rebScanCursor)) s ≤
      2 * hashEvalCostWhp c + 4)
    (hfp_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s (fpAtGenProg
      ((((mkWhpParams c U V w n_max, base), fs.rebCandSalt), b), fs.rebScanCursor)))
    (hrs_st : (Memory.spec 0).clientState s
      (readRebSliceIdxGenProg ((mkWhpCoreParams c U V w n_max, base), b)) = s)
    (hrs_res : (Memory.spec 0).clientResult s
      (readRebSliceIdxGenProg ((mkWhpCoreParams c U V w n_max, base), b)) = fs.rebSliceIdx b)
    (hrs_mc : memoryCost
      (readRebSliceIdxGenProg ((mkWhpCoreParams c U V w n_max, base), b)) s = 4)
    (hrs_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readRebSliceIdxGenProg ((mkWhpCoreParams c U V w n_max, base), b)))
    (hbl_st : (Memory.spec 0).clientState s (btreeLookupGenProg (((mkWhpCoreParams c U V w n_max,
      base), fs.rebSliceIdx b), fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor)) = s)
    (hbl_fst : ((Memory.spec 0).clientResult s (btreeLookupGenProg (((mkWhpCoreParams c U V w n_max,
      base), fs.rebSliceIdx b), fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor))).1 =
      lkFlag)
    (hbl_mc : memoryCost (btreeLookupGenProg (((mkWhpCoreParams c U V w n_max, base),
      fs.rebSliceIdx b), fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor)) s ≤ 262)
    (hbl_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s (btreeLookupGenProg
      (((mkWhpCoreParams c U V w n_max, base), fs.rebSliceIdx b),
        fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor)))
    (htail_eq : (if lkFlag = 1 then writeHdrProg ((base, hdrRebCollision), 1)
      else rebScanCommitNoneProg ((((mkWhpCoreParams c U V w n_max, base), fs.rebSliceIdx b),
        fs.fpAt c U n_max θ fs.rebCandSalt b fs.rebScanCursor), fs.rebScanCursor)) = pTail)
    (hcTail_le : cTail ≤ 2445)
    (htail_mc : memoryCost pTail s ≤ cTail)
    (htail_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s pTail)
    (htail_step : FastStateStep base c U V w n_max θ fsOut s
      ((Memory.spec 0).clientState s pTail)) :
    let prog := Memory.read (base + hdrRebCollision) >>= fun coll =>
      if coll = 0 then
        readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
        readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0) >>= fun cnt =>
        if cur < cnt then rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
        else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
      else pure ()
    memoryCost prog s ≤ 2 * hashEvalCostWhp c + 2740 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsOut s ((Memory.spec 0).clientState s prog) := by
  set cp := mkWhpCoreParams c U V w n_max
  set cur := fs.rebScanCursor
  set fp := fs.fpAt c U n_max θ fs.rebCandSalt b cur
  have hst_eq :
      (Memory.spec 0).clientState s (Memory.read (base + hdrRebCollision) >>= fun coll =>
        if coll = 0 then
          readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
          readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0) >>= fun cnt =>
          if cur < cnt then rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
          else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
        else pure ()) =
      (Memory.spec 0).clientState s pTail := by
    rw [clientState_bind, hc_st, hc_res, ite_eq_left hc0,
      clientState_bind, hcur_st, hcur_res, clientState_bind, h0_st, h0_res,
      ite_eq_left hcur_lt]
    unfold rebScanInBoundsProg; dsimp only; rw [hwp1]; simp only [pure_bind]
    rw [clientState_bind, hrl_st, hrl_res, clientState_bind, hro_st, hro_res, ite_eq_left hst_act]
    unfold rebScanInsertCoordProg; dsimp only; rw [hwp1]; simp only [pure_bind]
    rw [clientState_bind, hcs_st, hcs_res, clientState_bind, hfp_st, hfp_res,
      clientState_bind, hrs_st, hrs_res, clientState_bind, hbl_st, hbl_fst, htail_eq]
  dsimp only; rw [hst_eq]
  refine ⟨?_, ?_, htail_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hc_st, hc_res, ite_eq_left hc0]; simp only [memoryCost_bind]
    rw [hcur_st, hcur_res, hcur_mc, h0_st, h0_res, ite_eq_left hcur_lt]
    unfold rebScanInBoundsProg; dsimp only; rw [hwp1]
    simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrl_st, hrl_res, hro_st, hro_res, ite_eq_left hst_act]
    unfold rebScanInsertCoordProg; dsimp only; rw [hwp1]
    simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hcs_st, hcs_res, hcs_mc, hfp_st, hfp_res, hrs_st, hrs_res, hbl_st, hbl_fst, htail_eq]
    have hc1 : memoryCost (Memory.read (base + hdrRebCollision)) s = 1 := rfl
    omega
  · refine validProg_bind hc_vp ?_; rw [hc_st, hc_res, ite_eq_left hc0]
    refine validProg_bind hcur_vp ?_; rw [hcur_st, hcur_res]
    refine validProg_bind h0_vp ?_; rw [h0_st, h0_res, ite_eq_left hcur_lt]
    unfold rebScanInBoundsProg; dsimp only; rw [hwp1]; simp only [pure_bind]
    refine validProg_bind hrl_vp ?_; rw [hrl_st, hrl_res]
    refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_left hst_act]
    unfold rebScanInsertCoordProg; dsimp only; rw [hwp1]; simp only [pure_bind]
    refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]
    refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
    refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
    refine validProg_bind hbl_vp ?_; rw [hbl_st, hbl_fst, htail_eq]; exact htail_vp

private theorem rebScanOne_bumpCursor_lift {c U V w n_max base b tailCost : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {rm : ℕ → Option ℕ} {s : Memory.State}
    {pBr : Memory.Prog Unit}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hc0 : fs.rebCollision = 0)
    (hcur_n : fs.rebScanCursor < n_max)
    (hv_r : ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hc_st : (Memory.spec 0).clientState s (Memory.read (base + hdrRebCollision)) = s)
    (hc_res : (Memory.spec 0).clientResult s (Memory.read (base + hdrRebCollision)) =
      fs.rebCollision)
    (hc_mc : memoryCost (Memory.read (base + hdrRebCollision)) s = 1)
    (hc_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (Memory.read (base + hdrRebCollision)))
    (hcur_st : (Memory.spec 0).clientState s (readHdrProg (base, hdrRebScanCursor)) = s)
    (hcur_res : (Memory.spec 0).clientResult s (readHdrProg (base, hdrRebScanCursor)) =
      fs.rebScanCursor)
    (hcur_mc : memoryCost (readHdrProg (base, hdrRebScanCursor)) s = 1)
    (hcur_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readHdrProg (base, hdrRebScanCursor)))
    (h0_st : (Memory.spec 0).clientState s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)) = s)
    (h0_res : (Memory.spec 0).clientResult s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)) = fs.bktCount b)
    (h0_mc : memoryCost
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)) s ≤ 2)
    (h0_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0)))
    (hBr_eq : (if fs.rebScanCursor < fs.bktCount b then
        rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), fs.rebScanCursor)
      else writeHdrProg ((base, hdrRebScanCursor), fs.rebScanCursor + 1)) = pBr)
    (hBr_st : (Memory.spec 0).clientState s pBr = (Memory.spec 0).clientState s
      (writeHdrProg ((base, hdrRebScanCursor), fs.rebScanCursor + 1)))
    (hBr_mc : memoryCost pBr s ≤ tailCost)
    (hBr_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s pBr) :
    let cp := mkWhpCoreParams c U V w n_max
    let prog := Memory.read (base + hdrRebCollision) >>= fun coll =>
      if coll = 0 then
        readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
        readBktFieldGenProg (((cp, base), b), 0) >>= fun cnt =>
        if cur < cnt then
          rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
        else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
      else pure ()
    let fs1 : FastState := { fs with rebScanCursor := fs.rebScanCursor + 1 }
    memoryCost prog s ≤ tailCost + 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs1 s ((Memory.spec 0).clientState s prog) ∧
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
  have hw := writeHdrStep (fs := fs) henv (by dsimp [hdrRebScanCursor]; decide)
    (henv.fits_of_le_n_max (by omega)) (fun h => by dsimp [hdrRebScanCursor] at h; omega)
    hseed hrep (hdrOff := hdrRebScanCursor) (val := fs.rebScanCursor + 1) (s := s)
  have hs'_eq : (Memory.spec 0).clientState s
      (Memory.read (base + hdrRebCollision) >>= fun coll =>
        if coll = 0 then
          readHdrProg (base, hdrRebScanCursor) >>= fun cur =>
          readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 0) >>= fun cnt =>
          if cur < cnt then
            rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)
          else writeHdrProg ((base, hdrRebScanCursor), cur + 1)
        else pure ()) =
      (Memory.spec 0).clientState s
        (writeHdrProg ((base, hdrRebScanCursor), fs.rebScanCursor + 1)) := by
    rw [clientState_bind, hc_st, hc_res, ite_eq_left hc0,
      clientState_bind, hcur_st, hcur_res, clientState_bind, h0_st, h0_res, hBr_eq, hBr_st]
  dsimp only
  rw [hs'_eq]
  refine ⟨?_, ?_, hw.2.2, rfl, rfl, rfl, rfl, rfl,
    fun _ => ⟨hc0, rfl, Nat.le_succ _, rm, hv_r⟩⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hc_st, hc_res, hc_mc, ite_eq_left hc0]; simp only [memoryCost_bind]
    rw [hcur_st, hcur_res, hcur_mc, h0_st, h0_res, hBr_eq]
    omega
  · refine validProg_bind hc_vp ?_; rw [hc_st, hc_res, ite_eq_left hc0]
    refine validProg_bind hcur_vp ?_; rw [hcur_st, hcur_res]
    refine validProg_bind h0_vp ?_; rw [h0_st, h0_res, hBr_eq]; exact hBr_vp

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
  have hh := fastMemHdrs hrep
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
          have hwc := writeHdrStep (fs := fs) henv (by dsimp [hdrRebCollision]; decide)
            (henv.fits_const (by decide)) (fun h => by dsimp [hdrRebCollision] at h; omega)
            hseed hrep (hdrOff := hdrRebCollision) (val := 1) (s := s)
          have hlft := rebScanOne_inBounds_insert_lift (cTail := 1) (lkFlag := 1)
            (fsOut := { fs with rebCollision := 1 }) hwp1 hc0 hcur_lt hst_act
            hc_st hc_res hc_vp hcur_st hcur_res hcur_mc hcur_vp h0_st h0_res (le_of_eq h0_mc)
            h0_vp hrl_st hrl_res hrl_mc hrl_vp hro_st hro_res hro_mc hro_vp hcs_st hcs_res hcs_mc
            hcs_vp hfp_st hfp_res hfp_mc hfp_vp hrs_st hrs_res hrs_mc hrs_vp hbl_st
            (by rw [hbl_res]) hbl_mc hbl_vp (by simp) (by omega) hwc.1 hwc.2.1 hwc.2.2
          exact ⟨hlft.1, hlft.2.1, hlft.2.2, rfl, rfl, rfl, rfl, rfl, fun h0 => by cases h0⟩
        | none =>
          have hrm_none : rm fp = none := hlk_eq.symm.trans hlk
          rw [hrm_none] at hbl_res
          dsimp only at hbl_res ⊢
          obtain ⟨hcn_mc, hcn_vp, hcn_step⟩ :=
            rebScanCommitNoneProg_fastStep henv hrIdx hfp_lt hcur_tot hins_lt hv_r hseed hrep
              (s := s)
          have hv_r1 := (hv_r.insert_spec hth hins_lt.le hfp_lt hcur_val).2
          have hlft := rebScanOne_inBounds_insert_lift (cTail := 2445) (lkFlag := 0)
            (fsOut := { fs with
              slices := Function.update fs.slices (fs.rebSliceIdx b)
                (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                  (fs.slices (fs.rebSliceIdx b)) fp cur)
              rebScanCursor := cur + 1
              rebInsCount := fs.rebInsCount + 1 })
            hwp1 hc0 hcur_lt hst_act hc_st hc_res hc_vp hcur_st hcur_res hcur_mc hcur_vp
            h0_st h0_res (le_of_eq h0_mc) h0_vp hrl_st hrl_res hrl_mc hrl_vp hro_st hro_res hro_mc
            hro_vp hcs_st hcs_res hcs_mc hcs_vp hfp_st hfp_res hfp_mc hfp_vp hrs_st hrs_res
            hrs_mc hrs_vp hbl_st (by rw [hbl_res]) hbl_mc hbl_vp (by simp [cur]) (by omega)
            hcn_mc hcn_vp hcn_step
          refine ⟨hlft.1, hlft.2.1, hlft.2.2, rfl, rfl, rfl, rfl, rfl,
            fun _ => ⟨hc0, rfl, le_rfl, Function.update rm fp (some cur), ?_⟩⟩
          change ValidWhpSlice n_max (fs.rebInsCount + 1)
            (Function.update fs.slices (fs.rebSliceIdx b) _ (fs.rebSliceIdx b)) _
          rw [Function.update_self]; exact hv_r1
      · have hncond : ¬(cur < fs.bktCount b ∧
            (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)) := fun h => hst_act h.2
        rw [ite_eq_right hncond]
        have hw := writeHdrStep (fs := fs) henv (by dsimp [hdrRebScanCursor]; decide)
          (henv.fits_of_le_n_max (by omega)) (fun h => by dsimp [hdrRebScanCursor] at h; omega)
          hseed hrep (hdrOff := hdrRebScanCursor) (val := cur + 1) (s := s)
        have hst_in : (Memory.spec 0).clientState s
            (rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)) =
            (Memory.spec 0).clientState s (writeHdrProg ((base, hdrRebScanCursor), cur + 1)) := by
          unfold rebScanInBoundsProg; dsimp only; rw [hwp1]; simp only [pure_bind]
          rw [clientState_bind, hrl_st, hrl_res, clientState_bind, hro_st, hro_res,
            ite_eq_right hst_act]
        have hmc_in : memoryCost
            (rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)) s ≤ 7 := by
          unfold rebScanInBoundsProg; dsimp only; rw [hwp1]
          simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
          rw [hrl_st, hrl_res, hrl_mc, hro_st, hro_res, hro_mc, ite_eq_right hst_act]
          have := hw.1; omega
        have hvp_in : ValidProg w (base + largeSpaceWhp c U V w n_max) s
            (rebScanInBoundsProg (((mkWhpParams c U V w n_max, base), b), cur)) := by
          unfold rebScanInBoundsProg; dsimp only; rw [hwp1]; simp only [pure_bind]
          refine validProg_bind hrl_vp ?_; rw [hrl_st, hrl_res]
          refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_right hst_act]
          exact hw.2.1
        have hlft := rebScanOne_bumpCursor_lift (tailCost := 7) henv hc0 hcur_n hv_r hseed hrep
          hc_st hc_res hc_mc hc_vp hcur_st hcur_res hcur_mc hcur_vp h0_st h0_res (le_of_eq h0_mc)
          h0_vp (ite_eq_left hcur_lt) hst_in hmc_in hvp_in
        have hlft_mc := hlft.1; dsimp only [cp] at hlft_mc ⊢
        exact ⟨by omega, hlft.2.1, hlft.2.2⟩
    · have hncond : ¬(cur < fs.bktCount b ∧
          (fs.locState b cur = 1 ∨ fs.locState b cur = 2 + fs.oldEp)) := fun h => hcur_lt h.1
      rw [ite_eq_right hncond]
      have hw := writeHdrStep (fs := fs) henv (by dsimp [hdrRebScanCursor]; decide)
        (henv.fits_of_le_n_max (by omega)) (fun h => by dsimp [hdrRebScanCursor] at h; omega)
        hseed hrep (hdrOff := hdrRebScanCursor) (val := cur + 1) (s := s)
      have hlft := rebScanOne_bumpCursor_lift (tailCost := 1) henv hc0 hcur_n hv_r hseed hrep
        hc_st hc_res hc_mc hc_vp hcur_st hcur_res hcur_mc hcur_vp h0_st h0_res (le_of_eq h0_mc)
        h0_vp (ite_eq_right hcur_lt) rfl hw.1 hw.2.1
      have hlft_mc := hlft.1; dsimp only [cp] at hlft_mc ⊢
      exact ⟨by omega, hlft.2.1, hlft.2.2⟩

/-- Parameter-free `iterate` wrapper for `rebScanOneProg` (`p = ((((wp, base), b), ()), k)`). -/
@[irreducible] def rebScanLoopGenProg : (((WhpParams × ℕ) × ℕ) × Unit) × ℕ → Memory.Prog Unit
  | ((d, u), k) => iterate rebScanOneProg d k u

/-- `Realizes .exact` certificate for `rebScanLoopGenProg`. -/
theorem realizes_rebScanLoopGen :
    Realizes .exact rebScanLoopGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × Unit) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((d, u), k) s => iterationSafe rebScanOneProg RebScanOnePre w d k u s)
      (fun _ _ => 0) := by
  unfold rebScanLoopGenProg
  have hloop := Realizes.iterate₀
    (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
    (WordEncoding.encode (α := Unit))
    realizes_rebScanOne
    memoryCost_rebScanOneProg_pos
  have heq_safe :
      (fun w (p : (((WhpParams × ℕ) × ℕ) × Unit) × ℕ) s =>
        iterationSafe rebScanOneProg RebScanOnePre w p.1.1 p.2 p.1.2 s) =
      (fun w ((d, u), k) s => iterationSafe rebScanOneProg RebScanOnePre w d k u s) := by
    funext w ⟨⟨d, u⟩, k⟩ s; rfl
  have heq_prog :
      (fun (p : (((WhpParams × ℕ) × ℕ) × Unit) × ℕ) => iterate rebScanOneProg p.1.1 p.2 p.1.2) =
      (fun ((d, u), k) => iterate rebScanOneProg d k u) := by
    funext ⟨⟨d, u⟩, k⟩; rfl
  rw [← heq_safe, ← heq_prog]; exact hloop

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

/-- Iteration cost and `FastStateStep` specification for `rebScanLoopGenProg`. -/
theorem rebScanLoop_spec {c U V w n_max base b : ℕ}
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

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end

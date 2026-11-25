/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.RebRole
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.Bounds
import CslibFrontier.Tactic.Realize

/-!
# Fast Deletion Move-Last Rebuild Slice Relocation

Sub-helper 6.2c relocating `loc_last -> loc_del` in `rebSlice[b]` and handling Stage-2 candidate
rebuild collisions.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveRebGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delMoveRebGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveRebGenProg_fastStep`
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

/-- Sub-helper 6.2c (collision reset): reset `rebSlice`, advance `rebCandSalt`, and zero cursors
(`d = ((cp, base), rIdx)`). -/
@[irreducible] private def delMoveRebCollisionProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), rIdx) => do
    let z0 ← pure 0
    let z1 ← pure 1
    resetBTreeSliceGenProg ((cp, base), rIdx)
    let cand ← readHdrProg (base, hdrRebCandSalt)
    let cand1 ← pure (cand + z1)
    writeHdrProg ((base, hdrRebCandSalt), cand1)
    writeHdrProg ((base, hdrRebScanCursor), z0)
    writeHdrProg ((base, hdrRebInsCount), z0)

private theorem realizes_delMoveRebCollision :
    Realizes .exact delMoveRebCollisionProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), rIdx) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          rIdx < 3 * numBucketsWhp n_max ∧
          fs.rebCandSalt < sMaxWhp c n_max)
      (fun _ _ => 0) := by
  unfold delMoveRebCollisionProg
  have hrs := realizes_resetBTreeSliceGen
  have hrh := realizes_readHdr
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rIdx⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hrIdx, hcs_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hsmax_n := (large_bounds_lt_n_max hth).2.2.2.2.1
    obtain ⟨_, _, hrs_step⟩ := resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
    set s1 := (Memory.spec 0).clientState s
      (resetBTreeSliceGenProg ((mkWhpCoreParams c U V w n_max, base), rIdx))
    obtain ⟨hst_c, hres_c, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s1)
    have hmem_c : s1.mem (base + hdrRebCandSalt) = fs.rebCandSalt :=
      hrs_step.2.2.1.2.2.2.2.2.2.2.2.2.1
    simp only [wp_large_M hth] at *
    first
    | trivial
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (dsimp only [s1] at hst_c hres_c hmem_c
       rw [hres_c, hmem_c]
       exact henv.fits_of_le_n_max (by omega))
  )

private theorem delMoveRebCollisionProg_fastStep {c U V w n_max base rIdx : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrIdx : rIdx < 3 * numBucketsWhp n_max)
    (hcs_lt : fs.rebCandSalt < sMaxWhp c n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveRebCollisionProg ((mkWhpCoreParams c U V w n_max, base), rIdx)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices rIdx (resetBTreeSlice (fs.slices rIdx))
        rebCandSalt := fs.rebCandSalt + 1
        rebScanCursor := 0
        rebInsCount := 0 } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hsmax_n := (large_bounds_lt_n_max hth).2.2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hrs_mc, hrs_vp, hrs_step⟩ :=
    resetBTreeSliceGenProg_fastStep henv hrIdx hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s (resetBTreeSliceGenProg ((cp, base), rIdx))
  obtain ⟨hst_c, hres_c, hmc_c, hvp_c⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
    (by dsimp [hdrRebCandSalt]; omega) (s := s1)
  rw [hrs_step.2.2.1.2.2.2.2.2.2.2.2.2.1] at hres_c
  obtain ⟨hw1_mc, hw1_vp, hw1_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebCandSalt) henv
    (by decide) (henv.fits_of_le_n_max (by omega))
    (by intro h; cases h) hrs_step.2.1 hrs_step.2.2.1
    (val := fs.rebCandSalt + 1) (s := s1)
  set s2 :=
    (Memory.spec 0).clientState s1 (writeHdrProg ((base, hdrRebCandSalt), fs.rebCandSalt + 1))
  obtain ⟨hw2_mc, hw2_vp, hw2_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebScanCursor) henv
    (by decide) (henv.fits_const (by decide))
    (by intro h; cases h) hw1_step.2.1 hw1_step.2.2.1
    (val := 0) (s := s2)
  set s3 := (Memory.spec 0).clientState s2 (writeHdrProg ((base, hdrRebScanCursor), 0))
  obtain ⟨hw3_mc, hw3_vp, hw3_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebInsCount) henv
    (by decide) (henv.fits_const (by decide))
    (by intro h; cases h) hw2_step.2.1 hw2_step.2.2.1
    (val := 0) (s := s3)
  dsimp only
  unfold delMoveRebCollisionProg
  simp only [cp, pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (resetBTreeSliceGenProg ((cp, base), rIdx) >>= fun _ =>
        readHdrProg (base, hdrRebCandSalt) >>= fun cand =>
        writeHdrProg ((base, hdrRebCandSalt), cand + 1) >>= fun _ =>
        writeHdrProg ((base, hdrRebScanCursor), 0) >>= fun _ =>
        writeHdrProg ((base, hdrRebInsCount), 0)) =
      (Memory.spec 0).clientState s3 (writeHdrProg ((base, hdrRebInsCount), 0)) := by
    rw [clientState_bind, clientState_bind, hst_c, hres_c, clientState_bind,
      clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, ((hrs_step.trans hw1_step).trans hw2_step).trans hw3_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, s2, s3, cp] at hrs_mc hst_c hres_c hmc_c hw1_mc hw2_mc hw3_mc ⊢
    rw [hst_c, hres_c, hmc_c]; omega
  · refine validProg_bind hrs_vp ?_
    refine validProg_bind hvp_c ?_; rw [hst_c, hres_c]
    exact validProg_bind hw1_vp (validProg_bind hw2_vp hw3_vp)

/-- Sub-helper 6.2c (insert+inc): insert `(fp_cand_last, loc_del)` into `rIdx` and increment
`rebInsCount`. -/
@[irreducible] private def delMoveRebInsertIncProg :
    ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, base), rIdx), (fp_cand_last, loc_del)) => do
    let z1 ← pure 1
    btreeInsertGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
    let ins ← readHdrProg (base, hdrRebInsCount)
    let ins1 ← pure (ins + z1)
    writeHdrProg ((base, hdrRebInsCount), ins1)

private theorem realizes_delMoveRebInsertInc :
    Realizes .exact delMoveRebInsertIncProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), rIdx), (fp_cand_last, loc_del)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (rm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          rIdx < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_cand_last < 2 ^ fpBitsWhp n_max ∧
          fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max fs.rebInsCount (fs.slices rIdx) rm)
      (fun _ _ => 0) := by
  unfold delMoveRebInsertIncProg
  have hbi := realizes_btreeInsertGen
  have hrh := realizes_readHdr
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, rIdx⟩, ⟨fp_cand_last, loc_del⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hrIdx,
      hld, hfp, hins_lt, hv_r⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hML12 := numBucketsWhp_mul_scale_pow12_le hth
    have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    obtain ⟨_, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp hval_ld (s := s)
    set s_bi := (Memory.spec 0).clientState s
      (btreeInsertGenProg
        ((((mkWhpCoreParams c U V w n_max, base), rIdx), fp_cand_last), loc_del))
    obtain ⟨hst_i, hres_i, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebInsCount)
      (by dsimp [hdrRebInsCount]; omega) (s := s_bi)
    have hmem_i : s_bi.mem (base + hdrRebInsCount) = fs.rebInsCount :=
      hbi_step.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    have hfit_i : Fits w
        ((Memory.spec 0).clientResult s_bi (readHdrProg (base, hdrRebInsCount)) + 1) := by
      rw [hres_i, hmem_i]; exact henv.fits_of_le_n_max (by omega)
    dsimp only [s_bi] at hst_i hfit_i
    simp only [hst_i] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hfit_i
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices rIdx, rm,
        henv, rfl, hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp, hval_ld⟩
  )

private theorem delMoveRebInsertIncProg_fastStep {c U V w n_max base rIdx loc_del fp_cand_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {rm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrIdx : rIdx < 3 * numBucketsWhp n_max)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_cand_last < 2 ^ fpBitsWhp n_max)
    (hins_lt : fs.rebInsCount < 8 * (slabScale n_max) ^ 12)
    (hv_r : ValidWhpSlice n_max fs.rebInsCount (fs.slices rIdx) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveRebInsertIncProg
      (((mkWhpCoreParams c U V w n_max, base), rIdx), (fp_cand_last, loc_del))
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2428 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices rIdx
          (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices rIdx) fp_cand_last loc_del)
        rebInsCount := fs.rebInsCount + 1 } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    btreeInsertGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp hval_ld (s := s)
  set s_bi := (Memory.spec 0).clientState s
    (btreeInsertGenProg ((((cp, base), rIdx), fp_cand_last), loc_del))
  obtain ⟨hst_i, hres_i, hmc_i, hvp_i⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebInsCount)
    (by dsimp [hdrRebInsCount]; omega) (s := s_bi)
  rw [hbi_step.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1] at hres_i
  obtain ⟨hwh_mc, hwh_vp, hwh_step⟩ := writeHdrProg_fastStep (hdrOff := hdrRebInsCount) henv
    (by decide) (henv.fits_of_le_n_max (by omega))
    (by intro h; cases h) hbi_step.2.1 hbi_step.2.2.1
    (val := fs.rebInsCount + 1) (s := s_bi)
  dsimp only
  unfold delMoveRebInsertIncProg
  simp only [cp, pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (btreeInsertGenProg ((((cp, base), rIdx), fp_cand_last), loc_del) >>= fun _ =>
        readHdrProg (base, hdrRebInsCount) >>= fun ins =>
        writeHdrProg ((base, hdrRebInsCount), ins + 1)) =
      (Memory.spec 0).clientState s_bi
        (writeHdrProg ((base, hdrRebInsCount), fs.rebInsCount + 1)) := by
    rw [clientState_bind, clientState_bind]
    dsimp only [s_bi, cp] at hst_i hres_i ⊢
    rw [hst_i, hres_i]
  rw [hs'_eq]
  refine ⟨?_, ?_, hbi_step.trans hwh_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s_bi, cp] at hbi_mc hst_i hres_i hmc_i hwh_mc ⊢
    rw [hst_i, hres_i, hmc_i]; omega
  · refine validProg_bind hbi_vp ?_
    dsimp only [s_bi, cp] at hst_i hres_i hvp_i hwh_vp ⊢
    refine validProg_bind hvp_i ?_; rw [hst_i, hres_i]; exact hwh_vp

/-- Sub-helper 6.2c (active branch): relocate `loc_last → loc_del` in `rebSlice[b]` once
`rebAct = 1` and `st_last ∈ {1, 2 + oldEp}` hold. -/
@[irreducible] private def delMoveRebActiveProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), fp_cand_last) => do
    let z1 ← pure 1
    let rebCur ← readHdrProg (base, hdrRebScanCursor)
    let rIdx ← readRebSliceIdxGenProg ((cp, base), b)
    if loc_last < rebCur then
      btreeUpdateGenProg ((((cp, base), rIdx), fp_cand_last), loc_del)
    else if loc_del < rebCur then do
      let lk ← btreeLookupGenProg (((cp, base), rIdx), fp_cand_last)
      if lk.1 = z1 then
        delMoveRebCollisionProg ((cp, base), rIdx)
      else
        delMoveRebInsertIncProg (((cp, base), rIdx), (fp_cand_last, loc_del))
    else
      pure ()

private theorem realizes_delMoveRebActive :
    Realizes .exact delMoveRebActiveProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), fp_cand_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (rm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_cand_last < 2 ^ fpBitsWhp n_max ∧
          fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
      (fun _ _ => 0) := by
  unfold delMoveRebActiveProg
  have hrh := realizes_readHdr
  have hrs := realizes_readRebSliceIdxGen
  have hbu := realizes_btreeUpdateGen
  have hbl := realizes_btreeLookupGen
  have hrc := realizes_delMoveRebCollision
  have hri := realizes_delMoveRebInsertInc
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, fp_cand_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hb, hrIdx,
      hld, hfp, hcs_lt, hins_lt, hv_r⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    obtain ⟨hst_rc, hres_rc, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hbl_st, _, _, _⟩ := btreeLookupGenProg_spec henv hrIdx hins_lt.le
      (hrep.slice_rep hrIdx) hv_r hfp (s := s)
    simp only [hst_rc, hres_rc, hrs_st, hrs_res, hbl_st, wp_large_M hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices (fs.rebSliceIdx b), rm,
        henv, rfl, hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp, hval_ld⟩
    | exact ⟨c, U, V, w, n_max, fs.rebInsCount, fs.slices (fs.rebSliceIdx b), rm,
        henv, rfl, hrIdx, hins_lt.le, hrep.slice_rep hrIdx, hv_r, hfp⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hrIdx, hcs_lt⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hrIdx, hld, hfp, hins_lt, hv_r⟩
  )

/-- Sub-helper 6.2c: relocate `loc_last → loc_del` in `rebSlice[b]` (`rebQuad`). -/
@[irreducible] def delMoveRebGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), ((rebAct, st_last), fp_cand_last)) => do
    let z1 ← pure 1
    let z2 ← pure 2
    let oldEp ← readOldEpProg base
    let tagOld ← pure (z2 + oldEp)
    if rebAct = z1 ∧ (st_last = z1 ∨ st_last = tagOld) then
      delMoveRebActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_cand_last)
    else
      pure ()

theorem realizes_delMoveRebGen :
    Realizes .exact delMoveRebGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), ((rebAct, _), fp_cand_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_cand_last < 2 ^ fpBitsWhp n_max ∧
          (rebAct = 1 →
            fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
            ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm))
      (fun _ _ => 0) := by
  unfold delMoveRebGenProg
  have hro := realizes_readOldEp
  have hra := realizes_delMoveRebActive
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, ⟨⟨rebAct, st_last⟩, fp_cand_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hce, hb, hrIdx,
      hld, hfp, hreb_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    simp only [hst_o, hres_o] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | (have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
       have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
       change 2 + fs.oldEp < 2 ^ w; omega)
    | (obtain ⟨hcs_lt, hins_lt, rm, hv_r⟩ := hreb_fn (by omega)
       exact ⟨c, U, V, w, n_max, θ, fs, rm, henv, rfl, hseed, hrep, hb, hrIdx,
         hld, hfp, hcs_lt, hins_lt, hv_r⟩)
  )

/-- A prefix `p` that leaves the state unchanged and returns `r` peels off `p >>= k`: the state,
result and validity of `p >>= k` are those of `k r`, and its cost is that of `p` plus `k r`. -/
private theorem bind_of_readOnly {α : Type} {w F : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r : α} (hst : (Memory.spec 0).clientState s p = s)
    (hres : (Memory.spec 0).clientResult s p = r) (hvp : ValidProg w F s p) :
    ∀ (β : Type) (k : α → Memory.Prog β),
    (Memory.spec 0).clientState s (p >>= k) = (Memory.spec 0).clientState s (k r) ∧
    (Memory.spec 0).clientResult s (p >>= k) = (Memory.spec 0).clientResult s (k r) ∧
    memoryCost (p >>= k) s = memoryCost p s + memoryCost (k r) s ∧
    (ValidProg w F s (p >>= k) ↔ ValidProg w F s (k r)) := fun _ k => by
  refine ⟨by rw [clientState_bind, hst, hres], by rw [clientResult_bind, hst, hres],
    by rw [memoryCost_bind', hst, hres], fun h hm => ?_, fun h => validProg_bind hvp ?_⟩
  · have := ((validHistory_bind' w p k s).1 (h hm)).2
    rwa [hst, hres] at this
  · rwa [hst, hres]

theorem delMoveRebGenProg_fastStep
    {c U V w n_max base b loc_del loc_last st_last fp_cand_last : ℕ}
    {rebActiveB : Bool} {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hrIdx : fs.rebSliceIdx b < 3 * numBucketsWhp n_max)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_cand_last < 2 ^ fpBitsWhp n_max)
    (hreb_fn : rebActiveB = true →
      fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs.rebInsCount (fs.slices (fs.rebSliceIdx b)) rm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let rebAct := if rebActiveB then 1 else 0
    let prog := delMoveRebGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)),
        ((rebAct, st_last), fp_cand_last))
    let s' := (Memory.spec 0).clientState s prog
    let rIdx := fs.rebSliceIdx b
    let (slices', (rebCandSalt', (rebScanCursor', rebInsCount'))) :=
      if rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs.oldEp) then
        if loc_last < fs.rebScanCursor then
          (Function.update fs.slices rIdx
            (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices rIdx) fp_cand_last loc_del),
           (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount)))
        else if loc_del < fs.rebScanCursor then
          match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices rIdx) fp_cand_last with
          | some _ =>
            (Function.update fs.slices rIdx (resetBTreeSlice (fs.slices rIdx)),
             (fs.rebCandSalt + 1, (0, 0)))
          | none =>
            (Function.update fs.slices rIdx
              (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
                (fs.slices rIdx) fp_cand_last loc_del),
             (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount + 1)))
        else (fs.slices, (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount)))
      else (fs.slices, (fs.rebCandSalt, (fs.rebScanCursor, fs.rebInsCount)))
    memoryCost prog s ≤ 2696 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := slices'
        rebCandSalt := rebCandSalt'
        rebScanCursor := rebScanCursor'
        rebInsCount := rebInsCount' } s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  have hO := bind_of_readOnly hst_o hres_o hvp_o
  have hcond_iff :
      ((if rebActiveB then 1 else 0) = 1 ∧ (st_last = 1 ∨ st_last = 2 + fs.oldEp)) ↔
      (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs.oldEp)) = true := by
    cases rebActiveB <;> simp
  dsimp only
  unfold delMoveRebGenProg
  simp only [pure_bind]
  rw [(hO _ _).1, (hO _ _).2.2.1, (hO _ _).2.2.2, hmc_o]
  by_cases hcond : (rebActiveB && decide (st_last = 1 ∨ st_last = 2 + fs.oldEp)) = true
  · rw [ite_eq_left hcond, ite_eq_left (hcond_iff.mpr hcond)]
    obtain ⟨hcs_lt, hins_lt, rm, hv_r⟩ := hreb_fn ((Bool.and_eq_true _ _).mp hcond).1
    obtain ⟨hst_rc, hres_rc, hmc_rc, hvp_rc⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebScanCursor)
      (by dsimp [hdrRebScanCursor]; omega) (s := s)
    rw [hrep.2.2.2.2.2.2.2.2.2.2.1] at hres_rc
    obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readRebSliceIdxGenProg_spec henv hb hrep (s := s)
    have hR := bind_of_readOnly hst_rc hres_rc hvp_rc
    have hI := bind_of_readOnly hrs_st hrs_res hrs_vp
    unfold delMoveRebActiveProg
    simp only [pure_bind]
    rw [(hR _ _).1, (hR _ _).2.2.1, (hR _ _).2.2.2, hmc_rc,
      (hI _ _).1, (hI _ _).2.2.1, (hI _ _).2.2.2, hrs_mc]
    by_cases hll_r : loc_last < fs.rebScanCursor
    · simp only [hll_r, ↓reduceIte]
      obtain ⟨hbu_mc, hbu_vp, hbu_step⟩ :=
        btreeUpdateGenProg_fastStep henv hrIdx hins_lt.le hseed hrep hv_r hfp hval_ld (s := s)
      exact ⟨by omega, hbu_vp, hbu_step⟩
    simp only [hll_r, ↓reduceIte]
    by_cases hld_r : loc_del < fs.rebScanCursor
    · simp only [hld_r, ↓reduceIte]
      obtain ⟨hbl_st, hbl_res, hbl_mc, hbl_vp⟩ :=
        btreeLookupGenProg_spec henv hrIdx hins_lt.le (hrep.slice_rep hrIdx) hv_r hfp (s := s)
      rw [← hv_r.lookup_eq hth hins_lt.le hfp] at hbl_res
      have hL := bind_of_readOnly hbl_st hbl_res hbl_vp
      rw [(hL _ _).1, (hL _ _).2.2.1, (hL _ _).2.2.2]
      cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.rebSliceIdx b)) fp_cand_last with
      | some v_hit =>
        obtain ⟨hrc_mc, hrc_vp, hrc_step⟩ :=
          delMoveRebCollisionProg_fastStep henv hrIdx hcs_lt hseed hrep (s := s)
        simp only [↓reduceIte]
        exact ⟨by omega, hrc_vp, hrc_step⟩
      | none =>
        obtain ⟨hri_mc, hri_vp, hri_step⟩ :=
          delMoveRebInsertIncProg_fastStep henv hrIdx hld hfp hins_lt hv_r hseed hrep (s := s)
        simp only [Nat.zero_ne_one, ↓reduceIte]
        exact ⟨by omega, hri_vp, hri_step⟩
    simp only [hld_r, ↓reduceIte]
    exact ⟨by rw [memoryCost_pure]; omega, validProg_pure _, FastStateStep.refl hseed hrep⟩
  rw [ite_eq_right hcond, ite_eq_right fun h => hcond (hcond_iff.mp h)]
  exact ⟨by rw [memoryCost_pure]; omega, validProg_pure _, FastStateStep.refl hseed hrep⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

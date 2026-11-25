/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.Bounds
import CslibFrontier.Tactic.Realize

/-!
# Fast Deletion Move-Last Live & Overmars Slice Relocation

Sub-helper 6.2b relocating `loc_last -> loc_del` in `liveSlice[b]` and `overmarsSlice[b]` with
exact Overmars collision handling.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveLiveOmGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delMoveLiveOmGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveLiveOmGenProg_fastStep`
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

/-- `readBktFieldGenProg_spec` as a `CostBoundedStep`. -/
private theorem CostBoundedStep.readBkt {c U V w n_max base b i : ℕ} {fs : FastState}
    {s : Memory.State} (henv : WhpLargeEnv c U V w n_max w base) (hb : b < numBucketsWhp n_max)
    (hi : i < 10) (hrep : FastMemRep base c U V w n_max fs s.mem) :
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), i)) s
      (getBktField fs b i) 2 :=
  .of (readBktFieldGenProg_spec henv hb hi hrep)

/-- Sub-helper 6.2b (Overmars insert+inc): insert `(fp_live_last, loc_del)` into `omIdx` and
increment `overmarsInsCount b`. -/
@[irreducible] private def delMoveOmInsertIncProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, base), (b, omIdx)), (fp_live_last, loc_del)) => do
    let z1 ← pure 1
    btreeInsertGenProg ((((cp, base), omIdx), fp_live_last), loc_del)
    let omIns ← readBktFieldGenProg (((cp, base), b), 7)
    let omIns1 ← pure (omIns + z1)
    writeBktFieldGenProg ((((cp, base), b), 7), omIns1)

private theorem realizes_delMoveOmInsertInc :
    Realizes .exact delMoveOmInsertIncProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), (b, omIdx)), (fp_live_last, loc_del)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (om : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          omIdx = fs.overmarsSliceIdx b ∧
          omIdx < 3 * numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices omIdx) om)
      (fun _ _ => 0) := by
  unfold delMoveOmInsertIncProg
  have hbi := realizes_btreeInsertGen
  have hrb := realizes_readBktFieldGen
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, omIdx⟩⟩, ⟨fp_live_last, loc_del⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, rfl, homIdx,
      hld, hfp, hins_lt, hv_om⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hML12 := numBucketsWhp_mul_scale_pow12_le hth
    have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    obtain ⟨_, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om hfp hval_ld (s := s)
    set s_bi := (Memory.spec 0).clientState s
      (btreeInsertGenProg
        ((((mkWhpCoreParams c U V w n_max, base), fs.overmarsSliceIdx b), fp_live_last), loc_del))
    obtain ⟨hst_7, hres_7, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hbi_step.2.2.1 (s := s_bi)
    simp only [getBktField] at hres_7
    have hfit7 : Fits w ((Memory.spec 0).clientResult s_bi
        (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 7)) + 1) := by
      rw [hres_7]; exact henv.fits_of_le_n_max (by omega)
    dsimp only [s_bi] at hst_7 hres_7 hfit7
    simp only [hst_7, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact hfit7
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), om,
        henv, rfl, homIdx, hins_lt.le, hrep.slice_rep homIdx, hv_om, hfp, hval_ld⟩
  )

private theorem delMoveOmInsertIncProg_fastStep {c U V w n_max base b loc_del fp_live_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {om : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_live_last < 2 ^ fpBitsWhp n_max)
    (hins_lt : fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12)
    (hv_om : ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let omIdx := fs.overmarsSliceIdx b
    let prog := delMoveOmInsertIncProg
      (((mkWhpCoreParams c U V w n_max, base), (b, omIdx)), (fp_live_last, loc_del))
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2432 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        slices := Function.update fs.slices omIdx
          (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices omIdx) fp_live_last loc_del)
        overmarsInsCount := Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1) }
      s s' := by
  have hth := henv.2.2.2.1
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have h8L12 : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by have := (large_bounds_lt_n_max hth).1; omega)).trans hML12
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.overmarsSliceIdx; omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om hfp hval_ld (s := s)
  set s_bi := (Memory.spec 0).clientState s
    (btreeInsertGenProg ((((cp, base), fs.overmarsSliceIdx b), fp_live_last), loc_del))
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ :=
    writeBktFieldGenProg_fastStep henv hb (by decide : 7 < 10) (by omega)
      hbi_step.2.1 hbi_step.2.2.1 (val := fs.overmarsInsCount b + 1) (s := s_bi)
  dsimp only
  unfold delMoveOmInsertIncProg
  simp only [cp, pure_bind]
  exact CostBoundedStep.elim (.bind ⟨rfl, rfl, hbi_mc, hbi_vp⟩ <|
    .bind (CostBoundedStep.readBkt henv hb (by decide : 7 < 10) hbi_step.2.2.1)
      ⟨rfl, rfl, hwb_mc.le, hwb_vp⟩)
    (by omega) (hbi_step.trans hwb_step)

/-- Active Overmars helper for `delMoveOmSubProg` once `overmarsActive b = 1`. -/
@[irreducible] private def delMoveOmActiveProg :
    ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((cp, base), b), ((loc_del, loc_last), fp_live_last)) => do
    let omCur ← readBktFieldGenProg (((cp, base), b), 6)
    let orl ← readBktFieldGenProg (((cp, base), b), 4)
    let omIdx ← pure (3 * b + orl)
    if loc_last < omCur then
      btreeUpdateGenProg ((((cp, base), omIdx), fp_live_last), loc_del)
    else if loc_del < omCur then
      delMoveOmInsertIncProg (((cp, base), (b, omIdx)), (fp_live_last, loc_del))
    else
      pure ()

private theorem realizes_delMoveOmActive :
    Realizes .exact delMoveOmActiveProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), ((loc_del, _), fp_live_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (om : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
      (fun _ _ => 0) := by
  unfold delMoveOmActiveProg
  have hrb := realizes_readBktFieldGen
  have hbu := realizes_btreeUpdateGen
  have hmi := realizes_delMoveOmInsertInc
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, ⟨⟨loc_del, loc_last⟩, fp_live_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, hor, hld, hfp,
      hins_lt, hv_om⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    obtain ⟨hst_6, hres_6, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 6 < 10)
      hrep (s := s)
    obtain ⟨hst_4, hres_4, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 4 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_6 hres_4
    simp only [hst_6, hres_6, hst_4, hres_4, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), om,
        henv, rfl, homIdx, hins_lt.le, hrep.slice_rep homIdx, hv_om, hfp, hval_ld⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, rfl, homIdx,
        hld, hfp, hins_lt, hv_om⟩
  )

/-- Sub-helper 6.2b (Overmars part): relocate `loc_last → loc_del` in `overmarsSlice[b]` when
`inLiveTree` already holds (`d = (((cp, base), b), ((loc_del, loc_last), fp_live_last))`). -/
@[irreducible] private def delMoveOmSubProg :
    ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((cp, base), b), ((loc_del, loc_last), fp_live_last)) => do
    let z1 ← pure 1
    let omAct ← readBktFieldGenProg (((cp, base), b), 5)
    if omAct = z1 then
      delMoveOmActiveProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))
    else
      pure ()

private theorem realizes_delMoveOmSub :
    Realizes .exact delMoveOmSubProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), ((loc_del, _), fp_live_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om))
      (fun _ _ => 0) := by
  unfold delMoveOmSubProg
  have hrb := realizes_readBktFieldGen
  have hma := realizes_delMoveOmActive
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, ⟨⟨loc_del, loc_last⟩, fp_live_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hor, hld, hfp, hom_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hst_5, hres_5, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 5 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_5
    simp only [hst_5, hres_5, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | (obtain ⟨hins_lt, om, hv_om⟩ := hom_fn (by assumption)
       exact ⟨c, U, V, w, n_max, θ, fs, om, henv, rfl, hseed, hrep, hb, hor, hld, hfp,
         hins_lt, hv_om⟩)
  )

private theorem delMoveOmSubProg_fastStep {c U V w n_max base b loc_del loc_last fp_live_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_live_last < 2 ^ fpBitsWhp n_max)
    (hom_fn : fs.overmarsActive b = 1 →
      fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveOmSubProg
      (((mkWhpCoreParams c U V w n_max, base), b), ((loc_del, loc_last), fp_live_last))
    let s' := (Memory.spec 0).clientState s prog
    let omIdx := fs.overmarsSliceIdx b
    let omPair :=
      if fs.overmarsActive b = 1 then
        if loc_last < fs.overmarsCursor b then
          (Function.update fs.slices omIdx
            (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices omIdx) fp_live_last loc_del),
           fs.overmarsInsCount)
        else if loc_del < fs.overmarsCursor b then
          (Function.update fs.slices omIdx
            (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices omIdx) fp_live_last loc_del),
           Function.update fs.overmarsInsCount b (fs.overmarsInsCount b + 1))
        else (fs.slices, fs.overmarsInsCount)
      else (fs.slices, fs.overmarsInsCount)
    memoryCost prog s ≤ 2438 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := omPair.1, overmarsInsCount := omPair.2 } s s' := by
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  set cp := mkWhpCoreParams c U V w n_max
  dsimp only
  unfold delMoveOmSubProg
  simp only [cp, pure_bind]
  have h5 := CostBoundedStep.readBkt henv hb (by decide : 5 < 10) hrep (s := s)
  by_cases ha1 : fs.overmarsActive b = 1
  · rw [ite_eq_left ha1]
    obtain ⟨hins_lt, om, hv_om⟩ := hom_fn ha1
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    -- The active branch reads fields 5, 6 and 4, then runs the cursor case split.
    have hpre : ∀ {s₂ C}, CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
        (if loc_last < fs.overmarsCursor b then
          btreeUpdateGenProg ((((cp, base), fs.overmarsSliceIdx b), fp_live_last), loc_del)
        else if loc_del < fs.overmarsCursor b then
          delMoveOmInsertIncProg (((cp, base), (b, fs.overmarsSliceIdx b)), (fp_live_last, loc_del))
        else pure ()) s₂ () C →
        CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
          (readBktFieldGenProg (((cp, base), b), 5) >>= fun omAct =>
            if omAct = 1 then
              delMoveOmActiveProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))
            else pure ()) s₂ () (2 + (2 + (2 + C))) := by
      intro s₂ C h
      refine .bind h5 ?_
      simp only [getBktField, ite_eq_left ha1]
      unfold delMoveOmActiveProg; simp only [pure_bind]
      exact .bind (CostBoundedStep.readBkt henv hb (by decide : 6 < 10) hrep) <|
        .bind (CostBoundedStep.readBkt henv hb (by decide : 4 < 10) hrep) h
    by_cases hll_c : loc_last < fs.overmarsCursor b
    · rw [ite_eq_left hll_c]
      obtain ⟨hbu_mc, hbu_vp, hbu_step⟩ :=
        btreeUpdateGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om hfp hval_ld (s := s)
      exact CostBoundedStep.elim
        (hpre (by rw [ite_eq_left hll_c]; exact ⟨rfl, rfl, hbu_mc, hbu_vp⟩)) (by omega) hbu_step
    · rw [ite_eq_right hll_c]
      by_cases hld_c : loc_del < fs.overmarsCursor b
      · rw [ite_eq_left hld_c]
        obtain ⟨hmi_mc, hmi_vp, hmi_step⟩ :=
          delMoveOmInsertIncProg_fastStep henv hb hor hld hfp hins_lt hv_om hseed hrep (s := s)
        exact CostBoundedStep.elim
          (hpre (by rw [ite_eq_right hll_c, ite_eq_left hld_c]; exact ⟨rfl, rfl, hmi_mc, hmi_vp⟩))
          (by omega) hmi_step
      · rw [ite_eq_right hld_c]
        exact CostBoundedStep.elim
          (hpre (by rw [ite_eq_right hll_c, ite_eq_right hld_c]; exact .pure _ _))
          (by omega) (FastStateStep.refl hseed hrep)
  · rw [ite_eq_right ha1]
    exact CostBoundedStep.elim
      (.bind h5 (by simp only [getBktField, ite_eq_right ha1]; exact .pure _ _))
      (by omega) (FastStateStep.refl hseed hrep)

/-- Active helper for `delMoveLiveOmGenProg` once `inLiveTree` holds. -/
@[irreducible] private def delMoveLiveOmActiveProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), fp_live_last) => do
    let lr ← readBktFieldGenProg (((cp, base), b), 2)
    let lIdx ← pure (3 * b + lr)
    btreeUpdateGenProg ((((cp, base), lIdx), fp_live_last), loc_del)
    delMoveOmSubProg (((cp, base), b), ((loc_del, loc_last), fp_live_last))

private theorem realizes_delMoveLiveOmActive :
    Realizes .exact delMoveLiveOmActiveProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), fp_live_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.overmarsRole b < 3 ∧
          fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om))
      (fun _ _ => 0) := by
  unfold delMoveLiveOmActiveProg
  have hrb := realizes_readBktFieldGen
  have hbu := realizes_btreeUpdateGen
  have hmo := realizes_delMoveOmSub
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, fp_live_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hb, hlr, hor, hne_lo,
      hld, hfp, hlic, hv_l, hom_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hval_ld := loc_lt_two_pow_valLaneBits hld
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    obtain ⟨hst_2, hres_2, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 2 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_2
    simp only [hst_2, hres_2, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), lm,
        henv, rfl, hlIdx, hlic, hrep.slice_rep hlIdx, hv_l, hfp, hval_ld⟩
    | (obtain ⟨_, _, hbu_step⟩ :=
         btreeUpdateGenProg_fastStep henv hlIdx hlic hseed hrep hv_l hfp hval_ld (s := s)
       refine ⟨c, U, V, w, n_max, θ, _, henv, rfl, hbu_step.2.1, hbu_step.2.2.1, hb, hor,
         hld, hfp, fun ha1 => ?_⟩
       obtain ⟨hins_lt, om, hv_om⟩ := hom_fn ha1
       refine ⟨hins_lt, om, ?_⟩
       change ValidWhpSlice n_max (fs.overmarsInsCount b)
         (Function.update fs.slices (fs.liveSliceIdx b)
           (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
             (fs.slices (fs.liveSliceIdx b)) fp_live_last loc_del)
           (fs.overmarsSliceIdx b)) om
       rwa [Function.update_of_ne hne_lo.symm])
  )

/-- Sub-helper 6.2b: relocate `loc_last → loc_del` in `liveSlice[b]` and `overmarsSlice[b]`
(`fastDeleteMoveSlices`). -/
@[irreducible] def delMoveLiveOmGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), (st_last, fp_live_last)) => do
    let z1 ← pure 1
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    let inL ← inLiveTreeProg ((stg, oldEp), (doneB, st_last))
    if inL = z1 then
      delMoveLiveOmActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_live_last)
    else
      pure ()

theorem realizes_delMoveLiveOmGen :
    Realizes .exact delMoveLiveOmGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, _)), (_, fp_live_last)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.overmarsRole b < 3 ∧
          fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          fp_live_last < 2 ^ fpBitsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om))
      (fun _ _ => 0) := by
  unfold delMoveLiveOmGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hil := realizes_inLiveTree
  have hma := realizes_delMoveLiveOmActive
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, ⟨st_last, fp_live_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hce, hb, hlr, hor, hne_lo,
      hld, hfp, hlic, hv_l, hom_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    obtain ⟨hst_s, hres_s, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    obtain ⟨hst_o, hres_o, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    obtain ⟨hst_8, hres_8, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 8 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_8
    obtain ⟨hst_il, _, _, _⟩ := inLiveTreeProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (rebStage := s.mem (base + hdrRebStage))
      (oldEp := fs.oldEp) (rebDoneB := fs.rebDoneFlag b) (st := st_last) (s := s)
    simp only [hst_s, hres_s, hst_o, hres_o, hst_8, hres_8, hst_il, wp_large_M hth] at *
    first
    | decide
    | exact h2w
    | exact hold
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hb, hlr, hor, hne_lo,
        hld, hfp, hlic, hv_l, hom_fn⟩
  )

theorem delMoveLiveOmGenProg_fastStep
    {c U V w n_max base b loc_del loc_last st_last fp_live_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hlr : fs.liveRole b < 3) (hor : fs.overmarsRole b < 3)
    (hne_lo : fs.liveSliceIdx b ≠ fs.overmarsSliceIdx b)
    (hld : loc_del < totalLocalCoordsWhp n_max)
    (hfp : fp_live_last < 2 ^ fpBitsWhp n_max)
    (hlic : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_l : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm)
    (hom_fn : fs.overmarsActive b = 1 →
      fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hst_eq : st_last = fs.locState b loc_last)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveLiveOmGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)), (st_last, fp_live_last))
    let s' := (Memory.spec 0).clientState s prog
    let omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp_live_last fs
    memoryCost prog s ≤ 2718 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with slices := omPair.1, overmarsInsCount := omPair.2 } s s' := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hval_ld := loc_lt_two_pow_valLaneBits hld
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hst_s, hres_s, hmc_s, hvp_s⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (by dsimp [hdrRebStage]; omega) (s := s)
  rw [hrep.2.2.2.2.2.1] at hres_s
  obtain ⟨hst_o, hres_o, hmc_o, hvp_o⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  obtain ⟨hst_il, hres_il, hmc_il, hvp_il⟩ := inLiveTreeProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (rebStage := fs.rebStage) (oldEp := fs.oldEp)
    (rebDoneB := fs.rebDoneFlag b) (st := st_last) (s := s)
  dsimp only
  unfold delMoveLiveOmGenProg fastDeleteMoveSlices
  simp only [cp, pure_bind, ← hst_eq]
  by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_last = true
  · rw [ite_eq_left hin] at hres_il ⊢
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    obtain ⟨hbu_mc, hbu_vp, hbu_step⟩ :=
      btreeUpdateGenProg_fastStep henv hlIdx hlic hseed hrep hv_l hfp hval_ld (s := s)
    set s_bu := (Memory.spec 0).clientState s
      (btreeUpdateGenProg ((((cp, base), fs.liveSliceIdx b), fp_live_last), loc_del))
    set sl_live' := Function.update fs.slices (fs.liveSliceIdx b)
      (btreeUpdate (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) fp_live_last loc_del)
    set fs_bu : FastState := { fs with slices := sl_live' }
    have hom_fn' : fs_bu.overmarsActive b = 1 →
        fs_bu.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
        ∃ om, ValidWhpSlice n_max (fs_bu.overmarsInsCount b)
          (fs_bu.slices (fs_bu.overmarsSliceIdx b)) om := by
      intro ha1
      obtain ⟨hins_lt, om, hv_om⟩ := hom_fn ha1
      refine ⟨hins_lt, om, ?_⟩
      dsimp only [fs_bu, sl_live']
      have hne' : fs_bu.overmarsSliceIdx b ≠ fs.liveSliceIdx b := hne_lo.symm
      rwa [Function.update_of_ne hne']
    obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
      delMoveOmSubProg_fastStep (fs := fs_bu) henv hb hor hld hfp hom_fn'
        hbu_step.2.1 hbu_step.2.2.1 (loc_last := loc_last) (s := s_bu)
    have hact : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
        (delMoveLiveOmActiveProg ((((cp, base), b), (loc_del, loc_last)), fp_live_last))
        ((Memory.spec 0).clientState s_bu
          (delMoveOmSubProg (((cp, base), b), ((loc_del, loc_last), fp_live_last)))) () 2714 := by
      unfold delMoveLiveOmActiveProg; simp only [pure_bind]
      exact .mono (.bind (CostBoundedStep.readBkt henv hb (by decide : 2 < 10) hrep) <|
        .bind ⟨rfl, rfl, hbu_mc, hbu_vp⟩ ⟨rfl, rfl, hom_mc, hom_vp⟩) (by omega)
    simp only [hin, and_true]
    exact CostBoundedStep.elim (.bind ⟨hst_s, hres_s, hmc_s.le, hvp_s⟩ <|
      .bind ⟨hst_o, hres_o, hmc_o.le, hvp_o⟩ <|
      .bind (CostBoundedStep.readBkt henv hb (by decide : 8 < 10) hrep) <|
      .bind ⟨hst_il, hres_il, hmc_il.le, hvp_il⟩ hact) (by omega) (hbu_step.trans hom_step)
  · rw [ite_eq_right hin] at hres_il ⊢
    have hfls : ¬(fs.overmarsActive b = 1 ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_last = true) :=
      fun ⟨_, h⟩ => hin h
    rw [ite_eq_right hfls]
    exact CostBoundedStep.elim (.bind ⟨hst_s, hres_s, hmc_s.le, hvp_s⟩ <|
      .bind ⟨hst_o, hres_o, hmc_o.le, hvp_o⟩ <|
      .bind (CostBoundedStep.readBkt henv hb (by decide : 8 < 10) hrep) <|
      .bind ⟨hst_il, hres_il, hmc_il.le, hvp_il⟩ (.pure _ _)) (by omega)
      (FastStateStep.refl hseed hrep)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

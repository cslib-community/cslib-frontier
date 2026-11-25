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
# Stage 4 of `epochTick`

Implements and verifies `epochTickStage4GenProg`, which clears up to `8` nodes/items per tick
from the inactive buffer trie and transitions `rebStage` to `5` once `nodeAlloc ≤ 8`.
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

/-- Execute Stage 4 of `epochTick` (`d = (cp, base)`). -/
@[irreducible] def epochTickStage4GenProg :
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

/-- `Realizes .exact` certificate for `epochTickStage4GenProg`. -/
theorem realizes_epochTickStage4Gen :
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
    have hh := fastMemHdrs hrep
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
    | exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, henv, rfl, hold_or,
        hrep.buf_rep hold_or, hclr⟩
  )

/-- `FastStateStep` specification for `epochTickStage4GenProg`. -/
theorem epochTickStage4GenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hs4 : fs.rebStage = 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := epochTickStage4GenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 124 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (epochTickStage4 fs) s s' := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hc.curEp_or with h | h <;> simp [FastState.oldEp, h]
  have hbo := hc.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
  obtain ⟨_, hclr, _⟩ := hbo
  have hr := stageCursorReads_spec henv hc.curEp_or hold_or hrep (s := s)
  obtain ⟨hcl_mc, hcl_vp, hcl_step⟩ :=
    bufClearStepsGenProg_fastStep henv hold_or hclr hseed hrep (k := 8) (s := s)
  set s1 := (Memory.spec 0).clientState s
    (bufClearStepsGenProg (((cp, base), fs.oldEp), 8))
  set tr' := bufClearSteps 8 (fs.buf fs.oldEp)
  set fs1 : FastState := { fs with buf := Function.update fs.buf fs.oldEp tr' }
  set nextStg : ℕ := if (fs.buf fs.oldEp).nodeAlloc ≤ 8 then 5 else 4
  have hnext_fit : Fits w nextStg := by
    by_cases h8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
    · simp only [nextStg, ite_eq_left h8]; exact henv.fits_const (by decide)
    · simp only [nextStg, ite_eq_right h8]; exact henv.fits_const (by decide)
  obtain ⟨hw_mc, hw_vp, hw_step⟩ := writeHdrStep (fs := fs1) henv
    (by dsimp [hdrRebStage]; decide) hnext_fit
    (fun h6 => by dsimp [hdrRebStage] at h6; omega) hcl_step.2.1 hcl_step.2.2.1
    (hdrOff := hdrRebStage) (val := nextStg) (s := s1)
  have hfs_eq : updateFastHdr fs1 hdrRebStage nextStg = epochTickStage4 fs := by
    dsimp only [epochTickStage4, updateFastHdr, hdrRebStage, fs1, tr', nextStg]
    by_cases h8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8 <;> simp [h8]
  have hbr_eq :
      (if (fs.buf fs.oldEp).nodeAlloc ≤ 8 then writeHdrProg ((base, hdrRebStage), 5)
       else writeHdrProg ((base, hdrRebStage), 4)) =
      writeHdrProg ((base, hdrRebStage), nextStg) := by
    by_cases h8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8 <;> simp [nextStg, h8]
  dsimp only
  unfold epochTickStage4GenProg; simp only [pure_bind]
  rw [← hfs_eq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hr.ro_st, hr.ro_res, hr.ra_st, hr.ra_res]; dsimp only
    rw [hbr_eq]
    have hro_mc := hr.ro_mc
    have hra_mc := hr.ra_mc
    dsimp only [s1, cp, nextStg] at hcl_mc hw_mc hro_mc hra_mc ⊢; omega
  · refine validProg_bind hr.ro_vp ?_; rw [hr.ro_st, hr.ro_res]
    refine validProg_bind hr.ra_vp ?_; rw [hr.ra_st, hr.ra_res]; dsimp only
    rw [hbr_eq]
    exact validProg_bind hcl_vp hw_vp
  · rw [clientState_bind, hr.ro_st, hr.ro_res, clientState_bind, hr.ra_st, hr.ra_res]
    dsimp only; rw [hbr_eq, clientState_bind]
    exact hcl_step.trans hw_step

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end

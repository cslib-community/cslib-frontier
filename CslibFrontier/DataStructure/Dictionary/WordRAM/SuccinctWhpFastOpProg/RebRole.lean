/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Bucket Role & Rebuild Slice Index Readers

Parameter-free `Memory.Prog` readers recovering `(fs.rebRole b, fs.overmarsRole b)` and
`fs.rebSliceIdx b` from bucket metadata without mutating memory.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readRebAndOmRoleGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readRebSliceIdxGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_readRebAndOmRoleGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readRebAndOmRoleGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_readRebSliceIdxGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readRebSliceIdxGenProg_spec`
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

/-- Read `(fs.rebRole b, fs.overmarsRole b)` from bucket `b` metadata fields `2` and `4`
(`d = ((cp, base), b)`). -/
@[irreducible] def readRebAndOmRoleGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z3 ← pure 3
    let lr ← readBktFieldGenProg (((cp, base), b), 2)
    let orl ← readBktFieldGenProg (((cp, base), b), 4)
    let rRole ←
      if lr ≤ z3 then do
        let rem ← pure (z3 - lr)
        if orl ≤ rem then pure (rem - orl) else pure z0
      else
        pure z0
    pure (rRole, orl)

theorem realizes_readRebAndOmRoleGen :
    Realizes .exact readRebAndOmRoleGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold readRebAndOmRoleGenProg
  have hrb := realizes_readBktFieldGen
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
    | omega
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

theorem readRebAndOmRoleGenProg_spec {c U V w n_max base b : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readRebAndOmRoleGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if fs.liveRole b ≤ 3 ∧ fs.overmarsRole b ≤ 3 - fs.liveRole b
       then fs.rebRole b else 0, fs.overmarsRole b) ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨h2_st, h2_res, h2_mc, h2_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 2 < 10) hrep (s := s)
  obtain ⟨h4_st, h4_res, h4_mc, h4_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
  simp only [getBktField] at h2_res h4_res
  unfold readRebAndOmRoleGenProg FastState.rebRole
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, h2_st, h2_res, clientState_bind, h4_st, h4_res]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte]; split_ifs <;> rfl
    · simp only [hlr3, ↓reduceIte]; rfl
  · rw [clientResult_bind, h2_st, h2_res, clientResult_bind, h4_st, h4_res]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte, true_and]
      by_cases hor3 : fs.overmarsRole b ≤ 3 - fs.liveRole b <;>
        simp only [hor3, ↓reduceIte, clientResult_pure_whp]
    · simp only [hlr3, ↓reduceIte, false_and, clientResult_pure_whp]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [h2_st, h2_res, h2_mc, h4_st, h4_res, h4_mc]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte]
      by_cases hor3 : fs.overmarsRole b ≤ 3 - fs.liveRole b <;>
        simp [hor3]
    · simp [hlr3]
  · refine validProg_bind h2_vp ?_; rw [h2_st, h2_res]
    refine validProg_bind h4_vp ?_; rw [h4_st, h4_res]
    by_cases hlr3 : fs.liveRole b ≤ 3
    · simp only [hlr3, ↓reduceIte]
      by_cases hor3 : fs.overmarsRole b ≤ 3 - fs.liveRole b <;>
        (simp only [hor3, ↓reduceIte]; exact validProg_pure _)
    · simp only [hlr3, ↓reduceIte]; exact validProg_pure _

private theorem readRebAndOmRoleGenProg_fst_le (cp : WhpCoreParams) (base b : ℕ)
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (readRebAndOmRoleGenProg ((cp, base), b))).1 ≤ 3 := by
  unfold readRebAndOmRoleGenProg
  simp only [pure_bind, clientResult_bind]
  split_ifs <;> simp only [clientResult_pure_whp] <;> omega

/-- Read `fs.rebSliceIdx b = 3 * b + (3 - fs.liveRole b - fs.overmarsRole b)`
(`d = ((cp, base), b)`). -/
@[irreducible] def readRebSliceIdxGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), b) => do
    let ro ← readRebAndOmRoleGenProg ((cp, base), b)
    pure (3 * b + ro.1)

theorem realizes_readRebSliceIdxGen :
    Realizes .exact readRebSliceIdxGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold readRebSliceIdxGenProg
  have hro := realizes_readRebAndOmRoleGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hfst := readRebAndOmRoleGenProg_fst_le (mkWhpCoreParams c U V w n_max) base b s
    simp only [wp_large_M hth] at *
    first
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
  )

theorem readRebSliceIdxGenProg_spec {c U V w n_max base b : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readRebSliceIdxGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.rebSliceIdx b ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ :=
    readRebAndOmRoleGenProg_spec henv hb hrep (s := s)
  unfold readRebSliceIdxGenProg FastState.rebSliceIdx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hro_st]; rfl
  · rw [clientResult_bind, hro_st, hro_res, clientResult_pure_whp]
    dsimp only [FastState.rebRole]
    split_ifs <;> omega
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hro_st, hro_mc]; simp
  · refine validProg_bind hro_vp ?_; rw [hro_st]; exact validProg_pure _

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

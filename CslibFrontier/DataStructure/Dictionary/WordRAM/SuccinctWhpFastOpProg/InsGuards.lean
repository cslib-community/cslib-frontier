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
# Fast Insertion Read-Only Pre-Check Guards

Read-only `Memory.Prog` subroutines evaluating Guard 1 (bucket capacity & pool free stack), Guard 2
(`rKey` collisions in `buf curEp` / `buf oldEp`), live-slice fingerprint collision status, and
Guard 3 (`buf curEp` collision capacity).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCheckCapPoolGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCheckRKeyGuardsGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insReadFpLiveGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCheckFpCapOptGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCheckCapPoolGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCheckRKeyGuardsGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insReadFpLiveGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCheckFpCapOptGenProg_spec`
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

/-- Guard 1 (`insCheckCapPoolGenProg`): check `totalLocalCoordsWhp ≤ X ∨ (cf ≤ X ∧ poolFreeTop = 0)`
without mutating memory, returning `(0, 0)` if rejected or `(1, X)` if accepted. -/
@[irreducible] def insCheckCapPoolGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let X ← readBktFieldGenProg (((cp, base), b), z0)
    let top ← readHdrProg (base, hdrPoolFreeTop)
    let tl ← pure (wpTotalLoc cp)
    let cf ← pure (wpCapFront cp)
    if tl ≤ X ∨ (cf ≤ X ∧ top = z0) then
      pure (z0, z0)
    else
      pure (z1, X)

theorem realizes_insCheckCapPoolGen :
    Realizes .exact insCheckCapPoolGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold insCheckCapPoolGenProg
  have hrb := realizes_readBktFieldGen
  have hrh := realizes_readHdr
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
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

theorem insCheckCapPoolGenProg_spec {c U V w n_max base b : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insCheckCapPoolGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let X := fs.bktCount b
    let cf := capFrontWhp n_max
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0) then (0, 0) else (1, X)) ∧
    memoryCost prog s ≤ 3 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hc0_st, hc0_res, hc0_mc, hc0_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
  simp only [getBktField] at hc0_res
  obtain ⟨ht_st, ht_res, ht_mc, ht_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
    (by dsimp [hdrPoolFreeTop]; omega) (s := s)
  rw [hrep.2.2.1] at ht_res
  dsimp only
  unfold insCheckCapPoolGenProg; dsimp only
  simp only [wp_large_totalLoc hth, wp_large_capFront hth, pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hc0_st, hc0_res, clientState_bind, ht_st, ht_res]
    split_ifs <;> rfl
  · rw [clientResult_bind, hc0_st, hc0_res, clientResult_bind, ht_st, ht_res]
    split_ifs <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hc0_st, hc0_res, hc0_mc, ht_st, ht_res, ht_mc]
    split_ifs <;> (simp only [memoryCost_pure]; omega)
  · refine validProg_bind hc0_vp ?_; rw [hc0_st, hc0_res]
    refine validProg_bind ht_vp ?_; rw [ht_st, ht_res]
    split_ifs <;> exact validProg_pure _

/-- Return `1` iff `(bufLookup (fs.buf ep) rKey).isSome`, else `0` (`d = (((cp, base), ep), rKey)`).
-/
@[irreducible] private def insBufIsSomeGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | d => do
    let lk ← bufLookupGenProg d
    pure lk.1

private theorem realizes_insBufIsSomeGen :
    Realizes .exact insBufIsSomeGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BufReadGenPre
      (fun _ _ => 0) := by
  unfold insBufIsSomeGenProg
  have hbl := realizes_bufLookupGen
  realize
  exact h

private theorem insBufIsSomeGenProg_spec {c U V w n_max base ep rKey : ℕ}
    {fs : FastState} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn) :
    let prog := insBufIsSomeGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey).isSome then 1 else 0) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hl_st, hl_res, hl_mc, hl_vp⟩ :=
    bufLookupGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s)
  dsimp only
  unfold insBufIsSomeGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hl_st]; rfl
  · rw [clientResult_bind, hl_st, hl_res, clientResult_pure_whp]
    rcases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey with _ | ⟨_, _⟩ <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hl_st, memoryCost_pure]; omega
  · refine validProg_bind hl_vp ?_; rw [hl_st]; exact validProg_pure _

/-- Return `1` iff `fs.rebStage ≤ 3 ∧ (bufLookup (fs.buf fs.oldEp) rKey).isSome`
(`d = ((cp, base), rKey)`). -/
@[irreducible] private def insOldBufSomeGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), rKey) => do
    let z0 ← pure 0
    let z3 ← pure 3
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    if stg ≤ z3 then
      insBufIsSomeGenProg (((cp, base), oldEp), rKey)
    else
      pure z0

private theorem realizes_insOldBufSomeGen :
    Realizes .exact insOldBufSomeGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          (fs.rebStage ≤ 3 →
            ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap))
      (fun _ _ => 0) := by
  unfold insOldBufSomeGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hib := realizes_insBufIsSomeGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce, hbo_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    rw [hrep.2.2.2.2.2.1] at hst_res
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
      hrep.2.2.2.1 (s := s)
    simp only [hst_st, hst_res, hro_st, hro_res] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | (obtain ⟨oldMap, hv_old⟩ := hbo_fn (by omega)
       exact ⟨c, U, V, w, n_max, fs.buf fs.oldEp, oldMap, henv, rfl, hold_or,
         hrep.buf_rep hold_or, hv_old⟩)
  )

private theorem insOldBufSomeGenProg_spec {c U V w n_max base rKey : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hbo_fn : fs.rebStage ≤ 3 →
      ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insOldBufSomeGenProg ((mkWhpCoreParams c U V w n_max, base), rKey)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome
       then 1 else 0) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 10 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
  obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
    (by dsimp [hdrRebStage]; omega) (s := s)
  rw [hrep.2.2.2.2.2.1] at hst_res
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  dsimp only
  unfold insOldBufSomeGenProg; dsimp only; simp only [pure_bind]
  by_cases hle3 : fs.rebStage ≤ 3
  · obtain ⟨oldMap, hv_old⟩ := hbo_fn hle3
    obtain ⟨hib_st, hib_res, hib_mc, hib_vp⟩ :=
      insBufIsSomeGenProg_spec henv hold_or hrep hv_old (rKey := rKey) (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, clientState_bind, hro_st, hro_res,
        ite_eq_left hle3, hib_st]
    · rw [clientResult_bind, hst_st, hst_res, clientResult_bind, hro_st, hro_res,
        ite_eq_left hle3, hib_res]
      by_cases hs : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome = true
      · simp [hle3, hs]
      · simp [hle3, hs]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, hro_st, hro_res, hro_mc, ite_eq_left hle3]; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res]
      refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_left hle3]
      exact hib_vp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, clientState_bind, hro_st, hro_res,
        ite_eq_right hle3]; rfl
    · rw [clientResult_bind, hst_st, hst_res, clientResult_bind, hro_st, hro_res,
        ite_eq_right hle3, clientResult_pure_whp]; simp [hle3]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, hro_st, hro_res, hro_mc, ite_eq_right hle3,
        memoryCost_pure]; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res]
      refine validProg_bind hro_vp ?_; rw [hro_st, hro_res, ite_eq_right hle3]
      exact validProg_pure _

/-- Guard 2 (`insCheckRKeyGuardsGenProg`): return `0` if `rKey` collides in `buf curEp` or active
`buf oldEp`, else `1` (`d = ((cp, base), rKey)`). -/
@[irreducible] def insCheckRKeyGuardsGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), rKey) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let curEp ← readHdrProg (base, hdrCurEp)
    let cHit ← insBufIsSomeGenProg (((cp, base), curEp), rKey)
    let oHit ← insOldBufSomeGenProg ((cp, base), rKey)
    if cHit = z1 ∨ oHit = z1 then
      pure z0
    else
      pure z1

theorem realizes_insCheckRKeyGuardsGen :
    Realizes .exact insCheckRKeyGuardsGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap ∧
          (fs.rebStage ≤ 3 →
            ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap))
      (fun _ _ => 0) := by
  unfold insCheckRKeyGuardsGenProg
  have hrh := realizes_readHdr
  have hib := realizes_insBufIsSomeGen
  have hob := realizes_insOldBufSomeGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur, hbo_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hce_res
    obtain ⟨hc_st, _, _, _⟩ :=
      insBufIsSomeGenProg_spec henv hce hrep hv_cur (rKey := rKey) (s := s)
    obtain ⟨ho_st, _, _, _⟩ :=
      insOldBufSomeGenProg_spec henv hce hbo_fn hrep (rKey := rKey) (s := s)
    simp only [hce_st, hce_res, hc_st, ho_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.curEp, curMap, henv, rfl, hce, hrep.buf_rep hce, hv_cur⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce, hbo_fn⟩
  )

theorem insCheckRKeyGuardsGenProg_spec {c U V w n_max base rKey : ℕ}
    {fs : FastState} {curMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hv_cur : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hbo_fn : fs.rebStage ≤ 3 →
      ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insCheckRKeyGuardsGenProg ((mkWhpCoreParams c U V w n_max, base), rKey)
    let bad : Prop :=
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if bad then 0 else 1) ∧
    memoryCost prog s ≤ 4 * cTabWhp c + 19 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
    (by dsimp [hdrCurEp]; omega) (s := s)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨hc_st, hc_res, hc_mc, hc_vp⟩ :=
    insBufIsSomeGenProg_spec henv hce hrep hv_cur (rKey := rKey) (s := s)
  obtain ⟨ho_st, ho_res, ho_mc, ho_vp⟩ :=
    insOldBufSomeGenProg_spec henv hce hbo_fn hrep (rKey := rKey) (s := s)
  dsimp only
  unfold insCheckRKeyGuardsGenProg; dsimp only; simp only [pure_bind]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hce_st, hce_res, clientState_bind, hc_st, hc_res,
      clientState_bind, ho_st, ho_res]
    split_ifs <;> rfl
  · rw [clientResult_bind, hce_st, hce_res, clientResult_bind, hc_st, hc_res,
      clientResult_bind, ho_st, ho_res]
    by_cases h1 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome = true <;>
      by_cases h2 : fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome = true <;>
      simp [h1, h2]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hce_st, hce_res, hce_mc, hc_st, hc_res, ho_st, ho_res]
    split_ifs <;> (simp only [memoryCost_pure]; omega)
  · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
    refine validProg_bind hc_vp ?_; rw [hc_st, hc_res]
    refine validProg_bind ho_vp ?_; rw [ho_st, ho_res]
    split_ifs <;> exact validProg_pure _

/-- Read `(fpOfSaltOpt (bktSalt b) u_val, liveSliceIdx b)` without mutating memory. -/
@[irreducible] private def insEvalLiveFpGenProg :
    (WhpParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((wp, base), (b, u_val)) => do
    let si ← readLiveSaltIdxGenProg ((wp.1, base), b)
    let hrt ← mkHashRtGenProg (wp, base)
    let fp ← fpOfSaltOptRtProg ((hrt, si.1), u_val)
    pure (fp, si.2)

private theorem realizes_insEvalLiveFpGen :
    Realizes .exact insEvalLiveFpGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((wp, base), (b, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3)
      (fun _ _ => 0) := by
  unfold insEvalLiveFpGenProg
  have hrs := realizes_readLiveSaltIdxGen
  have hmh := realizes_mkHashRtGen
  have hfp := realizes_fpOfSaltOptRt
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hb, hlr⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, _, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    simp only [hcp_eq] at *
    simp only [hrs_st, hrs_res, hmh_st, hmh_res, hfp_st] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

/-- Read `(hasFpCollision, (fp, liveSliceIdx b))` for key `u` without mutating memory. -/
@[irreducible] def insReadFpLiveGenProg :
    (WhpParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((wp, base), (b, u_val)) => do
    let fl ← insEvalLiveFpGenProg ((wp, base), (b, u_val))
    let lk ← btreeLookupGenProg (((wp.1, base), fl.2), fl.1)
    pure (lk.1, fl)

theorem realizes_insReadFpLiveGen :
    Realizes .exact insReadFpLiveGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((wp, base), (b, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm)
      (fun _ _ => 0) := by
  unfold insReadFpLiveGenProg
  have hev := realizes_insEvalLiveFpGen
  have hbt := realizes_btreeLookupGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, heq_wp, hseed, hrep, hb, hlr, hins, hv_sl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    have hev_st : (Memory.spec 0).clientState s
        (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u_val))) = s := by
      unfold insEvalLiveFpGenProg; dsimp only; rw [hcp_eq]
      rw [clientState_bind, hrs_st, hrs_res, clientState_bind, hmh_st, hmh_res,
        clientState_bind, hfp_st]; rfl
    have hev_res : (Memory.spec 0).clientResult s
        (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u_val))) =
        (if hs : fs.bktSalt b < sMaxWhp c n_max then
          if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
         else 0, fs.liveSliceIdx b) := by
      unfold insEvalLiveFpGenProg; dsimp only; rw [hcp_eq]
      rw [clientResult_bind, hrs_st, hrs_res, clientResult_bind, hmh_st, hmh_res,
        clientResult_bind, hfp_st, hfp_res]; rfl
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hfp_lt := fpOfSaltOpt_lt c U n_max (fs.bktSalt b) u_val θ.2
    obtain ⟨hbt_st, _, _, _⟩ :=
      btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
    simp only [hcp_eq] at *
    simp only [hev_st, hev_res, hbt_st] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), lm,
        henv, rfl, hlIdx, hins, hrep.slice_rep hlIdx, hv_sl, hfp_lt⟩
  )

theorem insReadFpLiveGenProg_spec {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_sl : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm) :
    let prog := insReadFpLiveGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let lIdx := fs.liveSliceIdx b
    let hasCol := (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices lIdx) fp).isSome
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if hasCol then 1 else 0, (fp, lIdx)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 266 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u.val) henv hseed (s := s)
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  have hfp_eq : (if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u.val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u.val, hu⟩ else 0
     else 0) = fp := by
    dsimp only [fp, fpOfSalt]
    split_ifs with hs hu <;> first | rfl | exact absurd u.isLt hu
  rw [hfp_eq] at hfp_res
  have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
    rw [← hfp_eq]; exact fpOfSaltOpt_lt c U n_max _ _ θ.2
  have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.liveSliceIdx; omega
  obtain ⟨hbt_st, hbt_res, hbt_mc, hbt_vp⟩ :=
    btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
  rw [← hv_sl.lookup_eq hth hins hfp_lt] at hbt_res
  have hev_st : (Memory.spec 0).clientState s
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) = s := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    rw [clientState_bind, hrs_st, hrs_res, clientState_bind, hmh_st, hmh_res,
      clientState_bind, hfp_st]; rfl
  have hev_res : (Memory.spec 0).clientResult s
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) =
      (fp, fs.liveSliceIdx b) := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    rw [clientResult_bind, hrs_st, hrs_res, clientResult_bind, hmh_st, hmh_res,
      clientResult_bind, hfp_st, hfp_res]; rfl
  have hev_mc : memoryCost
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) s ≤
      hashEvalCostWhp c + 4 := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrs_st, hrs_res, hrs_mc, hmh_st, hmh_res, hmh_mc, hfp_st, hfp_res, memoryCost_pure]
    have hfp_mc' : memoryCost (fpOfSaltOptRtProg ((mkHashRt c U w n_max base, fs.bktSalt b),
        u.val)) s ≤ hashEvalCostWhp c := hfp_mc
    dsimp only; omega
  have hev_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) := by
    unfold insEvalLiveFpGenProg; dsimp only; rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
    exact validProg_pure _
  dsimp only
  unfold insReadFpLiveGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hev_st, hev_res, clientState_bind, hbt_st]; rfl
  · rw [clientResult_bind, hev_st, hev_res, clientResult_bind, hbt_st, hbt_res,
      clientResult_pure_whp]
    cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hev_st, hev_res, hbt_st, memoryCost_pure]
    dsimp only [cp, fp] at hbt_mc ⊢; omega
  · refine validProg_bind hev_vp ?_; rw [hev_st, hev_res]
    refine validProg_bind hbt_vp ?_; rw [hbt_st]; exact validProg_pure _

/-- Read `(fs.buf fs.curEp).itemAlloc` from headers `hdrBuf0ItemAlloc` / `hdrBuf1ItemAlloc`. -/
@[irreducible] private def insReadCurBufItemAllocProg (base : ℕ) : Memory.Prog ℕ := do
  let z0 ← pure 0
  let curEp ← readHdrProg (base, hdrCurEp)
  if curEp = z0 then
    readHdrProg (base, hdrBuf0ItemAlloc)
  else
    readHdrProg (base, hdrBuf1ItemAlloc)

private theorem realizes_insReadCurBufItemAlloc :
    Realizes .exact insReadCurBufItemAllocProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w base _ => 2 ≤ w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold insReadCurBufItemAllocProg
  have hrh := realizes_readHdr
  realize
  all_goals (
    obtain ⟨_, hfit32⟩ := h
    exact hfit32.of_le (by dsimp [hdrCurEp, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega)
  )

private theorem insReadCurBufItemAllocProg_spec {c U V w n_max base : ℕ}
    {fs : FastState} {s : Memory.State}
    (_henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insReadCurBufItemAllocProg base
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (fs.buf fs.curEp).itemAlloc ∧
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
    (by dsimp [hdrCurEp]; omega) (s := s)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨hi0_st, hi0_res, hi0_mc, hi0_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf0ItemAlloc)
    (by dsimp [hdrBuf0ItemAlloc]; omega) (s := s)
  obtain ⟨hi1_st, hi1_res, hi1_mc, hi1_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrBuf1ItemAlloc)
    (by dsimp [hdrBuf1ItemAlloc]; omega) (s := s)
  have hia0 : s.mem (base + hdrBuf0ItemAlloc) = (fs.buf 0).itemAlloc :=
    (hrep.buf_rep (Or.inl rfl)).2.2.2.1
  have hia1 : s.mem (base + hdrBuf1ItemAlloc) = (fs.buf 1).itemAlloc :=
    (hrep.buf_rep (Or.inr rfl)).2.2.2.1
  rw [hia0] at hi0_res
  rw [hia1] at hi1_res
  dsimp only
  unfold insReadCurBufItemAllocProg; simp only [pure_bind]
  rcases hce with hc0 | hc1
  · rw [hc0] at hce_res ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hce_st, hce_res, ite_eq_left rfl, hi0_st]
    · rw [clientResult_bind, hce_st, hce_res, ite_eq_left rfl, hi0_res]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hce_st, hce_res, hce_mc, ite_eq_left rfl, hi0_mc]
    · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res, ite_eq_left rfl]; exact hi0_vp
  · rw [hc1] at hce_res ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hce_st, hce_res, ite_eq_right (by decide : ¬(1 = 0)), hi1_st]
    · rw [clientResult_bind, hce_st, hce_res, ite_eq_right (by decide : ¬(1 = 0)), hi1_res]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hce_st, hce_res, hce_mc, ite_eq_right (by decide : ¬(1 = 0)), hi1_mc]
    · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res, ite_eq_right (by decide : ¬(1 = 0))]
      exact hi1_vp

/-- Guard 3 active helper (`hasFpCollision = true`): return `0` iff
`!bufEverPresent (buf curEp) rKey ∧ 2 * sMaxWhp ≤ (buf curEp).itemAlloc`, else `1`. -/
@[irreducible] private def insCheckFpCapActiveGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), rKey) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let curEp ← readHdrProg (base, hdrCurEp)
    let ev ← bufEverPresentGenProg (((cp, base), curEp), rKey)
    let ia ← insReadCurBufItemAllocProg base
    let cap ← pure (wpBufItemCap cp)
    if ev = z0 ∧ cap ≤ ia then
      pure z0
    else
      pure z1

private theorem realizes_insCheckFpCapActiveGen :
    Realizes .exact insCheckFpCapActiveGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
      (fun _ _ => 0) := by
  unfold insCheckFpCapActiveGenProg
  have hrh := realizes_readHdr
  have hev := realizes_bufEverPresentGen
  have hia := realizes_insReadCurBufItemAlloc
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hce_res
    obtain ⟨hev_st, _, _, _⟩ :=
      bufEverPresentGenProg_spec henv hce (hrep.buf_rep hce) hv_cur (rKey := rKey) (s := s)
    obtain ⟨hia_st, _, _, _⟩ := insReadCurBufItemAllocProg_spec henv hce hrep (s := s)
    simp only [hce_st, hce_res, hev_st, hia_st] at *
    first
    | exact h2w
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact ⟨c, U, V, w, n_max, fs.buf fs.curEp, curMap, henv, rfl, hce, hrep.buf_rep hce, hv_cur⟩
  )

/-- Guard 3 wrapper (`d = (((cp, base), hasCol), rKey)`). -/
@[irreducible] def insCheckFpCapOptGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), hasCol), rKey) => do
    let z1 ← pure 1
    if hasCol = z1 then
      insCheckFpCapActiveGenProg ((cp, base), rKey)
    else
      pure z1

theorem realizes_insCheckFpCapOptGen :
    Realizes .exact insCheckFpCapOptGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), _), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
      (fun _ _ => 0) := by
  unfold insCheckFpCapOptGenProg
  have hca := realizes_insCheckFpCapActiveGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, hasCol⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur⟩
  )

theorem insCheckFpCapOptGenProg_spec {c U V w n_max base rKey : ℕ}
    {fs : FastState} {curMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State} (hasFpCollision : Bool)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hv_cur : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let hasCol := if hasFpCollision then 1 else 0
    let prog := insCheckFpCapOptGenProg (((mkWhpCoreParams c U V w n_max, base), hasCol), rKey)
    let bad3 : Prop :=
      hasFpCollision ∧
        !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
        2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if bad3 then 0 else 1) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  dsimp only
  unfold insCheckFpCapOptGenProg; dsimp only; simp only [pure_bind]
  cases hasFpCollision with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one, false_and, memoryCost_pure]
    exact ⟨rfl, rfl, Nat.zero_le _, validProg_pure _⟩
  | true =>
    simp only [↓reduceIte, true_and]
    obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hce_res
    obtain ⟨hev_st, hev_res, hev_mc, hev_vp⟩ :=
      bufEverPresentGenProg_spec henv hce (hrep.buf_rep hce) hv_cur (rKey := rKey) (s := s)
    obtain ⟨hia_st, hia_res, hia_mc, hia_vp⟩ :=
      insReadCurBufItemAllocProg_spec henv hce hrep (s := s)
    unfold insCheckFpCapActiveGenProg; dsimp only
    simp only [wp_large_bufItemCap hth, pure_bind]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hce_st, hce_res, clientState_bind, hev_st, hev_res,
        clientState_bind, hia_st, hia_res]
      split_ifs <;> rfl
    · rw [clientResult_bind, hce_st, hce_res, clientResult_bind, hev_st, hev_res,
        clientResult_bind, hia_st, hia_res]
      cases bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey <;>
        by_cases hle : 2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc <;>
        simp [hle]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hce_st, hce_res, hce_mc, hev_st, hev_res, hia_st, hia_res]
      split_ifs <;> (simp only [memoryCost_pure]; omega)
    · refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
      refine validProg_bind hev_vp ?_; rw [hev_st, hev_res]
      refine validProg_bind hia_vp ?_; rw [hia_st, hia_res]
      split_ifs <;> exact validProg_pure _

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

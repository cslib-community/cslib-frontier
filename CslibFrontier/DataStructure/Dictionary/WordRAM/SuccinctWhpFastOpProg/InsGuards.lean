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

private theorem CostBoundedStep.weaken {α : Type} {w F C C' : ℕ} {s s' : Memory.State}
    {p : Memory.Prog α} {r r' : α} (h : CostBoundedStep w F s p s' r C) (hr : r = r')
    (hC : C ≤ C') :
    (Memory.spec 0).clientState s p = s' ∧ (Memory.spec 0).clientResult s p = r' ∧
      memoryCost p s ≤ C' ∧ ValidProg w F s p :=
  ⟨h.clientState_eq, h.clientResult_eq.trans hr, h.memoryCost_le.trans hC, h.validProg⟩

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
  realize [realizes_readBktFieldGen, realizes_readHdr]
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
  have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
  obtain ⟨hc0_st, hc0_res, hc0_mc, hc0_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
  simp only [getBktField] at hc0_res
  obtain ⟨ht_st, ht_res, ht_mc, ht_vp⟩ := readHdrProg_large_spec c U V w n_max
    (base := base) (hdrOff := hdrPoolFreeTop) (s := s) (by decide)
  rw [hrep.2.2.1] at ht_res
  dsimp only
  unfold insCheckCapPoolGenProg; dsimp only
  simp only [wp_large_totalLoc hth, wp_large_capFront hth, pure_bind]
  exact CostBoundedStep.weaken (.bind ⟨hc0_st, hc0_res, hc0_mc.le, hc0_vp⟩ <|
    .bind ⟨ht_st, ht_res, ht_mc.le, ht_vp⟩ <| .ite (.pure _ _) (.pure _ _)) rfl (by omega)

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
  realize [realizes_bufLookupGen]
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
  exact CostBoundedStep.weaken (.bind ⟨hl_st, hl_res, hl_mc, hl_vp⟩ (.pure _ _))
    (by rcases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey with _ | ⟨_, _⟩ <;> rfl)
    (by omega)

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
  realize [realizes_readHdr, realizes_readOldEp, realizes_insBufIsSomeGen]
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce, hbo_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrRebStage) (s := s) (by decide)
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
  have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
  obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_large_spec c U V w n_max
    (base := base) (hdrOff := hdrRebStage) (s := s) (by decide)
  rw [hrep.2.2.2.2.2.1] at hst_res
  obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce
    hrep.2.2.2.1 (s := s)
  unfold insOldBufSomeGenProg
  simp only [pure_bind]
  refine CostBoundedStep.weaken (C := 1 + (1 + (2 * cTabWhp c + 8)))
    (.bind ⟨hst_st, hst_res, hst_mc.le, hst_vp⟩ <|
      .bind ⟨hro_st, hro_res, hro_mc.le, hro_vp⟩ ?_) rfl (by omega)
  by_cases hle3 : fs.rebStage ≤ 3
  · obtain ⟨oldMap, hv_old⟩ := hbo_fn hle3
    obtain ⟨hb1, hb2, hb3, hb4⟩ := insBufIsSomeGenProg_spec henv hold_or hrep hv_old (rKey := rKey)
    simpa only [hle3, true_and, ↓reduceIte] using
      (⟨hb1, hb2, hb3, hb4⟩ : CostBoundedStep ..)
  · simpa only [hle3, false_and, ↓reduceIte] using
      (CostBoundedStep.pure s 0).mono (Nat.zero_le _)

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
  realize [realizes_readHdr, realizes_insBufIsSomeGen, realizes_insOldBufSomeGen]
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur, hbo_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrCurEp) (s := s) (by decide)
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
  have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_large_spec c U V w n_max
    (base := base) (hdrOff := hdrCurEp) (s := s) (by decide)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨hc_st, hc_res, hc_mc, hc_vp⟩ :=
    insBufIsSomeGenProg_spec henv hce hrep hv_cur (rKey := rKey) (s := s)
  obtain ⟨ho_st, ho_res, ho_mc, ho_vp⟩ :=
    insOldBufSomeGenProg_spec henv hce hbo_fn hrep (rKey := rKey) (s := s)
  dsimp only
  unfold insCheckRKeyGuardsGenProg; dsimp only; simp only [pure_bind]
  refine CostBoundedStep.weaken (.bind ⟨hce_st, hce_res, hce_mc.le, hce_vp⟩ <|
    .bind ⟨hc_st, hc_res, hc_mc, hc_vp⟩ <| .bind ⟨ho_st, ho_res, ho_mc, ho_vp⟩ <|
    .ite (.pure _ _) (.pure _ _)) ?_ (by omega)
  split_ifs <;> simp_all

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
  realize [realizes_readLiveSaltIdxGen, realizes_mkHashRtGen, realizes_fpOfSaltOptRt]
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hlr⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, _, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    simp only [hcp_eq, hrs_st, hrs_res, hmh_st, hmh_res, hfp_st] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
  )

private theorem insEvalLiveFpGenProg_step {c U V w n_max base b u_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) :
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (insEvalLiveFpGenProg ((mkWhpParams c U V w n_max, base), (b, u_val))) s
      (if hs : fs.bktSalt b < sMaxWhp c n_max then
        if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
       else 0, fs.liveSliceIdx b)
      (hashEvalCostWhp c + 4) := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
  unfold insEvalLiveFpGenProg
  dsimp only
  rw [hwp1]
  exact .mono (.bind ⟨hrs_st, hrs_res, hrs_mc.le, hrs_vp⟩ <|
    .bind ⟨hmh_st, hmh_res, hmh_mc.le, hmh_vp⟩ <| .bind ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ <|
    .pure _ _) (by omega)

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
  realize [realizes_insEvalLiveFpGen, realizes_btreeLookupGen]
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hb, hlr, hins, hv_sl⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hev_step := insEvalLiveFpGenProg_step (u_val := u_val) henv hseed hrep hb (s := s)
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hfp_lt := fpOfSaltOpt_lt c U n_max (fs.bktSalt b) u_val θ.2
    obtain ⟨hbt_st, _, _, _⟩ :=
      btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
    simp only [hcp_eq, hev_step.clientState_eq, hev_step.clientResult_eq, hbt_st] at *
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
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  have hfp_eq : (if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u.val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u.val, hu⟩ else 0
     else 0) = fp := by simp [fp, fpOfSalt, u.isLt]
  have hev := insEvalLiveFpGenProg_step (u_val := u.val) henv hseed hrep hb (s := s)
  rw [hfp_eq] at hev
  have hfp_lt : fp < 2 ^ fpBitsWhp n_max := hfp_eq ▸ fpOfSaltOpt_lt c U n_max _ _ θ.2
  have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.liveSliceIdx; omega
  obtain ⟨hbt_st, hbt_res, hbt_mc, hbt_vp⟩ :=
    btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
  rw [← hv_sl.lookup_eq hth hins hfp_lt] at hbt_res
  dsimp only
  unfold insReadFpLiveGenProg; dsimp only
  rw [hwp1]
  refine CostBoundedStep.weaken
    (.bind hev <| .bind ⟨hbt_st, hbt_res, hbt_mc, hbt_vp⟩ <| .pure _ _) ?_ (by omega)
  cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    (fs.slices (fs.liveSliceIdx b)) fp <;> rfl

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
  realize [realizes_readHdr]
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
  have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_large_spec c U V w n_max
    (base := base) (hdrOff := hdrCurEp) (s := s) (by decide)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨_, _hv, _hna, hmIa, _⟩ := hrep.buf_rep hce
  obtain ⟨hi_st, hi_res, hi_mc, hi_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base)
    (hdrOff := if fs.curEp = 0 then hdrBuf0ItemAlloc else hdrBuf1ItemAlloc)
    (by split_ifs <;> dsimp [hdrBuf0ItemAlloc, hdrBuf1ItemAlloc] <;> omega) (s := s)
  unfold insReadCurBufItemAllocProg
  simp only [pure_bind]
  refine CostBoundedStep.weaken (C := 1 + 1)
    (.bind ⟨hce_st, hce_res, hce_mc.le, hce_vp⟩ ?_) rfl (by omega)
  have hstep : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readHdrProg (base, if fs.curEp = 0 then hdrBuf0ItemAlloc else hdrBuf1ItemAlloc)) s
      (fs.buf fs.curEp).itemAlloc 1 := ⟨hi_st, hi_res.trans hmIa, hi_mc.le, hi_vp⟩
  split_ifs with hc0 <;> simpa only [hc0, ↓reduceIte] using hstep

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
  realize [realizes_readHdr, realizes_bufEverPresentGen, realizes_insReadCurBufItemAlloc]
  all_goals (
    rcases d with ⟨⟨cp, base⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, curMap, henv, rfl, hrep, hce, hv_cur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have h2w := henv.two_le_w
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrCurEp) (s := s) (by decide)
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
  realize [realizes_insCheckFpCapActiveGen]
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
  have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
  dsimp only
  unfold insCheckFpCapOptGenProg; dsimp only; simp only [pure_bind]
  cases hasFpCollision with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one, false_and, memoryCost_pure]
    exact ⟨rfl, rfl, Nat.zero_le _, validProg_pure _⟩
  | true =>
    simp only [↓reduceIte, true_and]
    obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrCurEp) (s := s) (by decide)
    rw [hrep.2.2.2.1] at hce_res
    obtain ⟨hev_st, hev_res, hev_mc, hev_vp⟩ :=
      bufEverPresentGenProg_spec henv hce (hrep.buf_rep hce) hv_cur (rKey := rKey) (s := s)
    obtain ⟨hia_st, hia_res, hia_mc, hia_vp⟩ :=
      insReadCurBufItemAllocProg_spec henv hce hrep (s := s)
    unfold insCheckFpCapActiveGenProg; dsimp only
    simp only [wp_large_bufItemCap hth, pure_bind]
    refine CostBoundedStep.weaken (.bind ⟨hce_st, hce_res, hce_mc.le, hce_vp⟩ <|
      .bind ⟨hev_st, hev_res, hev_mc, hev_vp⟩ <| .bind ⟨hia_st, hia_res, hia_mc, hia_vp⟩ <|
      .ite (.pure _ _) (.pure _ _)) ?_ (by omega)
    cases bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey <;> simp

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

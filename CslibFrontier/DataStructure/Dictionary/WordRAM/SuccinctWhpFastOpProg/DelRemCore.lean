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
# Fast Deletion Removal Core (`buf`, `liveSlice`, `overmarsSlice`)

Sub-helpers for Substep 1 (`fastDeleteRemove`) removing `u` from `buf 0`/`buf 1`,
`liveSlice[b]`, and `overmarsSlice[b]`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemBufGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemLiveGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemOmGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delRemBufGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemBufGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delRemLiveGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemLiveGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delRemOmGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delRemOmGenProg_fastStep`
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

private theorem inLiveTag_reads_step {c U V w n_max base b : ℕ} {fs : FastState}
    {s : Memory.State} (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1) (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readHdrProg (base, hdrRebStage)) s fs.rebStage 1 ∧
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readOldEpProg base) s fs.oldEp 1 ∧
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), 8)) s
      (fs.rebDoneFlag b) 2 := by
  have := headerWords_le_largeSpaceWhp c U V w n_max
  exact ⟨hrep.2.2.2.2.2.1 ▸ .of (readHdrProg_spec (w := w) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega)),
    .of (readOldEpProg_spec (w := w) (by dsimp [hdrCurEp]; omega) hce hrep.2.2.2.1),
    CostBoundedStep.readBkt henv hb (by decide : 8 < 10) hrep⟩

/-- Sub-helper 6.1a: delete `rKey_u` from `buf 0` (`st_del = 2`) or `buf 1` (`st_del = 3`). -/
@[irreducible] def delRemBufGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), st_del), rKey_u) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let z3 ← pure 3
    if st_del = z2 then
      bufDeleteGenProg (((cp, base), z0), rKey_u)
    else if st_del = z3 then
      bufDeleteGenProg (((cp, base), z1), rKey_u)
    else
      pure ()

theorem realizes_delRemBufGen :
    Realizes .exact delRemBufGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), st_del), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (st_del = 2 → ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0) ∧
          (st_del = 3 → ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1))
      (fun _ _ => 0) := by
  unfold delRemBufGenProg
  have hbd := realizes_bufDeleteGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, st_del⟩, rKey_u⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, h2, h3⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    first
    | exact henv.fits_const (by decide)
    | (obtain ⟨m0, hv0⟩ := h2 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 0, m0, henv, rfl, Or.inl rfl,
         hrep.buf_rep (Or.inl rfl), hv0⟩)
    | (obtain ⟨m1, hv1⟩ := h3 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 1, m1, henv, rfl, Or.inr rfl,
         hrep.buf_rep (Or.inr rfl), hv1⟩)
  )

theorem delRemBufGenProg_fastStep {c U V w n_max base st_del rKey_u : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (h2 : st_del = 2 → ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0)
    (h3 : st_del = 3 → ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemBufGenProg (((mkWhpCoreParams c U V w n_max, base), st_del), rKey_u)
    let s' := (Memory.spec 0).clientState s prog
    let buf1 :=
      if st_del = 2 then
        Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
      else if st_del = 3 then
        Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
      else fs.buf
    memoryCost prog s ≤ 2 * cTabWhp c + 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := buf1 } s s' := by
  simp only [delRemBufGenProg, pure_bind]
  split_ifs with hs2 hs3
  · obtain ⟨m0, hv0⟩ := h2 hs2
    exact bufDeleteGenProg_fastStep henv (Or.inl rfl) hseed hrep hv0
  · obtain ⟨m1, hv1⟩ := h3 hs3
    exact bufDeleteGenProg_fastStep henv (Or.inr rfl) hseed hrep hv1
  · exact ⟨Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩

/-- Sub-helper 6.1b: delete `fp_live_u` from `liveSlice[b]` when `inLiveTree` holds. -/
@[irreducible] def delRemLiveGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((cp, base), b), (st_del, fp_live_u)) => do
    let z1 ← pure 1
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    let inL ← inLiveTreeProg ((stg, oldEp), (doneB, st_del))
    if inL = z1 then do
      let lr ← readBktFieldGenProg (((cp, base), b), 2)
      let lIdx ← pure (3 * b + lr)
      btreeDeleteGenProg (((cp, base), lIdx), fp_live_u)
    else
      pure ()

theorem realizes_delRemLiveGen :
    Realizes .exact delRemLiveGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), (_, fp_live_u)) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemLiveGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hil := realizes_inLiveTree
  have hbd := realizes_btreeDeleteGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, ⟨st_del, fp_live_u⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, lm, henv, rfl, hrep, hce, hb, hlr, hins, hv_l, hfp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨hS, hO, h8⟩ := inLiveTag_reads_step henv hce hb hrep (s := s)
    have h2 := CostBoundedStep.readBkt henv hb (by decide : 2 < 10) hrep (s := s)
    have hst_il := (inLiveTreeProg_spec (w := w) (F := 0) (rebStage := fs.rebStage)
      (oldEp := fs.oldEp) (rebDoneB := fs.rebDoneFlag b) (st := st_del) (s := s)).1
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    simp only [hS.clientState_eq, hS.clientResult_eq, hO.clientState_eq, hO.clientResult_eq,
      h8.clientState_eq, h8.clientResult_eq, h2.clientState_eq, h2.clientResult_eq, getBktField,
      hst_il, wp_large_M hth] at *
    first
    | decide
    | exact h2w
    | exact hold
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), lm,
        henv, rfl, hlIdx, hins, hrep.slice_rep hlIdx, hv_l, hfp⟩
  )

theorem delRemLiveGenProg_fastStep {c U V w n_max base b st_del fp_live_u : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_l : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm)
    (hfp : fp_live_u < 2 ^ fpBitsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemLiveGenProg (((mkWhpCoreParams c U V w n_max, base), b), (st_del, fp_live_u))
    let s' := (Memory.spec 0).clientState s prog
    let lIdx := fs.liveSliceIdx b
    let slices1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices lIdx
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices lIdx) fp_live_u)
      else fs.slices
    memoryCost prog s ≤ 280 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with slices := slices1 } s s' := by
  obtain ⟨hS, hO, h8⟩ := inLiveTag_reads_step henv hce hb hrep (s := s)
  have hIL := CostBoundedStep.of
    (inLiveTreeProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max)
      (rebStage := fs.rebStage) (oldEp := fs.oldEp) (rebDoneB := fs.rebDoneFlag b) (st := st_del)
      (s := s))
  simp only [delRemLiveGenProg, pure_bind]
  by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
  · rw [ite_eq_left hin] at hIL ⊢
    have h2 := CostBoundedStep.readBkt henv hb (by decide : 2 < 10) hrep (s := s)
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
      btreeDeleteGenProg_fastStep henv hlIdx hins hseed hrep hv_l hfp (s := s)
    exact CostBoundedStep.elim (.bind hS <| .bind hO <| .bind h8 <| .bind hIL <| .if_pos rfl <|
      .bind h2 ⟨rfl, rfl, hbd_mc, hbd_vp⟩) (by omega) hbd_step
  · rw [ite_eq_right hin] at hIL ⊢
    exact CostBoundedStep.elim
      (.bind hS <| .bind hO <| .bind h8 <| .bind hIL <| .if_neg (by decide) <| .pure _ _)
      (by omega) (FastStateStep.refl hseed hrep)

/-- Active deletion helper for `delRemOmGenProg`: read `overmarsRole b` and delete `fp_live_u`
from `overmarsSlice[b]`. -/
@[irreducible] private def delRemOmDeleteProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), fp_live_u) => do
    let orl ← readBktFieldGenProg (((cp, base), b), 4)
    let omIdx ← pure (3 * b + orl)
    btreeDeleteGenProg (((cp, base), omIdx), fp_live_u)

private theorem realizes_delRemOmDelete :
    Realizes .exact delRemOmDeleteProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), fp_live_u) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (om : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          fs.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.overmarsInsCount b)
            (fs.slices (fs.overmarsSliceIdx b)) om ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemOmDeleteProg
  have hrb := realizes_readBktFieldGen
  have hbd := realizes_btreeDeleteGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, fp_live_u⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, om, henv, rfl, hrep, hb, hor, hins_om, hv_om, hfp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨hst_4, hres_4, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 4 < 10)
      hrep (s := s)
    simp only [getBktField] at hres_4
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    simp only [hst_4, hres_4, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), om,
        henv, rfl, homIdx, hins_om, hrep.slice_rep homIdx, hv_om, hfp⟩
  )

/-- Read `if inLiveTree rebStage oldEp (rebDoneFlag b) st then 1 else 0` without mutating memory.
-/
@[irreducible] private def readInLiveTagGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), st) => do
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    inLiveTreeProg ((stg, oldEp), (doneB, st))

private theorem realizes_readInLiveTagGen :
    Realizes .exact readInLiveTagGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max)
      (fun _ _ => 0) := by
  unfold readInLiveTagGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hil := realizes_inLiveTree
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, st⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce, hb⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have hold : fs.oldEp ≤ 1 := by rcases hce with hc | hc <;> simp [FastState.oldEp, hc]
    obtain ⟨⟨hst_s, hres_s, _, _⟩, ⟨hst_o, hres_o, _, _⟩, ⟨hst_8, hres_8, _, _⟩⟩ :=
      inLiveTag_reads_step henv hce hb hrep (s := s)
    simp only [hst_s, hres_s, hst_o, hres_o, hst_8, hres_8, wp_large_M hth] at *
    first
    | decide
    | exact h2w
    | exact hold
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem readInLiveTagGenProg_spec {c U V w n_max base b st : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readInLiveTagGenProg (((mkWhpCoreParams c U V w n_max, base), b), st)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st then 1 else 0) ∧
    memoryCost prog s ≤ 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hS, hO, h8⟩ := inLiveTag_reads_step henv hce hb hrep (s := s)
  suffices h : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readInLiveTagGenProg (((mkWhpCoreParams c U V w n_max, base), b), st)) s
      (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st then 1 else 0) 5 from
    ⟨h.clientState_eq, h.clientResult_eq, h.memoryCost_le, h.validProg⟩
  unfold readInLiveTagGenProg
  exact .mono (.bind hS <| .bind hO <| .bind h8 <| .of (inLiveTreeProg_spec (w := w)
    (rebStage := fs.rebStage) (oldEp := fs.oldEp) (rebDoneB := fs.rebDoneFlag b) (st := st)))
    (by omega)

/-- Sub-helper 6.1c: delete `fp_live_u` from `overmarsSlice[b]` when active and `< overmarsCursor`.
-/
@[irreducible] def delRemOmGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), loc_del), (st_del, fp_live_u)) => do
    let z1 ← pure 1
    let omAct ← readBktFieldGenProg (((cp, base), b), 5)
    let omCur ← readBktFieldGenProg (((cp, base), b), 6)
    let inL ← readInLiveTagGenProg (((cp, base), b), st_del)
    if omAct = z1 ∧ loc_del < omCur ∧ inL = z1 then
      delRemOmDeleteProg (((cp, base), b), fp_live_u)
    else
      pure ()

theorem realizes_delRemOmGen :
    Realizes .exact delRemOmGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), _), (_, fp_live_u)) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3 ∧
          (fs.overmarsActive b = 1 →
            fs.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
            ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b)
              (fs.slices (fs.overmarsSliceIdx b)) om) ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemOmGenProg
  have hrb := realizes_readBktFieldGen
  have hil := realizes_readInLiveTagGen
  have hdo := realizes_delRemOmDelete
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, ⟨st_del, fp_live_u⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce, hb, hor, hom_fn, hfp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h5 := CostBoundedStep.readBkt henv hb (by decide : 5 < 10) hrep (s := s)
    have h6 := CostBoundedStep.readBkt henv hb (by decide : 6 < 10) hrep (s := s)
    have hst_il := (readInLiveTagGenProg_spec henv hce hb hrep (st := st_del) (s := s)).1
    simp only [h5.clientState_eq, h5.clientResult_eq, h6.clientState_eq, h6.clientResult_eq,
      getBktField, hst_il, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce, hb⟩
    | (obtain ⟨hins_om, om, hv_om⟩ := hom_fn (by omega)
       exact ⟨c, U, V, w, n_max, fs, om, henv, rfl, hrep, hb, hor, hins_om, hv_om, hfp⟩)
  )

theorem delRemOmGenProg_fastStep {c U V w n_max base b loc_del st_del fp_live_u : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hom_fn : fs.overmarsActive b = 1 →
      fs.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) om)
    (hfp : fp_live_u < 2 ^ fpBitsWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delRemOmGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), (st_del, fp_live_u))
    let s' := (Memory.spec 0).clientState s prog
    let omIdx := fs.overmarsSliceIdx b
    let slices2 :=
      if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices omIdx
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices omIdx) fp_live_u)
      else fs.slices
    memoryCost prog s ≤ 285 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with slices := slices2 } s s' := by
  have h5 := CostBoundedStep.readBkt henv hb (by decide : 5 < 10) hrep (s := s)
  have h6 := CostBoundedStep.readBkt henv hb (by decide : 6 < 10) hrep (s := s)
  obtain ⟨hIL1, hIL2, hIL3, hIL4⟩ :=
    readInLiveTagGenProg_spec henv hce hb hrep (st := st_del) (s := s)
  simp only [getBktField] at h5 h6
  have hin_iff {x : Bool} : (if x then 1 else 0) = (1 : ℕ) ↔ x = true := by cases x <;> simp
  simp only [delRemOmGenProg, delRemOmDeleteProg, pure_bind]
  by_cases hcond : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
      inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
  · rw [ite_eq_left hcond]
    obtain ⟨ha, hloc, hin⟩ := hcond
    obtain ⟨hins_om, om, hv_om⟩ := hom_fn ha
    have h4 := CostBoundedStep.readBkt henv hb (by decide : 4 < 10) hrep (s := s)
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    obtain ⟨hbd_mc, hbd_vp, hbd_step⟩ :=
      btreeDeleteGenProg_fastStep henv homIdx hins_om hseed hrep hv_om hfp (s := s)
    exact CostBoundedStep.elim (.bind h5 <| .bind h6 <| .bind ⟨hIL1, hIL2, hIL3, hIL4⟩ <|
      .if_pos ⟨ha, hloc, hin_iff.mpr hin⟩ <| .bind h4 ⟨rfl, rfl, hbd_mc, hbd_vp⟩)
      (by omega) hbd_step
  · rw [ite_eq_right hcond]
    exact CostBoundedStep.elim (.bind h5 <| .bind h6 <| .bind ⟨hIL1, hIL2, hIL3, hIL4⟩ <|
      .if_neg (fun ⟨ha, hloc, hin⟩ => hcond ⟨ha, hloc, hin_iff.mp hin⟩) <| .pure _ _) (by omega)
      (FastStateStep.refl hseed hrep)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end

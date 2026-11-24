/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeFallbackBase
-- Private fallback pool helpers shared across the LargeFallbackBase/LargeEpochFallback split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeFallbackBase
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic `1 · OPT` Fallback Transition and Dictionary Operations (`LargeEpochFallback`)

Completes the deterministic `1 · OPT` `FallbackPool` (`fallbackMode = 1`) for
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024] atop `LargeFallbackBase`:

1. **`enterFallbackProg`**: deterministic in-place transition from any `CoreValid` `BlockPoolState`
   into a valid `FallbackState` (`tailLen ≤ 6 * M * K`, `fallbackMode := 1`) preserving `1 · OPT`
   frontier and `PoolItemsRefines` without resampling active epoch hash seeds.
2. **Public Fallback Operations**: `fallbackQueryProg`, `fallbackInsertProg`, `fallbackDeleteProg`,
   and `fallbackPopAnyProg` (`RealizesBounded .exact`, `¬ReadsWidth`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.enterFallbackProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.FallbackOpCtx`,
  `FallbackLayout.toCtx`, `fallbackQueryProg`, `fallbackInsertProg`, `fallbackDeleteProg`,
  `fallbackPopAnyProg`.

## Main results

* `enterFallbackProg_spec`, `fallbackQueryProg_spec`, `fallbackInsertProg_spec`,
  `fallbackDeleteProg_spec`, `fallbackPopAnyProg_spec`.
-/

public section

open scoped BigOperators

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Finset

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Tail Owner Reconstruction and `enterFallbackProg` -/

/-- Step 3 helpers: read `(bp₁.ownerOf (π (p / K) * K + p % K)).1` and fill `ownerTail`. -/
private def fbTailOwnerAtBlkProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (mctx, (P, off)) => do
    let tb ← bpReadSlabOwnerProg (mctx, (P, 2))
    let tIdx ← bpTbSlotProg (mctx, (tb, off))
    bpReadTailOwnerProg (mctx, (tIdx, 0))

private theorem state_fbTailOwnerAtBlkProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbTailOwnerAtBlkProg x) = s := by
  rcases x with ⟨mctx, ⟨P, off⟩⟩
  unfold fbTailOwnerAtBlkProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
    StateTransitionSpec.clientState_bind, clientState_bpTbSlotProg]
  exact clientState_bpReadTailOwnerProg _ s

private theorem realizesBounded_fbTailOwnerAtBlk :
    RealizesBounded .exact fbTailOwnerAtBlkProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (mctx, _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  have hts := realizesBounded_bpTbSlot
  have hrto := realizesBounded_bpReadTailOwner
  realize
  all_goals (
    rcases d with ⟨mctx, ⟨P, off⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    have h12K := hmv.twelve_K_le
    have h2_w : 2 < 2 ^ w := lt_of_le_of_lt (by omega) hnc_w
    try simp only [runClient_state_bpReadSlabOwnerProg, runClient_state_bpTbSlotProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | omega)

private def fbSlotBktTag2Prog : BpMetaCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | (mctx, (P, off)) => do
    let b ← bpReadSlabOwnerProg (mctx, (P, 1))
    let cur ← bpActCurProg (mctx, b)
    if off < cur then pure b else fbTailOwnerAtBlkProg (mctx, (P, off))

private theorem state_fbSlotBktTag2Prog (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbSlotBktTag2Prog x) = s := by
  rcases x with ⟨mctx, ⟨P, off⟩⟩
  unfold fbSlotBktTag2Prog
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
    StateTransitionSpec.clientState_bind, clientState_bpActCurProg]
  split_ifs
  · rfl
  · exact state_fbTailOwnerAtBlkProg _ s

private theorem realizesBounded_fbSlotBktTag2 :
    RealizesBounded .exact fbSlotBktTag2Prog
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (mctx, _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  have hac := realizesBounded_bpActCur
  have hto := realizesBounded_fbTailOwnerAtBlk
  realize
  all_goals (
    rcases d with ⟨mctx, ⟨P, off⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_state_bpReadSlabOwnerProg, runClient_state_bpActCurProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hw1)

private def fbSlotBktRawProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (mctx, p) => do
    let dm ← bpDivModKProg (mctx, p)
    let tag ← bpReadSlabOwnerProg (mctx, (dm.1, 0))
    if tag = 1 then
      bpReadSlabOwnerProg (mctx, (dm.1, 1))
    else if tag = 2 then
      fbSlotBktTag2Prog (mctx, dm)
    else
      fbTailOwnerAtBlkProg (mctx, dm)

private theorem state_fbSlotBktRawProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbSlotBktRawProg x) = s := by
  rcases x with ⟨mctx, p⟩
  unfold fbSlotBktRawProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpDivModKProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg]
  split_ifs
  · exact clientState_bpReadSlabOwnerProg _ s
  · exact state_fbSlotBktTag2Prog _ s
  · exact state_fbTailOwnerAtBlkProg _ s

private theorem realizesBounded_fbSlotBktRaw :
    RealizesBounded .exact fbSlotBktRawProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (mctx, _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hdm := realizesBounded_bpDivModK
  have hrso := realizesBounded_bpReadSlabOwner
  have ht2 := realizesBounded_fbSlotBktTag2
  have hto := realizesBounded_fbTailOwnerAtBlk
  realize
  all_goals (
    rcases d with ⟨mctx, p⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    have h12K := hmv.twelve_K_le
    have h2_w : 2 < 2 ^ w := lt_of_le_of_lt (by omega) hnc_w
    try simp only [runClient_state_bpDivModKProg, runClient_state_bpReadSlabOwnerProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | omega)

private def fbFillTailOwnerWriteProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((mctx, p), t) => do
    let b ← fbSlotBktRawProg (mctx, p)
    bpWriteTailDirRawProg ((mctx, t), b)
    pure (t + 1)

private theorem frontier_fbFillTailOwnerWriteProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbFillTailOwnerWriteProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, p⟩, t⟩
  unfold fbFillTailOwnerWriteProg
  rw [StateTransitionSpec.clientState_bind, state_fbSlotBktRawProg,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
    frontier_bpWriteTailDirRawProg]

private theorem realizesBounded_fbFillTailOwnerWrite :
    RealizesBounded .exact fbFillTailOwnerWriteProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, _), t) s =>
        t < (BpMetaLayout.ofCtx mctx).nCap ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsb := realizesBounded_fbSlotBktRaw
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨mctx, p⟩, t⟩
    obtain ⟨ht_lt, hmv⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hs := state_fbSlotBktRawProg (mctx, p) s
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hs]
    first | exact hmv | omega)

private def fbFillTailOwnerStepProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((mctx, baseP), t) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if t < nCap ∧ baseP ≤ nCap - t then do
      let p ← pure (baseP + t)
      fbFillTailOwnerWriteProg ((mctx, p), t)
    else
      pure t

private theorem memoryCost_fbFillTailOwnerStep_pos
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (fbFillTailOwnerStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩, _⟩
  simp [fbFillTailOwnerStepProg, bpReadScalarProg]

private theorem frontier_fbFillTailOwnerStep (d : BpMetaCtx × ℕ) (t : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbFillTailOwnerStepProg (d, t))).frontier = s.frontier := by
  rcases d with ⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, baseP⟩
  unfold fbFillTailOwnerStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · simp only [pure_bind]; exact frontier_fbFillTailOwnerWriteProg _ s
  · rfl

private theorem realizesBounded_fbFillTailOwnerStep :
    RealizesBounded .exact fbFillTailOwnerStepProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hwr := realizesBounded_fbFillTailOwnerWrite
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, baseP⟩, t⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have ht_w : t < 2 ^ w := hwords 15
    dsimp only [BpMetaLayout.ofCtx] at *
    try simp only [runClient_state_bpReadScalarProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hw1 | omega)

private def fbFillTailOwnerLoopProg : ((BpMetaCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((d, t), fuel) => iterate fbFillTailOwnerStepProg d fuel t

private theorem realizesBounded_fbFillTailOwnerLoop :
    RealizesBounded .exact fbFillTailOwnerLoopProg
      (WordEncoding.encode (α := ((BpMetaCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((d, t), fuel) s =>
        iterationSafe fbFillTailOwnerStepProg
          (fun w' ((mctx, _), _) s' => (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier)
          w d fuel t s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BpMetaCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_fbFillTailOwnerStep
    memoryCost_fbFillTailOwnerStep_pos

/-- Write `fallbackMode := 1` at `metaBase + 2` (`¬ReadsWidth`). -/
private def fbWriteModeOneProg : BpMetaCtx → Memory.Prog Unit
  | ((((mb, obm), _), _), _) =>
    if 3 ≤ obm then Memory.write (mb + 2) 1 else pure ()

private theorem frontier_fbWriteModeOneProg (mctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbWriteModeOneProg mctx)).frontier = s.frontier := by
  rcases mctx with ⟨⟨⟨⟨mb, obm⟩, _⟩, _⟩, _⟩
  unfold fbWriteModeOneProg; dsimp only; split_ifs <;> rfl

private theorem realizesBounded_fbWriteModeOne :
    RealizesBounded .exact fbWriteModeOneProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w mctx s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
    have hv0 := h
    dsimp only [BpMetaLayout.ofCtx] at hv0
    have hw := hv0.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have ho32 := hv0.offBktMeta_ge
    have hd1 := hv0.offSlabDir_ge
    have hd2 := hv0.offTailDir_ge
    have hd3 := hv0.offSlabOwner_ge
    have hd4 := hv0.offTailOwner_ge
    have hfr := hv0.frontier_ge
    have hfr_w := hmem.1
    dsimp only [Fits] at *
    first | exact hw1 | omega)

private def fbEnterFinishBodyProg : (BpMetaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, sPure), (baseP, tailLen)) => do
    let z0 ← pure 0
    let _ ← fbFillTailOwnerLoopProg ((((mctx, baseP), z0)), tailLen)
    bpWriteScalarProg ((mctx, 10), sPure)
    fbWriteModeOneProg mctx

private theorem frontier_fbEnterFinishBodyProg
    (x : (BpMetaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbEnterFinishBodyProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, sPure⟩, ⟨baseP, tailLen⟩⟩
  unfold fbEnterFinishBodyProg; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    frontier_fbWriteModeOneProg, frontier_bpWriteScalarProg]
  exact (iterationSafe_of_frontier fbFillTailOwnerStepProg
    (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbFillTailOwnerStep d' a' st)
    (d := (mctx, baseP)) (s := s) trivial tailLen 0).2

private theorem realizesBounded_fbEnterFinishBody :
    RealizesBounded .exact fbEnterFinishBodyProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hfl := realizesBounded_fbFillTailOwnerLoop
  have hws := realizesBounded_bpWriteScalar
  have hwm := realizesBounded_fbWriteModeOne
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, sPure⟩, ⟨baseP, tailLen⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hfr_fl := (iterationSafe_of_frontier fbFillTailOwnerStepProg
      (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbFillTailOwnerStep d' a' st)
      (d := (mctx, baseP)) (s := s) trivial tailLen 0).2
    set s_fl := ((Memory.spec 0).runClient s
      (fbFillTailOwnerLoopProg ((((mctx, baseP), 0)), tailLen))).2.1
    have hfr_ws := runClient_frontier_bpWriteScalarProg ((mctx, 10), sPure) s_fl
    dsimp only [mctx, s_fl] at hfr_fl hfr_ws ⊢
    try unfold fbFillTailOwnerLoopProg at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact h10_w | (
      exact (iterationSafe_of_frontier fbFillTailOwnerStepProg
        (fun w' (d' : BpMetaCtx × ℕ) fr' => (BpMetaLayout.ofCtx d'.1).Valid w' fr')
        (fun d' a' st _ => frontier_fbFillTailOwnerStep d' a' st)
        (d := (mctx, baseP)) (s := s) hmv tailLen 0).1) | (
      try rw [hfr_ws]
      rw [hfr_fl]; exact hmv))

private def fbEnterFinishProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((mctx, nSide), sPure) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if nSide ≤ nCap ∧ sPure ≤ nCap / k then do
      let baseP ← pure (sPure * k)
      if baseP ≤ nSide then do
        let tailLen ← pure (nSide - baseP)
        fbEnterFinishBodyProg ((mctx, sPure), (baseP, tailLen))
      else pure ()
    else pure ()

private theorem frontier_fbEnterFinishProg (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbEnterFinishProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, nSide⟩, sPure⟩
  unfold fbEnterFinishProg; dsimp only
  split_ifs
  · simp only [pure_bind]
    split_ifs
    · exact frontier_fbEnterFinishBodyProg _ s
    · rfl
  · rfl

private theorem realizesBounded_fbEnterFinish :
    RealizesBounded .exact fbEnterFinishProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hbd := realizesBounded_fbEnterFinishBody
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, nSide⟩, sPure⟩
    have hmv := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at *
    try dsimp only [Fits] at *
    first | exact hmv | (
      have hmul : sPure * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      omega) | omega)

private def fbRunCompactPureProg : BlockPoolCtx × ℕ → Memory.Prog ℕ
  | (bpctx, bf) => do
    let z0 ← pure 0
    let ps ← fbCompactPureLoopProg ((((bpctx, bf), (z0, z0))), bf)
    pure ps.2

private theorem frontier_fbRunCompactPureProg
    (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbRunCompactPureProg x)).frontier = s.frontier := by
  rcases x with ⟨bpctx, bf⟩
  unfold fbRunCompactPureProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  exact (iterationSafe_of_frontier fbCompactPureStepProg
    (fun _ d' _ => 0 < (SlotIoLayout.ofCtx d'.1.2).pgL.w) (w := 0)
    (fun d' a' st hw' => frontier_fbCompactPureStep d' a' st hw')
    (d := (bpctx, bf)) (s := s) hw bf (0, 0)).2

private theorem realizesBounded_fbRunCompactPure :
    RealizesBounded .exact fbRunCompactPureProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hcl := realizesBounded_fbCompactPureLoop
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, bf⟩
    obtain ⟨hmv, hiov⟩ := h
    try dsimp only [Fits] at *
    exact (iterationSafe_of_frontier fbCompactPureStepProg
      (fun w' (d' : BlockPoolCtx × ℕ) fr' =>
        (BpMetaLayout.ofCtx d'.1.1).Valid w' fr' ∧
        (SlotIoLayout.ofCtx d'.1.2).Valid w' fr')
      (fun d' a' st hd' => frontier_fbCompactPureStep d' a' st hd'.2.w_pos)
      (d := ((mctx, ioctx), bf)) (s := s) ⟨hmv, hiov⟩ bf (0, 0)).1)

private def fbCompactAndFinishAtProg : (BlockPoolCtx × ℕ) × ℕ → Memory.Prog Unit
  | (((mctx, ioctx), nSide), bf) => do
    let sPure ← fbRunCompactPureProg ((mctx, ioctx), bf)
    fbEnterFinishProg ((mctx, nSide), sPure)

private theorem frontier_fbCompactAndFinishAtProg
    (x : (BlockPoolCtx × ℕ) × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbCompactAndFinishAtProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨mctx, ioctx⟩, nSide⟩, bf⟩
  unfold fbCompactAndFinishAtProg
  rw [StateTransitionSpec.clientState_bind, frontier_fbEnterFinishProg]
  exact frontier_fbRunCompactPureProg ((mctx, ioctx), bf) s hw

private theorem realizesBounded_fbCompactAndFinishAt :
    RealizesBounded .exact fbCompactAndFinishAtProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrc := realizesBounded_fbRunCompactPure
  have hfin := realizesBounded_fbEnterFinish
  realize
  all_goals (
    rcases d with ⟨⟨⟨mctx, ioctx⟩, nSide⟩, bf⟩
    obtain ⟨hmv, hiov⟩ := h
    have hfr := frontier_fbRunCompactPureProg ((mctx, ioctx), bf) s hiov.w_pos
    dsimp only [StateTransitionSpec.clientState] at hfr
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfr]
    first | exact hmv | exact hiov)

private def fbEnterCompactAndFinishProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), nSide) => do
    let dm ← bpDivModKProg (mctx, nSide)
    fbCompactAndFinishAtProg (((mctx, ioctx), nSide), dm.1)

private theorem frontier_fbEnterCompactAndFinishProg
    (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbEnterCompactAndFinishProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, nSide⟩
  unfold fbEnterCompactAndFinishProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpDivModKProg]
  exact frontier_fbCompactAndFinishAtProg _ s hw

private theorem realizesBounded_fbEnterCompactAndFinish :
    RealizesBounded .exact fbEnterCompactAndFinishProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hdm := realizesBounded_bpDivModK
  have hcfa := realizesBounded_fbCompactAndFinishAt
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, nSide⟩
    obtain ⟨hmv, hiov⟩ := h
    try simp only [runClient_state_bpDivModKProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov)

/-- Deterministically transition in-place from any `CoreValid` `BlockPoolState` into `FallbackState`
(`fallbackMode := 1` at `metaBase + 2`, `1 · OPT` peak space, zero seed resampling, `¬ReadsWidth`).
-/
def enterFallbackProg : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    fbUndoTopSwapProg (mctx, ioctx)
    let nSide ← bpReadScalarProg (mctx, 1)
    fbEnterCompactAndFinishProg ((mctx, ioctx), nSide)

theorem frontier_enterFallbackProg (ctx : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx ctx.2).pgL.w) :
    ((Memory.spec 0).clientState s (enterFallbackProg ctx)).frontier = s.frontier := by
  rcases ctx with ⟨mctx, ioctx⟩
  unfold enterFallbackProg
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    clientState_bpReadScalarProg, frontier_fbEnterCompactAndFinishProg _ _ hw]
  exact frontier_fbUndoTopSwapProg (mctx, ioctx) s hw

theorem realizesBounded_enterFallback :
    RealizesBounded .exact enterFallbackProg
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hun := realizesBounded_fbUndoTopSwap
  have hrs := realizesBounded_bpReadScalar
  have hcf := realizesBounded_fbEnterCompactAndFinish
  realize
  all_goals (
    rcases d with ⟨mctx, ioctx⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hfr_un := frontier_fbUndoTopSwapProg (mctx, ioctx) s hiov.w_pos
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfr_un]
    first | exact hmv | exact hiov | exact hw1)

private theorem set1_swap_eq_comp_swapIdx (f : ℕ → ℕ) (b₁ b₂ x : ℕ) :
    BlockPoolState.set1 (BlockPoolState.set1 f b₁ (f b₂)) b₂ (f b₁) x =
      f (swapIdx b₁ b₂ x) := by
  unfold swapIdx
  by_cases h2 : x = b₂
  · subst h2; rw [BlockPoolState.set1_self]
    by_cases h12 : x = b₁
    · subst h12; rw [ite_eq_left rfl]
    · rw [ite_eq_right h12, ite_eq_left rfl]
  · rw [BlockPoolState.set1_of_ne _ _ _ _ h2]
    by_cases h1 : x = b₁
    · subst h1; rw [BlockPoolState.set1_self, ite_eq_left rfl]
    · rw [BlockPoolState.set1_of_ne _ _ _ _ h1, ite_eq_right h1, ite_eq_right h2]

private theorem coreValid_slabMeta_le_nCap {mp : BpMetaLayout} {w fr : ℕ}
    {bp : BlockPoolState}
    (hmv : mp.Valid w fr) (hcv : bp.CoreValid)
    (hM : bp.M = mp.M) (_hK : bp.K = mp.K) (hms : bp.maxSlabs = mp.maxSlabs)
    {Q : ℕ} (hQ : Q < bp.B_full) :
    bp.blkTag Q ≤ mp.nCap ∧ bp.blkMeta1 Q ≤ mp.nCap ∧ bp.blkMeta2 Q ≤ mp.nCap := by
  have htag3 := hcv.blkTag_lt Q hQ
  have h12K := hmv.twelve_K_le
  have hK64 := hmv.K_ge
  have h16M := hmv.sixteen_M_le
  have hmsK := hmv.maxSlabs_K_le
  have htag_nc : bp.blkTag Q ≤ mp.nCap := by omega
  rcases (by omega : bp.blkTag Q = 0 ∨ bp.blkTag Q = 1 ∨ bp.blkTag Q = 2) with ht0 | ht1 | ht2
  · obtain ⟨hm1_lt, _⟩ := hcv.unres_bwd Q hQ ht0
    have hul_lt := (hcv.tail_block_card_lt).2
    obtain ⟨hm2_lt, _⟩ := hcv.tb_fwd Q hQ.le (Or.inl ht0)
    have htb_max := hcv.tbHighWater_le_max
    rw [hM] at hul_lt htb_max
    exact ⟨htag_nc, by omega, by omega⟩
  · obtain ⟨hb, hvp, _⟩ := hcv.slab_bwd Q hQ ht1
    have hq_ms := (hcv.bkt_bounds _ hb).1
    rw [hM] at hb; rw [hms] at hq_ms
    have hms_nc : mp.maxSlabs ≤ mp.nCap :=
      (Nat.le_mul_of_pos_right _ (by omega : 0 < mp.K)).trans ((Nat.le_add_right _ _).trans hmsK)
    exact ⟨htag_nc, by omega, (hvp.le.trans hq_ms).trans hms_nc⟩
  · obtain ⟨hb, _, _⟩ := hcv.act_bwd Q hQ ht2
    obtain ⟨hm2_lt, _⟩ := hcv.tb_fwd Q hQ.le (Or.inr ht2)
    have htb_max := hcv.tbHighWater_le_max
    rw [hM] at hb htb_max
    exact ⟨htag_nc, by omega, by omega⟩

private theorem fbSwapSlabLaneProg_spec {mp : BpMetaLayout} {w b₁ b₂ lane : ℕ} {s : Memory.State}
    (hmv : mp.Valid w s.frontier)
    (hb₁ : b₁ < mp.maxBlocks) (hb₂ : b₂ < mp.maxBlocks) (hlane : lane < 3)
    (hv₁ : (if lane = 0 then (extractBlockPool mp s.mem).blkTag b₁
            else if lane = 1 then (extractBlockPool mp s.mem).blkMeta1 b₁
            else (extractBlockPool mp s.mem).blkMeta2 b₁) ≤ mp.nCap)
    (hv₂ : (if lane = 0 then (extractBlockPool mp s.mem).blkTag b₂
            else if lane = 1 then (extractBlockPool mp s.mem).blkMeta1 b₂
            else (extractBlockPool mp s.mem).blkMeta2 b₂) ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (fbSwapSlabLaneProg ((mp.toCtx, (b₁, b₂)), lane))
    s'.frontier = s.frontier ∧
    (∀ addr, ¬mp.OwnsMetaAddr addr → s'.mem addr = s.mem addr) ∧
    extractBlockPool mp s'.mem =
      if lane = 0 then { bp with blkTag := fun x => bp.blkTag (swapIdx b₁ b₂ x) }
      else if lane = 1 then { bp with blkMeta1 := fun x => bp.blkMeta1 (swapIdx b₁ b₂ x) }
      else { bp with blkMeta2 := fun x => bp.blkMeta2 (swapIdx b₁ b₂ x) } := by
  dsimp only
  set bp := extractBlockPool mp s.mem
  have hoso_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offSlabOwner := by
    have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; have := hmv.offSlabOwner_ge; omega
  rcases (by omega : lane = 0 ∨ lane = 1 ∨ lane = 2) with rfl | rfl | rfl
  · simp only [↓reduceIte] at hv₁ hv₂ ⊢
    have hr : (Memory.spec 0).clientResult s
        (fbReadSlabLanePairProg ((mp.toCtx, (b₁, b₂)), 0)) = (bp.blkTag b₁, bp.blkTag b₂) := by
      unfold fbReadSlabLanePairProg
      rw [prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_tag, prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_tag, prog_clientResult_pure]
    unfold fbSwapSlabLaneProg
    rw [StateTransitionSpec.clientState_bind, state_fbReadSlabLanePairProg, hr]
    unfold fbWriteSlabLanePairProg
    rw [StateTransitionSpec.clientState_bind]
    set s₁ :=
      (Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (b₁, 0)), bp.blkTag b₂))
    have hwf₁ := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge b₁ 0 (bp.blkTag b₂)
    have hwf₂ := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge b₂ 0 (bp.blkTag b₁)
    have hbp₁ := extractBlockPool_writeSlabOwner (P := b₁) (lane := 0) hmv hb₁ (by decide) hv₂
      (s := s)
    dsimp only at hbp₁; rw [ite_eq_left rfl] at hbp₁
    have hbp₂ := extractBlockPool_writeSlabOwner (P := b₂) (lane := 0)
      ((hwf₁.1.frontier_eq s).symm ▸ hmv) hb₂ (by decide) hv₁ (s := s₁)
    dsimp only at hbp₂; rw [ite_eq_left rfl, hbp₁] at hbp₂
    refine ⟨(hwf₂.1.frontier_eq s₁).trans (hwf₁.1.frontier_eq s),
      fun a ha => (hwf₂.1.mem_outside s₁ a ha).trans (hwf₁.1.mem_outside s a ha), ?_⟩
    rw [hbp₂]
    congr 1; ext x; exact set1_swap_eq_comp_swapIdx bp.blkTag b₁ b₂ x
  · simp only [Nat.one_ne_zero, ↓reduceIte] at hv₁ hv₂ ⊢
    have hr : (Memory.spec 0).clientResult s
        (fbReadSlabLanePairProg ((mp.toCtx, (b₁, b₂)), 1)) = (bp.blkMeta1 b₁, bp.blkMeta1 b₂) := by
      unfold fbReadSlabLanePairProg
      rw [prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m1, prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m1, prog_clientResult_pure]
    unfold fbSwapSlabLaneProg
    rw [StateTransitionSpec.clientState_bind, state_fbReadSlabLanePairProg, hr]
    unfold fbWriteSlabLanePairProg
    rw [StateTransitionSpec.clientState_bind]
    set s₁ :=
      (Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (b₁, 1)), bp.blkMeta1 b₂))
    have hwf₁ := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge b₁ 1 (bp.blkMeta1 b₂)
    have hwf₂ := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge b₂ 1 (bp.blkMeta1 b₁)
    have hbp₁ := extractBlockPool_writeSlabOwner (P := b₁) (lane := 1) hmv hb₁ (by decide) hv₂
      (s := s)
    dsimp only at hbp₁; rw [ite_eq_right Nat.one_ne_zero, ite_eq_left rfl] at hbp₁
    have hbp₂ := extractBlockPool_writeSlabOwner (P := b₂) (lane := 1)
      ((hwf₁.1.frontier_eq s).symm ▸ hmv) hb₂ (by decide) hv₁ (s := s₁)
    dsimp only at hbp₂; rw [ite_eq_right Nat.one_ne_zero, ite_eq_left rfl, hbp₁] at hbp₂
    refine ⟨(hwf₂.1.frontier_eq s₁).trans (hwf₁.1.frontier_eq s),
      fun a ha => (hwf₂.1.mem_outside s₁ a ha).trans (hwf₁.1.mem_outside s a ha), ?_⟩
    rw [hbp₂]
    congr 1; ext x; exact set1_swap_eq_comp_swapIdx bp.blkMeta1 b₁ b₂ x
  · simp only [OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ↓reduceIte] at hv₁ hv₂ ⊢
    have hr : (Memory.spec 0).clientResult s
        (fbReadSlabLanePairProg ((mp.toCtx, (b₁, b₂)), 2)) = (bp.blkMeta2 b₁, bp.blkMeta2 b₂) := by
      unfold fbReadSlabLanePairProg
      rw [prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m2, prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m2, prog_clientResult_pure]
    unfold fbSwapSlabLaneProg
    rw [StateTransitionSpec.clientState_bind, state_fbReadSlabLanePairProg, hr]
    unfold fbWriteSlabLanePairProg
    rw [StateTransitionSpec.clientState_bind]
    set s₁ :=
      (Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (b₁, 2)), bp.blkMeta2 b₂))
    have hwf₁ := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge b₁ 2 (bp.blkMeta2 b₂)
    have hwf₂ := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge b₂ 2 (bp.blkMeta2 b₁)
    have hbp₁ := extractBlockPool_writeSlabOwner (P := b₁) (lane := 2) hmv hb₁ (by decide) hv₂
      (s := s)
    dsimp only at hbp₁
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl] at hbp₁
    have hbp₂ := extractBlockPool_writeSlabOwner (P := b₂) (lane := 2)
      ((hwf₁.1.frontier_eq s).symm ▸ hmv) hb₂ (by decide) hv₁ (s := s₁)
    dsimp only at hbp₂
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, hbp₁] at hbp₂
    refine ⟨(hwf₂.1.frontier_eq s₁).trans (hwf₁.1.frontier_eq s),
      fun a ha => (hwf₂.1.mem_outside s₁ a ha).trans (hwf₁.1.mem_outside s a ha), ?_⟩
    rw [hbp₂]
    congr 1; ext x; exact set1_swap_eq_comp_swapIdx bp.blkMeta2 b₁ b₂ x

private theorem swapRangeIdx_blk_div_mod {b₁ b₂ K p : ℕ} (hK : 0 < K) (hle : b₁ ≤ b₂) :
    swapRangeIdx (b₁ * K) (b₂ * K) K p / K = swapIdx b₁ b₂ (p / K) ∧
    swapRangeIdx (b₁ * K) (b₂ * K) K p % K = p % K := by
  have div_mod_add : ∀ B off, off < K →
      (B * K + off) / K = B ∧ (B * K + off) % K = off := fun B off hoff =>
    ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add],
     by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]⟩
  unfold swapRangeIdx swapIdx
  by_cases h1 : b₁ * K ≤ p ∧ p < b₁ * K + K
  · rw [ite_eq_left h1]
    have hoff : p - b₁ * K < K := by omega
    have hp_eq : p = b₁ * K + (p - b₁ * K) := by omega
    obtain ⟨hd1, hm1⟩ := div_mod_add b₁ (p - b₁ * K) hoff
    obtain ⟨hd2, hm2⟩ := div_mod_add b₂ (p - b₁ * K) hoff
    rw [← hp_eq] at hd1 hm1
    rw [hd1, hm1, hd2, hm2, ite_eq_left rfl]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right h1]
    by_cases h2 : b₂ * K ≤ p ∧ p < b₂ * K + K
    · rw [ite_eq_left h2]
      have hne12 : b₂ ≠ b₁ := by rintro rfl; exact h1 h2
      have hoff : p - b₂ * K < K := by omega
      have hp_eq : p = b₂ * K + (p - b₂ * K) := by omega
      obtain ⟨hd2, hm2⟩ := div_mod_add b₂ (p - b₂ * K) hoff
      obtain ⟨hd1, hm1⟩ := div_mod_add b₁ (p - b₂ * K) hoff
      rw [← hp_eq] at hd2 hm2
      rw [hd2, hm2, hd1, hm1, ite_eq_right hne12, ite_eq_left rfl]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right h2]
      have hp_dm := Nat.div_add_mod p K
      have hm_lt := Nat.mod_lt p hK
      rw [Nat.mul_comm] at hp_dm
      have hne1 : p / K ≠ b₁ := by intro he; rw [he] at hp_dm; exact h1 ⟨by omega, by omega⟩
      have hne2 : p / K ≠ b₂ := by intro he; rw [he] at hp_dm; exact h2 ⟨by omega, by omega⟩
      rw [ite_eq_right hne1, ite_eq_right hne2]
      exact ⟨rfl, rfl⟩

private theorem fbSwapSlabMeta3Prog_spec {mp : BpMetaLayout} {w b₁ b₂ : ℕ}
    {bp₁ : BlockPoolState} {π : ℕ → ℕ} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hcv₁ : bp₁.CoreValid)
    (hM₁ : bp₁.M = mp.M) (hK₁ : bp₁.K = mp.K) (hms₁ : bp₁.maxSlabs = mp.maxSlabs)
    (hb₁_mb : b₁ < mp.maxBlocks) (hb₂_mb : b₂ < mp.maxBlocks)
    (hπ₁ : π b₁ < bp₁.B_full) (hπ₂ : π b₂ < bp₁.B_full)
    (htag : (extractBlockPool mp s.mem).blkTag = fun B => bp₁.blkTag (π B))
    (hm1 : (extractBlockPool mp s.mem).blkMeta1 = fun B => bp₁.blkMeta1 (π B))
    (hm2 : (extractBlockPool mp s.mem).blkMeta2 = fun B => bp₁.blkMeta2 (π B)) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (fbSwapSlabMeta3Prog (mp.toCtx, (b₁, b₂)))
    let π' := fun B => π (swapIdx b₁ b₂ B)
    s'.frontier = s.frontier ∧
    (∀ addr, ¬mp.OwnsMetaAddr addr → s'.mem addr = s.mem addr) ∧
    extractBlockPool mp s'.mem =
      { bp with
        blkTag := fun B => bp₁.blkTag (π' B)
        blkMeta1 := fun B => bp₁.blkMeta1 (π' B)
        blkMeta2 := fun B => bp₁.blkMeta2 (π' B) } := by
  dsimp only
  obtain ⟨hv1_0, hv1_1, hv1_2⟩ := coreValid_slabMeta_le_nCap hmv hcv₁ hM₁ hK₁ hms₁ hπ₁
  obtain ⟨hv2_0, hv2_1, hv2_2⟩ := coreValid_slabMeta_le_nCap hmv hcv₁ hM₁ hK₁ hms₁ hπ₂
  unfold fbSwapSlabMeta3Prog
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  obtain ⟨hfr0, hout0, hbp0⟩ := fbSwapSlabLaneProg_spec (lane := 0) hmv hb₁_mb hb₂_mb (by decide)
    (by simp only [↓reduceIte, htag]; exact hv1_0)
    (by simp only [↓reduceIte, htag]; exact hv2_0)
  set s₀ := (Memory.spec 0).clientState s (fbSwapSlabLaneProg ((mp.toCtx, (b₁, b₂)), 0))
  rw [ite_eq_left rfl] at hbp0
  obtain ⟨hfr1, hout1, hbp1⟩ := fbSwapSlabLaneProg_spec (lane := 1) (s := s₀)
    (hfr0.symm ▸ hmv) hb₁_mb hb₂_mb (by decide)
    (by simp only [Nat.one_ne_zero, ↓reduceIte, hbp0, hm1]; exact hv1_1)
    (by simp only [Nat.one_ne_zero, ↓reduceIte, hbp0, hm1]; exact hv2_1)
  set s₁ := (Memory.spec 0).clientState s₀ (fbSwapSlabLaneProg ((mp.toCtx, (b₁, b₂)), 1))
  rw [ite_eq_right Nat.one_ne_zero, ite_eq_left rfl] at hbp1
  obtain ⟨hfr2, hout2, hbp2⟩ := fbSwapSlabLaneProg_spec (lane := 2) (s := s₁)
    ((hfr1.trans hfr0).symm ▸ hmv) hb₁_mb hb₂_mb (by decide)
    (by simp only [OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ↓reduceIte, hbp1, hbp0, hm2]; exact hv1_2)
    (by simp only [OfNat.ofNat_ne_zero, Nat.reduceEqDiff, ↓reduceIte, hbp1, hbp0, hm2]; exact hv2_2)
  rw [ite_eq_right (by decide), ite_eq_right (by decide)] at hbp2
  refine ⟨hfr2.trans (hfr1.trans hfr0),
    fun a ha => (hout2 a ha).trans ((hout1 a ha).trans (hout0 a ha)), ?_⟩
  rw [hbp2, hbp1, hbp0, htag, hm1, hm2]

private theorem fbCompactPureLoop_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {w slack : ℕ} {bp₁ : BlockPoolState} {s₁ : Memory.State}
    (hmv : mp.Valid w s₁.frontier) (hiov : io.Valid io.pgL.w s₁.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hbp₁_def : extractBlockPool mp s₁.mem = bp₁)
    (hcv₁ : bp₁.CoreValid) (hns_le : bp₁.nSide ≤ mp.nCap)
    (_hio₁ : io.StateInv bp₁.nSide slack s₁.mem) :
    ∀ fuel P sPure (π π_inv : ℕ → ℕ) (st : Memory.State),
      st.frontier = s₁.frontier →
      P + fuel = bp₁.B_full →
      sPure ≤ P →
      (∀ x, π_inv (π x) = x) →
      (∀ y, π (π_inv y) = y) →
      (∀ B < bp₁.B_full, π B < bp₁.B_full) →
      (∀ B, bp₁.B_full ≤ B → π B = B) →
      (∀ B, P ≤ B → π B = B) →
      (∀ B < sPure, bp₁.blkTag (π B) = 1) →
      (∀ B, sPure ≤ B → B < P → bp₁.blkTag (π B) ≠ 1) →
      (extractBlockPool mp st.mem).nSide = bp₁.nSide →
      (extractBlockPool mp st.mem).actCode = bp₁.actCode →
      (extractBlockPool mp st.mem).tailOwnerBkt = bp₁.tailOwnerBkt →
      (extractBlockPool mp st.mem).blkTag = (fun B => bp₁.blkTag (π B)) →
      (extractBlockPool mp st.mem).blkMeta1 = (fun B => bp₁.blkMeta1 (π B)) →
      (extractBlockPool mp st.mem).blkMeta2 = (fun B => bp₁.blkMeta2 (π B)) →
      io.StateInv bp₁.nSide slack st.mem →
      (∀ p < bp₁.nSide,
        slotIoPairAt io st.mem p = slotIoPairAt io s₁.mem (π (p / mp.K) * mp.K + p % mp.K)) →
      (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → st.mem addr = s₁.mem addr) →
      (io.usePaged ≠ 0 →
        extractPageUnperm io.pgL st.mem = extractPageUnperm io.pgL s₁.mem ∧
        ∀ idx < (extractPagePair io.pgL s₁.mem).virtLen io.partner.side,
          slotIoPairAt io.partner st.mem idx = slotIoPairAt io.partner s₁.mem idx) →
      let st' := (Memory.spec 0).clientState st
        (iterate fbCompactPureStepProg ((mp.toCtx, io.toCtx), bp₁.B_full) fuel (P, sPure))
      let res := (Memory.spec 0).clientResult st
        (iterate fbCompactPureStepProg ((mp.toCtx, io.toCtx), bp₁.B_full) fuel (P, sPure))
      ∃ (π' π_inv' : ℕ → ℕ),
        res.1 = bp₁.B_full ∧
        res.2 ≤ bp₁.B_full ∧
        st'.frontier = s₁.frontier ∧
        (∀ x, π_inv' (π' x) = x) ∧
        (∀ y, π' (π_inv' y) = y) ∧
        (∀ B < bp₁.B_full, π' B < bp₁.B_full) ∧
        (∀ B, bp₁.B_full ≤ B → π' B = B) ∧
        (∀ B < res.2, bp₁.blkTag (π' B) = 1) ∧
        (∀ B, res.2 ≤ B → B < bp₁.B_full → bp₁.blkTag (π' B) ≠ 1) ∧
        (extractBlockPool mp st'.mem).nSide = bp₁.nSide ∧
        (extractBlockPool mp st'.mem).actCode = bp₁.actCode ∧
        (extractBlockPool mp st'.mem).tailOwnerBkt = bp₁.tailOwnerBkt ∧
        (extractBlockPool mp st'.mem).blkTag = (fun B => bp₁.blkTag (π' B)) ∧
        (extractBlockPool mp st'.mem).blkMeta1 = (fun B => bp₁.blkMeta1 (π' B)) ∧
        (extractBlockPool mp st'.mem).blkMeta2 = (fun B => bp₁.blkMeta2 (π' B)) ∧
        io.StateInv bp₁.nSide slack st'.mem ∧
        (∀ p < bp₁.nSide,
          slotIoPairAt io st'.mem p = slotIoPairAt io s₁.mem (π' (p / mp.K) * mp.K + p % mp.K)) ∧
        (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → st'.mem addr = s₁.mem addr) ∧
        (io.usePaged ≠ 0 →
          extractPageUnperm io.pgL st'.mem = extractPageUnperm io.pgL s₁.mem ∧
          ∀ idx < (extractPagePair io.pgL s₁.mem).virtLen io.partner.side,
            slotIoPairAt io.partner st'.mem idx = slotIoPairAt io.partner s₁.mem idx) := by
  have hM₁ : bp₁.M = mp.M := by rw [← hbp₁_def]; rfl
  have hK₁ : bp₁.K = mp.K := by rw [← hbp₁_def]; rfl
  have hms₁ : bp₁.maxSlabs = mp.maxSlabs := by rw [← hbp₁_def]; rfl
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  have h16le := hmv.sixteen_MK_le_maxTail
  have hmt : mp.M * mp.K ≤ mp.maxTail := by
    rw [Nat.mul_assoc] at h16le
    exact (Nat.mul_le_mul_left_iff (by decide : 0 < 16)).mp h16le
  have hBf_mul : bp₁.B_full * mp.K ≤ bp₁.nSide := by
    have := hcv₁.nSide_eq; rw [hK₁] at this; omega
  have hBf_div : bp₁.B_full ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hBf_mul.trans hns_le)
  have hBf_mb : bp₁.B_full < mp.maxBlocks := by have := hmv.div_K_add_two_le; omega
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
  intro fuel; induction fuel with
  | zero =>
    intro P sPure π π_inv st hfr hsum hsp_le hl hr hlt hfix_hi _ hlo hmid
      hns hac htob htag hm1 hm2 hio harr hout hpg
    have hP : P = bp₁.B_full := by omega
    subst hP
    exact ⟨π, π_inv, rfl, hsp_le, hfr, hl, hr, hlt, hfix_hi, hlo, hmid,
      hns, hac, htob, htag, hm1, hm2, hio, harr, hout, hpg⟩
  | succ f ih =>
    intro P sPure π π_inv st hfr hsum hsp_le hl hr hlt hfix_hi hfix_P hlo hmid
      hns hac htob htag hm1 hm2 hio harr hout hpg
    have hP_lt : P < bp₁.B_full := by omega
    have hP_nc : P < mp.nCap := by
      have : (P + 1) * mp.K ≤ bp₁.B_full * mp.K := Nat.mul_le_mul_right _ hP_lt
      have h1 : P + 1 ≤ (P + 1) * mp.K := Nat.le_mul_of_pos_right _ hK
      omega
    have hπP : π P = P := hfix_P P le_rfl
    have hr_tag : (Memory.spec 0).clientResult st (bpReadSlabOwnerProg (mp.toCtx, (P, 0))) =
        bp₁.blkTag P := by
      rw [clientResult_bpReadSlabOwner_tag, htag]; dsimp only; rw [hπP]
    by_cases ht1 : bp₁.blkTag P = 1
    · have hsp_div : sPure ≤ mp.nCap / mp.K := (hsp_le.trans hP_lt.le).trans hBf_div
      have hP_div : P ≤ mp.nCap / mp.K := hP_lt.le.trans hBf_div
      have hsp_mb : sPure < mp.maxBlocks := (lt_of_le_of_lt hsp_le hP_lt).trans hBf_mb
      have hP_mb : P < mp.maxBlocks := hP_lt.trans hBf_mb
      have hb1_ns : sPure * mp.K + mp.K ≤ bp₁.nSide := by
        have : (sPure + 1) * mp.K ≤ bp₁.B_full * mp.K :=
          Nat.mul_le_mul_right _ (lt_of_le_of_lt hsp_le hP_lt)
        rw [Nat.add_one_mul] at this; exact this.trans hBf_mul
      have hb2_ns : P * mp.K + mp.K ≤ bp₁.nSide := by
        have : (P + 1) * mp.K ≤ bp₁.B_full * mp.K := Nat.mul_le_mul_right _ hP_lt
        rw [Nat.add_one_mul] at this; exact this.trans hBf_mul
      have hdisj_sr : sPure * mp.K = P * mp.K ∨ sPure * mp.K + mp.K ≤ P * mp.K ∨
          P * mp.K + mp.K ≤ sPure * mp.K := by
        rcases eq_or_lt_of_le hsp_le with rfl | hlt_sp
        · exact Or.inl rfl
        · refine Or.inr (Or.inl ?_)
          have : (sPure + 1) * mp.K ≤ P * mp.K := Nat.mul_le_mul_right _ hlt_sp
          rwa [Nat.add_one_mul] at this
      obtain ⟨hfr_sr, hio_sr, harr_sr, hout_sr, hpg_sr⟩ :=
        fbSwapRangeProg_spec (hfr.symm ▸ hmv) (hfr.symm ▸ hiov) hio hns_le hb1_ns hb2_ns hdisj_sr
      set st_sr := (Memory.spec 0).clientState st
        (fbSwapRangeProg (((mp.toCtx, io.toCtx), (sPure * mp.K, P * mp.K)), mp.K))
      have hbp_sr : extractBlockPool mp st_sr.mem = extractBlockPool mp st.mem :=
        extractBlockPool_congr hmv.w_pos hmv.K_ge hmt
          (fun a hma => hout_sr a (fun hia => hdisj a hma hia))
      obtain ⟨hfr_sm, hout_sm, hbp_sm⟩ :=
        fbSwapSlabMeta3Prog_spec (s := st_sr) (bp₁ := bp₁) (π := π)
          ((hfr_sr.trans hfr).symm ▸ hmv) hcv₁ hM₁ hK₁ hms₁ hsp_mb hP_mb
          (hlt _ (lt_of_le_of_lt hsp_le hP_lt)) (hlt _ hP_lt)
          (by rw [hbp_sr]; exact htag) (by rw [hbp_sr]; exact hm1) (by rw [hbp_sr]; exact hm2)
      set st_nx := (Memory.spec 0).clientState st_sr (fbSwapSlabMeta3Prog (mp.toCtx, (sPure, P)))
      have hstep_st : (Memory.spec 0).clientState st
          (fbCompactPureStepProg (((mp.toCtx, io.toCtx), bp₁.B_full), (P, sPure))) = st_nx := by
        unfold fbCompactPureStepProg
        rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
        rw [hnc_eq, ite_eq_left ⟨hP_lt, hP_nc⟩, StateTransitionSpec.clientState_bind,
          clientState_bpReadSlabOwnerProg, hr_tag]
        unfold fbCompactPureHitProg; dsimp only
        rw [ite_eq_left ⟨ht1, hsp_le⟩, StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_pure]
        unfold fbCompactSwapBlkProg fbCompactSwapBlkBodyProg fbCompactDoRangeProg
        dsimp only
        rw [hnc_eq, hk_eq, ite_eq_left hsp_div, ite_eq_left hP_div,
          StateTransitionSpec.clientState_bind]
        simp only [pure_bind]; rfl
      have hstep_res : (Memory.spec 0).clientResult st
          (fbCompactPureStepProg (((mp.toCtx, io.toCtx), bp₁.B_full), (P, sPure))) =
          (P + 1, sPure + 1) := by
        unfold fbCompactPureStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg]; dsimp only
        rw [hnc_eq, ite_eq_left ⟨hP_lt, hP_nc⟩, prog_clientResult_bind,
          clientState_bpReadSlabOwnerProg, hr_tag]
        unfold fbCompactPureHitProg; dsimp only
        rw [ite_eq_left ⟨ht1, hsp_le⟩, prog_clientResult_bind, prog_clientResult_pure]
      set π' := fun B => π (swapIdx sPure P B)
      set π_inv' := fun Q => swapIdx sPure P (π_inv Q)
      have hio_out : ∀ addr, io.OwnsAddr addr → st_nx.mem addr = st_sr.mem addr := fun a hia =>
        hout_sm a (fun hma => hdisj a hma hia)
      obtain ⟨hio_nx, harr_nx⟩ := io.congr_of_outside hiov.w_pos hio_sr hio_out
      unfold iterate; dsimp only
      rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind, hstep_st, hstep_res]
      refine ih (P + 1) (sPure + 1) π' π_inv' st_nx (hfr_sm.trans (hfr_sr.trans hfr))
        (by omega) (Nat.succ_le_succ hsp_le)
        (fun x => by dsimp only [π', π_inv']; rw [hl, swapIdx_involutive])
        (fun y => by dsimp only [π', π_inv']; rw [swapIdx_involutive, hr])
        (fun B hB => hlt _ (swapIdx_lt (lt_of_le_of_lt hsp_le hP_lt) hP_lt hB))
        (fun B hB => by
          dsimp only [π']; unfold swapIdx
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact hfix_hi B hB)
        (fun B hB => by
          dsimp only [π']; unfold swapIdx
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact hfix_P B (by omega))
        (fun B hB => by
          dsimp only [π']
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hB) with rfl | hlt_sp
          · unfold swapIdx; rw [ite_eq_left rfl, hπP]; exact ht1
          · unfold swapIdx
            rw [ite_eq_right (ne_of_lt hlt_sp), ite_eq_right (by omega)]
            exact hlo B hlt_sp)
        (fun B hB1 hB2 => by
          dsimp only [π']
          have hB_le_P : B ≤ P := Nat.lt_succ_iff.mp hB2
          rcases eq_or_lt_of_le hB_le_P with rfl | hlt_P
          · unfold swapIdx
            rcases eq_or_lt_of_le hsp_le with hsp_eq | hsp_lt
            · omega
            · rw [ite_eq_right (ne_of_gt hsp_lt), ite_eq_left rfl]
              exact hmid sPure le_rfl hsp_lt
          · unfold swapIdx
            rw [ite_eq_right (by omega), ite_eq_right (ne_of_lt hlt_P)]
            exact hmid B (by omega) hlt_P)
        (by rw [hbp_sm, hbp_sr]; exact hns)
        (by rw [hbp_sm, hbp_sr]; exact hac)
        (by rw [hbp_sm, hbp_sr]; exact htob)
        (by rw [hbp_sm])
        (by rw [hbp_sm])
        (by rw [hbp_sm])
        hio_nx
        (fun p hp => by
          rw [harr_nx p hp, harr_sr p hp, harr _ (swapRangeIdx_lt hb1_ns hb2_ns hp)]
          obtain ⟨hd, hm⟩ := swapRangeIdx_blk_div_mod hK hsp_le (p := p)
          rw [hd, hm])
        (fun a ha => (hout_sm a (fun h => ha (Or.inl h))).trans
          ((hout_sr a (fun h => ha (Or.inr h))).trans (hout a ha)))
        (fun hnz => by
          obtain ⟨hu₀, hp₀⟩ := hpg hnz
          obtain ⟨hu_sr, hp_sr⟩ := hpg_sr hnz
          have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → st_nx.mem addr = st_sr.mem addr :=
            fun a ha => by apply hio_out a; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
          have hu_nx : extractPageUnperm io.pgL st_nx.mem = extractPageUnperm io.pgL st_sr.mem :=
            extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
          have hvl₀ : (extractPagePair io.pgL st.mem).virtLen io.partner.side =
              (extractPagePair io.pgL s₁.mem).virtLen io.partner.side :=
            congrArg (fun u => u.st.virtLen io.partner.side) hu₀
          have hvl_sr : (extractPagePair io.pgL st_sr.mem).virtLen io.partner.side =
              (extractPagePair io.pgL st.mem).virtLen io.partner.side :=
            congrArg (fun u => u.st.virtLen io.partner.side) hu_sr
          refine ⟨hu_nx.trans (hu_sr.trans hu₀), fun idx hidx => ?_⟩
          unfold SlotIoLayout.StateInv at hio_sr; rw [ite_eq_right hnz] at hio_sr
          have hidx_sr : idx < (extractPagePair io.pgL st_sr.mem).virtLen io.partner.side := by
            rwa [hvl_sr, hvl₀]
          have hp_lt_sr :
              (extractPageUnperm io.pgL st_sr.mem).toPhys io.partner.side idx < io.pgL.nCap :=
            (hio_sr.1.toPhys_lt hidx_sr).trans_le hio_sr.2.2.2.1
          have hp_nx : slotIoPairAt io.partner st_nx.mem idx =
              slotIoPairAt io.partner st_sr.mem idx := by
            unfold slotIoPairAt
            have hp_nz : io.partner.usePaged ≠ 0 := hnz
            rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_nx]
            exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt_sr
          exact hp_nx.trans ((hp_sr idx (hvl₀.symm ▸ hidx)).trans (hp₀ idx hidx)))
    · have hnot : ¬(bp₁.blkTag P = 1 ∧ sPure ≤ P) := fun h => ht1 h.1
      have hstep_st : (Memory.spec 0).clientState st
          (fbCompactPureStepProg (((mp.toCtx, io.toCtx), bp₁.B_full), (P, sPure))) = st := by
        unfold fbCompactPureStepProg
        rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
        rw [hnc_eq, ite_eq_left ⟨hP_lt, hP_nc⟩, StateTransitionSpec.clientState_bind,
          clientState_bpReadSlabOwnerProg, hr_tag]
        unfold fbCompactPureHitProg; dsimp only
        rw [ite_eq_right hnot, StateTransitionSpec.clientState_pure]
      have hstep_res : (Memory.spec 0).clientResult st
          (fbCompactPureStepProg (((mp.toCtx, io.toCtx), bp₁.B_full), (P, sPure))) =
          (P + 1, sPure) := by
        unfold fbCompactPureStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg]; dsimp only
        rw [hnc_eq, ite_eq_left ⟨hP_lt, hP_nc⟩, prog_clientResult_bind,
          clientState_bpReadSlabOwnerProg, hr_tag]
        unfold fbCompactPureHitProg; dsimp only
        rw [ite_eq_right hnot, prog_clientResult_pure]
      unfold iterate; dsimp only
      rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind, hstep_st, hstep_res]
      refine ih (P + 1) sPure π π_inv st hfr (by omega) (hsp_le.trans (Nat.le_succ P))
        hl hr hlt hfix_hi (fun B hB => hfix_P B (by omega)) hlo
        (fun B hB1 hB2 => ?_)
        hns hac htob htag hm1 hm2 hio harr hout hpg
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hB2) with rfl | hlt_P
      · rw [hπP]; exact ht1
      · exact hmid B hB1 hlt_P

private theorem compactPure_tail_le_six_MK {bp₁ : BlockPoolState} {sPure : ℕ}
    {π π_inv : ℕ → ℕ}
    (hcv₁ : bp₁.CoreValid)
    (hsp_le : sPure ≤ bp₁.B_full)
    (hl : ∀ x, π_inv (π x) = x)
    (hr : ∀ y, π (π_inv y) = y)
    (hlt : ∀ B < bp₁.B_full, π B < bp₁.B_full)
    (hfix_hi : ∀ B, bp₁.B_full ≤ B → π B = B)
    (hlo : ∀ B < sPure, bp₁.blkTag (π B) = 1)
    (hmid : ∀ B, sPure ≤ B → B < bp₁.B_full → bp₁.blkTag (π B) ≠ 1) :
    sPure * bp₁.K ≤ bp₁.nSide ∧ bp₁.nSide - sPure * bp₁.K < 6 * bp₁.M * bp₁.K := by
  have hns_eq := hcv₁.nSide_eq
  have hsp_mul : sPure * bp₁.K ≤ bp₁.nSide := by
    have : sPure * bp₁.K ≤ bp₁.B_full * bp₁.K := Nat.mul_le_mul_right _ hsp_le
    omega
  have hπ_inv_lt : ∀ Q < bp₁.B_full, π_inv Q < bp₁.B_full := fun Q hQ => by
    by_contra hge
    have hfix := hfix_hi (π_inv Q) (Nat.le_of_not_lt hge)
    rw [hr Q] at hfix
    omega
  set S02 := (Finset.range bp₁.B_full).filter (fun Q => bp₁.blkTag Q = 0 ∨ bp₁.blkTag Q = 2)
  have hcard_S02 : S02.card = bp₁.B_full - sPure := by
    symm
    have hbij := Finset.card_bij (s := Finset.range (bp₁.B_full - sPure)) (t := S02)
      (fun i _ => π (sPure + i))
      (fun i hi => by
        have hi_lt := mem_range.mp hi
        have hB_lt : sPure + i < bp₁.B_full := by omega
        have hne1 := hmid (sPure + i) (Nat.le_add_right _ _) hB_lt
        have ht3 := hcv₁.blkTag_lt _ (hlt _ hB_lt)
        exact mem_filter.mpr ⟨mem_range.mpr (hlt _ hB_lt), by omega⟩)
      (fun i₁ _ i₂ _ heq => by
        have := congrArg π_inv heq
        rw [hl, hl] at this
        omega)
      (fun Q hQ => by
        obtain ⟨hQ_r, hQ_02⟩ := mem_filter.mp hQ
        have hQ_lt := mem_range.mp hQ_r
        have hinv_lt := hπ_inv_lt Q hQ_lt
        have hge_sp : sPure ≤ π_inv Q := by
          by_contra hlt_sp
          have h1 := hlo (π_inv Q) (Nat.lt_of_not_le hlt_sp)
          rw [hr Q] at h1
          omega
        exact ⟨π_inv Q - sPure, mem_range.mpr (by omega), by
          rw [Nat.add_sub_of_le hge_sp, hr Q]⟩)
    simpa only [card_range] using hbij
  have hcard_plus1 := (hcv₁.tail_block_card_lt).1
  rw [Finset.range_add_one, Finset.filter_insert] at hcard_plus1
  simp only [hcv₁.blkTag_top, true_or, ↓reduceIte] at hcard_plus1
  have hnot_mem : bp₁.B_full ∉ S02 := by simp [S02]
  change (insert bp₁.B_full S02).card = _ at hcard_plus1
  rw [Finset.card_insert_of_notMem hnot_mem, hcard_S02] at hcard_plus1
  have hsub_eq : bp₁.B_full - sPure = bp₁.unresLen + bp₁.actBucketCount := by omega
  have hsum_r := hcv₁.sum_r_eq_tail_supply
  have hsum_lt : ∑ b ∈ Finset.range bp₁.M, bp₁.r b < bp₁.M * (6 * bp₁.K) := by
    have hne : (Finset.range bp₁.M).Nonempty := ⟨0, mem_range.mpr hcv₁.M_pos⟩
    calc ∑ b ∈ Finset.range bp₁.M, bp₁.r b
        < ∑ _b ∈ Finset.range bp₁.M, (6 * bp₁.K) :=
          Finset.sum_lt_sum_of_nonempty hne fun b hb => (hcv₁.bkt_bounds b (mem_range.mp hb)).2.1
      _ = bp₁.M * (6 * bp₁.K) := by rw [Finset.sum_const, card_range, smul_eq_mul]
  have htail_eq : bp₁.nSide - sPure * bp₁.K = (bp₁.B_full - sPure) * bp₁.K + bp₁.rem := by
    have hsp_bf : sPure * bp₁.K ≤ bp₁.B_full * bp₁.K := Nat.mul_le_mul_right _ hsp_le
    rw [Nat.sub_mul]
    omega
  rw [htail_eq, hsub_eq, ← hsum_r]
  refine ⟨hsp_mul, lt_of_lt_of_eq hsum_lt (by ring)⟩

private theorem fbSlotBktRawProg_spec {mp : BpMetaLayout}
    {bp₁ : BlockPoolState} {π : ℕ → ℕ} {p : ℕ} {s : Memory.State}
    (hcv₁ : bp₁.CoreValid) (hact0 : bp₁.topSwapAct = 0)
    (hM₁ : bp₁.M = mp.M) (hK₁ : bp₁.K = mp.K)
    (hlt : ∀ B < bp₁.B_full, π B < bp₁.B_full)
    (hfix_hi : ∀ B, bp₁.B_full ≤ B → π B = B)
    (hac : (extractBlockPool mp s.mem).actCode = bp₁.actCode)
    (htob : (extractBlockPool mp s.mem).tailOwnerBkt = bp₁.tailOwnerBkt)
    (htag : (extractBlockPool mp s.mem).blkTag = (fun B => bp₁.blkTag (π B)))
    (hm1 : (extractBlockPool mp s.mem).blkMeta1 = (fun B => bp₁.blkMeta1 (π B)))
    (hm2 : (extractBlockPool mp s.mem).blkMeta2 = (fun B => bp₁.blkMeta2 (π B)))
    (hp : p < bp₁.nSide) :
    let q := π (p / mp.K) * mp.K + p % mp.K
    q < bp₁.nSide ∧
    (Memory.spec 0).clientResult s (fbSlotBktRawProg (mp.toCtx, p)) = (bp₁.ownerOf q).1 ∧
    (bp₁.ownerOf q).1 < mp.M := by
  dsimp only
  have hK : 0 < mp.K := by rw [← hK₁]; exact hcv₁.K_pos
  have hoff : p % mp.K < mp.K := Nat.mod_lt p hK
  have hns_eq := hcv₁.nSide_eq
  rw [hK₁] at hns_eq
  set B := p / mp.K
  set off := p % mp.K
  set Q := π B
  have hQ_dom : Q < bp₁.B_full ∨ (Q = bp₁.B_full ∧ off < bp₁.rem) := by
    by_cases hB : B < bp₁.B_full
    · exact Or.inl (hlt B hB)
    · have hrem_lt : bp₁.rem < mp.K := by
        unfold BlockPoolState.rem; rw [hK₁]; exact Nat.mod_lt _ hK
      have hB_lt1 : B < bp₁.B_full + 1 :=
        (Nat.div_lt_iff_lt_mul hK).mpr (by rw [Nat.add_one_mul]; omega)
      have hB_eq : B = bp₁.B_full := by omega
      have hp_dm := Nat.div_add_mod p mp.K
      rw [Nat.mul_comm] at hp_dm
      change B * mp.K + off = p at hp_dm
      rw [hB_eq] at hp_dm
      exact Or.inr ⟨(hfix_hi B (by omega)).trans hB_eq, by omega⟩
  have hq_lt : Q * mp.K + off < bp₁.nSide := by
    rcases hQ_dom with h1 | ⟨h1, h2⟩
    · have : (Q + 1) * mp.K ≤ bp₁.B_full * mp.K := Nat.mul_le_mul_right _ h1
      rw [Nat.add_one_mul] at this; omega
    · rw [h1]; omega
  have hq_div : (Q * mp.K + off) / bp₁.K = Q := by
    rw [hK₁, Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
  have hq_mod : (Q * mp.K + off) % bp₁.K = off := by
    rw [hK₁, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  have heff_Q : bp₁.effBlk Q off = Q := by unfold BlockPoolState.effBlk; simp [hact0]
  have hb_lt_M : (bp₁.ownerOf (Q * mp.K + off)).1 < mp.M :=
    hM₁ ▸ (hcv₁.ownerOf_bounds_and_toPhys hq_lt).1
  refine ⟨hq_lt, ?_, hb_lt_M⟩
  have hactCur_eq : ∀ b, (extractBlockPool mp s.mem).actCur b = bp₁.actCur b := fun b => by
    unfold BlockPoolState.actCur
    have hK_ex : (extractBlockPool mp s.mem).K = mp.K := rfl
    rw [hac, hK_ex, hK₁]
  unfold fbSlotBktRawProg BlockPoolState.ownerOf
  rw [prog_clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK,
    prog_clientResult_bind, clientState_bpReadSlabOwnerProg, clientResult_bpReadSlabOwner_tag]
  dsimp only
  rw [hq_div, hq_mod, heff_Q]
  have htag_B : (extractBlockPool mp s.mem).blkTag B = bp₁.blkTag Q := by rw [htag]
  rw [htag_B]
  by_cases ht1 : bp₁.blkTag Q = 1
  · rw [ite_eq_left ht1, ite_eq_left ht1, clientResult_bpReadSlabOwner_m1, hm1]
  · rw [ite_eq_right ht1, ite_eq_right ht1]
    by_cases ht2 : bp₁.blkTag Q = 2
    · rw [ite_eq_left ht2, ite_eq_left ht2]
      unfold fbSlotBktTag2Prog
      rw [prog_clientResult_bind, clientState_bpReadSlabOwnerProg, clientResult_bpReadSlabOwner_m1,
        prog_clientResult_bind, clientState_bpActCurProg, bpActCurProg_spec, hactCur_eq, hm1]
      dsimp only
      by_cases hcur : off < bp₁.actCur (bp₁.blkMeta1 Q)
      · rw [ite_eq_left hcur, ite_eq_left hcur, prog_clientResult_pure]
      · rw [ite_eq_right hcur, ite_eq_right hcur]
        have hQ_le : Q ≤ bp₁.B_full := by rcases hQ_dom with h1 | ⟨h1, _⟩ <;> omega
        have htb_8M : bp₁.blkMeta2 Q < 8 * mp.M := by
          have := (hcv₁.tb_fwd Q hQ_le (Or.inr ht2)).1.trans_le hcv₁.tbHighWater_le_max
          rwa [hM₁] at this
        unfold fbTailOwnerAtBlkProg BlockPoolState.ownerOfTail
        rw [prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
          clientResult_bpReadSlabOwner_m2, hm2]; dsimp only
        rw [prog_clientResult_bind, clientState_bpTbSlotProg, clientResult_bpTbSlot htb_8M hoff,
          clientResult_bpReadTailOwner_bkt, htob, hK₁]
    · rw [ite_eq_right ht2, ite_eq_right ht2]
      have ht0 : bp₁.blkTag Q = 0 := by
        rcases hQ_dom with h1 | ⟨h1, _⟩
        · have := hcv₁.blkTag_lt Q h1; omega
        · rw [h1]; exact hcv₁.blkTag_top
      have hQ_le : Q ≤ bp₁.B_full := by rcases hQ_dom with h1 | ⟨h1, _⟩ <;> omega
      have htb_8M : bp₁.blkMeta2 Q < 8 * mp.M := by
        have := (hcv₁.tb_fwd Q hQ_le (Or.inl ht0)).1.trans_le hcv₁.tbHighWater_le_max
        rwa [hM₁] at this
      unfold fbTailOwnerAtBlkProg BlockPoolState.ownerOfTail
      rw [prog_clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m2, hm2]; dsimp only
      rw [prog_clientResult_bind, clientState_bpTbSlotProg, clientResult_bpTbSlot htb_8M hoff,
        clientResult_bpReadTailOwner_bkt, htob, hK₁]

private theorem fbFillTailOwnerLoop_spec {mp : BpMetaLayout}
    {w baseP tailLen : ℕ} {bp₁ : BlockPoolState} {π : ℕ → ℕ} {s₂ : Memory.State}
    (hmv : mp.Valid w s₂.frontier)
    (hcv₁ : bp₁.CoreValid) (hact0 : bp₁.topSwapAct = 0)
    (hM₁ : bp₁.M = mp.M) (hK₁ : bp₁.K = mp.K)
    (hns_le : bp₁.nSide ≤ mp.nCap)
    (hbase_add : baseP + tailLen = bp₁.nSide)
    (htl_8 : tailLen < 8 * mp.M * mp.K)
    (hlt : ∀ B < bp₁.B_full, π B < bp₁.B_full)
    (hfix_hi : ∀ B, bp₁.B_full ≤ B → π B = B) :
    ∀ fuel t (st : Memory.State),
      st.frontier = s₂.frontier →
      t + fuel = tailLen →
      (extractFallback mp st.mem).nSide = bp₁.nSide →
      (extractFallback mp st.mem).ownerBlk = (fun B =>
        if B < mp.maxBlocks then bp₁.blkMeta1 (π B) else 0) →
      (extractBlockPool mp st.mem).actCode = bp₁.actCode →
      (extractBlockPool mp st.mem).tailOwnerBkt = bp₁.tailOwnerBkt →
      (extractBlockPool mp st.mem).blkTag = (fun B => bp₁.blkTag (π B)) →
      (extractBlockPool mp st.mem).blkMeta1 = (fun B => bp₁.blkMeta1 (π B)) →
      (extractBlockPool mp st.mem).blkMeta2 = (fun B => bp₁.blkMeta2 (π B)) →
      (∀ i < t, (extractFallback mp st.mem).ownerTail i =
        (bp₁.ownerOf (π ((baseP + i) / mp.K) * mp.K + (baseP + i) % mp.K)).1) →
      (∀ addr, ¬mp.OwnsMetaAddr addr → st.mem addr = s₂.mem addr) →
      let st' :=
        (Memory.spec 0).clientState st (iterate fbFillTailOwnerStepProg (mp.toCtx, baseP) fuel t)
      st'.frontier = s₂.frontier ∧
      (extractFallback mp st'.mem).nSide = bp₁.nSide ∧
      (extractFallback mp st'.mem).ownerBlk = (fun B =>
        if B < mp.maxBlocks then bp₁.blkMeta1 (π B) else 0) ∧
      (∀ i < tailLen, (extractFallback mp st'.mem).ownerTail i =
        (bp₁.ownerOf (π ((baseP + i) / mp.K) * mp.K + (baseP + i) % mp.K)).1) ∧
      (∀ addr, ¬mp.OwnsMetaAddr addr → st'.mem addr = s₂.mem addr) := by
  have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
    have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  intro fuel; induction fuel with
  | zero =>
    intro t st hfr hsum hns hob _ _ _ _ _ hlo hout
    have ht : t = tailLen := by omega
    subst ht
    exact ⟨hfr, hns, hob, hlo, hout⟩
  | succ f ih =>
    intro t st hfr hsum hns hob hac htob htag hm1 hm2 hlo hout
    have ht_tl : t < tailLen := by omega
    have hp_ns : baseP + t < bp₁.nSide := by omega
    have ht_nc : t < mp.nCap := by omega
    have hbp_sub : baseP ≤ mp.nCap - t := by omega
    have ht_8 : t < 8 * mp.M * mp.K := ht_tl.trans htl_8
    obtain ⟨_, hr_bkt, hb_M⟩ := fbSlotBktRawProg_spec (s := st) hcv₁ hact0 hM₁ hK₁ hlt hfix_hi
      hac htob htag hm1 hm2 hp_ns
    set b := (bp₁.ownerOf (π ((baseP + t) / mp.K) * mp.K + (baseP + t) % mp.K)).1
    have hb_nc : b ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
    have hb_pb : b < 2 ^ mp.ptrB := lt_of_le_of_lt hb_nc hmv.nCap_lt_ptrB
    set st₁ := (Memory.spec 0).clientState st (bpWriteTailDirRawProg ((mp.toCtx, t), b))
    have hstep_st : (Memory.spec 0).clientState st
        (fbFillTailOwnerStepProg ((mp.toCtx, baseP), t)) = st₁ := by
      unfold fbFillTailOwnerStepProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
      rw [hnc_eq, ite_eq_left ⟨ht_nc, hbp_sub⟩]; simp only [pure_bind]
      unfold fbFillTailOwnerWriteProg
      rw [StateTransitionSpec.clientState_bind, state_fbSlotBktRawProg, hr_bkt,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    have hstep_res : (Memory.spec 0).clientResult st
        (fbFillTailOwnerStepProg ((mp.toCtx, baseP), t)) = t + 1 := by
      unfold fbFillTailOwnerStepProg
      rw [prog_clientResult_bind, clientState_bpReadScalarProg]; dsimp only
      rw [hnc_eq, ite_eq_left ⟨ht_nc, hbp_sub⟩]; simp only [pure_bind]
      unfold fbFillTailOwnerWriteProg
      rw [prog_clientResult_bind, state_fbSlotBktRawProg, hr_bkt,
        prog_clientResult_bind, prog_clientResult_pure]
    have hwf := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge t b
    have hfb₁ := extractFallback_writeOwnerTail (hfr.symm ▸ hmv) ht_8 hb_pb hb_nc (s := st)
    have htd_out : ∀ addr, ¬(mp.metaBase + mp.offTailDir ≤ addr ∧
        addr < mp.metaBase + mp.offTailDir + packedWords (8 * mp.M * mp.K) mp.ptrB mp.w) →
        st₁.mem addr = st.mem addr := by
      intro addr ha
      dsimp only [st₁]; unfold bpWriteTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
      rw [ite_eq_left ⟨ht_8, hb_nc⟩, clientState_writePackedCompGenProg]
      exact writePacked_outside hmv.w_pos st.mem ht_8 b ha
    have ho32 := hmv.offBktMeta_ge
    have hd1 := hmv.offSlabDir_ge; have hd2 := hmv.offTailDir_ge
    have hd3 := hmv.offSlabOwner_ge; have hd4 := hmv.offTailOwner_ge
    have h16le := hmv.sixteen_MK_le_maxTail
    have h8_16 : 8 * mp.M * mp.K ≤ 16 * mp.M * mp.K := by nlinarith
    have hac₁ : (extractBlockPool mp st₁.mem).actCode = bp₁.actCode := by
      rw [← hac]; ext x; dsimp only [extractBlockPool]
      split_ifs with hx
      · exact readPacked_congr hmv.w_pos (N := 16 * mp.M)
          (fun a ha => htd_out a (by omega)) (by omega)
      · rfl
    have htob₁ : (extractBlockPool mp st₁.mem).tailOwnerBkt = bp₁.tailOwnerBkt := by
      rw [← htob]; ext x; dsimp only [extractBlockPool]
      split_ifs with hx
      · exact readPacked_congr hmv.w_pos (N := 16 * mp.maxTail)
          (fun a ha => htd_out a (by omega)) (by omega)
      · rfl
    have htag₁ : (extractBlockPool mp st₁.mem).blkTag = (fun B => bp₁.blkTag (π B)) := by
      rw [← htag]; ext x; dsimp only [extractBlockPool]
      split_ifs with hx
      · exact readPacked_congr hmv.w_pos (N := 4 * mp.maxBlocks)
          (fun a ha => htd_out a (by omega)) (by omega)
      · rfl
    have hm1₁ : (extractBlockPool mp st₁.mem).blkMeta1 = (fun B => bp₁.blkMeta1 (π B)) := by
      rw [← hm1]; ext x; dsimp only [extractBlockPool]
      split_ifs with hx
      · exact readPacked_congr hmv.w_pos (N := 4 * mp.maxBlocks)
          (fun a ha => htd_out a (by omega)) (by omega)
      · rfl
    have hm2₁ : (extractBlockPool mp st₁.mem).blkMeta2 = (fun B => bp₁.blkMeta2 (π B)) := by
      rw [← hm2]; ext x; dsimp only [extractBlockPool]
      split_ifs with hx
      · exact readPacked_congr hmv.w_pos (N := 4 * mp.maxBlocks)
          (fun a ha => htd_out a (by omega)) (by omega)
      · rfl
    unfold iterate; dsimp only
    rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
    refine ih (t + 1) st₁ ((hwf.1.frontier_eq st).trans hfr) (by omega)
      (by rw [hfb₁]; simp only; exact hns)
      (by rw [hfb₁]; simp only; exact hob)
      hac₁ htob₁ htag₁ hm1₁ hm2₁
      (fun i hi => by
        rw [hfb₁]; simp only
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hi_lt
        · exact Function.update_self ..
        · rw [Function.update_of_ne (by omega)]; exact hlo i hi_lt)
      (fun a ha => (hwf.1.mem_outside st a ha).trans (hout a ha))

/-- Main specification of `enterFallbackProg`: transitions any `CoreValid` `BlockPoolState` on `fl`
into a valid `FallbackLayout.StateInv` (`fallbackMode = 1`) preserving `frontier`, `slack`, active
hash seeds, outside memory, and `PoolItemsRefines`. -/
theorem enterFallbackProg_spec {fl : FallbackLayout} {w slack : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hN : s.mem fl.bpL.mp.metaBase = fl.N)
    (hseed : BitPackedDoubleTabulation.SeedRep (fl.bpL.mp.metaBase + offBktHash) fl.bpL.mp.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt s.mem)
    (hcv : (extractBlockPool fl.bpL.mp s.mem).CoreValid)
    (hns_le : (extractBlockPool fl.bpL.mp s.mem).nSide ≤ fl.N)
    (hio : fl.bpL.io.StateInv (extractBlockPool fl.bpL.mp s.mem).nSide slack s.mem)
    (href : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (extractBlockPool fl.bpL.mp s.mem).nSide
      (fun p => ((extractBlockPool fl.bpL.mp s.mem).ownerOf p).1)
      (slotIoPairAt fl.bpL.io s.mem) s_abs) :
    let s' := (Memory.spec 0).clientState s (enterFallbackProg (fl.bpL.mp.toCtx, fl.bpL.io.toCtx))
    s'.frontier = s.frontier ∧
    (extractFallback fl.bpL.mp s'.mem).nSide = (extractBlockPool fl.bpL.mp s.mem).nSide ∧
    fl.StateInv slack θ_bkt s'.mem s_abs ∧
    (∀ addr, ¬fl.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.bpL.io.usePaged ≠ 0 →
      extractPageUnperm fl.bpL.io.pgL s'.mem = extractPageUnperm fl.bpL.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.bpL.io.pgL s.mem).virtLen fl.bpL.io.partner.side,
        slotIoPairAt fl.bpL.io.partner s'.mem idx = slotIoPairAt fl.bpL.io.partner s.mem idx) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  have hmv : mp.Valid w s.frontier := hv.bp_valid.mp_valid
  have hiov : io.Valid io.pgL.w s.frontier :=
    hv.bp_valid.w_eq_io ▸ hmv.w_eq.symm ▸ hv.bp_valid.io_valid
  have hdisj := hv.bp_valid.disjoint
  obtain ⟨hfr₁, hcv₁, hact₁, hns₁, hio₁_raw, href₁_raw, hout₁, hpg₁⟩ :=
    fbUndoTopSwapProg_spec hmv hiov hdisj hcv hns_le hio href
  set s₁ := (Memory.spec 0).clientState s (fbUndoTopSwapProg (mp.toCtx, io.toCtx))
  set bp₁ := extractBlockPool mp s₁.mem
  have hio₁ : io.StateInv bp₁.nSide slack s₁.mem := hns₁.symm ▸ hio₁_raw
  have href₁ : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      bp₁.nSide (fun p => (bp₁.ownerOf p).1) (slotIoPairAt io s₁.mem) s_abs :=
    hns₁.symm ▸ href₁_raw
  have hns₁_le : bp₁.nSide ≤ mp.nCap := hns₁.symm ▸ hns_le
  obtain ⟨π, π_inv, hres1, hsp_le, hfr₂, hl_π, hr_π, hlt_π, hfix_π, hlo_π, hmid_π,
      hns₂, hac₂, htob₂, htag₂, hm1₂, hm2₂, hio₂, harr₂, hout₂, hpg₂⟩ :=
    fbCompactPureLoop_spec (hfr₁.symm ▸ hmv) (hfr₁.symm ▸ hiov) hdisj rfl hcv₁ hns₁_le hio₁
      bp₁.B_full 0 0 id id s₁ rfl (Nat.zero_add _) le_rfl
      (fun _ => rfl) (fun _ => rfl) (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ h => absurd h (Nat.not_lt_zero _))
      rfl rfl rfl rfl rfl rfl hio₁
      (fun p _ => congrArg (slotIoPairAt io s₁.mem)
        (by dsimp only [id]; rw [Nat.mul_comm, Nat.div_add_mod]))
      (fun _ _ => rfl) (fun _ => ⟨rfl, fun _ _ => rfl⟩)
  set s₂ := (Memory.spec 0).clientState s₁
    (iterate fbCompactPureStepProg ((mp.toCtx, io.toCtx), bp₁.B_full) bp₁.B_full (0, 0))
  set sPure := ((Memory.spec 0).clientResult s₁
    (iterate fbCompactPureStepProg ((mp.toCtx, io.toCtx), bp₁.B_full) bp₁.B_full (0, 0))).2
  have hM₁ : bp₁.M = mp.M := rfl
  have hK₁ : bp₁.K = mp.K := rfl
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  obtain ⟨hsp_mul_raw, htl_lt6_raw⟩ :=
    compactPure_tail_le_six_MK hcv₁ hsp_le hl_π hr_π hlt_π hfix_π hlo_π hmid_π
  rw [hK₁] at hsp_mul_raw
  rw [hM₁, hK₁] at htl_lt6_raw
  set baseP := sPure * mp.K
  set tailLen := bp₁.nSide - baseP
  have hsp_div : sPure ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hsp_mul_raw.trans hns₁_le)
  have hsp_nc : sPure ≤ mp.nCap :=
    (Nat.le_mul_of_pos_right _ hK).trans (hsp_mul_raw.trans hns₁_le)
  have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
    have := hmv.M_ge; have := hmv.K_ge; nlinarith
  have htl_8 : tailLen < 8 * mp.M * mp.K := htl_lt6_raw.trans h6lt8
  have hob₂ : (extractFallback mp s₂.mem).ownerBlk =
      (fun B => if B < mp.maxBlocks then bp₁.blkMeta1 (π B) else 0) := by
    ext B
    have heq_m1 : (extractBlockPool mp s₂.mem).blkMeta1 B = bp₁.blkMeta1 (π B) :=
      congrFun hm1₂ B
    change (if B < mp.maxBlocks then
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s₂.mem (4 * B + 1) else 0) =
      bp₁.blkMeta1 (π B) at heq_m1
    unfold extractFallback; dsimp only
    split_ifs with hB
    · rw [ite_eq_left hB] at heq_m1; exact heq_m1
    · rfl
  obtain ⟨hfr₃, hns₃, hob₃, hot₃, hout₃⟩ :=
    fbFillTailOwnerLoop_spec (s₂ := s₂) (hfr₂.symm ▸ hfr₁.symm ▸ hmv)
      hcv₁ hact₁ hM₁ hK₁ hns₁_le (Nat.add_sub_of_le hsp_mul_raw) htl_8 hlt_π hfix_π
      tailLen 0 s₂ rfl (Nat.zero_add _) hns₂ hob₂ hac₂ htob₂ htag₂ hm1₂ hm2₂
      (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ => rfl)
  set s₃ := (Memory.spec 0).clientState s₂
    (iterate fbFillTailOwnerStepProg (mp.toCtx, baseP) tailLen 0)
  set s₄ := (Memory.spec 0).clientState s₃ (bpWriteScalarProg ((mp.toCtx, 10), sPure))
  have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 10 sPure
  have hfb₄ := extractFallback_writeScalar_10
    ((hfr₃.trans (hfr₂.trans hfr₁)).symm ▸ hmv) hsp_nc (s := s₃)
  set s₅ := (Memory.spec 0).clientState s₄ (fbWriteModeOneProg mp.toCtx)
  have h3_obm : 3 ≤ mp.offBktMeta := by have := hmv.offBktMeta_ge; omega
  have hs₅_mem : s₅.mem = Function.update s₄.mem (mp.metaBase + 2) 1 := by
    dsimp only [s₅]; unfold fbWriteModeOneProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left h3_obm]; rfl
  have hs₅_fr : s₅.frontier = s.frontier :=
    (frontier_fbWriteModeOneProg mp.toCtx s₄).trans
      ((hwf_sc.1.frontier_eq s₃).trans (hfr₃.trans (hfr₂.trans hfr₁)))
  have hm2_not_mp : ¬mp.OwnsMetaAddr (mp.metaBase + 2) := by
    intro hma
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
    · omega
    · omega
    · have := hmv.offBktMeta_ge; omega
  have hfb₅ : extractFallback mp s₅.mem = extractFallback mp s₄.mem :=
    extractFallback_congr hmv.w_pos fun a hma => by
      rw [hs₅_mem]
      exact Function.update_of_ne (fun he => hm2_not_mp (by rwa [← he])) 1 s₄.mem
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
  have hst_tot : (Memory.spec 0).clientState s (enterFallbackProg (mp.toCtx, io.toCtx)) = s₅ := by
    unfold enterFallbackProg
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_bpReadScalarProg, clientResult_bpReadScalar s₁ (Or.inl rfl)]
    have hs1_ns : s₁.mem (mp.metaBase + 1) = bp₁.nSide := rfl
    rw [hs1_ns]
    unfold fbEnterCompactAndFinishProg
    rw [StateTransitionSpec.clientState_bind, clientState_bpDivModKProg, clientResult_bpDivModK]
    have hbf_eq : bp₁.nSide / mp.K = bp₁.B_full := rfl
    rw [hbf_eq]
    unfold fbCompactAndFinishAtProg fbRunCompactPureProg fbCompactPureLoopProg
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      prog_clientResult_bind, StateTransitionSpec.clientState_pure, prog_clientResult_pure]
    change (Memory.spec 0).clientState s₂ (fbEnterFinishProg ((mp.toCtx, bp₁.nSide), sPure)) = s₅
    unfold fbEnterFinishProg; dsimp only
    rw [hnc_eq, hk_eq, ite_eq_left ⟨hns₁_le, hsp_div⟩]; simp only [pure_bind]
    rw [ite_eq_left hsp_mul_raw]
    unfold fbEnterFinishBodyProg fbFillTailOwnerLoopProg; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  rw [hst_tot]
  have hout_tot : ∀ addr, ¬fl.OwnsAddr addr → s₅.mem addr = s.mem addr := fun a ha => by
    have hne2 : a ≠ mp.metaBase + 2 := fun h => ha (Or.inl h)
    have hnot_bp : ¬(mp.OwnsMetaAddr a ∨ io.OwnsAddr a) := fun h => ha (Or.inr h)
    have hma : ¬mp.OwnsMetaAddr a := fun h => hnot_bp (Or.inl h)
    rw [hs₅_mem, Function.update_of_ne hne2]
    exact (hwf_sc.1.mem_outside s₃ a hma).trans
      ((hout₃ a hma).trans ((hout₂ a hnot_bp).trans (hout₁ a hnot_bp)))
  have hio_out : ∀ addr, io.OwnsAddr addr → s₅.mem addr = s₂.mem addr := fun a hia => by
    have hne2 : a ≠ mp.metaBase + 2 := fun h => hv.disjoint_hdr2 a (Or.inr h) hia
    have hma : ¬mp.OwnsMetaAddr a := fun hma => hdisj a hma hia
    rw [hs₅_mem, Function.update_of_ne hne2]
    exact (hwf_sc.1.mem_outside s₃ a hma).trans (hout₃ a hma)
  obtain ⟨hio₅, harr₅⟩ := io.congr_of_outside hiov.w_pos hio₂ hio_out
  have hns₅ : (extractFallback mp s₅.mem).nSide = bp₁.nSide := by
    rw [hfb₅, hfb₄]; simp only; exact hns₃
  have hblk₅ : (extractFallback mp s₅.mem).fullBlocks = sPure := by rw [hfb₅, hfb₄]
  have hob₅ : (extractFallback mp s₅.mem).ownerBlk =
      (fun B => if B < mp.maxBlocks then bp₁.blkMeta1 (π B) else 0) := by
    rw [hfb₅, hfb₄]; simp only; exact hob₃
  have hot₅ : (extractFallback mp s₅.mem).ownerTail = (extractFallback mp s₃.mem).ownerTail := by
    rw [hfb₅, hfb₄]
  set σ := fun p => π (p / mp.K) * mp.K + p % mp.K
  set σ_inv := fun q => π_inv (q / mp.K) * mp.K + q % mp.K
  have div_mod_add : ∀ B off, off < mp.K →
      (B * mp.K + off) / mp.K = B ∧ (B * mp.K + off) % mp.K = off := fun B off hoff =>
    ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add],
     by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]⟩
  have hσ_left : ∀ p < bp₁.nSide, σ_inv (σ p) = p := fun p _ => by
    dsimp only [σ, σ_inv]
    obtain ⟨hd, hm⟩ := div_mod_add (π (p / mp.K)) (p % mp.K) (Nat.mod_lt p hK)
    rw [hd, hm, hl_π, Nat.mul_comm, Nat.div_add_mod]
  have hσ_right : ∀ q < bp₁.nSide, σ (σ_inv q) = q := fun q _ => by
    dsimp only [σ, σ_inv]
    obtain ⟨hd, hm⟩ := div_mod_add (π_inv (q / mp.K)) (q % mp.K) (Nat.mod_lt q hK)
    rw [hd, hm, hr_π, Nat.mul_comm, Nat.div_add_mod]
  have hσ_lt : ∀ p < bp₁.nSide, σ p < bp₁.nSide := fun p hp =>
    (fbSlotBktRawProg_spec (s := s₂) hcv₁ hact₁ hM₁ hK₁ hlt_π hfix_π
      hac₂ htob₂ htag₂ hm1₂ hm2₂ hp).1
  have hπ_inv_lt : ∀ Q < bp₁.B_full, π_inv Q < bp₁.B_full := fun Q hQ => by
    by_contra hge
    have hfix := hfix_π (π_inv Q) (Nat.le_of_not_lt hge)
    rw [hr_π Q] at hfix; omega
  have hπ_inv_hi : ∀ Q, bp₁.B_full ≤ Q → π_inv Q = Q := fun Q hQ => by
    have := congrArg π_inv (hfix_π Q hQ)
    rw [hl_π Q] at this; exact this.symm
  have hσ_inv_lt : ∀ q < bp₁.nSide, σ_inv q < bp₁.nSide := fun q hq => by
    dsimp only [σ_inv]
    have hns_eq := hcv₁.nSide_eq; rw [hK₁] at hns_eq
    have hoff := Nat.mod_lt q hK
    by_cases hB : q / mp.K < bp₁.B_full
    · have h1 := hπ_inv_lt _ hB
      have : (π_inv (q / mp.K) + 1) * mp.K ≤ bp₁.B_full * mp.K := Nat.mul_le_mul_right _ h1
      rw [Nat.add_one_mul] at this; omega
    · rw [hπ_inv_hi _ (Nat.le_of_not_lt hB), Nat.mul_comm, Nat.div_add_mod]
      exact hq
  have how₅ : ∀ p < bp₁.nSide,
      (extractFallback mp s₅.mem).owner p = (bp₁.ownerOf (σ p)).1 := fun p hp => by
    unfold FallbackState.owner
    have hK5 : (extractFallback mp s₅.mem).K = mp.K := rfl
    rw [hblk₅, hK5]
    by_cases hp_lo : p < baseP
    · rw [ite_eq_left hp_lo, hob₅]; dsimp only
      have hdiv_lt : p / mp.K < sPure := (Nat.div_lt_iff_lt_mul hK).mpr hp_lo
      have hdiv_mb : p / mp.K < mp.maxBlocks := by
        have := hmv.div_K_add_two_le; omega
      rw [ite_eq_left hdiv_mb]
      have ht1 : bp₁.blkTag (π (p / mp.K)) = 1 := hlo_π _ hdiv_lt
      unfold BlockPoolState.ownerOf
      dsimp only [σ]
      obtain ⟨hd, hm⟩ := div_mod_add (π (p / mp.K)) (p % mp.K) (Nat.mod_lt p hK)
      have heff : bp₁.effBlk (π (p / mp.K)) (p % mp.K) = π (p / mp.K) := by
        unfold BlockPoolState.effBlk; simp [hact₁]
      rw [hK₁, hd, hm, heff, ite_eq_left ht1]
    · rw [ite_eq_right hp_lo, hot₅]
      have ht_lt : p - baseP < tailLen := by omega
      have hbp_re : baseP + (p - baseP) = p := Nat.add_sub_of_le (Nat.le_of_not_lt hp_lo)
      rw [hot₃ _ ht_lt, hbp_re]
  have hval₅ : (extractFallback mp s₅.mem).Valid :=
    { M_ge := by have := hmv.M_ge; change 2 ≤ mp.M; omega
      K_ge := hmv.K_ge
      blocks_le := by
        have hK5 : (extractFallback mp s₅.mem).K = mp.K := rfl
        rw [hns₅, hblk₅, hK5]; exact hsp_mul_raw
      tail_le := by
        unfold FallbackState.tailLen
        have hK5 : (extractFallback mp s₅.mem).K = mp.K := rfl
        have hM5 : (extractFallback mp s₅.mem).M = mp.M := rfl
        rw [hns₅, hblk₅, hK5, hM5]; exact htl_lt6_raw.le
      blk_lt := fun B hB => by
        rw [hblk₅] at hB
        rw [hob₅]; dsimp only
        have hB_mb : B < mp.maxBlocks := by have := hmv.div_K_add_two_le; omega
        rw [ite_eq_left hB_mb]
        have ht1 := hlo_π B hB
        have hπB := hlt_π B (lt_of_lt_of_le hB hsp_le)
        have hM5 : (extractFallback mp s₅.mem).M = mp.M := rfl
        rw [hM5, ← hM₁]
        exact (hcv₁.slab_bwd (π B) hπB ht1).1
      tail_lt := fun t ht => by
        unfold FallbackState.tailLen at ht
        have hK5 : (extractFallback mp s₅.mem).K = mp.K := rfl
        rw [hns₅, hblk₅, hK5] at ht
        rw [hot₅, hot₃ t ht]
        have hp_lt : baseP + t < bp₁.nSide := by omega
        exact (fbSlotBktRawProg_spec (s := s₂) hcv₁ hact₁ hM₁ hK₁ hlt_π hfix_π
          hac₂ htob₂ htag₂ hm1₂ hm2₂ hp_lt).2.2 }
  have href₅ := href₁.comp_perm σ σ_inv hσ_left hσ_right hσ_lt hσ_inv_lt how₅
    (fun p hp => (harr₅ p hp).trans (harr₂ p hp))
  have hN₅ : s₅.mem mp.metaBase = fl.N := by
    have hnot : ¬fl.OwnsAddr mp.metaBase := by
      dsimp only [mp] at hmv ⊢
      rintro (h2 | hma | hia)
      · omega
      · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
        · omega
        · omega
        · have := hmv.offBktMeta_ge; omega
      · exact hv.disjoint_hdr2 fl.bpL.mp.metaBase (Or.inl rfl) hia
    exact (hout_tot mp.metaBase hnot).trans hN
  have hseed₅ : BitPackedDoubleTabulation.SeedRep (mp.metaBase + offBktHash) mp.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt
      s₅.mem :=
    hseed.congr_on hmv.w_pos fun a h1 h2 => by
      have hw_eq : mp.w = w := hmv.w_eq.symm
      rw [hw_eq] at h2
      exact hout_tot a (hv.not_owns_seeds h1 (by unfold offBktMeta offFpHash; omega))
  have hinv₅ : fl.StateInv slack θ_bkt s₅.mem s_abs :=
    { hdr_N := hN₅
      mode_eq := by rw [hs₅_mem, Function.update_self]
      seed_bkt := hseed₅
      fb_valid := hval₅
      nSide_le := hns₅.trans_le hns₁_le
      io_inv := hns₅.symm ▸ hio₅
      refines := hns₅.symm ▸ href₅ }
  refine ⟨hs₅_fr, hns₅.trans hns₁, hinv₅, hout_tot, fun hnz => ?_⟩
  obtain ⟨hu₁, hp₁⟩ := hpg₁ hnz
  obtain ⟨hu₂, hp₂⟩ := hpg₂ hnz
  have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → s₅.mem addr = s₂.mem addr := fun a ha => by
    apply hio_out a; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
  have hu₅ : extractPageUnperm io.pgL s₅.mem = extractPageUnperm io.pgL s₂.mem :=
    extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
  have hvl₁ : (extractPagePair io.pgL s₁.mem).virtLen io.partner.side =
      (extractPagePair io.pgL s.mem).virtLen io.partner.side :=
    congrArg (fun u => u.st.virtLen io.partner.side) hu₁
  have hvl₂ : (extractPagePair io.pgL s₂.mem).virtLen io.partner.side =
      (extractPagePair io.pgL s₁.mem).virtLen io.partner.side :=
    congrArg (fun u => u.st.virtLen io.partner.side) hu₂
  refine ⟨hu₅.trans (hu₂.trans hu₁), fun idx hidx => ?_⟩
  unfold SlotIoLayout.StateInv at hio₂; rw [ite_eq_right hnz] at hio₂
  have hidx₂ : idx < (extractPagePair io.pgL s₂.mem).virtLen io.partner.side := by
    rwa [hvl₂, hvl₁]
  have hp_lt₂ : (extractPageUnperm io.pgL s₂.mem).toPhys io.partner.side idx < io.pgL.nCap :=
    (hio₂.1.toPhys_lt hidx₂).trans_le hio₂.2.2.2.1
  have hp₅ : slotIoPairAt io.partner s₅.mem idx = slotIoPairAt io.partner s₂.mem idx := by
    unfold slotIoPairAt
    have hp_nz : io.partner.usePaged ≠ 0 := hnz
    rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu₅]
    exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt₂
  exact hp₅.trans ((hp₂ idx (hvl₁.symm ▸ hidx)).trans (hp₁ idx hidx))

/-! ## Section 2: Public `FallbackPool` Dictionary Operations -/

/-- Wire context `(FeistelHashCtx × BlockPoolCtx)` for `FallbackPool` dictionary operations. -/
abbrev FallbackOpCtx := FeistelHashCtx × BlockPoolCtx

/-- Serialize `fl : FallbackLayout` to `FallbackOpCtx`. -/
@[expose] def FallbackLayout.toCtx (fl : FallbackLayout) : FallbackOpCtx :=
  (fl.feistelCtx, (fl.bpL.mp.toCtx, fl.bpL.io.toCtx))

/-- `FallbackPool` `query(u)` returning `(0, 0)` on `none` and `(1, v.val)` on `some v`
(`¬ReadsWidth`). -/
def fallbackQueryProg : FallbackOpCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | ((fctx, (mctx, ioctx)), u_val) => do
    let bq ← feistelSplitBoundedProg (fctx, u_val)
    let r ← fbScanProg ((mctx, ioctx), bq)
    pure (r.1, scanResVal r)

theorem realizesBounded_fallbackQuery :
    RealizesBounded .exact fallbackQueryProg
      (WordEncoding.encode (α := FallbackOpCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((fctx, (mctx, ioctx)), u_val) s =>
        FeistelSplitPre w (fctx, u_val) s ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hfs := realizesBounded_feistelSplit
  have hsc := realizesBounded_fbScan
  realize
  all_goals (
    rcases d with ⟨⟨fctx, ⟨mctx, ioctx⟩⟩, u_val⟩
    obtain ⟨hpre, hmv, hiov⟩ := h
    try simp only [Prod.mk.eta] at *
    first | exact hpre | (
      have hs := clientState_feistelSplitBoundedProg (fctx, u_val) s
      dsimp only [StateTransitionSpec.clientState] at hs ⊢
      rw [hs]; first | exact hmv | exact hiov))

theorem fallbackQueryProg_spec {fl : FallbackLayout} {w slack : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv slack θ_bkt s.mem s_abs) (u : Fin fl.U) :
    (Memory.spec 0).clientState s (fallbackQueryProg (fl.toCtx, u.val)) = s ∧
    (Memory.spec 0).clientResult s (fallbackQueryProg (fl.toCtx, u.val)) =
      match s_abs u with
      | none => (0, 0)
      | some v => (1, v.val) := by
  obtain ⟨hfs_res, hfs_st, _⟩ := feistelSplitBoundedProg_spec hv.N_le_U hinv.seed_bkt u
  change (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = _
    at hfs_res
  change (Memory.spec 0).clientState s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = s
    at hfs_st
  obtain ⟨hsc_st, hsc_res⟩ := fbScanProg_spec hv hinv u
  have hctx : fl.toCtx = (fl.feistelCtx, (fl.bpL.mp.toCtx, fl.bpL.io.toCtx)) := rfl
  unfold fallbackQueryProg; rw [hctx]
  refine ⟨?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hfs_st, hfs_res,
      StateTransitionSpec.clientState_bind, hsc_st, StateTransitionSpec.clientState_pure]
  · rw [prog_clientResult_bind, hfs_st, hfs_res, prog_clientResult_bind, hsc_st,
      prog_clientResult_pure]
    cases hs : s_abs u with
    | none => rw [hs] at hsc_res; rw [hsc_res]
    | some v => rw [hs] at hsc_res; exact Prod.ext hsc_res.1 hsc_res.2.2.1

private def fbInsertNewCommitProg :
    ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((mctx, ioctx), (bkt, q_u)), v_val), (nSide, t)) => do
    slotIoAppendRawProg ((ioctx, nSide), (q_u, v_val))
    bpWriteTailDirRawProg ((mctx, t), bkt)
    bpWriteScalarProg ((mctx, 1), nSide + 1)

private theorem frontier_fbInsertNewCommitProg
    (x : ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbInsertNewCommitProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨mctx, ioctx⟩, ⟨bkt, q_u⟩⟩, v_val⟩, ⟨nSide, t⟩⟩
  unfold fbInsertNewCommitProg
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    frontier_bpWriteScalarProg, frontier_bpWriteTailDirRawProg]
  have haf :=
    (slotIoAppendProg_frame (io := SlotIoLayout.ofCtx ioctx) hw nSide q_u v_val).frontier_eq s
  unfold slotIoAppendProg at haf; rw [SlotIoLayout.toCtx_ofCtx] at haf
  exact haf

private theorem realizesBounded_fbInsertNewCommit :
    RealizesBounded .exact fbInsertNewCommitProg
      (WordEncoding.encode (α := ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((mctx, ioctx), _), _), (nSide, _)) s =>
        nSide < (BpMetaLayout.ofCtx mctx).nCap ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hap := realizesBounded_slotIoAppendRaw
  have htd := realizesBounded_bpWriteTailDirRaw
  have hws := realizesBounded_bpWriteScalar
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mctx, ioctx⟩, ⟨bkt, q_u⟩⟩, v_val⟩, ⟨nSide, t⟩⟩
    obtain ⟨hns_lt, hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hiov | exact hw1 | (
      have haf := (slotIoAppendProg_frame (io := SlotIoLayout.ofCtx ioctx) hiov.w_pos nSide q_u
        v_val).frontier_eq s
      unfold slotIoAppendProg at haf; rw [SlotIoLayout.toCtx_ofCtx] at haf
      set s_ap :=
        ((Memory.spec 0).runClient s (slotIoAppendRawProg ((ioctx, nSide), (q_u, v_val)))).2.1
      have htd_f := runClient_frontier_bpWriteTailDirRawProg ((mctx, t), bkt) s_ap
      dsimp only [s_ap, StateTransitionSpec.clientState] at haf htd_f ⊢
      try rw [htd_f]
      rw [haf]; exact hmv) | omega)

private def fbInsertNewCheckProg :
    ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((mctx, ioctx), bq), v_val), (nSide, fb0)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if nSide < nCap then
      if fb0 ≤ nCap / k then
        if fb0 * k ≤ nSide then do
          let t ← pure (nSide - fb0 * k)
          fbInsertNewCommitProg ((((mctx, ioctx), bq), v_val), (nSide, t))
        else pure ()
      else pure ()
    else pure ()

private theorem frontier_fbInsertNewCheckProg
    (x : ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbInsertNewCheckProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, bq⟩, v_val⟩, ⟨nSide, fb0⟩⟩
  unfold fbInsertNewCheckProg; dsimp only
  split_ifs
  · simp only [pure_bind]; exact frontier_fbInsertNewCommitProg _ s hw
  all_goals rfl

private theorem realizesBounded_fbInsertNewCheck :
    RealizesBounded .exact fbInsertNewCheckProg
      (WordEncoding.encode (α := ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((mctx, ioctx), _), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hcm := realizesBounded_fbInsertNewCommit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, bq⟩, v_val⟩, ⟨nSide, fb0⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    try dsimp only [BpMetaLayout.ofCtx] at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | (
      have hmul : fb0 * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      omega) | omega)

private def fbInsertNewProg : (BlockPoolCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((mctx, ioctx), bq), v_val) => do
    fbMaybePromoteProg (mctx, ioctx)
    let nSide ← bpReadScalarProg (mctx, 1)
    let fb0 ← bpReadScalarProg (mctx, 10)
    fbInsertNewCheckProg ((((mctx, ioctx), bq), v_val), (nSide, fb0))

private theorem realizesBounded_fbInsertNew :
    RealizesBounded .exact fbInsertNewProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hmp := realizesBounded_fbMaybePromote
  have hrs := realizesBounded_bpReadScalar
  have hck := realizesBounded_fbInsertNewCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, bq⟩, v_val⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | exact hw1 | exact h10_w | (
      have hfr := frontier_fbMaybePromoteProg (mctx, ioctx) s hiov.w_pos
      dsimp only [mctx, StateTransitionSpec.clientState] at hfr ⊢
      rw [hfr]; first | exact hmv | exact hiov))

/-- `FallbackPool` `insert(u, v)` (`¬ReadsWidth`). -/
def fallbackInsertProg : (FallbackOpCtx × ℕ) × ℕ → Memory.Prog Unit
  | (((fctx, (mctx, ioctx)), u_val), v_val) => do
    let bq ← feistelSplitBoundedProg (fctx, u_val)
    let r ← fbScanProg ((mctx, ioctx), bq)
    if r.1 = 1 then
      slotIoWriteRawProg ((ioctx, scanResSlot r), (bq.2, v_val))
    else
      fbInsertNewProg (((mctx, ioctx), bq), v_val)

theorem realizesBounded_fallbackInsert :
    RealizesBounded .exact fallbackInsertProg
      (WordEncoding.encode (α := (FallbackOpCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((fctx, (mctx, ioctx)), u_val), _) s =>
        FeistelSplitPre w (fctx, u_val) s ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hfs := realizesBounded_feistelSplit
  have hsc := realizesBounded_fbScan
  have hwr := realizesBounded_slotIoWriteRaw
  have hin := realizesBounded_fbInsertNew
  realize
  all_goals (
    rcases d with ⟨⟨⟨fctx, ⟨mctx, ioctx⟩⟩, u_val⟩, v_val⟩
    obtain ⟨hpre, hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hpre | exact hw1 | (
      have hs := clientState_feistelSplitBoundedProg (fctx, u_val) s
      set bq := (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fctx, u_val))
      have hsc_s := state_fbScanProg ((mctx, ioctx), bq) s
      dsimp only [bq, StateTransitionSpec.clientState] at hs hsc_s ⊢
      rw [hs]; try rw [hsc_s]
      first | exact hmv | exact hiov))

theorem fallbackInsertProg_spec {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv 0 θ_bkt s.mem s_abs)
    (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : s_abs u = none →
      (extractFallback fl.bpL.mp s.mem).nSide < fl.N ∧
      fl.bpL.io.AppendCap (extractFallback fl.bpL.mp s.mem).nSide s.mem) :
    let fb := extractFallback fl.bpL.mp s.mem
    let s' := (Memory.spec 0).clientState s (fallbackInsertProg ((fl.toCtx, u.val), v.val))
    let slack' :=
      if fl.bpL.io.usePaged = 0 ∨ (extractPageUnperm fl.bpL.io.pgL s.mem).cleanPhase = 0 then 0
      else 24
    s'.frontier = s.frontier ∧
    (extractFallback fl.bpL.mp s'.mem).nSide =
      (if s_abs u = none then fb.nSide + 1 else fb.nSide) ∧
    fl.StateInv slack' θ_bkt s'.mem (Function.update s_abs u (some v)) ∧
    (∀ addr, ¬fl.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.bpL.io.usePaged ≠ 0 →
      (extractPagePair fl.bpL.io.pgL s'.mem).virtLen fl.bpL.io.partner.side =
        (extractPagePair fl.bpL.io.pgL s.mem).virtLen fl.bpL.io.partner.side ∧
      (extractPagePair fl.bpL.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.bpL.io.pgL s.mem).totalItems + 1
         else (extractPagePair fl.bpL.io.pgL s.mem).totalItems) ∧
      ∀ idx < (extractPagePair fl.bpL.io.pgL s.mem).virtLen fl.bpL.io.partner.side,
        slotIoPairAt fl.bpL.io.partner s'.mem idx = slotIoPairAt fl.bpL.io.partner s.mem idx) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  set fb := extractFallback mp s.mem
  have hmv : mp.Valid w s.frontier := hv.bp_valid.mp_valid
  have hiov : io.Valid io.pgL.w s.frontier :=
    hv.bp_valid.w_eq_io ▸ hmv.w_eq.symm ▸ hv.bp_valid.io_valid
  have hdisj := hv.bp_valid.disjoint
  obtain ⟨hfs_res, hfs_st, _⟩ := feistelSplitBoundedProg_spec hv.N_le_U hinv.seed_bkt u
  change (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = _
    at hfs_res
  change (Memory.spec 0).clientState s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = s
    at hfs_st
  obtain ⟨hsc_st, hsc_res⟩ := fbScanProg_spec hv hinv u
  set bkt := epochBucket fl.c fl.U fl.N θ_bkt u
  set q_u := keyQuotient (bWhp fl.N) u.val
  have hq_u : q_u < 2 ^ io.pgL.qBits :=
    (keyQuotient_bWhp_lt hv.N_le_U u).trans_le (Nat.pow_le_pow_right Nat.one_lt_two.le hv.qBits_le)
  have hv_v : v.val < 2 ^ io.pgL.vBits := by
    rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.V)
  set slack' :=
    if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  have hctx : fl.toCtx = (fl.feistelCtx, (mp.toCtx, io.toCtx)) := rfl
  unfold fallbackInsertProg; rw [hctx]
  rw [StateTransitionSpec.clientState_bind, hfs_st, hfs_res,
    StateTransitionSpec.clientState_bind, hsc_st]
  dsimp only
  cases hs_u : s_abs u with
  | some v_old =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hhit_lt, _, how_hit, hpr_hit⟩ := hsc_res
    set hitP := ((Memory.spec 0).clientResult s (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u)))).2.1
    have hnone_f : ¬(some v_old = none) := by simp
    rw [ite_eq_left hr1, ite_eq_right hnone_f]
    obtain ⟨hio', harr', hpart'⟩ := slotIoWriteProg_spec hiov hinv.io_inv hhit_lt hq_u hv_v
    have hwf := slotIoWriteProg_frame (io := io) hiov.w_pos hitP q_u v.val
    unfold slotIoWriteProg at hio' harr' hpart' hwf
    set s' := (Memory.spec 0).clientState s (slotIoWriteRawProg ((io.toCtx, hitP), (q_u, v.val)))
    have hout_tot : ∀ addr, ¬fl.OwnsAddr addr → s'.mem addr = s.mem addr := fun a ha =>
      hwf.mem_outside s a (fun hia => ha (Or.inr (Or.inr hia)))
    have hfb' : extractFallback mp s'.mem = fb :=
      extractFallback_congr hmv.w_pos fun a hma =>
        hwf.mem_outside s a (fun hia => hdisj a hma hia)
    have hN' : s'.mem mp.metaBase = fl.N :=
      (hwf.mem_outside s mp.metaBase (fun hia => hv.disjoint_hdr2 _ (Or.inl rfl) hia)).trans
        hinv.hdr_N
    have hm2' : s'.mem (mp.metaBase + 2) = 1 :=
      (hwf.mem_outside s (mp.metaBase + 2) (fun hia => hv.disjoint_hdr2 _ (Or.inr rfl) hia)).trans
        hinv.mode_eq
    have hseed' : BitPackedDoubleTabulation.SeedRep (mp.metaBase + offBktHash) mp.w
        (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt
        s'.mem :=
      hinv.seed_bkt.congr_on hmv.w_pos fun a h1 h2 => by
        have hw_eq : mp.w = w := hmv.w_eq.symm
        rw [hw_eq] at h2
        exact hout_tot a (hv.not_owns_seeds h1 (by unfold offBktMeta offFpHash; omega))
    have href' := hinv.refines.update_at (pr' := slotIoPairAt io s'.mem) v hhit_lt how_hit
      (by rw [hpr_hit]) (by rw [harr' hitP hhit_lt, ite_eq_left rfl])
      (fun q hq hne => by rw [harr' q hq, ite_eq_right hne])
    have hinv' : fl.StateInv slack' θ_bkt s'.mem (Function.update s_abs u (some v)) :=
      { hdr_N := hN'
        mode_eq := hm2'
        seed_bkt := hseed'
        fb_valid := hfb'.symm ▸ hinv.fb_valid
        nSide_le := hfb'.symm ▸ hinv.nSide_le
        io_inv := hfb'.symm ▸ hio'.mono_slack (Nat.zero_le _) hsl_le
        refines := hfb'.symm ▸ href' }
    refine ⟨hwf.frontier_eq s, congrArg FallbackState.nSide hfb', hinv', hout_tot, fun hnz => ?_⟩
    obtain ⟨hu_eq, hp_eq⟩ := hpart' hnz
    have hst_eq : extractPagePair io.pgL s'.mem = extractPagePair io.pgL s.mem :=
      congrArg PageUnpermState.st hu_eq
    rw [ite_eq_right hnone_f, hst_eq]
    exact ⟨rfl, rfl, hp_eq⟩
  | none =>
    rw [hs_u] at hsc_res
    obtain ⟨hns_lt, hpg_cap⟩ := hcap_new hs_u
    have hr_ne1 : ((Memory.spec 0).clientResult s
        (fbScanProg ((mp.toCtx, io.toCtx), (bkt, q_u)))).1 ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1, ite_eq_left rfl]
    obtain ⟨hfr₁, hns₁, _, htl_plus₁, hval₁, hio₁, href₁, _, hout₁, hpg₁⟩ :=
      fbMaybePromoteProg_spec hmv hiov hdisj hinv.fb_valid hinv.nSide_le hinv.io_inv hinv.refines
    set s₁ := (Memory.spec 0).clientState s (fbMaybePromoteProg (mp.toCtx, io.toCtx))
    set fb₁ := extractFallback mp s₁.mem
    set fb0 := fb₁.fullBlocks
    set t := fb.nSide - fb0 * mp.K
    have hK : 0 < mp.K := by have := hmv.K_ge; omega
    have hfb1_K : fb₁.K = mp.K := rfl
    have hfb1_M : fb₁.M = mp.M := rfl
    have hbl_le₁ : fb0 * mp.K ≤ fb.nSide := by
      have hb := hval₁.blocks_le; rwa [hfb1_K, hns₁] at hb
    have hfb0_div : fb0 ≤ mp.nCap / mp.K :=
      (Nat.le_div_iff_mul_le hK).mpr (hbl_le₁.trans hns_lt.le)
    have ht_eq_tl : t = fb₁.tailLen := by
      unfold FallbackState.tailLen; rw [hns₁, hfb1_K]
    have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
      have := hmv.M_ge; have := hmv.K_ge; nlinarith
    have ht_8 : t < 8 * mp.M * mp.K := by
      rw [ht_eq_tl]; exact (Nat.le_add_right _ mp.K).trans_lt (htl_plus₁.trans_lt h6lt8)
    have hbkt_M : bkt < mp.M := by
      have hM_eq : mp.M = 2 ^ bWhp fl.N := by dsimp only [mp]; rw [hv.mp_eq]; rfl
      rw [hM_eq]; exact feistelBucket_lt (bWhp fl.N) _ u.val
    have hbkt_nc : bkt ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
    have hbkt_pb : bkt < 2 ^ mp.ptrB := lt_of_le_of_lt hbkt_nc hmv.nCap_lt_ptrB
    have hcap_io₁ : if io.usePaged = 0 then fb.nSide + 1 ≤ io.pgL.nCap
        else (extractPagePair io.pgL s₁.mem).totalItems + 1 ≤ io.pgL.nCap := by
      by_cases h0 : io.usePaged = 0
      · rw [ite_eq_left h0]
        unfold SlotIoLayout.AppendCap at hpg_cap
        rwa [ite_eq_left h0] at hpg_cap
      · rw [ite_eq_right h0]
        have hst₁ : extractPagePair io.pgL s₁.mem = extractPagePair io.pgL s.mem :=
          congrArg PageUnpermState.st (hpg₁ h0).1
        rw [hst₁]
        unfold SlotIoLayout.AppendCap at hpg_cap
        rwa [ite_eq_right h0] at hpg_cap
    obtain ⟨hio₂_raw, harr₂, hpg₂⟩ :=
      slotIoAppendProg_spec (hfr₁.symm ▸ hiov) hio₁ hcap_io₁ hq_u hv_v
    have haf := slotIoAppendProg_frame (io := io) hiov.w_pos fb.nSide q_u v.val
    unfold slotIoAppendProg at hio₂_raw harr₂ hpg₂ haf
    have hsl_eq : (if io.usePaged = 0 ∨
        (extractPageUnperm io.pgL s₁.mem).cleanPhase = 0 then 0 else 24) = slack' := by
      by_cases h0 : io.usePaged = 0
      · simp [slack', h0]
      · simp only [slack', h0, false_or, (hpg₁ h0).1]
    have hio₂ : io.StateInv (fb.nSide + 1) slack'
        ((Memory.spec 0).clientState s₁
          (slotIoAppendRawProg ((io.toCtx, fb.nSide), (q_u, v.val)))).mem :=
      hsl_eq ▸ hio₂_raw
    set s₂ := (Memory.spec 0).clientState s₁
      (slotIoAppendRawProg ((io.toCtx, fb.nSide), (q_u, v.val)))
    have hfr₂ : s₂.frontier = s.frontier := (haf.frontier_eq s₁).trans hfr₁
    have hfb₂ : extractFallback mp s₂.mem = fb₁ :=
      extractFallback_congr hmv.w_pos fun a hma =>
        haf.mem_outside s₁ a (fun hia => hdisj a hma hia)
    set s₃ := (Memory.spec 0).clientState s₂ (bpWriteTailDirRawProg ((mp.toCtx, t), bkt))
    have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
      have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
    have hwf_td := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge t bkt
    have hfb₃ := extractFallback_writeOwnerTail (hfr₂.symm ▸ hmv) ht_8 hbkt_pb hbkt_nc (s := s₂)
    rw [hfb₂] at hfb₃
    have hfr₃ : s₃.frontier = s.frontier := (hwf_td.1.frontier_eq s₂).trans hfr₂
    set s₄ := (Memory.spec 0).clientState s₃ (bpWriteScalarProg ((mp.toCtx, 1), fb.nSide + 1))
    have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 1 (fb.nSide + 1)
    have hns1_nc : fb.nSide + 1 ≤ mp.nCap := hns_lt
    have hfb₄ := extractFallback_writeScalar_1 (hfr₃.symm ▸ hmv) hns1_nc (s := s₃)
    rw [hfb₃] at hfb₄
    have hfr₄ : s₄.frontier = s.frontier := (hwf_sc.1.frontier_eq s₃).trans hfr₃
    have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
    have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
    have hst_tot : (Memory.spec 0).clientState s
        (fbInsertNewProg (((mp.toCtx, io.toCtx), (bkt, q_u)), v.val)) = s₄ := by
      unfold fbInsertNewProg
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        clientState_bpReadScalarProg, clientResult_bpReadScalar s₁ (Or.inl rfl),
        StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s₁ (Or.inr ⟨le_rfl, by omega⟩)]
      have hs1_ns : s₁.mem (mp.metaBase + 1) = fb.nSide := hns₁
      have hs1_fb : s₁.mem (mp.metaBase + 10) = fb0 := rfl
      rw [hs1_ns, hs1_fb]
      unfold fbInsertNewCheckProg; dsimp only
      rw [hnc_eq, hk_eq, ite_eq_left hns_lt, ite_eq_left hfb0_div, ite_eq_left hbl_le₁]
      simp only [pure_bind]
      unfold fbInsertNewCommitProg
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
    rw [hst_tot]
    have hio_out : ∀ addr, io.OwnsAddr addr → s₄.mem addr = s₂.mem addr := fun a hia => by
      have hma : ¬mp.OwnsMetaAddr a := fun hma => hdisj a hma hia
      exact (hwf_sc.1.mem_outside s₃ a hma).trans (hwf_td.1.mem_outside s₂ a hma)
    obtain ⟨hio₄, harr₄⟩ := io.congr_of_outside hiov.w_pos hio₂ hio_out
    have hout_tot : ∀ addr, ¬fl.OwnsAddr addr → s₄.mem addr = s.mem addr := fun a ha => by
      have hnot_bp : ¬(mp.OwnsMetaAddr a ∨ io.OwnsAddr a) := fun h => ha (Or.inr h)
      have hma : ¬mp.OwnsMetaAddr a := fun h => hnot_bp (Or.inl h)
      have hia : ¬io.OwnsAddr a := fun h => hnot_bp (Or.inr h)
      exact (hwf_sc.1.mem_outside s₃ a hma).trans
        ((hwf_td.1.mem_outside s₂ a hma).trans
          ((haf.mem_outside s₁ a hia).trans (hout₁ a hnot_bp)))
    have hns₄ : (extractFallback mp s₄.mem).nSide = fb.nSide + 1 := by rw [hfb₄]
    have hblk₄ : (extractFallback mp s₄.mem).fullBlocks = fb0 := by rw [hfb₄]
    have hob₄ : (extractFallback mp s₄.mem).ownerBlk = fb₁.ownerBlk := by rw [hfb₄]
    have hot₄ : (extractFallback mp s₄.mem).ownerTail = Function.update fb₁.ownerTail t bkt := by
      rw [hfb₄]
    have how_new : (extractFallback mp s₄.mem).owner fb.nSide = bkt := by
      unfold FallbackState.owner
      have hK4 : (extractFallback mp s₄.mem).K = mp.K := rfl
      rw [hblk₄, hK4, ite_eq_right (not_lt.mpr hbl_le₁), hot₄]
      exact Function.update_self ..
    have how_old : ∀ p < fb.nSide, (extractFallback mp s₄.mem).owner p = fb₁.owner p :=
      fun p hp => by
        unfold FallbackState.owner
        have hK4 : (extractFallback mp s₄.mem).K = mp.K := rfl
        rw [hblk₄, hK4, hfb1_K]
        by_cases hp_lo : p < fb0 * mp.K
        · rw [ite_eq_left hp_lo, ite_eq_left hp_lo, hob₄]
        · rw [ite_eq_right hp_lo, ite_eq_right hp_lo, hot₄,
            Function.update_of_ne (by dsimp only [t]; omega)]
    have href₄ := href₁.append_new (ow' := (extractFallback mp s₄.mem).owner)
      (pr' := slotIoPairAt io s₄.mem) v hs_u how_new
      (by rw [harr₄ _ (Nat.lt_succ_self _), harr₂ _ (Nat.lt_succ_self _), ite_eq_left rfl])
      how_old
      (fun p hp => by
        rw [harr₄ p (Nat.lt_succ_of_lt hp), harr₂ p (Nat.lt_succ_of_lt hp),
          ite_eq_right (Nat.ne_of_lt hp)])
    have hval₄ : (extractFallback mp s₄.mem).Valid :=
      { M_ge := hval₁.M_ge
        K_ge := hval₁.K_ge
        blocks_le := by
          have hK4 : (extractFallback mp s₄.mem).K = mp.K := rfl
          rw [hns₄, hblk₄, hK4]; omega
        tail_le := by
          unfold FallbackState.tailLen
          have hK4 : (extractFallback mp s₄.mem).K = mp.K := rfl
          have hM4 : (extractFallback mp s₄.mem).M = mp.M := rfl
          rw [hns₄, hblk₄, hK4, hM4]
          have : fb.nSide + 1 - fb0 * mp.K = fb₁.tailLen + 1 := by
            rw [← ht_eq_tl]; dsimp only [t]; omega
          rw [this]; omega
        blk_lt := by rw [hblk₄, hob₄]; exact hval₁.blk_lt
        tail_lt := fun i hi => by
          unfold FallbackState.tailLen at hi
          have hK4 : (extractFallback mp s₄.mem).K = mp.K := rfl
          have hM4 : (extractFallback mp s₄.mem).M = mp.M := rfl
          rw [hns₄, hblk₄, hK4] at hi
          rw [hot₄, hM4]
          have hi_le : i ≤ t := by dsimp only [t]; omega
          rcases eq_or_lt_of_le hi_le with rfl | hi_lt
          · rw [Function.update_self]; exact hbkt_M
          · rw [Function.update_of_ne (ne_of_lt hi_lt)]
            exact hfb1_M ▸ hval₁.tail_lt i (ht_eq_tl ▸ hi_lt) }
    have hnot_m0 : ¬fl.OwnsAddr mp.metaBase := by
      dsimp only [mp] at hmv ⊢
      rintro (h2 | hma | hia)
      · omega
      · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
        · omega
        · omega
        · have := hmv.offBktMeta_ge; omega
      · exact hv.disjoint_hdr2 fl.bpL.mp.metaBase (Or.inl rfl) hia
    have hm2_not_bp : ¬(mp.OwnsMetaAddr (mp.metaBase + 2) ∨ io.OwnsAddr (mp.metaBase + 2)) := by
      rintro (hma | hia)
      · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
        · omega
        · omega
        · have := hmv.offBktMeta_ge; omega
      · exact hv.disjoint_hdr2 _ (Or.inr rfl) hia
    have hm2_4 : s₄.mem (mp.metaBase + 2) = 1 :=
      (hwf_sc.1.mem_outside s₃ _ (fun h => hm2_not_bp (Or.inl h))).trans
        ((hwf_td.1.mem_outside s₂ _ (fun h => hm2_not_bp (Or.inl h))).trans
          ((haf.mem_outside s₁ _ (fun h => hm2_not_bp (Or.inr h))).trans
            ((hout₁ _ hm2_not_bp).trans hinv.mode_eq)))
    have hseed₄ : BitPackedDoubleTabulation.SeedRep (mp.metaBase + offBktHash) mp.w
        (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt
        s₄.mem :=
      hinv.seed_bkt.congr_on hmv.w_pos fun a h1 h2 => by
        have hw_eq : mp.w = w := hmv.w_eq.symm
        rw [hw_eq] at h2
        exact hout_tot a (hv.not_owns_seeds h1 (by unfold offBktMeta offFpHash; omega))
    have hinv₄ : fl.StateInv slack' θ_bkt s₄.mem (Function.update s_abs u (some v)) :=
      { hdr_N := (hout_tot mp.metaBase hnot_m0).trans hinv.hdr_N
        mode_eq := hm2_4
        seed_bkt := hseed₄
        fb_valid := hval₄
        nSide_le := hns₄.trans_le hns1_nc
        io_inv := hns₄.symm ▸ hio₄
        refines := hns₄.symm ▸ href₄ }
    refine ⟨hfr₄, hns₄, hinv₄, hout_tot, fun hnz => ?_⟩
    obtain ⟨hu₁, hp₁⟩ := hpg₁ hnz
    obtain ⟨hvl₂, hti₂, hp₂⟩ := hpg₂ hnz
    have hst₁ : extractPagePair io.pgL s₁.mem = extractPagePair io.pgL s.mem :=
      congrArg PageUnpermState.st hu₁
    have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → s₄.mem addr = s₂.mem addr := fun a ha => by
      apply hio_out a; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
    have hu₄ : extractPageUnperm io.pgL s₄.mem = extractPageUnperm io.pgL s₂.mem :=
      extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
    have hst₄ : extractPagePair io.pgL s₄.mem = extractPagePair io.pgL s₂.mem :=
      congrArg PageUnpermState.st hu₄
    rw [ite_eq_left rfl]
    refine ⟨by rw [hst₄, hvl₂, hst₁], by rw [hst₄, hti₂, hst₁], fun idx hidx => ?_⟩
    unfold SlotIoLayout.StateInv at hio₂; rw [ite_eq_right hnz] at hio₂
    have hidx₂ : idx < (extractPagePair io.pgL s₂.mem).virtLen io.partner.side := by
      rwa [hvl₂, hst₁]
    have hp_lt₂ : (extractPageUnperm io.pgL s₂.mem).toPhys io.partner.side idx < io.pgL.nCap :=
      (hio₂.1.toPhys_lt hidx₂).trans_le hio₂.2.2.2.1
    have hp₄ : slotIoPairAt io.partner s₄.mem idx = slotIoPairAt io.partner s₂.mem idx := by
      unfold slotIoPairAt
      have hp_nz : io.partner.usePaged ≠ 0 := hnz
      rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu₄]
      exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt₂
    exact hp₄.trans ((hp₂ idx (hst₁.symm ▸ hidx)).trans (hp₁ idx hidx))

/-- `FallbackPool` `delete(u)` (`¬ReadsWidth`). -/
def fallbackDeleteProg : FallbackOpCtx × ℕ → Memory.Prog Unit
  | ((fctx, (mctx, ioctx)), u_val) => do
    let bq ← feistelSplitBoundedProg (fctx, u_val)
    let r ← fbScanProg ((mctx, ioctx), bq)
    if r.1 = 1 then
      fbDeleteSlotProg ((mctx, ioctx), scanResSlot r)
    else
      pure ()

theorem realizesBounded_fallbackDelete :
    RealizesBounded .exact fallbackDeleteProg
      (WordEncoding.encode (α := FallbackOpCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((fctx, (mctx, ioctx)), u_val) s =>
        FeistelSplitPre w (fctx, u_val) s ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hfs := realizesBounded_feistelSplit
  have hsc := realizesBounded_fbScan
  have hds := realizesBounded_fbDeleteSlot
  realize
  all_goals (
    rcases d with ⟨⟨fctx, ⟨mctx, ioctx⟩⟩, u_val⟩
    obtain ⟨hpre, hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hpre | exact hw1 | (
      have hs := clientState_feistelSplitBoundedProg (fctx, u_val) s
      set bq := (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fctx, u_val))
      have hsc_s := state_fbScanProg ((mctx, ioctx), bq) s
      dsimp only [bq, StateTransitionSpec.clientState] at hs hsc_s ⊢
      rw [hs]; try rw [hsc_s]
      first | exact hmv | exact hiov))

theorem fallbackDeleteProg_spec {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv 0 θ_bkt s.mem s_abs) (u : Fin fl.U) :
    let fb := extractFallback fl.bpL.mp s.mem
    let s' := (Memory.spec 0).clientState s (fallbackDeleteProg (fl.toCtx, u.val))
    let slack' :=
      if fl.bpL.io.usePaged = 0 ∨ (extractPageUnperm fl.bpL.io.pgL s.mem).cleanPhase = 0 then 0
      else 24
    s'.frontier = s.frontier ∧
    (extractFallback fl.bpL.mp s'.mem).nSide =
      (if s_abs u = none then fb.nSide else fb.nSide - 1) ∧
    fl.StateInv slack' θ_bkt s'.mem (Function.update s_abs u none) ∧
    (∀ addr, ¬fl.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.bpL.io.usePaged ≠ 0 →
      (extractPagePair fl.bpL.io.pgL s'.mem).virtLen fl.bpL.io.partner.side =
        (extractPagePair fl.bpL.io.pgL s.mem).virtLen fl.bpL.io.partner.side ∧
      (extractPagePair fl.bpL.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.bpL.io.pgL s.mem).totalItems
         else (extractPagePair fl.bpL.io.pgL s.mem).totalItems - 1) ∧
      ∀ idx < (extractPagePair fl.bpL.io.pgL s.mem).virtLen fl.bpL.io.partner.side,
        slotIoPairAt fl.bpL.io.partner s'.mem idx = slotIoPairAt fl.bpL.io.partner s.mem idx) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  set fb := extractFallback mp s.mem
  have hmv : mp.Valid w s.frontier := hv.bp_valid.mp_valid
  have hiov : io.Valid io.pgL.w s.frontier :=
    hv.bp_valid.w_eq_io ▸ hmv.w_eq.symm ▸ hv.bp_valid.io_valid
  have hdisj := hv.bp_valid.disjoint
  obtain ⟨hfs_res, hfs_st, _⟩ := feistelSplitBoundedProg_spec hv.N_le_U hinv.seed_bkt u
  change (Memory.spec 0).clientResult s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = _
    at hfs_res
  change (Memory.spec 0).clientState s (feistelSplitBoundedProg (fl.feistelCtx, u.val)) = s
    at hfs_st
  obtain ⟨hsc_st, hsc_res⟩ := fbScanProg_spec hv hinv u
  set slack' :=
    if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  have hctx : fl.toCtx = (fl.feistelCtx, (mp.toCtx, io.toCtx)) := rfl
  unfold fallbackDeleteProg; rw [hctx]
  rw [StateTransitionSpec.clientState_bind, hfs_st, hfs_res,
    StateTransitionSpec.clientState_bind, hsc_st]
  cases hs_u : s_abs u with
  | none =>
    rw [hs_u] at hsc_res
    have hr_ne1 : ((Memory.spec 0).clientResult s
        (fbScanProg ((mp.toCtx, io.toCtx),
          (epochBucket fl.c fl.U fl.N θ_bkt u, keyQuotient (bWhp fl.N) u.val)))).1 ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1, StateTransitionSpec.clientState_pure, ite_eq_left rfl,
      Function.update_eq_self_iff.mpr hs_u.symm]
    exact ⟨rfl, rfl, hinv.mono_slack (Nat.zero_le _) hsl_le, fun _ _ => rfl,
      fun _ => ⟨rfl, by rw [ite_eq_left rfl], fun _ _ => rfl⟩⟩
  | some v_old =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hhit_lt, _, how_hit, hpr_hit⟩ := hsc_res
    have hnone_f : ¬(some v_old = none) := by simp
    rw [ite_eq_left hr1, ite_eq_right hnone_f]; dsimp only
    obtain ⟨hfr', hns', hval', hio', href', hout_bp, hpg'⟩ :=
      fbDeleteSlotProg_spec hmv hiov hdisj hinv.fb_valid hinv.nSide_le hinv.io_inv hinv.refines
        hhit_lt u how_hit (by rw [hpr_hit])
    set s' := (Memory.spec 0).clientState s
      (fbDeleteSlotProg ((mp.toCtx, io.toCtx),
        ((Memory.spec 0).clientResult s
          (fbScanProg ((mp.toCtx, io.toCtx),
            (epochBucket fl.c fl.U fl.N θ_bkt u, keyQuotient (bWhp fl.N) u.val)))).2.1))
    have hout_tot : ∀ addr, ¬fl.OwnsAddr addr → s'.mem addr = s.mem addr := fun a ha =>
      hout_bp a (fun h => ha (Or.inr h))
    have hnot_m0 : ¬fl.OwnsAddr mp.metaBase := by
      dsimp only [mp] at hmv ⊢
      rintro (h2 | hma | hia)
      · omega
      · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
        · omega
        · omega
        · have := hmv.offBktMeta_ge; omega
      · exact hv.disjoint_hdr2 fl.bpL.mp.metaBase (Or.inl rfl) hia
    have hm2_not_bp : ¬(mp.OwnsMetaAddr (mp.metaBase + 2) ∨ io.OwnsAddr (mp.metaBase + 2)) := by
      rintro (hma | hia)
      · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
        · omega
        · omega
        · have := hmv.offBktMeta_ge; omega
      · exact hv.disjoint_hdr2 _ (Or.inr rfl) hia
    have hseed' : BitPackedDoubleTabulation.SeedRep (mp.metaBase + offBktHash) mp.w
        (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt
        s'.mem :=
      hinv.seed_bkt.congr_on hmv.w_pos fun a h1 h2 => by
        have hw_eq : mp.w = w := hmv.w_eq.symm
        rw [hw_eq] at h2
        exact hout_tot a (hv.not_owns_seeds h1 (by unfold offBktMeta offFpHash; omega))
    have hinv' : fl.StateInv slack' θ_bkt s'.mem (Function.update s_abs u none) :=
      { hdr_N := (hout_tot mp.metaBase hnot_m0).trans hinv.hdr_N
        mode_eq := (hout_bp _ hm2_not_bp).trans hinv.mode_eq
        seed_bkt := hseed'
        fb_valid := hval'
        nSide_le := hns'.trans_le ((Nat.sub_le _ 1).trans hinv.nSide_le)
        io_inv := hns'.symm ▸ hio'
        refines := hns'.symm ▸ href' }
    refine ⟨hfr', hns', hinv', hout_tot, fun hnz => ?_⟩
    rw [ite_eq_right hnone_f]; exact hpg' hnz

/-- `FallbackPool` `popAny` (`0 < nSide`), returning `(u.val, v.val)` and deleting slot `nSide - 1`
(`¬ReadsWidth`). -/
def fallbackPopAnyProg : FallbackOpCtx → Memory.Prog (ℕ × ℕ)
  | (fctx, (mctx, ioctx)) => do
    let nSide ← bpReadScalarProg (mctx, 1)
    if 0 < nSide then do
      let last ← pure (nSide - 1)
      let b_last ← fbOwnerOfProg (mctx, last)
      let qv ← slotIoReadRawProg (ioctx, last)
      let ((_, (wv, w0)), (_, (_, (_, bBits)))) := fctx
      if bBits ≤ w0 then do
        let qLim ← pure (w0 - bBits)
        if qLim < wv then
          if qv.1 < 1 <<< qLim then do
            let u_val ← feistelReconBoundedProg (fctx, (b_last, qv.1))
            fbDeleteSlotProg ((mctx, ioctx), last)
            pure (u_val, qv.2)
          else pure (0, 0)
        else pure (0, 0)
      else pure (0, 0)
    else pure (0, 0)

/-- Word width `fctx.1.2.1` in a `FeistelHashCtx`. -/
abbrev feistelCtxW (fctx : FeistelHashCtx) : ℕ := fctx.1.2.1

/-- Reduced-key bit-width `fctx.1.2.2` in a `FeistelHashCtx`. -/
abbrev feistelCtxW0 (fctx : FeistelHashCtx) : ℕ := fctx.1.2.2

/-- Bucket-index bit-width `fctx.2.2.2.2` in a `FeistelHashCtx`. -/
abbrev feistelCtxBBits (fctx : FeistelHashCtx) : ℕ := fctx.2.2.2.2

theorem realizesBounded_fallbackPopAny :
    RealizesBounded .exact fallbackPopAnyProg
      (WordEncoding.encode (α := FallbackOpCtx))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (fctx, (mctx, ioctx)) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier ∧
        feistelCtxW fctx = w ∧
        ∀ bkt q_val, q_val < 2 ^ (feistelCtxW0 fctx - feistelCtxBBits fctx) →
          FeistelReconPre w (fctx, (bkt, q_val)) s)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hfo := realizesBounded_fbOwnerOf
  have hsr := realizesBounded_slotIoReadRaw
  have hfr := realizesBounded_feistelRecon
  have hds := realizesBounded_fbDeleteSlot
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨_, _⟩, ⟨wv, w0⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, bBits⟩⟩⟩⟩, ⟨mctx, ioctx⟩⟩
    obtain ⟨hmv, hiov, hwv_eq, hrec⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hfo_all : ∀ x st, ((Memory.spec 0).runClient st (fbOwnerOfProg x)).2.1 = st :=
      state_fbOwnerOfProg
    have hsr_all : ∀ x st, ((Memory.spec 0).runClient st (slotIoReadRawProg x)).2.1 = st :=
      clientState_slotIoReadRawProg
    have hrec_all : ∀ x st, ((Memory.spec 0).runClient st (feistelReconBoundedProg x)).2.1 = st :=
      clientState_feistelReconBoundedProg
    have hw_lt_pow : w < 2 ^ w := Nat.lt_two_pow_self
    try simp only [StateTransitionSpec.clientState, runClient_state_bpReadScalarProg,
      hfo_all, hsr_all, hrec_all, Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | exact hw1 | (
      subst hwv_eq
      have hpow_lt : 1 <<< (w0 - bBits) < 2 ^ wv := by
        rw [Nat.shiftLeft_eq, one_mul]
        exact Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
      exact hpow_lt) | (
      apply hrec
      simp only [Nat.shiftLeft_eq, one_mul] at *
      assumption) | omega)

theorem fallbackPopAnyProg_spec {fl : FallbackLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv 0 θ_bkt s.mem s_abs)
    (hpos : 0 < (extractFallback fl.bpL.mp s.mem).nSide) :
    let fb := extractFallback fl.bpL.mp s.mem
    let s' := (Memory.spec 0).clientState s (fallbackPopAnyProg fl.toCtx)
    let uv := (Memory.spec 0).clientResult s (fallbackPopAnyProg fl.toCtx)
    let slack' :=
      if fl.bpL.io.usePaged = 0 ∨ (extractPageUnperm fl.bpL.io.pgL s.mem).cleanPhase = 0 then 0
      else 24
    s'.frontier = s.frontier ∧
    (extractFallback fl.bpL.mp s'.mem).nSide = fb.nSide - 1 ∧
    (∃ (u : Fin fl.U) (v : Fin fl.V),
      uv = (u.val, v.val) ∧
      s_abs u = some v ∧
      fl.StateInv slack' θ_bkt s'.mem (Function.update s_abs u none)) ∧
    (∀ addr, ¬fl.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.bpL.io.usePaged ≠ 0 →
      (extractPagePair fl.bpL.io.pgL s'.mem).virtLen fl.bpL.io.partner.side =
        (extractPagePair fl.bpL.io.pgL s.mem).virtLen fl.bpL.io.partner.side ∧
      (extractPagePair fl.bpL.io.pgL s'.mem).totalItems =
        (extractPagePair fl.bpL.io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair fl.bpL.io.pgL s.mem).virtLen fl.bpL.io.partner.side,
        slotIoPairAt fl.bpL.io.partner s'.mem idx = slotIoPairAt fl.bpL.io.partner s.mem idx) := by
  dsimp only
  let mp := fl.bpL.mp
  let io := fl.bpL.io
  set fb := extractFallback mp s.mem
  set last := fb.nSide - 1
  have hlast_lt : last < fb.nSide := Nat.sub_lt hpos Nat.one_pos
  have hmv : mp.Valid w s.frontier := hv.bp_valid.mp_valid
  have hiov : io.Valid io.pgL.w s.frontier :=
    hv.bp_valid.w_eq_io ▸ hmv.w_eq.symm ▸ hv.bp_valid.io_valid
  have hdisj := hv.bp_valid.disjoint
  have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
    have := hmv.M_ge; have := hmv.K_ge; nlinarith
  have how_r := fbOwnerOfProg_spec hmv hinv.fb_valid h6lt8 hinv.nSide_le hlast_lt
  obtain ⟨hpr_r, hpr_s⟩ := slotIoReadProg_spec hinv.io_inv hlast_lt
  unfold slotIoReadProg at hpr_r hpr_s
  obtain ⟨hu_lt, hv_lt, hfb_u, hkq_u, hs_top⟩ := hinv.refines.slot_key_val hlast_lt
  let u_top : Fin fl.U :=
    ⟨feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
      (fb.owner last) (slotIoPairAt io s.mem last).1, hu_lt⟩
  let v_top : Fin fl.V := ⟨(slotIoPairAt io s.mem last).2, hv_lt⟩
  have hbw_pos : 1 ≤ bWhp fl.N := by
    have hM_ge : 2 ≤ 2 ^ bWhp fl.N := by
      have h1 := hmv.M_ge; dsimp only [mp] at h1; rw [hv.mp_eq] at h1; exact h1
    by_contra hz
    have h0 : bWhp fl.N = 0 := by omega
    rw [h0] at hM_ge; omega
  have hle : bWhp fl.N ≤ keyBits fl.U := by
    unfold bWhp keyBits
    exact (Nat.sub_le _ _).trans ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
  have hrw_eq : redWidthWhp fl.U = keyBits fl.U := max_eq_right (by omega)
  have hqLim_eq : redWidthWhp fl.U - bWhp fl.N = quotBitsWhp fl.U fl.N := by
    rw [hrw_eq]; rfl
  have hbw_le_rw : bWhp fl.N ≤ redWidthWhp fl.U := hrw_eq ▸ hle
  have hq_qb : (slotIoPairAt io s.mem last).1 < 2 ^ quotBitsWhp fl.U fl.N := by
    rw [← hkq_u]; exact keyQuotient_bWhp_lt hv.N_le_U u_top
  have hqb_lt_wv : redWidthWhp fl.U - bWhp fl.N < mp.w := by
    have hsum : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ w := by
      unfold quotBitsWhp; rw [Nat.sub_add_cancel hle]
      exact Nat.clog_le_of_le_pow hv.fits_U.le
    rw [hqLim_eq, hmv.w_eq.symm]; omega
  have hq_sh : (slotIoPairAt io s.mem last).1 < 1 <<< (redWidthWhp fl.U - bWhp fl.N) := by
    rwa [hqLim_eq, Nat.shiftLeft_eq, one_mul]
  obtain ⟨hrec_r, hrec_s, _⟩ := feistelReconBoundedProg_spec hq_qb hinv.seed_bkt
    (bkt := fb.owner last)
  change (Memory.spec 0).clientResult s
    (feistelReconBoundedProg (fl.feistelCtx, (fb.owner last, (slotIoPairAt io s.mem last).1))) = _
    at hrec_r
  change (Memory.spec 0).clientState s
    (feistelReconBoundedProg (fl.feistelCtx, (fb.owner last, (slotIoPairAt io s.mem last).1))) = s
    at hrec_s
  obtain ⟨hfr', hns', hval', hio', href', hout_bp, hpg'⟩ :=
    fbDeleteSlotProg_spec hmv hiov hdisj hinv.fb_valid hinv.nSide_le hinv.io_inv hinv.refines
      hlast_lt u_top hfb_u.symm hkq_u.symm
  set s_del := (Memory.spec 0).clientState s (fbDeleteSlotProg ((mp.toCtx, io.toCtx), last))
  have hctx : fl.toCtx = (fl.feistelCtx, (mp.toCtx, io.toCtx)) := rfl
  have hns_mem : s.mem (mp.metaBase + 1) = fb.nSide := rfl
  have hst_tot : (Memory.spec 0).clientState s (fallbackPopAnyProg fl.toCtx) = s_del := by
    unfold fallbackPopAnyProg; rw [hctx]
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl), hns_mem, ite_eq_left hpos]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, state_fbOwnerOfProg, how_r,
      StateTransitionSpec.clientState_bind, hpr_s, hpr_r]
    change (Memory.spec 0).clientState s
      (if bWhp fl.N ≤ redWidthWhp fl.U then
        let qLim := pure (redWidthWhp fl.U - bWhp fl.N)
        qLim >>= fun ql =>
          if ql < mp.w then
            if (slotIoPairAt io s.mem last).1 < 1 <<< ql then _ else _
          else _
       else _) = s_del
    have hfb_ow : (extractFallback mp s.mem).owner last = fb.owner last := rfl
    rw [ite_eq_left hbw_le_rw]; simp only [pure_bind]
    rw [ite_eq_left hqb_lt_wv, ite_eq_left hq_sh, StateTransitionSpec.clientState_bind,
      hfb_ow, hrec_s, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have hres_tot : (Memory.spec 0).clientResult s (fallbackPopAnyProg fl.toCtx) =
      (u_top.val, v_top.val) := by
    unfold fallbackPopAnyProg; rw [hctx]
    rw [prog_clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl), hns_mem, ite_eq_left hpos]
    simp only [pure_bind]
    rw [prog_clientResult_bind, state_fbOwnerOfProg, how_r,
      prog_clientResult_bind, hpr_s, hpr_r]
    change (Memory.spec 0).clientResult s
      (if bWhp fl.N ≤ redWidthWhp fl.U then
        let qLim := pure (redWidthWhp fl.U - bWhp fl.N)
        qLim >>= fun ql =>
          if ql < mp.w then
            if (slotIoPairAt io s.mem last).1 < 1 <<< ql then _ else _
          else _
       else _) = _
    have hfb_ow : (extractFallback mp s.mem).owner last = fb.owner last := rfl
    rw [ite_eq_left hbw_le_rw]; simp only [pure_bind]
    rw [ite_eq_left hqb_lt_wv, ite_eq_left hq_sh, prog_clientResult_bind, hfb_ow, hrec_s, hrec_r,
      prog_clientResult_bind, prog_clientResult_pure]
  rw [hst_tot, hres_tot]
  have hout_tot : ∀ addr, ¬fl.OwnsAddr addr → s_del.mem addr = s.mem addr := fun a ha =>
    hout_bp a (fun h => ha (Or.inr h))
  have hnot_m0 : ¬fl.OwnsAddr mp.metaBase := by
    dsimp only [mp] at hmv ⊢
    rintro (h2 | hma | hia)
    · omega
    · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
      · omega
      · omega
      · have := hmv.offBktMeta_ge; omega
    · exact hv.disjoint_hdr2 fl.bpL.mp.metaBase (Or.inl rfl) hia
  have hm2_not_bp : ¬(mp.OwnsMetaAddr (mp.metaBase + 2) ∨ io.OwnsAddr (mp.metaBase + 2)) := by
    rintro (hma | hia)
    · rcases BpMetaLayout.OwnsMetaAddr.bounds hmv hma with (h1 | h10) | htab
      · omega
      · omega
      · have := hmv.offBktMeta_ge; omega
    · exact hv.disjoint_hdr2 _ (Or.inr rfl) hia
  have hseed' : BitPackedDoubleTabulation.SeedRep (mp.metaBase + offBktHash) mp.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt
      s_del.mem :=
    hinv.seed_bkt.congr_on hmv.w_pos fun a h1 h2 => by
      have hw_eq : mp.w = w := hmv.w_eq.symm
      rw [hw_eq] at h2
      exact hout_tot a (hv.not_owns_seeds h1 (by unfold offBktMeta offFpHash; omega))
  set slack' :=
    if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hinv' : fl.StateInv slack' θ_bkt s_del.mem (Function.update s_abs u_top none) :=
    { hdr_N := (hout_tot mp.metaBase hnot_m0).trans hinv.hdr_N
      mode_eq := (hout_bp _ hm2_not_bp).trans hinv.mode_eq
      seed_bkt := hseed'
      fb_valid := hval'
      nSide_le := hns'.trans_le ((Nat.sub_le _ 1).trans hinv.nSide_le)
      io_inv := hns'.symm ▸ hio'
      refines := hns'.symm ▸ href' }
  exact ⟨hfr', hns', ⟨u_top, v_top, rfl, hs_top, hinv'⟩, hout_tot, hpg'⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic `1 · OPT` Fallback Pool Primitives (`LargeFallbackBase`)

Low-level maintenance primitives and block-compaction loops for the deterministic `1 · OPT`
`FallbackPool` (`fallbackMode = 1`) in
[Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]:

1. **Conditional Promotion and Block Demotion**: `fbMaybePromoteProg` and `fbDemoteBlkProg`,
   together with functional specifications preserving `FallbackState.Valid` and `PoolItemsRefines`.
2. **Tail Pop and Slot Deletion**: `fbPopTailAtProg` and `fbDeleteSlotProg` removing any item slot
   `hitP < nSide` in place without exceeding the `1 · OPT` frontier.
3. **Transition Drain and Compaction Loops**: `topSwap` drain and pure-slab prefix compaction loops
   shared with `enterFallbackProg` in
   `CslibFrontier/DataStructure/Dictionary/WordRAM/ResizableSuccinctWhp/LargeEpochFallback.lean`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.fbMaybePromoteProg`,
  `fbDemoteBlkProg`, `fbPopTailAtProg`, `fbDeleteSlotProg`.

## Main results

* `fbMaybePromoteProg_spec`, `fbDemoteBlkProg_spec`, `fbPopTailAtProg_spec`,
  `fbDeleteSlotProg_spec`.
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

/-! ## Section 1: Conditional Promotion and Block Demotion -/

private def fbMaybePromoteInnerProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, ioctx), (nSide, fbBase)) => do
    let (_, (((m, k), _), _)) := mctx
    if fbBase ≤ nSide then
      if 5 * m * k < nSide - fbBase then
        fbPromoteOneBlockProg (mctx, ioctx)
      else pure ()
    else pure ()

private theorem realizesBounded_fbMaybePromoteInner :
    RealizesBounded .exact fbMaybePromoteInnerProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hpr := realizesBounded_fbPromoteOneBlock
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨nSide, fbBase⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    have h8mk := hmv.eight_MK_le
    have hns_w : nSide < 2 ^ w := hwords 27
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge h8mk
    have h5_w : 5 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    have h5m : 5 * m ≤ 8 * m * k := by nlinarith
    have h5mk : 5 * m * k ≤ 8 * m * k := by nlinarith
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega)

private def fbMaybePromoteCheckProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, ioctx), (nSide, fb0)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if nSide ≤ nCap then
      if fb0 ≤ nCap / k then do
        let fbBase ← pure (fb0 * k)
        fbMaybePromoteInnerProg ((mctx, ioctx), (nSide, fbBase))
      else pure ()
    else pure ()

private theorem realizesBounded_fbMaybePromoteCheck :
    RealizesBounded .exact fbMaybePromoteCheckProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hin := realizesBounded_fbMaybePromoteInner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨nSide, fb0⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega | (
      have hfb_mul : fb0 * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      omega))

/-- Conditionally promote one heavy tail block if `5 * M * K < tailLen`, guaranteeing
`tailLen' + K ≤ 6 * M * K` (`¬ReadsWidth`). -/
def fbMaybePromoteProg : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    let nSide ← bpReadScalarProg (mctx, 1)
    let fb0 ← bpReadScalarProg (mctx, 10)
    fbMaybePromoteCheckProg ((mctx, ioctx), (nSide, fb0))

theorem frontier_fbMaybePromoteProg (ctx : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx ctx.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbMaybePromoteProg ctx)).frontier = s.frontier := by
  rcases ctx with ⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩
  unfold fbMaybePromoteProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  unfold fbMaybePromoteCheckProg fbMaybePromoteInnerProg; dsimp only
  split_ifs
  · simp only [pure_bind]; split_ifs
    · exact frontier_fbPromoteOneBlockProg _ s hw
    all_goals rfl
  all_goals rfl

theorem realizesBounded_fbMaybePromote :
    RealizesBounded .exact fbMaybePromoteProg
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hchk := realizesBounded_fbMaybePromoteCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | exact hw1 | exact h10_w)

theorem fbMaybePromoteProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits w slack : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).Valid)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractFallback mp s.mem).nSide slack s.mem)
    (href : PoolItemsRefines U V bBits hBkt (extractFallback mp s.mem).nSide
      (extractFallback mp s.mem).owner (slotIoPairAt io s.mem) s_abs) :
    let fb := extractFallback mp s.mem
    let s' := (Memory.spec 0).clientState s (fbMaybePromoteProg (mp.toCtx, io.toCtx))
    let fb' := extractFallback mp s'.mem
    s'.frontier = s.frontier ∧
    fb'.nSide = fb.nSide ∧
    fb.fullBlocks ≤ fb'.fullBlocks ∧
    fb'.tailLen + mp.K ≤ 6 * mp.M * mp.K ∧
    fb'.Valid ∧
    io.StateInv fb.nSide slack s'.mem ∧
    PoolItemsRefines U V bBits hBkt fb.nSide fb'.owner (slotIoPairAt io s'.mem) s_abs ∧
    (∀ p < fb.fullBlocks * mp.K,
      slotIoPairAt io s'.mem p = slotIoPairAt io s.mem p ∧ fb'.owner p = fb.owner p) ∧
    (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → s'.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s'.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  set fb := extractFallback mp s.mem
  have hfb_def : extractFallback mp s.mem = fb := rfl
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  have hfb_K : fb.K = mp.K := rfl
  have hfb_M : fb.M = mp.M := rfl
  have hbl_le : fb.fullBlocks * mp.K ≤ fb.nSide := hfb_K ▸ hfb.blocks_le
  have hfb_div : fb.fullBlocks ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hbl_le.trans hns_le)
  unfold fbMaybePromoteProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inl rfl),
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩)]
  unfold fbMaybePromoteCheckProg; dsimp only
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
  have hm_eq : mp.toCtx.2.1.1.1 = mp.M := rfl
  have hns_mem : s.mem (mp.metaBase + 1) = fb.nSide := rfl
  have hfb_mem : s.mem (mp.metaBase + 10) = fb.fullBlocks := rfl
  rw [hns_mem, hfb_mem, hnc_eq, hk_eq, ite_eq_left hns_le, ite_eq_left hfb_div]
  simp only [pure_bind]
  unfold fbMaybePromoteInnerProg; dsimp only
  rw [hm_eq, hk_eq, ite_eq_left hbl_le]
  have htl_sub : fb.nSide - fb.fullBlocks * mp.K = fb.tailLen := rfl
  rw [htl_sub]
  by_cases hgt : 5 * mp.M * mp.K < fb.tailLen
  · rw [ite_eq_left hgt]
    have hmk_le : mp.M * mp.K ≤ fb.tailLen := by nlinarith
    obtain ⟨hfr, hns, hblk, htl, hval, hio', href', hlow, hout, hpg⟩ :=
      fbPromoteOneBlockProg_spec hmv hiov hdisj hfb hns_le hio href hmk_le
    rw [hfb_def] at hns hblk htl hio' href' hlow
    refine ⟨hfr, hns, by omega, ?_, hval, hio', href', hlow, hout, hpg⟩
    have h6 : fb.tailLen ≤ 6 * mp.M * mp.K := by
      have h := hfb.tail_le; rwa [hfb_M, hfb_K] at h
    rw [htl]
    have hk_mk : mp.K ≤ mp.M * mp.K := Nat.le_mul_of_pos_left _ (by have := hmv.M_ge; omega)
    omega
  · rw [ite_eq_right hgt, StateTransitionSpec.clientState_pure]
    rw [hfb_def]
    have hle5 : fb.tailLen ≤ 5 * mp.M * mp.K := Nat.le_of_not_lt hgt
    have hk_mk : mp.K ≤ mp.M * mp.K := Nat.le_mul_of_pos_left _ (by have := hmv.M_ge; omega)
    have h56 : 5 * mp.M * mp.K + mp.M * mp.K = 6 * mp.M * mp.K := by ring
    exact ⟨rfl, rfl, le_rfl, by omega, hfb, hio, href, fun _ _ => ⟨rfl, rfl⟩,
      fun _ _ => rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩

/-- Right-shift `ownerTail[0 .. tailLen)` by `k` slots (`rem` counts down `tailLen .. 1`). -/
private def fbShiftRightStepProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((mctx, k), rem) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if 0 < rem then
      if rem ≤ nCap then
        if k ≤ nCap - rem then do
          let idx ← pure (rem - 1)
          let v ← bpReadTailDirRawProg (mctx, idx)
          bpWriteTailDirRawProg ((mctx, idx + k), v)
          pure idx
        else pure rem
      else pure rem
    else pure rem

private theorem memoryCost_fbShiftRightStep_pos (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (fbShiftRightStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩, _⟩
  simp [fbShiftRightStepProg, bpReadScalarProg]

private theorem frontier_fbShiftRightStep (d : BpMetaCtx × ℕ) (rem : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbShiftRightStepProg (d, rem))).frontier = s.frontier := by
  rcases d with ⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, k⟩
  unfold fbShiftRightStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
      frontier_bpWriteTailDirRawProg]
  all_goals rfl

private theorem realizesBounded_fbShiftRightStep :
    RealizesBounded .exact fbShiftRightStepProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrtd := realizesBounded_bpReadTailDirRaw
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, k_sh⟩, rem⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hk_w : k_sh < 2 ^ w := hwords 14
    have hr_w : rem < 2 ^ w := hwords 15
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg, runClient_state_bpReadTailDirRawProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hw1 | omega)

private def fbShiftRightLoopProg : ((BpMetaCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((d, rem), fuel) => iterate fbShiftRightStepProg d fuel rem

private theorem realizesBounded_fbShiftRightLoop :
    RealizesBounded .exact fbShiftRightLoopProg
      (WordEncoding.encode (α := ((BpMetaCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((d, rem), fuel) s =>
        iterationSafe fbShiftRightStepProg
          (fun w' ((mctx, _), _) s' => (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier)
          w d fuel rem s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BpMetaCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_fbShiftRightStep
    memoryCost_fbShiftRightStep_pos

/-- Fill `ownerTail[0 .. K)` with `b_val`. -/
private def fbFillHeadStepProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((mctx, b_val), i) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if i < nCap then do
      bpWriteTailDirRawProg ((mctx, i), b_val)
      pure (i + 1)
    else pure i

private theorem memoryCost_fbFillHeadStep_pos (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (fbFillHeadStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩, _⟩
  simp [fbFillHeadStepProg, bpReadScalarProg]

private theorem frontier_fbFillHeadStep (d : BpMetaCtx × ℕ) (i : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbFillHeadStepProg (d, i))).frontier = s.frontier := by
  rcases d with ⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, b_val⟩
  unfold fbFillHeadStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
      frontier_bpWriteTailDirRawProg]
  · rfl

private theorem realizesBounded_fbFillHeadStep :
    RealizesBounded .exact fbFillHeadStepProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, b_val⟩, i⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hi_w : i < 2 ^ w := hwords 15
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hw1 | omega)

private def fbFillHeadLoopProg : ((BpMetaCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((d, i), fuel) => iterate fbFillHeadStepProg d fuel i

private theorem realizesBounded_fbFillHeadLoop :
    RealizesBounded .exact fbFillHeadLoopProg
      (WordEncoding.encode (α := ((BpMetaCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((d, i), fuel) s =>
        iterationSafe fbFillHeadStepProg
          (fun w' ((mctx, _), _) s' => (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier)
          w d fuel i s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BpMetaCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_fbFillHeadStep
    memoryCost_fbFillHeadStep_pos

/-- Read `(ownerBlk b₁, ownerBlk b₂)` (`2` binds). -/
private def fbReadBlkPairProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (mctx, (blk₁, blk₂)) => do
    let o₁ ← bpReadSlabOwnerProg (mctx, (blk₁, 1))
    let o₂ ← bpReadSlabOwnerProg (mctx, (blk₂, 1))
    pure (o₁, o₂)

private theorem state_fbReadBlkPairProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbReadBlkPairProg x) = s := by
  rcases x with ⟨mctx, ⟨blk₁, blk₂⟩⟩
  unfold fbReadBlkPairProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg]
  rfl

private theorem realizesBounded_fbReadBlkPair :
    RealizesBounded .exact fbReadBlkPairProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (mctx, _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  realize
  all_goals (
    rcases d with ⟨mctx, ⟨blk₁, blk₂⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_state_bpReadSlabOwnerProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hw1)

/-- Write `(o₂, o₁)` to `ownerBlk[blk₁]` and `ownerBlk[blk₂]` (`2` binds). -/
private def fbWriteBlkPairProg : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, (blk₁, blk₂)), (o₁, o₂)) => do
    bpWriteSlabOwnerProg ((mctx, (blk₁, 1)), o₂)
    bpWriteSlabOwnerProg ((mctx, (blk₂, 1)), o₁)

private theorem frontier_fbWriteBlkPairProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbWriteBlkPairProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ⟨blk₁, blk₂⟩⟩, ⟨o₁, o₂⟩⟩
  unfold fbWriteBlkPairProg
  rw [StateTransitionSpec.clientState_bind, frontier_bpWriteSlabOwnerProg,
    frontier_bpWriteSlabOwnerProg]

private theorem realizesBounded_fbWriteBlkPair :
    RealizesBounded .exact fbWriteBlkPairProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ⟨blk₁, blk₂⟩⟩, ⟨o₁, o₂⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_frontier_bpWriteSlabOwnerProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hw1)

private def fbDemoteSwapBodyProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | ((mctx, ioctx), (blk, lastBlk)) => do
    let (_, (((_, k), _), _)) := mctx
    let os ← fbReadBlkPairProg (mctx, (blk, lastBlk))
    fbSwapRangeProg (((mctx, ioctx), (blk * k, lastBlk * k)), k)
    fbWriteBlkPairProg ((mctx, (blk, lastBlk)), os)
    pure os.1

private theorem frontier_fbDemoteSwapBodyProg (x : BlockPoolCtx × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbDemoteSwapBodyProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, ⟨blk, lastBlk⟩⟩
  set mctx : BpMetaCtx := (p1, (((m, k), p2b), (mt, nCap)))
  unfold fbDemoteSwapBodyProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, state_fbReadBlkPairProg,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_pure, frontier_fbWriteBlkPairProg]
  exact frontier_fbSwapRangeProg ((mctx, ioctx), (blk * k, lastBlk * k)) k s hw

private theorem realizesBounded_fbDemoteSwapBody :
    RealizesBounded .exact fbDemoteSwapBodyProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, ioctx), (blk, lastBlk)) s =>
        blk ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        lastBlk ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrb := realizesBounded_fbReadBlkPair
  have hsr := realizesBounded_fbSwapRange
  have hwb := realizesBounded_fbWriteBlkPair
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨blk, lastBlk⟩⟩
    obtain ⟨hblk_d, hlast_d, hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hblk_d hlast_d hnc_w hK_ge
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hrb_s : ((Memory.spec 0).runClient s (fbReadBlkPairProg (mctx, (blk, lastBlk)))).2.1 = s :=
      state_fbReadBlkPairProg _ s
    dsimp only [mctx] at hrb_s
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hrb_s]
    first | exact hmv | exact hiov | (
      have h1 : blk * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp hblk_d
      omega) | (
      have h2 : lastBlk * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp hlast_d
      omega) | (
      have hfr := frontier_fbSwapRangeProg ((mctx, ioctx), (blk * k, lastBlk * k)) k s hiov.w_pos
      dsimp only [mctx, StateTransitionSpec.clientState] at hfr
      rw [hfr]; exact hmv))

/-- Swap full block `blk` with `lastBlk` in both `slotIo` and `ownerBlk`, returning `b_blk`. -/
private def fbDemoteSwapProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog ℕ
  | ((mctx, ioctx), (blk, lastBlk)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if blk ≤ nCap / k then
      if lastBlk ≤ nCap / k then
        fbDemoteSwapBodyProg ((mctx, ioctx), (blk, lastBlk))
      else pure 0
    else pure 0

private theorem frontier_fbDemoteSwapProg (x : BlockPoolCtx × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbDemoteSwapProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, ⟨blk, lastBlk⟩⟩
  unfold fbDemoteSwapProg; dsimp only
  split_ifs
  · exact frontier_fbDemoteSwapBodyProg _ s hw
  all_goals rfl

private theorem realizesBounded_fbDemoteSwap :
    RealizesBounded .exact fbDemoteSwapProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hbd := realizesBounded_fbDemoteSwapBody
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨blk, lastBlk⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega)

/-- Right-shift `ownerTail` by `K`, fill `ownerTail[0 .. K)` with `b_blk`, and set
`fullBlocks := lastBlk` (`3` binds). -/
private def fbDemoteTailProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((mctx, (lastBlk, tailLen)), b_blk) => do
    let (_, (((_, k), _), _)) := mctx
    let _ ← fbShiftRightLoopProg ((((mctx, k), tailLen)), tailLen)
    let z0 ← pure 0
    let _ ← fbFillHeadLoopProg ((((mctx, b_blk), z0)), k)
    bpWriteScalarProg ((mctx, 10), lastBlk)

private theorem frontier_fbDemoteTailProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbDemoteTailProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, p2c⟩⟩, ⟨lastBlk, tailLen⟩⟩, b_blk⟩
  set mctx : BpMetaCtx := (p1, (((m, k), p2b), p2c))
  unfold fbDemoteTailProg; dsimp only; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    frontier_bpWriteScalarProg]
  set s₁ := (Memory.spec 0).clientState s (fbShiftRightLoopProg (((mctx, k), tailLen), tailLen))
  have hfr₂ := (iterationSafe_of_frontier fbFillHeadStepProg
    (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbFillHeadStep d' a' st)
    (d := (mctx, b_blk)) (s := s₁) trivial k 0).2
  have hfr₁ := (iterationSafe_of_frontier fbShiftRightStepProg
    (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbShiftRightStep d' a' st)
    (d := (mctx, k)) (s := s) trivial tailLen tailLen).2
  exact hfr₂.trans hfr₁

private theorem realizesBounded_fbDemoteTail :
    RealizesBounded .exact fbDemoteTailProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsrl := realizesBounded_fbShiftRightLoop
  have hfhl := realizesBounded_fbFillHeadLoop
  have hws := realizesBounded_bpWriteScalar
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨lastBlk, tailLen⟩⟩, b_blk⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    try dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact h10_w | omega | (
      exact (iterationSafe_of_frontier fbShiftRightStepProg
        (fun w' (d' : BpMetaCtx × ℕ) fr' => (BpMetaLayout.ofCtx d'.1).Valid w' fr')
        (fun d' a' st _ => frontier_fbShiftRightStep d' a' st)
        (d := (mctx, k)) (s := s) hmv tailLen tailLen).1) | (
      have hfr₁ := (iterationSafe_of_frontier fbShiftRightStepProg
        (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbShiftRightStep d' a' st)
        (d := (mctx, k)) (s := s) trivial tailLen tailLen).2
      set s₁ := ((Memory.spec 0).runClient s _).2.1
      have hs₁_fr : s₁.frontier = s.frontier := hfr₁
      exact (iterationSafe_of_frontier fbFillHeadStepProg
        (fun w' (d' : BpMetaCtx × ℕ) fr' => (BpMetaLayout.ofCtx d'.1).Valid w' fr')
        (fun d' a' st _ => frontier_fbFillHeadStep d' a' st)
        (d := (mctx, b_blk)) (s := s₁) (hs₁_fr.symm ▸ hmv) k 0).1) | (
      have hfr₁ := (iterationSafe_of_frontier fbShiftRightStepProg
        (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbShiftRightStep d' a' st)
        (d := (mctx, k)) (s := s) trivial tailLen tailLen).2
      set s₁ := ((Memory.spec 0).runClient s _).2.1
      have hfr₂ := (iterationSafe_of_frontier fbFillHeadStepProg
        (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbFillHeadStep d' a' st)
        (d := (mctx, b_blk)) (s := s₁) trivial k 0).2
      dsimp only [s₁, mctx] at hfr₁ hfr₂ ⊢
      try unfold fbShiftRightLoopProg fbFillHeadLoopProg at *
      dsimp only [StateTransitionSpec.clientState] at hfr₁ hfr₂ ⊢
      rw [hfr₂, hfr₁]; exact hmv))

private def fbDemoteInnerProg : (BlockPoolCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), (blk, fb0)), (nSide, fbBase)) => do
    let (_, (_, (_, nCap))) := mctx
    if fbBase ≤ nSide then
      if nSide ≤ nCap then do
        let lastBlk ← pure (fb0 - 1)
        let tailLen ← pure (nSide - fbBase)
        let b_blk ← fbDemoteSwapProg ((mctx, ioctx), (blk, lastBlk))
        fbDemoteTailProg ((mctx, (lastBlk, tailLen)), b_blk)
      else pure ()
    else pure ()

private theorem realizesBounded_fbDemoteInner :
    RealizesBounded .exact fbDemoteInnerProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), (blk, fb0)), _) s =>
        blk < fb0 ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hds := realizesBounded_fbDemoteSwap
  have hdt := realizesBounded_fbDemoteTail
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨blk, fb0⟩⟩, ⟨nSide, fbBase⟩⟩
    obtain ⟨hblk_lt, hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hfb0_w : fb0 < 2 ^ w := hwords 28
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | omega | (
      have hfr := frontier_fbDemoteSwapProg ((mctx, ioctx), (blk, fb0 - 1)) s hiov.w_pos
      dsimp only [mctx, StateTransitionSpec.clientState] at hfr
      rw [hfr]; exact hmv))

private def fbDemoteCheckProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), blk), (nSide, fb0)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if blk < fb0 then
      if fb0 ≤ nCap / k then do
        let fbBase ← pure (fb0 * k)
        fbDemoteInnerProg (((mctx, ioctx), (blk, fb0)), (nSide, fbBase))
      else pure ()
    else pure ()

private theorem realizesBounded_fbDemoteCheck :
    RealizesBounded .exact fbDemoteCheckProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hin := realizesBounded_fbDemoteInner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, blk⟩, ⟨nSide, fb0⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega | (
      have hfb_mul : fb0 * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      omega))

/-- Demote full block `blk < fullBlocks` (`tailLen + K ≤ 6 * M * K`) by swapping it with
`lastBlk = fullBlocks - 1` and absorbing `[lastBlk * K, fullBlocks * K)` into `ownerTail[0 .. K)`
(`¬ReadsWidth`). -/
def fbDemoteBlkProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), blk) => do
    let nSide ← bpReadScalarProg (mctx, 1)
    let fb0 ← bpReadScalarProg (mctx, 10)
    fbDemoteCheckProg (((mctx, ioctx), blk), (nSide, fb0))

theorem frontier_fbDemoteBlkProg (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpCtxIo x)).pgL.w) :
    ((Memory.spec 0).clientState s (fbDemoteBlkProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, blk⟩
  unfold fbDemoteBlkProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  unfold fbDemoteCheckProg; dsimp only
  split_ifs
  · simp only [pure_bind]
    unfold fbDemoteInnerProg; dsimp only
    split_ifs
    · simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind, frontier_fbDemoteTailProg]
      exact frontier_fbDemoteSwapProg _ s hw
    all_goals rfl
  all_goals rfl

theorem realizesBounded_fbDemoteBlk :
    RealizesBounded .exact fbDemoteBlkProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hchk := realizesBounded_fbDemoteCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, blk⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | exact hw1 | exact h10_w)

private theorem fbShiftRightLoop_spec {mp : BpMetaLayout}
    {w fr₀ ns₀ fb0 tailLen : ℕ} {ot₀ ob₀ : ℕ → ℕ} {s_base : Memory.State}
    (hmv : mp.Valid w fr₀)
    (htl_plus : tailLen + mp.K ≤ 8 * mp.M * mp.K)
    (htl_kp_nc : tailLen + mp.K ≤ mp.nCap)
    (hot_M : ∀ i < tailLen, ot₀ i < mp.M) :
    ∀ fuel rem (st : Memory.State),
      st.frontier = fr₀ →
      rem = fuel →
      rem ≤ tailLen →
      (extractFallback mp st.mem).nSide = ns₀ →
      (extractFallback mp st.mem).fullBlocks = fb0 →
      (extractFallback mp st.mem).ownerBlk = ob₀ →
      (∀ i < rem, (extractFallback mp st.mem).ownerTail i = ot₀ i) →
      (∀ j, rem ≤ j → j < tailLen → (extractFallback mp st.mem).ownerTail (j + mp.K) = ot₀ j) →
      (∀ addr, ¬mp.OwnsMetaAddr addr → st.mem addr = s_base.mem addr) →
      let st' :=
        (Memory.spec 0).clientState st (iterate fbShiftRightStepProg (mp.toCtx, mp.K) fuel rem)
      st'.frontier = fr₀ ∧
      (extractFallback mp st'.mem).nSide = ns₀ ∧
      (extractFallback mp st'.mem).fullBlocks = fb0 ∧
      (extractFallback mp st'.mem).ownerBlk = ob₀ ∧
      (∀ j < tailLen, (extractFallback mp st'.mem).ownerTail (j + mp.K) = ot₀ j) ∧
      (∀ addr, ¬mp.OwnsMetaAddr addr → st'.mem addr = s_base.mem addr) := by
  have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
    have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  intro fuel; induction fuel with
  | zero =>
    intro rem st hfr hrem _ hns hfb_eq hob _ hhi hout
    subst hrem
    exact ⟨hfr, hns, hfb_eq, hob, fun j hj => hhi j (Nat.zero_le _) hj, hout⟩
  | succ f ih =>
    intro rem st hfr hrem hle_tl hns hfb_eq hob hlo hhi hout
    subst hrem
    have hpos : 0 < f + 1 := Nat.succ_pos f
    have hf_tl : f < tailLen := by omega
    have hrem_nc : f + 1 ≤ mp.nCap := by omega
    have hk_sub : mp.K ≤ mp.nCap - (f + 1) := by omega
    have hf_8 : f < 8 * mp.M * mp.K := by omega
    have hfk_8 : f + mp.K < 8 * mp.M * mp.K := by omega
    have hv_eq : (extractFallback mp st.mem).ownerTail f = ot₀ f := hlo f (Nat.lt_succ_self f)
    have hv_M : ot₀ f < mp.M := hot_M f hf_tl
    have hv_nc : ot₀ f ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
    have hv_pb : ot₀ f < 2 ^ mp.ptrB := lt_of_le_of_lt hv_nc hmv.nCap_lt_ptrB
    have hr_f : (Memory.spec 0).clientResult st (bpReadTailDirRawProg (mp.toCtx, f)) = ot₀ f := by
      unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
      rw [ite_eq_left hf_8, clientResult_readPackedCompGenProg]
      have : (extractFallback mp st.mem).ownerTail f =
          readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w st.mem f := by
        unfold extractFallback; dsimp only; rw [ite_eq_left hf_8]
      exact this.symm.trans hv_eq
    set st₁ :=
      (Memory.spec 0).clientState st (bpWriteTailDirRawProg ((mp.toCtx, f + mp.K), ot₀ f))
    have hstep_st : (Memory.spec 0).clientState st
        (fbShiftRightStepProg ((mp.toCtx, mp.K), f + 1)) = st₁ := by
      unfold fbShiftRightStepProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
      rw [hnc_eq, ite_eq_left hpos, ite_eq_left hrem_nc, ite_eq_left hk_sub]
      simp only [pure_bind, Nat.add_sub_cancel]
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg, hr_f,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    have hstep_res : (Memory.spec 0).clientResult st
        (fbShiftRightStepProg ((mp.toCtx, mp.K), f + 1)) = f := by
      unfold fbShiftRightStepProg
      rw [prog_clientResult_bind, clientState_bpReadScalarProg]; dsimp only
      rw [hnc_eq, ite_eq_left hpos, ite_eq_left hrem_nc, ite_eq_left hk_sub]
      simp only [pure_bind, Nat.add_sub_cancel, prog_clientResult_bind]
      rw [clientState_bpReadTailDirRawProg, hr_f, prog_clientResult_pure]
    have hwf := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge (f + mp.K) (ot₀ f)
    have hfb₁ := extractFallback_writeOwnerTail (hfr.symm ▸ hmv) hfk_8 hv_pb hv_nc (s := st)
    unfold iterate; dsimp only
    rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
    refine ih f st₁ ((hwf.1.frontier_eq st).trans hfr) rfl hf_tl.le
      (by rw [hfb₁]; simp only; exact hns)
      (by rw [hfb₁]; simp only; exact hfb_eq)
      (by rw [hfb₁]; simp only; exact hob)
      (fun i hi => by
        rw [hfb₁]; simp only
        rw [Function.update_of_ne (by omega)]; exact hlo i (Nat.lt_succ_of_lt hi))
      (fun j hj1 hj2 => by
        rw [hfb₁]; simp only
        rcases eq_or_lt_of_le hj1 with rfl | hgt_f
        · exact Function.update_self ..
        · rw [Function.update_of_ne (by omega)]; exact hhi j hgt_f hj2)
      (fun a ha => (hwf.1.mem_outside st a ha).trans (hout a ha))

private theorem fbFillHeadLoop_spec {mp : BpMetaLayout}
    {w fr₀ ns₀ fb0 tailLen b_blk : ℕ} {ot₁ ob₀ : ℕ → ℕ} {s_base : Memory.State}
    (hmv : mp.Valid w fr₀)
    (hb_pb : b_blk < 2 ^ mp.ptrB) (hb_nc : b_blk ≤ mp.nCap) :
    ∀ fuel i (st : Memory.State),
      st.frontier = fr₀ →
      i + fuel = mp.K →
      (extractFallback mp st.mem).nSide = ns₀ →
      (extractFallback mp st.mem).fullBlocks = fb0 →
      (extractFallback mp st.mem).ownerBlk = ob₀ →
      (∀ j < i, (extractFallback mp st.mem).ownerTail j = b_blk) →
      (∀ j, mp.K ≤ j → j < tailLen + mp.K → (extractFallback mp st.mem).ownerTail j = ot₁ j) →
      (∀ addr, ¬mp.OwnsMetaAddr addr → st.mem addr = s_base.mem addr) →
      let st' :=
        (Memory.spec 0).clientState st (iterate fbFillHeadStepProg (mp.toCtx, b_blk) fuel i)
      st'.frontier = fr₀ ∧
      (extractFallback mp st'.mem).nSide = ns₀ ∧
      (extractFallback mp st'.mem).fullBlocks = fb0 ∧
      (extractFallback mp st'.mem).ownerBlk = ob₀ ∧
      (∀ j < mp.K, (extractFallback mp st'.mem).ownerTail j = b_blk) ∧
      (∀ j, mp.K ≤ j → j < tailLen + mp.K → (extractFallback mp st'.mem).ownerTail j = ot₁ j) ∧
      (∀ addr, ¬mp.OwnsMetaAddr addr → st'.mem addr = s_base.mem addr) := by
  have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
    have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  intro fuel; induction fuel with
  | zero =>
    intro i st hfr hsum hns hfb_eq hob hlo hhi hout
    have hi : i = mp.K := by omega
    subst hi; exact ⟨hfr, hns, hfb_eq, hob, hlo, hhi, hout⟩
  | succ f ih =>
    intro i st hfr hsum hns hfb_eq hob hlo hhi hout
    have hi_K : i < mp.K := by omega
    have hi_8 : i < 8 * mp.M * mp.K := by have := hmv.M_ge; nlinarith
    have hi_nc : i < mp.nCap := by have := hmv.twelve_K_le; omega
    set st₁ := (Memory.spec 0).clientState st (bpWriteTailDirRawProg ((mp.toCtx, i), b_blk))
    have hstep_st : (Memory.spec 0).clientState st
        (fbFillHeadStepProg ((mp.toCtx, b_blk), i)) = st₁ := by
      unfold fbFillHeadStepProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
      rw [hnc_eq, ite_eq_left hi_nc, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_pure]
    have hstep_res : (Memory.spec 0).clientResult st
        (fbFillHeadStepProg ((mp.toCtx, b_blk), i)) = i + 1 := by
      unfold fbFillHeadStepProg
      rw [prog_clientResult_bind, clientState_bpReadScalarProg]; dsimp only
      rw [hnc_eq, ite_eq_left hi_nc, prog_clientResult_bind, prog_clientResult_pure]
    have hwf := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge i b_blk
    have hfb₁ := extractFallback_writeOwnerTail (hfr.symm ▸ hmv) hi_8 hb_pb hb_nc (s := st)
    unfold iterate; dsimp only
    rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
    refine ih (i + 1) st₁ ((hwf.1.frontier_eq st).trans hfr) (by omega)
      (by rw [hfb₁]; simp only; exact hns)
      (by rw [hfb₁]; simp only; exact hfb_eq)
      (by rw [hfb₁]; simp only; exact hob)
      (fun j hj => by
        rw [hfb₁]; simp only
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hj_lt
        · exact Function.update_self ..
        · rw [Function.update_of_ne (by omega)]; exact hlo j hj_lt)
      (fun j hj1 hj2 => by
        rw [hfb₁]; simp only
        rw [Function.update_of_ne (by omega)]; exact hhi j hj1 hj2)
      (fun a ha => (hwf.1.mem_outside st a ha).trans (hout a ha))

theorem fbDemoteBlkProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits w slack blk : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).Valid)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (htl_plus : (extractFallback mp s.mem).tailLen + mp.K ≤ 6 * mp.M * mp.K)
    (hblk : blk < (extractFallback mp s.mem).fullBlocks)
    (hio : io.StateInv (extractFallback mp s.mem).nSide slack s.mem)
    (href : PoolItemsRefines U V bBits hBkt (extractFallback mp s.mem).nSide
      (extractFallback mp s.mem).owner (slotIoPairAt io s.mem) s_abs) :
    let fb := extractFallback mp s.mem
    let lastBlk := fb.fullBlocks - 1
    let s' := (Memory.spec 0).clientState s (fbDemoteBlkProg ((mp.toCtx, io.toCtx), blk))
    let fb' := extractFallback mp s'.mem
    s'.frontier = s.frontier ∧
    fb'.nSide = fb.nSide ∧
    fb'.fullBlocks = lastBlk ∧
    fb'.Valid ∧
    io.StateInv fb.nSide slack s'.mem ∧
    PoolItemsRefines U V bBits hBkt fb.nSide fb'.owner (slotIoPairAt io s'.mem) s_abs ∧
    (∀ off < mp.K,
      slotIoPairAt io s'.mem (lastBlk * mp.K + off) = slotIoPairAt io s.mem (blk * mp.K + off) ∧
      fb'.owner (lastBlk * mp.K + off) = fb.owner (blk * mp.K + off)) ∧
    (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → s'.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s'.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  set fb := extractFallback mp s.mem
  set fb0 := fb.fullBlocks
  set lastBlk := fb0 - 1
  set tailLen := fb.nSide - fb0 * mp.K
  have hfb_K : fb.K = mp.K := rfl
  have hfb_M : fb.M = mp.M := rfl
  have htl_def : fb.tailLen = tailLen := rfl
  have htl_plus' : tailLen + mp.K ≤ 6 * mp.M * mp.K := htl_def ▸ htl_plus
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  have hbl_le : fb0 * mp.K ≤ fb.nSide := hfb_K ▸ hfb.blocks_le
  have hfb_div : fb0 ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hbl_le.trans hns_le)
  have hblk_div : blk ≤ mp.nCap / mp.K := hblk.le.trans hfb_div
  have hlast_div : lastBlk ≤ mp.nCap / mp.K := (Nat.sub_le _ _).trans hfb_div
  have hlast_lt : lastBlk < fb0 := by omega
  have hfb_mb : fb0 ≤ mp.maxBlocks := by have := hmv.div_K_add_two_le; omega
  have hblk_mb : blk < mp.maxBlocks := hblk.trans_le hfb_mb
  have hlast_mb : lastBlk < mp.maxBlocks := hlast_lt.trans_le hfb_mb
  have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
    have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
  have hoso_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offSlabOwner := by
    have := hmv.offSlabOwner_ge; omega
  have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
    have := hmv.M_ge; have := hmv.K_ge; nlinarith
  set b_blk := fb.ownerBlk blk
  set b_last := fb.ownerBlk lastBlk
  have hb_blk_M : b_blk < mp.M := hfb_M ▸ hfb.blk_lt blk hblk
  have hb_last_M : b_last < mp.M := hfb_M ▸ hfb.blk_lt lastBlk hlast_lt
  have hb_blk_nc : b_blk ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
  have hb_last_nc : b_last ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
  have hb_blk_pb : b_blk < 2 ^ mp.ptrB := lt_of_le_of_lt hb_blk_nc hmv.nCap_lt_ptrB
  have hb_last_pb : b_last < 2 ^ mp.ptrB := lt_of_le_of_lt hb_last_nc hmv.nCap_lt_ptrB
  have hrb_res : (Memory.spec 0).clientResult s (fbReadBlkPairProg (mp.toCtx, (blk, lastBlk))) =
      (b_blk, b_last) := by
    unfold fbReadBlkPairProg
    rw [prog_clientResult_bind, clientState_bpReadSlabOwnerProg]
    have hr1 : (Memory.spec 0).clientResult s (bpReadSlabOwnerProg (mp.toCtx, (blk, 1))) =
        b_blk := by
      unfold bpReadSlabOwnerProg; dsimp only [BpMetaLayout.toCtx, b_blk, fb, extractFallback]
      rw [ite_eq_left ⟨hblk_mb, by decide⟩, ite_eq_left hblk_mb]
      simp [pure_bind, clientResult_readPackedCompGenProg]
    have hr2 : (Memory.spec 0).clientResult s (bpReadSlabOwnerProg (mp.toCtx, (lastBlk, 1))) =
        b_last := by
      unfold bpReadSlabOwnerProg; dsimp only [BpMetaLayout.toCtx, b_last, fb, extractFallback]
      rw [ite_eq_left ⟨hlast_mb, by decide⟩, ite_eq_left hlast_mb]
      simp [pure_bind, clientResult_readPackedCompGenProg]
    rw [hr1, prog_clientResult_bind, clientState_bpReadSlabOwnerProg, hr2, prog_clientResult_pure]
  have hb1_ns : blk * mp.K + mp.K ≤ fb.nSide := by
    have : (blk + 1) * mp.K ≤ fb0 * mp.K := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_one_mul] at this; exact this.trans hbl_le
  have hb2_ns : lastBlk * mp.K + mp.K ≤ fb.nSide := by
    have : (lastBlk + 1) * mp.K = fb0 * mp.K := by congr 1; omega
    rw [Nat.add_one_mul] at this; exact this.le.trans hbl_le
  have hdisj_sr : blk * mp.K = lastBlk * mp.K ∨ blk * mp.K + mp.K ≤ lastBlk * mp.K ∨
      lastBlk * mp.K + mp.K ≤ blk * mp.K := by
    rcases eq_or_lt_of_le (by omega : blk ≤ lastBlk) with rfl | hlt
    · exact Or.inl rfl
    · refine Or.inr (Or.inl ?_)
      have : (blk + 1) * mp.K ≤ lastBlk * mp.K := Nat.mul_le_mul_right _ hlt
      rwa [Nat.add_one_mul] at this
  obtain ⟨hfr_sr, hio_sr, harr_sr, hout_sr, hpg_sr⟩ :=
    fbSwapRangeProg_spec hmv hiov hio hns_le hb1_ns hb2_ns hdisj_sr
  set s_sr := (Memory.spec 0).clientState s
    (fbSwapRangeProg (((mp.toCtx, io.toCtx), (blk * mp.K, lastBlk * mp.K)), mp.K))
  set s_w1 := (Memory.spec 0).clientState s_sr
    (bpWriteSlabOwnerProg ((mp.toCtx, (blk, 1)), b_last))
  set s_sw := (Memory.spec 0).clientState s_w1
    (bpWriteSlabOwnerProg ((mp.toCtx, (lastBlk, 1)), b_blk))
  have hwf_w1 := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge blk 1 b_last
  have hwf_w2 := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge lastBlk 1 b_blk
  have hfb_sr : extractFallback mp s_sr.mem = fb :=
    extractFallback_congr hmv.w_pos fun a hma =>
      hout_sr a (fun hia => hdisj a hma hia)
  have hfb_w1 := extractFallback_writeOwnerBlk (hfr_sr.symm ▸ hmv) hblk_mb hb_last_pb hb_last_nc
    (s := s_sr)
  have hfb_sw := extractFallback_writeOwnerBlk
    ((hwf_w1.1.frontier_eq s_sr).trans hfr_sr ▸ hmv) hlast_mb hb_blk_pb hb_blk_nc (s := s_w1)
  rw [hfb_sr] at hfb_w1; rw [hfb_w1] at hfb_sw
  have hfr_sw : s_sw.frontier = s.frontier :=
    (hwf_w2.1.frontier_eq s_w1).trans ((hwf_w1.1.frontier_eq s_sr).trans hfr_sr)
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
  have htl_kp_nc : tailLen + mp.K ≤ mp.nCap := by
    have hfb_split : fb0 * mp.K + tailLen = fb.nSide := Nat.add_sub_of_le hbl_le
    have hk_le_fb : mp.K ≤ fb0 * mp.K := le_mul_of_one_le_left (Nat.zero_le _) (by omega)
    omega
  set ob_sw := Function.update (Function.update fb.ownerBlk blk b_last) lastBlk b_blk
  set s_shr := (Memory.spec 0).clientState s_sw
    (iterate fbShiftRightStepProg (mp.toCtx, mp.K) tailLen tailLen)
  obtain ⟨hfr_shr, hns_shr, hfb_shr, hob_shr, hot_shr, hout_shr⟩ :=
    fbShiftRightLoop_spec (s_base := s_sw) hmv (htl_plus'.trans h6lt8.le) htl_kp_nc
      (fun i hi => hfb_M ▸ hfb.tail_lt i (htl_def.symm ▸ hi))
      tailLen tailLen s_sw hfr_sw rfl le_rfl
      (by rw [hfb_sw]) (by rw [hfb_sw]) (by rw [hfb_sw])
      (fun i _ => by rw [hfb_sw])
      (fun _ hj1 hj2 => absurd (lt_of_le_of_lt hj1 hj2) (lt_irrefl _))
      (fun _ _ => rfl)
  set s_fh := (Memory.spec 0).clientState s_shr
    (iterate fbFillHeadStepProg (mp.toCtx, b_blk) mp.K 0)
  obtain ⟨hfr_fh, hns_fh, hfb_fh, hob_fh, hot_fh_lo, hot_fh_hi, hout_fh⟩ :=
    fbFillHeadLoop_spec (s_base := s_sw) (tailLen := tailLen)
      (ot₁ := (extractFallback mp s_shr.mem).ownerTail) hmv hb_blk_pb hb_blk_nc
      mp.K 0 s_shr hfr_shr (Nat.zero_add _) hns_shr hfb_shr hob_shr
      (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun _ _ _ => rfl) hout_shr
  set s_fin := (Memory.spec 0).clientState s_fh (bpWriteScalarProg ((mp.toCtx, 10), lastBlk))
  have hlast_nc : lastBlk ≤ mp.nCap :=
    (le_mul_of_one_le_right (Nat.zero_le _) (by omega : 1 ≤ mp.K)).trans
      ((Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans (hbl_le.trans hns_le))
  have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 10 lastBlk
  have hfb_fin := extractFallback_writeScalar_10 (hfr_fh.symm ▸ hmv) hlast_nc (s := s_fh)
  have hds_st : (Memory.spec 0).clientState s
      (fbDemoteSwapProg ((mp.toCtx, io.toCtx), (blk, lastBlk))) = s_sw := by
    unfold fbDemoteSwapProg fbDemoteSwapBodyProg; dsimp only
    rw [hnc_eq, hk_eq, ite_eq_left hblk_div, ite_eq_left hlast_div,
      StateTransitionSpec.clientState_bind, state_fbReadBlkPairProg, hrb_res,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
    unfold fbWriteBlkPairProg; rw [StateTransitionSpec.clientState_bind]
  have hds_res : (Memory.spec 0).clientResult s
      (fbDemoteSwapProg ((mp.toCtx, io.toCtx), (blk, lastBlk))) = b_blk := by
    unfold fbDemoteSwapProg fbDemoteSwapBodyProg; dsimp only
    rw [hnc_eq, hk_eq, ite_eq_left hblk_div, ite_eq_left hlast_div,
      prog_clientResult_bind, state_fbReadBlkPairProg, hrb_res,
      prog_clientResult_bind, prog_clientResult_bind, prog_clientResult_pure]
  have hst_tot : (Memory.spec 0).clientState s (fbDemoteBlkProg ((mp.toCtx, io.toCtx), blk)) =
      s_fin := by
    unfold fbDemoteBlkProg
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl),
      StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩)]
    unfold fbDemoteCheckProg; dsimp only
    have hns_mem : s.mem (mp.metaBase + 1) = fb.nSide := rfl
    have hfb_mem : s.mem (mp.metaBase + 10) = fb0 := rfl
    rw [hns_mem, hfb_mem, hnc_eq, hk_eq, ite_eq_left hblk, ite_eq_left hfb_div]
    simp only [pure_bind]
    unfold fbDemoteInnerProg; dsimp only
    rw [hnc_eq, ite_eq_left hbl_le, ite_eq_left hns_le]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, hds_st, hds_res]
    unfold fbDemoteTailProg fbShiftRightLoopProg fbFillHeadLoopProg
    dsimp only; simp only [pure_bind]
    rw [hk_eq, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  rw [hst_tot]
  have hio_out : ∀ addr, io.OwnsAddr addr → s_fin.mem addr = s_sr.mem addr := fun a hia => by
    have hma : ¬mp.OwnsMetaAddr a := fun hma => hdisj a hma hia
    exact (hwf_sc.1.mem_outside s_fh a hma).trans
      ((hout_fh a hma).trans
        ((hwf_w2.1.mem_outside s_w1 a hma).trans (hwf_w1.1.mem_outside s_sr a hma)))
  obtain ⟨hio_fin, harr_fin⟩ := io.congr_of_outside hiov.w_pos hio_sr hio_out
  have hns_fin : (extractFallback mp s_fin.mem).nSide = fb.nSide := by
    rw [hfb_fin]; simp only; exact hns_fh
  have hfb_fin_blk : (extractFallback mp s_fin.mem).fullBlocks = lastBlk := by rw [hfb_fin]
  have hob_fin : (extractFallback mp s_fin.mem).ownerBlk = ob_sw := by
    rw [hfb_fin]; simp only; exact hob_fh
  have hot_fin :
      (extractFallback mp s_fin.mem).ownerTail = (extractFallback mp s_fh.mem).ownerTail :=
    by rw [hfb_fin]
  have hfb0_split : lastBlk * mp.K + mp.K = fb0 * mp.K := by
    rw [← Nat.add_one_mul]; congr 1; omega
  have htl_fin : (extractFallback mp s_fin.mem).tailLen = tailLen + mp.K := by
    unfold FallbackState.tailLen; rw [hns_fin, hfb_fin_blk]
    have hK_f : (extractFallback mp s_fin.mem).K = mp.K := rfl
    rw [hK_f]; omega
  set σ := swapRangeIdx (blk * mp.K) (lastBlk * mp.K) mp.K
  have div_mod_add : ∀ B off, off < mp.K →
      (B * mp.K + off) / mp.K = B ∧ (B * mp.K + off) % mp.K = off := fun B off hoff =>
    ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add],
     by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]⟩
  have how_fin : ∀ p < fb.nSide, (extractFallback mp s_fin.mem).owner p = fb.owner (σ p) := by
    intro p hp
    have hK_f : (extractFallback mp s_fin.mem).K = mp.K := rfl
    have hfb0_def : fb.fullBlocks = fb0 := rfl
    have hblk_mul_le : blk * mp.K ≤ lastBlk * mp.K := Nat.mul_le_mul_right _ (by omega)
    unfold FallbackState.owner
    rw [hfb_fin_blk, hK_f, hfb_K, hfb0_def]
    by_cases hp_last : lastBlk * mp.K ≤ p ∧ p < fb0 * mp.K
    · have hn_lt : ¬(p < lastBlk * mp.K) := by omega
      rw [ite_eq_right hn_lt, hot_fin]
      have hoff : p - lastBlk * mp.K < mp.K := by omega
      rw [hot_fh_lo _ hoff]
      have hσ_p : σ p = blk * mp.K + (p - lastBlk * mp.K) := by
        dsimp only [σ]; unfold swapRangeIdx
        rcases eq_or_lt_of_le (by omega : blk ≤ lastBlk) with rfl | hlt
        · rw [ite_eq_left ⟨hp_last.1, by omega⟩]
        · have hn1 : ¬(blk * mp.K ≤ p ∧ p < blk * mp.K + mp.K) := by
            have : (blk + 1) * mp.K ≤ lastBlk * mp.K := Nat.mul_le_mul_right _ hlt
            rw [Nat.add_one_mul] at this; omega
          rw [ite_eq_right hn1, ite_eq_left ⟨hp_last.1, by omega⟩]
      rw [hσ_p, ite_eq_left (by omega), (div_mod_add blk _ hoff).1]
    · by_cases hp_lo : p < lastBlk * mp.K
      · rw [ite_eq_left hp_lo, hob_fin]
        by_cases hp_blk : blk * mp.K ≤ p ∧ p < blk * mp.K + mp.K
        · have hblk_lt_last : blk < lastBlk :=
            Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hp_blk.1 hp_lo)
          have hdiv_blk : p / mp.K = blk := by
            have h1 := (Nat.le_div_iff_mul_le hK).mpr hp_blk.1
            have h2 : p / mp.K < blk + 1 :=
              (Nat.div_lt_iff_lt_mul hK).mpr (by rw [Nat.add_one_mul]; exact hp_blk.2)
            omega
          have hoff : p - blk * mp.K < mp.K := by omega
          have hσ_p : σ p = lastBlk * mp.K + (p - blk * mp.K) := by
            dsimp only [σ]; unfold swapRangeIdx; rw [ite_eq_left hp_blk]
          rw [hdiv_blk, hσ_p, ite_eq_left (by omega), (div_mod_add lastBlk _ hoff).1]
          dsimp only [ob_sw]
          rw [Function.update_of_ne (ne_of_lt hblk_lt_last), Function.update_self]
        · have hσ_p : σ p = p := by
            dsimp only [σ]; unfold swapRangeIdx
            rw [ite_eq_right hp_blk, ite_eq_right (by omega)]
          have hne_last : p / mp.K ≠ lastBlk :=
            ne_of_lt ((Nat.div_lt_iff_lt_mul hK).mpr hp_lo)
          have hne_blk : p / mp.K ≠ blk := by
            intro heq
            have hp_dm := Nat.div_add_mod p mp.K
            have hm_lt := Nat.mod_lt p hK
            rw [heq, Nat.mul_comm] at hp_dm
            exact hp_blk ⟨by omega, by omega⟩
          rw [hσ_p, ite_eq_left (hp_lo.trans_le (by omega))]
          dsimp only [ob_sw]
          rw [Function.update_of_ne hne_last, Function.update_of_ne hne_blk]
      · have hp_ge : fb0 * mp.K ≤ p := by omega
        rw [ite_eq_right hp_lo, hot_fin]
        have hσ_p : σ p = p := by
          dsimp only [σ]; unfold swapRangeIdx
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        have ht_ge : mp.K ≤ p - lastBlk * mp.K := by omega
        have ht_lt : p - lastBlk * mp.K < tailLen + mp.K := by omega
        have hj_lt : p - fb0 * mp.K < tailLen := by omega
        have hj_eq : p - lastBlk * mp.K = (p - fb0 * mp.K) + mp.K := by omega
        rw [hot_fh_hi _ ht_ge ht_lt, hj_eq, hot_shr _ hj_lt, hσ_p, ite_eq_right (by omega)]
  have hval_fin : (extractFallback mp s_fin.mem).Valid :=
    { M_ge := hfb.M_ge
      K_ge := hfb.K_ge
      blocks_le := by
        rw [hns_fin, hfb_fin_blk]
        have hK_f : (extractFallback mp s_fin.mem).K = mp.K := rfl
        rw [hK_f]; omega
      tail_le := by rw [htl_fin]; exact htl_plus'
      blk_lt := fun b hb => by
        rw [hfb_fin_blk] at hb
        rw [hob_fin]; dsimp only [ob_sw]
        rw [Function.update_of_ne (ne_of_lt hb)]
        by_cases hbb : b = blk
        · subst hbb; rw [Function.update_self]; exact hb_last_M
        · rw [Function.update_of_ne hbb]; exact hfb.blk_lt b (hb.trans hlast_lt)
      tail_lt := fun t ht => by
        rw [htl_fin] at ht
        rw [hot_fin]
        by_cases ht_K : t < mp.K
        · rw [hot_fh_lo t ht_K]; exact hb_blk_M
        · rw [hot_fh_hi t (Nat.le_of_not_lt ht_K) ht]
          have hj_eq : t = (t - mp.K) + mp.K := by omega
          rw [hj_eq, hot_shr (t - mp.K) (by omega)]
          exact hfb.tail_lt _ (by rw [htl_def]; omega) }
  have href_fin := href.comp_involution σ
    (fun p _ => swapRangeIdx_involutive hdisj_sr)
    (fun p hp => swapRangeIdx_lt hb1_ns hb2_ns hp)
    how_fin
    (fun p hp => (harr_fin p hp).trans (harr_sr p hp))
  refine ⟨(hwf_sc.1.frontier_eq s_fh).trans hfr_fh, hns_fin, hfb_fin_blk, hval_fin,
    hio_fin, href_fin, fun off hoff => ?_, fun addr ha => ?_, fun hnz => ?_⟩
  · have hp_lt : lastBlk * mp.K + off < fb.nSide := by omega
    have hσ_eq : σ (lastBlk * mp.K + off) = blk * mp.K + off := by
      dsimp only [σ]; unfold swapRangeIdx
      rcases eq_or_lt_of_le (by omega : blk ≤ lastBlk) with rfl | hlt
      · rw [ite_eq_left ⟨by omega, by omega⟩]; omega
      · have hn1 :
            ¬(blk * mp.K ≤ lastBlk * mp.K + off ∧ lastBlk * mp.K + off < blk * mp.K + mp.K) :=
          by
            have : (blk + 1) * mp.K ≤ lastBlk * mp.K := Nat.mul_le_mul_right _ hlt
            rw [Nat.add_one_mul] at this; omega
        rw [ite_eq_right hn1, ite_eq_left ⟨by omega, by omega⟩]; omega
    exact ⟨(harr_fin _ hp_lt).trans ((harr_sr _ hp_lt).trans (congrArg _ hσ_eq)),
      (how_fin _ hp_lt).trans (congrArg _ hσ_eq)⟩
  · have hma : ¬mp.OwnsMetaAddr addr := fun h => ha (Or.inl h)
    have hia : ¬io.OwnsAddr addr := fun h => ha (Or.inr h)
    exact (hwf_sc.1.mem_outside s_fh addr hma).trans
      ((hout_fh addr hma).trans
        ((hwf_w2.1.mem_outside s_w1 addr hma).trans
          ((hwf_w1.1.mem_outside s_sr addr hma).trans (hout_sr addr hia))))
  · obtain ⟨hu_sr, hp_sr⟩ := hpg_sr hnz
    have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → s_fin.mem addr = s_sr.mem addr := fun a ha => by
      apply hio_out a; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
    have hu_fin : extractPageUnperm io.pgL s_fin.mem = extractPageUnperm io.pgL s_sr.mem :=
      extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
    refine ⟨hu_fin.trans hu_sr, fun idx hidx => ?_⟩
    unfold SlotIoLayout.StateInv at hio_sr; rw [ite_eq_right hnz] at hio_sr
    have hidx_sr : idx < (extractPagePair io.pgL s_sr.mem).virtLen io.partner.side := by
      have : extractPagePair io.pgL s_sr.mem = extractPagePair io.pgL s.mem :=
        congrArg PageUnpermState.st hu_sr
      rwa [this]
    have hp_lt_sr :
        (extractPageUnperm io.pgL s_sr.mem).toPhys io.partner.side idx < io.pgL.nCap :=
      (hio_sr.1.toPhys_lt hidx_sr).trans_le hio_sr.2.2.2.1
    have hp_fin : slotIoPairAt io.partner s_fin.mem idx = slotIoPairAt io.partner s_sr.mem idx := by
      unfold slotIoPairAt
      have hp_nz : io.partner.usePaged ≠ 0 := hnz
      rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_fin]
      exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt_sr
    exact hp_fin.trans (hp_sr idx hidx)

/-! ## Section 2: Tail Pop and Slot Deletion -/

private def fbPopBackAndDecProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), last) => do
    slotIoPopBackRawProg ioctx
    bpWriteScalarProg ((mctx, 1), last)

private theorem frontier_fbPopBackAndDecProg (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbPopBackAndDecProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, last⟩
  unfold fbPopBackAndDecProg
  rw [StateTransitionSpec.clientState_bind, frontier_bpWriteScalarProg]
  have hpbf := (slotIoPopBackProg_frame (io := SlotIoLayout.ofCtx ioctx) hw).frontier_eq s
  unfold slotIoPopBackProg at hpbf; rw [SlotIoLayout.toCtx_ofCtx] at hpbf
  exact hpbf

private theorem realizesBounded_fbPopBackAndDec :
    RealizesBounded .exact fbPopBackAndDecProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hpb := realizesBounded_slotIoPopBackRaw
  have hws := realizesBounded_bpWriteScalar
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, last⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hiov | exact hw1 | (
      have hpbf := (slotIoPopBackProg_frame (io := SlotIoLayout.ofCtx ioctx) hiov.w_pos).frontier_eq
        s
      unfold slotIoPopBackProg at hpbf; rw [SlotIoLayout.toCtx_ofCtx] at hpbf
      dsimp only [StateTransitionSpec.clientState] at hpbf
      rw [hpbf]; exact hmv))

private def fbPopTailInnerProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), p), (nSide, fbBase)) =>
    if fbBase ≤ p then
      if p < nSide then do
        let t₁ ← pure (p - fbBase)
        let last ← pure (nSide - 1)
        let t₂ ← pure (last - fbBase)
        fbSwapTailSlotsProg (((mctx, ioctx), fbBase), (t₁, t₂))
        fbPopBackAndDecProg ((mctx, ioctx), last)
      else pure ()
    else pure ()

private theorem frontier_fbPopTailInnerProg
    (x : (BlockPoolCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbPopTailInnerProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨mctx, ioctx⟩, p⟩, ⟨nSide, fbBase⟩⟩
  unfold fbPopTailInnerProg; dsimp only
  split_ifs
  · simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind,
      frontier_fbPopBackAndDecProg ((mctx, ioctx), nSide - 1) _ hw]
    exact frontier_fbSwapTailSlotsProg ((mctx, ioctx), fbBase) _ _ s hw
  all_goals rfl

private theorem realizesBounded_fbPopTailInner :
    RealizesBounded .exact fbPopTailInnerProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsw := realizesBounded_fbSwapTailSlots
  have hpd := realizesBounded_fbPopBackAndDec
  realize
  all_goals (
    rcases d with ⟨⟨⟨mctx, ioctx⟩, p⟩, ⟨nSide, fbBase⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hp_w : p < 2 ^ w := hwords 27
    have hns_w : nSide < 2 ^ w := hwords 28
    have hfr := frontier_fbSwapTailSlotsProg ((mctx, ioctx), fbBase)
      (p - fbBase) (nSide - 1 - fbBase) s hiov.w_pos
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfr]
    first | exact hmv | exact hiov | omega)

private def fbPopTailCheckProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), p), (nSide, fb0)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if nSide ≤ nCap then
      if fb0 ≤ nCap / k then do
        let fbBase ← pure (fb0 * k)
        fbPopTailInnerProg (((mctx, ioctx), p), (nSide, fbBase))
      else pure ()
    else pure ()

private theorem realizesBounded_fbPopTailCheck :
    RealizesBounded .exact fbPopTailCheckProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hin := realizesBounded_fbPopTailInner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, p⟩, ⟨nSide, fb0⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega | (
      have hfb_mul : fb0 * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      omega))

/-- Pop tail slot `p ∈ [fullBlocks * K, nSide)` by swapping it with `nSide - 1` and popping back
(`¬ReadsWidth`). -/
def fbPopTailAtProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), p) => do
    let nSide ← bpReadScalarProg (mctx, 1)
    let fb0 ← bpReadScalarProg (mctx, 10)
    fbPopTailCheckProg (((mctx, ioctx), p), (nSide, fb0))

theorem frontier_fbPopTailAtProg (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpCtxIo x)).pgL.w) :
    ((Memory.spec 0).clientState s (fbPopTailAtProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, p⟩
  unfold fbPopTailAtProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  unfold fbPopTailCheckProg; dsimp only
  split_ifs
  · simp only [pure_bind]; exact frontier_fbPopTailInnerProg _ s hw
  all_goals rfl

theorem realizesBounded_fbPopTailAt :
    RealizesBounded .exact fbPopTailAtProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hchk := realizesBounded_fbPopTailCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, p⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | exact hw1 | exact h10_w)

theorem fbPopTailAtProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits w p : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).Valid)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractFallback mp s.mem).nSide 0 s.mem)
    (href : PoolItemsRefines U V bBits hBkt (extractFallback mp s.mem).nSide
      (extractFallback mp s.mem).owner (slotIoPairAt io s.mem) s_abs)
    (hp_ge : (extractFallback mp s.mem).fullBlocks * mp.K ≤ p)
    (hp_lt : p < (extractFallback mp s.mem).nSide)
    (u : Fin U)
    (how_p : (extractFallback mp s.mem).owner p = feistelBucket bBits hBkt u.val)
    (hpr_p : (slotIoPairAt io s.mem p).1 = keyQuotient bBits u.val) :
    let fb := extractFallback mp s.mem
    let s' := (Memory.spec 0).clientState s (fbPopTailAtProg ((mp.toCtx, io.toCtx), p))
    let fb' := extractFallback mp s'.mem
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    fb'.nSide = fb.nSide - 1 ∧
    fb'.Valid ∧
    io.StateInv (fb.nSide - 1) slack' s'.mem ∧
    PoolItemsRefines U V bBits hBkt (fb.nSide - 1) fb'.owner (slotIoPairAt io s'.mem)
      (Function.update s_abs u none) ∧
    (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → s'.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      (extractPagePair io.pgL s'.mem).virtLen io.partner.side =
        (extractPagePair io.pgL s.mem).virtLen io.partner.side ∧
      (extractPagePair io.pgL s'.mem).totalItems =
        (extractPagePair io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  set fb := extractFallback mp s.mem
  set fb0 := fb.fullBlocks
  set fbBase := fb0 * mp.K
  set last := fb.nSide - 1
  set t₁ := p - fbBase
  set t₂ := last - fbBase
  have hpos : 0 < fb.nSide := Nat.zero_lt_of_lt hp_lt
  have hlast_lt : last < fb.nSide := Nat.sub_lt hpos Nat.one_pos
  have hlast_ge : fbBase ≤ last := by omega
  have hfb_K : fb.K = mp.K := rfl
  have hfb_M : fb.M = mp.M := rfl
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  have hbl_le : fbBase ≤ fb.nSide := by
    dsimp only [fbBase, fb0]; rw [← hfb_K]; exact hfb.blocks_le
  have hfb_div : fb0 ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hbl_le.trans hns_le)
  have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
    have := hmv.M_ge; have := hmv.K_ge; nlinarith
  have hfb0_def : fb.fullBlocks = fb0 := rfl
  have ht₁_lt : t₁ < fb.tailLen := by
    dsimp only [t₁, fbBase]; unfold FallbackState.tailLen; rw [hfb_K, hfb0_def]; omega
  have ht₂_lt : t₂ < fb.tailLen := by
    dsimp only [t₂, last, fbBase]; unfold FallbackState.tailLen; rw [hfb_K, hfb0_def]; omega
  obtain ⟨hfr_sw, hfb_sw, hio_sw, harr_sw, hout_sw, hpg_sw⟩ :=
    fbSwapTailSlotsProg_spec hmv hiov hdisj hfb h6lt8 hns_le hio ht₁_lt ht₂_lt
  set s₁ := (Memory.spec 0).clientState s
    (fbSwapTailSlotsProg (((mp.toCtx, io.toCtx), fbBase), (t₁, t₂)))
  obtain ⟨hio₂_raw, harr₂, hpg₂⟩ := slotIoPopBackProg_spec (hfr_sw.symm ▸ hiov) hio_sw hpos
  have hpbf := slotIoPopBackProg_frame (io := io) hiov.w_pos
  unfold slotIoPopBackProg at hio₂_raw harr₂ hpg₂ hpbf
  set slack' :=
    if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_eq : (if io.usePaged = 0 ∨
      (extractPageUnperm io.pgL s₁.mem).cleanPhase = 0 then 0 else 24) = slack' := by
    by_cases h0 : io.usePaged = 0
    · simp [slack', h0]
    · simp only [slack', h0, false_or, (hpg_sw h0).1]
  have hio₂ : io.StateInv last slack'
      ((Memory.spec 0).clientState s₁ (slotIoPopBackRawProg io.toCtx)).mem :=
    hsl_eq ▸ hio₂_raw
  set s₂ := (Memory.spec 0).clientState s₁ (slotIoPopBackRawProg io.toCtx)
  have hfr₂ : s₂.frontier = s.frontier := (hpbf.frontier_eq s₁).trans hfr_sw
  set s₃ := (Memory.spec 0).clientState s₂ (bpWriteScalarProg ((mp.toCtx, 1), last))
  have hlast_nc : last ≤ mp.nCap := by omega
  have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 1 last
  have hfb₂ : extractFallback mp s₂.mem = extractFallback mp s₁.mem :=
    extractFallback_congr hmv.w_pos fun a hma =>
      hpbf.mem_outside s₁ a (fun hia => hdisj a hma hia)
  have hfb₃ := extractFallback_writeScalar_1 (hfr₂.symm ▸ hmv) hlast_nc (s := s₂)
  rw [hfb₂, hfb_sw] at hfb₃
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
  have hst_tot :
      (Memory.spec 0).clientState s (fbPopTailAtProg ((mp.toCtx, io.toCtx), p)) = s₃ := by
    unfold fbPopTailAtProg
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl),
      StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩)]
    unfold fbPopTailCheckProg; dsimp only
    have hns_mem : s.mem (mp.metaBase + 1) = fb.nSide := rfl
    have hfb_mem : s.mem (mp.metaBase + 10) = fb0 := rfl
    rw [hns_mem, hfb_mem, hnc_eq, hk_eq, ite_eq_left hns_le, ite_eq_left hfb_div]
    simp only [pure_bind]
    unfold fbPopTailInnerProg; dsimp only
    rw [ite_eq_left hp_ge, ite_eq_left hp_lt]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind]
    unfold fbPopBackAndDecProg
    rw [StateTransitionSpec.clientState_bind]
  rw [hst_tot]
  have hio_out : ∀ addr, io.OwnsAddr addr → s₃.mem addr = s₂.mem addr := fun a hia =>
    hwf_sc.1.mem_outside s₂ a (fun hma => hdisj a hma hia)
  obtain ⟨hio₃, harr₃⟩ := io.congr_of_outside hiov.w_pos hio₂ hio_out
  have hp_re : fbBase + t₁ = p := by omega
  have hlast_re : fbBase + t₂ = last := by omega
  have how₁ : ∀ q < fb.nSide, (extractFallback mp s₁.mem).owner q =
      (PhysSwap.mk p last).apply fb.owner q := by
    intro q hq
    unfold FallbackState.owner
    have hfb1_blk : (extractFallback mp s₁.mem).fullBlocks = fb0 := by rw [hfb_sw]
    have hfb1_ob : (extractFallback mp s₁.mem).ownerBlk = fb.ownerBlk := by rw [hfb_sw]
    have hfb1_ot : (extractFallback mp s₁.mem).ownerTail =
        (PhysSwap.mk t₁ t₂).apply fb.ownerTail := by rw [hfb_sw]
    have hK1 : (extractFallback mp s₁.mem).K = mp.K := rfl
    rw [hfb1_blk, hK1]
    by_cases hlt : q < fbBase
    · rw [ite_eq_left hlt, hfb1_ob,
        (PhysSwap.mk p last).apply_of_ne _ (by dsimp only; omega) (by dsimp only; omega),
        hfb_K, ite_eq_left hlt]
    · rw [ite_eq_right hlt, hfb1_ot]
      by_cases h1 : q = p
      · have hsub1 : p - fbBase = t₁ := rfl
        have hsub2 : last - fbBase = t₂ := rfl
        rw [h1, hsub1, (PhysSwap.mk t₁ t₂).apply_p₁, (PhysSwap.mk p last).apply_p₁,
          hfb_K, ite_eq_right (not_lt.mpr hlast_ge), hsub2]
      · by_cases h2 : q = last
        · have hsub2 : last - fbBase = t₂ := rfl
          have hsub1 : p - fbBase = t₁ := rfl
          rw [h2, hsub2, (PhysSwap.mk t₁ t₂).apply_p₂, (PhysSwap.mk p last).apply_p₂,
            hfb_K, ite_eq_right (not_lt.mpr hp_ge), hsub1]
        · rw [(PhysSwap.mk t₁ t₂).apply_of_ne _ (by dsimp only; omega) (by dsimp only; omega),
            (PhysSwap.mk p last).apply_of_ne _ h1 h2, hfb_K, ite_eq_right hlt]
  have href₁ := (href.apply_swap (sw := ⟨p, last⟩) hp_lt hlast_lt).congr
    (pr₂ := slotIoPairAt io s₁.mem)
    how₁ (fun q hq => by rw [harr_sw q hq, hp_re, hlast_re])
  have htop_bkt : (extractFallback mp s₁.mem).owner last = feistelBucket bBits hBkt u.val := by
    rw [how₁ last hlast_lt, (PhysSwap.mk p last).apply_p₂]; exact how_p
  have htop_q : (slotIoPairAt io s₁.mem last).1 = keyQuotient bBits u.val := by
    rw [harr_sw last hlast_lt, hp_re, hlast_re, (PhysSwap.mk p last).apply_p₂]; exact hpr_p
  have hns₃ : (extractFallback mp s₃.mem).nSide = last := by rw [hfb₃]
  have hblk₃ : (extractFallback mp s₃.mem).fullBlocks = fb0 := by rw [hfb₃]
  have hob₃ : (extractFallback mp s₃.mem).ownerBlk = fb.ownerBlk := by rw [hfb₃]
  have hot₃ : (extractFallback mp s₃.mem).ownerTail =
      (PhysSwap.mk t₁ t₂).apply fb.ownerTail := by rw [hfb₃]
  have how₃_eq : ∀ q < last,
      (extractFallback mp s₃.mem).owner q = (extractFallback mp s₁.mem).owner q := by
    intro q _
    unfold FallbackState.owner
    have hK3 : (extractFallback mp s₃.mem).K = mp.K := rfl
    have hK1 : (extractFallback mp s₁.mem).K = mp.K := rfl
    have hfb1_blk : (extractFallback mp s₁.mem).fullBlocks = fb0 := by rw [hfb_sw]
    have hfb1_ob : (extractFallback mp s₁.mem).ownerBlk = fb.ownerBlk := by rw [hfb_sw]
    have hfb1_ot : (extractFallback mp s₁.mem).ownerTail =
        (PhysSwap.mk t₁ t₂).apply fb.ownerTail := by rw [hfb_sw]
    rw [hblk₃, hfb1_blk, hK3, hK1, hob₃, hfb1_ob, hot₃, hfb1_ot]
  have href₃ := href₁.pop_last hpos htop_bkt htop_q how₃_eq
    (fun q hq => (harr₃ q hq).trans (harr₂ q hq))
  have hval₃ : (extractFallback mp s₃.mem).Valid :=
    { M_ge := hfb.M_ge
      K_ge := hfb.K_ge
      blocks_le := by
        rw [hns₃, hblk₃]
        have hK3 : (extractFallback mp s₃.mem).K = mp.K := rfl
        rw [hK3]; exact hlast_ge
      tail_le := by
        unfold FallbackState.tailLen
        have hK3 : (extractFallback mp s₃.mem).K = mp.K := rfl
        have hM3 : (extractFallback mp s₃.mem).M = mp.M := rfl
        rw [hns₃, hblk₃, hK3, hM3]
        have h6 := hfb.tail_le
        unfold FallbackState.tailLen at h6; rw [hfb_K, hfb_M, hfb0_def] at h6
        dsimp only [last]; omega
      blk_lt := by rw [hblk₃, hob₃]; exact hfb.blk_lt
      tail_lt := fun t ht => by
        unfold FallbackState.tailLen at ht
        have hK3 : (extractFallback mp s₃.mem).K = mp.K := rfl
        rw [hns₃, hblk₃, hK3] at ht
        rw [hot₃, physSwap_apply_eq_swapIdx]
        have ht_old : t < fb.tailLen := by
          unfold FallbackState.tailLen; rw [hfb_K, hfb0_def]; dsimp only [last] at ht; omega
        exact hfb.tail_lt _ (swapIdx_lt ht₁_lt ht₂_lt ht_old) }
  refine ⟨(hwf_sc.1.frontier_eq s₂).trans hfr₂, hns₃, hval₃, hio₃, href₃,
    fun addr ha => ?_, fun hnz => ?_⟩
  · have hma : ¬mp.OwnsMetaAddr addr := fun h => ha (Or.inl h)
    have hia : ¬io.OwnsAddr addr := fun h => ha (Or.inr h)
    exact (hwf_sc.1.mem_outside s₂ addr hma).trans
      ((hpbf.mem_outside s₁ addr hia).trans (hout_sw addr ha))
  · obtain ⟨hu₁, hp₁⟩ := hpg_sw hnz
    obtain ⟨hvl₂, hti₂, hp₂⟩ := hpg₂ hnz
    have hst₁ : extractPagePair io.pgL s₁.mem = extractPagePair io.pgL s.mem :=
      congrArg PageUnpermState.st hu₁
    have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → s₃.mem addr = s₂.mem addr := fun a ha => by
      apply hio_out a; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
    have hu₃ : extractPageUnperm io.pgL s₃.mem = extractPageUnperm io.pgL s₂.mem :=
      extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
    have hst₃ : extractPagePair io.pgL s₃.mem = extractPagePair io.pgL s₂.mem :=
      congrArg PageUnpermState.st hu₃
    refine ⟨by rw [hst₃, hvl₂, hst₁], by rw [hst₃, hti₂, hst₁], fun idx hidx => ?_⟩
    unfold SlotIoLayout.StateInv at hio₂; rw [ite_eq_right hnz] at hio₂
    have hidx₂ : idx < (extractPagePair io.pgL s₂.mem).virtLen io.partner.side := by
      rwa [hvl₂, hst₁]
    have hp_lt₂ : (extractPageUnperm io.pgL s₂.mem).toPhys io.partner.side idx < io.pgL.nCap :=
      (hio₂.1.toPhys_lt hidx₂).trans_le hio₂.2.2.2.1
    have hp₃ : slotIoPairAt io.partner s₃.mem idx = slotIoPairAt io.partner s₂.mem idx := by
      unfold slotIoPairAt
      have hp_nz : io.partner.usePaged ≠ 0 := hnz
      rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu₃]
      exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt₂
    exact hp₃.trans ((hp₂ idx (hst₁.symm ▸ hidx)).trans (hp₁ idx hidx))

private def fbDemotePopRunProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), blk), (fb1, off)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if blk < fb1 then
      if fb1 ≤ nCap / k then do
        let lastSlot ← pure ((fb1 - 1) * k + off)
        fbDemoteBlkProg ((mctx, ioctx), blk)
        fbPopTailAtProg ((mctx, ioctx), lastSlot)
      else pure ()
    else pure ()

private theorem frontier_fbDemotePopRunProg
    (x : (BlockPoolCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbDemotePopRunProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, blk⟩, ⟨fb1, off⟩⟩
  unfold fbDemotePopRunProg; dsimp only
  split_ifs
  · simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind,
      frontier_fbPopTailAtProg (((p1, (((m, k), p2b), (mt, nCap))), ioctx), (fb1 - 1) * k + off)
        _ hw]
    exact frontier_fbDemoteBlkProg _ s hw
  all_goals rfl

private theorem realizesBounded_fbDemotePopRun :
    RealizesBounded .exact fbDemotePopRunProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), (_, off)) s =>
        off < (BpMetaLayout.ofCtx mctx).K ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hdb := realizesBounded_fbDemoteBlk
  have hpt := realizesBounded_fbPopTailAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, blk⟩, ⟨fb1, off⟩⟩
    obtain ⟨hoff_lt, hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hoff_lt hnc_w hK_ge
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hfr := frontier_fbDemoteBlkProg ((mctx, ioctx), blk) s hiov.w_pos
    dsimp only [mctx, StateTransitionSpec.clientState] at hfr
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfr]
    first | exact hmv | exact hiov | omega | (
      have hfb_mul : fb1 * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      have hsplit : (fb1 - 1) * k + k = fb1 * k := by
        rw [← Nat.add_one_mul]; congr 1; omega
      omega))

private def fbDemoteAndPopProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, ioctx), (blk, off)) => do
    let (_, (((_, k), _), _)) := mctx
    if off < k then do
      fbMaybePromoteProg (mctx, ioctx)
      let fb1 ← bpReadScalarProg (mctx, 10)
      fbDemotePopRunProg (((mctx, ioctx), blk), (fb1, off))
    else pure ()

private theorem frontier_fbDemoteAndPopProg (x : BlockPoolCtx × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbDemoteAndPopProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, p2c⟩⟩, ioctx⟩, ⟨blk, off⟩⟩
  unfold fbDemoteAndPopProg; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_bpReadScalarProg, frontier_fbDemotePopRunProg _ _ hw]
    exact frontier_fbMaybePromoteProg _ s hw
  · rfl

private theorem realizesBounded_fbDemoteAndPop :
    RealizesBounded .exact fbDemoteAndPopProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hmp := realizesBounded_fbMaybePromote
  have hrs := realizesBounded_bpReadScalar
  have hrun := realizesBounded_fbDemotePopRun
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨blk, off⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hfr_mp := frontier_fbMaybePromoteProg (mctx, ioctx) s hiov.w_pos
    dsimp only [mctx, StateTransitionSpec.clientState] at hfr_mp
    try dsimp only [BpMetaLayout.ofCtx] at *
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfr_mp]
    first | exact hmv | exact hiov | exact h10_w | omega)

/-- Delete any slot `hitP < nSide` from `FallbackPool` (`¬ReadsWidth`). -/
def fbDeleteSlotProg : BlockPoolCtx × ℕ → Memory.Prog Unit
  | ((mctx, ioctx), hitP) => do
    let fb0 ← bpReadScalarProg (mctx, 10)
    let dm ← bpDivModKProg (mctx, hitP)
    if dm.1 < fb0 then
      fbDemoteAndPopProg ((mctx, ioctx), dm)
    else
      fbPopTailAtProg ((mctx, ioctx), hitP)

theorem frontier_fbDeleteSlotProg (x : BlockPoolCtx × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpCtxIo x)).pgL.w) :
    ((Memory.spec 0).clientState s (fbDeleteSlotProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, hitP⟩
  unfold fbDeleteSlotProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpDivModKProg]
  split_ifs
  · exact frontier_fbDemoteAndPopProg _ s hw
  · exact frontier_fbPopTailAtProg _ s hw

theorem realizesBounded_fbDeleteSlot :
    RealizesBounded .exact fbDeleteSlotProg
      (WordEncoding.encode (α := BlockPoolCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  have hdp := realizesBounded_fbDemoteAndPop
  have hpt := realizesBounded_fbPopTailAt
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, hitP⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg, runClient_state_bpDivModKProg,
      Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | exact h10_w)

theorem fbDeleteSlotProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits w hitP : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).Valid)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractFallback mp s.mem).nSide 0 s.mem)
    (href : PoolItemsRefines U V bBits hBkt (extractFallback mp s.mem).nSide
      (extractFallback mp s.mem).owner (slotIoPairAt io s.mem) s_abs)
    (hp_lt : hitP < (extractFallback mp s.mem).nSide)
    (u : Fin U)
    (how_p : (extractFallback mp s.mem).owner hitP = feistelBucket bBits hBkt u.val)
    (hpr_p : (slotIoPairAt io s.mem hitP).1 = keyQuotient bBits u.val) :
    let fb := extractFallback mp s.mem
    let s' := (Memory.spec 0).clientState s (fbDeleteSlotProg ((mp.toCtx, io.toCtx), hitP))
    let fb' := extractFallback mp s'.mem
    let slack' :=
      if io.usePaged = 0 ∨ (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    fb'.nSide = fb.nSide - 1 ∧
    fb'.Valid ∧
    io.StateInv (fb.nSide - 1) slack' s'.mem ∧
    PoolItemsRefines U V bBits hBkt (fb.nSide - 1) fb'.owner (slotIoPairAt io s'.mem)
      (Function.update s_abs u none) ∧
    (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → s'.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      (extractPagePair io.pgL s'.mem).virtLen io.partner.side =
        (extractPagePair io.pgL s.mem).virtLen io.partner.side ∧
      (extractPagePair io.pgL s'.mem).totalItems =
        (extractPagePair io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  set fb := extractFallback mp s.mem
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  have hfb_K : fb.K = mp.K := rfl
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
  unfold fbDeleteSlotProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩),
    StateTransitionSpec.clientState_bind, clientState_bpDivModKProg, clientResult_bpDivModK]
  dsimp only
  have hfb_mem : s.mem (mp.metaBase + 10) = fb.fullBlocks := rfl
  rw [hfb_mem]
  by_cases hlt_blk : hitP / mp.K < fb.fullBlocks
  · rw [ite_eq_left hlt_blk]
    have hp_lo : hitP < fb.fullBlocks * mp.K := (Nat.div_lt_iff_lt_mul hK).mp hlt_blk
    have hoff_lt : hitP % mp.K < mp.K := Nat.mod_lt hitP hK
    have hp_dm : (hitP / mp.K) * mp.K + hitP % mp.K = hitP := by
      rw [Nat.mul_comm, Nat.div_add_mod]
    obtain ⟨hfr₁, hns₁, hblk_le₁, htl_plus₁, hval₁, hio₁, href₁, hlow₁, hout₁, hpg₁⟩ :=
      fbMaybePromoteProg_spec hmv hiov hdisj hfb hns_le hio href
    set s₁ := (Memory.spec 0).clientState s (fbMaybePromoteProg (mp.toCtx, io.toCtx))
    set fb1 := (extractFallback mp s₁.mem).fullBlocks
    have hblk_lt₁ : hitP / mp.K < fb1 := lt_of_lt_of_le hlt_blk hblk_le₁
    have hfb1_div : fb1 ≤ mp.nCap / mp.K :=
      (Nat.le_div_iff_mul_le hK).mpr ((hval₁.blocks_le).trans (hns₁.symm ▸ hns_le))
    obtain ⟨hfr₂, hns₂, hblk₂, hval₂, hio₂, href₂, hslot₂, hout₂, hpg₂⟩ :=
      fbDemoteBlkProg_spec (hfr₁.symm ▸ hmv) (hfr₁.symm ▸ hiov) hdisj hval₁
        (hns₁.symm ▸ hns_le) htl_plus₁ hblk_lt₁ (hns₁.symm ▸ hio₁) (hns₁.symm ▸ href₁)
    set s₂ := (Memory.spec 0).clientState s₁ (fbDemoteBlkProg ((mp.toCtx, io.toCtx), hitP / mp.K))
    set lastSlot := (fb1 - 1) * mp.K + hitP % mp.K
    have hpos_fb1 : 1 ≤ fb1 := Nat.one_le_of_lt hblk_lt₁
    have hblk₂' : (extractFallback mp s₂.mem).fullBlocks = fb1 - 1 := hblk₂
    have hls_ge : (extractFallback mp s₂.mem).fullBlocks * mp.K ≤ lastSlot := by
      rw [hblk₂']; exact Nat.le_add_right _ _
    have hls_lt : lastSlot < (extractFallback mp s₂.mem).nSide := by
      have hns_def : (extractFallback mp s.mem).nSide = fb.nSide := rfl
      rw [hns₂, hns₁, hns_def]
      have h1 : (fb1 - 1) * mp.K + mp.K = fb1 * mp.K := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hpos_fb1]
      have h2 : fb1 * mp.K ≤ fb.nSide := by
        have hb := hval₁.blocks_le
        have hK1 : (extractFallback mp s₁.mem).K = mp.K := rfl
        rw [hK1, hns₁, hns_def] at hb; exact hb
      exact (Nat.add_lt_add_left hoff_lt _).trans_le (h1.le.trans h2)
    obtain ⟨hpr_ls, how_ls⟩ := hslot₂ (hitP % mp.K) hoff_lt
    rw [hp_dm] at hpr_ls how_ls
    obtain ⟨hpr_p₁, how_p₁⟩ := hlow₁ hitP hp_lo
    have how_s₂ : (extractFallback mp s₂.mem).owner lastSlot = feistelBucket bBits hBkt u.val :=
      how_ls.trans (how_p₁.trans how_p)
    have hpr_s₂ : (slotIoPairAt io s₂.mem lastSlot).1 = keyQuotient bBits u.val := by
      rw [hpr_ls, hpr_p₁]; exact hpr_p
    obtain ⟨hfr₃, hns₃, hval₃, hio₃_raw, href₃_raw, hout₃, hpg₃⟩ :=
      fbPopTailAtProg_spec ((hfr₂.trans hfr₁).symm ▸ hmv) ((hfr₂.trans hfr₁).symm ▸ hiov) hdisj
        hval₂ ((hns₂.trans hns₁).symm ▸ hns_le) (hns₂.symm ▸ hio₂)
        (hns₂.symm ▸ href₂) hls_ge hls_lt u how_s₂ hpr_s₂
    have hst_dp : (Memory.spec 0).clientState s
        (fbDemoteAndPopProg ((mp.toCtx, io.toCtx), (hitP / mp.K, hitP % mp.K))) =
        (Memory.spec 0).clientState s₂ (fbPopTailAtProg ((mp.toCtx, io.toCtx), lastSlot)) := by
      unfold fbDemoteAndPopProg; dsimp only
      rw [hk_eq, ite_eq_left hoff_lt, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s₁ (Or.inr ⟨le_rfl, by omega⟩)]
      unfold fbDemotePopRunProg; dsimp only
      have hfb1_eq : s₁.mem (mp.metaBase + 10) = fb1 := rfl
      rw [hfb1_eq, hnc_eq, hk_eq, ite_eq_left hblk_lt₁, ite_eq_left hfb1_div]
      simp only [pure_bind]
      rw [StateTransitionSpec.clientState_bind]
    rw [hst_dp]
    have hsl_eq : (if io.usePaged = 0 ∨
        (extractPageUnperm io.pgL s₂.mem).cleanPhase = 0 then 0 else 24) =
        (if io.usePaged = 0 ∨
          (extractPageUnperm io.pgL s.mem).cleanPhase = 0 then 0 else 24) := by
      by_cases h0 : io.usePaged = 0
      · simp [h0]
      · simp only [h0, false_or, (hpg₂ h0).1, (hpg₁ h0).1]
    rw [hns₂, hns₁] at hns₃ hio₃_raw href₃_raw
    rw [hsl_eq] at hio₃_raw
    refine ⟨hfr₃.trans (hfr₂.trans hfr₁), hns₃, hval₃, hio₃_raw, href₃_raw,
      fun addr ha => (hout₃ addr ha).trans ((hout₂ addr ha).trans (hout₁ addr ha)),
      fun hnz => ?_⟩
    obtain ⟨hu₁, hp₁⟩ := hpg₁ hnz
    obtain ⟨hu₂, hp₂⟩ := hpg₂ hnz
    obtain ⟨hvl₃, hti₃, hp₃⟩ := hpg₃ hnz
    have hst₁ : extractPagePair io.pgL s₁.mem = extractPagePair io.pgL s.mem :=
      congrArg PageUnpermState.st hu₁
    have hst₂ : extractPagePair io.pgL s₂.mem = extractPagePair io.pgL s₁.mem :=
      congrArg PageUnpermState.st hu₂
    refine ⟨by rw [hvl₃, hst₂, hst₁], by rw [hti₃, hst₂, hst₁], fun idx hidx => ?_⟩
    exact (hp₃ idx ((hst₂.trans hst₁).symm ▸ hidx)).trans
      ((hp₂ idx (hst₁.symm ▸ hidx)).trans (hp₁ idx hidx))
  · rw [ite_eq_right hlt_blk]
    have hp_ge : fb.fullBlocks * mp.K ≤ hitP := by
      by_contra hlt; exact hlt_blk ((Nat.div_lt_iff_lt_mul hK).mpr (Nat.lt_of_not_le hlt))
    exact fbPopTailAtProg_spec hmv hiov hdisj hfb hns_le hio href hp_ge hp_lt u how_p hpr_p

/-! ## Section 3: Block-Pool Drain and Pure-Slab Compaction Loops -/

private theorem PoolItemsRefines.comp_perm {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow ow' : ℕ → ℕ} {pr pr' : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs)
    (σ σ_inv : ℕ → ℕ)
    (hleft : ∀ p < nSide, σ_inv (σ p) = p)
    (hright : ∀ q < nSide, σ (σ_inv q) = q)
    (hlt : ∀ p < nSide, σ p < nSide)
    (hlt_inv : ∀ q < nSide, σ_inv q < nSide)
    (how : ∀ p < nSide, ow' p = ow (σ p))
    (hpr : ∀ p < nSide, pr' p = pr (σ p)) :
    PoolItemsRefines U V bBits hBkt nSide ow' pr' s_abs where
  slot_valid p hp := by
    rw [how p hp, hpr p hp]; exact h.slot_valid _ (hlt p hp)
  slot_inj p₁ hp₁ p₂ hp₂ he1 he2 := by
    rw [how p₁ hp₁, how p₂ hp₂] at he1
    rw [hpr p₁ hp₁, hpr p₂ hp₂] at he2
    have hin := h.slot_inj _ (hlt p₁ hp₁) _ (hlt p₂ hp₂) he1 he2
    have hσ := congrArg σ_inv hin
    rwa [hleft p₁ hp₁, hleft p₂ hp₂] at hσ
  models u v := by
    rw [h.models u v]
    constructor
    · rintro ⟨q, hq, h1, h2, h3⟩
      refine ⟨σ_inv q, hlt_inv q hq, ?_, ?_, ?_⟩
      · rw [how _ (hlt_inv q hq), hright q hq]; exact h1
      · rw [hpr _ (hlt_inv q hq), hright q hq]; exact h2
      · rw [hpr _ (hlt_inv q hq), hright q hq]; exact h3
    · rintro ⟨p, hp, h1, h2, h3⟩
      rw [how p hp] at h1; rw [hpr p hp] at h2 h3
      exact ⟨σ p, hlt p hp, h1, h2, h3⟩

/-- Step 1 of `enterFallbackProg`: undo any active partial `topSwap` (`topSwapAct = 1`). -/
private def fbUndoTopSwapBodyProg : (BlockPoolCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((mctx, ioctx), (src, dst)), cur) => do
    let (_, (((_, k), _), _)) := mctx
    fbSwapRangeProg (((mctx, ioctx), (src * k, dst * k)), cur)
    bpWriteScalarProg ((mctx, 13), 0)

private theorem frontier_fbUndoTopSwapBodyProg
    (x : (BlockPoolCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbUndoTopSwapBodyProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, p2c⟩⟩, ioctx⟩, ⟨src, dst⟩⟩, cur⟩
  unfold fbUndoTopSwapBodyProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, frontier_bpWriteScalarProg]
  exact frontier_fbSwapRangeProg _ cur s hw

private theorem realizesBounded_fbUndoTopSwapBody :
    RealizesBounded .exact fbUndoTopSwapBodyProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), (src, dst)), _) s =>
        src ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        dst ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsr := realizesBounded_fbSwapRange
  have hws := realizesBounded_bpWriteScalar
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨src, dst⟩⟩, cur⟩
    obtain ⟨hsrc_d, hdst_d, hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hsrc_d hdst_d hnc_w hK_ge
    have h13_w : 13 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hfr := frontier_fbSwapRangeProg ((mctx, ioctx), (src * k, dst * k)) cur s hiov.w_pos
    dsimp only [mctx, StateTransitionSpec.clientState] at hfr
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfr]
    first | exact hmv | exact hiov | exact h13_w | omega | (
      have h1 : src * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp hsrc_d
      omega) | (
      have h2 : dst * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp hdst_d
      omega))

private def fbUndoTopSwapCheckProg : (BlockPoolCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((mctx, ioctx), (src, dst)), cur) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if src ≤ nCap / k then
      if dst ≤ nCap / k then
        fbUndoTopSwapBodyProg (((mctx, ioctx), (src, dst)), cur)
      else pure ()
    else pure ()

private theorem frontier_fbUndoTopSwapCheckProg
    (x : (BlockPoolCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbUndoTopSwapCheckProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, ⟨src, dst⟩⟩, cur⟩
  unfold fbUndoTopSwapCheckProg; dsimp only
  split_ifs
  · exact frontier_fbUndoTopSwapBodyProg _ s hw
  all_goals rfl

private theorem realizesBounded_fbUndoTopSwapCheck :
    RealizesBounded .exact fbUndoTopSwapCheckProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hbd := realizesBounded_fbUndoTopSwapBody
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨src, dst⟩⟩, cur⟩
    obtain ⟨hmv, hiov⟩ := h
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega)

private def fbUndoTopSwapReadProg : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    let src ← bpReadScalarProg (mctx, 14)
    let dst ← bpReadScalarProg (mctx, 15)
    let cur ← bpReadScalarProg (mctx, 16)
    fbUndoTopSwapCheckProg (((mctx, ioctx), (src, dst)), cur)

private theorem frontier_fbUndoTopSwapReadProg (x : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbUndoTopSwapReadProg x)).frontier = s.frontier := by
  rcases x with ⟨mctx, ioctx⟩
  unfold fbUndoTopSwapReadProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  exact frontier_fbUndoTopSwapCheckProg _ s hw

private theorem realizesBounded_fbUndoTopSwapRead :
    RealizesBounded .exact fbUndoTopSwapReadProg
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hchk := realizesBounded_fbUndoTopSwapCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    have h12K := hmv.twelve_K_le
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge h12K
    have h16_w : 16 < 2 ^ w := by omega
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | omega)

private def fbUndoTopSwapProg : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    let act ← bpReadScalarProg (mctx, 13)
    if act = 1 then
      fbUndoTopSwapReadProg (mctx, ioctx)
    else
      pure ()

private theorem frontier_fbUndoTopSwapProg (x : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbUndoTopSwapProg x)).frontier = s.frontier := by
  rcases x with ⟨mctx, ioctx⟩
  unfold fbUndoTopSwapProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  split_ifs
  · exact frontier_fbUndoTopSwapReadProg _ s hw
  · rfl

private theorem realizesBounded_fbUndoTopSwap :
    RealizesBounded .exact fbUndoTopSwapProg
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrd := realizesBounded_fbUndoTopSwapRead
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    have h12K := hmv.twelve_K_le
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge h12K
    have h13_w : 13 < 2 ^ w := by omega
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | omega)

private theorem fbUndoTopSwapProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits w slack : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hcv : (extractBlockPool mp s.mem).CoreValid)
    (hns_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractBlockPool mp s.mem).nSide slack s.mem)
    (href : PoolItemsRefines U V bBits hBkt (extractBlockPool mp s.mem).nSide
      (fun p => ((extractBlockPool mp s.mem).ownerOf p).1) (slotIoPairAt io s.mem) s_abs) :
    let bp := extractBlockPool mp s.mem
    let s₁ := (Memory.spec 0).clientState s (fbUndoTopSwapProg (mp.toCtx, io.toCtx))
    let bp₁ := extractBlockPool mp s₁.mem
    s₁.frontier = s.frontier ∧
    bp₁.CoreValid ∧
    bp₁.topSwapAct = 0 ∧
    bp₁.nSide = bp.nSide ∧
    io.StateInv bp.nSide slack s₁.mem ∧
    PoolItemsRefines U V bBits hBkt bp.nSide
      (fun p => (bp₁.ownerOf p).1) (slotIoPairAt io s₁.mem) s_abs ∧
    (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → s₁.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s₁.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s₁.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  set bp := extractBlockPool mp s.mem
  have h16le := hmv.sixteen_MK_le_maxTail
  have hmt : mp.M * mp.K ≤ mp.maxTail := by
    rw [Nat.mul_assoc] at h16le
    exact (Nat.mul_le_mul_left_iff (by decide : 0 < 16)).mp h16le
  unfold fbUndoTopSwapProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩)]
  have hact_mem : s.mem (mp.metaBase + 13) = bp.topSwapAct := rfl
  rw [hact_mem]
  rcases (by have := hcv.topSwap_act_le; omega : bp.topSwapAct = 0 ∨ bp.topSwapAct = 1) with
    hact0 | hact1
  · rw [ite_eq_right (by omega : ¬(bp.topSwapAct = 1)), StateTransitionSpec.clientState_pure]
    exact ⟨rfl, hcv, hact0, rfl, hio, href, fun _ _ => rfl, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
  · rw [ite_eq_left hact1]
    obtain ⟨hcur_K, hsrc_B, hdst_B, _, hsrc_ne⟩ := hcv.topSwap_valid hact1
    have hK : 0 < mp.K := hcv.K_pos
    have hK_eq : bp.K = mp.K := rfl
    rw [hK_eq] at hcur_K
    have hBf_mul : bp.B_full * mp.K ≤ bp.nSide := by
      have := hcv.nSide_eq; rw [hK_eq] at this; omega
    have hb1_ns : bp.topSwapSrc * mp.K + bp.topSwapCur ≤ bp.nSide := by
      have : (bp.topSwapSrc + 1) * mp.K ≤ bp.B_full * mp.K := Nat.mul_le_mul_right _ hsrc_B
      rw [Nat.add_one_mul] at this; omega
    have hb2_ns : bp.topSwapDst * mp.K + bp.topSwapCur ≤ bp.nSide := by
      have : (bp.topSwapDst + 1) * mp.K ≤ bp.B_full * mp.K := Nat.mul_le_mul_right _ hdst_B
      rw [Nat.add_one_mul] at this; omega
    have hsrc_div : bp.topSwapSrc ≤ mp.nCap / mp.K :=
      (Nat.le_div_iff_mul_le hK).mpr ((Nat.le_add_right _ bp.topSwapCur).trans
        (hb1_ns.trans hns_le))
    have hdst_div : bp.topSwapDst ≤ mp.nCap / mp.K :=
      (Nat.le_div_iff_mul_le hK).mpr ((Nat.le_add_right _ bp.topSwapCur).trans
        (hb2_ns.trans hns_le))
    have hdisj_sr : bp.topSwapSrc * mp.K = bp.topSwapDst * mp.K ∨
        bp.topSwapSrc * mp.K + bp.topSwapCur ≤ bp.topSwapDst * mp.K ∨
        bp.topSwapDst * mp.K + bp.topSwapCur ≤ bp.topSwapSrc * mp.K := by
      rcases lt_trichotomy bp.topSwapSrc bp.topSwapDst with hlt | heq | hgt
      · refine Or.inr (Or.inl ?_)
        have : (bp.topSwapSrc + 1) * mp.K ≤ bp.topSwapDst * mp.K := Nat.mul_le_mul_right _ hlt
        rw [Nat.add_one_mul] at this; omega
      · exact absurd heq hsrc_ne
      · refine Or.inr (Or.inr ?_)
        have : (bp.topSwapDst + 1) * mp.K ≤ bp.topSwapSrc * mp.K := Nat.mul_le_mul_right _ hgt
        rw [Nat.add_one_mul] at this; omega
    obtain ⟨hfr_sr, hio_sr, harr_sr, hout_sr, hpg_sr⟩ :=
      fbSwapRangeProg_spec hmv hiov hio hns_le hb1_ns hb2_ns hdisj_sr
    set s_sr := (Memory.spec 0).clientState s
      (fbSwapRangeProg (((mp.toCtx, io.toCtx),
        (bp.topSwapSrc * mp.K, bp.topSwapDst * mp.K)), bp.topSwapCur))
    have hbp_sr : extractBlockPool mp s_sr.mem = bp :=
      extractBlockPool_congr hmv.w_pos hmv.K_ge hmt
        (fun a hma => hout_sr a (fun hia => hdisj a hma hia))
    set s₁ := (Memory.spec 0).clientState s_sr (bpWriteScalarProg ((mp.toCtx, 13), 0))
    have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 13 0
    have hbp₁_eq : extractBlockPool mp s₁.mem = { bp with topSwapAct := 0 } := by
      have h := extractBlockPool_writeScalar (k := 13) (val := 0) (hfr_sr.symm ▸ hmv)
        (Or.inr ⟨by decide, by decide⟩) (Nat.zero_le _) (s := s_sr)
      dsimp only at h
      rw [hbp_sr] at h
      simpa using h
    have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
    have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
    have hst_tot :
        (Memory.spec 0).clientState s (fbUndoTopSwapReadProg (mp.toCtx, io.toCtx)) = s₁ := by
      unfold fbUndoTopSwapReadProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
        StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
        StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩)]
      unfold fbUndoTopSwapCheckProg fbUndoTopSwapBodyProg; dsimp only
      have hs14 : s.mem (mp.metaBase + 14) = bp.topSwapSrc := rfl
      have hs15 : s.mem (mp.metaBase + 15) = bp.topSwapDst := rfl
      have hs16 : s.mem (mp.metaBase + 16) = bp.topSwapCur := rfl
      rw [hs14, hs15, hs16, hnc_eq, hk_eq, ite_eq_left hsrc_div, ite_eq_left hdst_div,
        StateTransitionSpec.clientState_bind]
    rw [hst_tot]
    have hio_out : ∀ addr, io.OwnsAddr addr → s₁.mem addr = s_sr.mem addr := fun a hia =>
      hwf_sc.1.mem_outside s_sr a (fun hma => hdisj a hma hia)
    obtain ⟨hio₁, harr₁⟩ := io.congr_of_outside hiov.w_pos hio_sr hio_out
    have hcv₁ : (extractBlockPool mp s₁.mem).CoreValid := by
      rw [hbp₁_eq]
      exact
        { M_pos := hcv.M_pos
          K_ge := hcv.K_ge
          bkt_bounds := hcv.bkt_bounds
          blkTag_lt := hcv.blkTag_lt
          blkTag_top := hcv.blkTag_top
          unres_fwd := hcv.unres_fwd
          unres_bwd := hcv.unres_bwd
          slab_fwd := hcv.slab_fwd
          slab_bwd := hcv.slab_bwd
          act_fwd := hcv.act_fwd
          act_bwd := hcv.act_bwd
          tb_fwd := hcv.tb_fwd
          freeTb_valid := hcv.freeTb_valid
          freeTb_inj := hcv.freeTb_inj
          tbHighWater_supply := hcv.tbHighWater_supply
          tbHighWater_le_max := hcv.tbHighWater_le_max
          topSwap_act_le := Nat.zero_le 1
          topSwap_valid := fun h => absurd h Nat.zero_ne_one
          tail_fwd := hcv.tail_fwd
          tail_bwd := hcv.tail_bwd }
    set σ := swapRangeIdx (bp.topSwapSrc * mp.K) (bp.topSwapDst * mp.K) bp.topSwapCur
    have div_mod_add : ∀ B off, off < mp.K →
        (B * mp.K + off) / mp.K = B ∧ (B * mp.K + off) % mp.K = off := fun B off hoff =>
      ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add],
       by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]⟩
    have how_σ : ∀ p < bp.nSide,
        ((extractBlockPool mp s₁.mem).ownerOf p).1 = (bp.ownerOf (σ p)).1 := by
      intro p _
      rw [hbp₁_eq]
      have h0_eff : ∀ B off, ({ bp with topSwapAct := 0 } : BlockPoolState).effBlk B off = B :=
        fun _ _ => by unfold BlockPoolState.effBlk; simp
      have h0_act : ∀ b, ({ bp with topSwapAct := 0 } : BlockPoolState).actCur b = bp.actCur b :=
        fun _ => rfl
      have heff_eq : p / mp.K = bp.effBlk (σ p / mp.K) (σ p % mp.K) ∧ p % mp.K = σ p % mp.K := by
        dsimp only [σ]; unfold swapRangeIdx
        by_cases h1 : bp.topSwapSrc * mp.K ≤ p ∧ p < bp.topSwapSrc * mp.K + bp.topSwapCur
        · rw [ite_eq_left h1]
          set off := p - bp.topSwapSrc * mp.K
          have hoff_cur : off < bp.topSwapCur := by omega
          have hoff_K : off < mp.K := hoff_cur.trans hcur_K
          have hp_eq : p = bp.topSwapSrc * mp.K + off := by omega
          rw [hp_eq, (div_mod_add _ _ hoff_K).1, (div_mod_add _ _ hoff_K).2,
            (div_mod_add _ _ hoff_K).1, (div_mod_add _ _ hoff_K).2]
          refine ⟨?_, rfl⟩
          unfold BlockPoolState.effBlk
          rw [ite_eq_left ⟨hact1, hoff_cur⟩, ite_eq_right hsrc_ne.symm, ite_eq_left rfl]
        · rw [ite_eq_right h1]
          by_cases h2 : bp.topSwapDst * mp.K ≤ p ∧ p < bp.topSwapDst * mp.K + bp.topSwapCur
          · rw [ite_eq_left h2]
            set off := p - bp.topSwapDst * mp.K
            have hoff_cur : off < bp.topSwapCur := by omega
            have hoff_K : off < mp.K := hoff_cur.trans hcur_K
            have hp_eq : p = bp.topSwapDst * mp.K + off := by omega
            rw [hp_eq, (div_mod_add _ _ hoff_K).1, (div_mod_add _ _ hoff_K).2,
              (div_mod_add _ _ hoff_K).1, (div_mod_add _ _ hoff_K).2]
            refine ⟨?_, rfl⟩
            unfold BlockPoolState.effBlk
            rw [ite_eq_left ⟨hact1, hoff_cur⟩, ite_eq_left rfl]
          · rw [ite_eq_right h2]
            refine ⟨?_, rfl⟩
            unfold BlockPoolState.effBlk
            by_cases hc : bp.topSwapAct = 1 ∧ p % mp.K < bp.topSwapCur
            · rw [ite_eq_left hc]
              have hp_dm := Nat.div_add_mod p mp.K
              rw [Nat.mul_comm] at hp_dm
              have hns : p / mp.K ≠ bp.topSwapSrc := by
                intro he; rw [he] at hp_dm; exact h1 ⟨by omega, by omega⟩
              have hnd : p / mp.K ≠ bp.topSwapDst := by
                intro he; rw [he] at hp_dm; exact h2 ⟨by omega, by omega⟩
              rw [ite_eq_right hns, ite_eq_right hnd]
            · rw [ite_eq_right hc]
      unfold BlockPoolState.ownerOf BlockPoolState.ownerOfTail
      dsimp only
      rw [h0_eff, h0_act, hK_eq, heff_eq.1, heff_eq.2]
    have href₁ := href.comp_involution σ
      (fun p _ => swapRangeIdx_involutive hdisj_sr)
      (fun p hp => swapRangeIdx_lt hb1_ns hb2_ns hp)
      how_σ
      (fun p hp => (harr₁ p hp).trans (harr_sr p hp))
    refine ⟨(hwf_sc.1.frontier_eq s_sr).trans hfr_sr, hcv₁, by rw [hbp₁_eq], by rw [hbp₁_eq],
      hio₁, href₁, fun addr ha => ?_, fun hnz => ?_⟩
    · have hma : ¬mp.OwnsMetaAddr addr := fun h => ha (Or.inl h)
      have hia : ¬io.OwnsAddr addr := fun h => ha (Or.inr h)
      exact (hwf_sc.1.mem_outside s_sr addr hma).trans (hout_sr addr hia)
    · obtain ⟨hu_sr, hp_sr⟩ := hpg_sr hnz
      have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → s₁.mem addr = s_sr.mem addr := fun a ha => by
        apply hio_out a; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
      have hu₁ : extractPageUnperm io.pgL s₁.mem = extractPageUnperm io.pgL s_sr.mem :=
        extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
      refine ⟨hu₁.trans hu_sr, fun idx hidx => ?_⟩
      unfold SlotIoLayout.StateInv at hio_sr; rw [ite_eq_right hnz] at hio_sr
      have hidx_sr : idx < (extractPagePair io.pgL s_sr.mem).virtLen io.partner.side := by
        have : extractPagePair io.pgL s_sr.mem = extractPagePair io.pgL s.mem :=
          congrArg PageUnpermState.st hu_sr
        rwa [this]
      have hp_lt_sr :
          (extractPageUnperm io.pgL s_sr.mem).toPhys io.partner.side idx < io.pgL.nCap :=
        (hio_sr.1.toPhys_lt hidx_sr).trans_le hio_sr.2.2.2.1
      have hp₁ : slotIoPairAt io.partner s₁.mem idx = slotIoPairAt io.partner s_sr.mem idx := by
        unfold slotIoPairAt
        have hp_nz : io.partner.usePaged ≠ 0 := hnz
        rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu₁]
        exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt_sr
      exact hp₁.trans (hp_sr idx hidx)

/-- Step 2 helpers: swap lanes `0, 1, 2` of `offSlabOwner` between `b₁` and `b₂`. -/
private def fbReadSlabLanePairProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((mctx, (b₁, b₂)), lane) => do
    let v₁ ← bpReadSlabOwnerProg (mctx, (b₁, lane))
    let v₂ ← bpReadSlabOwnerProg (mctx, (b₂, lane))
    pure (v₁, v₂)

private theorem state_fbReadSlabLanePairProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbReadSlabLanePairProg x) = s := by
  rcases x with ⟨⟨mctx, ⟨b₁, b₂⟩⟩, lane⟩
  unfold fbReadSlabLanePairProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg]
  rfl

private theorem realizesBounded_fbReadSlabLanePair :
    RealizesBounded .exact fbReadSlabLanePairProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ⟨b₁, b₂⟩⟩, lane⟩
    have hmv := h
    try simp only [runClient_state_bpReadSlabOwnerProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    exact hmv)

private def fbWriteSlabLanePairProg :
    ((BpMetaCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, (b₁, b₂)), lane), (v₁, v₂)) => do
    bpWriteSlabOwnerProg ((mctx, (b₁, lane)), v₂)
    bpWriteSlabOwnerProg ((mctx, (b₂, lane)), v₁)

private theorem frontier_fbWriteSlabLanePairProg
    (x : ((BpMetaCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbWriteSlabLanePairProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨mctx, ⟨b₁, b₂⟩⟩, lane⟩, ⟨v₁, v₂⟩⟩
  unfold fbWriteSlabLanePairProg
  rw [StateTransitionSpec.clientState_bind, frontier_bpWriteSlabOwnerProg,
    frontier_bpWriteSlabOwnerProg]

private theorem realizesBounded_fbWriteSlabLanePair :
    RealizesBounded .exact fbWriteSlabLanePairProg
      (WordEncoding.encode (α := ((BpMetaCtx × (ℕ × ℕ)) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, _), _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨⟨⟨mctx, ⟨b₁, b₂⟩⟩, lane⟩, ⟨v₁, v₂⟩⟩
    have hmv := h
    try simp only [runClient_frontier_bpWriteSlabOwnerProg] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    exact hmv)

private def fbSwapSlabLaneProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((mctx, (b₁, b₂)), lane) => do
    let vs ← fbReadSlabLanePairProg ((mctx, (b₁, b₂)), lane)
    fbWriteSlabLanePairProg (((mctx, (b₁, b₂)), lane), vs)

private theorem frontier_fbSwapSlabLaneProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbSwapSlabLaneProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ⟨b₁, b₂⟩⟩, lane⟩
  unfold fbSwapSlabLaneProg
  rw [StateTransitionSpec.clientState_bind, state_fbReadSlabLanePairProg,
    frontier_fbWriteSlabLanePairProg]

private theorem realizesBounded_fbSwapSlabLane :
    RealizesBounded .exact fbSwapSlabLaneProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrd := realizesBounded_fbReadSlabLanePair
  have hwr := realizesBounded_fbWriteSlabLanePair
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ⟨b₁, b₂⟩⟩, lane⟩
    have hmv := h
    have hs := state_fbReadSlabLanePairProg ((mctx, (b₁, b₂)), lane) s
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hs]
    exact hmv)

private def fbSwapSlabMeta3Prog : BpMetaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (mctx, (b₁, b₂)) => do
    fbSwapSlabLaneProg ((mctx, (b₁, b₂)), 0)
    fbSwapSlabLaneProg ((mctx, (b₁, b₂)), 1)
    fbSwapSlabLaneProg ((mctx, (b₁, b₂)), 2)

private theorem frontier_fbSwapSlabMeta3Prog (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbSwapSlabMeta3Prog x)).frontier = s.frontier := by
  rcases x with ⟨mctx, ⟨b₁, b₂⟩⟩
  unfold fbSwapSlabMeta3Prog
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    frontier_fbSwapSlabLaneProg, frontier_fbSwapSlabLaneProg, frontier_fbSwapSlabLaneProg]

private theorem realizesBounded_fbSwapSlabMeta3 :
    RealizesBounded .exact fbSwapSlabMeta3Prog
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsl := realizesBounded_fbSwapSlabLane
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨b₁, b₂⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    have h12K := hmv.twelve_K_le
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge h12K
    have h2_w : 2 < 2 ^ w := lt_of_le_of_lt (by omega) hnc_w
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hfr0 := frontier_fbSwapSlabLaneProg ((mctx, (b₁, b₂)), 0) s
    set s₀ := ((Memory.spec 0).runClient s (fbSwapSlabLaneProg ((mctx, (b₁, b₂)), 0))).2.1
    have hfr1 := frontier_fbSwapSlabLaneProg ((mctx, (b₁, b₂)), 1) s₀
    dsimp only [mctx, s₀, StateTransitionSpec.clientState] at hfr0 hfr1
    try dsimp only [Fits] at *
    try rw [hfr1]
    try rw [hfr0]
    first | exact hmv | omega)

private def fbCompactDoRangeProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, ioctx), (sPure, P)) => do
    let (_, (((_, k), _), _)) := mctx
    let b₁ ← pure (sPure * k)
    let b₂ ← pure (P * k)
    fbSwapRangeProg (((mctx, ioctx), (b₁, b₂)), k)

private theorem frontier_fbCompactDoRangeProg (x : BlockPoolCtx × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbCompactDoRangeProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, p2c⟩⟩, ioctx⟩, ⟨sPure, P⟩⟩
  unfold fbCompactDoRangeProg; dsimp only; simp only [pure_bind]
  exact frontier_fbSwapRangeProg _ k s hw

private theorem realizesBounded_fbCompactDoRange :
    RealizesBounded .exact fbCompactDoRangeProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), (sPure, P)) s =>
        sPure ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        P ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsr := realizesBounded_fbSwapRange
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨sPure, P⟩⟩
    obtain ⟨hsp_d, hP_d, hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hsp_d hP_d hnc_w hK_ge
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | (
      have h1 : sPure * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp hsp_d
      omega) | (
      have h2 : P * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp hP_d
      omega))

private def fbCompactSwapBlkBodyProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, ioctx), sp) => do
    fbCompactDoRangeProg ((mctx, ioctx), sp)
    fbSwapSlabMeta3Prog (mctx, sp)

private theorem frontier_fbCompactSwapBlkBodyProg (x : BlockPoolCtx × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbCompactSwapBlkBodyProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ioctx⟩, sp⟩
  unfold fbCompactSwapBlkBodyProg
  rw [StateTransitionSpec.clientState_bind, frontier_fbSwapSlabMeta3Prog]
  exact frontier_fbCompactDoRangeProg _ s hw

private theorem realizesBounded_fbCompactSwapBlkBody :
    RealizesBounded .exact fbCompactSwapBlkBodyProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), (sPure, P)) s =>
        sPure ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        P ≤ (BpMetaLayout.ofCtx mctx).nCap / (BpMetaLayout.ofCtx mctx).K ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hdr := realizesBounded_fbCompactDoRange
  have hsm := realizesBounded_fbSwapSlabMeta3
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ioctx⟩, ⟨sPure, P⟩⟩
    obtain ⟨hsp_d, hP_d, hmv, hiov⟩ := h
    have hfr := frontier_fbCompactDoRangeProg ((mctx, ioctx), (sPure, P)) s hiov.w_pos
    dsimp only [StateTransitionSpec.clientState] at hfr
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfr]
    first | exact hsp_d | exact hP_d | exact hmv | exact hiov)

private def fbCompactSwapBlkProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, ioctx), (sPure, P)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if sPure ≤ nCap / k then
      if P ≤ nCap / k then
        fbCompactSwapBlkBodyProg ((mctx, ioctx), (sPure, P))
      else pure ()
    else pure ()

private theorem frontier_fbCompactSwapBlkProg (x : BlockPoolCtx × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbCompactSwapBlkProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩, ⟨sPure, P⟩⟩
  unfold fbCompactSwapBlkProg; dsimp only
  split_ifs
  · exact frontier_fbCompactSwapBlkBodyProg _ s hw
  all_goals rfl

private theorem realizesBounded_fbCompactSwapBlk :
    RealizesBounded .exact fbCompactSwapBlkProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hbd := realizesBounded_fbCompactSwapBlkBody
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨sPure, P⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega)

private def fbCompactPureHitProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((bpctx, tag), (P, sPure)) =>
    if tag = 1 ∧ sPure ≤ P then do
      fbCompactSwapBlkProg (bpctx, (sPure, P))
      pure (P + 1, sPure + 1)
    else
      pure (P + 1, sPure)

private theorem frontier_fbCompactPureHitProg
    (x : (BlockPoolCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx x.1.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbCompactPureHitProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨bpctx, tag⟩, ⟨P, sPure⟩⟩
  unfold fbCompactPureHitProg; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    exact frontier_fbCompactSwapBlkProg (bpctx, (sPure, P)) s hw
  · rfl

private theorem realizesBounded_fbCompactPureHit :
    RealizesBounded .exact fbCompactPureHitProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (((mctx, ioctx), _), (P, _)) s =>
        P < (BpMetaLayout.ofCtx mctx).nCap ∧
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hcs := realizesBounded_fbCompactSwapBlk
  realize
  all_goals (
    rcases d with ⟨⟨⟨mctx, ioctx⟩, tag⟩, ⟨P, sPure⟩⟩
    obtain ⟨hP_lt, hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | exact hw1 | omega)

private def fbCompactPureStepProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((mctx, ioctx), B_full), (P, sPure)) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if P < B_full ∧ P < nCap then do
      let tag ← bpReadSlabOwnerProg (mctx, (P, 0))
      fbCompactPureHitProg (((mctx, ioctx), tag), (P, sPure))
    else
      pure (P, sPure)

private theorem memoryCost_fbCompactPureStep_pos
    (x : (BlockPoolCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (fbCompactPureStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩, _⟩,
    ⟨_, _⟩⟩
  simp [fbCompactPureStepProg, bpReadScalarProg]

private theorem frontier_fbCompactPureStep (d : BlockPoolCtx × ℕ) (acc : ℕ × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx d.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbCompactPureStepProg (d, acc))).frontier = s.frontier := by
  rcases d with ⟨⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, ioctx⟩, B_full⟩
  rcases acc with ⟨P, sPure⟩
  unfold fbCompactPureStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg]
    exact frontier_fbCompactPureHitProg _ s hw
  · rfl

private theorem realizesBounded_fbCompactPureStep :
    RealizesBounded .exact fbCompactPureStepProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrso := realizesBounded_bpReadSlabOwner
  have hhit := realizesBounded_fbCompactPureHit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, B_full⟩, ⟨P, sPure⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    dsimp only [BpMetaLayout.ofCtx] at *
    try simp only [runClient_state_bpReadScalarProg, runClient_state_bpReadSlabOwnerProg,
      Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | exact hw1 | omega)

private def fbCompactPureLoopProg :
    ((BlockPoolCtx × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((d, acc), fuel) => iterate fbCompactPureStepProg d fuel acc

private theorem realizesBounded_fbCompactPureLoop :
    RealizesBounded .exact fbCompactPureLoopProg
      (WordEncoding.encode (α := ((BlockPoolCtx × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((d, acc), fuel) s =>
        iterationSafe fbCompactPureStepProg
          (fun w' (((mctx, ioctx), _), _) s' =>
            (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier ∧
            (SlotIoLayout.ofCtx ioctx).Valid w' s'.frontier)
          w d fuel acc s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BlockPoolCtx × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizesBounded_fbCompactPureStep
    memoryCost_fbCompactPureStep_pos

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

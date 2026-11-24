/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageBaseProg
-- Page-arena primitives shared across the LargePageBaseProg/LargePageCoreProg split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageBaseProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deamortized Page-Arena Rebalancing and Frame Bounds (`LargePageCoreProg`)

This module builds on `LargePageBaseProg` to certify `O(1)` physical tail-slot swapping, background
promotion/demotion job launch, single-tick background rebalancing, and batched `fuel`-tick
rebalancing (`pageSwapTailSlotsProg`, `pageMaybeStartJobProg`, `pageTickBoundedProg`,
`pageRunTicksBatchProg`, `RealizesBounded .exact`, `¬ReadsWidth`) together with compositional
`BoundedFrameProg` cost and memory-frame bounds across all `PageArenaLayout` operations for the
deamortized worst-case WHP resizable succinct dictionary ([Bender, Farach-Colton, J. Kuszmaul, and
W. Kuszmaul, SOSA 2024, Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.pageSwapTailSlotsProg`,
  `pageMaybeStartJobProg`, `pageTickBoundedProg`, `pageRunTicksBatchProg`: `O(1)` tail-swap, job
  launch, single-tick rebalancer, and batched rebalancer in `Memory.Prog`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.PageArenaLayout.OwnsAddr`: combined
  metadata and item-arena modifiable word predicate.

## Main results

* `realizesBounded_pageSwapTailSlots`, `pageSwapTailSlotsProg_spec`,
  `realizesBounded_pageMaybeStartJob`, `pageMaybeStartJobProg_spec`,
  `realizesBounded_pageTick`, `pageTickBoundedProg_spec`,
  `realizesBounded_pageRunTicksBatch`, `pageRunTicksBatchProg_spec`: `RealizesBounded .exact`
  certificates (`¬ReadsWidth`) and exact `PagePairState` refinement theorems.
* `pageToPhysBoundedProg_frame`, `pageReadVirtBoundedProg_frame`, `pageWriteVirtBoundedProg_frame`,
  `pageRunTicksBatchProg_frame`, `pageInitScalarsProg_frame`, `pageInitDirBatchProg_frame`,
  `pageInitTailBatchProg_frame`: `BoundedFrameProg` cost and memory-frame certificates.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ### `O(1)` Tail-Swap, Job Launch, Background Tick, and Batched Rebalance (`¬ReadsWidth`) -/

/-- Swap physical tail slots `(p₁, p₂)` in both `offTail` metadata and physical `itemBase`
(`RealizesBounded .exact`, `¬ReadsWidth`). -/
def pageSwapTailSlotsProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (p₁, p₂)) =>
    if p₁ = p₂ then
      pure ()
    else if p₁ < nc ∧ p₂ < nc then do
      let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
      let r₁ ← pure (p₁ % (8 * pg))
      let r₂ ← pure (p₂ % (8 * pg))
      let ow₁ ← pageReadTailOwnerProg (ctx, r₁)
      let ow₂ ← pageReadTailOwnerProg (ctx, r₂)
      pageWriteTailResProg ((ctx, ow₁), r₂)
      pageWriteTailResProg ((ctx, ow₂), r₁)
      pageWriteTailOwnerProg ((ctx, r₁), ow₂)
      pageWriteTailOwnerProg ((ctx, r₂), ow₁)
      pageSwapPhysProg (ctx, (p₁, p₂))
    else
      pure ()

@[simp] theorem runClient_frontier_pageSwapTailSlotsProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageSwapTailSlotsProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageSwapTailSlotsProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageSwapTailSlots :
    RealizesBounded .exact pageSwapTailSlotsProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrto := realizesBounded_pageReadTailOwner
  have hwtr := realizesBounded_pageWriteTailRes
  have hwto := realizesBounded_pageWriteTailOwner
  have hsp := realizesBounded_pageSwapPhys
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨p₁, p₂⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, _, _, _, _⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [StateTransitionSpec.clientState] at *
    try simp only [runClient_frontier_pageWriteTailOwnerProg] at *
    try simp only [runClient_frontier_pageWriteTailResProg] at *
    try simp only [runClient_state_pageReadTailOwnerProg] at *
    try exact hv0
    try (
      have hm8 : ∀ x : ℕ, x % (8 * pg) < 8 * pg := fun x => Nat.mod_lt x (by omega)
      have h1 := hm8 p₁; have h2 := hm8 p₂
      omega))

theorem pageSwapTailSlotsProg_spec {L : PageArenaLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (hv : (extractPagePair L s.mem).Valid)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap)
    {p₁ p₂ : ℕ}
    (hp₁_lo : (extractPagePair L s.mem).totalPages * L.pgB ≤ p₁)
    (hp₁_hi : p₁ < (extractPagePair L s.mem).totalItems)
    (hp₂_lo : (extractPagePair L s.mem).totalPages * L.pgB ≤ p₂)
    (hp₂_hi : p₂ < (extractPagePair L s.mem).totalItems) :
    let u := extractPageUnperm L s.mem
    let res := u.st.swapTailSlots p₁ p₂
    let s' := (Memory.spec 0).clientState s (pageSwapTailSlotsProg (L.toCtx, (p₁, p₂)))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = { u with st := res.1 } ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  obtain ⟨hw, _, _, _, _, _, hpg16, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  dsimp only
  refine ⟨by simpa only [StateTransitionSpec.clientState] using
    runClient_frontier_pageSwapTailSlotsProg (L.toCtx, (p₁, p₂)) s, ?_⟩
  unfold pageSwapTailSlotsProg PagePairState.swapTailSlots
  dsimp only [PageArenaLayout.toCtx]
  by_cases heq : p₁ = p₂
  · rw [ite_eq_left heq, ite_eq_left heq]
    exact ⟨rfl, rfl⟩
  · have hp_nc : p₁ < L.nCap ∧ p₂ < L.nCap := ⟨hp₁_hi.trans_le hti, hp₂_hi.trans_le hti⟩
    rw [ite_eq_right heq, ite_eq_left hp_nc, ite_eq_right heq]
    have hB : 0 < L.pgB := hps ▸ hv.pageSize_pos
    have hr_read : ∀ p, p % (8 * L.pgB) < 8 * L.pgB →
        (Memory.spec 0).clientResult s (pageReadTailOwnerProg (L.toCtx, p % (8 * L.pgB))) =
          (if st.tailOwnerSide (p % (8 * L.pgB)) then 1 else 0,
            st.tailOwnerRing (p % (8 * L.pgB))) := fun p hr_lt => by
      unfold pageReadTailOwnerProg
      dsimp only [PageArenaLayout.toCtx, st, u, extractPageUnperm, extractPagePair]
      simp only [hr_lt, ↓reduceIte, pure_bind, prog_clientResult_bind,
        clientResult_readPackedCompGenProg, runClient_state_readPackedCompGenProg,
        prog_clientResult_pure]
      congr 1
      set enc := readPacked (L.metaBase + L.offTail) L.ptrB L.w s.mem (8 * L.pgB + p % (8 * L.pgB))
      rcases Nat.mod_two_eq_zero_or_one enc with h0 | h1
      · simp [h0]
      · simp [h1]
    have hr₁_lt : p₁ % (8 * L.pgB) < 8 * L.pgB := Nat.mod_lt _ (by omega)
    have hr₂_lt : p₂ % (8 * L.pgB) < 8 * L.pgB := Nat.mod_lt _ (by omega)
    obtain ⟨hk₁_lt, _, _⟩ := hv.tail_owner p₁ (hps.symm ▸ hp₁_lo) hp₁_hi
    obtain ⟨hk₂_lt, _, _⟩ := hv.tail_owner p₂ (hps.symm ▸ hp₂_lo) hp₂_hi
    rw [hps] at hk₁_lt hk₂_lt
    set r₁ := p₁ % (8 * L.pgB)
    set r₂ := p₂ % (8 * L.pgB)
    have how₁ : ((Memory.spec 0).runClient s
        (pageReadTailOwnerProg (L.toCtx, r₁))).1 =
        (if st.tailOwnerSide r₁ then 1 else 0, st.tailOwnerRing r₁) := hr_read p₁ hr₁_lt
    have how₂ : ((Memory.spec 0).runClient s
        (pageReadTailOwnerProg (L.toCtx, r₂))).1 =
        (if st.tailOwnerSide r₂ then 1 else 0, st.tailOwnerRing r₂) := hr_read p₂ hr₂_lt
    dsimp only [PageArenaLayout.toCtx] at how₁ how₂
    have hsb_if : ∀ b : Bool, (if (if b then 1 else 0) = 0 then 0 else 4 * L.pgB) =
        (if b then 4 * L.pgB else 0) := fun b => by cases b <;> rfl
    have hsb_1 : ∀ b : Bool, (if (if b then 1 else 0) = 0 then 0 else 1) =
        (if b then 1 else 0) := fun b => by cases b <;> rfl
    have hc_r₁ : r₁ < 8 * L.pgB ∧ st.tailOwnerRing r₂ < 8 * L.pgB := ⟨hr₁_lt, by omega⟩
    have hc_r₂ : r₂ < 8 * L.pgB ∧ st.tailOwnerRing r₁ < 8 * L.pgB := ⟨hr₂_lt, by omega⟩
    set m_w4 := writePacked (L.metaBase + L.offTail) L.ptrB L.w
      (writePacked (L.metaBase + L.offTail) L.ptrB L.w
        (writePacked (L.metaBase + L.offTail) L.ptrB L.w
          (writePacked (L.metaBase + L.offTail) L.ptrB L.w s.mem
            ((if st.tailOwnerSide r₁ then 4 * L.pgB else 0) + st.tailOwnerRing r₁) r₂)
          ((if st.tailOwnerSide r₂ then 4 * L.pgB else 0) + st.tailOwnerRing r₂) r₁)
        (8 * L.pgB + r₁) ((if st.tailOwnerSide r₂ then 1 else 0) + 2 * st.tailOwnerRing r₂))
      (8 * L.pgB + r₂) ((if st.tailOwnerSide r₁ then 1 else 0) + 2 * st.tailOwnerRing r₁)
    obtain ⟨hsw_eq, hsw_ar⟩ := swapPairGenProg_arena_eq hw hm_ib ho1 ho2 ⟨m_w4, s.frontier⟩ p₁ p₂
    dsimp only [StateTransitionSpec.clientState] at hsw_eq hsw_ar
    obtain ⟨hu1, ha1⟩ := extractPageUnperm_writeTailRes hw ho1 ho2 hm_ib s.mem
      (st.tailOwnerSide r₁) hk₁_lt (hr₂_lt.trans (by omega))
    obtain ⟨hu2, ha2⟩ := extractPageUnperm_writeTailRes hw ho1 ho2 hm_ib _
      (st.tailOwnerSide r₂) hk₂_lt (hr₁_lt.trans (by omega))
    obtain ⟨hu3, ha3⟩ := extractPageUnperm_writeTailOwner hw hpg16 ho1 ho2 hm_ib _
      hr₁_lt (by omega : st.tailOwnerRing r₂ < 8 * L.pgB) (st.tailOwnerSide r₂)
    obtain ⟨hu4, ha4⟩ := extractPageUnperm_writeTailOwner hw hpg16 ho1 ho2 hm_ib _
      hr₂_lt (by omega : st.tailOwnerRing r₁ < 8 * L.pgB) (st.tailOwnerSide r₁)
    refine ⟨?_, ?_⟩
    all_goals (
      unfold StateTransitionSpec.clientState
      simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
        runClient_state_pageReadTailOwnerProg, how₁, how₂]
      unfold pageWriteTailResProg pageWriteTailOwnerProg pageSwapPhysProg
      dsimp only
      rw [ite_eq_left hk₁_lt, ite_eq_left hk₂_lt,
        ite_eq_left hc_r₁, ite_eq_left hc_r₂, ite_eq_left hp_nc]
      simp only [pure_bind, runClient_state_writePackedCompGenProg, hsb_if, hsb_1])
    · rw [hsw_eq]; dsimp only [m_w4]; rw [hu4, hu3, hu2, hu1]
      dsimp only [u, st, extractPageUnperm] at hps ⊢; rw [hps]
    · rw [hsw_ar]; dsimp only [m_w4]; rw [ha4, ha3, ha2, ha1, applySwaps_cons, applySwaps_nil]

/-- Choose between `demoteBuild` (`3`) and `demoteSwap` (`2`) when launching a demotion job. -/
def pageStartDemoteCheckProg :
    PageArenaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog (ℕ × (ℕ × (ℕ × ℕ)))
  | (ctx, ((sb, qs), Q)) => do
    let qm1 ← pure (qs - 1)
    let pLast ← pageReadPageOfProg (ctx, (sb, qm1))
    if pLast = Q - 1 then
      pure (1, (3, (sb, 0)))
    else
      pure (1, (2, (sb, 0)))

@[simp] theorem runClient_state_pageStartDemoteCheckProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageStartDemoteCheckProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageStartDemoteCheckProg; dsimp only
  simp only [pure_bind, prog_runClient_state_bind, runClient_state_pageReadPageOfProg]
  split_ifs <;> simp

theorem realizesBounded_pageStartDemoteCheck :
    RealizesBounded .exact pageStartDemoteCheckProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      (fun w (ctx, ((_, qs), Q)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧ 0 < qs ∧ 0 < Q)
      (fun _ _ => 0) := by
  have hrpo := realizesBounded_pageReadPageOf
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, qs⟩, Q⟩⟩
    obtain ⟨hv0, hqs, hQ⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hsb_w : Fits w sb := hwords 11
    have hqs_w : Fits w qs := hwords 12
    have hQ_w : Fits w Q := hwords 13
    try dsimp only [Fits] at *
    first | exact hv0 | omega)

/-- Check promotion/demotion thresholds for side `sideBit` given `(q0, q1)` and tail count `r`. -/
def pageStartSideCheckProg :
    (PageArenaCtx × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog (ℕ × (ℕ × (ℕ × ℕ)))
  | (((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sideBit),
      ((q0, q1), r))) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let sb ← pure (if sideBit = 0 then 0 else 1)
    let qs ← pure (if sideBit = 0 then q0 else q1)
    if 11 * pg ≤ 4 * r then
      pure (1, (1, (sb, 0)))
    else if 0 < qs ∧ 4 * r ≤ 5 * pg then do
      let Q_w ← pure (q0 + q1)
      pageStartDemoteCheckProg (ctx, ((sb, qs), Q_w))
    else
      pure (0, (0, (0, 0)))

@[simp] theorem runClient_state_pageStartSideCheckProg
    (x : (PageArenaCtx × ℕ) × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageStartSideCheckProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageStartSideCheckProg; dsimp only
  simp only [pure_bind]
  split_ifs <;> simp

theorem realizesBounded_pageStartSideCheck :
    RealizesBounded .exact pageStartSideCheckProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      (fun w ((ctx, _), ((q0, q1), r)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        q0 + q1 ≤ (PageArenaLayout.ofCtx ctx).maxPages ∧
        r < 4 * (PageArenaLayout.ofCtx ctx).pgB)
      (fun _ _ => 0) := by
  have hdc := realizesBounded_pageStartDemoteCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩,
      ⟨⟨q0, q1⟩, r⟩⟩
    obtain ⟨hv0, hQ, hr⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, _, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> first | exact hv0 | omega)

/-- Check one side `sideBit ∈ {0, 1}` for `maybeStartJob`, returning `(flag, (jk, (js, jc)))`. -/
def pageStartSideProg : PageArenaCtx × ℕ → Memory.Prog (ℕ × (ℕ × (ℕ × ℕ)))
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sideBit) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let q0 ← Memory.read (mb + 21)
    let q1 ← Memory.read (mb + 22)
    let r ← Memory.read (mb + if sideBit = 0 then 23 else 24)
    if q0 < mp ∧ q1 < mp ∧ q0 + q1 ≤ mp ∧ r < 4 * pg then
      pageStartSideCheckProg ((ctx, sideBit), ((q0, q1), r))
    else
      pure (0, (0, (0, 0)))

@[simp] theorem runClient_state_pageStartSideProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (pageStartSideProg x)) = s := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageStartSideProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read]
  split_ifs <;> simp

theorem realizesBounded_pageStartSide :
    RealizesBounded .exact pageStartSideProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hchk := realizesBounded_pageStartSideCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have hfr_w := hmem.1
    have hsb_w : Fits w sb := hwords 11
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> first | exact hv0 | omega)

/-- Realize `PagePairState.maybeStartJob` in `Memory.Prog` (`¬ReadsWidth`). -/
def pageMaybeStartJobProg : PageArenaCtx → Memory.Prog Unit
  | ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)) => do
    let jk ← Memory.read (mb + 27)
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if jk = 0 ∨ 4 ≤ jk then do
      let z0 ← pure 0
      let c1 ← pure 1
      let o0 ← pageStartSideProg (ctx, z0)
      if o0.1 = 1 then
        pageWriteJobProg (mb, o0.2)
      else do
        let o1 ← pageStartSideProg (ctx, c1)
        if o1.1 = 1 then
          pageWriteJobProg (mb, o1.2)
        else
          pure ()
    else
      pure ()

@[simp] theorem runClient_frontier_pageMaybeStartJobProg
    (ctx : PageArenaCtx) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageMaybeStartJobProg ctx))).frontier =
      s.frontier := by
  rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageMaybeStartJobProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read]
  split_ifs
  · simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
      runClient_state_pageStartSideProg]
    split_ifs
    · simp
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_pageStartSideProg]
      split_ifs <;> simp
  · simp

theorem realizesBounded_pageMaybeStartJob :
    RealizesBounded .exact pageMaybeStartJobProg
      (WordEncoding.encode (α := PageArenaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ctx s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hss := realizesBounded_pageStartSide
  have hwj := realizesBounded_pageWriteJob
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageStartSideProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    first | exact hv0 | omega)

theorem pageMaybeStartJobProg_spec {L : PageArenaLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (htc_lt : ∀ side, (extractPagePair L s.mem).tailCount side < 4 * L.pgB)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hmp : (extractPagePair L s.mem).totalPages < L.maxPages) :
    let u := extractPageUnperm L s.mem
    let s' := (Memory.spec 0).clientState s (pageMaybeStartJobProg L.toCtx)
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = { u with st := u.st.maybeStartJob } ∧
    arenaPairAt L s'.mem = arenaPairAt L s.mem := by
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hps_st : st.pageSize = L.pgB := hps
  refine ⟨by simpa only [StateTransitionSpec.clientState] using
    runClient_frontier_pageMaybeStartJobProg L.toCtx s, ?_⟩
  have hside_spec : ∀ side : Bool,
      let sb := if side then 1 else 0
      let o_pure : Option PageJob :=
        if 11 * st.pageSize ≤ 4 * st.tailCount side then some (.promote side 0)
        else if 0 < st.fullPages side ∧ 4 * st.tailCount side ≤ 5 * st.pageSize then
          if st.pageOf side (st.fullPages side - 1) = st.totalPages - 1 then
            some (.demoteBuild side 0)
          else some (.demoteSwap side 0)
        else none
      (Memory.spec 0).clientResult s (pageStartSideProg (L.toCtx, sb)) =
        match o_pure with
        | some j => (1, encodePageJob j)
        | none => (0, (0, (0, 0))) := fun side => by
    dsimp only
    have hq0_mp : st.fullPages false < L.maxPages :=
      lt_of_le_of_lt (Nat.le_add_right _ _) hmp
    have hq1_mp : st.fullPages true < L.maxPages :=
      lt_of_le_of_lt (Nat.le_add_left _ _) hmp
    have hQ_mp : st.fullPages false + st.fullPages true ≤ L.maxPages := hmp.le
    have hr_lt : st.tailCount side < 4 * L.pgB := htc_lt side
    unfold pageStartSideProg pageStartSideCheckProg pageStartDemoteCheckProg
    dsimp only [PageArenaLayout.toCtx]
    simp only [prog_clientResult_bind, prog_clientResult_read, prog_runClient_state_read]
    have hr_read : s.mem (L.metaBase + if (if side then 1 else 0) = 0 then 23 else 24) =
        st.tailCount side := by cases side <;> rfl
    have hq0_m : s.mem (L.metaBase + 21) = st.fullPages false := rfl
    have hq1_m : s.mem (L.metaBase + 22) = st.fullPages true := rfl
    have hq_read : (if (if side then 1 else 0) = 0 then st.fullPages false
        else st.fullPages true) = st.fullPages side := by cases side <;> rfl
    have hsb_1 : (if (if side then 1 else 0) = 0 then 0 else 1) =
        (if side then 1 else 0) := by cases side <;> rfl
    have hc_start : st.fullPages false < L.maxPages ∧
        st.fullPages true < L.maxPages ∧
        st.fullPages false + st.fullPages true ≤ L.maxPages ∧
        st.tailCount side < 4 * L.pgB := ⟨hq0_mp, hq1_mp, hQ_mp, hr_lt⟩
    simp only [hq0_m, hq1_m, hr_read]
    rw [ite_eq_left hc_start]
    simp only [pure_bind, hq_read, hsb_1]
    rw [hps_st]
    by_cases h11 : 11 * L.pgB ≤ 4 * st.tailCount side
    · rw [ite_eq_left h11, ite_eq_left h11]
      simp [prog_clientResult_pure, encodePageJob, encodePageJobKind,
        encodePageJobSide, encodePageJobCur]
    · rw [ite_eq_right h11, ite_eq_right h11]
      by_cases h5 : 0 < st.fullPages side ∧ 4 * st.tailCount side ≤ 5 * L.pgB
      · rw [ite_eq_left h5, ite_eq_left h5]
        have hqm_mp : st.fullPages side - 1 < L.maxPages :=
          (Nat.sub_lt h5.1 Nat.one_pos).trans (by cases side <;> assumption)
        have hpOF := pageReadPageOfProg_eq side hqm_mp s
        dsimp only [PageArenaLayout.toCtx] at hpOF
        simp only [StateTransitionSpec.clientState, prog_clientResult_bind,
          runClient_state_pageReadPageOfProg, hpOF]
        have htotP_eq : st.fullPages false + st.fullPages true = st.totalPages := rfl
        have hpo_st : (extractPagePair L s.mem).pageOf side (st.fullPages side - 1) =
            st.pageOf side (st.fullPages side - 1) := rfl
        rw [htotP_eq, hpo_st]
        by_cases hpo : st.pageOf side (st.fullPages side - 1) = st.totalPages - 1
        · rw [ite_eq_left hpo, ite_eq_left hpo]
          cases side <;> simp [prog_clientResult_pure, encodePageJob, encodePageJobKind,
            encodePageJobSide, encodePageJobCur]
        · rw [ite_eq_right hpo, ite_eq_right hpo]
          cases side <;> simp [prog_clientResult_pure, encodePageJob, encodePageJobKind,
            encodePageJobSide, encodePageJobCur]
      · rw [ite_eq_right h5, ite_eq_right h5]; simp [prog_clientResult_pure]
  have hust : u.st = st := rfl
  unfold pageMaybeStartJobProg PagePairState.maybeStartJob
  rw [hust]
  dsimp only [PageArenaLayout.toCtx]
  have hj_dec : st.job = decodePageJob (s.mem (L.metaBase + 27)) (s.mem (L.metaBase + 28))
      (s.mem (L.metaBase + 29)) := rfl
  by_cases hjk0 : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27)) = 0 ∨
      4 ≤ (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27))
  · have hjk0_m : s.mem (L.metaBase + 27) = 0 ∨ 4 ≤ s.mem (L.metaBase + 27) := hjk0
    have hj_idle : st.job = .idle := by
      rw [hj_dec]; unfold decodePageJob
      rcases hjk0_m with h0 | h4 <;> split_ifs <;> first | rfl | omega
    rw [hj_idle]
    have hs0 := hside_spec false
    simp only [Bool.false_eq_true, ↓reduceIte, PageArenaLayout.toCtx] at hs0
    have hs1 := hside_spec true
    simp only [↓reduceIte, PageArenaLayout.toCtx] at hs1
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_runClient_state_read]
    rw [ite_eq_left hjk0]
    simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
      runClient_state_pageStartSideProg, hs0]
    generalize ho0 :
      (if 11 * st.pageSize ≤ 4 * st.tailCount false then some (PageJob.promote false 0)
      else if 0 < st.fullPages false ∧ 4 * st.tailCount false ≤ 5 * st.pageSize then
        if st.pageOf false (st.fullPages false - 1) = st.totalPages - 1 then
          some (PageJob.demoteBuild false 0)
        else some (PageJob.demoteSwap false 0)
      else none) = opt0
    cases opt0 with
    | some j0 =>
      dsimp only; simp only [↓reduceIte]
      exact extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib s j0
    | none =>
      dsimp only
      simp only [StateTransitionSpec.clientState, Nat.zero_ne_one, ↓reduceIte,
        prog_runClient_state_bind, runClient_state_pageStartSideProg, hs1]
      generalize ho1' : (if 11 * st.pageSize ≤ 4 * st.tailCount true then
          some (PageJob.promote true 0)
        else if 0 < st.fullPages true ∧ 4 * st.tailCount true ≤ 5 * st.pageSize then
          if st.pageOf true (st.fullPages true - 1) = st.totalPages - 1 then
            some (PageJob.demoteBuild true 0)
          else some (PageJob.demoteSwap true 0)
        else none) = opt1
      cases opt1 with
      | some j1 =>
        dsimp only; simp only [↓reduceIte]
        exact extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib s j1
      | none => exact ⟨rfl, rfl⟩
  · have hjk0_m : ¬(s.mem (L.metaBase + 27) = 0 ∨ 4 ≤ s.mem (L.metaBase + 27)) := hjk0
    have hj_nonidle : st.job ≠ .idle := by
      rw [hj_dec]; unfold decodePageJob
      intro hid; apply hjk0_m
      have h123 : s.mem (L.metaBase + 27) = 1 ∨ s.mem (L.metaBase + 27) = 2 ∨
          s.mem (L.metaBase + 27) = 3 := by omega
      rcases h123 with h1 | h2 | h3
      · simp [h1] at hid
      · simp [h2] at hid
      · simp [h3] at hid
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_runClient_state_read]
    rw [ite_eq_right hjk0, prog_runClient_state_pure]
    cases hj_c : st.job with
    | idle => exact absurd hj_c hj_nonidle
    | _ => exact ⟨rfl, rfl⟩

/-- Write `(fullPages, tailCount, tailHead)` of side `sb` (`3` scalar writes, `¬ReadsWidth`). -/
def pageWriteSideMetaProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((mb, sb), (qVal, (rVal, thVal))) => do
    Memory.write (mb + if sb = 0 then 21 else 22) qVal
    Memory.write (mb + if sb = 0 then 23 else 24) rVal
    Memory.write (mb + if sb = 0 then 25 else 26) thVal

@[simp] theorem runClient_frontier_pageWriteSideMetaProg
    (x : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageWriteSideMetaProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨_, _⟩, ⟨_, _, _⟩⟩; simp [pageWriteSideMetaProg]

theorem realizesBounded_pageWriteSideMeta :
    RealizesBounded .exact pageWriteSideMetaProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((mb, _), _) s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨mb, sb⟩, ⟨qv, rv, thv⟩⟩
    obtain ⟨hw32, hfr⟩ := h
    have := hmem.1
    dsimp only [Fits] at *
    omega)

theorem extractPageUnperm_pageWriteSideMetaProg {L : PageArenaLayout} (hw : 0 < L.w)
    (ho1 : 32 ≤ L.offDir)
    (ho2 : L.offDir + packedWords (4 * L.maxPages) L.ptrB L.w ≤ L.offTail)
    (hm_ib : L.metaBase + L.offTail + packedWords (16 * L.pgB) L.ptrB L.w ≤ L.itemBase)
    (s : Memory.State) (side : Bool) (qv rv thv : ℕ) :
    let m' := ((Memory.spec 0).clientState s
      (pageWriteSideMetaProg ((L.metaBase, if side then 1 else 0), (qv, (rv, thv))))).mem
    let u := extractPageUnperm L s.mem
    extractPageUnperm L m' =
      { u with
        st :=
          { u.st with
            fullPages := Function.update u.st.fullPages side qv
            tailCount := Function.update u.st.tailCount side rv
            tailHead := Function.update u.st.tailHead side thv } } ∧
    arenaPairAt L m' = arenaPairAt L s.mem := by
  dsimp only
  unfold pageWriteSideMetaProg StateTransitionSpec.clientState
  have h21 : (if (if side then 1 else 0) = 0 then 21 else 22) = (if side then 22 else 21) := by
    cases side <;> rfl
  have h23 : (if (if side then 1 else 0) = 0 then 23 else 24) = (if side then 24 else 23) := by
    cases side <;> rfl
  have h25 : (if (if side then 1 else 0) = 0 then 25 else 26) = (if side then 26 else 25) := by
    cases side <;> rfl
  simp only [prog_runClient_state_bind, prog_runClient_state_write, h21, h23, h25]
  obtain ⟨_, _, _, _, _, hsc_th⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib _
    (if side then 26 else 25) thv
  obtain ⟨hu_th, ha_th⟩ := hsc_th side rfl
  obtain ⟨_, _, _, _, hsc_tc, _⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib _
    (if side then 24 else 23) rv
  obtain ⟨hu_tc, ha_tc⟩ := hsc_tc side rfl
  obtain ⟨_, _, _, hsc_fp, _, _⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib s.mem
    (if side then 22 else 21) qv
  obtain ⟨hu_fp, ha_fp⟩ := hsc_fp side rfl
  rw [hu_th, hu_tc, hu_fp, ha_th, ha_tc, ha_fp]
  exact ⟨rfl, rfl⟩

/-- Directory + job commit at the end of `PageJob.promote` (`3` calls, `¬ReadsWidth`). -/
def pageCommitPromoteDirProg : PageArenaCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sb, (qs, Q))) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let z0 ← pure 0
    pageWritePageOfProg ((ctx, (sb, qs)), Q)
    pageWriteOwnerProg ((ctx, Q), (sb, qs))
    pageWriteJobProg (mb, (z0, (z0, z0)))

@[simp] theorem runClient_frontier_pageCommitPromoteDirProg
    (x : PageArenaCtx × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageCommitPromoteDirProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _, _⟩⟩
  simp [pageCommitPromoteDirProg]

theorem realizesBounded_pageCommitPromoteDir :
    RealizesBounded .exact pageCommitPromoteDirProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwpo := realizesBounded_pageWritePageOf
  have hwo := realizesBounded_pageWriteOwner
  have hwj := realizesBounded_pageWriteJob
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, qs, Q⟩⟩
    have hv0 := h
    have hsb_w : Fits w sb := hwords 11
    have hqs_w : Fits w qs := hwords 12
    have hQ_w : Fits w Q := hwords 13
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageWriteOwnerProg] at *
    try simp only [runClient_frontier_pageWritePageOfProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

/-- `tickOne` branch for `PageJob.promote`. -/
def pageTickPromoteEndProg : PageArenaCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sb, (qs, Q))) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let tc ← pageReadTailCountsProg mb
    let rs ← pure (if sb = 0 then tc.1 else tc.2)
    let ths ← Memory.read (mb + if sb = 0 then 25 else 26)
    if qs < mp ∧ Q < mp ∧ pg ≤ rs ∧ ths < 4 * pg then do
      let q1 ← pure (qs + 1)
      let r1 ← pure (rs - pg)
      let th1 ← pure ((ths + pg) % (4 * pg))
      pageWriteSideMetaProg ((mb, sb), (q1, (r1, th1)))
      pageCommitPromoteDirProg (ctx, (sb, (qs, Q)))
    else
      pure ()

@[simp] theorem runClient_frontier_pageTickPromoteEndProg
    (x : PageArenaCtx × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageTickPromoteEndProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _, _⟩⟩
  unfold pageTickPromoteEndProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadTailCountsProg, prog_runClient_state_read]
  split_ifs <;> simp

theorem realizesBounded_pageTickPromoteEnd :
    RealizesBounded .exact pageTickPromoteEndProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrtc := realizesBounded_pageReadTailCounts
  have hwsm := realizesBounded_pageWriteSideMeta
  have hcpd := realizesBounded_pageCommitPromoteDir
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨sb, qs, Q⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have hfr_w := hmem.1
    have hsb_w : Fits w sb := hwords 11
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_frontier_pageWriteSideMetaProg] at *
    try simp only [runClient_state_pageReadTailCountsProg] at *
    (try split_ifs at *) <;> (try exact hv0))
  all_goals (
    set tc_v := (Memory.spec 0).clientResult s (pageReadTailCountsProg mb)
    have hr0_lt : tc_v.1 < 2 ^ w := by
      simp only [tc_v, pageReadTailCountsProg,
        prog_clientResult_bind, prog_clientResult_read,
        prog_runClient_state_read, prog_clientResult_pure]
      exact hmem.2 (mb + 23)
    have hr1_lt : tc_v.2 < 2 ^ w := by
      simp only [tc_v, pageReadTailCountsProg,
        prog_clientResult_bind, prog_clientResult_read,
        prog_runClient_state_read, prog_clientResult_pure]
      exact hmem.2 (mb + 24)
    have hm4 : ∀ x : ℕ, x % (4 * pg) < 4 * pg := fun x => Nat.mod_lt x (by omega)
    have hm_th := hm4 (s.mem (mb + if sb = 0 then 25 else 26) + pg)
    omega)

/-- Single slot-swap step of `PageJob.promote` (`¬ReadsWidth`). -/
def pageTickPromoteStepProg :
    PageArenaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), ((sb, cur), Q)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let p₁ ← pageTailPhysBoundedProg (ctx, (sb, cur))
    if cur < nc - Q * pg then do
      let p₂ ← pure (Q * pg + cur)
      let o1 ← pure 1
      let cur1 ← pure (cur + 1)
      pageSwapTailSlotsProg (ctx, (p₁, p₂))
      pageWriteJobProg (mb, (o1, (sb, cur1)))
    else
      pure ()

@[simp] theorem runClient_frontier_pageTickPromoteStepProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageTickPromoteStepProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageTickPromoteStepProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageTailPhysBoundedProg]
  split_ifs <;> simp

theorem realizesBounded_pageTickPromoteStep :
    RealizesBounded .exact pageTickPromoteStepProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, ((_, cur), Q)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        cur < (PageArenaLayout.ofCtx ctx).pgB ∧
        Q * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have htp := realizesBounded_pageTailPhys
  have hsts := realizesBounded_pageSwapTailSlots
  have hwj := realizesBounded_pageWriteJob
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, cur⟩, Q⟩⟩
    have hsb_w : Fits w sb := hwords 11
    obtain ⟨hv0, hcur, hQ_nc⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [StateTransitionSpec.clientState] at *
    try simp only [runClient_frontier_pageSwapTailSlotsProg] at *
    try simp only [runClient_state_pageTailPhysBoundedProg] at *
    first | exact hv0 | omega)

/-- Dispatch one tick of `PageJob.promote` (`¬ReadsWidth`). -/
def pageTickPromoteProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (js, cur)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let fp ← pageReadFullPagesProg mb
    let sb ← pure (if js = 0 then 0 else 1)
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then do
        let Q ← pure (fp.1 + fp.2)
        if cur < pg then
          pageTickPromoteStepProg (ctx, ((sb, cur), Q))
        else do
          let qs ← pure (if sb = 0 then fp.1 else fp.2)
          pageTickPromoteEndProg (ctx, (sb, (qs, Q)))
      else
        pure ()
    else
      pure ()

@[simp] theorem runClient_frontier_pageTickPromoteProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageTickPromoteProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageTickPromoteProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg]
  split_ifs <;> simp

theorem realizesBounded_pageTickPromote :
    RealizesBounded .exact pageTickPromoteProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have htps := realizesBounded_pageTickPromoteStep
  have htpe := realizesBounded_pageTickPromoteEnd
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨js, cur⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadFullPagesProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    set fp_v := (Memory.spec 0).clientResult s (pageReadFullPagesProg mb)
    have hq0_mul : fp_v.1 * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    try (
      have hq1_mul : fp_v.2 * pg ≤ ((nc - fp_v.1 * pg) / pg) * pg :=
        Nat.mul_le_mul_right pg (by omega)
      have hdiv1 : ((nc - fp_v.1 * pg) / pg) * pg ≤ nc - fp_v.1 * pg :=
        Nat.div_mul_le_self _ pg
      have hsum_mul : (fp_v.1 + fp_v.2) * pg = fp_v.1 * pg + fp_v.2 * pg := Nat.add_mul ..
      have hsum_le : fp_v.1 + fp_v.2 ≤ nc := by
        have := Nat.le_mul_of_pos_right (fp_v.1 + fp_v.2) (by omega : 0 < pg)
        omega)
    omega)

/-- Directory swap commit at the end of `PageJob.demoteSwap` (`4` calls, `¬ReadsWidth`). -/
def pageSwapDemoteDirProg :
    PageArenaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) → Memory.Prog Unit
  | (ctx, ((sb, qm1), ((pDem, pLast), owLast))) => do
    pageWritePageOfProg ((ctx, owLast), pDem)
    pageWritePageOfProg ((ctx, (sb, qm1)), pLast)
    pageWriteOwnerProg ((ctx, pDem), owLast)
    pageWriteOwnerProg ((ctx, pLast), (sb, qm1))

@[simp] theorem runClient_frontier_pageSwapDemoteDirProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageSwapDemoteDirProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩,
    ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩⟩
  simp [pageSwapDemoteDirProg]

theorem realizesBounded_pageSwapDemoteDir :
    RealizesBounded .exact pageSwapDemoteDirProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwpo := realizesBounded_pageWritePageOf
  have hwo := realizesBounded_pageWriteOwner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, qm1⟩, ⟨⟨pDem, pLast⟩, ⟨os, ov⟩⟩⟩⟩
    have hv0 := h
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_frontier_pageWriteOwnerProg] at *
    try simp only [runClient_frontier_pageWritePageOfProg] at *
    exact hv0)

/-- `tickOne` branch for `PageJob.demoteSwap`. -/
def pageTickDemoteSwapBodyProg :
    PageArenaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ)) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)),
      ((sb, qm1), ((pDem, pLast), cur))) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if cur < pg then do
      let idx1 ← pure (pDem * pg + cur)
      let idx2 ← pure (pLast * pg + cur)
      let c2 ← pure 2
      let cur1 ← pure (cur + 1)
      pageSwapPhysProg (ctx, (idx1, idx2))
      pageWriteJobProg (mb, (c2, (sb, cur1)))
    else do
      let owLast ← pageReadOwnerProg (ctx, pLast)
      let c3 ← pure 3
      let z0 ← pure 0
      pageSwapDemoteDirProg (ctx, ((sb, qm1), ((pDem, pLast), owLast)))
      pageWriteJobProg (mb, (c3, (sb, z0)))

@[simp] theorem runClient_frontier_pageTickDemoteSwapBodyProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageTickDemoteSwapBodyProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩
  unfold pageTickDemoteSwapBodyProg; dsimp only; split_ifs <;> simp

theorem realizesBounded_pageTickDemoteSwapBody :
    RealizesBounded .exact pageTickDemoteSwapBodyProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, (_, ((pDem, pLast), _))) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        pDem * (PageArenaLayout.ofCtx ctx).pgB + (PageArenaLayout.ofCtx ctx).pgB ≤
          (PageArenaLayout.ofCtx ctx).nCap ∧
        pLast * (PageArenaLayout.ofCtx ctx).pgB + (PageArenaLayout.ofCtx ctx).pgB ≤
          (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hro := realizesBounded_pageReadOwner
  have hsp := realizesBounded_pageSwapPhys
  have hsdd := realizesBounded_pageSwapDemoteDir
  have hwj := realizesBounded_pageWriteJob
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, qm1⟩, ⟨⟨pDem, pLast⟩, cur⟩⟩⟩
    have hsb_w : Fits w sb := hwords 11
    have hqm1_w : Fits w qm1 := hwords 12
    have hcur_w : Fits w cur := hwords 15
    obtain ⟨hv0, hpD, hpL⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [StateTransitionSpec.clientState] at *
    try simp only [runClient_frontier_pageSwapDemoteDirProg] at *
    try simp only [runClient_frontier_pageSwapPhysProg] at *
    try simp only [runClient_state_pageReadOwnerProg] at *
    first | exact hv0 | omega)

/-- Validate page counts and directory bounds before stepping `PageJob.demoteSwap`. -/
def pageTickDemoteSwapCheckProg :
    (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sb, cur)), fp)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let Q ← pure (fp.1 + fp.2)
    let qs ← pure (if sb = 0 then fp.1 else fp.2)
    if 0 < qs ∧ 0 < Q ∧ Q ≤ mp then do
      let qm1 ← pure (qs - 1)
      let pDem ← pageReadPageOfProg (ctx, (sb, qm1))
      if pDem < Q then do
        let pLast ← pure (Q - 1)
        pageTickDemoteSwapBodyProg (ctx, ((sb, qm1), ((pDem, pLast), cur)))
      else
        pure ()
    else
      pure ()

@[simp] theorem runClient_frontier_pageTickDemoteSwapCheckProg
    (x : (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s
      (pageTickDemoteSwapCheckProg x))).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨sb, _⟩⟩, ⟨_, _⟩⟩
  unfold pageTickDemoteSwapCheckProg; dsimp only
  simp only [pure_bind]
  by_cases hsb : sb = 0
  · simp only [hsb, ↓reduceIte]
    split_ifs with hc1
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_pageReadPageOfProg]
      split_ifs <;> simp
    · simp
  · simp only [hsb, ↓reduceIte]
    split_ifs with hc1
    · simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_pageReadPageOfProg]
      split_ifs <;> simp
    · simp

theorem realizesBounded_pageTickDemoteSwapCheck :
    RealizesBounded .exact pageTickDemoteSwapCheckProg
      (WordEncoding.encode (α := (PageArenaCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), fp) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        (fp.1 + fp.2) * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hrpo := realizesBounded_pageReadPageOf
  have hbody := realizesBounded_pageTickDemoteSwapBody
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨sb, cur⟩⟩, ⟨fp1, fp2⟩⟩
    have hsb_w : Fits w sb := hwords 11
    have hcur_w : Fits w cur := hwords 12
    obtain ⟨hv0, hfp_nc⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    try simp only [runClient_state_pageReadPageOfProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hsum_le : fp1 + fp2 ≤ nc := by
      have := Nat.le_mul_of_pos_right (fp1 + fp2) (by omega : 0 < pg)
      omega
    (try exact hv0); try omega)
  all_goals (
    have hlt_mul : ∀ {x y : ℕ}, x < y → x * pg + pg ≤ y * pg := fun hx => by
      rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right pg hx
    have := hlt_mul ‹_ < fp1 + fp2›
    have := hlt_mul (by omega : fp1 + fp2 - 1 < fp1 + fp2)
    omega)

/-- Dispatch one tick of `PageJob.demoteSwap` (`¬ReadsWidth`). -/
def pageTickDemoteSwapProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (js, cur)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let fp ← pageReadFullPagesProg mb
    let sb ← pure (if js = 0 then 0 else 1)
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then
        pageTickDemoteSwapCheckProg ((ctx, (sb, cur)), fp)
      else
        pure ()
    else
      pure ()

@[simp] theorem runClient_frontier_pageTickDemoteSwapProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageTickDemoteSwapProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageTickDemoteSwapProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg]
  split_ifs <;> simp

theorem realizesBounded_pageTickDemoteSwap :
    RealizesBounded .exact pageTickDemoteSwapProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have hchk := realizesBounded_pageTickDemoteSwapCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨js, cur⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadFullPagesProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    set fp_v := (Memory.spec 0).clientResult s (pageReadFullPagesProg mb)
    have hq0_mul : fp_v.1 * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    try (
      have hq1_mul : fp_v.2 * pg ≤ ((nc - fp_v.1 * pg) / pg) * pg :=
        Nat.mul_le_mul_right pg (by omega)
      have hdiv1 : ((nc - fp_v.1 * pg) / pg) * pg ≤ nc - fp_v.1 * pg :=
        Nat.div_mul_le_self _ pg
      have hsum_mul : (fp_v.1 + fp_v.2) * pg = fp_v.1 * pg + fp_v.2 * pg := Nat.add_mul ..
      have hsum_le : fp_v.1 + fp_v.2 ≤ nc := by
        have := Nat.le_mul_of_pos_right (fp_v.1 + fp_v.2) (by omega : 0 < pg)
        omega)
    omega)

/-- `tickOne` branch for `PageJob.demoteBuild`. -/
def pageTickDemoteBuildStepProg :
    PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)),
      ((sb, cur), (ths, Q))) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let k_cur ← pure ((ths + 3 * pg + cur) % (4 * pg))
    let res_cur ← pure (((Q - 1) * pg + cur) % (8 * pg))
    let c3 ← pure 3
    let cur1 ← pure (cur + 1)
    pageWriteTailResProg ((ctx, (sb, k_cur)), res_cur)
    pageWriteTailOwnerProg ((ctx, res_cur), (sb, k_cur))
    pageWriteJobProg (mb, (c3, (sb, cur1)))

@[simp] theorem runClient_frontier_pageTickDemoteBuildStepProg
    (x : PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s
      (pageTickDemoteBuildStepProg x))).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  simp [pageTickDemoteBuildStepProg]

theorem realizesBounded_pageTickDemoteBuildStep :
    RealizesBounded .exact pageTickDemoteBuildStepProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, ((_, cur), (ths, Q))) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        0 < Q ∧
        cur < (PageArenaLayout.ofCtx ctx).pgB ∧
        ths < 4 * (PageArenaLayout.ofCtx ctx).pgB ∧
        (Q - 1) * (PageArenaLayout.ofCtx ctx).pgB + cur < (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hwtr := realizesBounded_pageWriteTailRes
  have hwto := realizesBounded_pageWriteTailOwner
  have hwj := realizesBounded_pageWriteJob
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, cur⟩, ⟨ths, Q⟩⟩⟩
    have hsb_w : Fits w sb := hwords 11
    obtain ⟨hv0, hQ0, hcur, hths, hQ⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [StateTransitionSpec.clientState] at *
    try simp only [runClient_frontier_pageWriteTailOwnerProg] at *
    try simp only [runClient_frontier_pageWriteTailResProg] at *
    have hc1 : (ths + 3 * pg + cur) % (4 * pg) < 4 * pg := Nat.mod_lt _ (by omega)
    have hc2 : ((Q - 1) * pg + cur) % (8 * pg) < 8 * pg := Nat.mod_lt _ (by omega)
    first | exact hv0 | omega)

/-- Commit side metadata and clear job state at the end of `PageJob.demoteBuild`. -/
def pageTickDemoteBuildEndProg :
    (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | ((mb, pg), ((sb, qs), (rs, ths))) => do
    let qm1 ← pure (qs - 1)
    let rp ← pure (rs + pg)
    let th3 ← pure ((ths + 3 * pg) % (4 * pg))
    let z0 ← pure 0
    pageWriteSideMetaProg ((mb, sb), (qm1, (rp, th3)))
    pageWriteJobProg (mb, (z0, (z0, z0)))

@[simp] theorem runClient_frontier_pageTickDemoteBuildEndProg
    (x : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s
      (pageTickDemoteBuildEndProg x))).frontier = s.frontier := by
  rcases x with ⟨⟨_, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  simp [pageTickDemoteBuildEndProg]

theorem realizesBounded_pageTickDemoteBuildEnd :
    RealizesBounded .exact pageTickDemoteBuildEndProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((mb, pg), ((_, qs), (rs, ths))) s =>
        32 ≤ pg ∧ 16 * pg < 2 ^ w ∧ mb + 32 ≤ s.frontier ∧ 0 < qs ∧ rs < 3 * pg ∧ ths < 4 * pg)
      (fun _ _ => 0) := by
  have hwsm := realizesBounded_pageWriteSideMeta
  have hwj := realizesBounded_pageWriteJob
  realize
  all_goals (
    rcases d with ⟨⟨mb, pg⟩, ⟨⟨sb, qs⟩, ⟨rs, ths⟩⟩⟩
    obtain ⟨hpg0, hpg16, hfr, hqs0, hrs, hths⟩ := h
    have hsb_w : Fits w sb := hwords 2
    have hqs_w : Fits w qs := hwords 3
    try simp only [runClient_frontier_pageWriteSideMetaProg] at *
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hm4 : (ths + 3 * pg) % (4 * pg) < 4 * pg := Nat.mod_lt _ (by omega)
    omega)

/-- Validate page counts and tail bounds before stepping `PageJob.demoteBuild`. -/
def pageTickDemoteBuildCheckProg :
    (PageArenaCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ)) → Memory.Prog Unit
  | (((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (sb, cur)),
      (fp, (tc, ths)))) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let Q ← pure (fp.1 + fp.2)
    let qs ← pure (if sb = 0 then fp.1 else fp.2)
    let rs ← pure (if sb = 0 then tc.1 else tc.2)
    if 0 < qs ∧ 0 < Q ∧ rs < 3 * pg ∧ ths < 4 * pg then
      if cur < pg then
        pageTickDemoteBuildStepProg (ctx, ((sb, cur), (ths, Q)))
      else
        pageTickDemoteBuildEndProg ((mb, pg), ((sb, qs), (rs, ths)))
    else
      pure ()

@[simp] theorem runClient_frontier_pageTickDemoteBuildCheckProg
    (x : (PageArenaCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s
      (pageTickDemoteBuildCheckProg x))).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩,
    ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩⟩
  unfold pageTickDemoteBuildCheckProg; dsimp only
  simp only [pure_bind]
  split_ifs <;> simp

theorem realizesBounded_pageTickDemoteBuildCheck :
    RealizesBounded .exact pageTickDemoteBuildCheckProg
      (WordEncoding.encode (α := (PageArenaCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), (fp, _)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        (fp.1 + fp.2) * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hstep := realizesBounded_pageTickDemoteBuildStep
  have hend := realizesBounded_pageTickDemoteBuildEnd
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨sb, cur⟩⟩, ⟨⟨fp1, fp2⟩, ⟨⟨tc1, tc2⟩, ths⟩⟩⟩
    obtain ⟨hv0, hfp_nc⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hsum_le : fp1 + fp2 ≤ nc := by
      have := Nat.le_mul_of_pos_right (fp1 + fp2) (by omega : 0 < pg)
      omega
    (try split_ifs at *) <;> try (first | exact hv0 | omega))
  all_goals (
    have hsb_w : Fits w sb := hwords 11
    have hcur_w : Fits w cur := hwords 12
    dsimp only [Fits] at *
    have hqm1_le : (fp1 + fp2 - 1) * pg + pg ≤ (fp1 + fp2) * pg := by
      rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right pg (by omega)
    omega)

/-- Dispatch one tick of `PageJob.demoteBuild` (`¬ReadsWidth`). -/
def pageTickDemoteBuildProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (js, cur)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let fp ← pageReadFullPagesProg mb
    let tc ← pageReadTailCountsProg mb
    let sb ← pure (if js = 0 then 0 else 1)
    let ths ← Memory.read (mb + if sb = 0 then 25 else 26)
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then
        pageTickDemoteBuildCheckProg ((ctx, (sb, cur)), (fp, (tc, ths)))
      else
        pure ()
    else
      pure ()

@[simp] theorem runClient_frontier_pageTickDemoteBuildProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageTickDemoteBuildProg x))).frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageTickDemoteBuildProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg,
    prog_runClient_state_read]
  split_ifs <;> simp

theorem realizesBounded_pageTickDemoteBuild :
    RealizesBounded .exact pageTickDemoteBuildProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have hrtc := realizesBounded_pageReadTailCounts
  have hchk := realizesBounded_pageTickDemoteBuildCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨js, cur⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadTailCountsProg] at *
    try simp only [runClient_state_pageReadFullPagesProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> try (first | exact hv0 | omega))
  all_goals (
    set fp_v := (Memory.spec 0).clientResult s (pageReadFullPagesProg mb)
    have hq0_mul : fp_v.1 * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    try (
      have hq1_mul : fp_v.2 * pg ≤ ((nc - fp_v.1 * pg) / pg) * pg :=
        Nat.mul_le_mul_right pg (by omega)
      have hdiv1 : ((nc - fp_v.1 * pg) / pg) * pg ≤ nc - fp_v.1 * pg :=
        Nat.div_mul_le_self _ pg
      have hsum_mul : (fp_v.1 + fp_v.2) * pg = fp_v.1 * pg + fp_v.2 * pg := Nat.add_mul ..
      have hsum_le : fp_v.1 + fp_v.2 ≤ nc := by
        have := Nat.le_mul_of_pos_right (fp_v.1 + fp_v.2) (by omega : 0 < pg)
        omega)
    omega)

/-- Single `O(1)` background rebalance tick (`st.tick`, `1 ≤ memoryCost`, `¬ReadsWidth`). -/
def pageTickBoundedProg : PageArenaCtx → Memory.Prog Unit
  | ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let jk ← Memory.read (mb + 27)
    let ja ← pageReadJobArgsProg mb
    let _ ←
      if jk = 1 then pageTickPromoteProg (ctx, (ja.1, ja.2))
      else if jk = 2 then pageTickDemoteSwapProg (ctx, (ja.1, ja.2))
      else if jk = 3 then pageTickDemoteBuildProg (ctx, (ja.1, ja.2))
      else pure ()
    pageMaybeStartJobProg ctx

theorem memoryCost_pageTickBoundedProg_pos (ctx : PageArenaCtx) (s : Memory.State) :
    1 ≤ memoryCost (pageTickBoundedProg ctx) s := by
  rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageTickBoundedProg; dsimp only
  simp only [Realization.memoryCost_bind', prog_memoryCost_read]
  omega

@[simp] theorem runClient_frontier_pageTickBoundedProg
    (ctx : PageArenaCtx) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageTickBoundedProg ctx))).frontier =
      s.frontier := by
  rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageTickBoundedProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read, runClient_state_pageReadJobArgsProg]
  split_ifs <;> simp

theorem realizesBounded_pageTick :
    RealizesBounded .exact pageTickBoundedProg
      (WordEncoding.encode (α := PageArenaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ctx s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrja := realizesBounded_pageReadJobArgs
  have hp := realizesBounded_pageTickPromote
  have hds := realizesBounded_pageTickDemoteSwap
  have hdb := realizesBounded_pageTickDemoteBuild
  have hms := realizesBounded_pageMaybeStartJob
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_frontier_pageTickPromoteProg] at *
    try simp only [runClient_frontier_pageTickDemoteSwapProg] at *
    try simp only [runClient_frontier_pageTickDemoteBuildProg] at *
    try simp only [runClient_state_pageReadJobArgsProg] at *
    first | exact hv0 | omega)

/-- Single iteration body for `pageRunTicksIterProg` (`1 ≤ memoryCost`, `¬ReadsWidth`). -/
def pageTickIterStepProg : PageArenaCtx × ℕ → Memory.Prog ℕ
  | (ctx, acc) => do
    pageTickBoundedProg ctx
    pure acc

theorem memoryCost_pageTickIterStepProg_pos
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (pageTickIterStepProg x) s := by
  rcases x with ⟨ctx, acc⟩
  unfold pageTickIterStepProg; dsimp only
  rw [Realization.memoryCost_bind']
  have := memoryCost_pageTickBoundedProg_pos ctx s
  omega

theorem realizesBounded_pageTickIterStep :
    RealizesBounded .exact pageTickIterStepProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have ht := realizesBounded_pageTick
  realize
  exact h

/-- Run `fuel` background ticks via `iterate pageTickIterStepProg` (`¬ReadsWidth`). -/
def pageRunTicksIterProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, z), fuel) => iterate pageTickIterStepProg ctx fuel z

theorem realizesBounded_pageRunTicksIter :
    RealizesBounded .exact pageRunTicksIterProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, z), fuel) s =>
        iterationSafe pageTickIterStepProg
          (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
          w ctx fuel z s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := PageArenaCtx))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_pageTickIterStep
    memoryCost_pageTickIterStepProg_pos

/-- Batched `fuel`-tick background rebalancer (`PagePairState.runTicks fuel`, `¬ReadsWidth`). -/
def pageRunTicksBatchProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (ctx, fuel) => do
    let _ ← pageRunTicksIterProg ((ctx, 0), fuel)
    pure ()

theorem pageRunTicksIter_safe (ctx : PageArenaCtx) (w : ℕ) :
    ∀ (fuel z : ℕ) (s : Memory.State),
      (PageArenaLayout.ofCtx ctx).Valid w s.frontier →
      iterationSafe pageTickIterStepProg
        (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
        w ctx fuel z s ∧
      ((Memory.spec 0).clientState s (iterate pageTickIterStepProg ctx fuel z)).frontier =
        s.frontier := by
  intro fuel
  induction fuel with
  | zero => intro _ s _; exact ⟨trivial, rfl⟩
  | succ k ih =>
    intro z s hv
    have hfr1 : ((Memory.spec 0).clientState s (pageTickIterStepProg (ctx, z))).frontier =
        s.frontier := by
      unfold pageTickIterStepProg StateTransitionSpec.clientState; dsimp only
      simp [runClient_frontier_pageTickBoundedProg]
    obtain ⟨hsafe, hfr_k⟩ := ih ((Memory.spec 0).clientResult s (pageTickIterStepProg (ctx, z)))
      ((Memory.spec 0).clientState s (pageTickIterStepProg (ctx, z))) (hfr1.symm ▸ hv)
    refine ⟨?_, ?_⟩
    · unfold iterationSafe
      rw [clientResult_width, clientState_width]
      exact ⟨hv, hsafe⟩
    · unfold iterate
      rw [StateTransitionSpec.clientState_bind, hfr_k, hfr1]

@[simp] theorem runClient_frontier_pageRunTicksBatchProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (pageRunTicksBatchProg x))).frontier =
      s.frontier := by
  rcases x with ⟨ctx, fuel⟩
  unfold pageRunTicksBatchProg pageRunTicksIterProg; dsimp only
  simp only [prog_runClient_state_bind, prog_runClient_state_pure]
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih =>
    unfold iterate
    rw [StateTransitionSpec.clientState_bind]
    have hfr1 : ((Memory.spec 0).clientState s (pageTickIterStepProg (ctx, 0))).frontier =
        s.frontier := by
      unfold pageTickIterStepProg StateTransitionSpec.clientState; dsimp only
      simp [runClient_frontier_pageTickBoundedProg]
    have hres0 : (Memory.spec 0).clientResult s (pageTickIterStepProg (ctx, 0)) = 0 := by
      unfold pageTickIterStepProg; simp
    rw [hres0]
    exact (ih _).trans hfr1

theorem realizesBounded_pageRunTicksBatch :
    RealizesBounded .exact pageRunTicksBatchProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hit := realizesBounded_pageRunTicksIter
  realize
  rcases d with ⟨ctx, fuel⟩
  exact (pageRunTicksIter_safe ctx w fuel 0 s h).1

theorem pageTickOne_refine {L : PageArenaLayout} {s : Memory.State} {slack : ℕ}
    (hvL : L.Valid L.w s.frontier)
    (hd : PagePairState.DriftInv (extractPagePair L s.mem) slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap) :
    let u := extractPageUnperm L s.mem
    let jk := s.mem (L.metaBase + 27)
    let js := s.mem (L.metaBase + 28)
    let cur := s.mem (L.metaBase + 29)
    let body : Memory.Prog Unit :=
      if jk = 1 then pageTickPromoteProg (L.toCtx, (js, cur))
      else if jk = 2 then pageTickDemoteSwapProg (L.toCtx, (js, cur))
      else if jk = 3 then pageTickDemoteBuildProg (L.toCtx, (js, cur))
      else pure ()
    let s₁ := (Memory.spec 0).clientState s body
    s₁.frontier = s.frontier ∧
    extractPageUnperm L s₁.mem = { u with st := u.st.tickOne.1 } ∧
    arenaPairAt L s₁.mem = applySwaps u.st.tickOne.2 (arenaPairAt L s.mem) := by
  dsimp only
  have ⟨hw, _, hpb, _, _, hpg32, hpg16, hmp4, hmp4_pb, hnc_mp, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  have hd_st : st.DriftInv slack := hd
  have hv := hd_st.valid
  have hjv := hd_st.jobValid
  have hps_st : st.pageSize = L.pgB := hps
  have hti_st : st.totalItems ≤ L.nCap := hti
  have hB : 0 < L.pgB := by omega
  have hptr1 : 1 < 2 ^ L.ptrB := by omega
  have htp2 : st.totalPages + 2 ≤ L.maxPages := by
    have hle : st.totalPages * L.pgB ≤ (L.maxPages - 2) * L.pgB := by
      have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq; omega
    have htp_le : st.totalPages ≤ L.maxPages - 2 := (Nat.mul_le_mul_right_iff hB).mp hle
    omega
  have hqb_le : (st.fullPages false + st.fullPages true) * L.pgB ≤ L.nCap := by
    have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq
    change st.totalPages * L.pgB ≤ L.nCap; omega
  have hq0_le : st.fullPages false ≤ L.nCap / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hq1_le : st.fullPages true ≤ (L.nCap - st.fullPages false * L.pgB) / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hc_q01 : st.fullPages false ≤ L.nCap / L.pgB ∧
      st.fullPages true ≤ (L.nCap - st.fullPages false * L.pgB) / L.pgB := ⟨hq0_le, hq1_le⟩
  set jk := s.mem (L.metaBase + 27)
  set js := s.mem (L.metaBase + 28)
  set cur := s.mem (L.metaBase + 29)
  set sj := decide (js ≠ 0)
  have hj_dec : st.job = decodePageJob jk js cur := rfl
  have hsb_eq : (if js = 0 then 0 else 1) = (if sj then 1 else 0) := by
    dsimp only [sj]; by_cases hz : js = 0 <;> simp [hz]
  have hfp_eq : (Memory.spec 0).clientResult s (pageReadFullPagesProg L.metaBase) =
      (st.fullPages false, st.fullPages true) := pageReadFullPagesProg_eq L s
  have htc_eq : (Memory.spec 0).clientResult s (pageReadTailCountsProg L.metaBase) =
      (st.tailCount false, st.tailCount true) := pageReadTailCountsProg_eq L s
  by_cases hjk1 : jk = 1
  · rw [ite_eq_left hjk1]
    have hj_pr : st.job = .promote sj cur := by rw [hj_dec]; simp [decodePageJob, hjk1, sj]
    unfold PagePairState.JobValid at hjv; rw [hj_pr] at hjv
    obtain ⟨hcur_le, hB_lt_r, _⟩ := hjv
    rw [hps_st] at hcur_le hB_lt_r
    refine ⟨by simpa only [StateTransitionSpec.clientState] using
      runClient_frontier_pageTickPromoteProg (L.toCtx, (js, cur)) s, ?_⟩
    unfold pageTickPromoteProg pageTickPromoteStepProg pageTickPromoteEndProg
      PagePairState.tickOne
    rw [hust, hj_pr]
    dsimp only [PageArenaLayout.toCtx]
    unfold StateTransitionSpec.clientState
    simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
      runClient_state_pageReadFullPagesProg, hfp_eq, hsb_eq]
    rw [ite_eq_left hq0_le, ite_eq_left hq1_le]
    rw [hps_st]
    by_cases hcur : cur < L.pgB
    · rw [ite_eq_left hcur, ite_eq_left hcur]
      have hp₁_eq : (Memory.spec 0).clientResult s
          (pageTailPhysBoundedProg (L.toCtx, (if sj then 1 else 0, cur))) =
          st.tailPhys sj cur :=
        pageTailPhysBoundedProg_eq hv hps hti sj (hcur.trans hB_lt_r)
      dsimp only [PageArenaLayout.toCtx] at hp₁_eq
      have hp₂_hi : st.totalPages * L.pgB + cur < st.totalItems := by
        have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq
        rcases Bool.eq_false_or_eq_true sj with hsj | hsj <;> (rw [hsj] at hB_lt_r; omega)
      have hp₂_lt : cur < L.nCap - (st.fullPages false + st.fullPages true) * L.pgB := by
        have hlt := hp₂_hi.trans_le hti
        unfold PagePairState.totalPages at hlt
        omega
      have hp₁_lo : st.totalPages * L.pgB ≤ st.tailPhys sj cur := hps_st ▸ le_physOfRes _ _ _
      have hp₁_hi : st.tailPhys sj cur < st.totalItems := hv.tail_lt sj cur (hcur.trans hB_lt_r)
      have hp₂_lo : st.totalPages * L.pgB ≤ st.totalPages * L.pgB + cur := Nat.le_add_right _ _
      simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_pageTailPhysBoundedProg, hp₁_eq, ite_eq_left hp₂_lt]
      obtain ⟨_, hu_sw, ha_sw⟩ := pageSwapTailSlotsProg_spec hvL hv hps hti
        hp₁_lo hp₁_hi hp₂_lo hp₂_hi
      set s_sw := (Memory.spec 0).clientState s
        (pageSwapTailSlotsProg (L.toCtx, (st.tailPhys sj cur, st.totalPages * L.pgB + cur)))
      have hs_sw_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s
          (pageSwapTailSlotsProg
            (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
              (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)),
            (st.tailPhys sj cur, (st.fullPages false + st.fullPages true) * L.pgB + cur))))) =
          s_sw := rfl
      rw [hs_sw_eq]
      obtain ⟨hu_j, ha_j⟩ := extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib s_sw
        (.promote sj (cur + 1))
      dsimp only [encodePageJob, encodePageJobKind, encodePageJobSide, encodePageJobCur,
        StateTransitionSpec.clientState] at hu_j ha_j
      rw [hu_j, hu_sw, ha_j, ha_sw]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hcur, ite_eq_right hcur]
      have hqs_eq : (if (if sj then 1 else 0) = 0 then st.fullPages false
          else st.fullPages true) = st.fullPages sj := by cases sj <;> rfl
      have hrs_eq : (if (if sj then 1 else 0) = 0 then st.tailCount false
          else st.tailCount true) = st.tailCount sj := by cases sj <;> rfl
      have hth_r : s.mem (L.metaBase + if (if sj then 1 else 0) = 0 then 25 else 26) =
          st.tailHead sj := by cases sj <;> rfl
      have hqs_mp : st.fullPages sj < L.maxPages := by
        unfold PagePairState.totalPages at htp2
        rcases Bool.eq_false_or_eq_true sj with hsj | hsj <;> (rw [hsj]; omega)
      have hQ_mp : st.fullPages false + st.fullPages true < L.maxPages := by
        unfold PagePairState.totalPages at htp2; omega
      have hth_lt : st.tailHead sj < 4 * L.pgB := hps_st ▸ hv.tailHead_lt sj
      have hc_pr_end : st.fullPages sj < L.maxPages ∧
          st.fullPages false + st.fullPages true < L.maxPages ∧
          L.pgB ≤ st.tailCount sj ∧ st.tailHead sj < 4 * L.pgB :=
        ⟨hqs_mp, hQ_mp, hB_lt_r.le, hth_lt⟩
      simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        runClient_state_pageReadTailCountsProg, htc_eq,
        prog_clientResult_read, prog_runClient_state_read, hqs_eq, hrs_eq, hth_r,
        ite_eq_left hc_pr_end]
      obtain ⟨hu_sm, ha_sm⟩ := extractPageUnperm_pageWriteSideMetaProg hw ho1 ho2 hm_ib s sj
        (st.fullPages sj + 1) (st.tailCount sj - L.pgB) ((st.tailHead sj + L.pgB) % (4 * L.pgB))
      set s_sm := (Memory.spec 0).clientState s
        (pageWriteSideMetaProg ((L.metaBase, if sj then 1 else 0),
          (st.fullPages sj + 1,
            (st.tailCount sj - L.pgB, (st.tailHead sj + L.pgB) % (4 * L.pgB)))))
      have hs_sm_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s
          (pageWriteSideMetaProg ((L.metaBase, if sj then 1 else 0),
            (st.fullPages sj + 1,
              (st.tailCount sj - L.pgB, (st.tailHead sj + L.pgB) % (4 * L.pgB))))))) = s_sm := rfl
      rw [hs_sm_eq]
      unfold pageCommitPromoteDirProg pageWritePageOfProg pageWriteOwnerProg
      dsimp only
      have hsb_01 : (if (if sj then 1 else 0) = 0 then 0 else 1) = (if sj then 1 else 0) := by
        cases sj <;> rfl
      simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
        ite_eq_left hqs_mp, ite_eq_left hQ_mp, runClient_state_writePackedCompGenProg, hsb_01]
      obtain ⟨hu_j, ha_j⟩ := extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib
        (Memory.State.mk _ s_sm.frontier) .idle
      dsimp only [encodePageJob, encodePageJobKind, encodePageJobSide, encodePageJobCur,
        StateTransitionSpec.clientState] at hu_j ha_j
      rw [hu_j, ha_j]
      obtain ⟨hu_ov, ha_ov⟩ := extractPageUnperm_writeOwnerVp hw ho1 ho2 hm_ib _
        hQ_mp (hqs_mp.trans (by omega))
      obtain ⟨hu_os, ha_os⟩ := extractPageUnperm_writeOwnerSide hw hptr1 ho1 ho2 hm_ib _ hQ_mp sj
      obtain ⟨hu_po, ha_po⟩ := extractPageUnperm_writePageOf hw ho1 ho2 hm_ib s_sm.mem sj
        hqs_mp (hQ_mp.trans (by omega))
      rw [hu_ov, hu_os, hu_po, hu_sm, ha_ov, ha_os, ha_po, ha_sm]
      refine ⟨?_, rfl⟩
      dsimp only [u, st, extractPageUnperm] at hps_st ⊢; rw [hps_st]; rfl
  · rw [ite_eq_right hjk1]
    by_cases hjk2 : jk = 2
    · rw [ite_eq_left hjk2]
      have hj_ds : st.job = .demoteSwap sj cur := by
        rw [hj_dec]; simp [decodePageJob, hjk2, sj]
      unfold PagePairState.JobValid at hjv; rw [hj_ds] at hjv
      obtain ⟨hcur_le, hqs_pos, hPd_lt⟩ := hjv
      rw [hps_st] at hcur_le
      have hQ_pos : 0 < st.fullPages false + st.fullPages true := by
        rcases Bool.eq_false_or_eq_true sj with hsj | hsj <;> (rw [hsj] at hqs_pos; omega)
      have hQ_mp : st.fullPages false + st.fullPages true ≤ L.maxPages := by
        change st.totalPages ≤ L.maxPages; omega
      have hqm1_mp : st.fullPages sj - 1 < L.maxPages := by
        unfold PagePairState.totalPages at htp2
        rcases Bool.eq_false_or_eq_true sj with hsj | hsj <;> (rw [hsj]; omega)
      have hPd_Q : st.pageOf sj (st.fullPages sj - 1) < st.fullPages false + st.fullPages true := by
        change _ < st.totalPages; omega
      have hc_ds : 0 < st.fullPages sj ∧ 0 < st.fullPages false + st.fullPages true ∧
          st.fullPages false + st.fullPages true ≤ L.maxPages := ⟨hqs_pos, hQ_pos, hQ_mp⟩
      refine ⟨by simpa only [StateTransitionSpec.clientState] using
        runClient_frontier_pageTickDemoteSwapProg (L.toCtx, (js, cur)) s, ?_⟩
      unfold pageTickDemoteSwapProg pageTickDemoteSwapCheckProg
        pageTickDemoteSwapBodyProg PagePairState.tickOne
      rw [hust, hj_ds]
      dsimp only [PageArenaLayout.toCtx]
      unfold StateTransitionSpec.clientState
      have hqs_eq : (if (if sj then 1 else 0) = 0 then st.fullPages false
          else st.fullPages true) = st.fullPages sj := by cases sj <;> rfl
      have hpOF : (Memory.spec 0).clientResult s
          (pageReadPageOfProg (L.toCtx, (if sj then 1 else 0, st.fullPages sj - 1))) =
          st.pageOf sj (st.fullPages sj - 1) := pageReadPageOfProg_eq sj hqm1_mp s
      dsimp only [PageArenaLayout.toCtx] at hpOF
      simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
        runClient_state_pageReadFullPagesProg, hfp_eq, hsb_eq]
      rw [ite_eq_left hq0_le, ite_eq_left hq1_le]
      simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        hqs_eq, ite_eq_left hc_ds, runClient_state_pageReadPageOfProg, hpOF,
        ite_eq_left hPd_Q]
      rw [hps_st]
      by_cases hcur : cur < L.pgB
      · rw [ite_eq_left hcur, ite_eq_left hcur]
        set p₁ := st.pageOf sj (st.fullPages sj - 1) * L.pgB + cur
        set p₂ := (st.fullPages false + st.fullPages true - 1) * L.pgB + cur
        have hp_nc : p₁ < L.nCap ∧ p₂ < L.nCap := by
          have h1 : (st.pageOf sj (st.fullPages sj - 1) + 1) * L.pgB ≤ st.totalPages * L.pgB :=
            Nat.mul_le_mul_right L.pgB hPd_Q
          have h2 : (st.totalPages - 1 + 1) * L.pgB ≤ st.totalPages * L.pgB :=
            Nat.mul_le_mul_right L.pgB (by omega)
          rw [Nat.add_one_mul] at h1 h2
          have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq
          unfold PagePairState.totalPages at h1 h2 hti_eq
          exact ⟨by dsimp only [p₁]; omega, by dsimp only [p₂]; omega⟩
        unfold pageSwapPhysProg
        dsimp only
        rw [ite_eq_left hp_nc]
        simp only [StateTransitionSpec.clientState, prog_runClient_state_bind]
        obtain ⟨hu_sw, ha_sw⟩ := swapPairGenProg_arena_eq hw hm_ib ho1 ho2 s p₁ p₂
        dsimp only [StateTransitionSpec.clientState] at hu_sw ha_sw
        obtain ⟨hu_j, ha_j⟩ := extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib
          (((Memory.spec 0).runClient s
            (swapPairGenProg (((L.itemBase, (L.qBits, L.vBits)), L.w), (p₁, p₂)))).2.1)
          (.demoteSwap sj (cur + 1))
        dsimp only [encodePageJob, encodePageJobKind, encodePageJobSide, encodePageJobCur,
          StateTransitionSpec.clientState] at hu_j ha_j
        rw [hu_j, hu_sw, ha_j, ha_sw, applySwaps_cons, applySwaps_nil]
        refine ⟨?_, rfl⟩
        dsimp only [u, st, extractPageUnperm] at hps_st ⊢; rw [hps_st]
      · rw [ite_eq_right hcur, ite_eq_right hcur]
        set pLast := st.fullPages false + st.fullPages true - 1
        set pDem := st.pageOf sj (st.fullPages sj - 1)
        have hpL_mp : pLast < L.maxPages := by
          dsimp only [pLast]; unfold PagePairState.totalPages at htp2; omega
        have hpD_mp : pDem < L.maxPages := by
          dsimp only [pDem]; unfold PagePairState.totalPages at htp2; omega
        have hpL_tp : pLast < st.totalPages := by
          dsimp only [pLast]; unfold PagePairState.totalPages; omega
        obtain ⟨hvpL_lt, _⟩ := hv.pageOf_owner pLast hpL_tp
        have hvpL_mp : st.ownerVp pLast < L.maxPages := by
          unfold PagePairState.totalPages at htp2
          rcases Bool.eq_false_or_eq_true (st.ownerSide pLast) with hsL | hsL <;>
            (rw [hsL] at hvpL_lt; omega)
        have howL : (Memory.spec 0).clientResult s (pageReadOwnerProg (L.toCtx, pLast)) =
            (if st.ownerSide pLast then 1 else 0, st.ownerVp pLast) := by
          unfold pageReadOwnerProg
          dsimp only [PageArenaLayout.toCtx]
          rw [ite_eq_left hpL_mp]
          simp only [StateTransitionSpec.clientState, pure_bind, prog_clientResult_bind,
            clientResult_readPackedCompGenProg, runClient_state_readPackedCompGenProg,
            prog_clientResult_pure]
          dsimp only [st, extractPagePair]
          simp only [hpL_mp, ↓reduceIte]
          congr 1
          by_cases hz : readPacked (L.metaBase + L.offDir) L.ptrB L.w s.mem (4 * pLast + 2) = 0 <;>
            simp [hz]
        dsimp only [PageArenaLayout.toCtx] at howL
        simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
          runClient_state_pageReadOwnerProg, howL]
        unfold pageSwapDemoteDirProg pageWritePageOfProg pageWriteOwnerProg
        dsimp only
        have hsb_01 : ∀ b : Bool, (if (if b then 1 else 0) = 0 then 0 else 1) =
            (if b then 1 else 0) := fun b => by cases b <;> rfl
        rw [ite_eq_left hvpL_mp, ite_eq_left hqm1_mp, ite_eq_left hpD_mp, ite_eq_left hpL_mp]
        simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
          runClient_state_writePackedCompGenProg, hsb_01]
        obtain ⟨hu_j, ha_j⟩ := extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib
          (Memory.State.mk _ s.frontier) (.demoteBuild sj 0)
        dsimp only [encodePageJob, encodePageJobKind, encodePageJobSide, encodePageJobCur,
          StateTransitionSpec.clientState] at hu_j ha_j
        rw [hu_j, ha_j]
        obtain ⟨hu4, ha4⟩ := extractPageUnperm_writeOwnerVp hw ho1 ho2 hm_ib _
          hpL_mp (hqm1_mp.trans (by omega))
        obtain ⟨hu3, ha3⟩ := extractPageUnperm_writeOwnerSide hw hptr1 ho1 ho2 hm_ib _ hpL_mp sj
        obtain ⟨hu2, ha2⟩ := extractPageUnperm_writeOwnerVp hw ho1 ho2 hm_ib _
          hpD_mp (hvpL_mp.trans (by omega))
        obtain ⟨hu1, ha1⟩ := extractPageUnperm_writeOwnerSide hw hptr1 ho1 ho2 hm_ib _
          hpD_mp (st.ownerSide pLast)
        obtain ⟨hup2, hap2⟩ := extractPageUnperm_writePageOf hw ho1 ho2 hm_ib _ sj
          hqm1_mp (hpL_mp.trans (by omega))
        obtain ⟨hup1, hap1⟩ := extractPageUnperm_writePageOf hw ho1 ho2 hm_ib s.mem
          (st.ownerSide pLast) hvpL_mp (hpD_mp.trans (by omega))
        rw [hu4, hu3, hu2, hu1, hup2, hup1, ha4, ha3, ha2, ha1, hap2, hap1]
        refine ⟨?_, rfl⟩
        dsimp only [u, st, extractPageUnperm] at hps_st ⊢; rw [hps_st]; rfl
    · rw [ite_eq_right hjk2]
      by_cases hjk3 : jk = 3
      · rw [ite_eq_left hjk3]
        have hj_db : st.job = .demoteBuild sj cur := by
          rw [hj_dec]; simp [decodePageJob, hjk3, sj]
        unfold PagePairState.JobValid at hjv; rw [hj_db] at hjv
        obtain ⟨hcur_le, hqs_pos, _, htc_3B, _, _⟩ := hjv
        rw [hps_st] at hcur_le htc_3B
        have hQ_pos : 0 < st.fullPages false + st.fullPages true := by
          rcases Bool.eq_false_or_eq_true sj with hsj | hsj <;> (rw [hsj] at hqs_pos; omega)
        have hth_lt : st.tailHead sj < 4 * L.pgB := hps_st ▸ hv.tailHead_lt sj
        have hc_db : 0 < st.fullPages sj ∧ 0 < st.fullPages false + st.fullPages true ∧
            st.tailCount sj < 3 * L.pgB ∧ st.tailHead sj < 4 * L.pgB :=
          ⟨hqs_pos, hQ_pos, htc_3B, hth_lt⟩
        refine ⟨by simpa only [StateTransitionSpec.clientState] using
          runClient_frontier_pageTickDemoteBuildProg (L.toCtx, (js, cur)) s, ?_⟩
        unfold pageTickDemoteBuildProg pageTickDemoteBuildCheckProg
          pageTickDemoteBuildStepProg pageTickDemoteBuildEndProg PagePairState.tickOne
        rw [hust, hj_db]
        dsimp only [PageArenaLayout.toCtx]
        unfold StateTransitionSpec.clientState
        have hqs_eq : (if (if sj then 1 else 0) = 0 then st.fullPages false
            else st.fullPages true) = st.fullPages sj := by cases sj <;> rfl
        have hrs_eq : (if (if sj then 1 else 0) = 0 then st.tailCount false
            else st.tailCount true) = st.tailCount sj := by cases sj <;> rfl
        have hth_r : s.mem (L.metaBase + if (if sj then 1 else 0) = 0 then 25 else 26) =
            st.tailHead sj := by cases sj <;> rfl
        simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
          runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg,
          hfp_eq, htc_eq, prog_clientResult_read, prog_runClient_state_read,
          hsb_eq, hth_r]
        rw [ite_eq_left hq0_le, ite_eq_left hq1_le]
        simp only [hqs_eq, hrs_eq, ite_eq_left hc_db]
        rw [hps_st]
        by_cases hcur : cur < L.pgB
        · rw [ite_eq_left hcur, ite_eq_left hcur]
          set k_cur := (st.tailHead sj + 3 * L.pgB + cur) % (4 * L.pgB)
          set res_cur := ((st.fullPages false + st.fullPages true - 1) * L.pgB + cur) % (8 * L.pgB)
          have hk_lt : k_cur < 4 * L.pgB := Nat.mod_lt _ (by omega)
          have hr_lt : res_cur < 8 * L.pgB := Nat.mod_lt _ (by omega)
          have hc_db_to : res_cur < 8 * L.pgB ∧ k_cur < 8 * L.pgB := ⟨hr_lt, by omega⟩
          unfold pageWriteTailResProg pageWriteTailOwnerProg
          dsimp only
          have hsb_4 : (if (if sj then 1 else 0) = 0 then 0 else 4 * L.pgB) =
              (if sj then 4 * L.pgB else 0) := by cases sj <;> rfl
          have hsb_1 : (if (if sj then 1 else 0) = 0 then 0 else 1) = (if sj then 1 else 0) := by
            cases sj <;> rfl
          rw [ite_eq_left hk_lt, ite_eq_left hc_db_to]
          simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
            runClient_state_writePackedCompGenProg, hsb_4, hsb_1]
          obtain ⟨hu_j, ha_j⟩ := extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib
            (Memory.State.mk _ s.frontier) (.demoteBuild sj (cur + 1))
          dsimp only [encodePageJob, encodePageJobKind, encodePageJobSide, encodePageJobCur,
            StateTransitionSpec.clientState] at hu_j ha_j
          rw [hu_j, ha_j]
          obtain ⟨hu2, ha2⟩ := extractPageUnperm_writeTailOwner hw hpg16 ho1 ho2 hm_ib _
            hr_lt (by omega : k_cur < 8 * L.pgB) sj
          obtain ⟨hu1, ha1⟩ := extractPageUnperm_writeTailRes hw ho1 ho2 hm_ib s.mem sj
            hk_lt (hr_lt.trans (by omega))
          rw [hu2, hu1, ha2, ha1]
          refine ⟨?_, rfl⟩
          dsimp only [u, st, extractPageUnperm] at hps_st ⊢; rw [hps_st]; rfl
        · rw [ite_eq_right hcur, ite_eq_right hcur]
          obtain ⟨hu_sm, ha_sm⟩ := extractPageUnperm_pageWriteSideMetaProg hw ho1 ho2 hm_ib s sj
            (st.fullPages sj - 1) (st.tailCount sj + L.pgB)
            ((st.tailHead sj + 3 * L.pgB) % (4 * L.pgB))
          set s_sm := (Memory.spec 0).clientState s
            (pageWriteSideMetaProg ((L.metaBase, if sj then 1 else 0),
              (st.fullPages sj - 1,
                (st.tailCount sj + L.pgB, (st.tailHead sj + 3 * L.pgB) % (4 * L.pgB)))))
          simp only [StateTransitionSpec.clientState, prog_runClient_state_bind]
          have hs_sm_eq : (((Memory.spec 0).runClient s
              (pageWriteSideMetaProg ((L.metaBase, if sj then 1 else 0),
                (st.fullPages sj - 1,
                  (st.tailCount sj + L.pgB, (st.tailHead sj + 3 * L.pgB) % (4 * L.pgB)))))).2.1) =
              s_sm := rfl
          rw [hs_sm_eq]
          obtain ⟨hu_j, ha_j⟩ := extractPageUnperm_pageWriteJobProg hw ho1 ho2 hm_ib s_sm .idle
          dsimp only [encodePageJob, encodePageJobKind, encodePageJobSide, encodePageJobCur,
            StateTransitionSpec.clientState] at hu_j ha_j
          rw [hu_j, hu_sm, ha_j, ha_sm]
          refine ⟨?_, rfl⟩
          dsimp only [u, st, extractPageUnperm] at hps_st ⊢; rw [hps_st]
      · rw [ite_eq_right hjk3]
        have hj_id : st.job = .idle := by
          rw [hj_dec]; simp [decodePageJob, hjk1, hjk2, hjk3]
        unfold PagePairState.tickOne; rw [hust, hj_id]
        exact ⟨rfl, rfl, rfl⟩

theorem pageTickBoundedProg_spec {L : PageArenaLayout} {s : Memory.State} {slack : ℕ}
    (hvL : L.Valid L.w s.frontier)
    (hd : PagePairState.DriftInv (extractPagePair L s.mem) slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap) :
    let u := extractPageUnperm L s.mem
    let res := u.st.tick
    let s' := (Memory.spec 0).clientState s (pageTickBoundedProg L.toCtx)
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = { u with st := res.1 } ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  dsimp only
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  have hd_st : st.DriftInv slack := hd
  have hv := hd_st.valid
  have hjv := hd_st.jobValid
  have hps_st : st.pageSize = L.pgB := hps
  have hti_st : st.totalItems ≤ L.nCap := hti
  have ⟨_, _, _, _, _, _, _, hmp4, _, hnc_mp, _, _, _, _, _⟩ := hvL
  have hB : 0 < L.pgB := hps_st ▸ hv.pageSize_pos
  have htp2 : st.totalPages + 2 ≤ L.maxPages := by
    have hle : st.totalPages * L.pgB ≤ (L.maxPages - 2) * L.pgB := by
      have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq; omega
    have htp_le : st.totalPages ≤ L.maxPages - 2 := (Nat.mul_le_mul_right_iff hB).mp hle
    omega
  obtain ⟨hfr₁, hu₁, ha₁⟩ := pageTickOne_refine hvL hd hps hti
  set body : Memory.Prog Unit :=
    if s.mem (L.metaBase + 27) = 1 then
      pageTickPromoteProg (L.toCtx, (s.mem (L.metaBase + 28), s.mem (L.metaBase + 29)))
    else if s.mem (L.metaBase + 27) = 2 then
      pageTickDemoteSwapProg (L.toCtx, (s.mem (L.metaBase + 28), s.mem (L.metaBase + 29)))
    else if s.mem (L.metaBase + 27) = 3 then
      pageTickDemoteBuildProg (L.toCtx, (s.mem (L.metaBase + 28), s.mem (L.metaBase + 29)))
    else pure ()
  set s₁ := (Memory.spec 0).clientState s body
  have hst₁_eq : extractPagePair L s₁.mem = st.tickOne.1 := congrArg PageUnpermState.st hu₁
  have hps₁ : (extractPagePair L s₁.mem).pageSize = L.pgB := by
    rw [hst₁_eq]
    unfold PagePairState.tickOne
    cases st.job with
    | idle => exact hps_st
    | promote sc cur =>
      dsimp only; split_ifs with hc
      · obtain ⟨hps_sw, _, _, _⟩ := swapTailSlots_meta_eq st _ _
        exact hps_sw.trans hps_st
      · exact hps_st
    | demoteSwap _ _ | demoteBuild _ _ => dsimp only; split_ifs <;> exact hps_st
  have hmp₁ : (extractPagePair L s₁.mem).totalPages < L.maxPages := by
    rw [hst₁_eq]
    unfold PagePairState.tickOne
    cases st.job with
    | idle => change st.totalPages < L.maxPages; omega
    | promote sc cur =>
      dsimp only; split_ifs with hc
      · obtain ⟨_, hfp_sw, _, _⟩ := swapTailSlots_meta_eq st _ _
        unfold PagePairState.totalPages at htp2 ⊢; dsimp only; rw [hfp_sw]; omega
      · unfold PagePairState.totalPages at htp2 ⊢; dsimp only
        cases sc <;> simp [Function.update_self, Function.update_of_ne] <;> omega
    | demoteSwap _ _ => dsimp only; split_ifs <;> (change st.totalPages < L.maxPages; omega)
    | demoteBuild sc _ =>
      dsimp only; split_ifs
      · change st.totalPages < L.maxPages; omega
      · unfold PagePairState.totalPages at htp2 ⊢; dsimp only
        cases sc <;> simp [Function.update_self, Function.update_of_ne] <;> omega
  have htc₁ : ∀ side, (extractPagePair L s₁.mem).tailCount side < 4 * L.pgB := fun side => by
    rw [hst₁_eq]
    have h0 := hps_st ▸ hv.tailCount_lt side
    unfold PagePairState.tickOne
    cases hj : st.job with
    | idle => exact h0
    | promote sc cur =>
      dsimp only; split_ifs with hc
      · obtain ⟨_, _, htc_sw, _⟩ := swapTailSlots_meta_eq st _ _
        rw [htc_sw]; exact h0
      · dsimp only
        by_cases hss : side = sc
        · subst hss; rw [Function.update_self]; omega
        · rw [Function.update_of_ne hss]; exact h0
    | demoteSwap _ _ => dsimp only; split_ifs <;> exact h0
    | demoteBuild sc cur =>
      dsimp only; split_ifs with hc
      · exact h0
      · dsimp only
        unfold PagePairState.JobValid at hjv; rw [hj] at hjv
        by_cases hss : side = sc
        · subst hss; rw [Function.update_self]; rw [hps_st] at hjv ⊢; omega
        · rw [Function.update_of_ne hss]; exact h0
  obtain ⟨hfr₂, hu₂, ha₂⟩ := pageMaybeStartJobProg_spec (hfr₁.symm ▸ hvL) htc₁ hps₁ hmp₁
  have hs'_eq : (Memory.spec 0).clientState s (pageTickBoundedProg L.toCtx) =
      (Memory.spec 0).clientState s₁ (pageMaybeStartJobProg L.toCtx) := by
    have hja_eq := pageReadJobArgsProg_eq L s
    unfold pageTickBoundedProg
    simp only [PageArenaLayout.toCtx, StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_clientResult_read, prog_runClient_state_read,
      runClient_state_pageReadJobArgsProg, hja_eq]
    dsimp only [s₁, body, PageArenaLayout.toCtx]
    split_ifs <;> simp [StateTransitionSpec.clientState]
  rw [hs'_eq]
  refine ⟨hfr₂.trans hfr₁, ?_, ha₂.trans ha₁⟩
  have hst_s1 : (extractPageUnperm L s₁.mem).st = st.tickOne.1 := hst₁_eq
  rw [hu₂, hst_s1, hu₁]; rfl

theorem pageRunTicksBatchProg_spec (fuel : ℕ) {L : PageArenaLayout} {s : Memory.State} {slack : ℕ}
    (hvL : L.Valid L.w s.frontier)
    (hd : PagePairState.DriftInv (extractPagePair L s.mem) slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap) :
    let u := extractPageUnperm L s.mem
    let res := PagePairState.runTicks fuel u.st
    let s' := (Memory.spec 0).clientState s (pageRunTicksBatchProg (L.toCtx, fuel))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = { u with st := res.1 } ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  suffices hiter : ∀ k {s : Memory.State} {slack : ℕ},
      L.Valid L.w s.frontier →
      PagePairState.DriftInv (extractPagePair L s.mem) slack →
      (extractPagePair L s.mem).pageSize = L.pgB →
      (extractPagePair L s.mem).totalItems ≤ L.nCap →
      let u := extractPageUnperm L s.mem
      let res := PagePairState.runTicks k u.st
      let s' := (Memory.spec 0).clientState s (iterate pageTickIterStepProg L.toCtx k 0)
      s'.frontier = s.frontier ∧
      extractPageUnperm L s'.mem = { u with st := res.1 } ∧
      arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) by
    unfold pageRunTicksBatchProg pageRunTicksIterProg StateTransitionSpec.clientState
    dsimp only
    simp only [prog_runClient_state_bind, prog_runClient_state_pure]
    exact hiter fuel hvL hd hps hti
  intro k
  induction k with
  | zero =>
    intro s _ _ _ _ _
    exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    intro s slack hvL₀ hd₀ hps₀ hti₀
    obtain ⟨hfr₁, hu₁, ha₁⟩ := pageTickBoundedProg_spec hvL₀ hd₀ hps₀ hti₀
    obtain ⟨hd₁, hps_t, _, hti_t, _, _, _⟩ := PagePairState.tick_driftInv.{0} hd₀
    have hstep_st : (Memory.spec 0).clientState s (pageTickIterStepProg (L.toCtx, 0)) =
        (Memory.spec 0).clientState s (pageTickBoundedProg L.toCtx) := by
      unfold pageTickIterStepProg StateTransitionSpec.clientState; simp
    have hstep_res : (Memory.spec 0).clientResult s (pageTickIterStepProg (L.toCtx, 0)) = 0 := by
      unfold pageTickIterStepProg; simp
    set s₁ := (Memory.spec 0).clientState s (pageTickBoundedProg L.toCtx)
    have hst₁ : extractPagePair L s₁.mem = (extractPagePair L s.mem).tick.1 :=
      congrArg PageUnpermState.st hu₁
    obtain ⟨hfr₂, hu₂, ha₂⟩ := ih (hfr₁.symm ▸ hvL₀) (hst₁.symm ▸ hd₁)
      (hst₁.symm ▸ hps_t.trans hps₀) (hst₁.symm ▸ hti_t.trans_le hti₀)
    dsimp only [PagePairState.runTicks]
    unfold iterate
    rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
    have hst₁_u : (extractPageUnperm L s₁.mem).st = (extractPageUnperm L s.mem).st.tick.1 := hst₁
    refine ⟨hfr₂.trans hfr₁, ?_, ?_⟩
    · rw [hu₂, hu₁]
    · rw [ha₂, hst₁_u, ha₁, applySwaps_append]

/-! ## Section 3: `PageArenaLayout` Frame and `memoryCost` Bounds -/

/-- Combined address footprint `OwnsMetaAddr ∨ OwnsItemAddr` of `PageArenaLayout`. -/
@[expose] def PageArenaLayout.OwnsAddr (L : PageArenaLayout) (addr : ℕ) : Prop :=
  L.OwnsMetaAddr addr ∨ L.OwnsItemAddr addr

theorem pageWriteJob_frame (L : PageArenaLayout) (x : ℕ × (ℕ × ℕ)) :
    BoundedFrameProg L.OwnsAddr 3 (pageWriteJobProg (L.metaBase, x)) := by
  rcases x with ⟨jk, js, jc⟩
  unfold pageWriteJobProg; dsimp only
  exact BoundedFrameProg.bind_prog
    (BoundedFrameProg.write_prog (Or.inl (Or.inl ⟨by omega, by omega⟩)) jk) fun _ =>
    BoundedFrameProg.bind_prog
      (BoundedFrameProg.write_prog (Or.inl (Or.inl ⟨by omega, by omega⟩)) js) fun _ =>
      BoundedFrameProg.write_prog (Or.inl (Or.inl ⟨by omega, by omega⟩)) jc

theorem pageWriteClean_frame (L : PageArenaLayout) (x : ℕ × (ℕ × ℕ)) :
    BoundedFrameProg L.OwnsAddr 3 (pageWriteCleanProg (L.metaBase, x)) := by
  rcases x with ⟨ph, cvp, coff⟩
  unfold pageWriteCleanProg; dsimp only
  exact BoundedFrameProg.bind_prog
    (BoundedFrameProg.write_prog (Or.inl (Or.inl ⟨by omega, by omega⟩)) ph) fun _ =>
    BoundedFrameProg.bind_prog
      (BoundedFrameProg.write_prog (Or.inl (Or.inl ⟨by omega, by omega⟩)) cvp) fun _ =>
      BoundedFrameProg.write_prog (Or.inl (Or.inl ⟨by omega, by omega⟩)) coff

theorem pageWriteSideMeta_frame (L : PageArenaLayout) (sb : ℕ) (x : ℕ × (ℕ × ℕ)) :
    BoundedFrameProg L.OwnsAddr 3 (pageWriteSideMetaProg ((L.metaBase, sb), x)) := by
  rcases x with ⟨qv, rv, thv⟩
  unfold pageWriteSideMetaProg; dsimp only
  have h1 : L.OwnsAddr (L.metaBase + if sb = 0 then 21 else 22) :=
    Or.inl (Or.inl (by split_ifs <;> refine ⟨by omega, by omega⟩))
  have h2 : L.OwnsAddr (L.metaBase + if sb = 0 then 23 else 24) :=
    Or.inl (Or.inl (by split_ifs <;> refine ⟨by omega, by omega⟩))
  have h3 : L.OwnsAddr (L.metaBase + if sb = 0 then 25 else 26) :=
    Or.inl (Or.inl (by split_ifs <;> refine ⟨by omega, by omega⟩))
  exact BoundedFrameProg.bind_prog (BoundedFrameProg.write_prog h1 qv) fun _ =>
    BoundedFrameProg.bind_prog (BoundedFrameProg.write_prog h2 rv) fun _ =>
      BoundedFrameProg.write_prog h3 thv

theorem pageReadFullPages_frame (L : PageArenaLayout) :
    BoundedFrameProg L.OwnsAddr 2 (pageReadFullPagesProg L.metaBase) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadFullPagesProg L.metaBase s)
    (fun s => by simp)

theorem pageReadTailCounts_frame (L : PageArenaLayout) :
    BoundedFrameProg L.OwnsAddr 2 (pageReadTailCountsProg L.metaBase) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadTailCountsProg L.metaBase s)
    (fun s => by simp)

theorem pageReadCleanPos_frame (L : PageArenaLayout) :
    BoundedFrameProg L.OwnsAddr 2 (pageReadCleanPosProg L.metaBase) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadCleanPosProg L.metaBase s)
    (fun s => by simp)

theorem pageReadJobArgs_frame (L : PageArenaLayout) :
    BoundedFrameProg L.OwnsAddr 2 (pageReadJobArgsProg L.metaBase) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadJobArgsProg L.metaBase s)
    (fun s => by simp)

theorem pageReadPageOf_frame (L : PageArenaLayout) (sb vp : ℕ) :
    BoundedFrameProg L.OwnsAddr 2 (pageReadPageOfProg (L.toCtx, (sb, vp))) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadPageOfProg (L.toCtx, (sb, vp)) s)
    (fun s => memoryCost_pageReadPageOfProg_le _ s)

theorem pageWritePageOf_frame {L : PageArenaLayout} (hw : 0 < L.w) (sb vp val : ℕ) :
    BoundedFrameProg L.OwnsAddr 4 (pageWritePageOfProg ((L.toCtx, (sb, vp)), val)) := by
  unfold pageWritePageOfProg; dsimp only [PageArenaLayout.toCtx]
  refine BoundedFrameProg.ite_prog (vp < L.maxPages) (fun hvp => ?_)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  simp only [pure_bind]
  have hidx : 4 * vp + (if sb = 0 then 0 else 1) < 4 * L.maxPages := by split_ifs <;> omega
  exact BoundedFrameProg.writePackedComp_prog hw hidx
    (fun addr hlo hhi => Or.inl (Or.inr (Or.inl ⟨hlo, hhi⟩)))

theorem pageReadOwner_frame (L : PageArenaLayout) (P : ℕ) :
    BoundedFrameProg L.OwnsAddr 4 (pageReadOwnerProg (L.toCtx, P)) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadOwnerProg (L.toCtx, P) s)
    (fun s => memoryCost_pageReadOwnerProg_le _ s)

theorem pageWriteOwner_frame {L : PageArenaLayout} (hw : 0 < L.w) (P sb vp : ℕ) :
    BoundedFrameProg L.OwnsAddr 8 (pageWriteOwnerProg ((L.toCtx, P), (sb, vp))) := by
  unfold pageWriteOwnerProg; dsimp only [PageArenaLayout.toCtx]
  refine BoundedFrameProg.ite_prog (P < L.maxPages) (fun hP => ?_)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  simp only [pure_bind]
  exact BoundedFrameProg.bind_prog
    (BoundedFrameProg.writePackedComp_prog hw (by omega : 4 * P + 2 < 4 * L.maxPages)
      (fun addr hlo hhi => Or.inl (Or.inr (Or.inl ⟨hlo, hhi⟩)))) fun _ =>
    BoundedFrameProg.writePackedComp_prog hw (by omega : 4 * P + 3 < 4 * L.maxPages)
      (fun addr hlo hhi => Or.inl (Or.inr (Or.inl ⟨hlo, hhi⟩)))

theorem pageReadTailRes_frame (L : PageArenaLayout) (sb k : ℕ) :
    BoundedFrameProg L.OwnsAddr 2 (pageReadTailResProg (L.toCtx, (sb, k))) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadTailResProg (L.toCtx, (sb, k)) s)
    (fun s => memoryCost_pageReadTailResProg_le _ s)

theorem pageWriteTailRes_frame {L : PageArenaLayout} (hw : 0 < L.w) (sb k val : ℕ) :
    BoundedFrameProg L.OwnsAddr 4 (pageWriteTailResProg ((L.toCtx, (sb, k)), val)) := by
  unfold pageWriteTailResProg; dsimp only [PageArenaLayout.toCtx]
  refine BoundedFrameProg.ite_prog (k < 4 * L.pgB) (fun hk => ?_)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  simp only [pure_bind]
  have hidx : (if sb = 0 then 0 else 4 * L.pgB) + k < 16 * L.pgB := by split_ifs <;> omega
  exact BoundedFrameProg.writePackedComp_prog hw hidx
    (fun addr hlo hhi => Or.inl (Or.inr (Or.inr ⟨hlo, hhi⟩)))

theorem pageReadTailOwner_frame (L : PageArenaLayout) (res : ℕ) :
    BoundedFrameProg L.OwnsAddr 2 (pageReadTailOwnerProg (L.toCtx, res)) :=
  BoundedFrameProg.readOnly_of_state_eq _
    (fun s => by simpa only [StateTransitionSpec.clientState] using
      runClient_state_pageReadTailOwnerProg (L.toCtx, res) s)
    (fun s => memoryCost_pageReadTailOwnerProg_le _ s)

theorem pageWriteTailOwner_frame {L : PageArenaLayout} (hw : 0 < L.w) (res sb k : ℕ) :
    BoundedFrameProg L.OwnsAddr 4 (pageWriteTailOwnerProg ((L.toCtx, res), (sb, k))) := by
  unfold pageWriteTailOwnerProg; dsimp only [PageArenaLayout.toCtx]
  refine BoundedFrameProg.ite_prog (res < 8 * L.pgB ∧ k < 8 * L.pgB) (fun h => ?_)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  simp only [pure_bind]
  exact BoundedFrameProg.writePackedComp_prog hw (by omega : 8 * L.pgB + res < 16 * L.pgB)
    (fun addr hlo hhi => Or.inl (Or.inr (Or.inr ⟨hlo, hhi⟩)))

theorem pageSwapPhys_frame {L : PageArenaLayout} (hw : 0 < L.w) (p₁ p₂ : ℕ) :
    BoundedFrameProg L.OwnsAddr 24 (pageSwapPhysProg (L.toCtx, (p₁, p₂))) := by
  unfold pageSwapPhysProg; dsimp only [PageArenaLayout.toCtx]
  exact BoundedFrameProg.ite_prog (p₁ < L.nCap ∧ p₂ < L.nCap)
    (fun hp => BoundedFrameProg.swapPairGen_prog hw hp.1 hp.2
      (fun addr hlo hhi => Or.inr ⟨hlo, hhi⟩))
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))

theorem pageTailPhysInner_frame (L : PageArenaLayout) (sb k base tsum : ℕ) :
    BoundedFrameProg L.OwnsAddr 3 (pageTailPhysInnerProg ((L.toCtx, (sb, k)), (base, tsum))) := by
  unfold pageTailPhysInnerProg; dsimp only [PageArenaLayout.toCtx]
  have hbr : ∀ res, BoundedFrameProg L.OwnsAddr 0
      (if res < 8 * L.pgB then do
        let off ← pure ((res + 8 * L.pgB - base % (8 * L.pgB)) % (8 * L.pgB))
        if off < tsum then pure (base + off) else pure 0
      else pure 0) := fun res =>
    BoundedFrameProg.ite_prog (res < 8 * L.pgB)
      (fun _ => by
        simp only [pure_bind]
        exact BoundedFrameProg.ite_prog _
          (fun _ => BoundedFrameProg.pure_prog _)
          (fun _ => BoundedFrameProg.pure_prog _))
      (fun _ => BoundedFrameProg.pure_prog 0)
  exact (BoundedFrameProg.bind_prog (pageReadTailRes_frame L sb k) hbr).mono
    (fun _ h => h) (by omega)

theorem pageTailPhys_frame (L : PageArenaLayout) (sb t : ℕ) :
    BoundedFrameProg L.OwnsAddr 8 (pageTailPhysBoundedProg (L.toCtx, (sb, t))) := by
  have hdsp : ∀ base tc th, BoundedFrameProg L.OwnsAddr 3
      (pageTailPhysDispatchProg (((L.toCtx, (sb, t)), base), (tc, th))) := fun base tc th => by
    unfold pageTailPhysDispatchProg; dsimp only [PageArenaLayout.toCtx]
    refine BoundedFrameProg.ite_prog _ (fun _ => ?_)
      (fun _ => (BoundedFrameProg.pure_prog 0).mono (fun _ h => h) (by omega))
    refine BoundedFrameProg.ite_prog _ (fun _ => ?_)
      (fun _ => (BoundedFrameProg.pure_prog 0).mono (fun _ h => h) (by omega))
    simp only [pure_bind]
    exact pageTailPhysInner_frame L sb _ base _
  unfold pageTailPhysBoundedProg; dsimp only [PageArenaLayout.toCtx]
  have hcont : ∀ (fp tc : ℕ × ℕ) (th : ℕ), BoundedFrameProg L.OwnsAddr 3
      (if fp.1 ≤ L.nCap / L.pgB then
        if fp.2 ≤ (L.nCap - fp.1 * L.pgB) / L.pgB then do
          let base ← pure ((fp.1 + fp.2) * L.pgB)
          pageTailPhysDispatchProg (((L.toCtx, (sb, t)), base), (tc, th))
        else pure 0
      else pure 0) := fun fp tc th =>
    BoundedFrameProg.ite_prog _
      (fun _ => BoundedFrameProg.ite_prog _
        (fun _ => by simp only [pure_bind]; exact hdsp _ tc th)
        (fun _ => (BoundedFrameProg.pure_prog 0).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog 0).mono (fun _ h => h) (by omega))
  dsimp only [PageArenaLayout.toCtx] at hcont
  exact (BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
    BoundedFrameProg.bind_prog (pageReadTailCounts_frame L) fun tc =>
    BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun th =>
    hcont fp tc th).mono (fun _ h => h) (by omega)

theorem pageEffDemote_frame (L : PageArenaLayout) (pRaw u_off : ℕ) :
    BoundedFrameProg L.OwnsAddr 8 (pageEffDemoteBoundedProg (L.toCtx, (pRaw, u_off))) := by
  have hin : ∀ sb qm1 pLast, BoundedFrameProg L.OwnsAddr 2
      (pageEffDemoteInnerProg (L.toCtx, ((sb, qm1), (pRaw, pLast)))) := fun sb qm1 pLast => by
    unfold pageEffDemoteInnerProg; dsimp only [PageArenaLayout.toCtx]
    exact (BoundedFrameProg.bind_prog (pageReadPageOf_frame L sb qm1) fun _ =>
      BoundedFrameProg.pure_prog _).mono (fun _ h => h) (by omega)
  have hchk : ∀ jk ja fp, BoundedFrameProg L.OwnsAddr 2
      (pageEffDemoteCheckProg ((L.toCtx, (pRaw, u_off)), ((jk, ja), fp))) := fun jk ja fp => by
    unfold pageEffDemoteCheckProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact BoundedFrameProg.ite_prog _
      (fun _ => hin _ _ _)
      (fun _ => (BoundedFrameProg.pure_prog pRaw).mono (fun _ h => h) (by omega))
  unfold pageEffDemoteBoundedProg; dsimp only [PageArenaLayout.toCtx]
  dsimp only [PageArenaLayout.toCtx] at hchk
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun jk =>
    BoundedFrameProg.bind_prog (pageReadJobArgs_frame L) fun ja =>
    BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
    BoundedFrameProg.ite_prog _
      (fun _ => BoundedFrameProg.ite_prog _
        (fun _ => hchk jk ja fp)
        (fun _ => (BoundedFrameProg.pure_prog pRaw).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog pRaw).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

theorem pageEffPage_frame (L : PageArenaLayout) (pRaw u_off : ℕ) :
    BoundedFrameProg L.OwnsAddr 11 (pageEffPageBoundedProg (L.toCtx, (pRaw, u_off))) := by
  unfold pageEffPageBoundedProg; dsimp only [PageArenaLayout.toCtx]
  have hcs : ∀ co : ℕ × ℕ, BoundedFrameProg L.OwnsAddr 8
      (if u_off < co.2 then do
        let o1 ← pure 1
        let pCur ← pageReadPageOfProg (L.toCtx, (o1, co.1))
        pure (if pRaw = pCur then co.1 else if pRaw = co.1 then pCur else pRaw)
      else pure pRaw) := fun co =>
    BoundedFrameProg.ite_prog (u_off < co.2)
      (fun _ => by
        simp only [pure_bind]
        exact (BoundedFrameProg.bind_prog (pageReadPageOf_frame L 1 co.1) fun _ =>
          BoundedFrameProg.pure_prog _).mono (fun _ h => h) (by omega))
      (fun _ => (BoundedFrameProg.pure_prog pRaw).mono (fun _ h => h) (by omega))
  dsimp only [PageArenaLayout.toCtx] at hcs
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun ph =>
    BoundedFrameProg.bind_prog (pageReadCleanPos_frame L) fun co =>
    BoundedFrameProg.ite_prog (ph = 2 ∧ 0 < co.2)
      (fun _ => hcs co)
      (fun _ => pageEffDemote_frame L pRaw u_off)).mono
    (fun _ h => h) (by omega)

theorem pageToPhysBoundedProg_frame (L : PageArenaLayout) (sb idx : ℕ) :
    BoundedFrameProg L.OwnsAddr 16 (pageToPhysBoundedProg (L.toCtx, (sb, idx))) := by
  have hfp : ∀ Q, BoundedFrameProg L.OwnsAddr 14
      (pageFullPhysBoundedProg (L.toCtx, ((sb, idx), Q))) := fun Q => by
    unfold pageFullPhysBoundedProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageReadPageOf_frame L sb (idx / L.pgB)) fun pRaw =>
      BoundedFrameProg.bind_prog (pageEffPage_frame L pRaw (idx % L.pgB)) fun effP =>
      BoundedFrameProg.ite_prog (effP < Q)
        (fun _ => BoundedFrameProg.pure_prog _)
        (fun _ => BoundedFrameProg.pure_prog 0)).mono (fun _ h => h) (by omega)
  unfold pageToPhysBoundedProg; dsimp only [PageArenaLayout.toCtx]
  dsimp only [PageArenaLayout.toCtx] at hfp
  have hcont : ∀ fp : ℕ × ℕ, BoundedFrameProg L.OwnsAddr 14
      (if fp.1 ≤ L.nCap / L.pgB then
        if fp.2 ≤ (L.nCap - fp.1 * L.pgB) / L.pgB then do
          let qs ← pure (if sb = 0 then fp.1 else fp.2)
          if idx < qs * L.pgB then do
            let Q ← pure (fp.1 + fp.2)
            pageFullPhysBoundedProg (L.toCtx, ((sb, idx), Q))
          else do
            let tOff ← pure (idx - qs * L.pgB)
            pageTailPhysBoundedProg (L.toCtx, (sb, tOff))
        else pure 0
      else pure 0) := fun fp =>
    BoundedFrameProg.ite_prog _
      (fun _ => BoundedFrameProg.ite_prog _
        (fun _ => by
          simp only [pure_bind]
          exact BoundedFrameProg.ite_prog _
            (fun _ => hfp (fp.1 + fp.2))
            (fun _ => (pageTailPhys_frame L sb _).mono (fun _ h => h) (by omega)))
        (fun _ => (BoundedFrameProg.pure_prog 0).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog 0).mono (fun _ h => h) (by omega))
  dsimp only [PageArenaLayout.toCtx] at hcont
  exact (BoundedFrameProg.bind_prog (pageReadFullPages_frame L) hcont).mono
    (fun _ h => h) (by omega)

theorem pageReadVirtBoundedProg_frame (L : PageArenaLayout) (sb idx : ℕ) :
    BoundedFrameProg L.OwnsAddr 20 (pageReadVirtBoundedProg (L.toCtx, (sb, idx))) := by
  unfold pageReadVirtBoundedProg; dsimp only [PageArenaLayout.toCtx]
  exact BoundedFrameProg.bind_prog (pageToPhysBoundedProg_frame L sb idx) fun p =>
    BoundedFrameProg.ite_prog (p < L.nCap)
      (fun _ => BoundedFrameProg.readPairGen_prog _ _)
      (fun _ => (BoundedFrameProg.pure_prog (0, 0)).mono (fun _ h => h) (by omega))

theorem pageWriteVirtBoundedProg_frame {L : PageArenaLayout} (hw : 0 < L.w)
    (sb idx q v : ℕ) :
    BoundedFrameProg L.OwnsAddr 24 (pageWriteVirtBoundedProg ((L.toCtx, (sb, idx)), (q, v))) := by
  unfold pageWriteVirtBoundedProg; dsimp only [PageArenaLayout.toCtx]
  exact BoundedFrameProg.bind_prog (pageToPhysBoundedProg_frame L sb idx) fun p =>
    BoundedFrameProg.ite_prog (p < L.nCap)
      (fun hp => BoundedFrameProg.writePairGen_prog hw hp
        (fun addr hlo hhi => Or.inr ⟨hlo, hhi⟩))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))

theorem pageSwapTailSlots_frame {L : PageArenaLayout} (hw : 0 < L.w) (p₁ p₂ : ℕ) :
    BoundedFrameProg L.OwnsAddr 44 (pageSwapTailSlotsProg (L.toCtx, (p₁, p₂))) := by
  unfold pageSwapTailSlotsProg; dsimp only [PageArenaLayout.toCtx]
  refine BoundedFrameProg.ite_prog (p₁ = p₂)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)) fun _ => ?_
  refine BoundedFrameProg.ite_prog (p₁ < L.nCap ∧ p₂ < L.nCap) (fun _ => ?_)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  simp only [pure_bind]
  exact (BoundedFrameProg.bind_prog (pageReadTailOwner_frame L _) fun ow₁ =>
    BoundedFrameProg.bind_prog (pageReadTailOwner_frame L _) fun ow₂ =>
    BoundedFrameProg.bind_prog (pageWriteTailRes_frame hw _ _ _) fun _ =>
    BoundedFrameProg.bind_prog (pageWriteTailRes_frame hw _ _ _) fun _ =>
    BoundedFrameProg.bind_prog (pageWriteTailOwner_frame hw _ _ _) fun _ =>
    BoundedFrameProg.bind_prog (pageWriteTailOwner_frame hw _ _ _) fun _ =>
    pageSwapPhys_frame hw p₁ p₂).mono (fun _ h => h) (by omega)

theorem pageStartSide_frame (L : PageArenaLayout) (sb : ℕ) :
    BoundedFrameProg L.OwnsAddr 6 (pageStartSideProg (L.toCtx, sb)) := by
  have hdc2 : ∀ sb' qs Q, BoundedFrameProg L.OwnsAddr 2
      (pageStartDemoteCheckProg (L.toCtx, ((sb', qs), Q))) := fun sb' qs Q => by
    unfold pageStartDemoteCheckProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageReadPageOf_frame L sb' (qs - 1)) fun pLast =>
      BoundedFrameProg.ite_prog (pLast = Q - 1)
        (fun _ => BoundedFrameProg.pure_prog _)
        (fun _ => BoundedFrameProg.pure_prog _)).mono (fun _ h => h) (by omega)
  have hssc2 : ∀ q0 q1 r, BoundedFrameProg L.OwnsAddr 2
      (pageStartSideCheckProg ((L.toCtx, sb), ((q0, q1), r))) := fun q0 q1 r => by
    unfold pageStartSideCheckProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact BoundedFrameProg.ite_prog _
      (fun _ => (BoundedFrameProg.pure_prog _).mono (fun _ h => h) (by omega)) fun _ =>
      BoundedFrameProg.ite_prog _
        (fun _ => hdc2 _ _ _)
        (fun _ => (BoundedFrameProg.pure_prog _).mono (fun _ h => h) (by omega))
  unfold pageStartSideProg; dsimp only [PageArenaLayout.toCtx]
  dsimp only [PageArenaLayout.toCtx] at hssc2
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun q0 =>
    BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun q1 =>
    BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun r =>
    BoundedFrameProg.ite_prog _
      (fun _ => hssc2 q0 q1 r)
      (fun _ => (BoundedFrameProg.pure_prog _).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

theorem pageMaybeStartJob_frame (L : PageArenaLayout) :
    BoundedFrameProg L.OwnsAddr 16 (pageMaybeStartJobProg L.toCtx) := by
  have hinner : BoundedFrameProg L.OwnsAddr 15
      (do
        let z0 ← pure 0
        let c1 ← pure 1
        let o0 ← pageStartSideProg (L.toCtx, z0)
        if o0.1 = 1 then
          pageWriteJobProg (L.metaBase, o0.2)
        else do
          let o1 ← pageStartSideProg (L.toCtx, c1)
          if o1.1 = 1 then
            pageWriteJobProg (L.metaBase, o1.2)
          else
            pure ()) := by
    simp only [pure_bind]
    exact BoundedFrameProg.bind_prog (pageStartSide_frame L 0) fun o0 =>
      BoundedFrameProg.ite_prog (o0.1 = 1)
        (fun _ => (pageWriteJob_frame L o0.2).mono (fun _ h => h) (by omega)) fun _ =>
      BoundedFrameProg.bind_prog (pageStartSide_frame L 1) fun o1 =>
        BoundedFrameProg.ite_prog (o1.1 = 1)
          (fun _ => pageWriteJob_frame L o1.2)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  unfold pageMaybeStartJobProg; dsimp only [PageArenaLayout.toCtx]
  dsimp only [PageArenaLayout.toCtx] at hinner
  exact BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun jk =>
    BoundedFrameProg.ite_prog (jk = 0 ∨ 4 ≤ jk)
      (fun _ => hinner)
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))

theorem pageTickPromote_frame {L : PageArenaLayout} (hw : 0 < L.w) (js cur : ℕ) :
    BoundedFrameProg L.OwnsAddr 60 (pageTickPromoteProg (L.toCtx, (js, cur))) := by
  have hstep : ∀ sb Q, BoundedFrameProg L.OwnsAddr 55
      (pageTickPromoteStepProg (L.toCtx, ((sb, cur), Q))) := fun sb Q => by
    unfold pageTickPromoteStepProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact BoundedFrameProg.bind_prog (pageTailPhys_frame L sb cur) fun p₁ =>
      BoundedFrameProg.ite_prog (cur < L.nCap - Q * L.pgB)
        (fun _ => BoundedFrameProg.bind_prog (pageSwapTailSlots_frame hw p₁ _) fun _ =>
          pageWriteJob_frame L _)
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  have hend : ∀ sb qs Q, BoundedFrameProg L.OwnsAddr 55
      (pageTickPromoteEndProg (L.toCtx, (sb, (qs, Q)))) := fun sb qs Q => by
    unfold pageTickPromoteEndProg pageCommitPromoteDirProg
    dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageReadTailCounts_frame L) fun tc =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun ths =>
      BoundedFrameProg.ite_prog _
        (fun _ => BoundedFrameProg.bind_prog (pageWriteSideMeta_frame L _ _) fun _ =>
          BoundedFrameProg.bind_prog (pageWritePageOf_frame hw _ _ _) fun _ =>
          BoundedFrameProg.bind_prog (pageWriteOwner_frame hw _ _ _) fun _ =>
          pageWriteJob_frame L _)
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
      (fun _ h => h) (by omega)
  unfold pageTickPromoteProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  dsimp only [PageArenaLayout.toCtx] at hstep hend
  exact (BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
    BoundedFrameProg.ite_prog (fp.1 ≤ L.nCap / L.pgB)
      (fun _ => BoundedFrameProg.ite_prog (fp.2 ≤ (L.nCap - fp.1 * L.pgB) / L.pgB)
        (fun _ => BoundedFrameProg.ite_prog (cur < L.pgB)
          (fun _ => hstep _ _)
          (fun _ => hend _ _ _))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

theorem pageTickDemoteSwap_frame {L : PageArenaLayout} (hw : 0 < L.w) (js cur : ℕ) :
    BoundedFrameProg L.OwnsAddr 40 (pageTickDemoteSwapProg (L.toCtx, (js, cur))) := by
  have hsdd : ∀ sb qm1 pDem pLast (owLast : ℕ × ℕ), BoundedFrameProg L.OwnsAddr 24
      (pageSwapDemoteDirProg (L.toCtx, ((sb, qm1), ((pDem, pLast), owLast)))) :=
    fun sb qm1 pDem pLast ⟨os, ov⟩ => by
      unfold pageSwapDemoteDirProg; dsimp only [PageArenaLayout.toCtx]
      exact BoundedFrameProg.bind_prog (pageWritePageOf_frame hw os ov pDem) fun _ =>
        BoundedFrameProg.bind_prog (pageWritePageOf_frame hw sb qm1 pLast) fun _ =>
        BoundedFrameProg.bind_prog (pageWriteOwner_frame hw pDem os ov) fun _ =>
        pageWriteOwner_frame hw pLast sb qm1
  have hbody : ∀ sb qm1 pDem pLast, BoundedFrameProg L.OwnsAddr 32
      (pageTickDemoteSwapBodyProg (L.toCtx, ((sb, qm1), ((pDem, pLast), cur)))) :=
    fun sb qm1 pDem pLast => by
      unfold pageTickDemoteSwapBodyProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
      dsimp only [PageArenaLayout.toCtx] at hsdd
      exact BoundedFrameProg.ite_prog (cur < L.pgB)
        (fun _ => (BoundedFrameProg.bind_prog (pageSwapPhys_frame hw _ _) fun _ =>
          pageWriteJob_frame L _).mono (C₂ := 32) (fun _ h => h) (by omega))
        (fun _ => (BoundedFrameProg.bind_prog (pageReadOwner_frame L pLast) fun owLast =>
          BoundedFrameProg.bind_prog (hsdd sb qm1 pDem pLast owLast) fun _ =>
          pageWriteJob_frame L _).mono (C₂ := 32) (fun _ h => h) (by omega))
  have hchk : ∀ (sb : ℕ) (fp : ℕ × ℕ), BoundedFrameProg L.OwnsAddr 35
      (pageTickDemoteSwapCheckProg ((L.toCtx, (sb, cur)), fp)) := fun sb fp => by
    unfold pageTickDemoteSwapCheckProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    dsimp only [PageArenaLayout.toCtx] at hbody
    exact BoundedFrameProg.ite_prog _
      (fun _ => (BoundedFrameProg.bind_prog (pageReadPageOf_frame L _ _) fun pDem =>
        BoundedFrameProg.ite_prog (pDem < fp.1 + fp.2)
          (fun _ => hbody _ _ pDem _)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
        (fun _ h => h) (by omega))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  unfold pageTickDemoteSwapProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  dsimp only [PageArenaLayout.toCtx] at hchk
  exact (BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
    BoundedFrameProg.ite_prog (fp.1 ≤ L.nCap / L.pgB)
      (fun _ => BoundedFrameProg.ite_prog (fp.2 ≤ (L.nCap - fp.1 * L.pgB) / L.pgB)
        (fun _ => hchk _ fp)
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

theorem pageTickDemoteBuild_frame {L : PageArenaLayout} (hw : 0 < L.w) (js cur : ℕ) :
    BoundedFrameProg L.OwnsAddr 20 (pageTickDemoteBuildProg (L.toCtx, (js, cur))) := by
  have hchk : ∀ sb fp tc ths, BoundedFrameProg L.OwnsAddr 12
      (pageTickDemoteBuildCheckProg ((L.toCtx, (sb, cur)), (fp, (tc, ths)))) :=
    fun sb fp tc ths => by
      unfold pageTickDemoteBuildCheckProg pageTickDemoteBuildStepProg pageTickDemoteBuildEndProg
      dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
      exact BoundedFrameProg.ite_prog _
        (fun _ => BoundedFrameProg.ite_prog (cur < L.pgB)
          (fun _ => (BoundedFrameProg.bind_prog (pageWriteTailRes_frame hw _ _ _) fun _ =>
            BoundedFrameProg.bind_prog (pageWriteTailOwner_frame hw _ _ _) fun _ =>
            pageWriteJob_frame L _).mono (fun _ h => h) (by omega))
          (fun _ => (BoundedFrameProg.bind_prog (pageWriteSideMeta_frame L _ _) fun _ =>
            pageWriteJob_frame L _).mono (fun _ h => h) (by omega)))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  unfold pageTickDemoteBuildProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  dsimp only [PageArenaLayout.toCtx] at hchk
  exact (BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
    BoundedFrameProg.bind_prog (pageReadTailCounts_frame L) fun tc =>
    BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun ths =>
    BoundedFrameProg.ite_prog (fp.1 ≤ L.nCap / L.pgB)
      (fun _ => BoundedFrameProg.ite_prog (fp.2 ≤ (L.nCap - fp.1 * L.pgB) / L.pgB)
        (fun _ => hchk _ fp tc ths)
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

theorem pageTick_frame {L : PageArenaLayout} (hw : 0 < L.w) :
    BoundedFrameProg L.OwnsAddr 80 (pageTickBoundedProg L.toCtx) := by
  have hdisp : ∀ jk (ja : ℕ × ℕ), BoundedFrameProg L.OwnsAddr 76
      (if jk = 1 then do
         pageTickPromoteProg (L.toCtx, (ja.1, ja.2))
         pageMaybeStartJobProg L.toCtx
       else if jk = 2 then do
         pageTickDemoteSwapProg (L.toCtx, (ja.1, ja.2))
         pageMaybeStartJobProg L.toCtx
       else if jk = 3 then do
         pageTickDemoteBuildProg (L.toCtx, (ja.1, ja.2))
         pageMaybeStartJobProg L.toCtx
       else
         pageMaybeStartJobProg L.toCtx) := fun jk ja =>
    BoundedFrameProg.ite_prog (jk = 1)
      (fun _ => BoundedFrameProg.bind_prog (pageTickPromote_frame hw ja.1 ja.2)
        (fun _ => pageMaybeStartJob_frame L)) fun _ =>
    BoundedFrameProg.ite_prog (jk = 2)
      (fun _ => (BoundedFrameProg.bind_prog (pageTickDemoteSwap_frame hw ja.1 ja.2)
        (fun _ => pageMaybeStartJob_frame L)).mono (C₂ := 76) (fun _ h => h) (by omega)) fun _ =>
    BoundedFrameProg.ite_prog (jk = 3)
      (fun _ => (BoundedFrameProg.bind_prog (pageTickDemoteBuild_frame hw ja.1 ja.2)
        (fun _ => pageMaybeStartJob_frame L)).mono (C₂ := 76) (fun _ h => h) (by omega))
      (fun _ => (pageMaybeStartJob_frame L).mono (C₂ := 76) (fun _ h => h) (by omega))
  unfold pageTickBoundedProg; dsimp only [PageArenaLayout.toCtx]
  dsimp only [PageArenaLayout.toCtx] at hdisp
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog L.OwnsAddr (L.metaBase + 27))
    fun jk => BoundedFrameProg.bind_prog (pageReadJobArgs_frame L) fun ja =>
    hdisp jk ja).mono (C₂ := 80) (fun _ h => h) (by omega)

theorem pageRunTicksBatchProg_frame {L : PageArenaLayout} (hw : 0 < L.w) (fuel : ℕ) :
    BoundedFrameProg L.OwnsAddr (80 * fuel) (pageRunTicksBatchProg (L.toCtx, fuel)) := by
  unfold pageRunTicksBatchProg pageRunTicksIterProg; dsimp only
  have hstep : ∀ a, BoundedFrameProg L.OwnsAddr 80 (pageTickIterStepProg (L.toCtx, a)) :=
    fun a => (BoundedFrameProg.bind_prog (pageTick_frame hw)
      (fun _ => BoundedFrameProg.pure_prog a)).mono (fun _ h => h) (by omega)
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.iterate_prog L.toCtx hstep fuel 0)
    (fun _ => BoundedFrameProg.pure_prog ())).mono (fun _ h => h) (by omega)

theorem pageInitScalarsProg_frame (L : PageArenaLayout) (n_0 : ℕ) :
    BoundedFrameProg L.OwnsMetaAddr 14 (pageInitScalarsProg (L.toCtx, n_0)) where
  frontier_eq s := by
    unfold pageInitScalarsProg pageWriteJobProg StateTransitionSpec.clientState
    dsimp only [PageArenaLayout.toCtx]; split_ifs <;> simp
  cost_le s := by
    unfold pageInitScalarsProg pageWriteJobProg
    dsimp only [PageArenaLayout.toCtx]; split_ifs <;> simp
  mem_outside s addr hnot := by
    have hne : ∀ k, 18 ≤ k → k < 32 → addr ≠ L.metaBase + k :=
      fun k h1 h2 heq => hnot (Or.inl ⟨by omega, by omega⟩)
    unfold pageInitScalarsProg pageWriteJobProg StateTransitionSpec.clientState
    dsimp only [PageArenaLayout.toCtx]
    split_ifs
    · simp only [pure_bind, prog_runClient_state_bind, prog_runClient_state_write]
      repeat rw [Function.update_of_ne (hne _ (by omega) (by omega))]
    · rfl

theorem pageInitDirBatchProg_frame {L : PageArenaLayout} (hw : 0 < L.w) (cur fuel : ℕ) :
    BoundedFrameProg L.OwnsMetaAddr (18 * fuel) (pageInitDirBatchProg ((L.toCtx, cur), fuel)) := by
  have hstep : ∀ a, BoundedFrameProg L.OwnsMetaAddr 18
      (pageInitDirStepProg (L.toCtx, a)) := fun a => by
    unfold pageInitDirStepProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    refine BoundedFrameProg.ite_prog (a < L.maxPages) (fun ha => ?_) (fun _ => ?_)
    · have hp0 : BoundedFrameProg L.OwnsMetaAddr 4
          (pageWritePageOfProg ((L.toCtx, (0, a)), a)) := by
        unfold pageWritePageOfProg; dsimp only [PageArenaLayout.toCtx]; rw [ite_eq_left ha]
        simp only [pure_bind]
        exact BoundedFrameProg.writePackedComp_prog hw (by omega : 4 * a + 0 < 4 * L.maxPages)
          (fun addr hlo hhi => Or.inr (Or.inl ⟨hlo, hhi⟩))
      have hp1 : BoundedFrameProg L.OwnsMetaAddr 4
          (pageWritePageOfProg ((L.toCtx, (1, a)), 0)) := by
        unfold pageWritePageOfProg; dsimp only [PageArenaLayout.toCtx]; rw [ite_eq_left ha]
        simp only [pure_bind]
        exact BoundedFrameProg.writePackedComp_prog hw (by omega : 4 * a + 1 < 4 * L.maxPages)
          (fun addr hlo hhi => Or.inr (Or.inl ⟨hlo, hhi⟩))
      have hwo : BoundedFrameProg L.OwnsMetaAddr 8
          (pageWriteOwnerProg ((L.toCtx, a), (0, a))) := by
        unfold pageWriteOwnerProg; dsimp only [PageArenaLayout.toCtx]; rw [ite_eq_left ha]
        simp only [pure_bind]
        exact BoundedFrameProg.bind_prog
          (BoundedFrameProg.writePackedComp_prog hw (by omega : 4 * a + 2 < 4 * L.maxPages)
            (fun addr hlo hhi => Or.inr (Or.inl ⟨hlo, hhi⟩))) fun _ =>
          BoundedFrameProg.writePackedComp_prog hw (by omega : 4 * a + 3 < 4 * L.maxPages)
            (fun addr hlo hhi => Or.inr (Or.inl ⟨hlo, hhi⟩))
      dsimp only [PageArenaLayout.toCtx] at hp0 hp1 hwo
      exact (BoundedFrameProg.bind_prog hp0 fun _ =>
        BoundedFrameProg.bind_prog hp1 fun _ =>
        BoundedFrameProg.bind_prog hwo fun _ =>
        BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
        BoundedFrameProg.pure_prog (a + 1)).mono (fun _ h => h) (by omega)
    · exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
        BoundedFrameProg.pure_prog a).mono (fun _ h => h) (by omega)
  exact BoundedFrameProg.iterate_prog L.toCtx hstep fuel cur

theorem pageInitTailBatchProg_frame {L : PageArenaLayout} (hw : 0 < L.w) (n_0 cur fuel : ℕ) :
    BoundedFrameProg L.OwnsMetaAddr (14 * fuel)
      (pageInitTailBatchProg (((L.toCtx, n_0), cur), fuel)) := by
  have hstep : ∀ a, BoundedFrameProg L.OwnsMetaAddr 14
      (pageInitTailStepProg ((L.toCtx, n_0), a)) := fun a => by
    unfold pageInitTailStepProg pageInitTailResSubProg; dsimp only [PageArenaLayout.toCtx]
    simp only [pure_bind]
    refine BoundedFrameProg.ite_prog (n_0 ≤ L.nCap ∧ a < 8 * L.pgB) (fun _ => ?_) (fun _ => ?_)
    · have hsub : ∀ qbm, BoundedFrameProg L.OwnsMetaAddr 8
          (if a < 4 * L.pgB then do
            pageWriteTailResProg ((L.toCtx, (0, a)), (qbm + a) % (8 * L.pgB))
            pageWriteTailResProg ((L.toCtx, (1, a)), (qbm + a) % (8 * L.pgB))
          else pure ()) := fun qbm => by
        refine BoundedFrameProg.ite_prog (a < 4 * L.pgB) (fun ha4 => ?_)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
        have hw0 : BoundedFrameProg L.OwnsMetaAddr 4
            (pageWriteTailResProg ((L.toCtx, (0, a)), (qbm + a) % (8 * L.pgB))) := by
          unfold pageWriteTailResProg; dsimp only [PageArenaLayout.toCtx]; rw [ite_eq_left ha4]
          simp only [pure_bind]
          exact BoundedFrameProg.writePackedComp_prog hw (by omega : 0 + a < 16 * L.pgB)
            (fun addr hlo hhi => Or.inr (Or.inr ⟨hlo, hhi⟩))
        have hw1 : BoundedFrameProg L.OwnsMetaAddr 4
            (pageWriteTailResProg ((L.toCtx, (1, a)), (qbm + a) % (8 * L.pgB))) := by
          unfold pageWriteTailResProg; dsimp only [PageArenaLayout.toCtx]; rw [ite_eq_left ha4]
          simp only [pure_bind]
          have hidx1 : (if (1 : ℕ) = 0 then 0 else 4 * L.pgB) + a < 16 * L.pgB := by
            simp only [Nat.one_ne_zero, ↓reduceIte]; omega
          exact BoundedFrameProg.writePackedComp_prog hw hidx1
            (fun addr hlo hhi => Or.inr (Or.inr ⟨hlo, hhi⟩))
        exact BoundedFrameProg.bind_prog hw0 fun _ => hw1
      have hwto : ∀ rv, BoundedFrameProg L.OwnsMetaAddr 4
          (pageWriteTailOwnerProg ((L.toCtx, a), (0, rv))) := fun rv => by
        unfold pageWriteTailOwnerProg; dsimp only [PageArenaLayout.toCtx]
        refine BoundedFrameProg.ite_prog (a < 8 * L.pgB ∧ rv < 8 * L.pgB) (fun _ => ?_)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
        simp only [pure_bind]
        exact BoundedFrameProg.writePackedComp_prog hw (by omega : 8 * L.pgB + a < 16 * L.pgB)
          (fun addr hlo hhi => Or.inr (Or.inr ⟨hlo, hhi⟩))
      dsimp only [PageArenaLayout.toCtx] at hsub hwto
      exact (BoundedFrameProg.bind_prog (hsub _) fun _ =>
        BoundedFrameProg.bind_prog (hwto _) fun _ =>
        BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
        BoundedFrameProg.pure_prog (a + 1)).mono (fun _ h => h) (by omega)
    · exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
        BoundedFrameProg.pure_prog a).mono (fun _ h => h) (by omega)
  exact BoundedFrameProg.iterate_prog (L.toCtx, n_0) hstep fuel cur

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

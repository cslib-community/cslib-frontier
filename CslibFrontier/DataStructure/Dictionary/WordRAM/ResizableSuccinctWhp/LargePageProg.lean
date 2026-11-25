/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargePageCoreProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Phase-2c/2d Unpermutation, Virtual Append, and Virtual PopBack (`LargePageProg`)

This module builds on `LargePageCoreProg` to certify `pageBeginUnpermBoundedProg`,
`pageUnpermStepBoundedProg`, `pageRunUnpermBatchProg`, `pageAppendBoundedProg`, and
`pagePopBackBoundedProg` (`RealizesBounded .exact`, `¬ReadsWidth`) together with their
`BoundedFrameProg` cost and memory-frame bounds for the deamortized worst-case WHP resizable
succinct dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.pageBeginUnpermBoundedProg`,
  `pageUnpermStepBoundedProg`, `pageRunUnpermBatchProg`, `pageAppendBoundedProg`,
  `pagePopBackBoundedProg`.

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

/-! ### Phase-2c/2d Unpermutation, Append, and PopBack `Memory.Prog` Operations -/

/-- Realize `PageUnpermState.beginUnperm` in `Memory.Prog` (`¬ReadsWidth`). -/
def pageBeginUnpermBoundedProg : PageArenaCtx → Memory.Prog Unit
  | ((((mb, _od), _o2), _w1), _c2) => do
    let ph ← Memory.read (mb + 18)
    let fp ← pageReadFullPagesProg mb
    let tc ← pageReadTailCountsProg mb
    if ph = 0 ∧ fp.1 = 0 ∧ tc.1 = 0 then do
      let jk ← Memory.read (mb + 27)
      let ph' ← pure (if jk = 0 ∨ 4 ≤ jk then 2 else 1)
      pageWriteCleanProg (mb, (ph', (0, 0)))
    else
      pure ()

theorem realizesBounded_pageBeginUnperm :
    RealizesBounded .exact pageBeginUnpermBoundedProg
      (WordEncoding.encode (α := PageArenaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ctx s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have hrtc := realizesBounded_pageReadTailCounts
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_state_pageReadTailCountsProg] at *
    try simp only [runClient_state_pageReadFullPagesProg] at *
    omega)

theorem pageBeginUnpermBoundedProg_spec {L : PageArenaLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB) :
    let u := extractPageUnperm L s.mem
    let s' := (Memory.spec 0).clientState s (pageBeginUnpermBoundedProg L.toCtx)
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = u.beginUnperm ∧
    arenaPairAt L s'.mem = arenaPairAt L s.mem := by
  dsimp only
  have ⟨hw, _, _, _, _, hpg32, _, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  have hps_st : st.pageSize = L.pgB := hps
  have hB : 0 < st.pageSize := by rw [hps_st]; omega
  have hvl_zero_iff : (st.fullPages false = 0 ∧ st.tailCount false = 0) ↔
      st.virtLen false = 0 := by
    unfold PagePairState.virtLen
    constructor
    · rintro ⟨h1, h2⟩; rw [h1, h2, zero_mul, add_zero]
    · intro hz
      have hq0 : st.fullPages false = 0 := by
        by_contra hnz
        have := Nat.mul_le_mul_right st.pageSize (Nat.pos_of_ne_zero hnz)
        omega
      rw [hq0, zero_mul, zero_add] at hz
      exact ⟨hq0, hz⟩
  unfold pageBeginUnpermBoundedProg PageUnpermState.beginUnperm
  rw [hust]
  dsimp only [PageArenaLayout.toCtx]
  unfold StateTransitionSpec.clientState
  have hph_r : s.mem (L.metaBase + 18) = u.cleanPhase := rfl
  have hfp_eq : (Memory.spec 0).clientResult s (pageReadFullPagesProg L.metaBase) =
      (st.fullPages false, st.fullPages true) := pageReadFullPagesProg_eq L s
  have htc_eq : (Memory.spec 0).clientResult s (pageReadTailCountsProg L.metaBase) =
      (st.tailCount false, st.tailCount true) := pageReadTailCountsProg_eq L s
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    prog_clientResult_read, prog_runClient_state_read,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg,
    hfp_eq, htc_eq, hph_r]
  by_cases hc : u.cleanPhase = 0 ∧ st.virtLen false = 0
  · have hc' : u.cleanPhase = 0 ∧ st.fullPages false = 0 ∧ st.tailCount false = 0 :=
      ⟨hc.1, hvl_zero_iff.mpr hc.2⟩
    rw [ite_eq_left hc', ite_eq_left hc]
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_runClient_state_read]
    have hph_eq : (if (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27)) = 0 ∨
        4 ≤ (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27)) then 2 else 1) =
        (if st.job = .idle then 2 else 1) := by
      change (if s.mem (L.metaBase + 27) = 0 ∨ 4 ≤ s.mem (L.metaBase + 27) then 2 else 1) = _
      have hj_dec : st.job = decodePageJob (s.mem (L.metaBase + 27)) (s.mem (L.metaBase + 28))
          (s.mem (L.metaBase + 29)) := rfl
      rw [hj_dec]; unfold decodePageJob
      split_ifs <;> first | rfl | exfalso; omega | (exfalso; rename_i h; exact h rfl)
    rw [hph_eq]
    obtain ⟨hu_c, ha_c⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s
      (if st.job = .idle then 2 else 1) 0 0
    dsimp only [StateTransitionSpec.clientState] at hu_c ha_c
    exact ⟨runClient_frontier_pageWriteCleanProg
      (L.metaBase, (if st.job = .idle then 2 else 1, (0, 0))) s, hu_c, ha_c⟩
  · have hc' : ¬(u.cleanPhase = 0 ∧ st.fullPages false = 0 ∧ st.tailCount false = 0) :=
      fun h => hc ⟨h.1, hvl_zero_iff.mp h.2⟩
    rw [ite_eq_right hc', ite_eq_right hc]
    exact ⟨rfl, rfl, rfl⟩

private def pageWriteOwnerVpOnlyProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((((((mb, od), (_ot, pb)), ((wv, _pg), (mp, _ib))), _), P), vp) =>
    if P < mp then
      writePackedCompGenProg ((((mb, od), (pb, wv)), 4 * P + 3), vp)
    else
      pure ()

@[simp] private theorem runClient_frontier_pageWriteOwnerVpOnlyProg
    (x : (PageArenaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageWriteOwnerVpOnlyProg x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, _⟩
  unfold pageWriteOwnerVpOnlyProg; dsimp only; split_ifs <;> simp

private theorem realizesBounded_pageWriteOwnerVpOnly :
    RealizesBounded .exact pageWriteOwnerVpOnlyProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwp := realizesBounded_writePackedCompGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, P⟩, vp⟩
    obtain ⟨hw, hwv, hpb, _, _, _, _, hmp_ge4, hmp4, _, _, _, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    dsimp only [Fits] at *
    try omega)
  all_goals exact ⟨4 * mp, hw, rfl, hpb, by omega, by omega⟩

/-- Directory swap commit when `cleanOff = pgB` in `cleanPhase = 2` (`4` calls, `¬ReadsWidth`). -/
private def pageCommitCleanDirProg : PageArenaCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (ctx, (cvp, (pCur, vpOther))) => do
    let o1 ← pure 1
    pageWritePageOfProg ((ctx, (o1, vpOther)), pCur)
    pageWritePageOfProg ((ctx, (o1, cvp)), cvp)
    pageWriteOwnerVpOnlyProg ((ctx, pCur), vpOther)
    pageWriteOwnerVpOnlyProg ((ctx, cvp), cvp)

@[simp] private theorem runClient_frontier_pageCommitCleanDirProg
    (x : PageArenaCtx × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageCommitCleanDirProg x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _, _⟩⟩
  simp [pageCommitCleanDirProg]

private theorem realizesBounded_pageCommitCleanDir :
    RealizesBounded .exact pageCommitCleanDirProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwpo := realizesBounded_pageWritePageOf
  have hwov := realizesBounded_pageWriteOwnerVpOnly
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨cvp, ⟨pCur, vpOther⟩⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h
    subst hwv
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_frontier_pageWriteOwnerVpOnlyProg] at *
    try simp only [runClient_frontier_pageWritePageOfProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

/-- Tail of `coff ≥ pg` branch in `pageUnpermPhase2Prog` (`maybeStartJob` + clean-state update). -/
private def pageFinishCleanStepProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), cvp) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    pageMaybeStartJobProg ctx
    let jk ← Memory.read (mb + 27)
    let q1' ← Memory.read (mb + 22)
    if q1' < mp then do
      let ph' ← pure (if jk = 0 ∨ 4 ≤ jk then 2 else 1)
      let nextVp ← pure (if cvp < q1' then cvp + 1 else q1')
      let z0 ← pure 0
      pageWriteCleanProg (mb, (ph', (nextVp, z0)))
    else
      pure ()

@[simp] private theorem runClient_frontier_pageFinishCleanStepProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageFinishCleanStepProg x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageFinishCleanStepProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    prog_runClient_state_read]
  split_ifs <;> simp

private theorem realizesBounded_pageFinishCleanStep :
    RealizesBounded .exact pageFinishCleanStepProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hms := realizesBounded_pageMaybeStartJob
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, cvp⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have hfr_w := hmem.1
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_frontier_pageMaybeStartJobProg] at *
    first | exact hv0 | omega)

/-- `cleanPhase = 2` helpers of `unpermStep`. -/
private def pageUnpermPhase2ZeroSwapProg :
    PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (cvp, pCur)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let p1 ← pure (pCur * pg)
    let p2 ← pure (cvp * pg)
    let c2 ← pure 2
    let o1 ← pure 1
    pageSwapPhysProg (ctx, (p1, p2))
    pageWriteCleanProg (mb, (c2, (cvp, o1)))

@[simp] private theorem runClient_frontier_pageUnpermPhase2ZeroSwapProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageUnpermPhase2ZeroSwapProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  simp [pageUnpermPhase2ZeroSwapProg]

private theorem realizesBounded_pageUnpermPhase2ZeroSwap :
    RealizesBounded .exact pageUnpermPhase2ZeroSwapProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, (cvp, pCur)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        cvp * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap ∧
        pCur * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hsp := realizesBounded_pageSwapPhys
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨cvp, pCur⟩⟩
    have hcvp_w : Fits w cvp := hwords 11
    have hpC_w : Fits w pCur := hwords 12
    obtain ⟨hv0, hcvp, hpC⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageSwapPhysProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

private def pageUnpermPhase2ZeroProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (cvp, q1)) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if q1 ≤ cvp then do
      let c3 ← pure 3
      let z0 ← pure 0
      pageWriteCleanProg (mb, (c3, (z0, z0)))
    else do
      let o1 ← pure 1
      let pCur ← pageReadPageOfProg (ctx, (o1, cvp))
      if pCur = cvp then do
        let c2 ← pure 2
        let cvp1 ← pure (cvp + 1)
        let z0 ← pure 0
        pageWriteCleanProg (mb, (c2, (cvp1, z0)))
      else if pCur < q1 then
        pageUnpermPhase2ZeroSwapProg (ctx, (cvp, pCur))
      else
        pure ()

@[simp] private theorem runClient_frontier_pageUnpermPhase2ZeroProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageUnpermPhase2ZeroProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageUnpermPhase2ZeroProg; dsimp only
  split_ifs
  · simp
  · simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
      runClient_state_pageReadPageOfProg]
    split_ifs <;> simp

private theorem realizesBounded_pageUnpermPhase2Zero :
    RealizesBounded .exact pageUnpermPhase2ZeroProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, (_, q1)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        q1 * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap ∧
        q1 < (PageArenaLayout.ofCtx ctx).maxPages)
      (fun _ _ => 0) := by
  have hrpo := realizesBounded_pageReadPageOf
  have hwcl := realizesBounded_pageWriteClean
  have hzs := realizesBounded_pageUnpermPhase2ZeroSwap
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨cvp, q1⟩⟩
    obtain ⟨hv0, hq1_nc, hq1_mp⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hmp_w : 4 * mp < 2 ^ w := lt_of_lt_of_le hmp4 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadPageOfProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    have hlt_le : ∀ {x y : ℕ}, x < y → x * pg ≤ y * pg := fun hx =>
      Nat.mul_le_mul_right pg hx.le
    try (have := hlt_le ‹_ < q1›)
    try (have := hlt_le (by omega : cvp < q1))
    omega)

private def pageUnpermPhase2MidSwapProg :
    PageArenaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)),
      ((cvp, coff), pCur)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let p1 ← pure (pCur * pg + coff)
    let p2 ← pure (cvp * pg + coff)
    let c2 ← pure 2
    let coff1 ← pure (coff + 1)
    pageSwapPhysProg (ctx, (p1, p2))
    pageWriteCleanProg (mb, (c2, (cvp, coff1)))

@[simp] private theorem runClient_frontier_pageUnpermPhase2MidSwapProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageUnpermPhase2MidSwapProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  simp [pageUnpermPhase2MidSwapProg]

private theorem realizesBounded_pageUnpermPhase2MidSwap :
    RealizesBounded .exact pageUnpermPhase2MidSwapProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, ((cvp, coff), pCur)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        coff < (PageArenaLayout.ofCtx ctx).pgB ∧
        cvp * (PageArenaLayout.ofCtx ctx).pgB + (PageArenaLayout.ofCtx ctx).pgB ≤
          (PageArenaLayout.ofCtx ctx).nCap ∧
        pCur * (PageArenaLayout.ofCtx ctx).pgB + (PageArenaLayout.ofCtx ctx).pgB ≤
          (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hsp := realizesBounded_pageSwapPhys
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨cvp, coff⟩, pCur⟩⟩
    have hcvp_w : Fits w cvp := hwords 11
    have hpC_w : Fits w pCur := hwords 13
    obtain ⟨hv0, hcoff, hcvp, hpC⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageSwapPhysProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

private def pageUnpermPhase2MidProg :
    PageArenaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (ctx, ((cvp, coff), q1)) =>
    if cvp < q1 then do
      let o1 ← pure 1
      let pCur ← pageReadPageOfProg (ctx, (o1, cvp))
      if pCur < q1 then
        pageUnpermPhase2MidSwapProg (ctx, ((cvp, coff), pCur))
      else
        pure ()
    else
      pure ()

@[simp] private theorem runClient_frontier_pageUnpermPhase2MidProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageUnpermPhase2MidProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageUnpermPhase2MidProg; dsimp only
  split_ifs
  · simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
      runClient_state_pageReadPageOfProg]
    split_ifs <;> simp
  · simp

private theorem realizesBounded_pageUnpermPhase2Mid :
    RealizesBounded .exact pageUnpermPhase2MidProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, ((_, coff), q1)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        coff < (PageArenaLayout.ofCtx ctx).pgB ∧
        q1 * (PageArenaLayout.ofCtx ctx).pgB ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hrpo := realizesBounded_pageReadPageOf
  have hms := realizesBounded_pageUnpermPhase2MidSwap
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨cvp, coff⟩, q1⟩⟩
    obtain ⟨hv0, hcoff, hq1_nc⟩ := h
    have ⟨hw, hwv, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hv0
    subst hwv
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_state_pageReadPageOfProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    have hlt_mul : ∀ {x y : ℕ}, x < y → x * pg + pg ≤ y * pg := fun hx => by
      rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right pg hx
    try (have := hlt_mul ‹_ < q1›)
    try (have := hlt_mul (by omega : cvp < q1))
    omega)

private def pageUnpermPhase2EndProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (ctx, (cvp, q1)) =>
    if cvp < q1 then do
      let o1 ← pure 1
      let pCur ← pageReadPageOfProg (ctx, (o1, cvp))
      let owC ← pageReadOwnerProg (ctx, cvp)
      pageCommitCleanDirProg (ctx, (cvp, (pCur, owC.2)))
      pageFinishCleanStepProg (ctx, cvp)
    else
      pure ()

@[simp] private theorem runClient_frontier_pageUnpermPhase2EndProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageUnpermPhase2EndProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageUnpermPhase2EndProg; dsimp only
  split_ifs <;> simp

private theorem realizesBounded_pageUnpermPhase2End :
    RealizesBounded .exact pageUnpermPhase2EndProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrpo := realizesBounded_pageReadPageOf
  have hro := realizesBounded_pageReadOwner
  have hccd := realizesBounded_pageCommitCleanDir
  have hfcs := realizesBounded_pageFinishCleanStep
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨cvp, q1⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := h
    subst hwv
    have h1_w : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try simp only [runClient_frontier_pageCommitCleanDirProg] at *
    try simp only [runClient_state_pageReadOwnerProg] at *
    try simp only [runClient_state_pageReadPageOfProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

private def pageUnpermPhase2Prog : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (cvp, coff)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let q1 ← Memory.read (mb + 22)
    if q1 ≤ nc / pg ∧ q1 < mp then
      if coff = 0 then
        pageUnpermPhase2ZeroProg (ctx, (cvp, q1))
      else if coff < pg then
        pageUnpermPhase2MidProg (ctx, ((cvp, coff), q1))
      else
        pageUnpermPhase2EndProg (ctx, (cvp, q1))
    else
      pure ()

@[simp] private theorem runClient_frontier_pageUnpermPhase2Prog
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageUnpermPhase2Prog x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  unfold pageUnpermPhase2Prog; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read]
  split_ifs <;> simp

private theorem realizesBounded_pageUnpermPhase2 :
    RealizesBounded .exact pageUnpermPhase2Prog
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hz := realizesBounded_pageUnpermPhase2Zero
  have hm := realizesBounded_pageUnpermPhase2Mid
  have he := realizesBounded_pageUnpermPhase2End
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨cvp, coff⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    have hq1_mul : s.mem (mb + 22) * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    omega)

/-- `cleanPhase = 3` branch of `unpermStep`. -/
private def pageUnpermPhase3SwapProg : PageArenaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), (cvp, p₂)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let o1 ← pure 1
    let p₁ ← pageTailPhysBoundedProg (ctx, (o1, cvp))
    let c3 ← pure 3
    let cvp1 ← pure (cvp + 1)
    let z0 ← pure 0
    pageSwapTailSlotsProg (ctx, (p₁, p₂))
    pageWriteCleanProg (mb, (c3, (cvp1, z0)))

@[simp] private theorem runClient_frontier_pageUnpermPhase3SwapProg
    (x : PageArenaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageUnpermPhase3SwapProg x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨_, _⟩⟩
  simp [pageUnpermPhase3SwapProg]

private theorem realizesBounded_pageUnpermPhase3Swap :
    RealizesBounded .exact pageUnpermPhase3SwapProg
      (WordEncoding.encode (α := PageArenaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, (cvp, _)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧ cvp < 4 * (PageArenaLayout.ofCtx ctx).pgB)
      (fun _ _ => 0) := by
  have htp := realizesBounded_pageTailPhys
  have hsts := realizesBounded_pageSwapTailSlots
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, ⟨cvp, p₂⟩⟩
    obtain ⟨hv0, hcvp⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageSwapTailSlotsProg] at *
    try simp only [runClient_state_pageTailPhysBoundedProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

private def pageUnpermPhase3Prog : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), cvp) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let q1 ← Memory.read (mb + 22)
    let r1 ← Memory.read (mb + 24)
    if r1 ≤ cvp then do
      let c4 ← pure 4
      let z0 ← pure 0
      pageWriteCleanProg (mb, (c4, (cvp, z0)))
    else if q1 ≤ nc / pg ∧ r1 < 4 * pg ∧ cvp < nc - q1 * pg then do
      let p₂ ← pure (q1 * pg + cvp)
      pageUnpermPhase3SwapProg (ctx, (cvp, p₂))
    else
      pure ()

@[simp] private theorem runClient_frontier_pageUnpermPhase3Prog
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageUnpermPhase3Prog x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageUnpermPhase3Prog; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read]
  split_ifs <;> simp

private theorem realizesBounded_pageUnpermPhase3 :
    RealizesBounded .exact pageUnpermPhase3Prog
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwcl := realizesBounded_pageWriteClean
  have hsw := realizesBounded_pageUnpermPhase3Swap
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, cvp⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    have hcvp_w : Fits w cvp := hwords 11
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try exact hv0); try omega)
  all_goals (
    have hq1_mul : s.mem (mb + 22) * pg ≤ (nc / pg) * pg := Nat.mul_le_mul_right pg (by omega)
    have hdiv0 : (nc / pg) * pg ≤ nc := Nat.div_mul_le_self nc pg
    omega)

/-- `cleanPhase = 1` branch of `unpermStep`. -/
private def pageUnpermPhase1TickProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), cvp) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    pageTickBoundedProg ctx
    let q1' ← Memory.read (mb + 22)
    let mvp ← pure (if cvp ≤ q1' then cvp else q1')
    let o1 ← pure 1
    let z0 ← pure 0
    pageWriteCleanProg (mb, (o1, (mvp, z0)))

@[simp] private theorem runClient_frontier_pageUnpermPhase1TickProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageUnpermPhase1TickProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  simp [pageUnpermPhase1TickProg]

private theorem realizesBounded_pageUnpermPhase1Tick :
    RealizesBounded .exact pageUnpermPhase1TickProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have ht := realizesBounded_pageTick
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, cvp⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    have hcvp_w : Fits w cvp := hwords 11
    try simp only [runClient_frontier_pageTickBoundedProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

private def pageUnpermPhase1Prog : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), cvp) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let jk ← Memory.read (mb + 27)
    let q1 ← Memory.read (mb + 22)
    if jk = 0 ∨ 4 ≤ jk then do
      let mvp ← pure (if cvp ≤ q1 then cvp else q1)
      let c2 ← pure 2
      let z0 ← pure 0
      pageWriteCleanProg (mb, (c2, (mvp, z0)))
    else
      pageUnpermPhase1TickProg (ctx, cvp)

@[simp] private theorem runClient_frontier_pageUnpermPhase1Prog
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageUnpermPhase1Prog x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageUnpermPhase1Prog; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read]
  split_ifs <;> simp

private theorem realizesBounded_pageUnpermPhase1 :
    RealizesBounded .exact pageUnpermPhase1Prog
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwcl := realizesBounded_pageWriteClean
  have ht1 := realizesBounded_pageUnpermPhase1Tick
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, cvp⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    have hcvp_w : Fits w cvp := hwords 11
    try dsimp only [Fits] at *
    first | exact hv0 | omega)

/-- Single `O(1)` Phase-2c/2d unpermutation step (`u.unpermStep`, `1 ≤ memoryCost`,
`¬ReadsWidth`). -/
def pageUnpermStepBoundedProg : PageArenaCtx → Memory.Prog Unit
  | ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let ph ← Memory.read (mb + 18)
    let co ← pageReadCleanPosProg mb
    if ph = 1 then
      pageUnpermPhase1Prog (ctx, co.1)
    else if ph = 2 then
      pageUnpermPhase2Prog (ctx, (co.1, co.2))
    else if ph = 3 then
      pageUnpermPhase3Prog (ctx, co.1)
    else
      pure ()

private theorem memoryCost_pageUnpermStepBoundedProg_pos
    (ctx : PageArenaCtx) (s : Memory.State) :
    1 ≤ memoryCost (pageUnpermStepBoundedProg ctx) s := by
  rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageUnpermStepBoundedProg; dsimp only
  simp only [Realization.memoryCost_bind', prog_memoryCost_read]
  omega

@[simp] private theorem runClient_frontier_pageUnpermStepBoundedProg
    (ctx : PageArenaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageUnpermStepBoundedProg ctx)).2.1.frontier = s.frontier := by
  rcases ctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold pageUnpermStepBoundedProg; dsimp only
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_read, runClient_state_pageReadCleanPosProg]
  split_ifs <;> simp

theorem realizesBounded_pageUnpermStep :
    RealizesBounded .exact pageUnpermStepBoundedProg
      (WordEncoding.encode (α := PageArenaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ctx s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrcp := realizesBounded_pageReadCleanPos
  have hp1 := realizesBounded_pageUnpermPhase1
  have hp2 := realizesBounded_pageUnpermPhase2
  have hp3 := realizesBounded_pageUnpermPhase3
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_state_pageReadCleanPosProg] at *
    first | exact hv0 | omega)

private def pageUnpermIterStepProg : PageArenaCtx × ℕ → Memory.Prog ℕ
  | (ctx, acc) => do
    pageUnpermStepBoundedProg ctx
    pure acc

private theorem memoryCost_pageUnpermIterStepProg_pos
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (pageUnpermIterStepProg x) s := by
  rcases x with ⟨ctx, acc⟩
  unfold pageUnpermIterStepProg; dsimp only
  rw [Realization.memoryCost_bind']
  have := memoryCost_pageUnpermStepBoundedProg_pos ctx s
  omega

private theorem realizesBounded_pageUnpermIterStep :
    RealizesBounded .exact pageUnpermIterStepProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hu := realizesBounded_pageUnpermStep
  realize
  exact h

private def pageRunUnpermIterProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, z), fuel) => iterate pageUnpermIterStepProg ctx fuel z

private theorem realizesBounded_pageRunUnpermIter :
    RealizesBounded .exact pageRunUnpermIterProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, z), fuel) s =>
        iterationSafe pageUnpermIterStepProg
          (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
          w ctx fuel z s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := PageArenaCtx))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_pageUnpermIterStep
    memoryCost_pageUnpermIterStepProg_pos

/-- Batched `fuel`-step Phase-2c/2d unpermuter (`runUnpermSteps fuel`, `¬ReadsWidth`). -/
def pageRunUnpermBatchProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (ctx, fuel) => do
    let _ ← pageRunUnpermIterProg ((ctx, 0), fuel)
    pure ()

private theorem pageRunUnpermIter_safe (ctx : PageArenaCtx) (w : ℕ) :
    ∀ (fuel z : ℕ) (s : Memory.State),
      (PageArenaLayout.ofCtx ctx).Valid w s.frontier →
      iterationSafe pageUnpermIterStepProg
        (fun w' (c', _) s' => (PageArenaLayout.ofCtx c').Valid w' s'.frontier)
        w ctx fuel z s := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; exact trivial
  | succ k ih =>
    intro z s hv
    have hfr1 : ((Memory.spec 0).clientState s (pageUnpermIterStepProg (ctx, z))).frontier =
        s.frontier := by
      unfold pageUnpermIterStepProg StateTransitionSpec.clientState; dsimp only
      simp [runClient_frontier_pageUnpermStepBoundedProg]
    unfold iterationSafe
    rw [clientResult_width, clientState_width]
    exact ⟨hv, ih _ _ (hfr1.symm ▸ hv)⟩

theorem realizesBounded_pageRunUnpermBatch :
    RealizesBounded .exact pageRunUnpermBatchProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hit := realizesBounded_pageRunUnpermIter
  realize
  rcases d with ⟨ctx, fuel⟩
  exact pageRunUnpermIter_safe ctx w fuel 0 s h

theorem pageUnpermStepBoundedProg_spec {L : PageArenaLayout} {s : Memory.State} {slack : ℕ}
    (hvL : L.Valid L.w s.frontier)
    (hi : (extractPageUnperm L s.mem).InvWithSlack slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap) :
    let u := extractPageUnperm L s.mem
    let res := u.unpermStep
    let s' := (Memory.spec 0).clientState s (pageUnpermStepBoundedProg L.toCtx)
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = res.1 ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  dsimp only
  have ⟨hw, _, _, _, _, hpg32, hpg16, hmp4, _, hnc_mp, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  have hi_u : u.InvWithSlack slack := hi
  have hv : st.Valid := hi_u.valid
  have hps_st : st.pageSize = L.pgB := hps
  have hti_st : st.totalItems ≤ L.nCap := hti
  have hB : 0 < L.pgB := by omega
  have htp2 : st.totalPages + 2 ≤ L.maxPages := by
    have hle : st.totalPages * L.pgB ≤ (L.maxPages - 2) * L.pgB := by
      have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq; omega
    have htp_le : st.totalPages ≤ L.maxPages - 2 := (Nat.mul_le_mul_right_iff hB).mp hle
    omega
  refine ⟨by simpa only [StateTransitionSpec.clientState] using
    runClient_frontier_pageUnpermStepBoundedProg L.toCtx s, ?_⟩
  unfold pageUnpermStepBoundedProg pageUnpermPhase1Prog
    pageUnpermPhase1TickProg PageUnpermState.unpermStep
  rw [hust]
  dsimp only [PageArenaLayout.toCtx]
  unfold StateTransitionSpec.clientState
  have hph_r : s.mem (L.metaBase + 18) = u.cleanPhase := rfl
  have hco_eq : (Memory.spec 0).clientResult s (pageReadCleanPosProg L.metaBase) =
      (u.cleanVp, u.cleanOff) := pageReadCleanPosProg_eq L s
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    prog_clientResult_read, prog_runClient_state_read,
    runClient_state_pageReadCleanPosProg, hco_eq, hph_r]
  by_cases hp1 : u.cleanPhase = 1
  · rw [ite_eq_left hp1, ite_eq_left hp1]
    obtain ⟨hwb, _, _⟩ := hi_u.phase1_wb hp1
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_runClient_state_read]
    have hq1_r : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 22)) =
        st.fullPages true := rfl
    have hj_dec : st.job = decodePageJob (s.mem (L.metaBase + 27)) (s.mem (L.metaBase + 28))
        (s.mem (L.metaBase + 29)) := rfl
    by_cases hj : st.job = .idle
    · have hjk0 : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27)) = 0 ∨
          4 ≤ (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27)) := by
        change s.mem (L.metaBase + 27) = 0 ∨ 4 ≤ s.mem (L.metaBase + 27)
        rw [hj_dec] at hj; unfold decodePageJob at hj
        by_contra hc
        have h123 : s.mem (L.metaBase + 27) = 1 ∨ s.mem (L.metaBase + 27) = 2 ∨
            s.mem (L.metaBase + 27) = 3 := by omega
        rcases h123 with h1 | h2 | h3
        · simp [h1] at hj
        · simp [h2] at hj
        · simp [h3] at hj
      rw [ite_eq_left hjk0, ite_eq_left hj, hq1_r]
      have hmin_eq : (if u.cleanVp ≤ st.fullPages true then u.cleanVp else st.fullPages true) =
          min u.cleanVp (st.fullPages true) := rfl
      rw [hmin_eq]
      obtain ⟨hu_c, ha_c⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s
        2 (min u.cleanVp (st.fullPages true)) 0
      dsimp only [StateTransitionSpec.clientState] at hu_c ha_c
      rw [hu_c, ha_c]
      exact ⟨rfl, rfl⟩
    · have hjk_nz : ¬((Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27)) = 0 ∨
          4 ≤ (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 27))) := by
        change ¬(s.mem (L.metaBase + 27) = 0 ∨ 4 ≤ s.mem (L.metaBase + 27))
        intro hc; apply hj; rw [hj_dec]; unfold decodePageJob
        rcases hc with h0 | h4 <;> split_ifs <;> first | rfl | omega
      rw [ite_eq_right hjk_nz, ite_eq_right hj]
      obtain ⟨_, hu_t, ha_t⟩ := pageTickBoundedProg_spec hvL hwb.toDriftInv hps hti
      set s_t := (Memory.spec 0).clientState s (pageTickBoundedProg L.toCtx)
      have hs_t_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s
          (pageTickBoundedProg
            ((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
              (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap))))) = s_t := rfl
      have hq1'_eq : s_t.mem (L.metaBase + 22) = st.tick.1.fullPages true := by
        have := congrArg (fun x => x.st.fullPages true) hu_t
        dsimp only [extractPageUnperm, extractPagePair] at this; exact this
      simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
        hs_t_eq, prog_clientResult_read, prog_runClient_state_read, hq1'_eq]
      have hmin_eq : (if u.cleanVp ≤ st.tick.1.fullPages true then u.cleanVp
          else st.tick.1.fullPages true) = min u.cleanVp (st.tick.1.fullPages true) := rfl
      rw [hmin_eq]
      obtain ⟨hu_c, ha_c⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_t
        1 (min u.cleanVp (st.tick.1.fullPages true)) 0
      dsimp only [StateTransitionSpec.clientState] at hu_c ha_c
      rw [hu_c, hu_t, ha_c, ha_t]
      exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hp1, ite_eq_right hp1]
    by_cases hp2 : u.cleanPhase = 2
    · rw [ite_eq_left hp2, ite_eq_left hp2]
      obtain ⟨hf0_u, _⟩ := hi_u.src_empty (by omega)
      have hf0 : st.fullPages false = 0 := hf0_u
      have htotP : st.totalPages = st.fullPages true := by
        unfold PagePairState.totalPages; rw [hf0, zero_add]
      have hq1_le : st.fullPages true ≤ L.nCap / L.pgB := by
        refine (Nat.le_div_iff_mul_le hB).mpr ?_
        have hti_eq := st.totalItems_eq; rw [hps_st, htotP] at hti_eq; omega
      have hq1_mp : st.fullPages true < L.maxPages := by omega
      have hc_q1 : st.fullPages true ≤ L.nCap / L.pgB ∧ st.fullPages true < L.maxPages :=
        ⟨hq1_le, hq1_mp⟩
      unfold pageUnpermPhase2Prog pageUnpermPhase2ZeroProg pageUnpermPhase2ZeroSwapProg
        pageUnpermPhase2MidProg pageUnpermPhase2MidSwapProg pageUnpermPhase2EndProg
      dsimp only
      have hq1_r : s.mem (L.metaBase + 22) = st.fullPages true := rfl
      simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
        prog_clientResult_read, prog_runClient_state_read, hq1_r, ite_eq_left hc_q1]
      by_cases hoff0 : u.cleanOff = 0
      · rw [ite_eq_left hoff0, ite_eq_left hoff0]
        by_cases hdone : st.fullPages true ≤ u.cleanVp
        · rw [ite_eq_left hdone, ite_eq_left hdone]
          (try dsimp only)
          obtain ⟨hu_c, ha_c⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s 3 0 0
          dsimp only [StateTransitionSpec.clientState] at hu_c ha_c
          rw [hu_c, ha_c]
          exact ⟨rfl, rfl⟩
        · rw [ite_eq_right hdone, ite_eq_right hdone]
          have hcvp_lt : u.cleanVp < st.fullPages true := Nat.lt_of_not_ge hdone
          have hcvp_mp : u.cleanVp < L.maxPages := hcvp_lt.trans hq1_mp
          have hpCur_lt : st.pageOf true u.cleanVp < st.fullPages true :=
            htotP ▸ hv.page_lt true u.cleanVp hcvp_lt
          have hpOF : (Memory.spec 0).clientResult s
              (pageReadPageOfProg (L.toCtx, (1, u.cleanVp))) =
              st.pageOf true u.cleanVp := pageReadPageOfProg_eq true hcvp_mp s
          dsimp only [PageArenaLayout.toCtx] at hpOF
          simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
            runClient_state_pageReadPageOfProg, hpOF]
          by_cases hP_eq : st.pageOf true u.cleanVp = u.cleanVp
          · rw [ite_eq_left hP_eq, ite_eq_left hP_eq]
            obtain ⟨hu_c, ha_c⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s
              2 (u.cleanVp + 1) 0
            dsimp only [StateTransitionSpec.clientState] at hu_c ha_c
            rw [hu_c, ha_c]
            exact ⟨rfl, rfl⟩
          · rw [ite_eq_right hP_eq, ite_eq_right hP_eq, ite_eq_left hpCur_lt]
            set p₁ := st.pageOf true u.cleanVp * L.pgB
            set p₂ := u.cleanVp * L.pgB
            have hp_nc : p₁ < L.nCap ∧ p₂ < L.nCap := by
              have h1 : (st.pageOf true u.cleanVp + 1) * L.pgB ≤ st.fullPages true * L.pgB :=
                Nat.mul_le_mul_right _ hpCur_lt
              have h2 : (u.cleanVp + 1) * L.pgB ≤ st.fullPages true * L.pgB :=
                Nat.mul_le_mul_right _ hcvp_lt
              rw [Nat.add_one_mul] at h1 h2
              have hti_eq := st.totalItems_eq; rw [hps_st, htotP] at hti_eq
              exact ⟨by dsimp only [p₁]; omega, by dsimp only [p₂]; omega⟩
            unfold pageSwapPhysProg
            dsimp only
            rw [ite_eq_left hp_nc]
            simp only [StateTransitionSpec.clientState, prog_runClient_state_bind]
            obtain ⟨hu_sw, ha_sw⟩ := swapPairGenProg_arena_eq hw hm_ib ho1 ho2 s p₁ p₂
            dsimp only [StateTransitionSpec.clientState] at hu_sw ha_sw
            obtain ⟨hu_c, ha_c⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib
              (((Memory.spec 0).runClient s
                (swapPairGenProg (((L.itemBase, (L.qBits, L.vBits)), L.w), (p₁, p₂)))).2.1)
              2 u.cleanVp 1
            dsimp only [StateTransitionSpec.clientState] at hu_c ha_c
            rw [hu_c, hu_sw, ha_c, ha_sw, applySwaps_cons, applySwaps_nil]
            dsimp only [p₁, p₂]; rw [hps_st]
            exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hoff0, ite_eq_right hoff0, ← hps_st]
        rw [hps_st]
        obtain ⟨_, hcvp_lt, _, _, _⟩ := hi_u.phase2_pos hp2 (Nat.pos_of_ne_zero hoff0)
        have hcvp_lt_st : u.cleanVp < st.fullPages true := hcvp_lt
        have hcvp_mp : u.cleanVp < L.maxPages := hcvp_lt_st.trans hq1_mp
        have hpCur_lt : st.pageOf true u.cleanVp < st.fullPages true :=
          htotP ▸ hv.page_lt true u.cleanVp hcvp_lt
        have hpOF : (Memory.spec 0).clientResult s
            (pageReadPageOfProg (L.toCtx, (1, u.cleanVp))) =
            st.pageOf true u.cleanVp := pageReadPageOfProg_eq true hcvp_mp s
        dsimp only [PageArenaLayout.toCtx] at hpOF
        by_cases hoff_lt : u.cleanOff < L.pgB
        · rw [ite_eq_left hoff_lt, ite_eq_left hoff_lt, ite_eq_left hcvp_lt_st]
          (try dsimp only)
          simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
            runClient_state_pageReadPageOfProg, hpOF, ite_eq_left hpCur_lt]
          set p₁ := st.pageOf true u.cleanVp * L.pgB + u.cleanOff
          set p₂ := u.cleanVp * L.pgB + u.cleanOff
          have hp_nc : p₁ < L.nCap ∧ p₂ < L.nCap := by
            have h1 : (st.pageOf true u.cleanVp + 1) * L.pgB ≤ st.fullPages true * L.pgB :=
              Nat.mul_le_mul_right _ hpCur_lt
            have h2 : (u.cleanVp + 1) * L.pgB ≤ st.fullPages true * L.pgB :=
              Nat.mul_le_mul_right _ hcvp_lt_st
            rw [Nat.add_one_mul] at h1 h2
            have hti_eq := st.totalItems_eq; rw [hps_st, htotP] at hti_eq
            exact ⟨by dsimp only [p₁]; omega, by dsimp only [p₂]; omega⟩
          unfold pageSwapPhysProg
          dsimp only
          rw [ite_eq_left hp_nc]
          obtain ⟨hu_sw, ha_sw⟩ := swapPairGenProg_arena_eq hw hm_ib ho1 ho2 s p₁ p₂
          dsimp only [StateTransitionSpec.clientState] at hu_sw ha_sw
          obtain ⟨hu_c, ha_c⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib
            (((Memory.spec 0).runClient s
              (swapPairGenProg (((L.itemBase, (L.qBits, L.vBits)), L.w), (p₁, p₂)))).2.1)
            2 u.cleanVp (u.cleanOff + 1)
          dsimp only [StateTransitionSpec.clientState] at hu_c ha_c
          rw [hu_c, hu_sw, ha_c, ha_sw, applySwaps_cons, applySwaps_nil]
          exact ⟨rfl, rfl⟩
        · rw [ite_eq_right hoff_lt, ite_eq_right hoff_lt, ite_eq_left hcvp_lt_st]
          have hpCur_mp : st.pageOf true u.cleanVp < L.maxPages := hpCur_lt.trans hq1_mp
          obtain ⟨hvpo_lt, _⟩ := hv.pageOf_owner u.cleanVp (htotP.symm ▸ hcvp_lt_st)
          have hvpo_mp : st.ownerVp u.cleanVp < L.maxPages := by
            cases hs_o : st.ownerSide u.cleanVp
            · rw [hs_o, hf0] at hvpo_lt; exact absurd hvpo_lt (Nat.not_lt_zero _)
            · rw [hs_o] at hvpo_lt; exact hvpo_lt.trans hq1_mp
          have howC : ((Memory.spec 0).clientResult s (pageReadOwnerProg (L.toCtx, u.cleanVp))).2 =
              st.ownerVp u.cleanVp := by
            unfold pageReadOwnerProg
            dsimp only [PageArenaLayout.toCtx]
            rw [ite_eq_left hcvp_mp]
            dsimp only [st, extractPagePair]
            rw [ite_eq_left hcvp_mp]
            simp only [pure_bind, prog_clientResult_bind, clientResult_readPackedCompGenProg,
              runClient_state_readPackedCompGenProg, prog_clientResult_pure]
          dsimp only [PageArenaLayout.toCtx] at howC
          (try dsimp only)
          simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
            runClient_state_pageReadPageOfProg, hpOF, runClient_state_pageReadOwnerProg, howC]
          unfold pageCommitCleanDirProg pageWritePageOfProg pageWriteOwnerVpOnlyProg
          dsimp only
          simp only [pure_bind]
          rw [ite_eq_left hvpo_mp, ite_eq_left hcvp_mp, ite_eq_left hpCur_mp, ite_eq_left hcvp_mp]
          simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
            runClient_state_writePackedCompGenProg, Nat.one_ne_zero, ↓reduceIte]
          set m_c := writePacked (L.metaBase + L.offDir) L.ptrB L.w
            (writePacked (L.metaBase + L.offDir) L.ptrB L.w
              (writePacked (L.metaBase + L.offDir) L.ptrB L.w
                (writePacked (L.metaBase + L.offDir) L.ptrB L.w s.mem
                  (4 * st.ownerVp u.cleanVp + 1) (st.pageOf true u.cleanVp))
                (4 * u.cleanVp + 1) u.cleanVp)
              (4 * st.pageOf true u.cleanVp + 3) (st.ownerVp u.cleanVp))
            (4 * u.cleanVp + 3) u.cleanVp
          obtain ⟨hu_c4, ha_c4⟩ := extractPageUnperm_writeOwnerVp hw ho1 ho2 hm_ib _
            hcvp_mp (hcvp_mp.trans (by omega))
          obtain ⟨hu_c3, ha_c3⟩ := extractPageUnperm_writeOwnerVp hw ho1 ho2 hm_ib _
            hpCur_mp (hvpo_mp.trans (by omega))
          obtain ⟨hu_c2, ha_c2⟩ := extractPageUnperm_writePageOf hw ho1 ho2 hm_ib _ true
            hcvp_mp (hcvp_mp.trans (by omega))
          obtain ⟨hu_c1, ha_c1⟩ := extractPageUnperm_writePageOf hw ho1 ho2 hm_ib s.mem true
            hvpo_mp (hpCur_mp.trans (by omega))
          simp only [↓reduceIte] at hu_c1 ha_c1 hu_c2 ha_c2
          have hu_mc : extractPageUnperm L m_c =
              { u with
                st :=
                  { st with
                    pageOf := PagePairState.set2
                      (PagePairState.set2 st.pageOf true (st.ownerVp u.cleanVp)
                        (st.pageOf true u.cleanVp)) true u.cleanVp u.cleanVp
                    ownerVp := Function.update
                      (Function.update st.ownerVp (st.pageOf true u.cleanVp)
                        (st.ownerVp u.cleanVp)) u.cleanVp u.cleanVp } } := by
            dsimp only [m_c]; rw [hu_c4, hu_c3, hu_c2, hu_c1]; rfl
          have ha_mc : arenaPairAt L m_c = arenaPairAt L s.mem := by
            dsimp only [m_c]; rw [ha_c4, ha_c3, ha_c2, ha_c1]
          set s_c : Memory.State := { mem := m_c, frontier := s.frontier }
          have htc_c : ∀ side, (extractPagePair L s_c.mem).tailCount side < 4 * L.pgB :=
            fun side => by
              have := congrArg (fun x => x.st.tailCount side) hu_mc
              dsimp only [s_c, extractPageUnperm] at this; rw [this]
              exact hps_st ▸ hv.tailCount_lt side
          have hps_c : (extractPagePair L s_c.mem).pageSize = L.pgB := by
            have := congrArg (fun x => x.st.pageSize) hu_mc
            dsimp only [s_c, extractPageUnperm] at this; rw [this]; exact hps_st
          have hmp_c : (extractPagePair L s_c.mem).totalPages < L.maxPages := by
            have := congrArg (fun x => x.st.totalPages) hu_mc
            dsimp only [s_c, extractPageUnperm] at this; rw [this]
            change st.totalPages < L.maxPages; omega
          obtain ⟨_, hu_ms, ha_ms⟩ := pageMaybeStartJobProg_spec (s := s_c) hvL htc_c hps_c hmp_c
          set s_ms := (Memory.spec 0).clientState s_c (pageMaybeStartJobProg L.toCtx)
          unfold pageFinishCleanStepProg; dsimp only
          have hs_ms_eq : (((Memory.spec 0).runClient s_c
              (pageMaybeStartJobProg
                ((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
                  (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)))).2.1) = s_ms := rfl
          simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
            hs_ms_eq, prog_runClient_state_read]
          set st_ms := (extractPagePair L s_c.mem).maybeStartJob
          have hu_sms : extractPageUnperm L s_ms.mem = { u with st := st_ms } := by
            rw [hu_ms]
            have hu_sc : extractPageUnperm L s_c.mem =
                { u with st := extractPagePair L s_c.mem } := by
              rw [show s_c.mem = m_c from rfl, hu_mc]
              have hst_mc := congrArg PageUnpermState.st hu_mc
              dsimp only [extractPageUnperm] at hst_mc ⊢
              rw [hst_mc]
            rw [hu_sc]
          have hjk_ms : (if (Memory.spec 0).clientResult s_ms (Memory.read (L.metaBase + 27)) = 0 ∨
              4 ≤ (Memory.spec 0).clientResult s_ms (Memory.read (L.metaBase + 27)) then 2
              else 1) = (if st_ms.job = .idle then 2 else 1) := by
            change (if s_ms.mem (L.metaBase + 27) = 0 ∨ 4 ≤ s_ms.mem (L.metaBase + 27) then 2
              else 1) = _
            have hj_d : st_ms.job = decodePageJob (s_ms.mem (L.metaBase + 27))
                (s_ms.mem (L.metaBase + 28)) (s_ms.mem (L.metaBase + 29)) :=
              (congrArg (fun x => x.st.job) hu_sms).symm
            rw [hj_d]; unfold decodePageJob
            split_ifs <;> first | rfl | exfalso; omega | (exfalso; rename_i h; exact h rfl)
          have hq1_ms : (Memory.spec 0).clientResult s_ms (Memory.read (L.metaBase + 22)) =
              st_ms.fullPages true := by
            change s_ms.mem (L.metaBase + 22) = st_ms.fullPages true
            have := congrArg (fun x => x.st.fullPages true) hu_sms
            dsimp only [extractPageUnperm, extractPagePair] at this; exact this
          have hq1_ms_mp : st_ms.fullPages true < L.maxPages := by
            have hfp_ms : st_ms.fullPages = (extractPagePair L s_c.mem).fullPages := by
              unfold st_ms PagePairState.maybeStartJob
              cases (extractPagePair L s_c.mem).job <;> try rfl
              dsimp only; split_ifs <;> rfl
            have hfp_sc : (extractPagePair L s_c.mem).fullPages true = st.fullPages true := by
              have := congrArg (fun x => x.st.fullPages true) hu_mc
              dsimp only [s_c, extractPageUnperm, extractPagePair] at this; exact this
            rw [hfp_ms, hfp_sc]; exact hq1_mp
          rw [hq1_ms, ite_eq_left hq1_ms_mp]
          simp only [pure_bind]
          rw [hjk_ms]
          have hmin_eq : (if u.cleanVp < st_ms.fullPages true then u.cleanVp + 1
              else st_ms.fullPages true) = min (u.cleanVp + 1) (st_ms.fullPages true) := by
            split_ifs <;> simp [Nat.min_def] <;> omega
          rw [hmin_eq]
          obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_ms
            (if st_ms.job = .idle then 2 else 1) (min (u.cleanVp + 1) (st_ms.fullPages true)) 0
          dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
          rw [hu_cl, hu_sms, ha_cl, ha_ms, ha_mc]
          have hst_c_eq : extractPagePair L s_c.mem =
              { st with
                pageOf := PagePairState.set2
                  (PagePairState.set2 st.pageOf true (st.ownerVp u.cleanVp)
                    (st.pageOf true u.cleanVp)) true u.cleanVp u.cleanVp
                ownerVp := Function.update
                  (Function.update st.ownerVp (st.pageOf true u.cleanVp)
                    (st.ownerVp u.cleanVp)) u.cleanVp u.cleanVp } :=
            congrArg PageUnpermState.st hu_mc
          dsimp only [st_ms]
          simp only [hst_c_eq]
          rw [hps_st]
          exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hp2, ite_eq_right hp2]
      by_cases hp3 : u.cleanPhase = 3
      · rw [ite_eq_left hp3, ite_eq_left hp3]
        obtain ⟨hf0_u, _⟩ := hi_u.src_empty (by omega)
        have hf0 : st.fullPages false = 0 := hf0_u
        have htotP : st.totalPages = st.fullPages true := by
          unfold PagePairState.totalPages; rw [hf0, zero_add]
        unfold pageUnpermPhase3Prog pageUnpermPhase3SwapProg
        dsimp only
        have hq1_r : s.mem (L.metaBase + 22) = st.fullPages true := rfl
        have hr1_r : s.mem (L.metaBase + 24) = st.tailCount true := rfl
        simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
          prog_clientResult_read, prog_runClient_state_read, hq1_r, hr1_r]
        by_cases hdone : st.tailCount true ≤ u.cleanVp
        · rw [ite_eq_left hdone, ite_eq_left hdone]
          (try dsimp only)
          obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s
            4 u.cleanVp 0
          dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
          rw [hu_cl, ha_cl]
          exact ⟨rfl, rfl⟩
        · rw [ite_eq_right hdone, ite_eq_right hdone]
          have hcvp_lt : u.cleanVp < st.tailCount true := Nat.lt_of_not_ge hdone
          have hq1_le : st.fullPages true ≤ L.nCap / L.pgB := by
            refine (Nat.le_div_iff_mul_le hB).mpr ?_
            have hti_eq := st.totalItems_eq; rw [hps_st, htotP] at hti_eq; omega
          have hr1_lt : st.tailCount true < 4 * L.pgB := hps_st ▸ hv.tailCount_lt true
          have hp₂_nc : u.cleanVp < L.nCap - st.fullPages true * L.pgB := by
            have hti_eq := st.totalItems_eq; rw [hps_st, htotP] at hti_eq; omega
          have hc_p3 : st.fullPages true ≤ L.nCap / L.pgB ∧ st.tailCount true < 4 * L.pgB ∧
              u.cleanVp < L.nCap - st.fullPages true * L.pgB := ⟨hq1_le, hr1_lt, hp₂_nc⟩
          rw [ite_eq_left hc_p3]
          have hp₁_eq : (Memory.spec 0).clientResult s
              (pageTailPhysBoundedProg (L.toCtx, (1, u.cleanVp))) =
              st.tailPhys true u.cleanVp :=
            pageTailPhysBoundedProg_eq hv hps hti true hcvp_lt
          dsimp only [PageArenaLayout.toCtx] at hp₁_eq
          have hp₁_lo : st.totalPages * L.pgB ≤ st.tailPhys true u.cleanVp :=
            hps_st ▸ le_physOfRes _ _ _
          have hp₁_hi : st.tailPhys true u.cleanVp < st.totalItems := hv.tail_lt true _ hcvp_lt
          have hp₂_lo : st.totalPages * L.pgB ≤ st.fullPages true * L.pgB + u.cleanVp := by
            rw [htotP]; exact Nat.le_add_right _ _
          have hp₂_hi : st.fullPages true * L.pgB + u.cleanVp < st.totalItems := by
            have hti_eq := st.totalItems_eq; rw [hps_st, htotP] at hti_eq; omega
          (try dsimp only)
          simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
            runClient_state_pageTailPhysBoundedProg, hp₁_eq]
          obtain ⟨_, hu_sw, ha_sw⟩ := pageSwapTailSlotsProg_spec hvL hv hps hti
            hp₁_lo hp₁_hi hp₂_lo hp₂_hi
          set s_sw := (Memory.spec 0).clientState s
            (pageSwapTailSlotsProg
              (L.toCtx, (st.tailPhys true u.cleanVp, st.fullPages true * L.pgB + u.cleanVp)))
          have hs_sw_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s
              (pageSwapTailSlotsProg
                (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
                  (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)),
                (st.tailPhys true u.cleanVp, st.fullPages true * L.pgB + u.cleanVp))))) = s_sw :=
            rfl
          rw [hs_sw_eq]
          obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_sw
            3 (u.cleanVp + 1) 0
          dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
          rw [hu_cl, hu_sw, ha_cl, ha_sw, hps_st]
          exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hp3, ite_eq_right hp3]
        exact ⟨rfl, rfl⟩

theorem pageRunUnpermBatchProg_spec (fuel : ℕ) {L : PageArenaLayout} {s : Memory.State}
    {slack : ℕ} (hvL : L.Valid L.w s.frontier)
    (hi : (extractPageUnperm L s.mem).InvWithSlack slack)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap) :
    let u := extractPageUnperm L s.mem
    let res := PageUnpermState.runUnpermSteps fuel u
    let s' := (Memory.spec 0).clientState s (pageRunUnpermBatchProg (L.toCtx, fuel))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = res.1 ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  suffices hiter : ∀ k {s : Memory.State},
      L.Valid L.w s.frontier →
      (extractPageUnperm L s.mem).InvWithSlack slack →
      (extractPagePair L s.mem).pageSize = L.pgB →
      (extractPagePair L s.mem).totalItems ≤ L.nCap →
      let u := extractPageUnperm L s.mem
      let res := PageUnpermState.runUnpermSteps k u
      let s' := (Memory.spec 0).clientState s (iterate pageUnpermIterStepProg L.toCtx k 0)
      s'.frontier = s.frontier ∧
      extractPageUnperm L s'.mem = res.1 ∧
      arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) by
    unfold pageRunUnpermBatchProg pageRunUnpermIterProg StateTransitionSpec.clientState
    dsimp only
    simp only [prog_runClient_state_bind, prog_runClient_state_pure]
    exact hiter fuel hvL hi hps hti
  intro k
  induction k with
  | zero => intro s _ _ _ _; exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    intro s hvL₀ hi₀ hps₀ hti₀
    obtain ⟨hfr₁, hu₁, ha₁⟩ := pageUnpermStepBoundedProg_spec hvL₀ hi₀ hps₀ hti₀
    obtain ⟨hi₁, hps_u, _, hti_u, _, _, _⟩ := PageUnpermState.unpermStep_spec.{0} hi₀
    have hstep_st : (Memory.spec 0).clientState s (pageUnpermIterStepProg (L.toCtx, 0)) =
        (Memory.spec 0).clientState s (pageUnpermStepBoundedProg L.toCtx) := by
      unfold pageUnpermIterStepProg StateTransitionSpec.clientState; simp
    have hstep_res : (Memory.spec 0).clientResult s (pageUnpermIterStepProg (L.toCtx, 0)) = 0 := by
      unfold pageUnpermIterStepProg; simp
    set s₁ := (Memory.spec 0).clientState s (pageUnpermStepBoundedProg L.toCtx)
    have hst₁ : extractPagePair L s₁.mem = (extractPageUnperm L s.mem).unpermStep.1.st :=
      congrArg PageUnpermState.st hu₁
    obtain ⟨hfr₂, hu₂, ha₂⟩ := ih (hfr₁.symm ▸ hvL₀) (hu₁.symm ▸ hi₁)
      (hst₁.symm ▸ hps_u.trans hps₀) (hst₁.symm ▸ hti_u.trans_le hti₀)
    dsimp only [PageUnpermState.runUnpermSteps]
    unfold iterate
    rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
    refine ⟨hfr₂.trans hfr₁, ?_, ?_⟩
    · rw [hu₂, hu₁]
    · rw [ha₂, hu₁, ha₁, applySwaps_append]

/-- Raw tail append (`st.rawAppend side`) in `Memory.Prog` (`¬ReadsWidth`). -/
private def pageRawAppendCommitProg :
    PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)),
      ((sb, rs), (th, totI))) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let k_new ← pure ((th + rs) % (4 * pg))
    let res_new ← pure (totI % (8 * pg))
    Memory.write (mb + if sb = 0 then 23 else 24) (rs + 1)
    pageWriteTailResProg ((ctx, (sb, k_new)), res_new)
    pageWriteTailOwnerProg ((ctx, res_new), (sb, k_new))

@[simp] private theorem runClient_frontier_pageRawAppendCommitProg
    (x : PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageRawAppendCommitProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  simp [pageRawAppendCommitProg]

private theorem realizesBounded_pageRawAppendCommit :
    RealizesBounded .exact pageRawAppendCommitProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, ((_, rs), (th, _))) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        rs + 1 < 4 * (PageArenaLayout.ofCtx ctx).pgB ∧
        th < 4 * (PageArenaLayout.ofCtx ctx).pgB)
      (fun _ _ => 0) := by
  have hwtr := realizesBounded_pageWriteTailRes
  have hwto := realizesBounded_pageWriteTailOwner
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, rs⟩, ⟨th, totI⟩⟩⟩
    have hsb_w : Fits w sb := hwords 11
    obtain ⟨hv0, hrs, hth⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageWriteTailResProg] at *
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    have hc1 : (th + rs) % (4 * pg) < 4 * pg := Nat.mod_lt _ (by omega)
    have hc2 : totI % (8 * pg) < 8 * pg := Nat.mod_lt _ (by omega)
    first | exact hv0 | omega)

private def pageRawAppendCheckProg :
    (PageArenaCtx × ℕ) × (ℕ × ((ℕ × ℕ) × ℕ)) → Memory.Prog Unit
  | (((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sb),
      (base, (tc, th)))) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if tc.1 ≤ nc - base then
      if tc.2 ≤ nc - base - tc.1 ∧ th < 4 * pg then do
        let rs ← pure (if sb = 0 then tc.1 else tc.2)
        if rs < 4 * pg - 1 then do
          let totI_w ← pure (base + tc.1 + tc.2)
          pageRawAppendCommitProg (ctx, ((sb, rs), (th, totI_w)))
        else
          pure ()
      else
        pure ()
    else
      pure ()

@[simp] private theorem runClient_frontier_pageRawAppendCheckProg
    (x : (PageArenaCtx × ℕ) × (ℕ × ((ℕ × ℕ) × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageRawAppendCheckProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, ⟨_, ⟨⟨_, _⟩, _⟩⟩⟩
  unfold pageRawAppendCheckProg; dsimp only
  simp only [pure_bind]
  split_ifs <;> simp

private theorem realizesBounded_pageRawAppendCheck :
    RealizesBounded .exact pageRawAppendCheckProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × (ℕ × ((ℕ × ℕ) × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), (base, _)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        base ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hcom := realizesBounded_pageRawAppendCommit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩,
      ⟨base, ⟨⟨tc1, tc2⟩, th⟩⟩⟩
    have hsb_w : Fits w sb := hwords 11
    obtain ⟨hv0, hbase⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, hnc_w, _, _, _, _⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> first | exact hv0 | omega)

private def pageRawAppendProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sideBit) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let fp ← pageReadFullPagesProg mb
    let tc ← pageReadTailCountsProg mb
    let sb ← pure (if sideBit = 0 then 0 else 1)
    let th ← Memory.read (mb + if sb = 0 then 25 else 26)
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then do
        let base ← pure ((fp.1 + fp.2) * pg)
        pageRawAppendCheckProg ((ctx, sb), (base, (tc, th)))
      else
        pure ()
    else
      pure ()

@[simp] private theorem runClient_frontier_pageRawAppendProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageRawAppendProg x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageRawAppendProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg,
    prog_runClient_state_read]
  split_ifs <;> simp

private theorem realizesBounded_pageRawAppend :
    RealizesBounded .exact pageRawAppendProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have hrtc := realizesBounded_pageReadTailCounts
  have hchk := realizesBounded_pageRawAppendCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩
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

/-- Shared post-rebalance clean-state sync for `appendSlot` / `popBackSlot` when
`ph = 1 ∨ (ph = 2 ∧ coff = 0)`. -/
private def pageZeroPhaseRebalanceProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), tickFuel) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    pageMaybeStartJobProg ctx
    pageRunTicksBatchProg (ctx, tickFuel)
    let z0 ← pure 0
    pageWriteCleanProg (mb, (z0, (z0, z0)))

@[simp] private theorem runClient_frontier_pageZeroPhaseRebalanceProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageZeroPhaseRebalanceProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  simp [pageZeroPhaseRebalanceProg]

private theorem realizesBounded_pageZeroPhaseRebalance :
    RealizesBounded .exact pageZeroPhaseRebalanceProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hms := realizesBounded_pageMaybeStartJob
  have hrt := realizesBounded_pageRunTicksBatch
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, tf⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_frontier_pageRunTicksBatchProg] at *
    try simp only [runClient_frontier_pageMaybeStartJobProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

private def pageRebalanceSyncCleanProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), tickFuel), cvp) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    pageMaybeStartJobProg ctx
    pageRunTicksBatchProg (ctx, tickFuel)
    let jk ← Memory.read (mb + 27)
    let q1 ← Memory.read (mb + 22)
    let ph' ← pure (if jk = 0 ∨ 4 ≤ jk then 2 else 1)
    let mvp ← pure (if cvp ≤ q1 then cvp else q1)
    let z0 ← pure 0
    pageWriteCleanProg (mb, (ph', (mvp, z0)))

@[simp] private theorem runClient_frontier_pageRebalanceSyncCleanProg
    (x : (PageArenaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageRebalanceSyncCleanProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, _⟩
  simp [pageRebalanceSyncCleanProg]

private theorem realizesBounded_pageRebalanceSyncClean :
    RealizesBounded .exact pageRebalanceSyncCleanProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hms := realizesBounded_pageMaybeStartJob
  have hrt := realizesBounded_pageRunTicksBatch
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, tf⟩, cvp⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    have hcvp_lt : Fits w cvp := hwords 12
    try simp only [runClient_frontier_pageRunTicksBatchProg] at *
    try simp only [runClient_frontier_pageMaybeStartJobProg] at *
    dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

/-- Deamortized `O(1)` virtual append (`u.appendSlot side` when `tickFuel = 16`,
`RealizesBounded .exact`, `¬ReadsWidth`). -/
def pageAppendBoundedProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sideBit), tickFuel) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let ph ← Memory.read (mb + 18)
    let co ← pageReadCleanPosProg mb
    pageRawAppendProg (ctx, sideBit)
    if ph = 0 then
      pageZeroPhaseRebalanceProg (ctx, tickFuel)
    else if ph = 1 ∨ (ph = 2 ∧ co.2 = 0) then
      pageRebalanceSyncCleanProg ((ctx, tickFuel), co.1)
    else
      pure ()

theorem realizesBounded_pageAppend :
    RealizesBounded .exact pageAppendBoundedProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrcp := realizesBounded_pageReadCleanPos
  have hra := realizesBounded_pageRawAppend
  have hzpr := realizesBounded_pageZeroPhaseRebalance
  have hrsc := realizesBounded_pageRebalanceSyncClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩, tf⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_frontier_pageRawAppendProg] at *
    try simp only [runClient_state_pageReadCleanPosProg] at *
    first | exact hv0 | omega)

private theorem pageRawAppendProg_spec {L : PageArenaLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (hv : (extractPagePair L s.mem).Valid)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems + 1 ≤ L.nCap)
    {side : Bool}
    (hr1 : (extractPagePair L s.mem).tailCount side + 1 < 4 * L.pgB) :
    let u := extractPageUnperm L s.mem
    let s' := (Memory.spec 0).clientState s
      (pageRawAppendProg (L.toCtx, if side then 1 else 0))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = { u with st := u.st.rawAppend side } ∧
    arenaPairAt L s'.mem = arenaPairAt L s.mem := by
  dsimp only
  obtain ⟨hw, _, _, _, _, _, hpg16, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  rw [hust]
  have hps_st : st.pageSize = L.pgB := hps
  have hti_st : st.totalItems + 1 ≤ L.nCap := hti
  have hB : 0 < L.pgB := hps_st ▸ hv.pageSize_pos
  have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq
  have hqb_le : (st.fullPages false + st.fullPages true) * L.pgB ≤ L.nCap := by
    change st.totalPages * L.pgB ≤ L.nCap; omega
  have hq0_le : st.fullPages false ≤ L.nCap / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hq1_le : st.fullPages true ≤ (L.nCap - st.fullPages false * L.pgB) / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hth_lt : st.tailHead side < 4 * L.pgB := hps_st ▸ hv.tailHead_lt side
  refine ⟨by simpa only [StateTransitionSpec.clientState] using
    runClient_frontier_pageRawAppendProg (L.toCtx, if side then 1 else 0) s, ?_⟩
  unfold pageRawAppendProg pageRawAppendCheckProg pageRawAppendCommitProg PagePairState.rawAppend
  dsimp only [PageArenaLayout.toCtx]
  unfold StateTransitionSpec.clientState
  have hsb_1 : (if (if side then 1 else 0) = 0 then 0 else 1) = (if side then 1 else 0) := by
    cases side <;> rfl
  have hth_r : s.mem (L.metaBase + if (if side then 1 else 0) = 0 then 25 else 26) =
      st.tailHead side := by cases side <;> rfl
  have hfp_eq : (Memory.spec 0).clientResult s (pageReadFullPagesProg L.metaBase) =
      (st.fullPages false, st.fullPages true) := pageReadFullPagesProg_eq L s
  have htc_eq : (Memory.spec 0).clientResult s (pageReadTailCountsProg L.metaBase) =
      (st.tailCount false, st.tailCount true) := pageReadTailCountsProg_eq L s
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg,
    hfp_eq, htc_eq, prog_clientResult_read, prog_runClient_state_read, hsb_1, hth_r]
  rw [ite_eq_left hq0_le, ite_eq_left hq1_le]
  have hc2a : st.tailCount false ≤ L.nCap - (st.fullPages false + st.fullPages true) * L.pgB := by
    change st.tailCount false ≤ L.nCap - st.totalPages * L.pgB; omega
  have hc2b : st.tailCount true ≤ L.nCap - (st.fullPages false + st.fullPages true) * L.pgB -
        st.tailCount false ∧ st.tailHead side < 4 * L.pgB :=
    ⟨by change st.tailCount true ≤ L.nCap - st.totalPages * L.pgB - _; omega, hth_lt⟩
  rw [ite_eq_left hc2a, ite_eq_left hc2b]
  have hrs_eq : (if (if side then 1 else 0) = 0 then st.tailCount false
      else st.tailCount true) = st.tailCount side := by cases side <;> rfl
  have hr1_st : st.tailCount side < 4 * L.pgB - 1 := by omega
  rw [hrs_eq, ite_eq_left hr1_st]
  set k_new := (st.tailHead side + st.tailCount side) % (4 * L.pgB)
  set res_new := ((st.fullPages false + st.fullPages true) * L.pgB +
      st.tailCount false + st.tailCount true) % (8 * L.pgB)
  have hk_lt : k_new < 4 * L.pgB := Nat.mod_lt _ (by omega)
  have hr_lt : res_new < 8 * L.pgB := Nat.mod_lt _ (by omega)
  have hc_to : res_new < 8 * L.pgB ∧ k_new < 8 * L.pgB := ⟨hr_lt, by omega⟩
  unfold pageWriteTailResProg pageWriteTailOwnerProg
  dsimp only
  have hsb_4 : (if (if side then 1 else 0) = 0 then 0 else 4 * L.pgB) =
      (if side then 4 * L.pgB else 0) := by cases side <;> rfl
  have h23 : (if (if side then 1 else 0) = 0 then 23 else 24) = (if side then 24 else 23) := by
    cases side <;> rfl
  rw [ite_eq_left hk_lt, ite_eq_left hc_to]
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    prog_runClient_state_write, runClient_state_writePackedCompGenProg, hsb_4, hsb_1, h23]
  obtain ⟨hu3, ha3⟩ := extractPageUnperm_writeTailOwner hw hpg16 ho1 ho2 hm_ib _
    hr_lt (by omega : k_new < 8 * L.pgB) side
  obtain ⟨hu2, ha2⟩ := extractPageUnperm_writeTailRes hw ho1 ho2 hm_ib _ side
    hk_lt (hr_lt.trans (by omega))
  obtain ⟨_, _, _, _, hsc_tc, _⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib s.mem
    (if side then 24 else 23) (st.tailCount side + 1)
  obtain ⟨hu1, ha1⟩ := hsc_tc side rfl
  rw [hu3, hu2, hu1, ha3, ha2, ha1]
  have hkn_eq : k_new = st.ringSlot side (st.tailCount side) := by
    unfold PagePairState.ringSlot; rw [hps_st]
  have hrn_eq : res_new = st.totalItems % (8 * st.pageSize) := by
    dsimp only [res_new]
    unfold PagePairState.totalPages at hti_eq
    rw [hps_st, ← hti_eq]
  rw [hkn_eq, hrn_eq]
  exact ⟨rfl, rfl⟩

private theorem pageRebalanceSyncCleanProg_spec {L : PageArenaLayout} {s_r : Memory.State}
    {u₀ : PageUnpermState} {st_r : PagePairState} {tf slack : ℕ}
    (hvL_r : L.Valid L.w s_r.frontier)
    (hu_r : extractPageUnperm L s_r.mem = { u₀ with st := st_r })
    (hd_ms : PagePairState.DriftInv st_r.maybeStartJob slack)
    (hps_r : st_r.pageSize = L.pgB)
    (hti_r : st_r.totalItems ≤ L.nCap)
    (htc_r : ∀ sc, st_r.tailCount sc < 4 * L.pgB)
    (hmp_r : st_r.totalPages < L.maxPages) :
    let st_fin := (PagePairState.runTicks tf st_r.maybeStartJob).1
    let sws := (PagePairState.runTicks tf st_r.maybeStartJob).2
    let s' := (Memory.spec 0).clientState s_r
      (pageRebalanceSyncCleanProg ((L.toCtx, tf), u₀.cleanVp))
    s'.frontier = s_r.frontier ∧
    extractPageUnperm L s'.mem =
      { st := st_fin
        cleanPhase := if st_fin.job = .idle then 2 else 1
        cleanVp := min u₀.cleanVp (st_fin.fullPages true)
        cleanOff := 0 } ∧
    arenaPairAt L s'.mem = applySwaps sws (arenaPairAt L s_r.mem) := by
  dsimp only
  have ⟨hw, _, _, _, _, _, _, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hvL_r
  have hst_r : extractPagePair L s_r.mem = st_r := congrArg PageUnpermState.st hu_r
  obtain ⟨hfr_m, hu_m, ha_m⟩ := pageMaybeStartJobProg_spec hvL_r
    (fun sc => hst_r.symm ▸ htc_r sc) (hst_r.symm ▸ hps_r) (hst_r.symm ▸ hmp_r)
  set s_m := (Memory.spec 0).clientState s_r (pageMaybeStartJobProg L.toCtx)
  have hst_m : extractPagePair L s_m.mem = st_r.maybeStartJob := by
    have := congrArg PageUnpermState.st hu_m
    dsimp only [extractPageUnperm] at this; rw [this, hst_r]
  have hst_m_u : (extractPageUnperm L s_m.mem).st = st_r.maybeStartJob := hst_m
  have hps_m : (extractPagePair L s_m.mem).pageSize = L.pgB := by
    rw [hst_m]
    have : ∀ x : PagePairState, x.maybeStartJob.pageSize = x.pageSize := fun x => by
      unfold PagePairState.maybeStartJob; cases x.job <;> try rfl
      dsimp only; split_ifs <;> rfl
    rw [this]; exact hps_r
  have hti_m : (extractPagePair L s_m.mem).totalItems ≤ L.nCap := by
    rw [hst_m]
    have : ∀ x : PagePairState, x.maybeStartJob.totalItems = x.totalItems := fun x => by
      unfold PagePairState.maybeStartJob; cases x.job <;> try rfl
      dsimp only; split_ifs <;> rfl
    rw [this]; exact hti_r
  obtain ⟨hfr_t, hu_t, ha_t⟩ := pageRunTicksBatchProg_spec tf
    (hfr_m.symm ▸ hvL_r) (hst_m.symm ▸ hd_ms) hps_m hti_m
  set s_t := (Memory.spec 0).clientState s_m (pageRunTicksBatchProg (L.toCtx, tf))
  set st_fin := (PagePairState.runTicks tf st_r.maybeStartJob).1
  have hu_st_fin : extractPageUnperm L s_t.mem = { u₀ with st := st_fin } := by
    rw [hu_t, hst_m_u, hu_m, hu_r]
  have hjk_fin : (if (Memory.spec 0).clientResult s_t (Memory.read (L.metaBase + 27)) = 0 ∨
      4 ≤ (Memory.spec 0).clientResult s_t (Memory.read (L.metaBase + 27)) then 2
      else 1) = (if st_fin.job = .idle then 2 else 1) := by
    change (if s_t.mem (L.metaBase + 27) = 0 ∨ 4 ≤ s_t.mem (L.metaBase + 27) then 2
      else 1) = _
    have hj_d : st_fin.job = decodePageJob (s_t.mem (L.metaBase + 27))
        (s_t.mem (L.metaBase + 28)) (s_t.mem (L.metaBase + 29)) :=
      (congrArg (fun x => x.st.job) hu_st_fin).symm
    rw [hj_d]; unfold decodePageJob
    split_ifs <;> first | rfl | exfalso; omega | (exfalso; rename_i h; exact h rfl)
  have hq1_fin : (Memory.spec 0).clientResult s_t (Memory.read (L.metaBase + 22)) =
      st_fin.fullPages true := by
    change s_t.mem (L.metaBase + 22) = st_fin.fullPages true
    have := congrArg (fun x => x.st.fullPages true) hu_st_fin
    dsimp only [extractPageUnperm, extractPagePair] at this; exact this
  unfold pageRebalanceSyncCleanProg
  dsimp only [PageArenaLayout.toCtx]
  unfold StateTransitionSpec.clientState
  have hs_m_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s_r
      (pageMaybeStartJobProg
        ((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
          (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap))))) = s_m := rfl
  have hs_t_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s_m
      (pageRunTicksBatchProg
        (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
          (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)), tf)))) = s_t := rfl
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    prog_runClient_state_pure, prog_clientResult_pure,
    hs_m_eq, hs_t_eq, prog_runClient_state_read,
    runClient_frontier_pageWriteCleanProg]
  rw [hjk_fin, hq1_fin]
  have hmin_eq : (if u₀.cleanVp ≤ st_fin.fullPages true then u₀.cleanVp
      else st_fin.fullPages true) = min u₀.cleanVp (st_fin.fullPages true) := rfl
  rw [hmin_eq]
  obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_t
    (if st_fin.job = .idle then 2 else 1) (min u₀.cleanVp (st_fin.fullPages true)) 0
  dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
  refine ⟨hfr_t.trans hfr_m, ?_, ?_⟩
  · rw [hu_cl, hu_st_fin]
  · rw [ha_cl, ha_t, hst_m_u, ha_m]

theorem pageAppendBoundedProg_spec {L : PageArenaLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (hv : (extractPageUnperm L s.mem).Valid)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems + 1 ≤ L.nCap)
    {side : Bool}
    (hside : 0 < (extractPageUnperm L s.mem).cleanPhase → side = true)
    (hph_lt : (extractPageUnperm L s.mem).cleanPhase < 4) :
    let u := extractPageUnperm L s.mem
    let res := u.appendSlot side
    let s' := (Memory.spec 0).clientState s
      (pageAppendBoundedProg ((L.toCtx, if side then 1 else 0), 16))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = res.1 ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  dsimp only
  have ⟨hw, _, _, _, _, hpg32, _, hmp4, _, hnc_mp, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  have hv_u : u.Valid := hv
  have hps_st : st.pageSize = L.pgB := hps
  have hti_st : st.totalItems + 1 ≤ L.nCap := hti
  have hB : 0 < L.pgB := by omega
  have hr1 : st.tailCount side + 1 < 4 * L.pgB := by
    by_cases hp0 : u.cleanPhase = 0
    · have hwb := (hv_u.phase0_wb hp0).1
      have htc_le : 4 * st.tailCount side ≤ 15 * st.pageSize := hwb.tailCount_le side
      rw [hps_st] at htc_le; omega
    · have hp_pos := Nat.pos_of_ne_zero hp0
      have hs_t := hside hp_pos; subst hs_t
      obtain ⟨hf0_u, ht0_u⟩ := hv_u.src_empty hp_pos
      have hf0 : st.fullPages false = 0 := hf0_u
      have ht0 : st.tailCount false = 0 := ht0_u
      have hphi_le : 16 * st.phi ≤ 28 * L.pgB := by
        rcases (by omega : u.cleanPhase = 1 ∨ u.cleanPhase = 2 ∨ u.cleanPhase = 3) with
          h1 | h2 | h3
        · have h_phi : 16 * st.phi ≤ 28 * st.pageSize := (hv_u.phase1_wb h1).1.phi_le
          rwa [hps_st] at h_phi
        · by_cases ho : u.cleanOff = 0
          · have h_phi : 16 * st.phi ≤ 28 * st.pageSize := (hv_u.phase2_zero h2 ho).1.phi_le
            rwa [hps_st] at h_phi
          · obtain ⟨_, _, _, _, h_phi⟩ := hv_u.phase2_pos h2 (Nat.pos_of_ne_zero ho)
            change 16 * st.phi + (st.pageSize - u.cleanOff) / 16 ≤ 25 * st.pageSize at h_phi
            rw [hps_st] at h_phi; omega
        · obtain ⟨_, _, _, _, h_phi⟩ := hv_u.phase3_inv h3
          change 16 * st.phi + (st.tailCount true - u.cleanVp) / 16 ≤ 25 * st.pageSize at h_phi
          rw [hps_st] at h_phi; omega
      unfold PagePairState.phi PagePairState.dev at hphi_le
      rw [hps_st] at hphi_le
      split_ifs at hphi_le <;> omega
  obtain ⟨hfr_r, hu_r, ha_r⟩ := pageRawAppendProg_spec hvL hv_u.valid hps hti hr1
  set s_r := (Memory.spec 0).clientState s
    (pageRawAppendProg (L.toCtx, if side then 1 else 0))
  have hst_r : extractPagePair L s_r.mem = st.rawAppend side :=
    congrArg PageUnpermState.st hu_r
  have hps_r : (extractPagePair L s_r.mem).pageSize = L.pgB := hst_r.symm ▸ hps_st
  have htc_r : ∀ sc, (extractPagePair L s_r.mem).tailCount sc < 4 * L.pgB := fun sc => by
    rw [hst_r]; dsimp only [PagePairState.rawAppend]
    by_cases hss : sc = side
    · subst hss; rw [Function.update_self]; exact hr1
    · rw [Function.update_of_ne hss]; exact hps_st ▸ hv_u.valid.tailCount_lt sc
  have hmp_r : (extractPagePair L s_r.mem).totalPages < L.maxPages := by
    rw [hst_r]
    have hle : st.totalPages * L.pgB ≤ (L.maxPages - 2) * L.pgB := by
      have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq; omega
    have htp_le : st.totalPages ≤ L.maxPages - 2 := (Nat.mul_le_mul_right_iff hB).mp hle
    change st.totalPages < L.maxPages; omega
  unfold pageAppendBoundedProg pageZeroPhaseRebalanceProg
    PageUnpermState.appendSlot PagePairState.stepAppend
  generalize (16 : ℕ) = tf
  dsimp only [PageArenaLayout.toCtx]
  unfold StateTransitionSpec.clientState
  have hph_r : s.mem (L.metaBase + 18) = u.cleanPhase := rfl
  have hco_eq : (Memory.spec 0).clientResult s (pageReadCleanPosProg L.metaBase) =
      (u.cleanVp, u.cleanOff) := pageReadCleanPosProg_eq L s
  have hs_r_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s
      (pageRawAppendProg
        (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
          (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)),
        if side then 1 else 0)))) = s_r := rfl
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    prog_clientResult_read, prog_runClient_state_read,
    runClient_state_pageReadCleanPosProg, hco_eq, hph_r, hs_r_eq]
  by_cases hp0 : u.cleanPhase = 0
  · rw [ite_eq_left hp0, ite_eq_left hp0]
    have hwb : st.WellBalanced := (hv_u.phase0_wb hp0).1
    obtain ⟨hd_ms, _, _, hti_r_eq, _, _⟩ := PagePairState.rawAppend_driftInv hwb side
    obtain ⟨hfr_m, hu_m, ha_m⟩ := pageMaybeStartJobProg_spec (hfr_r.symm ▸ hvL) htc_r hps_r hmp_r
    set s_m := (Memory.spec 0).clientState s_r (pageMaybeStartJobProg L.toCtx)
    have hst_m : extractPagePair L s_m.mem = (st.rawAppend side).maybeStartJob := by
      have := congrArg PageUnpermState.st hu_m
      dsimp only [extractPageUnperm] at this; rw [this, hst_r]
    have hps_m : (extractPagePair L s_m.mem).pageSize = L.pgB := by
      rw [hst_m]
      have : ∀ x : PagePairState, x.maybeStartJob.pageSize = x.pageSize := fun x => by
        unfold PagePairState.maybeStartJob; cases x.job <;> try rfl
        dsimp only; split_ifs <;> rfl
      rw [this]; exact hps_st
    have hti_m : (extractPagePair L s_m.mem).totalItems ≤ L.nCap := by
      rw [hst_m]
      have : ∀ x : PagePairState, x.maybeStartJob.totalItems = x.totalItems := fun x => by
        unfold PagePairState.maybeStartJob; cases x.job <;> try rfl
        dsimp only; split_ifs <;> rfl
      rw [this, hti_r_eq]; exact hti_st
    obtain ⟨hfr_t, hu_t, ha_t⟩ := pageRunTicksBatchProg_spec tf
      (hfr_m.symm ▸ hfr_r.symm ▸ hvL) (hst_m.symm ▸ hd_ms) hps_m hti_m
    set s_t := (Memory.spec 0).clientState s_m (pageRunTicksBatchProg (L.toCtx, tf))
    have hs_m_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s_r
        (pageMaybeStartJobProg
          ((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
            (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap))))) = s_m := rfl
    have hs_t_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s_m
        (pageRunTicksBatchProg
          (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
            (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)), tf)))) = s_t := rfl
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      hs_m_eq, hs_t_eq, runClient_frontier_pageWriteCleanProg]
    obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_t 0 0 0
    dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
    refine ⟨hfr_t.trans (hfr_m.trans hfr_r), ?_⟩
    rw [hu_cl, hu_t, hu_m, hu_r, ha_cl, ha_t, ha_m, ha_r]
    have hst_m_u : (extractPageUnperm L s_m.mem).st = (u.st.rawAppend side).maybeStartJob := hst_m
    rw [hst_m_u]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hp0, ite_eq_right hp0]
    by_cases hwb_br : u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0)
    · rw [ite_eq_left hwb_br, ite_eq_left hwb_br]
      have hwb : st.WellBalanced := by
        rcases hwb_br with h1 | ⟨h2, h0⟩
        · exact (hv_u.phase1_wb h1).1
        · exact (hv_u.phase2_zero h2 h0).1
      obtain ⟨hd_ms, _, _, hti_r_eq, _, _⟩ := PagePairState.rawAppend_driftInv hwb side
      have hu_r' : extractPageUnperm L s_r.mem = { u with st := st.rawAppend side } :=
        hust ▸ hu_r
      obtain ⟨hfr_sc, hu_sc, ha_sc⟩ := pageRebalanceSyncCleanProg_spec (tf := tf)
        (hfr_r.symm ▸ hvL) hu_r' hd_ms (hst_r ▸ hps_r) (hti_r_eq.trans_le hti_st)
        (fun sc => hst_r ▸ htc_r sc) (hst_r ▸ hmp_r)
      exact ⟨hfr_sc.trans hfr_r, hust ▸ hu_sc, hust ▸ (ha_sc.trans (congrArg _ ha_r))⟩
    · rw [ite_eq_right hwb_br, ite_eq_right hwb_br]
      simp only [prog_runClient_state_pure]
      rw [hust] at hu_r
      exact ⟨hfr_r, hu_r, ha_r.trans (applySwaps_nil _).symm⟩

/-- Raw tail popBack (`st.rawPopBack side`) in `Memory.Prog` (`¬ReadsWidth`). -/
private def pageRawPopBackCommitProg :
    PageArenaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), ((sb, rs), totI)) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let rm1 ← pure (rs - 1)
    let p₁ ← pageTailPhysBoundedProg (ctx, (sb, rm1))
    let p₂ ← pure (totI - 1)
    pageSwapTailSlotsProg (ctx, (p₁, p₂))
    Memory.write (mb + if sb = 0 then 23 else 24) rm1

@[simp] private theorem runClient_frontier_pageRawPopBackCommitProg
    (x : PageArenaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageRawPopBackCommitProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, ⟨⟨_, _⟩, _⟩⟩
  simp [pageRawPopBackCommitProg]

private theorem realizesBounded_pageRawPopBackCommit :
    RealizesBounded .exact pageRawPopBackCommitProg
      (WordEncoding.encode (α := PageArenaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, ((_, rs), totI)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧ 0 < rs ∧ 0 < totI)
      (fun _ _ => 0) := by
  have htp := realizesBounded_pageTailPhys
  have hsts := realizesBounded_pageSwapTailSlots
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩,
      ⟨⟨sb, rs⟩, totI⟩⟩
    have hsb_w : Fits w sb := hwords 11
    obtain ⟨hv0, hrs0, htot0⟩ := h
    have ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := hv0
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    have hrs_w : Fits w rs := hwords 12
    have htotI_w : Fits w totI := hwords 13
    try simp only [runClient_state_pageTailPhysBoundedProg] at *
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    first | exact hv0 | omega)

private def pageRawPopBackCheckProg :
    (PageArenaCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sb), (base, tc))) =>
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    if tc.1 ≤ nc - base then
      if tc.2 ≤ nc - base - tc.1 then do
        let totI ← pure (base + tc.1 + tc.2)
        let rs ← pure (if sb = 0 then tc.1 else tc.2)
        if 0 < rs ∧ 0 < totI then
          pageRawPopBackCommitProg (ctx, ((sb, rs), totI))
        else
          pure ()
      else
        pure ()
    else
      pure ()

@[simp] private theorem runClient_frontier_pageRawPopBackCheckProg
    (x : (PageArenaCtx × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pageRawPopBackCheckProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold pageRawPopBackCheckProg; dsimp only
  simp only [pure_bind]
  split_ifs <;> simp

private theorem realizesBounded_pageRawPopBackCheck :
    RealizesBounded .exact pageRawPopBackCheckProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), (base, _)) s =>
        (PageArenaLayout.ofCtx ctx).Valid w s.frontier ∧
        base ≤ (PageArenaLayout.ofCtx ctx).nCap)
      (fun _ _ => 0) := by
  have hcom := realizesBounded_pageRawPopBackCommit
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩,
      ⟨base, ⟨tc1, tc2⟩⟩⟩
    have hsb_w : Fits w sb := hwords 11
    obtain ⟨hv0, hbase⟩ := h
    have ⟨hw, hwv, _, _, _, _, _, _, _, _, hnc_w, _, _, _, _⟩ := hv0
    subst hwv
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    (try split_ifs at *) <;> first | exact hv0 | omega)

private def pageRawPopBackProg : PageArenaCtx × ℕ → Memory.Prog Unit
  | (((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sideBit) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let fp ← pageReadFullPagesProg mb
    let tc ← pageReadTailCountsProg mb
    let sb ← pure (if sideBit = 0 then 0 else 1)
    if fp.1 ≤ nc / pg then
      if fp.2 ≤ (nc - fp.1 * pg) / pg then do
        let base ← pure ((fp.1 + fp.2) * pg)
        pageRawPopBackCheckProg ((ctx, sb), (base, tc))
      else
        pure ()
    else
      pure ()

@[simp] private theorem runClient_frontier_pageRawPopBackProg
    (x : PageArenaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (pageRawPopBackProg x)).2.1.frontier =
      s.frontier := by
  rcases x with ⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, _⟩⟩, _⟩
  unfold pageRawPopBackProg; dsimp only
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg]
  split_ifs <;> simp

private theorem realizesBounded_pageRawPopBack :
    RealizesBounded .exact pageRawPopBackProg
      (WordEncoding.encode (α := PageArenaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrfp := realizesBounded_pageReadFullPages
  have hrtc := realizesBounded_pageReadTailCounts
  have hchk := realizesBounded_pageRawPopBackCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, hmp4, _, hnc_w, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try simp only [runClient_state_pageReadTailCountsProg] at *
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

/-- Deamortized `O(1)` virtual popBack (`u.popBackSlot side` when `tickFuel = 16`,
`RealizesBounded .exact`, `¬ReadsWidth`). -/
private def pagePopBackTailCleanProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((mb, ph), (cvp, coff)) =>
    if ph = 2 then do
      let c2 ← pure 2
      pageWriteCleanProg (mb, (c2, (cvp, coff)))
    else do
      let r1 ← Memory.read (mb + 24)
      let mvp ← pure (if cvp ≤ r1 then cvp else r1)
      let z0 ← pure 0
      pageWriteCleanProg (mb, (ph, (mvp, z0)))

@[simp] private theorem runClient_frontier_pagePopBackTailCleanProg
    (x : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s
      (pagePopBackTailCleanProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold pagePopBackTailCleanProg; dsimp only; split_ifs <;> simp

private theorem realizesBounded_pagePopBackTailClean :
    RealizesBounded .exact pagePopBackTailCleanProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mb, _), _) s => 32 < 2 ^ w ∧ mb + 32 ≤ s.frontier) (fun _ _ => 0) := by
  have hwcl := realizesBounded_pageWriteClean
  realize
  all_goals (
    rcases d with ⟨⟨mb, ph⟩, ⟨cvp, coff⟩⟩
    obtain ⟨hw32, hfr⟩ := h
    have hr1 := hmem.2 (mb + 24)
    have hfr_w := hmem.1
    have hph_w : Fits w ph := hwords 1
    have hcvp_w : Fits w cvp := hwords 2
    have hcoff_w : Fits w coff := hwords 3
    try dsimp only [Fits] at *
    omega)

/-- Deamortized `O(1)` virtual pop-back (`u.popBackSlot side` when `tickFuel = 16`,
`RealizesBounded .exact`, `¬ReadsWidth`). -/
def pagePopBackBoundedProg : (PageArenaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)), sideBit), tickFuel) => do
    let ctx := ((((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))
    let ph ← Memory.read (mb + 18)
    let co ← pageReadCleanPosProg mb
    pageRawPopBackProg (ctx, sideBit)
    if ph = 0 then
      pageZeroPhaseRebalanceProg (ctx, tickFuel)
    else if ph = 1 ∨ (ph = 2 ∧ co.2 = 0) then
      pageRebalanceSyncCleanProg ((ctx, tickFuel), co.1)
    else
      pagePopBackTailCleanProg ((mb, ph), co)

theorem realizesBounded_pagePopBack :
    RealizesBounded .exact pagePopBackBoundedProg
      (WordEncoding.encode (α := (PageArenaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (PageArenaLayout.ofCtx ctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrcp := realizesBounded_pageReadCleanPos
  have hrp := realizesBounded_pageRawPopBack
  have hzpr := realizesBounded_pageZeroPhaseRebalance
  have hrsc := realizesBounded_pageRebalanceSyncClean
  have hptc := realizesBounded_pagePopBackTailClean
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩, sb⟩, tf⟩
    have hv0 := h
    obtain ⟨hw, hwv, hpb, _, _, hpg32, hpg16, _, _, _, _, ho1, ho2, hm_ib, hib_fr⟩ := h
    subst hwv
    have hpow : 2 ^ pb ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hpb
    have hpg_w : 16 * pg < 2 ^ w := lt_of_lt_of_le hpg16 hpow
    have hfr_w := hmem.1
    try dsimp only [Fits, PageArenaLayout.ofCtx] at *
    try simp only [runClient_frontier_pageRawPopBackProg] at *
    try simp only [runClient_state_pageReadCleanPosProg] at *
    first | exact hv0 | omega)

private theorem pageRawPopBackProg_spec {L : PageArenaLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (hv : (extractPagePair L s.mem).Valid)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap)
    {side : Bool}
    (hr_pos : 0 < (extractPagePair L s.mem).tailCount side) :
    let u := extractPageUnperm L s.mem
    let res := u.st.rawPopBack side
    let s' := (Memory.spec 0).clientState s
      (pageRawPopBackProg (L.toCtx, if side then 1 else 0))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = { u with st := res.1 } ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  dsimp only
  have ⟨hw, _, _, _, _, _, _, _, _, _, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  rw [hust]
  have hps_st : st.pageSize = L.pgB := hps
  have hti_st : st.totalItems ≤ L.nCap := hti
  have hB : 0 < L.pgB := hps_st ▸ hv.pageSize_pos
  have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq
  have htot_pos : 0 < st.totalItems := by
    have hr_pos_st : 0 < st.tailCount side := hr_pos
    cases side <;> omega
  have hqb_le : (st.fullPages false + st.fullPages true) * L.pgB ≤ L.nCap := by
    change st.totalPages * L.pgB ≤ L.nCap; omega
  have hq0_le : st.fullPages false ≤ L.nCap / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  have hq1_le : st.fullPages true ≤ (L.nCap - st.fullPages false * L.pgB) / L.pgB :=
    (Nat.le_div_iff_mul_le hB).mpr (by rw [Nat.add_mul] at hqb_le; omega)
  refine ⟨by simpa only [StateTransitionSpec.clientState] using
    runClient_frontier_pageRawPopBackProg (L.toCtx, if side then 1 else 0) s, ?_⟩
  unfold pageRawPopBackProg pageRawPopBackCheckProg pageRawPopBackCommitProg
    PagePairState.rawPopBack
  dsimp only [PageArenaLayout.toCtx]
  unfold StateTransitionSpec.clientState
  have hsb_1 : (if (if side then 1 else 0) = 0 then 0 else 1) = (if side then 1 else 0) := by
    cases side <;> rfl
  have hfp_eq : (Memory.spec 0).clientResult s (pageReadFullPagesProg L.metaBase) =
      (st.fullPages false, st.fullPages true) := pageReadFullPagesProg_eq L s
  have htc_eq : (Memory.spec 0).clientResult s (pageReadTailCountsProg L.metaBase) =
      (st.tailCount false, st.tailCount true) := pageReadTailCountsProg_eq L s
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    runClient_state_pageReadFullPagesProg, runClient_state_pageReadTailCountsProg,
    hfp_eq, htc_eq, hsb_1]
  rw [ite_eq_left hq0_le, ite_eq_left hq1_le]
  have hc2a : st.tailCount false ≤ L.nCap - (st.fullPages false + st.fullPages true) * L.pgB := by
    change st.tailCount false ≤ L.nCap - st.totalPages * L.pgB; omega
  have hc2b : st.tailCount true ≤ L.nCap - (st.fullPages false + st.fullPages true) * L.pgB -
      st.tailCount false := by
    change st.tailCount true ≤ L.nCap - st.totalPages * L.pgB - _; omega
  rw [ite_eq_left hc2a, ite_eq_left hc2b]
  have hrs_eq : (if (if side then 1 else 0) = 0 then st.tailCount false
      else st.tailCount true) = st.tailCount side := by cases side <;> rfl
  have htot_sum : (st.fullPages false + st.fullPages true) * L.pgB +
      st.tailCount false + st.tailCount true = st.totalItems := by
    unfold PagePairState.totalPages at hti_eq; exact hti_eq.symm
  have hr_pos_st : 0 < st.tailCount side := hr_pos
  have hc3 : 0 < st.tailCount side ∧ 0 < st.totalItems := ⟨hr_pos_st, htot_pos⟩
  rw [hrs_eq, htot_sum, ite_eq_left hc3]
  have hp₁_eq : (Memory.spec 0).clientResult s
      (pageTailPhysBoundedProg (L.toCtx, (if side then 1 else 0, st.tailCount side - 1))) =
      st.tailPhys side (st.tailCount side - 1) :=
    pageTailPhysBoundedProg_eq hv hps hti side (Nat.sub_lt hr_pos Nat.one_pos)
  dsimp only [PageArenaLayout.toCtx] at hp₁_eq
  have hp₁_lo : st.totalPages * L.pgB ≤ st.tailPhys side (st.tailCount side - 1) :=
    hps_st ▸ le_physOfRes _ _ _
  have hp₁_hi : st.tailPhys side (st.tailCount side - 1) < st.totalItems :=
    hv.tail_lt side _ (Nat.sub_lt hr_pos Nat.one_pos)
  have hp₂_lo : st.totalPages * L.pgB ≤ st.totalItems - 1 := by
    unfold PagePairState.totalPages at hti_eq ⊢; cases side <;> omega
  have hp₂_hi : st.totalItems - 1 < st.totalItems := Nat.sub_lt htot_pos Nat.one_pos
  simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
    runClient_state_pageTailPhysBoundedProg, hp₁_eq]
  obtain ⟨_, hu_sw, ha_sw⟩ := pageSwapTailSlotsProg_spec hvL hv hps hti
    hp₁_lo hp₁_hi hp₂_lo hp₂_hi
  set s_sw := (Memory.spec 0).clientState s
    (pageSwapTailSlotsProg
      (L.toCtx, (st.tailPhys side (st.tailCount side - 1), st.totalItems - 1)))
  have hs_sw_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s
      (pageSwapTailSlotsProg
        (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
          (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)),
        (st.tailPhys side (st.tailCount side - 1), st.totalItems - 1))))) = s_sw := rfl
  have h23 : (if (if side then 1 else 0) = 0 then 23 else 24) = (if side then 24 else 23) := by
    cases side <;> rfl
  simp only [hs_sw_eq, prog_runClient_state_write, h23]
  obtain ⟨_, _, _, _, hsc_tc, _⟩ := extractPageUnperm_writeScalar hw ho1 ho2 hm_ib s_sw.mem
    (if side then 24 else 23) (st.tailCount side - 1)
  obtain ⟨hu_tc, ha_tc⟩ := hsc_tc side rfl
  rw [hu_tc, hu_sw, ha_tc, ha_sw]
  exact ⟨rfl, rfl⟩

theorem pagePopBackBoundedProg_spec {L : PageArenaLayout} {s : Memory.State}
    (hvL : L.Valid L.w s.frontier)
    (hv : (extractPageUnperm L s.mem).Valid)
    (hps : (extractPagePair L s.mem).pageSize = L.pgB)
    (hti : (extractPagePair L s.mem).totalItems ≤ L.nCap)
    {side : Bool}
    (hpos : 0 < (extractPagePair L s.mem).virtLen side)
    (hside : 0 < (extractPageUnperm L s.mem).cleanPhase → side = true)
    (hph_lt : (extractPageUnperm L s.mem).cleanPhase < 4) :
    let u := extractPageUnperm L s.mem
    let res := u.popBackSlot side
    let s' := (Memory.spec 0).clientState s
      (pagePopBackBoundedProg ((L.toCtx, if side then 1 else 0), 16))
    s'.frontier = s.frontier ∧
    extractPageUnperm L s'.mem = res.1 ∧
    arenaPairAt L s'.mem = applySwaps res.2 (arenaPairAt L s.mem) := by
  dsimp only
  have ⟨hw, _, _, _, _, hpg32, _, hmp4, _, hnc_mp, _, ho1, ho2, hm_ib, _⟩ := hvL
  set st := extractPagePair L s.mem
  set u := extractPageUnperm L s.mem
  have hust : u.st = st := rfl
  have hv_u : u.Valid := hv
  have hps_st : st.pageSize = L.pgB := hps
  have hti_st : st.totalItems ≤ L.nCap := hti
  have hpos_st : 0 < st.virtLen side := hpos
  have hB : 0 < L.pgB := by omega
  have hr_pos : 0 < st.tailCount side := by
    by_cases hp0 : u.cleanPhase = 0
    · exact (hv_u.phase0_wb hp0).1.tailCount_pos_of_virtLen hpos_st
    · have hp_pos := Nat.pos_of_ne_zero hp0
      have hs_t := hside hp_pos; subst hs_t
      by_cases hq : 0 < st.fullPages true
      · have hphi_le : 16 * st.phi ≤ 28 * L.pgB := by
          rcases (by omega : u.cleanPhase = 1 ∨ u.cleanPhase = 2 ∨ u.cleanPhase = 3) with
            h1 | h2 | h3
          · have h_phi : 16 * st.phi ≤ 28 * st.pageSize := (hv_u.phase1_wb h1).1.phi_le
            rwa [hps_st] at h_phi
          · by_cases ho : u.cleanOff = 0
            · have h_phi : 16 * st.phi ≤ 28 * st.pageSize := (hv_u.phase2_zero h2 ho).1.phi_le
              rwa [hps_st] at h_phi
            · obtain ⟨_, _, _, _, h_phi⟩ := hv_u.phase2_pos h2 (Nat.pos_of_ne_zero ho)
              change 16 * st.phi + (st.pageSize - u.cleanOff) / 16 ≤ 25 * st.pageSize at h_phi
              rw [hps_st] at h_phi; omega
          · obtain ⟨_, _, _, _, h_phi⟩ := hv_u.phase3_inv h3
            change 16 * st.phi + (st.tailCount true - u.cleanVp) / 16 ≤ 25 * st.pageSize at h_phi
            rw [hps_st] at h_phi; omega
        unfold PagePairState.phi PagePairState.dev at hphi_le
        rw [hps_st] at hphi_le; simp only [hq, ↓reduceIte] at hphi_le; omega
      · have hq0 : st.fullPages true = 0 := by omega
        unfold PagePairState.virtLen at hpos_st; rw [hq0, zero_mul, zero_add] at hpos_st
        exact hpos_st
  obtain ⟨hfr_r, hu_r, ha_r⟩ := pageRawPopBackProg_spec hvL hv_u.valid hps hti hr_pos
  set s_r := (Memory.spec 0).clientState s
    (pageRawPopBackProg (L.toCtx, if side then 1 else 0))
  have hst_r : extractPagePair L s_r.mem = (st.rawPopBack side).1 :=
    congrArg PageUnpermState.st hu_r
  obtain ⟨hps_sw, hfp_sw, htc_sw, _⟩ := swapTailSlots_meta_eq st
    (st.tailPhys side (st.tailCount side - 1)) (st.totalItems - 1)
  have hps_r : (extractPagePair L s_r.mem).pageSize = L.pgB := by
    rw [hst_r]; dsimp only [PagePairState.rawPopBack]; exact hps_sw.trans hps_st
  have htc_r : ∀ sc, (extractPagePair L s_r.mem).tailCount sc < 4 * L.pgB := fun sc => by
    rw [hst_r]; dsimp only [PagePairState.rawPopBack]
    have h0 : st.tailCount sc < 4 * L.pgB := hps_st ▸ hv_u.valid.tailCount_lt sc
    by_cases hss : sc = side
    · subst hss; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hss, htc_sw]; exact h0
  have hmp_r : (extractPagePair L s_r.mem).totalPages < L.maxPages := by
    rw [hst_r]; dsimp only [PagePairState.rawPopBack]
    have hle : st.totalPages * L.pgB ≤ (L.maxPages - 2) * L.pgB := by
      have hti_eq := st.totalItems_eq; rw [hps_st] at hti_eq; omega
    have htp_le : st.totalPages ≤ L.maxPages - 2 := (Nat.mul_le_mul_right_iff hB).mp hle
    unfold PagePairState.totalPages at htp_le ⊢; dsimp only; rw [hfp_sw]; omega
  unfold pagePopBackBoundedProg pageZeroPhaseRebalanceProg pagePopBackTailCleanProg
    PageUnpermState.popBackSlot PagePairState.stepPopBack PagePairState.stepPopBackTicks
  generalize (16 : ℕ) = tf
  dsimp only [PageArenaLayout.toCtx]
  unfold StateTransitionSpec.clientState
  have hph_r : s.mem (L.metaBase + 18) = u.cleanPhase := rfl
  have hco_eq : (Memory.spec 0).clientResult s (pageReadCleanPosProg L.metaBase) =
      (u.cleanVp, u.cleanOff) := pageReadCleanPosProg_eq L s
  have hs_r_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s
      (pageRawPopBackProg
        (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
          (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)),
        if side then 1 else 0)))) = s_r := rfl
  simp only [StateTransitionSpec.clientState, pure_bind, prog_runClient_state_bind,
    prog_clientResult_read, prog_runClient_state_read,
    runClient_state_pageReadCleanPosProg, hco_eq, hph_r, hs_r_eq]
  by_cases hp0 : u.cleanPhase = 0
  · rw [ite_eq_left hp0, ite_eq_left hp0]
    have hwb : st.WellBalanced := (hv_u.phase0_wb hp0).1
    obtain ⟨hd_ms, _, _, _, hti_r_eq, _, _, _⟩ := PagePairState.rawPopBack_driftInv.{0} hwb hpos_st
    obtain ⟨hfr_m, hu_m, ha_m⟩ := pageMaybeStartJobProg_spec (hfr_r.symm ▸ hvL) htc_r hps_r hmp_r
    set s_m := (Memory.spec 0).clientState s_r (pageMaybeStartJobProg L.toCtx)
    have hst_m : extractPagePair L s_m.mem = (st.rawPopBack side).1.maybeStartJob := by
      have := congrArg PageUnpermState.st hu_m
      dsimp only [extractPageUnperm] at this; rw [this, hst_r]
    have hps_m : (extractPagePair L s_m.mem).pageSize = L.pgB := by
      rw [hst_m]
      have : ∀ x : PagePairState, x.maybeStartJob.pageSize = x.pageSize := fun x => by
        unfold PagePairState.maybeStartJob; cases x.job <;> try rfl
        dsimp only; split_ifs <;> rfl
      rw [this]; exact hst_r ▸ hps_r
    have hti_m : (extractPagePair L s_m.mem).totalItems ≤ L.nCap := by
      rw [hst_m]
      have : ∀ x : PagePairState, x.maybeStartJob.totalItems = x.totalItems := fun x => by
        unfold PagePairState.maybeStartJob; cases x.job <;> try rfl
        dsimp only; split_ifs <;> rfl
      rw [this, hti_r_eq]; omega
    obtain ⟨hfr_t, hu_t, ha_t⟩ := pageRunTicksBatchProg_spec tf
      (hfr_m.symm ▸ hfr_r.symm ▸ hvL) (hst_m.symm ▸ hd_ms) hps_m hti_m
    set s_t := (Memory.spec 0).clientState s_m (pageRunTicksBatchProg (L.toCtx, tf))
    have hs_m_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s_r
        (pageMaybeStartJobProg
          ((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
            (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap))))) = s_m := rfl
    have hs_t_eq : Prod.fst (Prod.snd ((Memory.spec 0).runClient s_m
        (pageRunTicksBatchProg
          (((((L.metaBase, L.offDir), (L.offTail, L.ptrB)), ((L.w, L.pgB),
            (L.maxPages, L.itemBase))), ((L.qBits, L.vBits), L.nCap)), tf)))) = s_t := rfl
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind, hs_m_eq, hs_t_eq,
      runClient_frontier_pageWriteCleanProg]
    obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_t 0 0 0
    dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
    refine ⟨hfr_t.trans (hfr_m.trans hfr_r), ?_⟩
    rw [hu_cl, hu_t, hu_m, hu_r, ha_cl, ha_t, ha_m, ha_r, applySwaps_append]
    have hst_m_u : (extractPageUnperm L s_m.mem).st = (u.st.rawPopBack side).1.maybeStartJob :=
      hst_m
    rw [hst_m_u]
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right hp0, ite_eq_right hp0]
    by_cases hwb_br : u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0)
    · rw [ite_eq_left hwb_br, ite_eq_left hwb_br]
      have hwb : st.WellBalanced := by
        rcases hwb_br with h1 | ⟨h2, h0⟩
        · exact (hv_u.phase1_wb h1).1
        · exact (hv_u.phase2_zero h2 h0).1
      obtain ⟨hd_ms, _, _, _, hti_r_eq, _, _, _⟩ :=
        PagePairState.rawPopBack_driftInv.{0} hwb hpos_st
      obtain ⟨hfr_sc, hu_sc, ha_sc⟩ := pageRebalanceSyncCleanProg_spec (tf := tf)
        (hfr_r.symm ▸ hvL) hu_r hd_ms (hst_r ▸ hps_r) (hti_r_eq.trans_le (by omega))
        (fun sc => hst_r ▸ htc_r sc) (hst_r ▸ hmp_r)
      refine ⟨hfr_sc.trans hfr_r, hust ▸ hu_sc, ?_⟩
      rw [ha_sc, ha_r, applySwaps_append]
    · rw [ite_eq_right hwb_br, ite_eq_right hwb_br]
      by_cases hp2 : u.cleanPhase = 2
      · rw [ite_eq_left hp2, ite_eq_left hp2]
        (try dsimp only)
        simp only [runClient_frontier_pageWriteCleanProg]
        obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_r
          2 u.cleanVp u.cleanOff
        dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
        refine ⟨hfr_r, ?_⟩
        rw [hu_cl, hu_r, ha_cl, ha_r]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hp2, ite_eq_right hp2]
        have hr1_eq : s_r.mem (L.metaBase + 24) = (st.rawPopBack side).1.tailCount true := by
          have := congrArg (fun x => x.st.tailCount true) hu_r
          dsimp only [extractPageUnperm, extractPagePair] at this; exact this
        simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
          prog_clientResult_read, prog_runClient_state_read,
          runClient_frontier_pageWriteCleanProg, hr1_eq]
        have hmin_eq : (if u.cleanVp ≤ (st.rawPopBack side).1.tailCount true then u.cleanVp
            else (st.rawPopBack side).1.tailCount true) =
            min u.cleanVp ((st.rawPopBack side).1.tailCount true) := rfl
        rw [hmin_eq]
        obtain ⟨hu_cl, ha_cl⟩ := extractPageUnperm_pageWriteCleanProg hw ho1 ho2 hm_ib s_r
          u.cleanPhase (min u.cleanVp ((st.rawPopBack side).1.tailCount true)) 0
        dsimp only [StateTransitionSpec.clientState] at hu_cl ha_cl
        refine ⟨hfr_r, ?_⟩
        rw [hu_cl, hu_r, ha_cl, ha_r]
        exact ⟨rfl, rfl⟩


/-! ## Frame and `memoryCost` Bounds -/

private theorem pageWriteOwnerVpOnly_frame {L : PageArenaLayout} (hw : 0 < L.w) (P vp : ℕ) :
    BoundedFrameProg L.OwnsAddr 4 (pageWriteOwnerVpOnlyProg ((L.toCtx, P), vp)) := by
  unfold pageWriteOwnerVpOnlyProg; dsimp only [PageArenaLayout.toCtx]
  refine BoundedFrameProg.ite_prog (P < L.maxPages) (fun hP => ?_)
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  exact BoundedFrameProg.writePackedComp_prog hw (by omega : 4 * P + 3 < 4 * L.maxPages)
    (fun addr hlo hhi => Or.inl (Or.inr (Or.inl ⟨hlo, hhi⟩)))

theorem pageBeginUnpermBoundedProg_frame (L : PageArenaLayout) :
    BoundedFrameProg L.OwnsAddr 10 (pageBeginUnpermBoundedProg L.toCtx) := by
  unfold pageBeginUnpermBoundedProg; dsimp only [PageArenaLayout.toCtx]
  simp only [pure_bind]
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun ph =>
    BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
    BoundedFrameProg.bind_prog (pageReadTailCounts_frame L) fun tc =>
    BoundedFrameProg.ite_prog _
      (fun _ => BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
        pageWriteClean_frame L _)
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

private theorem pageUnpermPhase1_frame {L : PageArenaLayout} (hw : 0 < L.w) (cvp : ℕ) :
    BoundedFrameProg L.OwnsAddr 90 (pageUnpermPhase1Prog (L.toCtx, cvp)) := by
  have ht1 : BoundedFrameProg L.OwnsAddr 85 (pageUnpermPhase1TickProg (L.toCtx, cvp)) := by
    unfold pageUnpermPhase1TickProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageTick_frame hw) fun _ =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  unfold pageUnpermPhase1Prog; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun jk =>
    BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun q1 =>
    BoundedFrameProg.ite_prog (jk = 0 ∨ 4 ≤ jk)
      (fun _ => (pageWriteClean_frame L _).mono (fun _ h => h) (by omega))
      (fun _ => ht1)).mono (fun _ h => h) (by omega)

private theorem pageUnpermPhase2Zero_frame {L : PageArenaLayout} (hw : 0 < L.w) (cvp q1 : ℕ) :
    BoundedFrameProg L.OwnsAddr 32 (pageUnpermPhase2ZeroProg (L.toCtx, (cvp, q1))) := by
  have hsw : ∀ pCur, BoundedFrameProg L.OwnsAddr 28
      (pageUnpermPhase2ZeroSwapProg (L.toCtx, (cvp, pCur))) := fun pCur => by
    unfold pageUnpermPhase2ZeroSwapProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageSwapPhys_frame hw _ _) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  unfold pageUnpermPhase2ZeroProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  dsimp only [PageArenaLayout.toCtx] at hsw
  exact BoundedFrameProg.ite_prog (q1 ≤ cvp)
    (fun _ => (pageWriteClean_frame L _).mono (fun _ h => h) (by omega)) fun _ =>
    (BoundedFrameProg.bind_prog (pageReadPageOf_frame L 1 cvp) fun pCur =>
      BoundedFrameProg.ite_prog (pCur = cvp)
        (fun _ => (pageWriteClean_frame L _).mono (fun _ h => h) (by omega)) fun _ =>
      BoundedFrameProg.ite_prog (pCur < q1) (fun _ => hsw pCur)
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
      (fun _ h => h) (by omega)

private theorem pageUnpermPhase2Mid_frame {L : PageArenaLayout} (hw : 0 < L.w) (cvp coff q1 : ℕ) :
    BoundedFrameProg L.OwnsAddr 32 (pageUnpermPhase2MidProg (L.toCtx, ((cvp, coff), q1))) := by
  have hsw : ∀ pCur, BoundedFrameProg L.OwnsAddr 28
      (pageUnpermPhase2MidSwapProg (L.toCtx, ((cvp, coff), pCur))) := fun pCur => by
    unfold pageUnpermPhase2MidSwapProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageSwapPhys_frame hw _ _) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  unfold pageUnpermPhase2MidProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  dsimp only [PageArenaLayout.toCtx] at hsw
  exact BoundedFrameProg.ite_prog (cvp < q1)
    (fun _ => (BoundedFrameProg.bind_prog (pageReadPageOf_frame L 1 cvp) fun pCur =>
      BoundedFrameProg.ite_prog (pCur < q1) (fun _ => hsw pCur)
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
      (fun _ h => h) (by omega))
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))

private theorem pageUnpermPhase2End_frame {L : PageArenaLayout} (hw : 0 < L.w) (cvp q1 : ℕ) :
    BoundedFrameProg L.OwnsAddr 50 (pageUnpermPhase2EndProg (L.toCtx, (cvp, q1))) := by
  have hccd : ∀ pCur vpO, BoundedFrameProg L.OwnsAddr 16
      (pageCommitCleanDirProg (L.toCtx, (cvp, (pCur, vpO)))) := fun pCur vpO => by
    unfold pageCommitCleanDirProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact BoundedFrameProg.bind_prog (pageWritePageOf_frame hw 1 vpO pCur) fun _ =>
      BoundedFrameProg.bind_prog (pageWritePageOf_frame hw 1 cvp cvp) fun _ =>
      BoundedFrameProg.bind_prog (pageWriteOwnerVpOnly_frame hw pCur vpO) fun _ =>
      pageWriteOwnerVpOnly_frame hw cvp cvp
  have hfcs : BoundedFrameProg L.OwnsAddr 22 (pageFinishCleanStepProg (L.toCtx, cvp)) := by
    unfold pageFinishCleanStepProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageMaybeStartJob_frame L) fun _ =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun q1' =>
      BoundedFrameProg.ite_prog (q1' < L.maxPages)
        (fun _ => pageWriteClean_frame L _)
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
      (fun _ h => h) (by omega)
  unfold pageUnpermPhase2EndProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  dsimp only [PageArenaLayout.toCtx] at hccd hfcs
  exact BoundedFrameProg.ite_prog (cvp < q1)
    (fun _ => (BoundedFrameProg.bind_prog (pageReadPageOf_frame L 1 cvp) fun pCur =>
      BoundedFrameProg.bind_prog (pageReadOwner_frame L cvp) fun owC =>
      BoundedFrameProg.bind_prog (hccd pCur owC.2) fun _ => hfcs).mono
      (fun _ h => h) (by omega))
    (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))

private theorem pageUnpermPhase2_frame {L : PageArenaLayout} (hw : 0 < L.w) (cvp coff : ℕ) :
    BoundedFrameProg L.OwnsAddr 55 (pageUnpermPhase2Prog (L.toCtx, (cvp, coff))) := by
  have hdisp : ∀ q1, BoundedFrameProg L.OwnsAddr 50
      (if coff = 0 then pageUnpermPhase2ZeroProg (L.toCtx, (cvp, q1))
       else if coff < L.pgB then pageUnpermPhase2MidProg (L.toCtx, ((cvp, coff), q1))
       else pageUnpermPhase2EndProg (L.toCtx, (cvp, q1))) := fun q1 =>
    BoundedFrameProg.ite_prog (coff = 0)
      (fun _ => (pageUnpermPhase2Zero_frame hw cvp q1).mono (fun _ h => h) (by omega)) fun _ =>
    BoundedFrameProg.ite_prog (coff < L.pgB)
      (fun _ => (pageUnpermPhase2Mid_frame hw cvp coff q1).mono (fun _ h => h) (by omega))
      (fun _ => pageUnpermPhase2End_frame hw cvp q1)
  unfold pageUnpermPhase2Prog; dsimp only [PageArenaLayout.toCtx]
  dsimp only [PageArenaLayout.toCtx] at hdisp
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun q1 =>
    BoundedFrameProg.ite_prog (q1 ≤ L.nCap / L.pgB ∧ q1 < L.maxPages)
      (fun _ => hdisp q1)
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

private theorem pageUnpermPhase3_frame {L : PageArenaLayout} (hw : 0 < L.w) (cvp : ℕ) :
    BoundedFrameProg L.OwnsAddr 60 (pageUnpermPhase3Prog (L.toCtx, cvp)) := by
  have hsw : ∀ p₂, BoundedFrameProg L.OwnsAddr 56
      (pageUnpermPhase3SwapProg (L.toCtx, (cvp, p₂))) := fun p₂ => by
    unfold pageUnpermPhase3SwapProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageTailPhys_frame L 1 cvp) fun p₁ =>
      BoundedFrameProg.bind_prog (pageSwapTailSlots_frame hw p₁ p₂) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  unfold pageUnpermPhase3Prog; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
  dsimp only [PageArenaLayout.toCtx] at hsw
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun q1 =>
    BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun r1 =>
    BoundedFrameProg.ite_prog (r1 ≤ cvp)
      (fun _ => (pageWriteClean_frame L _).mono (fun _ h => h) (by omega)) fun _ =>
    BoundedFrameProg.ite_prog (q1 ≤ L.nCap / L.pgB ∧ r1 < 4 * L.pgB ∧ cvp < L.nCap - q1 * L.pgB)
      (fun _ => hsw (q1 * L.pgB + cvp))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

private theorem pageUnpermStep_frame {L : PageArenaLayout} (hw : 0 < L.w) :
    BoundedFrameProg L.OwnsAddr 100 (pageUnpermStepBoundedProg L.toCtx) := by
  unfold pageUnpermStepBoundedProg; dsimp only [PageArenaLayout.toCtx]
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun ph =>
    BoundedFrameProg.bind_prog (pageReadCleanPos_frame L) fun co =>
    BoundedFrameProg.ite_prog (ph = 1) (fun _ => pageUnpermPhase1_frame hw co.1) fun _ =>
    BoundedFrameProg.ite_prog (ph = 2)
      (fun _ => (pageUnpermPhase2_frame hw co.1 co.2).mono (fun _ h => h) (by omega)) fun _ =>
    BoundedFrameProg.ite_prog (ph = 3)
      (fun _ => (pageUnpermPhase3_frame hw co.1).mono (fun _ h => h) (by omega))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

theorem pageRunUnpermBatchProg_frame {L : PageArenaLayout} (hw : 0 < L.w) (fuel : ℕ) :
    BoundedFrameProg L.OwnsAddr (100 * fuel) (pageRunUnpermBatchProg (L.toCtx, fuel)) := by
  unfold pageRunUnpermBatchProg pageRunUnpermIterProg; dsimp only
  have hstep : ∀ a, BoundedFrameProg L.OwnsAddr 100 (pageUnpermIterStepProg (L.toCtx, a)) :=
    fun a => (BoundedFrameProg.bind_prog (pageUnpermStep_frame hw)
      (fun _ => BoundedFrameProg.pure_prog a)).mono (fun _ h => h) (by omega)
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.iterate_prog L.toCtx hstep fuel 0)
    (fun _ => BoundedFrameProg.pure_prog ())).mono (fun _ h => h) (by omega)

theorem pageAppendBoundedProg_frame {L : PageArenaLayout} (hw : 0 < L.w) (sb tickFuel : ℕ) :
    BoundedFrameProg L.OwnsAddr (80 * tickFuel + 48)
      (pageAppendBoundedProg ((L.toCtx, sb), tickFuel)) := by
  have hcom : ∀ sb' rs th totI, BoundedFrameProg L.OwnsAddr 10
      (pageRawAppendCommitProg (L.toCtx, ((sb', rs), (th, totI)))) := fun sb' rs th totI => by
    unfold pageRawAppendCommitProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    have hw_tc : L.OwnsAddr (L.metaBase + if sb' = 0 then 23 else 24) :=
      Or.inl (Or.inl (by split_ifs <;> refine ⟨by omega, by omega⟩))
    exact (BoundedFrameProg.bind_prog (BoundedFrameProg.write_prog hw_tc _) fun _ =>
      BoundedFrameProg.bind_prog (pageWriteTailRes_frame hw _ _ _) fun _ =>
      pageWriteTailOwner_frame hw _ _ _).mono (fun _ h => h) (by omega)
  have hchk : ∀ sb' base tc th, BoundedFrameProg L.OwnsAddr 10
      (pageRawAppendCheckProg ((L.toCtx, sb'), (base, (tc, th)))) := fun sb' base tc th => by
    unfold pageRawAppendCheckProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    dsimp only [PageArenaLayout.toCtx] at hcom
    exact BoundedFrameProg.ite_prog _
      (fun _ => BoundedFrameProg.ite_prog _
        (fun _ => BoundedFrameProg.ite_prog _
          (fun _ => hcom sb' _ th _)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  have hraw : BoundedFrameProg L.OwnsAddr 16 (pageRawAppendProg (L.toCtx, sb)) := by
    unfold pageRawAppendProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    dsimp only [PageArenaLayout.toCtx] at hchk
    exact (BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
      BoundedFrameProg.bind_prog (pageReadTailCounts_frame L) fun tc =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun th =>
      BoundedFrameProg.ite_prog _
        (fun _ => BoundedFrameProg.ite_prog _
          (fun _ => hchk _ _ tc th)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
      (fun _ h => h) (by omega)
  have hzpr : BoundedFrameProg L.OwnsAddr (80 * tickFuel + 24)
      (pageZeroPhaseRebalanceProg (L.toCtx, tickFuel)) := by
    unfold pageZeroPhaseRebalanceProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageMaybeStartJob_frame L) fun _ =>
      BoundedFrameProg.bind_prog (pageRunTicksBatchProg_frame hw tickFuel) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  have hrsc : ∀ cvp, BoundedFrameProg L.OwnsAddr (80 * tickFuel + 24)
      (pageRebalanceSyncCleanProg ((L.toCtx, tickFuel), cvp)) := fun cvp => by
    unfold pageRebalanceSyncCleanProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageMaybeStartJob_frame L) fun _ =>
      BoundedFrameProg.bind_prog (pageRunTicksBatchProg_frame hw tickFuel) fun _ =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  unfold pageAppendBoundedProg; dsimp only [PageArenaLayout.toCtx]
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun ph =>
    BoundedFrameProg.bind_prog (pageReadCleanPos_frame L) fun co =>
    BoundedFrameProg.bind_prog hraw fun _ =>
    BoundedFrameProg.ite_prog (ph = 0) (fun _ => hzpr) fun _ =>
    BoundedFrameProg.ite_prog (ph = 1 ∨ (ph = 2 ∧ co.2 = 0))
      (fun _ => hrsc co.1)
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
    (fun _ h => h) (by omega)

theorem pagePopBackBoundedProg_frame {L : PageArenaLayout} (hw : 0 < L.w) (sb tickFuel : ℕ) :
    BoundedFrameProg L.OwnsAddr (80 * tickFuel + 90)
      (pagePopBackBoundedProg ((L.toCtx, sb), tickFuel)) := by
  have hcom : ∀ sb' rs totI, BoundedFrameProg L.OwnsAddr 54
      (pageRawPopBackCommitProg (L.toCtx, ((sb', rs), totI))) := fun sb' rs totI => by
    unfold pageRawPopBackCommitProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    have hw_tc : L.OwnsAddr (L.metaBase + if sb' = 0 then 23 else 24) :=
      Or.inl (Or.inl (by split_ifs <;> refine ⟨by omega, by omega⟩))
    exact (BoundedFrameProg.bind_prog (pageTailPhys_frame L sb' (rs - 1)) fun p₁ =>
      BoundedFrameProg.bind_prog (pageSwapTailSlots_frame hw p₁ (totI - 1)) fun _ =>
      BoundedFrameProg.write_prog hw_tc _).mono (fun _ h => h) (by omega)
  have hchk : ∀ sb' base tc, BoundedFrameProg L.OwnsAddr 54
      (pageRawPopBackCheckProg ((L.toCtx, sb'), (base, tc))) := fun sb' base tc => by
    unfold pageRawPopBackCheckProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    dsimp only [PageArenaLayout.toCtx] at hcom
    exact BoundedFrameProg.ite_prog _
      (fun _ => BoundedFrameProg.ite_prog _
        (fun _ => BoundedFrameProg.ite_prog _
          (fun _ => hcom sb' _ _)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
      (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))
  have hraw : BoundedFrameProg L.OwnsAddr 60 (pageRawPopBackProg (L.toCtx, sb)) := by
    unfold pageRawPopBackProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    dsimp only [PageArenaLayout.toCtx] at hchk
    exact (BoundedFrameProg.bind_prog (pageReadFullPages_frame L) fun fp =>
      BoundedFrameProg.bind_prog (pageReadTailCounts_frame L) fun tc =>
      BoundedFrameProg.ite_prog _
        (fun _ => BoundedFrameProg.ite_prog _
          (fun _ => hchk _ _ tc)
          (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega)))
        (fun _ => (BoundedFrameProg.pure_prog ()).mono (fun _ h => h) (by omega))).mono
      (fun _ h => h) (by omega)
  have hzpr : BoundedFrameProg L.OwnsAddr (80 * tickFuel + 24)
      (pageZeroPhaseRebalanceProg (L.toCtx, tickFuel)) := by
    unfold pageZeroPhaseRebalanceProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageMaybeStartJob_frame L) fun _ =>
      BoundedFrameProg.bind_prog (pageRunTicksBatchProg_frame hw tickFuel) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  have hrsc : ∀ cvp, BoundedFrameProg L.OwnsAddr (80 * tickFuel + 24)
      (pageRebalanceSyncCleanProg ((L.toCtx, tickFuel), cvp)) := fun cvp => by
    unfold pageRebalanceSyncCleanProg; dsimp only [PageArenaLayout.toCtx]; simp only [pure_bind]
    exact (BoundedFrameProg.bind_prog (pageMaybeStartJob_frame L) fun _ =>
      BoundedFrameProg.bind_prog (pageRunTicksBatchProg_frame hw tickFuel) fun _ =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
      BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
      pageWriteClean_frame L _).mono (fun _ h => h) (by omega)
  have hptc : ∀ ph co, BoundedFrameProg L.OwnsAddr (80 * tickFuel + 24)
      (pagePopBackTailCleanProg ((L.metaBase, ph), co)) := fun ph co => by
    unfold pagePopBackTailCleanProg; dsimp only; simp only [pure_bind]
    exact BoundedFrameProg.ite_prog (ph = 2)
      (fun _ => (pageWriteClean_frame L _).mono (fun _ h => h) (by omega))
      (fun _ => (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun _ =>
        pageWriteClean_frame L _).mono (fun _ h => h) (by omega))
  unfold pagePopBackBoundedProg; dsimp only [PageArenaLayout.toCtx]
  exact (BoundedFrameProg.bind_prog (BoundedFrameProg.read_prog _ _) fun ph =>
    BoundedFrameProg.bind_prog (pageReadCleanPos_frame L) fun co =>
    BoundedFrameProg.bind_prog hraw fun _ =>
    BoundedFrameProg.ite_prog (ph = 0) (fun _ => hzpr) fun _ =>
    BoundedFrameProg.ite_prog (ph = 1 ∨ (ph = 2 ∧ co.2 = 0))
      (fun _ => hrsc co.1) (fun _ => hptc ph co)).mono (fun _ h => h) (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end

/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFast
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic

/-!
# Unified Small/Large Epoch Dispatcher (`pBase`-Addressed, `¬ReadsWidth`)

This module unifies the unhashed small regime (`SmallEpochLayout`, capacity marker `N = 0` at
`mem pBase`) and the hashed large regime (`FastEpochLayout`, capacity `whpThreshold c ≤ N` at
`mem pBase`) behind a single `pBase`-addressed 64-word `EpochParamTable` interface
(`EpochLayout`, `SmallEpochLayout.StateInv`, `LargeEpochInv`, `epochInitZeroedProg`,
`epochReadNSideProg`, `epochQueryProg`, `epochInsertProg`, `epochDeleteProg`, and
`epochPopAnyProg`).

Every dispatcher program inspects `Memory.read pBase` (`0` = small, `≠ 0` = large) and runs over
`Cslib.WordRAM.Basis.exact` with `¬ReadsWidth` (`RealizesBounded .exact`), charging at most the
`c`-only constant `epochStepCost c` in the small regime (`n_t < 2 * whpThreshold c`) and on the
large-epoch fast path (`fallbackMode = 0`).

## Main definitions

* `SmallEpochLayout.ParamTable`: small-regime 64-word parameter table at `[pBase, pBase + 64)`.
* `EpochLayout`: tagged layout unifying `SmallEpochLayout` (`N = 0`) and `FastEpochLayout`
  (`whpThreshold c ≤ N`).
* `EpochProgPre`, `EpochInsertProgPre`: `RealizesBounded` preconditions on `[pBase, pBase + 64)`.
* `smallStepCost`, `epochStepCost`: pure `c`-only worst-case `memoryCost` bounds.
* `epochInitZeroedProg`, `epochReadNSideProg`, `epochQueryProg`, `epochInsertProg`,
  `epochDeleteProg`, `epochPopAnyProg`: unified `pBase`-addressed `Memory.Prog` operations.

## Main results

* `PoolItemsRefines.card_eq`: exact bijection showing physical slot count `nSide` equals live key
  cardinality `(Finset.univ.filter (fun u => s_abs u ≠ none)).card`.
* `realizesBounded_epochInitZeroed`, `realizesBounded_epochReadNSide`,
  `realizesBounded_epochQuery`, `realizesBounded_epochInsert`,
  `realizesBounded_epochDelete`, `realizesBounded_epochPopAny`.
* `epochInitZeroedProg_spec_large`, `clientResult_epochReadNSideProg_large`,
  `epochQueryProg_spec_large`, `epochInsertProg_spec_large`, `epochDeleteProg_spec_large`,
  `epochPopAnyProg_spec_large`: large-epoch dispatcher specifications.
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
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'

/-! ## Section 1: Exact Domain-Size Bijection for `PoolItemsRefines` -/

/-- The physical active-slot count `nSide` of any `PoolItemsRefines` table equals the exact live
domain cardinality of `s_abs`. -/
theorem PoolItemsRefines.card_eq {U V bBits nSide : ℕ} {hBkt : ℕ → ℕ}
    {ownerFn : ℕ → ℕ} {pairFn : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    [DecidablePred fun u : Fin U => s_abs u ≠ none]
    (href : PoolItemsRefines U V bBits hBkt nSide ownerFn pairFn s_abs) :
    nSide = (Finset.univ.filter fun u : Fin U => s_abs u ≠ none).card := by
  classical
  have key_of : ∀ p, p < nSide →
      { u : Fin U // feistelBucket bBits hBkt u.val = ownerFn p ∧
        keyQuotient bBits u.val = (pairFn p).1 ∧ s_abs u ≠ none } := fun p hp => by
    obtain ⟨_, hv, hex⟩ := href.slot_valid p hp
    have hu := Classical.choose_spec hex
    refine ⟨Classical.choose hex, hu.1, hu.2, ?_⟩
    have hsome : s_abs (Classical.choose hex) = some ⟨(pairFn p).2, hv⟩ :=
      (href.models _ _).mpr ⟨p, hp, hu.1.symm, hu.2.symm, rfl⟩
    rw [hsome]
    exact Option.some_ne_none _
  rw [← Finset.card_range nSide]
  refine Finset.card_bij
    (fun p hp => (key_of p (Finset.mem_range.mp hp)).1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (key_of p (Finset.mem_range.mp hp)).2.2.2
  · intro p₁ hp₁ p₂ hp₂ heq
    have h1 := Finset.mem_range.mp hp₁
    have h2 := Finset.mem_range.mp hp₂
    have hk1 := (key_of p₁ h1).2
    have hk2 := (key_of p₂ h2).2
    have ho : ownerFn p₁ = ownerFn p₂ := by rw [← hk1.1, ← hk2.1, heq]
    have hq : (pairFn p₁).1 = (pairFn p₂).1 := by rw [← hk1.2.1, ← hk2.2.1, heq]
    exact href.slot_inj p₁ h1 p₂ h2 ho hq
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    cases hsu : s_abs u with
    | none => exact absurd hsu hu
    | some v =>
      obtain ⟨p, hp, ho, hq, _⟩ := (href.models u v).mp hsu
      refine ⟨p, Finset.mem_range.mpr hp, ?_⟩
      have hk := (key_of p hp).2
      have hsame_b : feistelBucket bBits hBkt (key_of p hp).1.val =
          feistelBucket bBits hBkt u.val := hk.1.trans ho
      have hsame_q : keyQuotient bBits (key_of p hp).1.val = keyQuotient bBits u.val :=
        hk.2.1.trans hq
      have hval : (key_of p hp).1.val = u.val := by
        have h1 := feistelReconstruct_feistelBucket bBits hBkt (key_of p hp).1.val
        have h2 := feistelReconstruct_feistelBucket bBits hBkt u.val
        rw [← h1, ← h2, hsame_b, hsame_q]
      exact Fin.ext hval

/-- In a `SmallEpochLayout`, `mem (L.metaBase + 1)` equals the live key count. -/
theorem SmallEpochLayout.StateInv.nSide_eq_card {L : SmallEpochLayout} {slack : ℕ}
    {mem : ℕ → ℕ} {s_abs : Fin L.U → Option (Fin L.V)}
    [DecidablePred fun u : Fin L.U => s_abs u ≠ none]
    (h : L.StateInv slack mem s_abs) :
    mem (L.metaBase + 1) = (Finset.univ.filter fun u : Fin L.U => s_abs u ≠ none).card :=
  h.2.2.2.card_eq

/-- In fast mode (`FastEpochInvGen`), `mem (fl.metaBase + 1) = bp.nSide` equals live key count. -/
theorem FastEpochInvGen.nSide_eq_card {slackCur : ℕ} {fl : FastEpochLayout} {slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    [DecidablePred fun u : Fin fl.U => s_abs u ≠ none]
    (h : FastEpochInvGen slackCur fl slack seeds mem s_abs) :
    (extractBlockPool fl.mp mem).nSide =
      (Finset.univ.filter fun u : Fin fl.U => s_abs u ≠ none).card :=
  h.refines.card_eq

/-- In fallback mode (`FallbackLayout.StateInv`), `fb.nSide` equals live key count. -/
theorem FallbackLayout.StateInv.nSide_eq_card {fl : FallbackLayout} {slack : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    [DecidablePred fun u : Fin fl.U => s_abs u ≠ none]
    (h : fl.StateInv slack θ_bkt mem s_abs) :
    (extractFallback fl.bpL.mp mem).nSide =
      (Finset.univ.filter fun u : Fin fl.U => s_abs u ≠ none).card :=
  h.refines.card_eq

/-! ## Section 2: Small-Regime `pBase` Parameter Table and Wrappers -/

/-- Small-regime 64-word `EpochParamTable` layout at `[pBase, pBase + 64)`: word `0` holds `0`
(distinguishing the small regime from large epochs where `whpThreshold c ≤ N`), word `1` holds
`L.metaBase`, and words `48..60` mirror `FastEpochLayout`'s `SlotIoCtx` slots. -/
@[expose] def SmallEpochLayout.ParamTable (L : SmallEpochLayout) (pBase : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  mem pBase = 0 ∧
  mem (pBase + 1) = L.metaBase ∧
  mem (pBase + 48) = L.io.usePaged ∧
  mem (pBase + 49) = L.io.sideBit ∧
  mem (pBase + 50) = L.io.pgL.metaBase ∧
  mem (pBase + 51) = L.io.pgL.offDir ∧
  mem (pBase + 52) = L.io.pgL.offTail ∧
  mem (pBase + 53) = L.io.pgL.ptrB ∧
  mem (pBase + 54) = L.io.pgL.w ∧
  mem (pBase + 55) = L.io.pgL.pgB ∧
  mem (pBase + 56) = L.io.pgL.maxPages ∧
  mem (pBase + 57) = L.io.pgL.itemBase ∧
  mem (pBase + 58) = L.io.pgL.qBits ∧
  mem (pBase + 59) = L.io.pgL.vBits ∧
  mem (pBase + 60) = L.io.pgL.nCap

theorem SmallEpochLayout.ParamTable.congr {L : SmallEpochLayout} {pBase : ℕ}
    {m₁ m₂ : ℕ → ℕ} (h : L.ParamTable pBase m₁)
    (heq : ∀ a, pBase ≤ a → a < pBase + 64 → m₂ a = m₁ a) :
    L.ParamTable pBase m₂ := by
  have hp : ∀ k < 64, m₂ (pBase + k) = m₁ (pBase + k) := fun k hk =>
    heq (pBase + k) (Nat.le_add_right _ _) (by omega)
  unfold SmallEpochLayout.ParamTable at h ⊢
  refine ⟨(hp 0 (by decide)).trans h.1, (hp 1 (by decide)).trans h.2.1,
    (hp 48 (by decide)).trans h.2.2.1, (hp 49 (by decide)).trans h.2.2.2.1,
    (hp 50 (by decide)).trans h.2.2.2.2.1, (hp 51 (by decide)).trans h.2.2.2.2.2.1,
    (hp 52 (by decide)).trans h.2.2.2.2.2.2.1, (hp 53 (by decide)).trans h.2.2.2.2.2.2.2.1,
    (hp 54 (by decide)).trans h.2.2.2.2.2.2.2.2.1,
    (hp 55 (by decide)).trans h.2.2.2.2.2.2.2.2.2.1,
    (hp 56 (by decide)).trans h.2.2.2.2.2.2.2.2.2.2.1,
    (hp 57 (by decide)).trans h.2.2.2.2.2.2.2.2.2.2.2.1,
    (hp 58 (by decide)).trans h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (hp 59 (by decide)).trans h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (hp 60 (by decide)).trans h.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- Direct read-only loader of `SlotIoCtx` from `pBase + 48..60` (`13` words, `¬ReadsWidth`). -/
private def loadSmallIoCtxProg (pBase : ℕ) : Memory.Prog SlotIoCtx := do
  let up ← Memory.read (pBase + 48)
  let sb ← Memory.read (pBase + 49)
  let mb ← Memory.read (pBase + 50)
  let od ← Memory.read (pBase + 51)
  let ot ← Memory.read (pBase + 52)
  let pb ← Memory.read (pBase + 53)
  let wv ← Memory.read (pBase + 54)
  let pg ← Memory.read (pBase + 55)
  let mp ← Memory.read (pBase + 56)
  let ib ← Memory.read (pBase + 57)
  let qb ← Memory.read (pBase + 58)
  let vb ← Memory.read (pBase + 59)
  let nc ← Memory.read (pBase + 60)
  pure ((up, sb), (((mb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc))

@[simp] private theorem clientState_read_eq (a : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.read a) = s := rfl

@[simp] private theorem runClient_state_loadSmallIoCtxProg (pBase : ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (loadSmallIoCtxProg pBase)).2.1 = s := by
  change (Memory.spec 0).clientState s (loadSmallIoCtxProg pBase) = s
  unfold loadSmallIoCtxProg
  iterate 13 (rw [StateTransitionSpec.clientState_bind, clientState_read_eq])
  rfl

private theorem clientState_loadSmallIoCtxProg (pBase : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (loadSmallIoCtxProg pBase) = s :=
  runClient_state_loadSmallIoCtxProg pBase s

private theorem memoryCost_loadSmallIoCtxProg (pBase : ℕ) (s : Memory.State) :
    memoryCost (loadSmallIoCtxProg pBase) s = 13 := by
  unfold loadSmallIoCtxProg
  iterate 13 (rw [Realization.memoryCost_bind', prog_memoryCost_read, clientState_read_eq])
  rw [memoryCost_pure]

private theorem clientResult_loadSmallIoCtxProg {L : SmallEpochLayout} {pBase : ℕ}
    {s : Memory.State} (hpt : L.ParamTable pBase s.mem) :
    (Memory.spec 0).clientResult s (loadSmallIoCtxProg pBase) = L.io.toCtx := by
  unfold loadSmallIoCtxProg
  iterate 13 (rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read])
  rw [prog_clientResult_pure, hpt.2.2.1, hpt.2.2.2.1, hpt.2.2.2.2.1, hpt.2.2.2.2.2.1,
    hpt.2.2.2.2.2.2.1, hpt.2.2.2.2.2.2.2.1, hpt.2.2.2.2.2.2.2.2.1, hpt.2.2.2.2.2.2.2.2.2.1,
    hpt.2.2.2.2.2.2.2.2.2.2.1, hpt.2.2.2.2.2.2.2.2.2.2.2.1, hpt.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hpt.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hpt.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  rfl

private theorem realizesBounded_loadSmallIoCtx :
    RealizesBounded .exact loadSmallIoCtxProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := SlotIoCtx))
      (fun w pBase s => 6 ≤ w ∧ pBase + 64 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (
    have hw6 : 6 ≤ w := h.1
    have hp : d + 64 ≤ s.frontier := h.2
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    omega)

/-- Readiness predicate for a small-regime epoch parameter block at `[pBase, pBase + 64)`. -/
@[expose] def SmallLayoutReady (w pBase : ℕ) (L : SmallEpochLayout) (s : Memory.State) : Prop :=
  6 ≤ w ∧ pBase + 64 ≤ s.frontier ∧ L.Valid w s.frontier ∧ L.ParamTable pBase s.mem

/-! ## Section 3: Unified `EpochLayout`, `EpochProgPre`, and Step Cost Bounds -/

/-- Worst-case `memoryCost` bound for a small-regime operation (`nSide < 2 * whpThreshold c`). -/
@[expose] def smallStepCost (c : ℕ) : ℕ :=
  21 * (2 * whpThreshold c) + 1600

/-- Unified pure `c`-only worst-case `memoryCost` bound for every `pBase`-addressed epoch
operation (`query`, `insert`, `delete`, `popAny`) in the small regime or large-epoch fast mode. -/
@[expose] def epochStepCost (c : ℕ) : ℕ :=
  max (smallStepCost c) (largeFastStepCost c) + 32

/-- Unified readiness precondition for `epochInitZeroedProg`, `epochQueryProg`,
`epochDeleteProg`, and `epochPopAnyProg` (`mem pBase = 0` → `SmallLayoutReady`,
`mem pBase ≠ 0` → `FastLayoutReady`). -/
@[expose] def EpochProgPre (w pBase : ℕ) (s : Memory.State) : Prop :=
  (s.mem pBase = 0 ∧ ∃ L : SmallEpochLayout, SmallLayoutReady w pBase L s) ∨
  (s.mem pBase ≠ 0 ∧ ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ FastLayoutReady w fl s)

/-- Precondition for `epochInsertProg`: strengthens the large-epoch branch of `EpochProgPre` with
`FastInsertProgPre` (which discharges `fastEnterFallbackProg`'s frame when starting at `mode = 0`).
-/
@[expose] def EpochInsertProgPre (w pBase : ℕ) (s : Memory.State) : Prop :=
  (s.mem pBase = 0 ∧ ∃ L : SmallEpochLayout, SmallLayoutReady w pBase L s) ∨
  (s.mem pBase ≠ 0 ∧ FastInsertProgPre w pBase s)

theorem EpochProgPre.of_small {w pBase : ℕ} {L : SmallEpochLayout} {s : Memory.State}
    (h : SmallLayoutReady w pBase L s) : EpochProgPre w pBase s :=
  Or.inl ⟨h.2.2.2.1, L, h⟩

theorem EpochProgPre.of_large {w : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hr : FastLayoutReady w fl s) : EpochProgPre w fl.pBase s := by
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hr.1.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hr.2.1 0 (by decide)
  exact Or.inr ⟨by rw [hm0]; omega, fl, rfl, hr⟩

theorem EpochInsertProgPre.of_small {w pBase : ℕ} {L : SmallEpochLayout} {s : Memory.State}
    (h : SmallLayoutReady w pBase L s) : EpochInsertProgPre w pBase s :=
  Or.inl ⟨h.2.2.2.1, L, h⟩

theorem EpochInsertProgPre.of_large {w slack : ℕ} {fl : FastEpochLayout}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl slack seeds s.mem s_abs)
    (hfp : s.mem fl.fpHashBase < 2 ^ (redWidthWhp fl.U - 1)) :
    EpochInsertProgPre w fl.pBase s := by
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hinv.1 0 (by decide)
  exact Or.inr ⟨by rw [hm0]; omega, hinv.fastInsertProgPre hv hfp⟩

private theorem epochProgPre_bounds {w pBase : ℕ} {s : Memory.State}
    (h : EpochProgPre w pBase s) : 6 ≤ w ∧ pBase + 64 ≤ s.frontier := by
  rcases h with ⟨_, _, hw6, hp, _, _⟩ | ⟨_, fl, rfl, hr⟩
  · exact ⟨hw6, hp⟩
  · exact FastProgPre.pBase_bound ⟨fl, rfl, hr⟩

private theorem epochInsertProgPre_bounds {w pBase : ℕ} {s : Memory.State}
    (h : EpochInsertProgPre w pBase s) : 6 ≤ w ∧ pBase + 64 ≤ s.frontier := by
  rcases h with ⟨_, _, hw6, hp, _, _⟩ | ⟨_, fl, rfl, hr, _⟩
  · exact ⟨hw6, hp⟩
  · exact FastProgPre.pBase_bound ⟨fl, rfl, hr⟩

/-- Named helper bundling a small or large epoch layout with uniform accessors. -/
inductive EpochLayout where
  /-- Unhashed small epoch (`N = 0`). -/
  | small (L : SmallEpochLayout) (pBase : ℕ)
  /-- Hashed large epoch (`whpThreshold c ≤ N`). -/
  | large (fl : FastEpochLayout)

namespace EpochLayout

/-- Address of the 64-word parameter block `[pBase, pBase + 64)`. -/
@[expose] def pBase : EpochLayout → ℕ
  | small _ pb => pb
  | large fl => fl.pBase

/-- Base metadata word address (`metaBase + 0` stores `N`, `metaBase + 1` stores `nSide`). -/
@[expose] def metaBase : EpochLayout → ℕ
  | small L _ => L.metaBase
  | large fl => fl.metaBase

/-- Underlying slot-I/O layout. -/
@[expose] def io : EpochLayout → SlotIoLayout
  | small L _ => L.io
  | large fl => fl.io

/-- Key universe bound `U`. -/
@[expose] def U : EpochLayout → ℕ
  | small L _ => L.U
  | large fl => fl.U

/-- Value universe bound `V`. -/
@[expose] def V : EpochLayout → ℕ
  | small L _ => L.V
  | large fl => fl.V

/-- Mutable word-address footprint of an initialized epoch (excluding `[pBase, pBase + 64)`,
`metaBase + 0`, and large-epoch hash seeds). -/
@[expose] def OwnsAddr : EpochLayout → ℕ → Prop
  | small L _ => L.OwnsAddr
  | large fl => fl.OwnsFastAddr

end EpochLayout

/-! ## Section 4: Unified `pBase`-Addressed Operations (`¬ReadsWidth`) -/

/-- Read `nSide = mem (metaBase + 1)` uniformly for either a small or large (fast or fallback)
epoch via its parameter block `pBase` (`¬ReadsWidth`). -/
def epochReadNSideProg (pBase : ℕ) : Memory.Prog ℕ := do
  let mb ← Memory.read (pBase + 1)
  Memory.read (mb + 1)

@[simp] theorem runClient_state_epochReadNSideProg (pBase : ℕ) (s : Memory.State) :
    clientOutState ((Memory.spec 0).runClient s (epochReadNSideProg pBase)) = s := by
  unfold epochReadNSideProg; simp

theorem clientState_epochReadNSideProg (pBase : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (epochReadNSideProg pBase) = s :=
  runClient_state_epochReadNSideProg pBase s

theorem memoryCost_epochReadNSideProg (pBase : ℕ) (s : Memory.State) :
    memoryCost (epochReadNSideProg pBase) s = 2 := by
  unfold epochReadNSideProg
  rw [Realization.memoryCost_bind', clientState_read_eq, prog_memoryCost_read,
    prog_memoryCost_read]

theorem realizesBounded_epochReadNSide :
    RealizesBounded .exact epochReadNSideProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w pBase s => EpochProgPre w pBase s) (fun _ _ => 0) := by
  realize
  all_goals (
    obtain ⟨hw6, hp⟩ := epochProgPre_bounds h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    rcases h with ⟨_, L, _, _, hv, hpt⟩ | ⟨_, fl, rfl, hr⟩
    · have hmb : s.mem (d + 1) = L.metaBase := hpt.2.1
      have hfr_mb : L.metaBase + 2 ≤ s.frontier := hv.hdr_frontier
      omega
    · have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hr.2.1 1 (by decide)
      have hfr_mb : fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N ≤ s.frontier :=
        hr.1.meta_frontier
      have h32 : 32 ≤ epochMetaWordsWhp fl.c fl.w fl.N := by
        have h1 := offEpochEnd_eq_epochMetaWordsWhp (c := fl.c) (w := fl.w) hr.1.thresh_le
        unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
          offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
          offBktMeta offFpHash offBktHash at h1
        omega
      omega)

theorem clientResult_epochReadNSideProg_small {L : SmallEpochLayout} {pBase : ℕ}
    {s : Memory.State} (hpt : L.ParamTable pBase s.mem) :
    (Memory.spec 0).clientResult s (epochReadNSideProg pBase) = s.mem (L.metaBase + 1) := by
  unfold epochReadNSideProg
  rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read,
    prog_clientResult_read, hpt.2.1]

theorem clientResult_epochReadNSideProg_large {fl : FastEpochLayout} {s : Memory.State}
    (hpt : fl.ParamTable s.mem) :
    (Memory.spec 0).clientResult s (epochReadNSideProg fl.pBase) = s.mem (fl.metaBase + 1) := by
  unfold epochReadNSideProg
  rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read,
    prog_clientResult_read, hpt 1 (by decide)]
  rfl

/-- Initialize an empty zeroed epoch (small if `mem pBase = 0`, large fast-mode if `mem pBase ≠ 0`,
after parameter table and hash seeds are populated) via `pBase` (`¬ReadsWidth`). -/
def epochInitZeroedProg (pBase : ℕ) : Memory.Prog Unit := do
  let nCap ← Memory.read pBase
  let mb ← Memory.read (pBase + 1)
  if nCap = 0 then
    smallEpochInitProg mb
  else do
    Memory.write mb nCap
    fastInitZeroedProg pBase

theorem realizesBounded_epochInitZeroed :
    RealizesBounded .exact epochInitZeroedProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w pBase s => EpochProgPre w pBase s) (fun _ _ => 0) := by
  have hsi := realizesBounded_smallEpochInit
  have hfi := realizesBounded_fastInitZeroed
  realize
  all_goals (
    obtain ⟨hw6, hp⟩ := epochProgPre_bounds h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    rcases h with ⟨hm0, L, _, _, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩
    <;> first
    | omega
    | (have hmb : s.mem (d + 1) = L.metaBase := hpt.2.1
       have hfr_mb : L.metaBase + 2 ≤ s.frontier := hv.hdr_frontier
       omega)
    | (have hcN : s.mem fl.pBase = fl.N := hr.2.1 0 (by decide)
       have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hr.2.1 1 (by decide)
       have h32 : 32 ≤ epochMetaWordsWhp fl.c fl.w fl.N := by
         have h1 := offEpochEnd_eq_epochMetaWordsWhp (c := fl.c) (w := fl.w) hr.1.thresh_le
         unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
           offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
           offBktMeta offFpHash offBktHash at h1
         omega
       have hfr_mb : fl.metaBase + 32 ≤ s.frontier :=
         le_trans (Nat.add_le_add_left h32 _) hr.1.meta_frontier
       have hN_lt : fl.N < 2 ^ w := lt_of_le_of_lt hr.1.N_le_U hr.1.fits_U
       first
       | omega
       | (rw [hmb]; omega)
       | (rw [hcN]; omega)
       | (refine ⟨fl, rfl, hr.1, ?_, ?_, ?_⟩
          · exact hr.2.1.congr fun a ha1 ha2 =>
              Function.update_of_ne (fun he => by
                have hpl := hr.1.pBase_lt_meta; rw [hmb] at he; omega) _ _
          · change Function.update s.mem (s.mem (fl.pBase + 1)) (s.mem fl.pBase)
              fl.bktHashBase < 2 ^ (redWidthWhp fl.U - 1)
            rw [Function.update_of_ne (by
              rw [hmb]; dsimp only [FastEpochLayout.bktHashBase]; unfold offBktHash; omega)]
            exact hr.2.2.1
          · change Function.update s.mem (s.mem (fl.pBase + 1)) (s.mem fl.pBase)
              fl.fpHashBase < 2 ^ (redWidthWhp fl.U - 1)
            have hne : fl.fpHashBase ≠ s.mem (fl.pBase + 1) := by
              rw [hmb]; dsimp only [FastEpochLayout.fpHashBase]
              unfold offFpHash offBktHash; omega
            rw [Function.update_of_ne hne]
            exact hr.2.2.2)))

/-- Exact specification of `epochInitZeroedProg` in the small regime (`N = 0`). -/
theorem epochInitZeroedProg_spec_small {L : SmallEpochLayout} {w pBase slack : ℕ}
    {s : Memory.State} (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hdisj : ∀ a, pBase ≤ a → a < pBase + 64 → ¬L.OwnsAddr a)
    (hio0 : L.io.StateInv 0 slack s.mem) :
    let s' := (Memory.spec 0).clientState s (epochInitZeroedProg pBase)
    s'.frontier = s.frontier ∧
    memoryCost (epochInitZeroedProg pBase) s ≤ 5 ∧
    L.ParamTable pBase s'.mem ∧
    L.StateInv slack s'.mem (fun _ => none) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (L.io.usePaged ≠ 0 →
      extractPageUnperm L.io.pgL s'.mem = extractPageUnperm L.io.pgL s.mem ∧
      ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
        slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  unfold epochInitZeroedProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_read_eq, prog_clientResult_read, prog_memoryCost_read,
    StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_read_eq, prog_clientResult_read, prog_memoryCost_read,
    hpt.1, hpt.2.1, ite_eq_left rfl]
  obtain ⟨hfr, hinv, hpg⟩ := smallEpochInitProg_spec hv hio0
  have hframe := smallEpochInitProg_frame (L := L)
  have hout : ∀ addr, ¬L.OwnsAddr addr →
      ((Memory.spec 0).clientState s (smallEpochInitProg L.metaBase)).mem addr = s.mem addr :=
    hframe.mem_outside s
  have hpt' : L.ParamTable pBase
      ((Memory.spec 0).clientState s (smallEpochInitProg L.metaBase)).mem :=
    hpt.congr fun a h1 h2 => hout a (hdisj a h1 h2)
  exact ⟨hfr, by have := hframe.cost_le s; omega, hpt', hinv, hout, hpg⟩

/-- Exact specification of `epochInitZeroedProg` in the large regime (`whpThreshold c ≤ N`). -/
theorem epochInitZeroedProg_spec_large {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hbkt_rep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N)
      seeds.bkt s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N)
      seeds.fp s.mem)
    (hzero_hdr : ∀ k, 1 ≤ k → k < 32 → s.mem (fl.metaBase + k) = 0)
    (hzero_tab : ∀ addr, fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → s.mem addr = 0)
    (hio : fl.io.StateInv 0 slack s.mem) :
    let s' := (Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase)
    s'.frontier = s.frontier ∧
    memoryCost (epochInitZeroedProg fl.pBase) s ≤ 45 ∧
    FastEpochInv fl slack seeds s'.mem (fun _ => none) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → addr ≠ fl.metaBase → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s'.mem = extractPageUnperm fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hpt 0 (by decide)
  have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  have hne : fl.N ≠ 0 := hN_pos.ne'
  set s1 : Memory.State := (Memory.spec 0).clientState s (Memory.write fl.metaBase fl.N)
  have hs1_mem : s1.mem = Function.update s.mem fl.metaBase fl.N := rfl
  have hs1_fr : s1.frontier = s.frontier := rfl
  have hpt1 : fl.ParamTable s1.mem := hpt.congr fun a ha1 ha2 => by
    rw [hs1_mem]; exact Function.update_of_ne (fun he => by
      have := hv.pBase_lt_meta; omega) _ _
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hbkt1 : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s1.mem :=
    hbkt_rep.congr_on hw_pos fun a h1 _ => by
      rw [hs1_mem]; exact Function.update_of_ne (by
        dsimp only [FastEpochLayout.bktHashBase] at h1; unfold offBktHash at h1; omega) _ _
  have hfp1 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s1.mem :=
    hfp_rep.congr_on hw_pos fun a h1 _ => by
      rw [hs1_mem]; exact Function.update_of_ne (by
        dsimp only [FastEpochLayout.fpHashBase] at h1
        unfold offFpHash offBktHash at h1; omega) _ _
  have hzh1 : ∀ k, 1 ≤ k → k < 32 → s1.mem (fl.metaBase + k) = 0 := fun k hk1 hk2 => by
    rw [hs1_mem, Function.update_of_ne (by omega)]; exact hzero_hdr k hk1 hk2
  have hzt1 : ∀ addr, fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → s1.mem addr = 0 := fun a h1 h2 => by
    have h32 : 32 ≤ offBktMeta fl.c fl.w fl.N := hv.mp_valid.offBktMeta_ge
    rw [hs1_mem, Function.update_of_ne (by omega)]; exact hzero_tab a h1 h2
  have hio_eq : ∀ addr, fl.io.OwnsAddr addr → s1.mem addr = s.mem addr := fun a ha => by
    rw [hs1_mem]; exact Function.update_of_ne (fun he =>
      hv.disj_fast_io a (Or.inl ⟨by rw [he], by rw [he]; omega⟩) ha) _ _
  have hio1 : fl.io.StateInv 0 slack s1.mem :=
    (fl.io.congr_of_outside hv.io_valid.w_pos hio hio_eq).1
  obtain ⟨hfr, hcost, hinv, hout, hpg⟩ :=
    fastInitZeroedProg_spec (s := s1) (hv := hs1_fr.symm ▸ hv) hpt1
      (by rw [hs1_mem, Function.update_self]) hbkt1 hfp1 hzh1 hzt1 hio1
  have hstep : (Memory.spec 0).clientState s (epochInitZeroedProg fl.pBase) =
      (Memory.spec 0).clientState s1 (fastInitZeroedProg fl.pBase) := by
    unfold epochInitZeroedProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm1, ite_eq_right hne, StateTransitionSpec.clientState_bind]
  have hmc : memoryCost (epochInitZeroedProg fl.pBase) s ≤ 45 := by
    unfold epochInitZeroedProg
    rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hm0,
      Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hm1, ite_eq_right hne,
      Realization.memoryCost_bind', prog_memoryCost_write]
    dsimp only [s1] at hcost
    omega
  rw [hstep]
  refine ⟨hfr.trans hs1_fr, hmc, hinv, fun a ha hne_mb => ?_, fun hup => ?_⟩
  · rw [hout a ha, hs1_mem, Function.update_of_ne hne_mb]
  · obtain ⟨hu1, hp1⟩ := hpg hup
    have hmem_m : ∀ a, fl.io.pgL.OwnsMetaAddr a → s1.mem a = s.mem a := fun a ha =>
      hio_eq a (by unfold SlotIoLayout.OwnsAddr; rw [ite_eq_right hup]; exact Or.inl ha)
    have hmem_i : ∀ a, fl.io.pgL.OwnsItemAddr a → s1.mem a = s.mem a := fun a ha =>
      hio_eq a (by unfold SlotIoLayout.OwnsAddr; rw [ite_eq_right hup]; exact Or.inr ha)
    have hup_s1 : extractPageUnperm fl.io.pgL s1.mem = extractPageUnperm fl.io.pgL s.mem :=
      extractPageUnperm_congr hv.io_valid.w_pos hmem_m
    refine ⟨hu1.trans hup_s1, fun idx hidx => ?_⟩
    have hlen_eq : (extractPagePair fl.io.pgL s1.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side := by
      have : extractPagePair fl.io.pgL s1.mem = extractPagePair fl.io.pgL s.mem :=
        congrArg PageUnpermState.st hup_s1
      rw [this]
    have hidx1 : idx < (extractPagePair fl.io.pgL s1.mem).virtLen fl.io.partner.side := by
      rwa [hlen_eq]
    refine (hp1 idx hidx1).trans ?_
    have hio_inv := hio
    simp only [SlotIoLayout.StateInv, hup, ↓reduceIte] at hio_inv
    have hup_p : fl.io.partner.usePaged ≠ 0 := hup
    unfold slotIoPairAt
    rw [ite_eq_right hup_p, ite_eq_right hup_p]
    change (extractPageUnperm fl.io.pgL s1.mem).virtAt (arenaPairAt fl.io.pgL s1.mem)
        fl.io.partner.side idx =
      (extractPageUnperm fl.io.pgL s.mem).virtAt (arenaPairAt fl.io.pgL s.mem)
        fl.io.partner.side idx
    rw [hup_s1]
    unfold PageUnpermState.virtAt
    have hlt : (extractPageUnperm fl.io.pgL s.mem).toPhys fl.io.partner.side idx <
        fl.io.pgL.nCap :=
      (hio_inv.1.toPhys_lt hidx).trans_le hio_inv.2.2.2.1
    exact arenaPairAt_congr hv.io_valid.w_pos hmem_i hlt

/-- Unified `pBase`-addressed `query(u)` dispatching small (`mem pBase = 0`) vs large
(`mem pBase ≠ 0`) (`¬ReadsWidth`). -/
def epochQueryProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (pBase, u_val) => do
    let nCap ← Memory.read pBase
    if nCap = 0 then do
      let mb ← Memory.read (pBase + 1)
      let ioctx ← loadSmallIoCtxProg pBase
      smallEpochQueryRawProg ((ioctx, mb), u_val)
    else
      largeEpochQueryProg (pBase, u_val)

theorem realizesBounded_epochQuery :
    RealizesBounded .exact epochQueryProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, _) s => EpochProgPre w pBase s) (fun _ _ => 0) := by
  have hli := realizesBounded_loadSmallIoCtx
  have hsq := realizesBounded_smallEpochQueryRaw
  have hlq := realizesBounded_largeEpochQuery
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨hw6, hp⟩ := epochProgPre_bounds h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    first | omega | (rcases h with ⟨hm0, L, _, _, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩ <;> first
    | (have hmb : s.mem (pBase + 1) = L.metaBase := hpt.2.1
       have hio_res := clientResult_loadSmallIoCtxProg (s := s) hpt
       simp only [StateTransitionSpec.clientState, runClient_state_loadSmallIoCtxProg,
         StateTransitionSpec.clientResult] at hio_res ⊢
       try rw [hio_res]
       first | (rw [hmb]; exact hv.hdr_frontier)
             | (rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid))
    | exact ⟨fl, rfl, hr⟩
    | (exfalso; exact absurd hm0 (by assumption))
    | (exfalso; exact hmne (by assumption))))

/-- Exact specification of `epochQueryProg` in the small regime (`N = 0`). -/
theorem epochQueryProg_spec_small {L : SmallEpochLayout} {w pBase slack : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hinv : L.StateInv slack s.mem s_abs) (u : Fin L.U) :
    (Memory.spec 0).clientState s (epochQueryProg (pBase, u.val)) = s ∧
    memoryCost (epochQueryProg (pBase, u.val)) s ≤ 21 * s.mem (L.metaBase + 1) + 20 ∧
    (Memory.spec 0).clientResult s (epochQueryProg (pBase, u.val)) =
      match s_abs u with
      | none => (0, 0)
      | some v => (1, v.val) := by
  obtain ⟨hst, hcost, hres⟩ := smallEpochQueryProg_spec hv hinv u
  have hio := clientResult_loadSmallIoCtxProg (s := s) hpt
  have hm := memoryCost_loadSmallIoCtxProg pBase s
  unfold epochQueryProg
  refine ⟨?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, hio]
    exact hst
  · rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.1, ite_eq_left rfl,
      Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.2.1,
      Realization.memoryCost_bind', clientState_loadSmallIoCtxProg, hm, hio]
    change 1 + (1 + (13 + memoryCost (smallEpochQueryProg L u.val) s)) ≤ _
    omega
  · rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, prog_clientResult_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, prog_clientResult_bind,
      clientState_loadSmallIoCtxProg, hio]
    exact hres

/-- Exact specification of `epochQueryProg` in the large regime (`whpThreshold c ≤ N`). -/
theorem epochQueryProg_spec_large {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl slack seeds s.mem s_abs) (u : Fin fl.U) :
    (Memory.spec 0).clientState s (epochQueryProg (fl.pBase, u.val)) = s ∧
    (Memory.spec 0).clientResult s (epochQueryProg (fl.pBase, u.val)) =
      (match s_abs u with | none => (0, 0) | some v => (1, v.val)) ∧
    (s.mem (fl.metaBase + 2) = 0 →
      memoryCost (epochQueryProg (fl.pBase, u.val)) s ≤ epochStepCost fl.c) := by
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hinv.1 0 (by decide)
  obtain ⟨hst, hres, hcost⟩ := largeEpochQueryProg_spec hv hinv u
  unfold epochQueryProg
  refine ⟨?_, ?_, fun hm => ?_⟩
  · rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
    exact hst
  · rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
    exact hres
  · rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hm0, ite_eq_right hN_pos.ne']
    have hc := hcost hm
    unfold epochStepCost
    have hle := le_max_right (smallStepCost fl.c) (largeFastStepCost fl.c)
    omega

/-- Unified `pBase`-addressed `insert(u, v)` dispatching small vs large (`¬ReadsWidth`). -/
def epochInsertProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, u_val), v_val) => do
    let nCap ← Memory.read pBase
    if nCap = 0 then do
      let mb ← Memory.read (pBase + 1)
      let ioctx ← loadSmallIoCtxProg pBase
      smallEpochInsertRawProg (((ioctx, mb), u_val), v_val)
    else
      largeEpochInsertProg ((pBase, u_val), v_val)

theorem realizesBounded_epochInsert :
    RealizesBounded .exact epochInsertProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => EpochInsertProgPre w pBase s) (fun _ _ => 0) := by
  have hli := realizesBounded_loadSmallIoCtx
  have hsi := realizesBounded_smallEpochInsertRaw
  have hli_lg := realizesBounded_largeEpochInsert
  realize
  all_goals (
    rcases d with ⟨⟨pBase, u_val⟩, v_val⟩
    obtain ⟨hw6, hp⟩ := epochInsertProgPre_bounds h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    first | omega | (rcases h with ⟨hm0, L, _, _, hv, hpt⟩ | ⟨hmne, hpre⟩ <;> first
    | (have hmb : s.mem (pBase + 1) = L.metaBase := hpt.2.1
       have hio_res := clientResult_loadSmallIoCtxProg (s := s) hpt
       simp only [StateTransitionSpec.clientState, runClient_state_loadSmallIoCtxProg,
         StateTransitionSpec.clientResult] at hio_res ⊢
       try rw [hio_res]
       first | (rw [hmb]; exact hv.hdr_frontier)
             | (rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid))
    | exact hpre
    | (exfalso; exact absurd hm0 (by assumption))
    | (exfalso; exact hmne (by assumption))))

/-- Exact specification of `epochInsertProg` in the small regime (`N = 0`). -/
theorem epochInsertProg_spec_small {L : SmallEpochLayout} {w pBase : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hdisj : ∀ a, pBase ≤ a → a < pBase + 64 → ¬L.OwnsAddr a)
    (hinv : L.StateInv 0 s.mem s_abs) (u : Fin L.U) (v : Fin L.V)
    (hcap_new : s_abs u = none →
      s.mem (L.metaBase + 1) < L.io.pgL.nCap ∧
      (L.io.usePaged ≠ 0 → (extractPagePair L.io.pgL s.mem).totalItems + 1 ≤ L.io.pgL.nCap)) :
    let s' := (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val))
    let slack' :=
      if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    memoryCost (epochInsertProg ((pBase, u.val), v.val)) s ≤
      21 * s.mem (L.metaBase + 1) + 1430 ∧
    L.ParamTable pBase s'.mem ∧
    L.StateInv slack' s'.mem (Function.update s_abs u (some v)) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (L.io.usePaged ≠ 0 →
      (extractPagePair L.io.pgL s'.mem).virtLen L.io.partner.side =
        (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side ∧
      ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
        slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  obtain ⟨hfr, hcost, hinv', hout, hpg⟩ := smallEpochInsertProg_spec hv hinv u v hcap_new
  have hio := clientResult_loadSmallIoCtxProg (s := s) hpt
  have hm := memoryCost_loadSmallIoCtxProg pBase s
  have hstep : (Memory.spec 0).clientState s (epochInsertProg ((pBase, u.val), v.val)) =
      (Memory.spec 0).clientState s (smallEpochInsertProg L u.val v.val) := by
    unfold epochInsertProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, hio]
    rfl
  have hmc : memoryCost (epochInsertProg ((pBase, u.val), v.val)) s ≤
      21 * s.mem (L.metaBase + 1) + 1430 := by
    unfold epochInsertProg
    rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.1, ite_eq_left rfl,
      Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.2.1,
      Realization.memoryCost_bind', clientState_loadSmallIoCtxProg, hm, hio]
    change 1 + (1 + (13 + memoryCost (smallEpochInsertProg L u.val v.val) s)) ≤ _
    omega
  rw [hstep]
  exact ⟨hfr, hmc, hpt.congr fun a h1 h2 => hout a (hdisj a h1 h2), hinv', hout, hpg⟩

/-- Exact specification of `epochInsertProg` in the large regime (`whpThreshold c ≤ N`). -/
theorem epochInsertProg_spec_large {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs) (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : s_abs u = none →
      (s.mem (fl.metaBase + 2) = 0 →
        (extractBlockPool fl.mp s.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem) ∧
      (s.mem (fl.metaBase + 2) = 1 →
        (extractFallback fl.mp s.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractFallback fl.mp s.mem).nSide s.mem)) :
    let s' := (Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u.val), v.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    LargeEpochInv fl slack' seeds s'.mem (Function.update s_abs u (some v)) ∧
    (s'.mem (fl.metaBase + 2) = 0 →
      memoryCost (epochInsertProg ((fl.pBase, u.val), v.val)) s ≤ epochStepCost fl.c) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems + 1
         else (extractPagePair fl.io.pgL s.mem).totalItems) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hinv.1 0 (by decide)
  obtain ⟨hfr, hl, hc, hof, hpg⟩ := largeEpochInsertProg_spec hv hinv u v hcap_new
  have hstep : (Memory.spec 0).clientState s (epochInsertProg ((fl.pBase, u.val), v.val)) =
      (Memory.spec 0).clientState s (largeEpochInsertProg ((fl.pBase, u.val), v.val)) := by
    unfold epochInsertProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  rw [hstep]
  refine ⟨hfr, hl, fun hm => ?_, hof, hpg⟩
  unfold epochInsertProg
  rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
    prog_memoryCost_read, hm0, ite_eq_right hN_pos.ne']
  have hcl := hc hm
  unfold epochStepCost
  have hle := le_max_right (smallStepCost fl.c) (largeFastStepCost fl.c)
  omega

/-- Unified `pBase`-addressed `delete(u)` dispatching small vs large (`¬ReadsWidth`). -/
def epochDeleteProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, u_val) => do
    let nCap ← Memory.read pBase
    if nCap = 0 then do
      let mb ← Memory.read (pBase + 1)
      let ioctx ← loadSmallIoCtxProg pBase
      smallEpochDeleteRawProg ((ioctx, mb), u_val)
    else
      largeEpochDeleteProg (pBase, u_val)

theorem realizesBounded_epochDelete :
    RealizesBounded .exact epochDeleteProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => EpochProgPre w pBase s) (fun _ _ => 0) := by
  have hli := realizesBounded_loadSmallIoCtx
  have hsd := realizesBounded_smallEpochDeleteRaw
  have hld := realizesBounded_largeEpochDelete
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨hw6, hp⟩ := epochProgPre_bounds h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    first | omega | (rcases h with ⟨hm0, L, _, _, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩ <;> first
    | (have hmb : s.mem (pBase + 1) = L.metaBase := hpt.2.1
       have hio_res := clientResult_loadSmallIoCtxProg (s := s) hpt
       simp only [StateTransitionSpec.clientState, runClient_state_loadSmallIoCtxProg,
         StateTransitionSpec.clientResult] at hio_res ⊢
       try rw [hio_res]
       first | (rw [hmb]; exact hv.hdr_frontier)
             | (rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid))
    | exact ⟨fl, rfl, hr⟩
    | (exfalso; exact absurd hm0 (by assumption))
    | (exfalso; exact hmne (by assumption))))

/-- Exact specification of `epochDeleteProg` in the small regime (`N = 0`). -/
theorem epochDeleteProg_spec_small {L : SmallEpochLayout} {w pBase : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hdisj : ∀ a, pBase ≤ a → a < pBase + 64 → ¬L.OwnsAddr a)
    (hinv : L.StateInv 0 s.mem s_abs) (u : Fin L.U) :
    let s' := (Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val))
    let slack' :=
      if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    memoryCost (epochDeleteProg (pBase, u.val)) s ≤ 21 * s.mem (L.metaBase + 1) + 1520 ∧
    L.ParamTable pBase s'.mem ∧
    L.StateInv slack' s'.mem (Function.update s_abs u none) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (L.io.usePaged ≠ 0 →
      (extractPagePair L.io.pgL s'.mem).virtLen L.io.partner.side =
        (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side ∧
      ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
        slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  obtain ⟨hfr, hcost, hinv', hout, hpg⟩ := smallEpochDeleteProg_spec hv hinv u
  have hio := clientResult_loadSmallIoCtxProg (s := s) hpt
  have hm := memoryCost_loadSmallIoCtxProg pBase s
  have hstep : (Memory.spec 0).clientState s (epochDeleteProg (pBase, u.val)) =
      (Memory.spec 0).clientState s (smallEpochDeleteProg L u.val) := by
    unfold epochDeleteProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, hio]
    rfl
  have hmc : memoryCost (epochDeleteProg (pBase, u.val)) s ≤
      21 * s.mem (L.metaBase + 1) + 1520 := by
    unfold epochDeleteProg
    rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.1, ite_eq_left rfl,
      Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.2.1,
      Realization.memoryCost_bind', clientState_loadSmallIoCtxProg, hm, hio]
    change 1 + (1 + (13 + memoryCost (smallEpochDeleteProg L u.val) s)) ≤ _
    omega
  rw [hstep]
  exact ⟨hfr, hmc, hpt.congr fun a h1 h2 => hout a (hdisj a h1 h2), hinv', hout, hpg⟩

/-- Exact specification of `epochDeleteProg` in the large regime (`whpThreshold c ≤ N`). -/
theorem epochDeleteProg_spec_large {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs) (u : Fin fl.U) :
    let s' := (Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    LargeEpochInv fl slack' seeds s'.mem (Function.update s_abs u none) ∧
    (s.mem (fl.metaBase + 2) = 0 →
      s'.mem (fl.metaBase + 2) = 0 ∧
      memoryCost (epochDeleteProg (fl.pBase, u.val)) s ≤ epochStepCost fl.c) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems
         else (extractPagePair fl.io.pgL s.mem).totalItems - 1) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hinv.1 0 (by decide)
  obtain ⟨hfr, hl, hfast, hof, hpg⟩ := largeEpochDeleteProg_spec hv hinv u
  have hstep : (Memory.spec 0).clientState s (epochDeleteProg (fl.pBase, u.val)) =
      (Memory.spec 0).clientState s (largeEpochDeleteProg (fl.pBase, u.val)) := by
    unfold epochDeleteProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  rw [hstep]
  refine ⟨hfr, hl, fun hm => ⟨(hfast hm).1, ?_⟩, hof, hpg⟩
  unfold epochDeleteProg
  rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
    prog_memoryCost_read, hm0, ite_eq_right hN_pos.ne']
  have hcl := (hfast hm).2
  unfold epochStepCost
  have hle := le_max_right (smallStepCost fl.c) (largeFastStepCost fl.c)
  omega

/-- Unified `pBase`-addressed `popAny` dispatching small vs large (`¬ReadsWidth`). -/
def epochPopAnyProg (pBase : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let nCap ← Memory.read pBase
  if nCap = 0 then do
    let mb ← Memory.read (pBase + 1)
    let ioctx ← loadSmallIoCtxProg pBase
    smallEpochPopAnyRawProg (ioctx, mb)
  else
    largeEpochPopAnyProg pBase

theorem realizesBounded_epochPopAny :
    RealizesBounded .exact epochPopAnyProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w pBase s => EpochProgPre w pBase s) (fun _ _ => 0) := by
  have hli := realizesBounded_loadSmallIoCtx
  have hsp := realizesBounded_smallEpochPopAnyRaw
  have hlp := realizesBounded_largeEpochPopAny
  realize
  all_goals (
    obtain ⟨hw6, hp⟩ := epochProgPre_bounds h
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    first | omega | (rcases h with ⟨hm0, L, _, _, hv, hpt⟩ | ⟨hmne, fl, rfl, hr⟩ <;> first
    | (have hmb : s.mem (d + 1) = L.metaBase := hpt.2.1
       have hio_res := clientResult_loadSmallIoCtxProg (s := s) hpt
       simp only [StateTransitionSpec.clientState, runClient_state_loadSmallIoCtxProg,
         StateTransitionSpec.clientResult] at hio_res ⊢
       try rw [hio_res]
       first | (rw [hmb]; exact hv.hdr_frontier)
             | (rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid))
    | exact ⟨fl, rfl, hr⟩
    | (exfalso; exact absurd hm0 (by assumption))
    | (exfalso; exact hmne (by assumption))))

/-- Exact specification of `epochPopAnyProg` in the small regime (`N = 0`, `0 < nSide`). -/
theorem epochPopAnyProg_spec_small {L : SmallEpochLayout} {w pBase : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hpt : L.ParamTable pBase s.mem)
    (hdisj : ∀ a, pBase ≤ a → a < pBase + 64 → ¬L.OwnsAddr a)
    (hinv : L.StateInv 0 s.mem s_abs) (hpos : 0 < s.mem (L.metaBase + 1)) :
    let res := (Memory.spec 0).clientResult s (epochPopAnyProg pBase)
    let s' := (Memory.spec 0).clientState s (epochPopAnyProg pBase)
    let slack' :=
      if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    ∃ (u : Fin L.U) (v : Fin L.V),
      res = (u.val, v.val) ∧ s_abs u = some v ∧
      s'.frontier = s.frontier ∧
      memoryCost (epochPopAnyProg pBase) s ≤ 1450 ∧
      L.ParamTable pBase s'.mem ∧
      s'.mem (L.metaBase + 1) = s.mem (L.metaBase + 1) - 1 ∧
      L.StateInv slack' s'.mem (Function.update s_abs u none) ∧
      (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
      (L.io.usePaged ≠ 0 →
        (extractPagePair L.io.pgL s'.mem).virtLen L.io.partner.side =
          (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side ∧
        (extractPagePair L.io.pgL s'.mem).totalItems =
          (extractPagePair L.io.pgL s.mem).totalItems - 1 ∧
        ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
          slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  obtain ⟨hfr, hcost, hns, ⟨u, v, hres, hsu, hinv'⟩, hout, hpg⟩ :=
    smallEpochPopAnyProg_spec hv hinv hpos
  have hio := clientResult_loadSmallIoCtxProg (s := s) hpt
  have hm := memoryCost_loadSmallIoCtxProg pBase s
  have hstep : (Memory.spec 0).clientState s (epochPopAnyProg pBase) =
      (Memory.spec 0).clientState s (smallEpochPopAnyProg L) := by
    unfold epochPopAnyProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, StateTransitionSpec.clientState_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, StateTransitionSpec.clientState_bind,
      clientState_loadSmallIoCtxProg, hio]
    rfl
  have hre : (Memory.spec 0).clientResult s (epochPopAnyProg pBase) =
      (Memory.spec 0).clientResult s (smallEpochPopAnyProg L) := by
    unfold epochPopAnyProg
    rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read,
      hpt.1, ite_eq_left rfl, prog_clientResult_bind, clientState_read_eq,
      prog_clientResult_read, hpt.2.1, prog_clientResult_bind,
      clientState_loadSmallIoCtxProg, hio]
    rfl
  have hmc : memoryCost (epochPopAnyProg pBase) s ≤ 1450 := by
    unfold epochPopAnyProg
    rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.1, ite_eq_left rfl,
      Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
      prog_memoryCost_read, hpt.2.1,
      Realization.memoryCost_bind', clientState_loadSmallIoCtxProg, hm, hio]
    change 1 + (1 + (13 + memoryCost (smallEpochPopAnyProg L) s)) ≤ _
    omega
  rw [hstep, hre]
  exact ⟨u, v, hres, hsu, hfr, hmc,
    hpt.congr fun a h1 h2 => hout a (hdisj a h1 h2), hns, hinv', hout, hpg⟩

/-- Exact specification of `epochPopAnyProg` in the large regime (`whpThreshold c ≤ N`). -/
theorem epochPopAnyProg_spec_large {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs)
    (hpos : (s.mem (fl.metaBase + 2) = 0 → 0 < (extractBlockPool fl.mp s.mem).nSide) ∧
      (s.mem (fl.metaBase + 2) = 1 → 0 < (extractFallback fl.mp s.mem).nSide)) :
    let res := (Memory.spec 0).clientResult s (epochPopAnyProg fl.pBase)
    let s' := (Memory.spec 0).clientState s (epochPopAnyProg fl.pBase)
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    ∃ (u : Fin fl.U) (v : Fin fl.V),
      res = (u.val, v.val) ∧ s_abs u = some v ∧
      s'.frontier = s.frontier ∧
      LargeEpochInv fl slack' seeds s'.mem (Function.update s_abs u none) ∧
      (s.mem (fl.metaBase + 2) = 0 →
        s'.mem (fl.metaBase + 2) = 0 ∧
        memoryCost (epochPopAnyProg fl.pBase) s ≤ epochStepCost fl.c) ∧
      (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
      (fl.io.usePaged ≠ 0 →
        (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
          (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
        (extractPagePair fl.io.pgL s'.mem).totalItems =
          (extractPagePair fl.io.pgL s.mem).totalItems - 1 ∧
        ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
          slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
  have hm0 : s.mem fl.pBase = fl.N := hinv.1 0 (by decide)
  obtain ⟨u, v, hres, hsu, hfr, hl, hfast, hof, hpg⟩ := largeEpochPopAnyProg_spec hv hinv hpos
  have hstep : (Memory.spec 0).clientState s (epochPopAnyProg fl.pBase) =
      (Memory.spec 0).clientState s (largeEpochPopAnyProg fl.pBase) := by
    unfold epochPopAnyProg
    rw [StateTransitionSpec.clientState_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  have hre : (Memory.spec 0).clientResult s (epochPopAnyProg fl.pBase) =
      (Memory.spec 0).clientResult s (largeEpochPopAnyProg fl.pBase) := by
    unfold epochPopAnyProg
    rw [prog_clientResult_bind, clientState_read_eq, prog_clientResult_read,
      hm0, ite_eq_right hN_pos.ne']
  rw [hstep, hre]
  refine ⟨u, v, hres, hsu, hfr, hl, fun hm => ⟨(hfast hm).1, ?_⟩, hof, hpg⟩
  unfold epochPopAnyProg
  rw [Realization.memoryCost_bind', clientState_read_eq, prog_clientResult_read,
    prog_memoryCost_read, hm0, ite_eq_right hN_pos.ne']
  have hcl := (hfast hm).2
  unfold epochStepCost
  have hle := le_max_right (smallStepCost fl.c) (largeFastStepCost fl.c)
  omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

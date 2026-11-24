/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.ValidHistoryPage
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.ValidHistoryBpMeta
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.ValidHistoryTree
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochCtx
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochState
-- Private fallback pool helpers shared across the LargeFallbackBase/LargeEpochFallback split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeFallbackBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochFallback
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochCtx

/-!
# Memory History Admissibility (`ValidHistory`) for Block-Pool, Fallback, and Fast-Epoch Context

This module proves `(Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)` for every
public `Memory.Prog` operation exported by `LargeBlockPool`, the fallback-pool primitives of
`LargeEpochState`, `LargeFallbackBase`, `LargeEpochFallback`, and `LargeEpochCtx` (`SlotIoLayout`
and `smallEpoch*` programs are already proved in `ValidHistoryPage`).

It uses private `import all` solely to unfold the unexposed `Memory.Prog` bodies of
`LargeBlockPool`, `LargeEpochState`, `LargeFallbackBase`, `LargeEpochFallback`, and
`LargeEpochCtx` without modifying any existing module.

## Main results

* `validHistory_bpInitProg`, `validHistory_bpReadAtRawProg`, `validHistory_bpWriteAtRawProg`,
  `validHistory_bpAppendRawProg`, `validHistory_bpPopBktBackRawProg`: block-pool operations
  (`LargeBlockPool`; the `@[expose]` wrappers `bpReadAtProg`, `bpWriteAtProg`, `bpAppendProg`, and
  `bpPopBktBackProg` are definitionally equal to the `*RawProg` forms).
* `validHistory_fbOwnerOfProg`, `validHistory_fbScanStepProg`, `validHistory_fbScanLoopProg`,
  `validHistory_fbScanProg`, `validHistory_fbSwapRangeStepProg`,
  `validHistory_fbSwapRangeLoopProg`, `validHistory_fbSwapRangeProg`,
  `validHistory_fbFindHeavyBktLoopProg`, `validHistory_fbFindMatchLoopProg`,
  `validHistory_fbSwapTailSlotsProg`, `validHistory_fbPartHeavyStepProg`,
  `validHistory_fbPartHeavyLoopProg`, `validHistory_fbShiftLeftStepProg`,
  `validHistory_fbShiftLeftLoopProg`, `validHistory_fbPromoteFinishProg`,
  `validHistory_fbPromoteBodyProg`, `validHistory_fbPromoteInnerCheckProg`,
  `validHistory_fbPromoteCheckProg`, `validHistory_fbPromoteOneBlockProg`: fallback-pool state
  primitives (`LargeEpochState`).
* `validHistory_fbMaybePromoteProg`, `validHistory_fbDemoteBlkProg`,
  `validHistory_fbPopTailAtProg`, `validHistory_fbDeleteSlotProg`,
  `validHistory_enterFallbackProg`, `validHistory_fallbackQueryProg`,
  `validHistory_fallbackInsertProg`, `validHistory_fallbackDeleteProg`,
  `validHistory_fallbackPopAnyProg`: fallback-pool operations (`LargeFallbackBase`,
  `LargeEpochFallback`).
* `validHistory_loadBpMetaCtxProg`, `validHistory_loadSlotIoCtxProg`,
  `validHistory_loadBlockPoolCtxProg`, `validHistory_loadHashStaticCtxProg`,
  `validHistory_loadTrieCtxProg`, `validHistory_loadBTreeSliceCtxProg`,
  `validHistory_fastFeistelSplitProg`, `validHistory_fastFeistelReconProg`,
  `validHistory_fastRKeyProg`, `validHistory_fastFpHashProg`, `validHistory_fastReadMetaProg`,
  `validHistory_fastWriteMetaProg`, `validHistory_fastReadBktLaneProg`,
  `validHistory_fastWriteBktLaneProg`, `validHistory_fastBpReadAtProg`,
  `validHistory_fastBpBktCountProg`, `validHistory_fastProbeProg`, `validHistory_fastQueryProg`:
  fast-epoch context loaders, hash evaluators, and read-only probe (`LargeEpochCtx`).
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

/-! ## Section 1: Generic `ValidHistory` Combinators -/

private theorem wellFormed_clientState {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact hwf.run hp

private theorem frontier_le_clientState {α : Type} {s : Memory.State} (p : Memory.Prog α) :
    s.frontier ≤ ((Memory.spec 0).clientState s p).frontier := by
  rw [← (Memory.spec 0).run_runClient p s]
  exact Memory.frontier_le_run s _

private theorem validHistory_bind_eq {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : (Memory.spec w).ValidHistory ((Memory.spec 0).clientState s p)
      ((Memory.spec w).clientHistory ((Memory.spec 0).clientState s p)
        (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq⟩

private theorem validHistory_bind_same {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hst : (Memory.spec 0).clientState s p = s)
    (hq : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (q ((Memory.spec 0).clientResult s p)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  refine validHistory_bind_eq hp ?_
  rwa [hst]

private theorem validHistory_bind_ro {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_eq hp (hq _ _ (frontier_le_clientState p))

private theorem validHistory_bind_wf {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_eq hp (hq _ _ (wellFormed_clientState hwf hp) (frontier_le_clientState p))

private theorem validHistory_read_bind {α : Type} {w a : ℕ} {s : Memory.State}
    {q : ℕ → Memory.Prog α} (ha : a < s.frontier)
    (hq : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (q (s.mem a)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (Memory.read a >>= q)) :=
  validHistory_bind_eq ⟨ha, trivial⟩ hq

private theorem validHistory_ite {α : Type} {w : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₁))
    (h₂ : ¬c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₂)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (if c then p₁ else p₂)) := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

private theorem bpMetaValid_mono {mp : BpMetaLayout} {w f₁ f₂ : ℕ}
    (h : mp.Valid w f₁) (hle : f₁ ≤ f₂) : mp.Valid w f₂ :=
  { h with frontier_ge := h.frontier_ge.trans hle }

private theorem pageArenaValid_mono {L : PageArenaLayout} {w f₁ f₂ : ℕ}
    (hv : L.Valid w f₁) (hle : f₁ ≤ f₂) : L.Valid w f₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hv
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15.trans hle⟩

private theorem slotIoValid_mono {io : SlotIoLayout} {w f₁ f₂ : ℕ}
    (hv : io.Valid w f₁) (hle : f₁ ≤ f₂) : io.Valid w f₂ := by
  unfold SlotIoLayout.Valid at hv ⊢
  by_cases h0 : io.usePaged = 0
  · rw [ite_eq_left h0] at hv ⊢
    obtain ⟨h1, h2, h3, h4, h5, htail⟩ := hv
    refine ⟨h1, h2, h3, h4, h5, ?_⟩
    by_cases hs : io.sideBit = 0
    · rw [ite_eq_left hs] at htail ⊢; exact htail.trans hle
    · rw [ite_eq_right hs] at htail ⊢
      obtain ⟨ha, hb, hc, hd, he⟩ := htail
      exact ⟨ha, hb, hc, hd, he.trans hle⟩
  · rw [ite_eq_right h0] at hv ⊢
    exact pageArenaValid_mono hv hle

private theorem validHistory_bp_ro {α β : Type} {w : ℕ} {mctx : BpMetaCtx} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', (BpMetaLayout.ofCtx mctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_ro hp fun a s' hfr => hq a s' (bpMetaValid_mono hmv hfr)

private theorem validHistory_bp_wf {α β : Type} {w : ℕ} {mctx : BpMetaCtx} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s) (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → (BpMetaLayout.ofCtx mctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_wf hwf hp fun a s' hwf' hfr =>
    hq a s' hwf' (bpMetaValid_mono hmv hfr)

private theorem validHistory_pool_ro {α β : Type} {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', (BpMetaLayout.ofCtx mctx).Valid w s'.frontier →
      (SlotIoLayout.ofCtx ioctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_ro hp fun a s' hfr =>
    hq a s' (bpMetaValid_mono hmv hfr) (slotIoValid_mono hiov hfr)

private theorem validHistory_pool_wf {α β : Type} {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → (BpMetaLayout.ofCtx mctx).Valid w s'.frontier →
      (SlotIoLayout.ofCtx ioctx).Valid w s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) :=
  validHistory_bind_wf hwf hp fun a s' hwf' hfr =>
    hq a s' hwf' (bpMetaValid_mono hmv hfr) (slotIoValid_mono hiov hfr)

private theorem validHistory_iterate_ro {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {d : δ} (fuel : ℕ) (a : σ) (s : Memory.State)
    (hbody : ∀ a' s', s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (body (d, a')))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d fuel a)) := by
  induction fuel generalizing a s with
  | zero => exact trivial
  | succ k ih =>
    unfold iterate
    exact validHistory_bind_ro (hbody a s le_rfl) fun a' s' hfr' =>
      ih a' s' fun a'' s'' hfr'' => hbody a'' s'' (hfr'.trans hfr'')

private theorem validHistory_iterate_wf {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {d : δ} (fuel : ℕ) (a : σ) (s : Memory.State)
    (hwf : Memory.WellFormed w s)
    (hbody : ∀ a' s', Memory.WellFormed w s' → s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (body (d, a')))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d fuel a)) := by
  induction fuel generalizing a s with
  | zero => exact trivial
  | succ k ih =>
    unfold iterate
    exact validHistory_bind_wf hwf (hbody a s hwf le_rfl) fun a' s' hwf' hfr' =>
      ih a' s' hwf' fun a'' s'' hwf'' hfr'' => hbody a'' s'' hwf'' (hfr'.trans hfr'')

/-! ## Section 2: `LargeBlockPool` `ValidHistory` Proofs -/

private theorem validHistory_bpExecOptSwapProg {w : ℕ} {ioctx : SlotIoCtx}
    {osw : ℕ × (ℕ × ℕ)} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpExecOptSwapProg (ioctx, osw))) := by
  rcases osw with ⟨hasSw, ⟨p₁, p₂⟩⟩
  unfold bpExecOptSwapProg
  exact validHistory_ite (fun _ => trivial) fun _ => validHistory_slotIoSwapRawProg hwf hiov

private theorem validHistory_bpBktTickStepProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpBktTickStepProg ((mctx, ioctx), b))) := by
  unfold bpBktTickStepProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpBktTickMetaProg hwf hmv)
    fun _ _ hwf' _ hiov' => validHistory_bpExecOptSwapProg hwf' hiov'

private theorem validHistory_bpRunBktTicks2Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunBktTicks2Prog ((mctx, ioctx), b))) := by
  unfold bpRunBktTicks2Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpBktTickStepProg hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpBktTickStepProg hwf' hmv' hiov'

private theorem validHistory_bpRunBktTicks4Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunBktTicks4Prog ((mctx, ioctx), b))) := by
  unfold bpRunBktTicks4Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpRunBktTicks2Prog hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpRunBktTicks2Prog hwf' hmv' hiov'

private theorem validHistory_bpRunBktTicks8Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunBktTicks8Prog ((mctx, ioctx), b))) := by
  unfold bpRunBktTicks8Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpRunBktTicks4Prog hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpRunBktTicks4Prog hwf' hmv' hiov'

private theorem validHistory_bpRunBktTicks16Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunBktTicks16Prog ((mctx, ioctx), b))) := by
  unfold bpRunBktTicks16Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpRunBktTicks8Prog hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpRunBktTicks8Prog hwf' hmv' hiov'

private theorem validHistory_bpTopCleanStepProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpTopCleanStepProg (mctx, ioctx))) := by
  unfold bpTopCleanStepProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpTopCleanMetaProg hwf hmv)
    fun _ _ hwf' _ hiov' => validHistory_bpExecOptSwapProg hwf' hiov'

private theorem validHistory_bpRunTopClean2Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunTopClean2Prog (mctx, ioctx))) := by
  unfold bpRunTopClean2Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpTopCleanStepProg hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpTopCleanStepProg hwf' hmv' hiov'

private theorem validHistory_bpRunTopClean4Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunTopClean4Prog (mctx, ioctx))) := by
  unfold bpRunTopClean4Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpRunTopClean2Prog hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpRunTopClean2Prog hwf' hmv' hiov'

private theorem validHistory_bpRunTopClean8Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunTopClean8Prog (mctx, ioctx))) := by
  unfold bpRunTopClean8Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpRunTopClean4Prog hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpRunTopClean4Prog hwf' hmv' hiov'

private theorem validHistory_bpRunTopClean16Prog {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpRunTopClean16Prog (mctx, ioctx))) := by
  unfold bpRunTopClean16Prog
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpRunTopClean8Prog hwf hmv hiov)
    fun _ _ hwf' hmv' hiov' => validHistory_bpRunTopClean8Prog hwf' hmv' hiov'

/-- Memory history admissibility for `bpInitProg` under `bpL.mp.Valid`. -/
theorem validHistory_bpInitProg {w : ℕ} {bpL : BlockPoolLayout} {s : Memory.State}
    (hmv : bpL.mp.Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bpInitProg bpL)) := by
  unfold bpInitProg
  exact validHistory_bpInitZeroedProg (by rwa [BpMetaLayout.ofCtx_toCtx])

/-- Memory history admissibility for `bpReadAtRawProg` (and `@[expose]` `bpReadAtProg`;
read-only). -/
theorem validHistory_bpReadAtRawProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b loc : ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpReadAtRawProg ((mctx, ioctx), (b, loc)))) := by
  unfold bpReadAtRawProg
  exact validHistory_pool_ro hmv hiov (validHistory_bpToPhysProg hmv)
    fun _ _ _ hiov' => validHistory_slotIoReadRawProg hiov'

/-- Memory history admissibility for `bpWriteAtRawProg` (and `@[expose]` `bpWriteAtProg`). -/
theorem validHistory_bpWriteAtRawProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b loc : ℕ} {qv : ℕ × ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpWriteAtRawProg (((mctx, ioctx), (b, loc)), qv))) := by
  unfold bpWriteAtRawProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpToPhysProg hmv)
    fun _ _ hwf' _ hiov' => validHistory_slotIoWriteRawProg hwf' hiov'

/-- Memory history admissibility for `bpAppendRawProg` (and `@[expose]` `bpAppendProg`). -/
theorem validHistory_bpAppendRawProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {qv : ℕ × ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpAppendRawProg (((mctx, ioctx), b), qv))) := by
  unfold bpAppendRawProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_slotIoAppendRawProg hwf₁ hiov₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  refine validHistory_pool_wf hwf₂ hmv₂ hiov₂ (validHistory_bpRawPostAppendMetaProg hwf₂ hmv₂)
    fun _ _ hwf₃ hmv₃ hiov₃ => ?_
  exact validHistory_bpRunBktTicks16Prog hwf₃ hmv₃ hiov₃

private theorem validHistory_bpPopBktPrepAndShrinkProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpPopBktPrepAndShrinkProg ((mctx, ioctx), b))) := by
  unfold bpPopBktPrepAndShrinkProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpPrepPopMetaProg hwf hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpExecOptSwapProg hwf₁ hiov₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  refine validHistory_pool_wf hwf₂ hmv₂ hiov₂ (validHistory_slotIoPopBackRawProg hwf₂ hiov₂)
    fun _ _ hwf₃ hmv₃ _ => ?_
  exact validHistory_bpCommitPopMetaProg hwf₃ hmv₃

/-- Memory history admissibility for `bpPopBktBackRawProg` (and `@[expose]` `bpPopBktBackProg`). -/
theorem validHistory_bpPopBktBackRawProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bpPopBktBackRawProg ((mctx, ioctx), b))) := by
  unfold bpPopBktBackRawProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpPopBktPrepAndShrinkProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpRunBktTicks16Prog hwf₁ hmv₁ hiov₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_bpRunTopClean16Prog hwf₂ hmv₂ hiov₂

/-! ## Section 3: `LargeEpochState` Fallback Primitives `ValidHistory` Proofs -/

/-- Memory history admissibility for `fbOwnerOfProg` (read-only). -/
theorem validHistory_fbOwnerOfProg {w : ℕ} {mctx : BpMetaCtx} {p : ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbOwnerOfProg (mctx, p))) := by
  have hmk : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbOwnerOfProg.bpGetMKFromCtxProg mctx)) := by
    rcases mctx with ⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩; exact trivial
  have hcaps : ∀ s', (Memory.spec w).ValidHistory s'
      ((Memory.spec w).clientHistory s' (fbOwnerOfProg.bpGetNcapFromCtxProg mctx)) := by
    intro _; rcases mctx with ⟨_, ⟨_, ⟨_, _⟩⟩⟩; exact trivial
  unfold fbOwnerOfProg
  refine validHistory_bp_ro hmv hmk fun _ _ hmv₁ => ?_
  refine validHistory_bp_ro hmv₁ (hcaps _) fun _ _ hmv₂ => ?_
  refine validHistory_bp_ro hmv₂ (validHistory_bpReadScalarProg hmv₂) fun _ _ hmv₃ => ?_
  refine validHistory_bp_ro hmv₃ (validHistory_bpDivModKProg w _ _) fun _ _ hmv₄ => ?_
  refine validHistory_ite (fun _ => validHistory_bpReadSlabOwnerProg hmv₄) fun _ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bpReadTailDirRawProg hmv₄

/-- Memory history admissibility for `fbScanStepProg` (read-only). -/
theorem validHistory_fbScanStepProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {nSide bkt q_u : ℕ} {acc : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbScanStepProg (((mctx, ioctx), (nSide, (bkt, q_u))), acc))) := by
  rcases acc with ⟨⟨cur, found⟩, ⟨hitP, hitVal⟩⟩
  unfold fbScanStepProg
  refine validHistory_ite (fun _ => ?_) fun _ => ?_
  · refine validHistory_pool_ro hmv hiov (validHistory_fbOwnerOfProg hmv)
      fun _ _ _ hiov₁ => ?_
    refine validHistory_bind_ro (validHistory_slotIoReadRawProg hiov₁) fun _ _ _ => ?_
    exact validHistory_ite (fun _ => trivial) (fun _ => trivial)
  · exact validHistory_bind_ro (validHistory_bpReadScalarProg hmv) fun _ _ _ => trivial

/-- Memory history admissibility for `fbScanLoopProg` (read-only). -/
theorem validHistory_fbScanLoopProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {nSide bkt q_u fuel : ℕ} {acc : (ℕ × ℕ) × (ℕ × ℕ)} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbScanLoopProg ((((mctx, ioctx), (nSide, (bkt, q_u))), acc), fuel))) := by
  unfold fbScanLoopProg
  exact validHistory_iterate_ro fuel acc s fun _ _ hfr =>
    validHistory_fbScanStepProg (bpMetaValid_mono hmv hfr) (slotIoValid_mono hiov hfr)

/-- Memory history admissibility for `fbScanProg` (read-only). -/
theorem validHistory_fbScanProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {bkt q_u : ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbScanProg ((mctx, ioctx), (bkt, q_u)))) := by
  unfold fbScanProg
  refine validHistory_pool_ro hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hmv₁ hiov₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_fbScanLoopProg hmv₁ hiov₁) fun _ _ _ => trivial

/-- Memory history admissibility for `fbSwapRangeStepProg`. -/
theorem validHistory_fbSwapRangeStepProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b₁ b₂ cur : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbSwapRangeStepProg (((mctx, ioctx), (b₁, b₂)), cur))) := by
  unfold fbSwapRangeStepProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ _ hiov₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_slotIoSwapRawProg hwf₁ hiov₁) fun _ _ _ => trivial

/-- Memory history admissibility for `fbSwapRangeLoopProg`. -/
theorem validHistory_fbSwapRangeLoopProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b₁ b₂ cur fuel : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbSwapRangeLoopProg ((((mctx, ioctx), (b₁, b₂)), cur), fuel))) := by
  unfold fbSwapRangeLoopProg
  exact validHistory_iterate_wf fuel cur s hwf fun _ _ hwf' hfr =>
    validHistory_fbSwapRangeStepProg hwf' (bpMetaValid_mono hmv hfr) (slotIoValid_mono hiov hfr)

/-- Memory history admissibility for `fbSwapRangeProg`. -/
theorem validHistory_fbSwapRangeProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {b₁ b₂ len : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbSwapRangeProg (((mctx, ioctx), (b₁, b₂)), len))) := by
  unfold fbSwapRangeProg
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_fbSwapRangeLoopProg hwf hmv hiov) fun _ _ _ => trivial

private theorem validHistory_fbCountBktStepProg {w : ℕ} {mctx : BpMetaCtx}
    {tailLen b : ℕ} {acc : ℕ × ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCountBktStepProg ((mctx, (tailLen, b)), acc))) := by
  rcases acc with ⟨t, cnt⟩
  unfold fbCountBktStepProg
  refine validHistory_bp_ro hmv (validHistory_bpReadScalarProg hmv) fun _ _ hmv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_ro (validHistory_bpReadTailDirRawProg hmv₁) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_fbCountBktLoopProg {w : ℕ} {mctx : BpMetaCtx}
    {tailLen b fuel : ℕ} {acc : ℕ × ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCountBktLoopProg (((mctx, (tailLen, b)), acc), fuel))) := by
  unfold fbCountBktLoopProg
  exact validHistory_iterate_ro fuel acc s fun _ _ hfr =>
    validHistory_fbCountBktStepProg (bpMetaValid_mono hmv hfr)

private theorem validHistory_fbFindHeavyBktStepProg {w : ℕ} {mctx : BpMetaCtx}
    {tailLen : ℕ} {acc : ℕ × ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbFindHeavyBktStepProg ((mctx, tailLen), acc))) := by
  rcases acc with ⟨b, bStar⟩
  unfold fbFindHeavyBktStepProg
  refine validHistory_bp_ro hmv (validHistory_bpReadScalarProg hmv) fun _ _ hmv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_fbCountBktLoopProg hmv₁) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `fbFindHeavyBktLoopProg` (read-only). -/
theorem validHistory_fbFindHeavyBktLoopProg {w : ℕ} {mctx : BpMetaCtx}
    {tailLen fuel : ℕ} {acc : ℕ × ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbFindHeavyBktLoopProg (((mctx, tailLen), acc), fuel))) := by
  unfold fbFindHeavyBktLoopProg
  exact validHistory_iterate_ro fuel acc s fun _ _ hfr =>
    validHistory_fbFindHeavyBktStepProg (bpMetaValid_mono hmv hfr)

private theorem validHistory_fbFindMatchStepProg {w : ℕ} {mctx : BpMetaCtx}
    {tailLen bStar : ℕ} {acc : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbFindMatchStepProg ((mctx, (tailLen, bStar)), acc))) := by
  rcases acc with ⟨t, ⟨found, src⟩⟩
  unfold fbFindMatchStepProg
  refine validHistory_bp_ro hmv (validHistory_bpReadScalarProg hmv) fun _ _ hmv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_ro (validHistory_bpReadTailDirRawProg hmv₁) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

/-- Memory history admissibility for `fbFindMatchLoopProg` (read-only). -/
theorem validHistory_fbFindMatchLoopProg {w : ℕ} {mctx : BpMetaCtx}
    {tailLen bStar fuel : ℕ} {acc : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbFindMatchLoopProg (((mctx, (tailLen, bStar)), acc), fuel))) := by
  unfold fbFindMatchLoopProg
  exact validHistory_iterate_ro fuel acc s fun _ _ hfr =>
    validHistory_fbFindMatchStepProg (bpMetaValid_mono hmv hfr)

private theorem validHistory_fbReadTailPairProg {w : ℕ} {mctx : BpMetaCtx}
    {t₁ t₂ : ℕ} {s : Memory.State} (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbReadTailPairProg (mctx, (t₁, t₂)))) := by
  unfold fbReadTailPairProg
  refine validHistory_bp_ro hmv (validHistory_bpReadTailDirRawProg hmv) fun _ _ hmv₁ => ?_
  exact validHistory_bind_ro (validHistory_bpReadTailDirRawProg hmv₁) fun _ _ _ => trivial

private theorem validHistory_fbWriteTailPairProg {w : ℕ} {mctx : BpMetaCtx}
    {t₁ t₂ b₁ b₂ : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbWriteTailPairProg ((mctx, (t₁, t₂)), (b₁, b₂)))) := by
  unfold fbWriteTailPairProg
  exact validHistory_bp_wf hwf hmv (validHistory_bpWriteTailDirRawProg hwf hmv)
    fun _ _ hwf₁ hmv₁ => validHistory_bpWriteTailDirRawProg hwf₁ hmv₁

/-- Memory history admissibility for `fbSwapTailSlotsProg`. -/
theorem validHistory_fbSwapTailSlotsProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {fbBase t₁ t₂ : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbSwapTailSlotsProg (((mctx, ioctx), fbBase), (t₁, t₂)))) := by
  unfold fbSwapTailSlotsProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_pool_wf hwf hmv hiov (validHistory_fbReadTailPairProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  exact validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_slotIoSwapRawProg hwf₁ hiov₁)
    fun _ _ hwf₂ hmv₂ _ => validHistory_fbWriteTailPairProg hwf₂ hmv₂

/-- Memory history admissibility for `fbPartHeavyStepProg`. -/
theorem validHistory_fbPartHeavyStepProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {fbBase tailLen bStar dst : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPartHeavyStepProg (((mctx, ioctx), (fbBase, (tailLen, bStar))), dst))) := by
  unfold fbPartHeavyStepProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_fbFindMatchLoopProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_bind_ro (validHistory_fbSwapTailSlotsProg hwf₂ hmv₂ hiov₂)
    fun _ _ _ => trivial

/-- Memory history admissibility for `fbPartHeavyLoopProg`. -/
theorem validHistory_fbPartHeavyLoopProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {fbBase tailLen bStar dst fuel : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPartHeavyLoopProg ((((mctx, ioctx), (fbBase, (tailLen, bStar))), dst), fuel))) := by
  unfold fbPartHeavyLoopProg
  exact validHistory_iterate_wf fuel dst s hwf fun _ _ hwf' hfr =>
    validHistory_fbPartHeavyStepProg hwf' (bpMetaValid_mono hmv hfr) (slotIoValid_mono hiov hfr)

/-- Memory history admissibility for `fbShiftLeftStepProg`. -/
theorem validHistory_fbShiftLeftStepProg {w : ℕ} {mctx : BpMetaCtx} {k t : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbShiftLeftStepProg ((mctx, k), t))) := by
  unfold fbShiftLeftStepProg
  refine validHistory_bp_wf hwf hmv (validHistory_bpReadScalarProg hmv) fun _ _ hwf₁ hmv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bp_wf hwf₁ hmv₁ (validHistory_bpReadTailDirRawProg hmv₁)
    fun _ _ hwf₂ hmv₂ => ?_
  exact validHistory_bind_ro (validHistory_bpWriteTailDirRawProg hwf₂ hmv₂) fun _ _ _ => trivial

/-- Memory history admissibility for `fbShiftLeftLoopProg`. -/
theorem validHistory_fbShiftLeftLoopProg {w : ℕ} {mctx : BpMetaCtx} {k t fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbShiftLeftLoopProg (((mctx, k), t), fuel))) := by
  unfold fbShiftLeftLoopProg
  exact validHistory_iterate_wf fuel t s hwf fun _ _ hwf' hfr =>
    validHistory_fbShiftLeftStepProg hwf' (bpMetaValid_mono hmv hfr)

/-- Memory history admissibility for `fbPromoteFinishProg`. -/
theorem validHistory_fbPromoteFinishProg {w : ℕ} {mctx : BpMetaCtx} {fb0 tailLen bStar : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPromoteFinishProg ((mctx, (fb0, tailLen)), bStar))) := by
  unfold fbPromoteFinishProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bp_wf hwf hmv (validHistory_bpWriteSlabOwnerProg hwf hmv)
    fun _ _ hwf₁ hmv₁ => ?_
  simp only [pure_bind]
  exact validHistory_bp_wf hwf₁ hmv₁ (validHistory_fbShiftLeftLoopProg hwf₁ hmv₁)
    fun _ _ _ hmv₂ => validHistory_bpWriteScalarProg hmv₂

/-- Memory history admissibility for `fbPromoteBodyProg`. -/
theorem validHistory_fbPromoteBodyProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {fb0 fbBase tailLen : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPromoteBodyProg (((mctx, ioctx), (fb0, fbBase)), tailLen))) := by
  unfold fbPromoteBodyProg
  simp only [pure_bind]
  refine validHistory_pool_wf hwf hmv hiov (validHistory_fbFindHeavyBktLoopProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  exact validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_fbPartHeavyLoopProg hwf₁ hmv₁ hiov₁)
    fun _ _ hwf₂ hmv₂ _ => validHistory_fbPromoteFinishProg hwf₂ hmv₂

/-- Memory history admissibility for `fbPromoteInnerCheckProg`. -/
theorem validHistory_fbPromoteInnerCheckProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {fb0 nSide fbBase : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPromoteInnerCheckProg (((mctx, ioctx), fb0), (nSide, fbBase)))) := by
  unfold fbPromoteInnerCheckProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_fbPromoteBodyProg hwf hmv hiov

/-- Memory history admissibility for `fbPromoteCheckProg`. -/
theorem validHistory_fbPromoteCheckProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {nSide fb0 : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPromoteCheckProg ((mctx, ioctx), (nSide, fb0)))) := by
  unfold fbPromoteCheckProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_fbPromoteInnerCheckProg hwf hmv hiov

/-- Memory history admissibility for `fbPromoteOneBlockProg`. -/
theorem validHistory_fbPromoteOneBlockProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbPromoteOneBlockProg (mctx, ioctx))) := by
  unfold fbPromoteOneBlockProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_fbPromoteCheckProg hwf₂ hmv₂ hiov₂

/-! ## Section 4: `LargeEpochFallback` `ValidHistory` Proofs -/

private theorem validHistory_fbMaybePromoteInnerProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {nSide fbBase : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbMaybePromoteInnerProg ((mctx, ioctx), (nSide, fbBase)))) := by
  unfold fbMaybePromoteInnerProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_ite (fun _ => validHistory_fbPromoteOneBlockProg hwf hmv hiov)
    (fun _ => trivial)

private theorem validHistory_fbMaybePromoteCheckProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {nSide fb0 : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbMaybePromoteCheckProg ((mctx, ioctx), (nSide, fb0)))) := by
  unfold fbMaybePromoteCheckProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_fbMaybePromoteInnerProg hwf hmv hiov

/-- Memory history admissibility for `fbMaybePromoteProg`. -/
theorem validHistory_fbMaybePromoteProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbMaybePromoteProg (mctx, ioctx))) := by
  unfold fbMaybePromoteProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_fbMaybePromoteCheckProg hwf₂ hmv₂ hiov₂

private theorem validHistory_fbShiftRightStepProg {w : ℕ} {mctx : BpMetaCtx} {k rem : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbShiftRightStepProg ((mctx, k), rem))) := by
  unfold fbShiftRightStepProg
  refine validHistory_bp_wf hwf hmv (validHistory_bpReadScalarProg hmv) fun _ _ hwf₁ hmv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bp_wf hwf₁ hmv₁ (validHistory_bpReadTailDirRawProg hmv₁)
    fun _ _ hwf₂ hmv₂ => ?_
  exact validHistory_bind_ro (validHistory_bpWriteTailDirRawProg hwf₂ hmv₂) fun _ _ _ => trivial

private theorem validHistory_fbShiftRightLoopProg {w : ℕ} {mctx : BpMetaCtx} {k rem fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbShiftRightLoopProg (((mctx, k), rem), fuel))) := by
  unfold fbShiftRightLoopProg
  exact validHistory_iterate_wf fuel rem s hwf fun _ _ hwf' hfr =>
    validHistory_fbShiftRightStepProg hwf' (bpMetaValid_mono hmv hfr)

private theorem validHistory_fbFillHeadStepProg {w : ℕ} {mctx : BpMetaCtx} {b_val i : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbFillHeadStepProg ((mctx, b_val), i))) := by
  unfold fbFillHeadStepProg
  refine validHistory_bp_wf hwf hmv (validHistory_bpReadScalarProg hmv) fun _ _ hwf₁ hmv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_bind_ro (validHistory_bpWriteTailDirRawProg hwf₁ hmv₁) fun _ _ _ => trivial

private theorem validHistory_fbFillHeadLoopProg {w : ℕ} {mctx : BpMetaCtx} {b_val i fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbFillHeadLoopProg (((mctx, b_val), i), fuel))) := by
  unfold fbFillHeadLoopProg
  exact validHistory_iterate_wf fuel i s hwf fun _ _ hwf' hfr =>
    validHistory_fbFillHeadStepProg hwf' (bpMetaValid_mono hmv hfr)

private theorem validHistory_fbReadBlkPairProg {w : ℕ} {mctx : BpMetaCtx} {blk₁ blk₂ : ℕ}
    {s : Memory.State} (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbReadBlkPairProg (mctx, (blk₁, blk₂)))) := by
  unfold fbReadBlkPairProg
  refine validHistory_bp_ro hmv (validHistory_bpReadSlabOwnerProg hmv) fun _ _ hmv₁ => ?_
  exact validHistory_bind_ro (validHistory_bpReadSlabOwnerProg hmv₁) fun _ _ _ => trivial

private theorem validHistory_fbWriteBlkPairProg {w : ℕ} {mctx : BpMetaCtx}
    {blk₁ blk₂ o₁ o₂ : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbWriteBlkPairProg ((mctx, (blk₁, blk₂)), (o₁, o₂)))) := by
  unfold fbWriteBlkPairProg
  exact validHistory_bp_wf hwf hmv (validHistory_bpWriteSlabOwnerProg hwf hmv)
    fun _ _ hwf₁ hmv₁ => validHistory_bpWriteSlabOwnerProg hwf₁ hmv₁

private theorem validHistory_fbDemoteSwapBodyProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {blk lastBlk : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbDemoteSwapBodyProg ((mctx, ioctx), (blk, lastBlk)))) := by
  unfold fbDemoteSwapBodyProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_fbReadBlkPairProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_fbSwapRangeProg hwf₁ hmv₁ hiov₁)
    fun _ _ hwf₂ hmv₂ _ => ?_
  exact validHistory_bind_ro (validHistory_fbWriteBlkPairProg hwf₂ hmv₂) fun _ _ _ => trivial

private theorem validHistory_fbDemoteSwapProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {blk lastBlk : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbDemoteSwapProg ((mctx, ioctx), (blk, lastBlk)))) := by
  unfold fbDemoteSwapProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_ite (fun _ => validHistory_fbDemoteSwapBodyProg hwf hmv hiov)
    (fun _ => trivial)

private theorem validHistory_fbDemoteTailProg {w : ℕ} {mctx : BpMetaCtx}
    {lastBlk tailLen b_blk : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbDemoteTailProg ((mctx, (lastBlk, tailLen)), b_blk))) := by
  unfold fbDemoteTailProg
  refine validHistory_bp_wf hwf hmv (validHistory_fbShiftRightLoopProg hwf hmv)
    fun _ _ hwf₁ hmv₁ => ?_
  simp only [pure_bind]
  exact validHistory_bp_wf hwf₁ hmv₁ (validHistory_fbFillHeadLoopProg hwf₁ hmv₁)
    fun _ _ _ hmv₂ => validHistory_bpWriteScalarProg hmv₂

private theorem validHistory_fbDemoteInnerProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {blk fb0 nSide fbBase : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbDemoteInnerProg (((mctx, ioctx), (blk, fb0)), (nSide, fbBase)))) := by
  unfold fbDemoteInnerProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_pool_wf hwf hmv hiov (validHistory_fbDemoteSwapProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ _ => validHistory_fbDemoteTailProg hwf₁ hmv₁

private theorem validHistory_fbDemoteCheckProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {blk nSide fb0 : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbDemoteCheckProg (((mctx, ioctx), blk), (nSide, fb0)))) := by
  unfold fbDemoteCheckProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_fbDemoteInnerProg hwf hmv hiov

/-- Memory history admissibility for `fbDemoteBlkProg`. -/
theorem validHistory_fbDemoteBlkProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {blk : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbDemoteBlkProg ((mctx, ioctx), blk))) := by
  unfold fbDemoteBlkProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_fbDemoteCheckProg hwf₂ hmv₂ hiov₂

private theorem validHistory_fbPopBackAndDecProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {last : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPopBackAndDecProg ((mctx, ioctx), last))) := by
  unfold fbPopBackAndDecProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_slotIoPopBackRawProg hwf hiov)
    fun _ _ _ hmv₁ _ => validHistory_bpWriteScalarProg hmv₁

private theorem validHistory_fbPopTailInnerProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {p nSide fbBase : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPopTailInnerProg (((mctx, ioctx), p), (nSide, fbBase)))) := by
  unfold fbPopTailInnerProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_pool_wf hwf hmv hiov (validHistory_fbSwapTailSlotsProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ hiov₁ => validHistory_fbPopBackAndDecProg hwf₁ hmv₁ hiov₁

private theorem validHistory_fbPopTailCheckProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {p nSide fb0 : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbPopTailCheckProg (((mctx, ioctx), p), (nSide, fb0)))) := by
  unfold fbPopTailCheckProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_fbPopTailInnerProg hwf hmv hiov

/-- Memory history admissibility for `fbPopTailAtProg`. -/
theorem validHistory_fbPopTailAtProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {p : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbPopTailAtProg ((mctx, ioctx), p))) := by
  unfold fbPopTailAtProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_fbPopTailCheckProg hwf₂ hmv₂ hiov₂

private theorem validHistory_fbDemotePopRunProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {blk fb1 off : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbDemotePopRunProg (((mctx, ioctx), blk), (fb1, off)))) := by
  unfold fbDemotePopRunProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_pool_wf hwf hmv hiov (validHistory_fbDemoteBlkProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ hiov₁ => validHistory_fbPopTailAtProg hwf₁ hmv₁ hiov₁

private theorem validHistory_fbDemoteAndPopProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {blk off : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbDemoteAndPopProg ((mctx, ioctx), (blk, off)))) := by
  unfold fbDemoteAndPopProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_pool_wf hwf hmv hiov (validHistory_fbMaybePromoteProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_fbDemotePopRunProg hwf₂ hmv₂ hiov₂

/-- Memory history admissibility for `fbDeleteSlotProg`. -/
theorem validHistory_fbDeleteSlotProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {hitP : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbDeleteSlotProg ((mctx, ioctx), hitP))) := by
  unfold fbDeleteSlotProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpDivModKProg w _ _)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_ite
    (fun _ => validHistory_fbDemoteAndPopProg hwf₂ hmv₂ hiov₂)
    (fun _ => validHistory_fbPopTailAtProg hwf₂ hmv₂ hiov₂)

private theorem validHistory_fbUndoTopSwapBodyProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {src dst cur : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbUndoTopSwapBodyProg (((mctx, ioctx), (src, dst)), cur))) := by
  unfold fbUndoTopSwapBodyProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_fbSwapRangeProg hwf hmv hiov)
    fun _ _ _ hmv₁ _ => validHistory_bpWriteScalarProg hmv₁

private theorem validHistory_fbUndoTopSwapCheckProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {src dst cur : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbUndoTopSwapCheckProg (((mctx, ioctx), (src, dst)), cur))) := by
  unfold fbUndoTopSwapCheckProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_ite (fun _ => validHistory_fbUndoTopSwapBodyProg hwf hmv hiov)
    (fun _ => trivial)

private theorem validHistory_fbUndoTopSwapReadProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbUndoTopSwapReadProg (mctx, ioctx))) := by
  unfold fbUndoTopSwapReadProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  refine validHistory_pool_wf hwf₂ hmv₂ hiov₂ (validHistory_bpReadScalarProg hmv₂)
    fun _ _ hwf₃ hmv₃ hiov₃ => ?_
  exact validHistory_fbUndoTopSwapCheckProg hwf₃ hmv₃ hiov₃

private theorem validHistory_fbUndoTopSwapProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbUndoTopSwapProg (mctx, ioctx))) := by
  unfold fbUndoTopSwapProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  exact validHistory_ite (fun _ => validHistory_fbUndoTopSwapReadProg hwf₁ hmv₁ hiov₁)
    (fun _ => trivial)

private theorem validHistory_fbReadSlabLanePairProg {w : ℕ} {mctx : BpMetaCtx}
    {b₁ b₂ lane : ℕ} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbReadSlabLanePairProg ((mctx, (b₁, b₂)), lane))) := by
  unfold fbReadSlabLanePairProg
  refine validHistory_bp_ro hmv (validHistory_bpReadSlabOwnerProg hmv) fun _ _ hmv₁ => ?_
  exact validHistory_bind_ro (validHistory_bpReadSlabOwnerProg hmv₁) fun _ _ _ => trivial

private theorem validHistory_fbWriteSlabLanePairProg {w : ℕ} {mctx : BpMetaCtx}
    {b₁ b₂ lane v₁ v₂ : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbWriteSlabLanePairProg (((mctx, (b₁, b₂)), lane), (v₁, v₂)))) := by
  unfold fbWriteSlabLanePairProg
  exact validHistory_bp_wf hwf hmv (validHistory_bpWriteSlabOwnerProg hwf hmv)
    fun _ _ hwf₁ hmv₁ => validHistory_bpWriteSlabOwnerProg hwf₁ hmv₁

private theorem validHistory_fbSwapSlabLaneProg {w : ℕ} {mctx : BpMetaCtx}
    {b₁ b₂ lane : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbSwapSlabLaneProg ((mctx, (b₁, b₂)), lane))) := by
  unfold fbSwapSlabLaneProg
  exact validHistory_bp_wf hwf hmv (validHistory_fbReadSlabLanePairProg hmv)
    fun _ _ hwf₁ hmv₁ => validHistory_fbWriteSlabLanePairProg hwf₁ hmv₁

private theorem validHistory_fbSwapSlabMeta3Prog {w : ℕ} {mctx : BpMetaCtx}
    {b₁ b₂ : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbSwapSlabMeta3Prog (mctx, (b₁, b₂)))) := by
  unfold fbSwapSlabMeta3Prog
  refine validHistory_bp_wf hwf hmv (validHistory_fbSwapSlabLaneProg hwf hmv)
    fun _ _ hwf₁ hmv₁ => ?_
  refine validHistory_bp_wf hwf₁ hmv₁ (validHistory_fbSwapSlabLaneProg hwf₁ hmv₁)
    fun _ _ hwf₂ hmv₂ => ?_
  exact validHistory_fbSwapSlabLaneProg hwf₂ hmv₂

private theorem validHistory_fbCompactDoRangeProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {sPure P : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCompactDoRangeProg ((mctx, ioctx), (sPure, P)))) := by
  unfold fbCompactDoRangeProg
  simp only [pure_bind]
  exact validHistory_fbSwapRangeProg hwf hmv hiov

private theorem validHistory_fbCompactSwapBlkBodyProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {sp : ℕ × ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbCompactSwapBlkBodyProg ((mctx, ioctx), sp))) := by
  unfold fbCompactSwapBlkBodyProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_fbCompactDoRangeProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ _ => validHistory_fbSwapSlabMeta3Prog hwf₁ hmv₁

private theorem validHistory_fbCompactSwapBlkProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {sPure P : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCompactSwapBlkProg ((mctx, ioctx), (sPure, P)))) := by
  unfold fbCompactSwapBlkProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_ite (fun _ => validHistory_fbCompactSwapBlkBodyProg hwf hmv hiov)
    (fun _ => trivial)

private theorem validHistory_fbCompactPureHitProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {tag P sPure : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCompactPureHitProg (((mctx, ioctx), tag), (P, sPure)))) := by
  unfold fbCompactPureHitProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_bind_ro (validHistory_fbCompactSwapBlkProg hwf hmv hiov) fun _ _ _ => trivial

private theorem validHistory_fbCompactPureStepProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {B_full : ℕ} {acc : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCompactPureStepProg (((mctx, ioctx), B_full), acc))) := by
  rcases acc with ⟨P, sPure⟩
  unfold fbCompactPureStepProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadSlabOwnerProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => validHistory_fbCompactPureHitProg hwf₂ hmv₂ hiov₂

private theorem validHistory_fbCompactPureLoopProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {B_full fuel : ℕ} {acc : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCompactPureLoopProg ((((mctx, ioctx), B_full), acc), fuel))) := by
  unfold fbCompactPureLoopProg
  exact validHistory_iterate_wf fuel acc s hwf fun _ _ hwf' hfr =>
    validHistory_fbCompactPureStepProg hwf' (bpMetaValid_mono hmv hfr) (slotIoValid_mono hiov hfr)

private theorem validHistory_fbTailOwnerAtBlkProg {w : ℕ} {mctx : BpMetaCtx} {P off : ℕ}
    {s : Memory.State} (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbTailOwnerAtBlkProg (mctx, (P, off)))) := by
  unfold fbTailOwnerAtBlkProg
  refine validHistory_bp_ro hmv (validHistory_bpReadSlabOwnerProg hmv) fun _ _ hmv₁ => ?_
  exact validHistory_bp_ro hmv₁ (validHistory_bpTbSlotProg w _ _) fun _ _ hmv₂ =>
    validHistory_bpReadTailOwnerProg hmv₂

private theorem validHistory_fbSlotBktTag2Prog {w : ℕ} {mctx : BpMetaCtx} {P off : ℕ}
    {s : Memory.State} (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbSlotBktTag2Prog (mctx, (P, off)))) := by
  unfold fbSlotBktTag2Prog
  refine validHistory_bp_ro hmv (validHistory_bpReadSlabOwnerProg hmv) fun _ _ hmv₁ => ?_
  refine validHistory_bp_ro hmv₁ (validHistory_bpActCurProg hmv₁) fun _ _ hmv₂ => ?_
  exact validHistory_ite (fun _ => trivial) fun _ => validHistory_fbTailOwnerAtBlkProg hmv₂

private theorem validHistory_fbSlotBktRawProg {w : ℕ} {mctx : BpMetaCtx} {p : ℕ}
    {s : Memory.State} (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbSlotBktRawProg (mctx, p))) := by
  unfold fbSlotBktRawProg
  refine validHistory_bp_ro hmv (validHistory_bpDivModKProg w _ _) fun _ _ hmv₁ => ?_
  refine validHistory_bp_ro hmv₁ (validHistory_bpReadSlabOwnerProg hmv₁) fun _ _ hmv₂ => ?_
  refine validHistory_ite (fun _ => validHistory_bpReadSlabOwnerProg hmv₂) fun _ => ?_
  exact validHistory_ite (fun _ => validHistory_fbSlotBktTag2Prog hmv₂)
    (fun _ => validHistory_fbTailOwnerAtBlkProg hmv₂)

private theorem validHistory_fbFillTailOwnerWriteProg {w : ℕ} {mctx : BpMetaCtx} {p t : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbFillTailOwnerWriteProg ((mctx, p), t))) := by
  unfold fbFillTailOwnerWriteProg
  refine validHistory_bp_wf hwf hmv (validHistory_fbSlotBktRawProg hmv)
    fun _ _ hwf₁ hmv₁ => ?_
  exact validHistory_bind_ro (validHistory_bpWriteTailDirRawProg hwf₁ hmv₁) fun _ _ _ => trivial

private theorem validHistory_fbFillTailOwnerStepProg {w : ℕ} {mctx : BpMetaCtx} {baseP t : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbFillTailOwnerStepProg ((mctx, baseP), t))) := by
  unfold fbFillTailOwnerStepProg
  refine validHistory_bp_wf hwf hmv (validHistory_bpReadScalarProg hmv)
    fun _ _ hwf₁ hmv₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_fbFillTailOwnerWriteProg hwf₁ hmv₁

private theorem validHistory_fbFillTailOwnerLoopProg {w : ℕ} {mctx : BpMetaCtx}
    {baseP t fuel : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbFillTailOwnerLoopProg (((mctx, baseP), t), fuel))) := by
  unfold fbFillTailOwnerLoopProg
  exact validHistory_iterate_wf fuel t s hwf fun _ _ hwf' hfr =>
    validHistory_fbFillTailOwnerStepProg hwf' (bpMetaValid_mono hmv hfr)

private theorem validHistory_fbWriteModeOneProg {w : ℕ} {mctx : BpMetaCtx} {s : Memory.State}
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fbWriteModeOneProg mctx)) := by
  rcases mctx with ⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
    ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩
  have hw := hmv.w_mach_pos
  have hd1 := hmv.offSlabDir_ge
  have hd2 := hmv.offTailDir_ge
  have hd3 := hmv.offSlabOwner_ge
  have hd4 := hmv.offTailOwner_ge
  have hfr := hmv.frontier_ge
  dsimp only [BpMetaLayout.ofCtx] at hd1 hd2 hd3 hd4 hfr
  unfold fbWriteModeOneProg
  refine validHistory_ite (fun hob => ?_) (fun _ => trivial)
  exact ⟨⟨by omega, Nat.one_lt_two_pow hw.ne'⟩, trivial⟩

private theorem validHistory_fbEnterFinishBodyProg {w : ℕ} {mctx : BpMetaCtx}
    {sPure baseP tailLen : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbEnterFinishBodyProg ((mctx, sPure), (baseP, tailLen)))) := by
  unfold fbEnterFinishBodyProg
  simp only [pure_bind]
  refine validHistory_bp_wf hwf hmv (validHistory_fbFillTailOwnerLoopProg hwf hmv)
    fun _ _ hwf₁ hmv₁ => ?_
  exact validHistory_bp_ro hmv₁ (validHistory_bpWriteScalarProg hmv₁) fun _ _ hmv₂ =>
    validHistory_fbWriteModeOneProg hmv₂

private theorem validHistory_fbEnterFinishProg {w : ℕ} {mctx : BpMetaCtx} {nSide sPure : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbEnterFinishProg ((mctx, nSide), sPure))) := by
  unfold fbEnterFinishProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_fbEnterFinishBodyProg hwf hmv

private theorem validHistory_fbRunCompactPureProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {bf : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbRunCompactPureProg ((mctx, ioctx), bf))) := by
  unfold fbRunCompactPureProg
  simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_fbCompactPureLoopProg hwf hmv hiov)
    fun _ _ _ => trivial

private theorem validHistory_fbCompactAndFinishAtProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {nSide bf : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbCompactAndFinishAtProg (((mctx, ioctx), nSide), bf))) := by
  unfold fbCompactAndFinishAtProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_fbRunCompactPureProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ _ => validHistory_fbEnterFinishProg hwf₁ hmv₁

private theorem validHistory_fbEnterCompactAndFinishProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {nSide : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbEnterCompactAndFinishProg ((mctx, ioctx), nSide))) := by
  unfold fbEnterCompactAndFinishProg
  exact validHistory_pool_wf hwf hmv hiov (validHistory_bpDivModKProg w _ _)
    fun _ _ hwf₁ hmv₁ hiov₁ => validHistory_fbCompactAndFinishAtProg hwf₁ hmv₁ hiov₁

/-- Memory history admissibility for `enterFallbackProg`. -/
theorem validHistory_enterFallbackProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (enterFallbackProg (mctx, ioctx))) := by
  unfold enterFallbackProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_fbUndoTopSwapProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_fbEnterCompactAndFinishProg hwf₂ hmv₂ hiov₂

/-- Memory history admissibility for `fallbackQueryProg` (read-only). -/
theorem validHistory_fallbackQueryProg {w : ℕ} {fctx : FeistelHashCtx} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {u_val : ℕ} {s : Memory.State}
    (hfs : FeistelSplitPre w (fctx, u_val) s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fallbackQueryProg ((fctx, (mctx, ioctx)), u_val))) := by
  unfold fallbackQueryProg
  refine validHistory_pool_ro hmv hiov (validHistory_feistelSplitBoundedProg hfs)
    fun _ _ hmv₁ hiov₁ => ?_
  exact validHistory_bind_ro (validHistory_fbScanProg hmv₁ hiov₁) fun _ _ _ => trivial

private theorem validHistory_fbInsertNewCommitProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {bkt q_u v_val nSide t : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbInsertNewCommitProg ((((mctx, ioctx), (bkt, q_u)), v_val), (nSide, t)))) := by
  unfold fbInsertNewCommitProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_slotIoAppendRawProg hwf hiov)
    fun _ _ hwf₁ hmv₁ _ => ?_
  exact validHistory_bp_wf hwf₁ hmv₁ (validHistory_bpWriteTailDirRawProg hwf₁ hmv₁)
    fun _ _ _ hmv₂ => validHistory_bpWriteScalarProg hmv₂

private theorem validHistory_fbInsertNewCheckProg {w : ℕ} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {bq : ℕ × ℕ} {v_val nSide fb0 : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbInsertNewCheckProg ((((mctx, ioctx), bq), v_val), (nSide, fb0)))) := by
  unfold fbInsertNewCheckProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_fbInsertNewCommitProg hwf hmv hiov

private theorem validHistory_fbInsertNewProg {w : ℕ} {mctx : BpMetaCtx} {ioctx : SlotIoCtx}
    {bq : ℕ × ℕ} {v_val : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fbInsertNewProg (((mctx, ioctx), bq), v_val))) := by
  unfold fbInsertNewProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_fbMaybePromoteProg hwf hmv hiov)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_bpReadScalarProg hmv₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  refine validHistory_pool_wf hwf₂ hmv₂ hiov₂ (validHistory_bpReadScalarProg hmv₂)
    fun _ _ hwf₃ hmv₃ hiov₃ => ?_
  exact validHistory_fbInsertNewCheckProg hwf₃ hmv₃ hiov₃

/-- Memory history admissibility for `fallbackInsertProg`. -/
theorem validHistory_fallbackInsertProg {w : ℕ} {fctx : FeistelHashCtx} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {u_val v_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hfs : FeistelSplitPre w (fctx, u_val) s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fallbackInsertProg (((fctx, (mctx, ioctx)), u_val), v_val))) := by
  unfold fallbackInsertProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_feistelSplitBoundedProg hfs)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_fbScanProg hmv₁ hiov₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_ite
    (fun _ => validHistory_slotIoWriteRawProg hwf₂ hiov₂)
    (fun _ => validHistory_fbInsertNewProg hwf₂ hmv₂ hiov₂)

/-- Memory history admissibility for `fallbackDeleteProg`. -/
theorem validHistory_fallbackDeleteProg {w : ℕ} {fctx : FeistelHashCtx} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {u_val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hfs : FeistelSplitPre w (fctx, u_val) s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fallbackDeleteProg ((fctx, (mctx, ioctx)), u_val))) := by
  unfold fallbackDeleteProg
  refine validHistory_pool_wf hwf hmv hiov (validHistory_feistelSplitBoundedProg hfs)
    fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  refine validHistory_pool_wf hwf₁ hmv₁ hiov₁ (validHistory_fbScanProg hmv₁ hiov₁)
    fun _ _ hwf₂ hmv₂ hiov₂ => ?_
  exact validHistory_ite
    (fun _ => validHistory_fbDeleteSlotProg hwf₂ hmv₂ hiov₂)
    (fun _ => trivial)

/-- Memory history admissibility for `fallbackPopAnyProg`. -/
theorem validHistory_fallbackPopAnyProg {w : ℕ} {fctx : FeistelHashCtx} {mctx : BpMetaCtx}
    {ioctx : SlotIoCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hmv : (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
    (hiov : (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
    (hrec : let ((_, (_, w0)), (_, (_, (_, bBits)))) := fctx
      ∀ bkt q_val, q_val < 2 ^ (w0 - bBits) → FeistelReconPre w (fctx, (bkt, q_val)) s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fallbackPopAnyProg (fctx, (mctx, ioctx)))) := by
  rcases fctx with ⟨⟨⟨hb, ob⟩, ⟨wv, w0⟩⟩, ⟨⟨rb, ct⟩, ⟨dt, ⟨bc, bBits⟩⟩⟩⟩
  dsimp only at hrec
  unfold fallbackPopAnyProg
  refine validHistory_bind_same (validHistory_bpReadScalarProg hmv)
    (clientState_bpReadScalarProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_same (validHistory_fbOwnerOfProg hmv) (state_fbOwnerOfProg _ s) ?_
  refine validHistory_bind_same (validHistory_slotIoReadRawProg hiov)
    (clientState_slotIoReadRawProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun hq_sh => ?_) (fun _ => trivial)
  have hq_lt : ((Memory.spec 0).clientResult s
      (slotIoReadRawProg (ioctx, (Memory.spec 0).clientResult s
        (bpReadScalarProg (mctx, 1)) - 1))).1 < 2 ^ (w0 - bBits) := by
    rwa [Nat.shiftLeft_eq, one_mul] at hq_sh
  refine validHistory_pool_wf hwf hmv hiov
    (validHistory_feistelReconBoundedProg (hrec _ _ hq_lt)) fun _ _ hwf₁ hmv₁ hiov₁ => ?_
  exact validHistory_bind_ro (validHistory_fbDeleteSlotProg hwf₁ hmv₁ hiov₁) fun _ _ _ => trivial

/-! ## Section 5: `LargeEpochCtx` `ValidHistory` Proofs -/

private theorem clientState_readParamPairProg (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (readParamPairProg x) = s :=
  runClient_state_readParamPairProg x s

private theorem clientState_readParamQuadProg
    (x : (ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (readParamQuadProg x) = s :=
  runClient_state_readParamQuadProg x s

private theorem validHistory_readParamPairProg {w pBase k₁ k₂ : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) (hk₁ : k₁ < 64) (hk₂ : k₂ < 64) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readParamPairProg (pBase, (k₁, k₂)))) := by
  unfold readParamPairProg
  exact validHistory_read_bind (by omega) (validHistory_read_bind (by omega) trivial)

private theorem validHistory_readParamQuadProg {w pBase k₁ k₂ k₃ k₄ : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) (hk₁ : k₁ < 64) (hk₂ : k₂ < 64) (hk₃ : k₃ < 64)
    (hk₄ : k₄ < 64) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (readParamQuadProg ((pBase, (k₁, k₂)), (k₃, k₄)))) := by
  unfold readParamQuadProg
  refine validHistory_bind_ro (validHistory_readParamPairProg hp hk₁ hk₂) fun _ _ hfr₁ => ?_
  exact validHistory_bind_ro (validHistory_readParamPairProg (hp.trans hfr₁) hk₃ hk₄)
    fun _ _ _ => trivial

/-- Memory history admissibility for `loadBpMetaCtxProg` (read-only). -/
theorem validHistory_loadBpMetaCtxProg {w pBase : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadBpMetaCtxProg pBase)) := by
  unfold loadBpMetaCtxProg
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParamQuadProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParamQuadProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParamQuadProg _ s) ?_
  exact validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) trivial

/-- Memory history admissibility for `loadSlotIoCtxProg` (read-only). -/
theorem validHistory_loadSlotIoCtxProg {w pBase : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadSlotIoCtxProg pBase)) := by
  unfold loadSlotIoCtxProg
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParamQuadProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParamQuadProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  exact validHistory_read_bind (by omega) trivial

/-- Memory history admissibility for `loadBlockPoolCtxProg` (read-only). -/
theorem validHistory_loadBlockPoolCtxProg {w pBase : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadBlockPoolCtxProg pBase)) := by
  unfold loadBlockPoolCtxProg
  refine validHistory_bind_same (validHistory_loadBpMetaCtxProg hp)
    (clientState_loadBpMetaCtxProg pBase s) ?_
  exact validHistory_bind_same (validHistory_loadSlotIoCtxProg hp)
    (clientState_loadSlotIoCtxProg pBase s) trivial

/-- Memory history admissibility for `loadHashStaticCtxProg` (read-only). -/
theorem validHistory_loadHashStaticCtxProg {w pBase isFp : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadHashStaticCtxProg (pBase, isFp))) := by
  unfold loadHashStaticCtxProg
  simp only [pure_bind]
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by split_ifs <;> decide) (by decide) (by decide)
      (by decide))
    (clientState_readParamQuadProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  exact validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by split_ifs <;> decide))
    (clientState_readParamPairProg _ s) trivial

/-- Memory history admissibility for `loadTrieCtxProg` (read-only). -/
theorem validHistory_loadTrieCtxProg {w pBase role : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadTrieCtxProg (pBase, role))) := by
  unfold loadTrieCtxProg
  simp only [pure_bind]
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by split_ifs <;> decide)
      (by split_ifs <;> decide) (by split_ifs <;> decide))
    (clientState_readParamQuadProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  exact validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParamQuadProg _ s) trivial

/-- Memory history admissibility for `loadBTreeSliceCtxProg` (read-only). -/
theorem validHistory_loadBTreeSliceCtxProg {w pBase b role : ℕ} {s : Memory.State}
    (hp : pBase + 64 ≤ s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (loadBTreeSliceCtxProg (pBase, (b, role)))) := by
  unfold loadBTreeSliceCtxProg
  dsimp only
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_bind_same
    (validHistory_readParamQuadProg hp (by decide) (by decide) (by decide) (by decide))
    (clientState_readParamQuadProg _ s) ?_
  exact validHistory_read_bind (by omega) trivial

/-- Memory history admissibility for `fastFeistelSplitProg` (read-only). -/
theorem validHistory_fastFeistelSplitProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastFeistelSplitProg (pBase, u_val))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hw0, hw0_le, hbc_w, hbw_w, _, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt, _⟩ :=
    evalSalted_ready_bounds hr
  obtain ⟨hv, hpt, hbkt, _⟩ := hr
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  have hU_pos : 0 < fl.U :=
    lt_of_lt_of_le (whpThreshold_pos fl.c) (hv.thresh_le.trans hv.N_le_U)
  unfold fastFeistelSplitProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun hle => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadHashStaticCtxProg hp)
    (clientState_loadHashStaticCtxProg _ s) ?_
  rw [clientResult_loadFeistelCtx hpt]
  have hu_lt_U : u_val < fl.U := by omega
  have hu_lt_w0 : u_val < 2 ^ redWidthWhp fl.U :=
    hu_lt_U.trans_le (le_two_pow_redWidthWhp fl.U)
  have hq_lt_w0 : u_val >>> bWhp fl.N < 2 ^ redWidthWhp fl.U :=
    (Nat.shiftRight_le _ _).trans_lt hu_lt_w0
  exact validHistory_feistelSplitBoundedProg
    ⟨hbw_w, hu_lt_w0, hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hbw_w.le,
      by rw [hv.w_eq]; rfl, hbkt, Nat.two_pow_pos _, hq_lt_w0, hd_lt, hc1_lt,
      htop_lt, hbot_lt, hfr_bkt⟩

/-- Memory history admissibility for `fastFeistelReconProg` (read-only). -/
theorem validHistory_fastFeistelReconProg {w pBase bkt q_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastFeistelReconProg (pBase, (bkt, q_val)))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hw0, hw0_le, hbc_w, hbw_w, _, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt, _⟩ :=
    evalSalted_ready_bounds hr
  obtain ⟨hv, hpt, hbkt, _⟩ := hr
  unfold fastFeistelReconProg
  refine validHistory_bind_same (validHistory_loadHashStaticCtxProg hp)
    (clientState_loadHashStaticCtxProg _ s) ?_
  rw [clientResult_loadFeistelCtx hpt]
  dsimp only [FastEpochLayout.feistelCtx]
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun hq_sh => ?_) (fun _ => trivial)
  have hbw_pos : 1 ≤ bWhp fl.N := by
    have hM := hv.mp_valid.M_ge
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hM
    unfold numBucketsWhp at hM
    by_contra hz
    have h0 : bWhp fl.N = 0 := by omega
    rw [h0] at hM; omega
  have hbw_kb : bWhp fl.N ≤ keyBits fl.U := by
    unfold bWhp keyBits
    exact (Nat.sub_le _ _).trans ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
  have hrw_eq : redWidthWhp fl.U = keyBits fl.U := max_eq_right (by omega)
  have hq_lt : q_val < 2 ^ quotBitsWhp fl.U fl.N := by
    rw [Nat.shiftLeft_eq, one_mul, hrw_eq] at hq_sh
    exact hq_sh
  have hsum_w : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ w := by
    unfold quotBitsWhp; rw [Nat.sub_add_cancel hbw_kb]
    exact Nat.clog_le_of_le_pow hv.fits_U.le
  have hq_w0 : q_val < 2 ^ redWidthWhp fl.U :=
    lt_of_lt_of_le hq_lt (two_pow_quotBitsWhp_le_redWidthWhp fl.U fl.N)
  exact validHistory_feistelReconBoundedProg
    ⟨quotBitsWhp fl.U fl.N, hbw_w, hsum_w, hq_lt,
      hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hbw_w.le, by rw [hv.w_eq]; rfl, hbkt,
      Nat.two_pow_pos _, hq_w0, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt⟩

/-- Memory history admissibility for `fastRKeyProg` (read-only). -/
theorem validHistory_fastRKeyProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastRKeyProg (pBase, u_val))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hfr_fp⟩ := evalSalted_ready_bounds hr
  obtain ⟨_, hpt, _, _⟩ := hr
  have hhb : s.mem (fl.pBase + 62) = fl.fpHashBase := hpt 62 (by decide)
  have hsp_pos := BitPackedDoubleTabulation.space_pos w (cTabWhp fl.c) (dTabWhp fl.c)
    (bCharWhp fl.N) (fpBitsWhp fl.N)
  unfold fastRKeyProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_read_bind (by rw [hhb]; omega) ?_
  exact validHistory_oddMulReducedProg w _ s

/-- Memory history admissibility for `fastFpHashProg` (read-only). -/
theorem validHistory_fastFpHashProg {w pBase salt u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastFpHashProg (pBase, (salt, u_val)))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hw0, hw0_le, hbc_w, _, hfp_w, hd_lt, hc1_lt, htop_lt, hbot_lt, _, hfr_fp⟩ :=
    evalSalted_ready_bounds hr
  obtain ⟨hv, hpt, _, hfp_α⟩ := hr
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  have hsm : s.mem (fl.pBase + 24) = sMaxWhp fl.c fl.N := hpt 24 (by decide)
  have hU_pos : 0 < fl.U :=
    lt_of_lt_of_le (whpThreshold_pos fl.c) (hv.thresh_le.trans hv.N_le_U)
  unfold fastFpHashProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun hle => ?_) (fun _ => trivial)
  refine validHistory_ite (fun hsalt => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_loadHashStaticCtxProg hp)
    (clientState_loadHashStaticCtxProg _ s) ?_
  rw [clientResult_loadFpStaticCtx hpt]
  have hu_lt_U : u_val < fl.U := by omega
  have hu_lt_w0 : u_val < 2 ^ redWidthWhp fl.U :=
    hu_lt_U.trans_le (le_two_pow_redWidthWhp fl.U)
  have hsalt_bc : salt < 2 ^ bCharWhp fl.N :=
    lt_of_lt_of_le (by omega : salt < sMaxWhp fl.c fl.N)
      (sMaxWhp_le_two_pow_bCharWhp hv.thresh_le)
  exact validHistory_evalSaltedBoundedProg
    ⟨hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hfp_w.le, by rw [hv.w_eq]; rfl, hfp_α,
      hsalt_bc, hu_lt_w0, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_fp⟩

private theorem epochMetaWords_ge_32 {c w N : ℕ} (ht : whpThreshold c ≤ N) :
    32 ≤ epochMetaWordsWhp c w N := by
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := c) (w := w) ht
  rw [← hend]
  unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
    offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
    offBktMeta offFpHash offBktHash
  omega

/-- Memory history admissibility for `fastReadMetaProg` (read-only). -/
theorem validHistory_fastReadMetaProg {w pBase off : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastReadMetaProg (pBase, off))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hv, hpt, _, _⟩ := hr
  have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  have h32 := epochMetaWords_ge_32 (w := fl.w) hv.thresh_le
  have hmf := hv.meta_frontier
  unfold fastReadMetaProg
  refine validHistory_ite (fun hoff => ?_) (fun _ => trivial)
  refine validHistory_read_bind (by omega) ?_
  rw [hmb]
  have hlt : fl.metaBase + off < s.frontier := by omega
  exact ⟨hlt, trivial⟩

/-- Memory history admissibility for `fastWriteMetaProg` (requires `val < 2 ^ w`). -/
theorem validHistory_fastWriteMetaProg {w pBase off val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) (hval : val < 2 ^ w) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastWriteMetaProg ((pBase, off), val))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hv, hpt, _, _⟩ := hr
  have hmb : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  have h32 := epochMetaWords_ge_32 (w := fl.w) hv.thresh_le
  have hmf := hv.meta_frontier
  unfold fastWriteMetaProg
  refine validHistory_ite (fun hoff => ?_) (fun _ => trivial)
  refine validHistory_read_bind (by omega) ?_
  rw [hmb]
  exact ⟨⟨by omega, hval⟩, trivial⟩

private theorem bktMeta_frontier_le {fl : FastEpochLayout} {w fr : ℕ}
    (hv : fl.Valid w fr) :
    fl.metaBase + offBktMeta fl.c fl.w fl.N +
      packedWords (16 * numBucketsWhp fl.N) (globalPtrBits fl.N) fl.w ≤ fr := by
  have hmv := hv.mp_valid
  have hd1 := hmv.offSlabDir_ge
  have hd2 := hmv.offTailDir_ge
  have hd3 := hmv.offSlabOwner_ge
  have hd4 := hmv.offTailOwner_ge
  have hfr := hmv.frontier_ge
  dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hd1 hd2 hd3 hd4 hfr
  omega

/-- Memory history admissibility for `fastReadBktLaneProg` (read-only). -/
theorem validHistory_fastReadBktLaneProg {w pBase b lane : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastReadBktLaneProg (pBase, (b, lane)))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hv, hpt, _, _⟩ := hr
  have hmv := hv.mp_valid
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  have hm31 : s.mem (fl.pBase + 31) = offBktMeta fl.c fl.w fl.N := hpt 31 (by decide)
  have hpb_res : (Memory.spec 0).clientResult s (readParamPairProg (fl.pBase, (10, 2))) =
      (globalPtrBits fl.N, fl.w) := by
    have hm10 : s.mem (fl.pBase + 10) = globalPtrBits fl.N := hpt 10 (by decide)
    have hm2 : s.mem (fl.pBase + 2) = fl.w := hpt 2 (by decide)
    exact Prod.ext hm10 hm2
  have hpb_le := hmv.ptrB_le
  have hfr_bm := bktMeta_frontier_le hv
  have hw_eq := hv.w_eq
  dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hpb_le
  unfold fastReadBktLaneProg
  refine validHistory_read_bind (by omega) ?_
  rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  rw [hm1, hm31, hpb_res]
  exact validHistory_readPackedCompGen
    ⟨16 * numBucketsWhp fl.N, hv.w_pos, hw_eq, by omega, by omega, by rwa [hw_eq]⟩

/-- Memory history admissibility for `fastWriteBktLaneProg`. -/
theorem validHistory_fastWriteBktLaneProg {w pBase b lane val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastWriteBktLaneProg ((pBase, (b, lane)), val))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hv, hpt, _, _⟩ := hr
  have hmv := hv.mp_valid
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hpt 11 (by decide)
  have hm1 : s.mem (fl.pBase + 1) = fl.metaBase := hpt 1 (by decide)
  have hm31 : s.mem (fl.pBase + 31) = offBktMeta fl.c fl.w fl.N := hpt 31 (by decide)
  have hpb_res : (Memory.spec 0).clientResult s (readParamPairProg (fl.pBase, (10, 2))) =
      (globalPtrBits fl.N, fl.w) := by
    have hm10 : s.mem (fl.pBase + 10) = globalPtrBits fl.N := hpt 10 (by decide)
    have hm2 : s.mem (fl.pBase + 2) = fl.w := hpt 2 (by decide)
    exact Prod.ext hm10 hm2
  have hpb_le := hmv.ptrB_le
  have hfr_bm := bktMeta_frontier_le hv
  have hw_eq := hv.w_eq
  dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hpb_le
  unfold fastWriteBktLaneProg
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  rw [hm11]
  refine validHistory_ite (fun hcond => ?_) (fun _ => trivial)
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_bind_same
    (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  rw [hm1, hm31, hpb_res]
  exact validHistory_writePackedCompGen hwf
    ⟨16 * numBucketsWhp fl.N, hv.w_pos, hw_eq, by omega, by omega, by rwa [hw_eq]⟩

/-- Memory history admissibility for `fastBpReadAtProg` (read-only). -/
theorem validHistory_fastBpReadAtProg {w pBase b loc : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBpReadAtProg (pBase, (b, loc)))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hv, hpt, _, _⟩ := hr
  have hmv : (BpMetaLayout.ofCtx fl.mp.toCtx).Valid w s.frontier := by
    rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid
  have hiov : (SlotIoLayout.ofCtx fl.io.toCtx).Valid w s.frontier := by
    rw [SlotIoLayout.ofCtx_toCtx]; exact hv.io_valid
  unfold fastBpReadAtProg
  refine validHistory_bind_same (validHistory_loadBlockPoolCtxProg hp)
    (clientState_loadBlockPoolCtxProg fl.pBase s) ?_
  rw [clientResult_loadBlockPoolCtxProg hpt]
  dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
  exact validHistory_bind_same (validHistory_bpToPhysProg hmv)
    (clientState_bpToPhysProg _ s) (validHistory_slotIoReadRawProg hiov)

/-- Memory history admissibility for `fastBpBktCountProg` (read-only). -/
theorem validHistory_fastBpBktCountProg {w pBase b : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastBpBktCountProg (pBase, b))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  obtain ⟨hv, hpt, _, _⟩ := hr
  have hmv : (BpMetaLayout.ofCtx fl.mp.toCtx).Valid w s.frontier := by
    rw [BpMetaLayout.ofCtx_toCtx]; exact hv.mp_valid
  unfold fastBpBktCountProg
  refine validHistory_bind_same (validHistory_loadBpMetaCtxProg hp)
    (clientState_loadBpMetaCtxProg fl.pBase s) ?_
  rw [clientResult_loadBpMetaCtxProg hpt]
  exact validHistory_bpReadBktCountProg hmv

private theorem validHistory_fastCheckTrieRoleProg {w pBase role rk b q_u : ℕ}
    {s : Memory.State} (hrole : role < 2) (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastCheckTrieRoleProg ((pBase, role), (rk, (b, q_u))))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  have ⟨hv, hpt, _, _⟩ := hr
  have htv : (TrieLayout.ofCtx (fl.trieL role).toCtx).Valid w s.frontier := by
    rw [TrieLayout.ofCtx_toCtx, hv.w_eq]; exact hv.trie_valid hrole
  unfold fastCheckTrieRoleProg
  refine validHistory_bind_same (validHistory_loadTrieCtxProg hp)
    (clientState_loadTrieCtxProg _ s) ?_
  rw [clientResult_loadTrieCtxProg hpt hrole]
  refine validHistory_bind_same (validHistory_bufLookupBoundedProg htv)
    (clientState_bufLookupBoundedProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_ro (validHistory_fastBpReadAtProg ⟨fl, rfl, hr⟩) fun _ _ _ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_fastCheckBTreeSliceProg {w : ℕ} {fl : FastEpochLayout}
    {b role fp q_u : ℕ} {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hb : b < numBucketsWhp fl.N) (hrole : role < 3) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastCheckBTreeSliceProg ((fl.pBase, (b, role)), (fp, q_u)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  have hbt : BTreeSlicePre w (fl.btL.toSliceCtx b role) s := by
    have hbtv := hr.1.bt_valid
    rw [← hr.1.w_eq] at hbtv
    exact ⟨hbtv, hb, hrole⟩
  unfold fastCheckBTreeSliceProg
  refine validHistory_bind_same (validHistory_loadBTreeSliceCtxProg hp)
    (clientState_loadBTreeSliceCtxProg _ s) ?_
  rw [clientResult_loadBTreeSliceCtxProg hr.2.1]
  refine validHistory_bind_same (validHistory_btreeLookupBoundedProg hbt)
    (clientState_btreeLookupBoundedProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_ro (validHistory_fastBpReadAtProg ⟨fl, rfl, hr⟩) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_fastCheckBTreeFpProg {w : ℕ} {fl : FastEpochLayout}
    {u_val b q_u role salt : ℕ} {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hb : b < numBucketsWhp fl.N) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastCheckBTreeFpProg (((fl.pBase, u_val), (b, q_u)), (role, salt)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  unfold fastCheckBTreeFpProg
  refine validHistory_ite (fun hrole => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_readParamPairProg hp (by decide) (by decide))
    (clientState_readParamPairProg _ s) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastFpHashProg ⟨fl, rfl, hr⟩)
    (clientState_fastFpHashProg _ s) ?_
  exact validHistory_ite (fun _ => validHistory_fastCheckBTreeSliceProg hr hb hrole)
    (fun _ => trivial)

private theorem validHistory_fastCheckBTreeProg {w pBase u_val b q_u : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastCheckBTreeProg ((pBase, u_val), (b, q_u)))) := by
  obtain ⟨fl, rfl, hr⟩ := hpre
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
  have hm11 : s.mem (fl.pBase + 11) = numBucketsWhp fl.N := hr.2.1 11 (by decide)
  unfold fastCheckBTreeProg
  refine validHistory_read_bind (by omega) ?_
  rw [hm11]
  refine validHistory_ite (fun hb => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg ⟨fl, rfl, hr⟩)
    (clientState_fastReadBktLaneProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadBktLaneProg ⟨fl, rfl, hr⟩)
    (clientState_fastReadBktLaneProg _ s) ?_
  exact validHistory_fastCheckBTreeFpProg hr hb

private theorem validHistory_fastProbeBTreeTailProg {w pBase u_val b q_u coll : ℕ}
    {s : Memory.State} (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastProbeBTreeTailProg ((pBase, u_val), ((b, q_u), coll)))) := by
  unfold fastProbeBTreeTailProg
  refine validHistory_bind_ro (validHistory_fastCheckBTreeProg hpre) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_fastProbeMissCurProg {w pBase u_val curRole c1Coll : ℕ}
    {bq : ℕ × ℕ} {rk : ℕ} {s : Memory.State} (hcr : curRole < 2)
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (fastProbeMissCurProg (((pBase, u_val), (curRole, c1Coll)), (bq, rk)))) := by
  obtain ⟨_, hp⟩ := FastProgPre.pBase_bound hpre
  unfold fastProbeMissCurProg
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_read_bind (by omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_fastProbeBTreeTailProg hpre)
  simp only [pure_bind]
  refine validHistory_bind_same (validHistory_fastCheckTrieRoleProg (by omega) hpre)
    (clientState_fastCheckTrieRoleProg _ s) ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_ite (fun _ => validHistory_fastProbeBTreeTailProg hpre) fun _ => ?_
  exact validHistory_ite
    (fun _ => validHistory_fastProbeBTreeTailProg hpre)
    (fun _ => validHistory_fastProbeBTreeTailProg hpre)

/-- Memory history admissibility for `fastProbeProg` (read-only). -/
theorem validHistory_fastProbeProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastProbeProg (pBase, u_val))) := by
  unfold fastProbeProg
  refine validHistory_bind_same (validHistory_fastFeistelSplitProg hpre)
    (clientState_fastFeistelSplitProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastRKeyProg hpre)
    (clientState_fastRKeyProg _ s) ?_
  refine validHistory_bind_same (validHistory_fastReadMetaProg hpre)
    (clientState_fastReadMetaProg _ s) ?_
  refine validHistory_ite (fun hcr => ?_) (fun _ => trivial)
  refine validHistory_bind_same (validHistory_fastCheckTrieRoleProg hcr hpre)
    (clientState_fastCheckTrieRoleProg _ s) ?_
  exact validHistory_ite (fun _ => trivial)
    (fun _ => validHistory_fastProbeMissCurProg hcr hpre)

/-- Memory history admissibility for `fastQueryProg` (read-only). -/
theorem validHistory_fastQueryProg {w pBase u_val : ℕ} {s : Memory.State}
    (hpre : FastProgPre w pBase s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (fastQueryProg (pBase, u_val))) := by
  unfold fastQueryProg
  refine validHistory_bind_ro (validHistory_fastProbeProg hpre) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

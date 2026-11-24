/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeTrieProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeMetaProg
-- Private SWAR B+-tree helpers shared across the LargeBTreeBase/LargeBTreeProg split.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeBase
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeProg
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeTrieProg

/-!
# Memory History Admissibility (`ValidHistory`) for B+-Tree and `BufTrie` Programs

This module proves `(Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)` for all ten
public `Memory.Prog` operations of `LargeBTreeBase`, `LargeBTreeProg`, and `LargeTrieProg`,
discharging the memory history admissibility obligation needed by `Realizes.code_spec` without
modifying any upstream module. The proofs unfold the unexposed program bodies via private
`import all` of `LargeMetaProg` (for `subClampProg`), `LargeBTreeBase`, `LargeBTreeProg`, and
`LargeTrieProg`, reducing every memory access to `validHistory_readPackedCompGen` and
`validHistory_writePackedCompGen`.

## Main results

* `validHistory_resetBTreeSliceBoundedProg`, `validHistory_btreeLookupBoundedProg`,
  `validHistory_btreeDeleteBoundedProg`, `validHistory_btreeUpdateBoundedProg`,
  `validHistory_btreeInsertBoundedProg`: memory history admissibility for the five public SWAR
  B+-tree slice programs in `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp`.
* `validHistory_bufLookupBoundedProg`, `validHistory_bufDeleteBoundedProg`,
  `validHistory_bufInsertBoundedProg`, `validHistory_bufCheckSlotBoundedProg`,
  `validHistory_bufClearStepsBoundedProg`:
  memory history admissibility for the five public `BufTrie` buffer programs.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

/-! ## Section 1: `ValidHistory` Combinators -/

private theorem wellFormed_clientState {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p)) :
    Memory.WellFormed w ((Memory.spec 0).clientState s p) := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact hwf.run hp

private theorem frontier_le_clientState {α : Type} (w : ℕ) (s : Memory.State)
    (p : Memory.Prog α) :
    s.frontier ≤ ((Memory.spec 0).clientState s p).frontier := by
  rw [← clientState_width w, ← (Memory.spec w).run_runClient p s]
  exact Memory.frontier_le_run s _

private theorem validHistory_bind_ro {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq _ _ (frontier_le_clientState w s p)⟩

private theorem validHistory_bind_wf {α β : Type} {w : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {q : α → Memory.Prog β}
    (hwf : Memory.WellFormed w s)
    (hp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hq : ∀ a s', Memory.WellFormed w s' → s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (q a))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p >>= q)) := by
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q))
  rw [validHistory_bind, clientResult_width, clientState_width]
  exact ⟨hp, hq _ _ (wellFormed_clientState hwf hp) (frontier_le_clientState w s p)⟩

private theorem validHistory_ite {α : Type} {w : ℕ} {s : Memory.State} {c : Prop} [Decidable c]
    {p₁ p₂ : Memory.Prog α}
    (h₁ : c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₁))
    (h₂ : ¬c → (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p₂)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (if c then p₁ else p₂)) := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h₁ hc
  · rw [ite_eq_right hc]; exact h₂ hc

private theorem validHistory_iterate_ro {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {d : δ} (n : ℕ) (a : σ) (s : Memory.State)
    (hbody : ∀ a' s', s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (body (d, a')))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d n a)) := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih =>
    unfold iterate
    refine validHistory_bind_ro (hbody a s le_rfl) fun a' s' hfr' =>
      ih a' s' fun a'' s'' hfr'' => hbody a'' s'' (hfr'.trans hfr'')

private theorem validHistory_iterate_wf {δ σ : Type} {w : ℕ}
    {body : δ × σ → Memory.Prog σ} {d : δ} (n : ℕ) (a : σ) (s : Memory.State)
    (hwf : Memory.WellFormed w s)
    (hbody : ∀ a' s', Memory.WellFormed w s' → s.frontier ≤ s'.frontier →
      (Memory.spec w).ValidHistory s' ((Memory.spec w).clientHistory s' (body (d, a')))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (iterate body d n a)) := by
  induction n generalizing a s with
  | zero => trivial
  | succ n ih =>
    unfold iterate
    refine validHistory_bind_wf hwf (hbody a s hwf le_rfl) fun a' s' hwf' hfr' =>
      ih a' s' hwf' fun a'' s'' hwf'' hfr'' => hbody a'' s'' hwf'' (hfr'.trans hfr'')

/-! ## Section 2: `LargeBTreeProg` `ValidHistory` Proofs -/

private theorem sliceHdrPre_mono {w : ℕ} {hctx : SliceHdrCtx} {fr₁ fr₂ : ℕ}
    (h : SliceHdrPre w hctx fr₁) (hle : fr₁ ≤ fr₂) : SliceHdrPre w hctx fr₂ := by
  rcases hctx with ⟨⟨⟨mb, ob⟩, ⟨pb, wv⟩⟩, hdrBase⟩
  obtain ⟨cap, hw6, hwv, hpb, hsl, hcap, hfr⟩ := h
  exact ⟨cap, hw6, hwv, hpb, hsl, hcap, hfr.trans hle⟩

private theorem sliceNodePre_mono {w : ℕ} {nctx : SliceNodeCtx} {fr₁ fr₂ : ℕ}
    (h : SliceNodePre w nctx fr₁) (hle : fr₁ ≤ fr₂) : SliceNodePre w nctx fr₂ := by
  rcases nctx with ⟨⟨⟨⟨mb, om⟩, ⟨ok, ov⟩⟩, ⟨⟨wv, wm⟩, ⟨wk, wvl⟩⟩⟩, ⟨ns, nodeBase⟩⟩
  obtain ⟨tot, hw6, hwv, hns, hwm, hwk, hwvl, hnb, htot, hfr1, hfr2, hfr3⟩ := h
  exact ⟨tot, hw6, hwv, hns, hwm, hwk, hwvl, hnb, htot,
    hfr1.trans hle, hfr2.trans hle, hfr3.trans hle⟩

private theorem btreeEpochLayout_valid_mono {L : BTreeEpochLayout} {w fr₁ fr₂ : ℕ}
    (h : L.Valid w fr₁) (hle : fr₁ ≤ fr₂) : L.Valid w fr₂ := by
  obtain ⟨hw, hwv, hpb, htm, hfp, hwvL, hwm, hwk, hwvl, h4k, h4v, hmcap, hkcap, hnsv, hns64,
    hnsp, h16b, htot, hd0, hd1, hd2, hfr⟩ := h
  exact ⟨hw, hwv, hpb, htm, hfp, hwvL, hwm, hwk, hwvl, h4k, h4v, hmcap, hkcap, hnsv, hns64,
    hnsp, h16b, htot, hd0, hd1, hd2, hfr.trans hle⟩

private theorem btreeSlicePre_mono {w : ℕ} {ctx : BTreeSliceCtx} {s₁ s₂ : Memory.State}
    (h : BTreeSlicePre w ctx s₁) (hle : s₁.frontier ≤ s₂.frontier) :
    BTreeSlicePre w ctx s₂ := by
  rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
    ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
  dsimp only [BTreeSlicePre, unpackSliceCtx] at h ⊢
  obtain ⟨hv, hb, hr⟩ := h
  exact ⟨btreeEpochLayout_valid_mono hv hle, hb, hr⟩

private theorem sliceHdrPre_of_btreeSlicePre {w : ℕ} {ctx : BTreeSliceCtx} {s : Memory.State}
    (h : BTreeSlicePre w ctx s) :
    SliceHdrPre w (ctxHdrAt ctx (16 * ctxB ctx + 6 + 2 * ctxRole ctx)) s.frontier := by
  rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
    ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
  dsimp only [BTreeSlicePre, unpackSliceCtx] at h
  obtain ⟨hv, hb, hr⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, hhdr⟩ := hv.hdr_facts hb hr
  exact hhdr

private theorem sliceNodePre_of_btreeSlicePre {w : ℕ} {ctx : BTreeSliceCtx} {s : Memory.State}
    (h : BTreeSlicePre w ctx s) :
    SliceNodePre w (ctxNodeAt ctx ((3 * ctxB ctx + ctxRole ctx) * ctxNs ctx)) s.frontier := by
  rcases ctx with ⟨⟨⟨⟨mb, ob⟩, ⟨om, ⟨ok, ov⟩⟩⟩, ⟨⟨pb, wv⟩, ⟨wm, ⟨wk, wvl⟩⟩⟩⟩,
    ⟨⟨⟨fp, wvL⟩, ⟨tm, ns⟩⟩, ⟨nb, ⟨b, role⟩⟩⟩⟩
  dsimp only [BTreeSlicePre, unpackSliceCtx] at h
  obtain ⟨hv, hb, hr⟩ := h
  obtain ⟨_, _, _, _, _, _, _, hnode⟩ := hv.node_facts hb hr
  exact hnode

/-! ### Pure SWAR helpers (zero memory operations) -/

private theorem validHistory_subClampProg (w : ℕ) (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (subClampProg p)) := by
  unfold subClampProg
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_laneGetBoundedProg (w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (laneGetBoundedProg d)) := by
  rcases d with ⟨⟨_, _⟩, _⟩; trivial

private theorem validHistory_wordTakeLowBoundedProg (w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (wordTakeLowBoundedProg d)) := by
  rcases d with ⟨⟨_, _⟩, _⟩; trivial

private theorem validHistory_wordDropLowBoundedProg (w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (wordDropLowBoundedProg d)) := by
  rcases d with ⟨⟨_, _⟩, _⟩; trivial

private theorem validHistory_wordInsertAtBoundedProg (w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (wordInsertAtBoundedProg d)) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩
  unfold wordInsertAtBoundedProg
  refine validHistory_bind_ro (validHistory_wordTakeLowBoundedProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_wordDropLowBoundedProg w _ _) fun _ _ _ => ?_
  trivial

private theorem validHistory_wordDeleteAtBoundedProg (w : ℕ) (d : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (wordDeleteAtBoundedProg d)) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold wordDeleteAtBoundedProg
  exact validHistory_bind_ro (validHistory_wordTakeLowBoundedProg w _ _) fun _ _ _ => trivial

private theorem validHistory_wordUpdateAtBoundedProg (w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (wordUpdateAtBoundedProg d)) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, _⟩
  unfold wordUpdateAtBoundedProg
  exact validHistory_bind_ro (validHistory_wordDeleteAtBoundedProg w _ _) fun _ _ _ =>
    validHistory_wordInsertAtBoundedProg w _ _

private theorem validHistory_swarOnesBoundedProg (w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (swarOnesBoundedProg d)) := by
  rcases d with ⟨_, _⟩; trivial

private theorem validHistory_ltMaskBoundedProg (w : ℕ) (d : (ℕ × ℕ) × (ℕ × ℕ))
    (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (ltMaskBoundedProg d)) := by
  rcases d with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold ltMaskBoundedProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_swarOnesBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_subClampProg w _ _) fun _ _ _ => trivial

private theorem validHistory_swarRankInnerProg (w : ℕ) (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ))
    (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (swarRankInnerProg d)) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩
  unfold swarRankInnerProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_ltMaskBoundedProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_swarOnesBoundedProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_laneGetBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_swarRankClampedProg (w : ℕ) (d : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ))
    (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (swarRankClampedProg d)) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩
  unfold swarRankClampedProg; simp only [pure_bind]
  exact validHistory_ite
    (fun _ => validHistory_swarRankInnerProg w _ _)
    (fun _ => validHistory_swarRankInnerProg w _ _)

private theorem validHistory_splitFullLeafProg (w : ℕ)
    (d : (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (splitFullLeafProg d)) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  unfold splitFullLeafProg
  refine validHistory_bind_ro (validHistory_wordTakeLowBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_wordTakeLowBoundedProg w _ _) fun _ _ _ => trivial

private theorem validHistory_splitFullBranchProg (w : ℕ)
    (d : (SplitParams × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (splitFullBranchProg d)) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  unfold splitFullBranchProg
  refine validHistory_bind_ro (validHistory_wordTakeLowBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_wordTakeLowBoundedProg w _ _) fun _ _ _ => trivial

private theorem validHistory_splitFullNodeAtProg (w : ℕ)
    (d : SplitParams × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (splitFullNodeAtProg d)) := by
  rcases d with ⟨⟨⟨_, _⟩, _⟩, ⟨_, ⟨_, _⟩⟩⟩
  unfold splitFullNodeAtProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_laneGetBoundedProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_wordDropLowBoundedProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_wordDropLowBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_ite
    (fun _ => validHistory_splitFullLeafProg w _ _)
    (fun _ => validHistory_splitFullBranchProg w _ _)

private theorem validHistory_computeRootSplitProg (w : ℕ)
    (d : (SplitParams × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (computeRootSplitProg d)) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold computeRootSplitProg; simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_splitFullNodeAtProg w _ _) fun _ _ _ => trivial

private theorem validHistory_computeChildSplitProg (w : ℕ)
    (d : ((SplitParams × (ℕ × ℕ)) × ℕ) × ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (computeChildSplitProg d)) := by
  rcases d with ⟨⟨⟨_, ⟨_, _⟩⟩, _⟩, ⟨_, _⟩⟩
  unfold computeChildSplitProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_splitFullNodeAtProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_wordInsertAtBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_wordInsertAtBoundedProg w _ _) fun _ _ _ => trivial

private theorem validHistory_leafInsertShiftProg (w : ℕ)
    (d : (SplitParams × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (leafInsertShiftProg d)) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, ⟨_, _⟩⟩⟩⟩
  unfold leafInsertShiftProg
  refine validHistory_bind_ro (validHistory_wordInsertAtBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_bind_ro (validHistory_wordInsertAtBoundedProg w _ _) fun _ _ _ => trivial

private theorem validHistory_leafInsertHitOrShiftProg (w : ℕ)
    (d : (SplitParams × (ℕ × ℕ)) × (((ℕ × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (leafInsertHitOrShiftProg d)) := by
  rcases d with ⟨⟨_, _⟩, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩
  unfold leafInsertHitOrShiftProg
  exact validHistory_ite
    (fun _ =>
      validHistory_bind_ro (validHistory_wordUpdateAtBoundedProg w _ _) fun _ _ _ => trivial)
    (fun _ => validHistory_leafInsertShiftProg w _ _)

private theorem validHistory_computeLeafInsertNodeProg (w : ℕ)
    (d : (SplitParams × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (computeLeafInsertNodeProg d)) := by
  rcases d with ⟨⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩, _⟩
  unfold computeLeafInsertNodeProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_swarRankClampedProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_laneGetBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_ite
    (fun _ => validHistory_leafInsertHitOrShiftProg w _ _)
    (fun _ => validHistory_leafInsertShiftProg w _ _)

private theorem validHistory_descendBranchNextProg (w : ℕ)
    (d : (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (descendBranchNextProg d)) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold descendBranchNextProg; simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_swarRankClampedProg w _ _) fun _ _ _ =>
    validHistory_laneGetBoundedProg w _ _

private theorem validHistory_btreeLookupHitProg (w : ℕ)
    (d : (BTreeSliceCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeLookupHitProg d)) := by
  rcases d with ⟨⟨_, _⟩, ⟨⟨_, _⟩, _⟩⟩
  unfold btreeLookupHitProg
  exact validHistory_ite
    (fun _ => validHistory_bind_ro (validHistory_laneGetBoundedProg w _ _) fun _ _ _ => trivial)
    (fun _ => trivial)

private theorem validHistory_btreeLookupRankProg (w : ℕ)
    (d : (BTreeSliceCtx × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeLookupRankProg d)) := by
  rcases d with ⟨⟨_, _⟩, _⟩
  unfold btreeLookupRankProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_swarRankClampedProg w _ _) fun _ _ _ => ?_
  refine validHistory_bind_ro (validHistory_laneGetBoundedProg w _ _) fun _ _ _ => ?_
  exact validHistory_ite
    (fun _ => validHistory_btreeLookupHitProg w _ _)
    (fun _ => trivial)

/-! ### Packed node and header accessors -/

private theorem validHistory_readSliceNodeAtProg {w : ℕ} {nctx : SliceNodeCtx} {u : ℕ}
    {s : Memory.State} (h : SliceNodePre w nctx s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readSliceNodeAtProg (nctx, u))) := by
  rcases nctx with ⟨⟨⟨⟨mb, om⟩, ⟨ok, ov⟩⟩, ⟨⟨wv, wm⟩, ⟨wk, wvl⟩⟩⟩, ⟨ns, nodeBase⟩⟩
  obtain ⟨tot, hw6, hwv, hns1, hwm, hwk, hwvl, hnb_tot, _, hfr1, hfr2, hfr3⟩ := h
  subst hwv
  unfold readSliceNodeAtProg
  refine validHistory_ite (fun hu => ?_) (fun _ => ?_)
  · simp only [pure_bind]
    refine validHistory_bind_ro
      (validHistory_readPackedCompGen ⟨tot, by omega, rfl, hwm, by omega, hfr1⟩)
      fun _ s₁ hs₁ => ?_
    refine validHistory_bind_ro
      (validHistory_readPackedCompGen ⟨tot, by omega, rfl, hwk, by omega, hfr2.trans hs₁⟩)
      fun _ s₂ hs₂ => ?_
    exact validHistory_bind_ro
      (validHistory_readPackedCompGen
        ⟨tot, by omega, rfl, hwvl, by omega, hfr3.trans (hs₁.trans hs₂)⟩)
      fun _ _ _ => trivial
  · exact validHistory_bind_ro
      (validHistory_readPackedCompGen ⟨tot, by omega, rfl, hwm, by omega, hfr1⟩)
      fun _ _ _ => trivial

private theorem validHistory_writeSliceNodeAtProg {w : ℕ} {nctx : SliceNodeCtx} {u : ℕ}
    {nd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : SliceNodePre w nctx s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeSliceNodeAtProg ((nctx, u), nd))) := by
  rcases nctx with ⟨⟨⟨⟨mb, om⟩, ⟨ok, ov⟩⟩, ⟨⟨wv, wm⟩, ⟨wk, wvl⟩⟩⟩, ⟨ns, nodeBase⟩⟩
  rcases nd with ⟨mw, ⟨kw, vw⟩⟩
  obtain ⟨tot, hw6, hwv, _, hwm, hwk, hwvl, hnb_tot, _, hfr1, hfr2, hfr3⟩ := h
  subst hwv
  unfold writeSliceNodeAtProg
  refine validHistory_ite (fun hu => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_wf hwf
    (validHistory_writePackedCompGen hwf ⟨tot, by omega, rfl, hwm, by omega, hfr1⟩)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁
    (validHistory_writePackedCompGen hwf₁ ⟨tot, by omega, rfl, hwk, by omega, hfr2.trans hs₁⟩)
    fun _ s₂ hwf₂ hs₂ => ?_
  exact validHistory_writePackedCompGen hwf₂
    ⟨tot, by omega, rfl, hwvl, by omega, hfr3.trans (hs₁.trans hs₂)⟩

private theorem validHistory_writeTwoNodesAtProg {w : ℕ} {nctx : SliceNodeCtx}
    {pair : (ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × (ℕ × (ℕ × ℕ)))} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (h : SliceNodePre w nctx s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeTwoNodesAtProg (nctx, pair))) := by
  rcases pair with ⟨⟨_, _⟩, ⟨_, _⟩⟩
  unfold writeTwoNodesAtProg
  exact validHistory_bind_wf hwf (validHistory_writeSliceNodeAtProg hwf h) fun _ _ hwf' hfr' =>
    validHistory_writeSliceNodeAtProg hwf' (sliceNodePre_mono h hfr')

private theorem validHistory_readSliceHdrAtProg {w : ℕ} {hctx : SliceHdrCtx}
    {s : Memory.State} (h : SliceHdrPre w hctx s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readSliceHdrAtProg hctx)) := by
  rcases hctx with ⟨⟨⟨mb, ob⟩, ⟨pb, wv⟩⟩, hdrBase⟩
  obtain ⟨cap, hw6, hwv, hpb, hsl, _, hfr⟩ := h
  subst hwv
  unfold readSliceHdrAtProg
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨cap, by omega, rfl, hpb, by omega, hfr⟩)
    fun _ s₁ hs₁ => ?_
  exact validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨cap, by omega, rfl, hpb, hsl, hfr.trans hs₁⟩)
    fun _ _ _ => trivial

private theorem validHistory_writeSliceHdrAtProg {w : ℕ} {hctx : SliceHdrCtx} {isRoot val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (h : SliceHdrPre w hctx s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeSliceHdrAtProg (hctx, (isRoot, val)))) := by
  rcases hctx with ⟨⟨⟨mb, ob⟩, ⟨pb, wv⟩⟩, hdrBase⟩
  obtain ⟨cap, hw6, hwv, hpb, hsl, _, hfr⟩ := h
  subst hwv
  unfold writeSliceHdrAtProg
  refine validHistory_ite (fun hi => ?_) (fun _ => trivial)
  simp only [pure_bind]
  exact validHistory_writePackedCompGen hwf ⟨cap, by omega, rfl, hpb, by omega, hfr⟩

/-! ### Top-level B+-tree operations -/

/-- Memory history admissibility for `resetBTreeSliceBoundedProg` under `Memory.WellFormed` and
`BTreeSlicePre`. -/
theorem validHistory_resetBTreeSliceBoundedProg {w : ℕ} {ctx : BTreeSliceCtx} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (resetBTreeSliceBoundedProg ctx)) := by
  have hhdr := sliceHdrPre_of_btreeSlicePre hpre
  unfold resetBTreeSliceBoundedProg; simp only [pure_bind]
  exact validHistory_bind_wf hwf (validHistory_writeSliceHdrAtProg hwf hhdr) fun _ _ hwf' hfr' =>
    validHistory_writeSliceHdrAtProg hwf' (sliceHdrPre_mono hhdr hfr')

private theorem validHistory_descendStepProg {w : ℕ} {ctx : BTreeSliceCtx} {q cur : ℕ}
    {s : Memory.State} (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (descendStepProg ((ctx, q), cur))) := by
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold descendStepProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_readSliceNodeAtProg hnode) fun _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => validHistory_descendBranchNextProg w _ _)

private theorem validHistory_descendLoopProg {w : ℕ} {ctx : BTreeSliceCtx} {q cur fuel : ℕ}
    {s : Memory.State} (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (descendLoopProg (((ctx, q), cur), fuel))) := by
  unfold descendLoopProg
  exact validHistory_iterate_ro fuel cur s fun _ _ hfr' =>
    validHistory_descendStepProg (btreeSlicePre_mono hpre hfr')

private theorem validHistory_btreeLookupLeafProg {w : ℕ} {ctx : BTreeSliceCtx} {leafIdx q : ℕ}
    {s : Memory.State} (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeLookupLeafProg (ctx, (leafIdx, q)))) := by
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold btreeLookupLeafProg; simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_readSliceNodeAtProg hnode) fun _ _ _ =>
    validHistory_btreeLookupRankProg w _ _

private theorem validHistory_btreeLookupNonEmptyProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q rt fuel : ℕ} {s : Memory.State} (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeLookupNonEmptyProg (((ctx, q), rt), fuel))) := by
  unfold btreeLookupNonEmptyProg
  exact validHistory_bind_ro (validHistory_descendLoopProg hpre) fun _ _ hfr' =>
    validHistory_btreeLookupLeafProg (btreeSlicePre_mono hpre hfr')

/-- Memory history admissibility for `btreeLookupBoundedProg` under `BTreeSlicePre` (read-only;
no `Memory.WellFormed` premise required). -/
theorem validHistory_btreeLookupBoundedProg {w : ℕ} {ctx : BTreeSliceCtx} {q : ℕ}
    {s : Memory.State} (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeLookupBoundedProg (ctx, q))) := by
  have hhdr := sliceHdrPre_of_btreeSlicePre hpre
  unfold btreeLookupBoundedProg; simp only [pure_bind]
  refine validHistory_bind_ro (validHistory_readSliceHdrAtProg hhdr) fun _ _ hfr' => ?_
  exact validHistory_ite
    (fun _ => trivial)
    (fun _ => validHistory_btreeLookupNonEmptyProg (btreeSlicePre_mono hpre hfr'))

private theorem validHistory_btreeDeleteHitProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q nodeBase leafIdx cnt r kAt : ℕ} {nd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (btreeDeleteHitProg (((ctx, q), (nodeBase, leafIdx)), ((cnt, r), (kAt, nd))))) := by
  unfold btreeDeleteHitProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_wordDeleteAtBoundedProg w _ _)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁ (validHistory_wordDeleteAtBoundedProg w _ _)
    fun _ s₂ hwf₂ hs₂ => ?_
  exact validHistory_writeSliceNodeAtProg hwf₂ (sliceNodePre_mono hnode (hs₁.trans hs₂))

private theorem validHistory_btreeDeleteRankProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q nodeBase leafIdx : ℕ} {nd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (btreeDeleteRankProg (((ctx, q), (nodeBase, leafIdx)), nd))) := by
  unfold btreeDeleteRankProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_swarRankClampedProg w _ _)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁ (validHistory_laneGetBoundedProg w _ _)
    fun _ s₂ hwf₂ hs₂ => ?_
  exact validHistory_ite
    (fun _ => validHistory_btreeDeleteHitProg hwf₂ (sliceNodePre_mono hnode (hs₁.trans hs₂)))
    (fun _ => trivial)

private theorem validHistory_btreeDeleteLeafProg {w : ℕ} {ctx : BTreeSliceCtx} {leafIdx q : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeDeleteLeafProg (ctx, (leafIdx, q)))) := by
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold btreeDeleteLeafProg; simp only [pure_bind]
  exact validHistory_bind_wf hwf (validHistory_readSliceNodeAtProg hnode) fun _ _ hwf' hfr' =>
    validHistory_btreeDeleteRankProg hwf' (sliceNodePre_mono hnode hfr')

private theorem validHistory_btreeDeleteNonEmptyProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q rt fuel : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeDeleteNonEmptyProg (((ctx, q), rt), fuel))) := by
  unfold btreeDeleteNonEmptyProg
  exact validHistory_bind_wf hwf (validHistory_descendLoopProg hpre) fun _ _ hwf' hfr' =>
    validHistory_btreeDeleteLeafProg hwf' (btreeSlicePre_mono hpre hfr')

/-- Memory history admissibility for `btreeDeleteBoundedProg` under `Memory.WellFormed` and
`BTreeSlicePre`. -/
theorem validHistory_btreeDeleteBoundedProg {w : ℕ} {ctx : BTreeSliceCtx} {q : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeDeleteBoundedProg (ctx, q))) := by
  have hhdr := sliceHdrPre_of_btreeSlicePre hpre
  unfold btreeDeleteBoundedProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceHdrAtProg hhdr) fun _ _ hwf' hfr' => ?_
  exact validHistory_ite
    (fun _ => trivial)
    (fun _ => validHistory_btreeDeleteNonEmptyProg hwf' (btreeSlicePre_mono hpre hfr'))

private theorem validHistory_btreeUpdateHitProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q newVal nodeBase leafIdx r kAt : ℕ} {nd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (btreeUpdateHitProg (((ctx, (q, newVal)), (nodeBase, leafIdx)), ((r, kAt), nd)))) := by
  unfold btreeUpdateHitProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  exact validHistory_bind_wf hwf (validHistory_wordUpdateAtBoundedProg w _ _) fun _ _ hwf' hfr' =>
    validHistory_writeSliceNodeAtProg hwf' (sliceNodePre_mono hnode hfr')

private theorem validHistory_btreeUpdateRankProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q newVal nodeBase leafIdx : ℕ} {nd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (btreeUpdateRankProg (((ctx, (q, newVal)), (nodeBase, leafIdx)), nd))) := by
  unfold btreeUpdateRankProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_swarRankClampedProg w _ _)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁ (validHistory_laneGetBoundedProg w _ _)
    fun _ s₂ hwf₂ hs₂ => ?_
  exact validHistory_ite
    (fun _ => validHistory_btreeUpdateHitProg hwf₂ (sliceNodePre_mono hnode (hs₁.trans hs₂)))
    (fun _ => trivial)

private theorem validHistory_btreeUpdateLeafProg {w : ℕ} {ctx : BTreeSliceCtx}
    {leafIdx q newVal : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeUpdateLeafProg (ctx, (leafIdx, (q, newVal))))) := by
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold btreeUpdateLeafProg; simp only [pure_bind]
  exact validHistory_bind_wf hwf (validHistory_readSliceNodeAtProg hnode) fun _ _ hwf' hfr' =>
    validHistory_btreeUpdateRankProg hwf' (sliceNodePre_mono hnode hfr')

private theorem validHistory_btreeUpdateNonEmptyProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q newVal rt : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeUpdateNonEmptyProg ((ctx, (q, newVal)), rt))) := by
  unfold btreeUpdateNonEmptyProg
  exact validHistory_bind_wf hwf (validHistory_descendLoopProg hpre) fun _ _ hwf' hfr' =>
    validHistory_btreeUpdateLeafProg hwf' (btreeSlicePre_mono hpre hfr')

/-- Memory history admissibility for `btreeUpdateBoundedProg` under `Memory.WellFormed` and
`BTreeSlicePre`. -/
theorem validHistory_btreeUpdateBoundedProg {w : ℕ} {ctx : BTreeSliceCtx} {q newVal : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeUpdateBoundedProg (ctx, (q, newVal)))) := by
  have hhdr := sliceHdrPre_of_btreeSlicePre hpre
  unfold btreeUpdateBoundedProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceHdrAtProg hhdr) fun _ _ hwf' hfr' => ?_
  exact validHistory_ite
    (fun _ => trivial)
    (fun _ => validHistory_btreeUpdateNonEmptyProg hwf' (btreeSlicePre_mono hpre hfr'))

private theorem validHistory_initEmptyRootAtProg {w : ℕ} {nctx : SliceNodeCtx} {hctx : SliceHdrCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w nctx s.frontier) (hhdr : SliceHdrPre w hctx s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (initEmptyRootAtProg (nctx, hctx))) := by
  unfold initEmptyRootAtProg
  refine validHistory_bind_wf hwf (validHistory_writeSliceNodeAtProg hwf hnode)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁
    (validHistory_writeSliceHdrAtProg hwf₁ (sliceHdrPre_mono hhdr hs₁))
    fun _ s₂ hwf₂ hs₂ => ?_
  exact validHistory_bind_wf hwf₂
    (validHistory_writeSliceHdrAtProg hwf₂ (sliceHdrPre_mono hhdr (hs₁.trans hs₂)))
    fun _ _ _ _ => trivial

private theorem validHistory_execRootSplitProg {w : ℕ} {ctx : BTreeSliceCtx}
    {hdrBase nodeBase al rt : ℕ} {rootNd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier)
    (hhdr : SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (execRootSplitProg ((ctx, (hdrBase, nodeBase)), ((al, rt), rootNd)))) := by
  unfold execRootSplitProg
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_bind_wf hwf (validHistory_computeRootSplitProg w _ _)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁
    (validHistory_writeTwoNodesAtProg hwf₁ (sliceNodePre_mono hnode hs₁))
    fun _ s₂ hwf₂ hs₂ => ?_
  refine validHistory_bind_wf hwf₂
    (validHistory_writeSliceNodeAtProg hwf₂ (sliceNodePre_mono hnode (hs₁.trans hs₂)))
    fun _ s₃ hwf₃ hs₃ => ?_
  exact validHistory_bind_wf hwf₃
    (validHistory_writeSliceHdrAtProg hwf₃ (sliceHdrPre_mono hhdr (hs₁.trans (hs₂.trans hs₃))))
    fun _ _ _ _ => trivial

private theorem validHistory_prepareNonEmptyRootProg {w : ℕ} {ctx : BTreeSliceCtx}
    {hdrBase nodeBase : ℕ} {hdr : ℕ × ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier)
    (hhdr : SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (prepareNonEmptyRootProg ((ctx, (hdrBase, nodeBase)), hdr))) := by
  unfold prepareNonEmptyRootProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceNodeAtProg hnode)
    fun _ _ hwf' hfr' => ?_
  exact validHistory_ite
    (fun _ => validHistory_execRootSplitProg hwf'
      (sliceNodePre_mono hnode hfr') (sliceHdrPre_mono hhdr hfr'))
    (fun _ => trivial)

private theorem validHistory_prepareRootBoundedProg {w : ℕ} {ctx : BTreeSliceCtx}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (prepareRootBoundedProg ctx)) := by
  have hhdr := sliceHdrPre_of_btreeSlicePre hpre
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold prepareRootBoundedProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceHdrAtProg hhdr) fun _ _ hwf' hfr' => ?_
  exact validHistory_ite
    (fun _ => validHistory_initEmptyRootAtProg hwf'
      (sliceNodePre_mono hnode hfr') (sliceHdrPre_mono hhdr hfr'))
    (fun _ => validHistory_prepareNonEmptyRootProg hwf'
      (sliceNodePre_mono hnode hfr') (sliceHdrPre_mono hhdr hfr'))

private theorem validHistory_finishChildSplitWritesProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q hdrBase nodeBase al cur childIdx : ℕ}
    {res : ((ℕ × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ((ℕ × (ℕ × ℕ)) × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier)
    (hhdr : SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (finishChildSplitWritesProg
          (((ctx, q), (hdrBase, nodeBase)), ((al, (cur, childIdx)), res)))) := by
  unfold finishChildSplitWritesProg
  refine validHistory_bind_wf hwf (validHistory_writeTwoNodesAtProg hwf hnode)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁
    (validHistory_writeSliceNodeAtProg hwf₁ (sliceNodePre_mono hnode hs₁))
    fun _ s₂ hwf₂ hs₂ => ?_
  refine validHistory_bind_wf hwf₂
    (validHistory_writeSliceHdrAtProg hwf₂ (sliceHdrPre_mono hhdr (hs₁.trans hs₂)))
    fun _ _ _ _ => ?_
  exact validHistory_ite (fun _ => trivial) (fun _ => trivial)

private theorem validHistory_splitChildBodyProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q hdrBase al cur r childIdx : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s)
    (hhdr : SliceHdrPre w (ctxHdrAt ctx hdrBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (splitChildBodyProg (((ctx, q), (hdrBase, al)), (cur, (r, childIdx))))) := by
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold splitChildBodyProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceNodeAtProg hnode)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁
    (validHistory_readSliceNodeAtProg (sliceNodePre_mono hnode hs₁))
    fun _ s₂ hwf₂ hs₂ => ?_
  refine validHistory_bind_wf hwf₂ (validHistory_computeChildSplitProg w _ _)
    fun _ s₃ hwf₃ hs₃ => ?_
  exact validHistory_finishChildSplitWritesProg hwf₃
    (sliceNodePre_mono hnode (hs₁.trans (hs₂.trans hs₃)))
    (sliceHdrPre_mono hhdr (hs₁.trans (hs₂.trans hs₃)))

private theorem validHistory_splitChildAndStepProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q cur r childIdx : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (splitChildAndStepProg ((ctx, q), (cur, (r, childIdx))))) := by
  have hhdr := sliceHdrPre_of_btreeSlicePre hpre
  unfold splitChildAndStepProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceHdrAtProg hhdr) fun _ _ hwf' hfr' => ?_
  exact validHistory_ite
    (fun _ => validHistory_splitChildBodyProg hwf'
      (btreeSlicePre_mono hpre hfr') (sliceHdrPre_mono hhdr hfr'))
    (fun _ => trivial)

private theorem validHistory_descendSplitBranchProg {w : ℕ} {ctx : BTreeSliceCtx}
    {q nodeBase cur : ℕ} {nd : ℕ × (ℕ × ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s)
    (hnode : SliceNodePre w (ctxNodeAt ctx nodeBase) s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (descendSplitBranchProg (((ctx, q), (nodeBase, cur)), nd))) := by
  unfold descendSplitBranchProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_swarRankClampedProg w _ _)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁ (validHistory_laneGetBoundedProg w _ _)
    fun _ s₂ hwf₂ hs₂ => ?_
  refine validHistory_bind_wf hwf₂
    (validHistory_readSliceNodeAtProg (sliceNodePre_mono hnode (hs₁.trans hs₂)))
    fun _ s₃ hwf₃ hs₃ => ?_
  exact validHistory_ite
    (fun _ => validHistory_splitChildAndStepProg hwf₃
      (btreeSlicePre_mono hpre (hs₁.trans (hs₂.trans hs₃))))
    (fun _ => trivial)

private theorem validHistory_descendSplitStepProg {w : ℕ} {ctx : BTreeSliceCtx} {q cur : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (descendSplitStepProg ((ctx, q), cur))) := by
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold descendSplitStepProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceNodeAtProg hnode)
    fun _ _ hwf' hfr' => ?_
  exact validHistory_ite
    (fun _ => trivial)
    (fun _ => validHistory_descendSplitBranchProg hwf'
      (btreeSlicePre_mono hpre hfr') (sliceNodePre_mono hnode hfr'))

private theorem validHistory_descendSplitLoopProg {w : ℕ} {ctx : BTreeSliceCtx} {q cur fuel : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (descendSplitLoopProg (((ctx, q), cur), fuel))) := by
  unfold descendSplitLoopProg
  exact validHistory_iterate_wf fuel cur s hwf fun _ _ hwf' hfr' =>
    validHistory_descendSplitStepProg hwf' (btreeSlicePre_mono hpre hfr')

private theorem validHistory_finishLeafInsertBoundedProg {w : ℕ} {ctx : BTreeSliceCtx}
    {leafIdx q val : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (finishLeafInsertBoundedProg (ctx, (leafIdx, (q, val))))) := by
  have hnode := sliceNodePre_of_btreeSlicePre hpre
  unfold finishLeafInsertBoundedProg; simp only [pure_bind]
  refine validHistory_bind_wf hwf (validHistory_readSliceNodeAtProg hnode)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁ (validHistory_computeLeafInsertNodeProg w _ _)
    fun _ s₂ hwf₂ hs₂ => ?_
  exact validHistory_writeSliceNodeAtProg hwf₂ (sliceNodePre_mono hnode (hs₁.trans hs₂))

/-- Memory history admissibility for `btreeInsertBoundedProg` under `Memory.WellFormed` and
`BTreeSlicePre`. -/
theorem validHistory_btreeInsertBoundedProg {w : ℕ} {ctx : BTreeSliceCtx} {q val : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s) (hpre : BTreeSlicePre w ctx s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (btreeInsertBoundedProg (ctx, (q, val)))) := by
  unfold btreeInsertBoundedProg
  refine validHistory_bind_wf hwf (validHistory_prepareRootBoundedProg hwf hpre)
    fun _ s₁ hwf₁ hs₁ => ?_
  refine validHistory_bind_wf hwf₁
    (validHistory_descendSplitLoopProg hwf₁ (btreeSlicePre_mono hpre hs₁))
    fun _ s₂ hwf₂ hs₂ => ?_
  exact validHistory_finishLeafInsertBoundedProg hwf₂
    (btreeSlicePre_mono hpre (hs₁.trans hs₂))

/-! ## Section 3: `LargeTrieProg` `ValidHistory` Proofs -/

private theorem trieLayout_valid_mono {L : TrieLayout} {w fr₁ fr₂ : ℕ}
    (h : L.Valid w fr₁) (hle : fr₁ ≤ fr₂) : L.Valid w fr₂ := by
  obtain ⟨hw, hwv, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct, hmc, h6m, h6q,
    hd1, hd2, hfr⟩ := h
  exact ⟨hw, hwv, hpb, hbc0, hbc, hbc_pb, hmn1, hmn_pb, hqm_pb, hct, hmc, h6m, h6q,
    hd1, hd2, hfr.trans hle⟩

private theorem and_shiftLeft_mask_lt (x bc : ℕ) :
    x &&& ((1 <<< bc) - 1) < 2 ^ bc := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos bc)

private theorem validHistory_bufWalkStepProg {w : ℕ} {ctx : TrieCtx}
    {st : (ℕ × ℕ) × ℕ} {s : Memory.State}
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufWalkStepProg (ctx, st))) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  rcases st with ⟨⟨found, cur⟩, remKey⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre
  obtain ⟨hw, hwv, hpb, _, _, _, hmn1, _, _, _, _, _, _, hd1, hd2, hfr⟩ := hpre
  subst hwv
  have hch_lt : remKey &&& ((1 <<< bc) - 1) < 2 ^ bc := and_shiftLeft_mask_lt remKey bc
  unfold bufWalkStepProg; simp only [pure_bind]
  by_cases hcur : cur < mn
  · rw [ite_eq_left hcur]
    have hidx : (cur <<< bc) + (remKey &&& ((1 <<< bc) - 1)) < mn * 2 ^ bc :=
      child_idx_lt hcur hch_lt
    refine validHistory_bind_ro
      (validHistory_readPackedCompGen ⟨mn * 2 ^ bc, hw, rfl, hpb, hidx, by omega⟩)
      fun _ _ _ => ?_
    exact validHistory_ite (fun _ => trivial) fun _ =>
      validHistory_ite (fun _ => validHistory_ite (fun _ => trivial) (fun _ => trivial))
        (fun _ => trivial)
  · rw [ite_eq_right hcur]
    have hidx0 : 0 < mn * 2 ^ bc := Nat.mul_pos hmn1 (Nat.two_pow_pos bc)
    refine validHistory_bind_ro
      (validHistory_readPackedCompGen ⟨mn * 2 ^ bc, hw, rfl, hpb, hidx0, by omega⟩)
      fun _ _ _ => ?_
    exact validHistory_ite (fun _ => trivial) fun _ =>
      validHistory_ite (fun _ => validHistory_ite (fun _ => trivial) (fun _ => trivial))
        (fun _ => trivial)

private theorem validHistory_bufWalkLoopProg {w : ℕ} {ctx : TrieCtx}
    {st : (ℕ × ℕ) × ℕ} {fuel : ℕ} {s : Memory.State}
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufWalkLoopProg ((ctx, st), fuel))) := by
  unfold bufWalkLoopProg
  exact validHistory_iterate_ro fuel st s fun _ _ hfr' =>
    validHistory_bufWalkStepProg (trieLayout_valid_mono hpre hfr')

private theorem validHistory_bufWalkBoundedProg {w : ℕ} {ctx : TrieCtx} {rKey : ℕ}
    {s : Memory.State} (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufWalkBoundedProg (ctx, rKey))) := by
  unfold bufWalkBoundedProg; simp only [pure_bind]
  exact validHistory_bind_ro (validHistory_bufWalkLoopProg hpre) fun _ _ _ => trivial

/-- Memory history admissibility for `bufLookupBoundedProg` under `TrieLayout.Valid` (read-only;
no `Memory.WellFormed` premise required). -/
theorem validHistory_bufLookupBoundedProg {w : ℕ} {ctx : TrieCtx} {rKey : ℕ}
    {s : Memory.State} (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufLookupBoundedProg (ctx, rKey))) := by
  have hpre0 := hpre
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, _, hd2, hfr⟩ := hpre
  subst hwv
  unfold bufLookupBoundedProg; simp only [pure_bind]
  dsimp only [trieMb, trieOn, trieOi, triePb, trieWv, trieMn, trieQm]
  refine validHistory_bind_ro (validHistory_bufWalkBoundedProg hpre0) fun wk s₁ hs₁ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_ite (fun hwk => ?_) (fun _ => trivial)
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun id1 s₂ hs₂ => ?_
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun act s₃ hs₃ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_ite (fun hid => ?_) (fun _ => trivial)
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₄ hs₄ => ?_
  exact validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun _ _ _ => trivial

/-- Memory history admissibility for `bufDeleteBoundedProg` under `Memory.WellFormed` and
`TrieLayout.Valid`. -/
theorem validHistory_bufDeleteBoundedProg {w : ℕ} {ctx : TrieCtx} {rKey : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufDeleteBoundedProg (ctx, rKey))) := by
  have hpre0 := hpre
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, _, hd2, hfr⟩ := hpre
  subst hwv
  unfold bufDeleteBoundedProg; simp only [pure_bind]
  dsimp only [trieMb, trieOn, triePb, trieWv, trieMn]
  refine validHistory_bind_wf hwf (validHistory_bufWalkBoundedProg hpre0)
    fun wk s₁ hwf₁ hs₁ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_ite (fun hwk => ?_) (fun _ => trivial)
  refine validHistory_bind_wf hwf₁
    (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₂ hwf₂ hs₂ => ?_
  refine validHistory_bind_wf hwf₂
    (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₃ hwf₃ hs₃ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  exact validHistory_writePackedCompGen hwf₃ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩

private theorem validHistory_bufAllocNodeProg {w : ℕ} {ctx : TrieCtx} {cur ch : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier)
    (hch : ch < 2 ^ (TrieLayout.ofCtx ctx).bChar) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufAllocNodeProg (ctx, (cur, ch)))) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre hch
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, hd1, hd2, hfr⟩ := hpre
  subst hwv
  unfold bufAllocNodeProg
  refine validHistory_bind_wf hwf
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun u s₁ hwf₁ hs₁ => ?_
  refine validHistory_ite (fun hcur => ?_) (fun _ => trivial)
  refine validHistory_ite (fun hu => ?_) (fun _ => trivial)
  have hidx : (cur <<< bc) + ch < mn * 2 ^ bc := child_idx_lt hcur hch
  refine validHistory_bind_wf hwf₁
    (validHistory_writePackedCompGen hwf₁ ⟨mn * 2 ^ bc, hw, rfl, hpb, hidx, by omega⟩)
    fun _ s₂ hwf₂ hs₂ => ?_
  refine validHistory_bind_wf hwf₂
    (validHistory_writePackedCompGen hwf₂ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₃ hwf₃ hs₃ => ?_
  refine validHistory_bind_wf hwf₃
    (validHistory_writePackedCompGen hwf₃ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₄ hwf₄ hs₄ => ?_
  refine validHistory_bind_wf hwf₄
    (validHistory_writePackedCompGen hwf₄ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₅ hwf₅ hs₅ => ?_
  exact validHistory_bind_wf hwf₅
    (validHistory_writePackedCompGen hwf₅ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun _ _ _ _ => trivial

private theorem validHistory_bufEnsureStepProg {w : ℕ} {ctx : TrieCtx} {st : ℕ × ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufEnsureStepProg (ctx, st))) := by
  have hpre0 := hpre
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  rcases st with ⟨cur, remKey⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre
  obtain ⟨hw, hwv, hpb, _, _, _, hmn1, _, _, _, _, _, _, hd1, hd2, hfr⟩ := hpre
  subst hwv
  have hch_lt : remKey &&& ((1 <<< bc) - 1) < 2 ^ bc := and_shiftLeft_mask_lt remKey bc
  unfold bufEnsureStepProg; simp only [pure_bind]
  by_cases hcur : cur < mn
  · rw [ite_eq_left hcur]
    have hidx : (cur <<< bc) + (remKey &&& ((1 <<< bc) - 1)) < mn * 2 ^ bc :=
      child_idx_lt hcur hch_lt
    refine validHistory_bind_wf hwf
      (validHistory_readPackedCompGen ⟨mn * 2 ^ bc, hw, rfl, hpb, hidx, by omega⟩)
      fun nxt s₁ hwf₁ hs₁ => ?_
    refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
    refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
    exact validHistory_bind_wf hwf₁
      (validHistory_bufAllocNodeProg hwf₁ (trieLayout_valid_mono hpre0 hs₁) hch_lt)
      fun _ _ _ _ => trivial
  · rw [ite_eq_right hcur]
    have hidx0 : 0 < mn * 2 ^ bc := Nat.mul_pos hmn1 (Nat.two_pow_pos bc)
    refine validHistory_bind_wf hwf
      (validHistory_readPackedCompGen ⟨mn * 2 ^ bc, hw, rfl, hpb, hidx0, by omega⟩)
      fun _ _ _ _ => ?_
    exact validHistory_ite (fun h => absurd h hcur) (fun _ => trivial)

private theorem validHistory_bufEnsureLoopProg {w : ℕ} {ctx : TrieCtx} {st : ℕ × ℕ}
    {fuel : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufEnsureLoopProg ((ctx, st), fuel))) := by
  unfold bufEnsureLoopProg
  exact validHistory_iterate_wf fuel st s hwf fun _ _ hwf' hfr' =>
    validHistory_bufEnsureStepProg hwf' (trieLayout_valid_mono hpre hfr')

private theorem validHistory_bufAttachLeafProg {w : ℕ} {ctx : TrieCtx} {leaf bkt loc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufAttachLeafProg (ctx, (leaf, (bkt, loc))))) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, _, hd2, hfr⟩ := hpre
  subst hwv
  unfold bufAttachLeafProg
  refine validHistory_ite (fun hleaf => ?_) (fun _ => trivial)
  refine validHistory_bind_wf hwf
    (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun id1 s₁ hwf₁ hs₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · refine validHistory_bind_wf hwf₁
      (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
      fun id s₂ hwf₂ hs₂ => ?_
    refine validHistory_ite (fun hid => ?_) (fun _ => trivial)
    refine validHistory_bind_wf hwf₂
      (validHistory_writePackedCompGen hwf₂ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₃ hwf₃ hs₃ => ?_
    refine validHistory_bind_wf hwf₃
      (validHistory_writePackedCompGen hwf₃ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₄ hwf₄ hs₄ => ?_
    refine validHistory_bind_wf hwf₄
      (validHistory_writePackedCompGen hwf₄ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₅ hwf₅ hs₅ => ?_
    refine validHistory_bind_wf hwf₅
      (validHistory_writePackedCompGen hwf₅ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₆ hwf₆ hs₆ => ?_
    refine validHistory_bind_wf hwf₆
      (validHistory_writePackedCompGen hwf₆ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₇ hwf₇ hs₇ => ?_
    exact validHistory_writePackedCompGen hwf₇ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩
  · simp only [pure_bind]
    refine validHistory_ite (fun hid => ?_) (fun _ => trivial)
    refine validHistory_bind_wf hwf₁
      (validHistory_writePackedCompGen hwf₁ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₂ hwf₂ hs₂ => ?_
    refine validHistory_bind_wf hwf₂
      (validHistory_writePackedCompGen hwf₂ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₃ hwf₃ hs₃ => ?_
    exact validHistory_writePackedCompGen hwf₃ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩

/-- Memory history admissibility for `bufInsertBoundedProg` under `Memory.WellFormed` and
`TrieLayout.Valid`. -/
theorem validHistory_bufInsertBoundedProg {w : ℕ} {ctx : TrieCtx} {rKey bkt loc : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufInsertBoundedProg (ctx, (rKey, (bkt, loc))))) := by
  unfold bufInsertBoundedProg; simp only [pure_bind]
  exact validHistory_bind_wf hwf (validHistory_bufEnsureLoopProg hwf hpre)
    fun _ _ hwf' hfr' =>
      validHistory_bufAttachLeafProg hwf' (trieLayout_valid_mono hpre hfr')

/-- Memory history admissibility for `bufCheckSlotBoundedProg` under `TrieLayout.Valid` (read-only;
no `Memory.WellFormed` premise required). -/
theorem validHistory_bufCheckSlotBoundedProg {w : ℕ} {ctx : TrieCtx} {id : ℕ}
    {s : Memory.State} (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufCheckSlotBoundedProg (ctx, id))) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre
  obtain ⟨hw, hwv, hpb, _, _, _, _, _, _, _, _, _, _, _, hd2, hfr⟩ := hpre
  subst hwv
  unfold bufCheckSlotBoundedProg
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₁ hs₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun hid => ?_) (fun _ => trivial)
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun leaf s₂ hs₂ => ?_
  refine validHistory_ite (fun hleaf => ?_) (fun _ => trivial)
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₃ hs₃ => ?_
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₄ hs₄ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => trivial)
  refine validHistory_ite (fun _ => trivial) fun _ => ?_
  refine validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun _ s₅ hs₅ => ?_
  exact validHistory_bind_ro
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun _ _ _ => trivial

private theorem validHistory_bufClearOneBoundedProg {w : ℕ} {ctx : TrieCtx} {dummy : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufClearOneBoundedProg (ctx, dummy))) := by
  rcases ctx with ⟨⟨⟨mb, oc⟩, ⟨on_, oi⟩⟩, ⟨⟨pb, wv⟩, ⟨⟨ct, bc⟩, ⟨mn, qm⟩⟩⟩⟩
  dsimp only [TrieLayout.ofCtx, TrieLayout.Valid] at hpre
  obtain ⟨hw, hwv, hpb, _, _, _, hmn1, _, _, _, _, _, _, hd1, hd2, hfr⟩ := hpre
  subst hwv
  unfold bufClearOneBoundedProg
  refine validHistory_bind_wf hwf
    (validHistory_readPackedCompGen ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
    fun na s₁ hwf₁ hs₁ => ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => ?_)
  · simp only [pure_bind]
    refine validHistory_ite (fun hu => ?_) (fun _ => trivial)
    refine validHistory_bind_wf hwf₁
      (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
      fun p s₂ hwf₂ hs₂ => ?_
    refine validHistory_bind_wf hwf₂
      (validHistory_readPackedCompGen ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
      fun ch s₃ hwf₃ hs₃ => ?_
    have htail : ∀ s₄, Memory.WellFormed w s₄ → s.frontier ≤ s₄.frontier →
        (Memory.spec w).ValidHistory s₄ ((Memory.spec w).clientHistory s₄ (do
          writePackedCompGenProg ((((mb, on_), (pb, w)), 6 * (na - 1) + 2), 0)
          writePackedCompGenProg ((((mb, oi), (pb, w)), 6 * qm), na - 1)
          writePackedCompGenProg ((((mb, oi), (pb, w)), 6 * qm + 1), 0)
          pure 0)) := by
      intro s₄ hwf₄ hs₄
      refine validHistory_bind_wf hwf₄
        (validHistory_writePackedCompGen hwf₄ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
        fun _ s₅ hwf₅ hs₅ => ?_
      refine validHistory_bind_wf hwf₅
        (validHistory_writePackedCompGen hwf₅ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
        fun _ s₆ hwf₆ hs₆ => ?_
      exact validHistory_bind_wf hwf₆
        (validHistory_writePackedCompGen hwf₆ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
        fun _ _ _ _ => trivial
    have hfr₃ : s.frontier ≤ s₃.frontier := hs₁.trans (hs₂.trans hs₃)
    refine validHistory_ite (fun hp => ?_) (fun _ => htail s₃ hwf₃ hfr₃)
    refine validHistory_ite (fun hch => ?_) (fun _ => htail s₃ hwf₃ hfr₃)
    rw [Nat.shiftLeft_eq, one_mul] at hch
    have hidx : (p <<< bc) + ch < mn * 2 ^ bc := child_idx_lt hp hch
    exact validHistory_bind_wf hwf₃
      (validHistory_writePackedCompGen hwf₃ ⟨mn * 2 ^ bc, hw, rfl, hpb, hidx, by omega⟩)
      fun _ s₄ hwf₄ hs₄ => htail s₄ hwf₄ (hfr₃.trans hs₄)
  · refine validHistory_bind_wf hwf₁
      (validHistory_writePackedCompGen hwf₁ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₂ hwf₂ hs₂ => ?_
    refine validHistory_bind_wf hwf₂
      (validHistory_writePackedCompGen hwf₂ ⟨6 * qm + 6, hw, rfl, hpb, by omega, by omega⟩)
      fun _ s₃ hwf₃ hs₃ => ?_
    exact validHistory_bind_wf hwf₃
      (validHistory_writePackedCompGen hwf₃ ⟨6 * mn, hw, rfl, hpb, by omega, by omega⟩)
      fun _ _ _ _ => trivial

private theorem validHistory_bufClearLoopProg {w : ℕ} {ctx : TrieCtx} {u k : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufClearLoopProg ((ctx, u), k))) := by
  unfold bufClearLoopProg
  exact validHistory_iterate_wf k u s hwf fun _ _ hwf' hfr' =>
    validHistory_bufClearOneBoundedProg hwf' (trieLayout_valid_mono hpre hfr')

/-- Memory history admissibility for `bufClearStepsBoundedProg` under `Memory.WellFormed` and
`TrieLayout.Valid`. -/
theorem validHistory_bufClearStepsBoundedProg {w : ℕ} {ctx : TrieCtx} {k : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hpre : (TrieLayout.ofCtx ctx).Valid w s.frontier) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (bufClearStepsBoundedProg (ctx, k))) := by
  unfold bufClearStepsBoundedProg
  exact validHistory_bind_wf hwf (validHistory_bufClearLoopProg hwf hpre) fun _ _ _ _ => trivial

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

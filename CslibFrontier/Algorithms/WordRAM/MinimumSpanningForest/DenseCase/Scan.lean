/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ScanOps
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded-Heap DJP Tree Growth and Sparse Heap Reset (`ftRunTree`)

Implements and verifies bounded-heap DJP tree growth (`ftRunTree`) for a single phase of
`[FredmanTarjan1987]` (§3) / `[PettieRamachandran2002]` (§3.4 `DenseCase`) toward `#8624`,
integrating CSR vertex scans (`DenseCase/ScanOps`), thresholded min-edge extraction, sparse
`O(touchedLen + 1)` Fibonacci heap reset via `FibonacciHeap.Native.Reset.resetProg`, supervertex
assignment, and amortized vertex potential accounting.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftRunTree`: Word-RAM program running
  one bounded-heap DJP tree from root `t` and resetting touched heap entries.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftRunTreeSafe`: word-width safety
  precondition for `ftRunTree`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.realizes_ftRunTree`: `Realizes .exact`
  witness for `ftRunTree` with zero auxiliary register work.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftRunTree_spec`: correctness,
  `FTPhaseInv` advancement, heap reset invariant, and amortized potential bound `≤ 7`.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.FibonacciHeap
open Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.Query.MinimumSpanningForest

/-! ## Private Tree-Growth Sub-Programs and `ftRunTree` -/

private structure FTRecordSelArgs where
  ctx : FTCtx
  y : ℕ
  selLen : ℕ

private word_enc_structure encFTRecordSelArgs : FTRecordSelArgs where
  ctx : encFTCtx,
  y : wordWords,
  selLen : wordWords

private instance : WordEncoding FTRecordSelArgs := ⟨11, encFTRecordSelArgs⟩

private structure FTExtractArgs where
  ctx : FTCtx
  treeId : ℕ
  touchedLen : ℕ
  selLen : ℕ

private word_enc_structure encFTExtractArgs : FTExtractArgs where
  ctx : encFTCtx,
  treeId : wordWords,
  touchedLen : wordWords,
  selLen : wordWords

private instance : WordEncoding FTExtractArgs := ⟨12, encFTExtractArgs⟩

private structure FTGrowEnv where
  ctx : FTCtx
  treeId : ℕ

private word_enc_structure encFTGrowEnv : FTGrowEnv where
  ctx : encFTCtx,
  treeId : wordWords

private instance : WordEncoding FTGrowEnv := ⟨10, encFTGrowEnv⟩

private structure FTFinishArgs where
  ctx : FTCtx
  treeId : ℕ
  nComp : ℕ
  selLen : ℕ
  jn : ℕ

private word_enc_structure encFTFinishArgs : FTFinishArgs where
  ctx : encFTCtx,
  treeId : wordWords,
  nComp : wordWords,
  selLen : wordWords,
  jn : wordWords

private instance : WordEncoding FTFinishArgs := ⟨13, encFTFinishArgs⟩

private def ftRecordSel (d : FTRecordSelArgs) : Memory.Prog Unit := do
  let eIdx ← Memory.read (d.ctx.auxBase + d.ctx.n + d.y)
  let origId ← Memory.read (d.ctx.edgeBase + 4 * eIdx + 3)
  Memory.write (d.ctx.selBufBase + d.selLen) origId

private def ftRecordSelSafe (w : ℕ) (d : FTRecordSelArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.ctx.auxBase + 2 * d.ctx.n) ∧ Fits w (d.ctx.edgeBase + 4 * d.ctx.m) ∧
    d.y < d.ctx.n ∧ d.ctx.auxBase + 2 * d.ctx.n ≤ s.frontier ∧
    d.ctx.edgeBase + 4 * d.ctx.m ≤ s.frontier ∧ d.ctx.selBufBase + d.selLen < s.frontier ∧
    s.mem (d.ctx.auxBase + d.ctx.n + d.y) < d.ctx.m

private theorem realizes_ftRecordSel : Realizes .exact
    ftRecordSel WordEncoding.encode WordEncoding.encode ftRecordSelSafe (fun _ _ => 0) := by
  unfold ftRecordSel
  realize
  all_goals
    rcases h with ⟨h16, haux, hedge, hy, haux_fr, hedge_fr, hsel_fr, he_lt⟩
    have hfront := hmem.frontier_fits
    fits

private def ftExtractAndAdvance (d : FTExtractArgs) : Memory.Prog FTGrowState := do
  let opt ← extractRawProg d.ctx.n d.ctx.fhBase
  match opt with
  | none => pure ⟨0, 0, d.touchedLen, d.selLen, d.ctx.n⟩
  | some p => do
    ftRecordSel ⟨d.ctx, p.1, d.selLen⟩
    let trY ← Memory.read (d.ctx.auxBase + p.1)
    if trY < d.treeId then
      pure ⟨0, 0, d.touchedLen, d.selLen + 1, trY⟩
    else do
      Memory.write (d.ctx.auxBase + p.1) d.treeId
      pure ⟨1, p.1, d.touchedLen, d.selLen + 1, d.ctx.n⟩

private def ftExtractAndAdvanceSafe (w : ℕ) (d : FTExtractArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.ctx.auxBase + 2 * d.ctx.n) ∧ Fits w (d.selLen + 1) ∧ Fits w d.ctx.n ∧
    d.treeId < d.ctx.n ∧ extractValid w ![d.ctx.n, d.ctx.fhBase] s ∧
    (∀ y k, (Memory.spec 0).clientResult s (extractRawProg d.ctx.n d.ctx.fhBase) = some (y, k) →
      let s₁ := (Memory.spec 0).clientState s (extractRawProg d.ctx.n d.ctx.fhBase)
      ftRecordSelSafe w ⟨d.ctx, y, d.selLen⟩ s₁ ∧
      d.ctx.auxBase + y < s₁.frontier)

private theorem realizes_ftExtractAndAdvance : Realizes .exact
    ftExtractAndAdvance WordEncoding.encode WordEncoding.encode
    ftExtractAndAdvanceSafe (fun _ _ => 0) := by
  unfold ftExtractAndAdvance
  realize [realizes_extractRawProg, realizes_ftRecordSel]
  all_goals
    rcases h with ⟨h16, haux, hsel, hn, ht, hex, hrec⟩
    have hfront := hmem.frontier_fits
    first
    | exact hex
    | fits
    | (cases hopt : (Memory.spec 0).clientResult s (extractRawProg d.ctx.n d.ctx.fhBase) with
      | none =>
        have h0 : optionWordsWith (WordEncoding.encode (α := ℕ × ℕ)) none 0 = 0 := rfl
        simp only [hopt, h0] at *
        contradiction
      | some p =>
        have hp_rec := hrec p.1 p.2 hopt
        have hfr_rec := Memory.frontier_le_clientState (w := 0)
          ((Memory.spec 0).clientState s (extractRawProg d.ctx.n d.ctx.fhBase))
          (ftRecordSel ⟨d.ctx, p.1, d.selLen⟩)
        have h0 : optionWordsWith (WordEncoding.encode (α := ℕ × ℕ)) (some p) 0 = 1 := rfl
        have h1 : optionWordsWith (WordEncoding.encode (α := ℕ × ℕ)) (some p) 1 = p.1 := by
          simp [optionWordsWith, WordEncoding.encode]; rfl
        simp only [hopt, h0, h1] at *
        first
        | exact hp_rec.1
        | (apply haux.of_le; have hplt : p.1 < d.ctx.n := hp_rec.1.2.2.2.1; omega))

private def ftGrowStep (d : FTGrowEnv × FTGrowState) : Memory.Prog FTGrowState := do
  let tl ← ftScanVertex ⟨d.1.ctx, d.1.treeId, d.2.x, d.2.touchedLen⟩
  let sz ← Memory.read (d.1.ctx.fhBase + 9 * d.1.ctx.n + 4)
  if sz = 0 then
    pure ⟨0, 0, tl, d.2.selLen, d.1.ctx.n⟩
  else if d.1.ctx.thresh < sz then
    pure ⟨0, 0, tl, d.2.selLen, d.1.ctx.n⟩
  else
    ftExtractAndAdvance ⟨d.1.ctx, d.1.treeId, tl, d.2.selLen⟩

private def ftGrowStepSafe (w : ℕ) (d : FTGrowEnv × FTGrowState) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.1.ctx.fhBase + (9 * d.1.ctx.n + 5)) ∧ Fits w d.1.ctx.n ∧
    ftScanVertexSafe w ⟨d.1.ctx, d.1.treeId, d.2.x, d.2.touchedLen⟩ s ∧
    let tl := (Memory.spec 0).clientResult s
      (ftScanVertex ⟨d.1.ctx, d.1.treeId, d.2.x, d.2.touchedLen⟩)
    let s₁ := (Memory.spec 0).clientState s
      (ftScanVertex ⟨d.1.ctx, d.1.treeId, d.2.x, d.2.touchedLen⟩)
    d.1.ctx.fhBase + 9 * d.1.ctx.n + 4 < s₁.frontier ∧
    (s₁.mem (d.1.ctx.fhBase + 9 * d.1.ctx.n + 4) ≠ 0 →
      ¬(d.1.ctx.thresh < s₁.mem (d.1.ctx.fhBase + 9 * d.1.ctx.n + 4)) →
      ftExtractAndAdvanceSafe w ⟨d.1.ctx, d.1.treeId, tl, d.2.selLen⟩ s₁)

private theorem realizes_ftGrowStep : Realizes .exact
    ftGrowStep (appendWords encFTGrowEnv WordEncoding.encode) WordEncoding.encode
    ftGrowStepSafe (fun _ _ => 0) := by
  unfold ftGrowStep
  realize [realizes_ftScanVertex, realizes_ftExtractAndAdvance]
  all_goals
    rcases h with ⟨h16, hfh, hn, hscan, hsz_fr, hex⟩
    first
    | exact hscan
    | exact hex (by assumption) (by assumption)
    | fits

private def ftFinishTree (d : FTFinishArgs) : Memory.Prog (ℕ × ℕ) := do
  if d.jn < d.treeId then
    let supJn ← Memory.read (d.ctx.auxBase + 2 * d.ctx.n + d.jn)
    Memory.write (d.ctx.auxBase + 2 * d.ctx.n + d.treeId) supJn
    pure (d.nComp, d.selLen)
  else do
    Memory.write (d.ctx.auxBase + 2 * d.ctx.n + d.treeId) d.nComp
    pure (d.nComp + 1, d.selLen)

private def ftFinishTreeSafe (w : ℕ) (d : FTFinishArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.ctx.auxBase + 3 * d.ctx.n) ∧ Fits w (d.nComp + 1) ∧
    d.treeId < d.ctx.n ∧ d.ctx.auxBase + 3 * d.ctx.n ≤ s.frontier

private theorem realizes_ftFinishTree : Realizes .exact
    ftFinishTree WordEncoding.encode WordEncoding.encode ftFinishTreeSafe (fun _ _ => 0) := by
  unfold ftFinishTree
  realize
  all_goals
    rcases h with ⟨h16, haux, hnc, hs, haux_fr⟩
    have hfront := hmem.frontier_fits
    fits

/-! ## Public Bounded-Heap Tree Runner (`ftRunTree`) -/

/-- Native safety domain for `ftRunTree`. -/
def ftRunTreeSafe (w : ℕ) (args : FTRunTreeArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (args.ctx.auxBase + 5 * args.ctx.n) ∧ Fits w args.ctx.n ∧
    args.root < args.ctx.n ∧ args.ctx.auxBase + 5 * args.ctx.n ≤ s.frontier ∧
    let s₁ := ⟨Function.update s.mem (args.ctx.auxBase + args.root) args.root, s.frontier⟩
    whileSafe (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
      ftGrowStep ftGrowStepSafe w ⟨args.ctx, args.root⟩ args.ctx.n
      ⟨1, args.root, 0, args.selLen, args.ctx.n⟩ s₁ ∧
    let res := (Memory.spec 0).clientResult s₁
      (boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
        ftGrowStep ⟨args.ctx, args.root⟩ args.ctx.n
        ⟨1, args.root, 0, args.selLen, args.ctx.n⟩)
    let s₂ := (Memory.spec 0).clientState s₁
      (boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
        ftGrowStep ⟨args.ctx, args.root⟩ args.ctx.n
        ⟨1, args.root, 0, args.selLen, args.ctx.n⟩)
    ResetSafe w ⟨args.ctx.n, args.ctx.fhBase, args.ctx.auxBase + 4 * args.ctx.n, res.touchedLen⟩
      s₂ ∧
    let s₃ := (Memory.spec 0).clientState s₂
      (resetProg ⟨args.ctx.n, args.ctx.fhBase, args.ctx.auxBase + 4 * args.ctx.n, res.touchedLen⟩)
    ftFinishTreeSafe w ⟨args.ctx, args.root, args.nComp, res.selLen, res.jn⟩ s₃

/-- Grows one bounded-heap DJP tree from root `args.root`, sparsely resets the Fibonacci heap in
`O(touchedLen + 1)` operations via `resetProg`, and assigns `sup[args.root]`, returning
`(nComp', selLen')`. -/
def ftRunTree (args : FTRunTreeArgs) : Memory.Prog (ℕ × ℕ) := do
  Memory.write (args.ctx.auxBase + args.root) args.root
  let res ← boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
    ftGrowStep ⟨args.ctx, args.root⟩ args.ctx.n ⟨1, args.root, 0, args.selLen, args.ctx.n⟩
  resetProg ⟨args.ctx.n, args.ctx.fhBase, args.ctx.auxBase + 4 * args.ctx.n, res.touchedLen⟩
  ftFinishTree ⟨args.ctx, args.root, args.nComp, res.selLen, res.jn⟩

private theorem one_le_memoryCost_ftGrowStep (d : FTGrowEnv × FTGrowState) (s : Memory.State) :
    1 ≤ memoryCost (ftGrowStep d) s := by
  rw [ftGrowStep, memoryCost_bind']
  exact Nat.le_trans (one_le_memoryCost_ftScanVertex _ s) (Nat.le_add_right _ _)

private theorem realizes_ftRunTree_work : Realizes .exact
    ftRunTree WordEncoding.encode WordEncoding.encode ftRunTreeSafe
    (fun d s => whileWork (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
      ftGrowStep (fun _ _ => 0) ⟨d.ctx, d.root⟩ d.ctx.n
      ⟨1, d.root, 0, d.selLen, d.ctx.n⟩
      ⟨Function.update s.mem (d.ctx.auxBase + d.root) d.root, s.frontier⟩) := by
  unfold ftRunTree
  realize [realizes_ftGrowStep, realizes_resetProg, realizes_ftFinishTree]
  all_goals
    rcases h with ⟨h16, haux, hn, hs, haux_fr, hbw, hres, hfin⟩
    have hfront := hmem.frontier_fits
    first
    | (intro _; exact whileSafe_imp _ _ (safe := ftGrowStepSafe)
        (safe' := fun w x s => ftGrowStepSafe w (⟨d.ctx, d.root⟩, x.2) s)
        (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ _ hs' => hs') hbw)
    | exact hres
    | exact hfin
    | exact h16.of_le (by decide)
    | fits

/-- Uniform exact-basis realization of `ftRunTree` with zero extra local work. -/
theorem realizes_ftRunTree : Realizes .exact
    ftRunTree WordEncoding.encode WordEncoding.encode ftRunTreeSafe (fun _ _ => 0) := by
  refine realizes_ftRunTree_work.mono_mul 1 fun d s => ?_
  have hle := whileWork_zero_le (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
    ftGrowStep one_le_memoryCost_ftGrowStep ⟨d.ctx, d.root⟩ d.ctx.n
    ⟨1, d.root, 0, d.selLen, d.ctx.n⟩
    ⟨Function.update s.mem (d.ctx.auxBase + d.root) d.root, s.frontier⟩
  have hcost : memoryCost (boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
      ftGrowStep ⟨d.ctx, d.root⟩ d.ctx.n ⟨1, d.root, 0, d.selLen, d.ctx.n⟩)
      ⟨Function.update s.mem (d.ctx.auxBase + d.root) d.root, s.frontier⟩ ≤
      memoryCost (ftRunTree d) s := by
    rw [ftRunTree, memoryCost_bind', memoryCost_write, clientState_write, memoryCost_bind']
    omega
  omega

/-! ## Inner Specifications (`ftRelaxUpdate`, `ftScanVertex`, `ftExtractAndAdvance`) -/

private theorem ftExtract_merge_growInv {w n K nComp selLen0 selLen tl : ℕ}
    {hn : Fits w n} {hK : Fits w K} {ctx : FTCtx} {es : List (IndexedEdge n)} {t yf : Fin n}
    {eIdx : Fin es.length} {selIdxs0 selTree : List (Fin es.length)}
    {s₀ s s₂ : Memory.State}
    (hfr₂ : s₂.frontier = s₀.frontier) (hwf₂ : Memory.WellFormed w s₂)
    (hmod : ∀ a, ¬growMod ctx n selLen0 selIdxs0.length a → s.mem a = s₀.mem a)
    (hs2_mod_s : ∀ a, a ∉ footprint n ctx.fhBase → a ≠ ctx.selBufBase + selLen →
      s₂.mem a = s.mem a)
    (hinv₂ : (framed hn hK ctx.fhBase).inv s₂)
    (habs₂ : (framed hn hK ctx.fhBase).abs s₂ =
      Function.update ((framed hn hK ctx.fhBase).abs s) yf none)
    (haux_not_fp : ∀ a, ctx.auxBase ≤ a → a < ctx.auxBase + 5 * n → a ∉ footprint n ctx.fhBase)
    (hsel_ne_aux : ∀ a, ctx.auxBase ≤ a → a < ctx.auxBase + 5 * n → a ≠ ctx.selBufBase + selLen)
    (hfp_buf : ∀ j < selTree.length,
      ctx.selBufBase + selLen0 + selIdxs0.length + j ∉ footprint n ctx.fhBase)
    (hsel_ne_buf : ∀ j < selTree.length,
      ctx.selBufBase + selLen0 + selIdxs0.length + j ≠ ctx.selBufBase + selLen)
    (hsel_lo2 : selLen0 + selIdxs0.length ≤ selLen) (hsel_hi : selLen < selLen0 + n)
    (ht_tr : t ∈ trSet ctx.auxBase n t s.mem)
    (hbound : ∀ v : Fin n, s.mem (ctx.auxBase + v.val) < t.val ∨
      s.mem (ctx.auxBase + v.val) = t.val ∨ s.mem (ctx.auxBase + v.val) = n)
    (htr_new : ∀ v ∈ trSet ctx.auxBase n t s.mem, s₀.mem (ctx.auxBase + v.val) = n)
    (htr_rel : ∀ v : Fin n, s.mem (ctx.auxBase + v.val) = s₀.mem (ctx.auxBase + v.val) ∨
      (s₀.mem (ctx.auxBase + v.val) = n ∧ s.mem (ctx.auxBase + v.val) = t.val))
    (hcut : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s)
    (hsel_len : selLen = selLen0 + (selIdxs0 ++ selTree).length)
    (hsel_card : (selIdxs0 ++ selTree).length + nComp + 1 =
      (visitedSet ctx.auxBase n t.val s₀.mem).card + (trSet ctx.auxBase n t s.mem).card)
    (hnd' : (selIdxs0 ++ (selTree ++ [eIdx])).Nodup)
    (hphase_verts : ∀ idx ∈ selIdxs0,
      es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∧
      es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem)
    (hsel_verts : ∀ idx ∈ selIdxs0 ++ selTree,
      es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem ∧
      es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem)
    (hacyclic' : IsAcyclic (((selIdxs0 ++ (selTree ++ [eIdx])).map fun i => es[i.val]).map
      IndexedEdge.toWeighted))
    (hext' : ∃ F_ext : List (WeightedEdge n ℕ),
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        ((((selIdxs0 ++ (selTree ++ [eIdx])).map fun i => es[i.val]).map
          IndexedEdge.toWeighted) ++ F_ext))
    (hsel_buf : ∀ j (hj : j < selTree.length),
      s.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) = es[selTree[j].val].id)
    (hsel_buf_new : s₂.mem (ctx.selBufBase + selLen) = es[eIdx.val].id)
    (htrY : s.mem (ctx.auxBase + yf.val) < t.val)
    (heIdx_end : (es[eIdx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].v = yf) ∨
      (es[eIdx.val].v ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].u = yf))
    (hsel_tree_verts : ∀ idx ∈ selTree,
      es[idx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[idx.val].v ∈ trSet ctx.auxBase n t s.mem)
    (htr_conn : ∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ y' ∈ trSet ctx.auxBase n t s.mem,
      (edgePartition (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
        IndexedEdge.toWeighted)).rel x' y' = true) :
    FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₀
      (selTree ++ [eIdx]) (trSet ctx.auxBase n t s.mem)
      ⟨0, 0, tl, selLen + 1, s.mem (ctx.auxBase + yf.val)⟩ s₂ := by
  have htr_s2 : ∀ v : Fin n, s₂.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) :=
    fun v => hs2_mod_s _ (haux_not_fp _ (by omega) (by omega))
      (hsel_ne_aux _ (by omega) (by omega))
  have htr_set_s2 : trSet ctx.auxBase n t s₂.mem = trSet ctx.auxBase n t s.mem := by
    ext v; simp only [mem_trSet, htr_s2 v]
  have hy_eq_s0 : s₀.mem (ctx.auxBase + yf.val) = s.mem (ctx.auxBase + yf.val) := by
    rcases htr_rel yf with h | ⟨_, h⟩
    · exact h.symm
    · omega
  have hy_vis_s0 : yf ∈ visitedSet ctx.auxBase n t.val s₀.mem :=
    mem_visitedSet.mpr (hy_eq_s0 ▸ htrY)
  have htl_le := hcut.htl_le
  refine ⟨hfr₂, hwf₂, Or.inl rfl, fun a ha => ?_, by rw [htr_set_s2]; exact ht_tr,
    fun v => by rw [htr_s2 v]; exact hbound v,
    fun v hv => by rw [htr_set_s2] at hv; exact htr_new v hv,
    fun v => by rw [htr_s2 v]; exact htr_rel v,
    hinv₂, htl_le, fun i hi => ?_, fun v hv => ?_,
    (by dsimp only; simp only [hsel_len, List.length_append, List.length_singleton]; omega),
    (by rw [htr_set_s2, ite_eq_left (⟨rfl, htrY⟩ : (0 : ℕ) = 0 ∧ _)]
        simp only [List.length_append, List.length_singleton] at hsel_card ⊢; omega),
    hnd', hphase_verts, fun idx hidx => ?_, hacyclic', hext', ?_, ?_⟩
  · simp only [growMod, not_or] at ha
    rw [hs2_mod_s a ha.1 (fun h => ha.2.2.2 (by rw [h]; exact ⟨by omega, by omega⟩)),
      hmod a (by simp only [growMod, not_or]; exact ha)]
  · dsimp only at hi
    rw [hs2_mod_s _ (haux_not_fp _ (by omega) (by omega)) (hsel_ne_aux _ (by omega) (by omega))]
    exact hcut.htouched_lt i hi
  · rw [habs₂] at hv
    by_cases hvy : v = yf
    · rw [hvy, Function.update_self] at hv; exact absurd hv (by simp)
    · rw [Function.update_of_ne hvy] at hv
      obtain ⟨i, hi, heq⟩ := hcut.htouched_cov v hv
      exact ⟨i, hi, by
        rw [hs2_mod_s _ (haux_not_fp _ (by omega) (by omega))
          (hsel_ne_aux _ (by omega) (by omega)), heq]⟩
  · rw [htr_set_s2]
    rw [← List.append_assoc, List.mem_append, List.mem_singleton] at hidx
    rcases hidx with h0 | rfl
    · exact hsel_verts idx h0
    · rcases heIdx_end with ⟨hu, hev⟩ | ⟨hv, heu⟩
      · exact ⟨Finset.mem_union_right _ hu,
          Finset.mem_union_left _ (by rw [hev]; exact hy_vis_s0)⟩
      · exact ⟨Finset.mem_union_left _ (by rw [heu]; exact hy_vis_s0),
          Finset.mem_union_right _ hv⟩
  · exact ftExtract_sel_buf_eq hsel_len hsel_buf hsel_buf_new
      (fun j hjl => hs2_mod_s _ (hfp_buf j hjl) (hsel_ne_buf j hjl))
  · dsimp only
    rw [ite_eq_right (by decide)]
    refine ⟨htr_set_s2.symm, Or.inr ⟨htrY, List.append_ne_nil_of_right_ne_nil _
      (List.cons_ne_nil _ _), eIdx, by simp, ?_, ?_, yf, ?_⟩⟩
    · intro idx hidx; simp only [List.dropLast_concat] at hidx
      rw [htr_set_s2]; exact hsel_tree_verts idx hidx
    · intro x' hx' y' hy'; simp only [List.dropLast_concat]
      rw [htr_set_s2] at hx' hy'; exact htr_conn x' hx' y' hy'
    · rcases heIdx_end with ⟨hu, hev⟩ | ⟨hv, heu⟩
      · exact ⟨es[eIdx.val].u, by rw [htr_set_s2]; exact hu, hy_eq_s0, Or.inl ⟨rfl, hev⟩⟩
      · exact ⟨es[eIdx.val].v, by rw [htr_set_s2]; exact hv, hy_eq_s0, Or.inr ⟨rfl, heu⟩⟩

private theorem ftExtract_grow_growInv {w n K nComp selLen0 selLen tl : ℕ}
    {hn : Fits w n} {hK : Fits w K} {ctx : FTCtx} {es : List (IndexedEdge n)} {t yf : Fin n}
    {eIdx : Fin es.length} {selIdxs0 selTree : List (Fin es.length)}
    {s₀ s s₃ : Memory.State}
    (hfr₃ : s₃.frontier = s₀.frontier) (hwf₃ : Memory.WellFormed w s₃)
    (hmod : ∀ a, ¬growMod ctx n selLen0 selIdxs0.length a → s.mem a = s₀.mem a)
    (hs3_mod_s : ∀ a, a ∉ footprint n ctx.fhBase → a ≠ ctx.selBufBase + selLen →
      a ≠ ctx.auxBase + yf.val → s₃.mem a = s.mem a)
    (hinv₃ : (framed hn hK ctx.fhBase).inv s₃)
    (hsel_lo2 : selLen0 + selIdxs0.length ≤ selLen) (hsel_hi : selLen < selLen0 + n)
    (hfp_buf : ∀ j < selTree.length,
      ctx.selBufBase + selLen0 + selIdxs0.length + j ∉ footprint n ctx.fhBase)
    (hsel_ne_buf : ∀ j < selTree.length,
      ctx.selBufBase + selLen0 + selIdxs0.length + j ≠ ctx.selBufBase + selLen)
    (hnot_buf_y : ∀ j < selTree.length,
      ctx.selBufBase + selLen0 + selIdxs0.length + j ≠ ctx.auxBase + yf.val)
    (ht_tr : t ∈ trSet ctx.auxBase n t s.mem)
    (hbound : ∀ v : Fin n, s.mem (ctx.auxBase + v.val) < t.val ∨
      s.mem (ctx.auxBase + v.val) = t.val ∨ s.mem (ctx.auxBase + v.val) = n)
    (htr_new : ∀ v ∈ trSet ctx.auxBase n t s.mem, s₀.mem (ctx.auxBase + v.val) = n)
    (htr_rel : ∀ v : Fin n, s.mem (ctx.auxBase + v.val) = s₀.mem (ctx.auxBase + v.val) ∨
      (s₀.mem (ctx.auxBase + v.val) = n ∧ s.mem (ctx.auxBase + v.val) = t.val))
    (hcut : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s)
    (hcut' : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s₃)
    (hsel_len : selLen = selLen0 + (selIdxs0 ++ selTree).length)
    (hsel_card : (selIdxs0 ++ selTree).length + nComp + 1 =
      (visitedSet ctx.auxBase n t.val s₀.mem).card + (trSet ctx.auxBase n t s.mem).card)
    (hnd' : (selIdxs0 ++ (selTree ++ [eIdx])).Nodup)
    (hphase_verts : ∀ idx ∈ selIdxs0,
      es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∧
      es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem)
    (hsel_verts : ∀ idx ∈ selIdxs0 ++ selTree,
      es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem ∧
      es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem)
    (hacyclic' : IsAcyclic (((selIdxs0 ++ (selTree ++ [eIdx])).map fun i => es[i.val]).map
      IndexedEdge.toWeighted))
    (hext' : ∃ F_ext : List (WeightedEdge n ℕ),
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        ((((selIdxs0 ++ (selTree ++ [eIdx])).map fun i => es[i.val]).map
          IndexedEdge.toWeighted) ++ F_ext))
    (hsel_buf : ∀ j (hj : j < selTree.length),
      s.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) = es[selTree[j].val].id)
    (hsel_buf_new : s₃.mem (ctx.selBufBase + selLen) = es[eIdx.val].id)
    (htr_s3_v : ∀ v : Fin n, v ≠ yf → s₃.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val))
    (htr_s3_y : s₃.mem (ctx.auxBase + yf.val) = t.val)
    (htr_set_s3 : trSet ctx.auxBase n t s₃.mem = insert yf (trSet ctx.auxBase n t s.mem))
    (hy_not_tr : yf ∉ trSet ctx.auxBase n t s.mem)
    (hy_is_n : s.mem (ctx.auxBase + yf.val) = n)
    (heIdx_end : (es[eIdx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].v = yf) ∨
      (es[eIdx.val].v ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].u = yf))
    (hsel_tree_verts : ∀ idx ∈ selTree,
      es[idx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[idx.val].v ∈ trSet ctx.auxBase n t s.mem)
    (htr_conn : ∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ y' ∈ trSet ctx.auxBase n t s.mem,
      (edgePartition (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
        IndexedEdge.toWeighted)).rel x' y' = true) :
    FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₀
      (selTree ++ [eIdx]) (trSet ctx.auxBase n t s.mem)
      ⟨1, yf.val, tl, selLen + 1, ctx.n⟩ s₃ := by
  have hy_s0_n : s₀.mem (ctx.auxBase + yf.val) = n := by
    rcases htr_rel yf with h | ⟨h, _⟩
    · exact h.symm.trans hy_is_n
    · exact h
  refine ⟨hfr₃, hwf₃, Or.inr rfl, fun a ha => ?_,
    by rw [htr_set_s3]; exact Finset.mem_insert_of_mem ht_tr,
    fun v => ?_, fun v hv => ?_, fun v => ?_,
    hinv₃, hcut.htl_le, hcut'.htouched_lt, hcut'.htouched_cov,
    (by dsimp only; simp only [hsel_len, List.length_append, List.length_singleton]; omega),
    ?_, hnd', hphase_verts, fun idx hidx => ?_, hacyclic', hext', ?_, ?_⟩
  · simp only [growMod, not_or] at ha
    rw [hs3_mod_s a ha.1 (fun h => ha.2.2.2 (by rw [h]; exact ⟨by omega, by omega⟩))
      (fun h => ha.2.1 (by rw [h]; have := yf.isLt; omega)),
      hmod a (by simp only [growMod, not_or]; exact ha)]
  · by_cases hvy : v = yf
    · rw [hvy]; right; left; exact htr_s3_y
    · rw [htr_s3_v v hvy]; exact hbound v
  · rw [htr_set_s3, Finset.mem_insert] at hv
    rcases hv with rfl | hv'
    · exact hy_s0_n
    · exact htr_new v hv'
  · by_cases hvy : v = yf
    · rw [hvy]; exact Or.inr ⟨hy_s0_n, htr_s3_y⟩
    · rw [htr_s3_v v hvy]; exact htr_rel v
  · rw [htr_set_s3, Finset.card_insert_of_notMem hy_not_tr,
      ite_eq_right (by intro h; exact absurd h.1 Nat.one_ne_zero)]
    simp only [List.length_append, List.length_singleton] at hsel_card ⊢; omega
  · rw [htr_set_s3]
    rw [← List.append_assoc, List.mem_append, List.mem_singleton] at hidx
    rcases hidx with h0 | rfl
    · exact ⟨Finset.mem_union.mpr (by
        rcases Finset.mem_union.mp (hsel_verts idx h0).1 with ha | hb
        · exact Or.inl ha
        · exact Or.inr (Finset.mem_insert_of_mem hb)),
        Finset.mem_union.mpr (by
        rcases Finset.mem_union.mp (hsel_verts idx h0).2 with ha | hb
        · exact Or.inl ha
        · exact Or.inr (Finset.mem_insert_of_mem hb))⟩
    · rcases heIdx_end with ⟨hu, hev⟩ | ⟨hv, heu⟩
      · exact ⟨Finset.mem_union_right _ (Finset.mem_insert_of_mem hu),
          Finset.mem_union_right _ (by rw [hev]; exact Finset.mem_insert_self _ _)⟩
      · exact ⟨Finset.mem_union_right _ (by rw [heu]; exact Finset.mem_insert_self _ _),
          Finset.mem_union_right _ (Finset.mem_insert_of_mem hv)⟩
  · exact ftExtract_sel_buf_eq hsel_len hsel_buf hsel_buf_new
      (fun j hjl => hs3_mod_s _ (hfp_buf j hjl) (hsel_ne_buf j hjl) (hnot_buf_y j hjl))
  · dsimp only
    rw [ite_eq_left rfl]
    refine ⟨hcut', yf, rfl, by rw [htr_set_s3]; exact Finset.mem_insert_self _ _, hy_not_tr,
      htr_set_s3, fun idx hidx => ?_, fun x' hx' y' hy' => ?_⟩
    · rw [List.mem_append, List.mem_singleton] at hidx
      rw [htr_set_s3]
      rcases hidx with htr | rfl
      · exact ⟨Finset.mem_insert_of_mem (hsel_tree_verts idx htr).1,
          Finset.mem_insert_of_mem (hsel_tree_verts idx htr).2⟩
      · rcases heIdx_end with ⟨hu, hev⟩ | ⟨hv, heu⟩
        · exact ⟨Finset.mem_insert_of_mem hu, by rw [hev]; exact Finset.mem_insert_self _ _⟩
        · exact ⟨by rw [heu]; exact Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hv⟩
    · rw [htr_set_s3] at hx' hy'
      have hW_eq : (((selIdxs0 ++ (selTree ++ [eIdx])).map fun i => es[i.val]).map
          IndexedEdge.toWeighted) =
          (((selIdxs0 ++ selTree).map fun i => es[i.val]).map IndexedEdge.toWeighted) ++
            [es[eIdx.val].toWeighted] := by
        rw [← List.append_assoc]
        simp only [List.map_append, List.map_singleton]
      rw [hW_eq]
      exact ftExtract_grow_conn _ _ _ yf htr_conn heIdx_end x' hx' y' hy'

private theorem ftExtractAndAdvance_post_rec {w n mRef t_val tl selLen : ℕ}
    {ctx : FTCtx} {s s₁ s₂ s_fin : Memory.State} {yf : Fin n} {ew : ℕ} {res_fin : FTGrowState}
    (hs_aux_fr : ctx.auxBase + 5 * n ≤ s.frontier) (hfr₁ : s₁.frontier = s.frontier)
    (hs2_fr : s₂.frontier = s₁.frontier)
    (hprog_eq : ftExtractAndAdvance ⟨ctx, t_val, tl, selLen⟩ =
      (extractRawProg ctx.n ctx.fhBase >>= fun opt => match opt with
        | none => pure ⟨0, 0, tl, selLen, ctx.n⟩
        | some p =>
          ftRecordSel ⟨ctx, p.1, selLen⟩ >>= fun _ =>
          Memory.read (ctx.auxBase + p.1) >>= fun trY =>
          if trY < t_val then pure ⟨0, 0, tl, selLen + 1, trY⟩
          else Memory.write (ctx.auxBase + p.1) t_val >>= fun _ =>
            pure ⟨1, p.1, tl, selLen + 1, ctx.n⟩))
    (hv_ex : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (extractRawProg ctx.n ctx.fhBase)))
    (h_opt : (Memory.spec 0).clientResult s (extractRawProg ctx.n ctx.fhBase) = some (yf.val, ew))
    (h_s1 : (Memory.spec 0).clientState s (extractRawProg ctx.n ctx.fhBase) = s₁)
    (hv_rec : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (ftRecordSel ⟨ctx, yf.val, selLen⟩)))
    (hs2_eq_sel : (Memory.spec 0).clientState s₁ (ftRecordSel ⟨ctx, yf.val, selLen⟩) = s₂)
    (hcost_rec : memoryCost (ftRecordSel ⟨ctx, yf.val, selLen⟩) s₁ ≤ 3)
    (hpot_s1 : memoryCost (extractRawProg ctx.n ctx.fhBase) s +
        potential n ((layout n ctx.fhBase).abs s₁) ≤
      potential n ((layout n ctx.fhBase).abs s) + 92 * ((2 * mRef) / n) + 92)
    (hpot_s_fin : potential n ((layout n ctx.fhBase).abs s_fin) =
      potential n ((layout n ctx.fhBase).abs s₁))
    (hbr_valid : (Memory.spec w).ValidHistory s₂
      ((Memory.spec w).clientHistory s₂
        (if s₂.mem (ctx.auxBase + yf.val) < t_val then
           pure (⟨0, 0, tl, selLen + 1, s₂.mem (ctx.auxBase + yf.val)⟩ : FTGrowState)
         else Memory.write (ctx.auxBase + yf.val) t_val >>= fun _ =>
           pure (⟨1, yf.val, tl, selLen + 1, ctx.n⟩ : FTGrowState))))
    (hbr_st : (Memory.spec 0).clientState s₂
      (if s₂.mem (ctx.auxBase + yf.val) < t_val then
         pure (⟨0, 0, tl, selLen + 1, s₂.mem (ctx.auxBase + yf.val)⟩ : FTGrowState)
       else Memory.write (ctx.auxBase + yf.val) t_val >>= fun _ =>
         pure (⟨1, yf.val, tl, selLen + 1, ctx.n⟩ : FTGrowState)) = s_fin)
    (hbr_res : (Memory.spec 0).clientResult s₂
      (if s₂.mem (ctx.auxBase + yf.val) < t_val then
         pure ⟨0, 0, tl, selLen + 1, s₂.mem (ctx.auxBase + yf.val)⟩
       else Memory.write (ctx.auxBase + yf.val) t_val >>= fun _ =>
         pure ⟨1, yf.val, tl, selLen + 1, ctx.n⟩) = res_fin)
    (hbr_cost : memoryCost
      (if s₂.mem (ctx.auxBase + yf.val) < t_val then
         pure (⟨0, 0, tl, selLen + 1, s₂.mem (ctx.auxBase + yf.val)⟩ : FTGrowState)
       else Memory.write (ctx.auxBase + yf.val) t_val >>= fun _ =>
         pure (⟨1, yf.val, tl, selLen + 1, ctx.n⟩ : FTGrowState)) s₂ ≤ 1) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (ftExtractAndAdvance ⟨ctx, t_val, tl, selLen⟩)) ∧
    (Memory.spec 0).clientState s (ftExtractAndAdvance ⟨ctx, t_val, tl, selLen⟩) = s_fin ∧
    (Memory.spec 0).clientResult s (ftExtractAndAdvance ⟨ctx, t_val, tl, selLen⟩) = res_fin ∧
    memoryCost (ftExtractAndAdvance ⟨ctx, t_val, tl, selLen⟩) s +
        potential n ((layout n ctx.fhBase).abs s_fin) ≤
      potential n ((layout n ctx.fhBase).abs s) + 92 * ((2 * mRef) / n) + 97 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprog_eq]
    refine validHistory_bind_step hv_ex ?_
    rw [h_opt, h_s1]; dsimp only
    refine validHistory_bind_step hv_rec ?_
    rw [hs2_eq_sel]
    exact validHistory_read_bind (by rw [hs2_fr, hfr₁]; have := yf.isLt; omega) hbr_valid
  · rw [hprog_eq, StateTransitionSpec.clientState_bind, h_opt, h_s1]
    dsimp only
    rw [StateTransitionSpec.clientState_bind, hs2_eq_sel,
      StateTransitionSpec.clientState_bind, clientState_read, clientResult_read, hbr_st]
  · rw [hprog_eq, StateTransitionSpec.clientResult_bind, h_opt, h_s1]
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, hs2_eq_sel,
      StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read, hbr_res]
  · rw [hprog_eq, memoryCost_bind', h_opt, h_s1]; dsimp only
    rw [memoryCost_bind', hs2_eq_sel, memoryCost_bind', memoryCost_read,
      clientResult_read, clientState_read]
    omega

private theorem ftExtractAndAdvance_spec {w n K mRef nComp selLen0 selLen tl : ℕ}
    {hn : Fits w n} {hK : Fits w K} {ctx : FTCtx} {es : List (IndexedEdge n)} {t : Fin n}
    {selIdxs0 selTree : List (Fin es.length)} {s₀ s : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s) (hwf : Memory.WellFormed w s)
    (hfr : s.frontier = s₀.frontier)
    (hmod : ∀ a, ¬growMod ctx n selLen0 selIdxs0.length a → s.mem a = s₀.mem a)
    (ht_tr : t ∈ trSet ctx.auxBase n t s.mem)
    (hbound : ∀ v : Fin n, s.mem (ctx.auxBase + v.val) < t.val ∨
      s.mem (ctx.auxBase + v.val) = t.val ∨ s.mem (ctx.auxBase + v.val) = n)
    (htr_new : ∀ v ∈ trSet ctx.auxBase n t s.mem, s₀.mem (ctx.auxBase + v.val) = n)
    (htr_rel : ∀ v : Fin n, s.mem (ctx.auxBase + v.val) = s₀.mem (ctx.auxBase + v.val) ∨
      (s₀.mem (ctx.auxBase + v.val) = n ∧ s.mem (ctx.auxBase + v.val) = t.val))
    (hcut : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s)
    (hsel_len : selLen = selLen0 + (selIdxs0 ++ selTree).length)
    (hsel_card : (selIdxs0 ++ selTree).length + nComp + 1 =
      (visitedSet ctx.auxBase n t.val s₀.mem).card + (trSet ctx.auxBase n t s.mem).card)
    (hsel_nd : (selIdxs0 ++ selTree).Nodup)
    (hphase_verts : ∀ idx ∈ selIdxs0,
      es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∧
      es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem)
    (hsel_tree_verts : ∀ idx ∈ selTree,
      es[idx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[idx.val].v ∈ trSet ctx.auxBase n t s.mem)
    (htr_conn : ∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ y' ∈ trSet ctx.auxBase n t s.mem,
      (edgePartition (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
        IndexedEdge.toWeighted)).rel x' y' = true)
    (hacyclic : IsAcyclic (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
      IndexedEdge.toWeighted))
    (hext : ∃ F_ext : List (WeightedEdge n ℕ),
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        ((((selIdxs0 ++ selTree).map fun i => es[i.val]).map IndexedEdge.toWeighted) ++ F_ext))
    (hsel_buf : ∀ j (hj : j < selTree.length),
      s.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) = es[selTree[j].val].id)
    (hsz_pos : 1 ≤ s.mem (ctx.fhBase + 9 * n + 4))
    (hsz_le : s.mem (ctx.fhBase + 9 * n + 4) ≤ ctx.thresh) :
    let prog := ftExtractAndAdvance ⟨ctx, t.val, tl, selLen⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftExtractAndAdvanceSafe w ⟨ctx, t.val, tl, selLen⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s + potential n ((layout n ctx.fhBase).abs s') ≤
      potential n ((layout n ctx.fhBase).abs s) + 92 * ((2 * mRef) / n) + 97 ∧
    ∃ selTree' scanned',
      FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₀ selTree' scanned' res s' ∧
      (∀ v : Fin n, s'.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) ∨
        (res.go = 1 ∧ v.val = res.x ∧ s.mem (ctx.auxBase + v.val) = n ∧
          s'.mem (ctx.auxBase + v.val) = t.val)) ∧
      res.touchedLen = tl ∧ (res.go = 1 → s.mem (ctx.auxBase + res.x) = n) := by
  have hcn := hs.cn; have hcm := hs.cm
  have hdisj_vt : Disjoint (visitedSet ctx.auxBase n t.val s₀.mem) (trSet ctx.auxBase n t s.mem) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 => by
      rw [mem_visitedSet] at hv1
      have := htr_new v hv2
      omega
  have hcard_le_n : (visitedSet ctx.auxBase n t.val s₀.mem).card +
      (trSet ctx.auxBase n t s.mem).card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj_vt]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hsel_len_lt_n : (selIdxs0 ++ selTree).length < n := by omega
  have hlen_lt_n : selIdxs0.length + selTree.length < n := by
    simpa only [List.length_append] using hsel_len_lt_n
  have hsel_lo2 : selLen0 + selIdxs0.length ≤ selLen := by
    rw [hsel_len, List.length_append]; omega
  have hsel_hi : selLen < selLen0 + n := by rw [hsel_len]; omega
  have hsel_buf_fr : ctx.selBufBase + selLen < s.frontier := by have := hs.selFr; omega
  have hnot_fp_sel : ctx.selBufBase + selLen ∉ footprint n ctx.fhBase := by
    simp only [footprint, Finset.mem_Ico]; rcases hs.selDisjFh with hd | hd <;> omega
  have hfp_buf : ∀ j < selTree.length,
      ctx.selBufBase + selLen0 + selIdxs0.length + j ∉ footprint n ctx.fhBase := fun j hjl => by
    simp only [footprint, Finset.mem_Ico]; rcases hs.selDisjFh with hd | hd <;> omega
  have hsel_ne_aux : ∀ a, ctx.auxBase ≤ a → a < ctx.auxBase + 5 * n →
      a ≠ ctx.selBufBase + selLen := fun a h1 h2 heq => by
    rcases hs.selDisjAux with hd | hd <;> omega
  have hsel_ne_buf : ∀ j < selTree.length,
      ctx.selBufBase + selLen0 + selIdxs0.length + j ≠ ctx.selBufBase + selLen :=
    fun j hj heq => by rw [hsel_len, List.length_append] at heq; omega
  have haux_not_fp : ∀ a, ctx.auxBase ≤ a → a < ctx.auxBase + 5 * n →
      a ∉ footprint n ctx.fhBase := fun a h1 h2 => by
    simp only [footprint, Finset.mem_Ico]; have := hs.fhLtAux; omega
  have hsel_verts : ∀ idx ∈ selIdxs0 ++ selTree,
      es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem ∧
      es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem := by
    intro idx hidx
    rw [List.mem_append] at hidx
    rcases hidx with h0 | htr
    · exact ⟨Finset.mem_union_left _ (hphase_verts idx h0).1,
        Finset.mem_union_left _ (hphase_verts idx h0).2⟩
    · exact ⟨Finset.mem_union_right _ (hsel_tree_verts idx htr).1,
        Finset.mem_union_right _ (hsel_tree_verts idx htr).2⟩
  have hex := extractRawProg_spec_n hcn hwf hn hK hcut.hinv
  dsimp only at hex
  generalize h_opt : (Memory.spec 0).clientResult s (extractRawProg ctx.n ctx.fhBase) = opt at hex
  generalize h_s1 : (Memory.spec 0).clientState s (extractRawProg ctx.n ctx.fhBase) = s₁ at hex
  rcases hex with ⟨hv_ex, hinv₁, hfr₁, hwf₁, hmod₁, hcard_ex, hnone_ex, hsome_ex, hcost_ex⟩
  cases hopt_cases : opt with
  | none =>
    exfalso
    obtain ⟨habs_emp, _⟩ := hnone_ex hopt_cases
    have : (IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s)).card = 0 := by
      rw [habs_emp]; simp [IndexedMinPQ.dom, IndexedMinPQ.empty]
    omega
  | some p =>
    obtain ⟨hy, hk_s, hmin_ex, habs₁⟩ := hsome_ex p.1 p.2 hopt_cases
    obtain ⟨yf, hy_val⟩ : ∃ yf : Fin n, p.1 = yf.val := ⟨⟨p.1, hy⟩, rfl⟩
    rw [show (⟨p.1, hy⟩ : Fin n) = yf from Fin.ext hy_val] at hk_s habs₁
    obtain ⟨hy_not_t, eIdx, heIdx_best, heIdx_wt, heIdx_end⟩ := hcut.hheap_cut yf p.2 hk_s
    have hy_not_tr : yf ∉ trSet ctx.auxBase n t s.mem := fun hmem =>
      hy_not_t (mem_trSet.mp hmem)
    have hs1_aux : ∀ a, (ctx.auxBase ≤ a ∧ a < ctx.auxBase + 5 * n) → s₁.mem a = s.mem a :=
      fun a ha => hmod₁ a (haux_not_fp a ha.1 ha.2)
    have hs1_edge : ∀ a, (ctx.edgeBase ≤ a ∧ a < ctx.edgeBase + 4 * es.length) →
        s₁.mem a = s.mem a := fun a ha =>
      hmod₁ a (by simp only [footprint, Finset.mem_Ico]; have := hs.edgeLtFh; omega)
    have hs1_best : s₁.mem (ctx.auxBase + n + yf.val) = eIdx.val := by
      rw [hs1_aux _ (by omega), heIdx_best]
    have horig_eq : s₁.mem (ctx.edgeBase + 4 * eIdx.val + 3) = es[eIdx.val].id := by
      rw [hs1_edge _ (by have := eIdx.isLt; omega)]
      exact (hs.hin eIdx.val eIdx.isLt).2.2.2
    have hrec_safe : ftRecordSelSafe w ⟨ctx, yf.val, selLen⟩ s₁ := by
      unfold ftRecordSelSafe; dsimp only
      refine ⟨hs.fit16, by rw [hcn]; exact hs.fitAux.of_le (by omega),
        by rw [hcm]; exact hs.fitEdge, by rw [hcn]; exact yf.isLt,
        by rw [hcn, hfr₁]; have := hs.auxFr; omega,
        by rw [hcm, hfr₁]; exact hs.edgeFr,
        by rw [hfr₁]; exact hsel_buf_fr,
        by rw [show ctx.auxBase + ctx.n + yf.val = ctx.auxBase + n + yf.val by rw [hcn],
            hs1_best, hcm]; exact eIdx.isLt⟩
    have hnot_fp_y : ctx.auxBase + yf.val ∉ footprint n ctx.fhBase :=
      haux_not_fp _ (by omega) (by omega)
    have hs1_trY : s₁.mem (ctx.auxBase + yf.val) = s.mem (ctx.auxBase + yf.val) :=
      hs1_aux _ (by omega)
    let s₂ : Memory.State := ⟨Function.update s₁.mem (ctx.selBufBase + selLen) es[eIdx.val].id,
      s₁.frontier⟩
    have hrec_prog : ftRecordSel ⟨ctx, yf.val, selLen⟩ =
        (Memory.read (ctx.auxBase + ctx.n + yf.val) >>= fun eI =>
         Memory.read (ctx.edgeBase + 4 * eI + 3) >>= fun orig =>
         Memory.write (ctx.selBufBase + selLen) orig) := rfl
    have hs2_eq_sel :
        (Memory.spec 0).clientState s₁ (ftRecordSel ⟨ctx, yf.val, selLen⟩) = s₂ := by
      rw [hrec_prog, StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        clientState_write]
      rw [show ctx.auxBase + ctx.n + yf.val = ctx.auxBase + n + yf.val by rw [hcn],
        hs1_best, horig_eq]
    have hcost_rec : memoryCost (ftRecordSel ⟨ctx, yf.val, selLen⟩) s₁ ≤ 3 := by
      rw [hrec_prog, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_write]
    have hv_rec : (Memory.spec w).ValidHistory s₁
        ((Memory.spec w).clientHistory s₁ (ftRecordSel ⟨ctx, yf.val, selLen⟩)) := by
      rw [hrec_prog]
      refine validHistory_read_bind (by rw [hfr₁]; have := hs.auxFr; omega) ?_
      refine validHistory_read_bind (by
        rw [show ctx.auxBase + ctx.n + yf.val = ctx.auxBase + n + yf.val by rw [hcn],
          hs1_best, hfr₁]; exact Nat.le_trans (by omega) hs.edgeFr) ?_
      refine validHistory_write_bind (by rw [hfr₁]; exact hsel_buf_fr) ?_
        (validHistory_pure w _ _)
      rw [show ctx.auxBase + ctx.n + yf.val = ctx.auxBase + n + yf.val by rw [hcn],
        hs1_best, horig_eq, ← horig_eq]
      exact hwf₁.mem_fits _
    have hn_c : Fits w ctx.n := by rw [hcn]; exact hs.hn
    have hinv_s_c : (framed hn_c hK ctx.fhBase).inv s :=
      framed_inv_congr hcn.symm hn hn_c hK hcut.hinv
    have hsafe : ftExtractAndAdvanceSafe w ⟨ctx, t.val, tl, selLen⟩ s := by
      unfold ftExtractAndAdvanceSafe; dsimp only
      refine ⟨hs.fit16, by rw [hcn]; exact hs.fitAux.of_le (by omega),
        hs.fitSel.of_le (by omega), hn_c, by rw [hcn]; exact t.isLt,
        ⟨by rw [hcn]; exact hs.fitFh, hinv_s_c.1, K, hK, hinv_s_c.2⟩,
        fun y0 k0 hk0 => ?_⟩
      rw [h_opt, hopt_cases] at hk0
      have hp0 := Prod.ext_iff.mp (Option.some.inj hk0)
      dsimp only at hp0
      rw [h_s1, ← hp0.1, hy_val]
      refine ⟨hrec_safe, ?_⟩
      rw [hfr₁]; have := hs.auxFr; omega
    obtain ⟨hnd', hacyclic', hext'⟩ := ftExtract_cutStep ht_tr hy_not_tr htr_new heIdx_wt
      heIdx_end (fun z kz hkz => by rw [← hy_val]; exact hmin_ex z kz hkz)
      hcut hsel_nd hphase_verts hsel_tree_verts htr_conn hacyclic hext
    have hlog_le : Nat.log 2 (s.mem (ctx.fhBase + 9 * n + 4)) ≤ (2 * mRef) / n := by
      have h1 : s.mem (ctx.fhBase + 9 * n + 4) ≤ 2 ^ ((2 * mRef) / n) := hsz_le.trans hs.threshLe
      exact (Nat.log_mono_right h1).trans_eq (Nat.log_pow (by decide : 1 < 2) _)
    have hpot_s1 : memoryCost (extractRawProg ctx.n ctx.fhBase) s +
        potential n ((layout n ctx.fhBase).abs s₁) ≤
        potential n ((layout n ctx.fhBase).abs s) + 92 * ((2 * mRef) / n) + 92 := by
      have hmul : 92 * (Nat.log 2 (s.mem (ctx.fhBase + 9 * n + 4)) + 1) ≤
          92 * ((2 * mRef) / n) + 92 := by
        have := Nat.mul_le_mul_left 92 (Nat.add_le_add_right hlog_le 1)
        omega
      omega
    have hprog_eq : ftExtractAndAdvance ⟨ctx, t.val, tl, selLen⟩ =
        (extractRawProg ctx.n ctx.fhBase >>= fun opt => match opt with
          | none => pure ⟨0, 0, tl, selLen, ctx.n⟩
          | some p =>
            ftRecordSel ⟨ctx, p.1, selLen⟩ >>= fun _ =>
            Memory.read (ctx.auxBase + p.1) >>= fun trY =>
            if trY < t.val then pure ⟨0, 0, tl, selLen + 1, trY⟩
            else Memory.write (ctx.auxBase + p.1) t.val >>= fun _ =>
              pure ⟨1, p.1, tl, selLen + 1, ctx.n⟩) := rfl
    have hy_s2 : s₂.mem (ctx.auxBase + yf.val) = s.mem (ctx.auxBase + yf.val) := by
      dsimp only [s₂]
      rw [Function.update_of_ne (hsel_ne_aux _ (by omega) (by omega)), hs1_trY]
    have hfp_s2 : ∀ a ∈ footprint n ctx.fhBase, s₂.mem a = s₁.mem a := fun a ha => by
      dsimp only [s₂]; rw [Function.update_of_ne (fun h => hnot_fp_sel (by rw [← h]; exact ha))]
    have hwf₂ : Memory.WellFormed w s₂ := by
      have hfit_id : Fits w es[eIdx.val].id := by
        rw [← horig_eq]; exact hwf₁.mem_fits _
      simpa only [s₂] using wellFormed_update hwf₁ hfit_id
    obtain ⟨hinv₂, habs₂, hpot₂⟩ := framed_preserved hinv₁ hfp_s2 (by dsimp only [s₂]; exact le_rfl)
      (by dsimp only [s₂]; exact hwf₁.frontier_fits)
    have hs2_mod_s : ∀ a, a ∉ footprint n ctx.fhBase → a ≠ ctx.selBufBase + selLen →
        s₂.mem a = s.mem a := fun a hfp hne => by
      dsimp only [s₂]; rw [Function.update_of_ne hne, hmod₁ a hfp]
    by_cases htrY : s.mem (ctx.auxBase + yf.val) < t.val
    · have hbr1 := ftExtractAndAdvance_post_rec (s_fin := s₂)
        (res_fin := ⟨0, 0, tl, selLen + 1, s.mem (ctx.auxBase + yf.val)⟩)
        hs.auxFr hfr₁ (by dsimp only [s₂]) hprog_eq hv_ex
        (by rw [h_opt, hopt_cases, ← Prod.eta p, hy_val]) h_s1 hv_rec hs2_eq_sel hcost_rec
        hpot_s1 hpot₂
        (by rw [ite_eq_left (by rw [hy_s2]; exact htrY)]; exact validHistory_pure w _ _)
        (by rw [ite_eq_left (by rw [hy_s2]; exact htrY), StateTransitionSpec.clientState_pure])
        (by rw [ite_eq_left (by rw [hy_s2]; exact htrY), StateTransitionSpec.clientResult_pure,
              hy_s2])
        (by rw [ite_eq_left (by rw [hy_s2]; exact htrY), memoryCost_pure]; omega)
      rcases hbr1 with ⟨hv_all, hst_all, hres_all, hcost_all⟩
      have hgrow_inv := ftExtract_merge_growInv (by dsimp only [s₂]; exact hfr₁.trans hfr)
        hwf₂ hmod hs2_mod_s hinv₂ (habs₂.trans habs₁) haux_not_fp hsel_ne_aux hfp_buf hsel_ne_buf
        hsel_lo2 hsel_hi ht_tr hbound htr_new htr_rel hcut hsel_len hsel_card hnd' hphase_verts
        hsel_verts hacyclic' hext' hsel_buf (by dsimp only [s₂]; rw [Function.update_self]) htrY
        heIdx_end hsel_tree_verts htr_conn
      refine ⟨hsafe, hv_all, by rw [hst_all]; exact hcost_all, selTree ++ [eIdx],
        trSet ctx.auxBase n t s.mem, ?_, fun v => ?_,
        by rw [hres_all]; exact ⟨rfl, fun h => absurd h Nat.zero_ne_one⟩⟩
      · rw [hst_all, hres_all]; exact hgrow_inv
      · rw [hst_all]
        left
        exact hs2_mod_s _ (haux_not_fp _ (by omega) (by omega))
          (hsel_ne_aux _ (by omega) (by omega))
    · have hy_is_n : s.mem (ctx.auxBase + yf.val) = n := by
        rcases hbound yf with h1 | h2 | h3
        · exact absurd h1 htrY
        · exact absurd (mem_trSet.mpr h2) hy_not_tr
        · exact h3
      let s₃ : Memory.State := ⟨Function.update s₂.mem (ctx.auxBase + yf.val) t.val, s₂.frontier⟩
      have hs3_fr : s₃.frontier = s.frontier := by dsimp only [s₃, s₂]; exact hfr₁
      have hfit_t : Fits w t.val := hn.of_le t.isLt.le
      have hwf₃ : Memory.WellFormed w s₃ := by
        simpa only [s₃] using wellFormed_update hwf₂ hfit_t
      have hfp_s3 : ∀ a ∈ footprint n ctx.fhBase, s₃.mem a = s₂.mem a := fun a ha => by
        dsimp only [s₃]; rw [Function.update_of_ne (fun h => hnot_fp_y (by rw [← h]; exact ha))]
      obtain ⟨hinv₃, habs₃, hpot₃⟩ := framed_preserved hinv₂ hfp_s3
        (by dsimp only [s₃]; exact le_rfl) (by dsimp only [s₃]; exact hwf₂.frontier_fits)
      have hbr2 := ftExtractAndAdvance_post_rec (s_fin := s₃)
        (res_fin := ⟨1, yf.val, tl, selLen + 1, ctx.n⟩)
        hs.auxFr hfr₁ (by dsimp only [s₂]) hprog_eq hv_ex
        (by rw [h_opt, hopt_cases, ← Prod.eta p, hy_val]) h_s1 hv_rec hs2_eq_sel hcost_rec
        hpot_s1 (hpot₃.trans hpot₂)
        (by rw [ite_eq_right (by rw [hy_s2]; exact htrY)]
            exact validHistory_write_bind (by dsimp only [s₂]; rw [hfr₁]; have := hs.auxFr; omega)
              hfit_t (validHistory_pure w _ _))
        (by rw [ite_eq_right (by rw [hy_s2]; exact htrY), StateTransitionSpec.clientState_bind,
              clientState_write, StateTransitionSpec.clientState_pure])
        (by rw [ite_eq_right (by rw [hy_s2]; exact htrY), StateTransitionSpec.clientResult_bind,
              StateTransitionSpec.clientResult_pure])
        (by rw [ite_eq_right (by rw [hy_s2]; exact htrY), memoryCost_bind', memoryCost_write,
              memoryCost_pure])
      rcases hbr2 with ⟨hv_all, hst_all, hres_all, hcost_all⟩
      have hs3_mod_s : ∀ a, a ∉ footprint n ctx.fhBase → a ≠ ctx.selBufBase + selLen →
          a ≠ ctx.auxBase + yf.val → s₃.mem a = s.mem a := fun a hfp hne1 hne2 => by
        dsimp only [s₃, s₂]
        rw [Function.update_of_ne hne2, Function.update_of_ne hne1, hmod₁ a hfp]
      have htr_s3_v : ∀ v : Fin n, v ≠ yf →
          s₃.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) := fun v hv =>
        hs3_mod_s _ (haux_not_fp _ (by omega) (by omega))
          (hsel_ne_aux _ (by omega) (by omega))
          (by intro h; apply hv; exact Fin.ext (by omega))
      have htr_s3_y : s₃.mem (ctx.auxBase + yf.val) = t.val := by
        dsimp only [s₃]; rw [Function.update_self]
      have htr_set_s3 : trSet ctx.auxBase n t s₃.mem = insert yf (trSet ctx.auxBase n t s.mem) := by
        ext v; simp only [mem_trSet, Finset.mem_insert]
        by_cases hvy : v = yf
        · rw [hvy]; simp [htr_s3_y]
        · simp [htr_s3_v v hvy, hvy]
      have htl_le := hcut.htl_le
      have hcut' := ftExtract_grow_cutInv hinv₃ (habs₃.trans (habs₂.trans habs₁)) hcut htr_s3_v
        htr_set_s3
        (fun i hi => hs3_mod_s _ (haux_not_fp _ (by omega) (by omega))
          (hsel_ne_aux _ (by omega) (by omega)) (by have := yf.isLt; omega))
        (fun v hv => hs3_mod_s _ (haux_not_fp _ (by omega) (by omega))
          (hsel_ne_aux _ (by omega) (by omega)) (by have := v.isLt; omega))
      have hnot_buf_y : ∀ j < selTree.length,
          ctx.selBufBase + selLen0 + selIdxs0.length + j ≠ ctx.auxBase + yf.val := fun j hjl => by
        have := yf.isLt; rcases hs.selDisjAux with hd | hd <;> omega
      have hsel_buf_new3 : s₃.mem (ctx.selBufBase + selLen) = es[eIdx.val].id := by
        dsimp only [s₃, s₂]
        rw [Function.update_of_ne (hsel_ne_aux _ (by omega) (by omega)).symm,
          Function.update_self]
      have hgrow_inv := ftExtract_grow_growInv (hs3_fr.trans hfr) hwf₃ hmod hs3_mod_s hinv₃
        hsel_lo2 hsel_hi hfp_buf hsel_ne_buf hnot_buf_y ht_tr hbound htr_new htr_rel hcut hcut'
        hsel_len hsel_card hnd' hphase_verts hsel_verts hacyclic' hext' hsel_buf hsel_buf_new3
        htr_s3_v htr_s3_y htr_set_s3 hy_not_tr hy_is_n heIdx_end hsel_tree_verts htr_conn
      refine ⟨hsafe, hv_all, by rw [hst_all]; exact hcost_all, selTree ++ [eIdx],
        trSet ctx.auxBase n t s.mem, ?_, fun v => ?_,
        by rw [hres_all]; exact ⟨rfl, fun _ => hy_is_n⟩⟩
      · rw [hst_all, hres_all]; exact hgrow_inv
      · rw [hst_all, hres_all]
        by_cases hvy : v = yf
        · rw [hvy]; right; refine ⟨rfl, rfl, hy_is_n, htr_s3_y⟩
        · left; exact htr_s3_v v hvy

/-! ## Inner Loop Step, Tree Finish, and `ftRunTree_spec` -/

private theorem ftGrowStep_spec {w n K mRef nComp selLen0 : ℕ}
    {hn : Fits w n} {hK : Fits w K} {ctx : FTCtx} {es : List (IndexedEdge n)} {t : Fin n}
    {selIdxs0 selTree : List (Fin es.length)} {scanned : Finset (Fin n)}
    {st : FTGrowState} {s₀ s : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s) (hwf : Memory.WellFormed w s)
    (hfr : s.frontier = s₀.frontier) (hgo1 : st.go = 1)
    (hgrow : FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₀ selTree scanned st s) :
    let prog := ftGrowStep (⟨ctx, t.val⟩, st)
    let st' := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftGrowStepSafe w (⟨ctx, t.val⟩, st) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, ¬growMod ctx n selLen0 selIdxs0.length a → s'.mem a = s.mem a) ∧
    (∀ v : Fin n, s'.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) ∨
      (s.mem (ctx.auxBase + v.val) = n ∧ s'.mem (ctx.auxBase + v.val) = t.val)) ∧
    (∀ v ∈ trSet ctx.auxBase n t s.mem, v ∈ trSet ctx.auxBase n t s'.mem) ∧
    (∃ selTree' scanned',
      FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₀ selTree' scanned' st' s') ∧
    memoryCost prog s + growPot ctx n mRef t st' s' ≤ growPot ctx n mRef t st s ∧
    growRank ctx n t st' s' < growRank ctx n t st s := by
  have hcn := hs.cn; have hcm := hs.cm
  have hgo := hgrow.hgo
  rw [ite_eq_left hgo1] at hgo
  rcases hgo with ⟨hcut, xFin, hx_eq, hx_mem, _, htr_eq_ins, hsel_tree_verts, htr_conn⟩
  have hx_tr : s.mem (ctx.auxBase + xFin.val) = t.val := mem_trSet.mp hx_mem
  have hsv := ftScanVertex_spec hs hwf hgrow.ht_tr hx_mem hcut
  dsimp only at hsv
  rw [← hx_eq] at hsv
  generalize h_tl : (Memory.spec 0).clientResult s
    (ftScanVertex ⟨ctx, t.val, st.x, st.touchedLen⟩) = tl at hsv
  generalize h_s1 : (Memory.spec 0).clientState s
    (ftScanVertex ⟨ctx, t.val, st.x, st.touchedLen⟩) = s₁ at hsv
  rcases hsv with ⟨hsafe_sv, hv_sv, hfr₁, hwf₁, hmod₁, hcut₁, hc_sv⟩
  have hcut₁_tr : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s₁ := by
    rwa [← htr_eq_ins] at hcut₁
  have htr_s1 : ∀ v : Fin n, s₁.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) :=
    fun v => hmod₁ _ (by
      simp only [scanMod, footprint, Finset.mem_Ico]; have := hs.fhLtAux; have := v.isLt; omega)
  have hoff_s1 : ∀ v : Fin n,
      s₁.mem (ctx.offBase + v.val) = s.mem (ctx.offBase + v.val) ∧
      s₁.mem (ctx.offBase + v.val + 1) = s.mem (ctx.offBase + v.val + 1) := fun v =>
    ⟨hmod₁ _ (by
        simp only [scanMod, footprint, Finset.mem_Ico]
        have := hs.offLtFh; have := hs.fhLtAux; have := v.isLt; omega),
      hmod₁ _ (by
        simp only [scanMod, footprint, Finset.mem_Ico]
        have := hs.offLtFh; have := hs.fhLtAux; have := v.isLt; omega)⟩
  have htrSet_s1 : trSet ctx.auxBase n t s₁.mem = trSet ctx.auxBase n t s.mem := by
    ext z; simp only [mem_trSet, htr_s1 z]
  have hcut₁_s1 : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s₁.mem) tl s₁ := by
    rwa [htrSet_s1]
  have hmod_s1 : ∀ a, ¬growMod ctx n selLen0 selIdxs0.length a → s₁.mem a = s₀.mem a :=
    fun a ha => (hmod₁ a (fun hm => ha (scanMod_imp_growMod hm))).trans (hgrow.hmod a ha)
  have hs₁ : FTStatic w n K mRef selLen0 ctx es s₁ :=
    hs.of_step (by rw [hfr₁]) fun a ha => hmod₁ a (by
      simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
      have := hs.edgeLtFh; have := hs.offLtFh; have := hs.adjLtFh; have := hs.fhLtAux
      rcases ha with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
  have hprog_eq : ftGrowStep (⟨ctx, t.val⟩, st) =
      (ftScanVertex ⟨ctx, t.val, st.x, st.touchedLen⟩ >>= fun tl =>
       Memory.read (ctx.fhBase + 9 * ctx.n + 4) >>= fun sz =>
       if sz = 0 then pure ⟨0, 0, tl, st.selLen, ctx.n⟩
       else if ctx.thresh < sz then pure ⟨0, 0, tl, st.selLen, ctx.n⟩
       else ftExtractAndAdvance ⟨ctx, t.val, tl, st.selLen⟩) := rfl
  let sz := s₁.mem (ctx.fhBase + 9 * ctx.n + 4)
  have hsz_n : s₁.mem (ctx.fhBase + 9 * n + 4) = sz := by dsimp only [sz]; rw [hcn]
  have hdom_sz : (IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s₁)).card = sz := by
    rw [← hsz_n]
    exact (extractRawProg_spec_n hcn hwf₁ hn hK hcut₁_s1.hinv).2.2.2.2.2.1
  have hsel_buf_s1 : ∀ j (hj : j < selTree.length),
      s₁.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) = es[selTree[j].val].id := by
    intro j hj
    have hac := hgrow.hacyclic.length_le_pred (Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt)
    simp only [List.length_map, List.length_append] at hac
    rw [hmod₁ _ (by
      simp only [scanMod, footprint, Finset.mem_Ico]
      rcases hs.selDisjFh with hd | hd <;> rcases hs.selDisjAux with hd2 | hd2 <;> omega)]
    exact hgrow.hsel_buf j hj
  by_cases hstop : sz = 0 ∨ ctx.thresh < sz
  · have hite_stop :
        (if sz = 0 then (pure ⟨0, 0, tl, st.selLen, ctx.n⟩ : Memory.Prog FTGrowState)
         else if ctx.thresh < sz then pure ⟨0, 0, tl, st.selLen, ctx.n⟩
         else ftExtractAndAdvance ⟨ctx, t.val, tl, st.selLen⟩) =
        pure ⟨0, 0, tl, st.selLen, ctx.n⟩ := by
      rcases hstop with h0 | hhi
      · exact ite_eq_left h0
      · by_cases h0 : sz = 0
        · exact ite_eq_left h0
        · rw [ite_eq_right h0, ite_eq_left hhi]
    have hsafe : ftGrowStepSafe w (⟨ctx, t.val⟩, st) s := by
      refine ⟨hs.fit16, by rw [hcn]; exact hs.fitFh, by rw [hcn]; exact hs.hn, hsafe_sv, ?_⟩
      rw [h_tl, h_s1]
      refine ⟨by dsimp only; rw [hfr₁, hcn]; have := hs.auxFr; have := hs.fhLtAux; omega,
        fun h0 hhi => ?_⟩
      exfalso; rcases hstop with h | h <;> [exact h0 h; exact hhi h]
    have hv_all : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (ftGrowStep (⟨ctx, t.val⟩, st))) := by
      rw [hprog_eq]
      refine validHistory_bind_step hv_sv ?_
      rw [h_tl, h_s1]
      refine validHistory_read_bind (by
        rw [hfr₁, hcn]; have := hs.auxFr; have := hs.fhLtAux; omega) ?_
      rw [hite_stop]; exact validHistory_pure w _ _
    have hst_all : (Memory.spec 0).clientState s (ftGrowStep (⟨ctx, t.val⟩, st)) = s₁ := by
      rw [hprog_eq, StateTransitionSpec.clientState_bind, h_tl, h_s1,
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        hite_stop, StateTransitionSpec.clientState_pure]
    have hres_all : (Memory.spec 0).clientResult s (ftGrowStep (⟨ctx, t.val⟩, st)) =
        ⟨0, 0, tl, st.selLen, ctx.n⟩ := by
      rw [hprog_eq, StateTransitionSpec.clientResult_bind, h_tl, h_s1,
        StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        hite_stop, StateTransitionSpec.clientResult_pure]
    have hc_step : memoryCost (ftGrowStep (⟨ctx, t.val⟩, st)) s ≤
        memoryCost (ftScanVertex ⟨ctx, t.val, st.x, st.touchedLen⟩) s + 1 := by
      rw [hprog_eq, memoryCost_bind', h_tl, h_s1, memoryCost_bind', memoryCost_read,
        clientResult_read, clientState_read, hite_stop, memoryCost_pure]
    have hclosed_or_dom :
        (∀ e ∈ es, (e.u ∈ trSet ctx.auxBase n t s₁.mem ↔ e.v ∈ trSet ctx.auxBase n t s₁.mem)) ∨
        ∃ Z : Finset (Fin n), ctx.thresh + 1 ≤ Z.card ∧
          ∀ z ∈ Z, z ∉ trSet ctx.auxBase n t s₁.mem ∧
            ∃ e ∈ es, (e.u ∈ trSet ctx.auxBase n t s₁.mem ∧ e.v = z) ∨
              (e.v ∈ trSet ctx.auxBase n t s₁.mem ∧ e.u = z) := by
      rcases hstop with h0 | hhi
      · left
        have hdom0 : IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s₁) = ∅ :=
          Finset.card_eq_zero.mp (hdom_sz.trans h0)
        intro e he
        constructor
        · intro hu
          by_contra hnv
          obtain ⟨kz, hkz, _⟩ := (hcut₁_s1.hscanned_cov e.u hu e he).1 ⟨rfl, hnv⟩
          have hmem : e.v ∈ IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s₁) :=
            IndexedMinPQ.mem_dom_iff.mpr ⟨kz, hkz⟩
          rw [hdom0] at hmem; exact Finset.notMem_empty _ hmem
        · intro hv
          by_contra hnu
          obtain ⟨kz, hkz, _⟩ := (hcut₁_s1.hscanned_cov e.v hv e he).2 ⟨rfl, hnu⟩
          have hmem : e.u ∈ IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s₁) :=
            IndexedMinPQ.mem_dom_iff.mpr ⟨kz, hkz⟩
          rw [hdom0] at hmem; exact Finset.notMem_empty _ hmem
      · right
        refine ⟨IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s₁), hdom_sz ▸ hhi, fun z hz => ?_⟩
        obtain ⟨kz, hkz⟩ := IndexedMinPQ.mem_dom_iff.mp hz
        obtain ⟨hne, eIdx, _, _, hend⟩ := hcut₁_s1.hheap_cut z kz hkz
        exact ⟨fun hmem => hne (mem_trSet.mp hmem), es[eIdx.val], List.getElem_mem eIdx.isLt, hend⟩
    have hgrow_end : FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₀ selTree
        (trSet ctx.auxBase n t s₁.mem) ⟨0, 0, tl, st.selLen, n⟩ s₁ := by
      have hcard_old := hgrow.hsel_card
      rw [ite_eq_right (by intro ⟨h0, _⟩; exact absurd h0 (by rw [hgo1]; decide))] at hcard_old
      refine ⟨hfr₁.trans hfr, hwf₁, Or.inl rfl, hmod_s1,
        by rw [htrSet_s1]; exact hgrow.ht_tr,
        fun v => by rw [htr_s1 v]; exact hgrow.hbound v,
        fun v hv => by rw [htrSet_s1] at hv; exact hgrow.htr_new v hv,
        fun v => by rw [htr_s1 v]; exact hgrow.htr_rel v,
        hcut₁_s1.hinv, hcut₁_s1.htl_le, hcut₁_s1.htouched_lt, hcut₁_s1.htouched_cov,
        hgrow.hsel_len,
        by dsimp only
           rw [htrSet_s1, ite_eq_right (by intro ⟨_, hlt⟩; have := t.isLt; omega)]
           exact hcard_old,
        hgrow.hsel_nd, hgrow.hphase_verts,
        fun idx hidx => by rw [htrSet_s1]; exact hgrow.hsel_verts idx hidx,
        hgrow.hacyclic, hgrow.hext, hsel_buf_s1, ?_⟩
      dsimp only
      rw [ite_eq_right (by decide)]
      exact ⟨rfl, Or.inl ⟨rfl, fun idx hidx => by rw [htrSet_s1]; exact hsel_tree_verts idx hidx,
        fun x' hx' y' hy' => by rw [htrSet_s1] at hx' hy'; exact htr_conn x' hx' y' hy',
        hclosed_or_dom⟩⟩
    have hc_pot : memoryCost (ftGrowStep (⟨ctx, t.val⟩, st)) s +
        growPot ctx n mRef t ⟨0, 0, tl, st.selLen, ctx.n⟩ s₁ ≤ growPot ctx n mRef t st s := by
      have hsum := grow_vertexSum_step_le (n := n) (mRef := mRef) (ctx := ctx) (t := t)
        (x := xFin) (st := st) (st' := ⟨0, 0, tl, st.selLen, ctx.n⟩)
        hoff_s1 ⟨hx_tr, hgo1, hx_eq.symm⟩ ⟨by rw [htr_s1]; exact hx_tr, by simp⟩
        fun v _ hv => ⟨by rw [htr_s1 v]; exact hv, by simp⟩
      have hvp := vertexPot_eq ctx n mRef xFin s.mem
      rw [hx_eq] at hc_sv hc_step
      rw [hvp] at hsum
      simp only [growPot_eq]
      rw [show ({ go := 0, x := 0, touchedLen := tl, selLen := st.selLen, jn := ctx.n } :
          FTGrowState).go = 0 from rfl,
        show ({ go := 0, x := 0, touchedLen := tl, selLen := st.selLen, jn := ctx.n } :
          FTGrowState).x = 0 from rfl] at *
      omega
    have hrank_lt : growRank ctx n t ⟨0, 0, tl, st.selLen, ctx.n⟩ s₁ < growRank ctx n t st s := by
      simp only [growRank_eq, ite_true]
      rw [ite_eq_right (by rw [hgo1]; decide)]
      have hc_le : (trSet ctx.auxBase n t s.mem).card ≤ n :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      omega
    refine ⟨hsafe, hv_all, hst_all ▸ hfr₁, hst_all ▸ hwf₁,
      fun a ha => by rw [hst_all]; exact hmod₁ a (fun hm => ha (scanMod_imp_growMod hm)),
      fun v => by rw [hst_all]; exact Or.inl (htr_s1 v),
      fun v hv => by rw [hst_all, htrSet_s1]; exact hv,
      ⟨selTree, trSet ctx.auxBase n t s₁.mem,
        by rw [hst_all, hres_all, hcn]; exact hgrow_end⟩,
      by rw [hst_all, hres_all]; exact hc_pot, by rw [hst_all, hres_all]; exact hrank_lt⟩
  · have hsz_pos : 1 ≤ s₁.mem (ctx.fhBase + 9 * n + 4) := by
      rw [hsz_n]; exact Nat.pos_of_ne_zero (fun h => hstop (Or.inl h))
    have hsz_le : s₁.mem (ctx.fhBase + 9 * n + 4) ≤ ctx.thresh := by
      rw [hsz_n]; exact Nat.not_lt.mp (fun h => hstop (Or.inr h))
    have hEA := ftExtractAndAdvance_spec hs₁ hwf₁ (hfr₁.trans hfr) hmod_s1
      (by rw [htrSet_s1]; exact hgrow.ht_tr)
      (fun v => by rw [htr_s1 v]; exact hgrow.hbound v)
      (fun v hv => by rw [htrSet_s1] at hv; exact hgrow.htr_new v hv)
      (fun v => by rw [htr_s1 v]; exact hgrow.htr_rel v)
      hcut₁_s1 hgrow.hsel_len
      (by
        have hc := hgrow.hsel_card
        rw [ite_eq_right (by intro ⟨h0, _⟩; exact absurd h0 (by rw [hgo1]; decide))] at hc
        rw [htrSet_s1]; exact hc)
      hgrow.hsel_nd hgrow.hphase_verts
      (fun idx hidx => by rw [htrSet_s1]; exact hsel_tree_verts idx hidx)
      (fun x' hx' y' hy' => by rw [htrSet_s1] at hx' hy'; exact htr_conn x' hx' y' hy')
      hgrow.hacyclic hgrow.hext hsel_buf_s1 hsz_pos hsz_le
    dsimp only at hEA
    generalize h_st' : (Memory.spec 0).clientResult s₁
      (ftExtractAndAdvance ⟨ctx, t.val, tl, st.selLen⟩) = st' at hEA
    generalize h_s2 : (Memory.spec 0).clientState s₁
      (ftExtractAndAdvance ⟨ctx, t.val, tl, st.selLen⟩) = s₂ at hEA
    rcases hEA with ⟨hsafe_ea, hv_ea, hc_ea, selTree', scanned', hgrow_ea, htr_ea,
      htl_ea, hst'_n⟩
    have hsafe : ftGrowStepSafe w (⟨ctx, t.val⟩, st) s := by
      refine ⟨hs.fit16, by rw [hcn]; exact hs.fitFh, by rw [hcn]; exact hs.hn, hsafe_sv, ?_⟩
      rw [h_tl, h_s1]
      exact ⟨by dsimp only; rw [hfr₁, hcn]; have := hs.auxFr; have := hs.fhLtAux; omega,
        fun _ _ => hsafe_ea⟩
    have hv_all : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (ftGrowStep (⟨ctx, t.val⟩, st))) := by
      rw [hprog_eq]
      refine validHistory_bind_step hv_sv ?_
      rw [h_tl, h_s1]
      refine validHistory_read_bind (by
        rw [hfr₁, hcn]; have := hs.auxFr; have := hs.fhLtAux; omega) ?_
      rw [ite_eq_right (by rw [hsz_n] at hsz_pos; omega),
        ite_eq_right (by rw [hsz_n] at hsz_le; exact Nat.not_lt.mpr hsz_le)]
      exact hv_ea
    have hst_all : (Memory.spec 0).clientState s (ftGrowStep (⟨ctx, t.val⟩, st)) = s₂ := by
      rw [hprog_eq, StateTransitionSpec.clientState_bind, h_tl, h_s1,
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        ite_eq_right (by rw [hsz_n] at hsz_pos; omega),
        ite_eq_right (by rw [hsz_n] at hsz_le; exact Nat.not_lt.mpr hsz_le), h_s2]
    have hres_all : (Memory.spec 0).clientResult s (ftGrowStep (⟨ctx, t.val⟩, st)) = st' := by
      rw [hprog_eq, StateTransitionSpec.clientResult_bind, h_tl, h_s1,
        StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        ite_eq_right (by rw [hsz_n] at hsz_pos; omega),
        ite_eq_right (by rw [hsz_n] at hsz_le; exact Nat.not_lt.mpr hsz_le), h_st']
    have hc_step : memoryCost (ftGrowStep (⟨ctx, t.val⟩, st)) s ≤
        memoryCost (ftScanVertex ⟨ctx, t.val, st.x, st.touchedLen⟩) s + 1 +
          memoryCost (ftExtractAndAdvance ⟨ctx, t.val, tl, st.selLen⟩) s₁ := by
      rw [hprog_eq, memoryCost_bind', h_tl, h_s1, memoryCost_bind', memoryCost_read,
        clientResult_read, clientState_read,
        ite_eq_right (by rw [hsz_n] at hsz_pos; omega),
        ite_eq_right (by rw [hsz_n] at hsz_le; exact Nat.not_lt.mpr hsz_le)]
      omega
    have hmod_off_s2 : ∀ a, (ctx.offBase ≤ a ∧ a < ctx.offBase + n + 1) →
        s₂.mem a = s.mem a := fun a ha => by
      have hng : ¬growMod ctx n selLen0 selIdxs0.length a := by
        simp only [growMod, footprint, Finset.mem_Ico, not_or, not_and]
        have := hs.offLtFh; have := hs.fhLtAux; rcases hs.selDisjOff with hd | hd <;> omega
      exact (hgrow_ea.hmod a hng).trans (hgrow.hmod a hng).symm
    have hoff_s2 : ∀ v : Fin n,
        s₂.mem (ctx.offBase + v.val) = s.mem (ctx.offBase + v.val) ∧
        s₂.mem (ctx.offBase + v.val + 1) = s.mem (ctx.offBase + v.val + 1) := fun v =>
      ⟨hmod_off_s2 _ (by omega), hmod_off_s2 _ (by omega)⟩
    have htr_ea' : ∀ v : Fin n,
        s₂.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) ∨
        (s.mem (ctx.auxBase + v.val) = n ∧ s₂.mem (ctx.auxBase + v.val) = t.val) := fun v => by
      rcases htr_ea v with heq | ⟨_, _, hn_s1, ht_s2⟩
      · exact Or.inl (heq.trans (htr_s1 v))
      · exact Or.inr ⟨(htr_s1 v).symm.trans hn_s1, ht_s2⟩
    have hx_after : s₂.mem (ctx.auxBase + xFin.val) = t.val ∧ ¬(st'.go = 1 ∧ xFin.val = st'.x) := by
      have hx_s2 : s₂.mem (ctx.auxBase + xFin.val) = t.val := by
        rcases htr_ea' xFin with heq | ⟨hn_x, _⟩
        · exact heq.trans hx_tr
        · exfalso; have := t.isLt; omega
      refine ⟨hx_s2, fun ⟨hgo1', hxeq⟩ => ?_⟩
      have hn_x := hst'_n hgo1'
      rw [← hxeq, htr_s1 xFin, hx_tr] at hn_x
      have := t.isLt; omega
    have hother_after : ∀ v : Fin n, v ≠ xFin → s.mem (ctx.auxBase + v.val) = t.val →
        s₂.mem (ctx.auxBase + v.val) = t.val ∧ ¬(st'.go = 1 ∧ v.val = st'.x) := by
      intro v _ hv_t
      have hv_s2 : s₂.mem (ctx.auxBase + v.val) = t.val := by
        rcases htr_ea' v with heq | ⟨hn_v, _⟩
        · exact heq.trans hv_t
        · exfalso; have := t.isLt; omega
      refine ⟨hv_s2, fun ⟨hgo1', hveq⟩ => ?_⟩
      have hn_v := hst'_n hgo1'
      rw [← hveq, htr_s1 v, hv_t] at hn_v
      have := t.isLt; omega
    have hc_pot : memoryCost (ftGrowStep (⟨ctx, t.val⟩, st)) s +
        growPot ctx n mRef t st' s₂ ≤ growPot ctx n mRef t st s := by
      have hsum := grow_vertexSum_step_le (n := n) (mRef := mRef) (ctx := ctx) (t := t)
        (x := xFin) (st := st) (st' := st') hoff_s2 ⟨hx_tr, hgo1, hx_eq.symm⟩ hx_after
        hother_after
      have hvp := vertexPot_eq ctx n mRef xFin s.mem
      have hlog_le : Nat.log 2 (s₁.mem (ctx.fhBase + 9 * n + 4)) ≤ (2 * mRef) / n := by
        have h1 : s₁.mem (ctx.fhBase + 9 * n + 4) ≤ 2 ^ ((2 * mRef) / n) :=
          hsz_le.trans hs.threshLe
        exact (Nat.log_mono_right h1).trans_eq (Nat.log_pow (by decide : 1 < 2) _)
      have hc_ea' : memoryCost (ftExtractAndAdvance ⟨ctx, t.val, tl, st.selLen⟩) s₁ +
          potential n ((layout n ctx.fhBase).abs s₂) ≤
          potential n ((layout n ctx.fhBase).abs s₁) + 92 * ((2 * mRef) / n) + 97 := hc_ea
      have htl_le := hcut₁_s1.htl_le
      rw [hx_eq] at hc_sv hc_step
      simp only [growPot_eq]
      rw [htl_ea]
      rw [hvp] at hsum
      omega
    have hrank_lt : growRank ctx n t st' s₂ < growRank ctx n t st s := by
      have hst_go0 : st.go ≠ 0 := by rw [hgo1]; decide
      simp only [growRank_eq]
      rw [ite_eq_right hst_go0]
      rcases hgrow_ea.hgo_bin with h0' | h1'
      · rw [ite_eq_left h0']
        have hc_le : (trSet ctx.auxBase n t s.mem).card ≤ n :=
          (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
        omega
      · rw [ite_eq_right (by rw [h1']; decide)]
        have hgo' := hgrow_ea.hgo
        rw [ite_eq_left h1'] at hgo'
        obtain ⟨_, x', hx'_eq, hx'_tr2, _, _⟩ := hgo'
        have hx'_nmem : x' ∉ trSet ctx.auxBase n t s.mem := by
          have hn_x := hst'_n h1'
          rw [hx'_eq, htr_s1 x'] at hn_x
          rw [mem_trSet, hn_x]; exact t.isLt.ne'
        have hsub : trSet ctx.auxBase n t s.mem ⊂ trSet ctx.auxBase n t s₂.mem := by
          refine ⟨fun v hv => ?_, fun hsup => hx'_nmem (hsup hx'_tr2)⟩
          rw [mem_trSet] at hv ⊢
          rcases htr_ea' v with heq | ⟨hn_v, _⟩
          · exact heq.trans hv
          · exfalso; have := t.isLt; omega
        have hlt_c := Finset.card_lt_card hsub
        have hc_le2 : (trSet ctx.auxBase n t s₂.mem).card ≤ n :=
          (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
        omega
    refine ⟨hsafe, hv_all, hst_all ▸ (hgrow_ea.hfr.trans hfr.symm), hst_all ▸ hgrow_ea.hwf,
      fun a ha => by rw [hst_all]; exact (hgrow_ea.hmod a ha).trans (hgrow.hmod a ha).symm,
      fun v => by rw [hst_all]; exact htr_ea' v,
      fun v hv => by
        rw [hst_all, mem_trSet]
        rw [mem_trSet] at hv
        rcases htr_ea' v with heq | ⟨hn_v, _⟩
        · exact heq.trans hv
        · exfalso; have := t.isLt; omega,
      ⟨selTree', scanned', by rw [hst_all, hres_all]; exact hgrow_ea⟩,
      by rw [hst_all, hres_all]; exact hc_pot, by rw [hst_all, hres_all]; exact hrank_lt⟩

private theorem ftFinishTree_spec {w : ℕ} {ctx : FTCtx} {t nComp selLen jn : ℕ}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hfit_aux : Fits w (ctx.auxBase + 3 * ctx.n)) (hfit_nc : Fits w (nComp + 1))
    (ht : t < ctx.n) (haux_fr : ctx.auxBase + 3 * ctx.n ≤ s.frontier) :
    let prog := ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftFinishTreeSafe w ⟨ctx, t, nComp, selLen, jn⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, a ≠ ctx.auxBase + 2 * ctx.n + t → s'.mem a = s.mem a) ∧
    res = (if jn < t then nComp else nComp + 1, selLen) ∧
    s'.mem (ctx.auxBase + 2 * ctx.n + t) =
      (if jn < t then s.mem (ctx.auxBase + 2 * ctx.n + jn) else nComp) ∧
    memoryCost prog s ≤ 2 := by
  have hsafe : ftFinishTreeSafe w ⟨ctx, t, nComp, selLen, jn⟩ s :=
    ⟨h16, hfit_aux, hfit_nc, ht, haux_fr⟩
  by_cases hjn : jn < t
  · have hprog : ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩ =
        (Memory.read (ctx.auxBase + 2 * ctx.n + jn) >>= fun supJn =>
          Memory.write (ctx.auxBase + 2 * ctx.n + t) supJn >>= fun _ =>
          pure (nComp, selLen)) := by
      simp [ftFinishTree, hjn, ← PFunctor.FreeM.bind_eq_bind]
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩)) := by
      rw [hprog]
      refine validHistory_read_bind (by omega) ?_
      exact validHistory_write_bind (by omega) (hwf.mem_fits _) (validHistory_pure w _ _)
    have hst : (Memory.spec 0).clientState s (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩) =
        ⟨Function.update s.mem (ctx.auxBase + 2 * ctx.n + t)
          (s.mem (ctx.auxBase + 2 * ctx.n + jn)), s.frontier⟩ := by
      rw [hprog, StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        StateTransitionSpec.clientState_bind, clientState_write,
        StateTransitionSpec.clientState_pure]
    have hres : (Memory.spec 0).clientResult s (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩) =
        (nComp, selLen) := by
      rw [hprog, StateTransitionSpec.clientResult_bind, clientState_read, clientResult_read,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    have hc : memoryCost (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩) s ≤ 2 := by
      rw [hprog, memoryCost_bind', memoryCost_read, memoryCost_bind', memoryCost_write,
        memoryCost_pure]
    refine ⟨hsafe, hv, by rw [hst], wellFormed_clientState hwf hv, fun a ha => ?_, ?_, ?_, hc⟩
    · rw [hst]; dsimp only; exact Function.update_of_ne ha _ _
    · rw [hres, ite_eq_left hjn]
    · rw [hst]; dsimp only; rw [Function.update_self, ite_eq_left hjn]
  · have hprog : ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩ =
        (Memory.write (ctx.auxBase + 2 * ctx.n + t) nComp >>= fun _ =>
          pure (nComp + 1, selLen)) := by
      simp [ftFinishTree, hjn]
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩)) := by
      rw [hprog]
      exact validHistory_write_bind (by omega) (hfit_nc.of_le (by omega)) (validHistory_pure w _ _)
    have hst : (Memory.spec 0).clientState s (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩) =
        ⟨Function.update s.mem (ctx.auxBase + 2 * ctx.n + t) nComp, s.frontier⟩ := by
      rw [hprog, StateTransitionSpec.clientState_bind, clientState_write,
        StateTransitionSpec.clientState_pure]
    have hres : (Memory.spec 0).clientResult s (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩) =
        (nComp + 1, selLen) := by
      rw [hprog, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    have hc : memoryCost (ftFinishTree ⟨ctx, t, nComp, selLen, jn⟩) s ≤ 2 := by
      rw [hprog, memoryCost_bind', memoryCost_write, memoryCost_pure]; omega
    refine ⟨hsafe, hv, by rw [hst], wellFormed_clientState hwf hv, fun a ha => ?_, ?_, ?_, hc⟩
    · rw [hst]; dsimp only; exact Function.update_of_ne ha _ _
    · rw [hres, ite_eq_right hjn]
    · rw [hst]; dsimp only; rw [Function.update_self, ite_eq_right hjn]

private structure FTRunTreeBridge {n : ℕ} (ctx : FTCtx) (t : Fin n) (nComp : ℕ)
    (res : FTGrowState) (res_fin : ℕ × ℕ) (s s₁ s₂ s₃ s₄ : Memory.State) : Prop where
  hres_fin_eq : res_fin = (if res.jn < t.val then nComp else nComp + 1, res.selLen)
  hsup_fin_eq : s₄.mem (ctx.auxBase + 2 * n + t.val) =
    if res.jn < t.val then s₃.mem (ctx.auxBase + 2 * n + res.jn) else nComp
  htr_s4 : ∀ v : Fin n, s₄.mem (ctx.auxBase + v.val) = s₂.mem (ctx.auxBase + v.val)
  hsup_old_s4 : ∀ k < n, k ≠ t.val →
    s₄.mem (ctx.auxBase + 2 * n + k) = s.mem (ctx.auxBase + 2 * n + k)
  hsup_s3_s : ∀ k < n, s₃.mem (ctx.auxBase + 2 * n + k) = s.mem (ctx.auxBase + 2 * n + k)
  hV_sub_s2 : ∀ v ∈ visitedSet ctx.auxBase n t.val s.mem,
    s₂.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val)
  hV'_eq : visitedSet ctx.auxBase n (t.val + 1) s₄.mem =
    visitedSet ctx.auxBase n t.val s.mem ∪ trSet ctx.auxBase n t s₂.mem
  hdisj_VA : Disjoint (visitedSet ctx.auxBase n t.val s.mem) (trSet ctx.auxBase n t s₂.mem)
  hV_vis_s1 : visitedSet ctx.auxBase n t.val s₁.mem = visitedSet ctx.auxBase n t.val s.mem
  htr_s1_V : ∀ v ∈ visitedSet ctx.auxBase n t.val s.mem,
    s₁.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val)

private theorem ftRunTree_sup_t_le {n : ℕ} {ctx : FTCtx} {t : Fin n} {nComp : ℕ}
    {res : FTGrowState} {res_fin : ℕ × ℕ} {s s₁ s₂ s₃ s₄ : Memory.State}
    (hb : FTRunTreeBridge ctx t nComp res res_fin s s₁ s₂ s₃ s₄)
    {v : Fin n} (hv : v ∈ visitedSet ctx.auxBase n t.val s.mem) :
    s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + v.val)) =
      s.mem (ctx.auxBase + 2 * n + s.mem (ctx.auxBase + v.val)) := by
  have hv_lt : s.mem (ctx.auxBase + v.val) < t.val := mem_visitedSet.mp hv
  rw [hb.htr_s4 v, hb.hV_sub_s2 v hv]
  exact hb.hsup_old_s4 _ (hv_lt.trans t.isLt) hv_lt.ne

private theorem ftRunTree_sup_A_eq {n : ℕ} {ctx : FTCtx} {t : Fin n} {nComp : ℕ}
    {res : FTGrowState} {res_fin : ℕ × ℕ} {s s₁ s₂ s₃ s₄ : Memory.State}
    (hb : FTRunTreeBridge ctx t nComp res res_fin s s₁ s₂ s₃ s₄)
    {u : Fin n} (huA : u ∈ trSet ctx.auxBase n t s₂.mem) :
    s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + u.val)) =
      (if res.jn < t.val then s.mem (ctx.auxBase + 2 * n + res.jn) else nComp) := by
  rw [hb.htr_s4 u, mem_trSet.mp huA, hb.hsup_fin_eq]
  by_cases hjn : res.jn < t.val
  · rw [ite_eq_left hjn, ite_eq_left hjn, hb.hsup_s3_s res.jn (hjn.trans t.isLt)]
  · rw [ite_eq_right hjn, ite_eq_right hjn]

private theorem ftRunTree_phase_rel {w n K : ℕ} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {t : Fin n} {nComp selLen0 : ℕ} {selIdxs0 selTree_bw : List (Fin es.length)}
    {scanned_bw : Finset (Fin n)} {res : FTGrowState} {res_fin : ℕ × ℕ}
    {s s₁ s₂ s₃ s₄ : Memory.State} {hn : Fits w n} {hK : Fits w K}
    (hphase : FTPhaseInv ctx es t.val nComp selLen0 (selLen0 + selIdxs0.length) selIdxs0 s.mem)
    (hgrow₂ : FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₁ selTree_bw scanned_bw res s₂)
    (hstop_bw : res.go ≠ 1) (hb : FTRunTreeBridge ctx t nComp res res_fin s s₁ s₂ s₃ s₄) :
    ∀ x ∈ visitedSet ctx.auxBase n (t.val + 1) s₄.mem,
    ∀ y ∈ visitedSet ctx.auxBase n (t.val + 1) s₄.mem,
      s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + x.val)) =
          s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + y.val)) ↔
      (edgePartition (((selIdxs0 ++ selTree_bw).map fun i => es[i.val]).map
        IndexedEdge.toWeighted)).rel x y = true := by
  let A := trSet ctx.auxBase n t s₂.mem
  let V := visitedSet ctx.auxBase n t.val s.mem
  let F := (selIdxs0.map fun i => es[i.val]).map IndexedEdge.toWeighted
  have hF_V : ∀ e ∈ F, e.u ∈ V ∧ e.v ∈ V := fun e he => by
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp he0
    exact hphase.hsel_verts idx hidx
  have hsup_t_le {v : Fin n} (hv : v ∈ V) := ftRunTree_sup_t_le hb hv
  have hgo := hgrow₂.hgo
  rw [ite_eq_right hstop_bw] at hgo
  rcases hgo with ⟨_, hjn_n | hjn_lt⟩
  · rcases hjn_n with ⟨_, htree_A, hA_conn, _⟩
    let G := (selTree_bw.map fun i => es[i.val]).map IndexedEdge.toWeighted
    have hFG_eq : (((selIdxs0 ++ selTree_bw).map fun i => es[i.val]).map
        IndexedEdge.toWeighted) = F ++ G := by
      simp only [F, G, List.map_append]
    have hG_A : ∀ e ∈ G, e.u ∈ A ∧ e.v ∈ A := by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp he0
      exact htree_A idx hidx
    intro x hx y hy
    rw [hb.hV'_eq, Finset.mem_union] at hx hy
    rcases hx with hxV | hxA <;> rcases hy with hyV | hyA
    · rw [hsup_t_le hxV, hsup_t_le hyV, hphase.hcomp_rel x hxV y hyV, hFG_eq]
      exact ⟨fun h => (edgePartition_mono_subperm (List.sublist_append_left F G).subperm h),
        fun h => (eqvGen_append_disjoint_left F G V A hb.hdisj_VA hF_V hG_A hxV h).2⟩
    · have hy_tr : s₂.mem (ctx.auxBase + y.val) = t.val := mem_trSet.mp hyA
      have hy_sup : s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + y.val)) = nComp := by
        rw [hb.htr_s4 y, hy_tr, hb.hsup_fin_eq, ite_eq_right (by omega)]
      have hx_sup_lt : s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + x.val)) < nComp := by
        rw [hsup_t_le hxV]; exact hphase.hsup_range x hxV
      rw [hFG_eq]
      refine ⟨fun heq => by omega, fun hrel => ?_⟩
      exact absurd (eqvGen_append_disjoint_left F G V A hb.hdisj_VA hF_V hG_A hxV hrel).1
        (Finset.disjoint_right.mp hb.hdisj_VA hyA)
    · have hx_tr : s₂.mem (ctx.auxBase + x.val) = t.val := mem_trSet.mp hxA
      have hx_sup : s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + x.val)) = nComp := by
        rw [hb.htr_s4 x, hx_tr, hb.hsup_fin_eq, ite_eq_right (by omega)]
      have hy_sup_lt : s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + y.val)) < nComp := by
        rw [hsup_t_le hyV]; exact hphase.hsup_range y hyV
      rw [hFG_eq]
      refine ⟨fun heq => by omega, fun hrel => ?_⟩
      exact absurd (eqvGen_append_disjoint_left F G V A hb.hdisj_VA hF_V hG_A hyV
        ((edgePartition (F ++ G)).symm hrel)).1 (Finset.disjoint_right.mp hb.hdisj_VA hxA)
    · rw [hb.htr_s4 x, hb.htr_s4 y, mem_trSet.mp hxA, mem_trSet.mp hyA]
      simp only [true_iff]
      exact hA_conn x hxA y hyA
  · rcases hjn_lt with ⟨hjn, hne, eIdx, hlast, htree₀_A, hA_conn₀, y0, u0, hu0A, hy0_jn, heIdx⟩
    obtain ⟨selTree₀, rfl⟩ : ∃ selTree₀, selTree_bw = selTree₀ ++ [eIdx] :=
      ⟨selTree_bw.dropLast, by
        have hg := (List.getLast_eq_iff_getLast?_eq_some hne).mpr hlast
        simpa only [hg] using (List.dropLast_append_getLast hne).symm⟩
    simp only [List.dropLast_concat] at htree₀_A hA_conn₀
    let G₀ := (selTree₀.map fun i => es[i.val]).map IndexedEdge.toWeighted
    have hG₀_A : ∀ e ∈ G₀, e.u ∈ A ∧ e.v ∈ A := by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp he0
      exact htree₀_A idx hidx
    have hW_eq : (((selIdxs0 ++ (selTree₀ ++ [eIdx])).map fun i => es[i.val]).map
        IndexedEdge.toWeighted) = (F ++ G₀) ++ [es[eIdx.val].toWeighted] := by
      rw [← List.append_assoc]; simp only [F, G₀, List.map_append, List.map_singleton]
    have hy0_V : y0 ∈ V := by
      have : y0 ∈ visitedSet ctx.auxBase n t.val s₁.mem := mem_visitedSet.mpr (hy0_jn ▸ hjn)
      rwa [hb.hV_vis_s1] at this
    have hbad_u : ∀ v ∈ V, (edgePartition (F ++ G₀)).rel v u0 = false := fun v hv =>
      Bool.eq_false_iff.mpr fun hr => Finset.disjoint_right.mp hb.hdisj_VA hu0A
        (eqvGen_append_disjoint_left F G₀ V A hb.hdisj_VA hF_V hG₀_A hv hr).1
    have hbad_ub : ∀ v ∈ V, (edgePartition (F ++ G₀)).rel u0 v = false := fun v hv =>
      Bool.eq_false_iff.mpr fun hr => Finset.disjoint_right.mp hb.hdisj_VA hu0A
        (eqvGen_append_disjoint_left F G₀ V A hb.hdisj_VA hF_V hG₀_A hv
          ((edgePartition _).symm hr)).1
    have hrel_V : ∀ a ∈ V, ∀ b ∈ V,
        (edgePartition ((F ++ G₀) ++ [es[eIdx.val].toWeighted])).rel a b = true ↔
        (edgePartition F).rel a b = true := by
      intro a ha b hbV
      rw [edgePartition_append_single_rel]
      dsimp only [IndexedEdge.toWeighted]
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact (eqvGen_append_disjoint_left F G₀ V A hb.hdisj_VA hF_V hG₀_A ha h).2
        · exfalso
          rcases heIdx with ⟨hu_e, _⟩ | ⟨hv_e, _⟩
          · rw [hu_e, hbad_u a ha] at h1; exact absurd h1 (by decide)
          · rw [hv_e, hbad_ub b hbV] at h2; exact absurd h2 (by decide)
        · exfalso
          rcases heIdx with ⟨hu_e, _⟩ | ⟨hv_e, _⟩
          · rw [hu_e, hbad_ub b hbV] at h2; exact absurd h2 (by decide)
          · rw [hv_e, hbad_u a ha] at h1; exact absurd h1 (by decide)
      · intro hF
        exact Or.inl (edgePartition_mono_subperm (List.sublist_append_left F G₀).subperm hF)
    have hrel_AV : ∀ x ∈ A, ∀ b ∈ V,
        (edgePartition ((F ++ G₀) ++ [es[eIdx.val].toWeighted])).rel x b = true ↔
        (edgePartition F).rel y0 b = true := by
      intro x hxA b hbV
      rw [edgePartition_append_single_rel]
      dsimp only [IndexedEdge.toWeighted]
      have hbad_xb : (edgePartition (F ++ G₀)).rel x b = false :=
        Bool.eq_false_iff.mpr fun hr => Finset.disjoint_right.mp hb.hdisj_VA hxA
          (eqvGen_append_disjoint_left F G₀ V A hb.hdisj_VA hF_V hG₀_A hbV
            ((edgePartition _).symm hr)).1
      have hbad_xy : (edgePartition (F ++ G₀)).rel x y0 = false :=
        Bool.eq_false_iff.mpr fun hr => Finset.disjoint_right.mp hb.hdisj_VA hxA
          (eqvGen_append_disjoint_left F G₀ V A hb.hdisj_VA hF_V hG₀_A hy0_V
            ((edgePartition _).symm hr)).1
      have hxu : (edgePartition (F ++ G₀)).rel x u0 = true := by
        simpa only [F, G₀, List.map_append] using hA_conn₀ x hxA u0 hu0A
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · rw [hbad_xb] at h; exact absurd h (by decide)
        · rcases heIdx with ⟨hu_e, hv_e⟩ | ⟨hv_e, hu_e⟩
          · rw [hv_e] at h2
            exact (eqvGen_append_disjoint_left F G₀ V A hb.hdisj_VA hF_V hG₀_A hy0_V h2).2
          · rw [hu_e, hbad_xy] at h1; exact absurd h1 (by decide)
        · rcases heIdx with ⟨hu_e, hv_e⟩ | ⟨hv_e, hu_e⟩
          · rw [hv_e, hbad_xy] at h1; exact absurd h1 (by decide)
          · rw [hu_e] at h2
            exact (eqvGen_append_disjoint_left F G₀ V A hb.hdisj_VA hF_V hG₀_A hy0_V h2).2
      · intro hF
        have hyb : (edgePartition (F ++ G₀)).rel y0 b = true :=
          edgePartition_mono_subperm (List.sublist_append_left F G₀).subperm hF
        rcases heIdx with ⟨hu_e, hv_e⟩ | ⟨hv_e, hu_e⟩
        · rw [hu_e, hv_e]; exact Or.inr (Or.inl ⟨hxu, hyb⟩)
        · rw [hv_e, hu_e]; exact Or.inr (Or.inr ⟨hxu, hyb⟩)
    have hsup_A_y0 : ∀ x ∈ A,
        s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + x.val)) =
        s.mem (ctx.auxBase + 2 * n + s.mem (ctx.auxBase + y0.val)) := by
      intro x hxA
      rw [hb.htr_s4 x, mem_trSet.mp hxA, hb.hsup_fin_eq, ite_eq_left hjn,
        hb.hsup_s3_s res.jn (hjn.trans t.isLt), ← hb.htr_s1_V y0 hy0_V, hy0_jn]
    intro x hx y hy
    rw [hb.hV'_eq, Finset.mem_union] at hx hy
    rcases hx with hxV | hxA <;> rcases hy with hyV | hyA
    · rw [hsup_t_le hxV, hsup_t_le hyV, hphase.hcomp_rel x hxV y hyV, hW_eq]
      exact (hrel_V x hxV y hyV).symm
    · rw [hsup_t_le hxV, hsup_A_y0 y hyA, hphase.hcomp_rel x hxV y0 hy0_V, hW_eq]
      have hr1 := (hrel_AV y hyA x hxV).trans
        ⟨fun h => (edgePartition F).symm h, fun h => (edgePartition F).symm h⟩
      exact ⟨fun h => (edgePartition _).symm (hr1.mpr h),
        fun h => hr1.mp ((edgePartition _).symm h)⟩
    · rw [hsup_A_y0 x hxA, hsup_t_le hyV, hphase.hcomp_rel y0 hy0_V y hyV, hW_eq]
      exact (hrel_AV x hxA y hyV).symm
    · rw [hb.htr_s4 x, hb.htr_s4 y, mem_trSet.mp hxA, mem_trSet.mp hyA, hW_eq]
      simp only [true_iff]
      exact edgePartition_mono_subperm (List.sublist_append_left (F ++ G₀) _).subperm
        (by simpa only [F, G₀, List.map_append] using hA_conn₀ x hxA y hyA)

private theorem ftRunTree_phase_deg {w n K : ℕ} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {t : Fin n} {nComp selLen0 : ℕ} {selIdxs0 selTree_bw : List (Fin es.length)}
    {scanned_bw : Finset (Fin n)} {res : FTGrowState} {res_fin : ℕ × ℕ}
    {s s₁ s₂ s₃ s₄ : Memory.State} {hn : Fits w n} {hK : Fits w K}
    (hphase : FTPhaseInv ctx es t.val nComp selLen0 (selLen0 + selIdxs0.length) selIdxs0 s.mem)
    (hgrow₂ : FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₁ selTree_bw scanned_bw res s₂)
    (hstop_bw : res.go ≠ 1) (hb : FTRunTreeBridge ctx t nComp res res_fin s s₁ s₂ s₃ s₄) :
    ∀ c : Fin res_fin.1,
      (∃ v ∈ visitedSet ctx.auxBase n (t.val + 1) s₄.mem,
        s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + v.val)) = c.val) ∧
      ((∀ e ∈ es,
          (e.u ∈ visitedSet ctx.auxBase n (t.val + 1) s₄.mem ∧
            s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + e.u.val)) = c.val) ↔
          (e.v ∈ visitedSet ctx.auxBase n (t.val + 1) s₄.mem ∧
            s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + e.v.val)) = c.val)) ∨
        ∃ A Z : Finset (Fin n),
          A ⊆ visitedSet ctx.auxBase n (t.val + 1) s₄.mem ∧
          (∀ u ∈ A, s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + u.val)) = c.val) ∧
          ctx.thresh + 1 ≤ Z.card ∧
          ∀ z ∈ Z, z ∉ A ∧
            ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z)) := by
  let A := trSet ctx.auxBase n t s₂.mem
  let V := visitedSet ctx.auxBase n t.val s.mem
  let V' := visitedSet ctx.auxBase n (t.val + 1) s₄.mem
  have hsup_t_le {v : Fin n} (hv : v ∈ V) := ftRunTree_sup_t_le hb hv
  have hsup_A_eq {u : Fin n} (hu : u ∈ A) := ftRunTree_sup_A_eq hb hu
  have hgo := hgrow₂.hgo
  rw [ite_eq_right hstop_bw] at hgo
  intro c
  by_cases hc_old : c.val < nComp
  · obtain ⟨⟨v0, hv0V, hv0_eq⟩, hc0_deg⟩ := hphase.hcomp_deg ⟨c.val, hc_old⟩
    have hnot_A : (∀ e ∈ es,
        (e.u ∈ V ∧ s.mem (ctx.auxBase + 2 * n + s.mem (ctx.auxBase + e.u.val)) = c.val) ↔
        (e.v ∈ V ∧ s.mem (ctx.auxBase + 2 * n + s.mem (ctx.auxBase + e.v.val)) = c.val)) →
        ∀ u ∈ A, s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + u.val)) ≠ c.val := by
      intro hcl_old u huA heq_c
      rw [hsup_A_eq huA] at heq_c
      rcases hgo with ⟨_, hjn_n | hjn_lt⟩
      · rcases hjn_n with ⟨hjn_eq, _⟩
        rw [ite_eq_right (by rw [hjn_eq]; exact Nat.not_lt.mpr t.isLt.le)] at heq_c
        omega
      · rcases hjn_lt with ⟨hjn, _, eIdx, _, _, _, y0, u0, hu0A, hy0_jn, heIdx⟩
        rw [ite_eq_left hjn] at heq_c
        have hy0_V : y0 ∈ V := by
          have : y0 ∈ visitedSet ctx.auxBase n t.val s₁.mem := mem_visitedSet.mpr (hy0_jn ▸ hjn)
          rwa [hb.hV_vis_s1] at this
        have hy0_eq : s.mem (ctx.auxBase + 2 * n + s.mem (ctx.auxBase + y0.val)) = c.val := by
          rw [← hb.htr_s1_V y0 hy0_V, hy0_jn]; exact heq_c
        rcases heIdx with ⟨hu_e, hv_e⟩ | ⟨hv_e, hu_e⟩
        · have h1 := (hcl_old es[eIdx.val] (List.getElem_mem eIdx.isLt)).mpr
            ⟨by rw [hv_e]; exact hy0_V, by rw [hv_e]; exact hy0_eq⟩
          rw [hu_e] at h1
          exact Finset.disjoint_left.mp hb.hdisj_VA h1.1 hu0A
        · have h1 := (hcl_old es[eIdx.val] (List.getElem_mem eIdx.isLt)).mp
            ⟨by rw [hu_e]; exact hy0_V, by rw [hu_e]; exact hy0_eq⟩
          rw [hv_e] at h1
          exact Finset.disjoint_left.mp hb.hdisj_VA h1.1 hu0A
    refine ⟨⟨v0, hb.hV'_eq ▸ Finset.mem_union_left _ hv0V, (hsup_t_le hv0V).trans hv0_eq⟩, ?_⟩
    rcases hc0_deg with hcl_old | ⟨Ac, Zc, hAcV, hAc_eq, hZc_card, hZc_nbr⟩
    · left
      have hv_old : ∀ u : Fin n, (u ∈ V' ∧
          s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + u.val)) = c.val) ↔
          (u ∈ V ∧ s.mem (ctx.auxBase + 2 * n + s.mem (ctx.auxBase + u.val)) = c.val) :=
        fun u => by
          dsimp only [V', V, A]; rw [hb.hV'_eq, Finset.mem_union]
          refine ⟨fun ⟨hu, h⟩ => hu.elim (fun huV => ⟨huV, (hsup_t_le huV).symm.trans h⟩)
              (fun huA => absurd h (hnot_A hcl_old _ huA)),
            fun ⟨huV, h⟩ => ⟨Or.inl huV, (hsup_t_le huV).trans h⟩⟩
      intro e he
      exact (hv_old e.u).trans ((hcl_old e he).trans (hv_old e.v).symm)
    · right
      exact ⟨Ac, Zc, hAcV.trans (hb.hV'_eq ▸ Finset.subset_union_left),
        fun u hu => (hsup_t_le (hAcV hu)).trans (hAc_eq u hu), hZc_card, hZc_nbr⟩
  · rcases hgo with ⟨_, ⟨hjn_eq, _, _, hclosed_or_Z⟩ | ⟨hjn_lt, _⟩⟩
    · have hjn_nlt : ¬(res.jn < t.val) := by rw [hjn_eq]; exact Nat.not_lt.mpr t.isLt.le
      have hc_eq : c.val = nComp := by
        have hlt : c.val < nComp + 1 :=
          lt_of_lt_of_eq c.isLt (by rw [hb.hres_fin_eq]; dsimp only; exact ite_eq_right hjn_nlt)
        omega
      refine ⟨⟨t, hb.hV'_eq ▸ Finset.mem_union_right _ hgrow₂.ht_tr,
        (hsup_A_eq hgrow₂.ht_tr).trans (by rw [ite_eq_right hjn_nlt, hc_eq])⟩, ?_⟩
      rcases hclosed_or_Z with hcl_A | ⟨Z, hZc, hZnbr⟩
      · left
        have hv_new : ∀ u : Fin n, (u ∈ V' ∧
            s₄.mem (ctx.auxBase + 2 * n + s₄.mem (ctx.auxBase + u.val)) = c.val) ↔ u ∈ A :=
          fun u => by
            dsimp only [V', V, A]; rw [hb.hV'_eq, Finset.mem_union]
            refine ⟨fun ⟨hu, h⟩ => hu.elim (fun huV => by
                have := hphase.hsup_range _ huV; rw [hsup_t_le huV] at h; omega) id,
              fun huA => ⟨Or.inr huA, (hsup_A_eq huA).trans
                (by rw [ite_eq_right hjn_nlt, hc_eq])⟩⟩
        intro e he
        exact (hv_new e.u).trans ((hcl_A e he).trans (hv_new e.v).symm)
      · right
        exact ⟨A, Z, hb.hV'_eq ▸ Finset.subset_union_right,
          fun u hu => (hsup_A_eq hu).trans (by rw [ite_eq_right hjn_nlt, hc_eq]), hZc, hZnbr⟩
    · exfalso
      have hlt : c.val < nComp :=
        lt_of_lt_of_eq c.isLt (by rw [hb.hres_fin_eq]; dsimp only; exact ite_eq_left hjn_lt)
      omega

private theorem ftRunTree_phase_next {w n K : ℕ} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {t : Fin n} {nComp selLen0 : ℕ} {selIdxs0 selTree_bw : List (Fin es.length)}
    {scanned_bw : Finset (Fin n)} {res : FTGrowState} {res_fin : ℕ × ℕ}
    {s s₁ s₂ s₃ s₄ : Memory.State} {hn : Fits w n} {hK : Fits w K}
    (hphase : FTPhaseInv ctx es t.val nComp selLen0 (selLen0 + selIdxs0.length) selIdxs0 s.mem)
    (hgrow₂ : FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s₁ selTree_bw scanned_bw res s₂)
    (hstop_bw : res.go ≠ 1) (hb : FTRunTreeBridge ctx t nComp res res_fin s s₁ s₂ s₃ s₄)
    (hsel_buf_s4 : ∀ j (hj : j < (selIdxs0 ++ selTree_bw).length),
      s₄.mem (ctx.selBufBase + selLen0 + j) = es[(selIdxs0 ++ selTree_bw)[j].val].id) :
    FTPhaseInv ctx es (t.val + 1) res_fin.1 selLen0 res_fin.2 (selIdxs0 ++ selTree_bw) s₄.mem := by
  let A := trSet ctx.auxBase n t s₂.mem
  let V := visitedSet ctx.auxBase n t.val s.mem
  let V' := visitedSet ctx.auxBase n (t.val + 1) s₄.mem
  have hgo0 : res.go = 0 := hgrow₂.hgo_bin.resolve_right hstop_bw
  have hcard_V' : V'.card = V.card + A.card := by
    dsimp only [V', V, A]; rw [hb.hV'_eq, Finset.card_union_of_disjoint hb.hdisj_VA]
  have hsup_t_le {v : Fin n} (hv : v ∈ V) := ftRunTree_sup_t_le hb hv
  have hsup_A_eq {u : Fin n} (hu : u ∈ A) := ftRunTree_sup_A_eq hb hu
  refine ⟨fun v => ?_, fun v hv => ?_, ?_, ?_, ?_, hgrow₂.hsel_nd, fun idx hidx => ?_,
    hgrow₂.hacyclic, hgrow₂.hext, hsel_buf_s4, fun v hv => ?_,
    ftRunTree_phase_rel hphase hgrow₂ hstop_bw hb,
    ftRunTree_phase_deg hphase hgrow₂ hstop_bw hb⟩
  · rw [hb.htr_s4 v]
    rcases hgrow₂.hbound v with hle | hle | heq
    · left; omega
    · left; omega
    · right; exact heq
  · by_cases hvt : v.val < t.val
    · have hvV : v ∈ V := mem_visitedSet.mpr (hphase.hprev_vis v hvt)
      rw [hb.htr_s4 v, hb.hV_sub_s2 v hvV]
      exact (hphase.hprev_vis v hvt).trans (Nat.lt_succ_self _)
    · have hveq : v = t := Fin.ext (by omega)
      have htA : v ∈ A := hveq ▸ hgrow₂.ht_tr
      rw [hb.htr_s4 v, mem_trSet.mp htA]
      exact Nat.lt_succ_self _
  · rw [hb.hres_fin_eq]
    by_cases hjn : res.jn < t.val
    · rw [ite_eq_left hjn]; exact hphase.hncomp_le.trans (Nat.le_succ _)
    · rw [ite_eq_right hjn]; exact Nat.succ_le_succ hphase.hncomp_le
  · rw [hb.hres_fin_eq]
    exact hgrow₂.hsel_len
  · rw [hb.hres_fin_eq, hcard_V']
    have h1 := hgrow₂.hsel_card
    dsimp only [V', V, A] at h1 ⊢
    rw [hb.hV_vis_s1] at h1
    by_cases hjn : res.jn < t.val
    · rw [ite_eq_left hjn, ite_eq_left ⟨hgo0, hjn⟩] at *
      omega
    · rw [ite_eq_right hjn, ite_eq_right (by intro ⟨_, hbad⟩; exact hjn hbad)] at *
      omega
  · have h := hgrow₂.hsel_verts idx hidx
    rw [hb.hV_vis_s1, ← hb.hV'_eq] at h
    exact h
  · rw [hb.hV'_eq, Finset.mem_union] at hv
    rcases hv with hvV | hvA
    · rw [hsup_t_le hvV]
      have hlt := hphase.hsup_range v hvV
      rw [hb.hres_fin_eq]
      by_cases hjn : res.jn < t.val <;> [rw [ite_eq_left hjn]; rw [ite_eq_right hjn]] <;> omega
    · rw [hb.htr_s4 v, mem_trSet.mp hvA, hb.hsup_fin_eq, hb.hres_fin_eq]
      by_cases hjn : res.jn < t.val
      · rw [ite_eq_left hjn, ite_eq_left hjn, hb.hsup_s3_s res.jn (hjn.trans t.isLt)]
        have hgo := hgrow₂.hgo; rw [ite_eq_right hstop_bw] at hgo
        rcases hgo with ⟨_, ⟨hjn_n, _⟩ | ⟨_, _, _, _, _, _, y0, _, _, hy0_jn, _⟩⟩
        · omega
        · have hy0_V : y0 ∈ V := by
            have : y0 ∈ visitedSet ctx.auxBase n t.val s₁.mem := mem_visitedSet.mpr (hy0_jn ▸ hjn)
            rwa [hb.hV_vis_s1] at this
          rw [hb.htr_s1_V y0 hy0_V] at hy0_jn
          rw [← hy0_jn]
          exact hphase.hsup_range y0 hy0_V
      · rw [ite_eq_right hjn, ite_eq_right hjn]
        omega

/-- Specification of `ftRunTree`: grows one bounded-heap DJP tree from root `t`, sparsely resets
touched heap entries in `O(touchedLen + 1)` memory steps via `resetProg`, assigns `sup[t]`, advances
`FTPhaseInv` from `t` to `t + 1`, and pays `memoryCost` + vertex-potential drop up to `7`. -/
theorem ftRunTree_spec {w n K mRef : ℕ} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {t : Fin n} {nComp selLen0 : ℕ} {selIdxs0 : List (Fin es.length)} {s : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s) (hwf : Memory.WellFormed w s)
    (ht_tr_n : s.mem (ctx.auxBase + t.val) = n)
    (hfh_inv : (framed hs.hn hs.hK ctx.fhBase).inv s)
    (hfh_empty : (framed hs.hn hs.hK ctx.fhBase).abs s = IndexedMinPQ.empty n)
    (hfh_pot : potential n ((layout n ctx.fhBase).abs s) = 0)
    (hphase : FTPhaseInv ctx es t.val nComp selLen0 (selLen0 + selIdxs0.length) selIdxs0 s.mem) :
    let prog := ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftRunTreeSafe w ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, a ∉ footprint n ctx.fhBase →
      (a < ctx.auxBase ∨ ctx.auxBase + 2 * n ≤ a) →
      (a < ctx.auxBase + 2 * n + t.val ∨ ctx.auxBase + 2 * n + t.val + 1 ≤ a) →
      (a < ctx.auxBase + 4 * n ∨ ctx.auxBase + 5 * n ≤ a) →
      (a < ctx.selBufBase + selLen0 ∨ ctx.selBufBase + selLen0 + n ≤ a) →
      s'.mem a = s.mem a) ∧
    (framed hs.hn hs.hK ctx.fhBase).inv s' ∧
    (framed hs.hn hs.hK ctx.fhBase).abs s' = IndexedMinPQ.empty n ∧
    potential n ((layout n ctx.fhBase).abs s') = 0 ∧
    (∃ selIdxs', FTPhaseInv ctx es (t.val + 1) res.1 selLen0 res.2 selIdxs' s'.mem) ∧
    memoryCost prog s +
      (∑ v : Fin n,
        if s'.mem (ctx.auxBase + v.val) < t.val + 1 then 0
        else vertexPot ctx n mRef v s'.mem) ≤
      7 +
      (∑ v : Fin n,
        if s.mem (ctx.auxBase + v.val) < t.val then 0
        else vertexPot ctx n mRef v s.mem) := by
  have hcn := hs.cn; have hn := hs.hn; have hK := hs.hK
  let selLenCur := selLen0 + selIdxs0.length
  let s₁ : Memory.State := ⟨Function.update s.mem (ctx.auxBase + t.val) t.val, s.frontier⟩
  have hs1_eq : (Memory.spec 0).clientState s (Memory.write (ctx.auxBase + t.val) t.val) = s₁ :=
    rfl
  have hnot_fp_tr_t : ctx.auxBase + t.val ∉ footprint n ctx.fhBase := by
    simp only [footprint, Finset.mem_Ico]; have := hs.fhLtAux; omega
  obtain ⟨hinv₁, habs₁, hpot₁⟩ := framed_preserved (s' := s₁) hfh_inv (fun a ha => by
    dsimp only [s₁]
    exact Function.update_of_ne (fun h : a = ctx.auxBase + t.val => by
      subst h; exact hnot_fp_tr_t ha) _ _)
    (by dsimp only [s₁]; exact le_rfl) (by dsimp only [s₁]; exact hwf.frontier_fits)
  have hwf₁ : Memory.WellFormed w s₁ := by
    simpa only [s₁] using wellFormed_update hwf (hn.of_le t.isLt.le)
  have htr_s1 : ∀ v : Fin n, v ≠ t →
      s₁.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) := fun v hv => by
    dsimp only [s₁]
    exact Function.update_of_ne (by intro h; apply hv; exact Fin.ext (by omega)) _ _
  have htr_t_s1 : s₁.mem (ctx.auxBase + t.val) = t.val := Function.update_self _ _ _
  have htrSet_s1 : trSet ctx.auxBase n t s₁.mem = {t} := by
    ext v; simp only [mem_trSet, Finset.mem_singleton]
    by_cases hvt : v = t
    · rw [hvt, htr_t_s1]; simp
    · rw [htr_s1 v hvt]
      rcases hphase.hbound v with hlt | heq <;> exact ⟨fun h => by omega, fun h => absurd h hvt⟩
  have hvis_s1 : visitedSet ctx.auxBase n t.val s₁.mem = visitedSet ctx.auxBase n t.val s.mem := by
    ext v; simp only [mem_visitedSet]
    by_cases hvt : v = t
    · rw [hvt, htr_t_s1, ht_tr_n]; constructor <;> intro h <;> omega
    · rw [htr_s1 v hvt]
  have ht_nvis : t ∉ visitedSet ctx.auxBase n t.val s.mem := by
    rw [mem_visitedSet, ht_tr_n]; omega
  have hsel_s1 : ∀ j (hj : j < [].length),
      s₁.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) =
        es[([][j] : Fin es.length).val].id :=
    fun _ hj => by simp at hj
  let st0 : FTGrowState := ⟨1, t.val, 0, selLenCur, ctx.n⟩
  have hcut0 : FTCutInv hn hK ctx es t ∅ 0 s₁ :=
    ⟨hinv₁, Nat.zero_le _, fun _ hi => by omega, by rw [touchedList_eq]; simp,
      fun _ hi => by omega, fun _ hi _ => by omega,
      fun v hv => by rw [habs₁, hfh_empty] at hv; simp [IndexedMinPQ.empty] at hv,
      fun v kv hkv => by rw [habs₁, hfh_empty] at hkv; simp [IndexedMinPQ.empty] at hkv,
      fun u hu => absurd hu (Finset.notMem_empty u)⟩
  have hgrow0 : FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s [] ∅ st0 s₁ := by
    refine ⟨rfl, hwf₁, Or.inr rfl, fun a ha => ?_,
      by rw [htrSet_s1]; exact Finset.mem_singleton_self _,
      fun v => ?_, fun v hv => ?_, fun v => ?_,
      hinv₁, Nat.zero_le _, fun _ hi => by dsimp only [st0] at hi; omega,
      fun v hv => by rw [habs₁, hfh_empty] at hv; simp [IndexedMinPQ.empty] at hv,
      by simp [st0, selLenCur],
      (by
        have := hphase.hsel_card
        dsimp only [st0]
        simp only [List.append_nil] at *
        rw [htrSet_s1, Finset.card_singleton]
        change selIdxs0.length + nComp + (if (1 : ℕ) = 0 ∧ ctx.n < t.val then 0 else 1) = _
        rw [ite_eq_right (by omega)]
        omega),
      by rw [List.append_nil]; exact hphase.hsel_nd,
      fun idx hidx => hphase.hsel_verts idx hidx,
      fun idx hidx => by
        rw [List.append_nil] at hidx
        exact ⟨Finset.mem_union_left _ (hphase.hsel_verts idx hidx).1,
          Finset.mem_union_left _ (hphase.hsel_verts idx hidx).2⟩,
      by rw [List.append_nil]; exact hphase.hacyclic,
      by rw [List.append_nil]; exact hphase.hext, hsel_s1, ?_⟩
    · dsimp only [s₁]
      exact Function.update_of_ne
        (fun h => ha (Or.inr (Or.inl ⟨by omega, by have := t.isLt; omega⟩))) _ _
    · by_cases hvt : v = t
      · rw [hvt, htr_t_s1]; exact Or.inr (Or.inl rfl)
      · rw [htr_s1 v hvt]
        rcases hphase.hbound v with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr (Or.inr heq)
    · rw [htrSet_s1, Finset.mem_singleton] at hv; rw [hv]; exact ht_tr_n
    · by_cases hvt : v = t
      · exact Or.inr ⟨hvt ▸ ht_tr_n, hvt ▸ htr_t_s1⟩
      · exact Or.inl (htr_s1 v hvt)
    · dsimp only [st0]; rw [ite_eq_left rfl]
      refine ⟨hcut0, t, rfl, by rw [htrSet_s1]; exact Finset.mem_singleton_self _,
        Finset.notMem_empty _, by rw [htrSet_s1]; simp, fun _ h => by simp at h,
        fun x' hx' y' hy' => ?_⟩
      rw [htrSet_s1, Finset.mem_singleton] at hx' hy'
      rw [hx', hy']; exact (edgePartition _).refl t
  let I_bw (st : FTGrowState) (s_cur : Memory.State) : Prop :=
    s_cur.frontier = s₁.frontier ∧
    Memory.WellFormed w s_cur ∧
    (∀ a, ¬growMod ctx n selLen0 selIdxs0.length a → s_cur.mem a = s₁.mem a) ∧
    (∀ v : Fin n, s_cur.mem (ctx.auxBase + v.val) = s₁.mem (ctx.auxBase + v.val) ∨
      (s₁.mem (ctx.auxBase + v.val) = n ∧ s_cur.mem (ctx.auxBase + v.val) = t.val)) ∧
    (∀ v ∈ trSet ctx.auxBase n t s₁.mem, v ∈ trSet ctx.auxBase n t s_cur.mem) ∧
    ∃ selTree scanned, FTGrowInv hn hK ctx es t nComp selLen0 selIdxs0 s selTree scanned st s_cur
  let S_bw : Set ℕ := {a | growMod ctx n selLen0 selIdxs0.length a}
  have hbw_spec := boundedWhile_potential_spec
    (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
    ftGrowStep ftGrowStepSafe w ⟨ctx, t.val⟩ 0 I_bw (growRank ctx n t)
    (growPot ctx n mRef t) S_bw
    (fun st s_cur _ hrank0 => by
      simp only [growRank_eq] at hrank0
      by_cases hgo : st.go = 0
      · simp [hgo]
      · rw [ite_eq_right hgo] at hrank0
        have hc : (trSet ctx.auxBase n t s_cur.mem).card ≤ n :=
          (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
        omega)
    (fun st s_cur ⟨hfr_c, hwf_c, hmod_c, hrel_c, htr_c, sel_c, sc_c, hgrow_c⟩ hgo1 => by
      have hs_c : FTStatic w n K mRef selLen0 ctx es s_cur :=
        hs.of_workMod (by rw [hfr_c]) fun a hfp h1 h2 => by
          have hng : ¬growMod ctx n selLen0 selIdxs0.length a := by
            simp only [growMod, not_or]
            refine ⟨hfp, fun h => ?_, fun h => ?_, fun h => ?_⟩
            · rcases h1 with h1 | h1 <;> omega
            · rcases h1 with h1 | h1 <;> omega
            · rcases h2 with h2 | h2 <;> omega
          rw [hmod_c a hng]
          dsimp only [s₁]; exact Function.update_of_ne (by rcases h1 with h | h <;> omega) _ _
      have hg := ftGrowStep_spec (s₀ := s) hs_c hwf_c hfr_c hgo1 hgrow_c
      dsimp only at hg
      rcases hg with ⟨hsafe_g, hv_g, hfr_g, hwf_g, hmod_g, hrel_g, htr_g, ⟨sel', sc', hgrow'⟩,
        hpot_g, hrank_g⟩
      refine ⟨hsafe_g, hv_g, by omega, ⟨by rw [hfr_g], fun a _ ha => hmod_g a ha⟩,
        ⟨hfr_g.trans hfr_c, hwf_g, fun a ha => (hmod_g a ha).trans (hmod_c a ha), fun v => ?_,
          fun v hv => htr_g v (htr_c v hv), sel', sc', hgrow'⟩, hrank_g⟩
      rcases hrel_g v with heq | ⟨hn_cur, ht_next⟩
      · rw [heq]; exact hrel_c v
      · rcases hrel_c v with heq1 | ⟨_, ht1⟩
        · exact Or.inr ⟨heq1.symm.trans hn_cur, ht_next⟩
        · exfalso; have := t.isLt; omega)
    ctx.n st0 s₁ ⟨rfl, hwf₁, fun _ _ => rfl, fun _ => Or.inl rfl, fun _ hv => hv, [], ∅, hgrow0⟩
    (by
      simp only [growRank_eq]
      rw [ite_eq_right (by dsimp only [st0]; decide), htrSet_s1, Finset.card_singleton, hcn]
      omega)
  dsimp only at hbw_spec
  generalize h_res : (Memory.spec 0).clientResult s₁
    (boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
      ftGrowStep ⟨ctx, t.val⟩ ctx.n st0) = res at hbw_spec
  generalize h_s2 : (Memory.spec 0).clientState s₁
    (boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
      ftGrowStep ⟨ctx, t.val⟩ ctx.n st0) = s₂ at hbw_spec
  rcases hbw_spec with ⟨hsafe_bw, hv_bw, hstop_bw, ⟨hfr₂, hwf₂, hmod₂, hrel₂, htr₂,
    selTree_bw, scanned_bw, hgrow₂⟩, _, hc_bw⟩
  have hgo0_bw : res.go = 0 := hgrow₂.hgo_bin.resolve_right hstop_bw
  have hfit_tl : Fits w (res.touchedLen + 1) :=
    hs.fitAux.of_le (by have := hgrow₂.htl_le; omega)
  have hres_fr : ctx.auxBase + 4 * ctx.n + res.touchedLen ≤ s₂.frontier := by
    rw [hfr₂]; dsimp only [s₁]; rw [hcn]; have := hs.auxFr; have := hgrow₂.htl_le; omega
  have hdisj_reset : ∀ i < res.touchedLen,
      ctx.auxBase + 4 * ctx.n + i < ctx.fhBase + 7 * ctx.n ∨
      ctx.fhBase + 8 * ctx.n ≤ ctx.auxBase + 4 * ctx.n + i :=
    fun i _ => Or.inr (by rw [hcn]; have := hs.fhLtAux; omega)
  have hn_c : Fits w ctx.n := by rw [hcn]; exact hn
  have hinv₂_c : (framed hn_c hK ctx.fhBase).inv s₂ :=
    framed_inv_congr hcn.symm hn hn_c hK hgrow₂.hinv
  let argsR : ResetArgs := ⟨ctx.n, ctx.fhBase, ctx.auxBase + 4 * ctx.n, res.touchedLen⟩
  have hfh_rst := resetProg_spec argsR hwf₂ hn_c hK hfit_tl hinv₂_c
    (by dsimp only [argsR]; exact hres_fr)
    (fun i hi => by dsimp only [argsR]; rw [hcn]; exact hgrow₂.htouched_lt i hi)
    (by dsimp only [argsR]; exact hdisj_reset)
    (fun v hv => by
      have hv_n : ((framed hn hK ctx.fhBase).abs s₂ ⟨v.val, hcn ▸ v.isLt⟩).isSome = true := by
        rw [framed_abs_congr hcn.symm hn hn_c hK s₂ ⟨v.val, hcn ▸ v.isLt⟩]; exact hv
      obtain ⟨i, hi, heq⟩ := hgrow₂.htouched_cov ⟨v.val, hcn ▸ v.isLt⟩ hv_n
      have heq' : s₂.mem (ctx.auxBase + 4 * ctx.n + i) = v.val := by rw [hcn]; exact heq
      exact ⟨i, hi, heq'⟩)
  dsimp only at hfh_rst
  set s₃ := (Memory.spec 0).clientState s₂ (resetProg argsR)
  have h_s3 : (Memory.spec 0).clientState s₂ (resetProg argsR) = s₃ := rfl
  rcases hfh_rst with ⟨hsafe_rst, hv_rst, hfr₃, hwf₃, hmod_rst, hinv₃_c, hemp₃_c, hpot₃_c, hc_rst⟩
  have hnc_fit : Fits w (nComp + 1) := hn.of_le (by have := hphase.hncomp_le; omega)
  have hft_fin := ftFinishTree_spec (ctx := ctx) (t := t.val) (nComp := nComp)
    (selLen := res.selLen) (jn := res.jn) hs.fit16 hwf₃
    (by rw [hcn]; exact hs.fitAux.of_le (by omega)) hnc_fit
    (by rw [hcn]; exact t.isLt)
    (by rw [hfr₃, hfr₂]; dsimp only [s₁]; rw [hcn]; have := hs.auxFr; omega)
  dsimp only at hft_fin
  generalize h_res_fin : (Memory.spec 0).clientResult s₃
    (ftFinishTree ⟨ctx, t.val, nComp, res.selLen, res.jn⟩) = res_fin at hft_fin
  generalize h_s4 : (Memory.spec 0).clientState s₃
    (ftFinishTree ⟨ctx, t.val, nComp, res.selLen, res.jn⟩) = s₄ at hft_fin
  rcases hft_fin with ⟨hsafe_fin, hv_fin, hfr₄, hwf₄, hmod_fin, hres_fin_eq, hsup_fin_eq, hc_fin⟩
  have hprog_eq : ftRunTree ⟨ctx, t.val, nComp, selLenCur⟩ =
      (Memory.write (ctx.auxBase + t.val) t.val >>= fun _ =>
       boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
         ftGrowStep ⟨ctx, t.val⟩ ctx.n st0 >>= fun r =>
       resetProg ⟨ctx.n, ctx.fhBase, ctx.auxBase + 4 * ctx.n, r.touchedLen⟩ >>= fun _ =>
       ftFinishTree ⟨ctx, t.val, nComp, r.selLen, r.jn⟩) := rfl
  have hsafe_all : ftRunTreeSafe w ⟨ctx, t.val, nComp, selLenCur⟩ s := by
    refine ⟨hs.fit16, by rw [hcn]; exact hs.fitAux, hn_c, by rw [hcn]; exact t.isLt,
      by rw [hcn]; exact hs.auxFr, hsafe_bw, ?_, ?_⟩
    · rw [h_res, h_s2]; exact hsafe_rst
    · rw [h_res, h_s2, h_s3]; exact hsafe_fin
  have hv_all : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (ftRunTree ⟨ctx, t.val, nComp, selLenCur⟩)) := by
    rw [hprog_eq]
    refine validHistory_write_bind (by have := hs.auxFr; have := t.isLt; omega)
      (hn.of_le t.isLt.le) ?_
    change (Memory.spec w).ValidHistory s₁ _
    refine validHistory_bind_step hv_bw ?_
    rw [h_res, h_s2]
    refine validHistory_bind_step hv_rst ?_
    rw [h_s3]
    exact hv_fin
  have hst_all : (Memory.spec 0).clientState s (ftRunTree ⟨ctx, t.val, nComp, selLenCur⟩) = s₄ := by
    rw [hprog_eq, StateTransitionSpec.clientState_bind, hs1_eq,
      StateTransitionSpec.clientState_bind, h_res, h_s2,
      StateTransitionSpec.clientState_bind, h_s3, h_s4]
  have hres_all : (Memory.spec 0).clientResult s (ftRunTree ⟨ctx, t.val, nComp, selLenCur⟩) =
      res_fin := by
    rw [hprog_eq, StateTransitionSpec.clientResult_bind, hs1_eq,
      StateTransitionSpec.clientResult_bind, h_res, h_s2,
      StateTransitionSpec.clientResult_bind, h_s3, h_res_fin]
  have hmod_rst' : ∀ a, a ∉ footprint n ctx.fhBase → s₃.mem a = s₂.mem a := by
    intro a ha
    have ha_c : a ∉ footprint argsR.capacity argsR.heapBase := by
      dsimp only [argsR]; rw [hcn]; exact ha
    exact hmod_rst a ha_c
  have hmod_s4 : ∀ a, a ∉ footprint n ctx.fhBase →
      (a < ctx.auxBase ∨ ctx.auxBase + 2 * n ≤ a) →
      (a < ctx.auxBase + 2 * n + t.val ∨ ctx.auxBase + 2 * n + t.val + 1 ≤ a) →
      (a < ctx.auxBase + 4 * n ∨ ctx.auxBase + 5 * n ≤ a) →
      (a < ctx.selBufBase + selLen0 ∨ ctx.selBufBase + selLen0 + n ≤ a) →
      s₄.mem a = s.mem a := by
    intro a hfp h1 h2 h3 h4
    have hneq_fin : a ≠ ctx.auxBase + 2 * ctx.n + t.val := by
      rw [hcn]; rcases h2 with h2 | h2 <;> omega
    rw [hmod_fin a hneq_fin, hmod_rst' a hfp, hmod₂ a (by
      simp only [growMod, not_or]; refine ⟨hfp, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        [rcases h1 with h1 | h1; rcases h3 with h3 | h3; rcases h4 with h4 | h4] <;> omega)]
    dsimp only [s₁]; exact Function.update_of_ne (by rcases h1 with h1 | h1 <;> omega) _ _
  have hnot_fp_4n : ∀ a, ctx.auxBase ≤ a → a < ctx.auxBase + 4 * n →
      a ∉ footprint n ctx.fhBase := fun a h1 h2 => by
    simp only [footprint, Finset.mem_Ico]; have := hs.fhLtAux; omega
  have htr_s4 : ∀ v : Fin n, s₄.mem (ctx.auxBase + v.val) = s₂.mem (ctx.auxBase + v.val) := by
    intro v
    rw [hmod_fin _ (by rw [hcn]; have := v.isLt; omega),
      hmod_rst' _ (hnot_fp_4n _ (by omega) (by omega))]
  have hsup_old_s4 : ∀ k < n, k ≠ t.val →
      s₄.mem (ctx.auxBase + 2 * n + k) = s.mem (ctx.auxBase + 2 * n + k) := fun k hk hne =>
    hmod_s4 _ (hnot_fp_4n _ (by omega) (by omega)) (Or.inr (by omega))
      (by by_cases hlt : k < t.val <;> [left; right] <;> omega) (Or.inl (by omega))
      (by rcases hs.selDisjAux with hd | hd <;> [right; left] <;> omega)
  have hsup_s3_s : ∀ k < n, s₃.mem (ctx.auxBase + 2 * n + k) = s.mem (ctx.auxBase + 2 * n + k) := by
    intro k hk
    rw [hmod_rst' _ (hnot_fp_4n _ (by omega) (by omega)), hmod₂ _ (by
      simp only [growMod, not_or]
      refine ⟨hnot_fp_4n _ (by omega) (by omega), fun h => by omega, fun h => by omega, ?_⟩
      rcases hs.selDisjAux with hd | hd <;> omega)]
    dsimp only [s₁]; exact Function.update_of_ne (by omega) _ _
  have hinv₃ : (framed hn hK ctx.fhBase).inv s₃ := framed_inv_congr hcn hn_c hn hK hinv₃_c
  have hemp₃ : (framed hn hK ctx.fhBase).abs s₃ = IndexedMinPQ.empty n := by
    ext v; rw [framed_abs_congr hcn.symm hn hn_c hK s₃ v, hemp₃_c]; rfl
  have hpot₃ : potential n ((layout n ctx.fhBase).abs s₃) = 0 := by
    rw [potential_congr hcn.symm s₃]; exact hpot₃_c
  have hfp_sub : ∀ a ∈ footprint n ctx.fhBase, a ≠ ctx.auxBase + 2 * ctx.n + t.val := by
    intro a ha; simp only [footprint, Finset.mem_Ico] at ha
    rw [hcn]; have := hs.fhLtAux; omega
  obtain ⟨hinv₄, habs₄, hpot₄⟩ := framed_preserved hinv₃
    (fun a ha => hmod_fin a (hfp_sub a ha)) (by rw [hfr₄])
    (by rw [hfr₄]; exact hwf₃.frontier_fits)
  have hemp₄ : (framed hn hK ctx.fhBase).abs s₄ = IndexedMinPQ.empty n := by rw [habs₄, hemp₃]
  have hpot₄' : potential n ((layout n ctx.fhBase).abs s₄) = 0 := by rw [hpot₄, hpot₃]
  let A := trSet ctx.auxBase n t s₂.mem
  let V := visitedSet ctx.auxBase n t.val s.mem
  let V' := visitedSet ctx.auxBase n (t.val + 1) s₄.mem
  have hV_sub_s2 : ∀ v ∈ V, s₂.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val) := by
    intro v hv
    have hv_lt : s.mem (ctx.auxBase + v.val) < t.val := mem_visitedSet.mp hv
    have hvt : v ≠ t := fun h => by subst h; omega
    have h1 := htr_s1 v hvt
    rcases hrel₂ v with heq | ⟨hn_v, _⟩
    · exact heq.trans h1
    · exfalso; omega
  have hV'_eq : V' = V ∪ A := by
    ext v
    simp only [V', V, A, mem_visitedSet, mem_trSet, Finset.mem_union, htr_s4 v]
    rcases hgrow₂.hbound v with hle | hlt | heq
    · constructor
      · intro _; left
        rcases hrel₂ v with heq1 | ⟨_, ht_eq⟩
        · have hvt : v ≠ t := fun h => by subst h; rw [htr_t_s1] at heq1; omega
          rw [heq1, htr_s1 v hvt] at hle; exact hle
        · exfalso; omega
      · rintro (hlt_s | heq_t)
        · have hvt : v ≠ t := fun h => by subst h; omega
          rcases hrel₂ v with heq1 | ⟨hn_v, _⟩
          · rw [heq1, htr_s1 v hvt]; exact hlt_s.trans (Nat.lt_succ_self _)
          · exfalso; rw [htr_s1 v hvt] at hn_v; omega
        · omega
    · exact ⟨fun _ => Or.inr hlt, fun _ => hlt ▸ Nat.lt_succ_self _⟩
    · constructor
      · intro hbad; exfalso; omega
      · rintro (hlt_s | hbad)
        · have hvt : v ≠ t := fun h => by subst h; omega
          rcases hrel₂ v with heq1 | ⟨hn_v, _⟩
          · rw [heq1, htr_s1 v hvt] at heq; omega
          · omega
        · omega
  have hdisj_VA : Disjoint V A := Finset.disjoint_left.mpr fun v hvV hvA => by
    have := hV_sub_s2 v hvV
    rw [mem_visitedSet] at hvV; rw [mem_trSet] at hvA; omega
  have hsel_buf_s4 : ∀ j (hj : j < (selIdxs0 ++ selTree_bw).length),
      s₄.mem (ctx.selBufBase + selLen0 + j) = es[(selIdxs0 ++ selTree_bw)[j].val].id := by
    intro j hj
    have hsel_lt_n : (selIdxs0 ++ selTree_bw).length ≤ n := by
      have hc := hgrow₂.hsel_card
      have hle_sum : (visitedSet ctx.auxBase n t.val s.mem).card + A.card ≤ n := by
        rw [← Finset.card_union_of_disjoint hdisj_VA]
        exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      dsimp only [A] at hle_sum; split_ifs at hc <;> omega
    have hj_n : j < n := hj.trans_le hsel_lt_n
    by_cases hj0 : j < selIdxs0.length
    · rw [congrArg (fun idx : Fin es.length => es[idx.val].id) (List.getElem_append_left hj0)]
      rw [hmod_fin _ (by rw [hcn]; rcases hs.selDisjAux with hd | hd <;> omega),
        hmod_rst' _ (by
          simp only [footprint, Finset.mem_Ico]; rcases hs.selDisjFh with hd | hd <;> omega),
        hmod₂ _ (fun hgm => by
          simp only [growMod, footprint, Finset.mem_Ico] at hgm
          rcases hs.selDisjFh with hd | hd <;> rcases hs.selDisjAux with ha | ha <;> omega)]
      dsimp only [s₁]
      rw [Function.update_of_ne (by rcases hs.selDisjAux with hd | hd <;> omega)]
      exact hphase.hsel_buf j hj0
    · have hj_t : j - selIdxs0.length < selTree_bw.length := by
        simp only [List.length_append] at hj; omega
      have hj_eq : j = selIdxs0.length + (j - selIdxs0.length) := by omega
      rw [congrArg (fun idx : Fin es.length => es[idx.val].id)
        (List.getElem_append_right (Nat.not_lt.mp hj0))]
      rw [hmod_fin _ (by rw [hcn]; rcases hs.selDisjAux with hd | hd <;> omega),
        hmod_rst' _ (by
          simp only [footprint, Finset.mem_Ico]
          rcases hs.selDisjFh with hd | hd <;> omega)]
      have hbuf := hgrow₂.hsel_buf (j - selIdxs0.length) hj_t
      rwa [show ctx.selBufBase + selLen0 + selIdxs0.length + (j - selIdxs0.length) =
        ctx.selBufBase + selLen0 + j by omega] at hbuf
  have hphase_next := ftRunTree_phase_next hphase hgrow₂ hstop_bw
    ⟨hres_fin_eq, by simpa only [hcn] using hsup_fin_eq, htr_s4, hsup_old_s4, hsup_s3_s,
      hV_sub_s2, hV'_eq, hdisj_VA, rfl, fun _ _ => rfl⟩ hsel_buf_s4
  have hcost_all : memoryCost (ftRunTree ⟨ctx, t.val, nComp, selLenCur⟩) s +
      (∑ v : Fin n,
        if s₄.mem (ctx.auxBase + v.val) < t.val + 1 then 0
        else vertexPot ctx n mRef v s₄.mem) ≤
      7 +
      (∑ v : Fin n,
        if s.mem (ctx.auxBase + v.val) < t.val then 0
        else vertexPot ctx n mRef v s.mem) := by
    have hc_prog : memoryCost (ftRunTree ⟨ctx, t.val, nComp, selLenCur⟩) s ≤
        1 + memoryCost (boundedWhile (fun (_ : FTGrowEnv) (st : FTGrowState) => st.go = 1)
          ftGrowStep ⟨ctx, t.val⟩ ctx.n st0) s₁ + (2 * res.touchedLen + 4) + 2 := by
      dsimp only [argsR] at hc_rst
      rw [hprog_eq, memoryCost_bind', memoryCost_write, hs1_eq,
        memoryCost_bind', h_res, h_s2, memoryCost_bind', h_s3]
      omega
    have hoff_eq : ∀ (m : ℕ → ℕ), (∀ a, ctx.offBase ≤ a → a < ctx.offBase + n + 1 → m a = s.mem a) →
        ∀ v : Fin n, vertexPot ctx n mRef v m = vertexPot ctx n mRef v s.mem := by
      intro m hm v
      have h1 : m (ctx.offBase + v.val + 1) = s.mem (ctx.offBase + v.val + 1) :=
        hm _ (by omega) (by have := v.isLt; omega)
      have h2 : m (ctx.offBase + v.val) = s.mem (ctx.offBase + v.val) :=
        hm _ (by omega) (by have := v.isLt; omega)
      simp only [vertexPot_eq, h1, h2]
    have hoff_s1 : ∀ v : Fin n, vertexPot ctx n mRef v s₁.mem = vertexPot ctx n mRef v s.mem :=
      hoff_eq s₁.mem fun a h1 h2 => by
        dsimp only [s₁]
        exact Function.update_of_ne (by have := hs.offLtFh; have := hs.fhLtAux; omega) _ _
    have hoff_s2 : ∀ v : Fin n, vertexPot ctx n mRef v s₂.mem = vertexPot ctx n mRef v s.mem :=
      hoff_eq s₂.mem fun a h1 h2 => by
        rw [hmod₂ a (by
          simp only [growMod, footprint, Finset.mem_Ico, not_or, not_and]
          have := hs.offLtFh; have := hs.fhLtAux; rcases hs.selDisjOff with hd | hd <;> omega)]
        dsimp only [s₁]
        exact Function.update_of_ne (by have := hs.offLtFh; have := hs.fhLtAux; omega) _ _
    have hoff_s4 : ∀ v : Fin n, vertexPot ctx n mRef v s₄.mem = vertexPot ctx n mRef v s.mem :=
      hoff_eq s₄.mem fun a h1 h2 => hmod_s4 a (by
        simp only [footprint, Finset.mem_Ico]; have := hs.offLtFh; omega)
        (Or.inl (by have := hs.offLtFh; have := hs.fhLtAux; omega))
        (Or.inl (by have := hs.offLtFh; have := hs.fhLtAux; omega))
        (Or.inl (by have := hs.offLtFh; have := hs.fhLtAux; omega))
        (by rcases hs.selDisjOff with hd | hd <;> [right; left] <;> omega)
    have hsum_bw_id :
        (∑ v : Fin n,
          if s₂.mem (ctx.auxBase + v.val) = t.val ∧ ¬(res.go = 1 ∧ v.val = res.x) then 0
          else vertexPot ctx n mRef v s₂.mem) +
        (∑ v : Fin n,
          if s.mem (ctx.auxBase + v.val) < t.val then 0
          else vertexPot ctx n mRef v s.mem) =
        (∑ v : Fin n,
          if s₁.mem (ctx.auxBase + v.val) = t.val ∧ ¬(st0.go = 1 ∧ v.val = st0.x) then 0
          else vertexPot ctx n mRef v s₁.mem) +
        (∑ v : Fin n,
          if s₄.mem (ctx.auxBase + v.val) < t.val + 1 then 0
          else vertexPot ctx n mRef v s₄.mem) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hoff_s1 v, hoff_s2 v, hoff_s4 v, htr_s4 v]
      have hs1_false : ¬(s₁.mem (ctx.auxBase + v.val) = t.val ∧ ¬(st0.go = 1 ∧ v.val = st0.x)) := by
        intro ⟨h1, h2⟩
        by_cases hvt : v = t
        · rw [hvt] at h2; exact h2 ⟨rfl, rfl⟩
        · rw [htr_s1 v hvt] at h1
          rcases hphase.hbound v with hlt | heq <;> omega
      rw [ite_eq_right hs1_false]
      rcases hphase.hbound v with hlt | heq
      · have hvV : v ∈ V := mem_visitedSet.mpr hlt
        have hs2_v := hV_sub_s2 v hvV
        rw [ite_eq_right (fun h => by rw [hs2_v] at h; omega), ite_eq_left hlt,
          ite_eq_left (by rw [hs2_v]; exact hlt.trans (Nat.lt_succ_self _))]
      · rcases hgrow₂.hbound v with hle2 | hlt2 | heq2
        · exfalso
          rcases hrel₂ v with heq1 | ⟨_, ht_eq⟩
          · by_cases hvt : v = t
            · subst hvt; rw [heq1, htr_t_s1] at hle2; omega
            · rw [heq1, htr_s1 v hvt, heq] at hle2; omega
          · omega
        · rw [ite_eq_left ⟨hlt2, fun ⟨h0, _⟩ => by rw [hgo0_bw] at h0; omega⟩,
            ite_eq_right (by rw [heq]; exact Nat.not_lt.mpr t.isLt.le),
            ite_eq_left (by rw [hlt2]; exact Nat.lt_succ_self _)]
          ring
        · rw [ite_eq_right (fun ⟨h0, _⟩ => by rw [heq2] at h0; exact t.isLt.ne' h0),
            ite_eq_right (by rw [heq]; exact Nat.not_lt.mpr t.isLt.le),
            ite_eq_right (by rw [heq2]; exact Nat.not_lt.mpr (Nat.succ_le_of_lt t.isLt))]
    have hst0_x : st0.x = t.val := rfl
    have hst0_go : st0.go = 1 := rfl
    have hst0_tl : st0.touchedLen = 0 := rfl
    simp only [growPot_eq] at hc_bw
    rw [hpot₁.trans hfh_pot, hst0_tl, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
      hst0_go, hst0_x] at hc_bw
    rw [hst0_go, hst0_x] at hsum_bw_id
    simp only [true_and] at hsum_bw_id hc_bw
    omega
  refine ⟨hsafe_all, hv_all, hst_all ▸ hfr₄.trans (hfr₃.trans hfr₂), hst_all ▸ hwf₄,
    fun a hfp h1 h2 h3 h4 => by rw [hst_all]; exact hmod_s4 a hfp h1 h2 h3 h4,
    by rw [hst_all]; exact hinv₄, by rw [hst_all]; exact hemp₄, by rw [hst_all]; exact hpot₄',
    ⟨selIdxs0 ++ selTree_bw, by rw [hst_all, hres_all]; exact hphase_next⟩,
    by rw [hst_all]; exact hcost_all⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

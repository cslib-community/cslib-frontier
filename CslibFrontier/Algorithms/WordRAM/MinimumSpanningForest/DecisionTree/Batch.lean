/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Eval
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Computability.WordRAM.Realization.ArrayOps
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg

/-!
# Batch Component Compaction, Decision-Tree Evaluation, and Lifting on the Word RAM

Implements `evalDecisionTreeBatchProg` as a step toward Theorem 5.8 of [PettieRamachandran2002]
(`Section 4.1, p. 23; Section 5.1, pp. 25–26`, Corollary 5.6 and Theorem 5.8, `#8624`) for
batch-evaluating a precomputed optimal MSF decision tree stored in `HoldsDTTable` across `k`
uncompacted simple components `C_0..C_{k-1}` in `Fin n` (each touching at most `r0` vertices),
using a single `O(n)`-initialized shared `vertMap`, a single shared `r0.choose 2`-word `slotMap`
scratch buffer (`evalDecisionTreeWithSlotMapProg`), and `O(v_i)` rollback via `activeVerts` to
return a compacted `GraphSlice` in `O(n + ∑ m_i + ∑ optDepth C_i + k)` total time and
`O(n + r0 + r0.choose 2 + ∑ m_i)` words.

Reuses `evalDecisionTreeWithSlotMapProg` / `evalDecisionTreeWithSlotMapProg_spec` from
`DecisionTree.Eval`, `compactVertices_isSimple` / `compactVertices_isMinSpanningForest` from
`GraphOps.Components`, `fillConstProg` / `fillConstProg_spec` from `ArrayOps`,
`word_enc_structure` encodings, and `Memory.FramedTriple` + `iterate_potential_spec`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DTBatchArgs`: input arguments (`tableBase`,
  `r0`, `numVerts`, `numComps`, `compMetaBase`) encoded via `word_enc_structure`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeBatchProg`: Word-RAM batch
  compaction, evaluation, reset, and lifting program returning a `GraphSlice`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeBatchProgSafe`: native
  word-width safety predicate for `evalDecisionTreeBatchProg`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_evalDecisionTreeBatchProg`: uniform
  `Realizes .exact` certificate with `work = 0`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.evalDecisionTreeBatchProg_spec`:
  `Memory.FramedTriple` specification producing `IsMinSpanningForest` sublists `Fs` packed
  contiguously as a `GraphSlice` preserving all cells below `s.frontier`, within space
  `n + r0 + r0.choose 2 + 9 * ∑ m_i` and time `≤ 47 * (n + ∑ m_i + ∑ optDepth C_i + k + 1)`.

## References

* [PettieRamachandran2002] Seth Pettie and Vijaya Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*, Journal of the ACM 49(1), 16–34, 2002.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Batch Programs, `word_enc_structure` Encodings, and Realization -/

private structure DTMapVertArgs where
  vertMap : ℕ
  activeVerts : ℕ
  n : ℕ
  u : ℕ
  vCount : ℕ
  deriving DecidableEq

private word_enc_structure encDTMapVertArgs : DTMapVertArgs where
  vertMap : wordWords,
  activeVerts : wordWords,
  n : wordWords,
  u : wordWords,
  vCount : wordWords

private instance : WordEncoding DTMapVertArgs := ⟨5, encDTMapVertArgs⟩

private structure DTWriteCompArgs where
  edgeBase : ℕ
  compEdges : ℕ
  idx : ℕ
  mu : ℕ
  mv : ℕ
  deriving DecidableEq

private word_enc_structure encDTWriteCompArgs : DTWriteCompArgs where
  edgeBase : wordWords,
  compEdges : wordWords,
  idx : wordWords,
  mu : wordWords,
  mv : wordWords

private instance : WordEncoding DTWriteCompArgs := ⟨5, encDTWriteCompArgs⟩

private structure DTCompactEnv where
  edgeBase : ℕ
  compEdges : ℕ
  vertMap : ℕ
  activeVerts : ℕ
  n : ℕ
  deriving DecidableEq

private word_enc_structure encDTCompactEnv : DTCompactEnv where
  edgeBase : wordWords,
  compEdges : wordWords,
  vertMap : wordWords,
  activeVerts : wordWords,
  n : wordWords

private instance : WordEncoding DTCompactEnv := ⟨5, encDTCompactEnv⟩

private structure DTResetEnv where
  activeVerts : ℕ
  vertMap : ℕ
  n : ℕ
  deriving DecidableEq

private word_enc_structure encDTResetEnv : DTResetEnv where
  activeVerts : wordWords,
  vertMap : wordWords,
  n : wordWords

private instance : WordEncoding DTResetEnv := ⟨3, encDTResetEnv⟩

private structure DTLiftEnv where
  outBase : ℕ
  activeVerts : ℕ
  deriving DecidableEq

private word_enc_structure encDTLiftEnv : DTLiftEnv where
  outBase : wordWords,
  activeVerts : wordWords

private instance : WordEncoding DTLiftEnv := ⟨2, encDTLiftEnv⟩

private structure DTLiftEvalArgs where
  tableBase : ℕ
  vCount : ℕ
  m : ℕ
  compEdges : ℕ
  outBase : ℕ
  activeVerts : ℕ
  slotMap : ℕ
  compIdx : ℕ
  outCnt : ℕ
  deriving DecidableEq

private word_enc_structure encDTLiftEvalArgs : DTLiftEvalArgs where
  tableBase : wordWords,
  vCount : wordWords,
  m : wordWords,
  compEdges : wordWords,
  outBase : wordWords,
  activeVerts : wordWords,
  slotMap : wordWords,
  compIdx : wordWords,
  outCnt : wordWords

private instance : WordEncoding DTLiftEvalArgs := ⟨9, encDTLiftEvalArgs⟩

private structure DTBatchEnv where
  tableBase : ℕ
  numVerts : ℕ
  compMetaBase : ℕ
  vertMap : ℕ
  activeVerts : ℕ
  slotMap : ℕ
  outBase : ℕ
  deriving DecidableEq

private word_enc_structure encDTBatchEnv : DTBatchEnv where
  tableBase : wordWords,
  numVerts : wordWords,
  compMetaBase : wordWords,
  vertMap : wordWords,
  activeVerts : wordWords,
  slotMap : wordWords,
  outBase : wordWords

private instance : WordEncoding DTBatchEnv := ⟨7, encDTBatchEnv⟩

/-- Input arguments for `evalDecisionTreeBatchProg`. -/
structure DTBatchArgs where
  /-- Base of precomputed DT lookup table. -/
  tableBase : ℕ
  /-- Vertex-count upper bound `r0` per component. -/
  r0 : ℕ
  /-- Outer vertex count `n`. -/
  numVerts : ℕ
  /-- Number of components `k`. -/
  numComps : ℕ
  /-- Base of stride-2 component metadata `(edgeBase_i, m_i)`. -/
  compMetaBase : ℕ
  deriving DecidableEq

/-- Faithful five-word encoding of `DTBatchArgs` as
`[tableBase, r0, numVerts, numComps, compMetaBase]`. -/
word_enc_structure encDTBatchArgs : DTBatchArgs where
  tableBase : wordWords,
  r0 : wordWords,
  numVerts : wordWords,
  numComps : wordWords,
  compMetaBase : wordWords

/-- Registered `WordEncoding` instance for `DTBatchArgs`. -/
instance : WordEncoding DTBatchArgs := ⟨5, encDTBatchArgs⟩

private def dtBatchSumStep (x : ℕ × ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let compMetaBase := Prod.fst x
  let st := Prod.snd x
  let m ← Memory.read (compMetaBase + 2 * Prod.fst st + 1)
  pure (Prod.fst st + 1, Prod.snd st + m)

private def dtBatchSumStepSafe (w : ℕ) (x : ℕ × ℕ × ℕ) (s : Memory.State) : Prop :=
  let compMetaBase := Prod.fst x
  let st := Prod.snd x
  Fits w 16 ∧ Fits w (Prod.fst st + 1) ∧
  Fits w (Prod.snd st + s.mem (compMetaBase + 2 * Prod.fst st + 1)) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtBatchSumStep x))

private theorem fits_at {k w v : ℕ} {enc : Fin k → ℕ}
    (i : Fin k) (hw : ∀ j, Fits w (enc j)) (hv : enc i = v := by rfl) : Fits w v :=
  hv ▸ hw i

private theorem realizes_dtBatchSumStep : Realizes .exact
    dtBatchSumStep
    (appendWords (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    dtBatchSumStepSafe (fun _ _ => 0) := by
  unfold dtBatchSumStep
  realize
  all_goals
    obtain ⟨h16, hidx, hacc, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [dtBatchSumStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid] at hv
    have hw_idx : Fits w (Prod.fst (Prod.snd d)) := fits_at 1 hwords
    have hw_acc : Fits w (Prod.snd (Prod.snd d)) := fits_at 2 hwords
    fits

private def dtFillConst (p : ℕ × ℕ) : Memory.Prog Unit :=
  fillConstProg (Prod.fst p) (Prod.snd p) (Prod.snd p)

private theorem realizes_dtFillConst : Realizes .exact
    dtFillConst WordEncoding.encode WordEncoding.encode
    (fun w p s => Fits w 16 ∧ Prod.fst p + Prod.snd p ≤ s.frontier) (fun _ _ => 0) := by
  unfold dtFillConst
  realize [realizes_fillConstProg]
  obtain ⟨_, hb⟩ := h
  exact hb

private def dtMapVertex (d : DTMapVertArgs) : Memory.Prog (ℕ × ℕ) := do
  let cur ← Memory.read (d.vertMap + d.u)
  if cur = d.n then
    Memory.write (d.vertMap + d.u) d.vCount
    Memory.write (d.activeVerts + d.vCount) d.u
    pure (d.vCount, d.vCount + 1)
  else
    pure (cur, d.vCount)

private def dtMapVertexSafe (w : ℕ) (d : DTMapVertArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.vCount + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtMapVertex d))

private theorem realizes_dtMapVertex : Realizes .exact
    dtMapVertex (WordEncoding.encode (α := DTMapVertArgs)) (WordEncoding.encode (α := ℕ × ℕ))
    dtMapVertexSafe (fun _ _ => 0) := by
  unfold dtMapVertex
  realize
  all_goals
    obtain ⟨h16, hv1, hv⟩ := h
    have hfront := hmem.frontier_fits
    have hw_vm : Fits w d.vertMap := fits_at 0 hwords
    have hw_av : Fits w d.activeVerts := fits_at 1 hwords
    have hw_n : Fits w d.n := fits_at 2 hwords
    have hw_u : Fits w d.u := fits_at 3 hwords
    have hw_vc : Fits w d.vCount := fits_at 4 hwords
    dsimp only [dtMapVertex, StateTransitionSpec.clientHistory] at hv
    by_cases h0 : s.mem (d.vertMap + d.u) = d.n
    · simp only [h0, ↓reduceIte, StateTransitionSpec.runClient_lift_bind',
        StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
        Memory.write, Memory.step_read, Memory.step_write, Memory.valid] at hv
      fits
    · simp only [h0, ↓reduceIte, StateTransitionSpec.runClient_lift_bind',
        StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
        Memory.step_read, Memory.valid] at hv
      fits

private def dtWriteCompEdge (d : DTWriteCompArgs) : Memory.Prog Unit := do
  let wt ← Memory.read (d.edgeBase + 4 * d.idx + 2)
  let eid ← Memory.read (d.edgeBase + 4 * d.idx + 3)
  Memory.write (d.compEdges + 4 * d.idx) d.mu
  Memory.write (d.compEdges + 4 * d.idx + 1) d.mv
  Memory.write (d.compEdges + 4 * d.idx + 2) wt
  Memory.write (d.compEdges + 4 * d.idx + 3) eid

private def dtWriteCompEdgeSafe (w : ℕ) (d : DTWriteCompArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtWriteCompEdge d))

private theorem realizes_dtWriteCompEdge : Realizes .exact
    dtWriteCompEdge (WordEncoding.encode (α := DTWriteCompArgs)) (WordEncoding.encode (α := Unit))
    dtWriteCompEdgeSafe (fun _ _ => 0) := by
  unfold dtWriteCompEdge
  realize
  all_goals
    obtain ⟨h16, hv⟩ := h
    have hfront := hmem.frontier_fits
    have hw_eb : Fits w d.edgeBase := fits_at 0 hwords
    have hw_ce : Fits w d.compEdges := fits_at 1 hwords
    have hw_idx : Fits w d.idx := fits_at 2 hwords
    have hw_mu : Fits w d.mu := fits_at 3 hwords
    have hw_mv : Fits w d.mv := fits_at 4 hwords
    dsimp only [dtWriteCompEdge, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.step_write,
      Memory.valid] at hv
    fits

private def dtCompactEdgeStep (x : DTCompactEnv × ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let env := Prod.fst x
  let st := Prod.snd x
  let u ← Memory.read (env.edgeBase + 4 * Prod.fst st)
  let v ← Memory.read (env.edgeBase + 4 * Prod.fst st + 1)
  let ru ← dtMapVertex ⟨env.vertMap, env.activeVerts, env.n, u, Prod.snd st⟩
  let rv ← dtMapVertex ⟨env.vertMap, env.activeVerts, env.n, v, Prod.snd ru⟩
  dtWriteCompEdge ⟨env.edgeBase, env.compEdges, Prod.fst st, Prod.fst ru, Prod.fst rv⟩
  pure (Prod.fst st + 1, Prod.snd rv)

private def dtCompactEdgeStepSafe (w : ℕ) (x : DTCompactEnv × ℕ × ℕ)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  let u := s.mem (env.edgeBase + 4 * Prod.fst st)
  let v := s.mem (env.edgeBase + 4 * Prod.fst st + 1)
  let a1 : DTMapVertArgs := ⟨env.vertMap, env.activeVerts, env.n, u, Prod.snd st⟩
  let ru := (Memory.spec 0).clientResult s (dtMapVertex a1)
  let s1 := (Memory.spec 0).clientState s (dtMapVertex a1)
  let a2 : DTMapVertArgs := ⟨env.vertMap, env.activeVerts, env.n, v, Prod.snd ru⟩
  let rv := (Memory.spec 0).clientResult s1 (dtMapVertex a2)
  let s2 := (Memory.spec 0).clientState s1 (dtMapVertex a2)
  Fits w 16 ∧ Fits w (Prod.fst st + 1) ∧
  env.edgeBase + 4 * Prod.fst st + 1 < s.frontier ∧
  dtMapVertexSafe w a1 s ∧
  dtMapVertexSafe w a2 s1 ∧
  dtWriteCompEdgeSafe w
    ⟨env.edgeBase, env.compEdges, Prod.fst st, Prod.fst ru, Prod.fst rv⟩ s2

private theorem realizes_dtCompactEdgeStep : Realizes .exact
    dtCompactEdgeStep
    (appendWords (WordEncoding.encode (α := DTCompactEnv))
      (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    dtCompactEdgeStepSafe (fun _ _ => 0) := by
  unfold dtCompactEdgeStep
  realize [realizes_dtMapVertex, realizes_dtWriteCompEdge]
  all_goals
    obtain ⟨h16, hidx, hlt, hm1, hm2, hwr⟩ := h
    have hfront := hmem.frontier_fits
    have := fits_at 0 hwords; have := fits_at 1 hwords; have := fits_at 2 hwords
    have := fits_at 3 hwords; have := fits_at 4 hwords; have := fits_at 5 hwords
    have := fits_at 6 hwords
    first
    | exact hm1
    | exact hm2
    | exact hwr
    | fits

private def dtResetVertMapStep (x : DTResetEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let idx := Prod.snd x
  let u ← Memory.read (env.activeVerts + idx)
  Memory.write (env.vertMap + u) env.n
  pure (idx + 1)

private def dtResetVertMapStepSafe (w : ℕ) (x : DTResetEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (Prod.snd x + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtResetVertMapStep x))

private theorem realizes_dtResetVertMapStep : Realizes .exact
    dtResetVertMapStep
    (appendWords (WordEncoding.encode (α := DTResetEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ))
    dtResetVertMapStepSafe (fun _ _ => 0) := by
  unfold dtResetVertMapStep
  realize
  all_goals
    obtain ⟨h16, hidx, hv⟩ := h
    have hfront := hmem.frontier_fits
    have := fits_at 0 hwords; have := fits_at 1 hwords; have := fits_at 2 hwords
    dsimp only [dtResetVertMapStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid] at hv
    fits

private def dtLiftOutStep (x : DTLiftEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let idx := Prod.snd x
  let mu ← Memory.read (env.outBase + 4 * idx)
  let mv ← Memory.read (env.outBase + 4 * idx + 1)
  let u ← Memory.read (env.activeVerts + mu)
  let v ← Memory.read (env.activeVerts + mv)
  Memory.write (env.outBase + 4 * idx) u
  Memory.write (env.outBase + 4 * idx + 1) v
  pure (idx + 1)

private def dtLiftOutStepSafe (w : ℕ) (x : DTLiftEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (Prod.snd x + 1) ∧
  (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dtLiftOutStep x))

private theorem realizes_dtLiftOutStep : Realizes .exact
    dtLiftOutStep
    (appendWords (WordEncoding.encode (α := DTLiftEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ))
    dtLiftOutStepSafe (fun _ _ => 0) := by
  unfold dtLiftOutStep
  realize
  all_goals
    obtain ⟨h16, hidx, hv⟩ := h
    have hfront := hmem.frontier_fits
    have := fits_at 0 hwords; have := fits_at 1 hwords
    dsimp only [dtLiftOutStep, StateTransitionSpec.clientHistory] at hv
    simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.valid] at hv
    fits

private def dtBatchEvalAndLift (d : DTLiftEvalArgs) : Memory.Prog (ℕ × ℕ) := do
  let delta ← evalDecisionTreeWithSlotMapProg
    ⟨d.tableBase, d.vCount, d.m, d.compEdges, d.outBase + 4 * d.outCnt, d.slotMap⟩
  let _ ← iterate dtLiftOutStep ⟨d.outBase + 4 * d.outCnt, d.activeVerts⟩ delta 0
  pure (d.compIdx + 1, d.outCnt + delta)

private def dtBatchEvalAndLiftSafe (w : ℕ) (d : DTLiftEvalArgs) (s : Memory.State) : Prop :=
  let q : DTScratchQuery :=
    ⟨d.tableBase, d.vCount, d.m, d.compEdges, d.outBase + 4 * d.outCnt, d.slotMap⟩
  let delta := (Memory.spec 0).clientResult s (evalDecisionTreeWithSlotMapProg q)
  let s1 := (Memory.spec 0).clientState s (evalDecisionTreeWithSlotMapProg q)
  Fits w 16 ∧ Fits w (d.outBase + 4 * d.outCnt) ∧
  Fits w (d.compIdx + 1) ∧ Fits w (d.outCnt + delta) ∧
  evalDecisionTreeWithSlotMapProgSafe w q s ∧
  iterationSafe dtLiftOutStep dtLiftOutStepSafe w
    ⟨d.outBase + 4 * d.outCnt, d.activeVerts⟩ delta 0 s1

private theorem realizes_dtBatchEvalAndLift : Realizes .exact
    dtBatchEvalAndLift (WordEncoding.encode (α := DTLiftEvalArgs))
    (WordEncoding.encode (α := ℕ × ℕ))
    dtBatchEvalAndLiftSafe (fun _ _ => 0) := by
  unfold dtBatchEvalAndLift
  realize [realizes_evalDecisionTreeWithSlotMapProg, realizes_dtLiftOutStep]
  all_goals
    obtain ⟨h16, hob, hci, hoc, hdt, hlift⟩ := h
    have hfront := hmem.frontier_fits
    have hw_tb : Fits w d.tableBase := fits_at 0 hwords
    have hw_vc : Fits w d.vCount := fits_at 1 hwords
    have hw_m : Fits w d.m := fits_at 2 hwords
    have hw_ce : Fits w d.compEdges := fits_at 3 hwords
    have hw_ob : Fits w d.outBase := fits_at 4 hwords
    have hw_av : Fits w d.activeVerts := fits_at 5 hwords
    have hw_sm : Fits w d.slotMap := fits_at 6 hwords
    have hw_ci : Fits w d.compIdx := fits_at 7 hwords
    have hw_oc : Fits w d.outCnt := fits_at 8 hwords
    first
    | exact hdt
    | (refine iterationSafe_imp hlift (fun _ => rfl) ?_
       intro _ _ hs
       exact ⟨⟨hob, h16.of_le (by omega)⟩, hs⟩)
    | fits

private def dtBatchCompStep (x : DTBatchEnv × ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let env := Prod.fst x
  let st := Prod.snd x
  let edgeBase ← Memory.read (env.compMetaBase + 2 * Prod.fst st)
  let m ← Memory.read (env.compMetaBase + 2 * Prod.fst st + 1)
  let compEdges ← Memory.allocDirty (4 * m)
  let cr ← iterate dtCompactEdgeStep
    ⟨edgeBase, compEdges, env.vertMap, env.activeVerts, env.numVerts⟩ m (0, 0)
  let _ ← iterate dtResetVertMapStep
    ⟨env.activeVerts, env.vertMap, env.numVerts⟩ (Prod.snd cr) 0
  dtBatchEvalAndLift ⟨env.tableBase, Prod.snd cr, m, compEdges, env.outBase, env.activeVerts,
    env.slotMap, Prod.fst st, Prod.snd st⟩

private def dtBatchCompStepSafe (w : ℕ) (x : DTBatchEnv × ℕ × ℕ)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  let edgeBase := s.mem (env.compMetaBase + 2 * Prod.fst st)
  let m := s.mem (env.compMetaBase + 2 * Prod.fst st + 1)
  let compEdges := s.frontier
  let s1 : Memory.State := ⟨s.mem, s.frontier + 4 * m⟩
  let cEnv : DTCompactEnv := ⟨edgeBase, compEdges, env.vertMap, env.activeVerts, env.numVerts⟩
  let cr := (Memory.spec 0).clientResult s1 (iterate dtCompactEdgeStep cEnv m (0, 0))
  let s2 := (Memory.spec 0).clientState s1 (iterate dtCompactEdgeStep cEnv m (0, 0))
  let rEnv : DTResetEnv := ⟨env.activeVerts, env.vertMap, env.numVerts⟩
  let s3 := (Memory.spec 0).clientState s2 (iterate dtResetVertMapStep rEnv (Prod.snd cr) 0)
  Fits w 16 ∧
  env.compMetaBase + 2 * Prod.fst st + 1 < s.frontier ∧
  Fits w (4 * m) ∧ Fits w (s.frontier + 4 * m) ∧
  iterationSafe dtCompactEdgeStep dtCompactEdgeStepSafe w cEnv m (0, 0) s1 ∧
  iterationSafe dtResetVertMapStep dtResetVertMapStepSafe w rEnv (Prod.snd cr) 0 s2 ∧
  dtBatchEvalAndLiftSafe w ⟨env.tableBase, Prod.snd cr, m, compEdges, env.outBase, env.activeVerts,
    env.slotMap, Prod.fst st, Prod.snd st⟩ s3

private theorem realizes_dtBatchCompStep : Realizes .exact
    dtBatchCompStep
    (appendWords (WordEncoding.encode (α := DTBatchEnv))
      (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    dtBatchCompStepSafe (fun _ _ => 0) := by
  unfold dtBatchCompStep
  realize [realizes_dtCompactEdgeStep, realizes_dtResetVertMapStep, realizes_dtBatchEvalAndLift]
  all_goals
    obtain ⟨h16, hlt, h4m, hs1, hc, hr, hev⟩ := h
    have hfront := hmem.frontier_fits
    have := fits_at 0 hwords; have := fits_at 1 hwords; have := fits_at 2 hwords
    have := fits_at 3 hwords; have := fits_at 4 hwords; have := fits_at 5 hwords
    have := fits_at 6 hwords; have := fits_at 7 hwords; have := fits_at 8 hwords
    first
    | exact iterationSafe_imp hc (fun _ => rfl) (fun _ _ hs => hs)
    | exact iterationSafe_imp hr (fun _ => rfl) (fun _ _ hs => hs)
    | exact hev
    | fits

/-- Batch evaluates the precomputed optimal decision tree on `k` uncompacted simple components
`C_0..C_{k-1}` in `Fin n` (each with `≤ r0` active vertices), sharing one `O(n)`-initialized
`vertMap` reset via `activeVerts` and one `r0.choose 2`-word `slotMap`, returning a `GraphSlice`
in `O(n + ∑ m_i + ∑ optDepth C_i + k)` time. -/
def evalDecisionTreeBatchProg (d : DTBatchArgs) : Memory.Prog GraphSlice := do
  let sumRes ← iterate dtBatchSumStep d.compMetaBase d.numComps (0, 0)
  let outBase ← Memory.allocDirty (4 * Prod.snd sumRes)
  let vertMap ← Memory.allocDirty d.numVerts
  let _ ← dtFillConst (vertMap, d.numVerts)
  let activeVerts ← Memory.allocDirty d.r0
  let slotMap ← Memory.allocDirty (if d.r0 = 0 then 0 else d.r0 * (d.r0 - 1) / 2)
  let res ← iterate dtBatchCompStep
    ⟨d.tableBase, d.numVerts, d.compMetaBase, vertMap, activeVerts, slotMap, outBase⟩
    d.numComps (0, 0)
  pure ⟨d.numVerts, Prod.snd res, outBase⟩

/-- Native safety domain for `evalDecisionTreeBatchProg`. -/
def evalDecisionTreeBatchProgSafe (w : ℕ) (d : DTBatchArgs) (s : Memory.State) : Prop :=
  let sumRes :=
    (Memory.spec 0).clientResult s (iterate dtBatchSumStep d.compMetaBase d.numComps (0, 0))
  let s1 := (Memory.spec 0).clientState s (iterate dtBatchSumStep d.compMetaBase d.numComps (0, 0))
  let outBase := s1.frontier
  let vertMap := outBase + 4 * Prod.snd sumRes
  let s2 : Memory.State := ⟨s1.mem, vertMap + d.numVerts⟩
  let s3 := (Memory.spec 0).clientState s2 (dtFillConst (vertMap, d.numVerts))
  let activeVerts := s3.frontier
  let slotMap := activeVerts + d.r0
  let maxE := if d.r0 = 0 then 0 else d.r0 * (d.r0 - 1) / 2
  let s5 : Memory.State := ⟨s3.mem, slotMap + maxE⟩
  Fits w 16 ∧ Fits w (4 * Prod.snd sumRes) ∧ Fits w (d.r0 * (d.r0 - 1)) ∧ Fits w maxE ∧
  Fits w (s1.frontier + 4 * Prod.snd sumRes) ∧ Fits w (vertMap + d.numVerts) ∧
  Fits w (s3.frontier + d.r0) ∧ Fits w (slotMap + maxE) ∧
  iterationSafe dtBatchSumStep dtBatchSumStepSafe w d.compMetaBase d.numComps (0, 0) s ∧
  iterationSafe dtBatchCompStep dtBatchCompStepSafe w
    ⟨d.tableBase, d.numVerts, d.compMetaBase, vertMap, activeVerts, slotMap, outBase⟩
    d.numComps (0, 0) s5

/-- Uniform `Realizes .exact` certificate for `evalDecisionTreeBatchProg` with `work = 0`. -/
theorem realizes_evalDecisionTreeBatchProg : Realizes .exact
    evalDecisionTreeBatchProg (WordEncoding.encode (α := DTBatchArgs))
    (WordEncoding.encode (α := GraphSlice))
    evalDecisionTreeBatchProgSafe (fun _ _ => 0) := by
  unfold evalDecisionTreeBatchProg
  realize [realizes_dtBatchSumStep, realizes_dtFillConst, realizes_dtBatchCompStep]
  all_goals
    obtain ⟨h16, h4m, hmul, hme, hs1, hvm, hs3, hs5, hsum, hcomp⟩ := h
    have := fits_at 0 hwords; have := fits_at 1 hwords; have := fits_at 2 hwords
    have := fits_at 3 hwords; have := fits_at 4 hwords
    have hfront := hmem.frontier_fits
    first
    | exact iterationSafe_imp hsum (fun _ => rfl) (fun _ _ hs => hs)
    | exact h16
    | exact le_rfl
    | exact iterationSafe_imp hcomp (fun _ => rfl) (fun _ _ hs => hs)
    | decide
    | omega
    | fits

/-! ## Section 3: Loop Specifications and Batch Evaluation Correctness -/

private theorem iterate_dtBatchSumStep_spec {w compMetaBase n : ℕ}
    {Cs : List (List (IndexedEdge n))} {edgeBases : List ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hmeta : ∀ i (hi : i < Cs.length),
      s.mem (compMetaBase + 2 * i) = edgeBases[i]?.getD 0 ∧
      s.mem (compMetaBase + 2 * i + 1) = Cs[i].length)
    (hmeta_lt : compMetaBase + 2 * Cs.length ≤ s.frontier)
    (hfit : Fits w (Cs.length + (Cs.map List.length).sum + 1)) :
    let prog := iterate dtBatchSumStep compMetaBase Cs.length (0, 0)
    iterationSafe dtBatchSumStep dtBatchSumStepSafe w compMetaBase Cs.length (0, 0) s ∧
    Memory.FramedTriple w s prog Cs.length ∅ fun res s' =>
      s' = s ∧ res.1 = Cs.length ∧ res.2 = (Cs.map List.length).sum := by
  let inv (k : ℕ) (st : ℕ × ℕ) (t : Memory.State) : Prop :=
    st.1 = k ∧ st.2 = ((Cs.take k).map List.length).sum ∧ t = s
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step dtBatchSumStep dtBatchSumStepSafe w
    compMetaBase 1 Cs.length inv ∅ (fun k hk st t ⟨hidx, hacc, ht⟩ => by
      subst hidx ht
      have hm_val : t.mem (compMetaBase + 2 * st.1 + 1) = Cs[st.1].length :=
        (hmeta st.1 hk).2
      have htake : (Cs.take (st.1 + 1)).map List.length =
          (Cs.take st.1).map List.length ++ [Cs[st.1].length] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]
        simp only [Option.toList_some, List.map_append, List.map_singleton]
      have hsum_le : ((Cs.take st.1).map List.length).sum + Cs[st.1].length ≤
          (Cs.map List.length).sum :=
        (by rw [htake, List.sum_append, List.sum_singleton]; omega :
          ((Cs.take (st.1 + 1)).map List.length).sum ≤ (Cs.map List.length).sum → _)
          (((List.take_sublist (st.1 + 1) Cs).map List.length).sum_le_sum
            fun _ _ => Nat.zero_le _)
      refine ⟨fun hv => ⟨h16, hfit.of_le (by dsimp only; omega),
        hfit.of_le (by dsimp only; rw [hm_val, hacc]; omega), hv⟩, ?_⟩
      dsimp only [dtBatchSumStep]
      refine Memory.FramedTriple.read_bind (by omega) ?_
      rw [hm_val]
      exact Memory.FramedTriple.pure (c := 0)
        ⟨rfl, by rw [htake, List.sum_append, List.sum_singleton, hacc], rfl⟩)
    (0, 0) s ⟨rfl, rfl, rfl⟩
  exact ⟨hsafe, hft.mono (by rw [one_mul]) fun _ _ ⟨hidx, hacc, ht⟩ =>
    ⟨ht, hidx, by simpa using hacc⟩⟩

private def VertMapInv (vertMap activeVerts n : ℕ) (active : List ℕ) (mem : ℕ → ℕ) : Prop :=
  active.Nodup ∧
  (∀ x ∈ active, x < n) ∧
  (∀ t (ht : t < active.length), mem (activeVerts + t) = active[t]) ∧
  (∀ x < n, ∀ t (ht : t < active.length), active[t] = x → mem (vertMap + x) = t) ∧
  (∀ x < n, x ∉ active → mem (vertMap + x) = n)

private theorem VertMapInv.length_le {vertMap activeVerts n : ℕ} {active : List ℕ}
    {mem : ℕ → ℕ} (hinv : VertMapInv vertMap activeVerts n active mem) :
    active.length ≤ n := by
  have hcard := Finset.card_le_card (α := ℕ) (s := active.toFinset) (t := Finset.range n)
    fun x hx => Finset.mem_range.mpr (hinv.2.1 x (List.mem_toFinset.mp hx))
  rw [List.toFinset_card_of_nodup hinv.1, Finset.card_range] at hcard
  exact hcard

private def MapVertPost (w vertMap activeVerts n r0 u : ℕ) (active : List ℕ)
    (V : Finset (Fin n)) (s : Memory.State) (res : ℕ × ℕ) (s' : Memory.State) : Prop :=
  s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
  (∀ a, ¬(vertMap ≤ a ∧ a < vertMap + n) →
    ¬(activeVerts ≤ a ∧ a < activeVerts + r0) → s'.mem a = s.mem a) ∧
  (∀ j < active.length, s'.mem (activeVerts + j) = s.mem (activeVerts + j)) ∧
  active.length ≤ Prod.snd res ∧ Prod.snd res ≤ active.length + 1 ∧
  ∃ active' : List ℕ, active'.length = Prod.snd res ∧ active'.length ≤ r0 ∧
    ∃ (hlt : Prod.fst res < active'.length), active'[Prod.fst res]'hlt = u ∧
      VertMapInv vertMap activeVerts n active' s'.mem ∧
      (∀ x ∈ active', ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ V)

private theorem dtMapVertex_spec {w vertMap activeVerts n r0 u : ℕ}
    {active : List ℕ} {V : Finset (Fin n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hu : u < n) (huV : (⟨u, hu⟩ : Fin n) ∈ V) (hV_card : V.card ≤ r0)
    (hactive_V : ∀ x ∈ active, ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ V)
    (hinv : VertMapInv vertMap activeVerts n active s.mem)
    (hvm_lt : vertMap + n ≤ s.frontier) (hav_lt : activeVerts + r0 ≤ s.frontier)
    (hdisj_va : vertMap + n ≤ activeVerts ∨ activeVerts + r0 ≤ vertMap) :
    let args : DTMapVertArgs := ⟨vertMap, activeVerts, n, u, active.length⟩
    let S : Set ℕ := Set.Ico vertMap (vertMap + n) ∪ Set.Ico activeVerts (activeVerts + r0)
    dtMapVertexSafe w args s ∧
    Memory.FramedTriple w s (dtMapVertex args) 3 S
      (MapVertPost w vertMap activeVerts n r0 u active V s) := by
  have h1_r0 : 1 ≤ r0 := Nat.le_trans (Finset.card_pos.mpr ⟨_, huV⟩) hV_card
  have hlen_le_r0 : active.length ≤ r0 := by
    let activeFin : List (Fin n) := active.pmap (fun x h => ⟨x, h⟩) hinv.2.1
    have hsub : activeFin.toFinset ⊆ V := fun y hy => by
      rw [List.mem_toFinset, List.mem_pmap] at hy
      obtain ⟨x, hx, rfl⟩ := hy; exact (hactive_V x hx).2
    calc active.length = activeFin.length := List.length_pmap.symm
      _ = activeFin.toFinset.card := (List.toFinset_card_of_nodup
        (List.Nodup.pmap (fun _ _ _ _ h => congrArg Fin.val h) hinv.1)).symm
      _ ≤ V.card := Finset.card_le_card hsub
      _ ≤ r0 := hV_card
  have hlen_le_n : active.length ≤ n := hinv.length_le
  let args : DTMapVertArgs := ⟨vertMap, activeVerts, n, u, active.length⟩
  let S : Set ℕ := Set.Ico vertMap (vertMap + n) ∪ Set.Ico activeVerts (activeVerts + r0)
  have hftCore : Memory.FramedTriple w s (dtMapVertex args) 3 S fun res s' =>
      s'.frontier = s.frontier ∧ True ∧
      (∀ a, ¬(vertMap ≤ a ∧ a < vertMap + n) →
        ¬(activeVerts ≤ a ∧ a < activeVerts + r0) → s'.mem a = s.mem a) ∧
      (∀ j < active.length, s'.mem (activeVerts + j) = s.mem (activeVerts + j)) ∧
      active.length ≤ Prod.snd res ∧ Prod.snd res ≤ active.length + 1 ∧
      ∃ active' : List ℕ, active'.length = Prod.snd res ∧ active'.length ≤ r0 ∧
        ∃ (hlt : Prod.fst res < active'.length), active'[Prod.fst res]'hlt = u ∧
          VertMapInv vertMap activeVerts n active' s'.mem ∧
          (∀ x ∈ active', ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ V) := by
    dsimp only [dtMapVertex, args]
    refine Memory.FramedTriple.read_bind (by omega) ?_
    by_cases hu_mem : u ∈ active
    · obtain ⟨t, ht, htu⟩ := List.mem_iff_getElem.mp hu_mem
      have hcur : s.mem (vertMap + u) = t := hinv.2.2.2.1 u hu t ht htu
      rw [hcur]
      refine (Memory.FramedTriple.ite (fun h => absurd h (by omega)) fun _ =>
        Memory.FramedTriple.pure (c := 0) ⟨rfl, trivial, fun _ _ _ => rfl, fun _ _ => rfl,
          le_rfl, Nat.le_succ _, active, rfl, hlen_le_r0, ht, htu, hinv, hactive_V⟩).mono
        (by omega) fun _ _ h => h
    · have hcur : s.mem (vertMap + u) = n := hinv.2.2.2.2 u hu hu_mem
      let active' := active ++ [u]
      have hnd' : active'.Nodup := List.nodup_append.mpr ⟨hinv.1, List.nodup_singleton u,
        fun a ha b hb hab => by
          simp only [List.mem_singleton] at hb; subst hb hab; exact hu_mem ha⟩
      have hlt_n' : ∀ x ∈ active', x < n := fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hinv.2.1 x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact hu
      have hV' : ∀ x ∈ active', ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ V := fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hactive_V x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact ⟨hu, huV⟩
      have hlen_lt_V : active.length < V.card := by
        let activeFin : List (Fin n) := active'.pmap (fun x h => ⟨x, h⟩) hlt_n'
        have hnd_fin : activeFin.Nodup :=
          List.Nodup.pmap (fun _ _ _ _ h => congrArg Fin.val h) hnd'
        have hsub : activeFin.toFinset ⊆ V := fun y hy => by
          rw [List.mem_toFinset, List.mem_pmap] at hy
          obtain ⟨x, hx, rfl⟩ := hy; exact (hV' x hx).2
        have hlen := Finset.card_le_card hsub
        rw [List.toFinset_card_of_nodup hnd_fin, List.length_pmap, List.length_append,
          List.length_singleton] at hlen; omega
      have hlen_lt_r0 : active.length < r0 := lt_of_lt_of_le hlen_lt_V hV_card
      have hlen' : active'.length = active.length + 1 := by simp [active']
      refine Memory.FramedTriple.ite (fun _ => ?_) (fun hne => absurd hcur hne)
      refine Memory.FramedTriple.write_bind_of_mem (by omega)
        (hwf.frontier_fits.of_le (by omega))
        (Or.inl (by simp only [Set.mem_Ico]; omega)) ?_
      refine Memory.FramedTriple.write_bind_of_mem (by dsimp only; omega)
        (hwf.frontier_fits.of_le (by omega))
        (Or.inr (by simp only [Set.mem_Ico]; omega)) ?_
      refine Memory.FramedTriple.pure (c := 0)
        ⟨rfl, trivial, fun a hna1 hna2 => ?_, fun j hj => ?_, Nat.le_succ _, le_rfl, active',
          hlen', by rw [hlen']; exact hlen_lt_r0, by omega, by simp [active'],
          ⟨hnd', hlt_n', fun t ht => ?_, fun x hx t ht htx => ?_, fun x hx hnot => ?_⟩, hV'⟩
      · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · dsimp only; rw [Function.update_of_ne (by omega),
          Function.update_of_ne (by rcases hdisj_va with h | h <;> omega)]
      · dsimp only; rw [hlen'] at ht; by_cases htl : t = active.length
        · subst htl; simp [active', Function.update_self]
        · have ht_old : t < active.length := by omega
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by
            rcases hdisj_va with h | h <;> omega), hinv.2.2.1 t ht_old, List.getElem_append_left]
      · dsimp only; rw [hlen'] at ht
        rw [Function.update_of_ne (by rcases hdisj_va with h | h <;> omega)]
        by_cases htl : t = active.length
        · subst htl; obtain rfl : x = u := by simpa [active'] using htx.symm
          exact Function.update_self ..
        · have ht_old : t < active.length := by omega
          rw [List.getElem_append_left ht_old] at htx
          have hxu : x ≠ u := fun heq => hu_mem (heq ▸ htx ▸ List.getElem_mem ht_old)
          rw [Function.update_of_ne (by omega)]; exact hinv.2.2.2.1 x hx t ht_old htx
      · dsimp only
        have hxu : x ≠ u := fun heq => hnot (by simp [active', heq])
        rw [Function.update_of_ne (by rcases hdisj_va with h | h <;> omega),
          Function.update_of_ne (by omega)]
        exact hinv.2.2.2.2 x hx fun ha => hnot (by simp [active', ha])
  have hft : Memory.FramedTriple w s (dtMapVertex args) 3 S
      (MapVertPost w vertMap activeVerts n r0 u active V s) :=
    (hftCore.wellFormed hwf).mono le_rfl fun _ _ ⟨⟨h1, _, h3⟩, hwf'⟩ => ⟨h1, hwf', h3⟩
  have hv1_fit : Fits w (active.length + 1) :=
    hwf.frontier_fits.of_le (by rcases hdisj_va with h | h <;> omega)
  exact ⟨⟨h16, hv1_fit, (framedTriple_iff_realization.mp hft).1⟩, hft⟩

private theorem dtWriteCompEdge_spec {w n : ℕ} {edgeBase compEdges idx mu mv : ℕ}
    {C : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hmu : Fits w mu) (hmv : Fits w mv)
    (hidx : idx < C.length)
    (hin : HoldsIndexedEdges edgeBase C s.mem)
    (hin_lt : edgeBase + 4 * C.length ≤ s.frontier)
    (hcomp_lt : compEdges + 4 * C.length ≤ s.frontier) :
    let args : DTWriteCompArgs := ⟨edgeBase, compEdges, idx, mu, mv⟩
    let S : Set ℕ := Set.Ico (compEdges + 4 * idx) (compEdges + 4 * idx + 4)
    dtWriteCompEdgeSafe w args s ∧
    Memory.FramedTriple w s (dtWriteCompEdge args) 6 S fun _ s' =>
      s'.frontier = s.frontier ∧
      Memory.WellFormed w s' ∧
      s'.mem (compEdges + 4 * idx) = mu ∧
      s'.mem (compEdges + 4 * idx + 1) = mv ∧
      s'.mem (compEdges + 4 * idx + 2) = C[idx].weight ∧
      s'.mem (compEdges + 4 * idx + 3) = C[idx].id := by
  let args : DTWriteCompArgs := ⟨edgeBase, compEdges, idx, mu, mv⟩
  let S : Set ℕ := Set.Ico (compEdges + 4 * idx) (compEdges + 4 * idx + 4)
  obtain ⟨_, _, hw, hid⟩ := hin idx hidx
  have hwt_fit := hwf.mem_fits (edgeBase + 4 * idx + 2)
  have hid_fit := hwf.mem_fits (edgeBase + 4 * idx + 3)
  have hftCore : Memory.FramedTriple w s (dtWriteCompEdge args) 6 S fun _ s' =>
      s'.frontier = s.frontier ∧ True ∧
      s'.mem (compEdges + 4 * idx) = mu ∧ s'.mem (compEdges + 4 * idx + 1) = mv ∧
      s'.mem (compEdges + 4 * idx + 2) = C[idx].weight ∧
      s'.mem (compEdges + 4 * idx + 3) = C[idx].id := by
    dsimp only [dtWriteCompEdge, args]
    refine Memory.FramedTriple.read_bind (by omega)
      (Memory.FramedTriple.read_bind (by omega) ?_)
    refine Memory.FramedTriple.write_bind_of_mem (by omega) hmu
      (by simp only [S, Set.mem_Ico]; omega)
      (Memory.FramedTriple.write_bind_of_mem (by dsimp; omega) hmv
        (by simp only [S, Set.mem_Ico]; omega)
      (Memory.FramedTriple.write_bind_of_mem (by dsimp; omega) hwt_fit
        (by simp only [S, Set.mem_Ico]; omega)
      (Memory.FramedTriple.write_bind_of_mem (by dsimp; omega) hid_fit
        (by simp only [S, Set.mem_Ico]; omega)
        (Memory.FramedTriple.pure (c := 0) ⟨rfl, trivial,
          by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self],
          by dsimp; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self],
          by dsimp; rw [Function.update_of_ne (by omega), Function.update_self, hw],
          by dsimp; rw [Function.update_self, hid]⟩))))
  have hft : Memory.FramedTriple w s (dtWriteCompEdge args) 6 S fun _ s' =>
      s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      s'.mem (compEdges + 4 * idx) = mu ∧ s'.mem (compEdges + 4 * idx + 1) = mv ∧
      s'.mem (compEdges + 4 * idx + 2) = C[idx].weight ∧
      s'.mem (compEdges + 4 * idx + 3) = C[idx].id :=
    (hftCore.wellFormed hwf).mono le_rfl fun _ _ ⟨⟨h1, _, h3⟩, hwf'⟩ => ⟨h1, hwf', h3⟩
  exact ⟨⟨h16, (framedTriple_iff_realization.mp hft).1⟩, hft⟩

private theorem iterate_dtCompactEdgeStep_spec
    {w n r0 edgeBase compEdges vertMap activeVerts : ℕ}
    {C : List (IndexedEdge n)} {V : Finset (Fin n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hV_card : V.card ≤ r0)
    (hCV : ∀ e ∈ C, e.u ∈ V ∧ e.v ∈ V)
    (hin : HoldsIndexedEdges edgeBase C s.mem)
    (hin_lt : edgeBase + 4 * C.length ≤ s.frontier)
    (hcomp_lt : compEdges + 4 * C.length ≤ s.frontier)
    (hvm_lt : vertMap + n ≤ s.frontier)
    (hav_lt : activeVerts + r0 ≤ s.frontier)
    (hdisj_ci : edgeBase + 4 * C.length ≤ compEdges ∨ compEdges + 4 * C.length ≤ edgeBase)
    (hdisj_cv : vertMap + n ≤ compEdges ∨ compEdges + 4 * C.length ≤ vertMap)
    (hdisj_ca : activeVerts + r0 ≤ compEdges ∨ compEdges + 4 * C.length ≤ activeVerts)
    (hdisj_va : vertMap + n ≤ activeVerts ∨ activeVerts + r0 ≤ vertMap)
    (hdisj_vi : edgeBase + 4 * C.length ≤ vertMap ∨ vertMap + n ≤ edgeBase)
    (hdisj_ai : edgeBase + 4 * C.length ≤ activeVerts ∨ activeVerts + r0 ≤ edgeBase)
    (hvm_init : ∀ x < n, s.mem (vertMap + x) = n) :
    let env : DTCompactEnv := ⟨edgeBase, compEdges, vertMap, activeVerts, n⟩
    let prog := iterate dtCompactEdgeStep env C.length (0, 0)
    let S : Set ℕ :=
      Set.Ico compEdges (compEdges + 4 * C.length) ∪
        (Set.Ico vertMap (vertMap + n) ∪ Set.Ico activeVerts (activeVerts + r0))
    iterationSafe dtCompactEdgeStep dtCompactEdgeStepSafe w env C.length (0, 0) s ∧
    Memory.FramedTriple w s prog (14 * C.length) S fun res s' =>
      s'.frontier = s.frontier ∧
      Memory.WellFormed w s' ∧
      res.1 = C.length ∧
      res.2 ≤ r0 ∧
      res.2 ≤ 2 * C.length ∧
      ∃ (active : List ℕ) (lift : Fin res.2 → Fin n) (C' : List (IndexedEdge res.2))
          (hact_len : active.length = res.2),
        Function.Injective lift ∧
        (∀ t (ht : t < res.2), (lift ⟨t, ht⟩).val = active[t]'(hact_len.symm ▸ ht)) ∧
        VertMapInv vertMap activeVerts n active s'.mem ∧
        C'.length = C.length ∧
        HoldsIndexedEdges compEdges C' s'.mem ∧
        C'.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = C := by
  let env : DTCompactEnv := ⟨edgeBase, compEdges, vertMap, activeVerts, n⟩
  let S_va : Set ℕ := Set.Ico vertMap (vertMap + n) ∪ Set.Ico activeVerts (activeVerts + r0)
  let S : Set ℕ := Set.Ico compEdges (compEdges + 4 * C.length) ∪ S_va
  let EdgeCompInv (k : ℕ) (active : List ℕ) (mem : ℕ → ℕ) : Prop :=
    ∀ j (hj : j < k) (hjC : j < C.length),
      ∃ mu mv, ∃ (hmu : mu < active.length) (hmv : mv < active.length),
        active[mu]'hmu = C[j].u.val ∧ active[mv]'hmv = C[j].v.val ∧
        mem (compEdges + 4 * j) = mu ∧ mem (compEdges + 4 * j + 1) = mv ∧
        mem (compEdges + 4 * j + 2) = C[j].weight ∧ mem (compEdges + 4 * j + 3) = C[j].id
  let inv (k : ℕ) (st : ℕ × ℕ) (t : Memory.State) : Prop :=
    st.1 = k ∧ st.2 ≤ 2 * k ∧ st.2 ≤ r0 ∧ t.frontier = s.frontier ∧
    Memory.WellFormed w t ∧ HoldsIndexedEdges edgeBase C t.mem ∧
    ∃ active : List ℕ, active.length = st.2 ∧
      VertMapInv vertMap activeVerts n active t.mem ∧
      (∀ x ∈ active, ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ V) ∧
      EdgeCompInv k active t.mem
  have hstep : ∀ k < C.length, ∀ st t, inv k st t →
      ((Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtCompactEdgeStep (env, st))) →
        dtCompactEdgeStepSafe w (env, st) t) ∧
      Memory.FramedTriple w t (dtCompactEdgeStep (env, st)) 14 S (inv (k + 1)) := by
    intro k hk st t ⟨hidx, hacc2, haccr0, htfr, hwt, hin_t, active, hact_len, hvm_t, hactV,
      hedges⟩
    subst hidx
    obtain ⟨hu, hv, _, _⟩ := hin_t st.1 hk
    obtain ⟨huV, hvV⟩ := hCV C[st.1] (List.getElem_mem hk)
    let u := C[st.1].u.val; let v := C[st.1].v.val
    have map_step : ∀ {z : ℕ} (hz : z < n) (hzV : (⟨z, hz⟩ : Fin n) ∈ V) {act0 : List ℕ}
        {t0 : Memory.State} (ht0_fr : t0.frontier = s.frontier) (hwt0 : Memory.WellFormed w t0)
        (hin0 : HoldsIndexedEdges edgeBase C t0.mem)
        (hvm0 : VertMapInv vertMap activeVerts n act0 t0.mem)
        (hact0V : ∀ x ∈ act0, ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ V)
        (hed0 : EdgeCompInv st.1 act0 t0.mem),
        let az : DTMapVertArgs := ⟨vertMap, activeVerts, n, z, act0.length⟩
        let rz := (Memory.spec 0).clientResult t0 (dtMapVertex az)
        let tz := (Memory.spec 0).clientState t0 (dtMapVertex az)
        dtMapVertexSafe w az t0 ∧
        Memory.FramedTriple w t0 (dtMapVertex az) 3 S_va
          (MapVertPost w vertMap activeVerts n r0 z act0 V t0) ∧
        tz.frontier = s.frontier ∧ Memory.WellFormed w tz ∧ HoldsIndexedEdges edgeBase C tz.mem ∧
        (∀ j < act0.length, tz.mem (activeVerts + j) = t0.mem (activeVerts + j)) ∧
        act0.length ≤ rz.2 ∧ rz.2 ≤ act0.length + 1 ∧
        ∃ act' : List ℕ, act'.length = rz.2 ∧ act'.length ≤ r0 ∧
          (∃ hlt : rz.1 < act'.length, act'[rz.1]'hlt = z) ∧
          VertMapInv vertMap activeVerts n act' tz.mem ∧
          (∀ x ∈ act', ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ V) ∧
          EdgeCompInv st.1 act' tz.mem := by
      intro z hz hzV act0 t0 ht0_fr hwt0 hin0 hvm0 hact0V hed0
      obtain ⟨hsf, hft⟩ := @dtMapVertex_spec w vertMap activeVerts n r0 z act0 V t0 h16 hwt0
        hz hzV hV_card hact0V hvm0 (by omega) (by omega) hdisj_va
      obtain ⟨_, _, _, htz_fr, hwtz, hmodz, hpresz, hle, hub, act', hact'_len, hact'_r0, hlt,
        heq, hvmz, hactzV⟩ := framedTriple_iff_realization.mp hft
      refine ⟨hsf, hft, htz_fr.trans ht0_fr, hwtz, hin0.congr fun a _ _ => hmodz a
          (by rcases hdisj_vi with h | h <;> omega) (by rcases hdisj_ai with h | h <;> omega),
        hpresz, hle, hub, act', hact'_len, hact'_r0, ⟨hlt, heq⟩, hvmz, hactzV,
        fun j hj hjC => by
        obtain ⟨mu, mv, hmu, hmv, hmu_eq, hmv_eq, h0, h1, h2, h3⟩ := hed0 j hj hjC
        have hmc : ∀ q < 4, _ = t0.mem (compEdges + 4 * j + q) := fun q _ =>
          hmodz _ (by rcases hdisj_cv with h | h <;> omega)
            (by rcases hdisj_ca with h | h <;> omega)
        have ha_eq : ∀ q (hq : q < act0.length),
            act'[q]'(hq.trans_le (hact'_len ▸ hle)) = act0[q] := fun q hq => by
          rw [← hvmz.2.2.1 q (hq.trans_le (hact'_len ▸ hle)), hpresz q hq, hvm0.2.2.1 q hq]
        exact ⟨mu, mv, hmu.trans_le (hact'_len ▸ hle), hmv.trans_le (hact'_len ▸ hle),
          (ha_eq mu hmu).trans hmu_eq, (ha_eq mv hmv).trans hmv_eq, (hmc 0 (by omega)).trans h0,
          (hmc 1 (by omega)).trans h1, (hmc 2 (by omega)).trans h2, (hmc 3 (by omega)).trans h3⟩⟩
    let a1 : DTMapVertArgs := ⟨vertMap, activeVerts, n, u, active.length⟩
    obtain ⟨hsafe_1, hft_1, hs1_fr, hwf1, hin1, _, hlen1_le, hlen1_ub, act1, hact1_len, _,
      ⟨hmu_lt, hmu_eq⟩, hvm1, hact1V, hedges1⟩ :=
      map_step C[st.1].u.isLt huV htfr hwt hin_t hvm_t hactV hedges
    set ru := (Memory.spec 0).clientResult t (dtMapVertex a1)
    set s1 := (Memory.spec 0).clientState t (dtMapVertex a1)
    let a2 : DTMapVertArgs := ⟨vertMap, activeVerts, n, v, act1.length⟩
    obtain ⟨hsafe_2, hft_2, hs2_fr, hwf2, hin2, hpres2, hlen2_le, hlen2_ub, act2, hact2_len,
      hact2_r0, ⟨hmv_lt, hmv_eq⟩, hvm2, hact2V, hedges2⟩ :=
      map_step C[st.1].v.isLt hvV hs1_fr hwf1 hin1 hvm1 hact1V hedges1
    set rv := (Memory.spec 0).clientResult s1 (dtMapVertex a2)
    set s2 := (Memory.spec 0).clientState s1 (dtMapVertex a2)
    have hru_rfl : (Memory.spec 0).clientResult t (dtMapVertex a1) = ru := rfl
    have hs1_rfl : (Memory.spec 0).clientState t (dtMapVertex a1) = s1 := rfl
    have hrv_rfl : (Memory.spec 0).clientResult s1 (dtMapVertex a2) = rv := rfl
    have hs2_rfl : (Memory.spec 0).clientState s1 (dtMapVertex a2) = s2 := rfl
    have hmu_lt2 : ru.1 < act2.length := lt_of_lt_of_le hmu_lt (hact2_len ▸ hlen2_le)
    have hmu_eq2 : act2[ru.1]'hmu_lt2 = u := by
      rw [← hvm2.2.2.1 ru.1 hmu_lt2, hpres2 ru.1 (hact1_len.symm ▸ hmu_lt),
        hvm1.2.2.1 ru.1 hmu_lt, hmu_eq]
    have hmu_fit : Fits w ru.1 :=
      hwf.frontier_fits.of_le (by have := hmu_lt2; have := hvm2.length_le; omega)
    have hmv_lt' : rv.1 < act2.length := hmv_lt
    have hmv_fit : Fits w rv.1 :=
      hwf.frontier_fits.of_le (by have := hmv_lt'; have := hvm2.length_le; omega)
    obtain ⟨hsafe_w, hft_w⟩ := @dtWriteCompEdge_spec w n edgeBase compEdges st.1 ru.1 rv.1
      C s2 h16 hwf2 hmu_fit hmv_fit hk hin2 (by rw [hs2_fr]; omega) (by rw [hs2_fr]; omega)
    have hsafe : dtCompactEdgeStepSafe w (env, st) t := by
      dsimp only [dtCompactEdgeStepSafe, env]
      refine ⟨h16, hwt.frontier_fits.of_le (by omega), by omega,
        by rw [hu, ← hact_len]; exact hsafe_1, ?_, ?_⟩
      · rw [hu, hv, ← hact_len]; dsimp only [a1] at hru_rfl hs1_rfl
        rw [hru_rfl, hs1_rfl, ← hact1_len]; exact hsafe_2
      · rw [hu, hv, ← hact_len]; dsimp only [a1] at hru_rfl hs1_rfl
        rw [hru_rfl, hs1_rfl, ← hact1_len]; dsimp only [a2] at hrv_rfl hs2_rfl
        rw [hrv_rfl, hs2_rfl]; exact hsafe_w
    refine ⟨fun _ => hsafe, ?_⟩
    dsimp only [dtCompactEdgeStep, env]
    refine Memory.FramedTriple.read_bind (by omega) ?_
    refine Memory.FramedTriple.read_bind (by omega) ?_
    rw [hu, hv, ← hact_len]
    refine Memory.FramedTriple.mono (c := 3 + (3 + (6 + 0))) ?_ (by omega) fun _ _ h => h
    refine Memory.FramedTriple.bind_same
      (((framedTriple_with_realization hft_1).frame_mono Set.subset_union_right).mono le_rfl
        (by rintro _ _ ⟨rfl, rfl, _⟩; dsimp only [a1] at hru_rfl hs1_rfl
            rw [hru_rfl, hs1_rfl, ← hact1_len]
            refine Memory.FramedTriple.bind_same
              ((framedTriple_with_realization hft_2).frame_mono Set.subset_union_right |>.mono
                le_rfl (by
                  rintro _ _ ⟨rfl, rfl, _⟩; dsimp only [a2] at hrv_rfl hs2_rfl
                  rw [hrv_rfl, hs2_rfl]
                  refine Memory.FramedTriple.bind_same
                    ((framedTriple_with_realization hft_w).frame_mono
                      (fun a ha => Or.inl (by simp only [Set.mem_Ico] at ha ⊢; omega)) |>.mono
                      le_rfl fun _ s3 ⟨_, hs3_eq, hs3_fr, hwf3, hw0, hw1, hw2, hw3⟩ => ?_)
                  have hs2_fr' : s2.frontier = s.frontier := hs2_fr
                  have hmod_w : ∀ a < s.frontier, a ∉ Set.Ico (compEdges + 4 * st.1)
                      (compEdges + 4 * st.1 + 4) → s3.mem a = s2.mem a :=
                    fun a ha hna => (hs3_eq ▸
                      (framedTriple_iff_realization.mp hft_w).2.2.1).mem_eq_of_not_mem
                      (by rw [hs2_fr']; exact ha) hna
                  have hin3 : HoldsIndexedEdges edgeBase C s3.mem := hin2.congr fun a _ _ =>
                    hmod_w a (by omega)
                      (by simp only [Set.mem_Ico]; rcases hdisj_ci with h | h <;> omega)
                  have hvm3 : VertMapInv vertMap activeVerts n act2 s3.mem :=
                    ⟨hvm2.1, hvm2.2.1,
                      fun q hq => (hmod_w _ (by have := hvm2.length_le; omega)
                        (by simp only [Set.mem_Ico]; rcases hdisj_ca with h|h <;> omega)).trans
                        (hvm2.2.2.1 q hq),
                      fun x hx q hq hqx => (hmod_w _ (by omega)
                        (by simp only [Set.mem_Ico]; rcases hdisj_cv with h|h <;> omega)).trans
                        (hvm2.2.2.2.1 x hx q hq hqx),
                      fun x hx hnot => (hmod_w _ (by omega)
                        (by simp only [Set.mem_Ico]; rcases hdisj_cv with h|h <;> omega)).trans
                        (hvm2.2.2.2.2 x hx hnot)⟩
                  have hedges3 : EdgeCompInv (st.1 + 1) act2 s3.mem := fun j hj hjC => by
                    by_cases hj_cur : j = st.1
                    · subst hj_cur
                      exact ⟨ru.1, rv.1, hmu_lt2, hmv_lt, hmu_eq2, hmv_eq, hw0, hw1, hw2, hw3⟩
                    · obtain ⟨mu, mv, hmu, hmv, hmu_e, hmv_e, h0, h1, h2, h3⟩ :=
                        hedges2 j (by omega) hjC
                      have hm_w : ∀ q < 4, s3.mem (compEdges + 4 * j + q) =
                          s2.mem (compEdges + 4 * j + q) := fun q _ =>
                        hmod_w _ (by omega) (by simp only [Set.mem_Ico]; omega)
                      exact ⟨mu, mv, hmu, hmv, hmu_e, hmv_e, (hm_w 0 (by omega)).trans h0,
                        (hm_w 1 (by omega)).trans h1, (hm_w 2 (by omega)).trans h2,
                        (hm_w 3 (by omega)).trans h3⟩
                  have hact2_len' : act2.length = rv.2 := hact2_len
                  have h1u : act1.length ≤ active.length + 1 := hact1_len ▸ hlen1_ub
                  have h2u : act2.length ≤ act1.length + 1 := hact2_len ▸ hlen2_ub
                  rw [hact_len] at h1u
                  exact Memory.FramedTriple.pure (c := 0)
                    ⟨rfl, by rw [← hact2_len']; omega,
                      by rw [← hact2_len']; exact hact2_r0, hs3_fr.trans hs2_fr', hwf3, hin3,
                      act2, hact2_len, hvm3, hact2V, hedges3⟩))))
  have hvm_init_inv : VertMapInv vertMap activeVerts n [] s.mem :=
    ⟨List.nodup_nil, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ _ _ h => by simp at h, fun x hx _ => hvm_init x hx⟩
  obtain ⟨hsafe_end, hft_end⟩ := iterate_framedTriple_of_step dtCompactEdgeStep
    dtCompactEdgeStepSafe w env 14 C.length inv S hstep (0, 0) s
    ⟨rfl, Nat.zero_le _, Nat.zero_le _, rfl, hwf, hin, [], rfl, hvm_init_inv,
      fun _ h => by simp at h, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine ⟨hsafe_end, hft_end.mono le_rfl fun res s' ⟨hidx_end, hacc2_end, haccr0_end, hfr_end,
      hwf_end, _, active, hact_len, hvm_end, _, hedges_end⟩ => ?_⟩
  let lift : Fin res.2 → Fin n := fun t => ⟨active[t.val]'(by omega),
    hvm_end.2.1 _ (List.getElem_mem (by omega))⟩
  have hlift_inj : Function.Injective lift := fun t₁ t₂ h =>
    Fin.ext (hvm_end.1.getElem_inj_iff.mp (congrArg Fin.val h))
  let C' : List (IndexedEdge res.2) := (List.finRange C.length).map fun i =>
    let mu := s'.mem (compEdges + 4 * i.val); let mv := s'.mem (compEdges + 4 * i.val + 1)
    if h : mu < res.2 ∧ mv < res.2 then
      ⟨⟨mu, h.1⟩, ⟨mv, h.2⟩, C[i.val].weight, C[i.val].id⟩
    else ⟨⟨0, by obtain ⟨_, _, hmu, _⟩ := hedges_end i.val i.isLt i.isLt; omega⟩,
      ⟨0, by obtain ⟨_, _, hmu, _⟩ := hedges_end i.val i.isLt i.isLt; omega⟩,
      C[i.val].weight, C[i.val].id⟩
  have hC'_len : C'.length = C.length := by
    dsimp only [C']; rw [List.length_map, List.length_finRange]
  have hC'_get : ∀ i (hi : i < C.length), ∃ mu mv, ∃ (hmu : mu < res.2) (hmv : mv < res.2),
      C'[i]'(hC'_len.symm ▸ hi) = ⟨⟨mu, hmu⟩, ⟨mv, hmv⟩, C[i].weight, C[i].id⟩ ∧
      active[mu]'(hact_len.symm ▸ hmu) = C[i].u.val ∧
      active[mv]'(hact_len.symm ▸ hmv) = C[i].v.val ∧
      s'.mem (compEdges + 4 * i) = mu ∧ s'.mem (compEdges + 4 * i + 1) = mv ∧
      s'.mem (compEdges + 4 * i + 2) = C[i].weight ∧ s'.mem (compEdges + 4 * i + 3) = C[i].id :=
    fun i hi => by
    obtain ⟨mu, mv, hmu, hmv, hmu_eq, hmv_eq, hm0, hm1, hm2, hm3⟩ := hedges_end i hi hi
    refine ⟨mu, mv, hact_len ▸ hmu, hact_len ▸ hmv, ?_, hmu_eq, hmv_eq, hm0, hm1, hm2, hm3⟩
    dsimp only [C']; rw [List.getElem_map, List.getElem_finRange]; simp only [Fin.val_cast]
    split_ifs with h_if
    · congr 1 <;> exact Fin.ext (by assumption)
    · exact absurd ⟨by omega, by omega⟩ h_if
  have hC'_holds : HoldsIndexedEdges compEdges C' s'.mem := fun i hi => by
    obtain ⟨_, _, _, _, hc, _, _, hm0, hm1, hm2, hm3⟩ := hC'_get i (hC'_len ▸ hi)
    exact hc ▸ ⟨hm0, hm1, hm2, hm3⟩
  have hC'_map : C'.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = C := by
    refine List.ext_getElem (by rw [List.length_map, hC'_len]) fun i _ hi2 => ?_
    obtain ⟨mu, mv, hmu, hmv, hc, hmu_eq, hmv_eq, _, _, _, _⟩ := hC'_get i hi2
    have hu : lift ⟨mu, hmu⟩ = C[i].u := Fin.ext hmu_eq
    have hv : lift ⟨mv, hmv⟩ = C[i].v := Fin.ext hmv_eq
    rw [List.getElem_map, hc, hu, hv]
  exact ⟨hfr_end, hwf_end, hidx_end, haccr0_end, hacc2_end, active, lift, C', hact_len, hlift_inj,
    fun _ _ => rfl, hvm_end, hC'_len, hC'_holds, hC'_map⟩

private theorem iterate_dtResetVertMapStep_spec {w activeVerts vertMap n : ℕ}
    {active : List ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hinv : VertMapInv vertMap activeVerts n active s.mem)
    (hvm_lt : vertMap + n ≤ s.frontier)
    (hav_lt : activeVerts + active.length ≤ s.frontier)
    (hdisj : vertMap + n ≤ activeVerts ∨ activeVerts + active.length ≤ vertMap) :
    let env : DTResetEnv := ⟨activeVerts, vertMap, n⟩
    let prog := iterate dtResetVertMapStep env active.length 0
    iterationSafe dtResetVertMapStep dtResetVertMapStepSafe w env active.length 0 s ∧
    Memory.FramedTriple w s prog (2 * active.length) (Set.Ico vertMap (vertMap + n))
      fun _ s' =>
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ x < n, s'.mem (vertMap + x) = n := by
  let env : DTResetEnv := ⟨activeVerts, vertMap, n⟩
  let S : Set ℕ := Set.Ico vertMap (vertMap + n)
  let invCore (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    (∀ x < n, x ∉ active → t.mem (vertMap + x) = s.mem (vertMap + x)) ∧
    (∀ j < k, ∀ (hj : j < active.length), t.mem (vertMap + active[j]'hj) = n)
  let inv (k a : ℕ) (t : Memory.State) : Prop := invCore k a t ∧ Memory.WellFormed w t
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step dtResetVertMapStep dtResetVertMapStepSafe w
    env 2 active.length inv S (fun k hk a t ⟨⟨ha, htfr, ht_mod, hnot_act, hreset⟩, hwt⟩ => by
      subst ha
      have hu_eq : t.mem (activeVerts + a) = active[a]'hk :=
        (ht_mod _ (by simp only [S, Set.mem_Ico]; rcases hdisj with h | h <;> omega)).trans
          (hinv.2.2.1 a hk)
      have hu_lt : active[a]'hk < n := hinv.2.1 _ (List.getElem_mem hk)
      refine ⟨fun hv => ⟨h16, hwf.frontier_fits.of_le (by have := hinv.length_le; omega), hv⟩,
        Memory.FramedTriple.wellFormed hwt ?_⟩
      dsimp only [dtResetVertMapStep, env]; refine Memory.FramedTriple.read_bind (by omega) ?_
      rw [hu_eq]
      refine Memory.FramedTriple.write_bind_of_mem (by omega) (hwf.frontier_fits.of_le (by omega))
        (by simp [S]; omega) ?_
      refine Memory.FramedTriple.pure (c := 0) ⟨rfl, htfr,
        fun x hx => ?_, fun x hx hnot => ?_, fun j hj hj' => ?_⟩
      · dsimp only; rw [Function.update_of_ne (by simp only [S, Set.mem_Ico] at hx; omega)]
        exact ht_mod x hx
      · have hne : x ≠ active[a]'hk := fun heq => hnot (heq ▸ List.getElem_mem hk)
        dsimp only; rw [Function.update_of_ne (by omega)]; exact hnot_act x hx hnot
      · by_cases hja : j = a
        · subst hja; dsimp only; exact Function.update_self _ _ _
        · have hne : active[j]'hj' ≠ active[a]'hk := fun heq => hja (hinv.1.getElem_inj_iff.mp heq)
          dsimp only; rw [Function.update_of_ne (by omega)]; exact hreset j (by omega) hj')
    0 s ⟨⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩, hwf⟩
  refine ⟨hsafe, hft.mono le_rfl fun _ _ ⟨⟨_, hfr_end, _, hnot_end, hact_end⟩, hwf_end⟩ =>
    ⟨hfr_end, hwf_end, fun x hx => ?_⟩⟩
  by_cases hmem : x ∈ active
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem; exact hact_end j hj hj
  · exact (hnot_end x hx hmem).trans (hinv.2.2.2.2 x hx hmem)

private theorem iterate_dtLiftOutStep_spec {w n v activeVerts outBase : ℕ}
    (lift : Fin v → Fin n) (F' : List (IndexedEdge v)) {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hlift : ∀ t (ht : t < v), s.mem (activeVerts + t) = (lift ⟨t, ht⟩).val)
    (hav_lt : activeVerts + v ≤ s.frontier)
    (hout_lt : outBase + 4 * F'.length ≤ s.frontier)
    (hdisj : outBase + 4 * F'.length ≤ activeVerts ∨ activeVerts + v ≤ outBase)
    (hholds : HoldsIndexedEdges outBase F' s.mem) :
    let env : DTLiftEnv := ⟨outBase, activeVerts⟩
    let prog := iterate dtLiftOutStep env F'.length 0
    iterationSafe dtLiftOutStep dtLiftOutStepSafe w env F'.length 0 s ∧
    Memory.FramedTriple w s prog (6 * F'.length) (Set.Ico outBase (outBase + 4 * F'.length))
      fun _ s' =>
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase (F'.map fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩)
          s'.mem := by
  let env : DTLiftEnv := ⟨outBase, activeVerts⟩
  let S : Set ℕ := Set.Ico outBase (outBase + 4 * F'.length)
  let F_lifted : List (IndexedEdge n) := F'.map fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩
  let invCore (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    (∀ i (hi : i < k) (hiL : i < F_lifted.length),
      t.mem (outBase + 4 * i) = F_lifted[i].u.val ∧
      t.mem (outBase + 4 * i + 1) = F_lifted[i].v.val ∧
      t.mem (outBase + 4 * i + 2) = F_lifted[i].weight ∧
      t.mem (outBase + 4 * i + 3) = F_lifted[i].id) ∧
    (∀ i (hi : i < F'.length), k ≤ i →
      t.mem (outBase + 4 * i) = F'[i].u.val ∧
      t.mem (outBase + 4 * i + 1) = F'[i].v.val ∧
      t.mem (outBase + 4 * i + 2) = F'[i].weight ∧
      t.mem (outBase + 4 * i + 3) = F'[i].id)
  let inv (k a : ℕ) (t : Memory.State) : Prop := invCore k a t ∧ Memory.WellFormed w t
  obtain ⟨hsafe, hft⟩ := iterate_framedTriple_of_step dtLiftOutStep dtLiftOutStepSafe w env 6
    F'.length inv S (fun k hk a t ⟨⟨ha, htfr, ht_mod, hlifted, hunlifted⟩, hwt⟩ => by
      subst ha
      obtain ⟨hmu, hmv, hw, hid⟩ := hunlifted a hk le_rfl
      have hu_lt := F'[a].u.isLt; have hv_lt := F'[a].v.isLt
      have hav_mem : ∀ z (hz : z < v), t.mem (activeVerts + z) = (lift ⟨z, hz⟩).val :=
        fun z hz => (ht_mod _ (by simp only [S, Set.mem_Ico]
                                  rcases hdisj with h | h <;> omega)).trans (hlift z hz)
      have hfit_l : ∀ z (hz : z < v), Fits w (lift ⟨z, hz⟩).val := fun z hz => by
        have hmem := hwf.mem_fits (activeVerts + z); rwa [hlift z hz] at hmem
      refine ⟨fun hv => ⟨h16, hwf.frontier_fits.of_le (by omega), hv⟩,
        Memory.FramedTriple.wellFormed hwt ?_⟩
      dsimp only [dtLiftOutStep, env]
      refine Memory.FramedTriple.read_bind (by omega) (Memory.FramedTriple.read_bind (by omega)
        (Memory.FramedTriple.read_bind (by rw [hmu]; omega) (Memory.FramedTriple.read_bind
          (by rw [hmv]; omega) ?_)))
      rw [hmu, hmv, hav_mem _ hu_lt, hav_mem _ hv_lt]
      refine Memory.FramedTriple.write_bind_of_mem (by omega) (hfit_l _ hu_lt)
        (by simp only [S, Set.mem_Ico]; omega) (Memory.FramedTriple.write_bind_of_mem
        (by dsimp only; omega) (hfit_l _ hv_lt) (by simp only [S, Set.mem_Ico]; omega) ?_)
      let mem' := Function.update (Function.update t.mem (outBase + 4 * a) (lift F'[a].u).val)
        (outBase + 4 * a + 1) (lift F'[a].v).val
      have hother : ∀ i q, i ≠ a → q < 4 →
          mem' (outBase + 4 * i + q) = t.mem (outBase + 4 * i + q) := fun i q _ _ => by
        dsimp only [mem']; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      refine Memory.FramedTriple.pure (c := 0) ⟨rfl, htfr,
        fun x hx => by
          dsimp only; rw [Function.update_of_ne (by simp only [S, Set.mem_Ico] at hx; omega),
            Function.update_of_ne (by simp only [S, Set.mem_Ico] at hx; omega)]; exact ht_mod x hx,
        fun i hi hiL => by
          by_cases hia : i = a
          · subst hia; exact ⟨
              by dsimp [mem', F_lifted]; rw [Function.update_of_ne (by omega),
                Function.update_self]; simp,
              by dsimp [mem', F_lifted]; rw [Function.update_self]; simp,
              by dsimp [mem', F_lifted]; rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]; simp [hw],
              by dsimp [mem', F_lifted]; rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]; simp [hid]⟩
          · obtain ⟨h0, h1, h2, h3⟩ := hlifted i (by omega) hiL
            exact ⟨(hother i 0 hia (by omega)).trans h0, (hother i 1 hia (by omega)).trans h1,
              (hother i 2 hia (by omega)).trans h2, (hother i 3 hia (by omega)).trans h3⟩,
        fun i hi _ => by
          obtain ⟨h0, h1, h2, h3⟩ := hunlifted i hi (by omega)
          exact ⟨(hother i 0 (by omega) (by omega)).trans h0,
            (hother i 1 (by omega) (by omega)).trans h1,
            (hother i 2 (by omega) (by omega)).trans h2,
            (hother i 3 (by omega) (by omega)).trans h3⟩⟩)
    0 s ⟨⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      fun i hi _ => hholds i hi⟩, hwf⟩
  exact ⟨hsafe, hft.mono le_rfl fun _ _ ⟨⟨_, hfr_end, _, hlifted_end, _⟩, hwf_end⟩ =>
    ⟨hfr_end, hwf_end, fun i hi => hlifted_end i (by simpa [F_lifted] using hi) hi⟩⟩

private def BatchCompInv {w : ℕ} (d : DTBatchArgs)
    (Cs : List (List (IndexedEdge d.numVerts))) (s0 : Memory.State)
    (k : ℕ) (st : ℕ × ℕ) (t : Memory.State) : Prop :=
  let totalM := (Cs.map List.length).sum
  let sumMk := ((Cs.take k).map List.length).sum
  st.1 = k ∧
  t.frontier ≤ s0.frontier + 4 * totalM + d.numVerts + d.r0 + d.r0.choose 2 + 5 * sumMk ∧
  s0.frontier + 4 * totalM + d.numVerts + d.r0 + d.r0.choose 2 ≤ t.frontier ∧
  Memory.WellFormed w t ∧
  (∀ a < s0.frontier, t.mem a = s0.mem a) ∧
  (∀ x < d.numVerts, t.mem (s0.frontier + 4 * totalM + x) = d.numVerts) ∧
  ∃ Fs : List (List (IndexedEdge d.numVerts)),
    Fs.length = k ∧ Fs.flatten.length = st.2 ∧ st.2 ≤ sumMk ∧
    HoldsIndexedEdges s0.frontier Fs.flatten t.mem ∧
    ∀ i (_ : i < k) (hiC : i < Cs.length) (hiF : i < Fs.length),
      Fs[i].Subperm Cs[i] ∧
      IsMinSpanningForest (Cs[i].map IndexedEdge.toWeighted) (Fs[i].map IndexedEdge.toWeighted)

private theorem list_map_take_sum_add {α : Type*} (l : List α) (f : α → ℕ)
    {k : ℕ} (hk : k < l.length) :
    ((l.take (k + 1)).map f).sum = ((l.take k).map f).sum + f l[k] ∧
    ((l.take (k + 1)).map f).sum ≤ (l.map f).sum :=
  ⟨by rw [List.take_add_one, List.getElem?_eq_getElem hk]
      simp only [Option.toList_some, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton],
   ((List.take_sublist (k + 1) l).map f).sum_le_sum fun _ _ => Nat.zero_le _⟩

private theorem dtBatchCompStep_spec {w tableFrontier : ℕ}
    {d : DTBatchArgs} {Cs : List (List (IndexedEdge d.numVerts))} {edgeBases : List ℕ}
    {s0 : Memory.State} (h16 : Fits w 16) (heb_len : edgeBases.length = Cs.length)
    (hmeta : ∀ i (hi : i < Cs.length),
      s0.mem (d.compMetaBase + 2 * i) = edgeBases[i]'(heb_len.symm ▸ hi) ∧
      s0.mem (d.compMetaBase + 2 * i + 1) = Cs[i].length)
    (hmeta_lt : d.compMetaBase + 2 * Cs.length ≤ s0.frontier)
    (hin : ∀ i (hi : i < Cs.length),
      HoldsIndexedEdges (edgeBases[i]'(heb_len.symm ▸ hi)) Cs[i] s0.mem ∧
      edgeBases[i]'(heb_len.symm ▸ hi) + 4 * Cs[i].length ≤ s0.frontier)
    (hsimp : ∀ i (hi : i < Cs.length),
      IsSimple (edgeEnds (Cs[i].map IndexedEdge.toWeighted)))
    (hvr : ∀ i (hi : i < Cs.length),
      ∃ V : Finset (Fin d.numVerts), V.card ≤ d.r0 ∧ ∀ e ∈ Cs[i], e.u ∈ V ∧ e.v ∈ V)
    (htab : HoldsDTTable d.r0 d.tableBase s0.mem)
    (hbnd : DTTableInBounds d.r0 d.tableBase tableFrontier s0.mem)
    (htab_fr : tableFrontier ≤ s0.frontier)
    (hfit : Fits w (s0.frontier + d.numVerts + d.r0 + 2 * d.r0.choose 2 +
      9 * (Cs.map List.length).sum + 1))
    {k : ℕ} (hk : k < Cs.length) (st : ℕ × ℕ) (t : Memory.State)
    (hinv : BatchCompInv (w := w) d Cs s0 k st t) :
    let vertMap := s0.frontier + 4 * (Cs.map List.length).sum
    let slotMap := vertMap + d.numVerts + d.r0
    let batchEnv : DTBatchEnv :=
      ⟨d.tableBase, d.numVerts, d.compMetaBase, vertMap, vertMap + d.numVerts, slotMap, s0.frontier⟩
    let m := Cs[k].length
    let optD := optDepth (edgeEnds (Cs[k].map IndexedEdge.toWeighted))
    dtBatchCompStepSafe w (batchEnv, st) t ∧
    Memory.FramedTriple w t (dtBatchCompStep (batchEnv, st)) (45 * m + 15 * optD + 18)
      (Set.Ici s0.frontier) (BatchCompInv (w := w) d Cs s0 (k + 1)) := by
  obtain ⟨hk_eq, ht_fr_le, hbase_le, hwt, hlt_s, hvm_t, Fs, hFs_len, hflat_len, hacc_le,
    hflat_holds, hFs_msf⟩ := hinv
  subst hk_eq
  let vertMap := s0.frontier + 4 * (Cs.map List.length).sum
  let slotMap := vertMap + d.numVerts + d.r0
  let batchEnv : DTBatchEnv :=
    ⟨d.tableBase, d.numVerts, d.compMetaBase, vertMap, vertMap + d.numVerts, slotMap, s0.frontier⟩
  let m := Cs[st.1].length
  obtain ⟨hsumM_k1, hsumM_le⟩ := list_map_take_sum_add Cs List.length hk
  rw [hsumM_k1] at hsumM_le
  have hm_val : t.mem (d.compMetaBase + 2 * st.1 + 1) = m :=
    (hlt_s _ (by omega)).trans (hmeta st.1 hk).2
  have heb_val : t.mem (d.compMetaBase + 2 * st.1) = edgeBases[st.1]'(heb_len.symm ▸ hk) :=
    (hlt_s _ (by omega)).trans (hmeta st.1 hk).1
  let edgeBase := edgeBases[st.1]'(heb_len.symm ▸ hk)
  let compEdges := t.frontier; let t1 : Memory.State := ⟨t.mem, compEdges + 4 * m⟩
  have hfit_4m : Fits w (4 * m) := hfit.of_le (by omega)
  have hfit_t1 : Fits w (t.frontier + 4 * m) := hfit.of_le (by omega)
  have hwf_t1 : Memory.WellFormed w t1 := ⟨hfit_t1, fun a => hwt.mem_fits a⟩
  have hin_k_t1 : HoldsIndexedEdges edgeBase Cs[st.1] t1.mem :=
    (hin st.1 hk).1.congr fun a _ _ => hlt_s a (by have := (hin st.1 hk).2; omega)
  obtain ⟨V, hV_card, hCV⟩ := hvr st.1 hk
  obtain ⟨hsafe_c, hft_c⟩ := @iterate_dtCompactEdgeStep_spec w d.numVerts d.r0 edgeBase compEdges
    vertMap (vertMap + d.numVerts) Cs[st.1] V t1 h16 hwf_t1 hV_card hCV hin_k_t1
    (by have := (hin st.1 hk).2; dsimp [t1, compEdges]; omega) (by dsimp [t1, compEdges]; omega)
    (by dsimp [t1, compEdges, vertMap]; omega) (by dsimp [t1, compEdges, vertMap]; omega)
    (.inl (by have := (hin st.1 hk).2; dsimp [compEdges]; omega))
    (.inl (by dsimp [compEdges, vertMap]; omega)) (.inl (by dsimp [compEdges, vertMap]; omega))
    (.inl (by omega)) (.inl (by have := (hin st.1 hk).2; dsimp [vertMap]; omega))
    (.inl (by have := (hin st.1 hk).2; dsimp [vertMap]; omega)) hvm_t
  let progC := iterate dtCompactEdgeStep
    ⟨edgeBase, compEdges, vertMap, vertMap + d.numVerts, d.numVerts⟩ m (0, 0)
  obtain ⟨_, _, hmod_c, hq_c⟩ := (framedTriple_iff_realization (p := progC)).mp hft_c
  generalize hcr_def : (Memory.spec 0).clientResult t1 progC = cr at hmod_c hq_c
  generalize ht2_def : (Memory.spec 0).clientState t1 progC = t2 at hmod_c hq_c
  obtain ⟨hfr_c, hwf_t2, _, hcr_r0, hcr_2m, active, lift, C',
      hact_len, hlift_inj, hlift_val, hvm_t2, hC'_len, hC'_holds, hC'_map⟩ := hq_c
  dsimp only [progC] at hmod_c hcr_def ht2_def
  obtain ⟨hsafe_r, hft_r⟩ := @iterate_dtResetVertMapStep_spec w
    (vertMap + d.numVerts) vertMap d.numVerts active t2
    h16 hwf_t2 hvm_t2 (by rw [hfr_c]; dsimp only [t1, compEdges, vertMap]; omega)
    (by rw [hfr_c]; dsimp only [t1, compEdges, vertMap]; omega) (.inl (by omega))
  let progR := iterate dtResetVertMapStep
    ⟨vertMap + d.numVerts, vertMap, d.numVerts⟩ active.length 0
  obtain ⟨_, _, hmod_r, hq_r⟩ := (framedTriple_iff_realization (p := progR)).mp hft_r
  generalize ht3_def : (Memory.spec 0).clientState t2 progR = t3 at hmod_r hq_r
  obtain ⟨hfr_r, hwf_t3, hvm_t3⟩ := hq_r
  dsimp only [progR] at hmod_r ht3_def
  have ht3_mod_r : ∀ a < t2.frontier, ¬(vertMap ≤ a ∧ a < vertMap + d.numVerts) →
      t3.mem a = t2.mem a := fun a ha hna =>
    hmod_r.mem_eq_of_not_mem ha (by simp only [Set.mem_Ico, vertMap]; exact hna)
  have hpres_t3_lt : ∀ a < s0.frontier, t3.mem a = s0.mem a := fun a ha => by
    have h21 : t2.mem a = t1.mem a := hmod_c.mem_eq_of_not_mem
      (by dsimp only [t1, compEdges]; omega) (by simp [Set.mem_Ico, vertMap]; omega)
    exact (ht3_mod_r a (by rw [hfr_c]; dsimp only [t1, compEdges]; omega)
      (by dsimp only [vertMap]; omega)).trans (h21.trans (hlt_s a ha))
  have hC'_simp : IsSimple (edgeEnds (C'.map IndexedEdge.toWeighted)) :=
    compactVertices_isSimple hC'_map (hsimp st.1 hk)
  have hC'_holds_t3 : HoldsIndexedEdges compEdges C' t3.mem := hC'_holds.congr fun a _ _ =>
    ht3_mod_r a (by rw [hfr_c]; dsimp only [t1, compEdges]; omega)
      (by dsimp only [vertMap]; omega)
  have htab_t3 : HoldsDTTable d.r0 d.tableBase t3.mem :=
    htab.congr hbnd fun a ha => hpres_t3_lt a (by omega)
  have hbnd_t3 : DTTableInBounds d.r0 d.tableBase tableFrontier t3.mem :=
    hbnd.mono le_rfl fun a ha => hpres_t3_lt a (by omega)
  have hmax_cr : cr.2.choose 2 ≤ d.r0.choose 2 := by
    rw [Nat.choose_two_right, Nat.choose_two_right]
    exact Nat.div_le_div_right (Nat.mul_le_mul hcr_r0 (Nat.sub_le_sub_right hcr_r0 1))
  have h2c_cr : 2 * cr.2.choose 2 = cr.2 * (cr.2 - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self cr.2).two_dvd]
  have hfit_mul : Fits w (cr.2 * (cr.2 - 1)) := by
    rw [← h2c_cr]; exact hfit.of_le (by omega)
  have hfit_dt : Fits w (t3.frontier + C'.length) := by
    rw [hfr_r, hfr_c, hC'_len]
    exact hfit.of_le (by dsimp only [t1, compEdges, m] at ht_fr_le ⊢; omega)
  let dtQ : DTScratchQuery :=
    ⟨d.tableBase, cr.2, m, compEdges, s0.frontier + 4 * st.2, slotMap⟩
  have hev := @evalDecisionTreeWithSlotMapProg_spec w d.r0 tableFrontier dtQ C' t3 h16 hwf_t3
    hcr_r0 (by dsimp only [dtQ, m]; exact hC'_len.symm) hC'_simp hC'_holds_t3
    (by rw [hfr_r, hfr_c]; dsimp only [dtQ, t1, compEdges, m]; omega)
    (by rw [hfr_r, hfr_c]; dsimp only [dtQ, t1, compEdges]; omega)
    (.inr (by dsimp only [dtQ]; omega)) htab_t3 hbnd_t3
    (by rw [hfr_r, hfr_c]; dsimp only [t1, compEdges]; omega)
    (fun a ha => by dsimp only [dtQ]; omega)
    (by rw [hfr_r, hfr_c]; dsimp only [dtQ, t1, compEdges, slotMap, vertMap]; omega)
    (.inr (by dsimp only [dtQ, slotMap, vertMap, compEdges]; omega))
    (.inl (by dsimp only [dtQ, slotMap, vertMap]; omega))
    (fun a ha => by dsimp only [dtQ, slotMap, vertMap]; omega)
    hfit_mul hfit_dt
  obtain ⟨_, _, hmod_dt, hq_dt⟩ :=
    (framedTriple_iff_realization (p := evalDecisionTreeWithSlotMapProg dtQ)).mp hev
  generalize hdelta_def :
    (Memory.spec 0).clientResult t3 (evalDecisionTreeWithSlotMapProg dtQ) = delta at hmod_dt hq_dt
  generalize ht4_def :
    (Memory.spec 0).clientState t3 (evalDecisionTreeWithSlotMapProg dtQ) = t4 at hmod_dt hq_dt
  obtain ⟨hsafe_dt, hwf_t4, ht4_fr_le, hdelta_le, F', hF'_len, hF'_sub, hF'_holds, hF'_msf⟩ :=
    hq_dt
  have hopt_C'_eq : optDepth (edgeEnds (C'.map IndexedEdge.toWeighted)) =
      optDepth (edgeEnds (Cs[st.1].map IndexedEdge.toWeighted)) := by
    refine optDepth_reindex _ _ (Fin.castOrderIso (by simp [hC'_len])).toEquiv ⟨lift, hlift_inj⟩
      fun i => by
      have hi_c : i.val < C'.length := by simpa using i.isLt
      have hi_s : i.val < Cs[st.1].length := by simpa [← hC'_len] using i.isLt
      have hget := congrArg (fun l => l[i.val]?) hC'_map
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi_c, List.getElem?_eq_getElem hi_s,
        Option.map_some, Option.some.injEq] at hget
      change Sym2.map lift (edgeEnds (C'.map IndexedEdge.toWeighted) i) =
        edgeEnds (Cs[st.1].map IndexedEdge.toWeighted) ⟨i.val, by simpa using hi_s⟩
      simp only [edgeEnds, List.getElem_map, IndexedEdge.toWeighted, Sym2.map_mk]
      exact congrArg (fun e => s(e.u, e.v)) hget
  have hdt_pres_outside : ∀ a < t3.frontier,
      ¬(slotMap ≤ a ∧ a < slotMap + cr.2.choose 2) →
      ¬(s0.frontier + 4 * st.2 ≤ a ∧ a < s0.frontier + 4 * st.2 + 4 * C'.length) →
      t4.mem a = t3.mem a := fun a ha hns hna =>
    hmod_dt.mem_eq_of_not_mem ha (by
      simp only [dtQ, Set.mem_union, Set.mem_Ico]; rintro (h | h); exacts [hns h, hna h])
  have hlift_t4 : ∀ j (hj : j < cr.2), t4.mem (vertMap + d.numVerts + j) = (lift ⟨j, hj⟩).val :=
    fun j hj => by
      have hst_m : st.2 + C'.length ≤ (Cs.map List.length).sum := by rw [hC'_len]; omega
      rw [hdt_pres_outside _ (by rw [hfr_r, hfr_c]; dsimp only [t1, compEdges, vertMap]; omega)
        (by dsimp only [slotMap, vertMap]; omega) (by dsimp only [vertMap]; omega),
        ht3_mod_r _ (by rw [hfr_c]; dsimp [t1, compEdges]; omega)
        (by dsimp [vertMap]; omega), hvm_t2.2.2.1 j (hact_len.symm ▸ hj), hlift_val j hj]
  have hfl_le : F'.length ≤ m := hF'_sub.length_le.trans (by rw [hC'_len])
  obtain ⟨hsafe_l, hft_l⟩ := @iterate_dtLiftOutStep_spec w d.numVerts cr.2
    (vertMap + d.numVerts) (s0.frontier + 4 * st.2) lift F' t4 h16 hwf_t4 hlift_t4
    (by have := hmod_dt.1; rw [hfr_r, hfr_c] at this; dsimp only [t1, compEdges, vertMap] at this ⊢
        omega)
    (by have := hmod_dt.1; rw [hfr_r, hfr_c] at this; dsimp only [t1, compEdges] at this; omega)
    (.inl (by dsimp only [vertMap]; omega)) hF'_holds
  let progL := iterate dtLiftOutStep ⟨s0.frontier + 4 * st.2, vertMap + d.numVerts⟩ F'.length 0
  obtain ⟨_, _, hmod_l, hq_l⟩ := (framedTriple_iff_realization (p := progL)).mp hft_l
  generalize ht5_def : (Memory.spec 0).clientState t4 progL = t5 at hmod_l hq_l
  obtain ⟨hfr_l, hwf_t5, hF_lifted_holds⟩ := hq_l
  dsimp only [progL] at hmod_l ht5_def
  have hsafe_step : dtBatchCompStepSafe w (batchEnv, st) t := by
    have hst_m : st.2 + m ≤ (Cs.map List.length).sum := by omega
    have hdl : delta ≤ m := hdelta_le.trans hC'_len.le
    have hsafe_al : dtBatchEvalAndLiftSafe w ⟨d.tableBase, cr.2, m, compEdges, s0.frontier,
        vertMap + d.numVerts, slotMap, st.1, st.2⟩ t3 :=
      ⟨h16, hfit.of_le (by dsimp only; omega), hfit.of_le (by dsimp only; omega),
        hfit.of_le (by dsimp only; rw [hdelta_def]; omega), hsafe_dt,
        by rw [hdelta_def, ht4_def, ← hF'_len]; exact hsafe_l⟩
    dsimp only [dtBatchCompStepSafe, batchEnv]
    refine ⟨h16, by omega, hm_val ▸ hfit_4m, hm_val ▸ hfit_t1,
      by rw [heb_val, hm_val]; exact hsafe_c,
      by rw [heb_val, hm_val, hcr_def, ht2_def, ← hact_len]; exact hsafe_r,
      by rw [heb_val, hm_val, hcr_def, ht2_def, ← hact_len, ht3_def]; exact hact_len ▸ hsafe_al⟩
  let F_new : List (IndexedEdge d.numVerts) := F'.map fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩
  have hF_new_sub : F_new.Subperm Cs[st.1] := by
    rw [← hC'_map]; obtain ⟨l, hp, hs⟩ := hF'_sub
    exact ⟨l.map _, hp.map _, hs.map _⟩
  have hF_new_msf : IsMinSpanningForest (Cs[st.1].map IndexedEdge.toWeighted)
      (F_new.map IndexedEdge.toWeighted) := by
    have heq_f : F_new.map IndexedEdge.toWeighted =
        contractEdgeList lift (F'.map IndexedEdge.toWeighted) := by
      simp [F_new, contractEdgeList, contractEdge, List.map_map, Function.comp_def,
        IndexedEdge.toWeighted]
    exact heq_f ▸ compactVertices_isMinSpanningForest hlift_inj hC'_map hF'_msf
  have hpres_t5_t3 : ∀ a < t3.frontier,
      ¬(slotMap ≤ a ∧ a < slotMap + cr.2.choose 2) →
      ¬(s0.frontier + 4 * st.2 ≤ a ∧ a < s0.frontier + 4 * st.2 + 4 * m) →
      t5.mem a = t3.mem a := fun a ha hns hna =>
    (hmod_l.mem_eq_of_not_mem (ha.trans_le hmod_dt.1) (by simp [Set.mem_Ico]; omega)).trans
      (hdt_pres_outside a ha hns (by rw [hC'_len]; exact hna))
  have hflat_new : HoldsIndexedEdges s0.frontier (Fs ++ [F_new]).flatten t5.mem := by
    rw [List.flatten_append, List.flatten_singleton]; intro i hi; rw [List.length_append] at hi
    by_cases hil : i < Fs.flatten.length
    · rw [List.getElem_append_left hil]
      exact hflat_holds.congr (fun a _ _ => (hpres_t5_t3 a
        (by rw [hfr_r, hfr_c]; dsimp [t1, compEdges]; omega)
        (by dsimp [slotMap, vertMap]; omega) (by omega)).trans
        ((ht3_mod_r a (by rw [hfr_c]; dsimp [t1, compEdges]; omega)
          (by dsimp [vertMap]; omega)).trans (hmod_c.mem_eq_of_not_mem (by dsimp [t1]; omega)
          (by simp [Set.mem_Ico, vertMap]; omega)))) i hil
    · rw [List.getElem_append_right (by omega)]
      simpa only [hflat_len, show s0.frontier + 4 * st.2 + 4 * (i - st.2) =
        s0.frontier + 4 * i by omega, F_new] using
        hF_lifted_holds (i - Fs.flatten.length)
          (by simp only [F_new, List.length_map] at hi ⊢; omega)
  have hQ5 : BatchCompInv (w := w) d Cs s0 (st.1 + 1) (st.1 + 1, st.2 + delta) t5 := by
    refine ⟨rfl, ?_, ?_, hwf_t5,
      fun a ha => (hpres_t5_t3 a (by rw [hfr_r, hfr_c]; dsimp [t1, compEdges]; omega)
        (by dsimp [slotMap, vertMap]; omega) (by omega)).trans (hpres_t3_lt a ha),
      fun x hx => (hpres_t5_t3 (vertMap + x)
        (by rw [hfr_r, hfr_c]; dsimp [t1, compEdges, vertMap]; omega)
        (by dsimp [slotMap, vertMap]; omega) (by dsimp [vertMap]; omega)).trans (hvm_t3 x hx),
      Fs ++ [F_new], by simp [hFs_len], by simp [List.flatten_append, hflat_len, F_new, hF'_len],
      by dsimp only; rw [hsumM_k1]; omega, hflat_new, fun i hi hiC hiF => by
        rw [List.length_append, List.length_singleton] at hiF; by_cases hil : i < st.1
        · rw [List.getElem_append_left (hFs_len.symm ▸ hil)]
          exact hFs_msf i hil hiC (hFs_len.symm ▸ hil)
        · obtain rfl : i = st.1 := by omega
          rw [List.getElem_append_right (by omega)]
          simp only [hFs_len, Nat.sub_self, List.getElem_singleton]
          exact ⟨hF_new_sub, hF_new_msf⟩⟩
    · have hle := hfr_l.le.trans ht4_fr_le
      rw [hfr_r, hfr_c, hC'_len] at hle; dsimp only [t1, compEdges] at hle; rw [hsumM_k1]; omega
    · rw [hfr_l]; have := hmod_dt.1; rw [hfr_r, hfr_c] at this
      dsimp [t1, compEdges] at this; omega
  let S_all : Set ℕ := Set.Ici s0.frontier
  have hft_step : Memory.FramedTriple w t (dtBatchCompStep (batchEnv, st))
      (45 * m + 15 * optDepth (edgeEnds (Cs[st.1].map IndexedEdge.toWeighted)) + 18) S_all
      (BatchCompInv (w := w) d Cs s0 (st.1 + 1)) := by
    have hm_r' : active.length ≤ 2 * m := hact_len ▸ hcr_2m
    dsimp only [dtBatchCompStep, batchEnv]
    refine Memory.FramedTriple.mono
      (c := 14 * m + (2 * active.length +
        (15 * (C'.length + optDepth (edgeEnds (C'.map IndexedEdge.toWeighted)) + 1) +
          (6 * F'.length + 0))) + 1 + 1 + 1)
      ?_ (by rw [hopt_C'_eq, hC'_len]; omega) fun _ _ h => h
    refine Memory.FramedTriple.read_bind (by omega)
      (Memory.FramedTriple.read_bind (by omega) ?_)
    rw [heb_val, hm_val]; refine Memory.FramedTriple.allocDirty_bind hfit_t1 ?_
    refine Memory.FramedTriple.bind_same (((framedTriple_with_realization hft_c).frame_mono
      fun _ ha => by
        simp only [S_all, Set.mem_Ici, Set.mem_union, Set.mem_Ico] at ha ⊢
        dsimp only [t1, compEdges, vertMap] at *; rcases ha with h|h|h <;> omega).mono le_rfl
      fun _ _ ⟨hr, hs, _⟩ => by
      rw [hr, hs, hcr_def, ht2_def]
      rw [show iterate dtResetVertMapStep ⟨vertMap + d.numVerts, vertMap, d.numVerts⟩ cr.2 0 =
        iterate dtResetVertMapStep ⟨vertMap + d.numVerts, vertMap, d.numVerts⟩ active.length 0
        from by rw [hact_len]]
      refine Memory.FramedTriple.bind_same (((framedTriple_with_realization hft_r).frame_mono
        fun _ ha => by simp only [S_all, Set.mem_Ici, Set.mem_Ico] at ha ⊢; omega).mono le_rfl
        fun _ _ ⟨_, hs', _⟩ => by
        rw [hs', ht3_def]; dsimp only [dtBatchEvalAndLift]
        refine Memory.FramedTriple.bind_same (((framedTriple_with_realization hev).frame_mono
          fun _ ha => by
            simp only [S_all, Set.mem_Ici, dtQ, Set.mem_union, Set.mem_Ico,
              slotMap, vertMap] at ha ⊢
            rcases ha with h | h <;> omega).mono le_rfl fun _ _ ⟨hr', hs'', _⟩ => by
          rw [hr', hs'', hdelta_def, ht4_def, ← hF'_len]
          refine Memory.FramedTriple.bind_same (((framedTriple_with_realization hft_l).frame_mono
            fun _ ha => by simp only [S_all, Set.mem_Ici, Set.mem_Ico] at ha ⊢; omega).mono
            le_rfl fun _ _ ⟨_, hs''', _⟩ => by
            rw [hs''', ht5_def]; exact Memory.FramedTriple.pure (c := 0) (hF'_len.symm ▸ hQ5)))))
  exact ⟨hsafe_step, hft_step⟩

private theorem framedTriple_of_Ici {α : Type} {w : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {c c' : ℕ} {Q : α → Memory.State → Prop}
    (h : Memory.FramedTriple w s p c (Set.Ici s.frontier) Q) (hc : c ≤ c') :
    Memory.FramedTriple w s p c' ∅ Q :=
  Memory.Triple.mono h hc fun _ _ ⟨hm, hq⟩ =>
    ⟨⟨hm.1, fun a ha _ => hm.2 a ha (by simp only [Set.mem_Ici]; omega)⟩, hq⟩

/-- Framed specification of `evalDecisionTreeBatchProg`: batch-evaluates the precomputed optimal
decision tree over `k` uncompacted simple components `C_0..C_{k-1}` in `Fin n` (each with at
most `r0` active vertices), returning a `GraphSlice` `res` with `res.numVertices = d.numVerts`,
`HoldsIndexedEdges res.edgeBase Fs.flatten s'.mem`, `Fs.flatten.length = res.numEdges`,
per-component `Subperm` and `IsMinSpanningForest`, full frame preservation below `s.frontier`,
space `≤ d.numVerts + d.r0 + d.r0.choose 2 + 9 * ∑ m_i`, and time
`≤ 47 * (n + ∑ m_i + ∑ optDepth C_i + k + 1)`. -/
theorem evalDecisionTreeBatchProg_spec {w tableFrontier : ℕ} {d : DTBatchArgs}
    {Cs : List (List (IndexedEdge d.numVerts))} {edgeBases : List ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hk_eq : d.numComps = Cs.length) (heb_len : edgeBases.length = Cs.length)
    (hmeta : ∀ i (hi : i < Cs.length),
      s.mem (d.compMetaBase + 2 * i) = edgeBases[i]'(heb_len.symm ▸ hi) ∧
      s.mem (d.compMetaBase + 2 * i + 1) = Cs[i].length)
    (hmeta_lt : d.compMetaBase + 2 * Cs.length ≤ s.frontier)
    (hin : ∀ i (hi : i < Cs.length),
      HoldsIndexedEdges (edgeBases[i]'(heb_len.symm ▸ hi)) Cs[i] s.mem ∧
      edgeBases[i]'(heb_len.symm ▸ hi) + 4 * Cs[i].length ≤ s.frontier)
    (hsimp : ∀ i (hi : i < Cs.length),
      IsSimple (edgeEnds (Cs[i].map IndexedEdge.toWeighted)))
    (hvr : ∀ i (hi : i < Cs.length),
      ∃ V : Finset (Fin d.numVerts), V.card ≤ d.r0 ∧ ∀ e ∈ Cs[i], e.u ∈ V ∧ e.v ∈ V)
    (htab : HoldsDTTable d.r0 d.tableBase s.mem)
    (hbnd : DTTableInBounds d.r0 d.tableBase tableFrontier s.mem)
    (htab_fr : tableFrontier ≤ s.frontier)
    (hfit : Fits w (s.frontier + d.numVerts + d.r0 + 2 * d.r0.choose 2 +
      9 * (Cs.map List.length).sum + 1)) :
    let prog := evalDecisionTreeBatchProg d
    let totalM := (Cs.map List.length).sum
    let sumOptD := (Cs.map fun C => optDepth (edgeEnds (C.map IndexedEdge.toWeighted))).sum
    Memory.FramedTriple w s prog
      (47 * (d.numVerts + totalM + sumOptD + Cs.length + 1)) ∅ fun res s' =>
        evalDecisionTreeBatchProgSafe w d s ∧
        res.numVertices = d.numVerts ∧
        s'.frontier ≤ s.frontier + d.numVerts + d.r0 + d.r0.choose 2 + 9 * totalM ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        Memory.WellFormed w s' ∧
        ∃ Fs : List (List (IndexedEdge d.numVerts)),
          Fs.length = Cs.length ∧
          HoldsIndexedEdges res.edgeBase Fs.flatten s'.mem ∧
          Fs.flatten.length = res.numEdges ∧
          ∀ i (hi : i < Cs.length) (hiF : i < Fs.length),
            Fs[i].Subperm Cs[i] ∧
            IsMinSpanningForest (Cs[i].map IndexedEdge.toWeighted)
              (Fs[i].map IndexedEdge.toWeighted) := by
  let totalM := (Cs.map List.length).sum
  let sumOptD := (Cs.map fun C => optDepth (edgeEnds (C.map IndexedEdge.toWeighted))).sum
  obtain ⟨hsafe_sum, hft_sum⟩ := @iterate_dtBatchSumStep_spec w d.compMetaBase d.numVerts Cs
    edgeBases s h16 hwf (fun i hi => by
      obtain ⟨h1, h2⟩ := hmeta i hi
      exact ⟨by simpa [List.getElem?_eq_getElem (heb_len.symm ▸ hi)] using h1, h2⟩)
    hmeta_lt (hfit.of_le (by omega))
  obtain ⟨sumRes, hsum_def⟩ : ∃ x, x = (Memory.spec 0).clientResult s
      (iterate dtBatchSumStep d.compMetaBase Cs.length (0, 0)) := ⟨_, rfl⟩
  obtain ⟨hvh_sum, hm_sum, hmod_sum, hs1_eq, hsum_idx, hsum_acc⟩ :=
    framedTriple_iff_realization.mp hft_sum
  rw [hsum_def.symm] at hsum_idx hsum_acc
  let outBase := s.frontier; let vertMap := outBase + 4 * totalM
  let s2 : Memory.State := ⟨s.mem, vertMap + d.numVerts⟩
  have hfit_4m : Fits w (4 * sumRes.2) := hfit.of_le (by rw [hsum_acc]; omega)
  have hfit_ob : Fits w (s.frontier + 4 * sumRes.2) := hfit.of_le (by rw [hsum_acc]; omega)
  have hfit_vm : Fits w (vertMap + d.numVerts) := hfit.of_le (by dsimp [vertMap, outBase]; omega)
  have hwf2 : Memory.WellFormed w s2 := ⟨hfit_vm, hwf.mem_fits⟩
  have hfill := @fillConstProg_spec w vertMap d.numVerts d.numVerts s2 hwf2
    (hfit.of_le (by omega)) (hfit.of_le (by omega)) (by dsimp only [s2]; omega)
  obtain ⟨s3, hs3_def⟩ : ∃ x, x = (Memory.spec 0).clientState s2
      (dtFillConst (vertMap, d.numVerts)) := ⟨_, rfl⟩
  obtain ⟨_, _, hmod_fill, hfr_fill, hwf3, hvm_vals⟩ := framedTriple_iff_realization.mp hfill
  rw [show (fillConstProg vertMap d.numVerts d.numVerts) = dtFillConst (vertMap, d.numVerts)
    from rfl] at hmod_fill hfr_fill hwf3 hvm_vals
  rw [hs3_def.symm] at hmod_fill hfr_fill hwf3 hvm_vals
  let activeVerts := s3.frontier
  let slotMap := activeVerts + d.r0
  let maxE := d.r0.choose 2
  have hmaxE_def : (if d.r0 = 0 then 0 else d.r0 * (d.r0 - 1) / 2) = maxE := by
    split_ifs with hr0
    · simp [maxE, hr0]
    · exact (Nat.choose_two_right _).symm
  have hav_eq : activeVerts = vertMap + d.numVerts := by dsimp only [activeVerts]; exact hfr_fill
  have hsm_eq : slotMap = vertMap + d.numVerts + d.r0 := by dsimp only [slotMap]; rw [hav_eq]
  have hfit_s4 : Fits w (s3.frontier + d.r0) := by
    rw [hfr_fill]; exact hfit.of_le (by dsimp only [s2, vertMap, outBase]; omega)
  have hfit_mul : Fits w (d.r0 * (d.r0 - 1)) := by
    have h2c : d.r0 * (d.r0 - 1) = 2 * maxE := by
      dsimp only [maxE]; rw [Nat.choose_two_right]
      exact (Nat.mul_div_cancel' (Nat.even_mul_pred_self d.r0).two_dvd).symm
    exact hfit.of_le (by rw [h2c]; dsimp only [maxE]; omega)
  have hfit_maxE : Fits w maxE := hfit.of_le (by dsimp only [maxE]; omega)
  have hfit_s5 : Fits w (slotMap + maxE) := by
    rw [hsm_eq]; exact hfit.of_le (by dsimp only [vertMap, outBase, maxE]; omega)
  let s5 : Memory.State := ⟨s3.mem, slotMap + maxE⟩
  have hwf5 : Memory.WellFormed w s5 := ⟨hfit_s5, fun a => hwf3.mem_fits a⟩
  let batchEnv : DTBatchEnv :=
    ⟨d.tableBase, d.numVerts, d.compMetaBase, vertMap, activeVerts, slotMap, outBase⟩
  let Φ (k : ℕ) (_ : ℕ × ℕ) (_ : Memory.State) : ℕ :=
    45 * (totalM - ((Cs.take k).map List.length).sum) +
    15 * (sumOptD - ((Cs.take k).map
      fun C => optDepth (edgeEnds (C.map IndexedEdge.toWeighted))).sum) + 18 * (Cs.length - k)
  have hstep : ∀ k < Cs.length, ∀ st t, BatchCompInv (w := w) d Cs s k st t →
      dtBatchCompStepSafe w (batchEnv, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (dtBatchCompStep (batchEnv, st))) ∧
      let st' := (Memory.spec 0).clientResult t (dtBatchCompStep (batchEnv, st))
      let t' := (Memory.spec 0).clientState t (dtBatchCompStep (batchEnv, st))
      memoryCost (dtBatchCompStep (batchEnv, st)) t + Φ (k + 1) st' t' ≤ Φ k st t + 0 ∧
      Memory.Modifies (Set.Ici s.frontier) t t' ∧
      BatchCompInv (w := w) d Cs s (k + 1) st' t' := by
    intro k hk st t hinv
    obtain ⟨hsafe_c, hft_c⟩ := dtBatchCompStep_spec h16 heb_len hmeta hmeta_lt hin hsimp hvr
      htab hbnd htab_fr hfit hk st t hinv
    rw [← hav_eq] at hsafe_c hft_c
    obtain ⟨hvh_c, hm_c, hmod_c, hinv_c⟩ := framedTriple_iff_realization.mp hft_c
    obtain ⟨hsumM_k1, hsumM_le⟩ := list_map_take_sum_add Cs List.length hk
    obtain ⟨hsumO_k1, hsumO_le⟩ := list_map_take_sum_add Cs
      (fun C => optDepth (edgeEnds (C.map IndexedEdge.toWeighted))) hk
    refine ⟨hsafe_c, hvh_c, ?_, hmod_c, hinv_c⟩
    have hm_c' : memoryCost (dtBatchCompStep (batchEnv, st)) t ≤ _ := hm_c
    dsimp only [Φ, totalM, sumOptD] at *
    rw [hsumM_k1] at hsumM_le ⊢; rw [hsumO_k1] at hsumO_le ⊢; omega
  have hs5_fr : s5.frontier = s.frontier + 4 * totalM + d.numVerts + d.r0 + maxE := by
    dsimp only [s5]; rw [hsm_eq]
  obtain ⟨hsafe_loop, hv_loop, hm_loop, hmod_loop, _, hfr_end_le, hfr_end_ge, hwf_end, _, _, Fs,
      hFs_len, hflat_len, hacc_le_end, hflat_holds, hFs_msf⟩ :=
    iterate_potential_spec dtBatchCompStep dtBatchCompStepSafe w batchEnv 0 Cs.length
      (BatchCompInv (w := w) d Cs s) Φ (Set.Ici s.frontier) hstep (0, 0) s5
      ⟨rfl, by omega, by omega, hwf5, fun a ha => hmod_fill.mem_eq_of_not_mem
        (by dsimp only [s2, vertMap, outBase]; omega) (by simp only [Set.mem_Ico]; omega),
        hvm_vals, [], rfl, rfl, Nat.zero_le _, fun _ hi => by simp at hi,
        fun _ hi _ _ => absurd hi (Nat.not_lt_zero _)⟩
  have hsumM_all : ((Cs.take Cs.length).map List.length).sum = totalM :=
    by rw [List.take_of_length_le le_rfl]
  rw [hsumM_all] at hfr_end_le hacc_le_end
  have hsafe_fin : evalDecisionTreeBatchProgSafe w d s := by
    dsimp only [evalDecisionTreeBatchProgSafe]; rw [hk_eq, ← hsum_def, hs1_eq]
    rw [hmaxE_def]
    exact ⟨h16, hfit_4m, hfit_mul, hfit_maxE, hfit_ob, hsum_acc ▸ hfit_vm,
      by rw [hsum_acc, ← hs3_def]; exact hfit_s4,
      by rw [hsum_acc, ← hs3_def]; exact hfit_s5,
      hsafe_sum, by rw [hsum_acc, ← hs3_def]; exact hsafe_loop⟩
  let S_all : Set ℕ := Set.Ici s.frontier
  have hft_loop : Memory.FramedTriple w s5 (iterate dtBatchCompStep batchEnv Cs.length (0, 0))
      (45 * totalM + 15 * sumOptD + 18 * Cs.length) S_all fun r' s' =>
        r' = (Memory.spec 0).clientResult s5 (iterate dtBatchCompStep batchEnv Cs.length (0, 0)) ∧
        s' = (Memory.spec 0).clientState s5 (iterate dtBatchCompStep batchEnv Cs.length (0, 0)) :=
    framedTriple_iff_realization.mpr ⟨hv_loop, by
      dsimp only [Φ] at hm_loop
      simp only [List.take_zero, List.map_nil, List.sum_nil] at hm_loop
      simpa only [add_zero] using (by omega : memoryCost _ s5 ≤ _), hmod_loop, rfl, rfl⟩
  refine framedTriple_of_Ici (c := Cs.length + (d.numVerts +
    (45 * totalM + 15 * sumOptD + 18 * Cs.length + 0 + 1 + 1) + 1 + 1)) ?_ (by omega)
  dsimp only [evalDecisionTreeBatchProg]; rw [hk_eq]
  refine Memory.FramedTriple.bind_same (((framedTriple_with_realization hft_sum).frame_mono
    (Set.empty_subset _)).mono le_rfl fun _ _ ⟨hr, hs, _⟩ => ?_)
  rw [hr, hs, ← hsum_def, hs1_eq, hsum_acc]
  refine Memory.FramedTriple.allocDirty_bind (hsum_acc ▸ hfit_ob) ?_
  refine Memory.FramedTriple.allocDirty_bind hfit_vm ?_
  change Memory.FramedTriple w s2 _ _ S_all _
  refine Memory.FramedTriple.bind_same (c₁ := d.numVerts)
    (((framedTriple_with_realization hfill).frame_mono
      fun a ha => by simp only [S_all, Set.mem_Ici, Set.mem_Ico] at ha ⊢; omega).mono le_rfl
      fun _ _ ⟨_, hs', _⟩ => ?_)
  rw [hs', show (Memory.spec 0).clientState s2
    (fillConstProg vertMap d.numVerts d.numVerts) = s3 from hs3_def.symm]
  refine Memory.FramedTriple.allocDirty_bind hfit_s4 ?_
  change Memory.FramedTriple w ⟨s3.mem, slotMap⟩ _ _ S_all _
  rw [hmaxE_def]
  refine Memory.FramedTriple.allocDirty_bind hfit_s5 ?_
  refine Memory.FramedTriple.bind_same (c₁ := 45 * totalM + 15 * sumOptD + 18 * Cs.length)
    (c₂ := 0) (hft_loop.mono le_rfl fun _ _ ⟨hr', hs''⟩ => ?_)
  rw [hr', hs'']
  exact Memory.FramedTriple.pure (c := 0) ⟨hsafe_fin, rfl,
    by dsimp only [maxE] at hs5_fr; omega,
    by dsimp only; omega, hwf_end, Fs, hFs_len, hflat_holds, hflat_len,
    fun i hi hiF => hFs_msf i hi hi hiF⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

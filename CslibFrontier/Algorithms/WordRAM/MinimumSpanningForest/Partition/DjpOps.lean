/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Layout
import CslibFrontier.DataStructure.Memory.Frame
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Dynamic Soft-Heap Partition Setup and DJP Subroutines on the Word RAM

Implements the `Memory.Prog` subroutines, native safety domains, and uniform `Realizes .exact`
(`work = 0`) certificates for workspace setup and dynamic Soft-Heap DJP round growth at
`ε = 1 / 16` ([PettieRamachandran2002], Section 3.2), consuming `buildUndirCSR`, `allocPool`,
`ArrayOps.fillConstProg`, `SoftHeap.shInsert`, and `SoftHeap.shExtractMin`.

All interfaces use named `word_enc_structure` types from `Partition.Layout` with zero positional
tuple projection chains.

## Main definitions

* `partSetup`, `partWriteStride4`, `partCopyIndexedEdge`: workspace setup and stride-4 writers.
* `partTryInsertEdge`, `partExpandStep`, `partExpandVertex`: Soft-Heap edge-expansion helpers.
* `partRoundInit`, `partDjpMaybeExpand`, `partDjpAddVert`, `partDjpDispatch`, `partDjpStep`,
  `partDjpLoop`: dynamic Soft-Heap DJP round initialization, step, and bounded loop.

## Main results

* `realizes_partSetup`, `realizes_partWriteStride4`, `realizes_partCopyIndexedEdge`,
  `realizes_partTryInsertEdge`, `realizes_partExpandStep`, `realizes_partExpandVertex`,
  `realizes_partRoundInit`, `realizes_partDjpMaybeExpand`, `realizes_partDjpAddVert`,
  `realizes_partDjpDispatch`, `realizes_partDjpStep`, `realizes_partDjpLoop`:
  uniform `Realizes .exact` certificates with `work = 0`.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-! ## Dynamic Soft-Heap DJP Growth Subroutines -/

/-- Conditionally inserts edge `d.eIdx` into the Soft Heap when active (`edgeState = 0`) and
neighbor `d.nb` is not yet in the current component (`inCur ≠ d.cid`). -/
def partTryInsertEdge (d : PartTryInsertArgs) : Memory.Prog SHHandle := do
  let st ← Memory.read (d.bufBase + 14 * d.n + d.eIdx)
  if st = 0 then
    let inNb ← Memory.read (d.bufBase + d.n + d.nb)
    if inNb ≠ d.cid then
      let wt ← Memory.read (d.edgeBase + 4 * d.eIdx + 2)
      shInsert (d.sh, d.eIdx, wt, 500 * (2 * d.m + 1))
    else pure d.sh
  else pure d.sh

/-- Native safety domain for `partTryInsertEdge`. -/
def partTryInsertEdgeSafe (w : ℕ) (d : PartTryInsertArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (500 * (2 * d.m + 1)) ∧ Fits w (d.bufBase + 14 * d.n + 14 * d.m) ∧
    d.bufBase + 14 * d.n + d.eIdx < s.frontier ∧
    (s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 →
      d.bufBase + d.n + d.nb < s.frontier ∧
      (s.mem (d.bufBase + d.n + d.nb) ≠ d.cid →
        d.edgeBase + 4 * d.eIdx + 2 < s.frontier ∧
        shInsertSafe w (d.sh, d.eIdx, s.mem (d.edgeBase + 4 * d.eIdx + 2),
          500 * (2 * d.m + 1)) s))

private theorem realizes_partTryInsertEdge_history : Realizes .exact
    partTryInsertEdge WordEncoding.encode WordEncoding.encode
    (fun w d s => partTryInsertEdgeSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partTryInsertEdge d)))
    (fun _ _ => 0) := by
  unfold partTryInsertEdge
  realize [realizes_shInsert]
  all_goals
    obtain ⟨⟨h16, hfuel, hbuf_fit, hst_lt, hbr⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ne_eq, ite_true, not_false_eq_true,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | (have := (hbr trivial).1; fits)
    | (have := ((hbr trivial).2 trivial).1; fits)
    | fits

/-- `partTryInsertEdge` is uniformly realized with `work = 0`. -/
theorem realizes_partTryInsertEdge : Realizes .exact
    partTryInsertEdge WordEncoding.encode WordEncoding.encode
    partTryInsertEdgeSafe (fun _ _ => 0) :=
  realizes_partTryInsertEdge_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partTryInsertEdge`. -/
theorem partTryInsertEdge_def (d : PartTryInsertArgs) : partTryInsertEdge d =
    (Memory.read (d.bufBase + 14 * d.n + d.eIdx) >>= fun st =>
      if st = 0 then
        Memory.read (d.bufBase + d.n + d.nb) >>= fun inNb =>
          if inNb ≠ d.cid then
            Memory.read (d.edgeBase + 4 * d.eIdx + 2) >>= fun wt =>
              shInsert (d.sh, d.eIdx, wt, 500 * (2 * d.m + 1))
          else pure d.sh
      else pure d.sh) := by
  unfold partTryInsertEdge
  rfl

/-- Unfolding equation for `partTryInsertEdgeSafe`. -/
theorem partTryInsertEdgeSafe_def (w : ℕ) (d : PartTryInsertArgs) (s : Memory.State) :
    partTryInsertEdgeSafe w d s =
      (Fits w 16 ∧ Fits w (500 * (2 * d.m + 1)) ∧ Fits w (d.bufBase + 14 * d.n + 14 * d.m) ∧
        d.bufBase + 14 * d.n + d.eIdx < s.frontier ∧
        (s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 →
          d.bufBase + d.n + d.nb < s.frontier ∧
          (s.mem (d.bufBase + d.n + d.nb) ≠ d.cid →
            d.edgeBase + 4 * d.eIdx + 2 < s.frontier ∧
            shInsertSafe w (d.sh, d.eIdx, s.mem (d.edgeBase + 4 * d.eIdx + 2),
              500 * (2 * d.m + 1)) s))) := by
  unfold partTryInsertEdgeSafe
  rfl

/-- Single CSR half-edge expansion step during dynamic DJP growth. -/
def partExpandStep (d : PartAdjEnv × PartExpandState) : Memory.Prog PartExpandState := do
  let env := d.1
  let st := d.2
  let nb ← Memory.read (env.adjBase + 2 * st.idx)
  let eIdx ← Memory.read (env.adjBase + 2 * st.idx + 1)
  let h' ← partTryInsertEdge ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid, nb, eIdx, st.sh⟩
  pure ⟨st.idx + 1, h'⟩

/-- Native safety domain for `partExpandStep`. -/
def partExpandStepSafe (w : ℕ) (d : PartAdjEnv × PartExpandState) (s : Memory.State) : Prop :=
  let env := d.1
  let st := d.2
  Fits w 16 ∧ Fits w (st.idx + 1) ∧ env.adjBase + 2 * st.idx + 1 < s.frontier ∧
    partTryInsertEdgeSafe w
      ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid,
        s.mem (env.adjBase + 2 * st.idx), s.mem (env.adjBase + 2 * st.idx + 1), st.sh⟩ s

private theorem realizes_partExpandStep_history : Realizes .exact
    partExpandStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partExpandStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partExpandStep d)))
    (fun _ _ => 0) := by
  unfold partExpandStep
  realize [realizes_partTryInsertEdge]
  all_goals
    obtain ⟨⟨h16, hj1, hadj_lt, htry⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partExpandStep` is uniformly realized with `work = 0`. -/
theorem realizes_partExpandStep : Realizes .exact
    partExpandStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partExpandStepSafe (fun _ _ => 0) :=
  realizes_partExpandStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partExpandStep`. -/
theorem partExpandStep_def (d : PartAdjEnv × PartExpandState) : partExpandStep d =
    (Memory.read (d.1.adjBase + 2 * d.2.idx) >>= fun nb =>
      Memory.read (d.1.adjBase + 2 * d.2.idx + 1) >>= fun eIdx =>
        partTryInsertEdge
          ⟨d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid, nb, eIdx, d.2.sh⟩ >>= fun h' =>
          pure ⟨d.2.idx + 1, h'⟩) := by
  unfold partExpandStep
  rfl

/-- Unfolding equation for `partExpandStepSafe`. -/
theorem partExpandStepSafe_def (w : ℕ) (d : PartAdjEnv × PartExpandState) (s : Memory.State) :
    partExpandStepSafe w d s =
      (Fits w 16 ∧ Fits w (d.2.idx + 1) ∧ d.1.adjBase + 2 * d.2.idx + 1 < s.frontier ∧
        partTryInsertEdgeSafe w
          ⟨d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid,
            s.mem (d.1.adjBase + 2 * d.2.idx),
            s.mem (d.1.adjBase + 2 * d.2.idx + 1), d.2.sh⟩ s) := by
  unfold partExpandStepSafe
  rfl

/-- Expands all active CSR edges incident to vertex `d.u` into the Soft Heap. -/
def partExpandVertex (d : PartExpandVertexArgs) : Memory.Prog SHHandle := do
  let startJ ← Memory.read (d.env.offBase + d.u)
  let endJ ← Memory.read (d.env.offBase + d.u + 1)
  let res ← iterate partExpandStep
    ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
    (endJ - startJ) ⟨startJ, d.sh⟩
  pure res.sh

/-- Native safety domain for `partExpandVertex`. -/
def partExpandVertexSafe (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) : Prop :=
  let startJ := s.mem (d.env.offBase + d.u)
  let endJ := s.mem (d.env.offBase + d.u + 1)
  Fits w 16 ∧ d.env.offBase + d.u + 1 < s.frontier ∧ startJ ≤ endJ ∧
    iterationSafe partExpandStep partExpandStepSafe w
      ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
      (endJ - startJ) ⟨startJ, d.sh⟩ s

private theorem realizes_partExpandVertex_history : Realizes .exact
    partExpandVertex WordEncoding.encode WordEncoding.encode
    (fun w d s => partExpandVertexSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partExpandVertex d)))
    (fun _ _ => 0) := by
  unfold partExpandVertex
  realize [realizes_partExpandStep]
  all_goals
    obtain ⟨⟨h16, hoff_lt, hle, hiter⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | exact iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => hs)
    | fits

/-- `partExpandVertex` is uniformly realized with `work = 0`. -/
theorem realizes_partExpandVertex : Realizes .exact
    partExpandVertex WordEncoding.encode WordEncoding.encode
    partExpandVertexSafe (fun _ _ => 0) :=
  realizes_partExpandVertex_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partExpandVertex`. -/
theorem partExpandVertex_def (d : PartExpandVertexArgs) : partExpandVertex d =
    (Memory.read (d.env.offBase + d.u) >>= fun startJ =>
      Memory.read (d.env.offBase + d.u + 1) >>= fun endJ =>
        iterate partExpandStep
          ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
          (endJ - startJ) ⟨startJ, d.sh⟩ >>= fun res =>
          pure res.sh) := by
  unfold partExpandVertex
  rfl

/-- Unfolding equation for `partExpandVertexSafe`. -/
theorem partExpandVertexSafe_def (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) :
    partExpandVertexSafe w d s =
      (Fits w 16 ∧ d.env.offBase + d.u + 1 < s.frontier ∧
        s.mem (d.env.offBase + d.u) ≤ s.mem (d.env.offBase + d.u + 1) ∧
        iterationSafe partExpandStep partExpandStepSafe w
          ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
          (s.mem (d.env.offBase + d.u + 1) - s.mem (d.env.offBase + d.u))
          ⟨s.mem (d.env.offBase + d.u), d.sh⟩ s) := by
  unfold partExpandVertexSafe
  rfl

/-- Writes four words `(u, v, weight, id)` in stride-4 layout at `d.dstBase + 4 * d.idx`. -/
def partWriteStride4 (d : PartWriteStride4Args) : Memory.Prog Unit := do
  Memory.write (d.dstBase + 4 * d.idx) d.u
  Memory.write (d.dstBase + 4 * d.idx + 1) d.v
  Memory.write (d.dstBase + 4 * d.idx + 2) d.weight
  Memory.write (d.dstBase + 4 * d.idx + 3) d.id

/-- Native safety domain for `partWriteStride4`. -/
def partWriteStride4Safe (w : ℕ) (d : PartWriteStride4Args) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.dstBase + 4 * d.idx + 3 < s.frontier

/-- `partWriteStride4` is uniformly realized with `work = 0`. -/
theorem realizes_partWriteStride4 : Realizes .exact
    partWriteStride4 WordEncoding.encode WordEncoding.encode
    partWriteStride4Safe (fun _ _ => 0) := by
  unfold partWriteStride4
  realize
  all_goals
    have h16 := h.1
    have hlt := h.2
    have hfront := hmem.frontier_fits
    fits

/-- Unfolding equation for `partWriteStride4`. -/
theorem partWriteStride4_def (d : PartWriteStride4Args) : partWriteStride4 d =
    (Memory.write (d.dstBase + 4 * d.idx) d.u >>= fun _ =>
      Memory.write (d.dstBase + 4 * d.idx + 1) d.v >>= fun _ =>
        Memory.write (d.dstBase + 4 * d.idx + 2) d.weight >>= fun _ =>
          Memory.write (d.dstBase + 4 * d.idx + 3) d.id) := by
  unfold partWriteStride4
  rfl

/-- Unfolding equation for `partWriteStride4Safe`. -/
theorem partWriteStride4Safe_def (w : ℕ) (d : PartWriteStride4Args) (s : Memory.State) :
    partWriteStride4Safe w d s = (Fits w 16 ∧ d.dstBase + 4 * d.idx + 3 < s.frontier) := by
  unfold partWriteStride4Safe
  rfl

/-- Copies stride-4 indexed edge `d.srcIdx` from `d.srcBase` to `d.dstBase + 4 * d.dstIdx`. -/
def partCopyIndexedEdge (d : PartCopyEdgeArgs) : Memory.Prog Unit := do
  let u ← Memory.read (d.srcBase + 4 * d.srcIdx)
  let v ← Memory.read (d.srcBase + 4 * d.srcIdx + 1)
  let wt ← Memory.read (d.srcBase + 4 * d.srcIdx + 2)
  let eid ← Memory.read (d.srcBase + 4 * d.srcIdx + 3)
  partWriteStride4 ⟨d.dstBase, d.dstIdx, u, v, wt, eid⟩

/-- Native safety domain for `partCopyIndexedEdge`. -/
def partCopyIndexedEdgeSafe (w : ℕ) (d : PartCopyEdgeArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.srcBase + 4 * d.srcIdx + 3 < s.frontier ∧
    d.dstBase + 4 * d.dstIdx + 3 < s.frontier

/-- `partCopyIndexedEdge` is uniformly realized with `work = 0`. -/
theorem realizes_partCopyIndexedEdge : Realizes .exact
    partCopyIndexedEdge WordEncoding.encode WordEncoding.encode
    partCopyIndexedEdgeSafe (fun _ _ => 0) := by
  unfold partCopyIndexedEdge
  realize [realizes_partWriteStride4]
  all_goals
    have h16 := h.1
    have hs := h.2.1
    have hd := h.2.2
    have hfront := hmem.frontier_fits
    first | exact ⟨h16, hd⟩ | fits

/-- Unfolding equation for `partCopyIndexedEdge`. -/
theorem partCopyIndexedEdge_def (d : PartCopyEdgeArgs) : partCopyIndexedEdge d =
    (Memory.read (d.srcBase + 4 * d.srcIdx) >>= fun u =>
      Memory.read (d.srcBase + 4 * d.srcIdx + 1) >>= fun v =>
        Memory.read (d.srcBase + 4 * d.srcIdx + 2) >>= fun wt =>
          Memory.read (d.srcBase + 4 * d.srcIdx + 3) >>= fun eid =>
            partWriteStride4 ⟨d.dstBase, d.dstIdx, u, v, wt, eid⟩) := by
  unfold partCopyIndexedEdge
  rfl

/-- Unfolding equation for `partCopyIndexedEdgeSafe`. -/
theorem partCopyIndexedEdgeSafe_def (w : ℕ) (d : PartCopyEdgeArgs) (s : Memory.State) :
    partCopyIndexedEdgeSafe w d s =
      (Fits w 16 ∧ d.srcBase + 4 * d.srcIdx + 3 < s.frontier ∧
        d.dstBase + 4 * d.dstIdx + 3 < s.frontier) := by
  unfold partCopyIndexedEdgeSafe
  rfl

/-- Checks stopping criteria after adding `d.vOut` (`d.dOut ≠ 0` or `d.env.maxsize ≤ d.size`),
expanding `d.vOut` only if continuing. -/
def partDjpMaybeExpand (d : PartDjpMaybeExpandArgs) : Memory.Prog PartDjpState := do
  if d.dOut ≠ 0 then
    pure ⟨0, 1, d.size, d.tLen, d.sh⟩
  else if d.env.maxsize ≤ d.size then
    pure ⟨0, 0, d.size, d.tLen, d.sh⟩
  else
    let h' ← partExpandVertex ⟨d.env, d.cid, d.vOut, d.sh⟩
    pure ⟨1, 0, d.size, d.tLen, h'⟩

/-- Native safety domain for `partDjpMaybeExpand`. -/
def partDjpMaybeExpandSafe (w : ℕ) (d : PartDjpMaybeExpandArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    (d.dOut = 0 → ¬(d.env.maxsize ≤ d.size) →
      partExpandVertexSafe w ⟨d.env, d.cid, d.vOut, d.sh⟩ s)

/-- `partDjpMaybeExpand` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpMaybeExpand : Realizes .exact
    partDjpMaybeExpand WordEncoding.encode WordEncoding.encode
    partDjpMaybeExpandSafe (fun _ _ => 0) := by
  unfold partDjpMaybeExpand
  realize [realizes_partExpandVertex]
  · exact h.2 (by omega) (by omega)
  · have h16 := h.1; fits
  · have h16 := h.1; fits

/-- Unfolding equation for `partDjpMaybeExpand`. -/
theorem partDjpMaybeExpand_def (d : PartDjpMaybeExpandArgs) : partDjpMaybeExpand d =
    (if d.dOut ≠ 0 then pure ⟨0, 1, d.size, d.tLen, d.sh⟩
    else if d.env.maxsize ≤ d.size then pure ⟨0, 0, d.size, d.tLen, d.sh⟩
    else partExpandVertex ⟨d.env, d.cid, d.vOut, d.sh⟩ >>= fun h' =>
      pure ⟨1, 0, d.size, d.tLen, h'⟩) := by
  unfold partDjpMaybeExpand
  rfl

/-- Unfolding equation for `partDjpMaybeExpandSafe`. -/
theorem partDjpMaybeExpandSafe_def (w : ℕ) (d : PartDjpMaybeExpandArgs) (s : Memory.State) :
    partDjpMaybeExpandSafe w d s =
      (Fits w 16 ∧ (d.dOut = 0 → ¬(d.env.maxsize ≤ d.size) →
        partExpandVertexSafe w ⟨d.env, d.cid, d.vOut, d.sh⟩ s)) := by
  unfold partDjpMaybeExpandSafe
  rfl

/-- Adds newly discovered vertex `d.vOut` and DJP tree edge `d.eIdx` to the current round. -/
def partDjpAddVert (d : PartDjpAddVertArgs) : Memory.Prog PartDjpState := do
  let bufBase := d.env.bufBase
  let n := d.env.n
  partCopyIndexedEdge ⟨d.env.edgeBase, bufBase + 10 * n, d.eIdx, d.tLen⟩
  let dOut ← Memory.read (bufBase + d.vOut)
  Memory.write (bufBase + 3 * n + d.size) d.vOut
  Memory.write (bufBase + n + d.vOut) d.cid
  Memory.write (bufBase + 2 * n + d.vOut) d.size
  partDjpMaybeExpand ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩

/-- Native safety domain for `partDjpAddVert`. -/
def partDjpAddVertSafe (w : ℕ) (d : PartDjpAddVertArgs) (s : Memory.State) : Prop :=
  let bufBase := d.env.bufBase
  let n := d.env.n
  let m := d.env.m
  Fits w 16 ∧ Fits w (d.size + 1) ∧ Fits w (d.tLen + 1) ∧ Fits w (bufBase + 14 * n + 14 * m) ∧
    partCopyIndexedEdgeSafe w ⟨d.env.edgeBase, bufBase + 10 * n, d.eIdx, d.tLen⟩ s ∧
    bufBase + d.vOut < s.frontier ∧ bufBase + 3 * n + d.size < s.frontier ∧
    bufBase + n + d.vOut < s.frontier ∧ bufBase + 2 * n + d.vOut < s.frontier ∧
    let s₁ := (Memory.spec 0).clientState s
      (partCopyIndexedEdge ⟨d.env.edgeBase, bufBase + 10 * n, d.eIdx, d.tLen⟩)
    let dOut := s₁.mem (bufBase + d.vOut)
    let s₂ : Memory.State := ⟨Function.update (Function.update (Function.update s₁.mem
      (bufBase + 3 * n + d.size) d.vOut) (bufBase + n + d.vOut) d.cid)
      (bufBase + 2 * n + d.vOut) d.size, s₁.frontier⟩
    partDjpMaybeExpandSafe w ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩ s₂

private theorem realizes_partDjpAddVert_history : Realizes .exact
    partDjpAddVert WordEncoding.encode WordEncoding.encode
    (fun w d s => partDjpAddVertSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partDjpAddVert d)))
    (fun _ _ => 0) := by
  unfold partDjpAddVert
  realize [realizes_partCopyIndexedEdge, realizes_partDjpMaybeExpand]
  all_goals
    obtain ⟨⟨h16, hsz, htl, _, hcopy, hlt1, hlt2, hlt3, hlt4, hme⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [Memory.write]
  all_goals fits

/-- `partDjpAddVert` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpAddVert : Realizes .exact
    partDjpAddVert WordEncoding.encode WordEncoding.encode
    partDjpAddVertSafe (fun _ _ => 0) :=
  realizes_partDjpAddVert_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partDjpAddVert`. -/
theorem partDjpAddVert_def (d : PartDjpAddVertArgs) : partDjpAddVert d =
    (partCopyIndexedEdge ⟨d.env.edgeBase, d.env.bufBase + 10 * d.env.n, d.eIdx, d.tLen⟩ >>=
      fun _ =>
        Memory.read (d.env.bufBase + d.vOut) >>= fun dOut =>
          Memory.write (d.env.bufBase + 3 * d.env.n + d.size) d.vOut >>= fun _ =>
            Memory.write (d.env.bufBase + d.env.n + d.vOut) d.cid >>= fun _ =>
            Memory.write (d.env.bufBase + 2 * d.env.n + d.vOut) d.size >>= fun _ =>
              partDjpMaybeExpand
                ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩) := by
  unfold partDjpAddVert
  rfl

/-- Unfolding equation for `partDjpAddVertSafe`. -/
theorem partDjpAddVertSafe_def (w : ℕ) (d : PartDjpAddVertArgs) (s : Memory.State) :
    partDjpAddVertSafe w d s =
      (Fits w 16 ∧ Fits w (d.size + 1) ∧ Fits w (d.tLen + 1) ∧
        Fits w (d.env.bufBase + 14 * d.env.n + 14 * d.env.m) ∧
        partCopyIndexedEdgeSafe w
          ⟨d.env.edgeBase, d.env.bufBase + 10 * d.env.n, d.eIdx, d.tLen⟩ s ∧
        d.env.bufBase + d.vOut < s.frontier ∧
        d.env.bufBase + 3 * d.env.n + d.size < s.frontier ∧
        d.env.bufBase + d.env.n + d.vOut < s.frontier ∧
        d.env.bufBase + 2 * d.env.n + d.vOut < s.frontier ∧
        let s₁ := (Memory.spec 0).clientState s
          (partCopyIndexedEdge ⟨d.env.edgeBase, d.env.bufBase + 10 * d.env.n, d.eIdx, d.tLen⟩)
        let dOut := s₁.mem (d.env.bufBase + d.vOut)
        let s₂ : Memory.State := ⟨Function.update (Function.update (Function.update s₁.mem
          (d.env.bufBase + 3 * d.env.n + d.size) d.vOut)
          (d.env.bufBase + d.env.n + d.vOut) d.cid)
          (d.env.bufBase + 2 * d.env.n + d.vOut) d.size, s₁.frontier⟩
        partDjpMaybeExpandSafe w
          ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩ s₂) := by
  unfold partDjpAddVertSafe
  rfl

/-- Processes an extracted edge `d.eIdx`, skipping internal edges and otherwise adding `vOut`. -/
def partDjpDispatch (d : PartDjpDispatchArgs) : Memory.Prog PartDjpState := do
  let edgeBase := d.env.edgeBase
  let inCurBase := d.env.bufBase + d.env.n
  let u ← Memory.read (edgeBase + 4 * d.eIdx)
  let v ← Memory.read (edgeBase + 4 * d.eIdx + 1)
  let cu ← Memory.read (inCurBase + u)
  let cv ← Memory.read (inCurBase + v)
  if cu = d.cid ∧ cv = d.cid then
    pure ⟨1, d.hitPrev, d.size, d.tLen, d.sh⟩
  else
    let vOut := if cu = d.cid then v else u
    partDjpAddVert ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩

/-- Native safety domain for `partDjpDispatch`. -/
def partDjpDispatchSafe (w : ℕ) (d : PartDjpDispatchArgs) (s : Memory.State) : Prop :=
  let edgeBase := d.env.edgeBase
  let inCurBase := d.env.bufBase + d.env.n
  let u := s.mem (edgeBase + 4 * d.eIdx)
  let v := s.mem (edgeBase + 4 * d.eIdx + 1)
  let cu := s.mem (inCurBase + u)
  let cv := s.mem (inCurBase + v)
  Fits w 16 ∧ edgeBase + 4 * d.eIdx + 1 < s.frontier ∧
    inCurBase + u < s.frontier ∧ inCurBase + v < s.frontier ∧
    (¬(cu = d.cid ∧ cv = d.cid) →
      let vOut := if cu = d.cid then v else u
      partDjpAddVertSafe w ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩ s)

private theorem realizes_partDjpDispatch_history : Realizes .exact
    partDjpDispatch WordEncoding.encode WordEncoding.encode
    (fun w d s => partDjpDispatchSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partDjpDispatch d)))
    (fun _ _ => 0) := by
  unfold partDjpDispatch
  realize [realizes_partDjpAddVert]
  all_goals
    obtain ⟨⟨h16, he_lt, hu_lt, hv_lt, hadd⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ite_true, ite_false, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first | exact hadd (by simp_all) | fits

/-- `partDjpDispatch` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpDispatch : Realizes .exact
    partDjpDispatch WordEncoding.encode WordEncoding.encode
    partDjpDispatchSafe (fun _ _ => 0) :=
  realizes_partDjpDispatch_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partDjpDispatch`. -/
theorem partDjpDispatch_def (d : PartDjpDispatchArgs) : partDjpDispatch d =
    (Memory.read (d.env.edgeBase + 4 * d.eIdx) >>= fun u =>
      Memory.read (d.env.edgeBase + 4 * d.eIdx + 1) >>= fun v =>
        Memory.read (d.env.bufBase + d.env.n + u) >>= fun cu =>
          Memory.read (d.env.bufBase + d.env.n + v) >>= fun cv =>
            if cu = d.cid ∧ cv = d.cid then pure ⟨1, d.hitPrev, d.size, d.tLen, d.sh⟩
            else
              let vOut := if cu = d.cid then v else u
              partDjpAddVert ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩) := by
  unfold partDjpDispatch
  rfl

/-- Unfolding equation for `partDjpDispatchSafe`. -/
theorem partDjpDispatchSafe_def (w : ℕ) (d : PartDjpDispatchArgs) (s : Memory.State) :
    partDjpDispatchSafe w d s =
      (Fits w 16 ∧ d.env.edgeBase + 4 * d.eIdx + 1 < s.frontier ∧
        d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx) < s.frontier ∧
        d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx + 1) < s.frontier ∧
        (¬(s.mem (d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx)) = d.cid ∧
            s.mem (d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx + 1)) = d.cid) →
          let u := s.mem (d.env.edgeBase + 4 * d.eIdx)
          let v := s.mem (d.env.edgeBase + 4 * d.eIdx + 1)
          let vOut := if s.mem (d.env.bufBase + d.env.n + u) = d.cid then v else u
          partDjpAddVertSafe w ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩ s)) := by
  unfold partDjpDispatchSafe
  rfl

/-- Single `boundedWhile` step of the dynamic Soft-Heap DJP loop. The initial `Memory.read`
of `bufBase` ensures `1 ≤ memoryCost (partDjpStep d) s` even when `shExtractMin` returns early
on an empty heap (`firstRoot = 0`, `memoryCost = 0`), allowing `Realizes.while₀` (`work = 0`). -/
def partDjpStep (d : PartDjpEnv × PartDjpState) : Memory.Prog PartDjpState := do
  let _ ← Memory.read d.1.env.bufBase
  let ext ← shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1))
  if ext.found = 0 then
    pure ⟨0, 0, d.2.size, d.2.tLen, ext.handle⟩
  else
    partDjpDispatch ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩

/-- Native safety domain for `partDjpStep`. -/
def partDjpStepSafe (w : ℕ) (d : PartDjpEnv × PartDjpState) (s : Memory.State) : Prop :=
  let m := d.1.env.m
  Fits w 16 ∧ Fits w (500 * (2 * m + 1)) ∧ d.1.env.bufBase < s.frontier ∧
    shExtractMinSafe w (d.2.sh, 500 * (2 * m + 1)) s ∧
    let ext := (Memory.spec 0).clientResult s (shExtractMin (d.2.sh, 500 * (2 * m + 1)))
    let s₁ := (Memory.spec 0).clientState s (shExtractMin (d.2.sh, 500 * (2 * m + 1)))
    (ext.found ≠ 0 →
      partDjpDispatchSafe w
        ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩ s₁)

private theorem realizes_partDjpStep_history : Realizes .exact
    partDjpStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partDjpStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partDjpStep d)))
    (fun _ _ => 0) := by
  unfold partDjpStep
  realize [realizes_shExtractMin, realizes_partDjpDispatch]
  all_goals
    obtain ⟨⟨h16, hfuel, hbuf_lt, hext, hdisp⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | exact hdisp (by assumption)
    | fits

/-- `partDjpStep` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpStep : Realizes .exact
    partDjpStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partDjpStepSafe (fun _ _ => 0) :=
  realizes_partDjpStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partDjpStep`. -/
theorem partDjpStep_def (d : PartDjpEnv × PartDjpState) : partDjpStep d =
    (Memory.read d.1.env.bufBase >>= fun _ =>
      shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1)) >>= fun ext =>
        if ext.found = 0 then pure ⟨0, 0, d.2.size, d.2.tLen, ext.handle⟩
        else partDjpDispatch
          ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩) := by
  unfold partDjpStep
  rfl

/-- Unfolding equation for `partDjpStepSafe`. -/
theorem partDjpStepSafe_def (w : ℕ) (d : PartDjpEnv × PartDjpState) (s : Memory.State) :
    partDjpStepSafe w d s =
      (Fits w 16 ∧ Fits w (500 * (2 * d.1.env.m + 1)) ∧ d.1.env.bufBase < s.frontier ∧
        shExtractMinSafe w (d.2.sh, 500 * (2 * d.1.env.m + 1)) s ∧
        let ext := (Memory.spec 0).clientResult s
          (shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1)))
        let s₁ := (Memory.spec 0).clientState s
          (shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1)))
        (ext.found ≠ 0 → partDjpDispatchSafe w
          ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩ s₁)) := by
  unfold partDjpStepSafe
  rfl

/-! ## Round Initialization, DJP While Loop, and Setup -/

/-- Initializes a new dynamic-DJP round at root `d.u` and expands `d.u` when
`1 < d.env.maxsize`. -/
def partRoundInit (d : PartExpandVertexArgs) : Memory.Prog SHHandle := do
  let n := d.env.n
  let bufBase := d.env.bufBase
  Memory.write (bufBase + 3 * n) d.u
  Memory.write (bufBase + n + d.u) d.cid
  Memory.write (bufBase + 2 * n + d.u) 0
  if d.env.maxsize ≤ 1 then pure d.sh
  else partExpandVertex d

/-- Native safety domain for `partRoundInit`. -/
def partRoundInitSafe (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) : Prop :=
  let n := d.env.n
  let bufBase := d.env.bufBase
  let s₁ : Memory.State := ⟨Function.update (Function.update (Function.update s.mem
    (bufBase + 3 * n) d.u) (bufBase + n + d.u) d.cid) (bufBase + 2 * n + d.u) 0, s.frontier⟩
  Fits w 16 ∧ bufBase + 3 * n < s.frontier ∧ bufBase + n + d.u < s.frontier ∧
    bufBase + 2 * n + d.u < s.frontier ∧
    (¬(d.env.maxsize ≤ 1) → partExpandVertexSafe w d s₁)

private theorem realizes_partRoundInit_history : Realizes .exact
    partRoundInit WordEncoding.encode WordEncoding.encode
    (fun w d s => partRoundInitSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partRoundInit d)))
    (fun _ _ => 0) := by
  unfold partRoundInit
  realize [realizes_partExpandVertex]
  all_goals
    obtain ⟨⟨h16, h1, h2, h3, hexp⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.write, Memory.step_write, Memory.valid]
  all_goals first | exact hexp (by omega) | fits

/-- `partRoundInit` is uniformly realized with `work = 0`. -/
theorem realizes_partRoundInit : Realizes .exact
    partRoundInit WordEncoding.encode WordEncoding.encode
    partRoundInitSafe (fun _ _ => 0) :=
  realizes_partRoundInit_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partRoundInit`. -/
theorem partRoundInit_def (d : PartExpandVertexArgs) : partRoundInit d =
    (Memory.write (d.env.bufBase + 3 * d.env.n) d.u >>= fun _ =>
      Memory.write (d.env.bufBase + d.env.n + d.u) d.cid >>= fun _ =>
        Memory.write (d.env.bufBase + 2 * d.env.n + d.u) 0 >>= fun _ =>
          if d.env.maxsize ≤ 1 then pure d.sh else partExpandVertex d) := by
  unfold partRoundInit
  rfl

/-- Unfolding equation for `partRoundInitSafe`. -/
theorem partRoundInitSafe_def (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) :
    partRoundInitSafe w d s =
      (let s₁ : Memory.State := ⟨Function.update (Function.update (Function.update s.mem
        (d.env.bufBase + 3 * d.env.n) d.u) (d.env.bufBase + d.env.n + d.u) d.cid)
        (d.env.bufBase + 2 * d.env.n + d.u) 0, s.frontier⟩
      Fits w 16 ∧ d.env.bufBase + 3 * d.env.n < s.frontier ∧
        d.env.bufBase + d.env.n + d.u < s.frontier ∧
        d.env.bufBase + 2 * d.env.n + d.u < s.frontier ∧
        (¬(d.env.maxsize ≤ 1) → partExpandVertexSafe w d s₁)) := by
  unfold partRoundInitSafe
  rfl

/-- Bounded while loop growing one dynamic-DJP component starting from expanded root `u`. -/
def partDjpLoop (d : PartDjpLoopArgs) : Memory.Prog PartDjpState := do
  if d.env.maxsize ≤ 1 then pure ⟨0, 0, 1, d.tLen, d.sh⟩
  else boundedWhile (fun _ (s : PartDjpState) => s.cont ≠ 0)
         partDjpStep ⟨d.env, d.cid⟩ (2 * d.env.m + 1) ⟨1, 0, 1, d.tLen, d.sh⟩

/-- Native safety domain for `partDjpLoop`. -/
def partDjpLoopSafe (w : ℕ) (d : PartDjpLoopArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    (¬(d.env.maxsize ≤ 1) →
      whileSafe (fun _ (s : PartDjpState) => s.cont ≠ 0)
        partDjpStep partDjpStepSafe w ⟨d.env, d.cid⟩ (2 * d.env.m + 1)
        ⟨1, 0, 1, d.tLen, d.sh⟩ s)

/-- `partDjpLoop` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpLoop : Realizes .exact
    partDjpLoop WordEncoding.encode WordEncoding.encode
    partDjpLoopSafe (fun _ _ => 0) := by
  unfold partDjpLoop
  realize [realizes_partDjpStep]
  all_goals first
    | (have h16 := h.1; fits)
    | (intro _; exact whileSafe_imp (fun _ (s : PartDjpState) => s.cont ≠ 0)
        (fun _ (s : PartDjpState) => s.cont ≠ 0)
        (safe := partDjpStepSafe)
        (safe' := fun w x s => partDjpStepSafe w (⟨d.env, d.cid⟩, x.2) s)
        (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ _ hs => hs) (h.2 (by omega)))

/-- Unfolding equation for `partDjpLoop`. -/
theorem partDjpLoop_def (d : PartDjpLoopArgs) : partDjpLoop d =
    (if d.env.maxsize ≤ 1 then pure ⟨0, 0, 1, d.tLen, d.sh⟩
    else boundedWhile (fun _ (s : PartDjpState) => s.cont ≠ 0)
      partDjpStep ⟨d.env, d.cid⟩ (2 * d.env.m + 1) ⟨1, 0, 1, d.tLen, d.sh⟩) := by
  unfold partDjpLoop
  rfl

/-- Unfolding equation for `partDjpLoopSafe`. -/
theorem partDjpLoopSafe_def (w : ℕ) (d : PartDjpLoopArgs) (s : Memory.State) :
    partDjpLoopSafe w d s =
      (Fits w 16 ∧ (¬(d.env.maxsize ≤ 1) →
        whileSafe (fun _ (s : PartDjpState) => s.cont ≠ 0)
          partDjpStep partDjpStepSafe w ⟨d.env, d.cid⟩ (2 * d.env.m + 1)
          ⟨1, 0, 1, d.tLen, d.sh⟩ s)) := by
  unfold partDjpLoopSafe
  rfl

/-- Allocates and zero-initializes CSR, Soft-Heap pool (`rankThreshold = 8`), and partition
workspace arrays using `buildUndirCSR`, `allocPool`, and `fillConstProg`. -/
def partSetup (d : PartSetupArgs) : Memory.Prog PartSetupResult := do
  let csr ← buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩
  let pool ← allocPool (2 * d.m) (4 * d.m)
  let bufBase ← Memory.allocDirty (14 * d.n + 14 * d.m)
  fillConstProg bufBase 0 (2 * d.n)
  fillConstProg (bufBase + 14 * d.n) 0 d.m
  pure ⟨⟨d.n, d.m, d.edgeBase, d.maxsize, csr.offBase, csr.adjBase, bufBase⟩,
    ⟨pool.1, pool.2, 0, 0, 0, partRankThreshold⟩⟩

/-- Native safety domain for `partSetup`. -/
def partSetupSafe (w : ℕ) (d : PartSetupArgs) (s : Memory.State) : Prop :=
  let s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩)
  let s₂ := (Memory.spec 0).clientState s₁ (allocPool (2 * d.m) (4 * d.m))
  let bufBase := s₂.frontier
  Fits w 16 ∧
    d.edgeBase + 4 * d.m ≤ s.frontier ∧
    Fits w (s.frontier + (2 * d.n + 4 * d.m + 1)) ∧
    (∀ j < d.m,
      s.mem (d.edgeBase + 4 * j) < d.n ∧ s.mem (d.edgeBase + 4 * j + 1) < d.n) ∧
    Fits w (s₁.frontier + 3 * (2 * d.m + 1) + 12 * (4 * d.m + 1) + 16) ∧
    Fits w (bufBase + (14 * d.n + 14 * d.m)) ∧
    Fits w (2 * d.n) ∧ Fits w d.m

/-- `partSetup` is uniformly realized with `work = 0`. -/
theorem realizes_partSetup : Realizes .exact
    partSetup WordEncoding.encode WordEncoding.encode
    partSetupSafe (fun _ _ => 0) := by
  unfold partSetup
  realize [realizes_buildUndirCSR, realizes_allocPool, realizes_fillConstProg]
  all_goals
    obtain ⟨h16, hin_lt, hfit_csr, hedges, hfit_pool, hfit_buf, h2n, hm⟩ := h
    have hfront := hmem.frontier_fits
    have hrt : partRankThreshold = 8 := rfl
    let s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩)
    let s₂ := (Memory.spec 0).clientState s₁ (allocPool (2 * d.m) (4 * d.m))
    let s₃ : Memory.State := ⟨s₂.mem, s₂.frontier + (14 * d.n + 14 * d.m)⟩
    have hfr_z1 : s₂.frontier + (14 * d.n + 14 * d.m) ≤
        ((Memory.spec 0).clientState s₃ (fillConstProg s₂.frontier 0 (2 * d.n))).frontier :=
      Memory.frontier_le_clientState s₃ (fillConstProg s₂.frontier 0 (2 * d.n))
    first
    | exact h16
    | exact hin_lt
    | exact hfit_csr
    | exact hedges
    | exact hfit_pool
    | exact h16.of_le (by omega)
    | exact h2n
    | (dsimp only [s₁, s₂, s₃] at hfr_z1 ⊢; omega)
    | fits

/-- Unfolding equation for `partSetup`. -/
theorem partSetup_def (d : PartSetupArgs) : partSetup d =
    (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩ >>= fun csr =>
      allocPool (2 * d.m) (4 * d.m) >>= fun pool =>
        Memory.allocDirty (14 * d.n + 14 * d.m) >>= fun bufBase =>
          fillConstProg bufBase 0 (2 * d.n) >>= fun _ =>
            fillConstProg (bufBase + 14 * d.n) 0 d.m >>= fun _ =>
              pure ⟨⟨d.n, d.m, d.edgeBase, d.maxsize, csr.offBase, csr.adjBase, bufBase⟩,
                ⟨pool.1, pool.2, 0, 0, 0, partRankThreshold⟩⟩) := by
  unfold partSetup
  rfl

/-- Unfolding equation for `partSetupSafe`. -/
theorem partSetupSafe_def (w : ℕ) (d : PartSetupArgs) (s : Memory.State) :
    partSetupSafe w d s =
      (let s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩)
      let s₂ := (Memory.spec 0).clientState s₁ (allocPool (2 * d.m) (4 * d.m))
      Fits w 16 ∧ d.edgeBase + 4 * d.m ≤ s.frontier ∧
        Fits w (s.frontier + (2 * d.n + 4 * d.m + 1)) ∧
        (∀ j < d.m,
          s.mem (d.edgeBase + 4 * j) < d.n ∧ s.mem (d.edgeBase + 4 * j + 1) < d.n) ∧
        Fits w (s₁.frontier + 3 * (2 * d.m + 1) + 12 * (4 * d.m + 1) + 16) ∧
        Fits w (s₂.frontier + (14 * d.n + 14 * d.m)) ∧ Fits w (2 * d.n) ∧ Fits w d.m) := by
  unfold partSetupSafe
  rfl

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

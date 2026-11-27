/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.DjpOps
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Outer Loop, Emission, and Top-Level `Partition` Programs on the Word RAM

Steps toward Theorem 5.8 of [PettieRamachandran2002] (#8624), implementing the `Memory.Prog`
subroutines, native safety domains, and uniform `Realizes .exact` (`work = 0`) certificates for
the outer loop of `Partition` (§3.1, p. 20; §3.2, pp. 21–22; §5.1, pp. 25–26). Defines the
output handle `PartitionResult` and word-encoded argument/state types via `word_enc_structure` for
post-DJP round emission (`partRoundFinish`, `partRunRound`), the outer vertex scan
(`partOuterStep`, `partRunOuterLoop`), the remaining-edge scan (`partEmitRemStep`,
`partRunRemLoop`), and the top-level `partitionProg` consuming `connectedComponentsProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartitionResult`,
  `PartCursor`, `PartWriteLocalEdgeArgs`, `PartMaybeEmitLocalArgs`, `PartEmitVertEnv`,
  `PartEdgeBufEnv`, `PartMarkDeadEnv`, `PartWriteRoundMetaArgs`, `PartEmitCompArgs`,
  `PartEmitCorrLoopArgs`, `PartMarkDeadLoopArgs`, `PartOuterState`, `PartRoundFinishArgs`:
  public word-encoded output, outer state, and round-emission argument structures.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partWriteLocalEdge`,
  `partMaybeEmitLocal`, `partEmitEdgeStep`, `partEmitVertStep`, `partEmitCorrStep`,
  `partMarkDeadStep`, `partWriteRoundMeta`, `partEmitComp`, `partEmitCorrLoop`,
  `partMarkDeadLoop`, `partRoundFinish`, `partRunRound`: per-round emission, corrupted-edge
  collection, dead marking, metadata writing, and full-round execution.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partOuterStep`, `partRunOuterLoop`,
  `partEmitRemStep`, `partRunRemLoop`: outer vertex loop and post-loop remaining-edge collector.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partitionProg`: top-level Word-RAM `Partition`
  driver returning `PartitionResult`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_partRoundFinish`,
  `realizes_partRunRound`, `realizes_partitionProg`: uniform `Realizes .exact` certificates
  with `work = 0`.

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-! ## Word-Encoded Result, Emission, and Outer-Loop Types -/

/-- Output handle returned by the Word-RAM `Partition` subroutine (`partitionProg`). -/
structure PartitionResult where
  /-- Number of partition rounds / components `k ≤ n`. -/
  numComps : ℕ
  /-- Base of stride-3 metadata `(v_i, m_i, cEdgeBase_i)` for `i < numComps`. -/
  compMetaBase : ℕ
  /-- Base of stride-1 `cLiftBase_i` pointers (`v_i` global vertex IDs each) for `i < numComps`. -/
  liftMetaBase : ℕ
  /-- Base of stride-4 corrupted edge array `M_C` (`HoldsIndexedEdges`). -/
  mcBase : ℕ
  /-- Length of `M_C` (`≤ m / 8`). -/
  mcLen : ℕ
  /-- Base of stride-4 remaining inter-component edge array `H_rem` (`HoldsIndexedEdges`). -/
  hRemBase : ℕ
  /-- Length of `H_rem` (`≤ m`). -/
  hRemLen : ℕ
  /-- Base of conglomerate label array `conglom[0..n) : Fin nConglom`. -/
  conglomBase : ℕ
  /-- Number of conglomerate components (`≤ n`). -/
  nConglom : ℕ
  deriving DecidableEq

/-- Faithful nine-word encoding of `PartitionResult`. -/
word_enc_structure encPartitionResult : PartitionResult where
  numComps : wordWords,
  compMetaBase : wordWords,
  liftMetaBase : wordWords,
  mcBase : wordWords,
  mcLen : wordWords,
  hRemBase : wordWords,
  hRemLen : wordWords,
  conglomBase : wordWords,
  nConglom : wordWords

instance : WordEncoding PartitionResult := ⟨9, encPartitionResult⟩

/-- Two-word loop cursor `(idx, count)` used by CSR, edge, and vertex emission loops. -/
structure PartCursor where
  /-- Current loop index. -/
  idx : ℕ
  /-- Cumulative output counter. -/
  count : ℕ
  deriving DecidableEq

/-- Faithful two-word encoding of `PartCursor`. -/
word_enc_structure encPartCursor : PartCursor where
  idx : wordWords,
  count : wordWords

instance : WordEncoding PartCursor := ⟨2, encPartCursor⟩

/-- Arguments for `partWriteLocalEdge`. -/
structure PartWriteLocalEdgeArgs where
  /-- Base address of global stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of `localIdx` map. -/
  localBase : ℕ
  /-- Base address of destination local edge slice. -/
  dstBase : ℕ
  /-- Global edge index `eIdx`. -/
  eIdx : ℕ
  /-- Current cumulative component edge count `cEdgeLen`. -/
  cEdgeLen : ℕ
  deriving DecidableEq

/-- Faithful five-word encoding of `PartWriteLocalEdgeArgs`. -/
word_enc_structure encPartWriteLocalEdgeArgs : PartWriteLocalEdgeArgs where
  edgeBase : wordWords,
  localBase : wordWords,
  dstBase : wordWords,
  eIdx : wordWords,
  cEdgeLen : wordWords

instance : WordEncoding PartWriteLocalEdgeArgs := ⟨5, encPartWriteLocalEdgeArgs⟩

/-- Arguments for `partMaybeEmitLocal`. -/
structure PartMaybeEmitLocalArgs where
  /-- Base address of global stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of partition workspace buffer. -/
  bufBase : ℕ
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Number of edges `m`. -/
  m : ℕ
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  /-- Neighbor endpoint vertex index. -/
  nb : ℕ
  /-- Edge index `eIdx`. -/
  eIdx : ℕ
  /-- Current cumulative component edge count `cEdgeLen`. -/
  cEdgeLen : ℕ
  deriving DecidableEq

/-- Faithful eight-word encoding of `PartMaybeEmitLocalArgs`. -/
word_enc_structure encPartMaybeEmitLocalArgs : PartMaybeEmitLocalArgs where
  edgeBase : wordWords,
  bufBase : wordWords,
  n : wordWords,
  m : wordWords,
  cid : wordWords,
  nb : wordWords,
  eIdx : wordWords,
  cEdgeLen : wordWords

instance : WordEncoding PartMaybeEmitLocalArgs := ⟨8, encPartMaybeEmitLocalArgs⟩

/-- Environment for per-vertex edge emission (`partEmitVertStep` and `partEmitComp`). -/
structure PartEmitVertEnv where
  /-- Base address of CSR offset array. -/
  offBase : ℕ
  /-- Base address of CSR half-edge array. -/
  adjBase : ℕ
  /-- Base address of global stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of partition workspace buffer. -/
  bufBase : ℕ
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Number of edges `m`. -/
  m : ℕ
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  deriving DecidableEq

/-- Faithful seven-word encoding of `PartEmitVertEnv`. -/
word_enc_structure encPartEmitVertEnv : PartEmitVertEnv where
  offBase : wordWords,
  adjBase : wordWords,
  edgeBase : wordWords,
  bufBase : wordWords,
  n : wordWords,
  m : wordWords,
  cid : wordWords

instance : WordEncoding PartEmitVertEnv := ⟨7, encPartEmitVertEnv⟩

/-- Shared environment for edge-flag loops (`partEmitCorrStep`, `partEmitRemStep`,
`partRunRemLoop`). -/
structure PartEdgeBufEnv where
  /-- Base address of global stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Base address of partition workspace buffer. -/
  bufBase : ℕ
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Number of edges `m`. -/
  m : ℕ
  deriving DecidableEq

/-- Faithful four-word encoding of `PartEdgeBufEnv`. -/
word_enc_structure encPartEdgeBufEnv : PartEdgeBufEnv where
  edgeBase : wordWords,
  bufBase : wordWords,
  n : wordWords,
  m : wordWords

instance : WordEncoding PartEdgeBufEnv := ⟨4, encPartEdgeBufEnv⟩

/-- Environment for `partMarkDeadStep` and `partMarkDeadLoop`. -/
structure PartMarkDeadEnv where
  /-- Base address of partition workspace buffer. -/
  bufBase : ℕ
  /-- Number of vertices `n`. -/
  n : ℕ
  deriving DecidableEq

/-- Faithful two-word encoding of `PartMarkDeadEnv`. -/
word_enc_structure encPartMarkDeadEnv : PartMarkDeadEnv where
  bufBase : wordWords,
  n : wordWords

instance : WordEncoding PartMarkDeadEnv := ⟨2, encPartMarkDeadEnv⟩

/-- Arguments for `partWriteRoundMeta`. -/
structure PartWriteRoundMetaArgs where
  /-- Base address of partition workspace buffer. -/
  bufBase : ℕ
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Zero-based round index `numComps`. -/
  numComps : ℕ
  /-- Vertex count `numVerts` of this component. -/
  numVerts : ℕ
  /-- Local edge count `numLocalEdges` of this component. -/
  numLocalEdges : ℕ
  /-- Base address of this component's local edge slice. -/
  cEdgeBase : ℕ
  /-- Base address of this component's global vertex lift slice. -/
  cLiftBase : ℕ
  deriving DecidableEq

/-- Faithful seven-word encoding of `PartWriteRoundMetaArgs`. -/
word_enc_structure encPartWriteRoundMetaArgs : PartWriteRoundMetaArgs where
  bufBase : wordWords,
  n : wordWords,
  numComps : wordWords,
  numVerts : wordWords,
  numLocalEdges : wordWords,
  cEdgeBase : wordWords,
  cLiftBase : wordWords

instance : WordEncoding PartWriteRoundMetaArgs := ⟨7, encPartWriteRoundMetaArgs⟩

/-- Arguments for `partEmitComp`. -/
structure PartEmitCompArgs where
  /-- Vertex/edge emission environment. -/
  env : PartEmitVertEnv
  /-- Stopping flag (`≠ 0` iff the last vertex was previously claimed). -/
  hitPrev : ℕ
  /-- Component vertex count `size`. -/
  size : ℕ
  /-- Cumulative component edge count before this round. -/
  cEdgeLen : ℕ
  deriving DecidableEq

/-- Faithful ten-word encoding of `PartEmitCompArgs`. -/
word_enc_structure encPartEmitCompArgs : PartEmitCompArgs where
  env : encPartEmitVertEnv,
  hitPrev : wordWords,
  size : wordWords,
  cEdgeLen : wordWords

instance : WordEncoding PartEmitCompArgs := ⟨10, encPartEmitCompArgs⟩

/-- Arguments for `partEmitCorrLoop`. -/
structure PartEmitCorrLoopArgs where
  /-- Edge-buffer environment. -/
  env : PartEdgeBufEnv
  /-- Number of collected corrupted item entries to scan. -/
  numCorr : ℕ
  /-- Cumulative `M_C` edge count before this round. -/
  mcLen : ℕ
  deriving DecidableEq

/-- Faithful six-word encoding of `PartEmitCorrLoopArgs`. -/
word_enc_structure encPartEmitCorrLoopArgs : PartEmitCorrLoopArgs where
  env : encPartEdgeBufEnv,
  numCorr : wordWords,
  mcLen : wordWords

instance : WordEncoding PartEmitCorrLoopArgs := ⟨6, encPartEmitCorrLoopArgs⟩

/-- Arguments for `partMarkDeadLoop`. -/
structure PartMarkDeadLoopArgs where
  /-- Dead-marking buffer environment. -/
  env : PartMarkDeadEnv
  /-- Component vertex count `size`. -/
  size : ℕ
  /-- Cumulative `cLiftAll` length before this round. -/
  cLiftLen : ℕ
  deriving DecidableEq

/-- Faithful four-word encoding of `PartMarkDeadLoopArgs`. -/
word_enc_structure encPartMarkDeadLoopArgs : PartMarkDeadLoopArgs where
  env : encPartMarkDeadEnv,
  size : wordWords,
  cLiftLen : wordWords

instance : WordEncoding PartMarkDeadLoopArgs := ⟨4, encPartMarkDeadLoopArgs⟩

/-- Mutable state carried across rounds of the outer vertex scan. -/
structure PartOuterState where
  /-- Current outer vertex cursor `u`. -/
  u : ℕ
  /-- Number of completed rounds/components. -/
  numComps : ℕ
  /-- Cumulative emitted local edge count across rounds. -/
  cEdgeLen : ℕ
  /-- Cumulative emitted lift vertex count across rounds. -/
  cLiftLen : ℕ
  /-- Cumulative emitted corrupted edge count `mcLen`. -/
  mcLen : ℕ
  /-- Cumulative DJP tree edge count `tLen`. -/
  tLen : ℕ
  /-- Soft-Heap handle with `firstRoot = 0` between rounds. -/
  sh : SHHandle
  deriving DecidableEq

/-- Faithful twelve-word encoding of `PartOuterState`. -/
word_enc_structure encPartOuterState : PartOuterState where
  u : wordWords,
  numComps : wordWords,
  cEdgeLen : wordWords,
  cLiftLen : wordWords,
  mcLen : wordWords,
  tLen : wordWords,
  sh : (WordEncoding.encode (α := SHHandle))

instance : WordEncoding PartOuterState := ⟨12, encPartOuterState⟩

/-- Arguments for `partRoundFinish`. -/
structure PartRoundFinishArgs where
  /-- Partition environment. -/
  env : PartEnv
  /-- Outer state prior to this round. -/
  outer : PartOuterState
  /-- Soft-Heap `nodeCount` at the start of this round. -/
  nc0 : ℕ
  /-- Final DJP loop state for this round. -/
  djp : PartDjpState
  deriving DecidableEq

/-- Faithful thirty-word encoding of `PartRoundFinishArgs`. -/
word_enc_structure encPartRoundFinishArgs : PartRoundFinishArgs where
  env : encPartEnv,
  outer : encPartOuterState,
  nc0 : wordWords,
  djp : encPartDjpState

instance : WordEncoding PartRoundFinishArgs := ⟨30, encPartRoundFinishArgs⟩

/-! ## Component, Corrupted, and Remaining Edge Emission Helpers -/

/-- Emits one compacted local `IndexedEdge` at `d.dstBase + 4 * d.cEdgeLen`. -/
def partWriteLocalEdge (d : PartWriteLocalEdgeArgs) : Memory.Prog ℕ := do
  let u ← Memory.read (d.edgeBase + 4 * d.eIdx)
  let v ← Memory.read (d.edgeBase + 4 * d.eIdx + 1)
  let lu ← Memory.read (d.localBase + u)
  let lv ← Memory.read (d.localBase + v)
  let wt ← Memory.read (d.edgeBase + 4 * d.eIdx + 2)
  let eid ← Memory.read (d.edgeBase + 4 * d.eIdx + 3)
  partWriteStride4 ⟨d.dstBase, d.cEdgeLen, lu, lv, wt, eid⟩
  pure (d.cEdgeLen + 1)

/-- Native safety domain for `partWriteLocalEdge`. -/
def partWriteLocalEdgeSafe (w : ℕ) (d : PartWriteLocalEdgeArgs) (s : Memory.State) : Prop :=
  let u := s.mem (d.edgeBase + 4 * d.eIdx)
  let v := s.mem (d.edgeBase + 4 * d.eIdx + 1)
  Fits w 16 ∧ Fits w (d.cEdgeLen + 1) ∧
    d.edgeBase + 4 * d.eIdx + 3 < s.frontier ∧
    d.localBase + u < s.frontier ∧ d.localBase + v < s.frontier ∧
    d.dstBase + 4 * d.cEdgeLen + 3 < s.frontier

private theorem realizes_partWriteLocalEdge_history : Realizes .exact
    partWriteLocalEdge WordEncoding.encode WordEncoding.encode
    (fun w d s => partWriteLocalEdgeSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partWriteLocalEdge d)))
    (fun _ _ => 0) := by
  unfold partWriteLocalEdge
  realize [realizes_partWriteStride4]
  all_goals
    obtain ⟨⟨h16, hc1, he_lt, hu_lt, hv_lt, hd_lt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | (rw [partWriteStride4Safe_def]; exact ⟨h16, hd_lt⟩)
    | fits

/-- `partWriteLocalEdge` is uniformly realized with `work = 0`. -/
private theorem realizes_partWriteLocalEdge : Realizes .exact
    partWriteLocalEdge WordEncoding.encode WordEncoding.encode
    partWriteLocalEdgeSafe (fun _ _ => 0) :=
  realizes_partWriteLocalEdge_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partWriteLocalEdge`. -/
theorem partWriteLocalEdge_def (d : PartWriteLocalEdgeArgs) : partWriteLocalEdge d =
    (Memory.read (d.edgeBase + 4 * d.eIdx) >>= fun u =>
      Memory.read (d.edgeBase + 4 * d.eIdx + 1) >>= fun v =>
        Memory.read (d.localBase + u) >>= fun lu =>
          Memory.read (d.localBase + v) >>= fun lv =>
            Memory.read (d.edgeBase + 4 * d.eIdx + 2) >>= fun wt =>
              Memory.read (d.edgeBase + 4 * d.eIdx + 3) >>= fun eid =>
                partWriteStride4 ⟨d.dstBase, d.cEdgeLen, lu, lv, wt, eid⟩ >>= fun _ =>
                  pure (d.cEdgeLen + 1)) := by
  unfold partWriteLocalEdge
  rfl

/-- Unfolding equation for `partWriteLocalEdgeSafe`. -/
theorem partWriteLocalEdgeSafe_def (w : ℕ) (d : PartWriteLocalEdgeArgs) (s : Memory.State) :
    partWriteLocalEdgeSafe w d s =
      (let u := s.mem (d.edgeBase + 4 * d.eIdx)
       let v := s.mem (d.edgeBase + 4 * d.eIdx + 1)
       Fits w 16 ∧ Fits w (d.cEdgeLen + 1) ∧
         d.edgeBase + 4 * d.eIdx + 3 < s.frontier ∧
         d.localBase + u < s.frontier ∧ d.localBase + v < s.frontier ∧
         d.dstBase + 4 * d.cEdgeLen + 3 < s.frontier) := by
  unfold partWriteLocalEdgeSafe
  rfl

/-- Conditionally claims edge `d.eIdx` for component `d.cid` when active and `inCur[d.nb] =
d.cid`. -/
def partMaybeEmitLocal (d : PartMaybeEmitLocalArgs) : Memory.Prog ℕ := do
  let st ← Memory.read (d.bufBase + 14 * d.n + d.eIdx)
  let inNb ← Memory.read (d.bufBase + d.n + d.nb)
  if st = 0 ∧ inNb = d.cid then
    Memory.write (d.bufBase + 14 * d.n + d.eIdx) 1
    partWriteLocalEdge
      ⟨d.edgeBase, d.bufBase + 2 * d.n, d.bufBase + 14 * d.n + 2 * d.m, d.eIdx, d.cEdgeLen⟩
  else
    pure d.cEdgeLen

/-- Native safety domain for `partMaybeEmitLocal`. -/
def partMaybeEmitLocalSafe (w : ℕ) (d : PartMaybeEmitLocalArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.bufBase + 14 * d.n + 14 * d.m) ∧
    d.bufBase + 14 * d.n + d.eIdx < s.frontier ∧ d.bufBase + d.n + d.nb < s.frontier ∧
    (s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 → s.mem (d.bufBase + d.n + d.nb) = d.cid →
      partWriteLocalEdgeSafe w
        ⟨d.edgeBase, d.bufBase + 2 * d.n, d.bufBase + 14 * d.n + 2 * d.m, d.eIdx, d.cEdgeLen⟩
        ⟨Function.update s.mem (d.bufBase + 14 * d.n + d.eIdx) 1, s.frontier⟩)

private theorem realizes_partMaybeEmitLocal_history : Realizes .exact
    partMaybeEmitLocal WordEncoding.encode WordEncoding.encode
    (fun w d s => partMaybeEmitLocalSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partMaybeEmitLocal d)))
    (fun _ _ => 0) := by
  unfold partMaybeEmitLocal
  realize [realizes_partWriteLocalEdge]
  all_goals
    obtain ⟨⟨h16, _, hst_lt, hnb_lt, hwle⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.write, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partMaybeEmitLocal` is uniformly realized with `work = 0`. -/
private theorem realizes_partMaybeEmitLocal : Realizes .exact
    partMaybeEmitLocal WordEncoding.encode WordEncoding.encode
    partMaybeEmitLocalSafe (fun _ _ => 0) :=
  realizes_partMaybeEmitLocal_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partMaybeEmitLocal`. -/
theorem partMaybeEmitLocal_def (d : PartMaybeEmitLocalArgs) : partMaybeEmitLocal d =
    (Memory.read (d.bufBase + 14 * d.n + d.eIdx) >>= fun st =>
      Memory.read (d.bufBase + d.n + d.nb) >>= fun inNb =>
        if st = 0 ∧ inNb = d.cid then
          Memory.write (d.bufBase + 14 * d.n + d.eIdx) 1 >>= fun _ =>
            partWriteLocalEdge
              ⟨d.edgeBase, d.bufBase + 2 * d.n, d.bufBase + 14 * d.n + 2 * d.m,
                d.eIdx, d.cEdgeLen⟩
        else pure d.cEdgeLen) := by
  unfold partMaybeEmitLocal
  rfl

/-- Unfolding equation for `partMaybeEmitLocalSafe`. -/
theorem partMaybeEmitLocalSafe_def (w : ℕ) (d : PartMaybeEmitLocalArgs) (s : Memory.State) :
    partMaybeEmitLocalSafe w d s =
      (Fits w 16 ∧ Fits w (d.bufBase + 14 * d.n + 14 * d.m) ∧
        d.bufBase + 14 * d.n + d.eIdx < s.frontier ∧ d.bufBase + d.n + d.nb < s.frontier ∧
        (s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 → s.mem (d.bufBase + d.n + d.nb) = d.cid →
          partWriteLocalEdgeSafe w
            ⟨d.edgeBase, d.bufBase + 2 * d.n, d.bufBase + 14 * d.n + 2 * d.m, d.eIdx, d.cEdgeLen⟩
            ⟨Function.update s.mem (d.bufBase + 14 * d.n + d.eIdx) 1, s.frontier⟩)) := by
  unfold partMaybeEmitLocalSafe
  rfl

/-- Single CSR half-edge scan step emitting internal edges of `V_i` into `C_i`. -/
def partEmitEdgeStep (d : PartAdjEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let nb ← Memory.read (env.adjBase + 2 * cur.idx)
  let eIdx ← Memory.read (env.adjBase + 2 * cur.idx + 1)
  let c' ← partMaybeEmitLocal
    ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid, nb, eIdx, cur.count⟩
  pure ⟨cur.idx + 1, c'⟩

/-- Native safety domain for `partEmitEdgeStep`. -/
def partEmitEdgeStepSafe (w : ℕ) (d : PartAdjEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ env.adjBase + 2 * cur.idx + 1 < s.frontier ∧
    partMaybeEmitLocalSafe w
      ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid,
        s.mem (env.adjBase + 2 * cur.idx), s.mem (env.adjBase + 2 * cur.idx + 1), cur.count⟩ s

private theorem realizes_partEmitEdgeStep_history : Realizes .exact
    partEmitEdgeStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitEdgeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitEdgeStep d)))
    (fun _ _ => 0) := by
  unfold partEmitEdgeStep
  realize [realizes_partMaybeEmitLocal]
  all_goals
    obtain ⟨⟨h16, hj1, hadj_lt, hme⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partEmitEdgeStep` is uniformly realized with `work = 0`. -/
private theorem realizes_partEmitEdgeStep : Realizes .exact
    partEmitEdgeStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitEdgeStepSafe (fun _ _ => 0) :=
  realizes_partEmitEdgeStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partEmitEdgeStep`. -/
theorem partEmitEdgeStep_def (d : PartAdjEnv × PartCursor) : partEmitEdgeStep d =
    (Memory.read (d.1.adjBase + 2 * d.2.idx) >>= fun nb =>
      Memory.read (d.1.adjBase + 2 * d.2.idx + 1) >>= fun eIdx =>
        partMaybeEmitLocal
          ⟨d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid, nb, eIdx, d.2.count⟩ >>= fun c' =>
            pure ⟨d.2.idx + 1, c'⟩) := by
  unfold partEmitEdgeStep
  rfl

/-- Unfolding equation for `partEmitEdgeStepSafe`. -/
theorem partEmitEdgeStepSafe_def (w : ℕ) (d : PartAdjEnv × PartCursor) (s : Memory.State) :
    partEmitEdgeStepSafe w d s =
      (Fits w 16 ∧ Fits w (d.2.idx + 1) ∧ d.1.adjBase + 2 * d.2.idx + 1 < s.frontier ∧
        partMaybeEmitLocalSafe w
          ⟨d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid,
            s.mem (d.1.adjBase + 2 * d.2.idx),
            s.mem (d.1.adjBase + 2 * d.2.idx + 1), d.2.count⟩ s) := by
  unfold partEmitEdgeStepSafe
  rfl

/-- Scans one live vertex `compVerts[d.2.idx]`'s CSR slice to emit internal edges of `C_i`. -/
def partEmitVertStep (d : PartEmitVertEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let u ← Memory.read (env.bufBase + 3 * env.n + cur.idx)
  let startJ ← Memory.read (env.offBase + u)
  let endJ ← Memory.read (env.offBase + u + 1)
  let res ← iterate partEmitEdgeStep
    ⟨env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, env.cid⟩
    (endJ - startJ) ⟨startJ, cur.count⟩
  pure ⟨cur.idx + 1, res.count⟩

/-- Native safety domain for `partEmitVertStep`. -/
def partEmitVertStepSafe (w : ℕ) (d : PartEmitVertEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  let u := s.mem (env.bufBase + 3 * env.n + cur.idx)
  let startJ := s.mem (env.offBase + u)
  let endJ := s.mem (env.offBase + u + 1)
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ env.bufBase + 3 * env.n + cur.idx < s.frontier ∧
    env.offBase + u + 1 < s.frontier ∧ startJ ≤ endJ ∧
    iterationSafe partEmitEdgeStep partEmitEdgeStepSafe w
      ⟨env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, env.cid⟩
      (endJ - startJ) ⟨startJ, cur.count⟩ s

private theorem realizes_partEmitVertStep_history : Realizes .exact
    partEmitVertStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitVertStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitVertStep d)))
    (fun _ _ => 0) := by
  unfold partEmitVertStep
  realize [realizes_partEmitEdgeStep]
  all_goals
    obtain ⟨⟨h16, ht1, hcv_lt, hoff_lt, hle, hiter⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | exact iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => hs)
    | fits

/-- `partEmitVertStep` is uniformly realized with `work = 0`. -/
private theorem realizes_partEmitVertStep : Realizes .exact
    partEmitVertStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitVertStepSafe (fun _ _ => 0) :=
  realizes_partEmitVertStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partEmitVertStep`. -/
theorem partEmitVertStep_def (d : PartEmitVertEnv × PartCursor) : partEmitVertStep d =
    (Memory.read (d.1.bufBase + 3 * d.1.n + d.2.idx) >>= fun u =>
      Memory.read (d.1.offBase + u) >>= fun startJ =>
        Memory.read (d.1.offBase + u + 1) >>= fun endJ =>
          iterate partEmitEdgeStep
            ⟨d.1.adjBase, d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid⟩
            (endJ - startJ) ⟨startJ, d.2.count⟩ >>= fun res =>
              pure ⟨d.2.idx + 1, res.count⟩) := by
  unfold partEmitVertStep
  rfl

/-- Unfolding equation for `partEmitVertStepSafe`. -/
theorem partEmitVertStepSafe_def (w : ℕ) (d : PartEmitVertEnv × PartCursor) (s : Memory.State) :
    partEmitVertStepSafe w d s =
      (let u := s.mem (d.1.bufBase + 3 * d.1.n + d.2.idx)
       let startJ := s.mem (d.1.offBase + u)
       let endJ := s.mem (d.1.offBase + u + 1)
       Fits w 16 ∧ Fits w (d.2.idx + 1) ∧ d.1.bufBase + 3 * d.1.n + d.2.idx < s.frontier ∧
         d.1.offBase + u + 1 < s.frontier ∧ startJ ≤ endJ ∧
         iterationSafe partEmitEdgeStep partEmitEdgeStepSafe w
           ⟨d.1.adjBase, d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid⟩
           (endJ - startJ) ⟨startJ, d.2.count⟩ s) := by
  unfold partEmitVertStepSafe
  rfl

/-- Processes one corrupted edge index from `corrBuf[d.2.idx]`, copying to `M_C` if
`edgeState = 0`. -/
def partEmitCorrStep (d : PartEdgeBufEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let eIdx ← Memory.read (env.bufBase + 14 * env.n + env.m + cur.idx)
  let st ← Memory.read (env.bufBase + 14 * env.n + eIdx)
  if st = 0 then
    Memory.write (env.bufBase + 14 * env.n + eIdx) 2
    partCopyIndexedEdge ⟨env.edgeBase, env.bufBase + 14 * env.n + 6 * env.m, eIdx, cur.count⟩
    pure ⟨cur.idx + 1, cur.count + 1⟩
  else
    pure ⟨cur.idx + 1, cur.count⟩

/-- Native safety domain for `partEmitCorrStep`. -/
def partEmitCorrStepSafe (w : ℕ) (d : PartEdgeBufEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  let eIdx := s.mem (env.bufBase + 14 * env.n + env.m + cur.idx)
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ Fits w (cur.count + 1) ∧
    Fits w (env.bufBase + 14 * env.n + 14 * env.m) ∧
    env.bufBase + 14 * env.n + env.m + cur.idx < s.frontier ∧
    env.bufBase + 14 * env.n + eIdx < s.frontier ∧
    (s.mem (env.bufBase + 14 * env.n + eIdx) = 0 →
      partCopyIndexedEdgeSafe w
        ⟨env.edgeBase, env.bufBase + 14 * env.n + 6 * env.m, eIdx, cur.count⟩
        ⟨Function.update s.mem (env.bufBase + 14 * env.n + eIdx) 2, s.frontier⟩)

private theorem realizes_partEmitCorrStep_history : Realizes .exact
    partEmitCorrStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitCorrStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitCorrStep d)))
    (fun _ _ => 0) := by
  unfold partEmitCorrStep
  realize [realizes_partCopyIndexedEdge]
  all_goals
    obtain ⟨⟨h16, ht1, hmc1, _, hcb_lt, hst_lt, hcopy⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partEmitCorrStep` is uniformly realized with `work = 0`. -/
private theorem realizes_partEmitCorrStep : Realizes .exact
    partEmitCorrStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitCorrStepSafe (fun _ _ => 0) :=
  realizes_partEmitCorrStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partEmitCorrStep`. -/
theorem partEmitCorrStep_def (d : PartEdgeBufEnv × PartCursor) : partEmitCorrStep d =
    (Memory.read (d.1.bufBase + 14 * d.1.n + d.1.m + d.2.idx) >>= fun eIdx =>
      Memory.read (d.1.bufBase + 14 * d.1.n + eIdx) >>= fun st =>
        if st = 0 then
          Memory.write (d.1.bufBase + 14 * d.1.n + eIdx) 2 >>= fun _ =>
            partCopyIndexedEdge
              ⟨d.1.edgeBase, d.1.bufBase + 14 * d.1.n + 6 * d.1.m, eIdx, d.2.count⟩ >>= fun _ =>
              pure ⟨d.2.idx + 1, d.2.count + 1⟩
        else
          pure ⟨d.2.idx + 1, d.2.count⟩) := by
  unfold partEmitCorrStep
  rfl

/-- Unfolding equation for `partEmitCorrStepSafe`. -/
theorem partEmitCorrStepSafe_def (w : ℕ) (d : PartEdgeBufEnv × PartCursor) (s : Memory.State) :
    partEmitCorrStepSafe w d s =
      (let eIdx := s.mem (d.1.bufBase + 14 * d.1.n + d.1.m + d.2.idx)
       Fits w 16 ∧ Fits w (d.2.idx + 1) ∧ Fits w (d.2.count + 1) ∧
         Fits w (d.1.bufBase + 14 * d.1.n + 14 * d.1.m) ∧
         d.1.bufBase + 14 * d.1.n + d.1.m + d.2.idx < s.frontier ∧
         d.1.bufBase + 14 * d.1.n + eIdx < s.frontier ∧
         (s.mem (d.1.bufBase + 14 * d.1.n + eIdx) = 0 →
           partCopyIndexedEdgeSafe w
             ⟨d.1.edgeBase, d.1.bufBase + 14 * d.1.n + 6 * d.1.m, eIdx, d.2.count⟩
             ⟨Function.update s.mem (d.1.bufBase + 14 * d.1.n + eIdx) 2, s.frontier⟩)) := by
  unfold partEmitCorrStepSafe
  rfl

/-- Copies `compVerts[d.2.idx]` to `cLiftAll[d.2.count]` and marks `dead[v] := 1`. -/
def partMarkDeadStep (d : PartMarkDeadEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let v ← Memory.read (env.bufBase + 3 * env.n + cur.idx)
  Memory.write (env.bufBase + 4 * env.n + cur.count) v
  Memory.write (env.bufBase + v) 1
  pure ⟨cur.idx + 1, cur.count + 1⟩

/-- Native safety domain for `partMarkDeadStep`. -/
def partMarkDeadStepSafe (w : ℕ) (d : PartMarkDeadEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  let v := s.mem (env.bufBase + 3 * env.n + cur.idx)
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ Fits w (cur.count + 1) ∧
    env.bufBase + 3 * env.n + cur.idx < s.frontier ∧
    env.bufBase + 4 * env.n + cur.count < s.frontier ∧
    env.bufBase + v < s.frontier

private theorem realizes_partMarkDeadStep_history : Realizes .exact
    partMarkDeadStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partMarkDeadStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partMarkDeadStep d)))
    (fun _ _ => 0) := by
  unfold partMarkDeadStep
  realize
  all_goals
    obtain ⟨⟨h16, ht1, hl1, hcv_lt, hcl_lt, hd_lt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

/-- `partMarkDeadStep` is uniformly realized with `work = 0`. -/
private theorem realizes_partMarkDeadStep : Realizes .exact
    partMarkDeadStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partMarkDeadStepSafe (fun _ _ => 0) :=
  realizes_partMarkDeadStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partMarkDeadStep`. -/
theorem partMarkDeadStep_def (d : PartMarkDeadEnv × PartCursor) : partMarkDeadStep d =
    (Memory.read (d.1.bufBase + 3 * d.1.n + d.2.idx) >>= fun v =>
      Memory.write (d.1.bufBase + 4 * d.1.n + d.2.count) v >>= fun _ =>
        Memory.write (d.1.bufBase + v) 1 >>= fun _ =>
          pure ⟨d.2.idx + 1, d.2.count + 1⟩) := by
  unfold partMarkDeadStep
  rfl

/-- Unfolding equation for `partMarkDeadStepSafe`. -/
theorem partMarkDeadStepSafe_def (w : ℕ) (d : PartMarkDeadEnv × PartCursor) (s : Memory.State) :
    partMarkDeadStepSafe w d s =
      (let v := s.mem (d.1.bufBase + 3 * d.1.n + d.2.idx)
       Fits w 16 ∧ Fits w (d.2.idx + 1) ∧ Fits w (d.2.count + 1) ∧
         d.1.bufBase + 3 * d.1.n + d.2.idx < s.frontier ∧
         d.1.bufBase + 4 * d.1.n + d.2.count < s.frontier ∧
         d.1.bufBase + v < s.frontier) := by
  unfold partMarkDeadStepSafe
  rfl

/-- Writes stride-3 component metadata and stride-1 lift pointer for round `d.numComps`. -/
def partWriteRoundMeta (d : PartWriteRoundMetaArgs) : Memory.Prog Unit := do
  Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps) d.numVerts
  Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps + 1) d.numLocalEdges
  Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps + 2) d.cEdgeBase
  Memory.write (d.bufBase + 9 * d.n + d.numComps) d.cLiftBase

/-- Native safety domain for `partWriteRoundMeta`. -/
def partWriteRoundMetaSafe (w : ℕ) (d : PartWriteRoundMetaArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.bufBase + 6 * d.n + 3 * d.numComps + 2 < s.frontier ∧
    d.bufBase + 9 * d.n + d.numComps < s.frontier

/-- `partWriteRoundMeta` is uniformly realized with `work = 0`. -/
private theorem realizes_partWriteRoundMeta : Realizes .exact
    partWriteRoundMeta WordEncoding.encode WordEncoding.encode
    partWriteRoundMetaSafe (fun _ _ => 0) := by
  unfold partWriteRoundMeta
  realize
  all_goals
    have h16 := h.1
    have hcm_lt := h.2.1
    have hlm_lt := h.2.2
    have hfront := hmem.frontier_fits
    fits

/-- Unfolding equation for `partWriteRoundMeta`. -/
theorem partWriteRoundMeta_def (d : PartWriteRoundMetaArgs) : partWriteRoundMeta d =
    (Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps) d.numVerts >>= fun _ =>
      Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps + 1) d.numLocalEdges >>= fun _ =>
        Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps + 2) d.cEdgeBase >>= fun _ =>
          Memory.write (d.bufBase + 9 * d.n + d.numComps) d.cLiftBase) := by
  unfold partWriteRoundMeta
  rfl

/-- Unfolding equation for `partWriteRoundMetaSafe`. -/
theorem partWriteRoundMetaSafe_def (w : ℕ) (d : PartWriteRoundMetaArgs) (s : Memory.State) :
    partWriteRoundMetaSafe w d s =
      (Fits w 16 ∧ d.bufBase + 6 * d.n + 3 * d.numComps + 2 < s.frontier ∧
        d.bufBase + 9 * d.n + d.numComps < s.frontier) := by
  unfold partWriteRoundMetaSafe
  rfl

/-- Emits component `C_i` edges from `liveCount` live vertices (`d.size` or `d.size - 1`). -/
def partEmitComp (d : PartEmitCompArgs) : Memory.Prog PartCursor := do
  if d.hitPrev = 0 then
    iterate partEmitVertStep d.env d.size ⟨0, d.cEdgeLen⟩
  else
    iterate partEmitVertStep d.env (d.size - 1) ⟨0, d.cEdgeLen⟩

/-- Native safety domain for `partEmitComp`. -/
def partEmitCompSafe (w : ℕ) (d : PartEmitCompArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ (d.hitPrev ≠ 0 → 1 ≤ d.size) ∧
    iterationSafe partEmitVertStep partEmitVertStepSafe w d.env
      (if d.hitPrev = 0 then d.size else d.size - 1) ⟨0, d.cEdgeLen⟩ s

/-- `partEmitComp` is uniformly realized with `work = 0`. -/
private theorem realizes_partEmitComp : Realizes .exact
    partEmitComp WordEncoding.encode WordEncoding.encode
    partEmitCompSafe (fun _ _ => 0) := by
  unfold partEmitComp
  realize [realizes_partEmitVertStep]
  all_goals
    obtain ⟨h16, hsub, hiter⟩ := h
    have hfront := hmem.frontier_fits
    first
    | (simp only [hc, ↓reduceIte] at hiter
       exact iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => hs))
    | exact hsub hc

/-- Unfolding equation for `partEmitComp`. -/
theorem partEmitComp_def (d : PartEmitCompArgs) : partEmitComp d =
    (if d.hitPrev = 0 then
      iterate partEmitVertStep d.env d.size ⟨0, d.cEdgeLen⟩
    else
      iterate partEmitVertStep d.env (d.size - 1) ⟨0, d.cEdgeLen⟩) := by
  unfold partEmitComp
  rfl

/-- Unfolding equation for `partEmitCompSafe`. -/
theorem partEmitCompSafe_def (w : ℕ) (d : PartEmitCompArgs) (s : Memory.State) :
    partEmitCompSafe w d s =
      (Fits w 16 ∧ (d.hitPrev ≠ 0 → 1 ≤ d.size) ∧
        iterationSafe partEmitVertStep partEmitVertStepSafe w d.env
          (if d.hitPrev = 0 then d.size else d.size - 1) ⟨0, d.cEdgeLen⟩ s) := by
  unfold partEmitCompSafe
  rfl

/-- Runs `partEmitCorrStep` over `d.numCorr` collected corrupted edges. -/
def partEmitCorrLoop (d : PartEmitCorrLoopArgs) : Memory.Prog PartCursor :=
  iterate partEmitCorrStep d.env d.numCorr ⟨0, d.mcLen⟩

/-- Native safety domain for `partEmitCorrLoop`. -/
def partEmitCorrLoopSafe (w : ℕ) (d : PartEmitCorrLoopArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    iterationSafe partEmitCorrStep partEmitCorrStepSafe w d.env d.numCorr ⟨0, d.mcLen⟩ s

/-- `partEmitCorrLoop` is uniformly realized with `work = 0`. -/
private theorem realizes_partEmitCorrLoop : Realizes .exact
    partEmitCorrLoop WordEncoding.encode WordEncoding.encode
    partEmitCorrLoopSafe (fun _ _ => 0) := by
  unfold partEmitCorrLoop
  realize [realizes_partEmitCorrStep]
  exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Unfolding equation for `partEmitCorrLoop`. -/
theorem partEmitCorrLoop_def (d : PartEmitCorrLoopArgs) : partEmitCorrLoop d =
    iterate partEmitCorrStep d.env d.numCorr ⟨0, d.mcLen⟩ := by
  unfold partEmitCorrLoop
  rfl

/-- Unfolding equation for `partEmitCorrLoopSafe`. -/
theorem partEmitCorrLoopSafe_def (w : ℕ) (d : PartEmitCorrLoopArgs) (s : Memory.State) :
    partEmitCorrLoopSafe w d s =
      (Fits w 16 ∧
        iterationSafe partEmitCorrStep partEmitCorrStepSafe w d.env d.numCorr ⟨0, d.mcLen⟩ s) := by
  unfold partEmitCorrLoopSafe
  rfl

/-- Runs `partMarkDeadStep` over `d.size` round vertices. -/
def partMarkDeadLoop (d : PartMarkDeadLoopArgs) : Memory.Prog PartCursor :=
  iterate partMarkDeadStep d.env d.size ⟨0, d.cLiftLen⟩

/-- Native safety domain for `partMarkDeadLoop`. -/
def partMarkDeadLoopSafe (w : ℕ) (d : PartMarkDeadLoopArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    iterationSafe partMarkDeadStep partMarkDeadStepSafe w d.env d.size ⟨0, d.cLiftLen⟩ s

/-- `partMarkDeadLoop` is uniformly realized with `work = 0`. -/
private theorem realizes_partMarkDeadLoop : Realizes .exact
    partMarkDeadLoop WordEncoding.encode WordEncoding.encode
    partMarkDeadLoopSafe (fun _ _ => 0) := by
  unfold partMarkDeadLoop
  realize [realizes_partMarkDeadStep]
  exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Unfolding equation for `partMarkDeadLoop`. -/
theorem partMarkDeadLoop_def (d : PartMarkDeadLoopArgs) : partMarkDeadLoop d =
    iterate partMarkDeadStep d.env d.size ⟨0, d.cLiftLen⟩ := by
  unfold partMarkDeadLoop
  rfl

/-- Unfolding equation for `partMarkDeadLoopSafe`. -/
theorem partMarkDeadLoopSafe_def (w : ℕ) (d : PartMarkDeadLoopArgs) (s : Memory.State) :
    partMarkDeadLoopSafe w d s =
      (Fits w 16 ∧
        iterationSafe partMarkDeadStep partMarkDeadStepSafe w d.env d.size ⟨0, d.cLiftLen⟩ s) := by
  unfold partMarkDeadLoopSafe
  rfl

/-! ## Round Finish, Full Round, Outer Loop, Remaining Edges, and Top-Level `partitionProg` -/

/-- Finalizes one dynamic-DJP round: emits `C_i`, collects/emits `M_i`, records `lift_i` and
dead vertices, writes round metadata, and resets `firstRoot := 0` for the next round. -/
def partRoundFinish (d : PartRoundFinishArgs) : Memory.Prog PartOuterState := do
  let env := d.env
  let outer := d.outer
  let djp := d.djp
  let cRes ← partEmitComp
    ⟨⟨env.offBase, env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, outer.numComps + 1⟩,
      djp.hitPrev, djp.size, outer.cEdgeLen⟩
  let numCorr ← shCollectCorrupted
    (djp.sh, d.nc0, env.bufBase + 14 * env.n + env.m, 0, 2 * env.m)
  let mRes ← partEmitCorrLoop
    ⟨⟨env.edgeBase, env.bufBase, env.n, env.m⟩, numCorr, outer.mcLen⟩
  let lRes ← partMarkDeadLoop ⟨⟨env.bufBase, env.n⟩, djp.size, outer.cLiftLen⟩
  partWriteRoundMeta
    ⟨env.bufBase, env.n, outer.numComps, djp.size, cRes.count - outer.cEdgeLen,
      env.bufBase + 14 * env.n + 2 * env.m + 4 * outer.cEdgeLen,
      env.bufBase + 4 * env.n + outer.cLiftLen⟩
  pure ⟨outer.u + 1, outer.numComps + 1, cRes.count, lRes.count, mRes.count, djp.tLen,
    ⟨djp.sh.itemBase, djp.sh.nodeBase, 0, djp.sh.itemCount, djp.sh.nodeCount,
      djp.sh.rankThreshold⟩⟩

/-- Native safety domain for `partRoundFinish`. -/
def partRoundFinishSafe (w : ℕ) (d : PartRoundFinishArgs) (s : Memory.State) : Prop :=
  let env := d.env
  let outer := d.outer
  let djp := d.djp
  let emitArgs : PartEmitCompArgs :=
    ⟨⟨env.offBase, env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, outer.numComps + 1⟩,
      djp.hitPrev, djp.size, outer.cEdgeLen⟩
  let s₁ := (Memory.spec 0).clientState s (partEmitComp emitArgs)
  let cRes := (Memory.spec 0).clientResult s (partEmitComp emitArgs)
  let corrArgs := (djp.sh, d.nc0, env.bufBase + 14 * env.n + env.m, 0, 2 * env.m)
  let numCorr := (Memory.spec 0).clientResult s₁ (shCollectCorrupted corrArgs)
  let s₂ := (Memory.spec 0).clientState s₁ (shCollectCorrupted corrArgs)
  let mcArgs : PartEmitCorrLoopArgs :=
    ⟨⟨env.edgeBase, env.bufBase, env.n, env.m⟩, numCorr, outer.mcLen⟩
  let s₃ := (Memory.spec 0).clientState s₂ (partEmitCorrLoop mcArgs)
  let deadArgs : PartMarkDeadLoopArgs := ⟨⟨env.bufBase, env.n⟩, djp.size, outer.cLiftLen⟩
  let s₄ := (Memory.spec 0).clientState s₃ (partMarkDeadLoop deadArgs)
  Fits w 16 ∧ Fits w (outer.u + 1) ∧ Fits w (outer.numComps + 1) ∧ Fits w (2 * env.m) ∧
    outer.cEdgeLen ≤ cRes.count ∧
    Fits w (env.bufBase + 14 * env.n + 14 * env.m) ∧
    Fits w (env.bufBase + 14 * env.n + 2 * env.m + 4 * outer.cEdgeLen) ∧
    Fits w (env.bufBase + 4 * env.n + outer.cLiftLen) ∧
    partEmitCompSafe w emitArgs s ∧
    shCollectCorruptedSafe w corrArgs s₁ ∧
    partEmitCorrLoopSafe w mcArgs s₂ ∧
    partMarkDeadLoopSafe w deadArgs s₃ ∧
    partWriteRoundMetaSafe w
      ⟨env.bufBase, env.n, outer.numComps, djp.size, cRes.count - outer.cEdgeLen,
        env.bufBase + 14 * env.n + 2 * env.m + 4 * outer.cEdgeLen,
        env.bufBase + 4 * env.n + outer.cLiftLen⟩ s₄

/-- `partRoundFinish` is uniformly realized with `work = 0`. -/
theorem realizes_partRoundFinish : Realizes .exact
    partRoundFinish WordEncoding.encode WordEncoding.encode
    partRoundFinishSafe (fun _ _ => 0) := by
  unfold partRoundFinish
  realize [realizes_partEmitComp, realizes_shCollectCorrupted,
    realizes_partEmitCorrLoop, realizes_partMarkDeadLoop, realizes_partWriteRoundMeta]
  all_goals first
    | exact h.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.2.2.2
    | (have h16 := h.1; have hu1 := h.2.1; have hnc1 := h.2.2.1
       have h2m := h.2.2.2.1; have hce := h.2.2.2.2.1
       have hbuf := h.2.2.2.2.2.1; have hcep := h.2.2.2.2.2.2.1
       have hclp := h.2.2.2.2.2.2.2.1; have hfront := hmem.frontier_fits; fits)

/-- Unfolding equation for `partRoundFinish`. -/
theorem partRoundFinish_def (d : PartRoundFinishArgs) : partRoundFinish d =
    (partEmitComp
      ⟨⟨d.env.offBase, d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m,
        d.outer.numComps + 1⟩, d.djp.hitPrev, d.djp.size, d.outer.cEdgeLen⟩ >>= fun cRes =>
      shCollectCorrupted
        (d.djp.sh, d.nc0, d.env.bufBase + 14 * d.env.n + d.env.m, 0, 2 * d.env.m) >>=
        fun numCorr =>
          partEmitCorrLoop
            ⟨⟨d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m⟩, numCorr, d.outer.mcLen⟩ >>=
            fun mRes =>
              partMarkDeadLoop
                ⟨⟨d.env.bufBase, d.env.n⟩, d.djp.size, d.outer.cLiftLen⟩ >>= fun lRes =>
                  partWriteRoundMeta
                    ⟨d.env.bufBase, d.env.n, d.outer.numComps, d.djp.size,
                      cRes.count - d.outer.cEdgeLen,
                      d.env.bufBase + 14 * d.env.n + 2 * d.env.m + 4 * d.outer.cEdgeLen,
                      d.env.bufBase + 4 * d.env.n + d.outer.cLiftLen⟩ >>= fun _ =>
                      pure ⟨d.outer.u + 1, d.outer.numComps + 1, cRes.count, lRes.count,
                        mRes.count, d.djp.tLen,
                        ⟨d.djp.sh.itemBase, d.djp.sh.nodeBase, 0, d.djp.sh.itemCount,
                          d.djp.sh.nodeCount, d.djp.sh.rankThreshold⟩⟩) := by
  unfold partRoundFinish
  rfl

/-- Unfolding equation for `partRoundFinishSafe`. -/
theorem partRoundFinishSafe_def (w : ℕ) (d : PartRoundFinishArgs) (s : Memory.State) :
    partRoundFinishSafe w d s =
      (let env := d.env
       let outer := d.outer
       let djp := d.djp
       let emitArgs : PartEmitCompArgs :=
         ⟨⟨env.offBase, env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, outer.numComps + 1⟩,
           djp.hitPrev, djp.size, outer.cEdgeLen⟩
       let s₁ := (Memory.spec 0).clientState s (partEmitComp emitArgs)
       let cRes := (Memory.spec 0).clientResult s (partEmitComp emitArgs)
       let corrArgs := (djp.sh, d.nc0, env.bufBase + 14 * env.n + env.m, 0, 2 * env.m)
       let numCorr := (Memory.spec 0).clientResult s₁ (shCollectCorrupted corrArgs)
       let s₂ := (Memory.spec 0).clientState s₁ (shCollectCorrupted corrArgs)
       let mcArgs : PartEmitCorrLoopArgs :=
         ⟨⟨env.edgeBase, env.bufBase, env.n, env.m⟩, numCorr, outer.mcLen⟩
       let s₃ := (Memory.spec 0).clientState s₂ (partEmitCorrLoop mcArgs)
       let deadArgs : PartMarkDeadLoopArgs := ⟨⟨env.bufBase, env.n⟩, djp.size, outer.cLiftLen⟩
       let s₄ := (Memory.spec 0).clientState s₃ (partMarkDeadLoop deadArgs)
       Fits w 16 ∧ Fits w (outer.u + 1) ∧ Fits w (outer.numComps + 1) ∧ Fits w (2 * env.m) ∧
         outer.cEdgeLen ≤ cRes.count ∧
         Fits w (env.bufBase + 14 * env.n + 14 * env.m) ∧
         Fits w (env.bufBase + 14 * env.n + 2 * env.m + 4 * outer.cEdgeLen) ∧
         Fits w (env.bufBase + 4 * env.n + outer.cLiftLen) ∧
         partEmitCompSafe w emitArgs s ∧
         shCollectCorruptedSafe w corrArgs s₁ ∧
         partEmitCorrLoopSafe w mcArgs s₂ ∧
         partMarkDeadLoopSafe w deadArgs s₃ ∧
         partWriteRoundMetaSafe w
           ⟨env.bufBase, env.n, outer.numComps, djp.size, cRes.count - outer.cEdgeLen,
             env.bufBase + 14 * env.n + 2 * env.m + 4 * outer.cEdgeLen,
             env.bufBase + 4 * env.n + outer.cLiftLen⟩ s₄) := by
  unfold partRoundFinishSafe
  rfl

/-- Executes one full dynamic-DJP round starting from live root `d.2.u`. -/
def partRunRound (d : PartEnv × PartOuterState) : Memory.Prog PartOuterState := do
  let env := d.1
  let st := d.2
  let h0 ← partRoundInit ⟨env, st.numComps + 1, st.u, st.sh⟩
  let st1 ← partDjpLoop ⟨env, st.numComps + 1, st.tLen, h0⟩
  partRoundFinish ⟨env, st, st.sh.nodeCount, st1⟩

/-- Native safety domain for `partRunRound`. -/
def partRunRoundSafe (w : ℕ) (d : PartEnv × PartOuterState) (s : Memory.State) : Prop :=
  let env := d.1
  let st := d.2
  let initArgs : PartExpandVertexArgs := ⟨env, st.numComps + 1, st.u, st.sh⟩
  let h0 := (Memory.spec 0).clientResult s (partRoundInit initArgs)
  let s₁ := (Memory.spec 0).clientState s (partRoundInit initArgs)
  let loopArgs : PartDjpLoopArgs := ⟨env, st.numComps + 1, st.tLen, h0⟩
  let st1 := (Memory.spec 0).clientResult s₁ (partDjpLoop loopArgs)
  let s₂ := (Memory.spec 0).clientState s₁ (partDjpLoop loopArgs)
  Fits w 16 ∧ Fits w (st.numComps + 1) ∧ partRoundInitSafe w initArgs s ∧
    partDjpLoopSafe w loopArgs s₁ ∧
    partRoundFinishSafe w ⟨env, st, st.sh.nodeCount, st1⟩ s₂

/-- `partRunRound` is uniformly realized with `work = 0`. -/
theorem realizes_partRunRound : Realizes .exact
    partRunRound (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partRunRoundSafe (fun _ _ => 0) := by
  unfold partRunRound
  realize [realizes_partRoundInit, realizes_partDjpLoop, realizes_partRoundFinish]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2.1
    | exact h.2.2.2.2
    | (have h16 := h.1; have hnc1 := h.2.1; fits)

/-- Unfolding equation for `partRunRound`. -/
theorem partRunRound_def (d : PartEnv × PartOuterState) : partRunRound d =
    (partRoundInit ⟨d.1, d.2.numComps + 1, d.2.u, d.2.sh⟩ >>= fun h0 =>
      partDjpLoop ⟨d.1, d.2.numComps + 1, d.2.tLen, h0⟩ >>= fun st1 =>
        partRoundFinish ⟨d.1, d.2, d.2.sh.nodeCount, st1⟩) := by
  unfold partRunRound
  rfl

/-- Unfolding equation for `partRunRoundSafe`. -/
theorem partRunRoundSafe_def (w : ℕ) (d : PartEnv × PartOuterState) (s : Memory.State) :
    partRunRoundSafe w d s =
      (let initArgs : PartExpandVertexArgs := ⟨d.1, d.2.numComps + 1, d.2.u, d.2.sh⟩
       let h0 := (Memory.spec 0).clientResult s (partRoundInit initArgs)
       let s₁ := (Memory.spec 0).clientState s (partRoundInit initArgs)
       let loopArgs : PartDjpLoopArgs := ⟨d.1, d.2.numComps + 1, d.2.tLen, h0⟩
       let st1 := (Memory.spec 0).clientResult s₁ (partDjpLoop loopArgs)
       let s₂ := (Memory.spec 0).clientState s₁ (partDjpLoop loopArgs)
       Fits w 16 ∧ Fits w (d.2.numComps + 1) ∧ partRoundInitSafe w initArgs s ∧
         partDjpLoopSafe w loopArgs s₁ ∧
         partRoundFinishSafe w ⟨d.1, d.2, d.2.sh.nodeCount, st1⟩ s₂) := by
  unfold partRunRoundSafe
  rfl

/-- Outer vertex scan step: skips already-claimed vertices (`dead[u] ≠ 0`), otherwise runs a
dynamic-DJP round starting at `u`. -/
def partOuterStep (d : PartEnv × PartOuterState) : Memory.Prog PartOuterState := do
  let env := d.1
  let st := d.2
  let dead ← Memory.read (env.bufBase + st.u)
  if dead ≠ 0 then
    pure ⟨st.u + 1, st.numComps, st.cEdgeLen, st.cLiftLen, st.mcLen, st.tLen, st.sh⟩
  else
    partRunRound d

/-- Native safety domain for `partOuterStep`. -/
def partOuterStepSafe (w : ℕ) (d : PartEnv × PartOuterState) (s : Memory.State) : Prop :=
  let env := d.1
  let st := d.2
  Fits w 16 ∧ Fits w (st.u + 1) ∧ env.bufBase + st.u < s.frontier ∧
    (s.mem (env.bufBase + st.u) = 0 → partRunRoundSafe w d s)

private theorem realizes_partOuterStep_history : Realizes .exact
    partOuterStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partOuterStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partOuterStep d)))
    (fun _ _ => 0) := by
  unfold partOuterStep
  realize [realizes_partRunRound]
  all_goals
    obtain ⟨⟨h16, hu1, hd_lt, hrun⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ne_eq, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  fits

/-- `partOuterStep` is uniformly realized with `work = 0`. -/
private theorem realizes_partOuterStep : Realizes .exact
    partOuterStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partOuterStepSafe (fun _ _ => 0) :=
  realizes_partOuterStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partOuterStep`. -/
theorem partOuterStep_def (d : PartEnv × PartOuterState) : partOuterStep d =
    (Memory.read (d.1.bufBase + d.2.u) >>= fun dead =>
      if dead ≠ 0 then
        pure ⟨d.2.u + 1, d.2.numComps, d.2.cEdgeLen, d.2.cLiftLen, d.2.mcLen, d.2.tLen, d.2.sh⟩
      else partRunRound d) := by
  unfold partOuterStep
  rfl

/-- Unfolding equation for `partOuterStepSafe`. -/
theorem partOuterStepSafe_def (w : ℕ) (d : PartEnv × PartOuterState) (s : Memory.State) :
    partOuterStepSafe w d s =
      (Fits w 16 ∧ Fits w (d.2.u + 1) ∧ d.1.bufBase + d.2.u < s.frontier ∧
        (s.mem (d.1.bufBase + d.2.u) = 0 → partRunRoundSafe w d s)) := by
  unfold partOuterStepSafe
  rfl

/-- Scans edge `d.2.idx`, copying it to `hRemBase` if still active (`edgeState[idx] = 0`). -/
def partEmitRemStep (d : PartEdgeBufEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let st ← Memory.read (env.bufBase + 14 * env.n + cur.idx)
  if st = 0 then
    partCopyIndexedEdge ⟨env.edgeBase, env.bufBase + 14 * env.n + 10 * env.m, cur.idx, cur.count⟩
    pure ⟨cur.idx + 1, cur.count + 1⟩
  else
    pure ⟨cur.idx + 1, cur.count⟩

/-- Native safety domain for `partEmitRemStep`. -/
def partEmitRemStepSafe (w : ℕ) (d : PartEdgeBufEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ Fits w (cur.count + 1) ∧
    Fits w (env.bufBase + 14 * env.n + 14 * env.m) ∧
    env.bufBase + 14 * env.n + cur.idx < s.frontier ∧
    (s.mem (env.bufBase + 14 * env.n + cur.idx) = 0 →
      partCopyIndexedEdgeSafe w
        ⟨env.edgeBase, env.bufBase + 14 * env.n + 10 * env.m, cur.idx, cur.count⟩ s)

private theorem realizes_partEmitRemStep_history : Realizes .exact
    partEmitRemStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitRemStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitRemStep d)))
    (fun _ _ => 0) := by
  unfold partEmitRemStep
  realize [realizes_partCopyIndexedEdge]
  all_goals
    obtain ⟨⟨h16, he1, hr1, _, hst_lt, hcopy⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partEmitRemStep` is uniformly realized with `work = 0`. -/
private theorem realizes_partEmitRemStep : Realizes .exact
    partEmitRemStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitRemStepSafe (fun _ _ => 0) :=
  realizes_partEmitRemStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partEmitRemStep`. -/
theorem partEmitRemStep_def (d : PartEdgeBufEnv × PartCursor) : partEmitRemStep d =
    (Memory.read (d.1.bufBase + 14 * d.1.n + d.2.idx) >>= fun st =>
      if st = 0 then
        partCopyIndexedEdge
          ⟨d.1.edgeBase, d.1.bufBase + 14 * d.1.n + 10 * d.1.m, d.2.idx, d.2.count⟩ >>= fun _ =>
          pure ⟨d.2.idx + 1, d.2.count + 1⟩
      else pure ⟨d.2.idx + 1, d.2.count⟩) := by
  unfold partEmitRemStep
  rfl

/-- Unfolding equation for `partEmitRemStepSafe`. -/
theorem partEmitRemStepSafe_def (w : ℕ) (d : PartEdgeBufEnv × PartCursor) (s : Memory.State) :
    partEmitRemStepSafe w d s =
      (Fits w 16 ∧ Fits w (d.2.idx + 1) ∧ Fits w (d.2.count + 1) ∧
        Fits w (d.1.bufBase + 14 * d.1.n + 14 * d.1.m) ∧
        d.1.bufBase + 14 * d.1.n + d.2.idx < s.frontier ∧
        (s.mem (d.1.bufBase + 14 * d.1.n + d.2.idx) = 0 →
          partCopyIndexedEdgeSafe w
            ⟨d.1.edgeBase, d.1.bufBase + 14 * d.1.n + 10 * d.1.m, d.2.idx, d.2.count⟩ s)) := by
  unfold partEmitRemStepSafe
  rfl

/-- Runs the outer vertex scan across `0 .. d.env.n - 1`. -/
def partRunOuterLoop (d : PartSetupResult) : Memory.Prog PartOuterState :=
  iterate partOuterStep d.env d.env.n ⟨0, 0, 0, 0, 0, 0, d.sh⟩

/-- Native safety domain for `partRunOuterLoop`. -/
def partRunOuterLoopSafe (w : ℕ) (d : PartSetupResult) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    iterationSafe partOuterStep partOuterStepSafe w d.env d.env.n ⟨0, 0, 0, 0, 0, 0, d.sh⟩ s

/-- `partRunOuterLoop` is uniformly realized with `work = 0`. -/
private theorem realizes_partRunOuterLoop : Realizes .exact
    partRunOuterLoop WordEncoding.encode WordEncoding.encode
    partRunOuterLoopSafe (fun _ _ => 0) := by
  unfold partRunOuterLoop
  realize [realizes_partOuterStep]
  exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Unfolding equation for `partRunOuterLoop`. -/
theorem partRunOuterLoop_def (d : PartSetupResult) : partRunOuterLoop d =
    iterate partOuterStep d.env d.env.n ⟨0, 0, 0, 0, 0, 0, d.sh⟩ := by
  unfold partRunOuterLoop
  rfl

/-- Unfolding equation for `partRunOuterLoopSafe`. -/
theorem partRunOuterLoopSafe_def (w : ℕ) (d : PartSetupResult) (s : Memory.State) :
    partRunOuterLoopSafe w d s =
      (Fits w 16 ∧
        iterationSafe partOuterStep partOuterStepSafe w
          d.env d.env.n ⟨0, 0, 0, 0, 0, 0, d.sh⟩ s) := by
  unfold partRunOuterLoopSafe
  rfl

/-- Runs the post-loop scan collecting remaining active edges into `hRemBase`. -/
def partRunRemLoop (d : PartEdgeBufEnv) : Memory.Prog PartCursor :=
  iterate partEmitRemStep d d.m ⟨0, 0⟩

/-- Native safety domain for `partRunRemLoop`. -/
def partRunRemLoopSafe (w : ℕ) (d : PartEdgeBufEnv) (s : Memory.State) : Prop :=
  Fits w 16 ∧ iterationSafe partEmitRemStep partEmitRemStepSafe w d d.m ⟨0, 0⟩ s

/-- `partRunRemLoop` is uniformly realized with `work = 0`. -/
private theorem realizes_partRunRemLoop : Realizes .exact
    partRunRemLoop WordEncoding.encode WordEncoding.encode
    partRunRemLoopSafe (fun _ _ => 0) := by
  unfold partRunRemLoop
  realize [realizes_partEmitRemStep]
  exact h.2

/-- Unfolding equation for `partRunRemLoop`. -/
theorem partRunRemLoop_def (d : PartEdgeBufEnv) : partRunRemLoop d =
    iterate partEmitRemStep d d.m ⟨0, 0⟩ := by
  unfold partRunRemLoop
  rfl

/-- Unfolding equation for `partRunRemLoopSafe`. -/
theorem partRunRemLoopSafe_def (w : ℕ) (d : PartEdgeBufEnv) (s : Memory.State) :
    partRunRemLoopSafe w d s =
      (Fits w 16 ∧ iterationSafe partEmitRemStep partEmitRemStepSafe w d d.m ⟨0, 0⟩ s) := by
  unfold partRunRemLoopSafe
  rfl

/-- Specialization of [PettieRamachandran2002] §3.2 (Fig. 2, p. 21) `Partition(G, t, ε)` over
`Memory.Prog` with target component size `t = d.maxsize` and fixed `ε = 1 / 16`
(`partRankThreshold = 8`, yielding at most `m / 8 = 2 * ε * m` corrupted edges). Materializes
compacted subgraphs `C_i`, corrupted edges `M_C`, remaining edges `H_rem`, and conglomerate
labels via `connectedComponentsProg` into `PartitionResult`. -/
def partitionProg (d : PartSetupArgs) : Memory.Prog PartitionResult := do
  if d.n = 0 then
    pure ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  else
    let setup ← partSetup d
    let res ← partRunOuterLoop setup
    let hRem ← partRunRemLoop ⟨d.edgeBase, setup.env.bufBase, d.n, d.m⟩
    let cc ← connectedComponentsProg ⟨d.n, res.tLen, setup.env.bufBase + 10 * d.n⟩
    let b := setup.env.bufBase
    pure ⟨res.numComps, b + 6 * d.n, b + 9 * d.n, b + 14 * d.n + 6 * d.m,
      res.mcLen, b + 14 * d.n + 10 * d.m, hRem.count, cc.compBase, cc.numComps⟩

/-- Native safety domain for `partitionProg`. -/
def partitionProgSafe (w : ℕ) (d : PartSetupArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    (d.n ≠ 0 →
      let setup := (Memory.spec 0).clientResult s (partSetup d)
      let s₁ := (Memory.spec 0).clientState s (partSetup d)
      let res := (Memory.spec 0).clientResult s₁ (partRunOuterLoop setup)
      let s₂ := (Memory.spec 0).clientState s₁ (partRunOuterLoop setup)
      let s₃ := (Memory.spec 0).clientState s₂
        (partRunRemLoop ⟨d.edgeBase, setup.env.bufBase, d.n, d.m⟩)
      Fits w (setup.env.bufBase + 14 * d.n + 14 * d.m) ∧
      partSetupSafe w d s ∧
      partRunOuterLoopSafe w setup s₁ ∧
      partRunRemLoopSafe w ⟨d.edgeBase, setup.env.bufBase, d.n, d.m⟩ s₂ ∧
      (setup.env.bufBase + 10 * d.n) + 4 * res.tLen ≤ s₃.frontier ∧
      Fits w (s₃.frontier + (4 * d.n + 4 * res.tLen + 1)) ∧
      ∀ j < res.tLen,
        s₃.mem (setup.env.bufBase + 10 * d.n + 4 * j) < d.n ∧
        s₃.mem (setup.env.bufBase + 10 * d.n + 4 * j + 1) < d.n)

/-- `partitionProg` is uniformly realized with `work = 0`. -/
theorem realizes_partitionProg : Realizes .exact
    partitionProg WordEncoding.encode WordEncoding.encode
    partitionProgSafe (fun _ _ => 0) := by
  unfold partitionProg
  realize [realizes_partSetup, realizes_partRunOuterLoop, realizes_partRunRemLoop,
    realizes_connectedComponentsProg]
  all_goals first
    | exact (h.2 (by assumption)).2.1
    | exact (h.2 (by assumption)).2.2.1
    | exact (h.2 (by assumption)).2.2.2.1
    | exact (h.2 (by assumption)).2.2.2.2.1
    | exact (h.2 (by assumption)).2.2.2.2.2.1
    | exact (h.2 (by assumption)).2.2.2.2.2.2
    | (have h16 := h.1; have hbuf := (h.2 hc).1; have hfront := hmem.frontier_fits; fits)

/-- Unfolding equation for `partitionProg`. -/
theorem partitionProg_def (d : PartSetupArgs) : partitionProg d =
    (if d.n = 0 then pure ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    else
      partSetup d >>= fun setup =>
        partRunOuterLoop setup >>= fun res =>
          partRunRemLoop ⟨d.edgeBase, setup.env.bufBase, d.n, d.m⟩ >>= fun hRem =>
            connectedComponentsProg ⟨d.n, res.tLen, setup.env.bufBase + 10 * d.n⟩ >>= fun cc =>
              let b := setup.env.bufBase
              pure ⟨res.numComps, b + 6 * d.n, b + 9 * d.n, b + 14 * d.n + 6 * d.m,
                res.mcLen, b + 14 * d.n + 10 * d.m, hRem.count, cc.compBase, cc.numComps⟩) := by
  unfold partitionProg
  rfl

/-- Unfolding equation for `partitionProgSafe`. -/
theorem partitionProgSafe_def (w : ℕ) (d : PartSetupArgs) (s : Memory.State) :
    partitionProgSafe w d s =
      (Fits w 16 ∧
        (d.n ≠ 0 →
          let setup := (Memory.spec 0).clientResult s (partSetup d)
          let s₁ := (Memory.spec 0).clientState s (partSetup d)
          let res := (Memory.spec 0).clientResult s₁ (partRunOuterLoop setup)
          let s₂ := (Memory.spec 0).clientState s₁ (partRunOuterLoop setup)
          let s₃ := (Memory.spec 0).clientState s₂
            (partRunRemLoop ⟨d.edgeBase, setup.env.bufBase, d.n, d.m⟩)
          Fits w (setup.env.bufBase + 14 * d.n + 14 * d.m) ∧
          partSetupSafe w d s ∧
          partRunOuterLoopSafe w setup s₁ ∧
          partRunRemLoopSafe w ⟨d.edgeBase, setup.env.bufBase, d.n, d.m⟩ s₂ ∧
          (setup.env.bufBase + 10 * d.n) + 4 * res.tLen ≤ s₃.frontier ∧
          Fits w (s₃.frontier + (4 * d.n + 4 * res.tLen + 1)) ∧
          ∀ j < res.tLen,
            s₃.mem (setup.env.bufBase + 10 * d.n + 4 * j) < d.n ∧
            s₃.mem (setup.env.bufBase + 10 * d.n + 4 * j + 1) < d.n)) := by
  unfold partitionProgSafe
  rfl

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.CSR
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
import Mathlib.Tactic.NormNum

/-!
# Partition Workspace Layout and Word-Encoded Interfaces

Defines workspace parameters (`partRankThreshold`, `partSHFuel`), flat workspace layout (`PartEnv`,
`PartLayout`), and faithful `word_enc_structure` encodings for every dynamic Soft-Heap DJP
partition subroutine in `Partition.{DjpOps, DjpStep, DjpLoop}`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartEnv`, `PartLayout`,
  `PartLayout.toEnv`: flat workspace addresses and validated separation invariants.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartSetupArgs`, `PartSetupResult`,
  `PartTryInsertArgs`, `PartAdjEnv`, `PartExpandState`, `PartExpandVertexArgs`, `PartDjpEnv`,
  `PartDjpState`, `PartDjpMaybeExpandArgs`, `PartDjpAddVertArgs`, `PartDjpDispatchArgs`,
  `PartDjpLoopArgs`, `PartWriteStride4Args`, `PartCopyEdgeArgs`: word-encoded argument and state
  structures eliminating nested positional tuple projections.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partRankThreshold`, `partSHFuel`: Soft-Heap
  rank threshold `8` (`ε = 1 / 16`) and fuel bound `500 * (2 * m + 1)`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.partRankThreshold_eq_eps`:
  `partRankThreshold = rankThresholdForEps (1 / 16)`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PartLayout.inSHPool_bounds`,
  `PartLayout.inSHPool_lt_bufBase`, `PartLayout.congr_below_itemBase`,
  `PartLayout.agree_outside_inSHPool`: framing lemmas isolating the Soft-Heap pools, CSR/edge
  arrays, and partition workspace.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-! ## Soft-Heap Specialization Parameters (`ε = 1 / 16`) -/

/-- Corruption rank threshold `r = 8` achieving Soft-Heap error rate `ε = 1 / 16`. -/
@[expose] def partRankThreshold : ℕ := 8

/-- `partRankThreshold = 8` equals `rankThresholdForEps (1 / 16)`. -/
theorem partRankThreshold_eq_eps :
    partRankThreshold = rankThresholdForEps (1 / 16 : ℚ) := by
  have hceil : Nat.ceil (12 / (1 / 16 : ℚ)) = 192 := by
    rw [show (12 / (1 / 16 : ℚ) : ℚ) = ((192 : ℕ) : ℚ) by norm_num, Nat.ceil_natCast]
  rw [partRankThreshold, rankThresholdForEps, hceil, show Nat.log 2 192 = 7 by decide]

/-- Soft-Heap `defill` fuel `shFuelBound partRankThreshold (2 * m)` (`500 * (2 * m + 1)`). -/
abbrev partSHFuel (m : ℕ) : ℕ := shFuelBound partRankThreshold (2 * m)

/-! ## Partition Environment and Word-Encoded Structs -/

/-- Shared read-only partition environment passed across DJP and emission routines. -/
structure PartEnv where
  /-- Number of graph vertices `n`. -/
  n : ℕ
  /-- Number of input edges `m`. -/
  m : ℕ
  /-- Base address of the stride-4 input `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Maximum vertices `maxsize` permitted per partition component. -/
  maxsize : ℕ
  /-- Base address of CSR vertex offset array (`n + 1` words). -/
  offBase : ℕ
  /-- Base address of CSR half-edge adjacency array (`4 * m` words). -/
  adjBase : ℕ
  /-- Base address of the `(14 * n + 14 * m)`-word partition workspace buffer. -/
  bufBase : ℕ
  deriving DecidableEq

/-- Faithful seven-word encoding of `PartEnv`. -/
word_enc_structure encPartEnv : PartEnv where
  n : wordWords,
  m : wordWords,
  edgeBase : wordWords,
  maxsize : wordWords,
  offBase : wordWords,
  adjBase : wordWords,
  bufBase : wordWords

instance : WordEncoding PartEnv := ⟨7, encPartEnv⟩

/-- Input arguments to `partSetup`. -/
structure PartSetupArgs where
  /-- Number of graph vertices `n`. -/
  n : ℕ
  /-- Number of input edges `m`. -/
  m : ℕ
  /-- Base address of the stride-4 input `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Maximum component vertex count `maxsize`. -/
  maxsize : ℕ
  deriving DecidableEq

/-- Faithful four-word encoding of `PartSetupArgs`. -/
word_enc_structure encPartSetupArgs : PartSetupArgs where
  n : wordWords,
  m : wordWords,
  edgeBase : wordWords,
  maxsize : wordWords

instance : WordEncoding PartSetupArgs := ⟨4, encPartSetupArgs⟩

/-- Output of `partSetup`: populated environment and initialized Soft-Heap handle. -/
structure PartSetupResult where
  /-- Allocated partition workspace environment. -/
  env : PartEnv
  /-- Empty initialized Soft-Heap pool handle with `rankThreshold = 8`. -/
  sh : SHHandle
  deriving DecidableEq

/-- Faithful thirteen-word encoding of `PartSetupResult`. -/
word_enc_structure encPartSetupResult : PartSetupResult where
  env : encPartEnv,
  sh : (WordEncoding.encode (α := SHHandle))

instance : WordEncoding PartSetupResult := ⟨13, encPartSetupResult⟩

/-- Arguments for `partTryInsertEdge`. -/
structure PartTryInsertArgs where
  /-- Base address of input edge array. -/
  edgeBase : ℕ
  /-- Base address of partition workspace buffer. -/
  bufBase : ℕ
  /-- Number of vertices `n`. -/
  n : ℕ
  /-- Number of edges `m`. -/
  m : ℕ
  /-- Current round component identifier `cid = numComps + 1`. -/
  cid : ℕ
  /-- Neighbor endpoint vertex index. -/
  nb : ℕ
  /-- Edge index in `0..m-1`. -/
  eIdx : ℕ
  /-- Current Soft-Heap handle. -/
  sh : SHHandle
  deriving DecidableEq

/-- Faithful thirteen-word encoding of `PartTryInsertArgs`. -/
word_enc_structure encPartTryInsertArgs : PartTryInsertArgs where
  edgeBase : wordWords,
  bufBase : wordWords,
  n : wordWords,
  m : wordWords,
  cid : wordWords,
  nb : wordWords,
  eIdx : wordWords,
  sh : (WordEncoding.encode (α := SHHandle))

instance : WordEncoding PartTryInsertArgs := ⟨13, encPartTryInsertArgs⟩

/-- Loop-invariant environment for scanning a vertex's CSR half-edges (`partExpandStep` and
`partEmitEdgeStep`). -/
structure PartAdjEnv where
  /-- Base address of CSR half-edge array. -/
  adjBase : ℕ
  /-- Base address of input edge array. -/
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

/-- Faithful six-word encoding of `PartAdjEnv`. -/
word_enc_structure encPartAdjEnv : PartAdjEnv where
  adjBase : wordWords,
  edgeBase : wordWords,
  bufBase : wordWords,
  n : wordWords,
  m : wordWords,
  cid : wordWords

instance : WordEncoding PartAdjEnv := ⟨6, encPartAdjEnv⟩

/-- Mutable loop state for `partExpandStep`. -/
structure PartExpandState where
  /-- Current CSR half-edge index. -/
  idx : ℕ
  /-- Current Soft-Heap handle. -/
  sh : SHHandle
  deriving DecidableEq

/-- Faithful seven-word encoding of `PartExpandState`. -/
word_enc_structure encPartExpandState : PartExpandState where
  idx : wordWords,
  sh : (WordEncoding.encode (α := SHHandle))

instance : WordEncoding PartExpandState := ⟨7, encPartExpandState⟩

/-- Arguments for `partExpandVertex` and `partRoundInit`. -/
structure PartExpandVertexArgs where
  /-- Partition environment. -/
  env : PartEnv
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  /-- Vertex index `u` to initialize or expand. -/
  u : ℕ
  /-- Current Soft-Heap handle. -/
  sh : SHHandle
  deriving DecidableEq

/-- Faithful fifteen-word encoding of `PartExpandVertexArgs`. -/
word_enc_structure encPartExpandVertexArgs : PartExpandVertexArgs where
  env : encPartEnv,
  cid : wordWords,
  u : wordWords,
  sh : (WordEncoding.encode (α := SHHandle))

instance : WordEncoding PartExpandVertexArgs := ⟨15, encPartExpandVertexArgs⟩

/-- Fixed environment for `partDjpStep` inside `partDjpLoop`. -/
structure PartDjpEnv where
  /-- Partition environment. -/
  env : PartEnv
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  deriving DecidableEq

/-- Faithful eight-word encoding of `PartDjpEnv`. -/
word_enc_structure encPartDjpEnv : PartDjpEnv where
  env : encPartEnv,
  cid : wordWords

instance : WordEncoding PartDjpEnv := ⟨8, encPartDjpEnv⟩

/-- Mutable loop state maintained across `partDjpStep` iterations. -/
structure PartDjpState where
  /-- Continuation flag (`1` while growing, `0` when stopped). -/
  cont : ℕ
  /-- Flag (`1` iff stopped upon touching a previously claimed vertex). -/
  hitPrev : ℕ
  /-- Number of vertices in the current DJP component. -/
  size : ℕ
  /-- Cumulative number of DJP tree edges written to `treeBase`. -/
  tLen : ℕ
  /-- Current Soft-Heap handle. -/
  sh : SHHandle
  deriving DecidableEq

/-- Faithful ten-word encoding of `PartDjpState`. -/
word_enc_structure encPartDjpState : PartDjpState where
  cont : wordWords,
  hitPrev : wordWords,
  size : wordWords,
  tLen : wordWords,
  sh : (WordEncoding.encode (α := SHHandle))

instance : WordEncoding PartDjpState := ⟨10, encPartDjpState⟩

/-- Arguments for `partDjpMaybeExpand`. -/
structure PartDjpMaybeExpandArgs where
  /-- Partition environment. -/
  env : PartEnv
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  /-- Current Soft-Heap handle. -/
  sh : SHHandle
  /-- Newly added vertex `vOut`. -/
  vOut : ℕ
  /-- Prior `dead[vOut]` value. -/
  dOut : ℕ
  /-- Updated component vertex count `size + 1`. -/
  size : ℕ
  /-- Updated cumulative DJP tree edge count `tLen + 1`. -/
  tLen : ℕ
  deriving DecidableEq

/-- Faithful eighteen-word encoding of `PartDjpMaybeExpandArgs`. -/
word_enc_structure encPartDjpMaybeExpandArgs : PartDjpMaybeExpandArgs where
  env : encPartEnv,
  cid : wordWords,
  sh : (WordEncoding.encode (α := SHHandle)),
  vOut : wordWords,
  dOut : wordWords,
  size : wordWords,
  tLen : wordWords

instance : WordEncoding PartDjpMaybeExpandArgs := ⟨18, encPartDjpMaybeExpandArgs⟩

/-- Arguments for `partDjpAddVert`. -/
structure PartDjpAddVertArgs where
  /-- Partition environment. -/
  env : PartEnv
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  /-- Current Soft-Heap handle. -/
  sh : SHHandle
  /-- Extracted edge index `eIdx`. -/
  eIdx : ℕ
  /-- Newly discovered endpoint `vOut`. -/
  vOut : ℕ
  /-- Current component vertex count `size`. -/
  size : ℕ
  /-- Current cumulative DJP tree edge count `tLen`. -/
  tLen : ℕ
  deriving DecidableEq

/-- Faithful eighteen-word encoding of `PartDjpAddVertArgs`. -/
word_enc_structure encPartDjpAddVertArgs : PartDjpAddVertArgs where
  env : encPartEnv,
  cid : wordWords,
  sh : (WordEncoding.encode (α := SHHandle)),
  eIdx : wordWords,
  vOut : wordWords,
  size : wordWords,
  tLen : wordWords

instance : WordEncoding PartDjpAddVertArgs := ⟨18, encPartDjpAddVertArgs⟩

/-- Arguments for `partDjpDispatch`. -/
structure PartDjpDispatchArgs where
  /-- Partition environment. -/
  env : PartEnv
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  /-- Updated Soft-Heap handle after `shExtractMin`. -/
  sh : SHHandle
  /-- Extracted edge index `eIdx`. -/
  eIdx : ℕ
  /-- Current `hitPrev` flag. -/
  hitPrev : ℕ
  /-- Current component vertex count `size`. -/
  size : ℕ
  /-- Current cumulative DJP tree edge count `tLen`. -/
  tLen : ℕ
  deriving DecidableEq

/-- Faithful eighteen-word encoding of `PartDjpDispatchArgs`. -/
word_enc_structure encPartDjpDispatchArgs : PartDjpDispatchArgs where
  env : encPartEnv,
  cid : wordWords,
  sh : (WordEncoding.encode (α := SHHandle)),
  eIdx : wordWords,
  hitPrev : wordWords,
  size : wordWords,
  tLen : wordWords

instance : WordEncoding PartDjpDispatchArgs := ⟨18, encPartDjpDispatchArgs⟩

/-- Arguments for `partDjpLoop`. -/
structure PartDjpLoopArgs where
  /-- Partition environment. -/
  env : PartEnv
  /-- Current round component identifier `cid`. -/
  cid : ℕ
  /-- Initial cumulative DJP tree edge count `tLen`. -/
  tLen : ℕ
  /-- Initial Soft-Heap handle after `partRoundInit`. -/
  sh : SHHandle
  deriving DecidableEq

/-- Faithful fifteen-word encoding of `PartDjpLoopArgs`. -/
word_enc_structure encPartDjpLoopArgs : PartDjpLoopArgs where
  env : encPartEnv,
  cid : wordWords,
  tLen : wordWords,
  sh : (WordEncoding.encode (α := SHHandle))

instance : WordEncoding PartDjpLoopArgs := ⟨15, encPartDjpLoopArgs⟩

/-- Arguments for `partWriteStride4`. -/
structure PartWriteStride4Args where
  /-- Base address of stride-4 destination array. -/
  dstBase : ℕ
  /-- Destination record index. -/
  idx : ℕ
  /-- First word (`u`). -/
  u : ℕ
  /-- Second word (`v`). -/
  v : ℕ
  /-- Third word (`weight`). -/
  weight : ℕ
  /-- Fourth word (`id`). -/
  id : ℕ
  deriving DecidableEq

/-- Faithful six-word encoding of `PartWriteStride4Args`. -/
word_enc_structure encPartWriteStride4Args : PartWriteStride4Args where
  dstBase : wordWords,
  idx : wordWords,
  u : wordWords,
  v : wordWords,
  weight : wordWords,
  id : wordWords

instance : WordEncoding PartWriteStride4Args := ⟨6, encPartWriteStride4Args⟩

/-- Arguments for `partCopyIndexedEdge`. -/
structure PartCopyEdgeArgs where
  /-- Base address of source stride-4 `IndexedEdge` array. -/
  srcBase : ℕ
  /-- Base address of destination stride-4 `IndexedEdge` array. -/
  dstBase : ℕ
  /-- Source edge index. -/
  srcIdx : ℕ
  /-- Destination edge index. -/
  dstIdx : ℕ
  deriving DecidableEq

/-- Faithful four-word encoding of `PartCopyEdgeArgs`. -/
word_enc_structure encPartCopyEdgeArgs : PartCopyEdgeArgs where
  srcBase : wordWords,
  dstBase : wordWords,
  srcIdx : wordWords,
  dstIdx : wordWords

instance : WordEncoding PartCopyEdgeArgs := ⟨4, encPartCopyEdgeArgs⟩

/-! ## Validated Workspace Layout and Separation Lemmas -/

/-- Validated memory layout and size/fit invariants for a `Partition` run on `n` vertices. -/
structure PartLayout (w n : ℕ) where
  /-- Input edge list `es : List (IndexedEdge n)`. -/
  es : List (IndexedEdge n)
  /-- Base address of the stride-4 input `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Maximum component size `maxsize ≥ 1`. -/
  maxsize : ℕ
  /-- Base address of CSR vertex offset array. -/
  offBase : ℕ
  /-- Base address of CSR half-edge adjacency array. -/
  adjBase : ℕ
  /-- Base address of the Soft-Heap item pool. -/
  itemBase : ℕ
  /-- Base address of the Soft-Heap node pool. -/
  nodeBase : ℕ
  /-- Base address of the `(14 * n + 14 * es.length)`-word workspace buffer. -/
  bufBase : ℕ
  /-- Initial memory frontier prior to `partSetup`. -/
  initFrontier : ℕ
  /-- Word width is at least 17 bits (`Fits w 16`). -/
  h16 : Fits w 16
  /-- `maxsize ≥ 1`. -/
  hmax_pos : 1 ≤ maxsize
  /-- Vertex count `n ≥ 1`. -/
  hn_pos : 1 ≤ n
  /-- Input edges lie strictly below `initFrontier`. -/
  hin_lt : edgeBase + 4 * es.length ≤ initFrontier
  /-- CSR offsets start at or above `initFrontier`. -/
  hoff_ge : initFrontier ≤ offBase
  /-- CSR adjacency starts after `(n + 1)` offset words. -/
  hoff_adj : offBase + n + 1 ≤ adjBase
  /-- Soft-Heap item pool starts after `4 * es.length` CSR adjacency words. -/
  hadj_it : adjBase + 4 * es.length ≤ itemBase
  /-- Soft-Heap node pool starts after item pool of capacity `2 * es.length`. -/
  hit_nd : itemBase + 3 * (2 * es.length + 1) ≤ nodeBase
  /-- Workspace buffer starts after node pool of capacity `4 * es.length`. -/
  hnd_buf : nodeBase + 12 * (4 * es.length + 1) ≤ bufBase
  /-- Workspace end plus connected-components scratch fits in `w` bits. -/
  hfit_end : Fits w (bufBase + 14 * n + 14 * es.length + 8 * n + 20)
  /-- Soft-Heap `defill` fuel fits in `w` bits. -/
  hfit_fuel : Fits w (partSHFuel es.length)

namespace PartLayout

/-- Extract the 7-word `PartEnv` record associated with `L`. -/
@[expose] def toEnv {w n : ℕ} (L : PartLayout w n) : PartEnv :=
  ⟨n, L.es.length, L.edgeBase, L.maxsize, L.offBase, L.adjBase, L.bufBase⟩

/-- Bounds on addresses inside `InSHPool ic nc capI capN h`. -/
theorem inSHPool_bounds {ic nc capI capN : ℕ} {h : SHHandle} {x : ℕ}
    (hx : InSHPool ic nc capI capN h x) :
    (h.itemBase ≤ x ∧ x < h.itemBase + 3 * (capI + 1)) ∨
    (h.nodeBase ≤ x ∧ x < h.nodeBase + 12 * (capN + 1)) := by
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; omega
  · right; omega

/-- Any cell in `InSHPool` (anchored at `L.itemBase`, `L.nodeBase`) lies in
`[L.itemBase, L.bufBase)`. -/
theorem inSHPool_lt_bufBase {w n ic nc : ℕ} (L : PartLayout w n)
    {h : SHHandle} (hib : h.itemBase = L.itemBase) (hnb : h.nodeBase = L.nodeBase)
    {x : ℕ} (hx : InSHPool ic nc (2 * L.es.length) (4 * L.es.length) h x) :
    L.itemBase ≤ x ∧ x < L.bufBase := by
  have := L.hit_nd
  have := L.hnd_buf
  rcases inSHPool_bounds hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hib] at * <;> rw [hnb] at * <;> omega

/-- Input edges end below `L.itemBase`. -/
theorem edge_lt_itemBase {w n : ℕ} (L : PartLayout w n) :
    L.edgeBase + 4 * L.es.length ≤ L.itemBase := by
  have := L.hin_lt; have := L.hoff_ge; have := L.hoff_adj; have := L.hadj_it; omega

/-- CSR offsets and adjacency lie below `L.itemBase`. -/
theorem csr_lt_itemBase {w n : ℕ} (L : PartLayout w n) :
    L.offBase + n + 1 ≤ L.adjBase ∧ L.adjBase + 4 * L.es.length ≤ L.itemBase :=
  ⟨L.hoff_adj, L.hadj_it⟩

/-- If `m₂` agrees with `m₁` on `[0, L.itemBase)`, then `HoldsIndexedEdges L.edgeBase L.es` and
`HoldsUndirCSR L.offBase L.adjBase L.es` transfer from `m₁` to `m₂`. -/
theorem congr_below_itemBase {w n : ℕ} (L : PartLayout w n) {m₁ m₂ : ℕ → ℕ}
    (hagree : ∀ x < L.itemBase, m₂ x = m₁ x) :
    (HoldsIndexedEdges L.edgeBase L.es m₁ → HoldsIndexedEdges L.edgeBase L.es m₂) ∧
    (HoldsUndirCSR L.offBase L.adjBase L.es m₁ → HoldsUndirCSR L.offBase L.adjBase L.es m₂) := by
  have he := L.edge_lt_itemBase
  have hc := L.csr_lt_itemBase
  refine ⟨fun h => h.congr fun x _ hx => hagree x (by omega),
    fun h => h.congr (fun x _ hx => hagree x (by omega)) (fun x _ hx => hagree x (by omega))⟩

/-- A memory update modifying only `InSHPool` leaves `[0, L.itemBase)` and `[L.bufBase, ...)`
untouched. -/
theorem agree_outside_inSHPool {w n ic nc : ℕ} (L : PartLayout w n)
    {h : SHHandle} (hib : h.itemBase = L.itemBase) (hnb : h.nodeBase = L.nodeBase)
    {m₁ m₂ : ℕ → ℕ}
    (hmod : ∀ x, m₂ x ≠ m₁ x → InSHPool ic nc (2 * L.es.length) (4 * L.es.length) h x) :
    (∀ x < L.itemBase, m₂ x = m₁ x) ∧ (∀ x, L.bufBase ≤ x → m₂ x = m₁ x) := by
  refine ⟨fun x hx => by_contra fun hne => ?_, fun x hx => by_contra fun hne => ?_⟩
  · have := L.inSHPool_lt_bufBase hib hnb (hmod x hne); omega
  · have := L.inSHPool_lt_bufBase hib hnb (hmod x hne); omega

end PartLayout

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

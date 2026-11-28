/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust

/-!
# Threshold-Rank Contraction and Dynamic Soft-Heap Robust Contraction

Umbrella module re-exporting threshold-rank and dynamic contraction steps toward Theorem 5.8 of
[PettieRamachandran2002] (#8624):

* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold`: `edgeEnds`
  and lexicographic weight bridge to `Cslib.Multigraph.msf`, `WeaklySupported` (the
  `WeightedEdge`-list / `edgePartition` counterpart of `Cslib.Multigraph.Supported` from
  [KhannaPuttermanSong2026], Sections 1.2 and 3.1, generalized for equal-weight substitutions),
  threshold-rank characterization `isMinSpanningForest_iff_threshold_partition`, and contraction
  preservation (`exists_extend_isMinSpanningForest_of_cutStep`,
  `isMinSpanningForest_append_of_contract`).
* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust`:
  `DynamicDJPTree`, dynamic Soft-Heap border-edge path property
  (`DynamicDJPTree.rel_treeEdges_filter_of_border`), dynamic contraction lifting
  (`weaklySupported_of_dynamicDJPTree`, `isMinSpanningForest_of_dynamicDJPTree`), stopping-rule
  conglomerate bound (`maxsize_le_card_biUnion_of_stop`), and simple-graph deduplication
  (`dedupSimpleEdges`, `dedupSimpleEdges_isSimple`, `isMinSpanningForest_of_dedupSimpleEdges`).

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002]
* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026]
-/

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree

/-!
# Exact finite graph serialization roundtrip

Reading the serialized finite graph and enumerating its vertices recovers the original finite
vertex list, including every port's order, direction, weight, and threshold.

## Main results

* `AndOrGraph.ofFn_graph_ofFinite`: the original finite vertex list is unchanged.
* `AndOrGraph.ofFinite_loopFree`: serialization preserves the absence of repeated port edges.
-/

public section

namespace Cslib.Complexity.NCL.AndOrGraph

/-- Finite serialization preserves the absence of repeated port edges at every vertex. -/
theorem ofFinite_loopFree {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (hl : G.LoopFree) : (ofFinite G).graph.LoopFree := by
  intro i
  rw [graph_ofFinite]
  exact hl _

/-- Reading and enumerating finite graph data recovers the complete original vertex list. -/
theorem ofFn_graph_ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    List.ofFn (ofFinite G).graph = List.ofFn G := by
  have hlen : (ofFinite G).vertices.length = n := by simp [ofFinite]
  calc
    _ = List.ofFn (fun i : Fin (ofFinite G).vertices.length => G (i.cast hlen)) := by
      congr 1
      funext i
      exact graph_ofFinite G i
    _ = List.ofFn G := (List.ofFn_congr hlen.symm G).symm

end Cslib.Complexity.NCL.AndOrGraph

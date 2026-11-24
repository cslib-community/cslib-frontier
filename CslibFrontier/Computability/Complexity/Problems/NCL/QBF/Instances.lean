/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Numbered
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
public import CslibFrontier.Computability.Complexity.Problems.NCL.Reachability

/-!
# Source reductions to explicit AND/OR NCL instances

Serialize the numbered circuit as vertex data and an edge count. All source inputs produce
valid graphs. The fixed-target, configuration-to-edge, and directional edge-to-edge instances
belong to their NCL languages exactly when the source belongs to `TQBFCNF`.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Reduction.graphData`: explicit graph data.
* `Cslib.Complexity.NCL.QBF.Reduction.toConfig`, `Cslib.Complexity.NCL.QBF.Reduction.toEdge`,
  `Cslib.Complexity.NCL.QBF.Reduction.toEdgeToEdge`: the three instance maps.

## Main results

* `Cslib.Complexity.NCL.QBF.Reduction.graphData_loopFree`: source instances have no self-loops.
* `Cslib.Complexity.NCL.QBF.Reduction.mem_toConfig_iff`,
  `Cslib.Complexity.NCL.QBF.Reduction.mem_toEdge_iff`,
  `Cslib.Complexity.NCL.QBF.Reduction.mem_toEdgeToEdge_iff`: source-language correctness.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 5 and Corollary 6]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Reduction

/-- The source circuit as natural-numbered vertex data and its exact edge count. -/
@[expose] def graphData (x : PrenexCNF) : AndOrGraph := AndOrGraph.ofFinite (Numbered.graph x)

/-- Every source input produces a valid finite AND/OR graph. -/
theorem graphData_valid (x : PrenexCNF) : (graphData x).Valid :=
  AndOrGraph.ofFinite_valid _ (Numbered.isAndOr x) (Numbered.wellFormed x)

/-- The encoded graph shared by the three reductions has no self-loops. -/
theorem graphData_loopFree (x : PrenexCNF) : (graphData x).graph.LoopFree := by
  change (AndOrGraph.ofFinite (Numbered.graph x)).graph.LoopFree
  intro i
  rw [AndOrGraph.graph_ofFinite]
  exact Numbered.loopFree x _

/-- The graph data are exactly the result of compiling the emitted source word. -/
theorem graphData_eq_compile (x : PrenexCNF) : graphData x = Word.compile (Numbered.word x) :=
  (Diagram.compile_toWord Prim.interp (Expanded.diagram x)).symm

/-- A fixed-target instance with one bit per edge. -/
@[expose] def toConfig (x : PrenexCNF) : AndOrNCL.Instance :=
  ⟨graphData x, Numbered.initial x, Numbered.target x⟩

/-- A configuration-to-edge instance tracking the output record at index four. -/
@[expose] def toEdge (x : PrenexCNF) : AndOrNCLEdge.Instance :=
  ⟨graphData x, Numbered.initial x, 4⟩

/-- A directional edge-to-edge instance from inactive try to satisfied sat. -/
@[expose] def toEdgeToEdge (x : PrenexCNF) : AndOrNCLEdgeToEdge.Instance :=
  ⟨graphData x, ⟨6, false⟩, ⟨0, false⟩⟩

private theorem config_initial (x : PrenexCNF) :
    (AndOrGraph.ofFinite (Numbered.graph x)).config (Numbered.initial x) =
      Numbered.initialConfig x :=
  AndOrGraph.config_eq_get _ _ (Numbered.length_initial x)

private theorem config_target (x : PrenexCNF) :
    (AndOrGraph.ofFinite (Numbered.graph x)).config (Numbered.target x) =
      Numbered.targetConfig x :=
  AndOrGraph.config_eq_get _ _ (Numbered.length_target x)

/-- The explicit fixed-target instance accepts exactly the upstream source language. -/
theorem mem_toConfig_iff (x : PrenexCNF) : toConfig x ∈ AndOrNCL ↔ x ∈ TQBFCNF := by
  have h := AndOrGraph.ofFinite_mem_AndOrNCL_iff (Numbered.graph x) (graphData_valid x)
    (Numbered.initial x) (Numbered.target x)
  refine h.trans ?_
  simp only [Numbered.length_initial, Numbered.length_target, true_and,
    config_initial, config_target]
  exact Numbered.reachable_iff_mem_TQBFCNF x

/-- The explicit configuration-to-edge instance accepts exactly the source language. -/
theorem mem_toEdge_iff (x : PrenexCNF) : toEdge x ∈ AndOrNCLEdge ↔ x ∈ TQBFCNF := by
  have h := AndOrGraph.ofFinite_mem_AndOrNCLEdge_iff (Numbered.graph x) (graphData_valid x)
    (Numbered.initial x) (Numbered.output x)
  rw [Numbered.output_val] at h
  refine h.trans ?_
  simp only [Numbered.length_initial, true_and, config_initial]
  exact Numbered.canReverse_iff_mem_TQBFCNF x

/-- The explicit directional edge-to-edge instance accepts exactly the source language. -/
theorem mem_toEdgeToEdge_iff (x : PrenexCNF) :
    toEdgeToEdge x ∈ AndOrNCLEdgeToEdge ↔ x ∈ TQBFCNF := by
  have h := AndOrGraph.ofFinite_mem_AndOrNCLEdgeToEdge_iff (Numbered.graph x) (graphData_valid x)
    (Numbered.tryIn x) (Numbered.satOut x) false false
  rw [Numbered.tryIn_val, Numbered.satOut_val] at h
  exact h.trans (Numbered.exists_reachable_sat_iff_mem_TQBFCNF x)

end Cslib.Complexity.NCL.QBF.Reduction

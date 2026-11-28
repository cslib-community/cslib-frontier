/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Planarized.Bits
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.PlaneReachability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time source reductions to plane-word NCL

The emitted plane word, its two canonical bit lists and the three fixed edge positions give
instances of the three plane-word decision problems. Their membership agrees with source truth.

## Main definitions

* `Cslib.Complexity.NCL.PlaneWordAndOrNCL.reduce`,
  `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge.reduce`,
  `Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge.reduce`: the three planar source reductions.

## Main results

* `Cslib.Complexity.NCL.PlaneWordAndOrNCL.reduce_mem_iff` and its edge variants: correctness.
* `Cslib.Complexity.NCL.PlaneWordAndOrNCL.computableInPolyTime_reduce` and its edge variants:
  polynomial-time emission.
* `Cslib.Complexity.NCL.QBF.Planarized.num_output`,
  `Cslib.Complexity.NCL.QBF.Planarized.num_tryIn`,
  `Cslib.Complexity.NCL.QBF.Planarized.num_satOut`: fixed edge positions.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Planarized

open Diagram _root_.Turing.MultiTapeTM

/-- Every source input emits valid planar AND/OR graph data. -/
theorem graphData_valid (x : PrenexCNF) : (graphData x).Valid :=
  Diagram.compile_valid Prim.interp (diagram x) (isAndOr x) (wellFormed x)

/-- The emitted graph has no self-loops. -/
theorem graphData_loopFree (x : PrenexCNF) : (graphData x).graph.LoopFree := by
  change (Word.compile ((diagram x).toWord Prim.interp 0)).graph.LoopFree
  rw [Diagram.compile_toWord]
  intro i
  rw [AndOrGraph.graph_ofFinite]
  exact (Diagram.finiteGraph_loopFree Prim.interp (diagram x) (loopFree x)) _

/-- The planar output record has creation-order edge number four. -/
theorem num_output (x : PrenexCNF) : (diagram x).num (output x) = 4 :=
  (Planar.Circuit.num_edge_compLeft OutputLatch.diagram _ OutputLatch.mem).trans
    (by decide +kernel)

/-- The tracked planar try input has creation-order edge number six. -/
theorem num_tryIn (x : PrenexCNF) : (diagram x).num (tryIn x) = 6 :=
  (Planar.Circuit.num_edge_compLeft OutputLatch.diagram _ OutputLatch.attempt).trans
    (by decide +kernel)

/-- The tracked planar satisfied output has creation-order edge number zero. -/
theorem num_satOut (x : PrenexCNF) : (diagram x).num (satOut x) = 0 :=
  (Planar.Circuit.num_edge_compLeft OutputLatch.diagram _ OutputLatch.sat).trans
    (by decide +kernel)

end Cslib.Complexity.NCL.QBF.Planarized

namespace Cslib.Complexity.NCL

open Diagram QBF.Planarized _root_.Turing.MultiTapeTM

namespace PlaneWordAndOrNCL

/-- The planar fixed-target source instance with explicit canonical configurations. -/
@[expose] def reduce (x : PrenexCNF) : PlaneWordAndOrNCL.Instance :=
  ⟨word x, initialBits x, targetBits x⟩

/-- The planar fixed-target source instance accepts exactly the source language. -/
theorem reduce_mem_iff (x : PrenexCNF) : reduce x ∈ PlaneWordAndOrNCL ↔ x ∈ TQBFCNF :=
  (Diagram.mem_plane_AndOrNCL_iff Prim.interp (diagram x) (checkPlane_word x)
    (graphData_valid x) (initial x).orient (target x).orient).trans
      ((and_iff_right (initial x).legal).trans (reachable_iff_mem_TQBFCNF x))

/-- Emit the planar fixed-target source instance in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF encPlaneWordAndOrNCL := by
  unfold reduce
  fun_prop

end PlaneWordAndOrNCL

namespace PlaneWordAndOrNCLEdge

/-- The planar configuration-to-edge source instance tracking the output record. -/
@[expose] def reduce (x : PrenexCNF) : PlaneWordAndOrNCLEdge.Instance :=
  ⟨word x, initialBits x, (diagram x).num (output x)⟩

/-- The planar configuration-to-edge instance accepts exactly the source language. -/
theorem reduce_mem_iff (x : PrenexCNF) : reduce x ∈ PlaneWordAndOrNCLEdge ↔ x ∈ TQBFCNF :=
  (Diagram.mem_plane_AndOrNCLEdge_iff Prim.interp (diagram x) (checkPlane_word x)
    (graphData_valid x) (initial x).orient (output x)).trans
      ((and_iff_right (initial x).legal).trans (canReverse_iff_mem_TQBFCNF x))

/-- Emit the planar configuration-to-edge source instance in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF encPlaneWordAndOrNCLEdge := by
  unfold reduce
  simp only [num_output]
  fun_prop

end PlaneWordAndOrNCLEdge

namespace PlaneWordAndOrNCLEdgeToEdge

/-- The planar directional source instance from inactive try to satisfied sat. -/
@[expose] def reduce (x : PrenexCNF) : PlaneWordAndOrNCLEdgeToEdge.Instance :=
  ⟨word x, ⟨(diagram x).num (tryIn x), false⟩, ⟨(diagram x).num (satOut x), false⟩⟩

/-- The planar directional source instance accepts exactly the source language. -/
theorem reduce_mem_iff (x : PrenexCNF) :
    reduce x ∈ PlaneWordAndOrNCLEdgeToEdge ↔ x ∈ TQBFCNF :=
  (Diagram.mem_plane_AndOrNCLEdgeToEdge_iff Prim.interp (diagram x) (checkPlane_word x)
    (graphData_valid x) (tryIn x) (satOut x) false false).trans
      (exists_reachable_sat_iff_mem_TQBFCNF x)

/-- Emit the planar directional source instance in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF encPlaneWordAndOrNCLEdgeToEdge := by
  unfold reduce
  simp only [num_tryIn, num_satOut]
  fun_prop

end PlaneWordAndOrNCLEdgeToEdge

end Cslib.Complexity.NCL

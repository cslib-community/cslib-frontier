/-
Copyright (c) 2026 Samuel Schlesinger, Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reduction
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.PlanarDrawing

/-!
# Polynomial-time reductions to planar AND/OR multigraphs

Compile the canonical plane-word instances into explicit graph instances. Their incidence graphs
have continuous polygonal embeddings, and all three reachability questions retain their answers.
The output specifications also record the loop-free source image for downstream constructions.

## Main definitions

* `PlanarAndOrNCL.reduce` and its edge variants give the canonical source reductions.

## Main results

* `PlanarAndOrNCL.reduce_mem_iff` and its edge variants prove source correctness.
* `PlanarAndOrNCL.reduce_spec` and its edge variants certify planar, valid, loop-free outputs.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

namespace PlanarAndOrNCL

/-- Compile the canonical plane-word reduction into an explicit planar graph instance. -/
@[expose] def reduce (x : PrenexCNF) : AndOrNCL.Instance :=
  let x := PlaneWordAndOrNCL.reduce x
  ⟨Word.compile x.word, x.initial, x.target⟩

/-- The source map is polynomial-time under the general graph instance encoding. -/
@[fun_prop]
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF encAndOrNCL := by
  fun_prop [reduce]

/-- Every source input emits a valid planar graph without self-loops. -/
theorem reduce_spec (x : PrenexCNF) :
    (reduce x).graph.Valid ∧ (reduce x).graph.IsPlanar ∧ (reduce x).graph.graph.LoopFree := by
  have h := (PlaneWordAndOrNCL.reduce_spec x).1
  exact ⟨h.2.2.1, Word.isPlanar_compile h.1 h.2.1 h.2.2.1, h.2.2.2⟩

/-- The explicit planar graph instance accepts exactly the source language. -/
theorem reduce_mem_iff (x : PrenexCNF) : reduce x ∈ PlanarAndOrNCL ↔ x ∈ TQBFCNF := by
  have h := (PlaneWordAndOrNCL.reduce_spec x).1
  simpa only [PlanarAndOrNCL, PlaneWordAndOrNCL, Set.mem_ofPred_eq,
    Word.isPlanar_compile h.1 h.2.1 h.2.2.1, and_true, h.1, h.2.1, true_and, reduce] using
      PlaneWordAndOrNCL.reduce_mem_iff x

end PlanarAndOrNCL

namespace PlanarAndOrNCLEdge

/-- Compile the canonical plane-word reduction into an explicit planar graph instance. -/
@[expose] def reduce (x : PrenexCNF) : AndOrNCLEdge.Instance :=
  let x := PlaneWordAndOrNCLEdge.reduce x
  ⟨Word.compile x.word, x.initial, x.edge⟩

/-- The source map is polynomial-time under the general graph instance encoding. -/
@[fun_prop]
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF encAndOrNCLEdge := by
  fun_prop [reduce]

/-- Every source input emits a valid planar graph without self-loops. -/
theorem reduce_spec (x : PrenexCNF) :
    (reduce x).graph.Valid ∧ (reduce x).graph.IsPlanar ∧ (reduce x).graph.graph.LoopFree := by
  have h := (PlaneWordAndOrNCLEdge.reduce_spec x).1
  exact ⟨h.2.2.1, Word.isPlanar_compile h.1 h.2.1 h.2.2.1, h.2.2.2⟩

/-- The explicit planar graph instance accepts exactly the source language. -/
theorem reduce_mem_iff (x : PrenexCNF) : reduce x ∈ PlanarAndOrNCLEdge ↔ x ∈ TQBFCNF := by
  have h := (PlaneWordAndOrNCLEdge.reduce_spec x).1
  simpa only [PlanarAndOrNCLEdge, PlaneWordAndOrNCLEdge, Set.mem_ofPred_eq,
    Word.isPlanar_compile h.1 h.2.1 h.2.2.1, and_true, h.1, h.2.1, true_and, reduce] using
      PlaneWordAndOrNCLEdge.reduce_mem_iff x

end PlanarAndOrNCLEdge

namespace PlanarAndOrNCLEdgeToEdge

/-- Compile the canonical plane-word reduction into an explicit planar graph instance. -/
@[expose] def reduce (x : PrenexCNF) : AndOrNCLEdgeToEdge.Instance :=
  let x := PlaneWordAndOrNCLEdgeToEdge.reduce x
  ⟨Word.compile x.word, x.first, x.second⟩

/-- The source map is polynomial-time under the general graph instance encoding. -/
@[fun_prop]
theorem computableInPolyTime_reduce :
    ComputableInPolyTime reduce encPrenexCNF encAndOrNCLEdgeToEdge := by
  fun_prop [reduce]

/-- Every source input emits a valid planar graph without self-loops. -/
theorem reduce_spec (x : PrenexCNF) :
    (reduce x).graph.Valid ∧ (reduce x).graph.IsPlanar ∧ (reduce x).graph.graph.LoopFree := by
  have h := (PlaneWordAndOrNCLEdgeToEdge.reduce_spec x).1
  exact ⟨h.2.2.1, Word.isPlanar_compile h.1 h.2.1 h.2.2.1, h.2.2.2⟩

/-- The explicit planar graph instance accepts exactly the source language. -/
theorem reduce_mem_iff (x : PrenexCNF) : reduce x ∈ PlanarAndOrNCLEdgeToEdge ↔ x ∈ TQBFCNF := by
  have h := (PlaneWordAndOrNCLEdgeToEdge.reduce_spec x).1
  simpa only [PlanarAndOrNCLEdgeToEdge, PlaneWordAndOrNCLEdgeToEdge, Set.mem_ofPred_eq,
    Word.isPlanar_compile h.1 h.2.1 h.2.2.1, and_true, h.1, h.2.1, true_and, reduce] using
      PlaneWordAndOrNCLEdgeToEdge.reduce_mem_iff x

end PlanarAndOrNCLEdgeToEdge

end Cslib.Complexity.NCL

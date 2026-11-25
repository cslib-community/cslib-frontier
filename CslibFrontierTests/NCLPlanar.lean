/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Hardness
import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Hardness
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Equivalence
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.PlanarDrawing

/-! Planar multigraph and plane-word decision problems, complexity bounds and source interfaces. -/

open Cslib.Complexity.NCL

/-- info: 'Cslib.Complexity.NCL.Word.computableInPolyTime_checkPlane' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Word.computableInPolyTime_checkPlane

/-- info: 'Cslib.Complexity.NCL.Word.computableInPolyTime_wellTyped' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Word.computableInPolyTime_wellTyped

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCL_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCL_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdge_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdgeToEdge_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlaneWordAndOrNCL' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlaneWordAndOrNCL

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCL_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCL_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCL_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCL_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdge

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdge_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdge_pspaceComplete

/-- info:
'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdgeToEdge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlaneWordAndOrNCLEdgeToEdge

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdgeToEdge_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdgeToEdge_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCL.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCL.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCL.pspaceHard_of_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCL.pspaceHard_of_inv

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdge.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdge.pspaceHard_of_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdge.pspaceHard_of_inv

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdgeToEdge.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlaneWordAndOrNCLEdgeToEdge.pspaceHard_of_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlaneWordAndOrNCLEdgeToEdge.pspaceHard_of_inv


/-- info: 'Cslib.Complexity.NCL.Word.planarOrthogonalDrawing_compile' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Word.planarOrthogonalDrawing_compile

-- Semantic correctness and the drawing refer to the same serialized reduction output.
example (x : Cslib.Complexity.PrenexCNF) :
    (PlaneWordAndOrNCL.reduce x ∈ PlaneWordAndOrNCL ↔ x ∈ Cslib.Complexity.TQBFCNF) ∧
    ∃ D : GridDrawing.Closed (Word.compile (PlaneWordAndOrNCL.reduce x).word).graph,
      Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing D.incidenceGraph D.orthogonalDrawing := by
  have h := (PlaneWordAndOrNCL.reduce_spec x).1
  exact ⟨PlaneWordAndOrNCL.reduce_mem_iff x, Word.planarOrthogonalDrawing_compile h.1 h.2.1⟩

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCL' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlanarAndOrNCL

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCL.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCL.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdge

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdge.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdge.reduce_spec

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge_mem_PSPACE

/-- info:
'Cslib.Complexity.NCL.polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms polyTimeReducible_TQBFCNF_PlanarAndOrNCLEdgeToEdge

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_pspaceHard' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge_pspaceHard

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge_pspaceComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge_pspaceComplete

/-- info: 'Cslib.Complexity.NCL.PlanarAndOrNCLEdgeToEdge.reduce_spec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PlanarAndOrNCLEdgeToEdge.reduce_spec

-- The general graph problems admit the self-loop example from the general NCL tests.
private def loopGraph : AndOrGraph :=
  ⟨[.and ⟨0, false⟩ ⟨0, true⟩ ⟨2, true⟩, .or ⟨1, false⟩ ⟨1, true⟩ ⟨2, false⟩], 3⟩

private theorem loopValid : loopGraph.Valid :=
  (AndOrGraph.checkValid_eq_true_iff _).mp (by decide +kernel)

private theorem loopPlanar : loopGraph.IsPlanar := by
  have h := (Cslib.Complexity.Graph.RotationCertificate.verifyGenusZero_eq_true_iff
    loopGraph.incidenceGraph ⟨[1, 5, 3, 4, 2, 0]⟩).mp (by decide +kernel)
  exact (Cslib.Complexity.Graph.RotationSystem.exists_numericalGenusZero_iff_exists_polygonalDrawing
    (AndOrGraph.incidenceGraph_endpoints loopGraph)).mp ⟨_, h.2⟩

example : ⟨loopGraph, [false, false, true], [true, false, true]⟩ ∈ PlanarAndOrNCL := by
  have hmove := ((AndOrGraph.checkStep_eq_true_iff _ loopValid.1 _ _).mp
    (show loopGraph.checkStep [false, false, true] [true, false, true] = true by
      decide +kernel)).2.2
  exact ⟨⟨loopValid, rfl, rfl, hmove.legal_left, .single hmove⟩, loopPlanar⟩

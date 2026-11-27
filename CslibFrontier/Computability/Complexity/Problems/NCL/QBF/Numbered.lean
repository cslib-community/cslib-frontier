/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Expansion
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Finite
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Typing

/-!
# Numbered source circuits and bit-list configurations

Expand the normalized closed circuit into AND/OR primitives and emit its word. Interpret vertex
and edge numbers on finite intervals. Serialize its initial and target configurations with one
bit per edge. The three correctness results use these finite semantics and include initial
legality, as required by the NCL decision problems.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Numbered.word`, `Cslib.Complexity.NCL.QBF.Numbered.vertices`:
  emitted word and natural-numbered vertex data.
* `Cslib.Complexity.NCL.QBF.Numbered.graph`: the corresponding graph on finite intervals.
* `Cslib.Complexity.NCL.QBF.Numbered.initial`, `Cslib.Complexity.NCL.QBF.Numbered.target`:
  fixed-width bit lists.

## Main results

* `Cslib.Complexity.NCL.QBF.Numbered.run_word`: word emission produces the vertex data.
* `Cslib.Complexity.NCL.QBF.Numbered.isAndOr`, `Cslib.Complexity.NCL.QBF.Numbered.loopFree`,
  `Cslib.Complexity.NCL.QBF.Numbered.wellFormed`: the finite graph has AND/OR vertices,
  consistent opposite endpoints, and no self-loops.
* `Cslib.Complexity.NCL.QBF.Numbered.reachable_iff_mem_TQBFCNF`,
  `Cslib.Complexity.NCL.QBF.Numbered.canReverse_iff_mem_TQBFCNF`,
  `Cslib.Complexity.NCL.QBF.Numbered.exists_reachable_sat_iff_mem_TQBFCNF`: finite semantics
  for all source inputs.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Numbered

open Diagram

/-- The exact number of edges in the emitted closed circuit. -/
@[expose]
def width (x : PrenexCNF) : ℕ := ([] : List Color).length + (Expanded.diagram x).innerCount

/-- The number of vertices in drawing order. -/
@[expose]
def vertexCount (x : PrenexCNF) : ℕ := (vertexList Prim.interp (Expanded.diagram x)).length

/-- The emitted diagram flattened to a word. -/
@[expose] def word (x : PrenexCNF) : Word := (Expanded.diagram x).toWord Prim.interp 0

/-- Every emitted source word checks from the empty boundary to the empty boundary. -/
theorem wellTyped_word (x : PrenexCNF) : (word x).WellTyped [] [] :=
  wellTyped_toWord Prim.interp (Expanded.diagram x)

/-- The emitted vertex data, with natural edge numbers. -/
@[expose] def vertices (x : PrenexCNF) : List (Vertex ℕ) :=
  (finiteVertexList Prim.interp (Expanded.diagram x)).map (Vertex.map Fin.val)

/-- The finite numbered semantics of the emitted circuit. -/
@[expose] def graph (x : PrenexCNF) : ConstraintGraph (Fin (vertexCount x)) (Fin (width x)) :=
  finiteGraph Prim.interp (Expanded.diagram x)

/-- Every numbered vertex is AND or OR. -/
theorem isAndOr (x : PrenexCNF) : (graph x).IsAndOr :=
  finiteGraph_isAndOr Prim.interp (Expanded.diagram x) (Expanded.isAndOr x)

/-- Finite numbering introduces no self-loops. -/
theorem loopFree (x : PrenexCNF) : (graph x).LoopFree :=
  finiteGraph_loopFree Prim.interp (Expanded.diagram x) (Expanded.loopFree x)

/-- Every numbered edge has two opposite ports of equal weight. -/
theorem wellFormed (x : PrenexCNF) : (graph x).WellFormed :=
  finiteGraph_wellFormed Prim.interp (Expanded.diagram x) (Expanded.wellFormed x)

/-- Running the emitted word gives exactly the vertex data and edge count. -/
theorem run_word (x : PrenexCNF) :
    Word.run (word x) ⟨[], 0, []⟩ = ⟨[], width x, vertices x⟩ := by
  simpa only [word, vertices, width, List.length_nil, Nat.zero_add] using
    run_toWord_finite Prim.interp (Expanded.diagram x)

@[simp] theorem length_vertices (x : PrenexCNF) : (vertices x).length = vertexCount x := by
  simp [vertices, finiteVertexList, vertexCount]

/-- Every listed edge number lies in the finite semantic interval. -/
theorem vertices_bounded (x : PrenexCNF) :
    ∀ v ∈ vertices x, ∀ p ∈ v.ports, p.port.edge < width x := by
  intro v hv p hp
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hv
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hp
  exact p.port.edge.isLt

/-- The initial orientation as one bit per numbered edge. -/
@[expose] def initial (x : PrenexCNF) : List Bool :=
  (Expanded.diagram x).bits (Expanded.initial x).orient

/-- The fixed target orientation as one bit per numbered edge. -/
@[expose]
def target (x : PrenexCNF) : List Bool := (Expanded.diagram x).bits (Expanded.target x).orient

@[simp] theorem length_initial (x : PrenexCNF) : (initial x).length = width x :=
  length_bits (Expanded.diagram x) (Expanded.initial x).orient

@[simp] theorem length_target (x : PrenexCNF) : (target x).length = width x :=
  length_bits (Expanded.diagram x) (Expanded.target x).orient

/-- Read the initial bit list on the finite edge interval. -/
@[expose] def initialConfig (x : PrenexCNF) : Fin (width x) → Bool :=
  fun i => (initial x).get (i.cast (length_initial x).symm)

/-- Read the target bit list on the finite edge interval. -/
@[expose] def targetConfig (x : PrenexCNF) : Fin (width x) → Bool :=
  fun i => (target x).get (i.cast (length_target x).symm)

private theorem initialConfig_eq (x : PrenexCNF) : initialConfig x =
    (Expanded.initial x).orient ∘ (Expanded.diagram x).numEquiv.symm :=
  funext fun i => get_bits (Expanded.diagram x) (Expanded.initial x).orient i

private theorem targetConfig_eq (x : PrenexCNF) : targetConfig x =
    (Expanded.target x).orient ∘ (Expanded.diagram x).numEquiv.symm :=
  funext fun i => get_bits (Expanded.diagram x) (Expanded.target x).orient i

/-- The numbered output edge for configuration-to-edge reachability. -/
@[expose]
def output (x : PrenexCNF) : Fin (width x) := (Expanded.diagram x).numEquiv (Expanded.output x)

/-- The numbered try input for edge-to-edge reachability. -/
@[expose]
def tryIn (x : PrenexCNF) : Fin (width x) := (Expanded.diagram x).numEquiv (Expanded.tryIn x)

/-- The numbered satisfied output for edge-to-edge reachability. -/
@[expose]
def satOut (x : PrenexCNF) : Fin (width x) := (Expanded.diagram x).numEquiv (Expanded.satOut x)

private theorem controller_num (D : Diagram Gate [Color.blue, Color.blue] [])
    (e : OutputLatch.diagram.Edge) :
    (((OutputLatch.diagram.comp D).subst Gate.expand).num
      ((openSimSubst Gate.expandOpenSim (OutputLatch.diagram.comp D)).ι
        (compLeft OutputLatch.diagram D e))) =
    (OutputLatch.diagram.subst Gate.expand).num
      ((openSimSubst Gate.expandOpenSim OutputLatch.diagram).ι e) := by
  change ((OutputLatch.diagram.subst Gate.expand).comp (D.subst Gate.expand)).num
    (OpenSim.compι (openSimSubst Gate.expandOpenSim OutputLatch.diagram)
      (openSimSubst Gate.expandOpenSim D) (compLeft OutputLatch.diagram D e)) = _
  rw [OpenSim.compι_compLeft]
  exact name_compLeft (OutputLatch.diagram.subst Gate.expand) (D.subst Gate.expand) Fin.val 0 _

/-- The output record always has edge number four. -/
@[simp] theorem output_val (x : PrenexCNF) : (output x).val = 4 := by
  rw [output, numEquiv_val]
  exact (controller_num _ OutputLatch.mem).trans (by decide +kernel)

/-- The outer try input always has edge number six. -/
@[simp] theorem tryIn_val (x : PrenexCNF) : (tryIn x).val = 6 := by
  rw [tryIn, numEquiv_val]
  exact (controller_num _ OutputLatch.attempt).trans (by decide +kernel)

/-- The body's returned sat always has edge number zero. -/
@[simp] theorem satOut_val (x : PrenexCNF) : (satOut x).val = 0 := by
  rw [satOut, numEquiv_val]
  exact (controller_num _ OutputLatch.sat).trans (by decide +kernel)

private theorem initial_legal (x : PrenexCNF) : (graph x).Legal (initialConfig x) := by
  rw [initialConfig_eq]
  exact (finiteSimulation Prim.interp (Expanded.diagram x)).legal_enc (Expanded.initial x).legal

/-- The initial bit list is legal and reaches its target exactly on true closed source inputs. -/
theorem reachable_iff_mem_TQBFCNF (x : PrenexCNF) :
    (graph x).Legal (initialConfig x) ∧ (graph x).Reachable (initialConfig x) (targetConfig x) ↔
      x ∈ TQBFCNF := by
  rw [and_iff_right (initial_legal x), initialConfig_eq, targetConfig_eq]
  exact (finite_reachable_iff Prim.interp (Expanded.diagram x)).trans
    (Expanded.reachable_iff_mem_TQBFCNF x)

/-- Numbered configuration-to-edge correctness, including legality of the initial bit list. -/
theorem canReverse_iff_mem_TQBFCNF (x : PrenexCNF) :
    (graph x).Legal (initialConfig x) ∧ (graph x).CanReverse (initialConfig x) (output x) ↔
      x ∈ TQBFCNF := by
  rw [and_iff_right (initial_legal x), initialConfig_eq]
  exact (finite_canReverse_iff Prim.interp (Expanded.diagram x) (Expanded.output x)).trans
    (Expanded.canReverse_iff_mem_TQBFCNF x)

/-- Directional edge-to-edge correctness on finite edge and vertex intervals. -/
theorem exists_reachable_sat_iff_mem_TQBFCNF (x : PrenexCNF) :
    (∃ s t, (graph x).Legal s ∧ s (tryIn x) = false ∧ t (satOut x) = false ∧
      (graph x).Reachable s t) ↔ x ∈ TQBFCNF :=
  (finite_exists_reachable_iff Prim.interp (Expanded.diagram x)
    (Expanded.tryIn x) (Expanded.satOut x) false false).trans
      (Expanded.exists_reachable_sat_iff_mem_TQBFCNF x)

end Cslib.Complexity.NCL.QBF.Numbered

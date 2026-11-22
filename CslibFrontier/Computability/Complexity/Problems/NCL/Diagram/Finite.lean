/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Incidence

/-!
# Finite numbered semantics of diagrams

Number vertices by their position in `vertexList` and edges in creation order. Configurations
then use a fixed finite interval, and their serialized bit lists have exactly that width.
The numbering gives a simulation preserving all three NCL reachability questions. For a closed
diagram, erasing the finite bounds on the vertex data gives exactly the output of its word run.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.finiteGraph`: the interpreted graph on finite vertex and edge
  intervals.
* `Cslib.Complexity.NCL.Diagram.finiteSimulation`: the numbering simulation.
* `Cslib.Complexity.NCL.Diagram.bits`: an orientation serialized in edge-number order.

## Main results

* `Cslib.Complexity.NCL.Diagram.finite_reachable_iff`,
  `Cslib.Complexity.NCL.Diagram.finite_canReverse_iff`,
  `Cslib.Complexity.NCL.Diagram.finite_exists_reachable_iff`: finite numbering preserves the
  three decision questions.
* `Cslib.Complexity.NCL.Diagram.run_toWord_finite`: the emitted word produces the finite graph's
  vertex data with bounds erased.

## References

* The decision questions are those of [Hearn and Demaine][HearnDemaine2005, Section 2.1].
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ) {a b : List Color}

/-- The graph with vertices in list order and edges in creation order, on finite intervals. -/
@[expose] def finiteGraph (D : Diagram Γ a b) :
    ConstraintGraph (Fin (vertexList I D).length) (Fin (a.length + D.innerCount)) :=
  ConstraintGraph.map (fun i => (vertexList I D).get i) D.numEquiv

/-- Legality agrees with the diagram under finite edge numbering. -/
private theorem legal_finiteGraph (D : Diagram Γ a b) (s : Fin (a.length + D.innerCount) → Bool) :
    (finiteGraph I D).Legal s ↔ (D.graph I).Legal (s ∘ D.numEquiv) := by
  rw [finiteGraph, ConstraintGraph.legal_map, ← forall_vertexList_iff]
  constructor
  · intro h v hv
    obtain ⟨i, rfl⟩ := List.get_of_mem hv
    exact h i
  · intro h i
    exact h _ (List.get_mem _ i)

/-- Finite numbering is an exact simulation of the diagram. -/
@[expose] def finiteSimulation (D : Diagram Γ a b) :
    ConstraintGraph.Simulation (D.graph I) (finiteGraph I D) :=
  ConstraintGraph.Simulation.ofLegalEquiv _ _ D.numEquiv fun s => by
    rw [legal_finiteGraph]
    simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

/-- Finite numbering preserves the AND/OR vertex property. -/
theorem finiteGraph_isAndOr (D : Diagram Γ a b) (h : (D.graph I).IsAndOr) :
    (finiteGraph I D).IsAndOr := by
  intro i
  have hv := (forall_mem_vertexList_iff (I := I) D (fun v => v.IsAndOr)).2 h _ (List.get_mem _ i)
  exact hv.map D.numEquiv

/-- Finite numbering preserves loop-freedom. -/
theorem finiteGraph_loopFree (D : Diagram Γ a b) (h : (D.graph I).LoopFree) :
    (finiteGraph I D).LoopFree := by
  have hv : ConstraintGraph.LoopFree
      (fun i : Fin (vertexList I D).length => (vertexList I D).get i) := by
    intro i
    exact (forall_mem_vertexList_iff (I := I) D
      (fun v => (v.ports.map (fun p : WeightedPort D.Edge => p.port.edge)).Nodup)).2
        h _ (List.get_mem _ i)
  exact hv.map D.numEquiv.injective

/-- Finite numbering preserves exact endpoint multiplicities and their common weights. -/
theorem finiteGraph_wellFormed (D : Diagram Γ a b) (h : (D.graph I).WellFormed) :
    (finiteGraph I D).WellFormed := by
  have hv : ConstraintGraph.WellFormed
      (fun i : Fin (vertexList I D).length => (vertexList I D).get i) := by
    obtain ⟨weight, hw⟩ := h
    refine ⟨weight, ?_⟩
    rw [ConstraintGraph.portMultiset_get, ← portMultiset_vertexList]
    exact hw
  exact hv.map D.numEquiv

/-- Reachability between numbered configurations agrees with diagram reachability. -/
theorem finite_reachable_iff (D : Diagram Γ a b) {s t : D.Edge → Bool} :
    (finiteGraph I D).Reachable (s ∘ D.numEquiv.symm) (t ∘ D.numEquiv.symm) ↔
      (D.graph I).Reachable s t := (finiteSimulation I D).reachable_enc_iff

/-- A numbered edge can be reversed exactly when the original edge can. -/
theorem finite_canReverse_iff (D : Diagram Γ a b) {s : D.Edge → Bool} (e : D.Edge) :
    (finiteGraph I D).CanReverse (s ∘ D.numEquiv.symm) (D.numEquiv e) ↔
      (D.graph I).CanReverse s e :=
  (finiteSimulation I D).canReverse_enc_iff (fun _ => rfl)

/-- Directional edge-to-edge reachability is preserved by finite numbering. -/
theorem finite_exists_reachable_iff (D : Diagram Γ a b) (eA eB : D.Edge) (dA dB : Bool) :
    (∃ s t, (finiteGraph I D).Legal s ∧ s (D.numEquiv eA) = dA ∧ t (D.numEquiv eB) = dB ∧
      (finiteGraph I D).Reachable s t) ↔
    ∃ s t, (D.graph I).Legal s ∧ s eA = dA ∧ t eB = dB ∧ (D.graph I).Reachable s t :=
  (finiteSimulation I D).exists_legal_reachable_iff (fun _ => rfl) (fun _ => rfl) dA dB

/-- Vertex data with each edge carrying its finite bound. -/
@[expose]
def finiteVertexList (D : Diagram Γ a b) : List (Vertex (Fin (a.length + D.innerCount))) :=
  (vertexList I D).map (Vertex.map D.numEquiv)

/-- Erasing finite bounds gives the original natural-numbered vertex list. -/
private theorem map_val_finiteVertexList (D : Diagram Γ a b) :
    (finiteVertexList I D).map (Vertex.map Fin.val) =
      (vertexList I D).map (Vertex.map D.num) := by
  simp only [finiteVertexList, List.map_map]
  rw [Vertex.map_comp_map (numEquiv_val D)]

/-- Running the word of a closed diagram emits precisely its finite vertex data. -/
theorem run_toWord_finite (D : Diagram Γ [] []) :
    Word.run (D.toWord I 0) ⟨[], 0, []⟩ =
      ⟨[], D.innerCount, (finiteVertexList I D).map (Vertex.map Fin.val)⟩ := by
  have hn : D.name Fin.elim0 0 = D.num := by
    funext e
    rcases e with i | e
    · exact Fin.elim0 i
    · rfl
  rw [run_toWord_closed, hn, map_val_finiteVertexList]

variable {I}

/-- Serialize an orientation in edge-number order. -/
@[expose]
def bits (D : Diagram Γ a b) (s : D.Edge → Bool) : List Bool := List.ofFn (s ∘ D.numEquiv.symm)

@[simp] theorem length_bits (D : Diagram Γ a b) (s : D.Edge → Bool) :
    (D.bits s).length = a.length + D.innerCount := List.length_ofFn

/-- Reading a serialized configuration gives the corresponding numbered direction. -/
theorem get_bits (D : Diagram Γ a b) (s : D.Edge → Bool) (i : Fin (a.length + D.innerCount)) :
    (D.bits s).get (i.cast (length_bits D s).symm) = s (D.numEquiv.symm i) := by
  unfold bits
  rw [List.get_ofFn]
  rfl

end Cslib.Complexity.NCL.Diagram

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Bundle
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Subdivision
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Reorient

/-!
# Incidence stubs and subdivisions

Drawing every original vertex as a source splits each edge into two downward stubs. A wire cap
joins the two stubs. Their reference directions differ at the two endpoints, so this graph is
one subdivision per edge followed by a polarity change. The existing subdivision simulation
therefore supplies its reachability semantics.

## Main definitions

* `Planar.Embedding.Stub.graph`: original vertices on endpoint labels and one cap per edge.
* `Planar.Embedding.Stub.simulation`: the simulation from the original constraint graph.

## Main results

* `Planar.Embedding.Stub.simulation_abs`: the original edge is read at its false incidence.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.Stub

open ConstraintGraph

variable {V E : Type*}

/-- Split original edges into endpoint-labeled stubs and join each pair by a wire cap. -/
@[expose] def graph (G : ConstraintGraph V E) (color : E → Color) : ConstraintGraph (V ⊕ E) (Port E)
  | .inl v => Sources.spec (fun p => color p.edge)
      ((G v).ports.map WeightedPort.port) (G v).minInflow
  | .inr e => Sinks.capSpec (color e) ⟨e, false⟩ ⟨e, true⟩

/-- The two segments of a subdivided edge are its two endpoint incidences. -/
@[expose] def segmentPortEquiv : Subdivision.Segment (fun _ : E => 1) ≃ Port E where
  toFun p := ⟨p.1, finTwoEquiv p.2⟩
  invFun p := ⟨p.edge, finTwoEquiv.symm p.dir⟩
  left_inv p := by simp
  right_inv p := by cases p; simp

/-- Reverse the reference direction on the second segment. -/
@[expose] def mask (p : Subdivision.Segment (fun _ : E => 1)) : Bool := finTwoEquiv p.2

private theorem endpoint_port (p : Port E) :
    (((⟨if p.dir then Subdivision.last (fun _ => 1) p.edge
      else Subdivision.first (fun _ => 1) p.edge, p.dir⟩ :
      Port (Subdivision.Segment (fun _ : E => 1))).reorient mask).map segmentPortEquiv) =
      ⟨p, false⟩ := by
  rcases p with ⟨e, _ | _⟩ <;> rfl

private theorem source_vertex (G : ConstraintGraph V E) (color : E → Color) (v : V)
    (hc : ∀ p ∈ (G v).ports, p.weight = (color p.port.edge).weight) :
    (((Subdivision.graph G (fun _ => 1) (fun e => (color e).weight)).reorient mask)
      (.inl v)).map segmentPortEquiv = (graph G color) (.inl v) := by
  change Vertex.mk _ (G v).minInflow = Vertex.mk _ (G v).minInflow
  apply congrArg (Vertex.mk · (G v).minInflow)
  simp only [Vertex.reorient, ConstraintGraph.reorient, Subdivision.graph,
    List.map_map, Function.comp_def]
  exact List.map_congr_left fun p hp => congrArg₂ WeightedPort.mk (endpoint_port p.port) (hc p hp)

private theorem cap_vertex (G : ConstraintGraph V E) (color : E → Color) (e : E)
    (j : Fin 1) :
    (((Subdivision.graph G (fun _ => 1) (fun e => (color e).weight)).reorient mask)
      (.inr ⟨e, j⟩)).map segmentPortEquiv = (graph G color) (.inr e) := by
  cases Subsingleton.elim j 0
  rfl

private theorem legal_map (G : ConstraintGraph V E) (color : E → Color)
    (hc : ∀ v p, p ∈ (G v).ports → p.weight = (color p.port.edge).weight) (s : Port E → Bool) :
    ((((Subdivision.graph G (fun _ => 1) (fun e => (color e).weight)).reorient mask).map
      segmentPortEquiv).Legal s) ↔ (graph G color).Legal s := by
  let H := Subdivision.graph G (fun _ => 1) (fun e => (color e).weight)
  change (∀ v, (((H.reorient mask) v).map segmentPortEquiv).Sat s) ↔
    ∀ v, ((graph G color) v).Sat s
  simp only [Sum.forall]
  refine and_congr (forall_congr' fun v => by rw [source_vertex G color v (hc v)]) ⟨?_, ?_⟩
  · exact fun h e => by simpa only [H, cap_vertex] using h ⟨e, 0⟩
  · exact fun h ⟨e, j⟩ => by simpa only [H, cap_vertex] using h e

variable [DecidableEq E]

/-- Subdivision and a reference-direction change realize the incidence-stub graph. -/
@[expose] def simulation (G : ConstraintGraph V E) (color : E → Color)
    (hc : ∀ v p, p ∈ (G v).ports → p.weight = (color p.port.edge).weight) (hl : G.LoopFree) :
    ConstraintGraph.Simulation G (graph G color) :=
  let H := Subdivision.graph G (fun _ => 1) (fun e => (color e).weight)
  let S := Subdivision.simulation G (fun _ => 1) (fun e => (color e).weight)
    (fun e => by cases color e <;> decide +kernel) hl
  S.trans ((H.reorientSimulation mask).trans
    (ConstraintGraph.Simulation.ofLegalEquiv (H.reorient mask) (graph G color) segmentPortEquiv
      (fun s => by
        have h := (legal_map G color hc (s ∘ segmentPortEquiv.symm)).symm
        simpa only [ConstraintGraph.legal_map, Function.comp_assoc,
          Equiv.symm_comp_self, Function.comp_id] using h)))

/-- The source orientation is read at the false endpoint stub. -/
theorem simulation_abs (G : ConstraintGraph V E) (color : E → Color)
    (hc : ∀ v p, p ∈ (G v).ports → p.weight = (color p.port.edge).weight) (hl : G.LoopFree)
    (s : Port E → Bool) (e : E) : (simulation G color hc hl).abs s e = s ⟨e, false⟩ := by
  simp only [simulation, ConstraintGraph.Simulation.trans, NCL.Simulation.trans,
    Function.comp_apply, Subdivision.simulation_abs]
  simp [ConstraintGraph.reorientSimulation, NCL.Simulation.ofEquiv,
    ConstraintGraph.Simulation.ofLegalEquiv, Subdivision.abs, Subdivision.first,
    mask, segmentPortEquiv, finTwoEquiv, Function.Involutive.toPerm,
    show ((0 : Fin 2) == 1) = false from by decide, Bool.add_eq_xor]

end Cslib.Complexity.NCL.Planar.Embedding.Stub

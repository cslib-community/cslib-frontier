/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Drawing
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Incidence
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Stub

/-!
# Canonical incidence drawings of finite graphs

List original vertices in order, draw their ports below them, route the incidences into edge
pairs, and cap every pair. The construction is computable from the vertex data, edge colors,
and well-formedness proof. Its graph simulates the original one by a single subdivision per
edge and the corresponding change of reference direction.

## Main definitions

* `Planar.Embedding.diagram`: the canonical closed diagram.
* `Planar.Embedding.simulation`: its reachability simulation.
* `Planar.Embedding.edge`: the tracked representative of an original edge.

## Main results

* `Planar.Embedding.simulation_abs`: abstraction reads the tracked edge.
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding

open Diagram

variable {m : ℕ}

/-- Draw every original vertex as a source cell. -/
@[expose] def sourceBundle (vs : List (Vertex (Fin m))) (color : Fin m → Color) :=
  Sources.vertices (fun p => color p.edge) vs

/-- Cap the incidences of each edge, in edge order. -/
@[expose] def sinkBundle (color : Fin m → Color) := Sinks.caps color (List.finRange m)

/-- Route the original incidence order into consecutive endpoint pairs. -/
@[expose] def routing (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    Wiring Cell (Sources.vertexColors (fun p => color p.edge) vs)
      (Sinks.pairColors color (List.finRange m))
      (Sources.vertexLabels vs) (Sinks.pairLabels (List.finRange m)) :=
  (reorder (Γ := Cell) (fun p => color p.edge) (Sinks.pairLabels (List.finRange m))
    (Sources.vertexLabels vs) (incidencePerm vs hw)).cast
      (Sources.vertexColors_eq _ _).symm (Sinks.pairColors_eq _ _).symm

/-- The canonical incidence drawing of a finite graph. -/
@[expose] def diagram (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) : Diagram Cell [] [] :=
  Drawing.closeDiagram (sourceBundle vs color) (routing vs color hw) (sinkBundle color)

/-- The incidence labels identify the canonical drawing's edges and constraints. -/
@[expose] def drawing (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) :
    Drawing (diagram vs color hw)
      (Sources.vertexSpecs (fun p => color p.edge) vs ++ Sinks.capSpecs color (List.finRange m)) :=
  Drawing.close (sourceBundle vs color) (routing vs color hw) (sinkBundle color)
    (vertexLabels_nodup vs hw) (mem_vertexLabels vs hw)

private theorem legal_stub (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (u : Port (Fin m) → Bool) :
    (Stub.graph (fun i : Fin vs.length => vs.get i) color).Legal u ↔
      (∀ v ∈ Sources.vertexSpecs (fun p => color p.edge) vs, v.Sat u) ∧
        (∀ v ∈ Sinks.capSpecs color (List.finRange m), v.Sat u) := by
  refine ⟨fun h => ⟨List.forall_mem_map.2 ?_, List.forall_mem_map.2 fun e _ => h (.inr e)⟩,
    fun ⟨hs, ht⟩ => Sum.rec (fun i => hs _ (List.mem_map_of_mem (List.get_mem _ i)))
      (fun e => ht _ (List.mem_map_of_mem (List.mem_finRange e)))⟩
  intro w hw
  obtain ⟨i, rfl⟩ := List.get_of_mem hw
  exact h (.inl i)

/-- The canonical drawing has exactly the incidence-stub graph's legal orientations. -/
theorem legal_diagram (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (u : Port (Fin m) → Bool) :
    ((diagram vs color hw).graph Cell.interp).Legal (u ∘ (drawing vs color hw).edgeEquiv) ↔
      (Stub.graph (fun i : Fin vs.length => vs.get i) color).Legal u := by
  rw [(drawing vs color hw).legal_iff, List.forall_mem_append, legal_stub]

/-- The canonical drawing simulates the original graph when its colors match the port weights. -/
@[expose] def simulation (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hc : ∀ i p, p ∈ (vs.get i).ports → p.weight = (color p.port.edge).weight)
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i)) :
    ConstraintGraph.Simulation (fun i : Fin vs.length => vs.get i)
      ((diagram vs color hw).graph Cell.interp) :=
  (Stub.simulation (fun i : Fin vs.length => vs.get i) color hc hl).trans
    (ConstraintGraph.Simulation.ofLegalEquiv _ _ (drawing vs color hw).edgeEquiv.symm
      (legal_diagram vs color hw))

/-- The false endpoint stub represents an original edge in the canonical drawing. -/
@[expose] def edge (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) (e : Fin m) :
    (diagram vs color hw).Edge := (drawing vs color hw).edgeEquiv.symm ⟨e, false⟩

/-- Abstraction reads the representative at the original edge's false incidence. -/
theorem simulation_abs (vs : List (Vertex (Fin m))) (color : Fin m → Color)
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hc : ∀ i p, p ∈ (vs.get i).ports → p.weight = (color p.port.edge).weight)
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i))
    (s : (diagram vs color hw).Edge → Bool) (e : Fin m) :
    (simulation vs color hw hc hl).abs s e = s (edge vs color hw e) := by
  simp only [simulation, ConstraintGraph.Simulation.trans, NCL.Simulation.trans,
    Function.comp_apply, Stub.simulation_abs, ConstraintGraph.Simulation.ofLegalEquiv, edge]

end Cslib.Complexity.NCL.Planar.Embedding

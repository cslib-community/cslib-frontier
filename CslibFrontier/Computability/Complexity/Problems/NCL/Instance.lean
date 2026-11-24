/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.AndOr
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation
public import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Basic

/-!
# Finite data for AND/OR constraint graphs

Store a vertex list with natural edge names and an edge count. Its graph uses finite intervals
for both vertices and edges. Valid data have bounded port names, AND/OR vertices and consistent
opposite endpoints. Both ports of a self-loop occur at the same vertex. Exactly one contributes
to its inflow in each orientation.

## Main definitions

* `Cslib.Complexity.NCL.AndOrGraph`: vertex data and an edge count.
* `Cslib.Complexity.NCL.AndOrGraph.graph`: semantics on finite intervals.
* `Cslib.Complexity.NCL.AndOrGraph.Valid`: the structural conditions on instances.

## Main results

* `Cslib.Complexity.NCL.AndOrGraph.checkVertices_eq_true_iff` checks vertex shapes on bounded data.
-/

public section

namespace Cslib.Complexity.NCL

/-- Natural-numbered vertex data, together with the number of edges. -/
@[ext]
structure AndOrGraph where
  /-- The numbered vertex records. -/
  vertices : List (Vertex ℕ)
  /-- The number of edges in the finite graph. -/
  edgeCount : ℕ

namespace AndOrGraph

/-- Every port names an edge in the declared interval. -/
@[expose]
def Bounded (g : AndOrGraph) : Prop := ∀ v ∈ g.vertices, ∀ p ∈ v.ports, p.port.edge < g.edgeCount

/-- Check all listed edge names against the declared edge count. -/
@[expose] def checkBounded (g : AndOrGraph) : Bool :=
  g.vertices.all (fun v => v.ports.all (fun p => decide (p.port.edge < g.edgeCount)))

/-- The finite check recognizes bounded port data. -/
theorem checkBounded_eq_true_iff (g : AndOrGraph) : g.checkBounded = true ↔ g.Bounded := by
  simp [checkBounded, Bounded, List.all_eq_true]

/-- Interpret the listed ports in the declared finite edge interval. -/
@[expose]
def graph (g : AndOrGraph) : ConstraintGraph (Fin g.vertices.length) (Fin g.edgeCount) := fun i =>
  let v := g.vertices.get i
  { ports := v.ports.filterMap fun p =>
      if h : p.port.edge < g.edgeCount then
        some (⟨⟨⟨p.port.edge, h⟩, p.port.dir⟩, p.weight⟩ : WeightedPort (Fin g.edgeCount))
      else none
    minInflow := v.minInflow }

/-- A finite port occurs exactly when its natural-numbered port occurs in the input vertex. -/
theorem mem_graph_ports_iff (g : AndOrGraph) (i : Fin g.vertices.length)
    (p : WeightedPort (Fin g.edgeCount)) :
    p ∈ (g.graph i).ports ↔ p.map Fin.val ∈ (g.vertices.get i).ports := by
  change p ∈ ((g.vertices.get i).ports.filterMap _) ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, he⟩
    split at he
    · cases Option.some.inj he
      exact hq
    · cases he
  · intro hp
    refine ⟨p.map Fin.val, hp, ?_⟩
    simp only [WeightedPort.map, Port.map, p.port.edge.isLt, ↓reduceDIte]

/-- Erasing finite bounds recovers the original port data when all names are bounded. -/
theorem graph_map_val (g : AndOrGraph) (h : g.Bounded) :
    g.graph.map Fin.val = fun i => g.vertices.get i := by
  funext i
  let v := g.vertices.get i
  have hv : ∀ p ∈ v.ports, p.port.edge < g.edgeCount := h _ (List.get_mem _ i)
  unfold ConstraintGraph.map graph
  simp only [Vertex.map, List.map_filterMap]
  have hp : v.ports.filterMap (fun p =>
      (if h : p.port.edge < g.edgeCount then
        some (⟨⟨⟨p.port.edge, h⟩, p.port.dir⟩, p.weight⟩ : WeightedPort (Fin g.edgeCount))
       else none).map (WeightedPort.map Fin.val)) = v.ports.map id :=
    List.filterMap_eq_map_iff_forall_eq_some.2 (by
      intro p hp
      rw [dite_eq_left (hv p hp)]
      rfl)
  rw [List.map_id] at hp
  change { ports := _, minInflow := v.minInflow } = v
  rw [hp]

/-- The serialized port multiset agrees with the finite semantics after erasing edge bounds. -/
theorem graph_portMultiset (g : AndOrGraph) (hb : g.Bounded) :
    Multiset.map (WeightedPort.map Fin.val) g.graph.portMultiset =
      ↑(g.vertices.flatMap Vertex.ports) := by
  rw [← ConstraintGraph.portMultiset_map, graph_map_val g hb, ConstraintGraph.portMultiset_get]

/-- Check that every listed vertex has AND/OR shape. -/
@[expose] def checkVertices (g : AndOrGraph) : Bool :=
  g.vertices.all Vertex.checkAndOr

/-- On bounded data, the local checks recognize exactly AND/OR vertices. -/
theorem checkVertices_eq_true_iff (g : AndOrGraph) (hb : g.Bounded) :
    g.checkVertices = true ↔ g.graph.IsAndOr := by
  rw [checkVertices, List.all_eq_true, List.forall_mem_iff_get, ConstraintGraph.IsAndOr]
  apply forall_congr'
  intro i
  rw [← congrFun (graph_map_val g hb) i]
  simp only [ConstraintGraph.map, Vertex.checkAndOr_map, Vertex.checkAndOr_eq_true_iff]

/-- The graph has bounded edge names and is a well-formed AND/OR multigraph. -/
@[expose] def Valid (g : AndOrGraph) : Prop :=
  g.Bounded ∧ g.graph.IsAndOr ∧ g.graph.WellFormed

/-- Read a list of orientation bits on the graph's finite edge interval. -/
@[expose]
def config (g : AndOrGraph) (s : List Bool) : Fin g.edgeCount → Bool := fun i => s.getD i false

/-- A list of the declared width reads by its finite indices. -/
theorem config_eq_get (g : AndOrGraph) (s : List Bool) (h : s.length = g.edgeCount) :
    g.config s = fun i => s.get (i.cast h.symm) := by
  funext i
  exact List.getD_eq_get s false (i.cast h.symm)

/-- Serializing a finite orientation and reading it back preserves every bit. -/
theorem config_ofFn (g : AndOrGraph) (s : Fin g.edgeCount → Bool) : g.config (List.ofFn s) = s := by
  rw [config_eq_get g _ List.length_ofFn]
  funext i
  rw [List.get_ofFn]
  rfl

/-- Reading every coordinate of a correctly sized bit list reconstructs that list. -/
theorem ofFn_config (g : AndOrGraph) (s : List Bool) (hs : s.length = g.edgeCount) :
    List.ofFn (g.config s) = s := by
  apply List.ext_getElem (by simp [hs])
  intro i _ hi
  simp only [List.getElem_ofFn, config]
  exact List.getD_eq_getElem s false hi

/-- Serialize a graph on finite vertex and edge intervals. -/
@[expose] def ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) : AndOrGraph :=
  ⟨List.ofFn (fun i => (G i).map Fin.val), m⟩

/-- Serialization keeps every edge name in the declared interval. -/
theorem ofFinite_bounded {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    (ofFinite G).Bounded := by
  intro v hv p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 hp
  exact q.port.edge.isLt

/-- Reading finite graph data recovers each original vertex. -/
theorem graph_ofFinite {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (i : Fin (ofFinite G).vertices.length) :
    (ofFinite G).graph i = G (i.cast (by simp [ofFinite])) := by
  apply Vertex.map_injective Fin.val_injective
  exact (congrFun (graph_map_val _ (ofFinite_bounded G)) i).trans (List.get_ofFn _ i)

private def vertexEquiv {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    Fin (ofFinite G).vertices.length ≃ Fin n := finCongr (by simp [ofFinite])

private theorem graph_ofFinite_eq {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    (ofFinite G).graph = G ∘ vertexEquiv G := funext (graph_ofFinite G)

/-- Serialization preserves the structural conditions of an AND/OR instance. -/
theorem ofFinite_valid {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m))
    (ha : G.IsAndOr) (hw : G.WellFormed) : (ofFinite G).Valid := by
  refine ⟨ofFinite_bounded G, ?_, ?_⟩
  · intro i
    rw [graph_ofFinite]
    exact ha _
  · rw [graph_ofFinite_eq]
    exact hw.reindex (vertexEquiv G)

/-- Serialized finite graph data have exactly the original legality and reachability semantics. -/
@[expose] def ofFiniteSimulation {n m : ℕ} (G : ConstraintGraph (Fin n) (Fin m)) :
    ConstraintGraph.Simulation G (ofFinite G).graph :=
  ConstraintGraph.Simulation.ofLegalEquiv _ _ (Equiv.refl _) fun s => by
    change (ofFinite G).graph.Legal s ↔ G.Legal s
    rw [graph_ofFinite_eq]
    exact ConstraintGraph.legal_comp G (vertexEquiv G).surjective s

end AndOrGraph

end Cslib.Complexity.NCL

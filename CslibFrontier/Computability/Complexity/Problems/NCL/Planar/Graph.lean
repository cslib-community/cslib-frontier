/-
Copyright (c) 2026 Samuel Schlesinger, Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Incidence
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.PlanarDrawing
import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Polygonal

/-!
# Planarity of explicit AND/OR multigraphs

Extract the listed incidence multigraph from the numbered NCL ports. Edge enumeration is bounded
by the explicit port list, including on malformed data with a large binary edge count. Planarity
means existence of a continuous polygonal embedding, with self-loops and parallel edges admitted.

## Main definitions

* `AndOrGraph.incidenceGraph` extracts the numbered incidence multigraph.
* `AndOrGraph.IsPlanar` states existence of a polygonal embedding.

## Main results

* `AndOrGraph.incidenceGraph_endpoints` shows that all incident endpoints are declared.
* `Word.isPlanar_compile` proves planarity of closed well-typed plane-word compilations.

## References

* [Hearn and Demaine][HearnDemaine2005, Theorem 9]
-/

public section

namespace Cslib.Complexity.NCL

namespace AndOrGraph

/-- The first vertex carrying a specified port, with zero as the default vertex index. -/
@[expose] def portVertex (g : AndOrGraph) (e : ℕ) (d : Bool) : ℕ :=
  ((g.vertices.zipIdx.find? fun v =>
    v.1.ports.any fun p => decide (p.port = ⟨e, d⟩)).map Prod.snd).getD 0

/-- The incidence multigraph, with vertex-list indices and one occurrence per declared edge.
Malformed edge counts exceeding the explicit port count produce an empty edge list. -/
@[expose] def incidenceGraph (g : AndOrGraph) : Cslib.Complexity.Graph :=
  let ps := g.vertices.flatMap Vertex.ports
  let m := if g.edgeCount ≤ ps.length then g.edgeCount else 0
  { vertices := List.range g.vertices.length
    edges := ((List.range ps.length).take m).map fun e =>
      (g.portVertex e false, g.portVertex e true) }

/-- The numbered multigraph admits a continuous real-plane polygonal embedding. -/
@[expose] def IsPlanar (g : AndOrGraph) : Prop :=
  ∃ D : Cslib.Complexity.Graph.PolygonalDrawing g.incidenceGraph, D.IsEmbedding

private theorem portVertex_lt (g : AndOrGraph) (hn : 0 < g.vertices.length) (e : ℕ)
    (d : Bool) : g.portVertex e d < g.vertices.length := by
  unfold portVertex
  cases h : g.vertices.zipIdx.find? (fun v =>
      v.1.ports.any fun p => decide (p.port = ⟨e, d⟩)) with
  | none => simpa only [Option.map_none, Option.getD_none] using hn
  | some v =>
    simpa only [Option.map_some, Option.getD_some, Nat.add_zero] using
      List.snd_lt_of_mem_zipIdx (List.mem_of_find?_eq_some h)

/-- All endpoints of the extracted incidence multigraph are declared, even for raw data. -/
theorem incidenceGraph_endpoints (g : AndOrGraph) :
    ∀ v ∈ g.incidenceGraph.incidenceVertices, v ∈ g.incidenceGraph.vertices := by
  intro v hv
  by_cases hn : 0 < g.vertices.length
  · change v ∈ List.range g.vertices.length
    apply List.mem_range.mpr
    simp only [Cslib.Complexity.Graph.incidenceVertices, incidenceGraph,
      List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hv
    obtain ⟨_, ⟨e, _, rfl⟩, rfl | rfl⟩ := hv
    · exact portVertex_lt g hn e false
    · exact portVertex_lt g hn e true
  · have hz : g.vertices = [] := List.length_eq_zero_iff.mp (by omega)
    simp [incidenceGraph, Cslib.Complexity.Graph.incidenceVertices, hz] at hv

private theorem raw_hasPort_iff (g : AndOrGraph) (hb : g.Bounded)
    (v : Fin g.vertices.length) (e : Fin g.edgeCount) (d : Bool) :
    (∃ w, (⟨⟨e.val, d⟩, w⟩ : WeightedPort ℕ) ∈ (g.vertices.get v).ports) ↔
      GridDrawing.HasPort g.graph v e d := by
  have h := GridDrawing.hasPort_map_iff g.graph Fin.val v e.val d
  rw [g.graph_map_val hb] at h
  change GridDrawing.HasPort (fun i : Fin g.vertices.length => g.vertices.get i) v e.val d ↔ _
  rw [h]
  constructor
  · rintro ⟨f, hf, he⟩
    exact Fin.ext he ▸ hf
  · intro hp
    exact ⟨e, hp, rfl⟩

private theorem portVertex_eq_of_drawing (g : AndOrGraph) (hb : g.Bounded)
    (D : GridDrawing.Closed g.graph) (e : Fin g.edgeCount) (d : Bool) :
    g.portVertex e.val d = (if d then D.target e else D.source e).val := by
  let v := if d then D.target e else D.source e
  have hp : GridDrawing.HasPort g.graph v e d := by
    cases d
    · exact D.source_port e
    · exact D.target_port e
  have hv : (g.vertices.get v, v.val) ∈ g.vertices.zipIdx := by
    simp only [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem v.isLt]
    rfl
  have hex : (g.vertices.zipIdx.find? fun v =>
      v.1.ports.any fun p => decide (p.port = ⟨e.val, d⟩)).isSome := by
    apply List.find?_isSome.mpr
    refine ⟨_, hv, ?_⟩
    obtain ⟨w, hw⟩ := (raw_hasPort_iff g hb v e d).mpr hp
    exact List.any_eq_true.mpr ⟨_, hw, by simp⟩
  cases hf : g.vertices.zipIdx.find? (fun v =>
      v.1.ports.any fun p => decide (p.port = ⟨e.val, d⟩)) with
  | none => simp only [hf, Option.isSome_none, Bool.false_eq_true] at hex
  | some u =>
    have hu := List.mem_of_find?_eq_some hf
    obtain ⟨hu', huget⟩ := List.mem_zipIdx' hu
    have hup := List.find?_some hf
    obtain ⟨p, hpu, hpe⟩ := List.any_eq_true.mp hup
    have hport : p.port = ⟨e.val, d⟩ := of_decide_eq_true hpe
    have hr : GridDrawing.HasPort g.graph ⟨u.2, hu'⟩ e d := by
      apply (raw_hasPort_iff g hb _ e d).mp
      refine ⟨p.weight, ?_⟩
      have hpeq : p = ⟨⟨e.val, d⟩, p.weight⟩ :=
        congrArg (fun q => (⟨q, p.weight⟩ : WeightedPort ℕ)) hport
      rw [← hpeq]
      change p ∈ g.vertices[u.2].ports
      rw [← huget]
      exact hpu
    have heq : (⟨u.2, hu'⟩ : Fin g.vertices.length) = v := by
      cases d
      · exact (D.source_eq _ _ hr).symm
      · exact (D.target_eq _ _ hr).symm
    simpa only [portVertex, hf, Option.map_some, Option.getD_some] using congrArg Fin.val heq

/-- The graph extracted from valid ports is the graph of any complete incidence drawing. -/
private theorem incidenceGraph_eq_drawing (g : AndOrGraph) (hg : g.Valid)
    (D : GridDrawing.Closed g.graph) : g.incidenceGraph = D.incidenceGraph := by
  have hc := portCount_eq_two_mul g hg.1 hg.2.2
  have hm : g.edgeCount ≤ (g.vertices.flatMap Vertex.ports).length := by omega
  apply Cslib.Complexity.Graph.ext
  · rfl
  · simp only [incidenceGraph, ite_eq_left hm, List.take_range, Nat.min_eq_left hm]
    rw [← List.map_coe_finRange_eq_range]
    simp only [List.map_map]
    rw [← List.ofFn_eq_map]
    congr 1
    funext e
    simp only [Function.comp_apply, portVertex_eq_of_drawing g hg.1 D e false,
      portVertex_eq_of_drawing g hg.1 D e true, Bool.false_eq_true, ↓reduceIte]

end AndOrGraph

/-- Every valid graph compiled from a closed well-typed plane word is planar. -/
theorem Word.isPlanar_compile {w : Word} (hP : w.checkPlane = true)
    (hT : w.WellTyped [] []) (hV : w.compile.Valid) : w.compile.IsPlanar := by
  obtain ⟨D, hD⟩ := Word.planarOrthogonalDrawing_compile hP hT
  rw [AndOrGraph.IsPlanar, AndOrGraph.incidenceGraph_eq_drawing _ hV D]
  exact ⟨hD.polygonalDrawing, hD.isEmbedding_polygonalDrawing⟩

end Cslib.Complexity.NCL

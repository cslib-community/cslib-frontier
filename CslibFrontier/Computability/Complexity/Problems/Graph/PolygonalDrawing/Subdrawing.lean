/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.IntersectionParity
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RegularContacts
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentRestriction
import Mathlib.Logic.Embedding.Basic

/-!
# Regular contacts of polygonal subdrawings

`PolygonalDrawing.subdrawing` retains literal routes at selected indexed edges.
`HasRegularContacts.subdrawing` shows that
regular contacts persist when selecting actual edge occurrences and identifying declared
vertex names with distinct source names. Each resulting segment is a literal source segment.
`EvenCrossings.of_route_restriction` carries even crossings and vertex marks to those routes.
This allows components of a cut graph to reuse the routes of the original drawing
in [issue #3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
`Cslib.Complexity.Graph.PolygonalDrawing.HasRegularContacts.exists_component_subdrawing`
applies both restrictions when the two copies of the cut vertex lie in different components.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open RotationCertificate

/-- Keep the literal routes of selected edge occurrences, reading each target vertex at
its corresponding source label. The endpoint compatibility retains the original end tags. -/
@[expose] def subdrawing {G H : Graph} (D : PolygonalDrawing G)
    (edges : Fin H.edges.length ↪ Fin G.edges.length)
    (label : ℕ → ℕ)
    (hEnds : ∀ i b, Dart.vertex (G := G) (edges i, b) = label (Dart.vertex (G := H) (i, b))) :
    PolygonalDrawing H where
  vertex := D.vertex ∘ label
  route i := D.route (edges i)
  endpoint_eq i b := (D.endpoint_eq (edges i) b).trans (congrArg D.vertex (hEnds i b))

/-- A subdrawing inherits regular contacts when its declared vertex labels inject into
the source declarations and every selected endpoint is declared in the subgraph. -/
theorem HasRegularContacts.subdrawing {G H : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (edges : Fin H.edges.length ↪ Fin G.edges.length) (label : ℕ → ℕ)
    (hEnds : ∀ i b, Dart.vertex (G := G) (edges i, b) = label (Dart.vertex (G := H) (i, b)))
    (hdecl : ∀ v ∈ H.incidenceVertices, v ∈ H.vertices)
    (hlabel : Set.MapsTo label {v | v ∈ H.vertices} {v | v ∈ G.vertices})
    (hinj : Set.InjOn label {v | v ∈ H.vertices}) :
    (D.subdrawing edges label hEnds).HasRegularContacts := by
  let A := D.subdrawing edges label hEnds
  let seg : A.SegmentIndex ↪ D.SegmentIndex := edges.sigmaMap fun _ => Function.Embedding.refl _
  refine ⟨fun i => hD.points_injective (edges i), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j s hs v hv he
    obtain ⟨b, hb, hvb⟩ := hD.vertex_contacts (edges i) j s hs (label v) (hlabel hv) he
    exact ⟨b, hb, hinj (RotationSystem.vertex_mem hdecl (i, b)) hv ((hEnds i b).symm.trans hvb)⟩
  · intro i j
    exact hD.endpoints_avoid_interiors (seg i) (seg j)
  · intro i j hij z hzi hzj
    exact hD.lines_ne_at_intersections (seg i) (seg j) (seg.injective.ne hij) z hzi hzj
  · intro k z h
    exact hD.no_open_triple (k.trans seg) z h
  · intro i j hij s t hs ht he
    obtain ⟨v, hv, hvEq⟩ := hD.shared_ends_are_vertices (seg i) (seg j)
      (edges.injective.ne hij) hs ht he
    have hendTimes : ({0, 1} : Set ℝ) ⊆ Set.Icc 0 1 :=
      Set.pair_subset_iff.mpr ⟨Set.left_mem_Icc.mpr zero_le_one, Set.right_mem_Icc.mpr zero_le_one⟩
    obtain ⟨b, _, hvb⟩ := hD.vertex_contacts (edges i.1) i.2 s (hendTimes hs) v hv hvEq.symm
    refine ⟨Dart.vertex (G := H) (i.1, b), RotationSystem.vertex_mem hdecl (i.1, b), ?_⟩
    change D.vertex (label (Dart.vertex (G := H) (i.1, b))) = _
    rw [← hEnds, hvb]
    exact hvEq

/-- Selecting literal routes transports even crossings and the marked vertices. Injectivity
on the retained vertex labels ensures that two independent edges remain independent in the
source graph. -/
theorem EvenCrossings.of_route_restriction {G H : Graph} {D : PolygonalDrawing G}
    {A : PolygonalDrawing H} {marked : ℕ → Prop} (hD : D.EvenCrossings marked)
    (edges : Fin H.edges.length ↪ Fin G.edges.length) (label : ℕ → ℕ)
    (hEnds : ∀ i b, Dart.vertex (G := G) (edges i, b) = label (Dart.vertex (G := H) (i, b)))
    (hdecl : ∀ v ∈ H.incidenceVertices, v ∈ H.vertices)
    (hinj : Set.InjOn label {v | v ∈ H.vertices}) (hroute : ∀ i, A.route i = D.route (edges i)) :
    A.EvenCrossings (marked ∘ label) := by
  intro i j hij hpair
  rw [hroute i, hroute j]
  apply hD (edges i) (edges j) (edges.injective.ne hij)
  rcases hpair with h | ⟨b, c, he, hm⟩
  · refine Or.inl fun b c he => h b c ?_
    rw [hEnds i b, hEnds j c] at he
    exact hinj (RotationSystem.vertex_mem hdecl (i, b))
      (RotationSystem.vertex_mem hdecl (j, c)) he
  · refine Or.inr ⟨b, c, ?_, ?_⟩
    · rw [hEnds i b, hEnds j c, he]
    · rwa [hEnds i b]

/-- A component of a split graph inherits the source routes and vertex points when identifying
the two split labels recovers their original incidences and the labels are in different
components. Both component drawings can reuse one original vertex point. Marked even
crossings are inherited by pulling the marks back along the vertex labels. -/
theorem HasRegularContacts.exists_component_subdrawing {G H : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (edges : Fin H.edges.length ↪ Fin G.edges.length)
    (w v : ℕ) (hv : v ∈ G.vertices) (hsep : ¬SameComponent H w v)
    (hdecl : ∀ u ∈ H.incidenceVertices, u ∈ H.vertices)
    (hvertices : ∀ u ∈ H.vertices, u = w ∨ u ∈ G.vertices)
    (hEnds : ∀ i b, Dart.vertex (G := G) (edges i, b) =
      Function.update id w v (Dart.vertex (G := H) (i, b))) (root : ℕ) :
    ∃ A : PolygonalDrawing (H.componentGraph root), A.HasRegularContacts ∧
      (∀ i, A.route i = D.route (edges (H.componentEdgeEquiv root i).val)) ∧
      A.vertex = D.vertex ∘ Function.update id w v ∧
      Set.MapsTo (Function.update id w v) {u | u ∈ (H.componentGraph root).vertices}
        {u | u ∈ G.vertices} ∧
      Set.InjOn (Function.update id w v) {u | u ∈ (H.componentGraph root).vertices} ∧
      (∀ marked, D.EvenCrossings marked → A.EvenCrossings (marked ∘ Function.update id w v)) := by
  let K := H.componentGraph root
  let label := Function.update id w v
  let e : Fin K.edges.length ↪ Fin G.edges.length :=
    (H.componentEdgeEquiv root).toEmbedding.trans ((Function.Embedding.subtype _).trans edges)
  have hcoord (i : Fin K.edges.length) (b : Bool) :
      Dart.vertex (G := G) (e i, b) = label (Dart.vertex (G := K) (i, b)) := by
    rw [H.vertex_componentEdgeEquiv root i b]
    exact hEnds _ _
  have hmem {u : ℕ} (hu : u ∈ K.vertices) : u ∈ H.vertices ∧ SameComponent H root u := by
    simpa only [K, H.mem_componentGraph_vertices, Graph.componentVertexSet, Finset.mem_filter,
      List.mem_toFinset] using hu
  have hmap : Set.MapsTo label {u | u ∈ K.vertices} {u | u ∈ G.vertices} := by
    intro u hu
    change label u ∈ G.vertices
    by_cases huw : u = w
    · subst u
      simpa only [label, Function.update_self] using hv
    · simpa only [label, Function.update_of_ne huw, id_eq] using
        (hvertices u (hmem hu).1).resolve_left huw
  have hinj : Set.InjOn label {u | u ∈ K.vertices} := by
    intro a ha b hb he
    have hca := (hmem ha).2
    have hcb := (hmem hb).2
    by_cases haw : a = w
    · subst a
      by_cases hbw : b = w
      · exact hbw.symm
      have hvb : v = b := by
        simpa only [label, Function.update_self, Function.update_of_ne hbw, id_eq] using he
      exact (hsep (hvb.symm ▸ hca.symm.trans hcb)).elim
    by_cases hbw : b = w
    · subst b
      have hav : a = v := by
        simpa only [label, Function.update_self, Function.update_of_ne haw, id_eq] using he
      exact (hsep (hav ▸ hcb.symm.trans hca)).elim
    · simpa only [label, Function.update_of_ne haw, Function.update_of_ne hbw, id_eq] using he
  have hKdecl := H.componentGraph_endpoints_declared root hdecl
  exact ⟨D.subdrawing e label hcoord, hD.subdrawing e label hcoord hKdecl hmap hinj,
    fun _ => rfl, rfl, hmap, hinj, fun _ hm =>
      hm.of_route_restriction e label hcoord hKdecl hinj (fun _ => rfl)⟩

end Cslib.Complexity.Graph.PolygonalDrawing

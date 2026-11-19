/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Routes
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Orthogonal.Polygonal
import Mathlib.Data.List.GetD

/-!
# Supplied orthogonal embeddings as polygonal embeddings

Every actual integer route is retained segment for segment. Existing route normalization
chooses the graph's first-to-second endpoint orientation; the coordinate map sends `(x,y)`
to `x+yi`, preserving the orientation of the real plane. The polygonal contact conditions
follow from the original full-segment contact certificates and injectivity of each complete
route parameter. No rotation, numerical genus or drawing provider is assumed.

This is original representation transport for the native supplied-drawing SAT compiler.
It is a static proof-side conversion, not an algorithm on arbitrary complex coordinates.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Orthogonal OrthogonalDrawing

/-- Convert a genuine supplied integer drawing to the existing polygonal drawing model,
retaining the original listed graph, vertices and indexed edge occurrences. -/
@[expose] noncomputable def IsPlanarOrthogonalDrawing.polygonalDrawing
    {G : Graph} {d : OrthogonalDrawing} (hd : IsPlanarOrthogonalDrawing G d) :
    PolygonalDrawing G where
  vertex v := complexPoint (drawingPosition G d v)
  route e := toPolygonalRoute (sourceRoute G d e).reverse
    (by simpa only [List.length_reverse] using sourceRoute_length_ge_two hd e.isLt)
  endpoint_eq e side := by
    have he := sourceRoute_endpoints hd e.isLt
    have hlen : 2 ≤ (sourceRoute G d e).reverse.length := by
      simpa only [List.length_reverse] using sourceRoute_length_ge_two hd e.isLt
    have hhead : (sourceRoute G d e).reverse.head? = some (sourceFinish G d e) := by
      simpa only [List.head?_reverse] using he.2
    have hlast : (sourceRoute G d e).reverse.getLast? = some (sourceStart G d e) := by
      simpa only [List.getLast?_reverse] using he.1
    cases side
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
      change (toPolygonalRoute _ _).start = _
      rw [start_toPolygonalRoute, Option.some.inj hhead]
      unfold sourceFinish Dart.vertex edgeEndpoint
      rw [List.getD_eq_getElem _ _ e.isLt]
      rfl
    · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
      change (toPolygonalRoute _ _).finish = _
      rw [finish_toPolygonalRoute, Option.some.inj hlast]
      unfold sourceStart Dart.vertex edgeEndpoint
      rw [List.getD_eq_getElem _ _ e.isLt]
      rfl

private theorem polygonalDrawing_eval_mem_support {G : Graph} {d : OrthogonalDrawing}
    (hd : IsPlanarOrthogonalDrawing G d) (e : Fin G.edges.length)
    (i : Fin (hd.polygonalDrawing.route e).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProdCLM ((hd.polygonalDrawing.route e).eval i t) ∈
      support (d.2.getD e []) := by
  have hlen : 2 ≤ (sourceRoute G d e).reverse.length := by
    simpa only [List.length_reverse] using sourceRoute_length_ge_two hd e.isLt
  rw [← support_sourceRoute G d e, ← support_reverse (sourceRoute G d e)]
  exact eval_toPolygonalRoute_mem_support _ hlen i ht

private theorem polygonalDrawing_vertex_contact {G : Graph} {d : OrthogonalDrawing}
    (hd : IsPlanarOrthogonalDrawing G d) (e : Fin G.edges.length)
    (i : Fin (hd.polygonalDrawing.route e).segments) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (v : ℕ) (hv : v ∈ G.vertices)
    (he : (hd.polygonalDrawing.route e).eval i t = hd.polygonalDrawing.vertex v) :
    ∃ b, (hd.polygonalDrawing.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v := by
  have hlen : 2 ≤ (sourceRoute G d e).reverse.length := by
    simpa only [List.length_reverse] using sourceRoute_length_ge_two hd e.isLt
  have hsimple := (isSimple_reverse_iff _).mpr (sourceRoute_regular hd e.isLt).2
  have hs := polygonalDrawing_eval_mem_support hd e i ht
  have he' := congrArg Complex.equivRealProdCLM he
  change Complex.equivRealProdCLM ((hd.polygonalDrawing.route e).eval i t) =
    Complex.equivRealProdCLM (complexPoint (drawingPosition G d v)) at he'
  rw [equivRealProd_complexPoint] at he'
  rw [he'] at hs
  obtain hfirst | hsecond := hd.avoidsVertices e e.isLt v hv hs
  · have hv' : Dart.vertex (e, false) = v := by
      unfold Dart.vertex edgeEndpoint
      rw [List.getD_eq_getElem _ _ e.isLt]
      exact hfirst.symm
    refine ⟨false, ?_, hv'⟩
    apply (eval_toPolygonalRoute_eq_endpoint_iff hsimple hlen i t ht false).mp
    exact he.trans ((hd.polygonalDrawing.endpoint_eq e false).trans
      (congrArg hd.polygonalDrawing.vertex hv')).symm
  · have hv' : Dart.vertex (e, true) = v := by
      unfold Dart.vertex edgeEndpoint
      rw [List.getD_eq_getElem _ _ e.isLt]
      exact hsecond.symm
    refine ⟨true, ?_, hv'⟩
    apply (eval_toPolygonalRoute_eq_endpoint_iff hsimple hlen i t ht true).mp
    exact he.trans ((hd.polygonalDrawing.endpoint_eq e true).trans
      (congrArg hd.polygonalDrawing.vertex hv')).symm

/-- Full real-support orthogonal drawing validity implies the actual polygonal embedding
contract, with no supplied rotation or topological comparison premise. -/
theorem IsPlanarOrthogonalDrawing.isEmbedding_polygonalDrawing
    {G : Graph} {d : OrthogonalDrawing} (hd : IsPlanarOrthogonalDrawing G d) :
    hd.polygonalDrawing.IsEmbedding where
  vertices_injective := fun _ hv _ hw he => drawingPosition_injOn hd hv hw
    (complexPoint_injective he)
  simple e := isSimple_toPolygonalRoute
    ((isSimple_reverse_iff _).mpr (sourceRoute_regular hd e.isLt).2)
    (by simpa only [List.length_reverse] using sourceRoute_length_ge_two hd e.isLt)
  vertex_contacts := polygonalDrawing_vertex_contact hd
  edge_contacts e f hef i j s t hs ht he := by
    have hfirst := polygonalDrawing_eval_mem_support hd e i hs
    have hsecond := polygonalDrawing_eval_mem_support hd f j ht
    rw [← he] at hsecond
    obtain ⟨v, hv, _, _, hp⟩ := hd.contacts e e.isLt f f.isLt
      (fun h => hef (Fin.ext h)) _ hfirst hsecond
    have heval : (hd.polygonalDrawing.route e).eval i s = hd.polygonalDrawing.vertex v := by
      apply Complex.equivRealProdCLM.injective
      exact hp.trans (equivRealProd_complexPoint _).symm
    obtain ⟨b, hb, hbe⟩ := polygonalDrawing_vertex_contact hd e i s hs v hv heval
    obtain ⟨c, hc, hce⟩ := polygonalDrawing_vertex_contact hd f j t ht v hv (he.symm.trans heval)
    exact ⟨b, c, hb, hc, hbe.trans hce.symm⟩

end Cslib.Complexity.Graph

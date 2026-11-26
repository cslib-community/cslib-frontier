/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Certificate
import CslibFrontier.Foundations.Geometry.Polygonal.Germs

/-!
# Replacing routes in polygonal embeddings

A replacement drawing with the same vertex positions and indexed route supports is embedded
when its new routes are simple and the graph declares every edge endpoint. The contact proof
recovers the endpoint name from the point, allowing both end tags of a loop.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

private theorem exists_atEnd_of_eval_eq_endpoint {p : Route} (hp : p.IsSimple)
    (i : Fin p.segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (b : Bool)
    (heq : p.eval i t = p.endpoint b) : ∃ c, p.AtEnd i t c := by
  have hend : p.eval (p.endSegment b) (Route.endTime b 0) = p.endpoint b := by
    simpa only [zero_smul, add_zero] using p.eval_near_end b 0
  rcases hp i (p.endSegment b) t (Route.endTime b 0) ht
      (Route.endTime_mem b ⟨le_rfl, zero_le_one⟩) (heq.trans hend.symm) with h | h | h
  · refine ⟨b, ?_⟩
    rw [Route.AtEnd, h, p.position_near_end]
    cases b <;> simp
  · exact ⟨false, h.1⟩
  · exact ⟨true, h.1⟩

/-- Simple replacement routes with unchanged supports and vertex positions preserve an
embedding of a graph whose edge endpoints are declared. -/
theorem IsEmbedding.of_same_route_supports {G : Graph} {D E : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hvertex : E.vertex = D.vertex) (hsimple : ∀ e, (E.route e).IsSimple)
    (hsupport : ∀ e, (E.route e).support = (D.route e).support) : E.IsEmbedding := by
  have hinj : Set.InjOn E.vertex {v | v ∈ G.vertices} := hvertex ▸ hD.vertices_injective
  have sample (e : Fin G.edges.length) (i : Fin (E.route e).segments) (t : ℝ)
      (ht : t ∈ Set.Icc 0 1) :
      ∃ (j : Fin (D.route e).segments) (s : ℝ), s ∈ Set.Icc 0 1 ∧
        (D.route e).eval j s = (E.route e).eval i t :=
    ((D.route e).mem_support_iff _).mp (hsupport e ▸ (E.route e).at_mem_support i ht)
  have end_at (e : Fin G.edges.length) (i : Fin (E.route e).segments) (t : ℝ)
      (ht : t ∈ Set.Icc 0 1) (b : Bool)
      (heq : (E.route e).eval i t = E.vertex (Dart.vertex (e, b))) :
      ∃ c, (E.route e).AtEnd i t c ∧ Dart.vertex (e, c) = Dart.vertex (e, b) := by
    obtain ⟨c, hc⟩ := exists_atEnd_of_eval_eq_endpoint (hsimple e) i ht b
      (heq.trans (E.endpoint_eq e b).symm)
    refine ⟨c, hc, hinj (RotationSystem.vertex_mem hG (e, c))
      (RotationSystem.vertex_mem hG (e, b)) ?_⟩
    calc
      E.vertex (Dart.vertex (e, c)) = (E.route e).endpoint c := (E.endpoint_eq e c).symm
      _ = (E.route e).eval i t := ((E.route e).at_eq_endpoint i ht c hc).symm
      _ = E.vertex (Dart.vertex (e, b)) := heq
  refine ⟨hinj, hsimple, ?_, ?_⟩
  · intro e i t ht v hv heq
    obtain ⟨j, s, hs, hj⟩ := sample e i t ht
    obtain ⟨b, _, hb⟩ :=
      hD.vertex_contacts e j s hs v hv (hj.trans (by simpa only [hvertex] using heq))
    obtain ⟨c, hc, hcb⟩ := end_at e i t ht b (by simpa only [hb] using heq)
    exact ⟨c, hc, hcb.trans hb⟩
  · intro e f hef i j s t hs ht heq
    obtain ⟨i', s', hs', hi'⟩ := sample e i s hs
    obtain ⟨j', t', ht', hj'⟩ := sample f j t ht
    obtain ⟨b, c, hb, hc, hbc⟩ :=
      hD.edge_contacts e f hef i' j' s' t' hs' ht' (hi'.trans (heq.trans hj'.symm))
    have same_end (k) (l : Fin (D.route k).segments) (u) (hu : u ∈ Set.Icc 0 1) (a)
        (ha : (D.route k).AtEnd l u a) : (D.route k).eval l u = E.vertex (Dart.vertex (k, a)) :=
      ((D.route k).at_eq_endpoint l hu a ha).trans ((D.endpoint_eq k a).trans (hvertex ▸ rfl))
    obtain ⟨b', hb', heb⟩ := end_at e i s hs b (hi'.symm.trans (same_end e i' s' hs' b hb))
    obtain ⟨c', hc', hfc⟩ := end_at f j t ht c (hj'.symm.trans (same_end f j' t' ht' c hc))
    exact ⟨b', c', hb', hc', heb.trans (hbc.trans hfc.symm)⟩

end Cslib.Complexity.Graph.PolygonalDrawing

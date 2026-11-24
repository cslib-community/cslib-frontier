/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.CutTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RouteSupports
import CslibFrontier.Foundations.Geometry.Polygonal.Germs
import CslibFrontier.Foundations.Geometry.Polygonal.SquareMove

/-!
# Square moves of embedded drawings with fixed routes

A local square move can send its center vertex to a nearby target while leaving every
exterior vertex fixed. An indexed edge that stays outside the open square retains its
entire original route, including its listed bends, even if the transport subdivides
other routes.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- Move the square's center vertex to a point less than the half-width away. The resulting
embedding fixes the coordinates of vertices outside the open square and leaves any route
whose entire support avoids the open square literally unchanged. -/
theorem IsEmbedding.exists_square_move {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (v : ℕ) (b : ℂ) {r : ℝ} (hr : 0 < r) (hb : ‖b - D.vertex v‖ < r) :
    ∃ E : PolygonalDrawing G, E.IsEmbedding ∧ E.vertex v = b ∧
      (∀ w, r ≤ max |(D.vertex w).re - (D.vertex v).re| |(D.vertex w).im - (D.vertex v).im| →
        E.vertex w = D.vertex w) ∧
      ∀ e, (∀ z ∈ (D.route e).support,
        r ≤ max |z.re - (D.vertex v).re| |z.im - (D.vertex v).im|) → E.route e = D.route e := by
  classical
  obtain ⟨F, walls, hinj, hv, hfixed, hline⟩ := Polygonal.exists_square_move (D.vertex v) b hr hb
  obtain ⟨P, hP, hvertex, hsupport⟩ := hD.exists_image_across_walls walls hinj hline
  let exterior (z : ℂ) : Prop := r ≤ max |z.re - (D.vertex v).re| |z.im - (D.vertex v).im|
  let fixed (e : Fin G.edges.length) : Prop := ∀ z ∈ (D.route e).support, exterior z
  let routes (e : Fin G.edges.length) := if fixed e then D.route e else P.route e
  have route_fixed (e : Fin G.edges.length) (he : fixed e) : routes e = D.route e := by
    simp [routes, he]
  have route_moved (e : Fin G.edges.length) (he : ¬fixed e) : routes e = P.route e := by
    simp [routes, he]
  have hend (e : Fin G.edges.length) (side : Bool) :
      (routes e).endpoint side = P.vertex (Dart.vertex (e, side)) := by
    by_cases he : fixed e
    · have hm := (D.route e).at_mem_support ((D.route e).endSegment side)
        (Route.endTime_mem side (t := 0) ⟨le_rfl, zero_le_one⟩)
      rw [(D.route e).eval_near_end, zero_smul, add_zero] at hm
      have heq := hfixed _ (he _ hm)
      rw [route_fixed e he, hvertex, Function.comp_apply, ← D.endpoint_eq e side, heq]
    · simpa only [route_moved e he] using P.endpoint_eq e side
  let E : PolygonalDrawing G := ⟨P.vertex, routes, hend⟩
  have hsimple (e : Fin G.edges.length) : (routes e).IsSimple := by
    by_cases he : fixed e
    · simpa only [route_fixed e he] using hD.simple e
    · simpa only [route_moved e he] using hP.simple e
  have hsame (e : Fin G.edges.length) : (routes e).support = (P.route e).support := by
    by_cases he : fixed e
    · rw [route_fixed e he, hsupport e]
      ext z
      constructor
      · intro hz
        exact ⟨z, hz, hfixed z (he z hz)⟩
      · rintro ⟨w, hw, rfl⟩
        rwa [hfixed w (he w hw)]
    · simp only [route_moved e he]
  refine ⟨E, hP.of_same_route_supports hG rfl hsimple hsame, ?_, ?_, ?_⟩
  · change P.vertex v = b
    rw [hvertex]
    exact hv
  · intro w hw
    change P.vertex w = D.vertex w
    rw [hvertex]
    exact hfixed _ hw
  · intro e he
    exact route_fixed e he

end Cslib.Complexity.Graph.PolygonalDrawing

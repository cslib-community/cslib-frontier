/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.Neighborhood

/-!
# Local segment neighborhoods of polygonal graph drawings

A vertex reached only at its incident route endpoints has a positive-radius ball
meeting only the first or last segments at that vertex. The finite segment arrangement
supplies the radius, retaining both ends of a loop. A polygonal embedding satisfies
the vertex contact hypothesis for every declared vertex.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- If the drawing reaches a vertex only at its corresponding endpoint parameters,
then a neighborhood of that vertex meets only its first or last incident segments. -/
theorem exists_vertex_ball_of_vertex_contacts {G : Graph} (D : PolygonalDrawing G) (v : ℕ)
    (hcontacts : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.route e).eval i t = D.vertex v →
        ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v) :
    ∃ ε > 0, ∀ e (i : Fin (D.route e).segments) w,
      w ∈ Metric.ball (D.vertex v) ε →
      w ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
        (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v) := by
  let ι := (e : Fin G.edges.length) × Fin (D.route e).segments
  obtain ⟨ε, hε, hball⟩ := Polygonal.exists_ball_only_incident_segments
    (fun p : ι => (D.route p.1).point p.2.castSucc)
    (fun p : ι => (D.route p.1).point p.2.succ) (D.vertex v)
  refine ⟨ε, hε, fun e i w hw hseg => ?_⟩
  have hcenter := hball ⟨e, i⟩ w hw hseg
  rw [segment_eq_image_lineMap] at hcenter
  obtain ⟨t, ht, heq⟩ := hcenter
  obtain ⟨b, hb, hvertex⟩ := hcontacts e i t ht heq
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi1 : (i.val : ℝ) + 1 ≤ (D.route e).segments := by exact_mod_cast i.isLt
  cases b
  · left
    refine ⟨?_, hvertex⟩
    have hi : (i.val : ℝ) = 0 := by
      dsimp [Polygonal.Route.AtEnd, Polygonal.Route.position] at hb
      linarith [ht.1]
    exact_mod_cast hi
  · right
    refine ⟨?_, hvertex⟩
    have hi : (i.val : ℝ) + 1 = (D.route e).segments := by
      dsimp [Polygonal.Route.AtEnd, Polygonal.Route.position] at hb
      linarith [ht.2]
    exact_mod_cast hi

/-- Near a declared vertex, every segment met by an embedding is an actual first or last
segment at that named vertex. -/
theorem IsEmbedding.exists_vertex_ball {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) (hv : v ∈ G.vertices) :
    ∃ ε > 0, ∀ e (i : Fin (D.route e).segments) w,
      w ∈ Metric.ball (D.vertex v) ε →
      w ∈ segment ℝ ((D.route e).point i.castSucc) ((D.route e).point i.succ) →
        (i.val = 0 ∧ Dart.vertex (e, false) = v) ∨
        (i.val + 1 = (D.route e).segments ∧ Dart.vertex (e, true) = v) :=
  D.exists_vertex_ball_of_vertex_contacts v (fun e i t ht => hD.vertex_contacts e i t ht v hv)

end Cslib.Complexity.Graph.PolygonalDrawing

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary public API clients)

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.VertexPlacement
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star

/-! # Prescribed vertex placement clients -/

public section

namespace CslibFrontierTests.PolygonalVertexPlacement

open Cslib.Complexity Graph RotationSystem PolygonalDrawing

-- Every target is occupied. In particular the center and its leaves cannot be placed
-- by moving any one vertex directly to its target first.
example : ∃ E : PolygonalDrawing (starGraph 3), E.IsEmbedding ∧
    E.vertex 0 = (PolygonalDrawing.star 3).vertex 1 ∧
    E.vertex 1 = (PolygonalDrawing.star 3).vertex 2 ∧
    E.vertex 2 = (PolygonalDrawing.star 3).vertex 3 ∧
    E.vertex 3 = (PolygonalDrawing.star 3).vertex 0 ∧
    (∀ a : Dart (starGraph 3), E.direction a = (PolygonalDrawing.star 3).direction a) := by
  let D := PolygonalDrawing.star 3
  let q (v : ℕ) := D.vertex ((v + 1) % 4)
  have hD := star_isEmbedding 3
  have hnames (v : ℕ) : v ∈ (starGraph 3).vertices ↔ v < 4 := by
    simp [starGraph]
  have hq : Set.InjOn q {v | v ∈ (starGraph 3).vertices} := by
    intro v hv w hw he
    have hmod : (v + 1) % 4 = (w + 1) % 4 := hD.vertices_injective
      ((hnames _).mpr (Nat.mod_lt _ (by decide)))
      ((hnames _).mpr (Nat.mod_lt _ (by decide))) he
    have hv' := (hnames v).mp hv
    have hw' := (hnames w).mp hw
    omega
  obtain ⟨E, hE, hpos, _, hdir, _, _⟩ := hD.exists_vertex_placement (by decide) q hq
  exact ⟨E, hE, hpos 0 (by decide), hpos 1 (by decide), hpos 2 (by decide),
    hpos 3 (by decide), hdir⟩

example : ∃ E : PolygonalDrawing (starGraph 3),
    E.IsEmbedding ∧ E = PolygonalDrawing.star 3 := by
  have hD := star_isEmbedding 3
  obtain ⟨E, hE, _, _, _, _, hid⟩ :=
    hD.exists_vertex_placement (by decide) _ hD.vertices_injective
  exact ⟨E, hE, hid (fun _ _ => rfl)⟩

end CslibFrontierTests.PolygonalVertexPlacement

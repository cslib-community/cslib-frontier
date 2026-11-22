/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary client of path transport)

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.PathTransport
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic.NormNum

/-!
The leaf of a one-edge star moves from `(1, 1)` to `(1, 3)` along a path above the real
axis. Protecting the axis fixes the center.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PolygonalPathTransport

open Cslib Cslib.Complexity Graph RotationSystem

example :
    ∃ E : PolygonalDrawing (starGraph 1), E.IsEmbedding ∧ E.vertex 0 = ⟨1, 3⟩ ∧
      E.vertex 1 = 0 := by
  let D := PolygonalDrawing.star 1
  have hleaf : D.vertex 0 = ⟨1, 1⟩ := by
    norm_num [D, PolygonalDrawing.star, PolygonalDrawing.starPoint]
  have hcenter : D.vertex 1 = 0 := by
    simp [D, PolygonalDrawing.star, PolygonalDrawing.starPoint]
  let K : Set ℂ := {z | z.im = 0}
  have hK : IsClosed K := isClosed_eq Complex.continuous_im continuous_const
  let p := Path.segment (D.vertex 0) (⟨1, 3⟩ : ℂ)
  have hp : Set.range p ⊆ Kᶜ := by
    dsimp only [p]
    rw [Path.range_segment, segment_eq_image_lineMap]
    rintro z ⟨t, ht, rfl⟩ hz
    change (AffineMap.lineMap (D.vertex 0) (⟨1, 3⟩ : ℂ) t).im = 0 at hz
    rw [hleaf] at hz
    norm_num [AffineMap.lineMap_apply_module', Complex.add_im, Complex.smul_im,
      Complex.sub_im, smul_eq_mul] at hz
    linarith only [hz, ht.1]
  have hother (w : ℕ) (hw : w ∈ (starGraph 1).vertices) (hne : w ≠ 0) :
      D.vertex w ∈ K := by
    have hw' : w < 2 := by simpa [starGraph] using hw
    have hone : w = 1 := by omega
    rw [hone, hcenter]
    exact Complex.zero_im
  obtain ⟨E, hE, hleaf', hfixed, _⟩ :=
    (PolygonalDrawing.star_isEmbedding 1).exists_vertex_move_along_path
      (starGraph_endpoints_declared 1) 0 p hK hp hother ∅ (by simp)
  have hcenterMem : 1 ∈ (starGraph 1).vertices := by simp [starGraph]
  exact ⟨E, hE, hleaf', (hfixed 1 hcenterMem (by decide)).trans hcenter⟩

end CslibFrontierTests.PolygonalPathTransport

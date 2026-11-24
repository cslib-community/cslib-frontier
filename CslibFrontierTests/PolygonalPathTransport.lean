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
axis. Protecting the axis fixes the center. A second client asks the transport theorem to find
its own path around an occupied leaf while fixing the spoke in a closed half-plane.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PolygonalPathTransport

open Cslib Polygonal Cslib.Complexity Graph RotationSystem

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

private def keptEdge : Fin (starGraph 3).edges.length := ⟨0, by decide⟩

example :
    ∃ E : PolygonalDrawing (starGraph 3), E.IsEmbedding ∧ E.vertex 1 = ⟨4, 1⟩ ∧
      E.vertex 2 = ⟨3, 1⟩ ∧ E.route keptEdge = (PolygonalDrawing.star 3).route keptEdge := by
  let D := PolygonalDrawing.star 3
  let K : Set ℂ := {z | z.re ≤ 3 / 2}
  have hK : IsClosed K := isClosed_Iic.preimage Complex.continuous_re
  have hopen : IsPathConnected Kᶜ := by
    have heq : Kᶜ = Complex.reCLM.toLinearMap ⁻¹' Set.Ioi (3 / 2) := by
      ext z
      change (¬ z.re ≤ (3 / 2 : ℝ)) ↔ (3 / 2 : ℝ) < z.re
      exact not_le
    rw [heq]
    refine ((convex_Ioi (𝕜 := ℝ) _).linear_preimage Complex.reCLM.toLinearMap).isPathConnected
      ⟨(2 : ℂ), ?_⟩
    change (3 / 2 : ℝ) < (2 : ℂ).re
    norm_num
  have hv : 1 ∈ (starGraph 3).vertices := by decide
  have hsource : D.vertex 1 ∉ K := by
    change ¬ (D.vertex 1).re ≤ (3 / 2 : ℝ)
    norm_num [D, PolygonalDrawing.star, PolygonalDrawing.starPoint]
  have htarget : (⟨4, 1⟩ : ℂ) ∉ K := by
    change ¬ (4 : ℝ) ≤ 3 / 2
    norm_num
  have hvacant : ∀ w ∈ (starGraph 3).vertices, w ≠ 1 → (⟨4, 1⟩ : ℂ) ≠ D.vertex w := by
    intro w hw hne heq
    have hlt : w < 4 := by simpa [starGraph] using hw
    have hcases : w = 0 ∨ w = 2 ∨ w = 3 := by omega
    have hre := congrArg Complex.re heq
    rcases hcases with rfl | rfl | rfl <;>
      norm_num [D, PolygonalDrawing.star, PolygonalDrawing.starPoint] at hre
  have hkeep : (D.route keptEdge).support ⊆ K := by
    change (Route.line ⟨(keptEdge.val : ℝ) + 1, 1⟩ 0).support ⊆ K
    rw [Route.support_line]
    have hconv : Convex ℝ K :=
      (convex_Iic _).linear_preimage Complex.reCLM.toLinearMap
    apply hconv.segment_subset
    · norm_num [keptEdge, K]
    · norm_num [K]
  obtain ⟨E, hE, hv', hfixed, hroutes⟩ :=
    (PolygonalDrawing.star_isEmbedding 3).exists_vertex_move_in_compl
      (starGraph_endpoints_declared 3) 1 hv hK hopen hsource htarget hvacant
      {keptEdge} (by rintro e rfl; exact hkeep)
  refine ⟨E, hE, hv', (hfixed 2 (by decide) (by decide)).trans ?_, hroutes keptEdge rfl⟩
  norm_num [D, PolygonalDrawing.star, PolygonalDrawing.starPoint]

end CslibFrontierTests.PolygonalPathTransport

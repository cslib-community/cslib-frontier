/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary square-move client)

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SquareMove
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import Mathlib.Tactic.NormNum

/-!
Move one leaf of a two-edge star while keeping the other edge's whole route. The unchanged
route meets the moving route at the center, so the client also exercises the mixed contact case.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PolygonalSquareMove

open Cslib Polygonal Cslib.Complexity Graph RotationSystem

private def fixedEdge : Fin (starGraph 2).edges.length := ⟨1, by decide⟩

example :
    ∃ E : PolygonalDrawing (starGraph 2), E.IsEmbedding ∧ E.vertex 0 = ⟨9 / 8, 1⟩ ∧
      E.vertex 2 = 0 ∧ E.route fixedEdge = (PolygonalDrawing.star 2).route fixedEdge := by
  let D := PolygonalDrawing.star 2
  have hleaf : D.vertex 0 = ⟨1, 1⟩ := by
    norm_num [D, PolygonalDrawing.star, PolygonalDrawing.starPoint]
  have hcenter : D.vertex 2 = 0 := by
    simp [D, PolygonalDrawing.star, PolygonalDrawing.starPoint]
  have hmove : ‖(⟨9 / 8, 1⟩ : ℂ) - D.vertex 0‖ < (1 / 4 : ℝ) := by
    rw [hleaf]
    have hdiff : (⟨9 / 8, 1⟩ : ℂ) - ⟨1, 1⟩ = ((1 / 8 : ℝ) : ℂ) := by
      apply Complex.ext <;> norm_num
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hroute : (D.route fixedEdge).support = segment ℝ (⟨2, 1⟩ : ℂ) 0 := by
    change (Route.line ⟨(fixedEdge.val : ℝ) + 1, 1⟩ 0).support = _
    rw [Route.support_line]
    norm_num [fixedEdge]
  obtain ⟨E, hE, hv, hout, he⟩ :=
    (PolygonalDrawing.star_isEmbedding 2).exists_square_move
      (starGraph_endpoints_declared 2) 0 ⟨9 / 8, 1⟩ (by norm_num) hmove
  refine ⟨E, hE, hv, (hout 2 ?_).trans hcenter, he fixedEdge ?_⟩
  · change (1 / 4 : ℝ) ≤
      max |(D.vertex 2).re - (D.vertex 0).re| |(D.vertex 2).im - (D.vertex 0).im|
    rw [hcenter, hleaf]
    norm_num
  · change ∀ z ∈ (D.route fixedEdge).support, (1 / 4 : ℝ) ≤
      max |z.re - (D.vertex 0).re| |z.im - (D.vertex 0).im|
    rw [hroute, hleaf, segment_eq_image_lineMap]
    rintro z ⟨t, _, rfl⟩
    let q := AffineMap.lineMap (⟨2, 1⟩ : ℂ) 0 t
    change (1 / 4 : ℝ) ≤ max |q.re - 1| |q.im - 1|
    have hq : q.re = 2 * q.im := by
      dsimp only [q]
      rw [AffineMap.lineMap_apply_module, smul_zero, add_zero]
      simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, mul_one]
      ring
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hx := abs_lt.mp ((le_max_left _ _).trans_lt hlt)
    have hy := abs_lt.mp ((le_max_right _ _).trans_lt hlt)
    linarith [hx.2, hy.1]

end CslibFrontierTests.PolygonalSquareMove

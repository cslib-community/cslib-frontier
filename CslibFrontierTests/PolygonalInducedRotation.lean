/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary module regression tests)

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Equivalence
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Points
import CslibFrontier.Foundations.Geometry.Polygonal.NoncrossingOrder
import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds

/-! Ordinary module clients read the rotation from actual geometry, without a supplied
realization. They check a degree-thirteen star's literal clockwise triple and reject its
reflection, and include empty graphs and sparse duplicate isolated declarations. -/

public section

namespace CslibFrontierTests.PolygonalInducedRotation

open Cslib Cslib.Complexity Cslib.Complexity.Graph Cslib.Polygonal RotationSystem

/-- Center-end darts of the degree-thirteen regression star. -/
abbrev port (i : Fin 13) : Dart (starGraph 13) := starDartEquiv 13 (i, true)

private theorem star_clockwise :
    sbtw ((PolygonalDrawing.star 13).direction (port 2))
      ((PolygonalDrawing.star 13).direction (port 1))
      ((PolygonalDrawing.star 13).direction (port 0)) := by
  have hdir (i : Fin 13) : (PolygonalDrawing.star 13).direction (port i) =
      ((⟨(i.val : ℝ) + 1, 1⟩ : ℂ).arg : Real.Angle) := by
    change (((Route.line ⟨(i.val : ℝ) + 1, 1⟩ 0).germ true).arg : Real.Angle) = _
    simp only [Route.germ_line, ↓reduceIte, sub_zero]
  rw [hdir, hdir, hdir]
  convert clockwise_ports (a := 1) (b := 2) (c := 3)
    (by norm_num) (by norm_num) (by norm_num) using 1 <;>
    norm_num

-- The interval is derived from the drawing's rays, rather than a supplied star rotation.
example : port 1 ∈ (PolygonalDrawing.star_isEmbedding 13).rotation.rotationInterval
    (port 0) (port 2) := by
  exact ((PolygonalDrawing.star_isEmbedding 13).realizes_rotation.clockwise
    (port 0) (port 1) (port 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).mp star_clockwise

example : ¬sbtw ((PolygonalDrawing.star 13).direction (port 0))
    ((PolygonalDrawing.star 13).direction (port 1))
    ((PolygonalDrawing.star 13).direction (port 2)) := star_clockwise.not_sbtw

-- A genuine drawing alone now suffices for the numerical existence conclusion.
example : ∃ r : RotationSystem (starGraph 13), r.NumericalGenusZero :=
  (exists_numericalGenusZero_iff_exists_polygonalDrawing
    (starGraph_endpoints_declared 13)).mpr
      ⟨PolygonalDrawing.star 13, PolygonalDrawing.star_isEmbedding 13⟩

example : ∃ r : RotationSystem ⟨[], []⟩, r.NumericalGenusZero :=
  (exists_numericalGenusZero_iff_exists_polygonalDrawing (by decide)).mpr
    ⟨PolygonalDrawing.points [], PolygonalDrawing.points_isEmbedding []⟩

example : ∃ r : RotationSystem ⟨[7, 2 ^ 250, 7], []⟩, r.NumericalGenusZero :=
  (exists_numericalGenusZero_iff_exists_polygonalDrawing (by decide)).mpr
    ⟨PolygonalDrawing.points [7, 2 ^ 250, 7],
      PolygonalDrawing.points_isEmbedding [7, 2 ^ 250, 7]⟩

end CslibFrontierTests.PolygonalInducedRotation

/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Converse
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Rotation

/-!
# Numerical genus zero is equivalent to polygonal realization

For a supplied rotation on a listed finite multigraph with declared incident endpoints,
the existing componentwise numerical genus-zero predicate is equivalent to an actual
polygonal embedding realizing its literal clockwise order. Coordinates are arbitrary
complex numbers and contacts quantify over all real segment parameters. Loops, indexed
parallel occurrences, arbitrary degree, disconnected components, repeated declarations,
isolates and empty graphs are included.

Without a supplied rotation, existence is also equivalent: every polygonal embedding supplies
its own literal clockwise rotation from its outgoing geometric rays.

This finite PL equivalence does not prove topological taming, a source-model comparison,
Hanani–Tutte, recognition, coordinate-bit or runtime bounds, or a planar CSP dichotomy.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.numericalGenusZero_iff_exists_polygonalDrawing`.
* `Cslib.Complexity.Graph.RotationSystem.exists_numericalGenusZero_iff_exists_polygonalDrawing`.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

/-- A supplied rotation has componentwise numerical genus zero exactly when an actual
polygonal embedding realizes its literal clockwise order. -/
theorem numericalGenusZero_iff_exists_polygonalDrawing {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    r.NumericalGenusZero ↔ ∃ D : PolygonalDrawing G, D.IsEmbedding ∧ D.Realizes r := by
  constructor
  · exact r.exists_polygonalDrawing hG
  · rintro ⟨D, hD, hR⟩
    exact hD.numericalGenusZero hG hR

/-- A listed graph admits a numerical genus-zero rotation exactly when it has a genuine
finite polygonal embedding. The rotation in the reverse implication is read from the drawing
itself, rather than supplied with it. -/
theorem exists_numericalGenusZero_iff_exists_polygonalDrawing {G : Graph}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    (∃ r : RotationSystem G, r.NumericalGenusZero) ↔
      ∃ D : PolygonalDrawing G, D.IsEmbedding := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨D, hD, -⟩ := r.exists_polygonalDrawing hG hr
    exact ⟨D, hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨hD.rotation, hD.numericalGenusZero hG hD.realizes_rotation⟩

end Cslib.Complexity.Graph.RotationSystem

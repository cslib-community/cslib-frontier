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

The same realization theorem embeds a regular drawing with simple routes and even
crossings between every distinct pair of edges, preserving the rotation read from
its outgoing directions. The independently-even case, topological taming and source-model
comparison remain separate.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.numericalGenusZero_iff_exists_polygonalDrawing`.
* `Cslib.Complexity.Graph.RotationSystem.exists_numericalGenusZero_iff_exists_polygonalDrawing`.
* `HasRegularContacts.exists_embedding_of_pairwise_even_crossings`.
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

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- A regular drawing with simple routes and even crossings between all distinct edge
pairs has an embedding realizing its actual clockwise rotation. This is the all-pairs-even
case for finite polygonal drawings with regular contacts. -/
theorem HasRegularContacts.exists_embedding_of_pairwise_even_crossings
    {G : Graph} {D : PolygonalDrawing G} (hD : D.HasRegularContacts)
    (hsimple : ∀ e, (D.route e).IsSimple)
    (heven : ∀ e f, e ≠ f → (D.route e).intersectionParity (D.route f) = false)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) :
    ∃ r : RotationSystem G, D.Realizes r ∧ ∃ E : PolygonalDrawing G,
      E.IsEmbedding ∧ E.Realizes r := by
  let hdir := hD.directions_injective hsimple
  have hr := D.realizes_rotationOfDirections
    (fun d => (hsimple d.1).germ_ne_zero d.2) hdir
  exact ⟨D.rotationOfDirections hdir, hr, (D.rotationOfDirections hdir).exists_polygonalDrawing hG
    (hD.numericalGenusZero_of_pairwise_even_crossings hsimple heven hr hG)⟩

end Cslib.Complexity.Graph.PolygonalDrawing

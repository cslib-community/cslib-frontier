/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.FaceColors
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpaceConverse

/-!
# A polygonal realization has numerical genus zero

For an arbitrary listed finite multigraph with declared incident endpoints, an actual
polygonal embedding that literally realizes a clockwise rotation has componentwise
numerical genus zero. The proof constructs colors on the actual face quotient from every
vertex-even indexed edge label and applies the cycle-space converse.

Coordinates are arbitrary complex numbers and segment parameters range over all real
numbers in `[0,1]`. Loops retain their two ends, parallel edges retain their list indices,
and sparse or duplicate declarations, isolates, disconnected graphs and the empty graph
are permitted. There is no degree bound or supplied topological, face-color or genus oracle.

The original finite PL proof also applies to a regular drawing with simple routes and
even crossings between every distinct pair of edges. This gives the all-pairs-even
case, with the literal clockwise rotation preserved. The listed points in a regular
drawing are injective along each route, so this case covers loopless multigraphs.
A topological-source comparison,
taming of arbitrary topological arcs, the independently-even case, recognition and
the planar CSP dichotomy remain open.

## Main results

* `Cslib.Complexity.Graph.PolygonalDrawing.IsEmbedding.numericalGenusZero`.
* `HasRegularContacts.numericalGenusZero_of_pairwise_even_crossings`.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- A genuine finite polygonal embedding with exact literal clockwise realization has
numerical genus zero on every component, including isolated declared vertices. -/
theorem IsEmbedding.numericalGenusZero {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {r : RotationSystem G}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hR : D.Realizes r) :
    r.NumericalGenusZero :=
  r.numericalGenusZero_of_vertexEven_faceBoundary hG
    (fun x hx => hD.exists_faceColors hR hG x hx)

/-- The literal clockwise rotation of a regular polygonal drawing with simple
routes and even crossings between all distinct edge pairs has numerical genus zero.
This is the all-pairs-even case under the regular polygonal drawing hypotheses. -/
theorem HasRegularContacts.numericalGenusZero_of_pairwise_even_crossings
    {G : Graph} {D : PolygonalDrawing G}
    (hD : D.HasRegularContacts) (hsimple : ∀ e, (D.route e).IsSimple)
    (heven : ∀ e f, e ≠ f → (D.route e).intersectionParity (D.route f) = false)
    {r : RotationSystem G} (hR : D.Realizes r)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices) :
    r.NumericalGenusZero :=
  r.numericalGenusZero_of_vertexEven_faceBoundary hG
    (fun x hx => hD.exists_faceColors_of_pairwise_even_crossings hsimple heven hR hG x hx)

end Cslib.Complexity.Graph.PolygonalDrawing

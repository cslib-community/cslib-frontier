/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Polygonal

/-!
A genuine one-edge integer drawing supplies the polygonal embedding contract, including
full real segment contacts. The route is supplied in the opposite orientation to its edge,
so this also checks that shared normalization retains the actual graph endpoints.
-/

open Cslib.Complexity Cslib.Complexity.Graph Cslib.Orthogonal

public section

namespace CslibFrontierTests.OrthogonalPolygonal

/-- One indexed edge with sparse original endpoint labels. -/
def oneEdge : Graph := ⟨[7, 23], [(7, 23)]⟩

private def edge : Fin oneEdge.edges.length := ⟨0, by simp [oneEdge]⟩

private def reversedDrawing : OrthogonalDrawing :=
  ([(0, 0), (2, 0)], [[(2, 0), (0, 0)]])

private theorem validDrawing : IsPlanarOrthogonalDrawing oneEdge reversedDrawing where
  vertexCount := rfl
  edgeCount := rfl
  labelsNodup := by decide
  positionsNodup := by decide
  endpointsDeclared := by simp [oneEdge]
  loopless := by simp [oneEdge]
  endpoints i hi := by
    have hi0 : i = 0 := by simpa [oneEdge] using hi
    subst i
    exact .inr ⟨rfl, rfl⟩
  orthogonal i hi := by
    have hi0 : i = 0 := by simpa [oneEdge] using hi
    subst i
    simp [reversedDrawing, IsOrthogonal, List.consecutivePairs, AxisAligned]
  simple i hi := by
    have hi0 : i = 0 := by simpa [oneEdge] using hi
    subst i
    simp [reversedDrawing, IsSimple, List.consecutivePairs]
  avoidsVertices i hi v hv _ := by
    have hi0 : i = 0 := by simpa [oneEdge] using hi
    subst i
    simpa [oneEdge] using hv
  contacts i hi j hj hij := by
    have hi0 : i = 0 := by simpa [oneEdge] using hi
    have hj0 : j = 0 := by simpa [oneEdge] using hj
    exact False.elim (hij (hi0.trans hj0.symm))

example : validDrawing.polygonalDrawing.IsEmbedding :=
  validDrawing.isEmbedding_polygonalDrawing

example : (validDrawing.polygonalDrawing.route edge).bends = 0 := rfl

example : (validDrawing.polygonalDrawing.route edge).endpoint false =
    validDrawing.polygonalDrawing.vertex 7 :=
  validDrawing.polygonalDrawing.endpoint_eq edge false

example : validDrawing.polygonalDrawing.vertex 7 ≠ validDrawing.polygonalDrawing.vertex 23 :=
  validDrawing.isEmbedding_polygonalDrawing.vertex_ne (by decide) (by decide) (by decide)

end CslibFrontierTests.OrthogonalPolygonal

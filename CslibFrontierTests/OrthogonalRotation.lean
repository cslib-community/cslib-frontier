/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.PolyTime.Graph.OrthogonalRotation

/-!
The four rays at a star center must follow east, south, west, north. Mixed input route
orientations retain that same literal order. A malformed route table exercises total
computation and rejection separately from the geometric correctness theorem.
-/

open Cslib.Complexity Cslib.Complexity.Graph

public section

namespace CslibFrontierTests.OrthogonalRotation

/-- A center joined to four separately indexed cardinal leaves. -/
def fourRayGraph : Graph :=
  ⟨[0, 1, 2, 3, 4], [(0, 1), (0, 2), (0, 3), (0, 4)]⟩

private def fourRayDrawing : OrthogonalDrawing :=
  ([(0, 0), (2, 0), (0, -2), (-2, 0), (0, 2)],
    [[(0, 0), (2, 0)], [(0, -2), (0, 0)], [(-2, 0), (0, 0)], [(0, 0), (0, 2)]])

example : (OrthogonalDrawing.rotationCertificate fourRayGraph fourRayDrawing).successor =
    [2, 1, 4, 3, 6, 5, 0, 7] := by decide

example : RotationCertificate.verifyGenusZero fourRayGraph
    (OrthogonalDrawing.rotationCertificate fourRayGraph fourRayDrawing) = true := by decide

example : (OrthogonalDrawing.rotationCertificate fourRayGraph ([], [])).successor =
    [0, 1, 0, 3, 0, 5, 0, 7] := by decide

example : RotationCertificate.verifyRotation fourRayGraph
    (OrthogonalDrawing.rotationCertificate fourRayGraph ([], [])) = false := by decide

example : (OrthogonalDrawing.rotationCertificate (⟨[], []⟩ : Graph) ([], [])).successor = [] :=
  by decide

example (G : Graph) (d : OrthogonalDrawing) (i : ℕ) (hi : i < 2 * G.edges.length) :
    OrthogonalDrawing.clockwiseSuccessor G d i < 2 * G.edges.length :=
  (OrthogonalDrawing.clockwiseSuccessor_spec G d hi).1

end CslibFrontierTests.OrthogonalRotation

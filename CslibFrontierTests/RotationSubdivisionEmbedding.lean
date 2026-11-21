/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (ordinary clients of the subdivision embedding)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SubdivisionEmbedding
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Bouquet

/-! # Actual subdivision embeddings of a star and a loop -/

public section

namespace CslibFrontierTests.RotationSubdivisionEmbedding

open Cslib.Complexity Graph RotationRecognition RotationSystem

/-- The original star has one-segment routes, so both cuts are on the same segment. -/
theorem star_subdivision :
    ∃ E : PolygonalDrawing (subdivisionGraph ⟨starGraph 2, [none, none, none]⟩),
      E.IsEmbedding ∧ E.vertex 2 = (PolygonalDrawing.star 2).vertex 2 ∧
        ∀ d, E.direction
          (subdivisionDart ⟨starGraph 2, [none, none, none]⟩ d) =
            (PolygonalDrawing.star 2).direction d := by
  let I : FixedRotationInput := ⟨starGraph 2, [none, none, none]⟩
  have hI : Valid I := (validate_eq_true_iff I).mp (by decide)
  obtain ⟨E, hE, hV, hdir⟩ :=
    exists_subdivision_embedding hI (PolygonalDrawing.star 2) (PolygonalDrawing.star_isEmbedding 2)
  exact ⟨E, hE, hV 2 (by decide), hdir⟩

private def threeSpokeStar : FixedRotationInput := ⟨starGraph 3, [none, none, none, none]⟩

-- Every subdivision dart at the center reads the direction of its original spoke.
example :
    ∃ E : PolygonalDrawing (subdivisionGraph threeSpokeStar), E.IsEmbedding ∧
      ∀ d : {d : Dart (subdivisionGraph threeSpokeStar) // d.vertex = 3},
        E.direction d.val =
          (PolygonalDrawing.star 3).direction
            ((subdivisionDartEquiv threeSpokeStar 3 (by decide)).symm d).val := by
  have hI : Valid threeSpokeStar := (validate_eq_true_iff _).mp (by decide)
  obtain ⟨E, hE, _, hdir⟩ :=
    exists_subdivision_embedding hI (PolygonalDrawing.star 3) (PolygonalDrawing.star_isEmbedding 3)
  refine ⟨E, hE, fun d => ?_⟩
  let f := subdivisionDartEquiv threeSpokeStar 3 (by decide)
  have h := subdivisionDart_subdivisionDartEquiv_symm threeSpokeStar 3 (by decide) d
  exact (congrArg E.direction h.symm).trans (hdir (f.symm d).val)

private def loop : FixedRotationInput := ⟨⟨[0], [(0, 0)]⟩, [none]⟩

private def loopEdge : Fin loop.graph.edges.length := ⟨0, by decide⟩

-- The two cuts on an actual closed route are different declared vertices.
example : ∃ (D : PolygonalDrawing loop.graph) (E : PolygonalDrawing (subdivisionGraph loop)),
    D.IsEmbedding ∧ E.IsEmbedding ∧ E.vertex 1 ≠ E.vertex 2 ∧
      ∀ b, E.direction (subdivisionDart loop (loopEdge, b)) = D.direction (loopEdge, b) := by
  have hI : Valid loop := (validate_eq_true_iff loop).mp (by decide)
  let c : RotationCertificate := ⟨[1, 0]⟩
  let r := RotationCertificate.decode loop.graph c (by decide)
  have hg : r.NumericalGenusZero :=
    (RotationCertificate.verifyEuler_eq_true_iff (G := loop.graph) (c := c)
      (by decide)).mp (by decide)
  let D := PolygonalDrawing.bouquet r (by decide)
  have hD : D.IsEmbedding := PolygonalDrawing.bouquet_isEmbedding r (by decide) hg (by decide)
  obtain ⟨E, hE, _, hdir⟩ := exists_subdivision_embedding hI D hD
  have hloop (b : Bool) :
      E.direction (subdivisionDart loop (loopEdge, b)) = D.direction (loopEdge, b) :=
    hdir (loopEdge, b)
  exact ⟨D, E, hD, hE, hE.vertex_ne (by decide) (by decide) (by decide), hloop⟩

end CslibFrontierTests.RotationSubdivisionEmbedding

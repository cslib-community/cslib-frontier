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

-- A positive small radius controls whole end pieces, including at the three-spoke center.
example :
    ∃ E : PolygonalDrawing (subdivisionGraph threeSpokeStar), E.IsEmbedding ∧
      ∀ d : Dart threeSpokeStar.graph,
        (E.route (subdivisionDart threeSpokeStar d).1).support ⊆
          Metric.ball ((PolygonalDrawing.star 3).vertex d.vertex) (1 / 100) := by
  have hI : Valid threeSpokeStar := (validate_eq_true_iff _).mp (by decide)
  obtain ⟨E, hE, _, _, hball⟩ :=
    exists_subdivision_embedding_in_balls hI (PolygonalDrawing.star 3)
      (PolygonalDrawing.star_isEmbedding 3) (ρ := 1 / 100) (by norm_num)
  exact ⟨E, hE, hball⟩

-- The selected leaf of every original dart is on the same prescribed radius.
example :
    ∃ (ρ : ℝ) (E : PolygonalDrawing (subdivisionGraph threeSpokeStar)),
      0 < ρ ∧ E.IsEmbedding ∧ ∀ d : Dart threeSpokeStar.graph,
        dist (E.vertex (subdivisionDart threeSpokeStar d).reverse.vertex)
          ((PolygonalDrawing.star 3).vertex d.vertex) = ρ := by
  have hI : Valid threeSpokeStar := (validate_eq_true_iff _).mp (by decide)
  have hD := PolygonalDrawing.star_isEmbedding 3
  obtain ⟨ε, hε, h⟩ := exists_subdivision_embedding_at_cutPorts hI (PolygonalDrawing.star 3) hD
  have hρ : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨half_pos hε, half_lt_self hε⟩
  obtain ⟨E, hE, _, _, hports, _⟩ := h (ε / 2) hρ
  refine ⟨ε / 2, E, hρ.1, hE, fun d => ?_⟩
  rw [hports]
  exact hD.dist_cutPort hρ.1.le d

-- The first spoke's middle piece avoids the disk of the second leaf.
private def firstMiddle : Fin (subdivisionGraph threeSpokeStar).edges.length := ⟨1, by decide⟩

example :
    ∃ (ρ : ℝ) (E : PolygonalDrawing (subdivisionGraph threeSpokeStar)),
      0 < ρ ∧ E.IsEmbedding ∧
        Disjoint (Metric.closedBall ((PolygonalDrawing.star 3).vertex 0) ρ)
          (Metric.closedBall ((PolygonalDrawing.star 3).vertex 3) ρ) ∧
        Disjoint (E.route firstMiddle).support
          (Metric.closedBall ((PolygonalDrawing.star 3).vertex 1) ρ) := by
  have hI : Valid threeSpokeStar := (validate_eq_true_iff _).mp (by decide)
  have hD := PolygonalDrawing.star_isEmbedding 3
  obtain ⟨ε, hε, h⟩ :=
    exists_subdivision_embedding_in_disjoint_disks hI (PolygonalDrawing.star 3) hD
  have hρ : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨half_pos hε, half_lt_self hε⟩
  obtain ⟨hdisj, E, hE, _, _, _, _, hmiddle⟩ := h (ε / 2) hρ
  let a := subdivisionEdgeIndex threeSpokeStar firstMiddle
  have hindex : 1 = 3 * a.original.val + a.piece.val :=
    subdivisionEdgeIndex_val threeSpokeStar firstMiddle
  have he : a.piece = 1 := Fin.ext (by change a.piece.val = 1; omega)
  have hzero : a.original.val = 0 := by omega
  refine ⟨ε / 2, E, hρ.1, hE, hdisj 0 (by decide) 3 (by decide) (by decide),
    Set.disjoint_left.mpr fun z hz hball => ?_⟩
  obtain ⟨b, hb, _⟩ := hmiddle firstMiddle he 1 (by decide) z hz hball
  change Dart.vertex (a.original, b) = 1 at hb
  have hidx : a.original = (⟨0, by decide⟩ : Fin threeSpokeStar.graph.edges.length) :=
    Fin.ext hzero
  rw [hidx] at hb
  cases b <;> revert hb <;> decide

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

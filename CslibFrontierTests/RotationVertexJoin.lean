/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeEndJoin
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexJoinGenus

/-! Different-component vertex joins retain parallel occurrences, a closed loop and points. -/

namespace CslibFrontierTests.RotationVertexJoin

open Cslib.Complexity Graph.RotationSystem

private abbrev G : Graph :=
  ⟨[0, 1, 2, 3, 4, 5, 6, 6], [(0, 1), (0, 1), (2, 3), (2, 3), (4, 4)]⟩

private abbrev c : Graph.RotationCertificate := ⟨[2, 3, 0, 1, 6, 7, 4, 5, 9, 8]⟩

private noncomputable def r : Graph.RotationSystem G :=
  Graph.RotationCertificate.decode G c (by decide)

private theorem genus : r.NumericalGenusZero :=
  (Graph.RotationCertificate.verifyEuler_eq_true_iff (by decide :
    Graph.RotationCertificate.verifyRotation G c = true)).mp (by decide)

private abbrev h : Graph.Dart G := (0, false)
private abbrev k : Graph.Dart G := (2, false)

-- The source has two genuinely nontrivial, distinct components, plus a loop and two points.
private theorem different : ¬ Graph.RotationCertificate.SameComponent G h.vertex k.vertex := by
  rw [← Graph.RotationCertificate.componentBool_eq_true_iff (by decide)]
  decide

example : (r.mergeVertices h k (by decide)).NumericalGenusZero :=
  numericalGenusZero_mergeVertices_of_not_sameComponent r (by decide) genus h k
    (by decide) different

-- The exact successor list is the source list with precisely the two outgoing entries swapped.
example : Graph.RotationCertificate.ofRotation (r.mergeVertices h k (by decide)) =
    ⟨[6, 3, 0, 1, 2, 7, 4, 5, 9, 8]⟩ := by decide +kernel

example : Graph.RotationCertificate.verifyGenusZero (mergeGraph h k)
    ⟨[6, 3, 0, 1, 2, 7, 4, 5, 9, 8]⟩ = true := by decide

example : (mergeGraph h k).2 = [(0, 1), (0, 1), (0, 3), (0, 3), (4, 4)] := rfl

example : (mergeGraph h k).1 = [0, 1, 0, 3, 4, 5, 6, 6] := rfl

-- Both parallel-edge components are joined, while the loop remains separate.
example : Graph.RotationCertificate.SameComponent (mergeGraph h k)
    (mergeDartEquiv h k (1, true)).vertex (mergeDartEquiv h k (3, true)).vertex := by
  rw [← Graph.RotationCertificate.componentBool_eq_true_iff (by decide)]
  decide

example : ¬ Graph.RotationCertificate.SameComponent (mergeGraph h k)
    (mergeDartEquiv h k h).vertex (mergeDartEquiv h k (4, false)).vertex := by
  rw [← Graph.RotationCertificate.componentBool_eq_true_iff (by decide)]
  decide

example : 5 ∉ (mergeGraph h k).incidenceVertices := by decide

-- Different components are essential: opposite corners of this planar dipole share no face.
private abbrev dipole : Graph := ⟨[0, 1], [(0, 1), (0, 1), (0, 1)]⟩
private abbrev dipoleTable : Graph.RotationCertificate := ⟨[2, 5, 4, 1, 0, 3]⟩
private noncomputable def dipoleRotation : Graph.RotationSystem dipole :=
  Graph.RotationCertificate.decode dipole dipoleTable (by decide)

example : Graph.RotationCertificate.verifyGenusZero dipole dipoleTable = true := by decide

example : Graph.RotationCertificate.verifyGenusZero
    (mergeGraph (G := dipole) (0, false) (0, true))
    (Graph.RotationCertificate.ofRotation
      (dipoleRotation.mergeVertices (0, false) (0, true) (by decide))) = false := by
  decide +kernel

private theorem faceFromTable (d e : Graph.Dart G)
    (he : (Graph.RotationCertificate.faceTable G c).getD d.index 0 = e.index) :
    r.faceNext d = e := by
  apply (Graph.Dart.indexEquiv G).injective
  apply Fin.ext
  exact (Graph.RotationCertificate.getD_faceTable (by decide) d).symm.trans he

-- Joining both ends retains four distinct parallel edges and the unrelated loop.
example :
    let a := r.faceNext h.reverse
    let b := r.faceNext k.reverse
    let e := mergeDartEquiv a b
    let h' := e h.reverse
    let k' := e k.reverse
    ∃ (hne : a.vertex ≠ b.vertex) (hne' : h'.vertex ≠ k'.vertex),
      ((r.mergeVertices a b hne).mergeVertices h' k' hne').NumericalGenusZero ∧
        (mergeGraph h' k').edges = [(0, 1), (0, 1), (0, 1), (0, 1), (4, 4)] := by
  obtain ⟨hne, hne', hz, _, _, _⟩ :=
    r.numericalGenusZero_mergeEdgeEnds (by decide) genus h k (by decide) (by decide) different
  refine ⟨hne, hne', hz, ?_⟩
  rw [faceFromTable h.reverse (1, false) (by decide),
    faceFromTable k.reverse (3, false) (by decide)]
  decide +kernel

-- The joined digons have opposite orders of their two payload darts around the retained marker.
example : ∃ (H : Graph) (s : Graph.RotationSystem H) (lift : Graph.Dart H ↪ Graph.Dart G),
    s.NumericalGenusZero ∧ H.edges = [(0, 1), (0, 1), (0, 1), (4, 4)] ∧
      (∃ x y, lift x = (1, false) ∧ lift y = (3, false) ∧ s.rotate x = y) ∧
      (∃ x y, lift x = (3, true) ∧ lift y = (1, true) ∧ s.rotate x = y) := by
  obtain ⟨H, s, lift, _, hedges, hz, _, hrange, hrotate⟩ :=
    r.exists_numericalGenusZero_glueMarkerEdges (by decide) genus h k
      (by decide) (by decide) different
  let f := r.rotate * Equiv.swap (r.faceNext h.reverse) (r.faceNext k.reverse) *
    Equiv.swap h.reverse k.reverse
  have splice (x y : Graph.Dart G) (hx : x.1 ≠ k.1) (hy : y.1 ≠ k.1)
      (tag : Bool) (h₁ : f x = (k.1, tag)) (h₂ : f (k.1, tag) = y) :
      ∃ X Y, lift X = x ∧ lift Y = y ∧ s.rotate X = Y := by
    obtain ⟨X, hX⟩ := (hrange x).mpr hx
    obtain ⟨Y, hY⟩ := (hrange y).mpr hy
    refine ⟨X, Y, hX, hY, (hrotate X Y).mpr (Or.inr ⟨tag, ?_, ?_⟩)⟩
    · rw [hX]
      exact h₁
    · rw [hY]
      exact h₂
  have ha : r.faceNext h.reverse = (1, false) := faceFromTable _ _ (by decide)
  have hb : r.faceNext k.reverse = (3, false) := faceFromTable _ _ (by decide)
  refine ⟨H, s, lift, hz, hedges.trans (by decide +kernel),
    splice (1, false) (3, false) (by decide) (by decide) false ?_ ?_,
    splice (3, true) (1, true) (by decide) (by decide) true ?_ ?_⟩
  all_goals
    dsimp only [f]
    rw [ha, hb]
    decide +kernel

end CslibFrontierTests.RotationVertexJoin

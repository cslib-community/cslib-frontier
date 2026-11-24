/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (rotation component restriction regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.ComponentEuler
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Equality

set_option linter.privateModule false

/-! Restrict a disconnected graph to the component containing two parallel occurrences. -/

namespace CslibFrontierTests.RotationComponentRestriction

open Cslib.Complexity Cslib.Complexity.Graph RotationCertificate

private abbrev G : Graph := ⟨[0, 1, 2, 3], [(0, 1), (0, 1), (2, 3)]⟩
private theorem hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices := by decide

private def certificate : RotationCertificate := ⟨[2, 3, 0, 1, 4, 5]⟩
private theorem certificate_ok : verifyRotation G certificate = true := by decide

private def r : RotationSystem G where
  rotate := Equiv.swap (0, false) (1, false) * Equiv.swap (0, true) (1, true)
  sameCycle_iff := by decide

private theorem other_component : ¬SameComponent G 0 2 := by
  intro h
  let mark (d : Dart G) : Bool := decide (d.vertex ≤ 1)
  have he := Dart.eq_of_sameComponent mark (fun a b h => by simp only [mark, h])
    (by decide +revert) (d := (0, false)) (e := (2, false)) h
  exact Bool.noConfusion he

-- The retained parallel occurrences keep their rotation, reversal and face traversal.
example : (∀ v ∈ (G.componentGraph 0).incidenceVertices, v ∈ (G.componentGraph 0).vertices) ∧
    (∀ i : Fin (G.componentGraph 0).edges.length, (G.componentEdgeEquiv 0 i).val ≠ 2) ∧
    ∃ d : Dart (G.componentGraph 0), d.vertex = 0 ∧
      (G.componentDartEquiv 0 hG d).val = (0, false) ∧
      let s := r.component 0 hG
      (G.componentDartEquiv 0 hG (s.rotate d)).val = (1, false) ∧
      (G.componentDartEquiv 0 hG d.reverse).val = (0, true) ∧
      (G.componentDartEquiv 0 hG (s.faceNext d)).val = (1, true) := by
  refine ⟨G.componentGraph_endpoints_declared 0 hG, ?_, ?_⟩
  · intro i he
    have hi : (2 : Fin G.edges.length) ∈ G.componentEdgeSet 0 :=
      he ▸ (G.componentEdgeEquiv 0 i).property
    apply other_component
    exact (G.mem_componentVertexSet_dart 0 hG (2, false)).mp
      ((G.mem_componentEdgeSet_iff 0 hG 2 false).mp hi)
  · let a : {d : Dart G // SameComponent G 0 d.vertex} :=
      ⟨(0, false), .refl (by decide)⟩
    let e := G.componentDartEquiv 0 hG
    let d := e.symm a
    have he : (e d).val = (0, false) := congrArg Subtype.val (e.apply_symm_apply a)
    refine ⟨d, ?_, he, ?_, ?_, ?_⟩
    · exact (G.vertex_componentDartEquiv 0 hG d).symm.trans (congrArg Dart.vertex he)
    · change (e ((r.component 0 hG).rotate d)).val = (1, false)
      rw [r.componentDartEquiv_rotate, he]
      decide
    · change (e d.reverse).val = (0, true)
      rw [G.componentDartEquiv_reverse, he]
      rfl
    · change (e ((r.component 0 hG).faceNext d)).val = (1, true)
      rw [r.componentDartEquiv_faceNext, he]
      decide

-- The two sides of the parallel-edge cycle give distinct faces in the restricted graph.
example : ∃ p q : (r.component 0 hG).Face, p ≠ q := by
  let e := r.componentFaceEquiv 0 hG
  let p : r.ComponentFace 0 :=
    ⟨Quotient.mk _ (0, false), (0, false), .refl (by decide), rfl⟩
  let q : r.ComponentFace 0 :=
    ⟨Quotient.mk _ (1, false), (1, false), .refl (by decide), rfl⟩
  refine ⟨e.symm p, e.symm q, e.symm.injective.ne ?_⟩
  intro h
  have hcyc : r.faceNext.SameCycle (0, false) (1, false) :=
    Quotient.exact (congrArg Subtype.val h)
  exact (by decide : ¬r.faceNext.SameCycle (0, false) (1, false)) hcyc

-- Assembling genus-zero choices keeps the nontrivial marked successor of the first parallel dart.
example : ∃ s : RotationSystem G, s.NumericalGenusZero ∧ s.rotate (0, false) = (1, false) := by
  have he : decode G certificate certificate_ok = r := by
    apply RotationSystem.ext_rotate
    apply Equiv.ext
    intro d
    apply (Dart.indexEquiv G).injective
    apply Fin.ext
    change ((decode G certificate certificate_ok).rotate d).index = (r.rotate d).index
    rw [index_decode_rotate certificate_ok]
    exact (by decide : ∀ a : Dart G, certificate.successor.getD a.index 0 = (r.rotate a).index) d
  have hr : r.NumericalGenusZero := he ▸ (verifyEuler_eq_true_iff certificate_ok).mp (by decide)
  obtain ⟨s, hz, hmarked⟩ := r.exists_numericalGenusZero_agreeing_on_of_components hG (· = 0)
    (fun root _ => ⟨r.component root hG, r.numericalGenusZero_component hG hr root,
      fun _ _ => rfl⟩)
  exact ⟨s, hz, (hmarked (0, false) rfl).trans (by decide)⟩

end CslibFrontierTests.RotationComponentRestriction

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (cut-vertex gluing regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CutIntervalGenus

set_option linter.privateModule false

/-! A two-edge star splits into two components and recovers its original genus equation. -/

namespace CslibFrontierTests.RotationCutIntervalGenus

open Cslib.Complexity Cslib.Complexity.Graph RotationCertificate

private abbrev G : Graph := ⟨[0, 1, 2], [(0, 1), (0, 2)]⟩
private abbrev H : Graph := ⟨[3, 0, 1, 2], [(3, 1), (0, 2)]⟩
private abbrev a : Dart G := (0, false)
private abbrev b : Dart G := (1, false)

private def original : RotationSystem G where
  rotate := Equiv.swap a b
  sameCycle_iff := by decide

private abbrev E : Fin G.edges.length ≃ Fin H.edges.length := Equiv.refl _
private abbrev table : RotationCertificate := ⟨[0, 1, 2, 3]⟩
private theorem table_ok : verifyRotation H table = true := by decide

private theorem no_loop_at_center :
    ∀ d : Dart G, d.vertex = a.vertex → d.reverse.vertex ≠ a.vertex := by decide

private theorem deleted_eq_bot : (G.toSimpleGraph.induce {u | u ≠ a.vertex}) = ⊥ := by
  ext u v
  have hu : u.val ≠ 0 := u.property
  have hv : v.val ≠ 0 := v.property
  change G.toSimpleGraph.Adj u.val v.val ↔ False
  simp [Graph.toSimpleGraph_adj, hu, hv]

-- The checked identity certificate on the two split edges supplies the genus-zero premise.
example : ¬SameComponent H 3 0 ∧ original.NumericalGenusZero := by
  let s := decode H table table_ok
  have hz : s.NumericalGenusZero := (verifyEuler_eq_true_iff table_ok).mp (by decide)
  have hrank {d : Dart G} (hd : d.vertex = a.vertex) (hne : d ≠ a) :
      ¬original.rotationDistance a d ≤ original.rotationDistance a a := by
    rw [original.rotationDistance_self]
    exact not_le_of_gt (original.rotationDistance_pos_of_ne a d hd.symm hne)
  have hclass (d : Dart G) (hd : d.vertex = a.vertex) :
      (G.toSimpleGraph.induce {u | u ≠ a.vertex}).Reachable
        ⟨a.reverse.vertex, no_loop_at_center a rfl⟩ ⟨d.reverse.vertex, no_loop_at_center d hd⟩ ↔
        original.rotationDistance a d ≤ original.rotationDistance a a := by
    rw [deleted_eq_bot, SimpleGraph.reachable_bot]
    by_cases he : d = a
    · subst d
      simp
    have hd' := (show ∀ z : Dart G, z.vertex = a.vertex → z ≠ a → z = b by decide) d hd he
    subst d
    exact iff_of_false (fun h => (by decide : a.reverse.vertex ≠ b.reverse.vertex)
      (congrArg Subtype.val h)) (hrank hd he)
  have hEnds (d : Dart G) : Dart.vertex (G := H) (E d.1, d.2) =
      if d.vertex = a.vertex ∧ original.rotationDistance a d ≤ original.rotationDistance a a
      then 3 else d.vertex := by
    by_cases he : d = a
    · subst d
      rw [ite_eq_left ⟨rfl, le_rfl⟩]
      rfl
    rw [ite_eq_right (fun h => hrank h.1 he h.2)]
    exact (by decide : ∀ z : Dart G, z ≠ a → Dart.vertex (G := H) (E z.1, z.2) = z.vertex) d he
  have hrot : s.rotate = (E.prodCongr (Equiv.refl Bool)).permCongr
      (original.rotate * Equiv.swap a (original.rotate.symm a)) := by
    apply Equiv.ext
    intro d
    apply (Dart.indexEquiv H).injective
    apply Fin.ext
    change ((decode H table table_ok).rotate d).index = Dart.index (G := H)
      ((E.prodCongr (Equiv.refl Bool)).permCongr
        (original.rotate * Equiv.swap a (original.rotate.symm a)) d)
    rw [index_decode_rotate table_ok]
    exact (by decide : ∀ z : Dart H, table.successor.getD z.index 0 = Dart.index (G := H)
      ((E.prodCongr (Equiv.refl Bool)).permCongr
        (original.rotate * Equiv.swap a (original.rotate.symm a)) z)) d
  have h := original.numericalGenusZero_of_component_cutInterval s a a rfl (by decide)
    3 (by decide) no_loop_at_center hclass E hEnds hrot (by decide) (by decide)
  exact ⟨h.1, h.2 hz⟩

private abbrev alternatingGraph : Graph := ⟨[0, 1, 2], [(0, 1), (0, 2), (0, 1), (0, 2)]⟩
private abbrev splitGraph : Graph := ⟨[3, 0, 1, 2], [(3, 1), (0, 2), (3, 1), (0, 2)]⟩
private abbrev first : Dart alternatingGraph := (0, false)
private abbrev second : Dart alternatingGraph := (1, false)

private abbrev selected (d : Dart alternatingGraph) : Prop :=
  d.vertex = 0 ∧ d.reverse.vertex = 1

private def alternatingRotation : RotationSystem alternatingGraph where
  rotate := Equiv.swap first (3, false) * Equiv.swap first (2, false) *
    Equiv.swap first second * Equiv.swap (0, true) (2, true) * Equiv.swap (1, true) (3, true)
  sameCycle_iff := by decide

private theorem alternating_deleted_eq_bot :
    (alternatingGraph.toSimpleGraph.induce {u | u ≠ first.vertex}) = ⊥ := by
  ext u v
  have hu : u.val ≠ 0 := u.property
  have hv : v.val ≠ 0 := v.property
  change alternatingGraph.toSimpleGraph.Adj u.val v.val ↔ False
  simp [Graph.toSimpleGraph_adj, hu, hv]

-- The selected and remaining ends alternate, yet the split separates the actual components.
example : (∀ d : Dart alternatingGraph, d.vertex = 0 →
      (selected (alternatingRotation.rotate d) ↔ ¬selected d)) ∧
    ¬SameComponent splitGraph 3 0 ∧
      ∀ root, (splitGraph.componentGraph root).edges.length < alternatingGraph.edges.length := by
  refine ⟨by decide, ?_⟩
  have hloop : ∀ d : Dart alternatingGraph, d.vertex = first.vertex →
      d.reverse.vertex ≠ first.vertex := by decide
  have hclass (d : Dart alternatingGraph) (hd : d.vertex = first.vertex) : selected d ↔
      (alternatingGraph.toSimpleGraph.induce {u | u ≠ first.vertex}).Reachable
        ⟨first.reverse.vertex, hloop first rfl⟩ ⟨d.reverse.vertex, hloop d hd⟩ := by
    rw [alternating_deleted_eq_bot, SimpleGraph.reachable_bot]
    exact ⟨fun h => Subtype.ext h.2.symm, fun h => ⟨hd, (congrArg Subtype.val h).symm⟩⟩
  let E : Fin alternatingGraph.edges.length ≃ Fin splitGraph.edges.length := Equiv.refl _
  exact split_component_separates first second rfl 3 (by decide) hloop selected (by decide)
    (fun _ h => h.1) hclass E (by decide +revert) (by decide)

end CslibFrontierTests.RotationCutIntervalGenus

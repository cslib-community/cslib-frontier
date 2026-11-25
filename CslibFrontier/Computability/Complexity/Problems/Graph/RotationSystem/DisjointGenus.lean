/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DisjointRotation

/-!
# Numerical genus of a disjoint listed union

Every incident component has exactly its source vertex, edge and complete face counts.
Genus zero follows componentwise from the two source rotations. Empty graphs, closed
components and declared points are allowed, with no target-genus provider.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

open Equiv RotationCertificate Perm.SelectedOrbits

/-- Disjoint union preserves source numerical genus zero component by component. -/
theorem numericalGenusZero_disjointUnion {G H : Graph} (r : RotationSystem G)
    (s : RotationSystem H) (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hH : ∀ v ∈ H.incidenceVertices, v ∈ H.1)
    (hr : r.NumericalGenusZero) (hs : s.NumericalGenusZero) :
    (r.disjointUnion s).NumericalGenusZero := by
  classical
  let t := r.disjointUnion s
  let e := disjointDartEquiv G H
  have hT := endpoints_declared_disjointUnion G H hG hH
  have horbit {K : Graph} (rot : RotationSystem K)
      (hK : ∀ v ∈ K.incidenceVertices, v ∈ K.1) :
      rot.NumericalGenusZero ↔ ∀ x : Dart K,
        Nat.card (OrbitOn rot.rotate (fun b => SameComponent K x.vertex b.vertex)) +
          Nat.card (OrbitOn rot.faceNext (fun b => SameComponent K x.vertex b.vertex)) =
        Nat.card (OrbitOn (Dart.reversal K) (fun b => SameComponent K x.vertex b.vertex)) + 2 := by
    rw [rot.numericalGenusZero_iff_component_cards hK]
    refine forall_congr' fun x => ?_
    have hv := Nat.card_congr (rot.vertexOrbitEquiv hK x)
    have hε := Nat.card_congr (edgeOrbitEquiv K hK x)
    simp only [Nat.card_eq_finsetCard] at hv hε
    rw [← hv, ← hε, card_componentFaceIndices,
      rot.count_faceRepresentatives_eq_card_componentFace hK]
  have hEmpty {V : Type} (w : Perm V) : Nat.card (OrbitOn w (fun _ => False)) = 0 :=
    @Nat.card_of_isEmpty _ ⟨fun ⟨_, _, hb, _⟩ => hb⟩
  apply (horbit t hT).mpr
  intro d
  obtain ⟨a, rfl⟩ := e.surjective d
  let q (b : Dart (G.disjointUnion H)) := SameComponent (G.disjointUnion H) (e a).vertex b.vertex
  let p : Dart G ⊕ Dart H → Prop := match a with
    | Sum.inl a => Sum.elim (fun b => SameComponent G a.vertex b.vertex) (fun _ => False)
    | Sum.inr a => Sum.elim (fun _ => False) (fun b => SameComponent H a.vertex b.vertex)
  have hp (b : Dart G ⊕ Dart H) : p b ↔ q (e b) := by
    have he := (sameComponent_disjointUnion_iff hG hH a b).symm
    cases a <;> cases b <;> exact he
  have hcount (f : Perm (Dart G)) (g : Perm (Dart H)) (u : Perm (Dart (G.disjointUnion H)))
      (hm : ∀ b, e (Equiv.sumCongr f g b) = u (e b)) :
      Nat.card (OrbitOn u q) = match a with
        | Sum.inl a => Nat.card (OrbitOn f (fun b => SameComponent G a.vertex b.vertex))
        | Sum.inr a => Nat.card (OrbitOn g (fun b => SameComponent H a.vertex b.vertex)) := by
    rw [← Nat.card_congr (orbitOnEquiv e (Equiv.sumCongr f g) u hm p q hp)]
    cases a with
    | inl a =>
      change Nat.card (OrbitOn (Equiv.sumCongr f g)
        (Sum.elim (fun b => SameComponent G a.vertex b.vertex) (fun _ => False))) = _
      rw [card_orbitOn_sum, hEmpty, Nat.add_zero]
    | inr a =>
      change Nat.card (OrbitOn (Equiv.sumCongr f g)
        (Sum.elim (fun _ => False) (fun b => SameComponent H a.vertex b.vertex))) = _
      rw [card_orbitOn_sum, hEmpty, Nat.zero_add]
  rw [hcount r.rotate s.rotate t.rotate (fun b => (rotate_disjointUnion r s b).symm),
    hcount r.faceNext s.faceNext t.faceNext (fun b => (faceNext_disjointUnion r s b).symm),
    hcount (Dart.reversal G) (Dart.reversal H) (Dart.reversal (G.disjointUnion H))
      (reverse_disjointDartEquiv G H)]
  cases a with
  | inl a => exact (horbit r hG).mp hr a
  | inr a => exact (horbit s hH).mp hs a

end Cslib.Complexity.Graph.RotationSystem

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (indexed path color regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.ComponentOrder
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SeparatingPairOrder
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceDartColors
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Forward
import Mathlib.Data.Fin.VecNotation

/-! Color transport along the subdivided arm of a three-arm graph. -/

set_option linter.privateModule false

namespace CslibFrontierTests.DartPathColors

open Cslib.Complexity Cslib.Complexity.Graph

private abbrev G : Graph := ⟨[0, 1, 2], [(0, 2), (2, 1), (0, 1), (0, 1)]⟩

private abbrev a₀ : Dart G := (0, false)
private abbrev b₀ : Dart G := (2, false)
private abbrev c₀ : Dart G := (3, false)
private abbrev a₁ : Dart G := (1, true)
private abbrev b₁ : Dart G := (2, true)
private abbrev c₁ : Dart G := (3, true)

private def rotation : RotationSystem G where
  rotate := Equiv.swap a₀ c₀ * Equiv.swap a₀ b₀ *
    Equiv.swap a₁ b₁ * Equiv.swap a₁ c₁ * Equiv.swap (0, true) (1, false)
  sameCycle_iff := by decide

private def label (e : Fin G.edges.length) : Bool := decide (e ≠ 3)

private def color (d : Dart G) : Bool :=
  decide (d = a₀ ∨ d = (1, false) ∨ d = b₁)

private theorem sector (d : Dart G) :
    color d + color (rotation.rotate.symm d) = label d.1 :=
  (by decide : ∀ d : Dart G, color d + color (rotation.rotate.symm d) = label d.1) d

private abbrev path : Fin 2 → Dart G := ![a₀, (1, false)]

-- The selected arm passes through a degree-two vertex on its way from vertex zero to vertex one.
example : color a₀ + color a₁ = true := by
  have h := rotation.color_ends_eq_of_dart_path (n := 1) path color label (fun _ => false)
    (by decide) (by decide) sector
  exact h.trans (by decide)

private def flippedColor (d : Dart G) : Bool := color d ^^ decide (d.vertex = 1)

-- Flipping all colors at vertex one gives one nonzero route contribution on this arm.
example : flippedColor a₀ + flippedColor a₁ = false := by
  have h := rotation.color_ends_eq_of_dart_path (n := 1) path flippedColor label
    (fun e => decide (e ≠ 0)) (by decide) (by decide) (by decide)
  exact h.trans (by decide)

-- Looking toward the unselected arm gives opposite answers at the two ends.
example : rotation.rotate.symm a₀ = c₀ ∧ rotation.rotate.symm a₁ ≠ c₁ := by
  have left := rotation.color_sum_eq_true_iff_inverse_rotate_of_three_darts color label sector
    a₀ b₀ c₀ rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have right := rotation.color_sum_eq_true_iff_inverse_rotate_of_three_darts color label sector
    a₁ b₁ c₁ rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨left.mp (by decide), fun he => (by decide : color a₁ + color c₁ ≠ true) (right.mpr he)⟩

private def armLength : Fin 3 → ℕ := Fin.cases 1 (fun _ => 0)

private def arms (k : Fin 3) : Fin (armLength k + 1) → Dart G :=
  Fin.cases (motive := fun k => Fin (armLength k + 1) → Dart G) path
    (fun k => ![if k = 0 then b₀ else c₀]) k

private noncomputable def startPorts : Fin 3 ≃ {d : Dart G // d.vertex = 0} :=
  Equiv.ofBijective (fun k => ⟨arms k 0, by revert k; decide⟩)
    (by decide)

private noncomputable def finishPorts : Fin 3 ≃ {d : Dart G // d.vertex = 1} :=
  Equiv.ofBijective (fun k => ⟨(arms k (Fin.last (armLength k))).reverse, by revert k; decide⟩)
    (by decide)

private def sameArmCrossing (e f : Fin G.edges.length) : Bool :=
  decide ((e = 0 ∧ f = 1) ∨ (e = 1 ∧ f = 0))

private def internalFlip (d : Dart G) : Bool := color d ^^ decide (d.vertex = 2)

-- The two nonzero contributions within the subdivided arm cancel.
example : rotation.rotate.symm a₀ = c₀ ↔ rotation.rotate.symm a₁ ≠ c₁ := by
  have opposite := rotation.inverse_rotate_iff_not_inverse_rotate_of_three_paths
    arms startPorts finishPorts (fun _ => rfl) (fun _ => rfl) (by decide) (by decide)
    internalFlip label (by decide) (by decide) sameArmCrossing
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact opposite

private theorem crossingParity_of_embedding {K : Graph} {D : PolygonalDrawing K}
    (hD : D.IsEmbedding) {a b : Fin K.edges.length} (hne : a ≠ b) :
    (D.route a).intersectionParity (D.route b) = false := by
  classical
  unfold Cslib.Polygonal.Route.intersectionParity
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨z, hz, hzt⟩ := of_decide_eq_true h
  rw [openSegment_eq_image_lineMap] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  exact hD.segment_interior_disjoint ⟨a, s⟩ ⟨b, t⟩
    (fun he => hne (congrArg Sigma.fst he).symm) w hw
    (openSegment_subset_segment ℝ _ _ hzt)

-- In an actual regular embedding, the subdivided arm has its own rank interval when
-- the rotation is cut at the first direct edge.
example : ∃ D : PolygonalDrawing G, D.HasRegularContacts ∧ D.Realizes rotation ∧
    (rotation.rotate.symm a₀ = c₀ ↔ rotation.rotate.symm a₁ ≠ c₁) ∧
    ∃ a b : Dart G, a.vertex = 0 ∧ b.vertex = 0 ∧
      ∀ d : Dart G, d.vertex = 0 → (d = a₀ ↔
        rotation.rotationDistance b₀ a ≤ rotation.rotationDistance b₀ d ∧
          rotation.rotationDistance b₀ d ≤ rotation.rotationDistance b₀ b) := by
  classical
  have hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices := by decide
  have genus : rotation.NumericalGenusZero := by
    have check := RotationCertificate.verifyRotation_ofRotation rotation hG
    have he : RotationCertificate.verifyEuler G (RotationCertificate.ofRotation rotation) =
        true := by decide +kernel
    rw [← RotationCertificate.decode_ofRotation rotation hG]
    exact (RotationCertificate.verifyEuler_eq_true_iff check).mp he
  obtain ⟨D, hD, hR⟩ := rotation.exists_polygonalDrawing hG genus
  have hreg := hD.hasRegularContacts (fun d => RotationSystem.vertex_mem hG d) (by decide)
  refine ⟨D, hreg, hR, ?_, ?_⟩
  · apply hreg.inverse_rotate_iff_not_inverse_rotate_of_three_paths hD.simple hR hG arms
      startPorts finishPorts (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_
    · decide
    · decide
    · intro a b hab i j
      have hne : (arms a i).1 ≠ (arms b j).1 :=
        (by decide : ∀ a b : Fin 3, a ≠ b → ∀ i j, (arms a i).1 ≠ (arms b j).1) a b hab i j
      exact crossingParity_of_embedding hD hne
  · let one : {w : ℕ // w ≠ 0} := ⟨1, by decide⟩
    let K := (G.toSimpleGraph.induce {w | w ≠ 0}).induce {w | w ≠ one}
    let two : {w : {n : ℕ // n ≠ 0} // w ≠ one} := ⟨⟨2, by decide⟩, by decide⟩
    let C := K.connectedComponentMk two
    let S : Set ℕ := Subtype.val '' (Subtype.val '' C.supp)
    have htwo : (2 : ℕ) ∈ S := ⟨two.val, ⟨two, rfl, rfl⟩, rfl⟩
    have hone : (1 : ℕ) ∉ S := by
      rintro ⟨w, ⟨x, _, rfl⟩, hx⟩
      exact x.property (Subtype.ext hx)
    have other : ∀ d : Dart G, d.vertex = 0 → d ≠ a₀ → d.reverse.vertex = 1 := by decide
    have enters (d : Dart G) (hd : d.vertex = 0) : d.reverse.vertex ∈ S ↔ d = a₀ := by
      constructor
      · intro hm
        by_contra he
        exact hone (other d hd he ▸ hm)
      · rintro rfl
        exact htwo
    obtain ⟨a, b, ha, hb, _, _, hinterval⟩ :=
      ClosedPassages.exists_separating_component_rank_interval hR hreg hD.simple
        hD.vertices_injective
        (RotationSystem.vertex_mem hG) (fun _ _ hne _ => crossingParity_of_embedding hD hne)
        one C b₀ a₀ rfl rfl hone htwo (by
          intro d hd hC hd'
          have h := other d hd (fun he => hC ((enters d hd).mpr he))
          exact (show (⟨d.reverse.vertex, hd'⟩ : {w : ℕ // w ≠ 0}) = one from
            Subtype.ext h).symm ▸ SimpleGraph.Reachable.refl one)
    exact ⟨a, b, ha, hb, fun d hd => (enters d hd).symm.trans (hinterval d hd)⟩

private abbrev withSpurs : Graph :=
  ⟨[0, 1, 2, 3, 4], [(0, 2), (2, 1), (0, 1), (0, 1), (2, 3), (0, 4)]⟩

private def spurRotation : RotationSystem withSpurs where
  rotate := Equiv.swap (0, false) (5, false) * Equiv.swap (0, false) (3, false) *
    Equiv.swap (0, false) (2, false) * Equiv.swap (1, true) (2, true) *
    Equiv.swap (1, true) (3, true) * Equiv.swap (0, true) (4, false) *
    Equiv.swap (0, true) (1, false)
  sameCycle_iff := by decide

private def spurArms (k : Fin 3) (i : Fin (armLength k + 1)) : Dart withSpurs :=
  ⟨Fin.castLE (by decide) (arms k i).1, (arms k i).2⟩

private abbrev one : {w : ℕ // w ≠ 0} := ⟨1, by decide⟩
private abbrev awayPair := (withSpurs.toSimpleGraph.induce {w | w ≠ 0}).induce {w | w ≠ one}
private abbrev two : {w : {x : ℕ // x ≠ 0} // w ≠ one} := ⟨⟨2, by decide⟩, by decide⟩
private abbrev armComponent := awayPair.connectedComponentMk two

private def spurComponents (k : Fin 3) : Option awayPair.ConnectedComponent :=
  if k = 0 then some armComponent else none

-- Taking the subdivided arm as the reference, the two direct pieces have opposite list
-- orders in a realized rotation with extra edges at an interior vertex and a separator.
example :
    let first (k : Fin 3) := spurArms k 0
    let last (k : Fin 3) := (spurArms k (Fin.last (armLength k))).reverse
    let pieces : List (Fin 3) := [1, 2]
    ∃ D : PolygonalDrawing withSpurs, D.HasRegularContacts ∧ D.Realizes spurRotation ∧
      spurRotation.rotate.symm (spurArms 0 0).reverse ≠ spurArms 0 1 ∧
      pieces.mergeSort (fun i j => decide
        (spurRotation.rotationDistance (last 0) (last i) ≤
          spurRotation.rotationDistance (last 0) (last j))) =
        (pieces.mergeSort (fun i j => decide
          (spurRotation.rotationDistance (first 0) (first i) ≤
            spurRotation.rotationDistance (first 0) (first j)))).reverse := by
  classical
  dsimp only
  have hG : ∀ v ∈ withSpurs.incidenceVertices, v ∈ withSpurs.vertices := by decide
  have genus : spurRotation.NumericalGenusZero := by
    have check := RotationCertificate.verifyRotation_ofRotation spurRotation hG
    rw [← RotationCertificate.decode_ofRotation spurRotation hG]
    exact (RotationCertificate.verifyEuler_eq_true_iff check).mp (by decide +kernel)
  obtain ⟨D, hD, hR⟩ := spurRotation.exists_polygonalDrawing hG genus
  have hreg := hD.hasRegularContacts (fun d => RotationSystem.vertex_mem hG d) (by decide)
  refine ⟨D, hreg, hR, by decide, ?_⟩
  let first (k : Fin 3) := spurArms k 0
  let last (k : Fin 3) := (spurArms k (Fin.last (armLength k))).reverse
  have heven : D.EvenCrossings (fun w => w = 0 ∨ w = 1) :=
    fun _ _ hne _ => crossingParity_of_embedding hD hne
  apply hreg.mergeSort_eq_reverse_of_separating_components hD.simple hR hG heven
    one (Or.inl rfl) (Or.inr rfl) first last (by decide) (by decide) (by decide)
    spurComponents _ _ 0 [1, 2] (by decide)
  · intro i j C hi hj
    have eqZero {k : Fin 3} (h : spurComponents k = some C) : k = 0 := by
      by_contra hne
      simp [spurComponents, hne] at h
    exact (eqZero hi).trans (eqZero hj).symm
  · have hin : (2 : ℕ) ∈ Subtype.val '' (Subtype.val '' armComponent.supp) :=
      ⟨two.val, ⟨two, rfl, rfl⟩, rfl⟩
    intro k
    fin_cases k
    · exact ⟨hin, hin⟩
    · rfl
    · rfl

end CslibFrontierTests.DartPathColors

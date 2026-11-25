/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (indexed path color regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.ThreePathOrder
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

-- The same three arms have an actual regular polygonal embedding.
example : ∃ D : PolygonalDrawing G, D.HasRegularContacts ∧ D.Realizes rotation ∧
    (rotation.rotate.symm a₀ = c₀ ↔ rotation.rotate.symm a₁ ≠ c₁) := by
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
  refine ⟨D, hreg, hR, ?_⟩
  apply hreg.inverse_rotate_iff_not_inverse_rotate_of_three_paths hD.simple hR hG arms
    startPorts finishPorts (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_
  · decide
  · decide
  · intro a b hab i j
    have hne : (arms a i).1 ≠ (arms b j).1 :=
      (by decide : ∀ a b : Fin 3, a ≠ b → ∀ i j, (arms a i).1 ≠ (arms b j).1) a b hab i j
    unfold Cslib.Polygonal.Route.intersectionParity
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨z, hz, hzt⟩ := of_decide_eq_true h
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hD.segment_interior_disjoint ⟨(arms a i).1, s⟩ ⟨(arms b j).1, t⟩
      (fun he => hne (congrArg Sigma.fst he).symm) w hw
      (openSegment_subset_segment ℝ _ _ hzt)

end CslibFrontierTests.DartPathColors

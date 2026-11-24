/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (indexed path color regression)

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.FaceDartColors
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

end CslibFrontierTests.DartPathColors

/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Probability.Minimax.Dantzig
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Linear programs over `ℚ` read off symmetric games

Checked runs of the reductions in `CslibFrontier.Probability.Minimax.Dantzig`. Each game
solution is written down by hand and checked with `decide +kernel`; the theorems then read the
status of the program off it.

* Dantzig's game of `min {x₁ + x₂ | x₁ + 2 x₂ ≥ 2, 2 x₁ + x₂ ≥ 2, x ≥ 0}`: the solution
  `(1/9, 1/9, 2/9, 2/9, 1/3)` gives the optimal solution `(2/3, 2/3)` of value `4/3` and the
  optimal dual solution `(1/3, 1/3)`.
* Adler's bounded game for the integer feasibility problems `x₁ + x₂ = 1` and `x₁ + x₂ = -1`,
  `x ≥ 0`, with `B = 1` and `β = 16`: a solution with `u = 0` gives the solution `(1, 0)` of the
  first, and one with `0 < u` shows that the second has none.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.Dantzig

open Matrix Cslib.Probability

/-! ### Dantzig's game of a linear program -/

/-- The constraint matrix of `x₁ + 2 x₂ ≥ 2`, `2 x₁ + x₂ ≥ 2`. -/
def lpA : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 2, 1]

/-- The right-hand side `(2, 2)`. -/
def lpB : Fin 2 → ℚ := ![2, 2]

/-- The objective `x₁ + x₂`. -/
def lpC : Fin 2 → ℚ := ![1, 1]

theorem lp_solution :
    IsSymmetricGameSolution (dantzigGame lpA lpB lpC)
      (Sum.elim ![1 / 9, 1 / 9] (Sum.elim ![2 / 9, 2 / 9] fun _ => 1 / 3)) := by
  refine isSymmetricGameSolution_dantzigGame_iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

/-- The game solution has `t = 1/3 > 0`, so `x / t = (2/3, 2/3)` is optimal, of value `4/3`, and
`y / t = (1/3, 1/3)` is optimal for the dual. -/
example :
    (∀ x', 0 ≤ x' → lpB ≤ lpA *ᵥ x' → 4 / 3 ≤ lpC ⬝ᵥ x') ∧
      ∀ y', 0 ≤ y' → y' ᵥ* lpA ≤ lpC → y' ⬝ᵥ lpB ≤ 4 / 3 := by
  obtain ⟨-, hx, -, hy⟩ := lp_solution.optimal_of_dantzigGame (by norm_num)
  have hxv : lpC ⬝ᵥ ((1 / 3 : ℚ)⁻¹ • ![2 / 9, 2 / 9]) = 4 / 3 := by decide +kernel
  have hyv : ((1 / 3 : ℚ)⁻¹ • ![1 / 9, 1 / 9]) ⬝ᵥ lpB = 4 / 3 := by decide +kernel
  exact ⟨fun x' h0 h => hxv ▸ hx x' h0 h, fun y' h0 h => hyv ▸ hy y' h0 h⟩

/-- The read-off point is `(2/3, 2/3)`. -/
example : ((1 / 3 : ℚ)⁻¹ • ![2 / 9, 2 / 9] : Fin 2 → ℚ) = ![2 / 3, 2 / 3] := by
  decide +kernel

/-! ### Adler's bounded game of a linear feasibility problem -/

/-- The integer constraint matrix of `x₁ + x₂ = b`. -/
def lfA : Matrix (Fin 1) (Fin 2) ℤ := !![1, 1]

/-- The bounded game `F(Â, b̂(16))` of `x₁ + x₂ = b`, `x ≥ 0`. For `B = 1`, `m = 1`, `n = 2` the
bound is `2 * (2! * (1 * 1 ^ 2 + 1) ^ 2) = 16`. -/
def boundedGame (b : Fin 1 → ℤ) :=
  feasibilityGame
    (fromBlocks (lfA.map (Int.cast : ℤ → ℚ)) (0 : Matrix (Fin 1) Unit ℚ)
      (of fun _ _ => 1 : Matrix Unit (Fin 2) ℚ) (1 : Matrix Unit Unit ℚ))
    (Sum.elim (fun i => (b i : ℚ)) fun _ => 16)

/-- The bound of `resolves_of_feasibilityGame_bounded` for `B = 1`, `m = 1`, `n = 2`. -/
theorem bound_le : ((Fintype.card (Fin 2) * ((Fintype.card (Fin 2)).factorial *
    (Fintype.card (Fin 1) * 1 ^ 2 + 1) ^ Fintype.card (Fin 2)) : ℕ) : ℚ) ≤ 16 := by
  decide +kernel

theorem lfA_le (i : Fin 1) (j : Fin 2) : |lfA i j| ≤ (1 : ℕ) := by
  revert i j
  decide +kernel

/-- A solution with `y = 0`, `v = 0`, `x̂ = (1, 0, 15) / 17`, `u = 0`, `t = 1 / 17`. -/
theorem feasible_solution :
    IsSymmetricGameSolution (boundedGame ![1])
      (Sum.elim (Sum.elim 0 fun _ => 0)
        (Sum.elim (Sum.elim (Sum.elim ![1 / 17, 0] fun _ => 15 / 17) fun _ => 0)
          fun _ => 1 / 17)) := by
  refine isSymmetricGameSolution_dantzigGame_iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

/-- `u = 0`, so the game solves `x₁ + x₂ = 1`, `x ≥ 0`, by the read-off point `(1, 0)`. -/
example : (lfA.map (Int.cast : ℤ → ℚ)) *ᵥ ![1, 0] = fun i => ((![1] : Fin 1 → ℤ) i : ℚ) := by
  obtain ⟨-, h, -⟩ := resolves_of_feasibilityGame_bounded lfA_le
    (by decide +kernel) bound_le feasible_solution
  obtain ⟨-, hAx⟩ := h rfl
  have hx : ((1 / 17 : ℚ)⁻¹ • ((Sum.elim ![1 / 17, 0] fun _ => 15 / 17 : Fin 2 ⊕ Unit → ℚ) ∘
      Sum.inl) : Fin 2 → ℚ) = ![1, 0] := by decide +kernel
  rwa [hx] at hAx

/-- A solution with `y = (0, 1/36)`, `v = 1/36`, `x̂ = (0, 0, 31/36)`, `u = 1/36`,
`t = 1/18`. -/
theorem infeasible_solution :
    IsSymmetricGameSolution (boundedGame ![-1])
      (Sum.elim (Sum.elim (Sum.elim 0 fun _ => 1 / 36) fun _ => 1 / 36)
        (Sum.elim (Sum.elim (Sum.elim 0 fun _ => 31 / 36) fun _ => 1 / 36) fun _ => 1 / 18)) := by
  refine isSymmetricGameSolution_dantzigGame_iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

/-- `0 < u`, so `x₁ + x₂ = -1`, `x ≥ 0` has no solution over `ℚ`. -/
example : ¬∃ x : Fin 2 → ℚ, 0 ≤ x ∧
    lfA.map (Int.cast : ℤ → ℚ) *ᵥ x = fun i => ((![-1] : Fin 1 → ℤ) i : ℚ) :=
  (resolves_of_feasibilityGame_bounded lfA_le (by decide +kernel) bound_le
    infeasible_solution).2.2 (by norm_num)

end CslibFrontierTests.GameTheory.Dantzig

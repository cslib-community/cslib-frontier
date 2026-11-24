/-
Copyright (c) 2026 xcthulhu, teddyli18000. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: xcthulhu, teddyli18000
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Regression for approximate LP dual certificates

The multiplier is nonnegative but not exactly dual feasible. Its two residual
coordinates have opposite signs, so the certificate uses both variable bounds.
-/

-- This module contains regression examples only, not an exported API.
set_option linter.privateModule false

open Matrix

private def A : Matrix (Fin 1) (Fin 2) ℚ := !![1, 1]
private def b : Fin 1 → ℚ := ![2]
private def c : Fin 2 → ℚ := ![1, 0]
private def y : Fin 1 → ℚ := ![1 / 2]
private def l : Fin 2 → ℚ := ![0, -1]
private def u : Fin 2 → ℚ := ![2, 1]

-- The certificate does not satisfy the exact dual equality.
example : y ᵥ* A ≠ c := by
  intro h
  have h₀ := congrFun h (0 : Fin 2)
  norm_num [A, c, y, vecMul, dotProduct, Fin.sum_univ_one] at h₀

-- The residual correction is 1 + 1/2. Exact dual feasibility is not assumed.
example (x : Fin 2 → ℚ) (hx : A *ᵥ x ≤ b) (hl : l ≤ x) (hu : x ≤ u) :
    c ⬝ᵥ x ≤ 5 / 2 := by
  have hy : 0 ≤ y := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    norm_num [y]
  have h := Matrix.dotProduct_le_dotProduct_add_max_of_mulVec_le
    (c := c) hx hy hl hu
  have hbound : y ⬝ᵥ b +
      ∑ j, max ((c - y ᵥ* A) j * l j) ((c - y ᵥ* A) j * u j) = 5 / 2 := by
    norm_num [A, b, c, y, l, u, vecMul, dotProduct, Fin.sum_univ_one, Fin.sum_univ_two,
      Pi.sub_apply, max_def]
  exact h.trans_eq hbound

-- The feasible region is nonempty and contains a point attaining objective 2.
example : A *ᵥ (![2, -1] : Fin 2 → ℚ) ≤ b ∧
    l ≤ (![2, -1] : Fin 2 → ℚ) ∧ (![2, -1] : Fin 2 → ℚ) ≤ u ∧
    c ⬝ᵥ (![2, -1] : Fin 2 → ℚ) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    norm_num [A, b, mulVec, dotProduct, Fin.sum_univ_two]
  · intro i
    fin_cases i <;> norm_num [l]
  · intro i
    fin_cases i <;> norm_num [u]
  · norm_num [c, dotProduct, Fin.sum_univ_two]

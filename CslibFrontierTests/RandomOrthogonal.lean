/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.LinearAlgebra.RandomOrthogonal
import Mathlib.Tactic.NormNum

/-! # Checked clients for Arora–Barak, Exercise 20.5

The exercise's `1 / 10` bound follows from the `1 / 4` bound, and the hypothesis `a ≠ 0` holds for
a concrete string. -/

set_option linter.privateModule false

open Finset Matrix

/-- The exercise's form: probability at least `1 / 10`. -/
example (n : ℕ) (a : Fin n → ZMod 2) (ha : a ≠ 0) :
    (1 / 10 : ℝ) ≤
      (#{y : Fin (n - 1) → Fin n → ZMod 2 |
          (∀ i, y i ⬝ᵥ a = 0) ∧ ∀ w, (∀ i, y i ⬝ᵥ w = 0) → w = 0 ∨ w = a} : ℝ) /
        #{y : Fin (n - 1) → Fin n → ZMod 2 | ∀ i, y i ⬝ᵥ a = 0} :=
  le_trans (by norm_num) (Cslib.LinearAlgebra.one_div_four_le_card_determines_div_card ha)

/-- The hypothesis is satisfiable: `a = (1, 0, 0)`. -/
example : (1 / 4 : ℝ) ≤
      (#{y : Fin (3 - 1) → Fin 3 → ZMod 2 |
          (∀ i, y i ⬝ᵥ Pi.single 0 1 = 0) ∧
            ∀ w, (∀ i, y i ⬝ᵥ w = 0) → w = 0 ∨ w = Pi.single 0 1} : ℝ) /
        #{y : Fin (3 - 1) → Fin 3 → ZMod 2 | ∀ i, y i ⬝ᵥ Pi.single 0 1 = 0} :=
  Cslib.LinearAlgebra.one_div_four_le_card_determines_div_card (by decide)

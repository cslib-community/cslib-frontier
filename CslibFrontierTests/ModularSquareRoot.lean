/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.ModularSquareRoot
import Mathlib.Tactic.NormNum.Prime

/-! Checked instances of the square-root algorithm of Goldreich Exercise 6.16, items 1–3. -/

set_option linter.privateModule false

namespace Cslib.Complexity.ModularSquareRoot

-- `P = 7 ≡ 3 (mod 4)`: no descent, the root is `2 ^ ((7 + 1) / 4) = 4`, whatever `t` is.
example : descentExponents 7 2 0 = (3, 0) ∧ sqrtMod 7 2 0 = 4 := by decide

-- `P = 13 ≡ 5 (mod 8)`: one halving with the non-residue `2`; `7 ^ 2 = 49 ≡ 10`.
example : descentExponents 13 10 2 = (3, 6) ∧ sqrtMod 13 10 2 = 7 := by decide

-- `P = 17 ≡ 1 (mod 16)`: three halvings with the non-residue `3`; `2 ≡ 6 ^ 2` is a
-- residue.
example : (descentExponents 17 2 3).1 = 1 ∧ sqrtMod 17 2 3 ^ 2 % 17 = 2 := by decide

-- The correctness theorem applied with its hypotheses checked.
example : (sqrtMod 17 2 3 : ZMod 17) ^ 2 = 2 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  exact sqrtMod_sq (by norm_num) ⟨6, by decide⟩ (Or.inr (by decide))

-- Item 3's exponents for `P = 13`: `10 ^ 3 * 2 ^ 6 ≡ 1 (mod 13)`.
example : Odd (descentExponents 13 10 2).1 ∧ Even (descentExponents 13 10 2).2 ∧
    ((10 : ℕ) : ZMod 13) ^ (descentExponents 13 10 2).1 *
      ((2 : ℕ) : ZMod 13) ^ (descentExponents 13 10 2).2 = 1 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact descentExponents_spec (by norm_num) (by decide) ⟨6, by decide⟩ (Or.inr (by decide))

end Cslib.Complexity.ModularSquareRoot

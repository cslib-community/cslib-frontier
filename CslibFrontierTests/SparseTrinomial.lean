/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ReducedProduct

/-! Regression tests for both halves of the sparse product reduction. -/

open Polynomial Cslib.SparseTrinomial

local instance : Fact (1 < (8 : ℕ)) := ⟨by decide⟩

-- At q = 2 the first wrapped monomial maps to one.
example : (((X : (ZMod 8)[X]) ^ 6 %ₘ (X ^ 4 + X ^ 2 + 1)).coeff 0) = 1 := by
  rw [coeff_mod_sparse 2 (by decide) _ (by norm_num) 0 (by decide)]
  norm_num [reducedCoeff, coeff_X_pow]

-- The low and high halves both receive the negative coefficient for X^(2q).
example : (((X : (ZMod 8)[X]) ^ 4 %ₘ (X ^ 4 + X ^ 2 + 1)).coeff 0) = -1 ∧
    (((X : (ZMod 8)[X]) ^ 4 %ₘ (X ^ 4 + X ^ 2 + 1)).coeff 2) = -1 := by
  constructor
  · rw [coeff_mod_sparse 2 (by decide) _ (by norm_num) 0 (by decide)]
    norm_num [reducedCoeff, coeff_X_pow]
  · rw [coeff_mod_sparse 2 (by decide) _ (by norm_num) 2 (by decide)]
    norm_num [reducedCoeff, coeff_X_pow]


open Cslib.ConvolutionOperand.Signed

-- Negative diagonal, row 1, shift 1, sum bit 2, q=2 and i=0.
-- The operands are coefficient 1/bit 1 and coefficient 3/bit 1.
example :
    let p : Query := ⟨2, 4, 0, [false, true, false, true, false, true], 2, false, false⟩
    source p = some (1, 1) ∧ source { p with right := true } = some (3, 1) ∧ correction p := by
  decide

-- The negative carry contributes exactly one; no recursive operand request is made.
example :
    let p : Query := ⟨2, 4, 0, [false, true, false, true, false, true], 0, true, false⟩
    source p = none ∧ correction p ∧ correction { p with bit := 1 } = false := by
  decide

-- The high half omits the third diagonal, and a one-bit tag is padding.
example :
    let p : Query := ⟨2, 4, 2, [true, false, false, false, false, false], 0, false, false⟩
    source p = none ∧ source { p with path := [false] } = none ∧ correction p = false := by
  decide

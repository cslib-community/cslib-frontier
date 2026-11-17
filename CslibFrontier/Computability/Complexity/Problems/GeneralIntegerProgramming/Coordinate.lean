/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.GeneralIntegerProgramming
import Mathlib.Data.List.GetD

/-!
# Coordinate bounds for integer programs

`IntegerProgram.unitCoeffs` represents a signed coordinate vector in the coefficient-list layout
of integer programs. `IntegerProgram.sum_unitCoeffs` evaluates it. The zero-one hardness and
rational denominator-clearing reductions use these vectors to constrain individual coordinates.
-/

public section

namespace Cslib.Complexity.IntegerProgram
open Finset

/-- A list of `n` integer coefficients, zero except for entry `j`, which has value `s`. -/
@[expose] def unitCoeffs (n j : ℕ) (s : ℤ) : List ℤ :=
  (List.range n).map fun k => if k = j then s else 0

/-- Evaluation of a signed coordinate vector. -/
theorem sum_unitCoeffs {n j : ℕ} (hj : j < n) (s : ℤ) (x : Fin n → ℤ) :
    ∑ k : Fin n, (unitCoeffs n j s).getD k 0 * x k = s * x ⟨j, hj⟩ := by
  have heq : ∀ k : Fin n, (unitCoeffs n j s).getD k 0 = if k = ⟨j, hj⟩ then s else 0 := by
    intro k
    simp [unitCoeffs, List.getD_eq_getElem?_getD, Fin.ext_iff, k.isLt]
  simp only [heq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Cslib.Complexity.IntegerProgram

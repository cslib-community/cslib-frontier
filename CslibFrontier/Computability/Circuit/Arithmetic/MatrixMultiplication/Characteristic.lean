/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.StrassenRank
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Specialization

/-!
# The exponent over an algebraically closed field of the same characteristic

For every field `F` of characteristic `p` and every algebraically closed field `KK` of
characteristic `p`, `omega KK ≤ omega F` (`omega_le_of_isAlgClosed`). A rank decomposition of
`⟨v, v, v⟩` over `F` transfers to `KK` (`Tensor.Rank.transfer`), and `omega` is the rank exponent
(`omega_eq_rankExponent`). So a lower bound on `omega` over the algebraic closure of `𝔽_p`, or of
`ℚ`, holds over every field of that characteristic.

## Main results

* `Cslib.Circuits.Arithmetic.MatrixMultiplication.omega_le_of_isAlgClosed`
-/

public section

namespace Cslib.Circuits.Arithmetic.MatrixMultiplication

open Cslib.Tensor

/-- **The exponent over an algebraically closed field is the smallest in its characteristic.** -/
theorem omega_le_of_isAlgClosed {F KK : Type} [Field F] [Field KK] [IsAlgClosed KK] (p : ℕ)
    [CharP F p] [CharP KK p] : omega KK ≤ omega F := by
  rw [omega_eq_rankExponent, omega_eq_rankExponent]
  refine rankExponent_le_of_rank fun v r hr => ?_
  have := Rank.transfer (F := F) (KK := KK) p (mm v v v : Tensor ℤ _ _ _) (r := r)
    (by rwa [map_mm])
  rwa [map_mm] at this

end Cslib.Circuits.Arithmetic.MatrixMultiplication

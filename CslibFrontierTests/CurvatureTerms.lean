/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Estimates
import CslibFrontier.Foundations.LinearAlgebra.Matrix.GlueDeterminant
import CslibFrontier.Foundations.RingTheory.PowerSeries.Meixner

/-! Tests of the definitions and estimates for the identity of crossing wires:

* glued determinants vanish when the groups have different sizes;
* the two coefficient families: their recursions, generating functions and orthogonality;
* the states of bounded energy;
* logarithms against square roots. -/

namespace CslibFrontierTests.CurvatureTerms

open Cslib.Circuits.Arithmetic.Separation.Curvature Filter

/-- A glued matrix whose row groups and column groups differ in size has determinant `0`. -/
example (N₁ N₂ : Matrix (Fin 2) (Fin 2) ℤ) :
    (Matrix.glue (fun i : Fin 2 => i = 0) (fun _ => True) N₁ N₂).det = 0 :=
  Matrix.det_glue_eq_zero_of_card_ne _ _ _ _ (by decide)

/-- The coefficient families start with `1`. -/
example (y : ℤ) (r : ℕ) : PowerSeries.meixnerB y r 0 = 1 ∧ PowerSeries.meixnerC y r 0 = 1 :=
  ⟨PowerSeries.meixnerB_zero_right y r, PowerSeries.meixnerC_zero_right y r⟩

/-- The generating function of the first family. -/
example (y : ℤ) (r : ℕ) :
    PowerSeries.mk (PowerSeries.meixnerB y r) * (1 + PowerSeries.C y * PowerSeries.X) ^ (r + 1) =
      (1 + PowerSeries.X) ^ r :=
  PowerSeries.mk_meixnerB_mul_pow y r

/-- Orthogonality modulo `y^N` for distinct indices. -/
example (y : ℤ) (N : ℕ) :
    y ^ N ∣ (1 - y) * ∑ r ∈ Finset.range N,
      y ^ r * (PowerSeries.meixnerB y r 1 * PowerSeries.meixnerB y r 2) := by
  simpa using PowerSeries.pow_dvd_meixnerB_orthogonality y N 1 2

/-- Only the empty state has energy `0`. -/
example : logLowStates 0 = 0 := logLowStates_zero

/-- The states of energy at most `E` are at most the square of the sets of energy at most `E`. -/
example (E : ℕ) : (lowStates E).card ≤ (lowSets E).card ^ 2 := by
  rw [sq]
  exact card_lowStates_le E

/-- `log (2 n + 1) ≤ √n / 10` for all large `n`. -/
example : ∀ᶠ n : ℕ in atTop, Real.log (2 * n + 1) ≤ (1 / 10) * Real.sqrt n :=
  eventually_log_le_mul_sqrt (by norm_num) (by norm_num)

end CslibFrontierTests.CurvatureTerms

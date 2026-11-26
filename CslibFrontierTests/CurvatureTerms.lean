/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.AtOne
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Estimates
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Inversion
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.StateWords
import CslibFrontier.Foundations.LinearAlgebra.Matrix.GlueDeterminant
import CslibFrontier.Foundations.RingTheory.PowerSeries.Meixner

/-! Tests of the definitions and estimates for the identity of crossing wires:

* glued determinants vanish when the groups have different sizes;
* the two coefficient families: their recursions, generating functions and orthogonality;
* the states of bounded energy, a state of size `1` and energy `2` and its word;
* the coincidence determinant, the matrix `Ψ`, the multipliers and the term matrices;
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

/-- The coincidence determinant of two equal increasing tuples is `1`. -/
example : (Matrix.of fun i j : Fin 2 => if ![0, 3] i = ![0, 3] j then (1 : ℤ) else 0).det = 1 := by
  rw [det_coinc (R := ℤ) ![0, 3] ![0, 3] (by decide) (by decide)]
  simp

/-- The coincidence determinant of two different increasing tuples is `0`. -/
example : (Matrix.of fun i j : Fin 2 => if ![0, 3] i = ![1, 3] j then (1 : ℤ) else 0).det = 0 := by
  rw [det_coinc (R := ℤ) ![0, 3] ![1, 3] (by decide) (by decide)]
  exact ite_eq_right fun h => by simpa using congrFun h 0

/-- The state `({0}, {0})` has size `1` and energy `2`, and its word has energy `2`. -/
example : (({0}, {0}) : Finset ℕ × Finset ℕ) ∈ states 1 2 ∧
    wordEnergy (word (⟨({0}, {0}), by simp [mem_lowStates, energy]⟩ : ↥(states 1 2))) = 2 :=
  ⟨by simp [mem_lowStates, energy], wordEnergy_word _⟩

/-- Ring homomorphisms commute with `Ψ`. -/
example (x : ℤ) (sa sb sc sd : Word 1) :
    Int.castRingHom ℚ (psi x sa sb sc sd) = psi (x : ℚ) sa sb sc sd :=
  map_psi _ x sa sb sc sd

/-- The product of the multipliers for one row and column at each site. -/
example (x : ℤ) (fa fb fc fd : Fin 1 → ℕ) :
    ∏ i, multiplier x fa fb fc fd i = (x ^ 2 - 1) ^ 1 *
      x ^ ((∑ i, (2 * fa i + 1)) + (∑ i, (2 * fc i + 1)) + (∑ i, 2 * fd i) +
        ∑ i, (2 * fb i + 2)) :=
  prod_multiplier x fa fb fc fd

/-- A term matrix of the expansion is glued from its two halves. -/
example (T : Finset (Fin 1 ⊕ Fin 1)) (X Y : Matrix (Fin 2) (Fin 2) ℤ)
    (A B' : Matrix (Fin 2) (Fin 1) ℤ)
    (A' B : Matrix (Fin 1) (Fin 2) ℤ) :
    termMat T X A A' Y B B' =
      Matrix.glue (rowGroup T) colGroup (termMat T X A A' 0 0 0) (termMat T 0 0 0 Y B B') :=
  termMat_eq_glue T X A A' Y B B'

end CslibFrontierTests.CurvatureTerms

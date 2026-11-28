/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Uniform averages of measurements

Sampling an index uniformly and then measuring defines another measurement.
For binary measurements its observable is the uniform average of the original
observables.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped BigOperators

variable {ι α A : Type*} [Fintype ι] [Nonempty ι] [Fintype α] [Ring A] [PartialOrder A]
  [IsOrderedAddMonoid A] [Module ℚ≥0 A] [PosSMulMono ℚ≥0 A]

/-- Choose one of the measurements uniformly at random. -/
@[expose] noncomputable def average (M : ι → Measurement α A) : Measurement α A where
  effect a := 𝔼 i, (M i).effect a
  nonneg a := expect_nonneg fun i _ => (M i).nonneg a
  sum_effect := by
    rw [← expect_sum_comm]
    simp only [sum_effect, Fintype.expect_const]

/-- Taking the observable commutes with uniform averaging. -/
theorem observable_average (M : ι → Measurement Bool A) :
    (average M).observable = 𝔼 i, (M i).observable := by
  simp only [average, observable, expect_sub_distrib]

/-- If every observable in the family commutes with an operator, then the
observable of their average measurement commutes with that operator. -/
theorem commute_observable_average [Algebra ℂ A] (M : ι → Measurement Bool A) (b : A)
    (h : ∀ i, Commute (M i).observable b) : Commute (average M).observable b := by
  rw [observable_average, Finset.expect, ← NNRat.cast_smul_eq_nnqsmul ℂ]
  exact (Commute.sum_left _ _ _ fun i _ => h i).smul_left _

end Cslib.Quantum.Measurement

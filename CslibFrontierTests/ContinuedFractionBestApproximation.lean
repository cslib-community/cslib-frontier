/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.NumberTheory.ContinuedFractions.BestApproximation
import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum

/-! Checked uses of strict best approximation: a nonterminal rational convergent, rational
termination, integer and negative inputs, and the counterexample at index zero. -/

set_option linter.privateModule false

open GenContFract (of)

-- The first convergent to 7/10 is 1; it is closer than every other integer.
example (c : ℤ) (hc : c ≠ 1) : |(7 / 10 : ℝ) - 1| < |(7 / 10 : ℝ) - c| := by
  have hconv : (7 / 10 : ℝ).convergent 1 = 1 := by
    norm_num [Real.convergent_succ, Real.convergent_zero, Int.fract]
  simpa only [hconv, Rat.cast_one, Int.cast_one, div_one] using
    Real.abs_sub_convergent_lt (7 / 10 : ℝ) (n := 1) (c := c) (d := 1)
      (by omega) (by omega) (by rw [hconv]; decide) (by rw [hconv]; simpa using hc)

-- No n = 0 version can hold, even for a positive rational input.
example : |(7 / 10 : ℝ) - 1| <
    |(7 / 10 : ℝ) - ((7 / 10 : ℝ).convergent 0 : ℝ)| := by
  norm_num [Real.convergent_zero]

-- At the final rational convergent the error is zero, and remains zero afterwards.
example : (7 / 10 : ℝ).convergent 3 = 7 / 10 ∧
    (7 / 10 : ℝ).convergent 4 = 7 / 10 := by
  norm_num [Real.convergent_succ, Real.convergent_zero, Int.fract]

-- This application is after termination and permits an unreduced competing fraction.
example : |(7 / 10 : ℝ) - ((7 / 10 : ℝ).convergent 4 : ℝ)| <
    |(7 / 10 : ℝ) - 6 / 8| := by
  apply Real.abs_sub_convergent_lt (n := 4) (c := 6) (d := 8) <;>
    norm_num [Real.convergent_succ, Real.convergent_zero, Int.fract]
  have hden := Rat.den_div_eq_of_coprime (a := 7) (b := 10) (by decide) (by decide)
  norm_num at hden
  have : (7 / 10 : ℚ).den = 10 := by exact_mod_cast hden
  omega

-- Integer inputs are already exact, at every index.
example (n : ℕ) : ((-3 : ℝ).convergent n : ℝ) = -3 := by
  norm_cast
  exact Real.convergent_of_int n

-- Negative inputs use the same theorem, without a positivity restriction on x.
example : |(-7 / 10 : ℝ) - ((-7 / 10 : ℝ).convergent 1 : ℝ)| <
    |(-7 / 10 : ℝ) - (-1)| := by
  have hconv : (-7 / 10 : ℝ).convergent 1 = -2 / 3 := by
    norm_num [Real.convergent_succ, Real.convergent_zero, Int.fract]
  simpa only [Int.cast_neg, Int.cast_one, div_one] using
    Real.abs_sub_convergent_lt (-7 / 10 : ℝ) (n := 1) (c := -1) (d := 1)
      (by omega) (by omega) (by have := ((-7 / 10 : ℝ).convergent 1).den_pos; omega)
      (by rw [hconv]; norm_num)

-- For any rational input, the repeated last convergent is exact; the terminal case really occurs.
example (r : ℚ) : ∃ N, ∀ n ≥ N, (of (r : ℝ)).convs n = (r : ℝ) := by
  obtain ⟨N, hN⟩ := (GenContFract.terminates_iff_rat (r : ℝ)).mpr ⟨r, rfl⟩
  exact ⟨N, fun n hn =>
    (GenContFract.of_correctness_of_terminatedAt
      (GenContFract.terminated_stable hn hN)).symm⟩

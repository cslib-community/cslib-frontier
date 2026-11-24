/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.RationalIntegerProgramming
import CslibFrontier.Computability.Complexity.Problems.Copositivity
meta import CslibFrontier.Computability.Complexity.Problems.RationalIntegerProgramming
import Mathlib.Tactic.NormNum

/-! Ordinary-import tests of rational input, integer witnesses and denominator clearing. -/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib.Complexity Turing.MultiTapeTM

-- Both numerator and denominator are binary, with the canonical positive denominator.
example (q : ℚ) : encRat q = encPair encIntBin encNat (q.num, q.den) := rfl
example (P : RationalIntegerProgram) : RationalIntegerProgram.enc P =
    encPair encUnary (encList RationalIntegerProgram.encInequality)
      (P.numVars, P.constraints) := rfl

-- 1/2 x ≤ 3/2 clears to x ≤ 3; the appended row enforces nonnegativity.
#guard (RationalIntegerProgram.clearDenominators ⟨1, [⟨[1/2], 3/2⟩]⟩).constraints ==
  [⟨[2], 6⟩, ⟨[-1], 0⟩]
-- Clear the bound's denominator too; charge/truncate extra columns in exactly the same way.
#guard (RationalIntegerProgram.clearDenominators ⟨0, [⟨[1/2], -1/3⟩]⟩).constraints ==
  [⟨[3], -2⟩]
#guard (RationalIntegerProgram.clearDenominators ⟨2, []⟩).constraints ==
  [⟨[-1, 0], 0⟩, ⟨[0, -1], 0⟩]

example : (⟨1, [⟨[1/2], 3/2⟩]⟩ : RationalIntegerProgram) ∈
    RationalIntegerProgram.Feasible := by
  refine ⟨fun _ => 3, fun _ => by norm_num, ?_⟩
  intro c hc
  simp only [List.mem_singleton] at hc
  subst c
  norm_num [Fin.sum_univ_one]

-- Rational feasibility alone is insufficient: x = 1/2 is not an integer witness.
example : (⟨1, [⟨[1], 1/2⟩, ⟨[-1], -1/2⟩]⟩ : RationalIntegerProgram) ∉
    RationalIntegerProgram.Feasible := by
  rintro ⟨x, _, hx⟩
  have h1 := hx ⟨[1], 1/2⟩ (by simp)
  have h2 := hx ⟨[-1], -1/2⟩ (by simp)
  norm_num [Fin.sum_univ_one] at h1 h2
  have heq : (x 0 : ℚ) = 1/2 := by linarith
  have h : 2 * x 0 = 1 := by exact_mod_cast (show 2 * (x 0 : ℚ) = 1 by linarith)
  omega

-- Unrestricted feasibility of x ≤ -1 does not imply the nonnegative problem.
example : (⟨1, [⟨[1/2], -1/2⟩]⟩ : RationalIntegerProgram) ∉
    RationalIntegerProgram.Feasible := by
  rintro ⟨x, hn, hx⟩
  have h := hx ⟨[1/2], -1/2⟩ (by simp)
  have hn' : (0 : ℚ) ≤ x 0 := by exact_mod_cast hn 0
  norm_num [Fin.sum_univ_one] at h
  linarith

-- Empty dimension does not make an inconsistent constant row satisfiable.
example : (⟨0, [⟨[], -1/3⟩]⟩ : RationalIntegerProgram) ∉
    RationalIntegerProgram.Feasible := by
  rintro ⟨x, _, hx⟩
  have h := hx ⟨[], -1/3⟩ (by simp)
  norm_num at h

example (P : RationalIntegerProgram) (x : Fin P.numVars → ℤ)
    (h : ∀ j, 0 ≤ x j)
    (hc : ∀ c ∈ P.constraints, ∑ j : Fin P.numVars,
      c.coeffs.getD j 0 * (x j : ℚ) ≤ c.rhs) :
    ∀ c ∈ P.clearDenominators.constraints,
      ∑ j : Fin P.numVars, c.coeffs.getD j 0 * x j ≤ c.rhs :=
  (RationalIntegerProgram.satisfies_clearDenominators_iff P x).mpr ⟨h, hc⟩

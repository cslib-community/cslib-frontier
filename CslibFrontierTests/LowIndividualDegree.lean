/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
import Mathlib.Algebra.Field.ZMod

/-! # The two-coordinate low individual degree verifier over three elements -/

set_option linter.privateModule false

open Cslib.PCP.LowIndividualDegree

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def prodVars : MvPolynomial (Fin 2) (ZMod 3) :=
  MvPolynomial.X 0 * MvPolynomial.X 1

/-- The verifier accepts a polynomial of individual degree one and total degree two. -/
example : (game (F := ZMod 3) 1 1).winProb (honest prodVars) (honest prodVars) = 1 := by
  apply winProb_honest
  intro i
  refine (MvPolynomial.degreeOf_mul_le i _ _).trans ?_
  fin_cases i <;> simp [MvPolynomial.degreeOf_X]

/-- The diagonal law includes a singleton line, with its point and line on opposite roles. -/
example (u : Point (ZMod 3) 2) :
    (Question.diagonal (linePoints u 0), Question.point u) ∈
      (diagonalQuestions (F := ZMod 3) 1).support := by
  refine mem_diagonalQuestions_support.mpr ⟨u, 0, 0, true, ?_⟩
  simp

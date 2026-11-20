/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.OneCoordinate
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod

/-! # Extraction from the one-coordinate honest tensor strategy -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum
open Cslib.Probability.PMF (uniformOfFintype)
open scoped MatrixOrder ComplexOrder

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def identityPoly : MvPolynomial (Fin 1) (ZMod 3) := MvPolynomial.X 0

private noncomputable def strategy :
    QuantumStrategy (Question (ZMod 3) 1) (Question (ZMod 3) 1)
      (Answer (ZMod 3) 1) (Answer (ZMod 3) 1) (Fin 1) (Fin 1) := by
  classical
  exact QuantumStrategy.ofDeterministic (honest identityPoly) (honest identityPoly)

/-- Evaluating the extracted polynomial measurements attains perfect agreement for this
nonconstant honest strategy. -/
example :
    let S := strategy.toCommuting
    ∃ (P R : Measurement (PolynomialFunction (ZMod 3) 1)
        (Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)),
      1 ≤ ∑ u, (uniformOfFintype (Point (ZMod 3) 1) u).toReal *
        ((Measurement.agreement S.state ((S.alice (.point u)).map decodePoint)
            (R.map fun f => f.eval u) +
          Measurement.agreement S.state (P.map fun f => f.eval u)
            ((S.bob (.point u)).map decodePoint)) / 2) := by
  intro S
  classical
  obtain ⟨P, R, _, _, h⟩ := exists_polynomial_measurements_one S 1
  have he : (branchGame (F := ZMod 3) 0 1 .axis).commutingWinProb S = 1 := by
    dsimp only [S]
    rw [TwoProverGame.commutingWinProb_toCommuting]
    unfold strategy
    rw [TwoProverGame.quantumWinProb_ofDeterministic]
    exact winProb_branch_honest identityPoly (by intro i; fin_cases i; simp [identityPoly]) .axis
  exact ⟨P, R, he ▸ h⟩

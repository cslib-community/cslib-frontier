/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.InductionBase
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.OneCoordinate
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod

/-! # Extraction from the one-coordinate honest tensor strategy -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum
open Cslib.Probability.PMF (uniformOfFintype)
open scoped BigOperators MatrixOrder ComplexOrder

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def identityPoly : MvPolynomial (Fin 1) (ZMod 3) := MvPolynomial.X 0

private noncomputable def strategy :
    QuantumStrategy (Question (ZMod 3) 1) (Question (ZMod 3) 1)
      (Answer (ZMod 3) 1) (Answer (ZMod 3) 1) (Fin 1) (Fin 1) := by
  classical
  exact QuantumStrategy.ofDeterministic (honest identityPoly) (honest identityPoly)

private theorem strategy_axis_score :
  (branchGame (F := ZMod 3) 0 1 .axis).commutingWinProb strategy.toCommuting = 1 := by
  classical
  rw [TwoProverGame.commutingWinProb_toCommuting]
  unfold strategy
  rw [TwoProverGame.quantumWinProb_ofDeterministic]
  exact winProb_branch_honest identityPoly (by intro i; fin_cases i; simp [identityPoly]) .axis

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
  exact ⟨P, R, strategy_axis_score ▸ h⟩

/-- The same honest strategy witnesses perfect matching mass in the local induction format. -/
example :
    ∃ G : POVM (Option (BoundedPolynomial (ZMod 3) 1 1)) (Fin 1),
      1 ≤ 𝔼 u : Point (ZMod 3) 1, ∑ g : BoundedPolynomial (ZMod 3) 1 1,
        (strategy.toCommuting.state
          ((QuantumStrategy.rightMeasurement (ι := Fin 1) G).effect (some g) *
            (decodedPoint strategy.toCommuting.alice u).effect
              (MvPolynomial.eval u g.val))).re := by
  have hs (a b : Fin 1) : strategy.state.ofLp (a, b) = strategy.state.ofLp (b, a) := by
    rw [Subsingleton.elim a b]
  obtain ⟨G, hG⟩ := exists_one_coordinate_polynomial_POVM strategy rfl hs 1
  exact ⟨G, strategy_axis_score ▸ hG⟩

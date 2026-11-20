/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.InductionBase
import Mathlib.Algebra.Field.ZMod

/-! # Degree-zero extraction from an honest two-coordinate strategy -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum
open scoped BigOperators MatrixOrder ComplexOrder

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def constantPoly : MvPolynomial (Fin 2) (ZMod 3) := MvPolynomial.C 2

private noncomputable def strategy :
    QuantumStrategy (Question (ZMod 3) 2) (Question (ZMod 3) 2)
      (Answer (ZMod 3) 2) (Answer (ZMod 3) 2) (Fin 1) (Fin 1) := by
  classical
  exact QuantumStrategy.ofDeterministic (honest constantPoly) (honest constantPoly)

private theorem strategy_point_projective (u : Point (ZMod 3) 2) :
    (strategy.alice (.point u)).toMeasurement.IsProjective := by
  classical
  intro a
  unfold strategy
  simp only [QuantumStrategy.ofDeterministic, POVM.toMeasurement_effect, POVM.const]
  split_ifs <;> simp

private theorem strategy_branch_score (b : Branch) :
    (branchGame (F := ZMod 3) 1 0 b).commutingWinProb strategy.toCommuting = 1 := by
  classical
  rw [TwoProverGame.commutingWinProb_toCommuting]
  unfold strategy
  rw [TwoProverGame.quantumWinProb_ofDeterministic]
  exact winProb_branch_honest constantPoly
    (fun i => (MvPolynomial.degreeOf_C (2 : ZMod 3) i).le) b

/-- The constant-polynomial strategy has zero axis and consistency loss, and the
extracted local measurement matches the honest point answers with mass at least one. -/
example :
    ∃ G : POVM (Option (BoundedPolynomial (ZMod 3) 2 0)) (Fin 1),
      1 ≤ 𝔼 u : Point (ZMod 3) 2, ∑ g : BoundedPolynomial (ZMod 3) 2 0,
        (strategy.toCommuting.state
          ((QuantumStrategy.rightMeasurement (ι := Fin 1) G).effect (some g) *
            (decodedPoint strategy.toCommuting.alice u).effect
              (MvPolynomial.eval u g.val))).re := by
  have hBob : strategy.bob = strategy.alice := rfl
  obtain ⟨G, hG⟩ :=
    exists_degree_zero_polynomial_POVM strategy strategy_point_projective (by
      rw [hBob]
      exact strategy_point_projective)
  refine ⟨G, ?_⟩
  have hAxis := strategy_branch_score .axis
  have hCons := strategy_branch_score .consistency
  rw [hAxis, hCons] at hG
  simpa only [sub_self, mul_zero, add_zero, sub_zero] using hG

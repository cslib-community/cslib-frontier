/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.InductionBase
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.ProjectiveSoundness
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

private theorem strategy_projective (q : Question (ZMod 3) 2) :
    (strategy.alice q).toMeasurement.IsProjective := by
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
    exists_degree_zero_polynomial_POVM strategy (fun u => strategy_projective (.point u)) (by
      rw [hBob]
      exact fun u => strategy_projective (.point u))
  refine ⟨G, ?_⟩
  have hAxis := strategy_branch_score .axis
  have hCons := strategy_branch_score .consistency
  rw [hAxis, hCons] at hG
  simpa only [sub_self, mul_zero, add_zero, sub_zero] using hG

/-- The soundness theorem on the honest two-coordinate strategy supplies two
projective measurements that agree with probability at least one half. -/
example :
    ∃ (P Q : POVM (BoundedPolynomial (ZMod 3) 2 0) (Fin 1)),
      P.toMeasurement.IsProjective ∧ Q.toMeasurement.IsProjective ∧
      1 / 2 ≤ Measurement.agreement strategy.toCommuting.state
        (QuantumStrategy.leftMeasurement (κ := Fin 1) P)
        (QuantumStrategy.rightMeasurement (ι := Fin 1) Q) := by
  have hscore : (game (F := ZMod 3) 1 0).quantumWinProb strategy = 1 := by
    rw [← TwoProverGame.commutingWinProb_toCommuting (game 1 0)]
    change (game (F := ZMod 3) 1 0).answersWinProb strategy.toCommuting.answers = 1
    rw [answersWinProb_game]
    change ((branchGame (F := ZMod 3) 1 0 .axis).commutingWinProb strategy.toCommuting +
      (branchGame (F := ZMod 3) 1 0 .consistency).commutingWinProb strategy.toCommuting +
      (branchGame (F := ZMod 3) 1 0 .diagonal).commutingWinProb strategy.toCommuting) / 3 = 1
    rw [strategy_branch_score .axis, strategy_branch_score .consistency,
      strategy_branch_score .diagonal]
    norm_num
  have hBob : strategy.bob = strategy.alice := rfl
  obtain ⟨P, Q, hP, hQ, _, _, hpair⟩ :=
    exists_projective_polynomial_POVMs_of_winProb (k := 10 ^ 30) (n := 1) (d := 0)
      (by simp) strategy strategy_projective (by rw [hBob]; exact strategy_projective)
  rw [hscore] at hpair
  conv_rhs at hpair =>
    norm_num [dimensionInductionError, inductionLossTerm, Real.zero_rpow,
      -Real.sqrt_mul, -Real.sqrt_mul']
  let x : ℝ := 3125000000000000000000000
  let σ := 320000 * (4 * Real.exp (-x))
  let ζ := σ + Real.sqrt (4 * σ)
  change 1 - Measurement.agreement strategy.toCommuting.state
    (QuantumStrategy.leftMeasurement (κ := Fin 1) P)
    (QuantumStrategy.rightMeasurement (ι := Fin 1) Q) ≤ ζ + 2 * Real.sqrt (18 * ζ) at hpair
  have he : Real.exp (-x) ≤ 1 / (x + 1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by dsimp [x]; positivity) (Real.add_one_le_exp x)
  have hσ : σ ≤ 1 / 1000000000000 := by
    calc
      _ ≤ 320000 * (4 * (1 / (x + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by norm_num)) (by norm_num)
      _ ≤ _ := by norm_num [x]
  have hroot : Real.sqrt (4 * σ) ≤ 1 / 250000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith only [hσ]
  have hζ : ζ ≤ 1 / 200000 := by
    dsimp only [ζ]
    linarith only [hσ, hroot]
  have hroot' : Real.sqrt (18 * ζ) ≤ 1 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith only [hζ]
  exact ⟨P, Q, hP, hQ, by linarith only [hpair, hζ, hroot']⟩

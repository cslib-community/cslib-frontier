/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PointCommutativity
import Mathlib.Algebra.Field.ZMod

/-! # The two-coordinate low individual degree verifier over three elements -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum
open scoped MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator Real

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private noncomputable def prodVars : MvPolynomial (Fin 2) (ZMod 3) :=
  MvPolynomial.X 0 * MvPolynomial.X 1

private theorem prodVars_degree (i : Fin 2) : prodVars.degreeOf i ≤ 1 := by
  refine (MvPolynomial.degreeOf_mul_le i _ _).trans ?_
  fin_cases i <;> simp [MvPolynomial.degreeOf_X]

/-- The verifier accepts a polynomial of individual degree one and total degree two. -/
example : (game (F := ZMod 3) 1 1).winProb (honest prodVars) (honest prodVars) = 1 :=
  winProb_honest prodVars prodVars_degree

/-- The diagonal law includes a singleton line, with its point and line on opposite roles. -/
example (u : Point (ZMod 3) 2) :
    (Question.diagonal (linePoints u 0), Question.point u) ∈
      (diagonalQuestions (F := ZMod 3) 1).support := by
  refine mem_diagonalQuestions_support.mpr ⟨u, 0, 0, true, ?_⟩
  simp


private noncomputable def honestProductStrategy :
    QuantumStrategy (Question (ZMod 3) 2) (Question (ZMod 3) 2)
      (Answer (ZMod 3) 2) (Answer (ZMod 3) 2) (Fin 1) (Fin 1) := by
  classical
  exact QuantumStrategy.ofDeterministic (honest prodVars) (honest prodVars)

private theorem honestProductBranchScore (b : Branch) :
    (branchGame (F := ZMod 3) 1 1 b).commutingWinProb honestProductStrategy.toCommuting = 1 := by
  rw [TwoProverGame.commutingWinProb_toCommuting]
  unfold honestProductStrategy
  rw [TwoProverGame.quantumWinProb_ofDeterministic]
  exact winProb_branch_honest prodVars prodVars_degree b

/-- For the honest product polynomial on two coordinates, the decoded vertical
measurements and the endpoint measurements have zero state distance. -/
example : let S := honestProductStrategy.toCommuting
    (𝔼 u : Point (ZMod 3) 1, 𝔼 t : ZMod 3, ∑ a, S.state.norm
      ((decodedPoint S.bob (Fin.snoc u t)).effect a -
        ((decodedVertical S.bob 1 u).map (fun f => f.value t)).effect a) ^ 2) ≤ 0 := by
  intro S
  classical
  simpa only [S, honestProductBranchScore, sub_self, mul_zero, add_zero] using
    bob_vertical_stateDist_le S 1

/-- Conditioning on any prefix with Alice in the point role preserves perfect
diagonal acceptance of the honest product polynomial. -/
example (i : Fin 2) :
    (𝔼 u : Point (ZMod 3) 2, 𝔼 v : Fin (i.val + 1) → ZMod 3,
      (1 - acceptScore honestProductStrategy.toCommuting 1
        (.point u) (.diagonal (linePoints u (prefixDirection i v))))) ≤ 0 := by
  simpa only [honestProductBranchScore, sub_self, mul_zero] using
    diagonalPointLossAt_le 1 1 honestProductStrategy.toCommuting i

/-- The diagonal commutator estimate gives zero for the honest product-polynomial strategy. -/
example : let S := honestProductStrategy.toCommuting
    (𝔼 u : Point (ZMod 3) 2, 𝔼 v : Point (ZMod 3) 2,
      Measurement.pairCommutatorDefect S.state (decodedPoint S.alice u) (decodedPoint S.alice v))
      ≤ 0 := by
  intro S
  classical
  have hPoint (u : Point (ZMod 3) 2) : (S.alice (.point u)).IsProjective := by
    intro a
    simp only [S, honestProductStrategy, QuantumStrategy.toCommuting,
      QuantumStrategy.ofDeterministic, QuantumStrategy.leftMeasurement, POVM.const]
    split_ifs <;> simp
  have hLine (L : Finset (Point (ZMod 3) 2)) : (S.bob (.diagonal L)).IsProjective := by
    intro a
    simp only [S, honestProductStrategy, QuantumStrategy.toCommuting,
      QuantumStrategy.ofDeterministic, QuantumStrategy.rightMeasurement, POVM.const]
    split_ifs <;> simp
  have hscore : (branchGame (F := ZMod 3) 1 1 .diagonal).commutingWinProb S = 1 :=
    honestProductBranchScore .diagonal
  have h := decodedPoint_pairCommutatorDefect_le (F := ZMod 3) (n := 1) S hPoint hLine 1
  rwa [hscore, sub_self, mul_zero] at h

private def shiftedSuccess (t : ZMod 3) (a : Answer (ZMod 3) 2) : Option (ZMod 3) :=
  if t = 0 then none else some (decodePoint a + 1)

/-- Compare the actual successful mismatch events when the first decoder may fail. -/
example : let S := honestProductStrategy.toCommuting
    (𝔼 u : Point (ZMod 3) 1, 𝔼 t : ZMod 3,
      ((S.answers (.point (Fin.snoc u t)) (.axis (verticalLine u))).toOuterMeasure
        {ab | ∃ a, shiftedSuccess t ab.1 = some a ∧
          a ≠ (decodeVertical 1 u ab.2).value t}).toReal) ≤
      (𝔼 u : Point (ZMod 3) 1, 𝔼 t : ZMod 3,
        ((S.answers (.point (Fin.snoc u t)) (.point (Fin.snoc u t))).toOuterMeasure
          {ab | ∃ a, shiftedSuccess t ab.1 = some a ∧ a ≠ decodePoint ab.2}).toReal) := by
  intro S
  classical
  let P (u : Point (ZMod 3) 1) (t : ZMod 3) :=
    (S.alice (.point (Fin.snoc u t))).map (shiftedSuccess t)
  have h := successfulMismatch_vertical_le (F := ZMod 3) (n := 1) S 1 P
  simp only [P, decodedPoint, decodedVertical, Measurement.map_map, Function.comp_apply,
    CommutingStrategy.successfulMismatch_map_map_eq_event] at h
  simpa only [S, honestProductBranchScore, sub_self, mul_zero, add_zero, Real.sqrt_zero] using h

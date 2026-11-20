/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.RestrictedStrategy
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Roots

/-! # Restricting low-individual-degree strategies to a slice

The degree-cap regression distinguishes the native and fixed diagonal bounds. The strategy
client checks that restricting honest projective measurements preserves the state and
projectivity and satisfies the fixed-cap loss bound.
-/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum Polynomial
open Cslib.Probability.PMF (uniformOfFintype)
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev F := ZMod 3
private abbrev L := linePoints (0 : Point F 1) (1 : Point F 1)

private def square (u : L) : F := (u.val 0) ^ 2

private theorem degree_two : LineHasDegree square 2 := by
  refine ⟨0, 1, rfl, X ^ 2, by simp, fun t => ?_⟩
  simp [square, Pi.smul_apply, smul_eq_mul]

private theorem not_degree_one : ¬ LineHasDegree square 1 := by
  intro h
  obtain ⟨p, hp, he⟩ := h.exists_polynomial
  have hEval (t : F) : p.eval t = ((X : Polynomial F) ^ 2).eval t := by
    simpa [square, Pi.smul_apply, smul_eq_mul] using (he t).symm
  have hEq : p = (X : Polynomial F) ^ 2 := by
    apply eq_of_natDegree_lt_card_of_eval_eq p _ Function.injective_id hEval
    rw [natDegree_X_pow, ZMod.card]
    omega
  rw [hEq, natDegree_X_pow] at hp
  omega

private theorem quadratic_accepted_on_lifted_line :
    lineAgrees 2 (appendLine (0 : F) L) (appendPoint 0 0) (appendLineAnswer 0 ⟨L, square⟩) 0 := by
  apply (lineAgrees_appendLineAnswer_iff 0 L 0 2 ⟨L, square⟩ 0).mpr
  refine ⟨rfl, degree_two, ?_⟩
  have hzero : (0 : Point F 1) ∈ L := by
    simpa using mem_linePoints (0 : Point F 1) (1 : Point F 1) (0 : F)
  exact ⟨hzero, by simp [square]⟩

/-- For `d = 1` the two-coordinate cap is two and the one-coordinate cap is one.
The larger diagonal predicate accepts the quadratic answer, but the smaller one rejects it. -/
example :
    accepts 1 (.diagonal (appendLine (0 : F) L)) (.point (appendPoint 0 0))
        (.inr (appendLineAnswer 0 ⟨L, square⟩)) (.inl 0) ∧
      ¬ accepts 1 (.diagonal L) (.point 0) (.inr ⟨L, square⟩) (.inl 0) := by
  exact ⟨quadratic_accepted_on_lifted_line, fun h => not_degree_one h.2.1⟩

/-- Holding the diagonal cap at two preserves acceptance of the same quadratic answer,
including when the point question goes to the first player. -/
example :
    acceptsWithDiagonalCap 1 2 (.point (0 : Point F 1)) (.diagonal L)
      (restrictAnswer (0 : F) (.inl 0))
      (restrictAnswer 0 (.inr (appendLineAnswer 0 ⟨L, square⟩))) := by
  exact acceptsWithDiagonalCap_restrict 0 1 2 (.point 0) (.diagonal L) _ _
    quadratic_accepted_on_lifted_line

private abbrev Observables := Matrix (Fin 1) (Fin 1) ℂ

private noncomputable def honestMeasurement (q : Question F 2) :
    Measurement (Answer F 2) Observables :=
  Measurement.const (honest (MvPolynomial.X 0) q)

private noncomputable def honestStrategy :
    CommutingStrategy (Question F 2) (Question F 2) (Answer F 2) (Answer F 2) Observables where
  state := AlgState.vector (EuclideanSpace.single 0 1) (by simp)
  alice := honestMeasurement
  bob := honestMeasurement
  commute x y a b := by
    unfold honestMeasurement
    simp only [Measurement.const]
    split_ifs <;> simp

private theorem honestMeasurement_isProjective (q : Question F 2) :
    (honestMeasurement q).IsProjective :=
  Measurement.isProjective_const _

/-- On each slice the restricted strategy for the first coordinate keeps its state and
projective measurements. Its mean diagonal loss obeys the fixed-cap bound. -/
example :
    (∀ x : F, (restrictStrategy x honestStrategy).state = honestStrategy.state ∧
      (∀ q, ((restrictStrategy x honestStrategy).alice q).IsProjective) ∧
      (∀ q, ((restrictStrategy x honestStrategy).bob q).IsProjective)) ∧
    (∑ x : F, (uniformOfFintype F x).toReal *
        (1 - (branchGameWithDiagonalCap 0 1 2 .diagonal).commutingWinProb
          (restrictStrategy x honestStrategy))) ≤
      2 * (1 - (branchGameWithDiagonalCap 1 1 2 .diagonal).commutingWinProb honestStrategy) := by
  have hA (q : Question F 2) : (honestStrategy.alice q).IsProjective :=
    honestMeasurement_isProjective q
  have hB (q : Question F 2) : (honestStrategy.bob q).IsProjective :=
    honestMeasurement_isProjective q
  refine ⟨?_, ?_⟩
  · intro x
    refine ⟨restrictStrategy_state (m := 1) x honestStrategy, ?_⟩
    have h := restrictStrategy_isProjective (m := 1) x honestStrategy hA hB
    exact h
  · simpa using commutingBranchLoss_restrict_le 0 1 2 .diagonal honestStrategy

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.ConsistencyTest
import CslibFrontier.Foundations.Data.BitString.OddPairs
import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Foundations.Quantum.Algebra.Measurement
import CslibFrontier.Foundations.Quantum.POVM
import CslibFrontier.Probability.PMF

/-! # Special-question consistency checks

A deterministic strategy on one-bit questions agrees on the first bit but disagrees on the
second. The corresponding winning probabilities are one and zero, and the squared distances
are zero and four. The rejecting round attains the factor four in both consistency bounds.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ConsistencyTest

open Cslib Cslib.PCP Cslib.Quantum
open scoped BigOperators ComplexOrder MatrixOrder

variable (φ : AlgState (Matrix (Fin 1) (Fin 1) ℂ))

private noncomputable def strategy :
    CommutingStrategy (PauliConsistencyQuestion Unit) (PauliConsistencyQuestion Unit)
      (Bool × Bool) Bool (Matrix (Fin 1) (Fin 1) ℂ) where
  state := φ
  alice _ := Measurement.const (false, true)
  bob _ := Measurement.const false
  commute _ _ a b := by
    simp only [Measurement.const]
    split_ifs <;> simp [Commute, SemiconjBy]

private theorem bitAgreementWinProb {R : Type} [Finite R] (seed : PMF R)
    (question : R → PauliConsistencyQuestion Unit) (basis : Bool)
    (hbasis : ∀ r, (question r).basis = basis) :
    (SeededGame.bitAgreement seed (fun r => (question r, question r))
      (fun r => (question r).checkedBit) (fun _ => id)).commutingWinProb (strategy φ) =
        if basis then 0 else 1 := by
  let := Fintype.ofFinite R
  rw [SeededGame.commutingWinProb_eq_sum]
  cases basis
  · simp only [Bool.false_eq_true, ite_false]
    rw [← Probability.PMF.sum_toReal seed]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [SeededGame.bitAgreement, PauliConsistencyQuestion.checkedBit, hbasis,
      CommutingStrategy.prob, strategy, Measurement.const, Fintype.sum_prod_type, φ.map_one]
  · simp [SeededGame.bitAgreement, PauliConsistencyQuestion.checkedBit, hbasis,
      CommutingStrategy.prob, strategy, Measurement.const, Fintype.sum_prod_type]

private theorem specialWinProb (basis : Bool) :
    (pauliSpecialQuestionTest Unit basis).commutingWinProb (strategy φ) =
      if basis then 0 else 1 := by
  let := BitString.oddPairs_nonempty (ι := Unit)
  exact bitAgreementWinProb φ (Probability.PMF.uniformOfFintype ↥(BitString.oddPairs Unit))
    (fun p => ⟨p.val.fst, p.val.snd, basis⟩) basis (fun _ => rfl)

private noncomputable def distanceSq (q : PauliConsistencyQuestion Unit) : ℝ :=
  φ.norm ((((strategy φ).alice q).map q.checkedBit).observable -
    ((strategy φ).bob q).observable) ^ 2

private theorem distanceSq_eq (q : PauliConsistencyQuestion Unit) :
    distanceSq φ q = if q.basis then 4 else 0 := by
  have hAlice : (((strategy φ).alice q).map q.checkedBit).observable =
      if q.basis then -1 else 1 := by
    cases h : q.basis <;>
      simp [strategy, PauliConsistencyQuestion.checkedBit, Measurement.observable_map,
        Measurement.const, h]
  have hBob : ((strategy φ).bob q).observable = 1 := by
    simp [strategy, Measurement.observable, Measurement.const]
  rw [distanceSq, hAlice, hBob]
  cases q.basis
  · simp
  · change φ.norm (-1 - 1) ^ 2 = 4
    rw [show (-1 : Matrix (Fin 1) (Fin 1) ℂ) - 1 = (-(2 : ℂ)) • 1 by
      simp [two_smul, sub_eq_add_neg]]
    norm_num [AlgState.norm_smul]

/-- The conditional bound attains zero on agreeing rounds and four on disagreeing rounds. -/
example (basis : Bool) :
    (𝔼 p : ↥(BitString.oddPairs Unit), distanceSq φ ⟨p.val.fst, p.val.snd, basis⟩) =
      if basis then 4 else 0 := by
  let := BitString.oddPairs_nonempty (ι := Unit)
  apply le_antisymm
  · have h := expect_norm_sub_sq_le_of_pauliSpecialQuestionTest basis (strategy φ)
    rw [specialWinProb φ basis] at h
    cases basis <;> simpa [distanceSq, strategy] using h
  · simp only [distanceSq_eq]
    exact (Fintype.expect_const (ι := ↥(BitString.oddPairs Unit))
      (if basis then (4 : ℝ) else 0)).ge

/-- A deterministic seeded game saturates the general agreement bound. -/
example :
    distanceSq φ ⟨fun _ => true, fun _ => true, true⟩ = 4 := by
  let q : PauliConsistencyQuestion Unit := ⟨fun _ => true, fun _ => true, true⟩
  change distanceSq φ q = 4
  apply le_antisymm
  · have h := SeededGame.sum_norm_sub_sq_le_of_bitAgreement (PMF.pure ())
      (fun _ => (q, q)) (fun _ => q.checkedBit) (fun _ => id) (strategy φ)
    rw [bitAgreementWinProb φ (PMF.pure ()) (fun _ => q) true (fun _ => rfl)] at h
    have hmap : (((strategy φ).bob q).map id).observable = ((strategy φ).bob q).observable := by
      rw [Measurement.observable_map, Measurement.observable]
      simp [strategy, Measurement.const]
    simp only [hmap] at h
    simpa [distanceSq, strategy] using h
  · simp [distanceSq_eq, q]

end CslibFrontierTests.ConsistencyTest

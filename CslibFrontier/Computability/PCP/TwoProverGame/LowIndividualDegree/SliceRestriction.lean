/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.RestrictedStrategy
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerticalAxis
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Restriction to a coordinate slice

Fixing the final coordinate embeds a lower-dimensional verifier question in
the original space. Restriction preserves accepted answers on the included questions.
The diagonal cutoff stays fixed as the dimension decreases. This is the restriction estimate
of [JNVWY2020LowIndividualDegree, Lemma 6.6], with the cutoff explicit.

## Main definitions

* `Cslib.PCP.LowIndividualDegree.restrictSliceTensor` restricts a tensor strategy
  while retaining the same state and preserving projectivity.

## Main results

* `Cslib.PCP.LowIndividualDegree.average_slice_axis_loss_le`,
  `Cslib.PCP.LowIndividualDegree.average_slice_consistency_loss_le`, and
  `Cslib.PCP.LowIndividualDegree.average_slice_diagonal_loss_le` bound the
  expected branch losses of the restricted strategy.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Probability.PMF Cslib.Quantum Finset
open scoped BigOperators

variable {F A : Type*} {m : ℕ}

variable [Field F] [Fintype F] [DecidableEq F]
  [Ring A] [PartialOrder A] [IsOrderedAddMonoid A] [Algebra ℂ A]
  [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

/-- Restricting to a uniform last coordinate costs at most the ratio of the
ambient and slice dimensions in the mean axis rejection probability. -/
theorem average_slice_axis_loss_le {n : ℕ}
    (S : CommutingStrategy (Question F (n + 2)) (Question F (n + 2))
      (Answer F (n + 2)) (Answer F (n + 2)) A) (d D : ℕ) :
    (n + 1 : ℝ) *
      (𝔼 t : F, (1 - (branchGameWithDiagonalCap (F := F) n d D .axis).commutingWinProb
      (restrictStrategy t S))) ≤
      (n + 2 : ℝ) *
        (1 - (branchGameWithDiagonalCap (F := F) (n + 1) d D .axis).commutingWinProb S) := by
  rw [← uniform_sum_eq_expect]
  simpa using
    commutingBranchLoss_restrict_le n d D .axis S

/-- A shared point sampled in a uniform slice is a uniform ambient point. -/
theorem average_slice_consistency_loss_le {n : ℕ}
    (S : CommutingStrategy (Question F (n + 2)) (Question F (n + 2))
      (Answer F (n + 2)) (Answer F (n + 2)) A) (d D : ℕ) :
    (𝔼 t : F, (1 - (branchGameWithDiagonalCap (F := F) n d D .consistency).commutingWinProb
        (restrictStrategy t S))) ≤
      1 - (branchGameWithDiagonalCap (F := F) (n + 1) d D .consistency).commutingWinProb S := by
  rw [← uniform_sum_eq_expect]
  simpa using
    commutingBranchLoss_restrict_le n d D .consistency S

/-- Restricting to a uniform slice discards only the longest diagonal prefix.
The diagonal degree cutoff is held fixed on both sides of the bound. -/
theorem average_slice_diagonal_loss_le {n : ℕ}
    (S : CommutingStrategy (Question F (n + 2)) (Question F (n + 2))
      (Answer F (n + 2)) (Answer F (n + 2)) A) (d D : ℕ) :
    (n + 1 : ℝ) *
      (𝔼 t : F, (1 - (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb
      (restrictStrategy t S))) ≤
      (n + 2 : ℝ) *
        (1 - (branchGameWithDiagonalCap (F := F) (n + 1) d D .diagonal).commutingWinProb S) := by
  rw [← uniform_sum_eq_expect]
  simpa using
    commutingBranchLoss_restrict_le n d D .diagonal S

omit [Fintype F] [DecidableEq F] in
private theorem decodePoint_comp_restrictAnswer (t : F) :
    decodePoint ∘ (restrictAnswer (m := m) t) = decodePoint := by
  funext a
  cases a with
  | inl a => simp
  | inr a =>
    obtain ⟨b, hb⟩ := restrictAnswer_inr_exists (m := m) t a
    simp only [Function.comp_apply, hb, decodePoint_inr]

omit [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A] in
/-- The decoded point measurement of a slice is the ambient point measurement
at the appended coordinate. -/
theorem decodedPoint_restrictSlice
    (S : CommutingStrategy (Question F (m + 2)) (Question F (m + 2))
      (Answer F (m + 2)) (Answer F (m + 2)) A) (t : F) (u : Point F (m + 1)) :
    decodedPoint (restrictStrategy t S).alice u = decodedPoint S.alice (Fin.snoc u t) := by
  classical
  rw [decodedPoint, decodedPoint, restrictStrategy_alice]
  change ((S.alice (.point (appendPoint t u))).map (restrictAnswer t)).map decodePoint =
    (S.alice (.point (Fin.snoc u t))).map decodePoint
  rw [Measurement.map_map, decodePoint_comp_restrictAnswer, appendPoint_apply]

section Tensor

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private noncomputable def restrictAnswerPOVM
    (M : POVM (Answer F (m + 1)) ι) (t : F) : POVM (Answer F m) ι := by
  classical
  exact (M.toMeasurement.map (restrictAnswer t)).toPOVM

/-- Restrict a finite tensor strategy while retaining its local spaces and shared state. -/
noncomputable def restrictSliceTensor
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F) :
    QuantumStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) ι κ where
  state := S.state
  norm_state := S.norm_state
  alice q := restrictAnswerPOVM (S.alice (appendQuestion t q)) t
  bob q := restrictAnswerPOVM (S.bob (appendQuestion t q)) t

@[simp] theorem restrictSliceTensor_state
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F) :
    (restrictSliceTensor S t).state = S.state := by
  unfold restrictSliceTensor
  rfl

/-- Equal local measurements remain equal upon restriction. -/
theorem restrictSliceTensor_bob_eq_alice
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι ι) (t : F) (h : S.bob = S.alice) :
    (restrictSliceTensor S t).bob = (restrictSliceTensor S t).alice := by
  unfold restrictSliceTensor
  rw [h]

/-- The restricted strategy uses projective measurements when the original does. -/
theorem restrictSliceTensor_alice_isProjective
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F)
    (h : ∀ q, ((S.alice q).toMeasurement).IsProjective) (q : Question F m) :
    (((restrictSliceTensor S t).alice q).toMeasurement).IsProjective := by
  classical
  unfold restrictSliceTensor restrictAnswerPOVM
  intro a
  simpa only [POVM.toMeasurement_effect, Measurement.toPOVM_effect] using
    ((h (appendQuestion t q)).map (restrictAnswer t)) a

/-- The tensor and commuting restrictions use the same bipartite effects. -/
theorem restrictSliceTensor_toCommuting
    (S : QuantumStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) ι κ) (t : F) :
    (restrictSliceTensor S t).toCommuting = restrictStrategy t S.toCommuting := by
  classical
  apply CommutingStrategy.ext
  · rw [restrictStrategy_state]
    unfold QuantumStrategy.toCommuting restrictSliceTensor
    rfl
  · funext q
    rw [restrictStrategy_alice]
    unfold QuantumStrategy.toCommuting restrictSliceTensor
    apply Measurement.ext
    intro a
    change kroneckerOne ((restrictAnswerPOVM (S.alice (appendQuestion t q)) t).effect a) =
      ((QuantumStrategy.leftMeasurement (κ := κ) (S.alice (appendQuestion t q))).map
        (restrictAnswer t)).effect a
    unfold restrictAnswerPOVM
    simp only [Measurement.toPOVM_effect, Measurement.map_effect, map_sum,
      POVM.toMeasurement_effect]
    rfl
  · funext q
    rw [restrictStrategy_bob]
    unfold QuantumStrategy.toCommuting restrictSliceTensor
    apply Measurement.ext
    intro a
    change oneKronecker ((restrictAnswerPOVM (S.bob (appendQuestion t q)) t).effect a) =
      ((QuantumStrategy.rightMeasurement (ι := ι) (S.bob (appendQuestion t q))).map
        (restrictAnswer t)).effect a
    unfold restrictAnswerPOVM
    simp only [Measurement.toPOVM_effect, Measurement.map_effect, map_sum,
      POVM.toMeasurement_effect]
    rfl

end Tensor

end Cslib.PCP.LowIndividualDegree

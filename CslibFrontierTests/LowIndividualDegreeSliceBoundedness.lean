/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SliceCommutativity
import CslibFrontier.Foundations.Quantum.Algebra.OutcomeCommutator
import CslibFrontierTests.QubitMeasurementFixture
import Mathlib.Algebra.Field.ZMod

/-! # Evaluated slice failure and commutation estimates -/

set_option linter.privateModule false

open Cslib.PCP Cslib.PCP.LowIndividualDegree Cslib.Quantum Matrix Finset
open CslibFrontierTests.QubitMeasurementFixture
open scoped BigOperators Real MatrixOrder Matrix.Norms.L2Operator

namespace CslibFrontierTests.LowIndividualDegreeSliceBoundedness

private abbrev F := ZMod 2

private noncomputable def zeroSlice : BoundedPolynomial F 0 0 := ⟨0, fun i => Fin.elim0 i⟩

private noncomputable def P : Measurement (Option (BoundedPolynomial F 0 0)) Mat := by
  classical
  exact (binary diagonalProjection diagonalProjection_star diagonalProjection_sq).map
    (fun b => if b then some zeroSlice else none)

private noncomputable def N : Measurement (Option Unit) Mat :=
  (binary uniformProjection uniformProjection_star uniformProjection_sq).map
    (fun b => if b then some () else none)

private noncomputable def B (_ : Point F 0) : Measurement F Mat := Measurement.const 0

private theorem commute_const_effect {α : Type*} [Fintype α] [DecidableEq α]
    (e : Mat) (a b : α) : Commute e ((Measurement.const a : Measurement α Mat).effect b) := by
  simp only [Measurement.const]
  split_ifs
  · exact Commute.one_right _
  · exact Commute.zero_right _

private noncomputable def failureTerm : ℝ :=
  𝔼 u : Point F 0, ∑ a : Unit, ∑ b : F,
    (φ (N.effect (some a) * (evaluatePolynomialMeasurement P u).effect (some b) *
      N.effect (some a) * P.effect none * (B u).effect b)).re

private theorem failureTerm_bound : |failureTerm| ≤ √((φ (P.effect none * 1)).re) := by
  classical
  exact abs_average_evaluated_sandwich_failure_le φ P N
    ((binary_projective _ _ _).map _) ((binary_projective _ _ _).map _)
    B 1 zero_le_one (fun g => (averagePolynomialPointEffect_mem_Icc B g).2)
    (fun _ _ b => commute_const_effect _ 0 b)
    (fun _ _ b => commute_const_effect _ 0 b)
    (fun _ => Commute.one_right _) (fun _ => Commute.one_right _)

/-- The example has a genuine nonzero failure contribution and the public bound applies. -/
example : failureTerm = 1 / 4 ∧ |failureTerm| ≤ √((φ (P.effect none * 1)).re) := by
  refine ⟨?_, failureTerm_bound⟩
  classical
  have hP (u : Point F 0) :
      (evaluatePolynomialMeasurement P u).effect (some 0) = diagonalProjection := by
    simp [evaluatePolynomialMeasurement, P, Measurement.map_map, Measurement.map_effect,
      binary, sum_filter, zeroSlice]
  have hPnone : P.effect none = 1 - diagonalProjection := by
    simp [P, Measurement.map_effect, binary, sum_filter]
  have hN : N.effect (some ()) = uniformProjection := by
    simp [N, Measurement.map_effect, binary, sum_filter]
  have hconst (u : Point F 0) :
      (∑ b : F, (φ (N.effect (some ()) *
        (evaluatePolynomialMeasurement P u).effect (some b) * N.effect (some ()) *
        P.effect none * (B u).effect b)).re) =
        (φ (uniformProjection * diagonalProjection * uniformProjection *
          (1 - diagonalProjection))).re := by
    rw [sum_eq_single_of_mem 0 (mem_univ 0)]
    · simp [B, Measurement.const, hP, hPnone, hN]
    · intro b _ hb
      simp [B, Measurement.const, hb]
  simp only [failureTerm, Fintype.sum_unique, hconst, Fintype.expect_const]
  norm_num [φ, AlgState.vector_apply, basisVector, EuclideanSpace.single, Matrix.mul_apply,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, uniformProjection,
    diagonalProjection,
    Matrix.one_apply]

private noncomputable def slices (x : F) : Measurement (Option (BoundedPolynomial F 0 0)) Mat :=
  if x = 0 then P else N.map (Option.map fun _ => zeroSlice)

private theorem slices_projective (x : F) : (slices x).IsProjective := by
  classical
  by_cases hx : x = 0
  · simpa only [slices, ite_eq_left hx, P] using
      (binary_projective diagonalProjection diagonalProjection_star diagonalProjection_sq).map
        (fun b => if b then some zeroSlice else none)
  · simpa only [slices, ite_eq_right hx, N] using
      ((binary_projective uniformProjection uniformProjection_star uniformProjection_sq).map
        (fun b => if b then some () else none)).map (Option.map fun _ => zeroSlice)

private noncomputable def verifier :
    CommutingStrategy (Question F 1) (Question F 1) (Answer F 1) (Answer F 1) Mat where
  state := φ
  alice _ := Measurement.const (.inl 0)
  bob _ := Measurement.const (.inl 0)
  commute _ _ _ _ := by
    simp only [Measurement.const]
    split_ifs <;> first | exact Commute.one_right _ | exact Commute.zero_right _

private theorem verifier_decodedPoint (w : Point F 1) :
    decodedPoint verifier.alice w = (Measurement.const 0 : Measurement F Mat) := by
  classical
  ext a
  simp only [decodedPoint, verifier, Measurement.map_effect, sum_filter, Measurement.const]
  rw [sum_eq_single_of_mem (.inl 0 : Answer F 1) (mem_univ _)]
  · simp [eq_comm]
  · intro b _ hb
    simp [hb]

/-- The two slices have noncommuting successful projections. Their commutator
defect is nevertheless bounded by the public theorem with its actual hypotheses. -/
example :
    ¬ Commute ((slices 0).effect (some zeroSlice)) ((slices 1).effect (some zeroSlice)) ∧
    (𝔼 u : Point F 1, 𝔼 v : Point F 1, Measurement.successfulPairDefect φ
      (evaluatePolynomialMeasurement (slices (u 0)) (Fin.init u))
      (evaluatePolynomialMeasurement (slices (v 0)) (Fin.init v))) ≤
      2 * (4 * √2 + 2 * √(64 * (1 - (branchGame (F := F) 0 0 .diagonal).commutingWinProb
        verifier)) + 2 + 2) := by
  classical
  constructor
  · intro h
    have hP : (slices 0).effect (some zeroSlice) = diagonalProjection := by
      simp [slices, P, binary, Measurement.map_effect, sum_filter]
    have hN : (slices 1).effect (some zeroSlice) = uniformProjection := by
      simp [slices, N, binary, Measurement.map_map, Measurement.map_effect, sum_filter]
    rw [hP, hN] at h
    have he := congrArg (fun a : Mat => a 0 1) h.eq
    norm_num [diagonalProjection, uniformProjection, Matrix.mul_apply, Fin.sum_univ_two] at he
  · let copy (_ : F) : Measurement (Option (BoundedPolynomial F 0 0)) Mat :=
      Measurement.const none
    have hcopy : (𝔼 x, Measurement.successfulCopyDefect φ (slices x) (copy x)) ≤ 1 := by
      apply expect_le univ_nonempty
      intro x _
      simpa only [Measurement.successfulCopyDefect, copy, Measurement.const, reduceCtorEq,
        ite_false, sub_zero, mul_one, AlgState.norm_one, one_pow] using
        Measurement.sum_norm_some_effect_mul_sq_le φ (slices x) (slices_projective x) 1
    have hmismatch (w : Point F 1) :
        Measurement.successfulMismatch φ
          (evaluatePolynomialMeasurement (slices (w (Fin.last 0))) (Fin.init w))
          (decodedPoint verifier.alice w) ≤ 1 := by
      let E := evaluatePolynomialMeasurement (slices (w (Fin.last 0))) (Fin.init w)
      rw [verifier_decodedPoint]
      unfold Measurement.successfulMismatch
      calc
        _ ≤ ∑ a : F, (φ (E.effect (some a))).re := by
          refine sum_le_sum fun a _ => ?_
          rw [mul_sub, mul_one, map_sub, Complex.sub_re]
          exact sub_le_self _ (φ.re_apply_nonneg (Commute.mul_nonneg (E.nonneg _)
            ((Measurement.const (0 : F)).nonneg a) (commute_const_effect _ 0 a)))
        _ ≤ 1 := by
          simp only [← Complex.re_sum, ← map_sum]
          exact φ.re_apply_le_one E.successfulEffect_mem_Icc.2
    have h := evaluatedSlice_successfulPairDefect_le verifier
      (fun _ => Measurement.isProjective_const _) (fun _ => Measurement.isProjective_const _)
      0 slices slices_projective (fun _ => 1) (fun _ => zero_le_one)
      (fun x g => (averagePolynomialPointEffect_mem_Icc _ g).2)
      (fun x w g a => by rw [verifier_decodedPoint]; exact commute_const_effect _ 0 a)
      (fun _ _ _ => Commute.one_right _) copy (fun _ => Measurement.isProjective_const _)
      (fun _ _ _ _ => commute_const_effect _ none _) (ξ := 1) (ζ := 1) (η := 1)
      hcopy
      (expect_le univ_nonempty fun x _ => by
        rw [mul_one]
        exact φ.re_apply_le_one ((slices x).effect_le_one none))
      (expect_le univ_nonempty fun w _ => hmismatch w)
    simpa [verifier, show (Fin.last 0 : Fin 1) = 0 by decide] using h

/-- Coarsening two deterministic measurements to the same successful outcome
reduces their squared copy defect from two to zero. -/
example :
    let L : Measurement (Option Bool) Mat := Measurement.const (some false)
    let R : Measurement (Option Bool) Mat := Measurement.const (some true)
    let f : Bool → Unit := fun _ => ()
    Measurement.successfulCopyDefect φ L R = 2 ∧
    Measurement.successfulCopyDefect φ (L.map (Option.map f)) (R.map (Option.map f)) = 0 ∧
    Measurement.successfulCopyDefect φ (L.map (Option.map f)) (R.map (Option.map f)) ≤
      Measurement.successfulCopyDefect φ L R := by
  intro L R f
  refine ⟨?_, ?_, Measurement.successfulCopyDefect_map_le φ L R
    (Measurement.isProjective_const _) (Measurement.isProjective_const _)
    (fun _ _ => commute_const_effect _ _ _) f⟩
  · norm_num [Measurement.successfulCopyDefect, L, R, Measurement.const, AlgState.norm_neg]
  · simp [Measurement.successfulCopyDefect, L, R, f, Measurement.map_effect, Measurement.const]

/-- One of two relabelings merges both outcomes, and the other distinguishes them.
The recovery estimate applies to the computational and uniform qubit measurements. -/
example :
    let L := (binary diagonalProjection diagonalProjection_star diagonalProjection_sq).map some
    let Q := (binary uniformProjection uniformProjection_star uniformProjection_sq).map some
    let R : Measurement (Option Bool) Mat := Measurement.const (some false)
    let f (u a : Bool) := u && a
    (𝔼 u : Bool, if f u false = f u true then (1 : ℝ) else 0) = 1 / 2 ∧
    Measurement.successfulPairDefect φ L Q ≤
      4 * (𝔼 u : Bool, Measurement.successfulPairDefect φ (L.map (Option.map (f u))) Q) +
        6 * Measurement.successfulCopyDefect φ L R + 2 := by
  intro L Q R f
  have hcollision (a a' : Bool) (hne : a ≠ a') :
      (𝔼 u : Bool, if f u a' = f u a then (1 : ℝ) else 0) = 1 / 2 := by
    cases a <;> cases a' <;> norm_num [f, Fintype.expect_eq_sum_div_card, Fintype.sum_bool] at *
  refine ⟨hcollision true false (by decide), ?_⟩
  have h := Measurement.successfulPairDefect_le_average_map φ L R Q
    ((binary_projective _ _ _).map _) (Measurement.isProjective_const _)
    ((binary_projective _ _ _).map _) (fun _ _ => commute_const_effect _ _ _)
    (fun _ _ => (commute_const_effect _ _ _).symm) f (κ := 1 / 2)
    (by norm_num) (fun a a' hne => (hcollision a a' hne).le)
  norm_num at h
  exact h

end CslibFrontierTests.LowIndividualDegreeSliceBoundedness

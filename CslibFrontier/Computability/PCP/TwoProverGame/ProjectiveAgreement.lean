/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled
import CslibFrontier.Foundations.Quantum.Orthogonalization

/-!
# Orthogonalizing two agreeing tensor measurements

A high agreement probability forces both measurements to have large squared-effect
mass in the corresponding marginal states. Orthogonalize each measurement in its
marginal state to get projective measurements on the original local spaces.
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Cslib.Quantum Matrix Finset
open scoped BigOperators MatrixOrder ComplexOrder Kronecker

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]

/-- Two local POVMs that agree in the joint state are close to projective POVMs
on their respective original spaces. Each squared state distance is at most
eighteen times the disagreement bound. -/
theorem exists_projective_pair_of_agreement (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (G : POVM α ι) (H : POVM α κ) {ζ : ℝ}
    (h : 1 - ζ ≤ Measurement.agreement φ (leftMeasurement (κ := κ) G) (rightMeasurement H)) :
    ∃ (P : POVM α ι) (R : POVM α κ),
      P.toMeasurement.IsProjective ∧ R.toMeasurement.IsProjective ∧
      (∑ a, φ.norm ((leftMeasurement (κ := κ) G).effect a -
        (leftMeasurement (κ := κ) P).effect a) ^ 2) ≤ 18 * ζ ∧
      (∑ a, φ.norm ((rightMeasurement (ι := ι) H).effect a -
        (rightMeasurement (ι := ι) R).effect a) ^ 2) ≤ 18 * ζ := by
  let L := leftMeasurement (κ := κ) G
  let R := rightMeasurement (ι := ι) H
  have hsq := Measurement.two_mul_agreement_le_sum_re_effect_sq φ L R
    (fun a => commute_liftedEffects G H a a)
  have hL := Measurement.sum_re_effect_sq_le_one φ L
  have hR := Measurement.sum_re_effect_sq_le_one φ R
  change 1 - ζ ≤ Measurement.agreement φ L R at h
  have hLeft : 1 - 2 * ζ ≤ ∑ a,
      (φ (kroneckerOne (κ := κ) (G.toMeasurement.effect a * G.toMeasurement.effect a))).re := by
    have he (a : α) : (φ (L.effect a * L.effect a)).re =
        (φ (kroneckerOne (κ := κ) (G.toMeasurement.effect a * G.toMeasurement.effect a))).re := by
      rw [map_mul (kroneckerOne (κ := κ))]
      rfl
    simp only [← he]
    linarith only [h, hsq, hR]
  have hRight : 1 - 2 * ζ ≤ ∑ a,
      (φ (oneKronecker (ι := ι) (H.toMeasurement.effect a * H.toMeasurement.effect a))).re := by
    have he (a : α) : (φ (R.effect a * R.effect a)).re =
        (φ (oneKronecker (ι := ι) (H.toMeasurement.effect a * H.toMeasurement.effect a))).re := by
      rw [map_mul (oneKronecker (ι := ι))]
      rfl
    simp only [← he]
    linarith only [h, hsq, hL]
  obtain ⟨P, hP, hdP⟩ := Measurement.exists_isProjective_sum_norm_map_sub_sq_le_of_le
    φ (kroneckerOne (κ := κ)) G.toMeasurement hLeft
  obtain ⟨T, hT, hdT⟩ := Measurement.exists_isProjective_sum_norm_map_sub_sq_le_of_le
    φ (oneKronecker (ι := ι)) H.toMeasurement hRight
  refine ⟨P.toPOVM, T.toPOVM, hP, hT, ?_, ?_⟩
  · simpa only [leftMeasurement, kroneckerOne_apply, POVM.toMeasurement_effect,
      Measurement.toPOVM_effect, show (9 : ℝ) * (2 * ζ) = 18 * ζ by ring] using hdP
  · simpa only [rightMeasurement, oneKronecker_apply, POVM.toMeasurement_effect,
      Measurement.toPOVM_effect, show (9 : ℝ) * (2 * ζ) = 18 * ζ by ring] using hdT

end Cslib.PCP.QuantumStrategy

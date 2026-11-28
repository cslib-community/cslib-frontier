/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.SpectralCut
import CslibFrontier.Foundations.Quantum.Algebra.Involution
import CslibFrontier.Foundations.Quantum.Pauli

/-! # Spectral cuts of an unequal two-coordinate spectrum -/

set_option linter.privateModule false

open Cslib.Quantum Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius MatrixOrder

private noncomputable def testSpectrum (b : Bool) : ℝ := if b then 3 / 4 else 1 / 4

/-- Only the two off-diagonal entries contribute, with the same positive gap. -/
example (A : Matrix Bool Bool ℂ) :
    ∫ t : ℝ, ‖A * diagonalCut testSpectrum t - diagonalCut testSpectrum t * A‖ ^ 2 =
      (‖A false true‖ ^ 2 + ‖A true false‖ ^ 2) / 2 := by
  rw [integral_norm_commutator_diagonalCut_sq testSpectrum (by
    intro b
    cases b <;> norm_num [testSpectrum])]
  norm_num [Fintype.sum_bool, testSpectrum]
  ring

/-- The trace state divides the squared Frobenius norm by the dimension. -/
example (A : Matrix Bool Bool ℂ) :
    (AlgState.normalizedMatrixTrace : AlgState (Matrix Bool Bool ℂ)).norm A ^ 2 =
      ‖A‖ ^ 2 / 2 := by
  simpa using AlgState.norm_sq_normalizedMatrixTrace A

private noncomputable def pauliXMeasurement : Measurement Bool (Matrix Bool Bool ℂ) :=
  Measurement.ofInvolution pauliX_isHermitian.isSelfAdjoint pauliX_mul_self

private def pureSpectrum (b : Bool) : ℝ := if b then 0 else 1

private theorem norm_pauliX_effect (a i j : Bool) :
    ‖pauliXMeasurement.effect a i j‖ = 1 / 2 := by
  change ‖signProj pauliX a i j‖ = _
  rw [signProj]
  change ‖(2⁻¹ : ℂ) * ((1 : Matrix Bool Bool ℂ) i j +
    (Cslib.BitString.signVal a : ℂ) * pauliX i j)‖ = _
  cases a <;> cases i <;> cases j <;>
    norm_num [Matrix.one_apply, Cslib.BitString.signVal, Complex.norm_mul]

/-- The Pauli X measurement on the pure diagonal state has agreement one half and
a strictly positive squared commutator sum. -/
example :
    let P := fun s : Finset Bool => diagonal fun i => if i ∈ s then (1 : ℂ) else 0
    (∑ s : {s : Finset Bool // s.Nonempty}, diagonalCutWidth pureSpectrum s *
        ∑ a, ‖pauliXMeasurement.effect a * P s.val - P s.val * pauliXMeasurement.effect a‖ ^ 2) =
      1 ∧ 1 ≤ 2 * Real.sqrt (2 * (1 / 2)) := by
  intro P
  have hd (i : Bool) : 0 ≤ pureSpectrum i := by cases i <;> norm_num [pureSpectrum]
  have he (a : Bool) :
      (∑ s : {s : Finset Bool // s.Nonempty},
        diagonalCutWidth pureSpectrum s *
          ‖pauliXMeasurement.effect a * P s.val - P s.val * pauliXMeasurement.effect a‖ ^ 2) =
        1 / 2 := by
    rw [← integral_diagonalCutSupport pureSpectrum
      (fun s => ‖pauliXMeasurement.effect a * P s - P s * pauliXMeasurement.effect a‖ ^ 2)
      (by simp [P])]
    simp only [P, ← diagonalCut_eq_diagonal_support]
    rw [integral_norm_commutator_diagonalCut_sq pureSpectrum hd]
    norm_num [Fintype.sum_bool, pureSpectrum, norm_pauliX_effect]
  have hsum :
      (∑ s : {s : Finset Bool // s.Nonempty}, diagonalCutWidth pureSpectrum s *
        ∑ a, ‖pauliXMeasurement.effect a * P s.val - P s.val * pauliXMeasurement.effect a‖ ^ 2) =
      1 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    norm_num [he]
  have hbound := pauliXMeasurement.sum_diagonalCutWidth_norm_commutator_sq_le pureSpectrum hd
    (by norm_num [Fintype.sum_bool, pureSpectrum]) (1 / 2) (by
      norm_num [Fintype.sum_bool, pureSpectrum, norm_pauliX_effect])
  change _ ≤ _ at hbound
  rw [hsum] at hbound
  exact ⟨hsum, hbound⟩

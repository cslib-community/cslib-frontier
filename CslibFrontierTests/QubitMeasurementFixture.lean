/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.Quantum.Algebra.SequentialMeasurement
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Ring.Idempotent

/-! # Computational and uniform qubit measurements for sequential tests -/

@[expose] public section

namespace CslibFrontierTests.QubitMeasurementFixture

open Cslib.Quantum Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
def diagonalProjection : Mat := !![1, 0; 0, 0]
noncomputable def uniformProjection : Mat := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

theorem diagonalProjection_star : star diagonalProjection = diagonalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalProjection, Matrix.star_apply]

theorem uniformProjection_star : star uniformProjection = uniformProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniformProjection, Matrix.star_apply]

theorem diagonalProjection_sq :
    diagonalProjection * diagonalProjection = diagonalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [diagonalProjection, Matrix.mul_apply, Fin.sum_univ_two]

theorem uniformProjection_sq :
    uniformProjection * uniformProjection = uniformProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [uniformProjection, Matrix.mul_apply, Fin.sum_univ_two]

def binary (e : Mat) (he : star e = e) (he₂ : e * e = e) : Measurement Bool Mat where
  effect b := if b then e else 1 - e
  nonneg b := by
    cases b
    · have hc : (1 - e) * (1 - e) = 1 - e := (show IsIdempotentElem e from he₂).one_sub
      simpa only [Bool.false_eq_true, ite_false, star_sub, star_one, he, hc]
        using star_mul_self_nonneg (1 - e)
    · simpa only [ite_true, he, he₂] using star_mul_self_nonneg e
  sum_effect := by simp

theorem binary_projective (e : Mat) (he : star e = e) (he₂ : e * e = e) :
    (binary e he he₂).IsProjective := by
  intro b
  cases b
  · exact (show IsIdempotentElem e from he₂).one_sub
  · exact he₂

theorem pair_projective (D U : Measurement Bool Mat)
    (hD : D.IsProjective) (hU : U.IsProjective) :
    ∀ i : Fin 2, (![D, U] i).IsProjective := by
  intro i
  fin_cases i
  · exact hD
  · exact hU

noncomputable def basisVector : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

noncomputable def φ : AlgState Mat :=
  AlgState.vector basisVector (EuclideanSpace.orthonormal_single.norm_eq_one 1)

end CslibFrontierTests.QubitMeasurementFixture

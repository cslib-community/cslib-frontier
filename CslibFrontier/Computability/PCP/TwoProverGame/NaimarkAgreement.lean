/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Computability.PCP.TwoProverGame.Naimark

/-!
# Transporting measurement agreement through Naimark dilation

Auxiliary measurements constructed on the dilated local spaces can be restricted to
the prepared ancilla coordinates. Agreement after any outcome relabeling is the same
in the dilated state as for the restricted measurements in the original state.
-/

public section

namespace Cslib.PCP.QuantumStrategy

open Cslib.Quantum Matrix Finset
open scoped MatrixOrder ComplexOrder Kronecker

variable {X Y A B C D V ι κ : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [Fintype D] [Fintype V] [DecidableEq V]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The strategy dilation preserves agreement between auxiliary measurements
when both measurements are restricted back to their prepared ancillas. -/
theorem agreement_dilate_restrictBasis (S : QuantumStrategy X Y A B ι κ)
    (a₀ : A) (b₀ : B) (L : POVM C (ι × A)) (R : POVM D (κ × B))
    (f : C → V) (g : D → V) :
    let T := (S.dilate a₀ b₀).toCommuting
    let O := S.toCommuting
    Measurement.agreement T.state ((leftMeasurement (κ := κ × B) L).map f)
      ((rightMeasurement (ι := ι × A) R).map g) =
    Measurement.agreement O.state
      ((leftMeasurement (κ := κ) (L.restrictBasis (ancillaBasis a₀))).map f)
      ((rightMeasurement (ι := ι) (R.restrictBasis (ancillaBasis b₀))).map g) := by
  classical
  intro T O
  simp only [Measurement.agreement_map_map]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases he : f a = g b
  · simp only [he, ite_true, T, O, toCommuting, AlgState.vector_apply, leftMeasurement,
      rightMeasurement, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      POVM.restrictBasis_effect, tensorMatrixCoeff_dilate]
  · simp only [he, ite_false]

end Cslib.PCP.QuantumStrategy

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
public import CslibFrontier.Foundations.Quantum.DensityMatrix
import CslibFrontier.Foundations.LinearAlgebra.Matrix.PosSemidefTrace
import CslibFrontier.Foundations.Quantum.DensityMatrix.Pure

/-!
# Algebraic states from density matrices

The state of a density matrix pairs an operator with the density under the trace.
This agrees with the existing vector state for a pure density matrix. Operators that
commute with the density can pass from one end of the pairing to the other.
-/

public section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Cslib.Quantum.AlgState

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive normalized functional associated with a density matrix. -/
noncomputable def ofDensityMatrix (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    AlgState (Matrix ι ι ℂ) where
  toFun E := (E * ρ).trace
  map_add' E F := by rw [Matrix.add_mul, Matrix.trace_add]
  map_smul' c E := by rw [Matrix.smul_mul, Matrix.trace_smul, RingHom.id_apply]
  monotone' E F h := by
    apply sub_nonneg.mp
    rw [← Matrix.trace_sub, ← Matrix.sub_mul]
    exact (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).trace_mul_nonneg hρ.posSemidef
  map_one' := by rw [Matrix.one_mul, hρ.trace_eq_one]

theorem ofDensityMatrix_apply {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) (E : Matrix ι ι ℂ) :
    ofDensityMatrix ρ hρ E = (E * ρ).trace := by
  unfold ofDensityMatrix
  rfl

theorem ofDensityMatrix_pureState (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    ofDensityMatrix (pureState ψ) (isDensityMatrix_pureState hψ) = vector ψ hψ := by
  ext E
  rw [ofDensityMatrix_apply, vector_apply, trace_mul_pureState]

/-- Commutation with the density allows cyclic exchange across its state pairing. -/
theorem ofDensityMatrix_mul_comm {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ)
    {E : Matrix ι ι ℂ} (hE : Commute E ρ) (F : Matrix ι ι ℂ) :
    ofDensityMatrix ρ hρ (E * F) = ofDensityMatrix ρ hρ (F * E) := by
  simp only [ofDensityMatrix_apply, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm E, Matrix.mul_assoc (F), ← hE.eq]

end Cslib.Quantum.AlgState

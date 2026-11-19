/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
public import CslibFrontier.Foundations.Quantum.Measurement.Classical
public import CslibFrontier.Foundations.Quantum.Register
import all CslibFrontier.Foundations.Quantum.Measurement.Classical

/-!
# Changing the replies to a coherent XOR query

The query-magnitude method of [Bennett et al.][BBBV1997] bounds the effect of changing
oracle answers on a quantum computation. Here the input is a joint density matrix
on a placed query and an arbitrary reference. The bound for one call uses the actual
probability of measuring an address at which the two response words differ.
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped ComplexOrder

/-- Input-weighted squared norm of the difference of two placed XOR gates, including the
untouched reference register. For any common purification of the input, it is the squared
norm of the difference of its two output vectors. It can be positive for identical output
density matrices when the outputs differ by a global phase. -/
@[expose] noncomputable def xorQueryDisturbance {a b m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H G : (Fin a → Bool) → Fin b → Bool) (A : Fin (a + b) ↪ Fin m)
    (ρ : Matrix ((Fin m → Bool) × κ) ((Fin m → Bool) × κ) ℂ) : ℝ :=
  let u := onFirst (κ := κ) (xorQuery H A).matrix
  let v := onFirst (κ := κ) (xorQuery G A).matrix
  (densityConj (u.val - v.val) ρ).trace.re

/-- The squared amplitude displacement at one coherent call is at most four times
the probability that a measurement of its live address reports different replies. -/
theorem xorQueryDisturbance_le {a b m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H G : (Fin a → Bool) → Fin b → Bool) (A : Fin (a + b) ↪ Fin m)
    {ρ : Matrix ((Fin m → Bool) × κ) ((Fin m → Bool) × κ) ℂ} (hρ : IsDensityMatrix ρ) :
    xorQueryDisturbance H G A ρ ≤ 4 * ((((POVM.basis.measureDensity ρ hρ).map fun z =>
      decide (H (queryRegisters A z.1).1 ≠ G (queryRegisters A z.1).1)) true).toReal) := by
  classical
  let u := onFirst (κ := κ) (xorQuery H A).matrix
  let v := onFirst (κ := κ) (xorQuery G A).matrix
  let D := u.val - v.val
  let bad := fun z : (Fin m → Bool) × κ =>
    decide (H (queryRegisters A z.1).1 ≠ G (queryRegisters A z.1).1)
  have mask : D * outcomeProjection bad true = D := by
    rw [outcomeProjection_eq_diagonal]
    ext i j
    rw [mul_diagonal]
    by_cases eq : H (queryRegisters A j.1).1 = G (queryRegisters A j.1).1
    · have col : (xorQuery H A).eval (ket j.1) = (xorQuery G A).eval (ket j.1) := by
        obtain ⟨⟨x, y, w⟩, hj⟩ := (queryRegisters A).symm.surjective j.1
        rw [← hj, Equiv.apply_symm_apply] at eq
        rw [← hj, xorQuery_eval_ket, xorQuery_eval_ket, eq]
      have entry := congrArg (fun ψ : Qubits m => ψ.ofLp i.1) col
      simp only [PlacedGate.eval_ket_apply] at entry
      simp [D, u, v, coe_onFirst, Matrix.kroneckerMap_apply, entry, bad]
    · rw [ite_eq_left (show bad j = true from decide_eq_true eq), mul_one]
  have bound := trace_densityConj_sub_le
    (mem_unitaryGroup_iff'.mp u.property) (mem_unitaryGroup_iff'.mp v.property)
    (classicalDensityBranch_posSemidef bad true hρ.posSemidef)
  change (densityConj D (densityConj (outcomeProjection bad true) ρ)).trace.re ≤ _ at bound
  rw [← densityConj_mul, mask] at bound
  change (densityConj D ρ).trace.re ≤ 4 * (((POVM.basis.measureDensity ρ hρ).map bad) true).toReal
  have pos := (classicalDensityBranch_posSemidef bad true hρ.posSemidef).trace_nonneg
  rw [map_measureDensity_basis_apply, ENNReal.toReal_ofReal (Complex.nonneg_iff.mp pos).1]
  exact bound

end Cslib.Quantum

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Trace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Multiplication traces with no variables and with a repeated root -/

public section

namespace CslibFrontierTests.PurePowerTrace

open MvPolynomial MvPolynomial.PurePower

-- The empty system has rank one, so its multiplication trace is the scalar itself.
theorem trace_empty :
    Algebra.trace ℤ (QuotientAlgebra 2 (fun _ : Fin 0 => (0 : MvPolynomial (Fin 0) ℤ)))
      (projection 2 (fun _ : Fin 0 => 0) (C 5)) = 5 := by
  rw [trace_eq_residue 1 (by decide) _ (by intro i; exact i.elim0)]
  have hJ : jacobian 2 (fun _ : Fin 0 => (0 : MvPolynomial (Fin 0) ℤ)) = 1 := by
    simp [jacobian]
  rw [hJ, mul_one, residue_low_degree (by decide) _ (by intro i; exact i.elim0) _ (by
    change (C (5 : ℤ) : MvPolynomial (Fin 0) ℤ).totalDegree ≤ 0
    exact (totalDegree_C _).le)]
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 0 => 2 - 1) = (0 : Fin 0 →₀ ℕ) :=
    Subsingleton.elim _ _
  rw [he]
  simp

private noncomputable abbrev lower : Fin 1 → MvPolynomial (Fin 1) ℤ := fun _ => 0

private theorem lower_degree (i : Fin 1) : (lower i).totalDegree < 2 := by
  simp [lower]

private theorem jacobian_squareZero : jacobian 2 lower = (2 : ℤ) • X 0 := by
  simp [jacobian, lower, smul_eq_C_mul]

private theorem residue_X : residue 2 lower (X 0) = 1 := by
  rw [residue_low_degree (by decide) lower lower_degree _ (by simp)]
  have he : Finsupp.equivFunOnFinite.symm (fun _ : Fin 1 => 2 - 1) =
      Finsupp.single 0 1 := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  rw [he]
  simp [X]

-- The algebra ℤ[X]/(X²) has a repeated root and a nonzero nilpotent variable class.
example : Algebra.trace ℤ (QuotientAlgebra 2 lower) (projection 2 lower 1) = 2 := by
  rw [trace_eq_residue 1 (by decide) lower (by intro i; simp [lower]),
    one_mul, jacobian_squareZero, residue_smul (by decide) lower lower_degree, residue_X]
  norm_num

example : Algebra.trace ℤ (QuotientAlgebra 2 lower) (projection 2 lower (X 0)) = 0 := by
  rw [trace_eq_residue 1 (by decide) lower (by intro i; simp [lower])]
  change linear (by decide) lower lower_degree (X 0 * jacobian 2 lower) = 0
  apply linear_mem_ideal
  have hprod : X 0 * jacobian 2 lower = C (2 : ℤ) * (X 0 ^ 2 - lower 0) := by
    rw [jacobian_squareZero]
    simp only [lower, sub_zero, smul_eq_C_mul]
    ring
  rw [hprod]
  exact (relationIdeal 2 lower).mul_mem_left (C 2) (Ideal.subset_span ⟨0, rfl⟩)

end CslibFrontierTests.PurePowerTrace

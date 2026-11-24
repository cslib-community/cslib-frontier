/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Basis
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! # Empty systems and nonreduced pure-power quotients -/

public section
namespace CslibFrontierTests.PurePowerBasis

open MvPolynomial MvPolynomial.PurePower Module

-- With no variables the quotient still has one normal monomial.
theorem rank_empty :
    finrank ℤ (QuotientAlgebra 3 (fun _ : Fin 0 => (0 : MvPolynomial (Fin 0) ℤ))) = 1 := by
  let b := normalBasis (by decide : 1 ≤ 3)
    (fun _ : Fin 0 => (0 : MvPolynomial (Fin 0) ℤ)) (by intro i; exact i.elim0)
  rw [finrank_eq_card_basis b]
  simp [NormalIndex]

private noncomputable def squareZeroBasis :
    Basis (NormalIndex 1 2) ℤ
      (QuotientAlgebra 2 (fun _ : Fin 1 => (0 : MvPolynomial (Fin 1) ℤ))) :=
  normalBasis (by decide) _ (by intro i; simp)

-- The repeated-root quotient ℤ[X] / (X²) has rank two over ℤ.
example : finrank ℤ (QuotientAlgebra 2 (fun _ : Fin 1 => (0 : MvPolynomial (Fin 1) ℤ))) = 2 := by
  rw [finrank_eq_card_basis squareZeroBasis]
  simp [NormalIndex]

-- Its variable class is nonzero but its square is zero.
example : projection 2 (fun _ : Fin 1 => (0 : MvPolynomial (Fin 1) ℤ)) (X 0) ≠ 0 := by
  have h := squareZeroBasis.ne_zero (fun _ => (1 : Fin 2))
  simp only [squareZeroBasis, normalBasis_apply, normalClass] at h
  have he : boxExponent (fun _ : Fin 1 => (1 : Fin 2)) = Finsupp.single 0 1 := by
    apply Finsupp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [boxExponent]
  simpa only [he, X] using h

example : (projection 2 (fun _ : Fin 1 => (0 : MvPolynomial (Fin 1) ℤ)) (X 0)) ^ 2 = 0 := by
  simpa only [map_zero] using projection_X_pow 2
    (fun _ : Fin 1 => (0 : MvPolynomial (Fin 1) ℤ)) 0

end CslibFrontierTests.PurePowerBasis

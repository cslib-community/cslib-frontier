/-
Copyright (c) 2026 Samuel Schlesinger, lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, additions to `Mathlib/Algebra/MvPolynomial/Degrees`)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Total-degree bounds without nontriviality assumptions

A formal variable has total degree at most one, even over the trivial coefficient semiring.
Mapping coefficients cannot increase total degree, whether or not the coefficient map is
injective. These bounds support divided differences and residue specialization without
importing an application of the degree calculus.
-/

public section

namespace MvPolynomial

/-- Every formal variable `X i` has total degree at most `1`, without requiring `Nontrivial R`. -/
theorem totalDegree_X_le {ι R : Type*} [CommSemiring R] (i : ι) :
    (X i : MvPolynomial ι R).totalDegree ≤ 1 := by
  change (monomial (Finsupp.single i 1) (1 : R)).totalDegree ≤ 1
  exact (totalDegree_monomial_le _ _).trans (by simp)

/-- Mapping coefficients cannot increase total degree, even when coefficients vanish. -/
theorem totalDegree_map_le {S T σ : Type*} [CommSemiring S] [CommSemiring T]
    (φ : S →+* T) (v : MvPolynomial σ S) :
    (v.map φ).totalDegree ≤ v.totalDegree :=
  Finset.sup_mono (MvPolynomial.support_map_subset φ v)

end MvPolynomial

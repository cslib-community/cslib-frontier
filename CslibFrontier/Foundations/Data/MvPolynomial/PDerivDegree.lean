/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, multivariate polynomial derivatives)

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Total degree of a formal partial derivative

The degree drops by at least one. The bound holds for arbitrary commutative semirings,
including the zero polynomial and positive characteristic, where further terms can disappear.
Ported from `LeanCanny.Algebra.PartialDerivativeDegree` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial

variable {ι R : Type*} [CommSemiring R]

/-- A formal partial derivative has total degree at most the original degree minus one. -/
theorem totalDegree_pderiv_le (p : MvPolynomial ι R) (i : ι) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    intro h
    have hn := MvPolynomial.mem_support_iff.mp hm
    rw [coeff_pderiv, h, zero_mul] at hn
    exact hn rfl
  have hd := le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  have he : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index]
    · simp
    · intro _ _
      rfl
    · intro _ _ _ _
      rfl
  rw [he] at hd
  omega


end MvPolynomial

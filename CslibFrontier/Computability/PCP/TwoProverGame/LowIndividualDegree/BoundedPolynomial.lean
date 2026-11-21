/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Fintype.Pi

/-!
# Polynomials of bounded individual degree

Bounding the degree in every coordinate gives a finite type of polynomial answers
over a finite field. A polynomial is determined by its coefficients at the
finitely many exponent tuples within those bounds.

## Main definitions

* `Cslib.PCP.LowIndividualDegree.BoundedPolynomial`: the type of polynomial answers
  with the supplied individual-degree bound.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open MvPolynomial

/-- A polynomial whose degree in every coordinate is at most `d`. -/
abbrev BoundedPolynomial (F : Type*) [CommSemiring F] (m d : ℕ) :=
  {p : MvPolynomial (Fin m) F // ∀ i, p.degreeOf i ≤ d}

variable {F : Type*} {m d : ℕ} [Field F]

instance [Finite F] : Finite (BoundedPolynomial F m d) := by
  classical
  let exponents (a : Fin m → Fin (d + 1)) : Fin m →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => (a i).val)
  let encode (p : BoundedPolynomial F m d) (a : Fin m → Fin (d + 1)) :=
    p.val.coeff (exponents a)
  refine Finite.of_injective encode fun p q h => Subtype.ext (MvPolynomial.ext _ _ fun e => ?_)
  by_cases he : ∀ i, e i ≤ d
  · let a (i : Fin m) : Fin (d + 1) := ⟨e i, Nat.lt_succ_of_le (he i)⟩
    have ha : exponents a = e := Finsupp.equivFunOnFinite_symm_coe e
    simpa only [encode, ha] using congrFun h a
  · have zeroCoeff (r : BoundedPolynomial F m d) : r.val.coeff e = 0 := by
      rw [← notMem_support_iff]
      exact fun hs => he fun i => (le_degreeOf_of_mem_support i hs).trans (r.prop i)
    rw [zeroCoeff p, zeroCoeff q]

noncomputable instance [Finite F] : Fintype (BoundedPolynomial F m d) :=
  Fintype.ofFinite _

end Cslib.PCP.LowIndividualDegree

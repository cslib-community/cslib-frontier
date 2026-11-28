/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.MvPolynomial.LastVariable
import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial interpolation across coordinate slices

View a polynomial in `m + 1` variables as a univariate polynomial in the last variable
with coefficients in the first `m` variables. The ordinary Lagrange basis then interpolates
polynomial-valued data. The construction controls the degree in the interpolation variable
and preserves common degree bounds in all other variables.

## Main definitions

* `MvPolynomial.interpolateLast`: interpolate a family of lower-dimensional polynomials.

## Main results

* `MvPolynomial.specializeLast_interpolateLast`: the interpolant recovers the given slices.
* `MvPolynomial.degreeOf_last_interpolateLast_le`: the last degree is at most the node count
  minus one.
* `MvPolynomial.degreeOf_castSucc_interpolateLast_le`: the other individual degree bounds
  are inherited from the input slices.
* `MvPolynomial.eq_of_specializeLast_eq`: enough slices uniquely determine the polynomial.
-/

public section

namespace MvPolynomial

open Finset

variable {R : Type*} {m : ℕ} [CommSemiring R]

section Field

variable {F ι : Type*} [Field F] [DecidableEq ι]

/-- Interpolate polynomials given on the distinct slices indexed by `s`. -/
noncomputable def interpolateLast (s : Finset ι) (x : ι → F)
    (g : ι → MvPolynomial (Fin m) F) : MvPolynomial (Fin (m + 1)) F :=
  (lastVariableEquiv F m).symm <| ∑ j ∈ s,
    Polynomial.C (g j) * (Lagrange.basis s x j).map C

/-- The interpolated polynomial specializes to the requested polynomial at each node. -/
theorem specializeLast_interpolateLast {s : Finset ι} {x : ι → F}
    (hx : Set.InjOn x s) (g : ι → MvPolynomial (Fin m) F) {j : ι} (hj : j ∈ s) :
    specializeLast (x j) (interpolateLast s x g) = g j := by
  rw [specializeLast_apply, interpolateLast]
  rw [AlgEquiv.apply_symm_apply, Polynomial.eval_finsetSum]
  rw [sum_eq_single_of_mem j hj]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Lagrange.eval_basis_self hx hj, map_one, mul_one]
  · intro i hi hij
    rw [Polynomial.eval_mul, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Lagrange.eval_basis_of_ne hij hj, map_zero, mul_zero]

/-- Interpolating over `s` puts degree at most `s.card - 1` in the last variable. -/
theorem degreeOf_last_interpolateLast_le {s : Finset ι} {x : ι → F}
    (hx : Set.InjOn x s) (g : ι → MvPolynomial (Fin m) F) :
    (interpolateLast s x g).degreeOf (Fin.last m) ≤ s.card - 1 := by
  rw [← natDegree_lastVariableEquiv, interpolateLast, AlgEquiv.apply_symm_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add,
    Polynomial.natDegree_map_eq_of_injective (C_injective (Fin m) F),
    Lagrange.natDegree_basis hx hj]

/-- Interpolation does not increase any of the degrees in the prefix variables. -/
theorem degreeOf_castSucc_interpolateLast_le (s : Finset ι) (x : ι → F)
    (g : ι → MvPolynomial (Fin m) F) (i : Fin m) {d : ℕ}
    (h : ∀ j ∈ s, (g j).degreeOf i ≤ d) :
    (interpolateLast s x g).degreeOf i.castSucc ≤ d := by
  rw [degreeOf_castSucc_le_iff]
  intro k
  unfold interpolateLast
  rw [AlgEquiv.apply_symm_apply, Polynomial.finsetSum_coeff]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j hj => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  exact (degreeOf_mul_le _ _ _).trans (by simpa using h j hj)

omit [DecidableEq ι] in
/-- Two polynomials of last degree strictly below the number of distinct slices coincide
if their specializations coincide on those slices. -/
theorem eq_of_specializeLast_eq {s : Finset ι} {x : ι → F} (hx : Set.InjOn x s)
    {p q : MvPolynomial (Fin (m + 1)) F}
    (hp : p.degreeOf (Fin.last m) < s.card) (hq : q.degreeOf (Fin.last m) < s.card)
    (h : ∀ j ∈ s, specializeLast (x j) p = specializeLast (x j) q) : p = q := by
  classical
  apply (lastVariableEquiv F m).injective
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (ι := s)
    _ _ (f := fun j => C (x j))
    (fun i j hij => Subtype.ext (hx i.prop j.prop (C_injective (Fin m) F hij)))
  · exact fun j => by simpa only [specializeLast_apply] using h j j.prop
  · rw [Fintype.card_coe, natDegree_lastVariableEquiv, natDegree_lastVariableEquiv]
    exact max_lt hp hq

end Field

end MvPolynomial

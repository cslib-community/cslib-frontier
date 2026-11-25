/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, beside `Mathlib.Algebra.MvPolynomial.Degrees`)

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Monomial extensions of functions on the cube

The monomial extension of `f : (ι → Bool) → R` is the polynomial `∑ u, f u * ∏_{u i} X i`: the
coefficient of the square-free monomial of the set bits of `u` is `f u`
(`MvPolynomial.monomialExtension`). Unlike the multilinear extension
(`MvPolynomial.multilinearExtension`), whose weights are `X i` and `1 - X i`, it does not
interpolate `f` on the cube; it records `f` in its coefficients. Its degree is at most the largest
number of set bits of a point where `f` does not vanish
(`MvPolynomial.totalDegree_monomialExtension_le`).

## Main definitions

* `MvPolynomial.monomialExtension`.

## Main results

* `MvPolynomial.totalDegree_monomialExtension_le`.
-/

public section

namespace MvPolynomial

open Finset

variable {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]

/-- The monomial extension `∑ u, f u * ∏_{u i} X i` of `f`. -/
@[expose] noncomputable def monomialExtension (f : (ι → Bool) → R) : MvPolynomial ι R :=
  ∑ u : ι → Bool, C (f u) * ∏ i, if u i then X i else 1

/-- The degree of the monomial extension is at most the number of set bits of the points where `f`
does not vanish. -/
theorem totalDegree_monomialExtension_le (f : (ι → Bool) → R) {d : ℕ}
    (hd : ∀ u, f u ≠ 0 → #{i | u i = true} ≤ d) : (monomialExtension f).totalDegree ≤ d := by
  refine totalDegree_finsetSum_le fun u _ => ?_
  by_cases hu : f u = 0
  · simp [hu]
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finsetProd _ _).trans (le_trans ?_ (hd u hu))
    rw [card_filter]
    refine sum_le_sum fun i _ => ?_
    split_ifs
    · exact (totalDegree_monomial_le _ _).trans (by simp)
    · simp

end MvPolynomial

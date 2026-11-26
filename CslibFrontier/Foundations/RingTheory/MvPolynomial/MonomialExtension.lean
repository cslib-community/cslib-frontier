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
(`MvPolynomial.totalDegree_monomialExtension_le`), and at the indicator of a point `c` it is the
sum of `f` over the points below `c` (`MvPolynomial.eval_indicator_monomialExtension`).

## Main definitions

* `MvPolynomial.monomialExtension`.

## Main results

* `MvPolynomial.totalDegree_monomialExtension_le`.
* `MvPolynomial.eval_indicator_monomialExtension`.
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

/-- At the indicator of `c`, the monomial extension of `f` is the sum of `f` over the points below
`c`: the monomial of `u` is `1` there when every set bit of `u` is set in `c`, and `0` otherwise. -/
theorem eval_indicator_monomialExtension (f : (ι → Bool) → R) (c : ι → Bool) :
    eval (fun i => if c i then 1 else 0) (monomialExtension f) =
      ∑ u with ∀ i, u i = true → c i = true, f u := by
  rw [monomialExtension, map_sum, sum_filter]
  refine sum_congr rfl fun u _ => ?_
  rw [map_mul, eval_C, map_prod]
  split_ifs with h
  · rw [prod_eq_one fun i _ => ?_, mul_one]
    cases hu : u i <;> simp [hu, h i]
  · push Not at h
    obtain ⟨i, hu, hc⟩ := h
    rw [prod_eq_zero (mem_univ i) (by simp [hu, hc]), mul_zero]

end MvPolynomial

/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, complex products)

public import CslibFrontier.Init
public import Mathlib.Basic.Complex.BigOperators

/-!
# Products over conjugation-stable finite sets

Each nonreal pair in a conjugation-stable set contributes a squared norm
to the product of values of a function that commutes with conjugation.
This exposes the factors that determine the sign of a real spectral product.

Adapted from `ConjugateProducts` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Complex

open Finset
open scoped ComplexConjugate

/-- A conjugation-stable product factors into the real values on the real axis and
one squared norm per nonreal pair, indexed by the points with positive imaginary part. -/
theorem prod_eq_ofReal_mul_prod_normSq (S : Finset ℂ) (f : ℂ → ℂ)
    (hS : ∀ z ∈ S, conj z ∈ S) (hf : ∀ z ∈ S, f (conj z) = conj (f z)) :
    (∏ z ∈ S, f z) =
      (((∏ z ∈ S.filter (fun z => z.im = 0), (f z).re) *
        ∏ z ∈ S.filter (fun z => 0 < z.im), normSq (f z) : ℝ) : ℂ) := by
  classical
  let P := S.filter fun z => 0 < z.im
  let N := S.filter fun z => z.im < 0
  let R := S.filter fun z => z.im = 0
  have hsplit : (S.filter fun z => z.im ≠ 0) = P ∪ N := by
    ext z
    simp only [P, N, mem_filter, mem_union, ← and_or_left, ne_iff_lt_or_gt, or_comm]
  have hdisjoint : Disjoint P N := by
    refine disjoint_left.mpr fun z hz hz' => ?_
    exact lt_asymm (mem_filter.mp hz).2 (mem_filter.mp hz').2
  have himage : P.image conj = N := by
    ext z
    simp only [P, N, mem_image, mem_filter]
    constructor
    · rintro ⟨w, ⟨hw, hpos⟩, rfl⟩
      exact ⟨hS w hw, by simpa only [conj_im, neg_neg_iff_pos] using hpos⟩
    · intro hz
      exact ⟨conj z, ⟨hS z hz.1, by simpa only [conj_im, neg_pos] using hz.2⟩, conj_conj z⟩
  have hreal : (∏ z ∈ R, f z) = ((∏ z ∈ R, (f z).re : ℝ) : ℂ) := by
    rw [ofReal_prod]
    refine prod_congr rfl fun z hz => ?_
    obtain ⟨hzS, hzim⟩ := mem_filter.mp hz
    have hfix : conj (f z) = f z := by rw [← hf z hzS, conj_eq_iff_im.mpr hzim]
    exact (conj_eq_iff_re.mp hfix).symm
  have hpairs : (∏ z ∈ P, f z) * (∏ z ∈ N, f z) =
      ((∏ z ∈ P, normSq (f z) : ℝ) : ℂ) := by
    rw [← himage, prod_image (g := conj) star_injective.injOn, ← prod_mul_distrib, ofReal_prod]
    exact prod_congr rfl fun z hz => by rw [hf z (mem_filter.mp hz).1, Complex.mul_conj]
  have hparts := (prod_filter_mul_prod_filter_not S (fun z => z.im = 0) f).symm
  rw [hsplit, prod_union hdisjoint] at hparts
  change (∏ z ∈ S, f z) = (∏ z ∈ R, f z) * ((∏ z ∈ P, f z) * ∏ z ∈ N, f z) at hparts
  rw [hparts, hreal, hpairs, ofReal_mul]

end Complex

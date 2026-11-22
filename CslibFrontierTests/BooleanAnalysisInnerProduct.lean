/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.InnerProduct
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! # The Fourier spectrum of the inner product

On one pair of bits the inner product is the conjunction `x ∧ y`, read as signs
`(1 + x + y - x y) / 2`: its coefficient on `{x, y}` is `-1 / 2`, both from the formula and by brute
force over the four inputs. On two pairs every coefficient is `± 1 / 4`, so a polynomial threshold
representation needs at least `4` monomials: the inner product is a threshold function over all
`16` sets, but not over the constant term and the two monomials `x₀ y₀`, `x₁ y₁`, in either form of
Corollary 5.11. The hypothesis `p ≠ 0` of the form that allows zeros is needed for every `n`:
`p = 0` and `T = ∅` meet the others. In the book's form `f = sgn(p)` with `sgn(0) = 1`, the
implicit `p ≢ 0` matters only on no pairs, where the inner product is constantly `false` (the sign
`1 = sgn(0)`). The character of a set on `ι ⊕ κ` factors over the halves, here over `ℤ`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisInnerProduct

open Cslib Cslib.BitString Finset

/-- The character of `{x₀, y₀}` at `x₀ = 1`, `y₀ = 0` is `(-1) * 1 = -1`, the product of the
characters of the two halves. -/
theorem chi_sumElim_one :
    chi ℤ ({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)) (Sum.elim ![true] ![false]) = -1 := by
  have hL : ({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)).toLeft = {0} := by decide
  have hR : ({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)).toRight = {0} := by decide
  rw [chi_sumElim, hL, hR]
  simp [chi]

/-- On one pair of bits the inner product is `AND`. -/
theorem innerProduct_one (x y : Fin 1 → Bool) : innerProduct (Sum.elim x y) = (x 0 && y 0) := by
  rw [innerProduct_sumElim, dotProduct, Fin.sum_univ_one]
  rfl

/-- The coefficient on both bits of one pair is `(-1) ^ |{0} ∩ {0}| / 2 = -1 / 2`. -/
theorem fourierCoeff_innerProduct_one :
    fourierCoeff (fun z : Fin 1 ⊕ Fin 1 → Bool => signVal (innerProduct z))
      {.inl 0, .inr 0} = -1 / 2 := by
  have h : ({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)).toLeft ∩
      ({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)).toRight = {0} := by decide
  rw [fourierCoeff_signVal_innerProduct, h]
  norm_num

/-- Brute force over the four inputs gives the same `-1 / 2`. -/
theorem fourierCoeff_innerProduct_one_bruteForce :
    fourierCoeff (fun z : Fin 1 ⊕ Fin 1 → Bool => signVal (innerProduct z))
      {.inl 0, .inr 0} = -1 / 2 := by
  rw [fourierCoeff, Fintype.expect_sumElim]
  simp only [innerProduct_sumElim, Fin.expect_univ_cons, Fintype.expect_bool,
    Fintype.expect_unique]
  norm_num [chi, dotProduct, signVal, show ∀ a b : Bool, a * b = (a && b) from fun _ _ => rfl]

/-- On two pairs of bits every coefficient is `± 1 / 4`. -/
theorem abs_fourierCoeff_innerProduct_two (S : Finset (Fin 2 ⊕ Fin 2)) :
    |fourierCoeff (fun z => signVal (innerProduct z)) S| = 1 / 4 := by
  rw [abs_fourierCoeff_signVal_innerProduct]
  norm_num

/-- The coefficient on `{x₀, y₀, y₁}` is `(-1) ^ |{0} ∩ {0, 1}| / 4 = -1 / 4`. -/
theorem fourierCoeff_innerProduct_two_three :
    fourierCoeff (fun z : Fin 2 ⊕ Fin 2 → Bool => signVal (innerProduct z))
      {.inl 0, .inr 0, .inr 1} = -1 / 4 := by
  rw [fourierCoeff_signVal_innerProduct]
  have h : ({.inl 0, .inr 0, .inr 1} : Finset (Fin 2 ⊕ Fin 2)).toLeft ∩
      ({.inl 0, .inr 0, .inr 1} : Finset (Fin 2 ⊕ Fin 2)).toRight = {0} := by decide
  rw [h]
  norm_num

/-- The empty set and the two pairs `{x₀, y₀}`, `{x₁, y₁}`: the constant term and the two
monomials of `c₀ + c₁ x₀ y₀ + c₂ x₁ y₁`. -/
def pairSets : Finset (Finset (Fin 2 ⊕ Fin 2)) :=
  {∅, {.inl 0, .inr 0}, {.inl 1, .inr 1}}

/-- The family has three sets. -/
theorem card_pairSets : #pairSets = 3 := by decide

/-- The hypothesis of Corollary 5.11 is satisfiable: the inner product is a threshold function
over all `16` sets. -/
theorem isPTFOn_univ_innerProduct :
    IsPTFOn (univ : Finset (Finset (Fin 2 ⊕ Fin 2))) innerProduct :=
  isPTFOn_of_fourierCoeff_eq_zero fun S hS => absurd (mem_univ S) hS

/-- Corollary 5.11, nowhere-vanishing form: the inner product is not a threshold function over the
three sets of `pairSets`. -/
theorem not_isPTFOn_pairSets_innerProduct : ¬ IsPTFOn pairSets innerProduct := fun h => by
  have := h.two_pow_le_card_innerProduct
  rw [card_pairSets] at this
  norm_num at this

/-- Corollary 5.11, allowing zeros: every `p` over `pairSets` with `IP · p ≥ 0` is zero. -/
theorem eq_zero_of_nonneg_mul_pairSets {p : (Fin 2 ⊕ Fin 2 → Bool) → ℝ}
    (hpT : ∀ S ∉ pairSets, fourierCoeff p S = 0)
    (hp : ∀ z, 0 ≤ signVal (innerProduct z) * p z) : p = 0 := by
  by_contra hp₀
  have := two_pow_le_card_innerProduct_of_nonneg_mul hpT hp₀ hp
  rw [card_pairSets] at this
  norm_num at this

/-- On two pairs, `p = 0` and `T = ∅` meet the other hypotheses of
`two_pow_le_card_innerProduct_of_nonneg_mul`, and `2 ^ 2 ≤ #∅` fails, so `p ≠ 0` cannot be
dropped. -/
theorem zero_satisfies_hypotheses_two :
    (∀ S ∉ (∅ : Finset (Finset (Fin 2 ⊕ Fin 2))),
        fourierCoeff (0 : (Fin 2 ⊕ Fin 2 → Bool) → ℝ) S = 0) ∧
      (∀ z : Fin 2 ⊕ Fin 2 → Bool,
        0 ≤ signVal (innerProduct z) * (0 : (Fin 2 ⊕ Fin 2 → Bool) → ℝ) z) ∧
      ¬ 2 ^ Fintype.card (Fin 2) ≤ #(∅ : Finset (Finset (Fin 2 ⊕ Fin 2))) := by
  refine ⟨fun S _ => ?_, fun z => by simp, by simp⟩
  simp [fourierCoeff]

/-- On no pairs the inner product is constantly `false`, read as the sign `1 = sgn(0)`, so in the
book's form `p = 0` represents it: there the book's implicit `p ≢ 0` is needed. -/
theorem innerProduct_fin_zero (z : Fin 0 ⊕ Fin 0 → Bool) : innerProduct z = false := by
  rw [← Sum.elim_comp_inl_inr z, innerProduct_sumElim]
  rfl

end CslibFrontierTests.BooleanAnalysisInnerProduct

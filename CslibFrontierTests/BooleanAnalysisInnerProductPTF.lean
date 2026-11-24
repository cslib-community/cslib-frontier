/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.InnerProductPTF
import CslibFrontier.Foundations.BooleanAnalysis.InnerProduct
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! # The PTF sparsity of the inner product

On one pair of bits `z = (x₀, y₀)` the inner product `fstBits z ⬝ᵥ sndBits z` is the conjunction
`x₀ ∧ y₀`, read as signs `(1 + x₀ + y₀ - x₀ y₀) / 2`: its coefficient on `{x₀, y₀}` is `-1 / 2`,
both from the formula and by brute force over the four inputs. On two pairs
`z = (x₀, x₁, y₀, y₁)` every coefficient is `± 1 / 4`, so a polynomial threshold representation
needs at least `4` monomials: the inner product is a threshold function over all `16` sets, but
not over the constant term and the two monomials `x₀ y₀`, `x₁ y₁`, in either form of
Corollary 5.11. The hypothesis `p ≠ 0` of the form that allows zeros is needed for every `n`:
`p = 0` and `T = ∅` meet the others. In the book's form `f = sgn(p)` with `sgn(0) = 1`, the
implicit `p ≢ 0` matters only on no pairs, where the inner product is constantly `false` (the sign
`1 = sgn(0)`).
-/

public section

namespace CslibFrontierTests.BooleanAnalysisInnerProductPTF

open Cslib Cslib.BitString Finset

/-- On one pair of bits the inner product is `AND`. -/
theorem dotProduct_fstBits_sndBits_one (z : BitString (1 + 1)) :
    fstBits z ⬝ᵥ sndBits z = (z 0 && z 1) := by
  rw [dotProduct, Fin.sum_univ_one, fstBits_apply, sndBits_apply]
  rfl

/-- The coefficient on both bits `{x₀, y₀}` of one pair is `-1 / 2`: the two halves of the mask
are both `1`, with inner product `1`. -/
theorem fourierCoeff_one :
    fourierCoeff (fun z : BitString (1 + 1) => signVal (fstBits z ⬝ᵥ sndBits z)) {0, 1} =
      -1 / 2 := by
  have h : ((fun i : Fin 1 => decide (Fin.castAdd 1 i ∈ ({0, 1} : Finset (Fin (1 + 1))))) ⬝ᵥ
      fun i : Fin 1 => decide (Fin.natAdd 1 i ∈ ({0, 1} : Finset (Fin (1 + 1))))) = true := by
    decide
  rw [fourierCoeff_signVal_dotProduct_fstBits_sndBits, h]
  norm_num [signVal]

/-- Brute force over the four inputs gives the same `-1 / 2`. -/
theorem fourierCoeff_one_bruteForce :
    fourierCoeff (fun z : BitString (1 + 1) => signVal (fstBits z ⬝ᵥ sndBits z)) {0, 1} =
      -1 / 2 := by
  simp only [fourierCoeff, dotProduct_fstBits_sndBits_one, Fin.expect_univ_cons_bool,
    Fintype.expect_unique]
  norm_num [chi, signVal]

/-- On two pairs of bits every coefficient is `± 1 / 4`. -/
theorem abs_fourierCoeff_two (S : Finset (Fin (2 + 2))) :
    |fourierCoeff (fun z : BitString (2 + 2) => signVal (fstBits z ⬝ᵥ sndBits z)) S| = 1 / 4 := by
  rw [abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits]
  norm_num

/-- The coefficient on `{x₀, y₀, y₁}` is `-1 / 4`: the halves of the mask are `(1, 0)` and
`(1, 1)`, with inner product `1`. -/
theorem fourierCoeff_two_three :
    fourierCoeff (fun z : BitString (2 + 2) => signVal (fstBits z ⬝ᵥ sndBits z)) {0, 2, 3} =
      -1 / 4 := by
  have h : ((fun i : Fin 2 => decide (Fin.castAdd 2 i ∈ ({0, 2, 3} : Finset (Fin (2 + 2))))) ⬝ᵥ
      fun i : Fin 2 => decide (Fin.natAdd 2 i ∈ ({0, 2, 3} : Finset (Fin (2 + 2))))) = true := by
    decide
  rw [fourierCoeff_signVal_dotProduct_fstBits_sndBits, h]
  norm_num [signVal]

/-- The empty set and the two pairs `{x₀, y₀}`, `{x₁, y₁}`: the constant term and the two
monomials of `c₀ + c₁ x₀ y₀ + c₂ x₁ y₁`. -/
def pairSets : Finset (Finset (Fin (2 + 2))) :=
  {∅, {0, 2}, {1, 3}}

/-- The family has three sets. -/
theorem card_pairSets : #pairSets = 3 := by decide

/-- The hypothesis of Corollary 5.11 is satisfiable: the inner product is a threshold function
over all `16` sets. -/
theorem isPTFOn_univ :
    IsPTFOn (univ : Finset (Finset (Fin (2 + 2))))
      fun z : BitString (2 + 2) => fstBits z ⬝ᵥ sndBits z :=
  isPTFOn_of_fourierCoeff_eq_zero fun S hS => absurd (mem_univ S) hS

/-- Corollary 5.11, nowhere-vanishing form: the inner product is not a threshold function over the
three sets of `pairSets`. -/
theorem not_isPTFOn_pairSets :
    ¬ IsPTFOn pairSets fun z : BitString (2 + 2) => fstBits z ⬝ᵥ sndBits z := fun h => by
  have := h.two_pow_le_card_dotProduct_fstBits_sndBits
  rw [card_pairSets] at this
  norm_num at this

/-- Corollary 5.11, allowing zeros: every `p` over `pairSets` with `IP · p ≥ 0` is zero. -/
theorem eq_zero_of_nonneg_mul_pairSets {p : BitString (2 + 2) → ℝ}
    (hpT : ∀ S ∉ pairSets, fourierCoeff p S = 0)
    (hp : ∀ z, 0 ≤ signVal (fstBits z ⬝ᵥ sndBits z) * p z) : p = 0 := by
  by_contra hp₀
  have := two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul hpT hp₀ hp
  rw [card_pairSets] at this
  norm_num at this

/-- On two pairs, `p = 0` and `T = ∅` meet the other hypotheses of
`two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul`, and `2 ^ 2 ≤ #∅` fails, so `p ≠ 0`
cannot be dropped. -/
theorem zero_satisfies_hypotheses_two :
    (∀ S ∉ (∅ : Finset (Finset (Fin (2 + 2)))),
        fourierCoeff (0 : BitString (2 + 2) → ℝ) S = 0) ∧
      (∀ z : BitString (2 + 2),
        0 ≤ signVal (fstBits z ⬝ᵥ sndBits z) * (0 : BitString (2 + 2) → ℝ) z) ∧
      ¬ 2 ^ 2 ≤ #(∅ : Finset (Finset (Fin (2 + 2)))) := by
  refine ⟨fun S _ => ?_, fun z => by simp, by simp⟩
  simp [fourierCoeff]

/-- On no pairs the inner product is constantly `false`, read as the sign `1 = sgn(0)`, so in the
book's form `p = 0` represents it: there the book's implicit `p ≢ 0` is needed. -/
theorem dotProduct_fstBits_sndBits_zero (z : BitString (0 + 0)) :
    fstBits z ⬝ᵥ sndBits z = false := by
  rw [dotProduct, Fin.sum_univ_zero]
  rfl

end CslibFrontierTests.BooleanAnalysisInnerProductPTF

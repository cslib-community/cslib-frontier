/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.CoordinateOperators
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Analysis.Normed.Module.Basic
import CslibFrontier.Foundations.BooleanAnalysis.Concentration
import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.Variance
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination

/-!
# The Khintchine–Kahane inequality

For vectors `w₁, …, wₙ` of a normed space and uniformly random signs `xᵢ`, the norm
`g(x) = ‖∑ᵢ xᵢ wᵢ‖` satisfies `𝔼 g ≥ √(𝔼 g² / 2)`: the **Khintchine–Kahane inequality**
(`BitString.expect_norm_sum_sq_le_two_mul_sq`) [O'Donnell, Exercise 2.55][ODonnell2014], with the
optimal constant found by Latała and Oleszkiewicz [LatalaOleszkiewicz1994], as the book's notes
record. The proof is the book's. By the triangle inequality `L g ≤ g` pointwise, where `L` is the
Laplacian (`BitString.laplacian_norm_sum_le`), so `I[g] = 𝔼[g L g] ≤ 𝔼 g²`; and `g` is even, so
its Fourier weight lies on sets of even size (`BitString.fourierCoeff_eq_zero_of_odd_card`) and
`2 Var[g] ≤ I[g]` (`BitString.two_mul_expect_sub_expect_sq_le_totalInfluence_of_even`). The
constant `2` is optimal (`BitString.two_le_of_forall_expect_norm_sum_sq_le`).

By an extra sign, an affine form `a₀ + ∑ᵢ aᵢ xᵢ` has the same absolute moments as the linear
form `a₀ x₀ + ∑ᵢ aᵢ xᵢ` [O'Donnell, Exercise 5.5][ODonnell2014], so the inequality holds for
every real function of degree at most one
(`BitString.expect_sq_le_two_mul_expect_abs_sq_of_mem_lowDegree_one`). This gives O'Donnell's
Theorem 5.2, that linear threshold functions have Fourier weight at least `1/2` up to level one
(`BitString.one_half_le_sum_fourierCoeff_sq_of_nonneg_mul`, in
`CslibFrontier.Foundations.BooleanAnalysis.PolynomialThresholdWeight`).

Khintchine's inequality for real coefficients with the constants of hypercontractivity is
`BitString.sqrt_sum_sq_le_exp_mul_lpNorm` in
`CslibFrontier.Foundations.BooleanAnalysis.LowDegreeMoments`; its `L^1` constant is `e`, not `√2`.

## Main results

* `Cslib.BitString.laplacian_norm_sum_le`: `L g ≤ g`.
* `Cslib.BitString.two_mul_expect_sub_expect_sq_le_totalInfluence_of_even`: `2 Var[g] ≤ I[g]` for
  even `g`.
* `Cslib.BitString.expect_norm_sum_sq_le_two_mul_sq`: the Khintchine–Kahane inequality.
* `Cslib.BitString.two_le_of_forall_expect_norm_sum_sq_le`: its constant `2` is optimal.
* `Cslib.BitString.expect_signVal_none_mul_add_sum_eq`: affine forms have the moments of linear
  forms.
* `Cslib.BitString.expect_sq_le_two_mul_expect_abs_sq_of_mem_lowDegree_one`: the inequality for
  real functions of degree at most one.

## Usage

Open `Cslib.BitString`. Uniform random signs are `signVal (x i)` for a uniform `x : ι → Bool`, so
`𝔼 x : ι → Bool, ‖∑ i, signVal (x i) • w i‖` is `𝔼 ‖∑ᵢ xᵢ wᵢ‖`; the vectors `w : ι → V` may lie in
any seminormed real space. The inequality says that Jensen's step
`𝔼 ‖∑ᵢ xᵢ wᵢ‖ ≤ √(𝔼 ‖∑ᵢ xᵢ wᵢ‖²)` loses at most a factor `√2`. In a real inner product space the
right side is `√(∑ᵢ ‖wᵢ‖²)` (`Cslib.BitString.expect_norm_sum_signVal_smul_sq` in
`CslibFrontier.Probability.BitString.Rademacher`), the bound that
`CslibFrontier.MachineLearning.Rademacher.Linear` uses for the Rademacher complexity of linear
predictors. For a real function `ℓ` on the cube, state degree at most one as
`ℓ ∈ lowDegree ℝ ι 1`. A linear form `fun x => ∑ i, a i * signVal (x i)` gets there by
`sum_mul_signVal_mem_lowDegree_one` (in
`CslibFrontier.Foundations.BooleanAnalysis.LowDegreeMoments`), an affine form by adding
`const_mem_lowDegree`, and any `ℓ` by
`mem_lowDegree_iff_fourierCoeff_eq_zero`. For a linear threshold function `f = sgn ℓ`, Theorem 5.2
is `one_half_le_sum_fourierCoeff_sq_of_nonneg_mul` in
`CslibFrontier.Foundations.BooleanAnalysis.PolynomialThresholdWeight`, which takes a nonzero
`ℓ ∈ lowDegree ℝ ι 1` and `∀ x, 0 ≤ signVal (f x) * ℓ x`, so `ℓ` may vanish on the cube; for
`IsPTF 1 f` use `IsPTF.one_half_le_sum_fourierCoeff_sq`. It improves the case
`k = 1` of the Gotsman–Linial bound `e⁻²` (`IsPTF.exp_neg_two_mul_le_sum_fourierCoeff_sq`), and
both go through the Cauchy–Schwarz step `sq_expect_abs_le_sum_fourierCoeff_sq_mul`. The checked
clients in
[CslibFrontierTests/BooleanAnalysisKhintchineKahane.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisKhintchineKahane.lean)
show that `2` is the least constant for two real weights, apply the inequality in the sup norm of
`ℝ²` and to the affine form `1 + x₀ + x₁`, check that `|x₀ + x₁|` has no weight on `{0}`, and
prove Theorem 5.2 for a dictator and for the AND of two bits.

## References

* [R. Latała, K. Oleszkiewicz, *On the best constant in the Khinchin–Kahane
  inequality*][LatalaOleszkiewicz1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Norm

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The Laplacian of a norm of a random signed sum is at most the norm** [O'Donnell,
Exercise 2.55(a)][ODonnell2014]: for `g(x) = ‖∑ᵢ xᵢ wᵢ‖`, `L g ≤ g` pointwise, since by the triangle
inequality `∑ᵢ g(x^{⊕i}) ≥ ‖∑ᵢ (v - 2 xᵢ wᵢ)‖ = |n - 2| g(x)`, where `v = ∑ᵢ xᵢ wᵢ`. -/
theorem laplacian_norm_sum_le (w : ι → V) (x : ι → Bool) :
    laplacian (fun x => ‖∑ i, signVal (x i) • w i‖) x ≤ ‖∑ i, signVal (x i) • w i‖ := by
  set v := ∑ i, signVal (x i) • w i
  have hflip (i : ι) :
      ∑ j, signVal (update x i (!x i) j) • w j = v - (2 * signVal (x i)) • w i := by
    have h (j : ι) : signVal (update x i (!x i) j) • w j =
        signVal (x j) • w j - if j = i then (2 * signVal (x i)) • w i else 0 := by
      by_cases hji : j = i
      · subst hji
        simp only [update_self, signVal_not, ↓reduceIte]
        module
      · simp [hji]
    simp only [h, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, v]
  have hsum : ∑ i, (v - (2 * signVal (x i)) • w i) = ((Fintype.card ι : ℝ) - 2) • v := by
    simp only [sum_sub_distrib, sum_const, card_univ, mul_smul, ← smul_sum, v]
    rw [sub_smul, Nat.cast_smul_eq_nsmul]
  have htri : |(Fintype.card ι : ℝ) - 2| * ‖v‖ ≤ ∑ i, ‖v - (2 * signVal (x i)) • w i‖ := by
    rw [← Real.norm_eq_abs, ← norm_smul, ← hsum]
    exact norm_sum_le _ _
  calc laplacian (fun x => ‖∑ i, signVal (x i) • w i‖) x
      = ∑ i, (‖v‖ - ‖v - (2 * signVal (x i)) • w i‖) / 2 := by
        simp only [laplacian, coordLaplacian_eq_flip, hflip, v]
    _ = ((Fintype.card ι : ℝ) * ‖v‖ - ∑ i, ‖v - (2 * signVal (x i)) • w i‖) / 2 := by
        rw [← sum_div, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    _ ≤ ‖v‖ := by
        rw [div_le_iff₀ two_pos]
        nlinarith [le_abs_self ((Fintype.card ι : ℝ) - 2), norm_nonneg v]

omit [DecidableEq ι] in
/-- A norm of a random signed sum is unchanged by flipping every sign. -/
private theorem norm_sum_not (w : ι → V) (x : ι → Bool) :
    ‖∑ i, signVal (!x i) • w i‖ = ‖∑ i, signVal (x i) • w i‖ := by
  simp only [signVal_not, neg_smul, sum_neg_distrib, norm_neg]

end Norm

/-- **The improved Poincaré inequality for even functions**
[O'Donnell, Exercise 2.28][ODonnell2014]: if `g` is unchanged by flipping every bit, then
`2 Var[g] ≤ I[g]`. An even function has no weight on the sets of one coordinate, so its variance
is its weight above level one, which is at most `I[g] / 2`
(`add_one_mul_sum_fourierCoeff_sq_le_totalInfluence`). -/
theorem two_mul_expect_sub_expect_sq_le_totalInfluence_of_even {g : (ι → Bool) → ℝ}
    (hg : ∀ x, g (fun i => !x i) = g x) :
    2 * 𝔼 x, (g x - 𝔼 y, g y) ^ 2 ≤ totalInfluence g := by
  have hW : ∑ S with S ≠ ∅, fourierCoeff g S ^ 2 = ∑ S with 1 < #S, fourierCoeff g S ^ 2 := by
    rw [sum_filter, sum_filter]
    refine sum_congr rfl fun S _ => ?_
    by_cases h1 : #S = 1
    · simp [fourierCoeff_eq_zero_of_odd_card hg (h1 ▸ odd_one : Odd #S)]
    · have : S ≠ ∅ ↔ 1 < #S := by rw [ne_empty_iff_nonempty, ← card_pos]; omega
      simp only [this]
  have h := add_one_mul_sum_fourierCoeff_sq_le_totalInfluence g 1
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq, hW]
  simpa [one_add_one_eq_two] using h

/-- **The Khintchine–Kahane inequality** [O'Donnell, Exercise 2.55][ODonnell2014]: for vectors
`wᵢ` of a normed space and uniformly random signs `xᵢ`,
`𝔼 ‖∑ᵢ xᵢ wᵢ‖² ≤ 2 (𝔼 ‖∑ᵢ xᵢ wᵢ‖)²`, that is, `𝔼 ‖∑ᵢ xᵢ wᵢ‖ ≥ √(𝔼 ‖∑ᵢ xᵢ wᵢ‖² / 2)`. -/
theorem expect_norm_sum_sq_le_two_mul_sq {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (w : ι → V) :
    𝔼 x : ι → Bool, ‖∑ i, signVal (x i) • w i‖ ^ 2 ≤
      2 * (𝔼 x : ι → Bool, ‖∑ i, signVal (x i) • w i‖) ^ 2 := by
  set g : (ι → Bool) → ℝ := fun x => ‖∑ i, signVal (x i) • w i‖
  -- `I[g] = 𝔼[g L g] ≤ 𝔼 g²`
  have hI : totalInfluence g ≤ 𝔼 x, g x ^ 2 := by
    rw [← expect_mul_laplacian]
    refine expect_le_expect fun x _ => ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (laplacian_norm_sum_le w x) (norm_nonneg _)
  have hvar := two_mul_expect_sub_expect_sq_le_totalInfluence_of_even (g := g) (norm_sum_not w)
  rw [Fintype.expect_sub_expect_sq] at hvar
  linarith

/-- **The constant `2` in the Khintchine–Kahane inequality is optimal, even for `V = ℝ`**
[O'Donnell, Exercise 2.55(c)][ODonnell2014]: it is attained by `x₀ + x₁`. -/
theorem two_le_of_forall_expect_norm_sum_sq_le {c : ℝ}
    (h : ∀ w : Fin 2 → ℝ, 𝔼 x : Fin 2 → Bool, ‖∑ i, signVal (x i) • w i‖ ^ 2 ≤
      c * (𝔼 x : Fin 2 → Bool, ‖∑ i, signVal (x i) • w i‖) ^ 2) :
    2 ≤ c := by
  have e (F : Bool → Bool → ℝ) : 𝔼 x : Fin 2 → Bool, F (x 0) (x 1) =
      (F false false + F false true + F true false + F true true) / 4 := by
    rw [Fintype.expect_equiv (finTwoArrowEquiv Bool) (fun x => F (x 0) (x 1))
      (fun p => F p.1 p.2) fun _ => rfl, Fintype.expect_prod_type]
    simp only [Fintype.expect_bool]
    ring
  have h1 := h 1
  simp only [Fin.sum_univ_two, Pi.one_apply, smul_eq_mul, mul_one, Real.norm_eq_abs] at h1
  rw [e (fun a b => |signVal a + signVal b| ^ 2), e fun a b => |signVal a + signVal b|] at h1
  norm_num at h1
  linarith

/-! ### Affine forms -/

/-- **An affine form has the moments of a linear form with one more sign**
[O'Donnell, Exercise 5.5(a)][ODonnell2014]: for an even `h`,
`𝔼_y h(b x₀ + ∑ᵢ aᵢ yᵢ)` over `y` on `Option ι` with `x₀ = y none` equals
`𝔼_x h(b + ∑ᵢ aᵢ xᵢ)`. -/
theorem expect_signVal_none_mul_add_sum_eq (h : ℝ → ℝ) (hh : ∀ t, h (-t) = h t) (b : ℝ)
    (a : ι → ℝ) :
    𝔼 y : Option ι → Bool, h (b * signVal (y none) + ∑ i, a i * signVal (y (some i))) =
      𝔼 x : ι → Bool, h (b + ∑ i, a i * signVal (x i)) := by
  rw [← Fintype.expect_equiv (Equiv.piOptionEquivProd (β := fun _ => Bool)).symm
    (fun p : Bool × (ι → Bool) => h (b * signVal p.1 + ∑ i, a i * signVal (p.2 i))) _
    fun p => rfl, Fintype.expect_prod_type, Fintype.expect_bool]
  have hflip : 𝔼 x : ι → Bool, h (b * signVal true + ∑ i, a i * signVal (x i)) =
      𝔼 x : ι → Bool, h (b + ∑ i, a i * signVal (x i)) := by
    refine Fintype.expect_bijective (fun x : ι → Bool => fun i => !x i)
      (Involutive.bijective fun x => by simp) _ _ fun x => ?_
    rw [← hh]
    congr 1
    simp only [signVal_true, signVal_not, mul_neg, sum_neg_distrib]
    ring
  rw [hflip]
  simp only [signVal_false, mul_one]
  ring

/-- **The Khintchine–Kahane inequality for functions of degree at most one**
[O'Donnell, Exercises 2.55 and 5.5][ODonnell2014]: if `ℓ` has Fourier degree at most one, then
`𝔼 ℓ² ≤ 2 (𝔼 |ℓ|)²`. -/
theorem expect_sq_le_two_mul_expect_abs_sq_of_mem_lowDegree_one {ℓ : (ι → Bool) → ℝ}
    (hℓ : ℓ ∈ lowDegree ℝ ι 1) :
    𝔼 x, ℓ x ^ 2 ≤ 2 * (𝔼 x, |ℓ x|) ^ 2 := by
  have hdeg := mem_lowDegree_iff_fourierCoeff_eq_zero.1 hℓ
  -- `ℓ = ℓ̂(∅) + ∑ᵢ ℓ̂({i}) xᵢ`
  have hexp (x : ι → Bool) :
      ℓ x = fourierCoeff ℓ ∅ + ∑ i, fourierCoeff ℓ {i} * signVal (x i) := by
    rw [← sum_fourierCoeff_mul_chi ℓ x,
      ← sum_filter_add_sum_filter_not univ fun S : Finset ι => 1 < #S,
      sum_eq_zero fun S hS => by
        rw [hdeg S (mem_filter.1 hS).2, zero_mul], zero_add]
    have hsplit : univ.filter (fun S : Finset ι => ¬ 1 < #S) =
        insert ∅ (univ.image fun i : ι => ({i} : Finset ι)) := by
      ext S
      simp [Nat.le_one_iff_eq_zero_or_eq_one, card_eq_one, eq_comm]
    rw [hsplit, sum_insert (by simp), sum_image fun i _ j _ h => singleton_injective h, chi_empty]
    simp only [chi_singleton, mul_one]
  set b := fourierCoeff ℓ ∅
  set a : ι → ℝ := fun i => fourierCoeff ℓ {i}
  -- the linear form with one more sign
  set w : Option ι → ℝ := fun j => j.elim b a
  have hlin (h : ℝ → ℝ) :
      𝔼 y : Option ι → Bool, h ‖∑ j, signVal (y j) • w j‖ = 𝔼 x, h ‖ℓ x‖ := by
    have e (y : Option ι → Bool) : ∑ j, signVal (y j) • w j =
        b * signVal (y none) + ∑ i, a i * signVal (y (some i)) := by
      rw [Fintype.sum_option]
      simp [w, smul_eq_mul, mul_comm]
    simp only [e, hexp]
    exact expect_signVal_none_mul_add_sum_eq (fun t => h ‖t‖) (fun t => by rw [norm_neg]) b a
  have hKK := expect_norm_sum_sq_le_two_mul_sq w
  rw [hlin (· ^ 2), hlin fun t => t] at hKK
  simpa only [Real.norm_eq_abs, sq_abs] using hKK

end Cslib.BitString

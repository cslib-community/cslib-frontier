/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Linearity
public import CslibFrontier.Probability.SmallBias
import CslibFrontier.Foundations.BooleanAnalysis.Affinity
import CslibFrontier.Probability.Fooling
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The derandomized BLR test

The *derandomized Blum–Luby–Rubinfeld test* with a distribution `X` on the cube queries a
Boolean function `f` at a uniformly random `x`, at an independent `y ∼ X`, and at `x + y`, and
accepts when `(f x ^^ f y) = f (x + y)`; `BitString.derandomizedBLRAcceptance X f` is the
probability that it accepts. With `X` uniform it is the BLR test
(`BitString.derandomizedBLRAcceptance_uniformOfFintype`). When `X` is `ε`-biased and has small
support, it uses far fewer random bits [O'Donnell, Section 6.4][ODonnell2014].

Reading `f` as the function `F x = (-1) ^ f x`, the test accepts with probability
`1/2 + 1/2 𝔼_{y ∼ X} [F(y) (F ∗ F)(y)]`
(`BitString.derandomizedBLRAcceptance_eq_sum_mul_convolution`). Linear functions, in particular
parities, still pass with probability one (`BitString.derandomizedBLRAcceptance_of_map_add`).

Conversely, write the acceptance probability as `1/2 + θ/2`. By Cauchy–Schwarz under `X`,
`θ² ≤ 𝔼_{y ∼ X} [(F ∗ F)(y)²]`; since `‖(F ∗ F)^‖₁ = ∑_S F̂(S)² = 1`, an `ε`-biased `X` fools
`(F ∗ F)²` up to `ε` (`BitString.IsSmallBias.fools_sq`), and the uniform expectation of
`(F ∗ F)²` is `∑_S F̂(S)⁴ ≤ max_S F̂(S)²`. Hence some `S` has `θ² - ε ≤ F̂(S)²`
(`BitString.exists_two_mul_derandomizedBLRAcceptance_sub_one_sq_sub_le_fourierCoeff_sq`), so `f`
has correlation at least `√(θ² - ε)` with `χ_S` or `-χ_S`, and is within relative distance
`1/2 - 1/2 √(θ² - ε)` of an affine function `b ^^ parityOn S`
[O'Donnell, Theorem 6.44][ODonnell2014]. The affine function may be a negated parity: those are
rejected with probability one, but a function that is `false` on the small support of `X` and
`true` off it is accepted almost always and is close only to the constant `true`.

## Main definitions

* `Cslib.BitString.derandomizedBLRAcceptance`: the acceptance probability of the derandomized
  BLR test.

## Main results

* `Cslib.BitString.derandomizedBLRAcceptance_eq_sum_mul_convolution`: the acceptance probability
  through the convolution.
* `Cslib.BitString.derandomizedBLRAcceptance_of_map_add`: completeness for linear functions.
* `Cslib.BitString.exists_two_mul_derandomizedBLRAcceptance_sub_one_sq_sub_le_fourierCoeff_sq`:
  the spectral form of soundness.
* `Cslib.BitString.exists_le_abs_fourierCoeff_of_le_derandomizedBLRAcceptance`,
  `Cslib.BitString.exists_hammingDist_xor_parityOn_le_of_le_derandomizedBLRAcceptance`: soundness
  in correlation and distance form [O'Donnell, Theorem 6.44][ODonnell2014].
* `Cslib.BitString.exists_hammingDist_xor_parityOn_le_of_one_sub_le_derandomizedBLRAcceptance`:
  acceptance `1 - δ` gives distance `δ + ε / (2 (1 - 2δ))`, a quantitative form of
  [O'Donnell, Remark 6.45][ODonnell2014].

## Usage

Open `Cslib.BitString`. Functions are `f : (ι → Bool) → Bool` with `^^` and `+`, as in the BLR
test of `CslibFrontier.Foundations.BooleanAnalysis.Linearity`, and the Fourier statements read `f`
as the signs `fun x => signVal (f x)`. The distribution is any `X : PMF (ι → Bool)`; the
soundness theorems assume `IsSmallBias ε X` (`CslibFrontier.Probability.SmallBias`) with
`0 ≤ ε`. Unfold the acceptance probability with `derandomizedBLRAcceptance_def`. The spectral form
takes `θ = 2 * derandomizedBLRAcceptance X f - 1`, of either sign. The correlation and distance
forms take any `θ` with `|θ| ≤ |2 * derandomizedBLRAcceptance X f - 1|`: the book's exact
acceptance `1/2 + θ/2` of either sign, or acceptance at least `1/2 + θ/2` for `0 ≤ θ`;
`Real.sqrt` is `0` on nonpositive arguments, so they are vacuous, not false, when `θ ^ 2 ≤ ε`.
The relative Hamming distance is `(hammingDist f g : ℝ) / 2 ^ Fintype.card ι`. The proof shares
two steps with the affinity test (`exists_sum_fourierCoeff_signVal_pow_four_le` and
`exists_hammingDist_xor_parityOn_le_of_le_abs_fourierCoeff` in
`CslibFrontier.Foundations.BooleanAnalysis.Affinity`) and the BLR acceptance condition in signs,
`ite_xor_eq_eq_signVal` in `Linearity`. The checked clients in
[CslibFrontierTests/BooleanAnalysisDerandomizedBLR.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisDerandomizedBLR.lean)
recover the BLR bounds from the uniform distribution and run the test with the powering
small-bias space on a thousand bits from 40 seed bits (`exists_isSmallBias_uniformOfFintype_map`),
where parities pass and acceptance `9/10` gives distance below `101/1000`. They also show that the
point mass at `0`, which is `1`-biased, accepts a conjunction with no Fourier coefficient above
`1/2`, so Theorem 6.44 proves that this point mass is not `ε`-biased for any `ε < 3/4`. The test is
an expectation over the cube: it is not packaged as a `PCP.LocalTest`, its count of
`n + O(log(n/ε))` random bits is not stated, and the improvements of
[O'Donnell, Exercises 6.32 and 6.33][ODonnell2014] are not formalized.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Probability
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The acceptance probability of the derandomized BLR test on `f` with distribution `X`: the
probability, over a uniformly random `x` and an independent `y ∼ X`, that
`(f x ^^ f y) = f (x + y)` [O'Donnell, Section 6.4][ODonnell2014]. -/
noncomputable def derandomizedBLRAcceptance (X : PMF (ι → Bool)) (f : (ι → Bool) → Bool) : ℝ :=
  𝔼 x, ∑ y, (X y).toReal * if (f x ^^ f y) = f (x + y) then 1 else 0

/-- The acceptance probability of the derandomized BLR test, unfolded. -/
theorem derandomizedBLRAcceptance_def (X : PMF (ι → Bool)) (f : (ι → Bool) → Bool) :
    derandomizedBLRAcceptance X f =
      𝔼 x, ∑ y, (X y).toReal * if (f x ^^ f y) = f (x + y) then 1 else 0 := by
  rw [derandomizedBLRAcceptance]

/-- **The acceptance probability of the derandomized BLR test**: reading `f` as signs `F`, the
test accepts with probability `1/2 + 1/2 𝔼_{y ∼ X} [F(y) (F ∗ F)(y)]`. -/
theorem derandomizedBLRAcceptance_eq_sum_mul_convolution (X : PMF (ι → Bool))
    (f : (ι → Bool) → Bool) :
    derandomizedBLRAcceptance X f = 1 / 2 + 1 / 2 * ∑ y, (X y).toReal *
      (signVal (f y) * convolution (fun x => signVal (f x)) (fun x => signVal (f x)) y) := by
  have h (y : ι → Bool) : 𝔼 x, signVal (f x) * (signVal (f y) * signVal (f (x + y))) =
      signVal (f y) * 𝔼 x, signVal (f x) * signVal (f (y + x)) := by
    rw [mul_expect]
    exact expect_congr rfl fun x _ => by rw [add_comm y]; ring
  rw [derandomizedBLRAcceptance, expect_sum_comm]
  simp only [ite_xor_eq_eq_signVal, mul_add, expect_add_distrib, ← mul_expect,
    Fintype.expect_const, sum_add_distrib, ← sum_mul, Probability.PMF.sum_toReal, one_mul, mul_sum,
    convolution]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  rw [h y]
  ring

/-- With the uniform distribution, the derandomized BLR test is the BLR test. -/
theorem derandomizedBLRAcceptance_uniformOfFintype (f : (ι → Bool) → Bool) :
    derandomizedBLRAcceptance (PMF.uniformOfFintype (ι → Bool)) f = blrAcceptance f := by
  rw [derandomizedBLRAcceptance, blrAcceptance]
  exact expect_congr rfl fun x _ => sum_uniformOfFintype_mul _

/-- **Completeness of the derandomized BLR test**: a linear function, one with
`f (x + y) = (f x ^^ f y)`, passes with probability one for every distribution `X`. -/
theorem derandomizedBLRAcceptance_of_map_add (X : PMF (ι → Bool)) {f : (ι → Bool) → Bool}
    (hf : ∀ x y, f (x + y) = (f x ^^ f y)) : derandomizedBLRAcceptance X f = 1 := by
  simp only [derandomizedBLRAcceptance, hf, ↓reduceIte, mul_one, Probability.PMF.sum_toReal,
    Fintype.expect_const]

/-- **Completeness of the derandomized BLR test** for parities. -/
theorem derandomizedBLRAcceptance_parityOn (X : PMF (ι → Bool)) (S : Finset ι) :
    derandomizedBLRAcceptance X (parityOn S) = 1 :=
  derandomizedBLRAcceptance_of_map_add X (parityOn_add S)

/-- **Soundness of the derandomized BLR test**, spectral form: if `X` is `ε`-biased and the test
accepts `f` with probability `1/2 + θ/2`, then `θ² - ε ≤ F̂(S)²` for some `S`, where `F` reads `f`
as signs; this is the core of [O'Donnell, Theorem 6.44][ODonnell2014]. Here
`θ = 2 * derandomizedBLRAcceptance X f - 1`, which may be negative: this is the only form that
covers `θ < 0`, as the book's exact acceptance `1/2 + θ/2` allows. -/
theorem exists_two_mul_derandomizedBLRAcceptance_sub_one_sq_sub_le_fourierCoeff_sq {ε : ℝ}
    (hε : 0 ≤ ε) {X : PMF (ι → Bool)} (hX : IsSmallBias ε X) (f : (ι → Bool) → Bool) :
    ∃ S, (2 * derandomizedBLRAcceptance X f - 1) ^ 2 - ε ≤
      fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set G := convolution F F
  set p : (ι → Bool) → ℝ := fun y => (X y).toReal
  have hθ : 2 * derandomizedBLRAcceptance X f - 1 = ∑ y, p y * (F y * G y) := by
    rw [derandomizedBLRAcceptance_eq_sum_mul_convolution]
    ring
  -- Cauchy–Schwarz under `X`, using `F y ^ 2 = 1`.
  have hcs : (∑ y, p y * (F y * G y)) ^ 2 ≤ ∑ y, p y * G y ^ 2 := by
    have h := sum_sq_le_sum_mul_sum_of_sq_le_mul univ (r := fun y => p y * (F y * G y))
      (f := p) (g := fun y => p y * G y ^ 2) (fun y _ => ENNReal.toReal_nonneg)
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)) fun y _ => by
        have hF : F y ^ 2 = 1 := by simp only [F, sq, signVal_mul_self]
        rw [mul_pow, mul_pow, hF, one_mul, sq (p y), mul_assoc]
    rwa [show ∑ y, p y = 1 from Probability.PMF.sum_toReal X, one_mul] at h
  -- `X` fools `G ^ 2`, since `‖Ĝ‖₁ = ∑_S F̂(S)² = 1`.
  have hnorm : ∑ S, |fourierCoeff G S| = 1 := by
    simp only [G, fourierCoeff_convolution, ← sq, abs_sq]
    exact sum_fourierCoeff_sq_signVal f
  have hfool := hX.fools_sq hε G
  rw [Fools, hnorm, one_pow, one_mul, expect_sq_eq_sum_fourierCoeff_sq] at hfool
  have hG4 : ∑ S, fourierCoeff G S ^ 2 = ∑ S, fourierCoeff F S ^ 4 := by
    simp only [G, fourierCoeff_convolution]
    exact sum_congr rfl fun S _ => by ring
  obtain ⟨S, hS⟩ := exists_sum_fourierCoeff_signVal_pow_four_le f
  refine ⟨S, ?_⟩
  rw [hθ]
  linarith [(abs_le.1 hfool).2]

/-- **Soundness of the derandomized BLR test**, correlation form
[O'Donnell, Theorem 6.44][ODonnell2014]: if `X` is `ε`-biased and the test accepts `f` with
probability `1/2 + θ'/2` where `|θ| ≤ |θ'|`, then reading `f` as signs, some Fourier coefficient
has `√(θ² - ε) ≤ |F̂(S)|`; that is, `f` has correlation at least `√(θ² - ε)` with `χ_S` or `-χ_S`.
This is the book's headline statement, whose hypothesis is the case `θ = θ'`, of either sign;
acceptance at least `1/2 + θ/2` with `θ ≥ 0` is the case `0 ≤ θ ≤ θ'`. The bound is vacuous when
`θ² ≤ ε`, where the square root is zero. -/
theorem exists_le_abs_fourierCoeff_of_le_derandomizedBLRAcceptance {ε θ : ℝ} (hε : 0 ≤ ε)
    {X : PMF (ι → Bool)} (hX : IsSmallBias ε X) {f : (ι → Bool) → Bool}
    (h : |θ| ≤ |2 * derandomizedBLRAcceptance X f - 1|) :
    ∃ S, √(θ ^ 2 - ε) ≤ |fourierCoeff (fun x => signVal (f x)) S| := by
  obtain ⟨S, hS⟩ := exists_two_mul_derandomizedBLRAcceptance_sub_one_sq_sub_le_fourierCoeff_sq hε hX
    f
  refine ⟨S, Real.sqrt_le_iff.2 ⟨abs_nonneg _, ?_⟩⟩
  rw [sq_abs]
  linarith [sq_le_sq.2 h]

/-- **Soundness of the derandomized BLR test**, distance form
[O'Donnell, Theorem 6.44][ODonnell2014]: if `X` is `ε`-biased and the test accepts `f` with
probability `1/2 + θ'/2` where `|θ| ≤ |θ'|`, then `f` differs from some affine function
`b ^^ parityOn S` on at most a `1/2 - 1/2 √(θ² - ε)` fraction of the inputs. This is the book's
"i.e." restatement, the form that Remark 6.45 uses
(`exists_hammingDist_xor_parityOn_le_of_one_sub_le_derandomizedBLRAcceptance`). The bound is
vacuous when `θ² ≤ ε`, where the square root is zero. -/
theorem exists_hammingDist_xor_parityOn_le_of_le_derandomizedBLRAcceptance {ε θ : ℝ}
    (hε : 0 ≤ ε) {X : PMF (ι → Bool)} (hX : IsSmallBias ε X) {f : (ι → Bool) → Bool}
    (h : |θ| ≤ |2 * derandomizedBLRAcceptance X f - 1|) :
    ∃ b S, (hammingDist f (fun x => b ^^ parityOn S x) : ℝ) / 2 ^ Fintype.card ι ≤
      1 / 2 - 1 / 2 * √(θ ^ 2 - ε) := by
  obtain ⟨S, hS⟩ := exists_le_abs_fourierCoeff_of_le_derandomizedBLRAcceptance hε hX h
  obtain ⟨b, hb⟩ := exists_hammingDist_xor_parityOn_le_of_le_abs_fourierCoeff hS
  exact ⟨b, S, hb.trans_eq (by ring)⟩

/-- **Acceptance near one gives a nearby affine function**, a quantitative form of
[O'Donnell, Remark 6.45][ODonnell2014]: if `X` is `ε`-biased and the test accepts `f` with
probability at least `1 - δ`, where `δ < 1/2`, then `f` differs from some affine function on at
most a `δ + ε / (2 (1 - 2δ))` fraction of the inputs. The explicit bound is not in the book; it
follows from Theorem 6.44 with `θ = 1 - 2δ` and `√(a² - ε) ≥ a - ε / a` for `a > 0`. So `f` is
nearly `δ`-close to an affine function when `ε ≪ δ (1 - 2δ)`, as the remark says for `ε ≪ δ` with
`δ` bounded away from `1/2`. -/
theorem exists_hammingDist_xor_parityOn_le_of_one_sub_le_derandomizedBLRAcceptance {ε δ : ℝ}
    (hε : 0 ≤ ε) {X : PMF (ι → Bool)} (hX : IsSmallBias ε X) {f : (ι → Bool) → Bool}
    (hδ : δ < 1 / 2) (h : 1 - δ ≤ derandomizedBLRAcceptance X f) :
    ∃ b S, (hammingDist f (fun x => b ^^ parityOn S x) : ℝ) / 2 ^ Fintype.card ι ≤
      δ + ε / (2 * (1 - 2 * δ)) := by
  have ha : 0 < 1 - 2 * δ := by linarith
  have hθ : |1 - 2 * δ| ≤ |2 * derandomizedBLRAcceptance X f - 1| := by
    rw [abs_of_pos ha]
    exact (by linarith : 1 - 2 * δ ≤ 2 * derandomizedBLRAcceptance X f - 1).trans (le_abs_self _)
  obtain ⟨b, S, hS⟩ := exists_hammingDist_xor_parityOn_le_of_le_derandomizedBLRAcceptance hε hX hθ
  refine ⟨b, S, hS.trans ?_⟩
  -- `√(a² - ε) ≥ a - ε / a` for `a > 0`.
  have hsqrt : (1 - 2 * δ) - ε / (1 - 2 * δ) ≤ √((1 - 2 * δ) ^ 2 - ε) := by
    rcases le_or_gt ε ((1 - 2 * δ) ^ 2) with hle | hlt
    · refine Real.le_sqrt_of_sq_le ?_
      have hq : ε / (1 - 2 * δ) * (1 - 2 * δ) = ε := div_mul_cancel₀ _ ha.ne'
      have hq' : ε / (1 - 2 * δ) ≤ 1 - 2 * δ := by
        rw [div_le_iff₀ ha]; nlinarith
      nlinarith [div_nonneg hε ha.le]
    · refine le_trans ?_ (Real.sqrt_nonneg _)
      rw [sub_nonpos, le_div_iff₀ ha]
      nlinarith
  have : ε / (2 * (1 - 2 * δ)) = 1 / 2 * (ε / (1 - 2 * δ)) := by
    field_simp
  rw [this]
  linarith

end Cslib.BitString

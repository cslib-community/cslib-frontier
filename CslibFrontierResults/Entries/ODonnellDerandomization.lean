/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.DerandomizedBLR
import CslibFrontier.Foundations.BooleanAnalysis.DeterministicEstimation
import CslibFrontier.Foundations.BooleanAnalysis.Regularity
import CslibFrontier.Foundations.BooleanAnalysis.SpectralNorm
import CslibFrontier.Probability.Fooling

/-!
# Collected results: regularity, small-bias fooling and derandomized testing and estimation
-/

register_result "odonnell-regularity-fourth-moment" where
  title := "Regularity of a real function on the cube is detected by its fourth spectral moment"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014,
      theorem := "Remark 6.3, Example 6.4 (constant and parity cases), Proposition 6.7",
      locator := "arXiv:2105.10386v1, §6.1, printed pp. 144–145" }
  ]
  theorems := [
    Cslib.BitString.isFourierRegular_expect_abs,
    Cslib.BitString.isFourierRegular_zero_iff,
    Cslib.BitString.not_isFourierRegular_chi,
    Cslib.BitString.sum_fourierCoeff_pow_four_sub_le_of_isFourierRegular,
    Cslib.BitString.pow_four_le_sum_fourierCoeff_pow_four_sub_of_not_isFourierRegular
  ]
  scope := "Every real function f on the cube (ι → Bool) over a finite coordinate type, with \
    IsFourierRegular ε f meaning |fourierCoeff f S| ≤ ε for every nonempty S (Definition 6.2). \
    Every f is (𝔼 x, |f x|)-regular; f is 0-regular exactly when it is constant; the character \
    χ_S of a nonempty S is not ε-regular for ε < 1. Proposition 6.7: an ε-regular f has \
    ∑ S, f̂(S)⁴ − (𝔼 f)⁴ ≤ ε² · 𝔼 x, (f x − 𝔼 y, f y)², and for 0 ≤ ε a function that is not \
    ε-regular has ∑ S, f̂(S)⁴ − (𝔼 f)⁴ ≥ ε⁴ (part (2) fails for ε < 0 when ι is nonempty). \
    The other cases of Example 6.4 (random functions, affine subspaces, inner product, \
    complete quadratic, majority) are not formalized."

register_result "odonnell-spectral-norm-products-restrictions" where
  title := "The spectral 1-norm is submultiplicative and does not increase under restriction"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercises 3.6 and 3.7(a)",
      locator := "arXiv:2105.10386v1, §3.6, printed p. 86" }
  ]
  theorems := [
    Cslib.BitString.sum_abs_fourierCoeff_mul_le,
    Cslib.BitString.sum_abs_fourierCoeff_piecewise_le
  ]
  scope := "Real functions f, g on the cube (ι → Bool) over a finite coordinate type, with \
    spectral norm ∑ S, |fourierCoeff f S|: the pointwise product fun x => f x * g x has spectral \
    norm at most the product of the spectral norms, and the restriction \
    fun x => f (J.piecewise x z), which keeps the coordinates in J free and fixes the others \
    to z, has spectral norm at most that of f. Exercise 3.7(b) (Fourier sparsity) is not \
    covered."

register_result "odonnell-small-bias-fools-spectral-norm" where
  title := "Small-bias distributions fool functions of small spectral norm and their squares"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Lemma 6.38 and Corollary 6.39",
      locator := "arXiv:2105.10386v1, §6.4, printed p. 157" }
  ]
  theorems := [
    Cslib.BitString.IsSmallBias.fools,
    Cslib.BitString.IsSmallBias.fools_sq
  ]
  scope := "A distribution X : PMF (ι → Bool) over a finite coordinate type with \
    IsSmallBias ε X (|bias X S| ≤ ε for every nonempty S, the book's ε-biased density) and \
    0 ≤ ε, and any real f on the cube: |∑ x, (X x).toReal * f x − 𝔼 x, f x| ≤ \
    (∑ S, |fourierCoeff f S|) * ε, and the same for fun x => f x ^ 2 with \
    (∑ S, |fourierCoeff f S|) ^ 2 * ε. The hypothesis 0 ≤ ε is needed (with no coordinates the \
    bias condition is vacuous). The sharper bounds of Exercise 6.32(a) are not formalized."

register_result "odonnell-derandomized-blr-test" where
  title := "Soundness of the Derandomized BLR Test with an ε-biased distribution"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 6.44 and Remark 6.45",
      locator := "arXiv:2105.10386v1, §6.4, printed p. 159 (proof to p. 160)" }
  ]
  theorems := [
    Cslib.BitString.exists_two_mul_derandomizedBLRAcceptance_sub_one_sq_sub_le_fourierCoeff_sq,
    Cslib.BitString.exists_le_abs_fourierCoeff_of_le_derandomizedBLRAcceptance,
    Cslib.BitString.exists_hammingDist_xor_parityOn_le_of_le_derandomizedBLRAcceptance,
    Cslib.BitString.exists_hammingDist_xor_parityOn_le_of_one_sub_le_derandomizedBLRAcceptance
  ]
  scope := "f : (ι → Bool) → Bool over a finite coordinate type, read as signs F = signVal ∘ f; \
    derandomizedBLRAcceptance X f is the probability, for x uniform and y ∼ X, that \
    (f x ^^ f y) = f (x + y); X satisfies IsSmallBias ε X with 0 ≤ ε. Spectral form: with \
    θ = 2 · acceptance − 1 of either sign, θ² − ε ≤ F̂(S)² for some S. For every real θ with \
    |θ| ≤ |2 · acceptance − 1| (the book's exact acceptance 1/2 + θ/2 of either sign, or \
    acceptance at least 1/2 + θ/2 with θ ≥ 0): √(θ² − ε) ≤ |F̂(S)| for some S, and f is within \
    relative Hamming distance 1/2 − √(θ² − ε)/2 of some b ^^ parityOn S; the bounds are \
    vacuous when θ² ≤ ε. Remark 6.45 is stated quantitatively: acceptance at least \
    1 − δ with δ < 1/2 gives distance at most δ + ε/(2(1 − 2δ)), an explicit bound that is not \
    in the book. The random-bit count n + O(log(n/ε)), a PCP.LocalTest packaging and \
    Exercises 6.32(b), 6.33 are not formalized."

register_result "odonnell-deterministic-fourier-estimation" where
  title := "Deterministic estimation of Fourier coefficients and bucket weights"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Propositions 6.40 and 6.41",
      locator := "arXiv:2105.10386v1, §6.4, printed pp. 157–158" }
  ]
  theorems := [
    Cslib.BitString.abs_sampleSpaceCoeff_sub_fourierCoeff_le,
    Cslib.BitString.exists_abs_sampleSpaceCoeff_sub_fourierCoeff_le,
    Cslib.BitString.abs_sampleSpaceBucketWeight_sub_bucketWeight_le,
    Cslib.BitString.exists_abs_sampleSpaceBucketWeight_sub_bucketWeight_le
  ]
  scope := "A sample space g : σ → ι → Bool over finite seeds is δ-biased when \
    IsSmallBias δ ((PMF.uniformOfFintype σ).map g). The coefficient estimate \
    sampleSpaceCoeff g f U = 𝔼 s, f (g s) * χ_U (g s) is within ‖f̂‖₁ δ of f̂(U) for real f and \
    0 ≤ δ; the bucket-weight estimate from g and a δ₂-biased h is within \
    2 ‖f̂‖₁ δ₁ + ‖f̂‖₁² δ₂ of bucketWeight f J S for real f with |f| ≤ 1 (the book takes \
    ±1-valued f). Each estimate reads f only at an explicit list of points (sampleSpacePoints, \
    sampleSpaceBucketPoints). The existence forms take a sample space from the powering \
    construction with at most 4 (n s / ε + 1)² seeds (4 (n (2 s + s²) / ε + 1)² for the bucket \
    weights) for accuracy ε when ‖f̂‖₁ ≤ s. The book's polynomial running time is not \
    certified by a machine model; Theorems 6.42 and 6.43 are not formalized."

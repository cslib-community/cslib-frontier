/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.CentralLimit
import CslibFrontier.Foundations.BooleanAnalysis.HammingBallWeight
import CslibFrontier.Foundations.BooleanAnalysis.MajorityInfluence

/-!
# Collected results: Hamming-ball degree-one weight via the CLT
-/

register_result "odonnell-hamming-ball-degree-one-limit" where
  title := "Mean and degree-one weight of Hamming balls tend to their Gaussian limits"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 5.25",
      locator := "arXiv:2105.10386v1, §5.4, printed p. 125" }
  ]
  theorems := [Cslib.BitString.tendsto_expect_hammingBall,
    Cslib.BitString.tendsto_levelWeight_one_hammingBall]
  scope := "For fixed real t, f_n is the 0/1 indicator of (√n)⁻¹ Σᵢ xᵢ > t on uniform \
    x ∈ {−1, 1}ⁿ, with x : Fin n → Bool read through signVal (false ↦ 1). As n → ∞, \
    E[f_n] → 1 − Φ(t), the book's complementary cdf, and W¹[f_n] → φ(t)², for the standard \
    Gaussian density φ and cdf Φ. Limits only, with no rate of convergence. The restatement \
    W¹[f_n] → U(α)² through the Gaussian isoperimetric function (Definition 5.26) is not stated."

register_result "odonnell-normalized-sign-sum-mean-absolute-limit" where
  title := "The mean absolute normalized sum of random signs tends to √(2/π)"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Equation (5.4)",
      locator := "arXiv:2105.10386v1, §5.2, printed p. 119" }
  ]
  theorems := [Cslib.BitString.tendsto_expect_abs_inv_sqrt_mul_sum_signVal]
  scope := "For uniform x ∈ {−1, 1}ⁿ, E[|Σᵢ xᵢ / √n|] → E[|Z|] = √(2/π) as n → ∞ along all n, \
    for a standard Gaussian Z. Limit only, with no rate of convergence. The central limit \
    theorem on the cube that gives it is a supporting step and is not registered."

register_result "odonnell-majority-total-influence-leading-term" where
  title := "Leading term of the total influence of majority"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 2.33",
      locator := "arXiv:2105.10386v1, §2.3, printed p. 51" }
  ]
  theorems := [Cslib.BitString.tendsto_totalInfluence_majority_div_sqrt,
    Cslib.BitString.tendsto_totalInfluence_majority_two_mul_add_one_div_sqrt]
  scope := "I[Maj_n] / √n → √(2/π), the leading term of I[Maj_n] = √(2/π) √n + O(n^{−1/2}); \
    a limit only, so neither the O(n^{−1/2}) error bound nor any rate is claimed, and the \
    theorem's other parts are not covered by this entry. The book's Maj_n is defined for odd \
    n: the odd statement takes n = 2m + 1 as m → ∞, where majority n is the book's Maj_n. The \
    all-n statement uses the library's majority n, which for even n breaks ties towards true \
    (sign −1)."

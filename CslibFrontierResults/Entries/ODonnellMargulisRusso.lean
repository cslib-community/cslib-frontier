/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.MargulisRusso

/-!
# Collected results: the Margulis–Russo formula
-/

register_result "odonnell-margulis-russo-formula" where
  title := "Margulis–Russo Formula: the derivative of a p-biased expectation"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Margulis–Russo Formula, equation (8.8)",
      locator := "arXiv:2105.10386v1, §8.4, printed p. 224; Definitions 8.39 and 8.40 of the \
        p-biased Fourier coefficient on printed pp. 220–221" }
  ]
  theorems := [Cslib.BitString.hasDerivAt_bernoulliAverage_one_sub_div_two]
  scope := "Any finite coordinate type ι, any h : (ι → Bool) → ℝ and 0 < p < 1, under \
    bernoulliAverage p, where each bit is true independently with probability p; true is the \
    source's −1, so a bit read through signVal has mean μ = 1 − 2p and standard deviation \
    σ = 2√(p(1 − p)). The source's E[f^{(p)}] as a function of μ is \
    m ↦ bernoulliAverage ((1 − m)/2) h, and its derivative at μ is σ⁻¹ Σᵢ f̂^{(p)}(i), with \
    σ = biasedStd p and f̂^{(p)}(i) = biasedFourierCoeff p h {i}, the p-biased Fourier \
    coefficient E_p[h · (signVal (x i) − μ)/σ] of Definitions 8.39 and 8.40."

register_result "odonnell-margulis-russo-monotone" where
  title := "Margulis–Russo Formula for monotone Boolean functions"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Margulis–Russo Formula, equation (8.9)",
      locator := "arXiv:2105.10386v1, §8.4, printed p. 225; Inf_i = σ² E[(D_{x_i} f)²] in the \
        proof of Proposition 8.45, printed p. 223; f^{(p)} for p ∈ (0, 1) in Notation 8.43, \
        printed p. 222" }
  ]
  theorems := [Cslib.BitString.hasDerivAt_bernoulliAverage_bitVal_sum_sq_derivative_of_monotone]
  scope := "Any finite coordinate type ι and f : (ι → Bool) → Bool monotone for false < true \
    (the source's monotonicity, with true read as −1). The identity holds as polynomials in p, \
    at every real p: the derivative of p ↦ bernoulliAverage p (bitVal ∘ f) is \
    Σᵢ E_p[(D_{x_i} f)²] for f read through signVal, with E_p the p-weighted sum. The left side \
    reads as Pr_p[f = true] only for p ∈ [0, 1], and the right side as the source's \
    I[f^{(p)}]/σ², since Inf_i[f^{(p)}] = σ² E_p[(D_{x_i} f)²], only for 0 < p < 1, where \
    Notation 8.43 defines f^{(p)} and σ² > 0: at p = 0 or 1 a dictator still has slope 1 while \
    σ² = 0. The p-biased influence itself is not defined. The middle term d/dμ E[f^{(p)}] of \
    (8.9) is not stated separately."

register_result "odonnell-monotone-strictly-increasing-p-biased" where
  title := "Nonconstant monotone functions have strictly increasing p-biased probability"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Remark 8.48",
      locator := "arXiv:2105.10386v1, §8.4, printed p. 225" }
  ]
  theorems := [Cslib.BitString.strictMonoOn_bernoulliAverage_bitVal_of_monotone]
  scope := "Any finite coordinate type ι and f : (ι → Bool) → Bool monotone for false < true and \
    taking two different values: p ↦ Pr_p[f = true] is strictly increasing on the closed \
    interval [0, 1]. The proof uses the expected number of pivotal coordinates in place of the \
    source's p-biased total influence."

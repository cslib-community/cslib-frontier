/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.BiasedFourier

/-!
# Collected results: `p`-biased Fourier analysis
-/

register_result "odonnell-p-biased-fourier-expansion" where
  title := "The p-biased Fourier basis is orthonormal and expands every function"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014,
      theorem := "Definition 8.40 (biased Fourier expansion) and Proposition 8.13 \
        (two-point p-biased case)",
      locator := "arXiv:2105.10386v1, §8.4, printed p. 221; basis function of Definition 8.39 \
        on printed p. 220; Proposition 8.13 in §8.1, printed p. 210" }
  ]
  theorems := [
    Cslib.BitString.bernoulliAverage_biasedChi_mul_biasedChi,
    Cslib.BitString.sum_biasedFourierCoeff_mul_biasedChi
  ]
  scope := "Proposition 8.13 is stated for every product Fourier basis of a finite product space; \
    this entry covers the case Ω = {−1, 1} with the basis {1, φ} of Definition 8.39 under π_p, \
    the setting of Definition 8.40. Any finite coordinate type ι, any f : (ι → Bool) → ℝ and \
    0 < p < 1, under bernoulliAverage p, where each bit is true independently with probability \
    p; true is the source's −1, so φ(false) = √(p/(1 − p)) is the source's φ(1). The characters \
    φ_S(x) = Π_{i ∈ S} φ(x i) are orthonormal and f = Σ_S f̂(S) φ_S with f̂(S) = E_p[f φ_S]. \
    The expansion is obtained from the point-indicator identity \
    1[x = y] = bernoulliWeight p y · Σ_S φ_S(x) φ_S(y), where bernoulliWeight p y = Π_i π_p(y i) \
    is the product mass at y, rather than from the source's dimension count."

register_result "odonnell-p-biased-parseval-plancherel" where
  title := "Mean, Parseval, variance, Plancherel and covariance in the p-biased Fourier basis"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 8.16 (p-biased basis on bits)",
      locator := "arXiv:2105.10386v1, §8.2, printed p. 211" }
  ]
  theorems := [
    Cslib.BitString.biasedFourierCoeff_empty,
    Cslib.BitString.bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq,
    Cslib.BitString.bernoulliAverage_sub_bernoulliAverage_sq_eq_sum_biasedFourierCoeff_sq,
    Cslib.BitString.bernoulliAverage_mul_eq_sum_biasedFourierCoeff_mul,
    Cslib.BitString.bernoulliAverage_sub_bernoulliAverage_mul_sub_bernoulliAverage_eq_sum
  ]
  scope := "Proposition 8.16 is stated for every product Fourier basis of a finite product space; \
    this entry covers the p-biased basis of Definitions 8.39 and 8.40 on bits, with all five \
    formulas. Any finite coordinate type ι and f, g : (ι → Bool) → ℝ. E_p[f] = f̂(∅) holds for \
    every real p (with bernoulliAverage p as the p-weighted sum); Parseval \
    E_p[f²] = Σ_S f̂(S)², the variance E_p[(f − E_p f)²] = Σ_{S ≠ ∅} f̂(S)², Plancherel \
    E_p[f g] = Σ_S f̂(S) ĝ(S) and the covariance \
    E_p[(f − E_p f)(g − E_p g)] = Σ_{S ≠ ∅} f̂(S) ĝ(S) take 0 < p < 1. The source's \
    inner product ⟨f, g⟩ is E_p[f g]."

register_result "odonnell-p-biased-dictator" where
  title := "The p-biased Fourier coefficients of a dictator"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Example 8.41",
      locator := "arXiv:2105.10386v1, §8.4, printed p. 221" }
  ]
  theorems := [Cslib.BitString.biasedFourierCoeff_dictator]
  scope := "Any finite coordinate type ι, any coordinate i and 0 < p < 1: the dictator \
    x ↦ signVal (x i), with true read as the source's −1, has p-biased coefficient μ = 1 − 2p on \
    ∅, σ = 2√(p(1 − p)) on {i} and 0 on every other set."

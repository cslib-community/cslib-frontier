/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.MajorityStability
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ArcsinSeries

/-!
# Collected results: the limiting spectrum and noise stability of majority
-/

register_result "odonnell-majority-noise-stability-limit" where
  title := "The noise stability of majority tends to (2/π) arcsin ρ"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 2.45",
      locator := "arXiv:2105.10386v1, §2.4, printed p. 54" }
  ]
  theorems := [Cslib.BitString.tendsto_noiseStability_signVal_majority,
    Cslib.BitString.tendsto_noiseSensitivity_majority]
  scope := "For every ρ ∈ [−1, 1], Stab_ρ of majority of 2m + 1 bits (read as signs) tends to \
    (2/π) arcsin ρ as m → ∞; equivalently, for δ ∈ [0, 1], NS_δ tends to arccos(1 − 2δ)/π. \
    Limits only, with no rate. Proved through the level weights (Theorem 5.22) and the arcsin \
    series, not the multidimensional central limit theorem."

register_result "odonnell-majority-level-weight-limit" where
  title := "The Fourier weight of majority at each odd level tends to [ρ^k] (2/π) arcsin ρ"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 5.22",
      locator := "arXiv:2105.10386v1, §5.3, printed p. 123" }
  ]
  theorems := [Cslib.BitString.tendsto_levelWeight_signVal_majority,
    Cslib.BitString.le_levelWeight_signVal_majority,
    Cslib.BitString.levelWeight_signVal_majority_le]
  scope := "For each j, W^(2j+1) of majority of 2m + 1 bits tends to (2/π) C(2j, j)/(4^j (2j + 1)) \
    as m → ∞; it is at least this limit for every m ≥ j and at most (1 + 2k/n) times it for \
    k = 2j + 1 < n/2 = (2m + 1)/2, the error bound (5.15). The book also states that the \
    weights decrease in n (Corollary 5.21, registered separately)."

register_result "odonnell-majority-level-weight-asymptotics" where
  title := "The level weights of majority are (2/π)^(3/2) k^(−3/2) (1 ± O(1/k))"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Corollary 5.23 and Exercise 5.27(a)",
      locator := "arXiv:2105.10386v1, §5.3, printed p. 124; §5.6, printed p. 137" }
  ]
  theorems := [Cslib.BitString.two_div_pi_mul_centralBinom_div_mem_Icc,
    Cslib.BitString.levelWeight_signVal_majority_mem_Icc,
    Cslib.BitString.sum_Ioc_levelWeight_signVal_majority_le,
    Cslib.BitString.le_sum_Ioc_levelWeight_signVal_majority,
    Cslib.BitString.sum_fourierCoeff_sq_signVal_majority_le]
  scope := "For odd k = 2j + 1: (2/π)^(3/2) k^(−3/2) ≤ [ρ^k] (2/π) arcsin ρ ≤ \
    (2/π)^(3/2) k^(−3/2) (1 + 1/k); and for n = 2m + 1 ≥ 2k², W^k of majority of n bits lies \
    between (2/π)^(3/2) k^(−3/2) and (2/π)^(3/2) k^(−3/2) (1 + 1/k)²; W^{>k} of majority lies \
    between (2/π)^(3/2) k^(−1/2) (1 − 3/k) (for n ≥ 2k²) and (2/π)^(3/2) k^(−1/2) (1 + 1/k) (for \
    every n); and for every ε > 0 the weight above any degree d ≥ 8/(π³ε²) + 4 is at most ε."

register_result "odonnell-majority-noise-stability-bounds" where
  title := "The noise stability of majority is within O(1/√((1 − ρ²) n)) above (2/π) arcsin ρ"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 5.18 (bounds)",
      locator := "arXiv:2105.10386v1, §5.2, printed p. 121" }
  ]
  theorems := [Cslib.BitString.le_noiseStability_signVal_majority,
    Cslib.BitString.noiseStability_signVal_majority_le]
  scope := "For majority of n = 2m + 1 bits read as signs: (2/π) arcsin ρ ≤ Stab_ρ for \
    0 ≤ ρ ≤ 1, and Stab_ρ ≤ (2/π) arcsin ρ + 3/√((1 − ρ²) n) for 0 ≤ ρ < 1, the book's \
    O(1/(√(1 − ρ²) √n)) with the constant 3. The monotonicity in n is registered separately \
    (Theorem 5.18, monotonicity in n)."

register_result "odonnell-arcsin-series" where
  title := "The Maclaurin series of arcsin"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Equation (5.9) and Exercise 5.18",
      locator := "arXiv:2105.10386v1, §5.3, printed p. 122; §5.6, printed p. 136" }
  ]
  theorems := [Real.hasSum_centralBinom_div_four_pow_mul_pow_two_mul, Real.hasSum_arcsin]
  scope := "1/√(1 − z²) = Σ C(2n, n)/4^n z^(2n) for |z| < 1 (part (a)), and \
    arcsin z = Σ C(2n, n)/(4^n (2n + 1)) z^(2n + 1) for |z| ≤ 1, including the endpoints \
    (parts (b) and (c))."

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
    Cslib.BitString.le_levelWeight_signVal_majority]
  scope := "For each j, W^(2j+1) of majority of 2m + 1 bits tends to (2/π) C(2j, j)/(4^j (2j + 1)) \
    as m → ∞, and is at least this limit for every m ≥ j (the lower half of (5.15)). The upper \
    half of (5.15), W^k ≤ (1 + 2k/n) times the limit, is not covered."

register_result "odonnell-majority-noise-stability-lower-bound" where
  title := "The noise stability of majority is at least (2/π) arcsin ρ"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 5.18 (lower bound)",
      locator := "arXiv:2105.10386v1, §5.3, printed p. 121" }
  ]
  theorems := [Cslib.BitString.le_noiseStability_signVal_majority]
  scope := "For 0 ≤ ρ ≤ 1 and every m, (2/π) arcsin ρ ≤ Stab_ρ of majority of 2m + 1 bits, the \
    closed interval containing the book's [0, 1). The upper bound \
    (2/π) arcsin ρ + O(1/√(1 − ρ²) · 1/√n) is not covered."

register_result "odonnell-arcsin-series" where
  title := "The Maclaurin series of arcsin"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Equation (5.9) and Exercise 5.18(a)–(b)",
      locator := "arXiv:2105.10386v1, §5.3, printed p. 122; §5.6, printed p. 136" }
  ]
  theorems := [Real.hasSum_centralBinom_div_four_pow_mul_pow_two_mul, Real.hasSum_arcsin]
  scope := "For |z| < 1: 1/√(1 − z²) = Σ C(2n, n)/4^n z^(2n) and \
    arcsin z = Σ C(2n, n)/(4^n (2n + 1)) z^(2n + 1). The endpoints z = ±1 (Exercise 5.18(c)) are \
    not covered."

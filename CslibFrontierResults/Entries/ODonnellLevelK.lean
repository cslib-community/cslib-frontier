/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.LevelK

/-!
# Collected results: the Level-k Inequalities
-/

register_result "odonnell-low-degree-weight-three-pow" where
  title := "Low-degree weight of a small set from Corollary 9.8"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Inequality (9.7)",
      locator := "arXiv:2105.10386v1, §9.2, printed p. 256" }
  ]
  theorems := [Cslib.BitString.sum_filter_card_le_fourierCoeff_indicator_sq_le_three_pow]
  scope := "Uniform cube on any finite coordinate type; the source's f : {−1, 1}ⁿ → {0, 1} is \
    the indicator A.indicator 1 of an arbitrary set A, with α = 𝔼 1_A. For every natural k, the \
    Fourier weight Σ_{|S| ≤ k} 1̂_A(S)², the empty set included, is at most 3^k α^(3/2)."

register_result "odonnell-level-k-inequalities" where
  title := "Level-k Inequalities"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Level-k Inequalities",
      locator := "arXiv:2105.10386v1, §9.5, printed p. 264" }
  ]
  theorems := [Cslib.BitString.sum_filter_card_le_fourierCoeff_indicator_sq_le_log_pow]
  scope := "Uniform cube on any finite coordinate type; the source's f : {−1, 1}ⁿ → {0, 1} is \
    the indicator A.indicator 1 of an arbitrary set A, with α = 𝔼 1_A. For every natural k with \
    1 ≤ k ≤ 2 ln(1/α), which forces 0 < α < 1, the Fourier weight Σ_{|S| ≤ k} 1̂_A(S)², the \
    empty set included, is at most (2e/k · ln(1/α))^k α², with the natural logarithm."

register_result "odonnell-degree-one-weight-noise-stability" where
  title := "Degree-one weight of a set through small-set expansion"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 9.18(a)",
      locator := "arXiv:2105.10386v1, §9.7, printed p. 273" }
  ]
  theorems := [Cslib.BitString.levelWeight_one_indicator_le_rpow]
  scope := "Uniform cube on any finite coordinate type; the source's f : {−1, 1}ⁿ → {0, 1} is \
    the indicator A.indicator 1 of an arbitrary set A, with α = 𝔼 1_A. For 0 < ρ ≤ 1, \
    W¹[1_A] ≤ (α^(2/(1 + ρ)) − α²)/ρ."

register_result "odonnell-sharp-level-one-inequality" where
  title := "Sharp Level-1 Inequality for {0, 1}-valued functions"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 9.18(b) (sharp Level-1 Inequality)",
      locator := "arXiv:2105.10386v1, §9.7, printed p. 273; stated in Remark 5.28, §5.4, \
        printed p. 126" }
  ]
  theorems := [Cslib.BitString.levelWeight_one_indicator_le]
  scope := "Uniform cube on any finite coordinate type; the source's f : {−1, 1}ⁿ → {0, 1} is \
    the indicator A.indicator 1 of an arbitrary set A, with α = 𝔼 1_A, and every α in [0, 1] \
    is allowed: W¹[1_A] ≤ 2α² ln(1/α), with the natural logarithm (both sides are 0 at α = 0). \
    This is the {0, 1}-valued case of Remark 5.28; the remark's further claim for \
    f : {−1, 1}ⁿ → [−1, 1] with α = 𝔼|f| is not covered."

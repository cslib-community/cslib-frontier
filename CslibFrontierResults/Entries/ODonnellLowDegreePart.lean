/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Analysis.LpNorm
import CslibFrontier.Foundations.BooleanAnalysis.LowDegreePart

/-!
# Collected results: the low-degree part in L^q
-/

register_result "odonnell-lp-norm-monotone-in-p" where
  title := "L^p norms increase with p"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 1.13",
      locator := "arXiv:2105.10386v1, §1.7, printed p. 37" }
  ]
  theorems := [Cslib.lpNorm_le_lpNorm_of_exponent_le]
  scope := "For a real function on any finite type under the uniform distribution, \
    ‖f‖_p ≤ ‖f‖_q for real 0 < p ≤ q, where ‖f‖_p = (𝔼 |f|^p)^(1/p). The book states it on the \
    cube {−1, 1}^n; the empty type is included. The extension to q = ∞ in the same exercise is \
    not covered."

register_result "odonnell-low-degree-projection-lq" where
  title := "Low-degree projection is bounded in L^q"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 10.37",
      locator := "arXiv:2105.10386v1, §10.4, printed p. 299" }
  ]
  theorems := [Cslib.BitString.lpNorm_lowDegreePart_le,
    Cslib.BitString.lpNorm_lowDegreePart_le_of_le_two]
  scope := "Real functions f on the uniform cube over any finite coordinate type, every k ∈ ℕ, \
    and f^{≤k} = ∑_{|S| ≤ k} f̂(S) χ_S: ‖f^{≤k}‖_q ≤ √(q − 1)^k ‖f‖_q for every real q ≥ 2, \
    and ‖f^{≤k}‖_q ≤ (1/√(q − 1))^k ‖f‖_q for every real 1 < q ≤ 2. Both ranges are also \
    Exercise 9.8(a) and (b) (§9.7, printed p. 271)."

register_result "odonnell-low-degree-part-noise-lq" where
  title := "The low-degree part against the noise operator in L^q"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Lemma 10.38",
      locator := "arXiv:2105.10386v1, §10.4, printed p. 300" }
  ]
  theorems := [Cslib.BitString.lpNorm_lowDegreePart_le_noiseOp]
  scope := "Real functions f on the uniform cube over any finite coordinate type, every k ∈ ℕ \
    and 0 < ρ ≤ 1: ‖f^{≤k}‖_q ≤ (√(q − 1)/ρ)^k ‖T_ρ f‖_q for every real q ≥ 2. The book \
    states only q = 4, ‖f^{≤k}‖_4 ≤ (√3/ρ)^k ‖T_ρ f‖_4, which is the instance q = 4."

/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.KahnKalaiLinial

/-!
# Collected results: large degree-one coefficients of monotone functions
-/

register_result "odonnell-monotone-large-degree-one-coefficient" where
  title := "A nonconstant monotone function has a large degree-one Fourier coefficient"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Exercise 9.33",
      locator := "arXiv:2105.10386v1, §9.7, printed p. 276" }
  ]
  theorems := [Cslib.BitString.exists_exp_neg_le_fourierCoeff_singleton_sq_of_monotone]
  scope := "For every monotone f : (ι → Bool) → Bool over a finite coordinate type ι with \
    ∃ x y, f x ≠ f y, read as signs F through signVal (false ↦ 1), some coordinate i has \
    exp (-(10 · I / V)) ≤ fourierCoeff F {i} ^ 2, where I = totalInfluence F and \
    V = 𝔼 x, (F x - 𝔼 y, F y) ^ 2. The book asks for some S ≠ ∅ with \
    f̂(S)² ≥ exp(−O(I[f]/Var[f])); this takes S a singleton, as the book's hint allows, and \
    fixes the constant in O(·) to 10. Monotonicity is for the pointwise order on Bool with \
    false < true; reading inputs and outputs through signVal reverses both orders, so this is \
    the book's monotonicity on {−1, 1}."

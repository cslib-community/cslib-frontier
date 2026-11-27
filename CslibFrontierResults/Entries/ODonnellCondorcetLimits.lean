/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.CondorcetLimits

/-!
# Collected results: Guilbaud's formula and the Condorcet bound for fair voting rules
-/

register_result "odonnell-guilbaud-formula" where
  title := "Guilbaud's formula for the probability of a Condorcet winner under majority"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Guilbaud's Formula (unnumbered)",
      locator := "arXiv:2105.10386v1, §2.5, printed p. 60" }
  ]
  theorems := [Cslib.BitString.tendsto_condorcetWinnerProb_majority]
  scope := "Under impartial culture, the probability of a Condorcet winner in the 3-candidate \
    Condorcet election using majority of 2m + 1 voters tends to (3/(2π)) arccos(−1/3) as \
    m → ∞. Limit only, with no rate."

register_result "odonnell-equal-coefficients-degree-one-weight" where
  title := "Equal degree-one coefficients force W¹ ≤ 2/π + o(1)"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Proposition 2.58",
      locator := "arXiv:2105.10386v1, §2.5, printed p. 60" }
  ]
  theorems := [Cslib.BitString.card_mul_levelWeight_one_le_of_fourierCoeff_singleton_eq,
    Cslib.BitString.eventually_levelWeight_one_le_of_fourierCoeff_singleton_eq]
  scope := "For f : BooleanFunction n read as signs with all degree-one coefficients equal: \
    n W¹[f] ≤ E[|x₁ + ⋯ + xₙ|]² exactly, and for every ε > 0, eventually in n, \
    W¹[f] ≤ 2/π + ε. Exercise 2.24's rate O(1/n) is not covered."

register_result "odonnell-condorcet-equal-coefficients-bound" where
  title := "Fair voting rules have a Condorcet winner with probability at most 7/9 + 4/(9π) + o(1)"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 2.57",
      locator := "arXiv:2105.10386v1, §2.5, printed p. 60" }
  ]
  theorems := [Cslib.BitString.eventually_condorcetWinnerProb_le]
  scope := "For every ε > 0, eventually in n, every rule f : BooleanFunction n whose degree-one \
    Fourier coefficients (read as signs) are all equal has probability of a Condorcet winner at \
    most 7/9 + 4/(9π) + ε under impartial culture. The tight value of Chapter 11.7 is not \
    covered."

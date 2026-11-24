/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.BooleanAnalysis.FriedgutJunta

/-!
# Collected results: concentration on the influential coordinates
-/

register_result "odonnell-concentration-on-influential-coordinates" where
  title := "A Boolean function's spectrum concentrates on its influential coordinates and high \
    degree, and with low-degree concentration it is close to a junta on them"
  topic := "analysis of Boolean functions"
  sources := [
    { paper := ODonnell2014, theorem := "Theorem 9.28",
      locator := "arXiv:2105.10386v1, §9.6, printed pp. 268–269" }
  ]
  theorems := [
    Cslib.BitString.card_filter_le_influence_le_div_of_totalInfluence_le,
    Cslib.BitString.sum_filter_not_subset_and_card_le_fourierCoeff_sq_le_of_totalInfluence_le,
    Cslib.BitString.sum_filter_not_subset_or_lt_card_fourierCoeff_sq_le,
    Cslib.BitString.exists_dependsOn_hammingDist_div_le_of_sum_lt_card_fourierCoeff_sq_le
  ]
  scope := "For f : (ι → Bool) → Bool over a finite coordinate type ι, read as signs F through \
    signVal (false ↦ 1), any bound K ≥ I[F] in place of the book's I[f], k : ℕ and the threshold \
    τ = ε² / (K² 9ᵏ). The count is stated for every τ > 0: at most K / τ coordinates have \
    influence at least τ, which is K³ 9ᵏ / ε² at the book's τ. The other parts take any J \
    containing every coordinate of influence more than τ (the book's J = {j : Inf_j ≥ τ} is one): \
    for ε ≥ 0 the weight on the sets S ⊄ J with |S| ≤ k is at most ε / 3, sharper than the \
    book's ε; if moreover the weight above degree k is at most ε, the weight outside \
    {S ⊆ J : |S| ≤ k} is at most 2ε and f is at relative Hamming distance at most ε from a \
    Boolean function depending only on the coordinates in J (Mathlib's DependsOn). The book's \
    0 < ε ≤ 1 is not assumed. The last step uses the sign of the average of F over the \
    coordinates outside J, which is within half the weight outside the subsets of J; this is \
    the instance of Exercise 3.34 the book cites, with deterministic rounding in place of the \
    exercise's random threshold, and Exercise 3.34 is not stated in general."

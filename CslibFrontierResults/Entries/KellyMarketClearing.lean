/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.ResourceAllocation.MarketClearing

/-!
# Collected results: smooth market-clearing characterization and 3/4 optimality (NRTV §21.3)

Registers Theorem 21.10 of Nisan–Roughgarden–Tardos–Vazirani ([Johari2007], Chapter 21, §21.3)
and Johari–Tsitsiklis ([JohariTsitsiklis2009]) formalized in
`CslibFrontier.GameTheory.ResourceAllocation.MarketClearing`.
-/

section
open Cslib.GameTheory

register_result "johari-tsitsiklis-market-clearing-characterization" where
  title := "Johari–Tsitsiklis characterization of smooth market-clearing mechanisms and 3/4 \
    optimality of proportional sharing"
  topic := "game theory"
  sources := [
    { paper := Johari2007,
      theorem := "Theorem 21.10",
      locator := "Chapter 21, §21.3, p. 554 (proof pp. 555–558)" },
    { paper := JohariTsitsiklis2009,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    IsMarketCompetitiveEquilibrium.isSocialOptimum,
    IsRegularMarketClearing.exists_isMarketCompetitiveEquilibrium,
    IsRegularMarketClearing.exists_priceScale,
    IsRegularMarketClearing.marketAllocation_eq_kellyAllocation,
    IsRegularMarketClearing.existsUnique_isMarketNashEquilibrium,
    IsRegularMarketClearing.efficiencyRatio_le_three_fourths,
    IsRegularMarketClearing.efficiencyRatio_eq_three_fourths_iff
  ]
  scope := "Single infinitely divisible resource of positive capacity C > 0 shared among at least \
    two users (2 ≤ Fintype.card ι) with admissible utilities IsAdmissibleUtility (concave, \
    strictly increasing, and differentiable within [0, ∞), matching Assumption 1 of \
    [Johari2007] §21.2). IsRegularMarketClearing formalizes the mechanism class 𝒟 of \
    Definition 21.8 with ∃ θ ≥ 0, D p θ = d in Condition (iii) rather than the printed \
    ∃ θ > 0, D p θ = d on p. 553 (which at d = 0 would exclude D(p, θ) = θ p^(-1/c) of \
    Example 21.9 and D(p, θ) = θ / B(p) of Theorem 21.10(ii) and make 𝒟 empty). \
    efficiencyRatio ranges over admissible utilities satisfying U_r(0) ≥ 0 (matching p. 554 and \
    Theorem 21.4); since IsRegularMarketClearing.existsUnique_isMarketNashEquilibrium proves \
    every D ∈ 𝒟 admits a unique Nash equilibrium on every admissible instance, the source's -∞ \
    fallback for nonexistence never triggers on 𝒟."

end

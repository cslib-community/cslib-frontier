/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.UtilityGame.Basic
import CslibFrontier.GameTheory.UtilityGame.CompetitiveFacilityLocation

/-!
# Collected results: Vetta's utility games and competitive facility location (NRTV Section 19.4)
-/

open Cslib.GameTheory
open Cslib.GameTheory.UtilityGame

register_result "nrtv-competitive-facility-location-potential" where
  title := "Competitive facility location is an exact potential game with social welfare \
    as potential"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Theorem 19.16",
      locator := "Section 19.4.2, pp. 503–504" }
  ]
  theorems := [
    CompetitiveFacilityLocation.isExactPotential,
    CompetitiveFacilityLocation.profit_sub_profit_eq
  ]
  scope := "Finite provider set ι and finite client set J with arbitrary real reservation values \
    value j and connection costs serviceCost j i a. Second-cheapest pricing secondPrice j s i \
    caps competitor connection costs at value j (agreeing with min_{i' ≠ i} c_{j, s_{i'}} \
    whenever c ≤ π and at least two providers exist, proved in secondPrice_eq_inf'). Proves \
    both the payoff-form unilateral deviation identity profit_sub_profit_eq and \
    CostGame.IsExactPotential (-socialWelfare ∘ profileSet) on toCostGame."

register_result "nrtv-competitive-facility-location-pos-fip" where
  title := "Pure equilibrium existence, price of stability 1, and convergence in facility location"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Corollary 19.17",
      locator := "Section 19.4.2, p. 504" }
  ]
  theorems := [
    CompetitiveFacilityLocation.exists_isPureNash,
    CompetitiveFacilityLocation.isPureNash_of_forall_socialWelfare_le,
    CompetitiveFacilityLocation.exists_isPureNash_forall_socialWelfare_le,
    CompetitiveFacilityLocation.hasFIP,
    CompetitiveFacilityLocation.exists_reflTransGen_isPureNash,
    CompetitiveFacilityLocation.exists_competitiveFacilityLocation_poa_eq_two
  ]
  scope := "For finite nonempty provider strategy sets S i and finite client set J: pure Nash \
    equilibria exist, every welfare-maximizing profile is a pure Nash equilibrium (so the price \
    of stability is 1), all improvement and best-response sequences terminate (HasFIP) and reach \
    a pure Nash equilibrium from any initial profile, and equilibria need not be socially optimal \
    (witnessed on 2 providers and 2 clients attaining exact PoA = 2)."

register_result "nrtv-competitive-facility-location-monotone-basic-utility" where
  title := "Competitive facility location is a monotone basic utility game"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Theorem 19.18",
      locator := "Section 19.4.3, p. 505" }
  ]
  theorems := [
    CompetitiveFacilityLocation.isBasic_toUtilityGame,
    CompetitiveFacilityLocation.isValid_toUtilityGame,
    CompetitiveFacilityLocation.monotone_socialWelfare
  ]
  scope := "Player-tagged ground set Σ i, S i models the disjoint union of provider location \
    sets. Proves Submodular.IsSubmodular socialWelfare, total profit budget ∑ i, profit i s ≤ \
    socialWelfare (profileSet s), exact marginal contribution profit i s = V(s) - V(s - s_i) \
    (IsBasic), and Monotone socialWelfare without restricting cost signs."

register_result "nrtv-monotone-utility-game-poa-two" where
  title := "Price of anarchy at most 2 for monotone utility games"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Theorem 19.19",
      locator := "Section 19.4.4, p. 505 and Section 19.5.3, p. 511" },
    { paper := Vetta2002,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    UtilityGame.IsValid.profileValue_le_two_mul_of_isPureNash,
    UtilityGame.IsValid.profileValue_le_two_mul_expected_of_isMixedNash
  ]
  scope := "For any finite player set ι and any UtilityGame satisfying IsValid (submodular \
    socialValue, total utility at most social welfare, utility at least marginal welfare \
    contribution) with Monotone socialValue: every pure Nash equilibrium s satisfies \
    profileValue o ≤ 2 * profileValue s for all profiles o, and the same factor-2 welfare bound \
    holds in expectation for all mixed Nash equilibria."

register_result "nrtv-monotone-basic-utility-random-best-response" where
  title := "Transient expected welfare bound for random best-response moves in basic utility games"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Theorem 19.20",
      locator := "Section 19.4.5, p. 506" },
    { paper := MirrokniVetta2004,
      theorem := unverified,
      locator := unverified },
    { paper := GoemansMirrokniVetta2005,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    UtilityGame.IsBasic.profileValue_le_expected_step_gain,
    UtilityGame.IsBasic.profileValue_sub_two_mul_expectedWalkValue_le,
    UtilityGame.IsBasic.mul_profileValue_le_expectedWalkValue
  ]
  scope := "In a monotone basic utility game with n = Fintype.card ι ≥ 1 players and \
    0 ≤ socialValue ∅, under any best-response selector IsBestResponse br (proved to exist on \
    finite nonempty strategy sets by exists_isBestResponse), t uniformly random player \
    best-response steps from any starting profile s₀ satisfy (1 / 2 - ε) * profileValue o ≤ \
    expectedWalkValue br s₀ t for every ε > 0 and profile o whenever (n / 2) * log (1 / ε) ≤ t."

register_result "nrtv-neighborhood-location-utility-game-tightness" where
  title := "Closed-neighborhood wealth-sharing location game is a valid utility game with PoA → 2"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Exercise 19.16",
      locator := "Exercises, p. 515" }
  ]
  theorems := [
    UtilityGame.isValid_neighborhoodGame,
    UtilityGame.monotone_neighborhoodGame_socialValue,
    UtilityGame.exists_neighborhoodGame_isPureNash_mul_lt
  ]
  scope := "Both parts (a) and (b) on finite undirected SimpleGraph instances: part (b) proves \
    neighborhoodGame satisfies IsValid and Monotone; part (a) constructs for every ε > 0 a \
    (k + 2)-player graph with a pure Nash equilibrium s of positive welfare and profile o \
    satisfying (2 - ε) * profileValue s < profileValue o."

register_result "nrtv-facility-location-opening-costs" where
  title := "Competitive facility location with opening costs: unbounded PoA and 2 V(S) + F bound"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Exercise 19.17",
      locator := "Section 19.5.3, p. 511 and Exercises, p. 515" }
  ]
  theorems := [
    CompetitiveFacilityLocation.isBasic_withOpeningCost,
    CompetitiveFacilityLocation.netWelfare_le_two_mul_add_openingCost_of_isPureNash,
    CompetitiveFacilityLocation.exists_withOpeningCost_poa_gt
  ]
  scope := "Both parts (a) and (b): part (a) proves that for every constant C, a 2-provider, \
    1-client instance with nonnegative opening costs and 0 ≤ c ≤ π admits a pure Nash \
    equilibrium s with 0 < V_f(s) and C * V_f(s) < V_f(o); part (b) proves V_f(o) ≤ 2 * V_f(s) \
    + ∑ i, f(i, s i) at every pure Nash equilibrium s."

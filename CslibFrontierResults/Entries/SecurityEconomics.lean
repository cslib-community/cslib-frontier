/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Security.Interdependent
import CslibFrontier.GameTheory.Security.SystemReliability

/-!
# Collected results: Economics of security — system reliability and interdependent security games
-/

register_result "varian-system-reliability-equilibria-and-welfare" where
  title := "Equilibria, underprovision, wrong-agent allocation, group-size comparative statics, \
    and liability internalization in Varian's total-effort, weakest-link, and best-shot system \
    reliability games"
  topic := "game theory"
  sources := [
    { paper := Varian2004,
      theorem := "Facts 1, 2, 3, 4, 5, 7, 8, and 9, and §3.3 best-shot analysis",
      locator := "§§3.1–7.2, pp. 3–11" }
  ]
  theorems := [
    Cslib.GameTheory.SystemReliabilitySpec.isPureNash_totalEffortGame_iff,
    Cslib.GameTheory.SystemReliabilitySpec.eq_single_of_isPureNash_totalEffortGame,
    Cslib.GameTheory.SystemReliabilitySpec.socialCost_totalEffortGame_single_le,
    Cslib.GameTheory.SystemReliabilitySpec.totalEffort_le_socialOpt_of_isPureNash,
    Cslib.GameTheory.SystemReliabilitySpec.totalEffort_lt_socialOpt_of_isPureNash,
    Cslib.GameTheory.SystemReliabilitySpec.wrongAgent_support_disjoint,
    Cslib.GameTheory.SystemReliabilitySpec.isPureNash_weakestLinkGame_const_inf,
    Cslib.GameTheory.SystemReliabilitySpec.isPureNash_weakestLinkGame_iff,
    Cslib.GameTheory.SystemReliabilitySpec.cost_weakestLinkGame_const_inf_le_of_isPureNash,
    Cslib.GameTheory.SystemReliabilitySpec.weakestLink_socialOpt_le_totalEffort_socialOpt,
    Cslib.GameTheory.SystemReliabilitySpec.prob_totalEffort_le_of_subset_of_isPureNash,
    Cslib.GameTheory.SystemReliabilitySpec.prob_weakestLink_le_of_subset_of_isPureNash,
    Cslib.GameTheory.SystemReliabilitySpec.identicalAgents_weakestLink_socialOpt_isPureNash,
    Cslib.GameTheory.SystemReliabilitySpec.isPureNash_totalEffortLiabilityGame_single,
    Cslib.GameTheory.SystemReliabilitySpec.isPureNash_weakestLinkNegligenceGame_const,
    Cslib.GameTheory.SystemReliabilitySpec.isPureNash_bestShotGame_single_iff,
    Cslib.GameTheory.SystemReliabilitySpec.isPureNash_bestShotGame_champion,
    Cslib.GameTheory.SystemReliabilitySpec.exists_eq_single_of_isPureNash_bestShotGame
  ]
  scope := "Finite player sets [Fintype ι] choosing nonnegative continuous efforts x : ι → ℝ≥0 in \
    CostGame minimization form val i * (1 - prob (agg x)) + unitCost i * x i (strategically \
    equivalent to maximizing Varian's expected net payoff val i * prob (agg x) - unitCost i * x i \
    up to the profile-independent constant val i, surveyed qualitatively in \
    Anderson–Moore–Nagaraja–Ozment 2007, Chapter 25, §25.2.1, printed p. 635), allowing boundary \
    corner standalone optima xBar i = 0 as well as interior first-order optima via \
    isStandaloneOpt_of_hasDerivAt. isPureNash_weakestLinkGame_iff explicitly records \
    [Nontrivial ι] (|ι| ≥ 2) for the [0, inf_i xBar i] continuum, since |ι| = 1 admits only \
    xBar i₀; Fact 5 is proved on equilibrium system reliability prob (totalEffort _) and \
    prob (weakestLink _) across sub-populations S ⊆ T via SystemReliabilitySpec.restrict. \
    Original robust ((∑ i, c_i) / c_min) / |ι| Price-of-Anarchy bounds are kept separate from \
    this entry. Sequential two-player moves (§8, Facts 10–12, pp. 11–13), adversaries (§9, \
    pp. 13–14), combined sum-of-efforts and weakest-link technologies (§10, pp. 14–15), and \
    imperfect-information future work (§11, p. 15) are not covered."

register_result "kunreuther-heal-interdependent-security-and-tipping" where
  title := "Contagion limits, symmetric pure Nash equilibria, Pigouvian taxation, and tipping \
    cascades in Kunreuther–Heal interdependent security games"
  topic := "game theory"
  sources := [
    { paper := KunreutherHeal2003,
      theorem := "Proposition 1, Corollary 1, §2 symmetry of pure Nash equilibria, and §3 \
        Pigouvian non-investment tax",
      locator := "§§2–3, NBER PDF pp. 3–13 (J. Risk Uncertain. 26(2–3), 231–249)" },
    { paper := HealKunreuther2007,
      theorem := "Theorems 1, 2, and 3, Definition 2, and §5.2 multi-round tipping cascades",
      locator := "§§3 and 5.2, and Appendix p. 20, Wharton PDF pp. 6–16, 20 (Risk Analysis \
        27(3), 621–634)" }
  ]
  theorems := [
    Cslib.GameTheory.InterdependentSecuritySpec.isPureNash_toCostGame_iff,
    Cslib.GameTheory.InterdependentSecuritySpec.isPureNash_iterate_bestResponse_bot,
    Cslib.GameTheory.InterdependentSecuritySpec.exists_isPureNash,
    Cslib.GameTheory.InterdependentSecuritySpec.coexistence_pureNash_iff_and_pareto,
    Cslib.GameTheory.InterdependentSecuritySpec.IsCriticalCoalition.tipsAll,
    Cslib.GameTheory.InterdependentSecuritySpec.isPureNash_allTrue_of_tipsAll,
    Cslib.GameTheory.InterdependentSecuritySpec.isCriticalCoalition_of_higher_contagion,
    Cslib.GameTheory.symmetricIDSSpec_cost_allFalse_eq_geom_sum,
    Cslib.GameTheory.symmetricIDSSpec_criticalCost_eq_geom_sum,
    Cslib.GameTheory.tendsto_symmetricIDSSpec_cost_allFalse_atTop,
    Cslib.GameTheory.eventually_not_dominant_invest_symmetricIDSSpec,
    Cslib.GameTheory.eq_const_of_isPureNash_symmetricIDSSpec,
    Cslib.GameTheory.isCoarseCorrelatedEquilibrium_symmetricIDSSpec_taxed_unique
  ]
  scope := "Finite Class 1 (partial-protection) binary interdependent security games \
    (CostGame ι (fun _ => Bool)) with non-additive direct and peer-contagion losses (surveyed \
    qualitatively in Anderson–Moore–Nagaraja–Ozment 2007, Chapter 25, §25.2.1, printed p. 635). \
    For Heal–Kunreuther (2007) Theorem 3, isCriticalCoalition_of_higher_contagion adds \
    normalized-reluctance alignment c_k / (p_k L_k) ≤ c_j / (p_j L_j) on replaced vs. replacing \
    agents (automatic for homogeneous (p, L, c)), correcting an omitted k ∈ M' \\ M case in \
    Appendix eq. (17) (p. 20) witnessed by checked Fin 3 and Fin 4 counterexamples in \
    CslibFrontierTests.GameTheory.SecurityEconomics. Original extensions in the same module \
    (public-signal correlated equilibria, the 2-agent mixed-vs-correlated strict cost gap, \
    Roughgarden (1, μ)-smoothness CCE Price of Anarchy, and the 1 + n q Prisoner's Dilemma \
    social-cost ratio) are omitted from this source-attributed entry. Insurance, \
    bankruptcy/limited liability, multi-period discounting, endogenous direct-loss risks (§4, \
    pp. 11–12), and Class 2 complete protection (§6, pp. 17–19) are not covered."

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Cooperative.Core
import CslibFrontier.GameTheory.Cooperative.MoulinCostSharing
import CslibFrontier.GameTheory.Cooperative.ShapleyValue

/-!
# Collected results: Cooperative TU games, Moulin cost sharing, Shapley value, and Nash bargaining
-/

register_result "jain-mahdian-bondareva-shapley-core" where
  title := "Bondareva–Shapley LP duality characterization of exact and approximate cores"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Theorems 15.6 and 15.8, Corollary 15.9, and Exercise 15.1",
      locator := "Section 15.2, pp. 388–390, and Section 15.8, p. 410" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.nonemptyCore_iff_balanced,
    Cslib.GameTheory.CooperativeGame.nonemptyCore_iff_balanced,
    Cslib.GameTheory.CostSharingGame.nonemptyApproxCore_iff_balanced,
    Cslib.GameTheory.CostSharingGame.IsSubadditive.isLeast_integralBalanced,
    Cslib.GameTheory.CostSharingGame.isGreatest_nonemptyApproxCore_integralityGapLP,
    Cslib.GameTheory.LinearExchangeEconomy.toCooperativeGame_nonemptyCore
  ]
  scope := "Finite agent type [Fintype A] [DecidableEq A] with real coalition costs or values \
    normalized by c(∅) = 0 (or v(∅) = 0). Strong LP duality (exists_isGreatest_isLeast_coreLP, \
    via Matrix.exists_isGreatest_isLeast_dotProduct) proves the Bondareva–Shapley theorem for \
    cost-sharing games (c(univ) ≤ ∑_S w_S c(S) for all balanced weights w) and cooperative \
    surplus games (∑_S w_S v(S) ≤ v(univ)), as well as the γ-Bondareva–Shapley theorem \
    (γ * c(univ) ≤ ∑_S w_S c(S) for every real γ, without requiring γ ≤ 1). For subadditive \
    games, the minimum integral objective of LP (15.2) equals c(univ) and, when 0 < c(univ), \
    the largest γ with nonempty γ-core equals lpOpt / c(univ) (Corollary 15.9). Exercise 15.1 \
    proves that every finite linear Arrow–Debreu exchange economy TU game has a nonempty core."

register_result "moulin-cross-monotonic-cost-sharing" where
  title := "Moulin's group-strategyproof iterative-pruning mechanism from cross-monotonic shares"
  topic := "algorithmic mechanism design"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Propositions 15.14 and 15.15, and Theorem 15.16",
      locator := "Section 15.3, Figure 15.2, pp. 392–394" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingScheme.inApproxCore_univ,
    Cslib.GameTheory.CostSharingScheme.isGreatest_isWilling_moulinServiced,
    Cslib.GameTheory.CostSharingScheme.moulinServiced_eq_of_validPruning,
    Cslib.GameTheory.CostSharingScheme.moulinMechanism_isGroupStrategyproof,
    Cslib.GameTheory.CostSharingScheme.moulinMechanism_isBudgetBalanced
  ]
  scope := "Finite agent type [Fintype A] with sealed-bid quasilinear utilities u_i q_i - p_i \
    and binary service q_i ∈ {0, 1} (bridged to SingleParameter.Mechanism). Any γ-budget-balanced \
    cross-monotonic scheme places share univ in the γ-core (Proposition 15.14). Iterative pruning \
    moulinServiced converges in at most |A| rounds to the unique largest willing coalition \
    {S | ∀ i ∈ S, ξ(S, i) ≤ b_i}, and any asynchronous valid pruning sequence terminating at a \
    willing coalition reaches the same set (Proposition 15.15). Moulin's mechanism M_ξ is \
    group-strategyproof against arbitrary coalitional misreports C.piecewise z u, satisfies \
    Voluntary Participation and Consumer Sovereignty, is γ-budget-balanced when ξ is, and \
    satisfies No Positive Transfers when shares are nonnegative (Theorem 15.16). Polynomial-time \
    oracle complexity of evaluating ξ is not modeled."

register_result "jain-mahdian-submodular-water-filling" where
  title := "Primal-dual water-filling cross-monotonic cost-sharing scheme for submodular games"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Lemma 15.18, Corollary 15.19, and Theorem 15.20",
      locator := "Section 15.4.1, Figure 15.3, pp. 396–397" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.IsTight.union,
    Cslib.GameTheory.CostSharingGame.isGreatest_maximalTightSet,
    Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isCrossMonotone,
    Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isBudgetBalanced,
    Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isNonneg
  ]
  scope := "For any nonnegative submodular cost-sharing game (bridged to \
    Cslib.Algorithms.Lean.Submodular.IsSubmodular), tight sets under a core-feasible allocation \
    are closed under union (Lemma 15.18), yielding a unique maximal tight subset maximalTightSet \
    (Corollary 15.19). The primal-dual water-filling scheme SubmodularCostShare (Dutta–Ray 1989; \
    Jain–Vazirani 2002) is nonnegative, 1-budget-balanced, and cross-monotone (Theorem 15.20). \
    Submodular function minimization oracle runtime for finding nextFreezeDelta is not modeled."

register_result "shapley-value-uniqueness" where
  title := "Shapley's axiomatic uniqueness theorem and submodular cross-monotonicity"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Example 15.24, Theorem 15.26, and Exercise 15.2",
      locator := "Sections 15.6.1–15.6.2, pp. 403–404, and Section 15.8, p. 410" },
    { paper := TardosVazirani2007,
      theorem := "Example 1.14 (Shapley value permutation-average definition)",
      locator := "Section 1.7.2, pp. 21–22" }
  ]
  theorems := [
    Cslib.GameTheory.shapleyValue_eq_permShapleyValue,
    Cslib.GameTheory.example15_24_not_inCore,
    Cslib.GameTheory.eq_shapleyValue_of_axioms,
    Cslib.GameTheory.existsUnique_shapleyValue,
    Cslib.GameTheory.CostSharingGame.IsSubmodular.shapleyScheme_isCrossMonotone,
    Cslib.GameTheory.CostSharingGame.IsSubmodular.shapleyValue_inCore
  ]
  scope := "Equates the subset-size factorial weight formula for shapleyValue with the uniform \
    average of marginal costs over all |A|! agent orderings (permShapleyValue). Evaluates \
    Example 15.24 to (23/6, 11/6, 7/3) outside the nonempty core of Example 15.2. Proves over \
    the 2^|A| - 1 unanimity-game Möbius basis that shapleyValue is the unique operator \
    satisfying Efficiency (made explicit where Definition 15.25 assumes budget balance implicitly \
    and writes S ⊂ A \\ {i} for S ⊆ A \\ {i} in Dummy), Symmetry (or Anonymity), Dummy, and \
    Additivity, without scalar homogeneity or nonnegativity hypotheses. Proves Exercise 15.2: \
    for submodular games, shapleyScheme is cross-monotone and shapleyValue lies in the core."

register_result "nash-bargaining-uniqueness" where
  title := "Nash's two-player axiomatic bargaining theorem"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Definition 15.27 and Theorem 15.28",
      locator := "Section 15.6.3, pp. 404–405" }
  ]
  theorems := [
    Cslib.GameTheory.isGreatest_nashBargainingSolution,
    Cslib.GameTheory.nashBargainingSolution_unique_maximizer,
    Cslib.GameTheory.eq_nashBargainingSolution_of_axioms,
    Cslib.GameTheory.existsUnique_nashBargainingSolution,
    Cslib.GameTheory.existsUnique_nashBargainingSolution_paretoOptimal
  ]
  scope := "On compact, convex 2-player feasible utility sets X ⊆ ℝ × ℝ containing a \
    disagreement point d ∈ X and at least one strictly individually rational point x > d \
    (without requiring comprehensiveness), maximizing the Nash product (x₁ - d₁)(x₂ - d₂) over \
    {x ∈ X | x ≥ d} attains a unique maximizer nashBargainingSolution that is strongly Pareto \
    optimal, symmetric, positive-affine scale-invariant (combining translation to d = (0, 0) \
    with Definition 15.27 scale independence), and satisfies IIA; moreover, it is the unique \
    bargaining solution satisfying Weak (or Strong) Pareto Optimality, Symmetry, Scale \
    Invariance, and IIA."

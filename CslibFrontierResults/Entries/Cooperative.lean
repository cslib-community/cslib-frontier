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

register_result "jain-mahdian-bondareva-shapley" where
  title := "Bondareva–Shapley LP duality characterization of the exact core"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Theorem 15.6",
      locator := "Section 15.2, p. 388" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.nonemptyCore_iff_balanced,
    Cslib.GameTheory.CooperativeGame.nonemptyCore_iff_balanced
  ]
  scope := "Finite agent type [Fintype A] [DecidableEq A] with real coalition costs or values \
    normalized by c(∅) = 0 (or v(∅) = 0). Strong LP duality (exists_isGreatest_isLeast_coreLP, \
    via Matrix.exists_isGreatest_isLeast_dotProduct) proves the Bondareva–Shapley theorem for \
    cost-sharing games (c(univ) ≤ ∑_S w_S c(S) for all balanced weights w) and cooperative \
    surplus games (∑_S w_S v(S) ≤ v(univ))."

register_result "jain-mahdian-approx-bondareva-shapley" where
  title := "Bondareva–Shapley characterization of the γ-approximate core"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Theorem 15.8",
      locator := "Section 15.2, p. 389" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.nonemptyApproxCore_iff_balanced
  ]
  scope := "Finite agent type [Fintype A] [DecidableEq A] with real coalition costs c(∅) = 0. \
    Proves that the γ-core is nonempty iff γ * c(univ) ≤ ∑_S w_S c(S) for all balanced weights \
    w, for every real γ (without needing Theorem 15.8's γ ≤ 1 restriction)."

register_result "jain-mahdian-core-integrality-gap" where
  title := "Largest approximate core factor equals the integrality gap of LP (15.2)"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Corollary 15.9",
      locator := "Section 15.2, p. 389" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.IsSubadditive.isLeast_integralBalanced,
    Cslib.GameTheory.CostSharingGame.IsSubadditive.isGreatest_nonemptyApproxCore_integralityGapLP
  ]
  scope := "Finite agent type [Fintype A] [DecidableEq A]. Defining integralLpOpt as the minimum \
    integral objective of LP (15.2) over IsIntegralBalancedWeights and \
    integralityGapLP := lpOpt / integralLpOpt, for any subadditive cost-sharing game \
    integralLpOpt = c(univ) and, when 0 < c(univ), the largest γ with nonempty γ-core equals \
    integralityGapLP."

register_result "jain-mahdian-linear-exchange-core" where
  title := "Nonempty core of a linear Arrow–Debreu exchange economy TU game"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Exercise 15.1",
      locator := "Exercises, p. 410" }
  ]
  theorems := [
    Cslib.GameTheory.LinearExchangeEconomy.toCooperativeGame_nonemptyCore
  ]
  scope := "Finite agent type [Fintype A] and finite good type [Fintype G] with nonnegative \
    endowments and linear marginal utilities. Proves coalitionValue attains the maximum total \
    utility over feasible/exact redistributions and marketPriceAllocation lies in the core of \
    toCooperativeGame."

register_result "jain-mahdian-cross-monotone-core" where
  title := "Cross-monotonic γ-budget-balanced cost-sharing schemes lie in the γ-core"
  topic := "algorithmic mechanism design"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Proposition 15.14",
      locator := "Section 15.3, p. 393" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingScheme.inApproxCore_univ
  ]
  scope := "Finite agent type [Fintype A]. Any γ-budget-balanced cross-monotonic cost-sharing \
    scheme ξ places ξ.share univ in the γ-core of G (and in the exact core when γ = 1)."

register_result "moulin-largest-willing-coalition" where
  title := "Unique largest willing coalition returned by Moulin's mechanism (with derived \
    pruning-order independence)"
  topic := "algorithmic mechanism design"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Proposition 15.15",
      locator := "Section 15.3, Figure 15.2, p. 393" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingScheme.isGreatest_isWilling_moulinServiced,
    Cslib.GameTheory.CostSharingScheme.moulinServiced_eq_of_validPruning
  ]
  scope := "Finite agent type [Fintype A] with arbitrary real bids b : A → ℝ (extending \
    Proposition 15.15's b_i ≥ 0 domain). For any cross-monotonic scheme ξ, synchronous iterative \
    pruning moulinServiced (Figure 15.2) converges in at most |A| rounds to the unique largest \
    willing coalition {S | ∀ i ∈ S, ξ(S, i) ≤ b_i} (isGreatest_isWilling_moulinServiced, \
    Proposition 15.15); moulinServiced_eq_of_validPruning is a derived order-independence result \
    showing that any finite path of valid partial deletions (ValidPruningStep) from univ \
    terminating at a willing coalition reaches the same set."

register_result "moulin-group-strategyproof-mechanism" where
  title := "Moulin's iterative-pruning mechanism is group-strategyproof and budget-balanced"
  topic := "algorithmic mechanism design"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Theorem 15.16",
      locator := "Section 15.3, p. 394" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingScheme.moulinMechanism_isGroupStrategyproof,
    Cslib.GameTheory.CostSharingScheme.moulinMechanism_isBudgetBalanced
  ]
  scope := "Finite agent type [Fintype A] with sealed-bid quasilinear utilities u_i q_i - p_i \
    and binary service q_i ∈ {0, 1} (bridged to SingleParameter.Mechanism). For any \
    cross-monotonic scheme ξ, moulinMechanism ξ is group-strategyproof against arbitrary \
    coalitional misreports C.piecewise z u, satisfies Voluntary Participation and Consumer \
    Sovereignty, is γ-budget-balanced when ξ is, and satisfies No Positive Transfers when shares \
    are nonnegative. Polynomial-time oracle complexity of evaluating ξ is not modeled."

register_result "jain-mahdian-submodular-tight-union" where
  title := "Closure under union of tight coalitions in submodular cost-sharing games"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Lemma 15.18",
      locator := "Section 15.4.1, p. 396" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.IsTight.union
  ]
  scope := "For any submodular cost-sharing game (bridged to \
    Cslib.Algorithms.Lean.Submodular.IsSubmodular) and allocation α core-feasible on T, if \
    S₁, S₂ ⊆ T are tight then S₁ ∪ S₂ is tight (IsTight.union, Lemma 15.18); closure under \
    intersection S₁ ∩ S₂ (IsTight.inter) is proved alongside it as a derived companion."

register_result "jain-mahdian-submodular-maximal-tight" where
  title := "Unique maximal tight subset in submodular cost-sharing games"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Corollary 15.19",
      locator := "Section 15.4.1, p. 396" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.isGreatest_maximalTightSet
  ]
  scope := "For any submodular cost-sharing game and allocation α core-feasible on T, \
    maximalTightSet G T α is the unique largest tight subset of T."

register_result "jain-mahdian-submodular-water-filling" where
  title := "Primal-dual water-filling cross-monotonic cost-sharing scheme for submodular games"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Theorem 15.20",
      locator := "Section 15.4.1, Figure 15.3, pp. 396–397" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isCrossMonotone,
    Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isBudgetBalanced,
    Cslib.GameTheory.CostSharingGame.submodularCostShareScheme_isNonneg
  ]
  scope := "For any nonnegative submodular cost-sharing game, the primal-dual water-filling \
    scheme submodularCostShareScheme (SubmodularCostShare, Dutta–Ray 1989; Jain–Vazirani 2002) \
    is nonnegative, 1-budget-balanced, and cross-monotone. Submodular function minimization \
    oracle runtime for finding nextFreezeDelta is not modeled."

register_result "shapley-value-permutation-average" where
  title := "Equivalence of the subset-weight and random-ordering Shapley value formulas"
  topic := "cooperative game theory"
  sources := [
    { paper := TardosVazirani2007,
      theorem := "Example 1.14",
      locator := "Section 1.7.2, p. 22" },
    { paper := JainMahdian2007,
      theorem := unverified,
      locator := "Section 15.6.1, p. 403" }
  ]
  theorems := [
    Cslib.GameTheory.shapleyValue_eq_permShapleyValue
  ]
  scope := "Finite agent type [Fintype A] [DecidableEq A]. Equates the subset-size factorial \
    weight formula for shapleyValue (Jain–Mahdian Section 15.6.1, p. 403, obtained there by \
    counting predecessor sets in a random ordering) with permShapleyValue, the uniform average of \
    marginal costs over all |A|! agent orderings (Tardos–Vazirani Example 1.14, p. 22)."

register_result "jain-mahdian-shapley-outside-core" where
  title := "Shapley value outside a nonempty facility-location core"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Example 15.24",
      locator := "Section 15.6.1, p. 403; Example 15.4 in Section 15.2, pp. 387–388" }
  ]
  theorems := [
    Cslib.GameTheory.example15_24_nonemptyCore,
    Cslib.GameTheory.example15_24_not_inCore
  ]
  scope := "On the 3-agent metric facility-location game example15_2, the core is nonempty — \
    witnessed by ![4, 2, 2] via FacilityLocationInstance.example15_2_inCore_four_two_two \
    (Example 15.4, pp. 387–388; packaged as example15_24_nonemptyCore) — whereas the Shapley \
    value evaluates to (23/6, 11/6, 7/3) and violates the {b, c} core inequality 25/6 > 4 \
    (example15_24_not_inCore, Example 15.24, p. 403)."

register_result "shapley-value-uniqueness" where
  title := "Shapley's axiomatic uniqueness theorem"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Theorem 15.26",
      locator := "Section 15.6.2, p. 404" }
  ]
  theorems := [
    Cslib.GameTheory.eq_shapleyValue_of_axioms,
    Cslib.GameTheory.existsUnique_shapleyValue
  ]
  scope := "Proves over the 2^|A| - 1 unanimity-game Möbius basis (via \
    Cslib.BitString.subsetMobius) that shapleyValue is the unique operator \
    φ : CostSharingGame A → A → ℝ satisfying Efficiency (made explicit where Definition 15.25 \
    assumes budget balance implicitly and writes S ⊂ A \\ {i} for S ⊆ A \\ {i} in Dummy), \
    Symmetry (or Anonymity), Dummy, and Additivity, without scalar homogeneity or nonnegativity \
    hypotheses."

register_result "jain-mahdian-submodular-shapley-cross-monotone" where
  title := "Cross-monotonicity and core membership of the Shapley value for submodular games"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Exercise 15.2",
      locator := "Exercises, p. 410; Section 15.6.1, p. 403" }
  ]
  theorems := [
    Cslib.GameTheory.CostSharingGame.IsSubmodular.shapleyScheme_isCrossMonotone,
    Cslib.GameTheory.CostSharingGame.IsSubmodular.shapleyValue_inCore
  ]
  scope := "For any submodular cost-sharing game G, the coalition-restricted Shapley scheme \
    G.shapleyScheme is cross-monotone (Exercise 15.2, p. 410) and shapleyValue G lies in the \
    core of G (Section 15.6.1, p. 403, derived via Proposition 15.14)."

register_result "nash-bargaining-uniqueness" where
  title := "Nash's two-player axiomatic bargaining theorem"
  topic := "cooperative game theory"
  sources := [
    { paper := JainMahdian2007,
      theorem := "Theorem 15.28",
      locator := "Section 15.6.3, p. 405" }
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

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.PredictionMarket.BooleanAggregation

/-!
# Collected results: Shapley–Shubik Boolean prediction markets
-/

register_result "nrtv-boolean-market-common-knowledge-aggregates" where
  title := "Common knowledge of aggregates at equilibrium in Boolean prediction markets"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Theorem 26.9",
      locator := "Chapter 26, §26.5.4, p. 668, Eqs. (26.1)–(26.2)" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.eq_condExpect_and_agentBid_of_roundPrice_const,
    Cslib.GameTheory.PredictionMarket.equilibrium_commonKnowledge_of_aggregates
  ]
  scope := "Any positive number of agents n > 0, Boolean security f : (Fin n → Bool) → Bool, and \
    prior P with positive mass at x (initial common knowledge S⁰ = priorSupport P = {y | 0 < P y} \
    so every conditioning event has strictly positive prior mass). Proves both the general \
    fixed-point form on any nonempty S ⊆ priorSupport P with constant clearing price p and its \
    instantiation at the market equilibrium (eqSet f P x, eqPrice f P x): condExpect f P S^∞ = p^∞ \
    (Eq. 26.1) and ∀ i, ∀ y ∈ S^∞, agentBid f P S^∞ i y = p^∞ (Eq. 26.2)."

register_result "nrtv-boolean-market-weighted-threshold-sufficiency" where
  title := "Weighted threshold functions converge to true value in Boolean prediction markets"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Theorem 26.12",
      locator := "Chapter 26, §26.5.5, p. 669 (using Definition 26.11, p. 669)" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.eq_of_mem_eqSet_of_isWeightedThreshold,
    Cslib.GameTheory.PredictionMarket.eqPrice_eq_of_isWeightedThreshold,
    Cslib.GameTheory.PredictionMarket.isWeightedThreshold_iff_forall_eqPrice_eq
  ]
  scope := "Any n > 0, weighted threshold function f : (Fin n → Bool) → Bool (Definition 26.11), \
    and any prior P with 0 < P x (initial support S⁰ = priorSupport P). Proves that f is constant \
    on eqSet f P x and eqPrice f P x = if f x then 1 else 0, together with the combined necessary \
    and sufficient characterization across all mixed-strategy priors."

register_result "nrtv-boolean-market-weighted-threshold-necessity" where
  title := "Non-threshold Boolean functions admit a non-converging prior in Boolean markets"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Theorem 26.13",
      locator := "Chapter 26, §26.5.5, p. 669" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.exists_prior_eqPrice_eq_half_of_not_isWeightedThreshold
  ]
  scope := "Any Boolean function f : (Fin n → Bool) → Bool failing IsWeightedThreshold (which \
    automatically forces n > 0). Constructs via Hahn–Banach separation of finite convex hulls an \
    explicit prior P (IsMixedStrategy P) under which every agent bids 1/2 in round 1 and the \
    market immediately stabilizes at eqPrice f P x = 1/2 ≠ f x for every x with 0 < P x."

register_result "nrtv-boolean-market-convergence-upper-bound" where
  title := "Convergence of Boolean prediction markets in at most n rounds"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Theorem 26.14",
      locator := "Chapter 26, §26.5.6, p. 669" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.commonKnowledge_succ_eq_self_at_n,
    Cslib.GameTheory.PredictionMarket.convergence_in_n_rounds_of_isWeightedThreshold
  ]
  scope := "Any n > 0, weighted threshold function f : (Fin n → Bool) → Bool, prior P, and state \
    x with 0 < P x, using NRTV §26.5.4 round indexing where commonKnowledge f P x r is the \
    common-knowledge set Sʳ after r rounds of trading (S⁰ = priorSupport P). Affine-dimension drop \
    in ℝⁿ first establishes Sⁿ⁺¹ = Sⁿ for every Boolean function f, whence for weighted threshold \
    functions every r ≥ n satisfies Sʳ = eqSet f P x and roundPrice f P Sʳ x = condExpect f P Sʳ \
    = if f x then 1 else 0."

register_result "nrtv-boolean-market-convergence-lower-bound" where
  title := "Worst-case n-round convergence lower bound on 2n inputs for Boolean markets"
  topic := "game theory"
  sources := [
    { paper := PennockSami2007,
      theorem := "Theorem 26.15",
      locator := "Chapter 26, §26.5.6, p. 669" }
  ]
  theorems := [
    Cslib.GameTheory.PredictionMarket.carryChain_convergence_rounds,
    Cslib.GameTheory.PredictionMarket.exists_n_round_lower_bound
  ]
  scope := "For every n > 0, constructs the 2n-input nested carry-chain weighted threshold \
    function carryChain n (Cₙ), explicit prior carryPrior n (Pₙ, IsMixedStrategy), and \
    positive-probability states carryInputFalse n (Cₙ = false) and carryInputTrue n (Cₙ = true). \
    For every r < n, Sʳ(x₀) = Sʳ(x₁) with condExpect = 1/2 and exact clearing prices 1/2 \
    (r + 1 < n) or (3n ∓ 1)/(6n) (r = n - 1), all strictly in (0, 1); at round r = n, common \
    knowledge determines Cₙ and the clearing price reaches Cₙ(x)."

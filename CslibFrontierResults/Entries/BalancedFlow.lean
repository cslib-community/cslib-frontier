/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Market.BalancedFlow
import CslibFrontier.GameTheory.Market.DPSVAlgorithm

/-!
# Collected results: Equality networks, tight sets, balanced flows, and the DPSV algorithm
-/

register_result "fisher-equality-network-and-tight-sets" where
  title := "Equality money-flow network, equilibrium cut test, Invariant, and maximal tight set"
  topic := "game theory"
  sources := [
    { paper := Vazirani2007,
      theorem := "Lemma 5.2, Lemma 5.3, and Section 5.8 maximal tight set",
      locator := "Section 5.3, Lemma 5.2, p. 109; Section 5.6, Lemma 5.3, p. 111; \
        Section 5.8, p. 115" }
  ]
  theorems := [
    Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_of_isMaxRealFlow,
    Cslib.GameTheory.Market.LinearFisherMarket.exists_isEquilibrium_iff_minCut,
    Cslib.GameTheory.Market.LinearFisherMarket.satisfiesInvariant_iff,
    Cslib.GameTheory.Market.LinearFisherMarket.isTightSet_union_and_inter,
    Cslib.GameTheory.Market.LinearFisherMarket.isTightSet_maximalTightSet,
    Cslib.GameTheory.Market.LinearFisherMarket.subset_maximalTightSet
  ]
  scope := "Finite buyer type [Fintype I] and finite good type [Fintype G] in LinearFisherMarket \
    (arbitrary nonnegative supplies supply : G → ℝ, matching Vazirani's unit-supply network when \
    supply g = 1). Instantiates Cslib.Algorithms.Lean.MaxFlow.RealFlow on equalityNetwork with a \
    finite non-binding big-M capacity ∑ g, p g * supply g + ∑ i, budget i + 1 on equality arcs. \
    Proves Lemma 5.2 (positive prices p are equilibrium prices iff both source and sink cuts are \
    min-cuts in N(p), and every max-flow yields an equilibrium allocation via moneyFlowToAlloc), \
    Lemma 5.3 (the Invariant holds iff goodValue p S ≤ budgetSum (buyerNeighborhood p S) for all \
    S), submodular closure of tight sets under union and intersection, and existence of the \
    unique maximal tight set maximalTightSet."

register_result "fisher-balanced-flows-and-divide-and-conquer" where
  title := "Balanced flows in linear Fisher equality networks and divide-and-conquer algorithm"
  topic := "game theory"
  sources := [
    { paper := Vazirani2007,
      theorem := "Lemma 5.4, Theorem 5.5, Lemmas 5.6–5.7, and Theorem 5.8",
      locator := "Section 5.7, Lemma 5.4, p. 112; Theorem 5.5, pp. 112–113; \
        Section 5.7.1, Lemmas 5.6–5.7 and Theorem 5.8, pp. 113–115" }
  ]
  theorems := [
    Cslib.GameTheory.Market.LinearFisherMarket.exists_isBalancedFlow,
    Cslib.GameTheory.Market.LinearFisherMarket.IsBalancedFlow.isMaxEqualityFlow,
    Cslib.GameTheory.Market.LinearFisherMarket.surplus_eq_of_isBalancedFlow,
    Cslib.GameTheory.Market.LinearFisherMarket.isBalancedFlow_iff_satisfiesPropertyOne,
    Cslib.GameTheory.Market.LinearFisherMarket.balancedFlowProgram_spec
  ]
  scope := "Finite buyer type [Fintype I] and finite good type [Fintype G] in LinearFisherMarket \
    (arbitrary nonnegative supplies). Proves existence of a balanced flow minimizing the squared \
    ℓ₂ surplus norm (equivalently ℓ₂ norm, isBalancedFlow_iff_sqrt), that every balanced flow is \
    a max-flow in N(p), Lemma 5.4 (uniqueness of the balanced surplus vector; note Vazirani \
    p. 112 prints 'strictly concave' for strictly convex), and Theorem 5.5 (characterization of \
    balanced max-flows by Property 1: no residual path in R(f) - {s, t} from smaller to strictly \
    larger surplus). Formalizes the divide-and-conquer algorithm of Section 5.7.1 as a Cslib.FreeM \
    query program balancedFlowProgram over MaxFlowQuery (batched level-by-level on pairwise \
    disjoint subnetworks with isolated buyers pruned from N₁), proving Lemmas 5.6–5.7 and \
    Theorem 5.8 (outputs a balanced max-flow in at most Fintype.card G max-flow oracle calls; \
    uniform shift X is chosen noncomputably via IVT, while max-flow queries are counted \
    explicitly)."

register_result "fisher-finding-tight-sets" where
  title := "Finding the minimum tight-set price scale and maximal tight set via max-flow"
  topic := "game theory"
  sources := [
    { paper := Vazirani2007,
      theorem := "Lemmas 5.9, 5.10, and 5.11",
      locator := "Section 5.9, Lemmas 5.9–5.11, pp. 117–118" }
  ]
  theorems := [
    Cslib.GameTheory.Market.LinearFisherMarket.minCut_scaledSubnetwork_of_le_minTightRatio,
    Cslib.GameTheory.Market.LinearFisherMarket.not_minCut_and_subset_of_minTightRatio_lt,
    Cslib.GameTheory.Market.LinearFisherMarket.ssubset_of_minCut_at_avgRatio,
    Cslib.GameTheory.Market.LinearFisherMarket.findTightSetProgram_spec
  ]
  scope := "Finite buyer type [Fintype I] and finite good type [Fintype G] in LinearFisherMarket \
    on any nonempty subset A of goods with positive value p g * supply g > 0. Proves Lemma 5.9 \
    (source cut is a min-cut in N(x · p) for 0 ≤ x ≤ x*, and for x > x* it is not a min-cut and \
    every min-cut puts S* on the source side), Lemma 5.10 (at average ratio x = m(Γ(A)) / p(A) > \
    x*, every min-cut puts a proper subset of A on the source side), and Lemma 5.11 \
    (findTightSetProgram in Cslib.FreeM computes (x*, S*) in at most A.card max-flow oracle \
    calls)."

register_result "fisher-rational-equilibria-polynomial-bit" where
  title := "Tight-set price denominator bound and polynomial-bit rationality of Fisher equilibria"
  topic := "game theory"
  sources := [
    { paper := Vazirani2007,
      theorem := "Lemma 5.12 and Theorem 5.1 (part 4)",
      locator := "Section 5.2, Theorem 5.1 part 4, pp. 107–108; Section 5.10, Lemma 5.12, \
        pp. 118–119" }
  ]
  theorems := [
    Cslib.GameTheory.Market.LinearFisherMarket.exists_rat_price_of_isTightSet,
    Cslib.GameTheory.Market.LinearFisherMarket.exists_rational_equilibrium_of_nat,
    Cslib.GameTheory.Market.LinearFisherMarket.exists_rational_equilibrium_of_rat
  ]
  scope := "Finite buyer type [Fintype I] and finite good type [Fintype G] in unit-supply \
    LinearFisherMarket (supply g = 1). Proves Lemma 5.12: for integer utilities u i g ≤ U and \
    integer budgets e i under positive prices satisfying the Invariant, every good in a tight \
    set S has a rational price with denominator at most S.card * U ^ (S.card - 1) ≤ n * U ^ n. \
    Proves Theorem 5.1 part 4 for both integer inputs (exists_rational_equilibrium_of_nat, \
    combining spanning-tree component rationality with integral max-flow min-cut on each \
    component, bounding price denominators by n * U ^ n and price/allocation numerators and \
    allocation denominators by E * U ^ n) and general rational inputs \
    (exists_rational_equilibrium_of_rat, clearing denominators per buyer and globally to obtain \
    explicit polynomial-bit bounds in m, n, B_num, and B_den). Together with \
    EisenbergGale.lean, this completes all four parts of Vazirani Theorem 5.1."

register_result "fisher-dpsv-main-algorithm" where
  title := "DPSV primal-dual algorithm, potential drop analysis, and polynomial max-flow bound"
  topic := "game theory"
  sources := [
    { paper := Vazirani2007,
      theorem := "Section 5.8 initialization, Lemmas 5.13–5.21, and Theorem 5.22",
      locator := "Section 5.8, pp. 115–117; Section 5.10, Lemmas 5.13–5.21 and Theorem 5.22, \
        pp. 119–121" }
  ]
  theorems := [
    Cslib.GameTheory.Market.LinearFisherMarket.dpsvInitPrice_spec,
    Cslib.GameTheory.Market.LinearFisherMarket.price_sub_ge_inv_sq_of_isTightSet,
    Cslib.GameTheory.Market.LinearFisherMarket.sum_sq_drop_of_transfer,
    Cslib.GameTheory.Market.LinearFisherMarket.surplusSqNorm_le_sub_sq_of_isBalancedFlow,
    Cslib.GameTheory.Market.LinearFisherMarket.isEqualityFlow_scaleActivePrices,
    Cslib.GameTheory.Market.LinearFisherMarket.surplusSqNorm_scaleActivePrices_le,
    Cslib.GameTheory.Market.LinearFisherMarket.exists_surplus_drop_of_residual_expand,
    Cslib.GameTheory.Market.LinearFisherMarket.surplusSqNorm_drop_of_minSurplus_lt,
    Cslib.GameTheory.Market.LinearFisherMarket.dpsvPhaseProgram_spec,
    Cslib.GameTheory.Market.LinearFisherMarket.dpsvProgram_spec
  ]
  scope := "Finite buyer type [Fintype I] (cardinality m) and finite good type [Fintype G] \
    (cardinality n) in LinearFisherMarket. Formalizes the Section 5.8 price initialization \
    dpsvInitPrice (p. 115, lowering goods with no equality edge at 1/n to max_i u_ij/α_i and \
    establishing the Invariant), Lemma 5.13 (tight-set price gap ≥ 1/Δ² for Δ = n U^n; noting \
    the printed typo r ≤ Δ for s ≤ Δ on p. 119), Lemmas 5.15–5.16 (surplus potential drop via \
    convexity), Lemmas 5.17–5.20 (per-iteration feasibility, monotone norm decrease, and \
    minimum-surplus drop), and Lemmas 5.14 and 5.21 (dpsvPhaseProgram executes 1 ≤ iters ≤ n \
    iterations in ≤ 2 n * iters max-flow queries and drops surplusSqNorm by factor \
    1 - 1 / (m * n), specializing to 1 - 1 / n² when m ≤ n). Proves Theorem 5.22 \
    (dpsvProgram_spec): for every non-degenerate unit-supply linear Fisher market with integer \
    utilities u i g ≤ U and integer budgets e i (M_tot = ∑ i, e i), dpsvProgram in Cslib.FreeM \
    over MaxFlowQuery terminates at an exact market equilibrium in at most \
    m * n * (Nat.log 2 (m * Δ^4 * M_tot^2) + 1) + n phases and at most n + 2 * n^2 * phases \
    max-flow oracle calls (O(m n^3 (log m + log n + n log U + log M_tot)), matching \
    O(n^4 (log n + n log U + log M)) when m ≤ n). Halts when all surpluses vanish (fixing p. 116 \
    where Case 1 of Section 5.7.1 was written) and handles zero-spending buyers outside H with \
    all equality edges in J (fixing p. 116's claim that B \\ H immediately drops J). States the \
    max-flow oracle query count in Cslib.FreeM rather than a machine-level bit-complexity runtime."

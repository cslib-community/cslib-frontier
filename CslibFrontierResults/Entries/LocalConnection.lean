/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.NetworkFormation.LocalConnection

/-!
# Collected results: local connection games (NRTV Section 19.2)
-/

open Cslib.GameTheory.LocalConnection

register_result "tardos-wexler-local-connection-social-optima" where
  title := "Social optima of the local connection game: stars for alpha >= 2 and complete graphs \
    for 0 <= alpha <= 2"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Lemma 19.1",
      locator := "Section 19.2.2, p. 490" },
    { paper := FabrikantLuthraManevaPapadimitriouShenker2003,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.LocalConnection.isOptimalNetwork_starGraph,
    Cslib.GameTheory.LocalConnection.isOptimalNetwork_top,
    Cslib.GameTheory.LocalConnection.NoDoubleEdges.isSocialOptimum_of_formedGraph_eq_starGraph,
    Cslib.GameTheory.LocalConnection.NoDoubleEdges.isSocialOptimum_of_formedGraph_eq_top
  ]
  scope := "Undirected local connection game on a finite vertex type V ([Fintype V], plus \
    [DecidableEq V] for profile-level statements) with edge-creation price alpha : R and extended \
    costs networkECost and socialECost in ENNReal (where disconnected pairs contribute edist = top \
    and each unordered pair {u, v} contributes dist(u, v) twice in the ordered-pair sum \
    sum_{u, v} edist(u, v), matching Tardos and Wexler Section 19.2.1, p. 490). \
    isOptimalNetwork_starGraph proves that SimpleGraph.starGraph r minimizes networkECost alpha \
    over all SimpleGraph V for 2 <= alpha (cost alpha * (n - 1) + 2 * (n - 1)^2), and \
    isOptimalNetwork_top proves that top : SimpleGraph V minimizes networkECost alpha for \
    0 <= alpha <= 2 (cost alpha * n.choose 2 + n * (n - 1)); the NoDoubleEdges companions lift \
    both characterizations to strategy profiles minimizing socialECost alpha."

register_result "tardos-wexler-local-connection-star-clique-nash" where
  title := "Star and complete-graph pure Nash equilibria in the local connection game"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Lemma 19.2",
      locator := "Section 19.2.2, p. 491" },
    { paper := FabrikantLuthraManevaPapadimitriouShenker2003,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.LocalConnection.NoDoubleEdges.isPureNash_of_formedGraph_eq_starGraph,
    Cslib.GameTheory.LocalConnection.isStableNetwork_starGraph,
    Cslib.GameTheory.LocalConnection.NoDoubleEdges.isPureNash_of_formedGraph_eq_top,
    Cslib.GameTheory.LocalConnection.isStableNetwork_top,
    Cslib.GameTheory.LocalConnection.isStableNetwork_top_iff
  ]
  scope := "Pure Nash equilibria (IsPureNash alpha s) and stable networks \
    (IsStableNetwork alpha G) of the unilateral local connection game on finite vertex sets \
    [Fintype V] [DecidableEq V] with extended individual costs playerECost in ENNReal. \
    NoDoubleEdges.isPureNash_of_formedGraph_eq_starGraph and isStableNetwork_starGraph prove that \
    for 1 <= alpha, every single-sponsor profile forming SimpleGraph.starGraph r (including both \
    center-sponsored starCenterProfile r and leaf-sponsored starLeafProfile r) is a pure Nash \
    equilibrium. NoDoubleEdges.isPureNash_of_formedGraph_eq_top and isStableNetwork_top prove that \
    for 0 <= alpha <= 1, every single-sponsor profile forming top is a pure Nash equilibrium, and \
    isStableNetwork_top_iff proves IsStableNetwork alpha top <-> alpha <= 1 when \
    3 <= Fintype.card V (for Fintype.card V = 2, top coincides with starGraph and remains stable \
    for all alpha >= 1)."

register_result "tardos-wexler-local-connection-price-of-stability" where
  title := "Price of stability of the local connection game: 1 outside (1, 2) and at most 4/3 \
    for 1 <= alpha <= 2"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Theorem 19.3",
      locator := "Section 19.2.2, p. 491" }
  ]
  theorems := [
    Cslib.GameTheory.LocalConnection.exists_isPureNash_isSocialOptimum_of_le_one,
    Cslib.GameTheory.LocalConnection.exists_isPureNash_isSocialOptimum_of_two_le,
    Cslib.GameTheory.LocalConnection.socialCost_starCenterProfile_lt_four_thirds_mul,
    Cslib.GameTheory.LocalConnection.exists_isPureNash_socialECost_le_four_thirds,
    Cslib.GameTheory.LocalConnection.networkCost_one_starGraph_div_top
  ]
  scope := "Finite local connection games on V ([Fintype V] [DecidableEq V]) with 0 <= alpha. \
    exists_isPureNash_isSocialOptimum_of_le_one (0 <= alpha <= 1) and \
    exists_isPureNash_isSocialOptimum_of_two_le (2 <= alpha) exhibit a pure Nash equilibrium that \
    also minimizes socialECost alpha (price of stability 1). For 1 <= alpha <= 2 and \
    2 <= Fintype.card V, socialCost_starCenterProfile_lt_four_thirds_mul proves the strict real \
    bound socialCost alpha (starCenterProfile r) < (4 / 3) * socialCost alpha s' against every \
    connected profile s', exists_isPureNash_socialECost_le_four_thirds gives the uniform ENNReal \
    bound socialECost alpha s <= ENNReal.ofReal (4 / 3) * socialECost alpha s' for all 0 <= alpha, \
    and networkCost_one_starGraph_div_top proves the exact star-to-clique ratio \
    (4 * n^2 - 6 * n + 2) / (3 * n^2 - 3 * n) at alpha = 1."

register_result "tardos-wexler-local-connection-diameter-poa" where
  title := "Social cost of a diameter-d Nash equilibrium is at most 3d times optimal"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Lemma 19.4",
      locator := "Section 19.2.3, pp. 491-492" },
    { paper := FabrikantLuthraManevaPapadimitriouShenker2003,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.LocalConnection.IsPureNash.socialCost_le_three_mul_diam_mul,
    Cslib.GameTheory.LocalConnection.IsPureNash.socialECost_le_three_mul_diam_mul
  ]
  scope := "For any pure Nash equilibrium s (0 <= alpha) on [Fintype V] [DecidableEq V] forming \
    G = formedGraph s of diameter d = G.diam, bridge edges cost at most alpha * (n - 1) via a \
    spanning tree of G and non-bridge edges paid by u cost at most 2 * d * (n - 1) via pairwise \
    disjoint critical shortest-path sets W_v, yielding socialCost alpha s <= 3 * d * \
    socialCost alpha s' for every connected s' and socialECost alpha s <= (3 * d) * \
    socialECost alpha s' for every profile s' (matching the explicit factor 3d in Tardos and \
    Wexler's proof of Lemma 19.4, p. 492)."

register_result "fabrikant-local-connection-sqrt-alpha-poa" where
  title := "O(sqrt(alpha)) equilibrium diameter and price of anarchy in the local connection game"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Theorem 19.5",
      locator := "Section 19.2.3, pp. 492-493" },
    { paper := FabrikantLuthraManevaPapadimitriouShenker2003,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.LocalConnection.IsPureNash.diam_le_sqrt_four_mul_add_one,
    Cslib.GameTheory.LocalConnection.IsPureNash.diam_le_two_mul_sqrt_add_one,
    Cslib.GameTheory.LocalConnection.IsPureNash.socialECost_le_six_mul_sqrt_add_three_mul
  ]
  scope := "Every pure Nash equilibrium s for 0 <= alpha on [Fintype V] [DecidableEq V] satisfies \
    ((formedGraph s).diam : R) <= Real.sqrt (4 * alpha + 1) <= 2 * Real.sqrt alpha + 1 and \
    socialECost alpha s <= ENNReal.ofReal (6 * Real.sqrt alpha + 3) * socialECost alpha s' for \
    every profile s'. Tardos and Wexler (Theorem 19.5, p. 492) state the diameter bound as \
    2 * sqrt(alpha) by setting dist(u, v) >= 2k and deducing k <= sqrt(alpha); for odd diameter \
    d = 2k + 1, shortcutting (u, v) saves 0 + 2 + ... + 2k = k(k + 1) = (d^2 - 1) / 4, giving the \
    sharp bound sqrt(4 * alpha + 1) <= 2 * sqrt(alpha) + 1 (attained with equality on the 4-vertex \
    path P_4 at alpha = 2, which is a checked pure Nash equilibrium of diameter 3 > 2 * sqrt(2))."

register_result "albers-local-connection-sublinear-alpha-poa" where
  title := "Diameter <= 4 alpha / sqrt(n) + 9 and O(1 + alpha / sqrt(n)) price of anarchy in the \
    local connection game"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007,
      theorem := "Theorem 19.6",
      locator := "Section 19.2.3, pp. 493-494" },
    { paper := AlbersEiltsEvenDarMansourRoditty2006,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    IsPureNash.diam_le_four_mul_div_sqrt_card_add_nine,
    IsPureNash.socialECost_le_twelve_mul_div_sqrt_card_add_twenty_seven_mul
  ]
  scope := "Every pure Nash equilibrium s for 0 <= alpha on n = Fintype.card V players \
    ([Fintype V] [DecidableEq V]) satisfies ((formedGraph s).diam : R) <= \
    4 * alpha / Real.sqrt n + 9 (proved for all 0 <= alpha and all n, including empty or singleton \
    V) and socialECost alpha s <= ENNReal.ofReal (12 * alpha / Real.sqrt n + 27) * \
    socialECost alpha s' for every profile s', establishing the O(1 + alpha / sqrt(n)) price of \
    anarchy bound of Tardos and Wexler Theorem 19.6 (pp. 493-494)."

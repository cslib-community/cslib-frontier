/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Congestion.CostSharing
import CslibFrontier.GameTheory.NetworkFormation.FairConnection
import CslibFrontier.GameTheory.NetworkFormation.Witnesses

/-!
# Result registry entries for network formation and fair connection games
-/

register_result "fair-cost-sharing-smoothness-poa" where
  title := "Price of anarchy at most k and (k, 0)-smoothness for fair cost-sharing congestion games"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2015,
      theorem := "Definition 2.1 and Theorem 3.2",
      locator := "author's version of 14 July 2015" },
    { paper := TardosWexler2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.CongestionGame.isSmooth_fairCostSharing,
    Cslib.GameTheory.CongestionGame.socialCost_fairCostSharing_le_card_mul_of_isPureNash,
    Cslib.GameTheory.CongestionGame.expected_socialCost_fairCostSharing_le_card_mul
  ]
  scope := "Over k-player fair cost-sharing congestion games (fairCostSharing resources c over \
    [Fintype ι], [DecidableEq ι], [DecidableEq E], [Finite E]) with nonnegative resource costs \
    (∀ e, 0 ≤ c e): proves (k, 0)-smoothness ([Roughgarden2015] Definition 2.1) and deduces \
    socialCost s ≤ k * socialCost s' for every pure Nash equilibrium s and every coarse correlated \
    equilibrium σ against arbitrary strategy profiles s' ([Roughgarden2015] Theorem 3.2)."

register_result "fair-connection-potential" where
  title := "Rosenthal's exact harmonic potential and sandwich bounds for fair connection games"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007, theorem := "Lemmas 19.7 and 19.8", locator := "§19.3.1" },
    { paper := Rosenthal1973, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.FairConnectionGame.isExactPotential_potential,
    Cslib.GameTheory.FairConnectionGame.socialCost_le_potential,
    Cslib.GameTheory.FairConnectionGame.potential_le_harmonic_mul_socialCost,
    Cslib.GameTheory.UndirectedFairConnectionGame.isExactPotential_potential
  ]
  scope := "Directed multigraph fair connection games (FairConnectionGame ι V E with arbitrary \
    parallel arcs and zero-cost arcs) and undirected simple-graph fair connection games \
    (UndirectedFairConnectionGame ι V over Sym2 V edges) with [Fintype ι], [DecidableEq ι], and \
    finite edge/vertex sets: embeds into CongestionGame.fairCostSharing, proving Rosenthal's \
    potential Φ s = ∑ e, edgeCost e * harmonic (edgeLoad s e) is an exact potential and \
    satisfies socialCost s ≤ Φ s ≤ H k * socialCost s for nonnegative edge costs \
    ([TardosWexler2007] §19.3.1, Lemmas 19.7 and 19.8)."

register_result "fair-connection-fip-nash-existence" where
  title := "Finite improvement property and pure Nash equilibrium existence in fair connection \
    games"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007, theorem := unverified, locator := "§19.3.1" },
    { paper := Rosenthal1973, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.FairConnectionGame.hasFIP,
    Cslib.GameTheory.FairConnectionGame.exists_isPureNash,
    Cslib.GameTheory.UndirectedFairConnectionGame.exists_isPureNash
  ]
  scope := "Directed and undirected finite fair connection games under G.TerminalsConnected \
    (every player i can reach sink i from source i via a simple path): establishes the finite \
    improvement property HasFIP and existence of a pure Nash equilibrium from finite simple-path \
    strategy sets and Rosenthal's exact harmonic potential Φ."

register_result "fair-connection-pos-harmonic" where
  title := "Price of stability at most H_k for directed and undirected fair connection games"
  topic := "game theory"
  sources := [
    { paper := AnshelevichDKTWR2008, theorem := unverified, locator := unverified },
    { paper := TardosWexler2007, theorem := "Theorem 19.10", locator := "§19.3.1" }
  ]
  theorems := [
    Cslib.GameTheory.FairConnectionGame.exists_isPureNash_socialCost_le_harmonic_mul,
    Cslib.GameTheory.FairConnectionGame.exists_isPureNash_socialCost_le_harmonic_mul_steinerCost,
    Cslib.GameTheory.FairConnectionGame.exists_reflTransGen_isPureNash_socialCost_le_harmonic_mul,
    Cslib.GameTheory.UndirectedFairConnectionGame.exists_isPureNash_socialCost_le_harmonic_mul
  ]
  scope := "Directed multigraph and undirected simple-graph fair connection games with finitely \
    many edges/vertices, nonnegative edge costs (∀ e, 0 ≤ G.edgeCost e), and connected terminals \
    (G.TerminalsConnected): proves existence of a pure Nash equilibrium s (and finite \
    better-response reachability from any profile s₀) satisfying socialCost s ≤ H k * OPT against \
    all profiles and all centralized Steiner subnetworks F (IsSteinerSubgraph F), matching \
    [TardosWexler2007] §19.3.1 Theorem 19.10. Does not tighten the general-k undirected bound \
    below H_k (#3035)."

register_result "fair-connection-poa-smoothness" where
  title := "Price of anarchy at most k and (k, 0)-smoothness for fair connection games"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2015,
      theorem := "Definition 2.1, derivation (3)–(5), and Theorem 3.2",
      locator := "author's version of 14 July 2015" },
    { paper := TardosWexler2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.FairConnectionGame.isSmooth,
    Cslib.GameTheory.FairConnectionGame.socialCost_le_card_mul_of_isPureNash,
    Cslib.GameTheory.FairConnectionGame.socialCost_le_card_mul_steinerCost_of_isPureNash,
    Cslib.GameTheory.UndirectedFairConnectionGame.socialCost_le_card_mul_of_isPureNash
  ]
  scope := "Directed multigraph and undirected simple-graph fair connection games with nonnegative \
    edge costs: proves (k, 0)-smoothness and deduces socialCost s ≤ k * socialCost s' (and \
    k * steinerCost F) for every pure Nash equilibrium s."

register_result "fair-connection-broadcast-pos-tight" where
  title := "Tightness of the H_k price-of-stability bound on directed single-sink networks"
  topic := "game theory"
  sources := [
    { paper := AnshelevichDKTWR2008, theorem := unverified, locator := unverified },
    { paper := RoughgardenTardos2007, theorem := "Example 17.3", locator := "Figure 17.3" },
    { paper := TardosWexler2007, theorem := unverified, locator := "§19.3.1" }
  ]
  theorems := [
    Cslib.GameTheory.isPureNash_broadcastNetwork_iff,
    Cslib.GameTheory.exists_forall_isPureNash_broadcastNetwork_mul_lt,
    Cslib.GameTheory.isPureNash_broadcastDirect_zero,
    Cslib.GameTheory.isPureNash_broadcastShared_zero
  ]
  scope := "Explicit (k + 2)-vertex directed single-sink broadcastNetwork k ε retaining zero-cost \
    feeder arcs source i → hub, shared trunk of cost 1 + ε, and private bypasses of cost \
    1 / (i + 1) ([RoughgardenTardos2007] Example 17.3 / Figure 17.3): for k ≥ 1 and any r < H k, \
    finds ε > 0 whose unique pure Nash equilibrium has cost > r * (1 + ε); at ε = 0 both the \
    all-direct (cost H k) and all-shared (cost 1) profiles are pure Nash equilibria."

register_result "undirected-broadcast-pos-one" where
  title := "Price of stability 1 in the undirected broadcast network counterpart"
  topic := "game theory"
  sources := [
    { paper := RoughgardenTardos2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.isPureNash_undirectedViaLastProfile,
    Cslib.GameTheory.socialCost_undirectedViaLastProfile_le
  ]
  scope := "Undirected simple-graph counterpart undirectedBroadcastNetwork k ε on Sym2 edges for \
    k ≥ 1 and ε ≥ 0: routing every player via source (k - 1) — sink yields a pure Nash \
    equilibrium globally minimizing social cost at 1 / k (PoS = 1)."

register_result "fair-connection-parallel-poa-tight" where
  title := "Tightness of the price of anarchy k on two-node parallel links"
  topic := "game theory"
  sources := [
    { paper := RoughgardenTardos2007, theorem := unverified, locator := unverified },
    { paper := TardosWexler2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.isPureNash_parallelExpensiveProfile,
    Cslib.GameTheory.socialCost_parallelExpensive_eq_mul_cheap,
    Cslib.GameTheory.exists_strictPureNash_parallelNetwork_mul_lt
  ]
  scope := "Two-node parallel-arc fair connection game parallelNetwork k ε with arcs of costs \
    1 + ε and k for k ≥ 1 players: exact PoA = k at ε = 0 and strict pure Nash equilibrium with \
    ratio k / (1 + ε) > r for any r < k when ε > 0."

register_result "fair-connection-best-nash-not-min-potential" where
  title := "Socially optimal pure Nash equilibrium need not minimize Rosenthal's potential"
  topic := "game theory"
  sources := [
    { paper := TardosWexler2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.potentialGapNetwork_best_nash_not_min_potential
  ]
  scope := "Three-player single-sink network potentialGapNetwork (trunk cost 2, bypasses 6 / 5): \
    proves the socially optimal profile (cost 2, Φ = 11 / 3) is a pure Nash equilibrium whereas \
    the all-direct pure Nash equilibrium (cost 18 / 5, Φ = 18 / 5) strictly minimizes Rosenthal's \
    potential."

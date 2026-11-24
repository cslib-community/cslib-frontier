/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Graphical.Basic
import CslibFrontier.GameTheory.Graphical.TreeNash

/-!
# Collected results: graphical games and `TreeNash`
-/

register_result "kearns-graphical-games-tree-nash" where
  title := "Two-pass TreeNash computes a Nash equilibrium and represents all Nash equilibria \
    of a tree graphical game"
  topic := "game theory"
  sources := [
    { paper := Kearns2007,
      theorem := "Theorem 7.3",
      locator := "Chapter 7, Section 7.3, Figure 7.1, pp. 165–166" }
  ]
  theorems := [
    Cslib.GameTheory.GraphicalGame.treeNash_isMixedNash,
    Cslib.GameTheory.GraphicalGame.isTreeNashOutput_iff_isMixedNash
  ]
  scope := "For any finite graphical game M : GraphicalGame ι S whose interaction graph M.graph \
    is a tree (M.graph.IsTree) rooted at r : ι, the abstract two-pass dynamic program TreeNash \
    over mixed strategy simplices computes a mixed Nash equilibrium M.treeNash hT r when all \
    strategy sets S i are nonempty (treeNash_isMixedNash), and its downstream tables and witness \
    predicates represent every mixed Nash equilibrium of M.toCostGame \
    (isTreeNashOutput_iff_isMixedNash). As in Kearns Section 7.3 before the discretized and \
    rectangular instantiations of Sections 7.3.1–7.3.2, tables are indexed over exact mixed \
    strategies without finite table encoding or machine running-time claims."

register_result "kearns-graphical-games-grid-perturbation" where
  title := "Rounding a Nash equilibrium of a degree-d graphical game to the nearest L1 tau-grid \
    strategy yields a (d * tau)-Nash equilibrium"
  topic := "game theory"
  sources := [
    { paper := Kearns2007,
      theorem := "Lemma 7.4",
      locator := "Chapter 7, Section 7.3.1, p. 167" }
  ]
  theorems := [
    Cslib.GameTheory.GraphicalGame.isApproxNash_nearestGridStrategy,
    Cslib.GameTheory.GraphicalGame.l1_nearestGridStrategy_le_of_mem
  ]
  scope := "For any finite binary-action graphical game M : GraphicalGame ι (fun _ => Bool) with \
    local payoffs in [0, 1], maximum vertex degree at most d, exact mixed Nash equilibrium p of \
    M.toCostGame, and grid resolution m ≥ 1 (grid spacing τ = 1 / m on binaryTauGrid m), \
    nearestGridStrategy m (p i) minimizes L1 distance to p i over binaryTauGrid m (within 1 / m \
    in L1 norm) and fun i => nearestGridStrategy m (p i) is an additive (d * (1 / m))-Nash \
    equilibrium of M (GraphicalGame.IsApproxNash). Proved via the multi-action L1 perturbation \
    lemma isApproxNash_of_l1_le."

register_result "kearns-graphical-games-local-neighborhood-payoff-equiv" where
  title := "Local neighborhood equivalence strictly refines expected payoff equivalence in \
    graphical games"
  topic := "game theory"
  sources := [
    { paper := Kearns2007,
      theorem := "Lemma 7.9",
      locator := "Chapter 7, Section 7.4.1, p. 171" }
  ]
  theorems := [
    Cslib.GameTheory.LocalNeighborhoodEquiv.expectedPayoffEquiv,
    Cslib.GameTheory.exists_graphicalGame_not_expectedPayoffEquiv
  ]
  scope := "Over finitely supported joint action distributions (Convexity.StdSimplex ℝ (∀ i, S i)) \
    for arbitrary player and strategy types ι and S, identical closed-neighborhood marginals \
    with respect to M.graph (LocalNeighborhoodEquiv) imply identical expected payoffs for every \
    player in M (GraphicalGame.ExpectedPayoffEquiv); conversely, whenever two distributions are \
    not local-neighborhood equivalent on G, there exists a {0, 1}-payoff graphical game on G \
    separating their expected payoffs."

register_result "kearns-graphical-games-local-neighborhood-ce" where
  title := "Local neighborhood equivalence preserves correlated equilibria in graphical games"
  topic := "game theory"
  sources := [
    { paper := Kearns2007,
      theorem := "Lemma 7.10",
      locator := "Chapter 7, Section 7.4.1, p. 171" }
  ]
  theorems := [
    Cslib.GameTheory.LocalNeighborhoodEquiv.isCorrelatedEquilibrium_iff
  ]
  scope := "For any graphical game M : GraphicalGame ι S with decidable player equality and any \
    finitely supported joint distributions σ, τ satisfying LocalNeighborhoodEquiv M.graph σ τ, σ \
    is a correlated equilibrium of M.toCostGame (CostGame.IsCorrelatedEquilibrium) if and only if \
    τ is."

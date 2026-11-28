/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Graphical.MarkovNetwork

/-!
# Collected results: local Markov networks and tree correlated equilibria
-/

open Cslib.GameTheory

register_result "kearns-graphical-games-local-markov-network" where
  title := "Local Markov network representation up to local neighborhood equivalence \
    (positive-support, ε-approximate closure, and unconditional tree forms, with C₄ \
    boundary counterexample)"
  topic := "game theory"
  sources := [
    { paper := Kearns2007,
      theorem := "Lemma 7.12 (corrected boundary scope: positive support, ε-closure, and trees)",
      locator := "Chapter 7, Section 7.4.2, Definition 7.11 and Lemma 7.12, pp. 172–174" }
  ]
  theorems := [
    exists_isPositiveLocalMarkovNetwork_of_exists_pos,
    exists_isPositiveLocalMarkovNetwork_neighborhoodMarginal_approx,
    exists_isLocalMarkovNetwork_of_isTree,
    exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4
  ]
  scope := "Over arbitrary finite player types ι and finite action families S : ι → Type*, \
    IsLocalMarkovNetwork G σ formalizes Kearns Definition 7.11 (nonnegative potentials ψ_i ≥ 0 \
    and normalizing factor Z > 0). The literal unguarded textbook statement of Lemma 7.12 is \
    false at zero-support boundary distributions on non-chordal graphs, witnessed by \
    exists_not_localNeighborhoodEquiv_isLocalMarkovNetwork_cycle4 on C₄ with binary actions \
    (uniform weight-1 distribution). Three faithful theorems establish the exact boundary: \
    (1) exists_isPositiveLocalMarkovNetwork_of_exists_pos proves exact strictly positive local \
    Markov network representation via maximum Shannon entropy whenever σ admits a strictly \
    positive local-neighborhood equivalent distribution; \
    (2) exists_isPositiveLocalMarkovNetwork_neighborhoodMarginal_approx proves ε-approximate \
    neighborhood-marginal representation for all graphs G, all distributions σ (zeros allowed), \
    and all ε > 0; and (3) exists_isLocalMarkovNetwork_of_isTree proves exact unconditional \
    nonnegative local Markov network representation (zeros allowed, no positivity) on every \
    finite tree G.IsTree."

register_result "kearns-graphical-games-markov-ce" where
  title := "Local Markov network representation of correlated equilibria in graphical games \
    (positive-support, ε-approximate, and unconditional tree forms, with C₄ boundary \
    counterexample)"
  topic := "game theory"
  sources := [
    { paper := Kearns2007,
      theorem := "Theorem 7.13 (corrected boundary scope: positive support, ε-CE, and trees)",
      locator := "Chapter 7, Section 7.4.2, Theorem 7.13, p. 174" }
  ]
  theorems := [
    GraphicalGame.exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos,
    GraphicalGame.exists_isPositiveLocalMarkovNetwork_isApproxCorrelatedEquilibrium,
    GraphicalGame.exists_isLocalMarkovNetwork_ce_of_isTree,
    exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4
  ]
  scope := "For any finite graphical game M : GraphicalGame ι S and correlated equilibrium σ of \
    M.toCostGame: (1) exists_ce_not_expectedPayoffEquiv_isLocalMarkovNetwork_cycle4 exhibits a \
    binary {0, 1}-payoff graphical game on C₄ and a correlated equilibrium σ whose \
    expected-payoff equivalence class is the singleton {σ}, yet σ is not a local Markov network \
    on C₄ (refuting literal unguarded Theorem 7.13 at zero-support boundary equilibria); \
    (2) exists_isPositiveLocalMarkovNetwork_ce_of_exists_pos proves exact Theorem 7.13 whenever \
    σ admits a strictly positive local-neighborhood equivalent distribution; \
    (3) exists_isPositiveLocalMarkovNetwork_isApproxCorrelatedEquilibrium proves for every game \
    M, every CE σ (zeros allowed), and every ε > 0 that there is a strictly positive local \
    Markov network ε-CE with payoffs and neighborhood marginals within ε of σ; and \
    (4) exists_isLocalMarkovNetwork_ce_of_isTree proves exact unconditional Theorem 7.13 (zeros \
    allowed, no positivity) for every tree graphical game M.graph.IsTree."

register_result "kearns-graphical-games-tree-ce-lp" where
  title := "Local neighborhood linear program exactly characterizes correlated equilibria \
    of tree graphical games"
  topic := "game theory"
  sources := [
    { paper := Kearns2007,
      theorem := "Theorem 7.14",
      locator := "Chapter 7, Section 7.4.3, Theorem 7.14, pp. 174–175" }
  ]
  theorems := [
    GraphicalGame.exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium,
    GraphicalGame.isLocalCorrelatedEquilibrium_iff_exists_isCorrelatedEquilibrium,
    GraphicalGame.treeLocalCE_size_bounds
  ]
  scope := "For any finite tree graphical game M : GraphicalGame ι S (M.graph.IsTree) over \
    arbitrary finite action families S (no positivity hypothesis; zero marginals allowed), \
    M.IsLocalCorrelatedEquilibrium formalizes Kearns's local linear program constraints (i)–(iii) \
    on p. 175 (local CE inequalities, local simplex constraints, and pairwise neighborhood \
    intersection consistency, proved equivalent on trees to edge consistency). \
    exists_isCorrelatedEquilibrium_of_isLocalCorrelatedEquilibrium lifts any feasible local \
    solution q to a global correlated equilibrium σ of M.toCostGame (represented as a \
    nonnegative local Markov network on M.graph) with exact neighborhood marginals q, matching \
    per-player expected payoffs and social welfare; \
    isLocalCorrelatedEquilibrium_iff_exists_isCorrelatedEquilibrium establishes exact soundness \
    and completeness; and treeLocalCE_size_bounds proves the variable count equals \
    M.tableEntries ≤ |ι| * m ^ (d + 1) with at most |ι| * m ^ 2 CE inequalities and \
    2 * (|ι| - 1) * m ^ 2 directed edge-consistency equations. Machine LP solver running-time \
    bounds are not claimed."

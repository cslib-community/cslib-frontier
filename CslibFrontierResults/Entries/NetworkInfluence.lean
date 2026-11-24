/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Network.InfluenceMaximization

/-!
# Collected results: Network influence submodularity (NRTV Chapter 24)
-/

register_result "kkt-diminishing-returns-cascade-submodular" where
  title := "Influence function is submodular for diminishing-returns cascade models"
  topic := "game theory"
  sources := [
    { paper := Kleinberg2007,
      theorem := "Theorem 24.4",
      locator := "Section 24.4, printed pp. 624, 626 (PDF pp. 645, 647)" },
    { paper := KempeKleinbergTardos2003,
      theorem := unverified,
      locator := unverified },
    { paper := KempeKleinbergTardos2005,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Network.CascadeModel.isSubmodular_influence_of_diminishingReturns
  ]
  scope := "For any order-independent CascadeModel C on a finite directed graph G : Digraph V \
    ([DecidableEq V] [Fintype V] [DecidableRel G.Adj], where G.Adj u v means u is an incoming \
    neighbor influencing v, prob v u X ∈ [0, 1] vanishes when ¬ G.Adj u v, and two-step \
    sequential survival (1 - prob v u₁ X) * (1 - prob v u₂ (insert u₁ X)) is symmetric in \
    u₁, u₂), if C.HasDiminishingReturns holds (X ⊆ Y → u ∉ Y → C.prob v u Y ≤ C.prob v u X), \
    then the expected final active-set size C.influence : Finset V → ℝ is submodular \
    (IsSubmodular C.influence). C.influence is schedule-invariant across all valid attempt \
    selectors ValidNextEdge G nextEdge (activeSetProb_congr_schedule); proved by translating C \
    to C.toGeneralThresholdModel (activeSetProb_eq_toGeneralThresholdModel), showing each \
    resulting local threshold function 1 - C.survivalProb v is submodular \
    (isSubmodular_toGeneralThresholdModel_thresholdFn), and applying Mossel–Roch Theorem 24.6 \
    (GeneralThresholdModel.isSubmodular_influence)."

register_result "kkt-independent-cascade-submodular" where
  title := "Influence function is submodular in the Independent Cascade Model"
  topic := "game theory"
  sources := [
    { paper := Kleinberg2007,
      theorem := "Theorem 24.5",
      locator := "Section 24.4, printed pp. 625–626 (PDF pp. 646–647)" },
    { paper := KempeKleinbergTardos2003,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Network.IndependentCascadeModel.isSubmodular_influence
  ]
  scope := "For any IndependentCascadeModel IC on a finite directed graph G : Digraph V \
    ([DecidableEq V] [Fintype V] [DecidableRel G.Adj], edge activation probabilities \
    IC.edgeProb u v ∈ [0, 1] vanishing when ¬ G.Adj u v), the expected final active-set size \
    IC.influence : Finset V → ℝ (= IC.toCascadeModel.influence) is submodular \
    (IsSubmodular IC.influence). Proved via Kleinberg's live-edge graph decomposition \
    (activeSetProb_eq_sum_liveGraphWeight and influence_eq_sum_liveGraphWeight), writing \
    IC.influence S as a nonnegative product-Bernoulli weighted sum over H : Digraph V of the \
    directed reachability coverage sizes |(liveReachable H S)| \
    (isSubmodular_weightedCoverage and isSubmodular_sum)."

register_result "mossel-roch-general-threshold-submodular" where
  title := "Influence function is submodular for General Threshold Models with submodular local \
    thresholds"
  topic := "game theory"
  sources := [
    { paper := Kleinberg2007,
      theorem := "Theorem 24.6",
      locator := "Section 24.4, printed p. 626 (PDF p. 647)" },
    { paper := MosselRoch2007,
      theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.Network.GeneralThresholdModel.isSubmodular_influence
  ]
  scope := "For any GeneralThresholdModel M on a finite directed graph G : Digraph V \
    ([DecidableEq V] [Fintype V] [DecidableRel G.Adj], local threshold functions \
    M.thresholdFn v : Finset V → ℝ depending only on active incoming neighbors inNeighbors G v, \
    monotone, normalized with M.thresholdFn v ∅ = 0 as in Kleinberg §24.4 p. 623, and bounded \
    above by 1), if IsSubmodular (M.thresholdFn v) holds for every v : V, then the expected \
    final active-set size M.influence S = ∫ θ, (M.thresholdFinal θ S).card ∂thresholdMeasure V \
    under independent Uniform[0, 1] vertex thresholds is submodular (IsSubmodular M.influence). \
    Derived from the general functional expectation theorem \
    GeneralThresholdModel.isSubmodular_integral_thresholdFinal via a measure-preserving \
    conditional reflection coupling on [0, 1]^V."

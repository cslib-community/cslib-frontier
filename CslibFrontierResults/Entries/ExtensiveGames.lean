/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Extensive.PerfectInfo
import CslibFrontier.GameTheory.Extensive.SequenceForm

/-!
# Collected results: extensive-form games, backward induction, sequence form, and Kuhn's theorem
-/

register_result "extensive-zermelo-backward-induction" where
  title := "Zermelo's theorem and backward-induction subgame-perfect equilibrium uniqueness"
  topic := "game theory"
  sources := [
    { paper := vonStengel2007,
      theorem := "Algorithm 3.9",
      locator := "Section 3.8, pp. 68–69" }
  ]
  theorems := [
    Cslib.GameTheory.Extensive.PerfectInfoTree.isPureSPE_iff_oneShot,
    Cslib.GameTheory.Extensive.PerfectInfoTree.isPureSPE_backwardInduction,
    Cslib.GameTheory.Extensive.PerfectInfoTree.exists_isPureSPE,
    Cslib.GameTheory.Extensive.PerfectInfoTree.existsUnique_isPureSPE_of_hasNoContinuationTies,
    Cslib.GameTheory.Extensive.PerfectInfoTree.existsUnique_isPureSPE
  ]
  scope := "Finite rooted perfect-information game trees PerfectInfoTree ι with leaves, \
    nonempty finite-action decision nodes, and finite-support chance nodes (for arbitrary \
    DecidableEq ι). Pure strategies assign actions at every decision node of player i, \
    including unreachable subtrees. Bottom-up backwardInduction constructs a pure SPE and Nash \
    equilibrium (isPureSPE_backwardInduction, exists_isPureSPE) unconditionally, matching \
    [vonStengel2007] Section 3.8 / Algorithm 3.9. IsPureSPE holds iff every decision node \
    satisfies local one-shot optimality (isPureSPE_iff_oneShot), and when distinct actions yield \
    distinct continuation values for the deciding player (HasNoContinuationTies) the pure SPE is \
    unique (existsUnique_isPureSPE_of_hasNoContinuationTies), specializing to deterministic trees \
    with pairwise distinct leaf payoffs (existsUnique_isPureSPE); those three results are library \
    additions beyond [vonStengel2007] §3.8. Does not embed PerfectInfoTree into ExtensiveTree."

register_result "extensive-sequence-form-kuhn-theorem" where
  title := "Sequence-form realization plans, Kuhn's theorem, and polytope vertices under perfect \
    recall"
  topic := "game theory"
  sources := [
    { paper := vonStengel2007,
      theorem := "Proposition 3.10, Proposition 3.11, and Corollary 3.12",
      locator := "Sections 3.9–3.10, pp. 69–72" }
  ]
  theorems := [
    Cslib.GameTheory.Extensive.isRealizationPlan_iff,
    Cslib.GameTheory.Extensive.isRealizationPlan_mixedToRealizationPlan,
    Cslib.GameTheory.Extensive.isRealizationPlan_behaviorToRealizationPlan,
    Cslib.GameTheory.Extensive.isBehaviorStrategy_realizationPlanToBehavior,
    Cslib.GameTheory.Extensive.behaviorToRealizationPlan_realizationPlanToBehavior,
    Cslib.GameTheory.Extensive.realizationPlanToBehavior_unique,
    Cslib.GameTheory.Extensive.kuhn_theorem,
    Cslib.GameTheory.Extensive.realizationEquivMixed_iff_mixedToRealizationPlan_eq,
    Cslib.GameTheory.Extensive.isVertex_seqPolyMat_iff,
    Cslib.GameTheory.Extensive.evalMixed_eq_seqPayoffMat,
    Cslib.GameTheory.Extensive.evalBehavior_eq_seqPayoffMat
  ]
  scope := "Finite multi-player extensive-form game trees ExtensiveTree ι H Act over ℝ with \
    finite information sets and finite nonempty action types. Under PerfectRecall T i, \
    realization plans (E x = e, x ≥ 0) match the nonnegativity, root-1, and flow-conservation \
    equations (isRealizationPlan_iff), biject with behavioral strategies modulo irrelevant \
    zero-probability information sets via realizationPlanToBehavior (Proposition 3.10), witness \
    Kuhn's theorem for every mixed strategy (kuhn_theorem, Corollary 3.12), and coincide with the \
    convex hull of pure realization plans whose basic feasible Matrix.IsVertex points equal the \
    pure plans (isVertex_seqPolyMat_iff, corresponding to the unnumbered §3.10 polytope-vertex \
    statement on p. 72), and represent two-player payoffs bilinearly via seqPayoffMat. \
    Realization-equivalence characterization \
    realizationEquivMixed_iff_mixedToRealizationPlan_eq (Proposition 3.11) additionally assumes \
    HasPositiveChance T and NoRepeatedInfoSet T j for opponent players j ≠ i. Zero-sum \
    sequence-form LP and Lemke's LCP algorithm remain open in #7789."

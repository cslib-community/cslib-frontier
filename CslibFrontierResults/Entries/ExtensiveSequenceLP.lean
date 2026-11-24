/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Extensive.PerfectInfoEmbedding
import CslibFrontier.GameTheory.Extensive.SequenceFormLP

/-!
# Collected results: perfect-information embedding, sequence-form LP duality, and minimax
-/

register_result "extensive-perfect-info-embedding" where
  title := "Embedding finite perfect-information trees into extensive-form games and Kuhn's theorem"
  topic := "game theory"
  sources := [
    { paper := vonStengel2007,
      theorem := "Section 3.7 and Corollary 3.12",
      locator := "Section 3.7, pp. 66–68, and Section 3.10, pp. 70–71" }
  ]
  theorems := [
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_isSingletonInfoSet,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_perfectRecall,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_noRepeatedInfoSet,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_evalPure,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_evalPure_ofExtensive,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_isPureNash_iff,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_backwardInduction_isPureNash,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_isMixedNash_iff,
    Cslib.GameTheory.Extensive.PerfectInfoTree.toExtensiveTree_kuhn_theorem
  ]
  scope := "Embeds any finite perfect-information game tree PerfectInfoTree ι with leaves, \
    decision nodes, and finite-support chance nodes into ExtensiveTree ι (T.InfoSet) \
    (fun _ h => h.Act) over ℝ. Every embedded information set is a singleton \
    (toExtensiveTree_isSingletonInfoSet); assuming [DecidableEq ι], the embedded tree satisfies \
    PerfectRecall and NoRepeatedInfoSet for every player i, admits a bijection \
    PureStrategy.toExtensiveEquiv preserving pure payoffs (toExtensiveTree_evalPure, \
    toExtensiveTree_evalPure_ofExtensive) and pure Nash equilibria \
    (toExtensiveTree_isPureNash_iff), and turns backwardInduction into a pure Nash equilibrium \
    of T.toExtensiveTree.toCostGame. Additionally assuming [Fintype ι] and \
    [∀ i, DecidableEq (T.InfoSet i)], mixed Nash equilibria correspond \
    (toExtensiveTree_isMixedNash_iff) and Kuhn's theorem yields an explicit realization-equivalent \
    behavioral strategy for any mixed strategy on T.toExtensiveTree \
    (toExtensiveTree_kuhn_theorem). Does not transfer subgame perfection to ExtensiveTree."

register_result "extensive-sequence-form-lp-minimax" where
  title := "Sequence-form linear programming, Nash complementarity, and zero-sum minimax"
  topic := "game theory"
  sources := [
    { paper := vonStengel2007,
      theorem := "Theorem 3.13 and Theorem 3.14",
      locator := "Sections 3.10–3.11, pp. 72–74" }
  ]
  theorems := [
    Cslib.GameTheory.Extensive.exists_seqMat_transpose_mulVec_ge,
    Cslib.GameTheory.Extensive.exists_isGreatest_isLeast_seqLP,
    Cslib.GameTheory.Extensive.isSeqBestResponseFalse_iff_dual,
    Cslib.GameTheory.Extensive.isSeqBestResponseTrue_iff_dual,
    Cslib.GameTheory.Extensive.isSeqNash_iff_complementarity,
    Cslib.GameTheory.Extensive.isMixedNash_toCostGame_iff_isSeqNash,
    Cslib.GameTheory.Extensive.isBehaviorNash_iff_isSeqNash,
    Cslib.GameTheory.Extensive.exists_isSeqNash,
    Cslib.GameTheory.Extensive.exists_isBehaviorNash,
    Cslib.GameTheory.Extensive.ExtensiveTree.IsZeroSum.seq_weak_duality,
    Cslib.GameTheory.Extensive.ExtensiveTree.IsZeroSum.exists_seq_lp_minimax,
    Cslib.GameTheory.Extensive.ExtensiveTree.IsZeroSum.exists_behavior_minimax
  ]
  scope := "Finite extensive-form game trees over ℝ with PerfectRecall and nonempty finite \
    action sets. For arbitrary [DecidableEq ι] and [Fintype (H i)], bounded dual feasibility \
    (exists_seqMat_transpose_mulVec_ge) and strong LP duality over sequence-form realization plans \
    (exists_isGreatest_isLeast_seqLP) hold for each player i. For two-player games \
    ExtensiveTree Bool H Act with [∀ i h, Fintype (Act i h)], [∀ i h, Nonempty (Act i h)], \
    [Finite (H i)] / [Fintype (H i)], and PerfectRecall T i for both players (plus \
    [∀ i, DecidableEq (H i)] in isMixedNash_toCostGame_iff_isSeqNash), proves KKT/LCP \
    best-response and Nash complementarity characterizations (isSeqNash_iff_complementarity), \
    equivalences between mixed, behavioral, and sequence-form Nash equilibria, existence of \
    sequence-form and behavioral Nash equilibria (exists_isSeqNash, exists_isBehaviorNash), and, \
    under ExtensiveTree.IsZeroSum (z.payoff false + z.payoff true = 0 at every leaf), LP minimax \
    duality and minimax behavioral Nash equilibria (exists_seq_lp_minimax, \
    exists_behavior_minimax). Lemke's LCP pivoting algorithm remains open in #7789."

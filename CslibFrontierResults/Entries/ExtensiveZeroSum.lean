/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Extensive.ZeroSum

/-!
# Collected results: zero-sum extensive-form sparse sequence form, minimax, and subgame perfection
-/

open Cslib.GameTheory.Extensive

register_result "extensive-zero-sum-sequence-minimax" where
  title := "Zero-sum extensive-form sparse sequence form, minimax equivalence, and subgame \
    perfection"
  topic := "game theory"
  sources := [
    { paper := vonStengel1996,
      theorem := unverified,
      locator := unverified },
    { paper := vonStengel2007,
      theorem := "Theorem 3.13",
      locator := unverified }
  ]
  theorems := [
    card_support_seqPayoffMat_le_card_terminal,
    dotProduct_seqPayoffMat_mulVec_eq_sum_support,
    dotProduct_seqPayoffMat_mulVec_eq_sum_terminal,
    ExtensiveTree.HasNoChance.leafSeqPair_injective,
    ExtensiveTree.HasNoChance.seqPayoffMat_leafSeqPair,
    ExtensiveTree.IsZeroSum.isBehaviorNash_iff_saddlePoint,
    ExtensiveTree.IsZeroSum.isSeqNash_iff_saddlePoint,
    ExtensiveTree.IsZeroSum.seq_minimax_duality,
    ExtensiveTree.IsZeroSum.seq_iSup_iInf_eq_iInf_iSup,
    ExtensiveTree.IsZeroSum.isSeqNash_iff_maximin_minimax,
    ExtensiveTree.IsSeqNash.payoff_eq,
    ExtensiveTree.IsSeqNash.interchange,
    ExtensiveTree.IsZeroSum.behavior_iSup_iInf_eq_iInf_iSup,
    ExtensiveTree.IsZeroSum.behavior_minimax_eq_seq_minimax,
    ExtensiveTree.IsZeroSum.isBehaviorNash_iff_maximin_minimax,
    ExtensiveTree.IsZeroSum.isBehaviorNash_of_saddle,
    ExtensiveTree.IsBehaviorNash.evalBehavior_eq,
    ExtensiveTree.IsBehaviorNash.interchange,
    ExtensiveTree.IsZeroSum.mixed_iSup_iInf_eq_iInf_iSup,
    ExtensiveTree.IsZeroSum.mixed_minimax_eq_behavior_minimax,
    ExtensiveTree.IsZeroSum.isMixedNash_evalMixed_eq,
    PerfectInfoTree.isPureSPE_iff_isBehaviorSPE,
    PerfectInfoTree.backwardInduction_isBehaviorSPE,
    PerfectInfoTree.IsZeroSum.backwardInduction_isSeqNash,
    PerfectInfoTree.IsZeroSum.isBehaviorNash_evalBehavior_eq_backwardInduction,
    PerfectInfoTree.IsZeroSum.backwardInduction_snd_eq_seq_minimax,
    PerfectInfoTree.IsZeroSum.isBehaviorSPE_evalBehavior_eq_backwardInduction,
    PerfectInfoTree.IsZeroSum.isPureNash_expectedPayoff_eq_backwardInduction,
    PerfectInfoTree.IsZeroSum.isMixedNash_expectedPayoff_eq_backwardInduction
  ]
  scope := "Finite two-player extensive-form game trees ExtensiveTree Bool H Act over ℝ with \
    nonempty finite action types [∀ i h, Fintype (Act i h)], [∀ i h, Nonempty (Act i h)], finite \
    information sets [Finite (H false)], [Finite (H true)], PerfectRecall T i for both players, \
    and ExtensiveTree.IsZeroSum (z.payoff false + z.payoff true = 0 at every leaf). Bounds \
    nonzero entries of T.seqPayoffMat p by Fintype.card (Terminal T) (and maps leaves \
    injectively to bare payoffs under HasNoChance); proves sequence-form, behavioral, and mixed \
    ⨆⨅ = ⨅⨆ minimax equivalence (with mixed_* additionally assuming [∀ i, Fintype (H i)] and \
    [∀ i, DecidableEq (H i)]), saddle-point and maximin/minimax Nash characterizations, \
    equilibrium interchangeability, and a saddle certificate (isBehaviorNash_of_saddle); and \
    connects PerfectInfoTree Bool backwardInduction and IsBehaviorSPE to minimax values and unique \
    equilibrium payoffs under PerfectInfoTree.IsZeroSum. Note: exact vonStengel1996 / \
    vonStengel2007 page/theorem locators are unverified, and Lemke's LCP pivoting algorithm plus \
    polynomial-time LP solver complexity bounds over ℚ remain open under #7789."

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.MachineLearning.OnlineLearning.Bandit

/-!
# Collected results: partial-information bandit block-exploration reduction (NRTV Chapter 4, §4.6)
-/

register_result "blum-mansour-bandit-block-reduction" where
  title :=
    "Block-exploration reduction from partial-information (bandit) to full-information learning"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007AGT,
      theorem := "Theorem 4.17",
      locator := "Chapter 4, §4.6, pp. 94–96" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.mabPlay_expected_loss_le_two_thirds,
    Cslib.MachineLearning.OnlineLearning.Experts.mabMW_expected_loss_le
  ]
  scope := "Finite nonempty action space of size N, horizon T ≥ N, and [0, 1]-valued oblivious \
    loss sequences (without requiring block count K to divide T; leftover tail rounds play \
    uniformly). Partitioning into K = ⌊(T / N)^{2/3}⌋ blocks of length m = ⌊T / K⌋ under the \
    uniform collision-free exploration schedule ι ↪ Fin m converts any causal full-information \
    algorithm family (IsOnlineAlgorithm) with K-round external regret C √(K ln N) into a \
    partial-information learner (mabPlay, with single-arm feedback causality certified by \
    mabPlay_bandit_congr) achieving expected loss at most minCumLoss ℓ T + (3 + 2 C) T^{2/3} \
    N^{1/3} ln N (mabPlay_expected_loss_le_two_thirds), and 7 T^{2/3} N^{1/3} ln N when \
    instantiated with capped Polynomial Weights mwFactor (mabMW_expected_loss_le). States \
    mathematical expected regret without claiming machine running time."

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.Approximation.Wrapper

/-!
# Collected results: undominated-strategy implementation and iterative wrapper mechanisms
-/

register_result "lavi-wrapper-iteration-bound" where
  title := "Iteration bound for proper subprocedures in the iterative ascending wrapper"
  topic := "mechanism design"
  sources := [
    { paper := Lavi2007,
      theorem := "Lemma 12.38",
      locator := "§12.5, p. 323 (Definitions 12.36–12.37 on p. 322)" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.Wrapper.WrapperProc.termRound_le_of_isProperOn
  ]
  scope := "Finite player type `[Fintype N] [DecidableEq N]` and arbitrary item type `M` under \
    arbitrary full-history deterministic strategies. Proves that whenever `P` is proper \
    (`IsProperOn`: feasible, Pareto maximal, shrinking-sets) along a profile `σ` and every \
    player's wrapper bid stays at most `v_max`, the wrapper terminates (`Terminates P σ`) in at \
    most `2 * Nat.log 2 ⌊v_max⌋₊ + 1` iterations. Holds for all `v_max ≥ 1` (including the \
    tight boundary `v_max = 1`, where `termRound ≤ 1`). No machine-model running-time claim is \
    made."

register_result "lavi-ksm-wrapper-dominant-approx" where
  title := "Dominant-strategy O(log(v_max) * c)-approximation for known single-minded players via \
    the iterative wrapper"
  topic := "mechanism design"
  sources := [
    { paper := Lavi2007,
      theorem := "Theorem 12.45",
      locator := "§12.5, p. 324 (Definition 12.40 and Proposition 12.41 on p. 323; \
        Definition 12.42 and Claims 12.43–12.44 on p. 324)" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.Wrapper.ksmProc_isDominantStrategyImpl,
    Cslib.GameTheory.Mechanism.Wrapper.ksmDominantStrategy_isDominant,
    Cslib.GameTheory.Mechanism.Wrapper.ksmProc_isLocalApproxOn,
    Cslib.GameTheory.Mechanism.Wrapper.WrapperProc.optWelfare_rBar_le
  ]
  scope := "Finite player type `[Fintype N] [LinearOrder N]` and finite item type \
    `[Fintype M] [DecidableEq M]` with arbitrary full-history adaptive deterministic strategies \
    and known nonempty desired bundles `bundle i` with `1 ≤ v i ≤ v_max`. Given any feasible \
    `c`-approximation algorithm `alg` (`0 ≤ c`), `Wrapper + KSM-PROC` is a dominant-strategy \
    implementation achieving explicit welfare approximation \
    `1 + 2 * (2 * Nat.log 2 ⌊v_max⌋₊ + 1) * c = O(log(v_max) * c)` for all `v_max ≥ 1`. \
    Formalizes the game-theoretic dominance, iteration-count, and welfare-approximation \
    guarantees; the machine-model polynomial running-time clause of Definition 12.35 (p. 321) \
    remains open under #7789. Precision notes: (1) Definition 12.42 (p. 324) prints `W_j` where \
    `W_{j+1}` (as used in Lemma 12.47, p. 325) is needed so `j = 0` does not vanish; (2) Claim \
    12.44's printed `5 * log(v_max) * c` vanishes at `v_max = 1`, whereas \
    `2 * (2 * ⌊log₂ v_max⌋ + 1) * c` holds for all `v_max ≥ 1`; (3) at a power-of-two tie \
    `2 * v_i^j = v̄_i` both doubling and retiring yield utility `0`, and `ksmDominantStrategy` \
    (retire on tie) satisfies the exact retirement biconditional of Proposition 12.41."

register_result "lavi-1ca-wrapper-undominated-approx" where
  title := "Implementation in undominated strategies achieving O(log²(v_max) * √m)-approximation \
    for single-value combinatorial auctions"
  topic := "mechanism design"
  sources := [
    { paper := Lavi2007,
      theorem := "Theorem 12.51",
      locator := "§12.5, p. 327 (Definition 12.35 on p. 321; Definition 12.46 and Lemma 12.47 on \
        pp. 325–326; Definition 12.48, Lemma 12.49, and Claim 12.50 on pp. 326–327)" }
  ]
  theorems := [
    Cslib.GameTheory.Mechanism.Wrapper.oneCaProc_isUndominatedImpl,
    Cslib.GameTheory.Mechanism.Wrapper.dominateOneCaStrategy_weaklyDominates,
    Cslib.GameTheory.Mechanism.Wrapper.oneCaProc_isLocalApproxOn,
    Cslib.GameTheory.Mechanism.Wrapper.WrapperProc.optWelfare_shrunkLosers_le,
    Cslib.GameTheory.Mechanism.Wrapper.WrapperProc.optWelfare_le_of_firstTimeShrink
  ]
  scope := "Finite player type `[Fintype N] [LinearOrder N]` and finite nonempty item type \
    `[Fintype M] [DecidableEq M] [Nonempty M]` with single-value valuations `(v̄_i, S̄_i)` \
    (`1 ≤ v̄_i ≤ v_max`, upward-closed, normalized `∅ ∉ S̄_i`, nonempty) and arbitrary \
    full-history adaptive deterministic strategies. Proves that `Wrapper + 1-CA-PROC` implements \
    an explicit `(1 + 2 * (2 ⌊log₂ v_max⌋ + 1) * (2 ⌊log₂ v_max⌋ + 2) * (3 + 2 √m))` = \
    `O(log²(v_max) * √m)` welfare approximation in undominated strategies (`oneCaStrategyClass`, \
    with explicit weak-dominance map `dominateOneCaStrategy`). Formalizes the game-theoretic \
    weak-dominance, iteration-count, and welfare-approximation guarantees; the machine-model \
    polynomial running-time and polynomial-time dominance-transition clauses of Definition 12.35 \
    (p. 321) remain open under #7789. Precision notes: (1) Theorem 12.51 (p. 327) prints \
    `O(log²(v_max) * c)` where `√m` is intended from Lemma 12.47 (`c = 3 + 2 √m`); (2) \
    `IsLoserIfSilent` states the exact silent-loser condition across `W_cur, M_cur, GREEDY_j` \
    (covering `j = 0` where `W_0 = ∅`), `1-CA-PROC` requires nonempty shrunk bundles \
    (`1 ≤ |b| ≤ ⌊√m⌋`) so Pareto holds on all profiles, and `oneCaStrategyClass` requires \
    `s_i^j ∈ S̄_i` at every round so `s_i^J ∈ S̄_i` holds in Claim 12.50."

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.QueryComplexity
import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Communication

/-!
# Collected results: combinatorial auctions, query complexity and communication lower bounds
-/

register_result "blumrosen-nisan-value-query-from-demand-queries" where
  title := "Simulating a value query with m * t item-price demand queries"
  topic := "game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Lemma 11.22",
      locator := "§11.5.1, p. 284" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.eval_valueQueryProg,
    Cslib.GameTheory.CombinatorialAuction.countQueries_valueQueryProg,
    Cslib.GameTheory.CombinatorialAuction.countQueries_valueQueryProg_le
  ]
  scope := "Normalized (v ∅ = 0) monotone valuations v : Finset M → ℝ whose bundle values are \
    t-bit nonnegative integers in {0, 1, ..., 2 ^ t - 1} (fixed-point valuations with t bits of \
    precision and known quantum δ > 0 reduce by scaling prices by δ). The FreeM (DemandQuery M) \
    program valueQueryProg t S telescopes t-step binary searches marginalValueProg over S using \
    half-integer test prices thresh - 1 / 2 and prohibitive outside price 2 ^ t (eliminating \
    demand tie-breaking ambiguity across every valid demand oracle). It recovers v S exactly in \
    S.card * t ≤ Fintype.card M * t demand queries. Bounds measure FreeM oracle query count only; \
    no machine running-time claim is made."

register_result "blumrosen-nisan-demand-query-value-lower-bound" where
  title := "Exponential value-query lower bound for simulating a demand query and finding an \
    optimal allocation"
  topic := "game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Lemma 11.23 and Exercise 11.3",
      locator := "§11.5.1, p. 284; Chapter 11 Exercises, p. 298" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.choose_half_le_countQueries_demandSim,
    Cslib.GameTheory.CombinatorialAuction.countQueries_oneDemandQueryOptimalAlloc,
    Cslib.GameTheory.CombinatorialAuction.eval_oneDemandQueryOptimalAlloc_optimal,
    Cslib.GameTheory.CombinatorialAuction.choose_half_sub_one_le_countQueries_optimalAlloc
  ]
  scope := "Finite item type [Fintype M] [DecidableEq M] with 2 ≤ Fintype.card M and deterministic \
    FreeM (ValueQuery M ℝ) programs. On the normalized monotone valuation class \
    IsSeparatorClassVal M (thresholdBaseVal M and single-bundle bumps hiddenBundleVal M T for \
    |T| = m / 2), uniform price separatorPrice M = 4 / (2 * (m / 2) + 1) makes ∅ the unique demand \
    of thresholdBaseVal M and T the unique demand of hiddenBundleVal M T. Every deterministic \
    value-query program simulating a demand query at separatorPrice M makes at least \
    m.choose (m / 2) value queries on thresholdBaseVal M (Lemma 11.23). Paired with bidder 1's \
    fixed normalized monotone valuation complementThresholdVal M, oneDemandQueryOptimalAlloc M \
    finds an optimal allocation in 1 demand query, whereas every deterministic value-query solver \
    (even with free knowledge of bidder 1) makes at least m.choose (m / 2) - 1 value queries \
    (Exercise 11.3). Bounds are exact deterministic oracle query counts; randomized algorithms are \
    not modeled."

register_result "blumrosen-nisan-dual-valuation-fooling-lemma" where
  title := "Dual-valuation fooling property for two-bidder 0/1 combinatorial auctions"
  topic := "game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Lemma 11.26",
      locator := "§11.6.2, pp. 288–289" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.leaf_dual_ne_of_ne
  ]
  scope := "Deterministic two-party communication protocols (Cslib.Communication.Protocol) \
    computing a welfare-maximizing allocation Allocation (Fin 2) M on pairs of normalized monotone \
    0/1 valuations MonotoneZeroOneVal M satisfying v(M) = 1. Distinct valuations u ≠ v reach \
    distinct protocol leaves on (v, v.dual hv) and (u, u.dual hu). Normalization v(∅) = 0 is \
    necessary (without it, constant u ≡ 0 and v ≡ 1 share a common optimal allocation across all \
    four rectangle corners, refuted in CombinatorialAuctionQueryComm tests), and v(M) = 1 ensures \
    that v.dual is itself normalized."

register_result "blumrosen-nisan-combinatorial-auction-communication-lower-bound" where
  title := "Exponential communication complexity lower bound for optimal combinatorial auctions"
  topic := "game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Theorem 11.25",
      locator := "§§11.6.1–11.6.2, pp. 288–289" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.choose_half_le_depth,
    Cslib.GameTheory.CombinatorialAuction.choose_half_le_ecomplexity
  ]
  scope := "Deterministic two-party communication protocols (Cslib.Communication.Protocol) over \
    any nonempty finite item type [Fintype M] [Nonempty M] solving OptimalTwoBidderAlloc on all \
    pairs of normalized monotone 0/1 valuations MonotoneZeroOneVal M. Every solving protocol has \
    depth at least (Fintype.card M).choose (Fintype.card M / 2), giving the same lower bound on \
    Protocol.ecomplexity. The hypothesis [Nonempty M] is sharp: at m = 0, 0.choose 0 = 1 while a \
    0-bit protocol succeeds (witnessed in CombinatorialAuctionQueryComm tests). For m ≥ 2 the \
    bound follows from Lemma 11.26 on the 2 ^ (m.choose (m / 2)) middle-slice valuations; for \
    m = 1 it follows directly from (vOne, vZero) vs. (vZero, vOne)."

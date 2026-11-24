/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.SingleMinded

/-!
# Collected results: single-minded combinatorial auctions (NRTV Ch. 11 §11.2)
-/

open Cslib.GameTheory.CombinatorialAuction.SingleMinded in
register_result "blumrosen-nisan-single-minded-dsic-char" where
  title := "Characterization of truthful mechanisms for single-minded bidders"
  topic := "algorithmic game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Lemma 11.9",
      locator := "§11.2.2, pp. 274–275" }
  ]
  theorems := [
    Mechanism.isWeakMonotone_of_isDSIC,
    Mechanism.hasCriticalPayments_of_isDSIC,
    Mechanism.isDSIC_of_isWeakMonotone,
    Mechanism.isDSIC_and_isIR_and_hasNonnegPayment_iff
  ]
  scope := "Single-minded combinatorial auction mechanisms over arbitrary bidder type N and item \
    type M with real-valued nonnegative bids (v* ≥ 0) and exact winner-set allocations \
    (winners receive their declared bundle S*, losers receive nothing and pay 0). The exact \
    two-way equivalence requires three side conditions pinned against the printed statement in \
    BlumrosenNisan2007, Lemma 11.9 (p. 274): (1) weak monotonicity in strict-value form \
    (S' ⊆ S* and v* < v'), since non-strict v* ≤ v' fails at the critical-value tie; \
    (2) individual rationality (IsIR) and (3) nonnegative payments (HasNonnegPayment), ruling out \
    degenerate constant-winning mechanisms with shifted payments when no losing bid exists. \
    Necessity of weak monotonicity needs neither IsIR nor HasNonnegPayment; sufficiency proves \
    DSIC, IsIR, and HasNonnegPayment with no tie-breaking assumption. Counterexamples witnessing \
    tightness of all three boundary conditions live in CslibFrontierTests.GameTheory.SingleMinded."

register_result "blumrosen-nisan-los-sqrt-m-approx" where
  title := "Greedy √m-approximation for single-minded combinatorial auctions (LOS)"
  topic := "algorithmic game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Lemma 11.10",
      locator := "§11.2.2, p. 275" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.SingleMinded.losWinners_approx
  ]
  scope := "Holds for every finite bidder type N with deterministic linear tie-breaking order, \
    every finite nonempty item type M (m = Fintype.card M ≥ 1), every nonnegative bid profile \
    b : N → SingleMindedBid M (including bids with empty desired bundle S* = ∅), and every \
    compatible (pairwise disjoint) winner set OPT : Finset N. Uses Mathlib's Cauchy–Schwarz \
    inequality directly on the per-winner blocked subset OPT_i (matching displays (11.1)–(11.2) \
    on p. 275). The Nonempty M hypothesis is tight when empty bundles are allowed (a single \
    bid (∅, 1) on m = 0 fails 1 ≤ √0 · 1). The companion LOS greedy mechanism properties \
    (losWinners_isCompatible, losWinners_isMonotone, losPayment_eq_criticalValue, \
    losPayment_eq_first_blocked, losMechanism_isDSIC, losMechanism_isIR) establish the \
    non-computational parts of Theorem 11.8 (p. 273) with Figure 11.1's printed payment typo \
    repaired (restoring k ∈ W); the polynomial-time clause of Theorem 11.8 is not formalized \
    here and remains open under #7789."

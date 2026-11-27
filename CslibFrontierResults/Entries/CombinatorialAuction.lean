/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Walrasian

/-!
# Collected results: combinatorial auctions, Walrasian equilibrium and LP relaxation
-/

register_result "blumrosen-nisan-first-welfare-theorem" where
  title := "First Welfare Theorem for combinatorial auctions (integral and fractional)"
  topic := "game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Theorem 11.13",
      locator := "§11.3.2, pp. 277–278 (LPR (11.3)–(11.6) on p. 276; Definition 11.12 on p. 277)" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.IsWalrasianEquilibrium.welfare_le,
    Cslib.GameTheory.CombinatorialAuction.IsWalrasianEquilibrium.lprObjective_le
  ]
  scope := "Finite bidder and item types [Fintype N] [Fintype M] with real valuations \
    v : N → Finset M → ℝ (no monotonicity assumption required). The integral form welfare_le \
    holds for arbitrary real valuations without normalization. The fractional form \
    lprObjective_le dominates every LPR-feasible x : N → Finset M → ℝ under the minimal \
    assumption ∀ i, 0 ≤ v i ∅ (strictly weaker than the normalization v i ∅ = 0 of \
    Definition 11.1, p. 268); this assumption is necessary because scaling ∑ S, x i S ≤ 1 by \
    a bidder's equilibrium utility in display (11.10) requires nonnegative utility."

register_result "blumrosen-nisan-second-welfare-theorem" where
  title := "Second Welfare Theorem for combinatorial auctions"
  topic := "game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Theorem 11.15",
      locator := "§11.3.2, pp. 278–279 (DLPR (11.7)–(11.9) on p. 276)" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.exists_isWalrasianEquilibrium_of_lprObjective_le,
    Cslib.GameTheory.CombinatorialAuction.exists_isWalrasianEquilibrium_of_isIntegral
  ]
  scope := "Finite bidder and item types [Fintype N] [Fintype M] with real valuations \
    v : N → Finset M → ℝ (no monotonicity assumption required), proved via strong linear \
    programming duality (Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg). The allocation \
    form exists_isWalrasianEquilibrium_of_lprObjective_le requires no normalization. The 0–1 \
    vector form exists_isWalrasianEquilibrium_of_isIntegral takes any feasible optimal x with \
    x i S ∈ {0, 1} and builds a supporting Walrasian equilibrium for the induced allocation \
    toAllocation (assigning ∅ to bidders with ∀ S, x i S = 0) under ∀ i, 0 ≤ v i ∅. No \
    polynomial-time or oracle-query claim is made."

register_result "blumrosen-nisan-walrasian-iff-integral-lpr" where
  title := "Existence of a Walrasian equilibrium iff LPR admits an integral optimal solution"
  topic := "game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Corollary 11.16",
      locator := "§11.3.2, p. 279" }
  ]
  theorems := [
    Cslib.GameTheory.CombinatorialAuction.exists_isWalrasianEquilibrium_iff
  ]
  scope := "Finite bidder and item types [Fintype N] [Fintype M] with real valuations \
    v : N → Finset M → ℝ satisfying ∀ i, 0 ≤ v i ∅ (strictly weaker than the normalization \
    v i ∅ = 0 of Definition 11.1, p. 268; monotonicity is not required). States that a \
    Walrasian equilibrium exists iff LPR admits a 0–1 optimal solution x; the companion lemma \
    exists_isIntegral_isLPROptimal_iff equates the latter with existence of an allocation \
    dominating every LPR-feasible vector. No polynomial-time or oracle-query claim is made."

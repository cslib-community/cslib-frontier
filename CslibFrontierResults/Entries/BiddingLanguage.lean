/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.BiddingLanguage

/-!
# Collected results: combinatorial auction bidding languages (NRTV Ch. 11 §11.4 & Exercise 11.5)
-/

open Cslib.GameTheory.CombinatorialAuction in
register_result "blumrosen-nisan-or-xor-expressiveness" where
  title := "Expressiveness and additive/unit-demand separations of OR and XOR bidding languages"
  topic := "algorithmic game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "§11.4.1 & Definition 11.17",
      locator := "§11.4.1, pp. 280–281" }
  ]
  theorems := [
    exists_xorBid_of_monotone,
    exists_orBid_of_isSuperadditive,
    exists_orBid_iff_monotone_and_isSuperadditive,
    exists_orBid_additiveValuation,
    xorBid_length_ge_additiveValuation,
    exists_xorBid_unitDemandValuation,
    not_exists_orBid_unitDemandValuation
  ]
  scope := "Finite item type M with real valuations v : Finset M → ℝ and atomic bids \
    SingleMindedBid M. Every normalized (v ∅ = 0) monotone valuation is represented by an XOR bid \
    of size 2 ^ |M| - 1 (exists_xorBid_of_monotone). A normalized valuation is represented by an \
    OR bid iff it is monotone and superadditive on disjoint bundles \
    (exists_orBid_iff_monotone_and_isSuperadditive; \
    normalization rules out positive-price empty-bundle atoms, which break superadditivity as \
    witnessed in CslibFrontierTests.GameTheory.BiddingLanguage). Nonnegative additive valuations \
    have OR size |M| while strictly positive ones require XOR size ≥ 2 ^ |M| - 1; nonnegative \
    unit-demand valuations have XOR size |M| while any with two positive items cannot be \
    represented by any OR bid."

open Cslib.GameTheory.CombinatorialAuction in
register_result "blumrosen-nisan-downward-sloping-or-of-xor" where
  title := "Size-m² OR-of-XORs representation of downward-sloping symmetric valuations"
  topic := "algorithmic game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Lemma 11.20",
      locator := "§11.4.2, p. 281 (Definitions 11.18–11.19 on p. 281)" }
  ]
  theorems := [
    exists_orOfXor_downwardSlopingValuation,
    xorBid_length_ge_downwardSlopingValuation,
    not_exists_orBid_downwardSlopingValuation
  ]
  scope := "Finite item type M of cardinality m = Fintype.card M and downward-sloping symmetric \
    valuation downwardSlopingValuation w with w antitone and nonnegative on {0, ..., m - 1}. \
    Constructs an explicit OR-of-XORs BidFormula (IsOrOfXor) of exact size m ^ 2 (using m XOR \
    clauses of m single-item atoms each; for m = 0 this is the empty formula BidFormula.zero of \
    size 0). Companion lower bounds prove that strictly positive marginals require XOR size \
    ≥ 2 ^ m - 1 and that w 1 < w 0 with m ≥ 2 rules out any OR representation."

open Cslib.GameTheory.CombinatorialAuction in
register_result "blumrosen-nisan-orstar-simulation" where
  title := "OR* simulation of general OR/XOR bidding formulae with dummy items"
  topic := "algorithmic game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Theorem 11.21",
      locator := "§11.4.3, pp. 282–283" }
  ]
  theorems := [
    exists_orStarBid_of_bidFormula
  ]
  scope := "Arbitrary item type M (no Fintype M required) and any BidFormula f of size s with \
    nonnegative atomic bid values (∀ b ∈ f.atoms, 0 ≤ b.value). Produces an OR* bid b on \
    M ⊕ Fin d of exact size s using d ≤ s.choose 2 (hence d ≤ s ^ 2, matching the book's proof \
    bound on p. 282) dummy items, one per XOR-conflicting pair of atomic bids, with \
    b.eval = f.eval and all atomic values nonnegative. No algorithmic winner-determination \
    running-time claim is made."

open Cslib.GameTheory.CombinatorialAuction in
register_result "blumrosen-nisan-majority-orstar-lower-bound" where
  title := "Exponential OR* size lower bound for the majority valuation"
  topic := "algorithmic game theory"
  sources := [
    { paper := BlumrosenNisan2007,
      theorem := "Exercise 11.5",
      locator := "Exercises, p. 299" }
  ]
  theorems := [
    majorityValuation_orStarBid_size_ge,
    thresholdValuation_orStarBid_size_ge
  ]
  scope := "Finite item type M of cardinality m = Fintype.card M and arbitrary finite dummy item \
    type D (no nonnegativity assumption on atomic prices required). Proves generally that any OR* \
    bid representing thresholdValuation k (assigning 1 to bundles of size ≥ k and 0 otherwise) \
    has size at least m.choose k. Specializing to majorityValuation M = thresholdValuation \
    ((m + 1) / 2), which matches (m : ℝ) / 2 ≤ S.card for every m : ℕ and is normalized for all \
    m ≥ 1, yields size ≥ m.choose (m / 2) since m.choose ((m + 1) / 2) = m.choose (m / 2)."

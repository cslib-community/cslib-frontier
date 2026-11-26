/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Fintype.OrderStatistic
public import CslibFrontier.GameTheory.Mechanism.CriticalBid
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Prior-free digital goods auctions and profit extraction

In a *digital goods auction* ([HartlineKarlin2007], Example 13.2, §13.1, p. 332), an auctioneer
sells an unlimited supply of identical copies of a zero-cost item (`c(x) = 0`) to single-parameter
bidders `i : ι`, each wanting one unit with private valuation `bᵢ ≥ 0`. Because there is no
feasibility constraint and marginal cost is zero, a digital goods auction is a `0`-`1`
`SingleParameter.Mechanism ι` whose profit on a nonnegative bid profile `b` is the total payment
`∑ i, M.payment b i`.

This module formalizes the profit-extraction framework of [HartlineKarlin2007], §13.4 (pp. 344–348
and Exercise 13.10, p. 361):

* the optimal single-price profit benchmarks `ℱ` (Definition 13.39, p. 347) and `ℱ⁽²⁾`
  (Definition 13.34, p. 345), defined without sorting as optima over candidate prices `b j` and
  proved equivalent (`singlePriceProfitOn_eq_sup_orderStatistic`) to the order-statistic formulas
  `max_{k ≥ m} k · v_(k)` via `Fintype.orderStatistic`;
* the competitive-ratio predicate `IsCompetitive` (multiplying through in Definition 13.33,
  §13.4.1, p. 345, to avoid `0 / 0`);
* the profit extractor `ProfitExtract_R` (`profitExtractOn`, Definition 13.40, p. 347), which is
  DSIC, individually rational, normalized, coincides with `criticalBidMechanism`, and extracts
  profit `R` whenever `0 ≤ R ≤ ℱ(b)` and `0` otherwise (Exercise 13.10, p. 361);
* the Random Sampling Profit Extraction auction `RSPE` (`rspe`, Definition 13.41, p. 348),
  represented as a family of deterministic mechanisms indexed by the fair-coin partition
  `s : Finset ι` (each universally truthful and individually rational, hence also truthful in
  expectation, Definition 13.5, p. 334), with expected profit `rspeExpectedProfit` averaged
  uniformly over all `2^|ι|` subsets via `Finset.expect`;
* **Theorem 13.42** (§13.4.5, p. 348): `RSPE` has competitive ratio exactly `4` against `ℱ⁽²⁾`
  for every finite bidder type with at least two bidders (`rspe_isCompetitive`,
  `exists_rspe_tight`, `isLeast_rspe_competitiveRatio`).

We make no running-time claim in this module. Two inaccuracies in [HartlineKarlin2007], p. 348,
are noted and repaired:
1. The intuition paragraph after Definition 13.41 prints `R' = ℱ⁽²⁾(b')` and `R'' = ℱ⁽²⁾(b'')`,
   whereas Definition 13.41(ii) and the proof of Theorem 13.42 use `ℱ(b')` and `ℱ(b'')`. We use
   `ℱ` (`optimalProfitOn`).
2. The prose and proof of Theorem 13.42 state that the realized profit of `RSPE` equals
   `min(R', R'')`. When `R' = R'' > 0`, both halves extract profit simultaneously, yielding
   `R' + R'' = 2 * R'` (see `sum_payment_rspe_eq` and the checked counterexample `b = (1, 1)` in
   `CslibFrontierTests.GameTheory.DigitalGoods`). The lower bound `min(R', R'') ≤ profit` always
   holds (`min_le_sum_payment_rspe`), with equality whenever `R' ≠ R''`.

## Main definitions

* `singlePriceProfitOn`: optimal single-price profit from a bidder subset `s` selling to at least
  `m` winners.
* `optimalProfitOn`, `optimalProfit`, `optimalProfitTwo`: specializations `ℱ(b_s)`, `ℱ(b)`
  ([HartlineKarlin2007], Definition 13.39), and `ℱ⁽²⁾(b)` (Definition 13.34).
* `IsCompetitive`: multiplicative competitive-ratio predicate (Definition 13.33).
* `profitExtractSize`, `profitExtractOn`, `profitExtract`: `ProfitExtract_R` (Definition 13.40).
* `rspe`, `rspeExpectedProfit`: the `RSPE` auction per partition and its expected profit
  (Definition 13.41).

## Main results

* `singlePriceProfitOn_eq_sup_orderStatistic`: equivalence with `max_{m ≤ k ≤ n} k · v_(k)`.
* `profitExtractOn_isDSIC`, `profitExtractOn_isIR`, `profitExtractOn_isNormalized`,
  `profitExtractOn_payment_eq_criticalBid`: `ProfitExtract_R` is DSIC, IR, normalized, and its
  payment equals the critical bid ([HartlineKarlin2007], Exercise 13.10).
* `sum_payment_profitExtractOn`, `sum_payment_profitExtract_of_le`: total profit of
  `ProfitExtract_R` is `R` when `0 ≤ R ≤ ℱ(b)` and `0` when `ℱ(b) < R` (Exercise 13.10).
* `rspe_isDSIC`, `rspe_isIR`, `rspe_isNormalized`, `rspe_truthfulInExpectation`: `RSPE` is
  universally truthful, IR, normalized, and truthful in expectation.
* `sum_payment_rspe_eq`, `min_le_sum_payment_rspe`: exact realized profit of `RSPE` on a partition
  and its `min(R', R'')` lower bound.
* `rspe_isCompetitive`, `exists_rspe_tight`, `isLeast_rspe_competitiveRatio`: **Theorem 13.42**,
  `RSPE` has competitive ratio exactly `4` with respect to `ℱ⁽²⁾`.

## References

* [J. D. Hartline and A. R. Karlin, *Profit Maximization in Mechanism Design*, Chapter 13 of
  *Algorithmic Game Theory*][HartlineKarlin2007]
-/

open Finset
open scoped BigOperators

public section

namespace Cslib.GameTheory.SingleParameter.DigitalGoods

/-! ### Optimal single-price profit benchmarks (`ℱ` and `ℱ⁽²⁾`) -/

section Benchmarks

variable {ι : Type*}

open Classical in
/-- The optimal single-price profit obtainable from bidders in `s` when selling to at least `m`
winners on bid profile `b`. Defined without sorting as the maximum of `b j * #{i ∈ s | b j ≤ b i}`
over all `j ∈ s` whose bid is accepted by at least `m` bidders in `s` (or `0` when no such `j`
exists, in particular when `s.card < m`).

For `m = 1` on `s = Finset.univ` this is `ℱ(b)` ([HartlineKarlin2007], Definition 13.39, §13.4.4,
p. 347); for `m = 2` it is `ℱ⁽²⁾(b)` (Definition 13.34, §13.4.2, p. 345). On nonnegative bids with
`1 ≤ m ≤ |ι|`, `singlePriceProfitOn_eq_sup_orderStatistic` shows this agrees with the book's
order-statistic formula `max_{m ≤ k ≤ n} k · v_(k)`. -/
@[expose] noncomputable def singlePriceProfitOn (m : ℕ) (s : Finset ι) (b : ι → ℝ) : ℝ :=
  if h : (s.filter fun j => m ≤ (s.filter fun i => b j ≤ b i).card).Nonempty then
    (s.filter fun j => m ≤ (s.filter fun i => b j ≤ b i).card).sup' h fun j =>
      b j * ((s.filter fun i => b j ≤ b i).card : ℝ)
  else 0

/-- The optimal single-price profit `ℱ(b_s)` from bidder subset `s` (at least one winner). -/
noncomputable abbrev optimalProfitOn (s : Finset ι) (b : ι → ℝ) : ℝ :=
  singlePriceProfitOn 1 s b

/-- The optimal single-price profit `ℱ(b)` over all bidders ([HartlineKarlin2007], Definition 13.39,
§13.4.4, p. 347). -/
noncomputable abbrev optimalProfit [Fintype ι] (b : ι → ℝ) : ℝ :=
  singlePriceProfitOn 1 Finset.univ b

/-- The optimal single-price profit `ℱ⁽²⁾(b)` with at least two winners ([HartlineKarlin2007],
Definition 13.34, §13.4.2, p. 345). -/
noncomputable abbrev optimalProfitTwo [Fintype ι] (b : ι → ℝ) : ℝ :=
  singlePriceProfitOn 2 Finset.univ b

/-- The optimal single-price profit over an empty bidder set is `0`. -/
@[simp]
theorem singlePriceProfitOn_empty (m : ℕ) (b : ι → ℝ) :
    singlePriceProfitOn m ∅ b = 0 := by
  unfold singlePriceProfitOn
  simp only [filter_empty, Finset.not_nonempty_empty, ↓reduceDIte]

/-- If fewer than `m` bidders are in `s`, then `singlePriceProfitOn m s b = 0`. -/
theorem singlePriceProfitOn_eq_zero_of_card_lt {m : ℕ} {s : Finset ι} (b : ι → ℝ)
    (hs : s.card < m) : singlePriceProfitOn m s b = 0 := by
  classical
  exact dite_eq_right fun ⟨j, hj⟩ =>
    not_le_of_gt hs ((mem_filter.1 hj).2.trans (card_filter_le s _))

/-- `singlePriceProfitOn m s b` depends only on the values of `b` on `s`. -/
theorem singlePriceProfitOn_congr {m : ℕ} {s : Finset ι} {b b' : ι → ℝ}
    (h : ∀ i ∈ s, b i = b' i) :
    singlePriceProfitOn m s b = singlePriceProfitOn m s b' := by
  classical
  have hf : ∀ j ∈ s,
      (s.filter fun i => b j ≤ b i) = (s.filter fun i => b' j ≤ b' i) := fun j hj =>
    filter_congr fun i hi => by rw [h j hj, h i hi]
  have hc : (s.filter fun j => m ≤ (s.filter fun i => b j ≤ b i).card) =
      (s.filter fun j => m ≤ (s.filter fun i => b' j ≤ b' i).card) :=
    filter_congr fun j hj => by rw [hf j hj]
  unfold singlePriceProfitOn
  by_cases h1 : (s.filter fun j => m ≤ (s.filter fun i => b j ≤ b i).card).Nonempty
  · rw [dite_eq_left h1, dite_eq_left (hc ▸ h1)]
    exact sup'_congr h1 hc fun j hj => by rw [hf j (mem_filter.1 hj).1, h j (mem_filter.1 hj).1]
  · rw [dite_eq_right h1, dite_eq_right (hc ▸ h1)]

/-- `singlePriceProfitOn m s b` is nonnegative whenever all bids in `s` are nonnegative. -/
theorem singlePriceProfitOn_nonneg {m : ℕ} {s : Finset ι} {b : ι → ℝ}
    (hb : ∀ i ∈ s, 0 ≤ b i) : 0 ≤ singlePriceProfitOn m s b := by
  unfold singlePriceProfitOn
  split_ifs with hne
  · obtain ⟨j, hj⟩ := hne
    exact le_sup'_of_le _ hj (mul_nonneg (hb j (mem_filter.1 hj).1) (Nat.cast_nonneg _))
  · exact le_rfl

/-- Every set `W ⊆ s` of at least `m` bidders all bidding at least `p` gives a lower bound
`p * W.card ≤ singlePriceProfitOn m s b`. -/
theorem mul_card_le_singlePriceProfitOn {m : ℕ} {s W : Finset ι} {b : ι → ℝ} {p : ℝ}
    (hb : ∀ i ∈ s, 0 ≤ b i) (hWs : W ⊆ s) (hWm : m ≤ W.card) (hp : ∀ i ∈ W, p ≤ b i) :
    p * (W.card : ℝ) ≤ singlePriceProfitOn m s b := by
  classical
  rcases W.eq_empty_or_nonempty with rfl | hWne
  · simpa only [card_empty, Nat.cast_zero, mul_zero] using singlePriceProfitOn_nonneg hb
  · obtain ⟨j, hjW, hjmin⟩ := W.exists_min_image b hWne
    have hjs : j ∈ s := hWs hjW
    have hsub : W ⊆ s.filter fun i => b j ≤ b i := fun i hi =>
      mem_filter.2 ⟨hWs hi, hjmin i hi⟩
    have hcard : W.card ≤ (s.filter fun i => b j ≤ b i).card := card_le_card hsub
    have hjm : j ∈ s.filter fun k => m ≤ (s.filter fun i => b k ≤ b i).card :=
      mem_filter.2 ⟨hjs, hWm.trans hcard⟩
    calc p * (W.card : ℝ)
        ≤ b j * (W.card : ℝ) :=
          mul_le_mul_of_nonneg_right (hp j hjW) (Nat.cast_nonneg _)
      _ ≤ b j * ((s.filter fun i => b j ≤ b i).card : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.cast_le.2 hcard) (hb j hjs)
      _ ≤ singlePriceProfitOn m s b := by
          rw [singlePriceProfitOn, dite_eq_left ⟨j, hjm⟩]
          exact le_sup' (fun k => b k * ((s.filter fun i => b k ≤ b i).card : ℝ)) hjm

/-- Upper bound: if every candidate bid `b j` (`j ∈ s`, with at least `m` acceptors) gives revenue
at most `r`, and `0 ≤ r`, then `singlePriceProfitOn m s b ≤ r`. -/
theorem singlePriceProfitOn_le {m : ℕ} {s : Finset ι} {b : ι → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ j ∈ s, m ≤ (s.filter fun i => b j ≤ b i).card →
      b j * ((s.filter fun i => b j ≤ b i).card : ℝ) ≤ r) :
    singlePriceProfitOn m s b ≤ r := by
  classical
  unfold singlePriceProfitOn
  split_ifs with hne
  · exact sup'_le hne _ fun j hj => h j (mem_filter.1 hj).1 (mem_filter.1 hj).2
  · exact hr

/-- When `s` is nonempty and has at least `m` bidders, `singlePriceProfitOn m s b` is attained at
some bid `b j` with `j ∈ s` accepted by at least `m` bidders in `s`. -/
theorem exists_mem_eq_singlePriceProfitOn {m : ℕ} {s : Finset ι} {b : ι → ℝ}
    (hne : s.Nonempty) (hm : m ≤ s.card) :
    ∃ j ∈ s, m ≤ (s.filter fun i => b j ≤ b i).card ∧
      singlePriceProfitOn m s b = b j * ((s.filter fun i => b j ≤ b i).card : ℝ) := by
  classical
  obtain ⟨j₀, hj₀, hmin⟩ := s.exists_min_image b hne
  have hall : (s.filter fun i => b j₀ ≤ b i) = s :=
    filter_true_of_mem fun i hi => hmin i hi
  have hcne : (s.filter fun j => m ≤ (s.filter fun i => b j ≤ b i).card).Nonempty :=
    ⟨j₀, mem_filter.2 ⟨hj₀, by rw [hall]; exact hm⟩⟩
  obtain ⟨j, hjc, hjmax⟩ := exists_mem_eq_sup' hcne
    (fun j => b j * ((s.filter fun i => b j ≤ b i).card : ℝ))
  refine ⟨j, (mem_filter.1 hjc).1, (mem_filter.1 hjc).2, ?_⟩
  simpa only [singlePriceProfitOn, hcne, ↓reduceDIte] using hjmax

/-- The sorting-free benchmark `singlePriceProfitOn m Finset.univ b` agrees with the textbook
order-statistic formula `max_{m ≤ k ≤ |ι|} k · v_(k)` ([HartlineKarlin2007], Definition 13.34,
p. 345 for `m = 2`, and Definition 13.39, p. 347 for `m = 1`), where the `k`-th largest valuation
`v_(k)` is `Fintype.orderStatistic b (|ι| - k)`. -/
theorem singlePriceProfitOn_eq_sup_orderStatistic [Fintype ι] [Nonempty ι] {m : ℕ}
    (hm : 1 ≤ m) (hcard : m ≤ Fintype.card ι) {b : ι → ℝ} (hb : 0 ≤ b) :
    singlePriceProfitOn m Finset.univ b =
      (Icc m (Fintype.card ι)).sup' (nonempty_Icc.2 hcard) fun k =>
        (k : ℝ) * Fintype.orderStatistic b (Fintype.card ι - k) := by
  classical
  set n := Fintype.card ι
  have hne : (Icc m n).Nonempty := nonempty_Icc.2 hcard
  apply le_antisymm
  · refine singlePriceProfitOn_le ?_ fun j _ hj => ?_
    · refine le_sup'_of_le _ (left_mem_Icc.2 hcard) ?_
      have hos := Fintype.orderStatistic_isOrderStatistic b (k := n - m) (by omega)
      obtain ⟨i, hi⟩ := hos.1
      exact mul_nonneg (Nat.cast_nonneg _) (hi ▸ hb i)
    · set c := (univ.filter fun i => b j ≤ b i).card
      have hc_le_n : c ≤ n := by
        simpa only [card_univ] using card_filter_le (univ : Finset ι) (fun i => b j ≤ b i)
      have hlt_card : (univ.filter fun i => b i < b j).card = n - c := by
        have hcomp := card_filter_add_card_filter_not (s := univ) (p := fun i => b j ≤ b i)
        rw [filter_congr fun _ _ => not_le, card_univ] at hcomp
        dsimp only [n, c] at hc_le_n ⊢
        omega
      set y := Fintype.orderStatistic b (n - c)
      have hos := Fintype.orderStatistic_isOrderStatistic b (k := n - c) (by omega)
      have hbj_le_y : b j ≤ y := by
        by_contra hlt
        have hle1 : (univ.filter fun i => b i ≤ y).card ≤ (univ.filter fun i => b i < b j).card :=
          card_le_card fun i hi =>
            mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.trans_lt (lt_of_not_ge hlt)⟩
        have hle2 := hos.2.2
        dsimp only [y, c, n] at hle1 hlt_card hle2 hc_le_n
        omega
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_left hbj_le_y (Nat.cast_nonneg _)).trans
        (le_sup' (fun k : ℕ => (k : ℝ) * Fintype.orderStatistic b (n - k))
          (mem_Icc.2 ⟨hj, hc_le_n⟩))
  · refine sup'_le hne _ fun k hk => ?_
    have hk_bounds := mem_Icc.1 hk
    set y : ℝ := Fintype.orderStatistic b (n - k)
    have hos := Fintype.orderStatistic_isOrderStatistic b (k := n - k) (by omega)
    have hge_card : k ≤ (univ.filter fun i => y ≤ b i).card := by
      have hcomp := card_filter_add_card_filter_not (s := univ) (p := fun i => b i < y)
      rw [filter_congr fun _ _ => not_lt, card_univ] at hcomp
      have hle1 := hos.2.1
      dsimp only [y, n] at hcomp hle1 hk_bounds ⊢
      omega
    obtain ⟨j, hj⟩ := hos.1
    have hy0 : 0 ≤ y := (hb j).trans_eq hj
    refine (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hge_card) hy0).trans ?_
    rw [mul_comm]
    exact mul_card_le_singlePriceProfitOn (fun i _ => hb i) (filter_subset _ _)
      (hk_bounds.1.trans hge_card) fun i hi => (mem_filter.1 hi).2

/-- An auction (represented by its profit or expected profit function `profit`) is `β`-competitive
with respect to a benchmark `bench` if `0 ≤ β` and `bench b ≤ β * profit b` on every nonnegative
bid profile `b`. This is the multiplicative rendering of `β = sup_v G(v) / A(v)`
([HartlineKarlin2007], Definition 13.33, §13.4.1, p. 345), avoiding `0 / 0` when both `bench b`
and `profit b` are zero and disallowing negative ratios when `bench = 0`. -/
@[expose] def IsCompetitive (bench profit : (ι → ℝ) → ℝ) (β : ℝ) : Prop :=
  0 ≤ β ∧ ∀ b : ι → ℝ, 0 ≤ b → bench b ≤ β * profit b

end Benchmarks

/-! ### Profit extraction (`ProfitExtract_R`, Definition 13.40 & Exercise 13.10) -/

section ProfitExtract

variable {ι : Type*}

open Classical in
/-- Auxiliary set of feasible equal-share group sizes `k ∈ {1, ..., #s}` such that at least `k`
bidders in `s` bid at least `R / k`. -/
private noncomputable def feasibleSizes (s : Finset ι) (R : ℝ) (b : ι → ℝ) : Finset ℕ :=
  (Icc 1 s.card).filter fun k : ℕ => k ≤ (s.filter fun i => R / (k : ℝ) ≤ b i).card

open Classical in
/-- The largest group size `k ∈ {1, ..., #s}` of bidders in `s` that can equally share target
profit `R ≥ 0` (i.e. at least `k` bidders in `s` bid at least `R / k`), or `0` if `R < 0` or no
such `k` exists ([HartlineKarlin2007], Definition 13.40, §13.4.4, p. 347). -/
@[expose] noncomputable def profitExtractSize (s : Finset ι) (R : ℝ) (b : ι → ℝ) : ℕ :=
  if 0 ≤ R then
    if h : ((Icc 1 s.card).filter fun k : ℕ =>
        k ≤ (s.filter fun i => R / (k : ℝ) ≤ b i).card).Nonempty then
      ((Icc 1 s.card).filter fun k : ℕ =>
        k ≤ (s.filter fun i => R / (k : ℝ) ≤ b i).card).max' h
    else 0
  else 0

open Classical in
/-- The digital goods auction profit extractor `ProfitExtract_R` restricted to the bidder subset
`s` ([HartlineKarlin2007], Definition 13.40, §13.4.4, p. 347). Finds the largest `k` such that at
least `k` bidders in `s` bid at least `R / k`; awards one unit to each bidder in `s` bidding at
least `R / k` and charges each `R / k`. Bidders outside `s` and losers receive `0` and pay `0`.

When `R = 0` and all bids in `s` are nonnegative, if `s` is nonempty then `k = s.card` and every
bidder in `s` wins at price `0` (profit `0 = R`). When `R < 0`, no bidder wins (`payment = 0`). -/
@[expose] noncomputable def profitExtractOn (s : Finset ι) (R : ℝ) : Mechanism ι where
  allocation b i :=
    if i ∈ s ∧ 0 < profitExtractSize s R b ∧ R / (profitExtractSize s R b : ℝ) ≤ b i then 1 else 0
  payment b i :=
    if i ∈ s ∧ 0 < profitExtractSize s R b ∧ R / (profitExtractSize s R b : ℝ) ≤ b i then
      R / (profitExtractSize s R b : ℝ)
    else 0

/-- `ProfitExtract_R` on the full bidder pool `Finset.univ` ([HartlineKarlin2007], Definition 13.40,
§13.4.4, p. 347). -/
noncomputable abbrev profitExtract [Fintype ι] (R : ℝ) : Mechanism ι :=
  profitExtractOn Finset.univ R

private theorem profitExtractSize_eq_zero_of_neg (s : Finset ι) {R : ℝ} (hR : R < 0)
    (b : ι → ℝ) : profitExtractSize s R b = 0 := by
  unfold profitExtractSize
  simp only [not_le.2 hR, ↓reduceIte]

private theorem mem_feasibleSizes_iff {s : Finset ι} {R : ℝ} {b : ι → ℝ} {k : ℕ} :
    k ∈ feasibleSizes s R b ↔
      1 ≤ k ∧ k ≤ s.card ∧ k ≤ (s.filter fun i => R / (k : ℝ) ≤ b i).card := by
  classical
  simp only [feasibleSizes, mem_filter, mem_Icc, and_assoc]

private theorem profitExtractSize_eq_feasibleSizes {s : Finset ι} {R : ℝ} (hR : 0 ≤ R)
    (b : ι → ℝ) :
    profitExtractSize s R b =
      if h : (feasibleSizes s R b).Nonempty then (feasibleSizes s R b).max' h else 0 := by
  unfold profitExtractSize feasibleSizes
  simp only [hR, ↓reduceIte]

private theorem profitExtractSize_mem_of_pos {s : Finset ι} {R : ℝ} {b : ι → ℝ}
    (hk : 0 < profitExtractSize s R b) :
    0 ≤ R ∧ profitExtractSize s R b ∈ feasibleSizes s R b := by
  by_cases hR : 0 ≤ R
  · by_cases hne : (feasibleSizes s R b).Nonempty
    · simp only [profitExtractSize_eq_feasibleSizes hR, hne, ↓reduceDIte]
      exact ⟨hR, max'_mem _ hne⟩
    · simp [profitExtractSize_eq_feasibleSizes hR, hne] at hk
  · simp [profitExtractSize_eq_zero_of_neg s (lt_of_not_ge hR)] at hk

private theorem le_profitExtractSize {s : Finset ι} {R : ℝ} (hR : 0 ≤ R) {b : ι → ℝ} {k : ℕ}
    (hk : k ∈ feasibleSizes s R b) : k ≤ profitExtractSize s R b := by
  rw [profitExtractSize_eq_feasibleSizes hR]
  have hne : (feasibleSizes s R b).Nonempty := ⟨k, hk⟩
  simp only [hne, ↓reduceDIte]
  exact le_max' (feasibleSizes s R b) k hk

private theorem feasibleSizes_nonempty_iff_le {s : Finset ι} {R : ℝ} (hR : 0 ≤ R) {b : ι → ℝ}
    (hb : ∀ i ∈ s, 0 ≤ b i) (hs : s.Nonempty) :
    (feasibleSizes s R b).Nonempty ↔ R ≤ optimalProfitOn s b := by
  classical
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨hk1, _, hcard⟩ := mem_feasibleSizes_iff.1 hk
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk1
    have hRle : R ≤ (R / (k : ℝ)) * ((s.filter fun i => R / (k : ℝ) ≤ b i).card : ℝ) := by
      calc R = (R / (k : ℝ)) * (k : ℝ) := (div_mul_cancel₀ R hkpos.ne').symm
        _ ≤ (R / (k : ℝ)) * ((s.filter fun i => R / (k : ℝ) ≤ b i).card : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.2 hcard) (div_nonneg hR hkpos.le)
    exact hRle.trans (mul_card_le_singlePriceProfitOn hb (filter_subset _ _)
      (hk1.trans hcard) fun i hi => (mem_filter.1 hi).2)
  · intro hRle
    obtain ⟨j, _, hj1, hjeq⟩ :=
      exists_mem_eq_singlePriceProfitOn (m := 1) hs (one_le_card.2 hs) (b := b)
    set c := (s.filter fun i => b j ≤ b i).card
    have hdiv_le : R / (c : ℝ) ≤ b j := (div_le_iff₀ (Nat.cast_pos.2 hj1)).2 (hjeq ▸ hRle)
    have hsub : (s.filter fun i => b j ≤ b i) ⊆ (s.filter fun i => R / (c : ℝ) ≤ b i) :=
      fun i hi => mem_filter.2 ⟨(mem_filter.1 hi).1, hdiv_le.trans (mem_filter.1 hi).2⟩
    exact ⟨c, mem_feasibleSizes_iff.2 ⟨hj1, card_filter_le _ _, card_le_card hsub⟩⟩

/-- When `profitExtractSize s R b > 0`, **exactly** `profitExtractSize s R b` bidders in `s` bid
at least `R / profitExtractSize s R b` (no ties leave extra winners). -/
theorem card_winners_profitExtractOn {s : Finset ι} {R : ℝ} {b : ι → ℝ}
    (hk : 0 < profitExtractSize s R b) :
    (s.filter fun i => R / (profitExtractSize s R b : ℝ) ≤ b i).card =
      profitExtractSize s R b := by
  classical
  set k := profitExtractSize s R b
  obtain ⟨hR, hmem⟩ := profitExtractSize_mem_of_pos hk
  obtain ⟨hk1, _, hge⟩ := mem_feasibleSizes_iff.1 hmem
  apply le_antisymm _ (by convert hge)
  by_contra! hlt
  have hprice : R / ((k + 1 : ℕ) : ℝ) ≤ R / (k : ℝ) :=
    div_le_div_of_nonneg_left hR (Nat.cast_pos.2 hk1) (Nat.cast_le.2 (Nat.le_succ k))
  have hsub : (s.filter fun i => R / (k : ℝ) ≤ b i) ⊆
      (s.filter fun i => R / ((k + 1 : ℕ) : ℝ) ≤ b i) :=
    fun i hi => mem_filter.2 ⟨(mem_filter.1 hi).1, hprice.trans (mem_filter.1 hi).2⟩
  have hmem' : k + 1 ∈ feasibleSizes s R b := mem_feasibleSizes_iff.2
    ⟨Nat.le_add_left 1 k, hlt.trans_le (card_filter_le _ _), hlt.trans_le (card_le_card hsub)⟩
  exact Nat.not_succ_le_self k (le_profitExtractSize hR hmem')

/-- Candidate group sizes assuming bidder `i ∈ s` accepts any price: `k ∈ {1, ..., #s}` such that
at least `k - 1` other bidders in `s.erase i` bid at least `R / k`. -/
private noncomputable def otherThresholdCands [DecidableEq ι] (s : Finset ι) (R : ℝ)
    (b : ι → ℝ) (i : ι) : Finset ℕ :=
  open Classical in
  (Icc 1 s.card).filter fun k : ℕ =>
    k ≤ ((s.erase i).filter fun j => R / (k : ℝ) ≤ b j).card + 1

private theorem one_mem_otherThresholdCands [DecidableEq ι] {s : Finset ι} {R : ℝ} {b : ι → ℝ}
    {i : ι} (hi : i ∈ s) : 1 ∈ otherThresholdCands s R b i := by
  classical
  refine mem_filter.2 ⟨mem_Icc.2 ⟨le_rfl, one_le_card.2 ⟨i, hi⟩⟩, ?_⟩
  exact Nat.le_add_left 1 _

/-- Largest `k ∈ {1, ..., #s}` such that at least `k - 1` bidders in `s.erase i` bid at least
`R / k`. Depends only on `b₋ᵢ`. -/
private noncomputable def otherThresholdSize [DecidableEq ι] (s : Finset ι) (R : ℝ)
    (b : ι → ℝ) (i : ι) (hi : i ∈ s) : ℕ :=
  (otherThresholdCands s R b i).max' ⟨1, one_mem_otherThresholdCands hi⟩

private theorem otherThresholdSize_spec [DecidableEq ι] {s : Finset ι} {R : ℝ} {b : ι → ℝ}
    {i : ι} (hi : i ∈ s) :
    1 ≤ otherThresholdSize s R b i hi ∧
      otherThresholdSize s R b i hi ≤ s.card ∧
      otherThresholdSize s R b i hi ≤
        ((s.erase i).filter fun j =>
          R / (otherThresholdSize s R b i hi : ℝ) ≤ b j).card + 1 := by
  classical
  have hmem := max'_mem (otherThresholdCands s R b i) ⟨1, one_mem_otherThresholdCands hi⟩
  simp only [otherThresholdCands, mem_filter, mem_Icc] at hmem
  exact ⟨hmem.1.1, hmem.1.2, hmem.2⟩

private theorem card_filter_update_erase [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) {i : ι}
    (hi : i ∈ s) (p z : ℝ) :
    (s.filter fun j => p ≤ Function.update b i z j).card =
      ((s.erase i).filter fun j => p ≤ b j).card + (if p ≤ z then 1 else 0) := by
  classical
  have hcong : ((s.erase i).filter fun j => p ≤ Function.update b i z j) =
      (s.erase i).filter fun j => p ≤ b j :=
    filter_congr fun j hj => by rw [Function.update_of_ne (mem_erase.1 hj).1]
  have hni : i ∉ (s.erase i).filter fun j => p ≤ Function.update b i z j := fun hm =>
    (mem_erase.1 (mem_filter.1 hm).1).1 rfl
  calc (s.filter fun j => p ≤ Function.update b i z j).card
      = ((insert i (s.erase i)).filter fun j => p ≤ Function.update b i z j).card := by
          rw [insert_erase hi]
    _ = _ := by
          rw [filter_insert, Function.update_self]
          split_ifs with hpz
          · rw [card_insert_of_notMem hni, hcong]
          · rw [hcong, add_zero]

private theorem le_otherThresholdSize_of_mem [DecidableEq ι] {s : Finset ι} {R : ℝ} {b : ι → ℝ}
    {i : ι} (hi : i ∈ s) {z : ℝ} {k : ℕ}
    (hk : k ∈ feasibleSizes s R (Function.update b i z)) :
    k ≤ otherThresholdSize s R b i hi := by
  classical
  obtain ⟨hk1, hks, hcard⟩ := mem_feasibleSizes_iff.1 hk
  rw [card_filter_update_erase s b hi] at hcard
  have hbound : k ≤ ((s.erase i).filter fun j => R / (k : ℝ) ≤ b j).card + 1 := by
    split_ifs at hcard <;> omega
  exact le_max' (otherThresholdCands s R b i) k
    (mem_filter.2 ⟨mem_Icc.2 ⟨hk1, hks⟩, hbound⟩)

private theorem profitExtractSize_update_eq_of_ge [DecidableEq ι] {s : Finset ι} {R : ℝ}
    (hR : 0 ≤ R) {b : ι → ℝ} {i : ι} (hi : i ∈ s) {z : ℝ}
    (hz : R / (otherThresholdSize s R b i hi : ℝ) ≤ z) :
    profitExtractSize s R (Function.update b i z) = otherThresholdSize s R b i hi := by
  classical
  set k₀ := otherThresholdSize s R b i hi
  obtain ⟨hk1, hks, hother⟩ := otherThresholdSize_spec (R := R) (b := b) hi
  have hmem : k₀ ∈ feasibleSizes s R (Function.update b i z) := by
    rw [mem_feasibleSizes_iff, card_filter_update_erase s b hi, ite_eq_left hz]
    exact ⟨hk1, hks, hother⟩
  have hle := le_profitExtractSize hR hmem
  exact le_antisymm
    (le_otherThresholdSize_of_mem hi (profitExtractSize_mem_of_pos (lt_of_lt_of_le hk1 hle)).2)
    hle

private theorem profitExtractOn_update_win_iff [DecidableEq ι] {s : Finset ι} {R : ℝ}
    (hR : 0 ≤ R) (b : ι → ℝ) {i : ι} (hi : i ∈ s) (z : ℝ) :
    (profitExtractOn s R).allocation (Function.update b i z) i = 1 ↔
      R / (otherThresholdSize s R b i hi : ℝ) ≤ z := by
  set k₀ := otherThresholdSize s R b i hi
  have hk₀_pos : 1 ≤ k₀ := (otherThresholdSize_spec (R := R) (b := b) hi).1
  constructor
  · intro hwin
    dsimp only [profitExtractOn] at hwin
    rw [Function.update_self] at hwin
    split_ifs at hwin with h
    · obtain ⟨_, hkpos, hdiv⟩ := h
      have hkle : profitExtractSize s R (Function.update b i z) ≤ k₀ :=
        le_otherThresholdSize_of_mem hi (profitExtractSize_mem_of_pos hkpos).2
      have hprice : R / (k₀ : ℝ) ≤ R / (profitExtractSize s R (Function.update b i z) : ℝ) :=
        div_le_div_of_nonneg_left hR (Nat.cast_pos.2 hkpos) (Nat.cast_le.2 hkle)
      exact hprice.trans hdiv
    · exact absurd hwin zero_ne_one
  · intro hz
    have hkeq := profitExtractSize_update_eq_of_ge hR hi hz
    dsimp only [profitExtractOn]
    rw [Function.update_self, hkeq]
    exact ite_eq_left ⟨hi, hk₀_pos, hz⟩

private theorem profitExtractOn_update_lose [DecidableEq ι] {s : Finset ι} {R : ℝ}
    (hR : 0 ≤ R) (b : ι → ℝ) {i : ι} (hi : i ∈ s) {z : ℝ}
    (hz : ¬ R / (otherThresholdSize s R b i hi : ℝ) ≤ z) :
    ¬ (i ∈ s ∧ 0 < profitExtractSize s R (Function.update b i z) ∧
      R / (profitExtractSize s R (Function.update b i z) : ℝ) ≤ Function.update b i z i) :=
  fun h => hz ((profitExtractOn_update_win_iff hR b hi z).1 (ite_eq_left h))

/-- `profitExtractOn s R` has a `0`-`1` allocation rule. -/
theorem profitExtractOn_isBinary (s : Finset ι) (R : ℝ) :
    IsBinary (profitExtractOn s R).allocation := by
  intro b _ i
  dsimp only [profitExtractOn]
  split_ifs <;> simp

/-- `profitExtractOn s R` has a monotone allocation rule. -/
theorem profitExtractOn_isMonotone [DecidableEq ι] (s : Finset ι) (R : ℝ) :
    IsMonotone (profitExtractOn s R).allocation := by
  intro i b _ z _ z' _ hzz'
  change (profitExtractOn s R).allocation (Function.update b i z) i ≤
    (profitExtractOn s R).allocation (Function.update b i z') i
  by_cases hR : 0 ≤ R
  · by_cases hi : i ∈ s
    · by_cases hz : R / (otherThresholdSize s R b i hi : ℝ) ≤ z
      · rw [(profitExtractOn_update_win_iff hR b hi z).2 hz,
          (profitExtractOn_update_win_iff hR b hi z').2 (hz.trans hzz')]
      · dsimp only [profitExtractOn]
        rw [ite_eq_right (profitExtractOn_update_lose hR b hi hz)]
        split_ifs <;> norm_num
    · simp only [profitExtractOn, hi, false_and, ↓reduceIte, le_refl]
  · simp only [profitExtractOn, profitExtractSize_eq_zero_of_neg s (lt_of_not_ge hR),
      lt_self_iff_false, false_and, and_false, ↓reduceIte, le_refl]

/-- On every bid profile, the payment of `profitExtractOn s R` equals its critical-bid payment
`criticalBid x b i * x b i` (hence coincides with `criticalBidMechanism`). In particular, losers
(`allocation b i = 0`) pay nothing (no positive transfers, [HartlineKarlin2007], §13.1.2,
p. 334). -/
theorem profitExtractOn_payment_eq_criticalBid [DecidableEq ι] (s : Finset ι) (R : ℝ)
    (b : ι → ℝ) (i : ι) :
    (profitExtractOn s R).payment b i =
      criticalBid (profitExtractOn s R).allocation b i *
        (profitExtractOn s R).allocation b i := by
  by_cases hR : 0 ≤ R
  · by_cases hi : i ∈ s
    · set k₀ := otherThresholdSize s R b i hi
      set t := R / (k₀ : ℝ)
      have hk₀_pos : 1 ≤ k₀ := (otherThresholdSize_spec (R := R) (b := b) hi).1
      have ht : 0 ≤ t := div_nonneg hR (Nat.cast_nonneg _)
      have hcrit : criticalBid (profitExtractOn s R).allocation b i = t :=
        criticalBid_eq_of_threshold ht
          (fun z htz => (profitExtractOn_update_win_iff hR b hi z).2 htz.le)
          (fun z _ hwin => (profitExtractOn_update_win_iff hR b hi z).1 hwin)
      rw [hcrit]
      have hself : Function.update b i (b i) = b := Function.update_eq_self i b
      by_cases hbi : t ≤ b i
      · have hkeq : profitExtractSize s R b = k₀ := by
          simpa only [hself] using profitExtractSize_update_eq_of_ge hR hi hbi
        have hcond : i ∈ s ∧ 0 < profitExtractSize s R b ∧
            R / (profitExtractSize s R b : ℝ) ≤ b i := hkeq ▸ ⟨hi, hk₀_pos, hbi⟩
        dsimp only [profitExtractOn]
        rw [ite_eq_left hcond, ite_eq_left hcond, hkeq, mul_one]
      · have hcond := hself ▸ profitExtractOn_update_lose hR b hi hbi
        dsimp only [profitExtractOn]
        rw [ite_eq_right hcond, ite_eq_right hcond, mul_zero]
    · simp only [profitExtractOn, hi, false_and, ↓reduceIte, mul_zero]
  · simp only [profitExtractOn, profitExtractSize_eq_zero_of_neg s (lt_of_not_ge hR),
      lt_self_iff_false, false_and, and_false, ↓reduceIte, mul_zero]

/-- `ProfitExtract_R` is dominant-strategy incentive compatible (truthful) on nonnegative bids
([HartlineKarlin2007], §13.4.4, p. 347 and Exercise 13.10, p. 361). -/
theorem profitExtractOn_isDSIC [DecidableEq ι] (s : Finset ι) (R : ℝ) :
    (profitExtractOn s R).IsDSIC :=
  (criticalBidMechanism_isDSIC (profitExtractOn_isMonotone s R)
    (profitExtractOn_isBinary s R)).congr fun b _ =>
    ⟨rfl, funext fun i => (profitExtractOn_payment_eq_criticalBid s R b i).symm⟩

/-- `ProfitExtract_R` is individually rational on nonnegative bids. -/
theorem profitExtractOn_isIR (s : Finset ι) (R : ℝ) :
    (profitExtractOn s R).IsIR := by
  classical
  exact (criticalBidMechanism_isIR (profitExtractOn_isBinary s R)).congr fun b _ =>
    ⟨rfl, funext fun i => (profitExtractOn_payment_eq_criticalBid s R b i).symm⟩

/-- In `ProfitExtract_R`, a bidder bidding `0` pays `0`. -/
theorem profitExtractOn_isNormalized [DecidableEq ι] (s : Finset ι) (R : ℝ) :
    (profitExtractOn s R).IsNormalized := by
  intro i b hb
  rw [profitExtractOn_payment_eq_criticalBid]
  exact criticalBidMechanism_isNormalized (profitExtractOn_isBinary s R) i b hb

private theorem sum_payment_profitExtractOn_eq_univ [Fintype ι] (s : Finset ι) (R : ℝ)
    (b : ι → ℝ) :
    ∑ i ∈ s, (profitExtractOn s R).payment b i = ∑ i, (profitExtractOn s R).payment b i :=
  sum_subset (subset_univ s) fun i _ his => by simp [profitExtractOn, his]

/-- Total profit of `ProfitExtract_R` on bidder subset `s`: for `R ≥ 0` and nonnegative bids on `s`,
it extracts `R` whenever `R ≤ ℱ(b_s)` and `0` when `ℱ(b_s) < R` ([HartlineKarlin2007], §13.4.4,
p. 347 and Exercise 13.10, p. 361). -/
theorem sum_payment_profitExtractOn [Fintype ι] (s : Finset ι) {R : ℝ} (hR : 0 ≤ R)
    {b : ι → ℝ} (hb : ∀ i ∈ s, 0 ≤ b i) :
    ∑ i, (profitExtractOn s R).payment b i = if R ≤ optimalProfitOn s b then R else 0 := by
  classical
  rw [← sum_payment_profitExtractOn_eq_univ]
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp only [sum_empty, singlePriceProfitOn_empty]
    split_ifs <;> linarith
  · by_cases hle : R ≤ optimalProfitOn s b
    · simp only [hle, ↓reduceIte]
      obtain ⟨k₀, hk₀⟩ := (feasibleSizes_nonempty_iff_le hR hb hsne).2 hle
      have hkpos : 0 < profitExtractSize s R b :=
        lt_of_lt_of_le (mem_feasibleSizes_iff.1 hk₀).1 (le_profitExtractSize hR hk₀)
      set k := profitExtractSize s R b
      have hcard := card_winners_profitExtractOn (s := s) (R := R) (b := b) hkpos
      calc ∑ i ∈ s, (profitExtractOn s R).payment b i
          = ∑ i ∈ s, if R / (k : ℝ) ≤ b i then R / (k : ℝ) else 0 :=
              sum_congr rfl fun i hi => by
                unfold profitExtractOn; dsimp only
                by_cases hdiv : R / (k : ℝ) ≤ b i
                · rw [ite_eq_left ⟨hi, hkpos, hdiv⟩, ite_eq_left hdiv]
                · rw [ite_eq_right fun h => hdiv h.2.2, ite_eq_right hdiv]
        _ = ∑ _i ∈ s.filter fun i => R / (k : ℝ) ≤ b i, R / (k : ℝ) :=
              (sum_filter (fun i => R / (k : ℝ) ≤ b i) (fun _ => R / (k : ℝ))).symm
        _ = ((s.filter fun i => R / (k : ℝ) ≤ b i).card : ℝ) * (R / (k : ℝ)) := by
              rw [sum_const, nsmul_eq_mul]
        _ = (k : ℝ) * (R / (k : ℝ)) := by rw [hcard]
        _ = R := mul_div_cancel₀ R (Nat.cast_pos.2 hkpos).ne'
    · have hk0 : profitExtractSize s R b = 0 := by
        simp [profitExtractSize_eq_feasibleSizes hR,
          mt (feasibleSizes_nonempty_iff_le hR hb hsne).1 hle]
      simp [hle, profitExtractOn, hk0]

/-- **Exercise 13.10** ([HartlineKarlin2007], p. 361; §13.4.4, p. 347): on nonnegative bids with
`0 ≤ R ≤ ℱ(b)`, `profitExtract R` obtains total profit `R`. Paired with `profitExtractOn_isDSIC`
and `profitExtractOn_isIR` (with `s = Finset.univ`). -/
theorem sum_payment_profitExtract_of_le [Fintype ι] {R : ℝ} (hR : 0 ≤ R) {b : ι → ℝ}
    (hb : 0 ≤ b) (hle : R ≤ optimalProfit b) :
    ∑ i, (profitExtract R).payment b i = R := by
  simpa only [hle, ↓reduceIte] using sum_payment_profitExtractOn Finset.univ hR fun i _ => hb i

end ProfitExtract

/-! ### Random Sampling Profit Extraction (`RSPE`, Definition 13.41 & Theorem 13.42) -/

section RSPE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The deterministic auction executed by **RSPE** (Random Sampling Profit Extraction;
[HartlineKarlin2007], Definition 13.41, §13.4.5, p. 348) on a fixed bipartition `(s, sᶜ)` of the
bidders. Computes `R' = ℱ(b_s)` and `R'' = ℱ(b_{sᶜ})`, then runs `ProfitExtract_{R''}` on `s` and
`ProfitExtract_{R'}` on `sᶜ`.

We follow Definition 13.41(ii) (`ℱ`, `optimalProfitOn`), repairing the typographical `ℱ⁽²⁾` in
the informal intuition paragraph of [HartlineKarlin2007], p. 348. -/
@[expose] noncomputable def rspe (s : Finset ι) : Mechanism ι where
  allocation b i :=
    if i ∈ s then
      (profitExtractOn s (optimalProfitOn sᶜ b)).allocation b i
    else
      (profitExtractOn sᶜ (optimalProfitOn s b)).allocation b i
  payment b i :=
    if i ∈ s then
      (profitExtractOn s (optimalProfitOn sᶜ b)).payment b i
    else
      (profitExtractOn sᶜ (optimalProfitOn s b)).payment b i

/-- The expected profit of **RSPE** on bid profile `b`, averaged uniformly over all `2^|ι|`
partitions `s : Finset ι` (equivalently, placing each bidder independently in `s` or `sᶜ` by a
fair coin flip). -/
@[expose] noncomputable def rspeExpectedProfit (b : ι → ℝ) : ℝ :=
  𝔼 s : Finset ι, ∑ i, (rspe s).payment b i

/-- Explicit sum-over-`2^n` form of `rspeExpectedProfit`. -/
theorem rspeExpectedProfit_eq_div (b : ι → ℝ) :
    rspeExpectedProfit b = (∑ s : Finset ι, ∑ i, (rspe s).payment b i) / 2 ^ Fintype.card ι := by
  unfold rspeExpectedProfit
  rw [expect_univ, Fintype.card_finset, NNRat.smul_def, mul_comm, NNRat.cast_inv,
    NNRat.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, ← div_eq_mul_inv]

/-- Each deterministic realization `rspe s` has a `0`-`1` allocation rule. -/
theorem rspe_isBinary (s : Finset ι) : IsBinary (rspe s).allocation := by
  intro b hb i
  unfold rspe; dsimp only
  split_ifs
  · exact profitExtractOn_isBinary s _ b hb i
  · exact profitExtractOn_isBinary sᶜ _ b hb i

omit [Fintype ι] in
private theorem optimalProfitOn_update_of_notMem {s : Finset ι} {i : ι} (hi : i ∉ s)
    (b : ι → ℝ) (v : ℝ) : optimalProfitOn s (Function.update b i v) = optimalProfitOn s b :=
  singlePriceProfitOn_congr fun _ hj => Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _

/-- **Universal truthfulness of RSPE**: for every partition `s : Finset ι`, the deterministic
auction `rspe s` is dominant-strategy incentive compatible ([HartlineKarlin2007], Definition 13.41,
§13.4.5, p. 348). -/
theorem rspe_isDSIC (s : Finset ι) : (rspe s).IsDSIC := by
  intro i b v hb hv
  simp only [Mechanism.utility, rspe]
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte, optimalProfitOn_update_of_notMem (notMem_compl.2 hi)]
    exact profitExtractOn_isDSIC s (optimalProfitOn sᶜ b) i b v hb hv
  · simp only [hi, ↓reduceIte, optimalProfitOn_update_of_notMem hi]
    exact profitExtractOn_isDSIC sᶜ (optimalProfitOn s b) i b v hb hv

/-- For every partition `s : Finset ι`, `rspe s` is individually rational on nonnegative bids. -/
theorem rspe_isIR (s : Finset ι) : (rspe s).IsIR := by
  intro i b hb
  simp only [Mechanism.utility, rspe]
  split_ifs
  · exact profitExtractOn_isIR s (optimalProfitOn sᶜ b) i b hb
  · exact profitExtractOn_isIR sᶜ (optimalProfitOn s b) i b hb

/-- For every partition `s : Finset ι`, a bidder bidding `0` pays `0` in `rspe s`. -/
theorem rspe_isNormalized (s : Finset ι) : (rspe s).IsNormalized := by
  intro i b hb
  unfold rspe; dsimp only
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte, optimalProfitOn_update_of_notMem (notMem_compl.2 hi)]
    exact profitExtractOn_isNormalized s (optimalProfitOn sᶜ b) i b hb
  · simp only [hi, ↓reduceIte, optimalProfitOn_update_of_notMem hi]
    exact profitExtractOn_isNormalized sᶜ (optimalProfitOn s b) i b hb

/-- **Truthfulness in expectation** of `RSPE` ([HartlineKarlin2007], Definition 13.5, §13.1.2,
p. 334): follows immediately from universal truthfulness (`rspe_isDSIC`). -/
theorem rspe_truthfulInExpectation (i : ι) (b : ι → ℝ) (v : ℝ) (hb : 0 ≤ b) (hv : 0 ≤ v) :
    𝔼 s : Finset ι, (rspe s).utility i v b ≤
      𝔼 s : Finset ι, (rspe s).utility i v (Function.update b i v) :=
  expect_le_expect fun s _ => rspe_isDSIC s i b v hb hv

/-- Exact realized profit of `rspe s` on nonnegative bids `b`: it extracts `R''` from `s` if
`R'' ≤ R'` and `R'` from `sᶜ` if `R' ≤ R''`. In particular, when `R' ≠ R''` the profit equals
`min R' R''`, and when `R' = R''` both sides succeed and the profit is `2 * R'`. This repairs the
imprecise remark in [HartlineKarlin2007], p. 348 ("the profit of RSPE is `min(R', R'')`"). -/
theorem sum_payment_rspe_eq (s : Finset ι) {b : ι → ℝ} (hb : 0 ≤ b) :
    ∑ i, (rspe s).payment b i =
      (if optimalProfitOn sᶜ b ≤ optimalProfitOn s b then optimalProfitOn sᶜ b else 0) +
        (if optimalProfitOn s b ≤ optimalProfitOn sᶜ b then optimalProfitOn s b else 0) := by
  have hsplit : ∑ i, (rspe s).payment b i =
      (∑ i ∈ s, (profitExtractOn s (optimalProfitOn sᶜ b)).payment b i) +
        (∑ i ∈ sᶜ, (profitExtractOn sᶜ (optimalProfitOn s b)).payment b i) := by
    rw [← sum_add_sum_compl s]
    exact congrArg₂ (· + ·) (sum_congr rfl fun i hi => ite_eq_left hi)
      (sum_congr rfl fun i hi => ite_eq_right (mem_compl.1 hi))
  rw [hsplit, sum_payment_profitExtractOn_eq_univ, sum_payment_profitExtractOn_eq_univ,
    sum_payment_profitExtractOn s (singlePriceProfitOn_nonneg fun i _ => hb i) fun i _ => hb i,
    sum_payment_profitExtractOn sᶜ (singlePriceProfitOn_nonneg fun i _ => hb i) fun i _ => hb i]

/-- For every partition `s` and nonnegative bid profile `b`, the profit of `rspe s` is at least
`min (ℱ(b_s)) (ℱ(b_{sᶜ}))`, matching the lower bound used in the proof of Theorem 13.42
([HartlineKarlin2007], p. 348). -/
theorem min_le_sum_payment_rspe (s : Finset ι) {b : ι → ℝ} (hb : 0 ≤ b) :
    min (optimalProfitOn s b) (optimalProfitOn sᶜ b) ≤ ∑ i, (rspe s).payment b i := by
  rw [sum_payment_rspe_eq s hb]
  have h1 : 0 ≤ optimalProfitOn s b := singlePriceProfitOn_nonneg fun i _ => hb i
  rcases lt_trichotomy (optimalProfitOn s b) (optimalProfitOn sᶜ b) with hlt | heq | hgt
  · simp only [min_eq_left hlt.le, not_le_of_gt hlt, hlt.le, ↓reduceIte, zero_add, le_refl]
  · simp only [heq, min_self, le_refl, ↓reduceIte]; linarith [heq ▸ h1]
  · simp only [min_eq_right hgt.le, hgt.le, not_le_of_gt hgt, ↓reduceIte, add_zero, le_refl]

/-! #### Combinatorial counting lemma for fair coin flips -/

/-- Exact count of subsets `s : Finset ι` separating an ordered pair `(i, j)` with `i ≠ j`:
`#{s | i ∈ s ∧ j ∉ s} = 2 ^ (|ι| - 2)`. -/
private theorem card_filter_mem_notMem {i j : ι} (hij : i ≠ j) :
    ((univ : Finset (Finset ι)).filter fun s => i ∈ s ∧ j ∉ s).card =
      2 ^ (Fintype.card ι - 2) := by
  set U := (univ.erase i).erase j
  have hj_mem : j ∈ univ.erase i := mem_erase.2 ⟨hij.symm, mem_univ j⟩
  have hcardU : U.card = Fintype.card ι - 2 := by
    rw [card_erase_of_mem hj_mem, card_erase_of_mem (mem_univ i), card_univ]
    omega
  have heq : (univ.filter fun s : Finset ι => i ∈ s ∧ j ∉ s) = U.powerset.image (insert i) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_powerset]
    constructor
    · rintro ⟨his, hjs⟩
      exact ⟨s.erase i, fun x hx => mem_erase.2 ⟨fun h => hjs (h ▸ (mem_erase.1 hx).2),
        mem_erase.2 ⟨(mem_erase.1 hx).1, mem_univ x⟩⟩, insert_erase his⟩
    · rintro ⟨t, htU, rfl⟩
      refine ⟨mem_insert_self i t, fun hj => ?_⟩
      rcases mem_insert.1 hj with hji | hjt
      · exact hij hji.symm
      · exact (mem_erase.1 (htU hjt)).1 rfl
  have hinj : Set.InjOn (insert i) (U.powerset : Set (Finset ι)) := fun t₁ ht₁ t₂ ht₂ h => by
    have hnot {t : Finset ι} (ht : t ∈ U.powerset) : i ∉ t := fun hi =>
      (mem_erase.1 (mem_erase.1 (mem_powerset.1 ht hi)).2).1 rfl
    simpa only [erase_insert (hnot ht₁), erase_insert (hnot ht₂)] using congrArg (·.erase i) h
  rw [heq, card_image_of_injOn hinj, card_powerset, hcardU]

/-- For `a + c = k`, `a * c ≤ (k - 1) * min a c`. -/
private theorem mul_le_pred_mul_min {a c k : ℕ} (h : a + c = k) :
    a * c ≤ (k - 1) * min a c := by
  rcases le_total a c with hac | hca
  · rw [min_eq_left hac]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [zero_mul, mul_zero, le_refl]
    · calc a * c ≤ a * (k - 1) := Nat.mul_le_mul_left a (by omega)
        _ = (k - 1) * a := mul_comm _ _
  · rw [min_eq_right hca]
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp only [mul_zero, le_refl]
    · exact Nat.mul_le_mul_right c (by omega)

/-- Double-counting formula: for any `W : Finset ι` with `2 ≤ W.card`,
`4 * ∑ s : Finset ι, (W ∩ s).card * (W \ s).card = W.card * (W.card - 1) * 2 ^ |ι|`. -/
private theorem four_mul_sum_inter_mul_sdiff {W : Finset ι} (hW : 2 ≤ W.card) :
    4 * ∑ s : Finset ι, (W ∩ s).card * (W \ s).card =
      W.card * (W.card - 1) * 2 ^ Fintype.card ι := by
  have hsum_term : ∀ s : Finset ι, (W ∩ s).card * (W \ s).card =
      ∑ i ∈ W, ∑ j ∈ W, if i ∈ s ∧ j ∉ s then 1 else 0 := by
    intro s
    rw [← filter_mem_eq_inter, sdiff_eq_filter, card_filter, card_filter, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp only [hi, hj, not_true_eq_false,
      not_false_eq_true, and_true, and_false, ↓reduceIte, mul_one, mul_zero]
  have hswap : ∑ s : Finset ι, (W ∩ s).card * (W \ s).card =
      ∑ i ∈ W, ∑ j ∈ W, ((univ : Finset (Finset ι)).filter fun s => i ∈ s ∧ j ∉ s).card := by
    simp_rw [hsum_term, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_comm
  have hcardι : 2 ≤ Fintype.card ι := hW.trans (card_le_univ W)
  have hpow : 4 * 2 ^ (Fintype.card ι - 2) = 2 ^ Fintype.card ι := by
    have h4 : (4 : ℕ) = 2 ^ 2 := rfl
    rw [h4, ← pow_add]
    congr 1
    omega
  have hinner : ∀ i ∈ W, ∑ j ∈ W,
      ((univ : Finset (Finset ι)).filter fun s => i ∈ s ∧ j ∉ s).card =
      (W.card - 1) * 2 ^ (Fintype.card ι - 2) := by
    intro i hi
    rw [← add_sum_erase W _ hi]
    have hdiag : ((univ : Finset (Finset ι)).filter fun s => i ∈ s ∧ i ∉ s).card = 0 :=
      card_eq_zero.2 (filter_eq_empty_iff.2 fun s _ h => h.2 h.1)
    rw [hdiag, zero_add,
      sum_congr rfl fun j hj => card_filter_mem_notMem (mem_erase.1 hj).1.symm,
      sum_const, card_erase_of_mem hi, smul_eq_mul]
  rw [hswap, sum_congr rfl hinner, sum_const, smul_eq_mul]
  calc 4 * (W.card * ((W.card - 1) * 2 ^ (Fintype.card ι - 2)))
      = W.card * (W.card - 1) * (4 * 2 ^ (Fintype.card ι - 2)) := by ring
    _ = W.card * (W.card - 1) * 2 ^ Fintype.card ι := by rw [hpow]

/-- Key coin-flip inequality from the proof of Theorem 13.42 ([HartlineKarlin2007], p. 348):
if `W` has size `k ≥ 2`, then over a uniform subset `s : Finset ι`,
`𝔼 [min(|W ∩ s|, |W \ s|)] ≥ k / 4` (stated in `ℕ` without division). -/
private theorem card_mul_two_pow_le_four_mul_sum_min {W : Finset ι} (hW : 2 ≤ W.card) :
    W.card * 2 ^ Fintype.card ι ≤ 4 * ∑ s : Finset ι, min (W ∩ s).card (W \ s).card := by
  refine Nat.le_of_mul_le_mul_left ?_ (by omega : 0 < W.card - 1)
  calc (W.card - 1) * (W.card * 2 ^ Fintype.card ι)
      = 4 * ∑ s : Finset ι, (W ∩ s).card * (W \ s).card := by
        rw [four_mul_sum_inter_mul_sdiff hW]; ring
    _ ≤ 4 * ∑ s : Finset ι, (W.card - 1) * min (W ∩ s).card (W \ s).card :=
        Nat.mul_le_mul_left 4 (sum_le_sum fun s _ =>
          mul_le_pred_mul_min (card_inter_add_card_sdiff W s))
    _ = (W.card - 1) * (4 * ∑ s : Finset ι, min (W ∩ s).card (W \ s).card) := by
        rw [← mul_sum]; ring

/-! #### Theorem 13.42: RSPE has competitive ratio 4 -/

/-- **Theorem 13.42 (profit bound)** ([HartlineKarlin2007], §13.4.5, p. 348): `RSPE` is
`4`-competitive with respect to the benchmark `ℱ⁽²⁾` (`optimalProfitTwo`), i.e., for every
nonnegative bid profile `b`, `ℱ⁽²⁾(b) ≤ 4 · 𝔼[RSPE(b)]`. -/
theorem rspe_isCompetitive :
    IsCompetitive (optimalProfitTwo (ι := ι)) rspeExpectedProfit 4 := by
  refine ⟨by norm_num, fun b hb => ?_⟩
  rcases lt_or_ge (Fintype.card ι) 2 with hsmall | hcard
  · dsimp only [optimalProfitTwo]
    rw [singlePriceProfitOn_eq_zero_of_card_lt b ((card_univ (α := ι)).symm ▸ hsmall),
      rspeExpectedProfit_eq_div]
    refine mul_nonneg (by norm_num) (div_nonneg (sum_nonneg fun s _ => ?_) (by positivity))
    exact (le_min (singlePriceProfitOn_nonneg fun i _ => hb i)
      (singlePriceProfitOn_nonneg fun i _ => hb i)).trans (min_le_sum_payment_rspe s hb)
  · have hcard_pos : 0 < (univ : Finset ι).card := by rw [card_univ]; omega
    obtain ⟨j, _, hj2, hjeq⟩ :=
      exists_mem_eq_singlePriceProfitOn (m := 2) (card_pos.1 hcard_pos)
        (by rw [card_univ]; exact hcard) (b := b)
    classical
    set p := b j
    set W := univ.filter fun i => p ≤ b i
    have hp0 : 0 ≤ p := hb j
    have hpart : ∀ s : Finset ι,
        p * ((min (W ∩ s).card (W \ s).card : ℕ) : ℝ) ≤ ∑ i, (rspe s).payment b i := by
      intro s
      have key : ∀ t V : Finset ι, V ⊆ t → V ⊆ W → p * (V.card : ℝ) ≤ optimalProfitOn t b := by
        intro t V hVt hVW
        rcases V.eq_empty_or_nonempty with rfl | hne'
        · simpa using singlePriceProfitOn_nonneg fun i _ => hb i
        · exact mul_card_le_singlePriceProfitOn (fun i _ => hb i) hVt (one_le_card.2 hne')
            fun i hi => (mem_filter.1 (hVW hi)).2
      rw [Nat.cast_min, mul_min_of_nonneg _ _ hp0]
      exact (min_le_min (key s _ inter_subset_right inter_subset_left)
        (key sᶜ _ (fun i hi => mem_compl.2 (mem_sdiff.1 hi).2) sdiff_subset)).trans
        (min_le_sum_payment_rspe s hb)
    have hpow_pos : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
    have hcomb : (W.card : ℝ) * 2 ^ Fintype.card ι ≤
        4 * ∑ s : Finset ι, ((min (W ∩ s).card (W \ s).card : ℕ) : ℝ) := by
      exact_mod_cast card_mul_two_pow_le_four_mul_sum_min hj2
    dsimp only [optimalProfitTwo]
    rw [rspeExpectedProfit_eq_div, hjeq, mul_div_assoc', le_div_iff₀ hpow_pos]
    calc p * (W.card : ℝ) * 2 ^ Fintype.card ι
        = p * ((W.card : ℝ) * 2 ^ Fintype.card ι) := by ring
      _ ≤ p * (4 * ∑ s : Finset ι, ((min (W ∩ s).card (W \ s).card : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hcomb hp0
      _ = 4 * ∑ s : Finset ι, p * ((min (W ∩ s).card (W \ s).card : ℕ) : ℝ) := by
            rw [← mul_sum]; ring
      _ ≤ 4 * ∑ s : Finset ι, ∑ i, (rspe s).payment b i :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun s _ => hpart s) (by norm_num)

omit [Fintype ι] in
/-- Optimal single-price revenue of the two-bid profile `b i₀ = 1`, `b i₁ = 2` (and `0` elsewhere)
on an arbitrary subset `s : Finset ι`. -/
private theorem optimalProfitOn_two_bid {i₀ i₁ : ι} (hne : i₀ ≠ i₁) (s : Finset ι) :
    optimalProfitOn s (fun i => if i = i₀ then 1 else if i = i₁ then 2 else 0) =
      if i₁ ∈ s then 2 else if i₀ ∈ s then 1 else 0 := by
  set b : ι → ℝ := fun i => if i = i₀ then 1 else if i = i₁ then 2 else 0
  have hb0 : ∀ i, 0 ≤ b i := fun i => by dsimp only [b]; split_ifs <;> norm_num
  have hbi0 : b i₀ = 1 := by dsimp only [b]; simp only [↓reduceIte]
  have hbi1 : b i₁ = 2 := by dsimp only [b]; simp only [hne.symm, ↓reduceIte]
  change optimalProfitOn s b = _
  apply le_antisymm
  · refine singlePriceProfitOn_le (by split_ifs <;> norm_num) fun j hj _ => ?_
    by_cases hj0 : j = i₀
    · rw [hj0, hbi0, one_mul]
      have hsub : (s.filter fun i => (1 : ℝ) ≤ b i) ⊆ if i₁ ∈ s then {i₀, i₁} else {i₀} := by
        intro i hi
        obtain ⟨his, hbi⟩ := mem_filter.1 hi
        rcases eq_or_ne i i₀ with rfl | h0
        · split_ifs <;> simp
        · rcases eq_or_ne i i₁ with rfl | h1
          · simp [his]
          · simp only [b, h0, h1, ↓reduceIte] at hbi
            linarith
      have hcard : (s.filter fun i => (1 : ℝ) ≤ b i).card ≤ if i₁ ∈ s then 2 else 1 :=
        (card_le_card hsub).trans (by split_ifs <;> simp [card_pair hne])
      have h0s : i₀ ∈ s := hj0 ▸ hj
      by_cases h1s : i₁ ∈ s <;>
        simp only [h0s, h1s, ↓reduceIte] at hcard ⊢ <;> exact_mod_cast hcard
    · by_cases hj1 : j = i₁
      · rw [hj1, hbi1]
        have hsub : (s.filter fun i => (2 : ℝ) ≤ b i) ⊆ {i₁} := fun i hi => by
          have hbi := (mem_filter.1 hi).2
          dsimp only [b] at hbi
          split_ifs at hbi with h0 h1 <;> first | exact mem_singleton.2 h1 | linarith
        have hcard : ((s.filter fun i => (2 : ℝ) ≤ b i).card : ℝ) ≤ 1 := by
          exact_mod_cast (card_le_card hsub).trans (by rw [card_singleton])
        simp only [hj1 ▸ hj, ↓reduceIte]
        linarith
      · simp only [b, hj0, hj1, ↓reduceIte, zero_mul]
        split_ifs <;> norm_num
  · have hsingle {x : ι} (hx : x ∈ s) : b x ≤ optimalProfitOn s b := by
      simpa only [card_singleton, Nat.cast_one, mul_one] using
        mul_card_le_singlePriceProfitOn (m := 1) (s := s) (W := {x}) (b := b) (p := b x)
          (fun i _ => hb0 i) (singleton_subset_iff.2 hx) (by rw [card_singleton])
          fun i hi => by rw [mem_singleton.1 hi]
    split_ifs with h1 h0
    · exact hbi1 ▸ hsingle h1
    · exact hbi0 ▸ hsingle h0
    · exact singlePriceProfitOn_nonneg fun i _ => hb0 i

/-- **Theorem 13.42 (tight instance)** ([HartlineKarlin2007], §13.4.5, p. 348, referring to the
two-bid example `($1, $2)` of §13.4.2, pp. 345–346): for every finite bidder type with at least
two bidders, putting bids `1` and `2` on two distinct bidders and `0` on the rest gives
`ℱ⁽²⁾(b) = 2` and `𝔼[RSPE(b)] = 1 / 2`. -/
theorem exists_rspe_tight (hcard : 2 ≤ Fintype.card ι) :
    ∃ b : ι → ℝ, 0 ≤ b ∧ optimalProfitTwo b = 2 ∧ rspeExpectedProfit b = 1 / 2 := by
  have hnt : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨i₀, i₁, hne⟩ := exists_pair_ne ι
  let b : ι → ℝ := fun i => if i = i₀ then 1 else if i = i₁ then 2 else 0
  have hb : 0 ≤ b := fun i => by dsimp only [b]; split_ifs <;> norm_num
  have hb0 : b i₀ = 1 := by dsimp only [b]; simp only [↓reduceIte]
  have hb1 : b i₁ = 2 := by dsimp only [b]; simp only [hne.symm, ↓reduceIte]
  have hF2 : optimalProfitTwo b = 2 := by
    apply le_antisymm
    · exact (singlePriceProfitOn_le (singlePriceProfitOn_nonneg (m := 1) fun i _ => hb i)
        fun j _ hj => mul_card_le_singlePriceProfitOn (fun i _ => hb i) (filter_subset _ _)
          (by omega) fun i hi => (mem_filter.1 hi).2).trans_eq
        (by simpa only [mem_univ, ↓reduceIte] using optimalProfitOn_two_bid hne univ)
    · have hle := mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := {i₀, i₁}) (b := b)
        (p := 1) (fun i _ => hb i) (subset_univ _) (by rw [card_pair hne]) fun i hi => by
          rcases mem_insert.1 hi with rfl | hi
          · rw [hb0]
          · rw [mem_singleton.1 hi, hb1]; norm_num
      simpa only [card_pair hne, Nat.cast_ofNat, one_mul] using hle
  have hpay : ∀ s : Finset ι, ∑ i, (rspe s).payment b i =
      (if i₀ ∈ s ∧ i₁ ∉ s then (1 : ℝ) else 0) +
        (if i₁ ∈ s ∧ i₀ ∉ s then (1 : ℝ) else 0) := by
    intro s
    rw [sum_payment_rspe_eq s hb, optimalProfitOn_two_bid hne s, optimalProfitOn_two_bid hne sᶜ]
    by_cases h0 : i₀ ∈ s <;> by_cases h1 : i₁ ∈ s <;>
      simp only [mem_compl, h0, h1, not_true_eq_false, not_false_eq_true, ↓reduceIte,
        and_true, and_false] <;> norm_num
  have hsum : ∑ s : Finset ι, ∑ i, (rspe s).payment b i =
      2 * (2 ^ (Fintype.card ι - 2) : ℝ) := by
    simp_rw [hpay, sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [card_filter_mem_notMem hne, card_filter_mem_notMem hne.symm]
    push_cast
    ring
  have hcard_eq : 2 + (Fintype.card ι - 2) = Fintype.card ι := by omega
  have hpow : (2 ^ Fintype.card ι : ℝ) = 4 * (2 ^ (Fintype.card ι - 2) : ℝ) := by
    rw [← hcard_eq, pow_add]; norm_num
  refine ⟨b, hb, hF2, ?_⟩
  rw [rspeExpectedProfit_eq_div, hsum, hpow]
  field_simp; norm_num

/-- **Theorem 13.42** ([HartlineKarlin2007], §13.4.5, p. 348): for every finite bidder type with
at least two bidders, the competitive ratio of **RSPE** with respect to `ℱ⁽²⁾` (`optimalProfitTwo`)
is **exactly `4`**: `4` is the least `β` such that `IsCompetitive optimalProfitTwo
rspeExpectedProfit β`. -/
theorem isLeast_rspe_competitiveRatio (hcard : 2 ≤ Fintype.card ι) :
    IsLeast {β : ℝ | IsCompetitive (optimalProfitTwo (ι := ι)) rspeExpectedProfit β} 4 := by
  refine ⟨rspe_isCompetitive, fun β hβ => ?_⟩
  obtain ⟨b, hb, hF2, hexp⟩ := exists_rspe_tight hcard
  have hle : (2 : ℝ) ≤ β * (1 / 2) := by simpa only [hF2, hexp] using hβ.2 b hb
  linarith

end RSPE

end Cslib.GameTheory.SingleParameter.DigitalGoods

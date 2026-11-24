/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.Lean.OnlineMatching.AdWords
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Checked tests for online budgeted ad allocation (`AdWords`)

Module-client checks exercising positive, negative, and boundary behavior of
`CslibFrontier.Algorithms.Lean.OnlineMatching.AdWords`:

* feasibility and infeasibility witnesses for `LP.IsPrimalFeasible` and `LP.IsDualFeasible`;
* deterministic tie-breaking (`argmaxOver_eq_some_iff`) toward the smallest advertiser index;
* the fractional LP integrality gap (`n` bidders of budget `1`, bid `n` on a single query yields
  LP value `n` vs. online revenue `1`), showing why `b t j ≤ B j` is necessary for the `1 / 2`
  ratio of Greedy against Eq. (28.11);
* the tight two-bidder Greedy example (NRTV p. 709): concrete check at `ε = 1 / 10` (`2.1` vs.
  `3.9`), explicit discrepancy witnesses against the printed `4` (`primalObj < 4` for `ε > 0`)
  and against `ε = 3 / 2` where Greedy (`3.5`) strictly beats the off-diagonal assignment (`2.5`);
* concrete separation showing MSVV strictly outperforms Greedy on a **tie-free** 3-query instance
  (`B = ![2, 2]`, bids `![1, 9/10], ![1, 9/10], ![1, 0]`): Greedy earns `2`, while both MSVV
  variants earn `29 / 10` (`= OPT`, leaving advertiser 1's budget strictly unexhausted);
* distinction between truncated-spend and all-or-nothing spend on a single-bidder partial-budget
  trace (`1` vs. `2 / 3`);
* non-exhausted `OPT` budget check (Exercise 28.6) applying `msvvTrunc_competitive`,
  `msvvAllOrNothing_competitive`, `msvvTrunc_competitive_countLP`,
  `msvvAllOrNothing_competitive_countLP`, `msvvTrunc_tradeoff`, and complementary slackness;
* empty-query (`T = 0`), empty-advertiser (`Empty`), and all-zero-bid boundary witnesses;
* concrete `(1 - R) / 2` bound deduced from `greedyAllOrNothing_competitive` and a concrete
  `k = 2` check for `discretePhi_tradeoff_zero`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.AdWords

open Finset Cslib.Algorithms.Lean.OnlineMatching.AdWords

/-! ### Positive and negative witnesses for LP predicates -/

private def sampleLP : LP (Fin 1) (Fin 2) where
  bid := ![![1, 2]]
  budget := ![2, 2]
  demand := ![1]

example : sampleLP.IsPrimalFeasible ![![1, 0]] := by
  refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · fin_cases i; fin_cases j <;> norm_num
  · fin_cases i; norm_num [sampleLP, Fin.sum_univ_two]
  · fin_cases j <;> norm_num [sampleLP]

/-- Negative allocation fails `IsPrimalFeasible`. -/
example : ¬ sampleLP.IsPrimalFeasible ![![-1, 0]] := fun h => by
  have := h.nonneg 0 0
  norm_num at this

/-- Allocation violating demand (`1 + 1 = 2 > 1`) fails `IsPrimalFeasible`. -/
example : ¬ sampleLP.IsPrimalFeasible ![![1, 1]] := fun h => by
  have := h.demand_le 0
  norm_num [sampleLP, Fin.sum_univ_two] at this

/-- Allocation violating budget fails `IsPrimalFeasible`. -/
example : ¬ (LP.unit ![![3, 0]] ![2, 2]).IsPrimalFeasible ![![1, 0]] := fun h => by
  have := h.budget_le 0
  norm_num [LP.unit] at this

/-- Valid dual witness certificates weak duality `primalObj ≤ dualObj`. -/
example : sampleLP.IsDualFeasible ![2] ![0, 0] := by
  refine ⟨fun i => by fin_cases i; norm_num, fun j => by fin_cases j <;> norm_num, fun i j => ?_⟩
  fin_cases i; fin_cases j <;> norm_num [sampleLP]

/-- Violating the dual covering inequality fails `IsDualFeasible`. -/
example : ¬ sampleLP.IsDualFeasible ![1] ![0, 0] := fun h => by
  have := h.bid_le 0 1
  norm_num [sampleLP] at this

/-! ### Tie-breaking witness for `argmaxOver` -/

example : argmaxOver (univ : Finset (Fin 2)) (fun _ => (5 : ℝ)) = some 0 := by
  rw [argmaxOver_eq_some_iff]
  exact ⟨mem_univ 0, fun _ _ => le_rfl, fun k _ hlt => absurd hlt (Fin.not_lt_zero k)⟩

/-! ### Unbounded-bid LP integrality gap (`n` vs. `1`) -/

/-- When `bid > budget` is allowed, a single query where `n` unit-budget bidders each bid `n` has
fractional LP value `n` (via `x 0 j = 1 / n`), while capped truncated greedy collects at most `1`.
Checked at `n = 4`. -/
private def gapBids : Fin 1 → Fin 4 → ℝ := fun _ _ => 4
private def gapBudget : Fin 4 → ℝ := fun _ => 1
private def gapLP : LP (Fin 1) (Fin 4) := LP.unit gapBids gapBudget
private noncomputable def gapAlloc : Fin 1 → Fin 4 → ℝ := fun _ _ => 1 / 4

example : gapLP.IsPrimalFeasible gapAlloc ∧
    gapLP.primalObj gapAlloc = 4 ∧
    revenue (greedyTruncRule gapBudget) gapBids = 1 := by
  refine ⟨⟨fun _ _ => by norm_num [gapAlloc], fun _ => by norm_num [gapLP, LP.unit, gapAlloc],
    fun _ => by norm_num [gapLP, LP.unit, gapBids, gapBudget, gapAlloc]⟩, ?_, ?_⟩
  · norm_num [gapLP, LP.primalObj, LP.unit, gapBids, gapAlloc]
  · have harg : argmaxOver (univ.filter fun j : Fin 4 => (0 : Fin 4 → ℝ) j < gapBudget j)
        (fun j => min (gapBids 0 j) (gapBudget j - (0 : Fin 4 → ℝ) j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [gapBudget]⟩, ?_, ?_⟩
      · intro k _
        simp only [gapBids, gapBudget, Pi.zero_apply, sub_zero, le_refl]
      · intro k _ hlt
        exact absurd hlt (Fin.not_lt_zero k)
    have hstep0 : greedyTruncRule gapBudget 0 (gapBids 0) = ⟨some 0, 1⟩ := by
      simp only [greedyTruncRule, harg]
      congr 1
      norm_num [gapBids, gapBudget]
    have hfin : finalSpent (greedyTruncRule gapBudget) gapBids =
        Function.update (0 : Fin 4 → ℝ) 0 1 := by
      change spentAt _ _ (Fin.succ 0) = _
      rw [spentAt_succ]
      simp only [Fin.castSucc_zero, spentAt_zero, hstep0, applyStep, Pi.zero_apply, zero_add]
    rw [revenue, hfin]
    norm_num [Fin.sum_univ_four]

/-! ### Greedy two-bidder example (NRTV p. 709) and printed discrepancy `4` vs. `4 - ε` -/

/-- At `ε = 1 / 10`, greedy earns `21 / 10` while `OPT` is `39 / 10` (strictly `< 4`). -/
example :
    revenue (greedyTruncRule twoBidderBudget) (twoBidderBids (1 / 10)) = 21 / 10 ∧
      revenue (greedyAllOrNothingRule twoBidderBudget) (twoBidderBids (1 / 10)) = 21 / 10 ∧
      (LP.unit (twoBidderBids (1 / 10)) twoBidderBudget).primalObj twoBidderOptAlloc = 39 / 10 ∧
      ∀ x, (LP.unit (twoBidderBids (1 / 10)) twoBidderBudget).IsPrimalFeasible x →
        (LP.unit (twoBidderBids (1 / 10)) twoBidderBudget).primalObj x < 4 := by
  have h := greedy_two_bidder_example (ε := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨by linarith [h.1], by linarith [h.2.1], by linarith [h.2.2.2.1], fun x hx => ?_⟩
  have hle := h.2.2.2.2 (by norm_num) x hx
  linarith

/-- At `ε = 3 / 2 ∈ (1, 2)`, greedy's `2 + ε = 7 / 2` strictly exceeds the off-diagonal assignment
`4 - ε = 5 / 2`, confirming that `ε ≤ 1` is required for `twoBidderOptAlloc` to be optimal. -/
example :
    revenue (greedyTruncRule twoBidderBudget) (twoBidderBids (3 / 2)) = 7 / 2 ∧
      (LP.unit (twoBidderBids (3 / 2)) twoBidderBudget).primalObj twoBidderOptAlloc = 5 / 2 := by
  have h := greedy_two_bidder_example (ε := (3 / 2 : ℝ)) (by norm_num) (by norm_num)
  exact ⟨by linarith [h.1], by linarith [h.2.2.2.1]⟩

/-- Deducing the weaker `(1 - R) / 2` bound from the tighter `greedyAllOrNothing_competitive`. -/
example {T : ℕ} {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : Fin T → ι → ℝ} {budget : ι → ℝ} {x : Fin T → ι → ℝ} {R : ℝ}
    (hB : ∀ j, 0 < budget j) (hR0 : 0 ≤ R) (hR1 : R ≤ 1)
    (hb0 : ∀ t j, 0 ≤ b t j) (hbR : ∀ t j, b t j ≤ R * budget j)
    (hx : (LP.unit b budget).IsPrimalFeasible x) :
    ((1 - R) / 2) * (LP.unit b budget).primalObj x ≤
      revenue (greedyAllOrNothingRule budget) b := by
  have h := greedyAllOrNothing_competitive hB hR0 hR1 hb0 hbR hx
  have hrev : 0 ≤ revenue (greedyAllOrNothingRule budget) b :=
    Finset.sum_nonneg fun j _ =>
      (greedyAllOrNothing_spent_mem (fun k => (hB k).le) hb0 (Fin.last T) j).1
  nlinarith

/-! ### Strict tie-free separation: MSVV (`2.9`) beats Greedy (`2.0`) -/

private def sepBudget : Fin 2 → ℝ := ![2, 2]
private noncomputable def sepBids : Fin 3 → Fin 2 → ℝ :=
  ![![1, 9 / 10], ![1, 9 / 10], ![1, 0]]

private lemma msvv_half_lt_point_nine :
    1 * msvvWeight (1 / 2) < (9 / 10 : ℝ) * msvvWeight 0 := by
  set u := Real.exp (-1 / 2)
  have hu_pos : 0 < u := Real.exp_pos _
  have hu_lt_one : u < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hu_sq : u ^ 2 = Real.exp (-1) := by
    rw [sq, ← Real.exp_add]
    congr 1
    norm_num
  have h_e_lt : Real.exp 1 < 81 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h_inv_gt : (1 / 9 : ℝ) < u := by
    have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hsq_gt : (1 / 81 : ℝ) < u ^ 2 := by
      rw [hu_sq]
      nlinarith [Real.exp_pos 1]
    nlinarith [sq_nonneg (u - 1 / 9)]
  have h1 : msvvWeight (1 / 2) = 1 - u := by
    simp only [msvvWeight, u]
    congr 2
    norm_num
  have h0 : msvvWeight 0 = 1 - u ^ 2 := by
    simp only [msvvWeight, hu_sq, zero_sub]
  rw [h1, h0]
  have hfac : (9 / 10 : ℝ) * (1 - u ^ 2) - (1 - u) = (1 - u) * (9 * u - 1) / 10 := by ring
  have hpos : 0 < (1 - u) * (9 * u - 1) / 10 := by
    have ha : 0 < 1 - u := by linarith
    have hb : 0 < 9 * u - 1 := by linarith
    positivity
  linarith

/-- On `sepBids` (`B = ![2, 2]`, `q 0 = ![1, 9/10]`, `q 1 = ![1, 9/10]`, `q 2 = ![1, 0]`):
no ties occur at any step. Both `greedyTruncRule` and `greedyAllOrNothingRule` collect `2`
(exhausting bidder 0 on `q 0, q 1`, then collecting `0` on `q 2`), while both `msvvTruncRule` and
`msvvAllOrNothingRule` spread `q 1` to bidder 1 and collect `29 / 10 = 2.9` (matching the optimum
LP value, while leaving bidder 1's budget strictly unexhausted: `0.9 < 2`). -/
example :
    revenue (greedyTruncRule sepBudget) sepBids = 2 ∧
      revenue (msvvTruncRule sepBudget) sepBids = 29 / 10 ∧
      revenue (msvvAllOrNothingRule sepBudget) sepBids = 29 / 10 := by
  have hg0 : greedyTruncRule sepBudget 0 (sepBids 0) = ⟨some 0, 1⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 => (0 : Fin 2 → ℝ) j < sepBudget j)
        (fun j => min (sepBids 0 j) (sepBudget j - (0 : Fin 2 → ℝ) j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k <;> norm_num [sepBids, sepBudget]
      · intro k _ hlt; exact absurd hlt (Fin.not_lt_zero k)
    simp only [greedyTruncRule, harg]
    norm_num [sepBids, sepBudget]
  have hgs1 : spentAt (greedyTruncRule sepBudget) sepBids 1 = ![1, 0] := by
    funext j; change spentAt _ _ (Fin.succ 0) j = _; rw [spentAt_succ]
    simp only [Fin.castSucc_zero, spentAt_zero, hg0, applyStep]
    fin_cases j <;> norm_num [Function.update]
  have hg1 : greedyTruncRule sepBudget ![1, 0] (sepBids 1) = ⟨some 0, 1⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 => (![1, 0] : Fin 2 → ℝ) j < sepBudget j)
        (fun j => min (sepBids 1 j) (sepBudget j - (![1, 0] : Fin 2 → ℝ) j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k <;> norm_num [sepBids, sepBudget]
      · intro k _ hlt; exact absurd hlt (Fin.not_lt_zero k)
    simp only [greedyTruncRule, harg]
    norm_num [sepBids, sepBudget]
  have hgs2 : spentAt (greedyTruncRule sepBudget) sepBids 2 = ![2, 0] := by
    funext j; change spentAt _ _ (Fin.succ 1) j = _; rw [spentAt_succ]
    have hcs : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
    rw [hcs, hgs1, hg1]
    fin_cases j <;> norm_num [applyStep, Function.update]
  have hg2 : greedyTruncRule sepBudget ![2, 0] (sepBids 2) = ⟨some 1, 0⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 => (![2, 0] : Fin 2 → ℝ) j < sepBudget j)
        (fun j => min (sepBids 2 j) (sepBudget j - (![2, 0] : Fin 2 → ℝ) j)) = some 1 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 1, by norm_num [sepBudget]⟩, ?_, ?_⟩
      · intro k hk; have hk' := (mem_filter.mp hk).2
        fin_cases k
        · norm_num [sepBudget] at hk'
        · exact le_rfl
      · intro k hk hlt; have hk' := (mem_filter.mp hk).2
        fin_cases k
        · norm_num [sepBudget] at hk'
        · exact absurd hlt (lt_irrefl 1)
    simp only [greedyTruncRule, harg]
    norm_num [sepBids, sepBudget]
  have hgrev : revenue (greedyTruncRule sepBudget) sepBids = 2 := by
    have hfin : finalSpent (greedyTruncRule sepBudget) sepBids = ![2, 0] := by
      funext j; change spentAt _ _ (Fin.succ 2) j = _; rw [spentAt_succ]
      have hcs : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
      rw [hcs, hgs2, hg2]
      fin_cases j <;> norm_num [applyStep, Function.update]
    norm_num [revenue, hfin, Fin.sum_univ_two]
  have hφ0_pos : 0 < msvvWeight 0 := by
    rw [msvvWeight, zero_sub, sub_pos, Real.exp_lt_one_iff]; norm_num
  have hφh_pos : 0 < msvvWeight (1 / 2) := by
    rw [msvvWeight, sub_pos, Real.exp_lt_one_iff]; norm_num
  -- MSVV truncated trace
  have hm0 : msvvTruncRule sepBudget 0 (sepBids 0) = ⟨some 0, 1⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 => (0 : Fin 2 → ℝ) j < sepBudget j)
        (fun j => sepBids 0 j * msvvWeight ((0 : Fin 2 → ℝ) j / sepBudget j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k
        · exact le_rfl
        · change (9 / 10 : ℝ) * msvvWeight (0 / 2) ≤ 1 * msvvWeight (0 / 2)
          rw [zero_div]; nlinarith
      · intro k _ hlt; exact absurd hlt (Fin.not_lt_zero k)
    simp only [msvvTruncRule, harg]
    norm_num [sepBids, sepBudget]
  have hms1 : spentAt (msvvTruncRule sepBudget) sepBids 1 = ![1, 0] := by
    funext j; change spentAt _ _ (Fin.succ 0) j = _; rw [spentAt_succ]
    simp only [Fin.castSucc_zero, spentAt_zero, hm0, applyStep]
    fin_cases j <;> norm_num [Function.update]
  have hm1 : msvvTruncRule sepBudget ![1, 0] (sepBids 1) = ⟨some 1, 9 / 10⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 => (![1, 0] : Fin 2 → ℝ) j < sepBudget j)
        (fun j => sepBids 1 j * msvvWeight ((![1, 0] : Fin 2 → ℝ) j / sepBudget j)) = some 1 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 1, by norm_num [sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k
        · change 1 * msvvWeight (1 / 2) ≤ (9 / 10 : ℝ) * msvvWeight (0 / 2)
          rw [zero_div]; exact msvv_half_lt_point_nine.le
        · exact le_rfl
      · intro k _ hlt; fin_cases k
        · change 1 * msvvWeight (1 / 2) < (9 / 10 : ℝ) * msvvWeight (0 / 2)
          rw [zero_div]; exact msvv_half_lt_point_nine
        · exact absurd hlt (lt_irrefl 1)
    simp only [msvvTruncRule, harg]
    norm_num [sepBids, sepBudget]
  have hms2 : spentAt (msvvTruncRule sepBudget) sepBids 2 = ![1, 9 / 10] := by
    funext j; change spentAt _ _ (Fin.succ 1) j = _; rw [spentAt_succ]
    have hcs : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
    rw [hcs, hms1, hm1]
    fin_cases j <;> norm_num [applyStep, Function.update]
  have hm2 : msvvTruncRule sepBudget ![1, 9 / 10] (sepBids 2) = ⟨some 0, 1⟩ := by
    have harg : argmaxOver
        (univ.filter fun j : Fin 2 => (![1, 9 / 10] : Fin 2 → ℝ) j < sepBudget j)
        (fun j => sepBids 2 j * msvvWeight ((![1, 9 / 10] : Fin 2 → ℝ) j / sepBudget j)) =
        some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k
        · exact le_rfl
        · change 0 * msvvWeight ((9 / 10 : ℝ) / 2) ≤ 1 * msvvWeight (1 / 2)
          rw [zero_mul]; linarith
      · intro k _ hlt; exact absurd hlt (Fin.not_lt_zero k)
    simp only [msvvTruncRule, harg]
    norm_num [sepBids, sepBudget]
  have hmrev : revenue (msvvTruncRule sepBudget) sepBids = 29 / 10 := by
    have hfin : finalSpent (msvvTruncRule sepBudget) sepBids = ![2, 9 / 10] := by
      funext j; change spentAt _ _ (Fin.succ 2) j = _; rw [spentAt_succ]
      have hcs : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
      rw [hcs, hms2, hm2]
      fin_cases j <;> norm_num [applyStep, Function.update]
    norm_num [revenue, hfin, Fin.sum_univ_two]
  -- MSVV all-or-nothing trace (identical because every bid fits strictly)
  have ha0 : msvvAllOrNothingRule sepBudget 0 (sepBids 0) = ⟨some 0, 1⟩ := by
    have harg : argmaxOver
        (univ.filter fun j : Fin 2 => (0 : Fin 2 → ℝ) j + sepBids 0 j ≤ sepBudget j)
        (fun j => sepBids 0 j * msvvWeight ((0 : Fin 2 → ℝ) j / sepBudget j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [sepBids, sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k
        · exact le_rfl
        · change (9 / 10 : ℝ) * msvvWeight (0 / 2) ≤ 1 * msvvWeight (0 / 2)
          rw [zero_div]; nlinarith
      · intro k _ hlt; exact absurd hlt (Fin.not_lt_zero k)
    simp only [msvvAllOrNothingRule, harg]; rfl
  have has1 : spentAt (msvvAllOrNothingRule sepBudget) sepBids 1 = ![1, 0] := by
    funext j; change spentAt _ _ (Fin.succ 0) j = _; rw [spentAt_succ]
    simp only [Fin.castSucc_zero, spentAt_zero, ha0, applyStep]
    fin_cases j <;> norm_num [Function.update]
  have ha1 : msvvAllOrNothingRule sepBudget ![1, 0] (sepBids 1) = ⟨some 1, 9 / 10⟩ := by
    have harg : argmaxOver
        (univ.filter fun j : Fin 2 => (![1, 0] : Fin 2 → ℝ) j + sepBids 1 j ≤ sepBudget j)
        (fun j => sepBids 1 j * msvvWeight ((![1, 0] : Fin 2 → ℝ) j / sepBudget j)) = some 1 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 1, by norm_num [sepBids, sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k
        · change 1 * msvvWeight (1 / 2) ≤ (9 / 10 : ℝ) * msvvWeight (0 / 2)
          rw [zero_div]; exact msvv_half_lt_point_nine.le
        · exact le_rfl
      · intro k _ hlt; fin_cases k
        · change 1 * msvvWeight (1 / 2) < (9 / 10 : ℝ) * msvvWeight (0 / 2)
          rw [zero_div]; exact msvv_half_lt_point_nine
        · exact absurd hlt (lt_irrefl 1)
    simp only [msvvAllOrNothingRule, harg]; rfl
  have has2 : spentAt (msvvAllOrNothingRule sepBudget) sepBids 2 = ![1, 9 / 10] := by
    funext j; change spentAt _ _ (Fin.succ 1) j = _; rw [spentAt_succ]
    have hcs : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
    rw [hcs, has1, ha1]
    fin_cases j <;> norm_num [applyStep, Function.update]
  have ha2 : msvvAllOrNothingRule sepBudget ![1, 9 / 10] (sepBids 2) = ⟨some 0, 1⟩ := by
    have harg : argmaxOver
        (univ.filter fun j : Fin 2 => (![1, 9 / 10] : Fin 2 → ℝ) j + sepBids 2 j ≤ sepBudget j)
        (fun j => sepBids 2 j * msvvWeight ((![1, 9 / 10] : Fin 2 → ℝ) j / sepBudget j)) =
        some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num [sepBids, sepBudget]⟩, ?_, ?_⟩
      · intro k _; fin_cases k
        · exact le_rfl
        · change 0 * msvvWeight ((9 / 10 : ℝ) / 2) ≤ 1 * msvvWeight (1 / 2)
          rw [zero_mul]; linarith
      · intro k _ hlt; exact absurd hlt (Fin.not_lt_zero k)
    simp only [msvvAllOrNothingRule, harg]; rfl
  have harev : revenue (msvvAllOrNothingRule sepBudget) sepBids = 29 / 10 := by
    have hfin : finalSpent (msvvAllOrNothingRule sepBudget) sepBids = ![2, 9 / 10] := by
      funext j; change spentAt _ _ (Fin.succ 2) j = _; rw [spentAt_succ]
      have hcs : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
      rw [hcs, has2, ha2]
      fin_cases j <;> norm_num [applyStep, Function.update]
    norm_num [revenue, hfin, Fin.sum_univ_two]
  exact ⟨hgrev, hmrev, harev⟩

/-! ### Truncated vs. all-or-nothing payment difference on a single bidder -/

/-- When a second query of bid `2 / 3` arrives for a bidder with `1 / 3` budget remaining,
`msvvTruncRule` collects the truncated remainder `1 / 3` (total `1`), whereas
`msvvAllOrNothingRule` skips the query (total `2 / 3`). -/
example :
    revenue (msvvTruncRule ![1]) ![![2 / 3], ![2 / 3]] = 1 ∧
      revenue (msvvAllOrNothingRule ![1]) ![![2 / 3], ![2 / 3]] = 2 / 3 := by
  have ht0 : msvvTruncRule ![1] 0 ![2 / 3] = ⟨some 0, 2 / 3⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 1 => (0 : Fin 1 → ℝ) j < ![1] j)
        (fun j => ![2 / 3] j * msvvWeight ((0 : Fin 1 → ℝ) j / ![1] j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      exact ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num⟩, fun k _ => by fin_cases k; exact le_rfl,
        fun k _ hlt => absurd hlt (Fin.not_lt_zero k)⟩
    simp only [msvvTruncRule, harg]; norm_num
  have hts1 : spentAt (msvvTruncRule ![1]) ![![2 / 3], ![2 / 3]] 1 = ![2 / 3] := by
    funext j; fin_cases j; change spentAt _ _ (Fin.succ 0) 0 = _
    rw [spentAt_succ]
    change applyStep (spentAt _ _ 0) (msvvTruncRule ![1] (spentAt _ _ 0) ![2 / 3]) 0 = 2 / 3
    rw [spentAt_zero, ht0]
    norm_num [applyStep, Function.update]
  have ht1 : msvvTruncRule ![1] ![2 / 3] ![2 / 3] = ⟨some 0, 1 / 3⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 1 => (![2 / 3] : Fin 1 → ℝ) j < ![1] j)
        (fun j => ![2 / 3] j * msvvWeight ((![2 / 3] : Fin 1 → ℝ) j / ![1] j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      exact ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num⟩, fun k _ => by fin_cases k; exact le_rfl,
        fun k _ hlt => absurd hlt (Fin.not_lt_zero k)⟩
    simp only [msvvTruncRule, harg]; norm_num
  have htrev : revenue (msvvTruncRule ![1]) ![![2 / 3], ![2 / 3]] = 1 := by
    have hfin : finalSpent (msvvTruncRule ![1]) ![![2 / 3], ![2 / 3]] = ![1] := by
      funext j; fin_cases j; change spentAt _ _ (Fin.succ 1) 0 = _
      rw [spentAt_succ]
      change applyStep (spentAt _ _ 1) (msvvTruncRule ![1] (spentAt _ _ 1) ![2 / 3]) 0 = 1
      rw [hts1, ht1]; norm_num [applyStep, Function.update]
    norm_num [revenue, hfin]
  have ha0 : msvvAllOrNothingRule ![1] 0 ![2 / 3] = ⟨some 0, 2 / 3⟩ := by
    have harg : argmaxOver
        (univ.filter fun j : Fin 1 => (0 : Fin 1 → ℝ) j + ![2 / 3] j ≤ ![1] j)
        (fun j => ![2 / 3] j * msvvWeight ((0 : Fin 1 → ℝ) j / ![1] j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      exact ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num⟩, fun k _ => by fin_cases k; exact le_rfl,
        fun k _ hlt => absurd hlt (Fin.not_lt_zero k)⟩
    simp only [msvvAllOrNothingRule, harg]; rfl
  have has1 : spentAt (msvvAllOrNothingRule ![1]) ![![2 / 3], ![2 / 3]] 1 = ![2 / 3] := by
    funext j; fin_cases j; change spentAt _ _ (Fin.succ 0) 0 = _
    rw [spentAt_succ]
    change applyStep (spentAt _ _ 0)
      (msvvAllOrNothingRule ![1] (spentAt _ _ 0) ![2 / 3]) 0 = 2 / 3
    rw [spentAt_zero, ha0]
    norm_num [applyStep, Function.update]
  have ha1 : msvvAllOrNothingRule ![1] ![2 / 3] ![2 / 3] = ⟨none, 0⟩ := by
    have hemp : (univ.filter fun j : Fin 1 => (![2 / 3] : Fin 1 → ℝ) j + ![2 / 3] j ≤ ![1] j) =
        ∅ := by
      ext j; fin_cases j; norm_num
    simp only [msvvAllOrNothingRule, hemp, argmaxOver, sort_empty, List.argmax_nil]
  have harev : revenue (msvvAllOrNothingRule ![1]) ![![2 / 3], ![2 / 3]] = 2 / 3 := by
    have hfin : finalSpent (msvvAllOrNothingRule ![1]) ![![2 / 3], ![2 / 3]] = ![2 / 3] := by
      funext j; fin_cases j; change spentAt _ _ (Fin.succ 1) 0 = _
      rw [spentAt_succ]
      change applyStep (spentAt _ _ 1)
        (msvvAllOrNothingRule ![1] (spentAt _ _ 1) ![2 / 3]) 0 = 2 / 3
      rw [has1, ha1]; norm_num [applyStep]
    norm_num [revenue, hfin]
  exact ⟨htrev, harev⟩

/-! ### Non-exhausted `OPT` budget witness (Exercise 28.6) and `countLP` -/

/-- Concrete keyword-frequency LP (`countLP`) where **neither** advertiser exhausts its budget
in `OPT` (`budget = ![10, 10]`, bids `![![1, 0], ![0, 2]]`, 3 queries `![0, 0, 1]`, so
`demand = ![2, 1]`, `OPT = 4` leaving slacks `8` and `8`). Exercises `LP.complementarySlackness`,
`msvvTrunc_competitive_countLP`, `msvvAllOrNothing_competitive_countLP`, `msvvTrunc_tradeoff`,
and `greedyTrunc_competitive`. -/
example :
    (1 - Real.exp (-1)) * Real.exp (-(1 / 5)) * 4 ≤
        revenue (msvvTruncRule ![10, 10]) (fun t j => ![![1, 0], ![0, 2]] (![0, 0, 1] t) j) ∧
      (1 - Real.exp (-1)) * (1 - 1 / 5) * Real.exp (-(1 / 5)) * 4 ≤
        revenue (msvvAllOrNothingRule ![10, 10])
          (fun t j => ![![1, 0], ![0, 2]] (![0, 0, 1] t) j) ∧
      4 ≤ 2 * revenue (greedyTruncRule ![10, 10])
        (fun t j => ![![1, 0], ![0, 2]] (![0, 0, 1] t) j) := by
  let bid : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 2]]
  let B : Fin 2 → ℝ := ![10, 10]
  let qs : Fin 3 → Fin 2 := ![0, 0, 1]
  let x : Fin 2 → Fin 2 → ℝ := ![![2, 0], ![0, 1]]
  have hfreq0 : (univ.filter fun t : Fin 3 => qs t = 0).card = 2 := by decide
  have hfreq1 : (univ.filter fun t : Fin 3 => qs t = 1).card = 1 := by decide
  have hx : (LP.countLP bid B qs).IsPrimalFeasible x := by
    refine ⟨fun i j => by fin_cases i <;> fin_cases j <;> norm_num [x], fun i => ?_, fun j => ?_⟩
    · fin_cases i
      · rw [Fin.sum_univ_two]
        change x 0 0 + x 0 1 ≤ ((univ.filter fun t : Fin 3 => qs t = 0).card : ℝ)
        rw [hfreq0]; norm_num [x]
      · rw [Fin.sum_univ_two]
        change x 1 0 + x 1 1 ≤ ((univ.filter fun t : Fin 3 => qs t = 1).card : ℝ)
        rw [hfreq1]; norm_num [x]
    · fin_cases j <;> norm_num [LP.countLP, bid, B, x, Fin.sum_univ_two]
  have hslack0 : ∑ i : Fin 2, bid i 0 * x i 0 < B 0 := by
    norm_num [bid, B, x, Fin.sum_univ_two]
  have hslack1 : ∑ i : Fin 2, bid i 1 * x i 1 < B 1 := by
    norm_num [bid, B, x, Fin.sum_univ_two]
  have hd : (LP.countLP bid B qs).IsDualFeasible ![1, 2] ![0, 0] := by
    refine ⟨fun i => by fin_cases i <;> norm_num, fun j => by fin_cases j <;> norm_num,
      fun i j => by fin_cases i <;> fin_cases j <;> norm_num [LP.countLP, bid]⟩
  have hobj : (LP.countLP bid B qs).primalObj x = 4 := by
    norm_num [LP.primalObj, LP.countLP, bid, x, Fin.sum_univ_two]
  have hdobj : (LP.countLP bid B qs).dualObj ![1, 2] ![0, 0] = 4 := by
    simp only [LP.dualObj, LP.countLP, B, Fin.sum_univ_two, hfreq0, hfreq1]; norm_num
  have _ := LP.complementarySlackness hx hd (by linarith) (i := 0) (j := 0) (by norm_num [x])
  have hB : ∀ j, 0 < B j := fun j => by fin_cases j <;> norm_num [B]
  have hb0 : ∀ i j, 0 ≤ bid i j := fun i j => by fin_cases i <;> fin_cases j <;> norm_num [bid]
  have hbR : ∀ i j, bid i j ≤ (1 / 5 : ℝ) * B j :=
    fun i j => by fin_cases i <;> fin_cases j <;> norm_num [bid, B]
  have hm1 := msvvTrunc_competitive_countLP qs hB hb0 hbR hx
  have hm2 := msvvAllOrNothing_competitive_countLP qs hB (by norm_num) (by norm_num) hb0 hbR hx
  obtain ⟨y, hy, hyobj⟩ := LP.exists_unitPrimal_of_countLP qs hx
  have hgr := greedyTrunc_competitive hB (fun t j => hb0 (qs t) j)
    (fun t j => by have := hbR (qs t) j; have := hB j; linarith) hy
  have _ := msvvTrunc_tradeoff hB (fun t j => hb0 (qs t) j) hy
  have _ : ∑ i : Fin 2, bid i 0 * x i 0 < B 0 ∧ ∑ i : Fin 2, bid i 1 * x i 1 < B 1 :=
    ⟨hslack0, hslack1⟩
  rw [hobj] at hm1 hm2 hyobj
  rw [hyobj] at hgr
  exact ⟨hm1, hm2, hgr⟩

/-! ### Edge cases: empty query stream, empty advertiser set, zero bids -/

example : revenue (msvvTruncRule ![5, 5]) (fun (t : Fin 0) => Fin.elim0 t) = 0 := by
  simp only [revenue, finalSpent, show Fin.last 0 = (0 : Fin 1) from rfl, spentAt_zero,
    Pi.zero_apply, sum_const_zero]

example : revenue (msvvTruncRule (Empty.elim : Empty → ℝ)) (fun (_ : Fin 2) => Empty.elim) = 0 := by
  simp only [revenue, univ_eq_empty, sum_empty]

example :
    (LP.unit (fun (_ : Fin 2) (_ : Fin 2) => (0 : ℝ)) ![3, 4]).primalObj
      (fun _ _ => 0) = 0 ∧
      revenue (msvvTruncRule ![3, 4]) (fun (_ : Fin 2) (_ : Fin 2) => (0 : ℝ)) = 0 := by
  refine ⟨by norm_num [LP.primalObj, LP.unit], ?_⟩
  have ht0 : msvvTruncRule ![3, 4] 0 (fun _ : Fin 2 => (0 : ℝ)) = ⟨some 0, 0⟩ := by
    have harg : argmaxOver (univ.filter fun j : Fin 2 => (0 : Fin 2 → ℝ) j < ![3, 4] j)
        (fun j => (0 : ℝ) * msvvWeight ((0 : Fin 2 → ℝ) j / ![3, 4] j)) = some 0 := by
      rw [argmaxOver_eq_some_iff]
      refine ⟨mem_filter.mpr ⟨mem_univ 0, by norm_num⟩, fun k _ => by simp,
        fun k _ hlt => absurd hlt (Fin.not_lt_zero k)⟩
    simp only [msvvTruncRule, harg]
    norm_num
  have hs1 : spentAt (msvvTruncRule ![3, 4]) (fun (_ : Fin 2) (_ : Fin 2) => 0) 1 = 0 := by
    funext j; change spentAt _ _ (Fin.succ 0) j = _; rw [spentAt_succ]
    simp only [Fin.castSucc_zero, spentAt_zero, ht0, applyStep]
    fin_cases j <;> norm_num [Function.update]
  have hs2 : finalSpent (msvvTruncRule ![3, 4]) (fun (_ : Fin 2) (_ : Fin 2) => 0) = 0 := by
    funext j; change spentAt _ _ (Fin.succ 1) j = _; rw [spentAt_succ]
    have hcs : (1 : Fin 2).castSucc = (1 : Fin 3) := rfl
    rw [hcs, hs1, ht0]
    fin_cases j <;> norm_num [applyStep, Function.update]
  simp only [revenue, hs2, Pi.zero_apply, sum_const_zero]

/-! ### Concrete check of `discretePhi_tradeoff_zero` (`k = 2`) -/

/-- With `k = 2`, `discretePhi 2 0 = 3 / 4`, `discretePhi 2 1 = 1 / 2`, `discretePhi 2 2 = 0`.
For `s = ![0, 0, 2]` (all total budget `2` ending in type `2`) and `w = ![0, 1, 1]`,
`w 0 = 0`, `w 1 = 1 ≤ 2 / 2`, `w 2 = 1 ≤ 2 / 2`, and `discretePhi_tradeoff_zero` gives
`3 / 4 * 2 = 3 / 2 ≤ 2`. -/
example :
    discretePhi 2 0 * (∑ i : Fin 3, (![0, 0, 2] : Fin 3 → ℝ) i) ≤
      ∑ i : Fin 3, (i.val : ℝ) / 2 * (![0, 0, 2] : Fin 3 → ℝ) i :=
  discretePhi_tradeoff_zero (k := 2) (by decide)
    (s := ![0, 0, 2]) (w := ![0, 1, 1])
    (by
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      norm_num [discretePhi])
    (by rfl)
    (fun i hi => by
      fin_cases i
      · simp at hi
      · rw [Finset.sum_filter, Fin.sum_univ_three]
        norm_num
      · rw [Finset.sum_filter, Fin.sum_univ_three]
        norm_num)

/-- General `discretePhi_tradeoff` with nonzero `w 0` (`k = 2`, `s = ![0, 0, 2]`, `w = ![1, 1, 1]`).
-/
example :
    (1 - 1 / (2 : ℝ)) * discretePhi 2 0 * (∑ i : Fin 3, (![0, 0, 2] : Fin 3 → ℝ) i) ≤
      ∑ i : Fin 3, (i.val : ℝ) / 2 * (![0, 0, 2] : Fin 3 → ℝ) i :=
  discretePhi_tradeoff (k := 2) (by decide)
    (s := ![0, 0, 2]) (w := ![1, 1, 1])
    (by
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      norm_num [discretePhi])
    (fun i => by
      fin_cases i <;> rw [Finset.sum_filter, Fin.sum_univ_three] <;> norm_num)

/-- Concrete `Filter.Tendsto` consequence: for any `δ > 0`, `discretePhi k 0` eventually gets
within `δ` of `1 - exp (-1)`. -/
example : ∃ N : ℕ, ∀ k ≥ N, |discretePhi k 0 - (1 - Real.exp (-1))| < 1 / 100 := by
  have h := Metric.tendsto_atTop.mp tendsto_discretePhi_zero (1 / 100) (by norm_num)
  simpa only [Real.dist_eq] using h

/-- For sufficiently small `R`, the MSVV truncated competitive factor is within `1 / 100` of
`1 - exp (-1)`. -/
example : ∃ δ > 0, ∀ R : ℝ, |R| < δ →
    |(1 - Real.exp (-1)) * Real.exp (-R) - (1 - Real.exp (-1))| < 1 / 100 := by
  have h := Metric.tendsto_nhds_nhds.mp tendsto_msvvTrunc_factor (1 / 100) (by norm_num)
  simpa only [Real.dist_eq, sub_zero] using h

end CslibFrontierTests.Algorithms.AdWords

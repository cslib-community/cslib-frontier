/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.BudgetedAuction.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Private-budget impossibility for multi-unit auctions (Dobzinski–Lavi–Nisan)

Proves the **impossibility theorem** of Dobzinski, Lavi, and Nisan ([DobzinskiLaviNisan2012];
primary PDF not inspected, theorem/page locators unverified): for any finite bidder set `ι` with
`2 ≤ Fintype.card ι` and any positive divisible supply `m > 0`, **no** deterministic auction is
simultaneously feasible (`IsFeasibleOnPos m`), nonnegative-paying (`HasNonnegPaymentOnPos`),
hard budget-feasible (`IsBudgetFeasibleOnPos`), individually rational (`IsIROnPos`), Pareto
optimal (`IsParetoOptimalOnPos m`), and dominant-strategy incentive compatible over private
`(val, budget)` types (`IsPrivateBudgetDSIC`).

The proof requires **no** anonymity, symmetry, continuity, or measure-theoretic Myerson integral:
1. `pinning_of_isPrivateBudgetDSIC_isParetoOptimal`: when a budget-constrained bidder `j` faces
   an unconstrained competitor `i` (`m * v < Bᵢ`) with `Bⱼ / m < v < w` (and all other bidders
   `k ∉ {i, j}` strictly below `v`), truthfulness, individual rationality, and Pareto optimality
   uniquely pin `(alloc j, alloc i, payment j) = (Bⱼ / v, m - Bⱼ / v, Bⱼ)`.
2. Telescoping the finite 9-point `IsPrivateBudgetDSIC` upper bound along
   `tₖ = (6 + k) / 6 * (B / m)` (`k = 0, …, 9`) yields
   `payment i ≤ (∑ r ∈ Finset.Ico 6 15, 1 / r) * B = (348911 / 360360) * B < B`,
   showing that a bidder with true type `(100 / m, 1)` can *affordably* over-report its budget to
   `⟨5 / (2 * m), 10⟩` and secure `3 / 5 * m` units for payment `< 1`.
3. Applying that profitable deviation symmetrically to both `i₀` and `i₁` at `⟨100 / m, 1⟩` gives
   `(118 ≤ 100)` against the total supply bound `alloc i₀ + alloc i₁ ≤ m`.

Note on the **hard-budget model**: `IsPrivateBudgetDSIC` allows bidders to report an inflated
budget `b'.budget > true_budget` whenever the *realized* payment satisfies `payment ≤ true_budget`
(since exceeding true budget incurs utility `-∞`). This models non-verifiable budgets (no upfront
escrow deposit). Under **non-overreportable** (`b'.budget ≤ true_budget`) budgets, even the fixed
tie-break capped second-price auction for a single *indivisible* unit (`alloc ∈ {0, 1}`) **is**
truthful, IR, and budget-feasible — while failing over-reportable `IsPrivateBudgetDSIC` on a budget
tie `![⟨5, 1⟩, ⟨3, 1⟩]` (both witnessed in `CslibFrontierTests.GameTheory.BudgetedAuction`).

## Main results

* `Cslib.GameTheory.BudgetedAuction.pinning_of_isPrivateBudgetDSIC_isParetoOptimal`:
  unique allocation and payment pinning against one unconstrained competitor with `Bᵢ > m * v`.
* `Cslib.GameTheory.BudgetedAuction.not_exists_privateBudgetDSIC_isParetoOptimal`:
  Dobzinski–Lavi–Nisan impossibility theorem for `2 ≤ Fintype.card ι` and `0 < m`
  ([DobzinskiLaviNisan2012], primary PDF not inspected; theorem/page locators unverified).

## References

* [S. Dobzinski, R. Lavi, and N. Nisan,
  *Multi-unit auctions with budget limits*][DobzinskiLaviNisan2012]
  (primary PDF not inspected; theorem/page locators unverified)
-/

public section

namespace Cslib.GameTheory.BudgetedAuction

private theorem sum_eq_pair_of_zero {ι : Type*} [Fintype ι] {f : ι → ℝ} {i j : ι} (hij : i ≠ j)
    (hother : ∀ k, k ≠ i → k ≠ j → f k = 0) :
    ∑ k, f k = f i + f j := by
  classical
  have hi_s := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hj_s := Finset.add_sum_erase (Finset.univ.erase i) f hj_mem
  have hz : ∑ k ∈ (Finset.univ.erase i).erase j, f k = 0 :=
    Finset.sum_eq_zero fun k hk =>
      hother k (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)) (Finset.ne_of_mem_erase hk)
  linarith

private theorem fin_sum_telescope : ∀ {n : ℕ} (f : Fin (n + 1) → ℝ),
    ∑ k : Fin n, (f k.succ - f k.castSucc) = f (Fin.last n) - f 0
  | 0, f => by simp
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have ih := fin_sum_telescope (fun k : Fin (n + 1) => f k.castSucc)
    have hsucc : ∀ k : Fin n, k.castSucc.succ = k.succ.castSucc := fun k => by
      ext; simp
    simp only [hsucc]
    have hlast : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
    have hzero : (0 : Fin (n + 1)).castSucc = 0 := by ext; simp
    rw [hlast]
    rw [hzero] at ih
    linarith

private theorem alloc_eq_zero_of_lt_unconstrained {ι : Type*} [Fintype ι]
    {M : BudgetedMechanism ι} {m : ℝ}
    (hbf : M.IsBudgetFeasibleOnPos) (hir : M.IsIROnPos)
    (hpo : M.IsParetoOptimalOnPos m)
    {θ : ι → BidderType} (hθ : ∀ k, (θ k).IsPos)
    {k a : ι} (hval : (θ k).val < (θ a).val)
    (hunc : (θ a).val * m < (θ a).budget) :
    (M.outcome θ).alloc k = 0 := by
  have hfeas := (hpo θ hθ).1
  have hce := (Outcome.isParetoOptimal_iff (fun r => (hθ r).1.le) hfeas (hbf θ hθ)).mp (hpo θ hθ)
  by_contra hne
  have hpos : 0 < (M.outcome θ).alloc k := lt_of_le_of_ne (hfeas.1 k) (Ne.symm hne)
  have hpay_eq : (M.outcome θ).payment a = (θ a).budget := hce.2 k a hpos hval
  have hxa_le : (M.outcome θ).alloc a ≤ m :=
    (Finset.single_le_sum (fun r _ => hfeas.1 r) (Finset.mem_univ a)).trans hfeas.2
  have hir_a : (M.outcome θ).payment a ≤ (θ a).val * (M.outcome θ).alloc a := by
    have := hir θ hθ a
    dsimp only [Outcome.utility] at this
    linarith
  have hmul : (θ a).val * (M.outcome θ).alloc a ≤ (θ a).val * m :=
    mul_le_mul_of_nonneg_left hxa_le (hθ a).1.le
  linarith

private theorem update_pos {ι : Type*} [DecidableEq ι] {θ : ι → BidderType}
    (hθ : ∀ k, (θ k).IsPos) (i : ι) {b : BidderType} (hb : b.IsPos) :
    ∀ k, (Function.update θ i b k).IsPos := by
  intro k
  by_cases h : k = i
  · subst h; simpa only [Function.update_self] using hb
  · simpa only [Function.update_of_ne h] using hθ k

section Proof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem unconstrained_winner_payment_eq {M : BudgetedMechanism ι} {m : ℝ} (hm : 0 < m)
    (hnn : M.HasNonnegPaymentOnPos) (hbf : M.IsBudgetFeasibleOnPos) (hir : M.IsIROnPos)
    (hpo : M.IsParetoOptimalOnPos m) (hic : M.IsPrivateBudgetDSIC)
    {θ : ι → BidderType} (hθ : ∀ k, (θ k).IsPos)
    {i j : ι} (hij : i ≠ j)
    (hv_i_unc : (θ i).val * m < (θ i).budget)
    (hrest : ∀ k, k ≠ i → k ≠ j → (θ k).val < (θ i).val)
    {t BigB : ℝ} (ht : (θ i).val < t) (hBigB : t * m < BigB) :
    (M.outcome (Function.update θ j ⟨t, BigB⟩)).alloc j = m ∧
      (M.outcome (Function.update θ j ⟨t, BigB⟩)).payment j = (θ i).val * m := by
  have ht_pos : 0 < t := (hθ i).1.trans ht
  have hBigB_pos : 0 < BigB := (mul_pos ht_pos hm).trans hBigB
  have hall_m : ∀ (w Bw : ℝ), (θ i).val < w → w * m < Bw →
      (M.outcome (Function.update θ j ⟨w, Bw⟩)).alloc j = m := by
    intro w Bw hw hBw
    have hw_pos : 0 < w := (hθ i).1.trans hw
    have hBw_pos : 0 < Bw := (mul_pos hw_pos hm).trans hBw
    have hθ' := update_pos hθ j (b := ⟨w, Bw⟩) ⟨hw_pos, hBw_pos⟩
    have hother : ∀ k, k ≠ j → (M.outcome (Function.update θ j ⟨w, Bw⟩)).alloc k = 0 := by
      intro k hkj
      refine alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθ' (a := j) ?_ ?_
      · simp only [Function.update_self, Function.update_of_ne hkj]
        by_cases hki : k = i
        · subst hki; exact hw
        · exact (hrest k hki hkj).trans hw
      · simpa only [Function.update_self] using hBw
    have hce := (Outcome.isParetoOptimal_iff (fun r => (hθ' r).1.le)
      (hpo _ hθ').1 (hbf _ hθ')).mp (hpo _ hθ')
    have hsum : ∑ k, (M.outcome (Function.update θ j ⟨w, Bw⟩)).alloc k = m :=
      (hce.1 ⟨j, by simpa only [Function.update_self] using hw_pos⟩).1
    have hsum_j : ∑ k, (M.outcome (Function.update θ j ⟨w, Bw⟩)).alloc k =
        (M.outcome (Function.update θ j ⟨w, Bw⟩)).alloc j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hz : ∑ k ∈ Finset.univ.erase j, (M.outcome (Function.update θ j ⟨w, Bw⟩)).alloc k = 0 :=
        Finset.sum_eq_zero fun k hk => hother k (Finset.ne_of_mem_erase hk)
      linarith
    linarith
  have hpay_const : ∀ (w₁ B₁ w₂ B₂ : ℝ),
      (θ i).val < w₁ → w₁ * m < B₁ → (θ i).val < w₂ → w₂ * m < B₂ →
      (M.outcome (Function.update θ j ⟨w₁, B₁⟩)).payment j ≤
        (M.outcome (Function.update θ j ⟨w₂, B₂⟩)).payment j := by
    intro w₁ B₁ w₂ B₂ hw₁ hB₁ hw₂ hB₂
    have hB : max B₁ B₂ > 0 := lt_max_of_lt_left ((mul_pos ((hθ i).1.trans hw₁) hm).trans hB₁)
    set Bmax := max B₁ B₂ + 1
    have hBmax_gt₁ : w₁ * m < Bmax := by dsimp only [Bmax]; linarith [le_max_left B₁ B₂]
    have hBmax_gt₂ : w₂ * m < Bmax := by dsimp only [Bmax]; linarith [le_max_right B₁ B₂]
    have hw₁_pos : 0 < w₁ := (hθ i).1.trans hw₁
    have hw₂_pos : 0 < w₂ := (hθ i).1.trans hw₂
    have hB₁_pos : 0 < B₁ := (mul_pos hw₁_pos hm).trans hB₁
    have hB₂_pos : 0 < B₂ := (mul_pos hw₂_pos hm).trans hB₂
    have hBmax_pos : 0 < Bmax := (mul_pos hw₁_pos hm).trans hBmax_gt₁
    have halloc₁ := hall_m w₁ B₁ hw₁ hB₁
    have halloc₂ := hall_m w₂ B₂ hw₂ hB₂
    have hir_le : ∀ w Bw (hw : (θ i).val < w) (hBw : w * m < Bw),
        (M.outcome (Function.update θ j ⟨w, Bw⟩)).payment j ≤ w * m := by
      intro w Bw hw hBw
      have hpos_w : 0 < w := (hθ i).1.trans hw
      have hpos_Bw : 0 < Bw := (mul_pos hpos_w hm).trans hBw
      have hθ' := update_pos hθ j (b := ⟨w, Bw⟩) ⟨hpos_w, hpos_Bw⟩
      have hiru := hir _ hθ' j
      dsimp only [Outcome.utility] at hiru
      rw [Function.update_self, hall_m w Bw hw hBw] at hiru
      linarith
    have hle_max : ∀ w Bw (hw : (θ i).val < w) (hBw : w * m < Bw) (hBw_le : Bw ≤ Bmax),
        (M.outcome (Function.update θ j ⟨w, Bw⟩)).payment j =
          (M.outcome (Function.update θ j ⟨w, Bmax⟩)).payment j := by
      intro w Bw hw hBw hBw_le
      have hpos_w : 0 < w := (hθ i).1.trans hw
      have hpos_Bw : 0 < Bw := (mul_pos hpos_w hm).trans hBw
      have hBmax_w : w * m < Bmax := hBw.trans_le hBw_le
      have hθw := update_pos hθ j (b := ⟨w, Bw⟩) ⟨hpos_w, hpos_Bw⟩
      have hθM := update_pos hθ j (b := ⟨w, Bmax⟩) ⟨hpos_w, hBmax_pos⟩
      have h12 : (M.outcome (Function.update θ j ⟨w, Bmax⟩)).payment j ≤ Bw :=
        (hir_le w Bmax hw hBmax_w).trans hBw.le
      have h21 : (M.outcome (Function.update θ j ⟨w, Bw⟩)).payment j ≤ Bmax :=
        (hbf _ hθw j).trans (by simp only [Function.update_self]; exact hBw_le)
      have hic1 := hic (Function.update θ j ⟨w, Bw⟩) hθw j ⟨w, Bmax⟩ ⟨hpos_w, hBmax_pos⟩
        (by simpa only [Function.update_idem, Function.update_self] using h12)
      have hic2 := hic (Function.update θ j ⟨w, Bmax⟩) hθM j ⟨w, Bw⟩ ⟨hpos_w, hpos_Bw⟩
        (by simpa only [Function.update_idem, Function.update_self] using h21)
      simp only [Outcome.utility, Function.update_idem, Function.update_self] at hic1 hic2
      rw [hall_m w Bw hw hBw, hall_m w Bmax hw hBmax_w] at hic1 hic2
      linarith
    have h1 := hle_max w₁ B₁ hw₁ hB₁ (by dsimp only [Bmax]; linarith [le_max_left B₁ B₂])
    have h2 := hle_max w₂ B₂ hw₂ hB₂ (by dsimp only [Bmax]; linarith [le_max_right B₁ B₂])
    have hθM₁ := update_pos hθ j (b := ⟨w₁, Bmax⟩) ⟨hw₁_pos, hBmax_pos⟩
    have hθM₂ := update_pos hθ j (b := ⟨w₂, Bmax⟩) ⟨hw₂_pos, hBmax_pos⟩
    have hic12 := hic (Function.update θ j ⟨w₁, Bmax⟩) hθM₁ j ⟨w₂, Bmax⟩ ⟨hw₂_pos, hBmax_pos⟩
      (by
        simp only [Function.update_idem, Function.update_self]
        exact (hir_le w₂ Bmax hw₂ hBmax_gt₂).trans hBmax_gt₂.le)
    simp only [Outcome.utility, Function.update_idem, Function.update_self] at hic12
    rw [hall_m w₁ Bmax hw₁ hBmax_gt₁, hall_m w₂ Bmax hw₂ hBmax_gt₂] at hic12
    linarith
  refine ⟨hall_m t BigB ht hBigB, le_antisymm ?_ ?_⟩
  · -- Upper bound `payment j ≤ (θ i).val * m` by taking `w₂ = (θ i).val + ε → (θ i).val`.
    by_contra hgt
    push Not at hgt
    let p := (M.outcome (Function.update θ j ⟨t, BigB⟩)).payment j
    have hgap : 0 < p - (θ i).val * m := sub_pos.mpr hgt
    let w₂ := (θ i).val + (p - (θ i).val * m) / (2 * m)
    have hw₂ : (θ i).val < w₂ := by
      have : 0 < (p - (θ i).val * m) / (2 * m) := div_pos hgap (by positivity)
      linarith
    have hw₂_pos : 0 < w₂ := (hθ i).1.trans hw₂
    let B₂ := w₂ * m + 1
    have hB₂ : w₂ * m < B₂ := by dsimp only [B₂]; linarith
    have hθ₂ := update_pos hθ j (b := ⟨w₂, B₂⟩) ⟨hw₂_pos, (mul_pos hw₂_pos hm).trans hB₂⟩
    have hle_p := hpay_const t BigB w₂ B₂ ht hBigB hw₂ hB₂
    have hiru := hir _ hθ₂ j
    dsimp only [Outcome.utility] at hiru
    rw [Function.update_self, hall_m w₂ B₂ hw₂ hB₂] at hiru
    have hw₂_mul : w₂ * m = (θ i).val * m + (p - (θ i).val * m) / 2 := by
      dsimp only [w₂]
      field_simp [hm.ne']
    linarith
  · -- Lower bound `(θ i).val * m ≤ payment j` via deviation from `s < (θ i).val`.
    by_contra hlt
    push Not at hlt
    let p := (M.outcome (Function.update θ j ⟨t, BigB⟩)).payment j
    have hp_nn : 0 ≤ p := hnn _ (update_pos hθ j ⟨ht_pos, hBigB_pos⟩) j
    have hgap : 0 < (θ i).val * m - p := sub_pos.mpr hlt
    let s := max ((θ i).val / 2) ((θ i).val - ((θ i).val * m - p) / (2 * m))
    have hs_pos : 0 < s := lt_max_of_lt_left (half_pos (hθ i).1)
    have hs_lt : s < (θ i).val := by
      refine max_lt (half_lt_self (hθ i).1) ?_
      have : 0 < ((θ i).val * m - p) / (2 * m) := div_pos hgap (by positivity)
      linarith
    have hsm_gt : p < s * m := by
      have hge : (θ i).val - ((θ i).val * m - p) / (2 * m) ≤ s := le_max_right _ _
      have hcalc : ((θ i).val - ((θ i).val * m - p) / (2 * m)) * m =
          (θ i).val * m - ((θ i).val * m - p) / 2 := by
        field_simp [hm.ne']
      have hmul := mul_le_mul_of_nonneg_right hge hm.le
      linarith
    let Bs := max (p + 1) 1
    have hBs_pos : 0 < Bs := lt_max_of_lt_right zero_lt_one
    have hθs := update_pos hθ j (b := ⟨s, Bs⟩) ⟨hs_pos, hBs_pos⟩
    have hxs0 : (M.outcome (Function.update θ j ⟨s, Bs⟩)).alloc j = 0 := by
      refine alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθs (a := i) ?_ ?_
      · simp only [Function.update_self, Function.update_of_ne hij]; exact hs_lt
      · simpa only [Function.update_of_ne hij] using hv_i_unc
    have hps0 : (M.outcome (Function.update θ j ⟨s, Bs⟩)).payment j = 0 := by
      have h1 : 0 ≤ (M.outcome (Function.update θ j ⟨s, Bs⟩)).payment j := hnn _ hθs j
      have h2 := hir _ hθs j
      simp only [Outcome.utility, Function.update_self, hxs0, mul_zero, zero_sub] at h2
      linarith
    have hic_dev := hic (Function.update θ j ⟨s, Bs⟩) hθs j ⟨t, BigB⟩ ⟨ht_pos, hBigB_pos⟩
      (by
        simp only [Function.update_idem, Function.update_self]
        exact le_trans (by linarith : p ≤ p + 1) (le_max_left _ _))
    simp only [Outcome.utility, Function.update_idem, Function.update_self,
      hall_m t BigB ht hBigB, hxs0, hps0, mul_zero, sub_zero] at hic_dev
    linarith

/-- **Unique allocation & payment pinning** ([DobzinskiLaviNisan2012], primary PDF not inspected):
in any feasible, nonnegative-paying, budget-feasible, individually rational, Pareto-optimal, and
private-budget DSIC mechanism for supply `m > 0`, when bidder `i` is unconstrained
(`(θ i).val * m < (θ i).budget`), bidder `j ≠ i` has strictly higher value `(θ i).val < (θ j).val`
and a binding budget `(θ j).budget ≤ (θ i).val * m`, and every other bidder `k ∉ {i, j}` has value
strictly below `(θ i).val`, then:
* `alloc j = (θ j).budget / (θ i).val`,
* `alloc i = m - (θ j).budget / (θ i).val`,
* all other bidders `k ∉ {i, j}` receive `0`, and
* when `(θ j).budget < (θ i).val * m`, bidder `j`'s budget is exhausted
  (`payment j = (θ j).budget`).
-/
theorem pinning_of_isPrivateBudgetDSIC_isParetoOptimal {M : BudgetedMechanism ι} {m : ℝ}
    (hm : 0 < m)
    (hnn : M.HasNonnegPaymentOnPos) (hbf : M.IsBudgetFeasibleOnPos) (hir : M.IsIROnPos)
    (hpo : M.IsParetoOptimalOnPos m) (hic : M.IsPrivateBudgetDSIC)
    {θ : ι → BidderType} (hθ : ∀ k, (θ k).IsPos)
    {i j : ι} (hij : i ≠ j)
    (hv_i_unc : (θ i).val * m < (θ i).budget)
    (hrest : ∀ k, k ≠ i → k ≠ j → (θ k).val < (θ i).val)
    (hlt_ij : (θ i).val < (θ j).val)
    (hbind : (θ j).budget ≤ (θ i).val * m) :
    (M.outcome θ).alloc j = (θ j).budget / (θ i).val ∧
      (M.outcome θ).alloc i = m - (θ j).budget / (θ i).val ∧
      (∀ k, k ≠ i → k ≠ j → (M.outcome θ).alloc k = 0) ∧
      ((θ j).budget < (θ i).val * m → (M.outcome θ).payment j = (θ j).budget) := by
  have hv_i_pos : 0 < (θ i).val := (hθ i).1
  have hB_j_pos : 0 < (θ j).budget := (hθ j).2
  have hfeas := (hpo θ hθ).1
  have hother0 : ∀ k, k ≠ i → k ≠ j → (M.outcome θ).alloc k = 0 := fun k hki hkj =>
    alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθ (a := i) (hrest k hki hkj) hv_i_unc
  have hsum_eq : (M.outcome θ).alloc i + (M.outcome θ).alloc j = m := by
    have hce := (Outcome.isParetoOptimal_iff (fun r => (hθ r).1.le)
      hfeas (hbf θ hθ)).mp (hpo θ hθ)
    have hsum : ∑ k, (M.outcome θ).alloc k = m := (hce.1 ⟨i, hv_i_pos⟩).1
    have hsplit : ∑ k, (M.outcome θ).alloc k = (M.outcome θ).alloc i + (M.outcome θ).alloc j :=
      sum_eq_pair_of_zero hij hother0
    linarith
  -- Helper: `alloc j ≤ budget / v_i` for `w > v_i` at budget `B_j`, via `(v_i + ε, BigB)`.
  have hupper : ∀ (w : ℝ), (θ i).val < w →
      (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j ≤ (θ j).budget / (θ i).val := by
    intro w hw
    have hw_pos : 0 < w := hv_i_pos.trans hw
    have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hw_pos, hB_j_pos⟩
    have hpj_le : (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j ≤ (θ j).budget := by
      simpa only [Function.update_self] using hbf _ hθw j
    rw [le_div_iff₀ hv_i_pos]
    by_contra hgt
    push Not at hgt
    let x := (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j
    have hgap : 0 < x * (θ i).val - (θ j).budget := sub_pos.mpr hgt
    have hx_le : x ≤ m :=
      (Finset.single_le_sum (fun r _ => (hpo _ hθw).1.1 r) (Finset.mem_univ j)).trans
        (hpo _ hθw).1.2
    let ε := (x * (θ i).val - (θ j).budget) / (2 * m)
    have hε_pos : 0 < ε := div_pos hgap (by positivity)
    let t := (θ i).val + ε
    let BigB := max (t * m + 1) ((θ j).budget + 1)
    have hBigB_gt : t * m < BigB := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hθ_t := update_pos hθ j (b := ⟨t, BigB⟩)
      ⟨hv_i_pos.trans (by linarith), (mul_pos (by linarith) hm).trans hBigB_gt⟩
    have ⟨hxt, hpt⟩ := unconstrained_winner_payment_eq hm hnn hbf hir hpo hic hθ hij
      hv_i_unc hrest (t := t) (BigB := BigB) (by linarith) hBigB_gt
    have hic_dev := hic (Function.update θ j ⟨t, BigB⟩) hθ_t j ⟨w, (θ j).budget⟩
      ⟨hw_pos, hB_j_pos⟩ (by
        simp only [Function.update_idem, Function.update_self]
        exact hpj_le.trans (le_trans (by linarith) (le_max_right _ _)))
    simp only [Outcome.utility, Function.update_idem, Function.update_self, hxt, hpt] at hic_dev
    have hx_nn : 0 ≤ x := (hpo _ hθw).1.1 j
    have hεm : ε * m = (x * (θ i).val - (θ j).budget) / 2 := by
      dsimp only [ε]; field_simp [hm.ne']
    have htm : t * m - (θ i).val * m = (x * (θ i).val - (θ j).budget) / 2 := by
      dsimp only [t]; linarith
    have htx : t * x = (θ i).val * x + ε * x := by dsimp only [t]; ring
    have : 0 ≤ ε * x := mul_nonneg hε_pos.le hx_nn
    linarith
  have hup_self : (M.outcome θ).alloc j ≤ (θ j).budget / (θ i).val := by
    have h := hupper (θ j).val hlt_ij
    simpa only [Function.update_eq_self] using h
  -- Whenever bidder `j` reports `w > v_i` with budget `B_j` and receives `< m`, its budget binds.
  have hpay_if_lt : ∀ w, (θ i).val < w →
      (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j < m →
      (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j = (θ j).budget := by
    intro w hw hltw
    have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hv_i_pos.trans hw, hB_j_pos⟩
    have hother_w : ∀ k, k ≠ i → k ≠ j →
        (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc k = 0 := fun k hki hkj =>
      alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθw (a := i)
        (by simpa only [Function.update_of_ne hkj, Function.update_of_ne hij] using hrest k hki hkj)
        (by simpa only [Function.update_of_ne hij] using hv_i_unc)
    have hce_w := (Outcome.isParetoOptimal_iff (fun r => (hθw r).1.le)
      (hpo _ hθw).1 (hbf _ hθw)).mp (hpo _ hθw)
    have hsum_w : ∑ k, (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc k = m :=
      (hce_w.1 ⟨i, by simpa only [Function.update_of_ne hij] using hv_i_pos⟩).1
    have hsplit := sum_eq_pair_of_zero hij hother_w
    have hxi_pos : 0 < (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc i := by linarith
    simpa only [Function.update_self] using hce_w.2 i j hxi_pos
      (by simp only [Function.update_of_ne hij, Function.update_self]; exact hw)
  -- Split between strict binding `(θ j).budget < (θ i).val * m` and boundary equality.
  rcases lt_or_eq_of_le hbind with hstrict | heq
  · have hpay_bind : ∀ (w : ℝ), (θ i).val < w →
        (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j = (θ j).budget :=
      fun w hw => hpay_if_lt w hw
        (lt_of_le_of_lt (hupper w hw) ((div_lt_iff₀ hv_i_pos).mpr (by linarith)))
    have hx_const : ∀ (w : ℝ), (θ i).val < w →
        (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j = (M.outcome θ).alloc j := by
      intro w hw
      have hw_pos : 0 < w := hv_i_pos.trans hw
      have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hw_pos, hB_j_pos⟩
      have hp_w := hpay_bind w hw
      have hp_s : (M.outcome θ).payment j = (θ j).budget := by
        have h := hpay_bind (θ j).val hlt_ij
        simpa only [Function.update_eq_self] using h
      have h1 := hic θ hθ j ⟨w, (θ j).budget⟩ ⟨hw_pos, hB_j_pos⟩ (by linarith)
      have h2 := hic (Function.update θ j ⟨w, (θ j).budget⟩) hθw j (θ j) (hθ j)
        (by
          simp only [Function.update_idem, Function.update_eq_self, Function.update_self]
          linarith)
      simp only [Outcome.utility, Function.update_idem, Function.update_eq_self,
        Function.update_self] at h1 h2
      have hxj_eq : (θ j).val * (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j ≤
          (θ j).val * (M.outcome θ).alloc j := by linarith
      have hxw_eq : w * (M.outcome θ).alloc j ≤
          w * (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j := by linarith
      exact le_antisymm
        (le_of_mul_le_mul_left hxj_eq (hθ j).1) (le_of_mul_le_mul_left hxw_eq hw_pos)
    have hlow : (θ j).budget / (θ i).val ≤ (M.outcome θ).alloc j := by
      rw [div_le_iff₀ hv_i_pos]
      by_contra hlt
      push Not at hlt
      let x := (M.outcome θ).alloc j
      have hgap : 0 < (θ j).budget - x * (θ i).val := sub_pos.mpr hlt
      have hx_nn : 0 ≤ x := hfeas.1 j
      have hx_pos : 0 < x := by
        by_contra hx0
        have hx0' : x = 0 := le_antisymm (le_of_not_gt hx0) hx_nn
        have hiru := hir θ hθ j
        dsimp only [Outcome.utility] at hiru
        have hps := hpay_bind (θ j).val hlt_ij
        rw [Function.update_eq_self] at hps
        have hx0'' : (M.outcome θ).alloc j = 0 := hx0'
        rw [hx0'', mul_zero, zero_sub] at hiru
        linarith
      let w := (θ i).val + ((θ j).budget - x * (θ i).val) / (2 * x)
      have hw : (θ i).val < w := by
        have : 0 < ((θ j).budget - x * (θ i).val) / (2 * x) := div_pos hgap (by positivity)
        linarith
      have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hv_i_pos.trans hw, hB_j_pos⟩
      have hiru := hir _ hθw j
      simp only [Outcome.utility, Function.update_self, hx_const w hw, hpay_bind w hw] at hiru
      have hwx : w * x = x * (θ i).val + ((θ j).budget - x * (θ i).val) / 2 := by
        dsimp only [w]; field_simp [hx_pos.ne']
      linarith
    have hxj : (M.outcome θ).alloc j = (θ j).budget / (θ i).val := le_antisymm hup_self hlow
    have hpj : (M.outcome θ).payment j = (θ j).budget := by
      have h := hpay_bind (θ j).val hlt_ij
      simpa only [Function.update_eq_self] using h
    exact ⟨hxj, by linarith, hother0, fun _ => hpj⟩
  · -- Boundary case `(θ j).budget = (θ i).val * m`: then `budget / v_i = m`.
    have hdiv_eq : (θ j).budget / (θ i).val = m := by
      rw [heq, mul_div_cancel_left₀ m hv_i_pos.ne']
    have hxj_eq : (M.outcome θ).alloc j = m := by
      by_contra hne
      have hxj_lt : (M.outcome θ).alloc j < m :=
        lt_of_le_of_ne (hdiv_eq ▸ hup_self) hne
      have hxi_pos : 0 < (M.outcome θ).alloc i := by linarith
      have hce := (Outcome.isParetoOptimal_iff (fun r => (hθ r).1.le)
        hfeas (hbf θ hθ)).mp (hpo θ hθ)
      have hpj_eq : (M.outcome θ).payment j = (θ j).budget := hce.2 i j hxi_pos hlt_ij
      have hic_ge : ∀ w, (θ i).val < w →
          (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j ≤ (M.outcome θ).alloc j := by
        intro w hw
        have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hv_i_pos.trans hw, hB_j_pos⟩
        have hp_le : (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j ≤
            (θ j).budget := by
          simpa only [Function.update_self] using hbf _ hθw j
        have h1 := hic θ hθ j ⟨w, (θ j).budget⟩ ⟨hv_i_pos.trans hw, hB_j_pos⟩ hp_le
        dsimp only [Outcome.utility] at h1
        rw [hpj_eq] at h1
        have : (θ j).val * (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j ≤
            (θ j).val * (M.outcome θ).alloc j := by linarith
        exact le_of_mul_le_mul_left this (hθ j).1
      -- Pick `w` just above `v_i` with `w * alloc j < v_i * m = budget`.
      have hxj_pos : 0 < (M.outcome θ).alloc j := by
        by_contra hx0
        have hx0' : (M.outcome θ).alloc j = 0 := le_antisymm (le_of_not_gt hx0) (hfeas.1 j)
        have hiru := hir θ hθ j
        dsimp only [Outcome.utility] at hiru
        rw [hx0', mul_zero, zero_sub] at hiru
        linarith
      let w := (θ i).val + ((θ i).val * (m - (M.outcome θ).alloc j)) / (2 * (M.outcome θ).alloc j)
      have hw : (θ i).val < w := by
        have : 0 < ((θ i).val * (m - (M.outcome θ).alloc j)) / (2 * (M.outcome θ).alloc j) :=
          div_pos (mul_pos hv_i_pos (sub_pos.mpr hxj_lt)) (by positivity)
        linarith
      have hxw_le := hic_ge w hw
      have hpw := hpay_if_lt w hw (lt_of_le_of_lt hxw_le hxj_lt)
      have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hv_i_pos.trans hw, hB_j_pos⟩
      have hiru := hir _ hθw j
      simp only [Outcome.utility, Function.update_self, hpw] at hiru
      have hwm : w * (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j ≤
          w * (M.outcome θ).alloc j :=
        mul_le_mul_of_nonneg_left hxw_le (hv_i_pos.trans hw).le
      have hcalc : w * (M.outcome θ).alloc j =
          (θ i).val * (M.outcome θ).alloc j + (θ i).val * (m - (M.outcome θ).alloc j) / 2 := by
        dsimp only [w]
        field_simp [hxj_pos.ne']
      have hlt_b : (θ i).val * (M.outcome θ).alloc j + (θ i).val * (m - (M.outcome θ).alloc j) / 2 <
          (θ i).val * m := by nlinarith
      linarith
    exact ⟨hxj_eq.trans hdiv_eq.symm, by linarith, hother0, fun h => absurd heq h.ne⟩

/-- Harmonic telescoping upper bound `∑_{r=6}^{14} 1 / r = 348911 / 360360 < 1`. -/
private theorem sum_inv_six_to_fourteen_lt_one :
    (∑ k : Fin 9, (1 : ℝ) / ((k.val : ℝ) + 6)) < 1 := by
  have hsum : ∑ k : Fin 9, (1 : ℝ) / ((k.val : ℝ) + 6) =
      1 / 6 + 1 / 7 + 1 / 8 + 1 / 9 + 1 / 10 + 1 / 11 + 1 / 12 + 1 / 13 + 1 / 14 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
    norm_num
  rw [hsum]
  norm_num

/-- At `(i, j)` with opponent `j` fixed at `⟨100 / m, 1⟩` and all other bidders `< 1 / m`,
reporting `⟨5 / (2 * m), 10⟩` grants `i` allocation `(3 / 5) * m` for a strictly budget-feasible
payment `< 1`. -/
private theorem payoff_at_overreport_budget {M : BudgetedMechanism ι} {m : ℝ} (hm : 0 < m)
    (hnn : M.HasNonnegPaymentOnPos) (hbf : M.IsBudgetFeasibleOnPos) (hir : M.IsIROnPos)
    (hpo : M.IsParetoOptimalOnPos m) (hic : M.IsPrivateBudgetDSIC)
    {i j : ι} (hij : i ≠ j) (θbase : ι → BidderType)
    (hbase_i : θbase i = ⟨100 / m, 1⟩) (hbase_j : θbase j = ⟨100 / m, 1⟩)
    (hbase_rest : ∀ k, k ≠ i → k ≠ j → θbase k = ⟨1 / (2 * m), 1⟩) :
    (M.outcome (Function.update θbase i ⟨5 / (2 * m), 10⟩)).alloc i = (3 / 5) * m ∧
      (M.outcome (Function.update θbase i ⟨5 / (2 * m), 10⟩)).payment i < 1 := by
  let t : Fin 10 → ℝ := fun k => ((k.val : ℝ) + 6) / (6 * m)
  let prof : Fin 10 → (ι → BidderType) := fun k => Function.update θbase i ⟨t k, 10⟩
  have hprof_pos : ∀ k r, (prof k r).IsPos := by
    intro k r
    dsimp only [prof]
    by_cases hri : r = i
    · subst hri
      rw [Function.update_self]
      refine ⟨div_pos (by positivity) (by positivity), by norm_num⟩
    · rw [Function.update_of_ne hri]
      by_cases hrj : r = j
      · subst hrj; rw [hbase_j]; exact ⟨div_pos (by norm_num) hm, zero_lt_one⟩
      · rw [hbase_rest r hri hrj]; exact ⟨div_pos zero_lt_one (by positivity), zero_lt_one⟩
  have ht_bounds : ∀ k : Fin 10, 1 / m ≤ t k ∧ t k ≤ 5 / (2 * m) := by
    intro k
    have hk_le : (k.val : ℝ) ≤ 9 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    have hk_nn : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    refine ⟨?_, ?_⟩
    · dsimp only [t]
      rw [div_le_div_iff₀ hm (by positivity)]
      nlinarith
    · dsimp only [t]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have halloc_i : ∀ k : Fin 10, (M.outcome (prof k)).alloc i = m - 1 / t k := by
    intro k
    have hkt_lo := (ht_bounds k).1
    have hkt_hi := (ht_bounds k).2
    have hpin := pinning_of_isPrivateBudgetDSIC_isParetoOptimal hm hnn hbf hir hpo hic
      (hprof_pos k) hij (by
        simp only [prof, Function.update_self]
        calc
          t k * m ≤ 5 / (2 * m) * m := mul_le_mul_of_nonneg_right hkt_hi hm.le
          _ = 5 / 2 := by field_simp [hm.ne']
          _ < 10 := by norm_num)
      (by
        intro r hri hrj
        simp only [prof, Function.update_self, Function.update_of_ne hri, hbase_rest r hri hrj]
        have : 1 / (2 * m) < 1 / m := by
          rw [div_lt_div_iff₀ (by positivity) hm]
          linarith
        linarith)
      (by
        simp only [prof, Function.update_self, Function.update_of_ne hij.symm, hbase_j]
        have : 5 / (2 * m) < 100 / m := by
          rw [div_lt_div_iff₀ (by positivity) hm]; linarith
        linarith)
      (by
        simp only [prof, Function.update_self, Function.update_of_ne hij.symm, hbase_j]
        have : (1 : ℝ) = (1 / m) * m := by field_simp [hm.ne']
        calc
          (1 : ℝ) = (1 / m) * m := this
          _ ≤ t k * m := mul_le_mul_of_nonneg_right hkt_lo hm.le)
    simpa only [prof, Function.update_self, Function.update_of_ne hij.symm, hbase_j] using hpin.2.1
  have hp0 : (M.outcome (prof 0)).payment i = 0 := by
    have ht0 : t 0 = 1 / m := by
      dsimp only [t]
      simp only [Fin.val_zero, Nat.cast_zero, zero_add]
      field_simp [hm.ne']
    have ha0 : (M.outcome (prof 0)).alloc i = 0 := by
      rw [halloc_i 0, ht0]; field_simp [hm.ne']; ring
    have h1 := hnn _ (hprof_pos 0) i
    have h2 := hir _ (hprof_pos 0) i
    simp only [Outcome.utility, ha0, mul_zero, zero_sub] at h2
    linarith
  have hstep : ∀ k : Fin 9,
      (M.outcome (prof k.succ)).payment i - (M.outcome (prof k.castSucc)).payment i ≤
        1 / ((k.val : ℝ) + 6) := by
    intro k
    have hp_prev_le : (M.outcome (prof k.castSucc)).payment i ≤ 10 := by
      have h := hbf _ (hprof_pos k.castSucc) i
      simpa only [prof, Function.update_self] using h
    have hic_k := hic (prof k.succ) (hprof_pos k.succ) i ⟨t k.castSucc, 10⟩
      ⟨div_pos (by positivity) (by positivity), by norm_num⟩
      (by
        dsimp only [prof] at hp_prev_le ⊢
        simp only [Function.update_idem, Function.update_self]
        exact hp_prev_le)
    have hupd : Function.update (prof k.succ) i ⟨t k.castSucc, 10⟩ = prof k.castSucc := by
      dsimp only [prof]; rw [Function.update_idem]
    rw [hupd] at hic_k
    dsimp only [Outcome.utility] at hic_k
    simp only [prof, Function.update_self] at hic_k
    rw [halloc_i k.succ, halloc_i k.castSucc] at hic_k
    have hdiff : t k.succ * ((m - 1 / t k.succ) - (m - 1 / t k.castSucc)) =
        1 / ((k.val : ℝ) + 6) := by
      dsimp only [t]
      simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      have hk1 : ((k.val : ℝ) + 6) ≠ 0 := by positivity
      have hk2 : ((k.val : ℝ) + 1 + 6) ≠ 0 := by positivity
      field_simp [hm.ne', hk1, hk2]
      ring
    linarith
  have ht9 : t (Fin.last 9) = 5 / (2 * m) := by
    dsimp only [t]
    simp only [Fin.val_last]
    field_simp [hm.ne']
    norm_num
  have hprof9 : prof (Fin.last 9) = Function.update θbase i ⟨5 / (2 * m), 10⟩ := by
    dsimp only [prof]; rw [ht9]
  have htel : (M.outcome (prof (Fin.last 9))).payment i - (M.outcome (prof 0)).payment i =
      ∑ k : Fin 9,
        ((M.outcome (prof k.succ)).payment i - (M.outcome (prof k.castSucc)).payment i) :=
    (fin_sum_telescope (fun k : Fin 10 => (M.outcome (prof k)).payment i)).symm
  have hsum_le : (M.outcome (prof (Fin.last 9))).payment i < 1 := by
    have hbound : ∑ k : Fin 9,
        ((M.outcome (prof k.succ)).payment i - (M.outcome (prof k.castSucc)).payment i) ≤
          ∑ k : Fin 9, (1 : ℝ) / ((k.val : ℝ) + 6) :=
      Finset.sum_le_sum fun k _ => hstep k
    linarith [sum_inv_six_to_fourteen_lt_one]
  refine ⟨?_, by rwa [← hprof9]⟩
  rw [← hprof9, halloc_i (Fin.last 9), ht9]
  field_simp [hm.ne']
  norm_num

/-- **Dobzinski–Lavi–Nisan Impossibility Theorem** ([DobzinskiLaviNisan2012], primary PDF not
inspected; theorem/page locators unverified): for every finite set of `n ≥ 2` bidders and every
strictly positive divisible supply `m > 0`, **no** deterministic mechanism over strictly positive
`(val, budget)` profiles satisfies feasibility, nonnegative payments, budget feasibility,
individual rationality, Pareto optimality, and private-budget dominant-strategy incentive
compatibility simultaneously. -/
theorem not_exists_privateBudgetDSIC_isParetoOptimal {m : ℝ} (hm : 0 < m)
    (hcard : 2 ≤ Fintype.card ι) :
    ¬ ∃ M : BudgetedMechanism ι,
      M.IsFeasibleOnPos m ∧
      M.HasNonnegPaymentOnPos ∧
      M.IsBudgetFeasibleOnPos ∧
      M.IsIROnPos ∧
      M.IsParetoOptimalOnPos m ∧
      M.IsPrivateBudgetDSIC := by
  rintro ⟨M, hfeas, hnn, hbf, hir, hpo, hic⟩
  have hcard_gt : 1 < (Finset.univ : Finset ι).card := by
    rw [Finset.card_univ]; omega
  obtain ⟨i₀, -, i₁, -, hne⟩ := Finset.one_lt_card.mp hcard_gt
  let θstar : ι → BidderType := fun k =>
    if k = i₀ ∨ k = i₁ then ⟨100 / m, 1⟩ else ⟨1 / (2 * m), 1⟩
  have hθ_pos : ∀ k, (θstar k).IsPos := by
    intro k
    dsimp only [θstar]
    split_ifs
    · exact ⟨div_pos (by norm_num) hm, zero_lt_one⟩
    · exact ⟨div_pos zero_lt_one (by positivity), zero_lt_one⟩
  have h0_eq : θstar i₀ = ⟨100 / m, 1⟩ := by simp [θstar]
  have h1_eq : θstar i₁ = ⟨100 / m, 1⟩ := by simp [θstar]
  have hrest_eq : ∀ k, k ≠ i₀ → k ≠ i₁ → θstar k = ⟨1 / (2 * m), 1⟩ := fun k h0 h1 => by
    simp [θstar, h0, h1]
  have ⟨hx0, hp0⟩ := payoff_at_overreport_budget hm hnn hbf hir hpo hic hne θstar
    h0_eq h1_eq hrest_eq
  have ⟨hx1, hp1⟩ := payoff_at_overreport_budget hm hnn hbf hir hpo hic hne.symm θstar
    h1_eq h0_eq (fun k h1 h0 => hrest_eq k h0 h1)
  have hdev_pos : (⟨5 / (2 * m), 10⟩ : BidderType).IsPos :=
    ⟨div_pos (by norm_num) (by positivity), by norm_num⟩
  have hic0 := hic θstar hθ_pos i₀ ⟨5 / (2 * m), 10⟩ hdev_pos
    (by simpa only [h0_eq] using hp0.le)
  have hic1 := hic θstar hθ_pos i₁ ⟨5 / (2 * m), 10⟩ hdev_pos
    (by simpa only [h1_eq] using hp1.le)
  dsimp only [Outcome.utility] at hic0 hic1
  rw [h0_eq, hx0] at hic0
  rw [h1_eq, hx1] at hic1
  have h100_mul : (100 / m) * (3 / 5 * m) = 60 := by field_simp [hm.ne']; ring
  rw [h100_mul] at hic0 hic1
  have hp0_nn : 0 ≤ (M.outcome θstar).payment i₀ := hnn θstar hθ_pos i₀
  have hp1_nn : 0 ≤ (M.outcome θstar).payment i₁ := hnn θstar hθ_pos i₁
  have hpair_sub : ({i₀, i₁} : Finset ι) ⊆ Finset.univ := Finset.subset_univ _
  have halloc_sum : (M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁ ≤ m := by
    calc
      (M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁
          = ∑ k ∈ ({i₀, i₁} : Finset ι), (M.outcome θstar).alloc k := by
              rw [Finset.sum_pair hne]
      _ ≤ ∑ k, (M.outcome θstar).alloc k :=
            Finset.sum_le_sum_of_subset_of_nonneg hpair_sub fun k _ _ => (hfeas θstar hθ_pos).1 k
      _ ≤ m := (hfeas θstar hθ_pos).2
  have h100_bound :
      (100 / m) * ((M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁) ≤ 100 := by
    calc
      (100 / m) * ((M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁)
          ≤ (100 / m) * m := mul_le_mul_of_nonneg_left halloc_sum (div_nonneg (by norm_num) hm.le)
      _ = 100 := by field_simp [hm.ne']
  linarith

end Proof

end Cslib.GameTheory.BudgetedAuction

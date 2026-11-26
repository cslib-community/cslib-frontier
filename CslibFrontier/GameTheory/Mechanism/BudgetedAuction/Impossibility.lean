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
  rw [← Finset.sum_subset (Finset.subset_univ {i, j}) fun k _ hk => ?_, Finset.sum_pair hij]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact hother k hk.1 hk.2

private theorem fin_sum_telescope : ∀ {n : ℕ} (f : Fin (n + 1) → ℝ),
    ∑ k : Fin n, (f k.succ - f k.castSucc) = f (Fin.last n) - f 0
  | 0, _ => by simp
  | n + 1, f => by
    have ih := fin_sum_telescope fun k : Fin (n + 1) => f k.castSucc
    have hsucc (k : Fin n) : k.castSucc.succ = k.succ.castSucc := rfl
    rw [Fin.sum_univ_castSucc]
    simp only [hsucc, Fin.castSucc_zero, Fin.succ_last] at ih ⊢
    linarith [ih]

private theorem payment_le_of_ir {ι : Type*} {M : BudgetedMechanism ι} (hir : M.IsIROnPos)
    {θ : ι → BidderType} (hθ : ∀ k, (θ k).IsPos) (k : ι) :
    (M.outcome θ).payment k ≤ (θ k).val * (M.outcome θ).alloc k := by
  linarith [show 0 ≤ (θ k).val * (M.outcome θ).alloc k - (M.outcome θ).payment k from hir θ hθ k]

private theorem alloc_le_of_po {ι : Type*} [Fintype ι] {M : BudgetedMechanism ι} {m : ℝ}
    (hpo : M.IsParetoOptimalOnPos m) {θ : ι → BidderType} (hθ : ∀ k, (θ k).IsPos) (k : ι) :
    (M.outcome θ).alloc k ≤ m :=
  (Finset.single_le_sum (fun r _ => (hpo θ hθ).1.1 r) (Finset.mem_univ k)).trans (hpo θ hθ).1.2

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
  have hpay_eq := hce.2 k a (lt_of_le_of_ne (hfeas.1 k) (Ne.symm hne)) hval
  linarith [payment_le_of_ir hir hθ a,
    mul_le_mul_of_nonneg_left (alloc_le_of_po hpo hθ a) (hθ a).1.le]

private theorem update_pos {ι : Type*} [DecidableEq ι] {θ : ι → BidderType}
    (hθ : ∀ k, (θ k).IsPos) (i : ι) {b : BidderType} (hb : b.IsPos) :
    ∀ k, (Function.update θ i b k).IsPos := fun k => by
  by_cases h : k = i <;> simp [h, hb, hθ k]

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
  have hall_m (w Bw : ℝ) (hw : (θ i).val < w) (hBw : w * m < Bw) :
      (M.outcome (Function.update θ j ⟨w, Bw⟩)).alloc j = m := by
    have hw_pos : 0 < w := (hθ i).1.trans hw
    have hθ' := update_pos hθ j (b := ⟨w, Bw⟩) ⟨hw_pos, (mul_pos hw_pos hm).trans hBw⟩
    have hce := (Outcome.isParetoOptimal_iff (fun r => (hθ' r).1.le)
      (hpo _ hθ').1 (hbf _ hθ')).mp (hpo _ hθ')
    rw [← (hce.1 ⟨j, by simpa only [Function.update_self] using hw_pos⟩).1]
    refine (Finset.sum_eq_single j (fun k _ hkj => ?_) (by simp)).symm
    refine alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθ' (a := j) ?_
      (by simpa only [Function.update_self] using hBw)
    simpa only [Function.update_self, Function.update_of_ne hkj] using
      (eq_or_ne k i).elim (fun hki => hki ▸ hw) fun hki => (hrest k hki hkj).trans hw
  have hir_le (w Bw : ℝ) (hw : (θ i).val < w) (hBw : w * m < Bw) :
      (M.outcome (Function.update θ j ⟨w, Bw⟩)).payment j ≤ w * m := by
    have hw_pos : 0 < w := (hθ i).1.trans hw
    have h := payment_le_of_ir hir
      (update_pos hθ j (b := ⟨w, Bw⟩) ⟨hw_pos, (mul_pos hw_pos hm).trans hBw⟩) j
    simpa only [Function.update_self, hall_m w Bw hw hBw] using h
  have hpay_const (w₁ B₁ w₂ B₂ : ℝ)
      (hw₁ : (θ i).val < w₁) (hB₁ : w₁ * m < B₁) (hw₂ : (θ i).val < w₂) (hB₂ : w₂ * m < B₂) :
      (M.outcome (Function.update θ j ⟨w₁, B₁⟩)).payment j ≤
        (M.outcome (Function.update θ j ⟨w₂, B₂⟩)).payment j := by
    set Bmax := max B₁ B₂ + 1
    have hw₁_pos : 0 < w₁ := (hθ i).1.trans hw₁
    have hw₂_pos : 0 < w₂ := (hθ i).1.trans hw₂
    have hBM₁ : w₁ * m < Bmax := by dsimp only [Bmax]; linarith [le_max_left B₁ B₂]
    have hBM₂ : w₂ * m < Bmax := by dsimp only [Bmax]; linarith [le_max_right B₁ B₂]
    have hBM_pos : 0 < Bmax := (mul_pos hw₁_pos hm).trans hBM₁
    have hle_max (w Bw : ℝ) (hw : (θ i).val < w) (hBw : w * m < Bw) (hle : Bw ≤ Bmax) :
        (M.outcome (Function.update θ j ⟨w, Bw⟩)).payment j =
          (M.outcome (Function.update θ j ⟨w, Bmax⟩)).payment j := by
      have hw_pos : 0 < w := (hθ i).1.trans hw
      have hBw_pos : 0 < Bw := (mul_pos hw_pos hm).trans hBw
      have hθw := update_pos hθ j (b := ⟨w, Bw⟩) ⟨hw_pos, hBw_pos⟩
      have hθM := update_pos hθ j (b := ⟨w, Bmax⟩) ⟨hw_pos, hBM_pos⟩
      have hic1 := hic _ hθw j ⟨w, Bmax⟩ ⟨hw_pos, hBM_pos⟩ (by
        simpa only [Function.update_idem, Function.update_self] using
          (hir_le w Bmax hw (hBw.trans_le hle)).trans hBw.le)
      have hic2 := hic _ hθM j ⟨w, Bw⟩ ⟨hw_pos, hBw_pos⟩ (by
        simpa only [Function.update_idem, Function.update_self] using
          (hbf _ hθw j).trans (by simpa only [Function.update_self] using hle))
      simp only [Outcome.utility, Function.update_idem, Function.update_self,
        hall_m w Bw hw hBw, hall_m w Bmax hw (hBw.trans_le hle)] at hic1 hic2
      linarith
    have h1 := hle_max w₁ B₁ hw₁ hB₁ (by dsimp only [Bmax]; linarith [le_max_left B₁ B₂])
    have h2 := hle_max w₂ B₂ hw₂ hB₂ (by dsimp only [Bmax]; linarith [le_max_right B₁ B₂])
    have hic12 := hic (Function.update θ j ⟨w₁, Bmax⟩)
      (update_pos hθ j ⟨hw₁_pos, hBM_pos⟩) j ⟨w₂, Bmax⟩ ⟨hw₂_pos, hBM_pos⟩
      (by simpa only [Function.update_idem, Function.update_self] using
            (hir_le w₂ Bmax hw₂ hBM₂).trans hBM₂.le)
    simp only [Outcome.utility, Function.update_idem, Function.update_self,
      hall_m w₁ Bmax hw₁ hBM₁, hall_m w₂ Bmax hw₂ hBM₂] at hic12
    linarith
  refine ⟨hall_m t BigB ht hBigB, le_antisymm ?_ ?_⟩
  · -- Upper bound `payment j ≤ (θ i).val * m` by taking `w₂ = (θ i).val + ε → (θ i).val`.
    by_contra! hgt
    let p := (M.outcome (Function.update θ j ⟨t, BigB⟩)).payment j
    let w₂ := (θ i).val + (p - (θ i).val * m) / (2 * m)
    have hw₂ : (θ i).val < w₂ :=
      lt_add_of_pos_right _ (div_pos (sub_pos.mpr hgt) (by positivity))
    have hw₂_mul : w₂ * m = (θ i).val * m + (p - (θ i).val * m) / 2 := by
      dsimp only [w₂]; field_simp [hm.ne']
    linarith [hpay_const t BigB w₂ (w₂ * m + 1) ht hBigB hw₂ (lt_add_one _),
      hir_le w₂ (w₂ * m + 1) hw₂ (lt_add_one _)]
  · -- Lower bound `(θ i).val * m ≤ payment j` via deviation from `s < (θ i).val`.
    by_contra! hlt
    let p := (M.outcome (Function.update θ j ⟨t, BigB⟩)).payment j
    have hp_nn : 0 ≤ p := hnn _ (update_pos hθ j ⟨ht_pos, hBigB_pos⟩) j
    let s := max ((θ i).val / 2) ((θ i).val - ((θ i).val * m - p) / (2 * m))
    have hs_pos : 0 < s := lt_max_of_lt_left (half_pos (hθ i).1)
    have hs_lt : s < (θ i).val :=
      max_lt (half_lt_self (hθ i).1)
        (sub_lt_self _ (div_pos (sub_pos.mpr hlt) (by positivity)))
    have hsm_gt : p < s * m := by
      have hmul := mul_le_mul_of_nonneg_right (le_max_right ((θ i).val / 2)
        ((θ i).val - ((θ i).val * m - p) / (2 * m))) hm.le
      have hcalc : ((θ i).val - ((θ i).val * m - p) / (2 * m)) * m =
          (θ i).val * m - ((θ i).val * m - p) / 2 := by field_simp [hm.ne']
      linarith
    let Bs := max (p + 1) 1
    have hθs := update_pos hθ j (b := ⟨s, Bs⟩) ⟨hs_pos, lt_max_of_lt_right zero_lt_one⟩
    have hxs0 : (M.outcome (Function.update θ j ⟨s, Bs⟩)).alloc j = 0 :=
      alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθs (a := i)
        (by simpa only [Function.update_self, Function.update_of_ne hij] using hs_lt)
        (by simpa only [Function.update_of_ne hij] using hv_i_unc)
    have hps0 : (M.outcome (Function.update θ j ⟨s, Bs⟩)).payment j = 0 :=
      le_antisymm (by simpa only [Function.update_self, hxs0, mul_zero] using
        payment_le_of_ir hir hθs j) (hnn _ hθs j)
    have hic_dev := hic _ hθs j ⟨t, BigB⟩ ⟨ht_pos, hBigB_pos⟩ (by
      simp only [Function.update_idem, Function.update_self]
      exact (by linarith : p ≤ p + 1).trans (le_max_left _ _))
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
  have hce := (Outcome.isParetoOptimal_iff (fun r => (hθ r).1.le)
    hfeas (hbf θ hθ)).mp (hpo θ hθ)
  have hother0 : ∀ k, k ≠ i → k ≠ j → (M.outcome θ).alloc k = 0 := fun k hki hkj =>
    alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθ (a := i) (hrest k hki hkj) hv_i_unc
  have hsum_eq : (M.outcome θ).alloc i + (M.outcome θ).alloc j = m := by
    linarith [(hce.1 ⟨i, hv_i_pos⟩).1, sum_eq_pair_of_zero hij hother0]
  -- Helper: `alloc j ≤ budget / v_i` for `w > v_i` at budget `B_j`, via `(v_i + ε, BigB)`.
  have hupper (w : ℝ) (hw : (θ i).val < w) :
      (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j ≤ (θ j).budget / (θ i).val := by
    have hw_pos : 0 < w := hv_i_pos.trans hw
    have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hw_pos, hB_j_pos⟩
    have hpj_le : (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j ≤ (θ j).budget := by
      simpa only [Function.update_self] using hbf _ hθw j
    rw [le_div_iff₀ hv_i_pos]
    by_contra! hgt
    let x := (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j
    let ε := (x * (θ i).val - (θ j).budget) / (2 * m)
    have hε_pos : 0 < ε := div_pos (sub_pos.mpr hgt) (by positivity)
    let t := (θ i).val + ε
    let BigB := max (t * m + 1) ((θ j).budget + 1)
    have hBigB_gt : t * m < BigB := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hθ_t := update_pos hθ j (b := ⟨t, BigB⟩)
      ⟨hv_i_pos.trans (by linarith), (mul_pos (by linarith) hm).trans hBigB_gt⟩
    obtain ⟨hxt, hpt⟩ := unconstrained_winner_payment_eq hm hnn hbf hir hpo hic hθ hij
      hv_i_unc hrest (t := t) (BigB := BigB) (by linarith) hBigB_gt
    have hic_dev := hic _ hθ_t j ⟨w, (θ j).budget⟩ ⟨hw_pos, hB_j_pos⟩ (by
      simpa only [Function.update_idem, Function.update_self] using
        hpj_le.trans ((lt_add_one _).le.trans (le_max_right _ _)))
    simp only [Outcome.utility, Function.update_idem, Function.update_self, hxt, hpt] at hic_dev
    have hεm : ε * m = (x * (θ i).val - (θ j).budget) / 2 := by dsimp only [ε]; field_simp [hm.ne']
    nlinarith only [hic_dev, hεm, hpj_le, hgt, hε_pos, (hpo _ hθw).1.1 j]
  have hup_self : (M.outcome θ).alloc j ≤ (θ j).budget / (θ i).val := by
    simpa only [Function.update_eq_self] using hupper (θ j).val hlt_ij
  -- Whenever bidder `j` reports `w > v_i` with budget `B_j` and receives `< m`, its budget binds.
  have hpay_if_lt (w : ℝ) (hw : (θ i).val < w)
      (hltw : (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j < m) :
      (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j = (θ j).budget := by
    have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hv_i_pos.trans hw, hB_j_pos⟩
    have hother_w : ∀ k, k ≠ i → k ≠ j →
        (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc k = 0 := fun k hki hkj =>
      alloc_eq_zero_of_lt_unconstrained hbf hir hpo hθw (a := i)
        (by simpa only [Function.update_of_ne hkj, Function.update_of_ne hij] using hrest k hki hkj)
        (by simpa only [Function.update_of_ne hij] using hv_i_unc)
    have hce_w := (Outcome.isParetoOptimal_iff (fun r => (hθw r).1.le)
      (hpo _ hθw).1 (hbf _ hθw)).mp (hpo _ hθw)
    have hxi_pos : 0 < (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc i := by
      linarith [(hce_w.1 ⟨i, by simpa only [Function.update_of_ne hij] using hv_i_pos⟩).1,
        sum_eq_pair_of_zero hij hother_w]
    simpa only [Function.update_self] using hce_w.2 i j hxi_pos
      (by simpa only [Function.update_of_ne hij, Function.update_self] using hw)
  -- Split between strict binding `(θ j).budget < (θ i).val * m` and boundary equality.
  rcases lt_or_eq_of_le hbind with hstrict | heq
  · have hpay_bind (w : ℝ) (hw : (θ i).val < w) :
        (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j = (θ j).budget :=
      hpay_if_lt w hw (lt_of_le_of_lt (hupper w hw) ((div_lt_iff₀ hv_i_pos).mpr (by linarith)))
    have hp_s : (M.outcome θ).payment j = (θ j).budget := by
      simpa only [Function.update_eq_self] using hpay_bind (θ j).val hlt_ij
    have hx_const (w : ℝ) (hw : (θ i).val < w) :
        (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j = (M.outcome θ).alloc j := by
      have hw_pos : 0 < w := hv_i_pos.trans hw
      have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hw_pos, hB_j_pos⟩
      have h1 := hic θ hθ j ⟨w, (θ j).budget⟩ ⟨hw_pos, hB_j_pos⟩ (hpay_bind w hw).le
      have h2 := hic _ hθw j (θ j) (hθ j) (by
        simpa only [Function.update_idem, Function.update_eq_self, Function.update_self] using
          hp_s.le)
      simp only [Outcome.utility, Function.update_idem, Function.update_eq_self,
        Function.update_self, hpay_bind w hw, hp_s] at h1 h2
      exact le_antisymm
        (le_of_mul_le_mul_left (by linarith : (θ j).val * _ ≤ (θ j).val * _) (hθ j).1)
        (le_of_mul_le_mul_left (by linarith : w * _ ≤ w * _) hw_pos)
    have hlow : (θ j).budget / (θ i).val ≤ (M.outcome θ).alloc j := by
      rw [div_le_iff₀ hv_i_pos]
      by_contra! hlt
      let x := (M.outcome θ).alloc j
      have hx_pos : 0 < x := lt_of_le_of_ne (hfeas.1 j) fun h0 => by
        nlinarith [payment_le_of_ir hir hθ j]
      let w := (θ i).val + ((θ j).budget - x * (θ i).val) / (2 * x)
      have hw : (θ i).val < w := lt_add_of_pos_right _ (div_pos (sub_pos.mpr hlt) (by positivity))
      have hiru := payment_le_of_ir hir
        (update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hv_i_pos.trans hw, hB_j_pos⟩) j
      simp only [Function.update_self, hx_const w hw, hpay_bind w hw] at hiru
      have hwx : w * x = x * (θ i).val + ((θ j).budget - x * (θ i).val) / 2 := by
        dsimp only [w]; field_simp [hx_pos.ne']
      linarith
    exact ⟨le_antisymm hup_self hlow, by linarith, hother0, fun _ => hp_s⟩
  · -- Boundary case `(θ j).budget = (θ i).val * m`: then `budget / v_i = m`.
    have hdiv_eq : (θ j).budget / (θ i).val = m := heq ▸ mul_div_cancel_left₀ m hv_i_pos.ne'
    have hxj_eq : (M.outcome θ).alloc j = m := by
      by_contra hne
      have hxj_lt : (M.outcome θ).alloc j < m := lt_of_le_of_ne (hdiv_eq ▸ hup_self) hne
      have hpj_eq : (M.outcome θ).payment j = (θ j).budget := hce.2 i j (by linarith) hlt_ij
      have hxj_pos : 0 < (M.outcome θ).alloc j := lt_of_le_of_ne (hfeas.1 j) fun h0 => by
        linarith [h0 ▸ payment_le_of_ir hir hθ j]
      -- Pick `w` just above `v_i` with `w * alloc j < v_i * m = budget`.
      let w := (θ i).val + ((θ i).val * (m - (M.outcome θ).alloc j)) / (2 * (M.outcome θ).alloc j)
      have hw : (θ i).val < w :=
        lt_add_of_pos_right _ (div_pos (mul_pos hv_i_pos (sub_pos.mpr hxj_lt)) (by positivity))
      have hθw := update_pos hθ j (b := ⟨w, (θ j).budget⟩) ⟨hv_i_pos.trans hw, hB_j_pos⟩
      have hp_le :
          (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).payment j ≤ (θ j).budget := by
        simpa only [Function.update_self] using hbf _ hθw j
      have h1 := hic θ hθ j ⟨w, (θ j).budget⟩ ⟨hv_i_pos.trans hw, hB_j_pos⟩ hp_le
      simp only [Outcome.utility, hpj_eq] at h1
      have hxw_le : (M.outcome (Function.update θ j ⟨w, (θ j).budget⟩)).alloc j ≤
          (M.outcome θ).alloc j :=
        le_of_mul_le_mul_left (by linarith : (θ j).val * _ ≤ (θ j).val * _) (hθ j).1
      have hiru := payment_le_of_ir hir hθw j
      simp only [Function.update_self, hpay_if_lt w hw (lt_of_le_of_lt hxw_le hxj_lt)] at hiru
      have hcalc : w * (M.outcome θ).alloc j =
          (θ i).val * (M.outcome θ).alloc j + (θ i).val * (m - (M.outcome θ).alloc j) / 2 := by
        dsimp only [w]; field_simp [hxj_pos.ne']
      nlinarith only [hiru, heq, hxj_lt, hv_i_pos, hw, hxw_le, hcalc]
    exact ⟨hxj_eq.trans hdiv_eq.symm, by linarith, hother0, fun h => absurd heq h.ne⟩

/-- Harmonic telescoping upper bound `∑_{r=6}^{14} 1 / r = 348911 / 360360 < 1`. -/
private theorem sum_inv_six_to_fourteen_lt_one :
    (∑ k : Fin 9, (1 : ℝ) / ((k.val : ℝ) + 6)) < 1 := by
  simp [Fin.sum_univ_succ]; norm_num

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
  have hprof_pos (k : Fin 10) : ∀ r : ι, (prof k r).IsPos :=
    update_pos (fun r => by
      rcases eq_or_ne r i with rfl | hri
      · exact hbase_i ▸ ⟨by positivity, zero_lt_one⟩
      · rcases eq_or_ne r j with rfl | hrj
        · exact hbase_j ▸ ⟨by positivity, zero_lt_one⟩
        · exact hbase_rest r hri hrj ▸ ⟨by positivity, zero_lt_one⟩)
      i ⟨by positivity, by norm_num⟩
  have ht_bounds (k : Fin 10) : 1 / m ≤ t k ∧ t k ≤ 5 / (2 * m) := by
    have hk_le : (k.val : ℝ) ≤ 9 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
    have hk_nn : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    exact ⟨(div_le_div_iff₀ hm (by positivity)).mpr (by nlinarith),
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)⟩
  have halloc_i (k : Fin 10) : (M.outcome (prof k)).alloc i = m - 1 / t k := by
    obtain ⟨hkt_lo, hkt_hi⟩ := ht_bounds k
    have hpin := pinning_of_isPrivateBudgetDSIC_isParetoOptimal hm hnn hbf hir hpo hic
      (hprof_pos k) hij
      (by simp only [prof, Function.update_self]
          calc t k * m
            _ ≤ 5 / (2 * m) * m := mul_le_mul_of_nonneg_right hkt_hi hm.le
            _ = 5 / 2 := by field_simp [hm.ne']
            _ < 10 := by norm_num)
      (fun r hri hrj => by
        simp only [prof, Function.update_self, Function.update_of_ne hri, hbase_rest r hri hrj]
        linarith [(div_lt_div_iff₀ (a := 1) (c := 1)
          (mul_pos zero_lt_two hm) hm).mpr (by linarith)])
      (by simp only [prof, Function.update_self, Function.update_of_ne hij.symm, hbase_j]
          linarith [(div_lt_div_iff₀ (a := 5) (c := 100)
            (mul_pos zero_lt_two hm) hm).mpr (by linarith)])
      (by simp only [prof, Function.update_self, Function.update_of_ne hij.symm, hbase_j]
          calc (1 : ℝ)
            _ = (1 / m) * m := by field_simp [hm.ne']
            _ ≤ t k * m := mul_le_mul_of_nonneg_right hkt_lo hm.le)
    simpa only [prof, Function.update_self, Function.update_of_ne hij.symm, hbase_j] using hpin.2.1
  have hp0 : (M.outcome (prof 0)).payment i = 0 := by
    have ha0 : (M.outcome (prof 0)).alloc i = 0 := by
      rw [halloc_i 0]
      simp only [t, Fin.val_zero, Nat.cast_zero, zero_add]
      field_simp [hm.ne']; ring
    linarith [ha0 ▸ payment_le_of_ir hir (hprof_pos 0) i, hnn _ (hprof_pos 0) i]
  have hstep (k : Fin 9) :
      (M.outcome (prof k.succ)).payment i - (M.outcome (prof k.castSucc)).payment i ≤
        1 / ((k.val : ℝ) + 6) := by
    have hic_k := hic (prof k.succ) (hprof_pos k.succ) i ⟨t k.castSucc, 10⟩
      ⟨div_pos (by positivity) (by positivity), by norm_num⟩
      (by simpa only [prof, Function.update_idem, Function.update_self] using
            hbf _ (hprof_pos k.castSucc) i)
    dsimp only [prof, Outcome.utility] at hic_k halloc_i
    simp only [Function.update_idem, Function.update_self,
      halloc_i k.succ, halloc_i k.castSucc] at hic_k
    have hdiff : t k.succ * ((m - 1 / t k.succ) - (m - 1 / t k.castSucc)) =
        1 / ((k.val : ℝ) + 6) := by
      simp only [t, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
      field_simp; ring
    linarith
  have ht9 : t (Fin.last 9) = 5 / (2 * m) := by
    simp only [t, Fin.val_last]
    field_simp [hm.ne']; norm_num
  have hprof9 : prof (Fin.last 9) = Function.update θbase i ⟨5 / (2 * m), 10⟩ := by rw [← ht9]
  have htel := fin_sum_telescope fun k : Fin 10 => (M.outcome (prof k)).payment i
  have hbound := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hstep k
  rw [← hprof9]
  refine ⟨?_, by linarith [sum_inv_six_to_fourteen_lt_one]⟩
  rw [halloc_i (Fin.last 9), ht9]
  field_simp [hm.ne']; norm_num

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
  obtain ⟨i₀, i₁, hne⟩ := Fintype.one_lt_card_iff.mp hcard
  let θstar : ι → BidderType := fun k =>
    if k = i₀ ∨ k = i₁ then ⟨100 / m, 1⟩ else ⟨1 / (2 * m), 1⟩
  have hθ_pos (k : ι) : (θstar k).IsPos := by
    dsimp only [θstar]
    split_ifs <;> exact ⟨by positivity, zero_lt_one⟩
  have h0_eq : θstar i₀ = ⟨100 / m, 1⟩ := by simp [θstar]
  have h1_eq : θstar i₁ = ⟨100 / m, 1⟩ := by simp [θstar]
  have hrest_eq (k : ι) (h0 : k ≠ i₀) (h1 : k ≠ i₁) : θstar k = ⟨1 / (2 * m), 1⟩ := by
    simp [θstar, h0, h1]
  obtain ⟨hx0, hp0⟩ := payoff_at_overreport_budget hm hnn hbf hir hpo hic hne θstar
    h0_eq h1_eq hrest_eq
  obtain ⟨hx1, hp1⟩ := payoff_at_overreport_budget hm hnn hbf hir hpo hic hne.symm θstar
    h1_eq h0_eq fun k h1 h0 => hrest_eq k h0 h1
  have hdev_pos : (⟨5 / (2 * m), 10⟩ : BidderType).IsPos := ⟨by positivity, by norm_num⟩
  have hic0 := hic θstar hθ_pos i₀ ⟨5 / (2 * m), 10⟩ hdev_pos (by simpa [h0_eq] using hp0.le)
  have hic1 := hic θstar hθ_pos i₁ ⟨5 / (2 * m), 10⟩ hdev_pos (by simpa [h1_eq] using hp1.le)
  simp only [Outcome.utility, h0_eq, h1_eq, hx0, hx1] at hic0 hic1
  have h100_mul : (100 / m) * (3 / 5 * m) = 60 := by field_simp [hm.ne']; ring
  have halloc_sum : (M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁ ≤ m :=
    calc (M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁
      _ = ∑ k ∈ ({i₀, i₁} : Finset ι), (M.outcome θstar).alloc k := (Finset.sum_pair hne).symm
      _ ≤ ∑ k, (M.outcome θstar).alloc k :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun k _ _ => (hfeas θstar hθ_pos).1 k
      _ ≤ m := (hfeas θstar hθ_pos).2
  have h100_bound :
      (100 / m) * ((M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁) ≤ 100 :=
    calc (100 / m) * ((M.outcome θstar).alloc i₀ + (M.outcome θstar).alloc i₁)
      _ ≤ (100 / m) * m := mul_le_mul_of_nonneg_left halloc_sum (div_nonneg (by norm_num) hm.le)
      _ = 100 := by field_simp [hm.ne']
  linarith [hnn θstar hθ_pos i₀, hnn θstar hθ_pos i₁]

end Proof

end Cslib.GameTheory.BudgetedAuction

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.SingleParameter
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-unit auctions with hard budget constraints

Foundational definitions and Pareto-optimality characterization for multi-unit auctions of a
divisible supply `m ≥ 0` among `ι` bidders with linear per-unit valuations `vᵢ ≥ 0` and hard
budget limits `Bᵢ ≥ 0` ([DobzinskiLaviNisan2012]; primary PDF not inspected, theorem/page locators
unverified).

Each bidder `i : ι` has type `⟨vᵢ, Bᵢ⟩ : BidderType`, receives a nonnegative allocation
`o.alloc i : ℝ` with `∑ i, o.alloc i ≤ m`, and makes a payment `o.payment i : ℝ`. Under hard
budget limits, an outcome exceeding `Bᵢ` yields `-∞` utility (modeled as a feasibility constraint
`o.payment i ≤ Bᵢ`); otherwise bidder `i`'s quasilinear utility is `vᵢ * o.alloc i - o.payment i`,
and the seller's revenue is `∑ i, o.payment i`.

We define both:
* **Public-budget mechanisms** (`SingleParameter.Mechanism` bridge via `toSingleParameter`):
  fixed public budgets `B : ι → ℝ`, reporting valuations `v : ι → ℝ`
  (`SingleParameter.Mechanism.IsDSIC`).
* **Private-budget mechanisms** (`BudgetedMechanism`): reporting pairs `θ : ι → BidderType`, where
  `IsPrivateBudgetDSIC` rules out profitable unilateral deviations whose realized payment stays
  within the bidder's true budget (`(M.outcome (update θ i b')).payment i ≤ (θ i).budget`).

Our main theorem in this module, `Outcome.isParetoOptimal_iff`, gives an exact characterization of
Pareto optimality over budget-feasible outcomes (allowing unrestricted side transfers
`o'.payment i ≤ B i` with fixed sum constraints): a feasible budget-feasible outcome `o` is Pareto
optimal iff (1) whenever some bidder has `vᵢ > 0`, the entire supply `m` is allocated and no
zero-value bidder holds positive allocation, and (2) whenever `o.alloc i > 0` and `vᵢ < vⱼ`, bidder
`j`'s budget is exhausted (`o.payment j = B j`).

## Main definitions

* `Cslib.GameTheory.BudgetedAuction.BidderType`: `(val, budget)` type record with `IsPos`.
* `Cslib.GameTheory.BudgetedAuction.Outcome`: `(alloc, payment)` pair with `IsFeasible`,
  `IsBudgetFeasible`, `HasNonnegPayment`, `utility`, `IsIR`, `revenue`, `ParetoDominates`, and
  `IsParetoOptimal`.
* `Cslib.GameTheory.BudgetedAuction.BudgetedMechanism`: deterministic direct-revelation mechanism
  mapping `θ : ι → BidderType` to `Outcome ι`, with `IsFeasibleOnPos`, `IsBudgetFeasibleOnPos`,
  `HasNonnegPaymentOnPos`, `IsIROnPos`, `IsParetoOptimalOnPos`, `IsPrivateBudgetDSIC`, and
  `toSingleParameter`.

## Main results

* `Cslib.GameTheory.BudgetedAuction.Outcome.isParetoOptimal_iff`: exact characterization of Pareto
  optimality for budget-constrained multi-unit auctions with supply `m ≥ 0` and valuations
  `∀ i, 0 ≤ v i` ([DobzinskiLaviNisan2012], primary PDF unverified).

## References

* [S. Dobzinski, R. Lavi, and N. Nisan,
  *Multi-unit auctions with budget limits*][DobzinskiLaviNisan2012]
  (primary PDF not inspected; theorem/page locators unverified)
-/

public section

namespace Cslib.GameTheory.BudgetedAuction

/-- Type of a budget-constrained bidder in a multi-unit auction with linear per-unit utility:
per-unit valuation `val` and hard budget cap `budget`. -/
@[ext]
structure BidderType where
  /-- Marginal value per unit of the good. -/
  val : ℝ
  /-- Maximum payment the bidder can afford. -/
  budget : ℝ

namespace BidderType

/-- A bidder type with strictly positive valuation and strictly positive budget. -/
@[expose] def IsPos (b : BidderType) : Prop :=
  0 < b.val ∧ 0 < b.budget

end BidderType

/-- An outcome of a multi-unit auction over bidder set `ι`: per-bidder allocations and payments. -/
@[ext]
structure Outcome (ι : Type*) where
  /-- Quantity allocated to each bidder. -/
  alloc : ι → ℝ
  /-- Monetary transfer paid by each bidder to the seller (may be negative in side-transfer
  comparisons). -/
  payment : ι → ℝ

namespace Outcome

section Operations

variable {ι : Type*}

/-- Quasilinear utility of bidder `i` with per-unit valuation `v i`
(assuming `o.payment i ≤ B i`). -/
@[expose] def utility (v : ι → ℝ) (o : Outcome ι) (i : ι) : ℝ :=
  v i * o.alloc i - o.payment i

/-- Nonnegative payment (`no positive transfers`): every bidder pays at least `0`. -/
@[expose] def HasNonnegPayment (o : Outcome ι) : Prop :=
  ∀ i, 0 ≤ o.payment i

/-- Hard budget feasibility against budget profile `B`. -/
@[expose] def IsBudgetFeasible (B : ι → ℝ) (o : Outcome ι) : Prop :=
  ∀ i, o.payment i ≤ B i

/-- Individual rationality against valuation profile `v`: every bidder receives nonnegative
utility. -/
@[expose] def IsIR (v : ι → ℝ) (o : Outcome ι) : Prop :=
  ∀ i, 0 ≤ o.utility v i

end Operations

section Finite

variable {ι : Type*} [Fintype ι]

/-- Allocation feasibility for divisible supply `m`: nonnegative allocations summing to at most
`m`. -/
@[expose] def IsFeasible (m : ℝ) (o : Outcome ι) : Prop :=
  (∀ i, 0 ≤ o.alloc i) ∧ ∑ i, o.alloc i ≤ m

/-- Total seller revenue `∑ i, o.payment i`. -/
@[expose] def revenue (o : Outcome ι) : ℝ :=
  ∑ i, o.payment i

/-- `o'` strictly Pareto-dominates `o` with respect to supply `m`, valuations `v`, and hard budgets
`B` (allowing side-payment transfers `o'.payment i ≤ B i` with no lower bound on payments). -/
@[expose] def ParetoDominates (m : ℝ) (v B : ι → ℝ) (o' o : Outcome ι) : Prop :=
  o'.IsFeasible m ∧ o'.IsBudgetFeasible B ∧
    (∀ i, o.utility v i ≤ o'.utility v i) ∧
    o.revenue ≤ o'.revenue ∧
    ((∃ i, o.utility v i < o'.utility v i) ∨ o.revenue < o'.revenue)

/-- An outcome `o` is Pareto optimal if it is feasible, budget-feasible, and not Pareto-dominated by
any feasible, budget-feasible outcome `o'`. -/
@[expose] def IsParetoOptimal (m : ℝ) (v B : ι → ℝ) (o : Outcome ι) : Prop :=
  o.IsFeasible m ∧ o.IsBudgetFeasible B ∧ ∀ o' : Outcome ι, ¬ o'.ParetoDominates m v B o

/-- Market-clearing and budget-exhaustion condition characterizing Pareto optimality. -/
private def IsClearedAndExhausted (m : ℝ) (v B : ι → ℝ) (o : Outcome ι) : Prop :=
  ((∃ i, 0 < v i) → ∑ i, o.alloc i = m ∧ ∀ i, v i = 0 → o.alloc i = 0) ∧
    (∀ i j, 0 < o.alloc i → v i < v j → o.payment j = B j)

private theorem sum_update_eq [DecidableEq ι] (f : ι → ℝ) (i : ι) (a : ℝ) :
    ∑ k, Function.update f i a k = ∑ k, f k + (a - f i) := by
  rw [← Finset.add_sum_erase Finset.univ (Function.update f i a) (Finset.mem_univ i),
    Function.update_self, Finset.sum_congr rfl fun k hk =>
      Function.update_of_ne (Finset.ne_of_mem_erase hk) a f]
  linarith [Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)]

private theorem sum_update_transfer [DecidableEq ι] (f : ι → ℝ) {i j : ι} (hij : i ≠ j) (δ : ℝ) :
    ∑ k, Function.update (Function.update f i (f i - δ)) j (f j + δ) k = ∑ k, f k := by
  rw [sum_update_eq, Function.update_of_ne hij.symm, sum_update_eq]
  ring

private theorem eq_of_le_of_sum_le {f g : ι → ℝ} (hle : ∀ i, f i ≤ g i)
    (hsum : ∑ i, g i ≤ ∑ i, f i) (i : ι) : f i = g i := by
  exact (Finset.sum_eq_sum_iff_of_le fun k _ => hle k).mp
    ((Finset.sum_le_sum fun k _ => hle k).antisymm hsum) i (Finset.mem_univ i)

private theorem isClearedAndExhausted_of_isParetoOptimal
    {m : ℝ} {v B : ι → ℝ} (hv : ∀ i, 0 ≤ v i) {o : Outcome ι}
    (hpo : o.IsParetoOptimal m v B) :
    IsClearedAndExhausted m v B o := by
  classical
  obtain ⟨⟨hnn, hsum⟩, hbf, hnd⟩ := hpo
  refine ⟨fun ⟨j, hjv⟩ => ⟨by_contra fun hne => ?_, fun i hvi => by_contra fun hxi => ?_⟩,
    fun i j hxi hvij => by_contra fun hne => ?_⟩
  · have hδ : 0 < m - ∑ i, o.alloc i := sub_pos.mpr (lt_of_le_of_ne hsum hne)
    let o' : Outcome ι := ⟨Function.update o.alloc j (o.alloc j + (m - ∑ i, o.alloc i)), o.payment⟩
    refine hnd o' ⟨⟨fun i => ?_, by simp only [o', sum_update_eq]; linarith⟩, hbf, fun i => ?_,
      le_rfl, Or.inl ⟨j, by simp only [utility, o', Function.update_self]; nlinarith⟩⟩
    · simp only [o', Function.update_apply]
      split_ifs <;> linarith [hnn i, hnn j]
    · rcases eq_or_ne i j with rfl | hi
      · simp only [utility, o', Function.update_self]; nlinarith
      · simp [utility, o', Function.update_of_ne hi]
  · have hxpos : 0 < o.alloc i := lt_of_le_of_ne (hnn i) (Ne.symm hxi)
    have hij : i ≠ j := fun h => by linarith [h ▸ hvi]
    let o' : Outcome ι :=
      ⟨Function.update (Function.update o.alloc i (o.alloc i - o.alloc i)) j
        (o.alloc j + o.alloc i), o.payment⟩
    have hsum_eq := sum_update_transfer o.alloc hij (o.alloc i)
    refine hnd o' ⟨⟨fun k => ?_, by dsimp only [o']; linarith⟩, hbf, fun k => ?_, le_rfl,
      Or.inl ⟨j, by simp only [utility, o', Function.update_self]; nlinarith⟩⟩
    · simp only [o', Function.update_apply]
      split_ifs <;> linarith [hnn i, hnn j, hnn k]
    · rcases eq_or_ne k j with rfl | hkj
      · simp only [utility, o', Function.update_self]; nlinarith
      · rcases eq_or_ne k i with rfl | hki <;> simp [utility, o', *]
  · have hltB : o.payment j < B j := lt_of_le_of_ne (hbf j) hne
    have hij : i ≠ j := fun h => lt_irrefl _ (h ▸ hvij)
    let mid : ℝ := (v i + v j) / 2
    have hmid_pos : 0 < mid := by dsimp only [mid]; linarith [hv i]
    let δ : ℝ := min (o.alloc i) ((B j - o.payment j) / mid)
    have hδ_pos : 0 < δ := lt_min hxi (div_pos (sub_pos.mpr hltB) hmid_pos)
    have hδ_le_alloc : δ ≤ o.alloc i := min_le_left _ _
    have hδ_mul_le : mid * δ ≤ B j - o.payment j :=
      calc
        mid * δ ≤ mid * ((B j - o.payment j) / mid) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hmid_pos.le
        _ = B j - o.payment j := mul_div_cancel₀ _ hmid_pos.ne'
    let t : ℝ := mid * δ
    let o' : Outcome ι :=
      { alloc := Function.update (Function.update o.alloc i (o.alloc i - δ)) j (o.alloc j + δ)
        payment := Function.update (Function.update o.payment i (o.payment i - t)) j
          (o.payment j + t) }
    have hsum_alloc : ∑ k, o'.alloc k = ∑ k, o.alloc k := sum_update_transfer o.alloc hij δ
    have hsum_pay : o'.revenue = o.revenue := sum_update_transfer o.payment hij t
    have hgap : 0 < (v j - v i) / 2 * δ := by nlinarith
    have hutil_i : o.utility v i < o'.utility v i := by
      simp only [utility, o', Function.update_of_ne hij, Function.update_self, t, mid]; linarith
    refine hnd o' ⟨⟨fun k => ?_, by linarith⟩, fun k => ?_, fun k => ?_, hsum_pay.ge,
      Or.inl ⟨i, hutil_i⟩⟩
    · simp only [o', Function.update_apply]
      split_ifs <;> linarith [hnn j, hnn k]
    · rcases eq_or_ne k j with rfl | hkj
      · simp only [o', Function.update_self, t]; linarith
      · rcases eq_or_ne k i with rfl | hki
        · simp only [o', Function.update_of_ne hkj, Function.update_self]
          linarith [hbf k, mul_nonneg hmid_pos.le hδ_pos.le]
        · simpa only [o', Function.update_of_ne hkj, Function.update_of_ne hki] using hbf k
    · rcases eq_or_ne k j with rfl | hkj
      · simp only [utility, o', Function.update_self, t, mid]; linarith
      · rcases eq_or_ne k i with rfl | hki
        exacts [hutil_i.le, by simp [utility, o', hkj, hki]]

private theorem isParetoOptimal_of_isClearedAndExhausted
    {m : ℝ} {v B : ι → ℝ} (hv : ∀ i, 0 ≤ v i) {o : Outcome ι}
    (hfeas : o.IsFeasible m) (hbf : o.IsBudgetFeasible B)
    (hce : IsClearedAndExhausted m v B o) :
    o.IsParetoOptimal m v B := by
  classical
  refine ⟨hfeas, hbf, fun o' ⟨⟨hnn', hsum'⟩, hbf', hu_le, hrev_le, hstrict⟩ => ?_⟩
  obtain ⟨hclear, hexh⟩ := hce
  let slackSet : Finset ι := Finset.univ.filter fun j => 0 < v j ∧ o.payment j < B j
  by_cases hslack : slackSet.Nonempty
  · -- Some bidder with `v j > 0` has unspent budget; form positive Pareto weights `w i`.
    set pStar : ℝ := (slackSet.image v).max' (hslack.image v)
    obtain ⟨j₀, hj₀_mem, hj₀_eq⟩ := Finset.mem_image.mp (Finset.max'_mem (slackSet.image v) _)
    obtain ⟨hj₀_v, hj₀_pay⟩ := (Finset.mem_filter.mp hj₀_mem).2
    obtain ⟨hsum_eq, -⟩ := hclear ⟨j₀, hj₀_v⟩
    have hpStar_pos : 0 < pStar := hj₀_v.trans_eq hj₀_eq
    have hge_of_alloc_pos (i : ι) (hi : 0 < o.alloc i) : pStar ≤ v i :=
      le_of_not_gt fun hlt => hj₀_pay.ne (hexh i j₀ hi (hlt.trans_eq hj₀_eq.symm))
    have hbudget_of_gt (i : ι) (hi : pStar < v i) : o.payment i = B i :=
      by_contra fun hne => hi.not_ge <| Finset.le_max' (slackSet.image v) (v i) <|
        Finset.mem_image_of_mem v <| Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, hpStar_pos.trans hi, lt_of_le_of_ne (hbf i) hne⟩
    let w : ι → ℝ := fun i => if v i ≤ pStar then 1 else pStar / v i
    have hw_pos (i : ι) : 0 < w i := by
      dsimp only [w]
      split_ifs with hle
      exacts [zero_lt_one, div_pos hpStar_pos (hpStar_pos.trans (lt_of_not_ge hle))]
    have hterm_le (i : ι) :
        w i * (o'.utility v i - o.utility v i) + (o'.payment i - o.payment i) ≤
          pStar * (o'.alloc i - o.alloc i) := by
      dsimp only [w, utility]
      split_ifs with hle
      · rcases (hfeas.1 i).eq_or_lt with hxi | hxi_pos
        · rw [← hxi]
          linarith [mul_le_mul_of_nonneg_right hle (hnn' i)]
        · rw [le_antisymm hle (hge_of_alloc_pos i hxi_pos)]
          linarith
      · have hgt : pStar < v i := lt_of_not_ge hle
        have hvi_pos : 0 < v i := hpStar_pos.trans hgt
        have hrew :
            (pStar / v i) * (v i * o'.alloc i - o'.payment i - (v i * o.alloc i - o.payment i)) +
              (o'.payment i - o.payment i) =
            pStar * (o'.alloc i - o.alloc i) +
              (1 - pStar / v i) * (o'.payment i - o.payment i) := by field_simp [hvi_pos.ne']; ring
        rw [hrew]
        linarith [mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr ((div_le_one hvi_pos).mpr hgt.le))
          (sub_nonpos.mpr ((hbf' i).trans_eq (hbudget_of_gt i hgt).symm))]
    have hsum_le :
        (∑ i, w i * (o'.utility v i - o.utility v i)) + (o'.revenue - o.revenue) ≤ 0 := by
      calc (∑ i, w i * (o'.utility v i - o.utility v i)) + (o'.revenue - o.revenue)
          = ∑ i, (w i * (o'.utility v i - o.utility v i) + (o'.payment i - o.payment i)) := by
            simp only [revenue, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ ≤ ∑ i, pStar * (o'.alloc i - o.alloc i) := Finset.sum_le_sum fun i _ => hterm_le i
        _ = pStar * (∑ i, o'.alloc i - ∑ i, o.alloc i) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib]
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpStar_pos.le (by linarith)
    have hwu_nn (i : ι) : 0 ≤ w i * (o'.utility v i - o.utility v i) :=
      mul_nonneg (hw_pos i).le (sub_nonneg.mpr (hu_le i))
    rcases hstrict with ⟨i₀, hi₀⟩ | hrev_lt
    · linarith [(mul_pos (hw_pos i₀) (sub_pos.mpr hi₀)).trans_le
        (Finset.single_le_sum (fun i _ => hwu_nn i) (Finset.mem_univ i₀))]
    · linarith [Finset.sum_nonneg (s := Finset.univ) fun i _ => hwu_nn i]
  · -- Every bidder with `v i > 0` already has `o.payment i = B i`, forcing equal payments.
    have hpay_le (i : ι) : o'.payment i ≤ o.payment i := by
      rcases (hv i).eq_or_lt with hvi0 | hvi
      · simpa only [utility, ← hvi0, zero_mul, zero_sub, neg_le_neg_iff] using hu_le i
      · exact (hbf' i).trans (not_lt.mp fun hlt =>
          hslack ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvi, hlt⟩⟩)
    have hpay_eq (i : ι) : o'.payment i = o.payment i := eq_of_le_of_sum_le hpay_le hrev_le i
    obtain ⟨i₀, hi₀⟩ := hstrict.resolve_right
      (not_lt_of_ge (Finset.sum_congr rfl fun i _ => hpay_eq i).le)
    simp only [utility, hpay_eq i₀, sub_lt_sub_iff_right] at hi₀
    obtain ⟨hsum_eq, hzero_alloc⟩ :=
      hclear ⟨i₀, (hv i₀).lt_of_ne' fun h0 => by simp [h0] at hi₀⟩
    have halloc_ge (i : ι) : o.alloc i ≤ o'.alloc i := by
      rcases (hv i).eq_or_lt with hvi0 | hvi
      · exact hzero_alloc i hvi0.symm ▸ hnn' i
      · exact le_of_mul_le_mul_left
          (by simpa only [utility, hpay_eq i, sub_le_sub_iff_right] using hu_le i) hvi
    exact lt_irrefl _ (eq_of_le_of_sum_le halloc_ge (hsum'.trans_eq hsum_eq.symm) i₀ ▸ hi₀)

/-- **Exact Pareto-optimality characterization** ([DobzinskiLaviNisan2012], primary PDF not
inspected): for a feasible, budget-feasible outcome `o` of supply `m` under nonnegative valuations
`v`, `o` is Pareto optimal if and only if:
1. whenever some bidder has `0 < v i`, the entire supply `m` is allocated (`∑ i, o.alloc i = m`)
   and no bidder with `v i = 0` holds positive allocation (`o.alloc i = 0`); and
2. whenever a bidder `i` receives positive allocation (`0 < o.alloc i`) and bidder `j` has strictly
   higher valuation (`v i < v j`), bidder `j`'s budget is exhausted (`o.payment j = B j`). -/
theorem isParetoOptimal_iff {m : ℝ} {v B : ι → ℝ} (hv : ∀ i, 0 ≤ v i)
    {o : Outcome ι} (hfeas : o.IsFeasible m) (hbf : o.IsBudgetFeasible B) :
    o.IsParetoOptimal m v B ↔
      ((∃ i, 0 < v i) → ∑ i, o.alloc i = m ∧ ∀ i, v i = 0 → o.alloc i = 0) ∧
      (∀ i j, 0 < o.alloc i → v i < v j → o.payment j = B j) :=
  ⟨isClearedAndExhausted_of_isParetoOptimal hv,
   isParetoOptimal_of_isClearedAndExhausted hv hfeas hbf⟩

end Finite

end Outcome

/-- A deterministic direct-revelation auction for bidders with private linear valuations and
private hard budgets (`θ i = ⟨vᵢ, Bᵢ⟩`). -/
structure BudgetedMechanism (ι : Type*) where
  /-- Allocation and payment outcome on reported profile `θ`. -/
  outcome : (ι → BidderType) → Outcome ι

namespace BudgetedMechanism

variable {ι : Type*} [Fintype ι]

/-- Allocation-feasibility on every strictly positive type profile. -/
@[expose] def IsFeasibleOnPos (M : BudgetedMechanism ι) (m : ℝ) : Prop :=
  ∀ θ : ι → BidderType, (∀ i, (θ i).IsPos) → (M.outcome θ).IsFeasible m

/-- Hard budget-feasibility on every strictly positive type profile. -/
@[expose] def IsBudgetFeasibleOnPos (M : BudgetedMechanism ι) : Prop :=
  ∀ θ : ι → BidderType, (∀ i, (θ i).IsPos) →
    (M.outcome θ).IsBudgetFeasible (fun i => (θ i).budget)

/-- Nonnegative payments (`no positive transfers`) on every strictly positive type profile. -/
@[expose] def HasNonnegPaymentOnPos (M : BudgetedMechanism ι) : Prop :=
  ∀ θ : ι → BidderType, (∀ i, (θ i).IsPos) → (M.outcome θ).HasNonnegPayment

/-- Individual rationality on every strictly positive type profile. -/
@[expose] def IsIROnPos (M : BudgetedMechanism ι) : Prop :=
  ∀ θ : ι → BidderType, (∀ i, (θ i).IsPos) → (M.outcome θ).IsIR (fun i => (θ i).val)

/-- Pareto optimality on every strictly positive type profile. -/
@[expose] def IsParetoOptimalOnPos (M : BudgetedMechanism ι) (m : ℝ) : Prop :=
  ∀ θ : ι → BidderType, (∀ i, (θ i).IsPos) →
    (M.outcome θ).IsParetoOptimal m (fun i => (θ i).val) (fun i => (θ i).budget)

/-- Dominant-strategy incentive compatibility for private `(val, budget)` types under hard budget
limits: no bidder `i` with true type `θ i` can strictly improve `val * alloc - payment` by
misreporting a strictly positive type `b'` whose resulting payment fits within `i`'s true budget
`(θ i).budget`. (Reports exceeding `(θ i).budget` yield utility `-∞` and are excluded.) -/
@[expose] def IsPrivateBudgetDSIC [DecidableEq ι] (M : BudgetedMechanism ι) : Prop :=
  ∀ (θ : ι → BidderType), (∀ k, (θ k).IsPos) →
    ∀ (i : ι) (b' : BidderType), b'.IsPos →
      (M.outcome (Function.update θ i b')).payment i ≤ (θ i).budget →
      (M.outcome (Function.update θ i b')).utility (fun k => (θ k).val) i ≤
        (M.outcome θ).utility (fun k => (θ k).val) i

/-- Convert a `BudgetedMechanism` at a fixed public budget profile `B` into a
`Cslib.GameTheory.SingleParameter.Mechanism`, reusing the single-parameter `IsDSIC` and `IsIR`
predicates. -/
@[expose] def toSingleParameter (M : BudgetedMechanism ι) (B : ι → ℝ) :
    SingleParameter.Mechanism ι where
  allocation v := (M.outcome (fun i => ⟨v i, B i⟩)).alloc
  payment v := (M.outcome (fun i => ⟨v i, B i⟩)).payment

end BudgetedMechanism

end Cslib.GameTheory.BudgetedAuction

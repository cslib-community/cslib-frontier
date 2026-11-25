/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Mechanism.BudgetedAuction.Basic
public import CslibFrontier.GameTheory.Mechanism.BudgetedAuction.DiscreteClinching
public import CslibFrontier.GameTheory.Mechanism.BudgetedAuction.Impossibility
public import CslibFrontier.GameTheory.Mechanism.BudgetedAuction.TwoBidderClinching
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked client tests for budget-constrained multi-unit auctions

Non-vacuity witnesses, boundary counterexamples, concrete trace evaluations, and a single
indivisible-item positive contrast mechanism (`cappedSecondPrice`) verifying that hard-budget
private-budget DSIC + discrete Pareto optimality **is** achievable when `alloc ∈ {0, 1}` (in sharp
contrast with the divisible impossibility theorem `not_exists_privateBudgetDSIC_isParetoOptimal`).
-/

public section

namespace CslibFrontierTests.GameTheory.BudgetedAuction

open Cslib.GameTheory.BudgetedAuction

/-! ### 1. Exact Pareto-optimality characterization witnesses -/

/-- Positive witness: `v = ![2, 5]`, `B = ![10, 4]`, `m = 3`, `alloc = ![1, 2]`, `payment = ![0, 4]`
is Pareto optimal because supply clears (`1 + 2 = 3`) and the higher bidder's budget is exhausted
(`4 = B 1`). -/
example :
    Outcome.IsParetoOptimal (ι := Fin 2) 3 ![2, 5] ![10, 4] ⟨![1, 2], ![0, 4]⟩ := by
  have hv : ∀ i : Fin 2, 0 ≤ (![(2 : ℝ), 5] i) := fun i => by fin_cases i <;> norm_num
  have hfeas : (⟨![1, 2], ![0, 4]⟩ : Outcome (Fin 2)).IsFeasible 3 :=
    ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]; norm_num⟩
  have hbf : (⟨![1, 2], ![0, 4]⟩ : Outcome (Fin 2)).IsBudgetFeasible ![10, 4] :=
    fun i => by fin_cases i <;> norm_num
  rw [Outcome.isParetoOptimal_iff hv hfeas hbf]
  refine ⟨fun _ => ⟨by simp [Fin.sum_univ_two]; norm_num, fun i hi => by
      fin_cases i <;> norm_num at hi⟩,
    fun i j _ hij => by
      fin_cases i <;> fin_cases j <;> simp at hij ⊢; linarith⟩

/-- Negative witness (slack supply): `alloc = ![1, 1]` leaves `1` unit unallocated when `m = 3` and
`v = ![2, 5]`, so it is **not** Pareto optimal. -/
example :
    ¬ Outcome.IsParetoOptimal (ι := Fin 2) 3 ![2, 5] ![10, 4] ⟨![1, 1], ![0, 4]⟩ := by
  intro h
  have hv : ∀ i : Fin 2, 0 ≤ (![(2 : ℝ), 5] i) := fun i => by fin_cases i <;> norm_num
  have hsum := ((Outcome.isParetoOptimal_iff hv h.1 h.2.1).mp h).1 ⟨0, by norm_num⟩ |>.1
  simp [Fin.sum_univ_two] at hsum
  norm_num at hsum

/-- Negative witness (`v i = 0` holding positive allocation): even though supply clears
(`1 + 2 = 3`) and bidder `1`'s budget is **exhausted** (`payment 1 = 4 = B 1`), giving `1` unit to
a zero-value bidder is **not** Pareto optimal (transfer it to bidder `1` at zero extra charge). -/
example :
    ¬ Outcome.IsParetoOptimal (ι := Fin 2) 3 ![0, 5] ![10, 4] ⟨![1, 2], ![0, 4]⟩ := by
  intro h
  have hv : ∀ i : Fin 2, 0 ≤ (![(0 : ℝ), 5] i) := fun i => by fin_cases i <;> norm_num
  have hz := ((Outcome.isParetoOptimal_iff hv h.1 h.2.1).mp h).1 ⟨1, by norm_num⟩ |>.2 0 rfl
  norm_num at hz

/-- Negative witness (unexhausted superior bidder): `payment 1 = 3 < 4 = B 1` while
`alloc 0 = 1 > 0` and `v 0 = 2 < 5 = v 1`. -/
example :
    ¬ Outcome.IsParetoOptimal (ι := Fin 2) 3 ![2, 5] ![10, 4] ⟨![1, 2], ![0, 3]⟩ := by
  intro h
  have hv : ∀ i : Fin 2, 0 ≤ (![(2 : ℝ), 5] i) := fun i => by fin_cases i <;> norm_num
  have heq := ((Outcome.isParetoOptimal_iff hv h.1 h.2.1).mp h).2 0 1 (by norm_num) (by norm_num)
  norm_num at heq

/-- Edge case (all-zero valuations): leaving supply `m = 3` unallocated is Pareto optimal when every
bidder has `v i = 0`. -/
example :
    Outcome.IsParetoOptimal (ι := Fin 2) 3 ![0, 0] ![10, 4] ⟨![0, 0], ![0, 0]⟩ := by
  have hv : ∀ i : Fin 2, 0 ≤ (![(0 : ℝ), 0] i) := fun i => by fin_cases i <;> norm_num
  have hfeas : (⟨![0, 0], ![0, 0]⟩ : Outcome (Fin 2)).IsFeasible 3 :=
    ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]⟩
  have hbf : (⟨![0, 0], ![0, 0]⟩ : Outcome (Fin 2)).IsBudgetFeasible ![10, 4] :=
    fun i => by fin_cases i <;> norm_num
  rw [Outcome.isParetoOptimal_iff hv hfeas hbf]
  exact ⟨fun ⟨i, hi⟩ => by fin_cases i <;> norm_num at hi,
    fun i j hi _ => by fin_cases i <;> norm_num at hi⟩

/-! ### 2. Impossibility theorem non-vacuity checks -/

example :
    ¬ ∃ M : BudgetedMechanism (Fin 2),
      M.IsFeasibleOnPos 1 ∧ M.HasNonnegPaymentOnPos ∧ M.IsBudgetFeasibleOnPos ∧
      M.IsIROnPos ∧ M.IsParetoOptimalOnPos 1 ∧ M.IsPrivateBudgetDSIC :=
  not_exists_privateBudgetDSIC_isParetoOptimal (m := 1) zero_lt_one (by decide)

example :
    ¬ ∃ M : BudgetedMechanism (Fin 3),
      M.IsFeasibleOnPos (7 / 2) ∧ M.HasNonnegPaymentOnPos ∧ M.IsBudgetFeasibleOnPos ∧
      M.IsIROnPos ∧ M.IsParetoOptimalOnPos (7 / 2) ∧ M.IsPrivateBudgetDSIC :=
  not_exists_privateBudgetDSIC_isParetoOptimal (m := 7 / 2) (by norm_num) (by decide)

/-! ### 3. Single indivisible-item contrast (`alloc ∈ {0, 1}`): capped second-price auction -/

/-- Effective capped bid `min val budget`. -/
private noncomputable def effBid (b : BidderType) : ℝ := min b.val b.budget

/-- Two-bidder single indivisible-item second-price auction on `min (val, budget)`, breaking ties
deterministically toward bidder `0` (`effBid (θ 1) ≤ effBid (θ 0)`). -/
private noncomputable def cappedSecondPrice : BudgetedMechanism (Fin 2) where
  outcome θ :=
    if effBid (θ 1) ≤ effBid (θ 0) then
      ⟨![1, 0], ![effBid (θ 1), 0]⟩
    else
      ⟨![0, 1], ![0, effBid (θ 0)]⟩

/-- `cappedSecondPrice` satisfies feasibility, nonnegative payments, budget feasibility, and IR. -/
example (θ : Fin 2 → BidderType) (hθ : ∀ i, (θ i).IsPos) :
    (cappedSecondPrice.outcome θ).IsFeasible 1 ∧
      (cappedSecondPrice.outcome θ).HasNonnegPayment ∧
      (cappedSecondPrice.outcome θ).IsBudgetFeasible (fun i => (θ i).budget) ∧
      (cappedSecondPrice.outcome θ).IsIR (fun i => (θ i).val) := by
  have he0 : 0 ≤ effBid (θ 0) := le_min (hθ 0).1.le (hθ 0).2.le
  have he1 : 0 ≤ effBid (θ 1) := le_min (hθ 1).1.le (hθ 1).2.le
  dsimp only [cappedSecondPrice]
  split_ifs with hw
  · refine ⟨⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]⟩,
      fun i => by fin_cases i <;> simp [he1],
      fun i => by
        fin_cases i
        · exact hw.trans (min_le_right _ _)
        · exact (hθ 1).2.le,
      fun i => by
        fin_cases i
        · have hle : effBid (θ 1) ≤ (θ 0).val := hw.trans (min_le_left (θ 0).val (θ 0).budget)
          exact sub_nonneg.mpr (by simpa [mul_one] using hle)
        · simp [Outcome.utility]⟩
  · have hlt : effBid (θ 0) < effBid (θ 1) := lt_of_not_ge hw
    refine ⟨⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]⟩,
      fun i => by fin_cases i <;> simp [he0],
      fun i => by
        fin_cases i
        · exact (hθ 0).2.le
        · exact hlt.le.trans (min_le_right _ _),
      fun i => by
        fin_cases i
        · simp [Outcome.utility]
        · have hle : effBid (θ 0) ≤ (θ 1).val := hlt.le.trans (min_le_left (θ 1).val (θ 1).budget)
          exact sub_nonneg.mpr (by simpa [mul_one] using hle)⟩

/-- Under **non-overreportable** (`b'.budget ≤ (θ i).budget`, verifiable deposit) budgets,
`cappedSecondPrice` IS dominant-strategy truthful on all profiles. -/
example (θ : Fin 2 → BidderType) (i : Fin 2) (b' : BidderType)
    (hcap : b'.budget ≤ (θ i).budget) :
    (cappedSecondPrice.outcome (Function.update θ i b')).utility (fun k => (θ k).val) i ≤
      (cappedSecondPrice.outcome θ).utility (fun k => (θ k).val) i := by
  fin_cases i
  · have eval : ∀ x : BidderType,
        (cappedSecondPrice.outcome (Function.update θ 0 x)).utility (fun k => (θ k).val) 0 =
          if effBid (θ 1) ≤ effBid x then (θ 0).val - effBid (θ 1) else 0 := by
      intro x
      dsimp only [cappedSecondPrice, Outcome.utility]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), Function.update_self]
      split_ifs <;> simp
    have h0 := eval b'
    have h1 := eval (θ 0)
    rw [Function.update_eq_self] at h1
    change (cappedSecondPrice.outcome (Function.update θ 0 b')).utility (fun k => (θ k).val) 0 ≤
      (cappedSecondPrice.outcome θ).utility (fun k => (θ k).val) 0
    rw [h0, h1]
    by_cases hdev : effBid (θ 1) ≤ effBid b' <;> by_cases htrue : effBid (θ 1) ≤ effBid (θ 0)
    · rw [ite_eq_left hdev, ite_eq_left htrue]
    · rw [ite_eq_left hdev, ite_eq_right htrue]
      have hlt : effBid (θ 0) < effBid (θ 1) := lt_of_not_ge htrue
      have hb_le : effBid (θ 1) ≤ (θ 0).budget :=
        hdev.trans ((min_le_right b'.val b'.budget).trans hcap)
      have hv_le : (θ 0).val ≤ effBid (θ 1) := by
        by_contra h
        exact lt_irrefl _ (lt_of_lt_of_le hlt (le_min (lt_of_not_ge h).le hb_le))
      linarith
    · rw [ite_eq_right hdev, ite_eq_left htrue]
      have := htrue.trans (min_le_left (θ 0).val (θ 0).budget); linarith
    · rw [ite_eq_right hdev, ite_eq_right htrue]
  · have eval : ∀ x : BidderType,
        (cappedSecondPrice.outcome (Function.update θ 1 x)).utility (fun k => (θ k).val) 1 =
          if effBid x ≤ effBid (θ 0) then 0 else (θ 1).val - effBid (θ 0) := by
      intro x
      dsimp only [cappedSecondPrice, Outcome.utility]
      rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), Function.update_self]
      split_ifs <;> simp
    have h0 := eval b'
    have h1 := eval (θ 1)
    rw [Function.update_eq_self] at h1
    change (cappedSecondPrice.outcome (Function.update θ 1 b')).utility (fun k => (θ k).val) 1 ≤
      (cappedSecondPrice.outcome θ).utility (fun k => (θ k).val) 1
    rw [h0, h1]
    by_cases hdev : effBid b' ≤ effBid (θ 0) <;> by_cases htrue : effBid (θ 1) ≤ effBid (θ 0)
    · rw [ite_eq_left hdev, ite_eq_left htrue]
    · rw [ite_eq_left hdev, ite_eq_right htrue]
      have hlt : effBid (θ 0) < effBid (θ 1) := lt_of_not_ge htrue
      have := hlt.le.trans (min_le_left (θ 1).val (θ 1).budget); linarith
    · rw [ite_eq_right hdev, ite_eq_left htrue]
      have hlt : effBid (θ 0) < effBid b' := lt_of_not_ge hdev
      have hb_lt : effBid (θ 0) < (θ 1).budget :=
        lt_of_lt_of_le hlt ((min_le_right b'.val b'.budget).trans hcap)
      have hv_le : (θ 1).val ≤ effBid (θ 0) := by
        by_contra h
        exact absurd (lt_min (lt_of_not_ge h) hb_lt) (not_lt.mpr htrue)
      linarith
    · rw [ite_eq_right hdev, ite_eq_right htrue]

/-- Conversely, when budgets may be **over-reported** (no upfront escrow, `IsPrivateBudgetDSIC`),
even single-item `cappedSecondPrice` fails truthfulness on the tie `θ = ![⟨5, 1⟩, ⟨3, 1⟩]`: bidder
`1` reports `⟨3, 2⟩`, wins the item paying `effBid (θ 0) = 1 ≤ 1` (true budget), and raises its
utility from `0` to `2`. -/
example : ¬ cappedSecondPrice.IsPrivateBudgetDSIC := by
  intro hic
  let θ : Fin 2 → BidderType := ![⟨5, 1⟩, ⟨3, 1⟩]
  let b' : BidderType := ⟨3, 2⟩
  have hθ : ∀ k, (θ k).IsPos := fun k => by
    fin_cases k
    · exact ⟨by norm_num [θ], by norm_num [θ]⟩
    · exact ⟨by norm_num [θ], by norm_num [θ]⟩
  have hb' : b'.IsPos := ⟨by norm_num [b'], by norm_num [b']⟩
  have hdev_eq : effBid (Function.update θ 1 b' 1) = 2 := by
    rw [Function.update_self]; exact min_eq_right (by norm_num [b'])
  have h0_eq : effBid (Function.update θ 1 b' 0) = 1 := by
    rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    exact min_eq_right (by norm_num [θ])
  have hdev_pay : (cappedSecondPrice.outcome (Function.update θ 1 b')).payment 1 = 1 := by
    dsimp only [cappedSecondPrice]
    rw [ite_eq_right (by rw [hdev_eq, h0_eq]; norm_num)]
    exact h0_eq
  have hle := hic θ hθ 1 b' hb' (by rw [hdev_pay]; exact le_rfl)
  have ht_u : (cappedSecondPrice.outcome θ).utility (fun k => (θ k).val) 1 = 0 := by
    dsimp only [Outcome.utility, cappedSecondPrice]
    have h0 : effBid (θ 0) = 1 := min_eq_right (by norm_num [θ])
    have h1 : effBid (θ 1) = 1 := min_eq_right (by norm_num [θ])
    rw [ite_eq_left (by rw [h0, h1])]
    simp
  have hd_u : (cappedSecondPrice.outcome (Function.update θ 1 b')).utility
      (fun k => (θ k).val) 1 = 2 := by
    dsimp only [Outcome.utility, cappedSecondPrice]
    rw [ite_eq_right (by rw [hdev_eq, h0_eq]; norm_num)]
    have hval1 : (θ 1).val = 3 := rfl
    rw [hval1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_one, h0_eq]
    norm_num
  linarith

/-- Tie-breaking distinction for `1` indivisible unit: at `θ = ![⟨2, 1⟩, ⟨1, 10⟩]`, awarding to
bidder `1` for payment `1` IS strictly Pareto-dominated by awarding to bidder `0` (`val = 2`) for
payment `1` (matching `cappedSecondPrice`). -/
example :
    let θ : Fin 2 → BidderType := ![⟨2, 1⟩, ⟨1, 10⟩]
    let bad : Outcome (Fin 2) := ⟨![0, 1], ![0, 1]⟩
    let good : Outcome (Fin 2) := ⟨![1, 0], ![1, 0]⟩
    cappedSecondPrice.outcome θ = good ∧
      good.ParetoDominates 1 (fun i => (θ i).val) (fun i => (θ i).budget) bad := by
  refine ⟨?_, ?_⟩
  · simp [cappedSecondPrice, effBid]
  · refine ⟨⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_two]⟩,
      fun i => by fin_cases i <;> norm_num,
      fun i => by fin_cases i <;> simp [Outcome.utility],
      by simp [Outcome.revenue, Fin.sum_univ_two],
      Or.inl ⟨0, by simp [Outcome.utility]⟩⟩

/-! ### 4. Continuous 2-bidder adaptive clinching auction (`twoBidderClinching`) witnesses -/

/-- Zero valuations return zero allocation and zero payment. -/
example : twoBidderClinching 2 ![1, 3] ![0, 0] = ⟨![0, 0], ![0, 0]⟩ :=
  twoBidderClinching_zero_zero 2 ![1, 3]

/-- Phase 0 evaluation (`m = 1, B = ![1, 2], v = ![1/2, 3]`): bidder `1` takes supply `1` at
price `1/2`. -/
example :
    (twoBidderClinching 1 ![1, 2] ![1 / 2, 3]).alloc 0 = 0 ∧
      (twoBidderClinching 1 ![1, 2] ![1 / 2, 3]).alloc 1 = 1 ∧
      (twoBidderClinching 1 ![1, 2] ![1 / 2, 3]).payment 0 = 0 ∧
      (twoBidderClinching 1 ![1, 2] ![1 / 2, 3]).payment 1 = 1 / 2 :=
  by
    have h := twoBidderClinching_phase0_lt (m := 1) (B := ![1, 2]) (v := ![1 / 2, 3])
      zero_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h

/-- Swapped public budgets (`B 1 < B 0`, `B = ![2, 1], v = ![3, 1/2]`): bidder `0` takes supply `1`
at price `1/2`. -/
example :
    (twoBidderClinching 1 ![2, 1] ![3, 1 / 2]).alloc 0 = 1 ∧
      (twoBidderClinching 1 ![2, 1] ![3, 1 / 2]).payment 0 = 1 / 2 := by
  have hs := twoBidderClinching_swap 1 (B := ![2, 1]) (v := ![3, 1 / 2]) (by norm_num) 0
  have hp := twoBidderClinching_phase0_lt (m := 1) (B := ![1, 2]) (v := ![1 / 2, 3])
    zero_lt_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · simpa using hs.1.trans hp.2.1
  · simpa using hs.2.trans hp.2.2.2

/-- Asymmetric-budget continuous clinching satisfies DSIC, IR, normalization, budget feasibility,
exact market clearing, and Pareto optimality simultaneously. -/
example :
    (twoBidderClinchingSP 2 ![3, 1]).IsDSIC ∧
      (twoBidderClinchingSP 2 ![3, 1]).IsIR ∧
      (twoBidderClinchingSP 2 ![3, 1]).IsNormalized ∧
      (twoBidderClinching 2 ![3, 1] ![4, 5]).IsParetoOptimal 2 ![4, 5] ![3, 1] ∧
      ∑ i, (twoBidderClinching 2 ![3, 1] ![4, 5]).alloc i = 2 := by
  have hB : ∀ i : Fin 2, 0 < (![(3 : ℝ), 1] i) := fun i => by fin_cases i <;> norm_num
  have hv : ∀ i : Fin 2, 0 ≤ (![(4 : ℝ), 5] i) := fun i => by fin_cases i <;> norm_num
  exact ⟨twoBidderClinchingSP_isDSIC (by norm_num) hB,
    twoBidderClinchingSP_isIR (by norm_num) hB,
    twoBidderClinchingSP_isNormalized (by norm_num) hB,
    twoBidderClinching_isParetoOptimal (by norm_num) hB hv,
    twoBidderClinching_sum_alloc (by norm_num) hB hv ⟨0, by norm_num⟩⟩

/-- Quantitative `m = 2` budget-manipulation check via `twoBidderClinching_budget_manipulation`:
bidder `1` (`⟨1, 1⟩` against `⟨5, 1⟩`) raises its utility from `1 / 4` to `1 - Real.log 2` while
paying `Real.log 2 ≤ 1`. -/
theorem twoBidderClinching_two_budget_manipulation :
    let θ : Fin 2 → BidderType := ![⟨5, 1⟩, ⟨1, 1⟩]
    let b' : BidderType := ⟨1, 1 + Real.log 2⟩
    ((twoBidderClinchingMechanism 2).outcome θ).utility (fun k => (θ k).val) 1 = 1 / 4 ∧
      ((twoBidderClinchingMechanism 2).outcome (Function.update θ 1 b')).payment 1 = Real.log 2 ∧
      ((twoBidderClinchingMechanism 2).outcome (Function.update θ 1 b')).utility
        (fun k => (θ k).val) 1 = 1 - Real.log 2 := by
  have h := twoBidderClinching_budget_manipulation (m := 2) (by norm_num)
  norm_num at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- Private-budget manipulation witness (`twoBidderClinching` is NOT `IsPrivateBudgetDSIC` for
`m = 1`). -/
example : ¬ (twoBidderClinchingMechanism 1).IsPrivateBudgetDSIC :=
  twoBidderClinching_not_privateBudgetDSIC zero_lt_one

/-! ### 5. Discrete `n`-bidder ascending clinching auction (`clinchAuction`) tests -/

/-- Exact 2-round divisible trace (`m = 4, prices = [1, 2], B = ![2, 4], v = ![1, 5]`):
* At `p = 1`: active demands `d = ![2, 4]` (`∑ d = 6`), bidder `0` clinches `0`, bidder `1` clinches
  `min 4 (4 - 2) = 2` paying `2`; remaining supply `2`, remaining budget `![2, 2]`.
* At `p = 2`: bidder `0` exits (`1 < 2`), bidder `1` demands `2 / 2 = 1` and clinches `1` paying
  `2` (exhausting its budget `2 + 2 = 4`!). -/
example :
    (clinchAuction (DemandRule.divisible (Fin 2)) 4 [1, 2] ![2, 4] ![1, 5]).alloc 0 = 0 ∧
      (clinchAuction (DemandRule.divisible (Fin 2)) 4 [1, 2] ![2, 4] ![1, 5]).alloc 1 = 3 ∧
      (clinchAuction (DemandRule.divisible (Fin 2)) 4 [1, 2] ![2, 4] ![1, 5]).payment 0 = 0 ∧
      (clinchAuction (DemandRule.divisible (Fin 2)) 4 [1, 2] ![2, 4] ![1, 5]).payment 1 = 4 := by
  simp [clinchAuction, clinchRun, clinchStep, clinchAmt, clinchDemands, DemandRule.divisible,
    Fin.sum_univ_two]
  norm_num

/-- Three-bidder discrete divisible auction is DSIC, IR, normalized, budget-feasible, and clears or
exhausts the highest bidder's budget at `p = 3`. -/
example :
    (clinchMechanism (DemandRule.divisible (Fin 3)) 5 [1, 2, 3] ![2, 3, 4]).IsDSIC ∧
      (clinchMechanism (DemandRule.divisible (Fin 3)) 5 [1, 2, 3] ![2, 3, 4]).IsIR ∧
      (clinchMechanism (DemandRule.divisible (Fin 3)) 5 [1, 2, 3] ![2, 3, 4]).IsNormalized ∧
      ((∑ k, (clinchAuction (DemandRule.divisible (Fin 3)) 5 [1, 2, 3]
          ![2, 3, 4] ![1, 2, 10]).alloc k = 5) ∨
        (clinchAuction (DemandRule.divisible (Fin 3)) 5 [1, 2, 3]
          ![2, 3, 4] ![1, 2, 10]).payment 2 = 4) := by
  have hpos : ∀ p ∈ ([1, 2, 3] : List ℝ), 0 < p := by simp
  have hsort : ([1, 2, 3] : List ℝ).Pairwise (· ≤ ·) := by simp; norm_num
  have hB : ∀ i : Fin 3, 0 ≤ (![(2 : ℝ), 3, 4] i) := fun i => by fin_cases i <;> norm_num
  refine ⟨clinchMechanism_isDSIC _ 5 hsort hpos hB,
    clinchMechanism_isIR _ 5 hpos hB,
    clinchMechanism_isNormalized _ 5 hpos hB,
    clinchAuction_clear_or_exhaust_divisible (by norm_num) hpos hB
      ⟨3, by simp, by norm_num, fun j hj => by fin_cases j <;> simp at hj ⊢; norm_num⟩⟩

/-- Indivisible `⌊r / p⌋` and capacity-capped `DemandRule` instances are DSIC. -/
example :
    (clinchMechanism (DemandRule.indivisible (Fin 2)) 3 [1, 2] ![5, 5]).IsDSIC ∧
      (clinchMechanism (DemandRule.capped (ι := Fin 2) ![2, 2]) 3 [1, 2] ![10, 10]).IsDSIC := by
  have hpos : ∀ p ∈ ([1, 2] : List ℝ), 0 < p := by simp
  have hsort : ([1, 2] : List ℝ).Pairwise (· ≤ ·) := by simp
  exact ⟨clinchMechanism_isDSIC _ 3 hsort hpos (fun i => by fin_cases i <;> norm_num),
    clinchMechanism_isDSIC _ 3 hsort hpos (fun i => by fin_cases i <;> norm_num)⟩

end CslibFrontierTests.GameTheory.BudgetedAuction

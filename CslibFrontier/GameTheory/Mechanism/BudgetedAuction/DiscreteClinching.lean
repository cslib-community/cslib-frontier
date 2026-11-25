/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.BudgetedAuction.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Discrete ascending clinching auction with public budgets

Implements and verifies the general `n`-bidder discrete ascending clinching auction along an
arbitrary ascending schedule of strictly positive prices `prices : List ℝ`, parameterized by a
budget-respecting active-demand rule `DemandRule ι` ([Ausubel2004]; [DobzinskiLaviNisan2012];
primary PDFs not inspected, theorem/page locators unverified).

At each round price `p > 0`:
* Each active bidder `k` (`p ≤ v k`) submits demand `d k = rule.demand k p (alloc k) (B k - pay k)`
  bounded so that `d k * p ≤ B k - pay k`; exited bidders (`v k < p`) submit demand `0`.
* Each bidder clinches `c k = min (d k) (max 0 (remSupply - ∑_{j ≠ k} d j))` units at price `p`.

This single parameterized algorithm covers:
* `DemandRule.divisible`: divisible budget-constrained demands `r / p`.
* `DemandRule.indivisible`: integer multi-unit demands `⌊r / p⌋`.
* `DemandRule.capped`: flat-valuation capacity-capped demands `min (max 0 (cap i - a)) (r / p)`
  (Ausubel's ascending auction under hard unit caps and budgets).

We prove supply feasibility (`clinchAuction_isFeasible`), nonnegative payments
(`clinchAuction_hasNonnegPayment`), hard budget feasibility (`clinchAuction_isBudgetFeasible`),
individual rationality (`clinchMechanism_isIR`), normalization (`clinchMechanism_isNormalized`),
**dominant-strategy incentive compatibility in valuations** (`clinchMechanism_isDSIC`), and a
market-clearing / budget-exhaustion guarantee whenever some posted price strictly separates the
unique highest bidder (`clinchAuction_clear_or_exhaust_divisible`).

## Main definitions

* `Cslib.GameTheory.BudgetedAuction.DemandRule`: budget-respecting demand rule, with constructors
  `divisible`, `indivisible`, and `capped`.
* `Cslib.GameTheory.BudgetedAuction.ClinchState`: round-by-round `(alloc, payment, remSupply)`
  auction state.
* `Cslib.GameTheory.BudgetedAuction.clinchAuction`: discrete `n`-bidder ascending clinching auction
  over `prices : List ℝ`.
* `Cslib.GameTheory.BudgetedAuction.clinchMechanism`: `SingleParameter.Mechanism ι` wrapper for
  fixed public budgets `B`.

## Main results

* `Cslib.GameTheory.BudgetedAuction.clinchAuction_isFeasible`
* `Cslib.GameTheory.BudgetedAuction.clinchAuction_hasNonnegPayment`
* `Cslib.GameTheory.BudgetedAuction.clinchAuction_isBudgetFeasible`
* `Cslib.GameTheory.BudgetedAuction.clinchMechanism_isIR`
* `Cslib.GameTheory.BudgetedAuction.clinchMechanism_isNormalized`
* `Cslib.GameTheory.BudgetedAuction.clinchMechanism_isDSIC`
* `Cslib.GameTheory.BudgetedAuction.clinchAuction_clear_or_exhaust_divisible`

## References

* [L. M. Ausubel, *An Efficient Ascending-Bid Auction for Multiple Objects*][Ausubel2004]
  (primary PDF not inspected; theorem/page locators unverified)
* [S. Dobzinski, R. Lavi, and N. Nisan,
  *Multi-unit auctions with budget limits*][DobzinskiLaviNisan2012]
  (primary PDF not inspected; theorem/page locators unverified)
-/

public section

namespace Cslib.GameTheory.BudgetedAuction

/-- A budget-respecting active-demand rule for the discrete ascending clinching auction. Given
bidder `i`, positive round price `p`, already-allocated quantity `a`, and remaining budget `r`,
`demand i p a r` returns bidder `i`'s active demand while `p ≤ v i`. -/
structure DemandRule (ι : Type*) where
  /-- Active demand at price `p`, cumulative allocation `a`, and remaining budget `r`. -/
  demand : ι → ℝ → ℝ → ℝ → ℝ
  /-- Active demand is nonnegative whenever `p > 0` and `r ≥ 0`. -/
  demand_nonneg : ∀ i p a r, 0 < p → 0 ≤ r → 0 ≤ demand i p a r
  /-- Demanding at price `p` never exceeds remaining budget `r`. -/
  demand_cost_le : ∀ i p a r, 0 < p → 0 ≤ r → demand i p a r * p ≤ r

namespace DemandRule

/-- Divisible demand rule `r / p`: a bidder demands as many fractional units as its remaining
budget `r` can purchase at price `p`. -/
@[expose] noncomputable def divisible (ι : Type*) : DemandRule ι where
  demand _ p _ r := r / p
  demand_nonneg _ _ _ _ hp hr := div_nonneg hr hp.le
  demand_cost_le _ p _ r hp _ := by rw [div_mul_cancel₀ _ hp.ne']

/-- Indivisible (integer) demand rule `⌊r / p⌋`: a bidder demands as many whole units as its
remaining budget `r` can purchase at price `p`. -/
@[expose] noncomputable def indivisible (ι : Type*) : DemandRule ι where
  demand _ p _ r := (Nat.floor (r / p) : ℝ)
  demand_nonneg _ _ _ _ _ _ := Nat.cast_nonneg _
  demand_cost_le _ p _ r hp hr := by
    calc
      (Nat.floor (r / p) : ℝ) * p ≤ (r / p) * p :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hr hp.le)) hp.le
      _ = r := div_mul_cancel₀ _ hp.ne'

/-- Capacity-capped divisible demand rule `min (max 0 (cap i - a)) (r / p)`, capturing Ausubel's
ascending auction with flat per-unit valuation up to bidder-specific quantity limit `cap i` and
hard budget limit `B i`. -/
@[expose] noncomputable def capped {ι : Type*} (cap : ι → ℝ) : DemandRule ι where
  demand i p a r := min (max 0 (cap i - a)) (r / p)
  demand_nonneg _ _ _ _ hp hr := le_min (le_max_left _ _) (div_nonneg hr hp.le)
  demand_cost_le _ p _ r hp _ := by
    calc
      min (max 0 _) (r / p) * p ≤ (r / p) * p :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le
      _ = r := div_mul_cancel₀ _ hp.ne'

end DemandRule

/-- Round-by-round state tracked by the discrete ascending clinching auction. -/
structure ClinchState (ι : Type*) where
  /-- Cumulative allocation awarded so far to each bidder. -/
  alloc : ι → ℝ
  /-- Cumulative payment accrued so far by each bidder. -/
  payment : ι → ℝ
  /-- Unallocated residual supply remaining to be sold. -/
  remSupply : ℝ

section DiscreteClinching

variable {ι : Type*} [Fintype ι]

/-- Active demand vector at round price `p`: `rule.demand k p (alloc k) (B k - pay k)` when
`p ≤ v k`, and `0` otherwise. -/
@[expose] noncomputable def clinchDemands (rule : DemandRule ι) (B v : ι → ℝ) (p : ℝ)
    (s : ClinchState ι) (k : ι) : ℝ :=
  open scoped Classical in
  if p ≤ v k then rule.demand k p (s.alloc k) (B k - s.payment k) else 0

/-- Quantity clinched by bidder `k` from demand profile `d` and remaining supply `remSupply`:
`min (d k) (max 0 (remSupply - ∑_{j ≠ k} d j))`. -/
@[expose] noncomputable def clinchAmt (d : ι → ℝ) (remSupply : ℝ) (k : ι) : ℝ :=
  min (d k) (max 0 (remSupply - ((∑ j, d j) - d k)))

/-- Single ascending-clock clinching round at price `p`. -/
@[expose] noncomputable def clinchStep (rule : DemandRule ι) (B v : ι → ℝ) (p : ℝ)
    (s : ClinchState ι) : ClinchState ι :=
  let d := clinchDemands rule B v p s
  let c := clinchAmt d s.remSupply
  { alloc := fun k => s.alloc k + c k
    payment := fun k => s.payment k + p * c k
    remSupply := s.remSupply - ∑ k, c k }

/-- Iterate `clinchStep` over a list of ascending prices starting from state `s`. -/
@[expose] noncomputable def clinchRun (rule : DemandRule ι) (B v : ι → ℝ) :
    List ℝ → ClinchState ι → ClinchState ι
  | [], s => s
  | p :: ps, s => clinchRun rule B v ps (clinchStep rule B v p s)

/-- Discrete `n`-bidder ascending clinching auction ([Ausubel2004]; [DobzinskiLaviNisan2012],
primary PDFs not inspected): starting from supply `m` and fixed public budgets `B`, runs
`clinchRun` along the ascending price list `prices`. -/
@[expose] noncomputable def clinchAuction (rule : DemandRule ι) (m : ℝ) (prices : List ℝ)
    (B v : ι → ℝ) : Outcome ι :=
  let st := clinchRun rule B v prices ⟨fun _ => 0, fun _ => 0, m⟩
  ⟨st.alloc, st.payment⟩

/-- `clinchAuction` packaged as a `SingleParameter.Mechanism ι` for fixed public budgets `B`. -/
@[expose] noncomputable def clinchMechanism (rule : DemandRule ι) (m : ℝ) (prices : List ℝ)
    (B : ι → ℝ) : SingleParameter.Mechanism ι where
  allocation v := (clinchAuction rule m prices B v).alloc
  payment v := (clinchAuction rule m prices B v).payment

private def ClinchState.Valid (m : ℝ) (B : ι → ℝ) (s : ClinchState ι) : Prop :=
  (∀ i, 0 ≤ s.alloc i) ∧ (∀ i, 0 ≤ s.payment i) ∧ (∀ i, s.payment i ≤ B i) ∧
    0 ≤ s.remSupply ∧ ∑ i, s.alloc i + s.remSupply = m

private theorem clinchAmt_nonneg {d : ι → ℝ} (hd : ∀ k, 0 ≤ d k) (S : ℝ) (k : ι) :
    0 ≤ clinchAmt d S k :=
  le_min (hd k) (le_max_left _ _)

private theorem clinchAmt_le_demand (d : ι → ℝ) (S : ℝ) (k : ι) :
    clinchAmt d S k ≤ d k :=
  min_le_left _ _

private theorem sum_clinchAmt_le {d : ι → ℝ} (hd : ∀ k, 0 ≤ d k) {S : ℝ} (hS : 0 ≤ S) :
    ∑ k, clinchAmt d S k ≤ S := by
  classical
  set D := ∑ j, d j
  by_cases hDS : D ≤ S
  · calc
      ∑ k, clinchAmt d S k ≤ ∑ k, d k := Finset.sum_le_sum fun k _ => clinchAmt_le_demand d S k
      _ = D := rfl
      _ ≤ S := hDS
  · have hlt : S < D := lt_of_not_ge hDS
    let A : Finset ι := Finset.univ.filter fun k => 0 < S - (D - d k)
    have hzero_out : ∀ k ∈ Finset.univ, k ∉ A → clinchAmt d S k = 0 := by
      intro k _ hk
      have hnp : S - (D - d k) ≤ 0 := by
        simpa [A, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hk
      dsimp only [clinchAmt]
      rw [max_eq_left hnp]
      exact min_eq_right (hd k)
    have hsum_eq : ∑ k, clinchAmt d S k = ∑ k ∈ A, clinchAmt d S k :=
      (Finset.sum_subset (Finset.filter_subset _ _) hzero_out).symm
    rw [hsum_eq]
    by_cases hAne : A.Nonempty
    · have hcard : (1 : ℝ) ≤ A.card := by exact_mod_cast hAne.card_pos
      have hterm : ∀ k ∈ A, clinchAmt d S k ≤ d k - (D - S) := by
        intro k hk
        have hpos : 0 < S - (D - d k) := (Finset.mem_filter.mp hk).2
        have hle : clinchAmt d S k ≤ max 0 (S - (D - d k)) := min_le_right _ _
        rw [max_eq_right hpos.le] at hle
        linarith
      have hsub_sum : ∑ k ∈ A, d k ≤ D :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => hd k
      have hbound : ∑ k ∈ A, (d k - (D - S)) = (∑ k ∈ A, d k) - (A.card : ℝ) * (D - S) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      have hmul : 1 * (D - S) ≤ (A.card : ℝ) * (D - S) :=
        mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hlt.le)
      calc
        ∑ k ∈ A, clinchAmt d S k ≤ ∑ k ∈ A, (d k - (D - S)) := Finset.sum_le_sum hterm
        _ = (∑ k ∈ A, d k) - (A.card : ℝ) * (D - S) := hbound
        _ ≤ D - 1 * (D - S) := by linarith
        _ = S := by linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.sum_empty]
      exact hS

omit [Fintype ι] in
private theorem clinchDemands_nonneg (rule : DemandRule ι) (B v : ι → ℝ) {p : ℝ} (hp : 0 < p)
    (s : ClinchState ι) (hrem : ∀ k, s.payment k ≤ B k) (k : ι) :
    0 ≤ clinchDemands rule B v p s k := by
  dsimp only [clinchDemands]
  split_ifs
  · exact rule.demand_nonneg k p (s.alloc k) (B k - s.payment k) hp (sub_nonneg.mpr (hrem k))
  · exact le_rfl

private theorem clinchStep_payment_le (rule : DemandRule ι) (B v : ι → ℝ) {p : ℝ} (hp : 0 < p)
    (s : ClinchState ι) (hbf : ∀ k, s.payment k ≤ B k) (k : ι) :
    (clinchStep rule B v p s).payment k ≤ B k := by
  dsimp only [clinchStep]
  have hcost : clinchDemands rule B v p s k * p ≤ B k - s.payment k := by
    dsimp only [clinchDemands]
    split_ifs
    · exact rule.demand_cost_le k p (s.alloc k) (B k - s.payment k) hp (sub_nonneg.mpr (hbf k))
    · rw [zero_mul]; exact sub_nonneg.mpr (hbf k)
  have hle : p * clinchAmt (clinchDemands rule B v p s) s.remSupply k ≤
      clinchDemands rule B v p s k * p := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (clinchAmt_le_demand _ _ k) hp.le
  linarith

private theorem clinchStep_valid (rule : DemandRule ι) {m : ℝ} (B v : ι → ℝ) {p : ℝ} (hp : 0 < p)
    (s : ClinchState ι) (hs : s.Valid m B) :
    (clinchStep rule B v p s).Valid m B := by
  obtain ⟨ha, hpay, hbf, hS, hbal⟩ := hs
  have hd_nn : ∀ k, 0 ≤ clinchDemands rule B v p s k := clinchDemands_nonneg rule B v hp s hbf
  have hc_nn : ∀ k, 0 ≤ clinchAmt (clinchDemands rule B v p s) s.remSupply k :=
    clinchAmt_nonneg hd_nn s.remSupply
  refine ⟨fun i => add_nonneg (ha i) (hc_nn i),
    fun i => add_nonneg (hpay i) (mul_nonneg hp.le (hc_nn i)),
    clinchStep_payment_le rule B v hp s hbf,
    sub_nonneg.mpr (sum_clinchAmt_le hd_nn hS), ?_⟩
  dsimp only [clinchStep]
  rw [Finset.sum_add_distrib]
  linarith

private theorem clinchRun_valid (rule : DemandRule ι) {m : ℝ} (B v : ι → ℝ) :
    ∀ (ps : List ℝ), (∀ p ∈ ps, 0 < p) →
      ∀ (s : ClinchState ι), s.Valid m B → (clinchRun rule B v ps s).Valid m B
  | [], _, _, hs => hs
  | p :: ps, hpos, s, hs =>
    clinchRun_valid rule B v ps (fun q hq => hpos q (List.mem_cons_of_mem p hq))
      (clinchStep rule B v p s) (clinchStep_valid rule B v (hpos p (List.mem_cons_self ..)) s hs)

private theorem clinchRun_mono_rem (rule : DemandRule ι) (B v : ι → ℝ) :
    ∀ (ps : List ℝ), (∀ p ∈ ps, 0 < p) →
      ∀ (s : ClinchState ι), (∀ k, s.payment k ≤ B k) →
        (∀ i, s.alloc i ≤ (clinchRun rule B v ps s).alloc i) ∧
        (∀ i, s.payment i ≤ (clinchRun rule B v ps s).payment i) ∧
        (clinchRun rule B v ps s).remSupply ≤ s.remSupply
  | [], _, _, _ => ⟨fun _ => le_rfl, fun _ => le_rfl, le_rfl⟩
  | p :: ps, hpos, s, hbf => by
    have hp : 0 < p := hpos p (List.mem_cons_self ..)
    have hd_nn := clinchDemands_nonneg rule B v hp s hbf
    have hc_nn := clinchAmt_nonneg hd_nn s.remSupply
    have ih := clinchRun_mono_rem rule B v ps (fun q hq => hpos q (List.mem_cons_of_mem p hq))
      (clinchStep rule B v p s) (clinchStep_payment_le rule B v hp s hbf)
    refine ⟨fun i => le_trans (by dsimp only [clinchStep]; linarith [hc_nn i]) (ih.1 i),
      fun i => le_trans
        (by dsimp only [clinchStep]; linarith [mul_nonneg hp.le (hc_nn i)]) (ih.2.1 i),
      le_trans ih.2.2 ?_⟩
    dsimp only [clinchStep]
    have hsum_nn : 0 ≤ ∑ k : ι, clinchAmt (clinchDemands rule B v p s) s.remSupply k :=
      Finset.sum_nonneg fun k _ => hc_nn k
    linarith

private theorem clinchRun_frozen (rule : DemandRule ι) (B v : ι → ℝ) (i : ι) :
    ∀ (ps : List ℝ), (∀ p ∈ ps, 0 < p) → (∀ p ∈ ps, v i < p) →
      ∀ (s : ClinchState ι), (∀ k, s.payment k ≤ B k) →
        (clinchRun rule B v ps s).alloc i = s.alloc i ∧
        (clinchRun rule B v ps s).payment i = s.payment i
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | p :: ps, hpos, hlt, s, hbf => by
    have hp : 0 < p := hpos p (List.mem_cons_self ..)
    have hvi : ¬ (p ≤ v i) := not_le.mpr (hlt p (List.mem_cons_self ..))
    have hdi0 : clinchDemands rule B v p s i = 0 := by
      dsimp only [clinchDemands]
      split_ifs; rfl
    have hci0 : clinchAmt (clinchDemands rule B v p s) s.remSupply i = 0 := by
      dsimp only [clinchAmt]
      rw [hdi0]
      exact min_eq_left (le_max_left _ _)
    have ih := clinchRun_frozen rule B v i ps
      (fun q hq => hpos q (List.mem_cons_of_mem p hq))
      (fun q hq => hlt q (List.mem_cons_of_mem p hq))
      (clinchStep rule B v p s) (clinchStep_payment_le rule B v hp s hbf)
    refine ⟨?_, ?_⟩
    · rw [clinchRun, ih.1]; dsimp only [clinchStep]; rw [hci0, add_zero]
    · rw [clinchRun, ih.2]; dsimp only [clinchStep]; rw [hci0, mul_zero, add_zero]

private theorem clinchRun_util_ge (rule : DemandRule ι) (B v : ι → ℝ) (i : ι) :
    ∀ (ps : List ℝ), (∀ p ∈ ps, 0 < p) →
      ∀ (s : ClinchState ι), (∀ k, s.payment k ≤ B k) →
        v i * s.alloc i - s.payment i ≤
          v i * (clinchRun rule B v ps s).alloc i - (clinchRun rule B v ps s).payment i
  | [], _, _, _ => le_rfl
  | p :: ps, hpos, s, hbf => by
    have hp : 0 < p := hpos p (List.mem_cons_self ..)
    have hd_nn := clinchDemands_nonneg rule B v hp s hbf
    have hc_nn := clinchAmt_nonneg hd_nn s.remSupply i
    have hstep_gain : v i * s.alloc i - s.payment i ≤
        v i * (clinchStep rule B v p s).alloc i - (clinchStep rule B v p s).payment i := by
      dsimp only [clinchStep]
      by_cases hle : p ≤ v i
      · have : 0 ≤ (v i - p) * clinchAmt (clinchDemands rule B v p s) s.remSupply i :=
          mul_nonneg (sub_nonneg.mpr hle) hc_nn
        linarith
      · have hdi0 : clinchDemands rule B v p s i = 0 := by
          dsimp only [clinchDemands]
          split_ifs; rfl
        have hci0 : clinchAmt (clinchDemands rule B v p s) s.remSupply i = 0 := by
          dsimp only [clinchAmt]; rw [hdi0]; exact min_eq_left (le_max_left _ _)
        rw [hci0]; linarith
    exact hstep_gain.trans (clinchRun_util_ge rule B v i ps
      (fun q hq => hpos q (List.mem_cons_of_mem p hq))
      (clinchStep rule B v p s) (clinchStep_payment_le rule B v hp s hbf))

private theorem clinchRun_util_le (rule : DemandRule ι) (B v : ι → ℝ) (i : ι) (val : ℝ) :
    ∀ (ps : List ℝ), (∀ p ∈ ps, 0 < p) → (∀ p ∈ ps, val < p) →
      ∀ (s : ClinchState ι), (∀ k, s.payment k ≤ B k) →
        val * (clinchRun rule B v ps s).alloc i - (clinchRun rule B v ps s).payment i ≤
          val * s.alloc i - s.payment i
  | [], _, _, _, _ => le_rfl
  | p :: ps, hpos, hlt, s, hbf => by
    have hp : 0 < p := hpos p (List.mem_cons_self ..)
    have hd_nn := clinchDemands_nonneg rule B v hp s hbf
    have hc_nn := clinchAmt_nonneg hd_nn s.remSupply i
    have ih := clinchRun_util_le rule B v i val ps
      (fun q hq => hpos q (List.mem_cons_of_mem p hq))
      (fun q hq => hlt q (List.mem_cons_of_mem p hq))
      (clinchStep rule B v p s) (clinchStep_payment_le rule B v hp s hbf)
    have hval_lt : val < p := hlt p (List.mem_cons_self ..)
    have hdrop : (val - p) * clinchAmt (clinchDemands rule B v p s) s.remSupply i ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hval_lt.le) hc_nn
    have hstep_le : val * (clinchStep rule B v p s).alloc i -
        (clinchStep rule B v p s).payment i ≤ val * s.alloc i - s.payment i := by
      dsimp only [clinchStep]; linarith
    exact ih.trans hstep_le

private theorem clinchRun_dsic [DecidableEq ι] (rule : DemandRule ι) (B : ι → ℝ)
    (i : ι) (b : ι → ℝ) (v : ℝ) :
    ∀ (ps : List ℝ), ps.Pairwise (· ≤ ·) → (∀ p ∈ ps, 0 < p) →
      ∀ (s : ClinchState ι), (∀ k, s.payment k ≤ B k) →
        v * (clinchRun rule B b ps s).alloc i - (clinchRun rule B b ps s).payment i ≤
          v * (clinchRun rule B (Function.update b i v) ps s).alloc i -
            (clinchRun rule B (Function.update b i v) ps s).payment i
  | [], _, _, _, _ => le_rfl
  | p :: ps, hsort, hpos, s, hbf => by
    have hps_ge : ∀ q ∈ p :: ps, p ≤ q := fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hmem
      · exact le_rfl
      · exact (List.pairwise_cons.mp hsort).1 q hmem
    have htail_sort : ps.Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsort).2
    have hp : 0 < p := hpos p (List.mem_cons_self ..)
    have htail_pos : ∀ q ∈ ps, 0 < q := fun q hq => hpos q (List.mem_cons_of_mem p hq)
    by_cases hpb : p ≤ b i <;> by_cases hpv : p ≤ v
    · have hdem_eq : clinchDemands rule B b p s =
          clinchDemands rule B (Function.update b i v) p s := by
        funext k
        by_cases hki : k = i
        · subst hki
          dsimp only [clinchDemands]
          rw [Function.update_self]
          split_ifs; rfl
        · dsimp only [clinchDemands]
          rw [Function.update_of_ne hki]
      have hstep_eq : clinchStep rule B b p s =
          clinchStep rule B (Function.update b i v) p s := by
        dsimp only [clinchStep]; rw [hdem_eq]
      simp only [clinchRun, ← hstep_eq]
      exact clinchRun_dsic rule B i b v ps htail_sort htail_pos
        (clinchStep rule B b p s) (clinchStep_payment_le rule B b hp s hbf)
    · have hv_lt : ∀ q ∈ p :: ps, v < q := fun q hq =>
        lt_of_lt_of_le (lt_of_not_ge hpv) (hps_ge q hq)
      have hfr := clinchRun_frozen rule B (Function.update b i v) i (p :: ps) hpos
        (fun q hq => by rw [Function.update_self]; exact hv_lt q hq) s hbf
      have hle := clinchRun_util_le rule B b i v (p :: ps) hpos hv_lt s hbf
      rw [hfr.1, hfr.2]
      exact hle
    · have hb_lt : ∀ q ∈ p :: ps, b i < q := fun q hq =>
        lt_of_lt_of_le (lt_of_not_ge hpb) (hps_ge q hq)
      have hfr := clinchRun_frozen rule B b i (p :: ps) hpos hb_lt s hbf
      have hge := clinchRun_util_ge rule B (Function.update b i v) i (p :: ps) hpos s hbf
      rw [Function.update_self] at hge
      rw [hfr.1, hfr.2]
      exact hge
    · have hb_lt : ∀ q ∈ p :: ps, b i < q := fun q hq =>
        lt_of_lt_of_le (lt_of_not_ge hpb) (hps_ge q hq)
      have hv_lt : ∀ q ∈ p :: ps, v < q := fun q hq =>
        lt_of_lt_of_le (lt_of_not_ge hpv) (hps_ge q hq)
      have hfr_b := clinchRun_frozen rule B b i (p :: ps) hpos hb_lt s hbf
      have hfr_v := clinchRun_frozen rule B (Function.update b i v) i (p :: ps) hpos
        (fun q hq => by rw [Function.update_self]; exact hv_lt q hq) s hbf
      rw [hfr_b.1, hfr_b.2, hfr_v.1, hfr_v.2]

private theorem init_valid {m : ℝ} (hm : 0 ≤ m) {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) :
    (⟨fun _ => 0, fun _ => 0, m⟩ : ClinchState ι).Valid m B :=
  ⟨fun _ => le_rfl, fun _ => le_rfl, hB, hm, by simp⟩

/-- Feasibility of `clinchAuction`: allocations are nonnegative and sum to at most `m`. -/
theorem clinchAuction_isFeasible (rule : DemandRule ι) {m : ℝ} (hm : 0 ≤ m)
    {prices : List ℝ} (hpos : ∀ p ∈ prices, 0 < p) {B v : ι → ℝ} (hB : ∀ i, 0 ≤ B i) :
    (clinchAuction rule m prices B v).IsFeasible m := by
  have hv := clinchRun_valid rule B v prices hpos ⟨fun _ => 0, fun _ => 0, m⟩ (init_valid hm hB)
  exact ⟨hv.1, by dsimp only [clinchAuction]; linarith [hv.2.2.2.1, hv.2.2.2.2]⟩

/-- Nonnegative payments (`no positive transfers`) for `clinchAuction`. -/
theorem clinchAuction_hasNonnegPayment (rule : DemandRule ι) {m : ℝ} (hm : 0 ≤ m)
    {prices : List ℝ} (hpos : ∀ p ∈ prices, 0 < p) {B v : ι → ℝ} (hB : ∀ i, 0 ≤ B i) :
    (clinchAuction rule m prices B v).HasNonnegPayment :=
  (clinchRun_valid rule B v prices hpos ⟨fun _ => 0, fun _ => 0, m⟩ (init_valid hm hB)).2.1

/-- Hard budget feasibility for `clinchAuction`. -/
theorem clinchAuction_isBudgetFeasible (rule : DemandRule ι) {m : ℝ} (hm : 0 ≤ m)
    {prices : List ℝ} (hpos : ∀ p ∈ prices, 0 < p) {B v : ι → ℝ} (hB : ∀ i, 0 ≤ B i) :
    (clinchAuction rule m prices B v).IsBudgetFeasible B :=
  (clinchRun_valid rule B v prices hpos ⟨fun _ => 0, fun _ => 0, m⟩ (init_valid hm hB)).2.2.1

/-- Individual rationality for `clinchMechanism` (`SingleParameter.Mechanism.IsIR`). -/
theorem clinchMechanism_isIR (rule : DemandRule ι) (m : ℝ)
    {prices : List ℝ} (hpos : ∀ p ∈ prices, 0 < p) {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) :
    (clinchMechanism rule m prices B).IsIR := by
  intro i b _
  have h := clinchRun_util_ge rule B b i prices hpos ⟨fun _ => 0, fun _ => 0, m⟩ hB
  dsimp only [SingleParameter.Mechanism.utility, clinchMechanism, clinchAuction]
  linarith

/-- Normalization (`SingleParameter.Mechanism.IsNormalized`): a bidder bidding `0` pays `0`. -/
theorem clinchMechanism_isNormalized [DecidableEq ι] (rule : DemandRule ι) (m : ℝ)
    {prices : List ℝ} (hpos : ∀ p ∈ prices, 0 < p) {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) :
    (clinchMechanism rule m prices B).IsNormalized := by
  intro i b _
  have hfr := clinchRun_frozen rule B (Function.update b i 0) i prices hpos
    (fun p hp => by rw [Function.update_self]; exact hpos p hp)
    ⟨fun _ => 0, fun _ => 0, m⟩ hB
  exact hfr.2

/-- **Dominant-strategy incentive compatibility** of the discrete `n`-bidder ascending clinching
auction (`clinchMechanism`) for fixed public budgets `B` whenever `prices` is sorted ascending and
strictly positive ([Ausubel2004]; [DobzinskiLaviNisan2012], primary PDFs unverified). -/
theorem clinchMechanism_isDSIC [DecidableEq ι] (rule : DemandRule ι) (m : ℝ)
    {prices : List ℝ} (hsort : prices.Pairwise (· ≤ ·)) (hpos : ∀ p ∈ prices, 0 < p)
    {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) :
    (clinchMechanism rule m prices B).IsDSIC := fun i b v _ _ =>
  clinchRun_dsic rule B i b v prices hsort hpos ⟨fun _ => 0, fun _ => 0, m⟩ hB

private theorem clinchRun_clear_or_exhaust_divisible {m : ℝ} (B v : ι → ℝ) (i : ι) :
    ∀ (ps : List ℝ), (∀ p ∈ ps, 0 < p) →
      (∃ p ∈ ps, p ≤ v i ∧ ∀ j, j ≠ i → v j < p) →
      ∀ (s : ClinchState ι), s.Valid m B →
        (clinchRun (DemandRule.divisible ι) B v ps s).remSupply = 0 ∨
          (clinchRun (DemandRule.divisible ι) B v ps s).payment i = B i
  | [], _, ⟨_, hp, _⟩, _, _ => absurd hp (by simp)
  | p :: ps, hpos, ⟨q, hq, hqi, hq_other⟩, s, hs => by
    classical
    have hps_pos : ∀ r ∈ ps, 0 < r := fun r hr => hpos r (List.mem_cons_of_mem p hr)
    have hp : 0 < p := hpos p (List.mem_cons_self ..)
    have hs' := clinchStep_valid (DemandRule.divisible ι) B v hp s hs
    rcases List.mem_cons.mp hq with hqp | hmem
    · have hpi : p ≤ v i := hqp ▸ hqi
      have hp_other : ∀ j, j ≠ i → v j < p := fun j hj => hqp ▸ hq_other j hj
      have hother0 : ∀ j, j ≠ i →
          clinchDemands (DemandRule.divisible ι) B v p s j = 0 := by
        intro j hji
        dsimp only [clinchDemands]
        split_ifs with h
        · exact absurd h (not_le.mpr (hp_other j hji))
        · rfl
      have hsum_d : (∑ j, clinchDemands (DemandRule.divisible ι) B v p s j) =
          clinchDemands (DemandRule.divisible ι) B v p s i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have hz : ∑ j ∈ Finset.univ.erase i,
            clinchDemands (DemandRule.divisible ι) B v p s j = 0 :=
          Finset.sum_eq_zero fun j hj => hother0 j (Finset.ne_of_mem_erase hj)
        linarith
      have hsum_c : (∑ j, clinchAmt (clinchDemands (DemandRule.divisible ι) B v p s)
          s.remSupply j) =
          clinchAmt (clinchDemands (DemandRule.divisible ι) B v p s) s.remSupply i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have hz : ∑ j ∈ Finset.univ.erase i,
            clinchAmt (clinchDemands (DemandRule.divisible ι) B v p s) s.remSupply j = 0 :=
          Finset.sum_eq_zero fun j hj => by
            dsimp only [clinchAmt]
            rw [hother0 j (Finset.ne_of_mem_erase hj)]
            exact min_eq_left (le_max_left _ _)
        linarith
      have hdi : clinchDemands (DemandRule.divisible ι) B v p s i =
          (B i - s.payment i) / p := by
        dsimp only [clinchDemands, DemandRule.divisible]
        split_ifs; rfl
      have hci : clinchAmt (clinchDemands (DemandRule.divisible ι) B v p s) s.remSupply i =
          min ((B i - s.payment i) / p) s.remSupply := by
        dsimp only [clinchAmt]
        rw [hsum_d, sub_self, sub_zero, max_eq_right hs.2.2.2.1, hdi]
      have hmono := clinchRun_mono_rem (DemandRule.divisible ι) B v ps hps_pos
        (clinchStep (DemandRule.divisible ι) B v p s) hs'.2.2.1
      have hval_end := clinchRun_valid (DemandRule.divisible ι) B v ps hps_pos
        (clinchStep (DemandRule.divisible ι) B v p s) hs'
      by_cases hclear : s.remSupply ≤ (B i - s.payment i) / p
      · left
        have hrem0 : (clinchStep (DemandRule.divisible ι) B v p s).remSupply = 0 := by
          dsimp only [clinchStep]
          rw [hsum_c, hci, min_eq_right hclear, sub_self]
        exact le_antisymm (hmono.2.2.trans hrem0.le) hval_end.2.2.2.1
      · right
        have hlt : (B i - s.payment i) / p < s.remSupply := lt_of_not_ge hclear
        have hpay_eq : (clinchStep (DemandRule.divisible ι) B v p s).payment i = B i := by
          dsimp only [clinchStep]
          rw [hci, min_eq_left hlt.le, mul_div_cancel₀ _ hp.ne']
          linarith
        exact le_antisymm (hval_end.2.2.1 i) (hpay_eq ▸ hmono.2.1 i)
    · exact clinchRun_clear_or_exhaust_divisible B v i ps hps_pos
        ⟨q, hmem, hqi, hq_other⟩ (clinchStep (DemandRule.divisible ι) B v p s) hs'

/-- Market-clearing / budget-exhaustion guarantee for the discrete divisible `clinchAuction`: if
some posted price `p ∈ prices` strictly separates the highest bidder `i` from every other bidder
(`∀ j ≠ i, v j < p ≤ v i`), then at the end of the auction either the entire supply `m` is
allocated (`∑ k, alloc k = m`) or bidder `i`'s budget is exhausted (`payment i = B i`). -/
theorem clinchAuction_clear_or_exhaust_divisible {m : ℝ} (hm : 0 ≤ m)
    {prices : List ℝ} (hpos : ∀ p ∈ prices, 0 < p) {B v : ι → ℝ} (hB : ∀ k, 0 ≤ B k)
    {i : ι} (hsep : ∃ p ∈ prices, p ≤ v i ∧ ∀ j, j ≠ i → v j < p) :
    (∑ k, (clinchAuction (DemandRule.divisible ι) m prices B v).alloc k = m) ∨
      (clinchAuction (DemandRule.divisible ι) m prices B v).payment i = B i := by
  have hvalid := clinchRun_valid (DemandRule.divisible ι) B v prices hpos
    ⟨fun _ => 0, fun _ => 0, m⟩ (init_valid hm hB)
  rcases clinchRun_clear_or_exhaust_divisible B v i prices hpos hsep
      ⟨fun _ => 0, fun _ => 0, m⟩ (init_valid hm hB) with hrem | hpay
  · left; dsimp only [clinchAuction]; linarith [hvalid.2.2.2.2]
  · right; exact hpay

end DiscreteClinching

end Cslib.GameTheory.BudgetedAuction

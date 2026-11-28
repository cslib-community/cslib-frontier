/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.PredictionMarket.LMSR
import CslibFrontier.GameTheory.PredictionMarket.NoTrade
import CslibFrontier.GameTheory.PredictionMarket.OrderMatching
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Checked witnesses for prediction market no-trade, order matching, and conditional LMSR

Ordinary `module` client exercising `NoTrade.lean`, `OrderMatching.lean`, and Exercise 26.3 in
`LMSR.lean` across the export boundary:

* **Aumann's Agreement Theorem** (`aumann_agreement`, `aumann_agreement_at`) on a 4-state
  product partition model (`Ω = Fin 4`, uniform prior).
* **Fully Revealing REE** (`isFullyRevealingPrice_of_injective`,
  `isREE_commonValue_iff_omniscient_of_isFullyRevealing`) on `Fin 4`.
* **Milgrom–Stokey No-Trade Theorem** (`milgrom_stokey_no_trade`) on `Fin 4`, plus sharpness
  counterexamples for heterogeneous priors (`exists_strict_zeroSum_trade_of_ne_prior` and an
  explicit bet) and a subsidized market maker (`∑ i, t i ω > 0`).
* **Example 26.4** ([PennockSami2007, p. 660]): exact payoff vectors `[0.6, -0.4, -0.4, -0.4]`,
  `[-0.7, -0.7, 0.3, 0.3]`, and auctioneer surplus `[0.1, 1.1, 0.1, 0.1]`, certifying
  `HasIndivisibleMatch` and `HasDivisibleMatch`.
* **Model boundaries**: conditional security cancellation (`condition ≠ []`), separation between
  `HasDivisibleMatch` and `¬ HasIndivisibleMatch`, small-support Farkas certificates
  (`not_hasDivisibleMatch_iff_exists_small_farkas`), and client access to
  `DivisibleOrderMatching_coNPComplete`.
* **Exercise 26.3** ([PennockSami2007, pp. 674–675]): conditional LMSR integral identity, cost
  change, refund-on-cancellation payoff, and price invariance outside `ψ` on `Fin 3`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.PredictionMarketNoTradeMatching

open Finset Cslib.Complexity Cslib.GameTheory Cslib.GameTheory.PredictionMarket Cslib.Logic.PL

/-! ### 1. Partition model, Aumann Agreement, Fully Revealing REE, and Milgrom–Stokey No-Trade -/

/-- Agent 0 distinguishes `{0, 1}` from `{2, 3}` on `Fin 4`. -/
def part0 : Setoid (Fin 4) := Setoid.ker fun ω : Fin 4 => decide (ω.val < 2)

/-- Agent 1 distinguishes `{0, 2}` from `{1, 3}` on `Fin 4`. -/
def part1 : Setoid (Fin 4) := Setoid.ker fun ω : Fin 4 => decide (ω.val % 2 = 0)

/-- Two-agent partition profile on `Fin 4`. -/
def twoAgentParts : Fin 2 → Setoid (Fin 4) := ![part0, part1]

/-- Uniform prior on `Fin 4`. -/
noncomputable def unif4 : Fin 4 → ℝ := fun _ => 1 / 4

private theorem unif4_nonneg (ω : Fin 4) : 0 ≤ unif4 ω := by norm_num [unif4]

private theorem unif4_pos (ω : Fin 4) : 0 < unif4 ω := by norm_num [unif4]

private theorem combinedPartition_twoAgentParts :
    combinedPartition twoAgentParts = ⊥ := by
  ext ω₁ ω₂
  rw [combinedPartition_rel, Setoid.bot_def]
  constructor
  · intro h
    have h0 : decide (ω₁.val < 2) = decide (ω₂.val < 2) := h 0
    have h1 : decide (ω₁.val % 2 = 0) = decide (ω₂.val % 2 = 0) := h 1
    fin_cases ω₁ <;> fin_cases ω₂ <;> simp_all
  · rintro rfl i
    exact (twoAgentParts i).refl' _

private theorem commonKnowledgePartition_twoAgentParts :
    commonKnowledgePartition twoAgentParts = ⊤ := by
  rw [Setoid.eq_top_iff]
  intro ω₁ ω₂
  have h01 : commonKnowledgePartition twoAgentParts 0 1 :=
    le_iSup twoAgentParts 0
      (show decide ((0 : Fin 4).val < 2) = decide ((1 : Fin 4).val < 2) by decide)
  have h02 : commonKnowledgePartition twoAgentParts 0 2 :=
    le_iSup twoAgentParts 1
      (show decide ((0 : Fin 4).val % 2 = 0) = decide ((2 : Fin 4).val % 2 = 0) by decide)
  have h23 : commonKnowledgePartition twoAgentParts 2 3 :=
    le_iSup twoAgentParts 0
      (show decide ((2 : Fin 4).val < 2) = decide ((3 : Fin 4).val < 2) by decide)
  have h03 : commonKnowledgePartition twoAgentParts 0 3 :=
    (commonKnowledgePartition twoAgentParts).trans' h02 h23
  have hto0 (ω : Fin 4) : commonKnowledgePartition twoAgentParts 0 ω := by
    fin_cases ω
    · exact (commonKnowledgePartition twoAgentParts).refl' 0
    · exact h01
    · exact h02
    · exact h03
  exact (commonKnowledgePartition twoAgentParts).trans'
    ((commonKnowledgePartition twoAgentParts).symm' (hto0 ω₁)) (hto0 ω₂)

/-- Witness for Aumann's Agreement Theorem (`aumann_agreement` and `aumann_agreement_at`): on
`Fin 4` with uniform prior and `f = 1_{ω ∈ {0, 3}}`, both agents have constant posterior `1/2`
across `univ`, so `q_0 = q_1 = E[f | univ] = 1/2`. -/
example :
    let f : Fin 4 → ℝ := ![1, 0, 0, 1]
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)), 0 < unif4 ω →
      condExp unif4 (infoCell (twoAgentParts 0) ω) f = 1 / 2) ∧
    (∀ ω ∈ (Finset.univ : Finset (Fin 4)), 0 < unif4 ω →
      condExp unif4 (infoCell (twoAgentParts 1) ω) f = 1 / 2) ∧
    condExp unif4 (Finset.univ : Finset (Fin 4)) f = 1 / 2 := by
  intro f
  have hck : IsCommonKnowledgeEvent twoAgentParts (Finset.univ : Finset (Fin 4)) :=
    fun _ _ _ _ _ => Finset.mem_univ _
  have hpos : 0 < eventProb unif4 (Finset.univ : Finset (Fin 4)) := by
    simp only [eventProb_apply, Fin.sum_univ_four, unif4]; norm_num
  have hcell0 (a b : Fin 4)
      (hmem : ∀ x : Fin 4, (decide (a.val < 2) = decide (x.val < 2)) ↔ x = a ∨ x = b) :
      infoCell (twoAgentParts 0) a = {a, b} := by
    ext x
    simp only [mem_infoCell, Finset.mem_insert, Finset.mem_singleton]
    exact hmem x
  have hcell1 (a b : Fin 4)
      (hmem : ∀ x : Fin 4, (decide (a.val % 2 = 0) = decide (x.val % 2 = 0)) ↔ x = a ∨ x = b) :
      infoCell (twoAgentParts 1) a = {a, b} := by
    ext x
    simp only [mem_infoCell, Finset.mem_insert, Finset.mem_singleton]
    exact hmem x
  have h0 : ∀ ω ∈ (Finset.univ : Finset (Fin 4)), 0 < unif4 ω →
      condExp unif4 (infoCell (twoAgentParts 0) ω) f = 1 / 2 := by
    intro ω _ _
    fin_cases ω
    · change condExp unif4 (infoCell (twoAgentParts 0) 0) f = 1 / 2
      have hc : infoCell (twoAgentParts 0) 0 = {0, 1} :=
        hcell0 0 1 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
    · change condExp unif4 (infoCell (twoAgentParts 0) 1) f = 1 / 2
      have hc : infoCell (twoAgentParts 0) 1 = {1, 0} :=
        hcell0 1 0 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
    · change condExp unif4 (infoCell (twoAgentParts 0) 2) f = 1 / 2
      have hc : infoCell (twoAgentParts 0) 2 = {2, 3} :=
        hcell0 2 3 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
    · change condExp unif4 (infoCell (twoAgentParts 0) 3) f = 1 / 2
      have hc : infoCell (twoAgentParts 0) 3 = {3, 2} :=
        hcell0 3 2 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
  have h1 : ∀ ω ∈ (Finset.univ : Finset (Fin 4)), 0 < unif4 ω →
      condExp unif4 (infoCell (twoAgentParts 1) ω) f = 1 / 2 := by
    intro ω _ _
    fin_cases ω
    · change condExp unif4 (infoCell (twoAgentParts 1) 0) f = 1 / 2
      have hc : infoCell (twoAgentParts 1) 0 = {0, 2} :=
        hcell1 0 2 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
    · change condExp unif4 (infoCell (twoAgentParts 1) 1) f = 1 / 2
      have hc : infoCell (twoAgentParts 1) 1 = {1, 3} :=
        hcell1 1 3 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
    · change condExp unif4 (infoCell (twoAgentParts 1) 2) f = 1 / 2
      have hc : infoCell (twoAgentParts 1) 2 = {2, 0} :=
        hcell1 2 0 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
    · change condExp unif4 (infoCell (twoAgentParts 1) 3) f = 1 / 2
      have hc : infoCell (twoAgentParts 1) 3 = {3, 1} :=
        hcell1 3 1 fun x => by fin_cases x <;> decide
      rw [hc, condExp_apply, eventProb_apply, Finset.sum_pair (by decide),
        Finset.sum_pair (by decide)]
      norm_num [unif4, f]
  have hag := aumann_agreement unif4_nonneg hck hpos f h0 h1
  have _hat : (1 / 2 : ℝ) = 1 / 2 :=
    aumann_agreement_at unif4_nonneg f (unif4_pos 0)
      (E_i := Finset.univ) (E_j := Finset.univ)
      (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) h0 h1
  exact ⟨h0, h1, hag.2.symm⟩

/-- Witness that `commonKnowledgePartition twoAgentParts = ⊤` on `Fin 4`. -/
example : commonKnowledgePartition twoAgentParts = ⊤ :=
  commonKnowledgePartition_twoAgentParts

/-- Fully revealing REE witness on `Fin 4`: injective price `Pstar ω = ω.1` is fully revealing,
forms an REE for `f ω = ω.1` under average clearing, and equals every agent's posterior. -/
example :
    let Pstar : Fin 4 → ℝ := fun ω => (ω.val : ℝ)
    let clearAvg : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ := fun g ω => (g 0 ω + g 1 ω) / 2
    IsFullyRevealingPrice twoAgentParts Pstar ∧
      IsREE unif4 twoAgentParts (fun _ => Pstar) clearAvg Pstar := by
  intro Pstar clearAvg
  have hinj : Function.Injective Pstar := fun a b h => by
    have : a.val = b.val := Nat.cast_injective h
    exact Fin.ext this
  have hfr : IsFullyRevealingPrice twoAgentParts Pstar :=
    isFullyRevealingPrice_of_injective combinedPartition_twoAgentParts hinj
  refine ⟨hfr, ?_⟩
  rw [isREE_commonValue_iff_omniscient_of_isFullyRevealing
    (fun g ω c hc => by simp [clearAvg, hc 0, hc 1]) hfr]
  intro ω
  have hcell : infoCell (combinedPartition twoAgentParts) ω = {ω} := by
    rw [combinedPartition_twoAgentParts]
    ext ω'
    simp only [mem_infoCell, Setoid.bot_def, Finset.mem_singleton]
    exact eq_comm
  rw [hcell, condExp_apply, eventProb_apply, Finset.sum_singleton, Finset.sum_singleton,
    mul_div_cancel_left₀ _ (unif4_pos ω).ne']

/-- Witness for the Milgrom–Stokey No-Trade Theorem (`milgrom_stokey_no_trade`): on `Fin 4` with
common uniform prior `unif4` and partitions `twoAgentParts`, any interim individually rational
zero-sum trade `t` has zero interim expected profit for every agent in every state. -/
example (t : Fin 2 → Fin 4 → ℝ) (hzero : ∀ ω : Fin 4, t 0 ω + t 1 ω = 0)
    (hir : ∀ i : Fin 2, ∀ ω : Fin 4, 0 ≤ condExp unif4 (infoCell (twoAgentParts i) ω) (t i)) :
    ∀ i : Fin 2, ∀ ω : Fin 4, condExp unif4 (infoCell (twoAgentParts i) ω) (t i) = 0 := by
  have hck : IsCommonKnowledgeEvent twoAgentParts (Finset.univ : Finset (Fin 4)) :=
    fun _ _ _ _ _ => Finset.mem_univ _
  have hnt := milgrom_stokey_no_trade unif4_nonneg hck
    (fun ω _ => by simpa only [Fin.sum_univ_two] using hzero ω)
    (fun i ω _ _ => hir i ω)
  intro i ω
  exact hnt i ω (Finset.mem_univ ω) (unif4_pos ω)

/-- Sharpness counterexample (a): heterogeneous priors `P₁ = ![3/4, 1/4]` and `P₂ = ![1/4, 3/4]`
admit a strictly mutually profitable zero-sum bet (`E_{P₁}[t 0] = E_{P₂}[t 1] = 1/2 > 0`), both
explicitly and via `exists_strict_zeroSum_trade_of_ne_prior`. -/
example :
    let P₁ : Fin 2 → ℝ := ![3 / 4, 1 / 4]
    let P₂ : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    let t : Fin 2 → Fin 2 → ℝ := ![![1, -1], ![-1, 1]]
    IsMixedStrategy P₁ ∧ IsMixedStrategy P₂ ∧ P₁ ≠ P₂ ∧
      (∀ ω, t 0 ω + t 1 ω = 0) ∧
      0 < ∑ ω, P₁ ω * t 0 ω ∧ 0 < ∑ ω, P₂ ω * t 1 ω ∧
      (∃ t' : Fin 2 → Fin 2 → ℝ, (∀ ω, t' 0 ω + t' 1 ω = 0) ∧
        0 < ∑ ω, P₁ ω * t' 0 ω ∧ 0 < ∑ ω, P₂ ω * t' 1 ω) := by
  intro P₁ P₂ t
  have hP₁ : IsMixedStrategy P₁ :=
    isMixedStrategy_iff.mpr ⟨fun i => by fin_cases i <;> norm_num [P₁],
      by simp only [Fin.sum_univ_two, P₁]; norm_num⟩
  have hP₂ : IsMixedStrategy P₂ :=
    isMixedStrategy_iff.mpr ⟨fun i => by fin_cases i <;> norm_num [P₂],
      by simp only [Fin.sum_univ_two, P₂]; norm_num⟩
  have hne : P₁ ≠ P₂ := fun h => by
    have := congrFun h 0
    norm_num [P₁, P₂] at this
  refine ⟨hP₁, hP₂, hne, fun ω => by fin_cases ω <;> norm_num [t],
    by simp only [Fin.sum_univ_two, P₁, t]; norm_num,
    by simp only [Fin.sum_univ_two, P₂, t]; norm_num,
    exists_strict_zeroSum_trade_of_ne_prior hP₁ hP₂ hne⟩

/-- Sharpness counterexample (b): with a subsidized market maker (`∑ i, t i ω = 1/2 > 0`), both
agents achieve strictly positive interim expected profit `1/4 > 0` under a common prior. -/
example :
    let t : Fin 2 → Fin 4 → ℝ := fun _ _ => 1 / 4
    (∀ ω : Fin 4, 0 < ∑ i : Fin 2, t i ω) ∧
      ∀ i : Fin 2, ∀ ω : Fin 4, 0 < condExp unif4 (infoCell (twoAgentParts i) ω) (t i) := by
  intro t
  refine ⟨fun _ => by simp only [Fin.sum_univ_two, t]; norm_num, fun i ω => ?_⟩
  have hpos : 0 < eventProb unif4 (infoCell (twoAgentParts i) ω) :=
    eventProb_pos_of_mem unif4_nonneg (mem_infoCell_self _ ω) (unif4_pos ω)
  rw [condExp_eq_const unif4_nonneg hpos (c := 1 / 4) (fun _ _ _ => rfl)]
  norm_num

/-! ### 2. Compound order matching: Example 26.4, boundaries, Farkas certificates, `coNPComplete` -/

private theorem auctioneerPayoff_single (o : CompoundOrder) (α : Fin [o].length → ℝ)
    (ω : ℕ → Bool) :
    auctioneerPayoff [o] α ω = -(α ⟨0, by simp⟩) * orderPayoff o ω := by
  simp only [auctioneerPayoff]
  exact Fin.sum_univ_one fun i : Fin 1 => -(α i) * orderPayoff [o][i] ω

private theorem auctioneerPayoff_pair (o₁ o₂ : CompoundOrder) (α : Fin [o₁, o₂].length → ℝ)
    (ω : ℕ → Bool) :
    auctioneerPayoff [o₁, o₂] α ω =
      -(α ⟨0, by simp⟩) * orderPayoff o₁ ω + -(α ⟨1, by simp⟩) * orderPayoff o₂ ω := by
  have hne : (⟨0, by simp⟩ : Fin [o₁, o₂].length) ≠ ⟨1, by simp⟩ := fun h => by
    simpa using congrArg Fin.val h
  have huniv : (Finset.univ : Finset (Fin [o₁, o₂].length)) =
      {⟨0, by simp⟩, ⟨1, by simp⟩} := by
    ext ⟨k, hk⟩
    simp only [List.length_cons, List.length_nil] at hk
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, true_iff]
    omega
  simp only [auctioneerPayoff, huniv, Finset.sum_pair hne]
  rfl

/-- Example 26.4 order 1: buy 1 unit of `S_{X_0 ∧ X_1}` at price `0.4 = 2 / 5`
[PennockSami2007, Example 26.4, p. 660]. -/
def ex26_4_order1 : CompoundOrder :=
  ⟨1, 2 / 5, [[(0, true)], [(1, true)]], []⟩

/-- Example 26.4 order 2: sell 1 unit of `S_{X_0}` at price `0.3 = 3 / 10`
[PennockSami2007, Example 26.4, p. 660]. -/
def ex26_4_order2 : CompoundOrder :=
  ⟨-1, 3 / 10, [[(0, true)]], []⟩

/-- Example 26.4 order book `[ex26_4_order1, ex26_4_order2]`. -/
def ex26_4_orders : List CompoundOrder :=
  [ex26_4_order1, ex26_4_order2]

/-- State helper assigning `(b₀, b₁)` to variables `0, 1` and `false` elsewhere. -/
def state2 (b₀ b₁ : Bool) : ℕ → Bool
  | 0 => b₀
  | 1 => b₁
  | _ => false

/-- **Example 26.4** ([PennockSami2007, p. 660]): exact payoff vectors
`ϒ₁ = [0.6, -0.4, -0.4, -0.4]`, `ϒ₂ = [-0.7, -0.7, 0.3, 0.3]`, and auctioneer surplus
`ϒ_auc = [0.1, 1.1, 0.1, 0.1]`, certifying both `HasIndivisibleMatch` and `HasDivisibleMatch`. -/
example :
    orderPayoff ex26_4_order1 (state2 true true) = 3 / 5 ∧
    orderPayoff ex26_4_order1 (state2 true false) = -(2 / 5) ∧
    orderPayoff ex26_4_order1 (state2 false true) = -(2 / 5) ∧
    orderPayoff ex26_4_order1 (state2 false false) = -(2 / 5) ∧
    orderPayoff ex26_4_order2 (state2 true true) = -(7 / 10) ∧
    orderPayoff ex26_4_order2 (state2 true false) = -(7 / 10) ∧
    orderPayoff ex26_4_order2 (state2 false true) = 3 / 10 ∧
    orderPayoff ex26_4_order2 (state2 false false) = 3 / 10 ∧
    auctioneerPayoff ex26_4_orders (fun _ => 1) (state2 true true) = 1 / 10 ∧
    auctioneerPayoff ex26_4_orders (fun _ => 1) (state2 true false) = 11 / 10 ∧
    auctioneerPayoff ex26_4_orders (fun _ => 1) (state2 false true) = 1 / 10 ∧
    auctioneerPayoff ex26_4_orders (fun _ => 1) (state2 false false) = 1 / 10 ∧
    HasIndivisibleMatch ex26_4_orders ∧
    HasDivisibleMatch ex26_4_orders := by
  have hind : HasIndivisibleMatch ex26_4_orders := by
    refine ⟨fun _ => 1, fun _ => Or.inr rfl, ⟨⟨0, by decide⟩, rfl⟩, fun ω => ?_⟩
    rw [ex26_4_orders, auctioneerPayoff_pair]
    simp only [orderPayoff, ex26_4_order1, ex26_4_order2, CNF.eval_cons, CNF.eval_nil,
      Clause.eval_cons, Clause.eval_nil, Literal.eval_mk, Bool.or_false, Bool.and_true, ↓reduceIte]
    cases ω 0 <;> cases ω 1 <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hind,
    hasDivisibleMatch_of_hasIndivisibleMatch hind⟩
  · simp only [orderPayoff, ex26_4_order1, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · simp only [orderPayoff, ex26_4_order1, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · simp only [orderPayoff, ex26_4_order1, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · simp only [orderPayoff, ex26_4_order1, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · simp only [orderPayoff, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · simp only [orderPayoff, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · simp only [orderPayoff, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · simp only [orderPayoff, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num
  · rw [ex26_4_orders, auctioneerPayoff_pair]
    simp only [orderPayoff, ex26_4_order1, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil,
      Clause.eval_cons, Clause.eval_nil, Literal.eval_mk]; norm_num
  · rw [ex26_4_orders, auctioneerPayoff_pair]
    simp only [orderPayoff, ex26_4_order1, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil,
      Clause.eval_cons, Clause.eval_nil, Literal.eval_mk]; norm_num
  · rw [ex26_4_orders, auctioneerPayoff_pair]
    simp only [orderPayoff, ex26_4_order1, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil,
      Clause.eval_cons, Clause.eval_nil, Literal.eval_mk]; norm_num
  · rw [ex26_4_orders, auctioneerPayoff_pair]
    simp only [orderPayoff, ex26_4_order1, ex26_4_order2, state2, CNF.eval_cons, CNF.eval_nil,
      Clause.eval_cons, Clause.eval_nil, Literal.eval_mk]; norm_num

/-- Model-boundary witness for conditional security cancellation: an order on `S_{X_0 | X_1}` pays
`0` whenever `X_1` is false, regardless of `X_0`. -/
example :
    let o : CompoundOrder := ⟨2, 1 / 4, [[(0, true)]], [[(1, true)]]⟩
    orderPayoff o (state2 true true) = 3 / 2 ∧
    orderPayoff o (state2 false true) = -(1 / 2) ∧
    orderPayoff o (state2 true false) = 0 ∧
    orderPayoff o (state2 false false) = 0 := by
  intro o
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [orderPayoff, o, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]; norm_num)

/-- Separation between divisible and indivisible matching: buying `2` units of `S_{X_0}` at `1/2`
and selling `1` unit of `S_{X_0}` at `1/2` admits a divisible match (`α = (1/2, 1)`) but NO
indivisible match (`α ∈ {0, 1}²`). -/
example :
    let o₁ : CompoundOrder := ⟨2, 1 / 2, [[(0, true)]], []⟩
    let o₂ : CompoundOrder := ⟨-1, 1 / 2, [[(0, true)]], []⟩
    HasDivisibleMatch [o₁, o₂] ∧ ¬ HasIndivisibleMatch [o₁, o₂] := by
  intro o₁ o₂
  constructor
  · refine ⟨fun i => if i.val = 0 then 1 / 2 else 1,
      fun i => by dsimp only; split_ifs <;> norm_num,
      ⟨⟨1, by simp⟩, by norm_num⟩, fun ω => ?_⟩
    rw [auctioneerPayoff_pair]
    simp only [orderPayoff, o₁, o₂, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil,
      Literal.eval_mk, Bool.or_false, Bool.and_true, ↓reduceIte]
    cases ω 0 <;> norm_num
  · rintro ⟨α, h01, ⟨⟨k, hk⟩, hi₀⟩, hpay⟩
    have hT := hpay (state2 true false)
    have hF := hpay (state2 false false)
    rw [auctioneerPayoff_pair] at hT hF
    simp only [orderPayoff, o₁, o₂, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk, Bool.or_false, Bool.and_true, ↓reduceIte] at hT hF
    norm_num at hT hF
    have h0 := h01 0
    have h1 := h01 1
    simp only [List.length_cons, List.length_nil] at hk
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · change α 0 = 1 at hi₀; linarith
      · change α 1 = 1 at hi₀; linarith
    · linarith
    · linarith
    · linarith

/-- Small-support Farkas certificate witness (`not_hasDivisibleMatch_iff_exists_small_farkas`):
two buy orders on complementary events `S_{X_0}` and `S_{¬X_0}` at price `1/4` cannot match,
certified by `2 ≤ 2` states `{state2 true false, state2 false false}` with equal weights `1`. -/
example :
    let o₁ : CompoundOrder := ⟨1, 1 / 4, [[(0, true)]], []⟩
    let o₂ : CompoundOrder := ⟨1, 1 / 4, [[(0, false)]], []⟩
    ¬ HasDivisibleMatch [o₁, o₂] := by
  classical
  intro o₁ o₂
  rw [not_hasDivisibleMatch_iff_exists_small_farkas]
  have hne : state2 true false ≠ state2 false false := fun h => by
    have := congrFun h 0; simp [state2] at this
  refine ⟨{state2 true false, state2 false false}, fun _ => 1,
    by rw [Finset.card_pair hne]; simp, fun _ _ => by norm_num, fun ⟨k, hk⟩ => ?_⟩
  rw [Finset.sum_pair hne]
  simp only [List.length_cons, List.length_nil] at hk
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · change 0 < (1 : ℚ) * orderPayoff o₁ (state2 true false) +
        (1 : ℚ) * orderPayoff o₁ (state2 false false)
    simp only [orderPayoff, o₁, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]
    norm_num
  · change 0 < (1 : ℚ) * orderPayoff o₂ (state2 true false) +
        (1 : ℚ) * orderPayoff o₂ (state2 false false)
    simp only [orderPayoff, o₂, state2, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons,
      Clause.eval_nil, Literal.eval_mk]
    norm_num

/-- UNSAT vs SAT reduction witness: the unsatisfiable CNF `[[]]` maps to a matchable single-order
book, while the satisfiable CNF `[[(0, true)]]` maps to a non-matchable single-order book. -/
example :
    [⟨1, 1 / 2, ([[]] : CNF ℕ), []⟩] ∈ DivisibleOrderMatching ∧
    [⟨1, 1 / 2, ([[(0, true)]] : CNF ℕ), []⟩] ∉ DivisibleOrderMatching := by
  constructor
  · let o : CompoundOrder := ⟨1, 1 / 2, ([[]] : CNF ℕ), []⟩
    change HasDivisibleMatch [o]
    refine ⟨fun _ => 1, fun _ => ⟨by norm_num, le_rfl⟩, ⟨⟨0, by simp⟩, by norm_num⟩, fun ω => ?_⟩
    rw [auctioneerPayoff_single]
    simp only [orderPayoff, o, CNF.eval_cons, CNF.eval_nil, Clause.eval_nil, Bool.false_and,
      ↓reduceIte, Bool.false_eq_true]
    norm_num
  · let o : CompoundOrder := ⟨1, 1 / 2, ([[(0, true)]] : CNF ℕ), []⟩
    change ¬ HasDivisibleMatch [o]
    rintro ⟨α, -, ⟨⟨k, hk⟩, hi₀⟩, hpay⟩
    simp only [List.length_singleton] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have h := hpay (fun _ => true)
    rw [auctioneerPayoff_single] at h
    simp only [orderPayoff, o, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil,
      Literal.eval_mk, Bool.or_false, Bool.and_true, ↓reduceIte] at h
    norm_num at h
    change 0 < α 0 at hi₀
    linarith

/-- Ordinary `module` client access to Theorem 26.6(ii) (`DivisibleOrderMatching_coNPComplete`). -/
theorem client_DivisibleOrderMatching_coNPComplete :
    coNPComplete encOrderList DivisibleOrderMatching :=
  DivisibleOrderMatching_coNPComplete

/-! ### 3. Exercise 26.3: Conditional LMSR securities on `Fin 3` -/

/-- Exercise 26.3 witness on `Ω = Fin 3`, `b = 1`, `φ = {0}`, `ψ = {0, 1}`, `q = 0`, `δ = 1`:
verifies the integral pricing identity (a), the post-trade update cost and payoff (including full
cancellation refund at state `2 ∉ ψ`), and price invariance at state `2 ∉ ψ` (b). -/
example :
    let φ : Finset (Fin 3) := {0}
    let ψ : Finset (Fin 3) := {0, 1}
    let q : Fin 3 → ℝ := 0
    (∫ t in (0 : ℝ)..1, lmsrCondPrice 1 (fun ω => q ω + if ω ∈ φ then t else 0) φ ψ =
      lmsrCondCost 1 ψ (fun ω => q ω + if ω ∈ φ then 1 else 0) - lmsrCondCost 1 ψ q) ∧
    (lmsrTraderPayoff 1 q (lmsrCondUpdate 1 φ ψ q 1) 2 = 0) ∧
    (lmsrPrice 1 (lmsrCondUpdate 1 φ ψ q 1) 2 = lmsrPrice 1 q 2) := by
  intro φ ψ q
  have hb : (0 : ℝ) < 1 := by norm_num
  have hψ : ψ.Nonempty := ⟨0, by decide⟩
  exact ⟨integral_lmsrCondPrice_eq_sub_lmsrCondCost hb φ hψ q 1,
    by simpa [ψ] using lmsrTraderPayoff_lmsrCondUpdate hb φ hψ q 1 2,
    lmsrPrice_lmsrCondUpdate_of_notMem hb φ hψ q 1 (by decide)⟩

end CslibFrontierTests.GameTheory.PredictionMarketNoTradeMatching

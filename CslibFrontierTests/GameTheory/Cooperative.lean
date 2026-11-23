/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Cooperative.Core
import CslibFrontier.GameTheory.Cooperative.MoulinCostSharing
import CslibFrontier.GameTheory.Cooperative.ShapleyValue

/-!
# Cooperative games, cost sharing, Shapley value, and Nash bargaining

Checked examples exercising the cooperative game theory and cost-sharing modules
([JainMahdian2007], Chapter 15; [TardosVazirani2007], Section 1.7.2):

* **Facility location core and LP duality** (`Basic.lean`, `Core.lean`):
  - Example 15.2 (`(4, 2, 2)` and `(4, 1, 3)` in core, plus Proposition 15.10 dual LP witness).
  - Example 15.4 and `emptyCoreMetricFL` (6-vertex metric facility location with empty `1`-core,
    tight `(15 / 16)`-core, and exact `integralityGapLP = 15 / 16` via Corollary 15.9).
* **Linear Arrow–Debreu exchange economy** (Exercise 15.1, `Core.lean`): concrete 2-agent, 2-good
  economy with `v({0}) = 1`, `v({1}) = 2`, `v({0, 1}) = 7`, and competitive core payoff `(3, 4)`.
* **Moulin iterative pruning and `SubmodularCostShare`** (`MoulinCostSharing.lean`): 2-agent
  strictly submodular shared-setup game (`c({false}) = 4`, `c({true}) = 6`, `c({false, true}) = 8`),
  cascading 2-round Moulin dropout trace, and `submodularCostShareScheme` group-strategyproofness.
* **Shapley value** (`ShapleyValue.lean`): Example 15.24 (`(23 / 6, 11 / 6, 7 / 3)` outside a
  nonempty core), unanimity game, and the 3-player glove game (`(2 / 3, 1 / 6, 1 / 6)`).
* **Nash bargaining** (`ShapleyValue.lean`): asymmetric linear frontier `{x ≥ 0 | x₁ + 2 x₂ ≤ 4}`
  with disagreement `(0, 0)` uniquely selecting `(2, 1)`.
-/

namespace CslibFrontierTests.GameTheory.Cooperative

open Cslib.GameTheory

/-! ### Examples 15.2 & Proposition 15.10: Facility location core and dual LP witness -/

example :
    FacilityLocationInstance.example15_2.toCostSharingGame.InCore ![4, 2, 2] ∧
    FacilityLocationInstance.example15_2.toCostSharingGame.InCore ![4, 1, 3] :=
  ⟨FacilityLocationInstance.example15_2_inCore_four_two_two,
   FacilityLocationInstance.example15_2_inCore_four_one_three⟩

/-- Proposition 15.10 witness on `example15_2`: dual variables `α = (4, 2, 2)` and
`β(f₁, ·) = (2, 0, 0)`, `β(f₂, ·) = (0, 1, 1)` satisfy LP `(15.4)` and recover `(4, 2, 2)` in the
core whenever `∑ α_j = c(univ) = 8`. -/
example : FacilityLocationInstance.example15_2.toCostSharingGame.InCore ![4, 2, 2] := by
  let β : Fin 2 → Fin 3 → ℝ :=
    fun i j => match i, j with
      | 0, 0 => 2
      | 1, 1 => 1
      | 1, 2 => 1
      | _, _ => 0
  have hdual : FacilityLocationInstance.example15_2.IsDualFeasible ![4, 2, 2] β := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      fin_cases j <;> norm_num
    · intro i j
      fin_cases i <;> fin_cases j <;> norm_num [β]
    · obtain ⟨h00, h01, h02, h10, h11, h12⟩ := FacilityLocationInstance.example15_2_connCost
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [β, h00, h01, h02, h10, h11, h12]
    · intro i
      rw [Fin.sum_univ_three]
      have ho : FacilityLocationInstance.example15_2.openCost i = 2 := rfl
      rw [ho]
      fin_cases i <;> norm_num [β]
  refine ⟨?_, hdual.isCoreFeasible⟩
  rw [Fin.sum_univ_three, FacilityLocationInstance.example15_2_cost.2.2.2.2.2.2]
  norm_num

/-! ### Example 15.4 & Corollary 15.9: Empty core and exact integrality gap `15 / 16` -/

example :
    ¬ FacilityLocationInstance.emptyCoreBipartiteFL.toCostSharingGame.NonemptyCore ∧
    FacilityLocationInstance.emptyCoreBipartiteFL.toCostSharingGame.InApproxCore (15 / 16)
      ![7 / 2, 5 / 2, 3 / 2] ∧
    ¬ FacilityLocationInstance.emptyCoreBipartiteFL.toCostSharingGame.NonemptyApproxCore
      (16 / 16) ∧
    FacilityLocationInstance.example15_2.toCostSharingGame.toCooperativeGame.InCore
      (-![4, 2, 2]) :=
  ⟨FacilityLocationInstance.emptyCoreBipartiteFL_not_nonemptyCore,
   FacilityLocationInstance.emptyCoreBipartiteFL_inApproxCore,
   FacilityLocationInstance.emptyCoreBipartiteFL_not_nonemptyApproxCore_of_gt (by norm_num),
   (FacilityLocationInstance.example15_2.toCostSharingGame.inCore_toCooperativeGame_iff
     ![4, 2, 2]).2 FacilityLocationInstance.example15_2_inCore_four_two_two⟩

/-- Applying Corollary 15.9 (`isGreatest_nonemptyApproxCore_integralityGapLP`) to the genuine
6-vertex metric facility location instance `emptyCoreMetricFL`: `G.cost univ = 8`, the LP `(15.2)`
optimum is `15 / 2`, and the largest `γ` with nonempty `γ`-core is `integralityGapLP = 15 / 16`. -/
example :
    FacilityLocationInstance.emptyCoreMetricFL.toCostSharingGame.cost Finset.univ = 8 ∧
    FacilityLocationInstance.emptyCoreMetricFL.toCostSharingGame.lpOpt = 15 / 2 ∧
    FacilityLocationInstance.emptyCoreMetricFL.toCostSharingGame.integralityGapLP = 15 / 16 := by
  set G := FacilityLocationInstance.emptyCoreMetricFL.toCostSharingGame
  have happrox := FacilityLocationInstance.emptyCoreMetricFL_inApproxCore
  have huniv : G.cost Finset.univ = 8 := FacilityLocationInstance.emptyCoreMetricFL_cost_univ
  have hpos : 0 < G.cost Finset.univ := by linarith
  have hgreat := G.isGreatest_nonemptyApproxCore_integralityGapLP hpos
  have hge : (15 / 16 : ℝ) ≤ G.integralityGapLP :=
    hgreat.2 ⟨fun _ => 5 / 2, happrox⟩
  have hle : G.integralityGapLP ≤ 15 / 16 :=
    le_of_not_gt fun hgt =>
      FacilityLocationInstance.emptyCoreMetricFL_not_nonemptyApproxCore_of_gt hgt hgreat.1
  have hgap : G.integralityGapLP = 15 / 16 := le_antisymm hle hge
  refine ⟨huniv, ?_, hgap⟩
  unfold CostSharingGame.integralityGapLP at hgap
  rw [huniv] at hgap
  linarith

/-! ### Exercise 15.1: Concrete 2-agent, 2-good linear exchange economy -/

/-- Two agents (`Bool`) and two goods (`Bool`): agent `false` holds `(1, 0)` with utilities `(1,
4)`, and agent `true` holds `(0, 1)` with utilities `(3, 2)`. Trading yields grand-coalition value
`7 > 1 + 2`, and `marketPriceAllocation` assigns `(3, 4)` in the core. -/
noncomputable def twoGoodEconomy : LinearExchangeEconomy Bool Bool where
  endowment i g := if i = g then 1 else 0
  utility
    | false, false => 1
    | false, true => 4
    | true, false => 3
    | true, true => 2
  endowment_nonneg i g := by cases i <;> cases g <;> norm_num
  utility_nonneg i g := by cases i <;> cases g <;> norm_num

example :
    twoGoodEconomy.toCooperativeGame.val {false} = 1 ∧
    twoGoodEconomy.toCooperativeGame.val {true} = 2 ∧
    twoGoodEconomy.toCooperativeGame.val Finset.univ = 7 ∧
    twoGoodEconomy.marketPriceAllocation false = 3 ∧
    twoGoodEconomy.marketPriceAllocation true = 4 ∧
    twoGoodEconomy.toCooperativeGame.InCore twoGoodEconomy.marketPriceAllocation := by
  have huniv_ne : (Finset.univ : Finset Bool).Nonempty := Finset.univ_nonempty
  have hsup_f : (Finset.univ : Finset Bool).sup' huniv_ne
      (fun k => twoGoodEconomy.utility k false) = 3 := by
    refine le_antisymm (Finset.sup'_le huniv_ne _ fun k _ => ?_) ?_
    · cases k <;> norm_num [twoGoodEconomy]
    · exact le_trans (by norm_num [twoGoodEconomy])
        (Finset.le_sup' (fun k => twoGoodEconomy.utility k false) (Finset.mem_univ true))
  have hsup_t : (Finset.univ : Finset Bool).sup' huniv_ne
      (fun k => twoGoodEconomy.utility k true) = 4 := by
    refine le_antisymm (Finset.sup'_le huniv_ne _ fun k _ => ?_) ?_
    · cases k <;> norm_num [twoGoodEconomy]
    · exact le_trans (by norm_num [twoGoodEconomy])
        (Finset.le_sup' (fun k => twoGoodEconomy.utility k true) (Finset.mem_univ false))
  refine ⟨?_, ?_, ?_, ?_, ?_, twoGoodEconomy.marketPriceAllocation_inCore⟩
  · simp [LinearExchangeEconomy.toCooperativeGame, LinearExchangeEconomy.coalitionValue,
      twoGoodEconomy]
  · simp [LinearExchangeEconomy.toCooperativeGame, LinearExchangeEconomy.coalitionValue,
      twoGoodEconomy]
  · simp only [LinearExchangeEconomy.toCooperativeGame, LinearExchangeEconomy.coalitionValue,
      huniv_ne, ↓reduceDIte, Fintype.sum_bool, hsup_f, hsup_t]
    norm_num [twoGoodEconomy]
  · simp only [LinearExchangeEconomy.marketPriceAllocation, huniv_ne, ↓reduceDIte,
      Fintype.sum_bool, hsup_f, hsup_t]
    norm_num [twoGoodEconomy]
  · simp only [LinearExchangeEconomy.marketPriceAllocation, huniv_ne, ↓reduceDIte,
      Fintype.sum_bool, hsup_f, hsup_t]
    norm_num [twoGoodEconomy]

/-! ### Moulin iterative pruning and submodular cost sharing -/

/-- Two-agent strictly submodular shared-setup game on `Bool`: standalone costs `4` and `6`, joint
cost `8 < 4 + 6`. -/
def twoAgentSharedGame : CostSharingGame Bool where
  cost S :=
    if false ∈ S ∧ true ∈ S then 8
    else if false ∈ S then 4
    else if true ∈ S then 6
    else 0
  cost_empty := by simp

theorem twoAgentSharedGame_isSubmodular : twoAgentSharedGame.IsSubmodular := by
  intro S T
  by_cases hfS : false ∈ S <;> by_cases htS : true ∈ S <;>
    by_cases hfT : false ∈ T <;> by_cases htT : true ∈ T <;>
    simp [twoAgentSharedGame, hfS, htS, hfT, htT] <;> norm_num

theorem twoAgentSharedGame_isNonneg : twoAgentSharedGame.IsNonneg := by
  intro S
  by_cases hfS : false ∈ S <;> by_cases htS : true ∈ S <;>
    simp [twoAgentSharedGame, hfS, htS]

/-- Both `submodularCostShareScheme` (Theorem 15.20) and `shapleyScheme` (Exercise 15.2) yield
`1`-budget-balanced, group-strategyproof Moulin mechanisms on `twoAgentSharedGame`. -/
example :
    twoAgentSharedGame.submodularCostShareScheme.IsCrossMonotone ∧
    twoAgentSharedGame.submodularCostShareScheme.moulinMechanism.IsGroupStrategyproof ∧
    twoAgentSharedGame.submodularCostShareScheme.moulinMechanism.IsBudgetBalanced
      twoAgentSharedGame 1 ∧
    twoAgentSharedGame.shapleyScheme.moulinMechanism.IsGroupStrategyproof :=
  ⟨twoAgentSharedGame.submodularCostShareScheme_isCrossMonotone
      twoAgentSharedGame_isSubmodular twoAgentSharedGame_isNonneg,
   twoAgentSharedGame.submodularCostShareScheme.moulinMechanism_isGroupStrategyproof
      (twoAgentSharedGame.submodularCostShareScheme_isCrossMonotone
        twoAgentSharedGame_isSubmodular twoAgentSharedGame_isNonneg),
   twoAgentSharedGame.submodularCostShareScheme.moulinMechanism_isBudgetBalanced
      (twoAgentSharedGame.submodularCostShareScheme_isBudgetBalanced
        twoAgentSharedGame_isSubmodular twoAgentSharedGame_isNonneg),
   (twoAgentSharedGame_isSubmodular.moulinMechanism_shapleyScheme_isGroupStrategyproof).1⟩

/-- Explicit 2-round cascading dropout trace of `moulinMechanism` on `twoAgentSharedGame`'s Shapley
scheme (`ξ({false, true}) = (3, 5)`, `ξ({false}) = (4, 0)`): under bids `(7 / 2, 4)`, agent `true`
is pruned in round 1 (`5 > 4`), raising `false`'s share from `3` to `4 > 7 / 2`, so `false` is
pruned in round 2 and `moulinServiced = ∅`. Raising `false`'s bid to `9 / 2` stops at `{false}`. -/
example :
    let ξ := twoAgentSharedGame.shapleyScheme
    ξ.moulinServiced (fun b => if b then 4 else 7 / 2) = ∅ ∧
    ξ.moulinServiced (fun b => if b then 4 else 9 / 2) = {false} := by
  intro ξ
  have hcm := twoAgentSharedGame_isSubmodular.shapleyScheme_isCrossMonotone
  have hw0 : shapleyWeight 1 0 = 1 := by norm_num [shapleyWeight, Nat.factorial]
  have hw20 : shapleyWeight 2 0 = 1 / 2 := by norm_num [shapleyWeight, Nat.factorial]
  have hw21 : shapleyWeight 2 1 = 1 / 2 := by norm_num [shapleyWeight, Nat.factorial]
  have her_univ_t : ((Finset.univ : Finset Bool).erase true).powerset = {∅, {false}} := by decide
  have her_f : (({false} : Finset Bool).erase false).powerset = {∅} := by decide
  have her_t : (({true} : Finset Bool).erase true).powerset = {∅} := by decide
  have hshare_univ_t : ξ.share Finset.univ true = 5 := by
    have hcard : (Finset.univ : Finset Bool).card = 2 := by decide
    simp only [ξ, CostSharingGame.shapleyScheme, Finset.mem_univ, ↓reduceIte, hcard, her_univ_t]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [hw20, hw21, twoAgentSharedGame]
  have hshare_f : ξ.share {false} false = 4 := by
    simp only [ξ, CostSharingGame.shapleyScheme, Finset.mem_singleton, ↓reduceIte,
      Finset.card_singleton, her_f, Finset.sum_singleton]
    norm_num [hw0, twoAgentSharedGame]
  have hshare_t : ξ.share {true} true = 6 := by
    simp only [ξ, CostSharingGame.shapleyScheme, Finset.mem_singleton, ↓reduceIte,
      Finset.card_singleton, her_t, Finset.sum_singleton]
    norm_num [hw0, twoAgentSharedGame]
  refine ⟨?_, ?_⟩
  · -- Show `∅` is the unique willing coalition under `(7 / 2, 4)`.
    let b₁ : Bool → ℝ := fun b => if b then 4 else 7 / 2
    refine Finset.subset_empty.1 ?_
    have hwilling := ξ.isWilling_moulinServiced b₁
    set S := ξ.moulinServiced b₁
    by_cases ht : true ∈ S
    · by_cases hf : false ∈ S
      · have hS : S = Finset.univ := by ext x; cases x <;> simp [hf, ht]
        have h := hwilling true ht
        rw [hS, hshare_univ_t] at h
        norm_num [b₁] at h
      · have hS : S = {true} := by ext x; cases x <;> simp [hf, ht]
        have h := hwilling true ht
        rw [hS, hshare_t] at h
        norm_num [b₁] at h
    · by_cases hf : false ∈ S
      · have hS : S = {false} := by ext x; cases x <;> simp [hf, ht]
        have h := hwilling false hf
        rw [hS, hshare_f] at h
        norm_num [b₁] at h
      · intro x hx; cases x <;> simp_all
  · -- Under `(9 / 2, 4)`, `{false}` is willing while neither `univ` nor `{true}` is willing.
    let b₂ : Bool → ℝ := fun b => if b then 4 else 9 / 2
    have hgreat := ξ.isGreatest_isWilling_moulinServiced hcm b₂
    have hf_will : ξ.IsWilling b₂ {false} := by
      intro x hx
      rw [Finset.mem_singleton.1 hx, hshare_f]
      norm_num [b₂]
    have hsub : {false} ⊆ ξ.moulinServiced b₂ := hgreat.2 hf_will
    refine le_antisymm ?_ hsub
    intro x hx
    cases x
    · exact Finset.mem_singleton_self false
    · exfalso
      change true ∈ ξ.moulinServiced b₂ at hx
      have hS : ξ.moulinServiced b₂ = Finset.univ := by
        ext y; cases y <;> simp [hsub (Finset.mem_singleton_self false), hx]
      have h := hgreat.1 true hx
      rw [hS, hshare_univ_t] at h
      norm_num [b₂] at h

/-! ### Shapley value: Example 15.24, unanimity game, and 3-player glove game -/

example :
    shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame 0 = 23 / 6 ∧
    shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame 1 = 11 / 6 ∧
    shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame 2 = 7 / 3 ∧
    ¬ FacilityLocationInstance.example15_2.toCostSharingGame.InCore
        (shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame) :=
  ⟨example15_24_shapleyValue.1, example15_24_shapleyValue.2.1,
   example15_24_shapleyValue.2.2, example15_24_not_inCore⟩

/-- Unanimity game on `{0, 1} ⊆ Fin 3` with weight `6`: players `0, 1` split `6` equally `(3, 3)`
and dummy player `2` pays `0`. -/
example :
    let U := unanimityGame ({0, 1} : Finset (Fin 3)) (by decide) 6
    shapleyValue U 0 = 3 ∧ shapleyValue U 1 = 3 ∧ shapleyValue U 2 = 0 := by
  intro U
  have hd2 : U.IsDummyAgent 2 := by
    intro S _
    simp only [U, unanimityGame]
    have hiff : ({0, 1} : Finset (Fin 3)) ⊆ insert 2 S ↔ ({0, 1} : Finset (Fin 3)) ⊆ S := by
      refine ⟨fun h x hx => ?_, fun h => h.trans (Finset.subset_insert 2 S)⟩
      rcases Finset.mem_insert.1 (h hx) with rfl | hxS
      · exfalso; revert hx; decide
      · exact hxS
    simp only [hiff]
  have hsym01 : U.AreSymmetric 0 1 := by
    intro S h0S h1S
    simp only [U, unanimityGame]
    have hn0 : ¬ ({0, 1} : Finset (Fin 3)) ⊆ insert 0 S := fun h =>
      h1S ((Finset.mem_insert.1 (h (by decide))).resolve_left (by decide))
    have hn1 : ¬ ({0, 1} : Finset (Fin 3)) ⊆ insert 1 S := fun h =>
      h0S ((Finset.mem_insert.1 (h (by decide))).resolve_left (by decide))
    simp only [hn0, hn1, ↓reduceIte]
  have hp2 : shapleyValue U 2 = 0 := shapleyValue_satisfiesDummy U 2 hd2
  have hp01 : shapleyValue U 0 = shapleyValue U 1 := shapleyValue_isSymmetric U 0 1 hsym01
  have heff := shapleyValue_isEfficient U
  rw [Fin.sum_univ_three] at heff
  have huniv : U.cost Finset.univ = 6 := by
    simp only [U, unanimityGame, Finset.subset_univ, ↓reduceIte]
  rw [huniv, hp2, hp01] at heff
  refine ⟨by linarith, by linarith, hp2⟩

/-- Three-player **glove game** (`0` holds one left glove; `1` and `2` each hold one right glove):
`v(S) = 1` iff `0 ∈ S ∧ (1 ∈ S ∨ 2 ∈ S)`. Under cost-surplus duality (`c = -v`), the Shapley shares
are `(-2 / 3, -1 / 6, -1 / 6)`, i.e. surplus shares `(2 / 3, 1 / 6, 1 / 6)`. -/
def gloveGame : CooperativeGame (Fin 3) where
  val S := if (0 : Fin 3) ∈ S ∧ ((1 : Fin 3) ∈ S ∨ (2 : Fin 3) ∈ S) then 1 else 0
  val_empty := by simp

example :
    shapleyValue gloveGame.toCostSharingGame 0 = -(2 / 3) ∧
    shapleyValue gloveGame.toCostSharingGame 1 = -(1 / 6) ∧
    shapleyValue gloveGame.toCostSharingGame 2 = -(1 / 6) := by
  set G := gloveGame.toCostSharingGame
  have hsym12 : G.AreSymmetric 1 2 := by
    intro S h1S h2S
    simp only [G, CooperativeGame.toCostSharingGame, gloveGame]
    by_cases h0 : (0 : Fin 3) ∈ S <;> simp [h0, h1S, h2S]
  have hp12 : shapleyValue G 1 = shapleyValue G 2 := shapleyValue_isSymmetric G 1 2 hsym12
  have hp0 : shapleyValue G 0 = -(2 / 3) := by
    have her0 : (Finset.univ.erase (0 : Fin 3)).powerset = {∅, {1}, {2}, {1, 2}} := by decide
    have hcardA : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
    have hw0 : shapleyWeight 3 0 = 1 / 3 := by norm_num [shapleyWeight, Nat.factorial]
    have hw1 : shapleyWeight 3 1 = 1 / 6 := by norm_num [shapleyWeight, Nat.factorial]
    have hw2 : shapleyWeight 3 2 = 1 / 3 := by norm_num [shapleyWeight, Nat.factorial]
    rw [shapleyValue, hcardA, her0]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    norm_num [hw0, hw1, hw2, G, CooperativeGame.toCostSharingGame, gloveGame]
  have heff := shapleyValue_isEfficient G
  rw [Fin.sum_univ_three, hp0, ← hp12] at heff
  have huniv : G.cost Finset.univ = -1 := by
    simp [G, CooperativeGame.toCostSharingGame, gloveGame]
  rw [huniv] at heff
  exact ⟨hp0, by linarith, by linarith⟩

/-! ### Asymmetric Nash bargaining solution -/

/-- Asymmetric linear Pareto frontier `X = {(u₁, u₂) ≥ 0 | u₁ + 2 u₂ ≤ 4}` with disagreement
`(0, 0)`: maximizing `u₁ u₂` uniquely selects `(2, 1)`. -/
def asymBargaining : BargainingProblem where
  feasible := {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + 2 * x.2 ≤ 4}
  disagreement := (0, 0)
  disagreement_mem := ⟨le_rfl, le_rfl, by norm_num⟩
  convex := by
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    refine ⟨by nlinarith [hp.1, hq.1], by nlinarith [hp.2.1, hq.2.1], ?_⟩
    have : 4 = a * 4 + b * 4 := by linear_combination 4 * hab.symm
    nlinarith [hp.2.2, hq.2.2]
  isCompact := by
    have heq : {x : ℝ × ℝ | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + 2 * x.2 ≤ 4} =
        (Set.Icc (0 : ℝ) 4 ×ˢ Set.Icc (0 : ℝ) 2) ∩ {x : ℝ × ℝ | x.1 + 2 * x.2 ≤ 4} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc]
      exact ⟨fun ⟨h₁, h₂, hs⟩ => ⟨⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩, hs⟩,
        fun ⟨⟨⟨h₁, _⟩, ⟨h₂, _⟩⟩, hs⟩ => ⟨h₁, h₂, hs⟩⟩
    rw [heq]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le (continuous_fst.add (continuous_const.mul continuous_snd)) continuous_const)
  exists_strictlyIR := ⟨(2, 1), ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

example : nashBargainingSolution asymBargaining = (2, 1) := by
  symm
  refine nashBargainingSolution_unique_maximizer asymBargaining ?_ ?_
  · exact ⟨⟨by norm_num, by norm_num, by norm_num⟩,
      by norm_num [asymBargaining], by norm_num [asymBargaining]⟩
  · obtain ⟨⟨h₁, h₂, hsum⟩, _, _⟩ :=
      nashBargainingSolution_mem_individuallyRational asymBargaining
    set x := nashBargainingSolution asymBargaining
    simp only [BargainingProblem.nashProduct, asymBargaining]
    have hsq : 0 ≤ (x.1 - 2 * x.2) ^ 2 := sq_nonneg _
    have hsum_sq : (x.1 + 2 * x.2) ^ 2 ≤ 16 := by nlinarith
    nlinarith

end CslibFrontierTests.GameTheory.Cooperative

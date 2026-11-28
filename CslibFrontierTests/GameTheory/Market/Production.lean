/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Market.Production
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for Arrow–Debreu production economies and the First Welfare Theorem

* **Robinson Crusoe economy (`robinsonCrusoe`):** one consumer, one firm, two goods (`0` = input
  corn/labor, `1` = produced good) with convex technology `y 1 ^ 2 ≤ -y 0` and utility `b 0 * b 1`,
  checking equilibrium, exact market clearing, Pareto optimality via
  `ProductionEconomy.IsCompetitiveEquilibrium.isParetoOptimal`, and core membership via
  `ProductionEconomy.IsCompetitiveEquilibrium.isInCore`.
* **Sharpness counterexample 1 (`satiatedEcon`):** with a satiated consumer, a competitive
  equilibrium need not be Pareto optimal.
* **Sharpness counterexample 2 (`nonProfitMaxEcon`):** with a locally nonsatiated consumer and a
  firm that fails to maximize profit, consumer demand optimality plus exact clearing fail even weak
  Pareto optimality.
* **Exchange-market bridge witness (`bridgeEx`):** verifies
  `ExchangeMarket.toProductionEconomy_isCompetitiveEquilibrium_iff`,
  `ExchangeMarket.toProductionEconomy_isParetoOptimal_iff`, and
  `ProductionEconomy.IsCompetitiveEquilibrium.isParetoOptimal`.
-/

public section

namespace CslibFrontierTests.GameTheory.Market.Production

open Cslib.GameTheory.Market
open Finset

section RobinsonCrusoe

/-- Robinson Crusoe production economy: one consumer with endowment `![3, 0]` and utility
`b 0 * b 1`, and one firm converting good `0` into good `1` via `y 1 ^ 2 ≤ -y 0`. -/
def robinsonCrusoe : ProductionEconomy Unit Unit (Fin 2) where
  consumptionSet _ := {b | ∀ g, 0 ≤ b g}
  utility _ b := b 0 * b 1
  endowment _ := ![3, 0]
  productionSet _ := {y | y 0 ≤ 0 ∧ (0 ≤ y 1 → y 1 ^ 2 ≤ -y 0)}
  share _ _ := 1
  share_nonneg _ _ := zero_le_one
  share_sum _ := by simp

theorem robinsonCrusoe_lns :
    ∀ i, IsLocallyNonsatiatedOn (robinsonCrusoe.consumptionSet i) (robinsonCrusoe.utility i) := by
  intro _ b hb ε hε
  let b' : Fin 2 → ℝ := ![b 0 + ε / 2, b 1 + ε / 2]
  refine ⟨b', fun g => by fin_cases g <;> dsimp [b'] <;> linarith [hb 0, hb 1], ?_, ?_⟩
  · intro g
    fin_cases g <;>
      · dsimp [b']
        rw [add_sub_cancel_left, abs_of_pos (half_pos hε)]
        exact half_lt_self hε
  · dsimp [robinsonCrusoe, b']
    nlinarith [hb 0, hb 1]

theorem robinsonCrusoe_isCompetitiveEquilibrium :
    robinsonCrusoe.IsCompetitiveEquilibrium
      (fun _ => ![2, 1]) (fun _ => ![-1, 1]) ![1, 2] := by
  refine ⟨fun g => by fin_cases g <;> norm_num, ?_, ?_, ?_, ?_⟩
  · intro _
    rw [ProductionEconomy.mem_supplySet]
    refine ⟨⟨by norm_num, fun _ => by norm_num⟩, fun y' hy' => ?_⟩
    simp only [expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue]
    by_cases hy1 : 0 ≤ y' 1
    · have hsq := hy'.2 hy1
      nlinarith [sq_nonneg (y' 1 - 1)]
    · have hy0 : y' 0 ≤ 0 := hy'.1
      linarith
  · intro _
    rw [ProductionEconomy.mem_demandSet, mem_demandSetOn]
    refine ⟨⟨fun g => by fin_cases g <;> norm_num, ?_⟩, ?_⟩
    · simp only [ProductionEconomy.income_eq, robinsonCrusoe, Finset.univ_unique,
        Finset.sum_singleton, expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.isValue]
      norm_num
    · rintro b ⟨hb_nn, hb_exp⟩
      simp only [ProductionEconomy.income_eq, robinsonCrusoe, Finset.univ_unique,
        Finset.sum_singleton, expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.isValue] at hb_exp ⊢
      nlinarith [sq_nonneg (b 0 - 2 * b 1), hb_nn 0, hb_nn 1]
  · intro g
    fin_cases g
    · simp [ProductionEconomy.excessDemand_eq, ProductionEconomy.totalSupply_eq,
        ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum,
        robinsonCrusoe]
      norm_num
    · simp [ProductionEconomy.excessDemand_eq, ProductionEconomy.totalSupply_eq,
        ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum,
        robinsonCrusoe]
  · intro g
    fin_cases g
    · simp [ProductionEconomy.excessDemand_eq, ProductionEconomy.totalSupply_eq,
        ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum,
        robinsonCrusoe]
      norm_num
    · simp [ProductionEconomy.excessDemand_eq, ProductionEconomy.totalSupply_eq,
        ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum,
        robinsonCrusoe]

theorem robinsonCrusoe_isExactFeasible :
    robinsonCrusoe.IsExactFeasibleAllocation (fun _ => ![2, 1]) (fun _ => ![-1, 1]) :=
  robinsonCrusoe_isCompetitiveEquilibrium.isExactFeasibleAllocation_of_price_pos
    fun g => by fin_cases g <;> norm_num

theorem robinsonCrusoe_isParetoOptimal :
    robinsonCrusoe.IsParetoOptimal (fun _ => ![2, 1]) (fun _ => ![-1, 1]) :=
  robinsonCrusoe_isCompetitiveEquilibrium.isParetoOptimal robinsonCrusoe_lns

theorem robinsonCrusoe_isInCore :
    robinsonCrusoe.IsInCore (fun _ => ![2, 1]) (fun _ => ![-1, 1]) :=
  robinsonCrusoe_isCompetitiveEquilibrium.isInCore robinsonCrusoe_lns

end RobinsonCrusoe

section Counterexamples

/-- Two-consumer pure-exchange economy where consumer `0` is completely satiated (`u₀ ≡ 0`). -/
def satiatedEcon : ProductionEconomy (Fin 2) Empty Unit where
  consumptionSet _ := {b | ∀ g, 0 ≤ b g}
  utility i b := if i = 0 then 0 else b ()
  endowment _ _ := 1
  productionSet := Empty.elim
  share _ := Empty.elim
  share_nonneg _ j := j.elim
  share_sum j := j.elim

theorem satiatedEcon_isCompetitiveEquilibrium :
    satiatedEcon.IsCompetitiveEquilibrium (fun _ _ => 1) Empty.elim (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun j => j.elim, ?_, ?_, ?_⟩
  · intro i
    rw [ProductionEconomy.mem_demandSet, mem_demandSetOn]
    fin_cases i
    · refine ⟨⟨fun _ => zero_le_one, ?_⟩, fun b _ => le_rfl⟩
      simp [satiatedEcon, ProductionEconomy.income_eq, expenditure_eq_sum]
    · refine ⟨⟨fun _ => zero_le_one, ?_⟩, fun b hb => ?_⟩
      · simp [satiatedEcon, ProductionEconomy.income_eq, expenditure_eq_sum]
      · simpa [satiatedEcon, ProductionEconomy.income_eq, expenditure_eq_sum] using hb.2
  · intro _
    simp [satiatedEcon, ProductionEconomy.excessDemand_eq, ProductionEconomy.totalSupply_eq,
      ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum]
  · intro _
    simp [satiatedEcon, ProductionEconomy.excessDemand_eq, ProductionEconomy.totalSupply_eq,
      ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum]

theorem satiatedEcon_not_isParetoOptimal :
    ¬ satiatedEcon.IsParetoOptimal (fun _ _ => 1) Empty.elim := by
  rintro ⟨_, h⟩
  let x' : Fin 2 → Unit → ℝ := fun i _ => if i = 0 then 0 else 2
  refine h ⟨x', Empty.elim, ?_, ?_, 1, ?_⟩
  · refine ⟨fun i _ => by fin_cases i <;> norm_num [satiatedEcon, x'], fun j => j.elim, fun _ => ?_⟩
    simp [satiatedEcon, ProductionEconomy.totalSupply_eq, ProductionEconomy.totalEndowment_eq_sum,
      ProductionEconomy.totalProduction_eq_sum, Fin.sum_univ_two, x']
  · intro i
    fin_cases i <;> norm_num [satiatedEcon, x']
  · norm_num [satiatedEcon, x']

/-- Production economy where consumer utility is locally nonsatiated, exact clearing holds, and
the consumer maximizes utility, yet the firm fails to maximize profit and the allocation is not even
weakly Pareto optimal. -/
def nonProfitMaxEcon : ProductionEconomy Unit Unit (Fin 2) where
  consumptionSet _ := {b | ∀ g, 0 ≤ b g}
  utility _ b := b 0 + 2 * b 1
  endowment _ := ![1, 1]
  productionSet _ := {y | ∃ a ∈ Set.Icc (0 : ℝ) 1, y = ![-a, a]}
  share _ _ := 1
  share_nonneg _ _ := zero_le_one
  share_sum _ := by simp

theorem nonProfitMaxEcon_failure_without_profitMax :
    (∀ i, IsLocallyNonsatiatedOn (nonProfitMaxEcon.consumptionSet i) (nonProfitMaxEcon.utility i)) ∧
    (∀ i, (fun _ => ![1, 1]) i ∈ nonProfitMaxEcon.demandSet ![1, 2] (fun _ => ![0, 0]) i) ∧
    (∀ g, nonProfitMaxEcon.excessDemand (fun _ => ![1, 1]) (fun _ => ![0, 0]) g = 0) ∧
    (![0, 0] ∉ nonProfitMaxEcon.supplySet ![1, 2] ()) ∧
    ¬ nonProfitMaxEcon.IsWeaklyParetoOptimal (fun _ => ![1, 1]) (fun _ => ![0, 0]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ b hb ε hε
    refine ⟨![b 0 + ε / 2, b 1], fun g => by fin_cases g <;> dsimp <;> linarith [hb 0, hb 1],
      fun g => by fin_cases g <;> dsimp <;> simp [abs_of_pos (half_pos hε), hε, half_lt_self hε],
      ?_⟩
    dsimp [nonProfitMaxEcon]
    linarith
  · intro _
    rw [ProductionEconomy.mem_demandSet, mem_demandSetOn]
    refine ⟨⟨fun g => by fin_cases g <;> norm_num, ?_⟩, ?_⟩
    · simp [nonProfitMaxEcon, ProductionEconomy.income_eq, expenditure_eq_sum, Fin.sum_univ_two]
    · rintro b ⟨_, hb_exp⟩
      simp only [nonProfitMaxEcon, ProductionEconomy.income_eq, Finset.univ_unique,
        Finset.sum_singleton, expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.isValue] at hb_exp ⊢
      linarith
  · intro g
    fin_cases g <;>
      simp [nonProfitMaxEcon, ProductionEconomy.excessDemand_eq, ProductionEconomy.totalSupply_eq,
        ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum]
  · intro hsup
    rw [ProductionEconomy.mem_supplySet] at hsup
    have hy1 : ![-1, 1] ∈ nonProfitMaxEcon.productionSet () :=
      ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    have hle := hsup.2 ![-1, 1] hy1
    simp only [expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue] at hle
    norm_num at hle
  · rintro ⟨_, hnot⟩
    refine hnot ⟨fun _ => ![0, 2], fun _ => ![-1, 1], ?_, ?_⟩
    · refine ⟨fun _ g => by fin_cases g <;> norm_num, fun _ => ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, ?_⟩
      intro g
      fin_cases g
      · simp [nonProfitMaxEcon, ProductionEconomy.totalSupply_eq,
          ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum]
      · simp [nonProfitMaxEcon, ProductionEconomy.totalSupply_eq,
          ProductionEconomy.totalEndowment_eq_sum, ProductionEconomy.totalProduction_eq_sum]
        norm_num
    · intro _
      dsimp [nonProfitMaxEcon]
      norm_num

end Counterexamples

section BridgeTest

/-- Symmetric 2-trader, 2-good exchange market testing `ExchangeMarket.toProductionEconomy`. -/
def bridgeEx : ExchangeMarket (Fin 2) (Fin 2) where
  endowment i := if i = 0 then ![2, 0] else ![0, 2]
  utility _ b := b 0 + b 1
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> norm_num

theorem bridgeEx_equilibrium_and_pareto :
    bridgeEx.toProductionEconomy.IsCompetitiveEquilibrium
      (fun _ => ![1, 1]) Empty.elim (fun _ => 1) ∧
    bridgeEx.IsParetoOptimal (fun _ => ![1, 1]) := by
  have heq : bridgeEx.IsCompetitiveEquilibrium (fun _ => ![1, 1]) (fun _ => 1) := by
    refine ⟨fun _ => zero_le_one, ?_, ?_, ?_⟩
    · intro i
      rw [ExchangeMarket.mem_demandSet, Cslib.GameTheory.Market.mem_demandSet]
      refine ⟨⟨fun g => by fin_cases g <;> norm_num, ?_⟩, fun b hb => ?_⟩
      · fin_cases i <;>
          simp [bridgeEx, ExchangeMarket.income_eq, expenditure_eq_sum, Fin.sum_univ_two] <;>
          norm_num
      · have hexp := hb.2
        fin_cases i <;>
          simp [bridgeEx, ExchangeMarket.income_eq, expenditure_eq_sum,
            Fin.sum_univ_two] at hexp ⊢ <;>
          linarith
    · intro g
      fin_cases g <;>
        simp [bridgeEx, ExchangeMarket.excessDemand_eq, ExchangeMarket.totalSupply_eq_sum,
          Fin.sum_univ_two]
    · intro g
      fin_cases g <;>
        simp [bridgeEx, ExchangeMarket.excessDemand_eq, ExchangeMarket.totalSupply_eq_sum,
          Fin.sum_univ_two]
  have hlns : ∀ i, IsLocallyNonsatiated (bridgeEx.utility i) := by
    intro _ b hb ε hε
    refine ⟨![b 0 + ε / 2, b 1], fun g => by fin_cases g <;> dsimp <;> linarith [hb 0, hb 1],
      fun g => by fin_cases g <;> dsimp <;> simp [abs_of_pos (half_pos hε), hε, half_lt_self hε],
      ?_⟩
    dsimp [bridgeEx]
    linarith
  have heqProd :
      bridgeEx.toProductionEconomy.IsCompetitiveEquilibrium
        (fun _ => ![1, 1]) Empty.elim (fun _ => 1) :=
    (bridgeEx.toProductionEconomy_isCompetitiveEquilibrium_iff _ Empty.elim _).mpr heq
  exact ⟨heqProd,
    (bridgeEx.toProductionEconomy_isParetoOptimal_iff _ Empty.elim).mp
      (heqProd.isParetoOptimal fun i => by
        rw [ExchangeMarket.toProductionEconomy_consumptionSet,
          ExchangeMarket.toProductionEconomy_utility]
        exact hlns i)⟩

end BridgeTest

end CslibFrontierTests.GameTheory.Market.Production

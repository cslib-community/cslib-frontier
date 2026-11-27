/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.Core
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Arrow–Debreu production economies and the First Welfare Theorem

In an **Arrow–Debreu private-ownership production economy** (`ProductionEconomy I J G`,
[ArrowDebreu1954], §1; [Debreu1959], Chapters 5–6 (primary PDF unverified);
[MasColellWhinstonGreen1995], Section 16.C (primary PDF unverified)):

* each consumer `i : I` has a consumption set `consumptionSet i ⊆ (G → ℝ)`, a utility function
  `utility i : (G → ℝ) → ℝ`, and an initial endowment bundle `endowment i : G → ℝ`;
* each firm `j : J` has a production set `productionSet j ⊆ (G → ℝ)` in net-output convention
  (inputs negative, outputs positive);
* consumer `i` owns nonnegative share `share i j` of firm `j`'s profit (`∑ i, share i j = 1`).

In a **competitive equilibrium** `(x, y, p)`:
1. prices are nonnegative (`∀ g, 0 ≤ p g`);
2. every firm `j` maximizes profit `expenditure p (y j)` on `productionSet j` (`supplySet`);
3. every consumer `i` maximizes `utility i` on `consumptionSet i` within wealth
   `expenditure p (endowment i) + ∑ j, share i j * expenditure p (y j)` (`demandSet`);
4. markets clear with free disposal (`excessDemand x y g ≤ 0`) and complementary slackness
   (`p g * excessDemand x y g = 0`).

For the cooperative **core** (`IsBlockedBy` / `IsInCore`), a nonempty coalition `S : Finset I`
blocks `(x, y)` if it can choose consumption `x' i ∈ consumptionSet i` (`i ∈ S`) and production
plans `y' j ∈ productionSet j` within its coalition endowment and share-weighted production
`(∑ i ∈ S, endowment i g) + ∑ j, (∑ i ∈ S, share i j) * y' j g`, making every member of `S` weakly
better off and at least one strictly better off (private-ownership coalition production with
fractional firm-share weights `∑ i ∈ S, share i j`, generalizing [DebreuScarf1963]; primary PDF
unverified).

Notice that weak Pareto optimality of competitive equilibria
(`ProductionEconomy.IsCompetitiveEquilibrium.isWeaklyParetoOptimal`) holds unconditionally
whenever `I` is nonempty—requiring neither local nonsatiation nor monotonicity—since strict
improvements for every consumer already strictly exceed each consumer's budget via
`lt_expenditure_of_mem_demandSetOn`.

## Main definitions

* `Cslib.GameTheory.Market.ProductionEconomy`: Arrow–Debreu private-ownership economy with
  `totalEndowment`, `totalProduction`, `totalSupply`, `supplySet`, `income`, `IsBudgetFeasible`,
  `demandSet`, `IsFeasibleAllocation`, `IsExactFeasibleAllocation`, `excessDemand`,
  `IsCompetitiveEquilibrium`, `IsParetoOptimal`, `IsWeaklyParetoOptimal`, `IsBlockedBy`, `IsInCore`.
* `Cslib.GameTheory.Market.ExchangeMarket.toProductionEconomy`: canonical embedding of a pure
  exchange market `ExchangeMarket I G` as a production economy with `Empty` firms and nonnegative
  consumption sets `{b : G → ℝ | ∀ g, 0 ≤ b g}`.

## Main results

* `Cslib.GameTheory.Market.ProductionEconomy.sum_income`,
  `Cslib.GameTheory.Market.ProductionEconomy.walras_law`: aggregate wealth identity and **Walras's
  law** for private-ownership production economies.
* `Cslib.GameTheory.Market.ProductionEconomy.IsCompetitiveEquilibrium.isParetoOptimal`: **First
  Fundamental Theorem of Welfare Economics** ([ArrowDebreu1954]; [MasColellWhinstonGreen1995],
  Section 16.C, primary PDF unverified): under `IsLocallyNonsatiatedOn`, every competitive
  equilibrium allocation is Pareto optimal.
* `Cslib.GameTheory.Market.ProductionEconomy.IsCompetitiveEquilibrium.isWeaklyParetoOptimal`:
  weak First Welfare Theorem without local nonsatiation (requires only `[Nonempty I]`).
* `Cslib.GameTheory.Market.ProductionEconomy.IsCompetitiveEquilibrium.isInCore`: under
  `IsLocallyNonsatiatedOn`, every competitive equilibrium lies in the share-weighted core.
* `Cslib.GameTheory.Market.ExchangeMarket.toProductionEconomy_isCompetitiveEquilibrium_iff`,
  `Cslib.GameTheory.Market.ExchangeMarket.toProductionEconomy_isParetoOptimal_iff`,
  `Cslib.GameTheory.Market.ExchangeMarket.toProductionEconomy_isInCore_iff`,
  `Cslib.GameTheory.Market.ExchangeMarket.IsCompetitiveEquilibrium.isParetoOptimal_via_production`:
  exact correspondence between `ExchangeMarket` and `ProductionEconomy`.

## References

* [K. J. Arrow and G. Debreu,
  *Existence of an Equilibrium for a Competitive Economy*][ArrowDebreu1954]
* [G. Debreu, *Theory of Value*][Debreu1959] (primary PDF unverified)
* [A. Mas-Colell, M. D. Whinston, and J. R. Green,
  *Microeconomic Theory*][MasColellWhinstonGreen1995] (primary PDF unverified)
* [G. Debreu and H. Scarf, *A Limit Theorem on the Core of an Economy*][DebreuScarf1963]
  (primary PDF unverified)
-/

public section

namespace Cslib.GameTheory.Market

open Finset

/-! ### Private-ownership production economies -/

/-- An **Arrow–Debreu private-ownership production economy** ([ArrowDebreu1954], §1;
[Debreu1959], Chapters 5–6, primary PDF unverified) with consumers `I`, firms `J`, and goods `G`:
consumers have consumption sets `consumptionSet i`, utilities `utility i`, endowments
`endowment i`, and nonnegative firm profit shares `share i j` summing to `1` per firm; firms have
production sets `productionSet j` in net-output convention. -/
@[ext]
structure ProductionEconomy (I J G : Type*) [Fintype I] where
  /-- Consumption set `X_i ⊆ (G → ℝ)` of consumer `i`. -/
  consumptionSet : I → Set (G → ℝ)
  /-- Utility function `u_i : (G → ℝ) → ℝ` of consumer `i`. -/
  utility : I → (G → ℝ) → ℝ
  /-- Initial endowment bundle `ω_i : G → ℝ` of consumer `i`. -/
  endowment : I → G → ℝ
  /-- Net-output production possibility set `Y_j ⊆ (G → ℝ)` of firm `j`. -/
  productionSet : J → Set (G → ℝ)
  /-- Ownership share `θ_{ij}` of firm `j`'s profit held by consumer `i`. -/
  share : I → J → ℝ
  /-- Profit shares are nonnegative. -/
  share_nonneg : ∀ (i : I) (j : J), 0 ≤ share i j
  /-- Every firm's profit shares sum to `1` across consumers. -/
  share_sum : ∀ j : J, ∑ i : I, share i j = 1

namespace ProductionEconomy

/-- Aggregate net production `∑ j, y j g` of good `g` across firms `J`. -/
def totalProduction {J G : Type*} [Fintype J] (y : J → G → ℝ) (g : G) : ℝ :=
  ∑ j : J, y j g

theorem totalProduction_eq_sum {J G : Type*} [Fintype J] (y : J → G → ℝ) (g : G) :
    totalProduction y g = ∑ j : J, y j g := by rfl

section EndowmentAndSupply

variable {I J G : Type*} [Fintype I] (E : ProductionEconomy I J G)

/-- Aggregate initial endowment `∑ i, E.endowment i g` of good `g`. -/
def totalEndowment (g : G) : ℝ :=
  ∑ i : I, E.endowment i g

theorem totalEndowment_eq_sum (g : G) :
    E.totalEndowment g = ∑ i : I, E.endowment i g := by rfl

/-- Total resources `E.totalEndowment g + totalProduction y g` available for consumption. -/
def totalSupply [Fintype J] (y : J → G → ℝ) (g : G) : ℝ :=
  E.totalEndowment g + totalProduction y g

theorem totalSupply_eq [Fintype J] (y : J → G → ℝ) (g : G) :
    E.totalSupply y g = E.totalEndowment g + totalProduction y g := by rfl

end EndowmentAndSupply

section Prices

variable {I J G : Type*} [Fintype I] [Fintype G] (E : ProductionEconomy I J G)

/-- Profit-maximizing production plans of firm `j` on `E.productionSet j` at prices `p`. -/
def supplySet (p : G → ℝ) (j : J) : Set (G → ℝ) :=
  {y_j | y_j ∈ E.productionSet j ∧
    ∀ y', y' ∈ E.productionSet j → expenditure p y' ≤ expenditure p y_j}

@[simp] theorem mem_supplySet {p : G → ℝ} {j : J} {y_j : G → ℝ} :
    y_j ∈ E.supplySet p j ↔
      y_j ∈ E.productionSet j ∧
        ∀ y', y' ∈ E.productionSet j → expenditure p y' ≤ expenditure p y_j :=
  Iff.rfl

theorem supplySet_smul (p : G → ℝ) (j : J) {c : ℝ} (hc : 0 < c) :
    E.supplySet (c • p) j = E.supplySet p j := by
  ext y_j
  simp only [mem_supplySet, expenditure_smul_left, mul_le_mul_iff_right₀ hc]

variable [Fintype J]

/-- Consumer `i`'s wealth `expenditure p (E.endowment i) + ∑ j, E.share i j * expenditure p (y j)`
from endowment value and distributed firm profits at prices `p` and production profile `y`. -/
def income (p : G → ℝ) (y : J → G → ℝ) (i : I) : ℝ :=
  expenditure p (E.endowment i) + ∑ j : J, E.share i j * expenditure p (y j)

theorem income_eq (p : G → ℝ) (y : J → G → ℝ) (i : I) :
    E.income p y i =
      expenditure p (E.endowment i) + ∑ j : J, E.share i j * expenditure p (y j) := by rfl

theorem income_smul (c : ℝ) (p : G → ℝ) (y : J → G → ℝ) (i : I) :
    E.income (c • p) y i = c * E.income p y i := by
  simp only [income, expenditure_smul_left, mul_add, mul_left_comm (E.share i _), Finset.mul_sum]

/-- Aggregate consumer wealth equals the market value of total resources `E.totalSupply y`. -/
theorem sum_income (p : G → ℝ) (y : J → G → ℝ) :
    ∑ i : I, E.income p y i = expenditure p (E.totalSupply y) := by
  have hend : ∑ i : I, expenditure p (E.endowment i) = expenditure p E.totalEndowment := by
    simp only [expenditure_eq_sum, totalEndowment, Finset.mul_sum]
    exact Finset.sum_comm
  have hprod : ∑ i : I, ∑ j : J, E.share i j * expenditure p (y j) =
      expenditure p (totalProduction y) := by
    calc
      ∑ i : I, ∑ j : J, E.share i j * expenditure p (y j)
        = ∑ j : J, (∑ i : I, E.share i j) * expenditure p (y j) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ j : J, expenditure p (y j) := by simp only [E.share_sum, one_mul]
      _ = expenditure p (totalProduction y) := by
            simp only [expenditure_eq_sum, totalProduction_eq_sum, Finset.mul_sum]
            exact Finset.sum_comm
  calc
    ∑ i : I, E.income p y i
      = (∑ i : I, expenditure p (E.endowment i)) +
          ∑ i : I, ∑ j : J, E.share i j * expenditure p (y j) := by
            simp only [income, Finset.sum_add_distrib]
    _ = expenditure p E.totalEndowment + expenditure p (totalProduction y) := by rw [hend, hprod]
    _ = expenditure p (E.totalSupply y) := by
          rw [← expenditure_add]
          rfl

/-- Bundle `b` is budget-feasible for consumer `i` at prices `p` and production profile `y`. -/
@[expose] def IsBudgetFeasible (p : G → ℝ) (y : J → G → ℝ) (i : I) (b : G → ℝ) : Prop :=
  Market.IsBudgetFeasibleOn (E.consumptionSet i) p (E.income p y i) b

/-- Consumer `i`'s Marshallian demand set on `E.consumptionSet i` at `(p, y)`. -/
def demandSet (p : G → ℝ) (y : J → G → ℝ) (i : I) : Set (G → ℝ) :=
  Market.demandSetOn (E.consumptionSet i) (E.utility i) p (E.income p y i)

@[simp] theorem mem_demandSet {p : G → ℝ} {y : J → G → ℝ} {i : I} {b : G → ℝ} :
    b ∈ E.demandSet p y i ↔
      b ∈ Market.demandSetOn (E.consumptionSet i) (E.utility i) p (E.income p y i) :=
  Iff.rfl

theorem demandSet_smul (p : G → ℝ) (y : J → G → ℝ) (i : I) {c : ℝ} (hc : 0 < c) :
    E.demandSet (c • p) y i = E.demandSet p y i := by
  simp only [demandSet, E.income_smul]
  exact Market.demandSetOn_smul (E.consumptionSet i) (E.utility i) p (E.income p y i) hc

end Prices

section Allocations

variable {I J G : Type*} [Fintype I] [Fintype J] (E : ProductionEconomy I J G)

/-- Allocation `(x, y)` is **feasible** (with free disposal) if every `x i ∈ E.consumptionSet i`,
every `y j ∈ E.productionSet j`, and `∑ i, x i g ≤ E.totalSupply y g` for every good `g`. -/
@[expose] def IsFeasibleAllocation (x : I → G → ℝ) (y : J → G → ℝ) : Prop :=
  (∀ i, x i ∈ E.consumptionSet i) ∧ (∀ j, y j ∈ E.productionSet j) ∧
    ∀ g : G, ∑ i : I, x i g ≤ E.totalSupply y g

/-- Allocation `(x, y)` is **exact-feasible** (equality market clearing, no free disposal). -/
@[expose] def IsExactFeasibleAllocation (x : I → G → ℝ) (y : J → G → ℝ) : Prop :=
  (∀ i, x i ∈ E.consumptionSet i) ∧ (∀ j, y j ∈ E.productionSet j) ∧
    ∀ g : G, ∑ i : I, x i g = E.totalSupply y g

theorem IsExactFeasibleAllocation.isFeasibleAllocation {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} (hex : E.IsExactFeasibleAllocation x y) :
    E.IsFeasibleAllocation x y :=
  ⟨hex.1, hex.2.1, fun g => (hex.2.2 g).le⟩

/-- Aggregate excess demand `(∑ i, x i g) - E.totalSupply y g` for good `g`. -/
def excessDemand (x : I → G → ℝ) (y : J → G → ℝ) (g : G) : ℝ :=
  (∑ i : I, x i g) - E.totalSupply y g

theorem excessDemand_eq (x : I → G → ℝ) (y : J → G → ℝ) (g : G) :
    E.excessDemand x y g = (∑ i : I, x i g) - E.totalSupply y g := by rfl

/-- A feasible allocation `(x, y)` is **Pareto optimal** if no feasible `(x', y')` makes every
consumer weakly better off and at least one strictly better off. -/
@[expose] def IsParetoOptimal (x : I → G → ℝ) (y : J → G → ℝ) : Prop :=
  E.IsFeasibleAllocation x y ∧
    ¬ ∃ (x' : I → G → ℝ) (y' : J → G → ℝ), E.IsFeasibleAllocation x' y' ∧
      (∀ i, E.utility i (x i) ≤ E.utility i (x' i)) ∧
      ∃ i, E.utility i (x i) < E.utility i (x' i)

/-- A feasible allocation `(x, y)` is **weakly Pareto optimal** if no feasible `(x', y')` makes
every consumer strictly better off. -/
@[expose] def IsWeaklyParetoOptimal (x : I → G → ℝ) (y : J → G → ℝ) : Prop :=
  E.IsFeasibleAllocation x y ∧
    ¬ ∃ (x' : I → G → ℝ) (y' : J → G → ℝ), E.IsFeasibleAllocation x' y' ∧
      ∀ i, E.utility i (x i) < E.utility i (x' i)

theorem IsParetoOptimal.isWeaklyParetoOptimal [Nonempty I] {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} (hpo : E.IsParetoOptimal x y) :
    E.IsWeaklyParetoOptimal x y :=
  ⟨hpo.1, fun ⟨x', y', hfeas, hlt⟩ =>
    let ⟨i₀⟩ := ‹Nonempty I›
    hpo.2 ⟨x', y', hfeas, fun i => (hlt i).le, i₀, hlt i₀⟩⟩

end Allocations

section Equilibrium

variable {I J G : Type*} [Fintype I] [Fintype J] [Fintype G] (E : ProductionEconomy I J G)

theorem expenditure_excessDemand (p : G → ℝ) (x : I → G → ℝ) (y : J → G → ℝ) :
    expenditure p (E.excessDemand x y) = ∑ i : I, (expenditure p (x i) - E.income p y i) := by
  calc
    expenditure p (E.excessDemand x y)
      = (∑ g : G, p g * ∑ i : I, x i g) - expenditure p (E.totalSupply y) := by
          simp only [expenditure_eq_sum, excessDemand, mul_sub, Finset.sum_sub_distrib]
    _ = (∑ i : I, expenditure p (x i)) - ∑ i : I, E.income p y i := by
          rw [E.sum_income p y]
          congr 1
          simp only [expenditure_eq_sum, Finset.mul_sum]
          exact Finset.sum_comm
    _ = ∑ i : I, (expenditure p (x i) - E.income p y i) := (Finset.sum_sub_distrib _ _).symm

/-- **Weak Walras inequality** for production economies. -/
theorem expenditure_excessDemand_le_zero {p : G → ℝ} {x : I → G → ℝ} {y : J → G → ℝ}
    (hfeas : ∀ i, E.IsBudgetFeasible p y i (x i)) :
    expenditure p (E.excessDemand x y) ≤ 0 := by
  rw [E.expenditure_excessDemand]
  exact Finset.sum_nonpos fun i _ => sub_nonpos.2 (hfeas i).2

/-- **Walras's law** for production economies: under local nonsatiation on `E.consumptionSet i`,
optimal consumer demand implies zero aggregate excess-demand value. -/
theorem walras_law {p : G → ℝ} {x : I → G → ℝ} {y : J → G → ℝ}
    (hlns : ∀ i, IsLocallyNonsatiatedOn (E.consumptionSet i) (E.utility i))
    (hdem : ∀ i, x i ∈ E.demandSet p y i) :
    expenditure p (E.excessDemand x y) = 0 := by
  rw [E.expenditure_excessDemand]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(hlns i).expenditure_eq_of_mem_demandSetOn ((E.mem_demandSet).1 (hdem i)), sub_self]

/-- A **competitive (Walrasian) equilibrium** `(x, y, p)` of `ProductionEconomy`
([ArrowDebreu1954], §1): nonnegative prices `p`, profit maximization by each firm `j`, utility
maximization within wealth by each consumer `i`, free-disposal market clearing `excessDemand x y g ≤
0`, and complementary slackness `p g * excessDemand x y g = 0`. -/
@[expose] def IsCompetitiveEquilibrium (x : I → G → ℝ) (y : J → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ (∀ j, y j ∈ E.supplySet p j) ∧ (∀ i, x i ∈ E.demandSet p y i) ∧
    (∀ g, E.excessDemand x y g ≤ 0) ∧ ∀ g, p g * E.excessDemand x y g = 0

theorem IsCompetitiveEquilibrium.isFeasibleAllocation {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x y p) :
    E.IsFeasibleAllocation x y :=
  ⟨fun i => ((Market.mem_demandSetOn).1 ((E.mem_demandSet).1 (heq.2.2.1 i))).1.1,
    fun j => (heq.2.1 j).1, fun g => sub_nonpos.1 (heq.2.2.2.1 g)⟩

theorem IsCompetitiveEquilibrium.smul {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x y p)
    {c : ℝ} (hc : 0 < c) : E.IsCompetitiveEquilibrium x y (c • p) :=
  ⟨fun g => mul_nonneg hc.le (heq.1 g),
    fun j => (E.supplySet_smul p j hc).symm ▸ heq.2.1 j,
    fun i => (E.demandSet_smul p y i hc).symm ▸ heq.2.2.1 i,
    heq.2.2.2.1, fun g => by simp [smul_eq_mul, mul_assoc, heq.2.2.2.2 g]⟩

theorem IsCompetitiveEquilibrium.of_locallyNonsatiated {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ}
    (hlns : ∀ i, IsLocallyNonsatiatedOn (E.consumptionSet i) (E.utility i))
    (hp : ∀ g, 0 ≤ p g) (hsup : ∀ j, y j ∈ E.supplySet p j) (hdem : ∀ i, x i ∈ E.demandSet p y i)
    (hclear : ∀ g, E.excessDemand x y g ≤ 0) :
    E.IsCompetitiveEquilibrium x y p := by
  refine ⟨hp, hsup, hdem, hclear, fun g => ?_⟩
  have hwal : ∑ k : G, p k * E.excessDemand x y k = 0 := by
    rw [← expenditure_eq_sum]
    exact E.walras_law hlns hdem
  exact (Finset.sum_eq_zero_iff_of_nonpos fun k _ =>
    mul_nonpos_of_nonneg_of_nonpos (hp k) (hclear k)).1 hwal g (Finset.mem_univ g)

theorem IsCompetitiveEquilibrium.sum_eq_totalSupply_of_price_pos {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x y p)
    {g : G} (hpg : 0 < p g) : ∑ i : I, x i g = E.totalSupply y g :=
  sub_eq_zero.1 ((mul_eq_zero.1 (heq.2.2.2.2 g)).resolve_left hpg.ne')

theorem IsCompetitiveEquilibrium.isExactFeasibleAllocation_of_price_pos
    {E : ProductionEconomy I J G} {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x y p) (hp_pos : ∀ g, 0 < p g) :
    E.IsExactFeasibleAllocation x y :=
  ⟨fun i => ((Market.mem_demandSetOn).1 ((E.mem_demandSet).1 (heq.2.2.1 i))).1.1,
    fun j => (heq.2.1 j).1, fun g => heq.sum_eq_totalSupply_of_price_pos (hp_pos g)⟩

end Equilibrium

/-! ### First Welfare Theorem and private-ownership core -/

section WelfareAndCore

variable {I J G : Type*} [Fintype I] [Fintype J] [Fintype G]

/-- Shared coalition-level supply/profit expenditure bound: at nonnegative prices `p` and
profit-maximizing plans `yj`, any consumption/production plans `(x', y')` respecting coalition `S`'s
endowments and share-weighted production cost at most `∑ i ∈ S, E.income p yj i`. -/
private theorem sum_expenditure_le_sum_income_of_supplySet {E : ProductionEconomy I J G}
    {S : Finset I} {p : G → ℝ} {x' : I → G → ℝ} {yj y' : J → G → ℝ}
    (hp : ∀ g, 0 ≤ p g)
    (hsup : ∀ j, yj j ∈ E.supplySet p j)
    (hy'_mem : ∀ j, y' j ∈ E.productionSet j)
    (hclear : ∀ g : G,
      ∑ i ∈ S, x' i g ≤ (∑ i ∈ S, E.endowment i g) + ∑ j : J, (∑ i ∈ S, E.share i j) * y' j g) :
    ∑ i ∈ S, expenditure p (x' i) ≤ ∑ i ∈ S, E.income p yj i := by
  calc
    ∑ i ∈ S, expenditure p (x' i)
      = ∑ g : G, p g * ∑ i ∈ S, x' i g := by
          simp only [expenditure_eq_sum, Finset.mul_sum]
          exact Finset.sum_comm
    _ ≤ ∑ g : G, p g *
          ((∑ i ∈ S, E.endowment i g) + ∑ j : J, (∑ i ∈ S, E.share i j) * y' j g) :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hclear g) (hp g)
    _ = (∑ i ∈ S, expenditure p (E.endowment i)) +
          ∑ j : J, (∑ i ∈ S, E.share i j) * expenditure p (y' j) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · simp only [expenditure_eq_sum, Finset.mul_sum]
          exact Finset.sum_comm
        · simp only [expenditure_eq_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun g _ => by ring
    _ ≤ (∑ i ∈ S, expenditure p (E.endowment i)) +
          ∑ j : J, (∑ i ∈ S, E.share i j) * expenditure p (yj j) := by
        gcongr with j _
        · exact Finset.sum_nonneg fun i _ => E.share_nonneg i j
        · exact (hsup j).2 (y' j) (hy'_mem j)
    _ = ∑ i ∈ S, E.income p yj i := by
        simp only [income_eq, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_mul S (fun i => E.share i j) _

private theorem sum_expenditure_le_sum_income_univ {E : ProductionEconomy I J G}
    {p : G → ℝ} {x' : I → G → ℝ} {y y' : J → G → ℝ}
    (hp : ∀ g, 0 ≤ p g) (hsup : ∀ j, y j ∈ E.supplySet p j)
    (hfeas : E.IsFeasibleAllocation x' y') :
    ∑ i : I, expenditure p (x' i) ≤ ∑ i : I, E.income p y i := by
  refine sum_expenditure_le_sum_income_of_supplySet hp hsup hfeas.2.1 fun g => ?_
  simpa only [E.share_sum, one_mul, totalSupply, totalEndowment, totalProduction] using hfeas.2.2 g

/-- **First Fundamental Theorem of Welfare Economics with production** ([ArrowDebreu1954];
[MasColellWhinstonGreen1995], Section 16.C, primary PDF unverified): if every consumer's utility
is locally nonsatiated on `E.consumptionSet i`, every competitive equilibrium `(x, y, p)` is Pareto
optimal. -/
theorem IsCompetitiveEquilibrium.isParetoOptimal {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x y p)
    (hlns : ∀ i, IsLocallyNonsatiatedOn (E.consumptionSet i) (E.utility i)) :
    E.IsParetoOptimal x y := by
  refine ⟨heq.isFeasibleAllocation, ?_⟩
  rintro ⟨x', y', hfeas, hweak, i₀, hstrict⟩
  exact not_exists_paretoImprovementOn
    (fun i _ => (E.mem_demandSet).1 (heq.2.2.1 i)) (fun i _ => hlns i) (fun i _ => hfeas.1 i)
    (sum_expenditure_le_sum_income_univ heq.1 heq.2.1 hfeas)
    ⟨fun i _ => hweak i, i₀, Finset.mem_univ i₀, hstrict⟩

/-- **Weak First Welfare Theorem without local nonsatiation**: for any nonempty finite consumer set
`I`, every competitive equilibrium `(x, y, p)` is weakly Pareto optimal without any local
nonsatiation or monotonicity assumption. -/
theorem IsCompetitiveEquilibrium.isWeaklyParetoOptimal [Nonempty I] {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x y p) :
    E.IsWeaklyParetoOptimal x y := by
  refine ⟨heq.isFeasibleAllocation, ?_⟩
  rintro ⟨x', y', hfeas, hstrict⟩
  exact not_exists_strictParetoImprovementOn Finset.univ_nonempty
    (fun i _ => (E.mem_demandSet).1 (heq.2.2.1 i)) (fun i _ => hfeas.1 i)
    (sum_expenditure_le_sum_income_univ heq.1 heq.2.1 hfeas)
    fun i _ => hstrict i

/-- A nonempty coalition `S : Finset I` **blocks** `(x, y)` in a private-ownership production
economy via `(x', y')` if `x' i ∈ E.consumptionSet i` (`i ∈ S`), `y' j ∈ E.productionSet j`,
coalition consumption uses at most `(∑ i ∈ S, E.endowment i g) + ∑ j, (∑ i ∈ S, E.share i j) *
y' j g` of every good, every member of `S` is weakly better off, and at least one is strictly
better off (share-weighted production extension of [DebreuScarf1963]; primary PDF unverified). -/
@[expose] def IsBlockedBy (E : ProductionEconomy I J G) (S : Finset I)
    (x' : I → G → ℝ) (y' : J → G → ℝ) (x : I → G → ℝ) : Prop :=
  S.Nonempty ∧
    (∀ i ∈ S, x' i ∈ E.consumptionSet i) ∧
    (∀ j, y' j ∈ E.productionSet j) ∧
    (∀ g : G, ∑ i ∈ S, x' i g ≤
      (∑ i ∈ S, E.endowment i g) + ∑ j : J, (∑ i ∈ S, E.share i j) * y' j g) ∧
    (∀ i ∈ S, E.utility i (x i) ≤ E.utility i (x' i)) ∧
    ∃ i ∈ S, E.utility i (x i) < E.utility i (x' i)

/-- The **core** of a private-ownership production economy: feasible allocations `(x, y)` that no
nonempty coalition can block under share-weighted coalition production. -/
@[expose] def IsInCore (E : ProductionEconomy I J G) (x : I → G → ℝ) (y : J → G → ℝ) : Prop :=
  E.IsFeasibleAllocation x y ∧ ∀ (S : Finset I) (x' : I → G → ℝ) (y' : J → G → ℝ),
    ¬ E.IsBlockedBy S x' y' x

omit [Fintype G] in
theorem IsInCore.isParetoOptimal [Nonempty I] {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} (hcore : E.IsInCore x y) :
    E.IsParetoOptimal x y := by
  refine ⟨hcore.1, fun ⟨x', y', hfeas, hweak, i₀, hstrict⟩ => ?_⟩
  refine hcore.2 univ x' y' ⟨univ_nonempty, fun i _ => hfeas.1 i, hfeas.2.1, fun g => ?_,
    fun i _ => hweak i, i₀, mem_univ i₀, hstrict⟩
  simpa only [E.share_sum, one_mul, totalSupply, totalEndowment, totalProduction] using hfeas.2.2 g

/-- **Core inclusion with production**: under local nonsatiation on `E.consumptionSet i`, every
competitive equilibrium allocation belongs to the share-weighted private-ownership core. -/
theorem IsCompetitiveEquilibrium.isInCore {E : ProductionEconomy I J G}
    {x : I → G → ℝ} {y : J → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x y p)
    (hlns : ∀ i, IsLocallyNonsatiatedOn (E.consumptionSet i) (E.utility i)) :
    E.IsInCore x y := by
  refine ⟨heq.isFeasibleAllocation, fun S x' y' hblock => ?_⟩
  obtain ⟨_, hx'_mem, hy'_mem, hclear, hweak, i₀, hi₀S, hstrict⟩ := hblock
  exact not_exists_paretoImprovementOn
    (fun i _ => (E.mem_demandSet).1 (heq.2.2.1 i)) (fun i _ => hlns i) hx'_mem
    (sum_expenditure_le_sum_income_of_supplySet heq.1 heq.2.1 hy'_mem hclear)
    ⟨hweak, i₀, hi₀S, hstrict⟩

end WelfareAndCore

end ProductionEconomy

/-! ### Bridge from `ExchangeMarket` to `ProductionEconomy` -/

namespace ExchangeMarket

section ProductionBridge

variable {I G : Type*} [Fintype I]

/-- View an `ExchangeMarket I G` as a `ProductionEconomy I Empty G` with no firms (`Empty`) and
nonnegative consumption sets `{b : G → ℝ | ∀ g, 0 ≤ b g}`. -/
def toProductionEconomy (E : ExchangeMarket I G) : ProductionEconomy I Empty G where
  consumptionSet _ := {b : G → ℝ | ∀ g, 0 ≤ b g}
  utility := E.utility
  endowment := E.endowment
  productionSet := Empty.elim
  share _ := Empty.elim
  share_nonneg _ j := j.elim
  share_sum j := j.elim

@[simp] theorem toProductionEconomy_consumptionSet (E : ExchangeMarket I G) (i : I) :
    E.toProductionEconomy.consumptionSet i = {b : G → ℝ | ∀ g, 0 ≤ b g} := by rfl

@[simp] theorem toProductionEconomy_utility (E : ExchangeMarket I G) :
    E.toProductionEconomy.utility = E.utility := by rfl

@[simp] theorem toProductionEconomy_endowment (E : ExchangeMarket I G) :
    E.toProductionEconomy.endowment = E.endowment := by rfl

@[simp] theorem toProductionEconomy_totalEndowment (E : ExchangeMarket I G) (g : G) :
    E.toProductionEconomy.totalEndowment g = E.totalSupply g := by
  rw [ProductionEconomy.totalEndowment_eq_sum, ExchangeMarket.totalSupply_eq_sum]
  rfl

@[simp] theorem toProductionEconomy_totalSupply (E : ExchangeMarket I G)
    (y : Empty → G → ℝ) (g : G) :
    E.toProductionEconomy.totalSupply y g = E.totalSupply g := by
  rw [ProductionEconomy.totalSupply_eq, ProductionEconomy.totalProduction_eq_sum]
  simp

@[simp] theorem toProductionEconomy_excessDemand (E : ExchangeMarket I G)
    (x : I → G → ℝ) (y : Empty → G → ℝ) :
    E.toProductionEconomy.excessDemand x y = E.excessDemand x := by
  ext g
  rw [ProductionEconomy.excessDemand_eq, ExchangeMarket.excessDemand_eq,
    toProductionEconomy_totalSupply]

theorem toProductionEconomy_isFeasibleAllocation_iff (E : ExchangeMarket I G)
    (x : I → G → ℝ) (y : Empty → G → ℝ) :
    E.toProductionEconomy.IsFeasibleAllocation x y ↔ E.IsFeasibleAllocation x := by
  simp [ProductionEconomy.IsFeasibleAllocation, ExchangeMarket.IsFeasibleAllocation]

theorem toProductionEconomy_isParetoOptimal_iff (E : ExchangeMarket I G)
    (x : I → G → ℝ) (y : Empty → G → ℝ) :
    E.toProductionEconomy.IsParetoOptimal x y ↔ E.IsParetoOptimal x := by
  simp only [ProductionEconomy.IsParetoOptimal, ExchangeMarket.IsParetoOptimal,
    toProductionEconomy_isFeasibleAllocation_iff, toProductionEconomy_utility]
  constructor <;> rintro ⟨hf, h⟩ <;> refine ⟨hf, ?_⟩
  · rintro ⟨x', hx', hw, i, hs⟩
    exact h ⟨x', Empty.elim, hx', hw, i, hs⟩
  · rintro ⟨x', _, hx', hw, i, hs⟩
    exact h ⟨x', hx', hw, i, hs⟩

theorem toProductionEconomy_isInCore_iff (E : ExchangeMarket I G)
    (x : I → G → ℝ) (y : Empty → G → ℝ) :
    E.toProductionEconomy.IsInCore x y ↔ E.IsInCore x := by
  simp only [ProductionEconomy.IsInCore, ExchangeMarket.IsInCore,
    ProductionEconomy.IsBlockedBy, ExchangeMarket.IsBlockedBy,
    toProductionEconomy_isFeasibleAllocation_iff, toProductionEconomy_consumptionSet,
    toProductionEconomy_utility, toProductionEconomy_endowment]
  constructor <;> rintro ⟨hf, h⟩ <;> refine ⟨hf, ?_⟩
  · intro S z ⟨hS, hz_nn, hz_end, hw, hs⟩
    exact h S z Empty.elim ⟨hS, hz_nn, fun j => j.elim, by simpa using hz_end, hw, hs⟩
  · intro S z _ ⟨hS, hz_nn, _, hz_end, hw, hs⟩
    exact h S z ⟨hS, hz_nn, by simpa using hz_end, hw, hs⟩

section WithGoodsFintype

variable [Fintype G]

@[simp] theorem toProductionEconomy_income (E : ExchangeMarket I G) (p : G → ℝ)
    (y : Empty → G → ℝ) (i : I) : E.toProductionEconomy.income p y i = E.income p i := by
  rw [ProductionEconomy.income_eq, ExchangeMarket.income_eq]
  simp

@[simp] theorem toProductionEconomy_demandSet (E : ExchangeMarket I G) (p : G → ℝ)
    (y : Empty → G → ℝ) (i : I) :
    E.toProductionEconomy.demandSet p y i = E.demandSet p i := by
  ext b
  rw [ProductionEconomy.mem_demandSet, ExchangeMarket.mem_demandSet,
    Market.mem_demandSetOn, Market.mem_demandSet,
    toProductionEconomy_income, toProductionEconomy_consumptionSet, toProductionEconomy_utility]
  rfl

theorem toProductionEconomy_isCompetitiveEquilibrium_iff (E : ExchangeMarket I G)
    (x : I → G → ℝ) (y : Empty → G → ℝ) (p : G → ℝ) :
    E.toProductionEconomy.IsCompetitiveEquilibrium x y p ↔ E.IsCompetitiveEquilibrium x p := by
  simp [ProductionEconomy.IsCompetitiveEquilibrium, ExchangeMarket.IsCompetitiveEquilibrium,
    ProductionEconomy.supplySet]

/-- Derivation of `ExchangeMarket.IsCompetitiveEquilibrium.isParetoOptimal` directly from
`ProductionEconomy.IsCompetitiveEquilibrium.isParetoOptimal` via `toProductionEconomy`. -/
theorem IsCompetitiveEquilibrium.isParetoOptimal_via_production {E : ExchangeMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) : E.IsParetoOptimal x := by
  rw [← E.toProductionEconomy_isParetoOptimal_iff x Empty.elim]
  exact ProductionEconomy.IsCompetitiveEquilibrium.isParetoOptimal
    ((E.toProductionEconomy_isCompetitiveEquilibrium_iff x Empty.elim p).mpr heq) hlns

end WithGoodsFintype

end ProductionBridge

end ExchangeMarket

end Cslib.GameTheory.Market

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Compact

/-!
# Linear Fisher markets and the Eisenberg–Gale convex program

In Fisher's linear market model ([EisenbergGale1959]; [Vazirani2007], Section 5.2, pp. 105–107),
each buyer `i : I` arrives with money budget `budget i ≥ 0` and additive linear utility
`buyerUtility x i = ∑ g, utility i g * x i g` over divisible goods `g : G` of supply
`supply g ≥ 0` (`LinearFisherMarket.unitSupply` specializes to unit supply `supply g = 1`).

Eisenberg and Gale [EisenbergGale1959] proved that the market equilibria of a non-degenerate linear
Fisher market are captured by maximizing the budget-weighted logarithmic Nash social welfare
(`eisenbergGaleObjective`, Program `(5.1)` of [Vazirani2007], Section 5.2, p. 105):

`max ∑ i, budget i * log (∑ g, utility i g * x i g)` subject to `∑ i, x i g ≤ supply g` and `x ≥ 0`.

This module establishes the three-way equivalence between linear Fisher market equilibria, the
Karush–Kuhn–Tucker / maximum bang-per-buck conditions (`IsEisenbergGaleKKT` and `bangPerBuck`), and
global maximizers of `eisenbergGaleObjective` ([Vazirani2007], Section 5.2, pp. 105–107; KKT
conditions `(i)`–`(iv)` on p. 106), together with existence of equilibrium, convexity of the
equilibrium allocation set, and uniqueness of equilibrium utilities and prices ([Vazirani2007],
Theorem 5.1, p. 107).

## Main definitions

* `Cslib.GameTheory.Market.LinearFisherMarket`: linear Fisher market with budgets, supplies, and
  marginal utilities, with `unitSupply`, `toFisherMarket`, `toLinearExchangeMarket`,
  `buyerUtility`, `bangPerBuck`, `IsEquilibrium`, and `IsParetoOptimal`.
* `Cslib.GameTheory.Market.LinearFisherMarket.IsNonDegenerate`: standard non-degeneracy hypotheses
  of [Vazirani2007], Section 5.2 (positive budgets and supplies, every buyer desires some good, and
  every good is desired by some buyer).
* `Cslib.GameTheory.Market.LinearFisherMarket.eisenbergGaleObjective`,
  `Cslib.GameTheory.Market.LinearFisherMarket.IsPositiveUtilityAllocation`,
  `Cslib.GameTheory.Market.LinearFisherMarket.IsEisenbergGaleKKT`,
  `Cslib.GameTheory.Market.LinearFisherMarket.eisenbergGaleDualPrice`: the Eisenberg–Gale objective
  `(5.1)`, its positive-utility feasible domain, its KKT optimality conditions, and the explicit
  dual equilibrium price vector `max_i (budget i * utility i g / buyerUtility x i)`.

## Main results

* `Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_bangPerBuck`: a non-degenerate
  linear Fisher market clears at `(x, p)` if and only if prices are positive, all supplies and
  budgets are exhausted, and buyers purchase only maximum bang-per-buck goods (`utility i g / p g`).
* `Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_isEisenbergGaleKKT`: market
  equilibrium is equivalent to the Eisenberg–Gale KKT optimality conditions ([Vazirani2007],
  Section 5.2, p. 106).
* `Cslib.GameTheory.Market.LinearFisherMarket.IsEisenbergGaleKKT.eisenbergGaleObjective_le`,
  `Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_isMaxOn_eisenbergGaleObjective`:
  an allocation participates in a market equilibrium if and only if it maximizes the Eisenberg–Gale
  program `(5.1)`, with dual prices `eisenbergGaleDualPrice x`.
* `Cslib.GameTheory.Market.LinearFisherMarket.IsNonDegenerate.exists_isEquilibrium`: existence of a
  market equilibrium in every non-degenerate linear Fisher market ([EisenbergGale1959];
  [Vazirani2007], Theorem 5.1, p. 107).
* `Cslib.GameTheory.Market.LinearFisherMarket.convex_setOf_exists_isEquilibrium`: convexity of the
  set of equilibrium allocations ([Vazirani2007], Theorem 5.1, p. 107).
* `Cslib.GameTheory.Market.LinearFisherMarket.buyerUtility_eq_of_isEquilibrium`,
  `Cslib.GameTheory.Market.LinearFisherMarket.price_eq_of_isEquilibrium`: uniqueness of equilibrium
  buyer utilities and equilibrium prices ([Vazirani2007], Theorem 5.1, p. 107).
* `Cslib.GameTheory.Market.LinearFisherMarket.IsEquilibrium.isParetoOptimal`: Pareto optimality of
  linear Fisher market equilibria.
* `Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_iff_toLinearExchangeMarket`,
  `Cslib.GameTheory.Market.LinearFisherMarket.isEquilibrium_smul_of_toLinearExchangeMarket`:
  reduction of linear Fisher market equilibrium to linear Arrow–Debreu exchange equilibrium
  ([CodenottiVaradarajan2007], Section 6.1.7, p. 140).

## References

* [CodenottiVaradarajan2007]
* [EisenbergGale1959]
* [Vazirani2007]
-/

public section

namespace Cslib.GameTheory.Market

/-- A **linear Fisher market** ([EisenbergGale1959]; [Vazirani2007], Section 5.2, p. 105): each
buyer `i : I` has nonnegative money budget `budget i` and nonnegative marginal utilities
`utility i : G → ℝ` over divisible goods `g : G` of supply `supply g ≥ 0`. -/
structure LinearFisherMarket (I G : Type*) where
  /-- Money budget `budget i` available to buyer `i`. -/
  budget : I → ℝ
  /-- Available supply `supply g` of divisible good `g`. -/
  supply : G → ℝ
  /-- Marginal utility `utility i g` obtained by buyer `i` per unit of good `g`. -/
  utility : I → G → ℝ
  /-- Buyer budgets are nonnegative. -/
  budget_nonneg : ∀ i : I, 0 ≤ budget i
  /-- Good supplies are nonnegative. -/
  supply_nonneg : ∀ g : G, 0 ≤ supply g
  /-- Marginal utilities are nonnegative. -/
  utility_nonneg : ∀ (i : I) (g : G), 0 ≤ utility i g

namespace LinearFisherMarket

section Definitions

variable {I G : Type*}

/-- Construct a linear Fisher market with unit supply (`supply g = 1`) of every good, the
normalization used throughout [Vazirani2007], Section 5.2, Program `(5.1)`, p. 105. -/
def unitSupply (budget : I → ℝ) (utility : I → G → ℝ)
    (budget_nonneg : ∀ i, 0 ≤ budget i) (utility_nonneg : ∀ i g, 0 ≤ utility i g) :
    LinearFisherMarket I G where
  budget := budget
  supply _ := 1
  utility := utility
  budget_nonneg := budget_nonneg
  supply_nonneg _ := zero_le_one
  utility_nonneg := utility_nonneg

@[simp] theorem unitSupply_budget (budget : I → ℝ) (utility : I → G → ℝ)
    (hb : ∀ i, 0 ≤ budget i) (hu : ∀ i g, 0 ≤ utility i g) :
    (unitSupply budget utility hb hu).budget = budget := by rfl

@[simp] theorem unitSupply_supply (budget : I → ℝ) (utility : I → G → ℝ)
    (hb : ∀ i, 0 ≤ budget i) (hu : ∀ i g, 0 ≤ utility i g) (g : G) :
    (unitSupply budget utility hb hu).supply g = 1 := by rfl

@[simp] theorem unitSupply_utility (budget : I → ℝ) (utility : I → G → ℝ)
    (hb : ∀ i, 0 ≤ budget i) (hu : ∀ i g, 0 ≤ utility i g) :
    (unitSupply budget utility hb hu).utility = utility := by rfl

/-- View a `LinearFisherMarket` as a general `FisherMarket` with `linearUtility` [Fintype G]. -/
def toFisherMarket [Fintype G] (M : LinearFisherMarket I G) : FisherMarket I G where
  budget := M.budget
  supply := M.supply
  utility i := linearUtility (M.utility i)
  budget_nonneg := M.budget_nonneg
  supply_nonneg := M.supply_nonneg

@[simp] theorem toFisherMarket_budget [Fintype G] (M : LinearFisherMarket I G) :
    M.toFisherMarket.budget = M.budget := by rfl

@[simp] theorem toFisherMarket_supply [Fintype G] (M : LinearFisherMarket I G) :
    M.toFisherMarket.supply = M.supply := by rfl

@[simp] theorem toFisherMarket_utility [Fintype G] (M : LinearFisherMarket I G) (i : I) :
    M.toFisherMarket.utility i = linearUtility (M.utility i) := by rfl

/-- Embed a linear Fisher market into a `LinearExchangeMarket` by giving buyer `i` fraction
`budget i / totalBudget` of every good's supply ([CodenottiVaradarajan2007], Section 6.1.7,
p. 140). -/
noncomputable def toLinearExchangeMarket [Fintype I] (M : LinearFisherMarket I G) :
    LinearExchangeMarket I G where
  endowment i g := (M.budget i / ∑ k : I, M.budget k) * M.supply g
  utility := M.utility
  endowment_nonneg i g :=
    mul_nonneg
      (div_nonneg (M.budget_nonneg i) (Finset.sum_nonneg fun k _ => M.budget_nonneg k))
      (M.supply_nonneg g)
  utility_nonneg := M.utility_nonneg

@[simp] theorem toLinearExchangeMarket_endowment [Fintype I] (M : LinearFisherMarket I G)
    (i : I) (g : G) :
    M.toLinearExchangeMarket.endowment i g =
      (M.budget i / ∑ k : I, M.budget k) * M.supply g := by rfl

@[simp] theorem toLinearExchangeMarket_utility [Fintype I] (M : LinearFisherMarket I G) :
    M.toLinearExchangeMarket.utility = M.utility := by rfl

/-- Buyer `i`'s additive linear utility `∑ g, utility i g * x i g` under allocation `x`. -/
def buyerUtility [Fintype G] (M : LinearFisherMarket I G) (x : I → G → ℝ) (i : I) : ℝ :=
  linearUtility (M.utility i) (x i)

theorem buyerUtility_eq [Fintype G] (M : LinearFisherMarket I G) (x : I → G → ℝ) (i : I) :
    M.buyerUtility x i = linearUtility (M.utility i) (x i) := by rfl

/-- Buyer `i`'s **bang-per-buck** (marginal utility per unit money) `utility i g / p g` on good `g`
at price vector `p` ([Vazirani2007], Section 5.2, p. 106). -/
noncomputable def bangPerBuck (M : LinearFisherMarket I G)
    (p : G → ℝ) (i : I) (g : G) : ℝ :=
  M.utility i g / p g

theorem bangPerBuck_eq (M : LinearFisherMarket I G) (p : G → ℝ) (i : I) (g : G) :
    M.bangPerBuck p i g = M.utility i g / p g := by rfl

/-- Market equilibrium `(x, p)` of linear Fisher market `M`. -/
@[expose] def IsEquilibrium [Fintype I] [Fintype G] (M : LinearFisherMarket I G)
    (x : I → G → ℝ) (p : G → ℝ) : Prop :=
  M.toFisherMarket.IsEquilibrium x p

/-- Pareto optimality of allocation `x` in linear Fisher market `M`. -/
@[expose] def IsParetoOptimal [Fintype I] [Fintype G] (M : LinearFisherMarket I G)
    (x : I → G → ℝ) : Prop :=
  M.toFisherMarket.IsParetoOptimal x

/-- Standard non-degeneracy conditions for Fisher's linear market model ([Vazirani2007],
Section 5.2, Theorem 5.1, pp. 105–107): positive buyer budgets, positive good supplies, every buyer
desires at least one good, and every good has at least one interested buyer. Note that
[Vazirani2007], Section 5.2 writes "if each good has a potential buyer" (`good_desired`) explicitly
while leaving `budget_pos`, `supply_pos`, and `buyer_nonsatiated` implicit. -/
structure IsNonDegenerate (M : LinearFisherMarket I G) : Prop where
  /-- Every buyer has a strictly positive budget. -/
  budget_pos : ∀ i : I, 0 < M.budget i
  /-- Every good has strictly positive supply. -/
  supply_pos : ∀ g : G, 0 < M.supply g
  /-- Every buyer has strictly positive marginal utility for at least one good. -/
  buyer_nonsatiated : ∀ i : I, ∃ g : G, 0 < M.utility i g
  /-- Every good has strictly positive marginal utility for at least one buyer. -/
  good_desired : ∀ g : G, ∃ i : I, 0 < M.utility i g

/-- The **Eisenberg–Gale objective** `∑ i, budget i * log (buyerUtility x i)` ([EisenbergGale1959];
[Vazirani2007], Section 5.2, Program `(5.1)`, p. 105). -/
noncomputable def eisenbergGaleObjective [Fintype I] [Fintype G]
    (M : LinearFisherMarket I G) (x : I → G → ℝ) : ℝ :=
  ∑ i : I, M.budget i * Real.log (M.buyerUtility x i)

theorem eisenbergGaleObjective_eq [Fintype I] [Fintype G]
    (M : LinearFisherMarket I G) (x : I → G → ℝ) :
    M.eisenbergGaleObjective x = ∑ i : I, M.budget i * Real.log (M.buyerUtility x i) := by rfl

/-- A feasible allocation giving every buyer strictly positive utility, forming the effective domain
of the logarithmic Eisenberg–Gale objective `(5.1)`. -/
@[expose] def IsPositiveUtilityAllocation [Fintype I] [Fintype G] (M : LinearFisherMarket I G)
    (x : I → G → ℝ) : Prop :=
  M.toFisherMarket.IsFeasibleAllocation x ∧ ∀ i : I, 0 < M.buyerUtility x i

/-- **Karush–Kuhn–Tucker optimality conditions** for the Eisenberg–Gale convex program `(5.1)`
([Vazirani2007], Section 5.2, p. 106, conditions `(i)`–`(iv)`) with primal allocation `x` and dual
supply multipliers (prices) `p`. -/
structure IsEisenbergGaleKKT [Fintype I] [Fintype G] (M : LinearFisherMarket I G)
    (x : I → G → ℝ) (p : G → ℝ) : Prop where
  /-- Dual prices are nonnegative. -/
  price_nonneg : ∀ g : G, 0 ≤ p g
  /-- Primal allocation is feasible and gives every buyer strictly positive utility. -/
  pos_alloc : M.IsPositiveUtilityAllocation x
  /-- Dual stationarity: `budget i * utility i g / buyerUtility x i ≤ p g`. -/
  stationarity : ∀ (i : I) (g : G), M.budget i * M.utility i g / M.buyerUtility x i ≤ p g
  /-- Primal complementary slackness: positive purchases achieve `budget i * utility i g /
  buyerUtility x i = p g`. -/
  primal_slackness : ∀ (i : I) (g : G), 0 < x i g →
    M.budget i * M.utility i g / M.buyerUtility x i = p g
  /-- Dual complementary slackness: positively priced goods clear completely. -/
  dual_slackness : ∀ g : G, p g * (M.supply g - ∑ i : I, x i g) = 0

/-- Explicit **Eisenberg–Gale dual price** of good `g` induced by a positive-utility allocation `x`:
`max_i (budget i * utility i g / buyerUtility x i)` (`0` when `I` is empty). -/
noncomputable def eisenbergGaleDualPrice [Fintype I] [Fintype G]
    (M : LinearFisherMarket I G) (x : I → G → ℝ) (g : G) : ℝ :=
  if hI : (Finset.univ : Finset I).Nonempty then
    Finset.univ.sup' hI fun i => M.budget i * M.utility i g / M.buyerUtility x i
  else 0

theorem eisenbergGaleDualPrice_of_nonempty [Fintype I] [Fintype G] [Nonempty I]
    (M : LinearFisherMarket I G) (x : I → G → ℝ) (g : G) :
    M.eisenbergGaleDualPrice x g =
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : I => M.budget i * M.utility i g / M.buyerUtility x i) := by
  simp [eisenbergGaleDualPrice]

end Definitions

/-! ### Logarithm helper inequalities -/

private theorem directional_log_increase {m₁ m₂ U₁ U₂ u₁ u₂ c : ℝ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hc : 0 < c)
    (hslope : m₁ * u₁ / U₁ < m₂ * u₂ / U₂) :
    ∃ ε : ℝ, 0 < ε ∧ ε < c ∧ 0 < U₁ - u₁ * ε ∧ 0 < U₂ + u₂ * ε ∧
      m₁ * Real.log U₁ + m₂ * Real.log U₂ <
        m₁ * Real.log (U₁ - u₁ * ε) + m₂ * Real.log (U₂ + u₂ * ε) := by
  set a : ℝ := u₁ / U₁
  set b : ℝ := u₂ / U₂
  have ha : 0 ≤ a := div_nonneg hu₁ hU₁.le
  have hb_nn : 0 ≤ b := div_nonneg hu₂ hU₂.le
  have hΔ : 0 < m₂ * b - m₁ * a :=
    sub_pos.2 (by simpa only [a, b, mul_div_assoc] using hslope)
  set D₁ : ℝ := 2 * (a + 1)
  set D₂ : ℝ := 2 * ((m₁ + m₂) * a * b + 1)
  have hD₁ : 0 < D₁ := by positivity
  have hD₂ : 0 < D₂ := by positivity
  set ε : ℝ := min (c / 2) (min (1 / D₁) ((m₂ * b - m₁ * a) / D₂))
  have hε_pos : 0 < ε := lt_min (half_pos hc) (lt_min (div_pos one_pos hD₁) (div_pos hΔ hD₂))
  have hε_lt_c : ε < c := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hc)
  have hε_D₁ : ε ≤ 1 / D₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hε_D₂ : ε ≤ (m₂ * b - m₁ * a) / D₂ := (min_le_right _ _).trans (min_le_right _ _)
  have haε_lt : a * ε < 1 := by
    have hle : ε * D₁ ≤ 1 := (le_div_iff₀ hD₁).1 hε_D₁
    nlinarith
  have hx₁ : 0 < 1 - a * ε := sub_pos.2 haε_lt
  have hx₂ : 0 < 1 + b * ε := by nlinarith
  have hu₁_eq : u₁ = a * U₁ := (div_mul_cancel₀ u₁ hU₁.ne').symm
  have hu₂_eq : u₂ = b * U₂ := (div_mul_cancel₀ u₂ hU₂.ne').symm
  have hU₁_sub : U₁ - u₁ * ε = U₁ * (1 - a * ε) := by rw [hu₁_eq]; ring
  have hU₂_add : U₂ + u₂ * ε = U₂ * (1 + b * ε) := by rw [hu₂_eq]; ring
  have hU₁' : 0 < U₁ - u₁ * ε := by rw [hU₁_sub]; exact mul_pos hU₁ hx₁
  have hU₂' : 0 < U₂ + u₂ * ε := by rw [hU₂_add]; exact mul_pos hU₂ hx₂
  refine ⟨ε, hε_pos, hε_lt_c, hU₁', hU₂', ?_⟩
  have hlog₁ : -(a * ε) / (1 - a * ε) ≤ Real.log (1 - a * ε) := by
    have h1 : -(a * ε) / (1 - a * ε) = 1 - (1 - a * ε)⁻¹ := by
      field_simp [hx₁.ne']
      ring
    exact h1.trans_le (Real.one_sub_inv_le_log_of_pos hx₁)
  have hlog₂ : (b * ε) / (1 + b * ε) ≤ Real.log (1 + b * ε) := by
    have h2 : (b * ε) / (1 + b * ε) = 1 - (1 + b * ε)⁻¹ := by
      field_simp [hx₂.ne']
      ring
    exact h2.trans_le (Real.one_sub_inv_le_log_of_pos hx₂)
  have hcross : m₁ * a * (1 + b * ε) < m₂ * b * (1 - a * ε) := by
    have hle : ε * D₂ ≤ m₂ * b - m₁ * a := (le_div_iff₀ hD₂).1 hε_D₂
    have hab_nn : 0 ≤ (m₁ + m₂) * a * b := by positivity
    nlinarith
  have hfrac : m₁ * ((a * ε) / (1 - a * ε)) < m₂ * ((b * ε) / (1 + b * ε)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, div_lt_div_iff₀ hx₁ hx₂]
    linarith [mul_lt_mul_of_pos_right hcross hε_pos]
  have hsum_pos : 0 < m₁ * Real.log (1 - a * ε) + m₂ * Real.log (1 + b * ε) := by
    have hm₁_le := mul_le_mul_of_nonneg_left hlog₁ hm₁.le
    have hm₂_le := mul_le_mul_of_nonneg_left hlog₂ hm₂.le
    rw [neg_div, mul_neg] at hm₁_le
    linarith
  rw [hU₁_sub, hU₂_add, Real.log_mul hU₁.ne' hx₁.ne', Real.log_mul hU₂.ne' hx₂.ne']
  linarith

/-! ### KKT, bang-per-buck, and equilibrium equivalence -/

section Equivalence

variable {I G : Type*} [Fintype I] [Fintype G]

/-- Every linear Fisher market equilibrium in which each buyer desires at least one good is Pareto
optimal. -/
theorem IsEquilibrium.isParetoOptimal {M : LinearFisherMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (heq : M.IsEquilibrium x p) (hns : ∀ i, ∃ g, 0 < M.utility i g) :
    M.IsParetoOptimal x :=
  FisherMarket.IsEquilibrium.isParetoOptimal heq
    (fun i => (isLocallyNonsatiated_linearUtility_iff (M.utility i)).2 (hns i))

/-- In any equilibrium of a linear Fisher market where every good is desired by some buyer, every
good has a strictly positive price. -/
theorem IsEquilibrium.price_pos {M : LinearFisherMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (heq : M.IsEquilibrium x p) (hgood : ∀ g, ∃ i, 0 < M.utility i g) (g : G) :
    0 < p g := by
  obtain ⟨i, hi⟩ := hgood g
  have hmem := M.toFisherMarket.mem_demandSet.1 (heq.2.1 i)
  rw [toFisherMarket_utility, toFisherMarket_budget] at hmem
  exact price_pos_of_mem_demandSet_linearUtility heq.1 hmem hi

/-- **Bang-per-buck characterization of linear Fisher equilibrium** ([Vazirani2007], Section 5.2,
pp. 105–106): when every buyer desires some good and every good is desired by some buyer, `(x, p)`
is a market equilibrium if and only if prices are strictly positive, bundles are nonnegative, every
good's supply is completely sold, every buyer spends their entire budget, and buyers purchase only
goods maximizing `bangPerBuck p i g = utility i g / p g`. -/
theorem isEquilibrium_iff_bangPerBuck {M : LinearFisherMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g) (hgood : ∀ g, ∃ i, 0 < M.utility i g) :
    M.IsEquilibrium x p ↔
      (∀ g, 0 < p g) ∧
      (∀ i g, 0 ≤ x i g) ∧
      (∀ g, ∑ i : I, x i g = M.supply g) ∧
      (∀ i, expenditure p (x i) = M.budget i) ∧
      ∀ i g, 0 < x i g → ∀ g', M.bangPerBuck p i g' ≤ M.bangPerBuck p i g := by
  constructor
  · intro heq
    have hp_pos : ∀ g, 0 < p g := heq.price_pos hgood
    have hclear : ∀ g, ∑ i : I, x i g = M.supply g :=
      fun g => heq.sum_eq_supply_of_price_pos (hp_pos g)
    have hdem : ∀ i, (∀ g, 0 ≤ x i g) ∧ expenditure p (x i) = M.budget i ∧
        ∀ g, 0 < x i g → ∀ g', M.utility i g' / p g' ≤ M.utility i g / p g := fun i => by
      have hmem := M.toFisherMarket.mem_demandSet.1 (heq.2.1 i)
      rw [toFisherMarket_utility, toFisherMarket_budget] at hmem
      exact (mem_demandSet_linearUtility_iff (M.utility_nonneg i) (M.budget_nonneg i) hp_pos
        (hbuyer i)).1 hmem
    exact ⟨hp_pos, fun i g => (hdem i).1 g, hclear, fun i => (hdem i).2.1,
      fun i g hxg g' => (hdem i).2.2 g hxg g'⟩
  · rintro ⟨hp_pos, hx_nn, hclear, hexp, hmax⟩
    refine ⟨fun g => (hp_pos g).le, fun i => ?_, fun g => ?_, fun g => ?_⟩
    · rw [FisherMarket.mem_demandSet, toFisherMarket_utility, toFisherMarket_budget]
      exact (mem_demandSet_linearUtility_iff (M.utility_nonneg i) (M.budget_nonneg i) hp_pos
        (hbuyer i)).2 ⟨hx_nn i, hexp i, hmax i⟩
    · simp only [toFisherMarket_supply, hclear g, le_rfl]
    · simp only [toFisherMarket_supply, hclear g, sub_self, mul_zero]

/-- In any Eisenberg–Gale KKT solution `(x, p)`, each buyer `i` spends exactly `M.budget i` and
the aggregate market value of supplies equals total buyer budgets. -/
theorem IsEisenbergGaleKKT.expenditure_eq_budget {M : LinearFisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (hkkt : M.IsEisenbergGaleKKT x p) (i : I) :
    expenditure p (x i) = M.budget i := by
  have hUi : 0 < M.buyerUtility x i := hkkt.pos_alloc.2 i
  have hterm : ∀ g : G, (p g * x i g) * M.buyerUtility x i =
      M.budget i * (M.utility i g * x i g) := by
    intro g
    rcases (hkkt.pos_alloc.1.1 i g).eq_or_lt with hxg0 | hxg
    · rw [← hxg0]
      simp
    · have hp_eq := (hkkt.primal_slackness i g hxg).symm
      rw [hp_eq]
      field_simp [hUi.ne']
  have hsum : expenditure p (x i) * M.buyerUtility x i = M.budget i * M.buyerUtility x i := by
    calc
      expenditure p (x i) * M.buyerUtility x i
        = ∑ g : G, (p g * x i g) * M.buyerUtility x i := by
            rw [expenditure_eq_sum, Finset.sum_mul]
      _ = ∑ g : G, M.budget i * (M.utility i g * x i g) :=
          Finset.sum_congr rfl fun g _ => hterm g
      _ = M.budget i * M.buyerUtility x i := by
            rw [← Finset.mul_sum, buyerUtility_eq, linearUtility_eq_sum]
  exact mul_right_cancel₀ hUi.ne' hsum

theorem IsEisenbergGaleKKT.expenditure_supply_eq_totalBudget {M : LinearFisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (hkkt : M.IsEisenbergGaleKKT x p) :
    expenditure p M.supply = M.toFisherMarket.totalBudget := by
  calc
    expenditure p M.supply
      = ∑ g : G, p g * ∑ i : I, x i g := by
          rw [expenditure_eq_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          linarith [hkkt.dual_slackness g]
    _ = ∑ i : I, expenditure p (x i) := by
          simp only [expenditure_eq_sum, Finset.mul_sum]
          exact Finset.sum_comm
    _ = M.toFisherMarket.totalBudget := by
          rw [FisherMarket.totalBudget_eq_sum]
          exact Finset.sum_congr rfl fun i _ => hkkt.expenditure_eq_budget i

/-- **KKT sufficiency for market equilibrium** ([Vazirani2007], Section 5.2, p. 106): when every
buyer has a positive budget, any pair `(x, p)` satisfying the Eisenberg–Gale KKT conditions is a
linear Fisher market equilibrium. -/
theorem IsEisenbergGaleKKT.isEquilibrium {M : LinearFisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (hkkt : M.IsEisenbergGaleKKT x p)
    (hbudget : ∀ i, 0 < M.budget i) : M.IsEquilibrium x p := by
  refine ⟨hkkt.price_nonneg, fun i => ?_, hkkt.pos_alloc.1.2, hkkt.dual_slackness⟩
  have hUi : 0 < M.buyerUtility x i := hkkt.pos_alloc.2 i
  have hmi : 0 < M.budget i := hbudget i
  rw [FisherMarket.mem_demandSet, Market.mem_demandSet, toFisherMarket_utility,
    toFisherMarket_budget]
  refine ⟨⟨hkkt.pos_alloc.1.1 i, (hkkt.expenditure_eq_budget i).le⟩, fun b' hb' => ?_⟩
  have hstat : ∀ g : G, M.budget i * M.utility i g ≤ p g * M.buyerUtility x i := fun g =>
    (div_le_iff₀ hUi).1 (hkkt.stationarity i g)
  have hmul : M.budget i * linearUtility (M.utility i) b' ≤
      M.budget i * M.buyerUtility x i := by
    calc
      M.budget i * linearUtility (M.utility i) b'
        = ∑ g : G, (M.budget i * M.utility i g) * b' g := by
            simp only [linearUtility_eq_sum, mul_assoc, Finset.mul_sum]
      _ ≤ ∑ g : G, (p g * M.buyerUtility x i) * b' g :=
            Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_right (hstat g) (hb'.1 g)
      _ = expenditure p b' * M.buyerUtility x i := by
            simp only [expenditure_eq_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun g _ => by ring
      _ ≤ M.budget i * M.buyerUtility x i :=
            mul_le_mul_of_nonneg_right hb'.2 hUi.le
  exact le_of_mul_le_mul_left hmul hmi

/-- **KKT necessity for market equilibrium** ([Vazirani2007], Section 5.2, p. 106): when budgets are
positive, every buyer desires some good, and every good is desired by some buyer, every linear
Fisher market equilibrium `(x, p)` satisfies the Eisenberg–Gale KKT conditions. -/
theorem IsEquilibrium.isEisenbergGaleKKT {M : LinearFisherMarket I G}
    {x : I → G → ℝ} {p : G → ℝ} (heq : M.IsEquilibrium x p)
    (hbudget : ∀ i, 0 < M.budget i)
    (hbuyer : ∀ i, ∃ g, 0 < M.utility i g)
    (hgood : ∀ g, ∃ i, 0 < M.utility i g) :
    M.IsEisenbergGaleKKT x p := by
  have hbpb := (isEquilibrium_iff_bangPerBuck hbuyer hgood).1 heq
  rcases hbpb with ⟨hp_pos, hx_nn, hclear, hexp, hmax⟩
  have hex_buy : ∀ i : I, ∃ g₀ : G, 0 < x i g₀ := fun i => by
    have h : ∑ g : G, (0 : ℝ) < ∑ g : G, p g * x i g := by
      rw [Finset.sum_const_zero, ← expenditure_eq_sum, hexp i]; exact hbudget i
    obtain ⟨g, -, hg⟩ := Finset.exists_lt_of_sum_lt h
    exact ⟨g, pos_of_mul_pos_right hg (hp_pos g).le⟩
  have hUi_eq : ∀ (i : I) {g₀ : G}, 0 < x i g₀ →
      M.buyerUtility x i = (M.utility i g₀ / p g₀) * M.budget i := by
    intro i g₀ hg₀
    have hterm : ∀ g : G, M.utility i g * x i g = (M.utility i g₀ / p g₀) * (p g * x i g) := by
      intro g
      rcases (hx_nn i g).eq_or_lt with hxg0 | hxg
      · simp [← hxg0]
      · rw [← show M.utility i g / p g = M.utility i g₀ / p g₀ from
          le_antisymm (hmax i g₀ hg₀ g) (hmax i g hxg g₀)]
        field_simp [(hp_pos g).ne']
    rw [buyerUtility_eq, linearUtility_eq_sum, Finset.sum_congr rfl fun g _ => hterm g,
      ← Finset.mul_sum, ← expenditure_eq_sum, hexp i]
  have hUi_pos : ∀ i : I, 0 < M.buyerUtility x i := fun i => by
    obtain ⟨g₀, hg₀⟩ := hex_buy i
    obtain ⟨g₁, hg₁⟩ := hbuyer i
    rw [hUi_eq i hg₀]
    exact mul_pos ((div_pos hg₁ (hp_pos g₁)).trans_le (hmax i g₀ hg₀ g₁)) (hbudget i)
  refine ⟨fun g => (hp_pos g).le, ⟨heq.isFeasibleAllocation, hUi_pos⟩, ?_, ?_, heq.2.2.2⟩
  · intro i g
    obtain ⟨g₀, hg₀⟩ := hex_buy i
    have hratio : M.utility i g / p g ≤ M.utility i g₀ / p g₀ := hmax i g₀ hg₀ g
    rw [div_le_iff₀ (hUi_pos i), hUi_eq i hg₀]
    linarith [mul_le_mul_of_nonneg_right ((div_le_iff₀ (hp_pos g)).1 hratio) (hbudget i).le]
  · intro i g hxg
    rw [div_eq_iff (hUi_pos i).ne', hUi_eq i hxg]
    field_simp [(hp_pos g).ne']

/-- **Eisenberg–Gale KKT equivalence** ([Vazirani2007], Section 5.2, p. 106,
conditions `(i)`–`(iv)`): under `M.IsNonDegenerate` (in fact without needing `supply_pos`),
`(x, p)` is a linear Fisher market equilibrium if and only if `(x, p)` satisfies
`M.IsEisenbergGaleKKT x p`. -/
theorem isEquilibrium_iff_isEisenbergGaleKKT {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (x : I → G → ℝ) (p : G → ℝ) :
    M.IsEquilibrium x p ↔ M.IsEisenbergGaleKKT x p :=
  ⟨fun heq => heq.isEisenbergGaleKKT hnd.budget_pos hnd.buyer_nonsatiated hnd.good_desired,
    fun hkkt => hkkt.isEquilibrium hnd.budget_pos⟩

/-! ### Global optimality, uniqueness, convexity, and existence -/

private theorem eisenbergGaleObjective_sub (M : LinearFisherMarket I G) (x y : I → G → ℝ) :
    M.eisenbergGaleObjective y - M.eisenbergGaleObjective x =
      ∑ i : I, M.budget i * (Real.log (M.buyerUtility y i) - Real.log (M.buyerUtility x i)) := by
  simp only [eisenbergGaleObjective, ← Finset.sum_sub_distrib, ← mul_sub]

private theorem IsEisenbergGaleKKT.sum_budget_mul_div_sub_one_le_zero
    {M : LinearFisherMarket I G} {x y : I → G → ℝ} {p : G → ℝ}
    (hkkt : M.IsEisenbergGaleKKT x p) (hy : M.toFisherMarket.IsFeasibleAllocation y) :
    ∑ i : I, M.budget i * (M.buyerUtility y i / M.buyerUtility x i - 1) ≤ 0 := by
  have hexpand : ∀ i : I, M.budget i * (M.buyerUtility y i / M.buyerUtility x i) =
      ∑ g : G, (M.budget i * M.utility i g / M.buyerUtility x i) * y i g := by
    intro i
    simp only [buyerUtility_eq, linearUtility_eq_sum, div_eq_mul_inv, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  calc
    ∑ i : I, M.budget i * (M.buyerUtility y i / M.buyerUtility x i - 1)
      = (∑ i : I, ∑ g : G, (M.budget i * M.utility i g / M.buyerUtility x i) * y i g) -
          M.toFisherMarket.totalBudget := by
            simp only [FisherMarket.totalBudget_eq_sum, toFisherMarket_budget, mul_sub, mul_one,
              Finset.sum_sub_distrib]
            congr 1
            exact Finset.sum_congr rfl fun i _ => hexpand i
    _ ≤ (∑ i : I, ∑ g : G, p g * y i g) - M.toFisherMarket.totalBudget := by
          refine sub_le_sub_right (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun g _ => ?_) _
          exact mul_le_mul_of_nonneg_right (hkkt.stationarity i g) (hy.1 i g)
    _ = (∑ g : G, p g * ∑ i : I, y i g) - M.toFisherMarket.totalBudget := by
          congr 1
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
    _ ≤ expenditure p M.supply - M.toFisherMarket.totalBudget := by
          rw [expenditure_eq_sum]
          refine sub_le_sub_right (Finset.sum_le_sum fun g _ => ?_) _
          exact mul_le_mul_of_nonneg_left (by simpa only [toFisherMarket_supply] using hy.2 g)
            (hkkt.price_nonneg g)
    _ = 0 := by rw [hkkt.expenditure_supply_eq_totalBudget, sub_self]

private theorem IsEisenbergGaleKKT.budget_mul_log_sub_le
    {M : LinearFisherMarket I G} {x y : I → G → ℝ} {p : G → ℝ}
    (hkkt : M.IsEisenbergGaleKKT x p) (hy : M.IsPositiveUtilityAllocation y) (i : I) :
    M.budget i * (Real.log (M.buyerUtility y i) - Real.log (M.buyerUtility x i)) ≤
      M.budget i * (M.buyerUtility y i / M.buyerUtility x i - 1) := by
  have hr : 0 < M.buyerUtility y i / M.buyerUtility x i :=
    div_pos (hy.2 i) (hkkt.pos_alloc.2 i)
  rw [← Real.log_div (hy.2 i).ne' (hkkt.pos_alloc.2 i).ne']
  exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr) (M.budget_nonneg i)

/-- **Global optimality of KKT allocations** ([EisenbergGale1959]; [Vazirani2007], Section 5.2,
Program `(5.1)`, p. 105): any allocation `x` admitting an Eisenberg–Gale KKT multiplier `p`
globally maximizes `M.eisenbergGaleObjective` over all positive-utility feasible allocations `y`. -/
theorem IsEisenbergGaleKKT.eisenbergGaleObjective_le {M : LinearFisherMarket I G}
    {x y : I → G → ℝ} {p : G → ℝ}
    (hkkt : M.IsEisenbergGaleKKT x p) (hy : M.IsPositiveUtilityAllocation y) :
    M.eisenbergGaleObjective y ≤ M.eisenbergGaleObjective x := by
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hkkt.budget_mul_log_sub_le hy i
  linarith [eisenbergGaleObjective_sub M x y, hkkt.sum_budget_mul_div_sub_one_le_zero hy.1]

/-- Any positive-utility feasible allocation `y` attaining at least the Eisenberg–Gale objective
value of a KKT allocation `x` (when budgets are positive) induces the **exact same buyer utilities**
`M.buyerUtility y = M.buyerUtility x`. -/
theorem IsEisenbergGaleKKT.buyerUtility_eq_of_eisenbergGaleObjective_eq
    {M : LinearFisherMarket I G} {x y : I → G → ℝ} {p : G → ℝ}
    (hkkt : M.IsEisenbergGaleKKT x p) (hbudget : ∀ i, 0 < M.budget i)
    (hy : M.IsPositiveUtilityAllocation y)
    (hobj : M.eisenbergGaleObjective x ≤ M.eisenbergGaleObjective y) :
    M.buyerUtility y = M.buyerUtility x := by
  ext i₀
  by_contra hne
  have hx₀ := hkkt.pos_alloc.2 i₀
  have hlt := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => hkkt.budget_mul_log_sub_le hy i) ⟨i₀, Finset.mem_univ _, by
      rw [← Real.log_div (hy.2 i₀).ne' hx₀.ne']
      exact mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos (div_pos (hy.2 i₀) hx₀)
        fun h => hne ((div_eq_one_iff_eq hx₀.ne').1 h)) (hbudget i₀)⟩
  linarith [eisenbergGaleObjective_sub M x y, hkkt.sum_budget_mul_div_sub_one_le_zero hy.1]

/-- **Uniqueness of equilibrium buyer utilities** ([Vazirani2007], Theorem 5.1, p. 107): in a
non-degenerate linear Fisher market, any two market equilibria yield identical buyer utility
profiles (`M.buyerUtility x = M.buyerUtility y`). -/
theorem buyerUtility_eq_of_isEquilibrium {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) {x y : I → G → ℝ} {p q : G → ℝ}
    (hx : M.IsEquilibrium x p) (hy : M.IsEquilibrium y q) :
    M.buyerUtility x = M.buyerUtility y := by
  have hkkt_x := (isEquilibrium_iff_isEisenbergGaleKKT hnd x p).1 hx
  have hkkt_y := (isEquilibrium_iff_isEisenbergGaleKKT hnd y q).1 hy
  exact (hkkt_x.buyerUtility_eq_of_eisenbergGaleObjective_eq hnd.budget_pos hkkt_y.pos_alloc
    (hkkt_y.eisenbergGaleObjective_le hkkt_x.pos_alloc)).symm

/-- **Uniqueness of equilibrium prices** ([Vazirani2007], Theorem 5.1, p. 107): in a non-degenerate
linear Fisher market, equilibrium prices are uniquely determined (`p = q`). -/
theorem price_eq_of_isEquilibrium {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) {x y : I → G → ℝ} {p q : G → ℝ}
    (hx : M.IsEquilibrium x p) (hy : M.IsEquilibrium y q) :
    p = q := by
  have hle : ∀ {x₁ x₂ : I → G → ℝ} {p₁ p₂ : G → ℝ},
      M.IsEquilibrium x₁ p₁ → M.IsEquilibrium x₂ p₂ → ∀ g : G, p₁ g ≤ p₂ g := by
    intro x₁ x₂ p₁ p₂ hx₁ hx₂ g
    have hkkt₁ := (isEquilibrium_iff_isEisenbergGaleKKT hnd x₁ p₁).1 hx₁
    have hkkt₂ := (isEquilibrium_iff_isEisenbergGaleKKT hnd x₂ p₂).1 hx₂
    have hU_eq : M.buyerUtility x₁ = M.buyerUtility x₂ :=
      buyerUtility_eq_of_isEquilibrium hnd hx₁ hx₂
    have hp₁_pos : 0 < p₁ g := hx₁.price_pos hnd.good_desired g
    have hsum_eq : ∑ i : I, x₁ i g = M.supply g := hx₁.sum_eq_supply_of_price_pos hp₁_pos
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
      (g := fun i => x₁ i g) (by simpa [hsum_eq] using hnd.supply_pos g)
    calc
      p₁ g = M.budget i * M.utility i g / M.buyerUtility x₁ i :=
        (hkkt₁.primal_slackness i g hi).symm
      _ = M.budget i * M.utility i g / M.buyerUtility x₂ i := by
        rw [congrFun hU_eq i]
      _ ≤ p₂ g := hkkt₂.stationarity i g
  ext g
  exact le_antisymm (hle hx hy g) (hle hy hx g)

/-- **Convexity of equilibrium allocations** ([Vazirani2007], Theorem 5.1, p. 107): in a
non-degenerate linear Fisher market, the set of equilibrium allocations `{x | ∃ p, M.IsEquilibrium
x p}` is convex. -/
theorem convex_setOf_exists_isEquilibrium {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) :
    Convex ℝ {x : I → G → ℝ | ∃ p : G → ℝ, M.IsEquilibrium x p} := by
  rintro x ⟨p, hx⟩ y ⟨q, hy⟩ a b ha hb hab
  rw [price_eq_of_isEquilibrium hnd hy hx] at hy
  have hkkt_x := (isEquilibrium_iff_isEisenbergGaleKKT hnd x p).1 hx
  have hkkt_y := (isEquilibrium_iff_isEisenbergGaleKKT hnd y p).1 hy
  have hU_eq : M.buyerUtility y = M.buyerUtility x :=
    buyerUtility_eq_of_isEquilibrium hnd hy hx
  refine ⟨p, (isEquilibrium_iff_isEisenbergGaleKKT hnd (a • x + b • y) p).2 ?_⟩
  have hU_combo : ∀ i : I, M.buyerUtility (a • x + b • y) i = M.buyerUtility x i := by
    intro i
    have hlin : M.buyerUtility (a • x + b • y) i =
        a * M.buyerUtility x i + b * M.buyerUtility y i := by
      simp only [buyerUtility_eq, linearUtility_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hlin, congrFun hU_eq i, ← add_mul, hab, one_mul]
  have hsum_combo : ∀ g, ∑ i : I, (a • x + b • y) i g =
      a * (∑ i : I, x i g) + b * ∑ i : I, y i g := fun g => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfeas : M.toFisherMarket.IsFeasibleAllocation (a • x + b • y) := by
    refine ⟨fun i g => add_nonneg (mul_nonneg ha (hkkt_x.pos_alloc.1.1 i g))
      (mul_nonneg hb (hkkt_y.pos_alloc.1.1 i g)), fun g => ?_⟩
    calc
      ∑ i : I, (a • x + b • y) i g = a * (∑ i : I, x i g) + b * ∑ i : I, y i g := hsum_combo g
      _ ≤ a * M.supply g + b * M.supply g :=
            add_le_add (mul_le_mul_of_nonneg_left (hkkt_x.pos_alloc.1.2 g) ha)
              (mul_le_mul_of_nonneg_left (hkkt_y.pos_alloc.1.2 g) hb)
      _ = M.supply g := by rw [← add_mul, hab, one_mul]
  refine ⟨hkkt_x.price_nonneg, ⟨hfeas, fun i => by rw [hU_combo i]; exact hkkt_x.pos_alloc.2 i⟩,
    fun i g => by rw [hU_combo i]; exact hkkt_x.stationarity i g,
    fun i g hpos => ?_, fun g => ?_⟩
  · rw [hU_combo i]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpos
    by_cases hxg : 0 < x i g
    · exact hkkt_x.primal_slackness i g hxg
    · have hxg0 : x i g = 0 := le_antisymm (not_lt.1 hxg) (hkkt_x.pos_alloc.1.1 i g)
      rw [hxg0, mul_zero, zero_add] at hpos
      have hyg : 0 < y i g := pos_of_mul_pos_right hpos hb
      rw [← congrFun hU_eq i]
      exact hkkt_y.primal_slackness i g hyg
  · rw [hsum_combo]
    linear_combination a * hkkt_x.dual_slackness g + b * hkkt_y.dual_slackness g +
      p g * M.supply g * hab.symm

/-- **Primal optimality implies Eisenberg–Gale KKT** ([EisenbergGale1959]; [Vazirani2007],
Section 5.2, p. 106): in a non-degenerate linear Fisher market, any
maximizer `x` of `M.eisenbergGaleObjective` on `{y | M.IsPositiveUtilityAllocation y}` pairs with
the explicit price vector `M.eisenbergGaleDualPrice x` to satisfy `M.IsEisenbergGaleKKT`. -/
theorem isEisenbergGaleKKT_eisenbergGaleDualPrice_of_isMaxOn {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) {x : I → G → ℝ}
    (hx : M.IsPositiveUtilityAllocation x)
    (hmax : IsMaxOn M.eisenbergGaleObjective {y | M.IsPositiveUtilityAllocation y} x) :
    M.IsEisenbergGaleKKT x (M.eisenbergGaleDualPrice x) := by
  classical
  set p : G → ℝ := M.eisenbergGaleDualPrice x
  have hstat : ∀ (i : I) (g : G), M.budget i * M.utility i g / M.buyerUtility x i ≤ p g := by
    intro i g
    have hI : (Finset.univ : Finset I).Nonempty := ⟨i, Finset.mem_univ i⟩
    simpa only [p, eisenbergGaleDualPrice, hI, ↓reduceDIte] using
      Finset.le_sup' (fun k => M.budget k * M.utility k g / M.buyerUtility x k) (Finset.mem_univ i)
  have hp_nonneg : ∀ g : G, 0 ≤ p g := fun g => by
    by_cases hI : (Finset.univ : Finset I).Nonempty
    · obtain ⟨i, -⟩ := hI
      exact (div_nonneg (mul_nonneg (M.budget_nonneg i) (M.utility_nonneg i g))
        (hx.2 i).le).trans (hstat i g)
    · simp [p, eisenbergGaleDualPrice, hI]
  -- Giving each buyer `i` an extra amount `d i` of good `g` cannot raise the objective.
  have hperturb : ∀ (g : G) (d : I → ℝ), (∀ i, 0 ≤ x i g + d i) →
      ∑ i, x i g + ∑ i, d i ≤ M.supply g →
      (∀ i, 0 < M.buyerUtility x i + M.utility i g * d i) →
      ∑ i, M.budget i * (Real.log (M.buyerUtility x i + M.utility i g * d i) -
        Real.log (M.buyerUtility x i)) ≤ 0 := by
    intro g d hnn hsum hpos
    set y : I → G → ℝ := fun i g' => x i g' + if g' = g then d i else 0
    have hU : ∀ i, M.buyerUtility y i = M.buyerUtility x i + M.utility i g * d i := fun i => by
      simp [y, buyerUtility_eq, linearUtility_eq_sum, mul_add, Finset.sum_add_distrib]
    have hy : M.IsPositiveUtilityAllocation y := by
      refine ⟨⟨fun i g' => ?_, fun g' => ?_⟩, fun i => by rw [hU]; exact hpos i⟩
      · by_cases hg : g' = g
        · simpa [y, hg] using hnn i
        · simpa [y, hg] using hx.1.1 i g'
      · by_cases hg : g' = g
        · simpa [y, hg, Finset.sum_add_distrib] using hsum
        · simpa [y, hg] using hx.1.2 g'
    simp only [← hU]
    linarith [eisenbergGaleObjective_sub M x y, isMaxOn_iff.1 hmax y hy]
  refine ⟨hp_nonneg, hx, hstat, fun i₁ g hxi₁ => (hstat i₁ g).antisymm ?_, fun g => ?_⟩
  · by_contra hlt
    push Not at hlt
    have hI : (Finset.univ : Finset I).Nonempty := ⟨i₁, Finset.mem_univ i₁⟩
    obtain ⟨i₂, -, hi₂_eq⟩ :=
      Finset.exists_mem_eq_sup' hI (fun k => M.budget k * M.utility k g / M.buyerUtility x k)
    have hpg : p g = M.budget i₂ * M.utility i₂ g / M.buyerUtility x i₂ := by
      simpa only [p, eisenbergGaleDualPrice, hI, ↓reduceDIte] using hi₂_eq
    rw [hpg] at hlt
    have hne : i₁ ≠ i₂ := by
      rintro rfl
      exact lt_irrefl _ hlt
    obtain ⟨ε, hε_pos, hε_lt, hU₁', hU₂', hlog_inc⟩ :=
      directional_log_increase (hnd.budget_pos i₁) (hnd.budget_pos i₂) (hx.2 i₁) (hx.2 i₂)
        (M.utility_nonneg i₁ g) (M.utility_nonneg i₂ g) hxi₁ hlt
    set d : I → ℝ := fun i => if i = i₁ then -ε else if i = i₂ then ε else 0 with hd
    have hd0 : ∀ i, i ≠ i₁ ∧ i ≠ i₂ → d i = 0 := fun i hi => by simp [hd, hi.1, hi.2]
    have h := hperturb g d
      (fun i => by
        simp only [hd]
        split_ifs with h1
        · subst h1; linarith
        all_goals linarith [hx.1.1 i g])
      (by
        rw [Fintype.sum_eq_add (f := d) i₁ i₂ hne hd0]
        simpa [hd, hne.symm] using hx.1.2 g)
      (fun i => by
        simp only [hd]
        split_ifs with h1 h2
        · subst h1; linarith
        · subst h2; linarith
        · simpa using hx.2 i)
    rw [Fintype.sum_eq_add i₁ i₂ hne fun i hi => by simp [hd0 i hi]] at h
    simp only [hd, ↓reduceIte, hne.symm, mul_neg, ← sub_eq_add_neg] at h
    linarith
  · rcases (show ∑ i, x i g ≤ M.supply g by simpa using hx.1.2 g).eq_or_lt with hfull | hslack
    · rw [hfull, sub_self, mul_zero]
    exfalso
    obtain ⟨i₀, hi₀⟩ := hnd.good_desired g
    have hδ := sub_pos.2 hslack
    set d : I → ℝ := Pi.single i₀ (M.supply g - ∑ i, x i g)
    have hd : ∀ i, 0 ≤ d i := fun i => by by_cases h : i = i₀ <;> simp [d, h, hδ.le]
    have h := hperturb g d
      (fun i => add_nonneg (hx.1.1 i g) (hd i)) (by simp [d])
      (fun i => add_pos_of_pos_of_nonneg (hx.2 i) (mul_nonneg (M.utility_nonneg i g) (hd i)))
    rw [Fintype.sum_eq_single i₀ fun i hi => by simp [d, hi]] at h
    simp only [d, Pi.single_eq_same] at h
    exact h.not_gt (mul_pos (hnd.budget_pos i₀) (sub_pos.2
      (Real.log_lt_log (hx.2 i₀) (lt_add_of_pos_right _ (mul_pos hi₀ hδ)))))

/-- **Eisenberg–Gale primal optimality equivalence** ([EisenbergGale1959]; [Vazirani2007],
Section 5.2, Program `(5.1)`, pp. 105–107): in a non-degenerate linear Fisher market, an allocation
`x` participates in a market equilibrium `(x, p)` if and only if `x` is a positive-utility feasible
allocation maximizing `M.eisenbergGaleObjective` over `{y | M.IsPositiveUtilityAllocation y}`. -/
theorem isEquilibrium_iff_isMaxOn_eisenbergGaleObjective {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (x : I → G → ℝ) :
    (∃ p : G → ℝ, M.IsEquilibrium x p) ↔
      M.IsPositiveUtilityAllocation x ∧
        IsMaxOn M.eisenbergGaleObjective {y | M.IsPositiveUtilityAllocation y} x := by
  constructor
  · rintro ⟨p, heq⟩
    have hkkt := (isEquilibrium_iff_isEisenbergGaleKKT hnd x p).1 heq
    exact ⟨hkkt.pos_alloc, fun y hy => hkkt.eisenbergGaleObjective_le hy⟩
  · rintro ⟨hx, hmax⟩
    exact ⟨M.eisenbergGaleDualPrice x,
      (isEisenbergGaleKKT_eisenbergGaleDualPrice_of_isMaxOn hnd hx hmax).isEquilibrium
        hnd.budget_pos⟩

/-- **Existence of linear Fisher market equilibrium** ([EisenbergGale1959]; [Vazirani2007],
Theorem 5.1, p. 107): every non-degenerate linear Fisher market admits a market equilibrium
`(x, p)`. -/
theorem IsNonDegenerate.exists_isEquilibrium {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) :
    ∃ (x : I → G → ℝ) (p : G → ℝ), M.IsEquilibrium x p := by
  classical
  by_cases hI : Nonempty I
  · have hcard_pos : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
    let x₀ : I → G → ℝ := fun _ g => M.supply g / (Fintype.card I : ℝ)
    have hx₀_feas : M.toFisherMarket.IsFeasibleAllocation x₀ := by
      refine ⟨fun _ g => div_nonneg (M.supply_nonneg g) hcard_pos.le, fun g => ?_⟩
      simp only [toFisherMarket_supply, x₀, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_div_cancel₀ _ hcard_pos.ne']
      exact le_rfl
    have hx₀_U : ∀ i : I, 0 < M.buyerUtility x₀ i := fun i => by
      obtain ⟨g₀, hg₀⟩ := hnd.buyer_nonsatiated i
      rw [buyerUtility_eq, linearUtility_eq_sum]
      exact (mul_pos hg₀ (div_pos (hnd.supply_pos g₀) hcard_pos)).trans_le (Finset.single_le_sum
        (fun g _ => mul_nonneg (M.utility_nonneg i g) (hx₀_feas.1 i g)) (Finset.mem_univ g₀))
    have hx₀ : M.IsPositiveUtilityAllocation x₀ := ⟨hx₀_feas, hx₀_U⟩
    let Umax : I → ℝ := fun i => ∑ g : G, M.utility i g * M.supply g
    have hU_le_max : ∀ {y : I → G → ℝ}, M.toFisherMarket.IsFeasibleAllocation y →
        ∀ i : I, M.buyerUtility y i ≤ Umax i := by
      intro y hy i
      rw [buyerUtility_eq, linearUtility_eq_sum]
      refine Finset.sum_le_sum fun g _ => ?_
      have hy_le : y i g ≤ M.supply g :=
        (Finset.single_le_sum (fun k _ => hy.1 k g) (Finset.mem_univ i)).trans (hy.2 g)
      exact mul_le_mul_of_nonneg_left hy_le (M.utility_nonneg i g)
    have hUmax_pos : ∀ i : I, 0 < Umax i := fun i =>
      (hx₀_U i).trans_le (hU_le_max hx₀_feas i)
    let δ : I → ℝ := fun i =>
      min (M.buyerUtility x₀ i)
        (Real.exp ((M.eisenbergGaleObjective x₀ -
          ∑ k ∈ Finset.univ.erase i, M.budget k * Real.log (Umax k)) / M.budget i))
    have hδ_pos : ∀ i : I, 0 < δ i := fun i => lt_min (hx₀_U i) (Real.exp_pos _)
    let K : Set (I → G → ℝ) :=
      {y | (∀ i g, 0 ≤ y i g) ∧ (∀ g, ∑ i : I, y i g ≤ M.supply g) ∧
        ∀ i : I, δ i ≤ M.buyerUtility y i}
    have hx₀_mem : x₀ ∈ K := ⟨hx₀_feas.1, hx₀_feas.2, fun i => min_le_left _ _⟩
    let Box : Set (I → G → ℝ) :=
      Set.pi Set.univ fun _ => Set.pi Set.univ fun g => Set.Icc 0 (M.supply g)
    have hBox_compact : IsCompact Box :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    have hK_sub : K ⊆ Box := by
      intro y hy i _ g _
      exact ⟨hy.1 i g,
        (Finset.single_le_sum (fun k _ => hy.1 k g) (Finset.mem_univ i)).trans (hy.2.1 g)⟩
    have hK_closed : IsClosed K := by
      have hc₁ : IsClosed {y : I → G → ℝ | ∀ i g, 0 ≤ y i g} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun g =>
          isClosed_le continuous_const (by fun_prop)
      have hc₂ : IsClosed {y : I → G → ℝ | ∀ g, ∑ i : I, y i g ≤ M.supply g} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun g => isClosed_le (by fun_prop) continuous_const
      have hc₃ : IsClosed {y : I → G → ℝ | ∀ i : I, δ i ≤ M.buyerUtility y i} := by
        simp only [buyerUtility_eq, linearUtility_eq_sum, Set.ofPred_forall]
        exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
      exact hc₁.inter (hc₂.inter hc₃)
    have hK_compact : IsCompact K := hBox_compact.of_isClosed_subset hK_closed hK_sub
    have hf_cont : ContinuousOn M.eisenbergGaleObjective K := by
      have hterm : ∀ i : I, ContinuousOn
          (fun y : I → G → ℝ => M.budget i * Real.log (∑ g : G, M.utility i g * y i g)) K :=
        fun i => continuousOn_const.mul
          (ContinuousOn.log (by fun_prop) fun y hy => by
            have hpos := (hδ_pos i).trans_le (hy.2.2 i)
            rw [buyerUtility_eq, linearUtility_eq_sum] at hpos
            exact hpos.ne')
      have heq_obj : M.eisenbergGaleObjective = fun y : I → G → ℝ =>
          ∑ i : I, M.budget i * Real.log (∑ g : G, M.utility i g * y i g) := by
        ext y
        simp only [eisenbergGaleObjective_eq, buyerUtility_eq, linearUtility_eq_sum]
      rw [heq_obj]
      fun_prop
    obtain ⟨xStar, hxStar_K, hxStar_max⟩ :=
      hK_compact.exists_isMaxOn ⟨x₀, hx₀_mem⟩ hf_cont
    have hxStar_pos : M.IsPositiveUtilityAllocation xStar :=
      ⟨⟨hxStar_K.1, hxStar_K.2.1⟩, fun i => (hδ_pos i).trans_le (hxStar_K.2.2 i)⟩
    have hxStar_global : IsMaxOn M.eisenbergGaleObjective {y | M.IsPositiveUtilityAllocation y}
        xStar := by
      intro y hy
      by_cases hlow : M.eisenbergGaleObjective y < M.eisenbergGaleObjective x₀
      · exact hlow.le.trans (hxStar_max hx₀_mem)
      · push Not at hlow
        have hy_K : y ∈ K := by
          refine ⟨hy.1.1, hy.1.2, fun i => (min_le_right _ _).trans ?_⟩
          have hrest_le :
              ∑ k ∈ Finset.univ.erase i, M.budget k * Real.log (M.buyerUtility y k) ≤
                ∑ k ∈ Finset.univ.erase i, M.budget k * Real.log (Umax k) := by
            refine Finset.sum_le_sum fun k _ => ?_
            exact mul_le_mul_of_nonneg_left
              (Real.log_le_log (hy.2 k) (hU_le_max hy.1 k)) (M.budget_nonneg k)
          have hsplit := Finset.add_sum_erase Finset.univ
            (fun k => M.budget k * Real.log (M.buyerUtility y k)) (Finset.mem_univ i)
          rw [← Real.exp_log (hy.2 i)]
          refine Real.exp_le_exp.2 ((div_le_iff₀ (hnd.budget_pos i)).2 ?_)
          linarith [eisenbergGaleObjective_eq M y]
        exact hxStar_max hy_K
    obtain ⟨pStar, hpStar⟩ :=
      (isEquilibrium_iff_isMaxOn_eisenbergGaleObjective hnd xStar).2 ⟨hxStar_pos, hxStar_global⟩
    exact ⟨xStar, pStar, hpStar⟩
  · have : IsEmpty I := not_nonempty_iff.1 hI
    have : IsEmpty G := ⟨fun g => by
      obtain ⟨i, _⟩ := hnd.good_desired g
      exact isEmptyElim i⟩
    refine ⟨isEmptyElim, isEmptyElim, fun g => isEmptyElim g, fun i => isEmptyElim i,
      fun g => isEmptyElim g, fun g => isEmptyElim g⟩

/-! ### Linear Fisher-to-Arrow–Debreu reduction ([CodenottiVaradarajan2007], Section 6.1.7) -/

private theorem IsNonDegenerate.totalBudget_pos [Nonempty I] {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) : 0 < M.toFisherMarket.totalBudget := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  rw [FisherMarket.totalBudget_eq_sum]
  exact (hnd.budget_pos i₀).trans_le
    (Finset.single_le_sum (fun i _ => M.budget_nonneg i) (Finset.mem_univ i₀))

private theorem toLinearExchangeMarket_toExchangeMarket_eq (M : LinearFisherMarket I G) :
    M.toLinearExchangeMarket.toExchangeMarket = M.toFisherMarket.toExchangeMarket := by
  ext i g
  · simp [FisherMarket.totalBudget_eq_sum]
  · simp

omit [Fintype I] in
private theorem IsNonDegenerate.buyer_locallyNonsatiated {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) (i : I) : IsLocallyNonsatiated (M.toFisherMarket.utility i) := by
  rw [toFisherMarket_utility]
  exact (isLocallyNonsatiated_linearUtility_iff (M.utility i)).2 (hnd.buyer_nonsatiated i)

/-- Under `M.IsNonDegenerate` with `[Nonempty I]`, `(x, p)` is a linear Fisher equilibrium of `M`
if and only if `expenditure p M.supply = M.toFisherMarket.totalBudget` and `(x, p)` is a
competitive equilibrium of `M.toLinearExchangeMarket` ([CodenottiVaradarajan2007], Section 6.1.7,
p. 140). -/
theorem isEquilibrium_iff_toLinearExchangeMarket [Nonempty I] {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) {x : I → G → ℝ} {p : G → ℝ} :
    M.IsEquilibrium x p ↔
      expenditure p M.supply = M.toFisherMarket.totalBudget ∧
        M.toLinearExchangeMarket.IsCompetitiveEquilibrium x p := by
  simpa only [IsEquilibrium, LinearExchangeMarket.IsCompetitiveEquilibrium, toFisherMarket_supply,
    toLinearExchangeMarket_toExchangeMarket_eq] using
    M.toFisherMarket.isEquilibrium_iff_toExchangeMarket hnd.totalBudget_pos
      hnd.buyer_locallyNonsatiated

/-- **Rescaling recovery** ([CodenottiVaradarajan2007], Section 6.1.7, p. 140): in a non-degenerate
linear Fisher market with `[Nonempty I]`, any competitive equilibrium `(x, p)` of
`M.toLinearExchangeMarket` rescales directly to a linear Fisher market equilibrium of `M`. -/
theorem isEquilibrium_smul_of_toLinearExchangeMarket [Nonempty I] {M : LinearFisherMarket I G}
    (hnd : M.IsNonDegenerate) {x : I → G → ℝ} {p : G → ℝ}
    (heq : M.toLinearExchangeMarket.IsCompetitiveEquilibrium x p) :
    M.IsEquilibrium x ((M.toFisherMarket.totalBudget / expenditure p M.supply) • p) := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨g₀, _⟩ := hnd.buyer_nonsatiated i₀
  have hp_pos : ∀ g : G, 0 < p g := fun g => by
    obtain ⟨i, hi⟩ := hnd.good_desired g
    have hmem := M.toLinearExchangeMarket.toExchangeMarket.mem_demandSet.1 (heq.2.1 i)
    simp only [LinearExchangeMarket.toExchangeMarket_utility,
      toLinearExchangeMarket_utility] at hmem
    exact price_pos_of_mem_demandSet_linearUtility heq.1 hmem hi
  have hval : 0 < expenditure p M.supply := by
    rw [expenditure_eq_sum]
    exact (mul_pos (hp_pos g₀) (hnd.supply_pos g₀)).trans_le
      (Finset.single_le_sum (fun g _ => mul_nonneg (hp_pos g).le (M.supply_nonneg g))
        (Finset.mem_univ g₀))
  have heq' : M.toFisherMarket.toExchangeMarket.IsCompetitiveEquilibrium x p := by
    rwa [← toLinearExchangeMarket_toExchangeMarket_eq]
  exact M.toFisherMarket.isEquilibrium_smul_of_toExchangeMarket hnd.totalBudget_pos
    hnd.buyer_locallyNonsatiated heq' hval

end Equivalence

end LinearFisherMarket

end Cslib.GameTheory.Market

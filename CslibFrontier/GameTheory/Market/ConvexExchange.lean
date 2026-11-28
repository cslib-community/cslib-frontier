/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.GrossSubstitutes
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Foundations.Analysis.ReverseHolder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

/-!
# Convex feasibility programs for linear and CES exchange economies, and non-convexity for `ρ < -1`

Building on `CslibFrontier.GameTheory.Market.Basic` and
`CslibFrontier.GameTheory.Market.GrossSubstitutes`, this module formalizes Sections 6.4 and 6.5.1
of [CodenottiVaradarajan2007] (pp. 149–151):

1. **Convex feasibility program for linear exchange economies (§6.4.1, p. 149; Nenakov–Primak 1983,
   Jain 2004):** for a `LinearExchangeMarket I G` with marginal utilities `a_{ij} ≥ 0` and
   endowments `w_{ij} ≥ 0`, the logarithmic-price feasibility constraints
   `∑_k a_{ik} x_{ik} ≥ a_{ij} ∑_k w_{ik} exp(ψ_k - ψ_j)`, `∑_i x_{ij} = ∑_i w_{ij}`, `x ≥ 0`
   (`LinearExchangeMarket.IsConvexProgramFeasible`) define a convex set in `(ψ, x)`
   (`LinearExchangeMarket.convex_setOf_isConvexProgramFeasible`) whose feasible pairs correspond
   bijectively to positive-price competitive equilibria `(x, exp ∘ ψ)` whenever every trader desires
   at least one good (`LinearExchangeMarket.isConvexProgramFeasible_iff_isCompetitiveEquilibrium`).
2. **CES utility properties, strict demand uniqueness `(6.7)`, and Proposition 6.11 (§6.4.2,
   pp. 149–150):**
   * positive degree-`1` homogeneity (`cesUtility_smul`), monotonicity (`cesUtility_mono`), and
     concavity (`concaveOn_cesUtility`) of `cesUtility α ρ` on `ℝ_+^G` for `ρ ≤ 1, ρ ≠ 0`;
   * strict uniqueness of closed-form CES Marshallian demand `(6.7)` (`demandSet_cesUtility_eq`)
     for all `ρ < 1, ρ ≠ 0`;
   * `CESExchangeMarket` and its exact positive-price competitive-equilibrium characterization via
     `IsWalrasianEquilibrium`
     (`CESExchangeMarket.isCompetitiveEquilibrium_iff_isWalrasianEquilibrium`);
   * **Proposition 6.11** (`convexOn_cesTransformedDemand`, Equations `(6.8)`–`(6.9)`, p. 150): for
     `-1 ≤ ρ_i < 0` and transformed prices `σ_j = √(π_j)` (`ρ = -1`), the transformed demand
     `f_{ij}(σ) = σ_j x_{ij}(σ^2)` is convex on `ℝ_{++}^G`, so the transformed equilibrium price set
     `{σ ∈ ℝ_{++}^G | ∀ g, ∑_i f_{ig}(σ) ≤ σ_g ∑_i w_{ig}}` is convex and preconnected
     (`CESExchangeMarket.convex_setOf_transformedEquilibrium`).
3. **Multiple disconnected equilibria for `ρ < -1` (§6.5.1, p. 151; Gjerstad 1996):**
   in the 2-trader, 2-good CES exchange economy `gjerstadMarket` with endowments `(1, 0), (0, 1)`
   and utilities `((ax)^ρ + y^ρ)^{1/ρ}`, `((x/a)^ρ + y^ρ)^{1/ρ}`, `(1/2, 1/2)` is always a
   Walrasian equilibrium price, and for every `ρ < -1` and every `a > 0` with
   `a^{-ρ/(1-ρ)} < (-ρ - 1)/(1 - ρ)` there exists a unique `p ∈ (0, 1/2)` such that `(p, 1 - p)`
   and `(1 - p, p)` are Walrasian equilibria while `(q, 1 - q)` is not an equilibrium for any
   `q ∈ (0, 1/2) \ {p}` (`gjerstadMarket_exists_disconnected_equilibria`).

## Main definitions

* `Cslib.GameTheory.Market.LinearExchangeMarket.IsConvexProgramFeasible`: the Nenakov–Primak–Jain
  convex feasibility constraints for linear Arrow–Debreu exchange markets
  ([CodenottiVaradarajan2007], Section 6.4.1, p. 149).
* `Cslib.GameTheory.Market.CESExchangeMarket`: Arrow–Debreu exchange economy with CES utilities,
  together with `toExchangeMarket`, `excessDemandFn`, and `transformedEquilibriumSet`.
* `Cslib.GameTheory.Market.cesTransformedDemand`: transformed CES demand
  `f_{ij}(σ) = σ_j x_{ij}(σ^2)` ([CodenottiVaradarajan2007], Section 6.4.2, pp. 149–150).
* `Cslib.GameTheory.Market.gjerstadMarket`: the 2-trader, 2-good CES exchange economy of
  [CodenottiVaradarajan2007], Section 6.5.1, p. 151.

## Main results

* `LinearExchangeMarket.isConvexProgramFeasible_iff_isCompetitiveEquilibrium`,
  `LinearExchangeMarket.exists_isConvexProgramFeasible_of_isCompetitiveEquilibrium`, and
  `LinearExchangeMarket.convex_setOf_isConvexProgramFeasible`: exact equilibrium equivalence and
  convexity of the linear-exchange feasibility program ([CodenottiVaradarajan2007], Section 6.4.1,
  p. 149).
* `Cslib.GameTheory.Market.cesUtility_smul`, `Cslib.GameTheory.Market.cesUtility_mono`,
  `Cslib.GameTheory.Market.concaveOn_cesUtility`: positive homogeneity, monotonicity, and concavity
  of CES utility functions.
* `Cslib.GameTheory.Market.demandSet_cesUtility_eq`: strict uniqueness of closed-form CES demand
  `(6.7)` ([CodenottiVaradarajan2007], Section 6.4.2, p. 149).
* `Cslib.GameTheory.Market.convexOn_cesTransformedDemand`: **Proposition 6.11**
  ([CodenottiVaradarajan2007], Section 6.4.2, p. 150).
* `Cslib.GameTheory.Market.CESExchangeMarket.isWalrasianEquilibrium_sq_iff`,
  `Cslib.GameTheory.Market.CESExchangeMarket.convex_setOf_transformedEquilibrium`: convex
  feasibility characterization of positive CES equilibria for `-1 ≤ ρ_i < 0`.
* `Cslib.GameTheory.Market.gjerstadMarket_isWalrasianEquilibrium_half`,
  `Cslib.GameTheory.Market.gjerstadMarket_exists_disconnected_equilibria`: multiple disconnected
  equilibria for every `ρ < -1` ([CodenottiVaradarajan2007], Section 6.5.1, p. 151).

## References

* [CodenottiVaradarajan2007], Sections 6.4.1, 6.4.2, 6.5.1, and 6.7, pp. 149–151, 156
-/

public section

namespace Cslib.GameTheory.Market

open Finset Set
open scoped BigOperators

/-! ### §6.4.1 Convex feasibility program for linear exchange economies -/

namespace LinearExchangeMarket

section ConvexProgram

variable {I G : Type*} [Fintype I] [Fintype G] (E : LinearExchangeMarket I G)

/-- Feasibility constraints of the Nenakov–Primak–Jain convex program for a linear exchange economy
([CodenottiVaradarajan2007], Section 6.4.1, p. 149): logarithmic prices `ψ : G → ℝ` (representing
`π_g = exp (ψ g)`) and nonnegative allocations `x : I → G → ℝ` clearing every good's aggregate
supply and satisfying `∑_k a_{ik} x_{ik} ≥ a_{ij} ∑_k w_{ik} exp (ψ_k - ψ_j)` for all `i, j`. -/
@[expose] def IsConvexProgramFeasible (ψ : G → ℝ) (x : I → G → ℝ) : Prop :=
  (∀ i g, 0 ≤ x i g) ∧
  (∀ g, ∑ i : I, x i g = E.toExchangeMarket.totalSupply g) ∧
  ∀ i g, E.utility i g * (∑ k : G, E.endowment i k * Real.exp (ψ k - ψ g)) ≤
    ∑ k : G, E.utility i k * x i k

/-- **Equivalence of the linear-exchange convex program with positive-price competitive equilibria**
([CodenottiVaradarajan2007], Section 6.4.1, p. 149): when every trader desires at least one good,
`(ψ, x)` satisfies `E.IsConvexProgramFeasible ψ x` if and only if `(x, fun g => Real.exp (ψ g))` is
a competitive equilibrium of `E`. -/
theorem isConvexProgramFeasible_iff_isCompetitiveEquilibrium
    (hns : ∀ i : I, ∃ g : G, 0 < E.utility i g) (ψ : G → ℝ) (x : I → G → ℝ) :
    E.IsConvexProgramFeasible ψ x ↔
      E.IsCompetitiveEquilibrium x (fun g => Real.exp (ψ g)) := by
  set p : G → ℝ := fun g => Real.exp (ψ g)
  have hp : ∀ g : G, 0 < p g := fun g => Real.exp_pos (ψ g)
  have hrhs_eq : ∀ i g,
      E.utility i g * (∑ k : G, E.endowment i k * Real.exp (ψ k - ψ g)) =
        (E.utility i g / p g) * E.toExchangeMarket.income p i := by
    intro i g
    rw [ExchangeMarket.income_eq, toExchangeMarket_endowment, expenditure_eq_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Real.exp_sub]
    dsimp only [p]
    ring
  rw [E.isCompetitiveEquilibrium_iff_bangPerBuck hp hns]
  constructor
  · rintro ⟨hx_nn, hclear, hineq⟩
    have hG_nonempty : ∀ i : I, (univ : Finset G).Nonempty := fun i => by
      obtain ⟨g, _⟩ := hns i
      exact ⟨g, mem_univ g⟩
    let r : I → ℝ := fun i =>
      univ.sup' (hG_nonempty i) fun g => E.utility i g / p g
    have hr_ge : ∀ i g, E.utility i g / p g ≤ r i := fun i g =>
      le_sup' (fun k => E.utility i k / p k) (mem_univ g)
    have hr_pos : ∀ i, 0 < r i := fun i => by
      obtain ⟨g, hg⟩ := hns i
      exact (div_pos hg (hp g)).trans_le (hr_ge i g)
    have hutil_le_exp : ∀ i, ∑ k : G, E.utility i k * x i k ≤ r i * expenditure p (x i) := by
      intro i
      rw [expenditure_eq_sum, mul_sum]
      refine sum_le_sum fun k _ => ?_
      have hle : E.utility i k ≤ r i * p k := (div_le_iff₀ (hp k)).1 (hr_ge i k)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hle (hx_nn i k)
    have hinc_le_util : ∀ i, r i * E.toExchangeMarket.income p i ≤
        ∑ k : G, E.utility i k * x i k := by
      intro i
      obtain ⟨g₀, -, hg₀⟩ := exists_mem_eq_sup' (hG_nonempty i) fun k => E.utility i k / p k
      have hr_eq : r i = E.utility i g₀ / p g₀ := hg₀
      rw [hr_eq, ← hrhs_eq i g₀]
      exact hineq i g₀
    have hinc_le_exp : ∀ i, E.toExchangeMarket.income p i ≤ expenditure p (x i) := fun i =>
      le_of_mul_le_mul_left ((hinc_le_util i).trans (hutil_le_exp i)) (hr_pos i)
    have hsum_eq : ∑ i : I, E.toExchangeMarket.income p i = ∑ i : I, expenditure p (x i) := by
      rw [E.toExchangeMarket.sum_income p, expenditure_eq_sum]
      calc ∑ g : G, p g * E.toExchangeMarket.totalSupply g
          = ∑ g : G, p g * ∑ i : I, x i g :=
              sum_congr rfl fun g _ => by rw [hclear g]
        _ = ∑ i : I, expenditure p (x i) := by
              simp only [expenditure_eq_sum, mul_sum]
              exact sum_comm
    have hexp_eq : ∀ i, expenditure p (x i) = E.toExchangeMarket.income p i := fun i => by
      have hdiff0 : ∑ k : I, (expenditure p (x k) - E.toExchangeMarket.income p k) = 0 := by
        rw [sum_sub_distrib, hsum_eq, sub_self]
      have hi0 := (sum_eq_zero_iff_of_nonneg fun k _ => sub_nonneg.2 (hinc_le_exp k)).1
        hdiff0 i (mem_univ i)
      exact sub_eq_zero.1 hi0
    refine ⟨hx_nn, hclear, hexp_eq, fun i g hxg g' => ?_⟩
    have hutil_eq : ∑ k : G, E.utility i k * x i k = r i * expenditure p (x i) :=
      le_antisymm (hutil_le_exp i) (hexp_eq i ▸ hinc_le_util i)
    have hdiff_k : ∑ k : G, (r i * p k - E.utility i k) * x i k = 0 := by
      have h1 : ∑ k : G, r i * p k * x i k = r i * expenditure p (x i) := by
        rw [expenditure_eq_sum, mul_sum]
        exact sum_congr rfl fun k _ => by ring
      simp only [sub_mul, sum_sub_distrib, h1, hutil_eq, sub_self]
    have hterm_nn : ∀ k ∈ (univ : Finset G), 0 ≤ (r i * p k - E.utility i k) * x i k :=
      fun k _ => mul_nonneg (sub_nonneg.2 ((div_le_iff₀ (hp k)).1 (hr_ge i k))) (hx_nn i k)
    have hg0 := (sum_eq_zero_iff_of_nonneg hterm_nn).1 hdiff_k g (mem_univ g)
    have hrg : E.utility i g / p g = r i := by
      have hzero : r i * p g - E.utility i g = 0 := (mul_eq_zero.1 hg0).resolve_right hxg.ne'
      exact (div_eq_iff (hp g).ne').2 (by linarith)
    exact (hr_ge i g').trans_eq hrg.symm
  · rintro ⟨hx_nn, hclear, hexp, hmax⟩
    refine ⟨hx_nn, hclear, fun i g => ?_⟩
    rw [hrhs_eq i g, ← hexp i, expenditure_eq_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    rcases (hx_nn i k).eq_or_lt with hxk0 | hxk
    · simp [← hxk0]
    · have hle : E.utility i g / p g * p k ≤ E.utility i k :=
        (le_div_iff₀ (hp k)).1 (hmax i k hxk g)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hle hxk.le

/-- When every trader desires some good and every good is desired by some trader, every competitive
equilibrium `(x, p)` of `E` has strictly positive prices and corresponds via `ψ g = Real.log (p g)`
to a feasible solution of the linear-exchange convex program ([CodenottiVaradarajan2007],
Section 6.4.1, p. 149). -/
theorem exists_isConvexProgramFeasible_of_isCompetitiveEquilibrium
    (hns : ∀ i : I, ∃ g : G, 0 < E.utility i g)
    (hgood : ∀ g : G, ∃ i : I, 0 < E.utility i g)
    {x : I → G → ℝ} {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p) :
    ∃ ψ : G → ℝ, (∀ g, Real.exp (ψ g) = p g) ∧ E.IsConvexProgramFeasible ψ x := by
  have hp_pos : ∀ g : G, 0 < p g := fun g => by
    obtain ⟨i, hi⟩ := hgood g
    exact price_pos_of_mem_demandSet_linearUtility heq.1
      (E.toExchangeMarket_utility i ▸ E.toExchangeMarket.mem_demandSet.1 (heq.2.1 i)) hi
  refine ⟨fun g => Real.log (p g), fun g => Real.exp_log (hp_pos g), ?_⟩
  rw [E.isConvexProgramFeasible_iff_isCompetitiveEquilibrium hns]
  have hp_eq : (fun g => Real.exp (Real.log (p g))) = p := funext fun g => Real.exp_log (hp_pos g)
  rwa [hp_eq]

/-- **Convexity of the linear-exchange feasibility set** ([CodenottiVaradarajan2007], Section 6.4.1,
p. 149): the set of pairs `(ψ, x)` satisfying `E.IsConvexProgramFeasible ψ x` is convex. -/
theorem convex_setOf_isConvexProgramFeasible :
    Convex ℝ {q : (G → ℝ) × (I → G → ℝ) | E.IsConvexProgramFeasible q.1 q.2} := by
  rintro ⟨ψ₁, x₁⟩ ⟨hx₁_nn, hx₁_clr, hx₁_ineq⟩ ⟨ψ₂, x₂⟩ ⟨hx₂_nn, hx₂_clr, hx₂_ineq⟩ a b ha hb hab
  refine ⟨fun i g => add_nonneg (mul_nonneg ha (hx₁_nn i g)) (mul_nonneg hb (hx₂_nn i g)),
    fun g => ?_, fun i g => ?_⟩
  · simp only [Prod.smul_snd, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      sum_add_distrib, ← mul_sum, hx₁_clr g, hx₂_clr g]
    rw [← add_mul, hab, one_mul]
  · simp only [Prod.smul_fst, Prod.fst_add, Prod.smul_snd, Prod.snd_add, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have hexp_conv : ∀ k : G,
        Real.exp ((a * ψ₁ k + b * ψ₂ k) - (a * ψ₁ g + b * ψ₂ g)) ≤
          a * Real.exp (ψ₁ k - ψ₁ g) + b * Real.exp (ψ₂ k - ψ₂ g) := fun k => by
      have harg : (a * ψ₁ k + b * ψ₂ k) - (a * ψ₁ g + b * ψ₂ g) =
          a • (ψ₁ k - ψ₁ g) + b • (ψ₂ k - ψ₂ g) := by simp only [smul_eq_mul]; ring
      rw [harg]
      simpa only [smul_eq_mul] using
        convexOn_exp.2 (mem_univ (ψ₁ k - ψ₁ g)) (mem_univ (ψ₂ k - ψ₂ g)) ha hb hab
    have hsum_le :
        E.utility i g *
            ∑ k : G, E.endowment i k * Real.exp ((a * ψ₁ k + b * ψ₂ k) - (a * ψ₁ g + b * ψ₂ g)) ≤
          a * (E.utility i g * ∑ k : G, E.endowment i k * Real.exp (ψ₁ k - ψ₁ g)) +
            b * (E.utility i g * ∑ k : G, E.endowment i k * Real.exp (ψ₂ k - ψ₂ g)) := by
      have h1 : ∑ k : G, E.endowment i k *
            Real.exp ((a * ψ₁ k + b * ψ₂ k) - (a * ψ₁ g + b * ψ₂ g)) ≤
          a * (∑ k : G, E.endowment i k * Real.exp (ψ₁ k - ψ₁ g)) +
            b * (∑ k : G, E.endowment i k * Real.exp (ψ₂ k - ψ₂ g)) := by
        calc
          ∑ k : G, E.endowment i k *
              Real.exp ((a * ψ₁ k + b * ψ₂ k) - (a * ψ₁ g + b * ψ₂ g))
            ≤ ∑ k : G, E.endowment i k *
                (a * Real.exp (ψ₁ k - ψ₁ g) + b * Real.exp (ψ₂ k - ψ₂ g)) :=
                sum_le_sum fun k _ =>
                  mul_le_mul_of_nonneg_left (hexp_conv k) (E.endowment_nonneg i k)
          _ = a * (∑ k : G, E.endowment i k * Real.exp (ψ₁ k - ψ₁ g)) +
                b * (∑ k : G, E.endowment i k * Real.exp (ψ₂ k - ψ₂ g)) := by
                simp only [mul_add, sum_add_distrib, mul_sum]
                congr 1 <;> exact sum_congr rfl fun k _ => by ring
      calc
        E.utility i g *
            ∑ k : G, E.endowment i k * Real.exp ((a * ψ₁ k + b * ψ₂ k) - (a * ψ₁ g + b * ψ₂ g))
          ≤ E.utility i g *
              (a * (∑ k : G, E.endowment i k * Real.exp (ψ₁ k - ψ₁ g)) +
                b * (∑ k : G, E.endowment i k * Real.exp (ψ₂ k - ψ₂ g))) :=
              mul_le_mul_of_nonneg_left h1 (E.utility_nonneg i g)
        _ = a * (E.utility i g * ∑ k : G, E.endowment i k * Real.exp (ψ₁ k - ψ₁ g)) +
              b * (E.utility i g * ∑ k : G, E.endowment i k * Real.exp (ψ₂ k - ψ₂ g)) := by ring
    have hrhs_split :
        ∑ k : G, E.utility i k * (a * x₁ i k + b * x₂ i k) =
          a * (∑ k : G, E.utility i k * x₁ i k) + b * (∑ k : G, E.utility i k * x₂ i k) := by
      simp only [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> exact sum_congr rfl fun k _ => by ring
    rw [hrhs_split]
    exact hsum_le.trans (add_le_add (mul_le_mul_of_nonneg_left (hx₁_ineq i g) ha)
      (mul_le_mul_of_nonneg_left (hx₂_ineq i g) hb))

end ConvexProgram

end LinearExchangeMarket

/-! ### §6.4.2 CES utility homogeneity, concavity, strict demand uniqueness, and Proposition 6.11 -/

section CESProperties

variable {G : Type*} [Fintype G]

/-- Positive homogeneity of degree `1` for `cesUtility α ρ` on nonnegative bundles
([CodenottiVaradarajan2007], Section 6.1.5, p. 139). -/
theorem cesUtility_smul {α b : G → ℝ} {ρ c : ℝ}
    (hα : ∀ g, 0 ≤ α g) (hρ : ρ ≠ 0) (hb : ∀ g, 0 ≤ b g) (hc : 0 < c) :
    cesUtility α ρ (c • b) = c * cesUtility α ρ b := by
  have hsum_eq : (∑ g : G, α g * ((c • b) g) ^ ρ) ^ (1 / ρ) =
      c * (∑ g : G, α g * (b g) ^ ρ) ^ (1 / ρ) := by
    have hterm : ∀ g : G, α g * ((c • b) g) ^ ρ = c ^ ρ * (α g * (b g) ^ ρ) := fun g => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Real.mul_rpow hc.le (hb g)]
      ring
    simp_rw [hterm, ← mul_sum]
    have hsum_nn : 0 ≤ ∑ g : G, α g * (b g) ^ ρ :=
      sum_nonneg fun g _ => mul_nonneg (hα g) (Real.rpow_nonneg (hb g) ρ)
    rw [Real.mul_rpow (Real.rpow_nonneg hc.le ρ) hsum_nn, ← Real.rpow_mul hc.le,
      mul_one_div_cancel hρ, Real.rpow_one]
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · by_cases h0 : ∃ g : G, b g ≤ 0
    · obtain ⟨g, hg⟩ := h0
      have hcb0 : ∃ g : G, (c • b) g ≤ 0 := ⟨g, mul_nonpos_of_nonneg_of_nonpos hc.le hg⟩
      rw [cesUtility_of_neg_of_exists_nonpos α hneg hcb0,
        cesUtility_of_neg_of_exists_nonpos α hneg ⟨g, hg⟩, mul_zero]
    · push Not at h0
      have hcb_pos : ∀ g : G, 0 < (c • b) g := fun g => mul_pos hc (h0 g)
      rw [cesUtility_of_bundle_pos α ρ hcb_pos, cesUtility_of_bundle_pos α ρ h0]
      exact hsum_eq
  · rw [cesUtility_of_pos_exp hpos, cesUtility_of_pos_exp hpos]
    exact hsum_eq

/-- Zero scaling of `cesUtility α ρ`: `cesUtility α ρ 0 = 0` for `ρ ≠ 0` on any nonempty `G`. -/
theorem cesUtility_zero [Nonempty G] (α : G → ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    cesUtility α ρ 0 = 0 := by
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · exact cesUtility_of_neg_of_exists_nonpos α hneg ⟨Classical.arbitrary G, le_rfl⟩
  · rw [cesUtility_of_pos_exp hpos]
    simp only [Pi.zero_apply, Real.zero_rpow hpos.ne', mul_zero, sum_const_zero]
    exact Real.zero_rpow (one_div_ne_zero hpos.ne')

/-- Monotonicity of `cesUtility α ρ` on nonnegative bundles for `α ≥ 0` and `ρ ≠ 0`. -/
theorem cesUtility_mono {α b₁ b₂ : G → ℝ} {ρ : ℝ}
    (hα : ∀ g, 0 ≤ α g) (hρ : ρ ≠ 0) (hb₁ : ∀ g, 0 ≤ b₁ g) (hle : ∀ g, b₁ g ≤ b₂ g) :
    cesUtility α ρ b₁ ≤ cesUtility α ρ b₂ := by
  have hb₂ : ∀ g, 0 ≤ b₂ g := fun g => (hb₁ g).trans (hle g)
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · by_cases h1 : ∃ g : G, b₁ g ≤ 0
    · rw [cesUtility_of_neg_of_exists_nonpos α hneg h1]
      exact cesUtility_nonneg hα ρ hb₂
    · push Not at h1
      have h2 : ∀ g, 0 < b₂ g := fun g => lt_of_lt_of_le (h1 g) (hle g)
      rw [cesUtility_of_bundle_pos α ρ h1, cesUtility_of_bundle_pos α ρ h2]
      rcases eq_or_lt_of_le (sum_nonneg fun g _ =>
          mul_nonneg (hα g) (Real.rpow_nonneg (h2 g).le ρ)) with hsum20 | hsum2_pos
      · have hα0 : ∀ g, α g = 0 := fun g => by
          have hg0 := (sum_eq_zero_iff_of_nonneg fun k _ =>
            mul_nonneg (hα k) (Real.rpow_nonneg (h2 k).le ρ)).1 hsum20.symm g (mem_univ g)
          exact (mul_eq_zero.1 hg0).resolve_right (Real.rpow_pos_of_pos (h2 g) ρ).ne'
        simp [hα0]
      · have hsum_le : ∑ g : G, α g * (b₂ g) ^ ρ ≤ ∑ g : G, α g * (b₁ g) ^ ρ :=
          sum_le_sum fun g _ => mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (h1 g) (hle g) hneg.le) (hα g)
        exact Real.rpow_le_rpow_of_nonpos hsum2_pos hsum_le (one_div_nonpos.2 hneg.le)
  · rw [cesUtility_of_pos_exp hpos, cesUtility_of_pos_exp hpos]
    refine Real.rpow_le_rpow
      (sum_nonneg fun g _ => mul_nonneg (hα g) (Real.rpow_nonneg (hb₁ g) ρ))
      (sum_le_sum fun g _ => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hb₁ g) (hle g) hpos.le) (hα g))
      (one_div_nonneg.2 hpos.le)

/-- Reverse Minkowski superadditivity for `cesUtility α ρ` on nonnegative bundles when `ρ < 1`,
`ρ ≠ 0`, and `α > 0`. -/
private theorem cesUtility_add_ge.{u} {G : Type u} [Fintype G] {α x y : G → ℝ} {ρ : ℝ}
    (hα : ∀ g, 0 < α g) (hρ_lt : ρ < 1) (hρ_ne : ρ ≠ 0)
    (hx : ∀ g, 0 ≤ x g) (hy : ∀ g, 0 ≤ y g) :
    cesUtility α ρ x + cesUtility α ρ y ≤ cesUtility α ρ (x + y) := by
  have hxy_nn : ∀ g, 0 ≤ (x + y) g := fun g => add_nonneg (hx g) (hy g)
  have hα_nn : ∀ g, 0 ≤ α g := fun g => (hα g).le
  -- Helper proving superadditivity on any nonempty finite index type where `x + y > 0`.
  have hcore : ∀ {ι : Type u} [Fintype ι] [Nonempty ι] (β u v : ι → ℝ),
      (∀ i, 0 < β i) → (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) →
      (ρ < 0 → (∀ i, 0 < u i) ∧ (∀ i, 0 < v i)) →
      (∀ i, 0 < u i + v i) →
      (∑ i : ι, β i * (u i) ^ ρ) ^ (1 / ρ) + (∑ i : ι, β i * (v i) ^ ρ) ^ (1 / ρ) ≤
        (∑ i : ι, β i * (u i + v i) ^ ρ) ^ (1 / ρ) := by
    intro ι _ _ β u v hβ hu hv hneg_pos huv
    let fu : ι → ℝ := fun i => (β i) ^ (1 / ρ) * u i
    let fv : ι → ℝ := fun i => (β i) ^ (1 / ρ) * v i
    let fw : ι → ℝ := fun i => fu i + fv i
    let h : ι → ℝ := fun i => (fw i) ^ (ρ - 1)
    have hfu_nn : ∀ i, 0 ≤ fu i := fun i => mul_nonneg (Real.rpow_nonneg (hβ i).le _) (hu i)
    have hfv_nn : ∀ i, 0 ≤ fv i := fun i => mul_nonneg (Real.rpow_nonneg (hβ i).le _) (hv i)
    have hfw_pos : ∀ i, 0 < fw i := fun i => by
      have : fw i = (β i) ^ (1 / ρ) * (u i + v i) := by dsimp only [fw, fu, fv]; ring
      rw [this]
      exact mul_pos (Real.rpow_pos_of_pos (hβ i) _) (huv i)
    have hh_pos : ∀ i, 0 < h i := fun i => Real.rpow_pos_of_pos (hfw_pos i) _
    have hnorm_h_pos : 0 < Cslib.lpNorm (ρ / (ρ - 1)) h := Cslib.lpNorm_pos _ hh_pos
    have hrh_u : Cslib.lpNorm ρ fu * Cslib.lpNorm (ρ / (ρ - 1)) h ≤ 𝔼 i : ι, fu i * h i := by
      rcases lt_or_gt_of_ne hρ_ne with hneg | hpos
      · exact Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_neg hneg
          (fun i => mul_pos (Real.rpow_pos_of_pos (hβ i) _) ((hneg_pos hneg).1 i))
          (fun i => (hh_pos i).le)
      · exact Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_pos hpos hρ_lt hfu_nn hh_pos
    have hrh_v : Cslib.lpNorm ρ fv * Cslib.lpNorm (ρ / (ρ - 1)) h ≤ 𝔼 i : ι, fv i * h i := by
      rcases lt_or_gt_of_ne hρ_ne with hneg | hpos
      · exact Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_neg hneg
          (fun i => mul_pos (Real.rpow_pos_of_pos (hβ i) _) ((hneg_pos hneg).2 i))
          (fun i => (hh_pos i).le)
      · exact Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_pos hpos hρ_lt hfv_nn hh_pos
    have heq_w : 𝔼 i : ι, fw i * h i = Cslib.lpNorm ρ fw * Cslib.lpNorm (ρ / (ρ - 1)) h :=
      Cslib.expect_mul_rpow_sub_one hρ_ne hρ_lt.ne hfw_pos
    have hexp_add : (𝔼 i : ι, fu i * h i) + (𝔼 i : ι, fv i * h i) = 𝔼 i : ι, fw i * h i := by
      rw [← expect_add_distrib]
      exact expect_congr rfl fun i _ => by dsimp only [fw]; ring
    have hlp_le : Cslib.lpNorm ρ fu + Cslib.lpNorm ρ fv ≤ Cslib.lpNorm ρ fw := by
      have hmul : (Cslib.lpNorm ρ fu + Cslib.lpNorm ρ fv) * Cslib.lpNorm (ρ / (ρ - 1)) h ≤
          Cslib.lpNorm ρ fw * Cslib.lpNorm (ρ / (ρ - 1)) h := by linarith
      exact le_of_mul_le_mul_right hmul hnorm_h_pos
    have hcard_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
    have hcard_rpow_pos : 0 < (Fintype.card ι : ℝ) ^ (1 / ρ) :=
      Real.rpow_pos_of_pos hcard_pos _
    have hlp_to_sum : ∀ (z : ι → ℝ), (∀ i, 0 ≤ z i) →
        (Fintype.card ι : ℝ) ^ (1 / ρ) * Cslib.lpNorm ρ (fun i => (β i) ^ (1 / ρ) * z i) =
          (∑ i : ι, β i * (z i) ^ ρ) ^ (1 / ρ) := fun z hz => by
      have hfz_nn : ∀ i, 0 ≤ (β i) ^ (1 / ρ) * z i := fun i =>
        mul_nonneg (Real.rpow_nonneg (hβ i).le _) (hz i)
      rw [Cslib.lpNorm_of_nonneg ρ hfz_nn, expect_eq_sum_div_card, card_univ]
      have hpow : ∀ i : ι, ((β i) ^ (1 / ρ) * z i) ^ ρ = β i * (z i) ^ ρ := fun i => by
        rw [Real.mul_rpow (Real.rpow_nonneg (hβ i).le _) (hz i), ← Real.rpow_mul (hβ i).le,
          one_div_mul_cancel hρ_ne, Real.rpow_one]
      simp_rw [hpow]
      have hsum_nn : 0 ≤ ∑ i : ι, β i * (z i) ^ ρ :=
        sum_nonneg fun i _ => mul_nonneg (hβ i).le (Real.rpow_nonneg (hz i) ρ)
      have hcr_ne : (Fintype.card ι : ℝ) ^ ρ⁻¹ ≠ 0 := (Real.rpow_pos_of_pos hcard_pos _).ne'
      rw [one_div, Real.div_rpow hsum_nn hcard_pos.le, mul_div_cancel₀ _ hcr_ne]
    have hfw_eq : fw = fun i => (β i) ^ (1 / ρ) * (u i + v i) := funext fun i => by
      dsimp only [fw, fu, fv]; ring
    have hmul := mul_le_mul_of_nonneg_left hlp_le hcard_rpow_pos.le
    rw [mul_add, hfw_eq, hlp_to_sum u hu, hlp_to_sum v hv,
      hlp_to_sum (fun i => u i + v i) fun i => (huv i).le] at hmul
    exact hmul
  rcases lt_or_gt_of_ne hρ_ne with hneg | hpos
  · by_cases hx0 : ∃ g : G, x g ≤ 0
    · rw [cesUtility_of_neg_of_exists_nonpos α hneg hx0, zero_add]
      exact cesUtility_mono hα_nn hρ_ne hy fun g => le_add_of_nonneg_left (hx g)
    · by_cases hy0 : ∃ g : G, y g ≤ 0
      · rw [cesUtility_of_neg_of_exists_nonpos α hneg hy0, add_zero]
        exact cesUtility_mono hα_nn hρ_ne hx fun g => le_add_of_nonneg_right (hy g)
      · push Not at hx0 hy0
        rcases isEmpty_or_nonempty G with hEmpty | hNonempty
        · have hxy_pos : ∀ g, 0 < (x + y) g := fun g => add_pos (hx0 g) (hy0 g)
          rw [cesUtility_of_bundle_pos α ρ hx0, cesUtility_of_bundle_pos α ρ hy0,
            cesUtility_of_bundle_pos α ρ hxy_pos]
          simp [Real.zero_rpow (inv_ne_zero hρ_ne)]
        · have hxy_pos : ∀ g, 0 < (x + y) g := fun g => add_pos (hx0 g) (hy0 g)
          rw [cesUtility_of_bundle_pos α ρ hx0, cesUtility_of_bundle_pos α ρ hy0,
            cesUtility_of_bundle_pos α ρ hxy_pos]
          exact hcore α x y hα hx hy (fun _ => ⟨hx0, hy0⟩) fun g => hxy_pos g
  · rw [cesUtility_of_pos_exp hpos, cesUtility_of_pos_exp hpos, cesUtility_of_pos_exp hpos]
    classical
    let S : Finset G := univ.filter fun g => 0 < x g + y g
    by_cases hS : S.Nonempty
    · have hzero_out : ∀ g, g ∉ S → x g = 0 ∧ y g = 0 := fun g hg => by
        have hle : x g + y g ≤ 0 := not_lt.1 fun hlt => hg (mem_filter.2 ⟨mem_univ g, hlt⟩)
        exact ⟨by linarith [hx g, hy g], by linarith [hx g, hy g]⟩
      have hsum_restrict : ∀ (z : G → ℝ), (∀ g, g ∉ S → z g = 0) →
          ∑ g : G, α g * (z g) ^ ρ = ∑ s : S, α s.1 * (z s.1) ^ ρ := fun z hz => by
        calc ∑ g : G, α g * (z g) ^ ρ
            = ∑ g ∈ S, α g * (z g) ^ ρ :=
                (sum_subset (subset_univ S) fun g _ hg => by
                  rw [hz g hg, Real.zero_rpow hpos.ne', mul_zero]).symm
          _ = ∑ s : S, α s.1 * (z s.1) ^ ρ := (sum_coe_sort S fun g => α g * (z g) ^ ρ).symm
      have : Nonempty S := hS.coe_sort
      have hxy_restrict : ∑ g : G, α g * ((x + y) g) ^ ρ =
          ∑ s : S, α s.1 * (x s.1 + y s.1) ^ ρ :=
        hsum_restrict (x + y) fun g hg => by simp [(hzero_out g hg).1, (hzero_out g hg).2]
      rw [hsum_restrict x fun g hg => (hzero_out g hg).1,
        hsum_restrict y fun g hg => (hzero_out g hg).2, hxy_restrict]
      exact hcore (ι := S) (fun s => α s.1) (fun s => x s.1) (fun s => y s.1)
        (fun s => hα s.1) (fun s => hx s.1) (fun s => hy s.1)
        (fun hlt => (not_lt_of_gt hpos hlt).elim)
        (fun s => (mem_filter.1 s.2).2)
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      have hall0 : ∀ g : G, x g = 0 ∧ y g = 0 := fun g => by
        have hnot : ¬ 0 < x g + y g := fun hlt => by
          have : g ∈ S := mem_filter.2 ⟨mem_univ g, hlt⟩
          rw [hS] at this
          exact notMem_empty g this
        exact ⟨by linarith [hx g, hy g], by linarith [hx g, hy g]⟩
      have hx0 : x = 0 := funext fun g => (hall0 g).1
      have hy0 : y = 0 := funext fun g => (hall0 g).2
      simp [hx0, hy0, Real.zero_rpow hpos.ne', Real.zero_rpow (inv_ne_zero hρ_ne)]

/-- **Concavity of CES utilities** ([CodenottiVaradarajan2007], Section 6.1.5, p. 139 and
Section 6.4.2, p. 150): for strictly positive weights `α > 0` and any exponent `ρ ≤ 1` with
`ρ ≠ 0`, `cesUtility α ρ` is concave on `{b : G → ℝ | ∀ g, 0 ≤ b g}`. -/
theorem concaveOn_cesUtility {α : G → ℝ} {ρ : ℝ}
    (hα : ∀ g, 0 < α g) (hρ_le : ρ ≤ 1) (hρ_ne : ρ ≠ 0) :
    ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (cesUtility α ρ) := by
  have hconv_dom : Convex ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} := fun x hx y hy a b ha hb _ g =>
    add_nonneg (mul_nonneg ha (hx g)) (mul_nonneg hb (hy g))
  refine ⟨hconv_dom, fun x hx y hy a b ha hb hab => ?_⟩
  rcases hρ_le.eq_or_lt with rfl | hρ_lt
  · simp only [cesUtility_of_pos_exp zero_lt_one, Real.rpow_one, div_one, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum]
    refine le_of_eq (congrArg₂ (· + ·) ?_ ?_) <;>
      exact sum_congr rfl fun g _ => by ring
  · rcases eq_or_lt_of_le ha with rfl | ha_pos
    · obtain rfl : b = 1 := by linarith
      simp
    · rcases eq_or_lt_of_le hb with rfl | hb_pos
      · obtain rfl : a = 1 := by linarith
        simp
      · have hα_nn : ∀ g, 0 ≤ α g := fun g => (hα g).le
        have hadd := cesUtility_add_ge (x := a • x) (y := b • y) hα hρ_lt hρ_ne
          (fun g => mul_nonneg ha (hx g)) (fun g => mul_nonneg hb (hy g))
        rw [cesUtility_smul hα_nn hρ_ne hx ha_pos, cesUtility_smul hα_nn hρ_ne hy hb_pos] at hadd
        simpa only [smul_eq_mul] using hadd

/-- One-dimensional strict tangent inequality for `z ↦ z ^ ρ` at `z = 1` when `0 < ρ < 1`:
`z ^ ρ < 1 + ρ * (z - 1)` for every `z ≥ 0` with `z ≠ 1`. -/
private theorem rpow_lt_one_add_mul_sub_one_of_pos {ρ z : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hz : 0 ≤ z) (hne : z ≠ 1) :
    z ^ ρ < 1 + ρ * (z - 1) := by
  let φ : ℝ → ℝ := fun t => t ^ ρ - (1 + ρ * (t - 1))
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt φ (ρ * (t ^ (ρ - 1) - 1)) t := fun t ht => by
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := ρ) (Or.inl (mem_Ioi.1 ht).ne')
    have h2 : HasDerivAt (fun s : ℝ => 1 + ρ * (s - 1)) ρ t := by
      simpa only [mul_one] using (((hasDerivAt_id' t).sub_const 1).const_mul ρ).const_add 1
    convert h1.sub h2 using 1
    ring
  have hcont : ContinuousOn φ (Ici 0) :=
    (continuousOn_id.rpow_const fun _ _ => Or.inr hρ0.le).sub
      (continuous_const.add
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  rcases lt_or_gt_of_ne hne with hz_lt | hz_gt
  · have hmono : StrictMonoOn φ (Icc z 1) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc z 1)
        (hcont.mono fun t ht => hz.trans ht.1) fun t ht => ?_
      rw [interior_Icc] at ht
      have ht0 : 0 < t := hz.trans_lt ht.1
      rw [(hderiv t ht0).deriv]
      have hgt1 : 1 < t ^ (ρ - 1) := by
        simpa only [Real.one_rpow] using
          Real.rpow_lt_rpow_of_neg ht0 ht.2 (by linarith : ρ - 1 < 0)
      nlinarith
    have hlt : φ z < φ 1 := hmono ⟨le_rfl, hz_lt.le⟩ ⟨hz_lt.le, le_rfl⟩ hz_lt
    dsimp only [φ] at hlt
    simp only [Real.one_rpow, sub_self, mul_zero, add_zero] at hlt
    linarith
  · have hanti : StrictAntiOn φ (Icc 1 z) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc 1 z)
        (hcont.mono fun t ht => zero_le_one.trans ht.1) fun t ht => ?_
      rw [interior_Icc] at ht
      have ht0 : 0 < t := zero_lt_one.trans ht.1
      rw [(hderiv t ht0).deriv]
      have hlt1 : t ^ (ρ - 1) < 1 := by
        simpa only [Real.one_rpow] using
          Real.rpow_lt_rpow_of_neg zero_lt_one ht.1 (by linarith : ρ - 1 < 0)
      nlinarith
    have hlt : φ z < φ 1 := hanti ⟨le_rfl, hz_gt.le⟩ ⟨hz_gt.le, le_rfl⟩ hz_gt
    dsimp only [φ] at hlt
    simp only [Real.one_rpow, sub_self, mul_zero, add_zero] at hlt
    linarith

/-- One-dimensional strict tangent inequality for `z ↦ z ^ ρ` at `z = 1` when `ρ < 0`:
`1 + ρ * (z - 1) < z ^ ρ` for every `z > 0` with `z ≠ 1`. -/
private theorem one_add_mul_sub_one_lt_rpow_of_neg {ρ z : ℝ}
    (hρ : ρ < 0) (hz : 0 < z) (hne : z ≠ 1) :
    1 + ρ * (z - 1) < z ^ ρ := by
  let φ : ℝ → ℝ := fun t => t ^ ρ - (1 + ρ * (t - 1))
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt φ (ρ * (t ^ (ρ - 1) - 1)) t := fun t ht => by
    have h1 := Real.hasDerivAt_rpow_const (x := t) (p := ρ) (Or.inl (mem_Ioi.1 ht).ne')
    have h2 : HasDerivAt (fun s : ℝ => 1 + ρ * (s - 1)) ρ t := by
      simpa only [mul_one] using (((hasDerivAt_id' t).sub_const 1).const_mul ρ).const_add 1
    convert h1.sub h2 using 1
    ring
  have hφ1 : φ 1 = 0 := by simp [φ]
  rcases lt_or_gt_of_ne hne with hz_lt | hz_gt
  · have hanti : StrictAntiOn φ (Icc z 1) := by
      refine strictAntiOn_of_deriv_neg (convex_Icc z 1)
        (fun t ht => (hderiv t (hz.trans_le ht.1)).continuousAt.continuousWithinAt) fun t ht => ?_
      rw [interior_Icc] at ht
      rw [(hderiv t (hz.trans ht.1)).deriv]
      have hgt1 : 1 < t ^ (ρ - 1) := by
        simpa only [Real.one_rpow] using
          Real.rpow_lt_rpow_of_neg (hz.trans ht.1) ht.2 (by linarith : ρ - 1 < 0)
      nlinarith
    have hgt : φ 1 < φ z := hanti ⟨le_rfl, hz_lt.le⟩ ⟨hz_lt.le, le_rfl⟩ hz_lt
    dsimp only [φ] at hgt
    simp only [Real.one_rpow, sub_self, mul_zero, add_zero] at hgt
    linarith
  · have hmono : StrictMonoOn φ (Icc 1 z) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 1 z)
        (fun t ht => (hderiv t (zero_lt_one.trans_le ht.1)).continuousAt.continuousWithinAt)
        fun t ht => ?_
      rw [interior_Icc] at ht
      rw [(hderiv t (zero_lt_one.trans ht.1)).deriv]
      have hlt1 : t ^ (ρ - 1) < 1 := by
        simpa only [Real.one_rpow] using
          Real.rpow_lt_rpow_of_neg zero_lt_one ht.1 (by linarith : ρ - 1 < 0)
      nlinarith
    have hgt : φ 1 < φ z := hmono ⟨le_rfl, hz_gt.le⟩ ⟨hz_gt.le, le_rfl⟩ hz_gt
    dsimp only [φ] at hgt
    simp only [Real.one_rpow, sub_self, mul_zero, add_zero] at hgt
    linarith

/-- **Strict uniqueness of CES Marshallian demand (Equation `(6.7)`)** ([CodenottiVaradarajan2007],
Section 6.4.2, p. 149): for strictly positive weights `α > 0`, exponent `ρ < 1` with `ρ ≠ 0`,
strictly positive prices `p > 0`, and budget `m ≥ 0`, `cesDemand α ρ p m` is the **unique**
optimal bundle in `demandSet (cesUtility α ρ) p m`. -/
theorem demandSet_cesUtility_eq [Nonempty G] {α p : G → ℝ} {ρ m : ℝ}
    (hα : ∀ g, 0 < α g) (hρ_lt : ρ < 1) (hρ_ne : ρ ≠ 0) (hp : ∀ g, 0 < p g) (hm : 0 ≤ m) :
    demandSet (cesUtility α ρ) p m = {cesDemand α ρ p m} := by
  refine Set.Subset.antisymm (fun b hb => ?_)
    (Set.singleton_subset_iff.2 (cesDemand_mem_demandSet hα hρ_lt hρ_ne hp hm))
  rw [mem_demandSet] at hb
  rw [Set.mem_singleton_iff]
  set xStar := cesDemand α ρ p m
  have hx_mem := (mem_demandSet).1 (cesDemand_mem_demandSet hα hρ_lt hρ_ne hp hm)
  rcases eq_or_lt_of_le hm with rfl | hm_pos
  · rw [hb.1.eq_zero_of_zero hp]
    exact funext fun g => by simp [xStar, cesDemand_apply]
  · set D : ℝ := ∑ k : G, (α k) ^ (1 / (1 - ρ)) * (p k) ^ (- ρ / (1 - ρ))
    have hD_pos : 0 < D := sum_pos
      (fun k _ => mul_pos (Real.rpow_pos_of_pos (hα k) _) (Real.rpow_pos_of_pos (hp k) _))
      univ_nonempty
    have h1ρ_pos : 0 < 1 - ρ := by linarith
    have hx_pos : ∀ g, 0 < xStar g := fun g => by
      dsimp only [xStar]; rw [cesDemand_apply]
      exact mul_pos (div_pos (Real.rpow_pos_of_pos (hα g) _) (Real.rpow_pos_of_pos (hp g) _))
        (div_pos hm_pos hD_pos)
    have hux_pos : 0 < cesUtility α ρ xStar := by
      rw [cesUtility_of_bundle_pos α ρ hx_pos]
      exact Real.rpow_pos_of_pos (sum_pos
        (fun g _ => mul_pos (hα g) (Real.rpow_pos_of_pos (hx_pos g) ρ)) univ_nonempty) _
    have hge : cesUtility α ρ xStar ≤ cesUtility α ρ b := hb.2 xStar hx_mem.1
    -- Define positive budget weights `w g = p g * xStar g / m` and ratios `z g = b g / xStar g`.
    let w : G → ℝ := fun g => p g * xStar g / m
    let z : G → ℝ := fun g => b g / xStar g
    have hw_pos : ∀ g, 0 < w g := fun g => div_pos (mul_pos (hp g) (hx_pos g)) hm_pos
    have hw_sum : ∑ g : G, w g = 1 := by
      dsimp only [w]
      rw [← sum_div, ← expenditure_eq_sum, expenditure_cesDemand hα hρ_lt hp m, div_self hm_pos.ne']
    have hwz_le : ∑ g : G, w g * z g ≤ 1 := by
      have hterm : ∀ g : G, w g * z g = p g * b g / m := fun g => by
        dsimp only [w, z]
        field_simp [hm_pos.ne', (hx_pos g).ne']
      rw [sum_congr rfl fun g _ => hterm g, ← sum_div, ← expenditure_eq_sum]
      exact (div_le_one hm_pos).2 hb.1.2
    -- Express `α g * (xStar g) ^ ρ = w g * SStar`, where `SStar = ∑ k, α k * (xStar k) ^ ρ`.
    set SStar : ℝ := ∑ g : G, α g * (xStar g) ^ ρ
    have hSStar_pos : 0 < SStar := sum_pos
      (fun g _ => mul_pos (hα g) (Real.rpow_pos_of_pos (hx_pos g) ρ)) univ_nonempty
    have hterm_eq : ∀ g : G, α g * (xStar g) ^ ρ = w g * (D * (m / D) ^ ρ) := by
      intro g
      have hp_pow : p g / (p g) ^ (1 / (1 - ρ)) = (p g) ^ (- ρ / (1 - ρ)) := by
        calc p g / (p g) ^ (1 / (1 - ρ))
            = (p g) ^ (1 : ℝ) / (p g) ^ (1 / (1 - ρ)) := by rw [Real.rpow_one]
          _ = (p g) ^ (1 - 1 / (1 - ρ)) := (Real.rpow_sub (hp g) _ _).symm
          _ = (p g) ^ (- ρ / (1 - ρ)) := by congr 1; field_simp [h1ρ_pos.ne']; ring
      have hw_eq : w g = (α g) ^ (1 / (1 - ρ)) * (p g) ^ (- ρ / (1 - ρ)) / D := by
        dsimp only [w, xStar]
        rw [cesDemand_apply]
        have : p g * (((α g) ^ (1 / (1 - ρ)) / (p g) ^ (1 / (1 - ρ))) * (m / D)) / m =
            (α g) ^ (1 / (1 - ρ)) * (p g / (p g) ^ (1 / (1 - ρ))) / D := by
          field_simp [hm_pos.ne', hD_pos.ne', (Real.rpow_pos_of_pos (hp g) _).ne']
        rw [this, hp_pow]
      have hα_pow : α g * (α g) ^ (1 / (1 - ρ) * ρ) = (α g) ^ (1 / (1 - ρ)) := by
        calc α g * (α g) ^ (1 / (1 - ρ) * ρ)
            = (α g) ^ (1 : ℝ) * (α g) ^ (1 / (1 - ρ) * ρ) := by rw [Real.rpow_one]
          _ = (α g) ^ (1 + 1 / (1 - ρ) * ρ) := (Real.rpow_add (hα g) _ _).symm
          _ = (α g) ^ (1 / (1 - ρ)) := by congr 1; field_simp [h1ρ_pos.ne']; ring
      have hp_neg : ((p g) ^ (1 / (1 - ρ) * ρ))⁻¹ = (p g) ^ (- ρ / (1 - ρ)) := by
        rw [← Real.rpow_neg (hp g).le, one_div_mul_eq_div, neg_div]
      rw [hw_eq]
      dsimp only [xStar]
      rw [cesDemand_apply,
        Real.mul_rpow (div_nonneg (Real.rpow_nonneg (hα g).le _) (Real.rpow_nonneg (hp g).le _))
          (div_nonneg hm_pos.le hD_pos.le),
        Real.div_rpow (Real.rpow_nonneg (hα g).le _) (Real.rpow_nonneg (hp g).le _),
        ← Real.rpow_mul (hα g).le, ← Real.rpow_mul (hp g).le]
      have hD_cancel : (α g) ^ (1 / (1 - ρ)) * (p g) ^ (-ρ / (1 - ρ)) / D * (D * (m / D) ^ ρ) =
          (α g) ^ (1 / (1 - ρ)) * (p g) ^ (-ρ / (1 - ρ)) * (m / D) ^ ρ := by
        field_simp [hD_pos.ne']
      rw [hD_cancel, div_eq_mul_inv, ← mul_assoc, ← mul_assoc, hα_pow, hp_neg]
    have hSStar_eq : SStar = D * (m / D) ^ ρ := by
      dsimp only [SStar]
      rw [sum_congr rfl fun g _ => hterm_eq g, ← sum_mul, hw_sum, one_mul]
    have hsum_b : ∑ g : G, α g * (b g) ^ ρ = SStar * ∑ g : G, w g * (z g) ^ ρ := by
      rw [mul_sum]
      refine sum_congr rfl fun g _ => ?_
      have hb_eq : b g = xStar g * z g := by dsimp only [z]; field_simp [(hx_pos g).ne']
      rw [hb_eq, Real.mul_rpow (hx_pos g).le (div_nonneg (hb.1.1 g) (hx_pos g).le), ← mul_assoc,
        hterm_eq g, hSStar_eq]
      ring
    -- Prove `z g = 1` for every `g` by contradiction.
    by_contra hne
    have hex_ne : ∃ g₀ : G, z g₀ ≠ 1 := by
      obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hne
      exact ⟨g₀, fun h1 => hg₀ ((div_eq_one_iff_eq (hx_pos g₀).ne').1 h1)⟩
    obtain ⟨g₀, hg₀⟩ := hex_ne
    have hlin : ∑ g : G, w g * (1 + ρ * (z g - 1)) = 1 + ρ * ((∑ g : G, w g * z g) - 1) := by
      have h1 : ∑ g : G, w g * (1 + ρ * (z g - 1)) =
          (∑ g : G, w g) + ρ * ((∑ g : G, w g * z g) - ∑ g : G, w g) := by
        calc ∑ g : G, w g * (1 + ρ * (z g - 1))
            = ∑ g : G, (w g + ρ * (w g * z g - w g)) := sum_congr rfl fun g _ => by ring
          _ = (∑ g : G, w g) + ρ * ((∑ g : G, w g * z g) - ∑ g : G, w g) := by
                simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib]
      rw [h1, hw_sum]
    rcases lt_or_gt_of_ne hρ_ne with hneg | hpos
    · have hb_pos : ∀ g, 0 < b g := by
        by_contra hnot
        push Not at hnot
        rw [cesUtility_of_neg_of_exists_nonpos α hneg hnot] at hge
        linarith
      have hz_pos : ∀ g, 0 < z g := fun g => div_pos (hb_pos g) (hx_pos g)
      have hterm_le : ∀ g ∈ (univ : Finset G), w g * (1 + ρ * (z g - 1)) ≤ w g * (z g) ^ ρ :=
        fun g _ => by
          rcases eq_or_ne (z g) 1 with h1 | hne1
          · simp [h1]
          · exact mul_le_mul_of_nonneg_left
              (one_add_mul_sub_one_lt_rpow_of_neg hneg (hz_pos g) hne1).le (hw_pos g).le
      have hsum_lt : ∑ g : G, w g * (1 + ρ * (z g - 1)) < ∑ g : G, w g * (z g) ^ ρ :=
        sum_lt_sum hterm_le ⟨g₀, mem_univ g₀,
          mul_lt_mul_of_pos_left
            (one_add_mul_sub_one_lt_rpow_of_neg hneg (hz_pos g₀) hg₀) (hw_pos g₀)⟩
      have hlhs_ge : 1 ≤ ∑ g : G, w g * (1 + ρ * (z g - 1)) := by rw [hlin]; nlinarith
      have h1_lt : 1 < ∑ g : G, w g * (z g) ^ ρ := hlhs_ge.trans_lt hsum_lt
      have hlt_u : cesUtility α ρ b < cesUtility α ρ xStar := by
        rw [cesUtility_of_bundle_pos α ρ hb_pos, cesUtility_of_bundle_pos α ρ hx_pos, hsum_b]
        exact Real.rpow_lt_rpow_of_neg hSStar_pos
          (by nlinarith) (one_div_neg.2 hneg)
      linarith
    · have hz_nn : ∀ g, 0 ≤ z g := fun g => div_nonneg (hb.1.1 g) (hx_pos g).le
      have hterm_le : ∀ g ∈ (univ : Finset G), w g * (z g) ^ ρ ≤ w g * (1 + ρ * (z g - 1)) :=
        fun g _ => by
          rcases eq_or_ne (z g) 1 with h1 | hne1
          · simp [h1]
          · exact mul_le_mul_of_nonneg_left
              (rpow_lt_one_add_mul_sub_one_of_pos hpos hρ_lt (hz_nn g) hne1).le (hw_pos g).le
      have hsum_lt : ∑ g : G, w g * (z g) ^ ρ < ∑ g : G, w g * (1 + ρ * (z g - 1)) :=
        sum_lt_sum hterm_le ⟨g₀, mem_univ g₀,
          mul_lt_mul_of_pos_left
            (rpow_lt_one_add_mul_sub_one_of_pos hpos hρ_lt (hz_nn g₀) hg₀) (hw_pos g₀)⟩
      have hrhs_le : ∑ g : G, w g * (1 + ρ * (z g - 1)) ≤ 1 := by rw [hlin]; nlinarith
      have hlt_1 : ∑ g : G, w g * (z g) ^ ρ < 1 := hsum_lt.trans_le hrhs_le
      have hlt_u : cesUtility α ρ b < cesUtility α ρ xStar := by
        rw [cesUtility_of_pos_exp hpos, cesUtility_of_pos_exp hpos, hsum_b]
        have hnn : 0 ≤ SStar * ∑ g : G, w g * (z g) ^ ρ :=
          mul_nonneg hSStar_pos.le (sum_nonneg fun g _ =>
            mul_nonneg (hw_pos g).le (Real.rpow_nonneg (hz_nn g) ρ))
        exact Real.rpow_lt_rpow hnn (by nlinarith) (one_div_pos.2 hpos)
      linarith

/-- Transformed CES demand `f_{ij}(σ) = σ_j * x_{ij}(σ^2)` under the change of variables
`σ_k = π_k^{1 / (1 - ρ)} = √(π_k)` (`ρ = -1`) of [CodenottiVaradarajan2007], Section 6.4.2,
pp. 149–150. -/
noncomputable def cesTransformedDemand (α w : G → ℝ) (ρ_i : ℝ) (σ : G → ℝ) (g : G) : ℝ :=
  σ g * cesDemand α ρ_i (fun k => (σ k) ^ 2) (expenditure (fun k => (σ k) ^ 2) w) g

theorem cesTransformedDemand_apply (α w : G → ℝ) (ρ_i : ℝ) (σ : G → ℝ) (g : G) :
    cesTransformedDemand α w ρ_i σ g =
      σ g * cesDemand α ρ_i (fun k => (σ k) ^ 2) (expenditure (fun k => (σ k) ^ 2) w) g := by rfl

/-- Weighted `ℓ_p` norm `(∑ k, w k * (σ k) ^ p) ^ (1 / p)` is convex on `ℝ_+^G` for `1 ≤ p` and
`w ≥ 0` (by Minkowski's inequality). -/
private theorem convexOn_weighted_lpNorm {w : G → ℝ} {p : ℝ} (hw : ∀ k, 0 ≤ w k) (hp : 1 ≤ p) :
    ConvexOn ℝ {σ : G → ℝ | ∀ k, 0 ≤ σ k}
      (fun σ => (∑ k : G, w k * (σ k) ^ p) ^ (1 / p)) := by
  have hp_pos : 0 < p := by linarith
  have hconv_dom : Convex ℝ {σ : G → ℝ | ∀ k, 0 ≤ σ k} := fun x hx y hy a b ha hb _ k =>
    add_nonneg (mul_nonneg ha (hx k)) (mul_nonneg hb (hy k))
  refine ⟨hconv_dom, fun x hx y hy a b ha hb _ => ?_⟩
  let f : G → ℝ := fun k => (w k) ^ (1 / p) * (a * x k)
  let g : G → ℝ := fun k => (w k) ^ (1 / p) * (b * y k)
  have hf_nn : ∀ k ∈ (univ : Finset G), 0 ≤ f k := fun k _ =>
    mul_nonneg (Real.rpow_nonneg (hw k) _) (mul_nonneg ha (hx k))
  have hg_nn : ∀ k ∈ (univ : Finset G), 0 ≤ g k := fun k _ =>
    mul_nonneg (Real.rpow_nonneg (hw k) _) (mul_nonneg hb (hy k))
  have hmink := Real.Lp_add_le_of_nonneg (s := univ) hp hf_nn hg_nn
  have hterm_fg : ∀ k : G, (f k + g k) ^ p = w k * (a * x k + b * y k) ^ p := fun k => by
    have hfac : f k + g k = (w k) ^ (1 / p) * (a * x k + b * y k) := by dsimp only [f, g]; ring
    rw [hfac, Real.mul_rpow (Real.rpow_nonneg (hw k) _)
        (add_nonneg (mul_nonneg ha (hx k)) (mul_nonneg hb (hy k))),
      ← Real.rpow_mul (hw k), one_div_mul_cancel hp_pos.ne', Real.rpow_one]
  have hterm_f : ∀ k : G, (f k) ^ p = a ^ p * (w k * (x k) ^ p) := fun k => by
    dsimp only [f]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw k) _) (mul_nonneg ha (hx k)),
      Real.mul_rpow ha (hx k), ← Real.rpow_mul (hw k), one_div_mul_cancel hp_pos.ne',
      Real.rpow_one]
    ring
  have hterm_g : ∀ k : G, (g k) ^ p = b ^ p * (w k * (y k) ^ p) := fun k => by
    dsimp only [g]
    rw [Real.mul_rpow (Real.rpow_nonneg (hw k) _) (mul_nonneg hb (hy k)),
      Real.mul_rpow hb (hy k), ← Real.rpow_mul (hw k), one_div_mul_cancel hp_pos.ne',
      Real.rpow_one]
    ring
  have hpull_f : (∑ k : G, (f k) ^ p) ^ (1 / p) = a * (∑ k : G, w k * (x k) ^ p) ^ (1 / p) := by
    simp_rw [hterm_f, ← mul_sum]
    rw [Real.mul_rpow (Real.rpow_nonneg ha p)
        (sum_nonneg fun k _ => mul_nonneg (hw k) (Real.rpow_nonneg (hx k) p)),
      ← Real.rpow_mul ha, mul_one_div_cancel hp_pos.ne', Real.rpow_one]
  have hpull_g : (∑ k : G, (g k) ^ p) ^ (1 / p) = b * (∑ k : G, w k * (y k) ^ p) ^ (1 / p) := by
    simp_rw [hterm_g, ← mul_sum]
    rw [Real.mul_rpow (Real.rpow_nonneg hb p)
        (sum_nonneg fun k _ => mul_nonneg (hw k) (Real.rpow_nonneg (hy k) p)),
      ← Real.rpow_mul hb, mul_one_div_cancel hp_pos.ne', Real.rpow_one]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc (∑ k : G, w k * (a * x k + b * y k) ^ p) ^ (1 / p)
      = (∑ k : G, (f k + g k) ^ p) ^ (1 / p) := by simp_rw [hterm_fg]
    _ ≤ (∑ k : G, (f k) ^ p) ^ (1 / p) + (∑ k : G, (g k) ^ p) ^ (1 / p) := hmink
    _ = a * (∑ k : G, w k * (x k) ^ p) ^ (1 / p) +
          b * (∑ k : G, w k * (y k) ^ p) ^ (1 / p) := by rw [hpull_f, hpull_g]

/-- Concavity of the 3-factor weighted geometric mean `t^{a₁} s^{a₂} v^{a₃}` on positive triples
when `a₁, a₂, a₃ ≥ 0` and `a₁ + a₂ + a₃ = 1`. -/
private theorem weighted_geom3_concave {a₁ a₂ a₃ t₁ t₂ s₁ s₂ v₁ v₂ c₁ c₂ : ℝ}
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃) (ha_sum : a₁ + a₂ + a₃ = 1)
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc_sum : c₁ + c₂ = 1) :
    c₁ * (t₁ ^ a₁ * s₁ ^ a₂ * v₁ ^ a₃) + c₂ * (t₂ ^ a₁ * s₂ ^ a₂ * v₂ ^ a₃) ≤
      (c₁ * t₁ + c₂ * t₂) ^ a₁ * (c₁ * s₁ + c₂ * s₂) ^ a₂ * (c₁ * v₁ + c₂ * v₂) ^ a₃ := by
  set t := c₁ * t₁ + c₂ * t₂
  set s := c₁ * s₁ + c₂ * s₂
  set v := c₁ * v₁ + c₂ * v₂
  have hpos_comb : ∀ {x₁ x₂ : ℝ}, 0 < x₁ → 0 < x₂ → 0 < c₁ * x₁ + c₂ * x₂ := fun hx₁ hx₂ => by
    rcases eq_or_lt_of_le hc₁ with rfl | hc₁'
    · have : c₂ = 1 := by linarith
      subst this; simpa using hx₂
    · exact add_pos_of_pos_of_nonneg (mul_pos hc₁' hx₁) (mul_nonneg hc₂ hx₂.le)
  have ht : 0 < t := hpos_comb ht₁ ht₂
  have hs : 0 < s := hpos_comb hs₁ hs₂
  have hv : 0 < v := hpos_comb hv₁ hv₂
  have hR_pos : 0 < t ^ a₁ * s ^ a₂ * v ^ a₃ :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos ht a₁) (Real.rpow_pos_of_pos hs a₂))
      (Real.rpow_pos_of_pos hv a₃)
  have h1 := Real.geom_mean_le_arith_mean3_weighted ha₁ ha₂ ha₃
    (div_nonneg ht₁.le ht.le) (div_nonneg hs₁.le hs.le) (div_nonneg hv₁.le hv.le) ha_sum
  have h2 := Real.geom_mean_le_arith_mean3_weighted ha₁ ha₂ ha₃
    (div_nonneg ht₂.le ht.le) (div_nonneg hs₂.le hs.le) (div_nonneg hv₂.le hv.le) ha_sum
  have hcomb :
      c₁ * ((t₁ / t) ^ a₁ * (s₁ / s) ^ a₂ * (v₁ / v) ^ a₃) +
        c₂ * ((t₂ / t) ^ a₁ * (s₂ / s) ^ a₂ * (v₂ / v) ^ a₃) ≤ 1 := by
    calc
      c₁ * ((t₁ / t) ^ a₁ * (s₁ / s) ^ a₂ * (v₁ / v) ^ a₃) +
          c₂ * ((t₂ / t) ^ a₁ * (s₂ / s) ^ a₂ * (v₂ / v) ^ a₃)
        ≤ c₁ * (a₁ * (t₁ / t) + a₂ * (s₁ / s) + a₃ * (v₁ / v)) +
            c₂ * (a₁ * (t₂ / t) + a₂ * (s₂ / s) + a₃ * (v₂ / v)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hc₁) (mul_le_mul_of_nonneg_left h2 hc₂)
      _ = a₁ * ((c₁ * t₁ + c₂ * t₂) / t) + a₂ * ((c₁ * s₁ + c₂ * s₂) / s) +
            a₃ * ((c₁ * v₁ + c₂ * v₂) / v) := by ring
      _ = a₁ + a₂ + a₃ := by
            rw [div_self ht.ne', div_self hs.ne', div_self hv.ne', mul_one, mul_one, mul_one]
      _ = 1 := ha_sum
  have hdiv :
      (c₁ * (t₁ ^ a₁ * s₁ ^ a₂ * v₁ ^ a₃) + c₂ * (t₂ ^ a₁ * s₂ ^ a₂ * v₂ ^ a₃)) /
          (t ^ a₁ * s ^ a₂ * v ^ a₃) ≤ 1 := by
    have heq :
        (c₁ * (t₁ ^ a₁ * s₁ ^ a₂ * v₁ ^ a₃) + c₂ * (t₂ ^ a₁ * s₂ ^ a₂ * v₂ ^ a₃)) /
            (t ^ a₁ * s ^ a₂ * v ^ a₃) =
          c₁ * ((t₁ / t) ^ a₁ * (s₁ / s) ^ a₂ * (v₁ / v) ^ a₃) +
            c₂ * ((t₂ / t) ^ a₁ * (s₂ / s) ^ a₂ * (v₂ / v) ^ a₃) := by
      rw [Real.div_rpow ht₁.le ht.le, Real.div_rpow hs₁.le hs.le, Real.div_rpow hv₁.le hv.le,
        Real.div_rpow ht₂.le ht.le, Real.div_rpow hs₂.le hs.le, Real.div_rpow hv₂.le hv.le]
      field_simp [(Real.rpow_pos_of_pos ht a₁).ne', (Real.rpow_pos_of_pos hs a₂).ne',
        (Real.rpow_pos_of_pos hv a₃).ne']
    rw [heq]
    exact hcomb
  exact (div_le_one hR_pos).1 hdiv

/-- **Proposition 6.11** ([CodenottiVaradarajan2007], Section 6.4.2, Equations `(6.8)`–`(6.9)`,
p. 150): for strictly positive CES weights `α > 0`, nonnegative endowment `w ≥ 0`, and CES exponent
`-1 ≤ ρ_i < 0`, the transformed demand `σ ↦ cesTransformedDemand α w ρ_i σ g` (`σ_k = √(π_k)`) is a
**convex function** on the positive orthant `{σ : G → ℝ | ∀ k, 0 < σ k}`. -/
theorem convexOn_cesTransformedDemand [Nonempty G] {α w : G → ℝ} {ρ_i : ℝ}
    (hα : ∀ k, 0 < α k) (hw : ∀ k, 0 ≤ w k) (hρ_lo : -1 ≤ ρ_i) (hρ_hi : ρ_i < 0) (g : G) :
    ConvexOn ℝ {σ : G → ℝ | ∀ k, 0 < σ k} (fun σ => cesTransformedDemand α w ρ_i σ g) := by
  have hconv_dom : Convex ℝ {σ : G → ℝ | ∀ k, 0 < σ k} := by
    intro x hx y hy a b ha hb hab k
    rcases eq_or_lt_of_le ha with rfl | ha'
    · obtain rfl : b = 1 := by linarith
      simpa using hy k
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx k)) (mul_nonneg hb (hy k).le)
  refine ⟨hconv_dom, fun σ₁ hσ₁ σ₂ hσ₂ c₁ c₂ hc₁ hc₂ hcsum => ?_⟩
  -- Handle the degenerate zero-endowment case first (`f_{ij} ≡ 0`).
  by_cases hw0 : ∀ k : G, w k = 0
  · have hzero : ∀ σ : G → ℝ, cesTransformedDemand α w ρ_i σ g = 0 := fun σ => by
      simp [cesTransformedDemand_apply, cesDemand_apply, expenditure_eq_sum, hw0]
    simp [hzero]
  push Not at hw0
  obtain ⟨k₀, hk₀_ne⟩ := hw0
  have hk₀_pos : 0 < w k₀ := lt_of_le_of_ne (hw k₀) (Ne.symm hk₀_ne)
  -- Setup exponents matching Equations `(6.8)`–`(6.9)` with `ρ = -1` (`1 - ρ = 2`).
  have h1ρi_pos : 0 < 1 - ρ_i := by linarith
  set q : ℝ := (-2 * ρ_i) / (1 - ρ_i)
  have hq_pos : 0 < q := div_pos (by linarith) h1ρi_pos
  have hq_le1 : q ≤ 1 := (div_le_one h1ρi_pos).2 (by linarith)
  set a₁ : ℝ := 1 / 2
  set a₂ : ℝ := (ρ_i + 1) / (2 * (1 - ρ_i))
  set a₃ : ℝ := (-ρ_i) / (1 - ρ_i)
  have ha₁ : 0 ≤ a₁ := by positivity
  have ha₂ : 0 ≤ a₂ := div_nonneg (by linarith) (by positivity)
  have ha₃ : 0 ≤ a₃ := div_nonneg (by linarith) h1ρi_pos.le
  have ha_sum : a₁ + a₂ + a₃ = 1 := by
    dsimp only [a₁, a₂, a₃]
    field_simp [h1ρi_pos.ne']
    ring
  -- Auxiliary functions `L(σ)` (LHS of (6.8)), `v(σ)` (RHS of (6.9)), and `f(σ)`.
  let β : G → ℝ := fun k => (α k) ^ (1 / (1 - ρ_i))
  have hβ_pos : ∀ k, 0 < β k := fun k => Real.rpow_pos_of_pos (hα k) _
  let L : (G → ℝ) → ℝ := fun σ =>
    (α g) ^ (1 / (2 * (1 - ρ_i))) * (∑ k : G, w k * (σ k) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  let v : (G → ℝ) → ℝ := fun σ => cesUtility β q σ
  -- Algebraic identity `(6.8)`: `L σ = (f σ) ^ a₁ * (σ g) ^ a₂ * (v σ) ^ a₃` for `σ > 0`.
  have hkey : ∀ σ : G → ℝ, (∀ k, 0 < σ k) →
      0 < cesTransformedDemand α w ρ_i σ g ∧ 0 < v σ ∧
        L σ = (cesTransformedDemand α w ρ_i σ g) ^ a₁ * (σ g) ^ a₂ * (v σ) ^ a₃ := by
    intro σ hσ
    have hσ2_pos : ∀ k, 0 < (σ k) ^ 2 := fun k => sq_pos_of_pos (hσ k)
    have hinc_pos : 0 < expenditure (fun k => (σ k) ^ 2) w := by
      rw [expenditure_eq_sum]
      exact (sum_pos_iff_of_nonneg fun k _ => mul_nonneg (hσ2_pos k).le (hw k)).2
        ⟨k₀, mem_univ k₀, mul_pos (hσ2_pos k₀) hk₀_pos⟩
    set D : ℝ := ∑ k : G, (α k) ^ (1 / (1 - ρ_i)) * ((σ k) ^ 2) ^ (-ρ_i / (1 - ρ_i))
    have hD_pos : 0 < D := sum_pos
      (fun k _ => mul_pos (Real.rpow_pos_of_pos (hα k) _) (Real.rpow_pos_of_pos (hσ2_pos k) _))
      univ_nonempty
    have hf_pos : 0 < cesTransformedDemand α w ρ_i σ g := by
      rw [cesTransformedDemand_apply, cesDemand_apply]
      exact mul_pos (hσ g) (mul_pos
        (div_pos (Real.rpow_pos_of_pos (hα g) _) (Real.rpow_pos_of_pos (hσ2_pos g) _))
        (div_pos hinc_pos hD_pos))
    have hD_eq_sum : D = ∑ k : G, β k * (σ k) ^ q := by
      dsimp only [D, β]
      refine sum_congr rfl fun k _ => ?_
      congr 1
      rw [← Real.rpow_natCast (σ k) 2, ← Real.rpow_mul (hσ k).le]
      congr 1
      dsimp only [q]; push_cast; ring
    have hv_eq : v σ = D ^ (1 / q) := by
      dsimp only [v]
      rw [cesUtility_of_pos_exp hq_pos, ← hD_eq_sum]
    have hv_pos : 0 < v σ := by rw [hv_eq]; exact Real.rpow_pos_of_pos hD_pos _
    have hv_pow : (v σ) ^ a₃ = D ^ (1 / 2 : ℝ) := by
      rw [hv_eq, ← Real.rpow_mul hD_pos.le]
      congr 1
      dsimp only [q, a₃]
      field_simp [h1ρi_pos.ne', hρ_hi.ne]
    have hσg_pow : σ g / ((σ g) ^ 2) ^ (1 / (1 - ρ_i)) = (σ g) ^ (-((ρ_i + 1) / (1 - ρ_i))) := by
      rw [← Real.rpow_natCast (σ g) 2, ← Real.rpow_mul (hσ g).le]
      calc σ g / (σ g) ^ ((2 : ℕ) * (1 / (1 - ρ_i)))
          = (σ g) ^ (1 : ℝ) / (σ g) ^ ((2 : ℕ) * (1 / (1 - ρ_i))) := by rw [Real.rpow_one]
        _ = (σ g) ^ (1 - (2 : ℕ) * (1 / (1 - ρ_i))) := (Real.rpow_sub (hσ g) _ _).symm
        _ = (σ g) ^ (-((ρ_i + 1) / (1 - ρ_i))) := by
            congr 1; push_cast; field_simp [h1ρi_pos.ne']; ring
    have hf_rewrite : cesTransformedDemand α w ρ_i σ g =
        (α g) ^ (1 / (1 - ρ_i)) * (σ g) ^ (-((ρ_i + 1) / (1 - ρ_i))) *
          (expenditure (fun k => (σ k) ^ 2) w / D) := by
      rw [cesTransformedDemand_apply, cesDemand_apply]
      change σ g * (((α g) ^ (1 / (1 - ρ_i)) / ((σ g) ^ 2) ^ (1 / (1 - ρ_i))) *
          (expenditure (fun k => (σ k) ^ 2) w / D)) = _
      rw [← hσg_pow]
      ring
    have hinc_eq : expenditure (fun k => (σ k) ^ 2) w = ∑ k : G, w k * (σ k) ^ (2 : ℝ) := by
      rw [expenditure_eq_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [Real.rpow_two, mul_comm]
    refine ⟨hf_pos, hv_pos, ?_⟩
    rw [hf_rewrite, hv_pow]
    have h1 : ((α g) ^ (1 / (1 - ρ_i)) * (σ g) ^ (-((ρ_i + 1) / (1 - ρ_i))) *
        (expenditure (fun k => (σ k) ^ 2) w / D)) ^ a₁ =
        (α g) ^ (1 / (2 * (1 - ρ_i))) * (σ g) ^ (-a₂) *
          ((expenditure (fun k => (σ k) ^ 2) w) ^ (1 / 2 : ℝ) / D ^ (1 / 2 : ℝ)) := by
      rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hα g).le _) (Real.rpow_nonneg (hσ g).le _))
          (div_nonneg hinc_pos.le hD_pos.le),
        Real.mul_rpow (Real.rpow_nonneg (hα g).le _) (Real.rpow_nonneg (hσ g).le _),
        Real.div_rpow hinc_pos.le hD_pos.le,
        ← Real.rpow_mul (hα g).le, ← Real.rpow_mul (hσ g).le]
      have he1 : 1 / (1 - ρ_i) * a₁ = 1 / (2 * (1 - ρ_i)) := by
        dsimp only [a₁]; field_simp [h1ρi_pos.ne']
      have he2 : -((ρ_i + 1) / (1 - ρ_i)) * a₁ = -a₂ := by
        dsimp only [a₁, a₂]; field_simp [h1ρi_pos.ne']
      rw [he1, he2]
    rw [h1]
    have hσ_cancel : (σ g) ^ (-a₂) * (σ g) ^ a₂ = 1 := by
      rw [← Real.rpow_add (hσ g), neg_add_cancel, Real.rpow_zero]
    dsimp only [L]
    rw [← hinc_eq]
    have hD_half_ne : D ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hD_pos _).ne'
    calc (α g) ^ (1 / (2 * (1 - ρ_i))) * expenditure (fun k => (σ k) ^ 2) w ^ (1 / 2 : ℝ)
        = (α g) ^ (1 / (2 * (1 - ρ_i))) * 1 *
            (expenditure (fun k => (σ k) ^ 2) w ^ (1 / 2 : ℝ) / D ^ (1 / 2 : ℝ) *
              D ^ (1 / 2 : ℝ)) := by rw [mul_one, div_mul_cancel₀ _ hD_half_ne]
      _ = (α g) ^ (1 / (2 * (1 - ρ_i))) * (σ g) ^ (-a₂) *
            (expenditure (fun k => (σ k) ^ 2) w ^ (1 / 2 : ℝ) / D ^ (1 / 2 : ℝ)) *
            (σ g) ^ a₂ * D ^ (1 / 2 : ℝ) := by rw [← hσ_cancel]; ring
  set σ := c₁ • σ₁ + c₂ • σ₂
  have hσ_pos : ∀ k, 0 < σ k := hconv_dom hσ₁ hσ₂ hc₁ hc₂ hcsum
  obtain ⟨hf₁_pos, hv₁_pos, hL₁⟩ := hkey σ₁ hσ₁
  obtain ⟨hf₂_pos, hv₂_pos, hL₂⟩ := hkey σ₂ hσ₂
  obtain ⟨hf_pos, hv_pos, hL⟩ := hkey σ hσ_pos
  -- Step 1: `L` is convex on `ℝ_+^G` (Minkowski for `p = 2`).
  have hL_conv : L σ ≤ c₁ * L σ₁ + c₂ * L σ₂ := by
    have hlp := (convexOn_weighted_lpNorm hw (by norm_num : (1 : ℝ) ≤ 2)).2
      (fun k => (hσ₁ k).le) (fun k => (hσ₂ k).le) hc₁ hc₂ hcsum
    simp only [smul_eq_mul] at hlp
    dsimp only [L]
    have hmul := mul_le_mul_of_nonneg_left hlp
      (Real.rpow_nonneg (hα g).le (1 / (2 * (1 - ρ_i))))
    linarith
  -- Step 2: `v` is concave on `ℝ_+^G` (CES utility with `0 < q ≤ 1`).
  have hv_conc : c₁ * v σ₁ + c₂ * v σ₂ ≤ v σ := by
    simpa only [smul_eq_mul] using
      (concaveOn_cesUtility hβ_pos hq_le1 hq_pos.ne').2
        (fun k => (hσ₁ k).le) (fun k => (hσ₂ k).le) hc₁ hc₂ hcsum
  -- Step 3: `t^{a₁} s^{a₂} v^{a₃}` is concave and nondecreasing in `v`.
  set t := c₁ * cesTransformedDemand α w ρ_i σ₁ g + c₂ * cesTransformedDemand α w ρ_i σ₂ g
  have hgeom := weighted_geom3_concave ha₁ ha₂ ha₃ ha_sum hf₁_pos hf₂_pos (hσ₁ g) (hσ₂ g)
    hv₁_pos hv₂_pos hc₁ hc₂ hcsum
  have hv_comb_nn : 0 ≤ c₁ * v σ₁ + c₂ * v σ₂ :=
    add_nonneg (mul_nonneg hc₁ hv₁_pos.le) (mul_nonneg hc₂ hv₂_pos.le)
  have hmono_v :
      t ^ a₁ * (σ g) ^ a₂ * (c₁ * v σ₁ + c₂ * v σ₂) ^ a₃ ≤
        t ^ a₁ * (σ g) ^ a₂ * (v σ) ^ a₃ := by
    have ht_nn : 0 ≤ t := add_nonneg (mul_nonneg hc₁ hf₁_pos.le) (mul_nonneg hc₂ hf₂_pos.le)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv_comb_nn hv_conc ha₃)
      (mul_nonneg (Real.rpow_nonneg ht_nn a₁) (Real.rpow_nonneg (hσ_pos g).le a₂))
  -- Step 4: Combine and cancel `(σ g) ^ a₂ * (v σ) ^ a₃ > 0`, then square (`a₁ = 1/2`).
  have hchain : (cesTransformedDemand α w ρ_i σ g) ^ a₁ * (σ g) ^ a₂ * (v σ) ^ a₃ ≤
      t ^ a₁ * (σ g) ^ a₂ * (v σ) ^ a₃ := by
    have hσg_eq : σ g = c₁ * σ₁ g + c₂ * σ₂ g := by simp [σ]
    rw [← hL]
    calc L σ ≤ c₁ * L σ₁ + c₂ * L σ₂ := hL_conv
      _ = c₁ * ((cesTransformedDemand α w ρ_i σ₁ g) ^ a₁ * (σ₁ g) ^ a₂ * (v σ₁) ^ a₃) +
            c₂ * ((cesTransformedDemand α w ρ_i σ₂ g) ^ a₁ * (σ₂ g) ^ a₂ * (v σ₂) ^ a₃) := by
          rw [hL₁, hL₂]
      _ ≤ t ^ a₁ * (σ g) ^ a₂ * (c₁ * v σ₁ + c₂ * v σ₂) ^ a₃ := by
          rw [hσg_eq]; exact hgeom
      _ ≤ t ^ a₁ * (σ g) ^ a₂ * (v σ) ^ a₃ := hmono_v
  have hfac_pos : 0 < (σ g) ^ a₂ * (v σ) ^ a₃ :=
    mul_pos (Real.rpow_pos_of_pos (hσ_pos g) a₂) (Real.rpow_pos_of_pos hv_pos a₃)
  have hpow_le : (cesTransformedDemand α w ρ_i σ g) ^ a₁ ≤ t ^ a₁ :=
    le_of_mul_le_mul_right (by simpa only [mul_assoc] using hchain) hfac_pos
  have hsq := Real.rpow_le_rpow (Real.rpow_nonneg hf_pos.le a₁) hpow_le (by norm_num : (0 : ℝ) ≤ 2)
  have ht_nn : 0 ≤ t := add_nonneg (mul_nonneg hc₁ hf₁_pos.le) (mul_nonneg hc₂ hf₂_pos.le)
  rw [← Real.rpow_mul hf_pos.le, ← Real.rpow_mul ht_nn] at hsq
  have ha2 : a₁ * 2 = 1 := by dsimp only [a₁]; norm_num
  rw [ha2, Real.rpow_one, Real.rpow_one] at hsq
  simpa only [smul_eq_mul] using hsq

end CESProperties

/-! ### CES Arrow–Debreu exchange markets and convex feasibility for `-1 ≤ ρ_i < 0` -/

/-- A **CES Arrow–Debreu exchange economy** ([CodenottiVaradarajan2007], Section 6.4.2, p. 149):
each trader `i : I` has nonnegative endowment `endowment i`, strictly positive CES weights
`weight i`, and substitution parameter `rho i < 1` with `rho i ≠ 0`. -/
structure CESExchangeMarket (I G : Type*) where
  /-- Initial endowment `endowment i g` of good `g` held by trader `i`. -/
  endowment : I → G → ℝ
  /-- CES utility weights `weight i g > 0`. -/
  weight : I → G → ℝ
  /-- CES substitution parameter `rho i ∈ (-∞, 1) \ {0}` of trader `i`. -/
  rho : I → ℝ
  /-- Initial endowments are nonnegative. -/
  endowment_nonneg : ∀ (i : I) (g : G), 0 ≤ endowment i g
  /-- CES utility weights are strictly positive. -/
  weight_pos : ∀ (i : I) (g : G), 0 < weight i g
  /-- Each trader's CES parameter satisfies `rho i < 1`. -/
  rho_lt_one : ∀ i : I, rho i < 1
  /-- Each trader's CES parameter is nonzero. -/
  rho_ne_zero : ∀ i : I, rho i ≠ 0

namespace CESExchangeMarket

variable {I G : Type*} [Fintype I] [Fintype G] (E : CESExchangeMarket I G)

/-- View `E` as a general `ExchangeMarket I G` with `cesUtility (E.weight i) (E.rho i)`. -/
noncomputable def toExchangeMarket : ExchangeMarket I G where
  endowment := E.endowment
  utility i := cesUtility (E.weight i) (E.rho i)
  endowment_nonneg := E.endowment_nonneg

omit [Fintype I] in
@[simp] theorem toExchangeMarket_endowment : E.toExchangeMarket.endowment = E.endowment := by rfl

omit [Fintype I] in
@[simp] theorem toExchangeMarket_utility (i : I) :
    E.toExchangeMarket.utility i = cesUtility (E.weight i) (E.rho i) := by rfl

/-- Single-valued aggregate excess-demand function `Z(p)_g = ∑_i x_{ig}(p) - ∑_i w_{ig}` of CES
exchange economy `E` via Equation `(6.7)` ([CodenottiVaradarajan2007], Section 6.4.2, p. 149). -/
noncomputable def excessDemandFn (p : G → ℝ) (g : G) : ℝ :=
  (∑ i : I, cesDemand (E.weight i) (E.rho i) p (expenditure p (E.endowment i)) g) -
    E.toExchangeMarket.totalSupply g

theorem excessDemandFn_eq (p : G → ℝ) (g : G) :
    E.excessDemandFn p g =
      (∑ i : I, cesDemand (E.weight i) (E.rho i) p (expenditure p (E.endowment i)) g) -
        E.toExchangeMarket.totalSupply g := by rfl

theorem isHomogeneousDegZero_excessDemandFn : IsHomogeneousDegZero E.excessDemandFn := by
  intro c hc p hp
  funext g
  simp only [excessDemandFn_eq]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have h1ρ : 1 - E.rho i ≠ 0 := by linarith [E.rho_lt_one i]
  simp only [cesDemand_apply, expenditure_smul_left, Pi.smul_apply, smul_eq_mul]
  have hnum : (c * p g) ^ (1 / (1 - E.rho i)) =
      c ^ (1 / (1 - E.rho i)) * (p g) ^ (1 / (1 - E.rho i)) :=
    Real.mul_rpow hc.le (hp g).le
  have hden : ∑ k : G, (E.weight i k) ^ (1 / (1 - E.rho i)) *
        (c * p k) ^ (-E.rho i / (1 - E.rho i)) =
      c ^ (-E.rho i / (1 - E.rho i)) *
        ∑ k : G, (E.weight i k) ^ (1 / (1 - E.rho i)) * (p k) ^ (-E.rho i / (1 - E.rho i)) := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Real.mul_rpow hc.le (hp k).le]; ring
  rw [hnum, hden]
  have hc_pow : c ^ (1 / (1 - E.rho i)) * c ^ (-E.rho i / (1 - E.rho i)) = c := by
    rw [← Real.rpow_add hc]
    have hexp : 1 / (1 - E.rho i) + -E.rho i / (1 - E.rho i) = 1 := by field_simp [h1ρ]; ring
    rw [hexp, Real.rpow_one]
  have h1ne : c ^ (1 / (1 - E.rho i)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  have h2ne : c ^ (-E.rho i / (1 - E.rho i)) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
  calc (E.weight i g) ^ (1 / (1 - E.rho i)) /
          (c ^ (1 / (1 - E.rho i)) * (p g) ^ (1 / (1 - E.rho i))) *
        (c * expenditure p (E.endowment i) /
          (c ^ (-E.rho i / (1 - E.rho i)) *
            ∑ k : G, (E.weight i k) ^ (1 / (1 - E.rho i)) * (p k) ^ (-E.rho i / (1 - E.rho i))))
      = ((E.weight i g) ^ (1 / (1 - E.rho i)) / (p g) ^ (1 / (1 - E.rho i))) *
          (expenditure p (E.endowment i) /
            ∑ k : G, (E.weight i k) ^ (1 / (1 - E.rho i)) *
              (p k) ^ (-E.rho i / (1 - E.rho i))) *
          (c / (c ^ (1 / (1 - E.rho i)) * c ^ (-E.rho i / (1 - E.rho i)))) := by ring
    _ = ((E.weight i g) ^ (1 / (1 - E.rho i)) / (p g) ^ (1 / (1 - E.rho i))) *
          (expenditure p (E.endowment i) /
            ∑ k : G, (E.weight i k) ^ (1 / (1 - E.rho i)) *
              (p k) ^ (-E.rho i / (1 - E.rho i))) := by
        rw [hc_pow, div_self hc.ne', mul_one]

theorem satisfiesWalrasLaw_excessDemandFn [Nonempty G] : SatisfiesWalrasLaw E.excessDemandFn := by
  intro p hp
  rw [expenditure_eq_sum]
  have hterm : ∀ g : G, p g * E.excessDemandFn p g =
      (∑ i : I, p g * cesDemand (E.weight i) (E.rho i) p (expenditure p (E.endowment i)) g) -
        p g * E.toExchangeMarket.totalSupply g := fun g => by
    rw [excessDemandFn_eq, mul_sub, mul_sum]
  simp_rw [hterm, sum_sub_distrib]
  rw [sum_comm]
  have hsum : (∑ i : I, ∑ g : G,
        p g * cesDemand (E.weight i) (E.rho i) p (expenditure p (E.endowment i)) g) =
      ∑ i : I, expenditure p (E.endowment i) :=
    sum_congr rfl fun i _ =>
      (expenditure_eq_sum _ _).symm.trans
        (expenditure_cesDemand (E.weight_pos i) (E.rho_lt_one i) hp _)
  rw [hsum]
  have hinc := E.toExchangeMarket.sum_income p
  simp only [ExchangeMarket.income_eq, toExchangeMarket_endowment, expenditure_eq_sum] at hinc ⊢
  linarith

/-- Because CES demand `(6.7)` is unique, a positive price vector `p > 0` and allocation `x` form
a competitive equilibrium of `E.toExchangeMarket` if and only if `x` equals the closed-form CES
demand profile and `IsWalrasianEquilibrium E.excessDemandFn p`. -/
theorem isCompetitiveEquilibrium_iff_isWalrasianEquilibrium [Nonempty G]
    {x : I → G → ℝ} {p : G → ℝ} (hp : ∀ g, 0 < p g) :
    E.toExchangeMarket.IsCompetitiveEquilibrium x p ↔
      (∀ i, x i = cesDemand (E.weight i) (E.rho i) p (expenditure p (E.endowment i))) ∧
        IsWalrasianEquilibrium E.excessDemandFn p := by
  have hp_nn : ∀ g, 0 ≤ p g := fun g => (hp g).le
  have hdem_iff : ∀ i, x i ∈ E.toExchangeMarket.demandSet p i ↔
      x i = cesDemand (E.weight i) (E.rho i) p (expenditure p (E.endowment i)) := fun i => by
    rw [ExchangeMarket.mem_demandSet, toExchangeMarket_utility, ExchangeMarket.income_eq,
      toExchangeMarket_endowment,
      demandSet_cesUtility_eq (E.weight_pos i) (E.rho_lt_one i) (E.rho_ne_zero i) hp
        (expenditure_nonneg hp_nn (E.endowment_nonneg i)),
      Set.mem_singleton_iff]
  constructor
  · intro heq
    have hx_eq : ∀ i, x i = cesDemand (E.weight i) (E.rho i) p (expenditure p (E.endowment i)) :=
      fun i => (hdem_iff i).1 (heq.2.1 i)
    refine ⟨hx_eq, hp, fun g => ?_⟩
    have hclr := heq.2.2.1 g
    rw [ExchangeMarket.excessDemand_eq] at hclr
    simpa only [excessDemandFn_eq, ← hx_eq] using hclr
  · rintro ⟨hx_eq, heq⟩
    have hz0 := E.satisfiesWalrasLaw_excessDemandFn.eq_zero_of_isWalrasianEquilibrium heq
    have hex_eq : ∀ g, E.toExchangeMarket.excessDemand x g = E.excessDemandFn p g := fun g => by
      simp only [ExchangeMarket.excessDemand_eq, excessDemandFn_eq, hx_eq]
    refine ⟨hp_nn, fun i => (hdem_iff i).2 (hx_eq i),
      fun g => le_of_eq ((hex_eq g).trans (congrFun hz0 g)),
      fun g => by rw [hex_eq, hz0, Pi.zero_apply, mul_zero]⟩

/-- Transformed equilibrium price set `{σ ∈ ℝ_{++}^G | ∀ g, ∑_i f_{ig}(σ) ≤ σ_g ∑_i w_{ig}}` under
`σ_g = √(π_g)` ([CodenottiVaradarajan2007], Section 6.4.2, pp. 149–150). -/
@[expose] def transformedEquilibriumSet : Set (G → ℝ) :=
  {σ : G → ℝ | (∀ g, 0 < σ g) ∧
    ∀ g : G, ∑ i : I, cesTransformedDemand (E.weight i) (E.endowment i) (E.rho i) σ g ≤
      σ g * E.toExchangeMarket.totalSupply g}

/-- Equivalence between `σ ∈ E.transformedEquilibriumSet` and `IsWalrasianEquilibrium
E.excessDemandFn (fun k => (σ k) ^ 2)` ([CodenottiVaradarajan2007], Section 6.4.2, p. 149). -/
theorem isWalrasianEquilibrium_sq_iff {σ : G → ℝ} (hσ : ∀ g, 0 < σ g) :
    IsWalrasianEquilibrium E.excessDemandFn (fun k => (σ k) ^ 2) ↔
      σ ∈ E.transformedEquilibriumSet := by
  have hσ2 : ∀ g, 0 < (σ g) ^ 2 := fun g => sq_pos_of_pos (hσ g)
  refine ⟨fun h => ⟨hσ, fun g => ?_⟩, fun h => ⟨hσ2, fun g => ?_⟩⟩
  · have hle : ∑ i : I, cesDemand (E.weight i) (E.rho i) (fun k => (σ k) ^ 2)
        (expenditure (fun k => (σ k) ^ 2) (E.endowment i)) g ≤ E.toExchangeMarket.totalSupply g :=
      sub_nonpos.1 (by simpa only [excessDemandFn_eq] using h.2 g)
    simpa only [cesTransformedDemand_apply, ← mul_sum] using
      mul_le_mul_of_nonneg_left hle (hσ g).le
  · rw [excessDemandFn_eq, sub_nonpos]
    have hmul : σ g * ∑ i : I, cesDemand (E.weight i) (E.rho i) (fun k => (σ k) ^ 2)
        (expenditure (fun k => (σ k) ^ 2) (E.endowment i)) g ≤
        σ g * E.toExchangeMarket.totalSupply g := by
      simpa only [cesTransformedDemand_apply, ← mul_sum] using h.2 g
    exact le_of_mul_le_mul_left hmul (hσ g)

/-- **Convex feasibility characterization of CES exchange equilibria for `-1 ≤ ρ_i < 0`**
([CodenottiVaradarajan2007], Section 6.4.2, Proposition 6.11 corollary, pp. 149–150): when every
trader's CES parameter lies in `[-1, 0)`, the transformed equilibrium price set
`E.transformedEquilibriumSet` is convex (and hence preconnected). -/
theorem convex_setOf_transformedEquilibrium [Nonempty G]
    (hρ_lo : ∀ i : I, -1 ≤ E.rho i) (hρ_hi : ∀ i : I, E.rho i < 0) :
    Convex ℝ E.transformedEquilibriumSet := by
  intro σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab
  have hσ_pos : ∀ g, 0 < (a • σ₁ + b • σ₂) g := fun g => by
    rcases eq_or_lt_of_le ha with rfl | ha'
    · obtain rfl : b = 1 := by linarith
      simpa using hσ₂.1 g
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hσ₁.1 g)) (mul_nonneg hb (hσ₂.1 g).le)
  refine ⟨hσ_pos, fun g => ?_⟩
  calc
    ∑ i : I, cesTransformedDemand (E.weight i) (E.endowment i) (E.rho i) (a • σ₁ + b • σ₂) g
      ≤ ∑ i : I, (a * cesTransformedDemand (E.weight i) (E.endowment i) (E.rho i) σ₁ g +
          b * cesTransformedDemand (E.weight i) (E.endowment i) (E.rho i) σ₂ g) :=
          sum_le_sum fun i _ => by
            simpa only [smul_eq_mul] using
              (convexOn_cesTransformedDemand (E.weight_pos i) (E.endowment_nonneg i)
                (hρ_lo i) (hρ_hi i) g).2 hσ₁.1 hσ₂.1 ha hb hab
    _ = a * (∑ i : I, cesTransformedDemand (E.weight i) (E.endowment i) (E.rho i) σ₁ g) +
          b * (∑ i : I, cesTransformedDemand (E.weight i) (E.endowment i) (E.rho i) σ₂ g) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ a * (σ₁ g * E.toExchangeMarket.totalSupply g) +
          b * (σ₂ g * E.toExchangeMarket.totalSupply g) :=
          add_le_add (mul_le_mul_of_nonneg_left (hσ₁.2 g) ha)
            (mul_le_mul_of_nonneg_left (hσ₂.2 g) hb)
    _ = (a • σ₁ + b • σ₂) g * E.toExchangeMarket.totalSupply g := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

end CESExchangeMarket

/-! ### §6.5.1 Multiple disconnected equilibria for `ρ < -1` (Gjerstad's example) -/

section DisconnectedCES

/-- **Gjerstad's 2-trader, 2-good CES exchange economy** ([CodenottiVaradarajan2007],
Section 6.5.1, p. 151): trader `0` holds endowment `(1, 0)` and utility `((a x)^ρ + y^ρ)^{1/ρ}`
(weights `![a^ρ, 1]`), while trader `1` holds endowment `(0, 1)` and utility
`((x / a)^ρ + y^ρ)^{1/ρ}` (weights `![a^{-ρ}, 1]`). -/
noncomputable def gjerstadMarket (ρ a : ℝ) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) (ha : 0 < a) :
    CESExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![1, 0], ![0, 1]]
  weight := ![![a ^ ρ, 1], ![a ^ (-ρ), 1]]
  rho := fun _ => ρ
  endowment_nonneg := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  weight_pos := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨Real.rpow_pos_of_pos ha ρ, zero_lt_one⟩, ⟨Real.rpow_pos_of_pos ha (-ρ), zero_lt_one⟩⟩
  rho_lt_one _ := hρ1
  rho_ne_zero _ := hρ0

@[simp] theorem gjerstadMarket_endowment (ρ a : ℝ) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) (ha : 0 < a) :
    (gjerstadMarket ρ a hρ1 hρ0 ha).endowment = ![![1, 0], ![0, 1]] := by rfl

@[simp] theorem gjerstadMarket_weight (ρ a : ℝ) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) (ha : 0 < a) :
    (gjerstadMarket ρ a hρ1 hρ0 ha).weight = ![![a ^ ρ, 1], ![a ^ (-ρ), 1]] := by rfl

@[simp] theorem gjerstadMarket_rho (ρ a : ℝ) (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) (ha : 0 < a) (i : Fin 2) :
    (gjerstadMarket ρ a hρ1 hρ0 ha).rho i = ρ := by rfl

/-- Closed-form sign formula for the excess demand of good `0` in `gjerstadMarket ρ a` at price
`![p, 1 - p]` (`0 < p < 1`): writing `γ = -ρ / (1 - ρ)`, `b = a ^ γ`, and `t = (1 - p) / p`,
`Z_0(p, 1 - p) = b * t^γ * (b * (t - 1) - (t^γ - t^(1 - γ))) / ((1 + b * t^γ) * (b + t^γ))`. -/
private theorem gjerstadMarket_excessDemand_zero {ρ a p : ℝ}
    (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) (ha : 0 < a) (hp0 : 0 < p) (hp1 : p < 1) :
    (gjerstadMarket ρ a hρ1 hρ0 ha).excessDemandFn ![p, 1 - p] 0 =
      a ^ (-ρ / (1 - ρ)) * ((1 - p) / p) ^ (-ρ / (1 - ρ)) *
        (a ^ (-ρ / (1 - ρ)) * ((1 - p) / p - 1) -
          (((1 - p) / p) ^ (-ρ / (1 - ρ)) - ((1 - p) / p) ^ (1 - -ρ / (1 - ρ)))) /
        ((1 + a ^ (-ρ / (1 - ρ)) * ((1 - p) / p) ^ (-ρ / (1 - ρ))) *
          (a ^ (-ρ / (1 - ρ)) + ((1 - p) / p) ^ (-ρ / (1 - ρ)))) := by
  set γ := -ρ / (1 - ρ)
  set b := a ^ γ
  set t := (1 - p) / p
  have h1ρ : 0 < 1 - ρ := by linarith
  have hq0 : 0 < 1 - p := by linarith
  have ht_pos : 0 < t := div_pos hq0 hp0
  have hb_pos : 0 < b := Real.rpow_pos_of_pos ha γ
  have htγ_pos : 0 < t ^ γ := Real.rpow_pos_of_pos ht_pos γ
  have hden1 : 0 < 1 + b * t ^ γ := by positivity
  have hden2 : 0 < b + t ^ γ := by positivity
  have ha_pow1 : (a ^ ρ) ^ (1 / (1 - ρ)) = b⁻¹ := by
    dsimp only [b, γ]
    rw [← Real.rpow_mul ha.le, ← Real.rpow_neg ha.le]
    congr 1; ring
  have ha_pow2 : (a ^ (-ρ)) ^ (1 / (1 - ρ)) = b := by
    dsimp only [b, γ]
    rw [← Real.rpow_mul ha.le]
    congr 1; ring
  have h1_sub_γ : 1 - γ = 1 / (1 - ρ) := by
    dsimp only [γ]; field_simp [h1ρ.ne']; ring
  have hp_pow : p / p ^ (1 / (1 - ρ)) = p ^ γ := by
    calc p / p ^ (1 / (1 - ρ))
        = p ^ (1 : ℝ) / p ^ (1 / (1 - ρ)) := by rw [Real.rpow_one]
      _ = p ^ (1 - 1 / (1 - ρ)) := (Real.rpow_sub hp0 _ _).symm
      _ = p ^ γ := by congr 1; linarith
  have hqp_pow : (1 - p) ^ γ / p ^ γ = t ^ γ := by
    rw [← Real.div_rpow hq0.le hp0.le]
  have hx0 :
      cesDemand ![a ^ ρ, 1] ρ ![p, 1 - p] (expenditure ![p, 1 - p] ![1, 0]) 0 =
        1 / (1 + b * t ^ γ) := by
    simp only [cesDemand_apply, expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, add_zero, Real.one_rpow, one_mul, ha_pow1]
    change (b⁻¹ / p ^ (1 / (1 - ρ))) * (p / (b⁻¹ * p ^ γ + (1 - p) ^ γ)) = 1 / (1 + b * t ^ γ)
    have hnum : b⁻¹ / p ^ (1 / (1 - ρ)) * p = b⁻¹ * p ^ γ := by
      rw [div_mul_eq_mul_div, mul_div_assoc, hp_pow]
    have hD_eq : b⁻¹ * p ^ γ + (1 - p) ^ γ = b⁻¹ * p ^ γ * (1 + b * t ^ γ) := by
      rw [mul_add, mul_one, ← hqp_pow]
      field_simp [hb_pos.ne', (Real.rpow_pos_of_pos hp0 γ).ne']
    rw [← mul_div_assoc, hnum, hD_eq]
    field_simp [hb_pos.ne', (Real.rpow_pos_of_pos hp0 γ).ne', hden1.ne']
  have hx1 :
      cesDemand ![a ^ (-ρ), 1] ρ ![p, 1 - p] (expenditure ![p, 1 - p] ![0, 1]) 0 =
        b * t / (b + t ^ γ) := by
    simp only [cesDemand_apply, expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_one, mul_zero, zero_add, Real.one_rpow, one_mul, ha_pow2]
    change (b / p ^ (1 / (1 - ρ))) * ((1 - p) / (b * p ^ γ + (1 - p) ^ γ)) = b * t / (b + t ^ γ)
    have hnum : b / p ^ (1 / (1 - ρ)) * (1 - p) = b * t * p ^ γ := by
      have : (1 - p) / p ^ (1 / (1 - ρ)) = t * p ^ γ := by
        dsimp only [t]
        rw [div_mul_eq_mul_div, ← hp_pow]
        field_simp [hp0.ne', (Real.rpow_pos_of_pos hp0 (1 / (1 - ρ))).ne']
      calc b / p ^ (1 / (1 - ρ)) * (1 - p)
          = b * ((1 - p) / p ^ (1 / (1 - ρ))) := by ring
        _ = b * t * p ^ γ := by rw [this]; ring
    have hD_eq : b * p ^ γ + (1 - p) ^ γ = p ^ γ * (b + t ^ γ) := by
      rw [mul_add, ← hqp_pow]
      field_simp [(Real.rpow_pos_of_pos hp0 γ).ne']
    rw [← mul_div_assoc, hnum, hD_eq]
    field_simp [(Real.rpow_pos_of_pos hp0 γ).ne', hden2.ne']
  have hZ : (gjerstadMarket ρ a hρ1 hρ0 ha).excessDemandFn ![p, 1 - p] 0 =
      1 / (1 + b * t ^ γ) + b * t / (b + t ^ γ) - 1 := by
    simp only [CESExchangeMarket.excessDemandFn_eq, ExchangeMarket.totalSupply_eq_sum,
      CESExchangeMarket.toExchangeMarket_endowment, gjerstadMarket, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    rw [hx0, hx1]
  rw [hZ]
  have ht_mul1 : t ^ γ * t ^ (1 - γ) = t := by
    rw [← Real.rpow_add ht_pos, add_sub_cancel, Real.rpow_one]
  field_simp [hden1.ne', hden2.ne']
  linear_combination -b * ht_mul1

/-- Equilibrium characterization of `![p, 1 - p]` (`0 < p < 1`) in `gjerstadMarket ρ a`: by
Walras's law it holds if and only if `b * (t - 1) = t ^ γ - t ^ (1 - γ)` where `t = (1 - p) / p`,
`γ = -ρ / (1 - ρ)`, and `b = a ^ γ`. -/
private theorem gjerstadMarket_isWalrasianEquilibrium_iff {ρ a p : ℝ}
    (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) (ha : 0 < a) (hp0 : 0 < p) (hp1 : p < 1) :
    IsWalrasianEquilibrium (gjerstadMarket ρ a hρ1 hρ0 ha).excessDemandFn ![p, 1 - p] ↔
      a ^ (-ρ / (1 - ρ)) * ((1 - p) / p - 1) =
        ((1 - p) / p) ^ (-ρ / (1 - ρ)) - ((1 - p) / p) ^ (1 - -ρ / (1 - ρ)) := by
  set γ := -ρ / (1 - ρ)
  set b := a ^ γ
  set t := (1 - p) / p
  set E := gjerstadMarket ρ a hρ1 hρ0 ha
  have hp_pos : ∀ g : Fin 2, 0 < (![p, 1 - p] : Fin 2 → ℝ) g := by
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hp0, by linarith⟩
  rw [E.satisfiesWalrasLaw_excessDemandFn.isWalrasianEquilibrium_iff_eq_zero,
    and_iff_right hp_pos]
  have hZ0_iff : E.excessDemandFn ![p, 1 - p] = 0 ↔ E.excessDemandFn ![p, 1 - p] 0 = 0 := by
    refine ⟨fun h => congrFun h 0, fun h0 => ?_⟩
    have hw := E.satisfiesWalrasLaw_excessDemandFn hp_pos
    simp only [expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      h0, mul_zero, zero_add] at hw
    have h1 : E.excessDemandFn ![p, 1 - p] 1 = 0 :=
      (mul_eq_zero.1 hw).resolve_left (by linarith)
    funext g; fin_cases g <;> assumption
  rw [hZ0_iff, gjerstadMarket_excessDemand_zero hρ1 hρ0 ha hp0 hp1]
  have hb_pos : 0 < b := Real.rpow_pos_of_pos ha γ
  have ht_pos : 0 < t := div_pos (by linarith) hp0
  have htγ_pos : 0 < t ^ γ := Real.rpow_pos_of_pos ht_pos γ
  have hden_pos : 0 < (1 + b * t ^ γ) * (b + t ^ γ) := by positivity
  rw [div_eq_zero_iff]
  have hden_ne : (1 + b * t ^ γ) * (b + t ^ γ) ≠ 0 := hden_pos.ne'
  have hbt_ne : b * t ^ γ ≠ 0 := (mul_pos hb_pos htγ_pos).ne'
  change b * t ^ γ * (b * (t - 1) - (t ^ γ - t ^ (1 - γ))) = 0 ∨
      (1 + b * t ^ γ) * (b + t ^ γ) = 0 ↔ b * (t - 1) = t ^ γ - t ^ (1 - γ)
  simp only [hden_ne, or_false, mul_eq_zero, hbt_ne, false_or, sub_eq_zero]

/-- **Part `(i)` of §6.5.1** ([CodenottiVaradarajan2007], p. 151): for every `ρ < 1` (`ρ ≠ 0`) and
`a > 0`, `![1/2, 1/2]` is a Walrasian equilibrium price of `gjerstadMarket ρ a`. -/
theorem gjerstadMarket_isWalrasianEquilibrium_half {ρ a : ℝ}
    (hρ1 : ρ < 1) (hρ0 : ρ ≠ 0) (ha : 0 < a) :
    IsWalrasianEquilibrium (gjerstadMarket ρ a hρ1 hρ0 ha).excessDemandFn ![1 / 2, 1 / 2] := by
  have hhalf : (![1 / 2, 1 - (1 / 2 : ℝ)] : Fin 2 → ℝ) = ![1 / 2, 1 / 2] := by
    funext g; fin_cases g <;> norm_num
  rw [← hhalf, gjerstadMarket_isWalrasianEquilibrium_iff hρ1 hρ0 ha (by norm_num) (by norm_num)]
  norm_num

/-- For `0 < α < 1`, the ratio `u ↦ Real.sinh (α * u) / Real.sinh u` is strictly decreasing on
`(0, ∞)`. -/
private theorem strictAntiOn_sinh_div_sinh {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    StrictAntiOn (fun u : ℝ => Real.sinh (α * u) / Real.sinh u) (Ioi 0) := by
  let ψ : ℝ → ℝ := fun u => α * Real.cosh (α * u) * Real.sinh u - Real.sinh (α * u) * Real.cosh u
  have hψ_deriv : ∀ u : ℝ, HasDerivAt ψ ((α ^ 2 - 1) * Real.sinh (α * u) * Real.sinh u) u := by
    intro u
    have hmul : HasDerivAt (fun s : ℝ => α * s) α u := by
      simpa only [mul_one] using (hasDerivAt_id' u).const_mul α
    have h1 : HasDerivAt (fun s => Real.cosh (α * s)) (Real.sinh (α * u) * α) u :=
      (Real.hasDerivAt_cosh (α * u)).comp u hmul
    have h2 : HasDerivAt (fun s => Real.sinh (α * s)) (Real.cosh (α * u) * α) u :=
      (Real.hasDerivAt_sinh (α * u)).comp u hmul
    have hA := (h1.const_mul α).mul (Real.hasDerivAt_sinh u)
    have hB := h2.mul (Real.hasDerivAt_cosh u)
    convert hA.sub hB using 1
    ring
  have hψ_neg : ∀ u > 0, ψ u < 0 := by
    have hanti : StrictAntiOn ψ (Ici 0) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici 0)
        (fun u _ => (hψ_deriv u).continuousAt.continuousWithinAt) fun u hu => ?_
      rw [interior_Ici] at hu
      rw [(hψ_deriv u).deriv]
      have h1 : 0 < Real.sinh (α * u) := Real.sinh_pos_iff.2 (mul_pos hα0 hu)
      have h2 : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
      have h3 : α ^ 2 - 1 < 0 := by nlinarith
      nlinarith [mul_pos h1 h2]
    intro u hu
    have hlt := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hu.le) hu
    have h0 : ψ 0 = 0 := by simp [ψ]
    linarith
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
  · intro u hu
    have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.2 (mem_Ioi.1 hu)).ne'
    exact ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousAt.div
      Real.continuous_sinh.continuousAt hs).continuousWithinAt
  · intro u hu
    rw [interior_Ioi] at hu
    have hs_pos : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
    have hmul : HasDerivAt (fun s : ℝ => α * s) α u := by
      simpa only [mul_one] using (hasDerivAt_id' u).const_mul α
    have hnum : HasDerivAt (fun s => Real.sinh (α * s)) (Real.cosh (α * u) * α) u :=
      (Real.hasDerivAt_sinh (α * u)).comp u hmul
    have hdiv : HasDerivAt (fun s => Real.sinh (α * s) / Real.sinh s)
        ((Real.cosh (α * u) * α * Real.sinh u - Real.sinh (α * u) * Real.cosh u) /
          Real.sinh u ^ 2) u :=
      hnum.fun_div (Real.hasDerivAt_sinh u) hs_pos.ne'
    rw [hdiv.deriv]
    have heq : (Real.cosh (α * u) * α * Real.sinh u - Real.sinh (α * u) * Real.cosh u) /
        Real.sinh u ^ 2 = ψ u / Real.sinh u ^ 2 := by
      dsimp only [ψ]; ring
    rw [heq]
    exact div_neg_of_neg_of_pos (hψ_neg u hu) (sq_pos_of_pos hs_pos)

/-- **NRTV §6.5.1 — Multiple disconnected equilibria for `ρ < -1`** ([CodenottiVaradarajan2007],
Section 6.5.1, p. 151; Gjerstad 1996): for every `ρ < -1` and every `a > 0` satisfying
`a ^ (-ρ / (1 - ρ)) < (-ρ - 1) / (1 - ρ)`:
1. `![1/2, 1/2]` is a Walrasian equilibrium price of `gjerstadMarket ρ a`;
2. there exists a unique `p ∈ (0, 1/2)` such that `![p, 1 - p]` (and symmetrically `![1 - p, p]`)
   is a Walrasian equilibrium price;
3. for every `q` with `p < q < 1/2` (indeed every `q ∈ (0, 1/2) \ {p}`), `![q, 1 - q]` is **not**
   a Walrasian equilibrium price. -/
theorem gjerstadMarket_exists_disconnected_equilibria {ρ a : ℝ}
    (hρ : ρ < -1) (ha : 0 < a) (ha_small : a ^ (-ρ / (1 - ρ)) < (-ρ - 1) / (1 - ρ)) :
    let hρ1 : ρ < 1 := by linarith
    let hρ0 : ρ ≠ 0 := by linarith
    let E := gjerstadMarket ρ a hρ1 hρ0 ha
    IsWalrasianEquilibrium E.excessDemandFn ![1 / 2, 1 / 2] ∧
      ∃ p : ℝ, 0 < p ∧ p < 1 / 2 ∧
        IsWalrasianEquilibrium E.excessDemandFn ![p, 1 - p] ∧
        IsWalrasianEquilibrium E.excessDemandFn ![1 - p, p] ∧
        (∀ q : ℝ, 0 < q → q < 1 / 2 → q ≠ p →
          ¬ IsWalrasianEquilibrium E.excessDemandFn ![q, 1 - q]) := by
  have hρ1 : ρ < 1 := by linarith
  have hρ0 : ρ ≠ 0 := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  set γ : ℝ := -ρ / (1 - ρ)
  set α : ℝ := 2 * γ - 1
  set b : ℝ := a ^ γ
  have hα_eq : α = (-ρ - 1) / (1 - ρ) := by dsimp only [α, γ]; field_simp [h1ρ.ne']; ring
  have hα0 : 0 < α := by rw [hα_eq]; exact div_pos (by linarith) h1ρ
  have hα1 : α < 1 := by rw [hα_eq]; exact (div_lt_one h1ρ).2 (by linarith)
  have hb_pos : 0 < b := Real.rpow_pos_of_pos ha γ
  have hb_lt : b < α := hα_eq ▸ ha_small
  -- Relate `(t^γ - t^(1-γ)) / (t - 1)` for `t = exp (2 u)` to `sinh (α u) / sinh u`.
  let H : ℝ → ℝ := fun u => Real.sinh (α * u) / Real.sinh u
  have hH_eq : ∀ u : ℝ, 0 < u →
      ((Real.exp (2 * u)) ^ γ - (Real.exp (2 * u)) ^ (1 - γ)) / (Real.exp (2 * u) - 1) = H u := by
    intro u hu
    rw [← Real.exp_mul, ← Real.exp_mul]
    have hsh_pos : 0 < Real.sinh u := Real.sinh_pos_iff.2 hu
    have hdenom : Real.exp (2 * u) - 1 = 2 * Real.exp u * Real.sinh u := by
      rw [Real.sinh_eq]
      have h1 : Real.exp u * Real.exp u = Real.exp (2 * u) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linarith
    have hnum : Real.exp (2 * u * γ) - Real.exp (2 * u * (1 - γ)) =
        2 * Real.exp u * Real.sinh (α * u) := by
      rw [Real.sinh_eq]
      have h1 : Real.exp u * Real.exp (α * u) = Real.exp (2 * u * γ) := by
        rw [← Real.exp_add]; congr 1; dsimp only [α]; ring
      have h2 : Real.exp u * Real.exp (-(α * u)) = Real.exp (2 * u * (1 - γ)) := by
        rw [← Real.exp_add]; congr 1; dsimp only [α]; ring
      linarith
    rw [hnum, hdenom]
    dsimp only [H]
    field_simp [(Real.exp_pos u).ne', hsh_pos.ne']
  -- Find `uL > 0` with `b < H uL` using derivative of `u ↦ sinh (α u) - b * sinh u` at `0`.
  have hex_uL : ∃ uL > 0, b < H uL := by
    let φ : ℝ → ℝ := fun u => Real.sinh (α * u) - b * Real.sinh u
    have hd : HasDerivAt φ (α - b) 0 := by
      have hmul : HasDerivAt (fun u : ℝ => α * u) α 0 := by
        simpa only [mul_one] using (hasDerivAt_id' (0 : ℝ)).const_mul α
      have h1 : HasDerivAt (fun u => Real.sinh (α * u)) α 0 := by
        simpa only [Function.comp_def, mul_zero, Real.cosh_zero, one_mul] using
          (Real.hasDerivAt_sinh (α * 0)).comp 0 hmul
      have h2 : HasDerivAt (fun u => b * Real.sinh u) b 0 := by
        simpa only [Real.cosh_zero, mul_one] using (Real.hasDerivAt_sinh 0).const_mul b
      exact h1.sub h2
    have hlim' := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
      (nhdsWithin_mono 0 (fun x (hx : x ∈ Ioi (0 : ℝ)) => (mem_Ioi.1 hx).ne'))
    obtain ⟨uL, huL_gt, huL_pos⟩ :=
      ((hlim'.eventually (Ioi_mem_nhds (show (0 : ℝ) < α - b by linarith))).and
        self_mem_nhdsWithin).exists
    rw [slope_def_field, sub_zero] at huL_gt
    have hφ0 : φ 0 = 0 := by simp [φ]
    rw [hφ0, sub_zero] at huL_gt
    have hφ_pos : 0 < φ uL := (div_pos_iff_of_pos_right huL_pos).1 huL_gt
    refine ⟨uL, huL_pos, ?_⟩
    dsimp only [H, φ] at hφ_pos ⊢
    exact (lt_div_iff₀ (Real.sinh_pos_iff.2 huL_pos)).2 (by linarith)
  obtain ⟨uL, huL_pos, huL_gt⟩ := hex_uL
  -- Find `uR > uL` with `H uR < b` using `sinh (α u) / sinh u ≤ 2 * exp (-(1 - α) u)` for `u ≥ 1`.
  set uR : ℝ := max (uL + 1) (max 1 ((Real.log (2 / b) + 1) / (1 - α)))
  have huL_lt_uR : uL < uR := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have huR_ge1 : 1 ≤ uR := (le_max_left _ _).trans (le_max_right _ _)
  have huR_pos : 0 < uR := zero_lt_one.trans_le huR_ge1
  have huR_lt : H uR < b := by
    have hsh_pos : 0 < Real.sinh uR := Real.sinh_pos_iff.2 huR_pos
    have hsh_lo : Real.exp uR / 4 ≤ Real.sinh uR := by
      rw [Real.sinh_eq]
      have he2 : 2 ≤ Real.exp (2 * uR) := by
        have h1 : (2 : ℝ) ≤ 2 * uR + 1 := by linarith
        exact h1.trans (Real.add_one_le_exp (2 * uR))
      have hmul : Real.exp (-uR) * 2 ≤ Real.exp uR := by
        have hinv : Real.exp (-uR) * Real.exp (2 * uR) = Real.exp uR := by
          rw [← Real.exp_add]; congr 1; ring
        linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos (-uR)).le]
      linarith
    have hsh_hi : Real.sinh (α * uR) ≤ Real.exp (α * uR) / 2 := by
      rw [Real.sinh_eq]
      linarith [Real.exp_pos (-(α * uR))]
    have hlog_lt : Real.log (2 / b) < (1 - α) * uR := by
      have h1 : (Real.log (2 / b) + 1) / (1 - α) ≤ uR :=
        (le_max_right _ _).trans (le_max_right _ _)
      have h2 := (div_le_iff₀ (by linarith : 0 < 1 - α)).1 h1
      linarith
    have hexp_lt : 2 / b < Real.exp ((1 - α) * uR) := by
      have := Real.exp_lt_exp.2 hlog_lt
      rwa [Real.exp_log (div_pos two_pos hb_pos)] at this
    have hexp_ratio : Real.exp (α * uR) * Real.exp ((1 - α) * uR) = Real.exp uR := by
      rw [← Real.exp_add]; congr 1; ring
    have h2_lt : 2 * Real.exp (α * uR) < b * Real.exp uR := by
      have := mul_lt_mul_of_pos_left hexp_lt (Real.exp_pos (α * uR))
      rw [hexp_ratio] at this
      have hdiv_mul : Real.exp (α * uR) * (2 / b) = 2 * Real.exp (α * uR) / b := by ring
      rw [hdiv_mul, div_lt_iff₀ hb_pos] at this
      linarith
    dsimp only [H]
    rw [div_lt_iff₀ hsh_pos]
    nlinarith [hsh_lo, hsh_hi, h2_lt, hb_pos]
  -- Apply IVT to `H` on `[uL, uR]`.
  have hH_cont : ContinuousOn H (Icc uL uR) := fun u hu => by
    have hs : Real.sinh u ≠ 0 := (Real.sinh_pos_iff.2 (huL_pos.trans_le hu.1)).ne'
    exact ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousAt.div
      Real.continuous_sinh.continuousAt hs).continuousWithinAt
  obtain ⟨uStar, huStar_mem, huStar_eq⟩ :=
    intermediate_value_Icc' huL_lt_uR.le hH_cont ⟨huR_lt.le, huL_gt.le⟩
  have huStar_pos : 0 < uStar := huL_pos.trans_le huStar_mem.1
  set tStar : ℝ := Real.exp (2 * uStar)
  have htStar_gt1 : 1 < tStar := Real.one_lt_exp_iff.2 (by linarith)
  set pStar : ℝ := 1 / (1 + tStar)
  have hpStar_pos : 0 < pStar := by positivity
  have hpStar_lt_half : pStar < 1 / 2 :=
    one_div_lt_one_div_of_lt (by norm_num) (by linarith)
  have hpStar_lt1 : pStar < 1 := by linarith
  have htStar_eq : (1 - pStar) / pStar = tStar := by
    dsimp only [pStar]
    field_simp [(by linarith : 1 + tStar ≠ 0)]
    ring
  have hroot : b * (tStar - 1) = tStar ^ γ - tStar ^ (1 - γ) := by
    have h1 := hH_eq uStar huStar_pos
    rw [huStar_eq] at h1
    exact ((div_eq_iff (sub_pos.2 htStar_gt1).ne').1 h1).symm
  have heq_pStar : IsWalrasianEquilibrium (gjerstadMarket ρ a hρ1 hρ0 ha).excessDemandFn
      ![pStar, 1 - pStar] := by
    rw [gjerstadMarket_isWalrasianEquilibrium_iff hρ1 hρ0 ha hpStar_pos hpStar_lt1, htStar_eq]
    exact hroot
  -- Symmetric equilibrium `![1 - pStar, pStar]`.
  have heq_sym : IsWalrasianEquilibrium (gjerstadMarket ρ a hρ1 hρ0 ha).excessDemandFn
      ![1 - pStar, pStar] := by
    have hvec : (![1 - pStar, 1 - (1 - pStar)] : Fin 2 → ℝ) = ![1 - pStar, pStar] := by
      funext g; fin_cases g <;> simp
    rw [← hvec, gjerstadMarket_isWalrasianEquilibrium_iff hρ1 hρ0 ha (by linarith) (by linarith)]
    have ht_inv : (1 - (1 - pStar)) / (1 - pStar) = tStar⁻¹ := by
      dsimp only [pStar]
      field_simp [(by linarith : 1 + tStar ≠ 0), (by linarith : 0 < tStar).ne']
      ring
    rw [ht_inv]
    have ht0 : 0 < tStar := by linarith
    have hpow1 : (tStar⁻¹) ^ γ = tStar⁻¹ * tStar ^ (1 - γ) := by
      rw [Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, ← Real.rpow_neg_one, ← Real.rpow_add ht0]
      congr 1; ring
    have hpow2 : (tStar⁻¹) ^ (1 - γ) = tStar⁻¹ * tStar ^ γ := by
      rw [Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, ← Real.rpow_neg_one, ← Real.rpow_add ht0]
      congr 1; ring
    change b * (tStar⁻¹ - 1) = (tStar⁻¹) ^ γ - (tStar⁻¹) ^ (1 - γ)
    rw [hpow1, hpow2]
    have : tStar⁻¹ * (b * (tStar - 1)) = tStar⁻¹ * (tStar ^ γ - tStar ^ (1 - γ)) :=
      congrArg (tStar⁻¹ * ·) hroot
    field_simp [ht0.ne'] at this ⊢
    linarith
  refine ⟨gjerstadMarket_isWalrasianEquilibrium_half hρ1 hρ0 ha,
    pStar, hpStar_pos, hpStar_lt_half, heq_pStar, heq_sym, fun q hq0 hq_half hq_ne heq_q => ?_⟩
  have hq1 : q < 1 := by linarith
  rw [gjerstadMarket_isWalrasianEquilibrium_iff hρ1 hρ0 ha hq0 hq1] at heq_q
  set tq : ℝ := (1 - q) / q
  have htq_gt1 : 1 < tq := (one_lt_div hq0).2 (by linarith)
  set uq : ℝ := Real.log tq / 2
  have huq_pos : 0 < uq := div_pos (Real.log_pos htq_gt1) two_pos
  have hexp_uq : Real.exp (2 * uq) = tq := by
    have : 2 * uq = Real.log tq := by dsimp only [uq]; ring
    rw [this, Real.exp_log (by linarith)]
  have hHuq : H uq = b := by
    have heq_q' : b * (tq - 1) = tq ^ γ - tq ^ (1 - γ) := heq_q
    rw [← hH_eq uq huq_pos, hexp_uq, ← heq_q']
    field_simp [(sub_pos.2 htq_gt1).ne']
  have huq_eq : uq = uStar :=
    (strictAntiOn_sinh_div_sinh hα0 hα1).injOn huq_pos huStar_pos (hHuq.trans huStar_eq.symm)
  have htq_eq : tq = tStar := by rw [← hexp_uq, huq_eq]
  apply hq_ne
  have hq_eq : q = 1 / (1 + tq) := by
    dsimp only [tq]
    field_simp [hq0.ne', (by linarith : 1 + (1 - q) / q ≠ 0)]
    ring
  rw [hq_eq, htq_eq]

end DisconnectedCES

end Cslib.GameTheory.Market

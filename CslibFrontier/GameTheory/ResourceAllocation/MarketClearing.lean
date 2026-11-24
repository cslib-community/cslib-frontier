/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.ResourceAllocation.KellyMechanism
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Analysis.Convex.FirstOrder
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smooth market-clearing mechanisms and optimality of proportional sharing

In Section 21.3 of [Johari2007] (see also [JohariTsitsiklis2009]), a **smooth
market-clearing mechanism** is parameterized by a differentiable demand function
`D : (0, ∞) × [0, ∞) → [0, ∞)` such that for every capacity `C > 0`, user count `R ≥ 2`, and
nonzero bid profile `θ ∈ [0, ∞)^R`, there is a unique market-clearing price `p = p_D(θ) > 0`
satisfying `∑_r D(p, θ_r) = C`. Each user `r` receives `D(p, θ_r)` and pays `p · D(p, θ_r)`.

The class `𝒟` (`IsRegularMarketClearing`, [Johari2007], Definition 21.8) consists of smooth
market-clearing mechanisms whose price-anticipating payoffs are concave for all admissible
utilities (`IsAdmissibleUtility`) and whose demand functions cover `[0, ∞)` at every positive
price. Without assuming proportional sharing in advance, the Johari–Tsitsiklis characterization
theorem ([Johari2007], Theorem 21.10; [JohariTsitsiklis2009]) proves:

1. Every mechanism `D ∈ 𝒟` admits a price-taking competitive equilibrium, and every competitive
   equilibrium solves `SYSTEM` (`IsMarketCompetitiveEquilibrium.isSocialOptimum`,
   `IsRegularMarketClearing.exists_isMarketCompetitiveEquilibrium`).
2. Every mechanism `D ∈ 𝒟` has the separable form `D(p, θ) = θ / B(p)` for a concave, strictly
   increasing, differentiable bijection `B : (0, ∞) → (0, ∞)`
   (`IsRegularMarketClearing.exists_priceScale`), so at market clearing every mechanism in `𝒟`
   allocates proportionally to bids (`IsRegularMarketClearing.marketAllocation_eq_kellyAllocation`).
3. Every mechanism `D ∈ 𝒟` has a unique price-anticipating Nash equilibrium on every admissible
   utility instance with `|ι| ≥ 2` (`IsRegularMarketClearing.existsUnique_isMarketNashEquilibrium`),
   its worst-case Nash efficiency ratio satisfies `efficiencyRatio D ≤ 3 / 4`
   (`IsRegularMarketClearing.efficiencyRatio_le_three_fourths`), and equality
   `efficiencyRatio D = 3 / 4` holds if and only if `D(p, θ) = Δ * θ / p` for some `Δ > 0`, i.e.,
   Kelly's proportional sharing mechanism up to positive scalar rescaling
   (`IsRegularMarketClearing.efficiencyRatio_eq_three_fourths_iff`).

For the power-elasticity family `D_c(p, θ) = θ * p ^ (-1 / c)` (`c ≥ 1`, [Johari2007],
Example 21.9 and Exercises 21.1–21.2), we prove `D_c ∈ 𝒟`
(`isRegularMarketClearing_powerElasticity`) and show that its exact worst-case efficiency ratio is
`elasticityEfficiencyBound c = (2 * √c + 1) / (√c + 1) ^ 2` (`efficiencyRatio_powerElasticity`),
which is strictly decreasing on `[1, ∞)` from `3 / 4` at `c = 1`.

## Main definitions

* `Cslib.GameTheory.IsSmoothMarketClearing`: smooth market-clearing demand function `D(p, θ)`
  ([Johari2007], Definition 21.5).
* `Cslib.GameTheory.clearingPrice`, `Cslib.GameTheory.marketAllocation`,
  `Cslib.GameTheory.marketPayoff`: unique market-clearing price `p_D(θ)`, resulting allocation,
  and quasilinear payoff.
* `Cslib.GameTheory.IsMarketCompetitiveEquilibrium`: price-taking competitive equilibrium under `D`
  ([Johari2007], Definition 21.6).
* `Cslib.GameTheory.IsMarketNashEquilibrium`: price-anticipating Nash equilibrium under `D`
  ([Johari2007], Definition 21.7).
* `Cslib.GameTheory.IsRegularMarketClearing`: the mechanism class `𝒟` ([Johari2007],
  Definition 21.8).
* `Cslib.GameTheory.efficiencyRatio`: worst-case Nash-to-optimum aggregate welfare ratio `ρ(D)`
  ([Johari2007], §21.3, p. 554).
* `Cslib.GameTheory.powerElasticityMechanism`: power-elasticity demand family `θ * p ^ (-1 / c)`
  ([Johari2007], Example 21.9).
* `Cslib.GameTheory.elasticityEfficiencyBound`: worst-case efficiency function
  `G(c) = (2 * √c + 1) / (√c + 1) ^ 2` ([Johari2007], Eq. (21.38) and Figure 21.1).

## Main results

* `Cslib.GameTheory.IsMarketCompetitiveEquilibrium.isSocialOptimum`: every competitive equilibrium
  of a surjective smooth market-clearing mechanism solves `SYSTEM` ([Johari2007], Theorem 21.10(i)).
* `Cslib.GameTheory.IsRegularMarketClearing.exists_isMarketCompetitiveEquilibrium`: existence and
  welfare optimality of a competitive equilibrium for every `D ∈ 𝒟` ([Johari2007],
  Theorem 21.10(i)).
* `Cslib.GameTheory.IsRegularMarketClearing.exists_priceScale`: characterization
  `D(p, θ) = θ / B(p)` with `B : (0, ∞) → (0, ∞)` concave, strictly increasing, differentiable,
  and bijective ([Johari2007], Theorem 21.10(ii); [JohariTsitsiklis2009]).
* `Cslib.GameTheory.IsRegularMarketClearing.marketAllocation_eq_kellyAllocation`: every mechanism
  in `𝒟` allocates proportionally to bids at market clearing ([Johari2007], Eq. (21.29)).
* `Cslib.GameTheory.IsRegularMarketClearing.existsUnique_isMarketNashEquilibrium`: existence and
  uniqueness of the price-anticipating Nash equilibrium for every `D ∈ 𝒟` ([Johari2007],
  Theorem 21.10, Step 6).
* `Cslib.GameTheory.IsRegularMarketClearing.efficiencyRatio_le_three_fourths`: every `D ∈ 𝒟` has
  worst-case efficiency ratio at most `3 / 4` ([Johari2007], Theorem 21.10(iii)).
* `Cslib.GameTheory.IsRegularMarketClearing.efficiencyRatio_eq_three_fourths_iff`: equality
  `efficiencyRatio D = 3 / 4` holds iff `D(p, θ) = Δ * θ / p` for some `Δ > 0` ([Johari2007],
  Theorem 21.10(iii); [JohariTsitsiklis2009]).
* `Cslib.GameTheory.isSmoothMarketClearing_powerElasticity`,
  `Cslib.GameTheory.isRegularMarketClearing_powerElasticity`,
  `Cslib.GameTheory.clearingPrice_powerElasticity`: smoothness for `c > 0`, membership in `𝒟` for
  `c ≥ 1`, and clearing price of `θ * p ^ (-1 / c)` ([Johari2007], Example 21.9).
* `Cslib.GameTheory.elasticityEfficiencyBound_strictAntiOn`,
  `Cslib.GameTheory.elasticityEfficiencyBound_eq_of_one_lt`: strict decrease and Eq. (21.38) form
  of `G(c)` on `[1, ∞)`.
* `Cslib.GameTheory.IsMarketNashEquilibrium.elasticityEfficiencyBound_mul_welfare_le`,
  `Cslib.GameTheory.efficiencyRatio_powerElasticity`: exact worst-case efficiency
  `ρ(D_c) = G(c)` of `D_c(p, θ) = θ * p ^ (-1 / c)` for `c ≥ 1` ([Johari2007], Exercises 21.1–21.2).

## References

* [Johari2007]
* [JohariTsitsiklis2009]
-/

public section

open Filter Set
open scoped Topology

namespace Cslib.GameTheory

/-! ### Smooth market-clearing mechanisms and equilibria (Definitions 21.5–21.8) -/

/-- A **smooth market-clearing mechanism** ([Johari2007], §21.3, Definition 21.5) is a nonnegative
demand function `D : ℝ → ℝ → ℝ`, differentiable on `(0, ∞) × [0, ∞)`, such that for every user
count `R ≥ 2`, positive capacity `C > 0`, and nonzero nonnegative bid vector `θ : Fin R → ℝ`,
there exists a unique price `p > 0` clearing the market `∑ r, D p (θ r) = C`. -/
structure IsSmoothMarketClearing (D : ℝ → ℝ → ℝ) : Prop where
  /-- Joint differentiability of `(p, θ) ↦ D p θ` on `(0, ∞) × [0, ∞)`. -/
  differentiableOn : DifferentiableOn ℝ (Function.uncurry D) (Ioi 0 ×ˢ Ici 0)
  /-- Nonnegativity of demand on `(0, ∞) × [0, ∞)`. -/
  nonneg : ∀ p, 0 < p → ∀ θ, 0 ≤ θ → 0 ≤ D p θ
  /-- Existence and uniqueness of a positive market-clearing price for every `R ≥ 2`, `C > 0`, and
  nonzero `θ ≥ 0`. -/
  existsUnique_clearingPrice : ∀ (R : ℕ), 2 ≤ R → ∀ C, 0 < C → ∀ θ : Fin R → ℝ,
    (∀ r, 0 ≤ θ r) → (∃ r, θ r ≠ 0) → ∃! p, 0 < p ∧ ∑ r, D p (θ r) = C

open scoped Classical in
/-- The market-clearing price `p_D(θ)` solving `∑ i, D p (θ i) = C` with `p > 0` when such a price
exists, and `0` otherwise ([Johari2007], §21.3, Definition 21.5). -/
noncomputable def clearingPrice {ι : Type*} [Fintype ι] (D : ℝ → ℝ → ℝ) (C : ℝ) (θ : ι → ℝ) : ℝ :=
  if h : ∃ p, 0 < p ∧ ∑ i, D p (θ i) = C then Classical.choose h else 0

/-- Resource allocation `D(p_D(θ), θ_i)` assigned to user `i` at the market-clearing price
`clearingPrice D C θ` ([Johari2007], §21.3). -/
noncomputable def marketAllocation {ι : Type*} [Fintype ι] (D : ℝ → ℝ → ℝ) (C : ℝ)
    (θ : ι → ℝ) (i : ι) : ℝ :=
  D (clearingPrice D C θ) (θ i)

@[simp]
theorem marketAllocation_apply {ι : Type*} [Fintype ι] (D : ℝ → ℝ → ℝ) (C : ℝ)
    (θ : ι → ℝ) (i : ι) :
    marketAllocation D C θ i = D (clearingPrice D C θ) (θ i) := by
  unfold marketAllocation; rfl

/-- Finite quasilinear payoff `U_i(D(p_D(θ), θ_i)) - p_D(θ) D(p_D(θ), θ_i)` of user `i` at a
nonzero strategy profile `θ` ([Johari2007], §21.3, Eq. (21.27)). -/
noncomputable def marketPayoff {ι : Type*} [Fintype ι] (D : ℝ → ℝ → ℝ) (G : KellyGame ι)
    (θ : ι → ℝ) (i : ι) : ℝ :=
  G.utility i (marketAllocation D G.capacity θ i) -
    clearingPrice D G.capacity θ * marketAllocation D G.capacity θ i

@[simp]
theorem marketPayoff_apply {ι : Type*} [Fintype ι] (D : ℝ → ℝ → ℝ) (G : KellyGame ι)
    (θ : ι → ℝ) (i : ι) :
    marketPayoff D G θ i =
      G.utility i (marketAllocation D G.capacity θ i) -
        clearingPrice D G.capacity θ * marketAllocation D G.capacity θ i := by
  unfold marketPayoff; rfl

/-- A **competitive equilibrium** of a smooth market-clearing mechanism `D` on `G` ([Johari2007],
§21.3, Definition 21.6) is a nonzero nonnegative bid vector `θ` such that, taking the clearing
price `μ = clearingPrice D G.capacity θ` as fixed, each user `i` maximizes
`U_i(D(μ, t)) - μ D(μ, t)` over `t ≥ 0` at `t = θ_i`. -/
structure IsMarketCompetitiveEquilibrium {ι : Type*} [Fintype ι] (D : ℝ → ℝ → ℝ)
    (G : KellyGame ι) (θ : ι → ℝ) : Prop where
  /-- Bids are nonnegative. -/
  nonneg : ∀ i, 0 ≤ θ i
  /-- At least one bid is nonzero, so the market-clearing price is defined. -/
  exists_ne_zero : ∃ i, θ i ≠ 0
  /-- Each user maximizes its price-taking payoff given `μ = clearingPrice D G.capacity θ`. -/
  best_response : ∀ i (t : ℝ), 0 ≤ t →
    G.utility i (D (clearingPrice D G.capacity θ) t) -
      clearingPrice D G.capacity θ * D (clearingPrice D G.capacity θ) t ≤
    G.utility i (D (clearingPrice D G.capacity θ) (θ i)) -
      clearingPrice D G.capacity θ * D (clearingPrice D G.capacity θ) (θ i)

/-- A **price-anticipating Nash equilibrium** of a smooth market-clearing mechanism `D` on `G`
([Johari2007], §21.3, Definition 21.7) is a nonzero nonnegative bid vector `θ` such that no user
`i` can strictly increase its payoff by deviating to any `t ≥ 0`. Under Eq. (21.27) of
[Johari2007], a deviation that yields the composite zero vector `Function.update θ i t = 0` gives
payoff `-∞`, which never improves on the finite equilibrium payoff `marketPayoff D G θ i`. -/
structure IsMarketNashEquilibrium {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℝ → ℝ → ℝ)
    (G : KellyGame ι) (θ : ι → ℝ) : Prop where
  /-- Bids are nonnegative. -/
  nonneg : ∀ i, 0 ≤ θ i
  /-- At least one bid is nonzero. -/
  exists_ne_zero : ∃ i, θ i ≠ 0
  /-- No unilateral deviation yielding a nonzero composite profile increases user `i`'s payoff
  (deviations to the composite zero profile have payoff `-∞` in Eq. (21.27)). -/
  best_response : ∀ i (t : ℝ), 0 ≤ t → (∃ j, Function.update θ i t j ≠ 0) →
    marketPayoff D G (Function.update θ i t) i ≤ marketPayoff D G θ i

/-- Equivalence of `IsMarketNashEquilibrium`'s `best_response` condition with the `WithBot ℝ`
formulation assigning `⊥` (`-∞`) to the composite zero profile ([Johari2007], Eq. (21.27)). -/
theorem isMarketNashEquilibrium_iff_withBot {ι : Type*} [Fintype ι] [DecidableEq ι]
    [DecidablePred fun f : ι → ℝ => ∀ j, f j = 0]
    {D : ℝ → ℝ → ℝ} {G : KellyGame ι} {θ : ι → ℝ} :
    IsMarketNashEquilibrium D G θ ↔
      (∀ i, 0 ≤ θ i) ∧ (∃ i, θ i ≠ 0) ∧
        ∀ i (t : ℝ), 0 ≤ t →
          (if ∀ j, Function.update θ i t j = 0 then (⊥ : WithBot ℝ)
            else ↑(marketPayoff D G (Function.update θ i t) i)) ≤ ↑(marketPayoff D G θ i) := by
  refine ⟨fun h => ⟨h.nonneg, h.exists_ne_zero, fun i t ht => ?_⟩,
    fun ⟨h0, hne, hbr⟩ => ⟨h0, hne, fun i t ht hnz => ?_⟩⟩
  · split_ifs with hall
    · exact bot_le
    · push Not at hall
      exact WithBot.coe_le_coe.mpr (h.best_response i t ht hall)
  · have h := hbr i t ht
    obtain ⟨j, hj⟩ := hnz
    have hnot : ¬ ∀ k, Function.update θ i t k = 0 := fun hall => hj (hall j)
    split_ifs at h
    exact WithBot.coe_le_coe.mp h

/-- The class `𝒟` of **regular smooth market-clearing mechanisms** ([Johari2007], §21.3,
Definition 21.8; [JohariTsitsiklis2009]):
1. `D` is a smooth market-clearing mechanism (`IsSmoothMarketClearing D`, which includes
   nonnegativity `D(p, θ) ≥ 0`, Condition (iv)).
2. For every `R ≥ 2`, `C > 0`, admissible utility `u`, user `r`, and nonnegative `θ`, user `r`'s
   price-anticipating payoff is concave on `(0, ∞)` when `θ_{-r} = 0` and on `[0, ∞)` when
   `θ_{-r} ≠ 0`.
3. For every `p > 0` and desired allocation `d ≥ 0`, there exists a strategy `θ ≥ 0` achieving
   `D(p, θ) = d` (correcting the printed `θ > 0` typo at `d = 0` in [Johari2007], p. 553, which
   would exclude `D(p, θ) = θ p^{-1/c}` of Example 21.9 and `D(p, θ) = θ / B(p)` of
   Theorem 21.10(ii) and render `𝒟` empty). -/
structure IsRegularMarketClearing (D : ℝ → ℝ → ℝ) : Prop where
  /-- Condition (i) and (iv): `D` is a nonnegative smooth market-clearing mechanism. -/
  smooth : IsSmoothMarketClearing D
  /-- Condition (ii) when `θ_{-r} = 0`: price-anticipating payoff is concave on `(0, ∞)`. -/
  concaveOn_payoff_pos : ∀ (R : ℕ), 2 ≤ R → ∀ C, 0 < C → ∀ u, IsAdmissibleUtility u →
    ∀ (r : Fin R) (θ : Fin R → ℝ), (∀ s, s ≠ r → θ s = 0) →
      ConcaveOn ℝ (Ioi 0)
        (fun t => marketPayoff D ⟨C, fun _ => u⟩ (Function.update θ r t) r)
  /-- Condition (ii) when `θ_{-r} ≠ 0`: price-anticipating payoff is concave on `[0, ∞)`. -/
  concaveOn_payoff_nonneg : ∀ (R : ℕ), 2 ≤ R → ∀ C, 0 < C → ∀ u, IsAdmissibleUtility u →
    ∀ (r : Fin R) (θ : Fin R → ℝ), (∀ s, 0 ≤ θ s) → (∃ s, s ≠ r ∧ θ s ≠ 0) →
      ConcaveOn ℝ (Ici 0)
        (fun t => marketPayoff D ⟨C, fun _ => u⟩ (Function.update θ r t) r)
  /-- Condition (iii): at every positive price `p > 0`, every nonnegative demand `d ≥ 0` is
  attained by some strategy `θ ≥ 0`. -/
  surjective_demand : ∀ p, 0 < p → ∀ d, 0 ≤ d → ∃ θ, 0 ≤ θ ∧ D p θ = d

/-- Worst-case Nash-to-optimum aggregate welfare ratio `ρ(D)` of a market-clearing mechanism `D`
over all finite instances with `R ≥ 2` users, positive capacity `C > 0`, and nonnegative
admissible utilities (`IsAdmissibleUtility` with `U_r(0) ≥ 0`, [Johari2007], §21.3, p. 554). On
`IsRegularMarketClearing`, every such instance admits a unique Nash equilibrium, so the source's
`-∞` convention when an instance lacks a Nash equilibrium never triggers. -/
noncomputable def efficiencyRatio (D : ℝ → ℝ → ℝ) : ℝ :=
  sInf { ρ : ℝ | ∃ (R : ℕ) (_ : 2 ≤ R) (G : KellyGame (Fin R)) (d θ : Fin R → ℝ),
    0 < G.capacity ∧
    (∀ r, IsAdmissibleUtility (G.utility r)) ∧
    (∀ r, 0 ≤ G.utility r 0) ∧
    G.IsSocialOptimum d ∧
    IsMarketNashEquilibrium D G θ ∧
    ρ = G.welfare (marketAllocation D G.capacity θ) / G.welfare d }

/-- The power-elasticity market-clearing mechanism `D(p, θ) = θ * p ^ (-1 / c)` ([Johari2007],
§21.3, Example 21.9). At `c = 1` this recovers Kelly's proportional sharing demand `θ / p`. -/
noncomputable def powerElasticityMechanism (c p θ : ℝ) : ℝ :=
  θ * p ^ (-1 / c)

@[simp]
theorem powerElasticityMechanism_apply (c p θ : ℝ) :
    powerElasticityMechanism c p θ = θ * p ^ (-1 / c) := by
  unfold powerElasticityMechanism; rfl

/-- The Johari–Tsitsiklis worst-case efficiency function `G(c) = (2 * √c + 1) / (√c + 1) ^ 2` for
inverse demand elasticity `c ≥ 1` ([Johari2007], §21.3, Eq. (21.38) and Figure 21.1). -/
noncomputable def elasticityEfficiencyBound (c : ℝ) : ℝ :=
  (2 * Real.sqrt c + 1) / (Real.sqrt c + 1) ^ 2

theorem elasticityEfficiencyBound_def (c : ℝ) :
    elasticityEfficiencyBound c = (2 * Real.sqrt c + 1) / (Real.sqrt c + 1) ^ 2 := by
  unfold elasticityEfficiencyBound; rfl

/-! ### Basic properties of `IsSmoothMarketClearing` and `clearingPrice` -/

namespace IsSmoothMarketClearing

variable {D : ℝ → ℝ → ℝ}

/-- Transport of unique market-clearing price existence from `Fin R` to any `[Fintype ι]` with
`2 ≤ Fintype.card ι`. -/
theorem existsUnique_clearingPrice_fintype {ι : Type*} [Fintype ι] (hD : IsSmoothMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {C : ℝ} (hC : 0 < C) {θ : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    ∃! p, 0 < p ∧ ∑ i, D p (θ i) = C := by
  set e := Fintype.equivFin ι
  obtain ⟨i₀, hi₀⟩ := hne
  have hfin := hD.existsUnique_clearingPrice (Fintype.card ι) hcard C hC (θ ∘ e.symm)
    (fun r => hθ (e.symm r)) ⟨e i₀, by simp [hi₀]⟩
  have hsum_eq : ∀ p, (∑ r, D p ((θ ∘ e.symm) r)) = ∑ i, D p (θ i) := fun p =>
    e.symm.sum_comp (fun i => D p (θ i))
  simpa only [hsum_eq] using hfin

theorem clearingPrice_spec {ι : Type*} [Fintype ι] (hD : IsSmoothMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {C : ℝ} (hC : 0 < C) {θ : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    0 < clearingPrice D C θ ∧ ∑ i, D (clearingPrice D C θ) (θ i) = C := by
  obtain ⟨p, hp, _⟩ := hD.existsUnique_clearingPrice_fintype hcard hC hθ hne
  have hex : ∃ q, 0 < q ∧ ∑ i, D q (θ i) = C := ⟨p, hp⟩
  unfold clearingPrice
  split_ifs
  exact Classical.choose_spec hex

theorem clearingPrice_pos {ι : Type*} [Fintype ι] (hD : IsSmoothMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {C : ℝ} (hC : 0 < C) {θ : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    0 < clearingPrice D C θ :=
  (hD.clearingPrice_spec hcard hC hθ hne).1

theorem sum_marketAllocation_eq {ι : Type*} [Fintype ι] (hD : IsSmoothMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {C : ℝ} (hC : 0 < C) {θ : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    ∑ i, marketAllocation D C θ i = C := by
  simpa only [marketAllocation_apply] using (hD.clearingPrice_spec hcard hC hθ hne).2

theorem clearingPrice_eq_iff {ι : Type*} [Fintype ι] (hD : IsSmoothMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {C : ℝ} (hC : 0 < C) {θ : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) {p : ℝ} :
    clearingPrice D C θ = p ↔ 0 < p ∧ ∑ i, D p (θ i) = C := by
  obtain ⟨q, _, huniq⟩ := hD.existsUnique_clearingPrice_fintype hcard hC hθ hne
  have hspec := hD.clearingPrice_spec hcard hC hθ hne
  constructor
  · rintro rfl; exact hspec
  · intro hp; exact (huniq _ hspec).trans (huniq _ hp).symm

theorem isFeasibleAllocation_marketAllocation {ι : Type*} [Fintype ι]
    (hD : IsSmoothMarketClearing D) (hcard : 2 ≤ Fintype.card ι) {G : KellyGame ι}
    (hC : 0 < G.capacity) {θ : ι → ℝ} (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    G.IsFeasibleAllocation (marketAllocation D G.capacity θ) :=
  ⟨fun i => by
      rw [marketAllocation_apply]
      exact hD.nonneg _ (hD.clearingPrice_pos hcard hC hθ hne) _ (hθ i),
    (hD.sum_marketAllocation_eq hcard hC hθ hne).le⟩

theorem continuousOn_price (hD : IsSmoothMarketClearing D) {θ : ℝ} (hθ : 0 ≤ θ) :
    ContinuousOn (fun p => D p θ) (Ioi 0) := by
  have hmaps : MapsTo (fun p : ℝ => (p, θ)) (Ioi 0) (Ioi 0 ×ˢ Ici 0) :=
    fun p hp => ⟨hp, hθ⟩
  exact hD.differentiableOn.continuousOn.comp (Continuous.prodMk_left θ).continuousOn hmaps

theorem differentiableAt_price_of_pos (hD : IsSmoothMarketClearing D) {p θ : ℝ}
    (hp : 0 < p) (hθ : 0 < θ) :
    DifferentiableAt ℝ (fun q => D q θ) p := by
  have hmem : Ioi (0 : ℝ) ×ˢ Ici (0 : ℝ) ∈ 𝓝 (p, θ) :=
    prod_mem_nhds (Ioi_mem_nhds hp) (Ici_mem_nhds hθ)
  have hdiff : DifferentiableAt ℝ (Function.uncurry D) (p, θ) :=
    (hD.differentiableOn (p, θ) ⟨hp, hθ.le⟩).differentiableAt hmem
  have hpair : DifferentiableAt ℝ (fun q : ℝ => (q, θ)) p :=
    differentiableAt_id.prodMk (differentiableAt_const θ)
  exact hdiff.comp p hpair

end IsSmoothMarketClearing

/-! ### Competitive equilibrium optimality (Theorem 21.10(i), first half) -/

/-- **First Welfare Theorem for smooth market-clearing mechanisms** ([Johari2007], §21.3,
Theorem 21.10(i)): for any smooth market-clearing mechanism `D` whose demand covers `[0, ∞)` at
every positive price, every competitive equilibrium `θ` induces an optimal solution to `SYSTEM`. -/
theorem IsMarketCompetitiveEquilibrium.isSocialOptimum {ι : Type*} [Fintype ι]
    {D : ℝ → ℝ → ℝ} {G : KellyGame ι} {θ : ι → ℝ}
    (hce : IsMarketCompetitiveEquilibrium D G θ) (hD : IsSmoothMarketClearing D)
    (hsurj : ∀ p, 0 < p → ∀ d, 0 ≤ d → ∃ t, 0 ≤ t ∧ D p t = d)
    (hcard : 2 ≤ Fintype.card ι) (hC : 0 < G.capacity) :
    G.IsSocialOptimum (marketAllocation D G.capacity θ) := by
  set μ := clearingPrice D G.capacity θ
  have hμ : 0 < μ := hD.clearingPrice_pos hcard hC hce.nonneg hce.exists_ne_zero
  have hsum_d : ∑ i, marketAllocation D G.capacity θ i = G.capacity :=
    hD.sum_marketAllocation_eq hcard hC hce.nonneg hce.exists_ne_zero
  refine ⟨hD.isFeasibleAllocation_marketAllocation hcard hC hce.nonneg hce.exists_ne_zero,
    fun x hx => ?_⟩
  have hterm : ∀ i, G.utility i (x i) - μ * x i ≤
      G.utility i (marketAllocation D G.capacity θ i) -
        μ * marketAllocation D G.capacity θ i := by
    intro i
    obtain ⟨t, ht0, hdt⟩ := hsurj μ hμ (x i) (hx.1 i)
    have hbr := hce.best_response i t ht0
    change G.utility i (D μ t) - μ * D μ t ≤ G.utility i (D μ (θ i)) - μ * D μ (θ i) at hbr
    simpa only [marketAllocation_apply, hdt] using hbr
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_d] at hsum
  have hcap : μ * ∑ i, x i ≤ μ * G.capacity := mul_le_mul_of_nonneg_left hx.2 hμ.le
  change ∑ i, G.utility i (x i) ≤ ∑ i, G.utility i (marketAllocation D G.capacity θ i)
  linarith

/-! ### Steps 1–5 of Theorem 21.10: functional form `D(p, θ) = θ / B(p)` -/

section FunctionalForm

private theorem concaveOn_of_tendsto {s : Set ℝ} (hs : Convex ℝ s) {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hconc : ∀ n, ConcaveOn ℝ s (F n)) (hlim : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ConcaveOn ℝ s f := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ s := hs hx hy ha hb hab
  have h1 : Tendsto (fun n => a • F n x + b • F n y) atTop (𝓝 (a • f x + b • f y)) :=
    ((hlim x hx).const_smul a).add ((hlim y hy).const_smul b)
  exact le_of_tendsto_of_tendsto h1 (hlim _ hxy) (Eventually.of_forall fun n =>
    (hconc n).2 hx hy ha hb hab)

/-- Continuous injective functions on `[μ - ε, μ + ε]` place `g μ` strictly between the endpoint
values. -/
private theorem strict_between_of_continuousOn_injOn {g : ℝ → ℝ} {μ ε : ℝ} (hε : 0 < ε)
    (hcont : ContinuousOn g (Icc (μ - ε) (μ + ε))) (hinj : InjOn g (Icc (μ - ε) (μ + ε))) :
    (g (μ - ε) < g μ ∧ g μ < g (μ + ε)) ∨ (g (μ + ε) < g μ ∧ g μ < g (μ - ε)) := by
  have hL_mem : μ - ε ∈ Icc (μ - ε) (μ + ε) := ⟨le_rfl, by linarith⟩
  have hM_mem : μ ∈ Icc (μ - ε) (μ + ε) := ⟨by linarith, by linarith⟩
  have hR_mem : μ + ε ∈ Icc (μ - ε) (μ + ε) := ⟨by linarith, le_rfl⟩
  have hneL : g (μ - ε) ≠ g μ := fun heq => by linarith [hinj hL_mem hM_mem heq]
  have hneR : g (μ + ε) ≠ g μ := fun heq => by linarith [hinj hR_mem hM_mem heq]
  rcases lt_or_gt_of_ne hneL with hL_lt | hL_gt
  · rcases lt_or_gt_of_ne hneR with hR_lt | hR_gt
    · exfalso
      set v := (max (g (μ - ε)) (g (μ + ε)) + g μ) / 2
      have hv_lt : v < g μ := by dsimp only [v]; linarith [max_lt hL_lt hR_lt]
      have hvL : g (μ - ε) ≤ v := by
        dsimp only [v]; linarith [le_max_left (g (μ - ε)) (g (μ + ε)), max_lt hL_lt hR_lt]
      have hvR : g (μ + ε) ≤ v := by
        dsimp only [v]; linarith [le_max_right (g (μ - ε)) (g (μ + ε)), max_lt hL_lt hR_lt]
      obtain ⟨q₁, hq₁, hgv₁⟩ := intermediate_value_Icc (by linarith : μ - ε ≤ μ)
        (hcont.mono (Icc_subset_Icc_right (by linarith))) ⟨hvL, hv_lt.le⟩
      obtain ⟨q₂, hq₂, hgv₂⟩ := intermediate_value_Icc' (by linarith : μ ≤ μ + ε)
        (hcont.mono (Icc_subset_Icc_left (by linarith))) ⟨hvR, hv_lt.le⟩
      have hq₁_lt : q₁ < μ := lt_of_le_of_ne hq₁.2 fun h => by subst h; linarith [hgv₁]
      have hq₂_gt : μ < q₂ := lt_of_le_of_ne hq₂.1 fun h => by subst h; linarith [hgv₂]
      have hq_eq : q₁ = q₂ := hinj ⟨hq₁.1, by linarith [hq₁.2]⟩ ⟨by linarith [hq₂.1], hq₂.2⟩
        (hgv₁.trans hgv₂.symm)
      linarith
    · exact Or.inl ⟨hL_lt, hR_gt⟩
  · rcases lt_or_gt_of_ne hneR with hR_lt | hR_gt
    · exact Or.inr ⟨hR_lt, hL_gt⟩
    · exfalso
      set v := (g μ + min (g (μ - ε)) (g (μ + ε))) / 2
      have hv_gt : g μ < v := by dsimp only [v]; linarith [lt_min hL_gt hR_gt]
      have hvL : v ≤ g (μ - ε) := by
        dsimp only [v]; linarith [min_le_left (g (μ - ε)) (g (μ + ε)), lt_min hL_gt hR_gt]
      have hvR : v ≤ g (μ + ε) := by
        dsimp only [v]; linarith [min_le_right (g (μ - ε)) (g (μ + ε)), lt_min hL_gt hR_gt]
      obtain ⟨q₁, hq₁, hgv₁⟩ := intermediate_value_Icc' (by linarith : μ - ε ≤ μ)
        (hcont.mono (Icc_subset_Icc_right (by linarith))) ⟨hv_gt.le, hvL⟩
      obtain ⟨q₂, hq₂, hgv₂⟩ := intermediate_value_Icc (by linarith : μ ≤ μ + ε)
        (hcont.mono (Icc_subset_Icc_left (by linarith))) ⟨hv_gt.le, hvR⟩
      have hq₁_lt : q₁ < μ := lt_of_le_of_ne hq₁.2 fun h => by subst h; linarith [hgv₁]
      have hq₂_gt : μ < q₂ := lt_of_le_of_ne hq₂.1 fun h => by subst h; linarith [hgv₂]
      have hq_eq : q₁ = q₂ := hinj ⟨hq₁.1, by linarith [hq₁.2]⟩ ⟨by linarith [hq₂.1], hq₂.2⟩
        (hgv₁.trans hgv₂.symm)
      linarith

/-- Step 1 of Theorem 21.10 ([Johari2007], p. 555): every mechanism `D ∈ 𝒟` yields concave
price-taking payoffs `t ↦ u (D μ t) - μ * D μ t` on `[0, ∞)`. -/
private theorem IsRegularMarketClearing.concaveOn_priceTaking {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) {μ : ℝ} (hμ : 0 < μ) {u : ℝ → ℝ}
    (hu : IsAdmissibleUtility u) :
    ConcaveOn ℝ (Ici 0) (fun t => u (D μ t) - μ * D μ t) := by
  have hd0_pos : 0 < D μ 0 + 1 := by linarith [hD.smooth.nonneg μ hμ 0 le_rfl]
  obtain ⟨θStar, hθStar0, hDStar⟩ := hD.surjective_demand μ hμ (D μ 0 + 1) hd0_pos.le
  have hθStar_pos : 0 < θStar := lt_of_le_of_ne hθStar0 fun h0 => by
    rw [← h0] at hDStar; linarith
  set a := D μ θStar
  have ha_pos : 0 < a := by rw [show a = D μ 0 + 1 from hDStar]; exact hd0_pos
  set g : ℝ → ℝ := fun p => D p θStar
  have hg_cont : ContinuousOn g (Ioi 0) := hD.smooth.continuousOn_price hθStar0
  have hg_nhds : {p : ℝ | a / 2 < g p} ∈ 𝓝 μ :=
    (hg_cont.continuousAt (Ioi_mem_nhds hμ)).preimage_mem_nhds (Ioi_mem_nhds (half_lt_self ha_pos))
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.mem_nhds_iff.mp hg_nhds
  set δ := min (r / 2) (μ / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hr_pos) (half_pos hμ)
  have hg_pos_Icc : ∀ p ∈ Icc (μ - δ) (μ + δ), 0 < g p := fun p hp => by
    have hdist : dist p μ < r := by
      rw [Real.dist_eq, abs_lt]
      have hδr : δ ≤ r / 2 := min_le_left _ _
      exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
    exact lt_trans (half_pos ha_pos) (hr_ball hdist)
  have hg_inj : InjOn g (Icc (μ - δ) (μ + δ)) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have hp₁_pos : 0 < p₁ := by linarith [hp₁.1, min_le_right (r / 2) (μ / 2)]
    have hp₂_pos : 0 < p₂ := by linarith [hp₂.1, min_le_right (r / 2) (μ / 2)]
    have hgp₁ : 0 < g p₁ := hg_pos_Icc p₁ hp₁
    have huniq := hD.smooth.existsUnique_clearingPrice 2 le_rfl (2 * g p₁) (by positivity)
      (fun _ => θStar) (fun _ => hθStar0) ⟨0, hθStar_pos.ne'⟩
    have hsol₁ : 0 < p₁ ∧ ∑ _ : Fin 2, D p₁ θStar = 2 * g p₁ :=
      ⟨hp₁_pos, by simp only [Fin.sum_univ_two, g]; ring⟩
    have hsol₂ : 0 < p₂ ∧ ∑ _ : Fin 2, D p₂ θStar = 2 * g p₁ :=
      ⟨hp₂_pos, by simp only [Fin.sum_univ_two]; change g p₂ + g p₂ = 2 * g p₁; linarith⟩
    exact huniq.unique hsol₁ hsol₂
  set bg : ∀ n : ℕ, Fin (n + 2) → ℝ := fun _ _ => θStar
  set Cseq : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * a
  have hCseq_pos : ∀ n, 0 < Cseq n := fun n => mul_pos (by positivity) ha_pos
  have hconc_n : ∀ n : ℕ, ConcaveOn ℝ (Ici 0)
      (fun t => marketPayoff D ⟨Cseq n, fun _ => u⟩ (Function.update (bg n) 0 t) 0) := by
    intro n
    have h10 : (1 : Fin (n + 2)) ≠ 0 := fun h => by simpa using congrArg Fin.val h
    exact hD.concaveOn_payoff_nonneg (n + 2) (by omega) (Cseq n) (hCseq_pos n) u hu 0 (bg n)
      (fun _ => hθStar0) ⟨1, h10, hθStar_pos.ne'⟩
  refine concaveOn_of_tendsto (convex_Ici 0) hconc_n fun t ht => ?_
  have ht0 : 0 ≤ t := mem_Ici.mp ht
  set pseq : ℕ → ℝ := fun n => clearingPrice D (Cseq n) (Function.update (bg n) 0 t)
  have hsum_upd : ∀ (n : ℕ) (p : ℝ),
      ∑ r : Fin (n + 2), D p (Function.update (bg n) 0 t r) =
        D p t + ((n + 1 : ℕ) : ℝ) * g p := by
    intro n p
    rw [Fin.sum_univ_succ]
    simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _), bg,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul, g]
  have hp_tendsto : Tendsto pseq atTop (𝓝 μ) := by
    rw [Metric.tendsto_atTop]
    intro ε₀ hε₀
    set ε := min (ε₀ / 2) δ
    have hε_pos : 0 < ε := lt_min (half_pos hε₀) hδ_pos
    have hε_le_δ : ε ≤ δ := min_le_right _ _
    have hsub_δ : Icc (μ - ε) (μ + ε) ⊆ Icc (μ - δ) (μ + δ) :=
      Icc_subset_Icc (by linarith) (by linarith)
    have hsub_Ioi : Icc (μ - ε) (μ + ε) ⊆ Ioi 0 := fun p hp => by
      have hδ_le : δ ≤ μ / 2 := min_le_right _ _
      exact mem_Ioi.mpr (by linarith [hp.1])
    have hH_cont : ∀ n : ℕ, ContinuousOn
        (fun p => D p t + ((n + 1 : ℕ) : ℝ) * g p) (Icc (μ - ε) (μ + ε)) := fun n =>
      ((hD.smooth.continuousOn_price ht0).mono hsub_Ioi).add
        (continuousOn_const.mul (hg_cont.mono hsub_Ioi))
    have hupd0_n : ∀ (n : ℕ) (i : Fin (n + 2)), 0 ≤ Function.update (bg n) 0 t i := fun n i => by
      rcases eq_or_ne i 0 with rfl | hi
      · simpa only [Function.update_self] using ht0
      · simpa only [Function.update_of_ne hi, bg] using hθStar0
    have hupd_ne_n : ∀ n : ℕ, ∃ i : Fin (n + 2), Function.update (bg n) 0 t i ≠ 0 := fun n => by
      have h10 : (1 : Fin (n + 2)) ≠ 0 := fun h => by simpa using congrArg Fin.val h
      exact ⟨1, by simpa only [Function.update_of_ne h10, bg] using hθStar_pos.ne'⟩
    have hbet := strict_between_of_continuousOn_injOn hε_pos (hg_cont.mono hsub_Ioi)
      (hg_inj.mono hsub_δ)
    rcases hbet with ⟨hL_lt, hR_gt⟩ | ⟨hR_lt, hL_gt⟩
    · obtain ⟨N, hN⟩ := exists_nat_gt (D (μ - ε) t / (a - g (μ - ε)))
      refine ⟨N, fun n hn => ?_⟩
      have hn_gt : D (μ - ε) t / (a - g (μ - ε)) < ((n + 1 : ℕ) : ℝ) := by
        have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        push_cast; linarith
      have hlow : D (μ - ε) t + ((n + 1 : ℕ) : ℝ) * g (μ - ε) ≤ Cseq n := by
        have hgap : 0 < a - g (μ - ε) := sub_pos.mpr hL_lt
        have hmul := (div_lt_iff₀ hgap).mp hn_gt
        dsimp only [Cseq]; nlinarith
      have hhigh : Cseq n ≤ D (μ + ε) t + ((n + 1 : ℕ) : ℝ) * g (μ + ε) := by
        have hDt : 0 ≤ D (μ + ε) t := hD.smooth.nonneg _ (hsub_Ioi ⟨by linarith, le_rfl⟩) t ht0
        dsimp only [Cseq]; nlinarith
      obtain ⟨q, hq_mem, hq_eq⟩ := intermediate_value_Icc (by linarith : μ - ε ≤ μ + ε)
        (hH_cont n) ⟨hlow, hhigh⟩
      have hp_eq : pseq n = q := by
        rw [hD.smooth.clearingPrice_eq_iff (by simp) (hCseq_pos n) (hupd0_n n) (hupd_ne_n n)]
        exact ⟨hsub_Ioi hq_mem, (hsum_upd n q).trans hq_eq⟩
      rw [hp_eq, Real.dist_eq, abs_lt]
      have : ε ≤ ε₀ / 2 := min_le_left _ _
      exact ⟨by linarith [hq_mem.1], by linarith [hq_mem.2]⟩
    · obtain ⟨N, hN⟩ := exists_nat_gt (D (μ + ε) t / (a - g (μ + ε)))
      refine ⟨N, fun n hn => ?_⟩
      have hn_gt : D (μ + ε) t / (a - g (μ + ε)) < ((n + 1 : ℕ) : ℝ) := by
        have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        push_cast; linarith
      have hlow : D (μ + ε) t + ((n + 1 : ℕ) : ℝ) * g (μ + ε) ≤ Cseq n := by
        have hgap : 0 < a - g (μ + ε) := sub_pos.mpr hR_lt
        have hmul := (div_lt_iff₀ hgap).mp hn_gt
        dsimp only [Cseq]; nlinarith
      have hhigh : Cseq n ≤ D (μ - ε) t + ((n + 1 : ℕ) : ℝ) * g (μ - ε) := by
        have hDt : 0 ≤ D (μ - ε) t := hD.smooth.nonneg _ (hsub_Ioi ⟨le_rfl, by linarith⟩) t ht0
        dsimp only [Cseq]; nlinarith
      obtain ⟨q, hq_mem, hq_eq⟩ := intermediate_value_Icc' (by linarith : μ - ε ≤ μ + ε)
        (hH_cont n) ⟨hlow, hhigh⟩
      have hp_eq : pseq n = q := by
        rw [hD.smooth.clearingPrice_eq_iff (by simp) (hCseq_pos n) (hupd0_n n) (hupd_ne_n n)]
        exact ⟨hsub_Ioi hq_mem, (hsum_upd n q).trans hq_eq⟩
      rw [hp_eq, Real.dist_eq, abs_lt]
      have : ε ≤ ε₀ / 2 := min_le_left _ _
      exact ⟨by linarith [hq_mem.1], by linarith [hq_mem.2]⟩
  have hD_tendsto : Tendsto (fun n => D (pseq n) t) atTop (𝓝 (D μ t)) :=
    ((hD.smooth.continuousOn_price ht0).continuousAt (Ioi_mem_nhds hμ)).tendsto.comp hp_tendsto
  have hp_pos_ev : ∀ᶠ n in atTop, 0 < pseq n := hp_tendsto.eventually (Ioi_mem_nhds hμ)
  have hD_mem_ev : ∀ᶠ n in atTop, D (pseq n) t ∈ Ici (0 : ℝ) :=
    hp_pos_ev.mono fun n hn => hD.smooth.nonneg (pseq n) hn t ht0
  have hu_tendsto : Tendsto (fun n => u (D (pseq n) t)) atTop (𝓝 (u (D μ t))) := by
    have hnhds : Tendsto (fun n => D (pseq n) t) atTop (𝓝[Ici 0] (D μ t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hD_tendsto, hD_mem_ev⟩
    exact (hu.continuousOn (D μ t) (hD.smooth.nonneg μ hμ t ht0)).tendsto.comp hnhds
  have hpay_eq : (fun n => marketPayoff D ⟨Cseq n, fun _ => u⟩
      (Function.update (bg n) 0 t) 0) =
      fun n => u (D (pseq n) t) - pseq n * D (pseq n) t := by
    funext n
    simp only [marketPayoff_apply, marketAllocation_apply, Function.update_self, pseq]
  rw [hpay_eq]
  exact hu_tendsto.sub (hp_tendsto.mul hD_tendsto)

/-- A function on `[0, ∞)` that is both concave and convex is affine:
`f θ = (f 1 - f 0) * θ + f 0`. -/
private theorem eq_affine_of_concaveOn_convexOn_Ici {f : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Ici 0) f) (hconv : ConvexOn ℝ (Ici 0) f) {θ : ℝ} (hθ : 0 ≤ θ) :
    f θ = (f 1 - f 0) * θ + f 0 := by
  rcases le_or_gt θ 1 with hle1 | hgt1
  · have hcomb : (1 - θ) • (0 : ℝ) + θ • (1 : ℝ) = θ := by simp only [smul_eq_mul]; ring
    have h1 := hconc.2 (le_rfl : (0 : ℝ) ∈ Ici 0) (zero_le_one : (1 : ℝ) ∈ Ici 0)
      (sub_nonneg.mpr hle1) hθ (by ring)
    have h2 := hconv.2 (le_rfl : (0 : ℝ) ∈ Ici 0) (zero_le_one : (1 : ℝ) ∈ Ici 0)
      (sub_nonneg.mpr hle1) hθ (by ring)
    rw [hcomb] at h1 h2
    simp only [smul_eq_mul] at h1 h2
    linarith
  · have hθ_pos : 0 < θ := lt_trans zero_lt_one hgt1
    have hinv_le : 1 / θ ≤ 1 := (div_le_one hθ_pos).mpr hgt1.le
    have hcomb : (1 - 1 / θ) • (0 : ℝ) + (1 / θ) • θ = 1 := by
      simp only [smul_eq_mul, mul_zero, zero_add, one_div, inv_mul_cancel₀ hθ_pos.ne']
    have h1 := hconc.2 (le_rfl : (0 : ℝ) ∈ Ici 0) (hθ : θ ∈ Ici 0)
      (sub_nonneg.mpr hinv_le) (div_nonneg zero_le_one hθ) (by ring)
    have h2 := hconv.2 (le_rfl : (0 : ℝ) ∈ Ici 0) (hθ : θ ∈ Ici 0)
      (sub_nonneg.mpr hinv_le) (div_nonneg zero_le_one hθ) (by ring)
    rw [hcomb] at h1 h2
    simp only [smul_eq_mul] at h1 h2
    have hm1 := mul_le_mul_of_nonneg_left h1 hθ
    have hm2 := mul_le_mul_of_nonneg_left h2 hθ
    have hdist1 : θ * ((1 - 1 / θ) * f 0 + 1 / θ * f θ) = (θ - 1) * f 0 + f θ := by
      field_simp [hθ_pos.ne']
    rw [hdist1] at hm1 hm2
    linarith

/-- Step 2 of Theorem 21.10 ([Johari2007], p. 555): for every `p > 0` and `θ ≥ 0`,
`D p θ = θ * D p 1` with `0 < D p 1`. -/
private theorem IsRegularMarketClearing.demand_eq_mul_unit {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) {p : ℝ} (hp : 0 < p) :
    0 < D p 1 ∧ ∀ θ, 0 ≤ θ → D p θ = θ * D p 1 := by
  have hconc1 : ConcaveOn ℝ (Ici 0) (D p) := by
    have h :=
      hD.concaveOn_priceTaking hp (KellyGame.isAdmissibleUtility_linear (by linarith : 0 < p + 1))
    simpa only [show ∀ t, (p + 1) * D p t - p * D p t = D p t from fun t => by ring] using h
  have hconv1 : ConvexOn ℝ (Ici 0) (D p) := by
    have h := hD.concaveOn_priceTaking hp (KellyGame.isAdmissibleUtility_linear (half_pos hp))
    have hneg : ConcaveOn ℝ (Ici 0) (fun t => -(p / 2) * D p t) := by
      simpa only [show ∀ t, p / 2 * D p t - p * D p t = -(p / 2) * D p t from fun t => by ring]
        using h
    refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
    have hc := hneg.2 hx hy ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    have hmul := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 / p)
    have hpne : p ≠ 0 := hp.ne'
    have hlhs : 2 / p * (a * (-(p / 2) * D p x) + b * (-(p / 2) * D p y)) =
        -(a * D p x + b * D p y) := by field_simp [hpne]; ring
    have hrhs : 2 / p * (-(p / 2) * D p (a * x + b * y)) = -D p (a * x + b * y) := by
      field_simp [hpne]
    rw [hlhs, hrhs] at hmul
    linarith
  have haff : ∀ θ, 0 ≤ θ → D p θ = (D p 1 - D p 0) * θ + D p 0 :=
    fun θ hθ => eq_affine_of_concaveOn_convexOn_Ici hconc1 hconv1 hθ
  set a := D p 1 - D p 0
  set b := D p 0
  have hb0 : 0 ≤ b := hD.smooth.nonneg p hp 0 le_rfl
  have ha0 : 0 ≤ a := by
    by_contra hlt
    push Not at hlt
    set t := (b + 1) / (-a)
    have ht_pos : 0 < t := div_pos (by linarith) (by linarith)
    have hnonneg := hD.smooth.nonneg p hp t ht_pos.le
    rw [haff t ht_pos.le] at hnonneg
    have hval : a * t + b = -1 := by
      dsimp only [t]
      have ha_ne : a ≠ 0 := hlt.ne
      have hane : -a ≠ 0 := neg_ne_zero.mpr ha_ne
      field_simp [ha_ne, hane]
      ring
    linarith
  obtain ⟨θ₀, hθ₀, hd0⟩ := hD.surjective_demand p hp 0 le_rfl
  rw [haff θ₀ hθ₀] at hd0
  have hb_eq : b = 0 := by
    have : 0 ≤ a * θ₀ := mul_nonneg ha0 hθ₀
    linarith
  have ha_eq : a = D p 1 := by
    change D p 1 - b = D p 1
    rw [hb_eq, sub_zero]
  obtain ⟨θ₁, hθ₁, hd1⟩ := hD.surjective_demand p hp 1 zero_le_one
  rw [haff θ₁ hθ₁, hb_eq, add_zero, ha_eq] at hd1
  have hDp1_pos : 0 < D p 1 := by
    rcases eq_or_lt_of_le (hD.smooth.nonneg p hp 1 zero_le_one) with h0 | hpos
    · rw [← h0, zero_mul] at hd1; norm_num at hd1
    · exact hpos
  refine ⟨hDp1_pos, fun θ hθ => ?_⟩
  rw [haff θ hθ, hb_eq, add_zero, ha_eq, mul_comm]

private theorem convexOn_payment_of_payoff {s : Set ℝ} (hs : Convex ℝ s) {a w : ℝ → ℝ}
    (hconc : ∀ n : ℕ, ConcaveOn ℝ s (fun t => 1 / ((n : ℝ) + 1) * a t - w t)) :
    ConvexOn ℝ s w := by
  have hneg : ConcaveOn ℝ s (fun t => -w t) := by
    refine concaveOn_of_tendsto hs hconc fun t _ => ?_
    have hk : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := hk.mul_const (a t)
    rw [zero_mul] at hmul
    simpa only [zero_sub] using hmul.sub_const (w t)
  refine ⟨hs, fun x hx y hy p q hp hq hpq => ?_⟩
  have hc := hneg.2 hx hy hp hq hpq
  simp only [smul_eq_mul] at hc ⊢
  linarith

/-- Step 4 of Theorem 21.10 ([Johari2007], p. 556): user `r`'s equilibrium payment
`p_D(θ) D(p_D(θ), θ_r)` is convex in `θ_r`. -/
private theorem IsRegularMarketClearing.convexOn_payment_pos {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) {R : ℕ} (hR : 2 ≤ R) {C : ℝ} (hC : 0 < C)
    (r : Fin R) {θ : Fin R → ℝ} (hzero : ∀ s, s ≠ r → θ s = 0) :
    ConvexOn ℝ (Ioi 0)
      (fun t => clearingPrice D C (Function.update θ r t) *
        marketAllocation D C (Function.update θ r t) r) :=
  convexOn_payment_of_payoff (convex_Ioi 0)
    (a := fun t => marketAllocation D C (Function.update θ r t) r) fun n =>
      (hD.concaveOn_payoff_pos R hR C hC _
        (KellyGame.isAdmissibleUtility_linear (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
        r θ hzero).congr fun t _ => by simp only [marketPayoff_apply]

private theorem IsRegularMarketClearing.convexOn_payment_nonneg {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) {R : ℕ} (hR : 2 ≤ R) {C : ℝ} (hC : 0 < C)
    (r : Fin R) {θ : Fin R → ℝ} (hθ : ∀ s, 0 ≤ θ s) (hnz : ∃ s, s ≠ r ∧ θ s ≠ 0) :
    ConvexOn ℝ (Ici 0)
      (fun t => clearingPrice D C (Function.update θ r t) *
        marketAllocation D C (Function.update θ r t) r) :=
  convexOn_payment_of_payoff (convex_Ici 0)
    (a := fun t => marketAllocation D C (Function.update θ r t) r) fun n =>
      (hD.concaveOn_payoff_nonneg R hR C hC _
        (KellyGame.isAdmissibleUtility_linear (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
        r θ hθ hnz).congr fun t _ => by simp only [marketPayoff_apply]

/-- The inverse price scale `B(p) = (D p 1)⁻¹` and its inverse `Λ(μ) = clearingPrice D 1 ![μ, 0]`
for `D ∈ 𝒟` (Step 5 of Theorem 21.10, [Johari2007], p. 556). -/
private noncomputable def priceScale (D : ℝ → ℝ → ℝ) (p : ℝ) : ℝ :=
  (D p 1)⁻¹

private noncomputable def invPriceScale (D : ℝ → ℝ → ℝ) (μ : ℝ) : ℝ :=
  clearingPrice D 1 ![μ, 0]

private theorem IsRegularMarketClearing.clearingPrice_eq_iff_priceScale {ι : Type*} [Fintype ι]
    {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D) (hcard : 2 ≤ Fintype.card ι)
    {C : ℝ} (hC : 0 < C) {θ : ι → ℝ} (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) {p : ℝ} :
    clearingPrice D C θ = p ↔ 0 < p ∧ priceScale D p = (∑ i, θ i) / C := by
  classical
  have hD_eq : ∀ q, 0 < q → ∀ t, 0 ≤ t → D q t = t / priceScale D q := by
    intro q hq t ht
    rw [(hD.demand_eq_mul_unit hq).2 t ht, div_eq_mul_inv, priceScale, inv_inv]
  obtain ⟨i₀, hi₀⟩ := hne
  have hW_pos : 0 < ∑ i, θ i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have hi₀_pos : 0 < θ i₀ := lt_of_le_of_ne (hθ i₀) (Ne.symm hi₀)
    have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, θ i := Finset.sum_nonneg fun i _ => hθ i
    linarith
  rw [hD.smooth.clearingPrice_eq_iff hcard hC hθ ⟨i₀, hi₀⟩]
  refine ⟨fun ⟨hp, hsum⟩ => ⟨hp, ?_⟩, fun ⟨hp, hBp⟩ => ⟨hp, ?_⟩⟩
  · have hsum' : ∑ i, θ i / priceScale D p = C := by
      simpa only [← hD_eq p hp _ (hθ _)] using hsum
    rw [← Finset.sum_div] at hsum'
    have hBp_pos : 0 < priceScale D p := inv_pos.mpr (hD.demand_eq_mul_unit hp).1
    have hBp_ne : priceScale D p ≠ 0 := hBp_pos.ne'
    field_simp [hBp_ne, hC.ne'] at hsum' ⊢
    linarith
  · have hsum' : ∑ i, D p (θ i) = (∑ i, θ i) / priceScale D p := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => hD_eq p hp (θ i) (hθ i)
    rw [hsum', hBp, div_div_cancel₀ hW_pos.ne']

private theorem IsRegularMarketClearing.priceScale_props {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) :
    BijOn (priceScale D) (Ioi 0) (Ioi 0) ∧
    ConcaveOn ℝ (Ioi 0) (priceScale D) ∧
    StrictMonoOn (priceScale D) (Ioi 0) ∧
    DifferentiableOn ℝ (priceScale D) (Ioi 0) ∧
    (∀ p, 0 < p → ∀ θ, 0 ≤ θ → D p θ = θ / priceScale D p) ∧
    (∀ p, 0 < p → invPriceScale D (priceScale D p) = p) ∧
    (∀ μ, 0 < μ → priceScale D (invPriceScale D μ) = μ ∧ 0 < invPriceScale D μ) ∧
    ConvexOn ℝ (Ioi 0) (invPriceScale D) ∧
    StrictMonoOn (invPriceScale D) (Ioi 0) ∧
    DifferentiableOn ℝ (invPriceScale D) (Ioi 0) ∧
    (∀ μ, 0 < μ → invPriceScale D μ ≤ μ * deriv (invPriceScale D) μ) := by
  set B := priceScale D
  set Λ := invPriceScale D
  have hB_pos : ∀ p, 0 < p → 0 < B p := fun p hp =>
    inv_pos.mpr (hD.demand_eq_mul_unit hp).1
  have hD_eq : ∀ p, 0 < p → ∀ θ, 0 ≤ θ → D p θ = θ / B p := by
    intro p hp θ hθ
    rw [(hD.demand_eq_mul_unit hp).2 θ hθ, div_eq_mul_inv]
    dsimp only [B, priceScale]
    rw [inv_inv]
  have hB_diff_at : ∀ p, 0 < p → DifferentiableAt ℝ B p := fun p hp =>
    (hD.smooth.differentiableAt_price_of_pos hp zero_lt_one).inv
      (hD.demand_eq_mul_unit hp).1.ne'
  have hB_diff : DifferentiableOn ℝ B (Ioi 0) :=
    fun p hp => (hB_diff_at p hp).differentiableWithinAt
  have hΛ_spec : ∀ μ, 0 < μ → 0 < Λ μ ∧ B (Λ μ) = μ := by
    intro μ hμ
    have hθ0 : ∀ i : Fin 2, 0 ≤ (![μ, 0] : Fin 2 → ℝ) i := fun i => by
      fin_cases i <;> simp [hμ.le]
    have hne : ∃ i : Fin 2, (![μ, 0] : Fin 2 → ℝ) i ≠ 0 := ⟨0, by simp [hμ.ne']⟩
    have hiff :=
      (hD.clearingPrice_eq_iff_priceScale le_rfl zero_lt_one hθ0 hne (p := Λ μ)).mp rfl
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
      div_one] using hiff
  have hΛB : ∀ p, 0 < p → Λ (B p) = p := by
    intro p hp
    have hBp : 0 < B p := hB_pos p hp
    have hθ0 : ∀ i : Fin 2, 0 ≤ (![B p, 0] : Fin 2 → ℝ) i := fun i => by
      fin_cases i <;> simp [hBp.le]
    have hne : ∃ i : Fin 2, (![B p, 0] : Fin 2 → ℝ) i ≠ 0 := ⟨0, by simp [hBp.ne']⟩
    rw [show Λ (B p) = clearingPrice D 1 ![B p, 0] from rfl]
    rw [hD.clearingPrice_eq_iff_priceScale le_rfl zero_lt_one hθ0 hne]
    simp [hp, B]
  have hB_bij : BijOn B (Ioi 0) (Ioi 0) :=
    ⟨fun p hp => hB_pos p hp,
      fun p₁ hp₁ p₂ hp₂ heq => by rw [← hΛB p₁ hp₁, ← hΛB p₂ hp₂, heq],
      fun μ hμ => ⟨Λ μ, (hΛ_spec μ hμ).1, (hΛ_spec μ hμ).2⟩⟩
  have hpay_formula : ∀ {C : ℝ}, 0 < C → ∀ {θ : Fin 2 → ℝ} (t : ℝ),
      0 ≤ t → 0 ≤ θ 1 → 0 < t + θ 1 →
      clearingPrice D C (Function.update θ 0 t) *
        marketAllocation D C (Function.update θ 0 t) 0 =
        C * (t / (t + θ 1)) * Λ ((t + θ 1) / C) := by
    intro C hC θ t ht0 hθ1 hsum_pos
    set θ' := Function.update θ 0 t
    have hθ'_nonneg : ∀ i : Fin 2, 0 ≤ θ' i := fun i => by
      fin_cases i
      · simp [θ', ht0]
      · simp [θ', hθ1]
    have hsum_θ' : ∑ i : Fin 2, θ' i = t + θ 1 := by
      simp [Fin.sum_univ_two, θ']
    have hθ'_ne : ∃ i : Fin 2, θ' i ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : ∑ i : Fin 2, θ' i = 0 := Finset.sum_eq_zero fun i _ => hall i
      linarith
    set μ := (t + θ 1) / C
    have hμ_pos : 0 < μ := div_pos hsum_pos hC
    have hp_eq : clearingPrice D C θ' = Λ μ := by
      rw [hD.clearingPrice_eq_iff_priceScale le_rfl hC hθ'_nonneg hθ'_ne, hsum_θ']
      exact ⟨(hΛ_spec μ hμ_pos).1, (hΛ_spec μ hμ_pos).2⟩
    have halloc_eq : marketAllocation D C θ' 0 = C * (t / (t + θ 1)) := by
      simp only [marketAllocation_apply, hp_eq, θ', Function.update_self]
      rw [hD_eq (Λ μ) (hΛ_spec μ hμ_pos).1 t ht0, (hΛ_spec μ hμ_pos).2]
      dsimp only [μ]
      field_simp [hC.ne', hsum_pos.ne']
    rw [hp_eq, halloc_eq]
    ring
  have hΛ_conv : ConvexOn ℝ (Ioi 0) Λ := by
    have hconv_pay := hD.convexOn_payment_pos le_rfl zero_lt_one 0 (θ := ![0, 0])
      (fun s hs => by
        fin_cases s
        · exact absurd rfl hs
        · rfl)
    refine hconv_pay.congr fun t ht => ?_
    have ht_pos : 0 < t := mem_Ioi.mp ht
    have hform := hpay_formula zero_lt_one (θ := ![0, 0]) t ht_pos.le le_rfl
      (by simp [ht_pos])
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, add_zero, div_self ht_pos.ne',
      one_mul, div_one] at hform
    exact hform
  have hsecant_mono : ∀ μ₁ μ₂, 0 < μ₁ → μ₁ < μ₂ → Λ μ₁ / μ₁ ≤ Λ μ₂ / μ₂ := by
    intro μ₁ μ₂ hμ₁ hlt
    set S := μ₁ / 2
    have hS_pos : 0 < S := half_pos hμ₁
    set t₁ := μ₁ / 2
    set t₂ := μ₂ - μ₁ / 2
    have ht₁_pos : 0 < t₁ := half_pos hμ₁
    have ht₁_lt_t₂ : t₁ < t₂ := by dsimp only [t₁, t₂]; linarith
    have ht₂_pos : 0 < t₂ := lt_trans ht₁_pos ht₁_lt_t₂
    have hconv_w := hD.convexOn_payment_nonneg le_rfl zero_lt_one 0 (θ := ![0, S])
      (fun s => by fin_cases s <;> simp [hS_pos.le])
      ⟨1, by decide, by simp [hS_pos.ne']⟩
    set w : ℝ → ℝ := fun t => clearingPrice D 1 (Function.update (![0, S] : Fin 2 → ℝ) 0 t) *
      marketAllocation D 1 (Function.update (![0, S] : Fin 2 → ℝ) 0 t) 0
    have hw_eq : ∀ t, 0 ≤ t → w t = (t / (t + S)) * Λ (t + S) := by
      intro t ht0
      have hf := hpay_formula zero_lt_one (θ := ![0, S]) t ht0 hS_pos.le
        (by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; linarith)
      simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, one_mul, div_one, w] using hf
    have hw0 : w 0 = 0 := by simp [hw_eq 0 le_rfl]
    have hratio_le : t₁ / t₂ ≤ 1 := (div_le_one ht₂_pos).mpr ht₁_lt_t₂.le
    have hcomb : (1 - t₁ / t₂) • (0 : ℝ) + (t₁ / t₂) • t₂ = t₁ := by
      simp only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ ht₂_pos.ne']
    have hineq := hconv_w.2 (le_rfl : (0 : ℝ) ∈ Ici 0) (ht₂_pos.le : t₂ ∈ Ici 0)
      (sub_nonneg.mpr hratio_le) (div_nonneg ht₁_pos.le ht₂_pos.le) (by ring)
    change w ((1 - t₁ / t₂) • (0 : ℝ) + (t₁ / t₂) • t₂) ≤
      (1 - t₁ / t₂) • w 0 + (t₁ / t₂) • w t₂ at hineq
    rw [hcomb, hw0, hw_eq t₁ ht₁_pos.le, hw_eq t₂ ht₂_pos.le] at hineq
    simp only [smul_eq_mul, mul_zero, zero_add] at hineq
    have hsum1 : t₁ + S = μ₁ := by dsimp only [t₁, S]; ring
    have hsum2 : t₂ + S = μ₂ := by dsimp only [t₂, S]; ring
    rw [hsum1, hsum2] at hineq
    have hlhs : t₁ / μ₁ * Λ μ₁ = t₁ * (Λ μ₁ / μ₁) := by ring
    have hrhs : t₁ / t₂ * (t₂ / μ₂ * Λ μ₂) = t₁ * (Λ μ₂ / μ₂) := by
      field_simp [ht₂_pos.ne', (lt_trans hμ₁ hlt).ne']
    rw [hlhs, hrhs] at hineq
    exact le_of_mul_le_mul_left hineq ht₁_pos
  have hΛ_mono : StrictMonoOn Λ (Ioi 0) := by
    intro μ₁ hμ₁ μ₂ _ hlt
    have hsec := hsecant_mono μ₁ μ₂ hμ₁ hlt
    have hΛ₁_pos : 0 < Λ μ₁ := (hΛ_spec μ₁ hμ₁).1
    have hμ₂_pos : 0 < μ₂ := lt_trans hμ₁ hlt
    calc Λ μ₁ = μ₁ * (Λ μ₁ / μ₁) := (mul_div_cancel₀ _ hμ₁.ne').symm
      _ < μ₂ * (Λ μ₁ / μ₁) := mul_lt_mul_of_pos_right hlt (div_pos hΛ₁_pos hμ₁)
      _ ≤ μ₂ * (Λ μ₂ / μ₂) := mul_le_mul_of_nonneg_left hsec hμ₂_pos.le
      _ = Λ μ₂ := mul_div_cancel₀ _ hμ₂_pos.ne'
  have hB_mono : StrictMonoOn B (Ioi 0) := by
    intro p₁ hp₁ p₂ hp₂ hlt
    by_contra hle
    push Not at hle
    have := hΛ_mono.monotoneOn (hB_pos p₂ hp₂) (hB_pos p₁ hp₁) hle
    rw [hΛB p₁ hp₁, hΛB p₂ hp₂] at this
    linarith
  have hB_conc : ConcaveOn ℝ (Ioi 0) B := by
    refine ⟨convex_Ioi 0, fun p₁ hp₁ p₂ hp₂ a b ha hb hab => ?_⟩
    have hμ₁ : 0 < B p₁ := hB_pos p₁ hp₁
    have hμ₂ : 0 < B p₂ := hB_pos p₂ hp₂
    have hμ : a • B p₁ + b • B p₂ ∈ Ioi (0 : ℝ) := (convex_Ioi 0) hμ₁ hμ₂ ha hb hab
    have hp_comb : a • p₁ + b • p₂ ∈ Ioi (0 : ℝ) := (convex_Ioi 0) hp₁ hp₂ ha hb hab
    have hΛ_le := hΛ_conv.2 hμ₁ hμ₂ ha hb hab
    rw [hΛB p₁ hp₁, hΛB p₂ hp₂] at hΛ_le
    have hB_le := hB_mono.monotoneOn (hΛ_spec _ hμ).1 hp_comb hΛ_le
    rwa [(hΛ_spec _ hμ).2] at hB_le
  have hB'_pos : ∀ p, 0 < p → 0 < deriv B p := by
    intro p hp
    have hd : HasDerivWithinAt B (deriv B p) (Ioi 0) p :=
      (hB_diff_at p hp).hasDerivAt.hasDerivWithinAt
    have htan := hB_conc.neg.add_le_of_hasFDerivWithinAt hp (mem_Ioi.mpr (by linarith : 0 < p + 1))
      hd.neg.hasFDerivWithinAt
    simp only [Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at htan
    have hlt : B p < B (p + 1) := hB_mono hp (by linarith : 0 < p + 1) (by linarith)
    linarith
  have hΛ_cont : ContinuousOn Λ (Ioi 0) := hΛ_conv.continuousOn isOpen_Ioi
  have hΛ_hasDerivAt : ∀ μ, 0 < μ → HasDerivAt Λ (deriv B (Λ μ))⁻¹ μ := by
    intro μ hμ
    have hΛμ_pos : 0 < Λ μ := (hΛ_spec μ hμ).1
    exact HasDerivAt.of_local_left_inverse
      (hΛ_cont.continuousAt (Ioi_mem_nhds hμ))
      (hB_diff_at (Λ μ) hΛμ_pos).hasDerivAt
      (hB'_pos (Λ μ) hΛμ_pos).ne'
      (Filter.eventually_of_mem (Ioi_mem_nhds hμ) fun y hy => (hΛ_spec y hy).2)
  have hΛ_diff : DifferentiableOn ℝ Λ (Ioi 0) :=
    fun μ hμ => (hΛ_hasDerivAt μ hμ).differentiableAt.differentiableWithinAt
  have hΛ_elast : ∀ μ, 0 < μ → Λ μ ≤ μ * deriv Λ μ := by
    intro μ hμ
    have hdΛ : HasDerivAt Λ (deriv Λ μ) μ := (hΛ_hasDerivAt μ hμ).deriv ▸ (hΛ_hasDerivAt μ hμ)
    have hdq : HasDerivAt (fun y => Λ y / y)
        ((deriv Λ μ * μ - Λ μ * 1) / μ ^ 2) μ :=
      hdΛ.div (hasDerivAt_id' μ) hμ.ne'
    have hlim : Tendsto (slope (fun y => Λ y / y) μ) (𝓝[>] μ)
        (𝓝 ((deriv Λ μ * μ - Λ μ * 1) / μ ^ 2)) := by
      have h1 := hasDerivWithinAt_iff_tendsto_slope.mp (hdq.hasDerivWithinAt (s := Ioi μ))
      simpa only [Set.sdiff_singleton_eq_self (notMem_Ioi.mpr le_rfl)] using h1
    have hnonneg : ∀ᶠ y in 𝓝[>] μ, 0 ≤ slope (fun y => Λ y / y) μ y := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy_gt : μ < y := mem_Ioi.mp hy
      rw [slope_def_field]
      exact div_nonneg (sub_nonneg.mpr (hsecant_mono μ y hμ hy_gt)) (by linarith)
    have h0 := ge_of_tendsto hlim hnonneg
    have hnum : 0 ≤ deriv Λ μ * μ - Λ μ := by
      have hsq : 0 < μ ^ 2 := sq_pos_of_pos hμ
      have hmul := mul_nonneg h0 hsq.le
      rw [div_mul_cancel₀ _ hsq.ne'] at hmul
      linarith
    linarith
  exact ⟨hB_bij, hB_conc, hB_mono, hB_diff, hD_eq, hΛB,
    fun μ hμ => ⟨(hΛ_spec μ hμ).2, (hΛ_spec μ hμ).1⟩,
    hΛ_conv, hΛ_mono, hΛ_diff, hΛ_elast⟩

/-- **Functional form of mechanisms in `𝒟`** ([Johari2007], §21.3, Theorem 21.10(ii);
[JohariTsitsiklis2009]): for every mechanism `D ∈ 𝒟`, there exists a concave, strictly
increasing, differentiable bijection `B : (0, ∞) → (0, ∞)` such that `D(p, θ) = θ / B(p)` for all
`p > 0` and `θ ≥ 0`. -/
theorem IsRegularMarketClearing.exists_priceScale {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) :
    ∃ B : ℝ → ℝ,
      BijOn B (Ioi 0) (Ioi 0) ∧
      ConcaveOn ℝ (Ioi 0) B ∧
      StrictMonoOn B (Ioi 0) ∧
      DifferentiableOn ℝ B (Ioi 0) ∧
      ∀ p, 0 < p → ∀ θ, 0 ≤ θ → D p θ = θ / B p := by
  obtain ⟨hbij, hconc, hmono, hdiff, hD_eq, _⟩ := hD.priceScale_props
  exact ⟨priceScale D, hbij, hconc, hmono, hdiff, hD_eq⟩

/-- **Proportional market-clearing allocation** ([Johari2007], §21.3, Eq. (21.29)): every
mechanism `D ∈ 𝒟` allocates the resource in exact proportion to the bids `θ` at market clearing,
matching `KellyGame.allocation`. -/
theorem IsRegularMarketClearing.marketAllocation_eq_kellyAllocation {ι : Type*} [Fintype ι]
    {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D) (hcard : 2 ≤ Fintype.card ι)
    {G : KellyGame ι} (hC : 0 < G.capacity) {θ : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    marketAllocation D G.capacity θ = G.allocation θ := by
  classical
  obtain ⟨hbij, _, _, _, hD_eq, _, _, _, _, _, _⟩ := hD.priceScale_props
  have hp_pos : 0 < clearingPrice D G.capacity θ :=
    hD.smooth.clearingPrice_pos hcard hC hθ hne
  have hBp_eq : priceScale D (clearingPrice D G.capacity θ) = (∑ j, θ j) / G.capacity :=
    ((hD.clearingPrice_eq_iff_priceScale hcard hC hθ hne).mp rfl).2
  have hW_pos : 0 < ∑ j, θ j := by
    obtain ⟨i₀, hi₀⟩ := hne
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have : 0 < θ i₀ := lt_of_le_of_ne (hθ i₀) (Ne.symm hi₀)
    have : 0 ≤ ∑ j ∈ Finset.univ.erase i₀, θ j := Finset.sum_nonneg fun j _ => hθ j
    linarith
  funext i
  rw [marketAllocation_apply, hD_eq _ hp_pos (θ i) (hθ i), hBp_eq, KellyGame.allocation]
  field_simp [hC.ne', hW_pos.ne']

/-- **Existence and `SYSTEM` optimality of competitive equilibrium in `𝒟`** ([Johari2007], §21.3,
Theorem 21.10(i)): for every `D ∈ 𝒟`, `2 ≤ Fintype.card ι`, positive capacity, and admissible
utilities, there exists a competitive equilibrium `θ`, and its allocation solves `SYSTEM`. -/
theorem IsRegularMarketClearing.exists_isMarketCompetitiveEquilibrium {ι : Type*} [Fintype ι]
    {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D) (hcard : 2 ≤ Fintype.card ι)
    {G : KellyGame ι} (hC : 0 < G.capacity) (hU : ∀ i, IsAdmissibleUtility (G.utility i)) :
    ∃ θ, IsMarketCompetitiveEquilibrium D G θ ∧
      G.IsSocialOptimum (marketAllocation D G.capacity θ) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w, μ, hce_kelly, _⟩ := KellyGame.exists_isCompetitiveEquilibrium (G := G) hC hU
  obtain ⟨hw, hμ_pos, hμ_price, hbr_kelly⟩ := hce_kelly
  obtain ⟨hbij, _, _, _, hD_eq, _, _, _, _, _, _⟩ := hD.priceScale_props
  set B := priceScale D
  have hBμ_pos : 0 < B μ := hbij.mapsTo hμ_pos
  set θ : ι → ℝ := fun i => B μ * (w i / μ)
  have hθ_nonneg : ∀ i, 0 ≤ θ i := fun i =>
    mul_nonneg hBμ_pos.le (div_nonneg (hw i) hμ_pos.le)
  have hsum_w : ∑ i, w i = μ * G.capacity := by
    rw [hμ_price, KellyGame.price, div_mul_cancel₀ _ hC.ne']
  have hsum_θ : ∑ i, θ i = B μ * G.capacity := by
    have hdiv_sum : ∑ i, w i / μ = G.capacity := by
      rw [← Finset.sum_div, hsum_w, mul_div_cancel_left₀ _ hμ_pos.ne']
    simp only [θ, ← Finset.mul_sum, hdiv_sum]
  have hθ_ne : ∃ i, θ i ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : ∑ i, θ i = 0 := Finset.sum_eq_zero fun i _ => hall i
    have hpos : 0 < B μ * G.capacity := mul_pos hBμ_pos hC
    linarith
  have hp_eq : clearingPrice D G.capacity θ = μ := by
    rw [hD.clearingPrice_eq_iff_priceScale hcard hC hθ_nonneg hθ_ne, hsum_θ]
    exact ⟨hμ_pos, (mul_div_cancel_right₀ _ hC.ne').symm⟩
  have hce : IsMarketCompetitiveEquilibrium D G θ := by
    refine ⟨hθ_nonneg, hθ_ne, fun i t ht0 => ?_⟩
    rw [hp_eq]
    have hDt_nonneg : 0 ≤ D μ t := hD.smooth.nonneg μ hμ_pos t ht0
    have hDθi : D μ (θ i) = w i / μ := by
      rw [hD_eq μ hμ_pos (θ i) (hθ_nonneg i)]
      dsimp only [θ]
      exact mul_div_cancel_left₀ _ hBμ_pos.ne'
    rw [hDθi]
    have hbr := hbr_kelly i (μ * D μ t) (mul_nonneg hμ_pos.le hDt_nonneg)
    rw [mul_div_cancel_left₀ _ hμ_pos.ne'] at hbr
    have hmul_wi : μ * (w i / μ) = w i := mul_div_cancel₀ (w i) hμ_pos.ne'
    rw [hmul_wi]
    exact hbr
  exact ⟨θ, hce, hce.isSocialOptimum hD.smooth hD.surjective_demand hcard hC⟩

end FunctionalForm

/-! ### Step 6 of Theorem 21.10: Nash KKT conditions, existence, and uniqueness -/

section NashEquilibrium

private theorem isMaxOn_Ici_deriv_nonpos {φ : ℝ → ℝ} {x d : ℝ} (hx : 0 ≤ x)
    (hd : HasDerivWithinAt φ d (Ici 0) x) (hmax : ∀ t, 0 ≤ t → φ t ≤ φ x) : d ≤ 0 := by
  have hd_gt : HasDerivWithinAt φ d (Ioi x) x :=
    hd.mono fun y (hy : x < y) => mem_Ici.mpr (le_trans hx hy.le)
  have hlim : Tendsto (slope φ x) (𝓝[>] x) (𝓝 d) := by
    simpa only [Set.sdiff_singleton_eq_self (notMem_Ioi.mpr le_rfl)] using
      hasDerivWithinAt_iff_tendsto_slope.mp hd_gt
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmax y (le_trans hx hy.le))) (by linarith)

/-- Every convex differentiable function on `(0, ∞)` has a nondecreasing, continuous derivative
on `(0, ∞)`. -/
private theorem monotoneOn_and_continuousOn_deriv_of_convexOn_Ioi {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ (Ioi 0) f) (hdiff : DifferentiableOn ℝ f (Ioi 0)) :
    MonotoneOn (deriv f) (Ioi 0) ∧ ContinuousOn (deriv f) (Ioi 0) := by
  have hhd : ∀ x, 0 < x → HasDerivAt f (deriv f x) x := fun x hx =>
    ((hdiff x hx).differentiableAt (Ioi_mem_nhds hx)).hasDerivAt
  have htan : ∀ x y, 0 < x → 0 < y → f x + deriv f x * (y - x) ≤ f y := fun x y hx hy => by
    have h := hconv.add_le_of_hasFDerivAt hx hy (hhd x hx).hasFDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at h
    linarith
  have hmono : MonotoneOn (deriv f) (Ioi 0) := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · have h1 := htan x y hx hy
      have h2 := htan y x hy hx
      nlinarith
  refine ⟨hmono, fun x hx => (Metric.continuousAt_iff.mpr fun ε hε => ?_).continuousWithinAt⟩
  have hx_pos : 0 < x := mem_Ioi.mp hx
  have hsl : Tendsto (slope f x) (𝓝[≠] x) (𝓝 (deriv f x)) :=
    hasDerivAt_iff_tendsto_slope.mp (hhd x hx_pos)
  have hR_ev : ∀ᶠ y in 𝓝[>] x, slope f x y < deriv f x + ε / 2 :=
    (hsl.mono_left (nhdsGT_le_nhdsNE x)).eventually (Iio_mem_nhds (by linarith))
  obtain ⟨x₂, hx₂_sl, hx₂_gt⟩ := (hR_ev.and self_mem_nhdsWithin).exists
  have hL_ev : ∀ᶠ y in 𝓝[<] x, deriv f x - ε / 2 < slope f x y :=
    (hsl.mono_left (nhdsLT_le_nhdsNE x)).eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨x₁, ⟨hx₁_sl, hx₁_pos⟩, hx₁_lt⟩ :=
    ((hL_ev.and (Ioo_mem_nhdsLT hx_pos)).and self_mem_nhdsWithin).exists
  set uR : ℝ → ℝ := fun t => (f x₂ - f t) / (x₂ - t)
  set uL : ℝ → ℝ := fun t => (f t - f x₁) / (t - x₁)
  have huR_cont : ContinuousAt uR x :=
    (continuousAt_const.sub (hhd x hx_pos).continuousAt).div
      (continuousAt_const.sub continuousAt_id) (by linarith [mem_Ioi.mp hx₂_gt])
  have huL_cont : ContinuousAt uL x :=
    ((hhd x hx_pos).continuousAt.sub continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) (by linarith [mem_Iio.mp hx₁_lt])
  have huR_x : uR x < deriv f x + ε / 2 := by
    simpa only [uR, slope_def_field] using hx₂_sl
  have huL_x : deriv f x - ε / 2 < uL x := by
    have : slope f x x₁ = uL x := by rw [slope_comm, slope_def_field]
    linarith
  have hnhds : {t : ℝ | x₁ < t ∧ t < x₂ ∧ uR t < deriv f x + ε ∧ deriv f x - ε < uL t} ∈ 𝓝 x := by
    have h1 : ∀ᶠ t in 𝓝 x, x₁ < t := Ioi_mem_nhds hx₁_lt
    have h2 : ∀ᶠ t in 𝓝 x, t < x₂ := Iio_mem_nhds hx₂_gt
    have h3 : ∀ᶠ t in 𝓝 x, uR t < deriv f x + ε :=
      huR_cont.eventually (Iio_mem_nhds (by linarith))
    have h4 : ∀ᶠ t in 𝓝 x, deriv f x - ε < uL t :=
      huL_cont.eventually (Ioi_mem_nhds (by linarith))
    exact h1.and (h2.and (h3.and h4))
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  obtain ⟨ht_gt, ht_lt, ht_uR, ht_uL⟩ := hδ_ball ht
  have ht_pos : 0 < t := lt_trans hx₁_pos.1 ht_gt
  have hle_uR : deriv f t ≤ uR t := by
    have h := htan t x₂ ht_pos (lt_trans hx_pos hx₂_gt)
    dsimp only [uR]
    rw [le_div_iff₀ (by linarith)]
    linarith
  have huL_le : uL t ≤ deriv f t := by
    have h := htan t x₁ ht_pos hx₁_pos.1
    dsimp only [uL]
    rw [div_le_iff₀ (by linarith)]
    linarith
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- Every admissible utility has a continuous derivative within `[0, ∞)` on `[0, ∞)`. -/
private theorem IsAdmissibleUtility.continuousOn_derivWithin {u : ℝ → ℝ}
    (hu : IsAdmissibleUtility u) :
    ContinuousOn (derivWithin u (Ici 0)) (Ici 0) := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hx0 : 0 ≤ x := mem_Ici.mp hx
  have hsl : Tendsto (slope u x) (𝓝[>] x) (𝓝 (derivWithin u (Ici 0) x)) := by
    have hsub : Ioi x ⊆ Ici 0 := fun y hy => mem_Ici.mpr (le_trans hx0 (mem_Ioi.mp hy).le)
    have h1 := hasDerivWithinAt_iff_tendsto_slope.mp ((hu.hasDerivWithinAt hx0).mono hsub)
    simpa only [Set.sdiff_singleton_eq_self (notMem_Ioi.mpr le_rfl)] using h1
  have hR_ev : ∀ᶠ y in 𝓝[>] x, derivWithin u (Ici 0) x - ε / 2 < slope u x y :=
    hsl.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨x₂, hx₂_sl, hx₂_gt⟩ := (hR_ev.and self_mem_nhdsWithin).exists
  have hx₂_0 : 0 ≤ x₂ := le_trans hx0 (le_of_lt (mem_Ioi.mp hx₂_gt))
  set uR : ℝ → ℝ := fun t => (u x₂ - u t) / (x₂ - t)
  have huR_cont : ContinuousWithinAt uR (Ici 0) x :=
    (continuousWithinAt_const.sub (hu.continuousOn x hx)).div
      (continuousWithinAt_const.sub continuousWithinAt_id) (by linarith [mem_Ioi.mp hx₂_gt])
  have huR_x : derivWithin u (Ici 0) x - ε / 2 < uR x := by
    simpa only [uR, slope_def_field] using hx₂_sl
  rcases eq_or_lt_of_le hx0 with rfl | hx_pos
  · have hnhds : {t : ℝ | t < x₂ ∧ derivWithin u (Ici 0) 0 - ε < uR t} ∈ 𝓝[Ici 0] 0 :=
      Filter.inter_mem (nhdsWithin_le_nhds (Iio_mem_nhds hx₂_gt))
        (huR_cont.eventually (Ioi_mem_nhds (by linarith)))
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
    refine ⟨δ, hδ_pos, fun t ht_mem ht_dist => ?_⟩
    obtain ⟨ht_lt, ht_uR⟩ := hδ_sub ⟨ht_dist, ht_mem⟩
    have hge : uR t ≤ derivWithin u (Ici 0) t := by
      have h := hu.le_add_derivWithin ht_mem hx₂_0
      dsimp only [uR]
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hle : derivWithin u (Ici 0) t ≤ derivWithin u (Ici 0) 0 :=
      hu.derivWithin_antitoneOn le_rfl ht_mem ht_mem
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  · have hhd : HasDerivAt u (derivWithin u (Ici 0) x) x :=
      (hu.hasDerivWithinAt hx0).hasDerivAt (Ici_mem_nhds hx_pos)
    have hslL : Tendsto (slope u x) (𝓝[<] x) (𝓝 (derivWithin u (Ici 0) x)) :=
      (hasDerivAt_iff_tendsto_slope.mp hhd).mono_left (nhdsLT_le_nhdsNE x)
    have hL_ev : ∀ᶠ y in 𝓝[<] x, slope u x y < derivWithin u (Ici 0) x + ε / 2 :=
      hslL.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨x₁, ⟨hx₁_sl, hx₁_pos⟩, hx₁_lt⟩ :=
      ((hL_ev.and (Ioo_mem_nhdsLT hx_pos)).and self_mem_nhdsWithin).exists
    set uL : ℝ → ℝ := fun t => (u t - u x₁) / (t - x₁)
    have huL_cont : ContinuousWithinAt uL (Ici 0) x :=
      ((hu.continuousOn x hx).sub continuousWithinAt_const).div
        (continuousWithinAt_id.sub continuousWithinAt_const) (by linarith [mem_Iio.mp hx₁_lt])
    have huL_x : uL x < derivWithin u (Ici 0) x + ε / 2 := by
      have : slope u x x₁ = uL x := by rw [slope_comm, slope_def_field]
      linarith
    have hnhds : {t : ℝ | x₁ < t ∧ t < x₂ ∧ derivWithin u (Ici 0) x - ε < uR t ∧
        uL t < derivWithin u (Ici 0) x + ε} ∈ 𝓝[Ici 0] x := by
      have h1 : ∀ᶠ t in 𝓝[Ici 0] x, x₁ < t := nhdsWithin_le_nhds (Ioi_mem_nhds hx₁_lt)
      have h2 : ∀ᶠ t in 𝓝[Ici 0] x, t < x₂ := nhdsWithin_le_nhds (Iio_mem_nhds hx₂_gt)
      have h3 : ∀ᶠ t in 𝓝[Ici 0] x, derivWithin u (Ici 0) x - ε < uR t :=
        huR_cont.eventually (Ioi_mem_nhds (by linarith))
      have h4 : ∀ᶠ t in 𝓝[Ici 0] x, uL t < derivWithin u (Ici 0) x + ε :=
        huL_cont.eventually (Iio_mem_nhds (by linarith))
      exact h1.and (h2.and (h3.and h4))
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
    refine ⟨δ, hδ_pos, fun t ht_mem ht_dist => ?_⟩
    obtain ⟨ht_gt, ht_lt, ht_uR, ht_uL⟩ := hδ_sub ⟨ht_dist, ht_mem⟩
    have hge : uR t ≤ derivWithin u (Ici 0) t := by
      have h := hu.le_add_derivWithin ht_mem hx₂_0
      dsimp only [uR]
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hle : derivWithin u (Ici 0) t ≤ uL t := by
      have h := hu.le_add_derivWithin ht_mem hx₁_pos.1.le
      dsimp only [uL]
      rw [le_div_iff₀ (by linarith)]
      linarith
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩

/-- Transport of `concaveOn_payoff_nonneg` from `Fin R` to any `[Fintype ι] [DecidableEq ι]`. -/
private theorem IsRegularMarketClearing.concaveOn_payoff_nonneg_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {G : KellyGame ι} (hC : 0 < G.capacity)
    {i : ι} (hu : IsAdmissibleUtility (G.utility i)) {θ : ι → ℝ}
    (hθ : ∀ j, 0 ≤ θ j) (hnz : ∃ j, j ≠ i ∧ θ j ≠ 0) :
    ConcaveOn ℝ (Ici 0) (fun t => marketPayoff D G (Function.update θ i t) i) := by
  set e := Fintype.equivFin ι
  obtain ⟨j₀, hj₀_ne, hj₀_nz⟩ := hnz
  have hc_fin := hD.concaveOn_payoff_nonneg (Fintype.card ι) hcard G.capacity hC
    (G.utility i) hu (e i) (θ ∘ e.symm) (fun r => hθ (e.symm r))
    ⟨e j₀, fun heq => hj₀_ne (e.injective heq), by simp [hj₀_nz]⟩
  refine hc_fin.congr fun t ht => ?_
  have ht0 : 0 ≤ t := mem_Ici.mp ht
  have hupd_eq : Function.update (θ ∘ e.symm) (e i) t = Function.update θ i t ∘ e.symm := by
    funext r
    by_cases hr : r = e i
    · subst hr; simp
    · have hne : e.symm r ≠ i := fun h => hr (by rw [← h, e.apply_symm_apply])
      simp [Function.update_of_ne hr, Function.update_of_ne hne]
  have hp_eq : clearingPrice D G.capacity (Function.update (θ ∘ e.symm) (e i) t) =
      clearingPrice D G.capacity (Function.update θ i t) := by
    have h1 : ∀ j, 0 ≤ Function.update θ i t j := fun j => by
      by_cases hj : j = i <;> simp [hj, ht0, hθ]
    have h2 : ∃ j, Function.update θ i t j ≠ 0 :=
      ⟨j₀, by simp [Function.update_of_ne hj₀_ne, hj₀_nz]⟩
    have h1' : ∀ r, 0 ≤ Function.update (θ ∘ e.symm) (e i) t r := fun r => by
      rw [hupd_eq]; exact h1 (e.symm r)
    have h2' : ∃ r, Function.update (θ ∘ e.symm) (e i) t r ≠ 0 := by
      rw [hupd_eq]; exact ⟨e j₀, by simp [Function.update_of_ne hj₀_ne, hj₀_nz]⟩
    rw [hD.smooth.clearingPrice_eq_iff (by simpa using hcard) hC h1' h2', hupd_eq]
    have hsum : (∑ r, D (clearingPrice D G.capacity (Function.update θ i t))
        ((Function.update θ i t ∘ e.symm) r)) =
        ∑ j, D (clearingPrice D G.capacity (Function.update θ i t))
          (Function.update θ i t j) :=
      e.symm.sum_comp
        (fun j => D (clearingPrice D G.capacity (Function.update θ i t)) (Function.update θ i t j))
    rw [hsum]
    exact hD.smooth.clearingPrice_spec hcard hC h1 h2
  simp only [marketPayoff_apply, marketAllocation_apply, hp_eq, Function.update_self]

/-- At any Nash equilibrium of `D ∈ 𝒟`, every user faces a strictly positive sum of competing bids
(so at least two users bid strictly positively). -/
private theorem IsMarketNashEquilibrium.sum_erase_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℝ → ℝ → ℝ} {G : KellyGame ι} {θ : ι → ℝ} (hne : IsMarketNashEquilibrium D G θ)
    (hD : IsRegularMarketClearing D) (hcard : 2 ≤ Fintype.card ι) (hC : 0 < G.capacity)
    (i : ι) : 0 < ∑ j ∈ Finset.univ.erase i, θ j := by
  have hnonneg : 0 ≤ ∑ j ∈ Finset.univ.erase i, θ j :=
    Finset.sum_nonneg fun j _ => hne.nonneg j
  refine lt_of_le_of_ne hnonneg (Ne.symm fun hzero => ?_)
  obtain ⟨_, _, _, _, _, _, hΛ_spec, _, hΛ_mono, _, _⟩ := hD.priceScale_props
  have hsum_eq : ∑ j, θ j = θ i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hzero, add_zero]
  have hθi_pos : 0 < θ i := by
    obtain ⟨j₀, hj₀⟩ := hne.exists_ne_zero
    have hW : 0 < ∑ j, θ j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
      have : 0 < θ j₀ := lt_of_le_of_ne (hne.nonneg j₀) (Ne.symm hj₀)
      have : 0 ≤ ∑ j ∈ Finset.univ.erase j₀, θ j := Finset.sum_nonneg fun j _ => hne.nonneg j
      linarith
    linarith
  set θ' := Function.update θ i (θ i / 2)
  have hθ'_nonneg : ∀ j, 0 ≤ θ' j := fun j => by
    by_cases hj : j = i
    · subst hj; simp [θ', (half_pos hθi_pos).le]
    · simp [θ', hj, hne.nonneg j]
  have hθ'_ne : ∃ j, θ' j ≠ 0 := ⟨i, by simp [θ', (half_pos hθi_pos).ne']⟩
  have hsum_θ' : ∑ j, θ' j = θ i / 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i, θ' j = ∑ j ∈ Finset.univ.erase i, θ j :=
      Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    simp only [θ', Function.update_self, hrest, hzero, add_zero]
  have halloc_θ : marketAllocation D G.capacity θ i = G.capacity := by
    rw [hD.marketAllocation_eq_kellyAllocation hcard hC hne.nonneg hne.exists_ne_zero]
    simp only [KellyGame.allocation, hsum_eq, mul_div_cancel_right₀ _ hθi_pos.ne']
  have halloc_θ' : marketAllocation D G.capacity θ' i = G.capacity := by
    rw [hD.marketAllocation_eq_kellyAllocation hcard hC hθ'_nonneg hθ'_ne]
    simp only [KellyGame.allocation, hsum_θ', θ', Function.update_self,
      mul_div_cancel_right₀ _ (half_pos hθi_pos).ne']
  have hp_θ : clearingPrice D G.capacity θ = invPriceScale D (θ i / G.capacity) := by
    rw [hD.clearingPrice_eq_iff_priceScale hcard hC hne.nonneg hne.exists_ne_zero, hsum_eq]
    have hpos := div_pos hθi_pos hC
    exact ⟨(hΛ_spec _ hpos).2, (hΛ_spec _ hpos).1⟩
  have hp_θ' : clearingPrice D G.capacity θ' = invPriceScale D ((θ i / 2) / G.capacity) := by
    rw [hD.clearingPrice_eq_iff_priceScale hcard hC hθ'_nonneg hθ'_ne, hsum_θ']
    have hpos := div_pos (half_pos hθi_pos) hC
    exact ⟨(hΛ_spec _ hpos).2, (hΛ_spec _ hpos).1⟩
  have hp_lt : clearingPrice D G.capacity θ' < clearingPrice D G.capacity θ := by
    rw [hp_θ', hp_θ]
    exact hΛ_mono (div_pos (half_pos hθi_pos) hC) (div_pos hθi_pos hC)
      (div_lt_div_of_pos_right (half_lt_self hθi_pos) hC)
  have hbr := hne.best_response i (θ i / 2) (half_pos hθi_pos).le hθ'_ne
  change marketPayoff D G θ' i ≤ marketPayoff D G θ i at hbr
  simp only [marketPayoff_apply, halloc_θ, halloc_θ'] at hbr
  nlinarith

/-- Step 6 KKT characterization of Nash equilibria for `D ∈ 𝒟` ([Johari2007], Eqs. (21.31)–(21.32),
p. 556). -/
private theorem IsRegularMarketClearing.isMarketNashEquilibrium_iff_kkt
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {G : KellyGame ι} (hC : 0 < G.capacity)
    (hU : ∀ i, IsAdmissibleUtility (G.utility i)) {θ : ι → ℝ} :
    IsMarketNashEquilibrium D G θ ↔
      (∀ i, 0 ≤ θ i) ∧
      (∀ i, 0 < ∑ j ∈ Finset.univ.erase i, θ j) ∧
      (∀ i, derivWithin (G.utility i) (Ici 0) (G.allocation θ i) *
          (1 - G.allocation θ i / G.capacity) ≤
        invPriceScale D ((∑ j, θ j) / G.capacity) * (1 - G.allocation θ i / G.capacity) +
          ((∑ j, θ j) / G.capacity) * deriv (invPriceScale D) ((∑ j, θ j) / G.capacity) *
            (G.allocation θ i / G.capacity)) ∧
      (∀ i, 0 < G.allocation θ i →
        derivWithin (G.utility i) (Ici 0) (G.allocation θ i) *
          (1 - G.allocation θ i / G.capacity) =
        invPriceScale D ((∑ j, θ j) / G.capacity) * (1 - G.allocation θ i / G.capacity) +
          ((∑ j, θ j) / G.capacity) * deriv (invPriceScale D) ((∑ j, θ j) / G.capacity) *
            (G.allocation θ i / G.capacity)) := by
  obtain ⟨_, _, _, _, _, _, hΛ_spec, _, _, hΛ_diff, _⟩ := hD.priceScale_props
  set Λ := invPriceScale D
  set C := G.capacity
  have hpay_upd : ∀ (i : ι), (∀ j, 0 ≤ θ j) → 0 < ∑ j ∈ Finset.univ.erase i, θ j →
      let s := ∑ j ∈ Finset.univ.erase i, θ j
      ∀ t, 0 ≤ t →
        marketPayoff D G (Function.update θ i t) i =
          G.utility i (C * t / (t + s)) - (C * t / (t + s)) * Λ ((t + s) / C) := by
    intro i hθ0 hs s t ht0
    have hupd_nonneg : ∀ j, 0 ≤ Function.update θ i t j := fun j => by
      by_cases hj : j = i <;> simp [hj, ht0, hθ0]
    have hsum_upd : ∑ j, Function.update θ i t j = t + s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    have hts_pos : 0 < t + s := by linarith
    have hupd_ne : ∃ j, Function.update θ i t j ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : ∑ j, Function.update θ i t j = 0 := Finset.sum_eq_zero fun j _ => hall j
      linarith
    have halloc := congrFun
      (hD.marketAllocation_eq_kellyAllocation hcard hC hupd_nonneg hupd_ne) i
    simp only [KellyGame.allocation, Function.update_self, hsum_upd] at halloc
    have hp : clearingPrice D G.capacity (Function.update θ i t) = Λ ((t + s) / C) := by
      rw [hD.clearingPrice_eq_iff_priceScale hcard hC hupd_nonneg hupd_ne, hsum_upd]
      have hμt : 0 < (t + s) / C := div_pos hts_pos hC
      exact ⟨(hΛ_spec _ hμt).2, (hΛ_spec _ hμt).1⟩
    simp only [marketPayoff_apply, halloc, hp, C]
    ring
  have hderiv_upd : ∀ (i : ι) (s : ℝ), 0 < s → ∀ t, 0 ≤ t →
      HasDerivWithinAt
        (fun x => G.utility i (C * x / (x + s)) - (C * x / (x + s)) * Λ ((x + s) / C))
        (derivWithin (G.utility i) (Ici 0) (C * t / (t + s)) * (C * s / (t + s) ^ 2) -
          (C * s / (t + s) ^ 2 * Λ ((t + s) / C) +
            C * t / (t + s) * (deriv Λ ((t + s) / C) * (1 / C))))
        (Ici 0) t := by
    intro i s hs t ht0
    have hts_pos : 0 < t + s := by linarith
    have hfrac : HasDerivAt (fun x : ℝ => C * x / (x + s)) (C * s / (t + s) ^ 2) t := by
      have hnum : HasDerivAt (fun x : ℝ => C * x) C t := by
        simpa only [mul_one] using (hasDerivAt_id' t).const_mul C
      have hq := hnum.div ((hasDerivAt_id' t).add_const s) hts_pos.ne'
      have hsimp : (C * (t + s) - C * t * 1) / (t + s) ^ 2 = C * s / (t + s) ^ 2 := by ring
      rwa [hsimp] at hq
    have hmaps : MapsTo (fun x : ℝ => C * x / (x + s)) (Ici 0) (Ici 0) := fun x hx =>
      div_nonneg (mul_nonneg hC.le hx) (by linarith [mem_Ici.mp hx])
    have hdu := (hU i).hasDerivWithinAt (hmaps ht0)
    have hu_part := hdu.comp t hfrac.hasDerivWithinAt hmaps
    have hμ_pos : 0 < (t + s) / C := div_pos hts_pos hC
    have hdΛ : HasDerivAt Λ (deriv Λ ((t + s) / C)) ((t + s) / C) :=
      ((hΛ_diff _ hμ_pos).differentiableAt (Ioi_mem_nhds hμ_pos)).hasDerivAt
    have hlin : HasDerivAt (fun x : ℝ => (x + s) / C) (1 / C) t := by
      simpa only [one_div] using ((hasDerivAt_id' t).add_const s).div_const C
    have hpay_part := (hfrac.mul (hdΛ.comp t hlin)).hasDerivWithinAt (s := Ici 0)
    exact hu_part.sub hpay_part
  have hslope_simp : ∀ (i : ι), (∀ j, 0 ≤ θ j) → 0 < ∑ j ∈ Finset.univ.erase i, θ j →
      let s := ∑ j ∈ Finset.univ.erase i, θ j
      let μ := (∑ j, θ j) / C
      let d := G.allocation θ i
      derivWithin (G.utility i) (Ici 0) (C * θ i / (θ i + s)) * (C * s / (θ i + s) ^ 2) -
        (C * s / (θ i + s) ^ 2 * Λ ((θ i + s) / C) +
          C * θ i / (θ i + s) * (deriv Λ ((θ i + s) / C) * (1 / C))) =
      (derivWithin (G.utility i) (Ici 0) d * (1 - d / C) -
        (Λ μ * (1 - d / C) + μ * deriv Λ μ * (d / C))) / μ := by
    intro i hθ0 hs s μ d
    have hW_eq : θ i + s = ∑ j, θ j := Finset.add_sum_erase Finset.univ θ (Finset.mem_univ i)
    have hW_pos : 0 < ∑ j, θ j := by linarith [hθ0 i]
    have hd_eq : C * θ i / (θ i + s) = d := by
      simp only [d, C, KellyGame.allocation, hW_eq]
    have hμ_eq : (θ i + s) / C = μ := by simp only [μ, hW_eq]
    rw [hd_eq, hμ_eq]
    have hs_eq : s = ∑ j, θ j - θ i := by linarith
    dsimp only [μ, d, KellyGame.allocation]
    rw [hW_eq, hs_eq]
    field_simp [hC.ne', hW_pos.ne']
    ring
  constructor
  · intro hne
    have herase : ∀ i, 0 < ∑ j ∈ Finset.univ.erase i, θ j :=
      fun i => hne.sum_erase_pos hD hcard hC i
    refine ⟨hne.nonneg, herase, fun i => ?_, fun i hdi => ?_⟩
    · set s := ∑ j ∈ Finset.univ.erase i, θ j
      have hs : 0 < s := herase i
      obtain ⟨j₀, hj₀_mem⟩ := Finset.card_pos.mp (by
        by_contra h0
        push Not at h0
        have he : Finset.univ.erase i = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp h0)
        rw [show s = ∑ j ∈ Finset.univ.erase i, θ j from rfl, he, Finset.sum_empty] at hs
        linarith)
      have hj₀_ne : j₀ ≠ i := Finset.ne_of_mem_erase hj₀_mem
      have hnz_other : ∃ j, j ≠ i ∧ θ j ≠ 0 := by
        by_contra hall
        push Not at hall
        have h0 : s = 0 := Finset.sum_eq_zero fun j hj => hall j (Finset.ne_of_mem_erase hj)
        linarith
      obtain ⟨k₀, hk₀_ne, hk₀_nz⟩ := hnz_other
      have hW_pos : 0 < ∑ j, θ j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; linarith [hne.nonneg i]
      have hμ_pos : 0 < (∑ j, θ j) / C := div_pos hW_pos hC
      set φ : ℝ → ℝ :=
        fun x => G.utility i (C * x / (x + s)) - (C * x / (x + s)) * Λ ((x + s) / C)
      have hd := (hderiv_upd i s hs (θ i) (hne.nonneg i))
      rw [hslope_simp i hne.nonneg hs] at hd
      have hmax : ∀ t, 0 ≤ t → φ t ≤ φ (θ i) := fun t ht0 => by
        have hnz : ∃ j, Function.update θ i t j ≠ 0 :=
          ⟨k₀, by simp [Function.update_of_ne hk₀_ne, hk₀_nz]⟩
        have hbr := hne.best_response i t ht0 hnz
        rw [hpay_upd i hne.nonneg hs t ht0] at hbr
        have h0 := hpay_upd i hne.nonneg hs (θ i) (hne.nonneg i)
        rw [Function.update_eq_self] at h0
        rwa [h0] at hbr
      have hnonpos := isMaxOn_Ici_deriv_nonpos (hne.nonneg i) hd hmax
      have hdiv_nonpos := hnonpos
      have hnum_nonpos :
          derivWithin (G.utility i) (Ici 0) (G.allocation θ i) *
            (1 - G.allocation θ i / C) -
          (Λ ((∑ j, θ j) / C) * (1 - G.allocation θ i / C) +
            ((∑ j, θ j) / C) * deriv Λ ((∑ j, θ j) / C) * (G.allocation θ i / C)) ≤ 0 := by
        by_contra hgt
        push Not at hgt
        exact not_lt_of_ge hdiv_nonpos (div_pos hgt hμ_pos)
      linarith
    · set s := ∑ j ∈ Finset.univ.erase i, θ j
      have hs : 0 < s := herase i
      have hnz_other : ∃ j, j ≠ i ∧ θ j ≠ 0 := by
        by_contra hall
        push Not at hall
        have h0 : s = 0 := Finset.sum_eq_zero fun j hj => hall j (Finset.ne_of_mem_erase hj)
        linarith
      obtain ⟨k₀, hk₀_ne, hk₀_nz⟩ := hnz_other
      have hW_pos : 0 < ∑ j, θ j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; linarith [hne.nonneg i]
      have hμ_pos : 0 < (∑ j, θ j) / C := div_pos hW_pos hC
      have hθi_pos : 0 < θ i := by
        simp only [KellyGame.allocation] at hdi
        exact (mul_pos_iff_of_pos_left hC).mp ((div_pos_iff_of_pos_right hW_pos).mp hdi)
      have hd := (hderiv_upd i s hs (θ i) (hne.nonneg i)).hasDerivAt (Ici_mem_nhds hθi_pos)
      rw [hslope_simp i hne.nonneg hs] at hd
      have hloc : IsLocalMax
          (fun x => G.utility i (C * x / (x + s)) - (C * x / (x + s)) * Λ ((x + s) / C))
          (θ i) := by
        filter_upwards [Ioi_mem_nhds hθi_pos] with t ht
        have hnz : ∃ j, Function.update θ i t j ≠ 0 :=
          ⟨k₀, by simp [Function.update_of_ne hk₀_ne, hk₀_nz]⟩
        have hbr := hne.best_response i t ht.le hnz
        rw [hpay_upd i hne.nonneg hs t ht.le] at hbr
        have h0 := hpay_upd i hne.nonneg hs (θ i) (hne.nonneg i)
        rw [Function.update_eq_self] at h0
        rwa [h0] at hbr
      have hzero := hloc.hasDerivAt_eq_zero hd
      rw [div_eq_zero_iff] at hzero
      linarith [hzero.resolve_right hμ_pos.ne']
  · rintro ⟨hθ0, herase, hle, heq⟩
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hW_pos : 0 < ∑ j, θ j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      linarith [hθ0 i₀, herase i₀]
    have hne_zero : ∃ j, θ j ≠ 0 := by
      by_contra hall
      push Not at hall
      linarith [Finset.sum_eq_zero (s := Finset.univ) fun j _ => hall j]
    refine ⟨hθ0, hne_zero, fun i t ht0 _ => ?_⟩
    set s := ∑ j ∈ Finset.univ.erase i, θ j
    have hs : 0 < s := herase i
    have hnz_other : ∃ j, j ≠ i ∧ θ j ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : s = 0 := Finset.sum_eq_zero fun j hj => hall j (Finset.ne_of_mem_erase hj)
      linarith
    have hconc := hD.concaveOn_payoff_nonneg_fintype hcard hC (hU i) hθ0 hnz_other
    set φ : ℝ → ℝ :=
      fun x => G.utility i (C * x / (x + s)) - (C * x / (x + s)) * Λ ((x + s) / C)
    have hconc_φ : ConcaveOn ℝ (Ici 0) φ :=
      hconc.congr fun x hx => hpay_upd i hθ0 hs x hx
    have hd := hderiv_upd i s hs (θ i) (hθ0 i)
    rw [hslope_simp i hθ0 hs] at hd
    have htan_raw := hconc_φ.neg.add_le_of_hasFDerivWithinAt (hθ0 i) ht0 hd.neg.hasFDerivWithinAt
    simp only [Pi.neg_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at htan_raw
    have hμ_pos : 0 < (∑ j, θ j) / C := div_pos hW_pos hC
    set slope_val :=
      (derivWithin (G.utility i) (Ici 0) (G.allocation θ i) * (1 - G.allocation θ i / C) -
        (Λ ((∑ j, θ j) / C) * (1 - G.allocation θ i / C) +
          ((∑ j, θ j) / C) * deriv Λ ((∑ j, θ j) / C) * (G.allocation θ i / C))) /
      ((∑ j, θ j) / C)
    have hterm_nonpos : slope_val * (t - θ i) ≤ 0 := by
      rcases eq_or_lt_of_le (hθ0 i) with hi0 | hi_pos
      · rw [← hi0, sub_zero]
        have hnum : derivWithin (G.utility i) (Ici 0) (G.allocation θ i) *
            (1 - G.allocation θ i / C) -
          (Λ ((∑ j, θ j) / C) * (1 - G.allocation θ i / C) +
            ((∑ j, θ j) / C) * deriv Λ ((∑ j, θ j) / C) * (G.allocation θ i / C)) ≤ 0 :=
          sub_nonpos.mpr (hle i)
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hnum hμ_pos.le) ht0
      · have hdi : 0 < G.allocation θ i := div_pos (mul_pos hC hi_pos) hW_pos
        have hzero : slope_val = 0 := by
          dsimp only [slope_val]
          rw [heq i hdi, sub_self, zero_div]
        rw [hzero, zero_mul]
    rw [hpay_upd i hθ0 hs t ht0]
    have h0 := hpay_upd i hθ0 hs (θ i) (hθ0 i)
    rw [Function.update_eq_self] at h0
    rw [h0]
    linarith

/-- **Existence and uniqueness of the price-anticipating Nash equilibrium in `𝒟`** ([Johari2007],
§21.3, Theorem 21.10, Step 6, p. 556): for every mechanism `D ∈ 𝒟`, user type with
`2 ≤ Fintype.card ι`, positive capacity `G.capacity > 0`, and admissible utilities, there exists a
unique price-anticipating Nash equilibrium `θ`. -/
theorem IsRegularMarketClearing.existsUnique_isMarketNashEquilibrium
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D)
    (hcard : 2 ≤ Fintype.card ι) {G : KellyGame ι} (hC : 0 < G.capacity)
    (hU : ∀ i, IsAdmissibleUtility (G.utility i)) :
    ∃! θ, IsMarketNashEquilibrium D G θ := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hB_bij, _, _, _, _, hΛB, hΛ_spec, hΛ_conv, hΛ_mono, hΛ_diff, hΛ_elast⟩ :=
    hD.priceScale_props
  set B := priceScale D
  set Λ := invPriceScale D
  set C := G.capacity
  obtain ⟨hΛ'_mono, hΛ'_cont⟩ := monotoneOn_and_continuousOn_deriv_of_convexOn_Ioi hΛ_conv hΛ_diff
  have hΛ_cont : ContinuousOn Λ (Ioi 0) := hΛ_conv.continuousOn isOpen_Ioi
  set lhs : ι → ℝ → ℝ := fun i x => derivWithin (G.utility i) (Ici 0) x * (1 - x / C)
  set rhs : ℝ → ℝ → ℝ := fun μ x => Λ μ * (1 - x / C) + μ * deriv Λ μ * (x / C)
  have hlhs_cont : ∀ i, ContinuousOn (lhs i) (Icc 0 C) := fun i =>
    ((hU i).continuousOn_derivWithin.mono Icc_subset_Ici_self).mul
      (continuousOn_const.sub (continuousOn_id.div_const C))
  have hlhs_anti : ∀ i, StrictAntiOn (lhs i) (Icc 0 C) := by
    intro i x hx y hy hxy
    have hux_pos : 0 < derivWithin (G.utility i) (Ici 0) x := (hU i).derivWithin_pos hx.1
    have huy_le : derivWithin (G.utility i) (Ici 0) y ≤ derivWithin (G.utility i) (Ici 0) x :=
      (hU i).derivWithin_antitoneOn hx.1 hy.1 hxy.le
    have h1y_nonneg : 0 ≤ 1 - y / C := sub_nonneg.mpr ((div_le_one hC).mpr hy.2)
    have h1_lt : 1 - y / C < 1 - x / C := by
      have : x / C < y / C := div_lt_div_of_pos_right hxy hC
      linarith
    calc lhs i y = derivWithin (G.utility i) (Ici 0) y * (1 - y / C) := rfl
      _ ≤ derivWithin (G.utility i) (Ici 0) x * (1 - y / C) :=
          mul_le_mul_of_nonneg_right huy_le h1y_nonneg
      _ < derivWithin (G.utility i) (Ici 0) x * (1 - x / C) :=
          mul_lt_mul_of_pos_left h1_lt hux_pos
  have hrhs_mono_x : ∀ μ, 0 < μ → MonotoneOn (rhs μ) (Icc 0 C) := by
    intro μ hμ x hx y hy hxy
    have hdiff : rhs μ y - rhs μ x = (μ * deriv Λ μ - Λ μ) * ((y - x) / C) := by
      dsimp only [rhs]; ring
    have hel := hΛ_elast μ hμ
    have hnonneg : 0 ≤ (μ * deriv Λ μ - Λ μ) * ((y - x) / C) :=
      mul_nonneg (by linarith) (div_nonneg (by linarith) hC.le)
    linarith
  have hrhs_strict_μ : ∀ x ∈ Icc (0 : ℝ) C, StrictMonoOn (fun μ => rhs μ x) (Ioi 0) := by
    intro x hx μ₁ hμ₁ μ₂ hμ₂ hlt
    have hΛ₁_lt : Λ μ₁ < Λ μ₂ := hΛ_mono hμ₁ hμ₂ hlt
    have hμd₁_pos : 0 < Λ μ₁ := (hΛ_spec μ₁ hμ₁).2
    have hd₁_pos : 0 < deriv Λ μ₁ := by
      have := hΛ_elast μ₁ hμ₁
      have hμ₁_pos : 0 < μ₁ := hμ₁
      nlinarith
    have hd_le : deriv Λ μ₁ ≤ deriv Λ μ₂ := hΛ'_mono hμ₁ hμ₂ hlt.le
    have hprod_lt : μ₁ * deriv Λ μ₁ < μ₂ * deriv Λ μ₂ :=
      calc μ₁ * deriv Λ μ₁ < μ₂ * deriv Λ μ₁ := mul_lt_mul_of_pos_right hlt hd₁_pos
        _ ≤ μ₂ * deriv Λ μ₂ := mul_le_mul_of_nonneg_left hd_le (le_of_lt hμ₂)
    have hw1 : 0 ≤ 1 - x / C := sub_nonneg.mpr ((div_le_one hC).mpr hx.2)
    have hw2 : 0 ≤ x / C := div_nonneg hx.1 hC.le
    rcases eq_or_lt_of_le hw2 with hw2_0 | hw2_pos
    · have hw1_1 : 1 - x / C = 1 := by linarith
      dsimp only [rhs]
      rw [hw1_1, ← hw2_0]
      linarith
    · have h1 : Λ μ₁ * (1 - x / C) ≤ Λ μ₂ * (1 - x / C) :=
        mul_le_mul_of_nonneg_right hΛ₁_lt.le hw1
      have h2 : μ₁ * deriv Λ μ₁ * (x / C) < μ₂ * deriv Λ μ₂ * (x / C) :=
        mul_lt_mul_of_pos_right hprod_lt hw2_pos
      dsimp only [rhs]
      linarith
  have hrhs_cont_μ : ∀ x, ContinuousOn (fun μ => rhs μ x) (Ioi 0) := fun x =>
    (hΛ_cont.mul continuousOn_const).add ((continuousOn_id.mul hΛ'_cont).mul continuousOn_const)
  set KKT_i : ι → ℝ → ℝ → Prop := fun i μ x =>
    x ∈ Icc 0 C ∧ lhs i x ≤ rhs μ x ∧ (0 < x → lhs i x = rhs μ x)
  have hex_sol : ∀ i (μ : ℝ), 0 < μ → ∃! x, KKT_i i μ x := by
    intro i μ hμ
    have huniq : ∀ x₁ x₂, KKT_i i μ x₁ → KKT_i i μ x₂ → x₁ = x₂ := by
      intro x₁ x₂ h₁ h₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hx₂_pos : 0 < x₂ := lt_of_le_of_lt h₁.1.1 hlt
        have hl_lt := hlhs_anti i h₁.1 h₂.1 hlt
        have hr_le := hrhs_mono_x μ hμ h₁.1 h₂.1 hlt.le
        linarith [h₁.2.1, h₂.2.2 hx₂_pos]
      · have hx₁_pos : 0 < x₁ := lt_of_le_of_lt h₂.1.1 hgt
        have hl_lt := hlhs_anti i h₂.1 h₁.1 hgt
        have hr_le := hrhs_mono_x μ hμ h₂.1 h₁.1 hgt.le
        linarith [h₂.2.1, h₁.2.2 hx₁_pos]
    rcases le_or_gt (lhs i 0) (Λ μ) with h0_le | h0_gt
    · refine ⟨0, ⟨⟨le_rfl, hC.le⟩, ?_, fun h => absurd h (lt_irrefl 0)⟩,
        fun y hy => huniq y 0 hy ⟨⟨le_rfl, hC.le⟩, ?_, fun h => absurd h (lt_irrefl 0)⟩⟩
      · simpa only [rhs, zero_div, sub_zero, mul_one, mul_zero, add_zero] using h0_le
      · simpa only [rhs, zero_div, sub_zero, mul_one, mul_zero, add_zero] using h0_le
    · set g : ℝ → ℝ := fun x => lhs i x - rhs μ x
      have hg_cont : ContinuousOn g (Icc 0 C) :=
        (hlhs_cont i).sub
          ((continuousOn_const.mul (continuousOn_const.sub (continuousOn_id.div_const C))).add
            (continuousOn_const.mul (continuousOn_id.div_const C)))
      have hg0 : 0 < g 0 := by
        dsimp only [g, rhs]
        rw [zero_div, sub_zero, mul_one, mul_zero, add_zero]
        linarith
      have hgC : g C < 0 := by
        dsimp only [g, lhs, rhs]
        rw [div_self hC.ne', sub_self, mul_zero, mul_zero, zero_add, mul_one]
        have hΛμ_pos : 0 < Λ μ := (hΛ_spec μ hμ).2
        have hel := hΛ_elast μ hμ
        linarith
      obtain ⟨xStar, hx_mem, hgx⟩ := intermediate_value_Icc' hC.le hg_cont ⟨hgC.le, hg0.le⟩
      have hx_pos : 0 < xStar := lt_of_le_of_ne hx_mem.1 fun h0 => by
        rw [← h0] at hgx; linarith
      have heq_x : lhs i xStar = rhs μ xStar := sub_eq_zero.mp hgx
      have hkkt : KKT_i i μ xStar := ⟨hx_mem, heq_x.le, fun _ => heq_x⟩
      exact ⟨xStar, hkkt, fun y hy => huniq y xStar hy hkkt⟩
  let sol : ι → ℝ → ℝ := fun i μ => if hμ : 0 < μ then Classical.choose (hex_sol i μ hμ) else 0
  have hsol_spec : ∀ i {μ : ℝ} (hμ : 0 < μ), KKT_i i μ (sol i μ) := by
    intro i μ hμ
    dsimp only [sol]
    split_ifs
    exact (Classical.choose_spec (hex_sol i μ hμ)).1
  have hsol_eq_iff : ∀ i {μ : ℝ} (hμ : 0 < μ) {x : ℝ}, sol i μ = x ↔ KKT_i i μ x := by
    intro i μ hμ x
    have hsp := hsol_spec i hμ
    obtain ⟨_, _, hu⟩ := hex_sol i μ hμ
    exact ⟨fun h => h ▸ hsp, fun hx => (hu _ hsp).trans (hu _ hx).symm⟩
  have hsol_lt_C : ∀ i {μ : ℝ} (hμ : 0 < μ), sol i μ < C := by
    intro i μ hμ
    have hsp := hsol_spec i hμ
    refine lt_of_le_of_ne hsp.1.2 fun heqC => ?_
    have heq := hsp.2.2 (heqC ▸ hC)
    rw [heqC] at heq
    dsimp only [lhs, rhs] at heq
    rw [div_self hC.ne', sub_self, mul_zero, mul_zero, zero_add, mul_one] at heq
    have hΛμ_pos : 0 < Λ μ := (hΛ_spec μ hμ).2
    linarith [hΛ_elast μ hμ]
  have hsol_anti : ∀ i {μ₁ μ₂ : ℝ}, 0 < μ₁ → μ₁ < μ₂ →
      sol i μ₂ ≤ sol i μ₁ ∧ (0 < sol i μ₁ → sol i μ₂ < sol i μ₁) := by
    intro i μ₁ μ₂ hμ₁ hlt
    have hμ₂ : 0 < μ₂ := lt_trans hμ₁ hlt
    have h1 := hsol_spec i hμ₁
    have h2 := hsol_spec i hμ₂
    have hle : sol i μ₂ ≤ sol i μ₁ := by
      by_contra hgt
      push Not at hgt
      have hx₂_pos : 0 < sol i μ₂ := lt_of_le_of_lt h1.1.1 hgt
      have hl_lt := hlhs_anti i h1.1 h2.1 hgt
      have hr_le := hrhs_mono_x μ₁ hμ₁ h1.1 h2.1 hgt.le
      have hr_μ := hrhs_strict_μ (sol i μ₂) h2.1 hμ₁ hμ₂ hlt
      linarith [h1.2.1, h2.2.2 hx₂_pos]
    refine ⟨hle, fun hpos₁ => lt_of_le_of_ne hle fun heq => ?_⟩
    have heq₁ := h1.2.2 hpos₁
    have heq₂ := h2.2.2 (heq.symm ▸ hpos₁)
    rw [heq] at heq₂
    have hr_μ : rhs μ₁ (sol i μ₁) < rhs μ₂ (sol i μ₁) :=
      hrhs_strict_μ (sol i μ₁) h1.1 hμ₁ hμ₂ hlt
    linarith
  have hsol_cont : ∀ i, ContinuousOn (sol i) (Ioi 0) := by
    intro i μ₀ hμ₀
    have hμ₀_pos : 0 < μ₀ := mem_Ioi.mp hμ₀
    refine (Metric.continuousAt_iff.mpr fun ε hε => ?_).continuousWithinAt
    set x₀ := sol i μ₀
    have hx₀_sp := hsol_spec i hμ₀_pos
    have hx₀_lt_C : x₀ < C := hsol_lt_C i hμ₀_pos
    set x_hi := min C (x₀ + ε / 2)
    have hx_hi_gt : x₀ < x_hi := lt_min hx₀_lt_C (by linarith)
    have hx_hi_mem : x_hi ∈ Icc 0 C := ⟨by linarith [hx₀_sp.1.1], min_le_left _ _⟩
    have hgap_hi : lhs i x_hi < rhs μ₀ x_hi := by
      have hl := hlhs_anti i hx₀_sp.1 hx_hi_mem hx_hi_gt
      have hr := hrhs_mono_x μ₀ hμ₀_pos hx₀_sp.1 hx_hi_mem hx_hi_gt.le
      linarith [hx₀_sp.2.1]
    have hhi_ev : ∀ᶠ μ in 𝓝 μ₀, lhs i x_hi < rhs μ x_hi :=
      ((hrhs_cont_μ x_hi).continuousAt (Ioi_mem_nhds hμ₀_pos)).preimage_mem_nhds
        (Ioi_mem_nhds hgap_hi)
    rcases eq_or_lt_of_le hx₀_sp.1.1 with hx₀_0 | hx₀_pos
    · have hnhds : {μ : ℝ | 0 < μ ∧ lhs i x_hi < rhs μ x_hi} ∈ 𝓝 μ₀ :=
        Filter.inter_mem (Ioi_mem_nhds hμ₀_pos) hhi_ev
      obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hnhds
      refine ⟨δ, hδ_pos, fun μ hμ_dist => ?_⟩
      obtain ⟨hμ_pos, hμ_hi⟩ := hδ_ball hμ_dist
      have hsp := hsol_spec i hμ_pos
      have hlt_hi : sol i μ < x_hi := by
        by_contra hge
        push Not at hge
        have hl : lhs i (sol i μ) ≤ lhs i x_hi := by
          rcases eq_or_lt_of_le hge with heq | hgt
          · rw [heq]
          · exact (hlhs_anti i hx_hi_mem hsp.1 hgt).le
        have hr := hrhs_mono_x μ hμ_pos hx_hi_mem hsp.1 hge
        have hpos_sol : 0 < sol i μ := lt_of_le_of_lt hx₀_sp.1.1 (lt_of_lt_of_le hx_hi_gt hge)
        linarith [hsp.2.2 hpos_sol]
      rw [Real.dist_eq, abs_lt]
      have : x_hi ≤ x₀ + ε / 2 := min_le_right _ _
      exact ⟨by linarith [hsp.1.1, hx₀_0], by linarith⟩
    · set x_lo := max 0 (x₀ - ε / 2)
      have hx_lo_lt : x_lo < x₀ := max_lt hx₀_pos (by linarith)
      have hx_lo_mem : x_lo ∈ Icc 0 C := ⟨le_max_left _ _, by linarith [hx₀_sp.1.2]⟩
      have hgap_lo : rhs μ₀ x_lo < lhs i x_lo := by
        have hl := hlhs_anti i hx_lo_mem hx₀_sp.1 hx_lo_lt
        have hr := hrhs_mono_x μ₀ hμ₀_pos hx_lo_mem hx₀_sp.1 hx_lo_lt.le
        linarith [hx₀_sp.2.2 hx₀_pos]
      have hlo_ev : ∀ᶠ μ in 𝓝 μ₀, rhs μ x_lo < lhs i x_lo :=
        ((hrhs_cont_μ x_lo).continuousAt (Ioi_mem_nhds hμ₀_pos)).preimage_mem_nhds
          (Iio_mem_nhds hgap_lo)
      have hnhds : {μ : ℝ | 0 < μ ∧ lhs i x_hi < rhs μ x_hi ∧ rhs μ x_lo < lhs i x_lo} ∈ 𝓝 μ₀ :=
        Filter.inter_mem (Ioi_mem_nhds hμ₀_pos) (Filter.inter_mem hhi_ev hlo_ev)
      obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hnhds
      refine ⟨δ, hδ_pos, fun μ hμ_dist => ?_⟩
      obtain ⟨hμ_pos, hμ_hi, hμ_lo⟩ := hδ_ball hμ_dist
      have hsp := hsol_spec i hμ_pos
      have hlt_hi : sol i μ < x_hi := by
        by_contra hge
        push Not at hge
        have hl : lhs i (sol i μ) ≤ lhs i x_hi := by
          rcases eq_or_lt_of_le hge with heq | hgt
          · rw [heq]
          · exact (hlhs_anti i hx_hi_mem hsp.1 hgt).le
        have hr := hrhs_mono_x μ hμ_pos hx_hi_mem hsp.1 hge
        have hpos_sol : 0 < sol i μ := lt_of_lt_of_le (lt_trans hx₀_pos hx_hi_gt) hge
        linarith [hsp.2.2 hpos_sol]
      have hgt_lo : x_lo < sol i μ := by
        by_contra hle
        push Not at hle
        have hl : lhs i x_lo ≤ lhs i (sol i μ) := by
          rcases eq_or_lt_of_le hle with heq | hlt
          · rw [heq]
          · exact (hlhs_anti i hsp.1 hx_lo_mem hlt).le
        have hr := hrhs_mono_x μ hμ_pos hsp.1 hx_lo_mem hle
        linarith [hsp.2.1]
      rw [Real.dist_eq, abs_lt]
      have : x_hi ≤ x₀ + ε / 2 := min_le_right _ _
      have : x₀ - ε / 2 ≤ x_lo := le_max_right _ _
      exact ⟨by linarith, by linarith⟩
  set M_hi := (∑ i, lhs i 0) + 1
  have hM_hi_pos : 0 < M_hi := by
    have : 0 ≤ ∑ i, lhs i 0 := Finset.sum_nonneg fun i _ => by
      dsimp only [lhs]; rw [zero_div, sub_zero, mul_one]
      exact ((hU i).derivWithin_pos le_rfl).le
    dsimp only [M_hi]; linarith
  set μ_hi := B M_hi
  have hμ_hi_pos : 0 < μ_hi := hB_bij.mapsTo hM_hi_pos
  have hΛ_hi : Λ μ_hi = M_hi := hΛB M_hi hM_hi_pos
  have hsum_hi : ∑ i, sol i μ_hi = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsol_eq_iff i hμ_hi_pos]
    have hl0_nonneg : ∀ j, 0 ≤ lhs j 0 := fun j => by
      dsimp only [lhs]; rw [zero_div, sub_zero, mul_one]
      exact ((hU j).derivWithin_pos le_rfl).le
    have hle_M : lhs i 0 ≤ M_hi := by
      have := Finset.single_le_sum (fun j _ => hl0_nonneg j) (Finset.mem_univ i)
      dsimp only [M_hi]; linarith
    refine ⟨⟨le_rfl, hC.le⟩, ?_, fun h => absurd h (lt_irrefl 0)⟩
    dsimp only [rhs]
    rw [zero_div, sub_zero, mul_one, mul_zero, add_zero, hΛ_hi]
    exact hle_M
  set x_mid := C * (3 / 4)
  have hx_mid_mem : x_mid ∈ Icc 0 C :=
    ⟨by dsimp only [x_mid]; positivity, by dsimp only [x_mid]; linarith⟩
  obtain ⟨i_min, -, hi_min_le⟩ := Finset.exists_min_image Finset.univ (fun i => lhs i x_mid)
    Finset.univ_nonempty
  set m_lo := lhs i_min x_mid
  have hm_lo_pos : 0 < m_lo := by
    dsimp only [m_lo, lhs, x_mid]
    have : 1 - C * (3 / 4) / C = 1 / 4 := by field_simp [hC.ne']; ring
    rw [this]
    exact mul_pos ((hU i_min).derivWithin_pos hx_mid_mem.1) (by norm_num)
  set μ_lo := B (m_lo / 2) / 2
  have hμ_lo_pos : 0 < μ_lo := half_pos (hB_bij.mapsTo (half_pos hm_lo_pos))
  have hΛ_2μ_lo : Λ (2 * μ_lo) = m_lo / 2 := by
    have h2 : 2 * μ_lo = B (m_lo / 2) := by dsimp only [μ_lo]; ring
    rw [h2, hΛB _ (half_pos hm_lo_pos)]
  have hsum_lo : C < ∑ i, sol i μ_lo := by
    have hdΛ_lo : HasDerivAt Λ (deriv Λ μ_lo) μ_lo :=
      ((hΛ_diff μ_lo hμ_lo_pos).differentiableAt (Ioi_mem_nhds hμ_lo_pos)).hasDerivAt
    have htan_lo := hΛ_conv.add_le_of_hasFDerivAt hμ_lo_pos
      (mem_Ioi.mpr (by positivity : 0 < 2 * μ_lo)) hdΛ_lo.hasFDerivAt
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at htan_lo
    have h2sub : 2 * μ_lo - μ_lo = μ_lo := by ring
    rw [h2sub, hΛ_2μ_lo] at htan_lo
    have hΛ_lo_pos : 0 < Λ μ_lo := (hΛ_spec μ_lo hμ_lo_pos).2
    have hrhs_lt : rhs μ_lo x_mid < m_lo := by
      dsimp only [rhs, x_mid]
      have h1 : 1 - C * (3 / 4) / C = 1 / 4 := by field_simp [hC.ne']; ring
      have h2 : C * (3 / 4) / C = 3 / 4 := by field_simp [hC.ne']
      rw [h1, h2]
      linarith [hΛ_elast μ_lo hμ_lo_pos]
    have hgt_mid : ∀ i, x_mid < sol i μ_lo := fun i => by
      have hsp := hsol_spec i hμ_lo_pos
      by_contra hle
      push Not at hle
      have hl : lhs i x_mid ≤ lhs i (sol i μ_lo) := by
        rcases eq_or_lt_of_le hle with heq | hlt
        · rw [heq]
        · exact (hlhs_anti i hsp.1 hx_mid_mem hlt).le
      have hr := hrhs_mono_x μ_lo hμ_lo_pos hsp.1 hx_mid_mem hle
      have hmin := hi_min_le i (Finset.mem_univ i)
      linarith [hsp.2.1]
    have hsum_ge : ∑ _i : ι, x_mid ≤ ∑ i, sol i μ_lo :=
      Finset.sum_le_sum fun i _ => (hgt_mid i).le
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum_ge
    have hcard_r : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
    dsimp only [x_mid] at hsum_ge
    nlinarith
  have hμ_lo_lt_hi : μ_lo < μ_hi := by
    by_contra hge
    push Not at hge
    have hsum_le : ∑ i, sol i μ_lo ≤ ∑ i, sol i μ_hi :=
      Finset.sum_le_sum fun i _ => by
        rcases eq_or_lt_of_le hge with heq | hlt
        · rw [heq]
        · exact (hsol_anti i hμ_hi_pos hlt).1
    linarith
  have hS_cont : ContinuousOn (fun μ => ∑ i, sol i μ) (Icc μ_lo μ_hi) :=
    continuousOn_finsetSum _ fun i _ =>
      (hsol_cont i).mono fun μ hμ => lt_of_lt_of_le hμ_lo_pos hμ.1
  obtain ⟨μStar, hμStar_mem, hsumStar⟩ :=
    intermediate_value_Icc' hμ_lo_lt_hi.le hS_cont ⟨by linarith, hsum_lo.le⟩
  have hμStar_pos : 0 < μStar := lt_of_lt_of_le hμ_lo_pos hμStar_mem.1
  set dStar : ι → ℝ := fun i => sol i μStar
  set θStar : ι → ℝ := fun i => μStar * dStar i
  have hθStar0 : ∀ i, 0 ≤ θStar i := fun i =>
    mul_nonneg hμStar_pos.le (hsol_spec i hμStar_pos).1.1
  have hsum_θStar : ∑ i, θStar i = μStar * C := by
    simp only [θStar, ← Finset.mul_sum, dStar, hsumStar]
  have hμ_θStar : (∑ i, θStar i) / C = μStar := by
    rw [hsum_θStar, mul_div_cancel_right₀ _ hC.ne']
  have hallocStar : G.allocation θStar = dStar := by
    funext i
    have hCap_ne : G.capacity ≠ 0 := hC.ne'
    simp only [KellyGame.allocation, hsum_θStar, θStar]
    field_simp [hCap_ne, hC.ne', hμStar_pos.ne']
    dsimp only [C]
    ring
  have heraseStar : ∀ i, 0 < ∑ j ∈ Finset.univ.erase i, θStar j := fun i => by
    have hsum_e : ∑ j ∈ Finset.univ.erase i, dStar j = C - dStar i := by
      have := Finset.add_sum_erase Finset.univ dStar (Finset.mem_univ i)
      linarith [hsumStar]
    have hwe : ∑ j ∈ Finset.univ.erase i, θStar j = μStar * (C - dStar i) := by
      simp only [θStar, ← Finset.mul_sum, hsum_e]
    rw [hwe]
    exact mul_pos hμStar_pos (sub_pos.mpr (hsol_lt_C i hμStar_pos))
  have hneStar : IsMarketNashEquilibrium D G θStar := by
    rw [hD.isMarketNashEquilibrium_iff_kkt hcard hC hU]
    refine ⟨hθStar0, heraseStar, fun i => ?_, fun i hdi => ?_⟩
    · rw [hallocStar, hμ_θStar]
      exact (hsol_spec i hμStar_pos).2.1
    · rw [hallocStar] at hdi ⊢
      rw [hμ_θStar]
      exact (hsol_spec i hμStar_pos).2.2 hdi
  refine ⟨θStar, hneStar, fun θ hne => ?_⟩
  obtain ⟨hθ0, herase, hle, heq⟩ := (hD.isMarketNashEquilibrium_iff_kkt hcard hC hU).mp hne
  set μ := (∑ j, θ j) / C
  have hW_pos : 0 < ∑ j, θ j := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    linarith [hθ0 i₀, herase i₀]
  have hμ_pos : 0 < μ := div_pos hW_pos hC
  have hd_eq_sol : ∀ i, G.allocation θ i = sol i μ := fun i => by
    symm
    rw [hsol_eq_iff i hμ_pos]
    have hfeas := G.isFeasibleAllocation_allocation hC.le hθ0
    exact ⟨⟨hfeas.1 i, G.isFeasibleAllocation_le_capacity hfeas i⟩, hle i, heq i⟩
  have hsum_sol_μ : ∑ i, sol i μ = C := by
    rw [← Finset.sum_congr rfl fun i _ => hd_eq_sol i]
    exact G.sum_allocation_eq_capacity hW_pos.ne'
  have hμ_eq : μ = μStar := by
    by_contra hne_μ
    have hex_pos : ∀ m, 0 < m → ∑ i, sol i m = C → ∃ i₀, 0 < sol i₀ m := fun m hm hsm => by
      by_contra hall
      push Not at hall
      have h0 : ∑ i, sol i m ≤ 0 := Finset.sum_nonpos fun i _ => hall i
      linarith
    rcases lt_or_gt_of_ne hne_μ with hlt | hgt
    · obtain ⟨i₀, hi₀⟩ := hex_pos μ hμ_pos hsum_sol_μ
      have hsum_lt : ∑ i, sol i μStar < ∑ i, sol i μ :=
        Finset.sum_lt_sum (fun i _ => (hsol_anti i hμ_pos hlt).1)
          ⟨i₀, Finset.mem_univ i₀, (hsol_anti i₀ hμ_pos hlt).2 hi₀⟩
      linarith
    · obtain ⟨i₀, hi₀⟩ := hex_pos μStar hμStar_pos hsumStar
      have hsum_lt : ∑ i, sol i μ < ∑ i, sol i μStar :=
        Finset.sum_lt_sum (fun i _ => (hsol_anti i hμStar_pos hgt).1)
          ⟨i₀, Finset.mem_univ i₀, (hsol_anti i₀ hμStar_pos hgt).2 hi₀⟩
      linarith
  funext i
  have halloc_i := G.allocation_eq_div_price (w := θ) hC.ne' i
  have hprice_eq : G.price θ = μStar := by simp only [KellyGame.price, ← hμ_eq, μ, C]
  rw [hprice_eq, hd_eq_sol i, hμ_eq] at halloc_i
  calc θ i = μStar * (θ i / μStar) := (mul_div_cancel₀ (θ i) hμStar_pos.ne').symm
    _ = μStar * dStar i := by rw [← halloc_i]

end NashEquilibrium

/-! ### Properties of `elasticityEfficiencyBound` (`G(c)`) -/

section ElasticityBound

@[simp]
theorem elasticityEfficiencyBound_one : elasticityEfficiencyBound 1 = 3 / 4 := by
  rw [elasticityEfficiencyBound_def, Real.sqrt_one]
  norm_num

/-- Equivalence with Eq. (21.38) of [Johari2007] (p. 558) for `c > 1`:
`G(c) = (2 c √c - 3 c + 1) / (c - 1) ^ 2`. -/
theorem elasticityEfficiencyBound_eq_of_one_lt {c : ℝ} (hc : 1 < c) :
    elasticityEfficiencyBound c = (2 * c * Real.sqrt c - 3 * c + 1) / (c - 1) ^ 2 := by
  rw [elasticityEfficiencyBound_def]
  set s := Real.sqrt c
  have hs_gt : 1 < s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hc
  have hs_sq : s ^ 2 = c := Real.sq_sqrt (by linarith)
  have hsub_ne : s - 1 ≠ 0 := by linarith
  have hadd_ne : s + 1 ≠ 0 := by linarith
  have hc_ne : c - 1 ≠ 0 := by linarith
  rw [← hs_sq]
  field_simp [hsub_ne, hadd_ne, (show s ^ 2 - 1 ≠ 0 by nlinarith)]
  ring

/-- `elasticityEfficiencyBound` (`G(c)`) is strictly decreasing on `[1, ∞)` ([Johari2007],
Figure 21.1, p. 558). -/
theorem elasticityEfficiencyBound_strictAntiOn :
    StrictAntiOn elasticityEfficiencyBound (Ici 1) := by
  intro c₁ hc₁ c₂ hc₂ hlt
  rw [elasticityEfficiencyBound_def, elasticityEfficiencyBound_def]
  set s₁ := Real.sqrt c₁
  set s₂ := Real.sqrt c₂
  have hs₁_ge : 1 ≤ s₁ := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hc₁
  have hs_lt : s₁ < s₂ := Real.sqrt_lt_sqrt (by linarith [mem_Ici.mp hc₁]) hlt
  have hd₁ : 0 < (s₁ + 1) ^ 2 := by positivity
  have hd₂ : 0 < (s₂ + 1) ^ 2 := by positivity
  rw [div_lt_div_iff₀ hd₂ hd₁]
  have hdiff : (2 * s₁ + 1) * (s₂ + 1) ^ 2 - (2 * s₂ + 1) * (s₁ + 1) ^ 2 =
      (s₂ - s₁) * (2 * s₁ * s₂ + s₁ + s₂) := by ring
  have hpos : 0 < (s₂ - s₁) * (2 * s₁ * s₂ + s₁ + s₂) :=
    mul_pos (by linarith) (by nlinarith)
  linarith

theorem elasticityEfficiencyBound_le_three_fourths {c : ℝ} (hc : 1 ≤ c) :
    elasticityEfficiencyBound c ≤ 3 / 4 := by
  rw [← elasticityEfficiencyBound_one]
  exact elasticityEfficiencyBound_strictAntiOn.antitoneOn le_rfl hc hc

/-- Algebraic minimization of `F(y; c) = (1 - y)^2 / (1 + (c - 1) y) + y` on `[0, 1]`
([Johari2007], Eq. (21.37), p. 557). -/
private theorem elasticityEfficiencyBound_le_F {c y : ℝ} (hc : 1 ≤ c) (hy0 : 0 ≤ y) :
    elasticityEfficiencyBound c ≤ (1 - y) ^ 2 / (1 + (c - 1) * y) + y := by
  rw [elasticityEfficiencyBound_def]
  set s := Real.sqrt c
  have hs_ge : 1 ≤ s := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc
  have hs_sq : s ^ 2 = c := Real.sq_sqrt (by linarith)
  have hden1 : 0 < 1 + (c - 1) * y := by
    have : 0 ≤ (c - 1) * y := mul_nonneg (by linarith) hy0
    linarith
  have hden2 : 0 < (s + 1) ^ 2 := by positivity
  have h1 : (2 * s + 1) * (1 + (c - 1) * y) ≤
      ((1 - y) ^ 2 + y * (1 + (c - 1) * y)) * (s + 1) ^ 2 := by
    have hdiff : ((1 - y) ^ 2 + y * (1 + (s ^ 2 - 1) * y)) * (s + 1) ^ 2 -
        (2 * s + 1) * (1 + (s ^ 2 - 1) * y) = s ^ 2 * ((s + 1) * y - 1) ^ 2 := by ring
    have hnn : 0 ≤ s ^ 2 * ((s + 1) * y - 1) ^ 2 := by positivity
    rw [← hs_sq]
    linarith
  have h2 : (2 * s + 1) / (s + 1) ^ 2 ≤
      ((1 - y) ^ 2 + y * (1 + (c - 1) * y)) / (1 + (c - 1) * y) :=
    (div_le_div_iff₀ hden2 hden1).mpr h1
  have h3 : ((1 - y) ^ 2 + y * (1 + (c - 1) * y)) / (1 + (c - 1) * y) =
      (1 - y) ^ 2 / (1 + (c - 1) * y) + y := by
    rw [add_div, mul_div_cancel_right₀ _ hden1.ne']
  linarith

end ElasticityBound

/-! ### Steps 7–8 of Theorem 21.10: optimality of proportional sharing -/

section EfficiencyOptimality

private def efficiencyRatioSet (D : ℝ → ℝ → ℝ) : Set ℝ :=
  { ρ : ℝ | ∃ (R : ℕ) (_ : 2 ≤ R) (G : KellyGame (Fin R)) (d θ : Fin R → ℝ),
    0 < G.capacity ∧
    (∀ r, IsAdmissibleUtility (G.utility r)) ∧
    (∀ r, 0 ≤ G.utility r 0) ∧
    G.IsSocialOptimum d ∧
    IsMarketNashEquilibrium D G θ ∧
    ρ = G.welfare (marketAllocation D G.capacity θ) / G.welfare d }

private theorem welfare_pos_of_isSocialOptimum {ι : Type*} [Fintype ι] [Nonempty ι]
    {G : KellyGame ι} {d : ι → ℝ} (hd : G.IsSocialOptimum d) (hC : 0 < G.capacity)
    (hU : ∀ r, IsAdmissibleUtility (G.utility r)) (hU0 : ∀ r, 0 ≤ G.utility r 0) :
    0 < G.welfare d := by
  classical
  have hsum_d : ∑ r, d r = G.capacity :=
    hd.sum_eq_capacity fun r => (hU r).strictMonoOn.mono fun _ hz => hz.1
  have hex_pos : ∃ r₀, 0 < d r₀ := by
    by_contra hall
    push Not at hall
    linarith [Finset.sum_nonpos (s := Finset.univ) fun r _ => hall r]
  obtain ⟨r₀, hr₀⟩ := hex_pos
  unfold KellyGame.welfare
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r₀)]
  have h0 : 0 < G.utility r₀ (d r₀) :=
    lt_of_le_of_lt (hU0 r₀) ((hU r₀).strictMonoOn le_rfl (hd.1.1 r₀) hr₀)
  have hrest : 0 ≤ ∑ r ∈ Finset.univ.erase r₀, G.utility r (d r) :=
    Finset.sum_nonneg fun r _ =>
      le_trans (hU0 r) ((hU r).strictMonoOn.monotoneOn le_rfl (hd.1.1 r) (hd.1.1 r))
  linarith

private theorem bddBelow_efficiencyRatioSet (D : ℝ → ℝ → ℝ) (hD : IsSmoothMarketClearing D) :
    BddBelow (efficiencyRatioSet D) := by
  refine ⟨0, ?_⟩
  rintro ρ ⟨R, hR, G, d, θ, hC, hU, hU0, hd, hne, rfl⟩
  have hfeas_ne := hD.isFeasibleAllocation_marketAllocation (by simpa using hR) hC
    hne.nonneg hne.exists_ne_zero
  have hw_ne_nonneg : 0 ≤ G.welfare (marketAllocation D G.capacity θ) :=
    Finset.sum_nonneg fun r _ => by
      have hmono := (hU r).strictMonoOn.monotoneOn le_rfl (hfeas_ne.1 r) (hfeas_ne.1 r)
      linarith [hU0 r]
  have : Nonempty (Fin R) := Fin.pos_iff_nonempty.mp (by omega)
  exact div_nonneg hw_ne_nonneg (welfare_pos_of_isSocialOptimum hd hC hU hU0).le

private theorem nonempty_efficiencyRatioSet {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D) :
    (efficiencyRatioSet D).Nonempty := by
  set G : KellyGame (Fin 2) := ⟨1, fun _ x => 1 * x⟩
  have hU : ∀ r : Fin 2, IsAdmissibleUtility (G.utility r) :=
    fun _ => KellyGame.isAdmissibleUtility_linear zero_lt_one
  obtain ⟨d, hd⟩ := KellyGame.exists_isSocialOptimum (G := G) zero_le_one
    (fun r => (hU r).continuousOn.mono fun _ hz => hz.1)
  obtain ⟨θ, hne, _⟩ := hD.existsUnique_isMarketNashEquilibrium (G := G) (by decide) zero_lt_one hU
  exact ⟨_, 2, le_rfl, G, d, θ, zero_lt_one, hU, fun _ => by simp [G], hd, hne, rfl⟩

/-- Step 7 of Theorem 21.10 ([Johari2007], p. 557): for every `D ∈ 𝒟` and `μ > 0`,
`efficiencyRatio D ≤ elasticityEfficiencyBound (μ * deriv Λ μ / Λ μ)`. -/
private theorem IsRegularMarketClearing.efficiencyRatio_le_elasticityEfficiencyBound
    {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D) {μ : ℝ} (hμ : 0 < μ) :
    efficiencyRatio D ≤
      elasticityEfficiencyBound (μ * deriv (invPriceScale D) μ / invPriceScale D μ) := by
  obtain ⟨_, _, _, _, _, _, hΛ_spec, _, _, _, hΛ_elast⟩ := hD.priceScale_props
  set Λ := invPriceScale D
  have hΛμ_pos : 0 < Λ μ := (hΛ_spec μ hμ).2
  set c := μ * deriv Λ μ / Λ μ
  have hc_ge : 1 ≤ c := (one_le_div hΛμ_pos).mpr (hΛ_elast μ hμ)
  set s := Real.sqrt c
  have hs_ge : 1 ≤ s := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc_ge
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_ge
  have hs_sq : s ^ 2 = c := Real.sq_sqrt (by linarith)
  have hμd_eq : μ * deriv Λ μ = s ^ 2 * Λ μ := by
    rw [hs_sq]
    dsimp only [c]
    exact (div_mul_cancel₀ _ hΛμ_pos.ne').symm
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set A := (s + 1) * Λ μ
  have hA_pos : 0 < A := by positivity
  set d₁ := 1 / (s + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt (max s (s ^ 4 / (ε * (s + 1) ^ 2) + 1))
  set n := max N 2
  have hn2 : 2 ≤ n := le_max_right N 2
  have hn_gt_max : max s (s ^ 4 / (ε * (s + 1) ^ 2) + 1) < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast le_max_left N 2)
  have hn_gt_s : s < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn_gt_max
  have hn_gt_err : s ^ 4 / (ε * (s + 1) ^ 2) + 1 < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hn_gt_max
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans hs_pos hn_gt_s
  set d := s / ((n : ℝ) * (s + 1))
  have hd_pos : 0 < d := by positivity
  have hd_lt_d₁ : d < d₁ := by
    dsimp only [d, d₁]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hd₁_lt_one : d₁ < 1 := by
    dsimp only [d₁]
    rw [div_lt_one (by positivity)]
    linarith
  have hd_lt_one : d < 1 := lt_trans hd_lt_d₁ hd₁_lt_one
  set α := (Λ μ * (1 - d) + μ * deriv Λ μ * d) / (1 - d)
  have hα_pos : 0 < α := by
    dsimp only [α]
    have h1d : 0 < 1 - d := by linarith
    have hμd_pos : 0 < μ * deriv Λ μ := by rw [hμd_eq]; positivity
    positivity
  have hα_le_A : α ≤ A := by
    dsimp only [α, A]
    rw [hμd_eq, div_le_iff₀ (by linarith)]
    have h1 : d ≤ 1 / (s + 1) := hd_lt_d₁.le
    have h2 : d * (s + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp h1
    have hfac : (s + 1) * Λ μ * (1 - d) - (Λ μ * (1 - d) + s ^ 2 * Λ μ * d) =
        s * Λ μ * (1 - d * (s + 1)) := by ring
    have hnn : 0 ≤ s * Λ μ * (1 - d * (s + 1)) :=
      mul_nonneg (mul_pos hs_pos hΛμ_pos).le (by linarith)
    linarith
  set G_inst : KellyGame (Fin (n + 1)) :=
    ⟨1, fun r x => if r = 0 then A * x else α * x⟩
  have hU_inst : ∀ r : Fin (n + 1), IsAdmissibleUtility (G_inst.utility r) := fun r => by
    dsimp only [G_inst]
    split_ifs
    · exact KellyGame.isAdmissibleUtility_linear hA_pos
    · exact KellyGame.isAdmissibleUtility_linear hα_pos
  have hU0_inst : ∀ r : Fin (n + 1), 0 ≤ G_inst.utility r 0 := fun r => by
    dsimp only [G_inst]; split_ifs <;> simp
  set θ_inst : Fin (n + 1) → ℝ := fun r => if r = 0 then μ * d₁ else μ * d
  have hθ0_inst : ∀ r, 0 ≤ θ_inst r := fun r => by
    dsimp only [θ_inst]; split_ifs <;> positivity
  have hcard_erase0 : (Finset.univ.erase (0 : Fin (n + 1))).card = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]; omega
  have hsum_d_inst : d₁ + (n : ℝ) * d = 1 := by
    dsimp only [d₁, d]
    field_simp [hn_pos.ne', (by positivity : s + 1 ≠ 0)]
    ring
  have hsum_θ_inst : ∑ r : Fin (n + 1), θ_inst r = μ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
    have hrest : ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)), θ_inst r = (n : ℝ) * (μ * d) := by
      have hc : ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)), θ_inst r =
          ∑ _r ∈ Finset.univ.erase (0 : Fin (n + 1)), (μ * d) :=
        Finset.sum_congr rfl fun r hr => by simp [θ_inst, Finset.ne_of_mem_erase hr]
      rw [hc, Finset.sum_const, hcard_erase0, nsmul_eq_mul]
    rw [hrest]
    simp only [θ_inst, ↓reduceIte]
    nlinarith
  have halloc0 : G_inst.allocation θ_inst 0 = d₁ := by
    simp only [KellyGame.allocation, G_inst, hsum_θ_inst, θ_inst, ↓reduceIte, one_mul,
      mul_div_cancel_left₀ _ hμ.ne']
  have halloc_ne : ∀ r : Fin (n + 1), r ≠ 0 → G_inst.allocation θ_inst r = d := fun r hr => by
    simp only [KellyGame.allocation, G_inst, hsum_θ_inst, θ_inst, hr, ↓reduceIte, one_mul,
      mul_div_cancel_left₀ _ hμ.ne']
  have herase_inst : ∀ r : Fin (n + 1), 0 < ∑ j ∈ Finset.univ.erase r, θ_inst j := fun r => by
    have hsplit := Finset.add_sum_erase Finset.univ θ_inst (Finset.mem_univ r)
    rw [hsum_θ_inst] at hsplit
    have hlt_μ : θ_inst r < μ := by
      dsimp only [θ_inst]
      split_ifs <;> nlinarith
    linarith
  have hne_inst : IsMarketNashEquilibrium D G_inst θ_inst := by
    rw [hD.isMarketNashEquilibrium_iff_kkt (by simp; omega) (by simp [G_inst]) hU_inst]
    have hμ_eq : (∑ j, θ_inst j) / G_inst.capacity = μ := by simp [G_inst, hsum_θ_inst]
    have hfoc : ∀ r : Fin (n + 1),
        derivWithin (G_inst.utility r) (Ici 0) (G_inst.allocation θ_inst r) *
          (1 - G_inst.allocation θ_inst r / G_inst.capacity) =
        Λ μ * (1 - G_inst.allocation θ_inst r / G_inst.capacity) +
          μ * deriv Λ μ * (G_inst.allocation θ_inst r / G_inst.capacity) := by
      intro r
      by_cases hr : r = 0
      · subst hr
        rw [halloc0]
        have hu0 : G_inst.utility 0 = fun t => A * t := by funext t; simp [G_inst]
        rw [hu0, KellyGame.derivWithin_linear (by positivity)]
        simp only [G_inst, div_one, hμd_eq, A, d₁]
        field_simp [(by positivity : s + 1 ≠ 0)]
        ring
      · rw [halloc_ne r hr]
        have hur : G_inst.utility r = fun t => α * t := by funext t; simp [G_inst, hr]
        rw [hur, KellyGame.derivWithin_linear hd_pos.le]
        simp only [G_inst, div_one, α]
        exact div_mul_cancel₀ _ (by linarith)
    refine ⟨hθ0_inst, herase_inst, fun r => ?_, fun r _ => ?_⟩
    · rw [hμ_eq]; exact (hfoc r).le
    · rw [hμ_eq]; exact hfoc r
  set opt : Fin (n + 1) → ℝ := Pi.single 0 1
  have hopt_w : G_inst.welfare opt = A := by
    rw [KellyGame.welfare, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
    have hrest : ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)), G_inst.utility r (opt r) = 0 :=
      Finset.sum_eq_zero fun r hr => by
        simp [opt, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hr), G_inst]
    rw [hrest]
    simp [opt, G_inst]
  have hopt_inst : G_inst.IsSocialOptimum opt := by
    refine ⟨⟨fun r => by by_cases hr : r = 0 <;> simp [opt, hr], by simp [opt, G_inst]⟩,
      fun x hx => ?_⟩
    rw [hopt_w]
    calc G_inst.welfare x = ∑ r, G_inst.utility r (x r) := rfl
      _ ≤ ∑ r, A * x r := Finset.sum_le_sum fun r _ => by
          dsimp only [G_inst]
          split_ifs
          · exact le_rfl
          · exact mul_le_mul_of_nonneg_right hα_le_A (hx.1 r)
      _ = A * ∑ r, x r := (Finset.mul_sum ..).symm
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hx.2 hA_pos.le
      _ = A := mul_one A
  have hne_alloc_eq : marketAllocation D G_inst.capacity θ_inst = G_inst.allocation θ_inst :=
    hD.marketAllocation_eq_kellyAllocation (by simp; omega) (by simp [G_inst])
      hθ0_inst hne_inst.exists_ne_zero
  have hne_w : G_inst.welfare (marketAllocation D G_inst.capacity θ_inst) =
      A * d₁ + (n : ℝ) * (α * d) := by
    rw [hne_alloc_eq, KellyGame.welfare,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
    have hrest : ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)),
        G_inst.utility r (G_inst.allocation θ_inst r) = (n : ℝ) * (α * d) := by
      have hc : ∑ r ∈ Finset.univ.erase (0 : Fin (n + 1)),
          G_inst.utility r (G_inst.allocation θ_inst r) =
          ∑ _r ∈ Finset.univ.erase (0 : Fin (n + 1)), (α * d) :=
        Finset.sum_congr rfl fun r hr => by
          have hr0 := Finset.ne_of_mem_erase hr
          rw [halloc_ne r hr0]
          simp [G_inst, hr0]
      rw [hc, Finset.sum_const, hcard_erase0, nsmul_eq_mul]
    rw [hrest, halloc0]
    simp [G_inst]
  have hmem : G_inst.welfare (marketAllocation D G_inst.capacity θ_inst) / G_inst.welfare opt ∈
      efficiencyRatioSet D :=
    ⟨n + 1, by omega, G_inst, opt, θ_inst, by simp [G_inst], hU_inst, hU0_inst, hopt_inst,
      hne_inst, rfl⟩
  have hle_inf : efficiencyRatio D ≤
      G_inst.welfare (marketAllocation D G_inst.capacity θ_inst) / G_inst.welfare opt :=
    csInf_le (bddBelow_efficiencyRatioSet D hD.smooth) hmem
  have hratio_eq :
      G_inst.welfare (marketAllocation D G_inst.capacity θ_inst) / G_inst.welfare opt =
        elasticityEfficiencyBound c + s ^ 3 / (s + 1) ^ 2 * (d / (1 - d)) := by
    rw [hne_w, hopt_w, elasticityEfficiencyBound_def]
    change (A * d₁ + (n : ℝ) * (α * d)) / A =
      (2 * s + 1) / (s + 1) ^ 2 + s ^ 3 / (s + 1) ^ 2 * (d / (1 - d))
    have hnd : (n : ℝ) * d = s / (s + 1) := by
      dsimp only [d]; field_simp [hn_pos.ne', (by positivity : s + 1 ≠ 0)]
    have hmul_nd : (n : ℝ) * (α * d) = α * ((n : ℝ) * d) := by ring
    rw [hmul_nd, hnd]
    dsimp only [A, d₁, α]
    rw [hμd_eq]
    have h1d_ne : 1 - d ≠ 0 := by linarith
    field_simp [hΛμ_pos.ne', (by positivity : s + 1 ≠ 0), h1d_ne]
    ring
  have herr_lt : s ^ 3 / (s + 1) ^ 2 * (d / (1 - d)) < ε := by
    have hden_pos : 0 < (n : ℝ) * (s + 1) - s := by
      have : s * 1 < (n : ℝ) * (s + 1) :=
        mul_lt_mul hn_gt_s (by linarith) zero_lt_one (by positivity)
      linarith
    have hd_sub : d / (1 - d) = s / ((n : ℝ) * (s + 1) - s) := by
      have h1d_ne : 1 - s / ((n : ℝ) * (s + 1)) ≠ 0 := by
        change 1 - d ≠ 0; linarith
      dsimp only [d]
      field_simp [hn_pos.ne', (by positivity : s + 1 ≠ 0), hden_pos.ne', h1d_ne]
    rw [hd_sub, div_mul_div_comm]
    have hs4 : s ^ 3 * s = s ^ 4 := by ring
    rw [hs4, div_lt_iff₀ (mul_pos (by positivity) hden_pos)]
    have h1 : s ^ 4 / (ε * (s + 1) ^ 2) < (n : ℝ) - 1 := by linarith [hn_gt_err]
    have h2 : s ^ 4 < ((n : ℝ) - 1) * (ε * (s + 1) ^ 2) :=
      (div_lt_iff₀ (by positivity)).mp h1
    have hn1_pos : 0 < (n : ℝ) - 1 := by linarith [hn_gt_s, hs_ge]
    have hle1 : (n : ℝ) - 1 ≤ (n : ℝ) * (s + 1) - s := by
      have : 0 ≤ ((n : ℝ) - 1) * s := mul_nonneg hn1_pos.le hs_pos.le
      linarith
    have hle2 : ((n : ℝ) - 1) * (ε * (s + 1) ^ 2) ≤
        ε * ((s + 1) ^ 2 * ((n : ℝ) * (s + 1) - s)) := by
      have hpos_e : 0 ≤ ε * (s + 1) ^ 2 := by positivity
      have hm := mul_le_mul_of_nonneg_right hle1 hpos_e
      have hid : ((n : ℝ) * (s + 1) - s) * (ε * (s + 1) ^ 2) =
          ε * ((s + 1) ^ 2 * ((n : ℝ) * (s + 1) - s)) := by ring
      linarith
    exact lt_of_lt_of_le h2 hle2
  linarith

/-- **Upper bound on the efficiency of mechanisms in `𝒟`** ([Johari2007], §21.3,
Theorem 21.10(iii); [JohariTsitsiklis2009]): every regular smooth market-clearing
mechanism `D ∈ 𝒟` has worst-case price-anticipating Nash efficiency ratio at most `3 / 4`. -/
theorem IsRegularMarketClearing.efficiencyRatio_le_three_fourths {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) :
    efficiencyRatio D ≤ 3 / 4 := by
  obtain ⟨_, _, _, _, _, _, hΛ_spec, _, _, _, hΛ_elast⟩ := hD.priceScale_props
  have h1 := hD.efficiencyRatio_le_elasticityEfficiencyBound zero_lt_one
  have hc_ge : 1 ≤ 1 * deriv (invPriceScale D) 1 / invPriceScale D 1 :=
    (one_le_div (hΛ_spec 1 zero_lt_one).2).mpr (hΛ_elast 1 zero_lt_one)
  exact h1.trans (elasticityEfficiencyBound_le_three_fourths hc_ge)

/-- Any mechanism `D ∈ 𝒟` of the rescaled Kelly form `D(p, θ) = Δ * θ / p` (`Δ > 0`) achieves
exact worst-case efficiency ratio `3 / 4`. -/
private theorem IsRegularMarketClearing.efficiencyRatio_eq_three_fourths_of_scaledKelly
    {D : ℝ → ℝ → ℝ} (hD : IsRegularMarketClearing D) {Δ : ℝ} (hΔ : 0 < Δ)
    (hD_eq : ∀ p, 0 < p → ∀ θ, 0 ≤ θ → D p θ = Δ * θ / p) :
    efficiencyRatio D = 3 / 4 := by
  have hclear_eq : ∀ {R : ℕ}, 2 ≤ R → ∀ {C : ℝ}, 0 < C →
      ∀ {θ : Fin R → ℝ}, (∀ i, 0 ≤ θ i) → (∃ i, θ i ≠ 0) →
        clearingPrice D C θ = Δ * (∑ i, θ i) / C := by
    intro R hR C hC θ hθ hne
    obtain ⟨i₀, hi₀⟩ := hne
    have hW_pos : 0 < ∑ i, θ i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have : 0 < θ i₀ := lt_of_le_of_ne (hθ i₀) (Ne.symm hi₀)
      have : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, θ i := Finset.sum_nonneg fun i _ => hθ i
      linarith
    set pStar := Δ * (∑ i, θ i) / C
    have hpStar_pos : 0 < pStar := by positivity
    rw [hD.smooth.clearingPrice_eq_iff (by simpa using hR) hC hθ ⟨i₀, hi₀⟩]
    refine ⟨hpStar_pos, ?_⟩
    have hc : ∑ i, D pStar (θ i) = ∑ i, Δ * θ i / pStar :=
      Finset.sum_congr rfl fun i _ => hD_eq pStar hpStar_pos (θ i) (hθ i)
    rw [hc, ← Finset.sum_div, ← Finset.mul_sum]
    dsimp only [pStar]
    field_simp [hΔ.ne', hW_pos.ne', hC.ne']
  refine le_antisymm hD.efficiencyRatio_le_three_fourths ?_
  refine le_csInf (nonempty_efficiencyRatioSet hD) ?_
  rintro ρ ⟨R, hR, G, d, θ, hC, hU, hU0, hd, hne, rfl⟩
  set w : Fin R → ℝ := fun r => Δ * θ r
  have herase_θ : ∀ r, 0 < ∑ s ∈ Finset.univ.erase r, θ s :=
    fun r => hne.sum_erase_pos hD (by simpa using hR) hC r
  have hkelly_ne : G.IsNashEquilibrium w := by
    refine ⟨fun r => mul_nonneg hΔ.le (hne.nonneg r), fun r t ht0 => ?_⟩
    have hnz_other : ∃ s, s ≠ r ∧ θ s ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : ∑ s ∈ Finset.univ.erase r, θ s = 0 :=
        Finset.sum_eq_zero fun s hs => hall s (Finset.ne_of_mem_erase hs)
      linarith [herase_θ r]
    obtain ⟨k₀, hk₀_ne, hk₀_nz⟩ := hnz_other
    have hnz_upd : ∃ j, Function.update θ r (t / Δ) j ≠ 0 :=
      ⟨k₀, by simp [Function.update_of_ne hk₀_ne, hk₀_nz]⟩
    have hbr := hne.best_response r (t / Δ) (div_nonneg ht0 hΔ.le) hnz_upd
    have hpay_eq : ∀ θb : Fin R → ℝ, (∀ j, 0 ≤ θb j) → (∃ j, θb j ≠ 0) →
        marketPayoff D G θb r = G.payoff (fun j => Δ * θb j) r := by
      intro θb hθb0 hθbne
      have hp_eq := hclear_eq hR hC hθb0 hθbne
      have halloc_all : marketAllocation D G.capacity θb = G.allocation θb :=
        hD.marketAllocation_eq_kellyAllocation (by simpa using hR) hC hθb0 hθbne
      have halloc_eq := congrFun halloc_all r
      obtain ⟨j₀, hj₀⟩ := hθbne
      have hW_pos : 0 < ∑ j, θb j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
        have : 0 < θb j₀ := lt_of_le_of_ne (hθb0 j₀) (Ne.symm hj₀)
        have : 0 ≤ ∑ j ∈ Finset.univ.erase j₀, θb j := Finset.sum_nonneg fun j _ => hθb0 j
        linarith
      simp only [marketPayoff_apply, KellyGame.payoff, KellyGame.allocation, hp_eq, halloc_eq]
      have hsum_w : ∑ j, Δ * θb j = Δ * ∑ j, θb j := (Finset.mul_sum ..).symm
      rw [hsum_w]
      have halloc_w : G.capacity * (Δ * θb r) / (Δ * ∑ j, θb j) =
          G.capacity * θb r / ∑ j, θb j := by
        field_simp [hΔ.ne', hW_pos.ne']
      rw [halloc_w]
      congr 1
      field_simp [hC.ne', hW_pos.ne']
    have hupd0 : ∀ j, 0 ≤ Function.update θ r (t / Δ) j := fun j => by
      by_cases hj : j = r <;> simp [hj, div_nonneg ht0 hΔ.le, hne.nonneg]
    rw [hpay_eq _ hupd0 hnz_upd, hpay_eq θ hne.nonneg hne.exists_ne_zero] at hbr
    have hupd_w : (fun j => Δ * Function.update θ r (t / Δ) j) = Function.update w r t := by
      funext j
      by_cases hj : j = r
      · subst hj; simp [w, mul_div_cancel₀ _ hΔ.ne']
      · simp [w, hj]
    rwa [hupd_w] at hbr
  have halloc_w : marketAllocation D G.capacity θ = G.allocation w := by
    rw [hD.marketAllocation_eq_kellyAllocation (by simpa using hR) hC
      hne.nonneg hne.exists_ne_zero]
    funext r
    simp only [KellyGame.allocation, w, ← Finset.mul_sum]
    by_cases hW : ∑ j, θ j = 0
    · simp [hW]
    · field_simp [hΔ.ne', hW]
  have : Nonempty (Fin R) := Fin.pos_iff_nonempty.mp (by omega)
  rw [halloc_w, le_div_iff₀ (welfare_pos_of_isSocialOptimum hd hC hU hU0)]
  exact hkelly_ne.three_fourths_welfare_le hC hU hU0 hd.1

/-- **Johari–Tsitsiklis optimality of proportional sharing** ([Johari2007], §21.3,
Theorem 21.10(iii); [JohariTsitsiklis2009]): for any regular smooth market-clearing
mechanism `D ∈ 𝒟`, its worst-case Nash efficiency ratio equals `3 / 4` if and only if `D` is
Kelly's proportional sharing mechanism up to a positive scalar factor `Δ > 0`, i.e.,
`D(p, θ) = Δ * θ / p` for all `p > 0` and `θ ≥ 0`. -/
theorem IsRegularMarketClearing.efficiencyRatio_eq_three_fourths_iff {D : ℝ → ℝ → ℝ}
    (hD : IsRegularMarketClearing D) :
    efficiencyRatio D = 3 / 4 ↔
      ∃ Δ > 0, ∀ p, 0 < p → ∀ θ, 0 ≤ θ → D p θ = Δ * θ / p := by
  constructor
  · intro heq34
    obtain ⟨_, _, _, _, hD_eq, hΛB, hΛ_spec, _, _, hΛ_diff, hΛ_elast⟩ := hD.priceScale_props
    set B := priceScale D
    set Λ := invPriceScale D
    have hΨ_eq_one : ∀ μ, 0 < μ → μ * deriv Λ μ / Λ μ = 1 := by
      intro μ hμ
      have hΛμ_pos : 0 < Λ μ := (hΛ_spec μ hμ).2
      have hge1 : 1 ≤ μ * deriv Λ μ / Λ μ := (one_le_div hΛμ_pos).mpr (hΛ_elast μ hμ)
      refine le_antisymm ?_ hge1
      by_contra hgt1
      push Not at hgt1
      have hlt_G : elasticityEfficiencyBound (μ * deriv Λ μ / Λ μ) < 3 / 4 := by
        rw [← elasticityEfficiencyBound_one]
        exact elasticityEfficiencyBound_strictAntiOn le_rfl hge1 hgt1
      have hle_ρ := hD.efficiencyRatio_le_elasticityEfficiencyBound hμ
      linarith
    set q : ℝ → ℝ := fun μ => Λ μ / μ
    have hq_diff : DifferentiableOn ℝ q (Ioi 0) :=
      hΛ_diff.div differentiableOn_id fun μ hμ => (mem_Ioi.mp hμ).ne'
    have hq_deriv_zero : EqOn (deriv q) 0 (Ioi 0) := by
      intro μ hμ
      have hμ_pos : 0 < μ := mem_Ioi.mp hμ
      have hdΛ : HasDerivAt Λ (deriv Λ μ) μ :=
        ((hΛ_diff μ hμ).differentiableAt (Ioi_mem_nhds hμ_pos)).hasDerivAt
      have hdq : HasDerivAt q ((deriv Λ μ * μ - Λ μ * 1) / μ ^ 2) μ :=
        hdΛ.div (hasDerivAt_id' μ) hμ_pos.ne'
      rw [hdq.deriv]
      have h1 := hΨ_eq_one μ hμ_pos
      have hΛμ_pos : 0 < Λ μ := (hΛ_spec μ hμ_pos).2
      have hmul : μ * deriv Λ μ = Λ μ := (div_eq_one_iff_eq hΛμ_pos.ne').mp h1
      simp only [Pi.zero_apply]
      have : deriv Λ μ * μ - Λ μ * 1 = 0 := by linarith
      rw [this, zero_div]
    set Δ := Λ 1
    have hΔ_pos : 0 < Δ := (hΛ_spec 1 zero_lt_one).2
    have hΛ_lin : ∀ μ, 0 < μ → Λ μ = Δ * μ := by
      intro μ hμ
      have hconst := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hq_diff
        hq_deriv_zero hμ (zero_lt_one : (1 : ℝ) ∈ Ioi 0)
      dsimp only [q] at hconst
      rw [div_one] at hconst
      exact (div_eq_iff hμ.ne').mp hconst
    have hB_lin : ∀ p, 0 < p → B p = p / Δ := by
      intro p hp
      have hBp_pos : 0 < B p := hD.priceScale_props.1.mapsTo hp
      have h1 := hΛ_lin (B p) hBp_pos
      rw [hΛB p hp] at h1
      field_simp [hΔ_pos.ne']
      linarith
    refine ⟨Δ, hΔ_pos, fun p hp θ hθ => ?_⟩
    rw [hD_eq p hp θ hθ, hB_lin p hp]
    field_simp [hp.ne', hΔ_pos.ne']
  · rintro ⟨Δ, hΔ, hD_eq⟩
    exact hD.efficiencyRatio_eq_three_fourths_of_scaledKelly hΔ hD_eq

end EfficiencyOptimality

/-! ### Power-elasticity mechanisms `D(p, θ) = θ * p ^ (-1 / c)` (Example 21.9, Ex. 21.1–21.2) -/

section PowerElasticity

private theorem existsUnique_clearingPrice_powerElasticity {ι : Type*} [Fintype ι] {c : ℝ}
    (hc : 0 < c) {C : ℝ} (hC : 0 < C) {θ : ι → ℝ} (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    (0 < ((∑ i, θ i) / C) ^ c ∧
        ∑ i, powerElasticityMechanism c (((∑ i, θ i) / C) ^ c) (θ i) = C) ∧
      ∀ p, 0 < p ∧ ∑ i, powerElasticityMechanism c p (θ i) = C →
        p = ((∑ i, θ i) / C) ^ c := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  have hW_pos : 0 < ∑ i, θ i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have : 0 < θ i₀ := lt_of_le_of_ne (hθ i₀) (Ne.symm hi₀)
    have : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, θ i := Finset.sum_nonneg fun i _ => hθ i
    linarith
  set pStar := ((∑ i, θ i) / C) ^ c
  refine ⟨⟨Real.rpow_pos_of_pos (div_pos hW_pos hC) c, ?_⟩, fun p ⟨hp, hsum⟩ => ?_⟩
  · simp only [powerElasticityMechanism_apply, ← Finset.sum_mul]
    dsimp only [pStar]
    rw [← Real.rpow_mul (div_pos hW_pos hC).le, (show c * (-1 / c) = -1 by field_simp [hc.ne']),
      Real.rpow_neg_one]
    field_simp [hW_pos.ne', hC.ne']
  · simp only [powerElasticityMechanism_apply, ← Finset.sum_mul] at hsum
    have hp_rpow : p ^ (-1 / c) = C / ∑ i, θ i := by
      field_simp [hW_pos.ne'] at hsum ⊢
      linarith
    have h1 : (p ^ (-1 / c)) ^ (-c) = (C / ∑ i, θ i) ^ (-c) := congrArg (· ^ (-c)) hp_rpow
    rw [← Real.rpow_mul hp.le, (show -1 / c * -c = 1 by field_simp [hc.ne']),
      Real.rpow_one] at h1
    rw [h1]
    dsimp only [pStar]
    rw [Real.div_rpow hC.le hW_pos.le, Real.div_rpow hW_pos.le hC.le, Real.rpow_neg hC.le,
      Real.rpow_neg hW_pos.le]
    field_simp [(Real.rpow_pos_of_pos hC c).ne', (Real.rpow_pos_of_pos hW_pos c).ne']

/-- Every `powerElasticityMechanism c` (`c > 0`) is a smooth market-clearing mechanism
(`IsSmoothMarketClearing`). -/
theorem isSmoothMarketClearing_powerElasticity {c : ℝ} (hc : 0 < c) :
    IsSmoothMarketClearing (powerElasticityMechanism c) := by
  refine ⟨?_, fun p hp θ hθ => mul_nonneg hθ (Real.rpow_nonneg hp.le _), ?_⟩
  · rintro ⟨p, θ⟩ ⟨hp, _⟩
    have hp_pos : 0 < p := hp
    have hd1 : DifferentiableAt ℝ (fun x : ℝ × ℝ => x.2) (p, θ) := differentiableAt_snd
    have hrp : DifferentiableAt ℝ (fun z : ℝ => z ^ (-1 / c)) p :=
      (Real.hasDerivAt_rpow_const (Or.inl hp_pos.ne')).differentiableAt
    have hcomp : DifferentiableAt ℝ ((fun z : ℝ => z ^ (-1 / c)) ∘ Prod.fst) (p, θ) :=
      DifferentiableAt.comp (𝕜 := ℝ) (p, θ) hrp differentiableAt_fst
    have hd2 : DifferentiableAt ℝ (fun x : ℝ × ℝ => x.1 ^ (-1 / c)) (p, θ) :=
      hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => by simp)
    exact (hd1.mul hd2).differentiableWithinAt
  · intro R _ C hC θ hθ hne
    obtain ⟨hpStar, hu⟩ := existsUnique_clearingPrice_powerElasticity hc hC hθ hne
    exact ⟨((∑ r, θ r) / C) ^ c, hpStar, hu⟩

/-- Clearing price of `powerElasticityMechanism c` (`c > 0`):
`clearingPrice (powerElasticityMechanism c) C θ = ((∑ i, θ i) / C) ^ c` ([Johari2007],
Example 21.9, with the inverse exponent `c` of `B(p) = p ^ (1 / c)`). -/
theorem clearingPrice_powerElasticity {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c)
    (hcard : 2 ≤ Fintype.card ι) {C : ℝ} (hC : 0 < C) {θ : ι → ℝ}
    (hθ : ∀ i, 0 ≤ θ i) (hne : ∃ i, θ i ≠ 0) :
    clearingPrice (powerElasticityMechanism c) C θ = ((∑ i, θ i) / C) ^ c := by
  rw [(isSmoothMarketClearing_powerElasticity hc).clearingPrice_eq_iff hcard hC hθ hne]
  exact (existsUnique_clearingPrice_powerElasticity hc hC hθ hne).1

/-- **Example 21.9** ([Johari2007], §21.3, p. 553): for every `c ≥ 1`,
`powerElasticityMechanism c` (`D(p, θ) = θ * p ^ (-1 / c)`) belongs to `𝒟`
(`IsRegularMarketClearing`). -/
theorem isRegularMarketClearing_powerElasticity {c : ℝ} (hc : 1 ≤ c) :
    IsRegularMarketClearing (powerElasticityMechanism c) := by
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hsmooth := isSmoothMarketClearing_powerElasticity hc_pos
  have hsurj : ∀ p, 0 < p → ∀ d, 0 ≤ d → ∃ θ, 0 ≤ θ ∧ powerElasticityMechanism c p θ = d := by
    intro p hp d hd
    refine ⟨d * p ^ (1 / c), mul_nonneg hd (Real.rpow_nonneg hp.le _), ?_⟩
    rw [powerElasticityMechanism_apply, mul_assoc, ← Real.rpow_add hp,
      (show 1 / c + -1 / c = 0 by ring), Real.rpow_zero, mul_one]
  have hconc_pos : ∀ (R : ℕ), 2 ≤ R → ∀ C, 0 < C → ∀ u, IsAdmissibleUtility u →
      ∀ (r : Fin R) (θ : Fin R → ℝ), (∀ s, s ≠ r → θ s = 0) →
        ConcaveOn ℝ (Ioi 0)
          (fun t => marketPayoff (powerElasticityMechanism c) ⟨C, fun _ => u⟩
            (Function.update θ r t) r) := by
    intro R hR C hC u _ r θ hzero
    have hrpow_conv : ConvexOn ℝ (Ioi 0) (fun t : ℝ => C ^ (1 - c) * t ^ c) :=
      ((convexOn_rpow hc).subset Ioi_subset_Ici_self (convex_Ioi 0)).smul
        (Real.rpow_nonneg hC.le _)
    have hconc_target : ConcaveOn ℝ (Ioi 0) (fun t : ℝ => u C - C ^ (1 - c) * t ^ c) := by
      refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
      have hcv := hrpow_conv.2 hx hy ha hb hab
      simp only [smul_eq_mul] at hcv ⊢
      have huC : a * u C + b * u C = u C := by rw [← add_mul, hab, one_mul]
      linarith
    refine hconc_target.congr fun t ht => ?_
    have ht_pos : 0 < t := mem_Ioi.mp ht
    have hupd0 : ∀ s, 0 ≤ Function.update θ r t s := fun s => by
      by_cases hs : s = r
      · subst hs; simp [ht_pos.le]
      · simp [hs, hzero s hs]
    have hsum_t : ∑ s, Function.update θ r t s = t := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), Function.update_self]
      have h0 : ∑ s ∈ Finset.univ.erase r, Function.update θ r t s = 0 :=
        Finset.sum_eq_zero fun s hs => by
          have hne := Finset.ne_of_mem_erase hs
          simp [Function.update_of_ne hne, hzero s hne]
      rw [h0, add_zero]
    have hp_eq := clearingPrice_powerElasticity hc_pos (by simpa using hR) hC hupd0
      ⟨r, by simp [ht_pos.ne']⟩
    rw [hsum_t] at hp_eq
    have halloc_eq :
        marketAllocation (powerElasticityMechanism c) C (Function.update θ r t) r = C := by
      rw [marketAllocation_apply, hp_eq, Function.update_self, powerElasticityMechanism_apply,
        ← Real.rpow_mul (div_pos ht_pos hC).le,
        (show c * (-1 / c) = -1 by field_simp [hc_pos.ne']), Real.rpow_neg_one]
      field_simp [ht_pos.ne', hC.ne']
    simp only [marketPayoff_apply, halloc_eq, hp_eq]
    congr 1
    rw [Real.div_rpow ht_pos.le hC.le, mul_comm ((t ^ c) / (C ^ c)) C, mul_div_assoc',
      mul_comm C (t ^ c), mul_div_assoc]
    have hCpow : C / C ^ c = C ^ (1 - c) := by
      rw [sub_eq_add_neg, Real.rpow_add hC, Real.rpow_one, Real.rpow_neg hC.le, div_eq_mul_inv]
    rw [hCpow, mul_comm]
  have hconc_nonneg : ∀ (R : ℕ), 2 ≤ R → ∀ C, 0 < C → ∀ u, IsAdmissibleUtility u →
      ∀ (r : Fin R) (θ : Fin R → ℝ), (∀ s, 0 ≤ θ s) → (∃ s, s ≠ r ∧ θ s ≠ 0) →
        ConcaveOn ℝ (Ici 0)
          (fun t => marketPayoff (powerElasticityMechanism c) ⟨C, fun _ => u⟩
            (Function.update θ r t) r) := by
    intro R hR C hC u hu r θ hθ hnz
    obtain ⟨s₀, hs₀_ne, hs₀_nz⟩ := hnz
    set S := ∑ s ∈ Finset.univ.erase r, θ s
    have hS_pos : 0 < S := by
      have hs₀_mem : s₀ ∈ Finset.univ.erase r := Finset.mem_erase.mpr ⟨hs₀_ne, Finset.mem_univ s₀⟩
      have hs₀_pos : 0 < θ s₀ := lt_of_le_of_ne (hθ s₀) (Ne.symm hs₀_nz)
      exact lt_of_lt_of_le hs₀_pos (Finset.single_le_sum (fun s _ => hθ s) hs₀_mem)
    have hprop_conc : ConcaveOn ℝ (Ici 0) (fun t : ℝ => C * t / (t + S)) := by
      refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
      have hx0 : 0 ≤ x := mem_Ici.mp hx
      have hy0 : 0 ≤ y := mem_Ici.mp hy
      have hxS : 0 < x + S := by linarith
      have hyS : 0 < y + S := by linarith
      have hmS : 0 < a * x + b * y + S := by nlinarith
      simp only [smul_eq_mul]
      have hid : C * (a * x + b * y) / (a * x + b * y + S) -
          (a * (C * x / (x + S)) + b * (C * y / (y + S))) =
          C * S * a * b * (x - y) ^ 2 / ((a * x + b * y + S) * (x + S) * (y + S)) := by
        field_simp [hmS.ne', hxS.ne', hyS.ne']
        have : a = 1 - b := by linarith
        rw [this]; ring
      have : 0 ≤ C * S * a * b * (x - y) ^ 2 / ((a * x + b * y + S) * (x + S) * (y + S)) := by
        positivity
      linarith
    set g : ℝ → ℝ := fun t => t * (t + S) ^ (c - 1)
    have hg_deriv : ∀ t > -S, HasDerivAt g ((t + S) ^ (c - 2) * (c * t + S)) t := by
      intro t htS
      have htS_pos : 0 < t + S := by linarith
      have hd_pow : HasDerivAt (fun x : ℝ => (x + S) ^ (c - 1))
          ((c - 1) * (t + S) ^ (c - 2)) t := by
        have h1 := (Real.hasDerivAt_rpow_const (Or.inl htS_pos.ne') (p := c - 1)).comp t
          ((hasDerivAt_id' t).add_const S)
        have h2 : c - 1 - 1 = c - 2 := by ring
        rw [h2, mul_one] at h1
        exact h1
      have hmul := (hasDerivAt_id' t).mul hd_pow
      have hval : 1 * (t + S) ^ (c - 1) + t * ((c - 1) * (t + S) ^ (c - 2)) =
          (t + S) ^ (c - 2) * (c * t + S) := by
        have hsplit : (t + S) ^ (c - 1) = (t + S) ^ (c - 2) * (t + S) := by
          rw [← Real.rpow_add_one htS_pos.ne']
          congr 1; ring
        rw [hsplit]; ring
      rwa [hval] at hmul
    have hg'_deriv : ∀ t > -S, HasDerivAt (fun x => (x + S) ^ (c - 2) * (c * x + S))
        ((c - 1) * (t + S) ^ (c - 3) * (c * t + 2 * S)) t := by
      intro t htS
      have htS_pos : 0 < t + S := by linarith
      have hd1 : HasDerivAt (fun x : ℝ => (x + S) ^ (c - 2))
          ((c - 2) * (t + S) ^ (c - 3)) t := by
        have h1 := (Real.hasDerivAt_rpow_const (Or.inl htS_pos.ne') (p := c - 2)).comp t
          ((hasDerivAt_id' t).add_const S)
        have h2 : c - 2 - 1 = c - 3 := by ring
        rw [h2, mul_one] at h1
        exact h1
      have hd2 : HasDerivAt (fun x : ℝ => c * x + S) c t := by
        simpa only [mul_one] using ((hasDerivAt_id' t).const_mul c).add_const S
      have hmul := hd1.mul hd2
      have hval : (c - 2) * (t + S) ^ (c - 3) * (c * t + S) + (t + S) ^ (c - 2) * c =
          (c - 1) * (t + S) ^ (c - 3) * (c * t + 2 * S) := by
        have hsplit : (t + S) ^ (c - 2) = (t + S) ^ (c - 3) * (t + S) := by
          rw [← Real.rpow_add_one htS_pos.ne']
          congr 1; ring
        rw [hsplit]; ring
      rwa [hval] at hmul
    have hg_conv : ConvexOn ℝ (Ici 0) g := by
      have hg_cont : ContinuousOn g (Ici 0) := fun t ht =>
        (hg_deriv t (by linarith [mem_Ici.mp ht])).continuousAt.continuousWithinAt
      have hg_diff : DifferentiableOn ℝ g (interior (Ici 0)) := fun t ht => by
        have htS : -S < t := by rw [interior_Ici] at ht; linarith [mem_Ioi.mp ht]
        exact (hg_deriv t htS).differentiableAt.differentiableWithinAt
      have hg'_eq : EqOn (deriv g) (fun x => (x + S) ^ (c - 2) * (c * x + S)) (Ioi 0) :=
        fun t ht => (hg_deriv t (by linarith [mem_Ioi.mp ht])).deriv
      have hg'_mono_aux : MonotoneOn (fun x => (x + S) ^ (c - 2) * (c * x + S)) (Ioi 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
          (fun t ht => (hg'_deriv t (by linarith [mem_Ioi.mp ht])).continuousAt.continuousWithinAt)
          (fun t ht => by
            have htS : -S < t := by rw [interior_Ioi] at ht; linarith [mem_Ioi.mp ht]
            exact (hg'_deriv t htS).differentiableAt.differentiableWithinAt)
          fun t ht => ?_
        rw [interior_Ioi] at ht
        have ht_pos : 0 < t := mem_Ioi.mp ht
        rw [(hg'_deriv t (by linarith)).deriv]
        have hc1 : 0 ≤ c - 1 := by linarith
        have hp3 : 0 ≤ (t + S) ^ (c - 3) := Real.rpow_nonneg (by linarith) _
        have hlin_pos : 0 ≤ c * t + 2 * S := by nlinarith
        positivity
      have hg'_mono : MonotoneOn (deriv g) (interior (Ici 0)) := by
        rw [interior_Ici]
        intro x hx y hy hxy
        rw [hg'_eq hx, hg'_eq hy]
        exact hg'_mono_aux hx hy hxy
      exact hg'_mono.convexOn_of_deriv (convex_Ici 0) hg_cont hg_diff
    have hpay_conc : ConcaveOn ℝ (Ici 0)
        (fun t : ℝ => u (C * t / (t + S)) - C ^ (1 - c) * g t) := by
      refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
      have hx0 : 0 ≤ x := mem_Ici.mp hx
      have hy0 : 0 ≤ y := mem_Ici.mp hy
      have hfx : 0 ≤ C * x / (x + S) := div_nonneg (mul_nonneg hC.le hx0) (by linarith)
      have hfy : 0 ≤ C * y / (y + S) := div_nonneg (mul_nonneg hC.le hy0) (by linarith)
      have halloc_ineq := hprop_conc.2 hx hy ha hb hab
      have hcomb0 : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0)
      have hmono := hu.strictMonoOn.monotoneOn
        (add_nonneg (mul_nonneg ha hfx) (mul_nonneg hb hfy))
        (div_nonneg (mul_nonneg hC.le hcomb0) (by simp only [smul_eq_mul]; linarith))
        halloc_ineq
      have hcu := hu.concaveOn.2 hfx hfy ha hb hab
      have hcg := hg_conv.2 hx hy ha hb hab
      have hC_nonneg : 0 ≤ C ^ (1 - c) := Real.rpow_nonneg hC.le _
      have hcg_mul := mul_le_mul_of_nonneg_left hcg hC_nonneg
      simp only [smul_eq_mul] at hmono hcu hcg_mul ⊢
      linarith
    refine hpay_conc.congr fun t ht => ?_
    have ht0 : 0 ≤ t := mem_Ici.mp ht
    have hupd0 : ∀ s, 0 ≤ Function.update θ r t s := fun s => by
      by_cases hs : s = r <;> simp [hs, ht0, hθ]
    have hsum_t : ∑ s, Function.update θ r t s = t + S := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r), Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun s hs => Function.update_of_ne (Finset.ne_of_mem_erase hs) _ _
    have htS_pos : 0 < t + S := by linarith
    have hp_eq := clearingPrice_powerElasticity hc_pos (by simpa using hR) hC hupd0
      ⟨s₀, by simp [Function.update_of_ne hs₀_ne, hs₀_nz]⟩
    rw [hsum_t] at hp_eq
    have halloc_eq : marketAllocation (powerElasticityMechanism c) C (Function.update θ r t) r =
        C * t / (t + S) := by
      rw [marketAllocation_apply, hp_eq, Function.update_self, powerElasticityMechanism_apply,
        ← Real.rpow_mul (div_pos htS_pos hC).le,
        (show c * (-1 / c) = -1 by field_simp [hc_pos.ne']), Real.rpow_neg_one]
      field_simp [htS_pos.ne', hC.ne']
    simp only [marketPayoff_apply, halloc_eq, hp_eq, g]
    congr 1
    rw [Real.div_rpow htS_pos.le hC.le]
    have hCpow : C / C ^ c = C ^ (1 - c) := by
      rw [sub_eq_add_neg, Real.rpow_add hC, Real.rpow_one, Real.rpow_neg hC.le, div_eq_mul_inv]
    have htSpow : (t + S) ^ c / (t + S) = (t + S) ^ (c - 1) := by
      rw [sub_eq_add_neg, Real.rpow_add htS_pos, Real.rpow_neg_one, div_eq_mul_inv]
    calc C ^ (1 - c) * (t * (t + S) ^ (c - 1))
        = (C / C ^ c) * (t * ((t + S) ^ c / (t + S))) := by rw [hCpow, htSpow]
      _ = (t + S) ^ c / C ^ c * (C * t / (t + S)) := by ring
  exact ⟨hsmooth, hconc_pos, hconc_nonneg, hsurj⟩

private theorem invPriceScale_powerElasticity {c μ : ℝ} (hc : 1 ≤ c) (hμ : 0 < μ) :
    invPriceScale (powerElasticityMechanism c) μ = μ ^ c := by
  have hc_pos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hθ0 : ∀ i : Fin 2, 0 ≤ (![μ, 0] : Fin 2 → ℝ) i := fun i => by
    fin_cases i <;> simp [hμ.le]
  have hne : ∃ i : Fin 2, (![μ, 0] : Fin 2 → ℝ) i ≠ 0 := ⟨0, by simp [hμ.ne']⟩
  dsimp only [invPriceScale]
  rw [clearingPrice_powerElasticity hc_pos le_rfl zero_lt_one hθ0 hne]
  simp

private theorem deriv_invPriceScale_powerElasticity {c μ : ℝ} (hc : 1 ≤ c) (hμ : 0 < μ) :
    deriv (invPriceScale (powerElasticityMechanism c)) μ = c * μ ^ (c - 1) := by
  have heq : EqOn (invPriceScale (powerElasticityMechanism c)) (fun y => y ^ c) (Ioi 0) :=
    fun y hy => invPriceScale_powerElasticity hc hy
  have hd : HasDerivAt (fun y : ℝ => y ^ c) (c * μ ^ (c - 1)) μ :=
    Real.hasDerivAt_rpow_const (Or.inl hμ.ne')
  exact (hd.congr_of_eventuallyEq (heq.eventuallyEq_of_mem (Ioi_mem_nhds hμ))).deriv

/-- Pointwise bound for Exercise 21.2(b) ([Johari2007], p. 567): for admissible nonnegative `u`,
`c ≥ 1`, and `d, x ∈ [0, C]`,
`G(c) * u x ≤ u d + u'(d) * ((1 - d / C) / (1 + (c - 1) * (d / C))) * (x - d)`. -/
private theorem pointwise_powerElasticity_bound {u : ℝ → ℝ} (hu : IsAdmissibleUtility u)
    (hu0 : 0 ≤ u 0) {c C d x : ℝ} (hc : 1 ≤ c) (hC : 0 < C)
    (hd : d ∈ Icc 0 C) (hx : x ∈ Icc 0 C) :
    elasticityEfficiencyBound c * u x ≤
      u d + derivWithin u (Ici 0) d *
        ((1 - d / C) / (1 + (c - 1) * (d / C))) * (x - d) := by
  set γ := (1 - d / C) / (1 + (c - 1) * (d / C))
  have hdC_nonneg : 0 ≤ d / C := div_nonneg hd.1 hC.le
  have hdC_le_one : d / C ≤ 1 := (div_le_one hC).mpr hd.2
  have hden_ge : 1 ≤ 1 + (c - 1) * (d / C) := by
    have : 0 ≤ (c - 1) * (d / C) := mul_nonneg (by linarith) hdC_nonneg
    linarith
  have hγ_nonneg : 0 ≤ γ := div_nonneg (sub_nonneg.mpr hdC_le_one) (by linarith)
  have hγ_le_one : γ ≤ 1 := by
    dsimp only [γ]
    rw [div_le_one (by linarith)]
    nlinarith
  have hux_nonneg : 0 ≤ u x :=
    le_trans hu0 (hu.strictMonoOn.monotoneOn le_rfl hx.1 hx.1)
  have hG_le_one : elasticityEfficiencyBound c ≤ 1 :=
    le_trans (elasticityEfficiencyBound_le_three_fourths hc) (by norm_num)
  rcases le_or_gt x d with hxd | hdx
  · have htan := hu.le_add_derivWithin hd.1 hx.1
    have hu'_pos : 0 < derivWithin u (Ici 0) d := hu.derivWithin_pos hd.1
    have hmul : derivWithin u (Ici 0) d * (x - d) ≤
        derivWithin u (Ici 0) d * γ * (x - d) := by
      have : 0 ≤ derivWithin u (Ici 0) d * (1 - γ) * (d - x) :=
        mul_nonneg (mul_nonneg hu'_pos.le (by linarith)) (by linarith)
      nlinarith
    have hG_ux : elasticityEfficiencyBound c * u x ≤ u x :=
      mul_le_of_le_one_left hux_nonneg hG_le_one
    linarith
  · have hx_pos : 0 < x := lt_of_le_of_lt hd.1 hdx
    set y := d / x
    have hy0 : 0 ≤ y := div_nonneg hd.1 hx_pos.le
    have hy_lt1 : y < 1 := (div_lt_one hx_pos).mpr hdx
    have hdC_le_y : d / C ≤ y := by
      dsimp only [y]
      exact div_le_div_of_nonneg_left hd.1 hx_pos hx.2
    set w := (1 - y) / (1 + (c - 1) * y)
    have hden_y : 0 < 1 + (c - 1) * y := by
      have : 0 ≤ (c - 1) * y := mul_nonneg (by linarith) hy0
      linarith
    have hw_nonneg : 0 ≤ w := div_nonneg (by linarith) hden_y.le
    have hw_le_one : w ≤ 1 := by
      dsimp only [w]
      rw [div_le_one hden_y]
      nlinarith
    have hw_le_γ : w ≤ γ := by
      dsimp only [w, γ]
      rw [div_le_div_iff₀ hden_y (by linarith)]
      have hdiff : (1 - d / C) * (1 + (c - 1) * y) - (1 - y) * (1 + (c - 1) * (d / C)) =
          c * (y - d / C) := by ring
      have : 0 ≤ c * (y - d / C) := mul_nonneg (by linarith) (by linarith)
      linarith
    have htan := hu.le_add_derivWithin hd.1 hx.1
    have hud_lt_ux : u d < u x := hu.strictMonoOn hd.1 hx.1 hdx
    have hstep1 : u d + w * (u x - u d) ≤ u d + derivWithin u (Ici 0) d * γ * (x - d) := by
      have h1 : w * (u x - u d) ≤ γ * (u x - u d) :=
        mul_le_mul_of_nonneg_right hw_le_γ (by linarith)
      have h2 : γ * (u x - u d) ≤ γ * (derivWithin u (Ici 0) d * (x - d)) :=
        mul_le_mul_of_nonneg_left (by linarith) hγ_nonneg
      linarith
    have hud_ge : y * u x ≤ u d := by
      have hcomb : (1 - y) • (0 : ℝ) + y • x = d := by
        simp only [smul_eq_mul, mul_zero, zero_add, y, div_mul_cancel₀ _ hx_pos.ne']
      have hc0 := hu.concaveOn.2 (le_rfl : (0 : ℝ) ∈ Ici 0) hx.1
        (sub_nonneg.mpr hy_lt1.le) hy0 (by ring)
      rw [hcomb] at hc0
      simp only [smul_eq_mul] at hc0
      have : 0 ≤ (1 - y) * u 0 := mul_nonneg (by linarith) hu0
      linarith
    have hstep2 : ((1 - w) * y + w) * u x ≤ u d + w * (u x - u d) := by
      have h1w : 0 ≤ 1 - w := by linarith
      have hm := mul_le_mul_of_nonneg_left hud_ge h1w
      linarith
    have hF_eq : (1 - w) * y + w = (1 - y) ^ 2 / (1 + (c - 1) * y) + y := by
      dsimp only [w]
      field_simp [hden_y.ne']
      ring
    have hG_le_F := elasticityEfficiencyBound_le_F hc hy0
    rw [← hF_eq] at hG_le_F
    have hstep3 := mul_le_mul_of_nonneg_right hG_le_F hux_nonneg
    linarith

/-- **Instance-wise welfare guarantee of `powerElasticityMechanism c`** ([Johari2007],
Exercises 21.1 and 21.2(a, b), p. 567): for every `c ≥ 1`, `2 ≤ Fintype.card ι`, positive
capacity, and nonnegative admissible utilities, every Nash equilibrium `θ` of
`powerElasticityMechanism c` achieves at least `elasticityEfficiencyBound c` times the aggregate
welfare of any feasible allocation `x`. -/
theorem IsMarketNashEquilibrium.elasticityEfficiencyBound_mul_welfare_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {c : ℝ} (hc : 1 ≤ c) {G : KellyGame ι}
    {θ : ι → ℝ} (hne : IsMarketNashEquilibrium (powerElasticityMechanism c) G θ)
    (hcard : 2 ≤ Fintype.card ι) (hC : 0 < G.capacity)
    (hU : ∀ i, IsAdmissibleUtility (G.utility i)) (hU0 : ∀ i, 0 ≤ G.utility i 0)
    {x : ι → ℝ} (hx : G.IsFeasibleAllocation x) :
    elasticityEfficiencyBound c * G.welfare x ≤
      G.welfare (marketAllocation (powerElasticityMechanism c) G.capacity θ) := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hreg := isRegularMarketClearing_powerElasticity hc
  obtain ⟨hθ0, herase, hle, heq⟩ := (hreg.isMarketNashEquilibrium_iff_kkt hcard hC hU).mp hne
  have halloc_eq := hreg.marketAllocation_eq_kellyAllocation hcard hC hθ0 hne.exists_ne_zero
  rw [halloc_eq]
  set C := G.capacity
  set d := G.allocation θ
  set μ := (∑ j, θ j) / C
  have hW_pos : 0 < ∑ j, θ j := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    linarith [hθ0 i₀, herase i₀]
  have hμ_pos : 0 < μ := div_pos hW_pos hC
  have hsum_d : ∑ i, d i = C := G.sum_allocation_eq_capacity hW_pos.ne'
  have hd_feas : G.IsFeasibleAllocation d := G.isFeasibleAllocation_allocation hC.le hθ0
  set lam := μ ^ c
  have hlam_pos : 0 < lam := Real.rpow_pos_of_pos hμ_pos c
  have hrhs_pow : ∀ y : ℝ,
      invPriceScale (powerElasticityMechanism c) μ * (1 - y / C) +
        μ * deriv (invPriceScale (powerElasticityMechanism c)) μ * (y / C) =
      lam * (1 + (c - 1) * (y / C)) := by
    intro y
    rw [invPriceScale_powerElasticity hc hμ_pos, deriv_invPriceScale_powerElasticity hc hμ_pos]
    have hmul_pow : μ * (c * μ ^ (c - 1)) = c * μ ^ c := by
      have h1 : μ * μ ^ (c - 1) = μ ^ c := by
        rw [mul_comm, ← Real.rpow_add_one hμ_pos.ne']
        congr 1; ring
      calc μ * (c * μ ^ (c - 1)) = c * (μ * μ ^ (c - 1)) := by ring
        _ = c * μ ^ c := by rw [h1]
    rw [hmul_pow]
    dsimp only [lam]
    ring
  set modDeriv : ι → ℝ := fun i =>
    derivWithin (G.utility i) (Ici 0) (d i) * ((1 - d i / C) / (1 + (c - 1) * (d i / C)))
  have hkkt_le : ∀ i, modDeriv i ≤ lam := by
    intro i
    have hden_pos : 0 < 1 + (c - 1) * (d i / C) := by
      have : 0 ≤ (c - 1) * (d i / C) := mul_nonneg (by linarith) (div_nonneg (hd_feas.1 i) hC.le)
      linarith
    dsimp only [modDeriv]
    rw [← mul_div_assoc, div_le_iff₀ hden_pos, mul_comm lam]
    have h1 := hle i
    rw [hrhs_pow (d i)] at h1
    linarith
  have hkkt_eq : ∀ i, 0 < d i → modDeriv i = lam := by
    intro i hdi
    have hden_pos : 0 < 1 + (c - 1) * (d i / C) := by
      have : 0 ≤ (c - 1) * (d i / C) := mul_nonneg (by linarith) (div_nonneg (hd_feas.1 i) hC.le)
      linarith
    dsimp only [modDeriv]
    rw [← mul_div_assoc, div_eq_iff hden_pos.ne', mul_comm lam]
    have h1 := heq i hdi
    rw [hrhs_pow (d i)] at h1
    linarith
  have hvi : ∑ i, modDeriv i * (x i - d i) ≤ 0 := by
    calc ∑ i, modDeriv i * (x i - d i)
        ≤ ∑ i, lam * (x i - d i) := Finset.sum_le_sum fun i _ => by
          rcases eq_or_lt_of_le (hd_feas.1 i) with hi0 | hi_pos
          · have hle_i := hkkt_le i
            rw [← hi0, sub_zero]
            exact mul_le_mul_of_nonneg_right hle_i (hx.1 i)
          · rw [hkkt_eq i hi_pos]
      _ = lam * (∑ i, x i - ∑ i, d i) := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam_pos.le (by linarith [hx.2])
  have hpt : ∀ i, elasticityEfficiencyBound c * G.utility i (x i) ≤
      G.utility i (d i) + modDeriv i * (x i - d i) := fun i =>
    pointwise_powerElasticity_bound (hU i) (hU0 i) hc hC
      ⟨hd_feas.1 i, G.isFeasibleAllocation_le_capacity hd_feas i⟩
      ⟨hx.1 i, G.isFeasibleAllocation_le_capacity hx i⟩
  have hsum_pt := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum_pt
  change elasticityEfficiencyBound c * ∑ i, G.utility i (x i) ≤ ∑ i, G.utility i (d i)
  linarith

/-- **Exact worst-case efficiency of `powerElasticityMechanism c`** ([Johari2007], Exercise 21.2(c),
pp. 567–568): for every `c ≥ 1`, `efficiencyRatio (powerElasticityMechanism c) = G(c)`. -/
theorem efficiencyRatio_powerElasticity {c : ℝ} (hc : 1 ≤ c) :
    efficiencyRatio (powerElasticityMechanism c) = elasticityEfficiencyBound c := by
  have hreg := isRegularMarketClearing_powerElasticity hc
  refine le_antisymm ?_ ?_
  · have h1 := hreg.efficiencyRatio_le_elasticityEfficiencyBound (μ := 1) zero_lt_one
    rw [invPriceScale_powerElasticity hc zero_lt_one,
      deriv_invPriceScale_powerElasticity hc zero_lt_one] at h1
    simpa only [Real.one_rpow, one_mul, mul_one, div_one] using h1
  · refine le_csInf (nonempty_efficiencyRatioSet hreg) ?_
    rintro ρ ⟨R, hR, G, d, θ, hC, hU, hU0, hd, hne, rfl⟩
    have : Nonempty (Fin R) := Fin.pos_iff_nonempty.mp (by omega)
    rw [le_div_iff₀ (welfare_pos_of_isSocialOptimum hd hC hU hU0)]
    exact hne.elasticityEfficiencyBound_mul_welfare_le hc (by simpa using hR) hC hU hU0 hd.1

end PowerElasticity

end Cslib.GameTheory

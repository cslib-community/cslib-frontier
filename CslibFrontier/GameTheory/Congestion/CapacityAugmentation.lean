/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Congestion.Basic
public import CslibFrontier.GameTheory.Congestion.BeckmannPotential
public import CslibFrontier.GameTheory.Congestion.MarginalCostPricing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Capacity augmentation, concave and polynomial Pigou bounds, and Braess's paradox

This module formalizes the remaining nonatomic routing bounds, resource-augmentation guarantees,
atomic separation counterexamples, and network-design paradoxes from Roughgarden
[Roughgarden2007Routing], Chapter 18 (originally due to Braess, 1968, Roughgarden and Tardos,
2002, Roughgarden, 2003/2005/2006, Chakrabarty, 2004, and Correa, Schulz and Stier-Moses, 2005):

* **Concave Pigou bound** (`concaveLatencies`, `pigouBound_concaveLatencies`,
  `IsWardrop.cost_le_four_thirds_of_mem_concaveLatencies`, [Roughgarden2007Routing],
  Exercise 18.6): the class of nonnegative, nondecreasing, concave functions on `[0, ∞)` (including
  `id`, nonnegative constants, and `Real.sqrt`) has exact Pigou bound `4/3`.
* **Asymptotics of the polynomial Pigou bound**
  (`tendsto_toReal_pigouBound_polynomialLatencies_mul_log_div`,
  [Roughgarden2007Routing], Example 18.3 and Exercise 18.1): as `d → ∞`,
  `(pigouBound (polynomialLatencies d)).toReal * (Real.log d / d) → 1`, so the polynomial price of
  anarchy grows as `Θ(d / ln d)`.
* **Capacity augmentation and link speedup** (`scaleRate`, `speedup`,
  `IsWardrop.cost_le_inv_mul_of_scaleRate`, `IsWardrop.cost_le_of_scaleRate_two`,
  `IsWardrop.speedup_two_cost_le`, `exists_pigouNetwork_pow_scaleRate_cost_lt`,
  `exists_atomic_pureNash_socialCost_gt_doubled`, `HasAffineLatencies.cost_le_of_scaleRate`,
  `affine_scaleRate_bound_iff`,
  [Roughgarden2007Routing], Example 18.28, Theorem 18.29, Corollary 18.30, and Exercise 18.8(a–e)):
  * For arbitrary nonnegative nondecreasing latencies and `δ > 0`, a Wardrop equilibrium for rate
    `r` costs at most `(1 / δ)` times any flow feasible for `(1 + δ) r` (`δ = 1` gives the
    Roughgarden–Tardos `2r` theorem and the `c̃_e(x) = c_e(x/2)/2` link-speedup corollary).
  * Nonlinear Pigou networks `x ^ d` show that `1 / δ` (and `1` at `r = 2`) is best possible as
    `d → ∞`.
  * A 4-resource unweighted atomic congestion game with polynomial latency `k ^ 4` shows that the
    `2r` capacity-augmentation theorem fails in atomic selfish routing (`972 > 128`).
  * For nonnegative affine latencies, the exact smallest augmentation threshold is `δ = 1 / 4`
    (rate `(5 / 4) r`).
* **Braess's paradox and subnetwork bounds** (`braessInitial`, `braessAugmented`,
  `braessInitial_isWardrop_iff`, `braessAugmented_isWardrop_iff`, `braessAugmented_isOptimal_half`,
  `braess_paradox`, `restrictPaths`, `isFeasible_extend`,
  `IsWardrop.cost_le_toReal_pigouBound_mul_restrictPaths`,
  `HasAffineLatencies.cost_le_four_thirds_restrictPaths`, [Roughgarden2007Routing], Example 18.4
  and Remark 18.22): adding a zero-cost edge to the four-node Wheatstone network raises the unique
  Wardrop equilibrium cost from `3/2` to `2 = (4/3) * (3/2)`, which is worst possible across all
  affine subnetwork extensions.

## Main definitions

* `Cslib.GameTheory.concaveLatencies`: nonnegative, nondecreasing, concave latency functions on
  `[0, ∞)`.
* `Cslib.GameTheory.NonatomicCongestionGame.scaleRate`: demand-scaled game `(G, α r, c)`.
* `Cslib.GameTheory.NonatomicCongestionGame.speedup`: link-speedup game with latencies
  `c_e(x / α) / α`.
* `Cslib.GameTheory.NonatomicCongestionGame.restrictPaths`: subnetwork restriction along an
  injection `ι : P₁ ↪ P₂`.
* `Cslib.GameTheory.NonatomicCongestionGame.braessInitial`,
  `Cslib.GameTheory.NonatomicCongestionGame.braessAugmented`: the four-node Wheatstone network
  before and after adding the zero-cost edge.

## Main results

* `Cslib.GameTheory.pigouBound_concaveLatencies` and
  `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_four_thirds_of_mem_concaveLatencies`
  ([Roughgarden2007Routing], Exercise 18.6): `α(concaveLatencies) = 4/3`.
* `Cslib.GameTheory.tendsto_toReal_pigouBound_polynomialLatencies_mul_log_div`
  ([Roughgarden2007Routing], Exercise 18.1): asymptotic growth `~ d / ln d` of the polynomial Pigou
  bound.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_inv_mul_of_scaleRate` and
  `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_of_scaleRate_two`
  ([Roughgarden2007Routing], Exercise 18.8(c) and Theorem 18.29): `(1 + δ)r` and `2r` capacity
  augmentation.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.speedup_cost_le` and
  `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.speedup_two_cost_le`
  ([Roughgarden2007Routing], Corollary 18.30 and Exercise 18.8(a)): link-speedup corollaries.
* `Cslib.GameTheory.NonatomicCongestionGame.exists_pigouNetwork_pow_scaleRate_cost_lt`
  ([Roughgarden2007Routing], Example 18.28 and Exercise 18.8(d)): tightness on nonlinear Pigou
  networks.
* `Cslib.GameTheory.CongestionGame.exists_atomic_pureNash_socialCost_gt_doubled`
  ([Roughgarden2007Routing], Exercise 18.8(b)): atomic counterexample to `2r` augmentation.
* `Cslib.GameTheory.NonatomicCongestionGame.HasAffineLatencies.cost_le_of_scaleRate` and
  `Cslib.GameTheory.NonatomicCongestionGame.affine_scaleRate_bound_iff`
  ([Roughgarden2007Routing], Exercise 18.8(e)): exact affine augmentation threshold `δ = 1/4`.
* `Cslib.GameTheory.NonatomicCongestionGame.braessInitial_isWardrop_iff`,
  `Cslib.GameTheory.NonatomicCongestionGame.braessAugmented_isWardrop_iff`,
  `Cslib.GameTheory.NonatomicCongestionGame.braessAugmented_isOptimal_half`,
  `Cslib.GameTheory.NonatomicCongestionGame.braess_paradox`,
  `Cslib.GameTheory.NonatomicCongestionGame.isFeasible_extend`,
  `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_toReal_pigouBound_mul_restrictPaths`,
  and
  `Cslib.GameTheory.NonatomicCongestionGame.HasAffineLatencies.cost_le_four_thirds_restrictPaths`
  ([Roughgarden2007Routing], Example 18.4 and Remark 18.22): Braess's paradox and its tight `4/3`
  upper bound.

## References

* [Roughgarden2003]
* [Roughgarden2007Routing]
* [RoughgardenTardos2002]
-/

public section

namespace Cslib.GameTheory

open Set Filter
open scoped ENNReal Topology

/-! ### Exercise 18.6: Pigou bound of concave latencies -/

/-- The class of **nonnegative, nondecreasing, concave latency functions** on `[0, ∞)`
([Roughgarden2007Routing], Exercise 18.6). -/
def concaveLatencies : Set (ℝ → ℝ) :=
  {c | (∀ x, 0 ≤ x → 0 ≤ c x) ∧ MonotoneOn c (Ici 0) ∧ ConcaveOn ℝ (Ici 0) c}

/-- Membership in `concaveLatencies`, unfolded. -/
theorem mem_concaveLatencies {c : ℝ → ℝ} :
    c ∈ concaveLatencies ↔
      (∀ x, 0 ≤ x → 0 ≤ c x) ∧ MonotoneOn c (Ici 0) ∧ ConcaveOn ℝ (Ici 0) c :=
  Iff.rfl

/-- The identity latency `x ↦ x` belongs to `concaveLatencies`. -/
theorem id_mem_concaveLatencies : (fun x : ℝ => x) ∈ concaveLatencies :=
  ⟨fun _ hx => hx, monotoneOn_id, concaveOn_id (convex_Ici 0)⟩

/-- Every nonnegative constant latency belongs to `concaveLatencies`. -/
theorem const_mem_concaveLatencies (a : ℝ) (ha : 0 ≤ a) :
    (fun _ : ℝ => a) ∈ concaveLatencies :=
  ⟨fun _ _ => ha, monotoneOn_const, concaveOn_const a (convex_Ici 0)⟩

/-- The square-root latency `Real.sqrt` belongs to `concaveLatencies`. -/
theorem sqrt_mem_concaveLatencies : Real.sqrt ∈ concaveLatencies :=
  ⟨fun x _ => Real.sqrt_nonneg x, fun _ _ _ _ hxy => Real.sqrt_le_sqrt hxy,
    Real.strictConcaveOn_sqrt.concaveOn⟩

/-- **The Pigou bound of concave latencies is `4/3`** ([Roughgarden2007Routing], Exercise 18.6):
for any nonnegative, nondecreasing, concave `c` on `[0, ∞)` and `0 ≤ x ≤ r` with `0 < r`,
concavity between `0` and `r` gives `c(x) ≥ (x / r) c(r)`, whence
`x (c(r) - c(x)) ≤ (x / r) (1 - x / r) r c(r) ≤ (1/4) r c(r)`. -/
theorem pigouBound_concaveLatencies :
    pigouBound concaveLatencies = ENNReal.ofReal (4 / 3) := by
  refine le_antisymm ?_ ?_
  · have hinv : (1 - (1 / 4 : ℝ))⁻¹ = 4 / 3 := by norm_num
    rw [← hinv]
    refine pigouBound_le_ofReal_inv_one_sub (by norm_num) (fun c hc => hc.1)
      fun c ⟨hc0, hcm, hconc⟩ r x hr hx => ?_
    rcases le_total r x with hrx | hxr
    · have hle : c r ≤ c x := hcm hr hx hrx
      have hnonpos : x * (c r - c x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (sub_nonpos.2 hle)
      exact hnonpos.trans (mul_nonneg (by norm_num) (mul_nonneg hr (hc0 r hr)))
    · rcases hr.eq_or_lt with rfl | hr_pos
      · have hx0 : x = 0 := le_antisymm hxr hx
        simp [hx0]
      · set t := x / r
        have ht0 : 0 ≤ t := div_nonneg hx hr_pos.le
        have ht1 : t ≤ 1 := (div_le_one hr_pos).2 hxr
        have hconv_pt : (1 - t) • (0 : ℝ) + t • r = x := by
          simp only [smul_eq_mul, mul_zero, zero_add, t, div_mul_cancel₀ _ hr_pos.ne']
        have hconc_ineq := hconc.2 (le_rfl : (0 : ℝ) ∈ Ici 0) hr_pos.le
          (sub_nonneg.2 ht1) ht0 (sub_add_cancel 1 t)
        rw [hconv_pt] at hconc_ineq
        simp only [smul_eq_mul] at hconc_ineq
        have hc0_nonneg : 0 ≤ (1 - t) * c 0 := mul_nonneg (sub_nonneg.2 ht1) (hc0 0 le_rfl)
        have hcx_ge : t * c r ≤ c x := by linarith
        have hx_eq : x = t * r := by simp only [t, div_mul_cancel₀ _ hr_pos.ne']
        have hcr0 : 0 ≤ r * c r := mul_nonneg hr_pos.le (hc0 r hr_pos.le)
        have ht_quad : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
        calc x * (c r - c x)
            ≤ x * (c r - t * c r) := mul_le_mul_of_nonneg_left (by linarith) hx
          _ = t * (1 - t) * (r * c r) := by rw [hx_eq]; ring
          _ ≤ 1 / 4 * (r * c r) := mul_le_mul_of_nonneg_right ht_quad hcr0
  · refine le_of_eq_of_le ?_
      (pigouRatio_le_pigouBound id_mem_concaveLatencies zero_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2))
    norm_num [pigouRatio]

/-- **Price of anarchy for concave latencies is at most `4/3`** ([Roughgarden2007Routing],
Exercise 18.6): every nonatomic congestion game whose latencies belong to `concaveLatencies` has
price of anarchy at most `4/3`. -/
theorem NonatomicCongestionGame.IsWardrop.cost_le_four_thirds_of_mem_concaveLatencies
    {K P E : Type*} [Fintype P] [DecidableEq K] [DecidableEq E] [Finite E]
    {G : NonatomicCongestionGame K P E} (hG : ∀ e, G.latency e ∈ concaveLatencies)
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ 4 / 3 * G.cost g := by
  have h := hf.cost_le_toReal_pigouBound_mul (C := concaveLatencies)
    (by rw [pigouBound_concaveLatencies]; exact ENNReal.ofReal_ne_top) hG
    (fun e => (hG e).1) (fun e => (hG e).2.1) hg
  rwa [pigouBound_concaveLatencies, ENNReal.toReal_ofReal (by norm_num)] at h

/-! ### Exercise 18.1: asymptotic growth of the polynomial Pigou bound -/

/-- Real-parameter asymptotics of the polynomial Pigou bound:
`(1 - p * (p + 1) ^ (-(p + 1) / p))⁻¹ * (Real.log p / p) → 1` as `p → ∞`. -/
private theorem tendsto_polynomialPigouBound_mul_log_div :
    Tendsto (fun p : ℝ => (1 - p * (p + 1) ^ (-(p + 1) / p))⁻¹ * (Real.log p / p))
      atTop (𝓝 1) := by
  set u : ℝ → ℝ := fun p => Real.log (p + 1) / p
  have hu_zero : Tendsto u atTop (𝓝 0) := by
    have hlog_div : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa only [pow_one, one_mul, add_zero] using
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h1 : Tendsto (fun p : ℝ => Real.log (p + 1) / (p + 1)) atTop (𝓝 0) :=
      hlog_div.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
    have h2 : Tendsto (fun p : ℝ => 1 + p⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_inv_atTop_zero
    have hprod := h1.mul h2
    rw [zero_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with p hp
    dsimp only [u]
    have hp0 : p ≠ 0 := by linarith
    have hp1 : p + 1 ≠ 0 := by linarith
    field_simp
  have hu_pos : ∀ᶠ p in atTop, u p ∈ Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
    exact div_pos (Real.log_pos (by linarith)) (by linarith)
  have hu_nhds : Tendsto u atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_zero hu_pos
  have hexp_slope : Tendsto (fun p : ℝ => (1 - Real.exp (-u p)) / u p) atTop (𝓝 1) := by
    let ψ : ℝ → ℝ := fun y => 1 - Real.exp (-y)
    have hderiv : HasDerivAt ψ 1 0 := by
      have h1 := ((Real.hasDerivAt_exp (-(0 : ℝ))).comp (0 : ℝ)
        (hasDerivAt_neg (0 : ℝ))).const_sub (1 : ℝ)
      simpa only [ψ, Function.comp_def, neg_zero, Real.exp_zero, mul_neg, mul_one, neg_neg] using h1
    have hsl := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hderiv.hasDerivWithinAt
    refine (hsl.comp hu_nhds).congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with p _
    simp only [Function.comp_apply, slope_def_field, ψ, neg_zero, Real.exp_zero, sub_self, sub_zero]
  have hlog_ratio : Tendsto (fun p : ℝ => Real.log (p + 1) / Real.log p) atTop (𝓝 1) := by
    have h1p : Tendsto (fun p : ℝ => 1 + p⁻¹) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero
    have hlog1p : Tendsto (fun p : ℝ => Real.log (1 + p⁻¹)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using
        (Real.continuousAt_log one_ne_zero).tendsto.comp h1p
    have hinv_log : Tendsto (fun p : ℝ => (Real.log p)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hsum : Tendsto (fun p : ℝ => 1 + Real.log (1 + p⁻¹) * (Real.log p)⁻¹) atTop (𝓝 1) := by
      simpa only [mul_zero, add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add (hlog1p.mul hinv_log)
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
    have hp0 : 0 < p := by linarith
    have hp_inv_pos : 0 < 1 + p⁻¹ := by positivity
    have hlogp_ne : Real.log p ≠ 0 := (Real.log_pos (by linarith)).ne'
    have hmul : p + 1 = p * (1 + p⁻¹) := by field_simp [hp0.ne']
    rw [hmul, Real.log_mul hp0.ne' hp_inv_pos.ne']
    field_simp [hlogp_ne]
  have hrem : Tendsto (fun p : ℝ => (1 + p⁻¹)⁻¹ * (Real.log p)⁻¹ * Real.exp (-u p))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun p : ℝ => (1 + p⁻¹)⁻¹) atTop (𝓝 1) := by
      have h1p : Tendsto (fun p : ℝ => 1 + p⁻¹) atTop (𝓝 1) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_inv_atTop_zero
      simpa only [inv_one] using h1p.inv₀ one_ne_zero
    have h2 : Tendsto (fun p : ℝ => (Real.log p)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have h3 : Tendsto (fun p : ℝ => Real.exp (-u p)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
        Real.continuous_exp.continuousAt.tendsto.comp hu_zero.neg
    simpa only [mul_zero, zero_mul] using (h1.mul h2).mul h3
  have hF : Tendsto
      (fun p : ℝ => (1 - p * (p + 1) ^ (-(p + 1) / p)) * (p / Real.log p)) atTop (𝓝 1) := by
    have hmain : Tendsto
        (fun p : ℝ => ((1 - Real.exp (-u p)) / u p) * (Real.log (p + 1) / Real.log p) +
          (1 + p⁻¹)⁻¹ * (Real.log p)⁻¹ * Real.exp (-u p)) atTop (𝓝 1) := by
      simpa only [mul_one, add_zero] using (hexp_slope.mul hlog_ratio).add hrem
    refine hmain.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
    have hp0 : 0 < p := by linarith
    have hp1 : 0 < p + 1 := by linarith
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlogp1 : 0 < Real.log (p + 1) := Real.log_pos (by linarith)
    have hrpow : (p + 1) ^ (-(p + 1) / p) = (p + 1)⁻¹ * Real.exp (-u p) := by
      rw [Real.rpow_def_of_pos hp1]
      have hexp_eq : Real.log (p + 1) * (-(p + 1) / p) = -Real.log (p + 1) + -u p := by
        dsimp only [u]
        field_simp [hp0.ne']
        ring
      rw [hexp_eq, Real.exp_add, Real.exp_neg, Real.exp_log hp1]
    rw [hrpow]
    dsimp only [u]
    have h1pinv : 1 + p⁻¹ ≠ 0 := by positivity
    field_simp [hp0.ne', hp1.ne', hlogp.ne', hlogp1.ne', h1pinv]
    ring
  have hinv := hF.inv₀ one_ne_zero
  rw [inv_one] at hinv
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
  have hp0 : p ≠ 0 := by linarith
  have hlogp : Real.log p ≠ 0 := (Real.log_pos (by linarith)).ne'
  field_simp [hp0, hlogp]

/-- Natural-number degree form of the polynomial Pigou bound asymptotics:
`(1 - d * (d + 1) ^ (-(d + 1) / d))⁻¹ * (Real.log d / d) → 1` as `d → ∞`. -/
private theorem tendsto_polynomialPigouBound_nat_mul_log_div :
    Tendsto (fun d : ℕ =>
        (1 - (d : ℝ) * ((d : ℝ) + 1) ^ (-((d : ℝ) + 1) / (d : ℝ)))⁻¹ * (Real.log d / d))
      atTop (𝓝 1) := by
  have h := tendsto_polynomialPigouBound_mul_log_div.comp tendsto_natCast_atTop_atTop
  refine h.congr fun d => ?_
  simp only [Function.comp_apply, neg_add_rev]

/-- Asymptotic growth of `pigouBound (polynomialLatencies d)` ([Roughgarden2007Routing],
Exercise 18.1): `(pigouBound (polynomialLatencies d)).toReal * (Real.log d / d) → 1` as `d → ∞`. -/
theorem tendsto_toReal_pigouBound_polynomialLatencies_mul_log_div :
    Tendsto (fun d : ℕ => (pigouBound (polynomialLatencies d)).toReal * (Real.log d / d))
      atTop (𝓝 1) := by
  refine tendsto_polynomialPigouBound_nat_mul_log_div.congr fun d => ?_
  rw [pigouBound_polynomialLatencies,
    ENNReal.toReal_ofReal (inv_nonneg.2 (one_sub_pigouConst_pos d).le), neg_div]

/-! ### Capacity augmentation (Theorem 18.29, Corollary 18.30, Example 18.28, Exercise 18.8) -/

namespace NonatomicCongestionGame

section CapacityAugmentation

variable {K P E : Type*} [Fintype P] [DecidableEq E] (G : NonatomicCongestionGame K P E)

/-- The demand-scaled game `(G, α r, c)` where every commodity's traffic rate is multiplied by `α`
([Roughgarden2007Routing], Section 18.5.2). -/
def scaleRate (α : ℝ) : NonatomicCongestionGame K P E :=
  { G with rate := fun k => α * G.rate k }

/-- The link-speedup game `(G, r, c̃)` with `c̃_e(x) = c_e(x / α) / α` ([Roughgarden2007Routing],
Corollary 18.30, where `α = 2`). -/
noncomputable def speedup (α : ℝ) : NonatomicCongestionGame K P E :=
  { G with latency := fun e x => G.latency e (x / α) / α }

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem scaleRate_commodity (α : ℝ) : (G.scaleRate α).commodity = G.commodity := by rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem scaleRate_resources (α : ℝ) : (G.scaleRate α).resources = G.resources := by rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem scaleRate_rate (α : ℝ) (k : K) : (G.scaleRate α).rate k = α * G.rate k := by rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem scaleRate_latency (α : ℝ) : (G.scaleRate α).latency = G.latency := by rfl

@[simp]
theorem scaleRate_edgeFlow (α : ℝ) (f : P → ℝ) (e : E) :
    (G.scaleRate α).edgeFlow f e = G.edgeFlow f e := by
  rfl

@[simp]
theorem scaleRate_pathLatency (α : ℝ) (f : P → ℝ) (p : P) :
    (G.scaleRate α).pathLatency f p = G.pathLatency f p := by
  rfl

@[simp]
theorem scaleRate_cost (α : ℝ) (f : P → ℝ) :
    (G.scaleRate α).cost f = G.cost f := by
  rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem speedup_commodity (α : ℝ) : (G.speedup α).commodity = G.commodity := by rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem speedup_resources (α : ℝ) : (G.speedup α).resources = G.resources := by rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem speedup_rate (α : ℝ) : (G.speedup α).rate = G.rate := by rfl

omit [Fintype P] [DecidableEq E] in
@[simp]
theorem speedup_latency (α : ℝ) (e : E) (x : ℝ) :
    (G.speedup α).latency e x = G.latency e (x / α) / α := by rfl

@[simp]
theorem speedup_edgeFlow (α : ℝ) (f : P → ℝ) (e : E) :
    (G.speedup α).edgeFlow f e = G.edgeFlow f e := by
  rfl

variable {G}

omit [DecidableEq E] in
/-- Rescaling a feasible flow `g` by `α ≥ 0` produces a feasible flow of `G.scaleRate α`. -/
theorem IsFeasible.smul_scaleRate [DecidableEq K] {g : P → ℝ} (hg : G.IsFeasible g) {α : ℝ}
    (hα : 0 ≤ α) : (G.scaleRate α).IsFeasible (α • g) := by
  refine ⟨fun p => mul_nonneg hα (hg.1 p), fun k => ?_⟩
  dsimp only [scaleRate]
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact congrArg (α * ·) (hg.2 k)

omit [DecidableEq E] in
/-- Rescaling a feasible flow of `G.scaleRate α` (`α > 0`) by `α⁻¹` yields a feasible flow
of `G`. -/
private theorem isFeasible_inv_smul_of_scaleRate [DecidableEq K] {α : ℝ} (hα : 0 < α)
    {g : P → ℝ} (hg : (G.scaleRate α).IsFeasible g) :
    G.IsFeasible (α⁻¹ • g) := by
  refine ⟨fun p => mul_nonneg (inv_nonneg.2 hα.le) (hg.1 p), fun k => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  change α⁻¹ * ∑ p with (G.scaleRate α).commodity p = k, g p = G.rate k
  rw [hg.2 k]
  exact inv_mul_cancel_left₀ hα.ne' (G.rate k)

/-- **General `(1 + δ)r` capacity-augmentation bound** ([Roughgarden2007Routing],
Exercise 18.8(c)): if resource latencies are nonnegative and nondecreasing on `[0, ∞)`, `0 < δ`,
`f` is a Wardrop equilibrium for `G`, and `g` is feasible for `G.scaleRate (1 + δ)`, then
`G.cost f ≤ (1 / δ) * G.cost g`. -/
theorem IsWardrop.cost_le_inv_mul_of_scaleRate [DecidableEq K] [Finite E]
    (h0 : ∀ e x, 0 ≤ x → 0 ≤ G.latency e x)
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {δ : ℝ} (hδ : 0 < δ) {f g : P → ℝ}
    (hf : G.IsWardrop f) (hg : (G.scaleRate (1 + δ)).IsFeasible g) :
    G.cost f ≤ (1 / δ) * G.cost g := by
  have := Fintype.ofFinite E
  let cbar : E → ℝ → ℝ := fun e x => max (G.latency e (G.edgeFlow f e)) (G.latency e x)
  let Gbar : NonatomicCongestionGame K P E := { G with latency := cbar }
  have hdiff_le : Gbar.cost g - G.cost g ≤ G.cost f := by
    rw [Gbar.cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    have hfe : 0 ≤ G.edgeFlow f e := G.edgeFlow_nonneg hf.1.1 e
    have hge : 0 ≤ G.edgeFlow g e := G.edgeFlow_nonneg hg.1 e
    change G.edgeFlow g e * cbar e (G.edgeFlow g e) -
        G.edgeFlow g e * G.latency e (G.edgeFlow g e) ≤
      G.edgeFlow f e * G.latency e (G.edgeFlow f e)
    dsimp only [cbar]
    rcases le_total (G.edgeFlow f e) (G.edgeFlow g e) with hle | hle
    · rw [max_eq_right (hm e hfe hge hle), sub_self]
      exact mul_nonneg hfe (h0 e _ hfe)
    · rw [max_eq_left (hm e hge hfe hle)]
      have hlat_ge : 0 ≤ G.latency e (G.edgeFlow g e) := h0 e _ hge
      have hlat_fe : 0 ≤ G.latency e (G.edgeFlow f e) := h0 e _ hfe
      nlinarith
  have hlower : (1 + δ) * G.cost f ≤ Gbar.cost g := by
    have h1δ : 0 < 1 + δ := by linarith
    have hvi := hf.cost_le_sum_mul_pathLatency (isFeasible_inv_smul_of_scaleRate h1δ hg)
    have hsum_eq : ∑ p, ((1 + δ)⁻¹ • g) p * G.pathLatency f p =
        (1 + δ)⁻¹ * ∑ p, g p * G.pathLatency f p := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [hsum_eq, le_inv_mul_iff₀ h1δ] at hvi
    refine hvi.trans (Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left ?_ (hg.1 p))
    exact Finset.sum_le_sum fun e _ => le_max_left _ _
  have hmul : δ * G.cost f ≤ G.cost g := by linarith
  rw [one_div, le_inv_mul_iff₀ hδ]
  exact hmul

/-- **Roughgarden–Tardos `2r` capacity-augmentation theorem** ([Roughgarden2007Routing],
Theorem 18.29, originally [RoughgardenTardos2002]): for arbitrary nonnegative nondecreasing
latencies on `[0, ∞)`, a Wardrop equilibrium for `G` costs at most any flow feasible for twice the
traffic `(G.scaleRate 2)`. -/
theorem IsWardrop.cost_le_of_scaleRate_two [DecidableEq K] [Finite E]
    (h0 : ∀ e x, 0 ≤ x → 0 ≤ G.latency e x)
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : (G.scaleRate 2).IsFeasible g) :
    G.cost f ≤ G.cost g := by
  have hg' : (G.scaleRate (1 + 1)).IsFeasible g := by norm_num; exact hg
  have h := hf.cost_le_inv_mul_of_scaleRate h0 hm zero_lt_one hg'
  linarith

/-- **Link-speedup corollary, general `(1 + δ)` factor** ([Roughgarden2007Routing], Corollary 18.30
and Exercise 18.8(a)): deduced directly from `IsWardrop.cost_le_inv_mul_of_scaleRate` by rescaling
`f̃` to `(1 + δ)⁻¹ • f̃`. -/
theorem IsWardrop.speedup_cost_le [DecidableEq K] [Finite E]
    (h0 : ∀ e x, 0 ≤ x → 0 ≤ G.latency e x)
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {δ : ℝ} (hδ : 0 < δ) {f_tilde g : P → ℝ}
    (hf : (G.speedup (1 + δ)).IsWardrop f_tilde) (hg : G.IsFeasible g) :
    (G.speedup (1 + δ)).cost f_tilde ≤ (1 / δ) * G.cost g := by
  have := Fintype.ofFinite E
  set α := 1 + δ
  have hα : 0 < α := by linarith
  let G' := G.scaleRate α⁻¹
  have hf' : G'.IsWardrop (α⁻¹ • f_tilde) := by
    refine ⟨⟨fun p => mul_nonneg (inv_nonneg.2 hα.le) (hf.1.1 p), fun k => ?_⟩,
      fun p q hpq hpos => ?_⟩
    · dsimp only [G', scaleRate]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact congrArg (α⁻¹ * ·) (hf.1.2 k)
    · have hfp_pos : 0 < f_tilde p := by
        simp only [Pi.smul_apply, smul_eq_mul] at hpos
        exact pos_of_mul_pos_right hpos (inv_nonneg.2 hα.le)
      have hle := hf.2 p q hpq hfp_pos
      have hlat : ∀ r, (G.speedup α).pathLatency f_tilde r =
          α⁻¹ * G'.pathLatency (α⁻¹ • f_tilde) r := by
        intro r
        simp only [pathLatency, speedup_resources, speedup_latency, speedup_edgeFlow, G',
          scaleRate_resources, scaleRate_latency, scaleRate_edgeFlow, G.edgeFlow_smul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [div_eq_inv_mul, div_eq_inv_mul]
      rw [hlat p, hlat q] at hle
      exact le_of_mul_le_mul_left hle (inv_pos.2 hα)
  have hg' : (G'.scaleRate α).IsFeasible g := by
    refine ⟨hg.1, fun k => ?_⟩
    simp only [G', scaleRate_commodity, scaleRate_rate, mul_inv_cancel_left₀ hα.ne']
    exact hg.2 k
  have hcost_eq : (G.speedup α).cost f_tilde = G'.cost (α⁻¹ • f_tilde) := by
    rw [(G.speedup α).cost_eq_sum_edgeFlow, G'.cost_eq_sum_edgeFlow]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [speedup_edgeFlow, speedup_latency, G', scaleRate_edgeFlow, scaleRate_latency,
      G.edgeFlow_smul]
    field_simp [hα.ne']
  rw [hcost_eq]
  exact IsWardrop.cost_le_inv_mul_of_scaleRate (G := G') h0 hm hδ hf' hg'

/-- **Doubling link speed beats centralized routing** ([Roughgarden2007Routing], Corollary 18.30
and Exercise 18.8(a)): if `f̃` is a Wardrop equilibrium for `G.speedup 2` (`c̃_e(x) = c_e(x/2)/2`)
and `g` is feasible for `G`, then `(G.speedup 2).cost f̃ ≤ G.cost g`. -/
theorem IsWardrop.speedup_two_cost_le [DecidableEq K] [Finite E]
    (h0 : ∀ e x, 0 ≤ x → 0 ≤ G.latency e x)
    (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f_tilde g : P → ℝ} (hf : (G.speedup 2).IsWardrop f_tilde) (hg : G.IsFeasible g) :
    (G.speedup 2).cost f_tilde ≤ G.cost g := by
  have hf' : (G.speedup (1 + 1)).IsWardrop f_tilde := by norm_num; exact hf
  have h := hf'.speedup_cost_le h0 hm zero_lt_one hg
  norm_num at h ⊢
  exact h

/-- **Tightness of the `(1 + δ)r` capacity-augmentation bound `1 / δ`** ([Roughgarden2007Routing],
Example 18.28 and Exercise 18.8(d)): for every `δ > 0` and `ε > 0`, there exist a degree `d : ℕ`
and a flow `g` feasible for `(pigouNetwork (· ^ d) 1).scaleRate (1 + δ)` with `cost g < δ + ε`
(while the Wardrop equilibrium `![1, 0]` at rate `1` has cost `1`). Consequently, no factor
`β < 1 / δ` can replace `1 / δ` in `IsWardrop.cost_le_inv_mul_of_scaleRate`. -/
theorem exists_pigouNetwork_pow_scaleRate_cost_lt {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (d : ℕ) (g : Fin 2 → ℝ),
      ((pigouNetwork (fun x : ℝ => x ^ d) 1).scaleRate (1 + δ)).IsFeasible g ∧
        (pigouNetwork (fun x : ℝ => x ^ d) 1).cost g < δ + ε := by
  set η := min (1 / 2) (ε / 2)
  have hη_pos : 0 < η := lt_min (by norm_num) (half_pos hε)
  have hη_le_half : η ≤ 1 / 2 := min_le_left _ _
  have hη_le_eps : η ≤ ε / 2 := min_le_right _ _
  set t := 1 - η
  have ht_pos : 0 < t := by linarith
  have ht_lt_one : t < 1 := by linarith
  obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one hη_pos ht_lt_one
  refine ⟨d, ![t, 1 + δ - t], ?_, ?_⟩
  · refine ⟨fun p => ?_, fun _ => ?_⟩
    · fin_cases p
      · exact ht_pos.le
      · change 0 ≤ 1 + δ - t
        linarith
    · simp [scaleRate_commodity, scaleRate_rate, pigouNetwork, Fin.sum_univ_two]
  · rw [pigouNetwork_cost]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_pow, mul_one]
    have hpow : t * t ^ d ≤ t ^ d := mul_le_of_le_one_left (pow_nonneg ht_pos.le d) ht_lt_one.le
    have hsub : 1 + δ - t = δ + η := by dsimp only [t]; ring
    rw [hsub]
    linarith

/-! ### Exercise 18.8(e): exact affine capacity-augmentation threshold `δ = 1/4` -/

/-- **Affine capacity augmentation at `(5/4) r`** ([Roughgarden2007Routing], Exercise 18.8(e);
credited in Section 18.6 to Chakrabarty, 2004, and Correa, Schulz and Stier-Moses, 2005): if `G`
has nonnegative affine latencies, `1 / 4 ≤ δ`, `f` is a Wardrop equilibrium for `G`, and `g` is
feasible for `G.scaleRate (1 + δ)`, then `G.cost f ≤ G.cost g`. -/
theorem HasAffineLatencies.cost_le_of_scaleRate [DecidableEq K] [Finite E]
    (hG : G.HasAffineLatencies) {δ : ℝ} (hδ : 1 / 4 ≤ δ)
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : (G.scaleRate (1 + δ)).IsFeasible g) :
    G.cost f ≤ G.cost g := by
  have := Fintype.ofFinite E
  obtain ⟨a, b, ha, hb, hl⟩ := hG
  have h1δ : 0 < 1 + δ := by linarith
  have hvi := (isWardrop_iff_variationalInequality.1 hf).2 _
    (isFeasible_inv_smul_of_scaleRate h1δ hg)
  have hrhs : ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow ((1 + δ)⁻¹ • g) e =
      (1 + δ)⁻¹ * ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow g e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [G.edgeFlow_smul]
    ring
  rw [hrhs, le_inv_mul_iff₀ h1δ] at hvi
  have hcost_f_nonneg : 0 ≤ G.cost f :=
    G.cost_nonneg (fun e x hx => by rw [hl]; nlinarith [ha e, hb e]) hf.1.1
  have hcost_f_eq : G.cost f = ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow f e := by
    rw [G.cost_eq_sum_edgeFlow]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  rw [← hcost_f_eq] at hvi
  have h54 : (5 / 4 : ℝ) * G.cost f ≤ ∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow g e := by
    have : (5 / 4 : ℝ) * G.cost f ≤ (1 + δ) * G.cost f :=
      mul_le_mul_of_nonneg_right (by linarith) hcost_f_nonneg
    linarith
  rw [G.cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow]
  have hsq : ∑ e, G.edgeFlow f e * G.latency e (G.edgeFlow f e) +
      (∑ e, G.latency e (G.edgeFlow f e) * G.edgeFlow g e - (5 / 4 : ℝ) * G.cost f) ≤
      ∑ e, G.edgeFlow g e * G.latency e (G.edgeFlow g e) := by
    rw [hcost_f_eq, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [hl, hl]
    have hfe : 0 ≤ G.edgeFlow f e := G.edgeFlow_nonneg hf.1.1 e
    nlinarith [sq_nonneg (G.edgeFlow g e - G.edgeFlow f e / 2), ha e, hb e]
  linarith

/-- **Exact characterization of the affine augmentation threshold** ([Roughgarden2007Routing],
Exercise 18.8(e)): for `0 ≤ δ`, every nonatomic congestion game with nonnegative affine latencies
satisfies `G.cost f ≤ G.cost f*` (for Wardrop `f` at rate `r` and feasible/optimal `f*` at rate
`(1 + δ) r`) if and only if `1 / 4 ≤ δ`. -/
theorem affine_scaleRate_bound_iff {δ : ℝ} (hδ0 : 0 ≤ δ) :
    (∀ (K P E : Type) [Fintype P] [Finite E] [DecidableEq K] [DecidableEq E]
      (G : NonatomicCongestionGame K P E) (f g : P → ℝ),
        G.HasAffineLatencies → G.IsWardrop f → ((G.scaleRate (1 + δ)).IsOptimal g) →
          G.cost f ≤ G.cost g) ↔
      1 / 4 ≤ δ := by
  refine ⟨fun h => ?_, fun hδ K P E _ _ _ _ G f g hG hf hg =>
    hG.cost_le_of_scaleRate hδ hf hg.1⟩
  by_contra hlt
  push Not at hlt
  let G := pigouNetwork (fun x : ℝ => x) 1
  have hG : G.HasAffineLatencies :=
    ⟨![1, 0], ![0, 1], fun e => by fin_cases e <;> norm_num,
      fun e => by fin_cases e <;> norm_num, fun e x => by fin_cases e <;> simp [G, pigouNetwork]⟩
  have hf : G.IsWardrop ![1, 0] := pigouNetwork_isWardrop _ zero_le_one
  let g : Fin 2 → ℝ := ![1 / 2, 1 / 2 + δ]
  have hg_feas : (G.scaleRate (1 + δ)).IsFeasible g := by
    refine ⟨fun p => ?_, fun _ => ?_⟩
    · fin_cases p
      · simp [g]
      · simp [g]; linarith
    · simp [G, scaleRate_commodity, scaleRate_rate, pigouNetwork, g, Fin.sum_univ_two]
      ring
  have hg_opt : (G.scaleRate (1 + δ)).IsOptimal g := by
    refine ⟨hg_feas, fun q hq => ?_⟩
    simp only [scaleRate_cost, G, pigouNetwork_cost, g, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one]
    have hsum : q 0 + q 1 = 1 + δ := by
      have hs := hq.2 ()
      simpa [G, scaleRate_commodity, scaleRate_rate, pigouNetwork, Fin.sum_univ_two] using hs
    nlinarith [sq_nonneg (q 0 - 1 / 2)]
  have hbound := h Unit (Fin 2) (Fin 2) G ![1, 0] g hG hf hg_opt
  simp only [G, pigouNetwork_cost, g, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
    add_zero] at hbound
  linarith

end CapacityAugmentation

end NonatomicCongestionGame

/-! ### Exercise 18.8(b): atomic counterexample to `2r` capacity augmentation -/

namespace CongestionGame

/-- Four-player, four-resource unweighted atomic congestion game with nondecreasing polynomial
latency `k ^ 4`: player `i`'s strategy `true` uses `{i}`, and `false` uses the other three
resources `Finset.univ.erase i`. -/
private def atomicAugmentCounterexample : CongestionGame (Fin 4) (fun _ => Bool) (Fin 4) where
  resources i b := if b then {i} else Finset.univ.erase i
  latency _ k := (k : ℝ) ^ 4

/-- Eight-player unweighted atomic congestion game representing doubled traffic `2r` (two players
per commodity `i ∈ Fin 4`) on the exact same resources and `k ^ 4` latencies. -/
private def atomicAugmentDoubled : CongestionGame (Fin 2 × Fin 4) (fun _ => Bool) (Fin 4) where
  resources p b := if b then {p.2} else Finset.univ.erase p.2
  latency _ k := (k : ℝ) ^ 4

/-- **Atomic counterexample to `2r` capacity augmentation** ([Roughgarden2007Routing],
Exercise 18.8(b)): there is a four-commodity network with nonnegative nondecreasing polynomial
latency `k ^ 4` such that the unweighted `4`-player atomic congestion game `C₁` has a pure Nash
equilibrium `s` of social cost `972`, whereas the doubled `8`-player atomic congestion game `C₂`
(two unit-weight players per commodity, and equivalently a `4`-player weight-`2` profile) has a
profile `s*` of social cost `128 < 972`. -/
theorem exists_atomic_pureNash_socialCost_gt_doubled :
    ∃ (C₁ : CongestionGame (Fin 4) (fun _ => Bool) (Fin 4))
      (C₂ : CongestionGame (Fin 2 × Fin 4) (fun _ => Bool) (Fin 4))
      (s : Fin 4 → Bool) (s_star : Fin 2 × Fin 4 → Bool),
      (∀ p b, C₂.resources p b = C₁.resources p.2 b) ∧
      (∀ e, C₂.latency e = C₁.latency e) ∧
      (∀ e, Monotone (C₁.latency e)) ∧
      (∀ e k, 0 ≤ C₁.latency e k) ∧
      C₁.toCostGame.IsPureNash s ∧
      C₁.toCostGame.socialCost s = 972 ∧
      C₂.toCostGame.socialCost s_star = 128 ∧
      C₂.toCostGame.socialCost s_star < C₁.toCostGame.socialCost s := by
  have hc1 : atomicAugmentCounterexample.toCostGame.socialCost (fun _ => false) = 972 := by
    rw [socialCost_toCostGame]
    have h : ∑ e : Fin 4, atomicAugmentCounterexample.load (fun _ => false) e *
        atomicAugmentCounterexample.load (fun _ => false) e ^ 4 = 972 := by decide
    change ∑ e : Fin 4, (atomicAugmentCounterexample.load (fun _ => false) e : ℝ) *
        (atomicAugmentCounterexample.load (fun _ => false) e : ℝ) ^ 4 = 972
    exact_mod_cast h
  have hc2 : atomicAugmentDoubled.toCostGame.socialCost (fun _ => true) = 128 := by
    rw [socialCost_toCostGame]
    have h : ∑ e : Fin 4, atomicAugmentDoubled.load (fun _ => true) e *
        atomicAugmentDoubled.load (fun _ => true) e ^ 4 = 128 := by decide
    change ∑ e : Fin 4, (atomicAugmentDoubled.load (fun _ => true) e : ℝ) *
        (atomicAugmentDoubled.load (fun _ => true) e : ℝ) ^ 4 = 128
    exact_mod_cast h
  refine ⟨atomicAugmentCounterexample, atomicAugmentDoubled, fun _ => false, fun _ => true,
    fun _ _ => rfl, fun _ => rfl,
    fun _ a b hab => pow_le_pow_left₀ (Nat.cast_nonneg a) (by exact_mod_cast hab) 4,
    fun _ k => pow_nonneg (Nat.cast_nonneg k) 4, ?_, hc1, hc2, by linarith⟩
  intro i t
  simp only [toCostGame_cost, atomicAugmentCounterexample, ← Nat.cast_pow, ← Nat.cast_sum,
    Nat.cast_le]
  change (∑ e ∈ (if false then {i} else Finset.univ.erase i),
      atomicAugmentCounterexample.load (fun _ => false) e ^ 4) ≤
    ∑ e ∈ (if (Function.update (fun _ => false) i t) i then {i} else Finset.univ.erase i),
      atomicAugmentCounterexample.load (Function.update (fun _ => false) i t) e ^ 4
  revert i t
  decide

end CongestionGame

/-! ### Braess's paradox and subnetwork bounds (Example 18.4 & Remark 18.22) -/

namespace NonatomicCongestionGame

section Subnetwork

variable {K P₁ P₂ E : Type*} [Fintype P₁] [Fintype P₂] [DecidableEq E]
  (G : NonatomicCongestionGame K P₂ E) (ι : P₁ ↪ P₂)

/-- The subnetwork congestion game obtained by restricting available paths along an injection
`ι : P₁ ↪ P₂` ([Roughgarden2007Routing], Remark 18.22). -/
def restrictPaths : NonatomicCongestionGame K P₁ E where
  commodity p := G.commodity (ι p)
  resources p := G.resources (ι p)
  rate := G.rate
  latency := G.latency

omit [Fintype P₁] [Fintype P₂] [DecidableEq E] in
@[simp]
theorem restrictPaths_commodity (p : P₁) :
    (G.restrictPaths ι).commodity p = G.commodity (ι p) := by rfl

omit [Fintype P₁] [Fintype P₂] [DecidableEq E] in
@[simp]
theorem restrictPaths_resources (p : P₁) :
    (G.restrictPaths ι).resources p = G.resources (ι p) := by rfl

omit [Fintype P₁] [Fintype P₂] [DecidableEq E] in
@[simp]
theorem restrictPaths_rate : (G.restrictPaths ι).rate = G.rate := by rfl

omit [Fintype P₁] [Fintype P₂] [DecidableEq E] in
@[simp]
theorem restrictPaths_latency : (G.restrictPaths ι).latency = G.latency := by rfl

/-- Summing any weighted quantity against `Function.extend ι f₁ 0` over `P₂` reduces to `P₁`. -/
private theorem sum_extend_mul (f₁ : P₁ → ℝ) (w : P₂ → ℝ) :
    ∑ p₂, Function.extend ι f₁ 0 p₂ * w p₂ = ∑ p₁, f₁ p₁ * w (ι p₁) := by
  classical
  have hsub : Finset.univ.image ι ⊆ (Finset.univ : Finset P₂) := Finset.subset_univ _
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image fun _ _ _ _ h => ι.injective h]
    exact Finset.sum_congr rfl fun p₁ _ => by rw [ι.injective.extend_apply]
  · intro p₂ _ hp₂
    rw [Finset.mem_image] at hp₂
    push Not at hp₂
    have hnot : ¬ ∃ p₁, ι p₁ = p₂ := fun ⟨p₁, hp₁⟩ => hp₂ p₁ (Finset.mem_univ p₁) hp₁
    rw [Function.extend_apply' (f := ι) f₁ (0 : P₂ → ℝ) p₂ hnot, Pi.zero_apply, zero_mul]

omit [DecidableEq E] in
/-- Zero-extending a feasible flow of `G.restrictPaths ι` yields a feasible flow of `G`. -/
theorem isFeasible_extend [DecidableEq K] {f₁ : P₁ → ℝ}
    (hf₁ : (G.restrictPaths ι).IsFeasible f₁) :
    G.IsFeasible (Function.extend ι f₁ 0) := by
  refine ⟨fun p₂ => ?_, fun k => ?_⟩
  · by_cases h : ∃ p₁, ι p₁ = p₂
    · obtain ⟨p₁, rfl⟩ := h
      rw [ι.injective.extend_apply]
      exact hf₁.1 p₁
    · rw [Function.extend_apply' (f := ι) f₁ (0 : P₂ → ℝ) p₂ h]
      exact le_rfl
  · have h1 := sum_extend_mul ι f₁ (fun p₂ => if G.commodity p₂ = k then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter] at h1
    rw [h1]
    exact hf₁.2 k

/-- Zero-extension preserves every edge flow. -/
theorem edgeFlow_extend (f₁ : P₁ → ℝ) (e : E) :
    G.edgeFlow (Function.extend ι f₁ 0) e = (G.restrictPaths ι).edgeFlow f₁ e := by
  have h1 := sum_extend_mul ι f₁ (fun p₂ => if e ∈ G.resources p₂ then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter] at h1
  exact h1

/-- Zero-extension preserves total social cost: in particular, adding paths/edges to a network can
only decrease or preserve the minimum feasible cost. -/
theorem cost_extend [Finite E] (f₁ : P₁ → ℝ) :
    G.cost (Function.extend ι f₁ 0) = (G.restrictPaths ι).cost f₁ := by
  have := Fintype.ofFinite E
  rw [G.cost_eq_sum_edgeFlow, (G.restrictPaths ι).cost_eq_sum_edgeFlow]
  exact Finset.sum_congr rfl fun e _ => by rw [G.edgeFlow_extend ι f₁ e]; rfl

/-- **General bound on Braess's paradox** ([Roughgarden2007Routing], Remark 18.22): if `G` has
nonnegative nondecreasing latencies in `C` with `pigouBound C ≠ ⊤`, then any Wardrop equilibrium
`f₂` of the larger network `G` costs at most `(pigouBound C).toReal` times any feasible flow (and
in particular any Wardrop equilibrium) `f₁` of the subnetwork `G.restrictPaths ι`. -/
theorem IsWardrop.cost_le_toReal_pigouBound_mul_restrictPaths [DecidableEq K] [Finite E]
    {G : NonatomicCongestionGame K P₂ E} {C : Set (ℝ → ℝ)}
    (htop : pigouBound C ≠ ⊤) (hC : ∀ e, G.latency e ∈ C)
    (h0 : ∀ e x, 0 ≤ x → 0 ≤ G.latency e x) (hm : ∀ e, MonotoneOn (G.latency e) (Ici 0))
    {f₂ : P₂ → ℝ} (hf₂ : G.IsWardrop f₂)
    {f₁ : P₁ → ℝ} (hf₁ : (G.restrictPaths ι).IsFeasible f₁) :
    G.cost f₂ ≤ (pigouBound C).toReal * (G.restrictPaths ι).cost f₁ := by
  rw [← G.cost_extend ι f₁]
  exact hf₂.cost_le_toReal_pigouBound_mul htop hC h0 hm (G.isFeasible_extend ι hf₁)

/-- **Affine bound on Braess's paradox** ([Roughgarden2007Routing], Remark 18.22): adding edges or
paths to a network with nonnegative affine latencies cannot increase the Wardrop equilibrium cost
by more than a `4/3` factor. -/
theorem HasAffineLatencies.cost_le_four_thirds_restrictPaths [DecidableEq K] [Finite E]
    {G : NonatomicCongestionGame K P₂ E} (hG : G.HasAffineLatencies)
    {f₂ : P₂ → ℝ} (hf₂ : G.IsWardrop f₂)
    {f₁ : P₁ → ℝ} (hf₁ : (G.restrictPaths ι).IsFeasible f₁) :
    G.cost f₂ ≤ 4 / 3 * (G.restrictPaths ι).cost f₁ := by
  rw [← G.cost_extend ι f₁]
  exact hf₂.cost_le hG (G.isFeasible_extend ι hf₁)

end Subnetwork

section BraessWheatstone

/-- **Initial four-node Wheatstone network** before adding the cross edge
([Roughgarden2007Routing], Example 18.4, Figure 18.2(a)): edges `0 = (s, v)` and `3 = (w, t)` have
latency `x`, edges `1 = (v, t)` and `2 = (s, w)` have latency `1`; path `0` is `{0, 1}` and path
`1` is `{2, 3}`, routing `1` unit of traffic. -/
def braessInitial : NonatomicCongestionGame Unit (Fin 2) (Fin 4) where
  commodity _ := ()
  resources p := if p = 0 then {0, 1} else {2, 3}
  rate _ := 1
  latency e x := if e = 0 ∨ e = 3 then x else 1

/-- **Augmented four-node Wheatstone network** after adding the zero-cost edge `4 = (v, w)` and
cross path `2 = {0, 4, 3}` (`s → v → w → t`, [Roughgarden2007Routing], Example 18.4,
Figure 18.2(b)). -/
def braessAugmented : NonatomicCongestionGame Unit (Fin 3) (Fin 5) where
  commodity _ := ()
  resources p := match p with
    | 0 => {0, 1}
    | 1 => {2, 3}
    | 2 => {0, 4, 3}
  rate _ := 1
  latency e x := match e with
    | 0 => x
    | 1 => 1
    | 2 => 1
    | 3 => x
    | 4 => 0

@[simp]
theorem braessInitial_commodity (p : Fin 2) : braessInitial.commodity p = () := by rfl

@[simp]
theorem braessInitial_rate (k : Unit) : braessInitial.rate k = 1 := by rfl

@[simp]
theorem braessAugmented_commodity (p : Fin 3) : braessAugmented.commodity p = () := by rfl

@[simp]
theorem braessAugmented_rate (k : Unit) : braessAugmented.rate k = 1 := by rfl

/-- Both Wheatstone networks have nonnegative affine latencies. -/
theorem braessInitial_hasAffineLatencies : braessInitial.HasAffineLatencies :=
  ⟨![1, 0, 0, 1], ![0, 1, 1, 0],
    fun e => by fin_cases e <;> norm_num,
    fun e => by fin_cases e <;> norm_num,
    fun e x => by fin_cases e <;> simp [braessInitial]⟩

theorem braessAugmented_hasAffineLatencies : braessAugmented.HasAffineLatencies :=
  ⟨![1, 0, 0, 1, 0], ![0, 1, 1, 0, 0],
    fun e => by fin_cases e <;> norm_num,
    fun e => by fin_cases e <;> norm_num,
    fun e x => by fin_cases e <;> simp [braessAugmented]⟩

private theorem braessInitial_edgeFlow_zero (f : Fin 2 → ℝ) :
    braessInitial.edgeFlow f 0 = f 0 := by
  rw [edgeFlow, Finset.sum_filter, Fin.sum_univ_two]
  have h0 : (0 : Fin 4) ∈ braessInitial.resources 0 := by decide
  have h1 : (0 : Fin 4) ∉ braessInitial.resources 1 := by decide
  simp only [h0, h1, ↓reduceIte, add_zero]

private theorem braessInitial_edgeFlow_three (f : Fin 2 → ℝ) :
    braessInitial.edgeFlow f 3 = f 1 := by
  rw [edgeFlow, Finset.sum_filter, Fin.sum_univ_two]
  have h0 : (3 : Fin 4) ∉ braessInitial.resources 0 := by decide
  have h1 : (3 : Fin 4) ∈ braessInitial.resources 1 := by decide
  simp only [h0, h1, ↓reduceIte, zero_add]

/-- Path latencies in `braessInitial`: `f 0 + 1` and `1 + f 1`. -/
theorem braessInitial_pathLatency (f : Fin 2 → ℝ) (p : Fin 2) :
    braessInitial.pathLatency f p = if p = 0 then f 0 + 1 else 1 + f 1 := by
  fin_cases p
  · change ∑ e ∈ ({0, 1} : Finset (Fin 4)), braessInitial.latency e (braessInitial.edgeFlow f e) =
      if (0 : Fin 2) = 0 then f 0 + 1 else 1 + f 1
    rw [Finset.sum_pair (by decide), braessInitial_edgeFlow_zero]
    simp [braessInitial]
  · change ∑ e ∈ ({2, 3} : Finset (Fin 4)), braessInitial.latency e (braessInitial.edgeFlow f e) =
      if (1 : Fin 2) = 0 then f 0 + 1 else 1 + f 1
    rw [Finset.sum_pair (by decide), braessInitial_edgeFlow_three]
    simp [braessInitial]

/-- Cost formula for `braessInitial`. -/
theorem braessInitial_cost (f : Fin 2 → ℝ) :
    braessInitial.cost f = f 0 * (f 0 + 1) + f 1 * (1 + f 1) := by
  simp only [cost, braessInitial_pathLatency, Fin.sum_univ_two, ↓reduceIte]
  norm_num

/-- **Unique Wardrop equilibrium of the initial Braess network** ([Roughgarden2007Routing],
Example 18.4): `f` is a Wardrop equilibrium of `braessInitial` iff `f = ![1 / 2, 1 / 2]`, with
total cost `3 / 2`. -/
theorem braessInitial_isWardrop_iff {f : Fin 2 → ℝ} :
    braessInitial.IsWardrop f ↔ f = ![1 / 2, 1 / 2] := by
  have hw_half : braessInitial.IsWardrop ![1 / 2, 1 / 2] := by
    refine ⟨⟨fun p => by fin_cases p <;> norm_num, fun _ => ?_⟩, fun p q _ _ => ?_⟩
    · simp [braessInitial, Fin.sum_univ_two]
      norm_num
    · rw [braessInitial_pathLatency, braessInitial_pathLatency]
      fin_cases p <;> fin_cases q <;> norm_num
  refine ⟨fun hf => ?_, fun h => h ▸ hw_half⟩
  have hm : ∀ e, MonotoneOn (braessInitial.latency e) (Ici 0) := fun e x _ y _ hxy => by
    fin_cases e <;> simp [braessInitial, hxy]
  have h0 := isWardrop_latency_eq hm hf hw_half 0
  have h3 := isWardrop_latency_eq hm hf hw_half 3
  rw [braessInitial_edgeFlow_zero, braessInitial_edgeFlow_zero] at h0
  rw [braessInitial_edgeFlow_three, braessInitial_edgeFlow_three] at h3
  ext i
  fin_cases i
  · simpa [braessInitial] using h0
  · simpa [braessInitial] using h3

/-- Path latencies in `braessAugmented`. -/
theorem braessAugmented_pathLatency (f : Fin 3 → ℝ) :
    braessAugmented.pathLatency f 0 = (f 0 + f 2) + 1 ∧
      braessAugmented.pathLatency f 1 = 1 + (f 1 + f 2) ∧
      braessAugmented.pathLatency f 2 = (f 0 + f 2) + (f 1 + f 2) := by
  have he0 : braessAugmented.edgeFlow f 0 = f 0 + f 2 := by
    rw [edgeFlow, Finset.sum_filter, Fin.sum_univ_three]
    have h0 : (0 : Fin 5) ∈ braessAugmented.resources 0 := by decide
    have h1 : (0 : Fin 5) ∉ braessAugmented.resources 1 := by decide
    have h2 : (0 : Fin 5) ∈ braessAugmented.resources 2 := by decide
    simp only [h0, h1, h2, ↓reduceIte, add_zero]
  have he3 : braessAugmented.edgeFlow f 3 = f 1 + f 2 := by
    rw [edgeFlow, Finset.sum_filter, Fin.sum_univ_three]
    have h0 : (3 : Fin 5) ∉ braessAugmented.resources 0 := by decide
    have h1 : (3 : Fin 5) ∈ braessAugmented.resources 1 := by decide
    have h2 : (3 : Fin 5) ∈ braessAugmented.resources 2 := by decide
    simp only [h0, h1, h2, ↓reduceIte, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · change ∑ e ∈ ({0, 1} : Finset (Fin 5)),
        braessAugmented.latency e (braessAugmented.edgeFlow f e) = (f 0 + f 2) + 1
    rw [Finset.sum_pair (by decide), he0]
    rfl
  · change ∑ e ∈ ({2, 3} : Finset (Fin 5)),
        braessAugmented.latency e (braessAugmented.edgeFlow f e) = 1 + (f 1 + f 2)
    rw [Finset.sum_pair (by decide), he3]
    rfl
  · change ∑ e ∈ ({0, 4, 3} : Finset (Fin 5)),
        braessAugmented.latency e (braessAugmented.edgeFlow f e) = (f 0 + f 2) + (f 1 + f 2)
    rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide), he0, he3]
    change (f 0 + f 2) + (0 + (f 1 + f 2)) = (f 0 + f 2) + (f 1 + f 2)
    ring

/-- Cost formula for `braessAugmented`. -/
theorem braessAugmented_cost (f : Fin 3 → ℝ) :
    braessAugmented.cost f =
      f 0 * ((f 0 + f 2) + 1) + f 1 * (1 + (f 1 + f 2)) +
        f 2 * ((f 0 + f 2) + (f 1 + f 2)) := by
  obtain ⟨h0, h1, h2⟩ := braessAugmented_pathLatency f
  simp only [cost, Fin.sum_univ_three, h0, h1, h2]

/-- **Unique Wardrop equilibrium of the augmented Braess network** ([Roughgarden2007Routing],
Example 18.4): `f` is a Wardrop equilibrium of `braessAugmented` iff `f = ![0, 0, 1]`, with total
cost `2 = 4 / 3 * (3 / 2)` (whereas `![1 / 2, 1 / 2, 0]` is socially optimal of cost `3 / 2`). -/
theorem braessAugmented_isWardrop_iff {f : Fin 3 → ℝ} :
    braessAugmented.IsWardrop f ↔ f = ![0, 0, 1] := by
  obtain ⟨hl0, hl1, hl2⟩ := braessAugmented_pathLatency f
  constructor
  · intro hf
    have hsum : f 0 + f 1 + f 2 = 1 := by
      have h := hf.1.2 ()
      simpa [braessAugmented, Fin.sum_univ_three, add_assoc] using h
    have hf0 : 0 ≤ f 0 := hf.1.1 0
    have hf1 : 0 ≤ f 1 := hf.1.1 1
    have hf2 : 0 ≤ f 2 := hf.1.1 2
    have h0_eq : f 0 = 0 := by
      by_contra hne
      have hpos : 0 < f 0 := lt_of_le_of_ne hf0 (Ne.symm hne)
      have hle := hf.2 0 2 rfl hpos
      rw [hl0, hl2] at hle
      have hge1 : 1 ≤ f 1 + f 2 := by linarith
      linarith
    have h1_eq : f 1 = 0 := by
      by_contra hne
      have hpos : 0 < f 1 := lt_of_le_of_ne hf1 (Ne.symm hne)
      have hle := hf.2 1 2 rfl hpos
      rw [hl1, hl2] at hle
      linarith
    ext i
    fin_cases i
    · exact h0_eq
    · exact h1_eq
    · change f 2 = 1; linarith
  · rintro rfl
    refine ⟨⟨fun p => by fin_cases p <;> norm_num, fun _ => ?_⟩, fun p q _ _ => ?_⟩
    · simp [braessAugmented, Fin.sum_univ_three]
    · obtain ⟨h0', h1', h2'⟩ := braessAugmented_pathLatency ![0, 0, 1]
      norm_num at h0' h1' h2'
      have hall : ∀ r : Fin 3, braessAugmented.pathLatency ![0, 0, 1] r = 2 := by
        intro r
        fin_cases r
        · exact h0'
        · exact h1'
        · exact h2'
      rw [hall p, hall q]

/-- The even split `![1 / 2, 1 / 2, 0]` (avoiding the cross edge) is socially optimal in
`braessAugmented`, with total cost `3 / 2`. -/
theorem braessAugmented_isOptimal_half :
    braessAugmented.IsOptimal ![1 / 2, 1 / 2, 0] := by
  refine ⟨⟨fun p => by fin_cases p <;> norm_num, fun _ => ?_⟩, fun g hg => ?_⟩
  · simp only [braessAugmented_commodity, braessAugmented_rate, Finset.filter_true,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    norm_num
  · rw [braessAugmented_cost, braessAugmented_cost]
    have hsum : g 0 + g 1 + g 2 = 1 := by
      have h := hg.2 ()
      simpa only [braessAugmented_commodity, braessAugmented_rate, Finset.filter_true,
        Fin.sum_univ_three, add_assoc] using h
    have hg2 : 0 ≤ g 2 := hg.1 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    nlinarith [sq_nonneg (g 0 - g 1), sq_nonneg (g 2)]

/-- **Braess's paradox** ([Roughgarden2007Routing], Example 18.4 and Remark 18.22): adding the
zero-cost cross edge to the four-node Wheatstone network increases every Wardrop equilibrium's
cost by a factor of `4 / 3` (from `3 / 2` to `2`), attaining the worst-case affine bound
`HasAffineLatencies.cost_le_four_thirds_restrictPaths`. -/
theorem braess_paradox {f₁ : Fin 2 → ℝ} {f₂ : Fin 3 → ℝ}
    (hf₁ : braessInitial.IsWardrop f₁) (hf₂ : braessAugmented.IsWardrop f₂) :
    braessAugmented.cost f₂ = 4 / 3 * braessInitial.cost f₁ := by
  rw [braessInitial_isWardrop_iff.1 hf₁, braessAugmented_isWardrop_iff.1 hf₂,
    braessInitial_cost, braessAugmented_cost]
  norm_num

end BraessWheatstone

end NonatomicCongestionGame

end Cslib.GameTheory

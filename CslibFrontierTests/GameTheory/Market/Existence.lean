/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Market.Existence
public import CslibFrontier.GameTheory.Market.GaleNikaidoDebreu
public import CslibFrontier.GameTheory.Market.GrossSubstitutes
public import CslibFrontier.GameTheory.Market.Welfare
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for the Gale–Nikaido–Debreu lemma and competitive equilibrium existence

* `isFixedPt_priceRaisingMap_iff` characterization on `priceSimplex (Fin 2)`.
* Direct test of single-valued GND (`exists_excessDemand_le_zero_of_continuousOn`) on a smooth
  Walras-law excess demand field `z p = ![p 1 - p 0, p 0 - p 1]`.
* Direct test of set-valued GND (`exists_excessDemand_le_zero_of_upperHemicontinuousOn`).
* Concrete competitive equilibrium existence via `ExchangeMarket.exists_isCompetitiveEquilibrium` on
  a 2-trader, 2-good linear exchange market with strictly positive endowments.
* Asymmetric 2-trader, 2-good Cobb–Douglas exchange economy (`cd2x2`) proving equilibrium existence
  via `ExchangeMarket.exists_isCompetitiveEquilibrium` and verifying exact agreement with
  `Market/GrossSubstitutes.lean`'s `cobbDouglasDemand` and the normalized equilibrium price vector
  `![7 / 17, 10 / 17]`.
* Concrete strictly quasiconcave equilibrium existence via
  `ExchangeMarket.exists_isCompetitiveEquilibrium_of_strictQuasiconcaveOn` for utility
  `u(x) = (x 0 + 1) * (x 1 + 1)`.
* Boundary/zero-endowment counterexample showing that relaxing strict positivity of endowments
  (`∀ i g, 0 < E.endowment i g`) allows markets with no competitive equilibrium at all.
-/

public section

namespace CslibFrontierTests.GameTheory.Market.Existence

open Cslib.GameTheory.Market
open Finset Set

section GNDTests

theorem priceRaisingMap_fixed_test :
    let z : (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ => ![-1, -2]
    let p : Fin 2 → ℝ := ![1 / 2, 1 / 2]
    Function.IsFixedPt (priceRaisingMap z) p := by
  intro z p
  have hwalras : expenditure p (z p) ≤ 0 := by
    simp only [expenditure_eq_sum, Fin.sum_univ_two]
    norm_num [p, z]
  exact (isFixedPt_priceRaisingMap_iff hwalras).mpr fun g => by fin_cases g <;> norm_num [z]

theorem gnd_continuous_test :
    ∃ p ∈ priceSimplex (Fin 2), ∀ g, (![p 1 - p 0, p 0 - p 1] : Fin 2 → ℝ) g ≤ 0 := by
  let z : (Fin 2 → ℝ) → Fin 2 → ℝ := fun p => ![p 1 - p 0, p 0 - p 1]
  have hz_cont : ContinuousOn z (priceSimplex (Fin 2)) := by
    refine Continuous.continuousOn (continuous_pi fun g => ?_)
    fin_cases g
    · exact (continuous_apply 1).sub (continuous_apply 0)
    · exact (continuous_apply 0).sub (continuous_apply 1)
  have hz_walras : ∀ p ∈ priceSimplex (Fin 2), expenditure p (z p) ≤ 0 := by
    intro p _
    simp only [expenditure_eq_sum, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, z]
    nlinarith [sq_nonneg (p 0 - p 1)]
  exact exists_excessDemand_le_zero_of_continuousOn hz_cont hz_walras

theorem gnd_correspondence_test :
    ∃ p ∈ priceSimplex (Fin 2), ∃ z ∈ ({0} : Set (Fin 2 → ℝ)), ∀ g, z g ≤ 0 := by
  let Z : (Fin 2 → ℝ) → Set (Fin 2 → ℝ) := fun _ => {0}
  have hZ_uhc : UpperHemicontinuousOn Z (priceSimplex (Fin 2)) :=
    upperHemicontinuousOn_iff_forall_isOpen.mpr fun _ _ _ _ h =>
      Filter.Eventually.of_forall fun _ => h
  exact exists_excessDemand_le_zero_of_upperHemicontinuousOn (Z := Z)
    (fun _ _ => ⟨0, rfl⟩) (fun _ _ => isCompact_singleton) (fun _ _ => convex_singleton 0)
    hZ_uhc fun _ _ z hz => by rw [mem_singleton_iff.mp hz, expenditure_zero_right]

end GNDTests

section LinearMarketTest

/-- A 2-trader, 2-good linear exchange economy with strictly positive endowments. -/
def linearMarket2x2 : ExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 1], ![1, 2]]
  utility i := linearUtility (if i = 0 then ![1, 2] else ![2, 1])
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> norm_num

theorem linearMarket2x2_exists_equilibrium :
    ∃ x : Fin 2 → Fin 2 → ℝ, ∃ p ∈ priceSimplex (Fin 2),
      linearMarket2x2.IsCompetitiveEquilibrium x p := by
  refine linearMarket2x2.exists_isCompetitiveEquilibrium ?_ ?_ ?_ ?_
  · intro i g
    fin_cases i <;> fin_cases g <;> norm_num [linearMarket2x2]
  · intro i
    refine Continuous.continuousOn ?_
    change Continuous fun x : Fin 2 → ℝ =>
      linearUtility (if i = 0 then ![1, 2] else ![2, 1]) x
    simp_rw [linearUtility_eq_sum, Fin.sum_univ_two]
    exact (continuous_const.mul (continuous_apply 0)).add
      (continuous_const.mul (continuous_apply 1))
  · intro i
    exact hasConvexPreferences_linearUtility _
  · intro i
    dsimp [linearMarket2x2]
    rw [isLocallyNonsatiated_linearUtility_iff]
    fin_cases i
    · exact ⟨0, by norm_num⟩
    · exact ⟨0, by norm_num⟩

end LinearMarketTest

section CobbDouglasTest

/-- Asymmetric `2 × 2` Cobb–Douglas exchange economy matching `GrossSubstitutesTests.cobbDouglas2x2`
with endowments `![![2, 1], ![1, 2]]` and shares `![![1/2, 1/2], ![1/3, 2/3]]`. -/
noncomputable def cd2x2 : CobbDouglasExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 1], ![1, 2]]
  weight := ![![1 / 2, 1 / 2], ![1 / 3, 2 / 3]]
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> norm_num
  weight_nonneg i g := by fin_cases i <;> fin_cases g <;> norm_num
  sum_weight i := by
    fin_cases i <;>
      · simp only [Fin.sum_univ_two]
        norm_num

private lemma continuous_cobbDouglasUtility {α : Fin 2 → ℝ} (hα : ∀ g, 0 < α g) :
    Continuous (cobbDouglasUtility α) := by
  have hcoord : ∀ g, Continuous fun b : Fin 2 → ℝ => (b g) ^ (α g) := fun g =>
    (continuous_apply g).rpow_const fun _ => Or.inr (hα g).le
  have hEq : cobbDouglasUtility α = fun b => b 0 ^ α 0 * b 1 ^ α 1 := by
    ext b
    simp [cobbDouglasUtility_eq_prod, Fin.prod_univ_two]
  rw [hEq]
  exact (hcoord 0).mul (hcoord 1)

private lemma concaveOn_cobbDouglasUtility {α : Fin 2 → ℝ}
    (hα_pos : ∀ g, 0 < α g) (hα_sum : ∑ g : Fin 2, α g = 1) :
    ConcaveOn ℝ {b : Fin 2 → ℝ | ∀ g, 0 ≤ b g} (cobbDouglasUtility α) := by
  refine ⟨fun x hx y hy a c ha hc _ g => add_nonneg (mul_nonneg ha (hx g)) (mul_nonneg hc (hy g)),
    fun x hx y hy a c ha hc hac => ?_⟩
  let w : Fin 2 → ℝ := a • x + c • y
  have hw_nn : ∀ g, 0 ≤ w g := fun g => add_nonneg (mul_nonneg ha (hx g)) (mul_nonneg hc (hy g))
  have hα_nn : ∀ g, 0 ≤ α g := fun g => (hα_pos g).le
  by_cases hzero : ∃ g₀ : Fin 2, w g₀ = 0
  · obtain ⟨g₀, hg₀⟩ := hzero
    have hw_eq : a * x g₀ + c * y g₀ = 0 := hg₀
    have ha0 : a = 0 ∨ x g₀ = 0 :=
      mul_eq_zero.mp (by linarith [mul_nonneg ha (hx g₀), mul_nonneg hc (hy g₀)])
    have hc0 : c = 0 ∨ y g₀ = 0 :=
      mul_eq_zero.mp (by linarith [mul_nonneg ha (hx g₀), mul_nonneg hc (hy g₀)])
    have hM : a * cobbDouglasUtility α x = 0 := by
      rcases ha0 with rfl | hx0
      · simp
      · have hprod0 : cobbDouglasUtility α x = 0 := by
          rw [cobbDouglasUtility_eq_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ g₀)
            (by rw [hx0, Real.zero_rpow (hα_pos g₀).ne'])
        simp [hprod0]
    have hN : c * cobbDouglasUtility α y = 0 := by
      rcases hc0 with rfl | hy0
      · simp
      · have hprod0 : cobbDouglasUtility α y = 0 := by
          rw [cobbDouglasUtility_eq_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ g₀)
            (by rw [hy0, Real.zero_rpow (hα_pos g₀).ne'])
        simp [hprod0]
    simpa only [smul_eq_mul, hM, hN, add_zero] using cobbDouglasUtility_nonneg hw_nn (α := α)
  · push Not at hzero
    have hw_pos : ∀ g, 0 < w g := fun g => lt_of_le_of_ne (hw_nn g) (Ne.symm (hzero g))
    have hW_pos : 0 < cobbDouglasUtility α w := by
      rw [cobbDouglasUtility_eq_prod]
      exact Finset.prod_pos fun g _ => Real.rpow_pos_of_pos (hw_pos g) (α g)
    have hgm_x := Real.geom_mean_le_arith_mean_weighted Finset.univ α (fun g => x g / w g)
      (fun g _ => hα_nn g) hα_sum fun g _ => div_nonneg (hx g) (hw_pos g).le
    have hgm_y := Real.geom_mean_le_arith_mean_weighted Finset.univ α (fun g => y g / w g)
      (fun g _ => hα_nn g) hα_sum fun g _ => div_nonneg (hy g) (hw_pos g).le
    have hprod_x : ∏ g : Fin 2, (x g / w g) ^ α g =
        cobbDouglasUtility α x / cobbDouglasUtility α w := by
      simp only [cobbDouglasUtility_eq_prod, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun g _ => Real.div_rpow (hx g) (hw_pos g).le (α g)
    have hprod_y : ∏ g : Fin 2, (y g / w g) ^ α g =
        cobbDouglasUtility α y / cobbDouglasUtility α w := by
      simp only [cobbDouglasUtility_eq_prod, ← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun g _ => Real.div_rpow (hy g) (hw_pos g).le (α g)
    have hle_sum :
        a * (cobbDouglasUtility α x / cobbDouglasUtility α w) +
          c * (cobbDouglasUtility α y / cobbDouglasUtility α w) ≤ 1 := by
      have hax := mul_le_mul_of_nonneg_left (hprod_x ▸ hgm_x) ha
      have hcy := mul_le_mul_of_nonneg_left (hprod_y ▸ hgm_y) hc
      calc
        a * (cobbDouglasUtility α x / cobbDouglasUtility α w) +
            c * (cobbDouglasUtility α y / cobbDouglasUtility α w)
            ≤ a * ∑ g, α g * (x g / w g) + c * ∑ g, α g * (y g / w g) := add_le_add hax hcy
        _ = ∑ g, α g * ((a * x g + c * y g) / w g) := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun g _ => ?_
            ring
        _ = ∑ g, α g * 1 := Finset.sum_congr rfl fun g _ => by
            have hfrac : (a * x g + c * y g) / w g = 1 := by
              change w g / w g = 1
              exact div_self (hw_pos g).ne'
            rw [hfrac]
        _ = 1 := by simpa using hα_sum
    have hmul := (mul_le_mul_iff_left₀ hW_pos).mpr hle_sum
    have hdiv_eq :
        cobbDouglasUtility α w *
            (a * (cobbDouglasUtility α x / cobbDouglasUtility α w) +
              c * (cobbDouglasUtility α y / cobbDouglasUtility α w)) =
          a * cobbDouglasUtility α x + c * cobbDouglasUtility α y := by
      field_simp [hW_pos.ne']
    rw [mul_comm _ (cobbDouglasUtility α w), hdiv_eq, one_mul] at hmul
    simpa only [smul_eq_mul] using hmul

private lemma locallyNonsatiated_cobbDouglasUtility {α : Fin 2 → ℝ} (hα : ∀ g, 0 < α g) :
    IsLocallyNonsatiated (cobbDouglasUtility α) := by
  intro b hb ε hε
  let b' : Fin 2 → ℝ := fun g => b g + ε / 2
  have hb'_nn : ∀ g, 0 ≤ b' g := fun g => by dsimp [b']; linarith [hb g]
  have hlt_coord : ∀ g, b g ^ α g < b' g ^ α g := fun g =>
    Real.rpow_lt_rpow (hb g) (by dsimp [b']; linarith) (hα g)
  have hlt_prod : cobbDouglasUtility α b < cobbDouglasUtility α b' := by
    simp only [cobbDouglasUtility_eq_prod, Fin.prod_univ_two]
    exact mul_lt_mul' (hlt_coord 0).le (hlt_coord 1) (Real.rpow_nonneg (hb 1) _)
      (Real.rpow_pos_of_pos (by dsimp [b']; linarith [hb 0]) _)
  refine ⟨b', hb'_nn, fun g => ?_, hlt_prod⟩
  dsimp [b']
  rw [add_sub_cancel_left, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

theorem cd2x2_exists_equilibrium_and_matches_cobbDouglasDemand :
    ∃ x : Fin 2 → Fin 2 → ℝ, ∃ p ∈ priceSimplex (Fin 2),
      cd2x2.toExchangeMarket.IsCompetitiveEquilibrium x p ∧
      p = ![7 / 17, 10 / 17] ∧
      (∀ i, x i = cobbDouglasDemand (cd2x2.weight i) p (cd2x2.toExchangeMarket.income p i)) ∧
      x 0 = ![12 / 7, 6 / 5] ∧ x 1 = ![9 / 7, 9 / 5] := by
  have hw_pos : ∀ i g : Fin 2, 0 < cd2x2.weight i g := fun i g => by
    fin_cases i <;> fin_cases g <;> norm_num [cd2x2]
  obtain ⟨x, p, hp, heq⟩ := cd2x2.toExchangeMarket.exists_isCompetitiveEquilibrium
    (fun i g => by
      rw [cd2x2.toExchangeMarket_endowment]
      fin_cases i <;> fin_cases g <;> norm_num [cd2x2])
    (fun i => by
      rw [cd2x2.toExchangeMarket_utility]
      exact (continuous_cobbDouglasUtility (hw_pos i)).continuousOn)
    (fun i => by
      rw [cd2x2.toExchangeMarket_utility]
      exact HasConvexPreferences.of_concaveOn
        (concaveOn_cobbDouglasUtility (hw_pos i) (cd2x2.sum_weight i)))
    (fun i => by
      rw [cd2x2.toExchangeMarket_utility]
      exact locallyNonsatiated_cobbDouglasUtility (hw_pos i))
  have hp_pos : ∀ g : Fin 2, 0 < p g := by
    intro g
    refine lt_of_le_of_ne (hp.1 g) fun hg0 => ?_
    have hdem0 := Cslib.GameTheory.Market.mem_demandSet.mp
      (cd2x2.toExchangeMarket.mem_demandSet.mp (heq.2.1 0))
    let g₁ : Fin 2 := if g = 0 then 1 else 0
    have hsum_p := hp.2
    rw [Fin.sum_univ_two] at hsum_p
    have hpg₁ : p g₁ = 1 := by
      by_cases hg : g = 0
      · subst hg
        dsimp [g₁]
        linarith [hg0]
      · have hg1 : g = 1 := by omega
        subst hg1
        dsimp [g₁]
        linarith [hg0]
    have hinc0_pos : 0 < cd2x2.toExchangeMarket.income p 0 := by
      rw [cd2x2.toExchangeMarket.income_eq, expenditure_eq_sum, Fin.sum_univ_two,
        cd2x2.toExchangeMarket_endowment]
      by_cases hg : g = 0
      · subst hg
        dsimp [g₁] at hpg₁
        dsimp [cd2x2]
        nlinarith [hp.1 0, hp.1 1]
      · have hg1 : g = 1 := by omega
        subst hg1
        dsimp [g₁] at hpg₁
        dsimp [cd2x2]
        nlinarith [hp.1 0, hp.1 1]
    let M : ℝ := cd2x2.toExchangeMarket.income p 0
    let M₁ : ℝ := cd2x2.toExchangeMarket.utility 0 (x 0)
    let K : ℝ := (M₁ + 1) ^ 2 / M + 1
    let b' : Fin 2 → ℝ := fun k => if k = g then K else M
    have hK_pos : 0 < K := by positivity
    have hM_pos : 0 < M := hinc0_pos
    have hb'_nn : ∀ k, 0 ≤ b' k := fun k => by
      dsimp [b']
      split_ifs <;> linarith
    have hb'_exp : expenditure p b' = M := by
      rw [expenditure_eq_sum, Fin.sum_univ_two]
      by_cases hg : g = 0
      · subst hg
        dsimp [b', g₁, M] at hpg₁ ⊢
        simp only [Fin.isValue, ← hg0, hpg₁, zero_mul, zero_add, one_mul]
      · have hg1 : g = 1 := by omega
        subst hg1
        dsimp [b', g₁, M] at hpg₁ ⊢
        simp only [Fin.isValue, ← hg0, hpg₁, one_mul, zero_mul, add_zero]
    have hutil_lt : M₁ < cd2x2.toExchangeMarket.utility 0 b' := by
      have hM₁_nn : 0 ≤ M₁ := by
        change 0 ≤ cd2x2.toExchangeMarket.utility 0 (x 0)
        rw [cd2x2.toExchangeMarket_utility]
        exact cobbDouglasUtility_nonneg hdem0.1.1
      have h01 : cd2x2.toExchangeMarket.utility 0 b' = Real.sqrt (K * M) := by
        have hsqrt : ∀ t : ℝ, t ^ (1 / 2 : ℝ) = Real.sqrt t := fun t => (Real.sqrt_eq_rpow t).symm
        rw [cd2x2.toExchangeMarket_utility, Real.sqrt_mul hK_pos.le M]
        by_cases hg : g = 0
        · subst hg
          simp only [cd2x2, cobbDouglasUtility_eq_prod, Fin.prod_univ_two,
            Matrix.cons_val_zero, Matrix.cons_val_one, b']
          norm_num
          rw [hsqrt, hsqrt]
        · have hg1 : g = 1 := by omega
          subst hg1
          simp only [cd2x2, cobbDouglasUtility_eq_prod, Fin.prod_univ_two,
            Matrix.cons_val_zero, Matrix.cons_val_one, b']
          norm_num
          rw [hsqrt, hsqrt, mul_comm]
      have hKM : K * M = (M₁ + 1) ^ 2 + M := by
        dsimp [K]
        field_simp [hM_pos.ne']
      rw [h01]
      exact Real.lt_sqrt_of_sq_lt (by nlinarith)
    linarith [hdem0.2 b' ⟨hb'_nn, hb'_exp.le⟩]
  have hx_cd :
      ∀ i, x i = cobbDouglasDemand (cd2x2.weight i) p (cd2x2.toExchangeMarket.income p i) := by
    intro i
    have hmem : x i ∈ demandSet (cobbDouglasUtility (cd2x2.weight i)) p
        (cd2x2.toExchangeMarket.income p i) := by
      rw [← cd2x2.toExchangeMarket_utility]
      exact cd2x2.toExchangeMarket.mem_demandSet.mp (heq.2.1 i)
    rw [demandSet_cobbDouglasUtility_eq (hw_pos i) (cd2x2.sum_weight i) hp_pos
      (cd2x2.toExchangeMarket.income_nonneg hp.1 i)] at hmem
    exact mem_singleton_iff.mp hmem
  have hclear0 : x 0 0 + x 1 0 = 3 := by
    have hsum := heq.sum_eq_totalSupply_of_price_pos (hp_pos 0)
    rw [Fin.sum_univ_two, cd2x2.toExchangeMarket.totalSupply_eq_sum, Fin.sum_univ_two,
      cd2x2.toExchangeMarket_endowment] at hsum
    dsimp [cd2x2] at hsum
    norm_num at hsum
    exact hsum
  have hlin0 : 3 * (2 * p 0 + p 1) + 2 * (p 0 + 2 * p 1) = 18 * p 0 := by
    have h0 := congrFun (hx_cd 0) 0
    have h1 := congrFun (hx_cd 1) 0
    simp only [cobbDouglasDemand_apply, cd2x2.toExchangeMarket.income_eq,
      expenditure_eq_sum, Fin.sum_univ_two, cd2x2.toExchangeMarket_endowment] at h0 h1
    dsimp [cd2x2] at h0 h1
    norm_num at h0 h1
    have hp0_ne : p 0 ≠ 0 := (hp_pos 0).ne'
    have hsum_eq : (1 / 2 * (p 0 * 2 + p 1) / p 0) +
        (1 / 3 * (p 0 + p 1 * 2) / p 0) = 3 := by
      linarith
    field_simp [hp0_ne] at hsum_eq
    linarith
  have hp_eq : p = ![7 / 17, 10 / 17] := by
    have hsum_p := hp.2
    rw [Fin.sum_univ_two] at hsum_p
    ext g
    by_cases hg : g = 0
    · subst hg
      simp only [Matrix.cons_val_zero]
      linarith
    · have hg1 : g = 1 := by omega
      subst hg1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
  have hx0_eq : x 0 = ![12 / 7, 6 / 5] := by
    ext g
    have h0 := congrFun (hx_cd 0) g
    simp only [cobbDouglasDemand_apply, cd2x2.toExchangeMarket.income_eq, expenditure_eq_sum,
      Fin.sum_univ_two, cd2x2.toExchangeMarket_endowment, hp_eq] at h0
    by_cases hg : g = 0
    · subst hg
      simp only [cd2x2, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h0 ⊢
      norm_num at h0
      exact h0
    · have hg1 : g = 1 := by omega
      subst hg1
      simp only [cd2x2, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h0 ⊢
      norm_num at h0
      exact h0
  have hx1_eq : x 1 = ![9 / 7, 9 / 5] := by
    ext g
    have h1 := congrFun (hx_cd 1) g
    simp only [cobbDouglasDemand_apply, cd2x2.toExchangeMarket.income_eq, expenditure_eq_sum,
      Fin.sum_univ_two, cd2x2.toExchangeMarket_endowment, hp_eq] at h1
    by_cases hg : g = 0
    · subst hg
      simp only [cd2x2, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h1 ⊢
      norm_num at h1
      exact h1
    · have hg1 : g = 1 := by omega
      subst hg1
      simp only [cd2x2, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h1 ⊢
      norm_num at h1
      exact h1
  exact ⟨x, p, hp, heq, hp_eq, hx_cd, hx0_eq, hx1_eq⟩

end CobbDouglasTest

section StrictQuasiconcaveTest

/-- A 2-trader, 2-good exchange economy with smooth strictly quasiconcave utilities
`u(x) = (x 0 + 1) * (x 1 + 1)`. -/
def shiftedProductMarket2x2 : ExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![2, 1], ![1, 2]]
  utility _ x := (x 0 + 1) * (x 1 + 1)
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> norm_num

private lemma shiftedProduct_strictQuasiconcave {x y : Fin 2 → ℝ}
    (hx : ∀ g, 0 ≤ x g) (hy : ∀ g, 0 ≤ y g) (hne : x ≠ y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) <
      ((a • x + b • y) 0 + 1) * ((a • x + b • y) 1 + 1) := by
  have hx0 : 0 < x 0 + 1 := by linarith [hx 0]
  have hx1 : 0 < x 1 + 1 := by linarith [hx 1]
  have hy0 : 0 < y 0 + 1 := by linarith [hy 0]
  have hy1 : 0 < y 1 + 1 := by linarith [hy 1]
  have hz0_pos : 0 < (a • x + b • y) 0 + 1 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx 0, hy 0]
  have hz1_pos : 0 < (a • x + b • y) 1 + 1 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx 1, hy 1]
  have hmid :
      ((a • x + b • y) 0 + 1) * ((a • x + b • y) 1 + 1) =
        a * ((x 0 + 1) * (x 1 + 1)) + b * ((y 0 + 1) * (y 1 + 1)) -
          a * b * (y 0 - x 0) * (y 1 - x 1) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (a * x 0 + b * y 0 + 1) * (a * x 1 + b * y 1 + 1)
          = (a * (x 0 + 1) + b * (y 0 + 1)) * (a * (x 1 + 1) + b * (y 1 + 1)) := by
              rw [show a * x 0 + b * y 0 + 1 = a * (x 0 + 1) + b * (y 0 + 1) by
                calc a * x 0 + b * y 0 + 1 = a * x 0 + b * y 0 + (a + b) := by rw [hab]
                _ = a * (x 0 + 1) + b * (y 0 + 1) := by ring]
              rw [show a * x 1 + b * y 1 + 1 = a * (x 1 + 1) + b * (y 1 + 1) by
                calc a * x 1 + b * y 1 + 1 = a * x 1 + b * y 1 + (a + b) := by rw [hab]
                _ = a * (x 1 + 1) + b * (y 1 + 1) := by ring]
      _ = (a ^ 2 + a * b) * ((x 0 + 1) * (x 1 + 1)) +
            (b ^ 2 + a * b) * ((y 0 + 1) * (y 1 + 1)) -
            a * b * (y 0 - x 0) * (y 1 - x 1) := by ring
      _ = a * ((x 0 + 1) * (x 1 + 1)) + b * ((y 0 + 1) * (y 1 + 1)) -
            a * b * (y 0 - x 0) * (y 1 - x 1) := by
              rw [show a ^ 2 + a * b = a * (a + b) by ring,
                show b ^ 2 + a * b = b * (a + b) by ring, hab, mul_one, mul_one]
  have hmin_le : min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) ≤
      a * ((x 0 + 1) * (x 1 + 1)) + b * ((y 0 + 1) * (y 1 + 1)) := by
    have hm1 : a * min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) ≤
        a * ((x 0 + 1) * (x 1 + 1)) := mul_le_mul_of_nonneg_left (min_le_left _ _) ha.le
    have hm2 : b * min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) ≤
        b * ((y 0 + 1) * (y 1 + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hb.le
    have hsum : (a + b) * min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) =
        min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) := by rw [hab, one_mul]
    linarith
  have hdiff_ne : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
    by_contra! h
    apply hne
    ext g
    fin_cases g
    · exact h.1
    · exact h.2
  rcases le_or_gt (x 0) (y 0) with hx0y | hy0x <;> rcases le_or_gt (x 1) (y 1) with hx1y | hy1x
  · have hstrict : x 0 < y 0 ∨ x 1 < y 1 := by
      rcases hx0y.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ((hx1y.lt_or_eq).resolve_right fun h1 => hdiff_ne.elim (fun h0 => h0 h)
          (fun h1' => h1' h1))
    have hux_lt_uy : (x 0 + 1) * (x 1 + 1) < (y 0 + 1) * (y 1 + 1) := by
      rcases hstrict with h0 | h1
      · nlinarith
      · nlinarith
    have hz0 : x 0 < (a • x + b • y) 0 ∨ x 1 < (a • x + b • y) 1 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases hstrict with h0 | h1
      · exact Or.inl (by nlinarith)
      · exact Or.inr (by nlinarith)
    have hz0_ge : x 0 ≤ (a • x + b • y) 0 := by simp [Pi.add_apply, Pi.smul_apply]; nlinarith
    have hz1_ge : x 1 ≤ (a • x + b • y) 1 := by simp [Pi.add_apply, Pi.smul_apply]; nlinarith
    rw [min_eq_left hux_lt_uy.le]
    rcases hz0 with h0 | h1
    · nlinarith
    · nlinarith
  · rcases hx0y.lt_or_eq with h0 | h0
    · have hprod : a * b * (y 0 - x 0) * (y 1 - x 1) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos (mul_pos ha hb) (sub_pos.mpr h0)) (sub_neg.mpr hy1x)
      linarith
    · rw [h0] at hx0
      have hz1 : y 1 < (a • x + b • y) 1 := by simp [Pi.add_apply, Pi.smul_apply]; nlinarith
      have hmin_eq : min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) = (y 0 + 1) * (y 1 + 1) :=
        min_eq_right (by rw [h0]; exact mul_le_mul_of_nonneg_left (by linarith) hy0.le)
      rw [hmin_eq]
      have hz0_eq : (a • x + b • y) 0 = y 0 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0]
        calc a * y 0 + b * y 0 = (a + b) * y 0 := by ring
        _ = y 0 := by rw [hab, one_mul]
      rw [hz0_eq]
      exact mul_lt_mul_of_pos_left (by linarith) hy0
  · rcases hx1y.lt_or_eq with h1 | h1
    · have hprod : a * b * (y 0 - x 0) * (y 1 - x 1) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos ha hb) (sub_neg.mpr hy0x))
          (sub_pos.mpr h1)
      linarith
    · have hz0 : y 0 < (a • x + b • y) 0 := by simp [Pi.add_apply, Pi.smul_apply]; nlinarith
      have hmin_eq : min ((x 0 + 1) * (x 1 + 1)) ((y 0 + 1) * (y 1 + 1)) = (y 0 + 1) * (y 1 + 1) :=
        min_eq_right (by rw [h1]; exact mul_le_mul_of_nonneg_right (by linarith) hy1.le)
      rw [hmin_eq]
      have hz1_eq : (a • x + b • y) 1 = y 1 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1]
        calc a * y 1 + b * y 1 = (a + b) * y 1 := by ring
        _ = y 1 := by rw [hab, one_mul]
      rw [hz1_eq]
      exact mul_lt_mul_of_pos_right (by linarith) hy1
  · have hux_gt_uy : (y 0 + 1) * (y 1 + 1) < (x 0 + 1) * (x 1 + 1) := by nlinarith
    have hz0 : y 0 < (a • x + b • y) 0 := by simp [Pi.add_apply, Pi.smul_apply]; nlinarith
    have hz1 : y 1 < (a • x + b • y) 1 := by simp [Pi.add_apply, Pi.smul_apply]; nlinarith
    rw [min_eq_right hux_gt_uy.le]
    nlinarith

theorem shiftedProductMarket2x2_exists_equilibrium :
    ∃ x : Fin 2 → Fin 2 → ℝ, ∃ p ∈ priceSimplex (Fin 2),
      shiftedProductMarket2x2.IsCompetitiveEquilibrium x p := by
  refine shiftedProductMarket2x2.exists_isCompetitiveEquilibrium_of_strictQuasiconcaveOn
    ?_ ?_ ?_ ?_
  · intro i g
    fin_cases i <;> fin_cases g <;> norm_num [shiftedProductMarket2x2]
  · intro _
    exact Continuous.continuousOn
      (((continuous_apply 0).add continuous_const).mul ((continuous_apply 1).add continuous_const))
  · intro _ x y hx hy hne a b ha hb hab
    exact shiftedProduct_strictQuasiconcave hx hy hne ha hb hab
  · intro _ b hb ε hε
    let b' : Fin 2 → ℝ := fun g => if g = 0 then b 0 + ε / 2 else b 1
    refine ⟨b', fun g => ?_, fun g => ?_, ?_⟩
    · fin_cases g
      · dsimp [b']
        linarith [hb 0]
      · exact hb 1
    · fin_cases g
      · dsimp [b']
        rw [add_sub_cancel_left, abs_of_pos (half_pos hε)]
        exact half_lt_self hε
      · dsimp [b']
        rw [sub_self, abs_zero]
        exact hε
    · dsimp [shiftedProductMarket2x2, b']
      have h0 : 0 < ε / 2 := half_pos hε
      have h1 : 0 < b 1 + 1 := by linarith [hb 1]
      nlinarith

end StrictQuasiconcaveTest

section ZeroEndowmentCounterexample

/-- Exchange economy where good `1` has zero total endowment (`endowment = ![![1, 0], ![1, 0]]`),
trader `0` desires only good `0`, and trader `1` desires only good `1`. No competitive equilibrium
exists at any nonnegative price vector. -/
def zeroEndowmentMarket : ExchangeMarket (Fin 2) (Fin 2) where
  endowment := ![![1, 0], ![1, 0]]
  utility i x := if i = 0 then x 0 else x 1
  endowment_nonneg i g := by fin_cases i <;> fin_cases g <;> norm_num

theorem no_competitiveEquilibrium_zeroEndowmentMarket :
    ¬ ∃ x : Fin 2 → Fin 2 → ℝ, ∃ p : Fin 2 → ℝ,
      zeroEndowmentMarket.IsCompetitiveEquilibrium x p := by
  rintro ⟨x, p, hp, hdem, hclear, _⟩
  have hdem0 := Cslib.GameTheory.Market.mem_demandSet.mp
    (zeroEndowmentMarket.mem_demandSet.mp (hdem 0))
  have hdem1 := Cslib.GameTheory.Market.mem_demandSet.mp
    (zeroEndowmentMarket.mem_demandSet.mp (hdem 1))
  by_cases hp0 : p 0 = 0
  · let b' : Fin 2 → ℝ := fun g => if g = 0 then x 0 0 + 1 else x 0 1
    have hfeas : zeroEndowmentMarket.IsBudgetFeasible p 0 b' := by
      refine ⟨fun g => ?_, ?_⟩
      · fin_cases g
        · dsimp [b']
          linarith [hdem0.1.1 0]
        · exact hdem0.1.1 1
      · calc
          expenditure p b' = p 0 * (x 0 0 + 1) + p 1 * x 0 1 := by
              simp [expenditure_eq_sum, Fin.sum_univ_two, b']
          _ = p 0 * x 0 0 + p 1 * x 0 1 := by simp [hp0]
          _ = expenditure p (x 0) := by simp [expenditure_eq_sum, Fin.sum_univ_two]
          _ ≤ zeroEndowmentMarket.income p 0 := hdem0.1.2
    have hutil := hdem0.2 b' hfeas
    dsimp [zeroEndowmentMarket, b'] at hutil
    linarith
  · by_cases hp1 : p 1 = 0
    · let b' : Fin 2 → ℝ := fun g => if g = 1 then x 1 1 + 1 else x 1 0
      have hfeas : zeroEndowmentMarket.IsBudgetFeasible p 1 b' := by
        refine ⟨fun g => ?_, ?_⟩
        · fin_cases g
          · exact hdem1.1.1 0
          · dsimp [b']
            linarith [hdem1.1.1 1]
        · calc
            expenditure p b' = p 0 * x 1 0 + p 1 * (x 1 1 + 1) := by
                simp [expenditure_eq_sum, Fin.sum_univ_two, b']
            _ = p 0 * x 1 0 + p 1 * x 1 1 := by simp [hp1]
            _ = expenditure p (x 1) := by simp [expenditure_eq_sum, Fin.sum_univ_two]
            _ ≤ zeroEndowmentMarket.income p 1 := hdem1.1.2
      have hutil := hdem1.2 b' hfeas
      dsimp [zeroEndowmentMarket, b'] at hutil
      linarith
    · have hp0_pos : 0 < p 0 := lt_of_le_of_ne (hp 0) (Ne.symm hp0)
      have hp1_pos : 0 < p 1 := lt_of_le_of_ne (hp 1) (Ne.symm hp1)
      let b' : Fin 2 → ℝ := fun g => if g = 1 then p 0 / p 1 else 0
      have hinc1 : zeroEndowmentMarket.income p 1 = p 0 := by
        rw [zeroEndowmentMarket.income_eq, expenditure_eq_sum, Fin.sum_univ_two]
        simp [zeroEndowmentMarket]
      have hfeas : zeroEndowmentMarket.IsBudgetFeasible p 1 b' := by
        refine ⟨fun g => ?_, ?_⟩
        · fin_cases g
          · simp [b']
          · dsimp [b']
            positivity
        · rw [hinc1, expenditure_eq_sum, Fin.sum_univ_two]
          simp [b', mul_div_cancel₀ _ hp1_pos.ne']
      have hutil := hdem1.2 b' hfeas
      dsimp [zeroEndowmentMarket, b'] at hutil
      have hsupply1 : zeroEndowmentMarket.totalSupply 1 = 0 := by
        rw [zeroEndowmentMarket.totalSupply_eq_sum, Fin.sum_univ_two]
        norm_num [zeroEndowmentMarket]
      have hex1 := hclear 1
      rw [zeroEndowmentMarket.excessDemand_eq, Fin.sum_univ_two, hsupply1, sub_zero] at hex1
      have hpos : 0 < p 0 / p 1 := div_pos hp0_pos hp1_pos
      linarith [hdem0.1.1 1]

end ZeroEndowmentCounterexample

end CslibFrontierTests.GameTheory.Market.Existence

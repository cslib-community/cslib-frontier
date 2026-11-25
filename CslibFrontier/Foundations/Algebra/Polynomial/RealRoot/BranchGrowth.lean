/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, asymptotics of polynomial roots)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Polynomial.Basic

/-!
# Growth of divergent algebraic branches

Consider a real bivariate polynomial whose outer variable is the parameter and whose inner
variable is the branch value. If its degree in the branch value is at most `D`, a divergent
root at parameter `v ^ (D + 1)` eventually exceeds `v`. Reversing the polynomial in the
parameter makes its lower parameter coefficients negligible on the part of a branch below
that comparison scale, contradicting nonvanishing of its leading parameter coefficient.

Adapted from `PolynomialGrowthLimits`, `AlgebraicBranchGrowth`, and
`AlgebraicPowerScaleTest` in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Asymptotics Filter
open scoped Topology

variable {ι : Type*} {l : Filter ι}

private theorem eval_div_pow_tendsto_zero (q : Polynomial ℝ) {D k : ℕ}
    (hD : q.natDegree ≤ D) (hk : D < k) {v t : ι → ℝ}
    (hv : Tendsto v l atTop) (ht : Tendsto t l atTop)
    (hbound : ∀ᶠ x in l, 0 ≤ t x ∧ t x ≤ v x) :
    Tendsto (fun x => q.eval (t x) / v x ^ k) l (𝓝 0) := by
  have htv : t =O[l] v := IsBigO.of_bound' (hbound.mono fun x hx => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1, abs_of_nonneg (hx.1.trans hx.2)] using hx.2)
  have hq : q.eval =O[atTop] (fun x : ℝ => x ^ D) := by
    have hd : q.degree ≤ (X ^ D : Polynomial ℝ).degree := by
      rw [degree_X_pow]
      exact degree_le_of_natDegree_le hD
    simpa only [eval_pow, eval_X] using q.isBigO_atTop_of_degree_le _ hd
  have hqv : (fun x => q.eval (t x)) =O[l] (fun x => v x ^ D) :=
    (hq.comp_tendsto ht).trans (htv.pow D)
  have hsmall := (isLittleO_pow_pow_atTop_of_lt hk).comp_tendsto hv
  exact (hqv.trans_isLittleO hsmall).tendsto_div_nhds_zero

private theorem not_tendsto_eval_zero [NeBot l] (q : Polynomial ℝ) (hq : q ≠ 0)
    {t : ι → ℝ} (ht : Tendsto t l atTop) :
    ¬Tendsto (fun x => q.eval (t x)) l (𝓝 0) := by
  intro hz
  by_cases hd : 0 < q.degree
  · exact not_tendsto_nhds_of_tendsto_atTop ((q.abs_tendsto_atTop hd).comp ht) 0
      (by simpa only [abs_zero, Function.comp_def] using hz.abs)
  · have hC : q = C (q.coeff 0) := eq_C_of_degree_le_zero (le_of_not_gt hd)
    rw [hC] at hz
    have hc : q.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds
      (by simpa only [eval_C] using hz)
    exact hq (hC.trans (by rw [hc, C_0]))

/-- A divergent branch of roots at parameter `v ^ (D + 1)` eventually exceeds `v`.
The degree in the branch value is bounded by `D` in every parameter coefficient. -/
theorem eventually_lt_of_eval₂_pow_eq_zero (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    {D : ℕ} (hdegree : ∀ j, (P.coeff j).natDegree ≤ D)
    {v t : ι → ℝ} (hv : Tendsto v l atTop) (ht : Tendsto t l atTop)
    (hroot : ∀ᶠ x in l, P.eval₂ (evalRingHom (t x)) (v x ^ (D + 1)) = 0) :
    ∀ᶠ x in l, v x < t x := by
  by_contra hn
  have hfreq : ∃ᶠ x in l, t x ≤ v x :=
    (not_eventually.mp hn).mono fun _ hx => le_of_not_gt hx
  let l' := l ⊓ 𝓟 {x | t x ≤ v x}
  let : NeBot l' := frequently_iff_neBot.mp hfreq
  have hv' : Tendsto v l' atTop := hv.mono_left inf_le_left
  have ht' : Tendsto t l' atTop := ht.mono_left inf_le_left
  have hsmall : ∀ᶠ x in l', t x ≤ v x :=
    (eventually_principal.mpr fun _ hx => hx).filter_mono inf_le_right
  have hbound : ∀ᶠ x in l', 0 ≤ t x ∧ t x ≤ v x :=
    (ht'.eventually_ge_atTop 0).and hsmall
  let term (j : ℕ) (x : ι) := (P.reverse.coeff (j + 1)).eval (t x) *
    ((v x ^ (D + 1))⁻¹) ^ (j + 1)
  have hterm (j : ℕ) : Tendsto (term j) l' (𝓝 (0 : ℝ)) := by
    have hd : (P.reverse.coeff (j + 1)).natDegree ≤ D := by
      rw [coeff_reverse]
      exact hdegree _
    have hk : D < (D + 1) * (j + 1) := by
      calc
        D < D + 1 := Nat.lt_succ_self _
        _ = (D + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (D + 1) * (j + 1) := Nat.mul_le_mul_left _ (Nat.succ_pos _)
    simpa only [term, div_eq_mul_inv, pow_mul, inv_pow] using
      eval_div_pow_tendsto_zero _ hd hk hv' ht' hbound
  let S (x : ι) := ∑ j ∈ Finset.range P.natDegree, term j x
  have hS : Tendsto S l' (𝓝 (0 : ℝ)) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (Finset.range P.natDegree) (fun j _ => hterm j)
  have hform (x : ι) : P.reverse.eval₂ (evalRingHom (t x)) ((v x ^ (D + 1))⁻¹) =
      S x + P.leadingCoeff.eval (t x) := by
    rw [eval₂_eq_sum_range' _ (Nat.lt_succ_of_le P.reverse_natDegree_le) _,
      Finset.sum_range_succ']
    simp only [coeff_zero_reverse, pow_zero, mul_one, coe_evalRingHom]
    rfl
  have hlead : Tendsto (fun x => P.leadingCoeff.eval (t x)) l' (𝓝 (0 : ℝ)) := by
    have hneg : Tendsto (fun x => -S x) l' (𝓝 (0 : ℝ)) :=
      by simpa only [neg_zero] using hS.neg
    apply hneg.congr'
    filter_upwards [hroot.filter_mono (show l' ≤ l from inf_le_left),
      hv'.eventually_gt_atTop (0 : ℝ)] with x hx hvx
    let := invertibleOfNonzero (pow_ne_zero (D + 1) hvx.ne')
    have hr : P.reverse.eval₂ (evalRingHom (t x)) ((v x ^ (D + 1))⁻¹) = 0 := by
      simpa only [invOf_eq_inv] using
        (eval₂_reverse_eq_zero_iff (evalRingHom (t x)) (v x ^ (D + 1)) P).mpr hx
    rw [hform] at hr
    exact (eq_neg_of_add_eq_zero_right hr).symm
  exact not_tendsto_eval_zero _ (leadingCoeff_ne_zero.mpr hP) ht' hlead

end Polynomial

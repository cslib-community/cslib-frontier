/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Conditional Uniform Distributions on Finite Subsets and Rejection Resampling

This module proves finite-subset uniformity and density-bound lemmas for `PMF.uniformOfFinset` and
`PMF.uniformOfFintype`:

* `Cslib.Probability.PMF.unifOn_rehash_eq`: starting from a uniform draw on `E_prev`, keeping the
  sample when it lies in `E_curr ⊆ E_prev` and rejection-sampling uniformly from `E_curr` on
  `E_prev \ E_curr` yields the exact uniform distribution `PMF.uniformOfFinset E_curr`.
* `Cslib.Probability.PMF.uniformOfFinset_le_two_mul_uniformOfFintype`: when `|Θ| ≤ 2 * |E|`, the
  conditional uniform distribution on `E` is pointwise bounded by `2 * PMF.uniformOfFintype Θ`.
* `Cslib.Probability.PMF.card_le_two_mul_card_of_uniformOfFintype_compl_le_half`: if `{θ | θ ∉ E}`
  has uniform probability mass at most `1 / 2`, then `|Θ| ≤ 2 * |E|` and `E` is nonempty.
* `Cslib.Probability.PMF.pmf_eq_uniformOfFinset_of_ite_const`: any `PMF Θ` taking a constant value
  on a nonempty finset `E` and `0` outside `E` equals `PMF.uniformOfFinset E`.
-/

public section

namespace Cslib.Probability.PMF

open scoped BigOperators ENNReal

/-- **Conditional-uniform subset resampling identity**:
If `E_curr ⊆ E_prev` are nonempty finite sets, then starting from a sample drawn uniformly from
`E_prev`, keeping the sample when it lies in `E_curr` and rejection-sampling uniformly from `E_curr`
when it lies in `E_prev \ E_curr` produces the exact uniform distribution on `E_curr`:
`1 / |E_prev| + ((|E_prev| - |E_curr|) / |E_prev|) * (1 / |E_curr|) = 1 / |E_curr|`. -/
theorem unifOn_rehash_eq {Θ : Type*} [DecidableEq Θ] {E_prev E_curr : Finset Θ}
    (hsub : E_curr ⊆ E_prev) (hprev : E_prev.Nonempty) (hcurr : E_curr.Nonempty) :
    (PMF.uniformOfFinset E_prev hprev).bind
      (fun θ => if θ ∈ E_curr then PMF.pure θ else PMF.uniformOfFinset E_curr hcurr) =
      PMF.uniformOfFinset E_curr hcurr := by
  ext θ'
  have hP : (E_prev.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hprev.card_ne_zero
  have hC : (E_curr.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hcurr.card_ne_zero
  rw [PMF.bind_apply, tsum_eq_sum (s := E_prev), ← Finset.sum_sdiff hsub]
  · calc
      _ = (∑ _x ∈ E_prev \ E_curr,
            (E_prev.card : ℝ≥0∞)⁻¹ * PMF.uniformOfFinset E_curr hcurr θ') +
          ∑ x ∈ E_curr, (E_prev.card : ℝ≥0∞)⁻¹ * PMF.pure x θ' := by
        congr 1 <;> refine Finset.sum_congr rfl fun x hx => ?_
        · rw [Finset.mem_sdiff] at hx
          simp only [PMF.uniformOfFinset_apply E_prev hprev, hx.1, hx.2, ↓reduceIte]
        · simp only [PMF.uniformOfFinset_apply E_prev hprev, hsub hx, hx, ↓reduceIte]
      _ = _ := by
        rw [Finset.sum_const, ← Finset.mul_sum, Finset.card_sdiff_of_subset hsub, nsmul_eq_mul,
          PMF.uniformOfFinset_apply E_curr hcurr]
        by_cases hθ' : θ' ∈ E_curr
        · rw [Finset.sum_eq_single_of_mem θ' hθ' fun x _ hx => PMF.pure_apply_of_ne _ _ hx.symm,
            PMF.pure_apply_self]
          simp only [hθ', ↓reduceIte, mul_one]
          calc
            _ = (((E_prev.card - E_curr.card : ℕ) : ℝ≥0∞) + E_curr.card) *
                ((E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹) := by
              rw [add_mul, mul_left_comm (E_curr.card : ℝ≥0∞),
                ENNReal.mul_inv_cancel hC (ENNReal.natCast_ne_top _), mul_one]
            _ = _ := by
              rw [← Nat.cast_add, Nat.sub_add_cancel (Finset.card_le_card hsub), ← mul_assoc,
                ENNReal.mul_inv_cancel hP (ENNReal.natCast_ne_top _), one_mul]
        · rw [Finset.sum_eq_zero fun x hx => PMF.pure_apply_of_ne x θ' fun h => hθ' (h ▸ hx)]
          simp [hθ']
  · intro x hx
    simp only [PMF.uniformOfFinset_apply, hx, ↓reduceIte, zero_mul]

/-- Whenever `|Θ| ≤ 2 * |E|`, the conditional uniform distribution `PMF.uniformOfFinset E`
is pointwise bounded by `2 * PMF.uniformOfFintype Θ`. -/
theorem uniformOfFinset_le_two_mul_uniformOfFintype {Θ : Type*} [Fintype Θ] [Nonempty Θ]
    {E : Finset Θ} (hE : E.Nonempty) (hcard : Fintype.card Θ ≤ 2 * E.card) (θ : Θ) :
    PMF.uniformOfFinset E hE θ ≤ 2 * PMF.uniformOfFintype Θ θ := by
  classical
  rw [PMF.uniformOfFinset_apply, PMF.uniformOfFintype_apply]
  split_ifs with hθ
  · rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (by simp) (by simp),
      ENNReal.inv_mul_le_iff (Nat.cast_ne_zero.mpr hE.card_ne_zero) (ENNReal.natCast_ne_top _)]
    exact_mod_cast hcard.trans_eq (mul_comm _ _)
  · exact bot_le

/-- If the complement of `E : Finset Θ` has uniform probability mass at most `1 / 2` in a nonempty
finite space `Θ`, then `|Θ| ≤ 2 * |E|` and `E` is nonempty. -/
theorem card_le_two_mul_card_of_uniformOfFintype_compl_le_half {Θ : Type*} [Fintype Θ]
    [Nonempty Θ] {E : Finset Θ}
    (hprob : (PMF.uniformOfFintype Θ).toOuterMeasure {θ : Θ | θ ∉ E} ≤ 1 / 2) :
    Fintype.card Θ ≤ 2 * E.card ∧ E.Nonempty := by
  classical
  have hfilter : (Finset.univ.filter (· ∈ {θ : Θ | θ ∉ E})).card = Fintype.card Θ - E.card := by
    have hset : Finset.univ.filter (· ∈ {θ : Θ | θ ∉ E}) = Finset.univ \ E := by
      ext θ
      simp
    rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ E), Finset.card_univ]
  rw [toOuterMeasure_uniformOfFintype, hfilter, ← div_eq_mul_inv,
    ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
    one_div, ← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (by simp) (by simp)] at hprob
  have hnat : (Fintype.card Θ - E.card) * 2 ≤ Fintype.card Θ := by exact_mod_cast hprob
  have hΘ_pos : 0 < Fintype.card Θ := Fintype.card_pos
  exact ⟨by omega, Finset.card_pos.mp (by omega)⟩

/-- Any probability mass function `ν : PMF Θ` that takes a constant value `c` on a nonempty finset
`E` and `0` outside `E` equals `PMF.uniformOfFinset E hE`. -/
theorem pmf_eq_uniformOfFinset_of_ite_const {Θ : Type*} [DecidableEq Θ]
    {ν : PMF Θ} {E : Finset Θ} (hE : E.Nonempty) {c : ℝ≥0∞}
    (hν : ∀ θ, ν θ = if θ ∈ E then c else 0) :
    ν = PMF.uniformOfFinset E hE := by
  have h1 : c * E.card = 1 := by
    rw [← ν.tsum_coe, tsum_eq_sum (s := E)]
    · simp [hν, mul_comm]
    · intro θ hθ
      simp [hν θ, hθ]
  have hc : c = (E.card : ℝ≥0∞)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left h1
  ext θ
  rw [hν θ, hc, PMF.uniformOfFinset_apply]
  split_ifs <;> rfl

/-- Conditioning a uniform sample on membership in a nonempty subset increases the
average of a score in `[0, 1]` by at most the excluded probability. -/
theorem expect_finset_le_expect_add_compl {α : Type*} [Fintype α] [Nonempty α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) (h₀ : ∀ a, 0 ≤ f a) (h₁ : ∀ a, f a ≤ 1) :
    (𝔼 a ∈ s, f a) ≤ (𝔼 a, f a) + ((uniformOfFintype α).toOuterMeasure {a | a ∉ s}).toReal := by
  classical
  have hcard : s.card ≤ Fintype.card α := Finset.card_le_univ s
  have hs0 : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hα0 : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hle := Finset.expect_le hs (fun a _ => h₁ a)
  have hsum : ∑ a ∈ s, f a ≤ ∑ a, f a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun a _ _ => h₀ a
  have hfilter : Finset.univ.filter (fun a : α => a ∉ s) = Finset.univ \ s := by
    ext a
    simp
  rw [toOuterMeasure_uniformOfFintype_toReal]
  change (𝔼 a ∈ s, f a) ≤ (𝔼 a, f a) +
    ((Finset.univ.filter (fun a : α => a ∉ s)).card : ℝ) / Fintype.card α
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ,
    Nat.cast_sub hcard]
  have hdiff : (0 : ℝ) ≤ (Fintype.card α - s.card : ℝ) / Fintype.card α := by
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hcard)) hα0.le
  rw [Finset.expect_eq_sum_div_card] at hle
  rw [Finset.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  calc
    _ = (∑ a ∈ s, f a) / (Fintype.card α : ℝ) +
          ((∑ a ∈ s, f a) / s.card) * (((Fintype.card α : ℝ) - s.card) / Fintype.card α) := by
      field_simp [hs0.ne', hα0.ne']
      ring
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hsum hα0.le)
      (mul_le_of_le_one_left hdiff hle)

end Cslib.Probability.PMF

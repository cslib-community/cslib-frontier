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
  rw [PMF.bind_apply, PMF.uniformOfFinset_apply]
  by_cases hθ' : θ' ∈ E_curr
  · simp only [hθ', ↓reduceIte]
    rw [tsum_eq_sum (s := E_prev)]
    · have hsplit :
          ∑ x ∈ E_prev, (PMF.uniformOfFinset E_prev hprev) x *
            (if x ∈ E_curr then PMF.pure x else PMF.uniformOfFinset E_curr hcurr) θ' =
          ∑ x ∈ E_curr, (E_prev.card : ℝ≥0∞)⁻¹ * (if θ' = x then 1 else 0) +
          ∑ x ∈ E_prev \ E_curr, (E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹ := by
        rw [← Finset.sum_sdiff hsub, add_comm]
        congr 1
        · refine Finset.sum_congr rfl fun x hx => ?_
          have hx_prev : x ∈ E_prev := hsub hx
          simp only [PMF.uniformOfFinset_apply, hx_prev, hx, ↓reduceIte, PMF.pure_apply]
          congr 1
          split_ifs <;> rfl
        · refine Finset.sum_congr rfl fun x hx => ?_
          have hx_prev : x ∈ E_prev := (Finset.mem_sdiff.mp hx).1
          have hx_not : x ∉ E_curr := (Finset.mem_sdiff.mp hx).2
          simp only [PMF.uniformOfFinset_apply, hx_prev, hx_not, hθ', ↓reduceIte]
      rw [hsplit]
      have hsum1 :
          ∑ x ∈ E_curr, (E_prev.card : ℝ≥0∞)⁻¹ * (if θ' = x then 1 else 0) =
            (E_prev.card : ℝ≥0∞)⁻¹ := by
        rw [← Finset.mul_sum, Finset.sum_ite_eq E_curr θ' (fun _ => (1 : ℝ≥0∞))]
        simp only [hθ', ↓reduceIte, mul_one]
      have hsum2 :
          ∑ _x ∈ E_prev \ E_curr, (E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹ =
            ((E_prev.card - E_curr.card : ℕ) : ℝ≥0∞) *
              ((E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹) := by
        rw [Finset.sum_const, Finset.card_sdiff_of_subset hsub, nsmul_eq_mul]
      rw [hsum1, hsum2]
      have hcard_le : E_curr.card ≤ E_prev.card := Finset.card_le_card hsub
      have hprev_ne : (E_prev.card : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Finset.Nonempty.card_ne_zero hprev)
      have hcurr_ne : (E_curr.card : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Finset.Nonempty.card_ne_zero hcurr)
      have h1 : (E_prev.card : ℝ≥0∞)⁻¹ =
          (E_curr.card : ℝ≥0∞) * ((E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹) := by
        rw [← mul_assoc, mul_comm (E_curr.card : ℝ≥0∞), mul_assoc,
          ENNReal.mul_inv_cancel hcurr_ne (ENNReal.natCast_ne_top _), mul_one]
      calc (E_prev.card : ℝ≥0∞)⁻¹ +
            ((E_prev.card - E_curr.card : ℕ) : ℝ≥0∞) *
              ((E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹)
        _ = (E_curr.card : ℝ≥0∞) * ((E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹) +
            ((E_prev.card - E_curr.card : ℕ) : ℝ≥0∞) *
              ((E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹) := by
          rw [← h1]
        _ = ((E_curr.card + (E_prev.card - E_curr.card) : ℕ) : ℝ≥0∞) *
              ((E_prev.card : ℝ≥0∞)⁻¹ * (E_curr.card : ℝ≥0∞)⁻¹) := by
          rw [Nat.cast_add, add_mul]
        _ = (E_curr.card : ℝ≥0∞)⁻¹ := by
          rw [Nat.add_sub_of_le hcard_le, ← mul_assoc,
            ENNReal.mul_inv_cancel hprev_ne (ENNReal.natCast_ne_top _), one_mul]
    · intro x hx
      simp only [PMF.uniformOfFinset_apply, hx, ↓reduceIte, zero_mul]
  · simp only [hθ', ↓reduceIte]
    rw [tsum_eq_sum (s := ∅), Finset.sum_empty]
    intro x _
    by_cases hx_prev : x ∈ E_prev
    · by_cases hx_curr : x ∈ E_curr
      · have hne : θ' ≠ x := fun h => hθ' (h ▸ hx_curr)
        simp only [hx_curr, ↓reduceIte, PMF.pure_apply, hne, mul_zero]
      · simp only [hx_curr, ↓reduceIte, PMF.uniformOfFinset_apply, hθ', mul_zero]
    · simp only [PMF.uniformOfFinset_apply, hx_prev, ↓reduceIte, zero_mul]

/-- Whenever `|Θ| ≤ 2 * |E|`, the conditional uniform distribution `PMF.uniformOfFinset E`
is pointwise bounded by `2 * PMF.uniformOfFintype Θ`. -/
theorem uniformOfFinset_le_two_mul_uniformOfFintype {Θ : Type*} [Fintype Θ] [Nonempty Θ]
    {E : Finset Θ} (hE : E.Nonempty) (hcard : Fintype.card Θ ≤ 2 * E.card) (θ : Θ) :
    PMF.uniformOfFinset E hE θ ≤ 2 * PMF.uniformOfFintype Θ θ := by
  classical
  rw [PMF.uniformOfFinset_apply, PMF.uniformOfFintype_apply]
  split_ifs with hθ
  · have hE_ne : (E.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hE.card_ne_zero
    have hΘ_ne : (Fintype.card Θ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hle : (Fintype.card Θ : ℝ≥0∞) ≤ 2 * (E.card : ℝ≥0∞) := by exact_mod_cast hcard
    calc (E.card : ℝ≥0∞)⁻¹
      _ = (E.card : ℝ≥0∞)⁻¹ * ((Fintype.card Θ : ℝ≥0∞) * (Fintype.card Θ : ℝ≥0∞)⁻¹) := by
          rw [ENNReal.mul_inv_cancel hΘ_ne (ENNReal.natCast_ne_top _), mul_one]
      _ ≤ (E.card : ℝ≥0∞)⁻¹ * ((2 * (E.card : ℝ≥0∞)) * (Fintype.card Θ : ℝ≥0∞)⁻¹) := by
          gcongr
      _ = (2 * (Fintype.card Θ : ℝ≥0∞)⁻¹) * ((E.card : ℝ≥0∞)⁻¹ * (E.card : ℝ≥0∞)) := by ring
      _ = 2 * (Fintype.card Θ : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.inv_mul_cancel hE_ne (ENNReal.natCast_ne_top _), mul_one]
  · exact bot_le

/-- If the complement of `E : Finset Θ` has uniform probability mass at most `1 / 2` in a nonempty
finite space `Θ`, then `|Θ| ≤ 2 * |E|` and `E` is nonempty. -/
theorem card_le_two_mul_card_of_uniformOfFintype_compl_le_half {Θ : Type*} [Fintype Θ]
    [Nonempty Θ] {E : Finset Θ}
    (hprob : (PMF.uniformOfFintype Θ).toOuterMeasure {θ : Θ | θ ∉ E} ≤ 1 / 2) :
    Fintype.card Θ ≤ 2 * E.card ∧ E.Nonempty := by
  classical
  rw [toOuterMeasure_uniformOfFintype] at hprob
  have hfilter : (Finset.univ.filter (· ∈ {θ : Θ | θ ∉ E})).card = Fintype.card Θ - E.card := by
    have hset : Finset.univ.filter (· ∈ {θ : Θ | θ ∉ E}) = Finset.univ \ E := by
      ext θ
      simp
    rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ E), Finset.card_univ]
  rw [hfilter] at hprob
  have hΘ_pos : 0 < Fintype.card Θ := Fintype.card_pos
  have hΘ_ne : (Fintype.card Θ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hΘ_top : (Fintype.card Θ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmul : ((Fintype.card Θ - E.card : ℕ) : ℝ≥0∞) ≤ (Fintype.card Θ : ℝ≥0∞) * (1 / 2) := by
    calc ((Fintype.card Θ - E.card : ℕ) : ℝ≥0∞)
      _ = (((Fintype.card Θ - E.card : ℕ) : ℝ≥0∞) * (Fintype.card Θ : ℝ≥0∞)⁻¹) *
          (Fintype.card Θ : ℝ≥0∞) := by
          rw [mul_assoc, ENNReal.inv_mul_cancel hΘ_ne hΘ_top, mul_one]
      _ ≤ (1 / 2) * (Fintype.card Θ : ℝ≥0∞) := mul_le_mul' hprob le_rfl
      _ = (Fintype.card Θ : ℝ≥0∞) * (1 / 2) := mul_comm _ _
  have hmul2 : ((2 * (Fintype.card Θ - E.card) : ℕ) : ℝ≥0∞) ≤ (Fintype.card Θ : ℝ≥0∞) := by
    calc ((2 * (Fintype.card Θ - E.card) : ℕ) : ℝ≥0∞)
      _ = 2 * ((Fintype.card Θ - E.card : ℕ) : ℝ≥0∞) := by push_cast; rfl
      _ ≤ 2 * ((Fintype.card Θ : ℝ≥0∞) * (1 / 2)) := mul_le_mul' le_rfl hmul
      _ = (Fintype.card Θ : ℝ≥0∞) * ((2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹) := by rw [one_div]; ring
      _ = (Fintype.card Θ : ℝ≥0∞) := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have hnat : 2 * (Fintype.card Θ - E.card) ≤ Fintype.card Θ := by exact_mod_cast hmul2
  have hcard : Fintype.card Θ ≤ 2 * E.card := by omega
  have hpos : 0 < E.card := by omega
  exact ⟨hcard, Finset.card_pos.mp hpos⟩

/-- Any probability mass function `ν : PMF Θ` that takes a constant value `c` on a nonempty finset
`E` and `0` outside `E` equals `PMF.uniformOfFinset E hE`. -/
theorem pmf_eq_uniformOfFinset_of_ite_const {Θ : Type*} [DecidableEq Θ]
    {ν : PMF Θ} {E : Finset Θ} (hE : E.Nonempty) {c : ℝ≥0∞}
    (hν : ∀ θ, ν θ = if θ ∈ E then c else 0) :
    ν = PMF.uniformOfFinset E hE := by
  have hsum : (∑' θ, ν θ) = (E.card : ℝ≥0∞) * c := by
    rw [tsum_eq_sum (s := E)]
    · trans (∑ _θ ∈ E, c)
      · refine Finset.sum_congr rfl fun θ hθ => ?_
        rw [hν θ]
        simp only [hθ, ↓reduceIte]
      · rw [Finset.sum_const, nsmul_eq_mul]
    · intro θ hθ
      rw [hν θ]
      simp only [hθ, ↓reduceIte]
  have h1 : (E.card : ℝ≥0∞) * c = 1 := by
    rw [← hsum, ν.tsum_coe]
  have hcard_ne : (E.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hE.card_ne_zero
  have hc : c = (E.card : ℝ≥0∞)⁻¹ := by
    calc c
      _ = ((E.card : ℝ≥0∞)⁻¹ * (E.card : ℝ≥0∞)) * c := by
          rw [ENNReal.inv_mul_cancel hcard_ne (ENNReal.natCast_ne_top _), one_mul]
      _ = (E.card : ℝ≥0∞)⁻¹ * ((E.card : ℝ≥0∞) * c) := by ring
      _ = (E.card : ℝ≥0∞)⁻¹ := by rw [h1, mul_one]
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

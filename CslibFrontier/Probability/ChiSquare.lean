/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.Divergence
public import CslibFrontier.Probability.Hellinger
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.StatisticalDistance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.Renyi
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Chi-square divergence for discrete distributions

The Pearson `χ²` divergence `χ²(p ‖ q)` of `p : PMF α` with respect to reference distribution
`q : PMF α` (corresponding to `exp(D₂(p ‖ q)) - 1`, where `D₂` is Rényi divergence of order `2`):
* `echiSquare p q : ℝ≥0∞` equals `∑' a, ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) / q a`,
  so it is `⊤` whenever `p.support` is not contained in `q.support` (on finite types).
* `chiSquare p q : ℝ` is `(echiSquare p q).toReal`. Real-valued upper bounds and identities
  state `p.support ⊆ q.support` explicitly so off-support terms cannot silently vanish via
  `x / 0 = 0`.

Note that the reference/denominator distribution `q` is the **second** argument, matching
`MeasureTheory.InformationTheory.klDiv p.toMeasure q.toMeasure`.

## Main definitions

* `Cslib.Probability.PMF.echiSquare`: extended `ℝ≥0∞`-valued `χ²` divergence `χ²(p ‖ q)`.
* `Cslib.Probability.PMF.chiSquare`: real-valued `χ²` divergence `(echiSquare p q).toReal`.

## Main results

* `Cslib.Probability.PMF.echiSquare_ne_top_iff`: `echiSquare p q ≠ ⊤ ↔ p.support ⊆ q.support`.
* `Cslib.Probability.PMF.chiSquare_eq_sum`, `chiSquare_eq_sum_div_sub_one`,
  `one_add_chiSquare_eq_sum`: standard finite-sum formulas when `p.support ⊆ q.support`.
* `Cslib.Probability.PMF.one_add_echiSquare_pi`, `one_add_chiSquare_pi`,
  `one_add_echiSquare_iid`, `one_add_chiSquare_iid`: product and `iid` tensorization
  `1 + χ²(p^{\otimes n} ‖ q^{\otimes n}) = (1 + χ²(p ‖ q)) ^ n`.
* `Cslib.Probability.PMF.ofReal_four_mul_dist_sq_le_echiSquare`, `dist_le_sqrt_chiSquare_div_two`,
  `tvDist_le_sqrt_chiSquare`: `TV ≤ √(χ²) / 2` (for half-`L¹` `dist` and full-`L¹` `tvDist`).
* `Cslib.Probability.PMF.echiSquare_bind_le`, `chiSquare_bind_le`, `chiSquare_map_le`:
  data processing under Markov kernels and deterministic maps.
* `Cslib.Probability.PMF.one_add_chiSquare_bind_eq`, `one_add_chiSquare_bind_iid_eq`:
  the mixture second-moment identity (`Ingster` / `Le Cam`).
* `Cslib.Probability.PMF.exp_neg_half_sum_mul_log_div_le_bhattacharyya`:
  the classical overlap bounds the exponential of minus half the divergence.
* `Cslib.Probability.PMF.two_mul_hellingerSq_le_toReal_klDiv`,
  `toReal_klDiv_le_log_one_add_chiSquare`, `toReal_klDiv_le_chiSquare`,
  `two_mul_hellingerSq_le_chiSquare`: comparison hierarchy `2 h² ≤ KL ≤ log(1 + χ²) ≤ χ²`.

## References

* [Alexandre B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009], Springer,
  2009, Section 2.4.
* [Clément L. Canonne, *Topics and Techniques in Distribution Testing*][Canonne2022], Foundations
  and Trends in Communications and Information Theory, 2022; locators checked against the
  author-hosted draft (March 10, 2024): Appendix B (Definition B.1, `(B.2)`, `(B.5)`, Lemmas B.2
  and B.5) and Section 3.1 (Lemma 3.1 and `(3.10)`).
-/

public section

namespace Cslib.Probability.PMF

open Finset MeasureTheory InformationTheory
open scoped BigOperators Cslib.Probability.PMF ENNReal

variable {α β θ ι : Type*}

private lemma apply_eq_zero_of_support {p q : PMF α} (h : p.support ⊆ q.support) {a : α}
    (ha : q a = 0) : p a = 0 :=
  (PMF.apply_eq_zero_iff p a).mpr fun hap => (PMF.apply_eq_zero_iff q a).mp ha (h hap)

private lemma finset_prod_sq_div (s : Finset ι) (f g : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, f i ≠ ⊤) (hg : ∀ i ∈ s, g i ≠ ⊤) :
    (∏ i ∈ s, f i) ^ 2 / ∏ i ∈ s, g i = ∏ i ∈ s, f i ^ 2 / g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hfi : f i ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (hf i (Finset.mem_insert_self i s))
    have hgi : g i ≠ ⊤ := hg i (Finset.mem_insert_self i s)
    have hfs : (∏ j ∈ s, f j) ^ 2 ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.prod_ne_top fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hgs : ∏ j ∈ s, g j ≠ ⊤ :=
      ENNReal.prod_ne_top fun j hj => hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, mul_pow,
      ← ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hg j (Finset.mem_insert_of_mem hj))]
    rcases eq_or_ne (f i ^ 2) 0 with ha0 | ha0
    · simp [ha0]
    rcases eq_or_ne ((∏ j ∈ s, f j) ^ 2) 0 with hb0 | hb0
    · simp [hb0]
    rcases eq_or_ne (g i) 0 with hc0 | hc0
    · rw [hc0, zero_mul, ENNReal.div_zero (mul_ne_zero ha0 hb0), ENNReal.div_zero ha0,
        ENNReal.top_mul (mt ENNReal.div_eq_zero_iff.mp (not_or.mpr ⟨hb0, hgs⟩))]
    rcases eq_or_ne (∏ j ∈ s, g j) 0 with hd0 | hd0
    · rw [hd0, mul_zero, ENNReal.div_zero (mul_ne_zero ha0 hb0), ENNReal.div_zero hb0,
        ENNReal.mul_top (mt ENNReal.div_eq_zero_iff.mp (not_or.mpr ⟨ha0, hgi⟩))]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (.inl hc0) (.inl hgi)]
    ring

/-- Extended Pearson `χ²` divergence of `p` with respect to `q`, valued in `ℝ≥0∞`.
It equals `∑' a, (p a - q a)² / q a` when `p.support ⊆ q.support`, and `⊤` otherwise (on finite
types). -/
noncomputable def echiSquare (p q : PMF α) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) / q a

/-- Real-valued Pearson `χ²` divergence `(echiSquare p q).toReal` of `p` with respect to `q`.
Real-valued theorems assume `p.support ⊆ q.support` so off-support mass cannot be dropped via
`toReal ⊤ = 0`. -/
noncomputable def chiSquare (p q : PMF α) : ℝ :=
  (echiSquare p q).toReal

theorem echiSquare_eq_tsum (p q : PMF α) :
    echiSquare p q = ∑' a, ENNReal.ofReal (((p a).toReal - (q a).toReal) ^ 2) / q a := by
  rfl

@[simp]
theorem echiSquare_self (p : PMF α) : echiSquare p p = 0 := by
  simp [echiSquare]

theorem chiSquare_nonneg (p q : PMF α) : 0 ≤ chiSquare p q :=
  ENNReal.toReal_nonneg

@[simp]
theorem chiSquare_self (p : PMF α) : chiSquare p p = 0 := by
  simp [chiSquare]

theorem echiSquare_ne_top_iff [Finite α] {p q : PMF α} :
    echiSquare p q ≠ ⊤ ↔ p.support ⊆ q.support := by
  let := Fintype.ofFinite α
  rw [echiSquare, tsum_fintype, ne_eq, ENNReal.sum_eq_top]
  refine ⟨fun h a hap => by_contra fun haq => h ⟨a, Finset.mem_univ _, ?_⟩, fun h ⟨a, _, ha⟩ => ?_⟩
  · have hqa0 : q a = 0 := (PMF.apply_eq_zero_iff q a).mpr haq
    have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff p a).mp hap) (p.apply_ne_top a)
    rw [hqa0, ENNReal.div_zero (by simp [hpos])]
  · by_cases haq : q a = 0
    · simp [haq, apply_eq_zero_of_support h haq] at ha
    · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top haq ha

theorem echiSquare_eq_top_iff [Finite α] {p q : PMF α} :
    echiSquare p q = ⊤ ↔ ¬ p.support ⊆ q.support := by
  simpa using not_congr (@echiSquare_ne_top_iff α _ p q)

theorem echiSquare_eq_ofReal [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    echiSquare p q = ENNReal.ofReal (chiSquare p q) := by
  rw [chiSquare, ENNReal.ofReal_toReal (echiSquare_ne_top_iff.mpr h)]

theorem chiSquare_eq_sum [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    chiSquare p q = ∑ a, ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal := by
  rw [chiSquare, echiSquare, tsum_fintype, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : q a = 0
    · simp [ha, apply_eq_zero_of_support h ha]
    · rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro a _
    by_cases ha : q a = 0
    · simp [ha, apply_eq_zero_of_support h ha]
    · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top ha

theorem chiSquare_eq_sum_div_sub_one [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    chiSquare p q = (∑ a, (p a).toReal ^ 2 / (q a).toReal) - 1 := by
  rw [chiSquare_eq_sum h]
  have hpt (a : α) : ((p a).toReal - (q a).toReal) ^ 2 / (q a).toReal =
      (p a).toReal ^ 2 / (q a).toReal - 2 * (p a).toReal + (q a).toReal := by
    by_cases ha : q a = 0
    · simp [ha, apply_eq_zero_of_support h ha]
    · have := (ENNReal.toReal_pos ha (q.apply_ne_top a)).ne'
      field_simp; ring
  simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_toReal]
  ring

theorem one_add_chiSquare_eq_sum [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    1 + chiSquare p q = ∑ a, (p a).toReal ^ 2 / (q a).toReal := by
  linarith [chiSquare_eq_sum_div_sub_one h]

theorem chiSquare_eq_zero_iff [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    chiSquare p q = 0 ↔ p = q := by
  let := Fintype.ofFinite α
  rw [chiSquare_eq_sum h, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ =>
    div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)]
  constructor
  · intro hzero
    ext a
    by_cases ha : q a = 0
    · rw [ha, apply_eq_zero_of_support h ha]
    · have hqpos := (ENNReal.toReal_pos ha (q.apply_ne_top a)).ne'
      have hsub := sub_eq_zero.mp
        (sq_eq_zero_iff.mp ((div_eq_zero_iff.mp (hzero a (Finset.mem_univ a))).resolve_right hqpos))
      exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).mp hsub
  · rintro rfl _ _
    simp

theorem echiSquare_eq_zero_iff [Finite α] {p q : PMF α} : echiSquare p q = 0 ↔ p = q := by
  exact ⟨fun h => (chiSquare_eq_zero_iff (echiSquare_ne_top_iff.mp (by simp [h]))).mp
    (by simp [chiSquare, h]), fun h => h ▸ echiSquare_self p⟩

theorem one_add_echiSquare_eq_tsum [Finite α] (p q : PMF α) :
    1 + echiSquare p q = ∑' a, p a ^ 2 / q a := by
  let := Fintype.ofFinite α
  rw [tsum_fintype]
  by_cases h : p.support ⊆ q.support
  · rw [echiSquare_eq_ofReal h, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (chiSquare_nonneg p q), one_add_chiSquare_eq_sum h,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : q a = 0
    · simp [ha, apply_eq_zero_of_support h ha]
    · rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos ha (q.apply_ne_top a)),
        ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top a),
        ENNReal.ofReal_toReal (q.apply_ne_top a)]
  · rw [echiSquare_eq_top_iff.mpr h, add_top, eq_comm, ENNReal.sum_eq_top]
    rcases Set.not_subset.mp h with ⟨a, hap, haq⟩
    exact ⟨a, Finset.mem_univ _, by
      rw [(PMF.apply_eq_zero_iff q a).mpr haq,
        ENNReal.div_zero (pow_ne_zero 2 ((PMF.mem_support_iff p a).mp hap))]⟩

/-- Multiplicative tensorization of `1 + echiSquare` over finite independent products, valid
without any support assumption. -/
theorem one_add_echiSquare_pi [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p q : ∀ i, PMF (α i)) :
    1 + echiSquare (pi p) (pi q) = ∏ i, (1 + echiSquare (p i) (q i)) := by
  let (i : ι) := Fintype.ofFinite (α i)
  classical
  simp_rw [one_add_echiSquare_eq_tsum, tsum_fintype, Fintype.prod_sum, pi_apply]
  exact Finset.sum_congr rfl fun u _ => finset_prod_sq_div Finset.univ
    (fun i => p i (u i)) (fun i => q i (u i)) (fun i _ => (p i).apply_ne_top _)
    (fun i _ => (q i).apply_ne_top _)

/-- Tensorization of `1 + chiSquare` over finite independent products:
`1 + χ²(pi p ‖ pi q) = ∏ i, (1 + χ²(p i ‖ q i))`. -/
theorem one_add_chiSquare_pi [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p q : ∀ i, PMF (α i)) (h : ∀ i, (p i).support ⊆ (q i).support) :
    1 + chiSquare (pi p) (pi q) = ∏ i, (1 + chiSquare (p i) (q i)) := by
  have hpi : (pi p).support ⊆ (pi q).support := by
    intro u
    simp only [mem_support_pi_iff]
    exact fun hu i => h i (hu i)
  have hE := one_add_echiSquare_pi p q
  have hR : ∏ i, (1 + echiSquare (p i) (q i)) =
      ENNReal.ofReal (∏ i, (1 + chiSquare (p i) (q i))) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun _ _ => add_nonneg zero_le_one (chiSquare_nonneg _ _)]
    exact Finset.prod_congr rfl fun i _ => by
      rw [echiSquare_eq_ofReal (h i), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (chiSquare_nonneg _ _)]
  rw [hR, echiSquare_eq_ofReal hpi, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (chiSquare_nonneg _ _)] at hE
  exact (ENNReal.ofReal_eq_ofReal_iff (add_nonneg zero_le_one (chiSquare_nonneg _ _))
    (Finset.prod_nonneg fun _ _ => add_nonneg zero_le_one (chiSquare_nonneg _ _))).mp hE

/-- Multiplicative tensorization of `1 + echiSquare` for `n` i.i.d. draws, valid even when `n = 0`
or supports are not contained. -/
theorem one_add_echiSquare_iid [Finite α] (p q : PMF α) (n : ℕ) :
    1 + echiSquare (iid p n) (iid q n) = (1 + echiSquare p q) ^ n := by
  rw [iid_eq_pi, iid_eq_pi, one_add_echiSquare_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Tensorization of `1 + chiSquare` for `n` i.i.d. draws:
`1 + χ²(iid p n ‖ iid q n) = (1 + χ²(p ‖ q)) ^ n`. -/
theorem one_add_chiSquare_iid [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) (n : ℕ) :
    1 + chiSquare (iid p n) (iid q n) = (1 + chiSquare p q) ^ n := by
  rw [iid_eq_pi, iid_eq_pi, one_add_chiSquare_pi _ _ (fun _ => h), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Comparison between statistical distance and `χ²` divergence: `4 * (dist p q) ^ 2 ≤ χ²(p ‖ q)`
when `p.support ⊆ q.support`. -/
theorem four_mul_dist_sq_le_chiSquare [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    4 * dist p q ^ 2 ≤ chiSquare p q := by
  have hpt (a : α) : |(p a).toReal - (q a).toReal| =
      (|(p a).toReal - (q a).toReal| / Real.sqrt (q a).toReal) * Real.sqrt (q a).toReal := by
    by_cases ha : q a = 0
    · simp [ha, apply_eq_zero_of_support h ha]
    · exact (div_mul_cancel₀ _
        (Real.sqrt_pos.mpr (ENNReal.toReal_pos ha (q.apply_ne_top a))).ne').symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |(p a).toReal - (q a).toReal| / Real.sqrt (q a).toReal)
    (fun a => Real.sqrt (q a).toReal)
  simp_rw [← hpt, div_pow, sq_abs, Real.sq_sqrt ENNReal.toReal_nonneg, sum_toReal, mul_one,
    ← chiSquare_eq_sum h] at hcs
  exact (show 4 * dist p q ^ 2 = (∑ a, |(p a).toReal - (q a).toReal|) ^ 2 by
    rw [dist_eq]; ring).trans_le hcs

/-- Upper bound on half-`L¹` statistical distance via `χ²`:
`dist p q ≤ √(χ²(p ‖ q)) / 2` when `p.support ⊆ q.support`. -/
theorem dist_le_sqrt_chiSquare_div_two [Fintype α] {p q : PMF α} (h : p.support ⊆ q.support) :
    dist p q ≤ Real.sqrt (chiSquare p q) / 2 := by
  have hsq : dist p q ^ 2 ≤ chiSquare p q / 4 := by linarith [four_mul_dist_sq_le_chiSquare h]
  have hle := Real.le_sqrt_of_sq_le hsq
  rwa [Real.sqrt_div (chiSquare_nonneg p q),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at hle

/-- Unconditional extended inequality `ENNReal.ofReal (4 * dist p q ^ 2) ≤ echiSquare p q`. -/
theorem ofReal_four_mul_dist_sq_le_echiSquare [Fintype α] (p q : PMF α) :
    ENNReal.ofReal (4 * dist p q ^ 2) ≤ echiSquare p q := by
  by_cases h : p.support ⊆ q.support
  · exact echiSquare_eq_ofReal h ▸ ENNReal.ofReal_le_ofReal (four_mul_dist_sq_le_chiSquare h)
  · simp [echiSquare_eq_top_iff.mpr h]

/-- Upper bound on Mathlib's full-`L¹` total variation distance via `χ²`:
`tvDist p q ≤ √(χ²(p ‖ q))` when `p.support ⊆ q.support`. -/
theorem tvDist_le_sqrt_chiSquare [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (h : p.support ⊆ q.support) :
    MeasureTheory.tvDist p.toMeasure q.toMeasure ≤ Real.sqrt (chiSquare p q) := by
  let := Fintype.ofFinite α
  linarith [dist_le_sqrt_chiSquare_div_two h, dist_eq_tvDist_toMeasure_div_two p q]

private lemma one_add_echiSquare_eq_renyiMoment {γ : Type*} [Finite γ] (μ ν : PMF γ) :
    1 + echiSquare μ ν = renyiMoment 2 μ ν := by
  rw [one_add_echiSquare_eq_tsum, renyiMoment, show (2 : ℝ) - 1 = 1 by norm_num]
  exact tsum_congr fun _ => by simp only [ENNReal.rpow_one, div_eq_mul_inv, sq, mul_assoc]

/-- Unconditional data processing inequality for extended `χ²` divergence under a Markov kernel,
specialized from `renyiMoment_bind_le` at order `α = 2` (`1 + χ²(p ‖ q) = renyiMoment 2 p q`). -/
theorem echiSquare_bind_le [Finite α] [Finite β] (p q : PMF α) (kernel : α → PMF β) :
    echiSquare (p.bind kernel) (q.bind kernel) ≤ echiSquare p q := by
  have hle := renyiMoment_bind_le (by norm_num : (1 : ℝ) ≤ 2) p q kernel
  rw [← one_add_echiSquare_eq_renyiMoment, ← one_add_echiSquare_eq_renyiMoment] at hle
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp hle

/-- Data processing inequality for `χ²` divergence under a Markov kernel (real-valued). -/
theorem chiSquare_bind_le [Finite α] [Finite β] {p q : PMF α} (h : p.support ⊆ q.support)
    (kernel : α → PMF β) :
    chiSquare (p.bind kernel) (q.bind kernel) ≤ chiSquare p q :=
  ENNReal.toReal_mono (echiSquare_ne_top_iff.mpr h) (echiSquare_bind_le p q kernel)

/-- Data processing inequality for `χ²` divergence under a deterministic map. -/
theorem chiSquare_map_le [Finite α] [Finite β] {p q : PMF α} (h : p.support ⊆ q.support)
    (f : α → β) :
    chiSquare (p.map f) (q.map f) ≤ chiSquare p q := by
  simpa only [PMF.map, Function.comp_def] using chiSquare_bind_le h (fun a => PMF.pure (f a))

/-- Unconditional data processing inequality for extended `χ²` divergence under a
deterministic map. -/
theorem echiSquare_map_le [Finite α] [Finite β] (p q : PMF α) (f : α → β) :
    echiSquare (p.map f) (q.map f) ≤ echiSquare p q := by
  simpa only [PMF.map, Function.comp_def] using echiSquare_bind_le p q (fun a => PMF.pure (f a))

/-- Support containment for a mixture `μ.bind K` inside `q.support` holds whenever every supported
component `(K t).support` is contained in `q.support`. -/
theorem support_bind_subset_of_forall {μ : PMF θ} {K : θ → PMF α} {q : PMF α}
    (h : ∀ t ∈ μ.support, (K t).support ⊆ q.support) :
    (μ.bind K).support ⊆ q.support := by
  simpa only [PMF.support_bind, Set.iUnion_subset_iff] using h

/-- **Mixture second-moment identity** (Ingster / Le Cam):
for a mixture `μ.bind K` and reference distribution `q` with `(K t).support ⊆ q.support` for all
`t ∈ μ.support`,
`1 + χ²(μ.bind K ‖ q) =
  ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
    ∑ a, (K t a).toReal * (K t' a).toReal / (q a).toReal`. -/
theorem one_add_chiSquare_bind_eq [Fintype θ] [Fintype α] (μ : PMF θ) (K : θ → PMF α)
    (q : PMF α) (h : ∀ t ∈ μ.support, (K t).support ⊆ q.support) :
    1 + chiSquare (μ.bind K) q =
      ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
        ∑ a, (K t a).toReal * (K t' a).toReal / (q a).toReal := by
  rw [one_add_chiSquare_eq_sum (support_bind_subset_of_forall h)]
  simp_rw [sq, bind_apply_toReal, Finset.sum_mul_sum, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun t' _ => ?_)
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Product mixture second-moment identity:
`1 + χ²(μ.bind (fun t => pi (K t)) ‖ pi q)` expressed via products of coordinate second moments. -/
theorem one_add_chiSquare_bind_pi_eq [Fintype θ] [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (μ : PMF θ) (K : θ → ∀ i, PMF (α i)) (q : ∀ i, PMF (α i))
    (h : ∀ t ∈ μ.support, ∀ i, (K t i).support ⊆ (q i).support) :
    1 + chiSquare (μ.bind (fun t => pi (K t))) (pi q) =
      ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
        ∏ i, ∑ a, (K t i a).toReal * (K t' i a).toReal / (q i a).toReal := by
  classical
  have hsup : ∀ t ∈ μ.support, (pi (K t)).support ⊆ (pi q).support := fun t ht u hu => by
    rw [mem_support_pi_iff] at hu ⊢
    exact fun i => h t ht i (hu i)
  rw [one_add_chiSquare_bind_eq μ (fun t => pi (K t)) (pi q) hsup]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => congrArg _ ?_
  simp_rw [pi_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  exact (Fintype.prod_sum fun i a => (K t i a).toReal * (K t' i a).toReal / (q i a).toReal).symm

/-- `n`-fold i.i.d. mixture second-moment identity:
`1 + χ²(μ.bind (fun t => iid (K t) n) ‖ iid q n) =
  ∑ t, ∑ t', μ(t) μ(t') (∑ a, K(t, a) K(t', a) / q(a)) ^ n`. -/
theorem one_add_chiSquare_bind_iid_eq [Fintype θ] [Fintype α] (μ : PMF θ) (K : θ → PMF α)
    (q : PMF α) (n : ℕ) (h : ∀ t ∈ μ.support, (K t).support ⊆ q.support) :
    1 + chiSquare (μ.bind (fun t => iid (K t) n)) (iid q n) =
      ∑ t, ∑ t', (μ t).toReal * (μ t').toReal *
        (∑ a, (K t a).toReal * (K t' a).toReal / (q a).toReal) ^ n := by
  simp_rw [iid_eq_pi]
  rw [one_add_chiSquare_bind_pi_eq μ (fun t _ => K t) (fun _ => q) (fun t ht _ => h t ht)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma support_toReal_pos {p q : PMF α} (h : p.support ⊆ q.support) {a : α}
    (hpa : p a ≠ 0) : 0 < (p a).toReal ∧ 0 < (q a).toReal :=
  ⟨ENNReal.toReal_pos hpa (p.apply_ne_top a),
    ENNReal.toReal_pos
      (fun ha => (PMF.apply_eq_zero_iff q a).mp ha (h ((PMF.mem_support_iff p a).mpr hpa)))
      (q.apply_ne_top a)⟩

/-- The Bhattacharyya coefficient bounds the exponential of minus half the KL divergence. -/
theorem exp_neg_half_sum_mul_log_div_le_bhattacharyya [Fintype α] {p q : PMF α}
    (h : p.support ⊆ q.support) :
    Real.exp (-(∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) / 2) ≤
      bhattacharyya p q := by
  have hj := convexOn_exp.map_sum_le
    (t := (Finset.univ : Finset α)) (w := fun a => (p a).toReal)
    (p := fun a => -Real.log ((p a).toReal / (q a).toReal) / 2)
    (fun _ _ => ENNReal.toReal_nonneg) (sum_toReal p) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hexp : (∑ a, (p a).toReal * (-Real.log ((p a).toReal / (q a).toReal) / 2)) =
      -(∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hexp] at hj
  rw [bhattacharyya_eq_sum]
  refine hj.trans_eq (Finset.sum_congr rfl fun a _ => ?_)
  by_cases hpa : p a = 0
  · simp [hpa]
  · obtain ⟨hp, hq⟩ := support_toReal_pos h hpa
    rw [Real.exp_half, Real.exp_neg, Real.exp_log (div_pos hp hq), inv_div]
    calc
      (p a).toReal * Real.sqrt ((q a).toReal / (p a).toReal)
          = Real.sqrt ((p a).toReal ^ 2) * Real.sqrt ((q a).toReal / (p a).toReal) := by
            rw [Real.sqrt_sq hp.le]
      _ = Real.sqrt ((p a).toReal * (q a).toReal) := by
            rw [← Real.sqrt_mul (sq_nonneg _)]
            exact congrArg Real.sqrt (by field_simp)

/-- Comparison between squared Hellinger distance and KL divergence (natural log):
`2 * hellingerSq p q ≤ (klDiv p.toMeasure q.toMeasure).toReal` when `p.support ⊆ q.support`. -/
theorem two_mul_hellingerSq_le_toReal_klDiv [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {p q : PMF α} (h : p.support ⊆ q.support) :
    2 * hellingerSq p q ≤ (klDiv p.toMeasure q.toMeasure).toReal := by
  let := Fintype.ofFinite α
  rw [toReal_klDiv_toMeasure h, hellingerSq_eq_one_sub_bhattacharyya]
  linarith [exp_neg_half_sum_mul_log_div_le_bhattacharyya h,
    Real.add_one_le_exp (-(∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) / 2)]

/-- KL divergence is bounded by `log (1 + χ²)`:
`(klDiv p.toMeasure q.toMeasure).toReal ≤ Real.log (1 + chiSquare p q)`. -/
theorem toReal_klDiv_le_log_one_add_chiSquare [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {p q : PMF α} (h : p.support ⊆ q.support) :
    (klDiv p.toMeasure q.toMeasure).toReal ≤ Real.log (1 + chiSquare p q) := by
  let := Fintype.ofFinite α
  rw [toReal_klDiv_toMeasure h]
  set c : ℝ := 1 + chiSquare p q
  have hcpos : 0 < c := by linarith [chiSquare_nonneg p q]
  have hpt (a : α) :
      (p a).toReal * Real.log ((p a).toReal / (q a).toReal) - (p a).toReal * Real.log c ≤
        (p a).toReal ^ 2 / (q a).toReal / c - (p a).toReal := by
    by_cases hpa : p a = 0
    · simp [hpa]
    · obtain ⟨hppos, hqpos⟩ := support_toReal_pos h hpa
      have hlog := Real.log_le_sub_one_of_pos (div_pos (div_pos hppos hqpos) hcpos)
      rw [Real.log_div (div_pos hppos hqpos).ne' hcpos.ne'] at hlog
      nlinarith [mul_le_mul_of_nonneg_left hlog hppos.le,
        show (p a).toReal * ((p a).toReal / (q a).toReal / c) =
          (p a).toReal ^ 2 / (q a).toReal / c by ring]
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hpt a
  simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal, one_mul, ← Finset.sum_div,
    ← one_add_chiSquare_eq_sum h] at hsum
  rw [div_self hcpos.ne', sub_self] at hsum
  linarith

/-- KL divergence (natural log) is at most Pearson `χ²` divergence:
`(klDiv p.toMeasure q.toMeasure).toReal ≤ chiSquare p q`. -/
theorem toReal_klDiv_le_chiSquare [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    {p q : PMF α} (h : p.support ⊆ q.support) :
    (klDiv p.toMeasure q.toMeasure).toReal ≤ chiSquare p q := by
  linarith [toReal_klDiv_le_log_one_add_chiSquare h,
    Real.log_le_sub_one_of_pos (by linarith [chiSquare_nonneg p q] : 0 < 1 + chiSquare p q)]

/-- Comparison between squared Hellinger distance and `χ²` divergence:
`2 * hellingerSq p q ≤ chiSquare p q` when `p.support ⊆ q.support`. -/
theorem two_mul_hellingerSq_le_chiSquare [Finite α] {p q : PMF α} (h : p.support ⊆ q.support) :
    2 * hellingerSq p q ≤ chiSquare p q := by
  let : MeasurableSpace α := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  exact (two_mul_hellingerSq_le_toReal_klDiv h).trans (toReal_klDiv_le_chiSquare h)

end Cslib.Probability.PMF

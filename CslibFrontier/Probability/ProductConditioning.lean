/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import Cslib.Probability.StatisticalDistance
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.Chebyshev

/-!
# Conditioning a product distribution on an event

Condition independent coordinates `U₁, …, U_k` on an event `W`. Then the coordinates barely move:
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖² ≤ ln (1 / Pr[W]) / 2`
(`Cslib.Probability.PMF.sum_sq_dist_map_filter_pi_le`). This is Raz's conditioning lemma
[Raz, Claim 5.1][Raz1998], [Holenstein, Lemma 4.1][Holenstein2009], and it drives the coordinate
selection in the proof of the parallel repetition theorem. Holenstein states it as
`Pr[W] ≤ 2 ^ (-∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖²)` (`toOuterMeasure_toReal_le_two_rpow`), which follows
since `ln x / 2 ≤ log₂ x` for `x ≥ 1`, and uses it through Cauchy–Schwarz in the form
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖ ≤ √(k · ln (1 / Pr[W]))` (`sum_dist_map_filter_pi_le`).

The proof has three steps. Conditioning on `W` costs exactly `ln (1 / Pr[W])` nats of divergence
(`sum_mul_log_div_filter`). Divergence from a product distribution is superadditive over the
coordinates (`sum_sum_mul_log_div_map_le`): the gap is the divergence of the joint distribution
from the product of its own marginals, which is nonnegative by Gibbs' inequality. Pinsker's
inequality and Cauchy–Schwarz then bound the sum of statistical distances.

## Main results

* `Cslib.Probability.PMF.sum_mul_log_div_filter`: conditioning on `W` has divergence
  `ln (1 / Pr[W])`.
* `Cslib.Probability.PMF.sum_sum_mul_log_div_map_le`: superadditivity of divergence from a product.
* `Cslib.Probability.PMF.sum_sq_dist_map_le`: the squared distances of the marginals from the
  factors add up to at most half the divergence from the product (Pinsker's inequality).
* `Cslib.Probability.PMF.sum_sq_dist_map_filter_pi_le`: Raz's conditioning lemma.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_le_two_rpow`: Holenstein's form
  `Pr[W] ≤ 2 ^ (-∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖²)`.
* `Cslib.Probability.PMF.sq_sum_dist_map_filter_pi_le`,
  `Cslib.Probability.PMF.sum_dist_map_filter_pi_le`: the forms summed by Cauchy–Schwarz, over any
  subset of `k` coordinates and over all `k` coordinates,
  `∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖ ≤ √(k · ln (1 / Pr[W]))`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
* [R. Raz, *A parallel repetition theorem*][Raz1998]
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped Cslib.Probability.PMF

variable {α : Type*} [Fintype α]

/-- Conditioning on an event `W` has divergence `ln (1 / Pr[W])` from the original distribution,
in nats. -/
theorem sum_mul_log_div_filter (p : PMF α) (event : Set α) (hevent : ∃ a ∈ event, a ∈ p.support) :
    ∑ a, ((p.filter event hevent) a).toReal *
        Real.log (((p.filter event hevent) a).toReal / (p a).toReal) =
      Real.log (1 / (p.toOuterMeasure event).toReal) := by
  classical
  set w := (p.toOuterMeasure event).toReal
  have hw : 0 < w := (toOuterMeasure_toReal_pos_iff p event).mpr hevent
  have hterm (a : α) : ((p.filter event hevent) a).toReal *
      Real.log (((p.filter event hevent) a).toReal / (p a).toReal) =
        (if a ∈ event then (p a).toReal else 0) / w * Real.log (1 / w) := by
    rw [filter_apply_toReal]
    by_cases ha : a ∈ event
    · rw [ite_eq_left ha, ite_eq_left ha]
      by_cases hpa : (p a).toReal = 0
      · simp [hpa]
      · congr 2; field_simp; exact div_self hw.ne'
    · simp [ha]
  rw [sum_congr rfl fun a _ => hterm a, ← sum_mul, ← sum_div, ← toOuterMeasure_apply_toReal,
    div_self hw.ne', one_mul]

section Product

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- **Superadditivity of divergence from a product.** The divergences of the marginals of `P` from
the factors `p j` add up to at most the divergence of `P` from the product `pi p`, in nats. -/
theorem sum_sum_mul_log_div_map_le [DecidableEq ι] (P : PMF (∀ i, β i)) (p : ∀ i, PMF (β i))
    (h : P.support ⊆ (pi p).support) :
    ∑ j, ∑ a, ((P.map fun u => u j) a).toReal *
        Real.log (((P.map fun u => u j) a).toReal / (p j a).toReal) ≤
      ∑ u, (P u).toReal * Real.log ((P u).toReal / (pi p u).toReal) := by
  set M : ∀ j, PMF (β j) := fun j => P.map fun u => u j
  have hmarg (j : ι) := sum_map_mul P (fun u => u j)
    fun a => Real.log ((M j a).toReal / (p j a).toReal)
  have hsupp : P.support ⊆ (pi M).support := fun u hu => (mem_support_pi_iff M u).mpr fun j =>
    (PMF.mem_support_iff _ _).mpr ((pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp hu)).trans_le
      (le_map_apply P _ u)).ne'
  have hpt (u : ∀ i, β i) : (P u).toReal * Real.log ((P u).toReal / (pi p u).toReal) =
      (P u).toReal * Real.log ((P u).toReal / (pi M u).toReal) +
        ∑ j, (P u).toReal * Real.log ((M j (u j)).toReal / (p j (u j)).toReal) := by
    by_cases hu : P u = 0
    · simp [hu]
    have hu' : u ∈ P.support := (PMF.mem_support_iff _ _).mpr hu
    have hne {q : ∀ i, PMF (β i)} (hq : P.support ⊆ (pi q).support) (j : ι) :
        (q j (u j)).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨(PMF.mem_support_iff _ _).mp
        ((mem_support_pi_iff q u).mp (hq hu') j), PMF.apply_ne_top _ _⟩
    have hP : (P u).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hu, PMF.apply_ne_top _ _⟩
    rw [← mul_sum, ← mul_add]; congr 1; simp only [pi_apply, ENNReal.toReal_prod]
    rw [Real.log_div hP (prod_ne_zero_iff.mpr fun j _ => hne h j),
      Real.log_div hP (prod_ne_zero_iff.mpr fun j _ => hne hsupp j),
      Real.log_prod fun j _ => hne h j, Real.log_prod fun j _ => hne hsupp j]
    simp only [Real.log_div (hne hsupp _) (hne h _), sum_sub_distrib]; ring
  rw [sum_congr rfl fun u _ => hpt u, sum_add_distrib, sum_comm (s := univ) (t := univ)]
  simp only [← hmarg]; linarith [sum_mul_log_div_nonneg hsupp]

/-- **Pinsker's inequality for the marginals.** The squared statistical distances of the marginals
of `P` from the factors `p j` add up to at most half the divergence of `P` from the product `pi p`,
in nats: Pinsker's inequality for each marginal, summed by `sum_sum_mul_log_div_map_le`. -/
theorem sum_sq_dist_map_le [DecidableEq ι] (P : PMF (∀ i, β i)) (p : ∀ i, PMF (β i))
    (h : P.support ⊆ (pi p).support) :
    ∑ j, dist (P.map fun u => u j) (p j) ^ 2 ≤
      (∑ u, (P u).toReal * Real.log ((P u).toReal / (pi p u).toReal)) / 2 := by
  have hsum := (sum_le_sum fun j (_ : j ∈ univ) =>
    two_mul_dist_sq_le_sum_mul_log_div (p := P.map fun u => u j) (q := p j) fun a ha => by
      rw [PMF.support_map] at ha; rcases ha with ⟨u, hu, rfl⟩
      exact (mem_support_pi_iff p u).mp (h hu) j).trans (sum_sum_mul_log_div_map_le P p h)
  rw [← mul_sum] at hsum; linarith

/-- **Raz's conditioning lemma** [Raz, Claim 5.1][Raz1998], [Holenstein, Lemma 4.1][Holenstein2009].
Conditioning independent coordinates on an event `W` moves them little:
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖² ≤ ln (1 / Pr[W]) / 2`. -/
theorem sum_sq_dist_map_filter_pi_le (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) :
    ∑ j, dist (((pi p).filter W hW).map fun u => u j) (p j) ^ 2 ≤
      Real.log (1 / ((pi p).toOuterMeasure W).toReal) / 2 := by
  classical
  simpa only [sum_mul_log_div_filter] using sum_sq_dist_map_le _ p
    ((PMF.support_filter hW).subset.trans Set.inter_subset_right)

/-- **Raz's conditioning lemma** in the form of [Holenstein, Lemma 4.1, (4.1)][Holenstein2009]:
`Pr[W] ≤ 2 ^ (-∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖²)`. -/
theorem toOuterMeasure_toReal_le_two_rpow (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) :
    ((pi p).toOuterMeasure W).toReal ≤
      (2 : ℝ) ^ (-∑ j, dist (((pi p).filter W hW).map fun u => u j) (p j) ^ 2) := by
  set w := ((pi p).toOuterMeasure W).toReal
  have hw0 : 0 < w := (toOuterMeasure_toReal_pos_iff _ W).mpr hW
  have hlog : 0 ≤ Real.log (1 / w) := Real.log_nonneg
    (by rw [le_div_iff₀ hw0]; linarith [toOuterMeasure_toReal_le_one (pi p) W])
  have hle : Real.log (1 / w) / 2 ≤ Real.logb 2 (1 / w) := by
    rw [Real.logb, div_le_div_iff₀ two_pos (Real.log_pos one_lt_two)]
    nlinarith [(Real.log_le_sub_one_of_pos two_pos).trans (by norm_num : (2 : ℝ) - 1 ≤ 2)]
  rw [show w = (2 : ℝ) ^ (-Real.logb 2 (1 / w)) by
    rw [Real.rpow_neg zero_le_two, Real.rpow_logb two_pos (by norm_num) (by positivity),
      one_div, inv_inv]]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two
    (neg_le_neg ((sum_sq_dist_map_filter_pi_le p W hW).trans hle))

/-- **Raz's conditioning lemma**, summed over any `k` of the independent coordinates by
Cauchy–Schwarz: `(∑_{j ∈ s} ‖P_{Uⱼ | W} - P_{Uⱼ}‖)² ≤ k · ln (1 / Pr[W]) / 2` with `k = #s`. -/
theorem sq_sum_dist_map_filter_pi_le (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) (s : Finset ι) :
    (∑ j ∈ s, dist (((pi p).filter W hW).map fun u => u j) (p j)) ^ 2 ≤
      #s * Real.log (1 / ((pi p).toOuterMeasure W).toReal) / 2 :=
  sq_sum_le_card_mul_sum_sq.trans <| (mul_le_mul_of_nonneg_left
    ((sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _).trans (sum_sq_dist_map_filter_pi_le p W hW))
    (Nat.cast_nonneg _)).trans_eq (mul_div_assoc _ _ _).symm

/-- **Raz's conditioning lemma** in the form of [Holenstein, (4.2)][Holenstein2009]:
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖ ≤ √(k · ln (1 / Pr[W]))` for `k` independent coordinates. -/
theorem sum_dist_map_filter_pi_le (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) :
    ∑ j, dist (((pi p).filter W hW).map fun u => u j) (p j) ≤
      Real.sqrt (Fintype.card ι * Real.log (1 / ((pi p).toOuterMeasure W).toReal)) := by
  have hw0 : 0 < ((pi p).toOuterMeasure W).toReal := (toOuterMeasure_toReal_pos_iff _ W).mpr hW
  have hlog : 0 ≤ Real.log (1 / ((pi p).toOuterMeasure W).toReal) := Real.log_nonneg
    (by rw [le_div_iff₀ hw0]; linarith [toOuterMeasure_toReal_le_one (pi p) W])
  have h := card_univ (α := ι) ▸ sq_sum_dist_map_filter_pi_le p W hW univ
  exact Real.le_sqrt_of_sq_le
    (h.trans (by linarith [mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hlog]))

end Product

end Cslib.Probability.PMF

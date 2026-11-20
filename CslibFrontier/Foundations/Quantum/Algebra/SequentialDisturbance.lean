/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Approx
public import CslibFrontier.Foundations.Quantum.Algebra.SequentialMeasurement
import Mathlib.Analysis.Real.Sqrt

/-!
# State-dependent disturbance of a sequential measurement

The marginal of a later measurement is a sum of sandwiches by the products of the
earlier outcomes. Moving the target projector through each product restores the
isolated-measurement expression. The change in a weighted score is at most twice the
square root of the sum of squared commutator norms. This is the operator estimate in
[Ji, Natarajan, Vidick, Wright and Yuen, Lemma 12.16][JNVWY2020LowIndividualDegree].
-/

public section

namespace Cslib.Quantum

open Finset
open scoped Real

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

private theorem sum_re_star_mul_weight_le {ι : Type*} [Fintype ι] (φ : AlgState A)
    (X Y W : ι → A) (hW : ∀ i, star (W i) * W i ≤ 1) :
    (∑ i, (φ (star (X i) * (W i * Y i))).re) ≤
      √(∑ i, φ.norm (X i) ^ 2) * √(∑ i, φ.norm (Y i) ^ 2) := by
  calc
    _ ≤ ∑ i, φ.norm (X i) * φ.norm (Y i) := sum_le_sum fun i _ =>
      (φ.re_apply_star_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (φ.norm_mul_le_of_star_mul_self_le_one (hW i) _) (φ.norm_nonneg _))
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The one-sided change in a quadratic score after replacing a normalized family `Y`
by `X`, with a commuting contraction as weight at each index. -/
theorem AlgState.sum_weighted_quadratic_le {ι : Type*} [Fintype ι] (φ : AlgState A)
    (X Y W : ι → A) (hW : ∀ i, star (W i) * W i ≤ 1)
    (hX : ∀ i, Commute (X i) (W i)) (hY : ∀ i, Commute (Y i) (W i))
    (hXnorm : ∑ i, φ.norm (X i) ^ 2 ≤ 1) (hYnorm : ∑ i, φ.norm (Y i) ^ 2 ≤ 1) :
    (∑ i, (φ (star (X i) * X i * W i)).re) ≤
      (∑ i, (φ (star (Y i) * Y i * W i)).re) + 2 * √(∑ i, φ.norm (X i - Y i) ^ 2) := by
  let D := fun i => X i - Y i
  have hdiff (i : ι) :
      (φ (star (X i) * X i * W i)).re - (φ (star (Y i) * Y i * W i)).re =
        (φ (star (D i) * (W i * X i))).re + (φ (star (Y i) * (W i * D i))).re := by
    have heq : star (X i) * X i * W i - star (Y i) * Y i * W i =
        star (D i) * (W i * X i) + star (Y i) * (W i * D i) := by
      rw [← (hX i).eq, ← ((hX i).sub_left (hY i)).eq]
      simp only [D, star_sub]
      noncomm_ring
    rw [← Complex.sub_re, ← map_sub, heq, map_add, Complex.add_re]
  apply sub_le_iff_le_add'.mp
  rw [← sum_sub_distrib]
  simp only [hdiff, sum_add_distrib]
  have hx := (sum_re_star_mul_weight_le φ D X W hW).trans
    (by
      simpa only [mul_one, Real.sqrt_one] using mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hXnorm) (Real.sqrt_nonneg (∑ i, φ.norm (D i) ^ 2)))
  have hy := (sum_re_star_mul_weight_le φ Y D W hW).trans
    (by
      simpa only [one_mul, Real.sqrt_one] using mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt hYnorm) (Real.sqrt_nonneg (∑ i, φ.norm (D i) ^ 2)))
  simpa only [two_mul, D] using add_le_add hx hy

namespace Measurement

variable {α κ : Type*} [Fintype α] [Fintype κ]

/-- The difference between the score of a projective measurement after a normalized
prefix and its isolated score is controlled by the prefix commutators. The weights
(commuting with the effects and the prefix operators) can encode a second player's
conditional rejection effect. -/
theorem weighted_sandwich_le (φ : AlgState A) (M : Measurement α A) (hM : M.IsProjective)
    (K : κ → A) (hK : ∑ p, K p * star (K p) = 1) (W : α → A)
    (hW : ∀ a, star (W a) * W a ≤ 1) (hMW : ∀ a, Commute (M.effect a) (W a))
    (hKW : ∀ a p, Commute (star (K p)) (W a)) :
    (∑ a, ∑ p, (φ (K p * M.effect a * star (K p) * W a)).re) ≤
      (∑ a, (φ (M.effect a * W a)).re) +
        2 * √(∑ a, ∑ p, φ.norm (M.effect a * star (K p) - star (K p) * M.effect a) ^ 2) := by
  let X (z : α × κ) := M.effect z.1 * star (K z.2)
  let Y (z : α × κ) := star (K z.2) * M.effect z.1
  have hX (a : α) (p : κ) :
      star (X (a, p)) * X (a, p) = K p * M.effect a * star (K p) := by
    simp only [X, star_mul, star_star, (M.nonneg a).isSelfAdjoint.star_eq]
    rw [mul_assoc (K p), ← mul_assoc (M.effect a), hM a, ← mul_assoc (K p)]
  have hY (a : α) (p : κ) :
      star (Y (a, p)) * Y (a, p) = M.effect a * (K p * star (K p)) * M.effect a := by
    simp only [Y, star_mul, star_star, (M.nonneg a).isSelfAdjoint.star_eq, mul_assoc]
  have hXnorm : ∑ z, φ.norm (X z) ^ 2 = 1 := by
    simp only [Fintype.sum_prod_type, AlgState.norm_sq, hX]
    rw [sum_comm]
    simp only [← Complex.re_sum, ← map_sum, ← sum_mul, ← mul_sum, M.sum_effect, mul_one, hK,
      AlgState.map_one, Complex.one_re]
  have hYnorm : ∑ z, φ.norm (Y z) ^ 2 = 1 := by
    simp only [Fintype.sum_prod_type, AlgState.norm_sq, hY, ← Complex.re_sum, ← map_sum,
      ← sum_mul, ← mul_sum, hK, mul_one, show ∀ a, M.effect a * M.effect a = M.effect a from hM,
      M.sum_effect, AlgState.map_one, Complex.one_re]
  have hb := φ.sum_weighted_quadratic_le X Y (fun z => W z.1) (fun z => hW z.1)
    (fun z => (hMW z.1).mul_left (hKW z.1 z.2)) (fun z => (hKW z.1 z.2).mul_left (hMW z.1))
    hXnorm.le hYnorm.le
  simp only [Fintype.sum_prod_type, hX, hY, ← Complex.re_sum, ← map_sum, ← sum_mul, ← mul_sum,
    hK, mul_one, show ∀ a, M.effect a * M.effect a = M.effect a from hM, X, Y] at hb
  simpa only [← Complex.re_sum, ← map_sum, ← sum_mul] using hb

/-- The sum of squared commutator norms between the target projection and the adjoint
of the preceding transcript product. Later measurements do not enter the defect. -/
@[expose] noncomputable def prefixCommutatorDefect {k : ℕ} (φ : AlgState A)
    (M : Fin k → Measurement α A) (i : Fin k) : ℝ :=
  ∑ a, ∑ p, φ.norm ((M i).effect a * star (transcriptProduct (before M i) p) -
    star (transcriptProduct (before M i) p) * (M i).effect a) ^ 2

theorem prefixCommutatorDefect_nonneg {k : ℕ} (φ : AlgState A)
    (M : Fin k → Measurement α A) (i : Fin k) : 0 ≤ prefixCommutatorDefect φ M i := by
  unfold prefixCommutatorDefect
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

omit [Algebra ℂ A] [StarModule ℂ A] [SelfAdjointDecompose A] in
private theorem star_transcriptProduct_commute {k : ℕ} (M : Fin k → Measurement α A)
    (W : A) (h : ∀ j a, Commute ((M j).effect a) W) (p : Fin k → α) :
    Commute (star (transcriptProduct M p)) W := by
  induction k with
  | zero => rw [transcriptProduct_zero, star_one]; exact Commute.one_left W
  | succ k ih =>
    rw [transcriptProduct_succ, star_mul, ((M 0).nonneg (p 0)).isSelfAdjoint.star_eq]
    exact (ih (fun j => M j.succ) (fun j => h j.succ) (Fin.tail p)).mul_left (h 0 (p 0))

/-- The transcript score selected by coordinate `i` is at most its isolated score plus
twice the square root of the prefix commutator defect. The score may be weighted by
another player's rejection effect. -/
theorem sequentialProjective_weighted_le {k : ℕ} (φ : AlgState A)
    (M : Fin k → Measurement α A) (hM : ∀ j, (M j).IsProjective) (i : Fin k)
    (W : α → A) (hW : ∀ a, star (W a) * W a ≤ 1)
    (hc : ∀ j b a, Commute ((M j).effect b) (W a)) :
    (∑ g, (φ ((sequentialProjective M hM).effect g * W (g i))).re) ≤
      (∑ a, (φ ((M i).effect a * W a)).re) +
        2 * √(prefixCommutatorDefect φ M i) := by
  classical
  let K := transcriptProduct (before M i)
  have hK : ∑ p, K p * star (K p) = 1 :=
    sum_transcriptProduct_mul_star (before M i) (fun j => hM _)
  let E := (sequentialProjective M hM).effect
  have hgroup :
      (∑ g, (φ (E g * W (g i))).re) =
        ∑ a, ∑ g with g i = a, (φ (E g * W a)).re := by
    rw [← sum_fiberwise (univ : Finset (Fin k → α)) (fun g => g i)]
    refine sum_congr rfl fun a _ => sum_congr rfl fun g hg => ?_
    rw [(mem_filter.mp hg).2]
  have hcollapse (a : α) :
      (∑ g with g i = a, (φ (E g * W a)).re) =
        ∑ p, (φ (K p * (M i).effect a * star (K p) * W a)).re := by
    simp only [← Complex.re_sum, ← map_sum, ← sum_mul]
    rw [sum_filter, sequentialProjective_marginal M hM i a]
  have h := weighted_sandwich_le φ (M i) (hM i) K hK W hW (fun a => hc i a a)
    (fun a p => star_transcriptProduct_commute (before M i) (W a) (fun j b => hc _ b a) p)
  rw [hgroup]
  simp only [hcollapse]
  unfold prefixCommutatorDefect
  exact h

end Measurement

end Cslib.Quantum

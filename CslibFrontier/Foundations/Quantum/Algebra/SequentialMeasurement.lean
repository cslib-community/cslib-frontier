/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

/-!
# Sequential projective measurements

Record every outcome of a finite sequence of projective measurements. Each joint effect
sandwiches the effect of the remaining transcript by the first outcome's projection.
The construction requires no commutation between measurements.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset

variable {α A : Type*} [Fintype α] [Ring A] [PartialOrder A]

/-- The ordered product of the outcome effects along a transcript. -/
def transcriptProduct {k : ℕ} (M : Fin k → Measurement α A) (g : Fin k → α) : A :=
  (List.ofFn fun i => (M i).effect (g i)).prod

@[simp] theorem transcriptProduct_zero (M : Fin 0 → Measurement α A) (g : Fin 0 → α) :
    transcriptProduct M g = 1 := by
  unfold transcriptProduct
  rfl

theorem transcriptProduct_succ {k : ℕ} (M : Fin (k + 1) → Measurement α A) (g : Fin (k + 1) → α) :
    transcriptProduct M g = (M 0).effect (g 0) *
      transcriptProduct (fun i : Fin k => M i.succ) (Fin.tail g) := by
  unfold transcriptProduct
  rw [List.ofFn_succ, List.prod_cons]
  rfl

variable [StarRing A] [StarOrderedRing A]

/-- The joint measurement recording the outcomes of projective measurements in index order. -/
noncomputable def sequentialProjective :
    {k : ℕ} → (M : Fin k → Measurement α A) → (∀ i, (M i).IsProjective) →
      Measurement (Fin k → α) A
  | 0, _, _ => {
      effect := fun _ => 1
      nonneg := fun _ => zero_le_one
      sum_effect := by exact Fintype.sum_unique _ }
  | k + 1, M, hM => by
      let N := sequentialProjective (fun i : Fin k => M i.succ) (fun i => hM i.succ)
      refine
        { effect := fun g => (M 0).effect (g 0) * N.effect (Fin.tail g) * (M 0).effect (g 0)
          nonneg := fun g => ?_
          sum_effect := ?_ }
      · have h := star_right_conjugate_nonneg (N.nonneg (Fin.tail g)) ((M 0).effect (g 0))
        rwa [((M 0).nonneg (g 0)).isSelfAdjoint.star_eq] at h
      · have hidem (a : α) := hM 0 a
        rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp, Fintype.sum_prod_type]
        simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.tail_cons, ← sum_mul, ← mul_sum,
          N.sum_effect, mul_one, hidem, (M 0).sum_effect]

/-- The empty transcript has effect one. -/
@[simp] theorem sequentialProjective_effect_zero (M : Fin 0 → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (g : Fin 0 → α) :
    (sequentialProjective M hM).effect g = 1 := by
  rw [sequentialProjective.eq_1]

/-- The first projection sandwiches the joint effect of the remaining outcomes. -/
theorem sequentialProjective_effect_succ {k : ℕ} (M : Fin (k + 1) → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (g : Fin (k + 1) → α) :
    (sequentialProjective M hM).effect g =
      (M 0).effect (g 0) *
        (sequentialProjective (fun i : Fin k => M i.succ) (fun i => hM i.succ)).effect
          (Fin.tail g) * (M 0).effect (g 0) := by
  rw [sequentialProjective.eq_2]

/-- The effect of a transcript is the ordered product times its adjoint. -/
theorem sequentialProjective_effect {k : ℕ} (M : Fin k → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (g : Fin k → α) :
    (sequentialProjective M hM).effect g =
      transcriptProduct M g * star (transcriptProduct M g) := by
  induction k with
  | zero => rw [sequentialProjective.eq_1]; simp
  | succ k ih =>
    rw [sequentialProjective_effect_succ, transcriptProduct_succ, ih, star_mul,
      ((M 0).nonneg (g 0)).isSelfAdjoint.star_eq]
    simp only [mul_assoc]

/-- The products of all transcripts form a normalized family of measurement operators. -/
theorem sum_transcriptProduct_mul_star {k : ℕ} (M : Fin k → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) :
    ∑ g, transcriptProduct M g * star (transcriptProduct M g) = 1 := by
  simp only [← sequentialProjective_effect M hM, sum_effect]

/-- The chronological prefix before a selected position in a sequence. -/
@[expose] def before {k : ℕ} {T : Type*} (M : Fin k → T) (i : Fin k) : Fin i.val → T :=
  fun j => M (j.castLT (j.isLt.trans i.isLt))

/-- The effect of seeing outcome `b` at coordinate `i`, with all other outcomes
discarded, is the target effect sandwiched by the products of the earlier outcomes. -/
theorem sequentialProjective_marginal [DecidableEq α] {k : ℕ} (M : Fin k → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (i : Fin k) (b : α) :
    (∑ g, if g i = b then (sequentialProjective M hM).effect g else 0) =
      ∑ p, transcriptProduct (before M i) p * (M i).effect b *
        star (transcriptProduct (before M i) p) := by
  classical
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => α).sum_comp, Fintype.sum_prod_type]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.consEquiv_apply, Fin.cons_zero, sequentialProjective_effect_succ,
        Fin.tail_cons, sum_ite_irrel, ← sum_mul, ← mul_sum, sum_effect, mul_one, sum_const_zero,
        sum_ite_eq', mem_univ, ite_true, hM 0 b]
      change (M 0).effect b = ∑ _ : Fin 0 → α, (1 : A) * (M 0).effect b * star (1 : A)
      simp
    · simp only [Fin.consEquiv_apply, Fin.cons_succ, Fin.cons_zero,
        sequentialProjective_effect_succ,
        Fin.tail_cons]
      have hprefix : (fun l : Fin j.val => before M j.succ l.succ) =
          before (fun t : Fin k => M t.succ) j := rfl
      have hhead : before M j.succ (0 : Fin (j.val + 1)) = M 0 := rfl
      conv_rhs =>
        change ∑ p : Fin (j.val + 1) → α,
          transcriptProduct (before M j.succ) p * (M j.succ).effect b *
            star (transcriptProduct (before M j.succ) p)
        rw [← (Fin.consEquiv fun _ : Fin (j.val + 1) => α).sum_comp, Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => ?_
      rw [← sum_filter, ← sum_mul, ← mul_sum, sum_filter]
      simp only [ih, Fin.consEquiv_apply, transcriptProduct_succ,
        Fin.cons_zero, Fin.tail_cons, hprefix, star_mul, hhead,
        ((M 0).nonneg a).isSelfAdjoint.star_eq, sum_mul, mul_sum, mul_assoc]

/-- An operator commuting with each measured effect also commutes with each transcript effect. -/
theorem sequentialProjective_commute {k : ℕ} (M : Fin k → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (a : A) (h : ∀ i b, Commute ((M i).effect b) a)
    (g : Fin k → α) : Commute ((sequentialProjective M hM).effect g) a := by
  induction k with
  | zero =>
    rw [sequentialProjective.eq_1]
    exact Commute.one_left a
  | succ k ih =>
    rw [sequentialProjective_effect_succ]
    have ht := ih (fun i => M i.succ) (fun i => hM i.succ) (fun i => h i.succ) (Fin.tail g)
    exact ((h 0 (g 0)).mul_left ht).mul_left (h 0 (g 0))
/-- A one-step transcript has the effect of its only outcome. -/
theorem sequentialProjective_effect_one (M : Fin 1 → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (g : Fin 1 → α) :
    (sequentialProjective M hM).effect g = (M 0).effect (g 0) := by
  rw [sequentialProjective_effect_succ, sequentialProjective_effect_zero, mul_one, hM 0]

end Cslib.Quantum.Measurement

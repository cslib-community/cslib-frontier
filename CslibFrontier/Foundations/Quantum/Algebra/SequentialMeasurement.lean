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

/-!
# Sequential projective measurements

Record every outcome of a finite sequence of projective measurements. Each joint effect
sandwiches the effect of the remaining transcript by the first outcome's projection.
The construction requires no commutation between measurements.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset

variable {α A : Type*} [Fintype α] [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]

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

/-- A one-step transcript has the effect of its only outcome. -/
theorem sequentialProjective_effect_one (M : Fin 1 → Measurement α A)
    (hM : ∀ i, (M i).IsProjective) (g : Fin 1 → α) :
    (sequentialProjective M hM).effect g = (M 0).effect (g 0) := by
  rw [sequentialProjective_effect_succ, sequentialProjective_effect_zero, mul_one, hM 0]

end Cslib.Quantum.Measurement

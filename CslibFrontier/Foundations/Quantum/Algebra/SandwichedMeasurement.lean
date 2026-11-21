/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Consistency

/-!
# Sandwiched measurement effects

Sandwich each fine effect by the coarse effect indexed by its image. These
sandwiches form a submeasurement. For projective coarse effects they describe
measuring the coarse outcome first and retaining a matching fine outcome.
The remaining weight is a failure outcome.

## Main results

* `Cslib.Quantum.Measurement.sandwichBy` constructs the measurement with failure.
* `Cslib.Quantum.Measurement.abs_sum_weighted_sandwich_sub_le` compares two normalized families
  of sandwiches with the same positive middle operators.
-/

public section

namespace Cslib.Quantum

open Finset
open scoped BigOperators Real

variable {A α β : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype α] [Fintype β]

namespace Measurement

private theorem sum_sandwich_le_one (M : Measurement α A) (T : Measurement β A) (f : β → α) :
    (∑ b, M.effect (f b) * T.effect b * M.effect (f b)) ≤ 1 := by
  classical
  calc
    _ = ∑ a, M.effect a * (T.map f).effect a * M.effect a := by
      rw [← sum_fiberwise univ f (fun b => M.effect (f b) * T.effect b * M.effect (f b))]
      refine sum_congr rfl fun a _ => ?_
      rw [map_effect, mul_sum, sum_mul]
      exact sum_congr rfl fun b hb => by rw [(mem_filter.mp hb).2]
    _ ≤ ∑ a, M.effect a := by
      refine sum_le_sum fun a _ => ?_
      calc
        _ ≤ M.effect a * M.effect a := by
          simpa only [mul_one] using
            (M.nonneg a).isSelfAdjoint.conjugate_le_conjugate ((T.map f).effect_le_one a)
        _ ≤ _ := M.effect_mul_self_le a
    _ = 1 := M.sum_effect

/-- Retain a fine outcome when its image agrees with the result of the coarse
measurement. The sandwich uses the coarse effect on both sides. For a projective
coarse measurement this is the corresponding sequential measurement with failure. -/
def sandwichBy (T : Measurement β A) (M : Measurement α A) (f : β → α) :
    Measurement (Option β) A where
  effect x := x.elim (1 - ∑ b, M.effect (f b) * T.effect b * M.effect (f b))
    (fun b => M.effect (f b) * T.effect b * M.effect (f b))
  nonneg b := by
    cases b with
    | none => exact sub_nonneg.mpr (sum_sandwich_le_one M T f)
    | some b =>
        simpa only [Option.elim_some, (M.nonneg (f b)).isSelfAdjoint.star_eq] using
          star_left_conjugate_nonneg (T.nonneg b) (M.effect (f b))
  sum_effect := by rw [Fintype.sum_option]; exact sub_add_cancel _ _

@[simp]
theorem sandwichBy_effect_some (T : Measurement β A) (M : Measurement α A) (f : β → α) (b : β) :
    (T.sandwichBy M f).effect (some b) = M.effect (f b) * T.effect b * M.effect (f b) := by
  unfold sandwichBy
  rfl

end Measurement

namespace AlgState

private theorem abs_sum_norm_sq_sub_le (φ : AlgState A) (X Y : β → A)
    (hX : ∑ b, φ.norm (X b) ^ 2 ≤ 1) (hY : ∑ b, φ.norm (Y b) ^ 2 ≤ 1) :
    |(∑ b, φ.norm (X b) ^ 2) - ∑ b, φ.norm (Y b) ^ 2| ≤
      2 * √(∑ b, φ.norm (X b - Y b) ^ 2) := by
  let D := fun b => X b - Y b
  have h₁ := (φ.abs_sum_re_star_mul_le D X).trans <|
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX) (Real.sqrt_nonneg _)
  have h₂ := (φ.abs_sum_re_star_mul_le Y D).trans <|
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
  have hsplit (b : β) : star (X b) * X b - star (Y b) * Y b =
      star (D b) * X b + star (Y b) * D b := by
    simp only [D, star_sub, sub_mul, mul_sub]
    abel
  simp only [AlgState.norm_sq, ← sum_sub_distrib, ← Complex.sub_re, ← map_sub, hsplit,
    map_add, Complex.add_re, sum_add_distrib]
  exact (abs_add_le ..).trans (by
    rw [Real.sqrt_one, mul_one] at h₁
    rw [Real.sqrt_one, one_mul] at h₂
    simp only [AlgState.norm_sq, D] at h₁ h₂ ⊢
    linarith only [h₁, h₂])

/-- The difference between two sums of sandwiches is controlled by the weighted
squared state distance, provided the two sums each have state value at most one. -/
private theorem abs_sum_sandwich_sub_le (φ : AlgState A) (W X Y : β → A) (hW : ∀ b, 0 ≤ W b)
    (hX : ∑ b, (φ (star (X b) * W b * X b)).re ≤ 1)
    (hY : ∑ b, (φ (star (Y b) * W b * Y b)).re ≤ 1) :
    |(∑ b, (φ (star (X b) * W b * X b)).re) - ∑ b, (φ (star (Y b) * W b * Y b)).re| ≤
      2 * √(∑ b, (φ (star (X b - Y b) * W b * (X b - Y b))).re) := by
  choose K hK using fun b => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hW b)
  have he (b : β) (x : A) :
      φ.norm (K b * x) ^ 2 = (φ (star x * W b * x)).re := by
    rw [AlgState.norm_sq, hK b, star_mul]
    simp only [mul_assoc]
  have h := φ.abs_sum_norm_sq_sub_le (fun b => K b * X b) (fun b => K b * Y b)
    (by simpa only [he] using hX) (by simpa only [he] using hY)
  simpa only [← mul_sub, he] using h

end AlgState

namespace Measurement

/-- Compare two families of selected effects using the same, possibly outcome-dependent
positive contraction in the middle of each sandwich. This contraction can be dropped
from the state-distance bound. -/
theorem abs_sum_weighted_sandwich_sub_le (φ : AlgState A)
    (T : Measurement β A) (M N : Measurement α A) (f g : β → α)
    (C : β → A) (hC : ∀ b, C b ∈ Set.Icc (0 : A) 1)
    (hCT : ∀ b, Commute (C b) (T.effect b)) :
    let X (b : β) := M.effect (f b)
    let Y (b : β) := N.effect (g b)
    |(∑ b, (φ (X b * (C b * T.effect b) * X b)).re) -
      ∑ b, (φ (Y b * (C b * T.effect b) * Y b)).re| ≤
      2 * √(∑ b, (φ (star (X b - Y b) * T.effect b * (X b - Y b))).re) := by
  intro X Y
  let W b := C b * T.effect b
  have hW b : 0 ≤ W b := (hCT b).mul_nonneg (hC b).1 (T.nonneg b)
  have hWT b : W b ≤ T.effect b := by
    have h := (Commute.one_left (T.effect b) |>.sub_left (hCT b)).mul_nonneg
      (sub_nonneg.mpr (hC b).2) (T.nonneg b)
    simpa only [sub_mul, one_mul, sub_nonneg] using h
  have hle (D : β → A) : (∑ b, (φ (star (D b) * W b * D b)).re) ≤
      ∑ b, (φ (star (D b) * T.effect b * D b)).re :=
    sum_le_sum fun b _ => φ.re_apply_mono (star_left_conjugate_le_conjugate (hWT b) (D b))
  have hXstar b : star (X b) = X b := (M.nonneg _).isSelfAdjoint.star_eq
  have hYstar b : star (Y b) = Y b := (N.nonneg _).isSelfAdjoint.star_eq
  have hX : (∑ b, (φ (star (X b) * W b * X b)).re) ≤ 1 := (hle X).trans (by
    simpa only [hXstar, ← Complex.re_sum, ← map_sum] using
      φ.re_apply_le_one (sum_sandwich_le_one M T f))
  have hY : (∑ b, (φ (star (Y b) * W b * Y b)).re) ≤ 1 := (hle Y).trans (by
    simpa only [hYstar, ← Complex.re_sum, ← map_sum] using
      φ.re_apply_le_one (sum_sandwich_le_one N T g))
  have h := (φ.abs_sum_sandwich_sub_le W X Y hW hX hY).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hle fun b => X b - Y b)) (by norm_num))
  simpa only [hXstar, hYstar, W] using h

end Measurement

end Cslib.Quantum

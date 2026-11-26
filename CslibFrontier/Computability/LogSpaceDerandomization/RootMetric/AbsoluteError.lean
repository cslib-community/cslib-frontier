/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.FineProductMean
public import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric.ConditionalWalk
public import CslibFrontier.Foundations.Data.Finset.KthLargest.Moment

/-!
# Absolute row errors and conditional maximum envelopes

Conditional Jensen preserves the actual joint slice density. Repeating a full-rank
maximum at usage endpoints costs the explicit ambient width. The masks and errors can
all depend on the same environment; no independence or target range bound is used.
The two-array fourth-power estimate splits raw centered noise from absolute mean error.
These are original finite bounds adapting Samuel Schlesinger's row norm API.
-/
public section
namespace Cslib
open Finset
open scoped BigOperators
variable {Ω V : Type*} [Fintype Ω] [Fintype V]
  {N u : ℝ} {X Y U : Ω → V → Prop}
  [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
  [∀ σ y, Decidable (U σ y)]

/-- Two actual arrays pay the fourth moment with constant eight. -/
theorem rowNormPow_add_le (hNu : 0 ≤ N * u) (A B : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => A σ x y + B σ x y) ≤
      8 * (rowNormPow 4 N u X Y A + rowNormPow 4 N u X Y B) := by
  have hp (a b : ℝ) : |a + b| ^ 4 ≤ 8 * (|a| ^ 4 + |b| ^ 4) := by
    have h := add_pow_le (abs_nonneg a) (abs_nonneg b) 4
    norm_num only [Nat.reduceSub, Nat.reducePow] at h
    exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le a b) 4).trans h
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        ∑ y ∈ ({y | Y σ y} : Finset V), 8 * (|A σ x y| ^ 4 + |B σ x y| ^ 4) :=
      mul_le_mul_of_nonneg_left
        (expect_le_expect fun σ _ => sum_le_sum fun x _ => sum_le_sum fun y _ => hp _ _)
        (inv_nonneg.mpr hNu)
    _ = _ := by
      simp only [mul_add, sum_add_distrib, expect_add_distrib, ← mul_sum, ← mul_expect]
      ring

/-- Three nonnegative error envelopes pay a fourth moment with constant 64. -/
theorem rowNormPow_le_three (hNu : 0 ≤ N * u) (D A B C : Ω → V → V → ℝ)
    (hA : ∀ σ x y, 0 ≤ A σ x y) (hB : ∀ σ x y, 0 ≤ B σ x y)
    (hC : ∀ σ x y, 0 ≤ C σ x y)
    (hD : ∀ σ x y, X σ x → Y σ y →
      |D σ x y| ≤ A σ x y + B σ x y + C σ x y) :
    rowNormPow 4 N u X Y D ≤ 64 *
      (rowNormPow 4 N u X Y A + rowNormPow 4 N u X Y B + rowNormPow 4 N u X Y C) := by
  have hd : rowNormPow 4 N u X Y D ≤
      rowNormPow 4 N u X Y (fun σ x y => A σ x y + B σ x y + C σ x y) :=
    (rowNormPow_le_mul hNu (c := 1) fun σ x y hx hy => by
      rw [one_mul, abs_of_nonneg (add_nonneg (add_nonneg (hA _ _ _) (hB _ _ _)) (hC _ _ _))]
      exact pow_le_pow_left₀ (abs_nonneg _) (hD σ x y hx hy) 4).trans_eq (one_mul _)
  linarith [rowNormPow_add_le (X := X) (Y := Y) hNu A B,
    rowNormPow_add_le (X := X) (Y := Y) hNu (fun σ x y => A σ x y + B σ x y) C,
    rowNormPow_nonneg (s := 4) (X := X) (Y := Y) hNu C]

/-- Centered RAW noise and deterministic ABSOLUTE mean error pay the completed error.
The mean need not be a desired target or an independent random variable. -/
theorem rowNormPow_sub_le_centered (hNu : 0 ≤ N * u)
    (A : Ω → V → V → ℝ) (μ G : V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => A σ x y - G x y) ≤
      8 * (rowNormPow 4 N u X Y (fun σ x y => A σ x y - μ x y) +
        rowNormPow 4 N u X Y (fun _ x y => μ x y - G x y)) := by
  simpa only [sub_add_sub_cancel] using
    rowNormPow_add_le (X := X) (Y := Y) hNu (fun σ x y => A σ x y - μ x y)
      (fun _ x y => μ x y - G x y)

/-- A pointwise full-rank maximum envelope integrates with an explicit width cost.
Usage may be narrower than rank. In particular the maximum is never taken over usage. -/
theorem rowNormPow_le_fullRank_max (hNu : 0 ≤ N * u)
    (D E : Ω → V → V → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hE : ∀ σ x y, X σ x → U σ y →
      |E σ x y| ≤ c * kthLargest 1 {w | Y σ w} (fun w => |D σ x w|)) :
    rowNormPow 4 N u X U E ≤
      Fintype.card V * c ^ 4 * rowNormPow 4 N u X Y D := by
  unfold rowNormPow
  have hp (σ : Ω) (x : V) (hx : X σ x) :
      (∑ y ∈ ({y | U σ y} : Finset V), |E σ x y| ^ 4) ≤
        (Fintype.card V : ℝ) * c ^ 4 * ∑ w ∈ ({w | Y σ w} : Finset V), |D σ x w| ^ 4 := by
    have hmax := abs_kthLargest_pow_le_sum ({w | Y σ w} : Finset V) (D σ x) (by decide : 4 ≠ 0)
    have hb (y : V) (hy : y ∈ ({y | U σ y} : Finset V)) :
        |E σ x y| ^ 4 ≤ c ^ 4 * ∑ w ∈ ({w | Y σ w} : Finset V), |D σ x w| ^ 4 :=
      calc
        _ ≤ (c * kthLargest 1 {w | Y σ w} (fun w => |D σ x w|)) ^ 4 :=
          pow_le_pow_left₀ (abs_nonneg _) (hE σ x y hx (mem_filter.mp hy).2) 4
        _ ≤ _ := by
          rw [mul_pow, ← abs_of_nonneg (kthLargest_nonneg (k := 1))]
          exact mul_le_mul_of_nonneg_left hmax (pow_nonneg hc 4)
    calc
      _ ≤ ∑ _y : V, c ^ 4 * ∑ w ∈ ({w | Y σ w} : Finset V), |D σ x w| ^ 4 :=
        (sum_le_sum hb).trans (sum_le_univ_sum_of_nonneg fun _ =>
          mul_nonneg (pow_nonneg hc 4) (sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) 4))
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]; ring
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
        (Fintype.card V : ℝ) * c ^ 4 * ∑ w ∈ ({w | Y σ w} : Finset V), |D σ x w| ^ 4 :=
      mul_le_mul_of_nonneg_left
        (expect_le_expect fun σ _ => sum_le_sum fun x hx => hp σ x (mem_filter.mp hx).2)
        (inv_nonneg.mpr hNu)
    _ = _ := by simp only [← mul_sum, ← mul_expect]; ring

/-- Repeating a maximum over the same source by terminal rank rectangle costs two
explicit ambient widths. The input payment remains the original masked row norm. -/
theorem rowNormPow_rectangle_max_le (hNu : 0 ≤ N * u) (D : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ _ _ =>
      kthLargest 1 {z | X σ z} (fun z =>
        kthLargest 1 {w | Y σ w} (fun w => |D σ z w|))) ≤
      (Fintype.card V : ℝ) ^ 2 * rowNormPow 4 N u X Y D := by
  classical
  unfold rowNormPow
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, (Fintype.card V : ℝ) ^ 2 *
        ∑ z ∈ ({z | X σ z} : Finset V), ∑ w ∈ ({w | Y σ w} : Finset V),
          |D σ z w| ^ 4 := by
      refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
      let S : Finset V := {z | X σ z}
      let T : Finset V := {w | Y σ w}
      let m := fun z => kthLargest 1 T (fun w => |D σ z w|)
      let E := kthLargest 1 S m
      have hm (z : V) : 0 ≤ m z := kthLargest_nonneg
      have he : |E| ^ 4 ≤ ∑ z ∈ S, ∑ w ∈ T, |D σ z w| ^ 4 := by
        have h := abs_kthLargest_pow_le_sum S m (by decide : 4 ≠ 0)
        simp only [abs_of_nonneg (hm _)] at h
        refine h.trans (sum_le_sum fun z _ => ?_)
        simpa only [m, abs_of_nonneg (hm z)] using
          abs_kthLargest_pow_le_sum T (D σ z) (by decide : 4 ≠ 0)
      have hs : (#S : ℝ) ≤ Fintype.card V := mod_cast card_le_card (subset_univ S)
      have ht : (#T : ℝ) ≤ Fintype.card V := mod_cast card_le_card (subset_univ T)
      have hcard : (#S : ℝ) * #T ≤ (Fintype.card V : ℝ) ^ 2 := by
        simpa only [pow_two] using mul_le_mul hs ht (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      change (∑ _z ∈ S, ∑ _w ∈ T, |E| ^ 4) ≤ _
      simp only [sum_const, nsmul_eq_mul]
      calc
        _ = ((#S : ℝ) * #T) * |E| ^ 4 := by ring
        _ ≤ (Fintype.card V : ℝ) ^ 2 * (∑ z ∈ S, ∑ w ∈ T, |D σ z w| ^ 4) := by gcongr
    _ = _ := by simp only [← mul_expect]; ring

/-- Zero extension from usage to a larger rank domain preserves the exact integrated
row norm. This identity uses inclusion of masks, without a density estimate. -/
theorem rowNormPow_usage_mask (hUY : ∀ σ y, U σ y → Y σ y)
    (F : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => if U σ y then F σ x y else 0) =
      rowNormPow 4 N u X U F := by
  classical
  unfold rowNormPow
  refine congrArg _ (expect_congr rfl fun σ _ => sum_congr rfl fun x _ => ?_)
  rw [sum_filter, sum_filter]
  refine sum_congr rfl fun y _ => ?_
  by_cases hu : U σ y <;> simp [hu, hUY σ y]

/-- The actual conditional absolute preparation error pays only its original source
and usage row error. Zero extension keeps the full terminal rank domain on the left. -/
theorem rowNormPow_usage_conditional_abs_le (hNu : 0 ≤ N * u)
    (hUY : ∀ σ y, U σ y → Y σ y) (D : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun σ x y => if U σ y then
      rowSliceMean X U (fun τ a b => |D τ a b|) x y else 0) ≤
      rowNormPow 4 N u X U D := by
  rw [rowNormPow_usage_mask hUY]
  simpa only [rowSliceMean, conditionalTableMean, rowNormPow, abs_abs] using
    rowNormPow_conditionalTableMean_le (by decide : 4 ≠ 0) hNu X U fun σ x y => |D σ x y|

/-- Actual conditional averaging followed by clipping does not lose Jensen's density
cancellation. The remaining width comes solely from repeating the rank maximum. -/
theorem rowNormPow_clipped_conditional_le_fullRank (hNu : 0 ≤ N * u)
    (D E : Ω → V → V → ℝ) {c ζ : ℝ} (hc : 0 ≤ c)
    (hE0 : ∀ σ x y, 0 ≤ E σ x y)
    (hE : ∀ σ x y, X σ x → U σ y →
      E σ x y ≤ c * kthLargest 1 {w | Y σ w} (fun w => |D σ x w|)) :
    rowNormPow 4 N u X U (fun _ x y =>
      min 1 (|ζ| * rowSliceMean X U E x y)) ≤
      Fintype.card V * (|ζ| * c) ^ 4 * rowNormPow 4 N u X Y D := by
  refine ((rowNormPow_le_mul hNu (c := 1) fun σ x y _ _ => ?_).trans_eq (one_mul _)).trans
    ((rowNormPow_conditionalTableMean_le (by decide : 4 ≠ 0) hNu X U
        (fun τ a b => |ζ| * E τ a b)).trans
      (rowNormPow_le_fullRank_max hNu D _ (mul_nonneg (abs_nonneg ζ) hc) fun σ x y hx hy => by
        rw [abs_of_nonneg (mul_nonneg (abs_nonneg ζ) (hE0 σ x y)), mul_assoc]
        exact mul_le_mul_of_nonneg_left (hE σ x y hx hy) (abs_nonneg ζ)))
  have hm : 0 ≤ rowSliceMean X U E x y := expect_nonneg fun τ _ => hE0 τ x y
  simp only [conditionalTableMean, rowSliceMean, ← mul_expect] at hm ⊢
  rw [one_mul, abs_of_nonneg (le_min zero_le_one (mul_nonneg (abs_nonneg ζ) hm)),
    abs_of_nonneg (mul_nonneg (abs_nonneg ζ) hm)]
  exact pow_le_pow_left₀ (le_min zero_le_one (mul_nonneg (abs_nonneg ζ) hm)) (min_le_right _ _) 4
end Cslib

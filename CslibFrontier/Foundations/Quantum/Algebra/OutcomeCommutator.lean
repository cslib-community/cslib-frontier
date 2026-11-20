/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement
import CslibFrontier.Foundations.Quantum.Algebra.GatedAgreement
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Recovering commutation from coarsened outcomes

A random relabeling that rarely identifies distinct outcomes preserves the
commutator defect up to a collision charge and the error of a commuting copy.
The comparison moves one factor in the commutator to the copy. In the resulting
cross term the other factors form a positive sandwich commuting with the copy.

## Main results

* `Cslib.Quantum.Measurement.successfulPairDefect_le_average_map` bounds the original
  commutator defect using a randomly coarsened measurement.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped BigOperators

variable {A α β γ X : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ] [Fintype X] [Nonempty X]

private noncomputable def mixedDefect (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q : Measurement (Option β) A) : ℝ :=
  ∑ a, ∑ b, φ.norm (P.effect (some a) * Q.effect (some b) -
    Q.effect (some b) * R.effect (some a)) ^ 2

/-- Swapping the measurements leaves the sum of squared successful commutators unchanged. -/
theorem successfulPairDefect_comm (φ : AlgState A)
    (P : Measurement (Option α) A) (Q : Measurement (Option β) A) :
    successfulPairDefect φ P Q = successfulPairDefect φ Q P := by
  unfold successfulPairDefect
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by rw [φ.norm_sub_comm]

private theorem mixed_and_pairDefect_le (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q : Measurement (Option β) A) (hQ : Q.IsProjective) :
    mixedDefect φ P R Q ≤ 2 * (successfulPairDefect φ P Q + successfulCopyDefect φ P R) ∧
      successfulPairDefect φ P Q ≤ 2 * (mixedDefect φ P R Q + successfulCopyDefect φ P R) := by
  let e (a : α) (b : β) := Q.effect (some b) * (P.effect (some a) - R.effect (some a))
  have he : (∑ a, ∑ b, φ.norm (e a b) ^ 2) ≤ successfulCopyDefect φ P R :=
    sum_le_sum fun a _ => sum_norm_some_effect_mul_sq_le φ Q hQ _
  let p (a : α) := P.effect (some a)
  let q (b : β) := Q.effect (some b)
  let r (a : α) := R.effect (some a)
  have h (a : α) (b : β) :
      p a * q b - q b * r a = (p a * q b - q b * p a) + e a b := by
    simp only [e, p, q, r, mul_sub]
    abel
  constructor
  · unfold mixedDefect successfulPairDefect
    calc
      _ ≤ ∑ a : α, ∑ b : β, 2 * (φ.norm (p a * q b - q b * p a) ^ 2 + φ.norm (e a b) ^ 2) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => by
          change φ.norm (p a * q b - q b * r a) ^ 2 ≤ _
          rw [h]
          exact φ.norm_add_sq_le _ _
      _ ≤ _ := by
        simp only [← mul_sum, sum_add_distrib, mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add_right he _
  · unfold mixedDefect successfulPairDefect
    calc
      _ ≤ ∑ a : α, ∑ b : β, 2 * (φ.norm (p a * q b - q b * r a) ^ 2 + φ.norm (e a b) ^ 2) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => by
          change φ.norm (p a * q b - q b * p a) ^ 2 ≤ _
          rw [show p a * q b - q b * p a = (p a * q b - q b * r a) + -e a b by rw [h]; abel]
          simpa only [φ.norm_neg] using φ.norm_add_sq_le (p a * q b - q b * r a) (-e a b)
      _ ≤ _ := by
        simp only [← mul_sum, sum_add_distrib, mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add_right he _

private theorem mixedDefect_eq (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q : Measurement (Option β) A)
    (hP : P.IsProjective) (hR : R.IsProjective) (hQ : Q.IsProjective)
    (hRQ : ∀ a b, Commute (R.effect a) (Q.effect b)) :
    mixedDefect φ P R Q =
      ∑ a : α, ∑ b : β, ((φ (Q.effect (some b) * P.effect (some a) * Q.effect (some b))).re +
        (φ (Q.effect (some b) * R.effect (some a))).re -
        2 * (φ (Q.effect (some b) * P.effect (some a) * Q.effect (some b) *
          R.effect (some a))).re) := by
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  let p := P.effect (some a)
  let q := Q.effect (some b)
  let r := R.effect (some a)
  have hs : Commute r q := hRQ _ _
  have hp : star p = p := (P.nonneg _).isSelfAdjoint.star_eq
  have hq : star q = q := (Q.nonneg _).isSelfAdjoint.star_eq
  have hr : star r = r := (R.nonneg _).isSelfAdjoint.star_eq
  have hx : star (p * q) * (p * q) = q * p * q := by
    rw [star_mul, hp, hq, mul_assoc, ← mul_assoc p p, show p * p = p from hP _, ← mul_assoc]
  have hy : star (q * r) * (q * r) = q * r := by
    rw [star_mul, hq, hr, hs.eq]
    calc
      _ = q * (r * q) * r := by simp only [mul_assoc]
      _ = q * q * (r * r) := by rw [hs.eq]; simp only [mul_assoc]
      _ = _ := by rw [show q * q = q from hQ _, show r * r = r from hR _]
  change φ.norm (p * q - q * r) ^ 2 = _
  have he := norm_sub_sq (𝕜 := ℂ) (φ.toPreGNS (p * q)) (φ.toPreGNS (q * r))
  rw [← map_sub, φ.inner_toPreGNS] at he
  change φ.norm (p * q - q * r) ^ 2 =
    φ.norm (p * q) ^ 2 - 2 * (φ (star (p * q) * (q * r))).re +
      φ.norm (q * r) ^ 2 at he
  rw [AlgState.norm_sq φ (p * q), AlgState.norm_sq φ (q * r), hx, hy,
    star_mul, hp, hq, ← mul_assoc] at he
  dsimp only [p, q, r] at he ⊢
  linarith only [he]

private theorem sum_sandwich_copy_le_one (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q : Measurement (Option β) A)
    (hP : P.IsProjective) (hQ : Q.IsProjective)
    (hc : ∀ a a' b, Commute (Q.effect (some b) * P.effect (some a) * Q.effect (some b))
      (R.effect (some a'))) :
    (∑ a : α, ∑ a' : α, ∑ b : β, (φ (Q.effect (some b) * P.effect (some a) *
      Q.effect (some b) * R.effect (some a'))).re) ≤ 1 := by
  let E (a : α) (b : β) := Q.effect (some b) * P.effect (some a) * Q.effect (some b)
  have hE (a : α) (b : β) : 0 ≤ E a b := by
    simpa only [(Q.nonneg (some b)).isSelfAdjoint.star_eq] using
      star_right_conjugate_nonneg (P.nonneg (some a)) (Q.effect (some b))
  have hterm (a : α) (b : β) :
      E a b * R.successfulEffect ≤ E a b := by
    have hh : Commute (E a b) R.successfulEffect :=
      (Commute.sum_left _ _ _ fun a' _ => (hc a a' b).symm).symm
    rw [← sub_nonneg, ← mul_one_sub]
    exact ((Commute.one_right _).sub_right hh).mul_nonneg
      (hE a b) (sub_nonneg.mpr R.successfulEffect_mem_Icc.2)
  change (∑ a : α, ∑ a' : α, ∑ b : β, (φ (E a b * R.effect (some a'))).re) ≤ 1
  calc
    _ = ∑ a : α, ∑ b : β, (φ (E a b * R.successfulEffect)).re := by
      refine sum_congr rfl fun a _ => ?_
      rw [sum_comm]
      simp only [successfulEffect, mul_sum, map_sum, Complex.re_sum]
    _ ≤ ∑ a : α, ∑ b : β, (φ (E a b)).re :=
      sum_le_sum fun a _ => sum_le_sum fun b _ => φ.re_apply_mono (hterm a b)
    _ ≤ 1 := by
      simp only [← Complex.re_sum, ← map_sum]
      apply φ.re_apply_le_one
      have hterm (a : α) (b : β) : E a b =
          star (P.effect (some a) * Q.effect (some b)) *
            (P.effect (some a) * Q.effect (some b)) := by
        simp only [E, star_mul, (P.nonneg _).isSelfAdjoint.star_eq,
          (Q.nonneg _).isSelfAdjoint.star_eq, mul_assoc]
        rw [← mul_assoc (P.effect (some a)) (P.effect (some a)), hP]
      rw [sum_comm]
      simpa only [hterm] using sum_successful_product_sq_le P Q hP hQ

private theorem sum_paired_fibers (f : α → γ) (w : α → α → ℝ) :
    (∑ c : γ, ∑ a with f a = c, ∑ a' with f a' = c, w a a') =
      ∑ a, ∑ a', if f a' = f a then w a a' else 0 := by
  simp only [← sum_filter]
  rw [← sum_fiberwise univ f (fun a => ∑ a' with f a' = f a, w a a')]
  refine sum_congr rfl fun c _ => sum_congr rfl fun a ha => ?_
  rw [(mem_filter.mp ha).2]

private theorem mixedDefect_le_average_map (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q : Measurement (Option β) A)
    (hP : P.IsProjective) (hR : R.IsProjective) (hQ : Q.IsProjective)
    (hPR : ∀ a a', Commute (P.effect a) (R.effect a'))
    (hRQ : ∀ a b, Commute (R.effect a) (Q.effect b))
    (f : X → α → γ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcol : ∀ a a' : α, a ≠ a' → (𝔼 x, if f x a' = f x a then (1 : ℝ) else 0) ≤ κ) :
    mixedDefect φ P R Q ≤
      (𝔼 x, mixedDefect φ (P.map (Option.map (f x))) (R.map (Option.map (f x))) Q) + 2 * κ := by
  classical
  let p (a : α) := P.effect (some a)
  let q (b : β) := Q.effect (some b)
  let r (a : α) := R.effect (some a)
  let L := (∑ a : α, ∑ b : β, (φ (q b * p a * q b)).re) +
    ∑ a : α, ∑ b : β, (φ (q b * r a)).re
  let w (a a' : α) := ∑ b : β, (φ (q b * p a * q b * r a')).re
  have hc (a a' : α) (b : β) : Commute (q b * p a * q b) (r a') :=
    (((hRQ (some a') (some b)).symm.mul_left (hPR (some a) (some a'))).mul_left
      (hRQ (some a') (some b)).symm)
  have hw (a a' : α) : 0 ≤ w a a' := by
    refine sum_nonneg fun b _ => φ.re_apply_nonneg ((hc a a' b).mul_nonneg ?_ (R.nonneg _))
    simpa only [q, p, (Q.nonneg (some b)).isSelfAdjoint.star_eq] using
      star_right_conjugate_nonneg (P.nonneg (some a)) (Q.effect (some b))
  have hmass : (∑ a, ∑ a', w a a') ≤ 1 := sum_sandwich_copy_le_one φ P R Q hP hQ hc
  have hraw : mixedDefect φ P R Q = L - 2 * ∑ a, w a a := by
    rw [mixedDefect_eq φ P R Q hP hR hQ hRQ]
    simp only [L, w, p, q, r, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  have hmap (x : X) :
      mixedDefect φ (P.map (Option.map (f x))) (R.map (Option.map (f x))) Q =
        L - 2 * ∑ a, ∑ a', if f x a' = f x a then w a a' else 0 := by
    rw [mixedDefect_eq _ _ _ _ (hP.map _) (hR.map _) hQ
      (fun a b => (commute_map_right R _ _ (fun a' => (hRQ a' b).symm) a).symm)]
    simp only [map_option_effect_some, mul_sum, sum_mul, map_sum, Complex.re_sum]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    have hfirst :
        (∑ c : γ, ∑ b : β, ∑ a with f x a = c, (φ (q b * p a * q b)).re) =
          ∑ a : α, ∑ b : β, (φ (q b * p a * q b)).re := by
      simp_rw [sum_comm (s := univ) (f := fun (b : β) (a : α) =>
        (φ (q b * p a * q b)).re)]
      exact sum_fiberwise univ (f x) _
    have hsecond :
        (∑ c : γ, ∑ b : β, ∑ a with f x a = c, (φ (q b * r a)).re) =
          ∑ a : α, ∑ b : β, (φ (q b * r a)).re := by
      simp_rw [sum_comm (s := univ) (f := fun (b : β) (a : α) => (φ (q b * r a)).re)]
      exact sum_fiberwise univ (f x) _
    have hthird :
        (∑ c : γ, ∑ b : β, ∑ a' with f x a' = c,
          ∑ a with f x a = c, (φ (q b * p a * q b * r a')).re) =
        ∑ a, ∑ a', if f x a' = f x a then w a a' else 0 := by
      rw [← sum_paired_fibers (f x) w]
      refine sum_congr rfl fun c _ => ?_
      rw [sum_comm]
      calc
        _ = ∑ a' with f x a' = c, ∑ a with f x a = c,
            ∑ b : β, (φ (q b * p a * q b * r a')).re := by
          exact sum_congr rfl fun a' _ => sum_comm
        _ = _ := sum_comm
    change (∑ c : γ, ∑ b : β, ∑ a with f x a = c, (φ (q b * p a * q b)).re) +
      (∑ c : γ, ∑ b : β, ∑ a with f x a = c, (φ (q b * r a)).re) -
        2 * (∑ c : γ, ∑ b : β, ∑ a' with f x a' = c,
          ∑ a with f x a = c, (φ (q b * p a * q b * r a')).re) = _
    rw [hfirst, hsecond, hthird]
  have hmean (a a' : α) :
      (𝔼 x, if f x a' = f x a then w a a' else 0) ≤
        (if a' = a then w a a' else κ * w a a') := by
    by_cases h : a' = a
    · subst a'
      simp only [ite_true, Fintype.expect_const, le_rfl]
    · rw [ite_eq_right h]
      have he (x : X) : (if f x a' = f x a then w a a' else 0) =
          (if f x a' = f x a then (1 : ℝ) else 0) * w a a' := by
        split_ifs <;> simp
      simp only [he, ← expect_mul]
      exact mul_le_mul_of_nonneg_right (hcol _ _ (Ne.symm h)) (hw a a')
  have hcolmean :
      (𝔼 x, ∑ a, ∑ a', if f x a' = f x a then w a a' else 0) ≤ ∑ a, w a a + κ := by
    simp only [expect_sum_comm]
    calc
      _ ≤ ∑ a, ∑ a', if a' = a then w a a' else κ * w a a' :=
        sum_le_sum fun a _ => sum_le_sum fun a' _ => hmean a a'
      _ ≤ ∑ a, ∑ a', ((if a' = a then w a a' else 0) + κ * w a a') := by
        refine sum_le_sum fun a _ => sum_le_sum fun a' _ => ?_
        split_ifs <;> linarith [mul_nonneg hκ (hw a a')]
      _ ≤ _ := by
        simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ← mul_sum]
        linarith only [mul_le_mul_of_nonneg_left hmass hκ]
  simp only [hraw, hmap, expect_sub_distrib, Fintype.expect_const, ← mul_expect]
  linarith only [hcolmean]

/-- If a random map seldom identifies distinct successful outcomes, the original
commutator defect is controlled by the postprocessed commutators, the defect of
a commuting copy of the relabeled measurement, and the collision probability. -/
theorem successfulPairDefect_le_average_map (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q : Measurement (Option β) A)
    (hP : P.IsProjective) (hR : R.IsProjective) (hQ : Q.IsProjective)
    (hPR : ∀ a a', Commute (P.effect a) (R.effect a'))
    (hRQ : ∀ a b, Commute (R.effect a) (Q.effect b))
    (f : X → α → γ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcol : ∀ a a' : α, a ≠ a' → (𝔼 x, if f x a' = f x a then (1 : ℝ) else 0) ≤ κ) :
    successfulPairDefect φ P Q ≤
      4 * (𝔼 x, successfulPairDefect φ (P.map (Option.map (f x))) Q) +
        6 * successfulCopyDefect φ P R + 4 * κ := by
  have h := mixedDefect_le_average_map φ P R Q hP hR hQ hPR hRQ f hκ hcol
  have h' := (mixed_and_pairDefect_le φ P R Q hQ).2
  have hm := expect_le_expect (s := (univ : Finset X)) fun x _ =>
    ((mixed_and_pairDefect_le φ (P.map (Option.map (f x))) (R.map (Option.map (f x))) Q hQ).1).trans
      (mul_le_mul_of_nonneg_left (add_le_add_right
        (successfulCopyDefect_map_le φ P R hP hR (fun a a' => hPR (some a) (some a')) (f x)) _)
        (by norm_num))
  simp only [← mul_expect, expect_add_distrib, Fintype.expect_const] at hm
  linarith only [h, h', hm]

end Cslib.Quantum.Measurement

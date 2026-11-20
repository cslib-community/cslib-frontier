/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.CStar
public import CslibFrontier.Foundations.Quantum.Algebra.PrefixCommutator
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Estimates for projective measurements with a failure outcome

A completed projective measurement has ordinary outcomes `some a` and a complementary
effect at `none`. Estimates on the ordinary effects control the complete measurement.
Orthogonality and agreement with a commuting copy are what avoid a factor proportional
to the number of ordinary outcomes. This addresses the completion step in
[Ji, Natarajan, Vidick, Wright and Yuen, §12.3][JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.Quantum.Measurement.copyDefect_le_two_mul_successfulCopyDefect`: the copy discrepancy
  after including the failure outcome.
* `Cslib.Quantum.Measurement.pairCommutatorDefect_le_successful`: the two-outcome-family
  commutator estimate after including both failure effects.
* `Cslib.Quantum.Measurement.average_completedDefects_le`: the combined estimates under
  uniform independent questions.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped BigOperators

variable {A α β κ : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype α] [Fintype β] [Fintype κ]

/-- The sum of the successful effects within a completed measurement. -/
def successfulEffect (M : Measurement (Option α) A) : A :=
  ∑ a, M.effect (some a)

omit [StarOrderedRing A] in
theorem effect_none_eq_one_sub_successfulEffect (M : Measurement (Option α) A) :
    M.effect none = 1 - M.successfulEffect := by
  unfold successfulEffect
  exact eq_sub_of_add_eq (by simpa only [Fintype.sum_option] using M.sum_effect)

private theorem norm_sum_effect_mul_sq_le (φ : AlgState A)
    (M : Measurement β A) (hM : M.IsProjective) (ι : κ ↪ β) (X : κ → A) :
    φ.norm (∑ a, M.effect (ι a) * X a) ^ 2 ≤ ∑ a, φ.norm (X a) ^ 2 := by
  classical
  rw [AlgState.norm_sq, star_sum, sum_mul, map_sum, Complex.re_sum]
  refine sum_le_sum fun a _ => ?_
  rw [mul_sum, map_sum, Complex.re_sum]
  rw [sum_eq_single_of_mem a (mem_univ a)]
  · rw [← AlgState.norm_sq]
    apply pow_le_pow_left₀ (φ.norm_nonneg _)
    refine φ.norm_mul_le_of_star_mul_self_le_one ?_ _
    rw [((M.nonneg (ι a)).isSelfAdjoint.star_eq), hM (ι a)]
    exact M.effect_le_one _
  · intro b hb hba
    simp only [star_mul, ((M.nonneg (ι a)).isSelfAdjoint.star_eq),
      mul_assoc, ← mul_assoc (M.effect (ι a)), hM.mul_eq_zero (ι.injective.ne hba.symm),
      zero_mul, mul_zero, map_zero, Complex.zero_re]

private theorem sum_norm_selected_effect_mul_sq_le (φ : AlgState A) (M : Measurement β A)
    (hM : M.IsProjective) (ι : κ ↪ β) (x : A) :
    (∑ b, φ.norm (M.effect (ι b) * x) ^ 2) ≤ φ.norm x ^ 2 := by
  rw [← sum_norm_effect_mul_sq φ M hM x]
  calc
    _ = ∑ b ∈ univ.map ι, φ.norm (M.effect b * x) ^ 2 := by rw [sum_map]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _

/-- Commuting with each successful projection, together with a commuting copy for those
projections, controls commutation with the total successful effect. -/
theorem sum_successfulEffect_commutator_sq_le (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q : Measurement β A) (ι : κ ↪ β)
    (hP : P.IsProjective) (hR : R.IsProjective) (hQ : Q.IsProjective)
    (hPR : ∀ a b, Commute (P.effect (some a)) (R.effect (some b)))
    (hQR : ∀ a b, Commute (Q.effect b) (R.effect (some a))) :
    (∑ b, φ.norm (P.successfulEffect * Q.effect (ι b) -
      Q.effect (ι b) * P.successfulEffect) ^ 2) ≤
      8 * ((∑ b, ∑ a, φ.norm (P.effect (some a) * Q.effect (ι b) -
        Q.effect (ι b) * P.effect (some a)) ^ 2) +
        ∑ a, φ.norm (P.effect (some a) - R.effect (some a)) ^ 2) := by
  let X a b := P.effect (some a) * Q.effect (ι b) - Q.effect (ι b) * P.effect (some a)
  let D a := P.effect (some a) - R.effect (some a)
  let U b := ∑ a, P.effect (some a) * X a b
  let V b := ∑ a, R.effect (some a) * X a b
  let W b := ∑ a, P.effect (some a) * (Q.effect (ι b) * D a)
  let Z b := Q.effect (ι b) * ∑ a, P.effect (some a) * D a
  have heq (b : κ) : P.successfulEffect * Q.effect (ι b) -
      Q.effect (ι b) * P.successfulEffect = U b + V b + W b - Z b := by
    unfold successfulEffect U V W Z
    simp only [sum_mul, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    have hc : R.effect (some a) * X a b = X a b * R.effect (some a) :=
      (((hPR a a).mul_left (hQR a (ι b))).sub_left
        ((hQR a (ι b)).mul_left (hPR a a))).eq.symm
    rw [hc]
    dsimp only [X, D]
    have hidem : P.effect (some a) * P.effect (some a) = P.effect (some a) := hP _
    calc
      _ = (P.effect (some a) * P.effect (some a)) * Q.effect (ι b) -
          Q.effect (ι b) * (P.effect (some a) * P.effect (some a)) := by rw [hidem]
      _ = _ := by noncomm_ring
  have hu (b : κ) : φ.norm (U b) ^ 2 ≤ ∑ a, φ.norm (X a b) ^ 2 :=
    norm_sum_effect_mul_sq_le φ P hP Function.Embedding.some _
  have hv (b : κ) : φ.norm (V b) ^ 2 ≤ ∑ a, φ.norm (X a b) ^ 2 :=
    norm_sum_effect_mul_sq_le φ R hR Function.Embedding.some _
  have hw : ∑ b, φ.norm (W b) ^ 2 ≤ ∑ a, φ.norm (D a) ^ 2 := by
    calc
      _ ≤ ∑ b, ∑ a, φ.norm (Q.effect (ι b) * D a) ^ 2 := sum_le_sum fun b _ =>
        norm_sum_effect_mul_sq_le φ P hP Function.Embedding.some _
      _ ≤ _ := by
        rw [sum_comm]
        exact sum_le_sum fun a _ => sum_norm_selected_effect_mul_sq_le φ Q hQ ι _
  have hz : ∑ b, φ.norm (Z b) ^ 2 ≤ ∑ a, φ.norm (D a) ^ 2 :=
    (sum_norm_selected_effect_mul_sq_le φ Q hQ ι _).trans
      (norm_sum_effect_mul_sq_le φ P hP Function.Embedding.some _)
  have hpoint (b : κ) : φ.norm (U b + V b + W b - Z b) ^ 2 ≤
      4 * (φ.norm (U b) ^ 2 + φ.norm (V b) ^ 2 + φ.norm (W b) ^ 2 + φ.norm (Z b) ^ 2) := by
    have h := (φ.norm_sub_le (U b + V b + W b) (Z b)).trans (add_le_add_left
      ((φ.norm_add_le (U b + V b) (W b)).trans (add_le_add_left (φ.norm_add_le _ _) _)) _)
    refine (pow_le_pow_left₀ (φ.norm_nonneg _) h 2).trans ?_
    nlinarith [sq_nonneg (φ.norm (U b) - φ.norm (V b)),
      sq_nonneg (φ.norm (U b) - φ.norm (W b)), sq_nonneg (φ.norm (U b) - φ.norm (Z b)),
      sq_nonneg (φ.norm (V b) - φ.norm (W b)), sq_nonneg (φ.norm (V b) - φ.norm (Z b)),
      sq_nonneg (φ.norm (W b) - φ.norm (Z b))]
  simp only [heq]
  refine (sum_le_sum fun b _ => hpoint b).trans ?_
  simp only [← mul_sum, sum_add_distrib]
  change _ ≤ 8 * ((∑ b, ∑ a, φ.norm (X a b) ^ 2) + ∑ a, φ.norm (D a) ^ 2)
  linarith [sum_le_sum (s := univ) fun b _ => hu b, sum_le_sum (s := univ) fun b _ => hv b]

/-- Agreement defect on successful outcomes of two completed measurements. -/
@[expose] noncomputable def successfulCopyDefect (φ : AlgState A)
    (P R : Measurement (Option α) A) : ℝ :=
  ∑ a, φ.norm (P.effect (some a) - R.effect (some a)) ^ 2

/-- The failure effects differ by at most the summed squared discrepancy of the successful
effects in the state norm. Cross terms between distinct successful outcomes are nonpositive. -/
theorem norm_none_sub_sq_le_successfulCopyDefect (φ : AlgState A)
    (P R : Measurement (Option α) A) (hP : P.IsProjective) (hR : R.IsProjective)
    (hc : ∀ a b, Commute (P.effect (some a)) (R.effect (some b))) :
    φ.norm (P.effect none - R.effect none) ^ 2 ≤ successfulCopyDefect φ P R := by
  classical
  let D (a : α) := P.effect (some a) - R.effect (some a)
  have hd : P.effect none - R.effect none = -(∑ a, D a) := by
    rw [effect_none_eq_one_sub_successfulEffect, effect_none_eq_one_sub_successfulEffect]
    unfold successfulEffect D
    rw [sum_sub_distrib]
    abel
  unfold successfulCopyDefect
  change _ ≤ ∑ a, φ.norm (D a) ^ 2
  rw [hd, AlgState.norm_neg, AlgState.norm_sq, star_sum, sum_mul, map_sum, Complex.re_sum]
  refine sum_le_sum fun a _ => ?_
  rw [mul_sum, map_sum, Complex.re_sum]
  calc
    _ ≤ ∑ b, if b = a then φ.norm (D a) ^ 2 else 0 := by
      refine sum_le_sum fun b _ => ?_
      by_cases hab : b = a
      · subst b
        rw [ite_eq_left rfl, AlgState.norm_sq]
      · rw [ite_eq_right hab]
        have hp := hP.mul_eq_zero ((Option.some_injective α).ne (Ne.symm hab))
        have hr := hR.mul_eq_zero ((Option.some_injective α).ne (Ne.symm hab))
        have hpr := φ.re_apply_nonneg
          (Commute.mul_nonneg (P.nonneg (some a)) (R.nonneg (some b)) (hc a b))
        have hrp := φ.re_apply_nonneg
          (Commute.mul_nonneg (R.nonneg (some a)) (P.nonneg (some b)) (hc b a).symm)
        simp only [D, star_sub, (P.nonneg (some a)).isSelfAdjoint.star_eq,
          (R.nonneg (some a)).isSelfAdjoint.star_eq, sub_mul, mul_sub, hp, hr, zero_sub,
          sub_zero, map_sub, map_neg, Complex.sub_re, Complex.neg_re]
        linarith
    _ = _ := by simp

/-- The completed copy defect costs at most twice the successful part. -/
theorem copyDefect_le_two_mul_successfulCopyDefect (φ : AlgState A)
    (P R : Measurement (Option α) A) (hP : P.IsProjective) (hR : R.IsProjective)
    (hc : ∀ a b, Commute (P.effect (some a)) (R.effect (some b))) :
    copyDefect φ P R ≤ 2 * successfulCopyDefect φ P R := by
  unfold copyDefect
  rw [Fintype.sum_option]
  change φ.norm (P.effect none - R.effect none) ^ 2 + successfulCopyDefect φ P R ≤ _
  rw [two_mul]
  exact add_le_add_left (norm_none_sub_sq_le_successfulCopyDefect φ P R hP hR hc) _

/-- Commutator defect restricted to pairs of successful outcomes. -/
@[expose] noncomputable def successfulPairDefect (φ : AlgState A)
    (P : Measurement (Option α) A) (Q : Measurement (Option β) A) : ℝ :=
  ∑ a, ∑ b, φ.norm (P.effect (some a) * Q.effect (some b) -
    Q.effect (some b) * P.effect (some a)) ^ 2

private theorem norm_commutator_none (φ : AlgState A) (P : Measurement (Option α) A) (x : A) :
    φ.norm (P.effect none * x - x * P.effect none) =
      φ.norm (P.successfulEffect * x - x * P.successfulEffect) := by
  rw [effect_none_eq_one_sub_successfulEffect]
  have h : (1 - P.successfulEffect) * x - x * (1 - P.successfulEffect) =
      -(P.successfulEffect * x - x * P.successfulEffect) := by noncomm_ring
  rw [h, AlgState.norm_neg]

/-- The commutator bound after adjoining the two failure outcomes. There is no factor
depending on the size of either outcome alphabet. -/
theorem pairCommutatorDefect_le_successful (φ : AlgState A)
    (P R : Measurement (Option α) A) (Q T : Measurement (Option β) A)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (hR : R.IsProjective) (hT : T.IsProjective)
    (hPR : ∀ a b, Commute (P.effect a) (R.effect b))
    (hQR : ∀ a b, Commute (Q.effect a) (R.effect b))
    (hPT : ∀ a b, Commute (P.effect a) (T.effect b))
    (hQT : ∀ a b, Commute (Q.effect a) (T.effect b)) :
    pairCommutatorDefect φ P Q ≤ 81 * successfulPairDefect φ P Q +
      8 * successfulCopyDefect φ P R + 72 * successfulCopyDefect φ Q T := by
  let f (a : Option α) (b : Option β) :=
    φ.norm (P.effect a * Q.effect b - Q.effect b * P.effect a) ^ 2
  have hleft :
      (∑ b, f none b) ≤ 8 * ((∑ a : α, ∑ b, f (some a) b) + successfulCopyDefect φ P R) := by
    have h := sum_successfulEffect_commutator_sq_le φ P R Q (Function.Embedding.refl (Option β))
      hP hR hQ (fun a b => hPR (some a) (some b)) (fun a b => hQR b (some a))
    -- Reorder the success-by-all sum on the right.
    have hsum : (∑ b : Option β, ∑ a : α, f (some a) b) = ∑ a : α, ∑ b, f (some a) b :=
      sum_comm
    simpa only [Function.Embedding.refl_apply, f, norm_commutator_none, ← hsum,
      successfulCopyDefect] using h
  have hright : (∑ a : α, f (some a) none) ≤
      8 * (successfulPairDefect φ P Q + successfulCopyDefect φ Q T) := by
    have h := sum_successfulEffect_commutator_sq_le φ Q T P Function.Embedding.some
      hQ hT hP (fun a b => hQT (some a) (some b)) (fun a b => hPT b (some a))
    have hn (a : α) :
        φ.norm (Q.successfulEffect * P.effect (some a) -
          P.effect (some a) * Q.successfulEffect) =
        φ.norm (P.effect (some a) * Q.effect none - Q.effect none * P.effect (some a)) :=
      (norm_commutator_none φ Q _).symm.trans (φ.norm_sub_comm _ _)
    have hs (a : α) (b : β) :
        φ.norm (Q.effect (some b) * P.effect (some a) - P.effect (some a) * Q.effect (some b)) =
        φ.norm (P.effect (some a) * Q.effect (some b) - Q.effect (some b) * P.effect (some a)) :=
      φ.norm_sub_comm _ _
    simpa only [Function.Embedding.some_apply, hn, hs, f,
      successfulPairDefect, successfulCopyDefect] using h
  have hsuccess : ∑ a : α, ∑ b, f (some a) b =
      (∑ a : α, f (some a) none) + successfulPairDefect φ P Q := by
    simp only [Fintype.sum_option, successfulPairDefect, sum_add_distrib, f]
  unfold pairCommutatorDefect
  change (∑ a, ∑ b, f a b) ≤ _
  rw [Fintype.sum_option, hsuccess]
  rw [hsuccess] at hleft
  linarith

/-- The completed pair and copy defects under independent uniform questions, expressed in
terms of the two averages over successful outcomes. -/
theorem average_completedDefects_le {X : Type*} [Fintype X] [Nonempty X] (φ : AlgState A)
    (P R : X → Measurement (Option α) A)
    (hP : ∀ x, (P x).IsProjective) (hR : ∀ x, (R x).IsProjective)
    (hc : ∀ x y a b, Commute ((P x).effect a) ((R y).effect b)) {χ ζ : ℝ}
    (hpair : (𝔼 x, 𝔼 y, successfulPairDefect φ (P x) (P y)) ≤ χ)
    (hcopy : (𝔼 x, successfulCopyDefect φ (P x) (R x)) ≤ ζ) :
    (𝔼 x, 𝔼 y, pairCommutatorDefect φ (P x) (P y)) ≤ 81 * χ + 80 * ζ ∧
      (𝔼 x, copyDefect φ (P x) (R x)) ≤ 2 * ζ := by
  constructor
  · calc
      _ ≤ 𝔼 x, 𝔼 y, (81 * successfulPairDefect φ (P x) (P y) +
            8 * successfulCopyDefect φ (P x) (R x) + 72 * successfulCopyDefect φ (P y) (R y)) :=
        expect_le_expect fun x _ => expect_le_expect fun y _ =>
          pairCommutatorDefect_le_successful φ (P x) (R x) (P y) (R y)
            (hP x) (hP y) (hR x) (hR y) (hc x x) (hc y x) (hc x y) (hc y y)
      _ = 81 * (𝔼 x, 𝔼 y, successfulPairDefect φ (P x) (P y)) +
            80 * (𝔼 x, successfulCopyDefect φ (P x) (R x)) := by
        simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
        ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 𝔼 x, (2 * successfulCopyDefect φ (P x) (R x)) :=
        expect_le_expect fun x _ => copyDefect_le_two_mul_successfulCopyDefect φ (P x) (R x)
          (hP x) (hR x) (fun a b => hc x x (some a) (some b))
      _ = 2 * (𝔼 x, successfulCopyDefect φ (P x) (R x)) := by rw [Finset.mul_expect]
      _ ≤ _ := by gcongr

end Cslib.Quantum.Measurement

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement
import CslibFrontier.Foundations.Quantum.Algebra.CStar

/-!
# Consistency after completing a submeasurement

Completing two commuting submeasurements makes failure an ordinary outcome.
When the successful marginals agree, the full disagreement probability is at
most twice the gap between successful mass and diagonal agreement. Under
equality of the squared marginals, this also bounds the local projectivity
defect to which measurement orthogonalization applies.

## Main results

* `Cslib.Quantum.Measurement.one_sub_agreement_le_two_mul_successfulGap` controls
  consistency on the completed alphabet.
* `Cslib.Quantum.Measurement.agreement_le_sum_effect_sq_of_equal` controls
  two-sided agreement by the local squared effects.
* `Cslib.Quantum.Measurement.agreement_le_agreement_map` and
  `Cslib.Quantum.Measurement.abs_agreement_sub_right_le` transfer agreement
  through shared relabeling and a change of measurement.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped Real

variable {A α : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype α]

/-- With identical successful masses, disagreement on the completed alphabet
costs at most twice the successful disagreement on one side. A successful
answer on either side accounts for every disagreement, and an outcome on
which both sides succeed and disagree is counted twice on the right. -/
theorem one_sub_agreement_le_two_mul_successfulGap (φ : AlgState A)
    (L R : Measurement (Option α) A)
    (hcomm : ∀ a b, Commute (L.effect a) (R.effect b))
    (hmass : (φ L.successfulEffect).re = (φ R.successfulEffect).re) :
    1 - agreement φ L R ≤ 2 * ((φ L.successfulEffect).re -
      ∑ a, (φ (L.effect (some a) * R.effect (some a))).re) := by
  have hdiag : (∑ a, (φ (L.effect (some a) * R.effect (some a))).re) ≤
      (φ (L.successfulEffect * R.successfulEffect)).re := by
    simp only [successfulEffect, sum_mul, mul_sum, map_sum, Complex.re_sum]
    exact sum_le_sum fun a _ => single_le_sum (fun b _ => φ.re_apply_nonneg
      ((hcomm (some b) (some a)).mul_nonneg (L.nonneg _) (R.nonneg _))) (mem_univ a)
  have hnone : (φ (L.effect none * R.effect none)).re =
      1 - (φ L.successfulEffect).re - (φ R.successfulEffect).re +
        (φ (L.successfulEffect * R.successfulEffect)).re := by
    rw [L.effect_none_eq_one_sub_successfulEffect, R.effect_none_eq_one_sub_successfulEffect]
    simp only [sub_mul, mul_sub, one_mul, mul_one, map_sub, φ.map_one, Complex.one_re,
      Complex.sub_re]
    ring
  rw [agreement, Fintype.sum_option, hnone]
  linarith only [hdiag, hmass]

/-- Equal squared marginals bound the diagonal agreement by the sum of the
squared effects on either side. In a symmetric tensor strategy the marginal
equality follows from swap invariance of the state. -/
theorem agreement_le_sum_effect_sq_of_equal (φ : AlgState A) (L R : Measurement α A)
    (hcomm : ∀ a, Commute (L.effect a) (R.effect a))
    (hsq : ∀ a, (φ (L.effect a * L.effect a)).re = (φ (R.effect a * R.effect a)).re) :
    agreement φ L R ≤ ∑ a, (φ (L.effect a * L.effect a)).re := by
  refine sum_le_sum fun a _ => ?_
  have h := φ.re_apply_nonneg (star_mul_self_nonneg (L.effect a - R.effect a))
  rw [star_sub, (L.nonneg a).isSelfAdjoint.star_eq, (R.nonneg a).isSelfAdjoint.star_eq,
    sub_mul, mul_sub, mul_sub, ← (hcomm a).eq] at h
  simp only [map_sub, Complex.sub_re] at h
  linarith only [h, hsq a]

/-- Relabeling both commuting measurements by the same function can only increase
the probability that their outcomes match. -/
theorem agreement_le_agreement_map {β : Type*} [Fintype β] [DecidableEq β]
    (φ : AlgState A) (P Q : Measurement α A) (f : α → β)
    (hcomm : ∀ a b, Commute (P.effect a) (Q.effect b)) :
    agreement φ P Q ≤ agreement φ (P.map f) (Q.map f) := by
  rw [agreement_map_map, agreement]
  refine sum_le_sum fun a _ => ?_
  refine le_trans ?_ (single_le_sum (f := fun b =>
    if f a = f b then (φ (P.effect a * Q.effect b)).re else 0) (fun b _ => ?_) (mem_univ a))
  · simp
  · exact ite_nonneg (φ.re_apply_nonneg ((hcomm a b).mul_nonneg (P.nonneg a) (Q.nonneg b))) le_rfl

/-- Replacing one measurement changes its agreement with a fixed measurement by
at most the square root of the state-dependent squared distance. -/
theorem abs_agreement_sub_right_le (φ : AlgState A) (P Q R : Measurement α A) :
    |agreement φ P Q - agreement φ P R| ≤
      √(∑ a, φ.norm (Q.effect a - R.effect a) ^ 2) := by
  have hP : (∑ a, φ.norm (P.effect a) ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ a, (φ (P.effect a)).re := sum_le_sum fun a _ => by
        rw [AlgState.norm_sq, (P.nonneg a).isSelfAdjoint.star_eq]
        exact φ.re_apply_mono (P.effect_mul_self_le a)
      _ = 1 := P.sum_prob φ
  calc
    _ = |∑ a, (φ (star (P.effect a) * (Q.effect a - R.effect a))).re| := by
      simp only [agreement, (P.nonneg _).isSelfAdjoint.star_eq, mul_sub, map_sub,
        Complex.sub_re, sum_sub_distrib]
    _ ≤ √(∑ a, φ.norm (P.effect a) ^ 2) *
        √(∑ a, φ.norm (Q.effect a - R.effect a) ^ 2) :=
      φ.abs_sum_re_star_mul_le P.effect _
    _ ≤ _ := by
      simpa only [Real.sqrt_one, one_mul] using
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hP) (Real.sqrt_nonneg _)

/-- Successful mass changes by at most the state norm of the difference of
the two failure effects. -/
theorem abs_successfulMass_sub_le (φ : AlgState A) (P Q : Measurement (Option α) A) :
    |(φ P.successfulEffect).re - (φ Q.successfulEffect).re| ≤
      φ.norm (Q.effect none - P.effect none) := by
  have h := (Complex.abs_re_le_norm (φ (Q.effect none - P.effect none))).trans
    (φ.norm_apply_le_norm (Q.effect none - P.effect none))
  rw [Q.effect_none_eq_one_sub_successfulEffect, P.effect_none_eq_one_sub_successfulEffect,
    sub_sub_sub_cancel_left, map_sub, Complex.sub_re] at h
  simpa only [Q.effect_none_eq_one_sub_successfulEffect, P.effect_none_eq_one_sub_successfulEffect,
    sub_sub_sub_cancel_left] using h

/-- For two close measurements on one side, a measurement on the other side
that agrees with the original controls the distance after relabeling. The
bound is independent of the number of outcomes merged into each fiber. -/
theorem sum_norm_sub_sq_map_le_of_agreement {β : Type*} [Fintype β] [DecidableEq β]
    (φ : AlgState A) (L R P : Measurement α A) (f : α → β)
    (hLR : ∀ a b, Commute (L.effect a) (R.effect b))
    (hLP : ∀ a b, Commute (L.effect a) (P.effect b))
    {δ ρ : ℝ} (hag : 1 - δ ≤ agreement φ L R)
    (happrox : (∑ a, φ.norm (R.effect a - P.effect a) ^ 2) ≤ ρ) :
    ∑ b, φ.norm ((R.map f).effect b - (P.map f).effect b) ^ 2 ≤ 8 * δ + 4 * √ρ := by
  have hcross : 1 - (δ + √ρ) ≤ agreement φ L P := by
    have h := (abs_agreement_sub_right_le φ L R P).trans (Real.sqrt_le_sqrt happrox)
    linarith only [(abs_le.mp h).2, hag]
  have hR := sum_norm_sub_sq_le_of_agreement φ (L.map f) (R.map f)
    (fun b => commute_map_map L R hLR f f b b)
    (hag.trans (agreement_le_agreement_map φ L R f hLR))
  have hP := sum_norm_sub_sq_le_of_agreement φ (L.map f) (P.map f)
    (fun b => commute_map_map L P hLP f f b b)
    (hcross.trans (agreement_le_agreement_map φ L P f hLP))
  have hpoint (b : β) : φ.norm ((R.map f).effect b - (P.map f).effect b) ^ 2 ≤
      2 * (φ.norm ((L.map f).effect b - (R.map f).effect b) ^ 2 +
        φ.norm ((L.map f).effect b - (P.map f).effect b) ^ 2) := by
    let l := (L.map f).effect b
    let r := (R.map f).effect b
    let p := (P.map f).effect b
    change φ.norm (r - p) ^ 2 ≤ 2 * (φ.norm (l - r) ^ 2 + φ.norm (l - p) ^ 2)
    rw [show r - p = (r - l) + (l - p) by abel]
    refine (pow_le_pow_left₀ (φ.norm_nonneg _) (φ.norm_add_le (r - l) (l - p)) 2).trans ?_
    rw [φ.norm_sub_comm r l]
    nlinarith only [sq_nonneg (φ.norm (l - r) - φ.norm (l - p))]
  refine (sum_le_sum fun b _ => hpoint b).trans ?_
  rw [← mul_sum, sum_add_distrib]
  linarith only [hR, hP]

end Cslib.Quantum.Measurement

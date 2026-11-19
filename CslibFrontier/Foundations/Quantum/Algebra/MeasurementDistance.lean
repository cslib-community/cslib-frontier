/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

/-!
# State-dependent bounds for measurement distributions

Inserting all effects of a measurement between two families of operators gives a sum of
matrix coefficients bounded by the product of the families' state norms. In particular,
the bound has no factor for the number of outcomes of the inserted measurement. When
one family of projectors commutes with the state in its trace pairing, the same Cauchy–Schwarz
argument controls the error of replacing a second projective measurement.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset

variable {A α β : Type*} [Fintype α] [Fintype β] [Ring A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A] [SelfAdjointDecompose A]
  [TopologicalSpace A] [T2Space A] [IsSemitopologicalRing A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

omit [Fintype α] [Fintype β] [TopologicalSpace A] [T2Space A] [IsSemitopologicalRing A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A] in
private theorem sum_abs_re_apply_star_mul_le {γ : Type*} [Fintype γ] (φ : AlgState A)
    (u v : γ → A) :
    (∑ i, |(φ (star (u i) * v i)).re|) ≤
      √(∑ i, φ.norm (u i) ^ 2) * √(∑ i, φ.norm (v i) ^ 2) :=
  (sum_le_sum fun i _ => (Complex.abs_re_le_norm _).trans (φ.norm_apply_star_mul_le (u i) (v i)))
    |>.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

/-- Cauchy–Schwarz for a sum of coefficients weighted by the effects of a measurement. -/
theorem sum_abs_re_apply_star_mul_effect_mul_le (φ : AlgState A) (M : Measurement β A)
    (u v : α → A) :
    (∑ a, ∑ b, |(φ (star (u a) * M.effect b * v a)).re|) ≤
      √(∑ a, φ.norm (u a) ^ 2) * √(∑ a, φ.norm (v a) ^ 2) := by
  let R (b : β) := CFC.sqrt (M.effect b)
  have hR (b : β) : star (R b) * R b = M.effect b := by
    rw [(CFC.sqrt_nonneg (M.effect b)).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (M.nonneg b)
  have hnorm (w : α → A) :
      (∑ p : α × β, φ.norm (R p.2 * w p.1) ^ 2) = ∑ a, φ.norm (w a) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun a _ => ?_
    have heq (b : β) :
        star (R b * w a) * (R b * w a) = star (w a) * (M.effect b * w a) := by
      rw [star_mul, mul_assoc, ← mul_assoc (star (R b)), hR]
    simp only [AlgState.norm_sq, heq]
    rw [← Complex.re_sum, ← map_sum, ← mul_sum, ← sum_mul, M.sum_effect, one_mul]
  have hcoeff (a : α) (b : β) :
      star (R b * u a) * (R b * v a) = star (u a) * M.effect b * v a := by
    rw [star_mul, mul_assoc, ← mul_assoc (star (R b)), hR, mul_assoc]
  rw [← Fintype.sum_prod_type fun p : α × β => |(φ (star (u p.1) * M.effect p.2 * v p.1)).re|]
  rw [← hnorm u, ← hnorm v]
  simpa only [hcoeff] using
    sum_abs_re_apply_star_mul_le φ (fun p : α × β => R p.2 * u p.1) (fun p => R p.2 * v p.1)

/-- Replacing the operators on both sides of a measurement changes the resulting weights
by at most the state-norm distance of the replacement times the sum of the two norms. -/
theorem sum_abs_re_apply_conjugation_sub_le (φ : AlgState A) (M : Measurement β A)
    (u v : α → A) :
    (∑ a, ∑ b, |(φ (star (u a) * M.effect b * u a)).re -
        (φ (star (v a) * M.effect b * v a)).re|) ≤
      √(∑ a, φ.norm (u a - v a) ^ 2) *
        (√(∑ a, φ.norm (u a) ^ 2) + √(∑ a, φ.norm (v a) ^ 2)) := by
  let w : α → A := fun a => u a - v a
  have hdiff (a : α) (b : β) :
      (φ (star (u a) * M.effect b * u a)).re - (φ (star (v a) * M.effect b * v a)).re =
        (φ (star (u a) * M.effect b * w a)).re +
          (φ (star (w a) * M.effect b * v a)).re := by
    rw [← Complex.sub_re, ← Complex.add_re, ← map_sub, ← map_add]
    congr 2
    simp only [w, star_sub]
    noncomm_ring
  simp_rw [hdiff]
  change _ ≤ √(∑ a, φ.norm (w a) ^ 2) *
    (√(∑ a, φ.norm (u a) ^ 2) + √(∑ a, φ.norm (v a) ^ 2))
  calc
    _ ≤ ∑ a, ∑ b, (|(φ (star (u a) * M.effect b * w a)).re| +
          |(φ (star (w a) * M.effect b * v a)).re|) :=
      sum_le_sum fun a _ => sum_le_sum fun b _ => abs_add_le _ _
    _ ≤ _ := by
      simp only [sum_add_distrib, mul_add,
        mul_comm (√(∑ a, φ.norm (w a) ^ 2)) (√(∑ a, φ.norm (u a) ^ 2))]
      exact add_le_add (M.sum_abs_re_apply_star_mul_effect_mul_le φ u w)
        (M.sum_abs_re_apply_star_mul_effect_mul_le φ w v)

omit [T2Space A] [IsSemitopologicalRing A] in
private theorem sum_effect_norm_sq_le_one (φ : AlgState A) (P : Measurement α A) :
    (∑ a, φ.norm (P.effect a) ^ 2) ≤ 1 := by
  calc
    _ ≤ ∑ a, (φ (P.effect a)).re := by
      refine sum_le_sum fun a _ => φ.norm_sq_le_of_star_mul_le ?_
      rw [(P.nonneg a).isSelfAdjoint.star_eq]
      exact P.effect_mul_self_le a
    _ = 1 := by rw [← Complex.re_sum, ← map_sum, P.sum_effect, φ.map_one, Complex.one_re]

/-- Replacing one measurement inside a quadratic expression changes its weights by at
most twice the state-dependent distance between the two families of effects. -/
theorem sum_abs_re_apply_effect_conjugation_sub_le (φ : AlgState A) (M : Measurement β A)
    (P Q : Measurement α A) :
    (∑ a, ∑ b, |(φ (P.effect a * M.effect b * P.effect a)).re -
        (φ (Q.effect a * M.effect b * Q.effect a)).re|) ≤
      2 * √(∑ a, φ.norm (P.effect a - Q.effect a) ^ 2) := by
  have h := M.sum_abs_re_apply_conjugation_sub_le φ P.effect Q.effect
  have hP (a : α) := (P.nonneg a).isSelfAdjoint.star_eq
  have hQ (a : α) := (Q.nonneg a).isSelfAdjoint.star_eq
  simp_rw [hP, hQ] at h
  refine h.trans ?_
  rw [mul_comm 2]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  simpa only [Real.sqrt_one, one_add_one_eq_two] using add_le_add
    (Real.sqrt_le_sqrt (sum_effect_norm_sq_le_one φ P))
    (Real.sqrt_le_sqrt (sum_effect_norm_sq_le_one φ Q))

/-- A projective measurement commuting with `M` can be moved to the same side as `M`
with an error controlled by its distance from the replacement. -/
theorem sum_abs_re_apply_effect_mul_sub_conjugation_le (φ : AlgState A)
    (M : Measurement β A) (P Q : Measurement α A) (hP : P.IsProjective)
    (hcomm : ∀ a b, Commute (P.effect a) (M.effect b)) :
    (∑ a, ∑ b, |(φ (P.effect a * M.effect b)).re -
        (φ (Q.effect a * M.effect b * Q.effect a)).re|) ≤
      2 * √(∑ a, φ.norm (P.effect a - Q.effect a) ^ 2) := by
  have h (a : α) (b : β) :
      P.effect a * M.effect b * P.effect a = P.effect a * M.effect b := by
    rw [mul_assoc, (hcomm a b).symm.eq, ← mul_assoc, hP a]
  simpa only [h] using M.sum_abs_re_apply_effect_conjugation_sub_le φ P Q

omit [T2Space A] [IsSemitopologicalRing A] in
/-- If the projectors of `M` commute with the state in the trace pairing, changing a
projective second measurement changes the joint weights by at most twice its
state-dependent distance. The other two measurements may act on the same algebra as `M`. -/
theorem sum_abs_re_apply_mul_sub_mul_le_of_central (φ : AlgState A)
    (M : Measurement β A) (P Q : Measurement α A)
    (hM : M.IsProjective) (hP : P.IsProjective) (hQ : Q.IsProjective)
    (hcentral : ∀ b z, φ (M.effect b * z) = φ (z * M.effect b)) :
    (∑ a, ∑ b, |(φ (M.effect b * P.effect a)).re - (φ (M.effect b * Q.effect a)).re|) ≤
      2 * √(∑ a, φ.norm (P.effect a - Q.effect a) ^ 2) := by
  have hcut (b : β) (z : A) : φ (M.effect b * z * M.effect b) = φ (M.effect b * z) := by
    rw [mul_assoc, hcentral b (z * M.effect b), mul_assoc, hM b, hcentral b z]
  let D (a : α) := P.effect a - Q.effect a
  let restrict (w : α → A) (p : α × β) := w p.1 * M.effect p.2
  have hcoeff (u v : α → A) (a : α) (b : β) :
      φ (star (restrict u (a, b)) * restrict v (a, b)) =
        φ (M.effect b * (star (u a) * v a)) := by
    dsimp only [restrict]
    rw [star_mul, (M.nonneg b).isSelfAdjoint.star_eq]
    simpa only [mul_assoc] using hcut b (star (u a) * v a)
  have hnorm (w : α → A) :
      (∑ p, φ.norm (restrict w p) ^ 2) = ∑ a, φ.norm (w a) ^ 2 := by
    simp only [Fintype.sum_prod_type, AlgState.norm_sq, hcoeff]
    refine sum_congr rfl fun a _ => ?_
    rw [← Complex.re_sum, ← map_sum, ← sum_mul, M.sum_effect, one_mul]
  have hdiff (a : α) (b : β) :
      (φ (M.effect b * P.effect a)).re - (φ (M.effect b * Q.effect a)).re =
        (φ (star (restrict P.effect (a, b)) * restrict D (a, b))).re +
        (φ (star (restrict D (a, b)) * restrict Q.effect (a, b))).re := by
    rw [hcoeff, hcoeff, ← Complex.sub_re, ← Complex.add_re, ← map_sub, ← map_add]
    congr 2
    have hps : star (P.effect a) = P.effect a := (P.nonneg a).isSelfAdjoint.star_eq
    have hqs : star (Q.effect a) = Q.effect a := (Q.nonneg a).isSelfAdjoint.star_eq
    simp only [D, star_sub, hps, hqs, mul_sub, sub_mul, hP a, hQ a]
    abel
  have h₁ := sum_abs_re_apply_star_mul_le φ (restrict P.effect) (restrict D)
  have h₂ := sum_abs_re_apply_star_mul_le φ (restrict D) (restrict Q.effect)
  simp only [hnorm, Fintype.sum_prod_type] at h₁ h₂
  calc
    _ ≤ (∑ a, ∑ b, |(φ (star (restrict P.effect (a, b)) * restrict D (a, b))).re|) +
        ∑ a, ∑ b, |(φ (star (restrict D (a, b)) * restrict Q.effect (a, b))).re| := by
      simp only [← sum_add_distrib, hdiff]
      exact sum_le_sum fun a _ => sum_le_sum fun b _ => abs_add_le _ _
    _ ≤ _ := by
      refine (add_le_add h₁ h₂).trans ?_
      rw [mul_comm (√(∑ a, φ.norm (P.effect a) ^ 2)), ← mul_add, mul_comm 2]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      simpa only [Real.sqrt_one, one_add_one_eq_two] using add_le_add
        (Real.sqrt_le_sqrt (sum_effect_norm_sq_le_one φ P))
        (Real.sqrt_le_sqrt (sum_effect_norm_sq_le_one φ Q))

/-- Sequential weights are close to the product weights of two projective measurements
when the first replacement commutes with the state in the trace pairing. -/
theorem sum_abs_re_apply_conjugation_sub_mul_le_of_central (φ : AlgState A)
    (P Q : Measurement α A) (R T : Measurement β A) (hQ : Q.IsProjective)
    (hR : R.IsProjective) (hT : T.IsProjective)
    (hcentral : ∀ a z, φ (Q.effect a * z) = φ (z * Q.effect a)) :
    (∑ a, ∑ b, |(φ (P.effect a * R.effect b * P.effect a)).re -
        (φ (Q.effect a * T.effect b)).re|) ≤
      2 * √(∑ a, φ.norm (P.effect a - Q.effect a) ^ 2) +
        2 * √(∑ b, φ.norm (R.effect b - T.effect b) ^ 2) := by
  have hcut (a : α) (b : β) :
      φ (Q.effect a * R.effect b * Q.effect a) = φ (Q.effect a * R.effect b) := by
    rw [mul_assoc, hcentral a (R.effect b * Q.effect a), mul_assoc, hQ a,
      hcentral a (R.effect b)]
  have hx := R.sum_abs_re_apply_effect_conjugation_sub_le φ P Q
  simp only [hcut] at hx
  have hy := Q.sum_abs_re_apply_mul_sub_mul_le_of_central φ R T hQ hR hT hcentral
  rw [sum_comm] at hy
  refine le_trans ?_ (add_le_add hx hy)
  simp only [← sum_add_distrib]
  exact sum_le_sum fun a _ => sum_le_sum fun b _ => abs_sub_le _ _ _

end Cslib.Quantum.Measurement

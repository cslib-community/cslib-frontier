/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign.Rounding
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Words as sign vectors

A word `f : X → Bool` over a finite set of positions is read as the vector of signs
`signWord f = (signVal (f x))_x` in `EuclideanSpace ℝ X`. The inner product of two such vectors is
the sign correlation `∑ x, signVal (f x) * signVal (g x)` (`BitString.inner_signWord`), and each
has squared norm `|X|` (`BitString.norm_signWord_sq`). This lets inequalities for vectors in a
real inner product space, such as the Cauchy–Schwarz inequality, apply to Boolean words.

## Main definitions

* `Cslib.BitString.signWord`: the sign vector of a word.

## Main results

* `Cslib.BitString.inner_signWord`: inner products of sign vectors are sign correlations.
* `Cslib.BitString.norm_signWord_sq`: a sign vector has squared norm `|X|`.
* `Cslib.BitString.hammingDist_signRound_le_card_mul_norm_sub_sq`: Euclidean approximation
  to a normalized sign word bounds the number of rounding errors.
-/

public section

namespace Cslib.BitString

open scoped RealInnerProductSpace

variable {X : Type*} [Fintype X]

/-- The `±1` word of a Boolean function, as a vector of `EuclideanSpace ℝ X`. -/
@[expose] noncomputable def signWord (f : X → Bool) : EuclideanSpace ℝ X :=
  WithLp.toLp 2 fun x => signVal (f x)

omit [Fintype X] in
/-- Coordinates of the sign vector. -/
@[simp] theorem signWord_apply (f : X → Bool) (x : X) :
    signWord f x = signVal (f x) := rfl

omit [Fintype X] in
/-- Swapping both Boolean labels negates the sign vector. -/
@[simp] theorem signWord_not (f : X → Bool) :
    signWord (fun x => !(f x)) = -signWord f := by
  ext x
  simp

/-- The inner product of two sign vectors is the sign correlation of the words. -/
theorem inner_signWord (f g : X → Bool) :
    ⟪signWord f, signWord g⟫ = ∑ x, signVal (f x) * signVal (g x) := by
  simp [signWord, PiLp.inner_apply, mul_comm]

/-- A sign vector has squared norm `|X|`. -/
theorem norm_signWord_sq (f : X → Bool) : ‖signWord f‖ ^ 2 = Fintype.card X := by
  rw [← real_inner_self_eq_norm_sq, inner_signWord]
  simp [signVal_mul_self]

/-- The norm of a sign vector is the square root of its number of coordinates. -/
theorem norm_signWord (f : X → Bool) : ‖signWord f‖ = Real.sqrt (Fintype.card X) := by
  rw [← norm_signWord_sq f, Real.sqrt_sq (norm_nonneg _)]

/-- Coordinates of the normalized sign vector. -/
@[simp] theorem normalize_signWord_apply (f : X → Bool) (x : X) :
    NormedSpace.normalize (signWord f) x =
      (Real.sqrt (Fintype.card X))⁻¹ * signVal (f x) := by
  rw [NormedSpace.normalize, norm_signWord]
  rfl

/-- The rank-one matrix of a sign word acts by the domain cardinality times projection onto
its normalized direction. -/
theorem signWord_rankOne_apply [DecidableEq X] (g : X → Bool) (d : ℝ)
    (y : EuclideanSpace ℝ X) :
    (d • Matrix.vecMulVec (fun i => signVal (g i)) (fun i => signVal (g i))).toEuclideanLin y =
      ((d * Fintype.card X) * inner ℝ (NormedSpace.normalize (signWord g)) y) •
        NormedSpace.normalize (signWord g) := by
  have hsign : signWord g = Real.sqrt (Fintype.card X : ℝ) •
        NormedSpace.normalize (signWord g) := by
    simpa only [norm_signWord] using
      (NormedSpace.norm_smul_normalize (signWord g)).symm
  have houter := InnerProductSpace.symm_toEuclideanLin_rankOne (signWord g) (signWord g)
  simp only [star_trivial] at houter
  have happly : (Matrix.vecMulVec (fun i => signVal (g i))
      (fun i => signVal (g i))).toEuclideanLin y =
      inner ℝ (signWord g) y • signWord g := by
    change (Matrix.vecMulVec (signWord g) (signWord g)).toEuclideanLin y = _
    rw [← houter, LinearEquiv.apply_symm_apply]
    rfl
  rw [map_smul, LinearMap.smul_apply, happly]
  conv_lhs => rw [hsign, real_inner_smul_left, smul_smul, smul_smul]
  congr 1
  calc
    d * (Real.sqrt (Fintype.card X : ℝ) *
        inner ℝ (NormedSpace.normalize (signWord g)) y) * Real.sqrt (Fintype.card X : ℝ) =
        d * (Real.sqrt (Fintype.card X : ℝ)) ^ 2 *
          inner ℝ (NormedSpace.normalize (signWord g)) y := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg (Fintype.card X))]

/-- Positive normalization preserves every rounded sign, including the zero vector. -/
@[simp] theorem signRound_normalize (x : EuclideanSpace ℝ X) :
    signRound (NormedSpace.normalize x : EuclideanSpace ℝ X) = signRound x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hp : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx)
    funext i
    change decide (‖x‖⁻¹ * x i < 0) = decide (x i < 0)
    simp only [show (‖x‖⁻¹ * x i < 0) ↔ x i < 0 by
      simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hp :
        ‖x‖⁻¹ * x i < ‖x‖⁻¹ * 0 ↔ x i < 0)]

/-- Rounding an approximation to a normalized sign word makes at most the domain cardinality
times its squared Euclidean error in mistakes. -/
theorem hammingDist_signRound_le_card_mul_norm_sub_sq
    (f : X → Bool) (x : EuclideanSpace ℝ X) :
    (hammingDist (signRound x) f : ℝ) ≤
      Fintype.card X * ‖x - NormedSpace.normalize (signWord f)‖ ^ 2 := by
  by_cases hzero : Fintype.card X = 0
  · have : IsEmpty X := Fintype.card_eq_zero_iff.mp hzero
    simp [hammingDist]
  have h := sq_mul_hammingDist_signRound_le_sum_sq_sub f x
    (a := (Real.sqrt (Fintype.card X))⁻¹) (by positivity)
  have heq : ‖x - NormedSpace.normalize (signWord f)‖ ^ 2 =
      ∑ i, (x i - (Real.sqrt (Fintype.card X))⁻¹ * signVal (f i)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.sub_apply, normalize_signWord_apply]
  rw [← heq] at h
  have hcard : (Fintype.card X : ℝ) * (Real.sqrt (Fintype.card X))⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hzero)]
  simpa only [← mul_assoc, hcard, one_mul] using
    mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card X))

end Cslib.BitString

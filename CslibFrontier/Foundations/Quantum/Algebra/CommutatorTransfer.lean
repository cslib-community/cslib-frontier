/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.PrefixCommutator

/-!
# Transferring commutation through approximating measurements

Two measurements on one side approximately commute if their approximating measurements
on the other side commute exactly. The comparison depends on the squared state distances
to the approximating measurements and uses projectivity to sum over the other outcome.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset

variable {A α β : Type*} [Fintype α] [Fintype β]
  [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

/-- Transfer commutation from two commuting measurements to their approximations on the
other side. Exact cross-commutation is enough for the two products in the comparison. -/
theorem pairCommutatorDefect_le_of_commuting_copies (φ : AlgState A)
    (P R : Measurement α A) (Q T : Measurement β A)
    (hP : P.IsProjective) (hQ : Q.IsProjective) (hR : R.IsProjective) (hT : T.IsProjective)
    (hPT : ∀ a b, Commute (P.effect a) (T.effect b))
    (hRQ : ∀ a b, Commute (R.effect a) (Q.effect b))
    (hRT : ∀ a b, Commute (R.effect a) (T.effect b)) :
    pairCommutatorDefect φ P Q ≤ 8 * (copyDefect φ P R + copyDefect φ Q T) := by
  let X (a : α) (b : β) := P.effect a * (Q.effect b - T.effect b)
  let Y (a : α) (b : β) := T.effect b * (P.effect a - R.effect a)
  let Z (a : α) (b : β) := R.effect a * (T.effect b - Q.effect b)
  let W (a : α) (b : β) := Q.effect b * (R.effect a - P.effect a)
  have h (a : α) (b : β) :
      φ.norm (P.effect a * Q.effect b - Q.effect b * P.effect a) ^ 2 ≤
        4 * (φ.norm (X a b) ^ 2 + φ.norm (Y a b) ^ 2 +
          φ.norm (Z a b) ^ 2 + φ.norm (W a b) ^ 2) := by
    have he : P.effect a * Q.effect b - Q.effect b * P.effect a =
        (X a b + Y a b) + (Z a b + W a b) := by
      simp only [X, Y, Z, W, mul_sub, (hPT a b).eq, (hRT a b).eq, (hRQ a b).eq]
      abel
    rw [he]
    linarith [φ.norm_add_sq_le (X a b + Y a b) (Z a b + W a b),
      φ.norm_add_sq_le (X a b) (Y a b), φ.norm_add_sq_le (Z a b) (W a b)]
  have hX : (∑ a, ∑ b, φ.norm (X a b) ^ 2) = copyDefect φ Q T := by
    unfold X copyDefect
    rw [sum_comm]
    simp only [sum_norm_effect_mul_sq φ P hP]
  have hY : (∑ a, ∑ b, φ.norm (Y a b) ^ 2) = copyDefect φ P R := by
    simp only [Y, copyDefect, sum_norm_effect_mul_sq φ T hT]
  have hZ : (∑ a, ∑ b, φ.norm (Z a b) ^ 2) = copyDefect φ Q T := by
    unfold Z copyDefect
    rw [sum_comm]
    simp only [sum_norm_effect_mul_sq φ R hR, φ.norm_sub_comm (T.effect _)]
  have hW : (∑ a, ∑ b, φ.norm (W a b) ^ 2) = copyDefect φ P R := by
    simp only [W, copyDefect, sum_norm_effect_mul_sq φ Q hQ, φ.norm_sub_comm (R.effect _)]
  unfold pairCommutatorDefect
  refine (sum_le_sum fun a _ => sum_le_sum fun b _ => h a b).trans_eq ?_
  simp only [← mul_sum, sum_add_distrib, hX, hY, hZ, hW]
  ring

end Cslib.Quantum.Measurement

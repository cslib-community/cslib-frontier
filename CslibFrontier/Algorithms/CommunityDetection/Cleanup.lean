/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign.Rounding
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correcting approximate community labels by a weighted vote

Given a real matrix `M` and Boolean labels `h`, `cleanup M h` takes the sign of each row's
weighted vote against `h`. When all matrix entries have absolute value at most `C`, changing
`m` labels changes each vote by at most `2 C m`. Consequently a true-label row margin exceeding
`2 C m` corrects all the errors in one step.

The estimate is deterministic. In particular, the approximate labels may depend on the same
matrix used for cleanup; no independence or additional sample is needed by this step.

## Main results

* `Cslib.Algorithms.CommunityDetection.cleanup_eq_of_margin`: row margins correct label errors.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Finset BitString

variable {α : Type*} [Fintype α]

/-- Improve Boolean labels by the sign of each row's weighted vote. Negative votes produce
`true`; zero votes produce `false`. -/
noncomputable def cleanup (M : Matrix α α ℝ) (h : α → Bool) : α → Bool :=
  signRound (M.mulVec (fun j => signVal (h j)))

/-- Each output label records whether its weighted row vote is negative. -/
@[simp] theorem cleanup_apply (M : Matrix α α ℝ) (h : α → Bool) (i : α) :
    cleanup M h i = decide ((∑ j, M i j * signVal (h j)) < 0) := by
  simp [cleanup, signRound, Matrix.mulVec, dotProduct]

private theorem abs_vote_sub_le (w : α → ℝ) (h g : α → Bool) {C : ℝ} (hw : ∀ j, |w j| ≤ C) :
    |∑ j, w j * signVal (h j) - ∑ j, w j * signVal (g j)| ≤
      2 * C * (hammingDist h g : ℝ) := by
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [hammingDist, card_filter, Nat.cast_sum, Finset.mul_sum]
  refine sum_le_sum fun j _ => ?_
  by_cases hj : h j = g j
  · simp [hj]
  · have hs : |signVal (h j) - signVal (g j)| = 2 := by
      cases hh : h j <;> cases hg : g j <;> simp_all <;> norm_num
    rw [ite_eq_left hj]
    simp only [Nat.cast_one, mul_one, ← mul_sub, abs_mul, hs]
    nlinarith [hw j]

/-- A deterministic cleanup step: if the true-label margin in each row exceeds twice the
entry bound times the number of erroneous input labels, all labels are recovered. -/
theorem cleanup_eq_of_margin {M : Matrix α α ℝ} {h g : α → Bool} {C : ℝ}
    (hM : ∀ i j, |M i j| ≤ C)
    (hmargin : ∀ i, 2 * C * (hammingDist h g : ℝ) <
      signVal (g i) * ∑ j, M i j * signVal (g j)) :
    cleanup M h = g := by
  funext i
  have he := abs_vote_sub_le (M i) h g (hM i)
  have hm := hmargin i
  change decide ((∑ j, M i j * signVal (h j)) < 0) = g i
  cases hg : g i
  · simp only [hg, signVal_false, one_mul] at hm
    have hnonneg : 0 ≤ ∑ j, M i j * signVal (h j) := by
      linarith [(abs_le.mp he).1]
    simp [hnonneg.not_gt]
  · simp only [hg, signVal_true, neg_one_mul] at hm
    have hnegative : (∑ j, M i j * signVal (h j)) < 0 := by
      linarith [(abs_le.mp he).2]
    simp [hnegative]

end Cslib.Algorithms.CommunityDetection

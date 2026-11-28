/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
public import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Agreement under randomized outcome relabeling

When a random relabeling seldom identifies distinct outcomes, it can only
increase the agreement probability by the collision bound.
-/

public section

namespace Cslib.Quantum.Measurement

open Finset
open scoped BigOperators

variable {A α β X : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Fintype X]
  [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-- On average, relabeling both measurements raises agreement by at most the
largest collision probability for distinct original outcomes. -/
theorem expect_agreement_map_le [Nonempty X] (φ : AlgState A) (P Q : Measurement α A)
    (f : X → α → β) (hcomm : ∀ a b, Commute (P.effect a) (Q.effect b))
    {c : ℝ} (hc : 0 ≤ c)
    (hcollision : ∀ a b, a ≠ b → (𝔼 x, if f x a = f x b then (1 : ℝ) else 0) ≤ c) :
    (𝔼 x, agreement φ (P.map (f x)) (Q.map (f x))) ≤ agreement φ P Q + c := by
  classical
  let w (a b : α) := (φ (P.effect a * Q.effect b)).re
  have hw (a b : α) : 0 ≤ w a b :=
    φ.re_apply_nonneg ((hcomm a b).mul_nonneg (P.nonneg a) (Q.nonneg b))
  have htotal : (∑ a, ∑ b, w a b) = 1 := sum_re_effect_mul_effect φ P Q
  have hcoef (a b : α) :
      (𝔼 x, if f x a = f x b then w a b else 0) ≤ (if a = b then w a b else 0) + c * w a b := by
    rcases eq_or_ne a b with rfl | he
    · simpa [Fintype.expect_const] using mul_nonneg hc (hw a a)
    · rw [expect_congr rfl fun x _ => (boole_mul (f x a = f x b) (w a b)).symm, ← expect_mul,
        ite_eq_right he, zero_add]
      exact mul_le_mul_of_nonneg_right (hcollision a b he) (hw a b)
  simp only [agreement_map_map, expect_sum_comm]
  calc
    _ ≤ ∑ a, ∑ b, ((if a = b then w a b else 0) + c * w a b) :=
      sum_le_sum fun a _ => sum_le_sum fun b _ => hcoef a b
    _ = _ := by
      simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, htotal, mul_one,
        agreement, w]

end Cslib.Quantum.Measurement

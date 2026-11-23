/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, variance on finite product spaces)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Foundations.Probability.EfronStein
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate resampling for inner-product-valued functions

The squared-distance form of Efron–Stein extends to functions into a real inner
product space by applying the scalar inequality in a basis of the span of the
finite image. Equivalently, the global variance is at most the number of
coordinates times the variance under uniform single-coordinate resampling.

## Main results

* `Fintype.expect_expect_norm_sub_sq_le_sum_expect_expect_norm_sub_update_sq`.
-/

public section

open Finset Function
open scoped BigOperators

namespace Fintype

private theorem expect_expect_norm_sub_sq_le_two {A E : Type*}
    [Fintype A] [Nonempty A] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] (f : A → E) :
    (𝔼 u, 𝔼 v, ‖f u - f v‖ ^ 2) ≤ 2 * (𝔼 u, ‖f u‖ ^ 2) := by
  have hi : 0 ≤ (𝔼 u, 𝔼 v, inner ℝ (f u) (f v)) := by
    rw [Fintype.expect_eq_sum_div_card]
    refine div_nonneg ?_ (by positivity)
    simp only [Fintype.expect_eq_sum_div_card, ← sum_div, ← inner_sum, ← sum_inner]
    exact div_nonneg real_inner_self_nonneg (by positivity)
  simp only [norm_sub_sq_real, expect_add_distrib, expect_sub_distrib, Fintype.expect_const,
    ← mul_expect]
  linarith only [hi]

/-- A function constant along an update fiber bounds the squared change from
resampling that fiber, with a factor of two from the two independent samples. -/
theorem expect_expect_norm_sub_update_sq_le_two {I A E : Type*}
    [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (i : I) (f g : (I → A) → E) (hg : ∀ u a, g (update u i a) = g u) :
    (𝔼 u, 𝔼 a, ‖f (update u i a) - f u‖ ^ 2) ≤ 2 * (𝔼 u, ‖f u - g u‖ ^ 2) := by
  let p (u : I → A) := 𝔼 a, ‖f (update u i a) - f u‖ ^ 2
  let q (u : I → A) := ‖f u - g u‖ ^ 2
  change (𝔼 u, p u) ≤ 2 * (𝔼 u, q u)
  rw [← expect_expect_update p i, ← expect_expect_update q i, mul_expect]
  refine expect_le_expect fun u _ => ?_
  simp only [p, q, update_idem, hg]
  have hf (a b : A) : f (update u i b) - f (update u i a) =
      (f (update u i b) - g u) - (f (update u i a) - g u) := by abel
  simp only [hf]
  rw [expect_comm]
  exact expect_expect_norm_sub_sq_le_two (fun a => f (update u i a) - g u)

/-- Mean squared distance of two independent uniform tuples is at most the sum of
the mean squared changes on independently resampling each coordinate. -/
theorem expect_expect_norm_sub_sq_le_sum_expect_expect_norm_sub_update_sq
    {A E : Type*} [Fintype A] [Nonempty A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (f : (Fin n → A) → E) :
    (𝔼 u, 𝔼 v, ‖f u - f v‖ ^ 2) ≤ ∑ i, 𝔼 u, 𝔼 a, ‖f u - f (update u i a)‖ ^ 2 := by
  let V := Submodule.span ℝ (Set.range f)
  let : Module.Finite ℝ V := Module.Finite.span_of_finite _ (Set.finite_range f)
  let b := stdOrthonormalBasis ℝ V
  let g (u : Fin n → A) : V := ⟨f u, Submodule.subset_span ⟨u, rfl⟩⟩
  let c (i : Fin (Module.finrank ℝ V)) (u : Fin n → A) : ℝ := inner ℝ (b i) (g u)
  have h (u v : Fin n → A) : ‖f u - f v‖ ^ 2 = ∑ i, (c i u - c i v) ^ 2 := by
    change ‖g u - g v‖ ^ 2 = _
    rw [← b.sum_sq_norm_inner_right]
    simp only [inner_sub_right, c, Real.norm_eq_abs, sq_abs]
  simp only [h, expect_sum_comm]
  rw [sum_comm]
  exact sum_le_sum fun i _ => expect_expect_sq_sub_le_sum_expect_expect_sq_sub_update (c i)

end Fintype

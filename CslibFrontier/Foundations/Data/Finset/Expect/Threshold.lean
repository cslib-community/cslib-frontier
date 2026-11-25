/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.Expect
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Threshold cuts and real-valued distances

For two finite families of ordered pairs, a first-moment comparison for every placement into a
space with two points at positive distance implies the same comparison for every real-valued
placement. At a threshold `t`, the two sides of the cut are placed at the two points. The set
of thresholds separating two real numbers has length equal to their distance.
-/

public section

open Finset MeasureTheory Set
open scoped BigOperators

private noncomputable def crossing (a b : ℝ) : ℝ → ℝ := (uIoc b a).indicator 1

private lemma integrable_crossing (a b : ℝ) : Integrable (crossing a b) :=
  (integrable_indicator_iff measurableSet_uIoc).2
    (integrableOn_const (by simp [Real.volume_uIoc]))

private lemma integral_crossing (a b : ℝ) : ∫ t, crossing a b t = |a - b| := by
  rw [crossing, integral_indicator_one measurableSet_uIoc, measureReal_def, Real.volume_uIoc,
    ENNReal.toReal_ofReal (abs_nonneg _)]

private lemma integrable_expect_crossing {I : Type*} [Fintype I] (a b : I → ℝ) :
    Integrable (fun t => 𝔼 i, crossing (a i) (b i) t) := by
  simp only [expect_eq_sum_div_card]
  exact (integrable_finsetSum univ fun i _ => integrable_crossing (a i) (b i)).div_const _

private lemma integral_expect_crossing {I : Type*} [Fintype I] (a b : I → ℝ) :
    (∫ t, 𝔼 i, crossing (a i) (b i) t) = 𝔼 i, |a i - b i| := by
  simp only [expect_eq_sum_div_card, integral_div,
    integral_finsetSum univ fun i _ => integrable_crossing (a i) (b i), integral_crossing]

/-- Comparing the mean distances of two finite families of pairs for every placement into
`X` also compares their mean distances on the real line. Two points of `X` at positive
distance suffice. -/
theorem Fintype.expect_abs_sub_le_of_forall_expect_dist_le {V I J X : Type*}
    [Fintype I] [Fintype J] [PseudoMetricSpace X] (a b : I → V) (c d : J → V)
    {K : ℝ} (h : ∀ f : V → X, (𝔼 i, dist (f (a i)) (f (b i))) ≤
      K * 𝔼 j, dist (f (c j)) (f (d j))) {x y : X} (hxy : 0 < dist x y) (u : V → ℝ) :
    (𝔼 i, |u (a i) - u (b i)|) ≤ K * 𝔼 j, |u (c j) - u (d j)| := by
  have hcut (t : ℝ) : (𝔼 i, crossing (u (a i)) (u (b i)) t) ≤
      K * 𝔼 j, crossing (u (c j)) (u (d j)) t := by
    let f (v : V) := if t ≤ u v then x else y
    have hf (v w : V) : dist (f v) (f w) = dist x y * crossing (u v) (u w) t := by
      by_cases hv : t ≤ u v <;> by_cases hw : t ≤ u w <;>
        simp [f, crossing, mem_uIoc, ← not_le, hv, hw, dist_comm y x]
    have hh := h f
    simp only [hf, ← mul_expect] at hh
    rw [mul_left_comm K] at hh
    exact (mul_le_mul_iff_right₀ hxy).1 hh
  have hint := integral_mono (integrable_expect_crossing (u ∘ a) (u ∘ b))
    ((integrable_expect_crossing (u ∘ c) (u ∘ d)).const_mul K) hcut
  simpa only [integral_const_mul, integral_expect_crossing, Function.comp_apply] using hint

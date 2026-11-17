/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
public import Mathlib.Analysis.CStarAlgebra.Matrix
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Foundations.Analysis.Normed.FiniteNet
import Mathlib.Tactic.Linarith

/-!
# Finite-net bounds for random operator norms

Two half-nets of the Euclidean unit ball turn a uniform tail bound for the bilinear forms of a
random matrix into a tail bound for its operator norm. This probability step is independent of
the matrix's distribution and its entry representation.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_opNorm_gt_le_of_inner_tail`: the finite-net union bound.
-/

public section

open Finset

namespace Cslib.Probability.PMF

/-- If every bilinear form on the unit ball has tail probability at most `b` at threshold `r`,
the operator norm exceeds `4 r` with probability at most `25 ^ n * b`. -/
theorem toOuterMeasure_opNorm_gt_le_of_inner_tail {Ω : Type*} {n : ℕ}
    (p : PMF Ω) (M : Ω → Matrix (Fin n) (Fin n) ℝ) {r b : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b)
    (htail : ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      (p.toOuterMeasure {ω | r ≤ |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) y|}).toReal
        ≤ b) :
    (p.toOuterMeasure {ω | 4 * r < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖}).toReal ≤
      (25 : ℝ) ^ n * b := by
  classical
  obtain ⟨s, hcard, hs, hnet⟩ := NormedSpace.exists_halfNet (EuclideanSpace ℝ (Fin n))
  have hcard' : (s.card : ℝ) ≤ (5 : ℝ) ^ n := by
    have h : s.card ≤ 5 ^ n := by simpa only [finrank_euclideanSpace_fin] using hcard
    exact_mod_cast h
  let D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → Set Ω :=
    fun x y => {ω | r ≤ |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) y|}
  let B : Set Ω := ⋃ x ∈ s, ⋃ y ∈ s, D x y
  have hsub : {ω | 4 * r < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖} ⊆ B := by
    intro ω hω
    by_contra hnot
    have hall : ∀ x ∈ s, ∀ y ∈ s,
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) y| ≤ r := by
      intro x hx y hy
      have hxy : ω ∉ D x y := by
        intro hxy
        exact hnot (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx,
          Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, hxy⟩⟩⟩⟩)
      exact (not_le.mp hxy).le
    exact (not_lt_of_ge (ContinuousLinearMap.opNorm_le_four_mul_of_halfNet
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)) s s hnet hnet hr hall)) hω
  have hunion : (p.toOuterMeasure B).toReal ≤
      ∑ x ∈ s, ∑ y ∈ s, (p.toOuterMeasure (D x y)).toReal :=
    (toOuterMeasure_toReal_biUnion_finset_le p s _).trans
      (sum_le_sum fun _ _ => toOuterMeasure_toReal_biUnion_finset_le p s _)
  calc
    (p.toOuterMeasure {ω | 4 * r < ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖}).toReal
        ≤ (p.toOuterMeasure B).toReal :=
      ENNReal.toReal_mono (toOuterMeasure_ne_top p B) (MeasureTheory.measure_mono hsub)
    _ ≤ ∑ _x ∈ s, ∑ _y ∈ s, b := hunion.trans
      (sum_le_sum fun x hx => sum_le_sum fun y hy => htail x y (hs x hx) (hs y hy))
    _ = (s.card : ℝ) * (s.card : ℝ) * b := by simp; ring
    _ ≤ (5 : ℝ) ^ n * 5 ^ n * b := by gcongr
    _ = (25 : ℝ) ^ n * b := by rw [← mul_pow]; norm_num

end Cslib.Probability.PMF

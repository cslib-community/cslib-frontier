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

A single finite net of the Euclidean unit ball turns a uniform tail bound for the quadratic
forms of a random symmetric matrix into a tail bound for its operator norm. This probability
step is independent of the matrix's distribution and its entry representation.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_opNorm_gt_le_of_quadratic_tail`: the finite-net union bound.
-/

public section

open Finset

namespace Cslib.Probability.PMF

/-- If every quadratic form on the unit ball has tail probability at most `b` at threshold `t`,
a symmetric operator exceeds `t / (1 - 2 / q)` with probability at most `(2 q + 1) ^ n * b`.
The finite net has radius `1 / q`, with `q > 2`. -/
theorem toOuterMeasure_opNorm_gt_le_of_quadratic_tail {Ω : Type*} {n : ℕ}
    (p : PMF Ω) (M : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hsymm : ∀ ω, (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)).toLinearMap.IsSymmetric)
    {q : ℕ} (hq : 2 < q) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b)
    (htail : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 →
      (p.toOuterMeasure {ω | t ≤ |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) x|}).toReal
        ≤ b) :
    (p.toOuterMeasure {ω | t / (1 - 2 / (q : ℝ)) <
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖}).toReal ≤ (2 * q + 1 : ℝ) ^ n * b := by
  classical
  obtain ⟨s, hcard, hs, hnet⟩ :=
    NormedSpace.exists_natInverseNet (EuclideanSpace ℝ (Fin n)) q (by omega)
  have hcard' : (s.card : ℝ) ≤ (2 * q + 1 : ℝ) ^ n := by
    have h : s.card ≤ (2 * q + 1) ^ n := by
      simpa only [finrank_euclideanSpace_fin] using hcard
    exact_mod_cast h
  have hq' : (2 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hε : (1 : ℝ) / q < 1 / 2 := (div_lt_iff₀ hqpos).2 (by linarith)
  let D : EuclideanSpace ℝ (Fin n) → Set Ω :=
    fun x => {ω | t ≤ |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) x|}
  let B : Set Ω := ⋃ x ∈ s, D x
  have hsub : {ω | t / (1 - 2 / (q : ℝ)) <
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖} ⊆ B := by
    intro ω hω
    by_contra hnot
    have hall : ∀ x ∈ s,
        |inner ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω) x) x| ≤ t := by
      intro x hx
      have hx' : ω ∉ D x := by
        intro hx'
        exact hnot (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, hx'⟩⟩)
      exact (not_le.mp hx').le
    have hnorm := (Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)).opNorm_le_of_quadratic_net
      (hsymm ω) s (by positivity) hε ht hs hnet hall
    rw [show 1 - 2 * ((1 : ℝ) / q) = 1 - 2 / (q : ℝ) by ring] at hnorm
    exact (not_lt_of_ge hnorm) hω
  have hunion : (p.toOuterMeasure B).toReal ≤ ∑ x ∈ s, (p.toOuterMeasure (D x)).toReal :=
    toOuterMeasure_toReal_biUnion_finset_le p s _
  calc
    (p.toOuterMeasure {ω | t / (1 - 2 / (q : ℝ)) <
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M ω)‖}).toReal
        ≤ (p.toOuterMeasure B).toReal :=
      ENNReal.toReal_mono (toOuterMeasure_ne_top p B) (MeasureTheory.measure_mono hsub)
    _ ≤ ∑ _x ∈ s, b := hunion.trans (sum_le_sum fun x hx => htail x (hs x hx))
    _ = (s.card : ℝ) * b := by simp
    _ ≤ (2 * q + 1 : ℝ) ^ n * b := mul_le_mul_of_nonneg_right hcard' hb

end Cslib.Probability.PMF

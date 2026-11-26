/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Vertex
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Basic feasible vertices and extreme points over `ℝ`

Equates the algebraic vertex predicate `Matrix.IsVertex` for a finite real linear inequality
system `{y : α → ℝ | A *ᵥ y ≤ b}` with the convex-geometric `Set.extremePoints ℝ`.

## Main results

* `Matrix.isVertex_iff_mem_extremePoints_real`: `Matrix.IsVertex A b x` holds iff `x` is an
  extreme point of `{y : α → ℝ | A *ᵥ y ≤ b}`.
-/

public section

open Finset

namespace Matrix

/-- For any finite inequality system `A *ᵥ x ≤ b` over `ℝ`, basic feasible vertices
(`Matrix.IsVertex A b x`) coincide with convex-geometric extreme points of `{y | A *ᵥ y ≤ b}`. -/
theorem isVertex_iff_mem_extremePoints_real {κ α : Type*} [Fintype κ] [Fintype α]
    (A : Matrix κ α ℝ) (b : κ → ℝ) (x : α → ℝ) :
    IsVertex A b x ↔ x ∈ ({y : α → ℝ | A *ᵥ y ≤ b}).extremePoints ℝ := by
  classical
  rw [isVertex_iff]
  constructor
  · rintro ⟨hx, htight⟩
    refine ⟨hx, fun x₁ hx₁ x₂ hx₂ ⟨s, t, hs, ht, hst, hxst⟩ => ?_⟩
    obtain rfl : t = 1 - s := by linarith
    refine sub_eq_zero.1 (htight (x₁ - x) fun k hk => ?_)
    have hkx : (A *ᵥ x) k = b k := mem_tightRows.1 hk
    have hmul := congrFun (congrArg (A *ᵥ ·) hxst) k
    simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hmul
    have h1_zero : s * (b k - (A *ᵥ x₁) k) = 0 := by
      linarith [mul_nonneg hs.le (sub_nonneg.2 (hx₁ k)), mul_nonneg ht.le (sub_nonneg.2 (hx₂ k))]
    rw [mulVec_sub, Pi.sub_apply, hkx,
      ← sub_eq_zero.1 ((mul_eq_zero.1 h1_zero).resolve_left hs.ne'), sub_self]
  · rintro ⟨hx, hext⟩
    refine ⟨hx, fun v hv => ?_⟩
    by_contra hv0
    let slack : Finset κ := univ \ tightRows A b x
    let ε : ℝ :=
      if hne : slack.Nonempty then
        slack.inf' hne fun k => (b k - (A *ᵥ x) k) / (|(A *ᵥ v) k| + 1)
      else 1
    have hε : 0 < ε := by
      dsimp only [ε]
      split_ifs with hne
      · exact (lt_inf'_iff hne).2 fun k hk => div_pos
          (sub_pos.2 (lt_of_le_of_ne (hx k) fun h => (mem_sdiff.1 hk).2 (mem_tightRows.2 h)))
          (by positivity)
      · exact one_pos
    have hbound (k : κ) : ε * |(A *ᵥ v) k| ≤ b k - (A *ᵥ x) k := by
      by_cases htk : k ∈ tightRows A b x
      · simp [hv k htk, mem_tightRows.1 htk]
      · have hk : k ∈ slack := mem_sdiff.2 ⟨mem_univ k, htk⟩
        have hε_le : ε ≤ (b k - (A *ᵥ x) k) / (|(A *ᵥ v) k| + 1) :=
          (dite_eq_left (⟨k, hk⟩ : slack.Nonempty)).trans_le (inf'_le _ hk)
        linarith [(le_div_iff₀ (by positivity : (0 : ℝ) < |(A *ᵥ v) k| + 1)).1 hε_le]
    have hx₁ : A *ᵥ (x + ε • v) ≤ b := fun k ↦ by
      rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hbound k, mul_le_mul_of_nonneg_left (le_abs_self ((A *ᵥ v) k)) hε.le]
    have hx₂ : A *ᵥ (x - ε • v) ≤ b := fun k ↦ by
      rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hbound k, mul_le_mul_of_nonneg_left (neg_le_abs ((A *ᵥ v) k)) hε.le]
    have hseg : x ∈ openSegment ℝ (x + ε • v) (x - ε • v) := by
      refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      ring
    have heq : ε = 0 ∨ v = 0 := by simpa using hext hx₁ hx₂ hseg
    exact hv0 (heq.resolve_left hε.ne')

end Matrix

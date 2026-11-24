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
    have hfull : ∀ k ∈ tightRows A b x, (A *ᵥ (x₁ - x)) k = 0 := by
      intro k hk
      have hkx : (A *ᵥ x) k = b k := mem_tightRows.1 hk
      have hcomb : s * (b k - (A *ᵥ x₁) k) + t * (b k - (A *ᵥ x₂) k) = 0 := by
        have hmul : (A *ᵥ x) k = s * (A *ᵥ x₁) k + t * (A *ᵥ x₂) k := by
          rw [← hxst, mulVec_add, mulVec_smul, mulVec_smul]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc s * (b k - (A *ᵥ x₁) k) + t * (b k - (A *ᵥ x₂) k)
            = (s + t) * b k - (s * (A *ᵥ x₁) k + t * (A *ᵥ x₂) k) := by ring
          _ = 1 * b k - (A *ᵥ x) k := by rw [hst, hmul]
          _ = 0 := by rw [one_mul, hkx, sub_self]
      have h1_nonneg : 0 ≤ s * (b k - (A *ᵥ x₁) k) := mul_nonneg hs.le (sub_nonneg.2 (hx₁ k))
      have h2_nonneg : 0 ≤ t * (b k - (A *ᵥ x₂) k) := mul_nonneg ht.le (sub_nonneg.2 (hx₂ k))
      have h1_zero : s * (b k - (A *ᵥ x₁) k) = 0 :=
        le_antisymm (by linarith) h1_nonneg
      have hkx1 : (A *ᵥ x₁) k = b k := by
        rcases mul_eq_zero.1 h1_zero with hs0 | hsub0
        · exact absurd hs0 hs.ne'
        · exact (sub_eq_zero.1 hsub0).symm
      rw [mulVec_sub, Pi.sub_apply, hkx1, hkx, sub_self]
    exact sub_eq_zero.1 (htight (x₁ - x) hfull)
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
      · refine (Finset.lt_inf'_iff hne).2 fun k hk => ?_
        have hnot : k ∉ tightRows A b x := (mem_sdiff.1 hk).2
        have hlt : (A *ᵥ x) k < b k :=
          lt_of_le_of_ne (hx k) (fun h => hnot (mem_tightRows.2 h))
        exact div_pos (sub_pos.2 hlt) (by positivity)
      · exact one_pos
    have hbound : ∀ k, ε * |(A *ᵥ v) k| ≤ b k - (A *ᵥ x) k := by
      intro k
      by_cases htk : k ∈ tightRows A b x
      · have hv0k : (A *ᵥ v) k = 0 := hv k htk
        have hxk : (A *ᵥ x) k = b k := mem_tightRows.1 htk
        simp [hv0k, hxk]
      · have hkslack : k ∈ slack := mem_sdiff.2 ⟨mem_univ k, htk⟩
        have hne : slack.Nonempty := ⟨k, hkslack⟩
        have hε_le : ε ≤ (b k - (A *ᵥ x) k) / (|(A *ᵥ v) k| + 1) := by
          have hε_eq : ε = slack.inf' hne fun k => (b k - (A *ᵥ x) k) / (|(A *ᵥ v) k| + 1) := by
            simp only [ε, hne, ↓reduceDIte]
          rw [hε_eq]
          exact Finset.inf'_le _ hkslack
        have hden : 0 < |(A *ᵥ v) k| + 1 := by positivity
        have h1 : ε * (|(A *ᵥ v) k| + 1) ≤ b k - (A *ᵥ x) k :=
          (le_div_iff₀ hden).1 hε_le
        have h2 : ε * |(A *ᵥ v) k| ≤ ε * (|(A *ᵥ v) k| + 1) := by
          nlinarith [hε]
        linarith
    have hx₁ : A *ᵥ (x + ε • v) ≤ b := by
      intro k
      rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hab : ε * (A *ᵥ v) k ≤ ε * |(A *ᵥ v) k| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      linarith [hbound k]
    have hx₂ : A *ᵥ (x - ε • v) ≤ b := by
      intro k
      rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hab : -(ε * (A *ᵥ v) k) ≤ ε * |(A *ᵥ v) k| := by
        calc -(ε * (A *ᵥ v) k) = ε * (-(A *ᵥ v) k) := by ring
          _ ≤ ε * |(A *ᵥ v) k| := mul_le_mul_of_nonneg_left (neg_le_abs _) hε.le
      linarith [hbound k]
    have hseg : x ∈ openSegment ℝ (x + ε • v) (x - ε • v) := by
      refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      ring
    have heq := hext hx₁ hx₂ hseg
    have hεv : ε • v = 0 := by
      have : x + ε • v - x = 0 := by rw [heq, sub_self]
      simpa using this
    exact hv0 ((smul_eq_zero.1 hεv).resolve_left hε.ne')

end Matrix

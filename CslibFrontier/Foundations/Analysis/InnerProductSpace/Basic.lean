/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/InnerProductSpace/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Squared norm of a finite sum in a real inner product space

Expanding `‖∑ i ∈ s, f i‖ ^ 2 = ⟪∑ i ∈ s, f i, ∑ j ∈ s, f j⟫` separates the diagonal terms
`∑ i ∈ s, ‖f i‖ ^ 2` from the off-diagonal inner products `∑ p ∈ s.offDiag, ⟪f p.1, f p.2⟫`
(`norm_sum_sq_real`).

## Main results

* `norm_sum_sq_real`: the squared norm of a finite sum, expanded over the diagonal and the
  ordered pairs of distinct indices.
* `dist_half_smul_le`: the distance from half a unit vector to a point.
-/

public section

open Finset
open scoped RealInnerProductSpace

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The squared norm of a finite sum is the sum of the squared norms plus the inner products
over the ordered pairs of distinct indices. -/
theorem norm_sum_sq_real (s : Finset ι) (f : ι → V) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 + ∑ p ∈ s.offDiag, ⟪f p.1, f p.2⟫ := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner,
    ← sum_congr rfl fun i _ => (inner_sum s f (f i)).symm,
    ← sum_product' (f := fun i j => ⟪f i, f j⟫), ← diag_union_offDiag,
    sum_union (disjoint_diag_offDiag s), sum_diag]
  simp only [real_inner_self_eq_norm_sq]

/-- The distance from half a unit vector `u` to a point `x` is at most
`1 / 2 - ⟪u, x⟫ + ‖x‖ ^ 2`. -/
theorem dist_half_smul_le {u : V} (hu : ‖u‖ = 1) (x : V) :
    dist ((1 / 2 : ℝ) • u) x ≤ 1 / 2 - ⟪u, x⟫ + ‖x‖ ^ 2 := by
  rw [dist_eq_norm]
  have h1 : ‖(1 / 2 : ℝ) • u - x‖ ^ 2 = 1 / 4 - ⟪u, x⟫ + ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, hu, real_inner_smul_left,
      show ‖(1 / 2 : ℝ)‖ = 1 / 2 by norm_num]
    ring
  nlinarith [sq_nonneg (‖(1 / 2 : ℝ) • u - x‖ - 1 / 2), norm_nonneg ((1 / 2 : ℝ) • u - x)]

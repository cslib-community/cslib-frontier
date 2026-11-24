/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Star.Unitary

/-!
# Unitarity of self-adjoint involutions and of products

A `±1` observable, a self-adjoint `u` with `u * u = 1`, is unitary
(`IsSelfAdjoint.mem_unitary_of_mul_self`). Matrix and measurement-theoretic instances
(`Matrix.IsHermitian.mem_unitaryGroup_of_mul_self`, observables of projective measurements) are
corollaries.

The tactic `unitary_mem` closes a goal `u ∈ unitary R` for a product `u` of unitaries, of their
stars and of `1`, from the local hypotheses, which may be quantified
(`hX : ∀ a, X a ∈ unitary R`). It discharges the side goals of left multiplication by a unitary in
closeness chains (`Cslib.Quantum.AlgState.Approx.mul_left_unitary`).

## Main results

* `IsSelfAdjoint.mem_unitary_of_mul_self`: a self-adjoint involution is unitary.
-/

public section

/-- `unitary_mem` closes a goal `u ∈ unitary R` for a product `u` of unitaries, of their stars and
of `1`, using the local hypotheses, which may be quantified (`hX : ∀ a, X a ∈ unitary R`). -/
macro (name := unitaryMem) "unitary_mem" : tactic =>
  `(tactic| solve_by_elim (maxDepth := 16) [mul_mem, one_mem, Unitary.star_mem])

/-- A self-adjoint involution is unitary. -/
theorem IsSelfAdjoint.mem_unitary_of_mul_self {R : Type*} [Monoid R] [StarMul R] {u : R}
    (hu : IsSelfAdjoint u) (h : u * u = 1) : u ∈ unitary R := by
  rw [Unitary.mem_iff, hu.star_eq]
  exact ⟨h, h⟩

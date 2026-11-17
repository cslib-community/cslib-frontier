/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Approx
public import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Averages in a state

Rigidity arguments average over questions, group elements and outcomes. Mathlib's uniform average
`𝔼 i ∈ s, f i` (`Finset.expect`) handles these averages, and the state norm `‖·‖_φ` behaves under
it like a norm:

* the triangle inequality, `‖∑ a_i‖_φ ≤ ∑ ‖a_i‖_φ` and `‖𝔼 a_i‖_φ ≤ 𝔼 ‖a_i‖_φ`
  (`Cslib.Quantum.AlgState.norm_sum_le`, `Cslib.Quantum.AlgState.norm_expect_le`);
* **Jensen**, `‖𝔼 a_i‖²_φ ≤ 𝔼 ‖a_i‖²_φ` (`Cslib.Quantum.AlgState.norm_expect_sq_le`);
* **Jensen with contractions**, `‖𝔼 u_i d_i‖²_φ ≤ 𝔼 ‖d_i‖²_φ` when every `u_i` is a contraction
  (`Cslib.Quantum.AlgState.norm_expect_mul_sq_le`). This is the core step of twirling and of the
  compression of regular representations.

## Main results

* `Cslib.Quantum.AlgState.norm_expect_sq_le`: Jensen for the state norm.
* `Cslib.Quantum.AlgState.norm_expect_mul_sq_le`: Jensen with contractions.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Quantum.AlgState

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A] (φ : AlgState A) {ι : Type*} (s : Finset ι)

/-- The triangle inequality over finite sums. -/
theorem norm_sum_le (a : ι → A) : φ.norm (∑ i ∈ s, a i) ≤ ∑ i ∈ s, φ.norm (a i) := by
  simpa [norm, map_sum] using _root_.norm_sum_le s fun i => φ.toPreGNS (a i)

variable [Module ℚ≥0 A]

theorem norm_nnqsmul (q : ℚ≥0) (a : A) : φ.norm (q • a) = q * φ.norm a := by
  rw [← NNRat.cast_smul_eq_nnqsmul ℂ, norm_smul]
  simp

/-- The triangle inequality for averages. -/
theorem norm_expect_le (a : ι → A) : φ.norm (𝔼 i ∈ s, a i) ≤ 𝔼 i ∈ s, φ.norm (a i) :=
  le_expect_of_subadditive φ.norm_zero φ.norm_add_le fun n a => by
    rw [norm_nnqsmul, NNRat.smul_def]

/-- **Jensen** for the state norm: `‖𝔼_i a_i‖²_φ ≤ 𝔼_i ‖a_i‖²_φ`. -/
theorem norm_expect_sq_le (a : ι → A) :
    φ.norm (𝔼 i ∈ s, a i) ^ 2 ≤ 𝔼 i ∈ s, φ.norm (a i) ^ 2 :=
  (pow_le_pow_left₀ (φ.norm_nonneg _) (φ.norm_expect_le s a) 2).trans
    (s.sq_expect_le_expect_sq _)

/-- **Jensen with contractions**: `‖𝔼_i u_i d_i‖²_φ ≤ 𝔼_i ‖d_i‖²_φ` when every `u_i` is a
contraction. -/
theorem norm_expect_mul_sq_le {u d : ι → A} (hu : ∀ i ∈ s, star (u i) * u i ≤ 1) :
    φ.norm (𝔼 i ∈ s, u i * d i) ^ 2 ≤ 𝔼 i ∈ s, φ.norm (d i) ^ 2 :=
  (φ.norm_expect_sq_le s _).trans <| expect_le_expect fun i hi =>
    pow_le_pow_left₀ (φ.norm_nonneg _) (φ.norm_mul_le_of_star_mul_self_le_one (hu i hi) _) 2

end Cslib.Quantum.AlgState

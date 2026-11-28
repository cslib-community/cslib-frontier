/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
import CslibFrontier.Foundations.Analysis.InnerProductSpace.CHSH

/-!
# Tsirelson's inequality for states

For self-adjoint contractions `A₀, A₁, B₀, B₁` of a star-ordered algebra, `A_x⋆A_x ≤ 1` and
`B_y⋆B_y ≤ 1`, and every state `φ`,

`Re φ(A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁) ≤ 2√2`

(`Cslib.Quantum.AlgState.re_chsh_le`) [Cirel'son][Cirelson1980]. In the GNS pre-inner product space
of `φ` the observables are vectors of norm at most `1` and `φ(A_x B_y) = ⟨A_x, B_y⟩_φ`, so this is
the CHSH inequality for vectors (`chsh_re_inner_le`).

The bound needs neither commutation of the `A_x` with the `B_y` nor involutions: it covers the
observables `E_false - E_true` of arbitrary two-outcome measurements, which are only contractions.
Mathlib's `tsirelson_inequality` is the operator inequality for commuting involutions, proved by a
sum of squares.

## Main results

* `Cslib.Quantum.AlgState.re_chsh_le`: Tsirelson's inequality for a state.

## References

* [B. S. Cirel'son, *Quantum generalizations of Bell's inequality*][Cirelson1980]
-/

public section

namespace Cslib.Quantum.AlgState

variable {A : Type*} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
  [StarModule ℂ A] [SelfAdjointDecompose A]

/-- **Tsirelson's inequality** for a state: for self-adjoint contractions `A₀, A₁, B₀, B₁`,
`Re φ(A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁) ≤ 2√2`. -/
theorem re_chsh_le (φ : AlgState A) {A₀ A₁ B₀ B₁ : A} (hA₀ : IsSelfAdjoint A₀)
    (hA₁ : IsSelfAdjoint A₁) (hA₀' : star A₀ * A₀ ≤ 1) (hA₁' : star A₁ * A₁ ≤ 1)
    (hB₀ : star B₀ * B₀ ≤ 1) (hB₁ : star B₁ * B₁ ≤ 1) :
    (φ (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)).re ≤ 2 * √2 := by
  have h := chsh_re_inner_le (𝕜 := ℂ) (φ.norm_le_one hA₀') (φ.norm_le_one hA₁')
    (φ.norm_le_one hB₀) (φ.norm_le_one hB₁)
  simp only [inner_toPreGNS, hA₀.star_eq, hA₁.star_eq, RCLike.re_to_complex] at h
  simpa only [map_add, map_sub, Complex.add_re, Complex.sub_re] using h

end Cslib.Quantum.AlgState

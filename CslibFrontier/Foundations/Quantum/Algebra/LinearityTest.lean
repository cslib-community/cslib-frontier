/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Expect
public import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Linearity from consistency

In the two-player linearity test, one player answers a single query `a + b` with an observable
`A(a + b)`, and the other answers the pair `(a, b)` with two commuting observables `N₁(a, b)` and
`N₂(a, b)`. The test checks the product `N₁ N₂` against `A(a + b)`, and the consistency tests
check `N₁(a, b)` against `A(a)` and `N₂(a, b)` against `A(b)`.

If the other player's observables commute with the first player's, then passing these tests makes
the first player's observables linear on average:

`E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - ε - √η₁ - √η₂`

(`Cslib.Quantum.one_sub_le_expect_re_apply_mul_mul`), where `1 - ε` is the average correlation
`Re φ(N₁ N₂ A(a + b))` and `η₁`, `η₂` bound the average squared distances `‖A(a) - N₁(a, b)‖²_φ`
and `‖A(b) - N₂(a, b)‖²_φ`. The proof moves each factor `A(a)`, `A(b)` to the other player's
consistent copy and commutes it past the first player's operators
(`Cslib.Quantum.re_apply_mul_mul_ge`). This is the computation in
[Natarajan and Vidick, §3, proof of Theorem 11][NatarajanVidick2017] (arXiv:1610.03574v1), in any
state of any star-ordered algebra, with exact constants, and with the test outcomes written as
correlations of observables. Relating a strategy's winning probability to these correlations and
distances is tracked in cslib-community/cslib-frontier#6149.

Together with the rounding of approximately linear observables
(`Cslib.Quantum.exists_isProjective_charObs_of_linear`), the bound gives exactly linear unitaries
close to `A`.

## Main results

* `Cslib.Quantum.re_apply_mul_mul_ge`: the pointwise estimate.
* `Cslib.Quantum.one_sub_le_expect_re_apply_mul_mul`: linearity on average from the linearity and
  consistency tests.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Quantum

variable {R : Type*} [Ring R] [StarRing R] [PartialOrder R] [StarOrderedRing R] [Algebra ℂ R]
  [StarModule ℂ R] [SelfAdjointDecompose R]

/-- **Pointwise estimate.** If `N₁` commutes with `A₂` and `A₃`, and `N₂` commutes with `A₃`, then
`Re φ(A₃ A₂ A₁) ≥ Re φ(N₁ N₂ A₃) - ‖A₁ - N₁‖_φ - ‖A₂ - N₂‖_φ`, for unitaries `A₂`, `A₃`, `N₁`. -/
theorem re_apply_mul_mul_ge (φ : AlgState R) {A₁ A₂ A₃ N₁ N₂ : R} (h₂ : A₂ ∈ unitary R)
    (h₃ : A₃ ∈ unitary R) (hN₁ : N₁ ∈ unitary R) (hc₁₂ : Commute N₁ A₂) (hc₁₃ : Commute N₁ A₃)
    (hc₂₃ : Commute N₂ A₃) :
    (φ (N₁ * N₂ * A₃)).re - φ.norm (A₁ - N₁) - φ.norm (A₂ - N₂) ≤ (φ (A₃ * A₂ * A₁)).re := by
  have c₁ : A₁ ≈[φ; φ.norm (A₁ - N₁)] N₁ := AlgState.approx_iff.mpr le_rfl
  have c₂ : A₂ ≈[φ; φ.norm (A₂ - N₂)] N₂ := AlgState.approx_iff.mpr le_rfl
  have chain := calc
      A₃ * A₂ * A₁ ≈[φ; φ.norm (A₁ - N₁)] A₃ * A₂ * N₁ := c₁.mul_left_unitary (mul_mem h₃ h₂)
    _ = N₁ * A₃ * A₂ := by rw [← (hc₁₃.mul_right hc₁₂).eq, mul_assoc]
    _ ≈[φ; φ.norm (A₂ - N₂)] N₁ * A₃ * N₂ :=
        c₂.mul_left_unitary (mul_mem hN₁ h₃)
    _ = N₁ * N₂ * A₃ := by rw [mul_assoc, ← hc₂₃.eq, ← mul_assoc]
  have h := (Complex.re_le_norm _).trans chain.symm.norm_apply_sub_le
  rw [Complex.sub_re] at h
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem expect_expect_le_sqrt {f : (ι → Bool) → (ι → Bool) → ℝ} {η : ℝ}
    (h : 𝔼 a, 𝔼 b, f a b ^ 2 ≤ η) : 𝔼 a, 𝔼 b, f a b ≤ √η := by
  refine Real.le_sqrt_of_sq_le ?_
  calc (𝔼 a, 𝔼 b, f a b) ^ 2 ≤ 𝔼 a, (𝔼 b, f a b) ^ 2 := sq_expect_le_expect_sq _ _
    _ ≤ 𝔼 a, 𝔼 b, f a b ^ 2 := expect_le_expect fun a _ => sq_expect_le_expect_sq _ _
    _ ≤ η := h

/-- **Linearity from consistency.** Let `A(a)` be unitaries, and `N₁(a, b)`, `N₂(a, b)` operators
commuting with every `A(c)`, with `N₁(a, b)` unitary. If
`E_{a,b} Re φ(N₁(a, b) N₂(a, b) A(a + b)) ≥ 1 - ε`, `E_{a,b} ‖A(a) - N₁(a, b)‖²_φ ≤ η₁` and
`E_{a,b} ‖A(b) - N₂(a, b)‖²_φ ≤ η₂`, then `E_{a,b} Re φ(A(a) A(b) A(a + b)) ≥ 1 - ε - √η₁ - √η₂`. -/
theorem one_sub_le_expect_re_apply_mul_mul (φ : AlgState R) (A : (ι → Bool) → R)
    (N₁ N₂ : (ι → Bool) → (ι → Bool) → R) (hA : ∀ a, A a ∈ unitary R)
    (hN₁ : ∀ a b, N₁ a b ∈ unitary R) (hc₁ : ∀ a b c, Commute (N₁ a b) (A c))
    (hc₂ : ∀ a b c, Commute (N₂ a b) (A c)) {ε η₁ η₂ : ℝ}
    (hL : 1 - ε ≤ 𝔼 a, 𝔼 b, (φ (N₁ a b * N₂ a b * A (a + b))).re)
    (hC₁ : 𝔼 a, 𝔼 b, φ.norm (A a - N₁ a b) ^ 2 ≤ η₁)
    (hC₂ : 𝔼 a, 𝔼 b, φ.norm (A b - N₂ a b) ^ 2 ≤ η₂) :
    1 - ε - √η₁ - √η₂ ≤ 𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re := by
  have hpt : ∀ a b, (φ (N₁ a b * N₂ a b * A (a + b))).re - φ.norm (A a - N₁ a b) -
      φ.norm (A b - N₂ a b) ≤ (φ (A (a + b) * A b * A a)).re := fun a b =>
    re_apply_mul_mul_ge φ (hA b) (hA (a + b)) (hN₁ a b) (hc₁ a b b) (hc₁ a b (a + b))
      (hc₂ a b (a + b))
  have hd₁ := expect_expect_le_sqrt hC₁
  have hd₂ := expect_expect_le_sqrt hC₂
  have hsum : 𝔼 a, 𝔼 b, ((φ (N₁ a b * N₂ a b * A (a + b))).re - φ.norm (A a - N₁ a b) -
      φ.norm (A b - N₂ a b)) ≤ 𝔼 a, 𝔼 b, (φ (A (a + b) * A b * A a)).re :=
    expect_le_expect fun a _ => expect_le_expect fun b _ => hpt a b
  simp only [expect_sub_distrib] at hsum
  -- reindex `a ↦ a + b`
  have hre : 𝔼 a, 𝔼 b, (φ (A (a + b) * A b * A a)).re =
      𝔼 a, 𝔼 b, (φ (A a * A b * A (a + b))).re := by
    rw [expect_comm]
    conv_rhs => rw [expect_comm]
    refine expect_congr rfl fun b _ => ?_
    exact Fintype.expect_equiv (Equiv.addRight b) _ _ fun a => by
      simp only [Equiv.coe_addRight, BitString.add_cancel_right]
  linarith

end Cslib.Quantum

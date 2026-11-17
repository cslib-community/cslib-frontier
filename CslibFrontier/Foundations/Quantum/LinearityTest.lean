/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.LinearityTest
public import CslibFrontier.Foundations.Quantum.LinearityRounding

/-!
# Exactly linear observables from the linearity and consistency tests

In a tensor-product strategy on `ℂ^ι ⊗ ℂ^κ`, let the first player answer a single query `c` with
a `±1` observable `A(c) ⊗ 1`, and the second player answer a pair `(a, b)` with two commuting
`±1` observables `1 ⊗ N₁(a, b)` and `1 ⊗ N₂(a, b)`. If the linearity test correlation
`E_{a,b} Re φ((1 ⊗ N₁)(1 ⊗ N₂)(A(a + b) ⊗ 1))` is at least `1 - ε`, and the consistency distances
`E_{a,b} ‖A(a) ⊗ 1 - 1 ⊗ N₁(a, b)‖²_φ`, `E_{a,b} ‖A(b) ⊗ 1 - 1 ⊗ N₂(a, b)‖²_φ` are at most `η₁` and
`η₂`, then a projective measurement `P` on the first player's space `ℂ^ι` has unitary, exactly
linear character observables with

`E_a ‖(A(a) - χ_P(a)) ⊗ 1‖²_φ ≤ 40 (ε + √η₁ + √η₂)`

(`Cslib.Quantum.exists_isProjective_charObs_of_linearityTest`).

It composes linearity from consistency (`Cslib.Quantum.one_sub_le_expect_re_apply_mul_mul`, the
computation in the proof of [Natarajan and Vidick, §3, Theorem 11][NatarajanVidick2017],
arXiv:1610.03574v1) with the same-space rounding
(`Cslib.Quantum.exists_isProjective_charObs_kroneckerOne_of_linear`, a variant of their
Theorem 10). Unlike the source, the rounded observables act on the first player's factor, with no
ancilla. Deriving the correlations and distances from a strategy's winning probability, for the
players' measurements and with the source's question distribution, is tracked in
cslib-community/cslib-frontier#6149.

## Main results

* `Cslib.Quantum.exists_isProjective_charObs_of_linearityTest`: exactly linear unitaries from the
  linearity and consistency tests, on one player's factor.

## References

* [A. Natarajan and T. Vidick, *A quantum linearity test for robustly verifying
  entanglement*][NatarajanVidick2017]
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker MatrixOrder ComplexOrder BigOperators Matrix.Norms.L2Operator

variable {ι κ n : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype n]
  [DecidableEq n]

/-- **Exactly linear observables from the linearity and consistency tests**, on the first player's
factor of a tensor-product strategy. -/
theorem exists_isProjective_charObs_of_linearityTest (φ : AlgState (Matrix (ι × κ) (ι × κ) ℂ))
    (A : (n → Bool) → Matrix ι ι ℂ) (hA : ∀ a, IsSelfAdjoint (A a)) (hA2 : ∀ a, A a * A a = 1)
    (N₁ N₂ : (n → Bool) → (n → Bool) → Matrix κ κ ℂ) (hN₁ : ∀ a b, N₁ a b ∈ unitary (Matrix κ κ ℂ))
    {ε η₁ η₂ : ℝ}
    (hL : 1 - ε ≤ 𝔼 a, 𝔼 b, (φ ((1 ⊗ₖ N₁ a b) * (1 ⊗ₖ N₂ a b) * (A (a + b) ⊗ₖ 1))).re)
    (hC₁ : 𝔼 a, 𝔼 b, φ.norm (A a ⊗ₖ 1 - 1 ⊗ₖ N₁ a b) ^ 2 ≤ η₁)
    (hC₂ : 𝔼 a, 𝔼 b, φ.norm (A b ⊗ₖ 1 - 1 ⊗ₖ N₂ a b) ^ 2 ≤ η₂) :
    ∃ P : Measurement (n → Bool) (Matrix ι ι ℂ), P.IsProjective ∧
      (∀ a, P.charObs a ∈ unitary (Matrix ι ι ℂ)) ∧
      (∀ a a', P.charObs a * P.charObs a' = P.charObs (a + a')) ∧
      𝔼 a, φ.norm ((A a - P.charObs a) ⊗ₖ 1) ^ 2 ≤ 40 * (ε + √η₁ + √η₂) := by
  have hAu : ∀ a, A a ∈ unitary (Matrix ι ι ℂ) := fun a => by
    rw [Unitary.mem_iff, (hA a).star_eq]
    exact ⟨hA2 a, hA2 a⟩
  have hlin := one_sub_le_expect_re_apply_mul_mul φ (fun c => kroneckerOne (κ := κ) (A c))
    (fun a b => oneKronecker (ι := ι) (N₁ a b)) (fun a b => oneKronecker (ι := ι) (N₂ a b))
    (fun a => Unitary.map_mem _ (hAu a)) (fun a b => Unitary.map_mem _ (hN₁ a b))
    (fun a b c => (commute_kroneckerOne_oneKronecker _ _).symm)
    (fun a b c => (commute_kroneckerOne_oneKronecker _ _).symm)
    (by simpa only [kroneckerOne_apply, oneKronecker_apply] using hL)
    (by simpa only [kroneckerOne_apply, oneKronecker_apply] using hC₁)
    (by simpa only [kroneckerOne_apply, oneKronecker_apply] using hC₂)
  refine exists_isProjective_charObs_kroneckerOne_of_linear φ A hA hA2 ?_
  have e : ∀ a b, (A a * A b * A (a + b)) ⊗ₖ (1 : Matrix κ κ ℂ) =
      kroneckerOne (A a) * kroneckerOne (A b) * kroneckerOne (A (a + b)) := fun a b => by
    rw [← map_mul, ← map_mul, kroneckerOne_apply]
  simp only [e]
  linarith

end Cslib.Quantum

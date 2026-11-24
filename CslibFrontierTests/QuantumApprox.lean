/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Quantum.Algebra.Approx
import CslibFrontier.Foundations.Analysis.Asymptotics.PolyErr
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Computability.PCP.TwoProverGame.Commuting

/-! # The approximation calculus and polynomial error functions

Checked clients of `Cslib.Quantum.AlgState.Approx` and `Cslib.PolyErr`: chains of approximations in
`calc` add their errors, averaged closeness over questions is closeness in the weighted state on
the product algebra (instantiated on matrices), consistent provers have close effects, and
`fun_prop` proves that the error functions of typical robustness statements are polynomial.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumApprox

open Cslib Cslib.Quantum Cslib.Quantum.AlgState
open scoped MatrixOrder ComplexOrder

/-! ### Chains of approximations -/

/-- A three-step chain: errors add, and a left contraction is applied in the middle. -/
example {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : AlgState A)
    {a b c u : A} {δ₁ δ₂ δ₃ : ℝ} (h₁ : a ≈[φ; δ₁] b) (h₂ : u * b ≈[φ; δ₂] c)
    (h₃ : c ≈[φ; δ₃] 0) (hu : star u * u ≤ 1) : u * a ≈[φ; δ₁ + δ₂ + δ₃] 0 :=
  calc u * a ≈[φ; δ₁] u * b := h₁.mul_left hu
    _ ≈[φ; δ₂] c := h₂
    _ ≈[φ; δ₃] 0 := h₃

/-- Close operators have close expectations. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (φ : AlgState (Matrix ι ι ℂ)) {a b : Matrix ι ι ℂ}
    {δ : ℝ} (h : a ≈[φ; δ] b) : ‖φ a - φ b‖ ≤ δ :=
  h.norm_apply_sub_le

/-! ### Averages over questions -/

/-- Averaged closeness of matrix families over a question distribution. -/
example {Q ι : Type} [Fintype Q] [Fintype ι] [DecidableEq ι] (μ : PMF Q)
    (φ : AlgState (Matrix ι ι ℂ)) (f g : Q → Matrix ι ι ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (f ≈[avg μ fun _ => φ; δ] g) ↔ ∑ q, (μ q).toReal * φ.norm (f q - g q) ^ 2 ≤ δ ^ 2 :=
  approx_avg_iff hδ

/-- The calculus applies verbatim to averaged closeness. -/
example {Q ι : Type} [Fintype Q] [Fintype ι] [DecidableEq ι] (μ : PMF Q)
    (φ : Q → AlgState (Matrix ι ι ℂ)) {f g h : Q → Matrix ι ι ℂ} {δ δ' : ℝ}
    (h₁ : f ≈[avg μ φ; δ] g) (h₂ : g ≈[avg μ φ; δ'] h) : f ≈[avg μ φ; δ + δ'] h :=
  h₁.trans h₂

/-! ### Consistency -/

/-- Two provers asked the same question who agree with probability `1 - ε` have
`2ε`-close effects, in any commuting-operator strategy. -/
example {X A 𝒜 : Type} [Fintype A] [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (S : Cslib.PCP.CommutingStrategy X X A A 𝒜) (x : X) {ε : ℝ}
    (hε : 1 - ε ≤ Measurement.agreement S.state (S.alice x) (S.bob x)) :
    ∑ a, S.state.norm ((S.alice x).effect a - (S.bob x).effect a) ^ 2 ≤ 2 * ε :=
  Measurement.sum_norm_sub_sq_le_of_agreement _ _ _ (fun a => S.commute x x a a) hε

/-! ### Polynomial errors -/

example : PolyErr fun ε => 3 * √ε + (ε + √(2 * ε)) ^ 2 := by fun_prop

example (δ : ℝ → ℝ) (hδ : PolyErr δ) : PolyErr fun ε => 10 * δ (√ε) + δ ε * ε := by fun_prop

example (δ : ℝ → ℝ) (hδ : PolyErr δ) : PolyErr fun ε => √(δ (ε ^ 2)) + max ε (δ ε) := by
  fun_prop

/-- A polynomial error is small near `0`. -/
example (δ : ℝ → ℝ) (hδ : PolyErr δ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 → |δ ε| ≤ C * ε ^ c :=
  hδ.exists_le

example (δ : ℝ → ℝ) (hδ : PolyErr δ) : δ 0 = 0 :=
  hδ.apply_zero

end CslibFrontierTests.QuantumApprox

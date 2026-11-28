/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Foundations.Analysis.Normed.Close
import CslibFrontier.Foundations.Quantum.Algebra.Expect
import CslibFrontier.Foundations.Quantum.Algebra.FamApprox
import CslibFrontier.Foundations.Quantum.Orthogonalization

/-! # The closeness calculus

Checked clients of the unified closeness calculus: the generic relation `Cslib.Close` and its
`calc` chains, closeness in a state as an instance of it, Jensen's inequality for the state norm,
and closeness of measurement families, where orthogonalization and consistency compose in one
`calc` chain.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CloseCalculus

open Cslib Cslib.Quantum Finset
open scoped BigOperators MatrixOrder ComplexOrder

/-- Errors add along a `calc` chain of the generic relation. -/
example {A F : Type} [AddCommGroup A] [Module ℂ A] [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (L : A →ₗ[ℂ] F) {a b c : A} (h₁ : a ≈[L | 1] b) (h₂ : b ≈[L | 2] c) : a ≈[L | 1 + 2] c :=
  calc a ≈[L | 1] b := h₁
    _ ≈[L | 2] c := h₂

/-- Closeness in a state inherits sums from the generic calculus. -/
example {A : Type} [Ring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [Algebra ℂ A]
    [StarModule ℂ A] [SelfAdjointDecompose A] (φ : AlgState A) (f g : Fin 3 → A)
    (h : ∀ i ∈ univ, f i ≈[φ; 1] g i) : ∑ i, f i ≈[φ; ∑ _i : Fin 3, (1 : ℝ)] ∑ i, g i :=
  AlgState.Approx.sum univ h

/-- **Jensen with contractions** for the state norm. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (φ : AlgState (Matrix ι ι ℂ)) {κ : Type}
    (s : Finset κ) (u d : κ → Matrix ι ι ℂ) (hu : ∀ i ∈ s, star (u i) * u i ≤ 1) :
    φ.norm (𝔼 i ∈ s, u i * d i) ^ 2 ≤ 𝔼 i ∈ s, φ.norm (d i) ^ 2 :=
  φ.norm_expect_mul_sq_le s hu

/-- **Orthogonalization and consistency compose.** Orthogonalize every question's measurement,
then compare with a consistent family `R`: the two bounds chain in the family relation `≈ᶠ`. -/
example {ι α Q : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype Q] (μ : PMF Q)
    (φ : AlgState (Matrix ι ι ℂ)) (M R : Q → Measurement α (Matrix ι ι ℂ)) {ε ε' : ℝ}
    (hM : ∀ q, 1 - ε ≤ ∑ a, (φ ((M q).effect a * (M q).effect a)).re)
    (hc : ∀ q a, Commute ((M q).effect a) ((R q).effect a))
    (hagr : ∀ q, 1 - ε' ≤ Measurement.agreement φ (M q) (R q)) :
    ∃ P : Q → Measurement α (Matrix ι ι ℂ), (∀ q, (P q).IsProjective) ∧
      Measurement.effects P ≈ᶠ[μ, φ; √(9 * ε) + √(2 * ε')] Measurement.effects R := by
  obtain ⟨P, hP, h₁⟩ := Measurement.exists_isProjective_famApprox μ φ M hM
  refine ⟨P, hP, ?_⟩
  calc Measurement.effects P ≈ᶠ[μ, φ; √(9 * ε)] Measurement.effects M := h₁.symm
    _ ≈ᶠ[μ, φ; √(2 * ε')] Measurement.effects R :=
      Measurement.famApprox_of_agreement μ φ M R hc hagr

end CslibFrontierTests.CloseCalculus

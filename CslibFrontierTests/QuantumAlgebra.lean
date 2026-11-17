/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # States, measurements and commuting-operator strategies

Checked clients of the algebraic quantum core: vector states and their state-dependent norm on
matrices, measurements in an algebra and their bridge to matrix POVMs, the two instances of the
commuting-operator model (matrix algebras and arbitrary C⋆-algebras), and Tsirelson's bound in that
model, which the optimal EPR strategy attains.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumAlgebra

open Matrix Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame
open scoped Real MatrixOrder ComplexOrder

/-! ### States -/

/-- A vector state gives the identity norm `1`. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    (AlgState.vector ψ hψ).norm 1 = 1 :=
  AlgState.norm_one _

/-- Cauchy–Schwarz in a vector state. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (a b : Matrix ι ι ℂ) :
    ‖AlgState.vector ψ hψ (star a * b)‖ ≤
      (AlgState.vector ψ hψ).norm a * (AlgState.vector ψ hψ).norm b :=
  AlgState.norm_apply_star_mul_le _ a b

/-- Tsirelson's inequality holds in every state of a C⋆-algebra. -/
example {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] (φ : AlgState 𝒜)
    {A₀ A₁ B₀ B₁ : 𝒜} (hA₀ : IsSelfAdjoint A₀) (hA₁ : IsSelfAdjoint A₁)
    (hA₀' : star A₀ * A₀ ≤ 1) (hA₁' : star A₁ * A₁ ≤ 1) (hB₀ : star B₀ * B₀ ≤ 1)
    (hB₁ : star B₁ * B₁ ≤ 1) :
    (φ (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)).re ≤ 2 * √2 :=
  φ.re_chsh_le hA₀ hA₁ hA₀' hA₁' hB₀ hB₁

/-! ### Measurements -/

/-- The trivial measurement is projective and reports its outcome with certainty. -/
example (φ : AlgState (Matrix (Fin 2) (Fin 2) ℂ)) :
    (Measurement.const true : Measurement Bool (Matrix (Fin 2) (Fin 2) ℂ)).prob φ true = 1 := by
  simp [Measurement.prob_const]

example : (Measurement.const true : Measurement Bool (Matrix (Fin 2) (Fin 2) ℂ)).IsProjective :=
  Measurement.isProjective_const true

/-- In a vector state, a POVM measured as an algebraic measurement has its Born-rule
distribution. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (M : POVM Bool ι) (ψ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) : M.toMeasurement.distribution (AlgState.vector ψ hψ) = M.measure ψ hψ :=
  POVM.distribution_toMeasurement M ψ hψ

/-- Post-processing pushes the outcome distribution forward. -/
example (φ : AlgState (Matrix (Fin 2) (Fin 2) ℂ))
    (M : Measurement Bool (Matrix (Fin 2) (Fin 2) ℂ)) :
    (M.map not).distribution φ = (M.distribution φ).map not :=
  Measurement.distribution_map φ not M

/-! ### Commuting-operator strategies -/

/-- Tsirelson's bound for commuting-operator strategies in an arbitrary C⋆-algebra. -/
example {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (S : CommutingStrategy Bool Bool Bool Bool 𝒜) :
    chsh.commutingWinProb S ≤ Real.cos (π / 8) ^ 2 :=
  commutingWinProb_chsh_le S

/-- The answers of a commuting-operator strategy in a C⋆-algebra form a distribution. -/
noncomputable example {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (S : CommutingStrategy Bool Bool Bool Bool 𝒜) (x y : Bool) : PMF (Bool × Bool) :=
  S.answers x y

/-- The EPR strategy, as a commuting-operator strategy, attains Tsirelson's bound. -/
example : chsh.commutingWinProb chshEPR.toCommuting = Real.cos (π / 8) ^ 2 := by
  rw [commutingWinProb_toCommuting, quantumWinProb_chsh_chshEPR]

end CslibFrontierTests.QuantumAlgebra

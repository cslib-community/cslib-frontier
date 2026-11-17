/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.PCP.TwoProverGame.CHSHRigidity
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson

/-! # Rigidity of CHSH

Checked clients of the robust rigidity of CHSH: the sum-of-squares identity for vectors, near
anticommutation of near-optimal observables in any C⋆-algebra, the strategy-level statement for
commuting-operator strategies and, through `toCommuting`, for tensor-product strategies, and the
optimal EPR strategy, whose observables anticommute exactly in its state.
-/

namespace CslibFrontierTests.CHSHRigidity

open Cslib Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame
open scoped Real MatrixOrder ComplexOrder

/-- The sum-of-squares identity of CHSH in a complex inner product space. -/
example (u₀ u₁ v₀ v₁ : EuclideanSpace ℂ (Fin 3)) :
    ‖u₀ - ((√2)⁻¹ : ℂ) • (v₀ + v₁)‖ ^ 2 + ‖u₁ - ((√2)⁻¹ : ℂ) • (v₀ - v₁)‖ ^ 2 =
      ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖v₀‖ ^ 2 + ‖v₁‖ ^ 2 - √2 * (RCLike.re (inner ℂ u₀ v₀) +
        RCLike.re (inner ℂ u₀ v₁) + RCLike.re (inner ℂ u₁ v₀) - RCLike.re (inner ℂ u₁ v₁)) :=
  chsh_sos u₀ u₁ v₀ v₁

/-- Near-optimal commuting-operator strategies in any C⋆-algebra have nearly anticommuting
observables. -/
example {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (S : CommutingStrategy Bool Bool Bool Bool 𝒜) {ε : ℝ}
    (h : Real.cos (π / 8) ^ 2 - ε ≤ chsh.commutingWinProb S) :
    (S.alice false).observable * (S.alice true).observable +
        (S.alice true).observable * (S.alice false).observable ≈[S.state; chshRigidityError ε]
      0 :=
  S.anticomm_of_chsh h

/-- The same for tensor-product strategies, through their commuting-operator form. -/
example {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (S : QuantumStrategy Bool Bool Bool Bool ι κ) {ε : ℝ}
    (h : Real.cos (π / 8) ^ 2 - ε ≤ chsh.quantumWinProb S) :
    (S.toCommuting.alice false).observable * (S.toCommuting.alice true).observable +
        (S.toCommuting.alice true).observable * (S.toCommuting.alice false).observable
      ≈[S.toCommuting.state; chshRigidityError ε] 0 :=
  S.toCommuting.anticomm_of_chsh (by rwa [commutingWinProb_toCommuting])

/-- The error is a polynomial error function, so it vanishes at `0`. -/
example : chshRigidityError 0 = 0 :=
  polyErr_chshRigidityError.apply_zero

/-- The optimal EPR strategy attains Tsirelson's bound, so its observables anticommute exactly in
its state. -/
example :
    (chshEPR.toCommuting.alice false).observable * (chshEPR.toCommuting.alice true).observable +
      (chshEPR.toCommuting.alice true).observable * (chshEPR.toCommuting.alice false).observable
    ≈[chshEPR.toCommuting.state; 0] 0 := by
  have h := chshEPR.toCommuting.anticomm_of_chsh (ε := 0) (by
    rw [commutingWinProb_toCommuting, quantumWinProb_chsh_chshEPR, sub_zero])
  rwa [polyErr_chshRigidityError.apply_zero] at h

end CslibFrontierTests.CHSHRigidity

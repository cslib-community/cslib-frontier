/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Foundations.Quantum.Algebra.CHSHRigidity
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Near-optimal CHSH strategies are rigid

A commuting-operator strategy that wins CHSH with probability `cos²(π/8) - ε`, within `ε` of
Tsirelson's bound, has observables `A_x = P_x^0 - P_x^1` for Alice that nearly anticommute in the
shared state:

`‖A₀A₁ + A₁A₀‖_φ ≤ chshRigidityError ε = (4 + 2√2) √(8√2 ε)`

(`Cslib.PCP.CommutingStrategy.anticomm_of_chsh`). The error is a polynomial error function
(`Cslib.PCP.polyErr_chshRigidityError`), the `O(√ε)` of robust self-testing
[McKague, Yang and Scarani][McKagueYangScarani2012]. The measurements are arbitrary, so the
theorem covers every strategy of the finite-dimensional tensor-product model through
`Cslib.PCP.QuantumStrategy.toCommuting`, and every C⋆-algebraic strategy. Bob's observables are
rigid in the same way, by the symmetry of the game.

The statement is the operator-algebraic rigidity theorem `Cslib.Quantum.AlgState.chsh_anticomm`
applied to the correlations: a winning probability of `cos²(π/8) - ε` is a CHSH expression of
`2√2 - 8ε` (`Cslib.PCP.TwoProverGame.commutingWinProb_chsh`).

## Main definitions

* `Cslib.PCP.chshRigidityError`: the error function of CHSH rigidity.

## Main results

* `Cslib.PCP.CommutingStrategy.anticomm_of_chsh`: near-optimal strategies have nearly
  anticommuting observables.
* `Cslib.PCP.polyErr_chshRigidityError`: the error is polynomial.

## References

* [M. McKague, T. H. Yang and V. Scarani, *Robust self-testing of the
  singlet*][McKagueYangScarani2012]
-/

@[expose] public section

namespace Cslib.PCP

open Quantum
open scoped Real

/-- The error of CHSH rigidity, `(4 + 2√2) √(8√2 ε)`, for strategies within `ε` of Tsirelson's
bound. -/
noncomputable def chshRigidityError (ε : ℝ) : ℝ :=
  (4 + 2 * √2) * √(√2 * (8 * ε))

/-- The error of CHSH rigidity is a polynomial error function. -/
theorem polyErr_chshRigidityError : PolyErr chshRigidityError := by
  unfold chshRigidityError
  fun_prop

namespace CommutingStrategy

variable {X Y 𝒜 : Type*} [Ring 𝒜] [PartialOrder 𝒜] [Algebra ℂ 𝒜]

/-- Alice's and Bob's observables commute. -/
theorem commute_observable (S : CommutingStrategy X Y Bool Bool 𝒜) (x : X) (y : Y) :
    Commute (S.alice x).observable (S.bob y).observable :=
  ((S.commute x y false false).sub_right (S.commute x y false true)).sub_left
    ((S.commute x y true false).sub_right (S.commute x y true true))

/-- The CHSH expression of the observables is the CHSH combination of the correlations. -/
theorem re_chshExpr (S : CommutingStrategy X Y Bool Bool 𝒜) (x₀ x₁ : X) (y₀ y₁ : Y) :
    (S.state (AlgState.chshExpr (S.alice x₀).observable (S.alice x₁).observable
      (S.bob y₀).observable (S.bob y₁).observable)).re =
      S.correlation x₀ y₀ + S.correlation x₀ y₁ + S.correlation x₁ y₀ - S.correlation x₁ y₁ := by
  simp only [AlgState.chshExpr, correlation, map_add, map_sub, Complex.add_re, Complex.sub_re]

variable [StarRing 𝒜] [StarOrderedRing 𝒜] [StarModule ℂ 𝒜] [SelfAdjointDecompose 𝒜]
  [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint] [NonnegSpectrumClass ℝ 𝒜]

/-- **Rigidity of CHSH**: a commuting-operator strategy that wins CHSH with probability at least
`cos²(π/8) - ε` has nearly anticommuting observables for Alice,
`‖A₀A₁ + A₁A₀‖_φ ≤ chshRigidityError ε`. -/
theorem anticomm_of_chsh (S : CommutingStrategy Bool Bool Bool Bool 𝒜) {ε : ℝ}
    (h : Real.cos (π / 8) ^ 2 - ε ≤ TwoProverGame.chsh.commutingWinProb S) :
    (S.alice false).observable * (S.alice true).observable +
        (S.alice true).observable * (S.alice false).observable ≈[S.state; chshRigidityError ε]
      0 := by
  rw [TwoProverGame.commutingWinProb_chsh, Real.cos_sq_pi_div_eight] at h
  have hc : 2 * √2 - 8 * ε ≤ (S.state (AlgState.chshExpr (S.alice false).observable
      (S.alice true).observable (S.bob false).observable (S.bob true).observable)).re := by
    rw [re_chshExpr]
    linarith
  have hB : ∀ y, star (S.bob y).observable * (S.bob y).observable ≤ 1 := fun y =>
    (S.bob y).star_observable_mul_self_le_one
  have hA : ∀ x, star (S.alice x).observable * (S.alice x).observable ≤ 1 := fun x =>
    (S.alice x).star_observable_mul_self_le_one
  exact S.state.chsh_anticomm (S.alice false).isSelfAdjoint_observable
    (S.alice true).isSelfAdjoint_observable (S.bob false).isSelfAdjoint_observable
    (S.bob true).isSelfAdjoint_observable (hA false) (hA true) (hB false) (hB true)
    (S.commute_observable false false) (S.commute_observable false true)
    (S.commute_observable true false) (S.commute_observable true true) hc

end CommutingStrategy

end Cslib.PCP

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystem
import CslibFrontier.Foundations.Data.BitString.Sign.BigOperators

/-! # Linear constraint system games

Checked clients of joint measurements and linear constraint system games: the sign of an
assignment is the sign of its parity, and joint projections of commuting observables sum to `1`
and vanish on outcomes that contradict the product of the family. Two statements cover perfect
strategies. In any C⋆-algebra, an operator solution together with a *supplied* Bob that commutes
with Alice and agrees perfectly in a *supplied* state wins with certainty
(`commutingWinProb_strategy_of_agreement`; the scalar `evenPair` example supplies the agreement).
For a finite-dimensional operator solution, the maximally entangled transpose strategy obtains
Bob, the state and the agreement from the matrices alone and wins with certainty
(`commutingWinProb_maxEntangledStrategy`), exercised in general and on `evenPair` as `1 × 1`
matrices.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearSystem

open Cslib Cslib.Quantum Cslib.PCP
open scoped ComplexOrder MatrixOrder

/-- The assignment `(1, 1, 0)` has even parity on all three variables, so its signs multiply to
`1`. -/
example : ∏ v : Fin 3, BitString.signVal (![true, true, false] v) = 1 := by
  rw [← BitString.signVal_sum]
  have h : (∑ a, ![true, true, false] a) = false := by decide
  rw [h, BitString.signVal_false]

/-- Joint projections of commuting observables sum to `1`. -/
example {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (O : ι → A)
    (hO : ∀ i j, Commute (O i) (O j)) : ∑ a, jointProj O hO a = 1 :=
  sum_jointProj O hO

/-- An outcome contradicting the product of a family of involutions has effect `0`. -/
example {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (O : ι → A)
    (hO : ∀ i j, Commute (O i) (O j)) (hO' : ∀ j, O j * O j = 1)
    (hprod : jointProd O hO = (1 : ℂ) • 1) (a : ι → Bool)
    (ha : (1 : ℂ) ≠ ∏ j, (BitString.signVal (a j) : ℂ)) :
    jointProj O hO a = 0 :=
  jointProj_eq_zero O hO hO' hprod ha

/-- Operator solutions with a supplied perfectly agreeing Bob win every linear constraint system
game. -/
example {V E 𝒜 : Type} [Fintype V] [DecidableEq V] [Finite E] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (L : LinearSystem V E) (X : L.OperatorSolution 𝒜) (Y : V → 𝒜)
    (hY : ∀ v, IsSelfAdjoint (Y v)) (hY' : ∀ v, Y v * Y v = 1) (φ : AlgState 𝒜)
    (hXY : ∀ u v, Commute (X.op u) (Y v)) (hagree : ∀ v, X.op v ≈[φ; 0] Y v)
    (μ : PMF (E × V)) :
    (L.game μ).commutingWinProb (X.strategy Y hY hY' φ hXY) = 1 :=
  X.commutingWinProb_strategy_of_agreement Y hY hY' φ hXY hagree μ

/-- The identity state on `ℂ`. -/
noncomputable def complexState : AlgState ℂ where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  monotone' _ _ h := h
  map_one' := rfl

/-- The one equation `x₀ ⊕ x₁ = 0` on two variables. -/
def evenPair : LinearSystem (Fin 2) Unit where
  support _ := Finset.univ
  parity _ := false

theorem evenPair_satisfies : ∀ e, evenPair.Satisfies e (fun _ => false) := by
  intro e
  cases e
  decide

/-- The all-zero assignment is an operator solution of `evenPair` in `ℂ`, and with Bob holding the
same scalars it wins the game with certainty, for every question distribution. -/
example (μ : PMF (Unit × Fin 2)) :
    (evenPair.game μ).commutingWinProb
      ((LinearSystem.OperatorSolution.ofAssignment (fun _ => false) evenPair_satisfies).strategy
        (fun v => (BitString.signVal ((fun _ => false : Fin 2 → Bool) v) : ℂ))
        (fun _ => Complex.conj_ofReal _)
        (fun _ => by simp)
        complexState (fun _ _ => Commute.all _ _)) = 1 :=
  LinearSystem.OperatorSolution.commutingWinProb_strategy_of_agreement _ _ _ _ _ _
    (fun _ => AlgState.approx_self _ _) μ

/-- **Operator solutions give perfect strategies**: every finite-dimensional operator solution, from
its matrices alone, wins with certainty through the maximally entangled transpose strategy. -/
example {V E ι : Type} [Fintype V] [DecidableEq V] [Finite E] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (L : LinearSystem V E) (X : L.OperatorSolution (Matrix ι ι ℂ))
    (μ : PMF (E × V)) :
    (L.game μ).commutingWinProb X.maxEntangledStrategy = 1 :=
  X.commutingWinProb_maxEntangledStrategy μ

/-- **Concrete instance**: the all-zero assignment of `evenPair`, as `1 × 1` matrices, wins with
certainty through the maximally entangled transpose strategy. -/
example (μ : PMF (Unit × Fin 2)) :
    (evenPair.game μ).commutingWinProb
      (((LinearSystem.OperatorSolution.ofAssignment (fun _ => false) evenPair_satisfies).map
        (StarAlgHom.ofId ℂ (Matrix (Fin 1) (Fin 1) ℂ))).maxEntangledStrategy) = 1 :=
  LinearSystem.OperatorSolution.commutingWinProb_maxEntangledStrategy _ μ

end CslibFrontierTests.LinearSystem

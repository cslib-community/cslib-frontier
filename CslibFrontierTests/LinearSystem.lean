/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystem

/-! # Linear constraint system games

Checked clients of joint measurements and linear constraint system games: the sign of an
assignment is the sign of its parity, joint projections of commuting observables sum to `1` and
vanish on outcomes that contradict the product of the family, and operator solutions win every
linear constraint system game with certainty in any C⋆-algebra.
-/

namespace CslibFrontierTests.LinearSystem

open Cslib Cslib.Quantum Cslib.PCP

/-- The assignment `(1, 1, 0)` has even parity on all three variables, so its signs multiply to
`1`. -/
example : ∏ v : Fin 3, boolSign (![true, true, false] v) = 1 := by
  have h : setParity Finset.univ ![true, true, false] = false := by decide
  rw [prod_boolSign_eq, h, boolSign_false]

/-- Joint projections of commuting observables sum to `1`. -/
example {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (O : ι → A)
    (hO : ∀ i j, Commute (O i) (O j)) : ∑ a, jointProj O hO a = 1 :=
  sum_jointProj O hO

/-- An outcome contradicting the product of a family of involutions has effect `0`. -/
example {ι A : Type} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A] (O : ι → A)
    (hO : ∀ i j, Commute (O i) (O j)) (hO' : ∀ j, O j * O j = 1)
    (hprod : jointProd O hO = (1 : ℂ) • 1) (a : ι → Bool) (ha : (1 : ℂ) ≠ ∏ j, boolSign (a j)) :
    jointProj O hO a = 0 :=
  jointProj_eq_zero O hO hO' hprod ha

/-- Operator solutions with perfect agreement win every linear constraint system game. -/
example {V E 𝒜 : Type} [Fintype V] [DecidableEq V] [Finite E] [CStarAlgebra 𝒜] [PartialOrder 𝒜]
    [StarOrderedRing 𝒜] (L : LinearSystem V E) (X : L.OperatorSolution 𝒜) (Y : V → 𝒜)
    (hY : ∀ v, IsSelfAdjoint (Y v)) (hY' : ∀ v, Y v * Y v = 1) (φ : AlgState 𝒜)
    (hXY : ∀ u v, Commute (X.op u) (Y v)) (hagree : ∀ v, X.op v ≈[φ; 0] Y v)
    (μ : PMF (E × V)) :
    (L.game μ).commutingWinProb (X.strategy Y hY hY' φ hXY) = 1 :=
  X.commutingWinProb_strategy Y hY hY' φ hXY hagree μ

end CslibFrontierTests.LinearSystem

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystemConverse
public import CslibFrontier.Computability.PCP.TwoProverGame.Naimark
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Perfect tensor-product strategies for linear constraint system games

Every perfect finite-dimensional strategy for the game of a linear constraint system gives an
operator solution in the shared state, without any assumption on its measurements
(`Cslib.PCP.QuantumStrategy.stateSolution`): its Naimark dilation
(`Cslib.PCP.QuantumStrategy.dilate`) is projective and wins with the same probability, and its
commuting-operator form in the C⋆-algebra of matrices (with the operator norm) satisfies the
hypotheses of `Cslib.PCP.CommutingStrategy.stateSolution`
[Cleve and Mittal][CleveMittal2014].

## Main results

* `Cslib.PCP.QuantumStrategy.isProjective_toCommuting_alice`,
  `Cslib.PCP.QuantumStrategy.isProjective_toCommuting_bob`: projective measurements stay projective
  in the commuting-operator form.
* `Cslib.PCP.QuantumStrategy.stateSolution`: perfect strategies give state-dependent operator
  solutions.

## References

* [R. Cleve and R. Mittal, *Characterization of binary constraint system
  games*][CleveMittal2014]
-/

@[expose] public section

namespace Cslib.PCP

open Matrix Quantum
open scoped Kronecker MatrixOrder ComplexOrder

namespace QuantumStrategy

variable {X Y A B ι κ : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

theorem isProjective_toCommuting_alice (S : QuantumStrategy X Y A B ι κ) (x : X)
    (h : (S.alice x).toMeasurement.IsProjective) : (S.toCommuting.alice x).IsProjective := by
  intro a
  change (S.alice x).effect a ⊗ₖ (1 : Matrix κ κ ℂ) * (S.alice x).effect a ⊗ₖ 1 =
    (S.alice x).effect a ⊗ₖ 1
  rw [← mul_kronecker_mul, Matrix.mul_one]
  exact congrArg (· ⊗ₖ (1 : Matrix κ κ ℂ)) (h a)

theorem isProjective_toCommuting_bob (S : QuantumStrategy X Y A B ι κ) (y : Y)
    (h : (S.bob y).toMeasurement.IsProjective) : (S.toCommuting.bob y).IsProjective := by
  intro b
  change (1 : Matrix ι ι ℂ) ⊗ₖ (S.bob y).effect b * 1 ⊗ₖ (S.bob y).effect b =
    1 ⊗ₖ (S.bob y).effect b
  rw [← mul_kronecker_mul, Matrix.mul_one]
  exact congrArg ((1 : Matrix ι ι ℂ) ⊗ₖ ·) (h b)

variable {V E : Type*} [Fintype V] [DecidableEq V] [Finite E] (L : LinearSystem V E)
  {μ : PMF (E × V)}

open scoped Matrix.Norms.L2Operator in
/-- **Perfect strategies give operator solutions in the state** [Cleve and Mittal][CleveMittal2014]:
a finite-dimensional strategy winning the game of a linear constraint system with certainty, for
a question distribution of full support, gives a state-dependent operator solution: the `±1`
observables of Bob's Naimark-dilated measurements, in the dilated shared state. -/
noncomputable def stateSolution (S : QuantumStrategy E V (V → Bool) Bool ι κ) (hμ : ∀ q, μ q ≠ 0)
    (h : (L.game μ).quantumWinProb S = 1) :
    L.StateSolution (S.dilate (fun _ => false) false).toCommuting.state :=
  CommutingStrategy.stateSolution L (S.dilate (fun _ => false) false).toCommuting hμ
    (fun e => isProjective_toCommuting_alice _ e (S.isProjective_alice_dilate _ _ e))
    (fun v => isProjective_toCommuting_bob _ v (S.isProjective_bob_dilate _ _ v))
    (by rw [TwoProverGame.commutingWinProb_toCommuting, TwoProverGame.quantumWinProb_dilate, h])

end QuantumStrategy

end Cslib.PCP

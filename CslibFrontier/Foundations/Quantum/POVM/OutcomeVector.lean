/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2

/-!
# Square-root measurement branches

The square root of a POVM effect sends the input vector to an unnormalized branch vector.
Its squared norm is the Born weight. For a pair of local outcomes the square root is the
Kronecker product of the local square roots.

## Main results

* `norm_outcomeVector_sq`: the branch weight is the outcome probability for a unit input.
* `sqrtEffect_kronecker`: the square-root update for independent local measurements.
-/

public section

namespace Cslib.Quantum.POVM

open Matrix
open scoped MatrixOrder Kronecker

variable {A B ι κ : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]

/-- The square root `√E_a` of an effect. -/
@[expose] noncomputable def sqrtEffect (M : POVM A ι) (a : A) : Matrix ι ι ℂ :=
  CFC.sqrt (M.effect a)

theorem sqrtEffect_mul_self (M : POVM A ι) (a : A) : M.sqrtEffect a * M.sqrtEffect a = M.effect a :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr (M.posSemidef a))

theorem conjTranspose_sqrtEffect (M : POVM A ι) (a : A) : (M.sqrtEffect a)ᴴ = M.sqrtEffect a :=
  (CFC.sqrt_nonneg (M.effect a)).isSelfAdjoint.star_eq

/-- The unnormalized pure-state branch `√E_a ψ`. -/
@[expose] noncomputable def outcomeVector (M : POVM A ι) (ψ : EuclideanSpace ℂ ι)
    (a : A) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (M.sqrtEffect a *ᵥ ψ.ofLp)

/-- Its squared norm is the Born weight of the outcome, also for an unnormalized input. -/
theorem norm_outcomeVector_sq (M : POVM A ι) (ψ : EuclideanSpace ℂ ι) (a : A) :
    ‖M.outcomeVector ψ a‖ ^ 2 = M.prob ψ a := by
  apply Complex.ofReal_injective
  rw [ofReal_prob, Complex.ofReal_pow, ← EuclideanSpace.star_dotProduct_self_eq_norm_sq,
    outcomeVector, WithLp.ofLp_toLp, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    conjTranspose_sqrtEffect, sqrtEffect_mul_self]

variable [Fintype B] [Fintype κ] [DecidableEq κ]

/-- The positive square root of a product effect is the product of its local square roots. -/
theorem sqrtEffect_kronecker (M : POVM A ι) (N : POVM B κ) (a : A) (b : B) :
    (M.kronecker N).sqrtEffect (a, b) = M.sqrtEffect a ⊗ₖ N.sqrtEffect b := by
  apply (CFC.sqrt_eq_iff _ _ ((M.kronecker N).posSemidef (a, b)).nonneg
    (((CFC.sqrt_nonneg (M.effect a)).posSemidef.kronecker
      (CFC.sqrt_nonneg (N.effect b)).posSemidef).nonneg)).2
  change (M.sqrtEffect a ⊗ₖ N.sqrtEffect b) * (M.sqrtEffect a ⊗ₖ N.sqrtEffect b) =
    M.effect a ⊗ₖ N.effect b
  rw [← mul_kronecker_mul, sqrtEffect_mul_self, sqrtEffect_mul_self]

end Cslib.Quantum.POVM

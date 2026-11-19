/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix

/-!
# Vector expectations and scalar invariance of pure states

The projector of a scalar multiple scales by the scalar times its conjugate. In particular,
global phases disappear from the existing density-matrix representation. Pairing a pure
state with an operator under the trace gives the corresponding vector expectation.

## Main results

* `Cslib.Quantum.pureState_smul`: the exact scalar multiplication rule.
* `Cslib.Quantum.pureState_smul_of_norm_eq_one`: global phases leave the projector unchanged.
* `Cslib.Quantum.trace_mul_pureState`: the trace pairing is the vector expectation.
-/

public section

namespace Cslib.Quantum

open Matrix

variable {ι : Type*}

/-- Multiplying a vector by a scalar scales its projector by the squared scalar modulus. -/
theorem pureState_smul (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    pureState (c • ψ) = (c * star c) • pureState ψ := by
  ext i j
  simp [pureState_apply, mul_mul_mul_comm]

/-- A global phase has no effect on a pure-state density matrix. -/
theorem pureState_smul_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1)
    (ψ : EuclideanSpace ℂ ι) : pureState (c • ψ) = pureState ψ := by
  rw [pureState_smul]
  have h : c * star c = 1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  rw [h, one_smul]

/-- The signs of a vector determine the same pure-state density matrix. -/
@[simp] theorem pureState_neg (ψ : EuclideanSpace ℂ ι) : pureState (-ψ) = pureState ψ := by
  simpa only [neg_one_smul] using
    pureState_smul_of_norm_eq_one (-1) (by simp) ψ

/-- The trace pairing with a pure-state density matrix is the vector expectation. -/
theorem trace_mul_pureState [Fintype ι] (M : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    (M * pureState ψ).trace = star ψ.ofLp ⬝ᵥ (M *ᵥ ψ.ofLp) := by
  have hp : pureState ψ = Matrix.vecMulVec ψ.ofLp (star ψ.ofLp) := by
    ext i j
    exact pureState_apply ψ i j
  rw [hp, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

end Cslib.Quantum

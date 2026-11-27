/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.AlgState
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Symmetric tensor states

Swapping both factors of a tensor observable preserves its expectation in a
swap-invariant bipartite vector state.

## Main results

* `Cslib.Quantum.AlgState.vector_kronecker_swap` exchanges observables on the
  two factors of a symmetric vector state.
-/

public section

namespace Cslib.Quantum.AlgState

open Matrix Finset
open scoped Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector state of a swap-invariant bipartite vector gives the same
expectation when the two factors of a tensor observable are exchanged. -/
theorem vector_kronecker_swap (ψ : EuclideanSpace ℂ (ι × ι)) (hψ : ‖ψ‖ = 1)
    (hswap : ∀ a b, ψ.ofLp (a, b) = ψ.ofLp (b, a)) (X Y : Matrix ι ι ℂ) :
    AlgState.vector ψ hψ (X ⊗ₖ Y) = AlgState.vector ψ hψ (Y ⊗ₖ X) := by
  simp only [AlgState.vector_apply, dotProduct, Matrix.mulVec]
  let e := Equiv.prodComm ι ι
  refine ((e.sum_comp _).symm.trans ?_)
  refine sum_congr rfl fun i _ => ?_
  change star (ψ.ofLp (e i)) * (∑ j, (X ⊗ₖ Y) (e i) j * ψ.ofLp j) =
    star (ψ.ofLp i) * ∑ j, (Y ⊗ₖ X) i j * ψ.ofLp j
  rw [show ψ.ofLp (e i) = ψ.ofLp i from hswap i.2 i.1]
  congr 1
  refine ((e.sum_comp _).symm.trans ?_)
  refine sum_congr rfl fun j _ => ?_
  change (X i.2 j.2 * Y i.1 j.1) * ψ.ofLp (j.2, j.1) =
    (Y i.1 j.1 * X i.2 j.2) * ψ.ofLp j
  rw [hswap j.2 j.1, mul_comm (X i.2 j.2)]

end Cslib.Quantum.AlgState

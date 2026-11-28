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
  refine (e.sum_comp _).symm.trans (sum_congr rfl fun ⟨a, b⟩ _ => ?_)
  rw [← e.sum_comp (fun j => (X ⊗ₖ Y) (e (a, b)) j * ψ.ofLp j)]
  simp only [e, Equiv.prodComm_apply, Prod.swap_prod_mk, Pi.star_apply, kroneckerMap_apply,
    hswap b a]
  exact congrArg (star (ψ.ofLp (a, b)) * ·) (sum_congr rfl fun ⟨c, d⟩ _ => by
    rw [Prod.swap_prod_mk, hswap d c, mul_comm (X b d)])

end Cslib.Quantum.AlgState

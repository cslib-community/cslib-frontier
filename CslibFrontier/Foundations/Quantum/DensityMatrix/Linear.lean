/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix

/-!
# Linear partial trace

Bundle the existing partial trace as a complex-linear map, using its existing addition and
scalar laws. This lets linear measurement continuations observe a reference register and lets
the generic linear-map API handle sums and real scalar towers.

## Main definitions

* `Cslib.Quantum.partialTraceLeftLinearMap`: the existing partial trace as a linear map.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker

/-- The existing partial trace over the first factor, bundled with its established linearity. -/
noncomputable def partialTraceLeftLinearMap (ι κ : Type*) [Fintype ι] :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' := partialTraceLeft_smul

/-- Bundling changes no partial-trace entries. -/
@[simp] theorem partialTraceLeftLinearMap_apply (ι κ : Type*) [Fintype ι]
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceLeftLinearMap ι κ ρ = partialTraceLeft ρ := by rfl

/-- Observing only the right system pairs with its partial trace. -/
theorem trace_mul_partialTraceLeft {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [CommSemiring R] (M : Matrix κ κ R) (ρ : Matrix (ι × κ) (ι × κ) R) :
    (M * partialTraceLeft ρ).trace = (((1 : Matrix ι ι R) ⊗ₖ M) * ρ).trace := by
  have hselect (i : ι) (k : κ) :
      (∑ j : ι, ∑ l : κ, if i = j then M k l * ρ (j, l) (i, k) else 0) =
        ∑ l : κ, M k l * ρ (i, l) (i, k) := by
    rw [sum_comm]
    simp
  simp only [trace, diag_apply, Matrix.mul_apply, partialTraceLeft_apply, Fintype.sum_prod_type,
    kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.mul_sum, hselect]
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_comm

end Cslib.Quantum

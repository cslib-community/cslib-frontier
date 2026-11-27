/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix

/-!
# Pairing with a partial trace

Multiplication by an operator that acts only on the retained system passes through
the partial trace on either side. Under the matrix trace pairing, tensoring with
the identity is therefore adjoint to discarding the second system.

## Main results

* `partialTraceRight_kronecker_one_mul`, `partialTraceRight_mul_kronecker_one`:
  multiplication on the retained system commutes with discarding the second system.
* `trace_kronecker_one_mul`: the resulting trace pairing identity.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [CommSemiring R]

/-- Left multiplication by an operator on the retained system passes through the partial trace. -/
theorem partialTraceRight_kronecker_one_mul (X : Matrix ι ι R)
    (A : Matrix (ι × κ) (ι × κ) R) :
    partialTraceRight ((X ⊗ₖ (1 : Matrix κ κ R)) * A) = X * partialTraceRight A := by
  ext i j
  simp only [partialTraceRight_apply, Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq,
    mem_univ, ite_true]
  rw [sum_comm]
  simp_rw [← mul_sum]

/-- Right multiplication by an operator on the retained system passes through the partial trace. -/
theorem partialTraceRight_mul_kronecker_one (X : Matrix ι ι R)
    (A : Matrix (ι × κ) (ι × κ) R) :
    partialTraceRight (A * (X ⊗ₖ (1 : Matrix κ κ R))) = partialTraceRight A * X := by
  ext i j
  simp only [partialTraceRight_apply, Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero, sum_ite_eq',
    mem_univ, ite_true]
  rw [sum_comm]
  simp_rw [← sum_mul]

/-- Tensoring an operator with the identity and taking its trace pairing with a joint
matrix is equivalent to pairing it with the retained marginal. -/
theorem trace_kronecker_one_mul (X : Matrix ι ι R) (A : Matrix (ι × κ) (ι × κ) R) :
    ((X ⊗ₖ (1 : Matrix κ κ R)) * A).trace = (X * partialTraceRight A).trace := by
  rw [← trace_partialTraceRight ((X ⊗ₖ (1 : Matrix κ κ R)) * A),
    partialTraceRight_kronecker_one_mul]

omit [DecidableEq κ] [Fintype κ] in
/-- Swapping the two factors exchanges the two partial traces. -/
theorem partialTraceRight_reindex_prodComm (A : Matrix (ι × κ) (ι × κ) R) :
    partialTraceRight (reindex (Equiv.prodComm ι κ) (Equiv.prodComm ι κ) A) =
      partialTraceLeft A := by
  ext i j
  simp only [partialTraceRight_apply, partialTraceLeft_apply, reindex_apply, submatrix_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply]
  rfl

/-- A trace-preserving Kraus operation on the second system leaves the first marginal unchanged.
This is `partialTraceLeft_kraus` after exchanging the two systems. -/
theorem partialTraceRight_kraus [DecidableEq ι] {α : Type*} (s : Finset α)
    (K : α → Matrix κ κ ℂ) (hK : ∑ a ∈ s, (K a)ᴴ * K a = 1)
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) :
    partialTraceRight
      (∑ a ∈ s, ((1 : Matrix ι ι ℂ) ⊗ₖ K a) * ρ * ((1 : Matrix ι ι ℂ) ⊗ₖ K a)ᴴ) =
      partialTraceRight ρ := by
  let e := reindexAlgEquiv ℂ ℂ (Equiv.prodComm ι κ)
  have htrace (A : Matrix (ι × κ) (ι × κ) ℂ) :
      partialTraceLeft (e A) = partialTraceRight A := by
    simp only [← partialTraceRight_reindex_prodComm]
    rfl
  have hswap (A : Matrix κ κ ℂ) : e ((1 : Matrix ι ι ℂ) ⊗ₖ A) =
      A ⊗ₖ (1 : Matrix ι ι ℂ) := by
    ext i j
    exact mul_comm _ _
  have hstar (A : Matrix (ι × κ) (ι × κ) ℂ) : e Aᴴ = (e A)ᴴ := rfl
  rw [← htrace, ← htrace ρ, map_sum]
  simp only [map_mul, hstar, hswap]
  exact partialTraceLeft_kraus s K hK (e ρ)

end Cslib.Quantum

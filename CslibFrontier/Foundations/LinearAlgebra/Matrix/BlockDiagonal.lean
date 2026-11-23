/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, block-diagonal matrix calculus)

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Lagrange

/-!
# Block-diagonal matrices as operators

A block-diagonal matrix acts independently on each component of a vector. For Hermitian
blocks, the real continuous functional calculus also acts independently on each block.
Interpolate one polynomial on the finite union of the relevant spectra, then use that
block diagonalization commutes with polynomial evaluation.

## Main results

* `Matrix.blockDiagonal_mulVec_apply`: blockwise action on vectors.
* `Matrix.cfc_blockDiagonal`: blockwise evaluation in the functional calculus.
-/

public section

namespace Matrix

open Finset

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X]

/-- Matrix-vector multiplication by a block diagonal matrix is blockwise. -/
theorem blockDiagonal_mulVec_apply (A : X → Matrix ι ι ℂ) (v : ι × X → ℂ) (i : ι) (x : X) :
    (blockDiagonal A *ᵥ v) (i, x) = (A x *ᵥ fun j => v (j, x)) i := by
  unfold mulVec dotProduct
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  simp [blockDiagonal_apply, ite_mul]

variable [DecidableEq ι]

private def blockDiagonalAlgHom :
    (X → Matrix ι ι ℂ) →ₐ[ℝ] Matrix (ι × X) (ι × X) ℂ where
  toRingHom := blockDiagonalRingHom ι X ℂ
  commutes' z := by
    change blockDiagonal (fun _ : X => algebraMap ℝ (Matrix ι ι ℂ) z) = _
    simp only [Algebra.algebraMap_eq_smul_one]
    exact (blockDiagonal_smul z 1).trans (congrArg (z • ·) blockDiagonal_one)

/-- Evaluating a real function on a block-diagonal Hermitian matrix acts blockwise. -/
theorem cfc_blockDiagonal (f : ℝ → ℝ) (A : X → Matrix ι ι ℂ)
    (hA : ∀ x, (A x).IsHermitian) :
    cfc f (blockDiagonal A) = blockDiagonal (fun x => cfc f (A x)) := by
  classical
  have hbig : IsSelfAdjoint (blockDiagonal A) := by
    change (blockDiagonal A)ᴴ = blockDiagonal A
    rw [blockDiagonal_conjTranspose]
    exact congrArg blockDiagonal (funext hA)
  let T := spectrum ℝ (blockDiagonal A) ∪ ⋃ x, spectrum ℝ (A x)
  have hT : T.Finite := (blockDiagonal A).finite_real_spectrum.union
    (Set.finite_iUnion fun x => (A x).finite_real_spectrum)
  let P := Lagrange.interpolate hT.toFinset id f
  have hp (r : ℝ) (hr : r ∈ T) : P.eval r = f r :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) (hT.mem_toFinset.mpr hr)
  have hc (B : Matrix (ι × X) (ι × X) ℂ) (hB : IsSelfAdjoint B)
      (hsub : spectrum ℝ B ⊆ T) : cfc f B = Polynomial.aeval B P := by
    rw [← cfc_polynomial P B hB]
    exact cfc_congr fun r hr => (hp r (hsub hr)).symm
  have hc' (x : X) : cfc f (A x) = Polynomial.aeval (A x) P := by
    rw [← cfc_polynomial P (A x) (show IsSelfAdjoint (A x) from hA x)]
    exact cfc_congr fun r hr => (hp r (Or.inr (Set.mem_iUnion.mpr ⟨x, hr⟩))).symm
  rw [hc _ hbig (fun _ hr => Or.inl hr)]
  simp only [hc']
  let F : (X → Matrix ι ι ℂ) →ₐ[ℝ] Matrix (ι × X) (ι × X) ℂ := blockDiagonalAlgHom
  change Polynomial.aeval (F A) P = F (fun x => Polynomial.aeval (A x) P)
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]

end Matrix

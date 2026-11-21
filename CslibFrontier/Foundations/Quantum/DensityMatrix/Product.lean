/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.DensityMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# Tensor products of density matrices

Changing the basis labels by an equivalence or taking a tensor product preserves the
density-matrix conditions. A finite list of equal-dimensional independent registers
has basis strings indexed by a function on the register indices. The entries of their
joint density matrix are the products of the individual entries.

## Main definitions

* `Cslib.Quantum.productDensity`: the tensor product indexed by a tuple of basis labels.

## Main results

* `Cslib.Quantum.IsDensityMatrix.submatrix_equiv`: relabeling by an equivalence.
* `Cslib.Quantum.IsDensityMatrix.kronecker`: taking the product of two states.
* `Cslib.Quantum.isDensityMatrix_productDensity`: the tensor product is a density matrix.
-/

public section

namespace Cslib.Quantum

open scoped Kronecker ComplexOrder

/-- Relabeling both indices by the same equivalence preserves a density matrix. -/
theorem IsDensityMatrix.submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    {ρ : Matrix ι ι ℂ} (hρ : IsDensityMatrix ρ) (e : κ ≃ ι) :
    IsDensityMatrix (ρ.submatrix e e) := by
  refine ⟨hρ.posSemidef.submatrix e, ?_⟩
  change (∑ i, ρ (e i) (e i)) = 1
  exact (e.sum_comp fun i => ρ i i).trans hρ.trace_eq_one

/-- The Kronecker product represents two independent quantum states. -/
theorem IsDensityMatrix.kronecker {ι κ : Type*} [Fintype ι] [Fintype κ]
    {ρ : Matrix ι ι ℂ} {σ : Matrix κ κ ℂ} (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    IsDensityMatrix (ρ ⊗ₖ σ) :=
  ⟨hρ.posSemidef.kronecker hσ.posSemidef, by rw [Matrix.trace_kronecker, hρ.trace_eq_one,
    hσ.trace_eq_one, one_mul]⟩

/-- The density-matrix tensor product over independent registers with the same basis type. -/
def productDensity {ι : Type*} {k : ℕ} (ρ : Fin k → Matrix ι ι ℂ) :
    Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  Matrix.of fun x y => ∏ i, ρ i (x i) (y i)

/-- Tensor products of finite tuples of density matrices are density matrices. -/
theorem isDensityMatrix_productDensity {ι : Type*} [Fintype ι] {k : ℕ}
    (ρ : Fin k → Matrix ι ι ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) :
    IsDensityMatrix (productDensity ρ) := by
  induction k with
  | zero =>
    classical
    let zeroTuple : Fin 0 → ι := Fin.elim0
    have hz (z : Fin 0 → ι) : z = zeroTuple := funext fun i => i.elim0
    have heq : productDensity ρ = pureState (ket zeroTuple) := by
      ext x y
      rw [hz x, hz y]
      simp [productDensity, ket_apply]
    rw [heq]
    exact isDensityMatrix_pureState (norm_ket _)
  | succ k ih =>
    let e := (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).symm
    have ht := ((hρ 0).kronecker (ih (fun i => ρ i.succ) (fun i => hρ i.succ))).submatrix_equiv e
    convert ht using 1
    ext x y
    simp [productDensity, Fin.prod_univ_succ, Fin.tail, e]

end Cslib.Quantum

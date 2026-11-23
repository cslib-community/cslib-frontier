/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.SubstMatrix
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks

/-!
# Specialization matrices and closure properties of permanent projections

A polynomial over `K` is a projection of the `m × m` generic permanent
`(genericMatrix K m).permanent` if and only if it is the permanent of an `m × m` *specialization
matrix* (`IsSubstMatrix`), whose entries are variables `X i` or constants `C c` (`IsSubstEntry`).
Through block-diagonal specialization matrices, projections of generic permanents are closed under
multiplication (with dimensions adding) and monotone in the matrix dimension.

## Main results

* `Cslib.Circuits.Arithmetic.isProjection_permanent_iff_exists_isSubstMatrix`: `P` is a projection
  of `(genericMatrix K m).permanent` if and only if `P` is the permanent of an `m × m`
  specialization matrix.
* `Cslib.Circuits.Arithmetic.IsSubstMatrix.isProjection_permanent`: the permanent of a square
  specialization matrix on a finite type `α` is a projection of the `|α| × |α|` generic permanent.
* `Cslib.Circuits.Arithmetic.IsProjection.permanent_mul`: projections of generic permanents
  multiply by adding dimensions.
* `Cslib.Circuits.Arithmetic.isProjection_permanent_mono`: projections of generic permanents pad to
  any larger dimension.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*][Burgisser2000],
  Chapter 2
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

variable {K : Type u} [CommSemiring K] {m : ℕ} {σ : Type*}

/-- Applying a projection `ρ` to `(genericMatrix K m).permanent` gives the permanent of the
specialized matrix. -/
private theorem projection_permanent_genericMatrix (ρ : Fin (m * m) → σ ⊕ K) :
    projection ρ (genericMatrix K m).permanent =
      (Matrix.of fun i j : Fin m =>
        Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j)))).permanent := by
  rw [AlgHom.map_permanent]
  exact congrArg Matrix.permanent (Matrix.ext fun i j => by
    simp only [genericMatrix, Matrix.map_apply, Matrix.of_apply, projection_X])

namespace IsSubstMatrix

/-- The permanent of a square specialization matrix indexed by `α` is a projection of the
`|α| × |α|` generic permanent. -/
theorem isProjection_permanent {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α (MvPolynomial σ K)} (hM : IsSubstMatrix M) :
    IsProjection M.permanent (genericMatrix K (Fintype.card α)).permanent := by
  choose ρ hρ using hM
  let e := (Fintype.equivFin α).symm
  refine ⟨fun idx =>
    let pq := finProdFinEquiv.symm idx
    ρ (e pq.1) (e pq.2), ?_⟩
  rw [projection_permanent_genericMatrix, ← M.permanent_submatrix_equiv e]
  exact congrArg Matrix.permanent (Matrix.ext fun i j => by
    simpa only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using
      hρ (e i) (e j))

end IsSubstMatrix

/-- A polynomial `P` is a projection of `(genericMatrix K m).permanent` if and only if it is the
permanent of an `m × m` specialization matrix. -/
theorem isProjection_permanent_iff_exists_isSubstMatrix {P : MvPolynomial σ K} {m : ℕ} :
    IsProjection P (genericMatrix K m).permanent ↔
      ∃ M : Matrix (Fin m) (Fin m) (MvPolynomial σ K), IsSubstMatrix M ∧ M.permanent = P := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨Matrix.of fun i j => Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j))),
      fun i j => ⟨ρ (finProdFinEquiv (i, j)), rfl⟩,
      (projection_permanent_genericMatrix ρ).symm⟩
  · rintro ⟨M, hM, rfl⟩
    have h := hM.isProjection_permanent
    rwa [Fintype.card_fin] at h

/-- **Multiplicative closure of permanent projections**: if `P` is a projection of the `m × m`
generic permanent and `Q` is a projection of the `k × k` generic permanent, then `P * Q` is a
projection of the `(m + k) × (m + k)` generic permanent. -/
theorem IsProjection.permanent_mul {P Q : MvPolynomial σ K} {m k : ℕ}
    (hP : IsProjection P (genericMatrix K m).permanent)
    (hQ : IsProjection Q (genericMatrix K k).permanent) :
    IsProjection (P * Q) (genericMatrix K (m + k)).permanent := by
  obtain ⟨M₁, hM₁, rfl⟩ := isProjection_permanent_iff_exists_isSubstMatrix.mp hP
  obtain ⟨M₂, hM₂, rfl⟩ := isProjection_permanent_iff_exists_isSubstMatrix.mp hQ
  have h := (hM₁.fromBlocks .zero .zero hM₂).isProjection_permanent
  rwa [Matrix.permanent_fromBlocks_zero, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h

/-- **Monotonicity of permanent projections in the matrix dimension**: if `m ≤ k` and `P` is a
projection of `(genericMatrix K m).permanent`, then `P` is a projection of
`(genericMatrix K k).permanent`. -/
theorem isProjection_permanent_mono {P : MvPolynomial σ K} {m k : ℕ} (hmk : m ≤ k)
    (hP : IsProjection P (genericMatrix K m).permanent) :
    IsProjection P (genericMatrix K k).permanent := by
  have hone : IsProjection (1 : MvPolynomial σ K) (genericMatrix K (k - m)).permanent :=
    isProjection_permanent_iff_exists_isSubstMatrix.mpr ⟨1, .one, Matrix.permanent_one⟩
  have h := hP.permanent_mul hone
  rwa [mul_one, Nat.add_sub_of_le hmk] at h

end Cslib.Circuits.Arithmetic

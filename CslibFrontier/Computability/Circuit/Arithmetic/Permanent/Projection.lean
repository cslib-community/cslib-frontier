/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks

/-!
# Specialization matrices and closure properties of permanent projections

A polynomial over `K` is a projection of the `m × m` generic permanent
`(genericMatrix K m).permanent` if and only if it is the permanent of an `m × m` *specialization
matrix* (`IsSubstMatrix`), whose entries are variables `X i` or constants `C c` (`IsSubstEntry`).
Through block-diagonal specialization matrices, projections of generic permanents are closed under
multiplication (with dimensions adding) and monotone in the matrix dimension.

## Main definitions

* `Cslib.Circuits.Arithmetic.IsSubstEntry`: a polynomial that is a variable `X i` or a constant
  `C c`.
* `Cslib.Circuits.Arithmetic.IsSubstMatrix`: a matrix over `MvPolynomial σ K` whose entries satisfy
  `IsSubstEntry`.

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

/-- A polynomial in `MvPolynomial σ K` is a *projection substitution entry* if it is a variable
`X i` or a constant `C c`. -/
@[expose] def IsSubstEntry (p : MvPolynomial σ K) : Prop :=
  ∃ s : σ ⊕ K, Sum.elim X (fun a => C a) s = p

namespace IsSubstEntry

/-- Every constant polynomial `C c` is a substitution entry. -/
@[simp] theorem C (c : K) : IsSubstEntry (MvPolynomial.C c : MvPolynomial σ K) :=
  ⟨Sum.inr c, rfl⟩

/-- Every variable `X i` is a substitution entry. -/
@[simp] theorem X (i : σ) : IsSubstEntry (MvPolynomial.X i : MvPolynomial σ K) :=
  ⟨Sum.inl i, rfl⟩

/-- The zero polynomial is a substitution entry. -/
@[simp] theorem zero : IsSubstEntry (0 : MvPolynomial σ K) :=
  ⟨Sum.inr 0, map_zero _⟩

/-- The constant polynomial `1` is a substitution entry. -/
@[simp] theorem one : IsSubstEntry (1 : MvPolynomial σ K) :=
  ⟨Sum.inr 1, map_one _⟩

/-- Every numeral `n ≥ 2` is a substitution entry. -/
@[simp] theorem ofNat (n : ℕ) [n.AtLeastTwo] :
    IsSubstEntry (ofNat(n) : MvPolynomial σ K) :=
  ⟨Sum.inr (OfNat.ofNat n), map_ofNat MvPolynomial.C n⟩

end IsSubstEntry

/-- A matrix over `MvPolynomial σ K` is a *specialization matrix* if every entry is a variable
`X i` or a constant `C c` (`IsSubstEntry`). -/
@[expose] def IsSubstMatrix {α β : Type*} (M : Matrix α β (MvPolynomial σ K)) : Prop :=
  ∀ i j, IsSubstEntry (M i j)

namespace IsSubstMatrix

/-- The zero matrix is a specialization matrix. -/
@[simp] theorem zero {α β : Type*} : IsSubstMatrix (0 : Matrix α β (MvPolynomial σ K)) :=
  fun _ _ => .zero

/-- The identity matrix is a specialization matrix. -/
@[simp] theorem one {α : Type*} [DecidableEq α] :
    IsSubstMatrix (1 : Matrix α α (MvPolynomial σ K)) :=
  fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> [exact .one; exact .zero]

/-- A `2 × 2` block matrix built from specialization matrices is a specialization matrix. -/
theorem fromBlocks {α₁ α₂ β₁ β₂ : Type*}
    {A : Matrix α₁ β₁ (MvPolynomial σ K)} {B : Matrix α₁ β₂ (MvPolynomial σ K)}
    {C : Matrix α₂ β₁ (MvPolynomial σ K)} {D : Matrix α₂ β₂ (MvPolynomial σ K)}
    (hA : IsSubstMatrix A) (hB : IsSubstMatrix B) (hC : IsSubstMatrix C) (hD : IsSubstMatrix D) :
    IsSubstMatrix (Matrix.fromBlocks A B C D)
  | .inl i, .inl j => hA i j
  | .inl i, .inr j => hB i j
  | .inr i, .inl j => hC i j
  | .inr i, .inr j => hD i j

/-- Reindexing or selecting rows and columns preserves `IsSubstMatrix`. -/
theorem submatrix {α β α' β' : Type*} {M : Matrix α β (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) (f : α' → α) (g : β' → β) :
    IsSubstMatrix (M.submatrix f g) :=
  fun i j => hM (f i) (g j)

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

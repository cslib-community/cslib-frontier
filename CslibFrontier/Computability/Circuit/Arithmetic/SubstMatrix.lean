/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.VP
public import Mathlib.Data.Matrix.Block

/-!
# Specialization entries and specialization matrices

A polynomial in `MvPolynomial σ K` is a *projection substitution entry* (`IsSubstEntry`) when it is
a variable `X i` or a constant `C c`, that is, a single substituted value of
`Cslib.Circuits.Arithmetic.projection`. A matrix over `MvPolynomial σ K` is a *specialization
matrix* (`IsSubstMatrix`) when every entry satisfies `IsSubstEntry`. Specialization matrices are
closed under zero and identity matrices, `2 × 2` block matrices, and arbitrary row/column
selection (`Matrix.submatrix`), providing the common entry discipline for projections of generic
permanents and generic determinants.

## Main definitions

* `Cslib.Circuits.Arithmetic.IsSubstEntry`: a polynomial that is a variable `X i` or a constant
  `C c`.
* `Cslib.Circuits.Arithmetic.IsSubstMatrix`: a matrix over `MvPolynomial σ K` whose entries satisfy
  `IsSubstEntry`.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*][Burgisser2000],
  Chapter 2
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

section CommSemiring

variable {K : Type u} [CommSemiring K] {σ : Type*}

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

end IsSubstMatrix

end CommSemiring

namespace IsSubstEntry

variable {K : Type u} [CommRing K] {σ : Type*}

/-- The constant polynomial `-1` over a commutative ring is a substitution entry. -/
@[simp] theorem neg_one : IsSubstEntry (-1 : MvPolynomial σ K) :=
  ⟨Sum.inr (-1), by simp⟩

/-- Every integer cast over a commutative ring is a substitution entry. -/
@[simp] theorem intCast (z : ℤ) : IsSubstEntry (z : MvPolynomial σ K) :=
  ⟨Sum.inr z, map_intCast MvPolynomial.C z⟩

end IsSubstEntry

end Cslib.Circuits.Arithmetic

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SpanProgram.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Change of basis of a monotone span program

Multiplying every matrix `M_i` of a monotone span program on the right by one square matrix `R`
gives the program `(M_i * R)_i` of [Boneh and Shoup, Lemma 22.15, p. 982][BonehShoup2023]. When
`R` is invertible and its top row is `e₁`, the two programs accept the same coalitions: `R`
fixes the target vector `e₁`, and an invertible `R` maps a combination of rows to `e₁` exactly
when the combination itself is `e₁`. That the two programs also generate the same distribution
of shares is Lemma 22.15 itself, in
`CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.LinearEquivalence`.

## Main definitions

* `Cslib.Circuits.MonotoneSpanProgram.mulRight`: the program `(M_i * R)_i`.

## Main results

* `Cslib.Circuits.MonotoneSpanProgram.accepts_mulRight`: for an invertible `R` with top row
  `e₁`, both programs accept the same coalitions.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Lemma 22.15, p. 982.
-/

public section

open scoped Matrix

namespace Cslib.Circuits

namespace MonotoneSpanProgram

variable {F Party : Type*} [Field F]

/-- The span program whose matrices are `M_i * R` ([BonehShoup2023], Lemma 22.15, p. 982). It
has the same row dimensions and number of columns as `P`. -/
@[expose] def mulRight (P : MonotoneSpanProgram F Party)
    (R : Matrix (Fin (P.tailDim + 1)) (Fin (P.tailDim + 1)) F) : MonotoneSpanProgram F Party where
  tailDim := P.tailDim
  rowDim := P.rowDim
  matrix i := P.matrix i * R

@[simp]
theorem mulRight_matrix (P : MonotoneSpanProgram F Party)
    (R : Matrix (Fin (P.tailDim + 1)) (Fin (P.tailDim + 1)) F) (i : Party) :
    (P.mulRight R).matrix i = P.matrix i * R :=
  rfl

/-- Multiplying on the right by an invertible matrix whose top row is `e₁` does not change the
accepted coalitions. -/
theorem accepts_mulRight (P : MonotoneSpanProgram F Party)
    {R : Matrix (Fin (P.tailDim + 1)) (Fin (P.tailDim + 1)) F} (hR : IsUnit R.det)
    (htop : R 0 = Pi.single 0 1) (s : Finset Party) :
    (P.mulRight R).Accepts s ↔ P.Accepts s := by
  have htarget : P.target ᵥ* R = P.target := by
    rw [target, Matrix.single_one_vecMul]
    exact htop
  have hinj : Function.Injective fun w : Fin (P.tailDim + 1) → F => w ᵥ* R :=
    Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det R).2 hR)
  have key : ∀ w : (i : s) → Fin (P.rowDim i.1) → F,
      ∑ i : s, w i ᵥ* (P.mulRight R).matrix i.1 = (∑ i : s, w i ᵥ* P.matrix i.1) ᵥ* R := by
    intro w
    rw [Matrix.sum_vecMul]
    exact Finset.sum_congr rfl fun i _ => (Matrix.vecMul_vecMul _ _ _).symm
  rw [accepts_iff_exists_vecMul, accepts_iff_exists_vecMul]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, hinj ((key w).symm.trans (hw.trans htarget.symm))⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (key w).trans ((congrArg (· ᵥ* R) hw).trans htarget)⟩

end MonotoneSpanProgram

end Cslib.Circuits

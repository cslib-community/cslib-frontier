/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Formula
import CslibFrontier.Computability.Circuit.Arithmetic.Permanent.Projection
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks

/-!
# Arithmetic formulas are projections of the permanent

Every arithmetic formula `F : Formula (arithSignature K) n` computes a formal polynomial that
is a projection of the generic permanent of dimension `F.size + 1`. Here `K` is any commutative
semiring and `size` counts every operation node, including constants, with input leaves free.
Substitution uses `IsProjection`: each matrix entry is a variable or a scalar, without an extra
scalar multiplier on the result.

This is the permanent's formula-simulation property [Valiant][Valiant1979Algebra;
Orzel et al., Definition 1 and Lemma 4][OrzelSrinivasanTavenasYehudayoff2025].
The explicit linear bound and semiring generality are proved directly. Orzel et al. work over
fields of characteristic other than two and permit a nonzero scalar multiplier in projections;
neither restriction nor multiplier is needed for formula simulation. Valiant's full
`VNP`-hardness reduction and uniform construction runtime are not formalized here.

Each subformula is represented by a specialization matrix (`IsSubstMatrix`) on `Unit ⊕ α` with
one distinguished root whose internal block on `α` has permanent `1`. Addition and multiplication
combine two rooted matrices by adjoining one internal `Unit` vertex, and the final matrix is
padded to dimension `F.size + 1` via `IsSubstMatrix.isProjection_permanent` and
`isProjection_permanent_mono`.

## Main results

* `Cslib.Circuits.Formula.isProjection_permanent`: dimension `F.size + 1` suffices;
  `Cslib.Circuits.Formula.isProjection_permanent_toCircuit` states the same bound for
  `F.toCircuit.polynomial 0`.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [I. Orzel et al., *The Algebraic Cost of a Boolean Sum*][OrzelSrinivasanTavenasYehudayoff2025],
  Definition 1 (p. 47:3), Lemma 4 (p. 47:4) and projection conventions (p. 47:5)
-/

public section

namespace Matrix

open Equiv Equiv.Perm

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

/-- Involution on `(Unit ⊕ m) ⊕ (Unit ⊕ n)` swapping the two root elements `inl (inl ())` and
`inr (inl ())`. -/
private def swapRootEquiv (m n : Type*) :
    ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ≃ ((Unit ⊕ m) ⊕ (Unit ⊕ n)) :=
  let f : (Unit ⊕ m) ⊕ (Unit ⊕ n) → (Unit ⊕ m) ⊕ (Unit ⊕ n)
    | .inl (.inl u) => .inr (.inl u)
    | .inl (.inr i) => .inl (.inr i)
    | .inr (.inl u) => .inl (.inl u)
    | .inr (.inr j) => .inr (.inr j)
  have hf : Function.Involutive f := by rintro ((⟨⟨⟩⟩ | _) | (⟨⟨⟩⟩ | _)) <;> rfl
  hf.toPerm

/-- Rooted permanent multiplication block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
private def rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks M₁ 0 (fromBlocks (1 : Matrix Unit Unit R) 0 0 0) M₂).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    ((Equiv.sumAssoc Unit m (Unit ⊕ n)).symm.trans (swapRootEquiv m n))

/-- The permanent of `rootedMul M₁ M₂` is the product of the permanents of `M₁` and `M₂`. -/
private theorem permanent_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    (rootedMul M₁ M₂).permanent = M₁.permanent * M₂.permanent := by
  rw [rootedMul, permanent_submatrix_equiv_equiv, permanent_fromBlocks_zero₁₂]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedMul M₁ M₂`. -/
private theorem permanent_toBlocks₂₂_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedMul M₁ M₂).toBlocks₂₂.permanent = 1 := by
  rw [show (rootedMul M₁ M₂).toBlocks₂₂ =
      fromBlocks M₁.toBlocks₂₂ (of fun i => Sum.elim (M₁.toBlocks₂₁ i) 0) 0
        (fromBlocks (1 : Matrix Unit Unit R) M₂.toBlocks₁₂ 0 M₂.toBlocks₂₂) by
    ext (_ | (⟨⟩ | _)) (_ | (⟨⟩ | _)) <;> rfl,
    permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₂₁, permanent_one, h₁, h₂,
    mul_one, mul_one]

/-- Rooted permanent addition block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
private def rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks
    M₁
    (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedAdd M₁ M₂`. -/
private theorem permanent_toBlocks₂₂_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).toBlocks₂₂.permanent = 1 := by
  rw [show (rootedAdd M₁ M₂).toBlocks₂₂ = fromBlocks M₁.toBlocks₂₂ 0 0
      (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂) by
    ext (_ | (⟨⟩ | _)) (_ | (⟨⟩ | _)) <;> rfl,
    permanent_fromBlocks_zero, permanent_fromBlocks_zero₁₂, permanent_one, h₁, h₂,
    mul_one, mul_one]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then the permanent of
`rootedAdd M₁ M₂` is the sum of the permanents of `M₁` and `M₂`. -/
private theorem permanent_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).permanent = M₁.permanent + M₂.permanent := by
  rw [rootedAdd, permanent_submatrix_equiv]
  let r : (Unit ⊕ m) ⊕ (Unit ⊕ n) := .inr (.inl ())
  let B₁ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0) 0
      (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  let B₂ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
      (fromBlocks (0 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  rw [show fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
        (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
        (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂) =
      B₁.updateRow r (B₁ r + B₂ r) by
    ext ((⟨⟨⟩⟩ | _) | (⟨⟨⟩⟩ | _)) ((⟨⟨⟩⟩ | _) | (⟨⟨⟩⟩ | _)) <;> simp [B₁, B₂, r],
    permanent_updateRow_add, updateRow_eq_self, show B₁.updateRow r (B₂ r) = B₂ by
    ext ((⟨⟨⟩⟩ | _) | (⟨⟨⟩⟩ | _)) ((⟨⟨⟩⟩ | _) | (⟨⟨⟩⟩ | _)) <;> simp [B₁, B₂, r]]
  congr 1
  · rw [permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₁₂, permanent_one, h₂, mul_one,
      mul_one]
  · rw [← permanent_submatrix_equiv_equiv (swapRootEquiv m n) (Equiv.refl _),
      show B₂.submatrix (swapRootEquiv m n) (Equiv.refl _) =
        fromBlocks (fromBlocks (1 : Matrix Unit Unit R) 0 M₁.toBlocks₂₁ M₁.toBlocks₂₂) 0
          (fromBlocks M₁.toBlocks₁₁ M₁.toBlocks₁₂ 0 0) M₂ by
        ext ((⟨⟨⟩⟩ | _) | (⟨⟨⟩⟩ | _)) ((⟨⟨⟩⟩ | _) | (⟨⟨⟩⟩ | _)) <;> rfl,
      permanent_fromBlocks_zero₁₂, permanent_fromBlocks_zero₁₂, permanent_one, h₁, mul_one,
      one_mul]

end Matrix

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

variable {K : Type u} [CommSemiring K] {n : ℕ} {σ : Type*}

namespace IsSubstMatrix

private theorem rootedMul {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ K)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ K)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedMul M₁ M₂) :=
  (h₁.fromBlocks .zero (IsSubstMatrix.one.fromBlocks .zero .zero .zero) h₂).submatrix _ _

private theorem rootedAdd {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ K)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ K)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedAdd M₁ M₂) :=
  (h₁.fromBlocks
    ((h₂.submatrix Sum.inl Sum.inl).fromBlocks (h₂.submatrix Sum.inl Sum.inr) .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero (h₂.submatrix Sum.inr Sum.inl)
      (h₂.submatrix Sum.inr Sum.inr))).submatrix _ _

end IsSubstMatrix

/-- A polynomial `P` has a *rooted permanent representation* on internal vertices `α` if it is the
permanent of a specialization matrix `M` on `Unit ⊕ α` whose internal block `M.toBlocks₂₂` has
permanent `1`. -/
private def IsRootedPerm (α : Type) [Fintype α] [DecidableEq α] (P : MvPolynomial σ K) : Prop :=
  ∃ M : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ K),
    IsSubstMatrix M ∧ M.toBlocks₂₂.permanent = 1 ∧ M.permanent = P

namespace IsRootedPerm

/-- Every single-entry substitution `P` (a variable or constant) has a rooted permanent
representation with empty internal block. -/
private theorem of_isSubstEntry {P : MvPolynomial σ K} (hP : IsSubstEntry P) :
    IsRootedPerm Empty P := by
  refine ⟨Matrix.fromBlocks (Matrix.of fun _ _ => P) 0 0 0,
    IsSubstMatrix.fromBlocks (fun _ _ => hP) .zero .zero .zero,
    Matrix.permanent_isEmpty, ?_⟩
  rw [Matrix.permanent_fromBlocks_zero, Matrix.permanent_unique, Matrix.permanent_isEmpty, mul_one]
  rfl

/-- Additive closure of rooted permanent representations, adjoining one internal vertex. -/
private theorem add {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P Q : MvPolynomial σ K} (hP : IsRootedPerm α P) (hQ : IsRootedPerm β Q) :
    IsRootedPerm (α ⊕ (Unit ⊕ β)) (P + Q) := by
  rcases hP, hQ with ⟨⟨M₁, hM₁, hU₁, rfl⟩, ⟨M₂, hM₂, hU₂, rfl⟩⟩
  exact ⟨Matrix.rootedAdd M₁ M₂, hM₁.rootedAdd hM₂,
    Matrix.permanent_toBlocks₂₂_rootedAdd M₁ M₂ hU₁ hU₂,
    Matrix.permanent_rootedAdd M₁ M₂ hU₁ hU₂⟩

/-- Multiplicative closure of rooted permanent representations, adjoining one internal vertex. -/
private theorem mul {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {P Q : MvPolynomial σ K} (hP : IsRootedPerm α P) (hQ : IsRootedPerm β Q) :
    IsRootedPerm (α ⊕ (Unit ⊕ β)) (P * Q) := by
  rcases hP, hQ with ⟨⟨M₁, hM₁, hU₁, rfl⟩, ⟨M₂, hM₂, hU₂, rfl⟩⟩
  exact ⟨Matrix.rootedMul M₁ M₂, hM₁.rootedMul hM₂,
    Matrix.permanent_toBlocks₂₂_rootedMul M₁ M₂ hU₁ hU₂,
    Matrix.permanent_rootedMul M₁ M₂⟩

end IsRootedPerm

omit [CommSemiring K] in
private theorem card_sum_unit_le_size {α₀ α₁ : Type} [Fintype α₀] [Fintype α₁]
    (args : Fin 2 → Formula (arithSignature K) n)
    (h₀ : Fintype.card α₀ ≤ (args 0).size) (h₁ : Fintype.card α₁ ≤ (args 1).size) :
    Fintype.card (α₀ ⊕ (Unit ⊕ α₁)) ≤ (∑ j : Fin 2, (args j).size) + 1 := by
  simp only [Fintype.card_sum, Fintype.card_unique, Fin.sum_univ_two]
  omega

/-- Every arithmetic formula `F` computes a polynomial with a rooted permanent representation on
at most `F.size` internal vertices. -/
private theorem _root_.Cslib.Circuits.Formula.exists_isRootedPerm
    (F : Formula (arithSignature K) n) :
    ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α),
      Fintype.card α ≤ F.size ∧
      IsRootedPerm α (F.eval (arithInterpretationWith K C) X) := by
  induction F with
  | input i => exact ⟨Empty, inferInstance, inferInstance, le_rfl, .of_isSubstEntry (.X i)⟩
  | gate op args ih =>
    cases op with
    | const c => exact ⟨Empty, inferInstance, inferInstance, Nat.zero_le _, .of_isSubstEntry (.C c)⟩
    | add =>
      obtain ⟨α₀, _, _, h₀, hM₀⟩ := ih 0
      obtain ⟨α₁, _, _, h₁, hM₁⟩ := ih 1
      exact ⟨_, inferInstance, inferInstance, card_sum_unit_le_size args h₀ h₁, hM₀.add hM₁⟩
    | mul =>
      obtain ⟨α₀, _, _, h₀, hM₀⟩ := ih 0
      obtain ⟨α₁, _, _, h₁, hM₁⟩ := ih 1
      exact ⟨_, inferInstance, inferInstance, card_sum_unit_le_size args h₀ h₁, hM₀.mul hM₁⟩

/-- **Formula universality for the permanent**: the formal polynomial computed by an
arithmetic formula `F` is a projection of the `(F.size + 1) × (F.size + 1)` generic permanent.
This gives an explicit semiring version of the permanent part of
[Orzel et al., Lemma 4][OrzelSrinivasanTavenasYehudayoff2025]. `size` counts operation nodes,
including constants; the linear dimension bound is proved directly by the construction. -/
theorem _root_.Cslib.Circuits.Formula.isProjection_permanent
    (F : Formula (arithSignature K) n) :
    IsProjection (F.eval (arithInterpretationWith K C) X)
      (genericMatrix K (F.size + 1)).permanent := by
  obtain ⟨α, _, _, hα, M, hM, -, hperm⟩ := F.exists_isRootedPerm
  exact hperm ▸ isProjection_permanent_mono
    (by simp only [Fintype.card_sum, Fintype.card_unique]; omega) hM.isProjection_permanent

/-- The formal polynomial `(F.toCircuit).polynomial 0` of any arithmetic formula `F` is a
projection of `(genericMatrix K (F.size + 1)).permanent`. -/
theorem _root_.Cslib.Circuits.Formula.isProjection_permanent_toCircuit
    (F : Formula (arithSignature K) n) :
    IsProjection (F.toCircuit.polynomial 0) (genericMatrix K (F.size + 1)).permanent := by
  simpa [Circuit.polynomial] using F.isProjection_permanent

end Cslib.Circuits.Arithmetic

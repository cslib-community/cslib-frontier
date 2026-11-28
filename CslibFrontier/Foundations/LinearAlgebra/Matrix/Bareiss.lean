/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Sylvester–Bareiss minor identity and fraction-free Gauss–Jordan)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
public import Mathlib.LinearAlgebra.Matrix.Rank
import CslibFrontier.Tactic.FinIndex
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.LinearCombination

/-!
# Bareiss fraction-free Gauss–Jordan elimination and Sylvester minor identities

This module develops the pure matrix theory behind fraction-free (Bareiss / Edmonds) Gauss–Jordan
elimination and reduced row echelon form over fields and the integers:

* Bordering determinants (`Matrix.border`) satisfy the Schur-complement expansion
  `Matrix.det_border`, yielding both the 2×2 Sylvester / Desnanot–Jacobi identity
  (`Matrix.det_mul_det_fromBlocks_fin2`) and the upward Gauss–Jordan minor identity
  (`Matrix.det_mul_det_border_updateCol`).
* For a matrix `A : Matrix (Fin m) (Fin n) R` and pivot selections `S : Fin k → Fin m`,
  `C : Fin k → Fin n`, `Matrix.bareissMatrix A S C` stores the exact `k × k` minor determinants on
  pivoted rows `S a` and `(k + 1) × (k + 1)` minor determinants on unpivoted rows.
* Over `ℤ`, every Bareiss–Jordan step preserves exact integer divisibility by `pivotDet A S C`
  (`Matrix.pivotDet_dvd_bareissStep_int`), computes the next minor via `Int.ediv`
  (`Matrix.bareissStep_ediv_eq_int`), and obeys the Hadamard/factorial minor bound
  (`Matrix.abs_bareissMatrix_le`).
* Over any field `K`, scaling by `(pivotDet A S C)⁻¹` yields `Matrix.rrefOfBareiss A S C`, which
  preserves row space, rank, and kernel, produces a `LinearIndependent` row basis, a
  `LinearIndependent` kernel basis (`Matrix.kernelBasisVec`) spanning `LinearMap.ker A.mulVecLin`,
  a `Matrix.IsReducedRowEchelon` / `Matrix.IsPivotedBy` presentation under row permutation, and a
  canonical solution vector `Matrix.solveVec A S C b` whenever `A *ᵥ x = b` is consistent.

## References

* A. Schrijver, *Theory of Linear and Integer Programming* [Schrijver1986].
-/

public section

namespace Matrix

open Finset Submodule
open scoped Matrix BigOperators

/-! ### Block bordering and Sylvester / Cramer–Jordan determinant identities -/

section Identities

variable {R : Type*} {k : ℕ}

/-- Border a `k × k` matrix `A` on the right by column `b`, below by row `c`, and in the
bottom-right corner by scalar `d`. -/
@[expose] def border (A : Matrix (Fin k) (Fin k) R) (b c : Fin k → R) (d : R) :
    Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) R :=
  fromBlocks A (of fun i _ => b i) (of fun _ j => c j) (of fun _ _ => d)

@[simp]
theorem map_border {S' : Type*} [CommRing R] [CommRing S'] (f : R →+* S')
    (A : Matrix (Fin k) (Fin k) R) (b c : Fin k → R) (d : R) :
    (border A b c d).map f = border (A.map f) (f ∘ b) (f ∘ c) (f d) := by
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> rfl

variable {K : Type*} [Field K]

/-- Schur-complement determinant expansion of a bordered matrix around an invertible leading block
`A`. -/
theorem det_border {A : Matrix (Fin k) (Fin k) K} (hA : A.det ≠ 0) (b c : Fin k → K) (d : K) :
    (border A b c d).det = A.det * (d - c ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  let _ : Invertible A := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  rw [border, det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_unique (n := Unit), Matrix.mul_assoc]
  rfl

/-- Multiplying by an invertible matrix undoes multiplying by its inverse. -/
private theorem mulVec_inv_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι K}
    (hA : A.det ≠ 0) (b : ι → K) : A *ᵥ (A⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA), one_mulVec]

/-- **Cramer's rule**, coordinatewise: `det A` times coordinate `a` of `A⁻¹ *ᵥ b` is the determinant
of `A` with column `a` replaced by `b`. -/
private theorem det_mul_inv_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι K}
    (hA : A.det ≠ 0) (b : ι → K) (a : ι) : A.det * (A⁻¹ *ᵥ b) a = (A.updateCol a b).det := by
  rw [← cramer_apply, ← det_smul_inv_mulVec_eq_cramer A b (isUnit_iff_ne_zero.mpr hA)]
  rfl

/-- **Sylvester / Desnanot–Jacobi 2×2 determinant identity**: multiplying a `(k + 2) × (k + 2)`
block matrix determinant by its invertible `k × k` leading principal minor equals the 2×2
determinant of its `(k + 1) × (k + 1)` bordered minors. -/
theorem det_mul_det_fromBlocks_fin2 {A : Matrix (Fin k) (Fin k) K} (hA : A.det ≠ 0)
    (b₀ b₁ c₀ c₁ : Fin k → K) (d₀₀ d₀₁ d₁₀ d₁₁ : K) :
    A.det *
        (fromBlocks A
          (of fun i (j : Fin 2) => if j = 0 then b₀ i else b₁ i)
          (of fun (i : Fin 2) j => if i = 0 then c₀ j else c₁ j)
          ![![d₀₀, d₀₁], ![d₁₀, d₁₁]]).det =
      (border A b₀ c₀ d₀₀).det * (border A b₁ c₁ d₁₁).det -
        (border A b₀ c₁ d₁₀).det * (border A b₁ c₀ d₀₁).det := by
  let _ : Invertible A := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  set D : Matrix (Fin 2) (Fin 2) K := ![![d₀₀, d₀₁], ![d₁₀, d₁₁]]
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, det_fin_two, Matrix.mul_assoc]
  simp only [det_border hA]
  -- entry `(u, v)` of the Schur complement `D - C * (A⁻¹ * B)` is `D u v - C u ⬝ᵥ (A⁻¹ *ᵥ B v)`
  change A.det * (A.det * ((d₀₀ - c₀ ⬝ᵥ (A⁻¹ *ᵥ b₀)) * (d₁₁ - c₁ ⬝ᵥ (A⁻¹ *ᵥ b₁)) -
    (d₀₁ - c₀ ⬝ᵥ (A⁻¹ *ᵥ b₁)) * (d₁₀ - c₁ ⬝ᵥ (A⁻¹ *ᵥ b₀)))) = _
  ring

/-- **Cramer–Jordan upward elimination minor identity**: updating column `a` of an invertible
`(k + 1) × (k + 1)` bordered matrix `M = border A b₁ c d₁` by `(b₂, d₂)` satisfies the
fraction-free Gauss–Jordan identity
`A.det * det M' = det M * det (A[a ↦ b₂]) - det(border A b₂ c d₂) * det (A[a ↦ b₁])`. -/
theorem det_mul_det_border_updateCol {A : Matrix (Fin k) (Fin k) K} (hA : A.det ≠ 0)
    (b₁ c : Fin k → K) (d₁ : K) (hM : (border A b₁ c d₁).det ≠ 0)
    (b₂ : Fin k → K) (d₂ : K) (a : Fin k) :
    A.det * ((border A b₁ c d₁).updateCol (Sum.inl a) (Sum.elim b₂ fun _ => d₂)).det =
      (border A b₁ c d₁).det * (A.updateCol a b₂).det -
        (border A b₂ c d₂).det * (A.updateCol a b₁).det := by
  -- Cramer's rule and the Schur complement express every determinant through `x = M⁻¹ (b₂, d₂)`,
  -- `A⁻¹ b₁` and `A⁻¹ b₂`
  rw [← det_mul_inv_mulVec_apply hM, ← det_mul_inv_mulVec_apply hA, ← det_mul_inv_mulVec_apply hA,
    det_border hA, det_border hA]
  have hMx := mulVec_inv_mulVec hM (Sum.elim b₂ fun _ => d₂)
  generalize (border A b₁ c d₁)⁻¹ *ᵥ (Sum.elim b₂ fun _ => d₂) = x at hMx ⊢
  -- the two block rows of `border A b₁ c d₁ *ᵥ x = (b₂, d₂)`
  have h₁ : A *ᵥ (x ∘ Sum.inl) + x (Sum.inr ()) • b₁ = b₂ := funext fun t => by
    simpa [border, mulVec, dotProduct, mul_comm] using congrFun hMx (Sum.inl t)
  have h₂ : c ⬝ᵥ (x ∘ Sum.inl) + d₁ * x (Sum.inr ()) = d₂ := by
    simpa [border, mulVec, dotProduct] using congrFun hMx (Sum.inr ())
  have hx₁ : x ∘ Sum.inl = A⁻¹ *ᵥ b₂ - x (Sum.inr ()) • A⁻¹ *ᵥ b₁ := by
    rw [← mulVec_smul, ← mulVec_sub, ← h₁, add_sub_cancel_right, mulVec_mulVec,
      nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), one_mulVec]
  rw [hx₁, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h₂
  have ha : x (Sum.inl a) = (A⁻¹ *ᵥ b₂) a - x (Sum.inr ()) * (A⁻¹ *ᵥ b₁) a := congrFun hx₁ a
  linear_combination A.det ^ 2 * (d₁ - c ⬝ᵥ (A⁻¹ *ᵥ b₁)) * ha -
    A.det ^ 2 * (A⁻¹ *ᵥ b₁) a * h₂

end Identities

/-! ### Minor-scaled Bareiss–Jordan matrices -/

section MinorMatrix

variable {m n k : ℕ}

/-- Determinant of the `k × k` pivot submatrix indexed by row selection `S` and column selection
`C`. -/
@[expose] def pivotDet {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin k → Fin m) (C : Fin k → Fin n) : R :=
  (A.submatrix S C).det

@[simp]
theorem pivotDet_zero {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin 0 → Fin m) (C : Fin 0 → Fin n) : pivotDet A S C = 1 :=
  det_fin_zero

@[simp]
theorem map_pivotDet {R S' : Type*} [CommRing R] [CommRing S'] (f : R →+* S')
    (A : Matrix (Fin m) (Fin n) R) (S : Fin k → Fin m) (C : Fin k → Fin n) :
    f (pivotDet A S C) = pivotDet (A.map f) S C := by
  rw [pivotDet, pivotDet, RingHom.map_det]
  rfl

/-- If `pivotDet A S C ≠ 0`, both the row selection `S` and the column selection `C` are
injective. -/
theorem injective_of_pivotDet_ne_zero {R : Type*} [CommRing R] {A : Matrix (Fin m) (Fin n) R}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (h : pivotDet A S C ≠ 0) :
    Function.Injective S ∧ Function.Injective C :=
  ⟨fun _ _ ha => by_contra fun hne =>
      h (det_zero_of_row_eq hne (funext fun b => by simp only [submatrix_apply, ha])),
    fun _ _ hb => by_contra fun hne =>
      h (det_zero_of_column_eq hne fun a => by simp only [submatrix_apply, hb])⟩

/-- The minor-scaled Bareiss–Jordan matrix associated with pivot rows `S` and pivot columns `C`.
For a pivoted row `i = S a`, entry `(i, j)` is the `k × k` minor obtained by replacing column `C a`
with `j`. For an unpivoted row `i ∉ range S`, entry `(i, j)` is the `(k + 1) × (k + 1)` minor
obtained by bordering `A.submatrix S C` with row `i` and column `j`. -/
noncomputable def bareissMatrix {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin k → Fin m) (C : Fin k → Fin n) : Matrix (Fin m) (Fin n) R := by
  classical
  exact Matrix.of fun i j =>
    if h : ∃ a : Fin k, S a = i then
      (A.submatrix S (Function.update C h.choose j)).det
    else
      (A.submatrix (Fin.snoc S i) (Fin.snoc C j)).det

/-- Entry of `bareissMatrix A S C` on a pivoted row `S a`. -/
theorem bareissMatrix_pivot {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (hS : Function.Injective S) (C : Fin k → Fin n)
    (a : Fin k) (j : Fin n) :
    bareissMatrix A S C (S a) j = (A.submatrix S (Function.update C a j)).det := by
  classical
  have hex : ∃ b : Fin k, S b = S a := ⟨a, rfl⟩
  rw [bareissMatrix, of_apply, dite_eq_left hex, hS hex.choose_spec]

/-- Entry of `bareissMatrix A S C` on an unpivoted row `i`. -/
theorem bareissMatrix_nonPivot {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (C : Fin k → Fin n) {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) (j : Fin n) :
    bareissMatrix A S C i j = (A.submatrix (Fin.snoc S i) (Fin.snoc C j)).det := by
  classical
  rw [bareissMatrix, of_apply, dite_eq_right fun ⟨a, ha⟩ => hi a ha]

@[simp]
theorem bareissMatrix_zero {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin 0 → Fin m) (C : Fin 0 → Fin n) :
    bareissMatrix A S C = A := by
  ext i j
  rw [bareissMatrix_nonPivot A C (fun a => a.elim0) j, det_fin_one]
  rfl

/-- Mapping a matrix by a ring homomorphism commutes with `bareissMatrix`. -/
theorem map_bareissMatrix {R S' : Type*} [CommRing R] [CommRing S'] (f : R →+* S')
    (A : Matrix (Fin m) (Fin n) R) (S : Fin k → Fin m) (C : Fin k → Fin n) :
    (bareissMatrix A S C).map f = bareissMatrix (A.map f) S C := by
  classical
  ext i j
  simp only [bareissMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h <;> rw [RingHom.map_det] <;> rfl

/-- On a pivoted row `S a`, entry `(S a, C a)` equals `pivotDet A S C`. -/
theorem bareissMatrix_pivot_col_self {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (hS : Function.Injective S) (C : Fin k → Fin n) (a : Fin k) :
    bareissMatrix A S C (S a) (C a) = pivotDet A S C := by
  rw [bareissMatrix_pivot A hS C a (C a), Function.update_eq_self]
  rfl

/-- On a pivoted row `S a`, every other pivot column `C b` (`a ≠ b`) vanishes. -/
theorem bareissMatrix_pivot_col_ne {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (hS : Function.Injective S) (C : Fin k → Fin n)
    {a b : Fin k} (hab : a ≠ b) :
    bareissMatrix A S C (S a) (C b) = 0 := by
  rw [bareissMatrix_pivot A hS C a (C b)]
  exact det_zero_of_column_eq hab fun t => by
    simp only [submatrix_apply, Function.update_self, Function.update_of_ne hab.symm]

/-- On an unpivoted row `i`, every pivot column `C b` vanishes. -/
theorem bareissMatrix_nonPivot_col {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    {S : Fin k → Fin m} (C : Fin k → Fin n) {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) (b : Fin k) :
    bareissMatrix A S C i (C b) = 0 := by
  rw [bareissMatrix_nonPivot A C hi (C b)]
  exact det_zero_of_column_eq b.castSucc_ne_last fun t => by
    simp only [submatrix_apply, Fin.snoc_castSucc, Fin.snoc_last]

private def sumUnitEquiv (k : ℕ) : Fin k ⊕ Unit ≃ Fin (k + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin k)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

private theorem sumUnitEquiv_inl (k : ℕ) (a : Fin k) : sumUnitEquiv k (Sum.inl a) = a.castSucc :=
  rfl

private theorem sumUnitEquiv_inr (k : ℕ) (u : Unit) : sumUnitEquiv k (Sum.inr u) = Fin.last k :=
  rfl

private theorem det_snoc_eq_det_border {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin n) R)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (p : Fin m) (q : Fin n) :
    (A.submatrix (Fin.snoc S p) (Fin.snoc C q)).det =
      (border (A.submatrix S C) (fun a => A (S a) q) (fun b => A p (C b)) (A p q)).det := by
  rw [← det_submatrix_equiv_self (sumUnitEquiv k)]
  congr 1
  ext (i | ⟨⟩) (j | ⟨⟩) <;> simp [border, sumUnitEquiv_inl, sumUnitEquiv_inr]

/-- Replacing a selected column commutes with taking the submatrix. -/
private theorem submatrix_update_col {R : Type*} (A : Matrix (Fin m) (Fin n) R)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (a : Fin k) (j : Fin n) :
    A.submatrix S (Function.update C a j) = (A.submatrix S C).updateCol a fun t => A (S t) j := by
  ext u v
  simp only [submatrix_apply, updateCol_apply, Function.update_apply]
  split_ifs <;> rfl

/-- The minor on rows `S, p` and columns `C, q` with column `C a` replaced by column `j` is the
bordered matrix of `det_snoc_eq_det_border` with its column `a` replaced by column `j` of `A`. -/
private theorem det_snoc_update_eq_det_border_updateCol {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin n) R) (S : Fin k → Fin m) (C : Fin k → Fin n) (p : Fin m) (q : Fin n)
    (a : Fin k) (j : Fin n) :
    (A.submatrix (Fin.snoc S p) (Function.update (Fin.snoc C q) a.castSucc j)).det =
      ((border (A.submatrix S C) (fun t => A (S t) q) (fun t => A p (C t)) (A p q)).updateCol
        (Sum.inl a) (Sum.elim (fun t => A (S t) j) fun _ => A p j)).det := by
  rw [← det_submatrix_equiv_self (sumUnitEquiv k)]
  congr 1
  ext (u | ⟨⟩) (v | ⟨⟩) <;>
    simp [border, updateCol_apply, sumUnitEquiv_inl, sumUnitEquiv_inr, Function.update_apply,
      apply_ite (A _), (Fin.castSucc_lt_last a).ne']

/-- Appending two entries to a tuple, read through `finSumFinEquiv`. -/
private theorem snoc_snoc_finSumFinEquiv {α : Type*} (f : Fin k → α) (x y : α)
    (u : Fin k ⊕ Fin 2) :
    (Fin.snoc (Fin.snoc f x) y : Fin (k + 1 + 1) → α) (finSumFinEquiv (m := k) (n := 2) u) =
      Sum.elim f ![x, y] u := by
  rcases u with t | u
  · exact (Fin.snoc_castSucc (α := fun _ => α) y _ t.castSucc).trans (Fin.snoc_castSucc ..)
  · fin_cases u <;> simp [Fin.snoc]

/-- The minor on rows `S, p, i` and columns `C, q, j` is the determinant of the block matrix with
leading block `A.submatrix S C` appearing in `det_mul_det_fromBlocks_fin2`. -/
private theorem det_snoc_snoc_eq_det_fromBlocks {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin n) R) (S : Fin k → Fin m) (C : Fin k → Fin n) (p i : Fin m)
    (q j : Fin n) :
    (A.submatrix (Fin.snoc (Fin.snoc S p) i) (Fin.snoc (Fin.snoc C q) j)).det =
      (fromBlocks (A.submatrix S C)
        (of fun u (v : Fin 2) => if v = 0 then A (S u) q else A (S u) j)
        (of fun (u : Fin 2) v => if u = 0 then A p (C v) else A i (C v))
        ![![A p q, A p j], ![A i q, A i j]]).det := by
  rw [← det_submatrix_equiv_self (finSumFinEquiv (m := k) (n := 2))]
  congr 1
  ext u v
  simp only [submatrix_apply, snoc_snoc_finSumFinEquiv]
  rcases u with u | u <;> rcases v with v | v <;> [rfl; fin_cases v; fin_cases u;
    (fin_cases u <;> fin_cases v)] <;> rfl

/-- **Main Bareiss–Jordan identity over any field `K`:** appending a pivot `(p, q)` with
`p ∉ range S` and `bareissMatrix A S C p q ≠ 0` updates every row `i ≠ p` via the Sylvester /
Cramer–Jordan quotient by `pivotDet A S C`, and keeps row `p` unchanged. -/
theorem pivotDet_mul_bareissMatrix_snoc {K : Type*} [Field K] (A : Matrix (Fin m) (Fin n) K)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) (i : Fin m) (j : Fin n) :
    (i = p → bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j = bareissMatrix A S C p j) ∧
      (i ≠ p →
        pivotDet A S C * bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j =
          bareissMatrix A S C p q * bareissMatrix A S C i j -
            bareissMatrix A S C i q * bareissMatrix A S C p j) := by
  have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
  have hS'inj : Function.Injective (Fin.snoc S p) :=
    Fin.snoc_injective_of_injective hSinj fun ⟨a, ha⟩ => hp a ha
  refine ⟨?_, fun hne => ?_⟩
  · -- the new pivot row is unchanged
    rintro rfl
    have h1 := bareissMatrix_pivot A hS'inj (Fin.snoc C q) (Fin.last k) j
    rwa [Fin.snoc_last, Fin.update_snoc_last, ← bareissMatrix_nonPivot A C hp j] at h1
  by_cases hrow : ∃ a : Fin k, S a = i
  · -- an old pivot row: the Cramer–Jordan identity `det_mul_det_border_updateCol`
    obtain ⟨a, rfl⟩ := hrow
    have hM : (border (A.submatrix S C) (fun t => A (S t) q) (fun t => A p (C t))
        (A p q)).det ≠ 0 := by
      rwa [← det_snoc_eq_det_border, ← bareissMatrix_nonPivot A C hp q]
    have h1 := bareissMatrix_pivot A hS'inj (Fin.snoc C q) a.castSucc j
    rw [Fin.snoc_castSucc] at h1
    rw [h1, bareissMatrix_pivot A hSinj C a j, bareissMatrix_pivot A hSinj C a q,
      bareissMatrix_nonPivot A C hp q, bareissMatrix_nonPivot A C hp j,
      det_snoc_update_eq_det_border_updateCol, pivotDet,
      det_mul_det_border_updateCol hΔ _ _ _ hM, submatrix_update_col, submatrix_update_col,
      det_snoc_eq_det_border A S C p q, det_snoc_eq_det_border A S C p j]
    ring
  · -- an unpivoted row: the Sylvester identity `det_mul_det_fromBlocks_fin2`
    have hi : ∀ a : Fin k, S a ≠ i := not_exists.1 hrow
    have hi' : ∀ x, (Fin.snoc S p : Fin (k + 1) → Fin m) x ≠ i :=
      Fin.lastCases (by rw [Fin.snoc_last]; exact hne.symm)
        fun x => by rw [Fin.snoc_castSucc]; exact hi x
    rw [bareissMatrix_nonPivot A (Fin.snoc C q) hi' j, bareissMatrix_nonPivot A C hp q,
      bareissMatrix_nonPivot A C hi j, bareissMatrix_nonPivot A C hi q,
      bareissMatrix_nonPivot A C hp j, det_snoc_snoc_eq_det_fromBlocks, pivotDet,
      det_mul_det_fromBlocks_fin2 hΔ, det_snoc_eq_det_border A S C p q,
      det_snoc_eq_det_border A S C i j, det_snoc_eq_det_border A S C i q,
      det_snoc_eq_det_border A S C p j]

/-- Over `ℤ`, every Bareiss–Jordan update identity holds identically, giving exact divisibility by
`pivotDet A S C`. -/
theorem pivotDet_mul_bareissMatrix_snoc_int (A : Matrix (Fin m) (Fin n) ℤ)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) (i : Fin m) (j : Fin n) :
    (i = p → bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j = bareissMatrix A S C p j) ∧
      (i ≠ p →
        pivotDet A S C * bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j =
          bareissMatrix A S C p q * bareissMatrix A S C i j -
            bareissMatrix A S C i q * bareissMatrix A S C p j) := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  have hQ := pivotDet_mul_bareissMatrix_snoc (A.map f) (S := S) (C := C)
    (by rw [← map_pivotDet]; exact Int.cast_ne_zero.mpr hΔ) hp q
    (by rw [← map_bareissMatrix]; exact Int.cast_ne_zero.mpr hΔ') i j
  simp only [← map_pivotDet, ← map_bareissMatrix, Matrix.map_apply, f, eq_intCast] at hQ
  exact_mod_cast hQ

/-- Exact integer divisibility in a Bareiss–Jordan elimination step. -/
theorem pivotDet_dvd_bareissStep_int (A : Matrix (Fin m) (Fin n) ℤ)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) {i : Fin m} (hip : i ≠ p) (j : Fin n) :
    pivotDet A S C ∣
      bareissMatrix A S C p q * bareissMatrix A S C i j -
        bareissMatrix A S C i q * bareissMatrix A S C p j :=
  ⟨bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j,
    ((pivotDet_mul_bareissMatrix_snoc_int A hΔ hp q hΔ' i j).2 hip).symm⟩

/-- Exact quotient (`Int.ediv`) in a Bareiss–Jordan elimination step recovers
`bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j`. -/
theorem bareissStep_ediv_eq_int (A : Matrix (Fin m) (Fin n) ℤ)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) {i : Fin m} (hip : i ≠ p) (j : Fin n) :
    (bareissMatrix A S C p q * bareissMatrix A S C i j -
        bareissMatrix A S C i q * bareissMatrix A S C p j) / pivotDet A S C =
      bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j := by
  rw [← (pivotDet_mul_bareissMatrix_snoc_int A hΔ hp q hΔ' i j).2 hip]
  exact Int.mul_ediv_cancel_left _ hΔ

/-- Any predicate `Q` on rows that includes the new pivot row `p` and already makes column `j`
vanish in `bareissMatrix A S C` continues to make column `j` vanish after pivoting on `(p, q)`. -/
theorem bareissMatrix_snoc_zero_of_forall {K : Type*} [Field K] (A : Matrix (Fin m) (Fin n) K)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : bareissMatrix A S C p q ≠ 0) (j : Fin n) (Q : Fin m → Prop) (hQp : Q p)
    (hQzero : ∀ i : Fin m, Q i → bareissMatrix A S C i j = 0) :
    ∀ i : Fin m, Q i → bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j = 0 := by
  intro i hQi
  obtain ⟨h₁, h₂⟩ := pivotDet_mul_bareissMatrix_snoc A hΔ hp q hΔ' i j
  by_cases hip : i = p
  · rw [h₁ hip, hQzero p hQp]
  · simpa [hQzero i hQi, hQzero p hQp, hΔ] using h₂ hip

/-! ### Hadamard / factorial minor bounds over `ℤ` -/

/-- Hadamard-type bound for a `k × k` minor of an integer matrix with entries bounded by `B`. -/
private theorem abs_det_submatrix_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) (S : Fin k → Fin m) (C : Fin k → Fin n) :
    |(A.submatrix S C).det| ≤ (k.factorial * B ^ k : ℕ) := by
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow] using
    det_le (abv := AbsoluteValue.abs) (A := A.submatrix S C) fun u v => hA _ _

/-- Entry magnitude bound on pivoted rows of `bareissMatrix` over `ℤ`: `k! * B ^ k`. -/
theorem abs_bareissMatrix_pivot_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) {S : Fin k → Fin m} (hS : Function.Injective S)
    (C : Fin k → Fin n) (a : Fin k) (j : Fin n) :
    |bareissMatrix A S C (S a) j| ≤ (k.factorial * B ^ k : ℕ) :=
  bareissMatrix_pivot A hS C a j ▸ abs_det_submatrix_le A hA _ _

/-- Entry magnitude bound on unpivoted rows of `bareissMatrix` over `ℤ`:
`(k + 1)! * B ^ (k + 1)`. -/
theorem abs_bareissMatrix_nonPivot_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) {S : Fin k → Fin m} (C : Fin k → Fin n)
    {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) (j : Fin n) :
    |bareissMatrix A S C i j| ≤ ((k + 1).factorial * B ^ (k + 1) : ℕ) :=
  bareissMatrix_nonPivot A C hi j ▸ abs_det_submatrix_le A hA _ _

/-- Uniform entry magnitude bound for any stage of `bareissMatrix` over `ℤ`. -/
theorem abs_bareissMatrix_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) {S : Fin k → Fin m} (hS : Function.Injective S)
    (C : Fin k → Fin n) (i : Fin m) (j : Fin n) :
    |bareissMatrix A S C i j| ≤ ((k + 1).factorial * (B + 1) ^ (k + 1) : ℕ) := by
  by_cases hrow : ∃ a : Fin k, S a = i
  · obtain ⟨a, rfl⟩ := hrow
    refine (abs_bareissMatrix_pivot_le A hA hS C a j).trans ?_
    exact_mod_cast Nat.mul_le_mul (Nat.factorial_le (Nat.le_succ k))
      ((Nat.pow_le_pow_left (Nat.le_succ B) k).trans
        (Nat.pow_le_pow_right (Nat.succ_pos B) (Nat.le_succ k)))
  · refine (abs_bareissMatrix_nonPivot_le A hA C (not_exists.1 hrow) j).trans ?_
    exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ B) (k + 1))

/-- Pivot determinant magnitude bound: `|pivotDet A S C| ≤ k! * B ^ k`. -/
theorem abs_pivotDet_le (A : Matrix (Fin m) (Fin n) ℤ) {B : ℕ}
    (hA : ∀ u v, |A u v| ≤ B) (S : Fin k → Fin m) (C : Fin k → Fin n) :
    |pivotDet A S C| ≤ (k.factorial * B ^ k : ℕ) :=
  abs_det_submatrix_le A hA S C

/-! ### Rational RREF, row space, rank, row basis, kernel basis, and linear solver -/

section FieldResults

variable {K : Type*} [Field K]

/-- Rational reduced form `(pivotDet A S C)⁻¹ • bareissMatrix A S C`. -/
@[expose] noncomputable def rrefOfBareiss (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) : Matrix (Fin m) (Fin n) K :=
  (pivotDet A S C)⁻¹ • bareissMatrix A S C

/-- Entrywise form of `rrefOfBareiss`. -/
private theorem rrefOfBareiss_apply (A : Matrix (Fin m) (Fin n) K) (S : Fin k → Fin m)
    (C : Fin k → Fin n) (i : Fin m) (j : Fin n) :
    rrefOfBareiss A S C i j = (pivotDet A S C)⁻¹ * bareissMatrix A S C i j :=
  rfl

/-- A row on which `bareissMatrix` vanishes is a zero row of `rrefOfBareiss`. -/
private theorem rrefOfBareiss_row_eq_zero {A : Matrix (Fin m) (Fin n) K} {S : Fin k → Fin m}
    {C : Fin k → Fin n} {i : Fin m} (h : ∀ j : Fin n, bareissMatrix A S C i j = 0) :
    rrefOfBareiss A S C i = 0 :=
  funext fun j => by rw [rrefOfBareiss_apply, h j, mul_zero, Pi.zero_apply]

/-- Entry of `rrefOfBareiss A S C` on a pivoted row `S a`. -/
theorem rrefOfBareiss_pivot_entry {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (a : Fin k) (j : Fin n) :
    rrefOfBareiss A S C (S a) j = ((A.submatrix S C)⁻¹ *ᵥ (fun t => A (S t) j)) a := by
  have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
  rw [rrefOfBareiss_apply, bareissMatrix_pivot A hSinj C a j, submatrix_update_col,
    ← det_mul_inv_mulVec_apply hΔ]
  exact inv_mul_cancel_left₀ hΔ _

/-- Each pivot entry `(S a, C a)` in `rrefOfBareiss A S C` equals `1`. -/
theorem rrefOfBareiss_pivot_col_self {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (a : Fin k) :
    rrefOfBareiss A S C (S a) (C a) = 1 := by
  rw [rrefOfBareiss_apply, bareissMatrix_pivot_col_self A (injective_of_pivotDet_ne_zero hΔ).1,
    inv_mul_cancel₀ hΔ]

/-- Entries of `rrefOfBareiss A S C` in other pivot columns vanish on pivot rows. -/
theorem rrefOfBareiss_pivot_col_ne {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) {a b : Fin k}
    (hab : a ≠ b) : rrefOfBareiss A S C (S a) (C b) = 0 := by
  rw [rrefOfBareiss_apply, bareissMatrix_pivot_col_ne A (injective_of_pivotDet_ne_zero hΔ).1 C hab,
    mul_zero]

/-- Entries of `rrefOfBareiss A S C` in pivot columns vanish on unpivoted rows. -/
theorem rrefOfBareiss_nonPivot_col {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i)
    (b : Fin k) : rrefOfBareiss A S C i (C b) = 0 := by
  rw [rrefOfBareiss_apply, bareissMatrix_nonPivot_col A C hi b, mul_zero]

/-- Row elimination formula for unpivoted rows of `rrefOfBareiss A S C`. -/
theorem rrefOfBareiss_nonPivot_row {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    {i : Fin m} (hi : ∀ a : Fin k, S a ≠ i) :
    rrefOfBareiss A S C i = A i - ∑ a : Fin k, A i (C a) • rrefOfBareiss A S C (S a) := by
  ext j
  rw [rrefOfBareiss_apply, bareissMatrix_nonPivot A C hi j, det_snoc_eq_det_border,
    det_border hΔ, ← pivotDet, inv_mul_cancel_left₀ hΔ]
  simp [dotProduct, rrefOfBareiss_pivot_entry hΔ]

/-- Each pivot row of `rrefOfBareiss A S C` is a linear combination of the pivot rows of `A`. -/
theorem rrefOfBareiss_pivot_eq_sum {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (a : Fin k) :
    rrefOfBareiss A S C (S a) = ∑ b : Fin k, (A.submatrix S C)⁻¹ a b • A (S b) := by
  ext j
  simp only [rrefOfBareiss_pivot_entry hΔ a j, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]

/-- Each pivot row of `A` is a linear combination of the pivot rows of `rrefOfBareiss A S C`. -/
theorem row_pivot_eq_sum_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (a : Fin k) :
    A (S a) = ∑ b : Fin k, A (S a) (C b) • rrefOfBareiss A S C (S b) := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rrefOfBareiss_pivot_entry hΔ]
  exact (congrFun (mulVec_inv_mulVec hΔ fun t => A (S t) j) a).symm

/-- `rrefOfBareiss` has the exact same row space as `A`. -/
theorem span_row_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    Submodule.span K (Set.range (rrefOfBareiss A S C)) = Submodule.span K (Set.range A) := by
  have hpivot_mem : ∀ a : Fin k, rrefOfBareiss A S C (S a) ∈ span K (Set.range A) := fun a => by
    rw [rrefOfBareiss_pivot_eq_sum hΔ a]
    exact sum_smul_mem _ _ fun b _ => subset_span ⟨S b, rfl⟩
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_) <;> rintro _ ⟨i, rfl⟩ <;>
    by_cases hrow : ∃ a : Fin k, S a = i
  · obtain ⟨a, rfl⟩ := hrow
    exact hpivot_mem a
  · rw [rrefOfBareiss_nonPivot_row hΔ (not_exists.1 hrow)]
    exact sub_mem (subset_span ⟨i, rfl⟩) (sum_smul_mem _ _ fun a _ => hpivot_mem a)
  · obtain ⟨a, rfl⟩ := hrow
    rw [row_pivot_eq_sum_rrefOfBareiss hΔ a]
    exact sum_smul_mem _ _ fun b _ => subset_span ⟨S b, rfl⟩
  · rw [← sub_add_cancel (A i) (∑ a : Fin k, A i (C a) • rrefOfBareiss A S C (S a)),
      ← rrefOfBareiss_nonPivot_row hΔ (not_exists.1 hrow)]
    exact add_mem (subset_span ⟨i, rfl⟩) (sum_smul_mem _ _ fun a _ => subset_span ⟨S a, rfl⟩)

/-- `rrefOfBareiss` has the same rank as `A`. -/
theorem rank_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    (rrefOfBareiss A S C).rank = A.rank := by
  rw [← finrank_span_range_row, ← finrank_span_range_row]
  change Module.finrank K (Submodule.span K (Set.range (rrefOfBareiss A S C))) =
    Module.finrank K (Submodule.span K (Set.range A))
  rw [span_row_rrefOfBareiss hΔ]

/-- A vector orthogonal to every member of a family is orthogonal to its span. -/
private theorem dotProduct_eq_zero_of_mem_span {ι : Type*} {M : ι → Fin n → K} {v : Fin n → K}
    (hv : ∀ i, M i ⬝ᵥ v = 0) {w : Fin n → K} (hw : w ∈ Submodule.span K (Set.range M)) :
    w ⬝ᵥ v = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hv i
  | zero => exact zero_dotProduct v
  | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_dotProduct, hx, smul_zero]

/-- `rrefOfBareiss` has the exact same kernel as `A`. -/
theorem ker_mulVecLin_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    LinearMap.ker (rrefOfBareiss A S C).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext v
  simp only [LinearMap.mem_ker, mulVecLin_apply, funext_iff, mulVec, Pi.zero_apply]
  have hspan := span_row_rrefOfBareiss hΔ
  exact ⟨fun hv i => dotProduct_eq_zero_of_mem_span hv (hspan.ge (subset_span ⟨i, rfl⟩)),
    fun hv i => dotProduct_eq_zero_of_mem_span hv (hspan.le (subset_span ⟨i, rfl⟩))⟩

/-- The selected pivot rows `A ∘ S` are linearly independent whenever `pivotDet A S C ≠ 0`. -/
theorem linearIndependent_row_of_pivotDet_ne_zero {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) :
    LinearIndependent K (fun a : Fin k => A (S a)) :=
  LinearIndependent.of_comp (LinearMap.funLeft K K C) (linearIndependent_rows_of_det_ne_zero hΔ)

/-- When all unpivoted rows vanish in `bareissMatrix`, the pivot rows `A ∘ S` span the entire
row space of `A`. -/
theorem span_rowBasis_eq_of_bareiss_terminal {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0) :
    Submodule.span K (Set.range fun a : Fin k => A (S a)) = Submodule.span K (Set.range A) := by
  refine le_antisymm (span_mono (Set.range_comp_subset_range S A)) ?_
  rw [← span_row_rrefOfBareiss hΔ]
  refine span_le.2 (Set.range_subset_iff.2 fun i => ?_)
  by_cases hrow : ∃ a : Fin k, S a = i
  · obtain ⟨a, rfl⟩ := hrow
    rw [rrefOfBareiss_pivot_eq_sum hΔ a]
    exact sum_smul_mem _ _ fun b _ => subset_span ⟨b, rfl⟩
  · exact rrefOfBareiss_row_eq_zero (hterm i (not_exists.1 hrow)) ▸ zero_mem _

/-- When all unpivoted rows vanish, `A.rank = k`. -/
theorem rank_eq_of_bareiss_terminal {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0) :
    A.rank = k := by
  rw [← finrank_span_range_row]
  change Module.finrank K (Submodule.span K (Set.range A)) = k
  rw [← span_rowBasis_eq_of_bareiss_terminal hΔ hterm,
    finrank_span_eq_card (linearIndependent_row_of_pivotDet_ne_zero hΔ), Fintype.card_fin]

/-- Under a row permutation `σ` placing the pivot rows `S` in positions `0, …, k - 1`, strictly
increasing pivot columns `C`, and vanishing left-of-pivot entries `hzero`, the permuted
`rrefOfBareiss` is in Mathlib's `Matrix.IsPivotedBy` and `Matrix.IsReducedRowEchelon` form. -/
theorem isReducedRowEchelon_rrefOfBareiss {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hC : StrictMono C)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0)
    (hzero : ∀ a : Fin k, ∀ j : Fin n, j < C a → bareissMatrix A S C (S a) j = 0)
    (σ : Equiv.Perm (Fin m)) (hσ : ∀ a : Fin k, σ ⟨a.val, a.isLt.trans_le (by
      have ⟨hSinj, _⟩ := injective_of_pivotDet_ne_zero hΔ
      simpa using Fintype.card_le_of_injective S hSinj)⟩ = S a) :
    let U := (rrefOfBareiss A S C).submatrix σ id
    let l : Fin m → WithTop (Fin n) := fun i =>
      if hi : i.val < k then (C ⟨i.val, hi⟩ : WithTop (Fin n)) else ⊤
    U.IsPivotedBy l ∧ U.IsReducedRowEchelon := by
  intro U l
  -- rows below the pivot rows vanish; row `i < k` is pivot row `S i` of `rrefOfBareiss`
  have hZ : ∀ i : Fin m, ¬i.val < k → U i = 0 := fun i hi =>
    rrefOfBareiss_row_eq_zero (hterm (σ i) fun a ha => hi (by
      rw [← hσ a] at ha
      exact σ.injective ha ▸ a.isLt))
  have hrow : ∀ (i : Fin m) (hi : i.val < k) (j : Fin n),
      U i j = rrefOfBareiss A S C (S ⟨i, hi⟩) j := fun i hi j => by rw [← hσ ⟨i, hi⟩]; rfl
  have hone : ∀ (i : Fin m) (hi : i.val < k), U i (C ⟨i, hi⟩) = 1 := fun i hi => by
    rw [hrow i hi, rrefOfBareiss_pivot_col_self hΔ]
  have hlead : ∀ (i : Fin m) (hi : i.val < k) (j : Fin n), j < C ⟨i, hi⟩ → U i j = 0 :=
    fun i hi j hj => by rw [hrow i hi, rrefOfBareiss_apply, hzero _ j hj, mul_zero]
  have hech : U.IsRowEchelon := fun i₁ i₂ hlt j₂ h₁ => by
    by_cases hi₂ : i₂.val < k
    · exact hlead i₂ hi₂ j₂ <| lt_of_not_ge fun hle => one_ne_zero <|
        (hone i₁ (Nat.lt_trans hlt hi₂)).symm.trans (h₁ _ ((hC (show _ < _ from hlt)).trans_le hle))
    · exact congrFun (hZ i₂ hi₂) j₂
  have hpiv : U.IsPivotedBy l := by
    refine ⟨hech, fun i => ?_⟩
    by_cases hi : i.val < k
    · rw [show l i = (C ⟨i, hi⟩ : WithTop (Fin n)) from dite_eq_left hi]
      exact ⟨fun j hj => hlead i hi j (WithTop.coe_lt_coe.mp hj),
        fun c hc => by rw [← WithTop.coe_injective hc, hone i hi]; exact one_ne_zero⟩
    · rw [show l i = ⊤ from dite_eq_right hi]
      exact ⟨fun j _ => congrFun (hZ i hi) j, fun c hc => absurd hc WithTop.top_ne_coe⟩
  -- a leading entry sits in a pivot row `i < k`, in the pivot column of that row
  have hcol : ∀ {i : Fin m} {c : Fin n}, U.IsLeadingEntry i c →
      ∃ hi : i.val < k, c = C ⟨i, hi⟩ := fun {i c} h =>
    have hi : i.val < k := not_not.1 fun hnot => h.row_ne_zero (hZ i hnot)
    ⟨hi, h.unique (hpiv.isLeadingEntry (dite_eq_left hi))⟩
  refine ⟨hpiv, hech, fun i c h => ?_, fun i₁ i₂ c hlt h => ?_⟩
  · obtain ⟨hi, rfl⟩ := hcol h
    exact hone i hi
  · obtain ⟨hi₂, rfl⟩ := hcol h
    rw [hrow i₁ (Nat.lt_trans hlt hi₂), rrefOfBareiss_pivot_col_ne hΔ (Fin.ne_of_lt hlt)]

/-- Canonical right-kernel basis vector associated with a non-pivot column `j`: has `-U (S a) j` in
each pivot column `C a`, `1` at coordinate `j`, and `0` at every other non-pivot column. -/
noncomputable def kernelBasisVec (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (j : Fin n) : Fin n → K := by
  classical
  exact fun c =>
    if hc : ∃ a : Fin k, C a = c then -rrefOfBareiss A S C (S hc.choose) j
    else if c = j then 1 else 0

theorem kernelBasisVec_pivot {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (j : Fin n) (a : Fin k) :
    kernelBasisVec A S C j (C a) = -rrefOfBareiss A S C (S a) j := by
  classical
  have hex : ∃ b : Fin k, C b = C a := ⟨a, rfl⟩
  rw [kernelBasisVec, dite_eq_left hex, (injective_of_pivotDet_ne_zero hΔ).2 hex.choose_spec]

theorem kernelBasisVec_nonPivot {A : Matrix (Fin m) (Fin n) K}
    (S : Fin k → Fin m) (C : Fin k → Fin n) (j c : Fin n) (hc : ∀ a : Fin k, C a ≠ c) :
    kernelBasisVec A S C j c = if c = j then 1 else 0 := by
  classical
  rw [kernelBasisVec, dite_eq_right fun ⟨a, ha⟩ => hc a ha]

/-- A sum over all columns splits into the pivot columns `C a` and the non-pivot columns. -/
private theorem sum_eq_sum_pivot_add_sum_nonPivot {C : Fin k → Fin n} (hC : Function.Injective C)
    (f : Fin n → K) :
    ∑ c, f c = ∑ a, f (C a) + ∑ j : { j : Fin n // ∀ a : Fin k, C a ≠ j }, f j.val := by
  classical
  rw [← Finset.sum_image (f := f) fun _ _ _ _ h => hC h,
    ← Finset.sum_subtype (univ \ univ.image C) (by simp) f, add_comm]
  exact (Finset.sum_sdiff (subset_univ _)).symm

/-- A pivot row `S a` of `rrefOfBareiss` has a `1` in its own pivot column and `0` in the other
pivot columns, so its dot product with `v` only sees `v (C a)` and the non-pivot columns. -/
private theorem rrefOfBareiss_pivot_dotProduct {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0) (a : Fin k)
    (v : Fin n → K) :
    rrefOfBareiss A S C (S a) ⬝ᵥ v = v (C a) +
      ∑ j : { j : Fin n // ∀ b : Fin k, C b ≠ j }, rrefOfBareiss A S C (S a) j.val * v j.val := by
  rw [dotProduct, sum_eq_sum_pivot_add_sum_nonPivot (injective_of_pivotDet_ne_zero hΔ).2,
    Fintype.sum_eq_single a fun b hb => by rw [rrefOfBareiss_pivot_col_ne hΔ hb.symm, zero_mul],
    rrefOfBareiss_pivot_col_self hΔ, one_mul]

/-- On a non-pivot coordinate `c`, a combination of the vectors `kernelBasisVec` reads off the
coefficient of the vector indexed by `c`. -/
private theorem sum_mul_kernelBasisVec_nonPivot {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (g : { j : Fin n // ∀ a : Fin k, C a ≠ j } → K)
    (c : { j : Fin n // ∀ a : Fin k, C a ≠ j }) :
    ∑ x, g x * kernelBasisVec A S C x.val c.val = g c := by
  rw [Fintype.sum_eq_single c, kernelBasisVec_nonPivot S C c.val c.val c.property,
    ite_eq_left rfl, mul_one]
  intro x hx
  rw [kernelBasisVec_nonPivot S C x.val c.val c.property,
    ite_eq_right fun h => hx (Subtype.ext h.symm),
    mul_zero]

/-- Every `kernelBasisVec` associated with a non-pivot column `j` lies in `ker A.mulVecLin`. -/
theorem mulVec_kernelBasisVec {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ c : Fin n, bareissMatrix A S C i c = 0)
    {j : Fin n} (hj : ∀ a : Fin k, C a ≠ j) :
    A *ᵥ kernelBasisVec A S C j = 0 := by
  change A.mulVecLin (kernelBasisVec A S C j) = 0
  rw [← LinearMap.mem_ker, ← ker_mulVecLin_rrefOfBareiss hΔ, LinearMap.mem_ker, mulVecLin_apply]
  ext i
  change rrefOfBareiss A S C i ⬝ᵥ kernelBasisVec A S C j = 0
  by_cases hrow : ∃ a : Fin k, S a = i
  · obtain ⟨a, rfl⟩ := hrow
    rw [rrefOfBareiss_pivot_dotProduct hΔ, kernelBasisVec_pivot hΔ, Fintype.sum_eq_single ⟨j, hj⟩,
      kernelBasisVec_nonPivot S C j j hj, ite_eq_left rfl, mul_one, neg_add_cancel]
    intro c hc
    rw [kernelBasisVec_nonPivot S C j c.val c.property,
      ite_eq_right fun h => hc (Subtype.ext h), mul_zero]
  · rw [rrefOfBareiss_row_eq_zero (hterm i (not_exists.1 hrow)), zero_dotProduct]

/-- The family of `kernelBasisVec` indexed by non-pivot columns is linearly independent. -/
theorem linearIndependent_kernelBasisVec (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) :
    LinearIndependent K
      (fun j : { j : Fin n // ∀ a : Fin k, C a ≠ j } => kernelBasisVec A S C j.val) := by
  refine Fintype.linearIndependent_iff.2 fun g hg j => ?_
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    sum_mul_kernelBasisVec_nonPivot] using congrFun hg j.val

/-- The `kernelBasisVec` vectors over non-pivot columns span `LinearMap.ker A.mulVecLin`. -/
theorem span_kernelBasisVec {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ c : Fin n, bareissMatrix A S C i c = 0) :
    Submodule.span K
        (Set.range fun j : { j : Fin n // ∀ a : Fin k, C a ≠ j } =>
          kernelBasisVec A S C j.val) =
      LinearMap.ker A.mulVecLin := by
  refine le_antisymm (span_le.2 <| Set.range_subset_iff.2 fun j =>
    mulVec_kernelBasisVec hΔ hterm j.property) fun v hv => ?_
  rw [← ker_mulVecLin_rrefOfBareiss (A := A) (S := S) (C := C) hΔ, LinearMap.mem_ker,
    mulVecLin_apply] at hv
  have hv_eq : v = ∑ j : { j : Fin n // ∀ a : Fin k, C a ≠ j },
      v j.val • kernelBasisVec A S C j.val := by
    ext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hc : ∃ a : Fin k, C a = c
    · obtain ⟨a, rfl⟩ := hc
      have hrow : rrefOfBareiss A S C (S a) ⬝ᵥ v = 0 := congrFun hv (S a)
      rw [rrefOfBareiss_pivot_dotProduct hΔ] at hrow
      simp only [kernelBasisVec_pivot hΔ, mul_comm (v _), neg_mul, Finset.sum_neg_distrib]
      linear_combination hrow
    · exact (sum_mul_kernelBasisVec_nonPivot (fun j => v j.val) ⟨c, not_exists.1 hc⟩).symm
  rw [hv_eq]
  exact sum_smul_mem _ _ fun j _ => subset_span ⟨j, rfl⟩

/-- At termination, `finrank K (LinearMap.ker A.mulVecLin) = n - k`. -/
theorem finrank_ker_mulVecLin_of_bareiss_terminal {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0) :
    Module.finrank K (LinearMap.ker A.mulVecLin) = n - k := by
  have hrn := A.mulVecLin.finrank_range_add_finrank_ker
  have hrk := rank_eq_of_bareiss_terminal hΔ hterm
  rw [finrank_range_mulVecLin] at hrn
  rw [hrk, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
  omega

/-- Canonical solution vector supported on the pivot columns `C`, solving the pivot rows `A ∘ S`. -/
noncomputable def solveVec (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (b : Fin m → K) : Fin n → K := by
  classical
  exact fun c =>
    if hc : ∃ a : Fin k, C a = c then ((A.submatrix S C)⁻¹ *ᵥ (fun t => b (S t))) hc.choose
    else 0

theorem solveVec_pivot {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (b : Fin m → K) (a : Fin k) :
    solveVec A S C b (C a) = ((A.submatrix S C)⁻¹ *ᵥ (fun t => b (S t))) a := by
  classical
  have hex : ∃ t : Fin k, C t = C a := ⟨a, rfl⟩
  rw [solveVec, dite_eq_left hex, (injective_of_pivotDet_ne_zero hΔ).2 hex.choose_spec]

theorem solveVec_nonPivot (A : Matrix (Fin m) (Fin n) K)
    (S : Fin k → Fin m) (C : Fin k → Fin n) (b : Fin m → K) {c : Fin n}
    (hc : ∀ a : Fin k, C a ≠ c) :
    solveVec A S C b c = 0 := by
  classical
  rw [solveVec, dite_eq_right fun ⟨a, ha⟩ => hc a ha]

private theorem dotProduct_solveVec {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (f : Fin n → K) (b : Fin m → K) :
    f ⬝ᵥ solveVec A S C b = ∑ a : Fin k, f (C a) * solveVec A S C b (C a) := by
  rw [dotProduct, sum_eq_sum_pivot_add_sum_nonPivot (injective_of_pivotDet_ne_zero hΔ).2,
    add_eq_left]
  exact Finset.sum_eq_zero fun c _ => by rw [solveVec_nonPivot A S C b c.property, mul_zero]

/-- `solveVec A S C b` always satisfies the pivot rows `(A *ᵥ x) (S a) = b (S a)`. -/
theorem mulVec_solveVec_pivot {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (b : Fin m → K) (a : Fin k) :
    (A *ᵥ solveVec A S C b) (S a) = b (S a) := by
  change A (S a) ⬝ᵥ solveVec A S C b = b (S a)
  rw [dotProduct_solveVec hΔ, ← congrFun (mulVec_inv_mulVec hΔ fun t => b (S t)) a]
  exact Finset.sum_congr rfl fun t _ => by rw [solveVec_pivot hΔ b t]; rfl

/-- `solveVec A S C b` solves `A *ᵥ x = b` iff `A *ᵥ x = b` is consistent. -/
theorem mulVec_solveVec_eq_iff_exists_mulVec_eq {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0)
    (b : Fin m → K) :
    A *ᵥ solveVec A S C b = b ↔ ∃ x : Fin n → K, A *ᵥ x = b := by
  refine ⟨fun h => ⟨solveVec A S C b, h⟩, ?_⟩
  rintro ⟨x, rfl⟩
  ext i
  have hi : A i ∈ span K (Set.range fun a : Fin k => A (S a)) :=
    (span_rowBasis_eq_of_bareiss_terminal hΔ hterm).ge (subset_span ⟨i, rfl⟩)
  have hdot := dotProduct_eq_zero_of_mem_span (v := x - solveVec A S C (A *ᵥ x)) (fun a => by
    rw [dotProduct_sub]
    exact sub_eq_zero.2 (mulVec_solveVec_pivot hΔ (A *ᵥ x) a).symm) hi
  rw [dotProduct_sub] at hdot
  exact (sub_eq_zero.mp hdot).symm

/-- Augmented matrix `[A | b]`. -/
@[expose] def augmentCol {R : Type*} (A : Matrix (Fin m) (Fin n) R) (b : Fin m → R) :
    Matrix (Fin m) (Fin (n + 1)) R :=
  of fun i => Fin.snoc (A i) (b i)

/-- The Bareiss–Jordan reduction of `[A | b]` at `(S, Fin.castSucc ∘ C)` yields `solveVec A S C b`
on pivot rows in the last column, and vanishes on unpivoted rows iff `A *ᵥ solveVec A S C b = b`. -/
theorem rrefOfBareiss_augmentCol {A : Matrix (Fin m) (Fin n) K}
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : pivotDet A S C ≠ 0)
    (hterm : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) → ∀ j : Fin n, bareissMatrix A S C i j = 0)
    (b : Fin m → K) :
    let Aaug := augmentCol A b
    let Caug := Fin.castSucc ∘ C
    (∀ a : Fin k, rrefOfBareiss Aaug S Caug (S a) (Fin.last n) = solveVec A S C b (C a)) ∧
      (A *ᵥ solveVec A S C b = b ↔
        ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) →
          bareissMatrix Aaug S Caug i (Fin.last n) = 0) := by
  intro Aaug Caug
  have hlast : ∀ i, Aaug i (Fin.last n) = b i := fun i => by simp [Aaug, augmentCol]
  have hcast : ∀ i a, Aaug i (Caug a) = A i (C a) := fun i a => by simp [Aaug, augmentCol, Caug]
  have hsub : Aaug.submatrix S Caug = A.submatrix S C := ext fun u v => hcast (S u) v
  have hΔaug : pivotDet Aaug S Caug ≠ 0 := by rwa [pivotDet, hsub]
  have hcol : ∀ a : Fin k,
      rrefOfBareiss Aaug S Caug (S a) (Fin.last n) = solveVec A S C b (C a) := fun a => by
    simp only [rrefOfBareiss_pivot_entry hΔaug, solveVec_pivot hΔ, hsub, hlast]
  have hnon : ∀ i : Fin m, (∀ a : Fin k, S a ≠ i) →
      rrefOfBareiss Aaug S Caug i (Fin.last n) = b i - (A *ᵥ solveVec A S C b) i := fun i hi => by
    -- by `hterm`, row `i` of `A` is a combination of the pivot rows of `rrefOfBareiss A S C`
    have hAi : A i = ∑ a : Fin k, A i (C a) • rrefOfBareiss A S C (S a) := by
      have h := rrefOfBareiss_nonPivot_row hΔ hi
      rwa [rrefOfBareiss_row_eq_zero (hterm i hi), eq_comm, sub_eq_zero] at h
    have hdot : ∀ a : Fin k,
        rrefOfBareiss A S C (S a) ⬝ᵥ solveVec A S C b = solveVec A S C b (C a) := fun a => by
      rw [rrefOfBareiss_pivot_dotProduct hΔ, add_eq_left]
      exact Finset.sum_eq_zero fun c _ => by rw [solveVec_nonPivot A S C b c.property, mul_zero]
    rw [rrefOfBareiss_nonPivot_row hΔaug hi, mulVec]
    dsimp only
    conv_rhs => rw [hAi, sum_dotProduct]
    simp [smul_dotProduct, hdot, hcol, hlast, hcast]
  refine ⟨hcol, fun hsol i hi => ?_, fun hzeros => funext fun i => ?_⟩
  · have hz := hnon i hi
    rw [hsol, sub_self, rrefOfBareiss_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hΔaug)
  · by_cases hrow : ∃ a : Fin k, S a = i
    · obtain ⟨a, rfl⟩ := hrow
      exact mulVec_solveVec_pivot hΔ b a
    · have hz := hnon i (not_exists.1 hrow)
      rw [rrefOfBareiss_apply, hzeros i (not_exists.1 hrow), mul_zero] at hz
      exact (sub_eq_zero.mp hz.symm).symm

end FieldResults

end MinorMatrix

end Matrix

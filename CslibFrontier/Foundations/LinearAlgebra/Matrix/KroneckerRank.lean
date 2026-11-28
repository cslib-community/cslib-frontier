/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact Kronecker product rank and flat Kronecker powers

Every matrix `A` over a field contains a nonsingular `A.rank × A.rank` submatrix
(`Matrix.exists_submatrix_det_ne_zero`). Combining that nonsingular minor witness with the
Kronecker rank upper bound (`Matrix.rank_kronecker_le`) and `Matrix.det_kronecker` upgrades
Kronecker rank submultiplicativity to an exact equality `(A ⊗ₖ B).rank = A.rank * B.rank`
(`Matrix.rank_kronecker`).

This module also defines the flat `k`-fold Kronecker power
`Matrix.kroneckerPow A k : Matrix (Fin k → m) (Fin k → n) R` indexed directly by `Fin k → m`
rather than nested binary products, proves its algebraic laws, action on product vectors and
eigenvectors (`Matrix.kroneckerPow_mulVec_prod`, `Matrix.kroneckerPow_mulVec_smul`), and deduces
`(Matrix.kroneckerPow A k).rank = A.rank ^ k` (`Matrix.rank_kroneckerPow`).

## Main definitions

* `Matrix.kroneckerPow`: the `k`-fold Kronecker power on `Fin k → m` by `Fin k → n`.

## Main results

* `Matrix.exists_submatrix_det_ne_zero`: existence of a nonsingular `A.rank × A.rank` minor.
* `Matrix.mulVec_map_eq_smul`: eigenvector/eigenvalue transfer along a ring homomorphism.
* `Matrix.kronecker_mulVec_smul`, `Matrix.mul_prod_ne_zero_iff`: tensor products of eigenvectors
  of `A` and `B` are eigenvectors of `A ⊗ₖ B` with eigenvalue `μ * ν`, and are nonzero if and only
  if both factors are nonzero ([AroraBarak07, Chapter 16, Exercise 14]).
* `Matrix.rank_kronecker`: `(A ⊗ₖ B).rank = A.rank * B.rank` over any field.
* `Matrix.kroneckerPow_succ_eq_submatrix`, `Matrix.kroneckerPow_mul`, `Matrix.kroneckerPow_pow`,
  `Matrix.trace_kroneckerPow`, `Matrix.trace_kroneckerPow_pow`,
  `Matrix.kroneckerPow_mulVec_prod`, `Matrix.kroneckerPow_mulVec_smul`,
  `Matrix.prod_vec_ne_zero_iff`, `Matrix.rank_kroneckerPow`: structure, powers, traces, action,
  eigenpairs, and rank of Kronecker powers.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
-/

public section

namespace Matrix

open Kronecker
open scoped BigOperators

/-! ### Nonsingular `rank × rank` minors and scalar-homomorphism eigenvector transfer -/

section Minors

/-- Every finite matrix `A` over a field contains an injective `A.rank × A.rank` submatrix with
nonzero determinant. -/
theorem exists_submatrix_det_ne_zero {m n K : Type*} [Field K] [Finite m] [Finite n]
    (A : Matrix m n K) :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n),
      Function.Injective r ∧ Function.Injective c ∧ (A.submatrix r c).det ≠ 0 := by
  classical
  cases nonempty_fintype m
  obtain ⟨κ, c, hc, hspan_c, hli_c⟩ := exists_linearIndependent' K A.col
  have : Finite κ := Finite.of_injective c hc
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcard_c : Fintype.card κ = A.rank := by
    rw [← finrank_span_range_col, ← hspan_c, finrank_span_eq_card hli_c]
  have hrank_sub : (A.submatrix id c).rank = Fintype.card κ := by
    rw [← finrank_span_range_col, show (A.submatrix id c).col = A.col ∘ c from rfl,
      finrank_span_eq_card hli_c]
  obtain ⟨μ, r, hr, hspan_r, hli_r⟩ := exists_linearIndependent' K (A.submatrix id c).row
  have : Finite μ := Finite.of_injective r hr
  let _ : Fintype μ := Fintype.ofFinite μ
  have hcard_r : Fintype.card μ = Fintype.card κ := by
    rw [← hrank_sub, ← finrank_span_range_row, ← hspan_r, finrank_span_eq_card hli_r]
  let ec : Fin A.rank ≃ κ := (Fintype.equivFinOfCardEq hcard_c).symm
  let er : Fin A.rank ≃ μ := (Fintype.equivFinOfCardEq (hcard_r.trans hcard_c)).symm
  refine ⟨r ∘ er, c ∘ ec, hr.comp er.injective, hc.comp ec.injective,
    IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp
      ?_))⟩
  have hrow : (A.submatrix (r ∘ er) (c ∘ ec)).row =
      LinearEquiv.funCongrLeft K K ec ∘ (((A.submatrix id c).row ∘ r) ∘ er) := by
    ext
    rfl
  rw [hrow]
  exact (hli_r.comp er er.injective).map' (LinearEquiv.funCongrLeft K K ec).toLinearMap
    (LinearEquiv.ker _)

/-- Eigenvector and eigenvalue equations transfer along any ring homomorphism. -/
theorem mulVec_map_eq_smul {m R S : Type*} [Semiring R] [Semiring S] [Fintype m]
    (f : R →+* S) (A : Matrix m m R) (v : m → R) (μ : R) (h : A *ᵥ v = μ • v) :
    A.map f *ᵥ (f ∘ v) = f μ • (f ∘ v) := by
  ext i
  rw [← f.map_mulVec A v, h]
  simp [map_mul]

/-- Tensor products of eigenvectors of `A` and `B` are eigenvectors of `A ⊗ₖ B` with eigenvalue
equal to the product of the individual eigenvalues ([AroraBarak07, Chapter 16, Exercise 14]). -/
theorem kronecker_mulVec_smul {m n R : Type*} [CommSemiring R] [Fintype m] [Fintype n]
    (A : Matrix m m R) (B : Matrix n n R) (u : m → R) (v : n → R) (μ ν : R)
    (hA : A *ᵥ u = μ • u) (hB : B *ᵥ v = ν • v) :
    (A ⊗ₖ B) *ᵥ (fun q => u q.1 * v q.2) = (μ * ν) • (fun q => u q.1 * v q.2) := by
  rw [kronecker_mulVec_mul, hA, hB]
  funext q
  simp [mul_mul_mul_comm]

/-- The tensor product vector `q ↦ u q.1 * v q.2` is nonzero if and only if both `u` and `v` are
nonzero ([AroraBarak07, Chapter 16, Exercise 14]). -/
theorem mul_prod_ne_zero_iff {m n R : Type*} [MulZeroClass R] [NoZeroDivisors R]
    {u : m → R} {v : n → R} :
    (fun q : m × n => u q.1 * v q.2) ≠ 0 ↔ u ≠ 0 ∧ v ≠ 0 := by
  simp [Function.ne_iff, exists_and_left, exists_and_right]

end Minors

/-! ### Exact rank of a Kronecker product -/

section KroneckerRank

/-- **Multiplicativity of rank under Kronecker product** over a field:
`(A ⊗ₖ B).rank = A.rank * B.rank`. -/
@[simp]
theorem rank_kronecker {l m n p K : Type*} [Field K] [Finite l] [Finite m] [Finite n] [Finite p]
    (A : Matrix l m K) (B : Matrix n p K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  refine le_antisymm (rank_kronecker_le A B) ?_
  obtain ⟨rA, cA, _, _, hdetA⟩ := exists_submatrix_det_ne_zero A
  obtain ⟨rB, cB, _, _, hdetB⟩ := exists_submatrix_det_ne_zero B
  have hunit : IsUnit (A.submatrix rA cA ⊗ₖ B.submatrix rB cB) :=
    (isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ <| by
      rw [det_kronecker]
      exact mul_ne_zero (pow_ne_zero _ hdetA) (pow_ne_zero _ hdetB))
  have hrank : (A.submatrix rA cA ⊗ₖ B.submatrix rB cB).rank = A.rank * B.rank := by
    simpa using rank_of_isUnit _ hunit
  have hsub : A.submatrix rA cA ⊗ₖ B.submatrix rB cB =
      (A ⊗ₖ B).submatrix (Prod.map rA rB) (Prod.map cA cB) := by
    ext ⟨_, _⟩ ⟨_, _⟩
    rfl
  rw [← hrank, hsub]
  exact rank_submatrix_le _ _ _

end KroneckerRank

/-! ### Flat `k`-fold Kronecker powers -/

section KroneckerPow

/-- The `k`-fold Kronecker power of `A : Matrix m n R`, indexed directly by `Fin k → m` and
`Fin k → n`, with `(x, y)`-entry `∏ i : Fin k, A (x i) (y i)`. -/
@[expose] def kroneckerPow {m n R : Type*} [CommMonoid R] (A : Matrix m n R) (k : ℕ) :
    Matrix (Fin k → m) (Fin k → n) R :=
  of fun x y => ∏ i : Fin k, A (x i) (y i)

@[simp]
theorem kroneckerPow_apply {m n R : Type*} [CommMonoid R] (A : Matrix m n R) (k : ℕ)
    (x : Fin k → m) (y : Fin k → n) :
    kroneckerPow A k x y = ∏ i : Fin k, A (x i) (y i) :=
  rfl

/-- The `0`-th Kronecker power is the `1 × 1` identity matrix on `Fin 0 → m`. -/
@[simp]
theorem kroneckerPow_zero {m R : Type*} [CommSemiring R] [DecidableEq m] (A : Matrix m m R) :
    kroneckerPow A 0 = 1 := by
  ext x y
  rw [Subsingleton.elim x y]
  simp

/-- Reindexing `kroneckerPow A 1` along `Equiv.funUnique` recovers `A`. -/
theorem kroneckerPow_one_submatrix {m n R : Type*} [CommMonoid R] (A : Matrix m n R) :
    (kroneckerPow A 1).submatrix (Equiv.funUnique (Fin 1) m).symm
      (Equiv.funUnique (Fin 1) n).symm = A := by
  ext i j
  simp [kroneckerPow]

/-- `kroneckerPow A (k + 1)` is `A ⊗ₖ kroneckerPow A k` reindexed along `Fin.consEquiv`. -/
theorem kroneckerPow_succ_eq_submatrix {m n R : Type*} [CommSemiring R] (A : Matrix m n R)
    (k : ℕ) :
    kroneckerPow A (k + 1) =
      (A ⊗ₖ kroneckerPow A k).submatrix (Fin.consEquiv fun _ => m).symm
        (Fin.consEquiv fun _ => n).symm := by
  ext x y
  simp only [kroneckerPow_apply, submatrix_apply, kroneckerMap_apply, Fin.prod_univ_succ,
    Fin.consEquiv_symm_apply]
  rfl

/-- Kronecker power distributes over matrix multiplication. -/
theorem kroneckerPow_mul {l m n R : Type*} [CommSemiring R] [Fintype m]
    (A : Matrix l m R) (B : Matrix m n R) (k : ℕ) :
    kroneckerPow (A * B) k = kroneckerPow A k * kroneckerPow B k := by
  ext x z
  simp only [kroneckerPow_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem kroneckerPow_one_matrix {m R : Type*} [CommSemiring R] [DecidableEq m] (k : ℕ) :
    kroneckerPow (1 : Matrix m m R) k = 1 := by
  ext x y
  rcases eq_or_ne x y with rfl | h
  · simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simpa [Matrix.one_apply, h] using Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- `kroneckerPow` commutes with matrix powers:
`kroneckerPow (A ^ d) k = (kroneckerPow A k) ^ d`. -/
theorem kroneckerPow_pow {m R : Type*} [CommSemiring R] [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (d k : ℕ) :
    kroneckerPow (A ^ d) k = (kroneckerPow A k) ^ d := by
  induction d with
  | zero => simp [pow_zero]
  | succ d ih => rw [pow_succ, pow_succ, kroneckerPow_mul, ih]

/-- The trace of a `k`-fold Kronecker power is the `k`-th power of the trace:
`(kroneckerPow A k).trace = A.trace ^ k`. -/
@[simp]
theorem trace_kroneckerPow {m R : Type*} [CommSemiring R] [Fintype m]
    (A : Matrix m m R) (k : ℕ) :
    (kroneckerPow A k).trace = A.trace ^ k := by
  simp only [trace, diag_apply, kroneckerPow_apply]
  rw [← Fintype.prod_sum (fun (_ : Fin k) j => A j j)]
  simp

/-- The trace of the `d`-th power of a `k`-fold Kronecker power equals `(A ^ d).trace ^ k`. -/
theorem trace_kroneckerPow_pow {m R : Type*} [CommSemiring R] [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (d k : ℕ) :
    ((kroneckerPow A k) ^ d).trace = (A ^ d).trace ^ k := by
  rw [← kroneckerPow_pow, trace_kroneckerPow]

/-- Transpose commutes with `kroneckerPow`. -/
@[simp]
theorem transpose_kroneckerPow {m n R : Type*} [CommMonoid R] (A : Matrix m n R) (k : ℕ) :
    (kroneckerPow A k)ᵀ = kroneckerPow Aᵀ k :=
  rfl

/-- Mapping along a monoid homomorphism commutes with `kroneckerPow`. -/
theorem map_kroneckerPow {m n R S : Type*} [CommMonoid R] [CommMonoid S]
    (f : R →* S) (A : Matrix m n R) (k : ℕ) :
    (kroneckerPow A k).map f = kroneckerPow (A.map f) k := by
  ext x y
  simp [map_prod]

/-- `kroneckerPow A k` acts coordinatewise on product vectors `y ↦ ∏ i, v i (y i)`. -/
theorem kroneckerPow_mulVec_prod {m n R : Type*} [CommSemiring R] [Fintype n]
    (A : Matrix m n R) (k : ℕ) (v : Fin k → n → R) :
    kroneckerPow A k *ᵥ (fun y => ∏ i, v i (y i)) = fun x => ∏ i, (A *ᵥ v i) (x i) := by
  funext x
  simp only [mulVec, dotProduct, kroneckerPow_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib.symm

/-- Tensor products of eigenvectors of `A` are eigenvectors of `kroneckerPow A k` with eigenvalue
equal to the product of the individual eigenvalues. -/
theorem kroneckerPow_mulVec_smul {m R : Type*} [CommSemiring R] [Fintype m]
    (A : Matrix m m R) (k : ℕ) (v : Fin k → m → R) (μ : Fin k → R)
    (h : ∀ i, A *ᵥ v i = μ i • v i) :
    kroneckerPow A k *ᵥ (fun y => ∏ i, v i (y i)) =
      (∏ i, μ i) • (fun y => ∏ i, v i (y i)) := by
  rw [kroneckerPow_mulVec_prod]
  funext x
  simp only [h, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- The `k`-fold tensor product vector `y ↦ ∏ i, v i (y i)` is nonzero if and only if every
factor `v i` is nonzero. -/
theorem prod_vec_ne_zero_iff {m R : Type*} [CommMonoidWithZero R] [NoZeroDivisors R]
    [Nontrivial R] {k : ℕ} {v : Fin k → m → R} :
    (fun y : Fin k → m => ∏ i, v i (y i)) ≠ 0 ↔ ∀ i, v i ≠ 0 := by
  simp only [Function.ne_iff, Pi.zero_apply, Finset.prod_ne_zero_iff, Finset.mem_univ,
    forall_true_left]
  exact ⟨fun ⟨y, hy⟩ i => ⟨y i, hy i⟩, fun h => by
    choose y hy using h
    exact ⟨y, hy⟩⟩

/-- **Rank of a Kronecker power** over a field: `(kroneckerPow A k).rank = A.rank ^ k`. -/
@[simp]
theorem rank_kroneckerPow {m n K : Type*} [Field K] [Finite m] [Finite n]
    (A : Matrix m n K) (k : ℕ) :
    (kroneckerPow A k).rank = A.rank ^ k := by
  cases nonempty_fintype m
  induction k with
  | zero =>
      have hli : LinearIndependent K (kroneckerPow A 0).row :=
        Fintype.linearIndependent_iff.mpr fun g hg i => by
          simpa [Subsingleton.elim i default, kroneckerPow] using congrFun hg default
      simpa using hli.rank_matrix
  | succ k ih =>
      rw [kroneckerPow_succ_eq_submatrix, rank_submatrix, rank_kronecker, ih, pow_succ']

end KroneckerPow

end Matrix

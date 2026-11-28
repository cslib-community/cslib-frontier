/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.DescriptorCertificate
public import CslibFrontier.Algorithms.LinearAlgebra.SparseLDLCertificate
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Structured index-one decouplings of sparse descriptor systems

`Cslib.LinearAlgebra.DecouplingCert` asks an untrusted tool for the dense matrices `P`, `Q` of
the Weierstrass form and their inverses, and checks eleven dense products. For a circuit, `E`
and `F` are very sparse, but `P` and `Q` are not: they contain the inverse of the algebraic block.
This file checks a decoupling in *Schur form* instead, and never forms that inverse.

The certificate `Cslib.LinearAlgebra.SparseDecouplingCert` consists of sparse transforms `T`, `U`
of the rows and of the unknowns, with sparse inverses `Tᵢ`, `Uᵢ`, such that

  `T E U = [[E₁₁, 0], [0, 0]]`,  `T F U = [[F₁₁, F₁₂], [F₂₁, F₂₂]]`

for a `k × k` block `E₁₁`, with sparse `LU` factors of `E₁₁` and `F₂₂` (so both are invertible),
the `r × k` matrix `K = F₂₂⁻¹ F₂₁` and the state matrix `A = E₁₁⁻¹ (F₁₁ - F₁₂ K)`. For a circuit,
`T` is a permutation and `U` is a permutation followed by a few eliminations for the floating
capacitors. The checker `SparseDecouplingCert.check` takes `E` and `F` as sparse rows (read with
`Cslib.LinearAlgebra.ofSparse`; `sparseOfRows` converts dense rows, and a netlist builds them
from its stamps) and recomputes, with sparse rational products,

  `Tᵢ T = 1`,  `U Uᵢ = 1`,  the blocks of `T E U` and `T F U`,  `E₁₁ = L U` and `F₂₂ = L' U'`
  (triangular, with nonzero diagonals),  `F₂₂ K = F₂₁`,  `E₁₁ A = F₁₁ - F₁₂ K`.

Acceptance yields an index-one decoupling of any real system with these `E` and `F`
(`SparseDecouplingCert.toDecoupling`) with state matrix `A`
(`SparseDecouplingCert.A_toDecoupling`), through the general construction
`DescriptorSystem.IndexOneDecoupling.ofSchur` of
`CslibFrontier.Foundations.Analysis.ODE.Descriptor`:

  `P = [[E₁₁⁻¹, -E₁₁⁻¹ F₁₂ F₂₂⁻¹], [0, F₂₂⁻¹]] T`,  `Q = U [[1, 0], [-K, 1]]`,

with inverses `Tᵢ [[E₁₁, F₁₂], [0, F₂₂]]` and `[[1, 0], [K, 1]] Uᵢ`. These matrices are real and
are never computed: only their sparse factors are checked. Every theorem about
`DescriptorSystem.IndexOneDecoupling` applies to the result.

## Main definitions

* `Cslib.LinearAlgebra.SparseDecouplingCert`, `SparseDecouplingCert.check`.
* `Cslib.LinearAlgebra.realOfSparse`, `Cslib.LinearAlgebra.sparseOfRows`.

## Main results

* `Cslib.LinearAlgebra.SparseDecouplingCert.toDecoupling`, `A_toDecoupling`, `Q₁'_toDecoupling`.
* `Cslib.LinearAlgebra.SparseDecouplingCert.isExponentiallyStableAt_of_check`.
-/

public section

open Matrix Mathlib.Tactic.Matrix

namespace Cslib.LinearAlgebra

/-! ### Sparse rows: zero tests, differences and blocks -/

section SparseRows

/-- `List.getD_map` with the default `[]`, for a map that sends `[]` to `[]`. -/
theorem getD_map_nil {β γ : Type*} (f : List β → List γ) (hf : f [] = [])
    (l : List (List β)) (i : ℕ) : (l.map f).getD i [] = f (l.getD i []) := by
  rw [← hf, List.getD_map]

/-- The sparse form of dense rows, without the zero entries. -/
@[expose] def sparseOfRows (rows : List (List ℚ)) : List (List (ℕ × ℚ)) :=
  rows.map fun r => (toSparseFrom 0 r).filter fun e => e.2 != 0

theorem sparseGet_filter_ne_zero (r : List (ℕ × ℚ)) (j : ℕ) :
    sparseGet (r.filter fun e => e.2 != 0) j = sparseGet r j := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    by_cases h : e.2 = 0
    · rw [List.filter_cons_of_neg (by simp [h]), ih, sparseGet_cons]
      split_ifs <;> simp [h]
    · rw [List.filter_cons_of_pos (by simp [h]), sparseGet_cons, sparseGet_cons, ih]

theorem ofSparse_sparseOfRows (m n : ℕ) (rows : List (List ℚ)) :
    ofSparse m n (sparseOfRows rows) = ofLists m n rows := by
  rw [← ofSparse_toSparse]
  ext i j
  rw [ofSparse_apply, ofSparse_apply, sparseOfRows, getD_map_nil _ rfl, getD_map_nil _ rfl,
    sparseGet_filter_ne_zero]

theorem length_sparseOfRows (rows : List (List ℚ)) : (sparseOfRows rows).length = rows.length :=
  List.length_map _

/-- Whether every row, with repeated columns merged, stores only zeros. -/
@[expose] def isZeroSparse (rows : List (List (ℕ × ℚ))) : Bool :=
  rows.all fun r => (sparseNormalize r).all fun e => e.2 == 0

theorem ofSparse_eq_zero_of_isZeroSparse {m n : ℕ} {rows : List (List (ℕ × ℚ))}
    (h : isZeroSparse rows = true) : ofSparse m n rows = 0 := by
  ext i j
  rw [ofSparse_apply, Matrix.zero_apply, ← sparseGet_sparseNormalize]
  refine sparseGet_eq_zero fun e he _ => ?_
  simp only [isZeroSparse, List.all_eq_true, beq_iff_eq] at h
  rw [List.getD_eq_getElem?_getD] at he
  rcases hi : rows[(i : ℕ)]? with _ | r
  · simp [hi, sparseNormalize] at he
  · rw [hi, Option.getD_some] at he
    exact h r (List.mem_of_getElem? hi) e he

/-- The rows of `X - Y`, without merging repeated columns. -/
@[expose] def subSparse : List (List (ℕ × ℚ)) → List (List (ℕ × ℚ)) → List (List (ℕ × ℚ))
  | r :: rs, s :: ss => (r ++ sparseMap (fun x => -x) s) :: subSparse rs ss
  | rs, [] => rs
  | [], ss => ss.map (sparseMap fun x => -x)

private theorem sparseGet_neg (s : List (ℕ × ℚ)) (j : ℕ) :
    sparseGet (sparseMap (fun x => -x) s) j = -sparseGet s j :=
  sparseGet_sparseMap neg_zero (fun a b => neg_add a b) s j

private theorem sparseGet_subSparse :
    ∀ (X Y : List (List (ℕ × ℚ))) (i j : ℕ),
      sparseGet ((subSparse X Y).getD i []) j =
        sparseGet (X.getD i []) j - sparseGet (Y.getD i []) j
  | r :: rs, s :: ss, 0, j => by
    simp [subSparse, sparseGet_append, sparseGet_neg, sub_eq_add_neg]
  | r :: rs, s :: ss, i + 1, j => by
    simpa [subSparse] using sparseGet_subSparse rs ss i j
  | rs, [], i, j => by cases rs <;> simp [subSparse]
  | [], s :: ss, i, j => by
    simp only [subSparse]
    rw [getD_map_nil _ rfl, sparseGet_neg]
    simp

theorem ofSparse_subSparse (m n : ℕ) (X Y : List (List (ℕ × ℚ))) :
    ofSparse m n (subSparse X Y) = ofSparse m n X - ofSparse m n Y := by
  ext i j
  simp only [ofSparse_apply, Matrix.sub_apply, sparseGet_subSparse]

/-- Whether `X` and `Y` read as the same matrix. -/
@[expose] def eqSparse (X Y : List (List (ℕ × ℚ))) : Bool := isZeroSparse (subSparse X Y)

theorem ofSparse_eq_of_eqSparse {m n : ℕ} {X Y : List (List (ℕ × ℚ))}
    (h : eqSparse X Y = true) : ofSparse m n X = ofSparse m n Y :=
  sub_eq_zero.1 ((ofSparse_subSparse m n X Y).symm.trans (ofSparse_eq_zero_of_isZeroSparse h))

/-- The sparse rows of the `n × n` identity. -/
@[expose] def oneSparse (n : ℕ) : List (List (ℕ × ℚ)) := List.ofFn fun i : Fin n => [(i.val, 1)]

theorem ofSparse_oneSparse (n : ℕ) : ofSparse n n (oneSparse n) = 1 := by
  ext i j
  simp [ofSparse_apply, oneSparse, List.getD_eq_getElem?_getD, sparseGet_cons, Matrix.one_apply,
    Fin.val_inj]

/-- The entries of a sparse row in the columns below `k`. -/
@[expose] def loCols (k : ℕ) (r : List (ℕ × ℚ)) : List (ℕ × ℚ) := r.filter fun e => Nat.blt e.1 k

/-- The entries of a sparse row in the columns from `k` on, shifted by `k`. -/
@[expose] def hiCols (k : ℕ) (r : List (ℕ × ℚ)) : List (ℕ × ℚ) :=
  (r.filter fun e => Nat.ble k e.1).map fun e => (e.1 - k, e.2)

/-- `loCols` keeps the entries in the columns below `k`. -/
theorem sparseGet_loCols (k : ℕ) (r : List (ℕ × ℚ)) {j : ℕ} (hj : j < k) :
    sparseGet (loCols k r) j = sparseGet r j := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    simp only [loCols] at ih ⊢
    by_cases he : e.1 < k
    · rw [List.filter_cons_of_pos (by simpa using he), sparseGet_cons, sparseGet_cons, ih]
    · rw [List.filter_cons_of_neg (by simpa using he), ih, sparseGet_cons,
        ite_eq_right (by omega)]

/-- `hiCols` shifts the entries in the columns from `k` on. -/
theorem sparseGet_hiCols (k : ℕ) (r : List (ℕ × ℚ)) (j : ℕ) :
    sparseGet (hiCols k r) j = sparseGet r (k + j) := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    simp only [hiCols] at ih ⊢
    by_cases he : k ≤ e.1
    · rw [List.filter_cons_of_pos (by simpa using he), List.map_cons, sparseGet_cons,
        sparseGet_cons, ih]
      simp only
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    · rw [List.filter_cons_of_neg (by simpa using he), ih, sparseGet_cons, ite_eq_right (by omega)]

/-- The four blocks of sparse rows split after row and column `k`. -/
@[expose] def blk₁₁ (k : ℕ) (X : List (List (ℕ × ℚ))) := (X.take k).map (loCols k)
/-- See `blk₁₁`. -/
@[expose] def blk₁₂ (k : ℕ) (X : List (List (ℕ × ℚ))) := (X.take k).map (hiCols k)
/-- See `blk₁₁`. -/
@[expose] def blk₂₁ (k : ℕ) (X : List (List (ℕ × ℚ))) := (X.drop k).map (loCols k)
/-- See `blk₁₁`. -/
@[expose] def blk₂₂ (k : ℕ) (X : List (List (ℕ × ℚ))) := (X.drop k).map (hiCols k)

/-- The split `Fin N ≃ Fin k ⊕ Fin r` for `k + r = N`. -/
@[expose] def blockEquiv {k r N : ℕ} (h : k + r = N) : Fin N ≃ Fin k ⊕ Fin r :=
  (finCongr h.symm).trans finSumFinEquiv.symm

theorem ofSparse_submatrix_blockEquiv {k r N : ℕ} (h : k + r = N) (X : List (List (ℕ × ℚ))) :
    (ofSparse N N X).submatrix (blockEquiv h).symm (blockEquiv h).symm =
      fromBlocks (ofSparse k k (blk₁₁ k X)) (ofSparse k r (blk₁₂ k X))
        (ofSparse r k (blk₂₁ k X)) (ofSparse r r (blk₂₂ k X)) := by
  have hl : ∀ (p : ℕ) (f : List (ℕ × ℚ) → List (ℕ × ℚ)), f [] = [] → ∀ Y : List (List (ℕ × ℚ)),
      sparseGet ((Y.map f).getD p []) = sparseGet (f (Y.getD p [])) := fun p f hf Y => by
    rw [getD_map_nil f hf]
  have he₁ : ∀ i : Fin k, (((blockEquiv h).symm (Sum.inl i)) : ℕ) = i := fun _ => by
    simp [blockEquiv]
  have he₂ : ∀ i : Fin r, (((blockEquiv h).symm (Sum.inr i)) : ℕ) = k + i := fun _ => by
    simp [blockEquiv]
  have ht : ∀ i : Fin k, (X.take k).getD i [] = X.getD i [] := fun i => by
    simp [List.getD_eq_getElem?_getD, i.is_lt]
  have hd : ∀ i : ℕ, (X.drop k).getD i [] = X.getD (k + i) [] := fun i => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  ext (i | i) (j | j) <;>
    simp only [submatrix_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, ofSparse_apply, he₁, he₂, blk₁₁, blk₁₂, blk₂₁, blk₂₂,
      hl _ _ (rfl : loCols k [] = []), hl _ _ (rfl : hiCols k [] = []), sparseGet_hiCols,
      sparseGet_loCols _ _ j.is_lt, ht, hd]

/-! #### Triangular factors -/

/-- Whether row `i + p` of `rows`, for every `p`, has its columns at most `i + p` (`lower`) or
at least `i + p` (otherwise) and a nonzero diagonal entry. -/
@[expose] def triGo (lower : Bool) : ℕ → List (List (ℕ × ℚ)) → Bool
  | _, [] => true
  | i, r :: rs => r.all (fun e => bif lower then Nat.ble e.1 i else Nat.ble i e.1) &&
      sparseGet r i != 0 && triGo lower (i + 1) rs

/-- Whether `rows` is an `n × n` triangular matrix (lower if `lower`) with nonzero diagonal. -/
@[expose] def isTriangular (lower : Bool) (n : ℕ) (rows : List (List (ℕ × ℚ))) : Bool :=
  rows.length == n && triGo lower 0 rows

private theorem triGo_spec {lower : Bool} :
    ∀ {i : ℕ} {rows : List (List (ℕ × ℚ))}, triGo lower i rows = true → ∀ p < rows.length,
      (∀ e ∈ rows.getD p [], if lower then e.1 ≤ i + p else i + p ≤ e.1) ∧
        sparseGet (rows.getD p []) (i + p) ≠ 0
  | _, [], _, p, hp => absurd hp (Nat.not_lt_zero _)
  | i, r :: rs, h, p, hp => by
    simp only [triGo, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
    rcases p with _ | p
    · refine ⟨fun e he => ?_, by simpa using h₂⟩
      have := h₁ e (by simpa using he)
      cases lower <;> simpa using this
    · have := triGo_spec h₃ p (by simpa using hp)
      simpa [show i + (p + 1) = i + 1 + p by omega] using this

theorem det_ne_zero_of_isTriangular {lower : Bool} {n : ℕ} {rows : List (List (ℕ × ℚ))}
    (h : isTriangular lower n rows = true) : (ofSparse n n rows).det ≠ 0 := by
  simp only [isTriangular, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, h⟩ := h
  have hs := triGo_spec h
  have hdiag : ∀ i : Fin n, ofSparse n n rows i i ≠ 0 := fun i => by
    simpa [ofSparse_apply] using (hs i (by omega)).2
  have hzero : ∀ (i j : Fin n), (if lower then (i : ℕ) < j else (j : ℕ) < i) →
      ofSparse n n rows i j = 0 := fun i j hij => by
    rw [ofSparse_apply]
    refine sparseGet_eq_zero fun e he hej => ?_
    have := (hs i (by omega)).1 e (by simpa using he)
    cases lower <;> simp_all <;> omega
  cases lower
  · rw [det_of_isUpperTriangular fun i j hij => hzero i j (by simpa using hij)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hdiag i
  · rw [det_of_isLowerTriangular _ fun i j hij => hzero i j (by simpa using hij)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hdiag i

/-- Whether `M = L U` for an `n × n` lower triangular `L` and upper triangular `U` with nonzero
diagonals, so that `M` is invertible. -/
@[expose] def isLUOf (n : ℕ) (L U M : List (List (ℕ × ℚ))) : Bool :=
  isTriangular true n L && isTriangular false n U && eqSparse (sparseMul L U) M

theorem det_ne_zero_of_isLUOf {n : ℕ} {L U M : List (List (ℕ × ℚ))}
    (h : isLUOf n L U M = true) : (ofSparse n n M).det ≠ 0 := by
  simp only [isLUOf, Bool.and_eq_true] at h
  obtain ⟨⟨hL, hU⟩, hM⟩ := h
  have hUl : U.length = n := by
    simp only [isTriangular, Bool.and_eq_true, beq_iff_eq] at hU; exact hU.1
  rw [← ofSparse_eq_of_eqSparse hM, ofSparse_sparseMul _ _ hUl.le, det_mul]
  exact mul_ne_zero (det_ne_zero_of_isTriangular hL) (det_ne_zero_of_isTriangular hU)

end SparseRows

/-! ### Structured decoupling certificates -/

/-- A proposed index-one decoupling in Schur form of a descriptor system with `N = k + r`
unknowns; see the module documentation. All matrices are sparse rational rows, except the
dense state matrix `A`. -/
structure SparseDecouplingCert where
  /-- The number of differential coordinates. -/
  k : ℕ
  /-- The number of algebraic coordinates. -/
  r : ℕ
  /-- `N × N`: the row transform; its first `k` rows produce the differential equations. -/
  T : List (List (ℕ × ℚ))
  /-- `N × N`: the inverse of `T`, checked as `Tᵢ T = 1`. -/
  Tᵢ : List (List (ℕ × ℚ))
  /-- `N × N`: the transform of the unknowns; its first `k` columns are differential. -/
  U : List (List (ℕ × ℚ))
  /-- `N × N`: the inverse of `U`, checked as `U Uᵢ = 1`. -/
  Uᵢ : List (List (ℕ × ℚ))
  /-- `k × k`: the lower triangular factor of `E₁₁`. -/
  LE : List (List (ℕ × ℚ))
  /-- `k × k`: the upper triangular factor of `E₁₁`. -/
  UE : List (List (ℕ × ℚ))
  /-- `r × r`: the lower triangular factor of `F₂₂`. -/
  LF : List (List (ℕ × ℚ))
  /-- `r × r`: the upper triangular factor of `F₂₂`. -/
  UF : List (List (ℕ × ℚ))
  /-- `r × k`: the solution `K` of `F₂₂ K = F₂₁`. -/
  K : List (List (ℕ × ℚ))
  /-- `k × k`: the reduced state matrix `E₁₁⁻¹ (F₁₁ - F₁₂ K)`, checked. -/
  A : List (List ℚ)

namespace SparseDecouplingCert

variable (c : SparseDecouplingCert) (N : ℕ)

/-- The sparse rows of `T X U`. -/
abbrev bar (X : List (List (ℕ × ℚ))) : List (List (ℕ × ℚ)) :=
  sparseMul (sparseMul c.T X) c.U

/-- Whether `c` is an index-one decoupling in Schur form of the pencil `(E, F)` with `N`
unknowns, given by sparse rows. All products are sparse and exact over `ℚ`. -/
@[expose] def check (E F : List (List (ℕ × ℚ))) : Bool :=
  let Eb := c.bar E
  let Fb := c.bar F
  c.k + c.r == N && Nat.ble E.length N && Nat.ble F.length N && c.T.length == N &&
  c.U.length == N && c.Uᵢ.length == N && c.K.length == c.r && c.A.length == c.k &&
  eqSparse (sparseMul c.Tᵢ c.T) (oneSparse N) &&
  eqSparse (sparseMul c.U c.Uᵢ) (oneSparse N) &&
  isZeroSparse (blk₁₂ c.k Eb) && isZeroSparse (blk₂₁ c.k Eb) && isZeroSparse (blk₂₂ c.k Eb) &&
  isLUOf c.k c.LE c.UE (blk₁₁ c.k Eb) && isLUOf c.r c.LF c.UF (blk₂₂ c.k Fb) &&
  eqSparse (sparseMul (blk₂₂ c.k Fb) c.K) (blk₂₁ c.k Fb) &&
  eqSparse (sparseMul (blk₁₁ c.k Eb) (sparseOfRows c.A))
    (subSparse (blk₁₁ c.k Fb) (sparseMul (blk₁₂ c.k Fb) c.K))

end SparseDecouplingCert

/-- The real matrix of sparse rational rows. -/
abbrev realOfSparse (m n : ℕ) (rows : List (List (ℕ × ℚ))) : Matrix (Fin m) (Fin n) ℝ :=
  (ofSparse m n rows).map ((↑) : ℚ → ℝ)

theorem realOfSparse_sparseOfRows (m n : ℕ) (rows : List (List ℚ)) :
    realOfSparse m n (sparseOfRows rows) = realOfRows m n rows := by
  rw [realOfSparse, ofSparse_sparseOfRows]

namespace SparseDecouplingCert

variable {c : SparseDecouplingCert} {N : ℕ}

/-- `sparseMul` computes the real matrix product when the right factor has at most `m` rows. -/
theorem realOfSparse_mul {l m n : ℕ} (X Y : List (List (ℕ × ℚ))) (hY : Y.length ≤ m) :
    realOfSparse l n (sparseMul X Y) = realOfSparse l m X * realOfSparse m n Y := by
  rw [realOfSparse, ofSparse_sparseMul _ _ hY, map_mul_ratCast]

/-- `subSparse` computes the real difference. -/
theorem realOfSparse_sub {m n : ℕ} (X Y : List (List (ℕ × ℚ))) :
    realOfSparse m n (subSparse X Y) = realOfSparse m n X - realOfSparse m n Y := by
  ext i j
  simp [ofSparse_subSparse]

private theorem isUnit_det_realOfSparse {n : ℕ} {L U M : List (List (ℕ × ℚ))}
    (h : isLUOf n L U M = true) : IsUnit (realOfSparse n n M).det := by
  have : (realOfSparse n n M).det = (((ofSparse n n M).det : ℚ) : ℝ) :=
    (RingHom.map_det (Rat.castHom ℝ) (ofSparse n n M)).symm
  rw [this, isUnit_iff_ne_zero]
  exact Rat.cast_ne_zero.2 (det_ne_zero_of_isLUOf h)

private theorem submatrix_transform (h : c.k + c.r = N) (X : Matrix (Fin N) (Fin N) ℝ) :
    (realOfSparse N N c.T).submatrix (blockEquiv h).symm id * X *
        (realOfSparse N N c.U).submatrix id (blockEquiv h).symm =
      (realOfSparse N N c.T * X * realOfSparse N N c.U).submatrix (blockEquiv h).symm
        (blockEquiv h).symm := rfl

/-- The blocks of a transformed matrix, as real matrices. -/
private theorem transform_blocks (h : c.k + c.r = N) (hU : c.U.length = N)
    {X : List (List (ℕ × ℚ))} (hX : X.length ≤ N) :
    (realOfSparse N N c.T).submatrix (blockEquiv h).symm id * realOfSparse N N X *
        (realOfSparse N N c.U).submatrix id (blockEquiv h).symm =
      fromBlocks (realOfSparse c.k c.k (blk₁₁ c.k (sparseMul (sparseMul c.T X) c.U)))
        (realOfSparse c.k c.r (blk₁₂ c.k (sparseMul (sparseMul c.T X) c.U)))
        (realOfSparse c.r c.k (blk₂₁ c.k (sparseMul (sparseMul c.T X) c.U)))
        (realOfSparse c.r c.r (blk₂₂ c.k (sparseMul (sparseMul c.T X) c.U))) := by
  rw [submatrix_transform, ← realOfSparse_mul _ _ hX, ← realOfSparse_mul _ _ hU.le,
    ← fromBlocks_map, ← ofSparse_submatrix_blockEquiv h]
  rfl

variable {m : ℕ} {E F : List (List (ℕ × ℚ))}

/-- The facts that an accepted certificate provides, as real matrices: the hypotheses of
`DescriptorSystem.IndexOneDecoupling.ofSchur`, and the equation `E₁₁ A = F₁₁ - F₁₂ K`. -/
structure Spec (c : SparseDecouplingCert) (N : ℕ) (E F : List (List (ℕ × ℚ))) : Prop where
  /-- The split `N = k + r`. -/
  hN : c.k + c.r = N
  /-- `Tᵢ T = 1`. -/
  hT : (realOfSparse N N c.Tᵢ).submatrix id (blockEquiv hN).symm *
    (realOfSparse N N c.T).submatrix (blockEquiv hN).symm id = 1
  /-- `U Uᵢ = 1`. -/
  hU : (realOfSparse N N c.U).submatrix id (blockEquiv hN).symm *
    (realOfSparse N N c.Uᵢ).submatrix (blockEquiv hN).symm id = 1
  /-- `T E U = [[E₁₁, 0], [0, 0]]`. -/
  hE : (realOfSparse N N c.T).submatrix (blockEquiv hN).symm id * realOfSparse N N E *
      (realOfSparse N N c.U).submatrix id (blockEquiv hN).symm =
    fromBlocks (realOfSparse c.k c.k (blk₁₁ c.k (c.bar E))) 0 0 0
  /-- The blocks of `T F U`. -/
  hF : (realOfSparse N N c.T).submatrix (blockEquiv hN).symm id * realOfSparse N N F *
      (realOfSparse N N c.U).submatrix id (blockEquiv hN).symm =
    fromBlocks (realOfSparse c.k c.k (blk₁₁ c.k (c.bar F)))
      (realOfSparse c.k c.r (blk₁₂ c.k (c.bar F))) (realOfSparse c.r c.k (blk₂₁ c.k (c.bar F)))
      (realOfSparse c.r c.r (blk₂₂ c.k (c.bar F)))
  /-- `E₁₁` is invertible. -/
  hE₁₁ : IsUnit (realOfSparse c.k c.k (blk₁₁ c.k (c.bar E))).det
  /-- `F₂₂` is invertible. -/
  hF₂₂ : IsUnit (realOfSparse c.r c.r (blk₂₂ c.k (c.bar F))).det
  /-- `F₂₂ K = F₂₁`. -/
  hK : realOfSparse c.r c.r (blk₂₂ c.k (c.bar F)) * realOfSparse c.r c.k c.K =
    realOfSparse c.r c.k (blk₂₁ c.k (c.bar F))
  /-- `E₁₁ A = F₁₁ - F₁₂ K`. -/
  hA : realOfSparse c.k c.k (blk₁₁ c.k (c.bar E)) * realOfRows c.k c.k c.A =
    realOfSparse c.k c.k (blk₁₁ c.k (c.bar F)) -
      realOfSparse c.k c.r (blk₁₂ c.k (c.bar F)) * realOfSparse c.r c.k c.K

/-- An accepted certificate satisfies `Spec`. -/
theorem spec (h : c.check N E F = true) : c.Spec N E F := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq, and_assoc] at h
  obtain ⟨hN, hEl, hFl, hTl, hUl, hUil, hKl, hAl, hT, hU, hE₁₂, hE₂₁, hE₂₂, hLE, hLF, hK, hA⟩ :=
    h
  refine ⟨hN, ?_, ?_, ?_, transform_blocks hN hUl hFl, isUnit_det_realOfSparse hLE,
    isUnit_det_realOfSparse hLF, ?_, ?_⟩
  · rw [submatrix_mul_equiv _ _ id (blockEquiv hN).symm id, submatrix_id_id,
      ← realOfSparse_mul _ _ hTl.le, realOfSparse, ofSparse_eq_of_eqSparse hT, ofSparse_oneSparse,
      Matrix.map_one _ Rat.cast_zero Rat.cast_one]
  · rw [submatrix_mul_equiv _ _ id (blockEquiv hN).symm id, submatrix_id_id,
      ← realOfSparse_mul _ _ hUil.le, realOfSparse, ofSparse_eq_of_eqSparse hU, ofSparse_oneSparse,
      Matrix.map_one _ Rat.cast_zero Rat.cast_one]
  · rw [transform_blocks hN hUl hEl]
    simp only [realOfSparse, ofSparse_eq_zero_of_isZeroSparse hE₁₂,
      ofSparse_eq_zero_of_isZeroSparse hE₂₁, ofSparse_eq_zero_of_isZeroSparse hE₂₂,
      Matrix.map_zero _ Rat.cast_zero]
  · rw [← realOfSparse_mul _ _ hKl.le]
    exact congrArg (Matrix.map · _) (ofSparse_eq_of_eqSparse hK)
  · rw [← realOfSparse_sparseOfRows, ← realOfSparse_mul _ _ (by rw [length_sparseOfRows, hAl]),
      ← realOfSparse_mul _ _ hKl.le, ← realOfSparse_sub]
    exact congrArg (Matrix.map · _) (ofSparse_eq_of_eqSparse hA)

variable {S : DescriptorSystem (Fin N) (Fin m)}

/-- **Soundness.** An accepted certificate for the sparse rows of `S.E` and `S.F` gives an
index-one decoupling of `S`, by `DescriptorSystem.IndexOneDecoupling.ofSchur`. -/
@[expose] noncomputable def toDecoupling (hE : S.E = realOfSparse N N E)
    (hF : S.F = realOfSparse N N F) (h : c.check N E F = true) :
    S.IndexOneDecoupling (Fin c.k) (Fin c.r) :=
  DescriptorSystem.IndexOneDecoupling.ofSchur (blockEquiv (spec h).hN)
    _ _ _ _ _ _ _ _ _ _ (spec h).hT (spec h).hU (hE ▸ (spec h).hE) (hF ▸ (spec h).hF)
    (spec h).hE₁₁ (spec h).hF₂₂ (spec h).hK

/-- The state matrix of the decoupling is the matrix of the checked `SparseDecouplingCert.A`. -/
theorem A_toDecoupling (hE : S.E = realOfSparse N N E) (hF : S.F = realOfSparse N N F)
    (h : c.check N E F = true) : (toDecoupling hE hF h).A = realOfRows c.k c.k c.A := by
  unfold toDecoupling
  refine (DescriptorSystem.IndexOneDecoupling.A_ofSchur ..).trans ?_
  rw [← (spec h).hA, ← Matrix.mul_assoc, nonsing_inv_mul _ (spec h).hE₁₁, Matrix.one_mul]

/-- The differential coordinates of the decoupling are the first `c.k` rows of `Uᵢ`. -/
theorem Q₁'_toDecoupling (hE : S.E = realOfSparse N N E) (hF : S.F = realOfSparse N N F)
    (h : c.check N E F = true) : (toDecoupling hE hF h).Q₁' = realOfSparse c.k N c.Uᵢ := by
  unfold toDecoupling
  refine (DescriptorSystem.IndexOneDecoupling.Q₁'_ofSchur ..).trans ?_
  ext i j
  simp [blockEquiv, toRows₁, realOfSparse, ofSparse_apply]

/-- **Descriptor stability from the reduced matrix.** If `c` is an accepted structured
decoupling of the sparse rows of `S.E` and `S.F`, `z₀` is an equilibrium and `ẋ = A x` is
exponentially stable for the checked reduced matrix `c.A`, then every solution with zero input
of `S` converges to `z₀` exponentially, in the Euclidean norm. -/
theorem isExponentiallyStableAt_of_check {z₀ : Fin N → ℝ} (hE : S.E = realOfSparse N N E)
    (hF : S.F = realOfSparse N N F) (hc : c.check N E F = true) (hz : S.IsEquilibrium z₀)
    (hA : (toEuclideanCLM (𝕜 := ℝ) (realOfRows c.k c.k c.A)).IsExponentiallyStable) :
    S.IsExponentiallyStableAt z₀ :=
  (toDecoupling hE hF hc).isExponentiallyStableAt hz (A_toDecoupling hE hF hc ▸ hA)

end SparseDecouplingCert

end Cslib.LinearAlgebra

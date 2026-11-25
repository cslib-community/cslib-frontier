/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.LDLCertificate
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Sparse and envelope `LDLᵀ` certificates, checked by the kernel

The dense checker `Cslib.LinearAlgebra.LDLCert` costs about `n³ / 6` integer products for an
`n × n` matrix, whatever its sparsity, and the dense Lyapunov residual about `2 n³`. The state
matrix of a circuit has a few entries per row, and a Lyapunov matrix `P` can often be chosen
banded. This module checks such certificates at a cost governed by the *envelope* of the factor
instead of by `n`. Its soundness theorems are about the same real matrices as those of the dense
checker (`Matrix.PosDef` and `Matrix.PosSemidef` of a rational matrix cast to `ℝ`), so the
stability and impulse-response theorems built on them apply unchanged.

## Sparse rows

A sparse matrix is a list of rows, each a list of `(column, value)` pairs, read by
`Cslib.LinearAlgebra.ofSparse m n rows`: entry `(i, j)` is the sum of the values that row `i`
stores at column `j` (`Cslib.LinearAlgebra.sparseGet`), and a missing row is zero. The reading
does not depend on the order of the pairs or on repeated columns, so the soundness proofs assume
nothing about them; the checkers nevertheless reject an input matrix whose rows do not have
strictly increasing columns below `n`, or that does not have `n` rows
(`Cslib.LinearAlgebra.isSparseShape`), as the dense checkers reject a ragged matrix.
`Cslib.LinearAlgebra.ofSparse_toSparse` reads the sparse form of dense rows as `ofLists`.

Rows are reached through a zipper (`Cslib.LinearAlgebra.zget`): while row `i` is processed, the
rows before it are kept reversed and the rows from it on in order, so that reaching row `k`
costs `|i - k|` steps instead of `k`. The sparse product `Cslib.LinearAlgebra.sparseMul` and
the transpose check `Cslib.LinearAlgebra.isTransposeOf` thus cost about the number of stored
entries times their distance from the diagonal.

## Envelope certificates with a remainder

A certificate `Cslib.LinearAlgebra.EnvLDLCert` for a symmetric `M` gives a unit lower-triangular
`L` by envelope, a diagonal `d` and a sparse symmetric remainder `R` with
`M = L * diagonal d * Lᵀ + R`. Row `i` of `L` is its first column `fᵢ` and its entries
`L i fᵢ, …, L i i`, ending in `1`; the entries left of `fᵢ` are zero. The factors are the
dense certificate `EnvLDLCert.toLDLCert`, with the rows padded by zeros, so `L` and `d` are the
matrices `LDLCert.L` and `LDLCert.d` of the dense checker. `R` must be diagonally dominant,
`∑_{j ≠ i} |R i j| ≤ R i i` (`Cslib.LinearAlgebra.ddGo`), hence positive semidefinite
(`Cslib.LinearAlgebra.posSemidef_of_diagDominant`); with positive pivots `M ≻ 0` follows.

The remainder keeps the certificate small. The exact factor of a banded matrix stays in the
band, but its entries grow by a few bits per row: about 10⁴ bits, and megabytes of source, for a
`512`-state ladder. An untrusted tool instead factors `M - ε • 1` in floating point, rounds `L`
and `d` to a dyadic grid, and lists the exact `R = M - L * diagonal d * Lᵀ`, which is about
`ε • 1` plus rounding errors, diagonally dominant once the grid is fine enough; its entries have
a bounded number of bits whatever `n` is. An exact factorization is the certificate with
`R = 0` (`rem = []`), and `EnvLDLCert.eq_of_factors` then states the factorization.

The check (`EnvLDLCert.factorsLower`, applied to `M - R`) compares, on the envelope, the entries
of `M - R` with those of `L * diagonal d * Lᵀ`, in integers: row `i` of `L` is scaled by the lcm
`sᵢ` of its denominators, and the row `uᵢ = (L i k * d k)ₖ` of `L * diagonal d` by its own lcm
`tᵢ`, so that entry `(i, j)` is checked as `num x * (tᵢ * sⱼ) = (∑ₖ ûᵢₖ âⱼₖ) * den x`, a dot
product over the overlap of the two rows' envelopes (`Cslib.LinearAlgebra.alignDot`). The
common scale of all of `d` that the dense checker uses would, for an exact factor, be the lcm of
all pivots' denominators, which grows quadratically in `n`, while each `tᵢ` involves only the
pivots in one row's envelope. The data of the rows above row `i` are kept in a reversed list,
of which row `i` reads the first `i - fᵢ`. Left of the envelope the check asks that `M - R`
store only zeros; there `L * diagonal d * Lᵀ` vanishes by construction. The cost is about
`∑ᵢ ∑_{j ∈ [fᵢ, i]} (j - max fᵢ fⱼ + 1)` products, which is `O(n w²)` for bandwidth `w`.

## The Lyapunov residual

`Cslib.LinearAlgebra.SparseLyapunovCert.check` recomputes `-(Aᵀ * P + P * A)` from sparse `A`
and `P`. The certificate carries the rows of `Aᵀ`, which the checker verifies against `A`, so
that both products `Aᵀ * P` and `P * A` take rows from rows. As in the dense checker, `A`, `Aᵀ`
and `P` are scaled to integers by the lcm of their denominators for the products
(`Cslib.LinearAlgebra.sparseScaledResidual`), each row of the residual is normalized by merging
repeated columns (`Cslib.LinearAlgebra.sparseNormalize`), and the residual's symmetry is proved
from that of the accepted `P`, not checked.

## Certificate layout

A certificate is Lean source. Write every rational entry of a sparse row, of `lower` and of
`diag` as `mkRat (.ofNat p) q` or `mkRat (.negSucc p) q`, and give each field its own
definition with its type. Numerals of `ℤ` or `ℚ` inside the pairs of a long list literal make
elaboration superlinear (typeclass inference dominates; a list of 2000 such pairs exceeds the
default heartbeat limit), while natural-number literals and explicit constructors elaborate in
linear time. The kernel evaluates `mkRat` like the division it replaces.

## Main definitions

* `Cslib.LinearAlgebra.sparseGet`, `Cslib.LinearAlgebra.ofSparse`,
  `Cslib.LinearAlgebra.isSparseShape`: the sparse format.
* `Cslib.LinearAlgebra.sparseMul`, `Cslib.LinearAlgebra.isTransposeOf`,
  `Cslib.LinearAlgebra.sparseNormalize`, `Cslib.LinearAlgebra.subRows`,
  `Cslib.LinearAlgebra.ddGo`: operations that the kernel evaluates.
* `Cslib.LinearAlgebra.EnvLDLCert`, `EnvLDLCert.factors`, `EnvLDLCert.checkPosDef`,
  `EnvLDLCert.checkPosSemidef`: envelope certificates for sparse symmetric matrices.
* `Cslib.LinearAlgebra.sparseResidual`, `Cslib.LinearAlgebra.SparseLyapunovCert`,
  `SparseLyapunovCert.check`.

## Main results

* `Cslib.LinearAlgebra.ofSparse_toSparse`, `Cslib.LinearAlgebra.ofSparse_sparseMul`,
  `Cslib.LinearAlgebra.ofSparse_eq_transpose_of_isTransposeOf`,
  `Cslib.LinearAlgebra.ofSparse_sparseResidual`: the operations compute the matrix ones.
* `Cslib.LinearAlgebra.posSemidef_of_diagDominant`: diagonal dominance gives `⪰ 0`.
* `Cslib.LinearAlgebra.EnvLDLCert.eq_add_of_factorsWith`: an accepted certificate writes `M` as
  `L * diagonal d * Lᵀ + R`.
* `Cslib.LinearAlgebra.EnvLDLCert.posDef_of_checkPosDef`,
  `Cslib.LinearAlgebra.EnvLDLCert.posSemidef_of_checkPosSemidef`: soundness over `ℝ`.
* `Cslib.LinearAlgebra.SparseLyapunovCert.posDef_of_check`: `P ≻ 0` and
  `-(Aᵀ * P + P * A) ≻ 0` over `ℝ`, with the statement of the dense
  `Cslib.LinearAlgebra.LyapunovCert.posDef_of_check`.
-/

public section

open Matrix Mathlib.Tactic.Matrix

namespace Cslib.LinearAlgebra

/-! ### Sparse rows -/

section Sparse

variable {α : Type*}

/-- The value of a sparse row at column `j`: the sum of the values stored at `j`. -/
@[expose] def sparseGet [Add α] [Zero α] : List (ℕ × α) → ℕ → α
  | [], _ => 0
  | e :: r, j => bif Nat.beq e.1 j then e.2 + sparseGet r j else sparseGet r j

@[simp] theorem sparseGet_nil [Add α] [Zero α] (j : ℕ) :
    sparseGet ([] : List (ℕ × α)) j = 0 := rfl

theorem sparseGet_cons [Add α] [Zero α] (e : ℕ × α) (r : List (ℕ × α)) (j : ℕ) :
    sparseGet (e :: r) j = if e.1 = j then e.2 + sparseGet r j else sparseGet r j := by
  simp only [sparseGet, cond_eq_ite, Nat.beq_eq]

theorem sparseGet_append [AddMonoid α] (r s : List (ℕ × α)) (j : ℕ) :
    sparseGet (r ++ s) j = sparseGet r j + sparseGet s j := by
  induction r with
  | nil => simp
  | cons e r ih =>
    simp only [List.cons_append, sparseGet_cons, ih]
    split_ifs <;> simp [add_assoc]

/-- A column at which every stored value is zero has value zero. -/
theorem sparseGet_eq_zero [AddMonoid α] {r : List (ℕ × α)} {j : ℕ}
    (h : ∀ e ∈ r, e.1 = j → e.2 = 0) : sparseGet r j = 0 := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    have ih' := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [sparseGet_cons]
    split_ifs with he
    · rw [h e List.mem_cons_self he, ih', add_zero]
    · exact ih'

/-- The matrix of a list of sparse rows: entry `(i, j)` is `sparseGet` of row `i` at `j`, and a
missing row is zero. -/
@[expose] def ofSparse [Add α] [Zero α] (m n : ℕ) (rows : List (List (ℕ × α))) :
    Matrix (Fin m) (Fin n) α :=
  of fun i j => sparseGet (rows.getD i []) j

theorem ofSparse_apply [Add α] [Zero α] (m n : ℕ) (rows : List (List (ℕ × α))) (i : Fin m)
    (j : Fin n) : ofSparse m n rows i j = sparseGet (rows.getD i []) j := rfl

/-- Whether the columns of a sparse row strictly increase from at least `c` and stay below
`n`. -/
@[expose] def colsAbove (n : ℕ) : ℕ → List (ℕ × α) → Bool
  | _, [] => true
  | c, e :: r => c ≤ e.1 && e.1 < n && colsAbove n (e.1 + 1) r

/-- Whether `rows` has exactly `m` rows, each with strictly increasing columns below `n`. -/
@[expose] def isSparseShape (m n : ℕ) (rows : List (List (ℕ × α))) : Bool :=
  rows.length == m && rows.all (colsAbove n 0)

theorem length_of_isSparseShape {m n : ℕ} {rows : List (List (ℕ × α))}
    (h : isSparseShape m n rows = true) : rows.length = m := by
  simp only [isSparseShape, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- The sparse form of a dense row, starting at column `k`. -/
@[expose] def toSparseFrom : ℕ → List α → List (ℕ × α)
  | _, [] => []
  | k, x :: r => (k, x) :: toSparseFrom (k + 1) r

theorem sparseGet_toSparseFrom [AddMonoid α] (k : ℕ) (r : List α) (j : ℕ) :
    sparseGet (toSparseFrom k r) j = if k ≤ j then r.getD (j - k) 0 else 0 := by
  induction r generalizing k with
  | nil => simp [toSparseFrom]
  | cons x r ih =>
    rw [toSparseFrom, sparseGet_cons, ih]
    rcases lt_trichotomy k j with h | rfl | h
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h
      simp [show k ≠ k + m + 1 by omega, show k + m + 1 - k = m + 1 by omega,
        show k + m + 1 - (k + 1) = m by omega]
      omega
    · simp
    · simp [h.ne', Nat.not_le.2 h, Nat.not_le.2 (Nat.lt_succ_of_lt h)]

/-- The sparse form of dense rows reads as the same matrix as `ofLists`. -/
theorem ofSparse_toSparse [AddMonoid α] (m n : ℕ) (rows : List (List α)) :
    ofSparse m n (rows.map (toSparseFrom 0)) = ofLists m n rows := by
  ext i j
  have hrow : (rows.map (toSparseFrom 0)).getD i [] = toSparseFrom 0 (rows.getD i []) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases rows[(i : ℕ)]? <;> rfl
  rw [ofSparse_apply, hrow, sparseGet_toSparseFrom]
  simp [ofLists_apply, ofList_apply]

/-! #### Zipper access to rows -/

/-- Row `k` of a list of rows whose rows `0, …, i - 1` are `past`, reversed, and whose rows from
`i` on are `future`. It costs `|i - k|` steps. -/
@[expose] def zget (past future : List (List (ℕ × α))) (i k : ℕ) : List (ℕ × α) :=
  bif Nat.blt k i then past.getD (i - 1 - k) [] else future.getD (k - i) []

theorem zget_eq (past future : List (List (ℕ × α))) (i k : ℕ) :
    zget past future i k = if k < i then past.getD (i - 1 - k) [] else future.getD (k - i) [] := by
  simp only [zget, cond_eq_ite, Nat.blt_eq]

theorem zget_nil (rows : List (List (ℕ × α))) (k : ℕ) : zget [] rows 0 k = rows.getD k [] := by
  simp [zget_eq]

/-- Moving the zipper one row forward. -/
theorem zget_step {past future rows : List (List (ℕ × α))} {i : ℕ}
    (h : ∀ k, zget past future i k = rows.getD k []) (k : ℕ) :
    zget (future.headD [] :: past) future.tail (i + 1) k = rows.getD k [] := by
  rw [← h k, zget_eq, zget_eq]
  rcases lt_trichotomy k i with hk | rfl | hk
  · rw [ite_eq_left (by omega), ite_eq_left hk, show i + 1 - 1 - k = (i - 1 - k) + 1 by omega,
      List.getD_cons_succ]
  · rw [ite_eq_left (by omega), ite_eq_right (lt_irrefl _), Nat.sub_self,
      show k + 1 - 1 - k = 0 by omega, List.getD_cons_zero]
    cases future <;> rfl
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hk
    rw [show i + m + 1 - (i + 1) = m by omega, show i + m + 1 - i = m + 1 by omega]
    cases future <;> simp

/-! #### Products -/

/-- A sparse row scaled by `c`. -/
@[expose] def sparseScale [Mul α] (c : α) (r : List (ℕ × α)) : List (ℕ × α) :=
  r.map fun e => (e.1, c * e.2)

theorem sparseGet_sparseScale [NonUnitalNonAssocSemiring α] (c : α) (r : List (ℕ × α))
    (j : ℕ) : sparseGet (sparseScale c r) j = c * sparseGet r j := by
  induction r with
  | nil => simp [sparseScale]
  | cons e r ih =>
    simp only [sparseScale, List.map_cons, sparseGet_cons] at ih ⊢
    split_ifs <;> simp [ih, mul_add]

/-- The rows of `B * C`, with the rows of `C` reached through a zipper at row `i` of `B`. -/
@[expose] def mulGo [Mul α] : ℕ → List (List (ℕ × α)) → List (List (ℕ × α)) →
    List (List (ℕ × α)) → List (List (ℕ × α))
  | _, _, _, [] => []
  | i, past, future, r :: rs =>
    r.flatMap (fun e => sparseScale e.2 (zget past future i e.1)) ::
      mulGo (i + 1) (future.headD [] :: past) future.tail rs

/-- The sparse product `B * C`: row `i` lists `B i k • (row k of C)` for the entries `(k, B i k)`
of row `i` of `B`, without merging repeated columns. -/
@[expose] def sparseMul [Mul α] (B C : List (List (ℕ × α))) : List (List (ℕ × α)) :=
  mulGo 0 [] C B

private theorem getD_mulGo [Mul α] (C : List (List (ℕ × α))) :
    ∀ (rs : List (List (ℕ × α))) (i : ℕ) (past future : List (List (ℕ × α))),
      (∀ k, zget past future i k = C.getD k []) → ∀ p,
        (mulGo i past future rs).getD p [] =
          (rs.getD p []).flatMap fun e => sparseScale e.2 (C.getD e.1 [])
  | [], _, _, _, _, p => by simp [mulGo]
  | r :: rs, i, past, future, h, p => by
    cases p with
    | zero =>
      simp only [mulGo, List.getD_cons_zero, h]
    | succ p =>
      simp only [mulGo, List.getD_cons_succ]
      exact getD_mulGo C rs (i + 1) _ _ (zget_step h) p

theorem length_sparseMul [Mul α] (B C : List (List (ℕ × α))) :
    (sparseMul B C).length = B.length := by
  suffices ∀ i past future, (mulGo i past future B).length = B.length from this _ _ _
  induction B with
  | nil => simp [mulGo]
  | cons r rs ih => intro i past future; simp [mulGo, ih]

private theorem sum_map_eq_sum_fin [NonUnitalNonAssocSemiring α] {m : ℕ} (r : List (ℕ × α))
    (g : ℕ → α) (hg : ∀ k, m ≤ k → g k = 0) :
    (r.map fun e => e.2 * g e.1).sum = ∑ k : Fin m, sparseGet r k * g k := by
  induction r with
  | nil => simp
  | cons e r ih =>
    simp only [List.map_cons, List.sum_cons, ih, sparseGet_cons]
    have : ∑ k : Fin m, (if e.1 = (k : ℕ) then e.2 + sparseGet r k else sparseGet r k) * g k =
        ∑ k : Fin m, ((if e.1 = (k : ℕ) then e.2 * g k else 0) + sparseGet r k * g k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp [add_mul]
    rw [this, Finset.sum_add_distrib]
    congr 1
    rcases Nat.lt_or_ge e.1 m with he | he
    · rw [Finset.sum_eq_single ⟨e.1, he⟩ (fun k _ hk => ite_eq_right fun h => hk (Fin.ext h.symm))
        (by simp)]
      simp
    · rw [hg _ he, mul_zero]
      exact (Finset.sum_eq_zero fun k _ => ite_eq_right fun h => by have := k.is_lt; omega).symm

/-- `sparseMul` computes the matrix product when `C` has at most `m` rows. -/
theorem ofSparse_sparseMul [NonUnitalNonAssocSemiring α] {l m n : ℕ}
    (B C : List (List (ℕ × α))) (hC : C.length ≤ m) :
    ofSparse l n (sparseMul B C) = ofSparse l m B * ofSparse m n C := by
  ext i j
  rw [ofSparse_apply, sparseMul, getD_mulGo C B 0 [] C (zget_nil C) i, Matrix.mul_apply]
  simp only [ofSparse_apply]
  have hflat : ∀ r : List (ℕ × α), sparseGet (r.flatMap fun e => sparseScale e.2 (C.getD e.1 []))
      j = (r.map fun e => e.2 * sparseGet (C.getD e.1 []) j).sum := by
    intro r
    induction r with
    | nil => simp
    | cons e r ih =>
      simp only [List.flatMap_cons, sparseGet_append, sparseGet_sparseScale, List.map_cons,
        List.sum_cons, ih]
  rw [hflat, sum_map_eq_sum_fin (m := m) _ (fun k => sparseGet (C.getD k []) j)]
  intro k hk
  rw [List.getD_eq_default _ _ (by omega), sparseGet_nil]

/-! #### Transposes -/

/-- Whether every stored entry `(k, x)` of row `i + p` of `rs` agrees with row `k` of the matrix
behind the zipper at column `i + p`. -/
@[expose] def transGo [Add α] [Zero α] [BEq α] : ℕ → List (List (ℕ × α)) →
    List (List (ℕ × α)) → List (List (ℕ × α)) → Bool
  | _, _, _, [] => true
  | i, past, future, r :: rs =>
    r.all (fun e => sparseGet (zget past future i e.1) i == sparseGet r e.1) &&
      transGo (i + 1) (future.headD [] :: past) future.tail rs

/-- Whether `B` is the transpose of `A`: every stored entry of either agrees with the other. -/
@[expose] def isTransposeOf [Add α] [Zero α] [BEq α] (A B : List (List (ℕ × α))) : Bool :=
  transGo 0 [] B A && transGo 0 [] A B

private theorem transGo_spec [Add α] [Zero α] [BEq α] [LawfulBEq α] (B : List (List (ℕ × α))) :
    ∀ (rs : List (List (ℕ × α))) (i : ℕ) (past future : List (List (ℕ × α))),
      (∀ k, zget past future i k = B.getD k []) → transGo i past future rs = true →
        ∀ p, ∀ e ∈ rs.getD p [], sparseGet (B.getD e.1 []) (i + p) = sparseGet (rs.getD p []) e.1
  | [], _, _, _, _, _, p => by simp
  | r :: rs, i, past, future, h, ht, p => by
    simp only [transGo, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at ht
    cases p with
    | zero =>
      intro e he
      have := ht.1 e (by simpa using he)
      rw [h] at this
      simpa using this
    | succ p =>
      intro e he
      have := transGo_spec B rs (i + 1) _ _ (zget_step h) ht.2 p e (by simpa using he)
      simpa [show i + (p + 1) = i + 1 + p by omega] using this

/-- An accepted transpose check relates every entry of `A` to the transposed entry of `B`. -/
theorem sparseGet_eq_of_isTransposeOf [AddMonoid α] [BEq α] [LawfulBEq α]
    {A B : List (List (ℕ × α))} (h : isTransposeOf A B = true) (i j : ℕ) :
    sparseGet (A.getD i []) j = sparseGet (B.getD j []) i := by
  simp only [isTransposeOf, Bool.and_eq_true] at h
  have h₁ := transGo_spec B A 0 [] B (zget_nil B) h.1
  have h₂ := transGo_spec A B 0 [] A (zget_nil A) h.2
  by_cases hA : ∃ e ∈ A.getD i [], e.1 = j
  · obtain ⟨e, he, rfl⟩ := hA
    simpa using (h₁ i e he).symm
  by_cases hB : ∃ e ∈ B.getD j [], e.1 = i
  · obtain ⟨e, he, rfl⟩ := hB
    simpa using h₂ j e he
  push Not at hA hB
  rw [sparseGet_eq_zero fun e he h => absurd h (hA e he),
    sparseGet_eq_zero fun e he h => absurd h (hB e he)]

/-- An accepted transpose check gives the transposed matrix. -/
theorem ofSparse_eq_transpose_of_isTransposeOf [AddMonoid α] [BEq α] [LawfulBEq α] {m n : ℕ}
    {A B : List (List (ℕ × α))} (h : isTransposeOf A B = true) :
    ofSparse n m B = (ofSparse m n A)ᵀ := by
  ext i j
  rw [transpose_apply, ofSparse_apply, ofSparse_apply, sparseGet_eq_of_isTransposeOf h]

/-! #### Normalization -/

/-- Insert an entry into a row sorted by column, adding it to an entry of the same column. -/
@[expose] def insertAdd [Add α] (e : ℕ × α) : List (ℕ × α) → List (ℕ × α)
  | [] => [e]
  | x :: r =>
    bif Nat.blt e.1 x.1 then e :: x :: r
    else bif Nat.beq e.1 x.1 then (x.1, e.2 + x.2) :: r
    else x :: insertAdd e r

theorem insertAdd_cons [Add α] (e x : ℕ × α) (r : List (ℕ × α)) :
    insertAdd e (x :: r) = if e.1 < x.1 then e :: x :: r
      else if e.1 = x.1 then (x.1, e.2 + x.2) :: r else x :: insertAdd e r := by
  simp only [insertAdd, cond_eq_ite, Nat.blt_eq, Nat.beq_eq]

/-- A row with its entries sorted by column and repeated columns merged. -/
@[expose] def sparseNormalize [Add α] (r : List (ℕ × α)) : List (ℕ × α) :=
  r.foldr insertAdd []

private theorem sparseGet_insertAdd [AddCommMonoid α] (e : ℕ × α) (r : List (ℕ × α)) (j : ℕ) :
    sparseGet (insertAdd e r) j = sparseGet [e] j + sparseGet r j := by
  induction r with
  | nil => simp [insertAdd]
  | cons x r ih =>
    rw [insertAdd_cons]
    split_ifs with h₁ h₂
    · simp only [sparseGet_cons, sparseGet_nil, add_zero]
      split_ifs <;> simp
    · simp only [sparseGet_cons, sparseGet_nil, add_zero, h₂]
      split_ifs <;> simp [add_assoc]
    · simp only [sparseGet_cons, ih, sparseGet_nil, add_zero]
      split_ifs <;> simp [add_left_comm]

theorem sparseGet_sparseNormalize [AddCommMonoid α] (r : List (ℕ × α)) (j : ℕ) :
    sparseGet (sparseNormalize r) j = sparseGet r j := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    rw [sparseNormalize, List.foldr_cons, ← sparseNormalize, sparseGet_insertAdd, ih,
      sparseGet_cons, sparseGet_cons]
    split_ifs <;> simp

end Sparse

/-! ### Integer scaling of sparse rows -/

/-- The integer row `s * q` for the stored values `q` of `r`, exact when every `q.den` divides
`s`. -/
@[expose] def scaleSparse (s : ℕ) (r : List (ℕ × ℚ)) : List (ℕ × ℤ) :=
  r.map fun e => (e.1, e.2.num * ((s / e.2.den : ℕ) : ℤ))

/-- The lcm of the denominators of all values stored in `rows`. -/
@[expose] def sparseDenLcm (rows : List (List (ℕ × ℚ))) : ℕ :=
  denLcm (rows.flatten.map (·.2))

private theorem cast_sparseGet_scaleSparse {s : ℕ} {r : List (ℕ × ℚ)}
    (hs : ∀ e ∈ r, e.2.den ∣ s) (j : ℕ) :
    ((sparseGet (scaleSparse s r) j : ℤ) : ℚ) = s * sparseGet r j := by
  induction r with
  | nil => simp [scaleSparse]
  | cons e r ih =>
    have ih' := ih fun x hx => hs x (List.mem_cons_of_mem _ hx)
    simp only [scaleSparse, List.map_cons, sparseGet_cons] at ih' ⊢
    split_ifs
    · rw [Int.cast_add, ih', mul_add, Rat.clearDenom_entry (hs e List.mem_cons_self)]
    · exact ih'

/-- Scaling every row by a common multiple `s` of the denominators scales the matrix. -/
theorem map_ofSparse_scaleSparse {m n s : ℕ} {rows : List (List (ℕ × ℚ))}
    (hs : ∀ e ∈ rows.flatten, e.2.den ∣ s) :
    (ofSparse m n (rows.map (scaleSparse s))).map ((↑) : ℤ → ℚ) = (s : ℚ) • ofSparse m n rows := by
  ext i j
  have hrow : (rows.map (scaleSparse s)).getD i [] = scaleSparse s (rows.getD i []) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases rows[(i : ℕ)]? <;> rfl
  have hs' : ∀ e ∈ rows.getD i [], e.2.den ∣ s := by
    intro e he
    rcases Nat.lt_or_ge i rows.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi] at he
      exact hs e (List.mem_flatten.2 ⟨_, List.getElem_mem hi, he⟩)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi] at he
  simp only [map_apply, Matrix.smul_apply, smul_eq_mul, ofSparse_apply]
  rw [hrow, cast_sparseGet_scaleSparse hs']

theorem den_dvd_sparseDenLcm {rows : List (List (ℕ × ℚ))} :
    ∀ e ∈ rows.flatten, e.2.den ∣ sparseDenLcm rows :=
  fun _ he => den_dvd_denLcm (List.mem_map_of_mem he)

/-! ### Envelope `LDLᵀ` certificates -/

/-- A row given by its first column `f` and its entries from `f` on, as a dense row. -/
@[expose] def envRow {α : Type*} [Zero α] (fr : ℕ × List α) : List α :=
  List.replicate fr.1 0 ++ fr.2

theorem getD_envRow {α : Type*} [Zero α] (f : ℕ) (r : List α) (k : ℕ) :
    (envRow (f, r)).getD k 0 = if f ≤ k then r.getD (k - f) 0 else 0 := by
  induction f generalizing k with
  | zero => simp [envRow]
  | succ f ih =>
    cases k with
    | zero => simp [envRow]
    | succ k =>
      have := ih k
      simp only [envRow, List.replicate_succ, List.cons_append, List.getD_cons_succ] at this ⊢
      rw [this]
      simp [Nat.add_sub_add_right]

/-- The dot product of two rows given by their first columns, over the overlap. -/
@[expose] def alignDot (f : ℕ) (u : List ℤ) (g : ℕ) (a : List ℤ) : ℤ :=
  if f ≤ g then rowDot (u.drop (g - f)) a else rowDot u (a.drop (f - g))

private theorem rowDot_comm (u a : List ℤ) : rowDot u a = rowDot a u := by
  induction u generalizing a with
  | nil => cases a <;> rfl
  | cons x u ih => cases a with
    | nil => rfl
    | cons y a => simp only [rowDot, ih, mul_comm]

private theorem rowDot_replicate_append (m : ℕ) (u a : List ℤ) :
    rowDot u (List.replicate m 0 ++ a) = rowDot (u.drop m) a := by
  induction m generalizing u with
  | zero => simp
  | succ m ih => cases u with
    | nil => simp [rowDot]
    | cons x u => simp [List.replicate_succ, rowDot, ih]

private theorem rowDot_replicate_append_both (f : ℕ) (u a : List ℤ) :
    rowDot (List.replicate f 0 ++ u) (List.replicate f 0 ++ a) = rowDot u a := by
  induction f with
  | zero => simp
  | succ f ih => simp [List.replicate_succ, rowDot, ih]

theorem alignDot_eq (f : ℕ) (u : List ℤ) (g : ℕ) (a : List ℤ) :
    alignDot f u g a = rowDot (envRow (f, u)) (envRow (g, a)) := by
  unfold alignDot envRow
  dsimp only
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [List.replicate_add, List.append_assoc, rowDot_replicate_append_both,
      rowDot_replicate_append, Nat.add_sub_cancel_left]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le h)
    rw [List.replicate_add, List.append_assoc, rowDot_replicate_append_both,
      rowDot_comm (List.replicate m 0 ++ u), rowDot_replicate_append, Nat.add_sub_cancel_left,
      rowDot_comm]

/-! ### Differences and diagonal dominance of sparse rows -/

section Dominance

variable {α : Type*}

/-- A sparse row with `f` applied to every stored value. -/
@[expose] def sparseMap {β : Type*} (f : α → β) (r : List (ℕ × α)) : List (ℕ × β) :=
  r.map fun e => (e.1, f e.2)

theorem sparseGet_sparseMap {β : Type*} [AddMonoid α] [AddMonoid β] {f : α → β} (hf0 : f 0 = 0)
    (hf : ∀ a b, f (a + b) = f a + f b) (r : List (ℕ × α)) (j : ℕ) :
    sparseGet (sparseMap f r) j = f (sparseGet r j) := by
  induction r with
  | nil => simp [sparseMap, hf0]
  | cons e r ih =>
    simp only [sparseMap, List.map_cons, sparseGet_cons] at ih ⊢
    split_ifs <;> simp [ih, hf]

/-- `rows - rem`, row by row, with repeated columns merged. A row of `rows` with no row of
`rem` is kept. -/
@[expose] def subRows : List (List (ℕ × ℚ)) → List (List (ℕ × ℚ)) → List (List (ℕ × ℚ))
  | r :: rs, s :: ss => sparseNormalize (r ++ sparseMap (fun x => -x) s) :: subRows rs ss
  | rs, [] => rs
  | [], _ :: _ => []

theorem sparseGet_subRows :
    ∀ (rows rem : List (List (ℕ × ℚ))) (i j : ℕ), i < rows.length →
      sparseGet ((subRows rows rem).getD i []) j =
        sparseGet (rows.getD i []) j - sparseGet (rem.getD i []) j
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | r :: rs, [], i, j, _ => by simp [subRows]
  | r :: rs, s :: ss, 0, j, _ => by
    simp only [subRows, List.getD_cons_zero, sparseGet_sparseNormalize, sparseGet_append,
      sparseGet_sparseMap neg_zero (fun a b => neg_add a b)]
    ring
  | r :: rs, s :: ss, i + 1, j, h => by
    simp only [subRows, List.getD_cons_succ]
    exact sparseGet_subRows rs ss i j (by simpa using h)

theorem length_subRows :
    ∀ (rows rem : List (List (ℕ × ℚ))), (subRows rows rem).length = rows.length
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: rs, _ :: ss => by simp [subRows, length_subRows rs ss]

/-- The sum of `|x|` over the stored entries `(k, x)` of a row with `k ≠ i`. -/
@[expose] def offAbs (i : ℕ) : List (ℕ × ℚ) → ℚ
  | [] => 0
  | e :: r => (bif Nat.beq e.1 i then 0 else |e.2|) + offAbs i r

theorem offAbs_cons (i : ℕ) (e : ℕ × ℚ) (r : List (ℕ × ℚ)) :
    offAbs i (e :: r) = (if e.1 = i then 0 else |e.2|) + offAbs i r := by
  simp only [offAbs, cond_eq_ite, Nat.beq_eq]

/-- Whether row `i + k` of `rows` is diagonally dominant by its stored entries, for every
`k`: `offAbs` is at most the diagonal entry. -/
@[expose] def ddGo : ℕ → List (List (ℕ × ℚ)) → Bool
  | _, [] => true
  | i, r :: rs => decide (offAbs i r ≤ sparseGet r i) && ddGo (i + 1) rs

private theorem sum_ite_le_abs {m : ℕ} (k i : ℕ) (x : ℚ) :
    ∑ j : Fin m, (if i = (j : ℕ) then 0 else if k = (j : ℕ) then |x| else 0) ≤
      if k = i then 0 else |x| := by
  split_ifs with hki
  · exact (Finset.sum_eq_zero fun j _ => by split_ifs <;> first | rfl | omega).le
  · calc ∑ j : Fin m, (if i = (j : ℕ) then 0 else if k = (j : ℕ) then |x| else 0)
        ≤ ∑ j : Fin m, (if k = (j : ℕ) then |x| else 0) :=
          Finset.sum_le_sum fun j _ => by split_ifs <;> simp [abs_nonneg]
      _ ≤ |x| := by
        rcases Nat.lt_or_ge k m with hk | hk
        · rw [Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj => ite_eq_right
            fun h => hj (Fin.ext h.symm)) (by simp)]
          simp
        · rw [Finset.sum_eq_zero fun j _ => ite_eq_right fun h => by
            have := j.is_lt; omega]
          exact abs_nonneg _

/-- The off-diagonal absolute values of a sparse row, read over `Fin m`, are bounded by
`offAbs`. -/
theorem sum_abs_le_offAbs {m : ℕ} (r : List (ℕ × ℚ)) (i : ℕ) :
    ∑ j : Fin m, (if i = (j : ℕ) then 0 else |sparseGet r j|) ≤ offAbs i r := by
  induction r with
  | nil => simp [offAbs]
  | cons e r ih =>
    calc ∑ j : Fin m, (if i = (j : ℕ) then 0 else |sparseGet (e :: r) j|)
        ≤ ∑ j : Fin m, ((if i = (j : ℕ) then 0 else if e.1 = (j : ℕ) then |e.2| else 0) +
            (if i = (j : ℕ) then 0 else |sparseGet r j|)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [sparseGet_cons]
          split_ifs <;> simp [abs_add_le]
      _ ≤ offAbs i (e :: r) := by
        rw [Finset.sum_add_distrib, offAbs_cons]
        exact add_le_add (sum_ite_le_abs e.1 i e.2) ih

private theorem ddGo_spec :
    ∀ (rows : List (List (ℕ × ℚ))) (i : ℕ), ddGo i rows = true → ∀ p < rows.length,
      offAbs (i + p) rows[p]! ≤ sparseGet rows[p]! (i + p)
  | [], _, _, p, hp => absurd hp (Nat.not_lt_zero _)
  | r :: rs, i, h, p, hp => by
    simp only [ddGo, Bool.and_eq_true, decide_eq_true_eq] at h
    cases p with
    | zero => simpa using h.1
    | succ p =>
      have := ddGo_spec rs (i + 1) h.2 p (by simpa using hp)
      simpa [show i + (p + 1) = i + 1 + p by omega] using this

/-- Accepted rows are diagonally dominant: `∑_{j ≠ i} |R i j| ≤ R i i`. -/
theorem diagDominant_of_ddGo {n : ℕ} {rows : List (List (ℕ × ℚ))} (h : ddGo 0 rows = true)
    (i : Fin n) :
    ∑ j, (if i = j then 0 else |ofSparse n n rows i j|) ≤ ofSparse n n rows i i := by
  simp only [ofSparse_apply, ← Fin.val_inj]
  rcases Nat.lt_or_ge i rows.length with hi | hi
  · have := ddGo_spec rows 0 h i hi
    rw [zero_add, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at this
    rw [List.getD_eq_getElem _ _ hi]
    exact (sum_abs_le_offAbs _ _).trans this
  · simp [List.getElem?_eq_none hi]

end Dominance

/-- **Diagonal dominance.** A symmetric real matrix with `∑_{j ≠ i} |R i j| ≤ R i i` for every
`i` is positive semidefinite. -/
theorem posSemidef_of_diagDominant {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ} (hR : Rᵀ = R)
    (h : ∀ i, ∑ j, (if i = j then 0 else |R i j|) ≤ R i i) : R.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hR], fun x => ?_⟩
  simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum]
  set c : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else |R i j| with hc
  have hsymm : ∀ i j, R j i = R i j := fun i j => by
    rw [← transpose_apply R i j, hR]
  have hcs : ∀ i j, c j i = c i j := fun i j => by
    simp only [hc, hsymm, eq_comm]
  -- each off-diagonal pair is bounded below
  have hT : ∀ i j, 0 ≤ 2 * (x i * (R i j * x j)) + c i j * x i ^ 2 + c i j * x j ^ 2 -
      (if i = j then 2 * (x i * (R i j * x j)) else 0) := by
    intro i j
    simp only [hc]
    split_ifs with hij
    · simp
    · rcases abs_cases (R i j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
      · nlinarith [mul_nonneg h2 (sq_nonneg (x i + x j))]
      · nlinarith [mul_nonneg (neg_nonneg.2 h2.le) (sq_nonneg (x i - x j))]
  have hsum := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hT i j
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at hsum
  have hswap : ∑ i, ∑ j, c i j * x j ^ 2 = ∑ i, ∑ j, c i j * x i ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hcs]
  have hdiag : ∑ i, ∑ j, c i j * x i ^ 2 ≤ ∑ i, x i * (R i i * x i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul]
    nlinarith [mul_le_mul_of_nonneg_right (h i) (sq_nonneg (x i))]
  have h2 : ∑ i, ∑ j, 2 * (x i * (R i j * x j)) = 2 * ∑ i, ∑ j, x i * (R i j * x j) := by
    simp only [Finset.mul_sum]
  have h3 : ∑ i, 2 * (x i * (R i i * x i)) = 2 * ∑ i, x i * (R i i * x i) := by
    simp only [Finset.mul_sum]
  rw [hswap] at hsum
  linarith [hsum, hdiag, h2, h3]

/-! ### Envelope `LDLᵀ` certificates -/

/-- An `LDLᵀ` witness for an `n × n` rational matrix `M`, by envelope, with a remainder: row `i`
of `lower` is the first column `fᵢ` of row `i` of `L` and its entries `L i fᵢ, …, L i i`,
ending in `1`, and `rem` lists the sparse rows of a symmetric, diagonally dominant `R` with
`M = L * diagonal d * Lᵀ + R`. An exact factorization has `rem = []`. -/
structure EnvLDLCert where
  /-- Row `i` is `(fᵢ, [L i fᵢ, …, L i i])`. -/
  lower : List (ℕ × List ℚ)
  /-- The diagonal `d 0, …, d (n - 1)`. -/
  diag : List ℚ
  /-- The sparse rows of the remainder `R`. -/
  rem : List (List (ℕ × ℚ))

namespace EnvLDLCert

variable (c : EnvLDLCert) {n : ℕ}

/-- The factors as a dense certificate: the rows of `L` padded with zeros on the left. -/
@[expose] def toLDLCert : LDLCert := ⟨c.lower.map envRow, c.diag⟩

/-- Whether row `k` of `rows` reaches column `i + k` and ends in `1`, for every `k`. -/
@[expose] def envShape : ℕ → List (ℕ × List ℚ) → Bool
  | _, [] => true
  | i, fr :: rows => fr.1 + fr.2.length == i + 1 && fr.2.getLast? == some 1 && envShape (i + 1) rows

theorem unitLowerFrom_of_envShape :
    ∀ {i : ℕ} {rows : List (ℕ × List ℚ)}, envShape i rows = true →
      LDLCert.unitLowerFrom i (rows.map envRow) = true
  | _, [], _ => rfl
  | i, fr :: rows, h => by
    simp only [envShape, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hlen, hlast⟩, hrest⟩ := h
    have hne : fr.2 ≠ [] := by rintro h; simp [h] at hlast
    simp only [List.map_cons, LDLCert.unitLowerFrom, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨by simp [envRow, hlen], ?_⟩, unitLowerFrom_of_envShape hrest⟩
    rw [envRow, List.getLast?_append_of_ne_nil _ hne, hlast]

private theorem envShape_spec :
    ∀ {i : ℕ} {rows : List (ℕ × List ℚ)}, envShape i rows = true → ∀ p (hp : p < rows.length),
      rows[p].1 + rows[p].2.length = i + p + 1 ∧ rows[p].2 ≠ []
  | _, [], _, p, hp => absurd hp (Nat.not_lt_zero _)
  | i, fr :: rows, h, p, hp => by
    simp only [envShape, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hlen, hlast⟩, hrest⟩ := h
    cases p with
    | zero =>
      have hne : fr.2 ≠ [] := by rintro h; rw [h] at hlast; simp at hlast
      exact ⟨by simpa using hlen, by simpa using hne⟩
    | succ p =>
      obtain ⟨h₁, h₂⟩ := envShape_spec hrest p (by simpa using hp)
      exact ⟨by simp only [List.getElem_cons_succ, h₁]; omega, by simpa using h₂⟩

/-- What is kept of a row above the current one: its first column, its entries of `L` scaled
to integers, their scale, and `d`. -/
abbrev RowData := ℕ × List ℤ × ℕ × ℚ

/-- The data kept of row `(f, r)` with pivot `di`. -/
@[expose] def rowData (fr : ℕ × List ℚ) (di : ℚ) : RowData :=
  (fr.1, scaleRow (denLcm fr.2) fr.2, denLcm fr.2, di)

/-- The check of row `i`, with data `rd`, entries `r` of `L` and stored row `mrow` of `M`, given
the data `prev` of the rows above, nearest first. The window `win` is the data of the rows
`fᵢ, …, i - 1`, `u` is row `i` of `L * diagonal d` on the envelope, scaled to integers `b` by
its lcm `t`; entry `(i, fᵢ + p)` is checked against the row `fᵢ + p` of the window. -/
@[expose] def rowCheck (prev : List RowData) (rd : RowData) (r : List ℚ)
    (mrow : List (ℕ × ℚ)) : Bool :=
  let win := (prev.take (r.length - 1)).reverse ++ [rd]
  let u := List.zipWith (· * ·) r (win.map (·.2.2.2))
  let t := denLcm u
  let b := scaleRow t u
  mrow.all (fun e => Nat.ble rd.1 e.1 || e.2 == 0) &&
    (((List.range' rd.1 r.length).map (sparseGet mrow)).zip win).all fun x =>
      x.1.num * ((t * x.2.2.2.1 : ℕ) : ℤ) == alignDot rd.1 b x.2.1 x.2.2.1 * x.1.den

/-- The check of every row, keeping the data of the rows above. -/
@[expose] def checkGo : List RowData → List (ℕ × List ℚ) → List ℚ → List (List (ℕ × ℚ)) → Bool
  | prev, fr :: rows, di :: ds, m :: ms =>
    rowCheck prev (rowData fr di) fr.2 m && checkGo (rowData fr di :: prev) rows ds ms
  | _, [], [], [] => true
  | _, _, _, _ => false

/-- Whether `c` factors, exactly and on and below the diagonal, the `n × n` matrix with sparse
rows `rows`: `c.lower` and `c.diag` have `n` entries, row `i` of `L` reaches the diagonal and
ends in `1`, `rows` has `n` rows and stores only zeros left of the envelope, and the envelope
entries agree with `L * diagonal d * Lᵀ`. Neither symmetry nor `c.rem` is used here. -/
@[expose] def factorsLower (n : ℕ) (rows : List (List (ℕ × ℚ))) : Bool :=
  c.lower.length == n && c.diag.length == n && envShape 0 c.lower && checkGo [] c.lower c.diag rows

/-- Whether `M = L * diagonal d * Lᵀ + R` for the symmetric `n × n` matrix `M` with sparse rows
`rows`: `R` (`c.rem`) is symmetric and diagonally dominant, and `c` factors `M - R` exactly.
The symmetry of `M` is not checked here. -/
@[expose] def factorsWith (n : ℕ) (rows : List (List (ℕ × ℚ))) : Bool :=
  isTransposeOf c.rem c.rem && ddGo 0 c.rem && c.factorsLower n (subRows rows c.rem)

/-- Whether `c` is a certificate for the `n × n` matrix with sparse rows `rows`: they have the
shape of an `n × n` matrix and are symmetric, and `factorsWith` accepts. -/
@[expose] def factors (n : ℕ) (rows : List (List (ℕ × ℚ))) : Bool :=
  isSparseShape n n rows && isTransposeOf rows rows && c.factorsWith n rows

/-- Whether `c` certifies `ofSparse n n rows ≻ 0`: it factors the matrix and every `d i` is
positive. -/
@[expose] def checkPosDef (n : ℕ) (rows : List (List (ℕ × ℚ))) : Bool :=
  c.factors n rows && c.diag.all (0 < ·)

/-- Whether `c` certifies `ofSparse n n rows ⪰ 0`: it factors the matrix and every `d i` is
nonnegative. -/
@[expose] def checkPosSemidef (n : ℕ) (rows : List (List (ℕ × ℚ))) : Bool :=
  c.factors n rows && c.diag.all (0 ≤ ·)

/-! #### Soundness of the envelope check -/

private theorem checkGo_spec :
    ∀ (prev : List RowData) (rows : List (ℕ × List ℚ)) (ds : List ℚ)
      (ms : List (List (ℕ × ℚ))), checkGo prev rows ds ms = true →
        ds.length = rows.length ∧ ms.length = rows.length ∧
          ∀ p (hp : p < rows.length) (hd : p < ds.length) (hm : p < ms.length),
            rowCheck (((List.zipWith rowData rows ds).take p).reverse ++ prev)
              (rowData rows[p] ds[p]) rows[p].2 ms[p] = true
  | prev, [], [], [], _ => ⟨rfl, rfl, fun p hp => absurd hp (Nat.not_lt_zero _)⟩
  | prev, fr :: rows, di :: ds, m :: ms, h => by
    simp only [checkGo, Bool.and_eq_true] at h
    obtain ⟨hd, hm, hrest⟩ := checkGo_spec _ rows ds ms h.2
    refine ⟨by simp [hd], by simp [hm], fun p hp hdp hmp => ?_⟩
    cases p with
    | zero => simpa using h.1
    | succ p =>
      have := hrest p (by simpa using hp) (by simpa using hdp) (by simpa using hmp)
      simpa [List.take_succ_cons, List.zipWith_cons_cons] using this
  | _, [], [], _ :: _, h => by simp [checkGo] at h
  | _, [], _ :: _, _, h => by simp [checkGo] at h
  | _, _ :: _, [], _, h => by simp [checkGo] at h
  | _, _ :: _, _ :: _, [], h => by simp [checkGo] at h

/-- The window of row `i`: the data of the rows `f, …, i`. -/
private theorem window_eq {D : List RowData} {i f : ℕ} (hi : i < D.length) (hf : f ≤ i) :
    ((D.take i).reverse.take (i - f)).reverse ++ [D[i]] = (D.take (i + 1)).drop f := by
  rw [List.take_reverse, List.reverse_reverse, List.length_take_of_le hi.le,
    show i - (i - f) = f by omega, List.take_add_one, List.getElem?_eq_getElem hi,
    Option.toList_some, List.drop_append_of_le_length (by simp; omega)]

private theorem getD_zipWith_mul' (a b : List ℚ) (k : ℕ) :
    (List.zipWith (· * ·) a b).getD k 0 = a.getD k 0 * b.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  cases a[k]? <;> cases b[k]? <;> simp

private theorem L_apply' (i k : Fin n) :
    c.toLDLCert.L n i k = (envRow (c.lower.getD i (0, []))).getD k 0 := by
  have : (c.lower.map envRow).getD i [] = envRow (c.lower.getD i (0, [])) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases c.lower[(i : ℕ)]? <;> rfl
  simp only [toLDLCert, LDLCert.L, ofLists_apply, ofList_apply]
  rw [this]

private theorem length_envRow_scaleRow (f : ℕ) (s : ℕ) (u : List ℚ) :
    (envRow (f, scaleRow s u)).length = f + u.length := by
  simp [envRow, scaleRow]

/-- The integer dot product of an entry check, read over `ℚ`: the scaled rows of
`L * diagonal d` and `L` give `t * s` times the entry of `L * diagonal d * Lᵀ`. -/
private theorem cast_alignDot {f g : ℕ} {r r' dw : List ℚ} {dg : ℕ → ℚ}
    (hfr : f + r.length ≤ n)
    (hdw : ∀ q < r.length, dw.getD q 0 = dg (f + q)) :
    ((alignDot f (scaleRow (denLcm (List.zipWith (· * ·) r dw)) (List.zipWith (· * ·) r dw)) g
        (scaleRow (denLcm r') r') : ℤ) : ℚ) =
      ((denLcm (List.zipWith (· * ·) r dw) * denLcm r' : ℕ) : ℚ) *
        ∑ k : Fin n, (envRow (f, r)).getD k 0 * dg k * (envRow (g, r')).getD k 0 := by
  set u := List.zipWith (· * ·) r dw
  have hu : u.length ≤ r.length := by simp [u]
  rw [alignDot_eq, rowDot_eq_sum (n := n) _ (by rw [length_envRow_scaleRow]; omega),
    Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Int.cast_mul, getD_envRow, getD_envRow, getD_envRow, getD_envRow]
  split_ifs with h₁ h₂
  rotate_left
  · simp
  · simp
  · simp
  rw [cast_getD_scaleRow (fun _ hq => den_dvd_denLcm hq),
    cast_getD_scaleRow (fun _ hq => den_dvd_denLcm hq), getD_zipWith_mul']
  rcases Nat.lt_or_ge (k - f) r.length with hk | hk
  · rw [hdw _ hk, show f + (k - f) = k by omega]
    push_cast
    ring
  · rw [List.getD_eq_default _ _ hk]
    simp

/-- An accepted exact check factors every symmetric matrix that the rows give. -/
theorem eq_of_factorsLower {rows : List (List (ℕ × ℚ))}
    (hsymm : (ofSparse n n rows)ᵀ = ofSparse n n rows) (h : c.factorsLower n rows = true) :
    ofSparse n n rows = c.toLDLCert.L n * diagonal (c.toLDLCert.d n) * (c.toLDLCert.L n)ᵀ := by
  simp only [factorsLower, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hlen, hdlen⟩, hshape⟩, hgo⟩ := h
  obtain ⟨-, hmlen, hrow⟩ := checkGo_spec [] c.lower c.diag rows hgo
  set D := List.zipWith rowData c.lower c.diag with hD
  have hDlen : D.length = n := by simp [hD, hlen, hdlen]
  have hDget : ∀ k (hk : k < D.length),
      D[k] = rowData (c.lower.getD k (0, [])) (c.diag.getD k 0) := by
    intro k hk
    simp only [hD, List.getElem_zipWith]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  set M := c.toLDLCert.L n * diagonal (c.toLDLCert.d n) * (c.toLDLCert.L n)ᵀ with hM
  have hMapply : ∀ i j : Fin n, M i j =
      ∑ k : Fin n, (envRow (c.lower.getD i (0, []))).getD k 0 * c.diag.getD k 0 *
        (envRow (c.lower.getD j (0, []))).getD k 0 := by
    intro i j
    rw [hM, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_diagonal, transpose_apply, c.L_apply' i k, c.L_apply' j k]
    simp [toLDLCert, LDLCert.d, ofList_apply]
  have hshape' : ∀ k < n, (c.lower.getD k (0, [])).1 + (c.lower.getD k (0, [])).2.length =
      k + 1 ∧ (c.lower.getD k (0, [])).2 ≠ [] := by
    intro k hk
    rw [List.getD_eq_getElem _ _ (by omega)]
    simpa using envShape_spec hshape k (by omega)
  -- the entries on and below the diagonal
  have hlow : ∀ i j : Fin n, j ≤ i → ofSparse n n rows i j = M i j := by
    intro i j hji
    have hi : (i : ℕ) < c.lower.length := hlen ▸ i.is_lt
    obtain ⟨hfl, hne⟩ := hshape' i i.is_lt
    have hlpos := List.length_pos_of_ne_nil hne
    have hc := hrow i hi (by omega) (by omega)
    simp only [List.append_nil] at hc
    rw [← List.getD_eq_getElem _ (0, []) hi, ← List.getD_eq_getElem _ 0 (by omega : (i : ℕ) <
      c.diag.length), ← List.getD_eq_getElem _ [] (by omega : (i : ℕ) < rows.length),
      ← hDget i (by omega)] at hc
    set fr := c.lower.getD i (0, []) with hfr
    have hrd : (D[(i : ℕ)]'(by omega)).1 = fr.1 := by rw [hDget]; rfl
    simp only [rowCheck, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Nat.ble_eq,
      beq_iff_eq, hrd, show fr.2.length - 1 = i - fr.1 by omega,
      window_eq (by omega : (i : ℕ) < D.length) (by omega : fr.1 ≤ i)] at hc
    obtain ⟨hzero, hent⟩ := hc
    rcases Nat.lt_or_ge (j : ℕ) fr.1 with hjf | hjf
    · -- left of the envelope both sides vanish
      have hv : ofSparse n n rows i j = 0 := by
        rw [ofSparse_apply]
        refine sparseGet_eq_zero fun e he hej => ?_
        rcases hzero e he with h | h
        · omega
        · exact h
      rw [hv, hMapply]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      obtain ⟨hfj, -⟩ := hshape' j j.is_lt
      have hL : (envRow (c.lower.getD j (0, []))).getD k 0 = 0 ∨ (envRow fr).getD k 0 = 0 := by
        by_cases hk : fr.1 ≤ (k : ℕ)
        · left
          rw [getD_envRow]
          split_ifs
          · exact List.getD_eq_default _ _ (by omega)
          · rfl
        · right
          rw [getD_envRow]
          exact ite_eq_right hk
      rcases hL with h | h <;> rw [h] <;> ring
    · -- on the envelope, the entry check
      set W := (D.take (i + 1)).drop fr.1 with hW
      have hWlen : W.length = fr.2.length := by simp [hW, hDlen]; omega
      have hWget : ∀ q (hq : q < W.length), W[q] = rowData (c.lower.getD (fr.1 + q) (0, []))
          (c.diag.getD (fr.1 + q) 0) := by
        intro q hq
        simp only [hW, List.getElem_drop, List.getElem_take]
        exact hDget _ _
      set p := (j : ℕ) - fr.1 with hp
      have hpl : p < fr.2.length := by omega
      have hmem : (sparseGet (rows.getD i []) (fr.1 + p), W[p]'(by omega)) ∈
          ((List.range' fr.1 fr.2.length).map (sparseGet (rows.getD i []))).zip W := by
        rw [List.mem_iff_getElem]
        refine ⟨p, by simp; omega, ?_⟩
        simp [List.getElem_zip, List.getElem_map, List.getElem_range']
      have hx := hent _ hmem
      rw [hWget p (by omega)] at hx
      simp only [rowData] at hx
      rw [show fr.1 + p = (j : ℕ) by omega] at hx
      set v := sparseGet (rows.getD i []) j
      have hq := LDLCert.entry_eq_of_scaled v.den_pos (Rat.mul_den_eq_num v).symm hx
      obtain ⟨hfj, hnej⟩ := hshape' j j.is_lt
      rw [cast_alignDot (n := n) (dg := fun k => c.diag.getD k 0) (by omega)
        (fun q hq' => by
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, hWget q (by omega)]
          rfl)] at hq
      rw [ofSparse_apply, hMapply]
      have hS : ((denLcm (List.zipWith (· * ·) fr.2 (W.map (·.2.2.2))) *
          denLcm (c.lower.getD j (0, [])).2 : ℕ) : ℚ) ≠ 0 := by
        have := Nat.mul_pos (denLcm_pos (List.zipWith (· * ·) fr.2 (W.map (·.2.2.2))))
          (denLcm_pos (c.lower.getD j (0, [])).2)
        exact_mod_cast this.ne'
      apply mul_right_cancel₀ hS
      rw [hq, mul_comm]
  ext i j
  rcases le_total j i with hji | hij
  · exact hlow i j hji
  · have h₁ := congrFun (congrFun hsymm i) j
    have h₂ := congrFun (congrFun c.toLDLCert.transpose_LDLt i) j
    rw [transpose_apply] at h₁ h₂
    rw [← h₁, hlow j i hij, hM]
    exact h₂

/-- The shape facts recorded by an accepted `factorsWith`. -/
private theorem shape_of_factorsWith {rows : List (List (ℕ × ℚ))}
    (h : c.factorsWith n rows = true) :
    c.toLDLCert.lower.length = n ∧ c.toLDLCert.diag.length = n ∧
      LDLCert.unitLowerFrom 0 c.toLDLCert.lower = true := by
  simp only [factorsWith, factorsLower, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨by simpa [toLDLCert] using h.2.1.1.1, h.2.1.1.2, unitLowerFrom_of_envShape h.2.1.2⟩

/-- An accepted `factorsWith` writes the symmetric matrix as `L * diagonal d * Lᵀ + R`. -/
theorem eq_add_of_factorsWith {rows : List (List (ℕ × ℚ))} (hlen : rows.length = n)
    (hsymm : (ofSparse n n rows)ᵀ = ofSparse n n rows) (h : c.factorsWith n rows = true) :
    ofSparse n n rows =
      c.toLDLCert.L n * diagonal (c.toLDLCert.d n) * (c.toLDLCert.L n)ᵀ + ofSparse n n c.rem := by
  simp only [factorsWith, Bool.and_eq_true] at h
  obtain ⟨⟨hR, -⟩, hf⟩ := h
  have hsub : ofSparse n n (subRows rows c.rem) = ofSparse n n rows - ofSparse n n c.rem := by
    ext i j
    rw [Matrix.sub_apply, ofSparse_apply, ofSparse_apply, ofSparse_apply,
      sparseGet_subRows rows c.rem i j (by omega)]
  have hRs : (ofSparse n n c.rem)ᵀ = ofSparse n n c.rem :=
    (ofSparse_eq_transpose_of_isTransposeOf hR).symm
  have := c.eq_of_factorsLower (by rw [hsub, transpose_sub, hsymm, hRs]) hf
  rw [hsub] at this
  exact sub_eq_iff_eq_add.1 this

/-- The remainder of an accepted `factorsWith` is positive semidefinite over `ℝ`. -/
theorem posSemidef_rem {rows : List (List (ℕ × ℚ))} (h : c.factorsWith n rows = true) :
    ((ofSparse n n c.rem).map ((↑) : ℚ → ℝ)).PosSemidef := by
  simp only [factorsWith, Bool.and_eq_true] at h
  obtain ⟨⟨hR, hdd⟩, -⟩ := h
  refine posSemidef_of_diagDominant (by
    rw [← transpose_map, ← ofSparse_eq_transpose_of_isTransposeOf hR]) fun i => ?_
  have h2 := (Rat.cast_le (K := ℝ)).2 (diagDominant_of_ddGo (n := n) hdd i)
  rw [Rat.cast_sum] at h2
  simp only [map_apply]
  convert h2 using 2 with j
  split_ifs <;> simp

/-- An accepted `factorsWith` with positive pivots proves the symmetric matrix positive definite
over `ℝ`. -/
theorem posDef_of_factorsWith {rows : List (List (ℕ × ℚ))} (hlen : rows.length = n)
    (hsymm : (ofSparse n n rows)ᵀ = ofSparse n n rows) (h : c.factorsWith n rows = true)
    (hd : c.diag.all (0 < ·) = true) : ((ofSparse n n rows).map ((↑) : ℚ → ℝ)).PosDef := by
  obtain ⟨hl, hdl, hu⟩ := c.shape_of_factorsWith h
  rw [c.eq_add_of_factorsWith hlen hsymm h, Matrix.map_add _ Rat.cast_add]
  exact (c.toLDLCert.posDef_of_eq hl hdl hu hd rfl).add_posSemidef (c.posSemidef_rem h)

/-- An accepted `factorsWith` with nonnegative pivots proves the symmetric matrix positive
semidefinite over `ℝ`. -/
theorem posSemidef_of_factorsWith {rows : List (List (ℕ × ℚ))} (hlen : rows.length = n)
    (hsymm : (ofSparse n n rows)ᵀ = ofSparse n n rows) (h : c.factorsWith n rows = true)
    (hd : c.diag.all (0 ≤ ·) = true) : ((ofSparse n n rows).map ((↑) : ℚ → ℝ)).PosSemidef := by
  obtain ⟨hl, -, hu⟩ := c.shape_of_factorsWith h
  rw [c.eq_add_of_factorsWith hlen hsymm h, Matrix.map_add _ Rat.cast_add]
  refine PosSemidef.add ?_ (c.posSemidef_rem h)
  obtain ⟨L, hL, h1, hM⟩ := c.toLDLCert.map_eq_of_eq hl hu rfl
  rw [hM, posSemidef_mul_diagonal_mul_conjTranspose_iff hL h1]
  intro i
  simp only [List.all_eq_true, decide_eq_true_eq] at hd
  have : 0 ≤ c.toLDLCert.d n i := by
    rw [LDLCert.d, ofList_apply]
    change 0 ≤ c.diag.getD i 0
    rcases Nat.lt_or_ge i c.diag.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      exact hd _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]
  exact_mod_cast this

private theorem symm_of_factors {rows : List (List (ℕ × ℚ))} (h : c.factors n rows = true) :
    rows.length = n ∧ (ofSparse n n rows)ᵀ = ofSparse n n rows ∧ c.factorsWith n rows = true := by
  simp only [factors, Bool.and_eq_true] at h
  exact ⟨length_of_isSparseShape h.1.1, (ofSparse_eq_transpose_of_isTransposeOf h.1.2).symm, h.2⟩

/-- **Soundness for `≻ 0`.** An accepted certificate proves the matrix positive definite over
`ℝ`. -/
theorem posDef_of_checkPosDef {rows : List (List (ℕ × ℚ))} (h : c.checkPosDef n rows = true) :
    ((ofSparse n n rows).map ((↑) : ℚ → ℝ)).PosDef := by
  simp only [checkPosDef, Bool.and_eq_true] at h
  obtain ⟨hlen, hsymm, hf⟩ := c.symm_of_factors h.1
  exact c.posDef_of_factorsWith hlen hsymm hf h.2

/-- **Soundness for `⪰ 0`.** An accepted certificate proves the matrix positive semidefinite
over `ℝ`. -/
theorem posSemidef_of_checkPosSemidef {rows : List (List (ℕ × ℚ))}
    (h : c.checkPosSemidef n rows = true) : ((ofSparse n n rows).map ((↑) : ℚ → ℝ)).PosSemidef := by
  simp only [checkPosSemidef, Bool.and_eq_true] at h
  obtain ⟨hlen, hsymm, hf⟩ := c.symm_of_factors h.1
  exact c.posSemidef_of_factorsWith hlen hsymm hf h.2

/-- An exact certificate (`rem = []`) factors the matrix. -/
theorem eq_of_factors {rows : List (List (ℕ × ℚ))} (h : c.factors n rows = true)
    (hrem : c.rem = []) :
    ofSparse n n rows = c.toLDLCert.L n * diagonal (c.toLDLCert.d n) * (c.toLDLCert.L n)ᵀ := by
  obtain ⟨hlen, hsymm, hf⟩ := c.symm_of_factors h
  rw [c.eq_add_of_factorsWith hlen hsymm hf, hrem]
  ext i j
  simp [ofSparse_apply]

end EnvLDLCert

/-! ### Sparse Lyapunov residuals -/

/-- The common scale `sparseDenLcm (A ++ At) * sparseDenLcm P` of the sparse residual. -/
@[expose] def sparseLyapunovScale (A At P : List (List (ℕ × ℚ))) : ℕ :=
  sparseDenLcm (A ++ At) * sparseDenLcm P

/-- The fraction-free sparse residual `-(Âᵀ * P̂ + P̂ * Â)`, row by row with repeated columns
merged, for `Âᵀ`, `P̂` and `Â` the rows of `At`, `P` and `A` scaled to integers by the lcm of
their denominators. -/
@[expose] def sparseScaledResidual (A At P : List (List (ℕ × ℚ))) : List (List (ℕ × ℤ)) :=
  let sA := sparseDenLcm (A ++ At)
  let hP := P.map (scaleSparse (sparseDenLcm P))
  List.zipWith (fun x y => sparseNormalize (sparseMap (fun z => -z) (x ++ y)))
    (sparseMul (At.map (scaleSparse sA)) hP) (sparseMul hP (A.map (scaleSparse sA)))

/-- The sparse residual `-(Aᵀ * P + P * A)` over `ℚ`, when `At` is the transpose of `A`
(`ofSparse_sparseResidual`): the fraction-free residual divided by its scale. -/
@[expose] def sparseResidual (A At P : List (List (ℕ × ℚ))) : List (List (ℕ × ℚ)) :=
  let σ := sparseLyapunovScale A At P
  (sparseScaledResidual A At P).map (sparseMap fun z : ℤ => (z : ℚ) / σ)

private theorem getD_map_of_nil {β γ : Type*} {f : List β → List γ} (hf : f [] = [])
    (l : List (List β)) (i : ℕ) : (l.map f).getD i [] = f (l.getD i []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hf]

/-- The rational sparse residual reads as `-(Aᵀ * P + P * A)`. -/
theorem ofSparse_sparseResidual {n : ℕ} {A At P : List (List (ℕ × ℚ))} (hAl : A.length = n)
    (hAtl : At.length = n) (hPl : P.length = n) (hT : isTransposeOf A At = true) :
    ofSparse n n (sparseResidual A At P) =
      -((ofSparse n n A)ᵀ * ofSparse n n P + ofSparse n n P * ofSparse n n A) := by
  have hσ : ((sparseLyapunovScale A At P : ℕ) : ℚ) ≠ 0 := by
    have := Nat.mul_pos (denLcm_pos ((A ++ At).flatten.map (·.2)))
      (denLcm_pos (P.flatten.map (·.2)))
    exact_mod_cast this.ne'
  ext i j
  rw [ofSparse_apply, sparseResidual, getD_map_of_nil (by simp [sparseMap]),
    sparseGet_sparseMap (by simp) (fun a b => by push_cast; ring), sparseScaledResidual]
  set sA := sparseDenLcm (A ++ At)
  set sP := sparseDenLcm P
  set hA := A.map (scaleSparse sA)
  set hAt := At.map (scaleSparse sA)
  set hP := P.map (scaleSparse sP)
  have hlX : (sparseMul hAt hP).length = n := by rw [length_sparseMul]; simp [hAt, hAtl]
  have hlY : (sparseMul hP hA).length = n := by rw [length_sparseMul]; simp [hP, hPl]
  rw [List.getD_eq_getElem _ _ (by simp [hlX, hlY]), List.getElem_zipWith,
    sparseGet_sparseNormalize, sparseGet_sparseMap neg_zero (fun a b => neg_add a b),
    sparseGet_append, ← List.getD_eq_getElem _ [] (by omega),
    ← List.getD_eq_getElem _ [] (by omega)]
  have hdA : ∀ e ∈ A.flatten, e.2.den ∣ sA := fun e he =>
    den_dvd_sparseDenLcm e (by simp only [List.flatten_append, List.mem_append]; exact .inl he)
  have hdAt : ∀ e ∈ At.flatten, e.2.den ∣ sA := fun e he =>
    den_dvd_sparseDenLcm e (by simp only [List.flatten_append, List.mem_append]; exact .inr he)
  have hX := map_intCast_mul (ofSparse n n hAt) (ofSparse n n hP)
  have hY := map_intCast_mul (ofSparse n n hP) (ofSparse n n hA)
  rw [← ofSparse_sparseMul _ _ (by simp [hP, hPl]), map_ofSparse_scaleSparse hdAt,
    map_ofSparse_scaleSparse den_dvd_sparseDenLcm, ofSparse_eq_transpose_of_isTransposeOf hT]
    at hX
  rw [← ofSparse_sparseMul _ _ (by simp [hA, hAl]), map_ofSparse_scaleSparse hdA,
    map_ofSparse_scaleSparse den_dvd_sparseDenLcm] at hY
  have hx := congrFun (congrFun hX i) j
  have hy := congrFun (congrFun hY i) j
  simp only [map_apply, ofSparse_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    smul_eq_mul] at hx hy
  rw [Matrix.neg_apply, Matrix.add_apply]
  push_cast
  rw [hx, hy]
  field_simp
  simp only [sparseLyapunovScale, Nat.cast_mul]
  ring

/-- Witnesses for a sparse quadratic Lyapunov certificate for `ẋ = A x`: the rows of `Aᵀ`, and
envelope certificates for `P ≻ 0` and `-(Aᵀ * P + P * A) ≻ 0`. -/
structure SparseLyapunovCert where
  /-- The sparse rows of `Aᵀ`, checked against `A`. -/
  At : List (List (ℕ × ℚ))
  /-- An envelope certificate for `P`. -/
  P : EnvLDLCert
  /-- An envelope certificate for `-(Aᵀ * P + P * A)`. -/
  Q : EnvLDLCert

namespace SparseLyapunovCert

/-- Whether `c` certifies `P ≻ 0` and `-(Aᵀ * P + P * A) ≻ 0` for the sparse `n × n` matrices
`A` and `P`. The residual is recomputed from `A`, `Aᵀ` and `P`, and its symmetry follows from
that of the accepted `P`. -/
@[expose] def check (c : SparseLyapunovCert) (n : ℕ) (A P : List (List (ℕ × ℚ))) : Bool :=
  isSparseShape n n A && isSparseShape n n c.At && isTransposeOf A c.At &&
    c.P.checkPosDef n P && c.Q.factorsWith n (sparseResidual A c.At P) &&
    c.Q.diag.all (0 < ·)

/-- **Soundness.** An accepted sparse Lyapunov certificate proves `P ≻ 0` and
`-(Aᵀ * P + P * A) ≻ 0` for the real matrices `A` and `P`. -/
theorem posDef_of_check {c : SparseLyapunovCert} {n : ℕ} {A P : List (List (ℕ × ℚ))}
    (h : c.check n A P = true) :
    ((ofSparse n n P).map ((↑) : ℚ → ℝ)).PosDef ∧
      (-(((ofSparse n n A).map ((↑) : ℚ → ℝ))ᵀ * (ofSparse n n P).map ((↑) : ℚ → ℝ) +
        (ofSparse n n P).map ((↑) : ℚ → ℝ) * (ofSparse n n A).map ((↑) : ℚ → ℝ))).PosDef := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hAt⟩, hT⟩, hP⟩, hQ⟩, hd⟩ := h
  refine ⟨c.P.posDef_of_checkPosDef hP, ?_⟩
  have hPc := hP
  simp only [EnvLDLCert.checkPosDef, EnvLDLCert.factors, Bool.and_eq_true] at hPc
  have hPs := ofSparse_eq_transpose_of_isTransposeOf (m := n) (n := n) hPc.1.1.2
  have hR := ofSparse_sparseResidual (length_of_isSparseShape hA) (length_of_isSparseShape hAt)
    (length_of_isSparseShape hPc.1.1.1) hT
  have hlen : (sparseResidual A c.At P).length = n := by
    simp [sparseResidual, sparseScaledResidual, length_sparseMul, length_of_isSparseShape hAt,
      length_of_isSparseShape hPc.1.1.1]
  have hsymm : (ofSparse n n (sparseResidual A c.At P))ᵀ =
      ofSparse n n (sparseResidual A c.At P) := by
    rw [hR, transpose_neg, transpose_add, transpose_mul, transpose_mul, transpose_transpose,
      ← hPs, add_comm]
  have := c.Q.posDef_of_factorsWith hlen hsymm hQ hd
  rwa [hR, Matrix.map_neg _ Rat.cast_neg, Matrix.map_add _ Rat.cast_add,
    LDLCert.map_ratCast_mul, LDLCert.map_ratCast_mul, transpose_map] at this

end SparseLyapunovCert

end Cslib.LinearAlgebra

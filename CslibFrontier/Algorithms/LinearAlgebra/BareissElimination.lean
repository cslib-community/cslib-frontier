/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Matrix.RowTable
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Bareiss
public import CslibFrontier.Foundations.Data.Nat.BinarySize
public import CslibFrontier.Foundations.Data.Rat.Basic
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.LinearCombination

/-!
# Executable Bareiss–Jordan elimination over `ℚ` and coefficient bit-length bounds

This module provides executable list-matrix Bareiss–Jordan elimination over `ℤ` and `ℚ`, proved
equivalent to the minor-scaled Bareiss–Jordan matrix `Matrix.bareissMatrix` from
`CslibFrontier.Foundations.LinearAlgebra.Matrix.Bareiss`.

## References and local adaptations

* Alexander Schrijver, *Theory of Linear and Integer Programming* (Wiley, 1986), Section 3.2,
  Theorem 3.2 (pp. 29–30, determinant encoding-size bound) and Section 3.3, Theorem 3.3
  (pp. 32–33), Corollary 3.3a (pp. 33–34), and the Gauss–Jordan discussion with Equations
  (28)–(30) (p. 35).
* **Local adaptation:** Whereas Schrijver's Section 3.3 analyzes normalized rational Gaussian and
  Gauss–Jordan elimination directly over `ℚ`, this module clears row denominators upfront
  (`clearDenoms`) and runs fraction-free Sylvester–Bareiss minor-scaled Gauss–Jordan updates over
  `ℤ` (`bareissElimCols`), bounding all intermediate integer entries and output numerators and
  denominators via the explicit Hadamard/factorial bound `stageEntryBound`.

## Main definitions

* `IntTable`, `RatTable`, `BareissState`, `RationalElimResult`, `LinearSystemInput`,
  `LinearSolveResult`: explicit row-major matrix and elimination records.
* `clearDenoms`: clears row denominators of a `RatTable` to produce an exact `IntTable`.
* `bareissStep`, `bareissElimCols`, `bareissElim`: column-by-column fraction-free Bareiss–Jordan
  integer elimination.
* `rationalElim`, `ratRref`, `ratRank`, `ratRowBasis`, `ratKernelBasis`, `ratSolve`: rational
  reduced row echelon form, exact rank, linearly independent row and kernel bases, and canonical
  linear system solving with certified inconsistency.
* `stageEntryBound`: uniform Hadamard/factorial bound on intermediate integer entries and output
  rational numerators and denominators.

## Main results

* `bareissElimCols_inv`: loop invariant equating executable `Int.ediv` updates with
  `Matrix.bareissMatrix` and certifying exact divisibility, echelon zeroes, and pivot determinants.
* `rationalElim_spec`, `ratRref_isReducedRowEchelon`, `ratRank_eq`: `rationalElim` produces a
  genuine `Matrix.IsPivotedBy` / `Matrix.IsReducedRowEchelon` matrix over `ℚ` preserving row space
  and rank, with linearly independent spanning row and kernel bases.
* `ratSolve_spec`: `ratSolve` returns a canonical solution vector iff `A *ᵥ x = b` is consistent.
* `bareissInv_entry_bound`, `size_stageEntryBound_le`, `rationalElim_entry_bounds`,
  `ratSolve_entry_bounds`: polynomial Hadamard/factorial entry magnitude and `Nat.size`
  bit-length bounds for all intermediate states and rational outputs.
-/

public section

namespace Cslib.LinearAlgebra

open Finset Submodule Matrix
open scoped Matrix BigOperators

/-! ### Explicit table and elimination record types -/

/-- Explicit row-major integer matrix. -/
abbrev IntTable := Cslib.RowTable ℤ

/-- Explicit row-major rational matrix. -/
abbrev RatTable := Cslib.RowTable ℚ

/-- Intermediate state of column-by-column Bareiss–Jordan integer elimination. -/
structure BareissState where
  /-- Current minor-scaled integer table. -/
  table : IntTable
  /-- Current nonzero pivot determinant (`1` initially). -/
  pivotDet : ℤ
  /-- Ordered distinct pivot row indices selected so far. -/
  pivotRows : List ℕ
  /-- Strictly increasing pivot column indices selected so far. -/
  pivotCols : List ℕ
  deriving Repr

/-- Complete output of Bareiss–Jordan elimination on a rational matrix. -/
structure RationalElimResult where
  /-- Reduced row echelon rational matrix of the same shape, pivot rows first. -/
  rref : RatTable
  /-- Exact rank (`= pivotRows.length = pivotCols.length`). -/
  rank : ℕ
  /-- Pivot row indices in the original matrix forming a basis of the row space. -/
  pivotRows : List ℕ
  /-- Strictly increasing pivot column indices. -/
  pivotCols : List ℕ
  /-- Non-pivot column indices in ascending order. -/
  nonPivotCols : List ℕ
  /-- Kernel basis vectors, one per non-pivot column. -/
  kernelBasis : List (List ℚ)
  deriving Repr

/-- Input linear system `A x = b` over `ℚ`. -/
structure LinearSystemInput where
  /-- Coefficient matrix `A`. -/
  matrix : RatTable
  /-- Right-hand side vector `b`. -/
  rhs : List ℚ
  deriving Repr

/-- Output of Bareiss–Jordan linear solving for `A x = b`. -/
structure LinearSolveResult where
  /-- Canonical solution vector supported on pivot columns if consistent, or `none`. -/
  solution : Option (List ℚ)
  /-- Pivot row indices selected during elimination. -/
  pivotRows : List ℕ
  /-- Pivot column indices selected during elimination. -/
  pivotCols : List ℕ
  deriving Repr

deriving instance DecidableEq for BareissState, RationalElimResult, LinearSystemInput,
  LinearSolveResult

/-! ### Row denominator clearing -/

/-- Product of denominators of all entries in a rational row. -/
@[expose] def rowDenomProd (r : List ℚ) : ℕ :=
  r.foldl (fun acc q => acc * q.den) 1

/-- Scale a rational row by `rowDenomProd r`, producing an exact integer row. -/
@[expose] def clearRow (r : List ℚ) : List ℤ :=
  let d := rowDenomProd r
  r.map fun q => q.num * Int.ofNat (d / q.den)

/-- Normalized rational row extracted at row index `i` of length `M.numCols`. -/
@[expose] def normalizedRatRow (M : RatTable) (i : ℕ) : List ℚ :=
  (List.range M.numCols).map fun j => M.entry i j

/-- Normalize and clear row denominators of a `RatTable`, unconditionally producing a well-formed
`IntTable` of identical dimensions. -/
@[expose] def clearDenoms (M : RatTable) : IntTable :=
  ⟨M.numRows, M.numCols, (List.range M.numRows).map fun i => clearRow (normalizedRatRow M i)⟩

/-- Per-row positive integer multiplier produced by `clearDenoms M`. -/
def rowMultiplier (M : RatTable) (i : Fin M.numRows) : ℕ :=
  rowDenomProd (normalizedRatRow M i.val)

private theorem rowDenomProd_eq_prod (r : List ℚ) :
    rowDenomProd r = (r.map Rat.den).prod := by
  rw [rowDenomProd, List.prod_eq_foldl, List.foldl_map]

theorem rowDenomProd_pos (r : List ℚ) : 0 < rowDenomProd r := by
  rw [rowDenomProd_eq_prod]
  exact List.prod_pos (by simp [Rat.den_pos])

theorem den_dvd_rowDenomProd {r : List ℚ} {q : ℚ} (hq : q ∈ r) :
    q.den ∣ rowDenomProd r := by
  rw [rowDenomProd_eq_prod]
  exact List.dvd_prod (List.mem_map_of_mem hq)

theorem cast_clearRow_mem {r : List ℚ} {q : ℚ} (hq : q ∈ r) :
    ((q.num * Int.ofNat (rowDenomProd r / q.den) : ℤ) : ℚ) = (rowDenomProd r : ℚ) * q := by
  obtain ⟨e, he⟩ := den_dvd_rowDenomProd hq
  rw [he, Nat.mul_div_cancel_left e q.den_pos]
  push_cast [Int.ofNat_eq_natCast]
  linear_combination -(e : ℚ) * Rat.mul_den_eq_num q

theorem clearDenoms_wellFormed (M : RatTable) : (clearDenoms M).WellFormed := by
  refine ⟨by simp [clearDenoms], fun r hr => ?_⟩
  simp only [clearDenoms, List.mem_map, List.mem_range] at hr
  obtain ⟨i, _, rfl⟩ := hr
  simp [clearRow, normalizedRatRow, clearDenoms]

theorem rowMultiplier_pos (M : RatTable) (i : Fin M.numRows) : 0 < rowMultiplier M i :=
  rowDenomProd_pos _

private theorem clearDenoms_entry_eq (M : RatTable) (i : Fin M.numRows) (j : Fin M.numCols) :
    (clearDenoms M).toMatrix i j =
      (M.toMatrix i j).num * Int.ofNat (rowMultiplier M i / (M.toMatrix i j).den) := by
  simp only [Cslib.RowTable.toMatrix_apply, Cslib.RowTable.entry, clearDenoms]
  rw [List.getD_map_range _ [] i.isLt]
  simp only [clearRow, normalizedRatRow, List.map_map, Function.comp_def]
  exact List.getD_map_range _ 0 j.isLt

theorem clearDenoms_toMatrix_apply (M : RatTable) (i : Fin M.numRows) (j : Fin M.numCols) :
    ((clearDenoms M).toMatrix i j : ℚ) = (rowMultiplier M i : ℚ) * M.toMatrix i j := by
  rw [clearDenoms_entry_eq M i j]
  exact cast_clearRow_mem (List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩)

theorem rowDenomProd_le_pow {r : List ℚ} {b : ℕ} (hb : ∀ q ∈ r, q.den ≤ 2 ^ b) :
    rowDenomProd r ≤ 2 ^ (r.length * b) := by
  rw [rowDenomProd_eq_prod]
  refine (List.prod_le_pow_length (r.map Rat.den) (2 ^ b) (by simpa using hb)).trans_eq ?_
  rw [List.length_map, ← pow_mul, Nat.mul_comm]

theorem clearDenoms_abs_le (M : RatTable) {b : ℕ}
    (hb : ∀ i : Fin M.numRows, ∀ j : Fin M.numCols,
      (M.toMatrix i j).num.natAbs ≤ 2 ^ b ∧ (M.toMatrix i j).den ≤ 2 ^ b)
    (i : Fin M.numRows) (j : Fin M.numCols) :
    |(clearDenoms M).toMatrix i j| ≤ ((2 ^ ((M.numCols + 1) * b) : ℕ) : ℤ) := by
  rw [← Int.natCast_natAbs, Int.ofNat_le, clearDenoms_entry_eq M i j, Int.natAbs_mul]
  change (M.toMatrix i j).num.natAbs * (rowMultiplier M i / (M.toMatrix i j).den) ≤ _
  have hprod : rowMultiplier M i ≤ 2 ^ (M.numCols * b) := by
    simpa only [rowMultiplier, normalizedRatRow, List.length_map, List.length_range] using
      rowDenomProd_le_pow (r := normalizedRatRow M i.val) fun q hq => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
        exact (hb i ⟨c, List.mem_range.mp hc⟩).2
  calc _ ≤ 2 ^ b * 2 ^ (M.numCols * b) :=
        Nat.mul_le_mul (hb i j).1 ((Nat.div_le_self _ _).trans hprod)
    _ = 2 ^ ((M.numCols + 1) * b) := by rw [Nat.add_mul, Nat.one_mul, Nat.pow_add, mul_comm]

/-! ### Executable Bareiss–Jordan elimination over `ℤ` -/

/-- Find the first unpivoted row index `< st.table.numRows` with a nonzero entry in column `c`. -/
@[expose] def findPivotRow (st : BareissState) (c : ℕ) : Option ℕ :=
  (List.range st.table.numRows).find? fun r =>
    !st.pivotRows.contains r && decide (st.table.entry r c ≠ 0)

/-- Perform one column step of Bareiss–Jordan elimination on column `c`. -/
@[expose] def bareissStep (st : BareissState) (c : ℕ) : BareissState :=
  match findPivotRow st c with
  | none => st
  | some p =>
    let pivVal := st.table.entry p c
    let prevDet := st.pivotDet
    let m := st.table.numRows
    let n := st.table.numCols
    let nextTable : IntTable :=
      Cslib.RowTable.tabulate m n fun i j =>
        if i = p then st.table.entry p j
        else
          (pivVal * st.table.entry i j - st.table.entry i c * st.table.entry p j) / prevDet
    { table := nextTable
      pivotDet := pivVal
      pivotRows := st.pivotRows ++ [p]
      pivotCols := st.pivotCols ++ [c] }

/-- Initial state of Bareiss–Jordan elimination on an integer table. -/
@[expose] def bareissInit (T : IntTable) : BareissState :=
  ⟨T, 1, [], []⟩

/-- Run Bareiss–Jordan elimination across columns `0, …, colLimit - 1`. -/
@[expose] def bareissElimCols (T : IntTable) (colLimit : ℕ) : BareissState :=
  (List.range colLimit).foldl bareissStep (bareissInit T)

/-- Run full Bareiss–Jordan elimination across all columns of `T`. -/
@[expose] def bareissElim (T : IntTable) : BareissState :=
  bareissElimCols T T.numCols

/-- Map a bounded list of row or column indices to `Fin k → Fin m`. -/
def finSel {m k : ℕ} (idxs : List ℕ) (hk : k = idxs.length) (hidxs : ∀ i ∈ idxs, i < m) :
    Fin k → Fin m :=
  fun a => ⟨idxs[a.val]'(hk ▸ a.isLt), hidxs _ (List.getElem_mem _)⟩

private theorem finSel_snoc {m k : ℕ} (idxs : List ℕ) (hk : k = idxs.length) (x : ℕ)
    (hx : x < m) (hidxs : ∀ i ∈ idxs, i < m) (hx' : ∀ i ∈ idxs ++ [x], i < m)
    {hk' : k + 1 = (idxs ++ [x]).length} :
    finSel (idxs ++ [x]) hk' hx' = Fin.snoc (finSel idxs hk hidxs) (⟨x, hx⟩ : Fin m) := by
  subst hk
  ext a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last, finSel, Fin.val_last,
      List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton]
  · simp only [Fin.snoc_castSucc, finSel, Fin.val_castSucc, List.getElem_append_left i.isLt]

private theorem pairwise_lt_strictMono {n k : ℕ} {cols : List ℕ} (hk : k = cols.length)
    (hpw : cols.Pairwise (· < ·)) (hcols : ∀ c ∈ cols, c < n) :
    StrictMono (finSel cols hk hcols) := fun a b hab =>
  (List.pairwise_iff_getElem.mp hpw) a.val b.val (hk ▸ a.isLt) (hk ▸ b.isLt) hab

/-- A value is missed by `finSel idxs` exactly when it does not occur in the list `idxs`. -/
private theorem forall_finSel_ne_iff {m k : ℕ} {idxs : List ℕ} {hk : k = idxs.length}
    {hidxs : ∀ i ∈ idxs, i < m} {i : Fin m} :
    (∀ a, finSel idxs hk hidxs a ≠ i) ↔ i.val ∉ idxs := by
  subst hk
  simp [finSel, Fin.ext_iff, List.mem_iff_getElem, Fin.forall_iff]

/-- Loop invariant linking `BareissState` to `Matrix.bareissMatrix`. -/
structure BareissInv (T : IntTable) (stepCols : ℕ) (st : BareissState) : Prop where
  wellFormed : st.table.WellFormed
  dims : st.table.numRows = T.numRows ∧ st.table.numCols = T.numCols
  len_eq : st.pivotRows.length = st.pivotCols.length
  row_lt : ∀ r ∈ st.pivotRows, r < T.numRows
  col_lt : ∀ c ∈ st.pivotCols, c < stepCols
  col_dim : ∀ c ∈ st.pivotCols, c < T.numCols
  row_nodup : st.pivotRows.Nodup
  col_strict : st.pivotCols.Pairwise (· < ·)
  pivotDet_ne_zero : st.pivotDet ≠ 0
  pivotDet_eq :
    st.pivotDet = Matrix.pivotDet T.toMatrix
      (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim)
  table_eq :
    ∀ (i : Fin T.numRows) (j : Fin T.numCols),
      st.table.entry i.val j.val =
        Matrix.bareissMatrix T.toMatrix
          (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim) i j
  term_cols :
    ∀ (i : Fin T.numRows), (∀ a, finSel st.pivotRows rfl row_lt a ≠ i) →
      ∀ (j : Fin T.numCols), j.val < stepCols →
        Matrix.bareissMatrix T.toMatrix
          (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim) i j = 0
  echelon_zero :
    ∀ (a : Fin st.pivotRows.length) (j : Fin T.numCols),
      j.val < st.pivotCols[a.val]'(len_eq ▸ a.isLt) →
        Matrix.bareissMatrix T.toMatrix
          (finSel st.pivotRows rfl row_lt) (finSel st.pivotCols len_eq col_dim)
          (finSel st.pivotRows rfl row_lt a) j = 0

private theorem findPivotRow_none {st : BareissState} {c : ℕ}
    (hnone : findPivotRow st c = none) :
    ∀ r < st.table.numRows, r ∉ st.pivotRows → st.table.entry r c = 0 := fun r hr hnr => by
  simpa [hnr] using List.find?_eq_none.mp hnone r (List.mem_range.mpr hr)

private theorem findPivotRow_some {st : BareissState} {c p : ℕ}
    (hsome : findPivotRow st c = some p) :
    p < st.table.numRows ∧ p ∉ st.pivotRows ∧ st.table.entry p c ≠ 0 :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some hsome), by simpa using List.find?_some hsome⟩

theorem bareissInv_init {T : IntTable} (hT : T.WellFormed) :
    BareissInv T 0 (bareissInit T) :=
  { wellFormed := hT
    dims := ⟨rfl, rfl⟩
    len_eq := rfl
    row_lt := fun _ h => nomatch h
    col_lt := fun _ h => nomatch h
    col_dim := fun _ h => nomatch h
    row_nodup := List.nodup_nil
    col_strict := List.Pairwise.nil
    pivotDet_ne_zero := one_ne_zero
    pivotDet_eq := (Matrix.pivotDet_zero T.toMatrix _ _).symm
    table_eq := fun i j => (congrFun₂ (Matrix.bareissMatrix_zero T.toMatrix _ _) i j).symm
    term_cols := fun _ _ _ hj => absurd hj (Nat.not_lt_zero _)
    echelon_zero := fun a _ _ => a.elim0 }

/-- Assemble `BareissInv` from pivot selections `S`, `C` indexed by any `k = st.pivotRows.length`.
After a pivot is appended, `k = _ + 1` and the selections are `Fin.snoc`s (`finSel_snoc`). -/
private theorem BareissInv.of_sel {T : IntTable} {stepCols k : ℕ} {st : BareissState}
    (hk : k = st.pivotRows.length) (wellFormed : st.table.WellFormed)
    (dims : st.table.numRows = T.numRows ∧ st.table.numCols = T.numCols)
    (len_eq : st.pivotRows.length = st.pivotCols.length)
    (row_lt : ∀ r ∈ st.pivotRows, r < T.numRows) (col_lt : ∀ c ∈ st.pivotCols, c < stepCols)
    (col_dim : ∀ c ∈ st.pivotCols, c < T.numCols) (row_nodup : st.pivotRows.Nodup)
    (col_strict : st.pivotCols.Pairwise (· < ·)) (pivotDet_ne_zero : st.pivotDet ≠ 0)
    {S : Fin k → Fin T.numRows} {C : Fin k → Fin T.numCols}
    (hS : finSel st.pivotRows hk row_lt = S)
    (hC : finSel st.pivotCols (hk.trans len_eq) col_dim = C)
    (pivotDet_eq : st.pivotDet = Matrix.pivotDet T.toMatrix S C)
    (table_eq : ∀ (i : Fin T.numRows) (j : Fin T.numCols),
      st.table.entry i.val j.val = Matrix.bareissMatrix T.toMatrix S C i j)
    (term_cols : ∀ i : Fin T.numRows, (∀ a, S a ≠ i) → ∀ j : Fin T.numCols, j.val < stepCols →
      Matrix.bareissMatrix T.toMatrix S C i j = 0)
    (echelon_zero : ∀ (a : Fin k) (j : Fin T.numCols), j < C a →
      Matrix.bareissMatrix T.toMatrix S C (S a) j = 0) :
    BareissInv T stepCols st := by
  subst hk hS hC
  exact ⟨wellFormed, dims, len_eq, row_lt, col_lt, col_dim, row_nodup, col_strict,
    pivotDet_ne_zero, pivotDet_eq, table_eq, term_cols, echelon_zero⟩

/-- Integer version of `Matrix.bareissMatrix_snoc_zero_of_forall`: a column that vanishes on a set
`Q` of rows containing the new pivot row keeps vanishing on `Q` after the pivot step. -/
private theorem bareissMatrix_snoc_zero_of_forall_int {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    {S : Fin k → Fin m} {C : Fin k → Fin n} (hΔ : Matrix.pivotDet A S C ≠ 0)
    {p : Fin m} (hp : ∀ a : Fin k, S a ≠ p) (q : Fin n)
    (hΔ' : Matrix.bareissMatrix A S C p q ≠ 0) (j : Fin n) (Q : Fin m → Prop) (hQp : Q p)
    (hQzero : ∀ i : Fin m, Q i → Matrix.bareissMatrix A S C i j = 0) (i : Fin m) (hQi : Q i) :
    Matrix.bareissMatrix A (Fin.snoc S p) (Fin.snoc C q) i j = 0 := by
  obtain ⟨h₁, h₂⟩ := Matrix.pivotDet_mul_bareissMatrix_snoc_int A hΔ hp q hΔ' i j
  by_cases hip : i = p
  · rw [h₁ hip, hQzero p hQp]
  · simpa [hQzero i hQi, hQzero p hQp, hΔ] using h₂ hip

/-- Column step of the invariant when column `c` has no pivot: the state is unchanged and column
`c` vanishes on every unpivoted row. -/
private theorem bareissInv_step_none {T : IntTable} {c : ℕ} (hc : c < T.numCols)
    {st : BareissState} (hinv : BareissInv T c st) (hfind : findPivotRow st c = none) :
    BareissInv T (c + 1) st :=
  { hinv with
    col_lt := fun x hx => (hinv.col_lt x hx).trans (Nat.lt_succ_self c)
    term_cols := fun i hi j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
      · exact hinv.term_cols i hi j hjlt
      · obtain rfl : j = ⟨c, hc⟩ := Fin.ext hjeq
        rw [← hinv.table_eq i ⟨c, hc⟩]
        exact findPivotRow_none hfind i.val (hinv.dims.1.symm ▸ i.isLt)
          (forall_finSel_ne_iff.1 hi) }

/-- Column step of the invariant when row `p` is the pivot found in column `c`: the new table is
the Bareiss–Jordan matrix of the pivot selections extended by `(p, c)`. -/
private theorem bareissInv_step_some {T : IntTable} {c p : ℕ} (hc : c < T.numCols)
    {st : BareissState} (hinv : BareissInv T c st) (hfind : findPivotRow st c = some p) :
    BareissInv T (c + 1) (bareissStep st c) := by
  obtain ⟨hp_lt, hp_notMem, hp_nz⟩ := findPivotRow_some hfind
  have hp_m : p < T.numRows := hinv.dims.1 ▸ hp_lt
  let S := finSel st.pivotRows rfl hinv.row_lt
  let C := finSel st.pivotCols hinv.len_eq hinv.col_dim
  have hp_fin : ∀ a, S a ≠ ⟨p, hp_m⟩ := forall_finSel_ne_iff.2 hp_notMem
  have hΔ : Matrix.pivotDet T.toMatrix S C ≠ 0 := hinv.pivotDet_eq ▸ hinv.pivotDet_ne_zero
  have hΔ' : Matrix.bareissMatrix T.toMatrix S C ⟨p, hp_m⟩ ⟨c, hc⟩ ≠ 0 :=
    hinv.table_eq ⟨p, hp_m⟩ ⟨c, hc⟩ ▸ hp_nz
  -- Columns left of the new pivot column vanish in the extended elimination matrix at every
  -- row that is not a pivot row, or is the pivot row of a later column.
  have hzero : ∀ j : Fin T.numCols, j.val < c → ∀ r : Fin T.numRows,
      ((∀ a, S a ≠ r) ∨ ∃ a, S a = r ∧ j < C a) →
      Matrix.bareissMatrix T.toMatrix (Fin.snoc S ⟨p, hp_m⟩) (Fin.snoc C ⟨c, hc⟩) r j = 0 :=
    fun j hjlt => bareissMatrix_snoc_zero_of_forall_int T.toMatrix hΔ hp_fin ⟨c, hc⟩ hΔ' j _
      (Or.inl hp_fin) fun r hr => hr.elim (hinv.term_cols r · j hjlt)
        fun ⟨a, ha, hja⟩ => ha ▸ hinv.echelon_zero a j hja
  simp only [bareissStep, hfind]
  refine BareissInv.of_sel (k := st.pivotRows.length + 1) (hk := by simp)
    (wellFormed := Cslib.RowTable.wellFormed_tabulate _ _ _) (dims := hinv.dims)
    (len_eq := by simp [hinv.len_eq])
    (row_lt := List.forall_mem_append.2 ⟨hinv.row_lt, by simpa using hp_m⟩)
    (col_lt := List.forall_mem_append.2
      ⟨fun x hx => (hinv.col_lt x hx).trans c.lt_succ_self, by simp⟩)
    (col_dim := List.forall_mem_append.2 ⟨hinv.col_dim, by simpa using hc⟩)
    (row_nodup := hinv.row_nodup.append (List.nodup_singleton p) (by simpa using hp_notMem))
    (col_strict := List.pairwise_append.2
      ⟨hinv.col_strict, List.pairwise_singleton _ _, by simpa using hinv.col_lt⟩)
    (pivotDet_ne_zero := hp_nz) (hS := finSel_snoc st.pivotRows rfl p hp_m hinv.row_lt _)
    (hC := finSel_snoc st.pivotCols hinv.len_eq c hc hinv.col_dim _)
    (pivotDet_eq := (hinv.table_eq ⟨p, hp_m⟩ ⟨c, hc⟩).trans
      (Matrix.bareissMatrix_nonPivot T.toMatrix C hp_fin ⟨c, hc⟩))
    (table_eq := fun i j => ?_) (term_cols := fun i hi j hj => ?_)
    (echelon_zero := fun a j => ?_)
  · -- the new table: row `p` is kept, the other rows are the exact Bareiss quotients
    rw [Cslib.RowTable.entry_tabulate_of_lt _ (hinv.dims.1.symm ▸ i.isLt)
      (hinv.dims.2.symm ▸ j.isLt)]
    by_cases hip : i.val = p
    · obtain rfl : i = ⟨p, hp_m⟩ := Fin.ext hip
      rw [ite_eq_left rfl, hinv.table_eq ⟨p, hp_m⟩ j]
      exact ((Matrix.pivotDet_mul_bareissMatrix_snoc_int T.toMatrix hΔ hp_fin ⟨c, hc⟩ hΔ'
        ⟨p, hp_m⟩ j).1 rfl).symm
    · rw [ite_eq_right hip, hinv.table_eq ⟨p, hp_m⟩ ⟨c, hc⟩, hinv.table_eq i j,
        hinv.table_eq i ⟨c, hc⟩, hinv.table_eq ⟨p, hp_m⟩ j, hinv.pivotDet_eq]
      exact Matrix.bareissStep_ediv_eq_int T.toMatrix hΔ hp_fin ⟨c, hc⟩ hΔ'
        (fun h => hip (congrArg Fin.val h)) j
  · -- unpivoted rows vanish in the columns `< c` and in the new pivot column `c`
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjlt | hjeq
    · exact hzero j hjlt i (Or.inl fun a => by simpa using hi a.castSucc)
    · obtain rfl : j = ⟨c, hc⟩ := Fin.ext hjeq
      simpa using Matrix.bareissMatrix_nonPivot_col T.toMatrix (Fin.snoc C ⟨c, hc⟩) hi
        (Fin.last _)
  · -- every pivot row, new or old, vanishes left of its pivot column
    refine Fin.lastCases (fun hj => ?_) (fun a hj => ?_) a
    · rw [Fin.snoc_last] at hj ⊢
      exact hzero j hj _ (Or.inl hp_fin)
    · rw [Fin.snoc_castSucc] at hj ⊢
      exact hzero j (Nat.lt_trans hj (hinv.col_lt _ (List.getElem_mem _))) _
        (Or.inr ⟨a, rfl, hj⟩)

theorem bareissInv_step {T : IntTable} {c : ℕ} (hc : c < T.numCols) {st : BareissState}
    (hinv : BareissInv T c st) : BareissInv T (c + 1) (bareissStep st c) := by
  cases hfind : findPivotRow st c with
  | none =>
    rw [show bareissStep st c = st by simp only [bareissStep, hfind]]
    exact bareissInv_step_none hc hinv hfind
  | some p => exact bareissInv_step_some hc hinv hfind

private theorem bareissElimCols_inv_aux {T : IntTable} (hT : T.WellFormed) :
    ∀ k ≤ T.numCols, BareissInv T k ((List.range k).foldl bareissStep (bareissInit T))
  | 0, _ => bareissInv_init hT
  | k + 1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact bareissInv_step hk (bareissElimCols_inv_aux hT k (Nat.le_of_succ_le hk))

/-- Correctness invariant for `bareissElimCols` across columns `< colLimit ≤ T.numCols`. -/
theorem bareissElimCols_inv {T : IntTable} (hT : T.WellFormed) {colLimit : ℕ}
    (hlim : colLimit ≤ T.numCols) :
    BareissInv T colLimit (bareissElimCols T colLimit) :=
  bareissElimCols_inv_aux hT colLimit hlim

/-- Correctness invariant for full `bareissElim`. -/
theorem bareissElim_inv {T : IntTable} (hT : T.WellFormed) :
    BareissInv T T.numCols (bareissElim T) :=
  bareissElimCols_inv hT (le_refl _)

/-! ### Executable rational RREF, rank, row basis, kernel basis, and linear solver -/

/-- Build a rational row from an `IntTable` row divided by `Δ`. -/
@[expose] def scaledIntRow (T : IntTable) (Δ : ℤ) (r : ℕ) : List ℚ :=
  (List.range T.numCols).map fun j => Rat.divInt (T.entry r j) Δ

/-- Extract normalized original rows of `M` at row indices `idxs`. -/
@[expose] def selectRatRows (M : RatTable) (idxs : List ℕ) : List (List ℚ) :=
  idxs.map fun r => normalizedRatRow M r

/-- Non-pivot column indices `< n` in ascending order. -/
@[expose] def computeNonPivotCols (n : ℕ) (pivotCols : List ℕ) : List ℕ :=
  (List.range n).filter fun c => !pivotCols.contains c

/-- Kernel basis vector associated with non-pivot column `j`. -/
@[expose] def buildKernelVec (st : BareissState) (j : ℕ) : List ℚ :=
  let pairs := st.pivotRows.zip st.pivotCols
  (List.range st.table.numCols).map fun c =>
    match pairs.find? (fun pc => pc.2 == c) with
    | some (p, _) => Rat.divInt (-st.table.entry p j) st.pivotDet
    | none => if c = j then 1 else 0

/-- Complete Bareiss–Jordan elimination on a rational matrix `M`: RREF, rank, row basis indices,
pivot/non-pivot columns, and kernel basis. -/
@[expose] def rationalElim (M : RatTable) : RationalElimResult :=
  let T := clearDenoms M
  let st := bareissElim T
  let k := st.pivotRows.length
  let pivRows := st.pivotRows.map (scaledIntRow st.table st.pivotDet)
  let zeroRows := List.replicate (M.numRows - k) (List.replicate M.numCols (0 : ℚ))
  let nonPiv := computeNonPivotCols M.numCols st.pivotCols
  { rref := ⟨M.numRows, M.numCols, pivRows ++ zeroRows⟩
    rank := k
    pivotRows := st.pivotRows
    pivotCols := st.pivotCols
    nonPivotCols := nonPiv
    kernelBasis := nonPiv.map (buildKernelVec st) }

/-- Executable rational reduced row echelon form. -/
@[expose] def ratRref (M : RatTable) : RatTable :=
  (rationalElim M).rref

/-- Exact rational matrix rank via Bareiss–Jordan elimination. -/
@[expose] def ratRank (M : RatTable) : ℕ :=
  (rationalElim M).rank

/-- Linearly independent spanning subset of rows of `M`. -/
@[expose] def ratRowBasis (M : RatTable) : List (List ℚ) :=
  selectRatRows M (rationalElim M).pivotRows

/-- Linearly independent spanning basis of `ker M.toMatrix.mulVecLin`. -/
@[expose] def ratKernelBasis (M : RatTable) : List (List ℚ) :=
  (rationalElim M).kernelBasis

/-- Augmented matrix `[A | b]` of shape `A.numRows × (A.numCols + 1)`. -/
@[expose] def augmentRatTable (A : RatTable) (b : List ℚ) : RatTable :=
  ⟨A.numRows, A.numCols + 1,
    (List.range A.numRows).map fun i => normalizedRatRow A i ++ [b.getD i 0]⟩

/-- Solve `A x = b` canonically via augmented Bareiss–Jordan elimination. -/
@[expose] def ratSolve (sys : LinearSystemInput) : LinearSolveResult :=
  let A := sys.matrix
  let aug := clearDenoms (augmentRatTable A sys.rhs)
  let st := bareissElimCols aug A.numCols
  let consistent :=
    (List.range A.numRows).all fun r =>
      st.pivotRows.contains r || decide (st.table.entry r A.numCols = 0)
  if consistent then
    let pairs := st.pivotRows.zip st.pivotCols
    let x :=
      (List.range A.numCols).map fun c =>
        match pairs.find? (fun pc => pc.2 == c) with
        | some (p, _) => Rat.divInt (st.table.entry p A.numCols) st.pivotDet
        | none => 0
    ⟨some x, st.pivotRows, st.pivotCols⟩
  else
    ⟨none, st.pivotRows, st.pivotCols⟩

/-! ### Row-scaling invariance and correctness of `rationalElim` / `ratSolve` -/

section ScaleAndCorrectness

private def rowScaled {m n : ℕ} (d : Fin m → ℚ) (A : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℚ :=
  Matrix.of fun i j => d i * A i j

private theorem span_rowSel_rowScaled {m n k : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) (S : Fin k → Fin m) :
    Submodule.span ℚ (Set.range fun a => rowScaled d A (S a)) =
      Submodule.span ℚ (Set.range fun a => A (S a)) := by
  refine le_antisymm (span_le.2 ?_) (span_le.2 ?_) <;> rintro _ ⟨a, rfl⟩
  · exact smul_mem _ (d (S a)) (subset_span ⟨a, rfl⟩)
  · exact (smul_mem_iff _ (hd (S a))).1 (subset_span ⟨a, rfl⟩)

private theorem span_row_rowScaled {m n : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    Submodule.span ℚ (Set.range (rowScaled d A)) = Submodule.span ℚ (Set.range A) :=
  span_rowSel_rowScaled hd A id

private theorem rank_rowScaled {m n : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    (rowScaled d A).rank = A.rank := by
  rw [rank_eq_finrank_span_row, rank_eq_finrank_span_row]
  change Module.finrank ℚ (Submodule.span ℚ (Set.range (rowScaled d A))) =
    Module.finrank ℚ (Submodule.span ℚ (Set.range A))
  rw [span_row_rowScaled hd A]

/-- Scaling the rows of `A` and of the right-hand side by nonzero factors does not change the
solutions of `A *ᵥ x = b`. -/
private theorem rowScaled_mulVec_eq_iff {m n : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) (b : Fin m → ℚ) :
    rowScaled d A *ᵥ x = (fun i => d i * b i) ↔ A *ᵥ x = b := by
  simp only [funext_iff, mulVec]
  refine forall_congr' fun i => ?_
  rw [show rowScaled d A i = d i • A i from rfl, smul_dotProduct, smul_eq_mul,
    mul_right_inj' (hd i)]

private theorem ker_mulVecLin_rowScaled {m n : ℕ} {d : Fin m → ℚ} (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℚ) :
    LinearMap.ker (rowScaled d A).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext v
  simpa only [LinearMap.mem_ker, mulVecLin_apply, Pi.zero_apply, mul_zero, ← Pi.zero_def] using
    rowScaled_mulVec_eq_iff hd A v 0

private theorem bareissInv_rat_bridge {T : IntTable} {colLimit m n : ℕ} {st : BareissState}
    (hinv : BareissInv T colLimit st) (M' : Matrix (Fin m) (Fin n) ℚ)
    (S : Fin st.pivotRows.length → Fin m) (C : Fin st.pivotRows.length → Fin n)
    (hm : m = T.numRows := by rfl) (hn : n = T.numCols := by rfl)
    (hS : ∀ a, (S a).val = st.pivotRows[a.val] := by intro _; rfl)
    (hC : ∀ a, (C a).val = st.pivotCols[a.val]'(hinv.len_eq ▸ a.isLt) := by intro _; rfl)
    (hM' : ∀ (i : Fin m) (j : Fin n),
      M' i j = (T.toMatrix ⟨i.val, hm ▸ i.isLt⟩ ⟨j.val, hn ▸ j.isLt⟩ : ℚ)) :
    Matrix.pivotDet M' S C = (st.pivotDet : ℚ) ∧
      (∀ i j, Matrix.bareissMatrix M' S C i j = (st.table.entry i.val j.val : ℚ)) ∧
      (∀ i, (∀ a, S a ≠ i) → ∀ j : Fin n, j.val < colLimit →
        Matrix.bareissMatrix M' S C i j = 0) ∧
      (∀ (a : Fin st.pivotRows.length) (j : Fin n),
        j < C a → Matrix.bareissMatrix M' S C (S a) j = 0) := by
  subst hm hn
  obtain rfl : S = finSel st.pivotRows rfl hinv.row_lt := funext fun a => Fin.ext (hS a)
  obtain rfl : C = finSel st.pivotCols hinv.len_eq hinv.col_dim := funext fun a => Fin.ext (hC a)
  obtain rfl : M' = T.toMatrix.map (Int.castRingHom ℚ) := Matrix.ext hM'
  have hB : ∀ i j, Matrix.bareissMatrix (T.toMatrix.map (Int.castRingHom ℚ)) _ _ i j =
      (st.table.entry i.val j.val : ℚ) := fun i j => by
    rw [← Matrix.map_bareissMatrix, Matrix.map_apply, ← hinv.table_eq i j, eq_intCast]
  refine ⟨?_, hB, fun i hi j hj => ?_, fun a j hj => ?_⟩
  · rw [← Matrix.map_pivotDet (Int.castRingHom ℚ), ← hinv.pivotDet_eq, eq_intCast]
  · rw [hB, hinv.table_eq, hinv.term_cols i hi j hj, Int.cast_zero]
  · rw [hB, hinv.table_eq, hinv.echelon_zero a j hj, Int.cast_zero]

private theorem bareissInv_divInt_eq_rrefOfBareiss {m n : ℕ} {st : BareissState}
    {M' : Matrix (Fin m) (Fin n) ℚ} {S : Fin st.pivotRows.length → Fin m}
    {C : Fin st.pivotRows.length → Fin n}
    (hΔ : Matrix.pivotDet M' S C = (st.pivotDet : ℚ))
    (hBM : ∀ i j, Matrix.bareissMatrix M' S C i j = (st.table.entry i.val j.val : ℚ))
    (hS : ∀ a, (S a).val = st.pivotRows[a.val])
    (a : Fin st.pivotRows.length) (j : Fin n) :
    Rat.divInt (st.table.entry (st.pivotRows[a.val]) j.val) st.pivotDet =
      Matrix.rrefOfBareiss M' S C (S a) j := by
  rw [Rat.divInt_eq_div, div_eq_mul_inv, mul_comm]
  change (st.pivotDet : ℚ)⁻¹ * (st.table.entry (st.pivotRows[a.val]) j.val : ℚ) =
    (Matrix.pivotDet M' S C)⁻¹ * Matrix.bareissMatrix M' S C (S a) j
  rw [hΔ, hBM (S a) j, hS a]

/-- Looking up the `a`-th key of a duplicate-free key list `ys` in `xs.zip ys` returns the `a`-th
pair. -/
private theorem find?_zip_getElem {xs ys : List ℕ} (hlen : xs.length = ys.length)
    (hy_nodup : ys.Nodup) {a : Fin xs.length} :
    (xs.zip ys).find? (fun pc => pc.2 == ys[a.val]'(hlen ▸ a.isLt)) =
      some (xs[a.val], ys[a.val]'(hlen ▸ a.isLt)) := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp, a, by simpa [hlen] using a.isLt, by simp, fun j hj => ?_⟩
  simpa [hy_nodup.getElem_inj_iff] using hj.ne

/-- Looking up a key that is not in `ys` in `xs.zip ys` fails. -/
private theorem find?_zip_eq_none {xs ys : List ℕ} {c : ℕ} (hc : c ∉ ys) :
    (xs.zip ys).find? (fun pc => pc.2 == c) = none :=
  List.find?_eq_none.2 fun ⟨_, y⟩ hmem => by
    simpa using fun h : y = c => hc (h ▸ (List.of_mem_zip hmem).2)

private theorem bareissInv_find?_pivot_eq {T : IntTable} {colLimit m n n' : ℕ}
    {st : BareissState} (hinv : BareissInv T colLimit st)
    {M' : Matrix (Fin m) (Fin n) ℚ} {S : Fin st.pivotRows.length → Fin m}
    {C : Fin st.pivotRows.length → Fin n} {C' : Fin st.pivotRows.length → Fin n'}
    (hΔ : Matrix.pivotDet M' S C = (st.pivotDet : ℚ))
    (hBM : ∀ i j, Matrix.bareissMatrix M' S C i j = (st.table.entry i.val j.val : ℚ))
    (j : Fin n) (c : Fin n') {onNonPivot target : ℚ} (sgn : ℤ)
    (hPiv : ∀ a, C' a = c → (sgn : ℚ) * Matrix.rrefOfBareiss M' S C (S a) j = target)
    (hNonPiv : (∀ a, C' a ≠ c) → onNonPivot = target)
    (hS : ∀ a, (S a).val = st.pivotRows[a.val] := by intro _; rfl)
    (hC' : ∀ a, (C' a).val = st.pivotCols[a.val]'(hinv.len_eq ▸ a.isLt) := by intro _; rfl) :
    (match (st.pivotRows.zip st.pivotCols).find? (fun pc => pc.2 == c.val) with
      | some (p, _) => Rat.divInt (sgn * st.table.entry p j.val) st.pivotDet
      | none => onNonPivot) = target := by
  have hC_nodup : st.pivotCols.Nodup := hinv.col_strict.imp Nat.ne_of_lt
  by_cases hc : ∃ a, C' a = c
  · obtain ⟨a, rfl⟩ := hc
    rw [hC' a, find?_zip_getElem hinv.len_eq hC_nodup]
    dsimp only
    rw [Rat.divInt_eq_div, Int.cast_mul, mul_div_assoc, ← Rat.divInt_eq_div,
      bareissInv_divInt_eq_rrefOfBareiss hΔ hBM hS a j]
    exact hPiv a rfl
  · rw [find?_zip_eq_none fun hmem => ?_]
    · exact hNonPiv (not_exists.1 hc)
    · obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp hmem
      exact hc ⟨⟨i, hinv.len_eq ▸ hi⟩, Fin.ext ((hC' _).trans hval)⟩

private theorem nodup_length_le_of_lt {l : List ℕ} {m : ℕ} (hnodup : l.Nodup)
    (hlt : ∀ x ∈ l, x < m) : l.length ≤ m :=
  (hnodup.subperm fun x hx => List.mem_range.mpr (hlt x hx)).length_le.trans_eq List.length_range

theorem rationalElim_wellFormed (M : RatTable) : (rationalElim M).rref.WellFormed := by
  have hinv := bareissElim_inv (clearDenoms_wellFormed M)
  refine ⟨?_, fun r hr => ?_⟩
  · have hlen : _ ≤ M.numRows := nodup_length_le_of_lt hinv.row_nodup hinv.row_lt
    simp only [rationalElim, List.length_append, List.length_map, List.length_replicate]
    omega
  · simp only [rationalElim, List.mem_append, List.mem_map, List.mem_replicate] at hr
    rcases hr with ⟨p, _, rfl⟩ | ⟨_, rfl⟩
    · simpa [scaledIntRow, rationalElim, clearDenoms] using hinv.dims.2
    · simp [rationalElim]

/-- Entry `(i, j)` of the table `(rationalElim M).rref`: the pivot rows come first, divided by the
pivot determinant, followed by zero rows. -/
private theorem rationalElim_rref_entry (M : RatTable) {i j : ℕ} (hi : i < M.numRows)
    (hj : j < M.numCols) :
    (rationalElim M).rref.entry i j =
      if h : i < (bareissElim (clearDenoms M)).pivotRows.length then
        Rat.divInt ((bareissElim (clearDenoms M)).table.entry
          ((bareissElim (clearDenoms M)).pivotRows[i]) j) (bareissElim (clearDenoms M)).pivotDet
      else 0 := by
  have hn : (bareissElim (clearDenoms M)).table.numCols = M.numCols :=
    (bareissElim_inv (clearDenoms_wellFormed M)).dims.2
  simp only [Cslib.RowTable.entry, rationalElim]
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ [] (by simpa using h),
      List.getElem_map]
    exact List.getD_map_range _ 0 (hn ▸ hj)
  · rw [List.getD_append_right _ _ _ _ (by simpa using h), List.getD_replicate _ (by simp; omega),
      List.getD_replicate _ hj]

/-- The non-pivot columns are the columns below `n` that are not pivot columns. -/
private theorem mem_computeNonPivotCols {n c : ℕ} {cols : List ℕ} :
    c ∈ computeNonPivotCols n cols ↔ c < n ∧ c ∉ cols := by
  simp [computeNonPivotCols]

/-- A duplicate-free list of `cols.length` pivot columns below `n` leaves `n - cols.length`
non-pivot columns. -/
private theorem length_computeNonPivotCols {n : ℕ} {cols : List ℕ} (hnodup : cols.Nodup)
    (hlt : ∀ c ∈ cols, c < n) : (computeNonPivotCols n cols).length = n - cols.length := by
  have h := List.length_eq_length_filter_add (l := List.range n) fun c => cols.contains c
  have hperm : ((List.range n).filter fun c => cols.contains c).Perm cols :=
    (List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnodup).2 fun c => by
      simpa using hlt c
  rw [List.length_range, hperm.length_eq] at h
  rw [computeNonPivotCols]
  omega

/-- Complete algebraic and reduced-echelon characterization of `rationalElim M` for any `M`. -/
theorem rationalElim_spec (M : RatTable) :
    let res := rationalElim M
    res.rref.WellFormed ∧
      res.rref.toMatrix.IsReducedRowEchelon ∧
      (∃ l, res.rref.toMatrix.IsPivotedBy l) ∧
      Submodule.span ℚ (Set.range res.rref.toMatrix) =
        Submodule.span ℚ (Set.range M.toMatrix) ∧
      res.rank = M.toMatrix.rank ∧
      res.pivotRows.length = res.rank ∧
      res.pivotCols.length = res.rank ∧
      res.nonPivotCols.length = M.numCols - res.rank ∧
      LinearIndependent ℚ (fun a : Fin res.pivotRows.length =>
        M.toMatrix ⟨res.pivotRows[a.val],
          (bareissElim_inv (clearDenoms_wellFormed M)).row_lt _ (List.getElem_mem _)⟩) ∧
      Submodule.span ℚ (Set.range fun a : Fin res.pivotRows.length =>
        M.toMatrix ⟨res.pivotRows[a.val],
          (bareissElim_inv (clearDenoms_wellFormed M)).row_lt _ (List.getElem_mem _)⟩) =
        Submodule.span ℚ (Set.range M.toMatrix) ∧
      res.kernelBasis.length = M.numCols - res.rank ∧
      LinearIndependent ℚ (fun idx : Fin res.kernelBasis.length =>
        (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) ∧
      Submodule.span ℚ (Set.range fun idx : Fin res.kernelBasis.length =>
        (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) =
        LinearMap.ker M.toMatrix.mulVecLin := by
  intro res
  set st := bareissElim (clearDenoms M)
  have hinv := bareissElim_inv (clearDenoms_wellFormed M)
  have hd : ∀ i : Fin M.numRows, (rowMultiplier M i : ℚ) ≠ 0 := fun i =>
    Nat.cast_ne_zero.mpr (rowMultiplier_pos M i).ne'
  let M' := rowScaled (fun i => (rowMultiplier M i : ℚ)) M.toMatrix
  let S : Fin st.pivotRows.length → Fin M.numRows := finSel st.pivotRows rfl hinv.row_lt
  let C : Fin st.pivotRows.length → Fin M.numCols := finSel st.pivotCols hinv.len_eq hinv.col_dim
  have ⟨hΔ_eq, hBM_eq, hterm_rat, hzero⟩ := bareissInv_rat_bridge hinv M' S C
    (hM' := fun i j => (clearDenoms_toMatrix_apply M i j).symm)
  have hΔ : Matrix.pivotDet M' S C ≠ 0 :=
    hΔ_eq.symm ▸ Int.cast_ne_zero.mpr hinv.pivotDet_ne_zero
  have hterm : ∀ i : Fin M.numRows, (∀ a, S a ≠ i) →
      ∀ j : Fin M.numCols, Matrix.bareissMatrix M' S C i j = 0 :=
    fun i hi j => hterm_rat i hi j j.isLt
  have ⟨hSinj, _⟩ := Matrix.injective_of_pivotDet_ne_zero hΔ
  have hkm : st.pivotRows.length ≤ M.numRows :=
    nodup_length_le_of_lt hinv.row_nodup hinv.row_lt
  -- the reduced matrix: `rrefOfBareiss M' S C` with the pivot rows moved to the top
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun a : Fin st.pivotRows.length => (⟨a.val, a.isLt.trans_le hkm⟩ : Fin M.numRows)) S
    (fun a b hab => Fin.ext (congrArg (Fin.val : Fin M.numRows → ℕ) hab)) hSinj
  have ⟨hUpiv, hUrref⟩ := Matrix.isReducedRowEchelon_rrefOfBareiss hΔ
    (pairwise_lt_strictMono hinv.len_eq hinv.col_strict hinv.col_dim) hterm hzero σ hσ
  have hrref_eq : res.rref.toMatrix = (Matrix.rrefOfBareiss M' S C).submatrix σ id := by
    ext (i : Fin M.numRows) (j : Fin M.numCols)
    change res.rref.entry i.val j.val = Matrix.rrefOfBareiss M' S C (σ i) j
    rw [rationalElim_rref_entry M i.isLt j.isLt]
    split_ifs with hi
    · rw [← show S ⟨i.val, hi⟩ = σ i from (hσ ⟨i.val, hi⟩).symm]
      exact bareissInv_divInt_eq_rrefOfBareiss hΔ_eq hBM_eq (fun _ => rfl) ⟨i.val, hi⟩ j
    · have hnot : ∀ a, S a ≠ σ i := fun a ha => hi (by
        rw [← hσ a] at ha
        exact σ.injective ha ▸ a.isLt)
      change 0 = (Matrix.pivotDet M' S C)⁻¹ * Matrix.bareissMatrix M' S C (σ i) j
      rw [hterm (σ i) hnot j, mul_zero]
  have hspan_rref : span ℚ (Set.range res.rref.toMatrix) = span ℚ (Set.range M.toMatrix) := by
    rw [hrref_eq, ← span_row_rowScaled hd M.toMatrix, ← Matrix.span_row_rrefOfBareiss hΔ]
    exact congrArg (span ℚ) (σ.surjective.range_comp (Matrix.rrefOfBareiss M' S C))
  have hrank : res.rank = M.toMatrix.rank := by
    rw [← rank_rowScaled hd M.toMatrix]
    exact (Matrix.rank_eq_of_bareiss_terminal hΔ hterm).symm
  have hrow_li : LinearIndependent ℚ (fun a : Fin st.pivotRows.length => M.toMatrix (S a)) :=
    (LinearIndependent.units_smul_iff (R := ℚ)
      (fun a : Fin st.pivotRows.length => M.toMatrix (S a))
      (fun a => Units.mk0 (rowMultiplier M (S a) : ℚ) (hd (S a)))).mp
      (Matrix.linearIndependent_row_of_pivotDet_ne_zero hΔ)
  have hrow_span : span ℚ (Set.range fun a : Fin st.pivotRows.length => M.toMatrix (S a)) =
      span ℚ (Set.range M.toMatrix) := by
    rw [← span_rowSel_rowScaled hd M.toMatrix S, ← span_row_rowScaled hd M.toMatrix]
    exact Matrix.span_rowBasis_eq_of_bareiss_terminal hΔ hterm
  -- the kernel basis: one vector `kernelBasisVec M' S C j` per non-pivot column `j`
  have hnonPiv_len : res.nonPivotCols.length = M.numCols - res.rank :=
    (length_computeNonPivotCols (hinv.col_strict.imp Nat.ne_of_lt) hinv.col_dim).trans
      (congrArg _ hinv.len_eq.symm)
  have hker_len_np : res.kernelBasis.length = res.nonPivotCols.length := List.length_map _
  let kerEquiv : Fin res.kernelBasis.length ≃ { j : Fin M.numCols // ∀ a, C a ≠ j } :=
    ((finCongr hker_len_np).trans (List.Nodup.getEquiv res.nonPivotCols
      (List.nodup_range.filter _))).trans
      { toFun := fun c => ⟨⟨c.1, (mem_computeNonPivotCols.1 c.2).1⟩,
          forall_finSel_ne_iff.2 (mem_computeNonPivotCols.1 c.2).2⟩
        invFun := fun j =>
          ⟨j.1.val, mem_computeNonPivotCols.2 ⟨j.1.isLt, forall_finSel_ne_iff.1 j.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hker_vec : (fun idx : Fin res.kernelBasis.length =>
      (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) =
      (fun j : { j : Fin M.numCols // ∀ a, C a ≠ j } => Matrix.kernelBasisVec M' S C j.1) ∘
        kerEquiv := by
    ext idx c
    simp only [Function.comp_apply]
    have hidx : idx.val < res.nonPivotCols.length := hker_len_np ▸ idx.isLt
    have hker_val : (kerEquiv idx).1.val = res.nonPivotCols[idx.val]'hidx := List.get_eq_getElem
    rw [show res.kernelBasis[idx.val] = buildKernelVec st (res.nonPivotCols[idx.val]'hidx) from
      List.getElem_map _, buildKernelVec, List.getD_map_range _ 0 (hinv.dims.2.symm ▸ c.isLt),
      ← hker_val]
    simpa only [neg_one_mul] using
      bareissInv_find?_pivot_eq hinv hΔ_eq hBM_eq (C' := C) (j := (kerEquiv idx).1) c (-1)
        (fun a ha => by
          subst ha
          simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
          exact (Matrix.kernelBasisVec_pivot hΔ _ a).symm)
        (fun hnc => by
          rw [Matrix.kernelBasisVec_nonPivot S C _ c hnc]
          simp only [Fin.ext_iff])
  refine ⟨rationalElim_wellFormed M, by rw [hrref_eq]; exact hUrref,
    ⟨_, by rw [hrref_eq]; exact hUpiv⟩, hspan_rref, hrank, rfl, hinv.len_eq.symm, hnonPiv_len,
    hrow_li, hrow_span, hker_len_np.trans hnonPiv_len, ?_, ?_⟩
  · rw [hker_vec]
    exact (Matrix.linearIndependent_kernelBasisVec M' S C).comp kerEquiv kerEquiv.injective
  · rw [hker_vec, kerEquiv.surjective.range_comp, Matrix.span_kernelBasisVec hΔ hterm,
      ker_mulVecLin_rowScaled hd]

/-- Convenience projection: `ratRref M` is in Mathlib's `Matrix.IsReducedRowEchelon`. -/
theorem ratRref_isReducedRowEchelon (M : RatTable) :
    (ratRref M).toMatrix.IsReducedRowEchelon :=
  (rationalElim_spec M).2.1

/-- Convenience projection: `ratRank M = M.toMatrix.rank`. -/
theorem ratRank_eq (M : RatTable) : ratRank M = M.toMatrix.rank :=
  (rationalElim_spec M).2.2.2.2.1

theorem augmentRatTable_toMatrix_apply (A : RatTable) (b : List ℚ)
    (i : Fin (augmentRatTable A b).numRows) (j : Fin (augmentRatTable A b).numCols) :
    (augmentRatTable A b).toMatrix i j =
      if hj : j.val < A.numCols then A.toMatrix ⟨i.val, i.isLt⟩ ⟨j.val, hj⟩
      else b.getD i.val 0 := by
  rw [Cslib.RowTable.toMatrix_apply, Cslib.RowTable.entry]
  dsimp only [augmentRatTable]
  rw [List.getD_map_range (n := A.numRows) _ [] i.isLt]
  have hlen : (normalizedRatRow A i.val).length = A.numCols := by simp [normalizedRatRow]
  split_ifs with hj
  · rw [List.getD_append _ _ _ _ (hlen.symm ▸ hj)]
    exact List.getD_map_range _ 0 hj
  · have hjlt : j.val < A.numCols + 1 := j.isLt
    rw [show j.val = (normalizedRatRow A i.val).length by omega, List.getD_append_cons_length]

/-- Selecting only original columns of `[A | b]` gives the corresponding submatrix of `A`. -/
private theorem augmentCol_submatrix_castSucc {m n k₁ k₂ : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (R : Fin k₁ → Fin m) (C : Fin k₂ → Fin n) :
    (Matrix.augmentCol A b).submatrix R (Fin.castSucc ∘ C) = A.submatrix R C := by
  ext u v
  simp [Matrix.augmentCol]

/-- Soundness and completeness of `ratSolve sys` with respect to `sys.matrix.toMatrix *ᵥ x = b`. -/
theorem ratSolve_spec (sys : LinearSystemInput) :
    let A := sys.matrix
    let b : Fin A.numRows → ℚ := fun i => sys.rhs.getD i.val 0
    let res := ratSolve sys
    (∀ x, res.solution = some x →
      x.length = A.numCols ∧ A.toMatrix *ᵥ (fun j : Fin A.numCols => x.getD j.val 0) = b) ∧
    (res.solution = none ↔ ¬ ∃ x : Fin A.numCols → ℚ, A.toMatrix *ᵥ x = b) := by
  intro A b res
  set augRat := augmentRatTable A sys.rhs
  set st := bareissElimCols (clearDenoms augRat) A.numCols
  have hinv := bareissElimCols_inv (clearDenoms_wellFormed augRat) (colLimit := A.numCols)
    (Nat.le_succ _)
  have hd : ∀ i : Fin A.numRows, (rowMultiplier augRat ⟨i.val, i.isLt⟩ : ℚ) ≠ 0 := fun i =>
    Nat.cast_ne_zero.mpr (rowMultiplier_pos augRat ⟨i.val, i.isLt⟩).ne'
  -- the scaled system `A' x = b'`, its augmented matrix `M'`, and the pivot selections
  let A' : Matrix (Fin A.numRows) (Fin A.numCols) ℚ :=
    rowScaled (fun i => (rowMultiplier augRat ⟨i.val, i.isLt⟩ : ℚ)) A.toMatrix
  let b' : Fin A.numRows → ℚ := fun i => (rowMultiplier augRat ⟨i.val, i.isLt⟩ : ℚ) * b i
  let M' : Matrix (Fin A.numRows) (Fin (A.numCols + 1)) ℚ := Matrix.augmentCol A' b'
  let S : Fin st.pivotRows.length → Fin A.numRows := finSel st.pivotRows rfl hinv.row_lt
  let Caug : Fin st.pivotRows.length → Fin (A.numCols + 1) :=
    finSel st.pivotCols hinv.len_eq hinv.col_dim
  let C_A : Fin st.pivotRows.length → Fin A.numCols :=
    finSel st.pivotCols hinv.len_eq hinv.col_lt
  have hCaug_eq : Caug = Fin.castSucc ∘ C_A := rfl
  have ⟨hΔ_eq, hBM_eq, hterm_rat, _⟩ := bareissInv_rat_bridge hinv M' S Caug
    (hM' := fun i j => by
      refine Eq.trans ?_ (clearDenoms_toMatrix_apply augRat ⟨i.val, i.isLt⟩ ⟨j.val, j.isLt⟩).symm
      rw [augmentRatTable_toMatrix_apply]
      refine Fin.lastCases ?_ (fun k => ?_) j <;>
        simp [M', A', b', b, Matrix.augmentCol, rowScaled])
  have hΔ_A : Matrix.pivotDet A' S C_A ≠ 0 := by
    have h : Matrix.pivotDet M' S Caug ≠ 0 :=
      hΔ_eq.symm ▸ Int.cast_ne_zero.mpr hinv.pivotDet_ne_zero
    rwa [Matrix.pivotDet, hCaug_eq, augmentCol_submatrix_castSucc] at h
  have hterm_A : ∀ i : Fin A.numRows, (∀ a, S a ≠ i) →
      ∀ j : Fin A.numCols, Matrix.bareissMatrix A' S C_A i j = 0 := fun i hi j => by
    rw [Matrix.bareissMatrix_nonPivot A' C_A hi j, ← augmentCol_submatrix_castSucc A' b',
      Fin.comp_snoc]
    exact (Matrix.bareissMatrix_nonPivot M' Caug hi j.castSucc).symm.trans
      (hterm_rat i hi j.castSucc j.isLt)
  have haug_res := Matrix.rrefOfBareiss_augmentCol hΔ_A hterm_A b'
  have hsolve_iff : ∀ x, A' *ᵥ x = b' ↔ A.toMatrix *ᵥ x = b := fun x =>
    rowScaled_mulVec_eq_iff hd A.toMatrix x b
  -- the consistency test reads the last column on the unpivoted rows
  let consistent := (List.range A.numRows).all fun r =>
    st.pivotRows.contains r || decide (st.table.entry r A.numCols = 0)
  have hcons_iff : consistent = true ↔
      ∀ i : Fin A.numRows, (∀ a, S a ≠ i) →
        Matrix.bareissMatrix M' S Caug i (Fin.last A.numCols) = 0 := by
    simp only [consistent, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      List.contains_eq_mem, decide_eq_true_eq, hBM_eq, Fin.val_last, Int.cast_eq_zero,
      show ∀ i, (∀ a, S a ≠ i) ↔ i.val ∉ st.pivotRows from fun i => forall_finSel_ne_iff,
      Fin.forall_iff, or_iff_not_imp_left, st]
  have hsolved : consistent = true → A.toMatrix *ᵥ Matrix.solveVec A' S C_A b' = b := fun h =>
    (hsolve_iff _).mp (haug_res.2.mpr (hcons_iff.mp h))
  have hcons_of : (∃ x, A.toMatrix *ᵥ x = b) → consistent = true := fun ⟨x, hx⟩ =>
    hcons_iff.mpr (haug_res.2.mp ((Matrix.mulVec_solveVec_eq_iff_exists_mulVec_eq hΔ_A hterm_A
      b').mpr ⟨x, (hsolve_iff x).mpr hx⟩))
  -- the returned list is the canonical solution vector
  let x₀ : List ℚ := (List.range A.numCols).map fun c =>
    match (st.pivotRows.zip st.pivotCols).find? (fun pc => pc.2 == c) with
    | some (p, _) => Rat.divInt (st.table.entry p A.numCols) st.pivotDet
    | none => 0
  have hvec : (fun j : Fin A.numCols => x₀.getD j.val 0) = Matrix.solveVec A' S C_A b' := by
    ext c
    rw [List.getD_map_range _ 0 c.isLt]
    simpa only [one_mul, Fin.val_last] using
      bareissInv_find?_pivot_eq hinv hΔ_eq hBM_eq (C' := C_A) (j := Fin.last A.numCols) c 1
        (fun a ha => by
          subst ha
          simp only [Int.cast_one, one_mul, M']
          rw [hCaug_eq]
          exact haug_res.1 a)
        (fun hnc => (Matrix.solveVec_nonPivot A' S C_A b' hnc).symm)
  have hres : res.solution = if consistent = true then some x₀ else none :=
    apply_ite LinearSolveResult.solution _ _ _
  rw [hres]
  refine ⟨fun x hx => ?_, ?_⟩
  · split_ifs at hx with hcons
    obtain rfl := Option.some.inj hx
    exact ⟨by simp [x₀], by rw [hvec]; exact hsolved hcons⟩
  · split_ifs with hcons
    · exact ⟨False.elim, fun h => h ⟨_, hsolved hcons⟩⟩
    · exact ⟨fun _ hex => hcons (hcons_of hex), fun _ => rfl⟩

end ScaleAndCorrectness

/-! ### Bit-length and magnitude bounds -/

/-- Uniform Hadamard/factorial upper bound `(min m n + 1)! * (B + 1) ^ (min m n + 1)`. -/
@[expose] def stageEntryBound (m n B : ℕ) : ℕ :=
  (min m n + 1).factorial * (B + 1) ^ (min m n + 1)

theorem one_le_stageEntryBound (m n B : ℕ) : 1 ≤ stageEntryBound m n B :=
  Nat.mul_pos (Nat.factorial_pos _) (Nat.pow_pos (Nat.succ_pos B))

theorem stageEntryBound_mono_left {m n₁ n₂ B : ℕ} (h : n₁ ≤ n₂) :
    stageEntryBound m n₁ B ≤ stageEntryBound m n₂ B := by
  have hmin : min m n₁ + 1 ≤ min m n₂ + 1 := by omega
  exact Nat.mul_le_mul (Nat.factorial_le hmin) (Nat.pow_le_pow_right B.succ_pos hmin)

theorem size_stageEntryBound_le (m n B : ℕ) :
    (stageEntryBound m n B).size ≤
      (min m n + 1) * ((min m n + 1).size + (B + 1).size) + 2 := by
  unfold stageEntryBound
  have h1 := Nat.size_mul_le ((min m n + 1).factorial) ((B + 1) ^ (min m n + 1))
  have h2 := Nat.size_factorial_le (min m n + 1)
  have h3 := Nat.size_pow_le (B + 1) (min m n + 1)
  rw [Nat.mul_add]
  omega

theorem bareissInv_pivotRows_length_le {T : IntTable} {c : ℕ} {st : BareissState}
    (hinv : BareissInv T c st) : st.pivotRows.length ≤ min T.numRows T.numCols :=
  Nat.le_min.mpr
    ⟨nodup_length_le_of_lt hinv.row_nodup hinv.row_lt,
      hinv.len_eq ▸ nodup_length_le_of_lt
        (List.Pairwise.imp (fun h => Nat.ne_of_lt h) hinv.col_strict) hinv.col_dim⟩

/-- Every entry and pivot determinant in any state satisfying `BareissInv T c st` is bounded in
magnitude by `stageEntryBound T.numRows T.numCols B`. -/
theorem bareissInv_entry_bound {T : IntTable} {c : ℕ} {st : BareissState}
    (hinv : BareissInv T c st) {B : ℕ} (hB : ∀ i : Fin T.numRows, ∀ j : Fin T.numCols,
      |T.toMatrix i j| ≤ B) :
    (∀ i : Fin T.numRows, ∀ j : Fin T.numCols,
      |st.table.entry i.val j.val| ≤ (stageEntryBound T.numRows T.numCols B : ℤ)) ∧
      |st.pivotDet| ≤ (stageEntryBound T.numRows T.numCols B : ℤ) := by
  have hk_le := bareissInv_pivotRows_length_le hinv
  have hS_inj : Function.Injective (finSel st.pivotRows rfl hinv.row_lt) := fun _ _ ha =>
    List.nodup_iff_injective_getElem.mp hinv.row_nodup (congrArg Fin.val ha)
  have hmono : ((st.pivotRows.length + 1).factorial * (B + 1) ^ (st.pivotRows.length + 1) : ℕ) ≤
      stageEntryBound T.numRows T.numCols B :=
    Nat.mul_le_mul (Nat.factorial_le (Nat.add_le_add_right hk_le 1))
      (Nat.pow_le_pow_right B.succ_pos (Nat.add_le_add_right hk_le 1))
  refine ⟨fun i j => ?_, ?_⟩
  · rw [hinv.table_eq i j]
    exact (Matrix.abs_bareissMatrix_le T.toMatrix hB hS_inj _ i j).trans (Int.ofNat_le.mpr hmono)
  · rw [hinv.pivotDet_eq]
    refine (Matrix.abs_pivotDet_le T.toMatrix hB _ _).trans (Int.ofNat_le.mpr (le_trans ?_ hmono))
    exact Nat.mul_le_mul (Nat.factorial_le (Nat.le_succ _))
      ((Nat.pow_le_pow_left (Nat.le_succ B) _).trans
        (Nat.pow_le_pow_right B.succ_pos (Nat.le_succ _)))

private theorem divInt_bounds_of_le {a Δ : ℤ} {M : ℕ} (hΔ : Δ ≠ 0)
    (ha : |a| ≤ (M : ℤ)) (hΔle : |Δ| ≤ (M : ℤ)) :
    (Rat.divInt a Δ).num.natAbs ≤ M ∧ (Rat.divInt a Δ).den ≤ M := by
  have ha' : a.natAbs ≤ M := Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using ha)
  have hΔ' : Δ.natAbs ≤ M := Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using hΔle)
  exact ⟨(Rat.natAbs_num_divInt_le a Δ hΔ).trans ha', (Rat.den_divInt_le a Δ hΔ).trans hΔ'⟩

private theorem find?_zip_divInt_bounds {T : IntTable} {colLimit : ℕ} {st : BareissState}
    (hinv : BareissInv T colLimit st) {M : ℕ}
    (hbd : (∀ i : Fin T.numRows, ∀ j : Fin T.numCols, |st.table.entry i.val j.val| ≤ (M : ℤ)) ∧
      |st.pivotDet| ≤ (M : ℤ))
    {c : ℕ} {j : Fin T.numCols} (sgn : ℤ) (hsgn : |sgn| = 1) {d : ℚ}
    (hd : d.num.natAbs ≤ M ∧ d.den ≤ M) :
    let q : ℚ := match (st.pivotRows.zip st.pivotCols).find? (fun pc : ℕ × ℕ => pc.2 == c) with
      | some (p, _) => Rat.divInt (sgn * st.table.entry p j.val) st.pivotDet
      | none => d
    q.num.natAbs ≤ M ∧ q.den ≤ M := by
  dsimp only
  rcases hmatch : (st.pivotRows.zip st.pivotCols).find? (fun pc : ℕ × ℕ => pc.2 == c) with
    _ | ⟨p, y⟩
  · exact hd
  · refine divInt_bounds_of_le hinv.pivotDet_ne_zero ?_ hbd.2
    rw [abs_mul, hsgn, one_mul]
    exact hbd.1 ⟨p, hinv.row_lt p (List.of_mem_zip (List.mem_of_find?_eq_some hmatch)).1⟩ j

/-- Every rational entry produced in `(rationalElim M).rref` and `(rationalElim M).kernelBasis` has
magnitude and denominator bounded by `stageEntryBound M.numRows M.numCols (2^((n+1)*b))`. -/
theorem rationalElim_entry_bounds (M : RatTable) {b : ℕ}
    (hb : ∀ i : Fin M.numRows, ∀ j : Fin M.numCols,
      (M.toMatrix i j).num.natAbs ≤ 2 ^ b ∧ (M.toMatrix i j).den ≤ 2 ^ b) :
    let B := stageEntryBound M.numRows M.numCols (2 ^ ((M.numCols + 1) * b))
    (∀ r ∈ (rationalElim M).rref.rows, ∀ q ∈ r, q.num.natAbs ≤ B ∧ q.den ≤ B) ∧
      (∀ v ∈ (rationalElim M).kernelBasis, ∀ q ∈ v, q.num.natAbs ≤ B ∧ q.den ≤ B) := by
  intro B
  have hinv := bareissElim_inv (clearDenoms_wellFormed M)
  have hbd := bareissInv_entry_bound hinv (clearDenoms_abs_le M hb)
  have h1B : 1 ≤ B := one_le_stageEntryBound _ _ _
  constructor
  · intro r hr q hq
    simp only [rationalElim, List.mem_append, List.mem_map, List.mem_replicate] at hr
    rcases hr with ⟨p, hp, rfl⟩ | ⟨_, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      exact divInt_bounds_of_le hinv.pivotDet_ne_zero
        (hbd.1 ⟨p, hinv.row_lt p hp⟩ ⟨j, hinv.dims.2 ▸ List.mem_range.mp hj⟩) hbd.2
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hq
      simpa using h1B
  · intro v hv q hq
    simp only [rationalElim, List.mem_map] at hv
    obtain ⟨j, hj, rfl⟩ := hv
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
    simpa only [neg_one_mul] using find?_zip_divInt_bounds hinv (M := B) hbd (c := c)
      (j := ⟨j, (mem_computeNonPivotCols.1 hj).1⟩) (-1) (by decide)
      (d := if c = j then 1 else 0) (by split_ifs <;> simpa using h1B)

/-- Every entry of the canonical solution returned by `ratSolve sys` has numerator magnitude and
denominator bounded by `stageEntryBound m (n + 1) (2 ^ ((n + 2) * b))`. -/
theorem ratSolve_entry_bounds (sys : LinearSystemInput) {b : ℕ}
    (hbA : ∀ i : Fin sys.matrix.numRows, ∀ j : Fin sys.matrix.numCols,
      (sys.matrix.toMatrix i j).num.natAbs ≤ 2 ^ b ∧
      (sys.matrix.toMatrix i j).den ≤ 2 ^ b)
    (hb_rhs : ∀ i : Fin sys.matrix.numRows,
      (sys.rhs.getD i.val 0).num.natAbs ≤ 2 ^ b ∧ (sys.rhs.getD i.val 0).den ≤ 2 ^ b) :
    let B := stageEntryBound sys.matrix.numRows (sys.matrix.numCols + 1)
      (2 ^ ((sys.matrix.numCols + 2) * b))
    ∀ x, (ratSolve sys).solution = some x → ∀ q ∈ x, q.num.natAbs ≤ B ∧ q.den ≤ B := by
  intro B x hx q hq
  set augRat := augmentRatTable sys.matrix sys.rhs
  have hinv := bareissElimCols_inv (clearDenoms_wellFormed augRat)
    (colLimit := sys.matrix.numCols) (Nat.le_succ _)
  have hB_aug : ∀ i : Fin augRat.numRows, ∀ j : Fin augRat.numCols,
      (augRat.toMatrix i j).num.natAbs ≤ 2 ^ b ∧ (augRat.toMatrix i j).den ≤ 2 ^ b := fun i j => by
    rw [augmentRatTable_toMatrix_apply]
    split_ifs with hj
    exacts [hbA ⟨i.val, i.isLt⟩ ⟨j.val, hj⟩, hb_rhs ⟨i.val, i.isLt⟩]
  have hbd := bareissInv_entry_bound hinv (clearDenoms_abs_le augRat hB_aug)
  have h1B : 1 ≤ B := one_le_stageEntryBound _ _ _
  simp only [ratSolve] at hx
  split_ifs at hx with hcons
  cases hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hq
  simpa only [one_mul] using find?_zip_divInt_bounds hinv (M := B) hbd (c := c)
    (j := ⟨sys.matrix.numCols, Nat.lt_succ_self _⟩) 1 (by decide) (d := 0) (by simpa using h1B)

end Cslib.LinearAlgebra

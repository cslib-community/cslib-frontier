/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth, Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.GetD

/-!
# Polymorphic row-major runtime matrices (`Cslib.RowTable`)

`Cslib.RowTable α` represents a dense matrix of runtime dimensions `numRows × numCols` stored in
row-major order as `rows : List (List α)`. Out-of-bounds reads via `RowTable.entry` default to `0`,
making `RowTable.toMatrix` total on arbitrary (possibly ragged) tables while forming a two-sided
equivalence with `Matrix (Fin m) (Fin n) α` on `RowTable.WellFormed` tables.

## Main definitions

* `Cslib.RowTable`: explicit row-major matrix record `(numRows, numCols, rows)`.
* `Cslib.RowTable.WellFormed`: rectangular shape predicate (`rows.length = numRows` and each row
  has length `numCols`).
* `Cslib.RowTable.entry`: total `(i, j)` lookup defaulting to `0` out of bounds.
* `Cslib.RowTable.tabulate`: build a well-formed `m × n` `RowTable α` from `g : ℕ → ℕ → α`.
* `Cslib.RowTable.toMatrix`, `Cslib.RowTable.ofMatrix`: conversion between `RowTable α` and
  `Matrix (Fin m) (Fin n) α`.
* `Cslib.RowTable.map`: entrywise functorial map preserving dimensions and `WellFormed`.

## Main results

* `Cslib.RowTable.toMatrix_ofMatrix`, `Cslib.RowTable.ofMatrix_toMatrix`: round-trip equivalence
  between `Matrix (Fin m) (Fin n) α` and well-formed `RowTable α`.
* `Cslib.RowTable.toMatrix_map`, `Cslib.RowTable.map_ofMatrix`: `RowTable.map` commutes with
  `toMatrix` (for zero-preserving maps) and `ofMatrix`.
* `Cslib.RowTable.eq_of_wellFormed_of_entry_eq`, `Cslib.RowTable.tabulate_entry`: extensionality
  and canonical re-tabulation of well-formed tables.
-/

public section

namespace Cslib

/-- Explicit row-major matrix of runtime dimensions `numRows × numCols`. -/
@[ext]
structure RowTable (α : Type*) where
  /-- Declared number of rows. -/
  numRows : ℕ
  /-- Declared number of columns. -/
  numCols : ℕ
  /-- Row-major list of rows. -/
  rows : List (List α)
  deriving Repr, DecidableEq

namespace RowTable

/-! ### Rectangular shape invariant and functorial map -/

section Basic

variable {α β γ : Type*}

/-- Rectangular shape invariant: `T.rows` has `T.numRows` rows, each of length `T.numCols`. -/
@[expose] def WellFormed (T : RowTable α) : Prop :=
  T.rows.length = T.numRows ∧ ∀ r ∈ T.rows, r.length = T.numCols

instance instDecidableWellFormed (T : RowTable α) : Decidable T.WellFormed :=
  inferInstanceAs (Decidable (T.rows.length = T.numRows ∧ ∀ r ∈ T.rows, r.length = T.numCols))

/-- Entrywise map on a `RowTable`, preserving declared dimensions. -/
@[expose] def map (f : α → β) (T : RowTable α) : RowTable β :=
  ⟨T.numRows, T.numCols, T.rows.map (List.map f)⟩

/-- `map` preserves `numRows`. -/
@[simp] theorem numRows_map (f : α → β) (T : RowTable α) : (T.map f).numRows = T.numRows := rfl

/-- `map` preserves `numCols`. -/
@[simp] theorem numCols_map (f : α → β) (T : RowTable α) : (T.map f).numCols = T.numCols := rfl

/-- Rows of `T.map f`. -/
@[simp] theorem rows_map (f : α → β) (T : RowTable α) :
    (T.map f).rows = T.rows.map (List.map f) := rfl

/-- Mapping the identity function returns `T` unchanged. -/
@[simp] theorem map_id (T : RowTable α) : T.map id = T := by
  ext <;> simp [map]

/-- Composition law for `RowTable.map`. -/
theorem map_map (g : β → γ) (f : α → β) (T : RowTable α) :
    (T.map f).map g = T.map (g ∘ f) := by
  ext <;> simp [map, List.map_map]

/-- `map` preserves `WellFormed`. -/
theorem WellFormed.map {T : RowTable α} (hT : T.WellFormed) (f : α → β) :
    (T.map f).WellFormed :=
  ⟨by simp [hT.1], List.forall_mem_map.2 fun r₀ hr₀ => by simp [hT.2 r₀ hr₀]⟩

/-- Construct the `m × n` `RowTable` whose `(i, j)` entry is `g i j` for `i < m` and `j < n`. -/
@[expose] def tabulate (m n : ℕ) (g : ℕ → ℕ → α) : RowTable α :=
  ⟨m, n, (List.range m).map fun i => (List.range n).map fun j => g i j⟩

/-- `tabulate m n g` has `m` rows. -/
@[simp] theorem numRows_tabulate (m n : ℕ) (g : ℕ → ℕ → α) :
    (tabulate m n g).numRows = m := rfl

/-- `tabulate m n g` has `n` columns. -/
@[simp] theorem numCols_tabulate (m n : ℕ) (g : ℕ → ℕ → α) :
    (tabulate m n g).numCols = n := rfl

/-- Every row of `(tabulate m n g).rows` has length `n`. -/
theorem length_of_mem_rows_tabulate {m n : ℕ} {g : ℕ → ℕ → α} {row : List α}
    (hrow : row ∈ (tabulate m n g).rows) : row.length = n := by
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hrow
  simp

/-- Every tabulated `m × n` `RowTable` is `WellFormed`. -/
theorem wellFormed_tabulate (m n : ℕ) (g : ℕ → ℕ → α) : (tabulate m n g).WellFormed :=
  ⟨by simp [tabulate], fun _ hrow => length_of_mem_rows_tabulate hrow⟩

/-- Convert a `Matrix (Fin m) (Fin n) α` into an `m × n` `RowTable α`. -/
@[expose] def ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) α) : RowTable α :=
  ⟨m, n, List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => A i j⟩

/-- `ofMatrix A` has `m` rows. -/
@[simp] theorem numRows_ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) α) :
    (ofMatrix A).numRows = m := rfl

/-- `ofMatrix A` has `n` columns. -/
@[simp] theorem numCols_ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) α) :
    (ofMatrix A).numCols = n := rfl

/-- `ofMatrix A` is always `WellFormed`. -/
theorem wellFormed_ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) α) :
    (ofMatrix A).WellFormed := by
  refine ⟨by simp [ofMatrix], fun _ hr => ?_⟩
  obtain ⟨_, rfl⟩ := List.mem_ofFn.1 hr
  simp

/-- `map` commutes with `ofMatrix`. -/
@[simp] theorem map_ofMatrix {m n : ℕ} (f : α → β) (A : Matrix (Fin m) (Fin n) α) :
    (ofMatrix A).map f = ofMatrix (A.map f) :=
  RowTable.ext rfl rfl (by simp [map, ofMatrix, Function.comp_def])

end Basic

/-! ### Zero-defaulting entry lookup and `Matrix` conversion -/

section Zero

variable {α β : Type*} [Zero α]

/-- Entry `(i, j)` of `T`, defaulting to `0` out of bounds. -/
@[expose] def entry (T : RowTable α) (i j : ℕ) : α :=
  (T.rows.getD i []).getD j 0

/-- Interpret `T : RowTable α` as a `Matrix (Fin T.numRows) (Fin T.numCols) α`. -/
@[expose] def toMatrix (T : RowTable α) : Matrix (Fin T.numRows) (Fin T.numCols) α :=
  Matrix.of fun i j => T.entry i.val j.val

/-- Matrix application on `T.toMatrix` reads `T.entry`. -/
@[simp] theorem toMatrix_apply (T : RowTable α) (i : Fin T.numRows) (j : Fin T.numCols) :
    T.toMatrix i j = T.entry i.val j.val := rfl

/-- Entry lookup on `tabulate m n g` returns `g i j` in bounds and `0` out of bounds. -/
theorem entry_tabulate (m n : ℕ) (g : ℕ → ℕ → α) (i j : ℕ) :
    (tabulate m n g).entry i j = if i < m ∧ j < n then g i j else 0 := by
  by_cases hi : i < m <;> by_cases hj : j < n <;>
    simp [entry, tabulate, List.getD_eq_getElem?_getD, hi, hj]

/-- In-bounds entry lookup on `tabulate m n g`. -/
@[simp] theorem entry_tabulate_of_lt {m n : ℕ} (g : ℕ → ℕ → α) {i j : ℕ}
    (hi : i < m) (hj : j < n) :
    (tabulate m n g).entry i j = g i j := by
  rw [entry_tabulate, ite_eq_left ⟨hi, hj⟩]

/-- Matrix interpretation of `tabulate m n g`. -/
@[simp] theorem toMatrix_tabulate (m n : ℕ) (g : ℕ → ℕ → α) :
    (tabulate m n g).toMatrix = Matrix.of fun i j => g i.val j.val :=
  Matrix.ext fun i j => entry_tabulate_of_lt g i.isLt j.isLt

/-- In-bounds entry lookup on `ofMatrix A`. -/
@[simp] theorem entry_ofMatrix_of_lt {m n : ℕ} (A : Matrix (Fin m) (Fin n) α) {i j : ℕ}
    (hi : i < m) (hj : j < n) :
    (ofMatrix A).entry i j = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [entry, ofMatrix, List.getD_eq_getElem?_getD, hi, hj]

/-- Converting `A : Matrix (Fin m) (Fin n) α` to `RowTable α` and back recovers `A`. -/
@[simp] theorem toMatrix_ofMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) α) :
    (ofMatrix A).toMatrix = A :=
  Matrix.ext fun i j => entry_ofMatrix_of_lt A i.isLt j.isLt

/-- Out-of-bounds reads on a `WellFormed` table return `0`. -/
theorem WellFormed.entry_eq_zero {T : RowTable α} (hT : T.WellFormed) {i j : ℕ}
    (h : ¬(i < T.numRows ∧ j < T.numCols)) : T.entry i j = 0 := by
  unfold entry
  rcases Nat.lt_or_ge i T.rows.length with hi | hi
  · have := hT.1
    have := hT.2 _ (List.getElem_mem hi)
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_default _ _ (by omega)]
  · rw [List.getD_eq_default _ _ hi, List.getD_nil]

/-- Every stored element of `T.rows` occurs as `T.entry i j` at valid row/column indices. -/
theorem exists_entry_eq_of_mem {T : RowTable α} {row : List α} {x : α}
    (hrow : row ∈ T.rows) (hx : x ∈ row) :
    ∃ i j, i < T.rows.length ∧ j < row.length ∧ T.entry i j = x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  exact ⟨i, j, hi, hj, by simp [entry, List.getD_eq_getElem?_getD, hi, hj]⟩

/-- Any predicate holding for `0` and for every stored element of `T.rows` holds for every
`T.entry i j`. -/
theorem entry_rel_of_mem {P : α → Prop} (h0 : P 0) {T : RowTable α}
    (h : ∀ row ∈ T.rows, ∀ x ∈ row, P x) (i j : ℕ) : P (T.entry i j) := by
  unfold entry
  rcases Nat.lt_or_ge i T.rows.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    rcases Nat.lt_or_ge j T.rows[i].length with hj | hj
    · rw [List.getD_eq_getElem _ _ hj]
      exact h _ (List.getElem_mem hi) _ (List.getElem_mem hj)
    · rwa [List.getD_eq_default _ _ hj]
  · rwa [List.getD_eq_default _ _ hi, List.getD_nil]

/-- Two `WellFormed` tables of equal dimensions are equal when their in-bounds entries agree. -/
theorem eq_of_wellFormed_of_entry_eq {A B : RowTable α} (hA : A.WellFormed) (hB : B.WellFormed)
    (hr : A.numRows = B.numRows) (hc : A.numCols = B.numCols)
    (h : ∀ i < A.numRows, ∀ j < A.numCols, A.entry i j = B.entry i j) : A = B :=
  RowTable.ext hr hc <| List.ext_getElem (hA.1.trans (hr.trans hB.1.symm)) fun i hiA hiB =>
    have hlenA := hA.2 _ (List.getElem_mem hiA)
    List.ext_getElem (hlenA.trans (hc.trans (hB.2 _ (List.getElem_mem hiB)).symm))
      fun j hjA hjB => by
        simpa only [entry, List.getD_eq_getElem _ _ hiA, List.getD_eq_getElem _ _ hiB,
          List.getD_eq_getElem _ _ hjA, List.getD_eq_getElem _ _ hjB] using
          h i (hA.1 ▸ hiA) j (hlenA ▸ hjA)

/-- Re-tabulating a `WellFormed` table from `entry` recovers it unchanged. -/
theorem tabulate_entry {T : RowTable α} (hT : T.WellFormed) :
    tabulate T.numRows T.numCols T.entry = T :=
  eq_of_wellFormed_of_entry_eq (wellFormed_tabulate _ _ _) hT rfl rfl fun _ hi _ hj =>
    entry_tabulate_of_lt _ hi hj

/-- Converting a `WellFormed` table to a `Matrix` and back via `ofMatrix` recovers `T`. -/
theorem ofMatrix_toMatrix {T : RowTable α} (hT : T.WellFormed) :
    ofMatrix T.toMatrix = T :=
  eq_of_wellFormed_of_entry_eq (wellFormed_ofMatrix _) hT rfl rfl fun _ hi _ hj =>
    entry_ofMatrix_of_lt _ hi hj

/-- `entry` commutes with any zero-preserving map `f`. -/
@[simp] theorem entry_map [Zero β] (f : α → β) (hf : f 0 = 0) (T : RowTable α) (i j : ℕ) :
    (T.map f).entry i j = f (T.entry i j) := by
  simp only [entry, map, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases T.rows[i]? with
  | none => simpa using hf.symm
  | some row =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases row[j]? with
    | none => simpa using hf.symm
    | some _ => rfl

/-- `toMatrix` commutes with `Matrix.map` for any zero-preserving `f`. -/
@[simp] theorem toMatrix_map [Zero β] (f : α → β) (hf : f 0 = 0) (T : RowTable α) :
    (T.map f).toMatrix = T.toMatrix.map f :=
  Matrix.ext fun i j => entry_map f hf T i.val j.val

end Zero

end RowTable

end Cslib

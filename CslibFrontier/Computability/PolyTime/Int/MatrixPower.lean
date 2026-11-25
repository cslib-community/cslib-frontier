/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.Int.DotProduct
public import CslibFrontier.Computability.PolyTime.Int.Table
public import Mathlib.Data.Matrix.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Uniform polynomial-time integer matrix-power columns

`Cslib.IntTable.mulVec` multiplies a stored integer row table by a stored integer vector.
Its dimension is the number of rows: short rows and vectors are padded by zero, and entries
past that dimension are ignored. The operation is total on ragged tables.

`Cslib.IntTable.powerColumn` starts with a standard basis vector and stores the complete vector
after each multiplication. Its native multitape polynomial-time certificate is uniform in the
table, unary iteration count, and unary seed index. Matrix and vector entries use signed binary.
No bound on the dimension or the matrix entries is assumed. The proof bounds every intermediate
coordinate's magnitude length by `1 + steps * (entryBits + dimension.size)` and uses the native
bounded-iteration rule. Thus exponentially large integer magnitudes do not become unary data.

## Main results

* `Cslib.IntTable.size_getD_powerColumn_le`: linear growth of coordinate bit lengths.
* `Cslib.IntTable.powerColumn_ofFn`: agreement with ordinary finite matrix powers.
* `Cslib.IntTable.computableInPolyTime_mulVec`: uniform native matrix-vector multiplication.
* `Cslib.IntTable.computableInPolyTime_powerColumn`: uniform native matrix-power columns.
-/

public section

namespace Cslib.IntTable

open Mathlib.Tactic.Matrix Turing.MultiTapeTM

/-- Multiply a stored row table by a stored vector, using the row count as the dimension.
Missing entries read as zero and coordinates past that dimension are ignored. -/
@[expose] def mulVec (rows : List (List ℤ)) (v : List ℤ) : List ℤ :=
  rows.map fun row => ListMatrix.dotProduct rows.length row v

/-- Iterate stored matrix-vector multiplication from the indicated standard basis vector.
An out-of-bounds seed gives the zero vector. -/
@[expose] def powerColumn (rows : List (List ℤ)) (steps seed : ℕ) : List ℤ :=
  (mulVec rows)^[steps] ((List.range rows.length).map fun j => if j = seed then 1 else 0)

/-- Matrix-vector multiplication returns one coordinate for every stored row. -/
@[simp] theorem length_mulVec (rows : List (List ℤ)) (v : List ℤ) :
    (mulVec rows v).length = rows.length := by
  simp only [mulVec, List.length_map]

/-- Each iteration is one multiplication of the previously stored vector. -/
theorem powerColumn_succ (rows : List (List ℤ)) (steps seed : ℕ) :
    powerColumn rows (steps + 1) seed = mulVec rows (powerColumn rows steps seed) :=
  Function.iterate_succ_apply' ..

/-- Every stored power column has the dimension of the table. -/
@[simp] theorem length_powerColumn (rows : List (List ℤ)) (steps seed : ℕ) :
    (powerColumn rows steps seed).length = rows.length := by
  cases steps with
  | zero => simp [powerColumn]
  | succ steps => rw [powerColumn_succ, length_mulVec]

/-- On tabulated square matrices and vectors, stored multiplication agrees with the usual
finite-coordinate sum. -/
theorem mulVec_ofFn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) :
    mulVec (List.ofFn fun i => List.ofFn (M i)) (List.ofFn v) =
      List.ofFn fun i => ∑ j : Fin n, M i j * v j := by
  simp only [mulVec, List.length_ofFn, List.map_ofFn, Function.comp_def,
    ListMatrix.dotProduct_ofFn]

/-- Tabulating a finite matrix and computing a stored power column agrees with the
corresponding column of its ordinary matrix power. -/
theorem powerColumn_ofFn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (steps : ℕ) (i : Fin n) :
    powerColumn (List.ofFn fun j => List.ofFn (M j)) steps i.val =
      List.ofFn fun j => (M ^ steps) j i := by
  induction steps with
  | zero =>
    simp only [powerColumn, Function.iterate_zero, id_eq, List.length_ofFn,
      List.map_range_eq_ofFn, pow_zero, Matrix.one_apply, Fin.ext_iff]
  | succ steps ih =>
    rw [powerColumn_succ, ih, mulVec_ofFn]
    simp only [pow_succ', Matrix.mul_apply]

private theorem size_getD_le {v : List ℤ} {b : ℕ}
    (h : ∀ z ∈ v, z.natAbs.size ≤ b) (i : ℕ) : (v.getD i 0).natAbs.size ≤ b := by
  rcases List.getD_mem_or v i 0 with hi | hi
  · exact h _ hi
  · rw [hi]
    simp

private theorem size_dotProduct_le {a v : List ℤ} {b c : ℕ}
    (ha : ∀ z ∈ a, z.natAbs.size ≤ b) (hv : ∀ z ∈ v, z.natAbs.size ≤ c) (n : ℕ) :
    (ListMatrix.dotProduct n a v).natAbs.size ≤ b + c + n.size := by
  rw [ListMatrix.dotProduct_eq_sum_map_range]
  have h := Int.size_natAbs_sum_le (b := b + c) (l :=
    (List.range n).map fun i => a.getD i 0 * v.getD i 0) (by
      intro z hz
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz
      exact (Int.size_natAbs_mul_le _ _).trans
        (Nat.add_le_add (size_getD_le ha i) (size_getD_le hv i)))
  simpa only [List.length_map, List.length_range] using h

private theorem size_of_mem_powerColumn_le {rows : List (List ℤ)} {b : ℕ}
    (hrows : ∀ row ∈ rows, ∀ z ∈ row, z.natAbs.size ≤ b) (steps seed : ℕ) :
    ∀ z ∈ powerColumn rows steps seed,
      z.natAbs.size ≤ 1 + steps * (b + rows.length.size) := by
  induction steps with
  | zero =>
    intro z hz
    simp only [powerColumn, Function.iterate_zero, id_eq, List.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    split <;> simp
  | succ steps ih =>
    intro z hz
    rw [powerColumn_succ] at hz
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hz
    have h := size_dotProduct_le (hrows row hrow) ih rows.length
    exact h.trans_eq (by ring)

/-- With at most `b` magnitude bits per matrix entry, each stored coordinate has at most
`1 + steps * (b + dimension.size)` magnitude bits. This also bounds defaulted reads. -/
theorem size_getD_powerColumn_le {rows : List (List ℤ)} {b : ℕ}
    (hrows : ∀ row ∈ rows, ∀ z ∈ row, z.natAbs.size ≤ b) (steps seed i : ℕ) :
    ((powerColumn rows steps seed).getD i 0).natAbs.size ≤
      1 + steps * (b + rows.length.size) :=
  size_getD_le (size_of_mem_powerColumn_le hrows steps seed) i

private theorem length_enc_powerColumn_le {rows : List (List ℤ)} {b : ℕ}
    (hrows : ∀ row ∈ rows, ∀ z ∈ row, z.natAbs.size ≤ b) (steps seed : ℕ) :
    (encList encIntBin (powerColumn rows steps seed)).length ≤
      rows.length * (2 * (1 + steps * (b + rows.length.size)) + 3) := by
  have h := length_encList_le encIntBin (powerColumn rows steps seed)
    (b := 1 + steps * (b + rows.length.size) + 1) (by
      intro z hz
      rw [length_encIntBin]
      exact Nat.add_le_add_right (size_of_mem_powerColumn_le hrows steps seed z hz) 1)
  simpa only [length_powerColumn, show ∀ a : ℕ, 2 * (a + 1) + 1 = 2 * a + 3 by omega]
    using h

/-- Multiply a uniformly computed binary-integer row table and vector in native polynomial
time. The dimension is the runtime row count; no rectangularity premise is required. -/
@[fun_prop] theorem computableInPolyTime_mulVec {α : Type} {encIn : α ↪ List Bool}
    {rows : α → List (List ℤ)} {v : α → List ℤ}
    (hrows : ComputableInPolyTime rows encIn encIntTable)
    (hv : ComputableInPolyTime v encIn (encList encIntBin)) :
    ComputableInPolyTime (fun x => mulVec (rows x) (v x)) encIn (encList encIntBin) := by
  unfold mulVec
  apply ComputableInPolyTime.mapWithInput hrows
  exact ComputableInPolyTime.listDotProduct.comp
    (show ComputableInPolyTime
      (fun p : α × List ℤ => ((rows p.1).length, p.2, v p.1))
      (encPair encIn (encList encIntBin))
      (encPair encUnary (encPair (encList encIntBin) (encList encIntBin))) by fun_prop)

/-- Compute stored integer matrix-power columns in native polynomial time, uniformly in the
binary-integer table and the unary step count and seed index. -/
@[fun_prop] theorem computableInPolyTime_powerColumn {α : Type} {encIn : α ↪ List Bool}
    {rows : α → List (List ℤ)} {steps seed : α → ℕ}
    (hrows : ComputableInPolyTime rows encIn encIntTable)
    (hsteps : ComputableInPolyTime steps encIn encUnary)
    (hseed : ComputableInPolyTime seed encIn encUnary) :
    ComputableInPolyTime (fun x => powerColumn (rows x) (steps x) (seed x))
      encIn (encList encIntBin) := by
  have hdim := (ComputableInPolyTime.length_list (encList encIntBin)).comp hrows
  have hdimBound := hdim.polyBounded
  have htableBound := hrows.polyBounded_length
  have hstepsBound := hsteps.polyBounded
  unfold powerColumn
  apply ComputableInPolyTime.iterateWith (encPar := encIntTable) hrows hsteps
    (by fun_prop) (by fun_prop)
    (bound := fun x => (rows x).length *
      (2 * (1 + steps x * ((encIntTable (rows x)).length + (rows x).length)) + 3))
  · exact hdimBound.mul
      (((PolyBounded.const 2).mul
        ((PolyBounded.const 1).add (hstepsBound.mul (htableBound.add hdimBound)))).add (.const 3))
  · intro x i hi
    have hentry : ∀ row ∈ rows x, ∀ z ∈ row,
        z.natAbs.size ≤ (encIntTable (rows x)).length := by
      intro row hrow z hz
      have h₁ : (encIntBin z).length ≤ (encList encIntBin row).length :=
        SizedListEncoding.length_elem_le row z hz
      have h₂ : (encList encIntBin row).length ≤ (encIntTable (rows x)).length :=
        SizedListEncoding.length_elem_le (rows x) row hrow
      have h := h₁.trans h₂
      rw [length_encIntBin] at h
      omega
    apply (length_enc_powerColumn_le hentry i (seed x)).trans
    gcongr
    exact Nat.size_le_self _

end Cslib.IntTable

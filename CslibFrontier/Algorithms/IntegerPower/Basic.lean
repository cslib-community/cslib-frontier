/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Nat.BinarySize
public import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.FinRange

/-!
# Materialized integer matrix-power search

`powerColumnVector M s i` computes `M ^ s` applied to the `i`-th standard basis vector.
Each multiplication first computes the previous column and then fills a new array-backed
`Vector`. Thus later coordinate reads access stored entries of that column.

The getter theorem identifies this computation with the mathematical matrix power. If every
matrix entry has absolute value at most one, an entry after `s` multiplications has absolute
value at most `n ^ s`, hence at most `s * n.size + 1` magnitude bits. These are correctness and
integer-size guarantees. The uniform native machine realization is supplied by
`Cslib.IntTable.powerColumn` in `CslibFrontier.Computability.PolyTime.Int.MatrixPower`;
the complete growth-search program and its agreement with this implementation are in `Program`.
The finite search checks every basis seed and the first `n + 1` powers, returning the first
nonzero next iterate whose squared norm has the required growth.

## Main definitions

* `Cslib.Algorithms.IntegerPower.powerColumnVector`: materialized matrix-vector iteration.
* `Cslib.Algorithms.IntegerPower.growingColumn?`: finite search using exact integer comparisons.
* `Cslib.Algorithms.IntegerPower.recoveredVector`: the selected next iterate, with a zero fallback.

## Main results

* `Cslib.Algorithms.IntegerPower.getElem_powerColumnVector`: agreement with a matrix-power column.
* `Cslib.Algorithms.IntegerPower.natAbs_powerColumnVector_le`: the entry magnitude bound.
* `Cslib.Algorithms.IntegerPower.size_powerColumnVector_le`: the binary magnitude-size bound.
-/

public section

namespace Cslib.Algorithms.IntegerPower

open Finset Matrix

variable {n : ℕ}

/-- Compute a power column by storing the entire column after each matrix multiplication. -/
@[expose] def powerColumnVector (M : Matrix (Fin n) (Fin n) ℤ) : ℕ → Fin n → Vector ℤ n
  | 0, i => Vector.ofFn fun j => if j = i then 1 else 0
  | s + 1, i =>
    let v := powerColumnVector M s i
    Vector.ofFn fun j => ∑ l : Fin n, M j l * v[l.1]

/-- Reading a stored power-column entry agrees with the corresponding matrix-power entry. -/
@[simp]
theorem getElem_powerColumnVector (M : Matrix (Fin n) (Fin n) ℤ) (s : ℕ)
    (i j : Fin n) : (powerColumnVector M s i)[j.1] = (M ^ s) j i := by
  induction s generalizing j with
  | zero => simp [powerColumnVector, Matrix.one_apply]
  | succ s ih =>
    simp only [powerColumnVector, Vector.getElem_ofFn, ih, pow_succ', Matrix.mul_apply]

/-- If all matrix entries have magnitude at most one, each multiplication grows the largest
entry magnitude by at most a factor of the dimension. -/
theorem natAbs_powerColumnVector_le (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ j l, (M j l).natAbs ≤ 1) (s : ℕ) (i j : Fin n) :
    ((powerColumnVector M s i)[j]).natAbs ≤ n ^ s := by
  change ((powerColumnVector M s i)[j.1]).natAbs ≤ n ^ s
  induction s generalizing j with
  | zero =>
    simp only [powerColumnVector, Vector.getElem_ofFn, pow_zero]
    split <;> simp
  | succ s ih =>
    simp only [powerColumnVector, Vector.getElem_ofFn]
    calc (∑ l : Fin n, M j l * (powerColumnVector M s i)[l.1]).natAbs
        ≤ ∑ l : Fin n, (M j l * (powerColumnVector M s i)[l.1]).natAbs :=
          Int.natAbs_sum_le _ _
      _ ≤ ∑ _l : Fin n, n ^ s := by
        refine sum_le_sum fun l _ => ?_
        rw [Int.natAbs_mul]
        exact (Nat.mul_le_mul (hM j l) (ih l)).trans_eq (one_mul _)
      _ = n ^ (s + 1) := by simp [pow_succ']

/-- The magnitude of each stored power-column entry uses at most `s * n.size + 1` binary digits.
An additional sign bit suffices to encode the corresponding integer. -/
theorem size_powerColumnVector_le (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ j l, (M j l).natAbs ≤ 1) (s : ℕ) (i j : Fin n) :
    ((powerColumnVector M s i)[j]).natAbs.size ≤ s * n.size + 1 :=
  (Nat.size_le_size (natAbs_powerColumnVector_le M hM s i j)).trans (Nat.size_pow_le n s)

/-- The seed and number of multiplications specifying a power column. -/
structure PowerColumn (n : ℕ) where
  /-- The number of multiplications before testing growth. -/
  steps : ℕ
  /-- The standard-basis vector from which this orbit starts. -/
  seed : Fin n
  deriving DecidableEq

/-- A column of an integer matrix power. -/
@[expose] def powerVector (M : Matrix (Fin n) (Fin n) ℤ) (s : ℕ) (i : Fin n) : Fin n → ℤ :=
  let v := powerColumnVector M s i
  fun j => v[j]

/-- The stored integer iteration computes the corresponding matrix-power column. -/
@[simp] theorem powerVector_apply (M : Matrix (Fin n) (Fin n) ℤ) (s : ℕ) (i j : Fin n) :
    powerVector M s i j = (M ^ s) j i :=
  getElem_powerColumnVector M s i j

/-- Test nonzero growth by comparing integer squared norms, without division. -/
@[expose] def grows (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (c : PowerColumn n) : Bool :=
  let v := powerVector M c.steps c.seed
  let w := powerVector M (c.steps + 1) c.seed
  decide (0 < dotProduct w w ∧ (k : ℤ) ^ 2 * dotProduct v v ≤ 4 * dotProduct w w)

/-- Search every basis orbit through its first `n + 1` multiplications. -/
@[expose] def powerColumns (n : ℕ) : List (PowerColumn n) :=
  (List.range (n + 1)).flatMap fun s => (List.finRange n).map fun i => ⟨s, i⟩

/-- The first growing column, in step order and then vertex order. -/
@[expose] def growingColumn? (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Option (PowerColumn n) :=
  (powerColumns n).find? (grows M k)

/-- The selected nonzero next iterate, or the zero vector if the search fails. -/
@[expose] def recoveredVector (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Fin n → ℤ :=
  match growingColumn? M k with
  | none => 0
  | some c => powerVector M (c.steps + 1) c.seed

/-- Every eligible seed and step occurs in the search. -/
theorem mem_powerColumns (c : PowerColumn n) : c ∈ powerColumns n ↔ c.steps < n + 1 := by
  rcases c with ⟨s, i⟩
  simp [powerColumns]

/-- The search examines at most a quadratic number of seed-step pairs. -/
theorem length_powerColumns (n : ℕ) : (powerColumns n).length = (n + 1) * n := by
  simp [powerColumns, List.length_flatMap]

/-- The finite search succeeds whenever a growing column occurs in its range. -/
theorem growingColumn?_isSome (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ)
    (h : ∃ c : PowerColumn n, c.steps < n + 1 ∧ grows M k c) :
    (growingColumn? M k).isSome := by
  rw [growingColumn?, List.find?_isSome]
  obtain ⟨c, hs, hc⟩ := h
  exact ⟨c, (mem_powerColumns c).mpr hs, hc⟩

/-- A successful search returns a candidate in range satisfying the exact growth test. -/
theorem growingColumn?_spec (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) {c : PowerColumn n}
    (h : growingColumn? M k = some c) : c.steps < n + 1 ∧ grows M k c :=
  ⟨(mem_powerColumns c).mp (List.mem_of_find?_eq_some h), List.find?_some h⟩

/-- The vector returned by the bounded search uses only a polynomial number of magnitude bits
per coordinate. This is an integer-size bound, separate from a machine-time certificate. -/
theorem size_recoveredVector_le (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i j, (M i j).natAbs ≤ 1) (k : ℕ) (j : Fin n) :
    (recoveredVector M k j).natAbs.size ≤ (n + 1) * n.size + 1 := by
  cases hc : growingColumn? M k with
  | none => simp [recoveredVector, hc]
  | some c =>
    have hs := (growingColumn?_spec M k hc).1
    have hsize := size_powerColumnVector_le M hM (c.steps + 1) c.seed j
    have hbound : (c.steps + 1) * n.size + 1 ≤ (n + 1) * n.size + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right n.size (by omega)) 1
    simpa only [recoveredVector, hc, powerVector] using hsize.trans hbound


end Cslib.Algorithms.IntegerPower

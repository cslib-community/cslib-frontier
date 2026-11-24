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

/-!
# Materialized integer matrix-power columns

`powerColumnVector M s i` computes `M ^ s` applied to the `i`-th standard basis vector.
Each multiplication first computes the previous column and then fills a new array-backed
`Vector`. Thus later coordinate reads access stored entries of that column.

The getter theorem identifies this computation with the mathematical matrix power. If every
matrix entry has absolute value at most one, an entry after `s` multiplications has absolute
value at most `n ^ s`, hence at most `s * n.size + 1` magnitude bits. These are correctness and
integer-size guarantees. The uniform native machine realization is supplied by
`Cslib.IntTable.powerColumn` in `CslibFrontier.Computability.PolyTime.Int.MatrixPower`;
the complete recovery program and its agreement with this implementation are in `Program`.

## Main definitions

* `Cslib.Algorithms.PlantedClique.powerColumnVector`: materialized matrix-vector iteration.

## Main results

* `Cslib.Algorithms.PlantedClique.getElem_powerColumnVector`: agreement with a matrix-power column.
* `Cslib.Algorithms.PlantedClique.natAbs_powerColumnVector_le`: the entry magnitude bound.
* `Cslib.Algorithms.PlantedClique.size_powerColumnVector_le`: the binary magnitude-size bound.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix

variable {n : ℕ}

/-- Compute a power column by storing the entire column after each matrix multiplication. -/
@[expose] def powerColumnVector (M : Matrix (Fin n) (Fin n) ℤ) : ℕ → Fin n → Vector ℤ n
  | 0, i => Vector.ofFn fun j => if j = i then 1 else 0
  | s + 1, i =>
    let v := powerColumnVector M s i
    Vector.ofFn fun j => ∑ l : Fin n, M j l * v[l.val]

/-- Reading a stored power-column entry agrees with the corresponding matrix-power entry. -/
@[simp]
theorem getElem_powerColumnVector (M : Matrix (Fin n) (Fin n) ℤ) (s : ℕ)
    (i j : Fin n) : (powerColumnVector M s i)[j.val] = (M ^ s) j i := by
  induction s generalizing j with
  | zero => simp [powerColumnVector, Matrix.one_apply]
  | succ s ih =>
    simp only [powerColumnVector, Vector.getElem_ofFn, ih, pow_succ', Matrix.mul_apply]

/-- If all matrix entries have magnitude at most one, each multiplication grows the largest
entry magnitude by at most a factor of the dimension. -/
theorem natAbs_powerColumnVector_le (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ j l, (M j l).natAbs ≤ 1) (s : ℕ) (i j : Fin n) :
    ((powerColumnVector M s i)[j]).natAbs ≤ n ^ s := by
  change ((powerColumnVector M s i)[j.val]).natAbs ≤ n ^ s
  induction s generalizing j with
  | zero =>
    simp only [powerColumnVector, Vector.getElem_ofFn, pow_zero]
    split <;> simp
  | succ s ih =>
    simp only [powerColumnVector, Vector.getElem_ofFn]
    calc (∑ l : Fin n, M j l * (powerColumnVector M s i)[l.val]).natAbs
        ≤ ∑ l : Fin n, (M j l * (powerColumnVector M s i)[l.val]).natAbs :=
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

end Cslib.Algorithms.PlantedClique

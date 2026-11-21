/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.MultiplicationQuery

/-!
# Streamed modular inner products

The outer carry-save tree ranges over word pairs. A real leaf starts the inner multiplication
tree directly on its two carry-save words. There is only one finishing carry-lookahead adder,
after both trees. A terminal multiplication leaf queries at most one bit of each operand.
-/

@[expose] public section
namespace Cslib.Circuits.Boolean.CarrySaveQuery.InnerProduct

open BitString
open scoped BigOperators

variable {w d : ℕ}

/-- A real row starts its product tree; rows past the supplied array are zero. -/
def rowPair (a b : Fin d → BitString w) (j : ℕ) : BitString (w + w) :=
  if h : j < d then Multiplication.rootPair (a ⟨j, h⟩) (b ⟨j, h⟩)
  else Fin.append (fun _ => false) (fun _ => false)

/-- The outer tree selects its row by a binary path. -/
def rows (a b : Fin d → BitString w) (path : List Bool) : BitString (w + w) :=
  rowPair a b (binaryValue path)

/-- One carry-lookahead finish for the nested carry-save trees. -/
def result (a b : Fin d → BitString w) : BitString w :=
  (carryLookaheadAdd w).eval interpretation (tree (rows a b) (Nat.clog 2 d) [])

private theorem val_row_padded (a b : Fin d → BitString w) {j : ℕ} (hj : d ≤ j) :
    pairVal (rowPair a b j) = 0 := by simp [rowPair, Nat.not_lt.mpr hj]

/-- The result is exactly the sum of products modulo the input precision, including
empty arrays and zero-width inputs. -/
theorem val_result (a b : Fin d → BitString w) :
    (equivFin w (result a b) : ℕ) =
      (∑ j : Fin d, (equivFin w (a j) : ℕ) * (equivFin w (b j) : ℕ)) % 2 ^ w := by
  rw [result, val_eval_carryLookaheadAdd_pair, pairVal_tree_mod]
  unfold rows
  rw [leafSum_binaryValue]
  simp only [binaryValue, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  have he : ∑ j ∈ Finset.range (2 ^ Nat.clog 2 d), pairVal (rowPair a b j) =
      ∑ j ∈ Finset.range d, pairVal (rowPair a b j) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.le_pow_clog (by decide) d))
    intro j _ hj
    exact val_row_padded a b (by simpa using hj)
  rw [he, ← Fin.sum_univ_eq_sum_range (fun j => pairVal (rowPair a b j))]
  rw [Finset.sum_nat_mod (Finset.univ : Finset (Fin d)) (2 ^ w)
    (fun j => pairVal (rowPair a b j.val)),
    Finset.sum_nat_mod Finset.univ (2 ^ w)
      (fun j : Fin d => (equivFin w (a j) : ℕ) * (equivFin w (b j) : ℕ))]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [rowPair, j.isLt, ↓reduceDIte, Multiplication.pairVal_rootPair_mod]

/-- At the row boundary a query continues at exactly the root of the selected product tree.
The selected word, bit and claim can therefore travel unchanged across this boundary. -/
theorem value_row (a b : Fin d → BitString w) (path : List Bool) (carry : Bool) (i : Fin w) :
    value (rows a b) ⟨path, 0, carry, i.val⟩ =
      if h : binaryValue path < d then
        value (Multiplication.leaves (a ⟨_, h⟩) (b ⟨_, h⟩))
          ⟨[], Nat.clog 2 w, carry, i.val⟩
      else false := by
  by_cases h : binaryValue path < d
  · simp [value, tree, rows, rowPair, h, Multiplication.rootPair]
  · have hz (t : Fin (w + w)) :
        Fin.append (fun _ : Fin w => false) (fun _ : Fin w => false) t = false :=
      Fin.addCases (fun j => Fin.append_left _ _ j) (fun j => Fin.append_right _ _ j) t
    cases carry <;> simp [value, tree, rows, rowPair, h, component, hz]

end Cslib.Circuits.Boolean.CarrySaveQuery.InnerProduct

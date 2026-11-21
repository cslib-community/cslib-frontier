/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SparseModeMass
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.InnerProductQuery
import CslibFrontier.Foundations.Data.BitString.Binary
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size

/-!
# A local inner-product circuit for the sparse mode weight test

Each row of the streamed inner product selects a colour row and two sparse entry indices.
Its operands are a clipped gap and a clipped multiplicity, and reversed or missing pairs
contribute zero. A logarithmic precision suffices for the exact resulting integer, even
on overweight tuples.
-/

public section

namespace Cslib.Circuits.Frontier.ModeMassQuery

open Cslib.SparseModeTuple BitString Finset Boolean.CarrySaveQuery

/-- Rectangular row, gap and multiplicity indices in the order used by the inner product. -/
def index (L : ℕ) : Fin L × Fin L × Fin L ≃ Fin (L * (L * L)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

/-- Precision holding both each clipped operand and the complete sum. -/
@[expose] def width (p L : ℕ) : ℕ := (L ^ 3 * p ^ 2 + p).size

/-- The complete precision is linear in the bit lengths of the budget and word length. -/
theorem width_le (p L : ℕ) : width p L ≤ 3 * L.size + 2 * p.size + 1 := by
  apply Nat.size_le.mpr
  have hL := Nat.lt_size_self L
  have hp := Nat.lt_size_self p
  have hpow : L ^ 3 * p ^ 2 < 2 ^ (3 * L.size + 2 * p.size) := by
    rw [pow_add, mul_comm 3, mul_comm 2 p.size, pow_mul, pow_mul]
    exact Nat.mul_lt_mul_of_lt_of_lt (Nat.pow_lt_pow_left hL (by decide))
      (Nat.pow_lt_pow_left hp (by decide))
  have hsmall := hp.trans_le (Nat.pow_le_pow_right (by decide)
    (by omega : p.size ≤ 3 * L.size + 2 * p.size))
  rw [pow_succ 2, Nat.mul_two]
  exact Nat.add_lt_add hpow hsmall

/-- One row of the integer inner product. Both natural operands are at most `p`. -/
@[expose] def pair (p : ℕ) (rows : List Row) {L : ℕ} : Fin L × Fin L × Fin L → ℕ × ℕ
  | (c, i, j) =>
      let es := entriesAt rows c.val
      (if i.val ≤ j.val then min p (gapAt es i.val) else 0, min p (copiesAt es j.val))

private theorem pair_le (p : ℕ) (rows : List Row) {L : ℕ} (z : Fin L × Fin L × Fin L) :
    (pair p rows z).1 ≤ p ∧ (pair p rows z).2 ≤ p := by
  rcases z with ⟨c, i, j⟩
  simp only [pair]
  split <;> simp

private def bits (w a : ℕ) : BitString w :=
  (equivFin w).symm ⟨a % 2 ^ w, Nat.mod_lt _ (by positivity)⟩

/-- The first input word comes from a single gap. The second comes from a single multiplicity. -/
def operand (right : Bool) (p L : ℕ) (rows : List Row) (j : Fin (L * (L * L))) :
    BitString (width p L) :=
  let v := pair p rows ((index L).symm j)
  bits (width p L) (if right then v.2 else v.1)

/-- Compute the clipped mass with the streamed modular inner-product circuit. -/
def result (p L : ℕ) (rows : List Row) : BitString (width p L) :=
  InnerProduct.result (operand false p L rows) (operand true p L rows)

private theorem val_operand (right : Bool) (p L : ℕ) (rows : List Row)
    (j : Fin (L * (L * L))) :
    (equivFin _ (operand right p L rows j) : ℕ) =
      if right then (pair p rows ((index L).symm j)).2 else (pair p rows ((index L).symm j)).1 := by
  have hp : p < 2 ^ width p L := (Nat.le_add_left _ _).trans_lt (Nat.lt_size_self _)
  have h := pair_le p rows ((index L).symm j)
  cases right <;> simp [operand, bits, Nat.mod_eq_of_lt (h.1.trans_lt hp),
    Nat.mod_eq_of_lt (h.2.trans_lt hp)]

/-- Every input-wire bit refers to just one of the selected sparse fields. -/
theorem operand_apply (right : Bool) (p L : ℕ) (rows : List Row) (j : Fin (L * (L * L)))
    (i : Fin (width p L)) :
    operand right p L rows j i = (if right then (pair p rows ((index L).symm j)).2
      else (pair p rows ((index L).symm j)).1).testBit i.val := by
  rw [← testBit_equivFin (operand right p L rows j) i, val_operand]

/-- The resulting integer is the full clipped sum. Modular wrap-around cannot change it. -/
theorem val_result (p L : ℕ) (rows : List Row) :
    (equivFin _ (result p L rows) : ℕ) =
      ∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L, clippedTerm p (entriesAt rows c) i j := by
  rw [result, InnerProduct.val_result]
  simp only [val_operand, Bool.false_eq_true, ↓reduceIte]
  have hsum :
      (∑ j : Fin (L * (L * L)), (pair p rows ((index L).symm j)).1 *
        (pair p rows ((index L).symm j)).2) =
        ∑ c ∈ range L, ∑ i ∈ range L, ∑ j ∈ range L, clippedTerm p (entriesAt rows c) i j := by
    calc
      _ = ∑ z : Fin L × Fin L × Fin L, (pair p rows z).1 * (pair p rows z).2 :=
        Fintype.sum_equiv (index L).symm _ _ fun _ => rfl
      _ = _ := by
        simp only [Fintype.sum_prod_type]
        simp_rw [← Fin.sum_univ_eq_sum_range]
        apply sum_congr rfl
        intro c _
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        dsimp only [pair, clippedTerm]
        split <;> simp
  rw [hsum, Nat.mod_eq_of_lt]
  exact (sum_clipped_le p L rows).trans_lt
    ((Nat.le_add_right _ _).trans_lt (Nat.lt_size_self _))

/-- The Boolean result's integer value is below the precision budget exactly for admissible
weighted mass. This test reads the sparse entries through the two clipped operands. -/
theorem val_result_lt_iff (p : ℕ) (rows : List Row) :
    (equivFin _ (result p (encode rows).length rows) : ℕ) < p ↔ mass rows < p := by
  rw [val_result]
  exact sum_clipped_lt_iff_of_encode p rows

end Cslib.Circuits.Frontier.ModeMassQuery

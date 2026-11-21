/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.InnerProductQuery
public import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# A single physical path for a modular inner product

The first path field selects a row and the second selects its shifted partial product.
This combines both carry-save traversals into the single word-valued sum accepted by the
native carry-save evaluator.
-/

@[expose] public section
namespace Cslib.Circuits.Boolean.CarrySaveQuery.InnerProduct

open BitString

variable {w d : ℕ}

private def sumTree (f : List Bool → ℕ) : ℕ → List Bool → ℕ
  | 0, p => f p
  | n + 1, p => sumTree f n (p ++ [false]) + sumTree f n (p ++ [true])

private theorem leafSum_eq (leaves : List Bool → BitString (w + w)) (n : ℕ) (p : List Bool) :
    leafSum leaves n p = sumTree (fun q => pairVal (leaves q)) n p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [leafSum, sumTree, ih]

private theorem sumTree_add (f : List Bool → ℕ) (n m : ℕ) (p : List Bool) :
    sumTree f (n + m) p = sumTree (sumTree f m) n p := by
  induction n generalizing p with
  | zero => simp [sumTree]
  | succ n ih => simp only [Nat.succ_add, sumTree, ih]

private theorem sumTree_congr_mod (M : ℕ) (f g : List Bool → ℕ) (n : ℕ) (p q : List Bool)
    (h : ∀ tail : List Bool, tail.length = n → f (p ++ tail) % M = g (q ++ tail) % M) :
    sumTree f n p % M = sumTree g n q % M := by
  induction n generalizing p q with
  | zero => simpa only [sumTree, List.append_nil] using h [] rfl
  | succ n ih =>
    have hc (s : Bool) : sumTree f n (p ++ [s]) % M = sumTree g n (q ++ [s]) % M := by
      apply ih
      intro tail htail
      simpa only [List.append_assoc, List.singleton_append] using
        h (s :: tail) (by simp [htail])
    rw [sumTree, sumTree, Nat.add_mod, hc false, hc true, ← Nat.add_mod]

private theorem sumTree_zero (n : ℕ) (p : List Bool) : sumTree (fun _ => 0) n p = 0 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [sumTree, ih, Nat.add_zero]

/-- Decode one path of the physical evaluator as two consecutive fields. -/
def flatLeaves (a b : Fin d → BitString w) (path : List Bool) : BitString (w + w) :=
  let row := binaryValue (path.take (Nat.clog 2 d))
  if h : row < d then
    Multiplication.leaves (a ⟨row, h⟩) (b ⟨row, h⟩) (path.drop (Nat.clog 2 d))
  else Fin.append (fun _ => false) (fun _ => false)

/-- The single padded tree has the same modular value as the nested row/product tree. -/
theorem val_flat (a b : Fin d → BitString w) :
    (equivFin w ((carryLookaheadAdd w).eval interpretation
      (tree (flatLeaves a b) (Nat.clog 2 d + Nat.clog 2 w) [])) : ℕ) =
    (equivFin w (result a b) : ℕ) := by
  rw [result, val_eval_carryLookaheadAdd_pair, val_eval_carryLookaheadAdd_pair,
    pairVal_tree_mod, pairVal_tree_mod, leafSum_eq, leafSum_eq, sumTree_add]
  apply sumTree_congr_mod
  intro row hr
  simp only [List.nil_append]
  by_cases h : binaryValue row < d
  · simp only [rows, rowPair, h, ↓reduceDIte, Multiplication.rootPair, pairVal_tree_mod,
      leafSum_eq]
    apply sumTree_congr_mod
    intro shift _
    simp [flatLeaves, ← hr, h]
  · have hz : sumTree (fun q => pairVal (flatLeaves a b q)) (Nat.clog 2 w) row % 2 ^ w =
        sumTree (fun _ => 0) (Nat.clog 2 w) [] % 2 ^ w := by
      apply sumTree_congr_mod
      intro shift _
      simp [flatLeaves, ← hr, h]
    simpa [sumTree_zero, rows, rowPair, h] using hz

/-- A claim about any output bit of the single tree is a claim about the modular inner product. -/
theorem bit_flat (a b : Fin d → BitString w) (i : Fin w) :
    (carryLookaheadAdd w).eval interpretation
      (tree (flatLeaves a b) (Nat.clog 2 d + Nat.clog 2 w) []) i =
    (∑ j : Fin d, (equivFin w (a j) : ℕ) * (equivFin w (b j) : ℕ)).testBit i.val := by
  rw [← testBit_equivFin ((carryLookaheadAdd w).eval interpretation
    (tree (flatLeaves a b) (Nat.clog 2 d + Nat.clog 2 w) [])) i,
    val_flat, val_result, Nat.testBit_mod_two_pow]
  simp [i.isLt]

end Cslib.Circuits.Boolean.CarrySaveQuery.InnerProduct

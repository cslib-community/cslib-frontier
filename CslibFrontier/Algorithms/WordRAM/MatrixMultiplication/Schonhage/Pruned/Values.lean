/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Codes
public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.Magnitude

/-!
# Values and flat addresses of the native recursion

## Main definitions

* `PrunedQuery.partialValue`: the requested accumulator after a prefix of the ten terms.

## Main results

* `PrunedQuery.slice_strided`: flat strided leaf arrays agree with the existing `sliceAt`.
* `PrunedQuery.abs_partialValue_le`: every intermediate accumulator has an explicit bound.

These are identities and magnitude bounds for the controller invariant. They do not assume
that a machine executes the recursion.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Finset

/-- The existing leaf indexing has the same least-significant-first decomposition as queries. -/
theorem leafIndex_cons {n : ℕ} (lam : Term) (v : Leaf n) :
    (Encoding.leafIndex (Fin.cons lam v)).val =
      (Encoding.termDigits.symm lam).val + 10 * (Encoding.leafIndex v).val := by
  simp only [Encoding.leafIndex, finFunctionFinEquiv_apply, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
    pow_succ, mul_sum]
  exact congrArg _ (sum_congr rfl fun _ _ => by ring)

/-- The native prefix/stride update selects exactly the existing mathematical child slice. -/
theorem slice_strided {n : ℕ} (a : ℕ → ℤ) (p s : ℕ) (lam : Term) :
    sliceAt (fun v : Leaf (n + 1) => a (p + s * (Encoding.leafIndex v).val)) lam =
      fun v : Leaf n => a (p + (Encoding.termDigits.symm lam).val * s +
        (s * 10) * (Encoding.leafIndex v).val) := by
  funext v
  change a (p + s * (Encoding.leafIndex (Fin.cons lam v)).val) = _
  rw [leafIndex_cons]; exact congrArg a (by ring)

/-- A frame's prefix and stride put every remaining leaf inside the original encoding array. -/
theorem leafAddress_lt {n p s size : ℕ} (hp : p < s) (hs : s * 10 ^ n = size)
    (v : Leaf n) : p + s * (Encoding.leafIndex v).val < size := by
  have hi := (Encoding.leafIndex v).isLt
  nlinarith

/-- The mathematical value of a requested native accumulator after terms numbered below `k`.
Unrequested directory cells are deliberately unspecified by the native interface. -/
def partialValue {n : ℕ} (a b : Leaf (n + 1) → ℤ) (S : Finset (OutStr (n + 1)))
    (w : OutStr (n + 1)) (k : ℕ) : ℤ :=
  ∑ i : Fin 10 with i.val < k ∧ (Encoding.termDigits i).Contributes (w 0),
    Pruned.childResult a b S (Encoding.termDigits i) (Fin.tail w)

/-- Before the first child, the native accumulator is zero. -/
@[simp]
theorem partialValue_zero {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) : partialValue a b S w 0 = 0 := by
  simp [partialValue]

/-- Processing the next term adds exactly its contributing child, or leaves the value unchanged. -/
theorem partialValue_succ {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) (k : Fin 10) :
    partialValue a b S w (k.val + 1) = partialValue a b S w k.val +
      if (Encoding.termDigits k).Contributes (w 0) then
        Pruned.childResult a b S (Encoding.termDigits k) (Fin.tail w) else 0 := by
  unfold partialValue
  split_ifs with hc
  · conv_rhs => rw [add_comm, ← sum_insert
      (f := fun i => Pruned.childResult a b S (Encoding.termDigits i) (Fin.tail w)) (by simp)]
    refine sum_congr ?_ fun _ _ => rfl
    ext i; simp only [mem_insert, mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨h, h'⟩ => if he : i = k then .inl he else
        .inr ⟨by have := Fin.val_ne_of_ne he; omega, h'⟩,
      by rintro (rfl | ⟨h, h'⟩); exacts [⟨by omega, hc⟩, ⟨by omega, h'⟩]⟩
  · rw [add_zero]
    refine sum_congr ?_ fun _ _ => rfl
    ext i; simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨h, h'⟩ =>
        ⟨by have := Fin.val_ne_of_ne (fun he : i = k => hc (he ▸ h')); omega, h'⟩,
      fun ⟨h, h'⟩ => ⟨by omega, h'⟩⟩

/-- After all ten terms, a requested accumulator is the existing pruned result. -/
theorem partialValue_ten {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) (hw : w ∈ S) :
    partialValue a b S w 10 = Pruned.result (n + 1) a b S w := by
  rw [Pruned.result_succ_apply, ite_eq_left hw, partialValue]
  exact sum_equiv Encoding.termDigits (fun _ => by simp) fun _ _ => rfl

/-- Every child's mathematical result has the bound for its remaining depth, including a
skipped empty child whose value is zero. -/
theorem abs_childResult_le {n : ℕ} (a b : Leaf (n + 1) → ℤ) (A B : ℤ)
    (hA : ∀ v, |a v| ≤ A) (hB : ∀ v, |b v| ≤ B)
    (S : Finset (OutStr (n + 1))) (lam : Term) (w : OutStr n) :
    |Pruned.childResult a b S lam w| ≤ 10 ^ n * (A * B) := by
  unfold Pruned.childResult; split_ifs
  · exact Pruned.abs_result_le _ _ A B (fun v => hA (Fin.cons lam v))
      (fun v => hB (Fin.cons lam v)) _ _
  · have := (abs_nonneg _).trans (hA fun _ => .P0)
    have := (abs_nonneg _).trans (hB fun _ => .P0)
    simp only [Pi.zero_apply, abs_zero]; positivity

/-- The bound covers all partial sums, not only the final recursively specified output. -/
theorem abs_partialValue_le {n : ℕ} (a b : Leaf (n + 1) → ℤ) (A B : ℤ)
    (hA : ∀ v, |a v| ≤ A) (hB : ∀ v, |b v| ≤ B)
    (S : Finset (OutStr (n + 1))) (w : OutStr (n + 1)) (k : ℕ) :
    |partialValue a b S w k| ≤ 10 ^ (n + 1) * (A * B) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA fun _ => .P0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB fun _ => .P0)
  refine (abs_sum_le_card_mul _ fun _ _ => abs_childResult_le a b A B hA hB S _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right ?_ (by positivity)).trans_eq
    (by ring : (10 : ℤ) * (10 ^ n * (A * B)) = 10 ^ (n + 1) * (A * B))
  exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin 10)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

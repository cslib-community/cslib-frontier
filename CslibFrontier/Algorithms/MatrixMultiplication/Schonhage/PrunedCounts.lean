/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.Pruned

/-!
# Counts of nonempty calls in the finite pruned recursion

## Main results

* `Pruned.calls_irrel`: the call trace depends only on the requests, not the encoded values.
* `Pruned.card_calls_le_totalSize_add_one`: requested-set cardinalities pay for every call,
  with one extra root for the empty-query boundary.

These are combinatorial facts about the existing finite trace. They do not assign an instruction
cost to the recursion. Native execution bounds must separately charge their actual instructions.

## References

The trace is from [AlmanWilliams2026, Section 2.4.2] and Anthropic's formal-math revision
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`, [pinned source](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2/Lemma10.lean).
-/

public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

open Finset

/-- An empty request set has no child requests. -/
@[simp]
theorem childSet_empty {n : ℕ} (lam : Term) : childSet (∅ : Finset (OutStr (n + 1))) lam = ∅ := by
  ext w
  simp [mem_childSet]

/-- Values of the two encoded arrays do not affect which calls are made. -/
theorem Pruned.calls_irrel {n : ℕ} (a b a' b' : Leaf n → ℤ) (S : Finset (OutStr n)) :
    Pruned.calls n a b S = Pruned.calls n a' b' S := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Pruned.calls_succ, Pruned.calls_succ]
    refine congrArg _ (congrArg (fun f => univ.val.bind f) (funext fun lam => ?_))
    by_cases h : (childSet S lam).Nonempty <;> simp only [Pruned.childCalls, h, ↓reduceIte]
    exact congrArg (Multiset.map (PrunedCall.under lam)) (ih _ _ _ _ _)

/-- One root call and all nonempty child traces, counted with their multiplicities. -/
theorem Pruned.card_calls_succ {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) :
    (Pruned.calls (n + 1) a b S).card = 1 + ∑ lam,
      if (childSet S lam).Nonempty then
        (Pruned.calls n (sliceAt a lam) (sliceAt b lam) (childSet S lam)).card else 0 := by
  rw [Pruned.calls_succ, Multiset.card_cons, Multiset.card_bind, Nat.add_comm]
  refine congrArg (Nat.add 1) (sum_congr rfl fun lam _ => ?_)
  simp only [Function.comp_apply, Multiset.card_map, Pruned.childCalls]
  split_ifs <;> rfl

/-- The passed-set total is the root size plus the totals of its nonempty children. -/
theorem Pruned.totalSize_succ {n : ℕ} (a b : Leaf (n + 1) → ℤ)
    (S : Finset (OutStr (n + 1))) :
    Pruned.totalSize a b S = S.card + ∑ lam,
      if (childSet S lam).Nonempty then
        Pruned.totalSize (sliceAt a lam) (sliceAt b lam) (childSet S lam) else 0 := by
  unfold Pruned.totalSize
  rw [Pruned.calls_succ, Multiset.map_cons, Multiset.sum_cons, Multiset.map_bind,
    Multiset.sum_bind]
  refine congrArg (Nat.add S.card) (sum_congr rfl fun lam _ => ?_)
  by_cases h : (childSet S lam).Nonempty <;>
    simp only [Pruned.childCalls, h, ↓reduceIte, Multiset.map_map,
      Multiset.map_zero, Multiset.sum_zero]
  rfl

/-- A nonempty call carries at least one query, so the passed-set total pays for every call. -/
theorem Pruned.card_calls_le_totalSize {n : ℕ} (a b : Leaf n → ℤ)
    (S : Finset (OutStr n)) (hS : S.Nonempty) :
    (Pruned.calls n a b S).card ≤ Pruned.totalSize a b S := by
  induction n with
  | zero => simpa [Pruned.calls, Pruned.run, Pruned.totalSize] using one_le_card.mpr hS
  | succ n ih =>
    rw [Pruned.card_calls_succ, Pruned.totalSize_succ]
    refine Nat.add_le_add (one_le_card.mpr hS) (sum_le_sum fun lam _ => ?_)
    split_ifs with h
    · exact ih _ _ _ h
    · exact le_rfl

/-- Empty requests make only the root call, including at zero depth. -/
theorem Pruned.card_calls_empty {n : ℕ} (a b : Leaf n → ℤ) :
    (Pruned.calls n a b ∅).card = 1 := by
  cases n with
  | zero => rfl
  | succ n => simp [Pruned.card_calls_succ]

/-- Every call is paid for by a requested-set element, except possibly an empty root. -/
theorem Pruned.card_calls_le_totalSize_add_one {n : ℕ} (a b : Leaf n → ℤ)
    (S : Finset (OutStr n)) :
    (Pruned.calls n a b S).card ≤ Pruned.totalSize a b S + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [Pruned.card_calls_empty]; omega
  · exact (Pruned.card_calls_le_totalSize a b S hS).trans (Nat.le_add_right _ _)

/-- Encoded values do not affect the total size of the request sets. -/
theorem Pruned.totalSize_irrel {n : ℕ} (a b a' b' : Leaf n → ℤ) (S : Finset (OutStr n)) :
    Pruned.totalSize a b S = Pruned.totalSize a' b' S := by
  rw [Pruned.totalSize, Pruned.totalSize, Pruned.calls_irrel a b a' b' S]

/-- Even without pruning, a ten-way depth-`n` tree has fewer than twice `10^n` nodes.
This ordinary count supplies a word-size bound for native timestamp generations. -/
theorem Pruned.card_calls_add_one_le {n : ℕ} (a b : Leaf n → ℤ)
    (S : Finset (OutStr n)) :
    (Pruned.calls n a b S).card + 1 ≤ 2 * 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let f : Term → ℕ := fun lam => if (childSet S lam).Nonempty then
      (Pruned.calls n (sliceAt a lam) (sliceAt b lam) (childSet S lam)).card else 0
    have hsum := sum_le_sum (s := univ) fun lam _ => (show f lam + 1 ≤ 2 * 10 ^ n by
      dsimp only [f]
      split_ifs
      · exact ih _ _ _
      · have : 0 < (10 : ℕ) ^ n := Nat.pow_pos (by decide)
        omega)
    simp only [sum_add_distrib, sum_const, card_univ, show Fintype.card Term = 10 by decide,
      smul_eq_mul] at hsum
    rw [Pruned.card_calls_succ, pow_succ]
    change 1 + (∑ lam, f lam) + 1 ≤ _
    omega

end Cslib.Algorithms.MatrixMultiplication.Schonhage

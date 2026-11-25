/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Weight
public import Cslib.Computability.QueryComplexity.Measures

/-!
# A block containing exactly two adjacent true bits

`adjacentPair n` accepts exactly the words whose two true positions are consecutive in the
linear order on `Fin n`. Overlapping choices are allowed: the middle pair of a four-bit word
is accepted. This is the local predicate in [AroraBarak07], Chapter 11 Exercise 2, printed
page 218 / PDF page 234. The global exercise takes an OR over disjoint blocks.

## Main definitions

* `Cslib.BitString.adjacentPair`: the local adjacent-pair predicate.

## Main results

* `Cslib.BitString.weight_eq_two_of_adjacentPair`: every accepted word has weight two.
* `Cslib.BitString.sensitivityAt_adjacentPair_of_true`: every bit is sensitive at acceptance.
* `Cslib.BitString.sensitivityAt_adjacentPair_le_three`: rejected-input sensitivity is at most
  three.
-/

public section

namespace Cslib.BitString

open Finset

/-- Exactly two positions are true, and they are adjacent without wraparound. The body is
exposed so finite checked examples can evaluate the predicate. -/
@[expose] def adjacentPair (n : ℕ) : BooleanFunction n := fun x =>
  decide (∃ a b : Fin n, b.val = a.val + 1 ∧ ∀ i, x i = decide (i = a ∨ i = b))

/-- Accepted words are precisely the indicators of adjacent pairs. -/
theorem adjacentPair_eq_true_iff {n : ℕ} {x : BitString n} :
    adjacentPair n x = true ↔
      ∃ a b : Fin n, b.val = a.val + 1 ∧ ∀ i, x i = decide (i = a ∨ i = b) := by
  simp [adjacentPair]

/-- An adjacent pair has two distinct endpoints, hence exactly two true bits. -/
theorem weight_eq_two_of_adjacentPair {n : ℕ} {x : BitString n}
    (h : adjacentPair n x = true) : weight x = 2 := by
  obtain ⟨a, b, hab, hx⟩ := adjacentPair_eq_true_iff.mp h
  rw [weight, show ({i | x i = true} : Finset (Fin n)) = {a, b} by ext; simp [hx]]
  exact card_pair fun he => by subst he; omega

/-- The all-false word is not an adjacent pair, including lengths zero and one. -/
@[simp] theorem adjacentPair_zero (n : ℕ) : adjacentPair n (fun _ => false) = false := by
  cases h : adjacentPair n (fun _ => false) with
  | false => rfl
  | true =>
    have hw := weight_eq_two_of_adjacentPair h
    simp [weight] at hw

/-- One true bit does not meet the two-bit acceptance condition. -/
@[simp] theorem adjacentPair_singleton {n : ℕ} (a : Fin n) :
    adjacentPair n (fun i => decide (i = a)) = false := by
  cases h : adjacentPair n (fun i => decide (i = a)) with
  | false => rfl
  | true =>
    have hw := weight_eq_two_of_adjacentPair h
    rw [weight, show ({i : Fin n | decide (i = a) = true} : Finset (Fin n)) = {a} by ext; simp,
      card_singleton] at hw
    omega

/-- Every pair of consecutive positions gives an accepted input. -/
theorem adjacentPair_pair {n : ℕ} (a b : Fin n) (hab : b.val = a.val + 1) :
    adjacentPair n (fun i => decide (i = a ∨ i = b)) = true :=
  adjacentPair_eq_true_iff.mpr ⟨a, b, hab, fun _ => rfl⟩

/-- Flipping one bit into an accepted word starts at weight one or weight three. -/
theorem weight_eq_one_or_three_of_update_adjacentPair {n : ℕ} {x : BitString n} {i : Fin n}
    (h : adjacentPair n (Function.update x i (!x i)) = true) :
    weight x = 1 ∨ weight x = 3 := by
  have hw := weight_eq_two_of_adjacentPair h
  cases hi : x i
  · simp only [hi, Bool.not_false] at hw
    rw [weight_update_true hi] at hw
    omega
  · have := weight_update_false hi
    simp only [hi, Bool.not_true] at hw
    omega

/-- Changing any single bit of an accepted pair destroys acceptance. -/
theorem adjacentPair_update_of_true {n : ℕ} {x : BitString n}
    (hx : adjacentPair n x = true) (i : Fin n) :
    adjacentPair n (Function.update x i (!x i)) = false := by
  cases h : adjacentPair n (Function.update x i (!x i)) with
  | false => rfl
  | true =>
    have hw := weight_eq_two_of_adjacentPair hx
    rcases weight_eq_one_or_three_of_update_adjacentPair h with ht | ht <;> omega

/-- Every coordinate is sensitive at an accepted adjacent pair. -/
theorem sensitivityAt_adjacentPair_of_true {n : ℕ} {x : BitString n}
    (hx : adjacentPair n x = true) : sensitivityAt (adjacentPair n) x = n := by
  refine le_antisymm (sensitivityAt_le_card _ _) ?_
  simpa only [card_univ, Fintype.card_fin] using
    card_le_sensitivityAt (S := univ) (f := adjacentPair n) (x := x) fun i _ => by
      simp [IsSensitiveCoord, adjacentPair_update_of_true hx i, hx]

private theorem card_neighbors_le_two {n : ℕ} (a : Fin n) :
    #{i : Fin n | i.val + 1 = a.val ∨ a.val + 1 = i.val} ≤ 2 := by
  rw [filter_or]
  exact (card_union_le _ _).trans (Nat.add_le_add
    (card_le_one.mpr fun i hi j hj => Fin.ext (by simp only [mem_filter] at hi hj; omega))
    (card_le_one.mpr fun i hi j hj => Fin.ext (by simp only [mem_filter] at hi hj; omega)))

/-- At a rejected word, at most three single-bit changes can create an adjacent pair.
A change into weight two starts at weight one or three. In the former case only the two
neighbors of the sole true bit can work; in the latter only its three true bits can work. -/
theorem sensitivityAt_adjacentPair_le_three {n : ℕ} {x : BitString n}
    (hx : adjacentPair n x = false) : sensitivityAt (adjacentPair n) x ≤ 3 := by
  have hacc (i : Fin n) (hi : i ∈ sensitiveCoords (adjacentPair n) x) :
      adjacentPair n (Function.update x i (!x i)) = true := by
    simpa only [mem_sensitiveCoords, IsSensitiveCoord, hx, Bool.not_eq_false] using hi
  rcases (sensitiveCoords (adjacentPair n) x).eq_empty_or_nonempty with hs | ⟨j, hj⟩
  · simp [sensitivityAt, hs]
  rcases weight_eq_one_or_three_of_update_adjacentPair (hacc j hj) with hw | hw
  · obtain ⟨a, ha⟩ := card_eq_one.mp hw
    have hxtrue (i : Fin n) : x i = true ↔ i = a := by
      simpa only [mem_filter, mem_univ, true_and, mem_singleton] using Finset.ext_iff.mp ha i
    refine (card_le_card (t := {i : Fin n | i.val + 1 = a.val ∨ a.val + 1 = i.val})
      fun i hi => ?_).trans ((card_neighbors_le_two a).trans (by decide))
    have hxi : x i = false := by
      cases ht : x i
      · rfl
      · have := weight_update_false ht
        have hw' := weight_eq_two_of_adjacentPair (hacc i hi)
        simp only [ht, Bool.not_true] at hw'
        omega
    have hai : a ≠ i := fun he => by simpa [hxi] using (hxtrue i).mpr he.symm
    obtain ⟨p, q, hpq, hp⟩ := adjacentPair_eq_true_iff.mp (hacc i hi)
    have hpa : a = p ∨ a = q := of_decide_eq_true
      (by simpa [Function.update_of_ne hai, (hxtrue a).mpr rfl] using (hp a).symm)
    have hpi : i = p ∨ i = q := of_decide_eq_true (by simpa [hxi] using (hp i).symm)
    simp only [mem_filter, mem_univ, true_and]
    rcases hpa with rfl | rfl <;> rcases hpi with rfl | rfl <;> simp_all
  · refine (card_le_card (t := {i | x i = true}) fun i hi => ?_).trans hw.le
    have ht := weight_eq_two_of_adjacentPair (hacc i hi)
    cases hi' : x i
    · simp only [hi', Bool.not_false] at ht
      rw [weight_update_true hi'] at ht
      omega
    · exact mem_filter.mpr ⟨mem_univ i, hi'⟩

end Cslib.BitString

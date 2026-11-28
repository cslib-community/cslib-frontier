/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness
public import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Nat.Choose.Sum

/-!
# Checking a tagged permutation by element distinctness

Give each destination one selector bit. Its requested record either participates in the
distinctness test or gets a flag that prevents a collision with the source. If a requested
record is missing, toggling its selector cancels the signed sum. If every requested record
occurs, only the empty selection contributes. With equally many source and destination records,
this checks the whole routing, including whether the tags form a permutation.

This single-test identity refines the two-test construction in the subsection “Checking a tagged
permutation” of [OpenAI2026MatrixExponentNineFourths]. Each free payload bit occurs once in the
test input. The selector contributes a unary weight. The identity is valid over every ring.
Conversely, guess the destinations and a strictly increasing table of outputs. Each distinct
list has one such routed table, its sorted order.

## Main results

* `sum_elementDistinctness_comparisonInput` checks inclusion of the requested records.
* `taggedPermutation_eq_sum_elementDistinctness` checks the tags and the payloads together.
* `elementDistinctness_eq_sum_sortedPermutations` counts the sorted routing of a flat bit string.
-/

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Finset Function

variable {n m k : ℕ}

/-- Append the requests to the source records in a flat string. The first bit of each source
word is zero. A request has first bit zero when selected and one otherwise. -/
@[expose] public def comparisonInput (source : Fin n → BitString k) (request : Fin m → BitString k)
    (selected : Finset (Fin m)) : BitString ((n + m) * (k + 1)) :=
  BitString.blocksEquiv.symm (Fin.append (fun i => Fin.cons false (source i))
    (fun j => Fin.cons (decide (j ∉ selected)) (request j)))

/-- With distinct requests, one signed distinctness test checks that the source records are
distinct and include every requested record. The two lists may have different lengths. -/
public theorem sum_elementDistinctness_comparisonInput (R : Type*) [Ring R]
    (source : Fin n → BitString k) (request : Fin m → BitString k) (hr : Injective request) :
    (∑ S : Finset (Fin m), if elementDistinctness _ _ (comparisonInput source request S)
      then (-1 : R) ^ #S else 0) =
      if Injective source ∧ ∀ j, ∃ i, source i = request j then 1 else 0 := by
  classical
  let missing := univ.filter (fun j => ¬ ∃ i, source i = request j)
  have accepts (S : Finset (Fin m)) :
      elementDistinctness _ _ (comparisonInput source request S) = true ↔
        Injective source ∧ S ⊆ missing := by
    simp only [elementDistinctness, comparisonInput, BitString.block_blocksEquiv_symm,
      decide_eq_true_eq, Fin.append_injective_iff]
    constructor
    · rintro ⟨hs, _, hcross⟩
      refine ⟨fun _ _ e => hs (Fin.cons_inj.mpr ⟨rfl, e⟩), fun j hj => ?_⟩
      simp only [missing, mem_filter, mem_univ, true_and]
      rintro ⟨i, hi⟩
      exact hcross i j (by simp [hj, hi])
    · rintro ⟨hs, hS⟩
      refine ⟨fun _ _ e => hs (Fin.cons_inj.mp e).2, fun _ _ e => hr (Fin.cons_inj.mp e).2, ?_⟩
      intro i j e
      obtain ⟨hflag, hword⟩ := Fin.cons_inj.mp e
      have hj : j ∈ S := by simpa using hflag
      exact (mem_filter.mp (hS hj)).2 ⟨i, hword⟩
  by_cases hs : Injective source
  · have hset : univ.filter (fun S => elementDistinctness _ _ (comparisonInput source request S)) =
        missing.powerset := by
      ext S
      simp only [mem_filter, mem_univ, true_and, mem_powerset, accepts, hs]
    have hempty : missing = ∅ ↔ ∀ j, ∃ i, source i = request j := by simp [missing]
    rw [← sum_filter, hset]
    have hsum := congrArg (Int.cast : ℤ → R) (sum_powerset_neg_one_pow_card (x := missing))
    push_cast at hsum
    simpa [hs, hempty] using hsum
  · simp [accepts, hs]

/-- The signed distinctness test for records addressed by the binary digits of their destination.
It accepts exactly a permutation of the addresses with the requested payload at every address.
No promise on the incoming addresses is required. -/
public theorem taggedPermutation_eq_sum_elementDistinctness (R : Type*) [Ring R]
    (tag : Fin n → Fin n) (x y : Fin n → BitString k) :
    (if Bijective tag ∧ ∀ i, x i = y (tag i) then (1 : R) else 0) =
      ∑ S : Finset (Fin n),
        if elementDistinctness _ _ (comparisonInput
          (fun i => Fin.append (BitString.indexBits (tag i)) (x i))
          (fun j => Fin.append (BitString.indexBits j) (y j)) S)
        then (-1 : R) ^ #S else 0 := by
  classical
  let word (j : Fin n) (z : BitString k) := Fin.append (BitString.indexBits j) z
  have word_eq {j l : Fin n} {z u : BitString k} : word j z = word l u ↔ j = l ∧ z = u := by
    change (Fin.appendEquiv _ _) (BitString.indexBits j, z) =
      (Fin.appendEquiv _ _) (BitString.indexBits l, u) ↔ _
    simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq, BitString.indexBits_injective.eq_iff]
  have hr : Injective (fun j => word j (y j)) := fun _ _ e => (word_eq.mp e).1
  rw [sum_elementDistinctness_comparisonInput R _ _ hr]
  apply if_congr _ rfl rfl
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨fun _ _ e => h.1 (word_eq.mp e).1, fun j => by
      obtain ⟨i, rfl⟩ := h.2 j
      exact ⟨i, word_eq.mpr ⟨rfl, hx i⟩⟩⟩
  · rintro ⟨_, h⟩
    have ht : Surjective tag := fun j => by
      obtain ⟨i, hi⟩ := h j
      exact ⟨i, (word_eq.mp hi).1⟩
    have hi : Injective tag := Finite.injective_iff_surjective.mpr ht
    refine ⟨⟨hi, ht⟩, fun i => ?_⟩
    obtain ⟨l, hl⟩ := h (tag i)
    obtain ⟨htag, hx⟩ := word_eq.mp hl
    rwa [hi htag] at hx

private theorem sorted_iff {α : Type*} [LinearOrder α] (x : Fin n → α)
    (tag : Fin n → Fin n) (y : Fin n → α) :
    (Bijective tag ∧ (∀ i, x i = y (tag i)) ∧ StrictMono y) ↔
      Injective x ∧ tag = (Tuple.sort x).symm ∧ y = x ∘ Tuple.sort x := by
  constructor
  · rintro ⟨ht, hxy, hy⟩
    let p := Equiv.ofBijective tag ht
    have hpy : x ∘ p.symm = y := funext fun j => by
      change x (p.symm j) = y j
      rw [hxy (p.symm j)]
      exact congrArg y (p.apply_symm_apply j)
    have hinj : Injective x := fun i j e =>
      ht.1 (hy.injective ((hxy i).symm.trans (e.trans (hxy j))))
    have hsorted : y = x ∘ Tuple.sort x := by
      rw [← hpy]
      exact Tuple.comp_sort_eq_comp_iff_monotone.mpr (hpy ▸ hy.monotone)
    refine ⟨hinj, funext fun i => (Tuple.sort x).eq_symm_apply.mpr (hinj ?_), hsorted⟩
    exact (congrFun hsorted (tag i)).symm.trans (hxy i).symm
  · rintro ⟨hx, rfl, rfl⟩
    exact ⟨(Tuple.sort x).symm.bijective, fun i => by simp,
      (Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)⟩

open scoped Classical in
/-- Summing over the destination tags and the sorted output table recovers distinctness.
The outputs are ordered by the binary value of each word, least significant bit first. -/
public theorem elementDistinctness_eq_sum_sortedPermutations (R : Type*) [AddCommMonoid R] [One R]
    (x : BitString (n * k)) :
    (if elementDistinctness n k x then (1 : R) else 0) =
      ∑ tag : Fin n → Fin n, ∑ y : Fin n → Fin (2 ^ k),
        if Bijective tag ∧ (∀ i, BitString.equivFin k (BitString.block x i) = y (tag i)) ∧
            StrictMono y then 1 else 0 := by
  classical
  let w := BitString.equivFin k ∘ BitString.block x
  change _ = ∑ tag : Fin n → Fin n, ∑ y : Fin n → Fin (2 ^ k),
    if Bijective tag ∧ (∀ i, w i = y (tag i)) ∧ StrictMono y then 1 else 0
  simp only [elementDistinctness, decide_eq_true_eq, sorted_iff, w]
  by_cases hx : Injective (BitString.block x) <;> simp [hx, ite_and]

end Cslib.Circuits.Boolean.ElementDistinctness

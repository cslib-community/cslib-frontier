/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Foundations.Data.List.ListsUpTo
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Total length of finite families of lists

A family of lists over a finite alphabet must have large total length when each list occurs
only a bounded number of times. The existing `List.listsUpTo` enumeration contains all lists
shorter than `L` and has at most `(|β| + 1) ^ L` entries over the full alphabet `β`.

## Main results

* `Finset.card_sub_mul_pow_mul_le_sum_length`: if every fiber has at most `M` elements, then
  the total length is at least `(|s| - M (|β| + 1) ^ L) L`.
* `Finset.card_sub_pow_mul_le_sum_length`: the specialization to pairwise distinct lists.
-/

public section

namespace Finset

/-- At most `(|β| + 1) ^ L` elements have pairwise distinct images that are lists of length
`< L` over `β`. -/
private lemma card_filter_length_lt_le {ι β : Type*} [Fintype β] {s : Finset ι}
    {f : ι → List β} (hf : Set.InjOn f s) (L : ℕ) :
    (s.filter fun x => (f x).length < L).card ≤ (Fintype.card β + 1) ^ L := by
  classical
  let words := List.listsUpTo (univ.toList : List β) L
  calc (s.filter fun x => (f x).length < L).card ≤ words.toFinset.card :=
      card_le_card_of_injOn f
        (fun x hx => List.mem_toFinset.mpr (List.mem_listsUpTo.mpr
          ⟨(mem_filter.mp hx).2.le, fun _ _ => by simp⟩))
        (hf.mono fun _ hx => (mem_filter.mp hx).1)
    _ ≤ words.length := List.toFinset_card_le _
    _ ≤ (Fintype.card β + 1) ^ L := by
        simpa only [length_toList, card_univ] using
          List.length_listsUpTo_le (univ.toList : List β) L

/-- If each list occurs at most `M` times in a finite family over `β`, then all but
`M (|β| + 1) ^ L` members have length at least `L`. Consequently the total length is at least
`(|s| - M (|β| + 1) ^ L) L`, including when `M` or `L` is zero. -/
theorem card_sub_mul_pow_mul_le_sum_length {ι β : Type*} [Fintype β] [DecidableEq β] {s : Finset ι}
    {f : ι → List β} {M : ℕ}
    (hf : ∀ l, (s.filter fun x => f x = l).card ≤ M) (L : ℕ) :
    (s.card - M * (Fintype.card β + 1) ^ L) * L ≤ ∑ x ∈ s, (f x).length := by
  classical
  let short := s.filter fun x => (f x).length < L
  let values := (s.image f).filter fun l => l.length < L
  have hmap : (short : Set ι).MapsTo f values := by
    intro x hx
    obtain ⟨hs, hlen⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_image_of_mem f hs, hlen⟩
  have hvalues : values.card ≤ (Fintype.card β + 1) ^ L :=
    card_filter_length_lt_le (f := id) (fun _ _ _ _ h => h) L
  have hbad : short.card ≤ M * (Fintype.card β + 1) ^ L := calc
    short.card = ∑ l ∈ values, (short.filter fun x => f x = l).card :=
      card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _ ∈ values, M := sum_le_sum fun l _ =>
      (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hf l)
    _ = M * values.card := by simp [Nat.mul_comm]
    _ ≤ M * (Fintype.card β + 1) ^ L := Nat.mul_le_mul_left M hvalues
  change (s.filter fun x => (f x).length < L).card ≤ _ at hbad
  have hsplit := card_filter_add_card_filter_not (s := s) (fun x => (f x).length < L)
  calc (s.card - M * (Fintype.card β + 1) ^ L) * L
      ≤ (s.filter fun x => ¬ (f x).length < L).card * L := Nat.mul_le_mul_right _ (by omega)
    _ ≤ ∑ x ∈ s.filter fun x => ¬ (f x).length < L, (f x).length := by
        rw [← Nat.nsmul_eq_mul]
        exact card_nsmul_le_sum _ _ _ fun x hx => by
          rw [mem_filter] at hx
          omega
    _ ≤ ∑ x ∈ s, (f x).length :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _

/-- Pairwise distinct lists over a finite alphabet `β` have total length at least
`(|s| - (|β| + 1) ^ L) L`. -/
theorem card_sub_pow_mul_le_sum_length {ι β : Type*} [Fintype β] {s : Finset ι}
    {f : ι → List β} (hf : Set.InjOn f s) (L : ℕ) :
    (s.card - (Fintype.card β + 1) ^ L) * L ≤ ∑ x ∈ s, (f x).length := by
  classical
  have h := card_sub_mul_pow_mul_le_sum_length (M := 1) (s := s) (f := f) (fun l => ?_) L
  · simpa only [one_mul] using h
  · refine card_le_one.mpr fun x hx y hy => ?_
    obtain ⟨hx, hfx⟩ := mem_filter.mp hx
    obtain ⟨hy, hfy⟩ := mem_filter.mp hy
    exact hf hx hy (hfx.trans hfy.symm)

end Finset

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith

/-!
# Small hitting sets for families of large sets

Let `S i ⊆ X`, for `i ∈ I`, be sets of at least `r²` elements each, with `r ≥ 1`. Then some
`P ⊆ X` meets every `S i` and has `|P| r ≤ |I| + |X|` (`Cslib.exists_hittingSet_card_mul_le`).
With `|I| ≤ |X| = n` this is a hitting set of at most `2n / r` elements.

The proof is the greedy argument of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (§3.2,
p. 15), where it selects the new portals of the batch procedure. While some element lies in at
least `r` of the sets not yet hit, take it; each such step hits at least `r` more sets, so at most
`|I| / r` steps are taken. Afterwards every element lies in fewer than `r` of the remaining sets,
which therefore have fewer than `|X| r` incidences in total; since each has at least `r²`
elements, fewer than `|X| / r` sets remain, and one element of each finishes the hitting set.

## Main results

* `Cslib.exists_hittingSet_card_mul_le`: a hitting set `P ⊆ X` with `|P| r ≤ |I| + |X|`.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.2, p. 15.
-/

public section

namespace Cslib

open Finset

/-- **Small hitting sets**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (the
portal selection of the batch procedure, §3.2, p. 15). If `r ≥ 1` and the sets `S i ⊆ X`, for
`i ∈ I`, each have at least `r²` elements, then some `P ⊆ X` meets every `S i` and has
`|P| r ≤ |I| + |X|`. -/
theorem exists_hittingSet_card_mul_le {ι α : Type*} [DecidableEq α] (X : Finset α)
    (I : Finset ι) (S : ι → Finset α) {r : ℕ} (hr : 0 < r) (hS : ∀ i ∈ I, S i ⊆ X)
    (hcard : ∀ i ∈ I, r ^ 2 ≤ #(S i)) :
    ∃ P ⊆ X, (∀ i ∈ I, (P ∩ S i).Nonempty) ∧ #P * r ≤ #I + #X := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  by_cases h : ∃ x ∈ X, r ≤ #{i ∈ I | x ∈ S i}
  · -- greedy step: take an element lying in at least `r` of the sets
    obtain ⟨x, hx, hrx⟩ := h
    obtain ⟨i₀, hi₀⟩ : ({i ∈ I | x ∈ S i} : Finset ι).Nonempty := card_pos.1 (hr.trans_le hrx)
    have hsub : ({i ∈ I | x ∉ S i} : Finset ι) ⊂ I :=
      (ssubset_iff_of_subset (filter_subset _ _)).2
        ⟨i₀, (mem_filter.1 hi₀).1, fun h => (mem_filter.1 h).2 (mem_filter.1 hi₀).2⟩
    obtain ⟨P, hPX, hP, hPc⟩ := ih _ hsub (fun i hi => hS i (mem_filter.1 hi).1)
      (fun i hi => hcard i (mem_filter.1 hi).1)
    refine ⟨insert x P, insert_subset hx hPX, fun i hi => ?_, ?_⟩
    · by_cases hxi : x ∈ S i
      · exact ⟨x, mem_inter.2 ⟨mem_insert_self _ _, hxi⟩⟩
      · obtain ⟨y, hy⟩ := hP i (mem_filter.2 ⟨hi, hxi⟩)
        exact ⟨y, mem_inter.2 ⟨mem_insert_of_mem (mem_inter.1 hy).1, (mem_inter.1 hy).2⟩⟩
    · have hsplit := card_filter_add_card_filter_not (s := I) (fun i => x ∈ S i)
      have hins := card_insert_le x P
      calc #(insert x P) * r ≤ (#P + 1) * r := Nat.mul_le_mul_right _ hins
        _ = #P * r + r := Nat.succ_mul _ _
        _ ≤ #I + #X := by omega
  · -- every element lies in fewer than `r` of the sets: take one element of each
    push Not at h
    have hne : ∀ i ∈ I, ∃ x, x ∈ S i := fun i hi =>
      card_pos.1 ((Nat.one_le_pow _ _ hr).trans (hcard i hi))
    choose f hf using hne
    refine ⟨I.attach.image fun i => f i.1 i.2, fun x hx => ?_, fun i hi => ⟨f i hi, ?_⟩, ?_⟩
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      exact hS i.1 i.2 (hf i.1 i.2)
    · exact mem_inter.2 ⟨mem_image.2 ⟨⟨i, hi⟩, mem_attach _ _, rfl⟩, hf i hi⟩
    · -- double counting: `|I| r² ≤ ∑ |S i| = ∑_{x ∈ X} #{i | x ∈ S i} ≤ |X| (r - 1)`
      have hdc : ∑ i ∈ I, #(S i) = ∑ x ∈ X, #{i ∈ I | x ∈ S i} := by
        have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := I) (t := X)
          (r := fun i x => x ∈ S i)
        simp only [bipartiteAbove, bipartiteBelow] at this
        rw [← this]
        refine sum_congr rfl fun i hi => ?_
        rw [filter_mem_eq_inter, inter_eq_right.2 (hS i hi)]
      have hlow : #I * r ^ 2 ≤ ∑ i ∈ I, #(S i) := by
        rw [mul_comm]
        exact card_nsmul_le_sum _ _ _ hcard |>.trans_eq' (by simp [mul_comm])
      have hup : ∑ x ∈ X, #{i ∈ I | x ∈ S i} ≤ #X * (r - 1) := by
        rw [mul_comm]
        exact (sum_le_card_nsmul _ _ _ fun x hx => Nat.le_sub_one_of_lt (h x hx)).trans_eq
          (by simp [mul_comm])
      have himg : #(I.attach.image fun i => f i.1 i.2) ≤ #I :=
        card_image_le.trans (card_attach).le
      have key : #I * r ≤ #X := by
        by_contra hlt
        push Not at hlt
        have h1 : (#X + 1) * r ≤ #I * r * r := Nat.mul_le_mul_right _ hlt
        have h2 : #I * r * r ≤ #X * (r - 1) := by
          rw [mul_assoc, ← sq]; exact hlow.trans (hdc ▸ hup)
        have h3 : #X * (r - 1) + #X * 1 = #X * r := by
          rw [← mul_add, Nat.sub_add_cancel hr]
        nlinarith
      calc #(I.attach.image fun i => f i.1 i.2) * r ≤ #I * r := Nat.mul_le_mul_right _ himg
        _ ≤ #I + #X := by omega

end Cslib

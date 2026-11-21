/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Forall2.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.Forall2

/-!
# Splitting aligned lists

Two lists aligned by `List.Forall₂ R` can be cut at matching positions: a cut of one side, as an
append or around a middle element, gives a cut of the other side with the same lengths, and the
parts stay aligned. Proofs that keep several lists aligned with one another, such as the chains,
hole triples and runs of a search, split them all around the element that changes.

## Main results

* `List.Forall₂.split_right`, `List.Forall₂.split_right_cons`, `List.Forall₂.split_left_cons`:
  cutting one side cuts the other.
* `List.Forall₂.split_of_length_eq`: two appends aligned with parts of equal lengths.
* `List.Forall₂.exists_mem_of_mem`: each element has an aligned partner.
-/

public section

namespace List.Forall₂

variable {α β : Type*} {R : α → β → Prop}

/-- An alignment with an append on the right is an append of alignments. -/
theorem split_right {l : List α} {pre post : List β} (h : Forall₂ R l (pre ++ post)) :
    ∃ a b, l = a ++ b ∧ a.length = pre.length ∧ Forall₂ R a pre ∧ Forall₂ R b post := by
  refine ⟨l.take pre.length, l.drop pre.length, (take_append_drop _ _).symm, ?_,
    forall₂_take_append _ _ _ h, forall₂_drop_append _ _ _ h⟩
  have := h.length_eq
  simp only [length_append, length_take] at this ⊢
  omega

/-- An alignment with a middle element on the right has an aligned middle element on the left. -/
theorem split_right_cons {l : List α} {pre post : List β} {x : β}
    (h : Forall₂ R l (pre ++ x :: post)) :
    ∃ a y b, l = a ++ y :: b ∧ a.length = pre.length ∧ Forall₂ R a pre ∧ R y x ∧
      Forall₂ R b post := by
  obtain ⟨a, b, rfl, hlen, ha, hb⟩ := h.split_right
  cases hb with
  | cons hy hb => exact ⟨a, _, _, rfl, hlen, ha, hy, hb⟩

/-- An alignment with a middle element on the left has an aligned middle element on the right. -/
theorem split_left_cons {pre post : List α} {x : α} {l : List β}
    (h : Forall₂ R (pre ++ x :: post) l) :
    ∃ a y b, l = a ++ y :: b ∧ a.length = pre.length ∧ Forall₂ R pre a ∧ R x y ∧
      Forall₂ R post b := by
  obtain ⟨a, y, b, rfl, hlen, ha, hy, hb⟩ := h.flip.split_right_cons
  exact ⟨a, y, b, rfl, hlen, ha.flip, hy, hb.flip⟩

/-- Every element of the left list has an aligned element in the right list. -/
theorem exists_mem_of_mem {a : List α} {b : List β} (h : Forall₂ R a b) {x : α} (hx : x ∈ a) :
    ∃ y ∈ b, R x y := by
  induction h with
  | nil => simp at hx
  | cons hxy _ ih =>
    rcases mem_cons.mp hx with rfl | hx
    · exact ⟨_, mem_cons_self, hxy⟩
    · obtain ⟨y, hy, hxy'⟩ := ih hx
      exact ⟨y, mem_cons_of_mem _ hy, hxy'⟩

/-- Two aligned appends whose first parts have equal lengths are aligned part by part. -/
theorem split_of_length_eq {a a' : List α} {b b' : List β} (hlen : a.length = b.length)
    (h : Forall₂ R (a ++ a') (b ++ b')) : Forall₂ R a b ∧ Forall₂ R a' b' := by
  have h₁ := forall₂_take a.length h
  have h₂ := forall₂_drop a.length h
  rw [take_left, hlen, take_left] at h₁
  rw [drop_left, hlen, drop_left] at h₂
  exact ⟨h₁, h₂⟩

end List.Forall₂

/-
Copyright (c) 2026 Samuel Schlesinger, Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Sam
-/

module
-- upstream: candidate (Mathlib, stable sorting)

public import CslibFrontier.Init
public import Mathlib.Data.List.Sort

/-!
# Agreement of stable merge sort and insertion sort

For a total transitive relation, merge sort and insertion sort return the same list, including
the order of elements tied by the relation. This connects a divide-and-conquer implementation
to the right fold used by insertion sort, for both symbolic proofs and machine certificates.
-/

public section

namespace List

private theorem orderedInsert_append_eq {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (a : α) : ∀ (l₁ l₂ : List α),
      (∀ b ∈ l₁, ¬ r a b) → (∀ c ∈ l₂, r a c) →
      List.orderedInsert r a (l₁ ++ l₂) = l₁ ++ a :: l₂
  | [], [], _, _ => by simp
  | [], c :: l₂, _, hl₂ => by
    simp [hl₂ c List.mem_cons_self]
  | b :: l₁, l₂, hl₁, hl₂ => by
    have hnb : ¬ r a b := hl₁ b List.mem_cons_self
    simp [hnb, orderedInsert_append_eq r a l₁ l₂ (fun x hx => hl₁ x (List.mem_cons_of_mem b hx))
      hl₂]

/-- The two stable sorts agree for every total transitive relation, even when distinct entries
are tied. -/
theorem mergeSort_decide_eq_insertionSort {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (htotal : ∀ a b, r a b ∨ r b a) :
    ∀ xs : List α, xs.mergeSort (fun a b => decide (r a b)) = xs.insertionSort r
  | [] => by simp
  | a :: l => by
    have tr : ∀ x y z, decide (r x y) = true → decide (r y z) = true →
        decide (r x z) = true := by grind
    have tot : ∀ x y, (decide (r x y) || decide (r y x)) = true := by grind
    obtain ⟨l₁, l₂, hcons, hl, hnot⟩ := List.mergeSort_cons tr tot a l
    have hpw : (l₁ ++ a :: l₂).Pairwise (fun x y => decide (r x y) = true) :=
      hcons ▸ List.pairwise_mergeSort tr tot (a :: l)
    have hl₂ : ∀ c ∈ l₂, r a c := fun c hc =>
      of_decide_eq_true ((List.pairwise_cons.mp (List.pairwise_append.mp hpw).2.1).1 c hc)
    have hl₁ : ∀ b ∈ l₁, ¬ r a b := fun b hb hrab => by
      have hnb := hnot b hb
      simp [hrab] at hnb
    rw [hcons, List.insertionSort_cons, ← mergeSort_decide_eq_insertionSort r htrans htotal l, hl]
    exact (orderedInsert_append_eq r a l₁ l₂ hl₁ hl₂).symm

end List

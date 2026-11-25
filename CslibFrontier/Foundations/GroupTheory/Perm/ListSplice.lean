/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/List)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.List

/-!
# Literal directed word equations for joining and splitting cycles

An outgoing successor swap concatenates two nonempty directed words at their last points.
The converse isolates an adjacent pair inside a word while retaining the remaining positive
cyclic order. Joining immediately before or after two markers and then skipping the second
marker gives the two orders of the retained blocks.
-/

public section

namespace List

open Equiv

variable {α : Type*} [DecidableEq α]

private theorem formPerm_append_comm {u v : List α} (h : (u ++ v).Nodup) :
    (u ++ v).formPerm = (v ++ u).formPerm :=
  List.formPerm_eq_of_isRotated h List.isRotated_append

/-- Joining the outgoing successors of the last points concatenates the directed words.
Only the last left point must be absent from the right word; no ambient finiteness is needed. -/
theorem formPerm_append_of_last_notMem (left right : List α) (hl : left ≠ []) (hr : right ≠ [])
    (h : left.getLast hl ∉ right) :
    (left ++ right).formPerm = left.formPerm * right.formPerm *
      Equiv.swap (left.getLast hl) (right.getLast hr) := by
  rcases left with _ | ⟨a, left⟩
  · exact (hl rfl).elim
  rcases right with _ | ⟨b, right⟩
  · exact (hr rfl).elim
  induction left generalizing a with
  | nil =>
    simp only [List.cons_append, List.nil_append, List.getLast_singleton,
      List.formPerm_singleton, one_mul] at h ⊢
    rw [Equiv.mul_swap_eq_swap_mul, List.formPerm_apply_of_notMem h, List.formPerm_apply_getLast]
    rfl
  | cons x left ih =>
    simp only [List.getLast_cons_cons] at h ⊢
    change Equiv.swap a x * ((x :: left) ++ (b :: right)).formPerm =
      (a :: x :: left).formPerm * (b :: right).formPerm *
        Equiv.swap ((x :: left).getLast (by simp)) ((b :: right).getLast hr)
    rw [ih x (by simp) h, List.formPerm_cons_cons]; simp only [mul_assoc]

/-- Splitting an adjacent pair off a directed word is the inverse of joining its two-point
cycle to the remaining word at the literal predecessor corner. The remaining order is unchanged. -/
theorem formPerm_split_adjacent_pair (left right : List α) (a b : α) (hl : left ≠ [])
    (hn : ((left ++ [a, b]) ++ right).Nodup) :
    ((left ++ [a, b]) ++ right).formPerm =
      (left ++ right).formPerm * Equiv.swap a b * Equiv.swap (left.getLast hl) b := by
  have hrot : ((right ++ left) ++ [a, b]).Nodup := by
    simpa only [List.append_assoc] using List.perm_append_comm.nodup_iff.mp hn
  have hsplit := List.nodup_append'.mp hrot
  have hrest : right ++ left ≠ [] := by simp [hl]
  have hword : ((left ++ [a, b]) ++ right).formPerm = ((right ++ left) ++ [a, b]).formPerm := by
    simpa only [List.append_assoc] using formPerm_append_comm hn
  rw [hword, formPerm_append_of_last_notMem _ _ hrest (by simp)
      (List.disjoint_left.mp hsplit.2.2 (List.getLast_mem _)),
    formPerm_append_comm hsplit.1, List.formPerm_pair, List.getLast_append_of_ne_nil _ hl,
    List.getLast_cons_cons, List.getLast_singleton]

-- After deleting one letter, its predecessor continues with its old successor.
private theorem formPerm_skip_letter (left right : List α) (b x y : α)
    (hn : (left ++ b :: right).Nodup) (hx : x ≠ b) (hy : y ≠ b) :
    (left ++ right).formPerm x = y ↔ (left ++ b :: right).formPerm x = y ∨
      (left ++ b :: right).formPerm x = b ∧ (left ++ b :: right).formPerm b = y := by
  by_cases hempty : right ++ left = []
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hempty; simp [hx]
  have hn' : ((left ++ [b]) ++ right).Nodup := by simpa using hn
  have hrot : ((right ++ left) ++ [b]).Nodup := by
    simpa only [List.append_assoc] using List.perm_append_comm.nodup_iff.mp hn'
  have hparts := List.nodup_append'.mp hrot
  have hb : b ∉ right ++ left := fun hm => List.disjoint_left.mp hparts.2.2 hm (by simp)
  let p := (right ++ left).getLast hempty
  let g := (left ++ right).formPerm
  have hf : (left ++ b :: right).formPerm = g * Equiv.swap p b := by
    have he : (left ++ b :: right).formPerm = ((right ++ left) ++ [b]).formPerm := by
      simpa only [List.append_assoc, List.singleton_append] using formPerm_append_comm hn'
    rw [he, formPerm_append_of_last_notMem _ _ hempty (by simp)
        (List.disjoint_left.mp hparts.2.2 (List.getLast_mem _)),
      formPerm_append_comm hparts.1]
    simp [p, g]
  have hfix : g b = b :=
    List.formPerm_apply_of_notMem (by simpa only [List.mem_append, or_comm] using hb)
  rcases eq_or_ne x p with rfl | hxp
  · simp [hf, hfix, Ne.symm hy]; rfl
  · simp [hf, Equiv.swap_apply_of_ne_of_ne hxp hx,
      show g x ≠ b from fun he => hx (g.injective (he.trans hfix.symm))]; rfl

/-- Join two directed cycles at their marked letters and suppress the second marker.
Swapping immediately before both markers places `left` then `right` after `a`. Swapping
immediately after both markers places `right` then `left` after `a`. The equivalences
describe the literal successor after skipping `b`, including empty blocks. -/
theorem formPerm_join_skip_marker_iff (left right : List α) (a b x y : α)
    (hn : ((a :: left) ++ (b :: right)).Nodup) (hx : x ≠ b) (hy : y ≠ b) :
    let g := (a :: left).formPerm * (b :: right).formPerm
    let before := g * Equiv.swap ((a :: left).getLast (by simp)) ((b :: right).getLast (by simp))
    let after := g * Equiv.swap a b
    ((a :: (left ++ right)).formPerm x = y ↔ before x = y ∨ before x = b ∧ before b = y) ∧
      ((a :: (right ++ left)).formPerm x = y ↔ after x = y ∨ after x = b ∧ after b = y) := by
  dsimp only
  have hparts := List.nodup_append'.mp hn
  have hswap := formPerm_append_of_last_notMem (a :: left) (b :: right) (by simp) (by simp)
    (List.disjoint_left.mp hparts.2.2 (List.getLast_mem _))
  refine ⟨hswap ▸ formPerm_skip_letter (a :: left) right b x y hn hx hy, ?_⟩
  have hnot : a ∉ right ++ [b] := by
    simpa [or_comm] using List.disjoint_left.mp hparts.2.2 (List.mem_cons_self ..)
  have ha : ((left ++ [a]) ++ (right ++ [b])).formPerm =
      (a :: left).formPerm * (b :: right).formPerm * Equiv.swap a b := by
    rw [formPerm_append_of_last_notMem _ _ (by simp) (by simp)
        (by simpa [List.getLast_append_of_ne_nil] using hnot),
      ← formPerm_append_comm (u := [a]) hparts.1,
      ← formPerm_append_comm (u := [b]) hparts.2.1]
    simp [List.getLast_append_of_ne_nil]
  have hperm : ((a :: left) ++ (b :: right)).Perm ((a :: right) ++ b :: left) :=
    List.Perm.cons a (List.perm_append_comm.trans
      (by simpa [List.append_assoc] using
        (List.perm_append_comm (l₁ := [b]) (l₂ := right)).append_right left))
  have hn' := hperm.nodup_iff.mp hn
  have hturn : ((left ++ [a]) ++ (right ++ [b])).formPerm =
      ((a :: right) ++ b :: left).formPerm := by
    simpa [List.append_assoc] using (formPerm_append_comm (u := (a :: right) ++ [b]) (v := left)
      (by simpa [List.append_assoc] using hn')).symm
  rw [← ha, hturn]
  exact formPerm_skip_letter (a :: right) left b x y hn' hx hy

end List

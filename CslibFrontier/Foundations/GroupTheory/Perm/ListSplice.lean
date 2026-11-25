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
    rw [Equiv.mul_swap_eq_swap_mul, List.formPerm_apply_of_notMem h,
      List.formPerm_apply_getLast]
    rfl
  | cons x left ih =>
    simp only [List.getLast_cons_cons] at h ⊢
    change Equiv.swap a x * ((x :: left) ++ (b :: right)).formPerm =
      (a :: x :: left).formPerm * (b :: right).formPerm *
        Equiv.swap ((x :: left).getLast (by simp)) ((b :: right).getLast hr)
    rw [ih x (by simp) h, List.formPerm_cons_cons]
    simp only [mul_assoc]

/-- Splitting an adjacent pair off a directed word is the inverse of joining its two-point
cycle to the remaining word at the literal predecessor corner. The remaining order is unchanged. -/
theorem formPerm_split_adjacent_pair (left right : List α) (a b : α) (hl : left ≠ [])
    (hn : ((left ++ [a, b]) ++ right).Nodup) :
    ((left ++ [a, b]) ++ right).formPerm =
      (left ++ right).formPerm * Equiv.swap a b * Equiv.swap (left.getLast hl) b := by
  have hrot : ((right ++ left) ++ [a, b]).Nodup := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := left ++ [a, b]) (l₂ := right)).nodup_iff.mp hn
  have hsplit := List.nodup_append'.mp hrot
  have hrest : right ++ left ≠ [] := by simp [hl]
  have hnot : (right ++ left).getLast hrest ∉ [a, b] := by
    intro hm
    exact List.disjoint_left.mp hsplit.2.2 (List.getLast_mem _) hm
  have hword : ((left ++ [a, b]) ++ right).formPerm =
      ((right ++ left) ++ [a, b]).formPerm := by
    simpa only [List.append_assoc] using
      List.formPerm_eq_of_isRotated hn (List.isRotated_append (l := left ++ [a, b]))
  rw [hword, formPerm_append_of_last_notMem _ _ hrest (by simp) hnot,
    List.formPerm_pair, List.getLast_append_of_ne_nil _ hl]
  have hrem := List.formPerm_eq_of_isRotated hsplit.1
    (List.isRotated_append (l := right) (l' := left))
  simp only [hrem, List.getLast_cons_cons, List.getLast_singleton]

-- After deleting one letter, its predecessor continues with its old successor.
private theorem formPerm_skip_letter (left right : List α) (b x y : α)
    (hn : (left ++ b :: right).Nodup) (hx : x ≠ b) (hy : y ≠ b) :
    (left ++ right).formPerm x = y ↔ (left ++ b :: right).formPerm x = y ∨
      (left ++ b :: right).formPerm x = b ∧ (left ++ b :: right).formPerm b = y := by
  by_cases hempty : right ++ left = []
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hempty
    simp [hx]
  have hn' : ((left ++ [b]) ++ right).Nodup := by
    simpa only [List.append_assoc, List.singleton_append] using hn
  have hrot : ((right ++ left) ++ [b]).Nodup := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := left ++ [b]) (l₂ := right)).nodup_iff.mp hn'
  have hparts := List.nodup_append'.mp hrot
  have hb : b ∉ right ++ left := fun hm => List.disjoint_left.mp hparts.2.2 hm (by simp)
  let p := (right ++ left).getLast hempty
  let g := (left ++ right).formPerm
  have hf : (left ++ b :: right).formPerm = g * Equiv.swap p b := by
    have he : (left ++ b :: right).formPerm = ((right ++ left) ++ [b]).formPerm := by
      simpa only [List.append_assoc, List.singleton_append] using List.formPerm_eq_of_isRotated hn'
        (List.isRotated_append (l := left ++ [b]) (l' := right))
    rw [he, formPerm_append_of_last_notMem _ _ hempty (by simp)
      (by
        intro hm
        have heq : (right ++ left).getLast hempty = b := List.mem_singleton.mp hm
        exact hb (heq ▸ List.getLast_mem hempty))]
    rw [List.formPerm_eq_of_isRotated hparts.1 (List.isRotated_append (l := right) (l' := left))]
    simp only [List.formPerm_singleton, mul_one, List.getLast_singleton, p, g]
  have hfix : g b = b :=
    List.formPerm_apply_of_notMem (by simpa only [List.mem_append, or_comm] using hb)
  rcases eq_or_ne x p with rfl | hxp
  · simp only [hf, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      hfix, Ne.symm hy, false_or, true_and]
    rfl
  · have hne : g x ≠ b := fun he => hx (g.injective (he.trans hfix.symm))
    simp only [hf, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxp hx, hne,
      false_and, or_false]
    rfl

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
    (fun hm => List.disjoint_left.mp hparts.2.2 (List.getLast_mem _) hm)
  constructor
  · rw [← hswap]
    exact formPerm_skip_letter (a :: left) right b x y hn hx hy
  · have hl : (left ++ [a]).formPerm = (a :: left).formPerm :=
      (List.formPerm_eq_of_isRotated hparts.1 (List.isRotated_append (l := [a]) (l' := left))).symm
    have hr : (right ++ [b]).formPerm = (b :: right).formPerm :=
      (List.formPerm_eq_of_isRotated hparts.2.1
        (List.isRotated_append (l := [b]) (l' := right))).symm
    have hnot : a ∉ right ++ [b] := by
      rw [List.mem_append, List.mem_singleton, or_comm, ← List.mem_cons]
      exact List.disjoint_left.mp hparts.2.2 (List.mem_cons_self ..)
    have ha : ((left ++ [a]) ++ (right ++ [b])).formPerm =
        (a :: left).formPerm * (b :: right).formPerm * Equiv.swap a b := by
      rw [formPerm_append_of_last_notMem _ _ (by simp) (by simp)
        (by simpa only [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _),
          List.getLast_singleton] using hnot), hl, hr]
      simp only [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast_singleton]
    have hperm : ((a :: left) ++ (b :: right)).Perm ((a :: right) ++ b :: left) := by
      simp only [List.cons_append]
      apply List.Perm.cons
      calc
        left ++ (b :: right) ~ (b :: right) ++ left := List.perm_append_comm
        _ ~ right ++ b :: left := by
          simpa only [List.append_assoc, List.singleton_append] using
            (List.perm_append_comm (l₁ := [b]) (l₂ := right)).append_right left
    have hturn : ((left ++ [a]) ++ (right ++ [b])).formPerm =
        ((a :: right) ++ b :: left).formPerm := by
      have hnafter : (left ++ ((a :: right) ++ [b])).Nodup := by
        apply (List.perm_append_comm (l₁ := ((a :: right) ++ [b])) (l₂ := left)).nodup_iff.mp
        simpa only [List.append_assoc, List.singleton_append] using hperm.nodup_iff.mp hn
      simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using
        List.formPerm_eq_of_isRotated hnafter
          (List.isRotated_append (l := left) (l' := (a :: right) ++ [b]))
    rw [← ha, hturn]
    exact formPerm_skip_letter (a :: right) left b x y (hperm.nodup_iff.mp hn) hx hy

end List

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.Basic
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Levenshtein distance on words

A `SingleEdit` inserts, deletes, or changes one letter anywhere in the current word.
`isLeast_editDist_unit` identifies the Wagner–Fischer table entry with the minimum length of
a sequence of such edits through arbitrary intermediate words. This is the unit-cost case of
[Wagner and Fischer, §3, Theorem 1, p. 171][WagnerFischer1974].
Each alignment gives a sequence of the same cost, and every sequence bounds the distance.
Reversing and joining sequences gives symmetry and the triangle inequality.
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

open Relation EditScript

variable {α : Type*}

/-- One insertion, deletion, or replacement by a different letter in the current word.
The `cons` constructor skips a common first letter and permits edits at any later position. -/
inductive SingleEdit : List α → List α → Prop where
  /-- Insert a letter at the front. -/
  | ins (b : α) (xs : List α) : SingleEdit xs (b :: xs)
  /-- Delete the front letter. -/
  | del (a : α) (xs : List α) : SingleEdit (a :: xs) xs
  /-- Change the front letter, keeping the tail. -/
  | sub {a b : α} (h : a ≠ b) (xs : List α) : SingleEdit (a :: xs) (b :: xs)
  /-- Perform the edit after a common first letter. -/
  | cons (a : α) {xs ys : List α} (h : SingleEdit xs ys) : SingleEdit (a :: xs) (a :: ys)

theorem SingleEdit.symm {x y : List α} (h : SingleEdit x y) : SingleEdit y x := by
  induction h with
  | ins b xs => exact .del b xs
  | del a xs => exact .ins a xs
  | sub h xs => exact .sub h.symm xs
  | cons a _ ih => exact .cons a ih

variable [DecidableEq α]

/-- Realize any alignment by exactly one edit per charged operation. -/
theorem EditScript.relatesInSteps_unit (s : EditScript α) :
    RelatesInSteps SingleEdit (src s) (tgt s) (cost Costs.unit s) := by
  induction s with
  | nil => simp
  | cons o s ih =>
    have keep (b : α) := ih.map (List.cons b) (fun _ _ h => SingleEdit.cons b h)
    cases o with
    | del a => simpa [EditOp.cost, EditOp.src, EditOp.tgt, Nat.add_comm] using
        RelatesInSteps.head _ _ _ _ (SingleEdit.del a (src s)) ih
    | ins b => simpa [EditOp.cost, EditOp.src, EditOp.tgt, Nat.add_comm] using
        RelatesInSteps.head _ _ _ _ (SingleEdit.ins b (src s)) (keep b)
    | sub a b =>
      by_cases h : a = b
      · subst b
        simpa [EditOp.cost, EditOp.src, EditOp.tgt] using keep a
      · simpa [EditOp.cost, EditOp.src, EditOp.tgt, h, Nat.add_comm] using
          RelatesInSteps.head _ _ _ _ (SingleEdit.sub h (src s)) (keep b)

-- Move one edit into an alignment. A deletion on the source consumes no target letter.
-- When both operations consume the target head, the tail alignment is available unchanged.
private theorem dist_le_cost_succ (s : EditScript α) {z : List α} (h : SingleEdit (tgt s) z) :
    editDist Costs.unit (src s) z ≤ cost Costs.unit s + 1 := by
  induction s generalizing z with
  | nil =>
    rw [tgt_nil] at h
    cases h with
    | ins b => simp [editDist_nil_cons]
  | cons o s ih =>
    have tailBound := editDist_le_cost Costs.unit s
    have insert (c : α) := (editDist_cons_right_le Costs.unit c (src (o :: s)) (tgt (o :: s))).trans
      (Nat.add_le_add_left (editDist_le_cost Costs.unit (o :: s)) 1)
    cases o <;> simp only [src_cons, tgt_cons, cost_cons, EditOp.src, EditOp.tgt, EditOp.cost,
      List.singleton_append, List.nil_append, Costs.unit_ins, Costs.unit_del] at h insert ⊢
    case del a =>
      exact (editDist_cons_left_le Costs.unit a (src s) z).trans (by
        have := ih h
        simp only [Costs.unit_del]; omega)
    case ins b =>
      cases h with
      | ins c => simpa only [Nat.add_comm 1] using insert c
      | del => omega
      | sub _ => exact (editDist_cons_right_le Costs.unit _ _ _).trans (by simp; omega)
      | cons _ he => exact (editDist_cons_right_le Costs.unit _ _ _).trans (by
          have := ih he
          simp; omega)
    case sub a b =>
      cases h with
      | ins c => simpa only [Nat.add_comm 1] using insert c
      | del => exact (editDist_cons_left_le Costs.unit a (src s) (tgt s)).trans (by simp; omega)
      | sub _ => exact (editDist_cons_cons_le Costs.unit _ _ (src s) (tgt s)).trans (by
          simp only [Costs.unit_sub]; split <;> omega)
      | cons _ he =>
        exact (editDist_cons_cons_le Costs.unit a b _ _).trans (by have := ih he; omega)

/-- The Levenshtein distance from a word to itself is zero. -/
@[simp] theorem editDist_unit_self (x : List α) : editDist Costs.unit x x = 0 := by
  induction x with
  | nil => rfl
  | cons a x ih => simpa [ih] using editDist_cons_cons_le Costs.unit a a x x

/-- The Levenshtein distance is the minimum number of single-letter edits at arbitrary positions
in successive words ([Wagner and Fischer, §3, Theorem 1, p. 171][WagnerFischer1974], unit costs). -/
theorem isLeast_editDist_unit (x y : List α) :
    IsLeast {n | RelatesInSteps SingleEdit x y n} (editDist Costs.unit x y) := by
  constructor
  · simpa [cost_optScript] using (optScript Costs.unit x y).relatesInSteps_unit
  · intro n hn
    have bound := hn.apply_le_apply_add (editDist Costs.unit x) fun a b hab => by
      simpa [cost_optScript] using dist_le_cost_succ (optScript Costs.unit x a) (by simpa using hab)
    simpa using bound

/-- Levenshtein distance is symmetric because an edit sequence can be reversed. -/
theorem editDist_unit_comm (x y : List α) : editDist Costs.unit x y = editDist Costs.unit y x := by
  suffices rev : ∀ {a b : List α} {n}, RelatesInSteps SingleEdit a b n →
      RelatesInSteps SingleEdit b a n from
    le_antisymm ((isLeast_editDist_unit x y).2 (rev (isLeast_editDist_unit y x).1))
      ((isLeast_editDist_unit y x).2 (rev (isLeast_editDist_unit x y).1))
  intro a b n h
  induction h with
  | refl => exact .refl _
  | tail _ _ _ _ h ih => exact .head _ _ _ _ h.symm ih

/-- Joining two shortest sequences gives the triangle inequality for Levenshtein distance. -/
theorem editDist_unit_triangle (x y z : List α) :
    editDist Costs.unit x z ≤ editDist Costs.unit x y + editDist Costs.unit y z :=
  (isLeast_editDist_unit x z).2 <| (isLeast_editDist_unit x y).1.trans (isLeast_editDist_unit y z).1

/-- Two words have Levenshtein distance zero exactly when they agree. -/
@[simp] theorem editDist_unit_eq_zero_iff {x y : List α} : editDist Costs.unit x y = 0 ↔ x = y := by
  refine ⟨fun h => RelatesInSteps.zero (h ▸ (isLeast_editDist_unit x y).1), ?_⟩
  rintro rfl
  exact editDist_unit_self x

end Cslib.Algorithms.Lean.EditDistance

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/Option)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.GroupTheory.Perm.Doubled
public import Mathlib.GroupTheory.Perm.Option

/-!
# Inserting a point in a permutation cycle

`Equiv.Perm.Insertion.insertAfter` inserts an optional point immediately after a chosen
point. Exact successor equations, complete orbit correspondence and the `removeNone`
inverse include singleton cycles. The results are about arbitrary permutations and have
no graph dependency or geometric hypothesis.
-/

public section

namespace Equiv.Perm.Insertion

open Equiv

variable {α : Type} [DecidableEq α]

/-- Insert `none` after `h` in the cycle of `f`, preserving every other successor. -/
@[expose] def insertAfter (f : Perm α) (h : α) : Perm (Option α) :=
  f.optionCongr * swap (some h) none

/-- The chosen old dart leads to the inserted dart. -/
@[simp] theorem insertAfter_at (f : Perm α) (h : α) :
    insertAfter f h (some h) = none := by
  simp [insertAfter]

/-- The inserted dart leads to the old successor of its corner. -/
@[simp] theorem insertAfter_none (f : Perm α) (h : α) :
    insertAfter f h none = some (f h) := by
  simp [insertAfter]

/-- All other old successors remain literally unchanged. -/
theorem insertAfter_other (f : Perm α) (h a : α) (ha : a ≠ h) :
    insertAfter f h (some a) = some (f a) := by
  simp [insertAfter, swap_apply_of_ne_of_ne, ha]

/-- Collapse just the inserted dart to its preceding corner. -/
@[expose] def collapse (h : α) : Option α → α := Option.elim' h id

private theorem sameCycle_collapse_step (f : Perm α) (h : α) (x : Option α) :
    f.SameCycle (collapse h x) (collapse h (insertAfter f h x)) := by
  rcases x with _ | a
  · exact Perm.sameCycle_apply_right.mpr .rfl
  · by_cases ha : a = h
    · subst ha
      simpa [collapse] using (Perm.SameCycle.rfl : f.SameCycle a a)
    · simpa [insertAfter_other f h a ha, collapse] using
        Perm.sameCycle_apply_right.mpr (.rfl : f.SameCycle a a)

private theorem sameCycle_some_step (f : Perm α) (h a : α) :
    (insertAfter f h).SameCycle (some a) (some (f a)) := by
  by_cases ha : a = h
  · subst a
    have h₁ : (insertAfter f h).SameCycle (some h) none := by
      rw [← insertAfter_at f h]
      exact Perm.sameCycle_apply_right.mpr .rfl
    have h₂ : (insertAfter f h).SameCycle none (some (f h)) := by
      rw [← insertAfter_none f h]
      exact Perm.sameCycle_apply_right.mpr .rfl
    exact h₁.trans h₂
  · rw [← insertAfter_other f h a ha]
    exact Perm.sameCycle_apply_right.mpr .rfl

/-- Insertion preserves exactly the old cycles, and places the new dart in the corner's cycle.
This includes singleton cycles and makes no distinct-vertex assumption. -/
theorem sameCycle_iff [Finite α] (f : Perm α) (h : α) (x y : Option α) :
    (insertAfter f h).SameCycle x y ↔ f.SameCycle (collapse h x) (collapse h y) := by
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
    clear hxy
    rw [← Perm.iterate_eq_pow]
    induction k with
    | zero => exact .rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (sameCycle_collapse_step f h _)
  · have lift {a b : α} (hab : f.SameCycle a b) :
        (insertAfter f h).SameCycle (some a) (some b) := by
      obtain ⟨k, rfl⟩ := hab.exists_nat_pow_eq
      clear hab
      rw [← Perm.iterate_eq_pow]
      induction k with
      | zero => exact .rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact ih.trans (sameCycle_some_step f h _)
    have link (z : Option α) : (insertAfter f h).SameCycle z (some (collapse h z)) := by
      rcases z with _ | a
      · rw [collapse, Option.elim'_none, ← insertAfter_at f h]
        exact Perm.sameCycle_apply_left.mpr .rfl
      · exact .rfl
    exact (link x).trans ((lift hxy).trans (link y).symm)

/-- Every cycle, including a fixed point, survives insertion exactly once. -/
noncomputable def orbitEquiv [Finite α] (f : Perm α) (h : α) :
    Quotient (Perm.SameCycle.setoid (insertAfter f h)) ≃
      Quotient (Perm.SameCycle.setoid f) where
  toFun := Quotient.map (collapse h) (fun _ _ => (sameCycle_iff f h _ _).mp)
  invFun := Quotient.map some (fun a b hab => (sameCycle_iff f h _ _).mpr hab)
  left_inv := by
    intro q
    refine Quotient.inductionOn q fun x => ?_
    apply Quotient.sound
    apply (sameCycle_iff f h _ _).mpr
    cases x <;> exact .rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q fun a => ?_
    rfl

/-- The number of all cycles is unchanged by inserting a dart in an existing cycle. -/
theorem card_orbits_insertAfter [Finite α] (f : Perm α) (h : α) :
    Nat.card (Quotient (Perm.SameCycle.setoid (insertAfter f h))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) :=
  Nat.card_congr (orbitEquiv f h)

/-- Deleting a non-singleton dart and reinserting it after its predecessor recovers the
literal permutation, including its orientation. `removeNone` is Mathlib's deletion. -/
theorem insertAfter_removeNone (f : Perm (Option α)) (h : α)
    (hh : f (some h) = none) : insertAfter (removeNone f) h = f := by
  apply Equiv.ext
  rintro (_ | a)
  · exact (insertAfter_none _ _).trans (removeNone_none f hh)
  · by_cases ha : a = h
    · subst ha
      exact (insertAfter_at _ _).trans hh.symm
    · rw [insertAfter_other _ _ _ ha]
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp fun he =>
        ha (Option.some.inj (f.injective (he.trans hh.symm)))
      exact removeNone_some f ⟨b, hb⟩

/-- A nonfixed optional point can be reinserted after its old predecessor. -/
private theorem exists_insertAfter_removeNone (f : Perm (Option α)) (hn : f none ≠ none) :
    ∃ h, insertAfter (removeNone f) h = f := by
  obtain ⟨h, hh⟩ := Option.ne_none_iff_exists'.mp fun he => hn (f.symm_apply_eq.mp he).symm
  exact ⟨h, insertAfter_removeNone f h (by rw [← hh, f.apply_symm_apply])⟩

omit [DecidableEq α] in
/-- Removing a dart from a cycle of length at least two preserves all remaining orbit
identifications; the two adjacent successors are joined with their original direction. -/
theorem sameCycle_removeNone_iff [Finite α] (f : Perm (Option α))
    (hn : f none ≠ none) (a b : α) :
    Perm.SameCycle (removeNone f) a b ↔ f.SameCycle (some a) (some b) := by
  classical
  obtain ⟨h, hf⟩ := exists_insertAfter_removeNone f hn
  conv_rhs => rw [← hf]
  rw [sameCycle_iff]
  rfl

omit [DecidableEq α] in
/-- Deleting a non-singleton dart preserves the total number of faces or vertex cycles. -/
theorem card_orbits_removeNone [Finite α] (f : Perm (Option α)) (hn : f none ≠ none) :
    Nat.card (Quotient (Perm.SameCycle.setoid (removeNone f))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) := by
  classical
  obtain ⟨h, hf⟩ := exists_insertAfter_removeNone f hn
  conv_rhs => rw [← hf]
  exact (card_orbits_insertAfter (removeNone f) h).symm

/-- Inserting two points gives the two literal outgoing-successor swaps. -/
theorem insertAfter_twice {α : Type} [DecidableEq α] (f : Perm α) (h k : α) :
    insertAfter (insertAfter f h) (some k) = f.optionCongr.optionCongr *
      swap (some (some h)) (some none) * swap (some (some k)) none := by
  have hm : (f.optionCongr * swap (some h) none).optionCongr =
      f.optionCongr.optionCongr * (swap (some h) none).optionCongr := by
    apply Equiv.ext
    rintro (_ | z) <;> rfl
  dsimp only [insertAfter]
  rw [hm, Equiv.optionCongr_swap]

end Equiv.Perm.Insertion

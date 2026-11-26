/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Prefix
public import CslibFrontier.Foundations.Data.List.MergeSort
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Tactic.PolyTime

/-!
# Uniform polynomial-time stable sorting

Insertion into a list is a first-match prefix scan. Insertion sort is a bounded fold: each step
adds exactly the framed encoding of one input element. Consequently insertion sort is uniformly
polynomial-time whenever comparison is, including comparisons that capture the original input.
For total transitive relations the stable merge-sort result agrees with insertion sort, giving
the same native machine certificate for `List.mergeSort` without changing its treatment of ties.
-/

public section

namespace Turing.MultiTapeTM

/-- A captured comparison uses `frame (frame (encIn x) ++ encA a) ++ encA b`: the input
and first argument form a framed pair, followed by the unframed second argument. -/
abbrev encCapturedComparison {α γ : Type} (encIn : γ ↪ List Bool) (encA : α ↪ List Bool) :
    ((γ × α) × α) ↪ List Bool :=
  encPair (encPair encIn encA) encA

namespace ComputableInPolyTime

variable {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
  {r : γ → α → α → Prop} [∀ x, DecidableRel (r x)]

/-- Insert before the first related entry, using a uniformly computable captured comparison. -/
theorem orderedInsertWithInput {list : γ → List α} {value : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA)
    (hrel : ComputableInPolyTime
      (fun p : (γ × α) × α => decide (r p.1.1 p.1.2 p.2))
      (encCapturedComparison encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).orderedInsert (r x) (value x))
      encIn (encList encA) := by
  have htest : ComputableInPolyTime
      (fun p : γ × α => decide (¬ r p.1 (value p.1) p.2))
      (encPair encIn encA) encBool := by
    have hcmp : ComputableInPolyTime
        (fun p : γ × α => decide (r p.1 (value p.1) p.2))
        (encPair encIn encA) encBool :=
      hrel.comp (g := fun p : γ × α => ((p.1, value p.1), p.2)) (by fun_prop)
    simpa only [_root_.decide_not, Function.comp_def] using bool_not.comp hcmp
  simpa only [List.orderedInsert_eq_take_drop] using
    (listAppend' (takeWhileWithInput hlist htest)
      (cons' hvalue (dropWhileWithInput hlist htest)))

/-- Stable insertion sort is polynomial-time with a comparison that captures the input. -/
theorem insertionSortWithInput {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hrel : ComputableInPolyTime
      (fun p : (γ × α) × α => decide (r p.1.1 p.1.2 p.2))
      (encCapturedComparison encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).insertionSort (r x)) encIn (encList encA) := by
  have hrev : ComputableInPolyTime (fun x => (list x).reverse) encIn (encList encA) := by
    fun_prop
  have hstep : ComputableInPolyTime
      (fun p : (γ × List α) × α => p.1.2.orderedInsert (r p.1.1) p.2)
      (encPair (encPair encIn (encList encA)) encA) (encList encA) := by
    apply orderedInsertWithInput (by fun_prop) (by fun_prop)
    exact hrel.comp
      (g := fun p : (((γ × List α) × α) × α) × α => ((p.1.1.1.1, p.1.2), p.2))
      (by fun_prop)
  have hfold := foldlWith_of_bounded_growth
    (par := fun x => x) (list := fun x => (list x).reverse) (init := fun _ => [])
    (step := fun x state value => state.orderedInsert (r x) value)
    id' hrev (const []) hstep
    (growth := fun x => 2 * (encList encA (list x)).length + 1)
    (((PolyBounded.const 2).mul hlist.polyBounded_length).add (PolyBounded.const 1))
    (fun x state value hvalue => ?_)
  · have heq (x : γ) (xs : List α) :
        xs.insertionSort (r x) = xs.foldr (List.orderedInsert (r x)) [] := by
      induction xs with
      | nil => exact List.insertionSort_nil (r x)
      | cons a xs ih => simp only [List.insertionSort_cons, List.foldr_cons, ih]
    simpa only [heq, List.foldr_eq_foldl_reverse] using hfold
  · have hsize := SizedListEncoding.length_elem_le (encA := encA) (encL := encList encA)
      (list x) value (by simpa using hvalue)
    have hlength := (List.Perm.flatMap_right (Turing.MultiTapeTM.frame ∘ encA)
      (List.perm_orderedInsert (r x) value state)).length_eq
    change (encList encA (state.orderedInsert (r x) value)).length =
      (encList encA (value :: state)).length at hlength
    simp only [encList_cons, List.length_append, length_frame] at hlength
    omega

/-- The exact stable merge-sort output has a uniform native polynomial-time certificate when
its captured comparison is total, transitive and polynomial-time. -/
theorem mergeSortWithInput {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hrel : ComputableInPolyTime
      (fun p : (γ × α) × α => decide (r p.1.1 p.1.2 p.2))
      (encCapturedComparison encIn encA) encBool)
    (htrans : ∀ x a b c, r x a b → r x b c → r x a c)
    (htotal : ∀ x a b, r x a b ∨ r x b a) :
    ComputableInPolyTime (fun x => (list x).mergeSort fun a b => decide (r x a b))
      encIn (encList encA) := by
  have heq (x : γ) := List.mergeSort_decide_eq_insertionSort (r x) (htrans x) (htotal x) (list x)
  simpa only [heq] using insertionSortWithInput hlist hrel

end ComputableInPolyTime

end Turing.MultiTapeTM

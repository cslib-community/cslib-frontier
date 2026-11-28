/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/MinMax.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.MinMax

/-!
# The first minimizer of a nonempty list

Mathlib's `List.argmin f l` is `none` exactly on the empty list. Algorithms that select a
cheapest candidate usually need the positive form, and often read the choice off with a
default through `Option.getD`. This file provides those forms.

## Main results

* `List.exists_argmin_eq_some`: a nonempty list has a first minimizer.
* `List.getD_argmin_mem`: on a nonempty list, the minimizer read with any default is a member.
* `List.getD_argmin_le`: the minimizer read with any default is at most every member.
-/

public section

namespace List

variable {α β : Type*} [LinearOrder β] {f : α → β} {l : List α}

/-- A nonempty list has a first minimizer. -/
theorem exists_argmin_eq_some (hl : l ≠ []) : ∃ m, l.argmin f = some m :=
  Option.ne_none_iff_exists'.1 (mt argmin_eq_none.1 hl)

/-- On a nonempty list, the first minimizer read with any default is a member of the list. -/
theorem getD_argmin_mem (hl : l ≠ []) (d : α) : (l.argmin f).getD d ∈ l := by
  obtain ⟨m, hm⟩ := exists_argmin_eq_some (f := f) hl
  simpa only [hm, Option.getD_some] using argmin_mem hm

/-- The first minimizer read with any default is at most every member of the list. -/
theorem getD_argmin_le {x : α} (hx : x ∈ l) (d : α) : f ((l.argmin f).getD d) ≤ f x := by
  obtain ⟨m, hm⟩ := exists_argmin_eq_some (f := f) (ne_nil_of_mem hx)
  simpa only [hm, Option.getD_some] using le_of_mem_argmin hx hm

theorem argmin_map_equiv {α γ : Type*} {δ : Type*} [LinearOrder δ]
    (e : α → γ) (l : List α) (f : γ → δ) :
    (l.argmin (f ∘ e)).map e = (l.map e).argmin f := by
  have hgen (acc : Option α) :
      (l.foldl (List.argAux fun x y => (f ∘ e) x < (f ∘ e) y) acc).map e =
        l.foldl (fun a b => List.argAux (f · < f ·) a (e b)) (acc.map e) := by
    induction l generalizing acc with
    | nil => rfl
    | cons x l ih =>
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      cases acc with
      | none => rfl
      | some c =>
        unfold List.argAux
        simp only [Option.map_some, Function.comp_apply]
        split_ifs <;> rfl
  simpa [List.argmin, List.foldl_map] using hgen none

theorem argmin_congr_mem {α δ : Type*} [LinearOrder δ] (all l : List α) {f g : α → δ}
    (hl : ∀ x ∈ l, x ∈ all) (hfg : ∀ x ∈ all, f x = g x) :
    l.argmin f = l.argmin g := by
  have hinv (m : List α) (acc : Option α) (hacc : ∀ z, acc = some z → f z = g z)
      (hm : ∀ x ∈ m, f x = g x) :
      m.foldl (List.argAux (f · < f ·)) acc = m.foldl (List.argAux (g · < g ·)) acc := by
    induction m generalizing acc with
    | nil => rfl
    | cons x m ih =>
      have hx := hm x List.mem_cons_self
      have hstep : List.argAux (f · < f ·) acc x = List.argAux (g · < g ·) acc x := by
        cases acc with
        | none => rfl
        | some z => simp only [List.argAux, hx, hacc z rfl]
      rw [List.foldl_cons, List.foldl_cons, hstep]
      refine ih _ (fun z hz => ?_) fun y hy => hm y (List.mem_cons_of_mem _ hy)
      cases acc with
      | none => exact Option.some.inj hz ▸ hx
      | some y =>
        dsimp only [List.argAux] at hz
        split_ifs at hz
        · exact Option.some.inj hz ▸ hx
        · exact hacc z hz
  exact hinv l none (by nofun) fun x hx => hfg x (hl x hx)

theorem isSome_argmin_filter {α δ : Type*} [LinearOrder δ] (l : List α) (p : α → Bool)
    (f : α → δ) : ((l.filter p).argmin f).isSome = l.any p := by
  rcases eq_or_ne (l.filter p) [] with h | h
  · have hf : l.any p = false := Bool.eq_false_iff.mpr fun ha => by
      obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp ha
      exact List.filter_eq_nil_iff.mp h x hx hp
    simp only [h, hf, List.argmin_nil, Option.isSome_none]
  · obtain ⟨m, hm⟩ := exists_argmin_eq_some (f := f) h
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
    rw [hm, Option.isSome_some, eq_comm, List.any_eq_true]
    exact ⟨x, List.mem_filter.mp hx⟩


end List

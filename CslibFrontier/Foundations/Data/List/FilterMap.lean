/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic

/-!
# `filterMap` as a filter followed by a map

`l.filterMap f` keeps the elements on which `f` is defined and maps them by `f`, read with any
default (`List.filterMap_eq_map_filter`). This is the form that list combinators which filter and
map separately compute.

## Main results

* `List.filterMap_eq_map_filter`: `l.filterMap f` is `l.filter (f · |>.isSome)` mapped by
  `(f · |>.getD d)`.
* `List.getElem?_filterMap_of_forall_isSome`, `List.take_filterMap_of_forall_isSome`: when `f` is
  defined on every element, `filterMap f` preserves positions, so it commutes with indexing and
  with `take`.
* `List.sum_map_filterMap_le`: a sum over the values of `filterMap f` is at most a sum over the
  list that bounds every value.
-/

public section

namespace List

/-- `filterMap` is a filter by definedness followed by a map, read with any default. -/
theorem filterMap_eq_map_filter {α β : Type*} (l : List α) (f : α → Option β) (d : β) :
    l.filterMap f = (l.filter fun a => (f a).isSome).map fun a => (f a).getD d := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : f a <;> simp [h, ih]

/-- When `f` is defined on every element, indexing `l.filterMap f` is indexing `l` and
applying `f`. -/
theorem getElem?_filterMap_of_forall_isSome {α β : Type*} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).isSome) → ∀ i : ℕ, (l.filterMap f)[i]? = l[i]?.bind f
  | [], _, _ => rfl
  | a :: l, h, i => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (mem_cons_self ..))
    rw [filterMap_cons_some hb]
    cases i with
    | zero => simp [hb]
    | succ i =>
      simpa using getElem?_filterMap_of_forall_isSome (fun v hv => h v (mem_cons_of_mem _ hv)) i

/-- When `f` is defined on every element, `filterMap f` commutes with `take`. -/
theorem take_filterMap_of_forall_isSome {α β : Type*} {f : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, (f a).isSome) → ∀ r : ℕ,
      (l.filterMap f).take r = (l.take r).filterMap f
  | [], _, _ => by simp
  | a :: l, h, r => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (mem_cons_self ..))
    cases r with
    | zero => simp
    | succ r =>
      rw [filterMap_cons_some hb, take_succ_cons, take_succ_cons, filterMap_cons_some hb,
        take_filterMap_of_forall_isSome (fun v hv => h v (mem_cons_of_mem _ hv)) r]

/-- A sum over the values of `filterMap f` is at most a sum over the list when every value `b` of
`f a` has `C b ≤ D a`. -/
theorem sum_map_filterMap_le {α β : Type*} {f : α → Option β} {C : β → ℕ} {D : α → ℕ}
    (h : ∀ a b, f a = some b → C b ≤ D a) (l : List α) :
    ((l.filterMap f).map C).sum ≤ (l.map D).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hf : f a with
    | none => simpa [filterMap_cons, hf] using ih.trans (Nat.le_add_left _ _)
    | some b => simpa [filterMap_cons, hf] using Nat.add_le_add (h a b hf) ih

end List

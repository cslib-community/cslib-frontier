/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Logic/Function/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Basic

/-!
# Updates of a function along a list

Updating a function `f` at the points `g i` to the values `v i`, for the indices `i` of a list in
order, gives `f` outside the points `g i` of the list and `v i` at them, if `g` is injective. If
the list contains every index, the result is `Function.extend g v f`.

## Main results

* `Function.foldl_update_apply`: the value after the updates of a list.
* `Function.foldl_update_eq_extend`: updates at all indices give `Function.extend`.
-/

public section

namespace Function

variable {ι α β : Type*} [DecidableEq β] {g : ι → β}

/-- After the updates at the points `g i` of the indices `i` of `s`, a point of `s` has the value
that `extend` gives it, and every other point keeps its value. -/
theorem foldl_update_apply (hg : Injective g) (v : ι → α) (s : List ι) (f : β → α) (y : β) :
    s.foldl (fun f i => update f (g i) (v i)) f y =
      if ∃ i ∈ s, g i = y then extend g v f y else f y := by
  induction s generalizing f with
  | nil => simp
  | cons i s ih =>
    rw [List.foldl_cons, ih]
    by_cases h : ∃ j ∈ s, g j = y
    · obtain ⟨j, hj, rfl⟩ := h
      rw [ite_eq_left ⟨j, hj, rfl⟩, ite_eq_left ⟨j, List.mem_cons_of_mem _ hj, rfl⟩,
        hg.extend_apply, hg.extend_apply]
    · by_cases hi : g i = y
      · subst hi
        simp [hg.extend_apply]
      · simp only [h, ↓reduceIte, update_of_ne (Ne.symm hi), List.mem_cons, exists_eq_or_imp, hi,
          false_or]

/-- Updates at the points `g i` of all indices `i`, in any order, give `Function.extend g v f`. -/
theorem foldl_update_eq_extend (hg : Injective g) (v : ι → α) {s : List ι} (hs : ∀ i, i ∈ s)
    (f : β → α) : s.foldl (fun f i => update f (g i) (v i)) f = extend g v f := by
  funext y
  rw [foldl_update_apply hg]
  by_cases h : ∃ i, g i = y
  · obtain ⟨i, rfl⟩ := h
    exact ite_eq_left ⟨i, hs i, rfl⟩
  · rw [ite_eq_right fun ⟨i, _, hi⟩ => h ⟨i, hi⟩, extend_apply' _ _ _ h]

end Function

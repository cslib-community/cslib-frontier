/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Operations

/-!
# First-occurrence indices under injective maps on a list

`List.idxOf_map_injOn` preserves the first occurrence of a member when the map is
injective only on the elements that occur. Repeated elements are allowed, and the map
may behave arbitrarily outside the list. Membership of the searched value is required.
The proof is relocated unchanged from CNF compaction's relabeling API.
-/

public section

namespace List

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- An injection on occurring elements preserves the first-occurrence index of a member. -/
theorem idxOf_map_injOn (l : List V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ l}) {v : V} (hv : v ∈ l) :
    (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => cases hv
  | cons a l ih =>
    rcases eq_or_ne a v with rfl | h
    · simp
    · rw [map_cons, idxOf_cons_ne _ fun heq => h (hf mem_cons_self hv heq), idxOf_cons_ne _ h]
      exact congrArg (· + 1) (ih (hf.mono fun _ => mem_cons_of_mem a) (mem_of_ne_of_mem h.symm hv))

end List

/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.List.Chain

/-!
# Ends of chains

In a chain without repeated entries, an entry whose only neighbour, in either direction, is a
single element `w` must be the first or the last entry: an inner entry has two distinct
neighbours. This is the argument that a pendant vertex of a Hamiltonian path is one of its ends,
used by the reductions to undirected Hamiltonian path without endpoints and to k-Path.

## Main results

* `List.IsChain.head?_eq_or_getLast?_eq_of_rel_eq`: an entry with a single neighbour is an end.
-/

public section

namespace List

/-- In a chain `l` of `R` without repeated entries, an entry `x` all of whose neighbours equal `w`,
whether related to `x` or from it, is the first or the last entry of `l`. -/
theorem IsChain.head?_eq_or_getLast?_eq_of_rel_eq {α : Type*} {R : α → α → Prop} {l : List α}
    (hch : l.IsChain R) (hnd : l.Nodup) {x w : α} (hx : x ∈ l)
    (hR : ∀ y, R x y ∨ R y x → y = w) : l.head? = some x ∨ l.getLast? = some x := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  rcases l₁.eq_nil_or_concat with rfl | ⟨L₁, a, rfl⟩
  · simp
  rw [List.concat_eq_append] at hnd hch
  rcases l₂ with _ | ⟨b, L₂⟩
  · simp
  exfalso
  rw [List.isChain_append, List.isChain_cons_cons] at hch
  have ha := hR a (Or.inr (hch.2.2 a (by simp) x rfl))
  have hb := hR b (Or.inl hch.2.1.1)
  rw [List.nodup_append] at hnd
  exact hnd.2.2 a (by simp) b (by simp) (ha.trans hb.symm)

end List

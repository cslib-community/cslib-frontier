/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Lookup
public import CslibFrontier.Foundations.Data.List.SortedAssoc.Flatten

/-!
# Range queries in B+-trees

`rangeM lo hi` returns the entries whose keys lie in the closed interval `[lo, hi]`, in key
order. At an interior node it walks along the separators. The child before a separator `s` holds
keys below `s`, so it is entered only when `s` is not at most `lo`; the children after `s` hold
keys that are at least `s`, so the walk goes on only while `s` is at most `hi`. That is two
comparisons per separator reached. In a leaf it runs the scan `Cslib.SortedAssoc.rangeM` of the
entry list. `visit` fires once at each node entered, the leaves included. Costs are not stated
here.

The walk enters children one after another; it does not follow a chain of leaves. What a chained
implementation would return is described by `range_eq_flatten_run`: the output is the
restriction of a contiguous run of leaves, every leaf of the run contributes, and every leaf of
the run other than its first and last is returned whole.

## Main definitions

* `rangeM`, `range`: restriction to a closed interval of keys.

## Main results

* `map_rangeM`: a monad morphism commutes with the query.
* `range_eq`: on a well-formed tree, `range` is `SortedAssoc.range` on `toList`.
* `Occupied.ne_nil_of_mem_leaves`: an occupied tree has no empty leaf when `2 ≤ t`.
* `range_eq_flatten_run`: on a well-formed tree, the output is the restriction of a contiguous
  run of leaves whose interior leaves are returned whole.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

open Cslib.SortedAssoc (leI)

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Entries with key in the closed interval `[lo, hi]`. Walk along the separators of a node:
enter the child before a separator unless the separator is at most `lo`, and go on past the
separator only when it is at most `hi`; in a leaf, scan the entries. `visit` fires once at each
node entered, when the walk along its separators ends. -/
@[expose] def rangeM (le : α → α → m Bool) (visit : m Unit) (lo hi : α) :
    BPlusTree α β → m (List (α × β))
  | .leaf entries => do
    visit
    SortedAssoc.rangeM le lo hi entries
  | .node first [] => do
    visit
    rangeM le visit lo hi first
  | .node first ((s, c) :: rest) => do
    let below ← if ← le s lo then pure [] else rangeM le visit lo hi first
    if ← le s hi then
      return below ++ (← rangeM le visit lo hi (.node c rest))
    else
      visit
      pure below
termination_by tr => sizeOf tr

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the range query. -/
theorem map_rangeM (hf : IsMonadHom m n f) (le : α → α → m Bool) (visit : m Unit) (lo hi : α)
    (tr : BPlusTree α β) :
    f (rangeM le visit lo hi tr) = rangeM (fun a b => f (le a b)) (f visit) lo hi tr := by
  fun_induction rangeM le visit lo hi tr <;>
    simp [rangeM, hf.map_bind, hf.map_pure, apply_ite f, SortedAssoc.map_rangeM hf, *]

end Transfer

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BPlusTree α β}

/-- Pure range restriction: the `Id` instantiation of `rangeM` with `visit := pure ()`. -/
def range (lo hi : α) (tr : BPlusTree α β) : List (α × β) :=
  Id.run (rangeM leI (pure ()) lo hi tr)

/-- `range` is the `Id` instantiation of `rangeM`. -/
theorem range_def (lo hi : α) : range lo hi tr = Id.run (rangeM leI (pure ()) lo hi tr) := (rfl)

/-- Range restriction of a leaf is the scan of its entries. -/
theorem range_leaf (lo hi : α) (entries : List (α × β)) :
    range lo hi (.leaf entries) = Id.run (SortedAssoc.rangeM leI lo hi entries) := by
  simp [range, rangeM]

/-- Range restriction of a node without separators is that of its only child. -/
@[simp] theorem range_node_nil (lo hi : α) (first : BPlusTree α β) :
    range lo hi (.node first []) = range lo hi first := by
  simp [range, rangeM]

/-- Range restriction at a node's first separator: the child before it contributes unless the
separator is at most `lo`, and what follows it contributes when the separator is at most `hi`. -/
theorem range_node_cons (lo hi s : α) (first c : BPlusTree α β) (rest : List (Branch α β)) :
    range lo hi (.node first ((s, c) :: rest)) =
      (if s ≤ lo then [] else range lo hi first) ++
        if s ≤ hi then range lo hi (.node c rest) else [] := by
  by_cases h₁ : s ≤ lo <;> by_cases h₂ : s ≤ hi <;> simp [range, rangeM, leI, h₁, h₂]

/-- Range restriction against the model under the search invariant. -/
private theorem range_eq_of (lo hi : α) :
    ∀ tr : BPlusTree α β, SearchInvariant t tr →
      range lo hi tr = SortedAssoc.range lo hi tr.toList
  | .leaf entries, h => by
    rw [range_leaf, toList_leaf]
    exact SortedAssoc.idRun_rangeM (by simpa using h.sorted) lo hi
  | .node first [], h => by
    rw [range_node_nil, range_eq_of lo hi first (h.child List.mem_cons_self)]
    simp
  | .node first ((s, c) :: rest), h => by
    rw [range_node_cons, toList_node_cons, SortedAssoc.range_append]
    congr 1
    · by_cases h₁ : s ≤ lo
      · simp only [h₁, ↓reduceIte]
        exact (SortedAssoc.range_eq_nil_iff.2 fun p hp => Or.inl
          ((h.separated.lt_of_mem_first (e := (s, c)) List.mem_cons_self hp).trans_le h₁)).symm
      · simp only [h₁, ↓reduceIte]
        exact range_eq_of lo hi first (h.child List.mem_cons_self)
    · by_cases h₂ : s ≤ hi
      · simp only [h₂, ↓reduceIte]
        exact range_eq_of lo hi (.node c rest) h.tail
      · simp only [h₂, ↓reduceIte]
        have hc := h.occupied c (by simp)
        exact (SortedAssoc.range_eq_nil_iff.2 fun q hq => Or.inr
          ((lt_of_not_ge h₂).trans_le
            (h.separated.le_of_mem_tail h.sorted (hc.size_pos h.two_le) hq))).symm
termination_by tr => sizeOf tr

/-- Model equation of range restriction on well-formed trees. -/
theorem range_eq (h : IsWF t tr) (lo hi : α) :
    range lo hi tr = SortedAssoc.range lo hi tr.toList :=
  range_eq_of lo hi tr h.searchInvariant

omit [LinearOrder α] in
/-- An occupied tree has no empty leaf when `2 ≤ t`. -/
theorem Occupied.ne_nil_of_mem_leaves (ht : 2 ≤ t) (ho : Occupied t tr) :
    ∀ l ∈ tr.leaves, l ≠ [] := by
  induction tr with
  | leaf entries =>
    rintro l hl
    obtain rfl : l = entries := by simpa [leaves_leaf] using hl
    have := ho.le_width
    simp only [width_leaf] at this
    exact List.ne_nil_of_length_pos (by omega)
  | node first rest ih₁ ih₂ =>
    intro l hl
    simp only [leaves_node, leavesRest_eq_flatMap, List.mem_append, List.mem_flatMap] at hl
    rcases hl with hl | ⟨e, he, hl⟩
    · exact ih₁ ho.first l hl
    · exact ih₂ e he
        (ho.of_mem_children (List.mem_cons_of_mem _ (List.mem_map_of_mem he))) l hl

/-- On a well-formed tree, the output of a range query is the restriction of a contiguous run of
leaves in which every leaf contributes and every leaf other than the first and last is returned
whole. Without the last two conjuncts the run could be all of `leaves`. -/
theorem range_eq_flatten_run (h : IsWF t tr) (lo hi : α) :
    ∃ pre run post : List (List (α × β)), tr.leaves = pre ++ run ++ post ∧
      range lo hi tr = (run.map (SortedAssoc.range lo hi)).flatten ∧
      (∀ l ∈ run, SortedAssoc.range lo hi l ≠ []) ∧
      ∀ l ∈ (run.drop 1).dropLast, SortedAssoc.range lo hi l = l := by
  rw [range_eq h]
  by_cases hne : ∀ l ∈ tr.leaves, l ≠ []
  · exact SortedAssoc.exists_run_range_flatten h.sorted hne lo hi
  · cases tr with
    | leaf entries =>
      obtain rfl : entries = [] := by simpa using hne
      exact ⟨[[]], [], [], by simp, by simp, by simp, by simp⟩
    | node first rest =>
      refine absurd (fun l hl => ?_) hne
      simp only [leaves_node, leavesRest_eq_flatMap, List.mem_append, List.mem_flatMap] at hl
      rcases hl with hl | ⟨e, he, hl⟩
      · exact (h.occupied_of_mem_children first (by simp)).ne_nil_of_mem_leaves h.two_le l hl
      · exact (h.occupied_of_mem_children e.child
          (List.mem_cons_of_mem _ (List.mem_map_of_mem he))).ne_nil_of_mem_leaves h.two_le l hl

end Pure

end BPlusTree

end Cslib.DataStructure

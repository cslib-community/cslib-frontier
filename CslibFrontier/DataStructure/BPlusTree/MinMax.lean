/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Lookup

/-!
# Least and greatest entries of B+-trees

The least entry of a B+-tree is the first entry of its leftmost leaf, and the greatest is the
last entry of its rightmost leaf. `minM` and `maxM` walk to that leaf through first, respectively
last, children. They compare no keys, so they take only the node-visit action `visit`, which
fires once at each node on the path, the leaf included. The pure operations are the `Id`
instantiations with `visit := pure ()`.

The model equations need the leaf that the walk reaches to be non-empty unless it is the root.
They are stated for occupied subtrees at `2 ≤ t`, which is what the sibling fallback of
`pred?` and `succ?` uses, and for well-formed trees.

## Main definitions

* `minM`, `maxM`: the walks, polymorphic.
* `min?`, `max?`: the pure operations.

## Main results

* `map_minM`, `map_maxM`: a monad morphism commutes with the walks.
* `min?_eq`, `max?_eq`: on a well-formed tree, `min?` and `max?` are the first and the last
  entry of `toList`.
* `Occupied.min?_eq`, `Occupied.max?_eq`: the same for an occupied subtree at `2 ≤ t`.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Least entry: descend through first children to the leftmost leaf and return its first entry.
`visit` fires once at each node on the path. -/
@[expose] def minM (visit : m Unit) : BPlusTree α β → m (Option (α × β))
  | .leaf entries => do
    visit
    pure entries.head?
  | .node first _ => do
    visit
    minM visit first

/-- Greatest entry: walk along the separators of each node, which is free, descend through last
children to the rightmost leaf and return its last entry. `visit` fires once at each node on the
path. -/
@[expose] def maxM (visit : m Unit) : BPlusTree α β → m (Option (α × β))
  | .leaf entries => do
    visit
    pure entries.getLast?
  | .node first [] => do
    visit
    maxM visit first
  | .node _ ((_, c) :: rest) => maxM visit (.node c rest)
termination_by tr => sizeOf tr

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the walk to the least entry. -/
theorem map_minM (hf : IsMonadHom m n f) (visit : m Unit) (tr : BPlusTree α β) :
    f (minM visit tr) = minM (f visit) tr := by
  fun_induction minM visit tr <;> simp [minM, hf.map_bind, hf.map_pure, *]

/-- A monad morphism commutes with the walk to the greatest entry. -/
theorem map_maxM (hf : IsMonadHom m n f) (visit : m Unit) (tr : BPlusTree α β) :
    f (maxM visit tr) = maxM (f visit) tr := by
  fun_induction maxM visit tr <;> simp [maxM, hf.map_bind, hf.map_pure, *]

end Transfer

section Pure

variable {α β : Type} {t : ℕ} {tr : BPlusTree α β}

/-- Pure least entry: the `Id` instantiation of `minM` with `visit := pure ()`. -/
def min? (tr : BPlusTree α β) : Option (α × β) := Id.run (minM (pure ()) tr)

/-- Pure greatest entry: the `Id` instantiation of `maxM` with `visit := pure ()`. -/
def max? (tr : BPlusTree α β) : Option (α × β) := Id.run (maxM (pure ()) tr)

/-- `min?` is the `Id` instantiation of `minM`. -/
theorem min?_def : min? tr = Id.run (minM (pure ()) tr) := (rfl)

/-- `max?` is the `Id` instantiation of `maxM`. -/
theorem max?_def : max? tr = Id.run (maxM (pure ()) tr) := (rfl)

/-- The least entry of a leaf is its first entry. -/
@[simp] theorem min?_leaf (entries : List (α × β)) : min? (.leaf entries) = entries.head? := by
  simp [min?, minM]

/-- The least entry of a node is that of its first child. -/
@[simp] theorem min?_node (first : BPlusTree α β) (rest : List (Branch α β)) :
    min? (.node first rest) = min? first := by
  simp [min?, minM]

/-- The greatest entry of a leaf is its last entry. -/
@[simp] theorem max?_leaf (entries : List (α × β)) : max? (.leaf entries) = entries.getLast? := by
  simp [max?, maxM]

/-- The greatest entry of a node without separators is that of its only child. -/
@[simp] theorem max?_node_nil (first : BPlusTree α β) : max? (.node first []) = max? first := by
  simp [max?, maxM]

/-- The greatest entry of a node is that of the node without its first child and separator. -/
@[simp] theorem max?_node_cons (s : α) (first c : BPlusTree α β) (rest : List (Branch α β)) :
    max? (.node first ((s, c) :: rest)) = max? (.node c rest) := by
  simp [max?, maxM]

/-- An occupied tree has a non-empty entry list when `2 ≤ t`. -/
theorem Occupied.toList_ne_nil (ht : 2 ≤ t) (ho : Occupied t tr) : tr.toList ≠ [] :=
  List.ne_nil_of_length_pos (ho.size_pos ht)

/-- The least entry against the model, at a tree whose children are occupied. -/
private theorem min?_eq_of (ht : 2 ≤ t) (tr : BPlusTree α β)
    (ho : ∀ c ∈ tr.children, Occupied t c) : min? tr = tr.toList.head? := by
  induction tr with
  | leaf entries => simp
  | node first rest ih _ =>
    have hf : Occupied t first := ho first (by simp)
    rw [min?_node, ih fun c hc => hf.of_mem_children hc, toList_node,
      List.head?_append_of_ne_nil _ (hf.toList_ne_nil ht)]

/-- The greatest entry against the model, at a tree whose children are occupied. -/
private theorem max?_eq_of (ht : 2 ≤ t) :
    ∀ tr : BPlusTree α β, (∀ c ∈ tr.children, Occupied t c) → max? tr = tr.toList.getLast?
  | .leaf entries, _ => by simp
  | .node first [], ho => by
    have hf : Occupied t first := ho first (by simp)
    rw [max?_node_nil, max?_eq_of ht first fun c hc => hf.of_mem_children hc]
    simp
  | .node first ((s, c) :: rest), ho => by
    have hc : Occupied t c := ho c (by simp)
    have hne : (BPlusTree.node c rest).toList ≠ [] := by
      rw [toList_node]
      exact List.append_ne_nil_of_left_ne_nil (hc.toList_ne_nil ht) _
    rw [max?_node_cons, toList_node_cons, List.getLast?_append_of_ne_nil _ hne]
    exact max?_eq_of ht (.node c rest) fun d hd => ho d (by
      simp only [children_node, List.map_cons, List.mem_cons] at hd ⊢
      exact Or.inr hd)
termination_by tr => sizeOf tr

/-- The least entry of an occupied subtree at `2 ≤ t` is the first entry of `toList`. -/
theorem Occupied.min?_eq (ht : 2 ≤ t) (ho : Occupied t tr) : min? tr = tr.toList.head? :=
  min?_eq_of ht tr fun _ hc => ho.of_mem_children hc

/-- The greatest entry of an occupied subtree at `2 ≤ t` is the last entry of `toList`. -/
theorem Occupied.max?_eq (ht : 2 ≤ t) (ho : Occupied t tr) : max? tr = tr.toList.getLast? :=
  max?_eq_of ht tr fun _ hc => ho.of_mem_children hc

variable [LinearOrder α]

/-- Model equation of the least entry on well-formed trees. -/
theorem min?_eq (h : IsWF t tr) : min? tr = tr.toList.head? :=
  min?_eq_of h.two_le tr h.occupied_of_mem_children

/-- Model equation of the greatest entry on well-formed trees. -/
theorem max?_eq (h : IsWF t tr) : max? tr = tr.toList.getLast? :=
  max?_eq_of h.two_le tr h.occupied_of_mem_children

end Pure

end BPlusTree

end Cslib.DataStructure

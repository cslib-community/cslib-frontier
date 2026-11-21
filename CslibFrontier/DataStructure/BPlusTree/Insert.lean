/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Lookup
public import CslibFrontier.Foundations.Data.List.SortedAssoc.Update

/-!
# Insertion into B+-trees

Insert-or-replace for the B+-trees of `Cslib.DataStructure.BPlusTree`, bottom-up: the entry is
inserted into a leaf, and a leaf or node that overflows splits, handing a separator to its
parent, which may overflow in turn; an overflow at the root grows a new root.

The two splits differ. A leaf with more than `2 * t - 1` entries keeps its first `t` entries, and
the rest form a new leaf whose first key is *copied* up as the separator: every entry stays in a
leaf. A node with more than `2 * t - 1` separators keeps its first `t`, the next separator *moves*
up, and its child becomes the first child of the new node.

Each operation is defined once over an arbitrary monad `m`, with a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, and no order instance in scope, so
that every comparison of keys goes through `le`. The pure operations are the `Id` instantiations
with the comparator `Cslib.SortedAssoc.leI` of a linear order and `visit := pure ()`. `visit`
fires once at each node on the path from the root to the leaf. At an interior node the
separators are scanned as in `slotM`, one comparison per separator passed and one more where the
scan stops, and a separator equal to the key does not end the search: the key goes into the child
that the separator introduces. In the leaf the entry is placed by `Cslib.SortedAssoc.insertM`.
The recursion is structural, so the definitions are `@[expose]`d and `decide` evaluates insertion
on concrete trees. Costs are not stated here.

## Main definitions

* `InsertResult`: a tree, or the two halves of a split with the separator between them.
* `InsertResult.ofLeaf`, `InsertResult.ofNode`: the leaf and the node split.
* `insertOrSplitM`, `insertRestM`, `insertM`: bottom-up insertion, polymorphic.
* `insertOrSplit`, `insertRest`, `insert`: the pure operations.

## References

* [R. Bayer and E. McCreight, *Organization and Maintenance of Large Ordered
  Indexes*][BayerMcCreight1972]
* [D. Comer, *The Ubiquitous B-Tree*][Comer1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

The statements here are not taken from a source.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

open Cslib.SortedAssoc (leI)

/-- The result of inserting into a subtree: a tree of the same height, or an overflow split
into two trees of the same height with the separator that goes between them. -/
inductive InsertResult (α : Type) (β : Type) : Type where
  /-- The subtree absorbed the entry. -/
  | tree (tr : BPlusTree α β)
  /-- The subtree overflowed and split, with `sep` separating the halves. -/
  | split (left : BPlusTree α β) (sep : α) (right : BPlusTree α β)

namespace InsertResult

variable {α β : Type}

/-- The entries of a result in order. A separator is not an entry. -/
@[expose] def toList : InsertResult α β → List (α × β)
  | tree tr => tr.toList
  | split l _ r => l.toList ++ r.toList

/-- Put a result in the place of a child followed by the branches `rest`. -/
@[expose] def withRest : InsertResult α β → List (Branch α β) →
    BPlusTree α β × List (Branch α β)
  | tree c, rest => (c, rest)
  | split l s r, rest => (l, (s, r) :: rest)

/-- The tree of a result at the root: an overflow grows a new root. -/
@[expose] def toTree : InsertResult α β → BPlusTree α β
  | tree tr => tr
  | split l s r => .node l [(s, r)]

/-- A leaf with the given entries, split when it has more than `2 * t - 1` of them: the first
`t` entries stay on the left, the rest go right, and the first key on the right is copied up as
the separator. The `[]` branch is unreachable for `t ≥ 1`. -/
@[expose] def ofLeaf (t : ℕ) (entries : List (α × β)) : InsertResult α β :=
  if entries.length ≤ 2 * t - 1 then tree (.leaf entries)
  else match entries.drop t with
    | [] => tree (.leaf entries)
    | p :: right => split (.leaf (entries.take t)) p.1 (.leaf (p :: right))

/-- A node with contents `first` and `rest`, split when it has more than `2 * t - 1` separators:
the first `t` branches stay on the left, the separator of the next one moves up, and its child
starts the right node. The `[]` branch is unreachable for `t ≥ 1`. -/
@[expose] def ofNode (t : ℕ) (first : BPlusTree α β) (rest : List (Branch α β)) :
    InsertResult α β :=
  if rest.length ≤ 2 * t - 1 then tree (.node first rest)
  else match rest.drop t with
    | [] => tree (.node first rest)
    | (s, c) :: right => split (.node first (rest.take t)) s (.node c right)

variable {t : ℕ}

/-- The entries of a tree result are the tree's. -/
@[simp] theorem toList_tree (tr : BPlusTree α β) : (tree tr).toList = tr.toList := rfl

/-- The entries of a split are the left entries, then the right entries. -/
@[simp] theorem toList_split (l r : BPlusTree α β) (s : α) :
    (split l s r).toList = l.toList ++ r.toList := rfl

/-- Growing a new root keeps the entries. -/
@[simp] theorem toList_toTree (x : InsertResult α β) : x.toTree.toList = x.toList := by
  cases x <;> simp [toTree]

/-- Placing a result in the place of a child keeps the entries, followed by those of `rest`. -/
theorem toList_withRest (x : InsertResult α β) (rest : List (Branch α β)) :
    (x.withRest rest).1.toList ++ ((x.withRest rest).2.flatMap fun e => e.child.toList) =
      x.toList ++ rest.flatMap fun e => e.child.toList := by
  cases x <;> simp [withRest]

/-- Splitting an overflowing leaf keeps its entries. -/
@[simp] theorem toList_ofLeaf (entries : List (α × β)) : (ofLeaf t entries).toList = entries := by
  unfold ofLeaf
  split_ifs
  · simp
  · split
    · simp
    · next p right heq =>
      rw [toList_split, toList_leaf, toList_leaf, ← heq, List.take_append_drop]

/-- Splitting an overflowing node keeps its entries. -/
@[simp] theorem toList_ofNode (first : BPlusTree α β) (rest : List (Branch α β)) :
    (ofNode t first rest).toList = (BPlusTree.node first rest).toList := by
  unfold ofNode
  split_ifs
  · rfl
  · split
    · rfl
    · next s c right heq =>
      have : rest = rest.take t ++ (s, c) :: right := by
        rw [← heq, List.take_append_drop]
      conv_rhs => rw [this]
      simp only [toList_split, toList_node, List.flatMap_append, List.flatMap_cons,
        Branch.child_mk, List.append_assoc]

end InsertResult

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

mutual
/-- Bottom-up insertion into a subtree: the tree with the entry inserted, or its split when it
overflows. A node is visited once, on entry. -/
@[expose] def insertOrSplitM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    BPlusTree α β → m (InsertResult α β)
  | .leaf entries => do
    visit
    return .ofLeaf t (← SortedAssoc.insertM le k v entries)
  | .node first rest => do
    visit
    match ← insertRestM t le visit k v rest with
    | some rest' => pure (.ofNode t first rest')
    | none =>
      let p := (← insertOrSplitM t le visit k v first).withRest rest
      pure (.ofNode t p.1 p.2)

/-- Insertion among the branches of a node, scanning the separators in order with the
comparisons of `slotM`: `none` defers to the child before the branches, because the key is below
the first separator; `some rest'` is the new list of branches, with the result of the descent
placed in the child after the last separator that is at most the key. -/
@[expose] def insertRestM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    List (Branch α β) → m (Option (List (Branch α β)))
  | [] => pure none
  | (s, c) :: rest => do
    if ← le s k then
      match ← insertRestM t le visit k v rest with
      | some rest' => pure (some ((s, c) :: rest'))
      | none =>
        let p := (← insertOrSplitM t le visit k v c).withRest rest
        pure (some ((s, p.1) :: p.2))
    else pure none
end

/-- A leaf is visited once; the entry is placed by the scan of its entries, and the leaf is split
when it overflows. -/
theorem insertOrSplitM_leaf (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (entries : List (α × β)) :
    insertOrSplitM t le visit k v (.leaf entries) = (do
      visit
      return .ofLeaf t (← SortedAssoc.insertM le k v entries)) := rfl

/-- A node is visited once, before its separators are searched; the result is split when it
overflows. -/
theorem insertOrSplitM_node (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (first : BPlusTree α β) (rest : List (Branch α β)) :
    insertOrSplitM t le visit k v (.node first rest) = (do
      visit
      match ← insertRestM t le visit k v rest with
      | some rest' => pure (.ofNode t first rest')
      | none =>
        let p := (← insertOrSplitM t le visit k v first).withRest rest
        pure (.ofNode t p.1 p.2)) := rfl

/-- The search past the last branch defers to the child before it. -/
@[simp] theorem insertRestM_nil (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    insertRestM t le visit k v ([] : List (Branch α β)) = pure none := rfl

/-- At a branch: defer to the preceding child when its separator is above the key, and otherwise
move on, descending into this branch's child when the later branches defer. -/
theorem insertRestM_cons (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (s : α) (c : BPlusTree α β) (rest : List (Branch α β)) :
    insertRestM t le visit k v ((s, c) :: rest) = (do
      if ← le s k then
        match ← insertRestM t le visit k v rest with
        | some rest' => pure (some ((s, c) :: rest'))
        | none =>
          let p := (← insertOrSplitM t le visit k v c).withRest rest
          pure (some ((s, p.1) :: p.2))
      else pure none) := rfl

/-- Insert-or-replace: the bottom-up insertion, growing a new root on overflow. -/
@[expose] def insertM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (tr : BPlusTree α β) : m (BPlusTree α β) := do
  return (← insertOrSplitM t le visit k v tr).toTree

/-- Insertion is the bottom-up insertion with an overflow at the root grown into a new root. -/
theorem insertM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (tr : BPlusTree α β) :
    insertM t le visit k v tr = (do return (← insertOrSplitM t le visit k v tr).toTree) := (rfl)

end Polymorphic

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α} {v : β}

/-- Pure bottom-up insertion into a subtree. -/
@[expose] def insertOrSplit (t : ℕ) (k : α) (v : β) (tr : BPlusTree α β) : InsertResult α β :=
  Id.run (insertOrSplitM t leI (pure ()) k v tr)

/-- Pure insertion among the branches of a node. -/
@[expose] def insertRest (t : ℕ) (k : α) (v : β) (rest : List (Branch α β)) :
    Option (List (Branch α β)) :=
  Id.run (insertRestM t leI (pure ()) k v rest)

/-- Pure insertion. -/
@[expose] def insert (t : ℕ) (k : α) (v : β) (tr : BPlusTree α β) : BPlusTree α β :=
  Id.run (insertM t leI (pure ()) k v tr)

/-- `insertOrSplit` is the `Id` instantiation of `insertOrSplitM`. -/
theorem insertOrSplit_def (tr : BPlusTree α β) :
    insertOrSplit t k v tr = Id.run (insertOrSplitM t leI (pure ()) k v tr) := (rfl)

/-- `insertRest` is the `Id` instantiation of `insertRestM`. -/
theorem insertRest_def (rest : List (Branch α β)) :
    insertRest t k v rest = Id.run (insertRestM t leI (pure ()) k v rest) := (rfl)

/-- `insert` is the `Id` instantiation of `insertM`. -/
theorem insert_def (tr : BPlusTree α β) :
    insert t k v tr = Id.run (insertM t leI (pure ()) k v tr) := (rfl)

end Pure

end BPlusTree

end Cslib.DataStructure

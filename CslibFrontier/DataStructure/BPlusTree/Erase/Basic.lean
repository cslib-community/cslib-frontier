/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Insert

/-!
# Erasure from B+-trees

Erasure for the B+-trees of `Cslib.DataStructure.BPlusTree`, bottom-up, with the shape of the
classic `Cslib.DataStructure.BTree.eraseM`: the entry is removed from a leaf, and a leaf or node
left one item short (`underflows`) is repaired by its parent against an adjacent sibling.

The repair merges the two siblings and splits the result again with the insertion splitters when
it has more than `2 * t - 1` items (`mergeSplit`), which covers both borrowing and merging. Two
leaves are concatenated and their separator is dropped; if they split again, the first key of the
new right leaf is copied up. Two nodes are joined around their separator, which is pulled down;
if they split again, a separator moves up. A child is repaired against its right sibling, and
the last child against its left one. A root left without separators collapses into its only
child (`collapse`), so the height falls only there.

Every entry is in a leaf, so there is no interior case: the search descends by the separators to
one leaf and removes the entry there. A separator changes only in `mergeSplit`. A separator equal
to the erased key stays where it is and need not be a key afterwards.

Each operation is defined once over an arbitrary monad `m`, with a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, and no order instance in scope.
The pure operations are the `Id` instantiations with the comparator `Cslib.SortedAssoc.leI` of a
linear order and `visit := pure ()`. `visit` fires once at each node on the path from the root to
the leaf, and once more for each sibling a repair inspects. At an interior node the separators
are scanned as in `slotM`, one comparison per separator passed and one more where the scan stops.
In the leaf the entry is removed by `Cslib.SortedAssoc.eraseM`. `eraseRestM` takes the child
before the branches together with the computation of its erasure, so that the recursion is
structural and the definitions are `@[expose]`d: `decide` evaluates erasure on concrete trees.
Costs are not stated here.

## Main definitions

* `underflows`, `mergeSplit`, `collapse`: underflow, the sibling repair and the root collapse.
* `rebalanceRightM`, `rebalanceLastM`: the repairs against the right and the left sibling.
* `eraseSubtreeM`, `eraseRestM`, `eraseM`: erasure, polymorphic.
* `eraseSubtree`, `eraseRest`, `erase`: the pure operations.

## Main results

* `map_eraseM`: a monad morphism commutes with erasure.
* `toList_erase`: on a well-formed tree, the entries after erasure are `Cslib.SortedAssoc.erase`
  of the entries.
* `IsWF.erase`: erasure preserves well-formedness.
* `height_erase`, `height_erase_le`, `height_le_height_erase_add_one`: the height falls by one
  exactly when the root collapses.
* `size_erase`: the size falls by one exactly when the key was present.
* `toList_erase_of_lookup_eq_none`: erasing an absent key keeps the entries.

The model equation needs more than sorted entries, as for insertion: the search trusts each
separator to bound the later children from below, which holds through a key of the child the
separator introduces, so the children must not be empty. Well-formedness provides that.

## References

* [R. Bayer and E. McCreight, *Organization and Maintenance of Large Ordered
  Indexes*][BayerMcCreight1972]
* [D. Comer, *The Ubiquitous B-Tree*][Comer1979]
* [N. Mündler, *A Verified Imperative Implementation of B-Trees*][Mundler2021]

The repair by merging and splitting again follows the functional deletion of [Mundler2021] for
classic B-trees. The statements here are not taken from a source.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

open Cslib.SortedAssoc (leI)

section Structure

variable {α β : Type}

/-- A leaf with fewer than `t - 1` entries, or a node with fewer than `t - 1` separators: a
child that erasure left one item short. -/
@[expose] def underflows (t : ℕ) (tr : BPlusTree α β) : Bool := decide (tr.width < t - 1)

/-- Merge two adjacent siblings, split again by the insertion splitters when the result has more
than `2 * t - 1` items. Two leaves are concatenated and the separator is dropped; two nodes are
joined around the separator. Siblings of a balanced tree are both leaves or both nodes; the
last case is unreachable there. -/
@[expose] def mergeSplit (t : ℕ) : BPlusTree α β → α → BPlusTree α β → InsertResult α β
  | .leaf l, _, .leaf r => .ofLeaf t (l ++ r)
  | .node lf lr, s, .node rf rr => .ofNode t lf (lr ++ (s, rf) :: rr)
  | l, s, r => .split l s r

/-- Drop an empty root: a node without separators is replaced by its only child. -/
@[expose] def collapse : BPlusTree α β → BPlusTree α β
  | .node first [] => first
  | tr => tr

end Structure

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Repair a child `c` followed by its right sibling `r` under the separator `s` and the branches
`rest`: if `c` underflows, inspect `r` (one visit) and merge them. -/
@[expose] def rebalanceRightM (t : ℕ) (visit : m Unit) (c : BPlusTree α β) (s : α)
    (r : BPlusTree α β) (rest : List (Branch α β)) : m (BPlusTree α β × List (Branch α β)) :=
  if underflows t c then do
    visit
    pure ((mergeSplit t c s r).withRest rest)
  else pure (c, (s, r) :: rest)

/-- Repair a last child `c` after its left sibling `prev` under the separator `s`: if `c`
underflows, inspect `prev` (one visit) and merge them. -/
@[expose] def rebalanceLastM (t : ℕ) (visit : m Unit) (prev : BPlusTree α β) (s : α)
    (c : BPlusTree α β) : m (BPlusTree α β × List (Branch α β)) :=
  if underflows t c then do
    visit
    pure ((mergeSplit t prev s c).withRest [])
  else pure (prev, [(s, c)])

/-- Repair against the right sibling visits and merges exactly when the child underflows. -/
theorem rebalanceRightM_def (t : ℕ) (visit : m Unit) (c : BPlusTree α β) (s : α)
    (r : BPlusTree α β) (rest : List (Branch α β)) :
    rebalanceRightM t visit c s r rest =
      if underflows t c then (do visit; pure ((mergeSplit t c s r).withRest rest))
      else pure (c, (s, r) :: rest) := (rfl)

/-- Repair against the left sibling visits and merges exactly when the last child underflows. -/
theorem rebalanceLastM_def (t : ℕ) (visit : m Unit) (prev : BPlusTree α β) (s : α)
    (c : BPlusTree α β) :
    rebalanceLastM t visit prev s c =
      if underflows t c then (do visit; pure ((mergeSplit t prev s c).withRest []))
      else pure (prev, [(s, c)]) := (rfl)

mutual
/-- Erasure from a subtree; the result may underflow by one item. A node is visited once, on
entry. -/
@[expose] def eraseSubtreeM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BPlusTree α β → m (BPlusTree α β)
  | .leaf entries => do
    visit
    return .leaf (← SortedAssoc.eraseM le k entries)
  | .node first rest => do
    visit
    let p ← eraseRestM t le visit k first (eraseSubtreeM t le visit k first) rest
    pure (.node p.1 p.2)

/-- Erasure among the branches after the child `prev`, whose erasure is `prevErased`, scanning
the separators in order with the comparisons of `slotM`. At a separator above the key, `prev` is
erased from and repaired against its right sibling. Past the last separator, the last child is
erased from and repaired against its left sibling. -/
@[expose] def eraseRestM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BPlusTree α β) (prevErased : m (BPlusTree α β)) :
    List (Branch α β) → m (BPlusTree α β × List (Branch α β))
  | [] => do return (← prevErased, [])
  | (s, c) :: rest => do
    if ← le s k then
      match rest with
      | [] => do rebalanceLastM t visit prev s (← eraseSubtreeM t le visit k c)
      | _ :: _ => do
        let p ← eraseRestM t le visit k c (eraseSubtreeM t le visit k c) rest
        pure (prev, (s, p.1) :: p.2)
    else
      rebalanceRightM t visit (← prevErased) s c rest
end

/-- Remove the entry with key `k`, if any, from a B+-tree of minimum degree `t`, comparing with
`le` and calling `visit` on each node of the search path and on each sibling a repair inspects;
a root left without separators collapses into its only child. -/
@[expose] def eraseM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BPlusTree α β) : m (BPlusTree α β) := do
  return collapse (← eraseSubtreeM t le visit k tr)

/-- Erasure is erasure from the root subtree followed by collapsing an empty root. -/
theorem eraseM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (tr : BPlusTree α β) :
    eraseM t le visit k tr = (do return collapse (← eraseSubtreeM t le visit k tr)) := (rfl)

/-- A leaf is visited once, and the entry is removed by the scan of its entries. -/
theorem eraseSubtreeM_leaf (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (entries : List (α × β)) :
    eraseSubtreeM t le visit k (.leaf entries) = (do
      visit
      return .leaf (← SortedAssoc.eraseM le k entries)) := rfl

/-- A node is visited once on entry, then its branches are searched. -/
theorem eraseSubtreeM_node (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (first : BPlusTree α β) (rest : List (Branch α β)) :
    eraseSubtreeM t le visit k (.node first rest) = (do
      visit
      let p ← eraseRestM t le visit k first (eraseSubtreeM t le visit k first) rest
      pure (.node p.1 p.2)) := rfl

/-- Past the last branch, the erasure of the preceding child is the result. -/
theorem eraseRestM_nil (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BPlusTree α β) (prevErased : m (BPlusTree α β)) :
    eraseRestM t le visit k prev prevErased [] = (do return (← prevErased, [])) := rfl

/-- At a branch: when its separator is above the key, erase from the preceding child and repair
it against this child; otherwise move on, erasing from the last child and repairing it against
its left sibling. -/
theorem eraseRestM_cons (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BPlusTree α β) (prevErased : m (BPlusTree α β)) (s : α) (c : BPlusTree α β)
    (rest : List (Branch α β)) :
    eraseRestM t le visit k prev prevErased ((s, c) :: rest) = (do
      if ← le s k then
        match rest with
        | [] => do rebalanceLastM t visit prev s (← eraseSubtreeM t le visit k c)
        | _ :: _ => do
          let p ← eraseRestM t le visit k c (eraseSubtreeM t le visit k c) rest
          pure (prev, (s, p.1) :: p.2)
      else
        rebalanceRightM t visit (← prevErased) s c rest) := rfl

end Polymorphic

section PureStructure

variable {α β : Type} {t : ℕ}

/-- Pure repair of a child against its right sibling. -/
@[expose] def rebalanceRight (t : ℕ) (c : BPlusTree α β) (s : α) (r : BPlusTree α β)
    (rest : List (Branch α β)) : BPlusTree α β × List (Branch α β) :=
  Id.run (rebalanceRightM t (pure ()) c s r rest)

/-- Pure repair of a last child against its left sibling. -/
@[expose] def rebalanceLast (t : ℕ) (prev : BPlusTree α β) (s : α) (c : BPlusTree α β) :
    BPlusTree α β × List (Branch α β) :=
  Id.run (rebalanceLastM t (pure ()) prev s c)

/-- `rebalanceRight` is the `Id` instantiation of `rebalanceRightM`. -/
theorem rebalanceRight_def (c : BPlusTree α β) (s : α) (r : BPlusTree α β)
    (rest : List (Branch α β)) :
    rebalanceRight t c s r rest = Id.run (rebalanceRightM t (pure ()) c s r rest) := (rfl)

/-- `rebalanceLast` is the `Id` instantiation of `rebalanceLastM`. -/
theorem rebalanceLast_def (prev : BPlusTree α β) (s : α) (c : BPlusTree α β) :
    rebalanceLast t prev s c = Id.run (rebalanceLastM t (pure ()) prev s c) := (rfl)

end PureStructure

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α}

/-- Pure erasure from a subtree. -/
@[expose] def eraseSubtree (t : ℕ) (k : α) (tr : BPlusTree α β) : BPlusTree α β :=
  Id.run (eraseSubtreeM t leI (pure ()) k tr)

/-- Pure erasure among the branches after the child `prev`, whose erasure is `prevErased`. -/
@[expose] def eraseRest (t : ℕ) (k : α) (prev prevErased : BPlusTree α β)
    (rest : List (Branch α β)) : BPlusTree α β × List (Branch α β) :=
  Id.run (eraseRestM t leI (pure ()) k prev (pure prevErased) rest)

/-- Pure erasure. -/
@[expose] def erase (t : ℕ) (k : α) (tr : BPlusTree α β) : BPlusTree α β :=
  Id.run (eraseM t leI (pure ()) k tr)

/-- `eraseSubtree` is the `Id` instantiation of `eraseSubtreeM`. -/
theorem eraseSubtree_def (tr : BPlusTree α β) :
    eraseSubtree t k tr = Id.run (eraseSubtreeM t leI (pure ()) k tr) := (rfl)

/-- `eraseRest` is the `Id` instantiation of `eraseRestM`. -/
theorem eraseRest_def (prev pe : BPlusTree α β) (rest : List (Branch α β)) :
    eraseRest t k prev pe rest = Id.run (eraseRestM t leI (pure ()) k prev (pure pe) rest) :=
  (rfl)

/-- `erase` is the `Id` instantiation of `eraseM`. -/
theorem erase_def (tr : BPlusTree α β) : erase t k tr = Id.run (eraseM t leI (pure ()) k tr) :=
  (rfl)

end Pure

end BPlusTree

end Cslib.DataStructure

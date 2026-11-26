/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.SortedAssoc
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# B+-trees

B+-trees in the minimum-degree form of [CLRS2009], Chapter 18: the variant of the B-trees of
[BayerMcCreight1972] that keeps every entry in a leaf and uses the interior nodes only to direct
the search ([Comer1979]). A `leaf` holds a list of entries. An interior `node` is a first child
followed by a list of `(separator, child)` pairs (`BPlusTree.Branch`), so a node with `m`
separators has `m + 1` children by construction. The tree is a map from keys to values, specified
by `toList` against the sorted association list model `List.IsSortedAssoc`.

A separator is a key, not an entry. The keys of the child that a separator introduces are at
least the separator, and the keys of every child before it are strictly below it (`Separated`).
A separator need not occur as a key in any leaf. The convention with separators bounding their
child strictly from below is not the one used here.

`leaves` lists the entry lists of the leaves from left to right, and `toList` is its
concatenation. `leaves` stands for the chain that links the leaves of a B+-tree: there are no
pointers. `height` counts the nodes on a root-to-leaf path, so a leaf has height `1`; the empty
tree is the empty leaf `leaf []`. The classic `Cslib.DataStructure.BTree` differs here, since
its leaf is the empty tree and has height `0`.

Well-formedness at minimum degree `t` is the hypothesis `IsWF t tr`, never part of the type:
`t ≥ 2`; every non-root leaf has between `t - 1` and `2 * t - 1` entries and every non-root
interior node between `t - 1` and `2 * t - 1` separators (`Occupied`); the root has at most
`2 * t - 1` entries or separators, and an interior root at least one separator; all leaves are
at the same depth (`Balanced`); the separator convention holds at every interior node
(`Separated`); and `toList` is key-sorted. `width` is the number of entries of a leaf or of
separators of an interior node, in which the root rule is stated.

`induction` is the induction principle for the nested type. The Boolean checkers `occupied`,
`balanced`, `separated` and `isWF` decide the predicates, so that well-formedness of concrete
trees is checked by `decide`. The operations and checkers are `@[expose]`d so that `decide` and
`rfl` evaluate them from other modules.

## Main definitions

* `Cslib.DataStructure.BPlusTree`: B+-trees with keys in `α` and values in `β`.
* `BPlusTree.Branch`, `BPlusTree.Branch.child`: a node's `(separator, child)` pairs.
* `BPlusTree.leaves`, `BPlusTree.toList`, `BPlusTree.size`, `BPlusTree.height`,
  `BPlusTree.keys`, `BPlusTree.map`, `BPlusTree.foldl`: the leaves in order, the entries in
  order and the basic API.
* `BPlusTree.Occupied`, `BPlusTree.Balanced`, `BPlusTree.Separated`, `BPlusTree.IsWF`: non-root
  occupancy, equal leaf depth, the separator convention and well-formedness at a minimum degree.
* `BPlusTree.occupied`, `BPlusTree.balanced`, `BPlusTree.separated`, `BPlusTree.isWF`: Boolean
  checkers deciding them.

## Main results

* `BPlusTree.induction`: induction over the nested type.
* `BPlusTree.toList_map`: mapping values maps the entries.
* `BPlusTree.Separated.lt_of_lt`: the separator convention between two positions of a node.
* `BPlusTree.IsWF.of_mem_children`: every subtree of a well-formed tree is well-formed.
* `BPlusTree.isWF_iff`: `isWF` decides `IsWF`.

## References

* [R. Bayer and E. McCreight, *Organization and Maintenance of Large Ordered
  Indexes*][BayerMcCreight1972]
* [D. Comer, *The Ubiquitous B-Tree*][Comer1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
-/

public section

universe u v w

namespace Cslib.DataStructure

/-- A B+-tree with keys in `α` and values in `β`. A leaf holds entries; an interior node is a
first child followed by `(separator, child)` pairs. -/
inductive BPlusTree (α : Type u) (β : Type v) : Type (max u v) where
  /-- A leaf holding a list of entries. -/
  | leaf (entries : List (α × β)) : BPlusTree α β
  /-- An interior node: a first child and a list of `(separator, child)` pairs. -/
  | node (first : BPlusTree α β) (rest : List (α × BPlusTree α β)) : BPlusTree α β

namespace BPlusTree

/-- A `(separator, child)` pair of an interior node. -/
abbrev Branch (α : Type u) (β : Type v) : Type (max u v) := α × BPlusTree α β

/-- The child of a branch. -/
abbrev Branch.child {α : Type u} {β : Type v} (e : Branch α β) : BPlusTree α β := e.2

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The child of a pair is its second component. -/
@[simp] theorem Branch.child_mk (k : α) (c : BPlusTree α β) : Branch.child (k, c) = c := rfl

mutual
/-- The entry lists of the leaves, from left to right: the representation of leaf chaining. -/
@[expose] def leaves : BPlusTree α β → List (List (α × β))
  | leaf entries => [entries]
  | node first rest => first.leaves ++ leavesRest rest
/-- The leaves of the children in a list of branches. -/
@[expose] def leavesRest : List (Branch α β) → List (List (α × β))
  | [] => []
  | (_, c) :: rest => c.leaves ++ leavesRest rest
end

/-- The entries from left to right, which is key order under `IsWF`. -/
@[expose] def toList (tr : BPlusTree α β) : List (α × β) := tr.leaves.flatten

mutual
/-- Number of nodes on a longest root-to-leaf path: a leaf has height `1`. -/
@[expose] def height : BPlusTree α β → ℕ
  | leaf _ => 1
  | node first rest => max (first.height + 1) (heightRest rest)
/-- Height contribution of the children in a list of branches. -/
@[expose] def heightRest : List (Branch α β) → ℕ
  | [] => 0
  | (_, c) :: rest => max (c.height + 1) (heightRest rest)
end

mutual
/-- Map a function over the values. -/
@[expose] def map (f : β → γ) : BPlusTree α β → BPlusTree α γ
  | leaf entries => leaf (entries.map fun p => (p.1, f p.2))
  | node first rest => node (first.map f) (mapRest f rest)
/-- Map a function over the values of the children in a list of branches. -/
@[expose] def mapRest (f : β → γ) : List (Branch α β) → List (Branch α γ)
  | [] => []
  | (k, c) :: rest => (k, c.map f) :: mapRest f rest
end

/-- Number of entries. -/
@[expose] def size (tr : BPlusTree α β) : ℕ := tr.toList.length

/-- The keys from left to right. -/
@[expose] def keys (tr : BPlusTree α β) : List α := tr.toList.map Prod.fst

/-- Fold over the entries from left to right, as in `toList`; the specification of any direct
recursive fold. -/
@[expose] def foldl (f : γ → α × β → γ) (init : γ) (tr : BPlusTree α β) : γ :=
  tr.toList.foldl f init

/-- An entry belongs to a tree when it belongs to its `toList`. -/
instance : Membership (α × β) (BPlusTree α β) := ⟨fun tr p => p ∈ tr.toList⟩

/-- Number of entries of a leaf, or of separators of an interior node. -/
@[expose] def width : BPlusTree α β → ℕ
  | leaf entries => entries.length
  | node _ rest => rest.length

/-- Children of the root node; a leaf has none. -/
@[expose] def children : BPlusTree α β → List (BPlusTree α β)
  | leaf _ => []
  | node first rest => first :: rest.map Branch.child

/-- Every node satisfies the occupancy bounds of a non-root node of minimum degree `t`: a leaf
has between `t - 1` and `2 * t - 1` entries, an interior node between `t - 1` and `2 * t - 1`
separators. -/
inductive Occupied (t : ℕ) : BPlusTree α β → Prop
  /-- A leaf is occupied when its entry count is in bounds. -/
  | leaf {entries : List (α × β)} :
      t - 1 ≤ entries.length → entries.length ≤ 2 * t - 1 → Occupied t (.leaf entries)
  /-- An interior node is occupied when its separator count is in bounds and all its children are
  occupied. -/
  | node {first : BPlusTree α β} {rest : List (Branch α β)} :
      t - 1 ≤ rest.length → rest.length ≤ 2 * t - 1 →
      Occupied t first → (∀ e ∈ rest, Occupied t e.child) → Occupied t (.node first rest)

/-- All leaves at the same depth: every child of a node has the height of the first child. -/
inductive Balanced : BPlusTree α β → Prop
  /-- A leaf is balanced. -/
  | leaf {entries : List (α × β)} : Balanced (.leaf entries)
  /-- A node is balanced when its children are balanced and of equal height. -/
  | node {first : BPlusTree α β} {rest : List (Branch α β)} :
      Balanced first → (∀ e ∈ rest, Balanced e.child) →
      (∀ e ∈ rest, e.child.height = first.height) → Balanced (.node first rest)

/-- The separator convention at every interior node: the keys of the child a separator introduces
are at least the separator, and the keys of every child before it are strictly below it. A
separator need not occur as a key. -/
inductive Separated [LinearOrder α] : BPlusTree α β → Prop
  /-- A leaf has no separators. -/
  | leaf {entries : List (α × β)} : Separated (.leaf entries)
  /-- At a node: the children are separated, each separator is at most the keys of its child, the
  keys of each child among the branches are below every later separator, and the keys of the first
  child are below every separator. -/
  | node {first : BPlusTree α β} {rest : List (Branch α β)} :
      Separated first → (∀ e ∈ rest, Separated e.child) →
      (∀ e ∈ rest, ∀ p ∈ e.child.toList, e.1 ≤ p.1) →
      rest.Pairwise (fun a b => ∀ p ∈ a.child.toList, p.1 < b.1) →
      (∀ e ∈ rest, ∀ p ∈ first.toList, p.1 < e.1) → Separated (.node first rest)

/-- Well-formed B+-tree of minimum degree `t`: root occupancy, non-root occupancy, equal leaf
depth, the separator convention, and key-sortedness of `toList`. -/
structure IsWF [LinearOrder α] (t : ℕ) (tr : BPlusTree α β) : Prop where
  /-- The minimum degree is at least `2`. -/
  two_le : 2 ≤ t
  /-- The root has at most `2 * t - 1` entries or separators. -/
  width_le : tr.width ≤ 2 * t - 1
  /-- An interior root has at least one separator. -/
  width_pos : (∀ entries, tr ≠ .leaf entries) → 1 ≤ tr.width
  /-- Every child of the root is occupied. -/
  occupied_of_mem_children : ∀ c ∈ tr.children, Occupied t c
  /-- All leaves are at the same depth. -/
  balanced : Balanced tr
  /-- The separator convention holds at every interior node. -/
  separated : Separated tr
  /-- The entries are sorted by strictly increasing key. -/
  sorted : tr.toList.IsSortedAssoc

mutual
/-- Boolean check of `Occupied t`. -/
@[expose] def occupied (t : ℕ) : BPlusTree α β → Bool
  | leaf entries => decide (t - 1 ≤ entries.length) && decide (entries.length ≤ 2 * t - 1)
  | node first rest =>
    decide (t - 1 ≤ rest.length) && decide (rest.length ≤ 2 * t - 1) && occupied t first &&
      occupiedRest t rest
/-- Boolean check that every child in a list of branches is occupied. -/
@[expose] def occupiedRest (t : ℕ) : List (Branch α β) → Bool
  | [] => true
  | (_, c) :: rest => occupied t c && occupiedRest t rest
end

mutual
/-- Boolean check of `Balanced`. -/
@[expose] def balanced : BPlusTree α β → Bool
  | leaf _ => true
  | node first rest => balanced first && balancedRest first.height rest
/-- Boolean check that every child in a list of branches is balanced and of height `h`. -/
@[expose] def balancedRest (h : ℕ) : List (Branch α β) → Bool
  | [] => true
  | (_, c) :: rest => balanced c && c.height == h && balancedRest h rest
end

/-- Boolean check that the keys of each child in a list of branches are below every later
separator. -/
@[expose] def belowLater [LinearOrder α] : List (Branch α β) → Bool
  | [] => true
  | a :: rest =>
    (rest.all fun b => a.child.toList.all fun p => decide (p.1 < b.1)) && belowLater rest

mutual
/-- Boolean check of `Separated`. -/
@[expose] def separated [LinearOrder α] : BPlusTree α β → Bool
  | leaf _ => true
  | node first rest =>
    separated first && separatedRest rest &&
      (rest.all fun e : Branch α β => e.child.toList.all fun p => decide (e.1 ≤ p.1)) &&
      belowLater rest && rest.all fun e => first.toList.all fun p => decide (p.1 < e.1)
/-- Boolean check that every child in a list of branches is separated. -/
@[expose] def separatedRest [LinearOrder α] : List (Branch α β) → Bool
  | [] => true
  | (_, c) :: rest => separated c && separatedRest rest
end

/-- Boolean check of `IsWF t`. -/
@[expose] def isWF [LinearOrder α] (t : ℕ) (tr : BPlusTree α β) : Bool :=
  decide (2 ≤ t) && decide (tr.width ≤ 2 * t - 1) &&
    (tr matches .leaf _ || decide (1 ≤ tr.width)) && tr.children.all (occupied t) &&
    balanced tr && separated tr && decide tr.toList.IsSortedAssoc

/-! ### Equation lemmas -/

section Equations

variable {first : BPlusTree α β} {rest : List (Branch α β)} {entries : List (α × β)} {k : α}
  {c : BPlusTree α β}

/-- A leaf is its own only leaf. -/
@[simp] theorem leaves_leaf : (leaf entries : BPlusTree α β).leaves = [entries] := rfl

/-- The leaves of a node are those of its first child followed by those of the others. -/
theorem leaves_node : (node first rest).leaves = first.leaves ++ leavesRest rest := rfl

/-- An empty list of branches has no leaves. -/
theorem leavesRest_nil : leavesRest ([] : List (Branch α β)) = [] := rfl

/-- The leaves of a list of branches start with those of the first child. -/
theorem leavesRest_cons : leavesRest ((k, c) :: rest) = c.leaves ++ leavesRest rest := rfl

/-- The leaves of a list of branches are those of its children, in order. -/
@[simp] theorem leavesRest_eq_flatMap :
    leavesRest rest = rest.flatMap fun e => e.child.leaves := by
  induction rest with
  | nil => rfl
  | cons e _ ih => exact e.casesOn fun _ _ => by simp [leavesRest_cons, ih]

/-- The entries of a leaf. -/
@[simp] theorem toList_leaf : (leaf entries : BPlusTree α β).toList = entries := by
  simp [toList]

/-- The entries of a node are those of its first child followed by those of the others. -/
@[simp] theorem toList_node :
    (node first rest).toList = first.toList ++ rest.flatMap fun e => e.child.toList := by
  simp only [toList, leaves_node, leavesRest_eq_flatMap, List.flatten_append, List.flatMap_def,
    List.flatten_flatten, List.map_map, Function.comp_def]

/-- The size of a leaf is its number of entries. -/
@[simp] theorem size_leaf : (leaf entries : BPlusTree α β).size = entries.length := by
  simp [size]

/-- A leaf has height `1`. -/
@[simp] theorem height_leaf : (leaf entries : BPlusTree α β).height = 1 := rfl

/-- The height of a node is one more than that of its tallest child. -/
@[simp] theorem height_node :
    (node first rest).height = max (first.height + 1) (heightRest rest) := rfl

/-- An empty list of branches contributes no height. -/
theorem heightRest_nil : heightRest ([] : List (Branch α β)) = 0 := rfl

/-- The height contribution of a list of branches. -/
theorem heightRest_cons :
    heightRest ((k, c) :: rest) = max (c.height + 1) (heightRest rest) := rfl

/-- A bound on the height contribution of a list of branches is a bound for every child. -/
theorem heightRest_le_iff {n : ℕ} : heightRest rest ≤ n ↔ ∀ e ∈ rest, e.child.height + 1 ≤ n := by
  induction rest with
  | nil => simp [heightRest_nil]
  | cons e _ ih => exact e.casesOn fun _ _ => by simp [heightRest_cons, ih]

/-- Mapping a leaf maps the values of its entries. -/
@[simp] theorem map_leaf (f : β → γ) :
    (leaf entries : BPlusTree α β).map f = leaf (entries.map fun p => (p.1, f p.2)) := rfl

/-- Mapping a node maps its children. -/
@[simp] theorem map_node (f : β → γ) :
    (node first rest).map f = node (first.map f) (mapRest f rest) := rfl

/-- Mapping a list of branches maps each child and keeps the separators. -/
@[simp] theorem mapRest_eq_map (f : β → γ) :
    mapRest f rest = rest.map fun e : Branch α β => (e.1, e.child.map f) := by
  induction rest with
  | nil => rfl
  | cons e _ ih => exact e.casesOn fun _ _ => by simp [mapRest, ih]

/-- A leaf has no children. -/
@[simp] theorem children_leaf : (leaf entries : BPlusTree α β).children = [] := rfl

/-- The children of a node. -/
@[simp] theorem children_node : (node first rest).children = first :: rest.map Branch.child := rfl

/-- The width of a leaf is its number of entries. -/
@[simp] theorem width_leaf : (leaf entries : BPlusTree α β).width = entries.length := rfl

/-- The width of a node is its number of separators. -/
@[simp] theorem width_node : (node first rest).width = rest.length := rfl

end Equations

variable {tr : BPlusTree α β}

/-! ### Induction -/

/-- A child of a node is smaller than the node: the measure for recursion into a child. -/
theorem sizeOf_lt_of_mem_children {first c : BPlusTree α β} {rest : List (Branch α β)}
    (hc : c ∈ (node first rest).children) : sizeOf c < sizeOf (node first rest) := by
  simp only [children_node, List.mem_cons, List.mem_map] at hc
  rcases hc with rfl | ⟨⟨a, c⟩, he, rfl⟩
  · simp [node.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem he
    simp [Prod.mk.sizeOf_spec, node.sizeOf_spec] at this ⊢; omega

/-- Induction on B+-trees, with a hypothesis for the first child and for every child among the
branches. This replaces the raw nested recursor in proofs. -/
theorem induction {motive : BPlusTree α β → Prop} (leaf : ∀ entries, motive (.leaf entries))
    (node : ∀ (first : BPlusTree α β) (rest : List (Branch α β)), motive first →
      (∀ e ∈ rest, motive e.child) → motive (.node first rest)) :
    ∀ tr, motive tr
  | .leaf entries => leaf entries
  | .node first rest =>
    node first rest (induction leaf node first) fun e _ => induction leaf node e.child
termination_by tr => sizeOf tr
decreasing_by
  · exact sizeOf_lt_of_mem_children List.mem_cons_self
  · exact sizeOf_lt_of_mem_children (List.mem_cons_of_mem _ (List.mem_map_of_mem ‹e ∈ rest›))

attribute [induction_eliminator] induction

/-! ### Basic API -/

/-- Membership in a tree is membership in its entries. -/
@[simp] theorem mem_def {p : α × β} : p ∈ tr ↔ p ∈ tr.toList := Iff.rfl

/-- The number of entries is the length of `toList`. -/
@[simp] theorem length_toList : tr.toList.length = tr.size := rfl

/-- The size of a node is the sum of the sizes of its children. -/
theorem size_node {first : BPlusTree α β} {rest : List (Branch α β)} :
    (node first rest).size = first.size + (rest.map fun e => e.child.size).sum := by
  simp only [size, toList_node, List.length_append, List.length_flatMap]

/-- A key belongs to `keys` exactly when some entry of the tree has it. -/
@[simp] theorem mem_keys {k : α} : k ∈ tr.keys ↔ ∃ v, (k, v) ∈ tr := by
  simp [keys]

/-- Every tree has positive height: a leaf is a node on its own path. -/
theorem height_pos : 0 < tr.height := by
  cases tr <;> simp [height_node]

/-- The trees of height `1` are the leaves. -/
theorem height_eq_one_iff : tr.height = 1 ↔ ∃ entries, tr = .leaf entries := by
  cases tr with
  | leaf entries => simp
  | node first rest =>
    have := height_pos (tr := first)
    simp only [height_node, reduceCtorEq, exists_false, iff_false]; omega

/-- Mapping over values maps the leaves. -/
@[simp] theorem leaves_map (f : β → γ) :
    (tr.map f).leaves = tr.leaves.map fun l => l.map fun p => (p.1, f p.2) := by
  induction tr with
  | leaf entries => simp
  | node first rest ih₁ ih₂ =>
    simp only [map_node, leaves_node, leavesRest_eq_flatMap, mapRest_eq_map, List.map_append, ih₁,
      List.flatMap_map, List.map_flatMap, Branch.child]
    exact congrArg (_ ++ ·) (List.flatMap_congr ih₂)

/-- Mapping over values maps the entries. -/
@[simp] theorem toList_map (f : β → γ) :
    (tr.map f).toList = tr.toList.map fun p => (p.1, f p.2) := by
  simp [toList, List.map_flatten]

/-- Mapping over values preserves the size. -/
@[simp] theorem size_map (f : β → γ) : (tr.map f).size = tr.size := by
  rw [size, size, toList_map, List.length_map]

/-- Mapping over values preserves the keys. -/
@[simp] theorem keys_map (f : β → γ) : (tr.map f).keys = tr.keys := by
  simp [keys, Function.comp_def]

/-- Mapping over values preserves the height. -/
@[simp] theorem height_map (f : β → γ) : (tr.map f).height = tr.height := by
  induction tr with
  | leaf entries => simp
  | node first rest ih₁ ih₂ =>
    have h : heightRest (mapRest f rest) = heightRest rest := by
      induction rest with
      | nil => rfl
      | cons e _ ih =>
        rcases e with ⟨k, c⟩
        rw [mapRest, heightRest_cons, heightRest_cons, ih₂ (k, c) List.mem_cons_self,
          ih fun e' he' => ih₂ e' (List.mem_cons_of_mem _ he')]
    rw [map_node, height_node, height_node, ih₁, h]

private theorem mem_children_cases {P : Prop} {c : BPlusTree α β} (hc : c ∈ tr.children)
    (hfirst : ∀ fst rest, tr = .node fst rest → c = fst → P)
    (hrest : ∀ fst rest (e : Branch α β), tr = .node fst rest → e ∈ rest → c = e.child → P) :
    P := by
  cases tr with
  | leaf entries => nomatch hc
  | node fst rest =>
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hfirst c rest rfl rfl
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
      exact hrest fst rest e rfl he rfl

/-- The entries of a child form a sublist of those of the tree. -/
theorem toList_sublist_of_mem_children {c : BPlusTree α β} (hc : c ∈ tr.children) :
    c.toList.Sublist tr.toList :=
  mem_children_cases hc (fun _ _ htr hc => htr ▸ hc ▸ toList_node ▸ List.sublist_append_left _ _)
    fun _ _ _ htr he hc => htr ▸ hc ▸ toList_node ▸ List.flatMap_def.symm ▸
      (List.sublist_flatten_of_mem
        (List.mem_map_of_mem (f := fun e : Branch α β => e.child.toList) he)).trans
        (List.sublist_append_right _ _)

/-- A child among the branches is lower than its node. -/
theorem height_succ_le_of_mem_rest {first : BPlusTree α β} {rest : List (Branch α β)}
    {e : Branch α β} (he : e ∈ rest) : e.child.height + 1 ≤ (node first rest).height :=
  (heightRest_le_iff.1 le_rfl e he).trans (le_max_right _ _)

/-- The first child is lower than its node. -/
theorem height_first_succ_le {first : BPlusTree α β} {rest : List (Branch α β)} :
    first.height + 1 ≤ (node first rest).height :=
  le_max_left _ _

/-- A child is lower than its tree. -/
theorem height_succ_le_of_mem_children {c : BPlusTree α β} (hc : c ∈ tr.children) :
    c.height + 1 ≤ tr.height :=
  mem_children_cases hc (fun _ _ htr hc => htr ▸ hc ▸ height_first_succ_le)
    fun _ _ _ htr he hc => htr ▸ hc ▸ height_succ_le_of_mem_rest he

/-! ### Inversion -/

section Inversion

variable {fst : BPlusTree α β} {rest : List (Branch α β)} {entries : List (α × β)} {t : ℕ}

/-- The children among the branches of a balanced node have the height of the first child. -/
theorem Balanced.height_of_mem_rest (h : Balanced (.node fst rest)) {e : Branch α β}
    (he : e ∈ rest) : e.child.height = fst.height :=
  match h with | .node _ _ h₃ => h₃ e he

/-- A balanced node is one higher than its first child. -/
theorem Balanced.height_node (h : Balanced (.node fst rest)) :
    (BPlusTree.node fst rest).height = fst.height + 1 := by
  rw [BPlusTree.height_node]
  exact max_eq_left (heightRest_le_iff.2 fun e he => by rw [h.height_of_mem_rest he])

/-- The first child of a balanced node is balanced. -/
theorem Balanced.first (h : Balanced (.node fst rest)) : Balanced fst :=
  match h with | .node h₁ _ _ => h₁

/-- The children among the branches of a balanced node are balanced. -/
theorem Balanced.of_mem_rest (h : Balanced (.node fst rest)) {e : Branch α β}
    (he : e ∈ rest) : Balanced e.child :=
  match h with | .node _ h₂ _ => h₂ e he

/-- A child of a balanced tree is exactly one lower. -/
theorem Balanced.height_of_mem_children {c : BPlusTree α β} (h : Balanced tr)
    (hc : c ∈ tr.children) : c.height + 1 = tr.height := by
  refine mem_children_cases hc (fun _ _ htr hce => ?_) fun _ _ _ htr he hce => ?_
  · subst htr hce
    exact h.height_node.symm
  · subst htr hce
    rw [h.height_node, h.height_of_mem_rest he]

/-- A child of a balanced tree is balanced. -/
theorem Balanced.of_mem_children {c : BPlusTree α β} (h : Balanced tr) (hc : c ∈ tr.children) :
    Balanced c :=
  mem_children_cases hc (fun _ _ htr hc => hc ▸ (htr ▸ h).first)
    fun _ _ _ htr he hc => hc ▸ (htr ▸ h).of_mem_rest he

/-- An occupied tree has at most `2 * t - 1` entries or separators at its root. -/
theorem Occupied.width_le {c : BPlusTree α β} (h : Occupied t c) : c.width ≤ 2 * t - 1 :=
  match h with | .leaf _ h₂ | .node _ h₂ _ _ => h₂

/-- An occupied tree has at least `t - 1` entries or separators at its root. -/
theorem Occupied.le_width {c : BPlusTree α β} (h : Occupied t c) : t - 1 ≤ c.width :=
  match h with | .leaf h₁ _ | .node h₁ _ _ _ => h₁

/-- The first child of an occupied node is occupied. -/
theorem Occupied.first (h : Occupied t (.node fst rest)) : Occupied t fst :=
  match h with | .node _ _ h₃ _ => h₃

/-- The children among the branches of an occupied node are occupied. -/
theorem Occupied.of_mem_rest (h : Occupied t (.node fst rest)) {e : Branch α β}
    (he : e ∈ rest) : Occupied t e.child :=
  match h with | .node _ _ _ h₄ => h₄ e he

/-- A child of an occupied tree is occupied. -/
theorem Occupied.of_mem_children {c : BPlusTree α β} (h : Occupied t tr)
    (hc : c ∈ tr.children) : Occupied t c :=
  mem_children_cases hc (fun _ _ htr hc => hc ▸ (htr ▸ h).first)
    fun _ _ _ htr he hc => hc ▸ (htr ▸ h).of_mem_rest he

end Inversion

section LinearOrder

variable [LinearOrder α] {t : ℕ} {c fst : BPlusTree α β} {rest : List (Branch α β)}

/-- The first child of a separated node is separated. -/
theorem Separated.first (h : Separated (.node fst rest)) : Separated fst :=
  match h with | .node h₁ _ _ _ _ => h₁

/-- The children among the branches of a separated node are separated. -/
theorem Separated.of_mem_rest (h : Separated (.node fst rest)) {e : Branch α β}
    (he : e ∈ rest) : Separated e.child :=
  match h with | .node _ h₂ _ _ _ => h₂ e he

/-- A separator is at most every key of the child it introduces. -/
theorem Separated.le_of_mem (h : Separated (.node fst rest)) {e : Branch α β} (he : e ∈ rest)
    {p : α × β} (hp : p ∈ e.child.toList) : e.1 ≤ p.1 :=
  match h with | .node _ _ h₃ _ _ => h₃ e he p hp

/-- The keys of each child among the branches are below every later separator. -/
theorem Separated.pairwise (h : Separated (.node fst rest)) :
    rest.Pairwise fun a b => ∀ p ∈ a.child.toList, p.1 < b.1 :=
  match h with | .node _ _ _ h₄ _ => h₄

/-- The keys of the first child are below every separator. -/
theorem Separated.lt_of_mem_first (h : Separated (.node fst rest)) {e : Branch α β}
    (he : e ∈ rest) {p : α × β} (hp : p ∈ fst.toList) : p.1 < e.1 :=
  match h with | .node _ _ _ _ h₅ => h₅ e he p hp

/-- The separator convention between two positions of a node: the keys of the child at an
earlier position are below the separator at a later one. -/
theorem Separated.lt_of_lt (h : Separated (.node fst rest)) {i j : Fin rest.length}
    (hij : i < j) {p : α × β} (hp : p ∈ rest[i].child.toList) : p.1 < rest[j].1 :=
  List.pairwise_iff_getElem.1 h.pairwise i j i.isLt j.isLt hij p hp

/-- A child of a separated tree is separated. -/
theorem Separated.of_mem_children (h : Separated tr) (hc : c ∈ tr.children) : Separated c :=
  mem_children_cases hc (fun _ _ htr hc => hc ▸ (htr ▸ h).first)
    fun _ _ _ htr he hc => hc ▸ (htr ▸ h).of_mem_rest he

/-- Every child of a well-formed tree has sorted entries. -/
theorem IsWF.sorted_of_mem_children (h : IsWF t tr) (hc : c ∈ tr.children) :
    c.toList.IsSortedAssoc :=
  h.sorted.sublist (toList_sublist_of_mem_children hc)

/-- An occupied, balanced, separated tree with sorted entries is well-formed when `2 ≤ t`: the
occupancy of a non-root node implies the root rule. -/
theorem Occupied.isWF (ht : 2 ≤ t) (ho : Occupied t c) (hb : Balanced c) (hp : Separated c)
    (hs : c.toList.IsSortedAssoc) : IsWF t c where
  two_le := ht
  width_le := ho.width_le
  width_pos _ := by have := ho.le_width; omega
  occupied_of_mem_children _ hc := ho.of_mem_children hc
  balanced := hb
  separated := hp
  sorted := hs

/-- Every subtree of a well-formed tree is well-formed: non-root occupancy implies the root rule
when `2 ≤ t`. -/
theorem IsWF.of_mem_children (h : IsWF t tr) (hc : c ∈ tr.children) : IsWF t c :=
  (h.occupied_of_mem_children c hc).isWF h.two_le (h.balanced.of_mem_children hc)
    (h.separated.of_mem_children hc) (h.sorted_of_mem_children hc)

end LinearOrder

/-! ### Decidability -/

section Decidability

variable {rest : List (Branch α β)} {t n : ℕ}

/-- `occupiedRest` checks every child among the branches with `occupied`. -/
@[simp] theorem occupiedRest_eq_all :
    occupiedRest t rest = rest.all fun e => occupied t e.child := by
  induction rest with
  | nil => rfl
  | cons e _ ih => exact e.casesOn fun _ _ => by simp [occupiedRest, ih]

/-- `balancedRest n` checks that every child among the branches is balanced and of height `n`. -/
@[simp] theorem balancedRest_eq_all :
    balancedRest n rest = rest.all fun e => balanced e.child && e.child.height == n := by
  induction rest with
  | nil => rfl
  | cons e _ ih => exact e.casesOn fun _ _ => by simp [balancedRest, ih, Bool.and_assoc]

/-- `occupied` decides `Occupied`. -/
@[simp] theorem occupied_iff : occupied t tr = true ↔ Occupied t tr := by
  induction tr with
  | leaf entries =>
    simp only [occupied, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun h => .leaf h.1 h.2, fun h => ⟨h.le_width, h.width_le⟩⟩
  | node first rest ih₁ ih₂ =>
    rw [occupied, occupiedRest_eq_all]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, ih₁]
    exact ⟨fun ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ => .node h₁ h₂ h₃ fun e he => (ih₂ e he).1 (h₄ e he),
      fun h => ⟨⟨⟨h.le_width, h.width_le⟩, h.first⟩,
        fun e he => (ih₂ e he).2 (h.of_mem_rest he)⟩⟩

/-- `balanced` decides `Balanced`. -/
@[simp] theorem balanced_iff : balanced tr = true ↔ Balanced tr := by
  induction tr with
  | leaf entries => exact ⟨fun _ => .leaf, fun _ => rfl⟩
  | node first rest ih₁ ih₂ =>
    rw [balanced, balancedRest_eq_all]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, ih₁]
    exact ⟨fun ⟨h₁, h₂⟩ => .node h₁ (fun e he => (ih₂ e he).1 (h₂ e he).1)
        fun e he => (h₂ e he).2,
      fun h => ⟨h.first, fun e he => ⟨(ih₂ e he).2 (h.of_mem_rest he), h.height_of_mem_rest he⟩⟩⟩

variable [LinearOrder α]

/-- `belowLater` decides that the keys of each child are below every later separator. -/
theorem belowLater_iff :
    belowLater rest = true ↔ rest.Pairwise fun a b => ∀ p ∈ a.child.toList, p.1 < b.1 := by
  induction rest with
  | nil => simp [belowLater]
  | cons a rest ih =>
    simp only [belowLater, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, ih,
      List.pairwise_cons]

/-- `separatedRest` checks every child among the branches with `separated`. -/
@[simp] theorem separatedRest_eq_all :
    separatedRest rest = rest.all fun e => separated e.child := by
  induction rest with
  | nil => rfl
  | cons e _ ih => exact e.casesOn fun _ _ => by simp [separatedRest, ih]

/-- `separated` decides `Separated`. -/
@[simp] theorem separated_iff : separated tr = true ↔ Separated tr := by
  induction tr with
  | leaf entries => exact ⟨fun _ => .leaf, fun _ => rfl⟩
  | node first rest ih₁ ih₂ =>
    rw [separated, separatedRest_eq_all]
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, ih₁, belowLater_iff]
    exact ⟨fun ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ =>
        .node h₁ (fun e he => (ih₂ e he).1 (h₂ e he)) h₃ h₄ h₅,
      fun h => ⟨⟨⟨⟨h.first, fun e he => (ih₂ e he).2 (h.of_mem_rest he)⟩,
        fun e he p hp => h.le_of_mem he hp⟩, h.pairwise⟩,
        fun e he p hp => h.lt_of_mem_first he hp⟩⟩

/-- `isWF` decides `IsWF`. -/
@[simp] theorem isWF_iff : isWF t tr = true ↔ IsWF t tr := by
  simp only [isWF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    occupied_iff, balanced_iff, separated_iff]
  refine ⟨fun ⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩ =>
    ⟨h₁, h₂, fun hne => ?_, h₄, h₅, h₆, h₇⟩, fun h =>
    ⟨⟨⟨⟨⟨⟨h.two_le, h.width_le⟩, ?_⟩, h.occupied_of_mem_children⟩, h.balanced⟩, h.separated⟩,
      h.sorted⟩⟩
  · cases tr with
    | leaf entries => exact absurd rfl (hne entries)
    | node => simpa using h₃
  · cases tr with
    | leaf => simp
    | node => exact Or.inr (h.width_pos nofun)

end Decidability

instance (t : ℕ) (tr : BPlusTree α β) : Decidable (Occupied t tr) :=
  decidable_of_iff _ occupied_iff

instance (tr : BPlusTree α β) : Decidable (Balanced tr) := decidable_of_iff _ balanced_iff

instance [LinearOrder α] (tr : BPlusTree α β) : Decidable (Separated tr) :=
  decidable_of_iff _ separated_iff

instance [LinearOrder α] (t : ℕ) (tr : BPlusTree α β) : Decidable (IsWF t tr) :=
  decidable_of_iff _ isWF_iff

end BPlusTree

end Cslib.DataStructure

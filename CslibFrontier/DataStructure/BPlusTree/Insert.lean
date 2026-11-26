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
* `Good`: a balanced, occupied subtree of a given height, which is what a split produces
  (`InsertResult.exists_good_split_ofLeaf`, `InsertResult.exists_good_split_ofNode`).
* `Linked`, `Sep`: the separator convention between neighbouring children, and that of a
  result (`separated_node_of_linked`, `sep_ofLeaf`, `sep_ofNode`, `linked_withRest_of_sep`).

## Main results

* `map_insertM`: a monad morphism commutes with insertion.
* `toList_insert`: on a well-formed tree, the entries after insertion are
  `Cslib.SortedAssoc.insert` of the entries.
* `IsWF.insert`: insertion preserves well-formedness.
* `height_insert`, `height_insert_le`, `height_le_height_insert`: the height grows by one exactly
  when the root splits.
* `size_insert`: the size grows by one exactly when the key was absent.

The model equation needs more than sorted entries: the search trusts each separator to bound the
later children from below, which holds through a key of the child the separator introduces, so
the children must not be empty. Well-formedness provides that. The separator convention is
preserved because, when no child is empty, it is a condition between neighbouring children, and
an insertion changes one child or puts two in its place.

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
the separator. The `[]` branch is unreachable. -/
@[expose] def ofLeaf (t : ℕ) (entries : List (α × β)) : InsertResult α β :=
  if entries.length ≤ 2 * t - 1 then tree (.leaf entries)
  else match entries.drop t with
    | [] => tree (.leaf entries)
    | p :: right => split (.leaf (entries.take t)) p.1 (.leaf (p :: right))

/-- A node with contents `first` and `rest`, split when it has more than `2 * t - 1` separators:
the first `t` branches stay on the left, the separator of the next one moves up, and its child
starts the right node. The `[]` branch is unreachable. -/
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
  · exact toList_leaf
  · cases heq : entries.drop t with
    | nil => exact toList_leaf
    | cons p right => rw [toList_split, toList_leaf, toList_leaf, ← heq, List.take_append_drop]

/-- Splitting an overflowing node keeps its entries. -/
@[simp] theorem toList_ofNode (first : BPlusTree α β) (rest : List (Branch α β)) :
    (ofNode t first rest).toList = (BPlusTree.node first rest).toList := by
  unfold ofNode
  split_ifs
  · rfl
  · cases heq : rest.drop t with
    | nil => rfl
    | cons sc right =>
      conv_rhs => rw [← List.take_append_drop t rest, heq]
      simp only [toList_split, toList_node, List.flatMap_append, List.flatMap_cons,
        List.append_assoc]

end InsertResult

/-! ### Shape -/

section Shape

variable {α β : Type} {t : ℕ}

/-- A subtree of height `h` that is balanced and occupied: what every child of a well-formed
node is. -/
structure Good (t h : ℕ) (c : BPlusTree α β) : Prop where
  /-- The subtree is balanced. -/
  balanced : Balanced c
  /-- The subtree has height `h`. -/
  height_eq : c.height = h
  /-- Every node of the subtree is occupied. -/
  occupied : Occupied t c

/-- A node with `t - 1` to `2 * t - 1` separators over good children of height `h` is good, of
height `h + 1`. -/
theorem good_node {first : BPlusTree α β} {rest : List (Branch α β)} {h : ℕ}
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child) (h₁ : t - 1 ≤ rest.length)
    (h₂ : rest.length ≤ 2 * t - 1) : Good t (h + 1) (.node first rest) :=
  have hb : Balanced (.node first rest) :=
    .node hf.balanced (fun e he => (hr e he).balanced)
      fun e he => (hr e he).height_eq.trans hf.height_eq.symm
  ⟨hb, by rw [hb.height_node, hf.height_eq], .node h₁ h₂ hf.occupied fun e he => (hr e he).occupied⟩

/-- The children of a balanced node whose children are occupied are good, of the height of
its first child. -/
theorem good_of_balanced_node {first : BPlusTree α β} {rest : List (Branch α β)}
    (hb : Balanced (.node first rest))
    (ho : ∀ c ∈ (BPlusTree.node first rest).children, Occupied t c) :
    Good t first.height first ∧ ∀ e ∈ rest, Good t first.height e.child :=
  ⟨⟨hb.first, rfl, ho first List.mem_cons_self⟩, fun _ he =>
    ⟨hb.of_mem_rest he, hb.height_of_mem_rest he,
      ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))⟩⟩

namespace InsertResult

/-- A leaf with more than `2 * t - 1` entries, and at most `t` more, splits into two good
leaves: the first `t` entries go left and the rest go right. -/
theorem exists_good_split_ofLeaf {entries : List (α × β)} (hlo : 2 * t - 1 < entries.length)
    (hhi : entries.length ≤ 2 * t - 1 + t) :
    ∃ l s r, ofLeaf t entries = split l s r ∧ Good t 1 l ∧ Good t 1 r := by
  have hnot : ¬ entries.length ≤ 2 * t - 1 := by omega
  simp only [ofLeaf, hnot, ↓reduceIte]
  split
  · next heq => exact absurd (List.drop_eq_nil_iff.1 heq) (by omega)
  · next p right heq =>
    have hrl := congrArg List.length heq
    simp only [List.length_drop] at hrl
    have htl : (entries.take t).length = t := by rw [List.length_take]; omega
    exact ⟨_, p.1, _, rfl, ⟨.leaf, rfl, .leaf (by omega) (by omega)⟩,
      ⟨.leaf, rfl, .leaf (by omega) (by omega)⟩⟩

/-- A node over good children of height `h` with more than `2 * t - 1` separators, and at most
`t + 1` more, splits into two good trees of height `h + 1`: the first `t` branches go left, the
separator of the next one moves up, and the rest go right. -/
theorem exists_good_split_ofNode {first : BPlusTree α β} {rest : List (Branch α β)} {h : ℕ}
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child)
    (hlo : 2 * t - 1 < rest.length) (hhi : rest.length ≤ 2 * t - 1 + t + 1) :
    ∃ l s r, ofNode t first rest = split l s r ∧ Good t (h + 1) l ∧ Good t (h + 1) r := by
  have hnot : ¬ rest.length ≤ 2 * t - 1 := by omega
  simp only [ofNode, hnot, ↓reduceIte]
  split
  · next heq => exact absurd (List.drop_eq_nil_iff.1 heq) (by omega)
  · next s c right heq =>
    have hmem : (s, c) ∈ rest := List.mem_of_mem_drop (heq ▸ List.mem_cons_self ..)
    have hright : ∀ e ∈ right, e ∈ rest := fun e he =>
      List.mem_of_mem_drop (heq ▸ List.mem_cons_of_mem _ he)
    have hrl := congrArg List.length heq
    simp only [List.length_drop, List.length_cons] at hrl
    have htl : (rest.take t).length = t := by rw [List.length_take]; omega
    exact ⟨_, s, _, rfl,
      good_node hf (fun e he => hr e (List.mem_of_mem_take he)) (by omega) (by omega),
      good_node (hr _ hmem) (fun e he => hr e (hright e he)) (by omega) (by omega)⟩

/-- The shape invariant of the result of inserting into `tr`: either a tree of the same height
with occupied children and at least as wide a root, still within `2 * t - 1`, or two good trees
of the same height. -/
private def Fits (t : ℕ) (tr : BPlusTree α β) : InsertResult α β → Prop
  | tree c => Balanced c ∧ c.height = tr.height ∧ (∀ c' ∈ c.children, Occupied t c') ∧
      tr.width ≤ c.width ∧ c.width ≤ 2 * t - 1
  | split l _ r => Good t tr.height l ∧ Good t tr.height r

/-- A leaf with at most one entry more than the `2 * t - 1` allowed, after the overflow split,
fits any leaf that had no more entries. -/
private theorem fits_ofLeaf {tr : BPlusTree α β} {entries : List (α × β)} (ht : 1 ≤ t)
    (hlen : entries.length ≤ 2 * t - 1 + 1) (hh : tr.height = 1)
    (hw : tr.width ≤ entries.length) : (ofLeaf t entries).Fits t tr := by
  by_cases hle : entries.length ≤ 2 * t - 1
  · simp only [ofLeaf, hle, ↓reduceIte]
    exact ⟨.leaf, hh.symm, by simp, hw, hle⟩
  · obtain ⟨l, s, r, heq, hl, hr⟩ :=
      exists_good_split_ofLeaf (t := t) (entries := entries) (by omega) (by omega)
    rw [heq]
    exact ⟨hh ▸ hl, hh ▸ hr⟩

/-- A node over good children of height `h` with at most one separator more than the `2 * t - 1`
allowed, after the overflow split, fits any tree of height `h + 1` that was no wider. -/
private theorem fits_ofNode {tr first : BPlusTree α β} {rest : List (Branch α β)} {h : ℕ}
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child)
    (hlen : rest.length ≤ 2 * t - 1 + 1) (hh : tr.height = h + 1)
    (hw : tr.width ≤ rest.length) : (ofNode t first rest).Fits t tr := by
  by_cases hle : rest.length ≤ 2 * t - 1
  · have hb : Balanced (.node first rest) :=
      .node hf.balanced (fun e he => (hr e he).balanced)
        fun e he => (hr e he).height_eq.trans hf.height_eq.symm
    simp only [ofNode, hle, ↓reduceIte]
    exact ⟨hb, by rw [hb.height_node, hf.height_eq, hh],
      List.forall_mem_cons.2 ⟨hf.occupied, List.forall_mem_map.2 fun e he => (hr e he).occupied⟩,
      hw, hle⟩
  · -- the node overflowed by exactly one separator
    obtain ⟨l, s, r, heq, hl, hr'⟩ := exists_good_split_ofNode hf hr (by omega) (by omega)
    rw [heq]
    exact ⟨hh ▸ hl, hh ▸ hr'⟩

/-- Placing a fitting result in the place of an occupied child of height `h` among good branches
keeps every child good, and adds at most one branch. -/
private theorem fits_withRest {c : BPlusTree α β} {x : InsertResult α β} (hx : x.Fits t c)
    (hc : Occupied t c) {h : ℕ} (hch : c.height = h) {rest : List (Branch α β)}
    (hr : ∀ e ∈ rest, Good t h e.child) :
    Good t h (x.withRest rest).1 ∧ (∀ e ∈ (x.withRest rest).2, Good t h e.child) ∧
      rest.length ≤ (x.withRest rest).2.length ∧
      (x.withRest rest).2.length ≤ rest.length + 1 := by
  cases x with
  | tree c' =>
    obtain ⟨hb, hh, hco, hk₁, hk₂⟩ := hx
    refine ⟨⟨hb, hh.trans hch, ?_⟩, hr, le_rfl, Nat.le_succ _⟩
    have := hc.le_width
    cases c' with
    | leaf es => exact .leaf (by simpa using this.trans hk₁) (by simpa using hk₂)
    | node f r =>
      exact .node (by simpa using this.trans hk₁) (by simpa using hk₂) (hco f List.mem_cons_self)
        fun e he => hco _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
  | split l s r =>
    exact ⟨hch ▸ hx.1, List.forall_mem_cons.2 ⟨hch ▸ hx.2, hr⟩, Nat.le_succ _, le_rfl⟩

end InsertResult

end Shape

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

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

mutual
/-- A monad morphism commutes with the bottom-up insertion into a subtree. -/
private theorem map_insertOrSplitM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (v : β) (tr : BPlusTree α β) :
    f (insertOrSplitM t le visit k v tr) =
      insertOrSplitM t (fun a b => f (le a b)) (f visit) k v tr := by
  match tr with
  | .leaf entries =>
    simp [insertOrSplitM_leaf, hf.map_bind, hf.map_pure, SortedAssoc.map_insertM hf]
  | .node first rest =>
    simp only [insertOrSplitM_node, hf.map_bind, map_insertRestM hf t le visit k v rest]
    refine bind_congr fun _ => bind_congr fun o => ?_
    cases o <;> simp [hf.map_bind, hf.map_pure, map_insertOrSplitM hf t le visit k v first]
termination_by sizeOf tr

/-- A monad morphism commutes with the insertion among the branches of a node. -/
private theorem map_insertRestM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (v : β) (rest : List (Branch α β)) :
    f (insertRestM t le visit k v rest) =
      insertRestM t (fun a b => f (le a b)) (f visit) k v rest := by
  match rest with
  | [] => simp [hf.map_pure]
  | (s, c) :: rest =>
    simp only [insertRestM_cons, hf.map_bind, apply_ite f, hf.map_pure,
      map_insertRestM hf t le visit k v rest]
    refine bind_congr fun b => ?_
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    refine bind_congr fun o => ?_
    cases o <;> simp [hf.map_bind, hf.map_pure, map_insertOrSplitM hf t le visit k v c]
termination_by sizeOf rest
end

/-- A monad morphism commutes with insertion. -/
theorem map_insertM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool) (visit : m Unit)
    (k : α) (v : β) (tr : BPlusTree α β) :
    f (insertM t le visit k v tr) = insertM t (fun a b => f (le a b)) (f visit) k v tr := by
  simp [insertM, hf.map_bind, hf.map_pure, map_insertOrSplitM hf]

end Transfer

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

/-- Insertion is the bottom-up insertion with an overflow grown into a new root. -/
theorem insert_eq_toTree (tr : BPlusTree α β) :
    insert t k v tr = (insertOrSplit t k v tr).toTree := rfl

/-- Insertion into a leaf places the entry in its entry list and splits on overflow. -/
theorem insertOrSplit_leaf (entries : List (α × β)) :
    insertOrSplit t k v (.leaf entries) = .ofLeaf t (SortedAssoc.insert k v entries) :=
  congrArg (InsertResult.ofLeaf t) (SortedAssoc.idRun_insertM k v entries)

/-- Insertion into a node: search its separators, descending into the first child when the key
is below them, then split on overflow. -/
theorem insertOrSplit_node (first : BPlusTree α β) (rest : List (Branch α β)) :
    insertOrSplit t k v (.node first rest) =
      match insertRest t k v rest with
      | some rest' => .ofNode t first rest'
      | none =>
        let p := (insertOrSplit t k v first).withRest rest
        .ofNode t p.1 p.2 := by
  -- In `Id`, bind is application and `pure` is the identity, so after unfolding, each branch of
  -- the monadic `match` is the corresponding pure branch by definition.
  simp only [insertOrSplit, insertRest, insertOrSplitM]
  cases insertRestM t leI (pure ()) k v rest <;> rfl

/-- The search past the last branch defers to the child before it. -/
@[simp] theorem insertRest_nil : insertRest t k v ([] : List (Branch α β)) = none := rfl

/-- The search at a branch: defer when its separator is above the key, and otherwise move on,
descending into this branch's child when the later branches defer. -/
theorem insertRest_cons (s : α) (c : BPlusTree α β) (rest : List (Branch α β)) :
    insertRest t k v ((s, c) :: rest) =
      if s ≤ k then
        match insertRest t k v rest with
        | some rest' => some ((s, c) :: rest')
        | none =>
          let p := (insertOrSplit t k v c).withRest rest
          some ((s, p.1) :: p.2)
      else none := by
  by_cases h : s ≤ k
  · simp only [insertRest, insertOrSplit, insertRestM, leI, h, decide_true, ↓reduceIte,
      pure_bind, bind_pure_comp]
    -- as in `insertOrSplit_node`, each branch in `Id` is the pure branch by definition
    cases insertRestM t leI (pure ()) k v rest <;> rfl
  · simp [insertRest, insertRestM, leI, h]

/-! ### The model equation -/

/-- The search among the branches of a node, against the model. The branches follow a sorted
prefix `pre` whose keys are below every separator; each separator is at most the keys of its
child, no child is empty, and the keys of each child are below the later separators. When the
search defers to the child before the branches, the key is below all their entries; otherwise it
performs the model insertion after the prefix. -/
private theorem insertRest_spec {rest : List (Branch α β)} (pre : List (α × β))
    (hs : (pre ++ rest.flatMap fun e => e.child.toList).IsSortedAssoc)
    (hle : ∀ e ∈ rest, ∀ p ∈ e.child.toList, e.1 ≤ p.1)
    (hne : ∀ e ∈ rest, e.child.toList ≠ [])
    (hpre : ∀ p ∈ pre, ∀ e ∈ rest, p.1 < e.1)
    (hpw : rest.Pairwise fun a b => ∀ p ∈ a.child.toList, p.1 < b.1)
    (hc : ∀ e ∈ rest,
      (insertOrSplit t k v e.child).toList = SortedAssoc.insert k v e.child.toList) :
    (insertRest t k v rest = none → ∀ p ∈ rest.flatMap fun e => e.child.toList, k < p.1) ∧
      ∀ r, insertRest t k v rest = some r →
        (pre ++ r.flatMap fun e => e.child.toList) =
          SortedAssoc.insert k v (pre ++ rest.flatMap fun e => e.child.toList) := by
  induction rest generalizing pre with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [List.flatMap_cons, Branch.child_mk] at hs ⊢
    obtain ⟨hpw₁, hpw₂⟩ := List.pairwise_cons.1 hpw
    obtain ⟨hcs, hle⟩ := List.forall_mem_cons.1 hle
    obtain ⟨hcne, hne⟩ := List.forall_mem_cons.1 hne
    obtain ⟨hcc, hc⟩ := List.forall_mem_cons.1 hc
    rw [insertRest_cons]
    by_cases hk : s ≤ k
    · -- the separator is passed: the key belongs to this child or a later one
      have ih := ih (pre ++ c.toList) (by simpa only [List.append_assoc] using hs) hle hne
        (fun p hp e he => (List.mem_append.1 hp).elim
          (fun hp => hpre p hp e (List.mem_cons_of_mem _ he)) (hpw₁ e he p))
        hpw₂ hc
      simp only [hk, ↓reduceIte]
      cases hr' : insertRest t k v rest with
      | some r' =>
        refine ⟨nofun, ?_⟩
        rintro _ ⟨rfl⟩
        simpa only [List.flatMap_cons, Branch.child_mk, List.append_assoc] using ih.2 r' hr'
      | none =>
        refine ⟨nofun, ?_⟩
        rintro _ ⟨rfl⟩
        have hlt : ∀ p ∈ pre, p.1 < k := fun p hp =>
          (hpre p hp (s, c) List.mem_cons_self).trans_le hk
        rw [← List.append_assoc, SortedAssoc.insert_append_of_forall_gt (ih.1 hr'),
          SortedAssoc.insert_append_of_forall_lt hlt, ← hcc,
          List.flatMap_cons, Branch.child_mk, InsertResult.toList_withRest, List.append_assoc]
    · -- the separator is above the key: defer to the child before it
      have hk' : k < s := lt_of_not_ge hk
      simp only [hk, ↓reduceIte]
      refine ⟨fun _ p hp => ?_, fun _ => nofun⟩
      rcases List.mem_append.1 hp with hp | hp
      · exact hk'.trans_le (hcs p hp)
      · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hcne
        rw [List.isSortedAssoc_append_iff, List.isSortedAssoc_append_iff] at hs
        exact (hk'.trans_le (hcs q hq)).trans (hs.2.1.2.2 q hq p hp)

/-- Model equation of the bottom-up insertion under the search invariant. -/
private theorem toList_insertOrSplit_of (k : α) (v : β) (tr : BPlusTree α β)
    (h : SearchInvariant t tr) :
    (insertOrSplit t k v tr).toList = SortedAssoc.insert k v tr.toList := by
  induction tr with
  | leaf entries => rw [insertOrSplit_leaf, InsertResult.toList_ofLeaf, toList_leaf]
  | node first rest ihf ihr =>
    have hp := h.separated
    have hmem : ∀ e ∈ rest, e.child ∈ (BPlusTree.node first rest).children :=
      fun e he => List.mem_cons_of_mem _ (List.mem_map_of_mem he)
    have spec := insertRest_spec (t := t) (k := k) (v := v) first.toList
      (by simpa only [toList_node] using h.sorted) (fun e he p hp' => hp.le_of_mem he hp')
      (fun e he => List.ne_nil_of_length_pos ((h.occupied _ (hmem e he)).size_pos h.two_le))
      (fun p hp' e he => hp.lt_of_mem_first he hp') hp.pairwise
      (fun e he => ihr e he (h.child (hmem e he)))
    rw [insertOrSplit_node]
    cases hr : insertRest t k v rest with
    | some r => simpa only [InsertResult.toList_ofNode, toList_node] using spec.2 r hr
    | none =>
      simp only [InsertResult.toList_ofNode, toList_node, InsertResult.toList_withRest,
        ihf (h.child List.mem_cons_self), SortedAssoc.insert_append_of_forall_gt (spec.1 hr)]

/-! ### The shape of the result -/

/-- The search among the branches of a node keeps every child good, and adds at most one
branch. -/
private theorem fits_insertRest {rest : List (Branch α β)} {h : ℕ}
    (hc : ∀ e ∈ rest, Good t h e.child ∧ (insertOrSplit t k v e.child).Fits t e.child)
    {r : List (Branch α β)} (hr : insertRest t k v rest = some r) :
    (∀ e ∈ r, Good t h e.child) ∧ rest.length ≤ r.length ∧ r.length ≤ rest.length + 1 := by
  induction rest generalizing r with
  | nil => simp at hr
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨⟨hcg, hcf⟩, hcr⟩ := List.forall_mem_cons.1 hc
    rw [insertRest_cons] at hr
    split_ifs at hr with hk
    cases hr' : insertRest t k v rest <;> rw [hr'] at hr <;> obtain ⟨rfl⟩ := hr
    · obtain ⟨hp₁, hp₂, hl₁, hl₂⟩ :=
        InsertResult.fits_withRest hcf hcg.occupied hcg.height_eq fun e he => (hcr e he).1
      exact ⟨List.forall_mem_cons.2 ⟨hp₁, hp₂⟩, by simpa using hl₁, by simpa using hl₂⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih hcr hr'
      exact ⟨List.forall_mem_cons.2 ⟨hcg, h₁⟩, by simpa using h₂, by simpa using h₃⟩

/-- Shape invariant of the bottom-up insertion. -/
private theorem fits_insertOrSplit (ht : 1 ≤ t) (k : α) (v : β) (tr : BPlusTree α β)
    (hb : Balanced tr) (ho : ∀ c ∈ tr.children, Occupied t c) (hw : tr.width ≤ 2 * t - 1)
    (hs : tr.toList.IsSortedAssoc) : (insertOrSplit t k v tr).Fits t tr := by
  induction tr with
  | leaf entries =>
    rw [toList_leaf] at hs
    rw [width_leaf] at hw
    have hlen := SortedAssoc.length_insert (k := k) (v := v) hs
    rw [insertOrSplit_leaf]
    exact InsertResult.fits_ofLeaf ht (by split at hlen <;> omega) rfl
      (by rw [width_leaf]; split at hlen <;> omega)
  | node first rest ihf ihr =>
    obtain ⟨hf, hr⟩ := good_of_balanced_node hb ho
    -- the hypotheses of the induction, for an occupied child
    have hchild : ∀ c ∈ (BPlusTree.node first rest).children, Occupied t c →
        (∀ c' ∈ c.children, Occupied t c') ∧ c.width ≤ 2 * t - 1 ∧ c.toList.IsSortedAssoc :=
      fun _ hc hoc => ⟨fun _ hc' => hoc.of_mem_children hc', hoc.width_le,
        hs.sublist (toList_sublist_of_mem_children hc)⟩
    have hrest : ∀ e ∈ rest, Good t first.height e.child ∧
        (insertOrSplit t k v e.child).Fits t e.child := fun e he => by
      obtain ⟨h₁, h₂, h₃⟩ := hchild _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
        (hr e he).occupied
      exact ⟨hr e he, ihr e he (hr e he).balanced h₁ h₂ h₃⟩
    have hh := hb.height_node
    rw [width_node] at hw
    rw [insertOrSplit_node]
    cases hrs : insertRest t k v rest with
    | some r =>
      obtain ⟨h₁, h₂, h₃⟩ := fits_insertRest hrest hrs
      exact InsertResult.fits_ofNode hf h₁ (by omega) hh (by simpa using h₂)
    | none =>
      obtain ⟨h₁, h₂, h₃⟩ := hchild first List.mem_cons_self hf.occupied
      obtain ⟨hp₁, hp₂, hl₁, hl₂⟩ :=
        InsertResult.fits_withRest (ihf hb.first h₁ h₂ h₃) hf.occupied rfl hr
      exact InsertResult.fits_ofNode hp₁ hp₂ (by omega) hh (by simpa using hl₁)

/-! ### The separator convention of the result -/

/-- The separator convention between neighbours: each separator is above the keys of the child
before it and at most the keys of its own child. When no child is empty this is the whole
convention at a node (`separated_node_of_linked`), and insertion changes it at one place. -/
@[expose] def Linked : BPlusTree α β → List (Branch α β) → Prop
  | _, [] => True
  | prev, (s, c) :: rest =>
    (∀ p ∈ prev.toList, p.1 < s) ∧ (∀ p ∈ c.toList, s ≤ p.1) ∧ Linked c rest

/-- The separator convention at a node holds between its neighbouring children. -/
theorem Separated.linked {first : BPlusTree α β} {rest : List (Branch α β)}
    (h : Separated (.node first rest)) : Linked first rest := by
  induction rest generalizing first with
  | nil => trivial
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    exact ⟨fun p hp => h.lt_of_mem_first (e := (s, c)) List.mem_cons_self hp,
      fun p hp => h.le_of_mem (e := (s, c)) List.mem_cons_self hp, ih h.tail⟩

/-- When no child among the branches is empty, the separator convention between neighbouring
children, over separated children, is the convention at the node. -/
theorem separated_node_of_linked {first : BPlusTree α β} {rest : List (Branch α β)}
    (hl : Linked first rest) (hf : Separated first) (hr : ∀ e ∈ rest, Separated e.child)
    (hne : ∀ e ∈ rest, e.child.toList ≠ []) : Separated (.node first rest) := by
  induction rest generalizing first with
  | nil => exact .node hf (by simp) (by simp) .nil (by simp)
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨h₁, h₂, h₃⟩ := hl
    have hc := ih h₃ (hr (s, c) List.mem_cons_self)
      (fun e he => hr e (List.mem_cons_of_mem _ he))
      (fun e he => hne e (List.mem_cons_of_mem _ he))
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (hne (s, c) List.mem_cons_self)
    exact .node hf hr (List.forall_mem_cons.2 ⟨h₂, fun e he p hp => hc.le_of_mem he hp⟩)
      (List.pairwise_cons.2 ⟨fun b hb p hp => hc.lt_of_mem_first hb hp, hc.pairwise⟩)
      (List.forall_mem_cons.2 ⟨h₁, fun e he p hp =>
        lt_of_lt_of_le (h₁ p hp) ((h₂ q hq).trans (hc.lt_of_mem_first he hq).le)⟩)

/-- The separator convention of a result: a separated tree, or two separated trees with the keys
of the left one below the separator and those of the right one at least it. -/
@[expose] def Sep : InsertResult α β → Prop
  | .tree c => Separated c
  | .split l s r =>
    Separated l ∧ Separated r ∧ (∀ p ∈ l.toList, p.1 < s) ∧ ∀ p ∈ r.toList, s ≤ p.1

/-- The split of a leaf with sorted entries has the separator convention. -/
theorem sep_ofLeaf {entries : List (α × β)} (hs : entries.IsSortedAssoc) :
    Sep (InsertResult.ofLeaf t entries) := by
  unfold InsertResult.ofLeaf
  split_ifs
  · exact Separated.leaf
  · split
    · exact Separated.leaf
    · next p right heq =>
      have he : entries = entries.take t ++ p :: right := by rw [← heq, List.take_append_drop]
      rw [he, List.isSortedAssoc_append_iff] at hs
      refine ⟨.leaf, .leaf, fun q hq => hs.2.2 q (by simpa using hq) p List.mem_cons_self,
        fun q hq => ?_⟩
      rw [toList_leaf] at hq
      rcases List.mem_cons.1 hq with rfl | hq
      exacts [le_rfl, ((List.isSortedAssoc_cons_iff.1 hs.2.1).1 q hq).le]

/-- The split of a separated node without empty children among its branches has the separator
convention. -/
theorem sep_ofNode {first : BPlusTree α β} {rest : List (Branch α β)}
    (h : Separated (.node first rest)) (hne : ∀ e ∈ rest, e.child.toList ≠ []) :
    Sep (InsertResult.ofNode t first rest) := by
  unfold InsertResult.ofNode
  split_ifs
  · exact h
  · split
    · exact h
    · next s c right heq =>
      have hmem : ∀ e ∈ (s, c) :: right, e ∈ rest := fun e he =>
        List.mem_of_mem_drop (heq ▸ he)
      have hdrop : ((s, c) :: right).Pairwise fun a b : Branch α β =>
          ∀ p ∈ a.child.toList, p.1 < b.1 :=
        heq ▸ h.pairwise.sublist (List.drop_sublist t rest)
      obtain ⟨hd₁, hd₂⟩ := List.pairwise_cons.1 hdrop
      have hsc : (s, c) ∈ rest := hmem _ List.mem_cons_self
      have htake : ∀ a ∈ rest.take t, ∀ p ∈ a.child.toList, p.1 < s := by
        have hp := h.pairwise
        rw [← List.take_append_drop t rest, heq] at hp
        exact fun a ha => (List.pairwise_append.1 hp).2.2 a ha (s, c) List.mem_cons_self
      refine ⟨.node h.first (fun e he => h.of_mem_rest (List.mem_of_mem_take he))
          (fun e he p hp => h.le_of_mem (List.mem_of_mem_take he) hp)
          (h.pairwise.sublist (List.take_sublist _ _))
          (fun e he p hp => h.lt_of_mem_first (List.mem_of_mem_take he) hp),
        .node (h.of_mem_rest hsc)
          (fun e he => h.of_mem_rest (hmem e (List.mem_cons_of_mem _ he)))
          (fun e he p hp => h.le_of_mem (hmem e (List.mem_cons_of_mem _ he)) hp) hd₂
          (fun e he p hp => hd₁ e he p hp), fun p hp => ?_, fun p hp => ?_⟩
      · rw [toList_node, List.mem_append, List.mem_flatMap] at hp
        rcases hp with hp | ⟨a, ha, hp⟩
        exacts [h.lt_of_mem_first hsc hp, htake a ha p hp]
      · rw [toList_node, List.mem_append, List.mem_flatMap] at hp
        rcases hp with hp | ⟨e, he, hp⟩
        · exact h.le_of_mem hsc hp
        · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (hne (s, c) hsc)
          exact (h.le_of_mem hsc hq).trans ((hd₁ e he q hq).le.trans
            (h.le_of_mem (hmem e (List.mem_cons_of_mem _ he)) hp))

omit [LinearOrder α] in
/-- The entries of the tree that takes the place of a child are entries of the result. -/
theorem mem_toList_of_mem_withRest_fst {x : InsertResult α β} {rest : List (Branch α β)}
    {p : α × β} (hp : p ∈ (x.withRest rest).1.toList) : p ∈ x.toList := by
  rcases x with c | ⟨l, s, r⟩
  exacts [hp, List.mem_append_left _ hp]

/-- The convention between neighbours looks at a child only through the bound of the next
separator on its keys. -/
theorem Linked.of_forall_lt {a b : BPlusTree α β} {rest : List (Branch α β)}
    (hl : Linked a rest)
    (hb : ∀ s c rest', rest = (s, c) :: rest' → ∀ p ∈ b.toList, p.1 < s) : Linked b rest := by
  rcases rest with _ | ⟨⟨s, c⟩, rest⟩
  exacts [trivial, ⟨hb s c rest rfl, hl.2.1, hl.2.2⟩]

/-- Placing a result with the separator convention in the place of a child linked to `rest`
keeps the convention between neighbours, when the keys of the result are below the next
separator. -/
theorem linked_withRest_of_sep {x : InsertResult α β} {c : BPlusTree α β}
    {rest : List (Branch α β)} (hx : Sep x) (hl : Linked c rest)
    (hr : ∀ e ∈ rest, Separated e.child)
    (hb : ∀ s c' rest', rest = (s, c') :: rest' → ∀ p ∈ x.toList, p.1 < s) :
    Linked (x.withRest rest).1 (x.withRest rest).2 ∧ Separated (x.withRest rest).1 ∧
      ∀ e ∈ (x.withRest rest).2, Separated e.child := by
  cases x with
  | tree m => exact ⟨hl.of_forall_lt hb, hx, hr⟩
  | split l' s' r' =>
    obtain ⟨hl', hr', h₁, h₂⟩ := hx
    exact ⟨⟨h₁, h₂, hl.of_forall_lt fun s c' rest' h p hp =>
      hb s c' rest' h p (List.mem_append_right _ hp)⟩, hl', List.forall_mem_cons.2 ⟨hr', hr⟩⟩

/-- Placing a result with the separator convention in the place of a child keeps the convention
between neighbours, when every key of the result is the inserted key or a key of the child, and
the inserted key is below the next separator. -/
private theorem linked_withRest {prev : BPlusTree α β} {x : InsertResult α β}
    {rest : List (Branch α β)} (hx : Sep x)
    (hkeys : ∀ p ∈ x.toList, p.1 = k ∨ p ∈ prev.toList) (hl : Linked prev rest)
    (hr : ∀ e ∈ rest, Separated e.child)
    (hk : ∀ s c rest', rest = (s, c) :: rest' → k < s) :
    Linked (x.withRest rest).1 (x.withRest rest).2 ∧ Separated (x.withRest rest).1 ∧
      ∀ e ∈ (x.withRest rest).2, Separated e.child :=
  linked_withRest_of_sep hx hl hr fun s c rest' h p hp => by
    subst h
    exact (hkeys p hp).elim (fun e => e ▸ hk s c rest' rfl) (hl.1 p)

/-- The search among the branches of a node keeps the separator convention between neighbours
and keeps every child separated. When it defers, the key is below the first separator. -/
private theorem linked_insertRest {prev : BPlusTree α β} {rest : List (Branch α β)}
    (hl : Linked prev rest) (hr : ∀ e ∈ rest, Separated e.child)
    (hc : ∀ e ∈ rest, Sep (insertOrSplit t k v e.child) ∧
      ∀ p ∈ (insertOrSplit t k v e.child).toList, p.1 = k ∨ p ∈ e.child.toList) :
    (insertRest t k v rest = none → ∀ s c rest', rest = (s, c) :: rest' → k < s) ∧
      ∀ r, insertRest t k v rest = some r → Linked prev r ∧ ∀ e ∈ r, Separated e.child := by
  induction rest generalizing prev with
  | nil => exact ⟨fun _ s c rest' h => (nomatch h), fun r hr => by simp at hr⟩
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨h₁, h₂, h₃⟩ := hl
    obtain ⟨hsc, hrr⟩ := List.forall_mem_cons.1 hr
    obtain ⟨⟨hsx, hkx⟩, hrc⟩ := List.forall_mem_cons.1 hc
    obtain ⟨ihn, ihs⟩ := ih h₃ hrr hrc
    rw [insertRest_cons]
    by_cases hk : s ≤ k
    · simp only [hk, ↓reduceIte]
      cases hrs : insertRest t k v rest with
      | some r' =>
        obtain ⟨hl', hs'⟩ := ihs r' hrs
        exact ⟨nofun, fun _ h =>
          Option.some.inj h ▸ ⟨⟨h₁, h₂, hl'⟩, List.forall_mem_cons.2 ⟨hsc, hs'⟩⟩⟩
      | none =>
        obtain ⟨hlw, hsw₁, hsw₂⟩ := linked_withRest hsx hkx h₃ hrr (ihn hrs)
        refine ⟨nofun, ?_⟩
        rintro _ ⟨rfl⟩
        exact ⟨⟨h₁, fun p hp => (hkx p (mem_toList_of_mem_withRest_fst hp)).elim (· ▸ hk) (h₂ p),
          hlw⟩, List.forall_mem_cons.2 ⟨hsw₁, hsw₂⟩⟩
    · simp only [hk, ↓reduceIte]
      exact ⟨fun _ _ _ _ h => (Prod.mk.inj (List.cons.inj h).1).1 ▸ lt_of_not_ge hk,
        fun _ => nofun⟩

/-- The bottom-up insertion keeps the separator convention. -/
private theorem sep_insertOrSplit (k : α) (v : β) (tr : BPlusTree α β)
    (h : SearchInvariant t tr) (hb : Balanced tr) (hw : tr.width ≤ 2 * t - 1) :
    Sep (insertOrSplit t k v tr) := by
  induction tr with
  | leaf entries =>
    rw [insertOrSplit_leaf]
    exact sep_ofLeaf (SortedAssoc.isSortedAssoc_insert (by simpa only [toList_leaf] using h.sorted))
  | node first rest ihf ihr =>
    obtain ⟨hgf, hgr⟩ := good_of_balanced_node hb h.occupied
    have hp := h.separated
    have ht1 : 1 ≤ t := Nat.le_of_succ_le h.two_le
    have hne : ∀ {h : ℕ} {c : BPlusTree α β}, Good t h c → c.toList ≠ [] := fun hg =>
      List.ne_nil_of_length_pos (hg.occupied.size_pos h.two_le)
    -- what the three inductions give for a child of the node
    have hchild : ∀ c ∈ (BPlusTree.node first rest).children, Good t first.height c →
        (SearchInvariant t c → Balanced c → c.width ≤ 2 * t - 1 →
          Sep (insertOrSplit t k v c)) →
        (insertOrSplit t k v c).Fits t c ∧ Sep (insertOrSplit t k v c) ∧
          ∀ p ∈ (insertOrSplit t k v c).toList, p.1 = k ∨ p ∈ c.toList := by
      intro c hc hg ih
      have hsc := h.child hc
      refine ⟨fits_insertOrSplit ht1 k v c hg.balanced hsc.occupied hg.occupied.width_le hsc.sorted,
        ih hsc hg.balanced hg.occupied.width_le, fun p hp' => ?_⟩
      rw [toList_insertOrSplit_of k v c hsc] at hp'
      exact (SortedAssoc.eq_or_mem_of_mem_insert hp').imp_left (congrArg Prod.fst)
    have hrest := fun e (he : e ∈ rest) =>
      hchild e.child (List.mem_cons_of_mem _ (List.mem_map_of_mem he)) (hgr e he) (ihr e he)
    have hlink := linked_insertRest (t := t) (k := k) (v := v) hp.linked
      (fun e he => hp.of_mem_rest he) fun e he => (hrest e he).2
    rw [insertOrSplit_node]
    cases hrs : insertRest t k v rest with
    | some r =>
      obtain ⟨hl, hsr⟩ := hlink.2 r hrs
      obtain ⟨hg, -, -⟩ := fits_insertRest (fun e he => ⟨hgr e he, (hrest e he).1⟩) hrs
      exact sep_ofNode (separated_node_of_linked hl hp.first hsr fun e he => hne (hg e he))
        fun e he => hne (hg e he)
    | none =>
      obtain ⟨hff, hfs, hfk⟩ := hchild first List.mem_cons_self hgf ihf
      obtain ⟨hl, hs₁, hs₂⟩ := linked_withRest hfs hfk hp.linked
        (fun e he => hp.of_mem_rest he) (hlink.1 hrs)
      obtain ⟨-, hg, -, -⟩ := InsertResult.fits_withRest hff hgf.occupied rfl hgr
      exact sep_ofNode (separated_node_of_linked hl hs₁ hs₂ fun e he => hne (hg e he))
        fun e he => hne (hg e he)

/-! ### Insertion on well-formed trees -/

variable {tr : BPlusTree α β}

/-- Model equation of insertion on well-formed trees. -/
theorem toList_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).toList = SortedAssoc.insert k v tr.toList := by
  rw [insert_eq_toTree, InsertResult.toList_toTree,
    toList_insertOrSplit_of k v tr h.searchInvariant]

/-- Insertion preserves well-formedness. -/
theorem IsWF.insert (h : IsWF t tr) (k : α) (v : β) : IsWF t (insert t k v tr) := by
  have ht := h.two_le
  have hf := fits_insertOrSplit (by omega) k v tr h.balanced h.occupied_of_mem_children
    h.width_le h.sorted
  have hp := sep_insertOrSplit k v tr h.searchInvariant h.balanced h.width_le
  have hs : (BPlusTree.insert t k v tr).toList.IsSortedAssoc :=
    toList_insert h k v ▸ SortedAssoc.isSortedAssoc_insert h.sorted
  rw [insert_eq_toTree] at hs ⊢
  rcases hx : insertOrSplit t k v tr with c | ⟨l, s, r⟩ <;> rw [hx] at hf hp hs
  · obtain ⟨hb, hh, hco, hk₁, hk₂⟩ := hf
    refine ⟨ht, hk₂, fun hne => ?_, hco, hb, hp, hs⟩
    cases tr with
    | leaf entries =>
      obtain ⟨es, rfl⟩ := height_eq_one_iff.1 hh
      exact absurd rfl (hne es)
    | node first rest => exact (h.width_pos nofun).trans hk₁
  · obtain ⟨hl, hr⟩ := hf
    obtain ⟨hpl, hpr, hlt, hle⟩ := hp
    exact ⟨ht, by simp [InsertResult.toTree]; omega,
      fun _ => by simp [InsertResult.toTree],
      List.forall_mem_cons.2 ⟨hl.occupied, List.forall_mem_singleton.2 hr.occupied⟩,
      .node hl.balanced (by simpa using hr.balanced)
        (by simpa using hr.height_eq.trans hl.height_eq.symm),
      .node hpl (by simpa using hpr) (by simpa using hle) (List.pairwise_singleton _ _)
        (by simpa using hlt), hs⟩

/-- On a well-formed tree, insertion keeps the height unless the root splits, and then raises
it by one. -/
theorem height_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).height =
      match insertOrSplit t k v tr with
      | .tree _ => tr.height
      | .split .. => tr.height + 1 := by
  have hf := fits_insertOrSplit (by have := h.two_le; omega) k v tr h.balanced
    h.occupied_of_mem_children h.width_le h.sorted
  rw [insert_eq_toTree]
  rcases hx : insertOrSplit t k v tr with c | ⟨l, s, r⟩ <;> rw [hx] at hf
  · exact hf.2.1
  · have hb : Balanced (.node l [(s, r)]) :=
      .node hf.1.balanced (by simpa using hf.2.balanced)
        (by simpa using hf.2.height_eq.trans hf.1.height_eq.symm)
    exact hb.height_node.trans (congrArg (· + 1) hf.1.height_eq)

/-- Insertion raises the height by at most one. -/
theorem height_insert_le (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).height ≤ tr.height + 1 := by
  cases h' : insertOrSplit t k v tr <;> simp [height_insert h, h']

/-- Insertion never lowers the height. -/
theorem height_le_height_insert (h : IsWF t tr) (k : α) (v : β) :
    tr.height ≤ (insert t k v tr).height := by
  cases h' : insertOrSplit t k v tr <;> simp [height_insert h, h']

/-- Insertion keeps the size when the key is present and adds one otherwise. -/
theorem size_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).size = if (lookup k tr).isSome then tr.size else tr.size + 1 := by
  rw [← length_toList (tr := insert t k v tr), toList_insert h,
    SortedAssoc.length_insert h.sorted, lookup_eq h, length_toList]

end Pure

end BPlusTree

end Cslib.DataStructure

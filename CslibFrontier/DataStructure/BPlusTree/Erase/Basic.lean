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
one leaf and removes the entry there. A separator changes only in `mergeSplit`: a separator equal
to the erased key stays where it is, and need not be a key afterwards, unless a repair drops or
replaces it.

Each operation is defined once over an arbitrary monad `m`, with a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, and no order instance in scope.
The pure operations are the `Id` instantiations with the comparator `Cslib.SortedAssoc.leI` of a
linear order and `visit := pure ()`. `visit` fires once at each node on the path from the root to
the leaf, and once more for each sibling a repair inspects. At an interior node the separators
are scanned as in `slotM`, one comparison per separator passed and one more where the scan stops.
In the leaf the entry is removed by `Cslib.SortedAssoc.eraseM`. `eraseRestM` takes the child
before the branches together with its erasure as a delayed computation, a function from `Unit`:
the recursion is then structural, so the definitions are `@[expose]`d and `decide` evaluates
erasure on concrete trees, and the erasure of a child is run only where the search descends, in
`Id` as in any other monad. Costs are not stated here.

## Main definitions

* `underflows`, `mergeSplit`, `collapse`: underflow, the sibling repair and the root collapse.
* `rebalanceRightM`, `rebalanceLastM`: the repairs against the right and the left sibling.
* `eraseSubtreeM`, `eraseRestM`, `eraseM`: erasure, polymorphic.
* `erase`: the pure operation.

## Main results

* `map_eraseM`: a monad morphism commutes with erasure.
* `toList_erase`: on a well-formed tree, the entries after erasure are `Cslib.SortedAssoc.erase`
  of the entries.
* `IsWF.erase`: erasure preserves well-formedness.
* `height_erase`: the height stays or falls by one.
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
    let p ← eraseRestM t le visit k first (fun _ => eraseSubtreeM t le visit k first) rest
    pure (.node p.1 p.2)

/-- Erasure among the branches after the child `prev`, whose erasure is `prevErased ()`, scanning
the separators in order with the comparisons of `slotM`. At a separator above the key, `prev` is
erased from and repaired against its right sibling. Past the last separator, the last child is
erased from and repaired against its left sibling. -/
@[expose] def eraseRestM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BPlusTree α β) (prevErased : Unit → m (BPlusTree α β)) :
    List (Branch α β) → m (BPlusTree α β × List (Branch α β))
  | [] => do return (← prevErased (), [])
  | (s, c) :: rest => do
    if ← le s k then
      match rest with
      | [] => do rebalanceLastM t visit prev s (← eraseSubtreeM t le visit k c)
      | _ :: _ => do
        let p ← eraseRestM t le visit k c (fun _ => eraseSubtreeM t le visit k c) rest
        pure (prev, (s, p.1) :: p.2)
    else
      rebalanceRightM t visit (← prevErased ()) s c rest
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
      let p ← eraseRestM t le visit k first (fun _ => eraseSubtreeM t le visit k first) rest
      pure (.node p.1 p.2)) := rfl

/-- Past the last branch, the erasure of the preceding child is the result. -/
theorem eraseRestM_nil (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BPlusTree α β) (prevErased : Unit → m (BPlusTree α β)) :
    eraseRestM t le visit k prev prevErased [] = (do return (← prevErased (), [])) := rfl

/-- At a branch: when its separator is above the key, erase from the preceding child and repair
it against this child; otherwise move on, erasing from the last child and repairing it against
its left sibling. -/
theorem eraseRestM_cons (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α)
    (prev : BPlusTree α β) (prevErased : Unit → m (BPlusTree α β)) (s : α) (c : BPlusTree α β)
    (rest : List (Branch α β)) :
    eraseRestM t le visit k prev prevErased ((s, c) :: rest) = (do
      if ← le s k then
        match rest with
        | [] => do rebalanceLastM t visit prev s (← eraseSubtreeM t le visit k c)
        | _ :: _ => do
          let p ← eraseRestM t le visit k c (fun _ => eraseSubtreeM t le visit k c) rest
          pure (prev, (s, p.1) :: p.2)
      else
        rebalanceRightM t visit (← prevErased ()) s c rest) := rfl

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the repair against the right sibling. -/
private theorem map_rebalanceRightM (hf : IsMonadHom m n f) (t : ℕ) (visit : m Unit)
    (c : BPlusTree α β) (s : α) (r : BPlusTree α β) (rest : List (Branch α β)) :
    f (rebalanceRightM t visit c s r rest) = rebalanceRightM t (f visit) c s r rest := by
  simp [rebalanceRightM_def, apply_ite f, hf.map_bind, hf.map_pure]

/-- A monad morphism commutes with the repair against the left sibling. -/
private theorem map_rebalanceLastM (hf : IsMonadHom m n f) (t : ℕ) (visit : m Unit)
    (prev : BPlusTree α β) (s : α) (c : BPlusTree α β) :
    f (rebalanceLastM t visit prev s c) = rebalanceLastM t (f visit) prev s c := by
  simp [rebalanceLastM_def, apply_ite f, hf.map_bind, hf.map_pure]

mutual
/-- A monad morphism commutes with erasure from a subtree. -/
private theorem map_eraseSubtreeM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BPlusTree α β) :
    f (eraseSubtreeM t le visit k tr) =
      eraseSubtreeM t (fun a b => f (le a b)) (f visit) k tr := by
  match tr with
  | .leaf entries =>
    simp [eraseSubtreeM_leaf, hf.map_bind, hf.map_pure, SortedAssoc.map_eraseM hf]
  | .node first rest =>
    simp [eraseSubtreeM_node, hf.map_bind, hf.map_pure,
      map_eraseRestM hf t le visit k first _ rest, map_eraseSubtreeM hf t le visit k first]
termination_by sizeOf tr

/-- A monad morphism commutes with erasure among the branches of a node. -/
private theorem map_eraseRestM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (prev : BPlusTree α β) (prevErased : Unit → m (BPlusTree α β))
    (rest : List (Branch α β)) :
    f (eraseRestM t le visit k prev prevErased rest) =
      eraseRestM t (fun a b => f (le a b)) (f visit) k prev (fun u => f (prevErased u))
        rest := by
  match rest with
  | [] => simp [eraseRestM_nil, hf.map_bind, hf.map_pure]
  | (s, c) :: rest =>
    simp only [eraseRestM_cons, hf.map_bind]
    refine bind_congr fun b => ?_
    cases b
    · simp [hf.map_bind, map_rebalanceRightM hf]
    · rcases rest with _ | ⟨e, rest⟩
      · simp [hf.map_bind, map_rebalanceLastM hf, map_eraseSubtreeM hf t le visit k c]
      · simp [hf.map_bind, hf.map_pure, map_eraseSubtreeM hf t le visit k c,
          map_eraseRestM hf t le visit k c _ (e :: rest)]
termination_by sizeOf rest
end

/-- A monad morphism commutes with erasure. -/
theorem map_eraseM (hf : IsMonadHom m n f) (t : ℕ) (le : α → α → m Bool) (visit : m Unit)
    (k : α) (tr : BPlusTree α β) :
    f (eraseM t le visit k tr) = eraseM t (fun a b => f (le a b)) (f visit) k tr := by
  simp [eraseM_def, hf.map_bind, hf.map_pure, map_eraseSubtreeM hf]

end Transfer

section PureStructure

variable {α β : Type} {t : ℕ}

/-- Pure repair of a child against its right sibling. -/
private def rebalanceRight (t : ℕ) (c : BPlusTree α β) (s : α) (r : BPlusTree α β)
    (rest : List (Branch α β)) : BPlusTree α β × List (Branch α β) :=
  Id.run (rebalanceRightM t (pure ()) c s r rest)

/-- Pure repair of a last child against its left sibling. -/
private def rebalanceLast (t : ℕ) (prev : BPlusTree α β) (s : α) (c : BPlusTree α β) :
    BPlusTree α β × List (Branch α β) :=
  Id.run (rebalanceLastM t (pure ()) prev s c)

/-- Pure repair against the right sibling merges only an underflowing child. -/
private theorem rebalanceRight_eq_ite (c : BPlusTree α β) (s : α) (r : BPlusTree α β)
    (rest : List (Branch α β)) :
    rebalanceRight t c s r rest =
      if underflows t c then (mergeSplit t c s r).withRest rest else (c, (s, r) :: rest) := by
  unfold rebalanceRight rebalanceRightM
  -- In `Id`, bind is application and `pure` is the identity, so each branch is the pure branch
  -- by definition.
  split <;> rfl

/-- Pure repair against the left sibling merges only an underflowing last child. -/
private theorem rebalanceLast_eq_ite (prev : BPlusTree α β) (s : α) (c : BPlusTree α β) :
    rebalanceLast t prev s c =
      if underflows t c then (mergeSplit t prev s c).withRest [] else (prev, [(s, c)]) := by
  unfold rebalanceLast rebalanceLastM
  -- as in `rebalanceRight_eq_ite`
  split <;> rfl

/-- Merging keeps the entries of both siblings; the separator is not an entry. -/
@[simp] theorem toList_mergeSplit (l : BPlusTree α β) (s : α) (r : BPlusTree α β) :
    (mergeSplit t l s r).toList = l.toList ++ r.toList := by
  cases l <;> cases r <;> simp [mergeSplit, List.flatMap_append]

/-- Repair against the right sibling keeps the entries. -/
private theorem toList_rebalanceRight (c : BPlusTree α β) (s : α) (r : BPlusTree α β)
    (rest : List (Branch α β)) :
    (rebalanceRight t c s r rest).1.toList ++
        ((rebalanceRight t c s r rest).2.flatMap fun e => e.child.toList) =
      c.toList ++ (r.toList ++ rest.flatMap fun e => e.child.toList) := by
  rw [rebalanceRight_eq_ite]
  split <;> simp [InsertResult.toList_withRest, List.append_assoc]

/-- Repair against the left sibling keeps the entries. -/
private theorem toList_rebalanceLast (prev : BPlusTree α β) (s : α) (c : BPlusTree α β) :
    (rebalanceLast t prev s c).1.toList ++
        ((rebalanceLast t prev s c).2.flatMap fun e => e.child.toList) =
      prev.toList ++ c.toList := by
  rw [rebalanceLast_eq_ite]
  split <;> simp [InsertResult.toList_withRest]

/-- Collapsing an empty root keeps the entries. -/
@[simp] theorem toList_collapse (tr : BPlusTree α β) : (collapse tr).toList = tr.toList := by
  unfold collapse
  split <;> simp

/-! ### Shape -/

/-- A subtree of height `h` that may be one item short: balanced, with occupied children, and
with `t - 2` to `2 * t - 1` entries or separators at its root. -/
private structure Underfull (t h : ℕ) (c : BPlusTree α β) : Prop where
  balanced : Balanced c
  height_eq : c.height = h
  children_occupied : ∀ x ∈ c.children, Occupied t x
  width_le : c.width ≤ 2 * t - 1
  le_width : t - 2 ≤ c.width

/-- The shape of the result `c` of erasing from `tr`: balanced, of the same height, with
occupied children, and at most one item fewer at its root. -/
private structure EraseFits (t : ℕ) (tr c : BPlusTree α β) : Prop where
  balanced : Balanced c
  height_eq : c.height = tr.height
  children_occupied : ∀ x ∈ c.children, Occupied t x
  width_le : c.width ≤ tr.width
  width_le_succ : tr.width ≤ c.width + 1

/-- A repaired child, or a repaired pair of children around a separator, all good. -/
private def Mended (t h : ℕ) : InsertResult α β → Prop
  | .tree c => Good t h c
  | .split l _ r => Good t h l ∧ Good t h r

/-- A good subtree is at most one item short. -/
private theorem Good.underfull {c : BPlusTree α β} {h : ℕ} (hc : Good t h c) :
    Underfull t h c :=
  ⟨hc.balanced, hc.height_eq, fun _ hx => hc.occupied.of_mem_children hx, hc.occupied.width_le,
    by have := hc.occupied.le_width; omega⟩

/-- A subtree that does not underflow is good. -/
private theorem Underfull.good {c : BPlusTree α β} {h : ℕ} (hc : Underfull t h c)
    (hu : underflows t c = false) : Good t h c := by
  have hw : t - 1 ≤ c.width := by simpa [underflows] using hu
  refine ⟨hc.balanced, hc.height_eq, ?_⟩
  cases c with
  | leaf es => exact .leaf hw hc.width_le
  | node f r =>
    exact .node hw hc.width_le (hc.children_occupied f List.mem_cons_self)
      fun e he => hc.children_occupied _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))

/-- A subtree one item short that underflows has exactly `t - 2` items at its root. -/
private theorem Underfull.width_eq_of_underflows {c : BPlusTree α β} {h : ℕ}
    (hc : Underfull t h c) (hu : underflows t c = true) : c.width = t - 2 := by
  have := hc.le_width
  have : c.width < t - 1 := by simpa [underflows] using hu
  omega

/-- The children of a subtree one item short are good, one level lower. -/
private theorem Underfull.good_of_mem_children {c x : BPlusTree α β} {h : ℕ}
    (hc : Underfull t (h + 1) c) (hx : x ∈ c.children) : Good t h x :=
  ⟨hc.balanced.of_mem_children hx,
    by have := hc.balanced.height_of_mem_children hx; rw [hc.height_eq] at this; omega,
    hc.children_occupied x hx⟩

/-- Erasure from an occupied subtree leaves it at most one item short. -/
private theorem EraseFits.underfull {tr c : BPlusTree α β} (hf : EraseFits t tr c)
    (ho : Occupied t tr) : Underfull t tr.height c :=
  ⟨hf.balanced, hf.height_eq, hf.children_occupied, hf.width_le.trans ho.width_le,
    by have := ho.le_width; have := hf.width_le_succ; omega⟩

/-- A leaf of `t - 1` to `2 * t - 1 + t` entries, split when it overflows, is good. -/
private theorem mended_ofLeaf {entries : List (α × β)} (hlo : t - 1 ≤ entries.length)
    (hhi : entries.length ≤ 2 * t - 1 + t) : Mended t 1 (InsertResult.ofLeaf t entries) := by
  by_cases hle : entries.length ≤ 2 * t - 1
  · simp only [InsertResult.ofLeaf, hle, ↓reduceIte]
    exact ⟨.leaf, rfl, .leaf hlo hle⟩
  · obtain ⟨l, s, r, heq, hl, hr⟩ :=
      InsertResult.exists_good_split_ofLeaf (t := t) (entries := entries) (by omega) hhi
    exact heq ▸ ⟨hl, hr⟩

/-- A node of `t - 1` to `2 * t - 1 + t + 1` separators over good children, split when it
overflows, is good. -/
private theorem mended_ofNode {first : BPlusTree α β} {rest : List (Branch α β)} {h : ℕ}
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child) (hlo : t - 1 ≤ rest.length)
    (hhi : rest.length ≤ 2 * t - 1 + t + 1) :
    Mended t (h + 1) (InsertResult.ofNode t first rest) := by
  by_cases hle : rest.length ≤ 2 * t - 1
  · simp only [InsertResult.ofNode, hle, ↓reduceIte]
    exact good_node hf hr hlo hle
  · obtain ⟨l, s, r, heq, hl, hr'⟩ :=
      InsertResult.exists_good_split_ofNode hf hr (by omega) (by omega)
    exact heq ▸ ⟨hl, hr'⟩

/-- Placing a repaired result among good branches keeps them good, adding at most one. -/
private theorem mended_withRest {x : InsertResult α β} {h : ℕ} (hx : Mended t h x)
    {rest : List (Branch α β)} (hr : ∀ e ∈ rest, Good t h e.child) :
    Good t h (x.withRest rest).1 ∧ (∀ e ∈ (x.withRest rest).2, Good t h e.child) ∧
      rest.length ≤ (x.withRest rest).2.length ∧
      (x.withRest rest).2.length ≤ rest.length + 1 := by
  cases x with
  | tree c => exact ⟨hx, hr, le_rfl, Nat.le_succ _⟩
  | split l s r => exact ⟨hx.1, List.forall_mem_cons.2 ⟨hx.2, hr⟩, Nat.le_succ _, le_rfl⟩

/-- Merging two adjacent subtrees of one height, with `t - 1` to `3 * t - 1` root items between
them, gives good results. -/
private theorem mended_mergeSplit {l r : BPlusTree α β} {h : ℕ} (hl : Underfull t h l)
    (hr : Underfull t h r) (s : α) (hlo : t - 1 ≤ l.width + r.width)
    (hhi : l.width + r.width ≤ 3 * t - 1) : Mended t h (mergeSplit t l s r) := by
  cases l with
  | leaf le =>
    cases r with
    | leaf re =>
      obtain rfl : 1 = h := hl.height_eq
      simp only [width_leaf] at hlo hhi
      exact mended_ofLeaf (by simp; omega) (by simp; omega)
    | node rf rr =>
      exact False.elim <| rf.height_pos.ne' <| Nat.succ.inj <|
        hr.balanced.height_node.symm.trans (hr.height_eq.trans hl.height_eq.symm)
  | node lf lr =>
    cases r with
    | leaf re =>
      exact False.elim <| lf.height_pos.ne' <| Nat.succ.inj <|
        hl.balanced.height_node.symm.trans (hl.height_eq.trans hr.height_eq.symm)
    | node rf rr =>
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 :=
        ⟨lf.height, by rw [← hl.height_eq, hl.balanced.height_node]⟩
      simp only [width_node] at hlo hhi
      exact mended_ofNode (hl.good_of_mem_children List.mem_cons_self)
        (List.forall_mem_append.2 ⟨fun _ he => hl.good_of_mem_children (List.mem_cons_of_mem _
          (List.mem_map_of_mem he)), List.forall_mem_cons.2 ⟨hr.good_of_mem_children
          List.mem_cons_self, fun _ he => hr.good_of_mem_children (List.mem_cons_of_mem _
          (List.mem_map_of_mem he))⟩⟩) (by simp; omega) (by simp; omega)

/-- Repair against the right sibling: the results are good, with one branch fewer or none. -/
private theorem good_rebalanceRight {c r : BPlusTree α β} {h : ℕ}
    (hc : Underfull t h c) (hr : Good t h r) (s : α) {rest : List (Branch α β)}
    (hrest : ∀ e ∈ rest, Good t h e.child) :
    Good t h (rebalanceRight t c s r rest).1 ∧
      (∀ e ∈ (rebalanceRight t c s r rest).2, Good t h e.child) ∧
      rest.length ≤ (rebalanceRight t c s r rest).2.length ∧
      (rebalanceRight t c s r rest).2.length ≤ rest.length + 1 := by
  rw [rebalanceRight_eq_ite]
  split
  · next hu =>
    have := hc.width_eq_of_underflows hu
    have := hr.occupied.le_width
    have := hr.occupied.width_le
    exact mended_withRest (mended_mergeSplit hc hr.underfull s (by omega) (by omega)) hrest
  · next hu =>
    exact ⟨hc.good (by simpa using hu), List.forall_mem_cons.2 ⟨hr, hrest⟩, Nat.le_succ _,
      le_rfl⟩

/-- Repair of a last child against its left sibling: the results are good, with at most one
branch. -/
private theorem good_rebalanceLast {prev c : BPlusTree α β} {h : ℕ}
    (hp : Good t h prev) (hc : Underfull t h c) (s : α) :
    Good t h (rebalanceLast t prev s c).1 ∧
      (∀ e ∈ (rebalanceLast t prev s c).2, Good t h e.child) ∧
      (rebalanceLast t prev s c).2.length ≤ 1 := by
  rw [rebalanceLast_eq_ite]
  split
  · next hu =>
    have := hc.width_eq_of_underflows hu
    have := hp.occupied.le_width
    have := hp.occupied.width_le
    obtain ⟨h₁, h₂, -, h₃⟩ := mended_withRest (rest := [])
      (mended_mergeSplit hp.underfull hc s (by omega) (by omega)) (by simp)
    exact ⟨h₁, h₂, by simpa using h₃⟩
  · next hu =>
    exact ⟨hp, List.forall_mem_cons.2 ⟨hc.good (by simpa using hu), by simp⟩, by simp⟩

end PureStructure

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α}

/-- Pure erasure from a subtree. -/
private def eraseSubtree (t : ℕ) (k : α) (tr : BPlusTree α β) : BPlusTree α β :=
  Id.run (eraseSubtreeM t leI (pure ()) k tr)

/-- Pure erasure among the branches after the child `prev`, whose erasure is `prevErased`. -/
private def eraseRest (t : ℕ) (k : α) (prev prevErased : BPlusTree α β)
    (rest : List (Branch α β)) : BPlusTree α β × List (Branch α β) :=
  Id.run (eraseRestM t leI (pure ()) k prev (fun _ => pure prevErased) rest)

/-- Pure erasure. -/
@[expose] def erase (t : ℕ) (k : α) (tr : BPlusTree α β) : BPlusTree α β :=
  Id.run (eraseM t leI (pure ()) k tr)

/-- `erase` is the `Id` instantiation of `eraseM`. -/
theorem erase_def (tr : BPlusTree α β) : erase t k tr = Id.run (eraseM t leI (pure ()) k tr) :=
  (rfl)

/-- Erasure from a leaf removes the entry by the scan of its entries. -/
private theorem eraseSubtree_leaf (entries : List (α × β)) :
    eraseSubtree t k (.leaf entries) = .leaf (Id.run (SortedAssoc.eraseM leI k entries)) := rfl

/-- Erasure from a leaf with sorted entries is the model erasure of its entries. -/
private theorem eraseSubtree_leaf_of_isSortedAssoc {entries : List (α × β)}
    (h : entries.IsSortedAssoc) :
    eraseSubtree t k (.leaf entries) = .leaf (SortedAssoc.erase k entries) := by
  rw [eraseSubtree_leaf, SortedAssoc.idRun_eraseM h]

/-- Erasure from a node is erasure among its branches. -/
private theorem eraseSubtree_node (first : BPlusTree α β) (rest : List (Branch α β)) :
    eraseSubtree t k (.node first rest) =
      .node (eraseRest t k first (eraseSubtree t k first) rest).1
        (eraseRest t k first (eraseSubtree t k first) rest).2 := rfl

/-- Past the last branch, the erasure of the preceding child. -/
@[simp] private theorem eraseRest_nil (prev pe : BPlusTree α β) :
    eraseRest t k prev pe [] = (pe, []) := rfl

/-- Pure erasure at a branch: when its separator is above the key, the erasure of the preceding
child is repaired against this child; otherwise the search moves on, and the last child is erased
from and repaired against its left sibling. -/
private theorem eraseRest_cons (prev pe : BPlusTree α β) (s : α) (c : BPlusTree α β)
    (rest : List (Branch α β)) :
    eraseRest t k prev pe ((s, c) :: rest) =
      if s ≤ k then
        match rest with
        | [] => rebalanceLast t prev s (eraseSubtree t k c)
        | _ :: _ =>
          let p := eraseRest t k c (eraseSubtree t k c) rest
          (prev, (s, p.1) :: p.2)
      else rebalanceRight t pe s c rest := by
  by_cases h : s ≤ k
  · simp only [eraseRest, eraseRestM, leI, h, decide_true, ↓reduceIte, rebalanceLast,
      eraseSubtree]
    -- In `Id`, bind is application and `pure` is the identity, so each branch of the monadic
    -- `match` is the corresponding pure branch by definition.
    cases rest <;> rfl
  · simp only [eraseRest, eraseRestM, leI, h, decide_false, ↓reduceIte, rebalanceRight]
    rfl

/-- Erasure is erasure from the root subtree, then collapsing an empty root. -/
private theorem erase_eq_collapse (tr : BPlusTree α β) :
    erase t k tr = collapse (eraseSubtree t k tr) := rfl

/-! ### The model equation -/

/-- The search among the branches after `prev`, against the model. Each separator is at most the
keys of its child and above the keys of `prev`, no child is empty, and the keys of each child are
below the later separators. Given that `pe` has the entries of the erasure of `prev`, the result
has the entries of the model erasure. -/
private theorem eraseRest_spec {rest : List (Branch α β)}
    (hle : ∀ e ∈ rest, ∀ p ∈ e.child.toList, e.1 ≤ p.1)
    (hne : ∀ e ∈ rest, e.child.toList ≠ [])
    (hpw : rest.Pairwise fun a b => ∀ p ∈ a.child.toList, p.1 < b.1)
    (hc : ∀ e ∈ rest, (eraseSubtree t k e.child).toList = SortedAssoc.erase k e.child.toList)
    (prev pe : BPlusTree α β) (hprev : ∀ e ∈ rest, ∀ p ∈ prev.toList, p.1 < e.1)
    (hpe : pe.toList = SortedAssoc.erase k prev.toList) :
    (eraseRest t k prev pe rest).1.toList ++
        ((eraseRest t k prev pe rest).2.flatMap fun e => e.child.toList) =
      SortedAssoc.erase k (prev.toList ++ rest.flatMap fun e => e.child.toList) := by
  induction rest generalizing prev pe with
  | nil => simp [hpe]
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨hpw₁, hpw₂⟩ := List.pairwise_cons.1 hpw
    have hcs : ∀ p ∈ c.toList, s ≤ p.1 := hle (s, c) List.mem_cons_self
    have hcc := hc (s, c) List.mem_cons_self
    rw [eraseRest_cons]
    split_ifs with hk
    · -- the separator is passed: the key is not in `prev`
      have hpre : SortedAssoc.erase k prev.toList = prev.toList :=
        SortedAssoc.erase_of_forall_ne fun p hp =>
          (lt_of_lt_of_le (hprev (s, c) List.mem_cons_self p hp) hk).ne
      rcases rest with _ | ⟨e, rest⟩
      · simp [toList_rebalanceLast, hpre, hcc]
      · have ih := ih (fun e he => hle e (List.mem_cons_of_mem _ he))
          (fun e he => hne e (List.mem_cons_of_mem _ he)) hpw₂
          (fun e he => hc e (List.mem_cons_of_mem _ he)) c (eraseSubtree t k c) hpw₁ hcc
        simp only [List.flatMap_cons, Branch.child_mk, SortedAssoc.erase_append, hpre] at ih ⊢
        rw [ih]
    · -- the separator is above the key: the key is in `prev` or absent
      have hk' : k < s := lt_of_not_ge hk
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (hne (s, c) List.mem_cons_self)
      have htail : SortedAssoc.erase k (c.toList ++ rest.flatMap fun e => e.child.toList) =
          c.toList ++ rest.flatMap fun e => e.child.toList := by
        refine SortedAssoc.erase_of_forall_ne fun p hp => ?_
        rcases List.mem_append.1 hp with hp | hp
        · exact (lt_of_lt_of_le hk' (hcs p hp)).ne'
        · obtain ⟨e, he, hp⟩ := List.mem_flatMap.1 hp
          exact ((lt_of_lt_of_le hk' (hcs q hq)).trans (lt_of_lt_of_le (hpw₁ e he q hq)
            (hle e (List.mem_cons_of_mem _ he) p hp))).ne'
      rw [toList_rebalanceRight, hpe, List.flatMap_cons, Branch.child_mk,
        SortedAssoc.erase_append, htail]

/-- Model equation of erasure from a subtree under the search invariant. -/
private theorem toList_eraseSubtree_of (k : α) (tr : BPlusTree α β)
    (h : SearchInvariant t tr) :
    (eraseSubtree t k tr).toList = SortedAssoc.erase k tr.toList := by
  induction tr with
  | leaf entries =>
    rw [eraseSubtree_leaf_of_isSortedAssoc (by simpa only [toList_leaf] using h.sorted),
      toList_leaf, toList_leaf]
  | node first rest ihf ihr =>
    have hp := h.separated
    have hmem : ∀ e ∈ rest, e.child ∈ (BPlusTree.node first rest).children :=
      fun e he => List.mem_cons_of_mem _ (List.mem_map_of_mem he)
    rw [eraseSubtree_node, toList_node, toList_node]
    exact eraseRest_spec (fun e he p hp' => hp.le_of_mem he hp')
      (fun e he => List.ne_nil_of_length_pos ((h.occupied _ (hmem e he)).size_pos h.two_le))
      hp.pairwise (fun e he => ihr e he (h.child (hmem e he)))
      first _ (fun e he p hp' => hp.lt_of_mem_first he hp')
      (ihf (h.child List.mem_cons_self))

/-! ### The shape of the result -/

/-- Shape of the erasure among the branches after a good child `prev`, whose erasure `pe` is at
most one item short: the results are good, with at most one branch fewer. -/
private theorem good_eraseRest {h : ℕ} {rest : List (Branch α β)}
    (hc : ∀ e ∈ rest, Good t h e.child ∧ Underfull t h (eraseSubtree t k e.child))
    {prev pe : BPlusTree α β} (hp : Good t h prev) (hpe : Underfull t h pe) (hne : rest ≠ []) :
    Good t h (eraseRest t k prev pe rest).1 ∧
      (∀ e ∈ (eraseRest t k prev pe rest).2, Good t h e.child) ∧
      (eraseRest t k prev pe rest).2.length ≤ rest.length ∧
      rest.length ≤ (eraseRest t k prev pe rest).2.length + 1 := by
  induction rest generalizing prev pe with
  | nil => exact absurd rfl hne
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    have hcg : Good t h c ∧ Underfull t h (eraseSubtree t k c) := hc _ List.mem_cons_self
    rw [eraseRest_cons]
    split_ifs with hk
    · rcases rest with _ | ⟨e, rest⟩
      · obtain ⟨r₁, r₂, r₃⟩ := good_rebalanceLast hp hcg.2 s
        exact ⟨r₁, r₂, by simpa using r₃, by simp⟩
      · obtain ⟨r₁, r₂, r₃, r₄⟩ := ih (fun e he => hc e (List.mem_cons_of_mem _ he))
          hcg.1 hcg.2 (List.cons_ne_nil _ _)
        exact ⟨hp, List.forall_mem_cons.2 ⟨r₁, r₂⟩, by simpa using r₃, by simpa using r₄⟩
    · obtain ⟨r₁, r₂, r₃, r₄⟩ := good_rebalanceRight hpe hcg.1 s fun e he =>
        (hc e (List.mem_cons_of_mem _ he)).1
      exact ⟨r₁, r₂, by simpa using r₄, by simpa using r₃⟩

/-- Shape invariant of erasure from a subtree. -/
private theorem eraseFits_eraseSubtree (ht : 2 ≤ t) (k : α) (tr : BPlusTree α β)
    (hb : Balanced tr) (ho : ∀ c ∈ tr.children, Occupied t c)
    (hpos : (∀ entries, tr ≠ .leaf entries) → 1 ≤ tr.width) (hs : tr.toList.IsSortedAssoc) :
    EraseFits t tr (eraseSubtree t k tr) := by
  induction tr with
  | leaf entries =>
    rw [toList_leaf] at hs
    have hlen := SortedAssoc.length_erase (k := k) hs
    rw [eraseSubtree_leaf_of_isSortedAssoc hs]
    exact ⟨.leaf, rfl, by simp, by simp only [width_leaf]; split at hlen <;> omega,
      by simp only [width_leaf]; split at hlen <;> omega⟩
  | node first rest ihf ihr =>
    obtain ⟨hf, hr⟩ := good_of_balanced_node hb ho
    have hh := hb.height_node
    have hne : rest ≠ [] := fun h => by simpa [h, width_node] using hpos (by simp)
    -- erasure from a good child leaves it at most one item short
    have hchild : ∀ c ∈ (BPlusTree.node first rest).children, Good t first.height c →
        (Balanced c → (∀ c' ∈ c.children, Occupied t c') →
          ((∀ entries, c ≠ .leaf entries) → 1 ≤ c.width) → c.toList.IsSortedAssoc →
            EraseFits t c (eraseSubtree t k c)) →
        Underfull t first.height (eraseSubtree t k c) := by
      intro c hc hg ih
      exact hg.height_eq ▸ (ih hg.balanced (fun _ hc' => hg.occupied.of_mem_children hc')
        (fun _ => by have := hg.occupied.le_width; omega)
        (hs.sublist (toList_sublist_of_mem_children hc))).underfull hg.occupied
    have hpe := hchild first List.mem_cons_self hf ihf
    have hc : ∀ e ∈ rest, Good t first.height e.child ∧
        Underfull t first.height (eraseSubtree t k e.child) := fun e he =>
      ⟨hr e he, hchild _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he)) (hr e he) (ihr e he)⟩
    obtain ⟨r₁, r₂, r₃, r₄⟩ := good_eraseRest hc hf hpe hne
    rw [eraseSubtree_node]
    have hb' : Balanced (.node (eraseRest t k first (eraseSubtree t k first) rest).1
        (eraseRest t k first (eraseSubtree t k first) rest).2) :=
      .node r₁.balanced (fun e he => (r₂ e he).balanced)
        fun e he => (r₂ e he).height_eq.trans r₁.height_eq.symm
    refine ⟨hb', by rw [hb'.height_node, r₁.height_eq, hh], fun x hx => ?_, r₃, r₄⟩
    simp only [children_node, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨e, he, rfl⟩
    exacts [r₁.occupied, (r₂ e he).occupied]

/-! ### The separator convention of the result -/

/-- Joining two runs of linked children around a separator above the keys of the first run and
at most the keys of the child it introduces. -/
private theorem Linked.append {a c : BPlusTree α β} {l₁ l₂ : List (Branch α β)} {s : α}
    (h₁ : Linked a l₁) (h₂ : Linked c l₂)
    (hlt : ∀ p ∈ (BPlusTree.node a l₁).toList, p.1 < s) (hle : ∀ p ∈ c.toList, s ≤ p.1) :
    Linked a (l₁ ++ (s, c) :: l₂) := by
  induction l₁ generalizing a with
  | nil => exact ⟨fun p hp => hlt p (by simpa using hp), hle, h₂⟩
  | cons e l₁ ih =>
    obtain ⟨s', c'⟩ := e
    obtain ⟨g₁, g₂, g₃⟩ := h₁
    refine ⟨g₁, g₂, ih g₃ fun p hp => hlt p ?_⟩
    simpa only [toList_node, List.flatMap_cons] using List.mem_append_right a.toList hp

/-- Merging two separated siblings, with the keys of the left one below their separator and
those of the right one at least it, gives a result with the separator convention, when the
entries of the two are sorted and no child of either is empty. -/
private theorem sep_mergeSplit {l r : BPlusTree α β} {s : α} (hl : Separated l)
    (hr : Separated r) (hls : ∀ p ∈ l.toList, p.1 < s) (hrs : ∀ p ∈ r.toList, s ≤ p.1)
    (hs : (l.toList ++ r.toList).IsSortedAssoc) (hln : ∀ c ∈ l.children, c.toList ≠ [])
    (hrn : ∀ c ∈ r.children, c.toList ≠ []) : Sep (mergeSplit t l s r) := by
  cases l with
  | leaf le =>
    cases r with
    | leaf re => exact sep_ofLeaf (by rwa [toList_leaf, toList_leaf] at hs)
    | node rf rr => exact ⟨hl, hr, hls, hrs⟩
  | node lf lr =>
    cases r with
    | leaf re => exact ⟨hl, hr, hls, hrs⟩
    | node rf rr =>
      have hne : ∀ e : Branch α β, e ∈ lr ++ (s, rf) :: rr → e.child.toList ≠ [] :=
        List.forall_mem_append.2 ⟨fun _ he => hln _ (List.mem_cons_of_mem _ (List.mem_map_of_mem
          he)), List.forall_mem_cons.2 ⟨hrn _ List.mem_cons_self, fun _ he => hrn _
          (List.mem_cons_of_mem _ (List.mem_map_of_mem he))⟩⟩
      exact sep_ofNode (separated_node_of_linked
        (hl.linked.append hr.linked hls fun p hp =>
          hrs p (by rw [toList_node]; exact List.mem_append_left _ hp))
        hl.first (List.forall_mem_append.2 ⟨fun _ => hl.of_mem_rest,
          List.forall_mem_cons.2 ⟨hr.first, fun _ => hr.of_mem_rest⟩⟩) hne) hne

/-- The erasure among the branches after a good child `prev` keeps the separator convention
between neighbours and keeps every child separated; the entries of the tree in the place of
`prev` come from `prev` or from the branches. -/
private theorem linked_eraseRest (ht : 2 ≤ t) {h : ℕ} {rest : List (Branch α β)}
    (hc : ∀ e ∈ rest, Good t h e.child ∧ Underfull t h (eraseSubtree t k e.child) ∧
      Separated e.child ∧ Separated (eraseSubtree t k e.child) ∧
      (eraseSubtree t k e.child).toList.Sublist e.child.toList)
    {prev pe : BPlusTree α β} (hp : Good t h prev) (hpe : Underfull t h pe)
    (hps : Separated prev) (hpes : Separated pe) (hsub : pe.toList.Sublist prev.toList)
    (hl : Linked prev rest)
    (hs : (prev.toList ++ rest.flatMap fun e => e.child.toList).IsSortedAssoc) :
    Linked (eraseRest t k prev pe rest).1 (eraseRest t k prev pe rest).2 ∧
      Separated (eraseRest t k prev pe rest).1 ∧
      (∀ e ∈ (eraseRest t k prev pe rest).2, Separated e.child) ∧
      ∀ x ∈ (eraseRest t k prev pe rest).1.toList,
        x ∈ prev.toList ∨ x ∈ rest.flatMap fun e => e.child.toList := by
  have hne : ∀ {c : BPlusTree α β}, Good t h c → ∀ x ∈ c.children, x.toList ≠ [] :=
    fun hg x hx => List.ne_nil_of_length_pos ((hg.occupied.of_mem_children hx).size_pos ht)
  have hne' : ∀ {c : BPlusTree α β}, Underfull t h c → ∀ x ∈ c.children, x.toList ≠ [] :=
    fun hu x hx => List.ne_nil_of_length_pos ((hu.children_occupied x hx).size_pos ht)
  induction rest generalizing prev pe with
  | nil => exact ⟨trivial, hpes, by simp, fun x hx => Or.inl (hsub.subset hx)⟩
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨h₁, h₂, h₃⟩ := hl
    obtain ⟨gc, uce, sc, sce, subc⟩ := hc (s, c) List.mem_cons_self
    have hrs : ∀ e ∈ rest, Separated e.child := fun e he =>
      (hc e (List.mem_cons_of_mem _ he)).2.2.1
    simp only [List.flatMap_cons, Branch.child_mk] at hs ⊢
    have hs' := List.isSortedAssoc_append_iff.1 hs
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _
      (List.ne_nil_of_length_pos (gc.occupied.size_pos ht))
    rw [eraseRest_cons]
    split_ifs with hk
    · rcases rest with _ | ⟨e, rest⟩
      · -- the last child is erased from and repaired against `prev`
        dsimp only
        rw [rebalanceLast_eq_ite]
        split
        · have hsep : Sep (mergeSplit t prev s (eraseSubtree t k c)) :=
            sep_mergeSplit hps sce h₁ (fun p hp' => h₂ p (subc.subset hp'))
              (hs.sublist ((List.Sublist.refl _).append
                (subc.trans (List.sublist_append_left _ _))))
              (hne hp) (hne' uce)
          obtain ⟨l₁, l₂, l₃⟩ := linked_withRest_of_sep (c := eraseSubtree t k c) (rest := [])
            hsep trivial (by simp) (by simp)
          refine ⟨l₁, l₂, l₃, fun x hx =>
            (List.mem_append.1 (toList_mergeSplit _ _ _ ▸ mem_toList_of_mem_withRest_fst hx)).imp
              id fun hx => List.mem_append_left _ (subc.subset hx)⟩
        · exact ⟨⟨h₁, fun p hp' => h₂ p (subc.subset hp'), trivial⟩, hps, by simpa using sce,
            fun x hx => Or.inl hx⟩
      · -- the search moves on
        obtain ⟨l₁, l₂, l₃, l₄⟩ := ih (fun e he => hc e (List.mem_cons_of_mem _ he)) gc uce sc
          sce subc h₃ hs'.2.1
        refine ⟨⟨h₁, fun x hx => ?_, l₁⟩, hps, List.forall_mem_cons.2 ⟨l₂, l₃⟩,
          fun x hx => Or.inl hx⟩
        rcases l₄ x hx with hx | hx
        · exact h₂ x hx
        · exact (h₂ q hq).trans ((List.isSortedAssoc_append_iff.1 hs'.2.1).2.2 q hq x hx).le
    · -- `prev` is erased from and repaired against this child
      rw [rebalanceRight_eq_ite]
      split
      · have hsep : Sep (mergeSplit t pe s c) :=
          sep_mergeSplit hpes sc (fun p hp' => h₁ p (hsub.subset hp')) h₂
            (hs.sublist (hsub.append (List.sublist_append_left _ _))) (hne' hpe) (hne gc)
        have hb : ∀ s₂ c₂ rest', rest = (s₂, c₂) :: rest' →
            ∀ p ∈ (mergeSplit t pe s c).toList, p.1 < s₂ := by
          rintro s₂ c₂ rest' rfl p hp'
          rw [toList_mergeSplit] at hp'
          rcases List.mem_append.1 hp' with hp' | hp'
          · exact (lt_of_lt_of_le (h₁ p (hsub.subset hp')) (h₂ q hq)).trans (h₃.1 q hq)
          · exact h₃.1 p hp'
        obtain ⟨l₁, l₂, l₃⟩ := linked_withRest_of_sep hsep h₃ hrs hb
        refine ⟨l₁, l₂, l₃, fun x hx =>
          (List.mem_append.1 (toList_mergeSplit _ _ _ ▸ mem_toList_of_mem_withRest_fst hx)).imp
            (hsub.subset ·) (List.mem_append_left _ ·)⟩
      · exact ⟨⟨fun p hp' => h₁ p (hsub.subset hp'), h₂, h₃⟩, hpes,
          List.forall_mem_cons.2 ⟨sc, hrs⟩, fun x hx => Or.inl (hsub.subset hx)⟩

/-- Erasure from a subtree keeps the separator convention. -/
private theorem separated_eraseSubtree (k : α) (tr : BPlusTree α β)
    (h : SearchInvariant t tr) (hb : Balanced tr)
    (hpos : (∀ entries, tr ≠ .leaf entries) → 1 ≤ tr.width) :
    Separated (eraseSubtree t k tr) := by
  induction tr with
  | leaf entries => exact .leaf
  | node first rest ihf ihr =>
    obtain ⟨hgf, hgr⟩ := good_of_balanced_node hb h.occupied
    have hp := h.separated
    have ht := h.two_le
    have hne : rest ≠ [] := fun h => by simpa [h, width_node] using hpos fun _ => nofun
    -- what the three inductions give for a child of the node
    have hchild : ∀ c ∈ (BPlusTree.node first rest).children, Good t first.height c →
        (SearchInvariant t c → Balanced c →
          ((∀ entries, c ≠ .leaf entries) → 1 ≤ c.width) → Separated (eraseSubtree t k c)) →
        Underfull t first.height (eraseSubtree t k c) ∧ Separated (eraseSubtree t k c) ∧
          (eraseSubtree t k c).toList.Sublist c.toList := by
      intro c hc hg ih
      have hsc := h.child hc
      have hcp : (∀ entries, c ≠ .leaf entries) → 1 ≤ c.width :=
        fun _ => (by omega : 1 ≤ t - 1).trans hg.occupied.le_width
      exact ⟨hg.height_eq ▸ (eraseFits_eraseSubtree ht k c hg.balanced hsc.occupied hcp
        hsc.sorted).underfull hg.occupied, ih hsc hg.balanced hcp,
        toList_eraseSubtree_of k c hsc ▸ List.filter_sublist⟩
    obtain ⟨uf, sf, subf⟩ := hchild first List.mem_cons_self hgf ihf
    have hrest := fun e (he : e ∈ rest) =>
      hchild e.child (List.mem_cons_of_mem _ (List.mem_map_of_mem he)) (hgr e he) (ihr e he)
    obtain ⟨l₁, l₂, l₃, -⟩ := linked_eraseRest ht
      (fun e he => ⟨hgr e he, (hrest e he).1, hp.of_mem_rest he, (hrest e he).2.1,
        (hrest e he).2.2⟩)
      hgf uf hp.first sf subf hp.linked (by simpa only [toList_node] using h.sorted)
    obtain ⟨-, g₂, -, -⟩ := good_eraseRest (fun e he => ⟨hgr e he, (hrest e he).1⟩) hgf uf hne
    rw [eraseSubtree_node]
    exact separated_node_of_linked l₁ l₂ l₃ fun e he =>
      List.ne_nil_of_length_pos ((g₂ e he).occupied.size_pos ht)

/-! ### Erasure on well-formed trees -/

variable {tr : BPlusTree α β}

/-- Model equation of erasure on well-formed trees. -/
theorem toList_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).toList = SortedAssoc.erase k tr.toList := by
  rw [erase_eq_collapse, toList_collapse,
    toList_eraseSubtree_of k tr h.searchInvariant]

/-- Erasure preserves well-formedness. -/
theorem IsWF.erase (h : IsWF t tr) (k : α) : IsWF t (erase t k tr) := by
  have ht := h.two_le
  obtain ⟨hb, -, hco, hk₁, -⟩ :=
    eraseFits_eraseSubtree ht k tr h.balanced h.occupied_of_mem_children h.width_pos h.sorted
  have hp := separated_eraseSubtree k tr h.searchInvariant h.balanced h.width_pos
  have hs : (BPlusTree.erase t k tr).toList.IsSortedAssoc :=
    toList_erase h k ▸ SortedAssoc.isSortedAssoc_erase h.sorted
  rw [erase_eq_collapse] at hs ⊢
  generalize eraseSubtree t k tr = c at *
  rcases c with es | ⟨f, _ | ⟨e, r⟩⟩ <;> simp only [collapse] at hs ⊢
  · exact ⟨ht, hk₁.trans h.width_le, fun hne => absurd rfl (hne es), by simp, .leaf, .leaf, hs⟩
  · exact (hco f List.mem_cons_self).isWF ht (hb.of_mem_children List.mem_cons_self) hp.first hs
  · exact ⟨ht, hk₁.trans h.width_le, fun _ => by simp, hco, hb, hp, hs⟩

/-- On a well-formed tree, erasure either keeps the height or lowers it by one. -/
theorem height_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).height = tr.height ∨ (erase t k tr).height + 1 = tr.height := by
  obtain ⟨hb, hh, -, -, -⟩ := eraseFits_eraseSubtree h.two_le k tr h.balanced
    h.occupied_of_mem_children h.width_pos h.sorted
  rw [erase_eq_collapse]
  generalize eraseSubtree t k tr = c at *
  rcases c with es | ⟨f, _ | ⟨e, r⟩⟩
  exacts [Or.inl hh, Or.inr (hb.height_node.symm.trans hh), Or.inl hh]

/-- Erasure removes one entry when the key is present and none otherwise. -/
theorem size_erase (h : IsWF t tr) (k : α) :
    (erase t k tr).size = if (lookup k tr).isSome then tr.size - 1 else tr.size := by
  rw [← length_toList (tr := erase t k tr), toList_erase h, SortedAssoc.length_erase h.sorted,
    lookup_eq h, length_toList]

/-- Erasing an absent key from a well-formed tree leaves the entries unchanged. -/
theorem toList_erase_of_lookup_eq_none (h : IsWF t tr) {k : α} (hk : lookup k tr = none) :
    (erase t k tr).toList = tr.toList := by
  rw [toList_erase h, SortedAssoc.erase_of_lookup_eq_none (by rwa [← lookup_eq h])]

end Pure

end BPlusTree

end Cslib.DataStructure

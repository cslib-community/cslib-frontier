/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.BinarySearch

/-!
# B-trees under a key function

Transporting a B-tree along a function on its keys, and the fact that the monadic lookup programs
commute with it: looking up `g k` in the tree with keys `g x` under a comparison `le` is the same
program as looking up `k` in the original tree under the comparison `fun a b => le (g a) (g b)`.
This lets a lookup be evaluated under an oracle that compares keys through a key function.

## Main definitions

* `BTree.mapKeys`, `BTree.mapKeysRest`: apply a function to every key, keeping values and shape.

## Main results

* `BTree.toList_mapKeys`: mapping keys maps the entries.
* `BTree.lookupM_mapKeys`, `BTree.lookupBinM_mapKeys`: lookup commutes with `mapKeys`.
-/

public section

universe w

namespace Cslib.DataStructure.BTree

variable {α α' β : Type}

mutual
/-- Map over keys, keeping values and shape. -/
@[expose] def mapKeys (g : α → α') : BTree α β → BTree α' β
  | .leaf => .leaf
  | .node first rest => .node (first.mapKeys g) (mapKeysRest g rest)
/-- Map over the keys of a list of triples. -/
@[expose] def mapKeysRest (g : α → α') : List (Triple α β) → List (Triple α' β)
  | [] => []
  | (k, v, c) :: rest => (g k, v, c.mapKeys g) :: mapKeysRest g rest
end

/-- Mapping keys over a node maps its first child and its triples. -/
@[simp] theorem mapKeys_node (g : α → α') (first : BTree α β) (rest : List (Triple α β)) :
    (node first rest).mapKeys g = node (first.mapKeys g) (mapKeysRest g rest) := rfl

/-- `mapKeysRest` is `List.map` over the triples. -/
theorem mapKeysRest_eq_map (g : α → α') (rest : List (Triple α β)) :
    mapKeysRest g rest = rest.map fun e => (g e.1, e.val, e.child.mapKeys g) := by
  induction rest with
  | nil => rfl
  | cons e rest ih => rcases e with ⟨_, _, _⟩; exact congrArg _ ih

/-- Mapping keys maps the entries, keeping values. -/
@[simp] theorem toList_mapKeys (g : α → α') (tr : BTree α β) :
    (tr.mapKeys g).toList = tr.toList.map fun x => (g x.1, x.2) := by
  induction tr with
  | leaf => rfl
  | node _ _ ih₁ ih₂ =>
    simp only [mapKeys_node, toList_node, toListRest_eq_flatMap, mapKeysRest_eq_map,
      List.map_append, ih₁, List.flatMap_map, List.map_flatMap, List.map_cons]
    exact congrArg _ (List.flatMap_congr fun e he => congrArg (_ :: ·) (ih₂ e he))

/-- The children of a tree with mapped keys are the mapped children. -/
private theorem children_mapKeys (g : α → α') (first : BTree α β) (rest : List (Triple α β)) :
    ((node first rest).mapKeys g).children = (node first rest).children.map (mapKeys g) := by
  simp only [mapKeys_node, children_node, mapKeysRest_eq_map, List.map_cons, List.map_map]
  rfl

/-- Induction on B-trees with one hypothesis for all children of a node. -/
private theorem induction_children {motive : BTree α β → Prop} (leaf : motive .leaf)
    (node : ∀ (first : BTree α β) (rest : List (Triple α β)),
      (∀ c ∈ (node first rest).children, motive c) → motive (.node first rest)) :
    ∀ tr, motive tr
  | .leaf => leaf
  | .node first rest => node first rest fun c _ => induction_children leaf node c
termination_by tr => sizeOf tr
decreasing_by exact sizeOf_lt_of_mem_children ‹_›

variable {m : Type → Type w} [Monad m]

/-- Lookup in a tree with mapped keys, compared through the key function, is lookup in the
original tree under the pulled-back comparison. -/
theorem lookupM_mapKeys (le : α' → α' → m Bool) (visit : m Unit) (g : α → α')
    (k : α) (tr : BTree α β) :
    lookupM le visit (g k) (tr.mapKeys g) = lookupM (fun a b => le (g a) (g b)) visit k tr := by
  fun_induction lookupM (fun a b => le (g a) (g b)) visit k tr with
  | case1 => simp only [mapKeys]; simp only [lookupM]
  | case2 first ih =>
    simp only [mapKeys, mapKeysRest]
    simp only [lookupM]
    exact bind_congr fun _ => by rw [ih]
  | case3 first k' v c rest ih2 ih1 =>
    simp only [mapKeys, mapKeysRest] at ih1 ⊢
    simp only [lookupM]
    refine bind_congr fun b => ?_
    cases b
    · simpa using ih1
    · refine bind_congr fun _ => bind_congr fun b => ?_
      cases b
      · simpa using ih2
      · rfl

private theorem mapKeysRest_take (g : α → α') (n : ℕ) (rest : List (Triple α β)) :
    mapKeysRest g (rest.take n) = (mapKeysRest g rest).take n := by
  simp only [mapKeysRest_eq_map, List.map_take]

private theorem mapKeysRest_drop (g : α → α') (n : ℕ) (rest : List (Triple α β)) :
    mapKeysRest g (rest.drop n) = (mapKeysRest g rest).drop n := by
  simp only [mapKeysRest_eq_map, List.map_drop]

/-- The within-node binary search commutes with mapping keys. -/
private theorem slotBinM_mapKeysRest (le : α' → α' → m Bool) (g : α → α') (k : α)
    (rest : List (Triple α β)) :
    slotBinM le (g k) (mapKeysRest g rest) =
      slotBinM (fun a b => le (g a) (g b)) k rest := by
  induction h : rest.length using Nat.strong_induction_on generalizing rest with
  | _ n ih =>
    rcases rest with _ | ⟨e, l⟩
    · simp only [mapKeysRest, slotBinM_nil]
    · have hm : mapKeysRest g (e :: l) =
          (g e.1, e.val, e.child.mapKeys g) :: mapKeysRest g l := by
        rcases e with ⟨_, _, _⟩; rfl
      have hl : (mapKeysRest g l).length = l.length := by
        rw [mapKeysRest_eq_map, List.length_map]
      rw [hm, slotBinM_cons, slotBinM_cons]
      simp only [hl, ← hm]
      have hlen : (l.length + 1) / 2 < (e :: l).length := by
        simp only [List.length_cons]; omega
      have hget : ((mapKeysRest g (e :: l))[(l.length + 1) / 2]'(by
          rw [mapKeysRest_eq_map, List.length_map]; exact hlen)).1 =
          g ((e :: l)[(l.length + 1) / 2]'hlen).1 := by
        simp only [mapKeysRest_eq_map, List.getElem_map]
      have hlt : (e :: l).length < n + 1 := by omega
      simp only [hget, ← mapKeysRest_take, ← mapKeysRest_drop]
      have h1 := ih _ (by simp only [List.length_take, List.length_cons] at hlt ⊢; omega)
        ((e :: l).take ((l.length + 1) / 2)) rfl
      have h3 := ih _ (by simp only [List.length_drop, List.length_cons] at hlt ⊢; omega)
        ((e :: l).drop ((l.length + 1) / 2 + 1)) rfl
      refine bind_congr fun b => ?_
      cases b
      · simp only [Bool.false_eq_true, ite_false, h3]
      · exact h1

/-- Lookup with binary in-node search in a tree with mapped keys, compared through the key
function, is lookup in the original tree under the pulled-back comparison. -/
theorem lookupBinM_mapKeys (le : α' → α' → m Bool) (visit : m Unit) (g : α → α')
    (k : α) (tr : BTree α β) :
    lookupBinM le visit (g k) (tr.mapKeys g) =
      lookupBinM (fun a b => le (g a) (g b)) visit k tr := by
  induction tr using induction_children with
  | leaf => simp only [mapKeys, lookupBinM_leaf]
  | node first rest ih =>
    rw [mapKeys_node, lookupBinM_node, lookupBinM_node, slotBinM_mapKeysRest]
    refine bind_congr fun _ => bind_congr fun i => ?_
    have hr : (mapKeysRest g rest)[i]? =
        rest[i]?.map fun e => (g e.1, e.val, e.child.mapKeys g) := by
      rw [mapKeysRest_eq_map, List.getElem?_map]
    have hc : ((node first rest).mapKeys g).children[i]? =
        (node first rest).children[i]?.map (mapKeys g) := by
      rw [children_mapKeys, List.getElem?_map]
    rw [mapKeys_node] at hc
    rw [hr, hc]
    rcases hri : rest[i]? with _ | e
    · rcases hci : (node first rest).children[i]? with _ | c
      · simp
      · simp only [Option.map_some, Option.map_none]
        exact bind_congr fun _ => by rw [ih c (List.mem_of_getElem? hci)]
    · simp only [Option.map_some]
      refine bind_congr fun b => ?_
      cases b
      · rcases hci : (node first rest).children[i]? with _ | c
        · simp
        · simpa [hci] using ih c (List.mem_of_getElem? hci)
      · rfl

end Cslib.DataStructure.BTree

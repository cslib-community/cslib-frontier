/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Comparisons.BinarySearch
public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle

/-!
# B-trees under a key function

The monadic lookup programs commute with mapping keys (`BTree.mapKeys`): looking up `g k` in the
tree with keys `g x` under a comparison `le` is the same program as looking up `k` in the original
tree under the comparison `fun a b => le (g a) (g b)`. This lets a lookup be evaluated under an
oracle that compares keys through a key function.

## Main results

* `BTree.lookupM_mapKeys`, `BTree.lookupBinM_mapKeys`: lookup commutes with `mapKeys`.
* `BTree.eval_lookupQ_keyOracle`, `BTree.eval_lookupBinQ_keyOracle`: the query programs, evaluated
  at the comparison oracle of a key function, are the pure lookups in the tree with mapped keys.
-/

public section

universe w

namespace Cslib.DataStructure.BTree

variable {α α' β : Type} {m : Type → Type w} [Monad m]

/-- Lookup in a tree with mapped keys, compared through the key function, is lookup in the
original tree under the pulled-back comparison. -/
theorem lookupM_mapKeys (le : α' → α' → m Bool) (visit : m Unit) (g : α → α')
    (k : α) (tr : BTree α β) :
    lookupM le visit (g k) (tr.mapKeys g) = lookupM (fun a b => le (g a) (g b)) visit k tr := by
  fun_induction lookupM (fun a b => le (g a) (g b)) visit k tr with
  | case1 => simp only [mapKeys_leaf]; simp only [lookupM]
  | case2 first ih =>
    simp only [mapKeys_node, mapKeysRest_eq_map, List.map_nil]
    simp only [lookupM]
    exact bind_congr fun _ => by rw [ih]
  | case3 first k' v c rest ih2 ih1 =>
    simp only [mapKeys_node, mapKeysRest_eq_map, List.map_cons, Triple.val_mk,
      Triple.child_mk] at ih1 ⊢
    simp only [lookupM]
    refine bind_congr fun b => ?_
    cases b
    · simpa using ih1
    · refine bind_congr fun _ => bind_congr fun b => ?_
      cases b
      · simpa using ih2
      · rfl

/-- The within-node binary search commutes with mapping keys. -/
private theorem slotBinM_mapKeysRest (le : α' → α' → m Bool) (g : α → α') (k : α)
    (rest : List (Triple α β)) :
    slotBinM le (g k) (mapKeysRest g rest) =
      slotBinM (fun a b => le (g a) (g b)) k rest := by
  cases rest with
  | nil => simp only [mapKeysRest_eq_map, List.map_nil, slotBinM_nil]
  | cons e l =>
    have hm : mapKeysRest g (e :: l) =
        (g e.1, e.val, e.child.mapKeys g) :: mapKeysRest g l := by
      simp only [mapKeysRest_eq_map, List.map_cons]
    have hl : (mapKeysRest g l).length = l.length := by
      rw [mapKeysRest_eq_map, List.length_map]
    rw [hm, slotBinM_cons, slotBinM_cons]
    simp only [hl, ← hm]
    simp only [mapKeysRest_eq_map, List.getElem_map, ← List.map_take, ← List.map_drop]
    simp only [← mapKeysRest_eq_map]
    rw [slotBinM_mapKeysRest le g k ((e :: l).take ((l.length + 1) / 2)),
      slotBinM_mapKeysRest le g k ((e :: l).drop ((l.length + 1) / 2 + 1))]
termination_by rest.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop, List.length_cons]
    omega

/-- Lookup with binary in-node search in a tree with mapped keys, compared through the key
function, is lookup in the original tree under the pulled-back comparison. -/
theorem lookupBinM_mapKeys (le : α' → α' → m Bool) (visit : m Unit) (g : α → α')
    (k : α) (tr : BTree α β) :
    lookupBinM le visit (g k) (tr.mapKeys g) =
      lookupBinM (fun a b => le (g a) (g b)) visit k tr := by
  induction tr using induction_children with
  | leaf => simp only [mapKeys_leaf, lookupBinM_leaf]
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

section Oracle

open Cslib.Query

variable {W : Type} [LinearOrder W]

/-- Under the comparison oracle of a key function, `lookupQ` evaluates to the pure `lookup` of the
mapped key in the tree with mapped keys. -/
theorem eval_lookupQ_keyOracle (key : α → W) (k : α) (tr : BTree α β) :
    (lookupQ k tr).eval (LEQuery.keyOracle key) = lookup (key k) (tr.mapKeys key) := by
  have h := Id.ext_iff.1
    ((FreeM.isMonadHom_pure_eval (LEQuery.keyOracle key)).map_lookupM LEQuery.ask (pure ()) k tr)
  rw [lookup_def, lookupM_mapKeys]
  simpa [lookupQ_def, Cslib.SortedAssoc.leI] using h

/-- Under the comparison oracle of a key function, `lookupBinQ` evaluates to the pure `lookupBin`
of the mapped key in the tree with mapped keys. -/
theorem eval_lookupBinQ_keyOracle (key : α → W) (k : α) (tr : BTree α β) :
    (lookupBinQ k tr).eval (LEQuery.keyOracle key) = lookupBin (key k) (tr.mapKeys key) := by
  have h := Id.ext_iff.1
    ((FreeM.isMonadHom_pure_eval (LEQuery.keyOracle key)).map_lookupBinM LEQuery.ask (pure ()) k tr)
  rw [lookupBin_def, lookupBinM_mapKeys]
  simpa [lookupBinQ_def, Cslib.SortedAssoc.leI] using h

end Oracle

end Cslib.DataStructure.BTree

/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation
import Mathlib.Tactic.FinCases

/-!
# Replacing a linked child

`replaceChild` lifts a separately represented replacement subtree into its original parent.
The replacement is separated from its parent and sibling and frames every record outside
the original child; one pointer update restores the whole linked-tree representation.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Place a distinguished child on the selected side of a linked parent. -/
@[expose] def nodeAt (right : Bool) (label : Label M extra)
    (child sibling : BinaryTree (Label M extra)) : BinaryTree (Label M extra) :=
  if right then .node label sibling child else .node label child sibling

/-- The parent contributes one address alongside its child and sibling. -/
theorem nodeAt_addresses (right : Bool) (label : Label M extra)
    (child sibling : BinaryTree (Label M extra)) :
    addresses (nodeAt right label child sibling) =
      Insert.insert label.address (addresses child ∪ addresses sibling) := by
  cases right <;> simp [nodeAt, addresses, BinaryTree.map, SearchTree.elements, Finset.union_comm]

/-- Separation of a child, its sibling, and their parent. -/
theorem nodeAt_distinct_iff (right : Bool) (label : Label M extra)
    (child sibling : BinaryTree (Label M extra)) :
    AddressesDistinct (nodeAt right label child sibling) ↔
      AddressesDistinct child ∧ AddressesDistinct sibling ∧
      label.address ∉ addresses child ∧ label.address ∉ addresses sibling ∧
      Disjoint (addresses child) (addresses sibling) := by
  cases right with
  | false => exact AddressesDistinct.node_iff ..
  | true =>
    rw [nodeAt, ite_eq_left rfl, AddressesDistinct.node_iff]
    constructor <;> rintro ⟨a, b, c, d, e⟩ <;> exact ⟨b, a, d, c, e.symm⟩

/-- The representation of a node whose distinguished child is on the selected side. -/
theorem represents_nodeAt_iff (right : Bool) (h : List (Record M (layout extra regs)))
    (parent : Pointer) (label : Label M extra) (child sibling : BinaryTree (Label M extra)) :
    Represents h parent (nodeAt right label child sibling) ↔
      h[label.address]? = some (record (if right then root sibling else root child)
        (if right then root child else root sibling) parent label) ∧
      Represents h (some label.address) child ∧ Represents h (some label.address) sibling := by
  cases right
  · exact Iff.rfl
  · exact ⟨fun r => ⟨r.1, r.2.2, r.2.1⟩, fun r => ⟨r.1, r.2.2, r.2.1⟩⟩

/-- The root of a node is its label, whichever side its distinguished child is on. -/
@[simp] theorem root_nodeAt (right : Bool) (label : Label M extra)
    (child sibling : BinaryTree (Label M extra)) :
    root (nodeAt right label child sibling) = some label.address := by
  cases right <;> rfl

/-- The root of a tree is one of its addresses. -/
theorem root_mem_addresses {t : BinaryTree (Label M extra)} {z : ℕ}
    (h : root t = some z) : z ∈ addresses t := by
  cases t with
  | nil => cases h
  | node label l r => exact (mem_addresses_iff ..).mpr ⟨.one, label, rfl, Option.some.inj h⟩

/-- Agreement on the addresses of a tree transports its representation. -/
theorem Represents.congr_addresses {h k : List (Record M (layout extra regs))}
    {t : BinaryTree (Label M extra)} {parent : Pointer} (rep : Represents h parent t)
    (agree : ∀ z ∈ addresses t, k[z]? = h[z]?) : Represents k parent t :=
  rep.congr fun p a hp => agree _ ((mem_addresses_iff ..).mpr ⟨p, a, hp, rfl⟩)

/-- Exchanging the side and the two subtrees gives the same node. -/
theorem nodeAt_not (right : Bool) (label : Label M extra)
    (child sibling : BinaryTree (Label M extra)) :
    nodeAt (!right) label sibling child = nodeAt right label child sibling := by
  cases right <;> rfl

/-- Replacing the distinguished child of a node by a tree with the same root, in a heap that
agrees outside the old child, keeps the node represented. -/
theorem Represents.nodeAt_congr_child (right : Bool) {h k : List (Record M (layout extra regs))}
    {label : Label M extra} {child child' sibling : BinaryTree (Label M extra)}
    {parent : Pointer} (rep : Represents h parent (nodeAt right label child sibling))
    (rep' : Represents k (some label.address) child') (same : root child' = root child)
    (outside : ∀ z, z ∉ addresses child → k[z]? = h[z]?)
    (nl : label.address ∉ addresses child)
    (dis : Disjoint (addresses child) (addresses sibling)) :
    Represents k parent (nodeAt right label child' sibling) := by
  obtain ⟨hl, _, hs⟩ := (represents_nodeAt_iff ..).mp rep
  refine (represents_nodeAt_iff ..).mpr ⟨by rw [outside _ nl, same]; exact hl, rep',
    hs.congr_addresses fun z hz => outside z fun m => Finset.disjoint_left.mp dis m hz⟩

/-- Reconnect a replacement child separated from its parent and sibling. Updating the parent
link preserves the sibling, global address separation, and all external records. -/
theorem replaceChild (right : Bool)
    (h k : List (Record M (layout extra regs))) (label : Label M extra)
    (old new sibling : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents h parent (nodeAt right label old sibling))
    (distinct : AddressesDistinct (nodeAt right label old sibling))
    (newRep : Represents k (some label.address) new) (newDistinct : AddressesDistinct new)
    (newRoot : label.address ∉ addresses new)
    (newSibling : Disjoint (addresses new) (addresses sibling))
    (frame : ∀ z, z ∉ addresses old → k[z]? = h[z]?) :
    let heap := k.modify label.address (fun n =>
      { n with ptr := Function.update n.ptr (if right then 1 else 0) (root new) })
    Represents heap parent (nodeAt right label new sibling) ∧
      AddressesDistinct (nodeAt right label new sibling) ∧
      (∀ z, z ∉ addresses (nodeAt right label old sibling) → heap[z]? = h[z]?) := by
  let par : Record M (layout extra regs) := record (if right then root sibling else root old)
    (if right then root old else root sibling) parent label
  let heap := k.modify label.address (fun n =>
    { n with ptr := Function.update n.ptr (if right then 1 else 0) (root new) })
  obtain ⟨hpar, _, hsib⟩ := (represents_nodeAt_iff ..).mp rep
  obtain ⟨_, ds, no, ns, dis⟩ := (nodeAt_distinct_iff ..).mp distinct
  have lookup : k[label.address]? = some par := (frame _ no).trans hpar
  have child : Represents heap (some label.address) new :=
    newRep.congr_addresses fun z hz =>
      List.getElem?_modify_ne _ _ fun eq : label.address = z => newRoot (eq ▸ hz)
  have sib : Represents heap (some label.address) sibling :=
    hsib.congr_addresses fun z hz =>
      (List.getElem?_modify_ne _ _ fun eq : label.address = z => ns (eq ▸ hz)).trans
        (frame _ fun hm => Finset.disjoint_left.mp dis hm hz)
  have head : heap[label.address]? =
      some (record (if right then root sibling else root new)
        (if right then root new else root sibling) parent label) := by
    simp only [heap, List.getElem?_modify_eq, lookup, Option.map_eq_map,
      Option.map_some, Option.some.injEq]
    cases right <;> simp only [par, record, Bool.false_eq_true, ↓reduceIte, Record.mk.injEq]
    all_goals exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
  refine ⟨(represents_nodeAt_iff ..).mpr ⟨head, child, sib⟩,
    (nodeAt_distinct_iff ..).mpr ⟨newDistinct, ds, newRoot, ns, newSibling⟩, fun z hz => ?_⟩
  rw [nodeAt_addresses] at hz
  have ne : label.address ≠ z := fun eq => hz (eq ▸ Finset.mem_insert_self _ _)
  have notOld : z ∉ addresses old := fun mem =>
    hz (Finset.mem_insert_of_mem (Finset.mem_union_left _ mem))
  exact (List.getElem?_modify_ne _ _ ne).trans (frame _ notOld)

end Cslib.DataStructure.SearchTree.PointerMachine

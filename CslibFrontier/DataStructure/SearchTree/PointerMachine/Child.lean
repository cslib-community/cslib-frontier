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
  have parts : h[label.address]? = some par ∧
      Represents h (some label.address) old ∧ Represents h (some label.address) sibling := by
    cases right with
    | false => exact rep
    | true => exact ⟨rep.1, rep.2.2, rep.2.1⟩
  obtain ⟨_, ds, no, ns, dis⟩ := (nodeAt_distinct_iff ..).mp distinct
  have lookup : k[label.address]? = some par := (frame _ no).trans parts.1
  have child : Represents heap (some label.address) new := by
    apply newRep.congr
    intro p u hu
    have mem : u.address ∈ addresses new := (mem_addresses_iff ..).mpr ⟨p, u, hu, rfl⟩
    have ne : label.address ≠ u.address := by
      intro eq
      exact newRoot (eq ▸ mem)
    exact List.getElem?_modify_ne _ _ ne
  have sib : Represents heap (some label.address) sibling := by
    apply parts.2.2.congr
    intro p u hu
    have mem : u.address ∈ addresses sibling := (mem_addresses_iff ..).mpr ⟨p, u, hu, rfl⟩
    have ne : label.address ≠ u.address := fun eq => ns (eq ▸ mem)
    have notOld : u.address ∉ addresses old := fun hm => Finset.disjoint_left.mp dis hm mem
    exact (List.getElem?_modify_ne _ _ ne).trans (frame _ notOld)
  have head : heap[label.address]? =
      some (record (if right then root sibling else root new)
        (if right then root new else root sibling) parent label) := by
    simp only [heap, List.getElem?_modify_eq, lookup, Option.map_eq_map,
      Option.map_some, Option.some.injEq]
    cases right <;> simp only [par, record, Bool.false_eq_true, ↓reduceIte, Record.mk.injEq]
    all_goals exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
  refine ⟨?_, ?_, ?_⟩
  · cases right with
    | false => exact ⟨head, child, sib⟩
    | true => exact ⟨head, sib, child⟩
  · cases right with
    | false =>
      apply (AddressesDistinct.node_iff ..).mpr
      exact ⟨newDistinct, ds, newRoot, ns, newSibling⟩
    | true =>
      apply (AddressesDistinct.node_iff ..).mpr
      exact ⟨ds, newDistinct, ns, newRoot, newSibling.symm⟩
  · intro z hz
    rw [nodeAt_addresses] at hz
    have ne : label.address ≠ z := by
      intro eq
      subst z
      exact hz (Finset.mem_insert_self _ _)
    have notOld : z ∉ addresses old := fun mem =>
      hz (Finset.mem_insert_of_mem (Finset.mem_union_left _ mem))
    exact (List.getElem?_modify_ne _ _ ne).trans (frame _ notOld)

end Cslib.DataStructure.SearchTree.PointerMachine

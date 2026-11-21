/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Context
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Child
import Mathlib.Tactic.FinCases

/-!
# Attaching a fresh leaf inside a linked context

`graftLeaf` validates the append-and-parent-update heap produced by leaf allocation.
Freshness comes from the previous heap length, so no old node can alias the new record.
The theorem reconstructs the whole linked tree, its address separation and exact footprint.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Appending at the old heap length and filling the context's vacant child link creates
exactly the plugged fresh leaf. Existing addresses remain distinct; the root changes only
for an empty context. The `side` agrees with the immediate ghost parent when one exists. -/
theorem graftLeaf (h : List (Record M (layout extra regs))) (cs : List (Frame M extra))
    (label : Label M extra) (side : Fin 2)
    (rep : Represents h none (plug cs .nil)) (distinct : AddressesDistinct (plug cs .nil))
    (atEnd : label.address = h.length)
    (chosen : match cs with
      | [] => True
      | .left _ _ :: _ => side = 0
      | .right _ _ :: _ => side = 1) :
    let extended := h ++ [record none none (contextParent cs) label]
    let heap := match contextParent cs with
      | none => extended
      | some a => extended.modify a
          (fun n => { n with ptr := Function.update n.ptr side.castSucc (some label.address) })
    let tree := plug cs (.node label .nil .nil)
    Represents heap none tree ∧ AddressesDistinct tree ∧
      addresses tree = Insert.insert label.address (addresses (plug cs .nil)) ∧
      root tree = if contextParent cs = none then some label.address else root (plug cs .nil) := by
  let extended := h ++ [record none none (contextParent cs) label]
  have fresh : label.address ∉ addresses (plug cs .nil) := by
    intro mem
    have bound := rep.address_lt mem
    omega
  have extendedRep : Represents extended none (plug cs .nil) := rep.append _
  have leafRep : Represents extended (contextParent cs) (.node label .nil .nil) := by
    simp [Represents, extended, atEnd, root]
  have leafDistinct : AddressesDistinct (.node label .nil .nil) := by
    simp [AddressesDistinct.node_iff, addresses, BinaryTree.map, SearchTree.elements]
  have wholeDistinct : AddressesDistinct (plug cs (.node label .nil .nil)) := by
    apply (addressesDistinct_plug_iff cs _).mpr
    refine ⟨leafDistinct, distinct, ?_⟩
    simpa [addresses, BinaryTree.map, SearchTree.elements] using fresh
  refine ⟨?_, wholeDistinct, ?_, ?_⟩
  · cases cs with
    | nil => exact leafRep
    | cons frame cs =>
      cases frame with
      | left parent sibling =>
        subst side
        have sub := ((represents_plug_iff extended cs (.node parent .nil sibling)).mp extendedRep).1
        have sep := distinct.focus (cs := cs)
        have freshHere : label.address ∉ addresses (.node parent .nil sibling) :=
          fun mem => fresh (addresses_subset_plug cs _ mem)
        have freshParts : label.address ≠ parent.address ∧ label.address ∉ addresses sibling := by
          simpa [addresses, BinaryTree.map, SearchTree.elements] using freshHere
        have np : parent.address ∉ addresses (.node label .nil .nil) := by
          simpa [addresses, BinaryTree.map, SearchTree.elements, ne_comm] using freshParts.1
        have ns : Disjoint (addresses (.node label .nil .nil)) (addresses sibling) := by
          simpa [addresses, BinaryTree.map, SearchTree.elements] using freshParts.2
        have changed := replaceChild false extended extended parent .nil
          (.node label .nil .nil) sibling (contextParent cs) sub sep leafRep leafDistinct np ns
          (fun _ _ => rfl)
        exact Represents.plug_of_frame (cs := cs) extendedRep distinct changed.1 rfl changed.2.2
      | right sibling parent =>
        subst side
        have sub := ((represents_plug_iff extended cs (.node parent sibling .nil)).mp extendedRep).1
        have sep := distinct.focus (cs := cs)
        have freshHere : label.address ∉ addresses (.node parent sibling .nil) :=
          fun mem => fresh (addresses_subset_plug cs _ mem)
        have freshParts : label.address ≠ parent.address ∧ label.address ∉ addresses sibling := by
          simpa [addresses, BinaryTree.map, SearchTree.elements] using freshHere
        have np : parent.address ∉ addresses (.node label .nil .nil) := by
          simpa [addresses, BinaryTree.map, SearchTree.elements, ne_comm] using freshParts.1
        have ns : Disjoint (addresses (.node label .nil .nil)) (addresses sibling) := by
          simpa [addresses, BinaryTree.map, SearchTree.elements] using freshParts.2
        have changed := replaceChild true extended extended parent .nil
          (.node label .nil .nil) sibling (contextParent cs) sub sep leafRep leafDistinct np ns
          (fun _ _ => rfl)
        exact Represents.plug_of_frame (cs := cs) extendedRep distinct changed.1 rfl changed.2.2
  · rw [addresses_plug cs (.node label .nil .nil)]
    simp [addresses, BinaryTree.map, SearchTree.elements]
  · cases cs with
    | nil => rfl
    | cons frame cs =>
      cases frame <;> exact root_plug_congr cs rfl

end Cslib.DataStructure.SearchTree.PointerMachine

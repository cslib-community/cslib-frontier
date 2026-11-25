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

private theorem graftLeaf_below (right : Bool) (h : List (Record M (layout extra regs)))
    (cs : List (Frame M extra)) (parent label : Label M extra)
    (sibling : BinaryTree (Label M extra))
    (extendedRep : Represents (h ++ [record none none (some parent.address) label]) none
      (plug cs (nodeAt right parent .nil sibling)))
    (distinct : AddressesDistinct (plug cs (nodeAt right parent .nil sibling)))
    (fresh : label.address ∉ addresses (plug cs (nodeAt right parent .nil sibling)))
    (leafRep : Represents (h ++ [record none none (some parent.address) label])
      (some parent.address) (.node label .nil .nil))
    (leafDistinct : AddressesDistinct (.node label .nil .nil)) :
    Represents ((h ++ [record none none (some parent.address) label]).modify parent.address
      (fun n =>
        { n with ptr := Function.update n.ptr (if right then 1 else 0) (some label.address) }))
      none (plug cs (nodeAt right parent (.node label .nil .nil) sibling)) := by
  have sub := ((represents_plug_iff _ cs _).mp extendedRep).1
  have freshHere : label.address ∉ addresses (nodeAt right parent .nil sibling) :=
    fun mem => fresh (addresses_subset_plug cs _ mem)
  rw [nodeAt_addresses] at freshHere
  have freshParts : label.address ≠ parent.address ∧ label.address ∉ addresses sibling := by
    simpa [addresses, BinaryTree.map, SearchTree.elements] using freshHere
  have changed := replaceChild right _ _ parent .nil (.node label .nil .nil) sibling
    (contextParent cs) sub distinct.focus leafRep leafDistinct
    (by simpa [addresses, BinaryTree.map, SearchTree.elements, ne_comm] using freshParts.1)
    (by simpa [addresses, BinaryTree.map, SearchTree.elements] using freshParts.2)
    (fun _ _ => rfl)
  exact extendedRep.plug_of_frame distinct changed.1 (by simp) changed.2.2

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
  have fresh : label.address ∉ addresses (plug cs .nil) := fun mem => by
    have := rep.address_lt mem; omega
  have extendedRep : Represents extended none (plug cs .nil) := rep.append _
  have leafRep : Represents extended (contextParent cs) (.node label .nil .nil) := by
    simp [Represents, extended, atEnd, root]
  have leafDistinct : AddressesDistinct (.node label .nil .nil) := by
    simp [AddressesDistinct.node_iff, addresses, BinaryTree.map, SearchTree.elements]
  refine ⟨?_, (addressesDistinct_plug_iff cs _).mpr ⟨leafDistinct, distinct,
    by simpa [addresses, BinaryTree.map, SearchTree.elements] using fresh⟩, ?_, ?_⟩
  · rcases cs with _ | ⟨⟨parent, sibling⟩ | ⟨sibling, parent⟩, cs⟩
    · exact leafRep
    · subst chosen
      exact graftLeaf_below false h cs parent label sibling extendedRep distinct fresh
        leafRep leafDistinct
    · subst chosen
      exact graftLeaf_below true h cs parent label sibling extendedRep distinct fresh
        leafRep leafDistinct
  · rw [addresses_plug cs (.node label .nil .nil)]
    simp [addresses, BinaryTree.map, SearchTree.elements]
  · cases cs with
    | nil => rfl
    | cons frame cs => cases frame <;> exact root_plug_congr cs rfl

end Cslib.DataStructure.SearchTree.PointerMachine

/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation
import CslibFrontier.DataStructure.SearchTree.PointerMachine.Child

/-!
# Ancestors of a linked subtree

These ghost frames describe ancestors and siblings, not an additional machine stack.
They adapt the ancestor contexts and labelled cursors of Stefan Langerman's earlier
`lean-bst` development to Frontier's `BinaryTree`.
`represents_plug_iff` decomposes a whole-tree heap representation into the focused subtree
and its surrounding context, and conversely reconstructs it. Parent pointers implement
the corresponding machine navigation.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- One ghost ancestor, retaining its label and the sibling outside the focus. -/
inductive Frame (M : Model) (extra : ℕ) where
  /-- The focus is the left child. -/
  | left (label : Label M extra) (right : BinaryTree (Label M extra))
  /-- The focus is the right child. -/
  | right (left : BinaryTree (Label M extra)) (label : Label M extra)

/-- Reconstruct the tree, with the immediate parent first in the context. -/
@[expose] def plug : List (Frame M extra) →
    BinaryTree (Label M extra) → BinaryTree (Label M extra)
  | [], t => t
  | .left label r :: cs, t => plug cs (.node label t r)
  | .right l label :: cs, t => plug cs (.node label l t)

/-- The immediate parent's address, or null at the overall root. -/
@[expose] def contextParent : List (Frame M extra) → Pointer
  | [] => none
  | .left label _ :: _ | .right _ label :: _ => some label.address

private theorem frame_nodeAt (f : Frame M extra) :
    ∃ (right : Bool) (label : Label M extra) (sibling : BinaryTree (Label M extra)),
      (∀ cs t, plug (f :: cs) t = plug cs (nodeAt right label t sibling)) ∧
      ∀ cs : List (Frame M extra), contextParent (f :: cs) = some label.address := by
  cases f with
  | left label sibling => exact ⟨false, label, sibling, fun _ _ => rfl, fun _ => rfl⟩
  | right sibling label => exact ⟨true, label, sibling, fun _ _ => rfl, fun _ => rfl⟩

@[simp] private theorem addresses_nil :
    addresses (.nil : BinaryTree (Label M extra)) = ∅ := rfl

/-- A plugged tree consists of the focus addresses and the addresses in its context. -/
theorem addresses_plug (cs : List (Frame M extra)) (t : BinaryTree (Label M extra)) :
    addresses (plug cs t) = addresses t ∪ addresses (plug cs .nil) := by
  induction cs generalizing t with
  | nil => simp [plug]
  | cons frame cs ih =>
    obtain ⟨right, label, sibling, hplug, -⟩ := frame_nodeAt frame
    rw [hplug cs t, hplug cs .nil,
      ih (nodeAt right label t sibling), ih (nodeAt right label .nil sibling)]
    simp [nodeAt_addresses, Finset.insert_union, Finset.union_insert, Finset.union_assoc]

/-- Heap representation of the ancestors and siblings around a supplied focus link.
The list and labels are proof data; no unbounded register or stack is added to the machine. -/
@[expose] def ContextRep (heap : List (Record M (layout extra regs))) :
    Pointer → List (Frame M extra) → Prop
  | _, [] => True
  | p, .left label r :: cs =>
      heap[label.address]? = some (record p (root r) (contextParent cs) label) ∧
        Represents heap (some label.address) r ∧ ContextRep heap (some label.address) cs
  | p, .right l label :: cs =>
      heap[label.address]? = some (record (root l) p (contextParent cs) label) ∧
        Represents heap (some label.address) l ∧ ContextRep heap (some label.address) cs

/-- A whole-tree representation is exactly the focused subtree plus its ancestor/sibling
context. This permits local mutation proofs to reconstruct the complete tree. -/
theorem represents_plug_iff (heap : List (Record M (layout extra regs)))
    (cs : List (Frame M extra)) (t : BinaryTree (Label M extra)) :
    Represents heap none (plug cs t) ↔
      Represents heap (contextParent cs) t ∧ ContextRep heap (root t) cs := by
  induction cs generalizing t with
  | nil => simp [plug, contextParent, ContextRep]
  | cons frame cs ih =>
    cases frame <;>
      simp only [plug, ih, contextParent, ContextRep, Represents, root] <;> tauto

/-- A complete tree is separated exactly when its focus and context are individually
separated and their address footprints are disjoint. -/
theorem addressesDistinct_plug_iff (cs : List (Frame M extra))
    (t : BinaryTree (Label M extra)) :
    AddressesDistinct (plug cs t) ↔ AddressesDistinct t ∧
      AddressesDistinct (plug cs .nil) ∧ Disjoint (addresses t) (addresses (plug cs .nil)) := by
  induction cs generalizing t with
  | nil => simp [plug]
  | cons f cs ih =>
    obtain ⟨right, label, sibling, hplug, -⟩ := frame_nodeAt f
    rw [hplug cs t, hplug cs .nil,
      ih (nodeAt right label t sibling), ih (nodeAt right label .nil sibling),
      addresses_plug cs (nodeAt right label .nil sibling)]
    simp only [nodeAt_distinct_iff, nodeAt_addresses, AddressesDistinct.nil, addresses_nil,
      Finset.empty_union, Finset.notMem_empty, not_false_eq_true, Finset.disjoint_empty_left,
      Finset.disjoint_insert_left, Finset.disjoint_union_left, Finset.disjoint_union_right,
      Finset.disjoint_insert_right, true_and, and_true]
    tauto

/-- A focused subtree inherits distinct addresses from its complete tree. -/
theorem AddressesDistinct.focus {cs : List (Frame M extra)}
    {t : BinaryTree (Label M extra)} (h : AddressesDistinct (plug cs t)) :
    AddressesDistinct t := (addressesDistinct_plug_iff cs t).mp h |>.1

/-- Replacing a focus by a separated tree with the same address footprint preserves
separation from every ancestor and sibling. -/
theorem AddressesDistinct.plug {cs : List (Frame M extra)}
    {before after : BinaryTree (Label M extra)}
    (h : AddressesDistinct (PointerMachine.plug cs before))
    (ha : AddressesDistinct after) (same : addresses after = addresses before) :
    AddressesDistinct (PointerMachine.plug cs after) := by
  obtain ⟨_, hc, hd⟩ := (addressesDistinct_plug_iff cs before).mp h
  exact (addressesDistinct_plug_iff cs after).mpr ⟨ha, hc, by simpa only [same] using hd⟩

/-- Equal focus roots give equal complete-tree roots, independently of interior shape. -/
theorem root_plug_congr (cs : List (Frame M extra))
    {a b : BinaryTree (Label M extra)} (eq : root a = root b) :
    root (plug cs a) = root (plug cs b) := by
  induction cs generalizing a b with
  | nil => exact eq
  | cons f cs ih => cases f <;> exact ih rfl

/-- The focused addresses are among the complete tree's addresses. -/
theorem addresses_subset_plug (cs : List (Frame M extra))
    (t : BinaryTree (Label M extra)) : addresses t ⊆ addresses (plug cs t) := by
  rw [addresses_plug]
  exact Finset.subset_union_left

/-- A focus's height plus its ancestor count is bounded by the complete tree's height. -/
theorem height_add_context_length_le (cs : List (Frame M extra))
    (t : BinaryTree (Label M extra)) : t.height + cs.length ≤ (plug cs t).height := by
  induction cs generalizing t with
  | nil => simp [plug]
  | cons frame cs ih =>
    obtain ⟨right, label, sibling, hplug, -⟩ := frame_nodeAt frame
    have h := ih (nodeAt right label t sibling)
    cases right <;>
      (simp only [hplug, nodeAt, Bool.false_eq_true, ↓reduceIte, List.length_cons,
        BinaryTree.height] at *; omega)

/-- A local replacement with the same root reconstructs the whole tree when the heap
outside the original focus is unchanged. Separation is derived from the original tree. -/
theorem Represents.plug_of_frame {h k : List (Record M (layout extra regs))}
    {cs : List (Frame M extra)} {before after : BinaryTree (Label M extra)}
    (rep : Represents h none (plug cs before)) (distinct : AddressesDistinct (plug cs before))
    (newRep : Represents k (contextParent cs) after) (sameRoot : root after = root before)
    (frame : ∀ a, a ∉ addresses before → k[a]? = h[a]?) :
    Represents k none (plug cs after) := by
  induction cs generalizing before after with
  | nil => exact newRep
  | cons f cs ih =>
    obtain ⟨right, label, sibling, hplug, hpar⟩ := frame_nodeAt f
    rw [hpar] at newRep
    rw [hplug] at rep distinct ⊢
    obtain ⟨_, _, no, _, dis⟩ := (nodeAt_distinct_iff ..).mp distinct.focus
    refine ih rep distinct ((((represents_plug_iff ..).mp rep).1).nodeAt_congr_child right
      newRep sameRoot frame no dis) (by simp) fun a ha => frame a fun mem => ha ?_
    rw [nodeAt_addresses]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ mem)

/-- Following a represented nonempty focus's parent takes one load and halt. The heap,
scalars and every other pointer register survive; at the root the resulting cursor is null. -/
theorem ascend_correct (s : State M (layout extra regs)) (cs : List (Frame M extra))
    (label : Label M extra) (l r : BinaryTree (Label M extra))
    (rep : Represents s.heap (contextParent cs) (.node label l r))
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t, Executes [.loadPtr 0 2 0, .halt] s t 2 ∧
      t.heap = s.heap ∧ t.data = s.data ∧ t.ptr 0 = contextParent cs ∧
      (∀ i, i ≠ 0 → t.ptr i = s.ptr i) := by
  let t := { s.setPtr 0 (contextParent cs) with pc := 1 }
  refine ⟨t, ⟨1, .single ?_, rfl, rfl⟩, rfl, rfl, ?_, ?_⟩
  · simp [step, pc, Instr.effect, Instr.next, State.deref, cursor, rep.1, record, t]
  · simp [t, State.setPtr]
  · intro i hi
    simp [t, State.setPtr, hi]

end Cslib.DataStructure.SearchTree.PointerMachine

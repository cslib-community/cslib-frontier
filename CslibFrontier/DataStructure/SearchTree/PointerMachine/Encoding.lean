/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation

/-!
# Canonical linked-tree input encoding

Preorder enumeration assigns consecutive ghost addresses to an existing `BinaryTree`.
The heap contains precisely its records, including parent links, and preserves every scalar
field. This is an input encoding; no machine instruction observes the assigned addresses.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Assign consecutive preorder addresses, retaining all scalar fields. -/
@[expose] def labelTree (base : ℕ) :
    BinaryTree (Fin (extra + 1) → M.Value) → BinaryTree (Label M extra)
  | .nil => .nil
  | .node data l r => .node ⟨base, data⟩ (labelTree (base + 1) l)
      (labelTree (base + 1 + l.numNodes) r)

/-- The preorder list of records, with the supplied external parent pointer. -/
@[expose] def encodeHeap (t : BinaryTree (Fin (extra + 1) → M.Value))
    (base : ℕ) (parent : Pointer) : List (Record M (layout extra regs)) :=
  match t with
  | .nil => []
  | .node data l r =>
    record (root (labelTree (base + 1) l))
      (root (labelTree (base + 1 + l.numNodes) r)) parent ⟨base, data⟩ ::
    (encodeHeap l (base + 1) (some base) ++
      encodeHeap r (base + 1 + l.numNodes) (some base))

/-- Encoding uses one record per node. -/
@[simp] theorem length_encodeHeap (t : BinaryTree (Fin (extra + 1) → M.Value))
    (base : ℕ) (parent : Pointer) :
    (encodeHeap (regs := regs) t base parent).length = t.numNodes := by
  induction t generalizing base parent with
  | nil => rfl
  | node data l r il ir => simp [encodeHeap, il, ir]

/-- Every assigned address lies in the consecutive interval reserved for its tree. -/
theorem address_labelTree {t : BinaryTree (Fin (extra + 1) → M.Value)}
    {base a : ℕ} (mem : a ∈ addresses (labelTree base t)) :
    base ≤ a ∧ a < base + t.numNodes := by
  induction t generalizing base with
  | nil => simp [labelTree, addresses, SearchTree.elements, BinaryTree.map] at mem
  | node data l r il ir =>
    change a ∈ Insert.insert base
      (addresses (labelTree (base + 1) l) ∪
        addresses (labelTree (base + 1 + l.numNodes) r)) at mem
    simp only [Finset.mem_insert, Finset.mem_union] at mem
    rcases mem with eq | hl | hr
    · subst a; simp
    · have := il hl; simp only [BinaryTree.numNodes]; omega
    · have := ir hr; simp only [BinaryTree.numNodes]; omega

/-- Preorder addresses distinguish all nodes. -/
theorem addressesDistinct_labelTree (base : ℕ)
    (t : BinaryTree (Fin (extra + 1) → M.Value)) :
    AddressesDistinct (labelTree base t) := by
  induction t generalizing base with
  | nil => exact AddressesDistinct.nil
  | node data l r il ir =>
    refine (AddressesDistinct.node_iff _ _ _).mpr ⟨il _, ir _,
      fun mem => by
        have := address_labelTree mem
        dsimp at this
        omega,
      fun mem => by
        have := address_labelTree mem
        dsimp at this
        omega,
      Finset.disjoint_left.mpr fun a hl hr => by
        have := address_labelTree hl
        have := address_labelTree hr
        omega⟩

/-- The encoded records represent the tree at their actual positions in any ambient heap. -/
theorem represents_encodeHeap (t : BinaryTree (Fin (extra + 1) → M.Value))
    (pre post : List (Record M (layout extra regs))) (parent : Pointer) :
    Represents (pre ++ encodeHeap t pre.length parent ++ post) parent
      (labelTree pre.length t) := by
  induction t generalizing pre post parent with
  | nil => trivial
  | node data l r il ir =>
    let entry : Record M (layout extra regs) := record (root (labelTree (pre.length + 1) l))
      (root (labelTree (pre.length + 1 + l.numNodes) r)) parent
      (⟨pre.length, data⟩ : Label M extra)
    refine ⟨by simp [encodeHeap], ?_, ?_⟩
    · simpa [encodeHeap, entry, List.append_assoc] using il (pre ++ [entry])
        (encodeHeap r (pre.length + 1 + l.numNodes) (some pre.length) ++ post) (some pre.length)
    · simpa [encodeHeap, entry, List.append_assoc, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ir (pre ++ entry :: encodeHeap l (pre.length + 1)
          (some pre.length)) post (some pre.length)

private theorem root_labelTree_lt {t : BinaryTree (Fin (extra + 1) → M.Value)}
    {base a : ℕ} (eq : root (labelTree base t) = some a) : a < base + t.numNodes := by
  cases t with
  | nil => cases eq
  | node data l r =>
    obtain rfl := Option.some.inj eq
    simp

/-- Every heap edge is valid within an ambient heap containing this tree and its parent. -/
theorem encodeHeap_links (t : BinaryTree (Fin (extra + 1) → M.Value))
    (base : ℕ) (parent : Pointer) {size : ℕ} (bound : base + t.numNodes ≤ size)
    (parentBound : ∀ a, parent = some a → a < size) :
    ∀ n ∈ encodeHeap (regs := regs) t base parent, ∀ f a, n.ptr f = some a → a < size := by
  induction t generalizing base parent with
  | nil => simp [encodeHeap]
  | node data l r il ir =>
    simp only [BinaryTree.numNodes] at bound
    have hp (b : ℕ) (hb : some base = some b) : b < size := Option.some.inj hb ▸ by omega
    intro n mem f a eq
    simp only [encodeHeap, List.mem_cons, List.mem_append] at mem
    rcases mem with rfl | hl | hr
    · simp only [record] at eq
      split at eq
      · have := root_labelTree_lt eq
        omega
      · split at eq
        · have := root_labelTree_lt eq
          omega
        · exact parentBound a eq
    · exact il (base + 1) (some base) (by omega) hp n hl f a eq
    · exact ir (base + 1 + l.numNodes) (some base) (by omega) hp n hr f a eq

end Cslib.DataStructure.SearchTree.PointerMachine

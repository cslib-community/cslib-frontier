/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Basic
public import CslibFrontier.DataStructure.SearchTree.Cost
public import Mathlib.Data.Tree.Get

/-!
# Linked representations of binary search trees

The left/right/parent record layout and recursive heap representation adapt Stefan Langerman's
earlier `lean-bst` development. This is an adaptation of that design, not a verbatim port of a
pinned source module. Mathematical trees use Frontier's existing `BinaryTree`.
Addresses are ghost labels, inaccessible to scalar instructions.
Extra data fields hold values and balancing metadata. Unrelated heap records are permitted.

`Represents` describes the contents of a subtree, independently of ordering and of a cursor.
Mutation routines must additionally establish separation of the records they modify.
The companion search module proves charged machine execution against `SearchTree.contains`.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine

open Cslib.PointerMachine

/-- Cursor, root, parent, grandparent, middle, null and comparison pointer registers;
query and temporary data registers followed by client registers. Records contain
left, right and parent links, then a key and client data fields. -/
abbrev layout (extra regs : ℕ) : Layout := ⟨7, regs + 2, 3, extra + 1⟩

/-- A ghost address and all scalar fields of a tree node. Only `data` is available
through scalar loads; `address` records its heap location for the proof. -/
structure Label (M : Model) (extra : ℕ) where
  /-- Heap location, used only in the representation proof. -/
  address : ℕ
  /-- Key in field zero, followed by client data. -/
  data : Fin (extra + 1) → M.Value

variable {M : Model} {extra regs : ℕ}

/-- Different positions in the represented tree have different heap addresses. -/
@[expose] def AddressesDistinct (t : BinaryTree (Label M extra)) : Prop :=
  ∀ p q u v, t.get p = some u → t.get q = some v → u.address = v.address → p = q

/-- The empty tree has no repeated address. -/
@[simp] theorem AddressesDistinct.nil : AddressesDistinct (.nil : BinaryTree (Label M extra)) := by
  intro p q u v hp
  cases p <;> cases hp

/-- The finite set of ghost node addresses. This is a proof footprint, not scalar data
available to the machine. -/
@[expose] def addresses (t : BinaryTree (Label M extra)) : Finset ℕ :=
  SearchTree.elements (t.map Label.address)

/-- The address footprint consists exactly of labels at existing tree positions. -/
theorem mem_addresses_iff (t : BinaryTree (Label M extra)) (a : ℕ) :
    a ∈ addresses t ↔ ∃ p label, t.get p = some label ∧ label.address = a := by
  induction t with
  | nil => simp [addresses, SearchTree.elements, BinaryTree.map, BinaryTree.get]
  | node label l r il ir =>
    change a ∈ Insert.insert label.address (addresses l ∪ addresses r) ↔ _
    simp only [Finset.mem_insert, Finset.mem_union, il, ir]
    constructor
    · rintro (h | ⟨p, u, hp, ha⟩ | ⟨p, u, hp, ha⟩)
      · exact ⟨.one, label, rfl, h.symm⟩
      · exact ⟨.bit0 p, u, hp, ha⟩
      · exact ⟨.bit1 p, u, hp, ha⟩
    · rintro ⟨p, u, hp, ha⟩
      cases p with
      | one =>
        cases Option.some.inj hp
        exact .inl ha.symm
      | bit0 p => exact .inr (.inl ⟨p, u, hp, ha⟩)
      | bit1 p => exact .inr (.inr ⟨p, u, hp, ha⟩)

/-- Address separation at a node consists of separation within each child and disjoint
child footprints, neither containing the root. -/
theorem AddressesDistinct.node_iff (label : Label M extra)
    (l r : BinaryTree (Label M extra)) :
    AddressesDistinct (.node label l r) ↔
      AddressesDistinct l ∧ AddressesDistinct r ∧
      label.address ∉ addresses l ∧ label.address ∉ addresses r ∧
      Disjoint (addresses l) (addresses r) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro p q u v hp hq eq
      exact PosNum.bit0.inj (h (.bit0 p) (.bit0 q) u v hp hq eq)
    · intro p q u v hp hq eq
      exact PosNum.bit1.inj (h (.bit1 p) (.bit1 q) u v hp hq eq)
    · intro mem
      obtain ⟨p, u, hp, eq⟩ := (mem_addresses_iff l label.address).mp mem
      have bad := h (.bit0 p) .one u label hp rfl eq
      cases bad
    · intro mem
      obtain ⟨p, u, hp, eq⟩ := (mem_addresses_iff r label.address).mp mem
      have bad := h (.bit1 p) .one u label hp rfl eq
      cases bad
    · apply Finset.disjoint_left.mpr
      intro a hl hr
      obtain ⟨p, u, hp, eu⟩ := (mem_addresses_iff l a).mp hl
      obtain ⟨q, v, hq, ev⟩ := (mem_addresses_iff r a).mp hr
      have bad := h (.bit0 p) (.bit1 q) u v hp hq (eu.trans ev.symm)
      cases bad
  · rintro ⟨hl, hr, nl, nr, dis⟩ p q u v hp hq eq
    cases p with
    | one =>
      cases Option.some.inj hp
      cases q with
      | one => rfl
      | bit0 q => exact (nl ((mem_addresses_iff l label.address).mpr ⟨q, v, hq, eq.symm⟩)).elim
      | bit1 q => exact (nr ((mem_addresses_iff r label.address).mpr ⟨q, v, hq, eq.symm⟩)).elim
    | bit0 p =>
      cases q with
      | one =>
        cases Option.some.inj hq
        exact (nl ((mem_addresses_iff l label.address).mpr ⟨p, u, hp, eq⟩)).elim
      | bit0 q => exact congrArg PosNum.bit0 (hl p q u v hp hq eq)
      | bit1 q =>
        exact (Finset.disjoint_left.mp dis
          ((mem_addresses_iff l u.address).mpr ⟨p, u, hp, rfl⟩)
          ((mem_addresses_iff r u.address).mpr ⟨q, v, hq, eq.symm⟩)).elim
    | bit1 p =>
      cases q with
      | one =>
        cases Option.some.inj hq
        exact (nr ((mem_addresses_iff r label.address).mpr ⟨p, u, hp, eq⟩)).elim
      | bit0 q =>
        exact (Finset.disjoint_left.mp dis
          ((mem_addresses_iff l u.address).mpr ⟨q, v, hq, eq.symm⟩)
          ((mem_addresses_iff r u.address).mpr ⟨p, u, hp, rfl⟩)).elim
      | bit1 q => exact congrArg PosNum.bit1 (hr p q u v hp hq eq)

/-- Root address of a ghost-labelled tree; the empty tree has a null root. -/
@[expose] def root : BinaryTree (Label M extra) → Pointer
  | .nil => none
  | .node x _ _ => some x.address

/-- Concrete left/right/parent record for a ghost label. -/
@[expose] def record (l r p : Pointer) (x : Label M extra) : Record M (layout extra regs) :=
  ⟨fun i => if i = 0 then l else if i = 1 then r else p, x.data⟩

/-- Every node has its labelled address, scalar fields and prescribed child/parent links.
The first pointer is the external parent of the represented subtree. -/
@[expose] def Represents (heap : List (Record M (layout extra regs))) :
    Pointer → BinaryTree (Label M extra) → Prop
  | _, .nil => True
  | p, .node x l r => heap[x.address]? = some (record (root l) (root r) p x) ∧
      Represents heap (some x.address) l ∧ Represents heap (some x.address) r

/-- Agreement on the represented tree's records transports its heap representation.
Unrelated records may change arbitrarily. -/
theorem Represents.congr {h k : List (Record M (layout extra regs))}
    {t : BinaryTree (Label M extra)} {parent : Pointer} (rep : Represents h parent t)
    (agree : ∀ p a, t.get p = some a → k[a.address]? = h[a.address]?) :
    Represents k parent t := by
  induction t generalizing parent with
  | nil => trivial
  | node a l r il ir =>
    exact ⟨(agree .one a rfl).trans rep.1,
      il rep.2.1 (fun p b hp => agree (.bit0 p) b hp),
      ir rep.2.2 (fun p b hp => agree (.bit1 p) b hp)⟩

/-- Every address in a represented subtree lies within the allocated heap. -/
theorem Represents.address_lt {heap : List (Record M (layout extra regs))}
    {parent : Pointer} {tree : BinaryTree (Label M extra)}
    (rep : Represents heap parent tree) {a : ℕ} (mem : a ∈ addresses tree) :
    a < heap.length := by
  induction tree generalizing parent with
  | nil => simp [addresses, SearchTree.elements, BinaryTree.map] at mem
  | node label l r il ir =>
    change a ∈ Insert.insert label.address (addresses l ∪ addresses r) at mem
    rcases Finset.mem_insert.mp mem with eq | mem
    · subst a
      exact (List.getElem?_eq_some_iff.mp rep.1).1
    · rcases Finset.mem_union.mp mem with mem | mem
      · exact il rep.2.1 mem
      · exact ir rep.2.2 mem

/-- Appending fresh records preserves every existing linked-tree representation. -/
theorem Represents.append {heap : List (Record M (layout extra regs))}
    {parent : Pointer} {tree : BinaryTree (Label M extra)}
    (h : Represents heap parent tree) (suffix : List (Record M (layout extra regs))) :
    Represents (heap ++ suffix) parent tree := by
  induction tree generalizing parent with
  | nil => trivial
  | node label left right ihl ihr =>
    refine ⟨?_, ihl h.2.1, ihr h.2.2⟩
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp h.1
    rw [List.getElem?_append_left bound]
    exact h.1

/-- Forget addresses and metadata, retaining the keys in Frontier's existing tree type. -/
@[expose] def keys (t : BinaryTree (Label M extra)) : BinaryTree M.Value :=
  t.map fun x => x.data 0

end Cslib.DataStructure.SearchTree.PointerMachine

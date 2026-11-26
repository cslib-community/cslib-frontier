/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation

/-!
# Scalar updates in linked trees

A scalar store updates the represented node's field without changing any links or registers.
The ghost tree records the same update at every occurrence of that address; no separation
hypothesis is needed. Updating a non-key field preserves the entire key tree.
This supplies payload and cached-metadata writes for a mutable dictionary, not AVL rebalancing.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

/-- Update one scalar field at a ghost address, retaining all addresses and links. -/
@[expose] def updateData (t : BinaryTree (Label M extra)) (a : ℕ)
    (field : Fin (extra + 1)) (value : M.Value) : BinaryTree (Label M extra) :=
  t.map fun label =>
    { label with data := if label.address = a then Function.update label.data field value
      else label.data }

/-- Scalar-field updates preserve the root pointer. -/
theorem root_updateData (t : BinaryTree (Label M extra)) (a : ℕ)
    (field : Fin (extra + 1)) (value : M.Value) :
    root (updateData t a field value) = root t := by
  cases t <;> rfl

/-- Payload or metadata writes leave the key tree unchanged. -/
theorem keys_updateData (t : BinaryTree (Label M extra)) (a : ℕ)
    (field : Fin (extra + 1)) (value : M.Value) (notKey : field ≠ 0) :
    keys (updateData t a field value) = keys t := by
  induction t with
  | nil => rfl
  | node label l r il ir =>
    change BinaryTree.node _ (keys (updateData l a field value))
      (keys (updateData r a field value)) = _
    rw [il, ir]
    by_cases h : label.address = a <;>
      simp [keys, BinaryTree.map, h, Ne.symm notKey]

/-- A heap scalar write implements the corresponding ghost-tree update. -/
theorem Represents.updateData {heap : List (Record M (layout extra regs))}
    {parent : Pointer} {t : BinaryTree (Label M extra)}
    (rep : Represents heap parent t) (a : ℕ)
    (field : Fin (extra + 1)) (value : M.Value) :
    Represents (heap.modify a fun n => { n with data := Function.update n.data field value })
      parent (updateData t a field value) := by
  induction t generalizing parent with
  | nil => trivial
  | node label l r il ir =>
    refine ⟨?_, il rep.2.1, ir rep.2.2⟩
    change (heap.modify a _)[label.address]? =
      some (record (root (PointerMachine.updateData l a field value))
        (root (PointerMachine.updateData r a field value))
        parent { label with data :=
          if label.address = a then Function.update label.data field value else label.data })
    rw [root_updateData, root_updateData]
    rcases eq_or_ne label.address a with rfl | h
    · simp [rep.1, record]
    · simp [h, Ne.symm h, rep.1, record]

/-- A store followed by halt takes two instructions, preserves all registers and links,
and updates exactly the selected field in the represented tree. The base register may
designate a node anywhere in the tree (or an unrelated record). -/
theorem storeData_correct (x : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents x.heap parent t) (base : Fin 7) (a : ℕ)
    (cursor : x.ptr base = some a) (field : Fin (extra + 1))
    (src : Fin (regs + 2)) (pc : x.pc = 0) :
    ∃ y, Executes [.storeData field base src, .halt] x y 2 ∧
      Represents y.heap parent (updateData t a field (x.data src)) ∧
      y.ptr = x.ptr ∧ y.data = x.data ∧ y.heap.length = x.heap.length ∧
      (∀ b, b ≠ a → y.heap[b]? = x.heap[b]?) := by
  let y : State M (layout extra regs) :=
    { x with pc := 1, heap := x.heap.modify a fun n =>
        { n with data := Function.update n.data field (x.data src) } }
  exact ⟨y, ⟨1, .single (by simp [step, pc, Instr.effect, State.modify, cursor, Instr.next, y]),
    rfl, rfl⟩, rep.updateData a field (x.data src), rfl, rfl, List.length_modify ..,
    fun _ hb => List.getElem?_modify_ne _ _ (Ne.symm hb)⟩

/-- A scalar write outside a tree leaves that ghost tree unchanged. -/
theorem updateData_eq_self (tree : BinaryTree (Label M extra)) (a : ℕ)
    (field : Fin (extra + 1)) (value : M.Value)
    (fresh : ∀ p u, tree.get p = some u → u.address ≠ a) :
    updateData tree a field value = tree := by
  induction tree with
  | nil => rfl
  | node label l r il ir =>
    change BinaryTree.node { label with data :=
      if label.address = a then Function.update label.data field value else label.data }
      (updateData l a field value) (updateData r a field value) = _
    rw [il (fun p u => fresh (.bit0 p) u), ir (fun p u => fresh (.bit1 p) u)]
    simp [fresh .one label rfl]


/-- Scalar-field writes preserve the complete node-address footprint. -/
@[simp] theorem addresses_updateData (tree : BinaryTree (Label M extra)) (a : ℕ)
    (field : Fin (extra + 1)) (value : M.Value) :
    addresses (updateData tree a field value) = addresses tree := by
  unfold addresses updateData
  rw [← BinaryTree.comp_map]
  rfl

/-- Scalar-field updates preserve the separation of node addresses. -/
theorem AddressesDistinct.updateData {tree : BinaryTree (Label M extra)}
    (h : AddressesDistinct tree) (a : ℕ) (field : Fin (extra + 1)) (value : M.Value) :
    AddressesDistinct (updateData tree a field value) := by
  have haddr (p : PosNum) :
      ((PointerMachine.updateData tree a field value).get p).map Label.address =
        (tree.get p).map Label.address := by
    clear h
    induction tree generalizing p with
    | nil => rfl
    | node _ _ _ _ _ =>
      cases p <;> simp_all [PointerMachine.updateData, BinaryTree.map, BinaryTree.get]
  intro p q u v hp hq eq
  obtain ⟨u', hu, eu⟩ := Option.map_eq_some_iff.mp
    ((haddr p).symm.trans (congrArg (Option.map _) hp))
  obtain ⟨v', hv, ev⟩ := Option.map_eq_some_iff.mp
    ((haddr q).symm.trans (congrArg (Option.map _) hq))
  exact h p q u' v' hu hv (eu.trans (eq.trans ev.symm))

end Cslib.DataStructure.SearchTree.PointerMachine

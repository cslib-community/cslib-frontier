/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation

/-! # Locating keys and payloads in linked search trees

Strict key ordering identifies a unique tree position for each key. A represented position
also identifies its allocated heap record and complete scalar payload.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Every label found at a tree position contributes its key to the represented key set. -/
theorem key_mem_of_get [LinearOrder M.Value] {tree : BinaryTree (Label M extra)}
    {p : PosNum} {a : Label M extra} (h : tree.get p = some a) :
    a.data 0 ∈ SearchTree.elements (keys tree) := by
  induction tree generalizing p with
  | nil => cases p <;> cases h
  | node b l r il ir =>
    cases p with
    | one => cases Option.some.inj h; exact Finset.mem_insert_self _ _
    | bit0 p => exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (il h))
    | bit1 p => exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ir h))

/-- In a strictly ordered linked tree, equal keys occupy the same position. -/
theorem get_key_injective [LinearOrder M.Value] {tree : BinaryTree (Label M extra)}
    (ordered : SearchTree.Ordered (keys tree)) {p q : PosNum} {a b : Label M extra}
    (hp : tree.get p = some a) (hq : tree.get q = some b) (eq : a.data 0 = b.data 0) : p = q := by
  induction tree generalizing p q with
  | nil => cases p <;> cases hp
  | node c l r il ir =>
    obtain ⟨hl, hr, low, high⟩ := ordered
    cases p with
    | one =>
      cases Option.some.inj hp
      cases q with
      | one => rfl
      | bit0 q => exact (lt_irrefl _ (eq ▸ low _ (key_mem_of_get hq))).elim
      | bit1 q => exact (lt_irrefl _ (eq ▸ high _ (key_mem_of_get hq))).elim
    | bit0 p =>
      cases q with
      | one =>
        cases Option.some.inj hq
        exact (lt_irrefl _ (eq ▸ low _ (key_mem_of_get hp))).elim
      | bit0 q => exact congrArg PosNum.bit0 (il hl hp hq)
      | bit1 q =>
        have h := lt_trans (low _ (key_mem_of_get hp)) (high _ (key_mem_of_get hq))
        exact (lt_irrefl _ (eq ▸ h)).elim
    | bit1 p =>
      cases q with
      | one =>
        cases Option.some.inj hq
        exact (lt_irrefl _ (eq ▸ high _ (key_mem_of_get hp))).elim
      | bit0 q =>
        have h := lt_trans (low _ (key_mem_of_get hq)) (high _ (key_mem_of_get hp))
        exact (lt_irrefl _ (eq ▸ h)).elim
      | bit1 q => exact congrArg PosNum.bit1 (ir hr hp hq)

/-- A represented position has an allocated record with exactly the ghost label's data. -/
theorem Represents.get {heap : List (Record M (layout extra regs))} {parent : Pointer}
    {tree : BinaryTree (Label M extra)} (rep : Represents heap parent tree)
    {p : PosNum} {a : Label M extra} (get : tree.get p = some a) :
    ∃ node, heap[a.address]? = some node ∧ node.data = a.data := by
  induction tree generalizing parent p with
  | nil => cases p <;> cases get
  | node b l r il ir =>
    cases p with
    | one => cases Option.some.inj get; exact ⟨_, rep.1, rfl⟩
    | bit0 p => exact il rep.2.1 get
    | bit1 p => exact ir rep.2.2 get

end Cslib.DataStructure.SearchTree.PointerMachine

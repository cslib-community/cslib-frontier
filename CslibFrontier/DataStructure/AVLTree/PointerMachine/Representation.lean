/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.Basic
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Height

/-!
# Linked representations of existing AVL trees

`Matches` couples a ghost-labelled linked tree to the existing `AVLTree`: both its keys
and its encoded cached heights agree, at every node. Heap contents remain governed by
`SearchTree.PointerMachine.Represents`; no second AVL tree type is introduced.

`recomputeHeight_mkNode` proves that the concrete nine-instruction height update implements
the cached-height constructor `AVLTree.mkNode`, preserving the matched children.
It requires consistent child heights but permits an arbitrary old root cache.

`Rebuilt` is the contract of a routine that rebuilds the subtree under the cursor in place;
the flat and the structured rebalancing programs both establish it.
-/

public section

namespace Cslib.DataStructure.AVLTree.PointerMachine

open Cslib.PointerMachine SearchTree.PointerMachine

variable {M : Model} {extra regs : ℕ}

/-- Same tree shape, scalar keys, and encoded cached heights at every node.
The height field must be distinct from key field zero when updating either independently. -/
@[expose] def Matches (encode : ℕ → M.Value) (field : Fin (extra + 1)) :
    BinaryTree (Label M extra) → AVLTree M.Value → Prop
  | .nil, .nil => True
  | .node label l r, .node key height left right =>
      label.data 0 = key ∧ label.data field = encode height ∧
        Matches encode field l left ∧ Matches encode field r right
  | _, _ => False

/-- A complete AVL match supplies the key-only representation used by search. -/
theorem Matches.keys {encode : ℕ → M.Value} {field : Fin (extra + 1)}
    {tree : BinaryTree (Label M extra)} {t : AVLTree M.Value}
    (h : Matches encode field tree t) : keys tree = t.toBinaryTree := by
  induction tree generalizing t with
  | nil =>
    cases t <;> simp_all [Matches, SearchTree.PointerMachine.keys, BinaryTree.map, toBinaryTree]
  | node label l r il ir =>
    cases t with
    | nil => cases h
    | node _ _ _ _ => exact h.1 ▸ congrArg₂ (BinaryTree.node _) (il h.2.2.1) (ir h.2.2.2)

/-- A full AVL match preserves the structural height of the underlying binary tree. -/
theorem Matches.shape_height {encode : ℕ → M.Value} {field : Fin (extra + 1)}
    {tree : BinaryTree (Label M extra)} {t : AVLTree M.Value}
    (h : Matches encode field tree t) : tree.height = t.toBinaryTree.height := by
  induction tree generalizing t with
  | nil => cases t <;> simp_all [Matches, BinaryTree.height, toBinaryTree]
  | node label l r il ir =>
    cases t with
    | nil => cases h
    | node _ _ _ _ => simp [BinaryTree.height, toBinaryTree, il h.2.2.1, ir h.2.2.2]

/-- A matched root cache is exactly the encoded AVL cached height, with zero for an empty tree. -/
theorem Matches.heightValue {encode : ℕ → M.Value} {field : Fin (extra + 1)}
    {tree : BinaryTree (Label M extra)} {t : AVLTree M.Value}
    (h : Matches encode field tree t) :
    heightValue (encode 0) field tree = encode t.cachedHeight := by
  cases tree <;> cases t <;> simp_all [Matches, SearchTree.PointerMachine.heightValue, cachedHeight]

/-- Nine actual instructions implement `mkNode`'s height recomputation on an existing
linked root. Its two children retain their complete AVL matches; only the root height
field and the declared scratch registers change. Allocation and rebalancing are separate. -/
theorem recomputeHeight_mkNode (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (x : State M (layout extra (regs + 1))) (label : Label M extra)
    (l r : BinaryTree (Label M extra)) (left right : AVLTree M.Value) (parent : Pointer)
    (rep : Represents x.heap parent (.node label l r))
    (distinct : AddressesDistinct (.node label l r))
    (ml : Matches encode field l left) (mr : Matches encode field r right)
    (hl : left.HeightConsistent) (hr : right.HeightConsistent)
    (cursor : x.ptr 0 = some label.address) (pc : x.pc = 0) :
    let value := encode (mkNode (label.data 0) left right).cachedHeight
    let tree := BinaryTree.node { label with data := Function.update label.data field value } l r
    ∃ y, Executes (recomputeHeight zero maxSucc field) x y 9 ∧
      y.heap = x.heap.modify label.address
        (fun n => { n with data := Function.update n.data field value }) ∧
      Represents y.heap parent tree ∧
      Matches encode field tree (mkNode (label.data 0) left right) ∧ AddressesDistinct tree ∧
      (∀ i, i ≠ 1 → i ≠ 2 → y.data i = x.data i) ∧
      (∀ i, i ≠ 2 → y.ptr i = x.ptr i) := by
  have lh : l.height = left.cachedHeight := ml.shape_height.trans (cachedHeight_eq_height hl).symm
  have rh : r.height = right.cachedHeight := mr.shape_height.trans (cachedHeight_eq_height hr).symm
  obtain ⟨y, exec, heap, rep', data, ptr⟩ := recomputeHeight_correct zero maxSucc encode
    zero_spec max_spec field x label l r parent rep
    (lh ▸ ml.heightValue) (rh ▸ mr.heightValue) cursor pc
  let value := encode (mkNode (label.data 0) left right).cachedHeight
  have keepL : updateData l label.address field value = l :=
    updateData_eq_self _ _ _ _ fun p u hp eq => nomatch distinct (.bit0 p) .one u label hp rfl eq
  have keepR : updateData r label.address field value = r :=
    updateData_eq_self _ _ _ _ fun p u hp eq => nomatch distinct (.bit1 p) .one u label hp rfl eq
  have shape : updateData (.node label l r) label.address field value =
      .node { label with data := Function.update label.data field value } l r := by
    simp only [updateData, BinaryTree.map, ↓reduceIte]
    exact congrArg₂ (BinaryTree.node _) keepL keepR
  have hval : encode (BinaryTree.node label l r).height = value := by
    simp [value, BinaryTree.height, lh, rh, Nat.add_comm]
  refine ⟨y, exec, ?_, ?_, ⟨?_, by simp, ml, mr⟩, shape ▸ distinct.updateData _ _ _, data, ptr⟩
  · simpa only [cachedHeight_mkNode, lh, rh, Nat.add_comm] using heap
  · simpa only [hval, shape] using rep'
  · simp [Ne.symm notKey]

/-- The subtree `old` under the cursor of `s` has been rebuilt in place as `tree`, which matches
`target`: it is represented under the same parent, occupies the same addresses, the cursor is at
its root, register six holds the former root, and the root register and every record outside
it are unchanged. -/
structure Rebuilt (encode : ℕ → M.Value) (field : Fin (extra + 1))
    (s t : State M (layout extra (regs + 1))) (parent : Pointer)
    (old tree : BinaryTree (Label M extra)) (target : AVLTree M.Value) : Prop where
  /-- The rebuilt subtree is represented under the same parent. -/
  rep : Represents t.heap parent tree
  /-- Its keys and height caches match the functional result. -/
  matched : Matches encode field tree target
  /-- Its addresses are distinct. -/
  distinct : AddressesDistinct tree
  /-- It occupies the addresses of the old subtree. -/
  footprint : addresses tree = addresses old
  /-- The cursor is at its root. -/
  cursor : t.ptr 0 = root tree
  /-- Register six holds the former root. -/
  saved : t.ptr 6 = s.ptr 0
  /-- The root register is unchanged. -/
  top : t.ptr 1 = s.ptr 1
  /-- No record outside the old subtree changed. -/
  frame : ∀ z, z ∉ addresses old → t.heap[z]? = s.heap[z]?

end Cslib.DataStructure.AVLTree.PointerMachine

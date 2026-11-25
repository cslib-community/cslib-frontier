/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Representation
public import CslibFrontier.DataStructure.AVLTree.Side
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Height
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Rotation

/-!
# Height-maintaining AVL rotation as a structured pointer-machine program

`Structured.rotate right` saves the old root, promotes its child on the selected side,
recomputes the old root's height, then follows its parent to recompute the promoted root's
height: 28 instructions. One program and one proof cover both rotations.

The result is stated as `Rebuilt`: the subtree under the cursor is again represented, matches
the functional result, keeps its addresses, and nothing outside it changed. What the program
does to registers is read off its text.

## Main definitions

* `rotate`: the rotation program.
* `Rebuilt`: a subtree rebuilt in place.

## Main results

* `recomputeHeight_mkNodeAt`: recomputing a cached height implements `mkNode`.
* `rotate_correct`: the rotation implements the functional rotation with its two cached-height
  updates.
* `matches_nodeAt`, `matches_nodeAt_mkNodeAt`: matching a node named by side.
-/

public section

namespace Cslib.DataStructure.AVLTree.PointerMachine.Structured

open Cslib.PointerMachine SearchTree.PointerMachine
open Cslib.Program (ExecWithin.seq)

variable {M : Model} {extra regs : ℕ}

/-- Eight instructions implement `mkNode`'s height recomputation on an existing
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
    (cursor : x.ptr 0 = some label.address) :
    let value := encode (mkNode (label.data 0) left right).cachedHeight
    let tree := BinaryTree.node { label with data := Function.update label.data field value } l r
    ∃ y, ExecWithin
        (SearchTree.PointerMachine.Structured.recomputeHeight zero maxSucc field) x y 8 ∧
      y.heap = x.heap.modify label.address
        (fun n => { n with data := Function.update n.data field value }) ∧
      Represents y.heap parent tree ∧
      Matches encode field tree (mkNode (label.data 0) left right) ∧ AddressesDistinct tree ∧
      (∀ i, i ≠ 1 → i ≠ 2 → y.data i = x.data i) ∧
      (∀ i, i ≠ 2 → y.ptr i = x.ptr i) := by
  have lh : l.height = left.cachedHeight :=
    (ml.shape_height).trans (cachedHeight_eq_height hl).symm
  have rh : r.height = right.cachedHeight :=
    (mr.shape_height).trans (cachedHeight_eq_height hr).symm
  obtain ⟨y, exec, heap, rep', data, ptr⟩ :=
    SearchTree.PointerMachine.Structured.recomputeHeight_correct zero maxSucc encode
      zero_spec max_spec field x label l r parent rep
    (by rw [lh]; exact ml.heightValue) (by rw [rh]; exact mr.heightValue) cursor
  let value := encode (mkNode (label.data 0) left right).cachedHeight
  have height : encode (BinaryTree.node label l r).height = value := by
    simp [value, BinaryTree.height, lh, rh, Nat.add_comm]
  have keepL : updateData l label.address field value = l :=
    updateData_eq_self _ _ _ _ fun p u hp eq => nomatch distinct (.bit0 p) .one u label hp rfl eq
  have keepR : updateData r label.address field value = r :=
    updateData_eq_self _ _ _ _ fun p u hp eq => nomatch distinct (.bit1 p) .one u label hp rfl eq
  have shape : updateData (.node label l r) label.address field value =
      .node { label with data := Function.update label.data field value } l r := by
    simp only [updateData, BinaryTree.map, ↓reduceIte]
    change BinaryTree.node _ (updateData l label.address field value)
      (updateData r label.address field value) = _
    rw [keepL, keepR]
  refine ⟨y, exec, ?_, ?_, ⟨by simp [Ne.symm notKey], by simp, ml, mr⟩,
    shape ▸ distinct.updateData _ _ _, data, ptr⟩
  · simpa only [cachedHeight_mkNode, lh, rh, Nat.add_comm] using heap
  · simpa only [height, shape] using rep'

/-- `recomputeHeight_mkNode`, with the children named by side. -/
theorem recomputeHeight_mkNodeAt (right : Bool) (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (x : State M (layout extra (regs + 1))) (label : Label M extra)
    (child sibling : BinaryTree (Label M extra)) (C S : AVLTree M.Value) (parent : Pointer)
    (rep : Represents x.heap parent (nodeAt right label child sibling))
    (distinct : AddressesDistinct (nodeAt right label child sibling))
    (mc : Matches encode field child C) (ms : Matches encode field sibling S)
    (hc : C.HeightConsistent) (hs : S.HeightConsistent)
    (cursor : x.ptr 0 = some label.address) :
    let value := encode (mkNodeAt right (label.data 0) C S).cachedHeight
    let tree := nodeAt right { label with data := Function.update label.data field value }
      child sibling
    ∃ y, ExecWithin
        (SearchTree.PointerMachine.Structured.recomputeHeight zero maxSucc field) x y 8 ∧
      y.heap = x.heap.modify label.address
        (fun n => { n with data := Function.update n.data field value }) ∧
      Represents y.heap parent tree ∧
      Matches encode field tree (mkNodeAt right (label.data 0) C S) ∧ AddressesDistinct tree := by
  cases right
  · exact (recomputeHeight_mkNode zero maxSucc encode zero_spec max_spec field notKey x label
      child sibling C S parent rep distinct mc ms hc hs cursor).imp
      fun _ ⟨r, e, p, m, d, _⟩ => ⟨r, e, p, m, d⟩
  · exact (recomputeHeight_mkNode zero maxSucc encode zero_spec max_spec field notKey x label
      sibling child S C parent rep distinct ms mc hs hc cursor).imp
      fun _ ⟨r, e, p, m, d, _⟩ => ⟨r, e, p, m, d⟩

/-- A node named by side matches a functional node named by the same side. -/
theorem matches_nodeAt {encode : ℕ → M.Value} {field : Fin (extra + 1)} {right : Bool}
    {label : Label M extra} {child sibling : BinaryTree (Label M extra)} {T : AVLTree M.Value}
    (m : Matches encode field (nodeAt right label child sibling) T) :
    ∃ h C S, T = nodeSide right (label.data 0) h C S ∧ label.data field = encode h ∧
      Matches encode field child C ∧ Matches encode field sibling S := by
  cases right <;> cases T with
  | nil => cases m
  | node key h l r =>
    obtain ⟨rfl, cache, ml, mr⟩ := m
    first | exact ⟨h, l, r, rfl, cache, ml, mr⟩ | exact ⟨h, r, l, rfl, cache, mr, ml⟩

/-- The parts of a match with `mkNodeAt`. -/
theorem matches_nodeAt_mkNodeAt {encode : ℕ → M.Value} {field : Fin (extra + 1)} {right : Bool}
    {label : Label M extra} {child sibling : BinaryTree (Label M extra)} {key : M.Value}
    {C S : AVLTree M.Value}
    (m : Matches encode field (nodeAt right label child sibling) (mkNodeAt right key C S)) :
    Matches encode field child C ∧ Matches encode field sibling S := by
  cases right
  exacts [⟨m.2.2.1, m.2.2.2⟩, ⟨m.2.2.2, m.2.2.1⟩]

open SearchTree.PointerMachine.Structured renaming rotate → rotateLinks,
  recomputeHeight → updateHeight in
open Register in
/-- Promote the child of the cursor on the selected side and repair both pivot heights, saving
the former root in register six. -/
@[expose] def rotate (right : Bool) (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    Code M (layout extra (regs + 1)) := pm[
  old ← cur;
  ⟪rotateLinks right⟫;
  cur ← old;
  ⟪updateHeight zero maxSucc field⟫;
  cur ← cur[parent];
  ⟪updateHeight zero maxSucc field⟫ ]

/-- The rotation implements the functional rotation's two cached-height updates in 28
instructions. The three untouched child trees need correct caches; the two pivot caches may
initially be arbitrary. External-parent reconnection is separate. -/
theorem rotate_correct (right : Bool) (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (x y : Label M extra)
    (a b c : BinaryTree (Label M extra)) (A B C : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (nodeAt right y (nodeAt right x a b) c))
    (distinct : AddressesDistinct (nodeAt right y (nodeAt right x a b) c))
    (ma : Matches encode field a A) (mb : Matches encode field b B)
    (mc : Matches encode field c C)
    (ha : A.HeightConsistent) (hb : B.HeightConsistent) (hc : C.HeightConsistent)
    (cursor : s.ptr 0 = some y.address) :
    ∃ t x' y', ExecWithin (rotate right zero maxSucc field) s t 28 ∧
      (x'.address = x.address ∧ x'.data 0 = x.data 0) ∧
      (y'.address = y.address ∧ y'.data 0 = y.data 0) ∧
      Rebuilt encode field s t parent (nodeAt right y (nodeAt right x a b) c)
        (nodeAt right x' a (nodeAt right y' b c))
        (mkNodeAt right (x.data 0) A (mkNodeAt right (y.data 0) B C)) := by
  obtain ⟨r, rot, rr, rc, rl, rf⟩ := SearchTree.PointerMachine.Structured.rotate_represents
    right (s.setPtr 6 (s.ptr 0)) x y a b c parent rep distinct cursor
  have r6 : r.ptr 6 = some y.address :=
    (rot.ptr_keep [0, 2, 3, 4] (by pm_frame) (by simp)).trans (by simp [cursor])
  obtain ⟨da, dY, xa, xY, aY⟩ := (nodeAt_distinct_iff ..).mp distinct.rotate
  -- Repair the height of the old root, now below the promoted node.
  obtain ⟨u, old, uh, ur, um, ud⟩ := recomputeHeight_mkNodeAt right zero maxSucc encode zero_spec
    max_spec field notKey (r.setPtr 0 (r.ptr 6)) y b c B C (some x.address)
    ((represents_nodeAt_iff ..).mp rr).2.2 dY mb mc hb hc (by simp [r6])
  simp only [State.heap_setPtr] at uh
  have ucur : u.ptr 0 = some y.address :=
    (old.ptr_keep [2] (by pm_frame) (by simp)).trans (by simp [r6])
  have ru := (nodeAt_not right x a _ ▸ rr).nodeAt_congr_child (!right) ur (by simp)
    (fun z hz => by
      rw [uh]
      exact List.getElem?_modify_ne _ _ fun e => hz (e ▸ by simp [nodeAt_addresses]))
    xY aY.symm
  rw [nodeAt_not] at ru
  have du := (nodeAt_distinct_iff right x a _).mpr ⟨da, ud, xa,
    by simpa [nodeAt_addresses] using xY,
    by simpa [nodeAt_addresses] using aY⟩
  -- Move back up to the promoted node and repair its height.
  have ascend : (Op.loadPtr 0 2 0).effect u = u.setPtr 0 (some x.address) := by
    have uy := ((represents_nodeAt_iff ..).mp ur).1
    simp [pm_simps, State.deref, ucur, uy, record]
  obtain ⟨v, new, vh, vr, vm, vd⟩ := recomputeHeight_mkNodeAt right zero maxSucc encode zero_spec
    max_spec field notKey (u.setPtr 0 (some x.address)) x a _ A _ parent ru du ma um ha
    (heightConsistent_mkNodeAt right hb hc) (by simp)
  simp only [State.heap_setPtr] at vh
  have kept (reg : Fin (layout extra (regs + 1)).ptrRegs)
      (hreg : reg ∉ [0, 2, 3, 4]) : v.ptr reg = (s.setPtr 6 (s.ptr 0)).ptr reg := by
    have notCursor : reg ≠ 0 := fun h => hreg (by simp [h])
    have notScratch : reg ∉ [2] := fun h => hreg (by simp_all)
    have hnew := new.ptr_keep [2] (by pm_frame) notScratch
    have hold := old.ptr_keep [2] (by pm_frame) notScratch
    have hrot := rot.ptr_keep [0, 2, 3, 4] (by pm_frame) hreg
    simpa [notCursor, hold, hrot] using hnew
  let x' : Label M extra := ⟨x.address, Function.update x.data field
    (encode (mkNodeAt right (x.data 0) A (mkNodeAt right (y.data 0) B C)).cachedHeight)⟩
  let y' : Label M extra := ⟨y.address, Function.update y.data field
    (encode (mkNodeAt right (y.data 0) B C).cachedHeight)⟩
  refine ⟨v, x', y', (ExecWithin.seq (ExecWithin.op_eq rfl) (ExecWithin.seq rot
    (ExecWithin.seq (ExecWithin.op_eq rfl) (ExecWithin.seq old
      (ExecWithin.seq (ExecWithin.op_eq ascend) new))))).mono (by omega),
    ⟨rfl, Function.update_of_ne (Ne.symm notKey) ..⟩,
    ⟨rfl, Function.update_of_ne (Ne.symm notKey) ..⟩,
    ⟨vr, vm, vd, ?_, ?_, ?_, ?_, fun z hz => ?_⟩⟩
  · simp [x', y', nodeAt_addresses, Finset.insert_comm, Finset.union_assoc]
  · exact (new.ptr_keep [2] (by pm_frame) (by simp)).trans (by simp [x'])
  · exact kept 6 (by simp)
  · simpa using kept 1 (by simp)
  · simp only [nodeAt_addresses, Finset.mem_insert, Finset.mem_union, not_or] at hz
    rw [vh, List.getElem?_modify_ne _ _ (Ne.symm hz.2.1.1), uh,
      List.getElem?_modify_ne _ _ (Ne.symm hz.1)]
    exact rf z hz.2.1.1 hz.1 fun e => hz.2.1.2.2 (root_mem_addresses e)

/-! Frames of `rotate`, for the programs that call it. -/

@[simp] theorem rotate_keepsSize (right : Bool) (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    (rotate (regs := regs) right zero maxSucc field).KeepsSize := by
  simp [rotate, Op.creates]

theorem rotate_dataDests (right : Bool) (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    (rotate (regs := regs) right zero maxSucc field).dataDests ⊆ [1, 2] := by
  simp [rotate, Op.dataDest]

@[simp] theorem rotate_fieldDests (right : Bool) (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    (rotate (regs := regs) right zero maxSucc field).fieldDests = [field, field] := by
  simp [rotate, Op.fieldDest]

end Cslib.DataStructure.AVLTree.PointerMachine.Structured

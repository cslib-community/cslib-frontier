/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Representation
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Rotation
public import CslibFrontier.Computability.PointerMachine.Blocks

/-!
# Height-maintaining pointer-machine AVL rotation

A concrete program saves the old root, rotates links, recomputes the old root's height,
then follows its parent to recompute the promoted root's height. All primitive blocks
are relocated into one finite program, including their charged continuation jumps.
The external parent's child link is left for the caller to reconnect.
-/

public section
namespace Cslib.DataStructure.AVLTree.PointerMachine
open Cslib.PointerMachine SearchTree.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Wrap a pointer rotation with saving its former root and repairing both pivot heights.
The supplied block must leave the former root's parent pointing to the promoted root.
The certified entry points below supply the concrete left and right rotations. -/
@[expose] def rotationProgram (rotation : List (Instr M (layout extra (regs + 1))))
    (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    List (Instr M (layout extra (regs + 1))) :=
  sequence [.movePtr 6 0, .halt] (sequence rotation
    (sequence [.movePtr 0 6, .halt] (sequence (recomputeHeight zero maxSucc field)
      (sequence [.loadPtr 0 2 0, .halt] (recomputeHeight zero maxSucc field)))))

/-- Right subtree rotation followed by bottom-up recomputation of both pivot heights.
Data temporaries one/two and pointer registers zero/two/three/four/six may change. -/
@[expose] def rotateRight (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    List (Instr M (layout extra (regs + 1))) :=
  rotationProgram SearchTree.PointerMachine.rotateRight zero maxSucc field

/-- Left subtree rotation followed by bottom-up recomputation of both pivot heights.
Data temporaries one/two and pointer registers zero/two/three/four/six may change. -/
@[expose] def rotateLeft (zero maxSucc : M.Op) (field : Fin (extra + 1)) :
    List (Instr M (layout extra (regs + 1))) :=
  rotationProgram SearchTree.PointerMachine.rotateLeft zero maxSucc field

private theorem assemble_executes
    (rotation : List (Instr M (layout extra (regs + 1)))) (size : rotation.length = 10)
    (zero maxSucc : M.Op) (field : Fin (extra + 1))
    (s r u v : State M (layout extra (regs + 1))) (pc : s.pc = 0)
    (rot : Executes rotation { s.setPtr 6 (s.ptr 0) with pc := 0 } r 10)
    (old : Executes (recomputeHeight zero maxSucc field) { r.setPtr 0 (r.ptr 6) with pc := 0 } u 9)
    (parent : Pointer) (read : (u.deref 0).map (fun n => n.ptr 2) = some parent)
    (new : Executes (recomputeHeight zero maxSucc field) { u.setPtr 0 parent with pc := 0 } v 9) :
    Executes (rotationProgram rotation zero maxSucc field) s { v with pc := 38 } 39 := by
  have save : Executes [.movePtr 6 0, .halt] s { s.setPtr 6 (s.ptr 0) with pc := 1 } 2 :=
    ⟨1, .single (by simp [step, pc, Instr.effect, Instr.next]), rfl, rfl⟩
  have move : Executes [.movePtr 0 6, .halt] { r with pc := 0 }
      { r.setPtr 0 (r.ptr 6) with pc := 1 } 2 :=
    ⟨1, .single (by simp [step, Instr.effect, Instr.next, State.setPtr]), rfl, rfl⟩
  have load : Executes [.loadPtr 0 2 0, .halt] { u with pc := 0 }
      { u.setPtr 0 parent with pc := 1 } 2 := by
    obtain ⟨node, hn, hp⟩ := Option.map_eq_some_iff.mp read
    refine ⟨1, .single ?_, rfl, rfl⟩
    change (u.ptr 0).bind (u.heap[·]?) = some node at hn
    simp [step, Instr.effect, Instr.next, State.deref, hn, hp, State.setPtr]
  have result := save.sequence (rot.sequence (move.sequence (old.sequence (load.sequence new))))
  simpa only [rotationProgram, Cslib.PointerMachine.sequence, List.length_append, List.length_map,
    List.length_cons,
    List.length_nil, recomputeHeight, readHeightsPrefix, size] using result

private theorem repair_frame
    (s r u v : State M (layout extra (regs + 1))) (oldAddr newAddr : ℕ) (middle : Pointer)
    (oldChange newChange : Record M (layout extra (regs + 1)) →
      Record M (layout extra (regs + 1)))
    (rl : r.heap.length = s.heap.length) (rd : r.data = s.data)
    (rp : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 →
      r.ptr i = Function.update s.ptr 6 (s.ptr 0) i)
    (rf : ∀ z, z ≠ newAddr → z ≠ oldAddr → middle ≠ some z → r.heap[z]? = s.heap[z]?)
    (uh : u.heap = r.heap.modify oldAddr oldChange)
    (ud : ∀ i, i ≠ 1 → i ≠ 2 → u.data i = r.data i)
    (up : ∀ i, i ≠ 2 → u.ptr i = Function.update r.ptr 0 (r.ptr 6) i)
    (vh : v.heap = u.heap.modify newAddr newChange)
    (vd : ∀ i, i ≠ 1 → i ≠ 2 → v.data i = u.data i)
    (vp : ∀ i, i ≠ 2 → v.ptr i = Function.update u.ptr 0 (some newAddr) i) :
    v.ptr 0 = some newAddr ∧ v.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → v.data i = s.data i) ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 6 → v.ptr i = s.ptr i) ∧
      v.ptr 6 = s.ptr 0 ∧
      (∀ z, z ≠ newAddr → z ≠ oldAddr → middle ≠ some z → v.heap[z]? = s.heap[z]?) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.update_self] using vp 0 (by simp [layout])
  · simpa only [vh, uh, List.length_modify] using rl
  · intro i h1 h2
    rw [vd i h1 h2, ud i h1 h2, rd]
  · intro i h0 h2 h3 h4 h6
    rw [vp i h2, Function.update_of_ne h0, up i h2, Function.update_of_ne h0,
      rp i h0 h2 h3 h4, Function.update_of_ne h6]
  · rw [vp 6 (by simp [layout]), Function.update_of_ne (by simp [layout]),
      up 6 (by simp [layout]), Function.update_of_ne (by simp [layout]),
      rp 6 (by simp [layout]) (by simp [layout]) (by simp [layout]) (by simp [layout]),
      Function.update_self]
  · intro z hn ho hm
    rw [vh, List.getElem?_modify_ne _ _ hn.symm, uh, List.getElem?_modify_ne _ _ ho.symm]
    exact rf z hn ho hm

/-- A concrete right rotation implements the existing AVL rotation's two cached-height
updates in 39 instructions. The three untouched child trees need correct caches;
the two pivot caches may initially be arbitrary. External-parent reconnection is separate. -/
theorem rotateRight_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (x y : Label M extra)
    (a b c : BinaryTree (Label M extra)) (A B C : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (.node y (.node x a b) c))
    (distinct : AddressesDistinct (.node y (.node x a b) c))
    (ma : Matches encode field a A) (mb : Matches encode field b B)
    (mc : Matches encode field c C)
    (ha : A.HeightConsistent) (hb : B.HeightConsistent) (hc : C.HeightConsistent)
    (cursor : s.ptr 0 = some y.address) (pc : s.pc = 0) :
    let oldHeight := encode (mkNode (y.data 0) B C).cachedHeight
    let newHeight := encode (mkNode (x.data 0) A (mkNode (y.data 0) B C)).cachedHeight
    let y' : Label M extra := { y with data := Function.update y.data field oldHeight }
    let x' : Label M extra := { x with data := Function.update x.data field newHeight }
    let tree := BinaryTree.node x' a (.node y' b c)
    ∃ t, Executes (rotateRight zero maxSucc field) s t 39 ∧
      Represents t.heap parent tree ∧
      Matches encode field tree (AVLTree.rotateRight (y.data 0) (mkNode (x.data 0) A B) C) ∧
      AddressesDistinct tree ∧ root tree = some x.address ∧ t.ptr 0 = root tree ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 6 → t.ptr i = s.ptr i) ∧
      t.ptr 6 = s.ptr 0 ∧
      (∀ z, z ≠ x.address → z ≠ y.address → root b ≠ some z →
        t.heap[z]? = s.heap[z]?) := by
  let saved : State M (layout extra (regs + 1)) := { s.setPtr 6 (s.ptr 0) with pc := 0 }
  obtain ⟨r, rot, rr, rc, rd, rl, rp, rf⟩ :=
    SearchTree.PointerMachine.rotateRight_represents saved x y a b c parent rep distinct
      (by simpa [saved, State.setPtr] using cursor) rfl
  have dRot := distinct.rotateRight
  have dOld : AddressesDistinct (.node y b c) := by
    intro p q u v hp hq eq
    exact PosNum.bit1.inj (dRot (.bit1 p) (.bit1 q) u v hp hq eq)
  have savedOld : r.ptr 6 = some y.address := by
    rw [rp 6 (by change (6 : Fin 7) ≠ 0; decide) (by change (6 : Fin 7) ≠ 2; decide)
      (by change (6 : Fin 7) ≠ 3; decide) (by change (6 : Fin 7) ≠ 4; decide)]
    simp [saved, State.setPtr, cursor]
  let oldStart : State M (layout extra (regs + 1)) :=
    { r.setPtr 0 (r.ptr 6) with pc := 0 }
  obtain ⟨u, old, uh, ur, um, _, ud, up⟩ := recomputeHeight_mkNode zero maxSucc encode
    zero_spec max_spec field notKey oldStart y b c B C (some x.address) rr.2.2 dOld mb mc hb hc
    (by simp [oldStart, State.setPtr, savedOld]) rfl
  let value := encode (mkNode (y.data 0) B C).cachedHeight
  let y' : Label M extra := { y with data := Function.update y.data field value }
  have xy : x.address ≠ y.address := by
    intro eq
    have bad := dRot .one (.bit1 .one) x y rfl rfl eq
    cases bad
  have keepA : updateData a y.address field value = a := by
    apply updateData_eq_self
    intro p z hz eq
    have bad := dRot (.bit0 p) (.bit1 .one) z y hz rfl eq
    cases bad
  have keepB : updateData b y.address field value = b := by
    apply updateData_eq_self
    intro p z hz eq
    have bad := dOld (.bit0 p) .one z y hz rfl eq
    cases bad
  have keepC : updateData c y.address field value = c := by
    apply updateData_eq_self
    intro p z hz eq
    have bad := dOld (.bit1 p) .one z y hz rfl eq
    cases bad
  have shape : updateData (.node x a (.node y b c)) y.address field value =
      .node x a (.node y' b c) := by
    change BinaryTree.node { x with data :=
      if x.address = y.address then Function.update x.data field value else x.data }
      (updateData a y.address field value)
      (.node { y with data :=
        if y.address = y.address then Function.update y.data field value else y.data }
        (updateData b y.address field value) (updateData c y.address field value)) = _
    rw [keepA, keepB, keepC]
    simp [xy, y']
  have ru : Represents u.heap parent (.node x a (.node y' b c)) := by
    rw [uh]
    simpa only [oldStart, State.setPtr, shape] using rr.updateData y.address field value
  have du : AddressesDistinct (.node x a (.node y' b c)) := by
    rw [← shape]
    exact dRot.updateData _ _ _
  have ucur : u.ptr 0 = some y.address := by
    rw [up 0 (by change (0 : Fin 7) ≠ 2; decide)]
    simp [oldStart, State.setPtr, savedOld]
  have read : (u.deref 0).map (fun n => n.ptr 2) = some (some x.address) := by
    simp [State.deref, ucur, ur.1, record]
  let newStart : State M (layout extra (regs + 1)) :=
    { u.setPtr 0 (some x.address) with pc := 0 }
  obtain ⟨v, new, vh, vr, vm, vd, vdata, vp⟩ := recomputeHeight_mkNode zero maxSucc encode
    zero_spec max_spec field notKey newStart x a (.node y' b c) A (mkNode (y.data 0) B C)
    parent ru du ma um ha (heightConsistent_mkNode hb hc)
    (by simp [newStart, State.setPtr]) rfl
  have frame := repair_frame s r u v y.address x.address (root b) _ _
    rl rd rp rf uh ud up vh vdata vp
  refine ⟨{ v with pc := 38 }, ?_, vr, vm, vd, rfl, frame⟩
  exact assemble_executes SearchTree.PointerMachine.rotateRight rfl zero maxSucc field
    s r u v pc rot old (some x.address) read new

/-- A concrete left rotation implements the existing AVL rotation's two cached-height
updates in 39 instructions. The three untouched child trees need correct caches;
the two pivot caches may initially be arbitrary. External-parent reconnection is separate. -/
theorem rotateLeft_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (x y : Label M extra)
    (a b c : BinaryTree (Label M extra)) (A B C : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (.node y a (.node x b c)))
    (distinct : AddressesDistinct (.node y a (.node x b c)))
    (ma : Matches encode field a A) (mb : Matches encode field b B)
    (mc : Matches encode field c C)
    (ha : A.HeightConsistent) (hb : B.HeightConsistent) (hc : C.HeightConsistent)
    (cursor : s.ptr 0 = some y.address) (pc : s.pc = 0) :
    let oldHeight := encode (mkNode (y.data 0) A B).cachedHeight
    let newHeight := encode (mkNode (x.data 0) (mkNode (y.data 0) A B) C).cachedHeight
    let y' : Label M extra := { y with data := Function.update y.data field oldHeight }
    let x' : Label M extra := { x with data := Function.update x.data field newHeight }
    let tree := BinaryTree.node x' (.node y' a b) c
    ∃ t, Executes (rotateLeft zero maxSucc field) s t 39 ∧
      Represents t.heap parent tree ∧
      Matches encode field tree (AVLTree.rotateLeft (y.data 0) A (mkNode (x.data 0) B C)) ∧
      AddressesDistinct tree ∧ root tree = some x.address ∧ t.ptr 0 = root tree ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 6 → t.ptr i = s.ptr i) ∧
      t.ptr 6 = s.ptr 0 ∧
      (∀ z, z ≠ x.address → z ≠ y.address → root b ≠ some z →
        t.heap[z]? = s.heap[z]?) := by
  let saved : State M (layout extra (regs + 1)) := { s.setPtr 6 (s.ptr 0) with pc := 0 }
  obtain ⟨r, rot, rr, rc, rd, rl, rp, rf⟩ :=
    SearchTree.PointerMachine.rotateLeft_represents saved x y a b c parent rep distinct
      (by simpa [saved, State.setPtr] using cursor) rfl
  have dRot := distinct.rotateLeft
  have dOld : AddressesDistinct (.node y a b) := by
    intro p q u v hp hq eq
    exact PosNum.bit0.inj (dRot (.bit0 p) (.bit0 q) u v hp hq eq)
  have savedOld : r.ptr 6 = some y.address := by
    rw [rp 6 (by change (6 : Fin 7) ≠ 0; decide) (by change (6 : Fin 7) ≠ 2; decide)
      (by change (6 : Fin 7) ≠ 3; decide) (by change (6 : Fin 7) ≠ 4; decide)]
    simp [saved, State.setPtr, cursor]
  let oldStart : State M (layout extra (regs + 1)) :=
    { r.setPtr 0 (r.ptr 6) with pc := 0 }
  obtain ⟨u, old, uh, ur, um, _, ud, up⟩ := recomputeHeight_mkNode zero maxSucc encode
    zero_spec max_spec field notKey oldStart y a b A B (some x.address) rr.2.1 dOld ma mb ha hb
    (by simp [oldStart, State.setPtr, savedOld]) rfl
  let value := encode (mkNode (y.data 0) A B).cachedHeight
  let y' : Label M extra := { y with data := Function.update y.data field value }
  have xy : x.address ≠ y.address := by
    intro eq
    have bad := dRot .one (.bit0 .one) x y rfl rfl eq
    cases bad
  have keepA : updateData a y.address field value = a := by
    apply updateData_eq_self
    intro p z hz eq
    have bad := dOld (.bit0 p) .one z y hz rfl eq
    cases bad
  have keepB : updateData b y.address field value = b := by
    apply updateData_eq_self
    intro p z hz eq
    have bad := dOld (.bit1 p) .one z y hz rfl eq
    cases bad
  have keepC : updateData c y.address field value = c := by
    apply updateData_eq_self
    intro p z hz eq
    have bad := dRot (.bit1 p) (.bit0 .one) z y hz rfl eq
    cases bad
  have shape : updateData (.node x (.node y a b) c) y.address field value =
      .node x (.node y' a b) c := by
    change BinaryTree.node { x with data :=
      if x.address = y.address then Function.update x.data field value else x.data }
      (.node { y with data :=
        if y.address = y.address then Function.update y.data field value else y.data }
        (updateData a y.address field value) (updateData b y.address field value))
      (updateData c y.address field value) = _
    rw [keepA, keepB, keepC]
    simp [xy, y']
  have ru : Represents u.heap parent (.node x (.node y' a b) c) := by
    rw [uh]
    simpa only [oldStart, State.setPtr, shape] using rr.updateData y.address field value
  have du : AddressesDistinct (.node x (.node y' a b) c) := by
    rw [← shape]
    exact dRot.updateData _ _ _
  have ucur : u.ptr 0 = some y.address := by
    rw [up 0 (by change (0 : Fin 7) ≠ 2; decide)]
    simp [oldStart, State.setPtr, savedOld]
  have read : (u.deref 0).map (fun n => n.ptr 2) = some (some x.address) := by
    simp [State.deref, ucur, ur.1, record]
  let newStart : State M (layout extra (regs + 1)) :=
    { u.setPtr 0 (some x.address) with pc := 0 }
  obtain ⟨v, new, vh, vr, vm, vd, vdata, vp⟩ := recomputeHeight_mkNode zero maxSucc encode
    zero_spec max_spec field notKey newStart x (.node y' a b) c (mkNode (y.data 0) A B) C
    parent ru du um mc (heightConsistent_mkNode ha hb) hc
    (by simp [newStart, State.setPtr]) rfl
  have frame := repair_frame s r u v y.address x.address (root b) _ _
    rl rd rp rf uh ud up vh vdata vp
  refine ⟨{ v with pc := 38 }, ?_, vr, vm, vd, rfl, frame⟩
  exact assemble_executes SearchTree.PointerMachine.rotateLeft rfl zero maxSucc field
    s r u v pc rot old (some x.address) read new


end Cslib.DataStructure.AVLTree.PointerMachine

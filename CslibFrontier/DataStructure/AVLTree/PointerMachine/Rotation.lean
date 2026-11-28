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
import CslibFrontier.DataStructure.AVLTree.Side

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
    List.length_cons, List.length_nil, recomputeHeight, readHeightsPrefix, size] using result

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
  refine ⟨by simpa only [Function.update_self] using vp 0 (by simp [layout]),
    by simpa only [vh, uh, List.length_modify] using rl,
    fun i h1 h2 => by rw [vd i h1 h2, ud i h1 h2, rd], fun i h0 h2 h3 h4 h6 => ?_, ?_,
    fun z hn ho hm => ?_⟩
  · rw [vp i h2, Function.update_of_ne h0, up i h2, Function.update_of_ne h0,
      rp i h0 h2 h3 h4, Function.update_of_ne h6]
  · rw [vp 6 (by simp [layout]), Function.update_of_ne (by simp [layout]),
      up 6 (by simp [layout]), Function.update_of_ne (by simp [layout]),
      rp 6 (by simp [layout]) (by simp [layout]) (by simp [layout]) (by simp [layout]),
      Function.update_self]
  · rw [vh, List.getElem?_modify_ne _ _ hn.symm, uh, List.getElem?_modify_ne _ _ ho.symm]
    exact rf z hn ho hm

private theorem recomputeHeight_mkNodeAt (right : Bool) (zero maxSucc : M.Op)
    (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label : Label M extra)
    (child sibling : BinaryTree (Label M extra)) (C S : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (nodeAt right label child sibling))
    (distinct : AddressesDistinct (nodeAt right label child sibling))
    (mc : Matches encode field child C) (ms : Matches encode field sibling S)
    (hc : C.HeightConsistent) (hs : S.HeightConsistent)
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    let value := encode (mkNodeAt right (label.data 0) C S).cachedHeight
    let tree := nodeAt right { label with data := Function.update label.data field value }
      child sibling
    ∃ y, Executes (recomputeHeight zero maxSucc field) s y 9 ∧
      y.heap = s.heap.modify label.address
        (fun n => { n with data := Function.update n.data field value }) ∧
      Represents y.heap parent tree ∧
      Matches encode field tree (mkNodeAt right (label.data 0) C S) ∧ AddressesDistinct tree ∧
      (∀ i, i ≠ 1 → i ≠ 2 → y.data i = s.data i) ∧
      (∀ i, i ≠ 2 → y.ptr i = s.ptr i) := by
  cases right
  · exact recomputeHeight_mkNode zero maxSucc encode zero_spec max_spec field notKey s label
      child sibling C S parent rep distinct mc ms hc hs cursor pc
  · exact recomputeHeight_mkNode zero maxSucc encode zero_spec max_spec field notKey s label
      sibling child S C parent rep distinct ms mc hs hc cursor pc

private theorem rotate_correct (right : Bool) (zero maxSucc : M.Op) (encode : ℕ → M.Value)
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
    (cursor : s.ptr 0 = some y.address) (pc : s.pc = 0) :
    let rotProg := if right then SearchTree.PointerMachine.rotateLeft
      else SearchTree.PointerMachine.rotateRight
    let oldHeight := encode (mkNodeAt right (y.data 0) B C).cachedHeight
    let newHeight := encode
      (mkNodeAt right (x.data 0) A (mkNodeAt right (y.data 0) B C)).cachedHeight
    let y' : Label M extra := { y with data := Function.update y.data field oldHeight }
    let x' : Label M extra := { x with data := Function.update x.data field newHeight }
    let tree := nodeAt right x' a (nodeAt right y' b c)
    ∃ t, Executes (rotationProgram rotProg zero maxSucc field) s t 39 ∧
      Represents t.heap parent tree ∧
      Matches encode field tree (mkNodeAt right (x.data 0) A (mkNodeAt right (y.data 0) B C)) ∧
      AddressesDistinct tree ∧ root tree = some x.address ∧ t.ptr 0 = root tree ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 6 → t.ptr i = s.ptr i) ∧
      t.ptr 6 = s.ptr 0 ∧
      (∀ z, z ≠ x.address → z ≠ y.address → root b ≠ some z →
        t.heap[z]? = s.heap[z]?) := by
  let saved : State M (layout extra (regs + 1)) := { s.setPtr 6 (s.ptr 0) with pc := 0 }
  let rotProg := if right then SearchTree.PointerMachine.rotateLeft (M := M) (extra := extra)
    (regs := regs + 1) else SearchTree.PointerMachine.rotateRight
  have hcur : saved.ptr 0 = some y.address := by simpa [saved, State.setPtr] using cursor
  have ⟨r, rot, rr, _, rd, rl, rp, rf⟩ :
      ∃ r, Executes rotProg saved r 10 ∧
        Represents r.heap parent (nodeAt right x a (nodeAt right y b c)) ∧
        r.ptr 0 = some x.address ∧ r.data = saved.data ∧ r.heap.length = saved.heap.length ∧
        (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → r.ptr i = saved.ptr i) ∧
        (∀ z, z ≠ x.address → z ≠ y.address → root b ≠ some z →
          r.heap[z]? = saved.heap[z]?) := by
    cases right
    · exact SearchTree.PointerMachine.rotateRight_represents saved x y a b c parent
        rep distinct hcur rfl
    · exact SearchTree.PointerMachine.rotateLeft_represents saved x y c b a parent
        rep distinct hcur rfl
  obtain ⟨da, dY, xa, xY, aY⟩ := (nodeAt_distinct_iff ..).mp (distinct.rotate right)
  have savedOld : r.ptr 6 = some y.address := by
    rw [rp 6 (by simp [layout]) (by simp [layout]) (by simp [layout]) (by simp [layout])]
    simp [saved, State.setPtr, cursor]
  let oldStart : State M (layout extra (regs + 1)) := { r.setPtr 0 (r.ptr 6) with pc := 0 }
  obtain ⟨u, old, uh, ur, um, ud', ud, up⟩ := recomputeHeight_mkNodeAt right zero maxSucc encode
    zero_spec max_spec field notKey oldStart y b c B C (some x.address)
    ((represents_nodeAt_iff ..).mp rr).2.2 dY mb mc hb hc
    (by simp [oldStart, State.setPtr, savedOld]) rfl
  have ru := (nodeAt_not right x a _ ▸ rr).nodeAt_congr_child (!right) ur (by simp)
    (fun z hz => by
      rw [uh]
      exact List.getElem?_modify_ne _ _ fun e => hz (e ▸ by simp [nodeAt_addresses]))
    xY aY.symm
  rw [nodeAt_not] at ru
  have du := (nodeAt_distinct_iff right x a _).mpr ⟨da, ud', xa,
    by simpa [nodeAt_addresses] using xY, by simpa [nodeAt_addresses] using aY⟩
  have ucur : u.ptr 0 = some y.address := by
    rw [up 0 (by simp [layout])]
    simp [oldStart, State.setPtr, savedOld]
  have read : (u.deref 0).map (fun n => n.ptr 2) = some (some x.address) := by
    simp [State.deref, ucur, ((represents_nodeAt_iff ..).mp ur).1, record]
  let newStart : State M (layout extra (regs + 1)) := { u.setPtr 0 (some x.address) with pc := 0 }
  obtain ⟨v, new, vh, vr, vm, vd, vdata, vp⟩ := recomputeHeight_mkNodeAt right zero maxSucc encode
    zero_spec max_spec field notKey newStart x a _ A _ parent ru du ma um ha
    (heightConsistent_mkNodeAt right hb hc) (by simp [newStart, State.setPtr]) rfl
  have frame := repair_frame s r u v y.address x.address (root b) _ _
    rl rd rp rf uh ud up vh vdata vp
  refine ⟨{ v with pc := 38 }, ?_, vr, vm, vd, root_nodeAt .., ?_⟩
  · exact assemble_executes rotProg (by cases right <;> rfl) zero maxSucc field
      s r u v pc rot old (some x.address) read new
  · simpa only [root_nodeAt] using frame

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
        t.heap[z]? = s.heap[z]?) :=
  rotate_correct false zero maxSucc encode zero_spec max_spec field notKey
    s x y a b c A B C parent rep distinct ma mb mc ha hb hc cursor pc

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
        t.heap[z]? = s.heap[z]?) :=
  rotate_correct true zero maxSucc encode zero_spec max_spec field notKey
    s x y c b a C B A parent rep distinct mc mb ma hc hb ha cursor pc

end Cslib.DataStructure.AVLTree.PointerMachine

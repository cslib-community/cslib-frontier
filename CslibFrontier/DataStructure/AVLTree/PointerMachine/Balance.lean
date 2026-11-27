/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Rotation
public import CslibFrontier.Computability.PointerMachine.Blocks
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Reconnect
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Child

/-!
# Pointer-machine AVL balancing

`balance_correct` proves that a finite pointer-machine program implements the existing
`AVLTree.balance` in at most 121 instructions. It permits an arbitrary old root cache and
requires height-consistent represented children. The implementation allocates no nodes;
it preserves every scalar payload field except the height, and all records outside the tree.

`Balance.readHeights`, `Balance.inChild`, and `Balance.heavyCase` give the shared assembly
blocks for cached-height selection, child reconnection, and single/double rotations.
-/

public section

namespace Cslib.DataStructure.AVLTree.PointerMachine

open Cslib.PointerMachine SearchTree.PointerMachine

variable {M : Model} {extra regs : ℕ}

/-- Read the two cached child heights into scalar registers one and two. -/
@[expose] def Balance.readHeights (zero : M.Op) (field : Fin (extra + 1)) (base : Fin 7) :
    List (Instr M (layout extra (regs + 1))) :=
  readHeightsPrefix zero field base ++ [.halt]

private theorem readHeights_correct (zero : M.Op) (z : M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = z)
    (field : Fin (extra + 1)) (base : Fin 7) (scratch : base ≠ 2)
    (s : State M (layout extra (regs + 1))) (label : Label M extra)
    (l r : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents s.heap parent (.node label l r))
    (cursor : s.ptr base = some label.address) (pc : s.pc = 0) :
    ∃ t, Executes (Balance.readHeights zero field base) s t 7 ∧ t.heap = s.heap ∧
      t.data 1 = heightValue z field l ∧ t.data 2 = heightValue z field r ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ i, i ≠ 2 → t.ptr i = s.ptr i) := by
  obtain ⟨t, run, tpc, heap, dl, dr, data, ptr⟩ := readHeightsPrefix_runs zero z zero_spec
    field base scratch [.halt] s label l r parent rep cursor pc
  exact ⟨t, ⟨6, run, by simp [Balance.readHeights, readHeightsPrefix, tpc], rfl⟩,
    heap, dl, dr, data, ptr⟩



/-- Run a child-subtree block, reconnect its result, then return to the original parent. -/
@[expose] def Balance.inChild (right : Bool) (body : List (Instr M (layout extra (regs + 1)))) :
    List (Instr M (layout extra (regs + 1))) :=
  sequence [.loadPtr 0 (if right then 1 else 0) 0, .halt]
    (sequence body (sequence reconnect [.loadPtr 0 2 0, .halt]))


private theorem inChild_correct (side : Bool)
    (body : List (Instr M (layout extra (regs + 1))))
    (s t : State M (layout extra (regs + 1))) (label oldLabel newLabel : Label M extra)
    (a b c d sibling : BinaryTree (Label M extra)) (parent : Pointer) (time : ℕ)
    (rep : Represents s.heap parent (nodeAt side label (.node oldLabel a b) sibling))
    (distinct : AddressesDistinct (nodeAt side label (.node oldLabel a b) sibling))
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0)
    (bodyExec : Executes body { s.setPtr 0 (some oldLabel.address) with pc := 0 } t time)
    (newRep : Represents t.heap (some label.address) (.node newLabel c d))
    (newDistinct : AddressesDistinct (.node newLabel c d))
    (sameAddresses : addresses (.node newLabel c d) = addresses (.node oldLabel a b))
    (newCursor : t.ptr 0 = some newLabel.address) (saved : t.ptr 6 = some oldLabel.address)
    (rootReg : t.ptr 1 = s.ptr 1)
    (frame : ∀ z, z ∉ addresses (.node oldLabel a b) → t.heap[z]? = s.heap[z]?) :
    ∃ u, Executes (Balance.inChild side body) s u (time + 14) ∧
      Represents u.heap parent (nodeAt side label (.node newLabel c d) sibling) ∧
      AddressesDistinct (nodeAt side label (.node newLabel c d) sibling) ∧
      u.ptr 0 = some label.address ∧ u.ptr 1 = s.ptr 1 ∧ u.data = t.data ∧
      u.heap.length = t.heap.length ∧
      (∀ z, z ∉ addresses (nodeAt side label (.node oldLabel a b) sibling) →
        u.heap[z]? = s.heap[z]?) := by
  let par : Record M (layout extra (regs + 1)) :=
    record (if side then root sibling else some oldLabel.address)
      (if side then some oldLabel.address else root sibling) parent label
  have lookup : s.heap[label.address]? = some par := by
    cases side <;> exact rep.1
  obtain ⟨_, _, no, _, dis⟩ := (nodeAt_distinct_iff ..).mp distinct
  have siblingNe : root sibling ≠ some oldLabel.address := by
    cases sibling with
    | nil => simp [root]
    | node u l r =>
      intro eq
      have same : u.address = oldLabel.address := Option.some.inj eq
      apply Finset.disjoint_left.mp dis
      · exact (mem_addresses_iff ..).mpr ⟨.one, oldLabel, rfl, rfl⟩
      · exact (mem_addresses_iff ..).mpr ⟨.one, u, rfl, same⟩
  have nav : Executes [.loadPtr 0 (if side then 1 else 0) 0, .halt] s
      { s.setPtr 0 (some oldLabel.address) with pc := 1 } 2 := by
    refine ⟨1, .single ?_, rfl, rfl⟩
    cases side <;>
      simp [step, pc, Instr.effect, Instr.next, State.deref, cursor, lookup, par, record]
  let restart : State M (layout extra (regs + 1)) := { t with pc := 0 }
  have read : restart.deref 0 =
      some (record (root c) (root d) (some label.address) newLabel) := by
    simp [restart, State.deref, newCursor, newRep.1]
  obtain ⟨u, field, connected, fields, oldLink, heap, data, ptr⟩ := reconnect_child restart
    (record (root c) (root d) (some label.address) newLabel) par label.address rfl read
    rfl ((frame _ no).trans lookup) (by cases side <;> simp [par, record, restart, saved])
  have fieldEq : field = if side then 1 else 0 := by
    rcases fields with rfl | rfl <;> cases side
    all_goals first
      | rfl
      | exact (siblingNe (by simpa [par, record, restart, saved] using oldLink)).elim
  have semantic := replaceChild side s.heap t.heap label (.node oldLabel a b)
    (.node newLabel c d) sibling parent rep distinct newRep newDistinct
    (by simpa only [sameAddresses] using no)
    (by simpa only [sameAddresses] using dis) frame
  rw [fieldEq] at heap
  have repU : Represents u.heap parent (nodeAt side label (.node newLabel c d) sibling) := by
    rw [heap]
    simpa only [restart, newCursor, root] using semantic.1
  have childU : Represents u.heap (some label.address) (.node newLabel c d) := by
    cases side with
    | false => exact repU.2.1
    | true => exact repU.2.2
  have curU : u.ptr 0 = some newLabel.address :=
    (ptr 0 (by change (0 : Fin 7) ≠ 2; decide)
      (by change (0 : Fin 7) ≠ 3; decide) (by change (0 : Fin 7) ≠ 5; decide)).trans newCursor
  let v : State M (layout extra (regs + 1)) :=
    { u.setPtr 0 (some label.address) with pc := 1 }
  have back : Executes [.loadPtr 0 2 0, .halt] { u with pc := 0 } v 2 := by
    refine ⟨1, .single ?_, rfl, rfl⟩
    simp [step, Instr.effect, Instr.next, State.deref, curU, childU.1, record, v, State.setPtr]
  let out : State M (layout extra (regs + 1)) :=
    { v with pc := 2 + (sequence body (sequence reconnect [.loadPtr 0 2 0, .halt])).length }
  have exec : Executes (Balance.inChild side body) s out (time + 14) := by
    have run := nav.sequence (bodyExec.sequence (connected.sequence back))
    convert run using 1 <;> simp [Balance.inChild, Cslib.PointerMachine.sequence]; omega
  refine ⟨out, exec, repU, semantic.2.1, ?_, ?_, data, ?_, ?_⟩
  · simp [out, v, State.setPtr]
  · have keep := ptr 1 (by change (1 : Fin 7) ≠ 2; decide)
      (by change (1 : Fin 7) ≠ 3; decide) (by change (1 : Fin 7) ≠ 5; decide)
    simpa [out, v, State.setPtr, restart, rootReg] using keep
  · simp [out, v, State.setPtr, heap, restart]
  · intro z hz
    simpa only [out, v, State.setPtr, heap, restart, newCursor, root] using semantic.2.2 z hz

private structure Effect (s t : State M (layout extra (regs + 1)))
    (old tree : BinaryTree (Label M extra)) (target : AVLTree M.Value)
    (encode : ℕ → M.Value) (field : Fin (extra + 1)) (parent : Pointer) : Prop
    extends Rebuilt encode field s t parent old tree target where
  size : t.heap.length = s.heap.length
  data : ∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i

private theorem rotate_correct (side : Bool) (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label : Label M extra)
    (l r : BinaryTree (Label M extra)) (A B : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (.node label l r))
    (distinct : AddressesDistinct (.node label l r))
    (ml : Matches encode field l A) (mr : Matches encode field r B)
    (hl : A.HeightConsistent) (hr : B.HeightConsistent)
    (nonempty : if side then A ≠ .nil else B ≠ .nil)
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t tree, Executes (if side then rotateRight zero maxSucc field else
      rotateLeft zero maxSucc field) s t 39 ∧
      Effect s t (.node label l r) tree
        (if side then AVLTree.rotateRight (label.data 0) A B else
          AVLTree.rotateLeft (label.data 0) A B) encode field parent := by
  cases side with
  | true =>
    cases A with
    | nil => exact (nonempty rfl).elim
    | node key height left right =>
      cases l with
      | nil => cases ml
      | node child a b =>
        rcases ml with ⟨keyEq, _, ma, mb⟩
        obtain ⟨t, run, rt, mt, dt, _, ct, size, data, ptr, saved, frame⟩ :=
          rotateRight_correct zero maxSucc encode zero_spec max_spec field notKey
            s child label a b r left right B parent rep distinct ma mb mr hl.2.1 hl.2.2 hr
            cursor pc
        refine ⟨t, _, run, ⟨⟨rt, ?_, dt, ?_, ct, saved, ?_, ?_⟩, size, data⟩⟩
        · simpa [AVLTree.rotateRight, mkNode, keyEq] using mt
        · simp [addresses, BinaryTree.map, SearchTree.elements,
            Finset.insert_union, Finset.union_insert, Finset.insert_comm]
        · exact ptr 1 (by change (1 : Fin 7) ≠ 0; decide)
            (by change (1 : Fin 7) ≠ 2; decide) (by change (1 : Fin 7) ≠ 3; decide)
            (by change (1 : Fin 7) ≠ 4; decide) (by change (1 : Fin 7) ≠ 6; decide)
        · intro z hz
          have no : z ≠ label.address ∧ z ≠ child.address ∧ z ∉ addresses b := by
            simp only [addresses, BinaryTree.map, SearchTree.elements, Finset.mem_insert,
              Finset.mem_union, not_or] at hz ⊢
            tauto
          apply frame z no.2.1 no.1
          cases b with
          | nil => simp [root]
          | node b bl br =>
            intro eq
            exact no.2.2 ((mem_addresses_iff ..).mpr ⟨.one, b, rfl, Option.some.inj eq⟩)
  | false =>
    cases B with
    | nil => exact (nonempty rfl).elim
    | node key height left right =>
      cases r with
      | nil => cases mr
      | node child b c =>
        rcases mr with ⟨keyEq, _, mb, mc⟩
        obtain ⟨t, run, rt, mt, dt, _, ct, size, data, ptr, saved, frame⟩ :=
          rotateLeft_correct zero maxSucc encode zero_spec max_spec field notKey
            s child label l b c A left right parent rep distinct ml mb mc hl hr.2.1 hr.2.2
            cursor pc
        refine ⟨t, _, run, ⟨⟨rt, ?_, dt, ?_, ct, saved, ?_, ?_⟩, size, data⟩⟩
        · simpa [AVLTree.rotateLeft, mkNode, keyEq] using mt
        · simp [addresses, BinaryTree.map, SearchTree.elements,
            Finset.insert_union, Finset.union_insert, Finset.insert_comm, Finset.union_assoc]
        · exact ptr 1 (by change (1 : Fin 7) ≠ 0; decide)
            (by change (1 : Fin 7) ≠ 2; decide) (by change (1 : Fin 7) ≠ 3; decide)
            (by change (1 : Fin 7) ≠ 4; decide) (by change (1 : Fin 7) ≠ 6; decide)
        · intro z hz
          have no : z ≠ label.address ∧ z ≠ child.address ∧ z ∉ addresses b := by
            simp only [addresses, BinaryTree.map, SearchTree.elements, Finset.mem_insert,
              Finset.mem_union, not_or] at hz ⊢
            tauto
          apply frame z no.2.1 no.1
          cases b with
          | nil => simp [root]
          | node b bl br =>
            intro eq
            exact no.2.2 ((mem_addresses_iff ..).mpr ⟨.one, b, rfl, Option.some.inj eq⟩)

private theorem height_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label : Label M extra)
    (l r : BinaryTree (Label M extra)) (A B : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (.node label l r))
    (distinct : AddressesDistinct (.node label l r))
    (ml : Matches encode field l A) (mr : Matches encode field r B)
    (hl : A.HeightConsistent) (hr : B.HeightConsistent)
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) (saved : s.ptr 6 = s.ptr 0) :
    ∃ t tree, Executes (recomputeHeight zero maxSucc field) s t 9 ∧
      Effect s t (.node label l r) tree (mkNode (label.data 0) A B) encode field parent := by
  obtain ⟨t, run, heap, rt, mt, dt, data, ptr⟩ := recomputeHeight_mkNode zero maxSucc encode
    zero_spec max_spec field notKey s label l r A B parent rep distinct ml mr hl hr cursor pc
  refine ⟨t, _, run, ⟨⟨rt, mt, dt, rfl, ?_, ?_, ?_, ?_⟩, ?_, data⟩⟩
  · exact (ptr 0 (by change (0 : Fin 7) ≠ 2; decide)).trans cursor
  · exact (ptr 6 (by change (6 : Fin 7) ≠ 2; decide)).trans saved
  · exact ptr 1 (by change (1 : Fin 7) ≠ 2; decide)
  · intro z hz
    rw [heap]
    apply List.getElem?_modify_ne
    intro eq
    exact hz ((mem_addresses_iff ..).mpr ⟨.one, label, rfl, eq⟩)
  · rw [heap, List.length_modify]

private theorem doubleRight_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label child : Label M extra)
    (a b r : BinaryTree (Label M extra)) (A B R : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (.node label (.node child a b) r))
    (distinct : AddressesDistinct (.node label (.node child a b) r))
    (ma : Matches encode field a A) (mb : Matches encode field b B)
    (mr : Matches encode field r R)
    (ha : A.HeightConsistent) (hb : B.HeightConsistent) (hr : R.HeightConsistent)
    (nonempty : B ≠ .nil) (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t tree, Executes
        (sequence (Balance.inChild false (rotateLeft zero maxSucc field))
          (rotateRight zero maxSucc field))
        s t 93 ∧
      Effect s t (.node label (.node child a b) r) tree
        (AVLTree.rotateRight (label.data 0) (AVLTree.rotateLeft (child.data 0) A B) R)
        encode field parent := by
  let start : State M (layout extra (regs + 1)) :=
    { s.setPtr 0 (some child.address) with pc := 0 }
  obtain ⟨dc, _, _, _, _⟩ := (AddressesDistinct.node_iff ..).mp distinct
  obtain ⟨u, inner, run, effect⟩ := rotate_correct false zero maxSucc encode zero_spec max_spec
    field notKey start child a b A B (some label.address) rep.2.1 dc ma mb ha hb nonempty
    (by simp [start, State.setPtr]) rfl
  cases inner with
  | nil =>
    have bad := effect.matched
    cases B <;> simp_all [Matches, AVLTree.rotateLeft, mkNode]
  | node pivot c d =>
    obtain ⟨v, innerRun, rv, dv, cv, pv, data, size, frame⟩ := inChild_correct false
      (rotateLeft zero maxSucc field) s u label child pivot a b c d r parent 39
      rep distinct cursor pc run effect.rep effect.distinct effect.footprint effect.cursor
      (by simpa [start, State.setPtr] using effect.saved)
      (by simpa [start, State.setPtr] using effect.top) effect.frame
    have nonempty' : AVLTree.rotateLeft (child.data 0) A B ≠ .nil := by
      cases B <;> simp [AVLTree.rotateLeft, mkNode]
    obtain ⟨t, tree, outerRun, outer⟩ := rotate_correct true zero maxSucc encode
      zero_spec max_spec field notKey { v with pc := 0 } label (.node pivot c d) r
      (AVLTree.rotateLeft (child.data 0) A B) R parent rv dv effect.matched mr
      (heightConsistent_rotateLeft ha hb) hr nonempty' cv rfl
    refine ⟨_, tree, innerRun.sequence outerRun, ⟨⟨outer.rep, outer.matched, outer.distinct,
      ?_, outer.cursor, outer.saved.trans (cv.trans cursor.symm), outer.top.trans pv, ?_⟩,
      outer.size.trans (size.trans effect.size), ?_⟩⟩
    · rw [outer.footprint]
      change Insert.insert label.address (addresses (.node pivot c d) ∪ addresses r) = _
      rw [effect.footprint]
      rfl
    · intro z hz
      rw [outer.frame z ?_, frame z hz]
      change z ∉ Insert.insert label.address (addresses (.node pivot c d) ∪ addresses r)
      rw [effect.footprint]
      exact hz
    · intro i hi hj
      rw [outer.data i hi hj]
      change v.data i = s.data i
      rw [data]
      exact effect.data i hi hj

private theorem doubleLeft_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label child : Label M extra)
    (l a b : BinaryTree (Label M extra)) (L A B : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (.node label l (.node child a b)))
    (distinct : AddressesDistinct (.node label l (.node child a b)))
    (ma : Matches encode field a A) (mb : Matches encode field b B)
    (ml : Matches encode field l L)
    (ha : A.HeightConsistent) (hb : B.HeightConsistent) (hl : L.HeightConsistent)
    (nonempty : A ≠ .nil) (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t tree, Executes
        (sequence (Balance.inChild true (rotateRight zero maxSucc field))
          (rotateLeft zero maxSucc field))
        s t 93 ∧
      Effect s t (.node label l (.node child a b)) tree
        (AVLTree.rotateLeft (label.data 0) L (AVLTree.rotateRight (child.data 0) A B))
        encode field parent := by
  let start : State M (layout extra (regs + 1)) :=
    { s.setPtr 0 (some child.address) with pc := 0 }
  obtain ⟨_, dc, _, _, _⟩ := (AddressesDistinct.node_iff ..).mp distinct
  obtain ⟨u, inner, run, effect⟩ := rotate_correct true zero maxSucc encode zero_spec max_spec
    field notKey start child a b A B (some label.address) rep.2.2 dc ma mb ha hb nonempty
    (by simp [start, State.setPtr]) rfl
  cases inner with
  | nil =>
    have bad := effect.matched
    cases A <;> simp_all [Matches, AVLTree.rotateRight, mkNode]
  | node pivot c d =>
    obtain ⟨v, innerRun, rv, dv, cv, pv, data, size, frame⟩ := inChild_correct true
      (rotateRight zero maxSucc field) s u label child pivot a b c d l parent 39
      rep distinct cursor pc run effect.rep effect.distinct effect.footprint effect.cursor
      (by simpa [start, State.setPtr] using effect.saved)
      (by simpa [start, State.setPtr] using effect.top) effect.frame
    have nonempty' : AVLTree.rotateRight (child.data 0) A B ≠ .nil := by
      cases A <;> simp [AVLTree.rotateRight, mkNode]
    obtain ⟨t, tree, outerRun, outer⟩ := rotate_correct false zero maxSucc encode
      zero_spec max_spec field notKey { v with pc := 0 } label l (.node pivot c d)
      L (AVLTree.rotateRight (child.data 0) A B) parent rv dv ml effect.matched
      hl (heightConsistent_rotateRight ha hb) nonempty' cv rfl
    refine ⟨_, tree, innerRun.sequence outerRun, ⟨⟨outer.rep, outer.matched, outer.distinct,
      ?_, outer.cursor, outer.saved.trans (cv.trans cursor.symm), outer.top.trans pv, ?_⟩,
      outer.size.trans (size.trans effect.size), ?_⟩⟩
    · rw [outer.footprint]
      change Insert.insert label.address (addresses l ∪ addresses (.node pivot c d)) = _
      rw [effect.footprint]
      rfl
    · intro z hz
      rw [outer.frame z ?_, frame z hz]
      change z ∉ Insert.insert label.address (addresses l ∪ addresses (.node pivot c d))
      rw [effect.footprint]
      exact hz
    · intro i hi hj
      rw [outer.data i hi hj]
      change v.data i = s.data i
      rw [data]
      exact effect.data i hi hj

private theorem Effect.withPc {s t : State M (layout extra (regs + 1))}
    {old tree : BinaryTree (Label M extra)} {target : AVLTree M.Value}
    {encode : ℕ → M.Value} {field : Fin (extra + 1)} {parent : Pointer}
    (h : Effect s t old tree target encode field parent) (pc : ℕ) :
    Effect s { t with pc := pc } old tree target encode field parent :=
  ⟨⟨h.rep, h.matched, h.distinct, h.footprint, h.cursor, h.saved, h.top, h.frame⟩,
    h.size, h.data⟩

private theorem Effect.before {s q t : State M (layout extra (regs + 1))}
    {old tree : BinaryTree (Label M extra)} {target : AVLTree M.Value}
    {encode : ℕ → M.Value} {field : Fin (extra + 1)} {parent : Pointer}
    (h : Effect q t old tree target encode field parent)
    (heap : q.heap = s.heap) (cursor : q.ptr 0 = s.ptr 0) (rootReg : q.ptr 1 = s.ptr 1)
    (data : ∀ i, i ≠ 1 → i ≠ 2 → q.data i = s.data i) :
    Effect s t old tree target encode field parent :=
  { h with
    top := h.top.trans rootReg
    size := h.size.trans (congrArg List.length heap)
    data := fun i hi hj => (h.data i hi hj).trans (data i hi hj)
    saved := h.saved.trans cursor
    frame := fun z hz => (h.frame z hz).trans (congrArg (fun h => h[z]?) heap) }

/-- Handle a heavy child: compare its two child heights and perform a single or double
rotation. `side = true` selects the left-heavy case and its final right rotation. -/
@[expose] def Balance.heavyCase (side : Bool) (zero maxSucc : M.Op) (le : M.Test)
    (field : Fin (extra + 1)) : List (Instr M (layout extra (regs + 1))) :=
  let turn := if side then rotateRight zero maxSucc field else rotateLeft zero maxSucc field
  let inner := if side then rotateLeft zero maxSucc field else rotateRight zero maxSucc field
  sequence [.loadPtr 3 (if side then 0 else 1) 0, .halt]
    (sequence (Balance.readHeights zero field 3)
      (branch le (if side then 2 else 1) (if side then 1 else 2) turn
        (sequence (Balance.inChild (!side) inner) turn)))

private theorem leftCase_correct (zero maxSucc : M.Op) (le : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label child : Label M extra)
    (a b r : BinaryTree (Label M extra)) (A B R : AVLTree M.Value) (parent : Pointer)
    (height : ℕ) (cache : child.data field = encode height)
    (hc : height = 1 + max A.cachedHeight B.cachedHeight)
    (rep : Represents s.heap parent (.node label (.node child a b) r))
    (distinct : AddressesDistinct (.node label (.node child a b) r))
    (ma : Matches encode field a A) (mb : Matches encode field b B)
    (mr : Matches encode field r R)
    (ha : A.HeightConsistent) (hb : B.HeightConsistent) (hr : R.HeightConsistent)
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t tree time, Executes (Balance.heavyCase true zero maxSucc le field) s t time ∧ time ≤ 106 ∧
      Effect s t (.node label (.node child a b) r) tree
        (if B.cachedHeight ≤ A.cachedHeight then
          AVLTree.rotateRight (label.data 0) (.node (child.data 0) height A B) R
        else AVLTree.rotateRight (label.data 0) (AVLTree.rotateLeft (child.data 0) A B) R)
        encode field parent := by
  let navState : State M (layout extra (regs + 1)) :=
    { s.setPtr 3 (some child.address) with pc := 1 }
  have nav : Executes [.loadPtr 3 0 0, .halt] s navState 2 := by
    refine ⟨1, .single ?_, rfl, rfl⟩
    simp [step, pc, Instr.effect, Instr.next, State.deref, cursor, rep.1, record, navState, root]
  obtain ⟨v, read, heap, dl, dr, data, ptr⟩ := readHeights_correct zero (encode 0) zero_spec
    field 3 (by decide) { navState with pc := 0 } child a b (some label.address) rep.2.1
    (by simp [navState, State.setPtr]) rfl
  let q : State M (layout extra (regs + 1)) := { v with pc := 0 }
  have qheap : q.heap = s.heap := heap
  have qp (i : Fin 7) (hi : i ≠ 2) (hj : i ≠ 3) : q.ptr i = s.ptr i := by
    rw [show q.ptr i = v.ptr i from rfl, ptr i hi]
    simp [navState, State.setPtr, hj]
  have qcursor : q.ptr 0 = some label.address :=
    (qp 0 (by decide) (by decide)).trans cursor
  have test : M.evalTest le (q.data 2) (q.data 1) = decide (B.cachedHeight ≤ A.cachedHeight) := by
    rw [show q.data 2 = v.data 2 from rfl, show q.data 1 = v.data 1 from rfl,
      dl, dr, ma.heightValue, mb.heightValue, le_spec]
  have chosen : ∃ t tree time,
      Executes (if M.evalTest le (q.data 2) (q.data 1) then rotateRight zero maxSucc field else
        sequence (Balance.inChild false (rotateLeft zero maxSucc field))
          (rotateRight zero maxSucc field))
        q t time ∧ time ≤ 93 ∧
      Effect q t (.node label (.node child a b) r) tree
        (if B.cachedHeight ≤ A.cachedHeight then
          AVLTree.rotateRight (label.data 0) (.node (child.data 0) height A B) R
        else AVLTree.rotateRight (label.data 0) (AVLTree.rotateLeft (child.data 0) A B) R)
        encode field parent := by
    by_cases h : B.cachedHeight ≤ A.cachedHeight
    · obtain ⟨t, tree, run, effect⟩ := rotate_correct true zero maxSucc encode zero_spec max_spec
        field notKey q label (.node child a b) r (.node (child.data 0) height A B) R parent
        (qheap.symm ▸ rep) distinct ⟨rfl, cache, ma, mb⟩ mr ⟨hc, ha, hb⟩ hr
        (by simp) qcursor rfl
      exact ⟨t, tree, 39, by simpa [test, h] using run, by omega, by simpa [h] using effect⟩
    · have nonempty : B ≠ .nil := by intro eq; simp [eq] at h
      obtain ⟨t, tree, run, effect⟩ := doubleRight_correct zero maxSucc encode zero_spec max_spec
        field notKey q label child a b r A B R parent (qheap.symm ▸ rep) distinct ma mb mr
        ha hb hr nonempty qcursor rfl
      exact ⟨t, tree, 93, by simpa [test, h] using run, le_rfl, by simpa [h] using effect⟩
  obtain ⟨t, tree, time, run, bound, effect⟩ := chosen
  have branched := run.branch (pc := rfl)
  refine ⟨_, tree, 2 + (7 + (time + 2) + 1) + 1, nav.sequence (read.sequence branched),
    by omega, ?_⟩
  exact (effect.before qheap (qp 0 (by decide) (by decide))
    (qp 1 (by decide) (by decide)) data).withPc _

private theorem rightCase_correct (zero maxSucc : M.Op) (le : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label child : Label M extra)
    (l a b : BinaryTree (Label M extra)) (L A B : AVLTree M.Value) (parent : Pointer)
    (height : ℕ) (cache : child.data field = encode height)
    (hc : height = 1 + max A.cachedHeight B.cachedHeight)
    (rep : Represents s.heap parent (.node label l (.node child a b)))
    (distinct : AddressesDistinct (.node label l (.node child a b)))
    (ma : Matches encode field a A) (mb : Matches encode field b B)
    (ml : Matches encode field l L)
    (ha : A.HeightConsistent) (hb : B.HeightConsistent) (hl : L.HeightConsistent)
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t tree time, Executes (Balance.heavyCase false zero maxSucc le field) s t time ∧ time ≤ 106 ∧
      Effect s t (.node label l (.node child a b)) tree
        (if A.cachedHeight ≤ B.cachedHeight then
          AVLTree.rotateLeft (label.data 0) L (.node (child.data 0) height A B)
        else AVLTree.rotateLeft (label.data 0) L (AVLTree.rotateRight (child.data 0) A B))
        encode field parent := by
  let navState : State M (layout extra (regs + 1)) :=
    { s.setPtr 3 (some child.address) with pc := 1 }
  have nav : Executes [.loadPtr 3 1 0, .halt] s navState 2 := by
    refine ⟨1, .single ?_, rfl, rfl⟩
    simp [step, pc, Instr.effect, Instr.next, State.deref, cursor, rep.1, record, navState, root]
  obtain ⟨v, read, heap, dl, dr, data, ptr⟩ := readHeights_correct zero (encode 0) zero_spec
    field 3 (by decide) { navState with pc := 0 } child a b (some label.address) rep.2.2
    (by simp [navState, State.setPtr]) rfl
  let q : State M (layout extra (regs + 1)) := { v with pc := 0 }
  have qheap : q.heap = s.heap := heap
  have qp (i : Fin 7) (hi : i ≠ 2) (hj : i ≠ 3) : q.ptr i = s.ptr i := by
    rw [show q.ptr i = v.ptr i from rfl, ptr i hi]
    simp [navState, State.setPtr, hj]
  have qcursor : q.ptr 0 = some label.address :=
    (qp 0 (by decide) (by decide)).trans cursor
  have test : M.evalTest le (q.data 1) (q.data 2) = decide (A.cachedHeight ≤ B.cachedHeight) := by
    rw [show q.data 2 = v.data 2 from rfl, show q.data 1 = v.data 1 from rfl,
      dl, dr, ma.heightValue, mb.heightValue, le_spec]
  have chosen : ∃ t tree time,
      Executes (if M.evalTest le (q.data 1) (q.data 2) then rotateLeft zero maxSucc field else
        sequence (Balance.inChild true (rotateRight zero maxSucc field))
          (rotateLeft zero maxSucc field))
        q t time ∧ time ≤ 93 ∧
      Effect q t (.node label l (.node child a b)) tree
        (if A.cachedHeight ≤ B.cachedHeight then
          AVLTree.rotateLeft (label.data 0) L (.node (child.data 0) height A B)
        else AVLTree.rotateLeft (label.data 0) L (AVLTree.rotateRight (child.data 0) A B))
        encode field parent := by
    by_cases h : A.cachedHeight ≤ B.cachedHeight
    · obtain ⟨t, tree, run, effect⟩ := rotate_correct false zero maxSucc encode zero_spec max_spec
        field notKey q label l (.node child a b) L (.node (child.data 0) height A B) parent
        (qheap.symm ▸ rep) distinct ml ⟨rfl, cache, ma, mb⟩ hl ⟨hc, ha, hb⟩
        (by simp) qcursor rfl
      exact ⟨t, tree, 39, by simpa [test, h] using run, by omega, by simpa [h] using effect⟩
    · have nonempty : A ≠ .nil := by intro eq; simp [eq] at h
      obtain ⟨t, tree, run, effect⟩ := doubleLeft_correct zero maxSucc encode zero_spec max_spec
        field notKey q label child l a b L A B parent (qheap.symm ▸ rep) distinct ma mb ml
        ha hb hl nonempty qcursor rfl
      exact ⟨t, tree, 93, by simpa [test, h] using run, le_rfl, by simpa [h] using effect⟩
  obtain ⟨t, tree, time, run, bound, effect⟩ := chosen
  have branched := run.branch (pc := rfl)
  refine ⟨_, tree, 2 + (7 + (time + 2) + 1) + 1, nav.sequence (read.sequence branched),
    by omega, ?_⟩
  exact (effect.before qheap (qp 0 (by decide) (by decide))
    (qp 1 (by decide) (by decide)) data).withPc _

/-- Balance at cursor zero using cached child/grandchild heights. `heavy a b` means
`b + 1 < a`; `le` compares heights. Pointer register one and scalar register zero
are client registers; the other declared scratch registers may change. -/
@[expose] def balance (zero maxSucc : M.Op) (heavy le : M.Test) (field : Fin (extra + 1)) :
    List (Instr M (layout extra (regs + 1))) :=
  sequence [.movePtr 6 0, .halt]
    (sequence (Balance.readHeights zero field 0)
      (branch heavy 1 2 (Balance.heavyCase true zero maxSucc le field)
        (branch heavy 2 1 (Balance.heavyCase false zero maxSucc le field)
          (recomputeHeight zero maxSucc field))))

/-- The concrete balance program implements `AVLTree.balance` in at most 121 instructions,
without allocation. Children must have consistent encoded caches; the old root cache may
be arbitrary. Register six retains the former root for the caller's subsequent reconnection. -/
theorem balance_correct (zero maxSucc : M.Op) (heavy le : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (heavy_spec : ∀ a b, M.evalTest heavy (encode a) (encode b) = decide (b + 1 < a))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label : Label M extra)
    (l r : BinaryTree (Label M extra)) (A B : AVLTree M.Value) (parent : Pointer)
    (rep : Represents s.heap parent (.node label l r))
    (distinct : AddressesDistinct (.node label l r))
    (ml : Matches encode field l A) (mr : Matches encode field r B)
    (hl : A.HeightConsistent) (hr : B.HeightConsistent)
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t tree time, Executes (balance zero maxSucc heavy le field) s t time ∧ time ≤ 121 ∧
      Represents t.heap parent tree ∧
      Matches encode field tree (AVLTree.balance (label.data 0) A B) ∧
      AddressesDistinct tree ∧ addresses tree = addresses (.node label l r) ∧
      root tree ≠ none ∧ t.ptr 0 = root tree ∧ t.ptr 1 = s.ptr 1 ∧ t.ptr 6 = s.ptr 0 ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ z, z ∉ addresses (.node label l r) → t.heap[z]? = s.heap[z]?) ∧
      (∀ (z : ℕ) (f : Fin (extra + 1)), f ≠ field →
        (t.heap[z]?).map (fun n => n.data f) = (s.heap[z]?).map (fun n => n.data f)) := by
  let saved : State M (layout extra (regs + 1)) := { s.setPtr 6 (s.ptr 0) with pc := 1 }
  have save : Executes [.movePtr 6 0, .halt] s saved 2 := by
    refine ⟨1, .single ?_, rfl, rfl⟩
    simp [step, pc, Instr.effect, Instr.next, saved]
  obtain ⟨v, read, heap, dl, dr, data, ptr⟩ := readHeights_correct zero (encode 0) zero_spec
    field 0 (by decide) { saved with pc := 0 } label l r parent rep
    (by simpa [saved, State.setPtr] using cursor) rfl
  let q : State M (layout extra (regs + 1)) := { v with pc := 0 }
  have qheap : q.heap = s.heap := heap
  have qp (i : Fin 7) (hi : i ≠ 2) (hj : i ≠ 6) : q.ptr i = s.ptr i := by
    rw [show q.ptr i = v.ptr i from rfl, ptr i hi]
    simp [saved, State.setPtr, hj]
  have qcursor : q.ptr 0 = some label.address := (qp 0 (by decide) (by decide)).trans cursor
  have qs : q.ptr 6 = q.ptr 0 := by
    rw [qp 0 (by decide) (by decide)]
    change v.ptr 6 = s.ptr 0
    rw [ptr 6 (by change (6 : Fin 7) ≠ 2; decide)]
    simp [saved, State.setPtr]
  have testL : M.evalTest heavy (q.data 1) (q.data 2) =
      decide (B.cachedHeight + 1 < A.cachedHeight) := by
    rw [show q.data 1 = v.data 1 from rfl, show q.data 2 = v.data 2 from rfl,
      dl, dr, ml.heightValue, mr.heightValue, heavy_spec]
  have testR : M.evalTest heavy (q.data 2) (q.data 1) =
      decide (A.cachedHeight + 1 < B.cachedHeight) := by
    rw [show q.data 1 = v.data 1 from rfl, show q.data 2 = v.data 2 from rfl,
      dl, dr, ml.heightValue, mr.heightValue, heavy_spec]
  have chosen : ∃ t tree time,
      Executes (if M.evalTest heavy (q.data 1) (q.data 2) then
          Balance.heavyCase true zero maxSucc le field else
        branch heavy 2 1 (Balance.heavyCase false zero maxSucc le field)
          (recomputeHeight zero maxSucc field))
        q t time ∧ time ≤ 108 ∧
      Effect q t (.node label l r) tree (AVLTree.balance (label.data 0) A B)
        encode field parent := by
    by_cases hL : B.cachedHeight + 1 < A.cachedHeight
    · cases A with
      | nil => simp at hL
      | node key height left right =>
        change B.cachedHeight + 1 < height at hL
        cases l with
        | nil => cases ml
        | node child a b =>
          rcases ml with ⟨keyEq, cache, ma, mb⟩
          obtain ⟨hc, ha, hb⟩ := hl
          obtain ⟨t, tree, time, run, bound, effect⟩ := leftCase_correct zero maxSucc le encode
            zero_spec max_spec le_spec field notKey q label child a b r left right B parent
            height cache hc (qheap.symm ▸ rep) distinct ma mb mr ha hb hr qcursor rfl
          refine ⟨t, tree, time, by simpa [testL, hL] using run, by omega, ?_⟩
          simpa [AVLTree.balance, hL, keyEq] using effect
    · have selected : ∃ t tree time,
          Executes (if M.evalTest heavy (q.data 2) (q.data 1) then
          Balance.heavyCase false zero maxSucc le field
            else recomputeHeight zero maxSucc field) q t time ∧ time ≤ 106 ∧
          Effect q t (.node label l r) tree (AVLTree.balance (label.data 0) A B)
            encode field parent := by
        by_cases hR : A.cachedHeight + 1 < B.cachedHeight
        · cases B with
          | nil => simp at hR
          | node key height left right =>
            change A.cachedHeight + 1 < height at hR
            change ¬ height + 1 < A.cachedHeight at hL
            cases r with
            | nil => cases mr
            | node child a b =>
              rcases mr with ⟨keyEq, cache, ma, mb⟩
              obtain ⟨hc, ha, hb⟩ := hr
              obtain ⟨t, tree, time, run, bound, effect⟩ := rightCase_correct zero maxSucc le encode
                zero_spec max_spec le_spec field notKey q label child l a b A left right parent
                height cache hc (qheap.symm ▸ rep) distinct ma mb ml ha hb hl qcursor rfl
              refine ⟨t, tree, time, by simpa [testR, hR] using run, bound, ?_⟩
              simpa [AVLTree.balance, hL, hR, keyEq] using effect
        · obtain ⟨t, tree, run, effect⟩ := height_correct zero maxSucc encode zero_spec max_spec
            field notKey q label l r A B parent (qheap.symm ▸ rep) distinct ml mr hl hr
            qcursor rfl qs
          exact ⟨t, tree, 9, by simpa [testR, hR] using run, by omega,
            by simpa [AVLTree.balance, hL, hR] using effect⟩
      obtain ⟨t, tree, time, run, bound, effect⟩ := selected
      have branched := run.branch (pc := rfl)
      refine ⟨{ t with pc := 1 + (recomputeHeight (regs := regs) zero maxSucc field).length +
        (Balance.heavyCase (regs := regs) false zero maxSucc le field).length }, tree, time + 2,
        ?_, by omega, effect.withPc _⟩
      simpa only [testL, decide_eq_false hL, Bool.false_eq_true, ↓reduceIte] using branched
  obtain ⟨t, tree, time, run, bound, effect⟩ := chosen
  have branched := run.branch (pc := rfl)
  have total := save.sequence (read.sequence branched)
  have finalEffect := effect.before qheap (qp 0 (by decide) (by decide))
    (qp 1 (by decide) (by decide)) data
  refine ⟨_, tree, _, total, by omega, finalEffect.rep, finalEffect.matched,
    finalEffect.distinct, finalEffect.footprint, ?_, finalEffect.cursor, finalEffect.top,
    finalEffect.saved, finalEffect.size, finalEffect.data, finalEffect.frame, ?_⟩
  · cases tree with
    | node => simp [root]
    | nil =>
      have matched := finalEffect.matched
      cases eq : AVLTree.balance (label.data 0) A B with
      | nil => exact (balance_ne_nil _ _ _ eq).elim
      | node => simp [eq, Matches] at matched
  · intro z f hf
    obtain ⟨_, steps, _, _⟩ := total
    apply steps.data_frame f
    simp only [Balance.heavyCase, Balance.readHeights, Balance.inChild, rotateRight, rotateLeft,
      rotationProgram, sequence_no_data_writes, branch_no_data_writes,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
    simp [recomputeHeight, readHeightsPrefix, SearchTree.PointerMachine.rotateRight,
      SearchTree.PointerMachine.rotateLeft, reconnect, Instr.WritesData, Ne.symm hf]


end Cslib.DataStructure.AVLTree.PointerMachine

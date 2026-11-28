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
import CslibFrontier.DataStructure.AVLTree.Side

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

private theorem readHeights_correct (zero : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (field : Fin (extra + 1)) (base savedReg : Fin 7)
    (hb : base ≠ 2) (h0 : savedReg ≠ 0) (h1 : savedReg ≠ 1)
    (s : State M (layout extra (regs + 1))) (val : Pointer)
    (label : Label M extra) (l r : BinaryTree (Label M extra)) (L R : AVLTree M.Value)
    (parent : Pointer) (rep : Represents s.heap parent (.node label l r))
    (ml : Matches encode field l L) (mr : Matches encode field r R)
    (target : (s.setPtr savedReg val).ptr base = some label.address) :
    ∃ v, Executes (Balance.readHeights zero field base)
        { s.setPtr savedReg val with pc := 0 } v 7 ∧
      v.heap = s.heap ∧
      v.data 1 = encode L.cachedHeight ∧ v.data 2 = encode R.cachedHeight ∧
      (∀ i, i ≠ 1 → i ≠ 2 → v.data i = s.data i) ∧
      v.ptr 0 = s.ptr 0 ∧ v.ptr 1 = s.ptr 1 ∧
      (∀ i, i ≠ 2 → v.ptr i = (s.setPtr savedReg val).ptr i) := by
  obtain ⟨v, run, tpc, heap, dl, dr, data, ptr⟩ := readHeightsPrefix_runs zero (encode 0)
    zero_spec field base hb [.halt] { s.setPtr savedReg val with pc := 0 } label l r parent
    rep target rfl
  exact ⟨v, ⟨6, run, by simp [Balance.readHeights, readHeightsPrefix, tpc], rfl⟩,
    heap, dl.trans ml.heightValue, dr.trans mr.heightValue, data,
    (ptr 0 (by simp [layout])).trans (by simp [State.setPtr, h0.symm]),
    (ptr 1 (by simp [layout])).trans (by simp [State.setPtr, h1.symm]), ptr⟩

private structure Effect (s t : State M (layout extra (regs + 1)))
    (old tree : BinaryTree (Label M extra)) (target : AVLTree M.Value)
    (encode : ℕ → M.Value) (field : Fin (extra + 1)) (parent : Pointer) : Prop
    extends Rebuilt encode field s t parent old tree target where
  size : t.heap.length = s.heap.length
  data : ∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i

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

/-- Run a child-subtree block, reconnect its result, then return to the original parent. -/
@[expose] def Balance.inChild (right : Bool) (body : List (Instr M (layout extra (regs + 1)))) :
    List (Instr M (layout extra (regs + 1))) :=
  sequence [.loadPtr 0 (if right then 1 else 0) 0, .halt]
    (sequence body (sequence reconnect [.loadPtr 0 2 0, .halt]))

private theorem inChild_correct (right : Bool)
    (body : List (Instr M (layout extra (regs + 1))))
    (encode : ℕ → M.Value) (field : Fin (extra + 1))
    (s t : State M (layout extra (regs + 1))) (label : Label M extra)
    (old new sibling : BinaryTree (Label M extra)) (parent : Pointer)
    (o time : ℕ) (target : AVLTree M.Value)
    (rep : Represents s.heap parent (nodeAt right label old sibling))
    (distinct : AddressesDistinct (nodeAt right label old sibling))
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0)
    (hroot : root old = some o)
    (bodyExec : Executes body { s.setPtr 0 (some o) with pc := 0 } t time)
    (built : Effect { s.setPtr 0 (some o) with pc := 0 } t old new target encode field
      (some label.address))
    (nonempty : new ≠ .nil) :
    ∃ u, Executes (Balance.inChild right body) s u (time + 14) ∧
      Represents u.heap parent (nodeAt right label new sibling) ∧
      AddressesDistinct (nodeAt right label new sibling) ∧
      u.ptr 0 = some label.address ∧ u.ptr 1 = s.ptr 1 ∧ u.data = t.data ∧
      u.heap.length = t.heap.length ∧
      (∀ z, z ∉ addresses (nodeAt right label old sibling) → u.heap[z]? = s.heap[z]?) := by
  obtain ⟨lookup, _, _⟩ := (represents_nodeAt_iff ..).mp rep
  obtain ⟨_, _, no, _, dis⟩ := (nodeAt_distinct_iff ..).mp distinct
  have nav : Executes [.loadPtr 0 (if right then 1 else 0) 0, .halt] s
      { s.setPtr 0 (some o) with pc := 1 } 2 := by
    refine ⟨1, .single ?_, rfl, rfl⟩
    cases right <;>
      simp [step, pc, Instr.effect, Instr.next, State.deref, cursor, lookup, record, hroot]
  obtain _ | ⟨nl, c, d⟩ := new
  · exact (nonempty rfl).elim
  have saved : t.ptr 6 = some o := by simpa [State.setPtr] using built.saved
  have read : ({ t with pc := 0 } : State M (layout extra (regs + 1))).deref 0 =
      some (record (root c) (root d) (some label.address) nl) := by
    simp [State.deref, built.cursor, root, built.rep.1]
  obtain ⟨u, fld, connected, fields, oldLink, heap, data, ptr⟩ :=
    reconnect_child { t with pc := 0 } _ _ label.address rfl read rfl
      ((built.frame _ no).trans lookup) (by cases right <;> simp [record, saved, hroot])
  have fieldEq : fld = if right then 1 else 0 := by
    have siblingNe : root sibling ≠ some o := fun e =>
      Finset.disjoint_left.mp dis (root_mem_addresses hroot) (root_mem_addresses e)
    rcases fields with rfl | rfl <;> cases right <;>
      first | rfl | exact (siblingNe (by simpa [record, saved] using oldLink)).elim
  have semantic := replaceChild right s.heap t.heap label old (.node nl c d) sibling parent
    rep distinct built.rep built.distinct (by simpa only [built.footprint] using no)
    (by simpa only [built.footprint] using dis) built.frame
  rw [fieldEq] at heap
  have repU : Represents u.heap parent (nodeAt right label (.node nl c d) sibling) := by
    simpa only [heap, built.cursor, root] using semantic.1
  have curU : u.ptr 0 = some nl.address :=
    (ptr 0 (by simp [layout]) (by simp [layout]) (by simp [layout])).trans built.cursor
  let v : State M (layout extra (regs + 1)) := { u.setPtr 0 (some label.address) with pc := 1 }
  have back : Executes [.loadPtr 0 2 0, .halt] { u with pc := 0 } v 2 :=
    ⟨1, .single (by simp [step, Instr.effect, Instr.next, State.deref, curU,
      ((represents_nodeAt_iff ..).mp repU).2.1.1, record, v, State.setPtr]), rfl, rfl⟩
  have exec : Executes (Balance.inChild right body) s
      { v with pc := 2 + (sequence body (sequence reconnect [.loadPtr 0 2 0, .halt])).length }
      (time + 14) := by
    have run := nav.sequence (bodyExec.sequence (connected.sequence back))
    convert run using 1 <;> simp [Balance.inChild, Cslib.PointerMachine.sequence]; omega
  have keepTop := ptr 1 (by simp [layout]) (by simp [layout]) (by simp [layout])
  exact ⟨_, exec, repU, semantic.2.1, by simp [v, State.setPtr],
    by simpa [v, State.setPtr] using keepTop.trans built.top, data,
    by simp [v, State.setPtr, heap], fun z hz =>
      by simpa only [v, State.setPtr, heap, built.cursor, root] using semantic.2.2 z hz⟩

private theorem rotate_effect {s t : State M (layout extra (regs + 1))} {right : Bool}
    {label ch : Label M extra} {a b sibling tree : BinaryTree (Label M extra)}
    {target : AVLTree M.Value} {encode : ℕ → M.Value} {field : Fin (extra + 1)} {parent : Pointer}
    (rt : Represents t.heap parent tree) (mt : Matches encode field tree target)
    (dt : AddressesDistinct tree)
    (fp : addresses tree = addresses (nodeAt right label (.node ch a b) sibling))
    (ct : t.ptr 0 = root tree) (saved : t.ptr 6 = s.ptr 0)
    (size : t.heap.length = s.heap.length)
    (data : ∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i)
    (ptr : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 6 → t.ptr i = s.ptr i)
    (frame : ∀ z, z ≠ ch.address → z ≠ label.address →
      root (if right then a else b) ≠ some z → t.heap[z]? = s.heap[z]?) :
    Effect s t (nodeAt right label (.node ch a b) sibling) tree target encode field parent :=
  ⟨⟨rt, mt, dt, fp, ct, saved,
    ptr 1 (by simp [layout]) (by simp [layout]) (by simp [layout]) (by simp [layout])
      (by simp [layout]), fun z hz => by
    rw [nodeAt_addresses] at hz
    simp only [addresses, BinaryTree.map, SearchTree.elements,
      Finset.mem_insert, Finset.mem_union, not_or] at hz
    refine frame z hz.2.1.1 hz.1 fun eq => ?_
    cases right; exacts [hz.2.1.2.2 (root_mem_addresses eq), hz.2.1.2.1 (root_mem_addresses eq)]⟩,
    size, data⟩

private theorem rotate_correct (right : Bool) {zero maxSucc : M.Op} {encode : ℕ → M.Value}
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    {field : Fin (extra + 1)} (notKey : field ≠ 0)
    {s : State M (layout extra (regs + 1))} {label : Label M extra}
    {child sibling : BinaryTree (Label M extra)} {C S : AVLTree M.Value} {parent : Pointer}
    (rep : Represents s.heap parent (nodeAt right label child sibling))
    (distinct : AddressesDistinct (nodeAt right label child sibling))
    (mc : Matches encode field child C) (ms : Matches encode field sibling S)
    (hc : C.HeightConsistent) (hs : S.HeightConsistent)
    (nonempty : C ≠ .nil) (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    let prog := if right then rotateLeft zero maxSucc field else rotateRight zero maxSucc field
    ∃ t tree, Executes prog s t 39 ∧
      Effect s t (nodeAt right label child sibling) tree
        (rotateAt right (label.data 0) C S) encode field parent := by
  cases C with
  | nil => exact (nonempty rfl).elim
  | node key height cl cr =>
    cases child with
    | nil => cases mc
    | node ch a b =>
      rcases mc with ⟨keyEq, _, ma, mb⟩
      cases right with
      | false =>
        obtain ⟨t, run, rt, mt, dt, _, ct, size, data, ptr, saved, frame⟩ :=
          rotateRight_correct zero maxSucc encode zero_spec max_spec field notKey
            s ch label a b sibling cl cr S parent rep distinct ma mb ms hc.2.1 hc.2.2 hs
            cursor pc
        exact ⟨t, _, run, rotate_effect rt
          (by simpa [rotateAt, AVLTree.rotateRight, mkNode, keyEq] using mt)
          dt (by simp [nodeAt, addresses, BinaryTree.map, SearchTree.elements,
            Finset.insert_union, Finset.union_insert, Finset.insert_comm])
          ct saved size data ptr frame⟩
      | true =>
        obtain ⟨t, run, rt, mt, dt, _, ct, size, data, ptr, saved, frame⟩ :=
          rotateLeft_correct zero maxSucc encode zero_spec max_spec field notKey
            s ch label sibling a b S cl cr parent rep distinct ms ma mb hs hc.2.1 hc.2.2
            cursor pc
        exact ⟨t, _, run, rotate_effect rt
          (by simpa [rotateAt, AVLTree.rotateLeft, mkNode, keyEq] using mt)
          dt (by simp [nodeAt, addresses, BinaryTree.map, SearchTree.elements,
            Finset.insert_union, Finset.union_insert, Finset.insert_comm, Finset.union_assoc])
          ct saved size data ptr frame⟩

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
  refine ⟨t, _, run, ⟨⟨rt, mt, dt, rfl,
    (ptr 0 (by simp [layout])).trans cursor, (ptr 6 (by simp [layout])).trans saved,
    ptr 1 (by simp [layout]), fun z hz => ?_⟩, by rw [heap, List.length_modify], data⟩⟩
  rw [heap]
  exact List.getElem?_modify_ne _ _ fun eq =>
    hz (root_mem_addresses (t := .node label l r) (congrArg some eq))

private theorem doubleRotate_correct (right : Bool) (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label child : Label M extra)
    (outer inner sibling : BinaryTree (Label M extra)) (O N S : AVLTree M.Value)
    (parent : Pointer)
    (rep : Represents s.heap parent (nodeAt right label (nodeAt right child outer inner) sibling))
    (distinct : AddressesDistinct (nodeAt right label (nodeAt right child outer inner) sibling))
    (mo : Matches encode field outer O) (mn : Matches encode field inner N)
    (ms : Matches encode field sibling S)
    (ho : O.HeightConsistent) (hn : N.HeightConsistent) (hs : S.HeightConsistent)
    (nonempty : N ≠ .nil) (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    let innerProg := if right then rotateRight zero maxSucc field else rotateLeft zero maxSucc field
    let outerProg := if right then rotateLeft zero maxSucc field else rotateRight zero maxSucc field
    ∃ t tree, Executes (sequence (Balance.inChild right innerProg) outerProg) s t 93 ∧
      Effect s t (nodeAt right label (nodeAt right child outer inner) sibling) tree
        (rotateAt right (label.data 0) (rotateAt (!right) (child.data 0) N O) S)
        encode field parent := by
  let start : State M (layout extra (regs + 1)) :=
    { s.setPtr 0 (some child.address) with pc := 0 }
  have hcRep := ((represents_nodeAt_iff ..).mp rep).2.1
  have hcDis := ((nodeAt_distinct_iff ..).mp distinct).1
  rw [← nodeAt_not right child outer inner] at hcRep hcDis
  obtain ⟨u, mid, run, eff⟩ := rotate_correct (!right) zero_spec max_spec notKey
    (s := start) hcRep hcDis mn mo hn ho nonempty (by simp [start, State.setPtr]) rfl
  rw [nodeAt_not] at eff
  have rotNe : rotateAt (!right) (child.data 0) N O ≠ .nil := by
    cases right <;> cases N <;> simp [rotateAt, AVLTree.rotateLeft, AVLTree.rotateRight, mkNode]
  have midNe : mid ≠ .nil := fun h => by
    cases eq : rotateAt (!right) (child.data 0) N O with
    | nil => exact rotNe eq
    | node => cases h ▸ eq ▸ eff.matched
  have run' : Executes (if right then rotateRight zero maxSucc field
      else rotateLeft zero maxSucc field) start u 39 := by
    cases right <;> exact run
  obtain ⟨v, innerRun, rv, dv, cv, pv, data, size, frame⟩ := inChild_correct right _ encode field
    s u label _ mid sibling parent child.address 39 _ rep distinct cursor pc (root_nodeAt ..)
    run' eff midNe
  have hcMid : (rotateAt (!right) (child.data 0) N O).HeightConsistent := by
    cases right; exacts [heightConsistent_rotateLeft ho hn, heightConsistent_rotateRight hn ho]
  obtain ⟨t, tree, outerRun, outer⟩ := rotate_correct right zero_spec max_spec notKey
    (s := { v with pc := 0 }) rv dv eff.matched ms hcMid hs rotNe cv rfl
  refine ⟨_, tree, innerRun.sequence outerRun,
    ⟨⟨outer.rep, outer.matched, outer.distinct,
      by rw [outer.footprint, nodeAt_addresses, nodeAt_addresses, eff.footprint], outer.cursor,
      outer.saved.trans (cv.trans cursor.symm), outer.top.trans pv, fun z hz => ?_⟩,
      outer.size.trans (size.trans eff.size),
      fun i hi hj => (outer.data i hi hj).trans (data ▸ eff.data i hi hj)⟩⟩
  rw [outer.frame z (by rwa [nodeAt_addresses, eff.footprint, ← nodeAt_addresses]), frame z hz]

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

private theorem heavyCase_correct (right : Bool) {zero maxSucc : M.Op} {le : M.Test}
    {encode : ℕ → M.Value}
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    {field : Fin (extra + 1)} (notKey : field ≠ 0)
    {s : State M (layout extra (regs + 1))} {label : Label M extra}
    {child sibling : BinaryTree (Label M extra)} {C S : AVLTree M.Value} {parent : Pointer}
    (rep : Represents s.heap parent (nodeAt right label child sibling))
    (distinct : AddressesDistinct (nodeAt right label child sibling))
    (mc : Matches encode field child C) (ms : Matches encode field sibling S)
    (hc : C.HeightConsistent) (hs : S.HeightConsistent)
    (heavy : S.cachedHeight + 1 < C.cachedHeight)
    (cursor : s.ptr 0 = some label.address) (pc : s.pc = 0) :
    ∃ t tree time,
      Executes (Balance.heavyCase (!right) zero maxSucc le field) s t time ∧ time ≤ 106 ∧
      Effect s t (nodeAt right label child sibling) tree
        (balanceAt right (label.data 0) C S) encode field parent := by
  cases C with
  | nil => simp at heavy
  | node key height cl cr =>
    cases child with
    | nil => cases mc
    | node ch a b =>
      rcases mc with ⟨keyEq, cache, ma, mb⟩
      change S.cachedHeight + 1 < height at heavy
      have ⟨lookup, childRep, _⟩ := (represents_nodeAt_iff ..).mp rep
      have nav : Executes [.loadPtr 3 (if !right then 0 else 1) 0, .halt] s
          { s.setPtr 3 (some ch.address) with pc := 1 } 2 := by
        refine ⟨1, .single ?_, rfl, rfl⟩
        cases right <;> simp [step, pc, Instr.effect, Instr.next, State.deref, cursor, lookup,
          record, root]
      obtain ⟨v, read, heap, d1, d2, data, qp0, qp1, _⟩ := readHeights_correct zero encode
        zero_spec field 3 3 (by decide) (by decide) (by decide) s (some ch.address) ch a b cl cr
        (some label.address) childRep ma mb (by simp [State.setPtr])
      let q : State M (layout extra (regs + 1)) := { v with pc := 0 }
      let outer := if right then b else a
      let inner := if right then a else b
      let O := if right then cr else cl
      let N := if right then cl else cr
      have eqChild : BinaryTree.node ch a b = nodeAt right ch outer inner := by cases right <;> rfl
      have eqC : AVLTree.node key height cl cr = nodeSide right (ch.data 0) height O N := by
        cases right <;> simp [nodeSide, keyEq, O, N]
      have test : M.evalTest le (q.data (if !right then 2 else 1))
          (q.data (if !right then 1 else 2)) = decide (N.cachedHeight ≤ O.cachedHeight) := by
        cases right <;> simp [q, d1, d2, le_spec, O, N]
      let turn := if !right then rotateRight (regs := regs) zero maxSucc field
        else rotateLeft zero maxSucc field
      let innerP := if !right then rotateLeft (regs := regs) zero maxSucc field
        else rotateRight zero maxSucc field
      have chosen : ∃ t tree time,
          Executes (if M.evalTest le (q.data (if !right then 2 else 1))
              (q.data (if !right then 1 else 2)) then turn
            else sequence (Balance.inChild (!!right) innerP) turn) q t time ∧ time ≤ 93 ∧
          Effect q t (nodeAt right label (.node ch a b) sibling) tree
            (balanceAt right (label.data 0) (.node key height cl cr) S) encode field parent := by
        rw [eqC, balanceAt_heavy right (label.data 0) (ch.data 0) height O N S heavy, test]
        by_cases h : N.cachedHeight ≤ O.cachedHeight
        · obtain ⟨t, tree, run, eff⟩ := rotate_correct right zero_spec max_spec notKey
            (s := q) (heap.symm ▸ rep) distinct (C := .node key height cl cr)
            ⟨keyEq, cache, ma, mb⟩ ms hc hs (by simp) (qp0.trans cursor) rfl
          exact ⟨t, tree, 39, by cases right <;> simpa [h, turn] using run, by omega,
            by simpa [h, eqC] using eff⟩
        · have nonempty : N ≠ .nil := fun eq => by simp [eq] at h
          have ⟨ho, hn⟩ := (eqC ▸ hc).of_nodeSide
          have ⟨t, tree, run, eff⟩ := doubleRotate_correct right zero maxSucc encode zero_spec
            max_spec field notKey q label ch outer inner sibling O N S parent
            (eqChild ▸ heap.symm ▸ rep) (eqChild ▸ distinct) (by cases right <;> assumption)
            (by cases right <;> assumption) ms ho hn hs nonempty (qp0.trans cursor) rfl
          exact ⟨t, tree, 93, by cases right <;> simpa [h, turn, innerP] using run, le_rfl,
            by rw [← eqChild] at eff; simpa [h] using eff⟩
      obtain ⟨t, tree, time, run, bound, effect⟩ := chosen
      exact ⟨_, tree, 2 + (7 + (time + 2) + 1) + 1,
        nav.sequence (read.sequence (run.branch (pc := rfl))), by omega,
        (effect.before heap qp0 qp1 data).withPc _⟩

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
  have save : Executes [.movePtr 6 0, .halt] s { s.setPtr 6 (s.ptr 0) with pc := 1 } 2 :=
    ⟨1, .single (by simp [step, pc, Instr.effect, Instr.next]), rfl, rfl⟩
  obtain ⟨v, read, heap, d1, d2, data, qp0, qp1, ptr⟩ := readHeights_correct zero encode zero_spec
    field 0 6 (by decide) (by decide) (by decide) s (s.ptr 0) label l r A B parent rep ml mr
    (by simpa [State.setPtr] using cursor)
  let q : State M (layout extra (regs + 1)) := { v with pc := 0 }
  have qs : q.ptr 6 = q.ptr 0 :=
    ((ptr 6 (by simp [layout])).trans (by simp [State.setPtr])).trans qp0.symm
  have testL : M.evalTest heavy (q.data 1) (q.data 2) =
      decide (B.cachedHeight + 1 < A.cachedHeight) := by simp [q, d1, d2, heavy_spec]
  have testR : M.evalTest heavy (q.data 2) (q.data 1) =
      decide (A.cachedHeight + 1 < B.cachedHeight) := by simp [q, d1, d2, heavy_spec]
  have chosen : ∃ t tree time,
      Executes (if M.evalTest heavy (q.data 1) (q.data 2) then
          Balance.heavyCase true zero maxSucc le field else
        branch heavy 2 1 (Balance.heavyCase false zero maxSucc le field)
          (recomputeHeight zero maxSucc field))
        q t time ∧ time ≤ 108 ∧
      Effect q t (.node label l r) tree (AVLTree.balance (label.data 0) A B)
        encode field parent := by
    by_cases hL : B.cachedHeight + 1 < A.cachedHeight
    · obtain ⟨t, tree, time, run, bound, eff⟩ := heavyCase_correct false zero_spec max_spec le_spec
        notKey (s := q) (heap.symm ▸ rep) distinct ml mr hl hr hL (qp0.trans cursor) rfl
      exact ⟨t, tree, time, by simpa [testL, hL] using run, by omega, eff⟩
    · have selected : ∃ t tree time,
          Executes (if M.evalTest heavy (q.data 2) (q.data 1) then
            Balance.heavyCase false zero maxSucc le field
          else recomputeHeight zero maxSucc field) q t time ∧ time ≤ 106 ∧
          Effect q t (.node label l r) tree (AVLTree.balance (label.data 0) A B)
            encode field parent := by
        by_cases hR : A.cachedHeight + 1 < B.cachedHeight
        · obtain ⟨t, tree, time, run, bound, eff⟩ := heavyCase_correct true zero_spec max_spec
            le_spec notKey (s := q) (heap.symm ▸ rep) distinct mr ml hr hl hR (qp0.trans cursor) rfl
          exact ⟨t, tree, time, by simpa [testR, hR] using run, bound, eff⟩
        · obtain ⟨t, tree, run, eff⟩ := height_correct zero maxSucc encode zero_spec max_spec
            field notKey q label l r A B parent (heap.symm ▸ rep) distinct ml mr hl hr
            (qp0.trans cursor) rfl qs
          exact ⟨t, tree, 9, by simpa [testR, hR] using run, by omega,
            by simpa [AVLTree.balance, hL, hR] using eff⟩
      obtain ⟨t, tree, time, run, bound, eff⟩ := selected
      exact ⟨_, tree, time + 2,
        by simpa only [testL, decide_eq_false hL, Bool.false_eq_true, ↓reduceIte] using
          run.branch (pc := rfl), by omega, eff.withPc _⟩
  obtain ⟨t, tree, time, run, bound, eff⟩ := chosen
  have total := save.sequence (read.sequence (run.branch (pc := rfl)))
  have fin := eff.before heap qp0 qp1 data
  refine ⟨_, tree, _, total, by omega, fin.rep, fin.matched, fin.distinct, fin.footprint,
    ?_, fin.cursor, fin.top, fin.saved, fin.size, fin.data, fin.frame, ?_⟩
  · cases tree with
    | node => simp [root]
    | nil =>
      cases eq : AVLTree.balance (label.data 0) A B
      exacts [(balance_ne_nil _ _ _ eq).elim, (eq ▸ fin.matched).elim]
  · intro z f hf
    obtain ⟨_, steps, _, _⟩ := total
    apply steps.data_frame f
    simp only [Balance.heavyCase, Balance.readHeights, Balance.inChild, rotateRight, rotateLeft,
      rotationProgram, sequence_no_data_writes, branch_no_data_writes,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
    simp [recomputeHeight, readHeightsPrefix, SearchTree.PointerMachine.rotateRight,
      SearchTree.PointerMachine.rotateLeft, reconnect, Instr.WritesData, Ne.symm hf]

end Cslib.DataStructure.AVLTree.PointerMachine

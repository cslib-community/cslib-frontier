/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Structured.Rotation
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Reconnect

/-!
# AVL balancing as a structured pointer-machine program

`Structured.balance` rebalances the subtree at the cursor from the cached heights of its
children and grandchildren, in at most 85 instructions, and `balance_correct` proves that it
implements `AVLTree.balance`. The program allocates no nodes; it preserves every scalar payload
field except the height, and all records outside the tree.

The two mirror-image cases are one program, `heavyCase right`, and one proof. Each step of the
proof states only what the step rebuilds (`Rebuilt`); what the program leaves unchanged is read
off its text.

## Main definitions

* `inChild`, `heavyCase`, `balance`: run a program on a child and reconnect its result; a single
  or double rotation of a child that is too tall; the balancing program.

## Main results

* `balance_correct`: the program implements `AVLTree.balance`.
-/

public section

namespace Cslib.DataStructure.AVLTree.PointerMachine.Structured

open Cslib.PointerMachine SearchTree.PointerMachine
open Cslib.Program (ExecWithin.seq ExecWithin.branch_pos ExecWithin.branch_neg)

variable {M : Model} {extra regs : ℕ}

open SearchTree.PointerMachine.Structured (readHeights) in
open SearchTree.PointerMachine.Structured renaming recomputeHeight → updateHeight,
  reconnect → relink in
open Register in
/-- Run a program on the child of the cursor on the selected side, reconnect its result, then
return to the original parent. -/
@[expose] def inChild (right : Bool) (body : Code M (layout extra (regs + 1))) :
    Code M (layout extra (regs + 1)) :=
  let child := childField right
  pm[
    cur ← cur[child];
    ⟪body⟫;
    ⟪relink⟫;
    cur ← cur[parent] ]

open SearchTree.PointerMachine.Structured (readHeights) in
open SearchTree.PointerMachine.Structured renaming recomputeHeight → updateHeight,
  reconnect → relink in
open Register in
/-- The child on the selected side is too tall: promote it, after first promoting its inner
child when that one is the taller. -/
@[expose] def heavyCase (right : Bool) (zero maxSucc : M.Op) (le : M.Test)
    (field : Fin (extra + 1)) : Code M (layout extra (regs + 1)) :=
  let child := childField right
  let outer : Fin (regs + 1 + 2) := if right then 2 else 1
  let inner : Fin (regs + 1 + 2) := if right then 1 else 2
  pm[
    tall ← cur[child];
    ⟪readHeights zero field tall⟫;
    if le inner outer then [ ⟪rotate right zero maxSucc field⟫ ] else [
      ⟪inChild right (rotate (!right) zero maxSucc field)⟫;
      ⟪rotate right zero maxSucc field⟫ ] ]

open SearchTree.PointerMachine.Structured (readHeights) in
open SearchTree.PointerMachine.Structured renaming recomputeHeight → updateHeight,
  reconnect → relink in
open Register in
/-- Balance at cursor zero using cached child and grandchild heights. `heavy a b` means
`b + 1 < a`; `le` compares heights. Pointer register one and scalar register zero are client
registers; the other declared scratch registers may change. -/
@[expose] def balance (zero maxSucc : M.Op) (heavy le : M.Test) (field : Fin (extra + 1)) :
    Code M (layout extra (regs + 1)) := pm[
  old ← cur;
  ⟪readHeights zero field cur⟫;
  if heavy lh rh then [ ⟪heavyCase false zero maxSucc le field⟫ ] else [
    if heavy rh lh then [ ⟪heavyCase true zero maxSucc le field⟫ ]
    else [ ⟪updateHeight zero maxSucc field⟫ ] ] ]

/-- A rebuilt subtree, seen from an earlier state with the same records, cursor and root
register. -/
theorem _root_.Cslib.DataStructure.AVLTree.PointerMachine.Rebuilt.of_start
    {encode : ℕ → M.Value} {field : Fin (extra + 1)}
    {s q t : State M (layout extra (regs + 1))} {parent : Pointer}
    {old tree : BinaryTree (Label M extra)} {target : AVLTree M.Value}
    (h : Rebuilt encode field q t parent old tree target) (heap : q.heap = s.heap)
    (cursor : q.ptr 0 = s.ptr 0) (top : q.ptr 1 = s.ptr 1) :
    Rebuilt encode field s t parent old tree target :=
  { h with
    saved := h.saved.trans cursor
    top := h.top.trans top
    frame := fun z hz => (h.frame z hz).trans (by rw [heap]) }

/-- Rebuilding the child on a side and reconnecting it rebuilds the node, in ten more
instructions. -/
private theorem inChild_correct (right : Bool) (body : Code M (layout extra (regs + 1)))
    (encode : ℕ → M.Value) (field : Fin (extra + 1))
    (s t : State M (layout extra (regs + 1))) (label : Label M extra)
    (old new sibling : BinaryTree (Label M extra)) (parent : Pointer) (o time : ℕ)
    (target : AVLTree M.Value)
    (rep : Represents s.heap parent (nodeAt right label old sibling))
    (distinct : AddressesDistinct (nodeAt right label old sibling))
    (cursor : s.ptr 0 = some label.address) (hroot : root old = some o)
    (bodyExec : ExecWithin body (s.setPtr 0 (some o)) t time)
    (built : Rebuilt encode field (s.setPtr 0 (some o)) t (some label.address) old new target)
    (nonempty : new ≠ .nil) :
    ∃ u, ExecWithin (inChild right body) s u (time + 10) ∧
      Represents u.heap parent (nodeAt right label new sibling) ∧
      AddressesDistinct (nodeAt right label new sibling) ∧
      u.ptr 0 = some label.address ∧ u.ptr 1 = s.ptr 1 ∧
      ∀ z, z ∉ addresses (nodeAt right label old sibling) → u.heap[z]? = s.heap[z]? := by
  obtain ⟨hl, -, -⟩ := (represents_nodeAt_iff ..).mp rep
  obtain ⟨-, -, no, -, dis⟩ := (nodeAt_distinct_iff ..).mp distinct
  have nav : (Op.loadPtr 0 (childField right) 0).effect s = s.setPtr 0 (some o) := by
    cases right <;> simp [pm_simps, State.deref, cursor, hl, record, childField, hroot]
  obtain ⟨nl, c, d, rfl⟩ : ∃ nl c d, new = .node nl c d := by
    cases new with
    | nil => exact (nonempty rfl).elim
    | node nl c d => exact ⟨nl, c, d, rfl⟩
  have tcur : t.ptr 0 = some nl.address := built.cursor
  have read : t.deref 0 = some (record (root c) (root d) (some label.address) nl) := by
    simp [State.deref, tcur, built.rep.1]
  have saved : t.ptr 6 = some o := by simpa using built.saved
  obtain ⟨u, fld, connected, fields, oldLink, heap, -, ptr⟩ :=
    SearchTree.PointerMachine.Structured.reconnect_child t _ _ label.address read rfl
      ((built.frame _ no).trans hl) (by cases right <;> simp [record, saved, hroot])
  have fieldEq : fld = childField right := by
    have siblingNe : root sibling ≠ some o := fun e =>
      Finset.disjoint_left.mp dis (root_mem_addresses hroot) (root_mem_addresses e)
    rcases fields with rfl | rfl <;> cases right
    all_goals first
      | rfl
      | exact (siblingNe (by simpa [record, saved] using oldLink)).elim
  have semantic := replaceChild right s.heap t.heap label old (.node nl c d) sibling parent rep
    distinct built.rep built.distinct (by simpa only [built.footprint] using no)
    (by simpa only [built.footprint] using dis) built.frame
  rw [fieldEq, tcur] at heap
  have repU : Represents u.heap parent (nodeAt right label (.node nl c d) sibling) := by
    rw [heap]
    exact semantic.1
  have back : (Op.loadPtr 0 2 0).effect u = u.setPtr 0 (some label.address) := by
    have ucur : u.ptr 0 = some nl.address :=
      (ptr 0 (by simp [layout]) (by simp [layout]) (by simp [layout])).trans tcur
    have child := ((represents_nodeAt_iff ..).mp repU).2.1.1
    simp [pm_simps, State.deref, ucur, child, record]
  refine ⟨_, (ExecWithin.seq (ExecWithin.op_eq nav) (ExecWithin.seq bodyExec
    (ExecWithin.seq connected (ExecWithin.op_eq back)))).mono (by omega), repU, semantic.2.1,
    by simp, ?_, fun z hz => ?_⟩
  · have keep := ptr 1 (by simp [layout]) (by simp [layout]) (by simp [layout])
    simpa [keep] using built.top
  · rw [State.heap_setPtr, heap]
    exact semantic.2.2 z hz

/-- A double rotation: promote the inner grandchild twice. -/
private theorem double_correct (right : Bool) (zero maxSucc : M.Op) (encode : ℕ → M.Value)
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
    (nonempty : N ≠ .nil) (cursor : s.ptr 0 = some label.address) :
    ∃ t tree, ExecWithin (.seq (inChild right (rotate (!right) zero maxSucc field))
        (rotate right zero maxSucc field)) s t 66 ∧
      Rebuilt encode field s t parent (nodeAt right label (nodeAt right child outer inner) sibling)
        tree (rotateAt right (label.data 0) (rotateAt (!right) (child.data 0) N O) S) := by
  obtain ⟨pv, p, q, rfl⟩ : ∃ pv p q, inner = nodeAt (!right) pv p q := by
    cases inner with
    | nil => cases N <;> simp_all [Matches]
    | node pv l r => cases right <;> [exact ⟨pv, r, l, rfl⟩; exact ⟨pv, l, r, rfl⟩]
  obtain ⟨h, P, Q, rfl, -, mp, mq⟩ := matches_nodeAt mn
  obtain ⟨hP, hQ⟩ := hn.of_nodeSide
  have view : nodeAt right child outer (nodeAt (!right) pv p q) =
      nodeAt (!right) child (nodeAt (!right) pv p q) outer := (nodeAt_not ..).symm
  obtain ⟨-, hchild, -⟩ := (represents_nodeAt_iff ..).mp rep
  obtain ⟨dchild, -, -, -, -⟩ := (nodeAt_distinct_iff ..).mp distinct
  rw [view] at hchild dchild
  -- Promote the inner grandchild over the child.
  obtain ⟨u, pv', child', run₁, ⟨-, pk⟩, -, built₁⟩ := rotate_correct (!right) zero maxSucc
    encode zero_spec max_spec field notKey (s.setPtr 0 (some child.address)) pv child p q outer
    P Q O (some label.address) hchild dchild mp mq mo hP hQ ho (by simp)
  rw [← view] at built₁
  obtain ⟨v, run₂, repv, dv, curv, topv, framev⟩ := inChild_correct right _ encode field s u
    label _ _ sibling parent child.address 28 _ rep distinct cursor (by simp) run₁ built₁
    (by cases right <;> simp [nodeAt])
  have view' := nodeAt_not right pv' (nodeAt (!right) child' q outer) p
  rw [view'] at repv dv
  -- Promote it again, over the root.
  obtain ⟨t, x', y', run₃, -, -, built₃⟩ := rotate_correct right zero maxSucc encode zero_spec
    max_spec field notKey v pv' label _ p sibling _ P S parent repv dv
    (matches_nodeAt_mkNodeAt built₁.matched).2 mp ms (heightConsistent_mkNodeAt _ hQ ho) hP hs
    curv
  have inside : addresses (nodeAt right pv' (nodeAt (!right) child' q outer) p) =
      addresses (nodeAt right child outer (nodeAt (!right) pv p q)) := by
    rw [← view', built₁.footprint]
  refine ⟨t, _, (ExecWithin.seq run₂ run₃).mono (by omega), ⟨built₃.rep, ?_, built₃.distinct, ?_,
    built₃.cursor, built₃.saved.trans (curv.trans cursor.symm), built₃.top.trans topv,
    fun z hz => ?_⟩⟩
  · rw [rotateAt_nodeSide, mkNodeAt_eq_nodeSide (!right) (pv.data 0) P, nodeSide_not,
      rotateAt_nodeSide, ← pk]
    exact built₃.matched
  · rw [built₃.footprint, nodeAt_addresses right label, nodeAt_addresses right label, inside]
  · rw [built₃.frame z (by
      rw [nodeAt_addresses right label, inside, ← nodeAt_addresses right label]
      exact hz), framev z hz]

/-- The heavy case: a single or a double rotation of the child that is too tall, chosen by
comparing the cached heights of its children. -/
private theorem heavy_correct (right : Bool) (zero maxSucc : M.Op) (le : M.Test)
    (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (label child : Label M extra)
    (outer inner sibling : BinaryTree (Label M extra)) (O N S : AVLTree M.Value)
    (parent : Pointer) (h : ℕ)
    (rep : Represents s.heap parent (nodeAt right label (nodeAt right child outer inner) sibling))
    (distinct : AddressesDistinct (nodeAt right label (nodeAt right child outer inner) sibling))
    (mo : Matches encode field outer O) (mn : Matches encode field inner N)
    (ms : Matches encode field sibling S)
    (ho : O.HeightConsistent) (hn : N.HeightConsistent) (hs : S.HeightConsistent)
    (cursor : s.ptr 0 = some label.address) :
    ∃ t tree, ExecWithin (heavyCase right zero maxSucc le field) s t 75 ∧
      Rebuilt encode field s t parent (nodeAt right label (nodeAt right child outer inner) sibling)
        tree
        (if N.cachedHeight ≤ O.cachedHeight then
          rotateAt right (label.data 0) (nodeSide right (child.data 0) h O N) S
        else rotateAt right (label.data 0) (rotateAt (!right) (child.data 0) N O) S) := by
  obtain ⟨hl, hchild, -⟩ := (represents_nodeAt_iff ..).mp rep
  have nav : (Op.loadPtr 3 (childField right) 0).effect s = s.setPtr 3 (some child.address) := by
    cases right <;> simp [pm_simps, State.deref, cursor, hl, record, childField]
  obtain ⟨q, read, qheap, d1, d2, -, qptr⟩ :=
    SearchTree.PointerMachine.Structured.readHeights_exec zero (encode 0) zero_spec field 3
      (by decide) (s.setPtr 3 (some child.address)) child (if right then inner else outer)
      (if right then outer else inner) (some label.address) (by cases right <;> exact hchild)
      (by simp)
  have qcur : q.ptr 0 = some label.address := (qptr 0 (by simp [layout])).trans (by simp [cursor])
  have qtop : q.ptr 1 = s.ptr 1 := (qptr 1 (by simp [layout])).trans (by simp)
  have qrep : Represents q.heap parent
      (nodeAt right label (nodeAt right child outer inner) sibling) := by
    rw [qheap]
    exact rep
  have test : M.evalTest le (q.data (if right then 1 else 2)) (q.data (if right then 2 else 1)) =
      decide (N.cachedHeight ≤ O.cachedHeight) := by
    cases right <;> simp [d1, d2, mo.heightValue, mn.heightValue, le_spec]
  by_cases hle : N.cachedHeight ≤ O.cachedHeight
  · obtain ⟨t, x', y', run, -, -, built⟩ := rotate_correct right zero maxSucc encode zero_spec
      max_spec field notKey q child label outer inner sibling O N S parent qrep distinct mo mn ms
      ho hn hs qcur
    refine ⟨t, nodeAt right x' outer (nodeAt right y' inner sibling),
      (ExecWithin.seq (ExecWithin.op_eq nav) (ExecWithin.seq read
      (ExecWithin.branch_pos
        (show Test.Holds q (Test.data le (if right then 1 else 2) (if right then 2 else 1)) from
          test.trans (decide_eq_true hle)) run))).mono (by omega), ?_⟩
    simp only [hle, ↓reduceIte, rotateAt_nodeSide]
    exact built.of_start qheap (qcur.trans cursor.symm) qtop
  · obtain ⟨t, tree, run, built⟩ := double_correct right zero maxSucc encode zero_spec max_spec
      field notKey q label child outer inner sibling O N S parent qrep distinct mo mn ms ho hn hs
      (by rintro rfl; simp at hle) qcur
    refine ⟨t, tree, (ExecWithin.seq (ExecWithin.op_eq nav) (ExecWithin.seq read
      (ExecWithin.branch_neg
        (fun holds :
            Test.Holds q (Test.data le (if right then 1 else 2) (if right then 2 else 1)) =>
          hle (of_decide_eq_true (test.symm.trans holds))) run))).mono (by omega), ?_⟩
    simp only [hle, ↓reduceIte]
    exact built.of_start qheap (qcur.trans cursor.symm) qtop

/-! Frames of `balance`, read off its text. Each is evaluated in a declaration of its own: the
program has 230 instructions, which exceeds the default recursion depth. Larger programs get
their frames from these by `simp`. -/

-- The program has 230 instructions; evaluating its frame exceeds the default depth.
set_option maxRecDepth 8192 in
/-- `balance` creates no record. -/
theorem balance_keepsSize (zero maxSucc : M.Op) (heavy le : M.Test) (field : Fin (extra + 1)) :
    (balance (regs := regs) zero maxSucc heavy le field).KeepsSize := by
  pm_frame

-- The program has 230 instructions; evaluating its frame exceeds the default depth.
set_option maxRecDepth 8192 in
/-- `balance` assigns only data registers one and two. -/
theorem balance_dataDests (zero maxSucc : M.Op) (heavy le : M.Test) (field : Fin (extra + 1)) :
    (balance (regs := regs) zero maxSucc heavy le field).dataDests ⊆ [1, 2] := by
  pm_frame

-- The program has 230 instructions; evaluating its frame exceeds the default depth.
set_option maxRecDepth 8192 in
/-- `balance` stores only into the height field. -/
theorem balance_fieldDests (zero maxSucc : M.Op) (heavy le : M.Test) (field : Fin (extra + 1)) :
    ∀ f ∈ (balance (regs := regs) zero maxSucc heavy le field).fieldDests, f = field :=
  fun _ hf => List.eq_of_mem_replicate (n := 13) hf

/-- The balance program implements `AVLTree.balance` in at most 85 instructions, without
allocation. Children must have consistent encoded caches; the old root cache may be arbitrary.
Register six retains the former root for the caller's subsequent reconnection. -/
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
    (cursor : s.ptr 0 = some label.address) :
    ∃ t tree, ExecWithin (balance zero maxSucc heavy le field) s t 85 ∧
      Represents t.heap parent tree ∧
      Matches encode field tree (AVLTree.balance (label.data 0) A B) ∧
      AddressesDistinct tree ∧ addresses tree = addresses (.node label l r) ∧
      root tree ≠ none ∧ t.ptr 0 = root tree ∧ t.ptr 1 = s.ptr 1 ∧ t.ptr 6 = s.ptr 0 ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ z, z ∉ addresses (.node label l r) → t.heap[z]? = s.heap[z]?) ∧
      (∀ (z : ℕ) (f : Fin (extra + 1)), f ≠ field →
        (t.heap[z]?).map (fun n => n.data f) = (s.heap[z]?).map (fun n => n.data f)) := by
  obtain ⟨q, read, qheap, d1, d2, -, qptr⟩ :=
    SearchTree.PointerMachine.Structured.readHeights_exec zero (encode 0) zero_spec field 0
      (by decide) (s.setPtr 6 (s.ptr 0)) label l r parent rep (by simpa using cursor)
  have qcur : q.ptr 0 = some label.address := (qptr 0 (by simp [layout])).trans (by simp [cursor])
  have qtop : q.ptr 1 = s.ptr 1 := (qptr 1 (by simp [layout])).trans (by simp)
  have q6 : q.ptr 6 = q.ptr 0 :=
    ((qptr 6 (by simp [layout])).trans (by simp [cursor])).trans qcur.symm
  have qrep : Represents q.heap parent (.node label l r) := by
    rw [qheap]
    exact rep
  have testL : M.evalTest heavy (q.data 1) (q.data 2) =
      decide (B.cachedHeight + 1 < A.cachedHeight) := by
    rw [d1, d2, ml.heightValue, mr.heightValue, heavy_spec]
  have testR : M.evalTest heavy (q.data 2) (q.data 1) =
      decide (A.cachedHeight + 1 < B.cachedHeight) := by
    rw [d1, d2, ml.heightValue, mr.heightValue, heavy_spec]
  have core : ∃ t tree,
      ExecWithin (.branch (.data heavy 1 2) (heavyCase false zero maxSucc le field)
        (.branch (.data heavy 2 1) (heavyCase true zero maxSucc le field)
          (SearchTree.PointerMachine.Structured.recomputeHeight zero maxSucc field))) q t 78 ∧
      Rebuilt encode field q t parent (.node label l r) tree
        (AVLTree.balance (label.data 0) A B) := by
    by_cases hL : B.cachedHeight + 1 < A.cachedHeight
    · cases A with
      | nil => simp at hL
      | node key h AL AR =>
        cases l with
        | nil => cases ml
        | node child a b =>
          obtain ⟨keyEq, -, ma, mb⟩ := ml
          obtain ⟨-, ha, hb⟩ := hl
          obtain ⟨t, tree, run, built⟩ := heavy_correct false zero maxSucc le encode zero_spec
            max_spec le_spec field notKey q label child a b r AL AR B parent h qrep distinct ma mb
            mr ha hb hr qcur
          refine ⟨t, tree, (ExecWithin.branch_pos (t := Test.data heavy 1 2)
            (testL.trans (decide_eq_true hL)) run).mono (by omega), ?_⟩
          have e : AVLTree.balance (label.data 0) (.node key h AL AR) B = _ :=
            balanceAt_heavy false (label.data 0) key h AL AR B hL
          rw [e, ← keyEq]
          exact built
    · have notL : ¬(Test.data heavy 1 2 : Test M (layout extra (regs + 1))).Holds q :=
        fun holds => hL (of_decide_eq_true (testL.symm.trans holds))
      by_cases hR : A.cachedHeight + 1 < B.cachedHeight
      · cases B with
        | nil => simp at hR
        | node key h BL BR =>
          cases r with
          | nil => cases mr
          | node child a b =>
            obtain ⟨keyEq, -, ma, mb⟩ := mr
            obtain ⟨-, ha, hb⟩ := hr
            obtain ⟨t, tree, run, built⟩ := heavy_correct true zero maxSucc le encode zero_spec
              max_spec le_spec field notKey q label child b a l BR BL A parent h qrep distinct mb
              ma ml hb ha hl qcur
            refine ⟨t, tree, (ExecWithin.branch_neg notL (ExecWithin.branch_pos
              (t := Test.data heavy 2 1) (testR.trans (decide_eq_true hR)) run)).mono
              (by omega), ?_⟩
            have e : AVLTree.balance (label.data 0) A (.node key h BL BR) = _ :=
              balanceAt_heavy true (label.data 0) key h BR BL A hR
            rw [e, ← keyEq]
            exact built
      · have notR : ¬(Test.data heavy 2 1 : Test M (layout extra (regs + 1))).Holds q :=
          fun holds => hR (of_decide_eq_true (testR.symm.trans holds))
        obtain ⟨t, run, heap, rt, mt, dt, -⟩ := recomputeHeight_mkNode zero maxSucc encode
          zero_spec max_spec field notKey q label l r A B parent qrep distinct ml mr hl hr qcur
        refine ⟨t, _, (ExecWithin.branch_neg notL (ExecWithin.branch_neg notR run)).mono
          (by omega), ⟨rt, ?_, dt, rfl, ?_, ?_, run.ptr_keep [2] (by pm_frame) (by simp),
          fun z hz => ?_⟩⟩
        · simpa [AVLTree.balance, hL, hR] using mt
        · exact (run.ptr_keep [2] (by pm_frame) (by simp)).trans qcur
        · exact (run.ptr_keep [2] (by pm_frame) (by simp)).trans q6
        · rw [heap]
          exact List.getElem?_modify_ne _ _ fun e =>
            hz ((mem_addresses_iff ..).mpr ⟨.one, label, rfl, e⟩)
  obtain ⟨t, tree, run, built⟩ := core
  have total : ExecWithin (balance zero maxSucc heavy le field) s t 85 :=
    (ExecWithin.seq (ExecWithin.op_eq rfl) (ExecWithin.seq read run)).mono (by omega)
  have built := built.of_start qheap (qcur.trans cursor.symm) qtop
  have size := balance_keepsSize (regs := regs) zero maxSucc heavy le field
  refine ⟨t, tree, total, built.rep, built.matched, built.distinct, built.footprint, ?_,
    built.cursor, built.top, built.saved, total.length_eq size,
    fun i h1 h2 => total.data_keep [1, 2] (balance_dataDests zero maxSucc heavy le field)
      (by simp [h1, h2]),
    built.frame, fun z f hf => total.field_keep size
      (fun h => hf (balance_fieldDests zero maxSucc heavy le field f h)) z⟩
  cases tree with
  | node => simp [root]
  | nil =>
    have matched := built.matched
    cases eq : AVLTree.balance (label.data 0) A B with
    | nil => exact (balance_ne_nil _ _ _ eq).elim
    | node => simp [eq, Matches] at matched

end Cslib.DataStructure.AVLTree.PointerMachine.Structured

/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Balance
public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Context
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.ReconnectContext
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Seek
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.InsertLeaf
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Graft

/-!
# Pointer-machine AVL insertion

The insertion program searches with a parent cursor, initializes and attaches one new leaf on a
miss, and balances ancestors by following parent links. Comparisons and height operations are
scalar primitives. Ghost contexts describe the proof; the program uses only fixed registers.
-/

public section
namespace Cslib.DataStructure.AVLTree.PointerMachine
open Cslib.PointerMachine SearchTree.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Scalar sources for a new AVL leaf: query register zero, initialized height register one,
and explicit client sources for all remaining fields. -/
@[expose] def leafRegisters (field : Fin (extra + 1))
    (source : Fin (extra + 1) → Fin (regs + 3)) (f : Fin (extra + 1)) : Fin (regs + 3) :=
  if f = field then 1 else if f = 0 then 0 else source f

/-- Initialize a height-one leaf, choose its child link by comparison with the parent key,
and allocate and attach it. A null parent installs the whole-tree root. -/
@[expose] def createLeaf (zero maxSucc : M.Op) (lt : M.Test) (field : Fin (extra + 1))
    (source : Fin (extra + 1) → Fin (regs + 3)) :
    List (Instr M (layout extra (regs + 1))) :=
  sequence [.op zero 1 0 0, .op maxSucc 1 1 1, .loadData 2 0 2, .halt]
    (branch lt 0 2 (insertLeaf (leafRegisters field source) 0)
      (insertLeaf (leafRegisters field source) 1))

/-- Balance the current ancestor, reconnect its new root, and move to its parent.
The enclosing loop decides whether another ancestor exists. -/
@[expose] def ancestorStep (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) : List (Instr M (layout extra (regs + 1))) :=
  sequence (balance zero maxSucc heavy le field)
    (sequence reconnect [.loadPtr 0 2 0, .halt])

/-- Follow parent links, balancing and reconnecting every ancestor until the cursor is null. -/
@[expose] def rebalanceAncestors (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) : List (Instr M (layout extra (regs + 1))) :=
  let body := ancestorStep zero maxSucc heavy le field
  [.null 5, .ifPtrEq 0 5 (2 + body.length)] ++
    body.map (Instr.relocate 2 0) ++ [.halt]

/-- On an unsuccessful search, create a leaf and repair its ancestors. A successful search
halts without allocating or changing the tree. -/
@[expose] def insertAfterSeek (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3)) :
    List (Instr M (layout extra (regs + 1))) :=
  let missing := sequence (createLeaf zero maxSucc lt field source)
    (sequence [.loadPtr 0 2 0, .halt] (rebalanceAncestors zero maxSucc heavy le field))
  [.null 5, .ifPtrEq 0 5 3, .halt] ++
    missing.map (Instr.relocate 3 (3 + missing.length)) ++ [.halt]

/-- Insert the query in data register zero into the AVL tree at cursor zero. Root register one
tracks the whole tree. All extra leaf payload sources are explicit. -/
@[expose] def insert (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3)) :
    List (Instr M (layout extra (regs + 1))) :=
  sequence (seek lt) (insertAfterSeek zero maxSucc lt heavy le field source)

private theorem initialize_correct (zero maxSucc : M.Op) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (s : State M (layout extra (regs + 1))) (pc : s.pc = 0) :
    let parentKey := ((s.deref 2).map (fun n => n.data 0)).getD (s.data 2)
    Executes [.op zero 1 0 0, .op maxSucc 1 1 1, .loadData 2 0 2, .halt] s
      { (s.setData 1 (encode 1)).setData 2 parentKey with pc := 3 } 4 := by
  let a := { s.setData 1 (encode 0) with pc := 1 }
  let b := { s.setData 1 (encode 1) with pc := 2 }
  refine ⟨3, .head s a _ _ ?_ (.head a b _ _ ?_ (.single ?_)), rfl, rfl⟩
  · simp [step, Instr.effect, Instr.next, pc, a, zero_spec]
  · simp [step, Instr.effect, Instr.next, a, b, State.setData, max_spec,
      Function.update_idem]
  · have h21 : (2 : Fin ((regs + 1) + 2)) ≠ 1 := by
      simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < (regs + 1) + 2)]
    cases h : s.deref 2 <;>
      simp only [State.deref] at h <;>
      simp [step, Instr.effect, Instr.next, b, State.setData, State.deref, h, h21]

private theorem createLeaf_correct [LinearOrder M.Value] (zero maxSucc : M.Op)
    (lt : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (source : Fin (extra + 1) → Fin (regs + 3))
    (safe : ∀ f, f ≠ field → f ≠ 0 → source f ≠ 1 ∧ source f ≠ 2)
    (s : State M (layout extra (regs + 1))) (pc : s.pc = 0)
    (vacant : match s.ptr 2 with
      | none => s.ptr 1 = none
      | some a => ∃ par, s.heap[a]? = some par ∧
          par.ptr (if M.evalTest lt (s.data 0) (par.data 0) then 0 else 1) = none) :
    let label : Label M extra := ⟨s.heap.length,
      fun f => if f = field then encode 1 else if f = 0 then s.data 0 else s.data (source f)⟩
    let parentKey := ((s.deref 2).map (fun n => n.data 0)).getD (s.data 2)
    let side : Fin 2 := if M.evalTest lt (s.data 0) parentKey then 0 else 1
    ∃ t, Executes (createLeaf zero maxSucc lt field source) s t (extra + 16) ∧
      t.heap = (match s.ptr 2 with
        | none => s.heap ++ [record none none (s.ptr 2) label]
        | some a => (s.heap ++ [record none none (s.ptr 2) label]).modify a
            (fun n => { n with ptr := Function.update n.ptr side.castSucc (some s.heap.length) })) ∧
      Represents t.heap (s.ptr 2) (.node label .nil .nil) ∧
      Matches encode field (.node label .nil .nil) (AVLTree.insert (s.data 0) .nil) ∧
      t.heap.length = s.heap.length + 1 ∧ t.ptr 0 = some s.heap.length ∧
      t.ptr 1 = (if s.ptr 2 = none then some s.heap.length else s.ptr 1) ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 5 → t.ptr i = s.ptr i) := by
  dsimp only
  let parentKey := ((s.deref 2).map (fun n => n.data 0)).getD (s.data 2)
  let side : Fin 2 := if M.evalTest lt (s.data 0) parentKey then 0 else 1
  let label : Label M extra := ⟨s.heap.length,
    fun f => if f = field then encode 1 else if f = 0 then s.data 0 else s.data (source f)⟩
  let initialized := { (s.setData 1 (encode 1)).setData 2 parentKey with pc := 3 }
  let q := { initialized with pc := 0 }
  have init := initialize_correct zero maxSucc encode zero_spec max_spec s pc
  have h01 : (0 : Fin (regs + 3)) ≠ 1 := by simp
  have h02 : (0 : Fin (regs + 3)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < regs + 3)]
  have h12 : (1 : Fin (regs + 3)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < regs + 3)]
  have keyData : (fun f => q.data (leafRegisters field source f)) = label.data := by
    funext f
    by_cases hf : f = field
    · subst f; simp [q, initialized, State.setData, leafRegisters, label, h12]
    · by_cases hk : f = 0
      · subst f; simp [q, initialized, State.setData, leafRegisters, label, hf, h01, h02]
      · simp [q, initialized, State.setData, leafRegisters, label, hf, hk,
          (safe f hf hk).1, (safe f hf hk).2]
  have vacancy : match q.ptr 2 with
      | none => q.ptr 1 = none
      | some a => ∃ par, q.heap[a]? = some par ∧ par.ptr side.castSucc = none := by
    change match s.ptr 2 with
      | none => s.ptr 1 = none
      | some a => ∃ par, s.heap[a]? = some par ∧ par.ptr side.castSucc = none
    cases hp : s.ptr 2 with
    | none => simpa [hp] using vacant
    | some a =>
      rw [hp] at vacant
      obtain ⟨par, get, slot⟩ := vacant
      refine ⟨par, get, ?_⟩
      cases h : M.evalTest lt (s.data 0) (par.data 0) <;>
        simpa [side, parentKey, State.deref, hp, get, h] using slot
  obtain ⟨t, run, heap, rep, size, cursor, rootReg, data, _, ptr, _⟩ :=
    insertLeaf_correct (leafRegisters field source) side q rfl vacancy
  have selected : Executes
      (if M.evalTest lt (q.data 0) (q.data 2) then
        insertLeaf (leafRegisters field source) 0 else insertLeaf (leafRegisters field source) 1)
      q t (extra + 9) := by
    cases h : M.evalTest lt (s.data 0) parentKey <;>
      simpa [q, initialized, State.setData, h01, h02, side, h] using run
  have branched := selected.branch lt 0 2 _ _ rfl
  have execution := init.sequence branched
  let result := { t with pc := 4 +
    (branch lt 0 2 (insertLeaf (leafRegisters field source) 0)
      (insertLeaf (leafRegisters field source) 1)).length }
  refine ⟨result, ?_, ?_, ?_, ?_, size, cursor, rootReg, ?_, ptr⟩
  · convert execution using 1 <;> first | rfl | omega
  · rw [keyData] at heap
    exact heap
  · rw [keyData] at rep
    exact rep
  · simp [Matches, AVLTree.insert, mkNode, Ne.symm notKey]
  · intro i h1 h2
    simp [result, data, q, initialized, State.setData, h1, h2]

private theorem ancestorStep_correct (zero maxSucc : M.Op) (heavy le : M.Test)
    (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (heavy_spec : ∀ a b, M.evalTest heavy (encode a) (encode b) = decide (b + 1 < a))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (s : State M (layout extra (regs + 1))) (cs : List (Frame M extra))
    (label : Label M extra) (l r : BinaryTree (Label M extra)) (L R : AVLTree M.Value)
    (rep : Represents s.heap none (plug cs (.node label l r)))
    (distinct : AddressesDistinct (plug cs (.node label l r)))
    (ml : Matches encode field l L) (mr : Matches encode field r R)
    (hl : L.HeightConsistent) (hr : R.HeightConsistent)
    (cursor : s.ptr 0 = some label.address) (rootReg : s.ptr 1 = root (plug cs (.node label l r)))
    (pc : s.pc = 0) :
    ∃ t tree time, Executes (ancestorStep zero maxSucc heavy le field) s t time ∧ time ≤ 132 ∧
      Represents t.heap none (plug cs tree) ∧
      Matches encode field tree (AVLTree.balance (label.data 0) L R) ∧
      AddressesDistinct (plug cs tree) ∧ addresses tree = addresses (.node label l r) ∧
      t.ptr 0 = contextParent cs ∧ t.ptr 1 = root (plug cs tree) ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ (a : ℕ) (f : Fin (extra + 1)), f ≠ field → (t.heap[a]?).map (fun n => n.data f) =
        (s.heap[a]?).map (fun n => n.data f)) := by
  obtain ⟨b, tree, tb, eb, bb, rb, mb, db, ab, nonempty, cb, rootB, saved, sizeB,
      dataB, frameB, payloadB⟩ := balance_correct zero maxSucc heavy le encode
    zero_spec max_spec heavy_spec le_spec field notKey s label l r L R (contextParent cs)
    ((represents_plug_iff ..).mp rep).1 (distinct.focus) ml mr hl hr cursor pc
  obtain ⟨c, tc, ec, bc, resultC⟩ := reconnect_context s.heap { b with pc := 0 } cs
    (.node label l r) tree rep distinct rb db ab frameB (by simp)
    (by intro eq; simp [eq, root] at nonempty) rfl cb (saved.trans cursor)
    (rootB.trans rootReg)
  cases tree with
  | nil => simp [root] at nonempty
  | node a left right =>
    have rc := ((represents_plug_iff c.heap cs (.node a left right)).mp resultC.rep).1
    obtain ⟨d, ed, heapD, dataD, cursorD, ptrD⟩ :=
      ascend_correct { c with pc := 0 } cs a left right rc
        (resultC.cursor.trans cb) rfl
    have run := eb.sequence (ec.sequence ed)
    let out := { d with pc := (balance (regs := regs) zero maxSucc heavy le field).length +
      (sequence (reconnect (M := M) (extra := extra) (regs := regs + 1))
        [.loadPtr 0 2 0, .halt]).length }
    refine ⟨out, .node a left right, tb + (tc + 2 + 1) + 1, run, by omega,
      ?_, mb, resultC.distinct, ab, cursorD, ?_, ?_, ?_, ?_⟩
    · simpa only [out, heapD] using resultC.rep
    · exact (ptrD 1 (by simp [layout])).trans resultC.root
    · exact (congrArg List.length heapD).trans (resultC.size.trans sizeB)
    · intro i h1 h2
      exact (congrFun dataD i).trans ((congrFun resultC.data i).trans (dataB i h1 h2))
    · intro z f hf
      change (d.heap[z]?).map (fun n => n.data f) = _
      rw [heapD, resultC.payload]
      exact payloadB z f hf

private theorem nullLoop_done (body : List (Instr M (layout extra (regs + 1))))
    (s : State M (layout extra (regs + 1))) (pc : s.pc = 0) (cursor : s.ptr 0 = none) :
    Executes ([.null 5, .ifPtrEq 0 5 (2 + body.length)] ++
      body.map (Instr.relocate 2 0) ++ [.halt]) s
      { s.setPtr 5 none with pc := 2 + body.length } 3 := by
  let mid := { s.setPtr 5 none with pc := 1 }
  refine ⟨2, .head s mid _ _ ?_ (.single ?_), ?_, rfl⟩
  · simp [step, pc, Instr.effect, Instr.next, mid]
  · simp [step, mid, Instr.effect, Instr.next, State.setPtr, cursor]
  · rw [Nat.add_comm 2 body.length]
    simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by simp)]
    simp

private theorem rebalance_done (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) (s : State M (layout extra (regs + 1)))
    (pc : s.pc = 0) (cursor : s.ptr 0 = none) :
    Executes (rebalanceAncestors zero maxSucc heavy le field) s
      { s.setPtr 5 none with pc := 2 +
        (ancestorStep (regs := regs) zero maxSucc heavy le field).length } 3 := by
  simpa only [rebalanceAncestors] using
    nullLoop_done (ancestorStep zero maxSucc heavy le field) s pc cursor

private theorem rebalance_step (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) (s t : State M (layout extra (regs + 1)))
    (time : ℕ) (pc : s.pc = 0) (cursor : s.ptr 0 ≠ none)
    (run : Executes (ancestorStep zero maxSucc heavy le field)
      { s.setPtr 5 none with pc := 0 } t time) :
    Runs (rebalanceAncestors zero maxSucc heavy le field) s { t with pc := 0 } (2 + time) := by
  let body := ancestorStep (regs := regs) zero maxSucc heavy le field
  let mid := { s.setPtr 5 none with pc := 1 }
  have bodyRun := run.inBlock [.null 5, .ifPtrEq 0 5 (2 + body.length)] [.halt] 0
  have bodyRun' : Runs (rebalanceAncestors zero maxSucc heavy le field)
      { s.setPtr 5 none with pc := 2 } { t with pc := 0 } time := by
    simpa [rebalanceAncestors, body] using bodyRun
  rw [show 2 + time = time + 1 + 1 by omega]
  refine .head s mid _ _ ?_ (.head mid _ _ _ ?_ bodyRun')
  · simp [step, rebalanceAncestors, pc, Instr.effect, Instr.next, mid]
  · simp [step, rebalanceAncestors, mid, Instr.effect, Instr.next, State.setPtr, cursor]

private theorem rebalance_correct [LinearOrder M.Value]
    (zero maxSucc : M.Op) (heavy le : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (heavy_spec : ∀ a b, M.evalTest heavy (encode a) (encode b) = decide (b + 1 < a))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (cs : List (Frame M extra)) (before after : BinaryTree (Label M extra))
    (original focused : AVLTree M.Value) (query : M.Value)
    (originalMatch : Matches encode field (plug cs before) original) (valid : original.Valid)
    (focusedMatch : Matches encode field before focused) (focusedValid : focused.Valid)
    (changedMatch : Matches encode field after (AVLTree.insert query focused))
    (path : SearchPath query cs) (s : State M (layout extra (regs + 1)))
    (rep : Represents s.heap none (plug cs after))
    (distinct : AddressesDistinct (plug cs after))
    (cursor : s.ptr 0 = contextParent cs) (rootReg : s.ptr 1 = root (plug cs after))
    (pc : s.pc = 0) :
    ∃ t tree time, Executes (rebalanceAncestors zero maxSucc heavy le field) s t time ∧
      time ≤ 134 * cs.length + 3 ∧ Represents t.heap none tree ∧
      Matches encode field tree (AVLTree.insert query original) ∧ AddressesDistinct tree ∧
      addresses tree = addresses (plug cs after) ∧ t.ptr 0 = none ∧ t.ptr 1 = root tree ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ (a : ℕ) (f : Fin (extra + 1)), f ≠ field → (t.heap[a]?).map (fun n => n.data f) =
        (s.heap[a]?).map (fun n => n.data f)) := by
  induction cs generalizing before after focused s with
  | nil =>
    have same : focused = original :=
      focusedValid.heightConsistent.eq_of_toBinaryTree_eq valid.heightConsistent
        (focusedMatch.keys.symm.trans originalMatch.keys)
    refine ⟨_, after, 3, rebalance_done zero maxSucc heavy le field s pc cursor,
      by simp, rep, ?_, distinct, rfl, ?_, rootReg, rfl, ?_, ?_⟩
    · simpa only [same] using changedMatch
    · simpa [State.setPtr, contextParent] using cursor
    · intro i _ _; rfl
    · intro a f _; rfl
  | cons frame cs ih =>
    let oldParent := match frame with
      | .left label sibling => BinaryTree.node label before sibling
      | .right sibling label => .node label sibling before
    let newParent := match frame with
      | .left label sibling => BinaryTree.node label after sibling
      | .right sibling label => .node label sibling after
    have originalParent : Matches encode field (plug cs oldParent) original := by
      cases frame <;> exact originalMatch
    obtain ⟨parentAVL, parentMatch, parentValid⟩ := originalParent.exists_valid_focus valid
    let cleared := { s.setPtr 5 none with pc := 0 }
    have currentRep : Represents cleared.heap none (plug cs newParent) := by
      cases frame <;> exact rep
    have currentDistinct : AddressesDistinct (plug cs newParent) := by
      cases frame <;> exact distinct
    have currentRoot : cleared.ptr 1 = root (plug cs newParent) := by
      cases frame <;> simpa [cleared, State.setPtr, newParent, plug] using rootReg
    have chosen : ∃ t tree time,
        Executes (ancestorStep zero maxSucc heavy le field) cleared t time ∧ time ≤ 132 ∧
        Represents t.heap none (plug cs tree) ∧
        Matches encode field tree (AVLTree.insert query parentAVL) ∧
        AddressesDistinct (plug cs tree) ∧ addresses tree = addresses newParent ∧
        t.ptr 0 = contextParent cs ∧ t.ptr 1 = root (plug cs tree) ∧
        t.heap.length = s.heap.length ∧
        (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
        (∀ (a : ℕ) (f : Fin (extra + 1)), f ≠ field → (t.heap[a]?).map (fun n => n.data f) =
          (s.heap[a]?).map (fun n => n.data f)) := by
      cases frame with
      | left label sibling =>
        cases parentAVL with
        | nil => cases parentMatch
        | node key height left right =>
          obtain ⟨keyEq, _, leftMatch, rightMatch⟩ := parentMatch
          have leftEq : left = focused :=
            parentValid.heightConsistent.2.1.eq_of_toBinaryTree_eq focusedValid.heightConsistent
              (leftMatch.keys.symm.trans focusedMatch.keys)
          subst left
          have cur : cleared.ptr 0 = some label.address := by
            simpa [cleared, State.setPtr, contextParent] using cursor
          obtain ⟨t, tree, time, run, bound, rt, mt, dt, footprint, ct, rootT,
              size, data, payload⟩ :=
            ancestorStep_correct zero maxSucc heavy le encode zero_spec max_spec heavy_spec le_spec
              field notKey cleared cs label after sibling (AVLTree.insert query focused) right
              currentRep currentDistinct changedMatch rightMatch
              (valid_insert focusedValid query).heightConsistent parentValid.heightConsistent.2.2
              cur currentRoot rfl
          refine ⟨t, tree, time, run, bound, rt, ?_, dt, footprint, ct, rootT, size, data, payload⟩
          simpa only [AVLTree.insert, ← keyEq, path.1, ↓reduceIte] using mt
      | right sibling label =>
        cases parentAVL with
        | nil => cases parentMatch
        | node key height left right =>
          obtain ⟨keyEq, _, leftMatch, rightMatch⟩ := parentMatch
          have rightEq : right = focused :=
            parentValid.heightConsistent.2.2.eq_of_toBinaryTree_eq focusedValid.heightConsistent
              (rightMatch.keys.symm.trans focusedMatch.keys)
          subst right
          have cur : cleared.ptr 0 = some label.address := by
            simpa [cleared, State.setPtr, contextParent] using cursor
          obtain ⟨t, tree, time, run, bound, rt, mt, dt, footprint, ct, rootT,
              size, data, payload⟩ :=
            ancestorStep_correct zero maxSucc heavy le encode zero_spec max_spec heavy_spec le_spec
              field notKey cleared cs label sibling after left (AVLTree.insert query focused)
              currentRep currentDistinct leftMatch changedMatch
              parentValid.heightConsistent.2.1 (valid_insert focusedValid query).heightConsistent
              cur currentRoot rfl
          refine ⟨t, tree, time, run, bound, rt, ?_, dt, footprint, ct, rootT, size, data, payload⟩
          simpa only [AVLTree.insert, ← keyEq, not_lt_of_gt path.1, path.1, ↓reduceIte] using mt
    obtain ⟨a, tree, time, run, bound, rt, mt, dt, footprint, ct, rootA,
      size, data, payload⟩ := chosen
    have pathTail : SearchPath query cs := by cases frame <;> exact path.2
    obtain ⟨b, result, tb, eb, bb, rb, mb, db, ab, cb, rootB, sizeB, dataB, payloadB⟩ :=
      ih oldParent tree parentAVL originalParent parentMatch parentValid mt pathTail
        { a with pc := 0 } rt dt ct rootA rfl
    have nonempty : s.ptr 0 ≠ none := by cases frame <;> simp_all [contextParent]
    have first := rebalance_step zero maxSucc heavy le field s a time pc nonempty run
    obtain ⟨n, en, halt, cost⟩ := eb
    refine ⟨b, result, 2 + time + tb,
      ⟨2 + time + n, first.trans en, halt, by omega⟩, ?_, rb, mb, db, ?_,
      cb, rootB, sizeB.trans size, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [ab, addresses_plug, footprint, ← addresses_plug]
      cases frame <;> rfl
    · intro i h1 h2
      exact (dataB i h1 h2).trans (data i h1 h2)
    · intro z f hf
      exact (payloadB z f hf).trans (payload z f hf)

/-- Linked-tree, register and scalar-payload outcome of set insertion. Existing records retain
all scalar fields except the height cache; a new record receives its explicit client payload.
This contract does not assert a full frame for records outside the tree. -/
structure InsertResult [LinearOrder M.Value] (encode : ℕ → M.Value)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3))
    (s t : State M (layout extra (regs + 1)))
    (before after : BinaryTree (Label M extra)) (original : AVLTree M.Value) : Prop where
  /-- The output is a complete linked tree. -/
  rep : Represents t.heap none after
  /-- Its keys and height caches match the existing functional AVL insertion exactly. -/
  matched : Matches encode field after (AVLTree.insert (s.data 0) original)
  /-- Distinct tree positions still occupy distinct records. -/
  distinct : AddressesDistinct after
  /-- Register one tracks the final whole-tree root. -/
  root : t.ptr 1 = SearchTree.PointerMachine.root after
  /-- At most one record is allocated, and no record is removed. -/
  space : s.heap.length ≤ t.heap.length ∧ t.heap.length ≤ s.heap.length + 1
  /-- Old tree addresses survive, and the only possible new address is the fresh heap end. -/
  footprint : addresses before ⊆ addresses after ∧
    addresses after ⊆ Insert.insert s.heap.length (addresses before)
  /-- Query and client scalar registers survive; registers one and two are scratch. -/
  data : ∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i
  /-- Every old record retains all non-height scalar fields, even outside the tree. -/
  payload : ∀ (a : ℕ) (f : Fin (extra + 1)), a < s.heap.length → f ≠ field →
    (t.heap[a]?).map (fun n => n.data f) = (s.heap[a]?).map (fun n => n.data f)
  /-- When allocated, the fresh record retains the query and specified client payload. -/
  freshPayload : s.heap.length < t.heap.length → ∀ f, f ≠ field →
    (t.heap[s.heap.length]?).map (fun n => n.data f) =
      some (if f = 0 then s.data 0 else s.data (source f))

private theorem InsertResult.withPc [LinearOrder M.Value]
    {encode : ℕ → M.Value} {field : Fin (extra + 1)}
    {source : Fin (extra + 1) → Fin (regs + 3)} {s t : State M (layout extra (regs + 1))}
    {before after : BinaryTree (Label M extra)} {original : AVLTree M.Value}
    (h : InsertResult encode field source s t before after original) (pc : ℕ) :
    InsertResult encode field source s { t with pc } before after original :=
  ⟨h.rep, h.matched, h.distinct, h.root, h.space, h.footprint, h.data, h.payload, h.freshPayload⟩

/-- An insertion result may be restated from an earlier state with the same heap and the same
scalar registers other than the two scratch registers. -/
theorem InsertResult.before [LinearOrder M.Value]
    {encode : ℕ → M.Value} {field : Fin (extra + 1)}
    {source : Fin (extra + 1) → Fin (regs + 3)} {s x t : State M (layout extra (regs + 1))}
    {before after : BinaryTree (Label M extra)} {original : AVLTree M.Value}
    (h : InsertResult encode field source x t before after original)
    (heap : x.heap = s.heap)
    (data : ∀ i, i ≠ 1 → i ≠ 2 → x.data i = s.data i)
    (safe : ∀ f, f ≠ field → f ≠ 0 → source f ≠ 1 ∧ source f ≠ 2) :
    InsertResult encode field source s t before after original := by
  have h01 : (0 : Fin ((regs + 1) + 2)) ≠ 1 := by simp
  have h02 : (0 : Fin ((regs + 1) + 2)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < (regs + 1) + 2)]
  have query := data 0 h01 h02
  refine ⟨h.rep, ?_, h.distinct, h.root, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [query] using h.matched
  · simpa only [heap] using h.space
  · simpa only [heap] using h.footprint
  · intro i h1 h2; exact (h.data i h1 h2).trans (data i h1 h2)
  · intro z f hz hf
    simpa only [heap] using h.payload z f (by simpa only [heap] using hz) hf
  · intro grows f hf
    have fresh := h.freshPayload (by simpa only [heap] using grows) f hf
    by_cases key : f = 0
    · simpa only [heap, key, ↓reduceIte, query] using fresh
    · simpa only [heap, key, ↓reduceIte, data (source f) (safe f hf key).1 (safe f hf key).2]
        using fresh

private theorem missing_correct [LinearOrder M.Value]
    (zero maxSucc : M.Op) (lt heavy le : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))
    (heavy_spec : ∀ a b, M.evalTest heavy (encode a) (encode b) = decide (b + 1 < a))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (source : Fin (extra + 1) → Fin (regs + 3))
    (safe : ∀ f, f ≠ field → f ≠ 0 → source f ≠ 1 ∧ source f ≠ 2)
    (s : State M (layout extra (regs + 1))) (cs : List (Frame M extra))
    (original : AVLTree M.Value)
    (matched : Matches encode field (plug cs .nil) original) (valid : original.Valid)
    (path : SearchPath (s.data 0) cs) (rep : Represents s.heap none (plug cs .nil))
    (distinct : AddressesDistinct (plug cs .nil))
    (parent : s.ptr 2 = contextParent cs) (rootReg : s.ptr 1 = root (plug cs .nil))
    (pc : s.pc = 0) :
    let code := sequence (createLeaf zero maxSucc lt field source)
      (sequence [.loadPtr 0 2 0, .halt] (rebalanceAncestors zero maxSucc heavy le field))
    ∃ t tree time, Executes code s t time ∧ time ≤ 134 * cs.length + extra + 23 ∧
      InsertResult encode field source s t (plug cs .nil) tree original := by
  intro code
  obtain ⟨vacant, chosen⟩ := path.vacant lt compare s cs rep parent rootReg
  let label : Label M extra := ⟨s.heap.length,
    fun f => if f = field then encode 1 else if f = 0 then s.data 0 else s.data (source f)⟩
  let side : Fin 2 := if M.evalTest lt (s.data 0)
      (((s.deref 2).map (fun n => n.data 0)).getD (s.data 2)) then 0 else 1
  obtain ⟨a, ea, heapA, leafA, matchA, sizeA, cursorA, rootA, dataA, _⟩ :=
    createLeaf_correct zero maxSucc lt encode zero_spec max_spec
      field notKey source safe s pc vacant
  have graft := graftLeaf s.heap cs label side rep distinct rfl (by
    cases cs with
    | nil => trivial
    | cons frame cs => cases frame <;> exact chosen)
  have repA : Represents a.heap none (plug cs (.node label .nil .nil)) := by
    rw [heapA, parent]
    exact graft.1
  have rootA' : a.ptr 1 = root (plug cs (.node label .nil .nil)) := by
    rw [rootA, parent, rootReg, graft.2.2.2]
  obtain ⟨b, eb, heapB, dataB, cursorB, ptrB⟩ :=
    ascend_correct { a with pc := 0 } cs label .nil .nil
      (by simpa only [parent] using leafA) cursorA rfl
  have repB : Represents b.heap none (plug cs (.node label .nil .nil)) := by
    simpa only [heapB] using repA
  obtain ⟨c, tree, time, ec, bound, repC, matchC, distinctC, addressesC, cursorC,
      rootC, sizeC, dataC, payloadC⟩ :=
    rebalance_correct zero maxSucc heavy le encode zero_spec max_spec heavy_spec le_spec
      field notKey cs .nil (.node label .nil .nil) original .nil (s.data 0)
      matched valid trivial valid_nil matchA path { b with pc := 0 } repB graft.2.1 cursorB
      ((ptrB 1 (by simp [layout])).trans rootA') rfl
  have run := ea.sequence (eb.sequence ec)
  let t := { c with pc := (createLeaf zero maxSucc lt field source).length +
    (sequence ([.loadPtr 0 2 0, .halt] : List (Instr M (layout extra (regs + 1))))
      (rebalanceAncestors zero maxSucc heavy le field)).length }
  have size : t.heap.length = s.heap.length + 1 :=
    sizeC.trans ((congrArg List.length heapB).trans sizeA)
  refine ⟨t, tree, extra + 16 + (2 + time + 1) + 1, run, by omega,
    ⟨repC, matchC, distinctC, rootC, ⟨by omega, by omega⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [addressesC, graft.2.2.1]
    exact ⟨Finset.subset_insert _ _, Finset.Subset.refl _⟩
  · intro i h1 h2
    exact (dataC i h1 h2).trans ((congrFun dataB i).trans (dataA i h1 h2))
  · intro z f hz hf
    change (c.heap[z]?).map (fun n => n.data f) = _
    rw [payloadC z f hf, heapB, heapA]
    cases hp : s.ptr 2 with
    | none => simp [List.getElem?_append_left hz]
    | some p =>
      by_cases eq : p = z
      · subst p
        simp [List.getElem?_modify_eq, Option.map_map, Function.comp_def,
          List.getElem?_append_left hz]
      · rw [List.getElem?_modify_ne _ _ eq, List.getElem?_append_left hz]
  · intro _ f hf
    change (c.heap[s.heap.length]?).map (fun n => n.data f) = _
    rw [payloadC _ f hf, heapB, leafA.1]
    simp [record, hf]

private theorem afterSeek_found (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3))
    (s : State M (layout extra (regs + 1))) (pc : s.pc = 0) (cursor : s.ptr 0 ≠ none) :
    Executes (insertAfterSeek zero maxSucc lt heavy le field source) s
      { s.setPtr 5 none with pc := 2 } 3 := by
  let mid := { s.setPtr 5 none with pc := 1 }
  refine ⟨2, .head s mid _ _ ?_ (.single ?_), ?_, rfl⟩
  · simp [step, insertAfterSeek, pc, Instr.effect, Instr.next, mid]
  · simp [step, insertAfterSeek, mid, Instr.effect, Instr.next, State.setPtr, cursor]
  · simp [insertAfterSeek]

private theorem nullBranch_missing (missing : List (Instr M (layout extra (regs + 1))))
    (s : State M (layout extra (regs + 1))) (pc : s.pc = 0) (cursor : s.ptr 0 = none)
    (t : State M (layout extra (regs + 1))) (time : ℕ)
    (exec : Executes missing { s.setPtr 5 none with pc := 0 } t time) :
    Executes ([.null 5, .ifPtrEq 0 5 3, .halt] ++
      missing.map (Instr.relocate 3 (3 + missing.length)) ++ [.halt]) s
      { t with pc := 3 + missing.length } (time + 3) := by
  let mid := { s.setPtr 5 none with pc := 1 }
  have placed := exec.inBlock [.null 5, .ifPtrEq 0 5 3, .halt] [.halt] (3 + missing.length)
  have placed' : Runs ([.null 5, .ifPtrEq 0 5 3, .halt] ++
      missing.map (Instr.relocate 3 (3 + missing.length)) ++ [.halt])
      { s.setPtr 5 none with pc := 3 } { t with pc := 3 + missing.length } time := by
    simpa using placed
  refine ⟨time + 2, .head s mid _ _ ?_ (.head mid _ _ _ ?_ placed'), ?_, by omega⟩
  · simp [step, pc, Instr.effect, Instr.next, mid]
  · simp [step, mid, Instr.effect, Instr.next, State.setPtr, cursor]
  · rw [Nat.add_comm 3 missing.length]
    simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by simp)]
    simp

private theorem afterSeek_missing (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3))
    (s : State M (layout extra (regs + 1))) (pc : s.pc = 0) (cursor : s.ptr 0 = none) :
    let missing := sequence (createLeaf zero maxSucc lt field source)
      (sequence [.loadPtr 0 2 0, .halt] (rebalanceAncestors zero maxSucc heavy le field))
    ∀ t time, Executes missing { s.setPtr 5 none with pc := 0 } t time →
      Executes (insertAfterSeek zero maxSucc lt heavy le field source) s
        { t with pc := 3 + missing.length } (time + 3) := by
  intro missing t time exec
  simpa only [insertAfterSeek] using nullBranch_missing missing s pc cursor t time exec
/-- The concrete finite program implements AVLTree.insert, preserving linked representation,
address separation and payloads while allocating at most one record. Its instruction bound is
linear in the original AVL height and logarithmic in the number of stored keys; the additive
term charges every initialized scalar field. All counts include allocation, jumps and halt. -/
theorem insert_correct [LinearOrder M.Value]
    (zero maxSucc : M.Op) (lt heavy le : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))
    (heavy_spec : ∀ a b, M.evalTest heavy (encode a) (encode b) = decide (b + 1 < a))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (source : Fin (extra + 1) → Fin (regs + 3))
    (safe : ∀ f, f ≠ field → f ≠ 0 → source f ≠ 1 ∧ source f ≠ 2)
    (s : State M (layout extra (regs + 1)))
    (tree : BinaryTree (Label M extra)) (original : AVLTree M.Value)
    (rep : Represents s.heap none tree) (distinct : AddressesDistinct tree)
    (matched : Matches encode field tree original) (valid : original.Valid)
    (cursor : s.ptr 0 = root tree) (rootReg : s.ptr 1 = root tree) (pc : s.pc = 0) :
    ∃ t result time, Executes (insert zero maxSucc lt heavy le field source) s t time ∧
      time ≤ 141 * original.cachedHeight + extra + 31 ∧
      time ≤ 282 * Nat.log 2 (original.elements.card + 1) + extra + 31 ∧
      InsertResult encode field source s t tree result original := by
  have h01 : (0 : Fin ((regs + 1) + 2)) ≠ 1 := by simp
  have h02 : (0 : Fin ((regs + 1) + 2)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < (regs + 1) + 2)]
  obtain ⟨a, ta, cs, focus, ea, ba, ra⟩ := seek_correct lt compare s tree rep cursor pc
  have query := ra.data 0 h01
  have rootA : a.ptr 1 = root tree :=
    (ra.ptr 1 (by simp [layout]) (by simp [layout]) (by simp [layout])).trans rootReg
  have visits : SearchTree.searchVisits (s.data 0) (keys tree) ≤ original.cachedHeight := by
    rw [matched.keys]
    exact searchVisits_le_cachedHeight valid.heightConsistent _
  have searchTime : ta ≤ 7 * original.cachedHeight + 4 := by omega
  have endpoint : ∃ t result time,
      Executes (insert zero maxSucc lt heavy le field source) s t time ∧
      time ≤ 141 * original.cachedHeight + extra + 31 ∧
      InsertResult encode field source s t tree result original := by
    cases focus with
    | nil =>
      let cleared := { a.setPtr 5 none with pc := 0 }
      have complete : Represents cleared.heap none (plug cs .nil) := by
        rw [show cleared.heap = s.heap from ra.heap, ← ra.reconstruction]
        exact rep
      have separated : AddressesDistinct (plug cs .nil) := ra.reconstruction ▸ distinct
      have m : Matches encode field (plug cs .nil) original := ra.reconstruction ▸ matched
      have path : SearchPath (cleared.data 0) cs := by
        simpa only [cleared, State.setPtr, query] using ra.path
      have parent : cleared.ptr 2 = contextParent cs := by
        simpa [cleared, State.setPtr] using ra.parent
      have rootCleared : cleared.ptr 1 = root (plug cs .nil) := by
        simpa [cleared, State.setPtr, ra.reconstruction] using rootA
      obtain ⟨b, result, tb, eb, bb, rb⟩ := missing_correct zero maxSucc lt heavy le encode
        zero_spec max_spec compare heavy_spec le_spec field notKey source safe
        cleared cs original m valid path complete separated parent rootCleared rfl
      have run := ea.sequence (afterSeek_missing zero maxSucc lt heavy le field source
        { a with pc := 0 } rfl ra.cursor b tb eb)
      let t := { b with pc := (seek (regs := regs + 1) (extra := extra) lt).length +
        (insertAfterSeek zero maxSucc lt heavy le field source).length }
      have before : InsertResult encode field source s b tree result original := by
        rw [ra.reconstruction]
        exact rb.before ra.heap (fun i h1 _ => ra.data i h1) safe
      have depth := height_add_context_length_le cs (.nil : BinaryTree (Label M extra))
      rw [← ra.reconstruction, matched.shape_height,
        ← cachedHeight_eq_height valid.heightConsistent] at depth
      refine ⟨t, result, ta + (tb + 3) + 1, run, by omega, before.withPc _⟩
    | node label left right =>
      have nonempty : a.ptr 0 ≠ none := by simp [ra.cursor, root]
      have present : AVLTree.contains (s.data 0) original = true := by
        rw [contains_eq_searchTree, ← matched.keys, ← ra.found]
        simp [ra.cursor, root]
      have unchanged := insert_eq_self valid ((contains_eq_true valid.ordered _).mp present)
      have run := ea.sequence
        (afterSeek_found zero maxSucc lt heavy le field source { a with pc := 0 } rfl nonempty)
      let t := { a.setPtr 5 none with pc := (seek (regs := regs + 1) (extra := extra) lt).length +
        (insertAfterSeek zero maxSucc lt heavy le field source).length }
      refine ⟨t, tree, ta + 3 + 1, run, by omega, ?_⟩
      refine ⟨?_, ?_, distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [t, State.setPtr, ra.heap] using rep
      · simpa only [unchanged] using matched
      · simpa [t, State.setPtr] using rootA
      · simp [t, State.setPtr, ra.heap]
      · exact ⟨Finset.Subset.refl _, Finset.subset_insert _ _⟩
      · intro i h1 _; exact ra.data i h1
      · intro z f _ _; simp only [t, State.setPtr, ra.heap]
      · intro grows
        have bad : s.heap.length < s.heap.length := by
          simpa only [t, State.setPtr, ra.heap] using grows
        omega
  obtain ⟨t, result, time, exec, bound, outcome⟩ := endpoint
  refine ⟨t, result, time, exec, bound, ?_, outcome⟩
  have logarithmic := valid.cachedHeight_le_two_mul_log
  omega

end Cslib.DataStructure.AVLTree.PointerMachine

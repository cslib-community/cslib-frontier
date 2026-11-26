/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Insert
public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Context
public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Structured.Balance
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Allocation
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.ReconnectContext
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Seek

/-!
# AVL insertion as a structured pointer-machine program

`Structured.insert` is the program of `Insert` written as a structured program. It searches with
a parent cursor, initializes and attaches one new leaf on a miss, and balances ancestors by
following parent links in a loop. It meets the same specification `InsertResult`, within
`105 * height + extra + 20` instructions, against `141 * height + extra + 31` for the flat
program.

## Main definitions

* `createLeaf`, `ancestorStep`, `rebalanceAncestors`, `insertAfterSeek`, `insert`: the programs.

## Main results

* `insert_correct`: the program implements `AVLTree.insert`.
-/

public section

namespace Cslib.DataStructure.AVLTree.PointerMachine.Structured

open Cslib.PointerMachine SearchTree.PointerMachine
open Cslib.Program (ExecWithin.skip ExecWithin.seq ExecWithin.branch_pos ExecWithin.branch_neg)

variable {M : Model} {extra regs : ℕ}

open SearchTree.PointerMachine.Structured (ascend) in
open SearchTree.PointerMachine.Structured renaming reconnect → relink, seek → seekParent,
  insertLeaf → addLeaf in
open Register in
/-- Initialize a height-one leaf, choose its child link by comparison with the parent key, and
allocate and attach it. A null parent installs the whole-tree root. -/
@[expose] def createLeaf (zero maxSucc : M.Op) (lt : M.Test) (field : Fin (extra + 1))
    (source : Fin (extra + 1) → Fin (regs + 3)) : Code M (layout extra (regs + 1)) := pm[
  lh := zero query query;
  lh := maxSucc lh lh;
  parentKey := par[key];
  if lt query parentKey then [ ⟪addLeaf (leafRegisters field source) 0⟫ ]
  else [ ⟪addLeaf (leafRegisters field source) 1⟫ ] ]

open SearchTree.PointerMachine.Structured (ascend) in
open SearchTree.PointerMachine.Structured renaming reconnect → relink, seek → seekParent,
  insertLeaf → addLeaf in
/-- Balance the current ancestor, reconnect its new root, and move to its parent. The enclosing
loop decides whether another ancestor exists. -/
@[expose] def ancestorStep (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) : Code M (layout extra (regs + 1)) := pm[
  ⟪balance zero maxSucc heavy le field⟫;
  ⟪relink⟫;
  ⟪ascend⟫ ]

open Register in
/-- Balance and reconnect every ancestor until the cursor is null. Register five must be null
on entry; each iteration restores that. -/
@[expose] def rebalanceLoop (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) : Code M (layout extra (regs + 1)) := pm[
  while cur ≠ nul do [ ⟪ancestorStep zero maxSucc heavy le field⟫; nul ← null ] ]

open Register in
/-- Follow parent links, balancing and reconnecting every ancestor until the cursor is null. -/
@[expose] def rebalanceAncestors (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) : Code M (layout extra (regs + 1)) := pm[
  nul ← null;
  ⟪rebalanceLoop zero maxSucc heavy le field⟫ ]

open SearchTree.PointerMachine.Structured (ascend) in
open SearchTree.PointerMachine.Structured renaming reconnect → relink, seek → seekParent,
  insertLeaf → addLeaf in
/-- Create a leaf at the vacant link found by the search and repair its ancestors. -/
@[expose] def missing (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3)) :
    Code M (layout extra (regs + 1)) := pm[
  ⟪createLeaf zero maxSucc lt field source⟫;
  ⟪ascend⟫;
  ⟪rebalanceAncestors zero maxSucc heavy le field⟫ ]

open Register in
/-- On an unsuccessful search, create a leaf and repair its ancestors. After a successful
search the heap is unchanged; pointer register five is cleared in both cases. -/
@[expose] def insertAfterSeek (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3)) :
    Code M (layout extra (regs + 1)) := pm[
  nul ← null;
  if cur = nul then [ ⟪missing zero maxSucc lt heavy le field source⟫ ] ]

open SearchTree.PointerMachine.Structured (ascend) in
open SearchTree.PointerMachine.Structured renaming reconnect → relink, seek → seekParent,
  insertLeaf → addLeaf in
/-- Insert the query in data register zero into the AVL tree at cursor zero. Root register one
tracks the whole tree. All extra leaf payload sources are explicit. -/
@[expose] def insert (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3)) :
    Code M (layout extra (regs + 1)) := pm[
  ⟪seekParent lt⟫;
  ⟪insertAfterSeek zero maxSucc lt heavy le field source⟫ ]

/-- Creating a leaf assigns only data registers one and two. -/
private theorem createLeaf_dataDests (zero maxSucc : M.Op) (lt : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3)) :
    (createLeaf zero maxSucc lt field source).dataDests ⊆ [1, 2] := by
  simp [createLeaf, Op.dataDest]

private theorem createLeaf_correct [LinearOrder M.Value] (zero maxSucc : M.Op)
    (lt : M.Test) (encode : ℕ → M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (field : Fin (extra + 1)) (notKey : field ≠ 0)
    (source : Fin (extra + 1) → Fin (regs + 3))
    (safe : ∀ f, f ≠ field → f ≠ 0 → source f ≠ 1 ∧ source f ≠ 2)
    (s : State M (layout extra (regs + 1)))
    (vacant : match s.ptr 2 with
      | none => s.ptr 1 = none
      | some a => ∃ par, s.heap[a]? = some par ∧
          par.ptr (if M.evalTest lt (s.data 0) (par.data 0) then 0 else 1) = none) :
    let label : Label M extra := ⟨s.heap.length,
      fun f => if f = field then encode 1 else if f = 0 then s.data 0 else s.data (source f)⟩
    let parentKey := ((s.deref 2).map (fun n => n.data 0)).getD (s.data 2)
    let side : Fin 2 := if M.evalTest lt (s.data 0) parentKey then 0 else 1
    ∃ t, ExecWithin (createLeaf zero maxSucc lt field source) s t (extra + 12) ∧
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
  let q : State M (layout extra (regs + 1)) := (s.setData 1 (encode 1)).setData 2 parentKey
  have e₁ : (Op.op zero 1 0 0).effect s = s.setData 1 (encode 0) := by
    simp [Op.effect, Op.instr, Instr.effect, zero_spec]
  have e₂ : (Op.op maxSucc 1 1 1).effect (s.setData 1 (encode 0)) = s.setData 1 (encode 1) := by
    simp [Op.effect, Op.instr, Instr.effect, State.setData, max_spec, Function.update_idem]
  have e₃ : (Op.loadData 2 0 2).effect (s.setData 1 (encode 1)) = q := by
    have h21 : (2 : Fin ((regs + 1) + 2)) ≠ 1 := by
      simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < (regs + 1) + 2)]
    cases h : s.deref 2 <;>
      simp only [State.deref] at h <;>
      simp [Op.effect, Op.instr, Instr.effect, q, parentKey, State.setData, State.deref, h, h21]
  have h01 : (0 : Fin (regs + 3)) ≠ 1 := by simp
  have h02 : (0 : Fin (regs + 3)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < regs + 3)]
  have h12 : (1 : Fin (regs + 3)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < regs + 3)]
  have keyData : (fun f => q.data (leafRegisters field source f)) = label.data := by
    funext f
    by_cases hf : f = field
    · subst f; simp [q, State.setData, leafRegisters, label, h12]
    · by_cases hk : f = 0
      · subst f; simp [q, State.setData, leafRegisters, label, hf, h01, h02]
      · simp [q, State.setData, leafRegisters, label, hf, hk,
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
      obtain ⟨par, get, slot⟩ := hp ▸ vacant
      exact ⟨par, get, by cases h : M.evalTest lt (s.data 0) (par.data 0) <;>
        simpa [side, parentKey, State.deref, hp, get, h] using slot⟩
  obtain ⟨t, run, heap, rep, size, cursor, rootReg, data, _, ptr, _⟩ :=
    SearchTree.PointerMachine.Structured.insertLeaf_correct (leafRegisters field source) side q
      vacancy
  have branched : ExecWithin (.branch (.data lt 0 2)
      (SearchTree.PointerMachine.Structured.insertLeaf (leafRegisters field source) 0)
      (SearchTree.PointerMachine.Structured.insertLeaf (leafRegisters field source) 1)) q t
      (extra + 9) := by
    cases h : M.evalTest lt (s.data 0) parentKey
    · exact ExecWithin.branch_neg (by simp [Test.Holds, q, State.setData, h01, h02, h])
        (by simpa [side, h] using run)
    · exact (ExecWithin.branch_pos (by simp [Test.Holds, q, State.setData, h01, h02, h])
        (by simpa [side, h] using run)).mono (by omega)
  have exec : ExecWithin (createLeaf zero maxSucc lt field source) s t (extra + 12) :=
    (ExecWithin.seq (ExecWithin.op_eq e₁) (ExecWithin.seq (ExecWithin.op_eq e₂)
      (ExecWithin.seq (ExecWithin.op_eq e₃) branched))).mono (by omega)
  refine ⟨t, exec, by rwa [keyData] at heap, by rwa [keyData] at rep, ?_, size, cursor, rootReg,
    fun i h1 h2 => exec.data_keep [1, 2] (createLeaf_dataDests zero maxSucc lt field source)
      (by simp [h1, h2]), ptr⟩
  simp [Matches, AVLTree.insert, mkNode, Ne.symm notKey]

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
    (cursor : s.ptr 0 = some label.address)
    (rootReg : s.ptr 1 = root (plug cs (.node label l r))) :
    ∃ t, ExecWithin (ancestorStep zero maxSucc heavy le field) s t 94 ∧
      ∃ tree, Represents t.heap none (plug cs tree) ∧
        Matches encode field tree (AVLTree.balance (label.data 0) L R) ∧
        AddressesDistinct (plug cs tree) ∧ addresses tree = addresses (.node label l r) ∧
        t.ptr 0 = contextParent cs ∧ t.ptr 1 = root (plug cs tree) := by
  obtain ⟨b, tree, eb, rb, mb, db, ab, nonempty, cb, rootB, saved, -, -, frameB, -⟩ :=
    balance_correct zero maxSucc heavy le encode
      zero_spec max_spec heavy_spec le_spec field notKey s label l r L R (contextParent cs)
      ((represents_plug_iff ..).mp rep).1 (distinct.focus) ml mr hl hr cursor
  obtain ⟨c, ec, resultC⟩ := SearchTree.PointerMachine.Structured.reconnect_context s.heap b cs
    (.node label l r) tree rep distinct rb db ab frameB (by simp)
    (by intro eq; simp [eq, root] at nonempty) cb (saved.trans cursor)
    (rootB.trans rootReg)
  cases tree with
  | nil => simp [root] at nonempty
  | node a left right =>
    have rc := ((represents_plug_iff c.heap cs (.node a left right)).mp resultC.rep).1
    obtain ⟨d, ed, heapD, -, cursorD, ptrD⟩ :=
      SearchTree.PointerMachine.Structured.ascend_correct c cs a left right rc
        (resultC.cursor.trans cb)
    exact ⟨d, (ExecWithin.seq eb (ExecWithin.seq ec ed)).mono (by omega), .node a left right,
      by simpa only [heapD] using resultC.rep, mb, resultC.distinct, ab, cursorD,
      (ptrD 1 (by simp [layout])).trans resultC.root⟩

/-- An ancestor frame, as a side: plugging into it is a node with the focus on that side. -/
private theorem frame_view [LT M.Value] (f : Frame M extra) :
    ∃ (d : Bool) (label : Label M extra) (sib : BinaryTree (Label M extra)),
      (∀ cs t, plug (f :: cs) t = plug cs (nodeAt d label t sib)) ∧
      (∀ cs : List (Frame M extra), contextParent (f :: cs) = some label.address) ∧
      ∀ (q : M.Value) cs, SearchPath q (f :: cs) ↔
        (if d then label.data 0 < q else q < label.data 0) ∧ SearchPath q cs := by
  cases f with
  | left label sib =>
    exact ⟨false, label, sib, fun _ _ => rfl, fun _ => rfl, fun _ _ => by simp [SearchPath]⟩
  | right sib label =>
    exact ⟨true, label, sib, fun _ _ => rfl, fun _ => rfl, fun _ _ => by simp [SearchPath]⟩

/-- The invariant of the rebalancing loop, with `k` ancestors still to visit: the cursor is the
parent of a focus that already matches the insertion into what it replaced, inside a tree that
is otherwise the original one. -/
private def Climbing [LinearOrder M.Value] (encode : ℕ → M.Value) (field : Fin (extra + 1))
    (original : AVLTree M.Value) (query : M.Value) (footprint : Finset ℕ) (k : ℕ)
    (x : State M (layout extra (regs + 1))) : Prop :=
  ∃ (cs : List (Frame M extra)) (before after : BinaryTree (Label M extra))
    (focused : AVLTree M.Value),
    cs.length = k ∧ Matches encode field (plug cs before) original ∧
    Matches encode field before focused ∧ focused.Valid ∧
    Matches encode field after (AVLTree.insert query focused) ∧ SearchPath query cs ∧
    Represents x.heap none (plug cs after) ∧ AddressesDistinct (plug cs after) ∧
    addresses (plug cs after) = footprint ∧ x.ptr 0 = contextParent cs ∧
    x.ptr 1 = root (plug cs after) ∧ x.ptr 5 = none

/-! Frames of the rebalancing loop, from those of its subprograms. -/

private theorem rebalance_keepsSize (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) :
    (rebalanceAncestors (regs := regs) zero maxSucc heavy le field).KeepsSize := by
  simp [rebalanceAncestors, rebalanceLoop, ancestorStep, balance_keepsSize, Op.creates]

private theorem rebalance_dataDests (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) :
    (rebalanceAncestors (regs := regs) zero maxSucc heavy le field).dataDests ⊆ [1, 2] := by
  simpa [rebalanceAncestors, rebalanceLoop, ancestorStep, Op.dataDest] using
    balance_dataDests zero maxSucc heavy le field

private theorem rebalance_fieldDests (zero maxSucc : M.Op) (heavy le : M.Test)
    (field : Fin (extra + 1)) :
    ∀ f ∈ (rebalanceAncestors (regs := regs) zero maxSucc heavy le field).fieldDests,
      f = field := by
  simpa [rebalanceAncestors, rebalanceLoop, ancestorStep, Op.fieldDest] using
    balance_fieldDests zero maxSucc heavy le field

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
    (cursor : s.ptr 0 = contextParent cs) (rootReg : s.ptr 1 = root (plug cs after)) :
    ∃ t tree, ExecWithin (rebalanceAncestors zero maxSucc heavy le field) s t
        (97 * cs.length + 2) ∧ Represents t.heap none tree ∧
      Matches encode field tree (AVLTree.insert query original) ∧ AddressesDistinct tree ∧
      addresses tree = addresses (plug cs after) ∧ t.ptr 0 = none ∧ t.ptr 1 = root tree ∧
      t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i) ∧
      (∀ (a : ℕ) (f : Fin (extra + 1)), f ≠ field → (t.heap[a]?).map (fun n => n.data f) =
        (s.heap[a]?).map (fun n => n.data f)) := by
  have main : ∃ t, ExecWithin (rebalanceAncestors zero maxSucc heavy le field) s t
        (97 * cs.length + 2) ∧
      ∃ tree, Represents t.heap none tree ∧
        Matches encode field tree (AVLTree.insert query original) ∧ AddressesDistinct tree ∧
        addresses tree = addresses (plug cs after) ∧ t.ptr 0 = none ∧ t.ptr 1 = root tree := by
    apply WP.exists_execWithin
    pm_exec [rebalanceAncestors]
    refine Program.WP.loopUntil_indexed
      (Climbing encode field original query (addresses (plug cs after))) 95
      (fun k x hx ht => ?_) (k := cs.length)
      ⟨cs, before, after, focused, rfl, originalMatch, focusedMatch, focusedValid, changedMatch,
        path, rep, distinct, rfl, by simpa using cursor, by simpa using rootReg, by simp⟩
      (fun j y _ hy holds n hn => ?_)
    · -- One ancestor: balance it, reconnect, move up, and restore the null register.
      obtain ⟨cs, before, after, focused, rfl, om, fm, fv, cm, path, rep, dist, fp, cur, top,
        nil⟩ := hx
      cases cs with
      | nil => exact (ht (by simp [pm_simps, cur, nil, contextParent])).elim
      | cons f cs =>
        obtain ⟨d, label, sib, hplug, hpar, hpath⟩ := frame_view f
        simp only [hplug] at om rep dist fp top
        rw [hpar] at cur
        obtain ⟨pathHere, pathTail⟩ := (hpath ..).mp path
        obtain ⟨parentAVL, pm, pv⟩ := om.exists_valid_focus valid
        obtain ⟨h, C, S, rfl, -, mC, mS⟩ := matches_nodeAt pm
        obtain ⟨hC, hS⟩ := pv.heightConsistent.of_nodeSide
        obtain rfl : C = focused := hC.eq_of_toBinaryTree_eq fv.heightConsistent
          (mC.keys.symm.trans fm.keys)
        have step : ∃ t, ExecWithin (ancestorStep zero maxSucc heavy le field) x t 94 ∧
            ∃ tree, Represents t.heap none (plug cs tree) ∧
              Matches encode field tree
                (balanceAt d (label.data 0) (AVLTree.insert query C) S) ∧
              AddressesDistinct (plug cs tree) ∧
              addresses tree = addresses (nodeAt d label after sib) ∧
              t.ptr 0 = contextParent cs ∧ t.ptr 1 = root (plug cs tree) := by
          have hi := (valid_insert fv query).heightConsistent
          cases d
          · exact ancestorStep_correct zero maxSucc heavy le encode zero_spec max_spec heavy_spec
              le_spec field notKey x cs label after sib _ S rep dist cm mS hi hS cur top
          · exact ancestorStep_correct zero maxSucc heavy le encode zero_spec max_spec heavy_spec
              le_spec field notKey x cs label sib after S _ rep dist mS cm hS hi cur top
        refine Program.WP.seq (Program.WP.call step ?_)
        rintro t ⟨tree, rt, mt, dt, at', ct, rootT⟩ n hn
        refine WP.op ⟨by omega, cs.length, by simp, cs, nodeAt d label before sib, tree, _, rfl,
          om, pm, pv, ?_, pathTail, rt, dt, ?_, by simpa [pm_simps] using ct,
          by simpa [pm_simps] using rootT, by simp [pm_simps]⟩
        · rwa [insert_nodeSide d _ h C S query pathHere]
        · rwa [addresses_plug, at', ← addresses_plug]
    · -- The loop ends at the root: no ancestor is left, and the focus is the whole tree.
      obtain ⟨cs', before', after', focused', -, om, fm, fv, cm, -, rep', dist', fp, cur, top,
        nil⟩ := hy
      rcases cs' with _ | ⟨f, _⟩
      · obtain rfl : focused' = original := fv.heightConsistent.eq_of_toBinaryTree_eq
          valid.heightConsistent (fm.keys.symm.trans om.keys)
        exact ⟨by omega, after', rep', cm, dist', fp, cur, top⟩
      · obtain ⟨_, _, _, -, hpar, -⟩ := frame_view f
        simp [pm_simps, cur, nil, hpar] at holds
  obtain ⟨t, run, tree, rt, mt, dt, at', ct, rootT⟩ := main
  exact ⟨t, tree, run, rt, mt, dt, at', ct, rootT,
    run.length_eq (rebalance_keepsSize zero maxSucc heavy le field),
    fun i h1 h2 => run.data_keep [1, 2] (rebalance_dataDests zero maxSucc heavy le field)
      (by simp [h1, h2]),
    fun a f hf => run.field_keep (rebalance_keepsSize zero maxSucc heavy le field)
      (fun h => hf (rebalance_fieldDests zero maxSucc heavy le field f h)) a⟩

/-- Creating a leaf and rebalancing its ancestors assigns only data registers one and two. -/
private theorem missing_dataDests (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3)) :
    (missing zero maxSucc lt heavy le field source).dataDests ⊆ [1, 2] := by
  simpa [missing] using And.intro (createLeaf_dataDests zero maxSucc lt field source)
    (rebalance_dataDests zero maxSucc heavy le field)

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
    (parent : s.ptr 2 = contextParent cs) (rootReg : s.ptr 1 = root (plug cs .nil)) :
    ∃ t tree, ExecWithin (missing zero maxSucc lt heavy le field source) s t
        (97 * cs.length + extra + 15) ∧
      InsertResult encode field source s t (plug cs .nil) tree original := by
  obtain ⟨vacant, chosen⟩ := path.vacant lt compare s cs rep parent rootReg
  let label : Label M extra := ⟨s.heap.length,
    fun f => if f = field then encode 1 else if f = 0 then s.data 0 else s.data (source f)⟩
  let side : Fin 2 := if M.evalTest lt (s.data 0)
      (((s.deref 2).map (fun n => n.data 0)).getD (s.data 2)) then 0 else 1
  obtain ⟨a, ea, heapA, leafA, matchA, sizeA, cursorA, rootA, dataA, _⟩ :=
    createLeaf_correct zero maxSucc lt encode zero_spec max_spec
      field notKey source safe s vacant
  have graft := graftLeaf s.heap cs label side rep distinct rfl (by
    cases cs with
    | nil => trivial
    | cons frame cs => cases frame <;> exact chosen)
  obtain ⟨b, eb, heapB, dataB, cursorB, ptrB⟩ :=
    SearchTree.PointerMachine.Structured.ascend_correct a cs label .nil .nil
      (by simpa only [parent] using leafA) cursorA
  obtain ⟨c, tree, ec, repC, matchC, distinctC, addressesC, cursorC,
      rootC, sizeC, dataC, payloadC⟩ :=
    rebalance_correct zero maxSucc heavy le encode zero_spec max_spec heavy_spec le_spec
      field notKey cs .nil (.node label .nil .nil) original .nil (s.data 0)
      matched valid trivial valid_nil matchA path b
      (heapB ▸ heapA ▸ parent ▸ graft.1) graft.2.1 cursorB
      (by rw [ptrB 1 (by simp [layout]), rootA, parent, rootReg, graft.2.2.2])
  have size : c.heap.length = s.heap.length + 1 :=
    sizeC.trans ((congrArg List.length heapB).trans sizeA)
  have exec : ExecWithin (missing zero maxSucc lt heavy le field source) s c
      (97 * cs.length + extra + 15) :=
    (ExecWithin.seq ea (ExecWithin.seq eb ec)).mono (by omega)
  refine ⟨c, tree, exec, ⟨repC, matchC, distinctC, rootC, ⟨by omega, by omega⟩, ?_,
    fun i h1 h2 => exec.data_keep [1, 2]
      (missing_dataDests zero maxSucc lt heavy le field source) (by simp [h1, h2]), ?_, ?_⟩⟩
  · rw [addressesC, graft.2.2.1]
    exact ⟨Finset.subset_insert _ _, Finset.Subset.refl _⟩
  · intro z f hz hf
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
    rw [payloadC _ f hf, heapB, leafA.1]
    simp [record, hf]

private theorem afterSeek_found (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3))
    (s : State M (layout extra (regs + 1))) (cursor : s.ptr 0 ≠ none) :
    ExecWithin (insertAfterSeek zero maxSucc lt heavy le field source) s (s.setPtr 5 none) 3 :=
  ExecWithin.seq ExecWithin.op
    (ExecWithin.branch_neg
      (by simpa [Test.Holds, Op.effect, Op.instr, Instr.effect] using cursor)
      (ExecWithin.skip (T := 0)))

private theorem afterSeek_missing (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (field : Fin (extra + 1)) (source : Fin (extra + 1) → Fin (regs + 3))
    (s : State M (layout extra (regs + 1))) (cursor : s.ptr 0 = none)
    (t : State M (layout extra (regs + 1))) (time : ℕ)
    (exec : ExecWithin (missing zero maxSucc lt heavy le field source) (s.setPtr 5 none) t
      time) :
    ExecWithin (insertAfterSeek zero maxSucc lt heavy le field source) s t (time + 2) :=
  (ExecWithin.seq ExecWithin.op
    (ExecWithin.branch_pos
      (by simpa [Test.Holds, Op.effect, Op.instr, Instr.effect] using cursor) exec)).mono
    (by omega)

/-- The concrete finite program implements AVLTree.insert, preserving linked representation,
address separation and payloads while allocating at most one record. Its instruction bound is
linear in the original AVL height and logarithmic in the number of stored keys; the additive
term charges every initialized scalar field. All counts include allocation and jumps. -/
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
    (cursor : s.ptr 0 = root tree) (rootReg : s.ptr 1 = root tree) :
    ∃ t result, ExecWithin (insert zero maxSucc lt heavy le field source) s t
        (105 * original.cachedHeight + extra + 20) ∧
      ExecWithin (insert zero maxSucc lt heavy le field source) s t
        (210 * Nat.log 2 (original.elements.card + 1) + extra + 20) ∧
      InsertResult encode field source s t tree result original := by
  obtain ⟨a, cs, focus, ea, ra⟩ :=
    SearchTree.PointerMachine.Structured.seek_correct lt compare s tree rep cursor
  have query := ra.data 0 (by simp)
  have rootA : a.ptr 1 = root tree :=
    (ra.ptr 1 (by simp [layout]) (by simp [layout]) (by simp [layout])).trans rootReg
  have visits : SearchTree.searchVisits (s.data 0) (keys tree) ≤ original.cachedHeight := by
    rw [matched.keys]; exact searchVisits_le_cachedHeight valid.heightConsistent _
  obtain ⟨t, result, exec, outcome⟩ : ∃ t result,
      ExecWithin (insert zero maxSucc lt heavy le field source) s t
        (105 * original.cachedHeight + extra + 20) ∧
      InsertResult encode field source s t tree result original := by
    cases focus with
    | nil =>
      let cleared := a.setPtr 5 none
      have parent : cleared.ptr 2 = contextParent cs := by
        simpa [cleared, State.setPtr] using ra.parent
      have rootCleared : cleared.ptr 1 = root (plug cs .nil) := by
        simpa [cleared, State.setPtr, ra.reconstruction] using rootA
      obtain ⟨b, result, eb, rb⟩ := missing_correct zero maxSucc lt heavy le encode
        zero_spec max_spec compare heavy_spec le_spec field notKey source safe
        cleared cs original (ra.reconstruction ▸ matched) valid (query.symm ▸ ra.path)
        (ra.heap.symm ▸ ra.reconstruction ▸ rep) (ra.reconstruction ▸ distinct) parent rootCleared
      have run := ExecWithin.seq ea
        (afterSeek_missing zero maxSucc lt heavy le field source a ra.cursor b _ eb)
      have depth := height_add_context_length_le cs (.nil : BinaryTree (Label M extra))
      rw [← ra.reconstruction, matched.shape_height,
        ← cachedHeight_eq_height valid.heightConsistent] at depth
      exact ⟨b, result, run.mono (by omega),
        ra.reconstruction ▸ rb.before ra.heap (fun i h1 _ => ra.data i h1) safe⟩
    | node label left right =>
      have present : AVLTree.contains (s.data 0) original = true := by
        rw [contains_eq_searchTree, ← matched.keys, ← ra.found]
        simp [ra.cursor, root]
      have run := ExecWithin.seq ea
        (afterSeek_found zero maxSucc lt heavy le field source a (by simp [ra.cursor, root]))
      let t := a.setPtr 5 none
      refine ⟨t, tree, run.mono (by omega), ?_, ?_, distinct, ?_, ?_,
        ⟨Finset.Subset.refl _, Finset.subset_insert _ _⟩, fun i h1 _ => ra.data i h1, ?_, ?_⟩
      · simpa only [t, State.setPtr, ra.heap] using rep
      · simpa only [insert_eq_self valid ((contains_eq_true valid.ordered _).mp present)]
          using matched
      · simpa [t, State.setPtr] using rootA
      · simp [t, State.setPtr, ra.heap]
      · intro z f _ _; simp only [t, State.setPtr, ra.heap]
      · intro grows; simp [t, State.setPtr, ra.heap] at grows
  exact ⟨t, result, exec, exec.mono (by have := valid.cachedHeight_le_two_mul_log; omega), outcome⟩

end Cslib.DataStructure.AVLTree.PointerMachine.Structured

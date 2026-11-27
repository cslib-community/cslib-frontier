/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Context
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Child
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Reconnect
public import CslibFrontier.Computability.PointerMachine.Frame

/-!
# Reconnecting a subtree within its complete tree

The local mutation supplies a replacement subtree and a frame for the old subtree's exterior.
The concrete reconnection program restores the complete heap representation and root register.
Separation follows from the original tree's distinct addresses and the preserved footprint.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Whole-tree and register guarantees after reconnecting a changed focus. -/
structure ReconnectResult (s : State M (layout extra regs)) (cs : List (Frame M extra))
    (tree : BinaryTree (Label M extra)) (t : State M (layout extra regs)) : Prop where
  /-- The complete tree is again linked correctly. -/
  rep : Represents t.heap none (plug cs tree)
  /-- Complete-tree addresses remain distinct. -/
  distinct : AddressesDistinct (plug cs tree)
  /-- The global root tracks the reconstructed tree. -/
  root : t.ptr 1 = PointerMachine.root (plug cs tree)
  /-- The cursor remains at the changed focus. -/
  cursor : t.ptr 0 = s.ptr 0
  /-- Reconnection preserves scalar registers. -/
  data : t.data = s.data
  /-- Reconnection allocates nothing. -/
  size : t.heap.length = s.heap.length
  /-- Only the global root and navigation scratch pointers can change. -/
  ptr : ∀ i, i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 5 → t.ptr i = s.ptr i
  /-- All scalar fields of all heap records survive reconnection. -/
  payload : ∀ (a : ℕ) (f : Fin (extra + 1)), (t.heap[a]?).map (fun n => n.data f) =
    (s.heap[a]?).map (fun n => n.data f)

private theorem payload_frame {s t : State M (layout extra regs)} {time : ℕ}
    (run : Executes reconnect s t time) (a : ℕ) (f : Fin (extra + 1)) :
    (t.heap[a]?).map (fun n => n.data f) = (s.heap[a]?).map (fun n => n.data f) := by
  obtain ⟨n, run, _, _⟩ := run
  exact run.data_frame f (by simp [reconnect, Instr.WritesData]) a

private theorem reconnect_below (right : Bool)
    (h : List (Record M (layout extra regs))) (s : State M (layout extra regs))
    (cs : List (Frame M extra)) (label : Label M extra)
    (old new sibling : BinaryTree (Label M extra))
    (rep : Represents h none (plug cs (nodeAt right label old sibling)))
    (distinct : AddressesDistinct (plug cs (nodeAt right label old sibling)))
    (newRep : Represents s.heap (some label.address) new)
    (newDistinct : AddressesDistinct new) (same : addresses new = addresses old)
    (frame : ∀ a, a ∉ addresses old → s.heap[a]? = h[a]?)
    (oldNonempty : old ≠ .nil) (newNonempty : new ≠ .nil)
    (pc : s.pc = 0) (cursor : s.ptr 0 = root new) (saved : s.ptr 6 = root old)
    (rootReg : s.ptr 1 = root (plug cs (nodeAt right label old sibling))) :
    ∃ t, Executes reconnect s t 7 ∧
      ReconnectResult s cs (nodeAt right label new sibling) t := by
  have localRep := ((represents_plug_iff h cs _).mp rep).1
  have localDistinct := AddressesDistinct.focus (cs := cs) distinct
  obtain ⟨_, _, no, _, dis⟩ := (nodeAt_distinct_iff ..).mp localDistinct
  let par : Record M (layout extra regs) :=
    record (if right then root sibling else root old)
      (if right then root old else root sibling) (contextParent cs) label
  have parentRead : s.heap[label.address]? = some par := by
    rw [frame _ no]
    cases right <;> exact localRep.1
  have oldRootNe : root sibling ≠ root old := by
    cases old with
    | nil => exact (oldNonempty rfl).elim
    | node o l r =>
      cases sibling with
      | nil => simp [root]
      | node b bl br =>
        intro eq
        have eq : b.address = o.address := Option.some.inj eq
        exact Finset.disjoint_left.mp dis (Finset.mem_insert_self _ _)
          (eq ▸ Finset.mem_insert_self _ _)
  cases new with
  | nil => exact (newNonempty rfl).elim
  | node a l r =>
    have read : s.deref 0 = some (record (root l) (root r) (some label.address) a) := by
      simpa [State.deref, cursor, root] using newRep.1
    have attached : par.ptr 0 = s.ptr 6 ∨ par.ptr 1 = s.ptr 6 := by
      cases right <;> simp [par, record, saved]
    obtain ⟨t, field, run, choice, selected, heap, data, ptr⟩ :=
      reconnect_child s _ par label.address pc read rfl parentRead attached
    have selectedField : field = if right then 1 else 0 := by
      rcases choice with rfl | rfl <;> cases right <;>
        simp_all [par, record]
    obtain ⟨parentRep, parentDistinct, exterior⟩ := replaceChild right h s.heap label old
      (.node a l r) sibling (contextParent cs) localRep localDistinct newRep newDistinct
      (by simpa only [same] using no)
      (by simpa only [same] using dis) frame
    have complete : Represents t.heap none
        (plug cs (nodeAt right label (.node a l r) sibling)) := by
      rw [heap, selectedField, cursor]
      exact rep.plug_of_frame distinct parentRep (by cases right <;> rfl) exterior
    have wholeDistinct := distinct.plug parentDistinct (by
      simp only [nodeAt_addresses, same])
    refine ⟨t, run, ⟨complete, wholeDistinct, ?_, ptr 0 (by simp [layout]) (by simp [layout])
      (by simp [layout]), data, ?_, ?_, payload_frame run⟩⟩
    · rw [ptr 1 (by simp [layout]) (by simp [layout]) (by simp [layout]), rootReg]
      exact root_plug_congr cs (by cases right <;> rfl)
    · simp [heap]
    · intro i _ h2 h3 h5
      exact ptr i h2 h3 h5

/-- Reattach a nonempty replacement with the original focus's footprint. Every hypothesis
about the changed heap is local to the focus; the whole-tree conclusion is proved by the
program. The root case takes five instructions and a proper ancestor takes seven. -/
theorem reconnect_context (h : List (Record M (layout extra regs)))
    (s : State M (layout extra regs)) (cs : List (Frame M extra))
    (old new : BinaryTree (Label M extra))
    (rep : Represents h none (plug cs old)) (distinct : AddressesDistinct (plug cs old))
    (newRep : Represents s.heap (contextParent cs) new) (newDistinct : AddressesDistinct new)
    (same : addresses new = addresses old)
    (frame : ∀ a, a ∉ addresses old → s.heap[a]? = h[a]?)
    (oldNonempty : old ≠ .nil) (newNonempty : new ≠ .nil)
    (pc : s.pc = 0) (cursor : s.ptr 0 = root new) (saved : s.ptr 6 = root old)
    (rootReg : s.ptr 1 = root (plug cs old)) :
    ∃ t time, Executes reconnect s t time ∧ time ≤ 7 ∧ ReconnectResult s cs new t := by
  cases cs with
  | nil =>
    cases new with
    | nil => exact (newNonempty rfl).elim
    | node a l r =>
      have read : s.deref 0 = some (record (root l) (root r) none a) := by
        simpa [State.deref, cursor, root, contextParent] using newRep.1
      obtain ⟨t, run, heap, data, rt, ptr⟩ := reconnect_root s _ pc read rfl
      refine ⟨t, 5, run, by simp, ⟨?_, newDistinct, rt.trans cursor, ?_, data,
        by rw [heap], ?_, payload_frame run⟩⟩
      · simpa only [heap, plug, contextParent] using newRep
      · exact ptr 0 (by simp [layout]) (by simp [layout]) (by simp [layout])
      · intro i h1 h2 _ h5
        exact ptr i h1 h2 h5
  | cons f cs =>
    cases f with
    | left label sibling =>
      obtain ⟨t, run, result⟩ := reconnect_below false h s cs label old new sibling rep distinct
        newRep newDistinct same frame oldNonempty newNonempty pc cursor saved rootReg
      exact ⟨t, 7, run, le_rfl, ⟨result.rep, result.distinct, result.root, result.cursor,
        result.data, result.size, result.ptr, result.payload⟩⟩
    | right sibling label =>
      obtain ⟨t, run, result⟩ := reconnect_below true h s cs label old new sibling rep distinct
        newRep newDistinct same frame oldNonempty newNonempty pc cursor saved rootReg
      exact ⟨t, 7, run, le_rfl, ⟨result.rep, result.distinct, result.root, result.cursor,
        result.data, result.size, result.ptr, result.payload⟩⟩

end Cslib.DataStructure.SearchTree.PointerMachine

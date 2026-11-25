/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.ReconnectContext
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Reconnect

/-!
# Reconnecting a changed focus inside its context, for the structured program

`reconnect_context` is the theorem of `ReconnectContext` for `Structured.reconnect`: after a
focus of a linked tree is replaced by a nonempty tree with the same addresses, reconnecting it
restores the representation of the whole tree, with the result `ReconnectResult`.

## Main results

* `reconnect_context`: reconnection takes at most eight instructions.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Structured

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

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
    (cursor : s.ptr 0 = root new) (saved : s.ptr 6 = root old)
    (rootReg : s.ptr 1 = root (plug cs (nodeAt right label old sibling))) :
    ∃ t, ExecWithin reconnect s t 8 ∧
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
        exact fun eq => Finset.disjoint_left.mp dis (Finset.mem_insert_self _ _)
          (Option.some.inj eq ▸ Finset.mem_insert_self _ _)
  cases new with
  | nil => exact (newNonempty rfl).elim
  | node a l r =>
    have read : s.deref 0 = some (record (root l) (root r) (some label.address) a) := by
      simpa [State.deref, cursor, root] using newRep.1
    have attached : par.ptr 0 = s.ptr 6 ∨ par.ptr 1 = s.ptr 6 := by
      cases right <;> simp [par, record, saved]
    obtain ⟨t, field, run, choice, selected, heap, data, ptr⟩ :=
      reconnect_child s _ par label.address read rfl parentRead attached
    have selectedField : field = if right then 1 else 0 := by
      rcases choice with rfl | rfl <;> cases right <;> simp_all [par, record]
    obtain ⟨parentRep, parentDistinct, exterior⟩ := replaceChild right h s.heap label old
      (.node a l r) sibling (contextParent cs) localRep localDistinct newRep newDistinct
      (by simpa only [same] using no) (by simpa only [same] using dis) frame
    have complete : Represents t.heap none
        (plug cs (nodeAt right label (.node a l r) sibling)) := by
      rw [heap, selectedField, cursor]
      exact rep.plug_of_frame distinct parentRep (by cases right <;> rfl) exterior
    have wholeDistinct := distinct.plug parentDistinct (by simp only [nodeAt_addresses, same])
    refine ⟨t, run, ⟨complete, wholeDistinct, ?_, ptr 0 (by simp [layout]) (by simp [layout])
      (by simp [layout]), data, by simp [heap], fun i _ h2 h3 h5 => ptr i h2 h3 h5, ?_⟩⟩
    · rw [ptr 1 (by simp [layout]) (by simp [layout]) (by simp [layout]), rootReg]
      exact root_plug_congr cs (by cases right <;> rfl)
    · intro b f
      rw [heap]
      by_cases hb : label.address = b
      · subst hb
        simp [List.getElem?_modify_eq, Option.map_map, Function.comp_def]
      · simp [List.getElem?_modify_ne _ _ hb]

/-- Reattach a nonempty replacement with the original focus's footprint. Every hypothesis
about the changed heap is local to the focus; the whole-tree conclusion is proved by the
program. The root case takes four instructions and a proper ancestor at most eight. -/
theorem reconnect_context (h : List (Record M (layout extra regs)))
    (s : State M (layout extra regs)) (cs : List (Frame M extra))
    (old new : BinaryTree (Label M extra))
    (rep : Represents h none (plug cs old)) (distinct : AddressesDistinct (plug cs old))
    (newRep : Represents s.heap (contextParent cs) new) (newDistinct : AddressesDistinct new)
    (same : addresses new = addresses old)
    (frame : ∀ a, a ∉ addresses old → s.heap[a]? = h[a]?)
    (oldNonempty : old ≠ .nil) (newNonempty : new ≠ .nil)
    (cursor : s.ptr 0 = root new) (saved : s.ptr 6 = root old)
    (rootReg : s.ptr 1 = root (plug cs old)) :
    ∃ t, ExecWithin reconnect s t 8 ∧ ReconnectResult s cs new t := by
  cases cs with
  | nil =>
    cases new with
    | nil => exact (newNonempty rfl).elim
    | node a l r =>
      have read : s.deref 0 = some (record (root l) (root r) none a) := by
        simpa [State.deref, cursor, root, contextParent] using newRep.1
      obtain ⟨t, run, heap, data, rt, ptr⟩ := reconnect_root s _ read rfl
      refine ⟨t, run.mono (by omega), ⟨?_, newDistinct, rt.trans cursor, ?_, data,
        by rw [heap], ?_, fun _ _ => by rw [heap]⟩⟩
      · simpa only [heap, plug, contextParent] using newRep
      · exact ptr 0 (by simp [layout]) (by simp [layout]) (by simp [layout])
      · exact fun i h1 h2 _ h5 => ptr i h1 h2 h5
  | cons f cs =>
    cases f with
    | left label sibling =>
      obtain ⟨t, run, result⟩ := reconnect_below false h s cs label old new sibling rep distinct
        newRep newDistinct same frame oldNonempty newNonempty cursor saved rootReg
      exact ⟨t, run, ⟨result.rep, result.distinct, result.root, result.cursor,
        result.data, result.size, result.ptr, result.payload⟩⟩
    | right sibling label =>
      obtain ⟨t, run, result⟩ := reconnect_below true h s cs label old new sibling rep distinct
        newRep newDistinct same frame oldNonempty newNonempty cursor saved rootReg
      exact ⟨t, run, ⟨result.rep, result.distinct, result.root, result.cursor,
        result.data, result.size, result.ptr, result.payload⟩⟩

end Cslib.DataStructure.SearchTree.PointerMachine.Structured

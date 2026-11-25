/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Allocation
public import CslibFrontier.Computability.PointerMachine.Blocks

/-!
# Allocating and attaching a leaf

`insertLeaf` fills a vacant child link of parent register two, or initializes root register one
when the parent is null. The side is fixed in the program. The original construction below
proves the exact heap update, fresh leaf representation and instruction count; ordering and
rebalancing belong to callers.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

/-- Attach cursor zero to the selected child of parent two, or set root one if parent is null.
Register five is scratch. -/
@[expose] def attachLeaf (side : Fin 2) : List (Instr M (layout extra regs)) :=
  [.null 5, .ifPtrEq 2 5 4, .storePtr side.castSucc 2 0, .halt, .movePtr 1 0, .halt]

/-- Allocate a leaf with the supplied scalar fields and attach it at the selected vacant link.
The null-parent case initializes root register one. -/
@[expose] def insertLeaf (source : Fin (extra + 1) → Fin (regs + 2)) (side : Fin 2) :
    List (Instr M (layout extra regs)) :=
  Cslib.PointerMachine.sequence (allocate source) (attachLeaf side)

private theorem attach_correct (side : Fin 2) (x : State M (layout extra regs))
    (pc : x.pc = 0) :
    ∃ y, Executes (attachLeaf side) x y 4 ∧
      y.heap = (x.modify 2 (fun n =>
        { n with ptr := Function.update n.ptr side.castSucc (x.ptr 0) })).heap ∧
      y.ptr = Function.update (Function.update x.ptr 5 none) 1
        (if x.ptr 2 = none then x.ptr 0 else x.ptr 1) ∧ y.data = x.data := by
  let s₁ := { x.setPtr 5 none with pc := 1 }
  let s₂ := { s₁ with pc := if x.ptr 2 = none then 4 else 2 }
  let y : State M (layout extra regs) :=
    { x with
      pc := if x.ptr 2 = none then 5 else 3
      heap := (x.modify 2 (fun n =>
        { n with ptr := Function.update n.ptr side.castSucc (x.ptr 0) })).heap
      ptr := Function.update (Function.update x.ptr 5 none) 1
        (if x.ptr 2 = none then x.ptr 0 else x.ptr 1) }
  refine ⟨y, ⟨3, .head x s₁ _ _ (by simp [step, attachLeaf, pc, s₁, Instr.effect, Instr.next])
    (.head s₁ s₂ _ _ (by cases hp : x.ptr 2 <;>
      simp [step, attachLeaf, s₁, s₂, Instr.effect, Instr.next, State.setPtr, hp])
    (.single (by cases hp : x.ptr 2 <;>
      simp [step, attachLeaf, s₁, s₂, y, Instr.effect, Instr.next, State.setPtr,
        State.modify, hp]))), by cases hp : x.ptr 2 <;> simp [attachLeaf, y, hp], rfl⟩,
    rfl, rfl, rfl⟩

/-- Filling a vacant child slot (or empty root) costs exactly `extra + 9` instructions.
The new leaf has the complete supplied payload and parent link. The heap formula preserves every
old record except the selected parent's child link; all scalar registers and pointer registers
other than cursor, root and null scratch are unchanged. No ordering or balance is asserted. -/
theorem insertLeaf_correct (source : Fin (extra + 1) → Fin (regs + 2)) (side : Fin 2)
    (x : State M (layout extra regs)) (pc : x.pc = 0)
    (vacant : match x.ptr 2 with
      | none => x.ptr 1 = none
      | some a => ∃ par, x.heap[a]? = some par ∧ par.ptr side.castSucc = none) :
    let label : Label M extra := ⟨x.heap.length, fun f => x.data (source f)⟩
    let heap := x.heap ++ [record none none (x.ptr 2) label]
    ∃ y, Executes (insertLeaf source side) x y (extra + 9) ∧
      y.heap = (match x.ptr 2 with
        | none => heap
        | some a => heap.modify a
            (fun n =>
              { n with ptr := Function.update n.ptr side.castSucc (some x.heap.length) })) ∧
      Represents y.heap (x.ptr 2) (.node label .nil .nil) ∧
      y.heap.length = x.heap.length + 1 ∧
      y.ptr 0 = some x.heap.length ∧
      y.ptr 1 = (if x.ptr 2 = none then some x.heap.length else x.ptr 1) ∧
      y.data = x.data ∧ y.ptr 5 = none ∧
      (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 5 → y.ptr i = x.ptr i) ∧
      (∀ a par, x.ptr 2 = some a → x.heap[a]? = some par →
        y.heap[a]? = some
          { par with ptr := Function.update par.ptr side.castSucc (some x.heap.length) }) := by
  intro label heap
  obtain ⟨a, alloc, ah, ap, ad, _⟩ := allocate_correct source x pc
  obtain ⟨b, attach, bh, bp, bd⟩ := attach_correct side { a with pc := 0 } rfl
  let y := { b with pc := (allocate (M := M) source).length +
      (attachLeaf (M := M) (extra := extra) (regs := regs) side).length }
  have hheap : y.heap = match x.ptr 2 with
      | none => heap
      | some p => heap.modify p fun n =>
          { n with ptr := Function.update n.ptr side.castSucc (some x.heap.length) } := by
    cases hp : x.ptr 2 <;> simpa [y, heap, label, State.modify, ap, ah, hp] using bh
  refine ⟨y, by simpa only [insertLeaf, Nat.add_assoc] using alloc.sequence attach, hheap, ?_,
    by cases hp : x.ptr 2 <;> simp [hheap, heap, hp],
    by simp [y, bp, ap], by simp [y, bp, ap], bd.trans ad,
    by simp [y, bp], fun i h0 h1 h5 => by simp [y, bp, ap, h0, h1, h5], fun p par hp get => ?_⟩
  · rw [hheap]
    cases hp : x.ptr 2 with
    | none => simp [Represents, root, heap, label, hp]
    | some p =>
      obtain ⟨par, get, _⟩ := hp ▸ vacant
      have bound : p < x.heap.length := (List.getElem?_eq_some_iff.mp get).1
      rw [Represents, List.getElem?_modify_ne _ _ (by omega : p ≠ x.heap.length)]
      simp [Represents, root, heap, label, hp]
  · simp [hheap, heap, hp, List.getElem?_append_left (List.getElem?_eq_some_iff.mp get).1, get]

end Cslib.DataStructure.SearchTree.PointerMachine

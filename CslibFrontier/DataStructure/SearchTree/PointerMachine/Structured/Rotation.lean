/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Rotation
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Registers

/-!
# Subtree rotation as a structured pointer-machine program

`Structured.rotate right` promotes the child of the cursor on the selected side, in nine
instructions. One program and one proof cover both rotations: the heap it produces is `rewire`,
whose effect on a represented tree is `represents_rewire_rotate`.

What the program leaves unchanged is read off its text: it assigns pointer registers zero, two,
three and four and no data register.

## Main results

* `rotate_represents`: a rotation preserves the recursive subtree representation.
-/

public section

namespace Cslib.DataStructure.SearchTree.PointerMachine.Structured

open Cslib.PointerMachine

variable {M : Model} {extra regs : ℕ}

open Register in
/-- Promote the child `near` of the cursor; `far` is the other side. The scratch pointers hold
the promoted node, the external parent and the middle subtree. -/
@[expose] def rotateFields (near far : Fin 3) : Code M (layout extra regs) := pm[
  pivot ← cur[near];
  up ← cur[parent];
  mid ← pivot[far];
  cur[near] ← mid;
  mid[parent] ← cur;
  pivot[far] ← cur;
  cur[parent] ← pivot;
  pivot[parent] ← up;
  cur ← pivot ]

/-- Promote the child of the cursor on the selected side; repair pivot and middle parent
links. -/
@[expose] def rotate (right : Bool) : Code M (layout extra regs) :=
  rotateFields (childField right) (childField !right)

/-- A rotation preserves the full recursive subtree representation, including parent links, in
nine instructions: `y` with child `x` on the selected side becomes `x` with `y` on the other
side, and the cursor moves from `y` to `x`. The external parent's child link and cached heights
are the caller's responsibility. Records outside the pivots and the middle root are
preserved. -/
theorem rotate_represents (right : Bool) (s : State M (layout extra regs))
    (x y : Label M extra) (a b c : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents s.heap parent (nodeAt right y (nodeAt right x a b) c))
    (distinct : AddressesDistinct (nodeAt right y (nodeAt right x a b) c))
    (cursor : s.ptr 0 = some y.address) :
    ∃ t, ExecWithin (rotate right) s t 9 ∧
      Represents t.heap parent (nodeAt right x a (nodeAt right y b c)) ∧
      t.ptr 0 = some x.address ∧ t.heap.length = s.heap.length ∧
      ∀ z, z ≠ x.address → z ≠ y.address → root b ≠ some z → t.heap[z]? = s.heap[z]? := by
  have hy : s.heap[y.address]? = some (record (if right then root c else some x.address)
      (if right then some x.address else root c) parent y) := by
    cases right <;> exact rep.1
  have hx : s.heap[x.address]? = some (record (if right then root b else root a)
      (if right then root a else root b) (some y.address) x) := by
    cases right
    · exact rep.2.1.1
    · exact rep.2.2.1
  have exec : ∃ t, ExecWithin (rotate right) s t 9 ∧ t.ptr 0 = some x.address ∧
      t.heap = rewire (childField right) (childField !right) s.heap x.address y.address (root b)
        parent := by
    apply WP.exists_execWithin
    pm_exec [rotate, rotateFields]
    cases right <;> cases middle : root b <;>
      simp [State.deref, State.modify, cursor, hy, hx, middle, rewire, record, childField]
  obtain ⟨t, run, cur, heap⟩ := exec
  refine ⟨t, run, heap ▸ represents_rewire_rotate right s.heap x y a b c parent rep distinct, cur,
    by rw [heap, length_rewire], fun z zx zy zb => ?_⟩
  rw [heap]
  exact rewire_frame _ _ _ _ _ _ _ _ zx zy zb

/-! Frames of `rotate`, for the programs that call it. -/

@[simp] theorem rotate_keepsSize (right : Bool) :
    (rotate right : Code M (layout extra regs)).KeepsSize := by
  pm_frame

@[simp] theorem rotate_dataDests (right : Bool) :
    (rotate right : Code M (layout extra regs)).dataDests = [] :=
  rfl

@[simp] theorem rotate_fieldDests (right : Bool) :
    (rotate right : Code M (layout extra regs)).fieldDests = [] :=
  rfl

end Cslib.DataStructure.SearchTree.PointerMachine.Structured

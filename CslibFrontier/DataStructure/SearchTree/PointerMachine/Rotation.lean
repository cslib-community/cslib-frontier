/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Representation
public import Mathlib.Data.Tree.Get
import Mathlib.Tactic.FinCases

/-!
# Pointer-machine subtree rotations

The programs promote either child of the cursor. It repairs both pivot parent links
and the middle subtree's parent link, including the empty-middle case. The caller must
reconnect the external parent's child link (or update its root register). Scalar payloads,
including cached heights, are unchanged; height recomputation belongs to AVL balancing.

The child rewiring adapts Stefan Langerman's earlier `lean-bst` rotation programs,
extended here with parent links.
-/

public section
namespace Cslib.DataStructure.SearchTree.PointerMachine
open Cslib.PointerMachine
variable {M : Model} {extra regs : ℕ}

/-- Promote the selected child of cursor zero. Scratch pointers two, three and four
hold the promoted node, external parent and middle subtree. No scalar register changes. -/
private def rotate (near far : Fin 3) : List (Instr M (layout extra regs)) :=
  [.loadPtr 2 near 0, .loadPtr 3 2 0, .loadPtr 4 far 2,
   .storePtr near 0 4, .storePtr 2 4 0, .storePtr far 2 0,
   .storePtr 2 0 2, .storePtr 2 2 3, .movePtr 0 2, .halt]

/-- Promote the left child of cursor zero; repair pivot and middle parent links. -/
@[expose] def rotateRight : List (Instr M (layout extra regs)) :=
  [.loadPtr 2 0 0, .loadPtr 3 2 0, .loadPtr 4 1 2,
   .storePtr 0 0 4, .storePtr 2 4 0, .storePtr 1 2 0,
   .storePtr 2 0 2, .storePtr 2 2 3, .movePtr 0 2, .halt]

/-- Promote the right child of cursor zero; repair pivot and middle parent links. -/
@[expose] def rotateLeft : List (Instr M (layout extra regs)) :=
  [.loadPtr 2 1 0, .loadPtr 3 2 0, .loadPtr 4 0 2,
   .storePtr 1 0 4, .storePtr 2 4 0, .storePtr 0 2 0,
   .storePtr 2 0 2, .storePtr 2 2 3, .movePtr 0 2, .halt]

private def tick (i : Instr M (layout extra regs)) (s : State M (layout extra regs)) :=
  { i.effect s with pc := s.pc + 1 }

private def finish (near far : Fin 3) (s : State M (layout extra regs)) :
    State M (layout extra regs) :=
  tick (.movePtr 0 2) (tick (.storePtr 2 2 3) (tick (.storePtr 2 0 2)
    (tick (.storePtr far 2 0) (tick (.storePtr 2 4 0) (tick (.storePtr near 0 4)
      (tick (.loadPtr 4 far 2) (tick (.loadPtr 3 2 0) (tick (.loadPtr 2 near 0) s))))))))

private theorem runs (near far : Fin 3) (s : State M (layout extra regs)) (pc : s.pc = 0) :
    Executes (rotate near far) s (finish near far s) 10 := by
  let s1 := tick (.loadPtr 2 near 0) s
  let s2 := tick (.loadPtr 3 2 0) s1
  let s3 := tick (.loadPtr 4 far 2) s2
  let s4 := tick (.storePtr near 0 4) s3
  let s5 := tick (.storePtr 2 4 0) s4
  let s6 := tick (.storePtr far 2 0) s5
  let s7 := tick (.storePtr 2 0 2) s6
  let s8 := tick (.storePtr 2 2 3) s7
  refine ⟨9, .head s s1 _ _ ?_ (.head s1 s2 _ _ ?_ (.head s2 s3 _ _ ?_
    (.head s3 s4 _ _ ?_ (.head s4 s5 _ _ ?_ (.head s5 s6 _ _ ?_
      (.head s6 s7 _ _ ?_ (.head s7 s8 _ _ ?_ (.single ?_)))))))), ?_, rfl⟩
  all_goals simp [step, rotate, finish, s1, s2, s3, s4, s5, s6, s7, s8, tick,
    Instr.next, pc]

/-- The exact heap writes of a rotation, in execution order. A null middle
subtree requires no parent write. Pivot addresses are proof data, not machine inputs. -/
private def rewire (near far : Fin 3) (h : List (Record M (layout extra regs))) (x y : ℕ)
    (middle parent : Pointer) : List (Record M (layout extra regs)) :=
  let h := h.modify y fun r => { r with ptr := Function.update r.ptr near middle }
  let h := middle.elim h fun b =>
    h.modify b fun r => { r with ptr := Function.update r.ptr 2 (some y) }
  let h := h.modify x fun r => { r with ptr := Function.update r.ptr far (some y) }
  let h := h.modify y fun r => { r with ptr := Function.update r.ptr 2 (some x) }
  h.modify x fun r => { r with ptr := Function.update r.ptr 2 parent }

/-- A rotation executes ten instructions, including halt. The heap is exactly
the five local pointer writes; all scalar registers and nonscratch pointers survive.
This is the machine execution lemma, not yet a whole-tree rotation invariant. -/
private theorem rotate_executes (near far : Fin 3) (s : State M (layout extra regs)) (x y : ℕ)
    (rx ry : Record M (layout extra regs)) (pc : s.pc = 0)
    (cursor : s.ptr 0 = some y) (hy : s.heap[y]? = some ry)
    (hx : s.heap[x]? = some rx) (left : ry.ptr near = some x) :
    ∃ t, Executes (rotate near far) s t 10 ∧
      t.heap = rewire near far s.heap x y (rx.ptr far) (ry.ptr 2) ∧
      t.ptr 0 = some x ∧ t.data = s.data ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → t.ptr i = s.ptr i) := by
  have keep : ∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 →
      (finish near far s).ptr i = s.ptr i := by
    intro i h0 h2 h3 h4
    cases mid : rx.ptr far <;>
      simp [finish, tick, Instr.effect, State.deref, State.setPtr, State.modify,
        cursor, hy, hx, left, mid, h0, h2, h3, h4]
  refine ⟨finish near far s, runs near far s pc, ?_, ?_, ?_, keep⟩
  all_goals cases mid : rx.ptr far <;>
    simp [finish, tick, Instr.effect, State.deref, State.setPtr, State.modify,
      cursor, hy, hx, left, mid, rewire]

/-- Records outside the pivots and the middle root are unchanged. -/
private theorem rewire_frame (near far : Fin 3)
    (h : List (Record M (layout extra regs))) (x y a : ℕ)
    (middle parent : Pointer) (ax : a ≠ x) (ay : a ≠ y) (am : middle ≠ some a) :
    (rewire near far h x y middle parent)[a]? = h[a]? := by
  cases middle with
  | none => simp [rewire, Ne.symm ax, Ne.symm ay]
  | some b =>
    have ab : b ≠ a := fun eq => am (congrArg some eq)
    simp [rewire, Ne.symm ax, Ne.symm ay, ab]

/-- Rotation creates no records. -/
private theorem length_rewire (near far : Fin 3) (h : List (Record M (layout extra regs))) (x y : ℕ)
    (middle parent : Pointer) : (rewire near far h x y middle parent).length = h.length := by
  cases middle <;> simp [rewire]


/-- For distinct pivots and a middle root distinct from both, the promoted node
points along the far field to the old root and inherits its parent; the old root points
along the near field to the middle subtree and has the promoted node as parent.
Scalar fields are preserved. -/
private theorem rewire_pivots (near far : Fin 3) (h : List (Record M (layout extra regs))) (x y : ℕ)
    (rx ry : Record M (layout extra regs)) (hx : h[x]? = some rx)
    (hy : h[y]? = some ry) (different : x ≠ y)
    (mx : rx.ptr far ≠ some x) (my : rx.ptr far ≠ some y) :
    let h' := rewire near far h x y (rx.ptr far) (ry.ptr 2)
    h'[x]? = some { rx with ptr := (Function.update
      (Function.update rx.ptr far (some y)) 2 (ry.ptr 2)) } ∧
    h'[y]? = some { ry with ptr := (Function.update
      (Function.update ry.ptr near (rx.ptr far)) 2 (some x)) } := by
  cases mid : rx.ptr far with
  | none => simp [rewire, different, Ne.symm different, hx, hy]
  | some b =>
    have bx : b ≠ x := fun eq => mx (mid.trans (congrArg some eq))
    have by' : b ≠ y := fun eq => my (mid.trans (congrArg some eq))
    simp [rewire, different, Ne.symm different, bx, by', hx, hy]

/-- The middle subtree changes only its root's parent link. -/
private theorem rewire_middle (near far : Fin 3)
    (h : List (Record M (layout extra regs))) (x y b : ℕ)
    (rb : Record M (layout extra regs)) (hb : h[b]? = some rb)
    (bx : b ≠ x) (by' : b ≠ y) (parent : Pointer) :
    (rewire near far h x y (some b) parent)[b]? =
      some { rb with ptr := Function.update rb.ptr 2 (some y) } := by
  simp [rewire, Ne.symm bx, Ne.symm by', hb]



private def unrotatePath : PosNum → PosNum
  | .one => .bit0 .one
  | .bit0 p => .bit0 (.bit0 p)
  | .bit1 .one => .one
  | .bit1 (.bit0 p) => .bit0 (.bit1 p)
  | .bit1 (.bit1 p) => .bit1 p

private def rotatePath : PosNum → PosNum
  | .one => .bit1 .one
  | .bit0 .one => .one
  | .bit0 (.bit0 p) => .bit0 p
  | .bit0 (.bit1 p) => .bit1 (.bit0 p)
  | .bit1 p => .bit1 (.bit1 p)

private theorem unrotatePath_injective : Function.Injective unrotatePath := by
  apply Function.LeftInverse.injective (g := rotatePath)
  intro p
  cases p with
  | one => rfl
  | bit0 p => rfl
  | bit1 p => cases p <;> rfl

/-- Address separation survives rotation, so the result can be rotated again. -/
theorem AddressesDistinct.rotateRight {x y : Label M extra}
    {a b c : BinaryTree (Label M extra)}
    (h : AddressesDistinct (.node y (.node x a b) c)) :
    AddressesDistinct (.node x a (.node y b c)) := by
  have get (p : PosNum) :
      (.node y (.node x a b) c : BinaryTree (Label M extra)).get (unrotatePath p) =
      (.node x a (.node y b c) : BinaryTree (Label M extra)).get p := by
    cases p with
    | one => rfl
    | bit0 p => rfl
    | bit1 p => cases p <;> rfl
  intro p q u v hp hq eq
  apply unrotatePath_injective
  exact h _ _ u v ((get p).trans hp) ((get q).trans hq) eq

private theorem rotatePath_injective : Function.Injective rotatePath := by
  apply Function.LeftInverse.injective (g := unrotatePath)
  intro p
  cases p with
  | one => rfl
  | bit0 p => cases p <;> rfl
  | bit1 p => rfl

/-- Address separation also survives the inverse, left rotation. -/
theorem AddressesDistinct.rotateLeft {x y : Label M extra}
    {a b c : BinaryTree (Label M extra)}
    (h : AddressesDistinct (.node x a (.node y b c))) :
    AddressesDistinct (.node y (.node x a b) c) := by
  have get (p : PosNum) :
      (.node x a (.node y b c) : BinaryTree (Label M extra)).get (rotatePath p) =
      (.node y (.node x a b) c : BinaryTree (Label M extra)).get p := by
    cases p with
    | one => rfl
    | bit0 p => cases p <;> rfl
    | bit1 p => rfl
  intro p q u v hp hq eq
  apply rotatePath_injective
  exact h _ _ u v ((get p).trans hp) ((get q).trans hq) eq

/-- A right rotation preserves the full recursive subtree representation, including
parent links, in ten actual instructions. The external parent's child link and cached
heights are the caller's responsibility. Registers outside the scratch set and records
outside the pivots and middle root are preserved. -/
theorem rotateRight_represents (s : State M (layout extra regs))
    (x y : Label M extra) (a b c : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents s.heap parent (.node y (.node x a b) c))
    (distinct : AddressesDistinct (.node y (.node x a b) c))
    (cursor : s.ptr 0 = some y.address) (pc : s.pc = 0) :
    ∃ t, Executes rotateRight s t 10 ∧
      Represents t.heap parent (.node x a (.node y b c)) ∧
      t.ptr 0 = some x.address ∧ t.data = s.data ∧ t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → t.ptr i = s.ptr i) ∧
      (∀ z, z ≠ x.address → z ≠ y.address → root b ≠ some z →
        t.heap[z]? = s.heap[z]?) := by
  rcases rep with ⟨hy, ⟨hx, ha, hb⟩, hc⟩
  have sep {p q : PosNum} {u v : Label M extra}
      (hp : (BinaryTree.node y (.node x a b) c).get p = some u)
      (hq : (BinaryTree.node y (.node x a b) c).get q = some v) (pq : p ≠ q) :
      u.address ≠ v.address := fun eq => pq (distinct p q u v hp hq eq)
  have xy : x.address ≠ y.address := sep (p := .bit0 .one) rfl (q := .one) rfl (by decide)
  have bx : root b ≠ some x.address := by
    cases b with
    | nil => simp [root]
    | node z l r =>
      exact fun h => sep (p := .bit0 (.bit1 .one)) rfl (q := .bit0 .one) rfl
        (by decide) (Option.some.inj h)
  have by' : root b ≠ some y.address := by
    cases b with
    | nil => simp [root]
    | node z l r =>
      exact fun h => sep (p := .bit0 (.bit1 .one)) rfl (q := .one) rfl
        (by decide) (Option.some.inj h)
  obtain ⟨t, exec, heap, cur, data, keep⟩ := rotate_executes 0 1 s x.address y.address
    (record (root a) (root b) (some y.address) x)
    (record (some x.address) (root c) parent y) pc cursor hy hx rfl
  have pivots := rewire_pivots 0 1 s.heap x.address y.address
    (record (root a) (root b) (some y.address) x)
    (record (some x.address) (root c) parent y) hx hy xy bx by'
  change
    (rewire 0 1 s.heap x.address y.address (root b) parent)[x.address]? = _ ∧
    (rewire 0 1 s.heap x.address y.address (root b) parent)[y.address]? = _ at pivots
  refine ⟨t, exec, ?_, cur, data, ?_, keep, ?_⟩
  · rw [heap]
    change Represents (rewire 0 1 s.heap x.address y.address (root b) parent)
      parent (.node x a (.node y b c))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [pivots.1]
      simp only [record, Option.some.injEq, Record.mk.injEq]
      exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
    · apply Represents.congr ha
      intro p u hp
      apply rewire_frame
      · exact sep (p := .bit0 (.bit0 p)) hp (q := .bit0 .one) rfl (by simp)
      · exact sep (p := .bit0 (.bit0 p)) hp (q := .one) rfl (by simp)
      · cases b with
        | nil => simp [root]
        | node z l r =>
          exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
            (q := .bit0 (.bit0 p)) hp (by simp) (Option.some.inj h)
    · rw [pivots.2]
      simp only [record, Option.some.injEq, Record.mk.injEq]
      exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
    · cases b with
      | nil => trivial
      | node z l r =>
        refine ⟨?_, ?_, ?_⟩
        · have hb := rewire_middle 0 1 s.heap x.address y.address z.address
            (record (root l) (root r) (some x.address) z) hb.1
            (sep (p := .bit0 (.bit1 .one)) rfl (q := .bit0 .one) rfl (by decide))
            (sep (p := .bit0 (.bit1 .one)) rfl (q := .one) rfl (by decide)) parent
          simp only [root]
          rw [hb]
          simp only [record, Option.some.injEq, Record.mk.injEq]
          exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
        · apply Represents.congr hb.2.1
          intro p u hp
          apply rewire_frame
          · exact sep (p := .bit0 (.bit1 (.bit0 p))) hp (q := .bit0 .one) rfl (by simp)
          · exact sep (p := .bit0 (.bit1 (.bit0 p))) hp (q := .one) rfl (by simp)
          · exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
              (q := .bit0 (.bit1 (.bit0 p))) hp (by simp) (Option.some.inj h)
        · apply Represents.congr hb.2.2
          intro p u hp
          apply rewire_frame
          · exact sep (p := .bit0 (.bit1 (.bit1 p))) hp (q := .bit0 .one) rfl (by simp)
          · exact sep (p := .bit0 (.bit1 (.bit1 p))) hp (q := .one) rfl (by simp)
          · exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
              (q := .bit0 (.bit1 (.bit1 p))) hp (by simp) (Option.some.inj h)
    · apply Represents.congr hc
      intro p u hp
      apply rewire_frame
      · exact sep (p := .bit1 p) hp (q := .bit0 .one) rfl (by simp)
      · exact sep (p := .bit1 p) hp (q := .one) rfl (by simp)
      · cases b with
        | nil => simp [root]
        | node z l r =>
          exact fun h => sep (p := .bit0 (.bit1 .one)) rfl
            (q := .bit1 p) hp (by simp) (Option.some.inj h)
  · rw [heap]
    exact length_rewire _ _ _ _ _ _ _
  · intro z zx zy zb
    rw [heap]
    exact rewire_frame _ _ _ _ _ _ _ _ zx zy zb

/-- A left rotation preserves the full recursive subtree representation, including
parent links, in ten actual instructions. The external parent's child link and cached
heights are the caller's responsibility. Registers outside the scratch set and records
outside the pivots and middle root are preserved. -/
theorem rotateLeft_represents (s : State M (layout extra regs))
    (x y : Label M extra) (a b c : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents s.heap parent (.node y a (.node x b c)))
    (distinct : AddressesDistinct (.node y a (.node x b c)))
    (cursor : s.ptr 0 = some y.address) (pc : s.pc = 0) :
    ∃ t, Executes rotateLeft s t 10 ∧
      Represents t.heap parent (.node x (.node y a b) c) ∧
      t.ptr 0 = some x.address ∧ t.data = s.data ∧ t.heap.length = s.heap.length ∧
      (∀ i, i ≠ 0 → i ≠ 2 → i ≠ 3 → i ≠ 4 → t.ptr i = s.ptr i) ∧
      (∀ z, z ≠ x.address → z ≠ y.address → root b ≠ some z →
        t.heap[z]? = s.heap[z]?) := by
  rcases rep with ⟨hy, hc, hx, hb, ha⟩
  have sep {p q : PosNum} {u v : Label M extra}
      (hp : (BinaryTree.node y a (.node x b c)).get p = some u)
      (hq : (BinaryTree.node y a (.node x b c)).get q = some v) (pq : p ≠ q) :
      u.address ≠ v.address := fun eq => pq (distinct p q u v hp hq eq)
  have xy : x.address ≠ y.address := sep (p := .bit1 .one) rfl (q := .one) rfl (by decide)
  have bx : root b ≠ some x.address := by
    cases b with
    | nil => simp [root]
    | node z l r =>
      exact fun h => sep (p := .bit1 (.bit0 .one)) rfl (q := .bit1 .one) rfl
        (by decide) (Option.some.inj h)
  have by' : root b ≠ some y.address := by
    cases b with
    | nil => simp [root]
    | node z l r =>
      exact fun h => sep (p := .bit1 (.bit0 .one)) rfl (q := .one) rfl
        (by decide) (Option.some.inj h)
  obtain ⟨t, exec, heap, cur, data, keep⟩ := rotate_executes 1 0 s x.address y.address
    (record (root b) (root c) (some y.address) x)
    (record (root a) (some x.address) parent y) pc cursor hy hx rfl
  have pivots := rewire_pivots 1 0 s.heap x.address y.address
    (record (root b) (root c) (some y.address) x)
    (record (root a) (some x.address) parent y) hx hy xy bx by'
  change
    (rewire 1 0 s.heap x.address y.address (root b) parent)[x.address]? = _ ∧
    (rewire 1 0 s.heap x.address y.address (root b) parent)[y.address]? = _ at pivots
  refine ⟨t, exec, ?_, cur, data, ?_, keep, ?_⟩
  · rw [heap]
    change Represents (rewire 1 0 s.heap x.address y.address (root b) parent)
      parent (.node x (.node y a b) c)
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [pivots.1]
      simp only [record, Option.some.injEq, Record.mk.injEq]
      exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
    · rw [pivots.2]
      simp only [record, Option.some.injEq, Record.mk.injEq]
      exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
    · apply Represents.congr hc
      intro p u hp
      apply rewire_frame
      · exact sep (p := .bit0 p) hp (q := .bit1 .one) rfl (by simp)
      · exact sep (p := .bit0 p) hp (q := .one) rfl (by simp)
      · cases b with
        | nil => simp [root]
        | node z l r =>
          exact fun h => sep (p := .bit1 (.bit0 .one)) rfl
            (q := .bit0 p) hp (by simp) (Option.some.inj h)
    · cases b with
      | nil => trivial
      | node z l r =>
        refine ⟨?_, ?_, ?_⟩
        · have hb := rewire_middle 1 0 s.heap x.address y.address z.address
            (record (root l) (root r) (some x.address) z) hb.1
            (sep (p := .bit1 (.bit0 .one)) rfl (q := .bit1 .one) rfl (by decide))
            (sep (p := .bit1 (.bit0 .one)) rfl (q := .one) rfl (by decide)) parent
          simp only [root]
          rw [hb]
          simp only [record, Option.some.injEq, Record.mk.injEq]
          exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩
        · apply Represents.congr hb.2.1
          intro p u hp
          apply rewire_frame
          · exact sep (p := .bit1 (.bit0 (.bit0 p))) hp (q := .bit1 .one) rfl (by simp)
          · exact sep (p := .bit1 (.bit0 (.bit0 p))) hp (q := .one) rfl (by simp)
          · exact fun h => sep (p := .bit1 (.bit0 .one)) rfl
              (q := .bit1 (.bit0 (.bit0 p))) hp (by simp) (Option.some.inj h)
        · apply Represents.congr hb.2.2
          intro p u hp
          apply rewire_frame
          · exact sep (p := .bit1 (.bit0 (.bit1 p))) hp (q := .bit1 .one) rfl (by simp)
          · exact sep (p := .bit1 (.bit0 (.bit1 p))) hp (q := .one) rfl (by simp)
          · exact fun h => sep (p := .bit1 (.bit0 .one)) rfl
              (q := .bit1 (.bit0 (.bit1 p))) hp (by simp) (Option.some.inj h)
    · apply Represents.congr ha
      intro p u hp
      apply rewire_frame
      · exact sep (p := .bit1 (.bit1 p)) hp (q := .bit1 .one) rfl (by simp)
      · exact sep (p := .bit1 (.bit1 p)) hp (q := .one) rfl (by simp)
      · cases b with
        | nil => simp [root]
        | node z l r =>
          exact fun h => sep (p := .bit1 (.bit0 .one)) rfl
            (q := .bit1 (.bit1 p)) hp (by simp) (Option.some.inj h)
  · rw [heap]
    exact length_rewire _ _ _ _ _ _ _
  · intro z zx zy zb
    rw [heap]
    exact rewire_frame _ _ _ _ _ _ _ _ zx zy zb

end Cslib.DataStructure.SearchTree.PointerMachine

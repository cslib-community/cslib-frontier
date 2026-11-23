/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Child
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
@[expose] def rewire (near far : Fin 3) (h : List (Record M (layout extra regs))) (x y : ℕ)
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
theorem rewire_frame (near far : Fin 3)
    (h : List (Record M (layout extra regs))) (x y a : ℕ)
    (middle parent : Pointer) (ax : a ≠ x) (ay : a ≠ y) (am : middle ≠ some a) :
    (rewire near far h x y middle parent)[a]? = h[a]? := by
  cases middle with
  | none => simp [rewire, Ne.symm ax, Ne.symm ay]
  | some b =>
    have ab : b ≠ a := fun eq => am (congrArg some eq)
    simp [rewire, Ne.symm ax, Ne.symm ay, ab]

/-- Rotation creates no records. -/
theorem length_rewire (near far : Fin 3) (h : List (Record M (layout extra regs))) (x y : ℕ)
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



/-- The pointer field of the child on a side: zero on the left, one on the right. -/
@[expose] def childField (right : Bool) : Fin 3 := if right then 1 else 0

/-- Changing only the parent link of the root gives the representation under a new parent. -/
private theorem Represents.reparent {h k : List (Record M (layout extra regs))}
    {t : BinaryTree (Label M extra)} {parent parent' : Pointer} (rep : Represents h parent t)
    (distinct : AddressesDistinct t)
    (top : ∀ z, root t = some z → ∀ node, h[z]? = some node →
      k[z]? = some { node with ptr := Function.update node.ptr 2 parent' })
    (rest : ∀ z ∈ addresses t, root t ≠ some z → k[z]? = h[z]?) :
    Represents k parent' t := by
  cases t with
  | nil => trivial
  | node label l r =>
    obtain ⟨_, _, nl, nr, _⟩ := (AddressesDistinct.node_iff ..).mp distinct
    have inside (z : ℕ) (hz : z ∈ addresses l ∨ z ∈ addresses r) : k[z]? = h[z]? := by
      refine rest z ?_ ?_
      · change z ∈ Insert.insert label.address (addresses l ∪ addresses r)
        simpa using Or.inr hz
      · rintro eq
        cases Option.some.inj eq
        exact hz.elim nl nr
    refine ⟨?_, rep.2.1.congr_addresses fun z hz => inside z (.inl hz),
      rep.2.2.congr_addresses fun z hz => inside z (.inr hz)⟩
    rw [top _ rfl _ rep.1]
    simp only [record, Option.some.injEq, Record.mk.injEq]
    exact ⟨by funext i; fin_cases i <;> rfl, trivial⟩

/-- Address separation survives a rotation on either side. -/
theorem AddressesDistinct.rotate (right : Bool) {x y : Label M extra}
    {a b c : BinaryTree (Label M extra)}
    (h : AddressesDistinct (nodeAt right y (nodeAt right x a b) c)) :
    AddressesDistinct (nodeAt right x a (nodeAt right y b c)) := by
  simp only [nodeAt_distinct_iff, nodeAt_addresses, Finset.mem_insert, Finset.mem_union,
    Finset.disjoint_insert_left, Finset.disjoint_insert_right, Finset.disjoint_union_left,
    Finset.disjoint_union_right, not_or] at h ⊢
  obtain ⟨⟨da, db, xa, xb, ab⟩, dc, ⟨yx, ya, yb⟩, yc, xc, ac, bc⟩ := h
  exact ⟨da, ⟨db, dc, yb, yc, bc⟩, xa, ⟨Ne.symm yx, xb, xc⟩, ⟨ya, ab, ac⟩⟩

/-- The heap rewiring of a rotation on either side preserves the full recursive subtree
representation, including parent links: `y` with child `x` on the selected side, whose own
children are `a` on that side and `b` on the other, becomes `x` with `a` on that side and `y`
on the other, and `b` becomes the child of `y` on the selected side. This is a statement about
heaps: any program whose writes are `rewire` inherits it. -/
theorem represents_rewire_rotate (right : Bool) (h : List (Record M (layout extra regs)))
    (x y : Label M extra) (a b c : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents h parent (nodeAt right y (nodeAt right x a b) c))
    (distinct : AddressesDistinct (nodeAt right y (nodeAt right x a b) c)) :
    Represents (rewire (childField right) (childField !right) h x.address y.address (root b)
      parent) parent (nodeAt right x a (nodeAt right y b c)) := by
  obtain ⟨hy, hx, hc⟩ := (represents_nodeAt_iff ..).mp rep
  obtain ⟨hx, ha, hb⟩ := (represents_nodeAt_iff ..).mp hx
  simp only [nodeAt_distinct_iff, nodeAt_addresses, Finset.mem_insert, Finset.mem_union,
    Finset.disjoint_insert_left, Finset.disjoint_union_left, not_or] at distinct
  obtain ⟨⟨da, db, xa, xb, ab⟩, dc, ⟨yx, ya, yb⟩, yc, xc, ac, bc⟩ := distinct
  have xy : x.address ≠ y.address := Ne.symm yx
  have bx : root b ≠ some x.address := fun e => xb (root_mem_addresses e)
  have by' : root b ≠ some y.address := fun e => yb (root_mem_addresses e)
  rw [root_nodeAt] at hy
  have pivots := rewire_pivots (childField right) (childField !right) h x.address y.address
    _ _ hx hy xy (by cases right <;> exact bx) (by cases right <;> exact by')
  have middle : (record (regs := regs) (if right then root b else root a)
      (if right then root a else root b) (some y.address) x).ptr (childField !right) = root b := by
    cases right <;> rfl
  have up : (record (regs := regs) (if right then root c else some x.address)
      (if right then some x.address else root c) parent y).ptr 2 = parent := rfl
  dsimp only at pivots
  rw [middle, up] at pivots
  have frame (z : ℕ) (zx : z ≠ x.address) (zy : z ≠ y.address) (zb : root b ≠ some z) :=
    rewire_frame (childField right) (childField !right) h x.address y.address z (root b) parent
      zx zy zb
  refine (represents_nodeAt_iff ..).mpr ⟨?_, ?_, (represents_nodeAt_iff ..).mpr ⟨?_, ?_, ?_⟩⟩
  · rw [pivots.1, root_nodeAt]
    simp only [record, Option.some.injEq, Record.mk.injEq]
    exact ⟨by cases right <;> funext i <;> fin_cases i <;> rfl, trivial⟩
  · exact ha.congr_addresses fun z hz => frame z (fun e => xa (e ▸ hz)) (fun e => ya (e ▸ hz))
      (fun e => Finset.disjoint_left.mp ab hz (root_mem_addresses e))
  · rw [pivots.2]
    simp only [record, Option.some.injEq, Record.mk.injEq]
    exact ⟨by cases right <;> funext i <;> fin_cases i <;> rfl, trivial⟩
  · refine hb.reparent db (fun z hz node hn => ?_) fun z hz ne =>
      frame z (fun e => xb (e ▸ hz)) (fun e => yb (e ▸ hz)) ne
    rw [hz]
    exact rewire_middle _ _ h x.address y.address z node hn (fun e => bx (hz.trans (e ▸ rfl)))
      (fun e => by' (hz.trans (e ▸ rfl))) parent
  · exact hc.congr_addresses fun z hz => frame z (fun e => xc (e ▸ hz)) (fun e => yc (e ▸ hz))
      (fun e => Finset.disjoint_left.mp bc (root_mem_addresses e) hz)

/-- Address separation survives rotation, so the result can be rotated again. -/
theorem AddressesDistinct.rotateRight {x y : Label M extra}
    {a b c : BinaryTree (Label M extra)}
    (h : AddressesDistinct (.node y (.node x a b) c)) :
    AddressesDistinct (.node x a (.node y b c)) :=
  AddressesDistinct.rotate false h

/-- Address separation also survives the inverse, left rotation. -/
theorem AddressesDistinct.rotateLeft {x y : Label M extra}
    {a b c : BinaryTree (Label M extra)}
    (h : AddressesDistinct (.node x a (.node y b c))) :
    AddressesDistinct (.node y (.node x a b) c) :=
  AddressesDistinct.rotate (x := y) (y := x) true h

/-- The heap rewiring of a right rotation preserves the full recursive subtree
representation, including parent links. -/
theorem represents_rewire_rotateRight (h : List (Record M (layout extra regs)))
    (x y : Label M extra) (a b c : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents h parent (.node y (.node x a b) c))
    (distinct : AddressesDistinct (.node y (.node x a b) c)) :
    Represents (rewire 0 1 h x.address y.address (root b) parent) parent
      (.node x a (.node y b c)) :=
  represents_rewire_rotate false h x y a b c parent rep distinct

/-- The heap rewiring of a left rotation preserves the full recursive subtree
representation, including parent links. -/
theorem represents_rewire_rotateLeft (h : List (Record M (layout extra regs)))
    (x y : Label M extra) (a b c : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents h parent (.node y a (.node x b c)))
    (distinct : AddressesDistinct (.node y a (.node x b c))) :
    Represents (rewire 1 0 h x.address y.address (root b) parent) parent
      (.node x (.node y a b) c) :=
  represents_rewire_rotate true h x y c b a parent rep distinct

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
  have hy := rep.1
  have hx := rep.2.1.1
  obtain ⟨t, exec, heap, cur, data, keep⟩ := rotate_executes 0 1 s x.address y.address
    (record (root a) (root b) (some y.address) x)
    (record (some x.address) (root c) parent y) pc cursor hy hx rfl
  refine ⟨t, exec, ?_, cur, data, ?_, keep, ?_⟩
  · rw [heap]
    exact represents_rewire_rotateRight s.heap x y a b c parent rep distinct
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
  have hy := rep.1
  have hx := rep.2.2.1
  obtain ⟨t, exec, heap, cur, data, keep⟩ := rotate_executes 1 0 s x.address y.address
    (record (root b) (root c) (some y.address) x)
    (record (root a) (some x.address) parent y) pc cursor hy hx rfl
  refine ⟨t, exec, ?_, cur, data, ?_, keep, ?_⟩
  · rw [heap]
    exact represents_rewire_rotateLeft s.heap x y a b c parent rep distinct
  · rw [heap]
    exact length_rewire _ _ _ _ _ _ _
  · intro z zx zy zb
    rw [heap]
    exact rewire_frame _ _ _ _ _ _ _ _ zx zy zb

end Cslib.DataStructure.SearchTree.PointerMachine

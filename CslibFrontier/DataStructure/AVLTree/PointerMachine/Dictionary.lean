/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.DictionaryRepresentation

/-!
# Pointer-machine memory dictionary operations

The root lives in pointer register one. Scalar zero supplies the address, scalar three the
value to write or the result of a read. Scalars one and two are scratch; registers from four
onward belong to the simulated machine. Every access navigates ordinary AVL links.
-/

public section
namespace Cslib.DataStructure.AVLTree.PointerMachine.Dictionary
open Cslib.PointerMachine SearchTree.PointerMachine
variable {M : Model} {regs : ℕ}

/-- Read a dictionary address, returning the default value on a missing key. -/
@[expose] def read (zero : M.Op) (lt : M.Test) : List (Instr M (layout 2 (regs + 2))) :=
  sequence [.movePtr 0 1, .halt]
    (sequence (search lt) [.op zero 3 0 0, .loadData 3 2 0, .halt])

/-- Insert an absent key and replace the selected node's payload. Existing keys keep their
node address; scalar three supplies the fresh or replacement value. -/
@[expose] def write (zero maxSucc : M.Op) (lt heavy le : M.Test) :
    List (Instr M (layout 2 (regs + 2))) :=
  sequence [.movePtr 0 1, .halt]
    (sequence (PointerMachine.insert zero maxSucc lt heavy le 1 (fun _ => 3))
      (sequence [.movePtr 0 1, .halt] (sequence (search lt) [.storeData 2 0 3, .halt])))

private theorem reset_correct (s : State M (layout 2 (regs + 2))) (pc : s.pc = 0) :
    Executes [.movePtr 0 1, .halt] s { s.setPtr 0 (s.ptr 1) with pc := 1 } 2 := by
  refine ⟨1, .single ?_, rfl, rfl⟩
  simp [step, pc, Instr.effect, Instr.next]

private theorem load_correct (zero : M.Op) (value : M.Value)
    (zero_spec : ∀ a b, M.evalOp zero a b = value)
    (s : State M (layout 2 (regs + 2))) (pc : s.pc = 0) :
    let result := ((s.deref 0).map (fun n => n.data 2)).getD value
    Executes [.op zero 3 0 0, .loadData 3 2 0, .halt] s
      { s.setData 3 result with pc := 2 } 3 := by
  let a := { s.setData 3 value with pc := 1 }
  refine ⟨2, .head s a _ _ ?_ (.single ?_), rfl, rfl⟩
  · simp [step, pc, Instr.effect, Instr.next, zero_spec, a]
  · cases hd : s.deref 0 <;> simp only [State.deref] at hd <;>
      simp [step, a, Instr.effect, Instr.next, State.deref, hd, State.setData,
        Function.update_idem]

/-- A complete dictionary read follows the AVL search path and returns the represented value.
It preserves the heap, root, query, and every client scalar register. -/
theorem read_correct [LinearOrder M.Value] (zero : M.Op) (lt : M.Test)
    (encode : ℕ → M.Value) (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))
    (s : State M (layout 2 (regs + 2))) (tree : BinaryTree (Label M 2))
    (avl : AVLTree M.Value) (memory : M.Value → M.Value)
    (rep : Represents s.heap none tree) (matched : Matches encode 1 tree avl)
    (valid : avl.Valid) (stored : Stores (encode 0) tree memory)
    (rootReg : s.ptr 1 = root tree) (pc : s.pc = 0) :
    ∃ t time, Executes (read zero lt) s t time ∧
      time ≤ 6 * avl.cachedHeight + 10 ∧ t.heap = s.heap ∧ t.ptr 1 = s.ptr 1 ∧
      t.data 3 = memory (s.data 0) ∧
      (∀ i, i ≠ 1 → i ≠ 3 → t.data i = s.data i) := by
  let start := { s.setPtr 0 (s.ptr 1) with pc := 0 }
  obtain ⟨a, time, run, bound, result⟩ := search_correct lt compare start tree none rep
    (by simp [start, State.setPtr, rootReg]) rfl
  let value := ((a.deref 0).map (fun n => n.data 2)).getD (encode 0)
  have correctValue : value = memory (s.data 0) := by
    cases hp : a.ptr 0 with
    | none =>
      have missing : SearchTree.contains (s.data 0) (keys tree) = false := by
        simpa [start, State.setPtr, hp] using result.found.symm
      simp [value, State.deref, hp, stored.absent (matched.keys.symm ▸ valid.ordered) missing]
    | some address =>
      obtain ⟨path, label, node, get, _, lookup, fields, key⟩ := result.key address hp
      simp [value, start, State.setPtr, State.deref, hp, lookup, fields,
        stored.value path label get, (congrFun fields 0).symm.trans key]
  have finish := load_correct zero (encode 0) zero_spec { a with pc := 0 } rfl
  have executed := (reset_correct s pc).sequence (run.sequence finish)
  let t := { a.setData 3 value with pc := 2 + (sequence (search (regs := regs + 2) lt)
    ([.op zero 3 0 0, .loadData 3 2 0, .halt] : List (Instr M (layout 2 (regs + 2))))).length }
  have visits : SearchTree.searchVisits (s.data 0) (keys tree) ≤ avl.cachedHeight :=
    matched.keys ▸ AVLTree.searchVisits_le_cachedHeight valid.heightConsistent _
  refine ⟨t, 2 + (time + 3 + 1) + 1, executed, ?_, result.heap, ?_, ?_, ?_⟩
  · change time ≤ 6 * SearchTree.searchVisits (s.data 0) (keys tree) + 3 at bound
    omega
  · exact (result.ptr 1 (by simp [layout]) (by simp [layout])).trans
      (by simp [start, State.setPtr])
  · simpa [t, State.setData] using correctValue
  · intro i h1 h3
    simpa only [t, start, State.setPtr, State.setData, Function.update_of_ne h3] using
      result.data i h1

/-- The output dictionary implements a total-memory update and preserves client registers. -/
structure WriteResult [LinearOrder M.Value] (encode : ℕ → M.Value)
    (s t : State M (layout 2 (regs + 2))) (tree : BinaryTree (Label M 2))
    (avl : AVLTree M.Value) (memory : M.Value → M.Value) : Prop where
  /-- Heap records implement the output tree. -/
  rep : Represents t.heap none tree
  /-- Keys and height caches match functional AVL insertion. -/
  matched : Matches encode 1 tree (AVLTree.insert (s.data 0) avl)
  /-- Distinct tree positions have distinct addresses. -/
  distinct : AddressesDistinct tree
  /-- The scalar payloads implement the written total memory. -/
  stored : Stores (encode 0) tree (Function.update memory (s.data 0) (s.data 3))
  /-- Pointer one tracks the resulting root. -/
  root : t.ptr 1 = SearchTree.PointerMachine.root tree
  /-- The operation allocates at most one node. -/
  space : s.heap.length ≤ t.heap.length ∧ t.heap.length ≤ s.heap.length + 1
  /-- Only scalar search/height scratch registers may change. -/
  data : ∀ i, i ≠ 1 → i ≠ 2 → t.data i = s.data i

/-- A concrete dictionary write inserts a missing address and changes its payload, with
logarithmic cost and at most one allocation. Existing memory cells retain their values. -/
theorem write_correct [LinearOrder M.Value] (zero maxSucc : M.Op) (lt heavy le : M.Test)
    (encode : ℕ → M.Value) (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (max_spec : ∀ a b, M.evalOp maxSucc (encode a) (encode b) = encode (max a b + 1))
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))
    (heavy_spec : ∀ a b, M.evalTest heavy (encode a) (encode b) = decide (b + 1 < a))
    (le_spec : ∀ a b, M.evalTest le (encode a) (encode b) = decide (a ≤ b))
    (s : State M (layout 2 (regs + 2))) (tree : BinaryTree (Label M 2))
    (avl : AVLTree M.Value) (memory : M.Value → M.Value)
    (rep : Represents s.heap none tree) (matched : Matches encode 1 tree avl)
    (valid : avl.Valid) (distinct : AddressesDistinct tree) (stored : Stores (encode 0) tree memory)
    (rootReg : s.ptr 1 = root tree) (pc : s.pc = 0) :
    ∃ t result time, Executes (write zero maxSucc lt heavy le) s t time ∧
      time ≤ 147 * avl.cachedHeight + 52 ∧ WriteResult encode s t result avl memory := by
  have h01 : (0 : Fin (regs + 4)) ≠ 1 := by simp
  have h02 : (0 : Fin (regs + 4)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < regs + 4)]
  have h31 : (3 : Fin (regs + 4)) ≠ 1 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 3 < regs + 4)]
  have h32 : (3 : Fin (regs + 4)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 3 < regs + 4),
      Nat.mod_eq_of_lt (by omega : 2 < regs + 4)]
  let start : State M (layout 2 (regs + 2)) := { s.setPtr 0 (s.ptr 1) with pc := 0 }
  obtain ⟨a, newTree, ta, ea, ba, _, ra⟩ := PointerMachine.insert_correct
    zero maxSucc lt heavy le encode zero_spec max_spec compare heavy_spec le_spec 1 (by decide)
    (fun _ => 3) (fun _ _ _ => ⟨h31, h32⟩) start tree avl rep distinct matched valid
    (by simp [start, State.setPtr, rootReg]) (by simp [start, State.setPtr, rootReg]) rfl
  have query : a.data 0 = s.data 0 := ra.data 0 h01 h02
  let seekStart : State M (layout 2 (regs + 2)) := { a.setPtr 0 (a.ptr 1) with pc := 0 }
  obtain ⟨b, tb, eb, bb, rb⟩ := search_correct lt compare seekStart newTree none ra.rep
    (by simp [seekStart, State.setPtr, ra.root]) rfl
  have present : SearchTree.contains (a.data 0) (keys newTree) = true := by
    rw [ra.matched.keys, query]
    exact (SearchTree.contains_eq_true (valid_insert valid (s.data 0)).ordered _).mpr
      (by change s.data 0 ∈ (AVLTree.insert (s.data 0) avl).elements; simp [elements_insert])
  obtain ⟨address, cursor⟩ :=
    Option.isSome_iff_exists.mp (by simpa [seekStart] using rb.found.trans present)
  obtain ⟨path, label, _, get, labelAddress, _, fields, key⟩ := rb.key address cursor
  have bRep : Represents b.heap none newTree := by
    simpa only [rb.heap, seekStart, State.setPtr, Nat.add_assoc] using ra.rep
  obtain ⟨c, ec, rc, ptrC, dataC, sizeC, _⟩ := storeData_correct { b with pc := 0 }
    newTree none bRep 0 address cursor 2 3 rfl
  let result := updateData newTree address 2 (s.data 3)
  have newStored : Stores (encode 0) result (Function.update memory (s.data 0) (s.data 3)) := by
    dsimp only [result]
    rw [← labelAddress]
    exact stores_insert_updatePayload (s := start) rep matched valid stored ra path label get
      ((congrFun fields 0).symm.trans (key.trans query)) (s.data 3)
  have run := (reset_correct s pc).sequence (ea.sequence
    ((reset_correct { a with pc := 0 } rfl).sequence (eb.sequence ec)))
  let t := { c with pc := 2 + (sequence
    (PointerMachine.insert zero maxSucc lt heavy le 1 (fun _ => (3 : Fin (regs + 4))))
    (sequence ([.movePtr 0 1, .halt] : List (Instr M (layout 2 (regs + 2))))
      (sequence (search lt) [.storeData 2 0 3, .halt]))).length }
  have visits : SearchTree.searchVisits (a.data 0) (keys newTree) ≤ avl.cachedHeight + 1 :=
    ra.matched.keys ▸
      (searchVisits_le_cachedHeight (valid_insert valid (s.data 0)).heightConsistent _).trans
        (cachedHeight_insert_le valid _).2
  refine ⟨t, result, 2 + (ta + (2 + (tb + 2 + 1) + 1) + 1) + 1, run, ?_,
    ⟨by simpa only [t, result, start, State.setPtr,
          (rb.data 3 h31).trans (ra.data 3 h31 h32)] using rc,
      matches_updatePayload ra.matched _ _, ra.distinct.updateData _ _ _, newStored,
      ?_, ?_, ?_⟩⟩
  · change ta ≤ 141 * avl.cachedHeight + 2 + 31 at ba
    change tb ≤ 6 * SearchTree.searchVisits (a.data 0) (keys newTree) + 3 at bb
    omega
  · change c.ptr 1 = root result
    rw [ptrC, rb.ptr 1 (by simp [layout]) (by simp [layout])]
    simpa [result, seekStart, State.setPtr, root_updateData] using ra.root
  · simpa only [t, seekStart, sizeC.trans (congrArg List.length rb.heap),
      start, State.setPtr] using ra.space
  · intro i h1 h2
    change c.data i = s.data i
    rw [dataC]
    exact (rb.data i h1).trans (ra.data i h1 h2)

end Cslib.DataStructure.AVLTree.PointerMachine.Dictionary

/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Dictionary
public import CslibFrontier.DataStructure.AVLTree.PointerMachine.Structured.Insert
public import CslibFrontier.DataStructure.SearchTree.PointerMachine.Structured.Search

/-!
# AVL dictionary reads and writes as structured pointer-machine programs

`Structured.read` and `Structured.write` are the programs of `Dictionary` written as structured
programs, with the same contracts: a read returns the represented value in
`7 * height + 6` instructions, and a write inserts a missing address and replaces its payload
in `112 * height + 35`, against `6 * height + 10` and `147 * height + 52` for the flat programs.

## Main definitions

* `read`, `write`: the programs.

## Main results

* `read_correct`, `write_correct`: they implement a total memory.
-/

public section

namespace Cslib.DataStructure.AVLTree.PointerMachine.Dictionary.Structured

open Cslib.PointerMachine SearchTree.PointerMachine
open Cslib.Program (ExecWithin.seq)

variable {M : Model} {regs : ℕ}

/-- Data register three: the value to write, or the result of a read. -/
@[simp, pm_simps] abbrev value : Fin (regs + 4) := 3

/-- Data field two: the value stored with a key. -/
@[simp, pm_simps] abbrev payload : Fin 3 := 2

open SearchTree.PointerMachine.Structured renaming search → find in
open Register in
/-- Read a dictionary address, returning the default value on a missing key. -/
@[expose] def read (zero : M.Op) (lt : M.Test) : Code M (layout 2 (regs + 2)) := pm[
  cur ← top;
  ⟪find lt⟫;
  value := zero query query;
  value := cur[payload] ]

open SearchTree.PointerMachine.Structured renaming search → find in
open Register in
/-- Insert an absent key and replace the selected node's payload. Existing keys keep their node
address; scalar three supplies the fresh or replacement value. -/
@[expose] def write (zero maxSucc : M.Op) (lt heavy le : M.Test) :
    Code M (layout 2 (regs + 2)) := pm[
  cur ← top;
  ⟪PointerMachine.Structured.insert zero maxSucc lt heavy le 1 (fun _ => 3)⟫;
  cur ← top;
  ⟪find lt⟫;
  cur[payload] := value ]

/-- A store updates exactly the selected field in the represented tree, and preserves all
registers and links. -/
private theorem storeData_effect {extra regs : ℕ} (x : State M (layout extra regs))
    (t : BinaryTree (Label M extra)) (parent : Pointer)
    (rep : Represents x.heap parent t) (base : Fin 7) (a : ℕ)
    (cursor : x.ptr base = some a) (field : Fin (extra + 1)) (src : Fin (regs + 2)) :
    Represents ((Op.storeData field base src).effect x).heap parent
        (updateData t a field (x.data src)) ∧
      ((Op.storeData field base src).effect x).ptr = x.ptr ∧
      ((Op.storeData field base src).effect x).data = x.data ∧
      ((Op.storeData field base src).effect x).heap.length = x.heap.length := by
  have heap : ((Op.storeData field base src).effect x).heap = x.heap.modify a fun n =>
      { n with data := Function.update n.data field (x.data src) } := by
    simp [Op.effect, Op.instr, Instr.effect, State.modify, cursor]
  refine ⟨heap ▸ rep.updateData a field (x.data src), ?_, ?_, by rw [heap, List.length_modify]⟩
  all_goals simp [Op.effect, Op.instr, Instr.effect]

/-- A complete dictionary read follows the AVL search path and returns the represented value.
It preserves the heap, root, query, and every client scalar register. -/
theorem read_correct [LinearOrder M.Value] (zero : M.Op) (lt : M.Test)
    (encode : ℕ → M.Value) (zero_spec : ∀ a b, M.evalOp zero a b = encode 0)
    (compare : ∀ a b, M.evalTest lt a b = decide (a < b))
    (s : State M (layout 2 (regs + 2))) (tree : BinaryTree (Label M 2))
    (avl : AVLTree M.Value) (memory : M.Value → M.Value)
    (rep : Represents s.heap none tree) (matched : Matches encode 1 tree avl)
    (valid : avl.Valid) (stored : Stores (encode 0) tree memory)
    (rootReg : s.ptr 1 = root tree) :
    ∃ t, ExecWithin (read zero lt) s t (7 * avl.cachedHeight + 6) ∧ t.heap = s.heap ∧
      t.ptr 1 = s.ptr 1 ∧
      t.data 3 = memory (s.data 0) ∧
      (∀ i, i ≠ 1 → i ≠ 3 → t.data i = s.data i) := by
  have visits : SearchTree.searchVisits (s.data 0) (keys tree) ≤ avl.cachedHeight := by
    rw [matched.keys]
    exact AVLTree.searchVisits_le_cachedHeight valid.heightConsistent _
  have main : ∃ t, ExecWithin (read zero lt) s t (7 * avl.cachedHeight + 6) ∧
      t.data 3 = memory (s.data 0) := by
    apply WP.exists_execWithin
    pm_exec [read]
    refine Program.WP.call (SearchTree.PointerMachine.Structured.search_correct lt compare _ tree
      none (by exact rep) ?_) ?_
    · simpa using rootReg
    rintro a result n time
    pm_exec [zero_spec]
    refine ⟨by simp at time; omega, ?_⟩
    cases hp : a.ptr 0 with
    | none =>
      have missing : SearchTree.contains (s.data 0) (keys tree) = false := by
        simpa [hp] using result.found.symm
      have ordered : SearchTree.Ordered (keys tree) := matched.keys.symm ▸ valid.ordered
      simp [State.deref, hp, stored.absent ordered missing]
    | some address =>
      obtain ⟨path, label, node, get, -, lookup, fields, key⟩ := result.key address hp
      have labelKey : label.data 0 = s.data 0 := fields ▸ key
      simp [State.deref, hp, lookup, fields, stored.value path label get, labelKey]
  obtain ⟨t, run, value⟩ := main
  exact ⟨t, run, run.heap_eq (by pm_frame), run.ptr_keep [0, 5] (by pm_frame) (by simp), value,
    fun i h1 h3 => run.data_keep [1, 3] (by pm_frame) (by simp [h1, h3])⟩

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
    (rootReg : s.ptr 1 = root tree) :
    ∃ t result, ExecWithin (write zero maxSucc lt heavy le) s t (112 * avl.cachedHeight + 35) ∧
      WriteResult encode s t result avl memory := by
  have h01 : (0 : Fin (regs + 4)) ≠ 1 := by simp
  have h02 : (0 : Fin (regs + 4)) ≠ 2 := by simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have h31 : (3 : Fin (regs + 4)) ≠ 1 := by simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have h32 : (3 : Fin (regs + 4)) ≠ 2 := by simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  let start : State M (layout 2 (regs + 2)) := s.setPtr 0 (s.ptr 1)
  obtain ⟨a, newTree, ea, _, ra⟩ := PointerMachine.Structured.insert_correct
    zero maxSucc lt heavy le encode zero_spec max_spec compare heavy_spec le_spec 1 (by decide)
    (fun _ => 3) (by intro f _ _; exact ⟨h31, h32⟩) start tree avl rep distinct matched valid
    (by simp [start, State.setPtr, rootReg]) (by simp [start, State.setPtr, rootReg])
  have query : a.data 0 = s.data 0 := ra.data 0 h01 h02
  have payload : a.data 3 = s.data 3 := ra.data 3 h31 h32
  let seekStart : State M (layout 2 (regs + 2)) := a.setPtr 0 (a.ptr 1)
  obtain ⟨b, eb, rb⟩ :=
    SearchTree.PointerMachine.Structured.search_correct lt compare seekStart newTree none ra.rep
    (by simp [seekStart, State.setPtr, ra.root])
  have present : SearchTree.contains (a.data 0) (keys newTree) = true := by
    rw [ra.matched.keys, query]
    exact (SearchTree.contains_eq_true (valid_insert valid (s.data 0)).ordered _).mpr
      (by change s.data 0 ∈ (AVLTree.insert (s.data 0) avl).elements; simp [elements_insert])
  obtain ⟨address, cursor⟩ :=
    Option.isSome_iff_exists.mp (by simpa [seekStart] using rb.found.trans present)
  obtain ⟨path, label, node, get, labelAddress, lookup, fields, key⟩ := rb.key address cursor
  have labelKey : label.data 0 = s.data 0 := (congrFun fields 0).symm.trans (key.trans query)
  have bPayload : b.data 3 = s.data 3 := (rb.data 3 h31).trans payload
  have bRep : Represents b.heap none newTree := by
    simpa only [rb.heap, seekStart, State.setPtr, Nat.add_assoc] using ra.rep
  obtain ⟨rc, ptrC, dataC, sizeC⟩ := storeData_effect b newTree none bRep 0 address cursor 2 3
  let c := (Op.storeData 2 0 3).effect b
  let result := updateData newTree address 2 (s.data 3)
  have resultRep : Represents c.heap none result := by simpa only [result, bPayload] using rc
  have resultMatches : Matches encode 1 result (AVLTree.insert (s.data 0) avl) :=
    matches_updatePayload ra.matched _ _
  have newStored : Stores (encode 0) result (Function.update memory (s.data 0) (s.data 3)) := by
    simpa only [result, labelAddress, start, State.setPtr] using
      stores_insert_updatePayload (s := start) rep matched valid stored ra path label get
        labelKey (s.data 3)
  have run : ExecWithin (write zero maxSucc lt heavy le) s c
      (1 + (105 * avl.cachedHeight + 2 + 20 +
        (1 + (7 * SearchTree.searchVisits (a.data 0) (keys newTree) + 3 + 1)))) :=
    ExecWithin.seq (ExecWithin.op_eq rfl) (ExecWithin.seq ea
      (ExecWithin.seq (ExecWithin.op_eq rfl) (ExecWithin.seq eb ExecWithin.op)))
  have visits : SearchTree.searchVisits (a.data 0) (keys newTree) ≤ avl.cachedHeight + 1 := by
    rw [ra.matched.keys]
    exact (searchVisits_le_cachedHeight (valid_insert valid (s.data 0)).heightConsistent _).trans
      (cachedHeight_insert_le valid _).2
  refine ⟨c, result, run.mono (by omega),
    ⟨resultRep, resultMatches, ra.distinct.updateData _ _ _, newStored, ?_, ?_, ?_⟩⟩
  · rw [ptrC, rb.ptr 1 (by simp [layout]) (by simp [layout])]
    simpa [result, seekStart, State.setPtr, root_updateData] using ra.root
  · simpa only [c, sizeC.trans (congrArg List.length rb.heap), start, seekStart, State.setPtr] using
      ra.space
  · exact fun i h1 h2 => (congrFun dataC i).trans ((rb.data i h1).trans (ra.data i h1 h2))

end Cslib.DataStructure.AVLTree.PointerMachine.Dictionary.Structured

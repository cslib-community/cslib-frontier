/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
public import CslibFrontier.Computability.PointerMachine.Defs

/-!
# Executing a stored comparison tree on a pointer machine

A single fixed instruction list interprets binary comparison programs. Internal records point
to two key records and two children. Leaves point to outputs. With this representation, the
interpreter takes exactly eight instructions per weight comparison and four additional
instructions, including the halt. This measures traversal after loading the tree and its
operand pointers. Grouping input graphs and assigning those pointers are separate steps of
the small-graph procedure in [PettieRamachandran2002], §6.
-/

public section

namespace Cslib.PointerMachine.ComparisonTree

open Cslib.Query

variable {E O W : Type} [Inhabited W] [LinearOrder W]

/-- The only data test available to the interpreter is key comparison. -/
abbrev model (W : Type) [Inhabited W] [LinearOrder W] : Model where
  Value := W
  undefined := default
  Op := Empty
  Test := Unit
  evalOp := nofun
  evalTest _ a b := decide (a ≤ b)

/-- Register 0 holds the current node, 1 and 2 hold operands, and 3 holds null.
Pointer fields 0–3 encode the tree and field 4 links a reusable key slot to its input edge. -/
abbrev layout : Layout := ⟨4, 2, 5, 1⟩

/-- A tree node either has a null first pointer (leaf), or has one pointer to each
of two keys and two children. At a leaf, the second pointer gives the result. -/
@[expose] def code (W : Type) [Inhabited W] [LinearOrder W] : List (Instr (model W) layout) :=
  [.loadPtr 1 0 0, .ifPtrEq 1 3 10, .loadPtr 2 1 0, .loadData 0 0 1, .loadData 1 0 2,
   .ifTest () 0 1 8, .loadPtr 0 3 0, .goto 0, .loadPtr 0 2 0, .goto 0, .loadPtr 0 1 0, .halt]

/-- Storage of a tree in a heap. The address of each operand and output is fixed independently
of the keys. Children may share records. -/
inductive Stored (H : List (Record (model W) layout)) (addr : E → ℕ) (out : O → Pointer) :
    FreeM (LEQuery E) O → ℕ → Prop where
  | leaf {i r o} (read : H[i]? = some r) (tag : r.ptr 0 = none) (result : r.ptr 1 = out o) :
      Stored H addr out (.pure o) i
  | node {i r a b left right} {k : Bool → FreeM (LEQuery E) O}
      (read : H[i]? = some r) (fst : r.ptr 0 = some (addr a)) (snd : r.ptr 1 = some (addr b))
      (yes : r.ptr 2 = some left) (no : r.ptr 3 = some right)
      (leftTree : Stored H addr out (k true) left) (rightTree : Stored H addr out (k false) right) :
      Stored H addr out (.liftBind (.le a b) k) i

private def leafRecord (result : Pointer) : Record (model W) layout :=
  ⟨fun f => if f = 1 then result else none, fun _ => default⟩

private def branchRecord (a b left right : ℕ) : Record (model W) layout :=
  ⟨fun f => some (if f = 0 then a else if f = 1 then b else if f = 2 then left else right),
   fun _ => default⟩

/-- Serialize a comparison program in preorder at the given starting address. This compiler
uses only the topology and the addresses. It never reads the operand keys. -/
def encode (addr : E → ℕ) (out : O → Pointer) :
    FreeM (LEQuery E) O → ℕ → List (Record (model W) layout)
  | .pure o, _ => [leafRecord (out o)]
  | .liftBind (.le a b) k, base =>
    let left := encode addr out (k true) (base + 1)
    let next := base + 1 + left.length
    branchRecord (addr a) (addr b) (base + 1) next :: left ++ encode addr out (k false) next

/-- The serialized program can be appended to an existing heap. Additional trailing records
are allowed, so both branches remain valid after building the rest of the heap. -/
theorem stored_encode (addr : E → ℕ) (out : O → Pointer) (p : FreeM (LEQuery E) O)
    (before after : List (Record (model W) layout)) :
    Stored (before ++ encode addr out p before.length ++ after) addr out p before.length := by
  induction p using FreeM.rec generalizing before after with
  | pure o =>
    apply Stored.leaf (r := leafRecord (out o))
    · simp [encode, List.append_assoc]
    · rfl
    · rfl
  | liftBind op k ih =>
    cases op with
    | le a b =>
      let left := encode (W := W) addr out (k true) (before.length + 1)
      let next := before.length + 1 + left.length
      let node : Record (model W) layout := branchRecord (addr a) (addr b) (before.length+1) next
      change Stored (before ++ (node :: left ++ encode addr out (k false) next) ++ after) _ _ _ _
      refine Stored.node (r := node) ?_ rfl rfl rfl rfl ?_ ?_
      · simp [List.append_assoc]
      · simpa [left, node, next, List.append_assoc] using
          ih true (before ++ [node]) (encode addr out (k false) next ++ after)
      · simpa [left, node, next, List.append_assoc, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using ih false (before ++ [node] ++ left) after

/-- An operand address points to an initialized record containing its key. -/
@[expose] def HoldsKeys (H : List (Record (model W) layout)) (addr : E → ℕ) (w : E → W) : Prop :=
  ∀ a, ∃ r, H[addr a]? = some r ∧ r.data 0 = w a

private abbrev MachineState (W : Type) [Inhabited W] [LinearOrder W] := State (model W) layout

private def advance (x : MachineState W) : ℕ → Option (MachineState W)
  | 0 => some x
  | n + 1 => (advance x n).bind (step (code W))

private theorem runs_of_advance {x y : MachineState W} {n : ℕ} (h : advance x n = some y) :
    Runs (code W) x y n := by
  induction n generalizing y with
  | zero => cases h; exact .refl _
  | succ n ih =>
    obtain ⟨z, hx, hy⟩ := Option.bind_eq_some_iff.mp h
    exact .tail _ _ _ _ (ih hx) hy

private theorem run_leaf {x : MachineState W} {i r} (pc : x.pc = 0) (root : x.ptr 0 = some i)
    (null : x.ptr 3 = none) (read : x.heap[i]? = some r) (tag : r.ptr 0 = none) :
    ∃ y, Runs (code W) x y 3 ∧ y.pc = 11 ∧ y.ptr 0 = r.ptr 1 ∧ y.heap = x.heap := by
  let y : MachineState W := { (x.setPtr 1 none).setPtr 0 (r.ptr 1) with pc := 11 }
  refine ⟨y, runs_of_advance ?_, rfl, ?_, rfl⟩
  · simp [advance, step, code, pc, Instr.effect, Instr.next, State.deref, root, read, tag,
      State.setPtr, null, y, Function.update]
  · simp [y, State.setPtr]

private theorem run_node {x : MachineState W} {i r a b ra rb}
    (pc : x.pc = 0) (root : x.ptr 0 = some i) (null : x.ptr 3 = none) (read : x.heap[i]? = some r)
    (fst : r.ptr 0 = some a) (snd : r.ptr 1 = some b)
    (ka : x.heap[a]? = some ra) (kb : x.heap[b]? = some rb) :
    ∃ y, Runs (code W) x y 8 ∧ y.pc = 0 ∧
      y.ptr 0 = (if ra.data 0 ≤ rb.data 0 then r.ptr 2 else r.ptr 3) ∧
      y.ptr 3 = none ∧ y.heap = x.heap := by
  let bit := decide (ra.data 0 ≤ rb.data 0)
  let child := if bit then r.ptr 2 else r.ptr 3
  let t := (((x.setPtr 1 (some a)).setPtr 2 (some b)).setData 0 (ra.data 0)).setData 1 (rb.data 0)
  let y : MachineState W := { t.setPtr 0 child with pc := 0 }
  refine ⟨y, runs_of_advance ?_, rfl, ?_, ?_, rfl⟩
  · by_cases h : ra.data 0 ≤ rb.data 0 <;>
      simp [advance, step, code, pc, Instr.effect, Instr.next, State.deref, root, read, fst, snd,
        State.setPtr, State.setData, null, ka, kb, Function.update, model, h, y, t, child, bit]
  · simp [y, t, child, bit, State.setPtr]
  · simp [y, t, State.setPtr, State.setData, Function.update, null]

/-- A stored tree returns the pointer to its answer in exactly eight instructions per query
plus four for fetching and returning the leaf, including the final halt. -/
theorem Stored.executes {H : List (Record (model W) layout)} {addr : E → ℕ} {out : O → Pointer}
    {p : FreeM (LEQuery E) O} {i : ℕ} (tree : Stored H addr out p i) {w : E → W}
    (keys : HoldsKeys H addr w) (x : State (model W) layout) (heap : x.heap = H)
    (pc : x.pc = 0) (root : x.ptr 0 = some i) (null : x.ptr 3 = none) :
    ∃ y, Executes (code W) x y (8 * p.countQueries (LEQuery.keyOracle w) + 4) ∧
      y.ptr 0 = out (p.eval (LEQuery.keyOracle w)) ∧ y.heap = H := by
  induction tree generalizing x with
  | leaf read tag result =>
    obtain ⟨y, run, halt, ans, stable⟩ := run_leaf pc root null (heap ▸ read) tag
    exact ⟨y, ⟨3, run, by rw [halt]; rfl, by simp⟩, ans.trans result, stable.trans heap⟩
  | @node i r a b left right k read fst snd yes no _ _ ihY ihN =>
    obtain ⟨ra, ka, wa⟩ := keys a
    obtain ⟨rb, kb, wb⟩ := keys b
    obtain ⟨z, run, start, next, zero, stable⟩ :=
      run_node pc root null (heap ▸ read) fst snd (heap ▸ ka) (heap ▸ kb)
    rw [wa, wb] at next
    have endHeap := stable.trans heap
    by_cases h : w a ≤ w b
    · obtain ⟨y, ⟨n, tail, stop, time⟩, ans, endH⟩ :=
        ihY z endHeap start (by simpa [h, yes] using next) zero
      refine ⟨y, ⟨8 + n, run.trans tail, stop, ?_⟩, ?_, endH⟩
      · simp [h, Nat.mul_add]
        omega
      · simpa [h] using ans
    · obtain ⟨y, ⟨n, tail, stop, time⟩, ans, endH⟩ :=
        ihN z endHeap start (by simpa [h, no] using next) zero
      refine ⟨y, ⟨8 + n, run.trans tail, stop, ?_⟩, ?_, endH⟩
      · simp [h, Nat.mul_add]
        omega
      · simpa [h] using ans

end Cslib.PointerMachine.ComparisonTree

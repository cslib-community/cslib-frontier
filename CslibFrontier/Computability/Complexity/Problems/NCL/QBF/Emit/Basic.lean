/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.Initial
public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.OutputLatch
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Expansion
public import Mathlib.Data.FinEnum

/-!
# Emitting source circuits as fixed instructions

An instruction places one fixed circuit fragment at a wire offset. Indexed list scans emit the
quantifier chain, clause rows and terminal. Expanding instructions gives the existing primitive
word, including its edge creation order.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.Opcode`: the finite table of circuit fragments.
* `Cslib.Complexity.NCL.QBF.Emit.Program`: fragment names paired with wire offsets.
* `Cslib.Complexity.NCL.QBF.Emit.expand`: expand instructions to primitive layers.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

open Diagram

/-- The fixed circuit fragments used by the source emitter. -/
inductive Opcode
  /-- The output latch and its initial controls. -/
  | output
  /-- An existential quantifier. -/
  | ex
  /-- A universal quantifier. -/
  | all
  /-- The first selected literal of a clause. -/
  | tapFirst
  /-- A later selected literal of a clause. -/
  | tap
  /-- Join two clause values. -/
  | conj
  /-- Return satisfaction through the control gate. -/
  | returnGate
  /-- Terminate two red wires. -/
  | cap
  /-- Start a free blue wire. -/
  | start
  /-- Start a blue wire constrained to be inactive. -/
  | fixed
  /-- Cross a blue wire followed by a red wire during a clause scan. -/
  | swapBlueRed
  /-- Cross a red wire followed by a blue wire during the return sweep. -/
  | swapRedBlue
  deriving @[expose] DecidableEq, Repr

instance : FinEnum Opcode :=
  FinEnum.ofList [.output, .ex, .all, .tapFirst, .tap, .conj, .returnGate, .cap, .start,
    .fixed, .swapBlueRed, .swapRedBlue] (by intro op; cases op <;> simp)

/-- A sequence of fixed fragments, each paired with its wire offset. -/
abbrev Program := List (ℕ × Opcode)

/-- A fixed gate diagram together with its source and target orientations. -/
structure Fragment where
  /-- Top wire colors. -/
  inputs : List Color
  /-- Bottom wire colors. -/
  outputs : List Color
  /-- The circuit implementing the instruction. -/
  diagram : Diagram Gate inputs outputs
  /-- Canonical edge directions indexed by the output record bit. -/
  orient : Bool → diagram.Edge → Bool

/-- A fragment whose initial and target directions are all false. -/
@[expose] def Fragment.inactive {a b : List Color} (D : Diagram Gate a b) : Fragment :=
  ⟨a, b, D, fun _ _ => false⟩

/-- The diagram and canonical configurations of each source instruction. -/
@[expose] def Opcode.data : Opcode → Fragment
  | .output => ⟨_, _, OutputLatch.diagram, fun r => (OutputLatch.canonical r true false).orient⟩
  | .ex => ⟨_, _, existsGadget, fun _ => Initial.existsInitial.orient⟩
  | .all => ⟨_, _, forallGadget, fun _ => Initial.forallInitial.orient⟩
  | .returnGate => ⟨_, _, Matrix.returnGate, fun _ => Initial.returnInitial.orient⟩
  | .tapFirst => .inactive Network.tapFirst
  | .tap => .inactive Network.tap
  | .conj => .inactive Network.conj
  | .cap => .inactive (gen Gate.cap)
  | .start => .inactive (gen Gate.start)
  | .fixed => .inactive (Gate.node [] [.blue])
  | .swapBlueRed => .inactive (Diagram.swap .blue .red)
  | .swapRedBlue => .inactive (Diagram.swap .red .blue)

/-- The boundary-indexed diagram for the fixed instruction language. -/
@[expose] def Opcode.gateFragment (op : Opcode) : Σ a b : List Color, Diagram Gate a b :=
  ⟨op.data.inputs, op.data.outputs, op.data.diagram⟩

/-- The fixed primitive diagram implementing each instruction tag. -/
@[expose] def Opcode.fragment (op : Opcode) : Σ a b : List Color, Diagram Prim a b :=
  let ⟨a, b, diagram⟩ := op.gateFragment
  ⟨a, b, diagram.subst Gate.expand⟩

/-- Expand one instruction to its primitive layers at the given offset. -/
@[expose] def Opcode.word (op : Opcode) (k : ℕ) : Word :=
  let ⟨_, _, diagram⟩ := op.fragment
  diagram.toWord Prim.interp k

/-- Expand every instruction, preserving order and local edge creation order. -/
@[expose] def expand (p : Program) : Word := p.flatMap fun i => i.2.word i.1

/-- Emit a literal position after recording whether an earlier literal started the accumulator. -/
@[expose] def collect (k : ℕ) (seen bit : Bool) : Program :=
  if seen then [(k, if bit then .tap else .swapBlueRed)] else if bit then [(k, .tapFirst)] else []

/-- Sweep the literal bundle, ending an unstarted accumulator with a fixed inactive source. -/
@[expose] def scan (k n : ℕ) (m : List Bool) (seen : Bool) : Program :=
  (List.range n).flatMap (fun i => collect (k + i) (seen || (m.take i).any id) (m.getD i false)) ++
    if seen || (m.take n).any id then [] else [(k + n, .fixed)]

private theorem seen_succ (m : List Bool) (i : ℕ) :
    (m.take (i + 1)).any id = (m.headD false || (m.tail.take i).any id) := by
  cases m <;> simp

private theorem getD_succ (m : List Bool) (i : ℕ) :
    m.getD (i + 1) false = m.tail.getD i false := by
  cases m <;> simp [List.getD_eq_getElem?_getD]

/-- The indexed scan emits the current position before sweeping the remaining mask. -/
theorem scan_succ (k n : ℕ) (m : List Bool) (seen : Bool) :
    scan k (n + 1) m seen = collect k seen (m.headD false) ++
      scan (k + 1) n m.tail (seen || m.headD false) := by
  unfold scan
  rw [List.range_succ_eq_map]
  simp only [List.flatMap_cons, List.flatMap_map]
  simp only [
    List.take_zero, List.any_nil, Bool.or_false, Nat.add_zero, ← List.headD_eq_getD,
    seen_succ, getD_succ,
    Bool.or_assoc, Nat.add_assoc, Nat.add_comm 1, List.append_assoc]

/-- Emit every remaining clause and join its value to the preceding accumulator. -/
@[expose] def conjoin (k n : ℕ) (ms : List (List Bool)) : Program :=
  ms.flatMap fun m => scan k n m false ++ [(k + n, .conj)]

/-- Emit a CNF network, starting its accumulator at the first clause. -/
@[expose] def network (k n : ℕ) (ms : List (List Bool)) : Program :=
  match ms with
  | [] => [(k + n, .start)]
  | m :: ms => scan k n m false ++ conjoin k n ms

/-- Emit quantifier fragments in binding order at the control-wire offset. -/
@[expose] def chain (k : ℕ) (qs : List Quantifier) : Program :=
  qs.map fun q => (k, match q with | .ex => .ex | .all => .all)

/-- Emit the terminal network, move its value to the controls, and terminate the literals. -/
@[expose] def terminal (k p : ℕ) (ms : List (List Bool)) : Program :=
  network (k + 2) (2 * p) ms ++
    ((List.range (2 * p)).reverse.map fun i => (k + 2 + i, .swapRedBlue)) ++
    [(k, .returnGate)] ++ List.replicate p (k, .cap)

/-- Emit a complete circuit from its prefix and mask matrix. -/
@[expose] def circuit (qs : List Quantifier) (ms : List (List Bool)) : Program :=
  [(0, .output)] ++ chain 0 qs ++ terminal 0 qs.length ms

end Cslib.Complexity.NCL.QBF.Emit

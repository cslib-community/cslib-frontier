/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.WordRAM.Memory
public import CslibFrontier.Computability.WordRAM.Blocks
public import CslibFrontier.Computability.WordRAM.Allocation

/-!
# Compiling pointer-machine instructions to word RAM

Nodes occupy fixed blocks of memory, with zero reserved for null. The compiler implements
pointer access and allocation using ordinary word-RAM instructions. Scalar operations and tests
come with their own word-RAM implementations and costs; no heap operation is assumed implemented.
Field accesses reuse `Cslib.WordRAM.readAt` and `Cslib.WordRAM.writeAt`. Allocation uses a
layout-specific initializer: `Cslib.WordRAM.alloc` zeroes every field, whereas scalar fields
require `encode M.undefined`, which need not be zero. It also takes six distinct register
parameters, whereas this initializer uses the base and two scratch registers, leaving the
next-free and zero registers unchanged until the final frontier update.
The fixed field list is unrolled, giving the stated layout-dependent constant cost.

Source instructions compile into equally sized code blocks, with jumps directly relocated to
the corresponding block. Padding is never executed by a simulated successful run.
-/

public section

namespace Cslib.PointerMachine.WordRAM

open Cslib.WordRAM (Code ExecWithin)

variable {M : Model} {L : Layout}

/-- A scalar routine returns one value and preserves memory and all other source/administrative
registers. Temporary registers may change. -/
structure ScalarResult (dst : Fin (regCount L)) (v : ℕ)
    (x y : Cslib.WordRAM.Data (regCount L)) : Prop where
  /-- Returned word. -/
  result : y.regs dst = v
  /-- Scalar computation does not change the heap. -/
  memory : y.mem = x.mem
  /-- Source registers, allocation pointer and null register are preserved except for `dst`. -/
  frame : ∀ r : Fin (regCount L), r.val < L.ptrRegs + L.dataRegs + 2 → r ≠ dst →
    y.regs r = x.regs r

/-- Writing the destination register alone meets the scalar routine's frame contract. -/
theorem ScalarResult.set (x : Cslib.WordRAM.Data (regCount L))
    (d : Fin (regCount L)) (v : ℕ) : ScalarResult d v x (x.set d v) where
  result := by simp [Cslib.WordRAM.Data.set]
  memory := rfl
  frame r _ hrd := by simp [Cslib.WordRAM.Data.set, Function.update_of_ne hrd]

/-- Implementations of the scalar basis in the standard word RAM. The admissibility predicates
state any additional headroom needed by scalar routines. They concern scalar operands only;
all pointer operations are implemented by the compiler below. -/
structure Scalars (M : Model) (L : Layout) where
  /-- Faithful single-word representation of scalar values. -/
  encode : M.Value ↪ ℕ
  /-- Code for a binary operation, with destination and two operand registers. -/
  op : M.Op → Fin (regCount L) → Fin (regCount L) → Fin (regCount L) →
    Code .standard (regCount L)
  /-- Code for a predicate, returning zero or one. -/
  test : M.Test → Fin (regCount L) → Fin (regCount L) → Fin (regCount L) →
    Code .standard (regCount L)
  /-- Uniform instruction bound for each scalar operation. -/
  opTime : M.Op → ℕ
  /-- Uniform instruction bound for each scalar predicate. -/
  testTime : M.Test → ℕ
  /-- Scalar-operation headroom at a given width. -/
  OpSafe : ℕ → M.Op → M.Value → M.Value → Prop
  /-- Scalar-predicate headroom at a given width. -/
  TestSafe : ℕ → M.Test → M.Value → M.Value → Prop
  /-- Correctness and frame of operation code, including its cost. -/
  op_spec : ∀ w o d a b (x : Cslib.WordRAM.Data (regCount L)) u v,
    x.regs a = encode u → x.regs b = encode v → OpSafe w o u v →
    Cslib.WordRAM.Fits w (encode (M.evalOp o u v)) →
    ∃ y, ExecWithin w (op o d a b) x y (opTime o) ∧
      ScalarResult d (encode (M.evalOp o u v)) x y
  /-- Correctness and frame of predicate code, including its cost. -/
  test_spec : ∀ w p d a b (x : Cslib.WordRAM.Data (regCount L)) u v,
    x.regs a = encode u → x.regs b = encode v → TestSafe w p u v → 1 < 2 ^ w →
    ∃ y, ExecWithin w (test p d a b) x y (testTime p) ∧
      ScalarResult d (if M.evalTest p u v then 1 else 0) x y

namespace Scalars

variable (S : Scalars M L)

/-- Scalar admissibility of the instruction about to execute. -/
@[expose] def Safe (w : ℕ) (x : State M L) : Instr M L → Prop
  | .op o _ a b => S.OpSafe w o (x.data a) (x.data b)
  | .ifTest p a b _ => S.TestSafe w p (x.data a) (x.data b)
  | _ => True

/-- Fill the listed offsets of a fresh record with their initial values. The list is fixed
by the source layout, not supplied by the running program. -/
@[expose] def initializeFields (base : Fin (regCount L)) :
    List (ℕ × ℕ) → Code .standard (regCount L)
  | [] => .op (.copy (zeroReg L) (zeroReg L))
  | (offset, value) :: rest =>
    .seq (.op (.const (addrReg L) offset)) <|
    .seq (.op (.bin .add (addrReg L) base (addrReg L))) <|
    .seq (.op (.const (valueReg L) value)) <|
    .seq (.op (.store (addrReg L) (valueReg L))) (initializeFields base rest)

/-- Pointer fields are initialized to null; scalar fields to the model's undefined value. -/
@[expose] def initialFields : List (ℕ × ℕ) :=
  (List.range L.ptrFields).map (fun f => (f, 0)) ++
    (List.range L.dataFields).map (fun f => (L.ptrFields + f, S.encode M.undefined))

/-- A null access does nothing; a nonnull access loads the fixed offset before `body`. -/
@[expose] def access (base : Fin (regCount L)) (offset : ℕ)
    (body : Code .standard (regCount L)) : Code .standard (regCount L) :=
  .branch (.eq base (zeroReg L)) (.op (.copy (zeroReg L) (zeroReg L)))
    (.seq (.op (.const (addrReg L) offset)) body)

/-- The register/memory part of one source instruction. A test also computes its Boolean
answer in a temporary register for the terminal branch. -/
@[expose] def effect : Instr M L → Code .standard (regCount L)
  | .null r => .op (.copy (ptrReg L r) (zeroReg L))
  | .movePtr r s => .op (.copy (ptrReg L r) (ptrReg L s))
  | .moveData r s => .op (.copy (dataReg L r) (dataReg L s))
  | .loadPtr r f b =>
    access (ptrReg L b) f.val
      (Cslib.WordRAM.readAt (addrReg L) (ptrReg L r) (ptrReg L b) (addrReg L))
  | .loadData r f b =>
    access (ptrReg L b) (L.ptrFields + f.val)
      (Cslib.WordRAM.readAt (addrReg L) (dataReg L r) (ptrReg L b) (addrReg L))
  | .storePtr f b r =>
    access (ptrReg L b) f.val
      (Cslib.WordRAM.writeAt (addrReg L) (ptrReg L b) (addrReg L) (ptrReg L r))
  | .storeData f b r =>
    access (ptrReg L b) (L.ptrFields + f.val)
      (Cslib.WordRAM.writeAt (addrReg L) (ptrReg L b) (addrReg L) (dataReg L r))
  | .op o d a b => S.op o (dataReg L d) (dataReg L a) (dataReg L b)
  | .create r =>
    .seq (.op (.copy (ptrReg L r) (freeReg L))) <|
    .seq (initializeFields (ptrReg L r) S.initialFields) <|
    .seq (.op (.const (addrReg L) (stride L)))
      (.op (.bin .add (freeReg L) (freeReg L) (addrReg L)))
  | .ifTest p a b _ => S.test p (valueReg L) (dataReg L a) (dataReg L b)
  | _ => .op (.copy (zeroReg L) (zeroReg L))

/-- Cost bound for the compiled register/memory part, independent of input size. -/
@[expose] def effectTime : Instr M L → ℕ
  | .loadPtr .. | .loadData .. | .storePtr .. | .storeData .. => 5
  | .create _ => 4 * (L.ptrFields + L.dataFields) + 4
  | .op o .. => S.opTime o
  | .ifTest p .. => S.testTime p
  | _ => 1

/-- Live code of one instruction, including the relocated terminal control instructions. -/
@[expose] def rawBlock (k pc : ℕ) (i : Instr M L) : Cslib.WordRAM.Program .standard (regCount L) :=
  match i with
  | .halt => [.halt (zeroReg L)]
  | _ => (S.effect i).assemble (k * pc) ++ match i with
    | .goto t => [.jump (k * t)]
    | .ifPtrEq a b t => [.branch (.eq (ptrReg L a) (ptrReg L b)) (k * t),
        .jump (k * (pc + 1))]
    | .ifTest _ _ _ t => [.branch (.lt (zeroReg L) (valueReg L)) (k * t),
        .jump (k * (pc + 1))]
    | _ => [.jump (k * (pc + 1))]

/-- A program-dependent fixed block size. -/
@[expose] def blockSize (code : List (Instr M L)) : ℕ :=
  code.foldr (fun i n => max ((S.effect i).size + 2) n) 1

/-- Pad a live instruction block to the common block size. -/
@[expose] def block (k pc : ℕ) (i : Instr M L) : Cslib.WordRAM.Program .standard (regCount L) :=
  S.rawBlock k pc i ++ List.replicate (k - (S.rawBlock k pc i).length) (.jump (k * (pc + 1)))

/-- Compile the whole source program to a finite standard word-RAM program. -/
@[expose] def compile (code : List (Instr M L)) : Cslib.WordRAM.Program .standard (regCount L) :=
  Cslib.Program.compileBlocks (S.block (S.blockSize code)) 0 code

/-- Uniform overhead per continuing source instruction, including terminal branches/jumps. -/
@[expose] def overhead (code : List (Instr M L)) : ℕ :=
  code.foldr (fun i n => max (S.effectTime i + 2) n) 1

end Scalars

end Cslib.PointerMachine.WordRAM

/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Gate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary

/-!
# Encodings of gates

A gate operation is encoded by the unary rank of its constructor in the declaration order of
`Cslib.Complexity.CookLevin.Quasilinear.Gate.Op` (`and` is `0`, …, `imp` is `7`), and a gate as the
framed tuple of its operation and its four variables, the variables in binary
(`enc_structure`). A machine can therefore read the operation of a gate as a number.

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.Gate.Op.index`: the rank of an operation.
* `Cslib.Complexity.CookLevin.Quasilinear.encGateOp`: the encoding of operations.
* `Cslib.Complexity.CookLevin.Quasilinear.encGate`: the encoding of gates.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing.MultiTapeTM

/-- The rank of an operation in the declaration order. -/
def Gate.Op.index : Gate.Op → ℕ
  | .and => 0
  | .or => 1
  | .xor => 2
  | .xnor => 3
  | .not => 4
  | .mux => 5
  | .assert => 6
  | .imp => 7

/-- Operations of the same rank are equal. -/
theorem Gate.Op.index_injective : Function.Injective Gate.Op.index := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

/-- The encoding of an operation: the unary rank of its constructor. -/
def encGateOp : Gate.Op ↪ List Bool :=
  ⟨fun o => encUnary o.index, fun _ _ h => Gate.Op.index_injective (encUnary.injective h)⟩

/-- The encoding of a gate: its operation by `encGateOp`, its four variables in binary. -/
enc_structure encGate : Gate where
  op : encGateOp, out : encNat, a : encNat, b : encNat, c : encNat

end Cslib.Complexity.CookLevin.Quasilinear

/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.GateEncoding

/-!
# Tests for the encoding of gates

Concrete checks for
`CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.GateEncoding`: the ranks of the
operations follow the declaration order, an operation is encoded by its rank in unary, and
distinct operations and distinct gates have distinct words.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.GateEncoding

open Cslib.Complexity.CookLevin.Quasilinear Turing.MultiTapeTM

/-- The ranks of the operations, in declaration order. -/
example : [Gate.Op.and, .or, .xor, .xnor, .not, .mux, .assert, .imp].map Gate.Op.index =
    [0, 1, 2, 3, 4, 5, 6, 7] := by decide

/-- An operation is encoded by the unary word of its rank. -/
example : encGateOp Gate.Op.mux = encUnary 5 := rfl

/-- Operations with equal codes are equal. -/
example : encGateOp Gate.Op.and ≠ encGateOp Gate.Op.or := fun h =>
  absurd (encGateOp.injective h) (by decide)

/-- Gates that differ in one variable have different words. -/
example : encGate (Gate.mk .and 1 2 3 4) ≠ encGate (Gate.mk .and 1 2 3 5) := fun h =>
  absurd (encGate.injective h) (by decide)

end CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.GateEncoding

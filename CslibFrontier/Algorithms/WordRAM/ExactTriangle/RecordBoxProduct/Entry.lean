/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Producer
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Entry

/-!
# Initialized producer-to-adapter composition

One fixed native program runs the complete producer from its original four headers and three
signed weight arrays, selects actual ordinal zero and invokes the actual record consumer.
The general caller interface handles any occupied ordinal; the initialized client here chooses
the first one with real code. Its existence follows from the original positive geometry.

The producer's pre-halt native witness and polynomial word bound derive every source pointer,
coordinate, caller base and dirty-word bound used by the record consumer. No producer layout,
run, solver or time certificate is an input hypothesis.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open RecordProduct
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- One fixed initialized composition of the record producer `RecordProduct.produce` with the
record consumer; selecting the first record costs one actual instruction. -/
abbrev entryProgram : Code .standard 320 := backend.entryProgram

/-- Complete initialized structured execution. The actual producer execution is a conclusion,
and its same native memory supplies the coordinate list consumed by the composed adapter. -/
theorem exec_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    backend.InputPost (W := W) (g := g) (p := p) hD hN values :=
  backend.exec_input values hlen hD hg hp hN hv hW

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Circuit.Boolean.NativeEvaluation
public import CslibFrontier.Computability.Circuit.Boolean.PopulationCount

/-! Checked non-Keccak clients for retained Boolean-circuit evaluation. -/

public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.NativeEvaluation

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open Turing.MultiTapeTM Turing.MultiTapeTM.Internal.NativeCompiler

/-- The fixed evaluator really runs the nonconstant 13-input population-count circuit. -/
example (input : BitString 13) :
    (evalCircuitCompiler (populationCountCircuit 13)).table.toTM.ComputesTidilyInTimeAndSpace
      (encBitString 13 input)
      (encBitString (Nat.clog 2 (13 + 1) + 1)
        ((populationCountCircuit 13).eval interpretation input))
      ((evalCircuitCompiler (populationCountCircuit 13)).time input)
      ((evalCircuitCompiler (populationCountCircuit 13)).workspace input) :=
  (evalCircuitCompiler (populationCountCircuit 13)).computes input

/-- The retained client emits exactly the population-count circuit's declared output width. -/
example (input : BitString 13) :
    (evalCircuitCompiler (populationCountCircuit 13)).outputBits input =
      Nat.clog 2 (13 + 1) + 1 :=
  outputBits_evalCircuitCompiler (populationCountCircuit 13) input

/-- The semantic output of the checked retained client is the exact Hamming weight. -/
example (input : BitString 13) :
    (BitString.equivFin (Nat.clog 2 (13 + 1) + 1)
      ((populationCountCircuit 13).eval interpretation input) : ℕ) =
        BitString.weight input :=
  val_eval_populationCountCircuit 13 input

/-- The same fixed circuit remains available through the ordinary PPT interface when concrete
program and resource coordinates are intentionally forgotten. -/
example : ComputableInPolyTime
    ((populationCountCircuit 13).eval interpretation)
    (encBitString 13) (encBitString (Nat.clog 2 (13 + 1) + 1)) :=
  computableInPolyTime_evalFixedCircuit (populationCountCircuit 13)

end CslibFrontierTests.Computability.Circuit.Boolean.NativeEvaluation

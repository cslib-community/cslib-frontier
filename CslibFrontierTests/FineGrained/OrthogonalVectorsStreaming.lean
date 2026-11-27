/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Ordinary-module clients of the orthogonal-vectors stream

The computed first half of the formula's variables drives the enumeration. Each vector is
followed by `false`, and the stream ends with `true`; concrete cases check vector and finish
order. An empty half still enumerates its one empty assignment, rather than running zero rounds.
-/

public section

namespace CslibFrontierTests.FineGrained.OrthogonalVectorsStreaming

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- Mark each streamed vector and append a distinct final marker. -/
def markedFirstHalf (φ : CNF ℕ) : List Bool :=
  ((OV.halfVectors φ (OV.firstVars φ)).map (fun word => word ++ [false])).flatten ++ [true]

example : ∃ e, ComputableInO markedFirstHalf encCNF encBits
    (fun φ => 2 ^ (OV.firstVars φ).length * ((encCNF φ).length + 1) ^ e)
    (fun φ => 2 ^ (OV.firstVars φ).length * ((encCNF φ).length + 1) ^ e) := by
  have hwrap : ComputableInPolyTime (fun word : List Bool => word ++ [false]) encBits encBits :=
    ComputableInPolyTime.bitsAppend .id' (.const [false])
  exact OV.exists_computableInO_stream OV.computableInPolyTime_firstVars
    OV.length_firstVars_le hwrap [true]

example : markedFirstHalf [] = [false, true] := by decide +kernel

example : markedFirstHalf [[(0, true)]] = [true, false, true] := by decide +kernel

example : markedFirstHalf [[(0, true), (1, true)]] = [true, false, false, false, true] := by
  decide +kernel

end CslibFrontierTests.FineGrained.OrthogonalVectorsStreaming

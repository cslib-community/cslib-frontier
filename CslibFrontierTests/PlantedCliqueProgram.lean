/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.Program
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
meta import CslibFrontier.Algorithms.PlantedClique.Program

/-!
# Computational clients of the uniform recovery program

The full recovery run below starts from an asymmetric raw word, with set diagonal bits and
empty lower-triangle entries. It checks that the decoder, stored integer power search, stable
selection and list-valued cleanup compose to recover an interspersed six-clique. This small
instance is an execution check outside the probability theorem's conservative size promise.

Further checks cover missing bits, ignored diagonal bits, the no-growth fallback, and a
zero-dimensional input. The certificate client computes the public target size from a varying
vertex count and then calls the same recovery program on the supplied raw adjacency word.

Run with `scripts/build.sh CslibFrontierTests.PlantedCliqueProgram --wfail --iofail`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueProgram

open Cslib.Algorithms.PlantedClique Turing.MultiTapeTM

private def upperOnlyClique : RecoveryInput where
  vertexCount := 8
  cliqueSize := 6
  adjacencyBits := (List.range 8).flatMap fun i =>
    (List.range 8).map fun j =>
      decide (i ≤ j ∧ i ∈ ([0, 1, 3, 4, 6, 7] : List ℕ) ∧
        j ∈ ([0, 1, 3, 4, 6, 7] : List ℕ))

-- The decoder removes diagonal bits and reflects upper-triangle edges.
example : (RecoveryInput.mk 2 1 [true, true, false, true]).signedRows =
    [[0, 1], [1, 0]] := by
  decide +kernel

-- Two framed unary fields of lengths two and one, followed by two raw bits.
example : (encRecoveryInput (RecoveryInput.mk 2 1 [true, false])).length = 10 := by
  decide +kernel

set_option linter.hashCommand false

#guard recoverInput upperOnlyClique == [0, 1, 3, 4, 6, 7]

-- The only supplied bit is diagonal, and every missing edge bit is false.
#guard recoverInput (RecoveryInput.mk 3 2 [true]) == []

#guard recoveredIntegerVector (RecoveryInput.mk 1 1 []) == [0]

#guard recoverInput (RecoveryInput.mk 0 6 [true, false, true]) == []

-- Runtime dimensions and raw words are inputs to one composed machine certificate.
example : ComputableInPolyTime
    (fun p : ℕ × List Bool => recoverInput ⟨p.1, p.1 / 2, p.2⟩)
    (encPair encUnary encBits) (encList encUnary) := by
  apply computableInPolyTime_recoverInput.comp
  fun_prop

end CslibFrontierTests.PlantedCliqueProgram

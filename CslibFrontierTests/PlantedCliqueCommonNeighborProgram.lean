/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.CommonNeighborProgram
meta import CslibFrontier.Algorithms.PlantedClique.CommonNeighborProgram

/-!
# Runtime clients of common-neighbor recovery

The graph below has an isolated vertex followed by a five-clique. The one-seed wrapper must
reject the first seed before recovering from a later one. The checks also cover relabeling,
invalid reduced outputs, and verification of duplicate, out-of-range, and nonclique answers.
The certificate client keeps the seed size fixed while both input dimensions and all adjacency
bits remain runtime data.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueCommonNeighborProgram

open Cslib.Algorithms.PlantedClique Turing.MultiTapeTM

private def isolatedThenClique : RecoveryInput where
  vertexCount := 6
  cliqueSize := 5
  adjacencyBits := (List.range 6).flatMap fun i =>
    (List.range 6).map fun j => decide (0 < i ∧ 0 < j ∧ i ≠ j)

set_option linter.hashCommand false

#guard isolatedThenClique.commonVertices [2, 4] == [1, 3, 5]

#guard (isolatedThenClique.inducedInput [1, 3, 5] 3).adjacencyBits ==
  [false, true, true, true, false, true, true, true, false]

#guard commonNeighborCandidate (fun _ => [99, 0, 0, 3]) isolatedThenClique [1] == [1, 2, 5]

#guard isolatedThenClique.validatesClique [1, 2, 3, 4, 5]

#guard !(isolatedThenClique.validatesClique [1, 1, 2, 3, 4])

#guard !(isolatedThenClique.validatesClique [1, 2, 3, 4, 6])

#guard !(isolatedThenClique.validatesClique [0, 1, 2, 3, 4])

#guard commonNeighborRecover recoverInput 1 isolatedThenClique == [1, 2, 3, 4, 5]

#guard commonNeighborRecover (fun _ => [99]) 1 isolatedThenClique == []

example (s : ℕ) : ComputableInPolyTime (commonNeighborRecover recoverInput s)
    encRecoveryInput (encList encUnary) :=
  computableInPolyTime_commonNeighborRecover s computableInPolyTime_recoverInput

example (x : RecoveryInput) (seed : List ℕ) (k : ℕ) :
    (x.inducedInput (x.commonVertices seed) k).graph =
      x.graph.comap (x.commonVertexEmbedding seed) :=
  x.graph_inducedInput _ _ (x.commonVertexEmbedding seed).toEmbedding (fun _ => rfl)

end CslibFrontierTests.PlantedCliqueCommonNeighborProgram

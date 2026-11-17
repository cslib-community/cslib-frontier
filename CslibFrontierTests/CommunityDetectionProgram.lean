/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Algorithms.CommunityDetection.Program
import CslibFrontier.Foundations.Data.List.Lookup
meta import CslibFrontier.Algorithms.CommunityDetection.Program

/-!
# Clients of the native community-recovery program

The execution case recovers two communities from two disjoint edges on four vertices. It runs
the complete matrix construction, power search, sign rounding, and cleanup. The small example
does not satisfy the conservative sufficient size bound of the probability theorem.

The ordinary-import clients check unconditional native efficiency, agreement with semantic
labels on presented graphs, and the dense input word layout. A zero-dimensional execution
checks the empty matrix and output path.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CommunityDetectionProgram

open Cslib Cslib.Algorithms.CommunityDetection Turing.MultiTapeTM

private def twoEdges : DenseGraphInput where
  vertexCount := 4
  adjacencyBits := [false, true, false, false, true, false, false, false,
    false, false, false, true, false, false, true, false]

example (params : PowerParameters) :
    ComputableInPolyTime
      (fun x : ℕ × List Bool => recoverInput params ⟨x.1, x.2⟩)
      (encPair encUnary encBits) (encList encBool) := by
  apply (computableInPolyTime_recoverInput params).comp
  fun_prop

open scoped Classical in
example (params : PowerParameters) {n : ℕ} (G : SimpleGraph (Fin n)) :
    (fun i : Fin n => (recoverInput params (DenseGraphInput.ofGraph G)).getD i.val false) =
      recoverPower params G := by
  simp only [recoverInput_ofGraph, List.getD_ofFn]

example (x : DenseGraphInput) :
    encDenseGraphInput x = encPair encUnary encBits (x.vertexCount, x.adjacencyBits) := rfl

set_option linter.hashCommand false

#guard recoverInput ⟨4, 8⟩ twoEdges == [false, false, true, true]

#guard recoverInput ⟨4, 8⟩ ⟨0, [true, false, true]⟩ == []

end CslibFrontierTests.CommunityDetectionProgram

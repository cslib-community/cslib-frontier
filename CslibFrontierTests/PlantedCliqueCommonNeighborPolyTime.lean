/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.CommonNeighborPolyTime

/-!
# Native solver clients for common-neighbor recovery

These ordinary-import clients use the actual native certificate and the represented
distributional-search endpoint. A uniform planted-set prior at `k(n)=n` defines a valid problem
at every dimension. The budget checks include dimension zero and a reduced target below the
numerical promise; these parameters remain covered by the all-parameter solver theorem.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueCommonNeighborPolyTime

open Cslib Cslib.Probability Cslib.Probability.PlantedClique
open Cslib.Algorithms.PlantedClique Turing.MultiTapeTM

example (s : ℕ) : IsPPTOn encRecoveryInput (encList encUnary)
    (fun input => pure (commonNeighborRecover recoverInput s input)) :=
  (computableInPolyTime_commonNeighborRecover s computableInPolyTime_recoverInput).isPPTOn

example (s : ℕ) : DistributionalSearchProblem.HasSolver
    (fun n => searchProblem (uniformPlantedSet n n le_rfl))
    (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
      (ProbComp.eval (program (RecoveryInput.ofGraph G n))).map (vertexSet n))
    (IsPPTOn encRecoveryInput (encList encUnary))
    (fun n => commonNeighborFailureBound n n s) :=
  searchProblem_commonNeighbor_hasPPTSolver s id (fun n => uniformPlantedSet n n le_rfl)

example (s : ℕ) : commonNeighborFailureBound 0 0 s = 1 := by
  simp [commonNeighborFailureBound]

example : commonNeighborFailureBound 8 6 1 = 1 := by
  simp [commonNeighborFailureBound]

end CslibFrontierTests.PlantedCliqueCommonNeighborPolyTime

/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.EigenvectorHybrid
import Mathlib.Tactic.NormNum

/-!
# Concrete clients of the sharpened eigenvector and hybrid solvers

The dimension `49 * 2 ^ 64` and target `51 * 2 ^ 32` meet the spectral size threshold exactly.
The uniform planted-set prior at these parameters witnesses that the raw and hybrid probability
theorems have nonempty hypotheses. A full planted clique in dimension `2 ^ 64` exercises the
hybrid's large-clique branch, outside the raw theorem's sparsity regime.

These large examples are symbolic applications of the actual programs' probability theorems;
they do not evaluate a matrix power or allocate a graph. Only the empty-input example executes.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueEigenvectorSharp

open Cslib Cslib.Algorithms.PlantedClique
open Cslib.Probability Cslib.Probability.PlantedClique Turing.MultiTapeTM

private abbrev thresholdN : ℕ := 49 * 2 ^ 64

private abbrev thresholdK : ℕ := 51 * 2 ^ 32

private theorem threshold_sqrt : Real.sqrt (thresholdN : ℝ) = 7 * 2 ^ 32 := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
  norm_num [thresholdN]

private theorem threshold_eq : (51 / 7 : ℝ) * Real.sqrt thresholdN = thresholdK := by
  rw [threshold_sqrt]
  norm_num [thresholdK]

example : ComputableInPolyTime recoverHybridEigenvectorInput encRecoveryInput
    (encList encUnary) := by
  fun_prop

example : recoverHybridEigenvectorInput ⟨0, 0, []⟩ = [] := by
  decide +kernel

-- The actual raw-adjacency algorithm has its error guarantee at the exact numerical threshold.
example :
    ((searchProblem (uniformPlantedSet thresholdN thresholdK
      (by norm_num [thresholdN, thresholdK]))).experiment
      (fun G => PMF.pure (vertexSet thresholdN
        (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G thresholdK)))) false).toReal ≤
      eigenvectorSharpError thresholdN thresholdK := by
  apply searchProblem_recoverApproximateEigenvectorInput_failure_le_sharp
  · norm_num [thresholdN]
  · norm_num [thresholdN, thresholdK]
  · exact threshold_eq.le

-- At this threshold the hybrid really uses the second-eigenvector branch.
example (G : SimpleGraph (Fin thresholdN)) :
    recoverHybridEigenvectorInput (RecoveryInput.ofGraph G thresholdK) =
      recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G thresholdK) := by
  unfold recoverHybridEigenvectorInput
  exact ite_eq_right (by
    change ¬1048576 * thresholdN ≤ thresholdK ^ 2
    norm_num [thresholdN, thresholdK])

example :
    ((searchProblem (uniformPlantedSet thresholdN thresholdK
      (by norm_num [thresholdN, thresholdK]))).experiment
      (fun G => PMF.pure (vertexSet thresholdN
        (recoverHybridEigenvectorInput (RecoveryInput.ofGraph G thresholdK)))) false).toReal ≤
      eigenvectorSharpError thresholdN thresholdK := by
  apply searchProblem_recoverHybridEigenvectorInput_failure_le
  · norm_num [thresholdN]
  · exact threshold_eq.le

-- A full planted clique uses the certified integer matrix-power branch.
example (G : SimpleGraph (Fin (2 ^ 64))) :
    recoverHybridEigenvectorInput (RecoveryInput.ofGraph G (2 ^ 64)) =
      recoverInput (RecoveryInput.ofGraph G (2 ^ 64)) := by
  unfold recoverHybridEigenvectorInput
  exact ite_eq_left (by
    change 1048576 * (2 ^ 64 : ℕ) ≤ (2 ^ 64) ^ 2
    norm_num)

example :
    ((searchProblem (uniformPlantedSet (2 ^ 64) (2 ^ 64) le_rfl)).experiment
      (fun G => PMF.pure (vertexSet (2 ^ 64)
        (recoverHybridEigenvectorInput (RecoveryInput.ofGraph G (2 ^ 64))))) false).toReal ≤
      eigenvectorSharpError (2 ^ 64) (2 ^ 64) := by
  apply searchProblem_recoverHybridEigenvectorInput_failure_le
  · norm_num
  · have hsqrt : Real.sqrt ((2 ^ 64 : ℕ) : ℝ) = 2 ^ 32 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      norm_num
    rw [hsqrt]
    norm_num

example : DistributionalSearchProblem.HasSolver
    (fun n => searchProblem (uniformPlantedSet n n le_rfl))
    (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
      (ProbComp.eval (program (RecoveryInput.ofGraph G n))).map (vertexSet n))
    (IsPPTOn encRecoveryInput (encList encUnary))
    (fun n => hybridEigenvectorRecoveryFailureBound n n) :=
  searchProblem_hybridEigenvector_hasPPTSolver id (fun n => uniformPlantedSet n n le_rfl)

end CslibFrontierTests.PlantedCliqueEigenvectorSharp

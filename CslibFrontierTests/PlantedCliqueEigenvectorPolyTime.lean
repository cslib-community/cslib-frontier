/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.EigenvectorPolyTime
import Mathlib.Tactic.NormNum

/-!
# Clients of the native finite-precision eigenvector solver

These ordinary-import clients check the native certificates for the rational output and the
complete recovery program, correctness on canonical graph inputs without a supplied
approximation, the uniform family interface, and the actual program's probability bound in a
feasible numerical regime. The large dimension is used only symbolically; no default filter
power or large graph is evaluated here. Small executable checks live in
`PlantedCliqueEigenvectorProgram`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueEigenvectorPolyTime

open Cslib Cslib.Algorithms.PlantedClique Cslib.Algorithms.IntegerVector
open Cslib.Probability Cslib.Probability.PlantedClique Turing.MultiTapeTM Finset

example : ComputableInPolyTime approximateSecondEigenvectorInput encRecoveryInput
    encRationalVector := by
  fun_prop

example : ComputableInPolyTime recoverApproximateEigenvectorInput encRecoveryInput
    (encList encUnary) := by
  fun_prop

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hclique : G.IsClique (S : Set (Fin n)))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256)
    (hdegree : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * S.card) :
    vertexSet n (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G S.card)) = S :=
  recoverApproximateEigenvectorInput_ofGraph_eq G S hk hsparse hclique hnoise hdegree

example : DistributionalSearchProblem.HasSolver
    (fun n => searchProblem (uniformPlantedSet n n le_rfl))
    (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
      (ProbComp.eval (program (RecoveryInput.ofGraph G n))).map (vertexSet n))
    (IsPPTOn encRecoveryInput (encList encUnary))
    (fun n => eigenvectorRecoveryFailureBound n n) :=
  searchProblem_eigenvector_hasPPTSolver id (fun n => uniformPlantedSet n n le_rfl)

example : eigenvectorRecoveryFailureBound 0 0 = 1 := by
  simp [eigenvectorRecoveryFailureBound]

-- The complete executable program has the exponential guarantee in a nonempty regime.
example :
    ((searchProblem (uniformPlantedSet ((2 ^ 25) ^ 2) (2 ^ 38) (by norm_num))).experiment
      (fun G => PMF.pure (vertexSet ((2 ^ 25) ^ 2)
        (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G (2 ^ 38))))) false).toReal ≤
      2 * Real.exp (-(((2 ^ 25) ^ 2 : ℕ) : ℝ)) +
        (((2 ^ 25) ^ 2 : ℕ) : ℝ) * Real.exp (-((2 ^ 38 : ℕ) : ℝ) / 32) := by
  apply searchProblem_recoverApproximateEigenvectorInput_failure_le
  · norm_num
  · norm_num
  · norm_num
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.sqrt_sq (by positivity)]
    norm_num

end CslibFrontierTests.PlantedCliqueEigenvectorPolyTime

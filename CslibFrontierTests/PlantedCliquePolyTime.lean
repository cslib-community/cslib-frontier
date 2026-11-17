/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.PolyTime

/-!
# Uniform represented planted-clique recovery clients

These checks use the actual native polynomial-time certificate and instantiate the semantic
solver theorem with a valid uniform prior at every dimension. They check the small-dimension
failure budget and a satisfying instance of the numerical recovery promise without enumerating
the large graph or running the recovery algorithm on it.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliquePolyTime

open Cslib Cslib.Probability Cslib.Probability.PlantedClique
open Cslib.Algorithms.PlantedClique Turing.MultiTapeTM

-- The same certificate handles every runtime vertex count, target size and adjacency word.
example : IsPPTOn encRecoveryInput (encList encUnary)
    (fun input => pure (recoverInput input)) :=
  computableInPolyTime_recoverInput.isPPTOn

-- Choosing k(n)=n gives a well-defined family at all n, including n=0.
example : DistributionalSearchProblem.HasSolver
    (fun n => searchProblem (uniformPlantedSet n n le_rfl))
    (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
      (ProbComp.eval (program (RecoveryInput.ofGraph G n))).map (vertexSet n))
    (IsPPTOn encRecoveryInput (encList encUnary))
    (fun n => recoveryFailureBound n n) :=
  searchProblem_hasPPTSolver id (fun n => uniformPlantedSet n n le_rfl)

example : recoveryFailureBound 0 0 = 1 := by
  simp [recoveryFailureBound]

-- At n=k=1024², the exponential branch's size assumptions are all satisfied.
example : 1 ≤ (1024 ^ 2 : ℕ) ∧ 6 ≤ (1024 ^ 2 : ℕ) ∧
    1024 * Real.sqrt ((1024 ^ 2 : ℕ) : ℝ) ≤ ((1024 ^ 2 : ℕ) : ℝ) := by
  refine ⟨by decide, by decide, ?_⟩
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.sqrt_sq (by norm_num)]
  norm_num

end CslibFrontierTests.PlantedCliquePolyTime

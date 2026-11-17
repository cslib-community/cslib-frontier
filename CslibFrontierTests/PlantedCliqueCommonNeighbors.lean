/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.CommonNeighborFinal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Ordinary-import clients of the common-neighbor probability proof

The exposure client uses an arbitrary increasing enumeration, as required by the executable
list representation. The finite numerical client has `k = √n` and seed size `32`, below the
base algorithm's `1024 √n` threshold. It witnesses consistency of every premise without
enumerating a large graph or executing a noncomputable probability distribution.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueCommonNeighbors

open Cslib.Algorithms.PlantedClique Cslib.Probability.PlantedClique Cslib.Probability.PMF

example {n m : ℕ} (S T : Finset (Fin n)) (ω : Coins n) (e : Fin m ↪o Fin n)
    (he : ∀ i, e i ∉ T) :
    (uniformOfFintype (Coins n)).map
        (fun η => (sample S (resampleOffSeed T ω η)).comap e) =
      (uniformOfFintype (Coins m)).map
        (sample (Finset.univ.filter fun i => e i ∈ S)) :=
  uniform_sample_resampleOffSeed_comap S T ω e he

-- The three independent upper-triangle edges of an unplanted triangle are counted once each.
example :
    ((uniformOfFintype (Coins 3)).toOuterMeasure {ω : Coins 3 |
      (sample ∅ ω).IsClique ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))}).toReal =
        (1 / 8 : ℝ) := by
  rw [prob_isClique_of_disjoint ∅ Finset.univ (by simp)]
  norm_num

private theorem feasible_regime :
    1 ≤ ((2 ^ 24) ^ 2 : ℕ) ∧ 6 ≤ (2 ^ 24 : ℕ) - 32 ∧
      1024 * Real.sqrt (((2 ^ 24 : ℕ) : ℝ) +
        2 * (((2 ^ 24) ^ 2 : ℕ) : ℝ) * (2 ^ 32 : ℝ)⁻¹) ≤
          (((2 ^ 24 : ℕ) - 32 : ℕ) : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  calc
    _ ≤ 1024 * Real.sqrt ((2 ^ 13 : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num)
      norm_num
    _ = 1024 * (2 ^ 13 : ℝ) := by rw [Real.sqrt_sq (by positivity)]
    _ ≤ _ := by norm_num

-- A public distributional-search endpoint for the actual represented common-neighbor solver.
example :
    ((searchProblem
      (uniformPlantedSet ((2 ^ 24) ^ 2) (2 ^ 24) (by norm_num))).experiment
        (fun G => PMF.pure (vertexSet ((2 ^ 24) ^ 2)
          (commonNeighborRecover recoverInput 32 (RecoveryInput.ofGraph G (2 ^ 24)))))
      false).toReal ≤
      (Real.exp (-2 * (((2 ^ 24) ^ 2 : ℕ) : ℝ) * ((2 ^ 32 : ℝ)⁻¹) ^ 2) +
        (2 * Real.exp (-(((2 ^ 24 : ℕ) - 32 : ℕ) : ℝ)) +
          (((2 ^ 24) ^ 2 : ℕ) : ℝ) *
            Real.exp (-(((2 ^ 24 : ℕ) - 32 : ℕ) : ℝ) / 32))) +
      ((((2 ^ 24) ^ 2 : ℕ) : ℝ) * Real.exp (-((2 ^ 24 : ℕ) : ℝ) / 32) +
        ((2 ^ 24) ^ 2 : ℕ).choose ((2 ^ 24 : ℕ) / 4) *
          ((2 : ℝ) ^ ((2 ^ 24 : ℕ) / 4).choose 2)⁻¹) :=
  searchProblem_commonNeighborRecover_failure_le _ 32 feasible_regime.1 feasible_regime.2.1
    feasible_regime.2.2

end CslibFrontierTests.PlantedCliqueCommonNeighbors

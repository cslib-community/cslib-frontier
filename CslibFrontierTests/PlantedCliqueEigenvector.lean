/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.PlantedClique.EigenvectorFinal
import Mathlib.Tactic.NormNum

/-!
# Ordinary-import clients of the raw-adjacency eigenvector theorem

These clients verify the public exact spectral specification, its finite-accuracy tolerance,
and its distributional-search endpoint. The numerical instance `n = 2^50`, `k = 2^38` satisfies
both conservative inequalities. No large graph is enumerated and no noncomputable eigenvector
is executed. The instance witnesses consistency of the numerical regime, not a practical size
recommendation.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PlantedCliqueEigenvector

open Cslib.Algorithms.PlantedClique Cslib.Probability.PlantedClique
open Finset

example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : ‖secondEigenvector G‖ = 1 :=
  norm_secondEigenvector G (by decide)

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 1 < n) :
    (G.adjMatrix ℝ).toEuclideanLin (secondEigenvector G) =
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)).eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) ⟨1, hn⟩ • secondEigenvector G :=
  adjMatrix_apply_secondEigenvector G hn

-- The approximation tolerance requires neither exact normalization nor a fixed eigenvector sign.
example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hclique : G.IsClique (S : Set (Fin n)))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256)
    (hdegree : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * S.card)
    (v : EuclideanSpace ℝ (Fin n))
    (happrox : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ‖v - ε • secondEigenvector G‖ ≤ 1 / 64) :
    G.recoverCliqueByDegree S.card
      (List.selectLargest (fun i => |v i|) S.card (List.finRange n)) = S :=
  recoverFromApproximateSecondEigenvector_eq G S hk hsparse hclique hnoise hdegree v happrox

private theorem feasible_regime :
    6 ≤ (2 ^ 38 : ℕ) ∧ 4096 * (2 ^ 38 : ℕ) ≤ (2 ^ 25) ^ 2 ∧
      8192 * Real.sqrt (((2 ^ 25) ^ 2 : ℕ) : ℝ) ≤ ((2 ^ 38 : ℕ) : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.sqrt_sq (by positivity)]
  norm_num

-- A genuine uniform-hidden-set search experiment at parameters satisfying every size premise.
open scoped Classical in
example :
    ((searchProblem (uniformPlantedSet ((2 ^ 25) ^ 2) (2 ^ 38) (by norm_num))).experiment
      (fun G => PMF.pure (recoverEigenvector G (2 ^ 38))) false).toReal ≤
      2 * Real.exp (-(((2 ^ 25) ^ 2 : ℕ) : ℝ)) +
        (((2 ^ 25) ^ 2 : ℕ) : ℝ) * Real.exp (-((2 ^ 38 : ℕ) : ℝ) / 32) :=
  searchProblem_recoverEigenvector_failure_le _ (by norm_num) feasible_regime.1
    feasible_regime.2.1 feasible_regime.2.2

end CslibFrontierTests.PlantedCliqueEigenvector

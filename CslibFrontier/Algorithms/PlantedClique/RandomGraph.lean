/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Algorithm
public import CslibFrontier.Algorithms.PlantedClique.Indicator
public import CslibFrontier.Probability.PlantedClique.Model
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith

/-!
# The planted graph as a rank-one signal plus noise

The signed adjacency matrix of the planted graph is its indicator outer product plus the
centered random noise, with a diagonal correction. That diagonal correction has operator norm
at most one. Consequently, the random-matrix bound `36 √n` gives the perturbation bound required
by the deterministic recovery proof when the planted set has size at least `1024 √n`.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix
open Cslib.Probability.PlantedClique

variable {n : ℕ}

/-- The signed adjacency matrix is the clique signal plus centered noise minus its planted
diagonal. The subtraction of the diagonal accounts for the absence of graph loops. -/
theorem signedAdjacency_sample_sub_cliqueSignal (S : Finset (Fin n)) (ω : Coins n) :
    (signedAdjacency (sample S ω)).map (Int.castRingHom ℝ) - cliqueSignal S =
      noise S ω - Matrix.diagonal (indicator S) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S <;>
      simp [signedAdjacency, cliqueSignal, indicator, Matrix.vecMulVec_apply, hi]
  · by_cases hS : i ∈ S ∧ j ∈ S
    · obtain ⟨hi, hj⟩ := hS
      have hadj := sample_adj_of_mem S ω hi hj hij
      simp [signedAdjacency, hij, hadj, cliqueSignal, indicator, Matrix.vecMulVec_apply,
        hi, hj, noise_of_mem S ω hi hj]
    · have hsignal : cliqueSignal S i j = 0 := by
        by_cases hi : i ∈ S
        · have hj : j ∉ S := fun hj => hS ⟨hi, hj⟩
          simp [cliqueSignal, indicator, Matrix.vecMulVec_apply, hi, hj]
        · simp [cliqueSignal, indicator, Matrix.vecMulVec_apply, hi]
      have hnoise := noise_of_not_mem S ω hij hS
      cases hω : ω (min i j, max i j) <;>
        simp [signedAdjacency, sample, hij, hS, hsignal, hnoise, hω]

/-- The planted diagonal is a coordinate projection and has operator norm at most one. -/
theorem opNorm_diagonal_indicator_le_one (S : Finset (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator S))‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  by_cases hi : i ∈ S <;> simp [indicator, hi]

/-- Removing the planted diagonal adds at most one to the centered-noise operator norm. -/
theorem opNorm_signedAdjacency_sample_sub_cliqueSignal_le (S : Finset (Fin n)) (ω : Coins n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((signedAdjacency (sample S ω)).map (Int.castRingHom ℝ) - cliqueSignal S)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ + 1 := by
  have hdiagonal := opNorm_diagonal_indicator_le_one S
  have htriangle := norm_sub_le (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator S)))
  rw [signedAdjacency_sample_sub_cliqueSignal, map_sub]
  linarith only [hdiagonal, htriangle]

/-- On the good random-matrix event, a planted set of size at least `1024 √n` has the
`#S / 16` perturbation bound used by deterministic recovery. -/
theorem opNorm_residual_le_card_div_sixteen (S : Finset (Fin n)) (ω : Coins n)
    (hn : 1 ≤ n) (hsize : 1024 * Real.sqrt n ≤ (S.card : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ ≤ 36 * Real.sqrt n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((signedAdjacency (sample S ω)).map (Int.castRingHom ℝ) - cliqueSignal S)‖ ≤
      (S.card : ℝ) / 16 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  linarith [opNorm_signedAdjacency_sample_sub_cliqueSignal_le S ω]

end Cslib.Algorithms.PlantedClique

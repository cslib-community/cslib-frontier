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
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Tactic.Linarith

/-!
# Signed and raw adjacency as signal plus noise

The signed adjacency matrix of the planted graph is its indicator outer product plus the
centered random noise, with a diagonal correction. That diagonal correction has operator norm
at most one. Consequently, the random-matrix bound `36 √n` gives the perturbation bound required
by the deterministic recovery proof when the planted set has size at least `1024 √n`.

For ordinary adjacency, the signal has rank at most two. The shared operator and directional
residual bounds divide signed noise by two and include both diagonal corrections, with an
additive error of at most one. Both the original and sharper second-eigenvector analyses use
these identities.
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

/-- Express the raw-adjacency rank-two error through signed adjacency, including the
diagonal correction that removes self-loops. -/
theorem adjMatrix_sub_rank_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) :
    G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S) =
      (1 / 2 : ℝ) • ((signedAdjacency G).map (Int.castRingHom ℝ) - cliqueSignal S -
        Matrix.diagonal (indicator univ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i ∈ S <;>
      norm_num [signedAdjacency, cliqueSignal, indicator, Matrix.vecMulVec_apply, hi]
  · by_cases hadj : G.Adj i j <;> by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      norm_num [signedAdjacency, cliqueSignal, indicator, Matrix.vecMulVec_apply, hij, hadj, hi, hj]


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

/-- The raw rank-two residual has half the signed-noise norm, with an additive one for
the two diagonal corrections. -/
theorem opNorm_raw_residual_le (S : Finset (Fin n)) (ω : Coins n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      ((sample S ω).adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ / 2 + 1 := by
  have hr := opNorm_signedAdjacency_sample_sub_cliqueSignal_le S ω
  have hd := opNorm_diagonal_indicator_le_one (univ : Finset (Fin n))
  rw [adjMatrix_sub_rank_two, map_smul, map_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have ht := norm_sub_le
    (Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((signedAdjacency (sample S ω)).map (Int.castRingHom ℝ) - cliqueSignal S))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator univ)))
  linarith

/-- In any fixed direction, the raw rank-two residual is controlled by half the signed
noise in that direction and a diagonal correction of at most the vector's norm. -/
theorem norm_raw_residual_apply_le (S : Finset (Fin n)) (ω : Coins n)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      ((sample S ω).adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S)) y‖ ≤
      ‖(noise S ω).toEuclideanLin y‖ / 2 + ‖y‖ := by
  have hd (T : Finset (Fin n)) :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator T)) y‖ ≤ ‖y‖ :=
    (ContinuousLinearMap.le_opNorm _ y).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (opNorm_diagonal_indicator_le_one T) (norm_nonneg y))
  rw [adjMatrix_sub_rank_two, signedAdjacency_sample_sub_cliqueSignal,
    map_smul, map_sub, map_sub, smul_apply,
    sub_apply, sub_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have ht := (norm_sub_le
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω) y -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator S)) y)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator univ)) y)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  have hdS := hd S
  have hdU := hd univ
  change (1 / 2 : ℝ) * ‖(noise S ω).toEuclideanLin y -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator S)) y -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator univ)) y‖ ≤ _
  change ‖(noise S ω).toEuclideanLin y -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator S)) y -
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator univ)) y‖ ≤
    ‖(noise S ω).toEuclideanLin y‖ +
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator S)) y‖ +
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (indicator univ)) y‖ at ht
  linarith

/-- On the good random-matrix event, a planted set of size at least `1024 √n` has the
`#S / 16` perturbation bound used by deterministic recovery. -/
theorem opNorm_residual_le_card_div_sixteen (S : Finset (Fin n)) (ω : Coins n)
    (hn : 1 ≤ n) (hsize : 1024 * Real.sqrt n ≤ (S.card : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ ≤ 36 * Real.sqrt n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((signedAdjacency (sample S ω)).map (Int.castRingHom ℝ) - cliqueSignal S)‖ ≤
      (S.card : ℝ) / 16 := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnreal
  have hresidual := opNorm_signedAdjacency_sample_sub_cliqueSignal_le S ω
  have hbound : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((signedAdjacency (sample S ω)).map (Int.castRingHom ℝ) - cliqueSignal S)‖ ≤
      37 * Real.sqrt n := by linarith
  linarith

end Cslib.Algorithms.PlantedClique

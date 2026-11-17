/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.EigenvectorBounds
public import CslibFrontier.Algorithms.PlantedClique.EigenvectorPolyTime
public import CslibFrontier.Algorithms.PlantedClique.Directional
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A sharper probability bound for the native second-eigenvector program

The actual finite-precision recovery program succeeds for `n ≥ 2^64`, `4096 k ≤ n`, and
`(51 / 7) √n ≤ k`, with the explicit error `eigenvectorSharpError n k`. Its program and native
polynomial-time certificate are the ones in `EigenvectorPolyTime`; no eigenvector or accuracy
witness is supplied as input.

This quantitative variant of the residual argument in [AlonKrivelevichSudakov1998], Section 2.2,
uses a single quadratic-form net for the operator norm and the library's Rademacher-row
concentration for the planted direction. The constants and finite cutoff are derived here.
The two estimates have different purposes: the global norm isolates the second eigenvalue,
while the directional norm gives a substantially smaller eigenvector error. Degree cleanup
then uses a sharper outside-degree estimate. The upper size restriction belongs to this
spectral theorem; `EigenvectorHybrid` supplies a separate large-clique branch.

## Main results

* `prob_recoverApproximateEigenvectorInput_ne_le_sharp`: fixed-set recovery failure.
* `searchProblem_recoverApproximateEigenvectorInput_failure_le_sharp`: the same bound for
  every independent prior on planted sets of the public target size.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix
open Cslib.Probability Cslib.Probability.PlantedClique

/-- Exponential failure budget for the sharpened second-eigenvector analysis: global noise,
noise in the clique direction, and outside degrees, respectively. -/
@[expose] noncomputable def eigenvectorSharpError (n k : ℕ) : ℝ :=
  2 * Real.exp (-(n : ℝ) / 64) + Real.exp (-(n : ℝ) / 16777216) +
    n * Real.exp (-(k : ℝ) / 32768)

private theorem recover_sample_eq_of_sharp_events {n : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    (hnlarge : 2 ^ 64 ≤ n) (hsparse : 4096 * S.card ≤ n)
    (hsize : 51 / 7 * Real.sqrt n ≤ (S.card : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ ≤ 30 / 7 * Real.sqrt n)
    (hdirection : ‖(noise S ω).toEuclideanLin (unitIndicator S)‖ ^ 2 ≤
      (1 + 1 / 1024 : ℝ) * n)
    (hdegree : ∀ v ∉ S,
      ((S.filter ((sample S ω).Adj v)).card : ℝ) ≤ 129 / 256 * S.card) :
    vertexSet n (recoverApproximateEigenvectorInput
      (RecoveryInput.ofGraph (sample S ω) S.card)) = S := by
  have hn40000 : (40000 : ℝ) ≤ n := by
    exact_mod_cast ((by norm_num : 40000 ≤ 2 ^ 64).trans hnlarge)
  have hroot : 200 ≤ Real.sqrt (n : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]
  have hk : 200 ≤ S.card := by
    have h : (200 : ℝ) ≤ S.card := by linarith
    exact_mod_cast h
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hraw := (opNorm_raw_residual_le S ω).trans
    (show ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ / 2 + 1 ≤
      15 / 7 * Real.sqrt n + 1 by linarith)
  have hdir : ‖(noise S ω).toEuclideanLin (unitIndicator S)‖ ≤
      1025 / 1024 * Real.sqrt n := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hrawdir := norm_raw_residual_apply_le S ω (unitIndicator S)
  rw [norm_unitIndicator hS] at hrawdir
  have hrawdir' : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      ((sample S ω).adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))
        (unitIndicator S)‖ ≤ 1025 / 2048 * Real.sqrt n + 1 := by
    linarith
  obtain ⟨hcenter, hsep, halign⟩ := secondEigenvector_bounds_of_residual_le
    (sample S ω) S hnlarge hsparse hsize hraw hrawdir'
  exact recoverApproximateEigenvectorInput_ofGraph_eq_of_spectral_bounds
    (sample S ω) S (by omega) hk ⟨hcenter, hsep⟩
    (fun _ hi _ hj hij => sample_adj_of_mem S ω hi hj hij) halign hdegree

private theorem dens_recover_ne_le_sharp {n : ℕ} (S : Finset (Fin n))
    (hnlarge : 2 ^ 64 ≤ n) (hsparse : 4096 * S.card ≤ n)
    (hsize : 51 / 7 * Real.sqrt n ≤ (S.card : ℝ)) :
    (dens ({ω : Coins n | vertexSet n (recoverApproximateEigenvectorInput
      (RecoveryInput.ofGraph (sample S ω) S.card)) ≠ S} : Finset _) : ℝ) ≤
      eigenvectorSharpError n S.card := by
  classical
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hkpos : 0 < S.card := by
    have h : (0 : ℝ) < S.card := lt_of_lt_of_le
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr hnpos)) hsize
    exact_mod_cast h
  let N : Finset (Coins n) := {ω | 30 / 7 * Real.sqrt n <
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖}
  let R : Finset (Coins n) := {ω | (1 + 1 / 1024 : ℝ) * n <
    ‖(noise S ω).toEuclideanLin (unitIndicator S)‖ ^ 2}
  let D : Finset (Coins n) := {ω | ∃ v, v ∉ S ∧
    129 / 256 * (S.card : ℝ) < ((S.filter ((sample S ω).Adj v)).card : ℝ)}
  have hN : (dens N : ℝ) ≤ 2 * Real.exp (-(n : ℝ) / 64) := by
    have h := dens_noise_opNorm_gt_le_mul S (c := 30 / 7) (by norm_num)
    have heq : ((7 : ℝ) / 2 - 49 * (30 / 7) ^ 2 / 256) * n = -(n : ℝ) / 64 := by ring
    simpa only [heq] using h
  have hR : (dens R : ℝ) ≤ Real.exp (-(n : ℝ) / 16777216) := by
    refine (dens_noise_unitIndicator_norm_sq_gt_le S (card_pos.mp hkpos)
      (ε := 1 / 1024) (by norm_num)).trans (Real.exp_le_exp.mpr ?_)
    have hkn : S.card ≤ n := by omega
    have hhalf : (n : ℝ) / 2 ≤ ((n - S.card : ℕ) : ℝ) := by
      rw [Nat.cast_sub hkn]
      have hs : (4096 : ℝ) * S.card ≤ n := by exact_mod_cast hsparse
      linarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
    norm_num
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hD : (dens D : ℝ) ≤ n * Real.exp (-(S.card : ℝ) / 32768) := by
    have h := dens_exists_outside_degree_gt_mean_add_le S hkpos
      (η := 1 / 256) (by norm_num)
    have heq : -2 * (1 / 256 : ℝ) ^ 2 * S.card = -(S.card : ℝ) / 32768 := by ring
    simpa only [show (1 / 2 : ℝ) + 1 / 256 = 129 / 256 by norm_num, heq] using h
  have hsub : ({ω : Coins n | vertexSet n (recoverApproximateEigenvectorInput
      (RecoveryInput.ofGraph (sample S ω) S.card)) ≠ S} : Finset _) ⊆ (N ∪ R) ∪ D := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_cases hn : ω ∈ N
    · exact mem_union_left D (mem_union_left R hn)
    by_cases hr : ω ∈ R
    · exact mem_union_left D (mem_union_right N hr)
    by_cases hd : ω ∈ D
    · exact mem_union_right (N ∪ R) hd
    have hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ ≤
        30 / 7 * Real.sqrt n := by
      simpa only [N, mem_filter, mem_univ, true_and, not_lt] using hn
    have hdir : ‖(noise S ω).toEuclideanLin (unitIndicator S)‖ ^ 2 ≤
        (1 + 1 / 1024 : ℝ) * n := by
      simpa only [R, mem_filter, mem_univ, true_and, not_lt] using hr
    have hdegree : ∀ v ∉ S,
        ((S.filter ((sample S ω).Adj v)).card : ℝ) ≤ 129 / 256 * S.card := by
      intro v hv
      apply le_of_not_gt
      intro h
      apply hd
      simp only [D, mem_filter, mem_univ, true_and]
      exact ⟨v, hv, h⟩
    exact (hω (recover_sample_eq_of_sharp_events S ω hnlarge hsparse hsize
      hnoise hdir hdegree)).elim
  calc
    _ ≤ (dens ((N ∪ R) ∪ D) : ℝ) := by exact_mod_cast dens_le_dens hsub
    _ ≤ (dens (N ∪ R) : ℝ) + (dens D : ℝ) := by exact_mod_cast dens_union_le (N ∪ R) D
    _ ≤ ((dens N : ℝ) + (dens R : ℝ)) + (dens D : ℝ) := by
      have hNR : (dens (N ∪ R) : ℝ) ≤ (dens N : ℝ) + (dens R : ℝ) := by
        exact_mod_cast dens_union_le N R
      exact add_le_add hNR le_rfl
    _ ≤ eigenvectorSharpError n S.card := add_le_add (add_le_add hN hR) hD

/-- Fixed-set failure probability for the actual finite-precision second-eigenvector program
at threshold `(51 / 7) √n`. Every spectral and numerical hypothesis is discharged internally. -/
theorem prob_recoverApproximateEigenvectorInput_ne_le_sharp {n : ℕ} (S : Finset (Fin n))
    (hnlarge : 2 ^ 64 ≤ n) (hsparse : 4096 * S.card ≤ n)
    (hsize : 51 / 7 * Real.sqrt n ≤ (S.card : ℝ)) :
    ((Cslib.Probability.PMF.uniformOfFintype (Coins n)).toOuterMeasure
      {ω : Coins n | vertexSet n (recoverApproximateEigenvectorInput
        (RecoveryInput.ofGraph (sample S ω) S.card)) ≠ S}).toReal ≤
      eigenvectorSharpError n S.card := by
  classical
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast] using
    dens_recover_ne_le_sharp S hnlarge hsparse hsize

/-- The same finite-precision program has the sharp failure guarantee under every independent
prior on hidden sets of the public target size, in the stated spectral regime. -/
theorem searchProblem_recoverApproximateEigenvectorInput_failure_le_sharp {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hnlarge : 2 ^ 64 ≤ n) (hsparse : 4096 * k ≤ n)
    (hsize : 51 / 7 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment
      (fun G => PMF.pure (vertexSet n
        (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G k)))) false).toReal ≤
      eigenvectorSharpError n k := by
  refine searchProblem_failure_le_of_fixedSet prior
    (fun G => vertexSet n (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G k)))
    (by unfold eigenvectorSharpError; positivity) ?_
  intro S hS
  simpa only [hS] using prob_recoverApproximateEigenvectorInput_ne_le_sharp S hnlarge
    (by simpa only [hS] using hsparse) (by simpa only [hS] using hsize)

end Cslib.Algorithms.PlantedClique

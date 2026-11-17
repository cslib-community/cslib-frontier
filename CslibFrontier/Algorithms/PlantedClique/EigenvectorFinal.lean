/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Eigenvector
public import CslibFrontier.Probability.PlantedClique.Degree
public import CslibFrontier.Probability.PlantedClique.Problem
public import CslibFrontier.Probability.PlantedClique.RandomMatrix
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Finset.Density
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Tactic.Positivity

/-!
# High-probability correctness of the second-eigenvector algorithm

The exact raw-adjacency algorithm recovers the planted set with failure probability at most
`2 exp (-n) + n exp (-k / 32)` when `6 ≤ k`, `4096 k ≤ n`, and `8192 √n ≤ k`.
The spectral and degree events are the already proved bounds for the independent edge coins.
No eigenvector alignment or spectral separation assumption remains in the probability theorem.

The result is also stated for the generic distributional search experiment and any prior on
hidden `k`-sets. The solver sees the graph alone (with the target size fixed as a parameter).
The exact spectral choice in `Eigenvector` is noncomputable; these are semantic correctness
statements, not a machine complexity certificate.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Real
open Cslib.Probability.PlantedClique

variable {n : ℕ}

/-- Finite probability bound for Algorithm A on every fixed planted set in the conservative
size regime. The probability space consists only of the independent fair edge coins. -/
theorem dens_recoverEigenvector_ne_le (S : Finset (Fin n)) (hn : 1 ≤ n) (hk : 6 ≤ S.card)
    (hsparse : 4096 * S.card ≤ n) (hsize : 8192 * Real.sqrt n ≤ (S.card : ℝ)) :
    (dens ({ω : Coins n | recoverEigenvector (sample S ω) S.card ≠ S} : Finset _) : ℝ) ≤
      2 * exp (-(n : ℝ)) + n * exp (-(S.card : ℝ) / 32) := by
  classical
  let N : Finset (Coins n) := {ω | 36 * Real.sqrt n <
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖}
  let D : Finset (Coins n) := {ω | ∃ v, v ∉ S ∧
    5 * S.card < 8 * (S.filter ((sample S ω).Adj v)).card}
  have hsub : ({ω : Coins n | recoverEigenvector (sample S ω) S.card ≠ S} : Finset _) ⊆
      N ∪ D := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_cases hN : ω ∈ N
    · exact mem_union_left D hN
    by_cases hD : ω ∈ D
    · exact mem_union_right N hD
    have hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (noise S ω)‖ ≤ 36 * Real.sqrt n := by
      simpa only [N, mem_filter, mem_univ, true_and, not_lt] using hN
    have hdegree : ∀ v ∉ S, 8 * (S.filter ((sample S ω).Adj v)).card ≤ 5 * S.card := by
      intro v hv
      apply le_of_not_gt
      intro h
      apply hD
      simp only [D, mem_filter, mem_univ, true_and]
      exact ⟨v, hv, h⟩
    exact (hω (recoverEigenvector_sample_eq S ω hn hk hsparse hsize hnoise hdegree)).elim
  calc
    _ ≤ (dens (N ∪ D) : ℝ) := by exact_mod_cast dens_le_dens hsub
    _ ≤ (dens N : ℝ) + (dens D : ℝ) := by exact_mod_cast dens_union_le N D
    _ ≤ _ := add_le_add (dens_noise_opNorm_gt_le S)
      (dens_exists_outside_degree_gt_le S (by omega))

/-- PMF form of the fixed-set failure bound. -/
theorem prob_recoverEigenvector_ne_le (S : Finset (Fin n)) (hn : 1 ≤ n) (hk : 6 ≤ S.card)
    (hsparse : 4096 * S.card ≤ n) (hsize : 8192 * Real.sqrt n ≤ (S.card : ℝ)) :
    ((Cslib.Probability.PMF.uniformOfFintype (Coins n)).toOuterMeasure
      {ω : Coins n | recoverEigenvector (sample S ω) S.card ≠ S}).toReal ≤
      2 * exp (-(n : ℝ)) + n * exp (-(S.card : ℝ) / 32) := by
  classical
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  simpa only [Set.mem_ofPred_eq, dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast] using
    dens_recoverEigenvector_ne_le S hn hk hsparse hsize

open scoped Classical in
/-- The exact second-eigenvector solver satisfies the generic distributional search guarantee
for any independent prior on hidden sets of the target size. This is a semantic guarantee;
no computation model or finite-precision realization is asserted. -/
theorem searchProblem_recoverEigenvector_failure_le {k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hn : 1 ≤ n) (hk : 6 ≤ k) (hsparse : 4096 * k ≤ n)
    (hsize : 8192 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment (fun G => PMF.pure (recoverEigenvector G k)) false).toReal ≤
      2 * exp (-(n : ℝ)) + n * exp (-(k : ℝ) / 32) := by
  refine searchProblem_failure_le_of_fixedSet prior (fun G => recoverEigenvector G k)
    (by positivity) ?_
  intro S hS
  have hrecover (ω : Coins n) :
      @recoverEigenvector n (sample S ω) (fun _ _ => Classical.propDecidable _) k =
        recoverEigenvector (sample S ω) k :=
    congrArg (fun d : DecidableRel (sample S ω).Adj =>
      @recoverEigenvector n (sample S ω) d k) (Subsingleton.elim _ _)
  simp only [hrecover]
  simpa only [hS] using
    prob_recoverEigenvector_ne_le S hn (by simpa only [hS] using hk)
      (by simpa only [hS] using hsparse) (by simpa only [hS] using hsize)

end Cslib.Algorithms.PlantedClique

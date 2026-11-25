/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.RandomGraph
public import CslibFrontier.Foundations.Analysis.InnerProductSpace.EigenvectorPerturbation
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The raw-adjacency second-eigenvector algorithm

Algorithm A of [AlonKrivelevichSudakov1998], Section 2.1 (p. 3), chooses a unit eigenvector for
the second largest eigenvalue of the ordinary adjacency matrix, selects the `k` largest absolute
coordinates, and applies degree cleanup. This file specifies that algorithm using Mathlib's
**ordered** spectral theorem. In particular, index `1` belongs to the decreasingly ordered
linear-map eigenbasis, not to the arbitrarily reindexed matrix eigenbasis.

The correctness proof follows the residual argument in Section 2.2 (pp. 4--7). The rank-two
signal is `(J + 1_S 1_Sᵀ) / 2`; the exact expectation also subtracts
`(I + diag(1_S)) / 2` to remove loops. Removing the all-ones component of the planted indicator
gives an approximate eigenvector at eigenvalue `k / 2`. The first and third ordered eigenvalues
are separated from that value, so a small residual implies proximity to the second eigenline.
The existing coordinate-rounding and degree-cleanup theorems finish the argument.

The explicit constants here are conservative: `4096 k ≤ n`, `8192 √n ≤ k`, and the existing
noise event of norm at most `36 √n`. Matching the paper's constant `10` and supplying a
finite-precision implementation with a native running-time certificate are tracked in
[#6238](https://github.com/cslib-community/cslib-frontier/issues/6238).
Mathlib's exact eigenvector choice is noncomputable. This file proves mathematical correctness;
the theorem `recoverFromApproximateSecondEigenvector_eq` gives an explicit `1 / 64` Euclidean
accuracy tolerance for the numerical implementation.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A unit second eigenvector of the ordinary adjacency matrix, ordered by decreasing
algebraic eigenvalue. The output is zero only when the graph has fewer than two vertices. -/
noncomputable def secondEigenvector (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    EuclideanSpace ℝ (Fin n) :=
  if hn : 1 < n then
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)).eigenvectorBasis
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) ⟨1, hn⟩
  else 0

/-- The `k` largest absolute coordinates of the second adjacency eigenvector. -/
noncomputable def eigenvectorApproximateSet (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) : Finset (Fin n) := by
  classical
  exact List.selectLargest (fun i => |secondEigenvector G i|) k (List.finRange n)

/-- Algorithm A: second adjacency eigenvector, largest absolute coordinates, then the
`3 k / 4` degree threshold. This is an exact mathematical specification. -/
noncomputable def recoverEigenvector (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Finset (Fin n) :=
  G.recoverCliqueByDegree k (eigenvectorApproximateSet G k)

/-- The selected vector has unit norm whenever a second eigenvalue exists. -/
theorem norm_secondEigenvector (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 1 < n) : ‖secondEigenvector G‖ = 1 := by
  rw [secondEigenvector, dite_eq_left hn]
  exact OrthonormalBasis.norm_eq_one _ _

/-- The chosen vector satisfies the adjacency eigen-equation for index `1` of Mathlib's
nonincreasingly ordered spectrum. -/
theorem adjMatrix_apply_secondEigenvector (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 1 < n) :
    (G.adjMatrix ℝ).toEuclideanLin (secondEigenvector G) =
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)).eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) ⟨1, hn⟩ • secondEigenvector G := by
  rw [secondEigenvector, dite_eq_left hn]
  exact LinearMap.IsSymmetric.apply_eigenvectorBasis _ _ _

/-- Coordinate selection has the requested size if it does not exceed the vertex count. -/
theorem card_eigenvectorApproximateSet (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {k : ℕ} (hk : k ≤ n) : (eigenvectorApproximateSet G k).card = k := by
  classical
  rw [eigenvectorApproximateSet, List.card_selectLargest _ _ (List.nodup_finRange n),
    List.length_finRange, min_eq_left hk]

private theorem abs_inner_unitIndicator_univ_le (S : Finset (Fin n))
    (hS : S.Nonempty) (hsparse : 4096 * S.card ≤ n) :
    |inner ℝ (unitIndicator (univ : Finset (Fin n))) (unitIndicator S)| ≤ 1 / 64 := by
  have hk : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hkpos := hS.card_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have huniv : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, mem_univ _⟩
  have hrootk : 0 < Real.sqrt (S.card : ℝ) := Real.sqrt_pos.mpr hk
  have hrootn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn
  have hinter : inner ℝ (indicator (univ : Finset (Fin n))) (indicator S) = S.card := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, indicator]
  have heq : inner ℝ (unitIndicator (univ : Finset (Fin n))) (unitIndicator S) =
      Real.sqrt (S.card : ℝ) / Real.sqrt (n : ℝ) := by
    rw [indicator_eq_sqrt_smul_unitIndicator huniv, indicator_eq_sqrt_smul_unitIndicator hS,
      real_inner_smul_left, real_inner_smul_right] at hinter
    simp only [card_univ, Fintype.card_fin] at hinter
    apply (eq_div_iff hrootn.ne').mpr
    have hcancel : Real.sqrt (S.card : ℝ) *
        (inner ℝ (unitIndicator (univ : Finset (Fin n))) (unitIndicator S) *
          Real.sqrt (n : ℝ) - Real.sqrt (S.card : ℝ)) = 0 := by
      nlinarith only [hinter, Real.sq_sqrt hk.le]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left hrootk.ne')
  rw [heq, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hrootn).mpr
  have hsparse' : (4096 : ℝ) * S.card ≤ n := by exact_mod_cast hsparse
  have hroot : 64 * Real.sqrt (S.card : ℝ) ≤ Real.sqrt (n : ℝ) := by
    nlinarith [Real.sq_sqrt hk.le, Real.sq_sqrt hn.le]
  linarith

/-- A small perturbation of the rank-two raw-adjacency signal makes the second
adjacency eigenvector approximate the planted indicator, up to sign. -/
theorem secondEigenvector_alignment (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hS : S.Nonempty) (hsparse : 4096 * S.card ≤ n)
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖secondEigenvector G - s • unitIndicator S‖ ^ 2 ≤ 49 / 2048 := by
  have hnthree : 3 ≤ n := by have := hS.card_pos; omega
  have huniv : (univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, by omega⟩, mem_univ _⟩
  let T := (G.adjMatrix ℝ).toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
  have herr (y : EuclideanSpace ℝ (Fin n)) :
      ‖T y - (((n : ℝ) / 2 * inner ℝ (unitIndicator univ) y) • unitIndicator univ +
        ((S.card : ℝ) / 2 * inner ℝ (unitIndicator S) y) • unitIndicator S)‖ ≤
          ((S.card : ℝ) / 2) / 128 * ‖y‖ := by
    have heq : T y - (((n : ℝ) / 2 * inner ℝ (unitIndicator univ) y) • unitIndicator univ +
        ((S.card : ℝ) / 2 * inner ℝ (unitIndicator S) y) • unitIndicator S) =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S)) y := by
      simp only [map_sub, map_smul, map_add, sub_apply,
        smul_apply, add_apply]
      change T y - _ = T y - (1 / 2 : ℝ) •
        ((cliqueSignal univ).toEuclideanLin y + (cliqueSignal S).toEuclideanLin y)
      rw [cliqueSignal_apply huniv, cliqueSignal_apply hS]
      simp only [card_univ, Fintype.card_fin]
      module
    rw [heq]
    have hb := (ContinuousLinearMap.le_opNorm _ y).trans
      (mul_le_mul_of_nonneg_right hnoise (norm_nonneg y))
    convert hb using 1
    ring
  have hab : 2 * ((S.card : ℝ) / 2) ≤ (n : ℝ) / 2 := by
    have hsparse' : (4096 : ℝ) * S.card ≤ n := by exact_mod_cast hsparse
    have hk : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    linarith
  have h := hT.exists_sign_second_eigenvector_sub_sq_le_of_rank_two
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) hnthree
    (norm_unitIndicator huniv) (norm_unitIndicator hS)
    (by positivity : 0 < (S.card : ℝ) / 2) hab
    (abs_inner_unitIndicator_univ_le S hS hsparse) herr
  simpa only [secondEigenvector, dite_eq_left (show 1 < n by omega)] using h

/-- Under the rank-two perturbation bound, the selected coordinates miss at most one
sixteenth of the planted vertices. -/
theorem eigenvectorApproximateSet_overlap (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hS : S.Nonempty) (hsparse : 4096 * S.card ≤ n)
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256) :
    16 * (S \ eigenvectorApproximateSet G S.card).card ≤ S.card := by
  classical
  obtain ⟨s, hs, hclose⟩ := secondEigenvector_alignment G S hS hsparse hnoise
  apply sixteen_mul_card_sdiff_le_of_signed_norm_sub_sq_le hS
    (card_eigenvectorApproximateSet G
      (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)).symm hs ?_
    (hclose.trans (by norm_num))
  intro i hi j hj
  exact List.weight_le_of_notMem_selectLargest (fun v => |secondEigenvector G v|) S.card
    (List.finRange n) (List.mem_finRange i) hi hj

/-- Complete deterministic correctness of the raw-adjacency eigenvector specification. -/
theorem recoverEigenvector_eq_of_opNorm_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hclique : G.IsClique (S : Set (Fin n)))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256)
    (hdegree : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * S.card) :
    recoverEigenvector G S.card = S := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  exact G.recoverCliqueByDegree_eq_of_overlap rfl
    (card_eigenvectorApproximateSet G
      (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)) hclique
    (eigenvectorApproximateSet_overlap G S hS hsparse hnoise) hdegree hk

/-- The exact spectral bound leaves an explicit numerical tolerance: a vector within
`1 / 64` of either orientation of the chosen unit second eigenvector supports exact rounding and
degree cleanup. The finite-precision eigensolver is tracked in
[#6238](https://github.com/cslib-community/cslib-frontier/issues/6238). -/
theorem recoverFromApproximateSecondEigenvector_eq
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hclique : G.IsClique (S : Set (Fin n)))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (G.adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256)
    (hdegree : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * S.card)
    (v : EuclideanSpace ℝ (Fin n))
    (happrox : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ‖v - ε • secondEigenvector G‖ ≤ 1 / 64) :
    G.recoverCliqueByDegree S.card
      (List.selectLargest (fun i => |v i|) S.card (List.finRange n)) = S := by
  classical
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : (List.selectLargest (fun i => |v i|) S.card (List.finRange n)).card = S.card := by
    rw [List.card_selectLargest _ _ (List.nodup_finRange n), List.length_finRange,
      min_eq_left (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)]
  obtain ⟨s, hs, hclose⟩ := secondEigenvector_alignment G S hS hsparse hnoise
  obtain ⟨ε, hε, happrox⟩ := happrox
  have hεnorm : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hsign : ε * s = 1 ∨ ε * s = -1 := by
    rcases hε with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num
  have hexact : ‖ε • secondEigenvector G - (ε * s) • unitIndicator S‖ ≤ 5 / 32 := by
    rw [mul_smul, ← smul_sub, norm_smul, hεnorm, one_mul]
    nlinarith [norm_nonneg (secondEigenvector G - s • unitIndicator S)]
  have hnear : ‖v - (ε * s) • unitIndicator S‖ ≤ 11 / 64 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub v (ε • secondEigenvector G)
      ((ε * s) • unitIndicator S)
    linarith
  have hsq : ‖v - (ε * s) • unitIndicator S‖ ^ 2 ≤ 1 / 32 := by
    nlinarith [norm_nonneg (v - (ε * s) • unitIndicator S)]
  have hoverlap : 16 *
      (S \ List.selectLargest (fun i => |v i|) S.card (List.finRange n)).card ≤ S.card := by
    apply sixteen_mul_card_sdiff_le_of_signed_norm_sub_sq_le hS hcard.symm hsign ?_ hsq
    intro i hi j hj
    exact List.weight_le_of_notMem_selectLargest (fun i => |v i|) S.card
      (List.finRange n) (List.mem_finRange i) hi hj
  exact G.recoverCliqueByDegree_eq_of_overlap rfl hcard hclique hoverlap hdegree hk

private theorem adjMatrix_sub_rank_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
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

open Cslib.Probability.PlantedClique

/-- The existing centered-noise event also gives the rank-two perturbation bound for the
ordinary adjacency matrix, including both diagonal corrections. -/
theorem opNorm_raw_residual_le_card_div_256 (S : Finset (Fin n)) (ω : Coins n)
    (hn : 1 ≤ n) (hsize : 8192 * Real.sqrt n ≤ (S.card : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (noise S ω)‖ ≤
      36 * Real.sqrt n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      ((sample S ω).adjMatrix ℝ - (1 / 2 : ℝ) • (cliqueSignal univ + cliqueSignal S))‖ ≤
        (S.card : ℝ) / 256 := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hnreal
  have hr := opNorm_signedAdjacency_sample_sub_cliqueSignal_le S ω
  have hd := opNorm_diagonal_indicator_le_one (univ : Finset (Fin n))
  rw [adjMatrix_sub_rank_two, map_smul, map_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have ht := norm_sub_le
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      ((signedAdjacency (sample S ω)).map (Int.castRingHom ℝ) - cliqueSignal S))
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal (indicator univ)))
  nlinarith only [ht, hr, hd, hnoise, hsqrt, hsize]

/-- On the good noise and outside-degree events, Algorithm A recovers every planted set in
the explicit conservative size regime. All spectral assumptions are discharged here. -/
theorem recoverEigenvector_sample_eq (S : Finset (Fin n)) (ω : Coins n)
    (hn : 1 ≤ n) (hk : 6 ≤ S.card) (hsparse : 4096 * S.card ≤ n)
    (hsize : 8192 * Real.sqrt n ≤ (S.card : ℝ))
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (noise S ω)‖ ≤
      36 * Real.sqrt n)
    (hdegree : ∀ v ∉ S, 8 * (S.filter ((sample S ω).Adj v)).card ≤ 5 * S.card) :
    recoverEigenvector (sample S ω) S.card = S := by
  apply recoverEigenvector_eq_of_opNorm_le (sample S ω) S hk hsparse
  · intro i hi j hj hij
    exact sample_adj_of_mem S ω hi hj hij
  · exact opNorm_raw_residual_le_card_div_256 S ω hn hsize hnoise
  · exact hdegree

end Cslib.Algorithms.PlantedClique

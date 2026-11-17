/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.CommunityDetection.Cleanup
public import CslibFrontier.Probability.StochasticBlockModel.Model
public import CslibFrontier.Foundations.Data.BitString.SignWord
public import CslibFrontier.Foundations.Analysis.InnerProductSpace.EigenvectorPerturbation
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A centered spectral algorithm for two-community recovery

For known within-community and between-community probabilities `p > q`, form
`M = A - ((p+q)/2) (J-I) + ((p-q)/2) I`. The stochastic block model gives
`M = d g gᵀ + N`, with `d = (p-q)/2`, the hidden labels read as signs, and centered noise `N`.
The algorithm rounds a leading unit eigenvector of `M` to signs and then applies one weighted
vote cleanup step with the same matrix.

The deterministic proof combines a rank-one perturbation estimate, the existing sign-rounding
bound, and robustness of the cleanup vote to a bounded number of erroneous labels. It permits
arbitrary community sizes and recovers the labels up to a global swap. The noise and margin
hypotheses in this file are established under the actual graph law in the probability analysis.

The low-rank approach is described in [McSherry2001], Sections 1.1--1.2. This development gives
an original dense-regime analysis of the centered single-eigenvector and vote algorithm;
McSherry's `Partition` algorithm instead splits columns and clusters their projections.

Mathlib's ordered spectral theorem specifies an exact, noncomputable eigenvector. This file
proves correctness of that mathematical algorithm, not a finite-precision implementation or a
machine running-time certificate. The constants are conservative and the accompanying dense
regime analysis is not a formalization of a sharp sparse recovery threshold.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Finset Matrix BitString NormedSpace Probability.StochasticBlockModel
open scoped RealInnerProductSpace unitInterval

variable {n : ℕ}

private theorem shifted_isSymmetric (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : (shiftedCenteredAdjacency p q G).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (shiftedCenteredAdjacency_transpose p q G))

/-- A leading unit eigenvector of the shifted centered adjacency matrix. The spectrum is
ordered by decreasing algebraic eigenvalue; an empty graph returns the zero vector. -/
noncomputable def leadingEigenvector (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : EuclideanSpace ℝ (Fin n) :=
  if hn : 0 < n then
    (shifted_isSymmetric p q G).eigenvectorBasis
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) ⟨0, hn⟩
  else 0

/-- Initial community labels, obtained by rounding a leading eigenvector to signs. -/
noncomputable def spectralLabels (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Fin n → Bool :=
  signRound (leadingEigenvector p q G)

/-- Center, take a leading eigenvector, round to signs, and perform one weighted vote cleanup.
The known probabilities are public parameters; the hidden labels are not inputs. -/
noncomputable def recoverSpectral (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Fin n → Bool :=
  cleanup (shiftedCenteredAdjacency p q G) (spectralLabels p q G)

/-- A small centered-noise operator norm makes the leading eigenvector approximate the
normalized hidden sign vector, up to its unavoidable sign ambiguity. -/
theorem leadingEigenvector_alignment (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (g : Fin n → Bool) (hn : 0 < n) (hd : 0 < gap p q)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : 2 * r ≤ gap p q * n)
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (shiftedCenteredAdjacency p q G - gap p q •
        Matrix.vecMulVec (fun i => signVal (g i)) (fun i => signVal (g i)))‖ ≤ r) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖leadingEigenvector p q G - s • normalize (signWord g)‖ ^ 2 ≤
        8 * (r / (gap p q * n)) ^ 2 := by
  have herr (y : EuclideanSpace ℝ (Fin n)) :
      ‖(shiftedCenteredAdjacency p q G).toEuclideanLin y -
          ((gap p q * n) * inner ℝ (normalize (signWord g)) y) •
            normalize (signWord g)‖ ≤ r * ‖y‖ := by
    have hsignal := signWord_rankOne_apply g (gap p q) y
    simp only [Fintype.card_fin] at hsignal
    rw [← hsignal]
    change ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (shiftedCenteredAdjacency p q G) y -
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (gap p q • Matrix.vecMulVec (fun i => signVal (g i))
          (fun i => signVal (g i))) y‖ ≤ _
    rw [← sub_apply, ← map_sub]
    exact (ContinuousLinearMap.le_opNorm _ y).trans
      (mul_le_mul_of_nonneg_right hnoise (norm_nonneg y))
  have h := (shifted_isSymmetric p q G).exists_sign_first_eigenvector_sub_sq_le_of_rank_one
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) hn
    (norm_normalize (norm_pos_iff.mp (show 0 < ‖signWord g‖ by
      rw [norm_signWord, Fintype.card_fin]
      exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))))
    (mul_pos hd (Nat.cast_pos.mpr hn)) hr hsmall herr
  simpa only [leadingEigenvector, dite_eq_left hn] using h

/-- The rounded spectral labels make at most `8 n (r/(d n))²` errors relative to one of the
two orientations of the hidden labels. -/
theorem spectralLabels_errors (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (g : Fin n → Bool) (hn : 0 < n) (hd : 0 < gap p q)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : 2 * r ≤ gap p q * n)
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (shiftedCenteredAdjacency p q G - gap p q •
        Matrix.vecMulVec (fun i => signVal (g i)) (fun i => signVal (g i)))‖ ≤ r) :
    ∃ g' : Fin n → Bool, (g' = g ∨ g' = fun i => !g i) ∧
      (hammingDist (spectralLabels p q G) g' : ℝ) ≤
        8 * n * (r / (gap p q * n)) ^ 2 := by
  obtain ⟨s, hs, hdist⟩ := leadingEigenvector_alignment p q G g hn hd hr hsmall hnoise
  have hround (g' : Fin n → Bool)
      (hclose : ‖leadingEigenvector p q G - normalize (signWord g')‖ ^ 2 ≤
        8 * (r / (gap p q * n)) ^ 2) :
      (hammingDist (spectralLabels p q G) g' : ℝ) ≤
        8 * n * (r / (gap p q * n)) ^ 2 := by
    have h := hammingDist_signRound_le_card_mul_norm_sub_sq g' (leadingEigenvector p q G)
    simp only [Fintype.card_fin] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hclose (Nat.cast_nonneg n)])
  rcases hs with rfl | rfl
  · exact ⟨g, Or.inl rfl, hround g (by simpa using hdist)⟩
  · exact ⟨fun i => !g i, Or.inr rfl, hround _ (by simpa using hdist)⟩

/-- Deterministic correctness under a centered-noise bound and a robust true-label margin.
The approximate labels and cleanup votes may use the same graph. -/
theorem recoverSpectral_eq_or_not_of_opNorm_le (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (g : Fin n → Bool) (hn : 0 < n) (hd : 0 < gap p q)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : 2 * r ≤ gap p q * n)
    (hnoise : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (shiftedCenteredAdjacency p q G - gap p q •
        Matrix.vecMulVec (fun i => signVal (g i)) (fun i => signVal (g i)))‖ ≤ r)
    (hmargin : ∀ i, 16 * n * (r / (gap p q * n)) ^ 2 <
      signVal (g i) * ∑ j, shiftedCenteredAdjacency p q G i j * signVal (g j)) :
    recoverSpectral p q G = g ∨ recoverSpectral p q G = fun i => !g i := by
  obtain ⟨g', hg', herr⟩ := spectralLabels_errors p q G g hn hd hr hsmall hnoise
  have hmargin' (i : Fin n) : 2 * (hammingDist (spectralLabels p q G) g' : ℝ) <
      signVal (g' i) * ∑ j, shiftedCenteredAdjacency p q G i j * signVal (g' j) := by
    have he : 2 * (hammingDist (spectralLabels p q G) g' : ℝ) <
        signVal (g i) * ∑ j, shiftedCenteredAdjacency p q G i j * signVal (g j) := by
      nlinarith only [herr, hmargin i]
    rcases hg' with rfl | rfl
    · exact he
    · simpa only [signVal_not, mul_neg, sum_neg_distrib, neg_mul, neg_neg] using he
  have hcorrect : recoverSpectral p q G = g' :=
    cleanup_eq_of_margin (abs_shiftedCenteredAdjacency_le_one p q G)
      (by simpa only [mul_one] using hmargin')
  rcases hg' with rfl | rfl
  · exact Or.inl hcorrect
  · exact Or.inr hcorrect

end Cslib.Algorithms.CommunityDetection

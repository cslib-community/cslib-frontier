/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate (Mathlib, graph adjacency spectrum)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# A radius bound for the ordered adjacency spectrum

Every eigenvalue of the ordinary adjacency matrix of a simple graph on `Fin n` has magnitude
at most `n`. The proof bounds the Euclidean operator norm using the absolute row and column
sums, then applies the bound to a unit vector of Mathlib's ordered orthonormal eigenbasis.

## Main results

* `SimpleGraph.abs_adjMatrix_eigenvalues_le`: a uniform radius bound for the decreasingly
  ordered real adjacency eigenvalues.
-/

public section

namespace SimpleGraph

open Finset Matrix

/-- Every ordered eigenvalue of a simple graph's adjacency matrix has magnitude at most
its number of vertices. This radius bound also covers dimensions zero and one. -/
theorem abs_adjMatrix_eigenvalues_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : Fin n) :
    |(Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)).eigenvalues
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) i| ≤ n := by
  have hentry (j l : Fin n) : |G.adjMatrix ℝ j l| ≤ 1 := by
    by_cases h : G.Adj j l <;> simp [h]
  have hrow (j : Fin n) : ∑ l, |G.adjMatrix ℝ j l| ≤ (n : ℝ) :=
    (sum_le_sum fun l _ => hentry j l).trans_eq (by simp)
  have hcol (l : Fin n) : ∑ j, |G.adjMatrix ℝ j l| ≤ (n : ℝ) :=
    (sum_le_sum fun j _ => hentry j l).trans_eq (by simp)
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (G.adjMatrix ℝ)‖ ≤ n := by
    simpa only [Real.sqrt_mul_self (Nat.cast_nonneg n)] using
      Matrix.opNorm_toEuclideanCLM_le_sqrt (G.adjMatrix ℝ)
        (Nat.cast_nonneg n) (Nat.cast_nonneg n) hrow hcol
  let T := (G.adjMatrix ℝ).toEuclideanLin
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_adjMatrix ℝ)
  let hn := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)
  let v := hT.eigenvectorBasis hn i
  have hv : ‖v‖ = 1 := (hT.eigenvectorBasis hn).norm_eq_one i
  have heig : T v = hT.eigenvalues hn i • v := hT.apply_eigenvectorBasis hn i
  have hbound := ContinuousLinearMap.le_opNorm
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (G.adjMatrix ℝ)) v
  change ‖T v‖ ≤ _ * ‖v‖ at hbound
  rw [heig, norm_smul, hv, Real.norm_eq_abs, mul_one, mul_one] at hbound
  exact hbound.trans hnorm

end SimpleGraph

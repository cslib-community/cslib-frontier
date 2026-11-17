/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.IntegerPower.Approximation
public import CslibFrontier.Algorithms.PlantedClique.Algorithm
public import CslibFrontier.Algorithms.PlantedClique.Indicator
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Deterministic correctness of spectral planted-clique recovery

A signed adjacency matrix within `k / 16` in Euclidean operator norm of the clique indicator
outer product gives a candidate set missing at most `k / 16` clique vertices. The degree
cleanup theorem then recovers the clique exactly if every outside vertex has at most `5 k / 8`
neighbors in it. Both hypotheses are discharged by the random-graph estimates in `Final`.

The proof applies to the executable integer algorithm. Its normalization and spectral argument
take place over `ℝ`, and the integer-to-real power-column bridge connects them to the computation.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix IntegerPower
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A small rank-one perturbation makes the integer power search and coordinate rounding miss
at most one sixteenth of the signal support. -/
theorem approximateSet_overlap (M : Matrix (Fin n) (Fin n) ℤ) (S : Finset (Fin n))
    (hS : S.Nonempty) (hM : (M.map (Int.castRingHom ℝ)).IsHermitian)
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      (M.map (Int.castRingHom ℝ) - cliqueSignal S)‖ ≤ (S.card : ℝ) / 16) :
    16 * (S \ approximateSet M S.card).card ≤ S.card := by
  let A := M.map (Int.castRingHom ℝ)
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  let u := unitIndicator S
  have hu : ‖u‖ = 1 := norm_unitIndicator hS
  have hk : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hresidual (y : EuclideanSpace ℝ (Fin n)) :
      ‖T y - ((S.card : ℝ) * inner ℝ u y) • u‖ ≤ (S.card : ℝ) / 16 * ‖y‖ := by
    rw [← cliqueSignal_apply hS y]
    have heq : T y - (cliqueSignal S).toEuclideanLin y =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (A - cliqueSignal S) y := by
      rw [map_sub]
      rfl
    rw [heq]
    exact (ContinuousLinearMap.le_opNorm _ y).trans
      (mul_le_mul_of_nonneg_right hnoise (norm_nonneg y))
  have hsignal : ‖T u - (S.card : ℝ) • u‖ ≤ (S.card : ℝ) / 16 := by
    have hr := hresidual u
    simpa only [real_inner_self_eq_norm_sq, hu, one_pow, mul_one] using hr
  have hgain := LinearMap.half_sq_le_norm_apply_sq (T := T.toLinearMap) hu hk hsignal
  obtain ⟨s, hs, hclose⟩ := recoveredVector_alignment M hS.card_pos hM hu
    (by positivity) hgain hresidual
  have hratio : (S.card : ℝ) / 16 / (S.card : ℝ) = 1 / 16 := by
    field_simp [hk.ne']
  rw [hratio] at hclose
  norm_num at hclose
  let z := WithLp.toLp 2 (fun i => (recoveredVector M S.card i : ℝ))
  apply sixteen_mul_card_sdiff_le_of_signed_norm_sub_sq_le hS
    (card_approximateSet M (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)).symm
    hs ?_ hclose
  intro i hi j hj
  have hweights := natAbs_le_of_notMem_approximateSet M S.card hi hj
  have hcast : |(recoveredVector M S.card i : ℝ)| ≤
      |(recoveredVector M S.card j : ℝ)| := by
    have hi' : |recoveredVector M S.card i| ≤ |recoveredVector M S.card j| := by
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
      exact_mod_cast hweights
    exact_mod_cast hi'
  change |‖z‖⁻¹ * z i| ≤ |‖z‖⁻¹ * z j|
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hcast (abs_nonneg _)

/-- The real signed adjacency matrix is symmetric. -/
theorem isHermitian_signedAdjacency (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((signedAdjacency G).map (Int.castRingHom ℝ)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [signedAdjacency, Matrix.map_apply, eq_comm, G.adj_comm]

/-- Complete deterministic recovery: a spectral perturbation bound and outside-degree bounds
imply that the executable algorithm returns exactly the planted clique. -/
theorem recover_eq_of_opNorm_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hk : 6 ≤ S.card) (hclique : G.IsClique (S : Set (Fin n)))
    (hnoise : ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((signedAdjacency G).map (Int.castRingHom ℝ) - cliqueSignal S)‖ ≤ (S.card : ℝ) / 16)
    (hdegree : ∀ v ∉ S, 8 * (S.filter (G.Adj v)).card ≤ 5 * S.card) :
    recover G S.card = S := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  exact G.recoverCliqueByDegree_eq_of_overlap rfl
    (card_approximateSet _ (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)) hclique
    (approximateSet_overlap _ S hS (isHermitian_signedAdjacency G) hnoise) hdegree hk

end Cslib.Algorithms.PlantedClique

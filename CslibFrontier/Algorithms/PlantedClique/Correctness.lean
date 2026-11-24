/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.PowerSearch
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

open Finset Matrix
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
  have hsearch := growingColumn?_isSome_of_large_direction M hS.card_pos hM hu hgain
  obtain ⟨c, _, hw, hpositive, hgrowth⟩ := recoveredVector_spec M S.card hsearch
  let y := (T.toLinearMap ^ c.steps) (EuclideanSpace.basisFun (Fin n) ℝ c.seed)
  let z := (T.toLinearMap ^ (c.steps + 1)) (EuclideanSpace.basisFun (Fin n) ℝ c.seed)
  have hzT : z = T y := by
    dsimp only [z, y]
    rw [pow_succ']
    rfl
  have hznorm : ‖z‖ ^ 2 =
      ((dotProduct (recoveredVector M S.card) (recoveredVector M S.card) : ℤ) : ℝ) := by
    rw [hw]
    exact norm_sq_powerVector M (c.steps + 1) c.seed
  have hz : z ≠ 0 := by
    have hp : (0 : ℝ) < ‖z‖ ^ 2 := by rw [hznorm]; exact_mod_cast hpositive
    intro hz
    simp [hz] at hp
  have hgrowth' : (S.card : ℝ) ^ 2 * ‖y‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
    rw [hznorm]
    dsimp only [y, T, A]
    rw [norm_sq_powerVector]
    exact_mod_cast hgrowth
  obtain ⟨s, hs, hclose⟩ := exists_sign_normalize_sub_sq_le_of_growth hu hz hk
    (by rw [hzT]; exact hresidual y) hgrowth'
  apply sixteen_mul_card_sdiff_le_of_signed_norm_sub_sq_le hS
    (card_approximateSet M (by simpa only [Fintype.card_fin] using Finset.card_le_univ S)).symm
    hs ?_ hclose
  intro i hi j hj
  have hwcast : WithLp.toLp 2 (fun i => (recoveredVector M S.card i : ℝ)) = z := by
    rw [hw]
    exact toLp_powerVector M (c.steps + 1) c.seed
  have hweights := natAbs_le_of_notMem_approximateSet M S.card hi hj
  have hcast : |(recoveredVector M S.card i : ℝ)| ≤
      |(recoveredVector M S.card j : ℝ)| := by
    have hi' : |recoveredVector M S.card i| ≤ |recoveredVector M S.card j| := by
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
      exact_mod_cast hweights
    exact_mod_cast hi'
  change |‖z‖⁻¹ * z i| ≤ |‖z‖⁻¹ * z j|
  rw [abs_mul, abs_mul, ← hwcast]
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

/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Algorithm
public import CslibFrontier.Foundations.Analysis.InnerProductSpace.RankOnePerturbation
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correctness of the integer power search

The integer growth test agrees exactly with squared Euclidean norms after casting to the reals.
The finite-dimensional power-growth theorem therefore guarantees that `growingColumn?` succeeds
on a symmetric matrix with a sufficiently large signal direction. The selected vector also
inherits the rank-one approximation estimate.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix

variable {n : ℕ}

/-- Casting an integer power column agrees with applying the corresponding real linear operator
power to a standard-basis vector. -/
theorem toLp_powerVector (M : Matrix (Fin n) (Fin n) ℤ) (s : ℕ) (i : Fin n) :
    WithLp.toLp 2 (fun j => (powerVector M s i j : ℝ)) =
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ))).toLinearMap ^ s)
        (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [← ContinuousLinearMap.toLinearMap_pow, ← map_pow]
  rw [← Matrix.map_pow]
  apply (WithLp.ext_iff 2).mpr
  simp only [ContinuousLinearMap.coe_coe,
    Matrix.ofLp_toEuclideanCLM, EuclideanSpace.basisFun_apply, PiLp.ofLp_single,
    Matrix.mulVec_single_one, powerVector_apply, Int.coe_castRingHom]
  rfl

/-- The squared real Euclidean norm of a power column is its integer squared norm cast to `ℝ`. -/
theorem norm_sq_powerVector (M : Matrix (Fin n) (Fin n) ℤ) (s : ℕ) (i : Fin n) :
    ‖((Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ))).toLinearMap ^ s)
      (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2 =
      ((dotProduct (powerVector M s i) (powerVector M s i) : ℤ) : ℝ) := by
  rw [← toLp_powerVector, EuclideanSpace.real_norm_sq_eq]
  simp only [dotProduct, Int.cast_sum, Int.cast_mul, pow_two]

/-- A large unit direction in a symmetric integer matrix makes the finite growth search succeed. -/
theorem growingColumn?_isSome_of_large_direction (M : Matrix (Fin n) (Fin n) ℤ) {k : ℕ}
    (hk : 0 < k) (hM : (M.map (Int.castRingHom ℝ)).IsHermitian)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1)
    (hgain : 2 * ((k : ℝ) ^ 2 / 4) ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ)) u‖ ^ 2) :
    (growingColumn? M k).isSome := by
  have hsymm :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ))).toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hM
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨i, s, hs, hnonzero, hgrowth⟩ := hsymm.exists_power_growth
    (EuclideanSpace.basisFun (Fin n) ℝ) hu (by positivity : 0 < (k : ℝ) ^ 2 / 4) hgain
  apply growingColumn?_isSome
  refine ⟨⟨s, i⟩, by simpa only [Fintype.card_fin] using hs, ?_⟩
  have hpositive : (0 : ℝ) < (dotProduct (powerVector M (s + 1) i)
      (powerVector M (s + 1) i) : ℤ) := by
    rw [← norm_sq_powerVector]
    exact sq_pos_of_pos (norm_pos_iff.mpr hnonzero)
  rw [norm_sq_powerVector, norm_sq_powerVector] at hgrowth
  have hint : (k : ℤ) ^ 2 * dotProduct (powerVector M s i) (powerVector M s i) ≤
      4 * dotProduct (powerVector M (s + 1) i) (powerVector M (s + 1) i) := by
    have hreal : (k : ℝ) ^ 2 * (dotProduct (powerVector M s i) (powerVector M s i) : ℤ) ≤
        4 * (dotProduct (powerVector M (s + 1) i) (powerVector M (s + 1) i) : ℤ) := by
      linarith
    exact_mod_cast hreal
  exact decide_eq_true ⟨by exact_mod_cast hpositive, hint⟩

/-- A successful search returns a nonzero vector with the stated integer growth bound. -/
theorem recoveredVector_spec (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ)
    (h : (growingColumn? M k).isSome) :
    ∃ c : PowerColumn n, c.steps < n + 1 ∧
      recoveredVector M k = powerVector M (c.steps + 1) c.seed ∧
      0 < dotProduct (recoveredVector M k) (recoveredVector M k) ∧
      (k : ℤ) ^ 2 * dotProduct (powerVector M c.steps c.seed)
        (powerVector M c.steps c.seed) ≤
        4 * dotProduct (recoveredVector M k) (recoveredVector M k) := by
  cases hc : growingColumn? M k with
  | none => simp [hc] at h
  | some c =>
    obtain ⟨hs, htest⟩ := growingColumn?_spec M k hc
    have hg := of_decide_eq_true htest
    refine ⟨c, hs, ?_, ?_, ?_⟩
    · simp [recoveredVector, hc]
    · simpa only [recoveredVector, hc] using hg.1
    · simpa only [recoveredVector, hc] using hg.2

end Cslib.Algorithms.PlantedClique

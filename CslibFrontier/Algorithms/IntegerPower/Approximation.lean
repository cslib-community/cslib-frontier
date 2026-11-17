/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.IntegerPower.Search
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Rank-one approximation by the exact integer power search

When a symmetric integer matrix has a sufficiently growing unit direction and a uniformly small
rank-one residual, the vector returned by the finite search approximates that direction up to
sign. The search and its growth test remain integer computations; normalization appears only in
the correctness statement. The error is quantitative in the ratio of the residual to the growth
threshold, allowing different rounding and cleanup procedures to use the same search analysis.
-/

public section

namespace Cslib.Algorithms.IntegerPower

open Matrix NormedSpace
open scoped RealInnerProductSpace

/-- A successful large-direction search with rank-one residual `r` returns a vector whose
normalization is within squared distance `8 (r/k)²` of the signal direction, up to sign. -/
theorem recoveredVector_alignment {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) {k : ℕ}
    (hk : 0 < k) (hM : (M.map (Int.castRingHom ℝ)).IsHermitian)
    {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ = 1) {a r : ℝ} (hr : 0 ≤ r)
    (hgain : 2 * ((k : ℝ) ^ 2 / 4) ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ)) v‖ ^ 2)
    (hresidual : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ)) y -
          (a * inner ℝ v y) • v‖ ≤ r * ‖y‖) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖normalize (WithLp.toLp 2 (fun i => (recoveredVector M k i : ℝ))) - s • v‖ ^ 2 ≤
        8 * (r / k) ^ 2 := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (M.map (Int.castRingHom ℝ))
  have hsearch := growingColumn?_isSome_of_large_direction M hk hM hv hgain
  obtain ⟨c, _, hw, hpositive, hgrowth⟩ := recoveredVector_spec M k hsearch
  let y := (T.toLinearMap ^ c.steps) (EuclideanSpace.basisFun (Fin n) ℝ c.seed)
  let z := (T.toLinearMap ^ (c.steps + 1)) (EuclideanSpace.basisFun (Fin n) ℝ c.seed)
  have hzT : z = T y := by
    dsimp only [z, y]
    rw [pow_succ']
    rfl
  have hznorm : ‖z‖ ^ 2 =
      ((dotProduct (recoveredVector M k) (recoveredVector M k) : ℤ) : ℝ) := by
    rw [hw]
    exact norm_sq_powerVector M (c.steps + 1) c.seed
  have hz : z ≠ 0 := by
    have hp : (0 : ℝ) < ‖z‖ ^ 2 := by rw [hznorm]; exact_mod_cast hpositive
    intro hz
    simp [hz] at hp
  have hgrowth' : (k : ℝ) ^ 2 * ‖y‖ ^ 2 ≤ 4 * ‖z‖ ^ 2 := by
    rw [hznorm]
    dsimp only [y, T]
    rw [norm_sq_powerVector]
    exact_mod_cast hgrowth
  have hwcast : WithLp.toLp 2 (fun i => (recoveredVector M k i : ℝ)) = z := by
    rw [hw]
    exact toLp_powerVector M (c.steps + 1) c.seed
  rw [hwcast, NormedSpace.normalize]
  exact exists_sign_normalize_sub_sq_le_of_growth hv hz (Nat.cast_pos.mpr hk) hr
    (by rw [hzT]; exact hresidual y) hgrowth'

end Cslib.Algorithms.IntegerPower

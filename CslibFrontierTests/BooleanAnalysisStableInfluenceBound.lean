/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.StableInfluenceBound
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Stable influences of the conjunction of two bits

Read as signs, the conjunction of two bits has influence `1 / 2` at each coordinate and
`ρ`-stable influence `(1 + ρ) / 4`. Corollary 9.25 bounds the latter by `(1 / 2) ^ (2 / (1 + ρ))`:
at `ρ = 0` the bound `1 / 4` is attained, and at `ρ = 1 / 3` it reads `1 / 3 ≤ (1 / 2) ^ (3 / 2)`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisStableInfluenceBound

open Cslib Cslib.BitString Finset

/-- The conjunction of two bits. -/
def and₂ (x : Fin 2 → Bool) : Bool :=
  x 0 && x 1

/-- Each coordinate has influence `1 / 2` on the conjunction. -/
theorem influence_and₂ (i : Fin 2) : influence i (fun x => signVal (and₂ x)) = 1 / 2 := by
  rw [influence_signVal]
  simp only [Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  fin_cases i <;> simp [and₂, Function.update]

/-- The `ρ`-stable influence of each coordinate on the conjunction is `(1 + ρ) / 4`. -/
theorem stableInfluence_and₂ (ρ : ℝ) (i : Fin 2) :
    stableInfluence ρ i (fun x => signVal (and₂ x)) = (1 + ρ) / 4 := by
  have h0 : ({S | (0 : Fin 2) ∈ S} : Finset (Finset (Fin 2))) = {{0}, {0, 1}} := by decide
  have h1 : ({S | (1 : Fin 2) ∈ S} : Finset (Finset (Fin 2))) = {{1}, {0, 1}} := by decide
  rw [stableInfluence_eq_sum]
  fin_cases i
  · rw [Fin.zero_eta, h0, sum_pair (by decide)]
    simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
    simp [chi, and₂]
    ring
  · rw [Fin.mk_one, h1, sum_pair (by decide)]
    simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
    simp [chi, and₂]
    ring

-- The derivative of the conjunction in either bit has noise stability `(1 + ρ) / 4`.
example (ρ : ℝ) (i : Fin 2) :
    noiseStability ρ (derivative i fun x => signVal (and₂ x)) = (1 + ρ) / 4 := by
  rw [← stableInfluence_eq_noiseStability_derivative, stableInfluence_and₂]

/-- Corollary 9.25 at `ρ = 1 / 3` is Corollary 9.12, `Infᵢ^{(1/3)}[F] ≤ Infᵢ[F] ^ (3/2)`, here for
the first bit of the conjunction. -/
theorem stableInfluence_one_third_and₂_le :
    stableInfluence (1 / 3) 0 (fun x => signVal (and₂ x)) ≤
      influence 0 (fun x => signVal (and₂ x)) ^ (3 / 2 : ℝ) := by
  have h := stableInfluence_signVal_le_influence_rpow (ρ := 1 / 3) (by norm_num) (by norm_num)
    and₂ 0
  rwa [show (2 : ℝ) / (1 + 1 / 3) = 3 / 2 by norm_num] at h

-- Corollary 9.12 for the conjunction, evaluated: `1 / 3 ≤ (1 / 2) ^ (3 / 2)`.
example : (1 / 3 : ℝ) ≤ (1 / 2) ^ (3 / 2 : ℝ) := by
  have h := stableInfluence_one_third_and₂_le
  rwa [stableInfluence_and₂, influence_and₂, show (1 + 1 / 3 : ℝ) / 4 = 1 / 3 by norm_num] at h

-- At `ρ = 0` the conjunction attains Corollary 9.25: both sides are `1 / 4`.
example (i : Fin 2) :
    stableInfluence 0 i (fun x => signVal (and₂ x)) =
      influence i (fun x => signVal (and₂ x)) ^ (2 / (1 + 0) : ℝ) := by
  rw [stableInfluence_and₂, influence_and₂]
  norm_num

end CslibFrontierTests.BooleanAnalysisStableInfluenceBound

/-
Copyright (c) 2026 Vincent Liew, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.CondorcetLimits

/-! # Equal degree-one coefficients: majority and a dictator

Majority of an odd number of voters has all degree-one coefficients equal, so Proposition 2.58 and
Theorem 2.57 apply to it; for majority of three voters the exact bound `3 W^1 ≤ E[|x₁ + x₂ + x₃|]²`
holds with `W^1 = 3/4`. A dictator on two voters has coefficients `1` and `0`, so it is excluded:
its degree-one weight is `1`, above `2/π`, and it always gives a Condorcet winner.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisCondorcetLimits

open Cslib Cslib.BitString Finset Filter
open scoped BigOperators

/-- Majority of `2 m + 1` voters has all degree-one coefficients equal. -/
theorem majority_fourierCoeff_singleton_eq (m : ℕ) (i j : Fin (2 * m + 1)) :
    fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) {i} =
      fourierCoeff (fun x => signVal (majority (2 * m + 1) x)) {j} := by
  rw [fourierCoeff_signVal_majority_singleton, fourierCoeff_signVal_majority_singleton]

-- The exact bound for majority of three voters.
example : (3 : ℕ) * levelWeight 1 (fun x => signVal (majority 3 x)) ≤
    (𝔼 x : Fin 3 → Bool, |∑ i, signVal (x i)|) ^ 2 :=
  card_mul_levelWeight_one_le_of_fourierCoeff_singleton_eq (majority 3)
    (majority_fourierCoeff_singleton_eq 1)

/-- The dictator on two voters has unequal degree-one coefficients. -/
theorem dictator_fourierCoeff_singleton_ne :
    fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) {0} ≠
      fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) {1} := by
  have h (S : Finset (Fin 2)) := fourierCoeff_signVal_xor false 0 S
  simp only [Bool.false_xor, signVal_false] at h
  rw [h, h]
  simp

/-- The dictator on two voters has degree-one weight `1`. -/
theorem levelWeight_one_dictator :
    levelWeight 1 (fun x : Fin 2 → Bool => signVal (x 0)) = 1 := by
  have h (S : Finset (Fin 2)) := fourierCoeff_signVal_xor false 0 S
  simp only [Bool.false_xor, signVal_false] at h
  simp [levelWeight_one, h]

end CslibFrontierTests.BooleanAnalysisCondorcetLimits

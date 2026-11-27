/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.CoalitionalInfluence
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Tests for coalitional influence

The conjunction of two voters, the threshold function `Th²₂`, is true on one of the four inputs,
and each voter is pivotal on half of them. So voter `0` has directed influence `1 / 4` toward
either outcome (Exercise 9.25(a)), which agrees with the unanimous-vote formula for monotone
functions (Exercise 9.25(d)); the two add up to its coalitional influence `1 / 2`
(Exercise 9.25(c)). Both voters together have directed influence `3 / 4` toward `true`, more than
voter `0` alone. Every nonempty coalition controls the parity (Exercise 9.25(e)), so its two
directed influences are probabilities adding up to one (Exercise 9.25(b)); unfolding the definition,
voter `0` has directed influence `1 / 2` toward each value of the parity of two voters. -/

public section

namespace CslibFrontierTests.BooleanAnalysisCoalitionalInfluence

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- Voter `0` is pivotal for the conjunction of two voters on half of the inputs. -/
theorem influence_threshold_two_two :
    influence 0 (fun x => signVal (threshold 2 2 x)) = 1 / 2 := by
  have h : #{x : Fin 2 → Bool | threshold 2 2 (Function.update x 0 !x 0) ≠ threshold 2 2 x} =
      2 := by decide
  rw [influence_signVal_eq_dens, dens]
  simp only [derivative_signVal_ne_zero_iff, h, Fintype.card_pi, Fintype.card_bool, prod_const,
    card_univ, Fintype.card_fin]
  norm_num

/-- The conjunction of two voters is `true` on one of the four inputs. -/
theorem expect_threshold_two_two_eq_true :
    𝔼 x : Fin 2 → Bool, (if threshold 2 2 x = true then (1 : ℝ) else 0) = 1 / 4 := by
  have h : #{x : Fin 2 → Bool | threshold 2 2 x = true} = 1 := by decide
  rw [Fintype.expect_boole, dens, h]
  simp

/-- Exercise 9.25(a): voter `0` has directed influence `1 / 4` toward `true`. -/
theorem coalitionInfluenceToward_true_singleton_threshold_two_two :
    coalitionInfluenceToward true {0} (threshold 2 2) = 1 / 4 := by
  rw [coalitionInfluenceToward_singleton, influence_threshold_two_two]
  norm_num

-- Exercise 9.25(d) computes the same value: voting `true`, voter `0` makes the conjunction `true`
-- on half of the inputs, against a quarter without it.
example : coalitionInfluenceToward true {0} (threshold 2 2) = 1 / 4 := by
  have h : #{z : Fin 2 → Bool |
      threshold 2 2 (({0} : Finset (Fin 2)).piecewise (fun _ => true) z) = true} = 2 := by decide
  rw [coalitionInfluenceToward_eq_of_monotone (monotone_threshold 2), Fintype.expect_boole, dens,
    h, expect_threshold_two_two_eq_true]
  norm_num

-- Exercises 9.25(a) and (c): voter `0` has influence `1 / 4` toward each outcome, so its
-- coalitional influence is `1 / 2`.
example : coalitionInfluence (Probability.PMF.uniformOfFintype (Fin 2 → Bool)) {0}
    (threshold 2 2) = 1 / 2 := by
  rw [coalitionInfluence_eq_add, coalitionInfluenceToward_singleton,
    coalitionInfluenceToward_singleton, influence_threshold_two_two]
  norm_num

-- Both voters, voting `true`, make the conjunction `true` always, so their directed influence
-- toward `true` is `3 / 4`, at least the `1 / 4` of voter `0` alone.
example : coalitionInfluenceToward true {0} (threshold 2 2) ≤
    coalitionInfluenceToward true univ (threshold 2 2) ∧
      coalitionInfluenceToward true univ (threshold 2 2) = 3 / 4 := by
  refine ⟨coalitionInfluenceToward_mono true (subset_univ _) _, ?_⟩
  have h : ∀ z : Fin 2 → Bool, threshold 2 2 (univ.piecewise (fun _ => true) z) = true := by
    decide
  rw [coalitionInfluenceToward_eq_of_monotone (monotone_threshold 2)]
  simp only [h, ↓reduceIte, Fintype.expect_const, expect_threshold_two_two_eq_true]
  norm_num

-- Exercise 9.25(e): voters `0` and `2` control the parity of four voters.
example : coalitionInfluence (Probability.PMF.uniformOfFintype (Fin 4 → Bool)) {0, 2}
    (parityOn univ) = 1 :=
  coalitionInfluence_parityOn_univ ⟨0, by simp⟩

/-- Unfolding the definition: whatever the other voter does, voter `0` can make the parity of two
voters `true`, which it is on half of the inputs, so voter `0` has directed influence `1 / 2`
toward `true`. -/
theorem coalitionInfluenceToward_true_singleton_parityOn :
    coalitionInfluenceToward true {0} (parityOn (univ : Finset (Fin 2))) = 1 / 2 := by
  have h1 : ∀ z : Fin 2 → Bool,
      ∃ y, parityOn univ (({0} : Finset (Fin 2)).piecewise y z) = true := by decide
  have h2 : #{x : Fin 2 → Bool | parityOn univ x = true} = 2 := by decide
  rw [coalitionInfluenceToward]
  simp only [h1, ↓reduceIte, Fintype.expect_const, Fintype.expect_boole, dens, h2]
  norm_num

-- Exercises 9.25(b), (c) and (e): voter `0`'s directed influences on the parity of two voters
-- lie in `[0, 1]` and add up to one, so the influence toward `false` is also `1 / 2`.
example (b : Bool) :
    0 ≤ coalitionInfluenceToward b {0} (parityOn (univ : Finset (Fin 2))) ∧
      coalitionInfluenceToward b {0} (parityOn (univ : Finset (Fin 2))) ≤ 1 ∧
      coalitionInfluenceToward false {0} (parityOn (univ : Finset (Fin 2))) = 1 / 2 := by
  refine ⟨coalitionInfluenceToward_nonneg b {0} _, coalitionInfluenceToward_le_one b {0} _, ?_⟩
  have h := (coalitionInfluence_eq_add {0} (parityOn (univ : Finset (Fin 2)))).symm.trans
    (coalitionInfluence_parityOn_univ ⟨0, by simp⟩)
  rw [coalitionInfluenceToward_true_singleton_parityOn] at h
  linarith

end CslibFrontierTests.BooleanAnalysisCoalitionalInfluence

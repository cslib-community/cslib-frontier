/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.Bribery
public import CslibFrontier.Foundations.BooleanAnalysis.Decomposition
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.Variance
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Tests for bribing monotone elections

The elections are the conjunction of two voters, the threshold function `Th²₂`, and the majority
of three voters. Read as signs, the conjunction has mean `1 / 2` and variance `3 / 4`, and fixing
voter `0` to `false` moves its mean to `1`, so its coefficient on `{0}` is `1 / 2`. The majority of
three voters has mean `0`. Each bribing theorem is applied to one of them; since no bribe leaves
the mean where it was, the bribed set it provides is nonempty. -/

public section

namespace CslibFrontierTests.BooleanAnalysisBribery

open Cslib Cslib.BitString Finset Real
open scoped BigOperators

/-- The conjunction of two voters, read as signs, has mean `1 / 2`: it is `false`, of sign `1`, on
three of the four inputs. -/
theorem expect_signVal_threshold_two_two : 𝔼 x, signVal (threshold 2 2 x) = 1 / 2 := by
  have h : hammingDist (threshold 2 2) (fun _ => false) = 1 := by decide
  rw [expect_signVal, h, Fintype.card_fin]
  norm_num

/-- The conjunction of two voters, read as signs, has variance `1 - (1 / 2) ^ 2 = 3 / 4`. -/
theorem variance_threshold_two_two :
    𝔼 x, (signVal (threshold 2 2 x) - 𝔼 y, signVal (threshold 2 2 y)) ^ 2 = 3 / 4 := by
  rw [expect_sub_expect_sq_signVal, expect_signVal_threshold_two_two]
  norm_num

/-- The majority of three voters, read as signs, has mean `0`. -/
theorem expect_signVal_majority_three : 𝔼 x, signVal (majority 3 x) = 0 := by
  have h : hammingDist (majority 3) (fun _ => false) = 4 := by decide
  rw [expect_signVal, h, Fintype.card_fin]
  norm_num

/-- Bribing nobody leaves the mean unchanged. -/
theorem expect_signVal_piecewise_empty {n : ℕ} (f : (Fin n → Bool) → Bool) (b : Bool) :
    𝔼 x, signVal (f ((∅ : Finset (Fin n)).piecewise (fun _ => b) x)) = 𝔼 x, signVal (f x) := by
  simp only [piecewise_empty]

-- Fixing voter `0` of the conjunction to `false` moves its mean from `1 / 2` to `1`, so its
-- coefficient on `{0}` is `1 / 2`.
example : fourierCoeff (fun x => signVal (threshold 2 2 x)) {0} = 1 / 2 := by
  have h := expect_update_false (fun x => signVal (threshold 2 2 x)) 0
  have h0 : ∀ x : Fin 2 → Bool, threshold 2 2 (Function.update x 0 false) = false := by decide
  simp only [h0, signVal_false, Fintype.expect_const, expect_signVal_threshold_two_two] at h
  linarith

-- Complementing every vote permutes the cube, so the conjunction of the complemented votes, which
-- is the negated disjunction, still has mean `1 / 2`.
example : 𝔼 x : Fin 2 → Bool, signVal (threshold 2 2 fun i => !x i) = 1 / 2 := by
  rw [Fintype.expect_comp_not fun x => signVal (threshold 2 2 x), expect_signVal_threshold_two_two]

-- One bribe raises the mean `1 / 2` of the conjunction by at least `(3 / 4) log 2 / 8`.
example : ∃ i, 1 / 2 + 3 / 4 * log 2 / 8 ≤
    𝔼 x, signVal (threshold 2 2 (({i} : Finset (Fin 2)).piecewise (fun _ => false) x)) := by
  obtain ⟨i, hi⟩ := exists_add_le_expect_signVal_piecewise_insert
    (f := threshold 2 2) (monotone_threshold 2) ∅
  rw [expect_signVal_piecewise_empty, expect_signVal_threshold_two_two, insert_empty,
    Fintype.card_fin] at hi
  exact ⟨i, le_of_eq_of_le (by norm_num) hi⟩

-- Proposition 9.27 with the book's `a = .99`, for the majority of three voters.
example : ∃ J : Finset (Fin 3), J.Nonempty ∧
    (#J : ℝ) ≤ 8 * (99 / 100) * 3 / ((1 - (99 / 100) ^ 2) * log 3) + 1 ∧
      99 / 100 ≤ 𝔼 x, signVal (majority 3 (J.piecewise (fun _ => false) x)) := by
  obtain ⟨J, hJ, hJm⟩ := exists_card_le_and_le_expect_signVal_piecewise_false
    (f := majority 3) (monotone_threshold 2) (by simp) (a := 99 / 100) (by norm_num) (by norm_num)
    (by rw [expect_signVal_majority_three]; norm_num)
  refine ⟨J, nonempty_iff_ne_empty.2 fun h => ?_, by simpa using hJ, hJm⟩
  rw [h, expect_signVal_piecewise_empty, expect_signVal_majority_three] at hJm
  norm_num at hJm

-- Proposition 9.27 bribing toward `true`, with `a = 1 / 2`, for the conjunction.
example : ∃ J : Finset (Fin 2), J.Nonempty ∧
    (#J : ℝ) ≤ 8 * (1 / 2) * 2 / ((1 - (1 / 2) ^ 2) * log 2) + 1 ∧
      𝔼 x, signVal (threshold 2 2 (J.piecewise (fun _ => true) x)) ≤ -(1 / 2) := by
  obtain ⟨J, hJ, hJm⟩ := exists_card_le_and_expect_signVal_piecewise_true_le
    (f := threshold 2 2) (monotone_threshold 2) (by simp) (a := 1 / 2) (by norm_num) (by norm_num)
    (by rw [expect_signVal_threshold_two_two])
  refine ⟨J, nonempty_iff_ne_empty.2 fun h => ?_, by simpa using hJ, hJm⟩
  rw [h, expect_signVal_piecewise_empty, expect_signVal_threshold_two_two] at hJm
  norm_num at hJm

-- Exercise 9.27(a) for the conjunction, of variance `3 / 4`, with `ε = 1 / 100`, in both
-- directions.
example : (∃ J : Finset (Fin 2), J.Nonempty ∧
      (#J : ℝ) ≤ 8 * 2 * log (2 / (1 / 100 * (3 / 4))) / log 2 + 2 ∧
        1 - 1 / 100 ≤ 𝔼 x, signVal (threshold 2 2 (J.piecewise (fun _ => false) x))) ∧
    ∃ J : Finset (Fin 2), J.Nonempty ∧
      (#J : ℝ) ≤ 8 * 2 * log (2 / (1 / 100 * (3 / 4))) / log 2 + 2 ∧
        𝔼 x, signVal (threshold 2 2 (J.piecewise (fun _ => true) x)) ≤ 1 / 100 - 1 := by
  have hV := variance_threshold_two_two.ge
  constructor
  · obtain ⟨J, hJ, hJm⟩ := exists_card_le_and_one_sub_le_expect_signVal_piecewise_false
      (f := threshold 2 2) (monotone_threshold 2) (by simp) (by norm_num) hV (ε := 1 / 100)
      (by norm_num) (by norm_num)
    refine ⟨J, nonempty_iff_ne_empty.2 fun h => ?_, by simpa using hJ, hJm⟩
    rw [h, expect_signVal_piecewise_empty, expect_signVal_threshold_two_two] at hJm
    norm_num at hJm
  · obtain ⟨J, hJ, hJm⟩ := exists_card_le_and_expect_signVal_piecewise_true_le_sub_one
      (f := threshold 2 2) (monotone_threshold 2) (by simp) (by norm_num) hV (ε := 1 / 100)
      (by norm_num) (by norm_num)
    refine ⟨J, nonempty_iff_ne_empty.2 fun h => ?_, by simpa using hJ, hJm⟩
    rw [h, expect_signVal_piecewise_empty, expect_signVal_threshold_two_two] at hJm
    norm_num at hJm

-- Exercise 9.27(b) for the conjunction with `ε = 1 / 100`: the empty coalition has no influence,
-- so the coalition is nonempty.
example : ∃ J : Finset (Fin 2), J.Nonempty ∧
    (#J : ℝ) ≤ 16 * 2 * log (2 / (1 / 100 * (3 / 4))) / log 2 + 4 ∧
      1 - 1 / 100 ≤
        coalitionInfluence (Probability.PMF.uniformOfFintype (Fin 2 → Bool)) J (threshold 2 2) := by
  obtain ⟨J, hJ, hJm⟩ := exists_card_le_and_one_sub_le_coalitionInfluence
    (f := threshold 2 2) (monotone_threshold 2) (by simp) (by norm_num)
    variance_threshold_two_two.ge (ε := 1 / 100) (by norm_num) (by norm_num)
  refine ⟨J, nonempty_iff_ne_empty.2 fun h => ?_, by simpa using hJ, hJm⟩
  rw [h, coalitionInfluence_eq_zero_of_forall_not _
    fun x hx => by simpa using isUndetermined_iff_outside.1 hx] at hJm
  norm_num at hJm

end CslibFrontierTests.BooleanAnalysisBribery

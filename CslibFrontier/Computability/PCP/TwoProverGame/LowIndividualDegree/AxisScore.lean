/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Axis-test acceptance conditional on a coordinate

The axis branch of the low individual degree test samples a point, a coordinate and a
choice of which player gets the line. The winning probability averages over exactly
these three choices. Selecting a coordinate charges the reciprocal of its sampling
probability, without changing the answer or degree checks.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Probability.PMF
open scoped BigOperators

variable {F A : Type*} {m : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Ring A] [PartialOrder A] [Algebra ℂ A]

/-- The probability of acceptance for a fixed pair of verifier questions. -/
@[expose] noncomputable def acceptScore
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (x y : Question F m) : ℝ := by
  classical
  exact ∑ a, ∑ b, if accepts d x y a b then S.prob x y a b else 0

private theorem uniform_sum_eq_expect {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∑ x, (uniformOfFintype ι x).toReal * f x) = 𝔼 x, f x := by
  simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    inv_mul_eq_div, Fintype.expect_eq_sum_div_card, sum_div]

variable [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

theorem acceptScore_le_one
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (x y : Question F m) : acceptScore S d x y ≤ 1 := by
  classical
  unfold acceptScore
  rw [← S.sum_prob x y]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  split_ifs
  · exact le_rfl
  · exact S.prob_nonneg _ _ _ _

/-- Average acceptance with the point and axis fixed and the roles chosen uniformly. -/
@[expose] noncomputable def axisScoreAt
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (u : Point F m) (i : Fin m) : ℝ :=
  let q := Question.axis (linePoints u (Pi.single i (1 : F)))
  (acceptScore S d (.point u) q + acceptScore S d q (.point u)) / 2

/-- The conditional axis score is the average over points and coordinates. -/
theorem axisScore_eq_expect (n d : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGame (F := F) n d .axis).commutingWinProb S =
      𝔼 u : Point F (n + 1), 𝔼 i : Fin (n + 1), axisScoreAt S d u i := by
  classical
  let G := branchGame (F := F) n d .axis
  let W (q : Question F (n + 1) × Question F (n + 1)) := acceptScore S d q.1 q.2
  have h : G.commutingWinProb S = ∑ q, (G.questions q).toReal * W q := by
    rw [G.commutingWinProb_eq_sum S, Fintype.sum_prod_type]
    simp only [W, acceptScore, G, branchGame_accepts]
  rw [h, show G.questions = axisQuestions n from
    (branchGame_questions (F := F) n d .axis).trans (branchQuestions_axis n),
    axisQuestions, sum_bind_mul]
  simp only [sum_bind_mul, assignLineRoles, sum_map_mul, uniform_sum_eq_expect]
  refine expect_congr rfl fun u _ => expect_congr rfl fun i _ => ?_
  rw [Fintype.expect_eq_sum_div_card, Fintype.sum_bool, Fintype.card_bool]
  simp only [axisScoreAt, W, Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  rw [add_comm]

/-- Conditioning the axis test on a particular coordinate increases its loss by at most
the number of coordinates. -/
theorem axisLossAt_le (n d : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) (i : Fin (n + 1)) :
    (𝔼 u : Point F (n + 1), (1 - axisScoreAt S d u i)) ≤
      (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) := by
  rw [axisScore_eq_expect, expect_comm univ univ]
  let f (j : Fin (n + 1)) := 𝔼 u : Point F (n + 1), (1 - axisScoreAt S d u j)
  have h0 (j : Fin (n + 1)) : 0 ≤ f j := by
    refine expect_nonneg fun u _ => sub_nonneg.mpr ?_
    unfold axisScoreAt
    linarith [acceptScore_le_one S d (.point u) (.axis (linePoints u (Pi.single j (1 : F)))),
      acceptScore_le_one S d (.axis (linePoints u (Pi.single j (1 : F)))) (.point u)]
  calc
    f i ≤ ∑ j, f j := single_le_sum (fun j _ => h0 j) (mem_univ i)
    _ = _ := by
      rw [← Fintype.card_mul_expect, Fintype.card_fin, Nat.cast_succ]
      simp only [f, expect_sub_distrib, Fintype.expect_const]

/-- The consistency score is the average when the same point is sent to both players. -/
theorem consistencyScore_eq_expect (n d : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGame (F := F) n d .consistency).commutingWinProb S =
      𝔼 u : Point F (n + 1), acceptScore S d (.point u) (.point u) := by
  classical
  let G := branchGame (F := F) n d .consistency
  let W (q : Question F (n + 1) × Question F (n + 1)) := acceptScore S d q.1 q.2
  have h : G.commutingWinProb S = ∑ q, (G.questions q).toReal * W q := by
    rw [G.commutingWinProb_eq_sum S, Fintype.sum_prod_type]
    simp only [W, acceptScore, G, branchGame_accepts]
  rw [h, show G.questions = consistencyQuestions from
    (branchGame_questions (F := F) n d .consistency).trans (branchQuestions_consistency n),
    consistencyQuestions, sum_map_mul, uniform_sum_eq_expect]

end Cslib.PCP.LowIndividualDegree

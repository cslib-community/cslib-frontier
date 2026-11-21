/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import Mathlib.Algebra.BigOperators.Expect
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Low individual degree branch scores

The axis branch of the low individual degree test samples a point, a coordinate and a
choice of which player gets the line. The winning probability averages over exactly
these three choices. Selecting a coordinate charges the reciprocal of its sampling
probability, without changing the answer or degree checks. The diagonal branch
also samples a direction inside a prefix. Its point-first rejection bound
charges for both the prefix and the choice of role.
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

/-- A pair of answer decoders agreeing on each accepted answer pair has agreement
at least the verifier acceptance score. -/
theorem acceptScore_le_decodedAgreement {B : Type*} [Fintype B] [DecidableEq B]
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (x y : Question F m) (f g : Answer F m → B)
    (hagree : ∀ a b, accepts d x y a b → f a = g b) :
    acceptScore S d x y ≤
      Cslib.Quantum.Measurement.agreement S.state ((S.alice x).map f) ((S.bob y).map g) := by
  classical
  simp only [acceptScore, Cslib.Quantum.Measurement.agreement_map_map]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  by_cases h : accepts d x y a b
  · simp only [ite_eq_left h, hagree a b h, ite_true, CommutingStrategy.prob, le_refl]
  · rw [ite_eq_right h]
    exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl

private theorem branchWinProb_eq_weighted {n : ℕ} (d : ℕ) (b : Branch)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGame (F := F) n d b).commutingWinProb S =
      ∑ q, (branchQuestions (F := F) n b q).toReal * acceptScore S d q.1 q.2 := by
  classical
  rw [TwoProverGame.commutingWinProb_eq_sum, Fintype.sum_prod_type]
  simp only [acceptScore, branchGame_questions, branchGame_accepts]

omit [Field F] [DecidableEq F] in
private theorem sum_assignLineRoles_eq (line point : Question F m)
    (w : Question F m × Question F m → ℝ) :
    ∑ q, (assignLineRoles line point q).toReal * w q = (w (point, line) + w (line, point)) / 2 := by
  rw [assignLineRoles, sum_map_mul, uniform_sum_eq_expect, Fintype.expect_eq_sum_div_card,
    Fintype.sum_bool, Fintype.card_bool]
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  rw [add_comm]

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
  rw [branchWinProb_eq_weighted, branchQuestions_axis, axisQuestions, sum_bind_mul]
  simp only [sum_bind_mul, uniform_sum_eq_expect, sum_assignLineRoles_eq, axisScoreAt]

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
  rw [branchWinProb_eq_weighted, branchQuestions_consistency, consistencyQuestions,
    sum_map_mul, uniform_sum_eq_expect]

/-- Diagonal acceptance at a fixed base point and prefix direction, averaging the two roles. -/
@[expose] noncomputable def diagonalScoreAt
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (u : Point F m) (i : Fin m) (v : Fin (i.val + 1) → F) : ℝ :=
  let q := Question.diagonal (linePoints u (prefixDirection i v))
  (acceptScore S d (.point u) q + acceptScore S d q (.point u)) / 2

/-- The diagonal acceptance probability averages over the base point, prefix and direction. -/
theorem diagonalScore_eq_expect (n d : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGame (F := F) n d .diagonal).commutingWinProb S =
      𝔼 u : Point F (n + 1), 𝔼 i : Fin (n + 1), 𝔼 v, diagonalScoreAt S d u i v := by
  rw [branchWinProb_eq_weighted, branchQuestions_diagonal, diagonalQuestions, sum_bind_mul]
  simp only [sum_bind_mul, uniform_sum_eq_expect, sum_assignLineRoles_eq, diagonalScoreAt]

/-- Conditioning the diagonal test on a prefix and the point-first role assignment
costs at most twice the number of coordinates in its rejection probability. -/
theorem diagonalPointLossAt_le (n d : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) (j : Fin (n + 1)) :
    (𝔼 u : Point F (n + 1), 𝔼 v : Fin (j.val + 1) → F,
        (1 - acceptScore S d (.point u) (.diagonal (linePoints u (prefixDirection j v))))) ≤
      2 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .diagonal).commutingWinProb S) := by
  rw [diagonalScore_eq_expect, expect_comm (ι := Point F (n + 1)) (κ := Fin (n + 1)) univ univ]
  let loss (i : Fin (n + 1)) := 𝔼 u : Point F (n + 1), 𝔼 v, (1 - diagonalScoreAt S d u i v)
  have h0 (i : Fin (n + 1)) : 0 ≤ loss i := by
    refine expect_nonneg fun u _ => expect_nonneg fun v _ => ?_
    unfold diagonalScoreAt
    linarith [acceptScore_le_one S d (.point u) (.diagonal (linePoints u (prefixDirection i v))),
      acceptScore_le_one S d (.diagonal (linePoints u (prefixDirection i v))) (.point u)]
  have hselected : loss j ≤ (n + 1 : ℝ) * (1 - 𝔼 i : Fin (n + 1),
      𝔼 u : Point F (n + 1), 𝔼 v, diagonalScoreAt S d u i v) := by
    calc
      _ ≤ ∑ i, loss i := single_le_sum (fun i _ => h0 i) (mem_univ _)
      _ = _ := by
        rw [← Fintype.card_mul_expect, Fintype.card_fin, Nat.cast_succ]
        simp only [loss, expect_sub_distrib, Fintype.expect_const]
  calc
    _ ≤ 𝔼 u : Point F (n + 1), 𝔼 v : Fin (j.val + 1) → F,
        (2 * (1 - diagonalScoreAt S d u j v)) := by
      refine expect_le_expect fun u _ => expect_le_expect fun v _ => ?_
      simp only [diagonalScoreAt]
      linarith [acceptScore_le_one S d (.diagonal (linePoints u (prefixDirection j v))) (.point u)]
    _ = 2 * loss j := by
      simp only [← mul_expect]
      rfl
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hselected (by norm_num)

end Cslib.PCP.LowIndividualDegree

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

/-- Acceptance for fixed questions and independent axis and diagonal cutoffs. -/
@[expose] noncomputable def acceptScoreAtDegrees
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d D : ℕ) (x y : Question F m) : ℝ := by
  classical
  exact ∑ a, ∑ b, if acceptsWithDiagonalCap d D x y a b then S.prob x y a b else 0

/-- The probability of acceptance for a fixed pair of verifier questions. -/
@[expose] noncomputable def acceptScore
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (x y : Question F m) : ℝ :=
  acceptScoreAtDegrees S d (m * d) x y

open scoped Classical in
theorem acceptScore_eq_sum
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (x y : Question F m) :
    acceptScore S d x y = ∑ a, ∑ b, if accepts d x y a b then S.prob x y a b else 0 := by
  classical
  rw [accepts_eq_withDiagonalCap]
  rfl

/-- A real-valued sum weighted by the uniform PMF is a finite expectation. -/
theorem uniform_sum_eq_expect {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∑ x, (uniformOfFintype ι x).toReal * f x) = 𝔼 x, f x := by
  simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    inv_mul_eq_div, Fintype.expect_eq_sum_div_card, sum_div]

variable [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]

theorem acceptScoreAtDegrees_le_one
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d D : ℕ) (x y : Question F m) : acceptScoreAtDegrees S d D x y ≤ 1 := by
  classical
  unfold acceptScoreAtDegrees
  rw [← S.sum_prob x y]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  split_ifs
  · exact le_rfl
  · exact S.prob_nonneg _ _ _ _

theorem acceptScore_le_one
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (x y : Question F m) : acceptScore S d x y ≤ 1 :=
  acceptScoreAtDegrees_le_one S d (m * d) x y

/-- A pair of answer decoders agreeing on each accepted answer pair has agreement
at least the verifier acceptance score. -/
theorem acceptScoreAtDegrees_le_decodedAgreement {B : Type*} [Fintype B] [DecidableEq B]
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d D : ℕ) (x y : Question F m) (f g : Answer F m → B)
    (hagree : ∀ a b, acceptsWithDiagonalCap d D x y a b → f a = g b) :
    acceptScoreAtDegrees S d D x y ≤
      Cslib.Quantum.Measurement.agreement S.state ((S.alice x).map f) ((S.bob y).map g) := by
  classical
  simp only [acceptScoreAtDegrees, Cslib.Quantum.Measurement.agreement_map_map]
  refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
  by_cases h : acceptsWithDiagonalCap d D x y a b
  · simp only [ite_eq_left h, hagree a b h, ite_true, CommutingStrategy.prob, le_refl]
  · rw [ite_eq_right h]
    exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl

/-- A pair of answer decoders agreeing on each accepted answer pair has agreement
at least the verifier acceptance score. -/
theorem acceptScore_le_decodedAgreement {B : Type*} [Fintype B] [DecidableEq B]
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d : ℕ) (x y : Question F m) (f g : Answer F m → B)
    (hagree : ∀ a b, accepts d x y a b → f a = g b) :
    acceptScore S d x y ≤
      Cslib.Quantum.Measurement.agreement S.state ((S.alice x).map f) ((S.bob y).map g) := by
  apply acceptScoreAtDegrees_le_decodedAgreement S d (m * d) x y f g
  simpa only [accepts_eq_withDiagonalCap] using hagree

private theorem branchWinProbAtDegrees_eq_weighted {n : ℕ} (d D : ℕ) (b : Branch)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGameWithDiagonalCap (F := F) n d D b).commutingWinProb S =
      ∑ q, (branchQuestions (F := F) n b q).toReal * acceptScoreAtDegrees S d D q.1 q.2 := by
  classical
  rw [TwoProverGame.commutingWinProb_eq_sum, Fintype.sum_prod_type]
  simp only [acceptScoreAtDegrees, branchGameWithDiagonalCap_questions,
    branchGameWithDiagonalCap_accepts]

omit [Field F] [DecidableEq F] in
private theorem sum_assignLineRoles_eq (line point : Question F m)
    (w : Question F m × Question F m → ℝ) :
    ∑ q, (assignLineRoles line point q).toReal * w q = (w (point, line) + w (line, point)) / 2 := by
  rw [assignLineRoles, sum_map_mul, uniform_sum_eq_expect, Fintype.expect_eq_sum_div_card,
    Fintype.sum_bool, Fintype.card_bool]
  simp only [Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  rw [add_comm]

/-- Average the line score over the two role assignments. -/
@[expose] noncomputable def lineScoreAtDegrees
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d D : ℕ) (u : Point F m) (line : Question F m) : ℝ :=
  (acceptScoreAtDegrees S d D (.point u) line + acceptScoreAtDegrees S d D line (.point u)) / 2

theorem lineScoreAtDegrees_le_one
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d D : ℕ) (u : Point F m) (line : Question F m) :
    lineScoreAtDegrees S d D u line ≤ 1 := by
  unfold lineScoreAtDegrees
  linarith [acceptScoreAtDegrees_le_one S d D (.point u) line,
    acceptScoreAtDegrees_le_one S d D line (.point u)]

/-- The axis score with a fixed diagonal cutoff is still the average over points and axes. -/
theorem axisScoreAtDegrees_eq_expect (n d D : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGameWithDiagonalCap (F := F) n d D .axis).commutingWinProb S =
      𝔼 u : Point F (n + 1), 𝔼 i : Fin (n + 1),
        lineScoreAtDegrees S d D u (.axis (linePoints u (Pi.single i (1 : F)))) := by
  rw [branchWinProbAtDegrees_eq_weighted, branchQuestions_axis, axisQuestions, sum_bind_mul]
  simp only [sum_bind_mul, uniform_sum_eq_expect, sum_assignLineRoles_eq, lineScoreAtDegrees]

/-- The consistency score averages the acceptance at a shared point. -/
theorem consistencyScoreAtDegrees_eq_expect (n d D : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGameWithDiagonalCap (F := F) n d D .consistency).commutingWinProb S =
      𝔼 u : Point F (n + 1), acceptScoreAtDegrees S d D (.point u) (.point u) := by
  rw [branchWinProbAtDegrees_eq_weighted, branchQuestions_consistency, consistencyQuestions,
    sum_map_mul, uniform_sum_eq_expect]

/-- The diagonal score averages over the base point, prefix, direction and roles. -/
theorem diagonalScoreAtDegrees_eq_expect (n d D : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb S =
      𝔼 u : Point F (n + 1), 𝔼 i : Fin (n + 1), 𝔼 v,
        lineScoreAtDegrees S d D u (.diagonal (linePoints u (prefixDirection i v))) := by
  rw [branchWinProbAtDegrees_eq_weighted, branchQuestions_diagonal, diagonalQuestions, sum_bind_mul]
  simp only [sum_bind_mul, uniform_sum_eq_expect, sum_assignLineRoles_eq, lineScoreAtDegrees]

omit [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A] in
private theorem acceptScoreAtDegrees_congr_cutoff
    (S : CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) A)
    (d D E : ℕ) (x y : Question F m)
    (h : ∀ a b, acceptsWithDiagonalCap d D x y a b ↔ acceptsWithDiagonalCap d E x y a b) :
    acceptScoreAtDegrees S d D x y = acceptScoreAtDegrees S d E x y := by
  classical
  simp only [acceptScoreAtDegrees, h]

/-- The diagonal cutoff has no effect on the axis branch's winning probability. -/
theorem axisWinProbAtDegrees_eq (n d D : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGameWithDiagonalCap (F := F) n d D .axis).commutingWinProb S =
      (branchGame (F := F) n d .axis).commutingWinProb S := by
  rw [branchGame_eq_withDiagonalCap, axisScoreAtDegrees_eq_expect, axisScoreAtDegrees_eq_expect]
  refine expect_congr rfl fun u _ => expect_congr rfl fun i _ => ?_
  unfold lineScoreAtDegrees
  refine congrArg (· / 2) (congrArg₂ (· + ·) ?_ ?_)
  all_goals
    apply acceptScoreAtDegrees_congr_cutoff
    intro a b
    cases a <;> cases b <;> rfl

/-- The diagonal cutoff has no effect on the consistency branch's winning probability. -/
theorem consistencyWinProbAtDegrees_eq (n d D : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) :
    (branchGameWithDiagonalCap (F := F) n d D .consistency).commutingWinProb S =
      (branchGame (F := F) n d .consistency).commutingWinProb S := by
  rw [branchGame_eq_withDiagonalCap, consistencyScoreAtDegrees_eq_expect,
    consistencyScoreAtDegrees_eq_expect]
  refine expect_congr rfl fun u _ => ?_
  apply acceptScoreAtDegrees_congr_cutoff
  intro a b
  cases a <;> cases b <;> rfl

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
  rw [branchGame_eq_withDiagonalCap, axisScoreAtDegrees_eq_expect]
  rfl

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
  rw [branchGame_eq_withDiagonalCap, consistencyScoreAtDegrees_eq_expect]
  rfl

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
  rw [branchGame_eq_withDiagonalCap, diagonalScoreAtDegrees_eq_expect]
  rfl

/-- Conditioning the diagonal test on a prefix and the point-first role assignment
costs at most twice the number of coordinates in its rejection probability. -/
theorem diagonalPointLossAtDegrees_le (n d D : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) (j : Fin (n + 1)) :
    (𝔼 u : Point F (n + 1), 𝔼 v : Fin (j.val + 1) → F,
        (1 - acceptScoreAtDegrees S d D (.point u)
          (.diagonal (linePoints u (prefixDirection j v))))) ≤
      2 * (n + 1 : ℝ) *
        (1 - (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb S) := by
  rw [diagonalScoreAtDegrees_eq_expect,
    expect_comm (ι := Point F (n + 1)) (κ := Fin (n + 1)) univ univ]
  let score (u : Point F (n + 1)) (i : Fin (n + 1)) (v : Fin (i.val + 1) → F) :=
    lineScoreAtDegrees S d D u (.diagonal (linePoints u (prefixDirection i v)))
  let loss (i : Fin (n + 1)) := 𝔼 u : Point F (n + 1), 𝔼 v, (1 - score u i v)
  have h0 (i : Fin (n + 1)) : 0 ≤ loss i := by
    refine expect_nonneg fun u _ => expect_nonneg fun v _ => ?_
    exact sub_nonneg.mpr (lineScoreAtDegrees_le_one S d D u _)
  have hselected : loss j ≤ (n + 1 : ℝ) * (1 - 𝔼 i : Fin (n + 1),
      𝔼 u : Point F (n + 1), 𝔼 v, score u i v) := by
    calc
      _ ≤ ∑ i, loss i := single_le_sum (fun i _ => h0 i) (mem_univ _)
      _ = _ := by
        rw [← Fintype.card_mul_expect, Fintype.card_fin, Nat.cast_succ]
        simp only [loss, expect_sub_distrib, Fintype.expect_const]
  calc
    _ ≤ 𝔼 u : Point F (n + 1), 𝔼 v : Fin (j.val + 1) → F,
        (2 * (1 - score u j v)) := by
      refine expect_le_expect fun u _ => expect_le_expect fun v _ => ?_
      simp only [score, lineScoreAtDegrees]
      linarith [acceptScoreAtDegrees_le_one S d D
        (.diagonal (linePoints u (prefixDirection j v))) (.point u)]
    _ = 2 * loss j := by
      simp only [← mul_expect]
      rfl
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hselected (by norm_num)

/-- Conditioning the diagonal test on a prefix and the point-first role assignment
costs at most twice the number of coordinates in its rejection probability. -/
theorem diagonalPointLossAt_le (n d : ℕ)
    (S : CommutingStrategy (Question F (n + 1)) (Question F (n + 1))
      (Answer F (n + 1)) (Answer F (n + 1)) A) (j : Fin (n + 1)) :
    (𝔼 u : Point F (n + 1), 𝔼 v : Fin (j.val + 1) → F,
        (1 - acceptScore S d (.point u) (.diagonal (linePoints u (prefixDirection j v))))) ≤
      2 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .diagonal).commutingWinProb S) := by
  rw [branchGame_eq_withDiagonalCap]
  exact diagonalPointLossAtDegrees_le n d ((n + 1) * d) S j

end Cslib.PCP.LowIndividualDegree

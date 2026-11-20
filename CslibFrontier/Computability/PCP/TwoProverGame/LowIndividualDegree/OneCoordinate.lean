/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.AxisScore
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialAnswer
public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform

/-!
# Polynomial measurements for the one-coordinate test

In one coordinate the axis-parallel line is the whole space. Its measurement can be used
as a single global polynomial measurement, the base case in the proof of Theorem 6.1 of
[Ji, Natarajan, Vidick, Wright and Yuen][JNVWY2020LowIndividualDegree].
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Quantum
open scoped BigOperators
open Cslib.Probability.PMF (uniformOfFintype)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- In one coordinate the geometric line question is deterministic. The point and the
assignment of the two roles remain uniform and independent. -/
theorem axisQuestions_one :
    axisQuestions (F := F) 0 =
      (uniformOfFintype (Point F 1)).bind fun u => assignLineRoles (.axis univ) (.point u) := by
  unfold axisQuestions
  apply congrArg (PMF.bind (uniformOfFintype (Point F 1)))
  funext u
  have h : (fun i : Fin (0 + 1) =>
      assignLineRoles (.axis (linePoints u (Pi.single i (1 : F)))) (.point u)) =
        fun _ => assignLineRoles (.axis univ) (.point u) := by
    funext i
    rw [linePoints_single_eq_univ u i]
  rw [h, PMF.bind_const]

section Soundness

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜]

local notation "Q" => Question F 1
local notation "Ans" => Answer F 1

private theorem axisScore_one (S : CommutingStrategy Q Q Ans Ans 𝒜) (d : ℕ) :
    (branchGame (F := F) 0 d .axis).commutingWinProb S =
      ∑ u, (uniformOfFintype (Point F 1) u).toReal *
        ((acceptScore S d (.point u) (.axis univ) +
          acceptScore S d (.axis univ) (.point u)) / 2) := by
  rw [axisScore_eq_expect]
  have h (u : Point F (0 + 1)) (i : Fin (0 + 1)) :
      linePoints u (Pi.single i (1 : F)) = univ := linePoints_single_eq_univ u i
  simp only [axisScoreAt, h, Fintype.expect_const]
  simp only [Fintype.expect_eq_sum_div_card, Cslib.Probability.PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div, sum_div]

/-- One-coordinate extraction. Each player's measurement on the unique axis-parallel line
gives a global degree-bounded polynomial measurement. Evaluating it at the other player's
point is at least as consistent, on average over the uniform point and the two roles, as
the axis-parallel test. -/
theorem exists_polynomial_measurements_one (S : CommutingStrategy Q Q Ans Ans 𝒜) (d : ℕ) :
    ∃ (P R : Measurement (PolynomialFunction F d) 𝒜),
      (∀ u p a, Commute (((S.alice (.point u)).map decodePoint).effect a) (R.effect p)) ∧
      (∀ u p a, Commute (P.effect p) (((S.bob (.point u)).map decodePoint).effect a)) ∧
      (∑ u, (uniformOfFintype (Point F 1) u).toReal *
        ((Measurement.agreement S.state ((S.alice (.point u)).map decodePoint)
            (R.map fun f => f.eval u) +
          Measurement.agreement S.state (P.map fun f => f.eval u)
            ((S.bob (.point u)).map decodePoint)) / 2)) ≥
        (branchGame (F := F) 0 d .axis).commutingWinProb S := by
  classical
  let P := (S.alice (.axis univ)).map (decodePolynomial d)
  let R := (S.bob (.axis univ)).map (decodePolynomial d)
  refine ⟨P, R, ?_, ?_, ?_⟩
  · intro u p a
    exact Measurement.commute_map_map _ _ (S.commute (.point u) (.axis univ))
      decodePoint (decodePolynomial d) a p
  · intro u p a
    exact Measurement.commute_map_map _ _ (S.commute (.axis univ) (.point u))
      (decodePolynomial d) decodePoint p a
  · rw [axisScore_one]
    refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply add_le_add
    · simp only [acceptScore, R, Measurement.map_map, Measurement.agreement_map_map]
      refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
      by_cases h : accepts d (.point u) (.axis univ) a b
      · have h' := decodePolynomial_agrees ((accepts_point_axis_iff d univ u a b).mp h)
        simp only [ite_eq_left h, Function.comp_apply, h'.symm, ite_true, CommutingStrategy.prob]
        exact le_rfl
      · rw [ite_eq_right h]
        exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl
    · simp only [acceptScore, P, Measurement.map_map, Measurement.agreement_map_map]
      refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
      by_cases h : accepts d (.axis univ) (.point u) a b
      · have h' := decodePolynomial_agrees h
        simp only [ite_eq_left h, Function.comp_apply, h', ite_true, CommutingStrategy.prob]
        exact le_rfl
      · rw [ite_eq_right h]
        exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl

end Soundness

end Cslib.PCP.LowIndividualDegree

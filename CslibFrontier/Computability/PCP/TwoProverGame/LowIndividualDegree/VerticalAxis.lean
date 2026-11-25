/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.AxisScore
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialAnswer
public import CslibFrontier.Foundations.Quantum.Algebra.SuccessfulAgreement
public import Mathlib.Data.Fin.Tuple.Basic
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The vertical axis test and decoded polynomial measurements

Conditioning the axis test on its last coordinate samples a uniform prefix and a
uniform position on the vertical line over that prefix. The decoder for an accepted
line answer gives its polynomial in the vertical coordinate. This is the axis-test
input to [Ji, Natarajan, Vidick, Wright and Yuen, Equation (112)]
[JNVWY2020LowIndividualDegree].
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Quantum
open scoped BigOperators Real

variable {F A : Type*} {n : ℕ} [Field F] [Fintype F] [DecidableEq F]

/-- The geometric line over prefix `u`, with the last coordinate free. -/
def verticalLine (u : Point F n) : Finset (Point F (n + 1)) :=
  linePoints (Fin.snoc u 0) (Pi.single (Fin.last n) 1)

omit [Fintype F] [DecidableEq F] in
theorem snoc_eq_vertical_affine (u : Point F n) (t : F) :
    Fin.snoc u t = Fin.snoc u 0 + t • Pi.single (Fin.last n) (1 : F) :=
  funext <| Fin.lastCases (by simp) fun _ => by simp [Fin.castSucc_ne_last]

theorem linePoints_snoc_vertical (u : Point F n) (t : F) :
    linePoints (Fin.snoc u t) (Pi.single (Fin.last n) (1 : F)) = verticalLine u :=
  snoc_eq_vertical_affine u t ▸ linePoints_translate_direction _ _ _

/-- Decode a raw vertical line answer in its last coordinate. -/
noncomputable def decodeVertical (d : ℕ) (u : Point F n) (a : Answer F (n + 1)) :
    PolynomialFunction F d :=
  decodeAffinePolynomial d (Fin.snoc u 0) (Pi.single (Fin.last n) 1) a

theorem decodeVertical_agrees {d : ℕ} (u : Point F n) (t : F) {a b : Answer F (n + 1)}
    (h : accepts d (.axis (verticalLine u)) (.point (Fin.snoc u t)) a b) :
    (decodeVertical d u a).value t = decodePoint b := by
  rw [decodeVertical, PolynomialFunction.value_eq_eval]
  exact decodeAffinePolynomial_agrees _ _ t (fun _ => t)
    (by simpa only [verticalLine, ← snoc_eq_vertical_affine] using h) rfl

section Measurement

variable [Ring A] [PartialOrder A] [IsOrderedAddMonoid A]

/-- Decode the outcomes of a point measurement. -/
@[expose] noncomputable def decodedPoint (M : Question F (n + 1) → Measurement (Answer F (n + 1)) A)
    (u : Point F (n + 1)) : Measurement F A :=
  (M (.point u)).map decodePoint

/-- Decode the outcomes of the vertical-line measurement to polynomial functions. -/
@[expose] noncomputable def decodedVertical
    (M : Question F (n + 1) → Measurement (Answer F (n + 1)) A)
    (d : ℕ) (u : Point F n) : Measurement (PolynomialFunction F d) A :=
  (M (.axis (verticalLine u))).map (decodeVertical d u)

end Measurement

section Score

variable [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [Algebra ℂ A]
  [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)

/-- Point-first agreement of the decoded responses for a fixed vertical test. -/
theorem acceptScore_le_verticalAgreement (S : CommutingStrategy Q Q Ans Ans A)
    (d : ℕ) (u : Point F n) (t : F) :
    acceptScore S d (.point (Fin.snoc u t)) (.axis (verticalLine u)) ≤
      Measurement.agreement S.state (decodedPoint S.alice (Fin.snoc u t))
        ((decodedVertical S.bob d u).map (fun f => f.value t)) := by
  rw [decodedPoint, decodedVertical, Measurement.map_map]
  exact acceptScore_le_decodedAgreement S d _ _ _ _ fun a b h =>
    (decodeVertical_agrees u t ((accepts_point_axis_iff d _ _ a b).mp h)).symm

/-- The average decoded vertical disagreement with Alice receiving the point is at most
twice the ambient dimension times the original axis-branch loss. The factor two
accounts for conditioning on the assignment of the two roles. -/
theorem verticalDisagreement_le (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ) :
    (𝔼 u : Point F n, 𝔼 t : F,
      (1 - Measurement.agreement S.state (decodedPoint S.alice (Fin.snoc u t))
        ((decodedVertical S.bob d u).map (fun f => f.value t)))) ≤
      2 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) := by
  have hpt (u : Point F n) (t : F) :
      1 - Measurement.agreement S.state (decodedPoint S.alice (Fin.snoc u t))
        ((decodedVertical S.bob d u).map (fun f => f.value t)) ≤
      2 * (1 - axisScoreAt S d (Fin.snoc u t) (Fin.last n)) := by
    have h := acceptScore_le_verticalAgreement S d u t
    have hr := acceptScore_le_one S d (.axis (verticalLine u)) (.point (Fin.snoc u t))
    have ha : axisScoreAt S d (Fin.snoc u t) (Fin.last n) =
        (acceptScore S d (.point (Fin.snoc u t)) (.axis (verticalLine u)) +
          acceptScore S d (.axis (verticalLine u)) (.point (Fin.snoc u t))) / 2 := by
      rw [axisScoreAt, linePoints_snoc_vertical]
    linarith
  refine (expect_le_expect fun u _ => expect_le_expect fun t _ => hpt u t).trans ?_
  simp only [← Finset.mul_expect,
    Fintype.expect_fin_snoc (f := fun w => 1 - axisScoreAt S d w (Fin.last n)), mul_assoc]
  exact mul_le_mul_of_nonneg_left (axisLossAt_le n d S (Fin.last n)) (by norm_num)

section Norm

variable [StarModule ℂ A] [SelfAdjointDecompose A]

/-- The distance between the two point answers is controlled by the consistency branch. -/
theorem decodedPoint_stateDist_le (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ) :
    (𝔼 u : Point F (n + 1), ∑ a,
      S.state.norm ((decodedPoint S.bob u).effect a - (decodedPoint S.alice u).effect a) ^ 2) ≤
    2 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S) := by
  classical
  have hpt (u : Point F (n + 1)) :
      (∑ a, S.state.norm ((decodedPoint S.bob u).effect a -
        (decodedPoint S.alice u).effect a) ^ 2) ≤
      2 * (1 - acceptScore S d (.point u) (.point u)) := by
    have hScore : acceptScore S d (.point u) (.point u) ≤
        Measurement.agreement S.state (decodedPoint S.alice u) (decodedPoint S.bob u) := by
      simp only [acceptScore_eq_sum, decodedPoint, Measurement.agreement_map_map]
      refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
      by_cases h : accepts d (.point u) (.point u) a b
      · obtain ⟨z, rfl, rfl⟩ := exists_eq_of_accepts_points d u u a b h
        simp only [ite_eq_left h, ite_true, CommutingStrategy.prob, le_refl]
      · rw [ite_eq_right h]; exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl
    have h := Measurement.sum_norm_sub_sq_le S.state (decodedPoint S.alice u) (decodedPoint S.bob u)
      fun a => Measurement.commute_map_map _ _ (S.commute (.point u) (.point u)) _ _ a a
    simp only [S.state.norm_sub_comm ((decodedPoint S.bob u).effect _)]
    linarith
  rw [consistencyScore_eq_expect]
  refine (expect_le_expect fun u _ => hpt u).trans_eq ?_
  simp only [← Finset.mul_expect, expect_sub_distrib, Fintype.expect_const]

private theorem vertical_stateDist_le (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ) :
    (𝔼 u : Point F n, 𝔼 t : F, ∑ a, S.state.norm
      ((decodedPoint S.alice (Fin.snoc u t)).effect a -
        ((decodedVertical S.bob d u).map (fun f => f.value t)).effect a) ^ 2) ≤
      4 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) := by
  classical
  have hpt (u : Point F n) (t : F) :
      (∑ a, S.state.norm ((decodedPoint S.alice (Fin.snoc u t)).effect a -
        ((decodedVertical S.bob d u).map (fun f => f.value t)).effect a) ^ 2) ≤
      2 * (1 - Measurement.agreement S.state (decodedPoint S.alice (Fin.snoc u t))
        ((decodedVertical S.bob d u).map (fun f => f.value t))) := by
    have h := Measurement.sum_norm_sub_sq_le S.state (decodedPoint S.alice (Fin.snoc u t))
      ((decodedVertical S.bob d u).map (fun f => f.value t)) fun a => by
        rw [decodedPoint, decodedVertical, Measurement.map_map]
        exact Measurement.commute_map_map _ _
          (S.commute (.point (Fin.snoc u t)) (.axis (verticalLine u))) _ _ a a
    linarith
  refine (expect_le_expect fun u _ => expect_le_expect fun t _ => hpt u t).trans ?_
  simp only [← Finset.mul_expect]; linarith [verticalDisagreement_le S d]

/-- Bob's decoded point and vertical-line measurements have squared state distance controlled
by the consistency and axis losses. This is the same-side comparison used in Equation (112). -/
theorem bob_vertical_stateDist_le (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ) :
    (𝔼 u : Point F n, 𝔼 t : F, ∑ a, S.state.norm
      ((decodedPoint S.bob (Fin.snoc u t)).effect a -
        ((decodedVertical S.bob d u).map (fun f => f.value t)).effect a) ^ 2) ≤
      8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
      4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S) := by
  have hpt (u : Point F n) (t : F) :
      (∑ a, S.state.norm ((decodedPoint S.bob (Fin.snoc u t)).effect a -
        ((decodedVertical S.bob d u).map (fun f => f.value t)).effect a) ^ 2) ≤
      2 * (∑ a, S.state.norm ((decodedPoint S.bob (Fin.snoc u t)).effect a -
        (decodedPoint S.alice (Fin.snoc u t)).effect a) ^ 2) +
      2 * (∑ a, S.state.norm ((decodedPoint S.alice (Fin.snoc u t)).effect a -
        ((decodedVertical S.bob d u).map (fun f => f.value t)).effect a) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun a _ => ?_
    let b := (decodedPoint S.bob (Fin.snoc u t)).effect a
    let p := (decodedPoint S.alice (Fin.snoc u t)).effect a
    let ℓ := ((decodedVertical S.bob d u).map (fun f => f.value t)).effect a
    have h : S.state.norm (b - ℓ) ≤ S.state.norm (b - p) + S.state.norm (p - ℓ) :=
      sub_add_sub_cancel b p ℓ ▸ S.state.norm_add_le _ _
    exact (pow_le_pow_left₀ (S.state.norm_nonneg _) h 2).trans
      (by nlinarith [sq_nonneg (S.state.norm (b - p) - S.state.norm (p - ℓ))])
  refine (expect_le_expect fun u _ => expect_le_expect fun t _ => hpt u t).trans ?_
  simp only [expect_add_distrib, ← Finset.mul_expect, Fintype.expect_fin_snoc (f := fun w =>
    ∑ a, S.state.norm ((decodedPoint S.bob w).effect a - (decodedPoint S.alice w).effect a) ^ 2)]
  linarith [decodedPoint_stateDist_le S d, vertical_stateDist_le S d]

/-- The average successful mismatch changes by at most the square root of the
same-side state-distance bound when comparing to the decoded vertical line or point.
This gives the measurement transfers used in Equations (113)–(114). -/
theorem successfulMismatch_vertical_abs_sub_le (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ)
    (P : Point F n → F → Measurement (Option F) A) :
    |(𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state (P u t)
        ((decodedVertical S.bob d u).map (fun f => f.value t))) -
      (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state (P u t)
        (decodedPoint S.bob (Fin.snoc u t)))| ≤
      √(8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
        4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S)) := by
  let err (u : Point F n) (t : F) :=
    ∑ a, S.state.norm ((decodedPoint S.bob (Fin.snoc u t)).effect a -
      ((decodedVertical S.bob d u).map (fun f => f.value t)).effect a) ^ 2
  have herr (u : Point F n) (t : F) : 0 ≤ err u t := sum_nonneg fun _ _ => sq_nonneg _
  have hj : (𝔼 u : Point F n, 𝔼 t : F, √(err u t)) ≤ √(𝔼 u : Point F n, 𝔼 t : F, err u t) := by
    simpa only [mul_one, one_pow, Fintype.expect_const, Real.sqrt_one,
      Real.sq_sqrt (herr _ _), Fintype.expect_prod_type] using
      Real.expect_mul_le_sqrt_mul_sqrt (univ : Finset (Point F n × F))
        (fun p => √(err p.1 p.2)) (fun _ => 1)
  have transfer {Q₁ Q₂ : Point F n → F → Measurement F A}
      (h : ∀ u t, (∑ a, S.state.norm ((Q₁ u t).effect a - (Q₂ u t).effect a) ^ 2) = err u t) :
      (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state (P u t) (Q₂ u t)) ≤
      (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state (P u t) (Q₁ u t)) +
        √(8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
          4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S)) := by
    refine (expect_le_expect fun u _ => expect_le_expect fun t _ =>
      h u t ▸ Measurement.successfulMismatch_le _ _ _ _).trans ?_
    simp only [expect_add_distrib]
    exact add_le_add_right (hj.trans (Real.sqrt_le_sqrt (bob_vertical_stateDist_le S d))) _
  exact abs_sub_le_iff.mpr ⟨sub_le_iff_le_add'.mpr (transfer fun _ _ => rfl),
    sub_le_iff_le_add'.mpr (transfer fun _ _ => sum_congr rfl fun _ _ => by
      rw [S.state.norm_sub_comm])⟩

/-- Transfer agreement of the successful slice measurements from Bob's point answers
to his vertical-line answers. The initial mismatch may be any bound supplied by the
slice construction. This is the comparison of Equation (113). -/
theorem successfulMismatch_vertical_le (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ)
    (P : Point F n → F → Measurement (Option F) A) :
    (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state (P u t)
      ((decodedVertical S.bob d u).map (fun f => f.value t))) ≤
    (𝔼 u : Point F n, 𝔼 t : F, Measurement.successfulMismatch S.state
      (P u t) (decodedPoint S.bob (Fin.snoc u t))) +
      √(8 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
        4 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S)) :=
  sub_le_iff_le_add'.mp (abs_sub_le_iff.mp (successfulMismatch_vertical_abs_sub_le S d P)).1

end Norm

end Score

end Cslib.PCP.LowIndividualDegree

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PointVariance
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialMeasurement
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialPointEffect
public import CslibFrontier.Foundations.Quantum.Algebra.SuccessfulAgreement
public import CslibFrontier.Foundations.Quantum.Algebra.SandwichedMeasurement
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementMixture
import CslibFrontier.Probability.PMF.Uniform

/-!
# The sandwiched polynomial submeasurement

This is the measurement construction in §9.2 of [JNVWY2020LowIndividualDegree].
The comparison used in Lemma 9.3 is proved here in terms of the point-copy and
weighted-variance errors. A separate estimate from the verifier bounds the variance.

## Main definitions

* `Cslib.PCP.LowIndividualDegree.sandwichedPolynomialMeasurement`: the average
  of the point-sandwiched polynomial effects, completed by a failure outcome.

## Main results

* `Cslib.PCP.LowIndividualDegree.abs_sandwichedPolynomial_score_sub_le`: the
  comparison with sandwiching on the other side at the point in the score.
* `Cslib.PCP.LowIndividualDegree.successfulMass_sandwichedPolynomial_lower_bound`
  transfers input agreement to successful mass using the SDP certificate.
* `Cslib.PCP.LowIndividualDegree.average_successfulMismatch_sandwichedPolynomial_le`
  bounds disagreement on successful outcomes.
* `Cslib.PCP.LowIndividualDegree.majorant_sub_sandwichedPolynomial_agreement_le`
  compares point agreement with the state value of the majorant.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Cslib.Quantum.Measurement Finset MvPolynomial
open scoped BigOperators Real

variable {A F : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Average the polynomial measurement after sandwiching each effect by the point
effect for that polynomial's value. The residual effect records failure. -/
noncomputable def sandwichedPolynomialMeasurement
    (R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A) :
    Measurement (Option (BoundedPolynomial F m d)) A :=
  Measurement.mixture (Cslib.Probability.PMF.uniformOfFintype (Point F m)) fun u =>
    T.sandwichBy (R u) (fun g => eval u g.val)

omit [DecidableEq F] in
/-- Each successful effect is the uniform average of the corresponding sandwiches. -/
theorem sandwichedPolynomialMeasurement_effect_some
    (R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A)
    (g : BoundedPolynomial F m d) :
    (sandwichedPolynomialMeasurement R T).effect (some g) =
      (Fintype.card (Point F m) : ℝ)⁻¹ • ∑ u : Point F m,
        (R u).effect (eval u g.val) * T.effect g * (R u).effect (eval u g.val) := by
  rw [sandwichedPolynomialMeasurement, Measurement.mixture_uniform_effect]
  simp only [Measurement.sandwichBy_effect_some]

omit [DecidableEq F] in
/-- A step of the self-improvement argument. In a score against positive contractions
on the opposite side, the averaged sandwiches can be replaced by pointwise sandwiches
around those contractions. The cost is the sum of twice the square roots of the
point-copy error and the weighted variance. -/
theorem abs_sandwichedPolynomial_score_sub_le (φ : AlgState A)
    (L R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A)
    (C : Point F m → BoundedPolynomial F m d → A) (hC : ∀ u g, C u g ∈ Set.Icc (0 : A) 1)
    (hCT : ∀ u g, Commute (C u g) (T.effect g))
    (hCR : ∀ u v g b, Commute (C u g) ((R v).effect b))
    (hLT : ∀ u g b, Commute ((L u).effect b) (T.effect g)) :
    |(𝔼 u : Point F m, ∑ g,
        (φ (C u g * (sandwichedPolynomialMeasurement R T).effect (some g))).re) -
      (𝔼 u : Point F m, ∑ g, (φ ((L u).effect (eval u g.val) * C u g *
        (L u).effect (eval u g.val) * T.effect g)).re)| ≤
      2 * √(𝔼 u : Point F m, copyDefect φ (R u) (L u)) +
      2 * √(weightedPointVariance φ L T) := by
  let f (u : Point F m) (g : BoundedPolynomial F m d) := eval u g.val
  let S (M : Point F m → Measurement F A) (u v : Point F m) :=
    ∑ g, (φ ((M v).effect (f v g) * (C u g * T.effect g) * (M v).effect (f v g))).re
  let V (u v : Point F m) (g : BoundedPolynomial F m d) :=
    (L v).effect (f v g) - (L u).effect (f u g)
  let e (u v : Point F m) := ∑ g, (φ (star (V u v g) * T.effect g * V u v g)).re
  have hright (u v : Point F m) :
      S R u v = ∑ g, (φ (C u g * ((R v).effect (f v g) * T.effect g *
        (R v).effect (f v g)))).re := by
    refine sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, ← (hCR u v g (f v g)).eq]
    simp only [mul_assoc]
  have hleft (u : Point F m) :
      S L u u = ∑ g, (φ ((L u).effect (f u g) * C u g *
        (L u).effect (f u g) * T.effect g)).re := by
    refine sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, mul_assoc ((L u).effect (f u g) * C u g),
      ← (hLT u g (f u g)).eq, ← mul_assoc]
  have h₁ : (𝔼 u : Point F m, ∑ g,
        (φ (C u g * (sandwichedPolynomialMeasurement R T).effect (some g))).re) =
      𝔼 u : Point F m, 𝔼 v : Point F m, S R u v := by
    refine expect_congr rfl fun u _ => ?_
    simp_rw [sandwichedPolynomialMeasurement_effect_some, mul_smul_comm, mul_sum,
      AlgState.re_apply_uniformAverage, hright, expect_sum_comm, f]
  have h₂ : (𝔼 u : Point F m, ∑ g, (φ ((L u).effect (f u g) * C u g *
        (L u).effect (f u g) * T.effect g)).re) =
      𝔼 u : Point F m, 𝔼 v : Point F m, S L u u := by
    simp only [Fintype.expect_const, hleft]
  rw [h₁, h₂]
  simp_rw [← expect_sub_distrib]
  refine (abs_expect_le _ _).trans <| (expect_le_expect fun u _ => abs_expect_le _ _).trans ?_
  have hp (u v : Point F m) : |S R u v - S L u u| ≤
      2 * √(copyDefect φ (R v) (L v)) + 2 * √(e u v) := by
    have hgroup := φ.sum_weighted_conj_le_sum_norm_sq T (f v)
      (fun b => (R v).effect b - (L v).effect b)
    have hcopy := (abs_sum_weighted_sandwich_sub_le φ T (R v) (L v) (f v) (f v)
      (C u) (hC u) (hCT u)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgroup)
        (by norm_num))
    have hvar := abs_sum_weighted_sandwich_sub_le φ T (L v) (L u) (f v) (f u)
      (C u) (hC u) (hCT u)
    exact (abs_sub_le (S R u v) (S L u v) (S L u u)).trans (add_le_add hcopy hvar)
  refine (expect_le_expect fun u _ => expect_le_expect fun v _ => hp u v).trans ?_
  have hcopy := Fintype.expect_sqrt_le_sqrt_expect (fun v : Point F m => copyDefect φ (R v) (L v))
    (fun v => sum_nonneg fun b _ => sq_nonneg _)
  have hvar : (𝔼 u : Point F m, 𝔼 v : Point F m, √(e u v)) ≤ √(weightedPointVariance φ L T) := by
    simpa only [Fintype.expect_prod_type, weightedPointVariance] using
      Fintype.expect_sqrt_le_sqrt_expect (fun z : Point F m × Point F m => e z.1 z.2)
        (fun z => sum_nonneg fun g _ =>
          φ.re_apply_nonneg (star_left_conjugate_nonneg (T.nonneg g) (V z.1 z.2 g)))
  simp only [expect_add_distrib, ← mul_expect, Fintype.expect_const]
  gcongr

omit [DecidableEq F] in
private theorem state_successfulMass_sandwichedPolynomial_eq (φ : AlgState A)
    (R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A) :
    (φ (sandwichedPolynomialMeasurement R T).successfulEffect).re =
      𝔼 u : Point F m, ∑ g, (φ ((R u).effect (eval u g.val) * T.effect g *
        (R u).effect (eval u g.val))).re := by
  rw [expect_sum_comm, successfulEffect, map_sum, Complex.re_sum]
  simp_rw [sandwichedPolynomialMeasurement_effect_some, AlgState.re_apply_uniformAverage]

/-- Complementary slackness identifies the mass of the sandwiched measurement
with the state expectation of the majorant, up to the cost of copying point
effects. The estimate uses no variation across different points. -/
theorem abs_successfulMass_sandwichedPolynomial_sub_majorant_le (φ : AlgState A)
    (L R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A)
    (hL : ∀ u, (L u).IsProjective)
    (hLT : ∀ u g b, Commute ((L u).effect b) (T.effect g)) (Z : A)
    (hslack : ∀ g, T.effect g * Z = T.effect g * averagePolynomialPointEffect R g) :
    |(φ (sandwichedPolynomialMeasurement R T).successfulEffect).re - (φ Z).re| ≤
      3 * √(𝔼 u : Point F m, copyDefect φ (R u) (L u)) := by
  let Rg (u : Point F m) (g : BoundedPolynomial F m d) := (R u).effect (eval u g.val)
  let Lg (u : Point F m) (g : BoundedPolynomial F m d) := (L u).effect (eval u g.val)
  have hmean : (𝔼 u : Point F m, ∑ g, (φ (T.effect g * Rg u g)).re) = (φ Z).re := by
    rw [expect_sum_comm]
    have he (g : BoundedPolynomial F m d) : (𝔼 u : Point F m, (φ (T.effect g * Rg u g)).re) =
        (φ (T.effect g * averagePolynomialPointEffect R g)).re := by
      rw [averagePolynomialPointEffect_eq, mul_smul_comm, mul_sum, AlgState.re_apply_uniformAverage]
    simp only [he, ← hslack, ← Complex.re_sum, ← map_sum, ← sum_mul, T.sum_effect, one_mul]
  have hp (u : Point F m) :
      |(∑ g, (φ (Rg u g * T.effect g * Rg u g)).re) -
          ∑ g, (φ (T.effect g * Rg u g)).re| ≤ 3 * √(copyDefect φ (R u) (L u)) := by
    have hex (g : BoundedPolynomial F m d) : Lg u g * T.effect g * Lg u g =
        T.effect g * Lg u g := by
      rw [(hLT u g _).eq, mul_assoc, hL u _]
    have hweighted := Real.sqrt_le_sqrt
      (φ.sum_weighted_conj_le_sum_norm_sq T (fun g => eval u g.val)
        (fun b => (R u).effect b - (L u).effect b))
    have hquad := (abs_sum_weighted_sandwich_sub_le φ T (R u) (L u)
      (fun g => eval u g.val) (fun g => eval u g.val)
      (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) (fun _ => Commute.one_left _)).trans
      (mul_le_mul_of_nonneg_left hweighted (by norm_num))
    change |(∑ g, (φ (Rg u g * (1 * T.effect g) * Rg u g)).re) -
      ∑ g, (φ (Lg u g * (1 * T.effect g) * Lg u g)).re| ≤ _ at hquad
    simp only [one_mul, hex] at hquad
    have hlin := (φ.abs_sum_weighted_mul_le T T.effect (fun g => Rg u g - Lg u g)
      T.nonneg (fun _ => le_rfl)).trans hweighted
    simp only [mul_sub, map_sub, Complex.sub_re, sum_sub_distrib] at hlin
    rw [abs_sub_comm] at hlin
    refine ((abs_sub_le (∑ g, (φ (Rg u g * T.effect g * Rg u g)).re)
      (∑ g, (φ (T.effect g * Lg u g)).re) (∑ g, (φ (T.effect g * Rg u g)).re)).trans
      (add_le_add hquad hlin)).trans_eq ?_
    simp only [copyDefect]; ring
  rw [state_successfulMass_sandwichedPolynomial_eq, ← hmean, ← expect_sub_distrib]
  refine (abs_expect_le _ _).trans ((expect_le_expect fun u _ => hp u).trans ?_)
  rw [← mul_expect]
  exact mul_le_mul_of_nonneg_left (Fintype.expect_sqrt_le_sqrt_expect _
    (fun _ => sum_nonneg fun _ _ => sq_nonneg _)) (by norm_num)

/-- A step of the completeness proof. A common majorant and complementary slackness
transfer the input polynomial agreement to the successful mass of the sandwiched
measurement. The input may itself have a failure outcome. -/
theorem successfulMass_sandwichedPolynomial_lower_bound (φ : AlgState A)
    (L R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A)
    (hL : ∀ u, (L u).IsProjective)
    (hLT : ∀ u g b, Commute ((L u).effect b) (T.effect g))
    (G : Measurement (Option (BoundedPolynomial F m d)) A) (Z : A)
    (hle : ∀ g : BoundedPolynomial F m d, averagePolynomialPointEffect R g ≤ Z)
    (hslack : ∀ g, T.effect g * Z = T.effect g * averagePolynomialPointEffect R g)
    (hGZ : ∀ g, Commute (G.effect g) Z)
    (hGR : ∀ g u b, Commute (G.effect g) ((R u).effect b)) :
    (𝔼 u : Point F m, ∑ g, (φ (G.effect (some g) * (R u).effect (eval u g.val))).re) -
        3 * √(𝔼 u : Point F m, copyDefect φ (R u) (L u)) ≤
      (φ (sandwichedPolynomialMeasurement R T).successfulEffect).re := by
  have hsum : (∑ g, (φ (G.effect (some g) * Z)).re) ≤ (φ Z).re := by
    have hZ : 0 ≤ Z := (averagePolynomialPointEffect_mem_Icc R
      (⟨0, by simp⟩ : BoundedPolynomial F m d)).1.trans (hle _)
    have hnone := φ.re_apply_nonneg ((hGZ none).mul_nonneg (G.nonneg none) hZ)
    have he := congrArg (fun x => (φ (x * Z)).re) G.sum_effect
    simp only [Fintype.sum_option, add_mul, map_add, Complex.add_re, one_mul,
      sum_mul, map_sum, Complex.re_sum] at he
    linarith only [he, hnone]
  have hmean (g : BoundedPolynomial F m d) :
      (𝔼 u : Point F m, (φ (G.effect (some g) * (R u).effect (eval u g.val))).re) =
        (φ (G.effect (some g) * averagePolynomialPointEffect R g)).re := by
    rw [averagePolynomialPointEffect_eq, mul_smul_comm, mul_sum, AlgState.re_apply_uniformAverage]
  have hscore : (𝔼 u : Point F m, ∑ g,
      (φ (G.effect (some g) * (R u).effect (eval u g.val))).re) ≤ (φ Z).re := by
    rw [expect_sum_comm]
    simp only [hmean]
    refine (sum_le_sum fun g _ => ?_).trans hsum
    have hc := (hGZ (some g)).sub_right
      (commute_averagePolynomialPointEffect R g _ (hGR (some g)))
    exact φ.re_apply_mono (by
      simpa only [mul_sub, sub_nonneg] using
        hc.mul_nonneg (G.nonneg (some g)) (sub_nonneg.mpr (hle g)))
  have hm := abs_successfulMass_sandwichedPolynomial_sub_majorant_le φ L R T hL hLT Z hslack
  linarith only [hscore, (abs_le.mp hm).1]

/-- Compute point disagreement directly in terms of the polynomial outcomes. -/
theorem successfulMismatch_evaluate_eq_sum (φ : AlgState A)
    (P : Measurement (Option (BoundedPolynomial F m d)) A)
    (u : Point F m) (Q : Measurement F A) :
    successfulMismatch φ (evaluatePolynomialMeasurement P u) Q =
      ∑ g, (φ (P.effect (some g) * (1 - Q.effect (eval u g.val)))).re := by
  unfold successfulMismatch
  simp only [evaluatePolynomialMeasurement_effect_some, sum_mul, map_sum, Complex.re_sum]
  conv_rhs => rw [← sum_fiberwise univ (fun g : BoundedPolynomial F m d => eval u g.val)]
  exact sum_congr rfl fun b _ => sum_congr rfl fun g hg => by rw [(mem_filter.mp hg).2]

/-- The successful outcomes of the sandwiched polynomial measurement disagree with
the projective point answers by at most the copy and variance error budget. -/
theorem average_successfulMismatch_sandwichedPolynomial_le (φ : AlgState A)
    (L R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A)
    (hL : ∀ u, (L u).IsProjective)
    (hLR : ∀ u v a b, Commute ((L u).effect a) ((R v).effect b))
    (hLT : ∀ u g b, Commute ((L u).effect b) (T.effect g)) :
    (𝔼 u : Point F m, successfulMismatch φ
      (evaluatePolynomialMeasurement (sandwichedPolynomialMeasurement R T) u) (L u)) ≤
      2 * √(𝔼 u : Point F m, copyDefect φ (R u) (L u)) +
      2 * √(weightedPointVariance φ L T) := by
  let H := sandwichedPolynomialMeasurement R T
  let C (u : Point F m) (g : BoundedPolynomial F m d) := 1 - (L u).effect (eval u g.val)
  have hCT (u : Point F m) (g : BoundedPolynomial F m d) : Commute (C u g) (T.effect g) :=
    (Commute.one_left _).sub_left (hLT u g _)
  have hCR (u v : Point F m) (g : BoundedPolynomial F m d) (b : F) :
      Commute (C u g) ((R v).effect b) := (Commute.one_left _).sub_left (hLR u v _ b)
  have hCH (u : Point F m) (g : BoundedPolynomial F m d) :
      Commute (C u g) (H.effect (some g)) := by
    rw [show H = _ from rfl, sandwichedPolynomialMeasurement_effect_some]
    exact (Commute.sum_right _ _ _ fun v _ =>
      ((hCR u v g _).mul_right (hCT u g)).mul_right (hCR u v g _)).smul_right _
  have hgroup (u : Point F m) : successfulMismatch φ (evaluatePolynomialMeasurement H u) (L u) =
      ∑ g, (φ (C u g * H.effect (some g))).re := by
    rw [successfulMismatch_evaluate_eq_sum]
    exact sum_congr rfl fun g _ => congrArg (fun x => (φ x).re) (hCH u g).eq.symm
  have hzero (u : Point F m) (g : BoundedPolynomial F m d) :
      (L u).effect (eval u g.val) * C u g * (L u).effect (eval u g.val) * T.effect g = 0 := by
    dsimp only [C]
    rw [mul_sub, mul_one, hL u _, sub_self, zero_mul, zero_mul]
  have h := abs_sandwichedPolynomial_score_sub_le φ L R T C
    (fun u g => ⟨sub_nonneg.mpr ((L u).effect_le_one _),
      sub_le_self _ ((L u).nonneg _)⟩) hCT hCR hLT
  simp only [hzero, map_zero, Complex.zero_re, sum_const_zero, Fintype.expect_const, sub_zero]
    at h
  exact (expect_congr rfl fun u _ => hgroup u).trans_le ((le_abs_self _).trans h)

/-- A step of the boundedness proof. The dual majorant's state value exceeds the
sandwiched measurement's point-agreement score by at most the stated copy and variance
budget. The same majorant dominates the averaged point effects whenever it is dual feasible. -/
theorem majorant_sub_sandwichedPolynomial_agreement_le (φ : AlgState A)
    (L R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A)
    (hL : ∀ u, (L u).IsProjective)
    (hLR : ∀ u v a b, Commute ((L u).effect a) ((R v).effect b))
    (hLT : ∀ u g b, Commute ((L u).effect b) (T.effect g)) (Z : A)
    (hslack : ∀ g, T.effect g * Z = T.effect g * averagePolynomialPointEffect R g) :
    let H := sandwichedPolynomialMeasurement R T
    (φ Z).re - (𝔼 u : Point F m, ∑ b,
      (φ ((evaluatePolynomialMeasurement H u).effect (some b) * (L u).effect b)).re) ≤
      5 * √(𝔼 u : Point F m, copyDefect φ (R u) (L u)) +
      2 * √(weightedPointVariance φ L T) := by
  intro H
  have hsplit (u : Point F m) :
      successfulMismatch φ (evaluatePolynomialMeasurement H u) (L u) =
        (φ H.successfulEffect).re -
          ∑ b, (φ ((evaluatePolynomialMeasurement H u).effect (some b) * (L u).effect b)).re := by
    simp only [successfulMismatch, mul_sub, mul_one, map_sub, Complex.sub_re, sum_sub_distrib]
    congr 1
    simpa only [successfulEffect, map_sum, Complex.re_sum] using
      congrArg (fun x => (φ x).re) (evaluatePolynomialMeasurement_successfulEffect H u)
  have hmis := average_successfulMismatch_sandwichedPolynomial_le φ L R T hL hLR hLT
  change (𝔼 u : Point F m, successfulMismatch φ (evaluatePolynomialMeasurement H u) (L u)) ≤ _
    at hmis
  simp_rw [hsplit, expect_sub_distrib, Fintype.expect_const] at hmis
  have hm := abs_successfulMass_sandwichedPolynomial_sub_majorant_le φ L R T hL hLT Z hslack
  change |(φ H.successfulEffect).re - (φ Z).re| ≤ _ at hm
  linarith only [hmis, (abs_le.mp hm).1]

end Cslib.PCP.LowIndividualDegree

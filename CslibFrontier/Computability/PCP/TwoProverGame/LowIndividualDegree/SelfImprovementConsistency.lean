/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SelfImprovementSandwich
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SelfImprovementCollision
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Quantum.Algebra.MeasurementMixture

/-!
# Strong self-consistency of sandwiched polynomial measurements

Agreement of the two sandwiched measurements is compared with a score in
which both polynomials agree at the sampled point. The off-diagonal part
costs a weighted collision term. An independent point and complementary
slackness then turn the remaining score into a pairing with the majorant.
These are the strong self-consistency estimates in §9.2 of [JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.successfulMass_sub_sandwichedAgreement_le`
  compares successful mass with the agreement of the two sandwiched measurements.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Cslib.Quantum.Measurement Finset MvPolynomial
open scoped BigOperators Real

variable {F A : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem average_majorant_mul_le (φ : AlgState A)
    (L R : Point F m → Measurement F A) (T : Measurement (BoundedPolynomial F m d) A)
    (Z : A) (hslack : ∀ g, T.effect g * Z = T.effect g * averagePolynomialPointEffect R g)
    (D : Point F m → A) (hD : ∀ u, D u ∈ Set.Icc (0 : A) 1)
    (hDT : ∀ u g, Commute (D u) (T.effect g)) :
    (𝔼 u : Point F m, (φ (D u * Z)).re) ≤
      (𝔼 u : Point F m, ∑ g, (φ (D u * T.effect g * (L u).effect (eval u g.val))).re) +
        √(weightedPointVariance φ L T) + √(𝔼 u : Point F m, copyDefect φ (R u) (L u)) := by
  let f (u : Point F m) (g : BoundedPolynomial F m d) := eval u g.val
  let W (u : Point F m) (g : BoundedPolynomial F m d) := D u * T.effect g
  let J (M : Point F m → Measurement F A) (u v : Point F m) :=
    ∑ g, (φ (W u g * (M v).effect (f v g))).re
  let e (u v : Point F m) := ∑ g,
    let E := (L v).effect (f v g) - (L u).effect (f u g)
    (φ (star E * T.effect g * E)).re
  have hW u g : 0 ≤ W u g := (hDT u g).mul_nonneg (hD u).1 (T.nonneg g)
  have hle u g : W u g ≤ T.effect g := by
    simpa only [sub_mul, one_mul, sub_nonneg] using
      ((Commute.one_left (T.effect g)).sub_left (hDT u g)).mul_nonneg
        (sub_nonneg.mpr (hD u).2) (T.nonneg g)
  have hstep (u v : Point F m) : J R u v ≤ J L u u + √(e u v) + √(copyDefect φ (R v) (L v)) := by
    have hv := φ.abs_sum_weighted_mul_le T (W u)
      (fun g => (L v).effect (f v g) - (L u).effect (f u g)) (hW u) (hle u)
    conv at hv =>
      lhs
      simp only [mul_sub, map_sub, Complex.sub_re, sum_sub_distrib]
    change |J L u v - J L u u| ≤ √(e u v) at hv
    have hc := (φ.abs_sum_weighted_mul_le T (W u)
      (fun g => (R v).effect (f v g) - (L v).effect (f v g)) (hW u) (hle u)).trans
      (Real.sqrt_le_sqrt (φ.sum_weighted_conj_le_sum_norm_sq T (f v)
        (fun a => (R v).effect a - (L v).effect a)))
    conv at hc =>
      lhs
      simp only [mul_sub, map_sub, Complex.sub_re, sum_sub_distrib]
    change |J R u v - J L u v| ≤ √(copyDefect φ (R v) (L v)) at hc
    linarith only [(abs_le.mp hv).2, (abs_le.mp hc).2]
  have hmean (u : Point F m) : (𝔼 v : Point F m, J R u v) = (φ (D u * Z)).re := by
    have he (g : BoundedPolynomial F m d) :
        (𝔼 v : Point F m, (φ (W u g * (R v).effect (f v g))).re) =
          (φ (W u g * averagePolynomialPointEffect R g)).re := by
      rw [averagePolynomialPointEffect_eq, mul_smul_comm, mul_sum, AlgState.re_apply_uniformAverage]
    change (𝔼 v : Point F m, ∑ g, (φ (W u g * (R v).effect (f v g))).re) = _
    rw [expect_sum_comm]
    simp only [he]
    simp only [W, mul_assoc, ← hslack]
    simp only [← Complex.re_sum, ← map_sum, ← mul_sum]
    rw [← sum_mul, T.sum_effect, one_mul]
  have hvar : (𝔼 u : Point F m, 𝔼 v : Point F m, √(e u v)) ≤ √(weightedPointVariance φ L T) := by
    simpa only [Fintype.expect_prod_type, weightedPointVariance] using
      Fintype.expect_sqrt_le_sqrt_expect (fun z : Point F m × Point F m => e z.1 z.2)
        (fun z => sum_nonneg fun g _ => φ.re_apply_nonneg
          (star_left_conjugate_nonneg (T.nonneg g)
            ((L z.2).effect (f z.2 g) - (L z.1).effect (f z.1 g))))
  have hcopy := Fintype.expect_sqrt_le_sqrt_expect (fun v : Point F m => copyDefect φ (R v) (L v))
    (fun v => sum_nonneg fun a _ => sq_nonneg _)
  have h := expect_le_expect (s := (univ : Finset (Point F m))) fun u _ =>
    expect_le_expect (s := (univ : Finset (Point F m))) fun v _ => hstep u v
  simp only [hmean, expect_add_distrib, Fintype.expect_const] at h
  change _ ≤ (𝔼 u : Point F m, J L u u) + _ + _
  linarith only [h, hvar, hcopy]

/-- Strong self-consistency estimate for two sandwiched polynomial measurements.
The point copies and polynomial measurements are on opposite commuting sides.
The dual majorant and slack equations are for the right-hand measurement. -/
theorem successfulMass_sub_sandwichedAgreement_le
    (φ : AlgState A) (L R : Point F m → Measurement F A)
    (U T : Measurement (BoundedPolynomial F m d) A) (Z : A)
    (hL : ∀ u, (L u).IsProjective) (hR : ∀ u, (R u).IsProjective)
    (hLR : ∀ u v a b, Commute ((L u).effect a) ((R v).effect b))
    (hLT : ∀ u g a, Commute ((L u).effect a) (T.effect g))
    (hUR : ∀ g u b, Commute (U.effect g) ((R u).effect b))
    (hUT : ∀ h g, Commute (U.effect h) (T.effect g))
    (hLZ : ∀ u a, Commute ((L u).effect a) Z)
    (hUZ : ∀ g, Commute (U.effect g) Z)
    (hle : ∀ g : BoundedPolynomial F m d, averagePolynomialPointEffect R g ≤ Z)
    (hslack : ∀ g, T.effect g * Z = T.effect g * averagePolynomialPointEffect R g) :
    let P := sandwichedPolynomialMeasurement L U
    let Q := sandwichedPolynomialMeasurement R T
    (φ P.successfulEffect).re - ∑ g, (φ (P.effect (some g) * Q.effect (some g))).re ≤
      5 * √(𝔼 u : Point F m, copyDefect φ (R u) (L u)) +
      5 * √(weightedPointVariance φ L T) + 2 * √(weightedPointVariance φ R U) +
      (m : ℝ) * d / Fintype.card F := by
  classical
  intro P Q
  let f (u : Point F m) (g : BoundedPolynomial F m d) := eval u g.val
  let X (u : Point F m) (g : BoundedPolynomial F m d) := (L u).effect (f u g)
  let H (u : Point F m) := U.sandwichBy (L u) (f u)
  let S (u : Point F m) (g : BoundedPolynomial F m d) := (H u).effect (some g)
  let D (u : Point F m) := (H u).successfulEffect
  have hS (u g) : S u g = X u g * U.effect g * X u g := by
    simp only [S, H, X, sandwichBy_effect_some]
  have hST (u h g) : Commute (S u h) (T.effect g) := by
    rw [hS]
    exact ((hLT u g _).mul_left (hUT h g)).mul_left (hLT u g _)
  have hSR (u v g b) : Commute (S u g) ((R v).effect b) := by
    rw [hS]
    exact ((hLR u v _ b).mul_left (hUR g v b)).mul_left (hLR u v _ b)
  have hD u : D u ∈ Set.Icc (0 : A) 1 := by
    refine ⟨sum_nonneg fun g _ => (H u).nonneg (some g), ?_⟩
    rw [← sub_nonneg, ← (H u).effect_none_eq_one_sub_successfulEffect]
    exact (H u).nonneg none
  have hDT (u g) : Commute (D u) (T.effect g) :=
    Commute.sum_left _ _ _ fun h _ => hST u h g
  have hdiag : (∑ g, (φ (P.effect (some g) * Q.effect (some g))).re) =
      𝔼 u : Point F m, ∑ g, (φ (S u g * Q.effect (some g))).re := by
    rw [expect_sum_comm]
    refine sum_congr rfl fun g _ => ?_
    rw [show P = sandwichedPolynomialMeasurement L U from rfl,
      sandwichedPolynomialMeasurement_effect_some, smul_mul_assoc, sum_mul,
      AlgState.re_apply_uniformAverage]
    simp only [hS, X, f]
  have ht := abs_sandwichedPolynomial_score_sub_le φ L R T S
    (fun u g => ⟨(H u).nonneg _, (H u).effect_le_one _⟩)
    (fun u g => hST u g g) (fun u v g b => hSR u v g b) hLT
  change |(𝔼 u : Point F m, ∑ g, (φ (S u g * Q.effect (some g))).re) -
    (𝔼 u : Point F m, ∑ g, (φ (X u g * S u g * X u g * T.effect g)).re)| ≤ _ at ht
  rw [← hdiag] at ht
  let w (u : Point F m) (g h : BoundedPolynomial F m d) :=
    (φ (X u g * (U.effect h * T.effect g) * X u g)).re
  have hxproj (u g) : X u g * X u g = X u g := hL u _
  have hink (u g h) : S u h * T.effect g * X u g =
      if f u h = f u g then X u g * (U.effect h * T.effect g) * X u g else 0 := by
    have hc : Commute (X u h) (T.effect g) := hLT u g (f u h)
    have heq : S u h * T.effect g * X u g =
        X u h * (U.effect h * T.effect g) * (X u h * X u g) := by
      rw [hS, mul_assoc (X u h * U.effect h) (X u h) (T.effect g), hc.eq]
      simp only [mul_assoc]
    rw [heq]
    by_cases he : f u h = f u g
    · have hh : X u h = X u g := congrArg (L u).effect he
      simp only [ite_eq_left he, hh, hxproj]
    · have hz : X u h * X u g = 0 := (hL u).mul_eq_zero he
      simp only [ite_eq_right he, hz, mul_zero]
  have hdiagTerm (u g) :
      (φ (X u g * S u g * X u g * T.effect g)).re = w u g g := by
    change _ = (φ (X u g * (U.effect g * T.effect g) * X u g)).re
    apply congrArg (fun y => (φ y).re)
    rw [hS]
    calc
      _ = (X u g * X u g) * U.effect g * (X u g * X u g) * T.effect g := by
        simp only [mul_assoc]
      _ = _ := by
        have hc : Commute (X u g) (T.effect g) := hLT u g (f u g)
        simp only [hxproj, mul_assoc]
        rw [hc.eq]
  have hs (u g) : (φ (D u * T.effect g * X u g)).re =
      (φ (X u g * S u g * X u g * T.effect g)).re +
        ∑ h with h ≠ g ∧ f u h = f u g, w u g h := by
    change (φ ((∑ h, S u h) * T.effect g * X u g)).re = _
    simp only [sum_mul, map_sum, Complex.re_sum, hink, hdiagTerm]
    have hg : (∑ h, if h = g then w u g g else 0) = w u g g := by simp
    rw [← hg, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun h _ => ?_
    by_cases he : h = g
    · subst h
      simp [w]
    · by_cases hf : f u h = f u g <;> simp [he, hf, w]
  have hsplit :
      (𝔼 u : Point F m, ∑ g, (φ (D u * T.effect g * X u g)).re) =
      (𝔼 u : Point F m, ∑ g, (φ (X u g * S u g * X u g * T.effect g)).re) +
        (𝔼 u : Point F m, ∑ g, ∑ h with h ≠ g ∧ f u h = f u g, w u g h) := by
    simp only [hs, sum_add_distrib, expect_add_distrib]
  have hcollision := average_polynomialCollision_sandwich_le φ L U T hUT
  change (𝔼 u : Point F m, ∑ g, ∑ h with h ≠ g ∧ f u h = f u g, w u g h) ≤ _
    at hcollision
  have htransport := average_majorant_mul_le φ L R T Z hslack D hD hDT
  change _ ≤ (𝔼 u : Point F m, ∑ g, (φ (D u * T.effect g * X u g)).re) + _ + _
    at htransport
  rw [hsplit] at htransport
  have hSZ (u g) : Commute (S u g) Z := by
    rw [hS]
    exact ((hLZ u _).mul_left (hUZ g)).mul_left (hLZ u _)
  have hmaj : (𝔼 u : Point F m, ∑ g, (φ (S u g * averagePolynomialPointEffect R g)).re) ≤
      𝔼 u : Point F m, (φ (D u * Z)).re := by
    refine expect_le_expect fun u _ => ?_
    change _ ≤ (φ ((∑ g, S u g) * Z)).re
    simp only [sum_mul, map_sum, Complex.re_sum]
    refine sum_le_sum fun g _ => φ.re_apply_mono ?_
    have hc := (hSZ u g).sub_right
      (commute_averagePolynomialPointEffect R g _ (fun v b => hSR u v g b))
    simpa only [mul_sub, sub_nonneg] using
      hc.mul_nonneg ((H u).nonneg (some g)) (sub_nonneg.mpr (hle g))
  have hmean (u g) : (φ (S u g * averagePolynomialPointEffect R g)).re =
      𝔼 v : Point F m, (φ (S u g * (R v).effect (f v g))).re := by
    rw [averagePolynomialPointEffect_eq, mul_smul_comm, mul_sum, AlgState.re_apply_uniformAverage]
  have hscore (v : Point F m) :
      (𝔼 u : Point F m, ∑ g, (φ (S u g * (R v).effect (f v g))).re) =
        ∑ g, (φ (P.effect (some g) * (R v).effect (f v g))).re := by
    rw [expect_sum_comm]
    refine sum_congr rfl fun g _ => ?_
    rw [show P = sandwichedPolynomialMeasurement L U from rfl,
      sandwichedPolynomialMeasurement_effect_some, smul_mul_assoc, sum_mul,
      AlgState.re_apply_uniformAverage]
    simp only [hS, X, f]
  have heq (v : Point F m) :
      (∑ g, (φ (P.effect (some g) * (R v).effect (f v g))).re) =
        (φ P.successfulEffect).re - successfulMismatch φ (evaluatePolynomialMeasurement P v) (R v)
      := by
    rw [successfulMismatch_evaluate_eq_sum]
    simp only [mul_sub, mul_one, map_sub, Complex.sub_re, sum_sub_distrib,
      ← Complex.re_sum, ← map_sum, successfulEffect, sub_sub_cancel, f]
  simp only [hmean, ← expect_sum_comm] at hmaj
  rw [expect_comm] at hmaj
  simp only [hscore, heq, expect_sub_distrib, Fintype.expect_const] at hmaj
  have hmis := average_successfulMismatch_sandwichedPolynomial_le φ R L U hR
    (fun u v a b => (hLR v u b a).symm) (fun u g b => (hUR g u b).symm)
  have hsym (u : Point F m) : copyDefect φ (L u) (R u) = copyDefect φ (R u) (L u) := by
    unfold copyDefect
    exact sum_congr rfl fun a _ => by rw [φ.norm_sub_comm]
  simp only [hsym] at hmis
  linarith only [(abs_le.mp ht).1, htransport, hcollision, hmaj, hmis]

end Cslib.PCP.LowIndividualDegree

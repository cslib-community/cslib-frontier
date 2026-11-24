/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PointVariance
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialEvaluationCollision
import CslibFrontier.Foundations.Quantum.Algebra.CompletedMeasurement
import CslibFrontier.Foundations.Quantum.Algebra.SandwichedMeasurement

/-!
# Polynomial collisions in self-improvement

Different polynomial outcomes can agree at a sampled point. First replace
the surrounding point effects by their versions at an independent point.
After this replacement the outcome weights are independent of the collision
event, so Schwartz–Zippel applies. This is the off-diagonal estimate in the
proof of strong self-consistency in §9.2 of [JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.average_polynomialCollision_sandwich_le`
  bounds the weighted off-diagonal contribution.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset MvPolynomial
open scoped BigOperators Real

variable {F A : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A step of strong self-consistency. The mass of distinct outcomes that
evaluate to the same point value is bounded by the weighted point variance
and the Schwartz–Zippel error. -/
theorem average_polynomialCollision_sandwich_le (φ : AlgState A)
    (L : Point F m → Measurement F A)
    (U T : Measurement (BoundedPolynomial F m d) A)
    (hUT : ∀ h g, Commute (U.effect h) (T.effect g)) :
    (𝔼 u : Point F m, ∑ g, ∑ h with h ≠ g ∧ eval u h.val = eval u g.val,
      let X := (L u).effect (eval u g.val)
      (φ (X * (U.effect h * T.effect g) * X)).re) ≤
      2 * √(weightedPointVariance φ L T) + (m : ℝ) * d / Fintype.card F := by
  classical
  let f (u : Point F m) (g : BoundedPolynomial F m d) := eval u g.val
  let X (u : Point F m) (g : BoundedPolynomial F m d) := (L u).effect (f u g)
  let C (u : Point F m) (g : BoundedPolynomial F m d) :=
    ∑ h with h ≠ g ∧ f u h = f u g, U.effect h
  let J (u v : Point F m) := ∑ g, (φ (X v g * (C u g * T.effect g) * X v g)).re
  let W (v : Point F m) (g h : BoundedPolynomial F m d) :=
    (φ (X v g * (U.effect h * T.effect g) * X v g)).re
  let e (u v : Point F m) := ∑ g, let D := X v g - X u g
    (φ (star D * T.effect g * D)).re
  let k : ℝ := (m : ℝ) * d / Fintype.card F
  have hC (u g) : C u g ∈ Set.Icc (0 : A) 1 := by
    refine ⟨sum_nonneg fun h _ => U.nonneg h, ?_⟩
    rw [← U.sum_effect]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun h _ _ => U.nonneg h
  have hCT (u g) : Commute (C u g) (T.effect g) :=
    Commute.sum_left _ _ _ fun h _ => hUT h g
  have hJ (u v) : J u v =
      ∑ g, ∑ h with h ≠ g ∧ f u h = f u g, W v g h := by
    simp only [J, C, W, sum_mul, mul_sum, map_sum, Complex.re_sum]
  have hstep (u v) : J u u ≤ J u v + 2 * √(e u v) := by
    have h := Measurement.abs_sum_weighted_sandwich_sub_le φ T (L v) (L u) (f v) (f u)
      (C u) (hC u) (hCT u)
    change |J u v - J u u| ≤ 2 * √(e u v) at h
    linarith only [(abs_le.mp h).1]
  have hW (v g h) : 0 ≤ W v g h := by
    have hp := star_left_conjugate_nonneg
      ((hUT h g).mul_nonneg (U.nonneg h) (T.nonneg g)) (X v g)
    rw [(L v).nonneg (f v g) |>.isSelfAdjoint.star_eq] at hp
    exact φ.re_apply_nonneg hp
  have htotal (v) : (∑ g, ∑ h, W v g h) ≤ 1 := by
    let P := T.sandwichBy (L v) (f v)
    have hp : P.successfulEffect ≤ 1 := by
      rw [← sub_nonneg, ← P.effect_none_eq_one_sub_successfulEffect]
      exact P.nonneg none
    have h := φ.re_apply_le_one hp
    simpa only [W, ← Complex.re_sum, ← map_sum, ← sum_mul, ← mul_sum, U.sum_effect,
      one_mul, Measurement.successfulEffect, P, Measurement.sandwichBy_effect_some] using h
  have hfixed (v) : (𝔼 u : Point F m, J u v) ≤ k := by
    simp only [hJ, sum_filter, expect_sum_comm]
    calc
      _ ≤ ∑ g, ∑ h, k * W v g h := by
        refine sum_le_sum fun g _ => sum_le_sum fun h _ => ?_
        by_cases hne : h = g
        · subst h
          simpa using mul_nonneg (show 0 ≤ k by unfold k; positivity) (hW v g g)
        · calc
            _ = (𝔼 u : Point F m, if f u h = f u g then (1 : ℝ) else 0) * W v g h := by
              rw [expect_mul]
              refine expect_congr rfl fun u _ => ?_
              by_cases he : f u h = f u g <;> simp [hne, he]
            _ ≤ _ := mul_le_mul_of_nonneg_right
              (expect_evaluation_collision_le g h (Ne.symm hne)) (hW v g h)
      _ ≤ _ := by
        simp only [← mul_sum]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (htotal v) (show 0 ≤ k by unfold k; positivity)
  have havg : (𝔼 u : Point F m, 𝔼 v : Point F m, J u v) ≤ k := by
    rw [expect_comm]
    simpa only [Fintype.expect_const] using
      (expect_le_expect (s := (univ : Finset (Point F m))) fun v _ => hfixed v)
  have hvar : (𝔼 u : Point F m, 𝔼 v : Point F m, √(e u v)) ≤ √(weightedPointVariance φ L T) := by
    simpa only [Fintype.expect_prod_type, weightedPointVariance] using
      Fintype.expect_sqrt_le_sqrt_expect (fun z : Point F m × Point F m => e z.1 z.2)
        (fun z => sum_nonneg fun g _ => φ.re_apply_nonneg
          (star_left_conjugate_nonneg (T.nonneg g) (X z.2 g - X z.1 g)))
  have h := expect_le_expect (s := (univ : Finset (Point F m))) fun u _ =>
    expect_le_expect (s := (univ : Finset (Point F m))) fun v _ => hstep u v
  simp only [Fintype.expect_const, expect_add_distrib, ← mul_expect] at h
  change (𝔼 u : Point F m, ∑ g, ∑ h with h ≠ g ∧ f u h = f u g, W u g h) ≤ _
  simp_rw [← hJ]
  linarith only [h, havg, hvar, show k = (m : ℝ) * d / Fintype.card F from rfl]

end Cslib.PCP.LowIndividualDegree

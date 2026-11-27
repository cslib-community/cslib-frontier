/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.AxisPolynomialAnswer
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Quantum.Algebra.CStar

/-!
# Weighted collisions of polynomial axis answers

A legal line answer can agree at the sampled point while differing on the
whole line. Conditioning on the line fixes the line measurement and the
polynomial restriction. The univariate root bound then controls this
collision probability, including when outcomes are weighted by an opposing
polynomial measurement. This is the collision step of §8 of
[JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.average_axisCollision_le` bounds the
  weighted collision term for any fixed coordinate.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset Function MvPolynomial
open scoped BigOperators

variable {F A : Type*} {n : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)

/-- The difference between accepting the correct value and accepting the whole
restriction is a collision effect. Its weighted state square costs at most
the degree divided by field size. -/
theorem average_axisCollision_le
    (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ)
    (T : Measurement (BoundedPolynomial F (n + 1) d) A)
    (hproj : ∀ L, (S.bob (.axis L)).IsProjective)
    (hcomm : ∀ u i g f, Commute (T.effect g) ((decodedCoordinate S.bob d u i).effect f))
    (i : Fin (n + 1)) :
    (𝔼 u : Point F (n + 1), ∑ g,
      let B := decodedCoordinate S.bob d u i
      let D := (B.map (fun f => f.value (u i))).effect (eval u g.val) -
        B.effect (axisRestriction u i g)
      (S.state (star D * T.effect g * D)).re) ≤ (d : ℝ) / Fintype.card F := by
  classical
  let B (u : Point F (n + 1)) := decodedCoordinate S.bob d u i
  let r (u : Point F (n + 1)) (g : BoundedPolynomial F (n + 1) d) := axisRestriction u i g
  let C u g := (B u).map (fun f => decide (f ≠ r u g ∧ f.value (u i) = (r u g).value (u i)))
  have he (u : Point F (n + 1)) (g : BoundedPolynomial F (n + 1) d) :
      ((B u).map (fun f => f.value (u i))).effect (eval u g.val) -
        (B u).effect (r u g) = (C u g).effect true := by
    have hv : (r u g).value (u i) = eval u g.val := by
      simp only [r, value_axisRestriction, update_eq_self]
    have hr : (B u).effect (r u g) =
        ∑ f, if f = r u g then (B u).effect f else 0 := by
      simp only [sum_ite_eq', mem_univ, ite_true]
    rw [Measurement.map_effect, hr]
    simp only [C, Measurement.map_effect, sum_filter, decide_eq_true_eq, ← sum_sub_distrib, hv]
    refine sum_congr rfl fun f _ => ?_
    by_cases h : f = r u g
    · subst f
      simp [hv]
    · simp [h]
  let w (u : Point F (n + 1)) (g : BoundedPolynomial F (n + 1) d)
      (f : PolynomialFunction F d) := (S.state (T.effect g * (B u).effect f)).re
  have hw (u : Point F (n + 1)) (g : BoundedPolynomial F (n + 1) d)
      (f : PolynomialFunction F d) : 0 ≤ w u g f :=
    S.state.re_apply_nonneg ((hcomm u i g f).mul_nonneg (T.nonneg g) ((B u).nonneg f))
  have hterm (u : Point F (n + 1)) (g : BoundedPolynomial F (n + 1) d) :
      (S.state (star ((C u g).effect true) * T.effect g * (C u g).effect true)).re =
        ∑ f, if f ≠ r u g ∧ f.value (u i) = (r u g).value (u i) then w u g f else 0 := by
    have hB : (B u).IsProjective := (hproj _).map _
    have hC : (C u g).IsProjective := hB.map _
    have hc : Commute (T.effect g) ((C u g).effect true) :=
      Measurement.commute_map_right _ _ _ (hcomm u i g) _
    rw [((C u g).nonneg true).isSelfAdjoint.star_eq, ← hc.eq, mul_assoc, hC true]
    simp only [C, Measurement.map_effect, mul_sum, map_sum, Complex.re_sum, sum_filter,
      decide_eq_true_eq, w]
    exact sum_congr rfl fun f _ => by split_ifs <;> simp
  change (𝔼 u : Point F (n + 1), ∑ g,
    let D := ((B u).map (fun f => f.value (u i))).effect (eval u g.val) - (B u).effect (r u g)
    (S.state (star D * T.effect g * D)).re) ≤ _
  simp only [he, hterm]
  rw [← Fintype.expect_expect_update _ i]
  have hBu (u : Point F (n + 1)) (t : F) : B (update u i t) = B u :=
    decodedCoordinate_update S.bob d u i t
  have hr (u : Point F (n + 1)) (t : F) (g : BoundedPolynomial F (n + 1) d) :
      r (update u i t) g = r u g := axisRestriction_update u i g t
  have hwUpdate (u : Point F (n + 1)) (t : F) (g : BoundedPolynomial F (n + 1) d)
      (f : PolynomialFunction F d) : w (update u i t) g f = w u g f := by
    simp only [w, hBu]
  simp only [hr, hwUpdate, update_self]
  conv_rhs => rw [← Fintype.expect_const (ι := Point F (n + 1)) ((d : ℝ) / Fintype.card F)]
  refine expect_le_expect fun u _ => ?_
  simp only [expect_sum_comm]
  have hnorm : (∑ g, ∑ f, w u g f) = 1 := by
    simp only [w, ← Complex.re_sum, ← map_sum, ← mul_sum, (B u).sum_effect, mul_one,
      T.sum_effect, S.state.map_one, Complex.one_re]
  rw [← mul_one ((d : ℝ) / Fintype.card F), ← hnorm]
  simp only [mul_sum]
  refine sum_le_sum fun g _ => sum_le_sum fun f _ => ?_
  by_cases h : f = r u g
  · subst f
    simpa using mul_nonneg (show 0 ≤ (d : ℝ) / Fintype.card F by positivity) (hw u g (r u g))
  · calc
      _ = (𝔼 t : F, if f.value t = (r u g).value t then (1 : ℝ) else 0) * w u g f := by
        rw [expect_mul]
        refine expect_congr rfl fun t _ => ?_
        by_cases ht : f.value t = (r u g).value t <;> simp [h, ht]
      _ ≤ _ := mul_le_mul_of_nonneg_right (expect_axisRestriction_collision_le u i g f h) (hw u g f)

end Cslib.PCP.LowIndividualDegree

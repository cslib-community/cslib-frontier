/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.AxisCollision
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PointVariance
import CslibFrontier.Foundations.Probability.InnerProductResampling
import CslibFrontier.Foundations.Quantum.Algebra.SandwichedMeasurement

/-!
# Point variance from verifier acceptance

To compare points on a shared axis, first replace each point answer by its
copy on the opposite side, then by the line answer's value, then by the
effect for the entire restricted polynomial. This last effect depends only
on the line. The consistency branch, the axis branch and the line collision
bound control these three replacements, respectively.

## Main results

* `Cslib.PCP.LowIndividualDegree.weightedPointVariance_le_verifier` bounds
  weighted point variance in terms of the verifier scores and degree.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset Function MvPolynomial
open scoped BigOperators

variable {F A : Type*} {n : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)

omit [Field F] [Fintype F] [DecidableEq F] in
private theorem norm_sub_sq_le_three (φ : AlgState A) (X Y Z C : A) :
    φ.norm (X - C) ^ 2 ≤
      3 * (φ.norm (X - Y) ^ 2 + φ.norm (Y - Z) ^ 2 + φ.norm (Z - C) ^ 2) := by
  have h₁ := φ.norm_add_le (X - Y) (Y - Z)
  have h₂ := φ.norm_add_le (X - Z) (Z - C)
  rw [sub_add_sub_cancel] at h₁ h₂
  have h := h₂.trans (add_le_add h₁ le_rfl)
  have hs := pow_le_pow_left₀ (φ.norm_nonneg _) h 2
  nlinarith only [hs, sq_nonneg (φ.norm (X - Y) - φ.norm (Y - Z)),
    sq_nonneg (φ.norm (X - Y) - φ.norm (Z - C)), sq_nonneg (φ.norm (Y - Z) - φ.norm (Z - C))]

/-- A step of the low-degree soundness proof. This version allows distinct
players' measurements and charges the factor for conditioning on the
point-first role of the actual verifier. The polynomial effects must
commute with the decoded opposing axis effects. -/
theorem weightedPointVariance_le_verifier (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ)
    (T : Measurement (BoundedPolynomial F (n + 1) d) A)
    (hproj : ∀ L, (S.bob (.axis L)).IsProjective)
    (hcomm : ∀ u i g f, Commute (T.effect g) ((decodedCoordinate S.bob d u i).effect f)) :
    weightedPointVariance S.state (decodedPoint S.bob) T ≤ (n + 1 : ℝ) *
      (6 * (2 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S) +
        4 * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) +
        (d : ℝ) / Fintype.card F)) := by
  classical
  let φ := S.state
  choose K hK using fun g => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (T.nonneg g)
  let f (u : Point F (n + 1)) (g : BoundedPolynomial F (n + 1) d) := eval u g.val
  let B (i : Fin (n + 1)) (u : Point F (n + 1)) := decodedCoordinate S.bob d u i
  let M (i : Fin (n + 1)) (u : Point F (n + 1)) := (B i u).map (fun a => a.value (u i))
  let X (u : Point F (n + 1)) g := K g * (decodedPoint S.bob u).effect (f u g)
  let Y (u : Point F (n + 1)) g := K g * (decodedPoint S.alice u).effect (f u g)
  let Z (i : Fin (n + 1)) (u : Point F (n + 1)) g := K g * (M i u).effect (f u g)
  let C (i : Fin (n + 1)) (u : Point F (n + 1)) g :=
    K g * (B i u).effect (axisRestriction u i g)
  have hnorm (g) (D : A) : φ.norm (K g * D) ^ 2 = (φ (star D * T.effect g * D)).re := by
    rw [AlgState.norm_sq, hK g, star_mul]
    simp only [mul_assoc]
  have hC (i : Fin (n + 1)) (u : Point F (n + 1)) (t : F) (g) :
      C i (update u i t) g = C i u g := by
    simp only [C, B, decodedCoordinate_update, axisRestriction_update]
  let e (i : Fin (n + 1)) (u : Point F (n + 1)) := ∑ g, φ.norm (X u g - C i u g) ^ 2
  let : InnerProductSpace ℝ φ.toPositiveLinearMap.PreGNS := InnerProductSpace.complexToReal
  have hlocal (i : Fin (n + 1)) :
      (𝔼 u : Point F (n + 1), 𝔼 t : F, ∑ g, φ.norm (X (update u i t) g - X u g) ^ 2) ≤
        2 * (𝔼 u : Point F (n + 1), e i u) := by
    simp only [e, expect_sum_comm, mul_sum]
    refine sum_le_sum fun g _ => ?_
    have h := Fintype.expect_expect_norm_sub_update_sq_le_two i
      (fun u => φ.toPreGNS (X u g)) (fun u => φ.toPreGNS (C i u g))
      (fun u t => congrArg φ.toPreGNS (hC i u t g))
    simp only [← map_sub] at h
    exact h
  have hvar : weightedPointResampling φ (decodedPoint S.bob) T ≤
      2 * (𝔼 i : Fin (n + 1), 𝔼 u : Point F (n + 1), e i u) := by
    rw [mul_expect]
    refine expect_le_expect fun i _ => ?_
    have h := hlocal i
    simpa only [X, ← mul_sub, hnorm, f, weightedPointResampling] using h
  let ec (u : Point F (n + 1)) := ∑ g, φ.norm (X u g - Y u g) ^ 2
  let ea (i : Fin (n + 1)) (u : Point F (n + 1)) := ∑ g, φ.norm (Y u g - Z i u g) ^ 2
  let er (i : Fin (n + 1)) (u : Point F (n + 1)) := ∑ g, φ.norm (Z i u g - C i u g) ^ 2
  have he (i : Fin (n + 1)) (u : Point F (n + 1)) : e i u ≤ 3 * (ec u + ea i u + er i u) := by
    simp only [e, ec, ea, er, ← sum_add_distrib, mul_sum]
    exact sum_le_sum fun g _ => norm_sub_sq_le_three φ _ _ _ _
  have hc : (𝔼 u : Point F (n + 1), ec u) ≤
      2 * (1 - (branchGame (F := F) n d .consistency).commutingWinProb S) := by
    refine (expect_le_expect fun u _ => ?_).trans (decodedPoint_stateDist_le S d)
    simp only [ec, X, Y, ← mul_sub, hnorm]
    exact φ.sum_weighted_conj_le_sum_norm_sq T (f u)
      (fun a => (decodedPoint S.bob u).effect a - (decodedPoint S.alice u).effect a)
  have ha : (𝔼 i : Fin (n + 1), 𝔼 u : Point F (n + 1), ea i u) ≤
      4 * (1 - (branchGame (F := F) n d .axis).commutingWinProb S) := by
    rw [expect_comm]
    refine (expect_le_expect fun u _ => expect_le_expect fun i _ => ?_).trans
      (axisPointStateDist_le S d)
    simp only [ea, Y, Z, ← mul_sub, hnorm]
    exact φ.sum_weighted_conj_le_sum_norm_sq T (f u)
      (fun a => (decodedPoint S.alice u).effect a - (M i u).effect a)
  have hr : (𝔼 i : Fin (n + 1), 𝔼 u : Point F (n + 1), er i u) ≤
      (d : ℝ) / Fintype.card F := by
    conv_rhs => rw [← Fintype.expect_const (ι := Fin (n + 1)) ((d : ℝ) / Fintype.card F)]
    refine expect_le_expect fun i _ => ?_
    simpa only [er, Z, C, ← mul_sub, hnorm, M, B, f] using
      average_axisCollision_le S d T hproj hcomm i
  have hall := expect_le_expect (s := (univ : Finset (Fin (n + 1)))) fun i _ =>
    expect_le_expect (s := (univ : Finset (Point F (n + 1)))) fun u _ => he i u
  simp only [← mul_expect, expect_add_distrib, Fintype.expect_const] at hall
  have hn : 0 ≤ (n + 1 : ℝ) := by positivity
  have hglobal := weightedPointVariance_le_resampling φ (decodedPoint S.bob) T
  rw [Nat.cast_succ] at hglobal
  refine hglobal.trans
    (mul_le_mul_of_nonneg_left ?_ hn)
  linarith only [hvar, hall, hc, ha, hr]

end Cslib.PCP.LowIndividualDegree

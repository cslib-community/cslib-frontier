/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SliceCommutativity
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialEvaluationCollision
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Quantum.Algebra.OutcomeCommutator

/-!
# Commutation of polynomial slice outcomes

Schwartz–Zippel bounds the probability that a random evaluation identifies two
distinct polynomial outcomes. Applying the commutator comparison to each
slice in turn recovers commutation for the original polynomial measurements.
This is the transfer used in Theorem 11.4 of [JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.polynomialSlice_successfulPairDefect_le`
  derives the original slice commutator bound from the verifier and slice hypotheses.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset MvPolynomial
open scoped BigOperators Real

variable {F A : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Recover commutation before evaluation from the averaged evaluated commutators.
A copy of each original slice on a commuting side pays for the comparison. -/
theorem successfulPairDefect_le_evaluatedSlices (φ : AlgState A)
    (M N : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ x, (M x).IsProjective) (hN : ∀ x, (N x).IsProjective)
    (hc : ∀ x y a b, Commute ((M x).effect a) ((N y).effect b)) :
    let P (w : Point F (m + 1)) :=
      evaluatePolynomialMeasurement (M (w (Fin.last m))) (Fin.init w)
    (𝔼 x, 𝔼 y, Measurement.successfulPairDefect φ (M x) (M y)) ≤
      16 * (𝔼 u, 𝔼 v, Measurement.successfulPairDefect φ (P u) (P v)) +
        30 * (𝔼 x, Measurement.successfulCopyDefect φ (M x) (N x)) +
        20 * ((m : ℝ) * d / Fintype.card F) := by
  intro P
  let κ := (m : ℝ) * d / Fintype.card F
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  let c (x : F) := Measurement.successfulCopyDefect φ (M x) (N x)
  let E (x : F) (u : Point F m) := evaluatePolynomialMeasurement (M x) u
  let f (u : Point F m) (g : BoundedPolynomial F m d) := eval u g.val
  have he (x : F) (u : Point F m) : (E x u).IsProjective :=
    (hM x).map (Option.map (f u))
  have h₁ (x y : F) :
      Measurement.successfulPairDefect φ (M x) (M y) ≤
        4 * (𝔼 u, Measurement.successfulPairDefect φ (E x u) (M y)) + 6 * c x + 4 * κ :=
    Measurement.successfulPairDefect_le_average_map φ (M x) (N x) (M y)
      (hM x) (hN x) (hM y) (hc x x) (fun a b => (hc y x b a).symm) f hκ
      expect_evaluation_collision_le
  have h₂ (x y : F) (u : Point F m) :
      Measurement.successfulPairDefect φ (E x u) (M y) ≤
        4 * (𝔼 v, Measurement.successfulPairDefect φ (E x u) (E y v)) + 6 * c y + 4 * κ := by
    rw [Measurement.successfulPairDefect_comm φ (E x u) (M y)]
    simp_rw [Measurement.successfulPairDefect_comm φ (E x u) (E y _)]
    exact Measurement.successfulPairDefect_le_average_map φ (M y) (N y) (E x u)
      (hM y) (hN y) (he x u) (hc y y)
      (fun a b => Measurement.commute_map_right (M x) (Option.map (f u)) _ (fun a' =>
        (hc x y a' a).symm) b) f hκ expect_evaluation_collision_le
  have hpoint (x y : F) :
      Measurement.successfulPairDefect φ (M x) (M y) ≤
        16 * (𝔼 u, 𝔼 v, Measurement.successfulPairDefect φ (E x u) (E y v)) +
          6 * c x + 24 * c y + 20 * κ := by
    have h := expect_le_expect (s := (univ : Finset (Point F m))) fun u _ => h₂ x y u
    simp only [expect_add_distrib, Fintype.expect_const, ← mul_expect] at h
    linarith only [h, h₁ x y]
  have havg := expect_le_expect (s := (univ : Finset F)) fun x _ =>
    expect_le_expect (s := (univ : Finset F)) fun y _ => hpoint x y
  simp only [expect_add_distrib, Fintype.expect_const, ← mul_expect] at havg
  have hmean :
      (𝔼 x : F, 𝔼 y : F, 𝔼 u : Point F m, 𝔼 v : Point F m,
        Measurement.successfulPairDefect φ (E x u) (E y v)) =
        𝔼 u, 𝔼 v, Measurement.successfulPairDefect φ (P u) (P v) := by
    rw [Fintype.expect_eq_expect_snoc]
    simp_rw [Fintype.expect_eq_expect_snoc
      (fun v => Measurement.successfulPairDefect φ (P _) (P v)), P, Fin.snoc_last, Fin.init_snoc]
    refine expect_congr rfl fun x _ => ?_
    rw [expect_comm univ univ]
  rw [hmean] at havg
  change _ ≤ 16 * (𝔼 u, 𝔼 v, Measurement.successfulPairDefect φ (P u) (P v)) +
    30 * (𝔼 x, c x) + 20 * κ
  linarith only [havg]

/-- The original successful polynomial effects approximately commute under the
point agreement, copy agreement and failure bounds of the slice construction. -/
theorem polynomialSlice_successfulPairDefect_le
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) A)
    (hPoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLine : ∀ L, (S.bob (.diagonal L)).IsProjective) (degree : ℕ)
    (M N : F → Measurement (Option (BoundedPolynomial F m d)) A)
    (hM : ∀ x, (M x).IsProjective) (hN : ∀ x, (N x).IsProjective)
    (hMN : ∀ x y a b, Commute ((M x).effect a) ((N y).effect b))
    (Z : F → A) (hZ : ∀ x, 0 ≤ Z x)
    (hbound : ∀ x (g : BoundedPolynomial F m d),
      averagePolynomialPointEffect (fun u => decodedPoint S.alice (Fin.snoc u x)) g ≤ Z x)
    (hMP : ∀ x w g a, Commute ((M x).effect g) ((decodedPoint S.alice w).effect a))
    (hMZ : ∀ x y g, Commute ((M x).effect g) (Z y))
    {η ζ ξ : ℝ}
    (hcopy : (𝔼 x, Measurement.successfulCopyDefect S.state (M x) (N x)) ≤ ξ)
    (hfail : (𝔼 x : F, (S.state ((M x).effect none * Z x)).re) ≤ ζ)
    (hpoint : (𝔼 w : Point F (m + 1), Measurement.successfulMismatch S.state
      (evaluatePolynomialMeasurement (M (w (Fin.last m))) (Fin.init w))
      (decodedPoint S.alice w)) ≤ η) :
    (𝔼 x, 𝔼 y, Measurement.successfulPairDefect S.state (M x) (M y)) ≤
      32 * (4 * √(2 * η) + 2 * √(64 * (m + 1 : ℝ) *
        (1 - (branchGame (F := F) m degree .diagonal).commutingWinProb S)) +
        2 * √ζ + 2 * √ξ) + 30 * ξ + 20 * ((m : ℝ) * d / Fintype.card F) := by
  have he := evaluatedSlice_successfulPairDefect_le S hPoint hLine degree M hM Z hZ hbound hMP hMZ
    N hN hMN hcopy hfail hpoint
  exact (successfulPairDefect_le_evaluatedSlices S.state M N hM hN hMN).trans
    (by linarith only [he, hcopy])

end Cslib.PCP.LowIndividualDegree

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SelfImprovementSandwich
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerifierPointVariance
import CslibFrontier.Foundations.Quantum.Algebra.CStar

/-!
# Self-improvement bounds from the verifier

For a polynomial measurement on the point player's side, combine weighted
point variance from the actual verifier with the sandwiched-measurement
estimates. The bounds cover point disagreement and the dual-majorant gap.
Obtaining the measurement and majorant uses the finite-dimensional SDP,
and strong self-consistency is a separate step.

## Main results

* `Cslib.PCP.LowIndividualDegree.sandwichedPolynomial_point_bounds_of_verifier`
  gives the two bounds from verifier acceptance and the dual slack equations.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset
open scoped BigOperators Real

variable {F A : Type*} {n : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)

/-- Two steps of nonprojective self-improvement. The verifier scores control
disagreement on success and the gap between agreement and the state value of
the dual majorant. The polynomial measurement commutes with Bob's effects. -/
theorem sandwichedPolynomial_point_bounds_of_verifier (S : CommutingStrategy Q Q Ans Ans A)
    (d : ℕ) (T : Measurement (BoundedPolynomial F (n + 1) d) A) (Z : A)
    (hpoint : ∀ u, (S.bob (.point u)).IsProjective)
    (haxis : ∀ L, (S.bob (.axis L)).IsProjective)
    (hT : ∀ q g b, Commute (T.effect g) ((S.bob q).effect b))
    (hslack : ∀ g, T.effect g * Z = T.effect g *
      averagePolynomialPointEffect (decodedPoint S.alice) g) :
    let L := decodedPoint S.bob
    let R := decodedPoint S.alice
    let H := sandwichedPolynomialMeasurement R T
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb S
    let ε := 1 - (branchGame (F := F) n d .axis).commutingWinProb S
    let ξ := (n + 1 : ℝ) * (6 * (2 * δ + 4 * ε + (d : ℝ) / Fintype.card F))
    (𝔼 u : Point F (n + 1), Measurement.successfulMismatch S.state
      (evaluatePolynomialMeasurement H u) (L u)) ≤ 2 * √(2 * δ) + 2 * √ξ ∧
    (S.state Z).re - (𝔼 u : Point F (n + 1), ∑ b,
      (S.state ((evaluatePolynomialMeasurement H u).effect (some b) * (L u).effect b)).re) ≤
      5 * √(2 * δ) + 2 * √ξ := by
  classical
  intro L R H δ ε ξ
  have hL (u : Point F (n + 1)) : (L u).IsProjective := (hpoint u).map _
  have hLR (u v : Point F (n + 1)) (a b : F) : Commute ((L u).effect a) ((R v).effect b) :=
    (Measurement.commute_map_map _ _ (S.commute (.point v) (.point u)) decodePoint decodePoint
      b a).symm
  have hLT (u : Point F (n + 1)) g (b : F) : Commute ((L u).effect b) (T.effect g) :=
    (Measurement.commute_map_right (S.bob (.point u)) decodePoint _ (hT (.point u) g) b).symm
  have hvar : weightedPointVariance S.state L T ≤ ξ := by
    apply weightedPointVariance_le_verifier S d T haxis
    intro u i g f
    exact Measurement.commute_map_right _ _ _ (hT (.axis (coordinateLine u i)) g) f
  have hcopy : (𝔼 u : Point F (n + 1), Measurement.copyDefect S.state (R u) (L u)) ≤ 2 * δ := by
    simpa only [Measurement.copyDefect, R, L,
      S.state.norm_sub_comm ((decodedPoint S.alice _).effect _) ((decodedPoint S.bob _).effect _)]
      using decodedPoint_stateDist_le S d
  constructor
  · exact (average_successfulMismatch_sandwichedPolynomial_le S.state L R T hL hLR hLT).trans
      (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcopy) (by norm_num))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) (by norm_num)))
  · exact (majorant_sub_sandwichedPolynomial_agreement_le S.state L R T hL hLR hLT Z hslack).trans
      (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcopy) (by norm_num))
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) (by norm_num)))

end Cslib.PCP.LowIndividualDegree

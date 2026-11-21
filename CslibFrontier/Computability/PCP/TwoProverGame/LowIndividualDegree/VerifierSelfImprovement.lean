/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SelfImprovementConsistency
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerifierPointVariance
import CslibFrontier.Foundations.Quantum.Algebra.CStar

/-!
# Self-improvement bounds from the verifier

For a polynomial measurement on the point player's side, combine weighted
point variance from the actual verifier with the sandwiched-measurement
estimates. The bounds cover point disagreement and the dual-majorant gap.
The two-sided estimate also controls strong self-consistency from
the verifier scores and the dual certificate.

## Main results

* `Cslib.PCP.LowIndividualDegree.sandwichedPolynomial_point_bounds_of_verifier`
  gives the two bounds from verifier acceptance and the dual slack equations.
* `Cslib.PCP.LowIndividualDegree.successfulMass_sub_sandwichedAgreement_le_of_verifier`
  bounds strong self-consistency of the two sandwiched measurements.
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

/-- Strong self-consistency from the actual low-degree verifier. The two
polynomial measurements are on the respective sides, and the majorant
certifies the right-hand polynomial measurement. -/
theorem successfulMass_sub_sandwichedAgreement_le_of_verifier
    (S : CommutingStrategy Q Q Ans Ans A) (d : ℕ)
    (U T : Measurement (BoundedPolynomial F (n + 1) d) A) (Z : A)
    (hLpoint : ∀ u, (S.bob (.point u)).IsProjective)
    (hRpoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLaxis : ∀ L, (S.bob (.axis L)).IsProjective)
    (hRaxis : ∀ L, (S.alice (.axis L)).IsProjective)
    (hT : ∀ q g b, Commute (T.effect g) ((S.bob q).effect b))
    (hU : ∀ q g a, Commute (U.effect g) ((S.alice q).effect a))
    (hUT : ∀ h g, Commute (U.effect h) (T.effect g))
    (hZ : ∀ q b, Commute ((S.bob q).effect b) Z)
    (hUZ : ∀ g, Commute (U.effect g) Z)
    (hle : ∀ g : BoundedPolynomial F (n + 1) d,
      averagePolynomialPointEffect (decodedPoint S.alice) g ≤ Z)
    (hslack : ∀ g, T.effect g * Z = T.effect g *
      averagePolynomialPointEffect (decodedPoint S.alice) g) :
    let P := sandwichedPolynomialMeasurement (decodedPoint S.bob) U
    let H := sandwichedPolynomialMeasurement (decodedPoint S.alice) T
    let δ (S' : CommutingStrategy Q Q Ans Ans A) :=
      1 - (branchGame (F := F) n d .consistency).commutingWinProb S'
    let ε (S' : CommutingStrategy Q Q Ans Ans A) :=
      1 - (branchGame (F := F) n d .axis).commutingWinProb S'
    let ξ (S' : CommutingStrategy Q Q Ans Ans A) :=
      (n + 1 : ℝ) * (6 * (2 * δ S' + 4 * ε S' + (d : ℝ) / Fintype.card F))
    (S.state P.successfulEffect).re -
      ∑ g, (S.state (P.effect (some g) * H.effect (some g))).re ≤
      5 * √(2 * δ S) + 5 * √(ξ S) + 2 * √(ξ S.swap) +
        (n + 1 : ℝ) * d / Fintype.card F := by
  classical
  intro P H δ ε ξ
  let L := decodedPoint S.bob
  let R := decodedPoint S.alice
  have hL (u : Point F (n + 1)) : (L u).IsProjective := (hLpoint u).map _
  have hR (u : Point F (n + 1)) : (R u).IsProjective := (hRpoint u).map _
  have hLR (u v : Point F (n + 1)) (a b : F) : Commute ((L u).effect a) ((R v).effect b) :=
    (Measurement.commute_map_map _ _ (S.commute (.point v) (.point u)) decodePoint decodePoint
      b a).symm
  have hLT (u : Point F (n + 1)) g (a : F) : Commute ((L u).effect a) (T.effect g) :=
    (Measurement.commute_map_right (S.bob (.point u)) decodePoint _ (hT (.point u) g) a).symm
  have hUR (g) (u : Point F (n + 1)) (b : F) : Commute (U.effect g) ((R u).effect b) :=
    Measurement.commute_map_right (S.alice (.point u)) decodePoint _ (hU (.point u) g) b
  have hLZ (u : Point F (n + 1)) (a : F) : Commute ((L u).effect a) Z :=
    (Measurement.commute_map_right (S.bob (.point u)) decodePoint Z
      (fun b => (hZ (.point u) b).symm) a).symm
  have hvarL : weightedPointVariance S.state L T ≤ ξ S := by
    apply weightedPointVariance_le_verifier S d T hLaxis
    intro u i g f
    exact Measurement.commute_map_right _ _ _ (hT (.axis (coordinateLine u i)) g) f
  have hvarR : weightedPointVariance S.state R U ≤ ξ S.swap := by
    apply weightedPointVariance_le_verifier S.swap d U hRaxis
    intro u i g f
    exact Measurement.commute_map_right _ _ _ (hU (.axis (coordinateLine u i)) g) f
  have hcopy : (𝔼 u : Point F (n + 1), Measurement.copyDefect S.state (R u) (L u)) ≤ 2 * δ S := by
    simpa only [Measurement.copyDefect, R, L,
      S.state.norm_sub_comm ((decodedPoint S.alice _).effect _) ((decodedPoint S.bob _).effect _)]
      using decodedPoint_stateDist_le S d
  have h := successfulMass_sub_sandwichedAgreement_le S.state L R U T Z hL hR hLR hLT hUR
    hUT hLZ hUZ hle hslack
  simp only [Nat.cast_succ] at h
  exact h.trans (by gcongr)

end Cslib.PCP.LowIndividualDegree

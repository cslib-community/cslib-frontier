/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.SelfImprovementSDP
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerifierSelfImprovement
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.MaxEntangled

/-!
# Tensor-product self-improvement

The local self-improvement program supplies a polynomial POVM and a dual
majorant. Both embed in the two players' matrix algebras, where the verifier
bounds apply to the corresponding sandwiched measurements.

## Main results

* `Cslib.PCP.LowIndividualDegree.exists_tensorSelfImprovement` constructs the
  polynomial POVM and majorant and proves the four verifier bounds.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Matrix Finset
open scoped BigOperators Kronecker MatrixOrder ComplexOrder Real Matrix.Norms.L2Operator

variable {F ι κ : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Poly" => BoundedPolynomial F (n + 1) d
local notation "Local" => Matrix ι ι ℂ
local notation "Joint" => Matrix (ι × κ) (ι × κ) ℂ

private theorem kroneckerOne_decodedPoint (M : Q → POVM Ans ι) (u : Point F (n + 1)) (a : F) :
    (kroneckerOne ((decodedPoint (fun q => (M q).toMeasurement) u).effect a) : Joint) =
      (decodedPoint (fun q => QuantumStrategy.leftMeasurement (M q)) u).effect a := by
  simp only [decodedPoint, Measurement.map_effect, map_sum]
  rfl

private theorem kroneckerOne_averagePolynomialPointEffect
    (M : Q → POVM Ans ι) (g : Poly) :
    (kroneckerOne (averagePolynomialPointEffect
      (decodedPoint (fun q => (M q).toMeasurement)) g) : Joint) =
      averagePolynomialPointEffect (decodedPoint (fun q => QuantumStrategy.leftMeasurement
        (M q))) g := by
  rw [averagePolynomialPointEffect_eq, averagePolynomialPointEffect_eq]
  change ((kroneckerOne (κ := κ)).toAlgHom.restrictScalars ℝ) _ = _
  simp only [map_smul, map_sum, AlgHom.coe_restrictScalars', StarAlgHom.coe_toAlgHom,
    kroneckerOne_decodedPoint]

private theorem exists_leftSelfImprovementCertificate (M : Q → POVM Ans ι) :
    ∃ (T : POVM Poly ι) (Z : Local), 0 ≤ Z ∧
      (∀ g : Poly, averagePolynomialPointEffect (decodedPoint
        (fun q => QuantumStrategy.leftMeasurement (κ := κ) (M q))) g ≤ Z ⊗ₖ (1 : Matrix κ κ ℂ)) ∧
      (∀ g, (QuantumStrategy.leftMeasurement (κ := κ) T).effect g * (Z ⊗ₖ (1 : Matrix κ κ ℂ)) =
        (QuantumStrategy.leftMeasurement (κ := κ) T).effect g *
          averagePolynomialPointEffect (decodedPoint
            (fun q => QuantumStrategy.leftMeasurement (κ := κ) (M q))) g) := by
  classical
  obtain ⟨T, Z, hZ, hle, hslack, _, _, _⟩ := exists_selfImprovement_trace_certificate (d := d)
    (decodedPoint (fun q => (M q).toMeasurement))
  refine ⟨T.toPOVM, Z, hZ, ?_, ?_⟩
  · intro g
    rw [← kroneckerOne_averagePolynomialPointEffect]
    exact OrderHomClass.mono (kroneckerOne (κ := κ)) (hle g)
  · intro g
    rw [← kroneckerOne_averagePolynomialPointEffect]
    change kroneckerOne (κ := κ) (T.effect g) * kroneckerOne Z =
      kroneckerOne (T.effect g) * kroneckerOne (averagePolynomialPointEffect
        (decodedPoint (fun q => (M q).toMeasurement)) g)
    rw [← map_mul, ← map_mul, hslack]

/-- For a finite-dimensional strategy with projective point and axis effects,
the local SDP constructs sandwiched polynomial measurements whose successful
mass, point disagreement, dual gap and strong self-consistency are controlled
by the input agreement and the verifier losses. -/
theorem exists_tensorSelfImprovement
    (S : QuantumStrategy Q Q Ans Ans ι ι) (G : POVM (Option Poly) ι) (η : ℝ)
    (hLpoint : ∀ u, (S.toCommuting.bob (.point u)).IsProjective)
    (hRpoint : ∀ u, (S.toCommuting.alice (.point u)).IsProjective)
    (hLaxis : ∀ L, (S.toCommuting.bob (.axis L)).IsProjective)
    (hRaxis : ∀ L, (S.toCommuting.alice (.axis L)).IsProjective)
    (hinput : 1 - η ≤ 𝔼 u : Point F (n + 1), ∑ g : Poly,
      (S.toCommuting.state ((QuantumStrategy.rightMeasurement G).effect (some g) *
        (decodedPoint S.toCommuting.alice u).effect (MvPolynomial.eval u g.val))).re) :
    let C := S.toCommuting
    let δ (C' : CommutingStrategy Q Q Ans Ans (Matrix (ι × ι) (ι × ι) ℂ)) :=
      1 - (branchGame (F := F) n d .consistency).commutingWinProb C'
    let ε (C' : CommutingStrategy Q Q Ans Ans (Matrix (ι × ι) (ι × ι) ℂ)) :=
      1 - (branchGame (F := F) n d .axis).commutingWinProb C'
    let ξ C' := (n + 1 : ℝ) * (6 * (2 * δ C' + 4 * ε C' + (d : ℝ) / Fintype.card F))
    ∃ (T : POVM Poly ι) (Z : Local),
      let L := decodedPoint C.bob
      let R := decodedPoint C.alice
      let P := sandwichedPolynomialMeasurement L (QuantumStrategy.rightMeasurement T)
      let H := sandwichedPolynomialMeasurement R (QuantumStrategy.leftMeasurement T)
      let W := Z ⊗ₖ (1 : Local)
      0 ≤ W ∧
      (∀ g : Poly, averagePolynomialPointEffect R g ≤ W) ∧
      1 - η - 3 * √(2 * δ C) ≤ (C.state H.successfulEffect).re ∧
      (𝔼 u : Point F (n + 1), Measurement.successfulMismatch C.state
        (evaluatePolynomialMeasurement H u) (L u)) ≤ 2 * √(2 * δ C) + 2 * √(ξ C) ∧
      (C.state W).re - (𝔼 u : Point F (n + 1), ∑ b,
        (C.state ((evaluatePolynomialMeasurement H u).effect (some b) * (L u).effect b)).re) ≤
          5 * √(2 * δ C) + 2 * √(ξ C) ∧
      (C.state P.successfulEffect).re -
        ∑ g, (C.state (P.effect (some g) * H.effect (some g))).re ≤
          5 * √(2 * δ C) + 5 * √(ξ C) + 2 * √(ξ C.swap) +
            (n + 1 : ℝ) * d / Fintype.card F := by
  classical
  intro C δ ε ξ
  obtain ⟨T, Z, hZ, hle, hslack⟩ :=
    exists_leftSelfImprovementCertificate (κ := ι) (d := d) S.alice
  let R := decodedPoint C.alice
  let L := decodedPoint C.bob
  let U := QuantumStrategy.rightMeasurement (ι := ι) T
  let V := QuantumStrategy.leftMeasurement (κ := ι) T
  let W := Z ⊗ₖ (1 : Local)
  have hT (q g b) : Commute (V.effect g) ((C.bob q).effect b) :=
    commute_kroneckerOne_oneKronecker (T.effect g) ((S.bob q).effect b)
  have hU (q g a) : Commute (U.effect g) ((C.alice q).effect a) :=
    (commute_kroneckerOne_oneKronecker ((S.alice q).effect a) (T.effect g)).symm
  obtain ⟨hpoint, hgap⟩ := sandwichedPolynomial_point_bounds_of_verifier
    C d V W hLpoint hLaxis hT hslack
  have hstrong := successfulMass_sub_sandwichedAgreement_le_of_verifier
    C d U V W hLpoint hRpoint hLaxis hRaxis hT hU
    (fun h g => (commute_kroneckerOne_oneKronecker (T.effect g) (T.effect h)).symm)
    (fun q b => (commute_kroneckerOne_oneKronecker Z ((S.bob q).effect b)).symm)
    (fun g => (commute_kroneckerOne_oneKronecker Z (T.effect g)).symm) hle hslack
  have hcopy : (𝔼 u : Point F (n + 1), Measurement.copyDefect C.state (R u) (L u)) ≤
      2 * δ C := by
    simpa only [Measurement.copyDefect, R, L, δ, C.state.norm_sub_comm] using
      decodedPoint_stateDist_le C d
  have hmass := successfulMass_sandwichedPolynomial_lower_bound C.state L R V
    (fun u => (hLpoint u).map _) (fun u g b =>
      (Measurement.commute_map_right (C.bob (.point u)) decodePoint _ (hT (.point u) g) b).symm)
    (QuantumStrategy.rightMeasurement G) W hle hslack
    (fun g => (commute_kroneckerOne_oneKronecker Z (G.effect g)).symm)
    (fun g u b => Measurement.commute_map_right (C.alice (.point u)) decodePoint _
      (fun a =>
        (commute_kroneckerOne_oneKronecker ((S.alice (.point u)).effect a) (G.effect g)).symm) b)
  refine ⟨T, Z, (hZ.posSemidef.kronecker PosSemidef.one).nonneg, hle,
    ?_, hpoint, hgap, hstrong⟩
  exact (sub_le_sub hinput (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcopy)
    (by norm_num))).trans hmass

end Cslib.PCP.LowIndividualDegree

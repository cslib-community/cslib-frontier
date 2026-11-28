/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Unsymmetrize
import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialEvaluationCollision
import CslibFrontier.Foundations.Quantum.Algebra.CompletionConsistency
import CslibFrontier.Foundations.Quantum.Algebra.RelabelAgreement

/-!
# Agreement on full low-degree polynomial outcomes

Compare the two polynomial measurements after evaluating them at a uniform point.
The verifier's consistency branch and the two point-agreement estimates control
the evaluated disagreement. Schwartz–Zippel then bounds the extra agreement due
to distinct polynomials having the same value at that point. This is the step
through Equation (34) in [JNVWY2020LowIndividualDegree, §6].
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset
open scoped BigOperators MatrixOrder ComplexOrder Real Matrix.Norms.L2Operator

variable {F ι κ : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "Pt" => Point F (n + 1)
local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Poly" => BoundedPolynomial F (n + 1) d

/-- Opposite-player point agreement and the verifier's consistency score
control agreement on the full polynomial outcomes. -/
theorem polynomial_disagreement_le_of_point_agreement
    (S : QuantumStrategy Q Q Ans Ans ι κ)
    (Gₐ : POVM Poly ι) (Gᵦ : POVM Poly κ) {σₐ σᵦ : ℝ}
    (hₐ : (𝔼 u : Pt, (1 - Measurement.agreement S.toCommuting.state
      ((QuantumStrategy.leftMeasurement (κ := κ) Gₐ).map fun g => MvPolynomial.eval u g.val)
      (decodedPoint S.toCommuting.bob u))) ≤ σₐ)
    (hᵦ : (𝔼 u : Pt, (1 - Measurement.agreement S.toCommuting.state
      (decodedPoint S.toCommuting.alice u)
      ((QuantumStrategy.rightMeasurement (ι := ι) Gᵦ).map fun g => MvPolynomial.eval u g.val))) ≤
        σᵦ) :
    let C := S.toCommuting
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb C
    1 - Measurement.agreement C.state (QuantumStrategy.leftMeasurement (κ := κ) Gₐ)
        (QuantumStrategy.rightMeasurement (ι := ι) Gᵦ) ≤
      σₐ + √(4 * (σᵦ + δ)) + ((n + 1 : ℝ) * d / Fintype.card F) := by
  classical
  intro C δ
  let A := decodedPoint C.alice
  let B := decodedPoint C.bob
  let L := QuantumStrategy.leftMeasurement (κ := κ) Gₐ
  let R := QuantumStrategy.rightMeasurement (ι := ι) Gᵦ
  let f (u : Pt) (g : Poly) := MvPolynomial.eval u g.val
  let D₁ (u : Pt) := ∑ a, C.state.norm ((A u).effect a - (R.map (f u)).effect a) ^ 2
  let D₂ (u : Pt) := ∑ a, C.state.norm ((B u).effect a - (A u).effect a) ^ 2
  have h₁ : (𝔼 u : Pt, D₁ u) ≤ 2 * σᵦ := by
    have hcomm (u : Pt) (a : F) : Commute ((A u).effect a) ((R.map (f u)).effect a) :=
      Measurement.commute_map_map _ _
        (QuantumStrategy.commute_liftedEffects (S.alice (.point u)) Gᵦ) decodePoint (f u) a a
    calc
      _ ≤ 𝔼 u : Pt, (2 - 2 * Measurement.agreement C.state (A u) (R.map (f u))) :=
        expect_le_expect fun u _ => Measurement.sum_norm_sub_sq_le _ _ _ (hcomm u)
      _ ≤ _ := by
        simp only [expect_sub_distrib, Fintype.expect_const, ← mul_expect]
        simp only [expect_sub_distrib, Fintype.expect_const] at hᵦ
        linarith only [hᵦ]
  have h₂ : (𝔼 u : Pt, D₂ u) ≤ 2 * δ := decodedPoint_stateDist_le C d
  have htriangle :
      (𝔼 u : Pt, ∑ a, C.state.norm ((B u).effect a - (R.map (f u)).effect a) ^ 2) ≤
        4 * (σᵦ + δ) := by
    calc
      _ ≤ 𝔼 u : Pt, (2 * (D₂ u + D₁ u)) := expect_le_expect fun u _ =>
        Measurement.sum_norm_sub_sq_triangle C.state (B u) (A u) (R.map (f u))
      _ ≤ _ := by
        simp only [← mul_expect, expect_add_distrib]
        linarith only [h₁, h₂]
  have hvalue :
      (𝔼 u : Pt, (1 - Measurement.agreement C.state (L.map (f u)) (R.map (f u)))) ≤
        σₐ + √(4 * (σᵦ + δ)) :=
    Measurement.expect_one_sub_agreement_le_of_distance C.state _ _ _ hₐ htriangle
  have hpoly :
      (𝔼 u : Pt, Measurement.agreement C.state (L.map (f u)) (R.map (f u))) ≤
        Measurement.agreement C.state L R + ((n + 1 : ℝ) * d / Fintype.card F) := by
    apply Measurement.expect_agreement_map_le C.state L R f
      (QuantumStrategy.commute_liftedEffects Gₐ Gᵦ) (by positivity)
    intro g h hne
    simpa only [f, Nat.cast_add, Nat.cast_one] using expect_evaluation_collision_le h g hne.symm
  simp only [expect_sub_distrib, Fintype.expect_const] at hvalue
  change 1 - Measurement.agreement C.state L R ≤ _
  linarith only [hvalue, hpoly]

/-- The extracted local polynomial POVMs agree with the opposing point
measurements and with one another on their full outcomes. -/
theorem exists_consistent_polynomial_POVMs_of_projective {k : ℕ} (D : ℕ)
    (hk : (n + 1) * d ≤ k) (S : QuantumStrategy Q Q Ans Ans ι κ)
    (hA : ∀ q, (S.alice q).toMeasurement.IsProjective)
    (hB : ∀ q, (S.bob q).toMeasurement.IsProjective) :
    let C := S.toCommuting
    let ε := 1 - (branchGame (F := F) n d .axis).commutingWinProb C
    let δ := 1 - (branchGame (F := F) n d .consistency).commutingWinProb C
    let γ :=
      1 - (branchGameWithDiagonalCap (F := F) n d D .diagonal).commutingWinProb C
    let r := (d : ℝ) / Fintype.card F
    let σ := 320000 * dimensionInductionError (n + 1) k ε δ γ r
    ∃ (Gₐ : POVM Poly ι) (Gᵦ : POVM Poly κ),
      (𝔼 u : Pt, (1 - Measurement.agreement C.state (decodedPoint C.alice u)
        ((QuantumStrategy.rightMeasurement (ι := ι) Gᵦ).map
          fun g => MvPolynomial.eval u g.val))) ≤ σ ∧
      (𝔼 u : Pt, (1 - Measurement.agreement C.state
        ((QuantumStrategy.leftMeasurement (κ := κ) Gₐ).map fun g => MvPolynomial.eval u g.val)
        (decodedPoint C.bob u))) ≤ σ ∧
      1 - Measurement.agreement C.state (QuantumStrategy.leftMeasurement (κ := κ) Gₐ)
        (QuantumStrategy.rightMeasurement (ι := ι) Gᵦ) ≤ σ + √(4 * (σ + δ)) + (n + 1) * r := by
  intro C ε δ γ r σ
  obtain ⟨Gₐ, Gᵦ, hᵦ, hₐ⟩ := exists_local_polynomial_POVMs_of_projective D hk S hA hB
  refine ⟨Gₐ, Gᵦ, hᵦ, hₐ, ?_⟩
  simpa only [r, ← mul_div_assoc] using
    polynomial_disagreement_le_of_point_agreement S Gₐ Gᵦ hₐ hᵦ

end Cslib.PCP.LowIndividualDegree

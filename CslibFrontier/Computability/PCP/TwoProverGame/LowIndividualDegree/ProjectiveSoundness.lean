/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialAgreement
import CslibFrontier.Computability.PCP.TwoProverGame.ProjectiveAgreement
import CslibFrontier.Foundations.Quantum.Algebra.CompletionConsistency

/-!
# Projective soundness of the low-individual-degree test

Round the two consistent polynomial POVMs separately on their original spaces.
Agreement on full polynomial outcomes controls the change caused by rounding
also after grouping outcomes by evaluation. This proves a quantitative variant of
[JNVWY2020LowIndividualDegree, Theorem 3.10]. It uses the explicit induction,
collision and rounding errors given below in place of the source's common
1/40000-power error.
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

/-- For arbitrary projective tensor strategies, the two local projective
polynomial measurements agree on full outcomes and with the opposing players'
decoded point measurements. The bounds are those of the quantitative variant described
above. They use the three branch losses and allow an independent diagonal cutoff `D`.
Set `D = (n + 1) * d` for the Figure 2 verifier. -/
theorem exists_projective_polynomial_POVMs {k : ℕ} (D : ℕ)
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
    let ζ := σ + √(4 * (σ + δ)) + (n + 1) * r
    let pointError := σ + √(8 * ζ + 4 * √(18 * ζ))
    ∃ (Pₐ : POVM Poly ι) (Pᵦ : POVM Poly κ),
      Pₐ.toMeasurement.IsProjective ∧ Pᵦ.toMeasurement.IsProjective ∧
      (𝔼 u : Pt, (1 - Measurement.agreement C.state (decodedPoint C.alice u)
        ((QuantumStrategy.rightMeasurement (ι := ι) Pᵦ).map
          fun g => MvPolynomial.eval u g.val))) ≤ pointError ∧
      (𝔼 u : Pt, (1 - Measurement.agreement C.state
        ((QuantumStrategy.leftMeasurement (κ := κ) Pₐ).map
          fun g => MvPolynomial.eval u g.val) (decodedPoint C.bob u))) ≤ pointError ∧
      1 - Measurement.agreement C.state (QuantumStrategy.leftMeasurement (κ := κ) Pₐ)
        (QuantumStrategy.rightMeasurement (ι := ι) Pᵦ) ≤ ζ + 2 * √(18 * ζ) := by
  classical
  intro C ε δ γ r σ ζ pointError
  obtain ⟨Gₐ, Gᵦ, hpointB, hpointA, hpoly⟩ :=
    exists_consistent_polynomial_POVMs_of_projective D hk S hA hB
  let φ := C.state
  let L := QuantumStrategy.leftMeasurement (κ := κ) Gₐ
  let R := QuantumStrategy.rightMeasurement (ι := ι) Gᵦ
  let A := decodedPoint C.alice
  let B := decodedPoint C.bob
  let f (u : Pt) (g : Poly) := MvPolynomial.eval u g.val
  have hLR : 1 - ζ ≤ Measurement.agreement φ L R := by
    change 1 - Measurement.agreement φ L R ≤ ζ at hpoly
    linarith only [hpoly]
  obtain ⟨Pₐ, Pᵦ, hPₐ, hPᵦ, hL, hR⟩ :=
    QuantumStrategy.exists_projective_pair_of_agreement φ Gₐ Gᵦ hLR
  let PL := QuantumStrategy.leftMeasurement (κ := κ) Pₐ
  let PR := QuantumStrategy.rightMeasurement (ι := ι) Pᵦ
  change (∑ a, φ.norm (L.effect a - PL.effect a) ^ 2) ≤ 18 * ζ at hL
  change (∑ a, φ.norm (R.effect a - PR.effect a) ^ 2) ≤ 18 * ζ at hR
  have hrev : 1 - ζ ≤ Measurement.agreement φ R L := by
    rw [← Measurement.agreement_comm φ L R
      (fun a => QuantumStrategy.commute_liftedEffects Gₐ Gᵦ a a)]
    exact hLR
  have hdistR (u : Pt) :
      (∑ a, φ.norm ((R.map (f u)).effect a - (PR.map (f u)).effect a) ^ 2) ≤
        8 * ζ + 4 * √(18 * ζ) :=
    Measurement.sum_norm_sub_sq_map_le_of_agreement φ L R PR (f u)
      (QuantumStrategy.commute_liftedEffects Gₐ Gᵦ)
      (QuantumStrategy.commute_liftedEffects Gₐ Pᵦ) hLR hR
  have hdistL (u : Pt) :
      (∑ a, φ.norm ((L.map (f u)).effect a - (PL.map (f u)).effect a) ^ 2) ≤
        8 * ζ + 4 * √(18 * ζ) :=
    Measurement.sum_norm_sub_sq_map_le_of_agreement φ R L PL (f u)
      (fun a b => (QuantumStrategy.commute_liftedEffects Gₐ Gᵦ b a).symm)
      (fun a b => (QuantumStrategy.commute_liftedEffects Pₐ Gᵦ b a).symm) hrev hL
  have hswapPoint (M : POVM Poly ι) (u : Pt) :
      Measurement.agreement φ ((QuantumStrategy.leftMeasurement (κ := κ) M).map (f u)) (B u) =
        Measurement.agreement φ (B u) ((QuantumStrategy.leftMeasurement (κ := κ) M).map (f u)) := by
    apply Measurement.agreement_comm
    exact fun a => Measurement.commute_map_map _ _
      (QuantumStrategy.commute_liftedEffects M (S.bob (.point u))) (f u) decodePoint a a
  refine ⟨Pₐ, Pᵦ, hPₐ, hPᵦ, ?_, ?_, ?_⟩
  · exact Measurement.expect_one_sub_agreement_le_of_distance φ A (fun u => R.map (f u))
      (fun u => PR.map (f u)) hpointB
      ((expect_le_expect fun u _ => hdistR u).trans_eq (Fintype.expect_const _))
  · change (𝔼 u : Pt, (1 - Measurement.agreement φ (PL.map (f u)) (B u))) ≤ pointError
    simp only [PL, hswapPoint Pₐ]
    apply Measurement.expect_one_sub_agreement_le_of_distance φ B (fun u => L.map (f u))
      (fun u => PL.map (f u))
    · change (𝔼 u : Pt, (1 - Measurement.agreement φ (L.map (f u)) (B u))) ≤ σ at hpointA
      simpa only [L, hswapPoint Gₐ] using hpointA
    · exact (expect_le_expect fun u _ => hdistL u).trans_eq (Fintype.expect_const _)
  · change 1 - Measurement.agreement φ PL PR ≤ ζ + 2 * √(18 * ζ)
    have hright := (Measurement.abs_agreement_sub_right_le φ L R PR).trans (Real.sqrt_le_sqrt hR)
    have hleft := (Measurement.abs_agreement_sub_right_le φ PR L PL).trans (Real.sqrt_le_sqrt hL)
    rw [← Measurement.agreement_comm φ L PR
          (fun a => QuantumStrategy.commute_liftedEffects Gₐ Pᵦ a a),
        ← Measurement.agreement_comm φ PL PR
          (fun a => QuantumStrategy.commute_liftedEffects Pₐ Pᵦ a a)] at hleft
    linarith only [hLR, (abs_le.mp hright).2, (abs_le.mp hleft).2]

/-- Disagreement bounds for the low-individual-degree verifier. -/
structure SoundnessErrors where
  /-- The bound for evaluation at a uniform point compared with the other player's answer. -/
  point : ℝ
  /-- The bound for disagreement on the full polynomial outcomes. -/
  polynomial : ℝ

/-- The explicit soundness errors in dimension `m`, with sampling parameter `k`,
verifier rejection probability `ε`, and degree-to-field-size ratio `r`. -/
@[expose] noncomputable def soundnessErrors (m : ℝ) (k : ℕ) (ε r : ℝ) : SoundnessErrors :=
  let σ := 320000 * dimensionInductionError m k (3 * ε) (3 * ε) (3 * ε) r
  let ζ := σ + √(4 * (σ + 3 * ε)) + m * r
  ⟨σ + √(8 * ζ + 4 * √(18 * ζ)), ζ + 2 * √(18 * ζ)⟩

/-- Low-individual-degree soundness stated using the loss in the full verifier.
This specializes the quantitative variant above by substituting three times the full
verifier loss for each branch loss in the two fields of soundnessErrors. -/
theorem exists_projective_polynomial_POVMs_of_winProb {k : ℕ}
    (hk : (n + 1) * d ≤ k) (S : QuantumStrategy Q Q Ans Ans ι κ)
    (hA : ∀ q, (S.alice q).toMeasurement.IsProjective)
    (hB : ∀ q, (S.bob q).toMeasurement.IsProjective) :
    let C := S.toCommuting
    let ε := 1 - (game (F := F) n d).quantumWinProb S
    let r := (d : ℝ) / Fintype.card F
    let errors := soundnessErrors (n + 1) k ε r
    ∃ (Pₐ : POVM Poly ι) (Pᵦ : POVM Poly κ),
      Pₐ.toMeasurement.IsProjective ∧ Pᵦ.toMeasurement.IsProjective ∧
      (𝔼 u : Pt, (1 - Measurement.agreement C.state (decodedPoint C.alice u)
        ((QuantumStrategy.rightMeasurement (ι := ι) Pᵦ).map
          fun g => MvPolynomial.eval u g.val))) ≤ errors.point ∧
      (𝔼 u : Pt, (1 - Measurement.agreement C.state
        ((QuantumStrategy.leftMeasurement (κ := κ) Pₐ).map
          fun g => MvPolynomial.eval u g.val) (decodedPoint C.bob u))) ≤ errors.point ∧
      1 - Measurement.agreement C.state (QuantumStrategy.leftMeasurement (κ := κ) Pₐ)
        (QuantumStrategy.rightMeasurement (ι := ι) Pᵦ) ≤ errors.polynomial := by
  intro C ε r errors
  let σ := 320000 * dimensionInductionError (n + 1) k (3 * ε) (3 * ε) (3 * ε) r
  let ζ := σ + √(4 * (σ + 3 * ε)) + (n + 1) * r
  let loss (b : Branch) := 1 - (branchGame (F := F) n d b).commutingWinProb C
  let σ₀ := 320000 * dimensionInductionError (n + 1) k
    (loss .axis) (loss .consistency) (loss .diagonal) r
  let ζ₀ := σ₀ + √(4 * (σ₀ + loss .consistency)) + (n + 1) * r
  have hloss (b : Branch) : loss b ≤ 3 * ε := by
    change 1 - (branchGame (F := F) n d b).commutingWinProb C ≤
      3 * (1 - (game (F := F) n d).quantumWinProb S)
    rw [← TwoProverGame.commutingWinProb_toCommuting (game n d)]
    exact branch_loss_le_three_mul n d b C.answers
  have hnonneg (b : Branch) : 0 ≤ loss b :=
    sub_nonneg.mpr (TwoProverGame.commutingWinProb_le_one _ _)
  have hσ : σ₀ ≤ σ := by
    dsimp only [σ₀, σ, dimensionInductionError, inductionLossTerm]
    gcongr <;> first | exact hnonneg _ | exact hloss _
  have hζ : ζ₀ ≤ ζ := by
    dsimp only [ζ₀, ζ]
    gcongr
    exact hloss .consistency
  obtain ⟨Pₐ, Pᵦ, hPₐ, hPᵦ, hpointB, hpointA, hpoly⟩ :=
    exists_projective_polynomial_POVMs ((n + 1) * d) hk S hA hB
  rw [← branchGame_eq_withDiagonalCap] at hpointB hpointA hpoly
  have h₁ : σ₀ + √(8 * ζ₀ + 4 * √(18 * ζ₀)) ≤ errors.point := by
    change _ ≤ σ + √(8 * ζ + 4 * √(18 * ζ))
    gcongr
  have h₂ : ζ₀ + 2 * √(18 * ζ₀) ≤ errors.polynomial := by
    change _ ≤ ζ + 2 * √(18 * ζ)
    gcongr
  exact ⟨Pₐ, Pᵦ, hPₐ, hPᵦ, hpointB.trans h₁, hpointA.trans h₁, hpoly.trans h₂⟩

end Cslib.PCP.LowIndividualDegree

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.ProjectiveSoundness
import CslibFrontier.Computability.PCP.TwoProverGame.NaimarkAgreement

/-!
# Low-individual-degree soundness for arbitrary POVMs

Apply projective soundness to a Naimark dilation. Restrict the two polynomial
measurements to the prepared ancilla coordinates. Both the point agreements and
the full-polynomial agreement are preserved, with the same error bounds on the
original local spaces.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator

variable {F ι κ : Type*} {n d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "Pt" => Point F (n + 1)
local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)
local notation "Poly" => BoundedPolynomial F (n + 1) d

/-- Every finite tensor strategy admits polynomial POVMs on its original spaces.
Their evaluations agree with the opposing players' decoded point answers, and
their full polynomial outcomes agree with one another. Both disagreement bounds
depend on the rejection probability of the original verifier. -/
theorem exists_polynomial_POVMs_of_winProb {k : ℕ}
    (hk : (n + 1) * d ≤ k) (S : QuantumStrategy Q Q Ans Ans ι κ) :
    let C := S.toCommuting
    let errors := soundnessErrors (n + 1) k (1 - (game (F := F) n d).quantumWinProb S)
      ((d : ℝ) / Fintype.card F)
    ∃ (Pₐ : POVM Poly ι) (Pᵦ : POVM Poly κ),
      (𝔼 u : Pt, (1 - Measurement.agreement C.state (decodedPoint C.alice u)
        ((QuantumStrategy.rightMeasurement (ι := ι) Pᵦ).map
          fun g => MvPolynomial.eval u g.val))) ≤ errors.point ∧
      (𝔼 u : Pt, (1 - Measurement.agreement C.state
        ((QuantumStrategy.leftMeasurement (κ := κ) Pₐ).map
          fun g => MvPolynomial.eval u g.val) (decodedPoint C.bob u))) ≤ errors.point ∧
      1 - Measurement.agreement C.state (QuantumStrategy.leftMeasurement (κ := κ) Pₐ)
        (QuantumStrategy.rightMeasurement (ι := ι) Pᵦ) ≤ errors.polynomial := by
  intro C errors
  let _ : DecidableEq Ans := Classical.decEq _
  let a₀ : Ans := .inl 0
  let T := S.dilate a₀ a₀
  obtain ⟨L, R, _, _, h₁, h₂, h₃⟩ :=
    exists_projective_polynomial_POVMs_of_winProb hk T
      (S.isProjective_alice_dilate a₀ a₀) (S.isProjective_bob_dilate a₀ a₀)
  let Pₐ := L.restrictBasis (ancillaBasis a₀)
  let Pᵦ := R.restrictBasis (ancillaBasis a₀)
  let f (u : Pt) (g : Poly) := MvPolynomial.eval u g.val
  have hA (u : Pt) : Measurement.agreement T.toCommuting.state
      (decodedPoint T.toCommuting.alice u)
      ((QuantumStrategy.rightMeasurement (ι := ι × Ans) R).map (f u)) =
        Measurement.agreement C.state (decodedPoint C.alice u)
          ((QuantumStrategy.rightMeasurement (ι := ι) Pᵦ).map (f u)) := by
    simpa only [T, C, Pᵦ, decodedPoint, QuantumStrategy.toCommuting, QuantumStrategy.dilate,
      POVM.restrictBasis_dilate] using
      S.agreement_dilate_restrictBasis a₀ a₀ ((S.alice (.point u)).dilate a₀) R decodePoint (f u)
  have hB (u : Pt) : Measurement.agreement T.toCommuting.state
      ((QuantumStrategy.leftMeasurement (κ := κ × Ans) L).map (f u))
      (decodedPoint T.toCommuting.bob u) =
        Measurement.agreement C.state ((QuantumStrategy.leftMeasurement (κ := κ) Pₐ).map (f u))
          (decodedPoint C.bob u) := by
    simpa only [T, C, Pₐ, decodedPoint, QuantumStrategy.toCommuting, QuantumStrategy.dilate,
      POVM.restrictBasis_dilate] using
      S.agreement_dilate_restrictBasis a₀ a₀ L ((S.bob (.point u)).dilate a₀) (f u) decodePoint
  have hPoly : Measurement.agreement T.toCommuting.state
      (QuantumStrategy.leftMeasurement (κ := κ × Ans) L)
      (QuantumStrategy.rightMeasurement (ι := ι × Ans) R) =
        Measurement.agreement C.state (QuantumStrategy.leftMeasurement (κ := κ) Pₐ)
          (QuantumStrategy.rightMeasurement (ι := ι) Pᵦ) := by
    simpa only [Measurement.map_id] using S.agreement_dilate_restrictBasis a₀ a₀ L R id id
  have hscore : (game (F := F) n d).quantumWinProb T = (game (F := F) n d).quantumWinProb S :=
    (game n d).quantumWinProb_dilate S a₀ a₀
  simp only [f] at hA hB
  refine ⟨Pₐ, Pᵦ, ?_, ?_, ?_⟩
  · simpa only [hscore, hA] using h₁
  · simpa only [hscore, hB] using h₂
  · simpa only [hscore, hPoly] using h₃

end Cslib.PCP.LowIndividualDegree

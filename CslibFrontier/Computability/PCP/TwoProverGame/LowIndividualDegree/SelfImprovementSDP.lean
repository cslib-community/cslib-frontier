/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.PolynomialPointEffect
public import Mathlib.Data.Fintype.Option
import CslibFrontier.Foundations.Quantum.POVM.Optimization

/-!
# The low-individual-degree self-improvement SDP

The objective matrix for a polynomial is the average point effect for its
values. Lemma 9.2 of [JNVWY2020LowIndividualDegree] gives a complete polynomial
measurement and a common positive majorant of those objective matrices, with
the measurement effects annihilating the corresponding slacks.

## Main results

* `Cslib.PCP.LowIndividualDegree.exists_selfImprovement_trace_certificate`
  gives the optimal primal and dual solutions for the finite matrix problem.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Quantum Finset Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {F ι : Type*} {m d : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

/-- The self-improvement SDP has a complete polynomial measurement and a positive dual
majorant with complementary slackness and equal primal and dual values. The primal
variables range over polynomial submeasurements, represented with a failure outcome.
The dual variables range over all common majorants of the averaged point effects. -/
theorem exists_selfImprovement_trace_certificate
    (B : (Fin m → F) → Measurement F (Matrix ι ι ℂ)) :
    ∃ (T : Measurement (BoundedPolynomial F m d) (Matrix ι ι ℂ)) (Z : Matrix ι ι ℂ),
      0 ≤ Z ∧ (∀ g : BoundedPolynomial F m d, averagePolynomialPointEffect B g ≤ Z) ∧
      (∀ g, T.effect g * Z = T.effect g * averagePolynomialPointEffect B g) ∧
      (∑ g, (T.effect g * averagePolynomialPointEffect B g).trace) = Z.trace ∧
      (∀ G : Measurement (Option (BoundedPolynomial F m d)) (Matrix ι ι ℂ),
        ∑ g, (G.effect (some g) * averagePolynomialPointEffect B g).trace ≤ Z.trace) ∧
      (∀ W : Matrix ι ι ℂ,
        (∀ g : BoundedPolynomial F m d, averagePolynomialPointEffect B g ≤ W) →
          Z.trace ≤ W.trace) := by
  let g₀ : BoundedPolynomial F m d := ⟨0, by simp⟩
  let : Nonempty (BoundedPolynomial F m d) := ⟨g₀⟩
  let H (g : BoundedPolynomial F m d) := averagePolynomialPointEffect B g
  have hH (g : BoundedPolynomial F m d) : (H g).PosSemidef :=
    (averagePolynomialPointEffect_mem_Icc B g).1.posSemidef
  obtain ⟨T, Z, hZ, hle, hcomp, htrace⟩ := POVM.exists_optimal_trace_certificate H hH
  refine ⟨T.toMeasurement, Z, hZ.nonneg, hle, ?_, ?_, ?_, ?_⟩
  · simpa only [POVM.toMeasurement_effect] using hcomp
  · simpa only [POVM.toMeasurement_effect] using htrace
  · intro G
    have hsum := G.sum_effect
    rw [Fintype.sum_option] at hsum
    apply POVM.sum_trace_mul_le_trace_of_le _ H Z (fun g => (G.nonneg (some g)).posSemidef)
      _ hZ hle
    rw [← hsum]
    exact le_add_of_nonneg_left (G.nonneg none)
  · intro W hW
    have hW₀ := ((hH g₀).nonneg.trans (hW g₀)).posSemidef
    rw [← htrace]
    exact POVM.sum_trace_mul_le_trace_of_le T.effect H W T.posSemidef
      (le_of_eq T.sum_effect) hW₀ hW

end Cslib.PCP.LowIndividualDegree

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.Straddle
public import CslibFrontier.Foundations.Probability.Gaussian.OffMedian
import CslibFrontier.Foundations.MeasureTheory.Constructions.BorelSpace.Order
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate

/-!
# Off-median straddling probabilities on subcubic and cubic multigraphs

Applying the off-median Sheppard bound
(`ProbabilityTheory.measureReal_stdGaussian_mem_uIoc_le_exp_mul_angle`) and Jensen's inequality for
`arccos` on the three edge vectors at a degree-`3` vertex yields the off-median straddling bound
`exp (-t ^ 2 / 2) * straddleBound ρ₀`. We prove both the single-vertex version for loopless
subcubic multigraphs (`G.MaxDegreeLE 3`), used on degree-`3` blocks of weight-capped compressions
without padding low-degree blocks, and its specialization to loopless cubic multigraphs.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.measureReal_mem_uIoc_le_exp_mul`: off-median Sheppard bound for
  unit projections of `Measure.pi (gaussianReal 0 1)`.
* `Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le_of_ncard_eq_three`: single-vertex
  straddling bound in any loopless multigraph of maximum degree at most `3`.
* `Cslib.Circuits.Frontier.Gaussian.measureReal_straddleEvent_le_exp_mul`: off-median vertex
  straddling bound `exp (-t ^ 2 / 2) * straddleBound ρ₀` on loopless cubic multigraphs.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Circuits.Frontier.Gaussian

variable {V E : Type*} [Fintype V] {G : Multigraph V E} {q : ℝ} {R : ℕ} {ρ₀ : ℝ}

/-- Off-median Sheppard bound for two unit projections of `Measure.pi (gaussianReal 0 1)`. -/
theorem measureReal_mem_uIoc_le_exp_mul {y y' : EuclideanSpace ℝ V} (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (t : ℝ) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | t ∈ Ι ⟪y, WithLp.toLp 2 ω⟫ ⟪y', WithLp.toLp 2 ω⟫} ≤
      exp (-t ^ 2 / 2) * (arccos ⟪y, y'⟫ / π) := by
  rw [← InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hy hy']
  exact (measureReal_pi_gaussianReal_eq (s := {x | t ∈ Ι ⟪y, x⟫ ⟪y', x⟫})
    (measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) t)).trans_le
    (measureReal_stdGaussian_mem_uIoc_le_exp_mul_angle hy hy' t)

/-- **Off-median straddling probability at a degree-`3` vertex** in any loopless multigraph of
maximum degree at most `3`: `P(straddleEvent G q R t v) ≤ exp (-t ^ 2 / 2) * straddleBound ρ₀`. -/
theorem measureReal_straddleEvent_le_of_ncard_eq_three [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) {v : V}
    (hv : (G.incidenceSet v).ncard = 3) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) ≤
      exp (-t ^ 2 / 2) * straddleBound ρ₀ := by
  classical
  obtain ⟨e₀, e₁, e₂, -, -, -, hinc⟩ := ncard_eq_three.mp hv
  set s : Finset E := {e₀, e₁, e₂}
  have hs : (s : Set E) = G.incidenceSet v := by simp [s, hinc]
  have hcard : s.card = 3 := by rw [← ncard_coe_finset, hs, hv]
  have hunit (e : E) : ‖edgeVector G q R e‖ = 1 := norm_edgeVector hloop hdeg hq (by linarith) hρ e
  have hjensen := sum_arccos_edgeVector_offDiag_le hloop hdeg hq hρ₀ hρ hs hcard
  have hshep (p : E × E) : (Measure.pi fun _ : V => gaussianReal 0 1).real
      {ω | t ∈ Ι (edgeScore G q R ω p.1) (edgeScore G q R ω p.2)} ≤
        exp (-t ^ 2 / 2) * (arccos ⟪edgeVector G q R p.1, edgeVector G q R p.2⟫ / π) :=
    measureReal_mem_uIoc_le_exp_mul (hunit p.1) (hunit p.2) t
  have h4 := (four_mul_measureReal_straddleEvent_le (q := q) (R := R) hs hcard t).trans
    (Finset.sum_le_sum fun p (_ : p ∈ s.offDiag) => hshep p)
  rw [← Finset.mul_sum, ← Finset.sum_div] at h4
  have hdiv : (∑ x ∈ s.offDiag, arccos ⟪edgeVector G q R x.1, edgeVector G q R x.2⟫) / π ≤
      6 * arccos ((1 + 3 * ρ₀) / 4) / π :=
    div_le_div_of_nonneg_right hjensen pi_pos.le
  have h4' : 4 * (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) ≤
      exp (-t ^ 2 / 2) * (6 * arccos ((1 + 3 * ρ₀) / 4) / π) :=
    h4.trans (mul_le_mul_of_nonneg_left hdiv (exp_pos _).le)
  unfold straddleBound
  have hident : exp (-t ^ 2 / 2) * (6 * arccos ((1 + 3 * ρ₀) / 4) / π) =
      4 * (exp (-t ^ 2 / 2) * (3 / (2 * π) * arccos ((1 + 3 * ρ₀) / 4))) := by
    field_simp; ring
  linarith

/-- **Off-median straddling probability** on loopless cubic multigraphs. -/
theorem measureReal_straddleEvent_le_exp_mul [Finite E] (hloop : G.Loopless)
    (h3 : ∀ v, (G.incidenceSet v).ncard = 3) (hq : 0 ≤ q) (hρ₀ : 0 ≤ ρ₀)
    (hρ : ρ₀ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : V) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real (straddleEvent G q R t v) ≤
      exp (-t ^ 2 / 2) * straddleBound ρ₀ :=
  measureReal_straddleEvent_le_of_ncard_eq_three hloop (fun w => (h3 w).le) hq hρ₀ hρ t (h3 v)

end Cslib.Circuits.Frontier.Gaussian

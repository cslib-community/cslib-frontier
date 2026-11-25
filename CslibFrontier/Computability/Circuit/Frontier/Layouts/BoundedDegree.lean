/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Core
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.MultiGaussian
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Gaussian cycle-rank coefficients in every fixed degree

Saturated compression and Gaussian vertex layouts give the layout hypothesis for maximum degree
`d ≥ 3` with coefficient

`A_d = (3d / (2d - 3)) · arccos (2 √(d - 1) / d) / π`

(`Cslib.Circuits.Frontier.layoutBound_degree`). Let `G` be a connected multigraph of maximum
degree `d` with cycle rank `β₁`. A saturated compression of `G` with budget `d` has a core, its
quotient, with at most `3d β₁ / (2d - 3)` edges and at most as many blocks
(`Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.mul_card_external_le`). Gaussian vertex
layouts give the core a layout of width `vertexCoefficient d · |E(core)| + o(|blocks|)`
(`Cslib.Circuits.Frontier.Gaussian.exists_width_le_vertexCoefficient`), and expanding it costs
`d log₂ |V|` edges at each frontier.

At `d = 3` the coefficient `3 arccos (2√2/3) / π ≈ 0.3245` is at most `1/3`
(`Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_three_le`), so the layout hypothesis for
maximum degree three holds with coefficient `1/3` (`Cslib.Circuits.Frontier.layoutBound_one_third`).

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.degreeCoefficient`: the coefficient `A_d`.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.degreeCoefficient_three_le`: `A_3 ≤ 1/3`.
* `Cslib.Circuits.Frontier.layoutBound_degree`: the layout hypothesis for maximum degree `d ≥ 3`
  with coefficient `A_d`.
* `Cslib.Circuits.Frontier.layoutBound_one_third`: the layout hypothesis for maximum degree three
  with coefficient `1/3`.
-/

@[expose] public section

open Real

namespace Cslib.Circuits.Frontier

namespace Gaussian

/-- The layout coefficient `A_d = (3d / (2d - 3)) · arccos (2 √(d - 1) / d) / π` of saturated
compression and Gaussian vertex scores in maximum degree `d`. -/
noncomputable def degreeCoefficient (d : ℕ) : ℝ :=
  3 * d / (2 * d - 3) * vertexCoefficient d

/-- The limiting adjacent correlation `2 √(d - 1) / d` is less than one for `d ≥ 3`. -/
theorem vertexCorrelation_lt_one {d : ℕ} (hd : 3 ≤ d) : vertexCorrelation d < 1 := by
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : √((d : ℝ) - 1) ^ 2 = d - 1 := sq_sqrt (by linarith)
  rw [vertexCorrelation, div_lt_one (by linarith)]
  nlinarith [sqrt_nonneg ((d : ℝ) - 1), sq_pos_of_pos (show (0 : ℝ) < d - 2 by linarith)]

/-- The limiting crossing probability `vertexCoefficient d` is positive for `d ≥ 3`. -/
theorem vertexCoefficient_pos {d : ℕ} (hd : 3 ≤ d) : 0 < vertexCoefficient d :=
  div_pos (arccos_pos.mpr (vertexCorrelation_lt_one hd)) pi_pos

/-- The layout coefficient `degreeCoefficient d` is positive for `d ≥ 3`. -/
theorem degreeCoefficient_pos {d : ℕ} (hd : 3 ≤ d) : 0 < degreeCoefficient d := by
  exact mul_pos (div_pos (by cast_linarith [hd]) (by cast_linarith)) (vertexCoefficient_pos hd)

/-- In degree three the coefficient `3 arccos (2√2/3) / π ≈ 0.3245` is at most `1/3`, since
`cos (π/9) ≤ 2√2/3`. -/
theorem degreeCoefficient_three_le : degreeCoefficient 3 ≤ 1 / 3 := by
  have hsqrt : (141421 : ℝ) / 100000 < √2 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpi := pi_gt_d2
  have hpi' := pi_lt_d2
  set θ := π / 9 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθlo : 0.3488 ≤ θ := by
    rw [hθ]
    linarith
  have hθhi : θ ≤ 0.35 := by
    rw [hθ]
    linarith
  have hcos : cos θ ≤ 2 * √2 / 3 := by
    have hb := cos_bound (x := θ) (by rw [abs_of_nonneg hθ0]; linarith)
    rw [abs_of_nonneg hθ0] at hb
    have h2 : θ ^ 2 ≥ 0.3488 ^ 2 := by gcongr
    have h4 : θ ^ 4 ≤ 0.35 ^ 4 := by gcongr
    nlinarith [(abs_le.mp hb).2]
  have harccos : arccos (2 * √2 / 3) ≤ θ :=
    (arccos_le_arccos hcos).trans_eq (arccos_cos hθ0 (by rw [hθ]; linarith))
  have hρ : vertexCorrelation 3 = 2 * √2 / 3 := by norm_num [vertexCorrelation]
  unfold degreeCoefficient vertexCoefficient
  rw [hρ, mul_div_assoc', div_le_iff₀ pi_pos]
  norm_num
  linarith

end Gaussian

/-- In a saturated compression of budget `d ≥ 3` of a connected multigraph into at least two blocks,
the quotient has at most `3 d / (2 d - 3) β₁` external edges. -/
theorem Multigraph.Compression.Saturated.card_external_le_div_mul_cycleRank
    {V E : Type*} [Finite E] {G : Multigraph V E} {d : ℕ} (hd : 3 ≤ d)
    {Q : G.Compression d} (hQ : Q.Saturated) (hG : G.toSimpleGraph.Connected)
    (two : 1 < Nat.card Q.blocks) :
    (Nat.card Q.external : ℝ) ≤ 3 * d / (2 * d - 3) * G.cycleRank := by
  have h := Nat.cast_le (α := ℝ).mpr (hQ.mul_card_external_le hG two)
  push_cast [Nat.cast_sub (by omega : 3 ≤ 2 * d)] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by cast_linarith [hd])]
  cast_linarith

/-- Since `3 d / (2 d - 3) ≤ 3` for `d ≥ 3`, a saturated quotient has at most `3 β₁` external edges
and at most `3 β₁` blocks. -/
theorem Multigraph.Compression.Saturated.card_external_and_blocks_le_three_mul_cycleRank
    {V E : Type*} [Finite E] {G : Multigraph V E} {d : ℕ} (hd : 3 ≤ d)
    {Q : G.Compression d} (hQ : Q.Saturated) (hG : G.toSimpleGraph.Connected)
    (two : 1 < Nat.card Q.blocks) :
    (Nat.card Q.external : ℝ) ≤ 3 * G.cycleRank ∧
      (Nat.card Q.blocks : ℝ) ≤ 3 * G.cycleRank := by
  have hE3 : (Nat.card Q.external : ℝ) ≤ 3 * G.cycleRank := by
    refine (hQ.card_external_le_div_mul_cycleRank hd hG two).trans
      (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    rw [div_le_iff₀ (by cast_linarith [hd])]
    cast_linarith
  exact ⟨hE3, (Nat.cast_le.mpr (hQ.card_blocks_le_card_external hG two)).trans hE3⟩

/-- **Gaussian vertex-score layouts.** For `d ≥ 3`, connected, loopless multigraphs of maximum
degree `d` have layouts of width `(A_d + o(1)) β₁ + o(|V|)`, where `β₁` is the cycle rank and
`A_d = (3d / (2d - 3)) · arccos (2 √(d - 1) / d) / π` is `Gaussian.degreeCoefficient d`. -/
theorem layoutBound_degree {d : ℕ} (hd : 3 ≤ d) :
    LayoutBound d (Gaussian.degreeCoefficient d) := by
  refine LayoutBound.of_saturated (Gaussian.degreeCoefficient_pos hd).le fun η hη => ?_
  obtain ⟨N₀, hN₀⟩ := Gaussian.exists_width_le_vertexCoefficient (by omega : 2 ≤ d)
    (show 0 < η / 3 by positivity)
  refine ⟨N₀, fun V E _ _ G Q hG hQ two big => ?_⟩
  -- A large quotient is laid out by Gaussian vertex scores. It has at most
  -- `3d / (2d - 3) β₁ ≤ 3 β₁` edges, and at most as many blocks.
  obtain ⟨σ, hσ⟩ := hN₀ Q.blocks Q.external Q.quotient Q.quotient_loopless
    Q.quotient_maxDegreeLE big
  refine ⟨σ, hσ.trans ?_⟩
  have hE := hQ.card_external_le_div_mul_cycleRank hd hG two
  have ⟨_, hV⟩ := hQ.card_external_and_blocks_le_three_mul_cycleRank hd hG two
  have hmain := mul_le_mul_of_nonneg_left hE (Gaussian.vertexCoefficient_pos hd).le
  have hslack := mul_le_mul_of_nonneg_left hV (show 0 ≤ η / 3 by positivity)
  unfold Gaussian.degreeCoefficient
  nlinarith

/-- **The layout hypothesis with coefficient one third** for maximum degree three, from Gaussian
vertex-score layouts: `A_3 = 3 arccos (2√2/3) / π ≤ 1/3`. -/
theorem layoutBound_one_third : LayoutBound 3 (1 / 3) :=
  (layoutBound_degree le_rfl).mono Gaussian.degreeCoefficient_three_le

end Cslib.Circuits.Frontier

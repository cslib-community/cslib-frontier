/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Indicator
public import CslibFrontier.Probability.PlantedClique.Directional
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith

/-!
# Noise applied to the normalized clique indicator

The sum-of-squared-row-sums bound becomes a bound for the actual signed noise applied to
`unitIndicator S`. Dividing by the planted-set cardinality gives squared norm at most
`(1 + ε) n`, with exponential failure probability in `n - |S|`.

## Main results

* `Cslib.Algorithms.PlantedClique.dens_noise_unitIndicator_norm_sq_gt_le`: a directional
  concentration bound for the normalized vector used in the spectral analysis.
-/

public section

open Finset Real
open scoped BigOperators

namespace Cslib.Algorithms.PlantedClique

open Cslib.Probability.PlantedClique

private theorem card_mul_noise_unitIndicator_norm_sq {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (ω : Coins n) :
    (S.card : ℝ) * ‖(noise S ω).toEuclideanLin (unitIndicator S)‖ ^ 2 =
      ∑ i, (∑ j ∈ S, noise S ω i j) ^ 2 := by
  have hcoord (i : Fin n) : (noise S ω).toEuclideanLin (unitIndicator S) i =
      (1 / Real.sqrt S.card) * ∑ j ∈ S, noise S ω i j := by
    change (∑ j, noise S ω i j * unitIndicator S j) = _
    simp only [unitIndicator_apply, mul_ite, mul_zero, ← sum_filter,
      filter_mem_eq_inter, univ_inter]
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hcoord, mul_pow]
  rw [← mul_sum, ← mul_assoc, card_mul_unitIndicator_height_sq hS, one_mul]

/-- The signed noise in the normalized clique direction has squared norm at most
`(1 + ε) n`, except with the displayed exponential failure density. -/
theorem dens_noise_unitIndicator_norm_sq_gt_le {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) :
    (dens ({ω : Coins n | (1 + ε) * (n : ℝ) <
      ‖(noise S ω).toEuclideanLin (unitIndicator S)‖ ^ 2} : Finset _) : ℝ) ≤
      exp (-((n - S.card : ℕ) : ℝ) / 2 * (ε ^ 2 / 2 - ε ^ 3 / 3)) := by
  classical
  have hk : (0 : ℝ) < S.card := Nat.cast_pos.mpr hS.card_pos
  have hsub : ({ω : Coins n | (1 + ε) * (n : ℝ) <
      ‖(noise S ω).toEuclideanLin (unitIndicator S)‖ ^ 2} : Finset _) ⊆
      ({ω : Coins n | (n - S.card : ℕ) * (1 + ε) * (S.card : ℝ) <
        ∑ i, (∑ j ∈ S, noise S ω i j) ^ 2} : Finset _) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω ⊢
    have hn : ((n - S.card : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n S.card
    have hmul := mul_lt_mul_of_pos_left hω hk
    rw [card_mul_noise_unitIndicator_norm_sq S hS ω] at hmul
    have hmean : ((n - S.card : ℕ) : ℝ) * (1 + ε) * S.card ≤
        (S.card : ℝ) * ((1 + ε) * n) := by
      calc
        _ ≤ (n : ℝ) * (1 + ε) * S.card := by gcongr
        _ = _ := by ring
    exact hmean.trans_lt hmul
  refine le_trans ?_ (dens_lt_sum_sq_noise_sum_le S hε)
  exact_mod_cast dens_le_dens hsub

end Cslib.Algorithms.PlantedClique

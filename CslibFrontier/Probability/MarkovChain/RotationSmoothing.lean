/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.AveragedPower
public import CslibFrontier.Probability.MarkovChain.MetricSmoothing
public import CslibFrontier.Probability.MarkovChain.RotationMap
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Squared-distance comparisons for fixed-degree averages of regular walks

A rotation map that dominates half of the time-averaged lazy walk inherits its CAT(0) comparison
for every placement. The same rotation map works for every target space. In particular,
`comparison_of_padded_cesaro` applies to the rotation map supplied by `exists_padded_lazy_cesaro`.
-/

public section

namespace Cslib.RotationMap

open Finset Cslib.Probability Cslib.Probability.MarkovChain
open scoped BigOperators

variable {V D : Type*} (G : RotationMap V D) [Fintype D] [Nonempty D]

/-- Under uniform stationarity, the endpoint energy is the average over oriented labels. -/
theorem crossEnergy_uniform_randomWalk [Fintype V] [Nonempty V] {X : Type*} [MetricSpace X]
    (x z : V → X) :
    crossEnergy (PMF.uniformOfFintype V) G.randomWalk x z =
      𝔼 p : V × D, dist (x p.1) (z (G.rot p).1) ^ 2 := by
  rw [Fintype.expect_prod_type]
  simp only [crossEnergy, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    stepOp_randomWalk, walk_apply,
    Fintype.expect_eq_sum_div_card, ← mul_sum, div_eq_inv_mul]
  rfl

/-- The fixed-width labels realize the exact time-averaged energy, including for a lazy graph. -/
theorem crossEnergy_cesaroPowers [Fintype V] {t : ℕ} [NeZero t] (π : PMF V) {X : Type*}
    [MetricSpace X] (x z : V → X) :
    crossEnergy π (G.cesaroPowers t).randomWalk x z =
      𝔼 h : Fin t, crossEnergy π (G.randomWalk ^ (h.val + 1)) x z := by
  simp only [crossEnergy, stepOp_randomWalk, walk_cesaroPowers, map_pow, mul_expect]
  exact (expect_sum_comm univ univ _).symm

/-- Pointwise domination of the averaged walk controls squared displacements for every placement
and every initial distribution. -/
theorem average_lazy_energy_le_of_walk [Fintype V] {T : Type*} [Fintype T] [Nonempty T]
    (R : RotationMap V T) {t : ℕ} [NeZero t]
    (hR : ∀ (f : V → ℝ), (∀ v, 0 ≤ f v) → ∀ v,
      (𝔼 h : Fin t, (G.lazy.walk ^ (h.val + 1)) f v) ≤ 2 * R.walk f v)
    (π : PMF V) {X : Type*} [MetricSpace X] (x z : V → X) :
    (∑ j ∈ range t, crossEnergy π (G.randomWalk.lazy ^ (j + 1)) x z) / t ≤
        2 * crossEnergy π R.randomWalk x z := by
  calc
    _ = 𝔼 h : Fin t, crossEnergy π (G.lazy.randomWalk ^ (h.val + 1)) x z := by
      rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, randomWalk_lazy,
        Fin.sum_univ_eq_sum_range (fun j => crossEnergy π (G.randomWalk.lazy ^ (j + 1)) x z)]
    _ = _ := (G.lazy.crossEnergy_cesaroPowers π x z).symm
    _ ≤ _ := by
      simp only [crossEnergy, stepOp_randomWalk, walk_cesaroPowers, mul_sum]
      apply sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left
        (hR (fun j => dist (x i) (z j) ^ 2) (fun _ => sq_nonneg _) i)
        (ENNReal.toReal_nonneg (a := π i))
      simpa only [mul_left_comm _ (2 : ℝ)] using h

/-- The prescribed-degree rotation map improves any squared-distance comparison enjoyed by the
predecessor, uniformly over all CAT(0) spaces used to test it. -/
theorem comparison_of_padded_cesaro [Fintype V] {T : Type*} [Fintype T] [Nonempty T]
    (R : RotationMap V T) {s : ℕ} (hs : 0 < s)
    (hR : ∀ (f : V → ℝ), (∀ v, 0 ≤ f v) → ∀ v,
      (𝔼 h : Fin (s + s), (G.lazy.walk ^ (h.val + 1)) f v) ≤ 2 * R.walk f v)
    {D' : MarkovChain V} {π : PMF V} (hG : G.randomWalk.IsStationary π) (hD : D'.IsStationary π)
    {X : Type*} [MetricSpace X] [CompleteCAT0Space X] {β : ℝ}
    (hcomp : ∀ y : V → X, crossEnergy π D' y y ≤ β * crossEnergy π G.randomWalk y y)
    (x : V → X) :
    crossEnergy π D' x x ≤ 96 * max 2 (β / (2 * s)) * crossEnergy π R.randomWalk x x := by
  let : NeZero (s + s) := ⟨by lia⟩
  have he := G.average_lazy_energy_le_of_walk R hR π x x
  rw [Nat.cast_add, ← two_mul (s : ℝ)] at he
  have hk : 0 ≤ max 2 (β / (2 * (s : ℝ))) := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  refine (energy_comparison_lazy_average hG hD hcomp hs x).trans ?_
  calc _ ≤ (48 * max 2 (β / (2 * s))) * (2 * crossEnergy π R.randomWalk x x) :=
         mul_le_mul_of_nonneg_left he (by positivity)
       _ = _ := by ring

end Cslib.RotationMap

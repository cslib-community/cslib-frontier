/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.GameTheory.P2P.Generosity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# P2P generosity tests and witnesses

Checked finite examples and algebraic witnesses for `CslibFrontier.GameTheory.P2P.Generosity`:

* Critical uniform threshold `θ_m = 4` (`x = 1 / 2`), positive stable equilibrium at `θ_m = 5`
  with best-response stability bounds (`uniform_stability`), and collapse below `4` at `θ_m = 3`.
* Mixture generosity (`mixtureTail`): exact rational equilibrium at `θ_m = 4, φ = 1 / 2` and a
  subcritical rescue witness at `θ_m = 3, φ = 1 / 3` (`x = 1 / 3`).
* Service differentiation penalty (`Claim 23.2`): `p = 1 / 2` at `α = 2` sustains `x = 1` even
  under `uniformTail 1`.
* Uniform exclusion tradeoff (`Exercise 23.2`): `z = 1 / 2` rescues `θ_m = 3` yet strictly reduces
  welfare when `θ_m = 5, α = 2`.
-/

namespace CslibFrontierTests.GameTheory.P2PGenerosity

open Cslib.GameTheory.P2P

example :
    generosityEquilibrium (uniformTail 4) (1 / 2) ∧
      (∀ x, generosityEquilibrium (uniformTail 4) x → x = 1 / 2) := by
  refine ⟨(uniformEquilibrium_iff (by norm_num)).mpr ⟨le_rfl, Or.inl (by norm_num [unifLowRoot])⟩,
    ?_⟩
  intro x hx
  rcases (uniformEquilibrium_iff (by norm_num)).mp hx with ⟨_, rfl | rfl⟩ <;>
    norm_num [unifLowRoot, unifHighRoot]

example :
    generosityEquilibrium (uniformTail 5) (unifHighRoot 5) ∧
      unifLowRoot 5 < 3 / 5 ∧ 3 / 5 < unifHighRoot 5 ∧
      (3 / 5 : ℝ) < uniformTail 5 (1 / (3 / 5)) ∧
      uniformTail 5 (1 / (4 / 5)) < 4 / 5 := by
  have h5 : (4 : ℝ) ≤ 5 := by norm_num
  have hsq5 : (2 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
    constructor
    · rw [Real.lt_sqrt (by norm_num)]
      norm_num
    · rw [Real.sqrt_lt' (by norm_num)]
      norm_num
  have hl : unifLowRoot 5 < 3 / 5 := by
    have hsqrt : Real.sqrt (5 * (5 - 4)) = Real.sqrt 5 := by ring_nf
    dsimp [unifLowRoot]
    rw [hsqrt]
    linarith
  have hh : (3 / 5 : ℝ) < unifHighRoot 5 := by
    have hsqrt : Real.sqrt (5 * (5 - 4)) = Real.sqrt 5 := by ring_nf
    dsimp [unifHighRoot]
    rw [hsqrt]
    linarith
  have hh45 : unifHighRoot 5 < 4 / 5 := by
    have hsqrt : Real.sqrt (5 * (5 - 4)) = Real.sqrt 5 := by ring_nf
    dsimp [unifHighRoot]
    rw [hsqrt]
    linarith
  have hstab1 := (uniform_stability h5 (by norm_num : (0 : ℝ) < 3 / 5)).1 hl hh
  have hstab2 := (uniform_stability h5 (by norm_num : (0 : ℝ) < 4 / 5)).2 (Or.inr hh45)
  exact ⟨(uniformEquilibrium_iff (by norm_num)).mpr ⟨h5, Or.inr rfl⟩, hl, hh, hstab1, hstab2⟩

example : ¬ ∃ x, generosityEquilibrium (uniformTail 3) x :=
  uniform_at_four_and_collapse.2 (by norm_num) (by norm_num)

example :
    generosityEquilibrium (mixtureTail 4 (1 / 2)) (1 / 2) ∧
      generosityEquilibrium (mixtureTail 3 (1 / 3)) (1 / 3) := by
  refine ⟨⟨by norm_num, by norm_num, ?_⟩, ⟨by norm_num, by norm_num, ?_⟩⟩
  · have h := (mixtureEquilibrium_iff (θ_m := 4) (φ := 1 / 2) (x := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
      ⟨by norm_num, Or.inr (by norm_num)⟩
    linarith
  · have h := (mixtureEquilibrium_iff (θ_m := 3) (φ := 1 / 3) (x := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
      ⟨by norm_num, Or.inl (by norm_num)⟩
    linarith

example :
    penaltyEquilibrium (uniformTail 1) 2 (1 / 2) 1 ∧
      ¬ ∃ x, generosityEquilibrium (uniformTail 1) x := by
  refine ⟨(fullCooperation_penalty_threshold (tail := uniformTail 1)
    (fun t ht => by simp [uniformTail, ht]) (by norm_num : (0 : ℝ) < 2) (by norm_num)).2,
    uniform_at_four_and_collapse.2 (by norm_num) (by norm_num)⟩

example :
    ((¬ ∃ x, generosityEquilibrium (uniformTail 3) x) ∧
      exclEquilibrium (uniformTail 3) (1 / 2) (exclHighRoot 3 (1 / 2)) ∧
      0 < exclWelfare 3 (exclHighRoot 3 (1 / 2)) (1 / 2)) ∧
    exclWelfare 2 (exclHighRoot 5 (1 / 2)) (1 / 2) < minimalistWelfare 2 (unifHighRoot 5) :=
  ⟨excl_rescues_low_generosity, excl_can_reduce_welfare⟩

end CslibFrontierTests.GameTheory.P2PGenerosity

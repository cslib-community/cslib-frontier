/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Strategic.Universality.DattaHorner
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Datta's Horner game on three small systems

* `4 x² − 1 = 0` in one variable has the root `x = 1/2`. Its chain has `D = 2` equations, so
  Alice, Bob and Critter have `2`, `2` and `3` pure strategies. The root, with Bob playing the
  rescaled Horner value at the single non-root node and Critter uniform, is a totally mixed Nash
  equilibrium.
* `27 x_j³ − 1 = 0`, `j < 2`, the sparse example of the shared-table game: each chain has `3`
  equations, so `D = 6` and the Horner game has `3`, `5` and `7` pure strategies, against `3`, `8`
  and `10` on the sparse table. The paper's printed `D = −1 + 4 + 4 = 7` would give `6` and `8`.
* `0 = 0` in one variable, a constant equation: its chain is empty, so `D = 0` and Bob has no
  non-reference strategies, but Critter keeps its strategy for the equation. Critter has `2` pure
  strategies and fixed weight `critterWeight = 1/2`, not `1 / (D + 1) = 1`. The point `x = 1/3`
  of the open simplex, with Critter uniform, is a totally mixed Nash equilibrium.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.DattaHorner

open MvPolynomial Finset Cslib.GameTheory Cslib.GameTheory.DattaHorner

/-! ### `4 x² − 1` -/

/-- `4 x² − 1`. -/
noncomputable def sq : Fin 1 → MvPolynomial (Fin 1) ℝ :=
  fun _ => monomial (Finsupp.single 0 2) 4 + monomial 0 (-1)

theorem support_sq (j : Fin 1) : (sq j).support = {Finsupp.single 0 2, 0} := by
  ext s
  by_cases h1 : s = Finsupp.single 0 2 <;> by_cases h0 : s = 0 <;>
    simp_all [sq, coeff_monomial, MvPolynomial.coeff_one, eq_comm]

theorem degreeOf_sq (j : Fin 1) (i : Fin 1) : degreeOf i (sq j) = 2 := by
  rw [degreeOf_eq_sup, support_sq, Fin.fin_one_eq_zero i]
  simp

/-- Alice, Bob and Critter have `2`, `2` and `3` pure strategies. -/
example : Fintype.card (Option (Strat sq .alice)) = 2 ∧
    Fintype.card (Option (Strat sq .bob)) = 2 ∧
    Fintype.card (Option (Strat sq .critter)) = 3 := by
  have hD : chainLength sq = 2 := by simp [chainLength, degreeOf_sq]
  have := card_strategies (F := sq) fun j => ⟨0, by simp [degreeOf_sq]⟩
  rw [hD] at this
  exact this

/-- The root `x = 1/2`, Bob's rescaled Horner values and Critter uniform. -/
noncomputable def sol : Coord sq → ℝ
  | ⟨.alice, _⟩ => 1 / 2
  | ⟨.bob, ⟨⟨j, p⟩, _⟩⟩ => (horner (sq j) (fun _ => 1 / 2) p.var p.expo - shift sq j) / scale sq j
  | ⟨.critter, _⟩ => critterWeight sq

/-- The root is a totally mixed Nash equilibrium. -/
example : (game sq).IsTotallyMixedNash (simplexProfile sol) := by
  rw [isTotallyMixedNash_game_iff]
  refine ⟨⟨fun i => ?_, ?_, fun j => ?_⟩, fun j p h => rfl, fun _ => rfl, fun _ _ => rfl,
    fun j => ?_, ?_⟩
  · norm_num [sol]
  · norm_num [sol]
  · simp [sq, sol, eval_monomial]
    norm_num
  · simp only [sol, critterWeight]
    positivity
  · simp only [sol, critterWeight, sum_const, card_univ, nsmul_eq_mul]
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin, mul_one_div,
      div_lt_one (by positivity)]
    push_cast
    linarith

/-! ### Two cubics -/

/-- `27 x_j³ − 1`. -/
noncomputable def cubes : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  fun j => monomial (Finsupp.single j 3) 27 + monomial 0 (-1)

theorem support_cubes (j : Fin 2) : (cubes j).support = {Finsupp.single j 3, 0} := by
  ext s
  by_cases h1 : s = Finsupp.single j 3 <;> by_cases h0 : s = 0 <;>
    simp_all [cubes, coeff_monomial, MvPolynomial.coeff_one, eq_comm]

theorem degreeOf_cubes (j i : Fin 2) : degreeOf i (cubes j) = if j = i then 3 else 0 := by
  rw [degreeOf_eq_sup, support_cubes]
  by_cases h : j = i <;> simp [h]

/-- The Horner game has `D = 6` chain equations and `3`, `5` and `7` pure strategies. -/
example : chainLength cubes = 6 ∧ Fintype.card (Option (Strat cubes .alice)) = 3 ∧
    Fintype.card (Option (Strat cubes .bob)) = 5 ∧
    Fintype.card (Option (Strat cubes .critter)) = 7 := by
  have hD : chainLength cubes = 6 := by
    simp [chainLength, degreeOf_cubes, Fin.sum_univ_two, Fin.prod_univ_two]
  have := card_strategies (F := cubes) fun j => ⟨j, by simp [degreeOf_cubes]⟩
  rw [hD] at this
  exact ⟨hD, this⟩

/-! ### A constant equation -/

/-- The constant equation `0 = 0` in one variable. -/
noncomputable def zeroSys : Fin 1 → MvPolynomial (Fin 1) ℝ := fun _ => 0

theorem bobNodes_zeroSys : bobNodes zeroSys = ∅ := by
  ext ⟨j, p⟩
  simp [mem_bobNodes, mem_nodes, zeroSys]

/-- The chain is empty, Critter has `2` pure strategies and its fixed weight is `1/2`. -/
example : chainLength zeroSys = 0 ∧ Fintype.card (Option (Strat zeroSys .bob)) = 1 ∧
    Fintype.card (Option (Strat zeroSys .critter)) = 2 ∧ critterWeight zeroSys = 1 / 2 := by
  refine ⟨by simp [chainLength, zeroSys], ?_, ?_, ?_⟩
  · simp [bobNodes_zeroSys]
  · simp [Fintype.card_sum, bobNodes_zeroSys]
  · norm_num [critterWeight, bobNodes_zeroSys]

/-- The point `x = 1/3`, with Critter uniform. -/
noncomputable def solZero : Coord zeroSys → ℝ
  | ⟨.alice, _⟩ => 1 / 3
  | ⟨.bob, _⟩ => 0
  | ⟨.critter, _⟩ => critterWeight zeroSys

/-- The constant branch: `x = 1/3`, with Critter uniform, is a totally mixed Nash equilibrium. -/
example : (game zeroSys).IsTotallyMixedNash (simplexProfile solZero) := by
  rw [isTotallyMixedNash_game_iff]
  refine ⟨⟨fun i => ?_, ?_, fun j => ?_⟩, fun j p h => ?_, fun _ => rfl, fun _ _ => rfl,
    fun j => ?_, ?_⟩
  · norm_num [solZero]
  · norm_num [solZero]
  · simp [zeroSys]
  · simp [bobNodes_zeroSys] at h
  · norm_num [solZero, critterWeight]
    positivity
  · simp [solZero, bobNodes_zeroSys, critterWeight]
    norm_num

end CslibFrontierTests.GameTheory.DattaHorner

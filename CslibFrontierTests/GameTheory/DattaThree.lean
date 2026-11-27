/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Strategic.Universality.DattaThree
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The three-player game on two cubics

The system `F_j(x) = 27 x_j³ - 1 = 0`, `j < 2`, has the single root `x = (1/3, 1/3)` in the open
simplex. Its sparse table `{x₀ᵃ | a ≤ 3} ∪ {x₁ᵇ | b ≤ 3}` has `7` exponents, so Alice, Bob and
Critter have `3`, `8` and `10` pure strategies. On the full box `{0, …, 3}²` of `16` exponents,
Bob and Critter would have `17` and `19`. The paper's printed `D = −1 + 4 + 4 = 7` gives `6` and
`8`, and the bound `|E| + m ≤ D + 2` is attained: `7 + 2 = 9`. The Horner game has
`D = 3 + 3 = 6` chain equations and gives `5` and `7` (`DattaHorner` tests).
The root, with Bob playing its monomials scaled by `1/8` and Critter uniform, is a totally mixed
Nash equilibrium.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.DattaThree

open MvPolynomial Finset Cslib.GameTheory Cslib.GameTheory.DattaThree

/-- `27 x_j³ - 1`. -/
noncomputable def cubes : Fin 2 → MvPolynomial (Fin 2) ℝ :=
  fun j => monomial (Finsupp.single j 3) 27 + monomial 0 (-1)

theorem mem_support_cubes (j : Fin 2) (s : Fin 2 →₀ ℕ) :
    s ∈ (cubes j).support ↔ s = Finsupp.single j 3 ∨ s = 0 := by
  have hne : Finsupp.single j 3 ≠ 0 := by simp
  by_cases h1 : Finsupp.single j 3 = s
  · subst h1
    simp [cubes, coeff_monomial, MvPolynomial.coeff_one, hne.symm]
  · by_cases h0 : (0 : Fin 2 →₀ ℕ) = s
    · subst h0
      simp [cubes, coeff_monomial, hne]
    · simpa [cubes, coeff_monomial, MvPolynomial.coeff_one, h1, Ne.symm h1, Ne.symm h0] using h0

theorem sparseTable_cubes :
    sparseTable cubes = Iic (Finsupp.single 0 3) ∪ Iic (Finsupp.single 1 3) := by
  ext e
  simp only [mem_sparseTable, mem_support_cubes, mem_union, mem_Iic, Fin.exists_fin_two]
  constructor
  · rintro (⟨s, rfl | rfl, h⟩ | ⟨s, rfl | rfl, h⟩)
    · exact .inl h
    · exact .inl (h.trans zero_le)
    · exact .inr h
    · exact .inr (h.trans zero_le)
  · rintro (h | h)
    · exact .inl ⟨_, .inl rfl, h⟩
    · exact .inr ⟨_, .inl rfl, h⟩

theorem card_sparseTable_cubes : #(sparseTable cubes) = 7 := by
  have hinter : Iic (Finsupp.single (0 : Fin 2) 3) ∩ Iic (Finsupp.single 1 3) = {0} := by
    ext e
    simp only [mem_inter, mem_Iic, mem_singleton, Finsupp.le_def, Fin.forall_fin_two]
    constructor
    · rintro ⟨⟨_, h01⟩, h10, _⟩
      ext i
      fin_cases i <;> simp_all
    · rintro rfl
      simp
  have hcard : ∀ j : Fin 2, #(Iic (Finsupp.single j 3)) = 4 := fun j => by
    simp [Finsupp.card_Iic]
  have := card_union_add_card_inter (Iic (Finsupp.single (0 : Fin 2) 3))
    (Iic (Finsupp.single 1 3))
  rw [hinter, hcard, hcard, card_singleton] at this
  rw [sparseTable_cubes]
  omega

/-- On the sparse table, Alice, Bob and Critter have `3`, `8` and `10` pure strategies. -/
example : Fintype.card (Option (Strat (sparseTable cubes) 2 .alice)) = 3 ∧
    Fintype.card (Option (Strat (sparseTable cubes) 2 .bob)) = 8 ∧
    Fintype.card (Option (Strat (sparseTable cubes) 2 .critter)) = 10 := by
  simp [card_sparseTable_cubes]

theorem support_cubes (j : Fin 2) : (cubes j).support = {Finsupp.single j 3, 0} := by
  ext s
  rw [mem_support_cubes, mem_insert, mem_singleton]

/-- `x_j` has degree `3` in `F_j` and `x_i`, `i ≠ j`, has degree `0`. -/
theorem degreeOf_cubes (i j : Fin 2) : degreeOf i (cubes j) = if i = j then 3 else 0 := by
  rw [degreeOf_eq_sup, support_cubes]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- `card_sparseTable_add_le` with the actual degrees: `7 + 2 ≤ 1 + 4 + 4 = 9`. -/
example : #(sparseTable cubes) + 2 ≤ 9 :=
  (card_sparseTable_add_le cubes).trans_eq (by
    simp [degreeOf_cubes, Fin.sum_univ_two, Fin.prod_univ_two])

/-- `card_sparseTable_le_pow` with the actual degree bound `3`: the sparse table has at most as
many exponents as the full box `{0, …, 3}²`, which has `16`. -/
example : #(sparseTable cubes) ≤ 16 :=
  card_sparseTable_le_pow (d := 3) fun j i => by
    rw [degreeOf_cubes]
    split_ifs <;> norm_num

/-- The root `x = (1/3, 1/3)`, Bob's monomial weights `xᵉ / 8`, and Critter uniform. -/
noncomputable def root : Coord (sparseTable cubes) 2 → ℝ
  | ⟨.alice, _⟩ => 1 / 3
  | ⟨.bob, e⟩ => expoPow (fun _ => 1 / 3) (e : sparseTable cubes).1 / 8
  | ⟨.critter, _⟩ => 1 / 10

/-- The root, with its monomials on Bob and Critter uniform, is a totally mixed Nash
equilibrium. -/
example : (game (sparseTable cubes) cubes).IsTotallyMixedNash (simplexProfile root) := by
  rw [isTotallyMixedNash_game_iff (isLowerSet_sparseTable cubes)
    (support_subset_sparseTable cubes)]
  refine ⟨⟨fun i => ?_, ?_, fun j => ?_⟩, fun e => ?_, fun e => ?_, fun j _ => ?_, fun j => ?_, ?_⟩
  · norm_num [root]
  · norm_num [root]
  · simp [cubes, eval_monomial, root]
    norm_num
  · simp [root, bobScale, card_sparseTable_cubes]
    norm_num
  · norm_num [root, critterWeight, card_sparseTable_cubes]
  · norm_num [root, critterWeight, card_sparseTable_cubes]
  · norm_num [root]
  · simp [root, card_sparseTable_cubes]
    norm_num

end CslibFrontierTests.GameTheory.DattaThree

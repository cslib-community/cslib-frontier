/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Code.MultilinearitySoundness
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests: polynomial soundness of the multilinearity test

Self-improvement applies to the product over `ZMod 5` corrupted at one point: the product is a
multilinear function within one point, and the lemma bounds the distance by
`5 * (5 + 5) + 2 * 2 ^ 2 * 5 = 90`. The hypotheses of the soundness theorem are satisfiable: over
`ZMod 41` (with `41 ≥ 40 * 1 ^ 2`) in one variable, a coordinate function has no wrong lines, and
the theorem applies with `ε = 1 / 800`.
-/

namespace CslibFrontierTests.Code.MultilinearitySoundness

open Cslib Cslib.Code Finset

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 41) := ⟨by decide⟩
instance : Fact (Nat.Prime 401) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 320009) := ⟨by norm_num⟩

/-- The product over `ZMod 5`, corrupted at the point `(4, 4)`. -/
private def corrupted (x : Fin 2 → ZMod 5) : ZMod 5 :=
  if x = ![4, 4] then 0 else x 0 * x 1

/-- The product of the two coordinates. -/
private def prod2 (x : Fin 2 → ZMod 5) : ZMod 5 := x 0 * x 1

private theorem isMultilinear_prod2 : IsMultilinear prod2 := by
  intro x i
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · have : lineRestrict prod2 x 0 = fun t => t * x 1 := by
      funext t
      simp [lineRestrict, prod2]
    rw [this]
    exact isAffineFun_id.mul_const _
  · have : lineRestrict prod2 x 1 = fun t => x 0 * t := by
      funext t
      simp [lineRestrict, prod2]
    rw [this]
    exact isAffineFun_id.const_mul _

private theorem hammingDist_corrupted : hammingDist corrupted prod2 = 1 := by decide

private theorem card_wrongPoints_corrupted (i : Fin 2) : #(wrongPoints corrupted i) = 5 := by
  fin_cases i <;> decide

-- Self-improvement for the corrupted product: the hypothesis `2 * 1 ≤ 25` holds, and the bound is
-- `90`.
example : hammingDist corrupted prod2 ≤ 90 := by
  have h := isMultilinear_prod2.hammingDist_le_of_two_mul_le (f := corrupted)
    (by rw [hammingDist_corrupted]; decide)
  simp only [Fin.sum_univ_two, card_wrongPoints_corrupted, ZMod.card] at h
  simpa using h

/-- A coordinate function in one variable over `ZMod 41`. -/
private def coord (x : Fin 1 → ZMod 41) : ZMod 41 := x 0

-- The hypotheses of the soundness theorem hold for it, with `ε = 1 / 800`.
example : ∃ g, IsMultilinear g ∧ (hammingDist coord g : ℝ) <
    3 * 1 ^ 2 * (1 / 800 + 1 / 41) * 41 ^ 1 := by
  have hcoord : IsMultilinear coord := by
    intro x i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have : lineRestrict coord x 0 = fun t => t := by
      funext t
      simp [lineRestrict, coord]
    rw [this]
    exact isAffineFun_id
  have hW (i : Fin 1) : wrongPoints coord i = ∅ := by
    ext x
    simp [wrongPoints, hcoord x i]
  have := exists_isMultilinear_hammingDist_lt coord (ε := 1 / 800) (by norm_num)
    (by simp [ZMod.card]) (by norm_num) fun i => by simp [hW, ZMod.card]
  simpa [ZMod.card] using this

/-- Over `ZMod 401` in one variable, corrupting `x 0` at `0` makes every point lie in
`wrongPoints` (`δ = 0`), yet with `δ = 1 / 401 ≤ 1 / 400` the unique line is `δ`-approximately
affine, so `wrongPointsApprox` is empty and `exists_isMultilinear_hammingDist_lt_of_approx`
applies. -/
private def oneVarSpike (x : Fin 1 → ZMod 401) : ZMod 401 :=
  if x 0 = 0 then 1 else x 0

example : ∃ g, IsMultilinear g ∧ (hammingDist oneVarSpike g : ℝ) <
    3 * 1 ^ 2 * (1 / 800 + 1 / 401 + 1 / 401) * 401 ^ 1 := by
  have hW (i : Fin 1) : wrongPointsApprox oneVarSpike (1 / 401) i = ∅ := by
    ext x
    simp only [wrongPointsApprox, mem_filter, mem_univ, true_and, notMem_empty, iff_false,
      not_not]
    refine ⟨fun t => t, isAffineFun_id, ?_⟩
    have hsub : (univ.filter fun t : ZMod 401 => lineRestrict oneVarSpike x i t ≠ t) ⊆ {0} := by
      intro t ht
      simp only [mem_filter, mem_univ, true_and, mem_singleton] at ht ⊢
      obtain rfl : i = 0 := Subsingleton.elim _ _
      by_contra h0
      exact ht (by simp [lineRestrict, oneVarSpike, h0])
    have hcard : #(univ.filter fun t : ZMod 401 => lineRestrict oneVarSpike x i t ≠ t) ≤ 1 :=
      (card_le_card hsub).trans (by simp)
    have hcardR : (#(univ.filter fun t : ZMod 401 => lineRestrict oneVarSpike x i t ≠ t) : ℝ) ≤
        1 := by exact_mod_cast hcard
    simpa [ZMod.card] using hcardR
  have h := exists_isMultilinear_hammingDist_lt_of_approx oneVarSpike (ε := 1 / 800) (δ := 1 / 401)
    (by norm_num) (by rw [ZMod.card]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    fun i => by rw [hW, Finset.card_empty, Nat.cast_zero, ZMod.card]; positivity
  rw [ZMod.card] at h
  exact h.imp fun g ⟨hg, hdist⟩ => ⟨hg, hdist.trans_eq (by norm_num)⟩

/-- Non-vacuous witness for `Test0` (`exists_isMultilinear_hammingDist_lt_of_lineOracle`) with a
nonzero single-point disagreement against the canonical affine line oracle over `ZMod p`. -/
private def spikeMod (p : ℕ) (x : Fin 1 → ZMod p) : ZMod p :=
  if x 0 = 0 then 1 else x 0

private theorem test0_spike {p : ℕ} [Fact (Nat.Prime p)] (hp : 320000 < p) :
    ∃ g, IsMultilinear g ∧ (hammingDist (spikeMod p) g : ℝ) <
      3 * 1 ^ 2 * (1 / 800 + 1 / 400 + 1 / p) * p ^ 1 := by
  let L : Fin 1 → (Fin 1 → ZMod p) → ZMod p → ZMod p := fun _ _ t => t
  have hL : ∀ i x, IsAffineFun (L i x) := fun _ _ => isAffineFun_id
  have hp' : (320000 : ℝ) < p := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < p := by linarith only [hp']
  have hrej : (Finset.univ.expect fun i : Fin 1 => Finset.univ.expect fun x : Fin 1 → ZMod p =>
      if L i (Function.update x i 0) (x i) = spikeMod p x then (0 : ℝ) else 1) <
      (1 / 800 : ℝ) * (1 / 400) / 1 := by
    have hsingle (x : Fin 1 → ZMod p) :
        (if L 0 (Function.update x 0 0) (x 0) = spikeMod p x then (0 : ℝ) else 1) =
          if x = 0 then (1 : ℝ) else 0 := by
      by_cases hx : x 0 = 0
      · have hx0 : x = 0 := funext fun j => by obtain rfl : j = 0 := Subsingleton.elim _ _; exact hx
        simp [L, spikeMod, hx0]
      · have hx0 : x ≠ 0 := fun h => hx (congrFun h 0)
        simp [L, spikeMod, hx, hx0]
    have hsum : (∑ x : Fin 1 → ZMod p, if x = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']
      simp
    rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_one]
    simp only [Fintype.card_fin, Nat.cast_one, div_one, hsingle]
    rw [Fintype.expect_eq_sum_div_card, hsum, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, pow_one, ZMod.card]
    rw [div_lt_iff₀ hp_pos]
    nlinarith only [hp']
  have h := exists_isMultilinear_hammingDist_lt_of_lineOracle (spikeMod p) L hL (ε := 1 / 800)
    (δ := 1 / 400) (by norm_num) (by rw [ZMod.card]; omega) (by norm_num) (by norm_num)
    (by norm_num) hrej
  rw [ZMod.card] at h
  exact h.imp fun g ⟨hg, hdist⟩ => ⟨hg, hdist.trans_eq (by norm_num)⟩

example : ∃ g, IsMultilinear g ∧ (hammingDist (spikeMod 320009) g : ℝ) <
    3 * 1 ^ 2 * (1 / 800 + 1 / 400 + 1 / 320009) * 320009 ^ 1 := by
  simpa only [Nat.cast_ofNat] using test0_spike (p := 320009) (by omega)

end CslibFrontierTests.Code.MultilinearitySoundness

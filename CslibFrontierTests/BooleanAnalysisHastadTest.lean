/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.HastadTest
import Mathlib.Tactic.FinCases

/-! # Tests for the Odd BLR test and Håstad's test

Dictators pass the Odd BLR test, constants pass it with probability `1/2`, Håstad's test accepts
dictators with probability `1 - δ / 2` and large parities with probability close to `1/2`, and
functions without notable coordinates pass Håstad's test with probability close to `1/2`. -/

public section

namespace CslibFrontierTests.BooleanAnalysisHastadTest

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- Håstad's test accepts dictators with probability `1 - δ / 2`. -/
example (δ : ℝ) : hastadAcceptance δ (fun x : Fin 3 → Bool => x 1) = 1 - δ / 2 :=
  hastadAcceptance_dictator δ 1

/-- Dictators pass the Odd BLR test. -/
example : oddBlrAcceptance (fun x : Fin 3 → Bool => x 0) = 1 := by
  rw [← hastadAcceptance_zero, hastadAcceptance_dictator]
  norm_num

/-- The constant `true` passes the Odd BLR test with probability `1/2`. -/
example : oddBlrAcceptance (fun _ : Fin 2 → Bool => true) = 1 / 2 := by
  simp [oddBlrAcceptance_eq_sum, fourierCoeff_const]

/-- The parity of all five bits passes Håstad's test with probability
`1/2 + 1/2 (1 - δ) ^ 5`. -/
example (δ : ℝ) :
    hastadAcceptance δ (parityOn (univ : Finset (Fin 5))) = 1 / 2 + 1 / 2 * (1 - δ) ^ 5 := by
  rw [hastadAcceptance_parityOn, card_univ, Fintype.card_fin, ite_eq_left (by decide)]

/-- Even parities pass Håstad's test with probability `1/2`. -/
example (δ : ℝ) : hastadAcceptance δ (parityOn ({0, 1} : Finset (Fin 3))) = 1 / 2 := by
  rw [hastadAcceptance_parityOn, ite_eq_right (by decide)]

/-- The odd-level Fourier coefficients of NAND on two bits, read as signs: both singletons have
coefficient `-1/2`. -/
theorem fourierCoeff_nand_singleton (i : Fin 2) :
    fourierCoeff (fun x : Fin 2 → Bool => signVal (!(x 0 && x 1))) {i} = -1 / 2 := by
  have e (g : (Fin 2 → Bool) → ℝ) : ∑ x, g x = ∑ p : Bool × Bool, g ![p.1, p.2] :=
    Fintype.sum_equiv (piFinTwoEquiv fun _ => Bool) _ _ fun x => by
      congr 1; ext j; fin_cases j <;> rfl
  rw [fourierCoeff_eq_sum, e]
  fin_cases i <;> simp [chi_singleton, Fintype.sum_prod_type] <;> norm_num

/-- The odd levels of the cube on two bits are the two singletons. -/
theorem filter_odd_card_fin_two :
    (univ.filter fun S : Finset (Fin 2) => Odd #S) = {{0}, {1}} := by
  decide

/-- **Proposition 7.46 with `M = 0`**: the odd coefficients of NAND are negative, so the Odd BLR
test accepts it with probability at most `1/2`. -/
example : oddBlrAcceptance (fun x : Fin 2 → Bool => !(x 0 && x 1)) ≤ 1 / 2 + 1 / 2 * 0 := by
  refine oddBlrAcceptance_le_of_fourierCoeff_le le_rfl fun S hS => ?_
  have hS' : S ∈ ({{0}, {1}} : Finset (Finset (Fin 2))) := by
    rw [← filter_odd_card_fin_two]; exact mem_filter.2 ⟨mem_univ _, hS⟩
  rcases mem_insert.1 hS' with rfl | hS'
  · rw [fourierCoeff_nand_singleton]; norm_num
  · rw [mem_singleton.1 hS', fourierCoeff_nand_singleton]; norm_num

/-- **The Fourier formula (7.4)** for NAND on two bits: the odd levels are the two singletons, of
coefficient `-1/2`, so Håstad's test accepts with probability
`1/2 + 1/2 · 2 (1 - δ) (-1/2) ^ 3 = 1/2 - (1 - δ) / 8`; at `δ = 0` this is the direct count
`3/8` below. -/
example (δ : ℝ) :
    hastadAcceptance δ (fun x : Fin 2 → Bool => !(x 0 && x 1)) = 1 / 2 - (1 - δ) / 8 := by
  rw [hastadAcceptance_eq_sum, filter_odd_card_fin_two, sum_pair (by decide),
    fourierCoeff_nand_singleton, fourierCoeff_nand_singleton]
  simp only [card_singleton, pow_one]
  ring

/-- The NAND of two bits passes the Odd BLR test with probability `3/8`, although both its odd
coefficients are `-1/2`: the bound of Proposition 7.46 needs a nonnegative maximum. -/
example : oddBlrAcceptance (fun x : Fin 2 → Bool => !(x 0 && x 1)) = 3 / 8 ∧
    fourierCoeff (fun x : Fin 2 → Bool => signVal (!(x 0 && x 1))) {0} = -1 / 2 ∧
    fourierCoeff (fun x : Fin 2 → Bool => signVal (!(x 0 && x 1))) {1} = -1 / 2 := by
  refine ⟨?_, fourierCoeff_nand_singleton 0, fourierCoeff_nand_singleton 1⟩
  have e (g : (Fin 2 → Bool) → ℝ) : 𝔼 x, g x = 𝔼 p : Bool × Bool, g ![p.1, p.2] :=
    Fintype.expect_equiv (piFinTwoEquiv fun _ => Bool) _ _ fun x => by
      congr 1; ext i; fin_cases i <;> rfl
  have hadd (a b : Bool) : a + b = (a ^^ b) := rfl
  simp only [oddBlrAcceptance_def, e, Fintype.expect_eq_sum_div_card, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.card_prod, Fintype.card_bool]
  norm_num [Pi.add_apply, hadd]

/-- Håstad's test accepts NAND with probability at most one, here `1/2 - (2/3) / 8`. -/
example : hastadAcceptance (1 / 3) (fun x : Fin 2 → Bool => !(x 0 && x 1)) ≤ 1 :=
  hastadAcceptance_le_one (by norm_num) (by norm_num) _

/-- Unfolding the definition: a constant passes Håstad's test with probability `1/2`. -/
example (δ : ℝ) : hastadAcceptance δ (fun _ : Fin 2 → Bool => true) = 1 / 2 := by
  simp [hastadAcceptance_def]

/-- A constant has no notable coordinates, so it passes Håstad's test with probability at most
`1/2 + 1/2 √ε` for every `0 ≤ ε ≤ δ`; in fact it passes with probability `1/2`. -/
example {ε : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ 1 / 2) :
    hastadAcceptance (1 / 2) (fun _ : Fin 3 → Bool => true) ≤ 1 / 2 + 1 / 2 * √ε :=
  hastadAcceptance_le_of_stableInfluence_le hε hεδ (by norm_num) fun i => by
    simp [stableInfluence_eq_sum, fourierCoeff_const, hε]

/-- No `(1/4, 1/4)`-notable coordinates means Håstad's test at `δ = 1/2` accepts with probability
at most `3/4`. -/
example {f : (Fin 4 → Bool) → Bool}
    (h : ∀ i, stableInfluence (1 - 1 / 4) i (fun x => signVal (f x)) ≤ 1 / 4) :
    hastadAcceptance (1 / 2) f ≤ 3 / 4 := by
  have := hastadAcceptance_le_of_stableInfluence_le (δ := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) h
  rw [show √(1 / 4 : ℝ) = 1 / 2 by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num] at this
  linarith

/-- Every partial sum of the squared coefficients of a Boolean function is at most one; here the
odd-level weight of the AND of two bits. -/
example : ∑ S with Odd #S, fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0 && x 1)) S ^ 2 ≤ 1 :=
  sum_fourierCoeff_sq_signVal_le_one _ _

/-- One term of the stable influence: the parity of bits `0` and `1` has coefficient `1` on
`{0, 1}`, so its `1/2`-stable influence at bit `0` is at least `1/2`. -/
example :
    (1 / 2 : ℝ) ≤ stableInfluence (1 / 2) 0
      (fun x => signVal (parityOn ({0, 1} : Finset (Fin 3)) x)) := by
  have h := pow_mul_fourierCoeff_sq_le_stableInfluence (ρ := 1 / 2) (by norm_num)
    (show (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) by decide)
    (fun x => signVal (parityOn ({0, 1} : Finset (Fin 3)) x))
  rwa [fourierCoeff_signVal_parityOn, ite_eq_left rfl, one_pow, mul_one,
    show #({0, 1} : Finset (Fin 3)) - 1 = 1 by decide, pow_one] at h

end CslibFrontierTests.BooleanAnalysisHastadTest

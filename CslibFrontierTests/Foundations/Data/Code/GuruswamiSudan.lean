/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Foundations.Algebra.Polynomial.Bivariate
import CslibFrontier.Foundations.Data.Code.GuruswamiSudan
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Tests: Bivariate polynomial algebra and Guruswami–Sudan list decoding

Exercises `CslibFrontier.Foundations.Algebra.Polynomial.Bivariate`,
`CslibFrontier.Foundations.Data.Code.SudanInterpolant`, and
`CslibFrontier.Foundations.Data.Code.GuruswamiSudan` via ordinary `module` imports
(without `import all`) across concrete, nonvacuous instances:

1. **Positive-characteristic multiplicity vanishing (`m ≥ char F`).** Over `ZMod 2` (`m = 2`) and
   `ZMod 3` (`m = 3`), verifies that bivariate Hasse / shifted Taylor vanishing distinguishes exact
   multiplicity orders (`VanishesToOrder 2` holds while `VanishesToOrder 3` fails for
   `X ^ 2 + Y ^ 2` at `(1, 1)` over `ZMod 2`, where ordinary second derivatives vanish identically)
   and yields `(X - C 1) ^ m ∣ Q.eval 1` with `Q.eval 1 ≠ 0`.
2. **Base change of multiplicity vanishing.** Maps a bivariate polynomial over `(ZMod 5)[X]` by
   specialization `evalRingHom 2 : (ZMod 5)[X] →+* ZMod 5` using `VanishesToOrder.map`.
3. **Strictly-beyond-Sudan list decoding over `ZMod 7`.** At `n = 7`, `k = 3`, `e = 3` (`t = 4`
   agreements), both unique decoding (`2 * 3 + 3 > 7`) and Sudan (`m = 1`, `#(monomials 2 3) = 6`)
   fail, while Guruswami–Sudan recovers two distinct quadratics `0` and `X * (X - 1)` from a single
   concrete word (via both `mem_guruswamiSudan_johnson_iff` at `m = 8, D = 31` and
   `mem_guruswamiSudan_iff` at `m = 5, D = 19`), rejects a far polynomial `C 1`, and satisfies
   `2 ≤ #list ≤ 9`.
4. **Infinite field (`ℚ`).** Verifies interpolation, least-`Y`-degree elimination, and list
   decoding over `ℚ` without `[Fintype F]`, recovering two distinct degree-`< 2` polynomials from a
   five-point word.
5. **Real Johnson-bound corollary.** Instantiates `exists_guruswamiSudan_of_eps` over `ZMod 7` with
   `k = 2`, `ε = 1 / 20`, proving nonvacuous recovery at distance `2 ≤ (1 - √(2 / 7) - 1 / 20) * 7`.
6. **Per-point weighted multiplicities.** Exercises both `weightedInterpolant` (via
   `isWeightedInterpolant_weightedInterpolant` and `natDegree_weightedInterpolant_le`) and
   `IsWeightedInterpolant.X_sub_C_dvd` on a non-constant multiplicity vector `![2, 2, 1, 1, 0]`.
7. **Factor refinement, weighted degree, and shared-API edge cases.** Checks `weightedDegree_mul`,
   `exists_eq_pow_mul_eval_ne_zero`, `eval_radical_primPart_eq_zero_iff`,
   `exists_eq_C_mul_prod_irreducible`, `sum_weightedDegree_le_of_eq_C_mul_prod`,
   `Sudan.add_mul_add_one_le_of_mul` (including `S = 0`),
   `IsInterpolant.rootMultiplicity_le_of_min`, zero handling of `weightedInterpolant`, and
   `card_guruswamiSudan_le` at `k = 1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.Data.Code.GuruswamiSudan

open Cslib Cslib.Code Cslib.Code.GuruswamiSudan Finset Polynomial Polynomial.Bivariate
  UniqueFactorizationMonoid
open scoped Polynomial.Bivariate

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### 1. Positive-characteristic multiplicity vanishing (`m ≥ char F`) -/

/-- Over `ZMod 2`, `Q₂(X, Y) = X ^ 2 + Y ^ 2` vanishes to order exactly `2` at `(1, 1)` (not order
`3`), and `(X - 1) ^ 2` divides the nonzero polynomial `Q₂(X, 1) = X ^ 2 + 1`. -/
example :
    let Q₂ : (ZMod 2)[X][Y] := C (X ^ 2) + Y ^ 2
    VanishesToOrder 2 (1 : ZMod 2) 1 Q₂ ∧
    ¬ VanishesToOrder 3 (1 : ZMod 2) 1 Q₂ ∧
    (hasseDerivBiv 2 0 Q₂).evalEval 1 1 = 1 ∧
    Q₂.eval 1 ≠ 0 ∧
    (X - C (1 : ZMod 2)) ^ 2 ∣ Q₂.eval 1 := by
  intro Q₂
  have hQ₂_shift : shift (1 : ZMod 2) 1 Q₂ = C (X ^ 2) + Y ^ 2 := by
    have hX2 : taylor (1 : ZMod 2) (X ^ 2) = X ^ 2 + 1 := by
      rw [taylor_X_pow]
      have h2 : (2 : (ZMod 2)[X]) = 0 :=
        (map_ofNat C 2).symm.trans (by rw [show (2 : ZMod 2) = 0 by decide, map_zero])
      have : (X + C (1 : ZMod 2)) ^ 2 = X ^ 2 + 2 * X + 1 := by
        rw [C_1]
        ring
      rw [this, h2, zero_mul, add_zero]
    have hC : shift (1 : ZMod 2) 1 (C (X ^ 2)) = C (X ^ 2 + 1) := by
      rw [shift_apply, map_C, taylor_C]
      change C (taylor (1 : ZMod 2) (X ^ 2)) = _
      rw [hX2]
    have h2Y : (2 : (ZMod 2)[X][Y]) = 0 := by
      have h2X : (2 : (ZMod 2)[X]) = 0 :=
        (map_ofNat C 2).symm.trans (by rw [show (2 : ZMod 2) = 0 by decide, map_zero])
      exact (map_ofNat C 2).symm.trans (by rw [h2X, map_zero])
    have hY2 : shift (1 : ZMod 2) 1 (Y ^ 2 : (ZMod 2)[X][Y]) = Y ^ 2 + 1 := by
      rw [shift_apply, Polynomial.map_pow, map_X, taylor_X_pow]
      have : (Y + C (C (1 : ZMod 2))) ^ 2 = Y ^ 2 + 2 * Y + 1 := by
        rw [C_1, C_1]
        ring
      rw [this, h2Y, zero_mul, add_zero]
    have h11 : (1 : (ZMod 2)[X][Y]) + 1 = 0 := by
      rw [← two_mul, mul_one]
      exact h2Y
    rw [map_add, hC, hY2, map_add, map_one]
    calc C (X ^ 2) + 1 + (Y ^ 2 + 1) = C (X ^ 2) + Y ^ 2 + (1 + 1) := by ring
      _ = C (X ^ 2) + Y ^ 2 := by rw [h11, add_zero]
  have hvan2 : VanishesToOrder 2 (1 : ZMod 2) 1 Q₂ := by
    intro i j hij
    rw [hQ₂_shift, coeff_add, coeff_C, coeff_X_pow]
    have hij' : (i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 1) := by omega
    rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [coeff_X_pow]
  have hhasse20 : (hasseDerivBiv 2 0 Q₂).evalEval 1 1 = 1 := by
    rw [← coeff_coeff_shift_eq_evalEval_hasseDerivBiv, hQ₂_shift, coeff_add, coeff_C, coeff_X_pow]
    simp [coeff_X_pow]
  have hnot3 : ¬ VanishesToOrder 3 (1 : ZMod 2) 1 Q₂ := by
    intro h3
    have h0 := (vanishesToOrder_iff_hasseDerivBiv 3 1 1 Q₂).1 h3 2 0 (by omega)
    rw [hhasse20] at h0
    exact one_ne_zero h0
  have heval_ne : Q₂.eval 1 ≠ 0 := by
    intro h0
    have hc := congrArg (fun p : (ZMod 2)[X] => p.coeff 2) h0
    simp [Q₂, eval_add, eval_C, eval_pow, eval_X, coeff_X_pow, coeff_one] at hc
  have hdvd : (X - C (1 : ZMod 2)) ^ 2 ∣ Q₂.eval 1 :=
    hvan2.X_sub_C_pow_dvd_eval (by simp)
  exact ⟨hvan2, hnot3, hhasse20, heval_ne, hdvd⟩

/-- Over `ZMod 3`, `Q₃(X, Y) = X ^ 3 - Y ^ 3` vanishes to order `3` at `(1, 1)` (at `m = char`),
yielding `(X - 1) ^ 3 ∣ Q₃(X, 1)`. -/
example :
    let Q₃ : (ZMod 3)[X][Y] := C (X ^ 3) - Y ^ 3
    VanishesToOrder 3 (1 : ZMod 3) 1 Q₃ ∧
    ¬ VanishesToOrder 4 (1 : ZMod 3) 1 Q₃ ∧
    (X - C (1 : ZMod 3)) ^ 3 ∣ Q₃.eval 1 := by
  intro Q₃
  have hQ₃_eq : Q₃ = (C X - Y) ^ 3 := by
    have h3 : (3 : (ZMod 3)[X][Y]) = 0 := by
      have h3X : (3 : (ZMod 3)[X]) = 0 :=
        (map_ofNat C 3).symm.trans (by rw [show (3 : ZMod 3) = 0 by decide, map_zero])
      exact (map_ofNat C 3).symm.trans (by rw [h3X, map_zero])
    have hpow : (C (X : (ZMod 3)[X]) - Y) ^ 3 =
        C (X ^ 3) - Y ^ 3 - 3 * C (X ^ 2) * Y + 3 * C X * Y ^ 2 := by
      rw [map_pow, map_pow]
      ring
    rw [hpow, h3]
    ring
  have hvan1 : VanishesToOrder 1 (1 : ZMod 3) 1 (C X - Y) := by
    rw [vanishesToOrder_one_iff]
    simp [evalEval_C, eval_X]
  have hvan3 : VanishesToOrder 3 (1 : ZMod 3) 1 Q₃ := by
    rw [hQ₃_eq]
    simpa using hvan1.pow 3
  have hshift3 : shift (1 : ZMod 3) 1 Q₃ = C (X ^ 3) - Y ^ 3 := by
    rw [hQ₃_eq, map_pow]
    have h1 : shift (1 : ZMod 3) 1 (C X - Y) = C X - Y := by
      rw [map_sub, shift_apply, map_C, taylor_C, shift_apply, map_X, taylor_X]
      change C (taylor (1 : ZMod 3) X) - (Y + C (C 1)) = C X - Y
      rw [taylor_X, map_add, map_one, C_1]
      ring
    rw [h1, ← hQ₃_eq]
  have hnot4 : ¬ VanishesToOrder 4 (1 : ZMod 3) 1 Q₃ := by
    intro h4
    have h0 := h4 3 0 (by omega)
    rw [hshift3, coeff_sub, coeff_C, coeff_X_pow] at h0
    simp [coeff_X_pow] at h0
  exact ⟨hvan3, hnot4, hvan3.X_sub_C_pow_dvd_eval (by simp)⟩

/-! ### 2. Base change of multiplicity vanishing under ring homomorphisms -/

/-- Specialization `evalRingHom 2 : (ZMod 5)[X] →+* ZMod 5` preserves multiplicity-`2` vanishing
at `(1, Z) ↦ (1, 2)`. -/
example :
    let R := (ZMod 5)[X]
    let z : R := X
    let Q : R[X][Y] := (Y - C (C z * X)) ^ 2
    let φ : R →+* ZMod 5 := Polynomial.evalRingHom 2
    VanishesToOrder 2 (1 : ZMod 5) 2 (Q.map (Polynomial.mapRingHom φ)) := by
  intro R z Q φ
  have hP : (C z * X : R[X]).eval 1 = z := by simp
  have hvan : VanishesToOrder 2 (1 : R) z Q := by
    simpa [Q] using (vanishesToOrder_one_X_sub_C hP).pow 2
  have hmap := hvan.map φ
  have hφz : φ z = 2 := by
    change (X : (ZMod 5)[X]).eval 2 = 2
    simp
  simpa [hφz] using hmap

/-! ### 3. Strictly-beyond-Sudan list decoding over `ZMod 7` -/

/-- The seven evaluation points of `ZMod 7`. -/
private def points7 : Fin 7 → ZMod 7 := fun i => (i : ℕ)

private theorem points7_injective : Function.Injective points7 := by
  decide

/-- Concrete word agreeing with `0` on `{0, 1, 2, 3}` and with `X * (X - 1)` on `{0, 1, 4, 5}`,
and with neither at `6`. -/
private def word7 : Fin 7 → ZMod 7 := ![0, 0, 0, 0, 5, 6, 1]

/-- Unique decoding (`2 * e + k ≤ n`) and Sudan (`m = 1`, `n < #(monomials 2 3)`) both fail for
`n = 7`, `k = 3`, `e = 3` (`t = 4`), whereas Guruswami–Sudan succeeds and recovers two distinct
quadratics `0` and `X * (X - 1)` while rejecting `C 1`. -/
example :
    ¬ (2 * 3 + 3 ≤ 7) ∧
    ¬ (7 < #(Sudan.monomials 2 3)) ∧
    let P₁ : (ZMod 7)[X] := 0
    let P₂ : (ZMod 7)[X] := X * (X - 1)
    let P₃ : (ZMod 7)[X] := C 1
    P₁ ≠ P₂ ∧
    P₁ ∈ guruswamiSudan points7 word7 8 3 31 ∧
    P₂ ∈ guruswamiSudan points7 word7 8 3 31 ∧
    P₃ ∉ guruswamiSudan points7 word7 8 3 31 ∧
    P₁ ∈ guruswamiSudan points7 word7 5 3 19 ∧
    P₂ ∈ guruswamiSudan points7 word7 5 3 19 ∧
    2 ≤ #(guruswamiSudan points7 word7 5 3 19) ∧
    #(guruswamiSudan points7 word7 5 3 19) ≤ 9 := by
  refine ⟨by decide, by decide, ?_⟩
  intro P₁ P₂ P₃
  have hne12 : P₁ ≠ P₂ := by
    intro h
    have hc : (0 : ZMod 7) = 2 * (2 - 1) := by
      simpa [P₁, P₂] using congrArg (fun p : (ZMod 7)[X] => p.eval 2) h
    exact absurd hc (by decide)
  have hdeg1 : P₁.degree < (3 : ℕ) := by
    dsimp only [P₁]
    rw [degree_zero]
    exact WithBot.bot_lt_coe _
  have hdeg2 : P₂.degree < (3 : ℕ) := by
    have : P₂ = X ^ 2 - X := by simp [P₂]; ring
    rw [this]
    compute_degree!
  have hdeg3 : P₃.degree < (3 : ℕ) := by
    dsimp only [P₃]
    compute_degree!
  have hdist1 : hammingDist (fun i => P₁.eval (points7 i)) word7 = 3 := by
    have hfun : (fun i => P₁.eval (points7 i)) = fun _ => 0 := by
      funext i
      simp [P₁]
    rw [hfun]
    decide
  have hfun2 : (fun i => P₂.eval (points7 i)) = ![0, 0, 2, 6, 5, 6, 2] := by
    funext i
    have hP2 : P₂.eval (points7 i) = points7 i * (points7 i - 1) := by simp [P₂]
    rw [hP2]
    clear hP2
    revert i
    decide
  have hdist2 : hammingDist (fun i => P₂.eval (points7 i)) word7 = 3 := by
    rw [hfun2]
    decide
  have hdist3 : hammingDist (fun i => P₃.eval (points7 i)) word7 = 6 := by
    have hfun : (fun i => P₃.eval (points7 i)) = ![1, 1, 1, 1, 1, 1, 1] := by
      funext i
      fin_cases i <;> simp [P₃]
    rw [hfun]
    decide
  have hjohnson := fun P =>
    mem_guruswamiSudan_johnson_iff (α := points7) (w := word7) (k := 3) (P := P)
      points7_injective (by omega) (e := 3) (by decide)
  have hm1_8 : P₁ ∈ guruswamiSudan points7 word7 8 3 31 := by
    simpa [hdist1] using (hjohnson P₁).2 ⟨hdeg1, by omega⟩
  have hm2_8 : P₂ ∈ guruswamiSudan points7 word7 8 3 31 := by
    simpa [hdist2] using (hjohnson P₂).2 ⟨hdeg2, by omega⟩
  have hm3_8 : P₃ ∉ guruswamiSudan points7 word7 8 3 31 := by
    intro hmem
    have hle := ((hjohnson P₃).1 hmem).2
    omega
  have hcard5 : Fintype.card (Fin 7) * (5 * (5 + 1) / 2) < #(Sudan.monomials (3 - 1) 19) := by
    decide
  have hagree1 : #{i | P₁.eval (points7 i) = word7 i} = 4 := by
    have heq : Finset.univ.filter (fun i : Fin 7 => P₁.eval (points7 i) = word7 i) =
        Finset.univ.filter (fun i : Fin 7 => (0 : ZMod 7) = word7 i) := by
      ext i
      simp [P₁]
    rw [heq]
    decide
  have hagree2 : #{i | P₂.eval (points7 i) = word7 i} = 4 := by
    have heq : Finset.univ.filter (fun i : Fin 7 => P₂.eval (points7 i) = word7 i) =
        Finset.univ.filter
          (fun i : Fin 7 => (![0, 0, 2, 6, 5, 6, 2] : Fin 7 → ZMod 7) i = word7 i) := by
      ext i
      simp [congrFun hfun2 i]
    rw [heq]
    decide
  have hm1_5 : P₁ ∈ guruswamiSudan points7 word7 5 3 19 :=
    (mem_guruswamiSudan_iff points7_injective (by omega) hcard5).2 ⟨hdeg1, by omega⟩
  have hm2_5 : P₂ ∈ guruswamiSudan points7 word7 5 3 19 :=
    (mem_guruswamiSudan_iff points7_injective (by omega) hcard5).2 ⟨hdeg2, by omega⟩
  have hge2 : 2 ≤ #(guruswamiSudan points7 word7 5 3 19) := by
    have hsub : ({P₁, P₂} : Finset (ZMod 7)[X]) ⊆ guruswamiSudan points7 word7 5 3 19 := by
      intro P hP
      simp only [mem_insert, mem_singleton] at hP
      rcases hP with rfl | rfl
      · exact hm1_5
      · exact hm2_5
    exact (card_pair hne12).symm.trans_le (card_le_card hsub)
  have hle9 : #(guruswamiSudan points7 word7 5 3 19) ≤ 9 := by
    have hmul := card_guruswamiSudan_mul_le (α := points7) (w := word7) (m := 5) (k := 3) (D := 19)
    omega
  exact ⟨hne12, hm1_8, hm2_8, hm3_8, hm1_5, hm2_5, hge2, hle9⟩

/-! ### 4. Infinite field (`ℚ`): no `[Fintype F]` required -/

/-- Five evaluation points in the infinite field `ℚ`. -/
private def pointsQ : Fin 5 → ℚ := fun i => (i : ℕ)

private theorem pointsQ_injective : Function.Injective pointsQ := by
  intro i j hij
  exact Fin.ext (Nat.cast_injective hij)

/-- Received word over `ℚ` agreeing with both `0` (on `{0, 3, 4}`) and `X` (on `{0, 1, 2}`). -/
private def wordQ : Fin 5 → ℚ := ![0, 1, 2, 0, 0]

/-- Guruswami–Sudan interpolation and list decoding operate over the infinite field `ℚ`,
producing a least-`Y`-degree multiplicity-`2` interpolant and recovering both `0` and `X`. -/
example :
    IsInterpolant pointsQ wordQ 2 1 5 (interpolant pointsQ wordQ 2 1 5) ∧
    (0 : ℚ[X]) ∈ guruswamiSudan pointsQ wordQ 2 2 5 ∧
    (X : ℚ[X]) ∈ guruswamiSudan pointsQ wordQ 2 2 5 ∧
    2 ≤ #(guruswamiSudan pointsQ wordQ 2 2 5) ∧
    #(guruswamiSudan pointsQ wordQ 2 2 5) ≤ 5 := by
  have hineq : Fintype.card (Fin 5) * (2 - 1) * 2 * (2 + 1) < (5 + 1) * (5 + 2) := by decide
  have hmon : Fintype.card (Fin 5) * (2 * (2 + 1) / 2) < #(Sudan.monomials 1 5) :=
    card_mul_lt_card_monomials_of_lt (by omega) hineq
  have hinterp := isInterpolant_interpolant pointsQ wordQ (by omega) hmon
  have hagree0 : #{i | (0 : ℚ[X]).eval (pointsQ i) = wordQ i} = 3 := by
    have hfun : ({i | (0 : ℚ[X]).eval (pointsQ i) = wordQ i} : Finset (Fin 5)) = {0, 3, 4} := by
      ext i
      fin_cases i <;> simp [wordQ]
    rw [hfun]
    decide
  have hagreeX : #{i | (X : ℚ[X]).eval (pointsQ i) = wordQ i} = 3 := by
    have hfun : ({i | (X : ℚ[X]).eval (pointsQ i) = wordQ i} : Finset (Fin 5)) = {0, 1, 2} := by
      ext i
      fin_cases i <;> simp [pointsQ, wordQ]
    rw [hfun]
    decide
  have hm0 : (0 : ℚ[X]) ∈ guruswamiSudan pointsQ wordQ 2 2 5 :=
    (mem_guruswamiSudan_iff_of_lt pointsQ_injective (by omega) hineq).2
      ⟨by rw [degree_zero]; exact WithBot.bot_lt_coe _, by omega⟩
  have hmX : (X : ℚ[X]) ∈ guruswamiSudan pointsQ wordQ 2 2 5 :=
    (mem_guruswamiSudan_iff_of_lt pointsQ_injective (by omega) hineq).2
      ⟨by compute_degree!, by omega⟩
  have hge2 : 2 ≤ #(guruswamiSudan pointsQ wordQ 2 2 5) := by
    have hsub : ({(0 : ℚ[X]), X} : Finset ℚ[X]) ⊆ guruswamiSudan pointsQ wordQ 2 2 5 := by
      intro P hP
      simp only [mem_insert, mem_singleton] at hP
      rcases hP with rfl | rfl
      · exact hm0
      · exact hmX
    have hne : (0 : ℚ[X]) ≠ X := X_ne_zero.symm
    exact (card_pair hne).symm.trans_le (card_le_card hsub)
  have hle5 : #(guruswamiSudan pointsQ wordQ 2 2 5) ≤ 5 := by
    simpa using card_guruswamiSudan_mul_le (α := pointsQ) (w := wordQ) (m := 2) (k := 2) (D := 5)
  exact ⟨hinterp, hm0, hmX, hge2, hle5⟩

/-! ### 5. Real / asymptotic Johnson-bound corollary -/

/-- Word over `ZMod 7` at Hamming distance `2` from `0`. -/
private def word7Dist2 : Fin 7 → ZMod 7 := ![0, 0, 0, 0, 0, 1, 2]

/-- Instantiates `exists_guruswamiSudan_of_eps` on `ZMod 7`, `k = 2`, `ε = 1 / 20`, verifying
nonvacuously that `2 ≤ (1 - √(2 / 7) - 1 / 20) * 7` and `0` is decoded with `m ≤ 11`. -/
example :
    ∃ m D : ℕ, 1 ≤ m ∧ m ≤ 11 ∧ D < m * 7 ∧
      #(guruswamiSudan points7 word7Dist2 m 2 D) ≤ D ∧
      (0 : (ZMod 7)[X]) ∈ guruswamiSudan points7 word7Dist2 m 2 D := by
  obtain ⟨m, D, hm1, hmle, hDlt, hdec⟩ :=
    exists_guruswamiSudan_of_eps (α := points7) (k := 2) points7_injective (by omega) (by decide)
      (ε := (1 : ℝ) / 20) (by norm_num)
  have hm11 : m ≤ 11 := by
    have hfl : ⌊(1 : ℝ) / (2 * (1 / 20))⌋₊ = 10 := by
      have : (1 : ℝ) / (2 * (1 / 20)) = (10 : ℕ) := by norm_num
      rw [this, Nat.floor_natCast]
    omega
  have hsqrt : Real.sqrt ((2 : ℝ) / 7) < 3 / 5 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hdist : hammingDist (fun i => (0 : (ZMod 7)[X]).eval (points7 i)) word7Dist2 = 2 := by
    have hfun : (fun i => (0 : (ZMod 7)[X]).eval (points7 i)) = fun _ => 0 := by
      funext i
      simp
    rw [hfun]
    decide
  have hdistR : (hammingDist (fun i => (0 : (ZMod 7)[X]).eval (points7 i)) word7Dist2 : ℝ) ≤
      (1 - Real.sqrt ((2 : ℝ) / Fintype.card (Fin 7)) - 1 / 20) * Fintype.card (Fin 7) := by
    rw [hdist, Fintype.card_fin]
    push_cast
    linarith
  obtain ⟨hcard, hmem⟩ := hdec word7Dist2
  refine ⟨m, D, hm1, hm11, by simpa using hDlt, by simpa using hcard,
    hmem 0 (by rw [degree_zero]; exact WithBot.bot_lt_coe _) hdistR⟩

/-! ### 6. Per-point weighted multiplicities (for weighted correlated agreement) -/

/-- Five evaluation points in `ZMod 7`. -/
private def points5of7 : Fin 5 → ZMod 7 := fun i => (i : ℕ)

private theorem points5of7_injective : Function.Injective points5of7 := by
  decide

/-- Non-constant multiplicity profile `![2, 2, 1, 1, 0]` with `∑ m_i (m_i + 1) / 2 = 8 < 10`:
the explicit elimination interpolant `weightedInterpolant` has least `Y`-degree and recovers `P = X`
from agreement on just `{0, 1}` (weighted sum `2 + 2 = 4 > 3`). -/
example :
    let mult : Fin 5 → ℕ := ![2, 2, 1, 1, 0]
    let w : Fin 5 → ZMod 7 := ![0, 1, 0, 0, 0]
    let Q := weightedInterpolant points5of7 w mult 1 3
    IsWeightedInterpolant points5of7 w mult 1 3 Q ∧
    (∀ Q', IsWeightedInterpolant points5of7 w mult 1 3 Q' → Q.natDegree ≤ Q'.natDegree) ∧
    Y - C (X : (ZMod 7)[X]) ∣ Q := by
  intro mult w Q
  have hsum : ∑ i : Fin 5, mult i * (mult i + 1) / 2 < #(Sudan.monomials 1 3) := by
    decide
  have hQ : IsWeightedInterpolant points5of7 w mult 1 3 Q :=
    isWeightedInterpolant_weightedInterpolant points5of7 w (by omega) hsum
  have hmin : ∀ Q', IsWeightedInterpolant points5of7 w mult 1 3 Q' → Q.natDegree ≤ Q'.natDegree :=
    fun _ hQ' => natDegree_weightedInterpolant_le points5of7 w (by omega) hQ'
  have hagree : 3 < ∑ i ∈ {i | (X : (ZMod 7)[X]).eval (points5of7 i) = w i}, mult i := by
    have hfilt : ({i | (X : (ZMod 7)[X]).eval (points5of7 i) = w i} : Finset (Fin 5)) = {0, 1} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, eval_X, mem_insert, mem_singleton]
      revert i
      decide
    rw [hfilt]
    decide
  exact ⟨hQ, hmin, hQ.X_sub_C_dvd points5of7_injective (by simp) hagree⟩

/-! ### 7. Factor refinement, weighted-degree additivity, and shared-API edge cases -/

/-- Concrete factor refinement on `Q = C (X + 1) * (Y - C X) ^ 2 * (Y - C 1)` over `ZMod 5`:
weighted degree is `4` (`1 + 2 + 1`), `exists_eq_pow_mul_eval_ne_zero` extracts exact multiplicity
`r ≥ 1` with `S.eval X ≠ 0`, `radical Q.primPart` is primitive and square-free, vanishing at `X`
and `1` and not at `C 2`, and `exists_eq_C_mul_prod_irreducible` yields primitive irreducible
factors whose `Y`-degrees sum to `3`. -/
example :
    let Q : (ZMod 5)[X][Y] := C (X + 1) * (Y - C X) ^ 2 * (Y - C 1)
    weightedDegree 1 Q = 4 ∧
    (∃ (r : ℕ) (S : (ZMod 5)[X][Y]), 1 ≤ r ∧ Q = (Y - C X) ^ r * S ∧ S.eval X ≠ 0) ∧
    (radical Q.primPart).IsPrimitive ∧
    Squarefree (radical Q.primPart) ∧
    (radical Q.primPart).eval X = 0 ∧
    (radical Q.primPart).eval 1 = 0 ∧
    (radical Q.primPart).eval (C 2) ≠ 0 ∧
    ∃ (c : (ZMod 5)[X]) (fs : Multiset (ZMod 5)[X][Y]),
      c ≠ 0 ∧
      (∀ R ∈ fs, Irreducible R ∧ R.IsPrimitive ∧ 1 ≤ R.natDegree ∧
        Sudan.WeightedDegreeLE 1 4 R) ∧
      Q = C c * fs.prod ∧
      (fs.map Polynomial.natDegree).sum = 3 := by
  intro Q
  have hX1_ne : (X + 1 : (ZMod 5)[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : (ZMod 5)[X] => p.coeff 1) h
    simp [coeff_one] at this
  have hCX1_ne : C (X + 1 : (ZMod 5)[X]) ≠ 0 := C_ne_zero.2 hX1_ne
  have hsq_ne : ((Y - C (X : (ZMod 5)[X])) ^ 2 : (ZMod 5)[X][Y]) ≠ 0 :=
    pow_ne_zero 2 (X_sub_C_ne_zero X)
  have hlin_ne : (Y - C (1 : (ZMod 5)[X]) : (ZMod 5)[X][Y]) ≠ 0 := X_sub_C_ne_zero 1
  have hQ0 : Q ≠ 0 := mul_ne_zero (mul_ne_zero hCX1_ne hsq_ne) hlin_ne
  have hwC : weightedDegree 1 (C (X + 1 : (ZMod 5)[X])) = 1 := by
    refine le_antisymm (weightedDegree_le_iff.2 fun a b hab => ?_) ?_
    · rw [coeff_C] at hab
      split_ifs at hab with hb
      · subst hb
        have := le_natDegree_of_ne_zero hab
        have hdeg : (X + 1 : (ZMod 5)[X]).natDegree ≤ 1 := by compute_degree!
        omega
      · simp at hab
    · have h1 : ((C (X + 1 : (ZMod 5)[X])).coeff 0).coeff 1 ≠ 0 := by simp [coeff_one]
      simpa using le_weightedDegree (d := 1) h1
  have hwQ : weightedDegree 1 Q = 4 := by
    dsimp only [Q]
    rw [weightedDegree_mul (mul_ne_zero hCX1_ne hsq_ne) hlin_ne,
      weightedDegree_mul hCX1_ne hsq_ne, hwC,
      weightedDegree_X_sub_C_pow (by simp) 2,
      weightedDegree_X_sub_C (by simp)]
  have hex_pow : ∃ (r : ℕ) (S : (ZMod 5)[X][Y]), 1 ≤ r ∧ Q = (Y - C X) ^ r * S ∧ S.eval X ≠ 0 :=
    exists_eq_pow_mul_eval_ne_zero hQ0 (by simp [Q])
  have hevalX : (radical Q.primPart).eval X = 0 := by
    rw [eval_radical_primPart_eq_zero_iff hQ0]
    simp [Q]
  have heval1 : (radical Q.primPart).eval 1 = 0 := by
    rw [eval_radical_primPart_eq_zero_iff hQ0]
    simp [Q]
  have heval2 : (radical Q.primPart).eval (C 2) ≠ 0 := by
    rw [ne_eq, eval_radical_primPart_eq_zero_iff hQ0]
    intro h0
    have hval : ((0 : ZMod 5) + 1) * (2 - 0) ^ 2 * (2 - 1) = 0 := by
      simpa [Q] using congrArg (fun p : (ZMod 5)[X] => p.eval 0) h0
    exact absurd hval (by decide)
  obtain ⟨c, fs, hc0, hfs, hQeq, hdeg_sum⟩ := exists_eq_C_mul_prod_irreducible hQ0
  have hfs_ne : ∀ R ∈ fs, R ≠ 0 := fun R hR => (hfs R hR).1.ne_zero
  have hwd_fs := (sum_weightedDegree_le_of_eq_C_mul_prod (d := 1) hc0 hfs_ne hQeq).2
  have hdegQ : Q.natDegree = 3 := by
    have hmon1 : ((Y - C (X : (ZMod 5)[X])) ^ 2).Monic := (monic_X_sub_C X).pow 2
    have hmon2 : (Y - C (1 : (ZMod 5)[X])).Monic := monic_X_sub_C 1
    have hdeg_prod : (((Y - C (X : (ZMod 5)[X])) ^ 2) * (Y - C 1)).natDegree = 3 := by
      rw [hmon1.natDegree_mul hmon2, (monic_X_sub_C X).natDegree_pow, natDegree_X_sub_C,
        natDegree_X_sub_C]
    have hQassoc : Q = C (X + 1) * ((Y - C X) ^ 2 * (Y - C 1)) := by simp [Q, mul_assoc]
    rw [hQassoc, natDegree_C_mul hX1_ne, hdeg_prod]
  refine ⟨hwQ, hex_pow, isPrimitive_radical_primPart Q, squarefree_radical_primPart Q,
    hevalX, heval1, heval2, c, fs, hc0, fun R hR => ?_, hQeq, hdeg_sum.trans hdegQ⟩
  exact ⟨(hfs R hR).1, (hfs R hR).2.1, (hfs R hR).2.2,
    Polynomial.Bivariate.weightedDegree_le_iff.1 ((hwd_fs R hR).trans hwQ.le)⟩

/-- Least-`Y`-degree root multiplicity bound (`≤ m`) on an elimination interpolant, non-vacuous
`k = 1` list-size bound `≤ D`, `Sudan.add_mul_add_one_le_of_mul` (retaining `S = 0`), and zero
handling of `interpolant` when no nonzero solution exists (`D = 0`). -/
example :
    (interpolant points7 word7 5 2 19).rootMultiplicity 0 ≤ 5 ∧
    #(guruswamiSudan points7 word7 2 1 5) ≤ 5 ∧
    (∀ a b, ((0 : (ZMod 5)[X][Y]).coeff b).coeff a ≠ 0 → a + 1 * (b + 1) ≤ 0) ∧
    VanishesToOrder 1 (points7 0) (word7 0) (interpolant points7 word7 1 1 0) ∧
    interpolant points7 word7 1 1 0 = 0 := by
  have hcard5 : Fintype.card (Fin 7) * (5 * (5 + 1) / 2) < #(Sudan.monomials 2 19) := by decide
  have hQ := isInterpolant_interpolant points7 word7 (by omega) hcard5
  have hmin : ∀ Q', IsInterpolant points7 word7 5 2 19 Q' →
      (interpolant points7 word7 5 2 19).natDegree ≤ Q'.natDegree :=
    fun _ hQ' => natDegree_weightedInterpolant_le points7 word7 (by omega) hQ'
  have hS0 : ∀ a b, ((0 : (ZMod 5)[X][Y]).coeff b).coeff a ≠ 0 → a + 1 * (b + 1) ≤ 0 :=
    Sudan.add_mul_add_one_le_of_mul (P := (X : (ZMod 5)[X])) (by simp)
      (by simp)
  have hvan0 : VanishesToOrder 1 (points7 0) (word7 0) (interpolant points7 word7 1 1 0) :=
    vanishesToOrder_weightedInterpolant points7 word7 (fun _ => 1) 1 0 0
  have hzero0 : interpolant points7 word7 1 1 0 = 0 := by
    have hdeg0 : (interpolant points7 word7 1 1 0).natDegree = 0 :=
      Nat.eq_zero_of_le_zero (natDegree_weightedInterpolant_le_bound _ _ _ _ _)
    have hwd0 : Sudan.WeightedDegreeLE 1 0 (interpolant points7 word7 1 1 0) :=
      weightedDegreeLE_weightedInterpolant _ _ _ _ _
    ext b a
    rw [coeff_zero, coeff_zero]
    by_cases hba : a = 0 ∧ b = 0
    · obtain ⟨rfl, rfl⟩ := hba
      have h00 := hvan0 0 0 (by omega)
      rw [coeff_coeff_shift_zero] at h00
      have ha0 : ((interpolant points7 word7 1 1 0).coeff 0).natDegree = 0 := by
        refine Nat.eq_zero_of_le_zero (natDegree_le_iff_coeff_eq_zero.2 fun k hk => ?_)
        by_contra hne
        have := hwd0 k 0 hne
        omega
      have hconst : (interpolant points7 word7 1 1 0).evalEval (points7 0) (word7 0) =
          ((interpolant points7 word7 1 1 0).coeff 0).coeff 0 := by
        conv_lhs =>
          rw [eq_C_of_natDegree_eq_zero hdeg0, evalEval_C, eq_C_of_natDegree_eq_zero ha0, eval_C]
      exact hconst.symm.trans h00
    · by_contra hne
      have := hwd0 a b hne
      omega
  exact ⟨hQ.rootMultiplicity_le_of_min hmin 0, card_guruswamiSudan_le, hS0, hvan0, hzero0⟩

end CslibFrontierTests.Foundations.Data.Code.GuruswamiSudan

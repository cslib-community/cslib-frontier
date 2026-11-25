/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.ParityAmplifier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ring-homomorphism transport and univariate `natDegree` bounds for parity factors

This module provides ring-homomorphism transport and univariate `natDegree` bounds for the
parity-amplifying series factors `Polynomial.parityFactor` and truncated coefficient sums
`Polynomial.sumCoeffsBelow` defined in `CslibFrontier.Foundations.Data.Polynomial.ParityAmplifier`.

When each input $L_i(T) \in R[T]$ is a univariate polynomial of `natDegree` at most $d$, the
$V^s$-coefficient of $\prod_{i \in I} B_i(L_i(T), V)$ in $R[T][V]$ has `natDegree` at most
$d (\#I + 2 s)$ (`Polynomial.natDegree_coeff_prod_parityFactor_le`), so every retained coefficient
for $s < \ell$ and their sum `sumCoeffsBelow ℓ` have `natDegree` at most $d (\#I + 2 (\ell - 1))$
(`Polynomial.natDegree_coeff_prod_parityFactor_le_of_lt`,
`Polynomial.natDegree_sumCoeffsBelow_prod_parityFactor_le`), matching Lemma 5.2 and equation (5.5)
of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH].

## Main results

* `Polynomial.map_evalInt`, `Polynomial.map_parityFactor`, `Polynomial.map_sumCoeffsBelow`:
  ring-homomorphism transport for `evalInt`, `parityFactor`, and `sumCoeffsBelow`.
* `Polynomial.eval_coeff_prod_parityFactor`, `Polynomial.eval_sumCoeffsBelow_prod_parityFactor`:
  pointwise evaluation of coefficients and truncated sums of products of univariate parity factors.
* `Polynomial.natDegree_evalInt_le`, `Polynomial.natDegree_coeff_parityFactor_le`:
  univariate `natDegree` bounds for `evalInt` and single parity-factor coefficients.
* `Polynomial.natDegree_coeff_prod_parityFactor_le`,
  `Polynomial.natDegree_coeff_prod_parityFactor_le_of_lt`,
  `Polynomial.natDegree_sumCoeffsBelow_prod_parityFactor_le`: univariate `natDegree` bounds for
  products of parity factors and their truncated coefficient sums.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Lemma 5.2 and Section 5.3)
-/

public noncomputable section

namespace Polynomial

open Finset

variable {κ R : Type*}

/-- Any ring homomorphism `φ : A →+* B` commutes with `Polynomial.evalInt`. -/
theorem map_evalInt {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (y : A)
    (p : ℤ[X]) :
    φ (evalInt y p) = evalInt (φ y) p := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [evalInt, eval₂_add, map_add] at ihp ihq ⊢
    rw [ihp, ihq]
  | monomial n a =>
    simp only [evalInt, eval₂_monomial, map_mul, map_pow, eq_intCast, map_intCast]

/-- Mapping `parityFactor ℓ y` coefficientwise by `φ : A →+* B` yields `parityFactor ℓ (φ y)`. -/
theorem map_parityFactor {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (ℓ : ℕ) (y : A) :
    (parityFactor ℓ y).map φ = parityFactor ℓ (φ y) := by
  ext s
  rw [coeff_map, coeff_parityFactor, coeff_parityFactor]
  split_ifs with hs
  · rw [map_mul, map_pow, map_evalInt, map_evalInt]
  · exact map_zero φ

/-- Any ring homomorphism `φ : A →+* B` commutes with `sumCoeffsBelow`. -/
theorem map_sumCoeffsBelow {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    (P : A[X]) (m : ℕ) :
    φ (P.sumCoeffsBelow m) = (P.map φ).sumCoeffsBelow m := by
  simp only [sumCoeffsBelow, map_sum, coeff_map]

/-- Evaluating the `s`-th coefficient of `∏ i ∈ I, parityFactor ℓ (L i)` at `t : R` agrees with
the `s`-th coefficient of `∏ i ∈ I, parityFactor ℓ ((L i).eval t)`. -/
theorem eval_coeff_prod_parityFactor [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → R[X]) (s : ℕ) (t : R) :
    ((∏ i ∈ I, parityFactor ℓ (L i)).coeff s).eval t =
      (∏ i ∈ I, parityFactor ℓ ((L i).eval t)).coeff s := by
  change evalRingHom t ((∏ i ∈ I, parityFactor ℓ (L i)).coeff s) = _
  rw [← coeff_map, Polynomial.map_prod]
  exact congrArg (fun Q : R[X] => Q.coeff s) (prod_congr rfl fun i _ => map_parityFactor _ ℓ _)

/-- Evaluating `sumCoeffsBelow m` of `∏ i ∈ I, parityFactor ℓ (L i)` at `t : R` agrees with
`sumCoeffsBelow m` of `∏ i ∈ I, parityFactor ℓ ((L i).eval t)`. -/
theorem eval_sumCoeffsBelow_prod_parityFactor [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → R[X]) (m : ℕ) (t : R) :
    ((∏ i ∈ I, parityFactor ℓ (L i)).sumCoeffsBelow m).eval t =
      (∏ i ∈ I, parityFactor ℓ ((L i).eval t)).sumCoeffsBelow m := by
  rw [sumCoeffsBelow, eval_finsetSum, sumCoeffsBelow]
  exact sum_congr rfl fun s _ => eval_coeff_prod_parityFactor I ℓ L s t

/-- For `y : R[X]` and `p : ℤ[X]`, `(evalInt y p).natDegree ≤ p.natDegree * y.natDegree`. -/
theorem natDegree_evalInt_le [CommRing R] (y : R[X]) (p : ℤ[X]) :
    (evalInt y p).natDegree ≤ p.natDegree * y.natDegree := by
  rw [evalInt, eval₂_eq_sum_range]
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  dsimp only [Function.comp_apply]
  rw [eq_intCast, ← C_eq_intCast]
  calc (C (p.coeff i : R) * y ^ i).natDegree
      ≤ i * y.natDegree := (natDegree_C_mul_le _ _).trans natDegree_pow_le
    _ ≤ p.natDegree * y.natDegree :=
        Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp (mem_range.mp hi))

/-- `evalInt y (parityBaseDigit ℓ j)` has `natDegree ≤ y.natDegree`. -/
theorem natDegree_evalInt_parityBaseDigit_le [CommRing R] (ℓ j : ℕ) (y : R[X]) :
    (evalInt y (parityBaseDigit ℓ j)).natDegree ≤ y.natDegree := by
  calc
    (evalInt y (parityBaseDigit ℓ j)).natDegree
      ≤ (parityBaseDigit ℓ j).natDegree * y.natDegree := natDegree_evalInt_le y _
    _ ≤ 1 * y.natDegree := Nat.mul_le_mul_right _ (natDegree_parityBaseDigit_le ℓ j)
    _ = y.natDegree := one_mul _

/-- `evalInt y hPoly` has `natDegree ≤ 2 * y.natDegree`. -/
theorem natDegree_evalInt_hPoly_le [CommRing R] (y : R[X]) :
    (evalInt y hPoly).natDegree ≤ 2 * y.natDegree := by
  rw [evalInt_hPoly]
  calc
    (y ^ 2 - y).natDegree
      ≤ max (y ^ 2).natDegree y.natDegree := natDegree_sub_le _ _
    _ ≤ max (2 * y.natDegree) y.natDegree := max_le_max natDegree_pow_le le_rfl
    _ = 2 * y.natDegree := max_eq_left (by omega)

/-- The `j`-th coefficient of `parityFactor ℓ y` has `natDegree ≤ (1 + 2 * j) * y.natDegree`. -/
theorem natDegree_coeff_parityFactor_le [CommRing R] (ℓ : ℕ) (y : R[X]) (j : ℕ) :
    ((parityFactor ℓ y).coeff j).natDegree ≤ (1 + 2 * j) * y.natDegree := by
  rw [coeff_parityFactor]
  split_ifs with hj
  · calc
      (evalInt y (parityBaseDigit ℓ j) * evalInt y hPoly ^ j).natDegree
        ≤ (evalInt y (parityBaseDigit ℓ j)).natDegree +
            (evalInt y hPoly ^ j).natDegree := natDegree_mul_le
      _ ≤ y.natDegree + j * (evalInt y hPoly).natDegree :=
          add_le_add (natDegree_evalInt_parityBaseDigit_le ℓ j y) natDegree_pow_le
      _ ≤ y.natDegree + j * (2 * y.natDegree) :=
          add_le_add le_rfl (Nat.mul_le_mul_left j (natDegree_evalInt_hPoly_le y))
      _ = (1 + 2 * j) * y.natDegree := by ring
  · simp only [natDegree_zero, zero_le]

/-- If every `L i` (`i ∈ I`) has `natDegree ≤ d`, then the `V ^ s`-coefficient of
`∏ i ∈ I, parityFactor ℓ (L i)` has `natDegree ≤ d * (#I + 2 * s)`. -/
theorem natDegree_coeff_prod_parityFactor_le [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → R[X]) {d : ℕ} (hL : ∀ i ∈ I, (L i).natDegree ≤ d) :
    ∀ s : ℕ, ((∏ i ∈ I, parityFactor ℓ (L i)).coeff s).natDegree ≤ d * (#I + 2 * s) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro s
    by_cases hs : s = 0 <;> simp [coeff_one, hs]
  | insert a I ha ih =>
    intro s
    rw [prod_insert ha, card_insert_of_notMem ha, coeff_mul]
    refine (natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun p hp => ?_⟩
    calc (((parityFactor ℓ (L a)).coeff p.1) *
          ((∏ i ∈ I, parityFactor ℓ (L i)).coeff p.2)).natDegree
        ≤ (1 + 2 * p.1) * (L a).natDegree + d * (#I + 2 * p.2) :=
          natDegree_mul_le.trans (add_le_add (natDegree_coeff_parityFactor_le ℓ (L a) p.1)
            (ih (fun i hi => hL i (mem_insert_of_mem hi)) p.2))
      _ ≤ (1 + 2 * p.1) * d + d * (#I + 2 * p.2) :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (hL a (mem_insert_self a I))) _
      _ = d * (#I + 1 + 2 * s) := by rw [← mem_antidiagonal.mp hp]; ring

/-- For `s < ℓ`, the `V ^ s`-coefficient of `∏ i ∈ I, parityFactor ℓ (L i)` has
`natDegree ≤ d * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_coeff_prod_parityFactor_le_of_lt [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → R[X]) {d : ℕ} (hL : ∀ i ∈ I, (L i).natDegree ≤ d) {s : ℕ} (hs : s < ℓ) :
    ((∏ i ∈ I, parityFactor ℓ (L i)).coeff s).natDegree ≤
      d * (#I + 2 * (ℓ - 1)) :=
  (natDegree_coeff_prod_parityFactor_le I ℓ L hL s).trans (Nat.mul_le_mul_left d (by omega))

/-- The truncated sum `sumCoeffsBelow ℓ (∏ i ∈ I, parityFactor ℓ (L i))` has
`natDegree ≤ d * (#I + 2 * (ℓ - 1))`. -/
theorem natDegree_sumCoeffsBelow_prod_parityFactor_le [CommRing R] (I : Finset κ) (ℓ : ℕ)
    (L : κ → R[X]) {d : ℕ} (hL : ∀ i ∈ I, (L i).natDegree ≤ d) :
    ((∏ i ∈ I, parityFactor ℓ (L i)).sumCoeffsBelow ℓ).natDegree ≤
      d * (#I + 2 * (ℓ - 1)) := by
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  exact ⟨Nat.zero_le _, fun _ hs =>
    natDegree_coeff_prod_parityFactor_le_of_lt I ℓ L hL (mem_range.mp hs)⟩

end Polynomial

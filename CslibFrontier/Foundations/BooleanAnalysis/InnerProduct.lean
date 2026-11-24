/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct
import CslibFrontier.Foundations.Data.BitString.Sign.BigOperators
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.ExpectPi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-!
# The Fourier spectrum of the inner product modulo two

The sign of the inner product of two `n`-bit strings has every Fourier coefficient equal to
`±2⁻ⁿ`: it is a bent function. Here the two strings are the two halves of one `2n`-bit input,
using `BitString.fstBits`, `BitString.sndBits`, and the Boolean-ring inner product `⬝ᵥ`.
The sign of the coefficient at a Fourier mask is the inner product of the mask's two halves.

Plancherel's identity then bounds correlation with an arbitrary real function `g` by `2⁻ⁿ` times
the spectral norm of `g`. Keeping the products on a set `S` of coordinate pairs gives correlation
exactly `2 ^ |S| / 2 ^ n` with the full inner product. In particular, this includes the empty set
and all coordinate pairs. The formulas are proved directly in the library's existing Fourier
normalization.

## Main results

* `Cslib.BitString.fourierCoeff_signVal_dotProduct_fstBits_sndBits`: the exact spectrum.
* `Cslib.BitString.abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits`: flatness of the spectrum.
* `Cslib.BitString.abs_expect_signVal_dotProduct_mul_le`: correlation is bounded by the spectral
  norm divided by `2 ^ n`.
* `Cslib.BitString.expect_signVal_dotProduct_mul_signVal_sum`: the exact correlation obtained by
  keeping an arbitrary set of coordinate pairs.

-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

private theorem expect_append {a b : ℕ} (f : BitString (a + b) → ℝ) :
    (𝔼 z, f z) = 𝔼 x : BitString a, 𝔼 y : BitString b, f (Fin.append x y) := by
  rw [← Fintype.expect_prod_type (fun p : BitString a × BitString b =>
    f (Fin.append p.1 p.2))]
  exact (Fintype.expect_equiv (Fin.appendEquiv a b) _ f fun _ => rfl).symm

private theorem expect_prod_bools {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Bool → Bool → ℝ) :
    (𝔼 x : ι → Bool, 𝔼 y : ι → Bool, ∏ i, f i (x i) (y i)) =
      ∏ i, 𝔼 a, 𝔼 b, f i a b := by
  simp_rw [← Fintype.prod_expect]
  exact (Fintype.prod_expect (fun i a => 𝔼 b, f i a b)).symm

private theorem expect_dotProduct_affineSigns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → Bool) :
    (𝔼 x : ι → Bool, 𝔼 y : ι → Bool,
      signVal (x ⬝ᵥ y) * signVal (a ⬝ᵥ x) * signVal (b ⬝ᵥ y)) =
      signVal (a ⬝ᵥ b) / (2 : ℝ) ^ Fintype.card ι := by
  simp only [dotProduct, signVal_sum, ← prod_mul_distrib]
  rw [expect_prod_bools (fun i x y =>
    signVal (x * y) * signVal (a i * x) * signVal (b i * y))]
  have h (i : ι) :
      (𝔼 x : Bool, 𝔼 y : Bool,
        signVal (x * y) * signVal (a i * x) * signVal (b i * y)) =
        signVal (a i * b i) / 2 := by
    simp only [Fintype.expect_bool]
    cases a i <;> cases b i <;> norm_num [Bool.mul_eq_and]
  simp only [h, prod_div_distrib, prod_const, card_univ]

private theorem chi_eq_signVal_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (x : ι → Bool) :
    chi ℝ S x = signVal ((fun i => decide (i ∈ S)) ⬝ᵥ x) := by
  rw [dotProduct_comm, dotProduct_eq_parityOn]
  simp [chi_eq_signVal_parityOn]

variable {n : ℕ}

/-- The Fourier coefficient of the sign of the inner product is `2⁻ⁿ`, with sign given by the
inner product of the Fourier mask's two halves. -/
theorem fourierCoeff_signVal_dotProduct_fstBits_sndBits (S : Finset (Fin (n + n))) :
    fourierCoeff (fun z : BitString (n + n) => signVal (fstBits z ⬝ᵥ sndBits z)) S =
      signVal ((fun i : Fin n => decide (Fin.castAdd n i ∈ S)) ⬝ᵥ
        (fun i : Fin n => decide (Fin.natAdd n i ∈ S))) / (2 : ℝ) ^ n := by
  have hchi (x y : BitString n) :
      chi ℝ S (Fin.append x y) =
        signVal ((fun i : Fin n => decide (Fin.castAdd n i ∈ S)) ⬝ᵥ x) *
          signVal ((fun i : Fin n => decide (Fin.natAdd n i ∈ S)) ⬝ᵥ y) := by
    rw [chi_eq_signVal_dotProduct, dotProduct, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Bool.add_eq_xor, signVal_xor, dotProduct]
  rw [fourierCoeff, expect_append]
  simp only [fstBits_append, sndBits_append, hchi, ← mul_assoc]
  simpa only [Fintype.card_fin] using expect_dotProduct_affineSigns
    (fun i : Fin n => decide (Fin.castAdd n i ∈ S))
    (fun i : Fin n => decide (Fin.natAdd n i ∈ S))

/-- All Fourier coefficients of the sign of the `n`-pair inner product have magnitude `2⁻ⁿ`.
The case `n = 0` is included. -/
theorem abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits (S : Finset (Fin (n + n))) :
    |fourierCoeff (fun z : BitString (n + n) => signVal (fstBits z ⬝ᵥ sndBits z)) S| =
      1 / (2 : ℝ) ^ n := by
  rw [fourierCoeff_signVal_dotProduct_fstBits_sndBits, abs_div, abs_signVal,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]

/-- Correlation with the inner product is at most the spectral norm divided by `2 ^ n`.
This applies to arbitrary real functions, with no boundedness assumption. -/
theorem abs_expect_signVal_dotProduct_mul_le (g : BitString (n + n) → ℝ) :
    |𝔼 z, signVal (fstBits z ⬝ᵥ sndBits z) * g z| ≤
      (∑ S, |fourierCoeff g S|) / (2 : ℝ) ^ n := by
  rw [expect_mul_eq_sum_fourierCoeff_mul]
  calc
    _ ≤ ∑ S, |fourierCoeff (fun z : BitString (n + n) =>
        signVal (fstBits z ⬝ᵥ sndBits z)) S * fourierCoeff g S| := abs_sum_le_sum_abs _ _
    _ = _ := by
      simp only [abs_mul, abs_fourierCoeff_signVal_dotProduct_fstBits_sndBits,
        div_eq_mul_inv, one_mul, ← mul_sum, mul_comm]

/-- Keeping the products on `S` gives correlation exactly `2 ^ |S| / 2 ^ n` with the full
inner product. In particular, retaining no pairs gives `2⁻ⁿ` and retaining every pair gives one. -/
theorem expect_signVal_dotProduct_mul_signVal_sum (S : Finset (Fin n)) :
    (𝔼 z : BitString (n + n), signVal (fstBits z ⬝ᵥ sndBits z) *
      signVal (∑ i ∈ S, fstBits z i * sndBits z i)) = (2 : ℝ) ^ S.card / 2 ^ n := by
  rw [expect_append]
  simp only [fstBits_append, sndBits_append]
  have hsum (x y : BitString n) :
      (∑ i ∈ S, x i * y i) = ∑ i, if i ∈ S then x i * y i else 0 := by simp
  simp only [hsum, dotProduct, signVal_sum, ← prod_mul_distrib]
  rw [expect_prod_bools (fun i x y =>
    signVal (x * y) * signVal (if i ∈ S then x * y else 0))]
  have h (i : Fin n) :
      (𝔼 x : Bool, 𝔼 y : Bool,
        signVal (x * y) * signVal (if i ∈ S then x * y else 0)) =
        (if i ∈ S then 2 else 1 : ℝ) / 2 := by
    by_cases hi : i ∈ S
    · simp [hi, signVal_mul_self]
    · simp only [Fintype.expect_bool]
      norm_num [hi, Bool.mul_eq_and, signVal]
  simp only [h, prod_div_distrib, prod_ite_mem_eq, prod_const, card_univ, Fintype.card_fin]

end Cslib.BitString

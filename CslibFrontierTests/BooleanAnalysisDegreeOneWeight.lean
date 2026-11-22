/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.DegreeOneWeight
public import CslibFrontier.Foundations.Data.BitString.Threshold
import CslibFrontier.Foundations.BooleanAnalysis.LongCode

/-! # Literals, the parity of two bits, and the extremes of noise stability

The negated dictator `x ↦ ¬x₁` on three bits is a literal: its only nonzero Fourier coefficient is
`-1`, on `{1}`. So it is unbiased, has degree-one weight one, no Fourier weight on `{0, 2}`, and
noise stability `ρ` at every rate. At `ρ = 1/2` it attains Proposition 2.50's bound, and at
`ρ = -1/3` the value `Stab_{-1/3} = -1/3` makes the book's Condorcet formula
`3/4 - 3/4 Stab_{-1/3}` equal to one. The parity of two bits is unbiased but not a literal: its
coefficient on `{0, 1}` is one, so its degree-one weight is not one, and `Stab_ρ = ρ ^ 2`.
Proposition 2.50 bounds its noise stability at `ρ = 1/2` by `1/2`, strictly, and also at the
endpoints `ρ = 0` and `ρ = 1`; at `ρ = -1/3` it is strictly above the rate, and the lower bound
also holds at `ρ = -1`. The majority of three bits is odd, so it has `Stab_{-1} = -1` without
being a literal: the equality case at negative rates needs `-1 < ρ`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisDegreeOneWeight

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-! ### A negated dictator -/

/-- The negated dictator `x ↦ ¬x₁` on three bits. -/
def antiDict (x : Fin 3 → Bool) : Bool :=
  !x 1

/-- The negated dictator is the literal `x ↦ true ⊕ x₁`. -/
theorem antiDict_eq_xor : antiDict = fun x => true ^^ x 1 := by
  funext x
  simp [antiDict]

/-- The Fourier coefficients of the negated dictator: `-1` on `{1}` and `0` elsewhere. -/
theorem fourierCoeff_antiDict (S : Finset (Fin 3)) :
    fourierCoeff (fun x => signVal (antiDict x)) S = if {1} = S then -1 else 0 := by
  rw [antiDict_eq_xor, fourierCoeff_signVal_xor, signVal_true]

/-- The negated dictator is unbiased. -/
theorem expect_signVal_antiDict : 𝔼 x, signVal (antiDict x) = 0 := by
  rw [← fourierCoeff_empty, fourierCoeff_antiDict]
  simp

/-- The negated dictator has degree-one weight one, by Exercise 1.19(a)'s converse. -/
theorem levelWeight_one_antiDict : levelWeight 1 (fun x => signVal (antiDict x)) = 1 :=
  (levelWeight_one_signVal_eq_one_iff antiDict).2 ⟨1, true, antiDict_eq_xor⟩

-- Exercise 1.19(a), forward direction: degree-one weight one recovers a literal.
example : ∃ (i : Fin 3) (b : Bool), antiDict = fun x => b ^^ x i :=
  (levelWeight_one_signVal_eq_one_iff antiDict).1 levelWeight_one_antiDict

-- With degree-one weight one, the coefficient on the two-element set `{0, 2}` vanishes.
example : fourierCoeff (fun x => signVal (antiDict x)) {0, 2} = 0 :=
  (levelWeight_signVal_eq_one_iff_fourierCoeff_eq_zero 1 antiDict).1 levelWeight_one_antiDict
    {0, 2} (by decide)

/-- The negated dictator has noise stability `-1/3` at `ρ = -1/3`. -/
theorem noiseStability_antiDict :
    noiseStability (-1 / 3) (fun x => signVal (antiDict x)) = -1 / 3 :=
  noiseStability_signVal_eq_of_levelWeight_one_eq_one levelWeight_one_antiDict (-1 / 3)

-- So the Condorcet formula `3/4 - 3/4 Stab_{-1/3}` of Theorem 2.56 is one.
example : 3 / 4 - 3 / 4 * noiseStability (-1 / 3) (fun x => signVal (antiDict x)) = 1 := by
  rw [noiseStability_antiDict]
  norm_num

-- Proposition 2.50's equality case, from the literal: at `ρ = 1/2` the bound is attained.
example : noiseStability (1 / 2) (fun x => signVal (antiDict x)) = 1 / 2 :=
  (noiseStability_signVal_eq_iff_of_expect_eq_zero (by norm_num) (by norm_num)
    expect_signVal_antiDict).2 ⟨1, true, antiDict_eq_xor⟩

-- The negative-rate equality, from the literal.
example : noiseStability (-1 / 3) (fun x => signVal (antiDict x)) = -1 / 3 :=
  (noiseStability_signVal_eq_iff_of_neg (by norm_num) (by norm_num) antiDict).2
    ⟨1, true, antiDict_eq_xor⟩

/-! ### The parity of two bits -/

/-- The parity of two bits. -/
def par₂ (x : Fin 2 → Bool) : Bool :=
  parityOn ({0, 1} : Finset (Fin 2)) x

/-- The parity of two bits, read as signs, has Fourier coefficient one on `{0, 1}` and zero
elsewhere. -/
theorem fourierCoeff_par₂ (S : Finset (Fin 2)) :
    fourierCoeff (fun x => signVal (par₂ x)) S = if S = {0, 1} then 1 else 0 :=
  fourierCoeff_signVal_parityOn _ S

/-- The parity of two bits is unbiased. -/
theorem expect_signVal_par₂ : 𝔼 x, signVal (par₂ x) = 0 := by
  rw [← fourierCoeff_empty, fourierCoeff_par₂]
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  decide

/-- The parity of two bits is not a literal. -/
theorem not_exists_par₂_eq_xor : ¬ ∃ (i : Fin 2) (b : Bool), par₂ = fun x => b ^^ x i := by
  rintro ⟨i, b, h⟩
  have h₀ := congrFun h 0
  have h₁ := congrFun h fun _ => true
  revert h₀ h₁
  revert i b
  decide

-- Its coefficient on `{0, 1}` is one, so its degree-one weight is not one.
example : levelWeight 1 (fun x => signVal (par₂ x)) ≠ 1 := fun h => by
  have h01 := (levelWeight_signVal_eq_one_iff_fourierCoeff_eq_zero 1 par₂).1 h {0, 1}
    (by decide)
  rw [fourierCoeff_par₂, ite_eq_left rfl] at h01
  exact one_ne_zero h01

-- Equivalently, it is not a literal.
example : levelWeight 1 (fun x => signVal (par₂ x)) ≠ 1 := fun h =>
  not_exists_par₂_eq_xor ((levelWeight_one_signVal_eq_one_iff par₂).1 h)

/-- The parity of two bits has noise stability `ρ ^ 2`. -/
theorem noiseStability_par₂ (ρ : ℝ) : noiseStability ρ (fun x => signVal (par₂ x)) = ρ ^ 2 := by
  rw [noiseStability_eq_sum]
  simp only [fourierCoeff_par₂, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte]
  rfl

-- Proposition 2.50 at `ρ = 1/2`: the parity is at most as noise-stable as a dictator.
example : noiseStability (1 / 2) (fun x => signVal (par₂ x)) ≤ 1 / 2 :=
  noiseStability_signVal_le_of_expect_eq_zero (by norm_num) (by norm_num) expect_signVal_par₂

-- Strictly so, since it is not a literal; its stability is in fact `1 / 4`.
example : noiseStability (1 / 2) (fun x => signVal (par₂ x)) ≠ 1 / 2 := fun h =>
  not_exists_par₂_eq_xor ((noiseStability_signVal_eq_iff_of_expect_eq_zero (by norm_num)
    (by norm_num) expect_signVal_par₂).1 h)

example : noiseStability (1 / 2) (fun x => signVal (par₂ x)) = 1 / 4 := by
  rw [noiseStability_par₂]
  norm_num

-- The bound at the endpoints `ρ = 0` and `ρ = 1`, where it is attained by every unbiased `f` and
-- every `f` respectively, so the equality case needs the open interval.
example : noiseStability 0 (fun x => signVal (par₂ x)) ≤ 0 :=
  noiseStability_signVal_le_of_expect_eq_zero le_rfl zero_le_one expect_signVal_par₂

example : noiseStability 1 (fun x => signVal (par₂ x)) ≤ 1 :=
  noiseStability_signVal_le_of_expect_eq_zero zero_le_one le_rfl expect_signVal_par₂

-- At `ρ = -1/3` the parity is at least as noise-stable as the rate, and strictly so.
example : -1 / 3 ≤ noiseStability (-1 / 3) (fun x => signVal (par₂ x)) :=
  le_noiseStability_signVal_of_nonpos (by norm_num) (by norm_num) par₂

example : noiseStability (-1 / 3) (fun x => signVal (par₂ x)) ≠ -1 / 3 := fun h =>
  not_exists_par₂_eq_xor ((noiseStability_signVal_eq_iff_of_neg (by norm_num) (by norm_num)
    par₂).1 h)

-- The lower bound at the endpoint `ρ = -1`.
example : -1 ≤ noiseStability (-1) (fun x => signVal (par₂ x)) :=
  le_noiseStability_signVal_of_nonpos le_rfl (by norm_num) par₂

/-! ### The majority of three bits at `ρ = -1` -/

/-- The majority of three bits has noise stability `-1` at `ρ = -1`: it is odd, so it has Fourier
weight only on sets of odd size. -/
theorem noiseStability_neg_one_majority_three :
    noiseStability (-1) (fun x => signVal (majority 3 x)) = -1 := by
  have hodd : IsOdd (majority 3) := by
    intro f
    revert f
    decide
  rw [noiseStability_eq_sum]
  conv_rhs => rw [← sum_fourierCoeff_sq_signVal (majority 3), ← sum_neg_distrib]
  refine sum_congr rfl fun S _ => ?_
  rcases Nat.even_or_odd #S with he | ho
  · rw [hodd.fourierCoeff_of_even he]
    ring
  · rw [ho.neg_one_pow]
    ring

/-- The majority of three bits is not a literal. -/
theorem not_exists_majority_three_eq_xor :
    ¬ ∃ (i : Fin 3) (b : Bool), majority 3 = fun x => b ^^ x i := by
  rintro ⟨i, b, h⟩
  have h₀ := congrFun h 0
  have h₁ := congrFun h ![true, false, false]
  have h₂ := congrFun h ![false, true, false]
  revert h₀ h₁ h₂
  revert i b
  decide

-- So the equality case of the negative-rate bound fails at `ρ = -1`.
example : ¬ (noiseStability (-1) (fun x => signVal (majority 3 x)) = -1 ↔
    ∃ (i : Fin 3) (b : Bool), majority 3 = fun x => b ^^ x i) := fun h =>
  not_exists_majority_three_eq_xor (h.1 noiseStability_neg_one_majority_three)

end CslibFrontierTests.BooleanAnalysisDegreeOneWeight

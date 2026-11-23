/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.DerandomizedBLR
public import CslibFrontier.Probability.SmallBias.Powering
import CslibFrontier.Foundations.BooleanAnalysis.Affinity

/-! # Tests for the derandomized BLR test

With the uniform distribution, which is `0`-biased, the derandomized test is the BLR test and
Theorem 6.44 gives a coefficient `|F̂(S)| ≥ θ` and an affine function within `1/2 - θ/2`. Parities
pass with probability one under the powering small-bias space on a thousand bits, and Remark 6.45
applies there with `ε = 999 / 2 ^ 20`. The constant `true` and the negated parities, which are
affine, are always rejected, the first through the convolution formula; at the negative
`θ = -1` Theorem 6.44 still finds a large coefficient of a negated parity. A point mass is only
`1`-biased, and it accepts every function with `f 0 = false`, such as a conjunction that is far
from every affine function; so the bias hypothesis cannot be dropped, and Theorem 6.44 shows that
the point mass is not `ε`-biased for `ε < 3/4`. The shared lemmas of the affinity test are checked
on parities and on the conjunction. -/

public section

namespace CslibFrontierTests.BooleanAnalysisDerandomizedBLR

open Cslib Cslib.BitString Cslib.Probability Finset
open scoped BigOperators

/-- The BLR acceptance condition in signs, at `(true ^^ false) = true`. -/
theorem ite_xor_eq_eq_signVal_true_false_true :
    (if (true ^^ false) = true then (1 : ℝ) else 0) =
      1 / 2 + 1 / 2 * (signVal true * (signVal false * signVal true)) :=
  ite_xor_eq_eq_signVal true false true

/-- The constant `true` is always rejected: reading it as the signs `F = -1`, the convolution
`F ∗ F` is `1`, and the acceptance probability is `1/2 + 1/2 ∑_y X(y) (-1) = 0`. -/
theorem derandomizedBLRAcceptance_true (X : PMF (Fin 3 → Bool)) :
    derandomizedBLRAcceptance X (fun _ => true) = 0 := by
  rw [derandomizedBLRAcceptance_eq_sum_mul_convolution]
  simp only [convolution, signVal_true, mul_neg, mul_one, neg_neg, Fintype.expect_const,
    sum_neg_distrib, Probability.PMF.sum_toReal]
  norm_num

/-- The dictator `x ↦ x 0` is linear, so it passes with probability one for every
distribution. -/
theorem derandomizedBLRAcceptance_dictator (X : PMF (Fin 3 → Bool)) :
    derandomizedBLRAcceptance X (fun x => x 0) = 1 :=
  derandomizedBLRAcceptance_of_map_add X fun _ _ => rfl

/-- With the uniform distribution, acceptance `1/2 + θ/2` gives `θ ≤ |F̂(S)|`. -/
theorem exists_le_abs_fourierCoeff_of_le_blrAcceptance {f : (Fin 3 → Bool) → Bool} {θ : ℝ}
    (hθ : 0 ≤ θ) (h : 1 / 2 + 1 / 2 * θ ≤ blrAcceptance f) :
    ∃ S, θ ≤ |fourierCoeff (fun x => signVal (f x)) S| := by
  rw [← derandomizedBLRAcceptance_uniformOfFintype] at h
  obtain ⟨S, hS⟩ := exists_le_abs_fourierCoeff_of_le_derandomizedBLRAcceptance le_rfl
    isSmallBias_uniformOfFintype (by rw [abs_of_nonneg hθ]; exact le_abs.2 (Or.inl (by linarith)))
  rw [sub_zero, Real.sqrt_sq hθ] at hS
  exact ⟨S, hS⟩

/-- With the uniform distribution, acceptance `1/2 + θ/2` gives an affine function within
`1/2 - θ/2`. -/
theorem exists_hammingDist_le_of_le_blrAcceptance {f : (Fin 3 → Bool) → Bool} {θ : ℝ}
    (hθ : 0 ≤ θ) (h : 1 / 2 + 1 / 2 * θ ≤ blrAcceptance f) :
    ∃ b S, (hammingDist f (fun x => b ^^ parityOn S x) : ℝ) / 2 ^ 3 ≤ 1 / 2 - 1 / 2 * θ := by
  rw [← derandomizedBLRAcceptance_uniformOfFintype] at h
  obtain ⟨b, S, hS⟩ := exists_hammingDist_xor_parityOn_le_of_le_derandomizedBLRAcceptance le_rfl
    isSmallBias_uniformOfFintype
    (by rw [abs_of_nonneg hθ]; exact le_abs.2 (Or.inl (by linarith)))
  rw [sub_zero, Real.sqrt_sq hθ, Fintype.card_fin] at hS
  exact ⟨b, S, hS⟩

/-- A parity passes the BLR test, so under the uniform distribution the spectral form of
Theorem 6.44 gives a coefficient with `F̂(S)² ≥ 1`. -/
theorem exists_one_le_fourierCoeff_sq_parityOn (S : Finset (Fin 3)) :
    ∃ T, 1 ≤ fourierCoeff (fun x => signVal (parityOn S x)) T ^ 2 := by
  obtain ⟨T, hT⟩ := exists_two_mul_derandomizedBLRAcceptance_sub_one_sq_sub_le_fourierCoeff_sq
    le_rfl isSmallBias_uniformOfFintype (parityOn S)
  rw [derandomizedBLRAcceptance_parityOn] at hT
  exact ⟨T, by linarith⟩

/-- A parity passes with probability one, so under any `ε`-biased distribution the distance form
of Theorem 6.44 with `θ = 1` gives an affine function within `1/2 - 1/2 √(1 - ε)`. -/
theorem exists_hammingDist_le_parityOn {ε : ℝ} (hε : 0 ≤ ε) {X : PMF (Fin 3 → Bool)}
    (hX : IsSmallBias ε X) (S : Finset (Fin 3)) :
    ∃ b T, (hammingDist (parityOn S) (fun x => b ^^ parityOn T x) : ℝ) / 2 ^ 3 ≤
      1 / 2 - 1 / 2 * √(1 - ε) := by
  obtain ⟨b, T, hT⟩ := exists_hammingDist_xor_parityOn_le_of_le_derandomizedBLRAcceptance hε hX
    (θ := 1) (f := parityOn S) (by rw [derandomizedBLRAcceptance_parityOn]; norm_num)
  rw [one_pow, Fintype.card_fin] at hT
  exact ⟨b, T, hT⟩

/-- Parities pass with probability one under the powering small-bias space on a thousand bits. -/
theorem exists_derandomizedBLRAcceptance_parityOn_eq_one (S : Finset (Fin 1000)) :
    ∃ g : BitString (2 * 20) → BitString 1000,
      IsSmallBias ((1000 - 1 : ℕ) / 2 ^ 20 : ℝ) ((PMF.uniformOfFintype _).map g) ∧
        derandomizedBLRAcceptance ((PMF.uniformOfFintype _).map g) (parityOn S) = 1 := by
  obtain ⟨g, hg⟩ := exists_isSmallBias_uniformOfFintype_map 1000 (m := 20) (by norm_num)
  exact ⟨g, hg, derandomizedBLRAcceptance_parityOn _ S⟩

/-- Under that space, acceptance `9/10` puts `f` within `1/10 + ε / (8/5) < 101/1000` of an affine
function, using `40` random seed bits instead of the `1000` of the second BLR query. -/
theorem exists_hammingDist_lt_of_nine_div_ten_le (g : BitString (2 * 20) → BitString 1000)
    (hg : IsSmallBias ((1000 - 1 : ℕ) / 2 ^ 20 : ℝ) ((PMF.uniformOfFintype _).map g))
    {f : BitString 1000 → Bool}
    (h : 9 / 10 ≤ derandomizedBLRAcceptance ((PMF.uniformOfFintype _).map g) f) :
    ∃ b S, (hammingDist f (fun x => b ^^ parityOn S x) : ℝ) / 2 ^ Fintype.card (Fin 1000) <
      101 / 1000 := by
  obtain ⟨b, S, hS⟩ := exists_hammingDist_xor_parityOn_le_of_one_sub_le_derandomizedBLRAcceptance
    (δ := 1 / 10) (f := f) (by positivity) hg (by norm_num) (by linarith)
  exact ⟨b, S, hS.trans_lt (by norm_num)⟩

/-- Negated parities are affine but always rejected, whatever the distribution. -/
theorem derandomizedBLRAcceptance_not_parityOn (X : PMF (Fin 3 → Bool)) (S : Finset (Fin 3)) :
    derandomizedBLRAcceptance X (fun x => !parityOn S x) = 0 := by
  simp [derandomizedBLRAcceptance_def, parityOn_add]

/-- A negated parity is accepted with probability `0 = 1/2 + θ/2` for `θ = -1`, so under any
`ε`-biased distribution the correlation form of Theorem 6.44 at the negative `θ = -1` gives a
coefficient with `√(1 - ε) ≤ |F̂(T)|`. -/
theorem exists_sqrt_le_abs_fourierCoeff_not_parityOn {ε : ℝ} (hε : 0 ≤ ε)
    {X : PMF (Fin 3 → Bool)} (hX : IsSmallBias ε X) (S : Finset (Fin 3)) :
    ∃ T, √(1 - ε) ≤ |fourierCoeff (fun x => signVal (!parityOn S x)) T| := by
  obtain ⟨T, hT⟩ := exists_le_abs_fourierCoeff_of_le_derandomizedBLRAcceptance hε hX (θ := -1)
    (f := fun x => !parityOn S x) (by rw [derandomizedBLRAcceptance_not_parityOn]; norm_num)
  rw [neg_one_sq] at hT
  exact ⟨T, hT⟩

/-- The conjunction of the first two of three bits. -/
def conj (x : Fin 3 → Bool) : Bool := x 0 && x 1

/-- The point mass at `0`, which is `1`-biased, accepts the conjunction with probability one. -/
theorem derandomizedBLRAcceptance_pure_conj :
    derandomizedBLRAcceptance (PMF.pure 0) conj = 1 := by
  have h (x : Fin 3 → Bool) : ∑ y, ((PMF.pure 0 y).toReal *
      if (conj x ^^ conj y) = conj (x + y) then (1 : ℝ) else 0) = 1 := by
    rw [sum_eq_single 0 (fun y _ hy => by simp [PMF.pure_apply, hy]) (by simp)]
    simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one, one_mul, add_zero,
      show conj 0 = false from rfl, Bool.xor_false]
  simp only [derandomizedBLRAcceptance_def, h, Fintype.expect_const]

/-- Yet the conjunction is far from affine: every Fourier coefficient has `|F̂(S)| ≤ 1/2`. -/
theorem abs_fourierCoeff_conj_le (S : Finset (Fin 3)) :
    |fourierCoeff (fun x => signVal (conj x)) S| ≤ 1 / 2 := by
  have hd : ∀ S : Finset (Fin 3),
      2 ≤ hammingDist conj (parityOn S) ∧ hammingDist conj (parityOn S) ≤ 6 := by decide
  obtain ⟨h2, h6⟩ := hd S
  have h2' : (2 : ℝ) ≤ hammingDist conj (parityOn S) := by exact_mod_cast h2
  have h6' : (hammingDist conj (parityOn S) : ℝ) ≤ 6 := by exact_mod_cast h6
  rw [fourierCoeff_signVal, abs_le, Fintype.card_fin]
  constructor <;> linarith

/-- So Theorem 6.44 with `θ = 1` shows that the point mass at `0` is not `ε`-biased for
`ε < 3/4`. -/
theorem not_isSmallBias_pure {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 3 / 4) :
    ¬ IsSmallBias ε (PMF.pure (0 : Fin 3 → Bool)) := by
  intro hX
  obtain ⟨S, hS⟩ := exists_le_abs_fourierCoeff_of_le_derandomizedBLRAcceptance hε hX
    (θ := 1) (f := conj) (by rw [derandomizedBLRAcceptance_pure_conj]; norm_num)
  have h := hS.trans (abs_fourierCoeff_conj_le S)
  rw [one_pow] at h
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - ε by linarith)
  nlinarith [Real.sqrt_nonneg (1 - ε)]

/-- The fourth spectral moment of the conjunction is at most `1/4`, its largest squared
coefficient. -/
theorem sum_fourierCoeff_conj_pow_four_le :
    ∑ T, fourierCoeff (fun x => signVal (conj x)) T ^ 4 ≤ 1 / 4 := by
  obtain ⟨S, hS⟩ := exists_sum_fourierCoeff_signVal_pow_four_le conj
  have h := abs_fourierCoeff_conj_le S
  rw [← sq_abs] at hS
  nlinarith [abs_nonneg (fourierCoeff (fun x => signVal (conj x)) S)]

/-- A parity has coefficient `1` on its set, so it is at distance `0` from an affine function
`b ^^ parityOn S`. -/
theorem exists_hammingDist_xor_parityOn_eq_zero (S : Finset (Fin 3)) :
    ∃ b, hammingDist (parityOn S) (fun x => b ^^ parityOn S x) = 0 := by
  obtain ⟨b, hb⟩ := exists_hammingDist_xor_parityOn_le_of_le_abs_fourierCoeff (f := parityOn S)
    (S := S) (t := 1) (by rw [fourierCoeff_signVal_parityOn, ite_eq_left rfl, abs_one])
  refine ⟨b, Nat.eq_zero_of_le_zero ?_⟩
  have h2 : (0 : ℝ) < 2 ^ Fintype.card (Fin 3) := by positivity
  rw [div_le_iff₀ h2] at hb
  exact_mod_cast (show (hammingDist (parityOn S) fun x => b ^^ parityOn S x : ℝ) ≤ 0 by linarith)

end CslibFrontierTests.BooleanAnalysisDerandomizedBLR

end

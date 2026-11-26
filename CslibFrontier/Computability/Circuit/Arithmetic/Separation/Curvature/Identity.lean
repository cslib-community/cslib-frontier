/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.States
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.StateWords
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.AtOne
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.GlueDeterminant
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The identity for two crossing wires

Proposition B.2 of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. For sizes
`μ, ν` and energies `e₁, e₂`, with `Θ = 2 (e₁ + e₂)`, there are integer tensors `Ψ_0, …, Ψ_Θ` on
four copies of the states (`states μ e₁`, `states ν e₂`) such that their sum is the product of the
two diagonal tensors, `Ψ_N` is a sum of at most `(N + 1) P(N)` products of a function of
`(s_a, s_d)` and one of `(s_b, s_c)`, and of at most `(N' + 1) P(N')` products of a function of
`(s_a, s_b)` and one of `(s_c, s_d)`, `N' = Θ - N` (`exists_crossing_identity`). Here `Ψ_N` is the
coefficient of `X^N` in the determinant `psi` of the matrix `matM`, built from the coefficient
families `PowerSeries.meixnerB` and `PowerSeries.meixnerC`; a state enters as the pair of the
increasing enumerations of its two sets (`word`).

The proof follows the paper. A Schur complement and multilinear expansion write the coefficients of
low degree as sums of products (`Matrix.det_sumElim_smul_add`, `Matrix.exists_det_glue_eq_mul`),
the orthogonality of the coefficient families (`PowerSeries.pow_dvd_meixnerB_orthogonality`) makes
the blocks congruent to low-rank products, and the substitution `X ↦ 1/X` exchanges the sites `b`
and `d` and gives the high coefficients.

## Main results

* `exists_crossing_identity`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition B.2 of the paper; module `Paper.Identity` (`prop_identity`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Curvature

open Finset Matrix
open PowerSeries
    (meixnerB meixnerC pow_dvd_meixnerB_orthogonality pow_mul_meixnerB_of_mul_eq_one
        pow_mul_meixnerC_of_mul_eq_one)

/-- The paper's `E(T)`, for `T = (T₁, T₂)`. -/
private def enT {K : ℕ} (T : Finset (Fin K ⊕ Fin K)) : ℕ :=
  ∑ r ∈ T, Sum.elim (fun r : Fin K => 2 * (r : ℕ) + 1) (fun r : Fin K => 2 * (r : ℕ) + 1) r

/-- The `T` with `|T₁| = |T₂|` and `E(T) ≤ N`: the terms that contribute to the coefficient of
`x^N`. -/
private def goodT (K N : ℕ) : Finset (Finset (Fin K ⊕ Fin K)) :=
  univ.filter fun T => T.toLeft.card = T.toRight.card ∧ enT T ≤ N

section Blocks

variable {R : Type*} [CommRing R] {μ ν : ℕ}

/-- The paper's `F`: the rows `([r = i])_{r<K}` for `i ∈ I_a` and `(B(r,i))_{r<K}` for `i ∈ I_d`. -/
private def facA (K : ℕ) (x : R) (sa : Word μ) (sd : Word ν) : Matrix (Fin μ ⊕ Fin ν) (Fin K) R :=
  of (Sum.elim (fun i r => if sa.row i = (r : ℕ) then 1 else 0) fun i r =>
      meixnerB (x ^ 2) r (sd.row i))

/-- The paper's `G`: the columns `([r = j])_{r<K}` for `j ∈ J_c` and `((y−1)B(r,j))_{r<K}` for `j ∈
J_b`. -/
private def facB (K : ℕ) (x : R) (sc : Word μ) (sb : Word ν) : Matrix (Fin K) (Fin μ ⊕ Fin ν) R :=
  of fun r => Sum.elim (fun j => if (r : ℕ) = sc.col j then 1 else 0)
    fun j => (x ^ 2 - 1) * meixnerB (x ^ 2) r (sb.col j)

private theorem sum_ite_val (K n : ℕ) (f : ℕ → R) :
    ∑ r : Fin K, (if n = (r : ℕ) then f r else 0) = if n < K then f n else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => if n = r then f r else 0) K, Finset.sum_ite_eq]
  simp

/-- Proof of Proposition B.2, the coefficients: the block of rows `a, d` and columns `c, b` is
congruent modulo `X^(2K)` to `F D G`, with `F = facA`, `G = facB` and the block `blU`; its part at
`(d, b)` uses the orthogonality of the coefficient families. The other half, for the rows `c, b`
and columns `a, d`, is this theorem for the states with the two sets exchanged, transposed. -/
private theorem prop_identity_blocks (K : ℕ) (x : R) (sa : Word μ) (sd : Word ν) (sc : Word μ)
    (sb : Word ν)
    (i j : Fin μ ⊕ Fin ν) :
    x ^ (2 * K) ∣ blU x sa sd sc sb i j -
      (facA K x sa sd * diagonal (fun r : Fin K => x ^ (2 * (r : ℕ) + 1)) * facB K x sc sb) i j :=
          by
  have hdvd : ∀ n, ¬ n < K → x ^ (2 * K) ∣ x ^ (2 * n + 1) := fun n hn =>
    pow_dvd_pow x (by omega)
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j with j | j
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, fromBlocks_apply₁₁, ite_mul, one_mul,
      zero_mul]
    rw [sum_ite_val K (sa.row i) (fun r => x ^ (2 * r + 1) * if r = sc.col j then 1 else 0)]
    by_cases h1 : sa.row i < K
    · simp [h1]
    · by_cases h2 : sa.row i = sc.col j
      · rw [ite_eq_right h1, ite_eq_left h2, sub_zero]
        exact hdvd _ h1
      · simp [h1, h2]
  · simp only
      [facA, facB, blU, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₂, ite_mul, one_mul,
      zero_mul]
    rw [sum_ite_val K (sa.row i)
      (fun r => x ^ (2 * r + 1) * ((x ^ 2 - 1) * meixnerB (x ^ 2) r (sb.col j)))]
    by_cases h1 : sa.row i < K
    · rw [ite_eq_left h1]
      exact ⟨0, by ring⟩
    · rw [ite_eq_right h1, sub_zero]
      exact ((hdvd _ h1).mul_right _).mul_left _
  · simp only [facA, facB, blU, of_apply, Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₂₁, mul_ite,
      mul_one, mul_zero, @eq_comm ℕ _ (sc.col j)]
    rw [sum_ite_val K (sc.col j) (fun r => meixnerB (x ^ 2) r (sd.row i) * x ^ (2 * r + 1))]
    by_cases h1 : sc.col j < K
    · rw [ite_eq_left h1]
      exact ⟨0, by ring⟩
    · rw [ite_eq_right h1, sub_zero]
      exact (hdvd _ h1).mul_right _
  · simp only [facA, facB, blU, of_apply, Sum.elim_inr, fromBlocks_apply₂₂]
    obtain ⟨w, hw⟩ := pow_dvd_meixnerB_orthogonality (x ^ 2) K (sd.row i) (sb.col j)
    refine ⟨x * w, ?_⟩
    have e : ∑ r : Fin K, meixnerB (x ^ 2) r (sd.row i) * (x ^ (2 * (r : ℕ) + 1) *
        ((x ^ 2 - 1) * meixnerB (x ^ 2) r (sb.col j))) =
        -(x * ((1 - x ^ 2) * ∑ r ∈ Finset.range K, (x ^ 2) ^ r * (meixnerB (x ^ 2) r (sd.row i) *
          meixnerB (x ^ 2) r (sb.col j)))) := by
      rw [Finset.sum_range, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun r _ => by rw [← pow_mul, pow_succ]; ring
    have z : (if sd.row i = sb.col j then x ^ (2 * sd.row i + 1) else 0) =
        x * (if sd.row i = sb.col j then (x ^ 2) ^ sd.row i else 0) := by
      split_ifs
      · rw [← pow_mul, pow_succ, mul_comm]
      · simp
    rw [e, z, pow_mul]
    linear_combination x * hw

/-- Unfolds an entry of the matrices M and of the multipliers. -/
local macro "entries" : tactic => `(tactic| simp only [matM, blX, blY, blU, multiplier,
      Word.row_swap, Word.col_swap,
      multiplier', exchangeBD, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl,
      Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      of_apply, Matrix.neg_apply, transpose_apply, Matrix.zero_apply, mul_zero])

/-- Proof of Proposition B.2, reflection: substituting `1/X` for `X` and multiplying the rows and
columns of `a, c` by `X^(2 i + 1)`, those of `d` by `(y - 1) y^i` and those of `b` by `y^(i + 1)`
gives, by the reciprocity of the coefficient families, the matrix `matM` with the sites `b` and `d`
exchanged and the rows and columns of the new `d` multiplied by `1 - y`. Entry by entry, with `z`
the inverse of `x`, the multipliers `multiplier` and `multiplier'`, and `exchangeBD`. -/
private theorem prop_identity_exchange {x z : R} (h : x * z = 1) (sa : Word μ) (sb : Word ν)
    (sc : Word μ)
    (sd : Word ν)
    (i j : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) :
    multiplier x sa.row sb.row sc.row sd.row i *
        (multiplier x sa.col sb.col sc.col sd.col j * matM z sa sb sc sd i j) =
      multiplier' x i *
          (multiplier' x j * (matM x sa sd sc sb).submatrix (exchangeBD μ ν) (exchangeBD μ ν) i j)
              := by
  have h2 : x ^ 2 * z ^ 2 = 1 := by rw [← mul_pow, h, one_pow]
  have hB := pow_mul_meixnerB_of_mul_eq_one h2
  have hC := pow_mul_meixnerC_of_mul_eq_one h2
  have hz : ∀ m : ℕ, x ^ (2 * m + 1) * z ^ (2 * m + 1) = 1 := fun m => by rw [← mul_pow, h, one_pow]
  rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;> entries
  · linear_combination (x ^ (2 * sa.row i + 1) * (x ^ 2 - 1)) * hC (sa.row i) (sd.col j)
  · by_cases h1 : sa.row i = sc.col j
    · rw [ite_eq_left h1, ite_eq_left h1, ← h1]
      linear_combination x ^ (2 * sa.row i + 1) * hz (sa.row i)
    · simp [h1]
  · linear_combination (x ^ 2 * (z ^ 2 - 1) * ((x ^ 2) ^ sb.col j *
        meixnerB (z ^ 2) (sa.row i) (sb.col j))) * hz (sa.row i) +
      (x ^ 2 * (z ^ 2 - 1)) * hB (sa.row i) (sb.col j) + meixnerC (x ^ 2) (sa.row i) (sb.col j) * h2
  · linear_combination (-(x ^ (2 * sa.col j + 1) * (x ^ 2 - 1))) * hC (sa.col j) (sd.row i)
  · linear_combination ((x ^ 2 - 1) *
        ((x ^ 2) ^ sd.row i * meixnerB (z ^ 2) (sc.col j) (sd.row i))) *
      hz (sc.col j) + (x ^ 2 - 1) * hB (sc.col j) (sd.row i)
  · by_cases h1 : sd.row i = sb.col j
    · rw [ite_eq_left h1, ite_eq_left h1.symm, ← h1]
      linear_combination (x ^ (2 * sd.row i + 1) * (1 - x ^ 2)) * hz (sd.row i)
    · simp [h1, Ne.symm h1]
  · by_cases h1 : sa.col j = sc.row i
    · rw [ite_eq_left h1, ite_eq_left h1, ← h1]
      linear_combination (-x ^ (2 * sa.col j + 1)) * hz (sa.col j)
    · simp [h1]
  · linear_combination (-(x ^ 2 - 1) *
        ((x ^ 2) ^ sd.col j * meixnerB (z ^ 2) (sc.row i) (sd.col j))) *
      hz (sc.row i) - (x ^ 2 - 1) * hB (sc.row i) (sd.col j)
  · linear_combination (-(x ^ (2 * sc.row i + 1) * (1 - x ^ 2))) * hC (sc.row i) (sb.col j) -
      (x ^ (2 * sc.row i + 1) * (x ^ 2) ^ sb.col j * meixnerC (z ^ 2) (sc.row i) (sb.col j)) * h2
  · linear_combination (-(x ^ 2 * (z ^ 2 - 1) * ((x ^ 2) ^ sb.row i *
        meixnerB (z ^ 2) (sa.col j) (sb.row i)))) * hz (sa.col j) -
      (x ^ 2 * (z ^ 2 - 1)) * hB (sa.col j) (sb.row i) - meixnerC (x ^ 2) (sa.col j) (sb.row i) * h2
  · by_cases h1 : sd.col j = sb.row i
    · rw [ite_eq_left h1, ite_eq_left h1.symm, ← h1]
      linear_combination (x ^ (2 * sd.col j + 1) * (x ^ 2 - 1)) * hz (sd.col j)
    · simp [h1, Ne.symm h1]
  · linear_combination (x ^ (2 * sc.col j + 1) * (1 - x ^ 2)) * hC (sc.col j) (sb.row i) +
      (x ^ (2 * sc.col j + 1) * (x ^ 2) ^ sb.row i * meixnerC (z ^ 2) (sc.col j) (sb.row i)) * h2

/-- Proof of Proposition B.2, reflection: rows and columns are permuted alike, so there is no sign,
and the product of all multipliers times `Ψ(1/X; s_a, s_b, s_c, s_d)` is
`(1 - y)^(2ν) Ψ(X; s_a, s_d, s_c, s_b)`. -/
private theorem prop_identity_exchange_det {x z : R} (h : x * z = 1) (sa : Word μ) (sb : Word ν)
    (sc : Word μ) (sd : Word ν) :
    (∏ i, multiplier x sa.row sb.row sc.row sd.row i) *
        ((∏ i, multiplier x sa.col sb.col sc.col sd.col i) * psi z sa sb sc sd) =
      (∏ i, (multiplier' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i) *
      ((∏ i, (multiplier' x : (Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν) → R) i) * psi x sa sd sc sb) := by
  rw [psi, psi, ← det_submatrix_equiv_self (exchangeBD μ ν) (matM x sa sd sc sb),
    ← det_mul_row (multiplier x sa.col sb.col sc.col sd.col) (matM z sa sb sc sd),
    ← det_mul_column (multiplier x sa.row sb.row sc.row sd.row)
        (of fun i j => multiplier x sa.col sb.col sc.col sd.col j *
      matM z sa sb sc sd i j),
    ← det_mul_row (multiplier' x)
        ((matM x sa sd sc sb).submatrix (exchangeBD μ ν) (exchangeBD μ ν)),
    ← det_mul_column (multiplier' x) (of fun i j => multiplier' x j *
      (matM x sa sd sc sb).submatrix (exchangeBD μ ν) (exchangeBD μ ν) i j)]
  exact congrArg det (Matrix.ext (prop_identity_exchange h sa sb sc sd))

/-- Proof of Proposition B.2, reflection: the multipliers at `a, c, d, b` contain `X` to the powers
`e₁, e₁, e₂ - 2ν, e₂ + 2ν`, `Θ` in all, and the factors `(y - 1)^(2ν)` and `(1 - y)^(2ν)` cancel.
So `X^Θ Ψ(1/X; s_a, s_b, s_c, s_d) = Ψ(X; s_a, s_d, s_c, s_b)`, `Θ = 2 (e₁ + e₂)`. Here `x` is an
element of a domain with inverse `z` and `x² ≠ 1`; the paper's case is `x = X` in the field of
fractions of `ℤ[X]`. -/
private theorem prop_identity_reflection [IsDomain R] {x z : R} (h : x * z = 1) (h1 : x ^ 2 ≠ 1)
    (sa : Word μ) (sb : Word ν) (sc : Word μ)
    (sd : Word ν) {e₁ e₂ : ℕ} (ha : wordEnergy sa = e₁) (hb : wordEnergy sb = e₂)
        (hc : wordEnergy sc = e₁) (hd : wordEnergy sd = e₂) :
    x ^ (2 * (e₁ + e₂)) * psi z sa sb sc sd = psi x sa sd sc sb := by
  have key := prop_identity_exchange_det h sa sb sc sd
  rw [prod_multiplier, prod_multiplier, prod_multiplier'] at key
  have hne : (1 - x ^ 2) ^ ν * (1 - x ^ 2) ^ ν ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 h1.symm)) (pow_ne_zero _ (sub_ne_zero.2 h1.symm))
  refine mul_left_cancel₀ hne ?_
  have hs : (x ^ 2 - 1) ^ ν * (x ^ 2 - 1) ^ ν = (1 - x ^ 2) ^ ν * (1 - x ^ 2) ^ ν := by
    rw [← mul_pow, ← mul_pow]
    exact congrArg (· ^ ν) (by ring)
  have hexp : (∑ i, (2 * sa.row i + 1)) + (∑ i, (2 * sc.row i + 1)) + (∑ i, 2 * sd.row i) +
      (∑ i, (2 * sb.row i + 2)) +
          ((∑ i, (2 * sa.col i + 1)) + (∑ i, (2 * sc.col i + 1)) + (∑ i, 2 * sd.col i) +
      ∑ i, (2 * sb.col i + 2)) = 2 * (e₁ + e₂) := by
    unfold wordEnergy at ha hb hc hd
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] at ha hb hc hd ⊢
    omega
  generalize (∑ i, (2 * sa.row i + 1)) + (∑ i, (2 * sc.row i + 1)) + (∑ i, 2 * sd.row i) +
    (∑ i, (2 * sb.row i + 2)) = a at key hexp
  generalize (∑ i, (2 * sa.col i + 1)) + (∑ i, (2 * sc.col i + 1)) + (∑ i, 2 * sd.col i) +
    (∑ i, (2 * sb.col i + 2)) = b at key hexp
  rw [← hexp, pow_add]
  linear_combination key - (x ^ a * x ^ b * psi z sa sb sc sd) * hs

end Blocks

/-- Proof of Proposition B.2 at `X = 1`: for states in the given classes, `Ψ` at `1` is a sign
depending on `μ, ν` only, times the indicator that the second set at `c` is the first at `a`, the
first at `c` the second at `a`, and likewise for `b` and `d`. -/
private theorem prop_identity_one (μ ν : ℕ) : ∃ ε : ℤˣ,
    ∀ (sa : Word μ) (sb : Word ν) (sc : Word μ) (sd : Word ν),
    StrictMono sa.row → StrictMono sa.col → StrictMono sb.row → StrictMono sb.col →
    StrictMono sc.row → StrictMono sc.col → StrictMono sd.row → StrictMono sd.col →
    psi (1 : ℤ) sa sb sc sd = ε * if sa = sc.swap ∧ sb = sd.swap then 1 else 0 := by
  let e : Equiv.Perm ((Fin μ ⊕ Fin ν) ⊕ (Fin μ ⊕ Fin ν)) := Equiv.sumComm _ _
  refine ⟨Equiv.Perm.sign e * (-1) ^ (μ + ν), fun sa sb sc sd ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2 => ?_⟩
  have h1 := det_permute' e (matM (1 : ℤ) sa sb sc sd)
  have h2 : (matM (1 : ℤ) sa sb sc sd).submatrix id e =
      fromBlocks (blU (1 : ℤ) sa sd sc sb) (blX (1 : ℤ) sa sd) (blY (1 : ℤ) sc sb)
        (-(blU (1 : ℤ) sa.swap sd.swap sc.swap sb.swap)ᵀ) :=
    Matrix.ext fun i j => by rcases i with i | i <;> rcases j with j | j <;> simp [matM, e]
  have hY : blY (1 : ℤ) sc sb = 0 :=
    Matrix.ext fun i j => by rcases i with i | i <;> rcases j with j | j <;> simp [blY]
  have hU : ∀ (sa : Word μ) (sd : Word ν) (sc : Word μ) (sb : Word ν),
      StrictMono sa.row → StrictMono sd.row →
      StrictMono sc.col → StrictMono sb.col →
      (blU (1 : ℤ) sa sd sc sb).det = (-1) ^ ν * ((if sa.row = sc.col then 1 else 0) *
        (if sd.row = sb.col then 1 else 0)) := by
    intro sa sd sc sb k1 k2 k3 k4
    have e1 : blU (1 : ℤ) sa sd sc sb =
        fromBlocks (of fun i j => if sa.row i = sc.col j then 1 else 0) 0
        (of fun i j => meixnerB 1 (sc.col j) (sd.row i))
            (-(of fun i j => if sd.row i = sb.col j then 1 else 0)) :=
      Matrix.ext fun i j => by rcases i with i | i <;> rcases j with j | j <;> simp [blU]
    rw [e1, det_fromBlocks_zero₁₂, det_neg, Fintype.card_fin, det_coinc _ _ k1 k3,
        det_coinc _ _ k2 k4]
    ring
  rw [h2, hY, det_fromBlocks_zero₂₁, det_neg, det_transpose, hU _ _ _ _ ha1 hd1 hc2 hb2,
    hU _ _ _ _ ha2 hd2 hc1 hb1] at h1
  simp only [Word.row_swap, Word.col_swap, Fintype.card_sum, Fintype.card_fin] at h1
  have hs : ((Equiv.Perm.sign e : ℤˣ) : ℤ) * ((Equiv.Perm.sign e : ℤˣ) : ℤ) = 1 :=
      Int.units_coe_mul_self _
  have hν : ((-1 : ℤ) ^ ν) * (-1) ^ ν = 1 := by rw [← mul_pow]; simp
  have hind : (if sa = sc.swap ∧ sb = sd.swap then (1 : ℤ) else 0) =
      ((if sa.row = sc.col then 1 else 0) * (if sd.row = sb.col then 1 else 0)) *
      ((if sa.col = sc.row then 1 else 0) * (if sd.col = sb.row then 1 else 0)) := by
    have hmul (p q : Prop) [Decidable p] [Decidable q] :
        (if p ∧ q then (1 : ℤ) else 0) = (if p then 1 else 0) * (if q then 1 else 0) := by
      by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
    simp only [Word.ext_iff, Word.row_swap, Word.col_swap, @eq_comm _ sb.row, @eq_comm _ sb.col,
      hmul]
    ring
  rw [psi, hind]
  push_cast
  linear_combination (-(matM (1 : ℤ) sa sb sc sd).det) * hs - ((Equiv.Perm.sign e : ℤˣ) : ℤ) * h1
    + ((Equiv.Perm.sign e : ℤˣ) : ℤ) * (-1) ^ (μ + ν) *
        (((if sa.row = sc.col then 1 else 0) * (if sd.row = sb.col then 1 else 0)) *
      ((if sa.col = sc.row then 1 else 0) * (if sd.col = sb.row then 1 else 0))) * hν

/-- A sum of products over a finite index set is a sum of `r` products, if `r` is at least the size
of the index set. -/
private theorem exists_products {β γ κ : Type} [Fintype κ] {f : β → γ → ℤ} (g : κ → β → ℤ)
    (h : κ → γ → ℤ)
    (hf : ∀ b c, f b c = ∑ t, g t b * h t c) {r : ℕ} (hr : Fintype.card κ ≤ r) :
    ∃ (g' : Fin r → β → ℤ) (h' : Fin r → γ → ℤ), ∀ b c, f b c = ∑ t, g' t b * h' t c := by
  classical
  let e := Fintype.equivFin κ
  refine ⟨fun t b => if ht : t.1 < Fintype.card κ then g (e.symm ⟨t.1, ht⟩) b else 0,
    fun t c => if ht : t.1 < Fintype.card κ then h (e.symm ⟨t.1, ht⟩) c else 0, fun b c => ?_⟩
  rw [hf]
  refine Finset.sum_of_injOn (fun t => Fin.castLE hr (e t))
    (fun _ _ _ _ he => e.injective (Fin.castLE_injective hr he)) (fun _ _ => by simp)
        (fun t _ ht => ?_) (fun t _ => ?_)
  · have hlt : ¬ t.1 < Fintype.card κ :=
      fun hlt => ht ⟨e.symm ⟨t.1, hlt⟩, by simp, by simp [Fin.castLE]⟩
    simp [hlt]
  · simp [(e t).2]

section Expansion

/-! ### The coefficients: the expansion

In this section `X = M₁`, `Y = M₂`, `A = F`, `A' = F'`, `B = G`, `B' = -G'` in the paper's letters,
and `l` is the diagonal of `D`. -/

variable {p q ρ : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype ρ]
    [DecidableEq ρ]
variable {R : Type*} [CommRing R]

/-- Proof of Proposition B.2, the coefficients: by a Schur complement, the determinant of the
matrix with the diagonal blocks `X, Y` and the other blocks `A D B`, `B' D A'` equals that of the
matrix with the block rows `(X, 0, A, 0)`, `(0, Y, 0, B')`, `(0, -D B, 1, 0)`, `(-D A', 0, 0, 1)`.
The paper allows a sign depending on the size; with these blocks there is none. -/
private theorem prop_identity_schur (l : ρ → R) (X : Matrix p p R) (A : Matrix p ρ R)
    (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (fromBlocks X (A * diagonal l * B) (B' * diagonal l * A') Y).det =
      (fromBlocks (fromBlocks X 0 0 Y) (fromBlocks A 0 0 B')
        (-(fromBlocks 0 (diagonal l * B) (diagonal l * A') 0)) 1).det := by
  rw [det_fromBlocks_one₂₂]
  congr 1
  rw [Matrix.mul_neg, sub_neg_eq_add, fromBlocks_multiply, fromBlocks_add]
  simp [Matrix.mul_assoc]

/-- Proof of Proposition B.2, the coefficients: each of the last rows is the sum of its part in
`D B`, respectively `D A'`, and its entry `±1`. Expanding by multilinearity over the sets `T` of
rows whose first part is taken, the term of `T` is the product of the entries of `D` in `T` (the
paper's `X^E(T)`) times the determinant of `termMat T`, in which the rows outside `T` keep only
their entry `1`. -/
private theorem prop_identity_expand (l : ρ → R) (X : Matrix p p R) (A : Matrix p ρ R)
    (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (fromBlocks X (A * diagonal l * B) (B' * diagonal l * A') Y).det =
      ∑ T : Finset (ρ ⊕ ρ), (∏ r ∈ T, Sum.elim l l r) * (termMat T X A A' Y B B').det := by
  have h1 :
      (of (Sum.elim (topRows X A Y B') fun r => Sum.elim l l r • lowRows A' B r + unitRows r) :
      Matrix ((p ⊕ q) ⊕ (ρ ⊕ ρ)) ((p ⊕ q) ⊕ (ρ ⊕ ρ)) R) =
      fromBlocks (fromBlocks X 0 0 Y) (fromBlocks A 0 0 B')
        (-(fromBlocks 0 (diagonal l * B) (diagonal l * A') 0)) 1 := by
    ext i j
    rcases i with (i | i) | (i | i) <;> rcases j with (j | j) | (j | j) <;>
      simp [topRows, lowRows, unitRows, Matrix.diagonal_mul]
  rw [prop_identity_schur, ← h1]
  exact Matrix.det_sumElim_smul_add (topRows X A Y B') (Sum.elim l l) (lowRows A' B) unitRows

/-- Proof of Proposition B.2, the coefficients: the term of `T` vanishes unless the two parts of `T`
have the same size, because the blocks are not square otherwise. (The rows outside `T` are kept,
with their entry `1`; the form with two blocks is `termMat_eq_glue`.) -/
private theorem prop_identity_term_zero (T : Finset (ρ ⊕ ρ)) (hT : T.toLeft.card ≠ T.toRight.card)
    (X : Matrix p p R) (A : Matrix p ρ R) (A' : Matrix ρ p R)
    (Y : Matrix q q R) (B : Matrix ρ q R) (B' : Matrix q ρ R) :
    (termMat T X A A' Y B B').det = 0 := by
  have := card_rowGroup (p := p) (q := q) T
  rw [termMat_eq_glue]
  exact Matrix.det_glue_eq_zero_of_card_ne _ _ _ _ (by rw [card_colGroup]; omega)

/-- Proof of Proposition B.2, the coefficients: for every `T`, the determinant of the term is a
function of `(X, A, A')` times a function of `(Y, B, B')`. -/
private theorem prop_identity_term_product (T : Finset (ρ ⊕ ρ)) :
    ∃ (α : Matrix p p R → Matrix p ρ R → Matrix ρ p R → R)
      (β : Matrix q q R → Matrix ρ q R → Matrix q ρ R → R),
      ∀ X A A' Y B B', (termMat T X A A' Y B B').det = α X A A' * β Y B B' := by
  obtain ⟨a, b, h⟩ := Matrix.exists_det_glue_eq_mul (R := R)
      (rowGroup T : (p ⊕ q) ⊕ (ρ ⊕ ρ) → Prop) colGroup
  exact ⟨fun X A A' => a (termMat T X A A' 0 0 0), fun Y B B' => b (termMat T 0 0 0 Y B B'),
    fun X A A' Y B B' => by rw [termMat_eq_glue, h]⟩

/-- Proof of Proposition B.2, the coefficients: the sets `T` with parts of equal size and energy at
most `N` are at most `P(N)` states. -/
private theorem prop_identity_term_count (K N : ℕ) : (goodT K N).card ≤ stateCount N := by
  change (goodT K N).card ≤ (lowStates N).card
  refine Finset.card_le_card_of_injOn
    (fun T => (T.toLeft.map Fin.valEmbedding, T.toRight.map Fin.valEmbedding)) ?_ ?_
  · intro T hT
    have hT' := (mem_filter.1 hT).2
    have e1 : enT T = energy (T.toLeft.map Fin.valEmbedding) +
        energy (T.toRight.map Fin.valEmbedding) := by
      conv_lhs => rw [← T.toLeft_disjSum_toRight]
      unfold enT energy
      rw [Finset.sum_disjSum, Finset.sum_map, Finset.sum_map]
      rfl
    exact mem_coe.2 (mem_lowStates.2 ⟨by simpa using hT'.1, e1 ▸ hT'.2⟩)
  · intro T _ T' _ h
    rw [← T.toLeft_disjSum_toRight, ← T'.toLeft_disjSum_toRight,
      Finset.map_injective _ (Prod.ext_iff.1 h).1, Finset.map_injective _ (Prod.ext_iff.1 h).2]

open Polynomial in
/-- Proof of Proposition B.2, the coefficients: the degree `N - E(T)` can be split between the two
factors in at most `N + 1` ways. So the coefficient of `X^N` of the determinant of a matrix with
the diagonal blocks `X, Y` and the other blocks `A D B`, `B' D A'`, `D = diag(X^(2r+1))`, is a sum,
over the `T` with parts of equal size and energy at most `N` and over `N + 1` degrees, of products
of a function of `(X, A, A')` and one of `(Y, B, B')`. -/
private theorem prop_identity_near (K N : ℕ) {S T : Type*}
    (X : S → Matrix p p ℤ[X]) (A : S → Matrix p (Fin K) ℤ[X]) (A' : S → Matrix (Fin K) p ℤ[X])
    (Y : T → Matrix q q ℤ[X]) (B : T → Matrix (Fin K) q ℤ[X]) (B' : T → Matrix q (Fin K) ℤ[X]) :
    ∃ (g : ↥(goodT K N) × Fin (N + 1) → S → ℤ) (h : ↥(goodT K N) × Fin (N + 1) → T → ℤ), ∀ s t,
      (fromBlocks (X s)
          (A s * diagonal (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) * B t)
        (B' t * diagonal (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) * A' s)
            (Y t)).det.coeff N =
      ∑ k, g k s * h k t := by
  choose α β hαβ using fun T : Finset (Fin K ⊕ Fin K) => prop_identity_term_product (p := p)
      (q := q) (R := ℤ[X]) T
  refine ⟨fun k s => (α k.1 (X s) (A s) (A' s)).coeff k.2,
    fun k t => ((Polynomial.X : ℤ[X]) ^ (enT (k.1 : Finset (Fin K ⊕ Fin K))) *
      β k.1 (Y t) (B t) (B' t)).coeff (N - k.2), fun s t => ?_⟩
  rw [prop_identity_expand, Polynomial.finsetSum_coeff, Fintype.sum_prod_type]
  have hw (T : Finset (Fin K ⊕ Fin K)) :
      ∏ r ∈ T, Sum.elim (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1))
        (fun r : Fin K => (Polynomial.X : ℤ[X]) ^ (2 * (r : ℕ) + 1)) r = Polynomial.X ^ enT T := by
    rw [enT, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun r _ => by rcases r with r | r <;> rfl
  rw [← Finset.sum_subset (Finset.subset_univ (goodT K N)), ← Finset.sum_coe_sort]
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [hw, hαβ, mul_left_comm, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range]
  · intro T _ hT
    rw [hw]
    by_cases hb : T.toLeft.card = T.toRight.card
    · rw [Polynomial.coeff_X_pow_mul',
        ite_eq_right fun hle => hT (mem_filter.2 ⟨mem_univ _, hb, hle⟩)]
    · rw [prop_identity_term_zero T hb, mul_zero, Polynomial.coeff_zero]

end Expansion

open Polynomial in
/-- Proof of Proposition B.2, part (b): the coefficient of `X^N` in `Ψ` is a sum of at most
`(N + 1) P(N)` products of a function of `(s_a, s_d)` and one of `(s_b, s_c)`. The paper uses this
only for the coefficients of degree `N < 2K`, here with `K = N + 1`. -/
private theorem prop_identity_coefficients (μ ν N : ℕ) :
    ∃ (g : Fin ((N + 1) * stateCount N) → Word μ × Word ν → ℤ)
        (h : Fin ((N + 1) * stateCount N) → Word ν × Word μ → ℤ),
      ∀ (sa : Word μ) (sb : Word ν) (sc : Word μ) (sd : Word ν),
        (psi (Polynomial.X : ℤ[X]) sa sb sc sd).coeff N = ∑ k, g k (sa, sd) * h k (sb, sc) := by
  obtain ⟨g, h, hgh⟩ := prop_identity_near (p := Fin μ ⊕ Fin ν) (q := Fin μ ⊕ Fin ν) (N + 1) N
    (S := Word μ × Word ν) (T := Word ν × Word μ)
    (fun s => blX X s.1 s.2) (fun s => facA (N + 1) X s.1 s.2)
    (fun s => (facA (N + 1) X s.1.swap s.2.swap)ᵀ)
    (fun t => blY X t.2 t.1) (fun t => facB (N + 1) X t.2 t.1)
    (fun t => -(facB (N + 1) X t.2.swap t.1.swap)ᵀ)
  have key : ∀ (sa : Word μ) (sb : Word ν) (sc : Word μ) (sd : Word ν),
      (psi (Polynomial.X : ℤ[X]) sa sb sc sd).coeff N = ∑ k, g k (sa, sd) * h k (sb, sc) := by
    intro sa sb sc sd
    rw [← hgh, ← sub_eq_zero, ← Polynomial.coeff_sub]
    refine (Polynomial.X_pow_dvd_iff (n := 2 * (N + 1))).1 ?_ N (by omega)
    refine dvd_det_sub _ _ _ fun i j => ?_
    rcases i with i | i <;> rcases j with j | j
    · simp [matM]
    · simpa only [matM, fromBlocks_apply₁₂] using prop_identity_blocks (N + 1) X sa sd sc sb i j
    · simp only [matM, fromBlocks_apply₂₁]
      rw [Matrix.neg_mul, Matrix.neg_mul, ← Matrix.diagonal_transpose, ← Matrix.transpose_mul,
        ← Matrix.transpose_mul, ← Matrix.mul_assoc]
      convert (prop_identity_blocks (N + 1) (X : ℤ[X]) sa.swap sd.swap sc.swap sb.swap
          j i).neg_right using 1
      simp only [Matrix.neg_apply, Matrix.transpose_apply]
      ring
    · simp [matM]
  have hcard : Fintype.card (↥(goodT (N + 1) N) × Fin (N + 1)) ≤ (N + 1) * stateCount N := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (prop_identity_term_count _ _)
  obtain ⟨g', h', e⟩ := exists_products (f := fun (p : Word μ × Word ν) (q : Word ν × Word μ) =>
    (psi (Polynomial.X : ℤ[X]) p.1 q.1 q.2 p.2).coeff N) g h (fun p q => key p.1 q.1 q.2 p.2) hcard
  exact ⟨g', h', fun sa sb sc sd => e (sa, sd) (sb, sc)⟩

section reflect

open Polynomial

variable {μ ν : ℕ}

/-- The reflection identity for polynomials: the reverse of `Ψ(X; s_a, s_b, s_c, s_d)` is
`Ψ(X; s_a, s_d, s_c, s_b)`, up to powers of `X`. -/
private theorem prop_identity_reverse (sa : Word μ) (sb : Word ν) (sc : Word μ) (sd : Word ν)
    {e₁ e₂ : ℕ} (ha : wordEnergy sa = e₁)
    (hb : wordEnergy sb = e₂) (hc : wordEnergy sc = e₁) (hd : wordEnergy sd = e₂) :
    (psi (X : ℤ[X]) sa sb sc sd).reverse * X ^ (2 * (e₁ + e₂)) =
      psi (X : ℤ[X]) sa sd sc sb * X ^ (psi (X : ℤ[X]) sa sb sc sd).natDegree := by
  set P := psi (X : ℤ[X]) sa sb sc sd with hP
  set Q := psi (X : ℤ[X]) sa sd sc sb with hQ
  let F := FractionRing ℤ[X]
  let ι : ℤ[X] →+* F := algebraMap ℤ[X] F
  have hι : Function.Injective ι := IsFractionRing.injective ℤ[X] F
  let x : F := ι X
  have hx : x ≠ 0 := fun h => X_ne_zero (hι (h.trans (map_zero ι).symm))
  have hxz : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have hx1 : x ^ 2 ≠ 1 := fun h => by
    simpa [coeff_one] using
      congrArg (fun p : ℤ[X] => p.coeff 2) (hι (by simpa [x] using h : ι (X ^ 2) = ι 1))
  have hi : ι = eval₂RingHom (Int.castRingHom F) x :=
    Polynomial.ringHom_ext (fun _ => by simp) (by simp [x])
  let φ : ℤ[X] →+* F := eval₂RingHom (Int.castRingHom F) x⁻¹
  let _ : Invertible (x⁻¹ : F) := ⟨x, hxz, mul_comm x x⁻¹ ▸ hxz⟩
  have hrev : ι P.reverse * (x⁻¹) ^ P.natDegree = φ P := by
    rw [hi, coe_eval₂RingHom]
    exact eval₂_reverse_mul_pow (Int.castRingHom F) (x⁻¹ : F) P
  have key := prop_identity_reflection hxz hx1 sa sb sc sd ha hb hc hd
  have hφP : psi (x⁻¹ : F) sa sb sc sd = φ P := by simp [hP, map_psi, φ]
  rw [hφP, show psi x sa sd sc sb = ι Q by rw [hQ, map_psi], ← hrev] at key
  apply hι
  rw [map_mul, map_mul, map_pow, map_pow, ← key]
  change ι P.reverse * x ^ _ = _ * x ^ _
  have : (x⁻¹) ^ P.natDegree * x ^ P.natDegree = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hx, one_pow]
  linear_combination (-(ι P.reverse * x ^ (2 * (e₁ + e₂)))) * this

/-- Proof of Proposition B.2, reflection: `deg Ψ ≤ Θ`, and the coefficient of `X^N` at
`(s_a, s_b, s_c, s_d)` is that of `X^(Θ - N)` at `(s_a, s_d, s_c, s_b)`. -/
private theorem prop_identity_reflection_coeff (sa : Word μ) (sb : Word ν) (sc : Word μ)
    (sd : Word ν)
    {e₁ e₂ : ℕ} (ha : wordEnergy sa = e₁)
    (hb : wordEnergy sb = e₂) (hc : wordEnergy sc = e₁) (hd : wordEnergy sd = e₂) :
    (psi (X : ℤ[X]) sa sb sc sd).natDegree ≤ 2 * (e₁ + e₂) ∧
    ∀ N M, N + M = 2 * (e₁ + e₂) →
      (psi (X : ℤ[X]) sa sb sc sd).coeff N = (psi (X : ℤ[X]) sa sd sc sb).coeff M := by
  have key := prop_identity_reverse sa sb sc sd ha hb hc hd
  set P := psi (X : ℤ[X]) sa sb sc sd
  set H := 2 * (e₁ + e₂)
  have hdeg : P.natDegree ≤ H := by
    by_contra hcon
    have h1 := congrArg (fun p : ℤ[X] => p.coeff H) key
    simp only [coeff_mul_X_pow', le_refl, ite_true, Nat.sub_self, hcon, ite_false,
      coeff_zero_reverse, leadingCoeff_eq_zero] at h1
    exact hcon (by simp [h1])
  refine ⟨hdeg, fun N M hNM => ?_⟩
  rcases le_or_gt N P.natDegree with hN | hN
  · have h1 := congrArg (fun p : ℤ[X] => p.coeff (H + (P.natDegree - N))) key
    simp only [coeff_mul_X_pow', Nat.le_add_right, ite_true, Nat.add_sub_cancel_left] at h1
    rw [ite_eq_left (by omega), coeff_reverse, revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hN] at h1
    exact h1.trans (congrArg _ (by omega))
  · have h1 := congrArg (fun p : ℤ[X] => p.coeff (M + P.natDegree)) key
    simp only [coeff_mul_X_pow', Nat.le_add_left, ite_true, Nat.add_sub_cancel,
      ite_eq_right (by omega : ¬ H ≤ M + P.natDegree)] at h1
    rw [coeff_eq_zero_of_natDegree_lt hN, h1]

end reflect

/-- **Paper: Proposition B.2.** Let `Θ = 2 (e₁ + e₂)`. There are integer tensors
`Ψ_0, …, Ψ_Θ` such that (a) `∑_N Ψ_N` is the product of the diagonal tensors of the states of size
`μ` and energy `e₁` (at `a, c`) and of size `ν` and energy `e₂` (at `b, d`); (b) `Ψ_N` is a sum of
at most `(N + 1) P(N)` products of a function of `(s_a, s_d)` and one of `(s_b, s_c)`; (c) `Ψ_N`
is a sum of at most `(N' + 1) P(N')` products of a function of `(s_a, s_b)` and one of
`(s_c, s_d)`, where `N' = Θ - N`. -/
theorem exists_crossing_identity (μ ν e₁ e₂ : ℕ) :
    ∃ Ψ : Fin (2 * (e₁ + e₂) + 1) → ↥(states μ e₁) → ↥(states ν e₂) → ↥(states μ e₁) →
        ↥(states ν e₂) → ℤ,
      (∀ a b c d, ∑ N, Ψ N a b c d = (if a = c then 1 else 0) * (if b = d then 1 else 0)) ∧
      (∀ N : Fin (2 * (e₁ + e₂) + 1),
          ∃ (g : Fin ((N.1 + 1) * stateCount N) → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
        (h : Fin ((N.1 + 1) * stateCount N) → ↥(states ν e₂) × ↥(states μ e₁) → ℤ),
        ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, d) * h k (b, c)) ∧
      (∀ N : Fin (2 * (e₁ + e₂) + 1), ∀ N', N' = 2 * (e₁ + e₂) - N.1 →
        ∃ (g : Fin ((N' + 1) * stateCount N') → ↥(states μ e₁) × ↥(states ν e₂) → ℤ)
        (h : Fin ((N' + 1) * stateCount N') → ↥(states μ e₁) × ↥(states ν e₂) → ℤ),
        ∀ a b c d, Ψ N a b c d = ∑ k, g k (a, b) * h k (c, d)) := by
  obtain ⟨ε, hε⟩ := prop_identity_one μ ν
  have hrefl (a : ↥(states μ e₁)) (b : ↥(states ν e₂)) (c : ↥(states μ e₁)) (d : ↥(states ν e₂)) :=
    prop_identity_reflection_coeff (word a) (word b) (word c).swap (word d).swap
      (wordEnergy_word a) (wordEnergy_word b)
      ((wordEnergy_swap _).trans (wordEnergy_word c))
      ((wordEnergy_swap _).trans (wordEnergy_word d))
  refine ⟨fun N a b c d => ε * (psi (Polynomial.X : Polynomial ℤ) (word a) (word b) (word c).swap
    (word d).swap).coeff N, fun a b c d => ?_, fun N => ?_, fun N _ hN' => ?_⟩
  · rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun N =>
      (psi (Polynomial.X : Polynomial ℤ) (word a) (word b) (word c).swap (word d).swap).coeff N)]
    have h1 := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hrefl a b c d).1) 1
    simp only [one_pow, mul_one] at h1
    rw [← Nat.succ_eq_add_one, ← h1, ← Polynomial.coe_evalRingHom, map_psi,
      Polynomial.coe_evalRingHom, Polynomial.eval_X,
      hε _ _ _ _ (word_strictMono a).1 (word_strictMono a).2 (word_strictMono b).1
        (word_strictMono b).2 (word_strictMono c).2 (word_strictMono c).1 (word_strictMono d).2
        (word_strictMono d).1, ← mul_assoc, Int.units_coe_mul_self ε, one_mul, Word.swap_swap,
      Word.swap_swap, ite_and]
    simp only [word_injective.eq_iff]
    split_ifs <;> simp
  · obtain ⟨g, h, hgh⟩ := prop_identity_coefficients μ ν N
    refine ⟨fun k p => ε * g k (word p.1, (word p.2).swap),
      fun k p => h k (word p.1, (word p.2).swap), fun a b c d => ?_⟩
    simp only [hgh, Finset.mul_sum, mul_assoc]
  · subst hN'
    obtain ⟨g, h, hgh⟩ := prop_identity_coefficients μ ν (2 * (e₁ + e₂) - N)
    refine ⟨fun k p => ε * g k (word p.1, word p.2),
      fun k p => h k ((word p.2).swap, (word p.1).swap), fun a b c d => ?_⟩
    dsimp only
    rw [(hrefl a b c d).2 N (2 * (e₁ + e₂) - N) (by omega), hgh, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

end Cslib.Circuits.Arithmetic.Separation.Curvature

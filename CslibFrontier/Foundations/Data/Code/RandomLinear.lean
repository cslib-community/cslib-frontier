/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.BallVolume
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Tactic.LinarithCast
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The distance of random linear codes

A `k`-by-`n` generating matrix `G` over `𝔽₂` encodes `x ∈ 𝔽₂ᵏ` as the combination `x ᵥ* G` of
its rows. For a fixed nonzero `x`, this combination is uniformly distributed when `G` is uniform:
every word `y ∈ 𝔽₂ⁿ` is hit by a `2⁻ⁿ` fraction of the matrices
(`Cslib.Code.card_filter_vecMul_eq_mul_two_pow`), since `G ↦ x ᵥ* G` is additive and onto (the
matrix whose row `i` is `y`, for some `i` with `x i = 1`, is sent to `y`), so its fibers have
equal size (`AddMonoidHom.card_fiber_eq_of_mem_range`). A union bound
over the `2ᵏ - 1` nonzero messages and the entropy bound on the volume of a Hamming ball then
give Goldreich's Proposition E.1 (`Cslib.Code.one_sub_inv_two_pow_lt_card_filter_le_hammingDist`):
if `2 d ≤ n` and `k + t ≤ n (1 - H₂(d / n))`, a uniformly random generating matrix yields a code
of distance at least `d` with probability greater than `1 - 2⁻ᵗ`.

## Main results

* `Cslib.Code.card_filter_vecMul_eq_mul_two_pow`: a fixed nonzero combination of the rows of a
  uniform matrix is uniform.
* `Cslib.Code.one_sub_inv_two_pow_lt_card_filter_le_hammingDist`: Goldreich, Proposition E.1.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008],
  Proposition E.1 (draft `r6.pdf`, Appendix E, PDF p. 96, printed p. 604).
-/

public section

namespace Cslib.Code

open Finset Matrix Real

/-- **A nonzero combination of the rows of a uniform matrix is uniform**: for a nonzero
`x ∈ 𝔽₂ᵏ` and any `y ∈ 𝔽₂ⁿ`, exactly a `2⁻ⁿ` fraction of the `k`-by-`n` matrices `G` satisfy
`x ᵥ* G = y`. -/
theorem card_filter_vecMul_eq_mul_two_pow {k n : ℕ} {x : Fin k → ZMod 2} (hx : x ≠ 0)
    (y : Fin n → ZMod 2) :
    #{G : Matrix (Fin k) (Fin n) (ZMod 2) | x ᵥ* G = y} * 2 ^ n = 2 ^ (k * n) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi1 : x i = 1 := (show ∀ z : ZMod 2, z ≠ 0 → z = 1 by decide) _ hi
  -- The matrix whose row `i` is `z` contributes `z` to the combination.
  have hrow (z : Fin n → ZMod 2) : x ᵥ* (of fun r j => if r = i then z j else 0) = z := by
    funext j
    simp [vecMul, dotProduct, hi1]
  have hfiber (z : Fin n → ZMod 2) :
      #{G : Matrix (Fin k) (Fin n) (ZMod 2) | x ᵥ* G = z} =
        #{G : Matrix (Fin k) (Fin n) (ZMod 2) | x ᵥ* G = 0} :=
    AddMonoidHom.card_fiber_eq_of_mem_range (vecMulBilin (ZMod 2) (ZMod 2) x :
      Matrix (Fin k) (Fin n) (ZMod 2) →ₗ[ZMod 2] _) ⟨_, hrow z⟩ ⟨_, hrow 0⟩
  have hsum := card_eq_sum_card_fiberwise (s := (univ : Finset (Matrix (Fin k) (Fin n) (ZMod 2))))
    (t := univ) (f := fun G => x ᵥ* G) fun _ _ => mem_univ _
  simp only [hfiber, sum_const, card_univ, smul_eq_mul] at hsum
  simpa [hfiber y, ZMod.card, ← pow_mul, mul_comm] using
    show _ = Fintype.card (Fin k → Fin n → ZMod 2) from hsum.symm

/-- **The distance of random linear codes** [Goldreich, Proposition E.1][Goldreich2008]. If
`2 d ≤ n` and `k + t ≤ n (1 - H₂(d / n))`, where `H₂(δ) = Real.binEntropy δ / Real.log 2` is the
binary entropy in bits, then a uniformly random `k`-by-`n` generating matrix `G` over `𝔽₂`
yields a code of distance at least `d` (every two messages are encoded `d` positions apart)
with probability greater than `1 - 2⁻ᵗ`.

The source states the hypothesis for large `k` as `n ≥ max(2d, (k + t) / (1 - H₂(d / n)))`;
this theorem holds at every `k` where the hypothesis does, so it implies the eventual statement.
The quotient is multiplied out because `1 - H₂(1 / 2) = 0`, where the source's bound is infinite
(and Lean's quotient would be `0`). -/
theorem one_sub_inv_two_pow_lt_card_filter_le_hammingDist {k n d t : ℕ} (hd : 2 * d ≤ n)
    (h : (k + t : ℝ) ≤ n * (1 - binEntropy (d / n) / log 2)) :
    1 - (1 / 2 : ℝ) ^ t <
      #{G : Matrix (Fin k) (Fin n) (ZMod 2) | ∀ x y, x ≠ y → d ≤ hammingDist (x ᵥ* G) (y ᵥ* G)} /
        Fintype.card (Matrix (Fin k) (Fin n) (ZMod 2)) := by
  classical
  set good : Finset (Matrix (Fin k) (Fin n) (ZMod 2)) :=
    {G | ∀ x y, x ≠ y → d ≤ hammingDist (x ᵥ* G) (y ᵥ* G)}
  set B : Finset (Fin n → ZMod 2) := {y | hammingNorm y < d}
  set X : Finset (Fin k → ZMod 2) := {x | x ≠ 0}
  have hcard : Fintype.card (Matrix (Fin k) (Fin n) (ZMod 2)) = 2 ^ (k * n) := by
    change Fintype.card (Fin k → Fin n → ZMod 2) = _
    simp [ZMod.card, ← pow_mul, mul_comm]
  -- A bad matrix sends some nonzero message to a light word.
  have hbad : goodᶜ ⊆ X.biUnion fun x => B.biUnion fun y =>
      {G : Matrix (Fin k) (Fin n) (ZMod 2) | x ᵥ* G = y} := by
    intro G hG
    simp only [good, compl_filter, mem_filter, mem_univ, true_and, not_forall, not_le] at hG
    obtain ⟨x, y, hxy, hlt⟩ := hG
    rw [hammingDist_eq_hammingNorm, neg_add_eq_sub, ← sub_vecMul] at hlt
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, X, B]
    exact ⟨y - x, sub_ne_zero.2 hxy.symm, _, hlt, rfl⟩
  have hbadcard : #goodᶜ * 2 ^ n ≤ #X * #B * 2 ^ (k * n) := by
    refine (Nat.mul_le_mul_right _ ((card_le_card hbad).trans card_biUnion_le)).trans ?_
    rw [sum_mul]
    refine (sum_le_sum fun x hx => Nat.mul_le_mul_right _ card_biUnion_le).trans ?_
    rw [sum_congr rfl fun x hx => by
      rw [sum_mul, sum_congr rfl fun y _ =>
        card_filter_vecMul_eq_mul_two_pow (mem_filter.1 hx).2 y]]
    simp [mul_assoc]
  have hX : (#X : ℝ) + 1 = 2 ^ k := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin k → ZMod 2)))
      fun x => x ≠ 0
    simp only [not_not, filter_eq', mem_univ, ite_true, card_singleton, card_univ,
      Fintype.card_fun, ZMod.card, Fintype.card_fin] at h
    exact_mod_cast h
  -- The ratio of bad matrices, as a real number.
  have hsplit : (#good : ℝ) = 2 ^ (k * n) - #goodᶜ := by
    have := card_compl_add_card good
    rw [hcard] at this
    cast_linarith [this]
  have hpos : (0 : ℝ) < 2 ^ (k * n) := by positivity
  -- The light words: none if `d = 0`, and at most `2 ^ (n H₂(d / n))` otherwise.
  have hlight : (#X : ℝ) * #B < 2 ^ n * (1 / 2) ^ t := by
    rcases Nat.eq_zero_or_pos d with rfl | hd₀
    · simp [show B = ∅ by simp [B]]
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hα₀ : (0 : ℝ) ≤ d / n := by positivity
    have hα : (d / n : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hnR]
      cast_linarith [hd]
    have hsub : B ⊆ ({y | hammingDist 0 y ≤ d - 1} : Finset (Fin n → ZMod 2)) := fun y hy => by
      simp only [B, mem_filter, mem_univ, true_and, hammingDist_zero_left] at hy ⊢
      omega
    have hvol := card_filter_hammingDist_le_le_exp_mul_qaryEntropy (β := fun _ : Fin n => ZMod 2)
      (q := 2) (fun _ => ZMod.card 2) 0 (r := d - 1) (α := d / n) (by norm_num; linarith)
      (by
        rw [Fintype.card_fin, div_mul_cancel₀ _ hnR.ne']
        exact_mod_cast Nat.sub_le d 1)
    rw [Fintype.card_fin, qaryEntropy_two] at hvol
    have hB : (#B : ℝ) ≤ exp (n * binEntropy (d / n)) :=
      (by exact_mod_cast card_le_card hsub : (#B : ℝ) ≤ _).trans hvol
    have hB₁ : (1 : ℝ) ≤ #B := by exact_mod_cast card_pos.2 ⟨0, by simp [B, hd₀]⟩
    have hlog : 0 < log 2 := log_pos one_lt_two
    have hexp : (2 : ℝ) ^ k * exp (n * binEntropy (d / n)) ≤ 2 ^ n * (1 / 2) ^ t := by
      rw [← rpow_natCast, ← rpow_natCast, ← rpow_natCast, ← exp_log two_pos, ← exp_mul,
        ← exp_mul, ← exp_add, one_div, ← exp_neg, ← exp_mul, ← exp_add, exp_le_exp]
      have e : (n : ℝ) * (1 - binEntropy (d / n) / log 2) * log 2 =
          n * log 2 - n * binEntropy (d / n) := by field_simp
      linarith [mul_le_mul_of_nonneg_right h hlog.le]
    calc (#X : ℝ) * #B < (#X + 1) * #B := by nlinarith
      _ = 2 ^ k * #B := by rw [hX]
      _ ≤ 2 ^ k * exp (n * binEntropy (d / n)) := by gcongr
      _ ≤ 2 ^ n * (1 / 2) ^ t := hexp
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat, lt_div_iff₀ hpos, hsplit]
  have : (#goodᶜ : ℝ) < 2 ^ (k * n) * (1 / 2) ^ t := by
    refine lt_of_mul_lt_mul_right (a := 2 ^ n) ?_ (by positivity)
    calc (#goodᶜ : ℝ) * 2 ^ n ≤ #X * #B * 2 ^ (k * n) := by exact_mod_cast hbadcard
      _ < 2 ^ n * (1 / 2) ^ t * 2 ^ (k * n) := by gcongr
      _ = 2 ^ (k * n) * (1 / 2) ^ t * 2 ^ n := by ring
  nlinarith

end Cslib.Code

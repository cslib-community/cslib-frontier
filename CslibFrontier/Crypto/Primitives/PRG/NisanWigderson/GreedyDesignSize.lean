/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.Derandomization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Data.Nat.Factorial

/-!
# Size of the greedy design under the parameters of Arora and Barak

Arora and Barak [Lemma 16.18][AroraBarak07] build an `(ℓ, n, d)`-design (Definition 16.17: blocks
of `n` elements of `[ℓ]`, two of them sharing at most `d`) with `2 ^ (d / 10)` blocks, for
`n > d` and `ℓ > 10 n² / d`, by the greedy algorithm `Cslib.Crypto.PRG.NisanWigderson.greedyMasks`
that scans all subsets of `[ℓ]`. Their proof that the greedy algorithm does not get stuck is
probabilistic. Here the size follows from the counting bound
`Cslib.Crypto.PRG.NisanWigderson.choose_le_length_greedyMasks_mul`,
`C(ℓ, d + 1) ≤ |greedy| · C(n, d + 1)²`. With `k = d + 1`, `C(n, k) ≤ n ^ k / k!`,
`C(ℓ, k) ≥ (ℓ - d) ^ k / k!` and `k ^ k ≤ 3 ^ k k!` (`Nat.pow_self_le_three_pow_mul_factorial`),
and `6 n² ≤ (ℓ - d) k` follows from `10 n² < ℓ d` and `d < n`. Hence the greedy design has at least
`2 ^ (d + 1)` blocks (`two_pow_succ_le_length_greedyMasks`), more than the `2 ^ (d / 10)` of the
lemma (`natCeil_rpow_le_length_greedyMasks`). The running time `2 ^ O(ℓ)` of the lemma is not
stated here.

The hypothesis `ℓ > 10 n² / d` is stated as `10 n² < ℓ d`, which is the same for `d > 0` and is
false for `d = 0`, where the source's quotient is undefined. The number `2 ^ (d / 10)` of blocks is
a real number; the design `Cslib.Crypto.PRG.NisanWigderson.Design.greedy` takes the first
`⌈2 ^ (d / 10)⌉` greedy blocks.

## Main results

* `Cslib.Crypto.PRG.NisanWigderson.two_pow_succ_le_length_greedyMasks`: at least `2 ^ (d + 1)`
  blocks.
* `Cslib.Crypto.PRG.NisanWigderson.natCeil_rpow_le_length_greedyMasks`: at least
  `⌈2 ^ (d / 10)⌉` blocks, the size half of Arora–Barak Lemma 16.18.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07]
-/

public section

namespace Cslib.Crypto.PRG.NisanWigderson

open Nat

/-- **The greedy design is large under the parameters of Arora and Barak.** If `d < n` and
`10 n² < ℓ d` (that is, `ℓ > 10 n² / d`), the greedy design of blocks of `n` positions of `[ℓ]`
sharing at most `d` of them has at least `2 ^ (d + 1)` blocks. -/
theorem two_pow_succ_le_length_greedyMasks {ℓ n d : ℕ} (hdn : d < n) (hℓ : 10 * n ^ 2 < ℓ * d) :
    2 ^ (d + 1) ≤ (greedyMasks ℓ n d).length := by
  set k := d + 1
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at hℓ
    · exact hd
  have hdℓ : 10 * d < ℓ := by
    by_contra h
    push Not at h
    have : ℓ * d ≤ 10 * d * d := Nat.mul_le_mul_right d h
    nlinarith
  have hnℓ : n ≤ ℓ := by nlinarith
  have hkey : 6 * n ^ 2 ≤ (ℓ - d) * k := by
    have h1 : (ℓ - d) * d ≤ (ℓ - d) * k := Nat.mul_le_mul_left _ (Nat.le_succ d)
    have h2 : (ℓ - d) * d + d * d = ℓ * d := by
      rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
    nlinarith
  -- `n ^ (2k) 6 ^ k ≤ (ℓ - d) ^ k k ^ k ≤ (ℓ - d) ^ k 3 ^ k k!`.
  have hpow : 2 ^ k * n ^ (2 * k) * 3 ^ k ≤ (ℓ - d) ^ k * k ! * 3 ^ k := by
    calc 2 ^ k * n ^ (2 * k) * 3 ^ k = (6 * n ^ 2) ^ k := by
          rw [mul_pow, pow_mul, show (6 : ℕ) = 2 * 3 by rfl, mul_pow]
          ring
      _ ≤ ((ℓ - d) * k) ^ k := Nat.pow_le_pow_left hkey k
      _ = (ℓ - d) ^ k * k ^ k := mul_pow _ _ _
      _ ≤ (ℓ - d) ^ k * (3 ^ k * k !) :=
          Nat.mul_le_mul_left _ (Nat.pow_self_le_three_pow_mul_factorial k)
      _ = (ℓ - d) ^ k * k ! * 3 ^ k := by ring
  have hpow' : 2 ^ k * n ^ (2 * k) ≤ (ℓ - d) ^ k * k ! :=
    Nat.le_of_mul_le_mul_right hpow (by positivity)
  -- `C(n, k) k! ≤ n ^ k` and `(ℓ - d) ^ k ≤ C(ℓ, k) k!`.
  have hn : n.choose k * k ! ≤ n ^ k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have hl : (ℓ - d) ^ k ≤ ℓ.choose k * k ! := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    have := Nat.pow_sub_le_descFactorial ℓ k
    rwa [show ℓ + 1 - k = ℓ - d by omega] at this
  have hchoose : 2 ^ k * n.choose k ^ 2 ≤ ℓ.choose k := by
    refine Nat.le_of_mul_le_mul_right (c := k ! * k !) ?_ (by positivity)
    calc 2 ^ k * n.choose k ^ 2 * (k ! * k !) = 2 ^ k * (n.choose k * k !) ^ 2 := by ring
      _ ≤ 2 ^ k * (n ^ k) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)
      _ = 2 ^ k * n ^ (2 * k) := by ring
      _ ≤ (ℓ - d) ^ k * k ! := hpow'
      _ ≤ ℓ.choose k * k ! * k ! := Nat.mul_le_mul_right _ hl
      _ = ℓ.choose k * (k ! * k !) := by ring
  have hpos : 0 < n.choose k ^ 2 := pow_pos (Nat.choose_pos hdn) 2
  have h := choose_le_length_greedyMasks_mul (a := d) hdn hnℓ
  exact Nat.le_of_mul_le_mul_right (hchoose.trans h) hpos

/-- **Arora–Barak Lemma 16.18, size half** [Arora and Barak, Lemma 16.18][AroraBarak07]. This is
not the full lemma: it omits the running time `2 ^ O(ℓ)` of the algorithm. If `d < n` and
`10 n² < ℓ d` (that is, `ℓ > 10 n² / d`), the greedy algorithm finds at least `⌈2 ^ (d / 10)⌉`
blocks, so `Design.greedy ℓ n d ⌈2 ^ (d / 10)⌉ _` is an `(ℓ, n, d)`-design with
`⌈2 ^ (d / 10)⌉` blocks. -/
theorem natCeil_rpow_le_length_greedyMasks {ℓ n d : ℕ} (hdn : d < n)
    (hℓ : 10 * n ^ 2 < ℓ * d) :
    ⌈(2 : ℝ) ^ ((d : ℝ) / 10)⌉₊ ≤ (greedyMasks ℓ n d).length := by
  refine Nat.ceil_le.2 ?_
  have h := two_pow_succ_le_length_greedyMasks hdn hℓ
  have h' : ((2 ^ (d + 1) : ℕ) : ℝ) ≤ (greedyMasks ℓ n d).length := by exact_mod_cast h
  refine le_trans ?_ h'
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)

end Cslib.Crypto.PRG.NisanWigderson

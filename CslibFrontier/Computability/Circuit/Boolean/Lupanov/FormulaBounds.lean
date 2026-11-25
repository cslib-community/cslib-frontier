/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Defs
import Cslib.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Foundations.Data.Nat.Div
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parameter bounds for local coding of formulas

This module supplies the arithmetic step for the local-coding formula construction. The finite
bound separates `a` outer variables, `c` row variables, a power-of-two block of `d` variables,
and groups of at most `s` rows. It does not assert that a formula realizing this bound exists;
the native construction supplies that theorem.

For any fixed natural accuracy parameter `P`, sufficiently large input dimensions admit
parameters with total dimension `n` and
`P * Nat.log2 n * formulaBound a c d s ≤ (P + 1) * 2 ^ n`.
Take `p = Nat.log2 n`, `d = 2 ^ (p - 1)`, `c = 3 * p`, and
`s = p - p / (2 * (P + 1))`. The unused dimension goes into `a`. The loss in the leading
denominator and the exponentially smaller table terms fit into the two halves of the slack.

## Main definitions

* `Cslib.Circuits.Boolean.LupanovFormula.formulaBound`: the finite local-coding leaf bound.

## Main results

* `Cslib.Circuits.Boolean.LupanovFormula.eventually_exists_formulaBound_le`: parameter
  selection with asymptotically sharp natural-number budget.
-/

public section

namespace Cslib.Circuits.Boolean.LupanovFormula

open Filter

/-- The finite leaf bound from the local-coding construction. -/
@[expose] def formulaBound (a c d s : ℕ) : ℕ :=
  2 ^ a * (a + (2 ^ d / d) * (d ^ 2 + (2 ^ c / s + 1) * (2 ^ s * c * s + d)))

private theorem formulaBound_le {a c d s p h r n : ℕ}
    (hp : 0 < p) (hr : r + 1 = p) (hd : d = 2 ^ r) (hc : c = 3 * p)
    (hs : s + h = p) (hn : a + c + d = n) (ha : a ≤ 2 ^ (p + 1)) :
    formulaBound a c d s ≤
      2 ^ (a + d) * (2 ^ c / s) + (12 * p + 3) * 2 ^ (n - h) := by
  have hrle : r ≤ d := hd ▸ Nat.lt_two_pow_self.le
  have hdpos : 0 < d := hd ▸ Nat.two_pow_pos r
  have hhn : h ≤ n := by omega
  have hdiv : 2 ^ d / d = 2 ^ (d - r) := by
    rw [hd]
    exact Nat.pow_div (by simpa only [hd] using hrle) two_pos
  have hdivmul : (2 ^ d / d) * d = 2 ^ d := by
    calc (2 ^ d / d) * d = 2 ^ (d - r) * 2 ^ r := by rw [hdiv, hd]
      _ = 2 ^ d := by rw [← pow_add, Nat.sub_add_cancel hrle]
  have had : 2 ^ a * (2 ^ d / d) * d = 2 ^ (a + d) := by
    rw [mul_assoc, hdivmul, pow_add]
  have hA : 2 ^ a * a ≤ 2 ^ (n - h) := by
    calc 2 ^ a * a ≤ 2 ^ a * 2 ^ (p + 1) := Nat.mul_le_mul_left _ ha
      _ = 2 ^ (a + (p + 1)) := (pow_add ..).symm
      _ ≤ 2 ^ (n - h) := Nat.pow_le_pow_right two_pos (by omega)
  have hS : 2 ^ a * (2 ^ d / d) * d ^ 2 ≤ 2 ^ (n - h) := by
    calc 2 ^ a * (2 ^ d / d) * d ^ 2 = (2 ^ a * (2 ^ d / d) * d) * d := by ring
      _ = 2 ^ (a + d) * 2 ^ r := by rw [had, hd]
      _ = 2 ^ (a + d + r) := (pow_add ..).symm
      _ ≤ 2 ^ (n - h) := Nat.pow_le_pow_right two_pos (by omega)
  have hT : 2 ^ (a + d) ≤ 2 ^ (n - h) := Nat.pow_le_pow_right two_pos (by omega)
  have hsM : s ≤ 2 ^ c :=
    (by omega : s ≤ p).trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right two_pos (by omega : p ≤ c)))
  have hrows : (2 ^ c / s + 1) * s ≤ 2 * 2 ^ c := by
    have := Nat.div_mul_le_self (2 ^ c) s
    nlinarith only [this, hsM]
  have hpow : 2 ^ (a + (d - r) + s + c) ≤ 2 * 2 ^ (n - h) := by
    calc 2 ^ (a + (d - r) + s + c) ≤ 2 ^ ((n - h) + 1) :=
        Nat.pow_le_pow_right two_pos (by omega)
      _ = 2 * 2 ^ (n - h) := by rw [pow_succ, mul_comm]
  have hK : 2 ^ a * (2 ^ d / d) * (2 ^ c / s + 1) * (2 ^ s * c * s) ≤
      12 * p * 2 ^ (n - h) := by
    calc 2 ^ a * (2 ^ d / d) * (2 ^ c / s + 1) * (2 ^ s * c * s)
        = (2 ^ a * (2 ^ d / d) * 2 ^ s * c) * ((2 ^ c / s + 1) * s) := by ring
      _ ≤ (2 ^ a * (2 ^ d / d) * 2 ^ s * c) * (2 * 2 ^ c) :=
        Nat.mul_le_mul_left _ hrows
      _ = 2 * c * 2 ^ (a + (d - r) + s + c) := by
        rw [hdiv]
        simp only [pow_add]
        ring
      _ ≤ 2 * c * (2 * 2 ^ (n - h)) := Nat.mul_le_mul_left _ hpow
      _ = 12 * p * 2 ^ (n - h) := by rw [hc]; ring
  have hsplit : formulaBound a c d s =
      2 ^ a * a + 2 ^ a * (2 ^ d / d) * d ^ 2 +
      2 ^ a * (2 ^ d / d) * (2 ^ c / s + 1) * (2 ^ s * c * s) +
      2 ^ (a + d) * (2 ^ c / s) + 2 ^ (a + d) := by
    unfold formulaBound
    calc _ = 2 ^ a * a + 2 ^ a * (2 ^ d / d) * d ^ 2 +
        2 ^ a * (2 ^ d / d) * (2 ^ c / s + 1) * (2 ^ s * c * s) +
        (2 ^ a * (2 ^ d / d) * d) * (2 ^ c / s + 1) := by ring
      _ = _ := by rw [had]; ring
  rw [hsplit]
  nlinarith only [hA, hS, hT, hK]

/-- For all sufficiently large dimensions, parameters of the native local-coding construction
fit the stated natural-number budget. For positive `P`, this is the bound
`(1 + 1 / P) * 2 ^ n / Nat.log2 n`, expressed without division in `ℕ`.
This is an arithmetic parameter-selection theorem; realizability by formulas is supplied by
the separate finite construction. -/
theorem eventually_exists_formulaBound_le (P : ℕ) :
    ∀ᶠ n in atTop, ∃ a c r s : ℕ, 0 < s ∧ a + (c + 2 ^ r) = n ∧
      P * Nat.log2 n * formulaBound a c (2 ^ r) s ≤ (P + 1) * 2 ^ n := by
  let q := 2 * (P + 1)
  have hq : 0 < q := by dsimp only [q]; omega
  obtain ⟨H, hH⟩ := eventually_atTop.mp
    (Nat.eventually_mul_pow_le_pow (120 * P * q ^ 2) 2 Nat.one_lt_two)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (Nat.eventually_mul_pow_le_pow 6 1 Nat.one_lt_two)
  let N := max (q * (H + 1)) (max K 1)
  filter_upwards [eventually_ge_atTop (2 ^ N)] with n hn
  let p := Nat.log2 n
  have hpN : N ≤ p := by
    simpa only [p, Nat.log2_eq_log_two] using Nat.le_log_of_pow_le Nat.one_lt_two hn
  have hp : 0 < p := by dsimp only [N] at hpN; omega
  have hn0 : n ≠ 0 := ne_of_gt ((Nat.two_pow_pos N).trans_le hn)
  have hlo : 2 ^ p ≤ n := by
    simpa only [p, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hn0
  have hhi : n < 2 ^ (p + 1) := by
    simpa only [p, Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two n
  let r := p - 1
  let d := 2 ^ r
  let c := 3 * p
  let h := p / q
  let s := p - h
  let a := n - (c + d)
  have hr : r + 1 = p := by dsimp only [r]; omega
  have hhalf : 2 * d = 2 ^ p := by rw [← hr, pow_succ]; dsimp only [d]; omega
  have hdim : c + d ≤ n := by
    have : 6 * p ≤ 2 ^ p := by simpa only [pow_one] using hK p (by dsimp only [N] at hpN; omega)
    dsimp only [c]; omega
  have haeq : a + c + d = n := by dsimp only [a]; omega
  have hlow : q * h ≤ p := Nat.mul_div_le p q
  have hhigh : p < q * (h + 1) := Nat.lt_mul_div_succ p hq
  have hHh : H + 1 ≤ h := (Nat.le_div_iff_mul_le hq).mpr
    (mul_comm q (H + 1) ▸ (le_max_left (q * (H + 1)) (max K 1)).trans hpN)
  have hhp : h ≤ p := (Nat.le_mul_of_pos_left h hq).trans hlow
  have hsh : s + h = p := by dsimp only [s]; omega
  have hspos : 0 < s := by
    have : 2 * h ≤ p := (Nat.mul_le_mul_right h (by dsimp only [q]; omega)).trans hlow
    dsimp only [s]; omega
  have hmain : 2 * P * p ≤ (2 * P + 1) * s := by
    have hqh : (2 * P + 1) * h ≤ p :=
      (Nat.mul_le_mul_right h (by dsimp only [q]; omega : 2 * P + 1 ≤ q)).trans hlow
    nlinarith only [hsh, hqh]
  have hpoly : 2 * P * p * (12 * p + 3) ≤ 2 ^ h := by
    have hpq : p ≤ 2 * q * h := by nlinarith only [hhigh, hHh]
    calc 2 * P * p * (12 * p + 3) ≤ 2 * P * p * (15 * p) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 30 * P * p ^ 2 := by ring
      _ ≤ 30 * P * (2 * q * h) ^ 2 := by gcongr
      _ = 120 * P * q ^ 2 * h ^ 2 := by ring
      _ ≤ 2 ^ h := hH h (by omega)
  have hbound := formulaBound_le hp hr rfl rfl hsh haeq (by dsimp only [a]; omega)
  have hmainbound : 2 * P * p * (2 ^ (a + d) * (2 ^ c / s)) ≤
      (2 * P + 1) * 2 ^ n := by
    calc 2 * P * p * (2 ^ (a + d) * (2 ^ c / s)) =
        2 ^ (a + d) * ((2 * P * p) * (2 ^ c / s)) := by ring
      _ ≤ 2 ^ (a + d) * ((2 * P + 1) * 2 ^ c) :=
        Nat.mul_le_mul_left _ (Nat.mul_div_le_mul_of_le_mul (2 ^ c) hmain)
      _ = (2 * P + 1) * 2 ^ n := by
        have he : a + d + c = n := by omega
        rw [← he, pow_add]
        ring
  have herr : 2 * P * p * ((12 * p + 3) * 2 ^ (n - h)) ≤ 2 ^ n := by
    have hhn : h ≤ n := by omega
    calc 2 * P * p * ((12 * p + 3) * 2 ^ (n - h)) =
        (2 * P * p * (12 * p + 3)) * 2 ^ (n - h) := by ring
      _ ≤ 2 ^ h * 2 ^ (n - h) := Nat.mul_le_mul_right _ hpoly
      _ = 2 ^ n := by rw [← pow_add, Nat.add_sub_cancel' hhn]
  refine ⟨a, c, r, s, hspos, by omega, ?_⟩
  change P * p * formulaBound a c d s ≤ (P + 1) * 2 ^ n
  have htwice := Nat.mul_le_mul_left (2 * P * p) hbound
  nlinarith only [htwice, hmainbound, herr]

end Cslib.Circuits.Boolean.LupanovFormula

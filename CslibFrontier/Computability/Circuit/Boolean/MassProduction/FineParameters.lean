/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Basic
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parameters for fine mass production

Fix a rational copy exponent `γ = num / den < 1` and a slack `X`. Inputs of length `n` are split
into a prefix of `prefixWidth n ≈ (γ + (1 - γ) / (X + 1)) n` bits and a suffix of the remaining
`suffixWidth n ≥ (X / (X + 1)) (1 - γ) n` bits (`mul_le_suffixWidth`). The prefix is encoded in
line-parity codes on `K ^ dimension` over a field of `2 ^ fieldWidth n` elements, where
`fieldWidth n` is a multiple of `blockWidth` and `dimension ≤ 2 ^ blockWidth`. Batches have
`2 ^ depth n` requests, where `depth n = ⌊γ n⌋ + 1`.

The dimension is large enough that `(dimension - 2) * fieldWidth n` eventually exceeds
`depth n` by any fixed amount (`eventually_add_depth_le`): this is the projective-direction
budget of the scheduler. The field width leaves `3 log₂ (n + 2)` prefix bits unused
(`dimension_mul_fieldWidth_le`), so a single code copy is negligible against `2 ^ prefixWidth n`.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Fine.prefixWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.suffixWidth`: the input split.
* `Cslib.Circuits.Boolean.MassProduction.Fine.dimension`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.blockWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.blocks`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.fieldWidth`: the code geometry.
* `Cslib.Circuits.Boolean.MassProduction.Fine.depth`: the batch exponent.

## References

* Simplifies MassProduction/Nonuniform/{GeometricSlopes,BlockParameters,
  CoefficientParameters}.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Fine

open Filter

variable (num den X : ℕ)

/-- The prefix width `⌊n (den + num X) / ((X + 1) den)⌋`. -/
def prefixWidth (n : ℕ) : ℕ :=
  n * (den + num * X) / ((X + 1) * den)

/-- The suffix width, the rest of the input. -/
def suffixWidth (n : ℕ) : ℕ :=
  n - prefixWidth num den X n

/-- The dimension of the code geometry. -/
def dimension : ℕ :=
  4 * (den + num * X) + 3

/-- The block width of the field exponent: `dimension ≤ 2 ^ blockWidth`. -/
def blockWidth : ℕ :=
  Nat.clog 2 (dimension num den X)

/-- The number of blocks of the field exponent. -/
def blocks (n : ℕ) : ℕ :=
  (prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) / (dimension num den X * blockWidth num den X)

/-- The field has `2 ^ fieldWidth n` elements. -/
def fieldWidth (n : ℕ) : ℕ :=
  blockWidth num den X * blocks num den X n

/-- Batches have `2 ^ depth n` requests. -/
def depth (n : ℕ) : ℕ :=
  num * n / den + 1

variable {num den X}

/-- When `num ≤ den`, the prefix width is at most the input length `n`. -/
theorem prefixWidth_le (hnd : num ≤ den) (n : ℕ) : prefixWidth num den X n ≤ n := by
  rcases Nat.eq_zero_or_pos den with rfl | hden
  · simp [prefixWidth]
  apply Nat.div_le_of_le_mul
  calc n * (den + num * X) ≤ n * ((X + 1) * den) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = (X + 1) * den * n := by ring

/-- When `num ≤ den`, the prefix width and suffix width sum to `n`. -/
theorem prefixWidth_add_suffixWidth (hnd : num ≤ den) (n : ℕ) :
    prefixWidth num den X n + suffixWidth num den X n = n :=
  Nat.add_sub_of_le (prefixWidth_le hnd n)

/-- The suffix keeps at least a `X / (X + 1)` fraction of `(1 - γ) n` bits. -/
theorem mul_le_suffixWidth (hnd : num ≤ den) (n : ℕ) :
    X * (den - num) * n ≤ (X + 1) * den * suffixWidth num den X n := by
  have hp : (X + 1) * den * prefixWidth num den X n ≤ n * (den + num * X) := Nat.mul_div_le _ _
  obtain ⟨e, rfl⟩ : ∃ e, den = num + e := ⟨den - num, by omega⟩
  rw [Nat.add_sub_cancel_left, suffixWidth, Nat.mul_sub]
  have h1 : (X + 1) * (num + e) * n = n * (num + e + num * X) + X * e * n := by ring
  omega

private theorem three_le_dimension : 3 ≤ dimension num den X := Nat.le_add_left 3 _

/-- The code dimension is at most `2 ^ blockWidth`. -/
theorem dimension_le_two_pow_blockWidth : dimension num den X ≤ 2 ^ blockWidth num den X :=
  Nat.le_pow_clog (by norm_num) _

/-- The block width is positive. -/
theorem blockWidth_pos : 0 < blockWidth num den X :=
  Nat.clog_pos one_lt_two (Nat.lt_of_lt_of_le (by norm_num) three_le_dimension)

/-- The code points use all but `3 log₂ (n + 2)` of the prefix bits. -/
theorem dimension_mul_fieldWidth_le (n : ℕ) :
    dimension num den X * fieldWidth num den X n + 3 * Nat.log 2 (n + 2) ≤
      prefixWidth num den X n ∨ fieldWidth num den X n = 0 := by
  by_cases h : 3 * Nat.log 2 (n + 2) ≤ prefixWidth num den X n
  · left
    have := Nat.div_mul_le_self (prefixWidth num den X n - 3 * Nat.log 2 (n + 2))
      (dimension num den X * blockWidth num den X)
    unfold fieldWidth blocks
    calc dimension num den X * (blockWidth num den X *
          ((prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) /
            (dimension num den X * blockWidth num den X))) + 3 * Nat.log 2 (n + 2)
        = (prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) /
            (dimension num den X * blockWidth num den X) *
            (dimension num den X * blockWidth num den X) + 3 * Nat.log 2 (n + 2) := by ring
      _ ≤ prefixWidth num den X n := by omega
  · exact Or.inr (by simp [fieldWidth, blocks, Nat.sub_eq_zero_of_le (not_le.mp h).le])

/-- The scheduler budget: `(dimension - 2) * fieldWidth n` eventually exceeds `depth n` by any
fixed amount. -/
theorem eventually_add_depth_le (hnd : num < den) (c : ℕ) :
    ∀ᶠ n in atTop, c + depth num den n ≤ (dimension num den X - 2) * fieldWidth num den X n := by
  set a := den + num * X with ha
  set ℓ := dimension num den X with hℓ
  set h := blockWidth num den X with hh
  set m := (X + 1) * den with hm
  have hℓa : ℓ = 4 * a + 3 := rfl
  have hhpos : 0 < h := blockWidth_pos
  have hmpos : 0 < m := Nat.mul_pos (by omega) (by omega)
  filter_upwards [Nat.eventually_add_mul_log_add_le (ℓ * m * c + ℓ * (X + 1) * den +
      (4 * a + 1) * (m + m * ℓ * h)) (3 * (4 * a + 1) * m) 2 one_lt_two] with n hn
  set p := prefixWidth num den X n with hp
  set L := Nat.log 2 (n + 2) with hL
  set F := fieldWidth num den X n with hF
  set D := depth num den n with hD
  -- Floor bounds.
  have F1 : n * a < m * (p + 1) := Nat.lt_mul_div_succ _ hmpos
  have F2 : p < ℓ * F + ℓ * h + 3 * L := by
    have := Nat.lt_mul_div_succ (p - 3 * L) (Nat.mul_pos (by omega : 0 < ℓ) hhpos)
    rw [hF, fieldWidth, blocks, ← hp, ← hL, ← hℓ, ← hh]
    have e : ℓ * h * ((p - 3 * L) / (ℓ * h) + 1) =
        ℓ * (h * ((p - 3 * L) / (ℓ * h))) + ℓ * h := by ring
    omega
  have F3 : den * D ≤ num * n + den := by
    dsimp only [D, depth]; nlinarith [Nat.mul_div_le (num * n) den]
  have F4 : ℓ * ((X + 1) * num) + 2 * a + 3 ≤ (4 * a + 1) * a := by
    obtain ⟨e, rfl⟩ : ∃ e, den = num + 1 + e := ⟨den - num - 1, by omega⟩
    rw [ha]; nlinarith
  change c + D ≤ (4 * a + 1) * F
  -- Multiply the goal by `ℓ * m` and combine the scaled floor bounds.
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.mul_pos (by omega : 0 < ℓ) hmpos)
  have R1 : ℓ * m * (c + D) = ℓ * m * c + ℓ * (X + 1) * (den * D) := by rw [hm]; ring
  have R7 : n ≤ (2 * a + 3) * n := Nat.le_mul_of_pos_left n (by omega)
  linarith [Nat.mul_le_mul_left (ℓ * (X + 1)) F3, Nat.mul_le_mul_right n F4,
    Nat.mul_le_mul_left (4 * a + 1) F1.le, Nat.mul_le_mul_left ((4 * a + 1) * m) F2.le]

/-- The prefix grows at least linearly: `n < (X + 1) * (prefixWidth n + 1)`. -/
private theorem lt_mul_prefixWidth_add_one (hden : 0 < den) (n : ℕ) :
    n < (X + 1) * (prefixWidth num den X n + 1) := by
  have F1 : n * (den + num * X) < (X + 1) * den * (prefixWidth num den X n + 1) :=
    Nat.lt_mul_div_succ _ (Nat.mul_pos (Nat.succ_pos _) hden)
  exact Nat.lt_of_mul_lt_mul_left (a := den) (by nlinarith [Nat.zero_le (n * (num * X))])

/-- Eventually the field exponent has at least `c` blocks. -/
theorem eventually_le_blocks (hden : 0 < den) (c : ℕ) :
    ∀ᶠ n in atTop, c ≤ blocks num den X n := by
  have hℓh : 0 < dimension num den X * blockWidth num den X :=
    Nat.mul_pos (by have := three_le_dimension (num := num) (den := den) (X := X); omega)
      blockWidth_pos
  filter_upwards [Nat.eventually_add_mul_log_add_le ((X + 1) * (c * (dimension num den X *
      blockWidth num den X) + 1)) (3 * (X + 1)) 2 one_lt_two] with n hn
  have hp := lt_mul_prefixWidth_add_one (X := X) (num := num) hden n
  have := Nat.lt_of_mul_lt_mul_left (a := X + 1) (b := c * (dimension num den X *
    blockWidth num den X) + 1 + 3 * Nat.log 2 (n + 2)) (c := prefixWidth num den X n + 1)
    (by linarith)
  exact (Nat.le_div_iff_mul_le hℓh).mpr (by omega)

/-- Eventually the suffix has at least `c` bits, when the slack is positive. -/
theorem eventually_le_suffixWidth (hnd : num < den) (hX : 0 < X) (c : ℕ) :
    ∀ᶠ n in atTop, c ≤ suffixWidth num den X n := by
  filter_upwards [eventually_ge_atTop ((X + 1) * den * c)] with n hn
  exact Nat.le_of_mul_le_mul_left (hn.trans ((Nat.le_mul_of_pos_left n
    (Nat.mul_pos hX (by omega))).trans (mul_le_suffixWidth hnd.le n)))
    (Nat.mul_pos (by omega) (by omega))

/-- Slack `X = 16 (P + 1)` in three factors costs less than `1 / (2 P)`. -/
theorem two_mul_slack_le (P : ℕ) :
    2 * P * ((16 * (P + 1) + 1) ^ 2 * (16 * (P + 1) + 2)) ≤ (2 * P + 1) * (16 * (P + 1)) ^ 3 := by
  nlinarith [Nat.zero_le (P ^ 3), Nat.zero_le (P ^ 2), Nat.zero_le P, Nat.zero_le (P ^ 4)]

/-- The leading-coefficient arithmetic of fine mass production. -/
theorem mul_add_le_of_slack {P n w p den num R L O : ℕ}
    (hsuffix : 16 * (P + 1) * (den - num) * n ≤ (16 * (P + 1) + 1) * den * w)
    (hsplit : n = p + w)
    (hR : 16 * (P + 1) * R ≤ (16 * (P + 1) + 2) * 2 ^ p)
    (hL : 16 * (P + 1) * w * L ≤ (16 * (P + 1) + 1) * 2 ^ w)
    (hO : 2 * P * (den - num) * n * O ≤ den * 2 ^ n) :
    P * (den - num) * n * (R * L + O) ≤ (P + 1) * den * 2 ^ n := by
  set X := 16 * (P + 1) with hX
  have hXpos : 0 < X := by omega
  have main : 2 * P * ((den - num) * n * (R * L)) ≤ (2 * P + 1) * (den * 2 ^ n) := by
    have h3 : X ^ 3 * ((den - num) * n * (R * L)) ≤
        (X + 1) ^ 2 * (X + 2) * (den * 2 ^ n) := by
      calc X ^ 3 * ((den - num) * n * (R * L)) = (X * (den - num) * n) * (X * R) * L * X := by
            ring
        _ ≤ ((X + 1) * den * w) * ((X + 2) * 2 ^ p) * L * X := by gcongr
        _ = (X + 1) * den * (X + 2) * 2 ^ p * (X * w * L) := by ring
        _ ≤ (X + 1) * den * (X + 2) * 2 ^ p * ((X + 1) * 2 ^ w) := by gcongr
        _ = (X + 1) ^ 2 * (X + 2) * (den * 2 ^ n) := by rw [hsplit, pow_add]; ring
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < X ^ 3 by positivity)
    calc X ^ 3 * (2 * P * ((den - num) * n * (R * L)))
        = 2 * P * (X ^ 3 * ((den - num) * n * (R * L))) := by ring
      _ ≤ 2 * P * ((X + 1) ^ 2 * (X + 2) * (den * 2 ^ n)) := Nat.mul_le_mul_left _ h3
      _ = 2 * P * ((X + 1) ^ 2 * (X + 2)) * (den * 2 ^ n) := by ring
      _ ≤ (2 * P + 1) * X ^ 3 * (den * 2 ^ n) :=
          Nat.mul_le_mul_right _ (hX ▸ two_mul_slack_le P)
      _ = X ^ 3 * ((2 * P + 1) * (den * 2 ^ n)) := by ring
  have e1 : 2 * (P * (den - num) * n * (R * L + O)) =
      2 * P * ((den - num) * n * (R * L)) + 2 * P * (den - num) * n * O := by ring
  have e2 : 2 * ((P + 1) * den * 2 ^ n) = (2 * P + 1) * (den * 2 ^ n) + den * 2 ^ n := by ring
  omega

/-- The last, partly filled code copy is negligible: eventually
`X' * fieldWidth n * 2 ^ (dimension * fieldWidth n) ≤ 2 ^ prefixWidth n`. -/
theorem eventually_mul_two_pow_dimension_le (hnd : num ≤ den) (X' : ℕ) :
    ∀ᶠ n in atTop, X' * fieldWidth num den X n *
      2 ^ (dimension num den X * fieldWidth num den X n) ≤ 2 ^ prefixWidth num den X n := by
  filter_upwards [eventually_ge_atTop (8 * X')] with n hn
  rcases dimension_mul_fieldWidth_le (num := num) (den := den) (X := X) n with h | h
  · have hd := three_le_dimension (num := num) (den := den) (X := X)
    have hF : fieldWidth num den X n ≤ n :=
      (Nat.le_mul_of_pos_left _ (by omega : 0 < dimension num den X)).trans
        ((Nat.le_add_right _ _).trans (h.trans (prefixWidth_le hnd n)))
    have hlog : n + 2 < 2 * 2 ^ Nat.log 2 (n + 2) := by
      simpa only [pow_succ'] using Nat.lt_pow_succ_log_self one_lt_two (n + 2)
    have h8 : X' * fieldWidth num den X n ≤ 2 ^ (3 * Nat.log 2 (n + 2)) := by
      have hcube : (n + 2) ^ 3 ≤ 8 * 2 ^ (3 * Nat.log 2 (n + 2)) := by
        calc (n + 2) ^ 3 ≤ (2 * 2 ^ Nat.log 2 (n + 2)) ^ 3 := by gcongr
          _ = 8 * 2 ^ (3 * Nat.log 2 (n + 2)) := by rw [mul_pow, ← pow_mul]; ring_nf
      have : 8 * (X' * fieldWidth num den X n) ≤ (n + 2) ^ 3 := by
        calc 8 * (X' * fieldWidth num den X n) ≤ 8 * X' * n := by
              rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hF
          _ ≤ n * n := Nat.mul_le_mul_right _ hn
          _ ≤ (n + 2) ^ 3 := by nlinarith
      omega
    calc X' * fieldWidth num den X n * 2 ^ (dimension num den X * fieldWidth num den X n)
        ≤ 2 ^ (3 * Nat.log 2 (n + 2)) * 2 ^ (dimension num den X * fieldWidth num den X n) :=
          Nat.mul_le_mul_right _ h8
      _ = 2 ^ (dimension num den X * fieldWidth num den X n + 3 * Nat.log 2 (n + 2)) := by
          rw [← pow_add, add_comm]
      _ ≤ 2 ^ prefixWidth num den X n := Nat.pow_le_pow_right (by norm_num) h
  · simp [h]

/-- The prefix leaves a linear number of suffix bits: `n / ((X + 1) den) ≤ suffixWidth n`. -/
private theorem div_le_suffixWidth (hnd : num < den) (hX : 0 < X) (n : ℕ) :
    n / ((X + 1) * den) ≤ suffixWidth num den X n := by
  have h := mul_le_suffixWidth (X := X) hnd.le n
  have h1 : n ≤ X * (den - num) * n := Nat.le_mul_of_pos_left n (Nat.mul_pos hX (by omega))
  exact Nat.div_le_of_le_mul (by linarith)

/-- The scheduler exponent leaves a linear number of bits:
`n / dimension + depth n + fieldWidth n ≤ n + 1`. -/
theorem div_le_sub_depth_add_fieldWidth (hnd : num < den) (n : ℕ) :
    n / dimension num den X + depth num den n + fieldWidth num den X n ≤ n + 1 := by
  have hℓ3 : 3 ≤ dimension num den X := three_le_dimension
  -- `dimension * fieldWidth n ≤ n`.
  have hF : dimension num den X * fieldWidth num den X n ≤ n :=
    (dimension_mul_fieldWidth_le n).elim
      (fun h => (Nat.le_add_right _ _).trans (h.trans (prefixWidth_le hnd.le n)))
      fun h => by simp [h]
  -- `den * depth n ≤ num * n + den`.
  have hD : den * depth num den n ≤ num * n + den := by
    dsimp only [depth]; nlinarith [Nat.mul_div_le (num * n) den]
  -- `2 den + dimension * num ≤ dimension * den`, since `num < den`.
  have h4 : 2 * den + dimension num den X * num ≤ dimension num den X * den := by
    obtain ⟨e, rfl⟩ : ∃ e, den = num + 1 + e := ⟨den - num - 1, by omega⟩
    dsimp only [dimension]; nlinarith [Nat.zero_le (num * X * e)]
  have hq : dimension num den X * (n / dimension num den X) ≤ n := Nat.mul_div_le n _
  generalize dimension num den X = ℓ at *
  -- Multiply the claim by `den * ℓ`.
  refine Nat.le_of_mul_le_mul_left (c := den * ℓ) ?_ (Nat.mul_pos (by omega) (by omega))
  linarith [Nat.mul_le_mul_left den hq, Nat.mul_le_mul_left ℓ hD, Nat.mul_le_mul_left den hF,
    Nat.mul_le_mul_right n h4]

/-- **The overhead is negligible.** For any polynomial factor `A (n + 1) ^ E`, eventually
`2 P (den - num) n · A (2 ^ prefixWidth n + 2 ^ (depth n + fieldWidth n)) (n + 1) ^ E` is at most
`den 2 ^ n`. -/
theorem eventually_overhead_le (hnd : num < den) (hX : 0 < X) (P A E : ℕ) :
    ∀ᶠ n in atTop, 2 * P * (den - num) * n *
      (A * (2 ^ prefixWidth num den X n + 2 ^ (depth num den n + fieldWidth num den X n)) *
        (n + 1) ^ E) ≤ den * 2 ^ n := by
  have hℓ3 : 3 ≤ dimension num den X := three_le_dimension
  set c := (X + 1) * den * dimension num den X with hc
  have hcpos : 0 < c := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  filter_upwards [Nat.eventually_mul_add_one_pow_le_pow_div (8 * P * den * A) (E + 1) c one_lt_two
      hcpos]
    with n hn
  set p := prefixWidth num den X n
  set q := depth num den n + fieldWidth num den X n
  have hp : n / c + p ≤ n := by
    have h1 := div_le_suffixWidth (X := X) hnd hX n
    have h2 := prefixWidth_add_suffixWidth (X := X) hnd.le n
    have : n / c ≤ n / ((X + 1) * den) := Nat.div_le_div_left
      (Nat.le_mul_of_pos_right _ (by omega)) (Nat.mul_pos (by omega) (by omega))
    omega
  have hq : n / c + q ≤ n + 1 := by
    have h1 := div_le_sub_depth_add_fieldWidth (X := X) hnd n
    have : n / c ≤ n / dimension num den X := Nat.div_le_div_left
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))) (by omega)
    omega
  have hpow : 2 ^ p + 2 ^ q ≤ 4 * 2 ^ (n - n / c) := by
    have h1 : 2 ^ p ≤ 2 ^ (n - n / c) := Nat.pow_le_pow_right two_pos (by omega)
    have h2 : 2 ^ q ≤ 2 * 2 ^ (n - n / c) := by
      calc 2 ^ q ≤ 2 ^ (n - n / c + 1) := Nat.pow_le_pow_right two_pos (by omega)
        _ = 2 * 2 ^ (n - n / c) := by rw [pow_succ]; ring
    omega
  calc 2 * P * (den - num) * n * (A * (2 ^ p + 2 ^ q) * (n + 1) ^ E)
      ≤ 2 * P * den * (n + 1) * (A * (4 * 2 ^ (n - n / c)) * (n + 1) ^ E) := by gcongr <;> omega
    _ = 8 * P * den * A * (n + 1) ^ (E + 1) * 2 ^ (n - n / c) := by ring
    _ ≤ 2 ^ (n / c) * 2 ^ (n - n / c) := Nat.mul_le_mul_right _ hn
    _ = 2 ^ n := by rw [← pow_add, Nat.add_sub_of_le (Nat.div_le_self n c)]
    _ ≤ den * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)

end Cslib.Circuits.Boolean.MassProduction.Fine

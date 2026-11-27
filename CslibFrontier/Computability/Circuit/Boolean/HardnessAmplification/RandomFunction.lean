/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
public import CslibFrontier.Computability.Circuit.Boolean.CountingBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Circuit.Counting
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Tactic.LinarithCast

/-!
# Random functions are hard on average

Boolean functions that are hard on average for circuits of size `2 ^ (n / 10)` exist: for
every `n ≥ 400` some `f` has, in the sense of Arora and Barak's Definition 16.7, average-case
hardness `H_avg(f)(n) ≥ 2 ^ (n / 10)`. That is, for some natural number `S ≥ 2 ^ (n / 10)`,
every circuit of size at most `S` agrees with `f` on less than a `1 / 2 + 1 / S` fraction of the
inputs (`exists_forall_complexity_le_card_agree_lt`).

The proof is the counting argument the exercise asks for. A fixed `g` agrees with a uniformly
random `f` on a binomially distributed number of inputs, so by Hoeffding's inequality at most a
`exp (-2 · 2 ^ n / S ^ 2)` fraction of the functions `f` agree with `g` on at least
`2 ^ n / 2 + 2 ^ n / S` inputs (`card_filter_add_le_card_agree_le`). At most
`2 ^ O(S log (n + S))` functions have circuit complexity at most `S`
(`card_computableFunctions_le_two_pow`), and with `S ≈ 2 ^ (n / 10)` the union bound over them
leaves a function that none of them approximates.

## Main results

* `Cslib.Circuits.Boolean.card_filter_add_le_card_agree_le`: Hoeffding's inequality for the
  agreement of a uniformly random function with a fixed one.
* `Cslib.Circuits.Boolean.exists_forall_complexity_le_card_agree_lt`: Arora and Barak,
  Exercise 16.3.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07], Definition 16.7, Example 16.9 and Exercise 16.3
-/

public section

namespace Cslib.Circuits.Boolean

open Finset Real

variable {n : ℕ}

/-- **Agreement with a random function concentrates.** For a fixed `g` and `t ≥ 0`, at most an
`exp (-2 t² / 2 ^ n)` fraction of the functions `f` on `n` bits agree with `g` on at least
`2 ^ n / 2 + t` inputs. The agreement count is that of the false coordinates of `f xor g`, a
uniformly random bit string of length `2 ^ n`, so this is Hoeffding's inequality
(`Cslib.BitString.card_filter_le_card_filter_sub_half_le`). -/
theorem card_filter_add_le_card_agree_le (g : BooleanFunction n) {t : ℝ} (ht : 0 ≤ t) :
    (#{f : BooleanFunction n | (2 : ℝ) ^ n / 2 + t ≤ #{x | g x = f x}} : ℝ) ≤
      2 ^ 2 ^ n * exp (-(2 * t ^ 2 / 2 ^ n)) := by
  have h := BitString.card_filter_le_card_filter_sub_half_le (ι := BitString n) univ false ht
  let e : BooleanFunction n ≃ BooleanFunction n :=
    { toFun := fun f x => f x ^^ g x
      invFun := fun f x => f x ^^ g x
      left_inv := fun f => by funext x; simp
      right_inv := fun f => by funext x; simp }
  have hagree (f : BooleanFunction n) :
      #{x | g x = f x} = #{x ∈ (univ : Finset (BitString n)) | e f x = false} := by
    refine congrArg _ (filter_congr fun x _ => ?_)
    change g x = f x ↔ (f x ^^ g x) = false
    cases f x <;> cases g x <;> simp
  have hcard : #{f : BooleanFunction n | (2 : ℝ) ^ n / 2 + t ≤ #{x | g x = f x}} =
      #{y : BitString n → Bool |
        t ≤ (#{x ∈ (univ : Finset (BitString n)) | y x = false} : ℝ) -
          #(univ : Finset (BitString n)) / 2} := by
    refine card_equiv e fun f => ?_
    simp only [mem_filter, mem_univ, true_and, hagree, card_univ, BitString, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    constructor <;> intro h <;> linarith
  rw [hcard]
  simpa only [card_univ, BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using h

/-- The arithmetic of the union bound: for `16 ≤ S`, `9 S ^ 4 < 2 (S - 1) ^ 10`. -/
private theorem nine_mul_pow_four_lt {S : ℕ} (hS : 16 ≤ S) : 9 * S ^ 4 < 2 * (S - 1) ^ 10 := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ S)
  simp only [Nat.add_sub_cancel]
  have hT : 15 ≤ T := by omega
  have h4 : (T + 1) ^ 4 ≤ 16 * T ^ 4 := by
    calc (T + 1) ^ 4 ≤ (2 * T) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ = 16 * T ^ 4 := by ring
  have h6 : 15 ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left hT 6
  have hT4 : 0 < T ^ 4 := by positivity
  calc 9 * (T + 1) ^ 4 ≤ 9 * (16 * T ^ 4) := Nat.mul_le_mul_left 9 h4
    _ < 2 * (T ^ 4 * 15 ^ 6) := by nlinarith
    _ ≤ 2 * (T ^ 4 * T ^ 6) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h6)
    _ = 2 * T ^ 10 := by ring

/-- **Random functions are hard on average** [Arora and Barak, Exercise 16.3][AroraBarak07] (web
draft 2007-01-08, printed p. 318, PDF p. 334). For every `n ≥ 400` there is a Boolean function
`f` on `n` bits with average-case hardness `H_avg(f)(n) ≥ 2 ^ (n / 10)` in the sense of the
draft's Definition 16.7: for the natural number `S = ⌈2 ^ (n / 10)⌉`, every De Morgan circuit with
at most `S` gates agrees with `f` on less than a `1 / 2 + 1 / S` fraction of the inputs.

`H_avg(f)(n)` is the largest natural number `S` with this property, so `H_avg(f)(n) ≥ 2 ^ (n / 10)`
says exactly that some natural number `S ≥ 2 ^ (n / 10)` has it, as stated here. "Every large
enough `n`" is made explicit as `n ≥ 400`. Circuits of size at most `S` are the functions of
circuit complexity at most `S` (`Cslib.Circuits.complexity`, counting every AND, OR, NOT and
constant gate; the draft also counts input vertices, which only admits fewer circuits here). The
library's non-strict `IsAverageCaseHard f S` follows from the strict bound. -/
theorem exists_forall_complexity_le_card_agree_lt {n : ℕ} (hn : 400 ≤ n) :
    ∃ f : BooleanFunction n, ∃ S : ℕ, (2 : ℝ) ^ ((n : ℝ) / 10) ≤ S ∧
      ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ S →
        (#{x | g x = f x} : ℝ) / 2 ^ n < 1 / 2 + 1 / S := by
  classical
  set S := ⌈(2 : ℝ) ^ ((n : ℝ) / 10)⌉₊ with hS_def
  have hpos : (0 : ℝ) < 2 ^ ((n : ℝ) / 10) := by positivity
  have hS₁ : (2 : ℝ) ^ ((n : ℝ) / 10) ≤ S := Nat.le_ceil _
  have hS₂ : (S : ℝ) < 2 ^ ((n : ℝ) / 10) + 1 := Nat.ceil_lt_add_one hpos.le
  have hpow : ((2 : ℝ) ^ ((n : ℝ) / 10)) ^ 10 = 2 ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  -- `2 ^ n ≤ S ^ 10` and `(S - 1) ^ 10 < 2 ^ n`
  have hlow : 2 ^ n ≤ S ^ 10 := by exact_mod_cast hpow ▸ pow_le_pow_left₀ hpos.le hS₁ 10
  have hS1 : 1 ≤ S := Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hlow
  have hhigh : (S - 1) ^ 10 < 2 ^ n := by
    have h1 : ((S - 1 : ℕ) : ℝ) < 2 ^ ((n : ℝ) / 10) := by
      rw [Nat.cast_sub hS1, Nat.cast_one]
      linarith
    exact_mod_cast hpow ▸ pow_lt_pow_left₀ h1 (Nat.cast_nonneg _) (by norm_num : (10 : ℕ) ≠ 0)
  -- `n ≤ S` and `16 ≤ S`, from `n ^ 10 ≤ 2 ^ n` for `n ≥ 400`
  have hn10 : n ^ 10 ≤ 2 ^ n := Nat.pow_le_two_pow (by norm_num) (by omega)
  have hnS : n ≤ S := by
    by_contra h
    have := Nat.pow_lt_pow_left (by omega : S < n) (by norm_num : (10 : ℕ) ≠ 0)
    omega
  have hS16 : 16 ≤ S := by omega
  -- the union bound
  set L := computableFunctionsLogBound n S
  have hL : L ≤ 9 * S ^ 2 := by
    refine (computableFunctionsLogBound_le_poly n S).trans ?_
    nlinarith
  have hkey : 9 * S ^ 4 < 2 * 2 ^ n := (nine_mul_pow_four_lt hS16).trans_le (by omega)
  have hSR : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  set t : ℝ := 2 ^ n / S
  have ht : 0 ≤ t := by positivity
  have hexp : (2 : ℝ) ^ L * exp (-(2 * t ^ 2 / 2 ^ n)) < 1 := by
    have hLt : (L : ℝ) < 2 * t ^ 2 / 2 ^ n := by
      have heq : 2 * t ^ 2 / 2 ^ n = 2 * 2 ^ n / S ^ 2 := by
        simp only [t]
        field_simp
      rw [heq, lt_div_iff₀ (by positivity)]
      cast_nlinarith [hL, hkey]
    calc (2 : ℝ) ^ L * exp (-(2 * t ^ 2 / 2 ^ n))
        ≤ exp L * exp (-(2 * t ^ 2 / 2 ^ n)) := by
          gcongr
          calc (2 : ℝ) ^ L ≤ exp 1 ^ L := by
                gcongr
                exact (by norm_num : (2 : ℝ) ≤ 1 + 1).trans (add_one_le_exp 1)
            _ = exp L := by rw [← exp_nat_mul, mul_one]
      _ = exp (L - 2 * t ^ 2 / 2 ^ n) := by rw [← exp_add]; ring_nf
      _ < exp 0 := exp_lt_exp.mpr (by linarith)
      _ = 1 := exp_zero
  let bad : Finset (BooleanFunction n) := (computableFunctions n S).biUnion fun g =>
    {f | (2 : ℝ) ^ n / 2 + t ≤ #{x | g x = f x}}
  have hbad : (#bad : ℝ) < 2 ^ 2 ^ n := by
    have hU : #bad ≤ ∑ g ∈ computableFunctions n S,
        #{f : BooleanFunction n | (2 : ℝ) ^ n / 2 + t ≤ #{x | g x = f x}} := card_biUnion_le
    calc (#bad : ℝ) ≤ ∑ g ∈ computableFunctions n S,
          (#{f : BooleanFunction n | (2 : ℝ) ^ n / 2 + t ≤ #{x | g x = f x}} : ℝ) := by
          exact_mod_cast hU
      _ ≤ ∑ _g ∈ computableFunctions n S, (2 : ℝ) ^ 2 ^ n * exp (-(2 * t ^ 2 / 2 ^ n)) :=
          sum_le_sum fun g _ => card_filter_add_le_card_agree_le g ht
      _ = (#(computableFunctions n S) : ℝ) * (2 ^ 2 ^ n * exp (-(2 * t ^ 2 / 2 ^ n))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ L * (2 ^ 2 ^ n * exp (-(2 * t ^ 2 / 2 ^ n))) := by
          gcongr
          exact_mod_cast card_computableFunctions_le_two_pow n S
      _ = 2 ^ 2 ^ n * (2 ^ L * exp (-(2 * t ^ 2 / 2 ^ n))) := by ring
      _ < 2 ^ 2 ^ n * 1 := by gcongr
      _ = 2 ^ 2 ^ n := mul_one _
  have hlt : #bad < #(univ : Finset (BooleanFunction n)) := by
    have hc : #(univ : Finset (BooleanFunction n)) = 2 ^ 2 ^ n := by
      simp [BooleanFunction, BitString]
    rw [hc]
    exact_mod_cast hbad
  obtain ⟨f, -, hf⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨f, S, hS₁, fun g hg => ?_⟩
  have : (1 / 2 + 1 / (S : ℝ)) * 2 ^ n = 2 ^ n / 2 + t := by
    simp only [t]
    ring
  rw [div_lt_iff₀ hN, this]
  exact lt_of_not_ge fun h => hf (mem_biUnion.mpr
    ⟨g, mem_computableFunctions_iff_complexity_le.mpr hg, by simpa using h⟩)

end Cslib.Circuits.Boolean

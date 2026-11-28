/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Crypto.Primitives.PRG.Circuit
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Cslib.Computability.Circuit.Boolean.Complexity
import CslibFrontier.Computability.Circuit.Boolean.CountingBound
import CslibFrontier.Computability.Circuit.Boolean.Synthesis
import CslibFrontier.Computability.Circuit.Complexity
import CslibFrontier.Computability.Circuit.Counting
import CslibFrontier.Crypto.Primitives.PRG.Deterministic
import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Foundations.Data.BitString.WordCount
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Uniform

/-!
# Non-explicit pseudorandom generators

Arora and Barak's Exercise 16.2 asks for some `ε > 0` and a function `G` that meets every
condition of their Definition 16.2 of a `2 ^ (ε ℓ)`-pseudorandom generator except the running
time of `G`. Those conditions are: the output length `S(ℓ) = 2 ^ (ε ℓ)` is a monotone,
polynomial-time computable function, seeds of `ℓ` bits map to `S(ℓ)` bits, and for every `ℓ` no
circuit of size at most `S(ℓ) ^ 3` tells `G(U_ℓ)` from `U_{S(ℓ)}` with advantage `1 / 10` or more.
The hint takes a random function from `ℓ` bits to `2 ^ (ℓ / 10)` bits.

**Circuit size.** Tests are `Cslib.Crypto.PRG.IsCircuitTest`: deterministic tests of De Morgan
circuit complexity at most the budget, counting every AND, OR, NOT and constant gate but not the
inputs. The draft's Definition 6.1 counts all nodes, inputs included. So a circuit of source size
`s` has at most `s` gates here, the library admits at least the source's tests, and the
indistinguishability bound below implies the source's. A refutation needs the converse: its
witness must fit the source's count. The one-bit witness below does: at most four gates, plus the
`m` input nodes and possibly a separate output node, is at most `m + 5 ≤ m ^ 3` nodes for every
output length `m ≥ 2`.

As printed, the exercise is false at `ℓ = 1`. The draft rounds a real number used as a whole number
up (Conventions, p. 7), so `S(1) = ⌈2 ^ ε⌉ ≥ 2` for every `ε > 0`. A one-bit seed has only two
outputs, and one of the tests `y₀`, `y₁` or `y₀ xor y₁`, each with at most four gates, is constant
on both outputs and balanced on `{0,1} ^ S(1)`. Its advantage is `1 / 2`
(`exists_isCircuitTest_le_advantage_one`). If `0 ∈ ℕ`, `ℓ = 0` fails for the same reason.

The corrected endpoint is proved for its **length and indistinguishability properties**
(`exists_generator_advantage_lt`); polynomial-time computability of the length function, the one
remaining condition of Definition 16.2, is not proved here and stays open. The correction keeps
the hint's `ε = 1 / 10` and the draft's rounding, `S(ℓ) = ⌈2 ^ (ℓ / 10)⌉`, for every `ℓ ≥ 2`, and
sets `S(ℓ) = ℓ` for `ℓ ≤ 1`.
Where `S(ℓ) ≤ ℓ`, which holds for `2 ≤ ℓ ≤ 58`, the generator truncates its seed, and the output is
exactly uniform. Otherwise `S(ℓ) ≥ 60` and `(S(ℓ) - 1) ^ 10 < 2 ^ ℓ`. Then the hint's argument
works: for a fixed test, Hoeffding's inequality bounds the fraction of functions
`g : {0,1} ^ ℓ → {0,1} ^ S(ℓ)` on which it has advantage at least `1 / 10` by
`2 exp (-2 ^ ℓ / 50)`, and a union bound over the at most `2 ^ O(S(ℓ) ^ 6)` tests of circuit
complexity at most `S(ℓ) ^ 3` leaves a good `g`.

## Main results

* `Cslib.Complexity.exists_isCircuitTest_le_advantage_one`: the printed exercise fails at `ℓ = 1`
  for every `ε > 0`.
* `Cslib.Complexity.exists_generator_advantage_lt`: the length and indistinguishability properties
  of Arora and Barak's Exercise 16.2, corrected at `ℓ ≤ 1`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07], Conventions (p. 7), Definition 16.2 and Exercise 16.2
-/

public section

namespace Cslib.Complexity

open Finset Real Cslib.Crypto Cslib.Crypto.PRG Cslib.Circuits Cslib.Circuits.Boolean

/-! ### The printed exercise fails at `ℓ = 1` -/

/-- A test that flips with coordinate `i` accepts exactly half of the strings. -/
private theorem two_mul_card_filter_of_flip {m : ℕ} (i : Fin m) (T : BitString m → Bool)
    (hT : ∀ y, T (Function.update y i (!y i)) = !T y) :
    2 * #{y : BitString m | T y = true} = 2 ^ m := by
  let e : BitString m ≃ BitString m :=
    { toFun := fun y => Function.update y i (!y i)
      invFun := fun y => Function.update y i (!y i)
      left_inv := fun y => by simp
      right_inv := fun y => by simp }
  have hswap : #{y : BitString m | T y = true} = #{y : BitString m | ¬ T y = true} := by
    refine card_equiv e fun y => ?_
    simp only [mem_filter, mem_univ, true_and]
    change T y = true ↔ ¬ T (Function.update y i (!y i)) = true
    rw [hT]
    cases T y <;> simp
  have h := card_filter_add_card_filter_not (s := (univ : Finset (BitString m)))
    fun y => T y = true
  rw [← hswap, card_univ] at h
  simpa [two_mul, BitString] using h

/-- **The printed Exercise 16.2 fails at `ℓ = 1`.** Under the draft's rounding convention
(a real number used as a whole number is rounded up, p. 7), a `2 ^ (ε ℓ)`-pseudorandom generator
has `m = S(1) = ⌈2 ^ ε⌉ ≥ 2` output bits on one-bit seeds, for every `ε > 0`. For every `G`, some
test computed by a circuit with at most `m ^ 3` gates (in fact at most four) has advantage at
least `1 / 10` (in fact `1 / 2`) on seeds of length one, so the pseudorandomness condition of Arora
and Barak's Definition 16.2 [AroraBarak07] fails at `ℓ = 1`. (`PRG.wordFamily` reads the first
`S(1)` bits of `G z`, padded with zeros, so no output-length hypothesis is needed.)

The test is one of `y₀`, `y₁` and `y₀ xor y₁`. `IsCircuitTest` counts gates only, while the draft's
Definition 6.1 counts all nodes. The witness also fits the draft's budget: at most four gates plus
the `m` input nodes and, if counted separately, one output node make at most
`m + 5 ≤ m ^ 3` nodes, as `m ≥ 2`. -/
theorem exists_isCircuitTest_le_advantage_one {ε : ℝ} (hε : 0 < ε) (G : List Bool → List Bool) :
    ∃ adversary, IsCircuitTest (⌈(2 : ℝ) ^ (ε * ((1 : ℕ) : ℝ))⌉₊ ^ 3) adversary ∧
      1 / 10 ≤ (PRG.wordFamily G (fun ℓ => ⌈(2 : ℝ) ^ (ε * ℓ)⌉₊) 1).advantage adversary := by
  classical
  set m := ⌈(2 : ℝ) ^ (ε * ((1 : ℕ) : ℝ))⌉₊ with hm_def
  have hm2 : 2 ≤ m := by
    have h1 : (1 : ℝ) < 2 ^ (ε * ((1 : ℕ) : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (by push_cast; linarith)
    have := Nat.lt_ceil.mpr (show ((1 : ℕ) : ℝ) < 2 ^ (ε * ((1 : ℕ) : ℝ)) by exact_mod_cast h1)
    omega
  set g : BitString 1 → BitString m :=
    fun z => PRG.wordFamily G (fun ℓ => ⌈(2 : ℝ) ^ (ε * ℓ)⌉₊) 1 z with hg_def
  have hseed (z : BitString 1) : z = (fun _ => z 0) :=
    funext fun j => by rw [Subsingleton.elim j 0]
  set a := g fun _ => false
  set b := g fun _ => true
  have hgz (z : BitString 1) : g z = a ∨ g z = b := by
    rw [hseed z]
    cases z 0
    exacts [Or.inl rfl, Or.inr rfl]
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  -- a test of complexity at most four that is balanced and constant on `{a, b}`
  obtain ⟨T, hTc, hTi, hT, hTab⟩ : ∃ T : BitString m → Bool,
      complexity interpretation (single T) ≤ 4 ∧ ∃ i : Fin m,
      (∀ y, T (Function.update y i (!y i)) = !T y) ∧ T a = T b := by
    by_cases h0 : a i₀ = b i₀
    · refine ⟨fun y => y i₀, by simp, i₀, fun y => by simp, h0⟩
    by_cases h1 : a i₁ = b i₁
    · refine ⟨fun y => y i₁, by simp, i₁, fun y => by simp, h1⟩
    refine ⟨fun y => y i₀ ^^ y i₁, ?_, i₀, fun y => ?_, ?_⟩
    · simpa using complexity_xor_le (fun y : BitString m => y i₀) fun y => y i₁
    · simp [Function.update_of_ne hi.symm]
    · change (a i₀ ^^ a i₁) = (b i₀ ^^ b i₁)
      revert h0 h1
      cases a i₀ <;> cases b i₀ <;> cases a i₁ <;> cases b i₁ <;> simp
  refine ⟨fun y => _root_.PMF.pure (T y),
    ⟨T, hTc.trans ((Nat.pow_le_pow_left hm2 3).trans' (by norm_num)), rfl⟩, ?_⟩
  have hhalf := two_mul_card_filter_of_flip hTi T hT
  rw [Generator.advantage_pure_eq]
  have hconst (z : BitString 1) : T (g z) = T a := by
    rcases hgz z with h | h <;> rw [h]
    exact hTab.symm
  have hcount : (#{y : BitString m | T y = true} : ℝ) / 2 ^ m = 1 / 2 := by
    have h : (2 : ℝ) * #{y : BitString m | T y = true} = 2 ^ m := by exact_mod_cast hhalf
    field_simp
    linarith
  change 1 / 10 ≤ |(#{z : BitString 1 | T (g z) = true} : ℝ) / 2 ^ 1 -
    #{y : BitString m | T y = true} / 2 ^ m|
  rw [hcount]
  simp only [hconst]
  cases T a
  · simp
    norm_num [abs_of_neg]
  · simp [BitString]
    norm_num

/-! ### The corrected endpoint -/

/-- For `m ≤ ℓ`, truncating the seed gives exactly uniform outputs. -/
private theorem card_filter_ofList_take {ℓ m : ℕ} (hm : m ≤ ℓ) (T : BitString m → Bool) :
    (#{z : BitString ℓ | T (BitString.ofList m ((List.ofFn z).take m)) = true} : ℝ) / 2 ^ ℓ =
      #{y : BitString m | T y = true} / 2 ^ m := by
  have h := BitString.card_filter_take hm fun w => T (BitString.ofList m w) = true
  simp only [BitString.ofList_ofFn] at h
  change (#{z : Fin ℓ → Bool | T (BitString.ofList m ((List.ofFn z).take m)) = true} : ℝ) / 2 ^ ℓ =
    #{y : Fin m → Bool | T y = true} / 2 ^ m
  rw [h, Nat.cast_mul, Nat.cast_pow, ← pow_sub_mul_pow 2 hm]
  push_cast
  field_simp

/-- **Hoeffding for one test.** For a fixed test `T` on `m` bits, at most a
`2 exp (-2 ^ ℓ / 50)` fraction of the functions `g : {0,1} ^ ℓ → {0,1} ^ m` give `T` advantage at
least `1 / 10`, comparing the fraction of seeds `z` with `T (g z)` with the density of `T`. -/
private theorem card_filter_le_abs_sub_le (ℓ m : ℕ) (T : BitString m → Bool) :
    (#{g : BitString ℓ → BitString m | 1 / 10 ≤
        |(#{z | T (g z) = true} : ℝ) / 2 ^ ℓ - #{y | T y = true} / 2 ^ m|} : ℝ) ≤
      (2 ^ m) ^ 2 ^ ℓ * (2 * exp (-(2 ^ ℓ / 50))) := by
  classical
  have h := Probability.PMF.pi_sum_abs_sub_mean_ge_card_mul
    (fun _ : BitString ℓ => Probability.PMF.uniformOfFintype (BitString m))
    (fun _ y => if T y = true then (1 : ℝ) else 0)
    (fun _ y _ => by split_ifs <;> simp) (γ := 1 / 10) (by norm_num)
  rw [Probability.PMF.pi_uniformOfFintype, Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
    at h
  have hcardι : (Fintype.card (BitString ℓ) : ℝ) = 2 ^ ℓ := by simp [BitString]
  have hcardF : (Fintype.card (BitString ℓ → BitString m) : ℝ) = (2 ^ m) ^ 2 ^ ℓ := by
    simp [BitString]
  have hmean : ∑ _x : BitString ℓ, ∑ y : BitString m,
      ((Probability.PMF.uniformOfFintype (BitString m)) y).toReal *
        (if T y = true then (1 : ℝ) else 0) =
        2 ^ ℓ * (#{y : BitString m | T y = true} / 2 ^ m) := by
    simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      mul_ite, mul_one, mul_zero, sum_ite, sum_const_zero, add_zero, sum_const, card_univ,
      nsmul_eq_mul]
    simp [BitString]
    ring
  have hsum (g : BitString ℓ → BitString m) :
      ∑ x, (if T (g x) = true then (1 : ℝ) else 0) = #{z | T (g z) = true} := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
  have hsub : (#{g : BitString ℓ → BitString m | 1 / 10 ≤
      |(#{z | T (g z) = true} : ℝ) / 2 ^ ℓ - #{y | T y = true} / 2 ^ m|} : ℝ) ≤
      #{g : BitString ℓ → BitString m | g ∈ {outcome : BitString ℓ → BitString m |
        (Fintype.card (BitString ℓ) : ℝ) * (1 / 10) ≤
          |(∑ i, (if T (outcome i) = true then (1 : ℝ) else 0)) -
            ∑ i : BitString ℓ, ∑ a : BitString m,
              ((Probability.PMF.uniformOfFintype (BitString m)) a).toReal *
                (if T a = true then (1 : ℝ) else 0)|}} := by
    gcongr with g
    intro hg
    simp only [Set.mem_ofPred_eq, hsum, hmean, hcardι]
    have h2 : (0 : ℝ) < 2 ^ ℓ := by positivity
    have heq : (#{z | T (g z) = true} : ℝ) - 2 ^ ℓ * (#{y | T y = true} / 2 ^ m) =
        2 ^ ℓ * ((#{z | T (g z) = true} : ℝ) / 2 ^ ℓ - #{y | T y = true} / 2 ^ m) := by
      field_simp
    rw [heq, abs_mul, abs_of_pos h2]
    exact mul_le_mul_of_nonneg_left hg h2.le
  rw [hcardF, hcardι, div_le_iff₀ (by positivity)] at h
  have he : rexp (-2 * (2 ^ ℓ : ℝ) * (1 / 10) ^ 2) = rexp (-(2 ^ ℓ / 50)) := by
    congr 1
    ring
  rw [he] at h
  rw [hcardι] at hsub
  linarith

/-- The arithmetic of the union bound: for `60 ≤ m`, `50 (18 m ^ 6 + 1) ≤ (m - 1) ^ 10`. -/
private theorem fifty_mul_le_pow_ten {m : ℕ} (hm : 60 ≤ m) :
    50 * (18 * m ^ 6 + 1) ≤ (m - 1) ^ 10 := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ m)
  simp only [Nat.add_sub_cancel]
  have hT : 59 ≤ T := by omega
  have h6 : (T + 1) ^ 6 ≤ 64 * T ^ 6 := by
    calc (T + 1) ^ 6 ≤ (2 * T) ^ 6 := Nat.pow_le_pow_left (by omega) 6
      _ = 64 * T ^ 6 := by ring
  have h4 : 59 ^ 4 ≤ T ^ 4 := Nat.pow_le_pow_left hT 4
  have hT6 : 1 ≤ T ^ 6 := Nat.one_le_pow _ _ (by omega)
  calc 50 * (18 * (T + 1) ^ 6 + 1) ≤ 50 * (18 * (64 * T ^ 6) + T ^ 6) := by
        gcongr
    _ ≤ 59 ^ 4 * T ^ 6 := by nlinarith
    _ ≤ T ^ 4 * T ^ 6 := Nat.mul_le_mul_right _ h4
    _ = T ^ 10 := by ring

/-- **The random case.** For `60 ≤ m` and `(m - 1) ^ 10 < 2 ^ ℓ`, some
`g : {0,1} ^ ℓ → {0,1} ^ m` gives every test of circuit complexity at most `m ^ 3` advantage
below `1 / 10`. -/
private theorem exists_forall_complexity_le_abs_sub_lt {ℓ m : ℕ} (hm : 60 ≤ m)
    (hℓ : (m - 1) ^ 10 < 2 ^ ℓ) :
    ∃ g : BitString ℓ → BitString m, ∀ T : BitString m → Bool,
      complexity interpretation (single T) ≤ m ^ 3 →
        |(#{z | T (g z) = true} : ℝ) / 2 ^ ℓ - #{y | T y = true} / 2 ^ m| < 1 / 10 := by
  classical
  set L := computableFunctionsLogBound m (m ^ 3)
  have hL : L ≤ 18 * m ^ 6 := by
    refine (computableFunctionsLogBound_le_poly m (m ^ 3)).trans ?_
    have hm1 : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num) m
    have h1 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hkey : 50 * (L + 1) < 2 ^ ℓ := by
    have := fifty_mul_le_pow_ten hm
    omega
  have hexp : (2 : ℝ) ^ L * (2 * exp (-(2 ^ ℓ / 50))) < 1 := by
    have hkeyR : (50 : ℝ) * (L + 1) < 2 ^ ℓ := by exact_mod_cast hkey
    have h2 : (2 : ℝ) ^ (L + 1) ≤ exp (L + 1) := by
      calc (2 : ℝ) ^ (L + 1) ≤ exp 1 ^ (L + 1) := by
            gcongr
            exact (by norm_num : (2 : ℝ) ≤ 1 + 1).trans (add_one_le_exp 1)
        _ = exp (L + 1) := by rw [← exp_nat_mul, mul_one]; push_cast; ring_nf
    calc (2 : ℝ) ^ L * (2 * exp (-(2 ^ ℓ / 50))) = 2 ^ (L + 1) * exp (-(2 ^ ℓ / 50)) := by
          ring
      _ ≤ exp (L + 1) * exp (-(2 ^ ℓ / 50)) := by gcongr
      _ = exp (L + 1 - 2 ^ ℓ / 50) := by rw [← exp_add]; ring_nf
      _ < exp 0 := exp_lt_exp.mpr (by linarith)
      _ = 1 := exp_zero
  let bad : Finset (BitString ℓ → BitString m) := (computableFunctions m (m ^ 3)).biUnion
    fun T => {g | 1 / 10 ≤ |(#{z | T (g z) = true} : ℝ) / 2 ^ ℓ - #{y | T y = true} / 2 ^ m|}
  have hU : #bad ≤ ∑ T ∈ computableFunctions m (m ^ 3),
      #{g : BitString ℓ → BitString m |
        1 / 10 ≤ |(#{z | T (g z) = true} : ℝ) / 2 ^ ℓ - #{y | T y = true} / 2 ^ m|} :=
    card_biUnion_le
  have hbad : (#bad : ℝ) < (2 ^ m) ^ 2 ^ ℓ := by
    calc (#bad : ℝ) ≤ ∑ T ∈ computableFunctions m (m ^ 3),
          (#{g : BitString ℓ → BitString m |
            1 / 10 ≤ |(#{z | T (g z) = true} : ℝ) / 2 ^ ℓ - #{y | T y = true} / 2 ^ m|} : ℝ) := by
          exact_mod_cast hU
      _ ≤ ∑ _T ∈ computableFunctions m (m ^ 3),
          ((2 : ℝ) ^ m) ^ 2 ^ ℓ * (2 * exp (-(2 ^ ℓ / 50))) :=
          sum_le_sum fun T _ => card_filter_le_abs_sub_le ℓ m T
      _ = (#(computableFunctions m (m ^ 3)) : ℝ) *
          (((2 : ℝ) ^ m) ^ 2 ^ ℓ * (2 * exp (-(2 ^ ℓ / 50)))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ L * (((2 : ℝ) ^ m) ^ 2 ^ ℓ * (2 * exp (-(2 ^ ℓ / 50)))) := by
          gcongr
          exact_mod_cast card_computableFunctions_le_two_pow m (m ^ 3)
      _ = ((2 : ℝ) ^ m) ^ 2 ^ ℓ * ((2 : ℝ) ^ L * (2 * exp (-(2 ^ ℓ / 50)))) := by ring
      _ < ((2 : ℝ) ^ m) ^ 2 ^ ℓ * 1 := by gcongr
      _ = ((2 : ℝ) ^ m) ^ 2 ^ ℓ := mul_one _
  have hlt : #bad < #(univ : Finset (BitString ℓ → BitString m)) := by
    have hc : #(univ : Finset (BitString ℓ → BitString m)) = (2 ^ m) ^ 2 ^ ℓ := by
      simp [BitString]
    rw [hc]
    exact_mod_cast hbad
  obtain ⟨g, -, hg⟩ := exists_mem_notMem_of_card_lt_card hlt
  exact ⟨g, fun T hT => lt_of_not_ge fun h => hg (mem_biUnion.mpr
    ⟨T, mem_computableFunctions_iff_complexity_le.mpr hT, by simpa using h⟩)⟩

/-- The corrected output length: `⌈2 ^ (ℓ / 10)⌉` for `ℓ ≥ 2`, and `ℓ` for `ℓ ≤ 1`. -/
private noncomputable def outputLength (ℓ : ℕ) : ℕ :=
  if ℓ ≤ 1 then ℓ else ⌈(2 : ℝ) ^ ((ℓ : ℝ) / 10)⌉₊

private theorem monotone_outputLength : Monotone outputLength := by
  refine monotone_nat_of_le_succ fun ℓ => ?_
  rcases Nat.lt_or_ge ℓ 2 with h | h
  · interval_cases ℓ
    · simp [outputLength]
    · simp only [outputLength, le_refl, ↓reduceIte, show ¬ (1 + 1 ≤ 1) by omega, ↓reduceIte]
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · simp only [outputLength, show ¬ ℓ ≤ 1 by omega, show ¬ ℓ + 1 ≤ 1 by omega, ↓reduceIte]
    refine Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    push_cast
    linarith

/-- For every seed length there is a good map: truncation when `outputLength ℓ ≤ ℓ`, and the
random case otherwise. -/
private theorem exists_good_map (ℓ : ℕ) :
    ∃ g : BitString ℓ → BitString (outputLength ℓ), ∀ T : BitString (outputLength ℓ) → Bool,
      complexity interpretation (single T) ≤ outputLength ℓ ^ 3 →
        |(#{z | T (g z) = true} : ℝ) / 2 ^ ℓ -
          #{y | T y = true} / 2 ^ outputLength ℓ| < 1 / 10 := by
  set m := outputLength ℓ with hm_def
  by_cases hmℓ : m ≤ ℓ
  · refine ⟨fun z => BitString.ofList m ((List.ofFn z).take m), fun T _ => ?_⟩
    rw [card_filter_ofList_take hmℓ, sub_self, abs_zero]
    norm_num
  have hℓ2 : 2 ≤ ℓ := by
    by_contra h
    have : m = ℓ := by simp only [hm_def, outputLength, show ℓ ≤ 1 by omega, ↓reduceIte]
    omega
  have hm : m = ⌈(2 : ℝ) ^ ((ℓ : ℝ) / 10)⌉₊ := by
    simp only [hm_def, outputLength, show ¬ ℓ ≤ 1 by omega, ↓reduceIte]
  have hpos : (0 : ℝ) < 2 ^ ((ℓ : ℝ) / 10) := by positivity
  have hpow : ((2 : ℝ) ^ ((ℓ : ℝ) / 10)) ^ 10 = 2 ^ ℓ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hm1 : 1 ≤ m := by omega
  have hhigh : (m - 1) ^ 10 < 2 ^ ℓ := by
    have hlt : ((m - 1 : ℕ) : ℝ) < 2 ^ ((ℓ : ℝ) / 10) := by
      rw [Nat.cast_sub hm1, Nat.cast_one, hm]
      linarith [Nat.ceil_lt_add_one hpos.le]
    have h := pow_lt_pow_left₀ hlt (Nat.cast_nonneg _) (by norm_num : (10 : ℕ) ≠ 0)
    rw [hpow] at h
    exact_mod_cast h
  -- `ℓ ≤ m - 1`, so `(m - 1) ^ 10 < 2 ^ (m - 1)`, which forces `m - 1 ≥ 59`
  have hm60 : 60 ≤ m := by
    by_contra hcon
    have hle : ℓ ≤ m - 1 := by omega
    have h2 : (m - 1) ^ 10 < 2 ^ (m - 1) :=
      hhigh.trans_le (Nat.pow_le_pow_right (by norm_num) hle)
    have hk : 2 ≤ m - 1 := by omega
    have hk' : m - 1 ≤ 58 := by omega
    obtain ⟨k, hk_eq⟩ : ∃ k, k = m - 1 := ⟨_, rfl⟩
    rw [← hk_eq] at h2 hk hk'
    interval_cases k <;> norm_num at h2
  exact exists_forall_complexity_le_abs_sub_lt hm60 hhigh

/-- **Non-explicit pseudorandom generators: the length and indistinguishability properties**
[Arora and Barak, Exercise 16.2][AroraBarak07] (web draft 2007-01-08, printed p. 318, PDF p. 334),
corrected at seed lengths `ℓ ≤ 1`. With the hint's `ε = 1 / 10`, some `G : {0,1}* → {0,1}*` and
the output length `S(ℓ) = ⌈2 ^ (ℓ / 10)⌉` at every `ℓ ≥ 2`, rounded up as the draft's conventions
prescribe, and `S(ℓ) = ℓ` at `ℓ ≤ 1`, satisfy: `S` is monotone, `|G(z)| = S(|z|)` for every `z`,
and for every `ℓ` every De Morgan circuit with at most `S(ℓ) ^ 3` gates has advantage below
`1 / 10` in distinguishing `G(U_ℓ)` from `U_{S(ℓ)}`.

These are the fields `monotone`, `length_eq` and `pseudorandom` of
`Cslib.Complexity.ExponentialTimePRG`; its `time` field (the running time of `G`) is dropped, as
the exercise allows. **Not proved here:** Definition 16.2 also requires the length function `S` to
be polynomial-time computable, a condition the exercise keeps; `ExponentialTimePRG` omits it, and
this theorem does not certify it, so that condition of the corrected exercise remains open.
Circuit size counts gates, not inputs; the draft's Definition 6.1 counts all nodes, so the tests
admitted here include the source's and the bound implies the source's. The printed exercise asks
for `S(ℓ) = ⌈2 ^ (ε ℓ)⌉` at every `ℓ`, which fails at `ℓ = 1` for every `ε > 0`
(`exists_isCircuitTest_le_advantage_one`). The correction changes only `S(1)`, from `2` to `1`, and
`S(0)`, from `1` to `0` if `0 ∈ ℕ`. -/
theorem exists_generator_advantage_lt :
    ∃ S : ℕ → ℕ, ∃ G : List Bool → List Bool,
      (∀ ℓ, 2 ≤ ℓ → S ℓ = ⌈(2 : ℝ) ^ ((ℓ : ℝ) / 10)⌉₊) ∧ (∀ ℓ ≤ 1, S ℓ = ℓ) ∧
      Monotone S ∧ (∀ z, (G z).length = S z.length) ∧
      ∀ ℓ adversary, IsCircuitTest (S ℓ ^ 3) adversary →
        (PRG.wordFamily G S ℓ).advantage adversary < 1 / 10 := by
  choose g hg using exists_good_map
  let G : List Bool → List Bool := fun w => List.ofFn (g w.length (BitString.ofList w.length w))
  have hG (ℓ : ℕ) (z : BitString ℓ) : PRG.wordFamily G outputLength ℓ z = g ℓ z := by
    have key : ∀ (w : List Bool) (hw : w.length = ℓ),
        BitString.ofList (outputLength ℓ) (G w) = g ℓ (BitString.ofList ℓ w) := by
      rintro w rfl
      simp [G]
    change BitString.ofList (outputLength ℓ) (G (List.ofFn z)) = g ℓ z
    rw [key _ (List.length_ofFn), BitString.ofList_ofFn]
  refine ⟨outputLength, G, fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, monotone_outputLength,
    fun z => by simp [G], fun ℓ adversary hadv => ?_⟩
  · simp [outputLength, show ¬ ℓ ≤ 1 by omega]
  · simp [outputLength, hℓ]
  obtain ⟨T, hT, rfl⟩ := hadv
  rw [Generator.advantage_pure_eq]
  simp only [hG]
  exact hg ℓ T hT

end Cslib.Complexity

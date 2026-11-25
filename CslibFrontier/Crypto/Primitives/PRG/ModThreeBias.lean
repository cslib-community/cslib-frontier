/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.ReadOnceBias
public import CslibFrontier.Foundations.Data.BitString.Weight
import CslibFrontier.Crypto.Primitives.PRG.Deterministic
import Mathlib.Analysis.Complex.Norm

/-!
# A small-bias distribution that space-bounded automata distinguish

The uniform distribution on the words of `n` bits whose weight is divisible by three
(`Cslib.Crypto.PRG.modThreeWords`), presented as the output of the generator
`Cslib.Crypto.PRG.modThreeGenerator` whose seed is such a word, has exponentially small bias but
is distinguished from uniform by a read-once automaton with three states. This is
[Goldreich, Exercise 8.39][Goldreich2007DraftR4]: there exist `exp(-Ω(n))`-bias distributions on
`{0,1}^n` that are not `(2, 0.666)`-pseudorandom in the sense of Definition 8.20. It contrasts with
Exercise 8.38, by which space-bounded pseudorandomness does imply small bias
(`Cslib.Crypto.PRG.Generator.Secure.isSmallBias`).

**Bias.** The character `χ_S` summed against `z ^ weight x` over the cube factors coordinatewise
into `(1 - z) ^ |S| (1 + z) ^ (n - |S|)` (`Cslib.BitString.sum_chi_mul_pow_weight`). Averaging this
over the cube roots of unity `1, ω, ω²` filters the words whose weight is divisible by three. For
nonempty `S` the term of `1` vanishes, and `|1 - ω| = √3`, `|1 + ω| = 1`, so three times the sum of
`χ_S` over these words has absolute value at most `2 √3 ^ |S|`. For `S = ∅` the same identity counts
the words: `3 |A| = 2 ^ n ± 2` up to an error of absolute value at most `2`. Hence
`|bias S| (2 ^ n - 2) ≤ 2 √3 ^ |S|` (`Cslib.Crypto.PRG.abs_bias_modThreeGenerator_mul_le`), and
the distribution is `4 (√3 / 2) ^ n`-biased for every `n`
(`Cslib.Crypto.PRG.isSmallBias_modThreeGenerator`), with `√3 / 2 < 1`.

**Distinguisher.** Counting the ones modulo three is a read-once program with three states
(`Cslib.Crypto.PRG.isReadOnceTest_countMod`), so the test `Cslib.Crypto.PRG.modThreeTest` is
computed by an automaton of space `2`, with at most `2 ^ 2` states per layer as in Definition
8.20. It accepts every generated word, and a uniform word with probability at most
`1/3 + 2/(3 · 2 ^ n)`; its distinguishing gap is at least `2/3 - 2/(3 · 2 ^ n)`
(`Cslib.Crypto.PRG.two_div_three_sub_le_advantage_modThreeTest`), which exceeds `0.666` for
`n ≥ 10` (`Cslib.Crypto.PRG.not_secure_modThreeGenerator`).

**Source mapping.** Goldreich states the exercise for distributions on `{0,1}^n`; here the
distribution is the output distribution of a generator whose seed set is the set of words itself,
as `Cslib.Crypto.PRG.Generator.Secure` and `Cslib.BitString.IsSmallBias` are stated for output
distributions. Definition 8.20 calls an ensemble `(s, ε)`-pseudorandom if every non-uniform
automaton of space `s` has distinguishing gap at most `ε`; `IsReadOnceTest (2 ^ s)` gives these
automata as read-once programs with `2 ^ s` states per layer and time-dependent transitions, and
`Generator.Secure` bounds the gap by `ε`. The source's bias (Eq. (8.18)) is
`2 |Pr[⊕_S = 1] - 1/2|`, the absolute value of `Cslib.BitString.bias`. The exercise asks for the
bias bound `exp(-Ω(n))`; it is proved with the explicit base `√3 / 2`, and the distinguisher works
for every `n ≥ 10`, so the ensemble fails Definition 8.20 at every such length.

## Main definitions

* `Cslib.Crypto.PRG.modThreeWords`: the words whose weight is divisible by three.
* `Cslib.Crypto.PRG.modThreeGenerator`: the uniform distribution on them, as a generator.
* `Cslib.Crypto.PRG.modThreeTest`: the test whether the weight is divisible by three.

## Main results

* `Cslib.BitString.sum_chi_mul_pow_weight`: the weight enumerator of a character.
* `Cslib.Crypto.PRG.abs_bias_modThreeGenerator_mul_le`: the bias bound at each set.
* `Cslib.Crypto.PRG.isSmallBias_modThreeGenerator`: the distribution is `4 (√3/2)^n`-biased.
* `Cslib.Crypto.PRG.isReadOnceTest_modThreeTest`: the test is a read-once test of width `2 ^ 2`.
* `Cslib.Crypto.PRG.two_div_three_sub_le_advantage_modThreeTest`: its distinguishing gap.
* `Cslib.Crypto.PRG.not_secure_modThreeGenerator`: the distribution is not
  `(2, 0.666)`-pseudorandom for `n ≥ 10`.
* `Cslib.Crypto.PRG.exists_isSmallBias_not_secure`: Exercise 8.39.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of March 2007,
  Definition 8.20, Eq. (8.18), Exercises 8.38 and 8.39][Goldreich2007DraftR4]
-/

public section

namespace Cslib.BitString

open Finset

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- **The weight enumerator of a character**: summing the character `χ_S` against `z ^ weight x`
over the cube gives `(1 - z) ^ |S| (1 + z) ^ (n - |S|)`, one factor per coordinate. -/
theorem sum_chi_mul_pow_weight (S : Finset ι) (z : R) :
    ∑ x : ι → Bool, chi R S x * z ^ weight x =
      (1 - z) ^ #S * (1 + z) ^ (Fintype.card ι - #S) := by
  let g : ι → Bool → R := fun i b => (if i ∈ S then (-1 : R) ^ b.toNat else 1) * z ^ b.toNat
  have hg (i : ι) : ∑ b, g i b = if i ∈ S then 1 - z else 1 + z := by
    rw [Fintype.sum_bool]
    split_ifs with hi <;> simp [g, hi] <;> ring
  calc ∑ x : ι → Bool, chi R S x * z ^ weight x = ∑ x : ι → Bool, ∏ i, g i (x i) := by
        refine sum_congr rfl fun x _ => ?_
        rw [prod_mul_distrib, Fintype.prod_ite_mem,
          prod_pow_eq_pow_sum univ (fun i => (x i).toNat) z, weight_eq_sum_toNat]
        rfl
    _ = ∏ i, ∑ b, g i b := (Fintype.prod_sum g).symm
    _ = (1 - z) ^ #S * (1 + z) ^ (Fintype.card ι - #S) := by
        simp_rw [hg]
        rw [prod_ite, prod_const, prod_const, filter_univ_mem, filter_not, filter_univ_mem,
          ← compl_eq_univ_sdiff, card_compl]

end Cslib.BitString

namespace Cslib.Crypto.PRG

open Cslib.BitString Finset
open scoped NNReal

/-- The words of `n` bits whose weight, the number of ones, is divisible by three. -/
@[expose] def modThreeWords (n : ℕ) : Finset (Fin n → Bool) :=
  {x | weight x % 3 = 0}

theorem mem_modThreeWords {n : ℕ} {x : Fin n → Bool} : x ∈ modThreeWords n ↔ weight x % 3 = 0 := by
  simp [modThreeWords]

instance (n : ℕ) : Nonempty (modThreeWords n) :=
  ⟨⟨fun _ => false, mem_modThreeWords.2 (by simp [weight])⟩⟩

/-- The uniform distribution on the words of weight divisible by three, as a generator: its seed
is such a word and its output is the word itself
[Goldreich, Exercise 8.39][Goldreich2007DraftR4]. -/
@[expose] def modThreeGenerator (n : ℕ) : Generator (modThreeWords n) (Fin n → Bool) :=
  ⟨Subtype.val⟩

@[simp]
theorem modThreeGenerator_apply {n : ℕ} (x : modThreeWords n) : modThreeGenerator n x = x.val :=
  rfl

/-- The test whether the weight of a word is divisible by three. -/
noncomputable def modThreeTest (n : ℕ) : Adversary (Fin n → Bool) :=
  fun x => PMF.pure (decide (weight x % 3 = 0))

/-! ### The roots-of-unity filter -/

/-- The primitive cube root of unity `-1/2 + (√3/2) i`. -/
private noncomputable def cubeRoot : ℂ :=
  ⟨-1 / 2, √3 / 2⟩

private theorem sqrt_three_mul_self : √3 * √3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

private theorem cubeRoot_sq : cubeRoot ^ 2 = ⟨-1 / 2, -(√3 / 2)⟩ := by
  apply Complex.ext
  · simp only [cubeRoot, sq, Complex.mul_re]
    linear_combination (-1 / 4 : ℝ) * sqrt_three_mul_self
  · simp only [cubeRoot, sq, Complex.mul_im]
    ring

private theorem cubeRoot_pow_three : cubeRoot ^ 3 = 1 := by
  rw [pow_succ, cubeRoot_sq]
  apply Complex.ext
  · simp only [cubeRoot, Complex.mul_re, Complex.one_re]
    linear_combination (1 / 4 : ℝ) * sqrt_three_mul_self
  · simp only [cubeRoot, Complex.mul_im, Complex.one_im]
    ring

private theorem one_add_cubeRoot_add_sq : 1 + cubeRoot + cubeRoot ^ 2 = 0 := by
  rw [cubeRoot_sq]
  apply Complex.ext <;> simp only [cubeRoot, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.zero_re, Complex.zero_im] <;> ring

/-- `1 + ω ^ m + ω ^ (2 m)` is `3` when `3` divides `m` and `0` otherwise. -/
private theorem one_add_cubeRoot_pow_add (m : ℕ) :
    1 + cubeRoot ^ m + (cubeRoot ^ 2) ^ m = if m % 3 = 0 then 3 else 0 := by
  have h3 := cubeRoot_pow_three
  have hsum := one_add_cubeRoot_add_sq
  rw [← pow_mul, mul_comm, pow_mul, pow_eq_pow_mod m h3]
  have hr : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize m % 3 = r at hr ⊢
  interval_cases r
  · norm_num
  · simpa using hsum
  · have h4 : (cubeRoot ^ 2) ^ 2 = cubeRoot := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    simp only [h4, OfNat.ofNat_ne_zero, ite_false]
    linear_combination hsum

private theorem norm_mk_of_mul_self_add (a b c : ℝ) (h : a * a + b * b = c) :
    ‖(⟨a, b⟩ : ℂ)‖ = √c := by
  rw [Complex.norm_def, Complex.normSq_mk, h]

private theorem norm_one_sub_cubeRoot : ‖1 - cubeRoot‖ = √3 := by
  rw [show (1 : ℂ) - cubeRoot = ⟨3 / 2, -(√3 / 2)⟩ from Complex.ext (by norm_num [cubeRoot])
    (by norm_num [cubeRoot])]
  exact norm_mk_of_mul_self_add _ _ _ (by linear_combination (1 / 4 : ℝ) * sqrt_three_mul_self)

private theorem norm_one_add_cubeRoot : ‖1 + cubeRoot‖ = 1 := by
  rw [show (1 : ℂ) + cubeRoot = ⟨1 / 2, √3 / 2⟩ from Complex.ext (by norm_num [cubeRoot])
    (by norm_num [cubeRoot]), norm_mk_of_mul_self_add _ _ 1
    (by linear_combination (1 / 4 : ℝ) * sqrt_three_mul_self), Real.sqrt_one]

private theorem norm_one_sub_cubeRoot_sq : ‖1 - cubeRoot ^ 2‖ = √3 := by
  rw [cubeRoot_sq, show (1 : ℂ) - ⟨-1 / 2, -(√3 / 2)⟩ = ⟨3 / 2, √3 / 2⟩ from
    Complex.ext (by norm_num) (by norm_num)]
  exact norm_mk_of_mul_self_add _ _ _ (by linear_combination (1 / 4 : ℝ) * sqrt_three_mul_self)

private theorem norm_one_add_cubeRoot_sq : ‖1 + cubeRoot ^ 2‖ = 1 := by
  rw [cubeRoot_sq, show (1 : ℂ) + ⟨-1 / 2, -(√3 / 2)⟩ = ⟨1 / 2, -(√3 / 2)⟩ from
    Complex.ext (by norm_num) (by norm_num), norm_mk_of_mul_self_add _ _ 1
    (by linear_combination (1 / 4 : ℝ) * sqrt_three_mul_self), Real.sqrt_one]

/-- The roots-of-unity filter: three times the sum of a character over the words of weight
divisible by three is the sum of the weight enumerator at `1`, `ω` and `ω²`. -/
private theorem three_mul_sum_chi (n : ℕ) (S : Finset (Fin n)) :
    3 * ∑ x ∈ modThreeWords n, chi ℂ S x =
      (1 - 1) ^ #S * (1 + 1) ^ (n - #S) + (1 - cubeRoot) ^ #S * (1 + cubeRoot) ^ (n - #S) +
        (1 - cubeRoot ^ 2) ^ #S * (1 + cubeRoot ^ 2) ^ (n - #S) := by
  have h (z : ℂ) : ∑ x : Fin n → Bool, chi ℂ S x * z ^ weight x =
      (1 - z) ^ #S * (1 + z) ^ (n - #S) := by
    rw [sum_chi_mul_pow_weight, Fintype.card_fin]
  have hfac (u a b : ℂ) : u + u * a + u * b = u * (1 + a + b) := by ring
  rw [← h 1, ← h cubeRoot, ← h (cubeRoot ^ 2), ← sum_add_distrib, ← sum_add_distrib,
    modThreeWords, sum_filter, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [one_pow, mul_one, hfac, one_add_cubeRoot_pow_add]
  split_ifs <;> ring

/-- For a nonempty set `S`, three times the sum of `χ_S` over the words of weight divisible by
three has absolute value at most `2 √3 ^ |S|`. -/
private theorem norm_three_mul_sum_chi_le (n : ℕ) {S : Finset (Fin n)} (hS : S.Nonempty) :
    ‖3 * ∑ x ∈ modThreeWords n, chi ℂ S x‖ ≤ 2 * √3 ^ #S := by
  rw [three_mul_sum_chi, sub_self, zero_pow hS.card_pos.ne', zero_mul, zero_add]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  simp only [norm_mul, norm_pow, norm_one_sub_cubeRoot, norm_one_add_cubeRoot,
    norm_one_sub_cubeRoot_sq, norm_one_add_cubeRoot_sq, one_pow, mul_one]
  ring

/-- Three times the number of words of weight divisible by three is within `2` of `2 ^ n`. -/
theorem abs_three_mul_card_modThreeWords_sub_le (n : ℕ) :
    |3 * (#(modThreeWords n) : ℝ) - 2 ^ n| ≤ 2 := by
  have h := three_mul_sum_chi n ∅
  simp only [chi_empty, sum_const, card_empty, pow_zero, one_mul, Nat.sub_zero, nsmul_eq_mul,
    mul_one] at h
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    show ((3 * (#(modThreeWords n) : ℝ) - 2 ^ n : ℝ) : ℂ) =
      (1 + cubeRoot) ^ n + (1 + cubeRoot ^ 2) ^ n by
        push_cast; rw [h, one_add_one_eq_two]
        ring]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_pow, norm_pow, norm_one_add_cubeRoot, norm_one_add_cubeRoot_sq, one_pow]
  norm_num

/-! ### Small bias -/

/-- **The bias of the mod-3 distribution**: at every nonempty set `S` of coordinates,
`|bias S| (2 ^ n - 2) ≤ 2 √3 ^ |S|`. -/
theorem abs_bias_modThreeGenerator_mul_le (n : ℕ) {S : Finset (Fin n)} (hS : S.Nonempty) :
    |bias (modThreeGenerator n).outputDist S| * (2 ^ n - 2) ≤ 2 * √3 ^ #S := by
  set A := modThreeWords n
  have hA : (0 : ℝ) < #A := by
    exact_mod_cast card_pos.2 ⟨fun _ => false, mem_modThreeWords.2 (by simp [weight])⟩
  have hbias : bias (modThreeGenerator n).outputDist S * #A = ∑ x ∈ A, chi ℝ S x := by
    rw [Generator.outputDist, bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card,
      Fintype.card_coe, div_mul_cancel₀ _ hA.ne']
    exact sum_coe_sort A (chi ℝ S)
  have hsum := norm_three_mul_sum_chi_le n hS
  rw [← show ((3 * ∑ x ∈ A, chi ℝ S x : ℝ) : ℂ) = 3 * ∑ x ∈ A, chi ℂ S x by push_cast [chi]; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), ← hbias,
    abs_mul, abs_of_pos hA] at hsum
  exact (mul_le_mul_of_nonneg_left
    (by linarith [(abs_le.mp (abs_three_mul_card_modThreeWords_sub_le n)).1] : (2 : ℝ) ^ n - 2 ≤
      3 * #A) (abs_nonneg _)).trans (by linarith)

/-- `√3 / 2 < 1`: the bias bound `4 (√3 / 2) ^ n` decays exponentially. -/
theorem sqrt_three_div_two_lt_one : √3 / 2 < 1 := by
  nlinarith [Real.sqrt_nonneg 3, sqrt_three_mul_self]

/-- **The mod-3 distribution has exponentially small bias**: it is `4 (√3 / 2) ^ n`-biased for
every `n` [Goldreich, Exercise 8.39][Goldreich2007DraftR4]. -/
theorem isSmallBias_modThreeGenerator (n : ℕ) :
    IsSmallBias (4 * (√3 / 2) ^ n) (modThreeGenerator n).outputDist := by
  intro S hS
  have h3 : 1 ≤ √3 := by nlinarith [Real.sqrt_nonneg 3, sqrt_three_mul_self]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · refine (abs_bias_le_one _ _).trans ?_
    interval_cases n
    · norm_num
    · rw [pow_one]; linarith
  · have h4 : (2 : ℝ) ^ 2 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hpow : √3 ^ #S ≤ √3 ^ n := pow_le_pow_right₀ h3 (by simpa using card_le_univ S)
    have hmul : |bias (modThreeGenerator n).outputDist S| * 2 ^ n ≤
        |bias (modThreeGenerator n).outputDist S| * (2 * (2 ^ n - 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith [abs_bias_modThreeGenerator_mul_le n hS]

/-! ### The distinguisher -/

/-- The test whether the weight is divisible by three is a read-once test of width `2 ^ 2`: three
states count the ones modulo three. -/
theorem isReadOnceTest_modThreeTest (n : ℕ) : IsReadOnceTest (2 ^ 2) (modThreeTest n) :=
  isReadOnceTest_countMod (by norm_num) (by norm_num) univ 0

/-- **The gap of the mod-3 test**: it accepts every word of the distribution and a uniform word
with probability at most `1/3 + 2/(3 · 2 ^ n)`. -/
theorem two_div_three_sub_le_advantage_modThreeTest (n : ℕ) :
    2 / 3 - 2 / (3 * 2 ^ n) ≤ (modThreeGenerator n).advantage (modThreeTest n) := by
  have htest : modThreeTest n = fun y => PMF.pure (decide (weight y % 3 = 0)) := rfl
  have hreal : ((modThreeGenerator n).realExperiment (modThreeTest n) true).toReal = 1 := by
    rw [htest, Generator.toReal_realExperiment_pure,
      show ({z | decide (weight (modThreeGenerator n z) % 3 = 0) = true} :
        Finset (modThreeWords n)) = univ from
          eq_univ_of_forall fun z => by simp [mem_modThreeWords.1 z.2],
      dens_univ, NNRat.cast_one]
  have hideal : (Generator.idealExperiment (modThreeTest n) true).toReal =
      #(modThreeWords n) / 2 ^ n := by
    rw [htest, Generator.toReal_idealExperiment_pure, nnratCast_dens]
    simp [modThreeWords]
  rw [Generator.advantage, hreal, hideal]
  refine le_trans ?_ (le_abs_self _)
  have hnn : 0 ≤ (2 ^ n + 2 - 3 * (#(modThreeWords n) : ℝ)) / (3 * 2 ^ n) :=
    div_nonneg (by linarith [(abs_le.mp (abs_three_mul_card_modThreeWords_sub_le n)).2])
      (by positivity)
  have hkey : (1 - (#(modThreeWords n) : ℝ) / 2 ^ n) - (2 / 3 - 2 / (3 * 2 ^ n)) =
      (2 ^ n + 2 - 3 * #(modThreeWords n)) / (3 * 2 ^ n) := by
    field_simp; ring
  linarith

/-- **The mod-3 distribution is not `(2, 0.666)`-pseudorandom** for `n ≥ 10`: a read-once
automaton with `2 ^ 2` states per layer distinguishes it from uniform with gap above `0.666`
[Goldreich, Exercise 8.39][Goldreich2007DraftR4]. -/
theorem not_secure_modThreeGenerator {n : ℕ} (hn : 10 ≤ n) :
    ¬ (modThreeGenerator n).Secure (IsReadOnceTest (2 ^ 2)) (666 / 1000) := by
  intro h
  have h1 := h _ (isReadOnceTest_modThreeTest n)
  rw [show ((666 / 1000 : ℝ≥0) : ℝ) = 666 / 1000 by rw [NNReal.coe_div]; norm_num] at h1
  have h3 : (2 : ℝ) / (3 * 2 ^ n) ≤ 2 / (3 * 2 ^ 10) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr; norm_num)
  norm_num at h3
  linarith [two_div_three_sub_le_advantage_modThreeTest n]

/-- **Small bias does not imply space-bounded pseudorandomness** ([Goldreich, Exercise
8.39][Goldreich2007DraftR4]): for some `c < 1`, the uniform distributions on the words of weight
divisible by three are `4 c ^ n`-biased and, for every `n ≥ 10`, not `(2, 0.666)`-pseudorandom. -/
theorem exists_isSmallBias_not_secure :
    ∃ c : ℝ, c < 1 ∧ ∀ n, 10 ≤ n →
      IsSmallBias (4 * c ^ n) (modThreeGenerator n).outputDist ∧
        ¬ (modThreeGenerator n).Secure (IsReadOnceTest (2 ^ 2)) (666 / 1000) :=
  ⟨√3 / 2, sqrt_three_div_two_lt_one, fun n hn =>
    ⟨isSmallBias_modThreeGenerator n, not_secure_modThreeGenerator hn⟩⟩

end Cslib.Crypto.PRG

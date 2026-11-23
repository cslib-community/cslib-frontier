/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.HastadTest
public import CslibFrontier.Logics.Propositional.CSP.HastadTest
import Mathlib.Tactic.FinCases

/-! # Tests for the Odd BLR test and Håstad's test

Dictators pass the Odd BLR test, constants pass it with probability `1/2`, Håstad's test accepts
dictators with probability `1 - δ / 2` and large parities with probability close to `1/2`, and
functions without notable coordinates pass Håstad's test with probability close to `1/2`.
Håstad's test at a rational flip probability is a Max-E3-Lin instance and a
Dictator-vs.-No-Notables test (Theorem 7.42), the Odd BLR test and the empty test are not, and
its checks can be evaluated. -/

public section

namespace CslibFrontierTests.BooleanAnalysisHastadTest

open Cslib Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.CSP Finset
open scoped BigOperators

/-- Håstad's test accepts dictators with probability `1 - δ / 2`. -/
example (δ : ℝ) : hastadAcceptance δ (fun x : Fin 3 → Bool => x 1) = 1 - δ / 2 :=
  hastadAcceptance_dictator δ 1

/-- Dictators pass the Odd BLR test. -/
example : oddBlrAcceptance (fun x : Fin 3 → Bool => x 0) = 1 := by
  rw [← hastadAcceptance_zero, hastadAcceptance_dictator]
  norm_num

/-- The constant `true` passes the Odd BLR test with probability `1/2`. -/
example : oddBlrAcceptance (fun _ : Fin 2 → Bool => true) = 1 / 2 := by
  simp [oddBlrAcceptance_eq_sum, fourierCoeff_const]

/-- The parity of all five bits passes Håstad's test with probability
`1/2 + 1/2 (1 - δ) ^ 5`. -/
example (δ : ℝ) :
    hastadAcceptance δ (parityOn (univ : Finset (Fin 5))) = 1 / 2 + 1 / 2 * (1 - δ) ^ 5 := by
  rw [hastadAcceptance_parityOn, card_univ, Fintype.card_fin, ite_eq_left (by decide)]

/-- Even parities pass Håstad's test with probability `1/2`. -/
example (δ : ℝ) : hastadAcceptance δ (parityOn ({0, 1} : Finset (Fin 3))) = 1 / 2 := by
  rw [hastadAcceptance_parityOn, ite_eq_right (by decide)]

/-- The odd-level Fourier coefficients of NAND on two bits, read as signs: both singletons have
coefficient `-1/2`. -/
theorem fourierCoeff_nand_singleton (i : Fin 2) :
    fourierCoeff (fun x : Fin 2 → Bool => signVal (!(x 0 && x 1))) {i} = -1 / 2 := by
  have e (g : (Fin 2 → Bool) → ℝ) : ∑ x, g x = ∑ p : Bool × Bool, g ![p.1, p.2] :=
    Fintype.sum_equiv (piFinTwoEquiv fun _ => Bool) _ _ fun x => by
      congr 1; ext j; fin_cases j <;> rfl
  rw [fourierCoeff_eq_sum, e]
  fin_cases i <;> simp [chi_singleton, Fintype.sum_prod_type] <;> norm_num

/-- The odd levels of the cube on two bits are the two singletons. -/
theorem filter_odd_card_fin_two :
    (univ.filter fun S : Finset (Fin 2) => Odd #S) = {{0}, {1}} := by
  decide

/-- **Proposition 7.46 with `M = 0`**: the odd coefficients of NAND are negative, so the Odd BLR
test accepts it with probability at most `1/2`. -/
example : oddBlrAcceptance (fun x : Fin 2 → Bool => !(x 0 && x 1)) ≤ 1 / 2 + 1 / 2 * 0 := by
  refine oddBlrAcceptance_le_of_fourierCoeff_le le_rfl fun S hS => ?_
  have hS' : S ∈ ({{0}, {1}} : Finset (Finset (Fin 2))) := by
    rw [← filter_odd_card_fin_two]; exact mem_filter.2 ⟨mem_univ _, hS⟩
  rcases mem_insert.1 hS' with rfl | hS'
  · rw [fourierCoeff_nand_singleton]; norm_num
  · rw [mem_singleton.1 hS', fourierCoeff_nand_singleton]; norm_num

/-- **The Fourier formula (7.4)** for NAND on two bits: the odd levels are the two singletons, of
coefficient `-1/2`, so Håstad's test accepts with probability
`1/2 + 1/2 · 2 (1 - δ) (-1/2) ^ 3 = 1/2 - (1 - δ) / 8`; at `δ = 0` this is the direct count
`3/8` below. -/
example (δ : ℝ) :
    hastadAcceptance δ (fun x : Fin 2 → Bool => !(x 0 && x 1)) = 1 / 2 - (1 - δ) / 8 := by
  rw [hastadAcceptance_eq_sum, filter_odd_card_fin_two, sum_pair (by decide),
    fourierCoeff_nand_singleton, fourierCoeff_nand_singleton]
  simp only [card_singleton, pow_one]
  ring

/-- The NAND of two bits passes the Odd BLR test with probability `3/8`, although both its odd
coefficients are `-1/2`: the bound of Proposition 7.46 needs a nonnegative maximum. -/
example : oddBlrAcceptance (fun x : Fin 2 → Bool => !(x 0 && x 1)) = 3 / 8 ∧
    fourierCoeff (fun x : Fin 2 → Bool => signVal (!(x 0 && x 1))) {0} = -1 / 2 ∧
    fourierCoeff (fun x : Fin 2 → Bool => signVal (!(x 0 && x 1))) {1} = -1 / 2 := by
  refine ⟨?_, fourierCoeff_nand_singleton 0, fourierCoeff_nand_singleton 1⟩
  have e (g : (Fin 2 → Bool) → ℝ) : 𝔼 x, g x = 𝔼 p : Bool × Bool, g ![p.1, p.2] :=
    Fintype.expect_equiv (piFinTwoEquiv fun _ => Bool) _ _ fun x => by
      congr 1; ext i; fin_cases i <;> rfl
  have hadd (a b : Bool) : a + b = (a ^^ b) := rfl
  simp only [oddBlrAcceptance_def, e, Fintype.expect_eq_sum_div_card, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.card_prod, Fintype.card_bool]
  norm_num [Pi.add_apply, hadd]

/-- Håstad's test accepts NAND with probability at most one, here `1/2 - (2/3) / 8`. -/
example : hastadAcceptance (1 / 3) (fun x : Fin 2 → Bool => !(x 0 && x 1)) ≤ 1 :=
  hastadAcceptance_le_one (by norm_num) (by norm_num) _

/-- Unfolding the definitions: a constant passes Håstad's test with probability `1/2`, and so does
the constant `0` with values in `[-1, 1]`. -/
example (δ : ℝ) :
    hastadAcceptance δ (fun _ : Fin 2 → Bool => true) = 1 / 2 ∧
      hastadValue δ (fun _ : Fin 2 → Bool => (0 : ℝ)) = 1 / 2 := by
  constructor
  · simp [hastadAcceptance_def]
  · simp [hastadValue_def]

/-- A constant has no notable coordinates, so it passes Håstad's test with probability at most
`1/2 + 1/2 √ε` for every `0 ≤ ε ≤ δ`; in fact it passes with probability `1/2`. -/
example {ε : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ 1 / 2) :
    hastadAcceptance (1 / 2) (fun _ : Fin 3 → Bool => true) ≤ 1 / 2 + 1 / 2 * √ε :=
  hastadAcceptance_le_of_stableInfluence_le hε hεδ (by norm_num) fun i => by
    simp [stableInfluence_eq_sum, fourierCoeff_const, hε]

/-- No `(1/4, 1/4)`-notable coordinates means Håstad's test at `δ = 1/2` accepts with probability
at most `3/4`. -/
example {f : (Fin 4 → Bool) → Bool}
    (h : ∀ i, stableInfluence (1 - 1 / 4) i (fun x => signVal (f x)) ≤ 1 / 4) :
    hastadAcceptance (1 / 2) f ≤ 3 / 4 := by
  have := hastadAcceptance_le_of_stableInfluence_le (δ := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) h
  rw [show √(1 / 4 : ℝ) = 1 / 2 by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num] at this
  linarith

/-- (7.4) for a function with values in `[-1, 1]`: the constant `1/2`, each query a sign of mean
`1/2`, passes Håstad's test with probability `1/2`. -/
example (δ : ℝ) : hastadValue δ (fun _ : Fin 3 → Bool => (1 / 2 : ℝ)) = 1 / 2 := by
  simp [hastadValue_eq_sum, fourierCoeff_const]

/-- Theorem 7.42: Håstad's test flipping each bit with probability `1/4` is a
`(1/2, 3/4)`-Dictator-vs.-No-Notables test using the Max-E3-Lin predicates. -/
example : IsDictatorVsNoNotables e3LinArity paritySem (1 / 2) (3 / 4) (hastadTest 1 4) := by
  convert isDictatorVsNoNotables_hastadTest (a := 1) (q := 4) (by norm_num) (by norm_num) using 1
  norm_num

/-- Theorem 7.42 at an irrational `δ`: a rational flip probability below `δ` gives the test. -/
example : ∃ T : ∀ n : ℕ, CSP Bool (Fin n → Bool),
    IsDictatorVsNoNotables e3LinArity paritySem (1 / 2) (1 - 1 / (2 * √2)) T := by
  have h2 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine exists_isDictatorVsNoNotables_e3Lin (by positivity) ?_
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- In the test, dictators pass with probability exactly `1 - 1/4`. -/
example : (hastadTest 1 4 5).satFraction paritySem (fun x => x 2) = 3 / 4 := by
  rw [satFraction_hastadTest (by norm_num) (by norm_num), hastadAcceptance_dictator]
  norm_num

/-- The checks of the test are 3-variable linear equations. A check whose mask leaves bit `0`
alone is passed by the dictator of bit `0`, `x₀ + y₀ + (x₀ + y₀ + b) = b`, and one whose mask flips
bit `0` is failed by it. -/
example :
    hastadCheck 1 ![true, false] ![false, false] true (![3, 0] : Fin 2 → Fin 4) ∈
      hastadTest 1 4 2 ∧
    (hastadCheck 1 ![true, false] ![false, false] true (![3, 0] : Fin 2 → Fin 4)).eval paritySem
      (fun x => x 0) = true ∧
    (hastadCheck 1 ![true, false] ![false, false] true (![0, 3] : Fin 2 → Fin 4)).eval paritySem
      (fun x => x 0) = false :=
  ⟨mem_hastadTest.2 ⟨_, _, _, _, rfl⟩, by decide, by decide⟩

/-- Soundness is for functions with values in `[-1, 1]`: the constant `0`, every query a fair
coin, passes with probability `1/2`. -/
example (n : ℕ) : (hastadTest 1 4 n).expectedSatFraction paritySem (fun _ => 0) = 1 / 2 := by
  rw [expectedSatFraction_hastadTest (by norm_num) (by norm_num), hastadValue_eq_sum]
  simp [fourierCoeff]

/-- The definition is not trivial: the empty test passes every function, dictators included, with
probability `1`, so it meets completeness but no soundness bound. -/
example {α β : ℝ} : ¬ IsDictatorVsNoNotables e3LinArity paritySem α β fun _ => [] := by
  intro h
  obtain ⟨err, herr, hs⟩ := h.exists_error
  obtain ⟨ε, ⟨hε0, hε1⟩, herrε⟩ : ∃ ε ∈ Set.Ioo (0 : ℝ) 1, err ε < 1 - α :=
    (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos) (herr.eventually
      (gt_mem_nhds (sub_pos.2 (h.lt.trans_le h.le_one))))).exists
  have hb := hs ε hε0 hε1.le 1 one_pos (fun _ => 0) (fun _ => by simp) fun i => by
    simp [stableInfluence_eq_sum, fourierCoeff, hε0.le]
  rw [expectedSatFraction_nil] at hb
  linarith

/-- **Soundness fails without noise**: the Odd BLR test, Håstad's test with flip probability
`0 / 1`, is not an `(α, 1)`-Dictator-vs.-No-Notables test for any `α < 1`. The parity of `2 N + 1`
bits passes with probability one, yet once `(1 - ε) ^ N < ε` it has no `(ε, ε)`-notable
coordinates. This is why Håstad's test adds noise. -/
example {α : ℝ} (hα : α < 1) :
    ¬ IsDictatorVsNoNotables e3LinArity paritySem α 1 (hastadTest 0 1) := by
  intro h
  obtain ⟨err, herr, hs⟩ := h.exists_error_satFraction
  obtain ⟨ε, ⟨hε0, hε1⟩, herrε⟩ : ∃ ε ∈ Set.Ioo (0 : ℝ) 1, err ε < 1 - α :=
    (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
      (herr.eventually (gt_mem_nhds (sub_pos.2 hα)))).exists
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε0 (show 1 - ε < 1 by linarith)
  have hinf (i : Fin (2 * N + 1)) :
      stableInfluence (1 - ε) i (fun x => signVal (parityOn univ x)) ≤ ε := by
    rw [stableInfluence_eq_sum, sum_eq_single_of_mem univ (by simp) fun S _ hS => by
      simp [fourierCoeff_signVal_parityOn, hS]]
    simp only [fourierCoeff_signVal_parityOn, ite_true, one_pow, mul_one, card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
    calc (1 - ε) ^ (2 * N) ≤ (1 - ε) ^ N :=
          pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
      _ ≤ ε := hN.le
  have hb := hs ε hε0 hε1.le _ (by omega) _ hinf
  rw [satFraction_hastadTest (by norm_num) (by norm_num), hastadAcceptance_parityOn, card_univ,
    Fintype.card_fin, ite_eq_left (by simp)] at hb
  norm_num at hb
  linarith

/-- Every partial sum of the squared coefficients of a Boolean function is at most one; here the
odd-level weight of the AND of two bits. -/
example : ∑ S with Odd #S, fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0 && x 1)) S ^ 2 ≤ 1 :=
  sum_fourierCoeff_sq_signVal_le_one _ _

/-- One term of the stable influence: the parity of bits `0` and `1` has coefficient `1` on
`{0, 1}`, so its `1/2`-stable influence at bit `0` is at least `1/2`. -/
example :
    (1 / 2 : ℝ) ≤ stableInfluence (1 / 2) 0
      (fun x => signVal (parityOn ({0, 1} : Finset (Fin 3)) x)) := by
  have h := pow_mul_fourierCoeff_sq_le_stableInfluence (ρ := 1 / 2) (by norm_num)
    (show (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) by decide)
    (fun x => signVal (parityOn ({0, 1} : Finset (Fin 3)) x))
  rwa [fourierCoeff_signVal_parityOn, ite_eq_left rfl, one_pow, mul_one,
    show #({0, 1} : Finset (Fin 3)) - 1 = 1 by decide, pow_one] at h

/-! ### Functions with values in `[-1, 1]` -/

/-- A `[-1, 1]`-valued function has every partial Fourier weight and every coefficient at most
one: here half a dictator. -/
example :
    ∑ S with Odd #S, fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0) / 2) S ^ 2 ≤ 1 ∧
      |fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0) / 2) {0}| ≤ 1 := by
  have hg : ∀ x : Fin 3 → Bool, |signVal (x 0) / 2| ≤ 1 := fun x => by
    rw [abs_div, abs_signVal]; norm_num
  exact ⟨sum_fourierCoeff_sq_le_one_of_abs_le_one hg _, abs_fourierCoeff_le_one_of_abs_le_one hg _⟩

/-- At the signs of a dictator, `hastadValue` is the dictator's acceptance probability. -/
example (δ : ℝ) : hastadValue δ (fun x : Fin 3 → Bool => signVal (x 1)) = 1 - δ / 2 := by
  rw [← hastadAcceptance_eq_hastadValue, hastadAcceptance_dictator]

/-- Soundness and the trivial bound for a `[-1, 1]`-valued constant. -/
example {ε : ℝ} (hε : 0 ≤ ε) (hεδ : ε ≤ 1 / 2) :
    hastadValue (1 / 2) (fun _ : Fin 3 → Bool => (1 / 3 : ℝ)) ≤ 1 / 2 + 1 / 2 * √ε ∧
      hastadValue 2 (fun _ : Fin 3 → Bool => (1 / 3 : ℝ)) ≤ 1 := by
  have hg : ∀ _ : Fin 3 → Bool, |(1 / 3 : ℝ)| ≤ 1 := fun _ => by norm_num [abs_div]
  refine ⟨hastadValue_le_of_stableInfluence_le hε hεδ (by norm_num) hg fun i => by
    simp [stableInfluence_eq_sum, fourierCoeff_const, hε],
    hastadValue_le_one (by norm_num) le_rfl hg⟩

/-! ### Independent bits with given means -/

/-- With means `1/2` and `0`, the string `(true, false)` has probability
`(1 - 1/2)/2 · 1/2 = 1/8`; the weights are nonnegative and sum to one. -/
example :
    meanWeight (![1 / 2, 0] : Fin 2 → ℝ) ![true, false] = 1 / 8 ∧
      0 ≤ meanWeight (![1 / 2, 0] : Fin 2 → ℝ) ![true, false] ∧
      ∑ a, meanWeight (![1 / 2, 0] : Fin 2 → ℝ) a = 1 := by
  refine ⟨?_, meanWeight_nonneg (fun i => by fin_cases i <;> norm_num [abs_div]) _,
    sum_meanWeight _⟩
  rw [meanWeight_def, Fin.prod_univ_two]
  norm_num

/-- Means `±1` are a point mass, and equal means `1/2` are the Bernoulli mask of rate `1/4`. -/
example (a : Fin 3 → Bool) :
    meanWeight (fun i => signVal (![true, false, true] i)) ![true, false, true] = 1 ∧
      meanWeight (fun _ => (1 / 2 : ℝ)) a = bernoulliWeight (1 / 4) a := by
  refine ⟨by rw [meanWeight_signVal, ite_eq_left rfl], ?_⟩
  convert meanWeight_const (1 / 4) a using 3
  norm_num

/-- **Exercise 1.4**: the expectation of the parity of bits `0` and `1`, at means `1/2` and
`-1/3`, is its Fourier expansion at the means, `1/2 · (-1/3)`; the character has that
expectation directly. -/
example :
    ∑ a, meanWeight (![1 / 2, -1 / 3] : Fin 2 → ℝ) a * signVal (parityOn univ a) = -1 / 6 ∧
      ∑ a, meanWeight (![1 / 2, -1 / 3] : Fin 2 → ℝ) a * chi ℝ univ a = -1 / 6 := by
  constructor
  · rw [sum_meanWeight_mul_eq_sum_fourierCoeff, sum_eq_single univ
      (fun S _ hS => by rw [fourierCoeff_signVal_parityOn, ite_eq_right hS, zero_mul])
      (by simp), fourierCoeff_signVal_parityOn, ite_eq_left rfl, one_mul, Fin.prod_univ_two]
    norm_num
  · rw [sum_meanWeight_mul_chi, Fin.prod_univ_two]
    norm_num

/-- The `{0, 1}` coordinates: the indicator polynomial of `(true, false)` at the probabilities
`1/4, 1/2` of `true` is `1/8`, and the multilinear extension of the constant one is one. -/
example :
    MvPolynomial.eval (fun i => (1 - (![1 / 2, 0] : Fin 2 → ℝ) i) / 2)
        (indicatorPoly ![true, false]) = 1 / 8 ∧
      MvPolynomial.eval (fun i => (1 - (![1 / 2, 0] : Fin 2 → ℝ) i) / 2)
        (multilinearExtension fun _ => (1 : ℝ)) = 1 := by
  constructor
  · rw [← meanWeight_eq_eval_indicatorPoly, meanWeight_def, Fin.prod_univ_two]
    norm_num
  · rw [← sum_meanWeight_mul_eq_eval_multilinearExtension]
    simp [sum_meanWeight]

/-- A digit of `Fin 4` below `1` selects bit `0` with probability `1/4`. -/
example :
    𝔼 m : Fin 3 → Fin 4, (if decide ((m 0 : ℕ) < 1) then (1 : ℝ) else 0) = 1 / 4 := by
  have h := expect_fin_lt_eq_bernoulliAverage (ι := Fin 3) (q := 4) (a := 1) (by norm_num)
    (by norm_num) fun s => if s 0 then (1 : ℝ) else 0
  rw [bernoulliAverage_coordinate] at h
  exact h.trans (by norm_num)

/-! ### Values of assignments and randomized assignments -/

/-- An equation `x₀ + x₁ + x₂ = true` at means `1/2, 1/2, 1` holds with probability
`1/2 - 1/2 · 1/4 = 3/8`. With a repeated variable, `x₀ + x₀ + x₂ = false` at the same means is
read position by position, so it holds with probability `5/8`, not `1`. -/
example :
    (⟨true, [0, 1, 2]⟩ : Constraint Bool (Fin 3)).satProb paritySem ![1 / 2, 1 / 2, 1] = 3 / 8 ∧
      (⟨false, [0, 0, 2]⟩ : Constraint Bool (Fin 3)).satProb paritySem ![1 / 2, 1 / 2, 1] =
        5 / 8 := by
  constructor <;> rw [satProb_paritySem] <;> norm_num

/-- The same probability `3/8` through the Fourier expansion of the predicate (Exercise 7.20(c))
and through its `multilinearExtension`. -/
example :
    (∑ S, fourierCoeff (fun a : Fin 3 → Bool => if paritySem true (List.ofFn a) then (1 : ℝ) else 0)
      S * ∏ i ∈ S, (![1 / 2, 1 / 2, 1] : Fin 3 → ℝ) i) = 3 / 8 ∧
    MvPolynomial.eval (fun i : Fin 3 => (1 - (![1 / 2, 1 / 2, 1] : Fin 3 → ℝ) i) / 2)
      (multilinearExtension fun a : Fin 3 → Bool =>
        if paritySem true (List.ofFn a) then (1 : ℝ) else 0) = 3 / 8 := by
  have h := satProb_paritySem (![1 / 2, 1 / 2, 1] : Fin 3 → ℝ) true 0 1 2
  constructor
  · rw [Constraint.satProb_eq_sum_fourierCoeff] at h
    refine h.trans ?_
    norm_num
  · have h3 : (1 / 2 : ℝ) + 1 / 2 * (signVal true * (![1 / 2, 1 / 2, 1] : Fin 3 → ℝ) 0 *
        (![1 / 2, 1 / 2, 1] : Fin 3 → ℝ) 1 * (![1 / 2, 1 / 2, 1] : Fin 3 → ℝ) 2) = 3 / 8 := by
      norm_num
    rw [Constraint.satProb_eq_eval_multilinearExtension, h3] at h
    convert h using 3
    funext i
    fin_cases i <;> rfl

/-- A probability, `0 ≤ satProb ≤ 1`, for means in `[-1, 1]`; at the signs of an assignment it
is whether the assignment satisfies the constraint. -/
example (g : Fin 3 → ℝ) (hg : ∀ v, |g v| ≤ 1) :
    0 ≤ (⟨true, [0, 1, 2]⟩ : Constraint Bool (Fin 3)).satProb paritySem g ∧
      (⟨true, [0, 1, 2]⟩ : Constraint Bool (Fin 3)).satProb paritySem g ≤ 1 ∧
      (⟨true, [0, 1, 2]⟩ : Constraint Bool (Fin 3)).satProb paritySem
        (fun v => signVal (![true, false, false] v)) = 1 :=
  ⟨Constraint.satProb_nonneg _ hg _, Constraint.satProb_le_one _ hg _, by
    rw [Constraint.satProb_signVal, ite_eq_left (by decide)]⟩

/-- The two equations `x₀ + x₁ + x₂ = b`, `b ∈ {true, false}`: every assignment satisfies exactly
one, so its value is `1/2`; listed as one check per bit `b`, the same through the uniform choice
of `b`. -/
example (σ : Fin 3 → Bool) :
    CSP.satFraction paritySem σ [⟨true, [0, 1, 2]⟩, ⟨false, [0, 1, 2]⟩] = 1 / 2 ∧
      CSP.satFraction paritySem σ
        ((univ : Finset Bool).toList.map fun b => ⟨b, [0, 1, 2]⟩) = 1 / 2 := by
  constructor
  · rw [satFraction_of_ne_nil _ _ (List.cons_ne_nil _ _)]
    simp only [List.countP_cons, List.countP_nil, List.length_cons, List.length_nil,
      Constraint.eval, List.map_cons, List.map_nil, paritySem_three]
    rcases Bool.eq_false_or_eq_true (σ 0 ^^ σ 1 ^^ σ 2) with h | h <;> simp [h]
  · rw [satFraction_map_toList _ _ univ_nonempty, Fintype.expect_eq_sum_div_card,
      Fintype.sum_bool, Fintype.card_bool]
    simp only [Constraint.eval, List.map_cons, List.map_nil, paritySem_three]
    rcases Bool.eq_false_or_eq_true (σ 0 ^^ σ 1 ^^ σ 2) with h | h <;> simp [h]

/-- The randomized value of the same pair at means `1/2, 1/2, 1` is `(3/8 + 5/8)/2 = 1/2`,
also through the uniform choice of `b`; it lies in `[0, 1]`, and at signs it is `satFraction`. -/
example :
    CSP.expectedSatFraction paritySem ![1 / 2, 1 / 2, 1]
        [⟨true, [0, 1, 2]⟩, ⟨false, [0, 1, 2]⟩] = 1 / 2 ∧
      CSP.expectedSatFraction paritySem ![1 / 2, 1 / 2, 1]
        ((univ : Finset Bool).toList.map fun b => ⟨b, [0, 1, 2]⟩) = 1 / 2 ∧
      CSP.expectedSatFraction paritySem (fun v => signVal (![true, false, false] v))
        [⟨true, [0, 1, 2]⟩, ⟨false, [0, 1, 2]⟩] =
        CSP.satFraction paritySem ![true, false, false]
          [⟨true, [0, 1, 2]⟩, ⟨false, [0, 1, 2]⟩] := by
  refine ⟨?_, ?_, expectedSatFraction_signVal _ _ _⟩
  · rw [expectedSatFraction_of_ne_nil _ _ (List.cons_ne_nil _ _)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, satProb_paritySem,
      List.length_cons, List.length_nil]
    norm_num
  · rw [expectedSatFraction_map_toList _ _ univ_nonempty, Fintype.expect_eq_sum_div_card,
      Fintype.sum_bool, Fintype.card_bool, satProb_paritySem, satProb_paritySem]
    norm_num

/-- Values of Håstad's test lie in `[0, 1]`, for an assignment and for a randomized one. -/
example (f : (Fin 2 → Bool) → Bool) :
    (hastadTest 1 4 2).satFraction paritySem f ∈ Set.Icc 0 1 ∧
      (hastadTest 1 4 2).expectedSatFraction paritySem (fun _ => 1 / 3) ∈ Set.Icc 0 1 :=
  ⟨satFraction_mem_Icc _ _ _, expectedSatFraction_mem_Icc _ (fun _ => by norm_num [abs_div]) _⟩

/-- Håstad's checks are 3-variable equations, and the `(1/2, 3/4)` test is also a `(1/2, 2/3)`
test. -/
example :
    (hastadTest 1 4 3).WellFormed e3LinArity ∧
      IsDictatorVsNoNotables e3LinArity paritySem (1 / 2) (2 / 3) (hastadTest 1 4) := by
  refine ⟨wellFormed_hastadTest 1 4 3, ?_⟩
  have h := isDictatorVsNoNotables_hastadTest (a := 1) (q := 4) (by norm_num) (by norm_num)
  exact h.of_le (by norm_num) (by norm_num)

/-- Unfolding the values: the nullary constraint `paritySem true []` (the empty XOR is `false`)
never holds; one satisfied equation has value `1`, the empty instance has value `1`, and the
equation `x₀ + x₁ + x₂ = true` at means `1/2, 1/2, 1` has value `3/8`. -/
example (g : Fin 3 → ℝ) (σ : Fin 3 → Bool) :
    (⟨true, []⟩ : Constraint Bool (Fin 3)).satProb paritySem g = 0 ∧
      CSP.satFraction paritySem ![true, false, false] [⟨true, [0, 1, 2]⟩] = 1 ∧
      CSP.satFraction paritySem σ ([] : CSP Bool (Fin 3)) = 1 ∧
      CSP.expectedSatFraction paritySem ![1 / 2, 1 / 2, 1] [⟨true, [0, 1, 2]⟩] = 3 / 8 := by
  refine ⟨?_, ?_, satFraction_nil _ _, ?_⟩
  · simp [Constraint.satProb_def, paritySem]
  · simp [satFraction_def, Constraint.eval]
  · rw [expectedSatFraction_def]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, satProb_paritySem,
      List.length_cons, List.length_nil]
    norm_num

end CslibFrontierTests.BooleanAnalysisHastadTest

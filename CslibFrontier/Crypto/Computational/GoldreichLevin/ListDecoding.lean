/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GoldreichLevin.Decoding
public import CslibFrontier.Crypto.Computational.GoldreichLevin.Parameters
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Crypto.Computational.GoldreichLevin.Nonuniform
import CslibFrontier.Foundations.Data.BitString.Parity.DotProduct
import CslibFrontier.Foundations.Data.BitString.Support.Equiv
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Goldreich–Levin Simultaneous List Decoding (Goldreich Theorem 7.8 & Exercise 7.6)

`Decoding.lean` proves the single-target Goldreich–Levin bound `decode_failure_le`: for any fixed
`x : BitString n` with `1 / 2 + ε ≤ agreement predictor x`, the pairwise-independent candidate set
`candidates predictor masks` omits `x` with probability at most
`n / (4 * ε ^ 2 * (2 ^ k - 1))`.

Goldreich Theorem 7.8 (and Exercise 7.6) requires a **simultaneous list decoder** that outputs a
list containing *every* correlated string `x : BitString n` with
`1 / 2 + ε ≤ agreement predictor x` in one run with probability at least `1 / 2`, together with a
pruned variant in which every output candidate is guaranteed to have correlation at least `ε / 2`
(and the returned list has size at most `1 / ε ^ 2`).

This module develops both finite list-decoding results on top of `Decoding.lean`,
`CslibFrontier/Foundations/BooleanAnalysis/Fourier.lean`, and
`CslibFrontier/Probability/Concentration.lean`:

1. **Parseval bound on the number of correlated strings (`card_filter_agreement_ge_le`):**
   For every `x : BitString n`, the Fourier coefficient of `r ↦ signVal (predictor r)` on the
   support `{i | x i = true}` is `2 * agreement predictor x - 1`
   (`fourierCoeff_signVal_eq_two_mul_agreement_sub_one`). By Parseval's identity
   (`BitString.sum_fourierCoeff_sq_signVal`), the squared correlations sum to `1`
   (`sum_two_mul_agreement_sub_one_sq`), so at most `1 / (4 * ε ^ 2)` strings `x : BitString n`
   can satisfy `1 / 2 + ε ≤ agreement predictor x`.
2. **Simultaneous list decoding (`decode_simultaneous_failure_le`,
   `decode_listMaskCount_simultaneous_success_ge_half`):**
   Union-bounding `decode_failure_le` over the `≤ 1 / (4 * ε ^ 2)` heavy strings shows that
   `decode predictor k` misses *any* string with `1 / 2 + ε ≤ agreement predictor x` with
   probability at most `n / (16 * ε ^ 4 * (2 ^ k - 1))`. Setting
   `listMaskCount n precision = maskCount n (2 * precision ^ 2)` gives `2 ^ k - 1 ≥ 8 * n * p ^ 4`,
   so simultaneous failure is at most `1 / 4 ≤ 1 / 2` and simultaneous success is at least `1 / 2`
   (in fact `≥ 3 / 4`), with candidate list size at most `2 ^ k ≤ 16 * n * p ^ 4 + 2`.
3. **Pruned simultaneous list decoding (`decodePruned`,
   `decodePruned_simultaneous_success_ge_half`):**
   Using a second independent batch of `m = pruneSampleCount n precision` uniform query points and
   Chernoff–Hoeffding concentration (`PMF.uniform_abs_sum_div_sub_expect_ge_le`), filtering
   `candidates predictor masks` at empirical agreement threshold `(2 * p + 3) / (4 * p)` succeeds
   with probability at least `1 / 2` in returning a list that:
   - contains every `x : BitString n` with `1 / 2 + 1 / p ≤ agreement predictor x`,
   - contains only strings `x : BitString n` with `1 / 2 + 1 / (2 * p) ≤ agreement predictor x`,
   - has cardinality at most `p ^ 2` on that event (and at most `16 * n * p ^ 4 + 2`
     unconditionally).

## Main definitions

* `Cslib.Crypto.GoldreichLevin.listMaskCount`: mask count `maskCount n (2 * precision ^ 2)` for
  simultaneous list decoding at correlation `1 / precision`.
* `Cslib.Crypto.GoldreichLevin.empiricalHits`: count of sample points `j : Fin m` on which
  `predictor (samples j) = x ⬝ᵥ samples j`.
* `Cslib.Crypto.GoldreichLevin.prunedCandidates`: candidates from `candidates predictor masks`
  whose empirical hit fraction is at least `num / den`.
* `Cslib.Crypto.GoldreichLevin.decodePruned`: two-stage distribution drawing uniform `masks` and
  independent uniform `samples` and returning `prunedCandidates`.
* `Cslib.Crypto.GoldreichLevin.pruneSampleCount`: sample count
  `32 * (listMaskCount n precision + 3) * precision ^ 2` for concentration pruning.

## Main results

* `Cslib.Crypto.GoldreichLevin.fourierCoeff_signVal_eq_two_mul_agreement_sub_one`: the Fourier
  coefficient on the support of `x` equals `2 * agreement predictor x - 1`.
* `Cslib.Crypto.GoldreichLevin.sum_two_mul_agreement_sub_one_sq`: Parseval's identity for inner
  product correlations (`∑ x, (2 * agreement predictor x - 1) ^ 2 = 1`).
* `Cslib.Crypto.GoldreichLevin.card_filter_agreement_ge_le`: at most `1 / (4 * ε ^ 2)` strings
  satisfy `1 / 2 + ε ≤ agreement predictor x`.
* `Cslib.Crypto.GoldreichLevin.decode_simultaneous_failure_le`: simultaneous failure bound
  `n / (16 * ε ^ 4 * (2 ^ k - 1))`.
* `Cslib.Crypto.GoldreichLevin.decode_listMaskCount_simultaneous_success_ge_half`: simultaneous
  list decoding at `listMaskCount n precision` succeeds with probability at least `1 / 2`.
* `Cslib.Crypto.GoldreichLevin.decodePruned_simultaneous_success_ge_half`: pruned simultaneous list
  decoding succeeds with probability at least `1 / 2`, outputting all `(1 / 2 + 1 / p)`-agreed
  strings, only `(1 / 2 + 1 / (2 * p))`-agreed strings, and at most `p ^ 2` strings.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008], Theorem 7.8
  (p. 254) and Exercise 7.6 (see also the March 2007 draft `r4.pdf` [Goldreich2007DraftR4],
  Theorem 7.8 and Exercise 7.6).
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability
open scoped BigOperators ENNReal

variable {n k m : ℕ}

/-! ### 1. Parseval identity for inner-product correlations and correlated-string count bound -/

/-- The uniform expectation of `score predictor x` over `BitString n` is `agreement predictor x`. -/
theorem expect_score_eq_agreement (predictor : BitString n → Bool) (x : BitString n) :
    (𝔼 r : BitString n, score predictor x r) = agreement predictor x := by
  rw [Finset.expect_eq_sum_div_card, agreement_eq_card_div]
  simp [score, Fintype.card_pi]

/-- Pointwise sign product identity: `signVal (predictor r) * signVal (x ⬝ᵥ r)` equals
`2 * score predictor x r - 1`. -/
theorem signVal_mul_signVal_dotProduct_eq (predictor : BitString n → Bool) (x r : BitString n) :
    BitString.signVal (predictor r) * BitString.signVal (x ⬝ᵥ r) =
      2 * score predictor x r - 1 := by
  rw [BitString.signVal_mul_signVal, score]
  split_ifs <;> ring

/-- The Fourier coefficient of `r ↦ signVal (predictor r)` at the support `{i | x i = true}` of `x`
is `2 * agreement predictor x - 1`. -/
theorem fourierCoeff_signVal_eq_two_mul_agreement_sub_one (predictor : BitString n → Bool)
    (x : BitString n) :
    BitString.fourierCoeff (fun r => BitString.signVal (predictor r))
        (Finset.univ.filter (fun i => x i = true)) =
      2 * agreement predictor x - 1 := by
  unfold BitString.fourierCoeff
  have hterm :
      (fun r : BitString n =>
          BitString.signVal (predictor r) *
            BitString.chi ℝ (Finset.univ.filter (fun i => x i = true)) r) =
        fun r : BitString n => 2 * score predictor x r - 1 := by
    funext r
    rw [BitString.chi_eq_signVal_parityOn, ← BitString.dotProduct_eq_parityOn r x,
      dotProduct_comm r x, signVal_mul_signVal_dotProduct_eq]
  rw [hterm, Finset.expect_sub_distrib, ← Finset.mul_expect, expect_score_eq_agreement,
    Finset.expect_const Finset.univ_nonempty]

/-- **Parseval's identity for inner-product correlations**: the squared correlations
`(2 * agreement predictor x - 1) ^ 2` summed over all `x : BitString n` equal `1`. -/
theorem sum_two_mul_agreement_sub_one_sq (predictor : BitString n → Bool) :
    ∑ x : BitString n, (2 * agreement predictor x - 1) ^ 2 = 1 := by
  have h : ∀ x : BitString n,
      (2 * agreement predictor x - 1) ^ 2 =
        BitString.fourierCoeff (fun r => BitString.signVal (predictor r))
          (BitString.supportEquiv x) ^ 2 := by
    intro x
    rw [BitString.supportEquiv_apply, fourierCoeff_signVal_eq_two_mul_agreement_sub_one]
  simp_rw [h]
  exact (Equiv.sum_comp BitString.supportEquiv
    (fun S => BitString.fourierCoeff (fun r => BitString.signVal (predictor r)) S ^ 2)).trans
    (BitString.sum_fourierCoeff_sq_signVal predictor)

/-- **Correlated-string count bound (multiplied form)**: for any `0 ≤ ε`, the number of strings
`x : BitString n` with `1 / 2 + ε ≤ agreement predictor x` satisfies `card * (4 * ε ^ 2) ≤ 1`. -/
theorem card_filter_agreement_ge_mul_le_one (predictor : BitString n → Bool) {ε : ℝ}
    (hε : 0 ≤ ε) :
    ((Finset.univ.filter (fun x : BitString n => 1 / 2 + ε ≤ agreement predictor x)).card : ℝ) *
      (4 * ε ^ 2) ≤ 1 := by
  calc
    ((Finset.univ.filter (fun x : BitString n => 1 / 2 + ε ≤ agreement predictor x)).card : ℝ) *
        (4 * ε ^ 2)
      = ∑ _x ∈ Finset.univ.filter (fun x : BitString n => 1 / 2 + ε ≤ agreement predictor x),
          (4 * ε ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : BitString n => 1 / 2 + ε ≤ agreement predictor x),
          (2 * agreement predictor x - 1) ^ 2 := by
        refine Finset.sum_le_sum fun x hx => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have h1 : 2 * ε ≤ 2 * agreement predictor x - 1 := by linarith
        have h2 : (2 * ε) ^ 2 ≤ (2 * agreement predictor x - 1) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        linarith
    _ ≤ ∑ x : BitString n, (2 * agreement predictor x - 1) ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg fun x => sq_nonneg _
    _ = 1 := sum_two_mul_agreement_sub_one_sq predictor

/-- **Correlated-string count bound**: for any `0 < ε`, at most `1 / (4 * ε ^ 2)` strings
`x : BitString n` satisfy `1 / 2 + ε ≤ agreement predictor x`. -/
theorem card_filter_agreement_ge_le (predictor : BitString n → Bool) {ε : ℝ}
    (hε : 0 < ε) :
    ((Finset.univ.filter (fun x : BitString n => 1 / 2 + ε ≤ agreement predictor x)).card : ℝ) ≤
      1 / (4 * ε ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  exact card_filter_agreement_ge_mul_le_one predictor hε.le

/-- At threshold `1 / 2 + 1 / (2 * precision)`, at most `precision ^ 2` strings `x : BitString n`
satisfy `1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x`. -/
theorem card_filter_agreement_ge_half_inv_le (predictor : BitString n → Bool) {precision : ℕ}
    (hprec : 0 < precision) :
    (Finset.univ.filter (fun x : BitString n =>
      1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x)).card ≤ precision ^ 2 := by
  have hp : (0 : ℝ) < precision := Nat.cast_pos.mpr hprec
  have hε : (0 : ℝ) < 1 / (2 * (precision : ℝ)) := by positivity
  have hmul := card_filter_agreement_ge_mul_le_one predictor hε.le
  have h4 : (4 : ℝ) * (1 / (2 * (precision : ℝ))) ^ 2 = 1 / (precision : ℝ) ^ 2 := by
    field_simp
    ring
  rw [h4, mul_one_div, div_le_one (by positivity)] at hmul
  exact_mod_cast hmul

/-! ### 2. Simultaneous finite list decoding (`decode predictor k`) -/

/-- **Simultaneous list-decoding failure bound**: for any `0 < ε` and `0 < k`, the probability
that `decode predictor k` omits *some* `x : BitString n` with `1 / 2 + ε ≤ agreement predictor x`
is at most `n / (16 * ε ^ 4 * (2 ^ k - 1))`. -/
theorem decode_simultaneous_failure_le (predictor : BitString n → Bool) (ε : ℝ) (hε : 0 < ε)
    (hk : 0 < k) :
    (decode predictor k).toOuterMeasure
        {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list} ≤
      ENNReal.ofReal ((n : ℝ) / (16 * ε ^ 4 * (2 ^ k - 1 : ℕ))) := by
  let H : Finset (BitString n) :=
    Finset.univ.filter (fun x : BitString n => 1 / 2 + ε ≤ agreement predictor x)
  let B : ℝ := (n : ℝ) / (4 * ε ^ 2 * (2 ^ k - 1 : ℕ))
  have hB : 0 ≤ B := by positivity
  have hsub :
      {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list} ⊆
        ⋃ x ∈ H, {list : Finset (BitString n) | x ∉ list} := by
    intro list hlist
    simp only [Set.mem_ofPred, not_forall] at hlist
    rcases hlist with ⟨x, hx, hxnot⟩
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩) hxnot
  calc
    (decode predictor k).toOuterMeasure
        {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list}
      ≤ (decode predictor k).toOuterMeasure
          (⋃ x ∈ H, {list : Finset (BitString n) | x ∉ list}) :=
        (decode predictor k).toOuterMeasure.mono hsub
    _ ≤ ∑ x ∈ H, (decode predictor k).toOuterMeasure {list : Finset (BitString n) | x ∉ list} :=
        MeasureTheory.measure_biUnion_finset_le H _
    _ ≤ ∑ _x ∈ H, ENNReal.ofReal B := by
        refine Finset.sum_le_sum fun x hx => ?_
        simp only [H, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact decode_failure_le predictor x ε hε hk hx
    _ = (H.card : ℝ≥0∞) * ENNReal.ofReal B := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((H.card : ℝ) * B) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg H.card), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((1 / (4 * ε ^ 2)) * B) := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (card_filter_agreement_ge_le predictor hε) hB
    _ = ENNReal.ofReal ((n : ℝ) / (16 * ε ^ 4 * (2 ^ k - 1 : ℕ))) := by
        congr 1
        dsimp [B]
        ring

/-- General target-bound specialization of `decode_simultaneous_failure_le`: when
`(n : ℝ) ≤ 16 * δ * ε ^ 4 * (2 ^ k - 1)`, `decode predictor k` fails to contain all
`(1 / 2 + ε)`-correlated strings with probability at most `ENNReal.ofReal δ`. -/
theorem decode_simultaneous_failure_le_of_le (predictor : BitString n → Bool) (ε δ : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (hparam : (n : ℝ) ≤ 16 * δ * ε ^ 4 * (2 ^ k - 1 : ℕ)) :
    (decode predictor k).toOuterMeasure
        {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list} ≤
      ENNReal.ofReal δ := by
  have hsub_pos : (0 : ℝ) < (2 ^ k - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (Nat.one_lt_two_pow hk.ne')
  have hden_pos : 0 < 16 * ε ^ 4 * (2 ^ k - 1 : ℕ) := by positivity
  have hfrac : (n : ℝ) / (16 * ε ^ 4 * (2 ^ k - 1 : ℕ)) ≤ δ := by
    rw [div_le_iff₀ hden_pos]
    linarith
  exact (decode_simultaneous_failure_le predictor ε hε hk).trans (ENNReal.ofReal_le_ofReal hfrac)

/-- When `(n : ℝ) ≤ 4 * ε ^ 4 * (2 ^ k - 1)`, `decode predictor k` fails to contain all
`(1 / 2 + ε)`-correlated strings with probability at most `1 / 4`. -/
theorem decode_simultaneous_failure_le_quarter (predictor : BitString n → Bool) (ε : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (hparam : (n : ℝ) ≤ 4 * ε ^ 4 * (2 ^ k - 1 : ℕ)) :
    (decode predictor k).toOuterMeasure
        {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list} ≤
      (1 / 4 : ℝ≥0∞) := by
  simpa using decode_simultaneous_failure_le_of_le predictor ε (1 / 4) hε hk (by linarith)

/-- When `(n : ℝ) ≤ 8 * ε ^ 4 * (2 ^ k - 1)`, `decode predictor k` fails to contain all
`(1 / 2 + ε)`-correlated strings with probability at most `1 / 2`. -/
theorem decode_simultaneous_failure_le_half (predictor : BitString n → Bool) (ε : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (hparam : (n : ℝ) ≤ 8 * ε ^ 4 * (2 ^ k - 1 : ℕ)) :
    (decode predictor k).toOuterMeasure
        {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list} ≤
      (1 / 2 : ℝ≥0∞) := by
  simpa using decode_simultaneous_failure_le_of_le predictor ε (1 / 2) hε hk (by linarith)

/-- **Simultaneous list-decoding success bound (`ℝ≥0∞`)**: when
`(n : ℝ) ≤ 8 * ε ^ 4 * (2 ^ k - 1)`, `decode predictor k` outputs a list containing every
`x : BitString n` with `1 / 2 + ε ≤ agreement predictor x` with probability at least `1 / 2`. -/
theorem decode_simultaneous_success_ge_half (predictor : BitString n → Bool) (ε : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (hparam : (n : ℝ) ≤ 8 * ε ^ 4 * (2 ^ k - 1 : ℕ)) :
    (1 / 2 : ℝ≥0∞) ≤
      (decode predictor k).toOuterMeasure
        {list : Finset (BitString n) |
          ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list} := by
  let S : Set (Finset (BitString n)) :=
    {list | ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list}
  have hfail : (decode predictor k).toOuterMeasure Sᶜ ≤ (1 / 2 : ℝ≥0∞) :=
    decode_simultaneous_failure_le_half predictor ε hε hk hparam
  have hle :
      (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) ≤
        (decode predictor k).toOuterMeasure S + (1 / 2 : ℝ≥0∞) := by
    calc
      (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) = 1 := ENNReal.add_halves 1
      _ = (decode predictor k).toOuterMeasure S + (decode predictor k).toOuterMeasure Sᶜ :=
        (Probability.PMF.toOuterMeasure_add_compl_ennreal (decode predictor k) S).symm
      _ ≤ (decode predictor k).toOuterMeasure S + (1 / 2 : ℝ≥0∞) := by gcongr
  exact (ENNReal.add_le_add_iff_right (by simp)).mp hle

/-- **Simultaneous list-decoding success bound (`ℝ`)**: when
`(n : ℝ) ≤ 8 * ε ^ 4 * (2 ^ k - 1)`, the real success probability of simultaneous list decoding is
at least `1 / 2`. -/
theorem decode_simultaneous_success_toReal_ge_half (predictor : BitString n → Bool) (ε : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (hparam : (n : ℝ) ≤ 8 * ε ^ 4 * (2 ^ k - 1 : ℕ)) :
    1 / 2 ≤
      ((decode predictor k).toOuterMeasure
        {list : Finset (BitString n) |
          ∀ x : BitString n, 1 / 2 + ε ≤ agreement predictor x → x ∈ list}).toReal := by
  simpa [one_div] using ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (decode_simultaneous_success_ge_half predictor ε hε hk hparam)

/-! ### 3. Explicit parameter schedule for simultaneous list decoding -/

/-- Number of random masks `k` for simultaneous list decoding at correlation `1 / precision`
(or `1 / (2 * precision)`): defined via `maskCount n (2 * precision ^ 2)` so that
`2 ^ k - 1 ≥ 8 * n * precision ^ 4`. -/
def listMaskCount (n precision : ℕ) : ℕ :=
  maskCount n (2 * precision ^ 2)

/-- `listMaskCount n precision` is always positive. -/
theorem listMaskCount_pos (n precision : ℕ) : 0 < listMaskCount n precision :=
  maskCount_pos n (2 * precision ^ 2)

/-- `2 ^ listMaskCount n precision - 1` is at least `8 * n * precision ^ 4`. -/
theorem subsetCount_listMaskCount_ge (n precision : ℕ) :
    8 * n * precision ^ 4 ≤ 2 ^ listMaskCount n precision - 1 := by
  unfold listMaskCount
  have h := subsetCount_maskCount_ge n (2 * precision ^ 2)
  have hring : 2 * n * (2 * precision ^ 2) ^ 2 = 8 * n * precision ^ 4 := by ring
  linarith

/-- The guess count `2 ^ listMaskCount n precision` is at most `16 * n * precision ^ 4 + 2`. -/
theorem guessCount_listMaskCount_le (n precision : ℕ) :
    2 ^ listMaskCount n precision ≤ 16 * n * precision ^ 4 + 2 := by
  unfold listMaskCount
  have h := guessCount_maskCount_le n (2 * precision ^ 2)
  have hring : 4 * n * (2 * precision ^ 2) ^ 2 + 2 = 16 * n * precision ^ 4 + 2 := by ring
  linarith

/-- `listMaskCount n precision` is bounded by `8 * n * precision ^ 4 + 1`. -/
theorem listMaskCount_le (n precision : ℕ) :
    listMaskCount n precision ≤ 8 * n * precision ^ 4 + 1 := by
  unfold listMaskCount
  have h := maskCount_le n (2 * precision ^ 2)
  have hring : 2 * n * (2 * precision ^ 2) ^ 2 + 1 = 8 * n * precision ^ 4 + 1 := by ring
  linarith

/-- At `k = listMaskCount n precision` and `ε = 1 / precision`, the quarter-failure parameter
condition `(n : ℝ) ≤ 4 * ε ^ 4 * (2 ^ k - 1)` holds (in fact `32 * n ≤ 4 * ε ^ 4 * (2 ^ k - 1)`). -/
theorem listMaskCount_sufficient (n : ℕ) {precision : ℕ} (hprec : 0 < precision) :
    (n : ℝ) ≤ 4 * (1 / (precision : ℝ)) ^ 4 * (2 ^ listMaskCount n precision - 1 : ℕ) := by
  have hp : (0 : ℝ) < precision := Nat.cast_pos.mpr hprec
  have hsub : (8 * n * precision ^ 4 : ℝ) ≤ (2 ^ listMaskCount n precision - 1 : ℕ) := by
    exact_mod_cast subsetCount_listMaskCount_ge n precision
  have hpos : (0 : ℝ) ≤ 4 * (1 / (precision : ℝ)) ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsub hpos
  have h32n : 32 * (n : ℝ) = 4 * (1 / (precision : ℝ)) ^ 4 * (8 * n * precision ^ 4 : ℝ) := by
    field_simp
    ring
  linarith

/-- At `k = listMaskCount n precision`, simultaneous list decoding for threshold
`1 / 2 + 1 / precision` fails with probability at most `1 / 4`. -/
theorem decode_listMaskCount_simultaneous_failure_le_quarter (predictor : BitString n → Bool)
    {precision : ℕ} (hprec : 0 < precision) :
    (decode predictor (listMaskCount n precision)).toOuterMeasure
        {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list} ≤
      (1 / 4 : ℝ≥0∞) := by
  have hp : (0 : ℝ) < precision := Nat.cast_pos.mpr hprec
  exact decode_simultaneous_failure_le_quarter predictor (1 / (precision : ℝ)) (by positivity)
    (listMaskCount_pos n precision) (listMaskCount_sufficient n hprec)

/-- At `k = listMaskCount n precision`, simultaneous list decoding for threshold
`1 / 2 + 1 / precision` fails with probability at most `1 / 2`. -/
theorem decode_listMaskCount_simultaneous_failure_le_half (predictor : BitString n → Bool)
    {precision : ℕ} (hprec : 0 < precision) :
    (decode predictor (listMaskCount n precision)).toOuterMeasure
        {list : Finset (BitString n) |
          ¬ ∀ x : BitString n, 1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list} ≤
      (1 / 2 : ℝ≥0∞) :=
  (decode_listMaskCount_simultaneous_failure_le_quarter predictor hprec).trans (by norm_num)

/-- **Simultaneous list decoding at `listMaskCount` (`ℝ≥0∞`)**: for `0 < precision`,
`decode predictor (listMaskCount n precision)` outputs a list containing every
`x : BitString n` with `1 / 2 + 1 / precision ≤ agreement predictor x` with probability at least
`1 / 2`. -/
theorem decode_listMaskCount_simultaneous_success_ge_half (predictor : BitString n → Bool)
    {precision : ℕ} (hprec : 0 < precision) :
    (1 / 2 : ℝ≥0∞) ≤
      (decode predictor (listMaskCount n precision)).toOuterMeasure
        {list : Finset (BitString n) |
          ∀ x : BitString n, 1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list} := by
  have hp : (0 : ℝ) < precision := Nat.cast_pos.mpr hprec
  have hparam := listMaskCount_sufficient n hprec
  have h8 : (n : ℝ) ≤ 8 * (1 / (precision : ℝ)) ^ 4 * (2 ^ listMaskCount n precision - 1 : ℕ) := by
    have hnonneg :
        0 ≤ 4 * (1 / (precision : ℝ)) ^ 4 * (2 ^ listMaskCount n precision - 1 : ℕ) := by
      positivity
    linarith
  exact decode_simultaneous_success_ge_half predictor (1 / (precision : ℝ)) (by positivity)
    (listMaskCount_pos n precision) h8

/-- **Simultaneous list decoding at `listMaskCount` (`ℝ`)**: for `0 < precision`, the real success
probability of `decode predictor (listMaskCount n precision)` is at least `1 / 2`. -/
theorem decode_listMaskCount_simultaneous_success_toReal_ge_half (predictor : BitString n → Bool)
    {precision : ℕ} (hprec : 0 < precision) :
    1 / 2 ≤
      ((decode predictor (listMaskCount n precision)).toOuterMeasure
        {list : Finset (BitString n) |
          ∀ x : BitString n, 1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x →
            x ∈ list}).toReal := by
  simpa [one_div] using ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (decode_listMaskCount_simultaneous_success_ge_half predictor hprec)

/-! ### 4. Pruned simultaneous list decoding (`decodePruned`) -/

/-- Number of sample indices `j : Fin m` on which `predictor (samples j) = x ⬝ᵥ samples j`. -/
def empiricalHits (predictor : BitString n → Bool) (samples : Fin m → BitString n)
    (x : BitString n) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => predictor (samples j) = x ⬝ᵥ samples j)).card

/-- `empiricalHits predictor samples x`, cast to `ℝ`, is the sum of `score predictor x (samples j)`
over `j : Fin m`. -/
theorem empiricalHits_eq_sum_score (predictor : BitString n → Bool)
    (samples : Fin m → BitString n) (x : BitString n) :
    (empiricalHits predictor samples x : ℝ) = ∑ j : Fin m, score predictor x (samples j) := by
  simp [empiricalHits, score, Finset.sum_boole]

/-- Candidates from `candidates predictor masks` whose empirical agreement on `samples` is at least
`num / den`, expressed in integer cross-multiplied form `m * num ≤ den * empiricalHits`. -/
def prunedCandidates (predictor : BitString n → Bool) (num den : ℕ)
    (masks : Fin k → BitString n) (samples : Fin m → BitString n) : Finset (BitString n) :=
  (candidates predictor masks).filter (fun x =>
    decide (m * num ≤ den * empiricalHits predictor samples x))

/-- Membership characterization for `prunedCandidates`. -/
@[simp]
theorem mem_prunedCandidates {predictor : BitString n → Bool} {num den : ℕ}
    {masks : Fin k → BitString n} {samples : Fin m → BitString n} {x : BitString n} :
    x ∈ prunedCandidates predictor num den masks samples ↔
      x ∈ candidates predictor masks ∧ m * num ≤ den * empiricalHits predictor samples x := by
  simp [prunedCandidates]

/-- `prunedCandidates` is a subset of `candidates predictor masks`. -/
theorem prunedCandidates_subset_candidates (predictor : BitString n → Bool) (num den : ℕ)
    (masks : Fin k → BitString n) (samples : Fin m → BitString n) :
    prunedCandidates predictor num den masks samples ⊆ candidates predictor masks :=
  Finset.filter_subset _ _

/-- `prunedCandidates` has cardinality at most `2 ^ k`. -/
theorem card_prunedCandidates_le (predictor : BitString n → Bool) (num den : ℕ)
    (masks : Fin k → BitString n) (samples : Fin m → BitString n) :
    (prunedCandidates predictor num den masks samples).card ≤ 2 ^ k :=
  (Finset.card_le_card (prunedCandidates_subset_candidates predictor num den masks samples)).trans
    (card_candidates_le predictor masks)

/-- The two-stage pruned Goldreich–Levin list-decoding distribution: sample `k` uniform masks for
candidate generation and `m` independent uniform sample points for empirical-agreement pruning at
threshold `num / den`. -/
noncomputable def decodePruned (predictor : BitString n → Bool) (k m num den : ℕ) :
    PMF (Finset (BitString n)) :=
  (PMF.uniformOfFintype (Fin k → BitString n)).bind (fun masks =>
    (PMF.uniformOfFintype (Fin m → BitString n)).map (prunedCandidates predictor num den masks))

/-- `score predictor x r` has absolute value at most `1`. -/
theorem abs_score_le_one (predictor : BitString n → Bool) (x r : BitString n) :
    |score predictor x r| ≤ 1 := by
  unfold score
  split_ifs <;> norm_num

/-- **Empirical agreement concentration**: for `m` uniform i.i.d. query points
`samples : Fin m → BitString n` and any `x : BitString n`, the empirical hit fraction deviates from
`agreement predictor x` by `γ ≥ 0` with probability at most `2 * exp (-(m * γ ^ 2) / 2)`. -/
theorem empiricalHits_div_sub_agreement_ge_le (predictor : BitString n → Bool)
    (x : BitString n) {γ : ℝ} (hγ : 0 ≤ γ) :
    (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure
        {samples : Fin m → BitString n |
          γ ≤ |(empiricalHits predictor samples x : ℝ) / m - agreement predictor x|} ≤
      ENNReal.ofReal (2 * Real.exp (-(m * γ ^ 2) / 2)) := by
  simpa only [← empiricalHits_eq_sum_score, expect_score_eq_agreement] using
    Probability.PMF.uniform_abs_sum_div_sub_expect_ge_le (m := m) (score predictor x)
      (abs_score_le_one predictor x) hγ

/-- Number of independent uniform estimation queries `m` used to prune the candidate list at
accuracy `1 / (4 * precision)` with failure probability at most `1 / 4`. -/
def pruneSampleCount (n precision : ℕ) : ℕ :=
  32 * (listMaskCount n precision + 3) * precision ^ 2

/-- `pruneSampleCount n precision` is positive whenever `0 < precision`. -/
theorem pruneSampleCount_pos (n : ℕ) {precision : ℕ} (hprec : 0 < precision) :
    0 < pruneSampleCount n precision := by
  unfold pruneSampleCount
  positivity

/-- Polynomial upper bound on `pruneSampleCount n precision`. -/
theorem pruneSampleCount_le (n precision : ℕ) :
    pruneSampleCount n precision ≤ 256 * n * precision ^ 6 + 128 * precision ^ 2 := by
  unfold pruneSampleCount
  have hk := listMaskCount_le n precision
  nlinarith

private theorem exp_neg_nat_le_inv_two_pow (K : ℕ) :
    Real.exp (-(K : ℝ)) ≤ 1 / (2 : ℝ) ^ K := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ K ≤ Real.exp (K : ℝ) := by
    simpa [← Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) h2 K
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by positivity) hpow

/-- Conditional on any fixed `masks : Fin (listMaskCount n precision) → BitString n`, the
probability over `samples ← uniformOfFintype` that empirical agreement deviates from true agreement
by at least `1 / (4 * precision)` on *some* candidate `x ∈ candidates predictor masks` is at most
`1 / 4`. -/
theorem prune_bad_samples_le_quarter (predictor : BitString n → Bool) {precision : ℕ}
    (hprec : 0 < precision) (masks : Fin (listMaskCount n precision) → BitString n) :
    (PMF.uniformOfFintype (Fin (pruneSampleCount n precision) → BitString n)).toOuterMeasure
        {samples |
          ∃ x ∈ candidates predictor masks,
            1 / (4 * (precision : ℝ)) ≤
              |(empiricalHits predictor samples x : ℝ) / pruneSampleCount n precision -
                agreement predictor x|} ≤
      (1 / 4 : ℝ≥0∞) := by
  let k := listMaskCount n precision
  let m := pruneSampleCount n precision
  let γ : ℝ := 1 / (4 * (precision : ℝ))
  let C := candidates predictor masks
  have hp : (0 : ℝ) < precision := Nat.cast_pos.mpr hprec
  have hγ : 0 ≤ γ := by positivity
  let E : ℝ := 2 * Real.exp (-(m * γ ^ 2) / 2)
  have hE_nonneg : 0 ≤ E := by positivity
  have hsub :
      {samples : Fin m → BitString n |
          ∃ x ∈ C,
            γ ≤ |(empiricalHits predictor samples x : ℝ) / m - agreement predictor x|} ⊆
        ⋃ x ∈ C,
          {samples : Fin m → BitString n |
            γ ≤ |(empiricalHits predictor samples x : ℝ) / m - agreement predictor x|} := by
    intro samples hs
    rcases hs with ⟨x, hx, hdev⟩
    exact Set.mem_biUnion hx hdev
  have hexp_eq : -((m : ℝ) * γ ^ 2) / 2 = -((k + 3 : ℕ) : ℝ) := by
    dsimp [m, γ, k, pruneSampleCount]
    push_cast
    field_simp
    ring
  have hE_le : E ≤ 1 / (4 * (2 : ℝ) ^ k) := by
    dsimp [E]
    rw [hexp_eq]
    have hexp := exp_neg_nat_le_inv_two_pow (k + 3)
    have hpow : (2 : ℝ) ^ (k + 3) = 8 * (2 : ℝ) ^ k := by ring
    rw [hpow] at hexp
    have hmul := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2)
    have hdiv : (2 : ℝ) * (1 / (8 * (2 : ℝ) ^ k)) = 1 / (4 * (2 : ℝ) ^ k) := by ring
    linarith
  have hcard : (C.card : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast card_candidates_le predictor masks
  have hprod : (C.card : ℝ) * E ≤ 1 / 4 := by
    calc
      (C.card : ℝ) * E ≤ (2 : ℝ) ^ k * (1 / (4 * (2 : ℝ) ^ k)) :=
        mul_le_mul hcard hE_le hE_nonneg (by positivity)
      _ = 1 / 4 := by field_simp
  calc
    (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure
        {samples |
          ∃ x ∈ C,
            γ ≤ |(empiricalHits predictor samples x : ℝ) / m - agreement predictor x|}
      ≤ (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure
          (⋃ x ∈ C,
            {samples |
              γ ≤ |(empiricalHits predictor samples x : ℝ) / m - agreement predictor x|}) :=
        (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure.mono hsub
    _ ≤ ∑ x ∈ C,
          (PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure
            {samples |
              γ ≤ |(empiricalHits predictor samples x : ℝ) / m - agreement predictor x|} :=
        MeasureTheory.measure_biUnion_finset_le C _
    _ ≤ ∑ _x ∈ C, ENNReal.ofReal E := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact empiricalHits_div_sub_agreement_ge_le predictor x hγ
    _ = (C.card : ℝ≥0∞) * ENNReal.ofReal E := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal ((C.card : ℝ) * E) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg C.card), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hprod
    _ = (1 / 4 : ℝ≥0∞) := by simp

/-- Deterministic pruning correctness on a good sample batch: when `candidates predictor masks`
contains all `(1 / 2 + 1 / p)`-agreed strings and every candidate's empirical agreement on `samples`
is within `1 / (4 * p)` of its true agreement, `prunedCandidates` at threshold
`(2 * p + 3) / (4 * p)` contains all `(1 / 2 + 1 / p)`-agreed strings, contains only
`(1 / 2 + 1 / (2 * p))`-agreed strings, and has cardinality at most `p ^ 2`. -/
theorem prunedCandidates_good_of_accurate (predictor : BitString n → Bool) {precision : ℕ}
    (hprec : 0 < precision) (masks : Fin (listMaskCount n precision) → BitString n)
    (samples : Fin (pruneSampleCount n precision) → BitString n)
    (hmasks : ∀ x : BitString n,
      1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ candidates predictor masks)
    (hsamples : ∀ x ∈ candidates predictor masks,
      |(empiricalHits predictor samples x : ℝ) / pruneSampleCount n precision -
        agreement predictor x| < 1 / (4 * (precision : ℝ))) :
    (∀ x : BitString n,
      1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x →
        x ∈ prunedCandidates predictor (2 * precision + 3) (4 * precision) masks samples) ∧
    (∀ x ∈ prunedCandidates predictor (2 * precision + 3) (4 * precision) masks samples,
      1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x) ∧
    (prunedCandidates predictor (2 * precision + 3) (4 * precision) masks samples).card ≤
      precision ^ 2 := by
  have hp : (0 : ℝ) < precision := Nat.cast_pos.mpr hprec
  have hm : 0 < pruneSampleCount n precision := pruneSampleCount_pos n hprec
  have hm' : (0 : ℝ) < pruneSampleCount n precision := Nat.cast_pos.mpr hm
  have hfrac1 : 1 / (precision : ℝ) - 1 / (4 * (precision : ℝ)) = 3 / (4 * (precision : ℝ)) := by
    ring
  have hfrac2 :
      3 / (4 * (precision : ℝ)) - 1 / (4 * (precision : ℝ)) = 1 / (2 * (precision : ℝ)) := by
    ring
  have h1 : ∀ x : BitString n,
      1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x →
        x ∈ prunedCandidates predictor (2 * precision + 3) (4 * precision) masks samples := by
    intro x hx
    have hcand : x ∈ candidates predictor masks := hmasks x hx
    rw [mem_prunedCandidates]
    refine ⟨hcand, ?_⟩
    have hacc := (abs_lt.mp (hsamples x hcand)).1
    have hlow :
        ((2 * precision + 3 : ℕ) : ℝ) ≤
          ((4 * precision : ℕ) : ℝ) *
            ((empiricalHits predictor samples x : ℝ) / pruneSampleCount n precision) := by
      push_cast
      have hdiv :
          1 / 2 + 3 / (4 * (precision : ℝ)) ≤
            (empiricalHits predictor samples x : ℝ) / pruneSampleCount n precision := by
        linarith
      have hmul := mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 4 * precision by positivity)
      have hring :
          (4 * (precision : ℝ)) * (1 / 2 + 3 / (4 * (precision : ℝ))) =
            2 * (precision : ℝ) + 3 := by
        field_simp
        ring
      linarith
    have hcross :
        (pruneSampleCount n precision : ℝ) * (2 * precision + 3 : ℕ) ≤
          (4 * precision : ℕ) * (empiricalHits predictor samples x : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hlow hm'.le
      have hcancel :
          (pruneSampleCount n precision : ℝ) *
              (((4 * precision : ℕ) : ℝ) *
                ((empiricalHits predictor samples x : ℝ) / pruneSampleCount n precision)) =
            (4 * precision : ℕ) * (empiricalHits predictor samples x : ℝ) := by
        field_simp
      linarith
    exact_mod_cast hcross
  have h2 : ∀ x ∈ prunedCandidates predictor (2 * precision + 3) (4 * precision) masks samples,
      1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x := by
    intro x hx
    rw [mem_prunedCandidates] at hx
    rcases hx with ⟨hcand, hthresh⟩
    have hacc := (abs_lt.mp (hsamples x hcand)).2
    have hthresh' :
        (pruneSampleCount n precision : ℝ) * ((2 * precision + 3 : ℕ) : ℝ) ≤
          ((4 * precision : ℕ) : ℝ) * (empiricalHits predictor samples x : ℝ) := by
      exact_mod_cast hthresh
    have hdiv :
        1 / 2 + 3 / (4 * (precision : ℝ)) ≤
          (empiricalHits predictor samples x : ℝ) / pruneSampleCount n precision := by
      rw [le_div_iff₀ hm']
      have h4p : (0 : ℝ) < 4 * (precision : ℝ) := by positivity
      rw [← mul_le_mul_iff_right₀ h4p]
      have hring :
          (1 / 2 + 3 / (4 * (precision : ℝ))) * (pruneSampleCount n precision : ℝ) *
              (4 * (precision : ℝ)) =
            (pruneSampleCount n precision : ℝ) * (2 * (precision : ℝ) + 3) := by
        field_simp
        ring
      push_cast at hthresh'
      linarith
    linarith
  have h3 :
      (prunedCandidates predictor (2 * precision + 3) (4 * precision) masks samples).card ≤
        precision ^ 2 := by
    have hsub :
        prunedCandidates predictor (2 * precision + 3) (4 * precision) masks samples ⊆
          Finset.univ.filter (fun x : BitString n =>
            1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h2 x hx⟩
    exact (Finset.card_le_card hsub).trans (card_filter_agreement_ge_half_inv_le predictor hprec)
  exact ⟨h1, h2, h3⟩

/-- **Pruned simultaneous list-decoding failure bound**: for `0 < precision`, `decodePruned`
fails the simultaneous completeness, soundness, or list-size specification with probability at most
`1 / 2` (in fact at most `1 / 4 + 1 / 4 = 1 / 2`). -/
theorem decodePruned_simultaneous_failure_le_half (predictor : BitString n → Bool)
    {precision : ℕ} (hprec : 0 < precision) :
    (decodePruned predictor (listMaskCount n precision) (pruneSampleCount n precision)
        (2 * precision + 3) (4 * precision)).toOuterMeasure
      {list : Finset (BitString n) |
        ¬ ((∀ x : BitString n,
              1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list) ∧
            (∀ x ∈ list, 1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x) ∧
            list.card ≤ precision ^ 2)} ≤
      (1 / 2 : ℝ≥0∞) := by
  let k := listMaskCount n precision
  let m := pruneSampleCount n precision
  let GoodList : Set (Finset (BitString n)) :=
    {list |
      (∀ x : BitString n, 1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list) ∧
      (∀ x ∈ list, 1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x) ∧
      list.card ≤ precision ^ 2}
  let GoodMasks : Set (Fin k → BitString n) :=
    {masks |
      ∀ x : BitString n,
        1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ candidates predictor masks}
  have hmasks_fail :
      (PMF.uniformOfFintype (Fin k → BitString n)).toOuterMeasure GoodMasksᶜ ≤ (1 / 4 : ℝ≥0∞) := by
    have h := decode_listMaskCount_simultaneous_failure_le_quarter predictor hprec
    rw [decode, PMF.toOuterMeasure_map_apply] at h
    exact h
  have hstep :
      ∀ masks ∈ (PMF.uniformOfFintype (Fin k → BitString n)).support,
        masks ∈ GoodMasks →
        ((PMF.uniformOfFintype (Fin m → BitString n)).map
            (prunedCandidates predictor (2 * precision + 3) (4 * precision) masks)).toOuterMeasure
          GoodListᶜ ≤ (1 / 4 : ℝ≥0∞) := by
    intro masks _ hmasks
    rw [PMF.toOuterMeasure_map_apply]
    refine le_trans
      ((PMF.uniformOfFintype (Fin m → BitString n)).toOuterMeasure.mono ?_)
      (prune_bad_samples_le_quarter predictor hprec masks)
    intro samples hbad
    rw [Set.mem_preimage, Set.mem_compl_iff] at hbad
    by_contra hgood
    have hacc :
        ∀ x ∈ candidates predictor masks,
          |(empiricalHits predictor samples x : ℝ) / pruneSampleCount n precision -
            agreement predictor x| < 1 / (4 * (precision : ℝ)) := by
      intro x hx
      by_contra hge
      exact hgood ⟨x, hx, not_lt.mp hge⟩
    exact hbad (prunedCandidates_good_of_accurate predictor hprec masks samples hmasks hacc)
  have hbind :=
    Probability.PMF.toOuterMeasure_bind_failure_le
      (PMF.uniformOfFintype (Fin k → BitString n))
      (fun masks =>
        (PMF.uniformOfFintype (Fin m → BitString n)).map
          (prunedCandidates predictor (2 * precision + 3) (4 * precision) masks))
      GoodMasks GoodListᶜ (1 / 4 : ℝ≥0∞) hstep
  have hhalf : (1 / 4 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by
    have h : ENNReal.ofReal (1 / 4 + 1 / 4) = ENNReal.ofReal (1 / 2) := by norm_num
    rw [ENNReal.ofReal_add (by norm_num) (by norm_num)] at h
    simpa using h
  calc
    (decodePruned predictor k m (2 * precision + 3) (4 * precision)).toOuterMeasure GoodListᶜ
      ≤ (PMF.uniformOfFintype (Fin k → BitString n)).toOuterMeasure GoodMasksᶜ + (1 / 4 : ℝ≥0∞) :=
        hbind
    _ ≤ (1 / 4 : ℝ≥0∞) + (1 / 4 : ℝ≥0∞) := by gcongr
    _ = (1 / 2 : ℝ≥0∞) := hhalf

/-- **Pruned simultaneous list-decoding success bound (`ℝ≥0∞`)**: for `0 < precision`,
`decodePruned` succeeds with probability at least `1 / 2` in returning a list that:
1. contains every `x : BitString n` with `1 / 2 + 1 / precision ≤ agreement predictor x`,
2. contains only `x : BitString n` with `1 / 2 + 1 / (2 * precision) ≤ agreement predictor x`,
3. has cardinality at most `precision ^ 2`. -/
theorem decodePruned_simultaneous_success_ge_half (predictor : BitString n → Bool)
    {precision : ℕ} (hprec : 0 < precision) :
    (1 / 2 : ℝ≥0∞) ≤
      (decodePruned predictor (listMaskCount n precision) (pruneSampleCount n precision)
          (2 * precision + 3) (4 * precision)).toOuterMeasure
        {list : Finset (BitString n) |
          (∀ x : BitString n,
            1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list) ∧
          (∀ x ∈ list, 1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x) ∧
          list.card ≤ precision ^ 2} := by
  let p :=
    decodePruned predictor (listMaskCount n precision) (pruneSampleCount n precision)
      (2 * precision + 3) (4 * precision)
  let S : Set (Finset (BitString n)) :=
    {list |
      (∀ x : BitString n, 1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list) ∧
      (∀ x ∈ list, 1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x) ∧
      list.card ≤ precision ^ 2}
  have hfail : p.toOuterMeasure Sᶜ ≤ (1 / 2 : ℝ≥0∞) :=
    decodePruned_simultaneous_failure_le_half predictor hprec
  have hle : (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) ≤ p.toOuterMeasure S + (1 / 2 : ℝ≥0∞) := by
    calc
      (1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) = 1 := ENNReal.add_halves 1
      _ = p.toOuterMeasure S + p.toOuterMeasure Sᶜ :=
        (Probability.PMF.toOuterMeasure_add_compl_ennreal p S).symm
      _ ≤ p.toOuterMeasure S + (1 / 2 : ℝ≥0∞) := by gcongr
  exact (ENNReal.add_le_add_iff_right (by simp)).mp hle

/-- **Pruned simultaneous list-decoding success bound (`ℝ`)**: for `0 < precision`, the real
success probability of `decodePruned` is at least `1 / 2`. -/
theorem decodePruned_simultaneous_success_toReal_ge_half (predictor : BitString n → Bool)
    {precision : ℕ} (hprec : 0 < precision) :
    1 / 2 ≤
      ((decodePruned predictor (listMaskCount n precision) (pruneSampleCount n precision)
          (2 * precision + 3) (4 * precision)).toOuterMeasure
        {list : Finset (BitString n) |
          (∀ x : BitString n,
            1 / 2 + 1 / (precision : ℝ) ≤ agreement predictor x → x ∈ list) ∧
          (∀ x ∈ list, 1 / 2 + 1 / (2 * (precision : ℝ)) ≤ agreement predictor x) ∧
          list.card ≤ precision ^ 2}).toReal := by
  simpa [one_div] using ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (decodePruned_simultaneous_success_ge_half predictor hprec)

end Cslib.Crypto.GoldreichLevin

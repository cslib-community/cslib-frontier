/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.HoeffdingStep
import CslibFrontier.Probability.PoissonBinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hoeffding's inequality for the biased binomial distribution

For a Bernoulli trial with parameter `p ∈ [0, 1]`, the centered moment generating function
`(1 - p) exp (-s p) + p exp (s (1 - p))` is bounded above by `exp (s² / 8)` for every `s : ℝ`
(`Cslib.one_sub_mul_exp_add_mul_exp_le`), by Mathlib’s bounded-variable sub-Gaussian estimate.
The binomial theorem gives the centered MGF identity (`Cslib.sum_choose_mul_pow_mul_exp`).
Specializing finite-PMF concentration to independent coins and using the replicated
Poisson-binomial law gives one-sided (`Cslib.sum_filter_le_sub_choose_mul_pow_le`,
`Cslib.sum_filter_le_mul_sub_choose_mul_pow_le`) and two-sided
(`Cslib.sum_filter_le_abs_sub_choose_mul_pow_le`) Hoeffding tail bounds for `Bin(Q, p)`, together
with the interval-complement form (`Cslib.sum_filter_notMem_choose_mul_pow_le`) used in Lemma 4.8 of
`[OpenAI2026ETH]` at `p = (r - 1) / (2 r)`. All tail inequalities hold for every `Q : ℕ`, including
`Q = 0`.

For the unbiased case `p = 1 / 2` in counting form on `ι → Bool`, see
`Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le`.

## Main results

* `Cslib.one_sub_mul_exp_add_mul_exp_le`: Hoeffding's lemma for a biased Bernoulli trial.
* `Cslib.sum_choose_mul_pow_eq_one`: binomial probability weights sum to `1`.
* `Cslib.choose_mul_pow_le_mode`: the binomial weight is largest at the mode `n p` when that is an
  integer.
* `Cslib.sum_choose_mul_pow_mul_exp`: centered moment generating function of `Bin(Q, p)`.
* `Cslib.sum_filter_le_sub_choose_mul_pow_le`: upper-tail Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_le_mul_sub_choose_mul_pow_le`: lower-tail Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_le_abs_sub_choose_mul_pow_le`: two-sided Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_notMem_choose_mul_pow_le`: tail bound outside a subset covering
  `[Q p - t, Q p + t]`.

## References

* [W. Hoeffding, *Probability Inequalities for Sums of Bounded Random Variables*][Hoeffding1963]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 4.7, Lemma 4.8,
  pp. 34–35.
-/

public section

namespace Cslib

open Finset Real

/-- **Hoeffding's lemma for a biased Bernoulli trial** `[Hoeffding1963]`: for `p ∈ [0, 1]` and
`s : ℝ`, the centered moment generating function `(1 - p) exp (-s p) + p exp (s (1 - p))` is at
most `exp (s² / 8)`. This specializes `Cslib.Probability.PMF.sum_mul_exp_sub_mean_le` to
`PMF.coin`. -/
theorem one_sub_mul_exp_add_mul_exp_le {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (s : ℝ) :
    (1 - p) * exp (-s * p) + p * exp (s * (1 - p)) ≤ exp (s ^ 2 / 8) := by
  have h := Probability.PMF.sum_mul_exp_sub_mean_le (Probability.PMF.coin ⟨p, hp₀, hp₁⟩)
    (fun b => if b then (1 : ℝ) else 0) (a := 0) (b := 1) (fun b _ => by cases b <;> norm_num) s
  simp only [Fintype.sum_bool, Probability.PMF.coin_apply_toReal, ↓reduceIte,
    Bool.false_eq_true, sub_zero, one_pow, mul_one, mul_zero, add_zero] at h
  convert h using 1
  rw [show s * (0 - p) = -s * p by ring]; ring

/-- The binomial weights `C(Q, k) p^k (1 - p)^(Q - k)` sum to `1`. -/
theorem sum_choose_mul_pow_eq_one (Q : ℕ) (p : ℝ) :
    ∑ k ∈ range (Q + 1), (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) = 1 := by
  calc ∑ k ∈ range (Q + 1), (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
      = ∑ k ∈ range (Q + 1), p ^ k * (1 - p) ^ (Q - k) * (Q.choose k : ℝ) :=
          sum_congr rfl fun _ _ => by ring
    _ = (p + (1 - p)) ^ Q := (add_pow p (1 - p) Q).symm
    _ = 1 := by simp only [add_sub_cancel, one_pow]

/-- **The centered binomial moment generating function**: summing
`C(Q, k) p^k (1 - p)^(Q - k) exp (s (k - Q p))` over `0 ≤ k ≤ Q` factors as the `Q`-th power of
the single-trial moment generating function. -/
theorem sum_choose_mul_pow_mul_exp (Q : ℕ) (p s : ℝ) :
    ∑ k ∈ range (Q + 1),
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p)) =
    ((1 - p) * exp (-s * p) + p * exp (s * (1 - p))) ^ Q := by
  rw [add_comm ((1 - p) * exp (-s * p)), add_pow]
  refine sum_congr rfl fun k hk => ?_
  have hkQ : k ≤ Q := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [mul_pow, mul_pow, ← exp_natCast_mul, ← exp_natCast_mul]
  calc (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p))
      = p ^ k * (1 - p) ^ (Q - k) * (Q.choose k : ℝ) *
          (exp (↑k * (s * (1 - p))) * exp (↑(Q - k) * (-s * p))) := by
        have hexp : s * ((k : ℝ) - Q * p) =
            (k : ℝ) * (s * (1 - p)) + ((Q : ℝ) - k) * (-s * p) := by ring
        rw [hexp, exp_add, ← Nat.cast_sub hkQ]
        ring
    _ = p ^ k * exp (↑k * (s * (1 - p))) *
          ((1 - p) ^ (Q - k) * exp (↑(Q - k) * (-s * p))) * (Q.choose k : ℝ) := by ring

/-- Every binomial probability weight `C(Q, k) p^k (1 - p)^(Q - k)` is nonnegative for
`p ∈ [0, 1]`. -/
private theorem choose_mul_pow_nonneg (Q k : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) := by
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
  positivity

/-- Express an event of the replicated Poisson-binomial law as a finite binomial sum. -/
private theorem poissonBinomial_event_toReal (Q : ℕ) (p : unitInterval) (P : ℕ → Prop)
    [DecidablePred P] :
    ((Probability.PMF.poissonBinomial (List.replicate Q p)).toOuterMeasure {k | P k}).toReal =
      ∑ k ∈ range (Q + 1) with P k,
        (Q.choose k : ℝ) * (p : ℝ) ^ k * (1 - p) ^ (Q - k) := by
  rw [_root_.PMF.toOuterMeasure_apply, tsum_eq_sum (s := range (Q + 1)) fun k hk => by
    simp [Set.indicator_apply, Probability.PMF.poissonBinomial_eq_zero_of_lt
      (ps := List.replicate Q p) (by simpa using hk)]]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [ENNReal.toReal_sum (fun _ _ => by split_ifs <;> simp [_root_.PMF.apply_ne_top]), sum_filter]
  exact sum_congr rfl fun k _ => by
    split_ifs <;> simp [Probability.PMF.poissonBinomial_replicate_apply_toReal]

/-- Bridge a filtered binomial sum directly to the `pi`-of-coins event probability used by
`Probability.Concentration`. -/
private theorem sum_filter_choose_mul_pow_eq_pi_toOuterMeasure (Q : ℕ) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (P : ℝ → Prop) [DecidablePred P] :
    (∑ k ∈ range (Q + 1) with P ((k : ℕ) : ℝ),
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)) =
    ((Probability.PMF.pi fun i : Fin (List.replicate Q (⟨p, hp₀, hp₁⟩ : unitInterval)).length =>
      Probability.PMF.coin (List.replicate Q (⟨p, hp₀, hp₁⟩ : unitInterval))[i]).toOuterMeasure
        {f | P (∑ i, if f i then (1 : ℝ) else 0)}).toReal := by
  let q : unitInterval := ⟨p, hp₀, hp₁⟩
  let ps := List.replicate Q q
  have hevent : {f : Fin ps.length → Bool | P (∑ i, if f i then (1 : ℝ) else 0)} =
      (fun f => ∑ i, if f i then 1 else 0) ⁻¹' {k | P ((k : ℕ) : ℝ)} := by
    ext f
    simp
  rw [hevent, ← _root_.PMF.toOuterMeasure_map_apply,
    ← Probability.PMF.poissonBinomial_eq_map_pi ps,
    poissonBinomial_event_toReal Q q (fun k => P ((k : ℕ) : ℝ))]

private noncomputable abbrev coinFamily (Q : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (i : Fin (List.replicate Q (⟨p, hp₀, hp₁⟩ : unitInterval)).length) : PMF Bool :=
  Probability.PMF.coin (List.replicate Q (⟨p, hp₀, hp₁⟩ : unitInterval))[i]

private theorem indicator_mem_Icc {ι : Type*} {P : ι → Bool → Prop} (i : ι) (b : Bool)
    (_ : P i b) :
    (if b then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> norm_num

private theorem sum_pi_coin_mean (Q : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (∑ i : Fin (List.replicate Q (⟨p, hp₀, hp₁⟩ : unitInterval)).length, ∑ b : Bool,
      (coinFamily Q hp₀ hp₁ i b).toReal * (if b then (1 : ℝ) else 0)) = Q * p := by
  simp [coinFamily, Probability.PMF.coin_apply_toReal]

/-- **Upper-tail Hoeffding inequality for `Bin(Q, p)`**: for `p ∈ [0, 1]` and `0 ≤ t`, the
binomial probability mass on `k - Q p ≥ t` is at most `exp (-2 t² / Q)`. At `Q = 0` the right-hand
side is `exp 0 = 1`. -/
theorem sum_filter_le_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ ((k : ℕ) : ℝ) - Q * p,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    exp (-2 * t ^ 2 / Q) := by
  classical
  rw [sum_filter_choose_mul_pow_eq_pi_toOuterMeasure Q hp₀ hp₁ (fun x => t ≤ x - Q * p)]
  have h := Probability.PMF.pi_sum_ge_mean_add (coinFamily Q hp₀ hp₁)
    (fun _ b => if b then (1 : ℝ) else 0) zero_le_one indicator_mem_Icc ht
  rw [sum_pi_coin_mean Q hp₀ hp₁] at h
  simpa only [Fintype.card_fin, List.length_replicate, one_pow, mul_one, ← le_sub_iff_add_le']
    using h

/-- **Lower-tail Hoeffding inequality for `Bin(Q, p)`**: for `p ∈ [0, 1]` and `0 ≤ t`, the
binomial probability mass on `Q p - k ≥ t` is at most `exp (-2 t² / Q)`. Derived directly from
`Cslib.Probability.PMF.pi_sum_le_mean_sub`. -/
theorem sum_filter_le_mul_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ Q * p - ((k : ℕ) : ℝ),
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    exp (-2 * t ^ 2 / Q) := by
  classical
  rw [sum_filter_choose_mul_pow_eq_pi_toOuterMeasure Q hp₀ hp₁ (fun x => t ≤ Q * p - x)]
  have h := Probability.PMF.pi_sum_le_mean_sub (coinFamily Q hp₀ hp₁)
    (fun _ b => if b then (1 : ℝ) else 0) zero_le_one indicator_mem_Icc ht
  rw [sum_pi_coin_mean Q hp₀ hp₁] at h
  simpa only [Fintype.card_fin, List.length_replicate, one_pow, mul_one, le_sub_comm] using h

/-- **Two-sided Hoeffding inequality for `Bin(Q, p)`** `[Hoeffding1963]`: for `p ∈ [0, 1]` and
`0 ≤ t`, the binomial probability mass on `|k - Q p| ≥ t` is at most `2 exp (-2 t² / Q)`. Derived
directly from `Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge`. -/
theorem sum_filter_le_abs_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ |((k : ℕ) : ℝ) - Q * p|,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    2 * exp (-2 * t ^ 2 / Q) := by
  classical
  rw [sum_filter_choose_mul_pow_eq_pi_toOuterMeasure Q hp₀ hp₁ (fun x => t ≤ |x - Q * p|)]
  have h := Probability.PMF.pi_sum_abs_sub_mean_ge (coinFamily Q hp₀ hp₁)
    (fun _ b => if b then (1 : ℝ) else 0) zero_le_one indicator_mem_Icc ht
  rw [sum_pi_coin_mean Q hp₀ hp₁] at h
  simpa only [Fintype.card_fin, List.length_replicate, one_pow, mul_one] using h

/-- **Interval-complement Hoeffding bound for `Bin(Q, p)`**: if `I` contains every integer
`0 ≤ k ≤ Q` within `t` of the mean `Q p`, then the binomial mass outside `I` is at most
`2 exp (-2 t² / Q)`. -/
theorem sum_filter_notMem_choose_mul_pow_le (Q : ℕ) (I : Finset ℕ) {p t : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (ht : 0 ≤ t)
    (hI : ∀ k ∈ range (Q + 1), |(k : ℝ) - Q * p| ≤ t → k ∈ I) :
    ∑ k ∈ range (Q + 1) with k ∉ I,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    2 * exp (-2 * t ^ 2 / Q) := by
  refine (sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun k _ _ =>
    choose_mul_pow_nonneg Q k hp₀ hp₁).trans (sum_filter_le_abs_sub_choose_mul_pow_le Q hp₀ hp₁ ht)
  simp only [mem_filter] at hk ⊢
  exact ⟨hk.1, le_of_not_gt fun h => hk.2 (hI k hk.1 h.le)⟩

/-- **The mode of the binomial distribution**: when `n p = w` is an integer, the weight
`C(n, k) p ^ k (1 - p) ^ (n - k)` of `Bin(n, p)` is largest at `k = w`. Consecutive weights satisfy
`t (k + 1) (k + 1) (1 - p) = t k (n - k) p`, so they increase up to `w` and decrease after it. -/
theorem choose_mul_pow_le_mode {n w : ℕ} {p : ℝ} (hw : w ≤ n) (hnp : (n : ℝ) * p = w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ n.choose w * p ^ w * (1 - p) ^ (n - w) := by
  set t : ℕ → ℝ := fun k => (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
  have ht0 (j : ℕ) : 0 ≤ t j := choose_mul_pow_nonneg n j hp0 hp1
  -- `t (k + 1) (k + 1) (1 - p) = t k (n - k) p`
  have hstep {j : ℕ} (hj : j < n) : t (j + 1) * ((j + 1) * (1 - p)) = t j * ((n - j : ℝ) * p) := by
    have hc : (n.choose (j + 1) : ℝ) * (j + 1) = n.choose j * (n - j : ℝ) := by
      rw [← Nat.cast_sub hj.le]
      exact_mod_cast Nat.choose_succ_right_eq n j
    have he : (1 - p) ^ (n - j) = (1 - p) ^ (n - (j + 1)) * (1 - p) := by
      rw [← pow_succ]
      congr 1
      omega
    dsimp only [t]
    rw [he, pow_succ]
    linear_combination (p ^ j * p * (1 - p) ^ (n - (j + 1)) * (1 - p)) * hc
  have hup {j : ℕ} (hjw : j < w) : t j ≤ t (j + 1) := by
    have : (j : ℝ) + 1 ≤ w := by exact_mod_cast hjw
    have : (w : ℝ) ≤ n := by exact_mod_cast hw
    have hp : 0 < p := hp0.lt_of_ne' fun h => by
      subst h
      linarith
    have hpos : (0 : ℝ) < (n - j) * p := mul_pos (by linarith) hp
    have h2 := mul_le_mul_of_nonneg_left (by nlinarith : ((j : ℝ) + 1) * (1 - p) ≤ (n - j) * p)
      (ht0 (j + 1))
    exact le_of_mul_le_mul_right (by linarith [hstep (hjw.trans_le hw)]) hpos
  have hdown {j : ℕ} (hwj : w ≤ j) (hjn : j < n) : t (j + 1) ≤ t j := by
    have : (w : ℝ) ≤ j := by exact_mod_cast hwj
    have : (j : ℝ) < n := by exact_mod_cast hjn
    have hpos : (0 : ℝ) < (j + 1) * (1 - p) := mul_pos (by positivity) (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_left (by nlinarith : ((n : ℝ) - j) * p ≤ (j + 1) * (1 - p))
      (ht0 j)
    exact le_of_mul_le_mul_right (by linarith [hstep hjn]) hpos
  rcases le_total k w with hkw | hwk
  · suffices ∀ d, k + d ≤ w → t k ≤ t (k + d) by
      simpa [Nat.add_sub_cancel' hkw] using this (w - k) (by omega)
    intro d
    induction d with
    | zero => exact fun _ => le_rfl
    | succ d ih => exact fun h => (ih (by omega)).trans (hup (by omega))
  · suffices ∀ d, w + d ≤ n → t (w + d) ≤ t w by
      simpa [Nat.add_sub_cancel' hwk] using this (k - w) (by omega)
    intro d
    induction d with
    | zero => exact fun _ => le_rfl
    | succ d ih => exact fun h => (hdown (j := w + d) (by omega) (by omega)).trans (ih (by omega))

end Cslib

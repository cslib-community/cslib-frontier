/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Event
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Azuma–Hoeffding inequality for sequential discrete processes

`Cslib.Probability.PMF.chain μ₀ step n` runs `n` sequential transitions from an initial
distribution `μ₀ : PMF S`, applying `step i : S → PMF S` in round `i`. Neither `[Fintype S]` nor a
measurable-space instance on `S` is assumed.

Suppose an adapted real process `X : ℕ → S → ℝ` starts at most `m` on `μ₀.support` and, from every
reachable state `s` in round `i < n`, has conditional expected increment at most `0` (a
supermartingale) while ranging over an interval `[a, a + c i]` of width `c i` on
`(step i s).support` (where `a` may depend on both `i` and `s`). Conditioning round by round and
applying Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) on `(S, ⊤)` bounds
the exponential moment by `exp (t² (∑ i < n, c i²) / 8)` (`tsum_chain_mul_exp_le`), and Markov's
inequality yields the Azuma–Hoeffding tail bound `exp (-2 ε² / ∑ i < n, c i²)` (`azuma_le`),
together with its submartingale lower tail (`azuma_le_sub`) and two-sided martingale bound
(`azuma_abs_le`).

## Main definitions

* `Cslib.Probability.PMF.chain`: `n`-step sequential kernel chain from an initial `PMF`.

## Main results

* `Cslib.Probability.PMF.tsum_mul_exp_sub_mean_le`,
  `Cslib.Probability.PMF.sum_mul_exp_sub_mean_le`: Hoeffding's centered moment-generating function
  bound on `PMF`s.
* `Cslib.Probability.PMF.tsum_mul_exp_le_of_tsum_toReal_mul_le_zero`: one-step supermartingale
  exponential moment bound.
* `Cslib.Probability.PMF.tsum_chain_mul_exp_le`: `n`-step supermartingale exponential moment bound.
* `Cslib.Probability.PMF.azuma_le`: Azuma–Hoeffding upper-tail inequality for supermartingales.
* `Cslib.Probability.PMF.azuma_le_sub`: Azuma–Hoeffding lower-tail inequality for submartingales.
* `Cslib.Probability.PMF.azuma_abs_le`: two-sided Azuma–Hoeffding inequality for martingales.

## References

* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
* [K. Azuma, *Weighted sums of certain dependent random variables*][Azuma1967]
* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989]
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-! ### Sequential chains of discrete kernels -/

section Chain

variable {S : Type*}

/-- Run `n` sequential steps from initial law `μ₀`, applying transition kernel `step i` at
round `i`. -/
noncomputable def chain (μ₀ : PMF S) (step : ℕ → S → PMF S) : ℕ → PMF S
  | 0 => μ₀
  | n + 1 => (chain μ₀ step n).bind (step n)

@[simp]
theorem chain_zero (μ₀ : PMF S) (step : ℕ → S → PMF S) : chain μ₀ step 0 = μ₀ := by
  rw [chain]

@[simp]
theorem chain_succ (μ₀ : PMF S) (step : ℕ → S → PMF S) (n : ℕ) :
    chain μ₀ step (n + 1) = (chain μ₀ step n).bind (step n) := by
  rw [chain]

theorem mem_support_chain_succ_iff (μ₀ : PMF S) (step : ℕ → S → PMF S) (n : ℕ) (s' : S) :
    s' ∈ (chain μ₀ step (n + 1)).support ↔
      ∃ s ∈ (chain μ₀ step n).support, s' ∈ (step n s).support := by
  rw [chain_succ, _root_.PMF.mem_support_bind_iff]

end Chain

/-! ### One-step Hoeffding exponential moment bounds -/

section OneStep

variable {α : Type*}

/-- Clamp `g` into `[a, a + c]` outside `q.support` so boundedness holds everywhere without
changing values on `q.support`. -/
private noncomputable def clampToSupport (q : PMF α) (g : α → ℝ) (a : ℝ) (x : α) : ℝ :=
  open Classical in if x ∈ q.support then g x else a

private theorem clampToSupport_mem_Icc {q : PMF α} {g : α → ℝ} {a c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ x ∈ q.support, g x ∈ Set.Icc a (a + c)) (x : α) :
    clampToSupport q g a x ∈ Set.Icc a (a + c) := by
  classical
  dsimp only [clampToSupport]
  split_ifs with hx
  · exact hg x hx
  · exact ⟨le_rfl, by linarith⟩

private theorem tsum_toReal_mul_clampToSupport (q : PMF α) (g : α → ℝ) (a : ℝ) :
    (∑' x, (q x).toReal * clampToSupport q g a x) = ∑' x, (q x).toReal * g x := by
  classical
  refine tsum_congr fun x => ?_
  dsimp only [clampToSupport]
  split_ifs with hx
  · rfl
  · rw [(q.apply_eq_zero_iff x).mpr hx, ENNReal.toReal_zero, zero_mul, zero_mul]

/-- **Hoeffding's lemma** for a discrete `PMF`: if `g` ranges over an interval `[a, a + c]` on
`q.support`, its centered exponential moment at `t` is at most `exp (t² c² / 8)`. -/
theorem tsum_mul_exp_sub_mean_le (q : PMF α) (g : α → ℝ) {a c : ℝ}
    (hg : ∀ x ∈ q.support, g x ∈ Set.Icc a (a + c)) (t : ℝ) :
    ∑' x, q x * ENNReal.ofReal (Real.exp (t * (g x - ∑' y, (q y).toReal * g y))) ≤
      ENNReal.ofReal (Real.exp (t ^ 2 * c ^ 2 / 8)) := by
  obtain ⟨x₀, hx₀⟩ := q.support_nonempty
  have hc : 0 ≤ c := by linarith [(hg x₀ hx₀).1, (hg x₀ hx₀).2]
  let _ : MeasurableSpace α := ⊤
  set g' := clampToSupport q g a
  have hg' : ∀ x, g' x ∈ Set.Icc a (a + c) := clampToSupport_mem_Icc hc hg
  have hmeas : Measurable g' := fun _ _ => trivial
  have hint_g' : Integrable g' q.toMeasure :=
    Integrable.of_mem_Icc a (a + c) hmeas.aemeasurable (ae_of_all _ hg')
  have hmean : ∫ x, g' x ∂q.toMeasure = ∑' y, (q y).toReal * g y := by
    rw [_root_.PMF.integral_eq_tsum q g' hint_g']
    simp only [smul_eq_mul]
    exact tsum_toReal_mul_clampToSupport q g a
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := q.toMeasure) hmeas.aemeasurable
    (ae_of_all _ hg')
  have hmgf := hsub.mgf_le t
  have hint_exp : Integrable (fun x => Real.exp (t * (g' x - ∫ y, g' y ∂q.toMeasure)))
      q.toMeasure := hsub.integrable_exp_mul t
  rw [mgf, _root_.PMF.integral_eq_tsum q _ hint_exp] at hmgf
  simp only [smul_eq_mul, hmean] at hmgf
  have htsum_eq :
      (∑' x, q x * ENNReal.ofReal (Real.exp (t * (g x - ∑' y, (q y).toReal * g y)))) =
        ENNReal.ofReal
          (∑' x, (q x).toReal * Real.exp (t * (g' x - ∑' y, (q y).toReal * g y))) := by
    set B := Real.exp (|t| * (|a| + |a + c| + |∑' y, (q y).toReal * g y|))
    have M_le (x : α) : Real.exp (t * (g' x - ∑' y, (q y).toReal * g y)) ≤ B := by
      rw [Real.exp_le_exp]
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
      have hgx : |g' x| ≤ |a| + |a + c| := by
        have h1 := neg_abs_le a
        have h2 := le_abs_self (a + c)
        have h3 := abs_nonneg a
        have h4 := abs_nonneg (a + c)
        rw [abs_le]
        exact ⟨by linarith [(hg' x).1], by linarith [(hg' x).2]⟩
      linarith [abs_sub (g' x) (∑' y, (q y).toReal * g y)]
    have hsumm :
        Summable fun x => (q x).toReal * Real.exp (t * (g' x - ∑' y, (q y).toReal * g y)) :=
      ((summable_toReal q).mul_right B).of_nonneg_of_le
        (fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
        fun x => mul_le_mul_of_nonneg_left (M_le x) ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hsumm]
    refine tsum_congr fun x => ?_
    classical
    by_cases hx : x ∈ q.support
    · have hgx : g' x = g x := ite_eq_left hx
      rw [hgx, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (_root_.PMF.apply_ne_top q x)]
    · rw [(q.apply_eq_zero_iff x).mpr hx, ENNReal.toReal_zero, zero_mul, zero_mul,
        ENNReal.ofReal_zero]
  rw [htsum_eq]
  refine ENNReal.ofReal_le_ofReal (hmgf.trans_eq (congrArg Real.exp ?_))
  have hba : a + c - a = c := by ring
  simp only [hba, NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_ofNat,
    div_pow, sq_abs]
  ring

/-- Finite-type specialization of `tsum_mul_exp_sub_mean_le`, written with ordinary `Finset`
sums. -/
theorem sum_mul_exp_sub_mean_le [Fintype α] (q : PMF α) (g : α → ℝ) {a c : ℝ}
    (hg : ∀ x ∈ q.support, g x ∈ Set.Icc a (a + c)) (t : ℝ) :
    ∑ x, (q x).toReal * Real.exp (t * (g x - ∑ y, (q y).toReal * g y)) ≤
      Real.exp (t ^ 2 * c ^ 2 / 8) := by
  have h := tsum_mul_exp_sub_mean_le q g hg t
  rw [tsum_fintype, tsum_fintype] at h
  have hsum :
      (∑ x, q x * ENNReal.ofReal (Real.exp (t * (g x - ∑ y, (q y).toReal * g y)))) =
        ENNReal.ofReal
          (∑ x, (q x).toReal * Real.exp (t * (g x - ∑ y, (q y).toReal * g y))) := by
    rw [ENNReal.ofReal_sum_of_nonneg
      fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (q.apply_ne_top x)]
  rw [hsum] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h

/-- **One-step supermartingale exponential moment bound**: if `g` has nonpositive expectation under
`q` and lies in an interval `[a, a + c]` of width `c` on `q.support`, then for every `t ≥ 0`,
`∑' x, q x * exp (t * g x) ≤ exp (t² c² / 8)`. -/
theorem tsum_mul_exp_le_of_tsum_toReal_mul_le_zero (q : PMF α) (g : α → ℝ) {c t : ℝ}
    (ht : 0 ≤ t) (hmean : ∑' x, (q x).toReal * g x ≤ 0)
    (hrange : ∃ a : ℝ, ∀ x ∈ q.support, g x ∈ Set.Icc a (a + c)) :
    ∑' x, q x * ENNReal.ofReal (Real.exp (t * g x)) ≤
      ENNReal.ofReal (Real.exp (t ^ 2 * c ^ 2 / 8)) := by
  obtain ⟨a, ha⟩ := hrange
  set μ := ∑' y, (q y).toReal * g y
  have hμ_le : ENNReal.ofReal (Real.exp (t * μ)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht hmean))
  calc ∑' x, q x * ENNReal.ofReal (Real.exp (t * g x))
      = ∑' x, ENNReal.ofReal (Real.exp (t * μ)) *
          (q x * ENNReal.ofReal (Real.exp (t * (g x - μ)))) := by
        refine tsum_congr fun x => ?_
        have hexp : Real.exp (t * g x) = Real.exp (t * μ) * Real.exp (t * (g x - μ)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hexp, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ring
    _ = ENNReal.ofReal (Real.exp (t * μ)) *
          ∑' x, q x * ENNReal.ofReal (Real.exp (t * (g x - μ))) := ENNReal.tsum_mul_left
    _ ≤ 1 * ENNReal.ofReal (Real.exp (t ^ 2 * c ^ 2 / 8)) :=
        mul_le_mul' hμ_le (tsum_mul_exp_sub_mean_le q g ha t)
    _ = ENNReal.ofReal (Real.exp (t ^ 2 * c ^ 2 / 8)) := one_mul _

end OneStep

/-! ### Multi-round Azuma–Hoeffding inequality -/

section Azuma

variable {S : Type*}

/-- **Multi-round supermartingale exponential moment bound.** If `X 0 ≤ m` on `μ₀.support` and, at
every reachable state `s` in round `i < n`, the increment `X (i + 1) · - X i s` under `step i s`
has conditional expectation at most `0` and lies in an interval of width `c i`, then for every
`t ≥ 0` the `n`-step exponential moment of `X n - m` is at most
`exp (t² (∑ i < n, c i²) / 8)`. -/
theorem tsum_chain_mul_exp_le (μ₀ : PMF S) (step : ℕ → S → PMF S) (X : ℕ → S → ℝ) (c : ℕ → ℝ)
    {m : ℝ} (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (h0 : ∀ s ∈ μ₀.support, X 0 s ≤ m)
    (hmean : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      ∑' s', (step i s s').toReal * (X (i + 1) s' - X i s) ≤ 0)
    (hrange : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      ∃ a : ℝ, ∀ s' ∈ (step i s).support, X (i + 1) s' - X i s ∈ Set.Icc a (a + c i)) :
    ∑' s, chain μ₀ step n s * ENNReal.ofReal (Real.exp (t * (X n s - m))) ≤
      ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i ∈ Finset.range n, c i ^ 2) / 8)) := by
  induction n with
  | zero =>
    simp only [chain_zero, Finset.range_zero, Finset.sum_empty, mul_zero, zero_div,
      Real.exp_zero, ENNReal.ofReal_one]
    calc ∑' s, μ₀ s * ENNReal.ofReal (Real.exp (t * (X 0 s - m)))
        ≤ ∑' s, μ₀ s * 1 := by
          refine tsum_le_tsum fun s => ?_
          by_cases hs : s ∈ μ₀.support
          · refine mul_le_mul_of_nonneg_left ?_ zero_le
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonneg_of_nonpos ht (sub_nonpos.mpr (h0 s hs))))
          · rw [(μ₀.apply_eq_zero_iff s).mpr hs, zero_mul, zero_mul]
      _ = 1 := by simp only [mul_one, _root_.PMF.tsum_coe]
  | succ n ih =>
    have ih' := ih (fun i hi => hmean i (Nat.lt_succ_of_lt hi))
      (fun i hi => hrange i (Nat.lt_succ_of_lt hi))
    rw [chain_succ, tsum_bind_mul]
    set B := ENNReal.ofReal (Real.exp (t ^ 2 * c n ^ 2 / 8))
    have hstep (s : S) :
        chain μ₀ step n s *
            ∑' s', step n s s' * ENNReal.ofReal (Real.exp (t * (X (n + 1) s' - m))) ≤
          chain μ₀ step n s * ENNReal.ofReal (Real.exp (t * (X n s - m))) * B := by
      by_cases hs : s ∈ (chain μ₀ step n).support
      · have hsplit :
            (∑' s', step n s s' * ENNReal.ofReal (Real.exp (t * (X (n + 1) s' - m)))) =
              ENNReal.ofReal (Real.exp (t * (X n s - m))) *
                ∑' s', step n s s' *
                  ENNReal.ofReal (Real.exp (t * (X (n + 1) s' - X n s))) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun s' => ?_
          have hexp :
              Real.exp (t * (X (n + 1) s' - m)) =
                Real.exp (t * (X n s - m)) * Real.exp (t * (X (n + 1) s' - X n s)) := by
            rw [← Real.exp_add]; congr 1; ring
          rw [hexp, ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
        rw [hsplit, ← mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (tsum_mul_exp_le_of_tsum_toReal_mul_le_zero (step n s) _ ht
            (hmean n (Nat.lt_succ_self n) s hs) (hrange n (Nat.lt_succ_self n) s hs))
          zero_le
      · rw [((chain μ₀ step n).apply_eq_zero_iff s).mpr hs, zero_mul, zero_mul, zero_mul]
    calc ∑' s, chain μ₀ step n s *
            ∑' s', step n s s' * ENNReal.ofReal (Real.exp (t * (X (n + 1) s' - m)))
        ≤ ∑' s, chain μ₀ step n s * ENNReal.ofReal (Real.exp (t * (X n s - m))) * B :=
          tsum_le_tsum hstep
      _ = (∑' s, chain μ₀ step n s * ENNReal.ofReal (Real.exp (t * (X n s - m)))) * B :=
          ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i ∈ Finset.range n, c i ^ 2) / 8)) * B :=
          mul_le_mul' ih' le_rfl
      _ = ENNReal.ofReal (Real.exp (t ^ 2 * (∑ i ∈ Finset.range (n + 1), c i ^ 2) / 8)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Finset.sum_range_succ]
          congr 2
          ring

/-- **Azuma–Hoeffding inequality**, upper tail [Hoeffding1963; Azuma1967]: if `X` starts at most
`m` on `μ₀.support` and each round `i < n` has conditional expected increment at most `0` and
increment range of width `c i` on `(step i s).support`, then
`Pr[X n ≥ m + ε] ≤ exp (-2 ε² / ∑ i < n, c i²)` for every `ε ≥ 0`. -/
theorem azuma_le (μ₀ : PMF S) (step : ℕ → S → PMF S) (X : ℕ → S → ℝ) (c : ℕ → ℝ)
    {m ε : ℝ} (n : ℕ) (hε : 0 ≤ ε)
    (h0 : ∀ s ∈ μ₀.support, X 0 s ≤ m)
    (hmean : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      ∑' s', (step i s s').toReal * (X (i + 1) s' - X i s) ≤ 0)
    (hrange : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      ∃ a : ℝ, ∀ s' ∈ (step i s).support, X (i + 1) s' - X i s ∈ Set.Icc a (a + c i)) :
    ((chain μ₀ step n).toOuterMeasure {s | m + ε ≤ X n s}).toReal ≤
      Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range n, c i ^ 2) := by
  set V := ∑ i ∈ Finset.range n, c i ^ 2
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => sq_nonneg (c i)
  rcases hV.eq_or_lt with hV0 | hVpos
  · rw [← hV0, div_zero, Real.exp_zero]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using toOuterMeasure_le_one (chain μ₀ step n) {s | m + ε ≤ X n s})
  set t := 4 * ε / V
  have ht : 0 ≤ t := by positivity
  set E : Set S := {s | m + ε ≤ X n s}
  have hmarkov :
      (chain μ₀ step n).toOuterMeasure E ≤
        ENNReal.ofReal (Real.exp (-(t * ε))) *
          ∑' s, chain μ₀ step n s * ENNReal.ofReal (Real.exp (t * (X n s - m))) := by
    rw [_root_.PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun s => ?_
    by_cases hs : s ∈ E
    · have h1 : (1 : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.exp (-(t * ε))) *
            ENNReal.ofReal (Real.exp (t * (X n s - m))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
        have hs' : m + ε ≤ X n s := hs
        have : ε ≤ X n s - m := by linarith
        nlinarith
      calc E.indicator (chain μ₀ step n) s
          = chain μ₀ step n s * 1 := by rw [Set.indicator_of_mem hs, mul_one]
        _ ≤ chain μ₀ step n s *
              (ENNReal.ofReal (Real.exp (-(t * ε))) *
                ENNReal.ofReal (Real.exp (t * (X n s - m)))) :=
            mul_le_mul_of_nonneg_left h1 zero_le
        _ = ENNReal.ofReal (Real.exp (-(t * ε))) *
              (chain μ₀ step n s * ENNReal.ofReal (Real.exp (t * (X n s - m)))) := by ring
    · simp only [Set.indicator_of_notMem hs, zero_le]
  have hbound :
      (chain μ₀ step n).toOuterMeasure E ≤
        ENNReal.ofReal (Real.exp (-2 * ε ^ 2 / V)) := by
    refine hmarkov.trans ?_
    refine (mul_le_mul' le_rfl (tsum_chain_mul_exp_le μ₀ step X c n ht h0 hmean hrange)).trans_eq ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    dsimp only [t]
    field_simp
    ring
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hbound

/-- **Azuma–Hoeffding inequality**, lower tail: if `X` starts at least `m` on `μ₀.support` and each
round `i < n` has conditional expected increment at least `0` (a submartingale) and increment range
of width `c i` on `(step i s).support`, then
`Pr[X n ≤ m - ε] ≤ exp (-2 ε² / ∑ i < n, c i²)` for every `ε ≥ 0`. -/
theorem azuma_le_sub (μ₀ : PMF S) (step : ℕ → S → PMF S) (X : ℕ → S → ℝ) (c : ℕ → ℝ)
    {m ε : ℝ} (n : ℕ) (hε : 0 ≤ ε)
    (h0 : ∀ s ∈ μ₀.support, m ≤ X 0 s)
    (hmean : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      0 ≤ ∑' s', (step i s s').toReal * (X (i + 1) s' - X i s))
    (hrange : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      ∃ a : ℝ, ∀ s' ∈ (step i s).support, X (i + 1) s' - X i s ∈ Set.Icc a (a + c i)) :
    ((chain μ₀ step n).toOuterMeasure {s | X n s ≤ m - ε}).toReal ≤
      Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range n, c i ^ 2) := by
  have h := azuma_le μ₀ step (fun i s => -X i s) c (m := -m) n hε
    (fun s hs => neg_le_neg (h0 s hs))
    (fun i hi s hs => by
      have heq : (fun s' => (step i s s').toReal * (-X (i + 1) s' - -X i s)) =
          fun s' => -((step i s s').toReal * (X (i + 1) s' - X i s)) :=
        funext fun s' => by ring
      rw [heq, tsum_neg]
      exact neg_nonpos.mpr (hmean i hi s hs))
    (fun i hi s hs => by
      obtain ⟨a, ha⟩ := hrange i hi s hs
      exact ⟨-(a + c i), fun s' hs' => ⟨by linarith [(ha s' hs').2], by linarith [(ha s' hs').1]⟩⟩)
  have hevent : {s : S | -m + ε ≤ -X n s} = {s | X n s ≤ m - ε} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hle <;> linarith
  rwa [hevent] at h

/-- **Azuma–Hoeffding inequality**, two-sided martingale form: if `X 0 = m` on `μ₀.support` and
each round `i < n` has conditional expected increment `0` and increment range of width `c i` on
`(step i s).support`, then `Pr[|X n - m| ≥ ε] ≤ 2 exp (-2 ε² / ∑ i < n, c i²)`. -/
theorem azuma_abs_le (μ₀ : PMF S) (step : ℕ → S → PMF S) (X : ℕ → S → ℝ) (c : ℕ → ℝ)
    {m ε : ℝ} (n : ℕ) (hε : 0 ≤ ε)
    (h0 : ∀ s ∈ μ₀.support, X 0 s = m)
    (hmean : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      ∑' s', (step i s s').toReal * (X (i + 1) s' - X i s) = 0)
    (hrange : ∀ i < n, ∀ s ∈ (chain μ₀ step i).support,
      ∃ a : ℝ, ∀ s' ∈ (step i s).support, X (i + 1) s' - X i s ∈ Set.Icc a (a + c i)) :
    ((chain μ₀ step n).toOuterMeasure {s | ε ≤ |X n s - m|}).toReal ≤
      2 * Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range n, c i ^ 2) := by
  linarith [toOuterMeasure_abs_sub_ge_toReal_le (chain μ₀ step n) (X n) m ε,
    azuma_le μ₀ step X c n hε (fun s hs => (h0 s hs).le)
      (fun i hi s hs => (hmean i hi s hs).le) hrange,
    azuma_le_sub μ₀ step X c n hε (fun s hs => (h0 s hs).ge)
      (fun i hi s hs => (hmean i hi s hs).ge) hrange]

end Azuma

end Cslib.Probability.PMF

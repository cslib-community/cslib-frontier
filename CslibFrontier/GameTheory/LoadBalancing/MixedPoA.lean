/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.LoadBalancing.MixedNash
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogDivLogLog
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Event
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mixed Nash price of anarchy upper bound on identical machines

This module formalizes the `O(log m / log log m)` upper bound on the mixed Nash price of anarchy
for selfish load balancing on `m ≥ 3` identical machines ([KoutsoupiasPapadimitriou1999];
[CzumajVocking2002]; [Vocking2007], Theorem 20.13 and Lemma 20.14; locator not re-verified against
primary PDF), matching the `Ω(log m / log log m)` lower bound in
`CslibFrontier.GameTheory.LoadBalancing.BallsIntoBins`.

## Proof overview

Let `G` be a load-balancing game on `m = |M| ≥ 3` identical machines (`G.IsIdentical`) and let `p`
be any mixed Nash equilibrium of `G`. When `optMakespan = 0`, all jobs have weight `0` and
`expectedMakespan p = 0`. Otherwise `0 < OPT = G.optMakespan`, and:

1. **Expected-load bound** (`IsIdentical.expectedLoad_le_two_mul_optMakespan`): every machine `j`
   satisfies `E[ℓ_j] ≤ 2 * OPT`. Indeed, if `E[ℓ_j] > 0`, some job `i` has `0 < p i j`, and
   summing the mixed Nash inequality `E[ℓ_j] ≤ E[ℓ_k] + w_i` over all `k : M` yields
   `m * E[ℓ_j] ≤ ∑ w_r + m * w_i ≤ 2 * m * OPT`.
2. **Weighted Chernoff bound** (`IsIdentical.prob_load_ge_le_exp_chernoff`, [Vocking2007],
   Lemma 20.14): bridging `productWeight p` to `Cslib.Probability.PMF.pi` and applying the
   multiplicative Chernoff bound `Cslib.Probability.PMF.pi_sum_ge_one_add_mul_le_exp_log` to the
   independent `[0, 1]`-valued normalized load contributions `X_i(A) = 1_{A i = j} * (w_i / OPT)`
   (whose mean is `E[ℓ_j] / OPT ≤ 2`) yields
   `Pr[ℓ_j ≥ c * OPT] ≤ exp (c - 2 - c * log (c / 2))` for every `c ≥ 2`.
3. **Union bound and expectation**
   (`IsIdentical.expectedMakespan_le_log_div_log_log`, [Vocking2007],
   Theorem 20.13): setting `T = 12 * log m / log (log m)` satisfies
   `T * (log (T / 2) - 1) ≥ 6 * log m ≥ 2 * log m`, so each machine exceeds `T * OPT` with
   probability at most `1 / m ^ 2`. By the union bound, `Pr[makespan ≥ T * OPT] ≤ 1 / m`, and since
   `makespan A ≤ ∑ w_i ≤ m * OPT` deterministically,
   `E[makespan] ≤ T * OPT + (m * OPT) * (1 / m) = (12 * log m / log (log m) + 1) * OPT`.

## Main results

* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.expectedLoad_le_two_mul_optMakespan`: every
  machine has expected load at most `2 * optMakespan` in any identical-machine mixed NE.
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.prob_load_ge_le_exp_chernoff` ([Vocking2007],
  Lemma 20.14): weighted Chernoff upper tail on any single machine's load in a mixed NE.
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.expectedMakespan_le_log_div_log_log`
  ([KoutsoupiasPapadimitriou1999]; [CzumajVocking2002]; [Vocking2007], Theorem 20.13): for
  `3 ≤ |M|` identical machines, every mixed Nash equilibrium satisfies
  `expectedMakespan p ≤ (12 * log |M| / log (log |M|) + 1) * optMakespan`.

## References

* [CzumajVocking2002]
* [KoutsoupiasPapadimitriou1999]
* [MitzenmacherUpfal2017]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory.LoadBalancingGame

open Finset

section IdenticalMixedPoA

/-- Convert a mixed strategy `q : M → ℝ` into a `PMF M`. -/
private noncomputable def mixedStrategyToPMF {M : Type*} [Fintype M] {q : M → ℝ}
    (hq : IsMixedStrategy q) : PMF M :=
  PMF.ofFintype (fun j => ENNReal.ofReal (q j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq.nonneg j), hq.sum_eq_one, ENNReal.ofReal_one])

private theorem mixedStrategyToPMF_toReal {M : Type*} [Fintype M] {q : M → ℝ}
    (hq : IsMixedStrategy q) (j : M) :
    (mixedStrategyToPMF hq j).toReal = q j := by
  simp only [mixedStrategyToPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hq.nonneg j)]

private theorem pi_mixedStrategyToPMF_toReal {ι M : Type*} [Fintype ι] [Fintype M]
    {p : ι → M → ℝ} (hp : ∀ i, IsMixedStrategy (p i)) (A : ι → M) :
    (Cslib.Probability.PMF.pi (fun i => mixedStrategyToPMF (hp i)) A).toReal =
      productWeight p A := by
  rw [Cslib.Probability.PMF.pi_apply, productWeight_def, ENNReal.toReal_prod]
  exact prod_congr rfl fun i _ => mixedStrategyToPMF_toReal (hp i) (A i)

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M]

/-- **Expected-load bound in identical-machine mixed Nash equilibria**: in any mixed Nash
equilibrium `p` on identical machines, every machine `j` has `expectedLoad p j ≤ 2 * optMakespan`.
-/
theorem IsIdentical.expectedLoad_le_two_mul_optMakespan {G : LoadBalancingGame ι M}
    (hId : G.IsIdentical) {p : ι → M → ℝ} (hp : G.toCostGame.IsMixedNash p) (j : M) :
    G.expectedLoad p j ≤ 2 * G.optMakespan := by
  have hp1 : ∀ i, ∑ k, p i k = 1 := fun i => (hp.1 i).sum_eq_one
  by_cases hpos : ∃ i : ι, 0 < p i j
  · obtain ⟨i, hij⟩ := hpos
    have hle_k : ∀ k : M, G.expectedLoad p j ≤ G.expectedLoad p k + G.weight i := fun k => by
      have hNE := ((G.isMixedNash_iff p).mp hp).2 i j hij k
      rw [hId j, hId k, div_one] at hNE
      have hpij_le1 : p i j ≤ 1 := by
        rw [← hp1 i]
        exact single_le_sum (fun m _ => (hp.1 i).nonneg m) (mem_univ j)
      have h1 : 0 ≤ (1 - p i j) * G.weight i :=
        mul_nonneg (sub_nonneg.mpr hpij_le1) (G.weight_nonneg i)
      have h2 : (1 - p i k) * G.weight i ≤ G.weight i := by
        nlinarith [(hp.1 i).nonneg k, G.weight_nonneg i]
      linarith
    have hsum : (Fintype.card M : ℝ) * G.expectedLoad p j ≤
        (∑ k : M, G.expectedLoad p k) + (Fintype.card M : ℝ) * G.weight i := by
      calc (Fintype.card M : ℝ) * G.expectedLoad p j
          = ∑ _k : M, G.expectedLoad p j := by
              rw [sum_const, card_univ, nsmul_eq_mul]
        _ ≤ ∑ k : M, (G.expectedLoad p k + G.weight i) := sum_le_sum fun k _ => hle_k k
        _ = (∑ k : M, G.expectedLoad p k) + (Fintype.card M : ℝ) * G.weight i := by
              rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
    have hsum_load : ∑ k : M, G.expectedLoad p k = ∑ r : ι, G.weight r := by
      have h := G.sum_speed_mul_expectedLoad hp1
      simp_rw [hId _, one_mul] at h
      exact h
    have hvol := hId.sum_weight_le_card_mul_optMakespan
    have hwi := hId.weight_le_optMakespan i
    have hm_pos : (0 : ℝ) < (Fintype.card M : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    nlinarith
  · push Not at hpos
    have h0 : G.expectedLoad p j = 0 := by
      rw [expectedLoad]
      refine sum_eq_zero fun i _ => ?_
      have hpij0 : p i j = 0 := le_antisymm (hpos i) ((hp.1 i).nonneg j)
      rw [hpij0, zero_mul]
    rw [h0]
    linarith [G.optMakespan_nonneg]

/-- **Weighted Chernoff upper tail on a single machine's load** ([Vocking2007], Lemma 20.14;
locator not re-verified against primary PDF): for any mixed Nash equilibrium `p` on identical
machines with `0 < optMakespan`, any machine `j`, and any `c ≥ 2`,
`Pr[load A j ≥ c * optMakespan] ≤ exp (c - 2 - c * log (c / 2))`. -/
theorem IsIdentical.prob_load_ge_le_exp_chernoff {G : LoadBalancingGame ι M} (hId : G.IsIdentical)
    {p : ι → M → ℝ} (hp : G.toCostGame.IsMixedNash p) (hopt : 0 < G.optMakespan) (j : M)
    {c : ℝ} (hc : 2 ≤ c) :
    (∑ A : ι → M, if c * G.optMakespan ≤ G.load A j then productWeight p A else 0) ≤
      Real.exp (c - 2 - c * Real.log (c / 2)) := by
  let pmf : ι → PMF M := fun i => mixedStrategyToPMF (hp.1 i)
  let score : ι → M → ℝ := fun i a => if a = j then G.weight i / G.optMakespan else 0
  have hscore : ∀ i a, a ∈ (pmf i).support → score i a ∈ Set.Icc 0 1 := fun i a _ => by
    simp only [score]
    split_ifs
    · exact ⟨div_nonneg (G.weight_nonneg i) hopt.le,
        (div_le_one hopt).mpr (hId.weight_le_optMakespan i)⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hmean : ∑ i : ι, ∑ a : M, (pmf i a).toReal * score i a ≤ 2 := by
    have hsum_eq : ∑ i : ι, ∑ a : M, (pmf i a).toReal * score i a =
        G.expectedLoad p j / G.optMakespan := by
      rw [expectedLoad, sum_div]
      refine sum_congr rfl fun i _ => ?_
      simp only [pmf, score, mul_ite, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte,
        mixedStrategyToPMF_toReal, hId j, div_one]
      ring
    rw [hsum_eq, div_le_iff₀ hopt]
    exact hId.expectedLoad_le_two_mul_optMakespan hp j
  have hδ : 0 ≤ c / 2 - 1 := by linarith
  have hchernoff :=
    Cslib.Probability.PMF.pi_sum_ge_one_add_mul_le_exp_log pmf score hscore hmean hδ
  have hmul_eq : (1 + (c / 2 - 1)) * 2 = c := by ring
  have hexp_eq : 2 * (c / 2 - 1 - (1 + (c / 2 - 1)) * Real.log (1 + (c / 2 - 1))) =
      c - 2 - c * Real.log (c / 2) := by
    have h1 : 1 + (c / 2 - 1) = c / 2 := by ring
    rw [h1]
    ring
  rw [hmul_eq, hexp_eq] at hchernoff
  have hprob_eq :
      ((Cslib.Probability.PMF.pi pmf).toOuterMeasure
          {A : ι → M | c ≤ ∑ i : ι, score i (A i)}).toReal =
        ∑ A : ι → M, if c * G.optMakespan ≤ G.load A j then productWeight p A else 0 := by
    rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
    refine sum_congr rfl fun A _ => ?_
    have hsum_score : ∑ i : ι, score i (A i) = G.load A j / G.optMakespan := by
      rw [G.load_eq_sum_div, hId j, div_one, sum_filter, sum_div]
      refine sum_congr rfl fun i _ => ?_
      simp only [score]
      split_ifs <;> simp
    have hiff : A ∈ {A : ι → M | c ≤ ∑ i : ι, score i (A i)} ↔
        c * G.optMakespan ≤ G.load A j := by
      simp only [Set.mem_ofPred_eq, hsum_score, le_div_iff₀ hopt]
    rw [pi_mixedStrategyToPMF_toReal (hp.1) A]
    by_cases h : c * G.optMakespan ≤ G.load A j
    · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]
  rwa [hprob_eq] at hchernoff

/-- **Identical-machine mixed price of anarchy upper bound** ([KoutsoupiasPapadimitriou1999];
[CzumajVocking2002]; [Vocking2007], Theorem 20.13; locator not re-verified against primary PDF):
for every load-balancing game on `m = |M| ≥ 3` identical machines and every mixed Nash equilibrium
`p`,
`expectedMakespan p ≤ (12 * log m / log (log m) + 1) * optMakespan = O(log m / log log m) * OPT`.
-/
theorem IsIdentical.expectedMakespan_le_log_div_log_log
    {G : LoadBalancingGame ι M} (hId : G.IsIdentical) (hm : 3 ≤ Fintype.card M)
    {p : ι → M → ℝ} (hp : G.toCostGame.IsMixedNash p) :
    G.expectedMakespan p ≤
      (12 * Real.log (Fintype.card M) / Real.log (Real.log (Fintype.card M)) + 1) *
        G.optMakespan := by
  set m : ℕ := Fintype.card M
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm_gt1 : 1 < Real.log (m : ℝ) := Real.one_lt_log_of_three_le hm3
  have hloglog_pos : 0 < Real.log (Real.log (m : ℝ)) := Real.log_pos hlogm_gt1
  rcases G.optMakespan_nonneg.eq_or_lt with hopt0 | hopt_pos
  · rw [G.expectedMakespan_eq_zero_of_optMakespan_eq_zero hopt0.symm p, ← hopt0, mul_zero]
  · -- Main case `0 < optMakespan`.
    set x : ℝ := Real.log (m : ℝ)
    set T : ℝ := 12 * x / Real.log x
    -- Show `√x < T / 6`, hence `T > 6 ≥ 2` and `T * (log (T / 2) - 1) ≥ 6 * x ≥ 2 * x`.
    have hsqrt_pos : 0 < √x := Real.sqrt_pos.mpr (by linarith)
    have hsqrt_gt1 : 1 < √x := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) hlogm_gt1
    have hlogx_lt : Real.log x < 2 * √x := by
      have h1 : Real.log (√x) ≤ √x - 1 := Real.log_le_sub_one_of_pos hsqrt_pos
      have h2 : Real.log (√x) = Real.log x / 2 := Real.log_sqrt (by linarith)
      linarith
    have hT6_gt : √x < T / 6 := by
      have hT6 : T / 6 = 2 * x / Real.log x := by simp only [T]; ring
      rw [hT6, lt_div_iff₀ hloglog_pos]
      have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
      nlinarith
    have hT_ge2 : 2 ≤ T := by linarith
    have hlog3_gt1 : 1 < Real.log 3 := Real.one_lt_log_of_three_le le_rfl
    have hlogT2 : Real.log x / 2 + 1 < Real.log (T / 2) := by
      have hT2_eq : T / 2 = 3 * (T / 6) := by ring
      rw [hT2_eq, Real.log_mul (by norm_num) (by linarith)]
      have hlog_T6 : Real.log x / 2 < Real.log (T / 6) := by
        rw [← Real.log_sqrt (by linarith)]
        exact Real.log_lt_log hsqrt_pos hT6_gt
      linarith
    have hexp_bound : T - 2 - T * Real.log (T / 2) ≤ -(2 * x) := by
      have hmul : T * (Real.log x / 2) < T * (Real.log (T / 2) - 1) :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      have hT_prod : T * (Real.log x / 2) = 6 * x := by
        simp only [T]
        field_simp [hloglog_pos.ne']
        ring
      linarith
    have hmachine_tail : ∀ j : M,
        (∑ A : ι → M, if T * G.optMakespan ≤ G.load A j then productWeight p A else 0) ≤
          1 / (m : ℝ) ^ 2 := fun j => by
      calc (∑ A : ι → M, if T * G.optMakespan ≤ G.load A j then productWeight p A else 0)
          ≤ Real.exp (T - 2 - T * Real.log (T / 2)) :=
            hId.prob_load_ge_le_exp_chernoff hp hopt_pos j hT_ge2
        _ ≤ Real.exp (-(2 * x)) := Real.exp_le_exp.mpr hexp_bound
        _ = 1 / (m : ℝ) ^ 2 := by
            rw [Real.exp_neg,
              show (2 : ℝ) * x = ((2 : ℕ) : ℝ) * Real.log (m : ℝ) by simp only [x]; norm_num,
              Real.exp_nat_mul, Real.exp_log hm_pos, one_div]
    -- Union bound over all `m` machines: `Pr[makespan A ≥ T * optMakespan] ≤ 1 / m`.
    have hunion :
        (∑ A : ι → M, if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0) ≤
          1 / (m : ℝ) := by
      have hpt : ∀ A : ι → M,
          (if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0) ≤
            ∑ j : M, if T * G.optMakespan ≤ G.load A j then productWeight p A else 0 := fun A => by
        have hw_nn : 0 ≤ productWeight p A := productWeight_nonneg (fun i => (hp.1 i).nonneg) A
        split_ifs with hms
        · obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
          refine single_le_sum (f := fun j =>
              if T * G.optMakespan ≤ G.load A j then productWeight p A else 0)
            (fun j _ => by split_ifs <;> linarith) (mem_univ jstar) |>.trans' ?_
          rw [ite_eq_left (hjstar.symm ▸ hms)]
        · exact sum_nonneg fun j _ => by split_ifs <;> linarith
      calc (∑ A : ι → M, if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0)
          ≤ ∑ A : ι → M, ∑ j : M,
              if T * G.optMakespan ≤ G.load A j then productWeight p A else 0 :=
            sum_le_sum fun A _ => hpt A
        _ = ∑ j : M, ∑ A : ι → M,
              if T * G.optMakespan ≤ G.load A j then productWeight p A else 0 := sum_comm
        _ ≤ ∑ _j : M, (1 / (m : ℝ) ^ 2) := sum_le_sum fun j _ => hmachine_tail j
        _ = (m : ℝ) * (1 / (m : ℝ) ^ 2) := by
            rw [sum_const, card_univ, nsmul_eq_mul]
        _ = 1 / (m : ℝ) := by field_simp
    -- Deterministic upper bound: `makespan A ≤ ∑ i, weight i ≤ m * optMakespan`.
    have hms_le_m : ∀ A : ι → M, G.makespan A ≤ (m : ℝ) * G.optMakespan := fun A => by
      refine ((G.makespan_le_iff A).mpr fun j => ?_).trans hId.sum_weight_le_card_mul_optMakespan
      rw [G.load_eq_sum_div, hId j, div_one]
      exact sum_le_univ_sum_of_nonneg fun i => G.weight_nonneg i
    -- Split `expectedMakespan p` at `T * optMakespan`.
    have hp1 : ∀ i, ∑ j, p i j = 1 := fun i => (hp.1 i).sum_eq_one
    have hsplit_pt : ∀ A : ι → M,
        productWeight p A * G.makespan A ≤
          productWeight p A * (T * G.optMakespan) +
            ((m : ℝ) * G.optMakespan) *
              (if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0) := fun A => by
      have hw_nn : 0 ≤ productWeight p A := productWeight_nonneg (fun i => (hp.1 i).nonneg) A
      by_cases h : T * G.optMakespan ≤ G.makespan A
      · rw [ite_eq_left h]
        have h1 : productWeight p A * G.makespan A ≤
            productWeight p A * ((m : ℝ) * G.optMakespan) :=
          mul_le_mul_of_nonneg_left (hms_le_m A) hw_nn
        have h2 : 0 ≤ productWeight p A * (T * G.optMakespan) := by positivity
        linarith
      · rw [ite_eq_right h, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left (le_of_not_ge h) hw_nn
    calc G.expectedMakespan p
        = ∑ A : ι → M, productWeight p A * G.makespan A := rfl
      _ ≤ ∑ A : ι → M,
            (productWeight p A * (T * G.optMakespan) +
              ((m : ℝ) * G.optMakespan) *
                (if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0)) :=
          sum_le_sum fun A _ => hsplit_pt A
      _ = (∑ A : ι → M, productWeight p A) * (T * G.optMakespan) +
            ((m : ℝ) * G.optMakespan) *
              (∑ A : ι → M, if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0) := by
          rw [sum_add_distrib, ← sum_mul, ← mul_sum]
      _ ≤ 1 * (T * G.optMakespan) + ((m : ℝ) * G.optMakespan) * (1 / (m : ℝ)) := by
          rw [sum_productWeight hp1]
          gcongr
      _ = (T + 1) * G.optMakespan := by
          field_simp [hm_pos.ne']

end IdenticalMixedPoA

end Cslib.GameTheory.LoadBalancingGame

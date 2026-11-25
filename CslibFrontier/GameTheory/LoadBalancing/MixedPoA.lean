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
# Mixed Nash price of anarchy upper bounds and weighted Chernoff tail

This module formalizes the weighted Chernoff tail lemma for load-balancing mixed profiles
([Vocking2007], Lemma 20.14; locator not re-verified against primary PDF), the
`O(log m / log log m)` upper bound on the mixed Nash price of anarchy for selfish load balancing
on `m ≥ 3` identical machines ([KoutsoupiasPapadimitriou1999]; [CzumajVocking2002]; [Vocking2007],
Theorem 20.13), and the constant-factor `O(optMakespan)` upper bound when all job weights on
identical machines are at most `optMakespan / log m` ([Vocking2007], Exercise 20.6(b)).

## Proof overview

1. **Weighted Chernoff bound** (`prob_subset_load_ge_le_exp`, [Vocking2007], Lemma 20.14):
   bridging `productWeight p` to `Cslib.Probability.PMF.pi` and applying
   `Cslib.Probability.PMF.pi_sum_ge_one_add_mul_le_exp_log` to the independent `[0, 1]`-valued
   normalized load contributions `X_i(A) = 1_{i ∈ S ∧ A i = j} * (w_i / s_j) / z` yields
   `Pr[∑_{i ∈ S, A i = j} w_i / s_j ≥ t] ≤ exp ((t - μ - t * log (t / μ)) / z)` whenever
   `w_i / s_j ≤ z` on `S` (with `p i j > 0`), the subset's expected load is at most `μ > 0`, and
   `μ ≤ t`. This general form is shared by identical-machine bounds here and by the uniformly
   related mixed PoA proof in `CslibFrontier.GameTheory.LoadBalancing.RelatedMixedPoA`.
2. **Expected-load bound** (`IsIdentical.expectedLoad_le_two_mul_optMakespan`): every machine `j`
   on identical machines satisfies `E[ℓ_j] ≤ 2 * OPT`.
3. **Identical-machine mixed PoA** (`IsIdentical.expectedMakespan_le_log_div_log_log`,
   [Vocking2007], Theorem 20.13): setting `T = 12 * log m / log (log m)` with `z = OPT` gives
   `Pr[ℓ_j ≥ T * OPT] ≤ 1 / m ^ 2`, union bound `Pr[makespan ≥ T * OPT] ≤ 1 / m`, and hence
   `expectedMakespan p ≤ (12 * log m / log (log m) + 1) * OPT`.
4. **Small-weight identical-machine mixed PoA**
   (`IsIdentical.expectedMakespan_le_seven_mul_optMakespan_of_weight_le`, [Vocking2007],
   Exercise 20.6(b)): when `w_i ≤ OPT / log m` for every job (`m ≥ 2`), setting `z = OPT / log m`
   and `T = 6` gives `Pr[ℓ_j ≥ 6 * OPT] ≤ exp ((4 - 6 * log 3) * log m) ≤ 1 / m ^ 2`, yielding
   `expectedMakespan p ≤ 7 * OPT`.

## Main results

* `Cslib.GameTheory.LoadBalancingGame.weight_eq_zero_of_optMakespan_eq_zero`,
  `Cslib.GameTheory.LoadBalancingGame.expectedMakespan_eq_zero_of_optMakespan_eq_zero`: when
  `optMakespan = 0`, every job has weight `0` and every mixed strategy profile has
  `expectedMakespan = 0`.
* `Cslib.GameTheory.LoadBalancingGame.prob_subset_load_ge_le_exp` ([Vocking2007], Lemma 20.14):
  weighted Chernoff upper tail on the load contributed to machine `j` by any subset `S` of jobs
  with per-job load cap `z > 0`.
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.expectedLoad_le_two_mul_optMakespan`: every
  machine has expected load at most `2 * optMakespan` in any identical-machine mixed NE.
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.prob_load_ge_le_exp_chernoff` ([Vocking2007],
  Lemma 20.14): weighted Chernoff upper tail on any single machine's load in an identical-machine
  mixed NE.
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.expectedMakespan_le_log_div_log_log`
  ([KoutsoupiasPapadimitriou1999]; [CzumajVocking2002]; [Vocking2007], Theorem 20.13): for
  `3 ≤ |M|` identical machines, every mixed Nash equilibrium satisfies
  `expectedMakespan p ≤ (12 * log |M| / log (log |M|) + 1) * optMakespan`.
* `IsIdentical.expectedMakespan_le_seven_mul_optMakespan_of_weight_le`
  ([Vocking2007], Exercise 20.6(b)): for `2 ≤ |M|` identical machines where every job satisfies
  `weight i ≤ optMakespan / log |M|`, every mixed Nash equilibrium satisfies
  `expectedMakespan p ≤ 7 * optMakespan`.

## References

* [CzumajVocking2002]
* [KoutsoupiasPapadimitriou1999]
* [MitzenmacherUpfal2017]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory.LoadBalancingGame

open Finset

section WeightedChernoff

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

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]

/-- **Weighted Chernoff upper tail on a subset of jobs** ([Vocking2007], Lemma 20.14; locator not
re-verified against primary PDF): under a product of mixed strategies `p`, for any machine `j`,
subset of jobs `S`, per-job load cap `z > 0` on jobs in `S` with positive probability on `j`,
mean upper bound `0 < μ`, and threshold `t ≥ μ`, the probability that the jobs in `S` assigned to
`j` contribute load at least `t` is at most `exp ((t - μ - t * log (t / μ)) / z)`. -/
theorem prob_subset_load_ge_le_exp (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : ∀ i, IsMixedStrategy (p i)) (j : M) (S : Finset ι) {z μ t : ℝ}
    (hz : 0 < z) (hμ_pos : 0 < μ) (ht : μ ≤ t)
    (hcap : ∀ i ∈ S, 0 < p i j → G.weight i / G.speed j ≤ z)
    (hmean : ∑ i ∈ S, p i j * (G.weight i / G.speed j) ≤ μ) :
    (∑ A : ι → M,
        if t ≤ ∑ i ∈ S with A i = j, G.weight i / G.speed j then productWeight p A else 0) ≤
      Real.exp ((t - μ - t * Real.log (t / μ)) / z) := by
  let pmf : ι → PMF M := fun i => mixedStrategyToPMF (hp i)
  let score : ι → M → ℝ := fun i a =>
    if i ∈ S ∧ a = j then (G.weight i / G.speed j) / z else 0
  have hscore : ∀ i a, a ∈ (pmf i).support → score i a ∈ Set.Icc 0 1 := fun i a ha => by
    simp only [score]
    split_ifs with h
    · obtain ⟨hiS, rfl⟩ := h
      have hpij_pos : 0 < p i a := by
        by_contra hle
        exact (PMF.mem_support_iff (pmf i) a).mp ha
          (by simp [pmf, mixedStrategyToPMF, ENNReal.ofReal_eq_zero, not_lt.mp hle])
      exact ⟨div_nonneg (div_nonneg (G.weight_nonneg i) (G.speed_pos a).le) hz.le,
        (div_le_one hz).mpr (hcap i hiS hpij_pos)⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hmean' : ∑ i : ι, ∑ a : M, (pmf i a).toReal * score i a ≤ μ / z := by
    refine (?_ : _ = (∑ i ∈ S, p i j * (G.weight i / G.speed j)) / z).trans_le
      (div_le_div_of_nonneg_right hmean hz.le)
    have hsub1 : ∑ i ∈ S, p i j * (G.weight i / G.speed j) / z =
        ∑ i : ι, if i ∈ S then p i j * (G.weight i / G.speed j) / z else 0 := by
      rw [← sum_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext
      simp
    rw [sum_div, hsub1]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single j (fun a _ ha => by simp [score, ha]) (by simp)]
    by_cases hi : i ∈ S <;> simp [score, pmf, hi, mixedStrategyToPMF_toReal, mul_div_assoc]
  have hδ : 0 ≤ t / μ - 1 := sub_nonneg.mpr ((one_le_div hμ_pos).mpr ht)
  have hchernoff :=
    Cslib.Probability.PMF.pi_sum_ge_one_add_mul_le_exp_log pmf score hscore hmean' hδ
  have hmul_eq : (1 + (t / μ - 1)) * (μ / z) = t / z := by field_simp [hμ_pos.ne', hz.ne']; ring
  have hexp_eq :
      (μ / z) * (t / μ - 1 - (1 + (t / μ - 1)) * Real.log (1 + (t / μ - 1))) =
        (t - μ - t * Real.log (t / μ)) / z := by
    rw [show 1 + (t / μ - 1) = t / μ by ring]
    field_simp [hμ_pos.ne', hz.ne']
  rw [hmul_eq, hexp_eq] at hchernoff
  refine (?_ : _ = ((Cslib.Probability.PMF.pi pmf).toOuterMeasure
      {A : ι → M | t / z ≤ ∑ i : ι, score i (A i)}).toReal).trans_le hchernoff
  rw [Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  refine sum_congr rfl fun A _ => ?_
  have hsum_score : ∑ i : ι, score i (A i) =
      (∑ i ∈ S with A i = j, G.weight i / G.speed j) / z := by
    have hsub2 : ∑ i ∈ S, (if A i = j then G.weight i / G.speed j else 0) / z =
        ∑ i : ι, if i ∈ S then (if A i = j then G.weight i / G.speed j else 0) / z else 0 := by
      rw [← sum_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext
      simp
    rw [sum_filter, sum_div, hsub2]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> by_cases hA : A i = j <;> simp [score, hi, hA]
  simp only [Set.mem_ofPred_eq, hsum_score, div_le_div_iff_of_pos_right hz]
  rw [pi_mixedStrategyToPMF_toReal hp A]

end WeightedChernoff

section IdenticalMixedPoA

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
    have hle_k (k : M) : G.expectedLoad p j ≤ G.expectedLoad p k + G.weight i := by
      have hNE := ((G.isMixedNash_iff p).mp hp).2 i j hij k
      rw [hId j, hId k, div_one] at hNE
      have hpij_le1 : p i j ≤ 1 :=
        hp1 i ▸ single_le_sum (fun m _ => (hp.1 i).nonneg m) (mem_univ j)
      nlinarith [(hp.1 i).nonneg k, G.weight_nonneg i]
    have hload := G.sum_speed_mul_expectedLoad hp1
    simp_rw [hId _, one_mul] at hload
    have hsum : (Fintype.card M : ℝ) * G.expectedLoad p j ≤
        (∑ r : ι, G.weight r) + (Fintype.card M : ℝ) * G.weight i :=
      calc (Fintype.card M : ℝ) * G.expectedLoad p j
          = ∑ _k : M, G.expectedLoad p j := by rw [sum_const, card_univ, nsmul_eq_mul]
        _ ≤ ∑ k : M, (G.expectedLoad p k + G.weight i) := sum_le_sum fun k _ => hle_k k
        _ = (∑ r : ι, G.weight r) + (Fintype.card M : ℝ) * G.weight i := by
              rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hload]
    have hm_pos : (0 : ℝ) < Fintype.card M := Nat.cast_pos.mpr Fintype.card_pos
    nlinarith [hId.sum_weight_le_card_mul_optMakespan, hId.weight_le_optMakespan i]
  · push Not at hpos
    rw [expectedLoad, sum_eq_zero fun i _ => by
      rw [le_antisymm (hpos i) ((hp.1 i).nonneg j), zero_mul]]
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
  have h := G.prob_subset_load_ge_le_exp hp.1 j univ hopt (by linarith : 0 < 2 * G.optMakespan)
    (by nlinarith : 2 * G.optMakespan ≤ c * G.optMakespan)
    (fun i _ _ => by rw [hId j, div_one]; exact hId.weight_le_optMakespan i)
    (hId.expectedLoad_le_two_mul_optMakespan hp j)
  have hload : ∀ A : ι → M,
      (∑ i ∈ (univ : Finset ι) with A i = j, G.weight i / G.speed j) = G.load A j :=
    fun _ => rfl
  have hrhs :
      (c * G.optMakespan - 2 * G.optMakespan -
          c * G.optMakespan * Real.log (c * G.optMakespan / (2 * G.optMakespan))) /
        G.optMakespan = c - 2 - c * Real.log (c / 2) := by
    have hdiv : c * G.optMakespan / (2 * G.optMakespan) = c / 2 := by
      field_simp [hopt.ne']
    rw [hdiv]
    field_simp [hopt.ne']
  simpa only [hload, hrhs] using h

/-- Shared union-bound and expectation split on identical machines: if every machine exceeds
`T * optMakespan` with probability at most `1 / |M| ^ 2`, then
`expectedMakespan p ≤ (T + 1) * optMakespan`. -/
private theorem IsIdentical.expectedMakespan_le_add_one_of_machine_tail
    {G : LoadBalancingGame ι M} (hId : G.IsIdentical) {p : ι → M → ℝ}
    (hp : ∀ i, IsMixedStrategy (p i)) {T : ℝ} (hT : 0 ≤ T)
    (htail : ∀ j : M,
      (∑ A : ι → M, if T * G.optMakespan ≤ G.load A j then productWeight p A else 0) ≤
        1 / (Fintype.card M : ℝ) ^ 2) :
    G.expectedMakespan p ≤ (T + 1) * G.optMakespan := by
  set m : ℕ := Fintype.card M
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => (hp i).nonneg j
  have hp1 : ∀ i, ∑ j, p i j = 1 := fun i => (hp i).sum_eq_one
  have hunion :
      (∑ A : ι → M, if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0) ≤
        1 / (m : ℝ) := by
    have hpt : ∀ A : ι → M,
        (if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0) ≤
          ∑ j : M, if T * G.optMakespan ≤ G.load A j then productWeight p A else 0 := fun A => by
      have hw_nn : 0 ≤ productWeight p A := productWeight_nonneg hp0 A
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
      _ ≤ ∑ _j : M, (1 / (m : ℝ) ^ 2) := sum_le_sum fun j _ => htail j
      _ = (m : ℝ) * (1 / (m : ℝ) ^ 2) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ = 1 / (m : ℝ) := by field_simp
  have hms_le_m : ∀ A : ι → M, G.makespan A ≤ (m : ℝ) * G.optMakespan := fun A => by
    refine ((G.makespan_le_iff A).mpr fun j => ?_).trans hId.sum_weight_le_card_mul_optMakespan
    rw [G.load_eq_sum_div, hId j, div_one]
    exact sum_le_univ_sum_of_nonneg fun i => G.weight_nonneg i
  have hopt_nn : 0 ≤ G.optMakespan := G.optMakespan_nonneg
  have hsplit_pt : ∀ A : ι → M,
      productWeight p A * G.makespan A ≤
        productWeight p A * (T * G.optMakespan) +
          ((m : ℝ) * G.optMakespan) *
            (if T * G.optMakespan ≤ G.makespan A then productWeight p A else 0) := fun A => by
    have hw_nn : 0 ≤ productWeight p A := productWeight_nonneg hp0 A
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
  · set x : ℝ := Real.log (m : ℝ)
    set T : ℝ := 12 * x / Real.log x
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
    refine hId.expectedMakespan_le_add_one_of_machine_tail hp.1 (by linarith) fun j => ?_
    calc (∑ A : ι → M, if T * G.optMakespan ≤ G.load A j then productWeight p A else 0)
        ≤ Real.exp (T - 2 - T * Real.log (T / 2)) :=
          hId.prob_load_ge_le_exp_chernoff hp hopt_pos j hT_ge2
      _ ≤ Real.exp (-(2 * x)) := Real.exp_le_exp.mpr hexp_bound
      _ = 1 / (m : ℝ) ^ 2 := by
          rw [Real.exp_neg,
            show (2 : ℝ) * x = ((2 : ℕ) : ℝ) * Real.log (m : ℝ) by simp only [x]; norm_num,
            Real.exp_nat_mul, Real.exp_log hm_pos, one_div]

/-- **Small-weight identical-machine mixed PoA** ([Vocking2007], Exercise 20.6(b); locator not
re-verified against primary PDF): on `m = |M| ≥ 2` identical machines, if every job has weight at
most `optMakespan / log m`, then every mixed Nash equilibrium `p` satisfies
`expectedMakespan p ≤ 7 * optMakespan = O(optMakespan)`. -/
theorem IsIdentical.expectedMakespan_le_seven_mul_optMakespan_of_weight_le
    {G : LoadBalancingGame ι M} (hId : G.IsIdentical) (hm : 2 ≤ Fintype.card M)
    {p : ι → M → ℝ} (hp : G.toCostGame.IsMixedNash p)
    (hw : ∀ i, G.weight i ≤ G.optMakespan / Real.log (Fintype.card M)) :
    G.expectedMakespan p ≤ 7 * G.optMakespan := by
  set m : ℕ := Fintype.card M
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  rcases G.optMakespan_nonneg.eq_or_lt with hopt0 | hopt_pos
  · rw [G.expectedMakespan_eq_zero_of_optMakespan_eq_zero hopt0.symm p, ← hopt0, mul_zero]
  · have hlog3_gt1 : 1 < Real.log 3 := Real.one_lt_log_of_three_le le_rfl
    have h7 : (7 : ℝ) = 6 + 1 := by norm_num
    rw [h7]
    refine hId.expectedMakespan_le_add_one_of_machine_tail hp.1 (by norm_num) fun j => ?_
    have hch := G.prob_subset_load_ge_le_exp hp.1 j univ
      (z := G.optMakespan / Real.log (m : ℝ)) (μ := 2 * G.optMakespan) (t := 6 * G.optMakespan)
      (div_pos hopt_pos hlogm_pos) (by linarith) (by linarith)
      (fun i _ _ => by rw [hId j, div_one]; exact hw i)
      (hId.expectedLoad_le_two_mul_optMakespan hp j)
    have hload : ∀ A : ι → M,
        (∑ i ∈ (univ : Finset ι) with A i = j, G.weight i / G.speed j) = G.load A j :=
      fun _ => rfl
    have hexp_eq :
        (6 * G.optMakespan - 2 * G.optMakespan -
            6 * G.optMakespan * Real.log (6 * G.optMakespan / (2 * G.optMakespan))) /
          (G.optMakespan / Real.log (m : ℝ)) =
        (4 - 6 * Real.log 3) * Real.log (m : ℝ) := by
      rw [show 6 * G.optMakespan / (2 * G.optMakespan) = 3 by field_simp [hopt_pos.ne']; norm_num]
      field_simp [hopt_pos.ne', hlogm_pos.ne']
      ring
    simp only [hload, hexp_eq] at hch
    calc (∑ A : ι → M, if 6 * G.optMakespan ≤ G.load A j then productWeight p A else 0)
        ≤ Real.exp ((4 - 6 * Real.log 3) * Real.log (m : ℝ)) := hch
      _ ≤ Real.exp (-(2 * Real.log (m : ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 / (m : ℝ) ^ 2 := by
          rw [Real.exp_neg,
            show (2 : ℝ) * Real.log (m : ℝ) = ((2 : ℕ) : ℝ) * Real.log (m : ℝ) by norm_num,
            Real.exp_nat_mul, Real.exp_log hm_pos, one_div]

end IdenticalMixedPoA

end Cslib.GameTheory.LoadBalancingGame

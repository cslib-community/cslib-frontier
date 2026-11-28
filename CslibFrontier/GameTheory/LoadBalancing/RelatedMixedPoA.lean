/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.LoadBalancing.MixedPoA
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.GameTheory.LoadBalancing.PurePoA
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mixed Nash price of anarchy upper bound on uniformly related machines

This module formalizes the Czumaj–Vöcking `O(log m / log log log m)` upper bound on the mixed
Nash price of anarchy for selfish load balancing on `m ≥ 16` uniformly related machines
([CzumajVocking2002]; [Vocking2007], Theorem 20.15, Lemma 20.16, and Lemma 20.17; locator not
re-verified against primary PDF), matching the `Ω(log m / log log log m)` lower bound in
`CslibFrontier.GameTheory.LoadBalancing.RelatedMixedLower`.

## Proof overview

Let `G` be a uniformly related load-balancing game on `m = |M|` machines and let `p` be any mixed
Nash equilibrium of `G`. When `optMakespan = 0`, `expectedMakespan p = 0`. Otherwise
`0 < OPT = G.optMakespan`, and:

1. **Expected-load speed prefixes and `O(log m / log log m)` maximum expected load**
   (`expectedSpeedPrefix`, `card_expectedSpeedPrefix_ge`, `expectedLoad_le_log_div_log_log`):
   define `L_k = {j : M | ∀ j', speed j ≤ speed j' → k * OPT ≤ E[ℓ_{j'}]}`. If `0 < p i j` and
   `E[ℓ_j] ≥ (k + 1) * OPT`, the mixed Nash inequality forces `Aopt i ∈ L_k` for any optimal pure
   assignment `Aopt`, giving `(k + 1) * #(L_{k+1}) ≤ #(L_k)` and hence `c! ≤ m` whenever some
   machine has `E[ℓ_j] ≥ (c + 1) * OPT`. Consequently, for `m ≥ 3`,
   `E[ℓ_j] ≤ (4 * log m / log (log m) + 3) * OPT ≤ (6 * log m / log (log m)) * OPT`.
2. **Speed doubling across expected-load groups** (`speed_doubling_expectedGroup`, [Vocking2007],
   Lemma 20.16): if machine `b` has `E[ℓ_b] < (k + 1) * OPT` and `L_{k+3}` is nonempty, then every
   job placing positive probability on `L_{k+3}` has `weight i > 2 * speed b * OPT` and
   `Aopt i ∈ L_{k+2}`. Comparing speed sums forces some machine in `G_{k+2} = L_{k+2} \ L_{k+3}` to
   have speed strictly greater than `2 * speed b` (hence `2 * s(k) < s(k + 2)`), and therefore a
   machine `j'` with `2 * speed b < speed j'` and `E[ℓ_{j'}] < (k + 3) * OPT`.
3. **Job-size cap for small-probability assignments** (`weight_le_twelve_mul_speed_mul_optMakespan`,
   [Vocking2007], Lemma 20.17): for every machine `j` and job `i` with `0 < p i j < 1 / 4`,
   setting `k = ⌊E[ℓ_j] / OPT⌋₊` and comparing `j` either with the speed-doubled machine `j'` from
   step 2 (when `L_{k+3}` is nonempty) or with `Aopt i` (when `L_{k+3}` is empty, so
   `E[ℓ_{Aopt i}] < (k + 4) * OPT`) yields `weight i ≤ 12 * speed j * OPT`.
4. **Heavy/light split, weighted Chernoff, and geometric tail integration**
   (`expectedMakespan_le_log_div_log_log_log`, [CzumajVocking2002]; [Vocking2007],
   Theorem 20.15): on the support of `productWeight p`, split each machine's load into
   `T_j^{(1)} = {i | 1 / 4 ≤ p i j}` (deterministically at most `4 * E[ℓ_j] ≤ (24 * log m /
   log log log m) * OPT`) and `T_j^{(2)} = {i | 0 < p i j ∧ p i j < 1 / 4}` (per-job load at most
   `12 * OPT`). Setting `T = 48 * log m / log (log (log m))` (`m ≥ 16`), the weighted Chernoff
   bound (`prob_subset_load_ge_le_exp`) and union bound yield
   `Pr[max_j load_2 A j ≥ (r + 1) * T * OPT] ≤ (1 / 2) ^ (r + 1)` for every `r : ℕ`, so a finite
   layer-cake sum gives `E[max_j load_2 A j] ≤ 2 * T * OPT` and hence
   `expectedMakespan p ≤ (120 * log m / log (log (log m))) * OPT`.

## Main definitions

* `Cslib.GameTheory.LoadBalancingGame.expectedSpeedPrefix`: the speed-sorted prefix `L_k` of
  machines all of whose at-least-as-fast peers have expected load at least `k * optMakespan`.

## Main results

* `Cslib.GameTheory.LoadBalancingGame.card_expectedSpeedPrefix_ge`,
  `Cslib.GameTheory.LoadBalancingGame.expectedLoad_le_log_div_log_log`: mixed-Nash speed-prefix
  cardinality growth `(k + 1) * #(L_{k+1}) ≤ #(L_k)` and `O(log m / log log m)` expected-load
  upper bound.
* `Cslib.GameTheory.LoadBalancingGame.speed_doubling_expectedGroup` ([Vocking2007], Lemma 20.16):
  speed doubling `2 * s(k) < s(k + 2)` between expected-load groups `G_k = L_k \ L_{k+1}`.
* `Cslib.GameTheory.LoadBalancingGame.weight_le_twelve_mul_speed_mul_optMakespan`
  ([Vocking2007], Lemma 20.17): every machine `j` and job `i` with `0 < p i j < 1 / 4` satisfies
  `weight i ≤ 12 * speed j * optMakespan`.
* `Cslib.GameTheory.LoadBalancingGame.expectedMakespan_le_log_div_log_log_log`
  ([CzumajVocking2002]; [Vocking2007], Theorem 20.15): for every load-balancing game on
  `m = |M| ≥ 16` uniformly related machines and every mixed Nash equilibrium `p`,
  `expectedMakespan p ≤ (120 * log m / log (log (log m))) * optMakespan`.

## References

* [CzumajVocking2002]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory.LoadBalancingGame

open Finset

section ExpectedSpeedPrefix

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M]

/-- The **expected-load speed-sorted prefix** `L_k` of machines all of whose at-least-as-fast peers
have expected load at least `k * optMakespan` under mixed profile `p` ([CzumajVocking2002];
[Vocking2007], §20.4.2). -/
@[expose] noncomputable def expectedSpeedPrefix (G : LoadBalancingGame ι M) (p : ι → M → ℝ)
    (k : ℕ) : Finset M :=
  open scoped Classical in
  univ.filter fun j =>
    ∀ j' : M, G.speed j ≤ G.speed j' → (k : ℝ) * G.optMakespan ≤ G.expectedLoad p j'

private theorem mul_optMakespan_le_expectedLoad_of_mem_prefix (G : LoadBalancingGame ι M)
    (p : ι → M → ℝ) (k : ℕ) {j : M} (hj : j ∈ G.expectedSpeedPrefix p k) :
    (k : ℝ) * G.optMakespan ≤ G.expectedLoad p j := by
  classical
  exact (mem_filter.mp hj).2 j le_rfl

omit [Nonempty M] in
/-- Unconditional mixed-Nash expected-load inequality: if `0 < p i j`, then for every machine `k`,
`expectedLoad p j ≤ expectedLoad p k + weight i / speed k`. -/
private theorem expectedLoad_le_of_isMixedNash_pos (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) {i : ι} {j : M} (hij : 0 < p i j) (k : M) :
    G.expectedLoad p j ≤ G.expectedLoad p k + G.weight i / G.speed k := by
  have hNE := ((G.isMixedNash_iff p).mp hp).2 i j hij k
  have hpij_le1 : p i j ≤ 1 := by
    rw [← (hp.1 i).sum_eq_one]
    exact single_le_sum (fun m _ => (hp.1 i).nonneg m) (mem_univ j)
  have h1 : 0 ≤ (1 - p i j) * (G.weight i / G.speed j) :=
    mul_nonneg (sub_nonneg.mpr hpij_le1) (div_nonneg (G.weight_nonneg i) (G.speed_pos j).le)
  have h2 : (1 - p i k) * (G.weight i / G.speed k) ≤ G.weight i / G.speed k := by
    have hdiv_nn : 0 ≤ G.weight i / G.speed k := div_nonneg (G.weight_nonneg i) (G.speed_pos k).le
    nlinarith [(hp.1 i).nonneg k]
  linarith

/-- Mixed-Nash prefix-list inclusion: if `0 < p i j` and `expectedLoad p j ≥ (k + 1) * optMakespan`,
then any optimal assignment `Aopt` places `i` on a machine in `expectedSpeedPrefix G p k`. -/
private theorem mem_expectedSpeedPrefix_of_expectedLoad_ge (G : LoadBalancingGame ι M)
    {p : ι → M → ℝ} {Aopt : ι → M} (hp : G.toCostGame.IsMixedNash p)
    (hAopt : G.makespan Aopt = G.optMakespan) {k : ℕ} {i : ι} {j : M} (hij : 0 < p i j)
    (hge : ((k + 1 : ℕ) : ℝ) * G.optMakespan ≤ G.expectedLoad p j) :
    Aopt i ∈ G.expectedSpeedPrefix p k :=
  G.mem_prefix_of_nash_load_ge hAopt
    (fun m => by simp only [expectedSpeedPrefix, mem_filter, mem_univ, true_and]) hge
    (G.expectedLoad_le_of_isMixedNash_pos hp hij)

omit [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M] in
/-- Speed-weighted expected load over a subset `S` of machines equals the probability-weighted
sum of job weights assigned to `S`. -/
private theorem sum_speed_mul_expectedLoad_subset (G : LoadBalancingGame ι M) (p : ι → M → ℝ)
    (S : Finset M) :
    ∑ j ∈ S, G.speed j * G.expectedLoad p j =
      ∑ i : ι, (∑ j ∈ S, p i j) * G.weight i := by
  simp only [expectedLoad, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun j _ => ?_
  have hs := (G.speed_pos j).ne'
  field_simp

/-- Speed-sum comparison across any two machine subsets `S₁, S₂` under a mixed Nash equilibrium:
if every machine in `S₁` has `expectedLoad p j ≥ c * optMakespan` and every job placing positive
probability on `S₁` is assigned by `Aopt` into `S₂`, then `c * ∑_{S₁} speed ≤ ∑_{S₂} speed`. -/
private theorem speed_sum_mul_le_of_expectedLoad_ge (G : LoadBalancingGame ι M)
    {p : ι → M → ℝ} {Aopt : ι → M} (hp : G.toCostGame.IsMixedNash p)
    (hopt : 0 < G.optMakespan) (hAopt : G.makespan Aopt = G.optMakespan)
    {c : ℝ} (S₁ S₂ : Finset M)
    (hle : ∀ j ∈ S₁, c * G.optMakespan ≤ G.expectedLoad p j)
    (hmap : ∀ i : ι, ∀ j ∈ S₁, 0 < p i j → Aopt i ∈ S₂) :
    c * ∑ j ∈ S₁, G.speed j ≤ ∑ j ∈ S₂, G.speed j := by
  classical
  have h1 : c * G.optMakespan * ∑ j ∈ S₁, G.speed j ≤
      ∑ j ∈ S₁, G.speed j * G.expectedLoad p j := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    have hl := hle j hj
    nlinarith [(G.speed_pos j).le]
  have h2 : ∑ j ∈ S₁, G.speed j * G.expectedLoad p j ≤ ∑ i with Aopt i ∈ S₂, G.weight i := by
    rw [G.sum_speed_mul_expectedLoad_subset p S₁, sum_filter]
    refine sum_le_sum fun i _ => ?_
    by_cases hi : Aopt i ∈ S₂
    · rw [ite_eq_left hi]
      have hple1 : ∑ j ∈ S₁, p i j ≤ 1 := by
        rw [← (hp.1 i).sum_eq_one]
        exact sum_le_univ_sum_of_nonneg fun j => (hp.1 i).nonneg j
      nlinarith [G.weight_nonneg i]
    · have hzero : ∑ j ∈ S₁, p i j = 0 := by
        refine sum_eq_zero fun j hj => ?_
        rcases ((hp.1 i).nonneg j).eq_or_lt with h | hpos
        · exact h.symm
        · exact absurd (hmap i j hj hpos) hi
      rw [ite_eq_right hi, hzero, zero_mul]
  have h3 := G.sum_weight_Aopt_mem_le hAopt S₂
  exact le_of_mul_le_mul_left (a := G.optMakespan) (by linarith) hopt

/-- **Mixed-Nash speed-prefix cardinality growth**: for every mixed Nash equilibrium `p` with
`0 < optMakespan` and every `k : ℕ`,
`(k + 1) * #(expectedSpeedPrefix G p (k + 1)) ≤ #(expectedSpeedPrefix G p k)`. -/
theorem card_expectedSpeedPrefix_ge (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) (hopt : 0 < G.optMakespan) (k : ℕ) :
    (k + 1) * #(G.expectedSpeedPrefix p (k + 1)) ≤ #(G.expectedSpeedPrefix p k) := by
  classical
  refine G.card_speedPrefix_step_of_sum_speed_le (G.expectedLoad p) (G.expectedSpeedPrefix p)
    (fun r j => by simp only [expectedSpeedPrefix, mem_filter, mem_univ, true_and])
    G.optMakespan_nonneg k fun _ => ?_
  obtain ⟨Aopt, hAopt⟩ := G.exists_makespan_eq_optMakespan
  exact G.speed_sum_mul_le_of_expectedLoad_ge hp hopt hAopt
    (G.expectedSpeedPrefix p (k + 1)) (G.expectedSpeedPrefix p k)
    (fun j hj => G.mul_optMakespan_le_expectedLoad_of_mem_prefix p (k + 1) hj)
    fun i j hj hpos => G.mem_expectedSpeedPrefix_of_expectedLoad_ge hp hAopt hpos
      (G.mul_optMakespan_le_expectedLoad_of_mem_prefix p (k + 1) hj)

omit [Nonempty M] in
/-- Expected loads are nonnegative under any mixed Nash equilibrium. -/
private theorem expectedLoad_nonneg (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) (j : M) : 0 ≤ G.expectedLoad p j :=
  sum_nonneg fun i _ => mul_nonneg ((hp.1 i).nonneg j)
    (div_nonneg (G.weight_nonneg i) (G.speed_pos j).le)

/-- A machine with expected load at least `(c + 1) * optMakespan > 0` receives some job with
positive probability. -/
private theorem exists_pos_of_expectedLoad_ge (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) (hopt : 0 < G.optMakespan) {j : M} {c : ℕ}
    (hge : ((c + 1 : ℕ) : ℝ) * G.optMakespan ≤ G.expectedLoad p j) : ∃ i, 0 < p i j := by
  by_contra! hnone
  have h0 : G.expectedLoad p j = 0 :=
    sum_eq_zero fun i _ => by rw [le_antisymm (hnone i) ((hp.1 i).nonneg j), zero_mul]
  have : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  nlinarith

/-- Factorial bound on machine count from a large expected load: if `0 < optMakespan` and some
machine `j` has `expectedLoad p j ≥ (c + 1) * optMakespan`, then `c! ≤ |M|`. -/
private theorem factorial_le_card_of_expectedLoad_ge (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) (hopt : 0 < G.optMakespan) (j : M) {c : ℕ}
    (hge : ((c + 1 : ℕ) : ℝ) * G.optMakespan ≤ G.expectedLoad p j) :
    c.factorial ≤ Fintype.card M := by
  classical
  obtain ⟨Aopt, hAopt⟩ := G.exists_makespan_eq_optMakespan
  obtain ⟨i₀, hi₀⟩ := G.exists_pos_of_expectedLoad_ge hp hopt hge
  exact factorial_le_card_of_prefix_step (G.expectedSpeedPrefix p)
    (G.card_expectedSpeedPrefix_ge hp hopt)
    (card_pos.mpr ⟨Aopt i₀, G.mem_expectedSpeedPrefix_of_expectedLoad_ge hp hAopt hi₀ hge⟩)

/-- **Maximum expected load in uniformly related mixed Nash equilibria**: on `m = |M| ≥ 3`
uniformly related machines, every machine `j` has expected load at most
`(4 * log m / log (log m) + 3) * optMakespan = O(log m / log log m) * OPT`. -/
theorem expectedLoad_le_log_div_log_log (G : LoadBalancingGame ι M) (hm : 3 ≤ Fintype.card M)
    {p : ι → M → ℝ} (hp : G.toCostGame.IsMixedNash p) (j : M) :
    G.expectedLoad p j ≤
      (4 * Real.log (Fintype.card M) / Real.log (Real.log (Fintype.card M)) + 3) *
        G.optMakespan := by
  rcases G.optMakespan_nonneg.eq_or_lt with hopt0 | hopt_pos
  · have hw0 : ∀ i, G.weight i = 0 := G.weight_eq_zero_of_optMakespan_eq_zero hopt0.symm
    have hE0 : G.expectedLoad p j = 0 := by simp [expectedLoad, hw0]
    rw [hE0, ← hopt0, mul_zero]
  · exact le_log_div_log_log_add_three_mul_of_factorial_le hm hopt_pos
      (G.expectedLoad_nonneg hp j) fun _ => G.factorial_le_card_of_expectedLoad_ge hp hopt_pos j

end ExpectedSpeedPrefix

section SpeedDoublingAndJobCap

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M]

/-- Core speed-doubling step ([Vocking2007], Lemma 20.16; locator not re-verified against primary
PDF): if `0 < optMakespan`, machine `b` has `expectedLoad p b < (k + 1) * optMakespan`, and
`expectedSpeedPrefix G p (k + 3)` is nonempty, then `G_{k + 2} = L_{k + 2} \ L_{k + 3}` contains a
machine strictly faster than `2 * speed b`. -/
private theorem exists_mem_expectedGroup_speed_gt_two_mul (G : LoadBalancingGame ι M)
    {p : ι → M → ℝ} (hp : G.toCostGame.IsMixedNash p) (hopt : 0 < G.optMakespan)
    {k : ℕ} {b : M} (hb : G.expectedLoad p b < ((k + 1 : ℕ) : ℝ) * G.optMakespan)
    (hne : (G.expectedSpeedPrefix p (k + 3)).Nonempty) :
    ∃ j ∈ G.expectedSpeedPrefix p (k + 2) \ G.expectedSpeedPrefix p (k + 3),
      2 * G.speed b < G.speed j := by
  classical
  obtain ⟨Aopt, hAopt⟩ := G.exists_makespan_eq_optMakespan
  let H : Finset M := (G.expectedSpeedPrefix p (k + 2)).filter fun j => 2 * G.speed b < G.speed j
  -- Every job `i` placing positive probability on `L_{k+3}` has `Aopt i ∈ H`.
  have hmap : ∀ i : ι, ∀ a ∈ G.expectedSpeedPrefix p (k + 3), 0 < p i a → Aopt i ∈ H := by
    intro i a ha hpos
    have ha_ge : ((k + 3 : ℕ) : ℝ) * G.optMakespan ≤ G.expectedLoad p a :=
      G.mul_optMakespan_le_expectedLoad_of_mem_prefix p (k + 3) ha
    have hmem : Aopt i ∈ G.expectedSpeedPrefix p (k + 2) :=
      G.mem_expectedSpeedPrefix_of_expectedLoad_ge hp hAopt hpos ha_ge
    have hNE_b := G.expectedLoad_le_of_isMixedNash_pos hp hpos b
    have hdiv_gt : 2 * G.optMakespan < G.weight i / G.speed b := by
      push_cast at ha_ge hb
      linarith
    have hw_gt : 2 * G.speed b * G.optMakespan < G.weight i := by
      have := (lt_div_iff₀ (G.speed_pos b)).mp hdiv_gt
      linarith
    have hopt_i : G.weight i / G.speed (Aopt i) ≤ G.optMakespan := by
      rw [← hAopt]
      exact G.weight_div_speed_le_makespan Aopt i
    have hw_le : G.weight i ≤ G.speed (Aopt i) * G.optMakespan := by
      have := (div_le_iff₀ (G.speed_pos (Aopt i))).mp hopt_i
      linarith
    have hsp_gt : 2 * G.speed b < G.speed (Aopt i) := by nlinarith
    exact mem_filter.mpr ⟨hmem, hsp_gt⟩
  -- Speed-sum comparison: `(k + 3) * ∑_{L_{k+3}} speed ≤ ∑_H speed`.
  have hspeed_le :
      ((k + 3 : ℕ) : ℝ) * ∑ a ∈ G.expectedSpeedPrefix p (k + 3), G.speed a ≤
        ∑ j ∈ H, G.speed j :=
    G.speed_sum_mul_le_of_expectedLoad_ge hp hopt hAopt (G.expectedSpeedPrefix p (k + 3)) H
      (fun a ha => G.mul_optMakespan_le_expectedLoad_of_mem_prefix p (k + 3) ha) hmap
  -- If no machine in `L_{k+2} \ L_{k+3}` has speed `> 2 * speed b`, then `H ⊆ L_{k+3}`.
  by_contra hnone
  push Not at hnone
  have hH_sub : H ⊆ G.expectedSpeedPrefix p (k + 3) := by
    intro j hj
    obtain ⟨hj2, hsp⟩ := mem_filter.mp hj
    by_contra hj3
    have := hnone j (mem_sdiff.mpr ⟨hj2, hj3⟩)
    linarith
  have hsum_H : ∑ j ∈ H, G.speed j ≤ ∑ a ∈ G.expectedSpeedPrefix p (k + 3), G.speed a :=
    sum_le_sum_of_subset_of_nonneg hH_sub fun j _ _ => (G.speed_pos j).le
  have hsum_pos : 0 < ∑ a ∈ G.expectedSpeedPrefix p (k + 3), G.speed a :=
    sum_pos (fun a _ => G.speed_pos a) hne
  have hk3 : (3 : ℝ) ≤ ((k + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ k + 3)
  nlinarith

/-- **Speed doubling across expected-load groups** ([CzumajVocking2002]; [Vocking2007],
Lemma 20.16; locator not re-verified against primary PDF): for `G_r = L_r \ L_{r + 1}`, if
`0 < optMakespan`, `G_k` is nonempty, and `L_{k + 3}` is nonempty, then `G_{k + 2}` is nonempty
and its maximum machine speed strictly exceeds twice the maximum machine speed of `G_k`. -/
theorem speed_doubling_expectedGroup (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) (hopt : 0 < G.optMakespan) {k : ℕ}
    (hGk : (G.expectedSpeedPrefix p k \ G.expectedSpeedPrefix p (k + 1)).Nonempty)
    (hLk3 : (G.expectedSpeedPrefix p (k + 3)).Nonempty) :
    ∃ (hGk2 : (G.expectedSpeedPrefix p (k + 2) \ G.expectedSpeedPrefix p (k + 3)).Nonempty),
      2 * (G.expectedSpeedPrefix p k \ G.expectedSpeedPrefix p (k + 1)).sup' hGk G.speed <
        (G.expectedSpeedPrefix p (k + 2) \ G.expectedSpeedPrefix p (k + 3)).sup' hGk2 G.speed := by
  classical
  obtain ⟨jmax, hjmax, hmax⟩ := exists_mem_eq_sup' hGk G.speed
  have hjmax_not : jmax ∉ G.expectedSpeedPrefix p (k + 1) := (mem_sdiff.mp hjmax).2
  simp only [expectedSpeedPrefix, mem_filter, mem_univ, true_and, not_forall, not_le] at hjmax_not
  obtain ⟨b, hsb, hEb⟩ := hjmax_not
  obtain ⟨j₂, hj₂, hsp₂⟩ := G.exists_mem_expectedGroup_speed_gt_two_mul hp hopt hEb hLk3
  refine ⟨⟨j₂, hj₂⟩, ?_⟩
  have hle_sup : G.speed j₂ ≤
      (G.expectedSpeedPrefix p (k + 2) \ G.expectedSpeedPrefix p (k + 3)).sup' ⟨j₂, hj₂⟩ G.speed :=
    le_sup' G.speed hj₂
  linarith

/-- Speed-doubling witness with an explicit expected-load ceiling: if `0 < optMakespan`,
`expectedLoad p b < (k + 1) * optMakespan`, and `L_{k + 3}` is nonempty, then there exists a
machine `j'` with `2 * speed b < speed j'` and `expectedLoad p j' < (k + 3) * optMakespan`. -/
private theorem exists_faster_expectedLoad_lt (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) (hopt : 0 < G.optMakespan) {k : ℕ} {b : M}
    (hb : G.expectedLoad p b < ((k + 1 : ℕ) : ℝ) * G.optMakespan)
    (hLk3 : (G.expectedSpeedPrefix p (k + 3)).Nonempty) :
    ∃ j' : M,
      2 * G.speed b < G.speed j' ∧
        G.expectedLoad p j' < ((k + 3 : ℕ) : ℝ) * G.optMakespan := by
  classical
  obtain ⟨j₂, hj₂, hsp₂⟩ := G.exists_mem_expectedGroup_speed_gt_two_mul hp hopt hb hLk3
  have hj₂_not : j₂ ∉ G.expectedSpeedPrefix p (k + 3) := (mem_sdiff.mp hj₂).2
  simp only [expectedSpeedPrefix, mem_filter, mem_univ, true_and, not_forall, not_le] at hj₂_not
  obtain ⟨j', hsj', hEj'⟩ := hj₂_not
  exact ⟨j', hsp₂.trans_le hsj', hEj'⟩

/-- **Small-probability job-size cap** ([CzumajVocking2002]; [Vocking2007], Lemma 20.17; locator
not re-verified against primary PDF): in any mixed Nash equilibrium `p` on uniformly related
machines, every machine `j` and job `i` with `0 < p i j < 1 / 4` satisfies
`weight i ≤ 12 * speed j * optMakespan`. -/
theorem weight_le_twelve_mul_speed_mul_optMakespan (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : G.toCostGame.IsMixedNash p) (j : M) (i : ι) (hpos : 0 < p i j)
    (hlt : p i j < 1 / 4) :
    G.weight i ≤ 12 * G.speed j * G.optMakespan := by
  classical
  rcases G.optMakespan_nonneg.eq_or_lt with hopt0 | hopt_pos
  · rw [G.weight_eq_zero_of_optMakespan_eq_zero hopt0.symm i, ← hopt0, mul_zero]
  · set k : ℕ := ⌊G.expectedLoad p j / G.optMakespan⌋₊
    have hk_le : (k : ℝ) * G.optMakespan ≤ G.expectedLoad p j := (le_div_iff₀ hopt_pos).mp
      (Nat.floor_le (div_nonneg (G.expectedLoad_nonneg hp j) hopt_pos.le))
    have hEj_lt : G.expectedLoad p j < ((k + 1 : ℕ) : ℝ) * G.optMakespan := by
      push_cast
      exact (div_lt_iff₀ hopt_pos).mp (Nat.lt_floor_add_one _)
    have hws_nn : 0 ≤ G.weight i / G.speed j :=
      div_nonneg (G.weight_nonneg i) (G.speed_pos j).le
    have hlhs_ge : (3 / 4 : ℝ) * (G.weight i / G.speed j) ≤
        (1 - p i j) * (G.weight i / G.speed j) := by
      nlinarith
    suffices hdiv_le : G.weight i / G.speed j ≤ 12 * G.optMakespan by
      linarith [(div_le_iff₀ (G.speed_pos j)).mp hdiv_le]
    by_cases hLk3 : (G.expectedSpeedPrefix p (k + 3)).Nonempty
    · -- Compare `j` against `j'` with `speed j' > 2 * speed j` and `E[ℓ_{j'}] < (k + 3) * OPT`.
      obtain ⟨j', hsp', hEj'⟩ := G.exists_faster_expectedLoad_lt hp hopt_pos hEj_lt hLk3
      have hNE := ((G.isMixedNash_iff p).mp hp).2 i j hpos j'
      have hhalf : G.weight i / G.speed j' ≤ (1 / 2 : ℝ) * (G.weight i / G.speed j) := by
        have h1 : G.weight i / G.speed j' ≤ G.weight i / (2 * G.speed j) :=
          div_le_div_of_nonneg_left (G.weight_nonneg i) (by linarith [G.speed_pos j]) hsp'.le
        have h2 : G.weight i / (2 * G.speed j) = (1 / 2 : ℝ) * (G.weight i / G.speed j) := by
          field_simp [(G.speed_pos j).ne']
        linarith
      have hrhs_le : (1 - p i j') * (G.weight i / G.speed j') ≤ G.weight i / G.speed j' := by
        have : 0 ≤ G.weight i / G.speed j' := div_nonneg (G.weight_nonneg i) (G.speed_pos j').le
        nlinarith [(hp.1 i).nonneg j']
      push_cast at hEj'
      linarith
    · -- `L_{k+3}` is empty, so every machine (including `Aopt i`) has `E[ℓ] < (k + 4) * OPT`.
      obtain ⟨Aopt, hAopt⟩ := G.exists_makespan_eq_optMakespan
      have hEAopt_lt : G.expectedLoad p (Aopt i) < ((k + 4 : ℕ) : ℝ) * G.optMakespan := by
        by_contra! hge
        replace hge : ((k + 3 + 1 : ℕ) : ℝ) * G.optMakespan ≤ G.expectedLoad p (Aopt i) := hge
        obtain ⟨r, hr⟩ := G.exists_pos_of_expectedLoad_ge hp hopt_pos hge
        exact hLk3 ⟨_, G.mem_expectedSpeedPrefix_of_expectedLoad_ge hp hAopt hr hge⟩
      have hNE := ((G.isMixedNash_iff p).mp hp).2 i j hpos (Aopt i)
      have hopt_i : G.weight i / G.speed (Aopt i) ≤ G.optMakespan := by
        rw [← hAopt]
        exact G.weight_div_speed_le_makespan Aopt i
      have hrhs_le : (1 - p i (Aopt i)) * (G.weight i / G.speed (Aopt i)) ≤ G.optMakespan := by
        have : 0 ≤ G.weight i / G.speed (Aopt i) :=
          div_nonneg (G.weight_nonneg i) (G.speed_pos (Aopt i)).le
        nlinarith [(hp.1 i).nonneg (Aopt i)]
      push_cast at hEAopt_lt
      linarith

end SpeedDoublingAndJobCap

section RelatedMixedPoAUpper

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M]

/-- Finite layer-cake upper bound: for any `x ≥ 0`, `u > 0`, and `S : ℕ` with
`x ≤ (S + 1) * u`, `x ≤ u + u * ∑ r ∈ range S, 1_{(r + 1) * u ≤ x}`. -/
private theorem le_layer_cake_sum {x u : ℝ} (hu : 0 < u) {S : ℕ}
    (hx : x ≤ ((S + 1 : ℕ) : ℝ) * u) :
    x ≤ u + u * ∑ r ∈ range S, if ((r + 1 : ℕ) : ℝ) * u ≤ x then (1 : ℝ) else 0 := by
  by_cases hlt : x < u
  · have hnn : 0 ≤ ∑ r ∈ range S, if ((r + 1 : ℕ) : ℝ) * u ≤ x then (1 : ℝ) else 0 :=
      sum_nonneg fun _ _ => by split_ifs <;> norm_num
    nlinarith
  · push Not at hlt
    set q : ℕ := ⌊x / u⌋₊
    have hq : (q : ℝ) * u ≤ x :=
      (le_div_iff₀ hu).mp (Nat.floor_le (div_nonneg (by linarith) hu.le))
    have hlt_q1 : x < ((q : ℝ) + 1) * u := (div_lt_iff₀ hu).mp (Nat.lt_floor_add_one (x / u))
    -- The first `min q S` indicators are all `1`.
    have hge : ((min q S : ℕ) : ℝ) ≤
        ∑ r ∈ range S, if ((r + 1 : ℕ) : ℝ) * u ≤ x then (1 : ℝ) else 0 :=
      calc ((min q S : ℕ) : ℝ)
          = ∑ r ∈ range (min q S), if ((r + 1 : ℕ) : ℝ) * u ≤ x then (1 : ℝ) else 0 := by
            rw [sum_ite_of_true fun r hr => (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
              ((mem_range.mp hr).trans_le (min_le_left q S))) hu.le).trans hq]
            simp
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (min_le_right q S))
            fun _ _ _ => by split_ifs <;> norm_num
    have hx_le : x ≤ u + u * ((min q S : ℕ) : ℝ) := by
      rcases min_cases q S with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> push_cast at hx ⊢ <;> linarith
    calc x ≤ u + u * ((min q S : ℕ) : ℝ) := hx_le
      _ ≤ u + u * ∑ r ∈ range S, if ((r + 1 : ℕ) : ℝ) * u ≤ x then (1 : ℝ) else 0 := by
          nlinarith [hge]

/-- Geometric sum bound `∑ r ∈ range S, (1 / 2) ^ (r + 1) ≤ 1`. -/
private theorem sum_half_pow_succ_le_one (S : ℕ) :
    ∑ r ∈ range S, (1 / 2 : ℝ) ^ (r + 1) ≤ 1 := by
  have hclosed : ∑ r ∈ range S, (1 / 2 : ℝ) ^ (r + 1) = 1 - (1 / 2 : ℝ) ^ S := by
    induction S with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, pow_succ]
      ring
  rw [hclosed]
  have : 0 ≤ (1 / 2 : ℝ) ^ S := by positivity
  linarith

/-- **Uniformly related mixed price of anarchy upper bound** ([CzumajVocking2002]; [Vocking2007],
Theorem 20.15; locator not re-verified against primary PDF): for every load-balancing game on
`m = |M| ≥ 16` uniformly related machines and every mixed Nash equilibrium `p`,
`expectedMakespan p ≤ (120 * log m / log (log (log m))) * optMakespan`. -/
theorem expectedMakespan_le_log_div_log_log_log (G : LoadBalancingGame ι M)
    (hm : 16 ≤ Fintype.card M) {p : ι → M → ℝ} (hp : G.toCostGame.IsMixedNash p) :
    G.expectedMakespan p ≤
      (120 * Real.log (Fintype.card M) / Real.log (Real.log (Real.log (Fintype.card M)))) *
        G.optMakespan := by
  classical
  set m : ℕ := Fintype.card M
  have hm16 : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  -- Establish `e < log m`, hence `1 < log (log m)` and `0 < log (log (log m))`.
  have hexp1_lt_log16 : Real.exp 1 < Real.log (16 : ℝ) := by
    have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
  set x : ℝ := Real.log (m : ℝ)
  have hx_gt_e : Real.exp 1 < x :=
    hexp1_lt_log16.trans_le (Real.log_le_log (by norm_num) hm16)
  have he_gt2 : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  have hx_pos : 0 < x := by linarith
  set y : ℝ := Real.log x
  have hy_gt1 : 1 < y := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hx_gt_e
  have hy_pos : 0 < y := by linarith
  set z : ℝ := Real.log y
  have hz_pos : 0 < z := Real.log_pos hy_gt1
  rcases G.optMakespan_nonneg.eq_or_lt with hopt0 | hopt_pos
  · rw [G.expectedMakespan_eq_zero_of_optMakespan_eq_zero hopt0.symm p, ← hopt0, mul_zero]
  · -- Step 1: Bound `E[ℓ_j] ≤ M_0 * OPT` with `M_0 = 6 * x / y`.
    set M₀ : ℝ := 6 * x / y
    have hM₀_pos : 0 < M₀ := by positivity
    have hE_le : ∀ j : M, G.expectedLoad p j ≤ M₀ * G.optMakespan := fun j => by
      have h1 := G.expectedLoad_le_log_div_log_log (by omega : 3 ≤ Fintype.card M) hp j
      have hy_le_xe : y ≤ x / Real.exp 1 := by
        have h := Real.log_le_sub_one_of_pos (div_pos hx_pos (Real.exp_pos 1))
        rw [Real.log_div hx_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
        linarith
      have h3_le : (3 : ℝ) ≤ 2 * x / y := by
        rw [le_div_iff₀ hy_pos]
        have : x / Real.exp 1 ≤ x / 2 := div_le_div_of_nonneg_left hx_pos.le (by norm_num) he_gt2.le
        linarith
      have hcoef : 4 * x / y + 3 ≤ M₀ := by
        have hadd : 4 * x / y + 2 * x / y = 6 * x / y := by ring
        simp only [M₀]
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_right hcoef hopt_pos.le)
    -- Step 2: Split each machine's load into heavy (`p i j ≥ 1 / 4`) and light (`0 < p i j < 1/4`).
    let light (j : M) : Finset ι := univ.filter fun i => 0 < p i j ∧ p i j < 1 / 4
    let lightLoad (A : ι → M) (j : M) : ℝ :=
      ∑ i ∈ light j with A i = j, G.weight i / G.speed j
    let lightMax (A : ι → M) : ℝ := univ.sup' univ_nonempty (lightLoad A)
    have hlightLoad_nn : ∀ A j, 0 ≤ lightLoad A j := fun A j =>
      sum_nonneg fun i _ => div_nonneg (G.weight_nonneg i) (G.speed_pos j).le
    have hlightMax_nn : ∀ A, 0 ≤ lightMax A := fun A => by
      obtain ⟨j₀⟩ := ‹Nonempty M›
      exact (hlightLoad_nn A j₀).trans (le_sup' (lightLoad A) (mem_univ j₀))
    have hms_split : ∀ A : ι → M, 0 < productWeight p A →
        G.makespan A ≤ 4 * M₀ * G.optMakespan + lightMax A := by
      intro A hposA
      have hpAi_pos : ∀ i : ι, 0 < p i (A i) := fun i =>
        ((hp.1 i).nonneg (A i)).lt_of_ne fun h0 => hposA.ne' <| by
          rw [productWeight_def]
          exact prod_eq_zero (mem_univ i) h0.symm
      rw [G.makespan_le_iff]
      intro j
      -- Split `load A j` by whether `1 / 4 ≤ p i j`; the light part lies inside `lightLoad A j`.
      have hsplit : G.load A j =
          (∑ i with A i = j ∧ 1 / 4 ≤ p i j, G.weight i / G.speed j) +
            ∑ i with A i = j ∧ ¬1 / 4 ≤ p i j, G.weight i / G.speed j := by
        rw [← filter_filter, ← filter_filter]
        exact (sum_filter_add_sum_filter_not _ _ _).symm
      have hheavy_le : (∑ i with A i = j ∧ 1 / 4 ≤ p i j, G.weight i / G.speed j) ≤
          4 * G.expectedLoad p j := by
        rw [expectedLoad, mul_sum]
        calc (∑ i with A i = j ∧ 1 / 4 ≤ p i j, G.weight i / G.speed j)
            ≤ ∑ i with A i = j ∧ 1 / 4 ≤ p i j, 4 * (p i j * (G.weight i / G.speed j)) :=
              sum_le_sum fun i hi => by
                nlinarith [(mem_filter.mp hi).2.2,
                  div_nonneg (G.weight_nonneg i) (G.speed_pos j).le]
          _ ≤ ∑ i : ι, 4 * (p i j * (G.weight i / G.speed j)) :=
              sum_le_univ_sum_of_nonneg fun i =>
                mul_nonneg (by norm_num) (mul_nonneg ((hp.1 i).nonneg j)
                  (div_nonneg (G.weight_nonneg i) (G.speed_pos j).le))
      have hlight_le : (∑ i with A i = j ∧ ¬1 / 4 ≤ p i j, G.weight i / G.speed j) ≤
          lightLoad A j := by
        refine sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
          fun i _ _ => div_nonneg (G.weight_nonneg i) (G.speed_pos j).le
        simp only [mem_filter, mem_univ, true_and, light] at hi ⊢
        exact ⟨⟨hi.1 ▸ hpAi_pos i, not_le.mp hi.2⟩, hi.1⟩
      linarith [hE_le j, le_sup' (lightLoad A) (mem_univ j)]
    -- Step 3: Chernoff tail on `lightLoad A j` at `t_r = (r + 1) * T * OPT` with `T = 48 * x / z`.
    set T : ℝ := 48 * x / z
    have hT_pos : 0 < T := by positivity
    have hz_lt_y : z < y := by linarith [Real.log_le_sub_one_of_pos hy_pos]
    have hlog8_gt1 : 1 < Real.log 8 := by
      rw [← Real.log_exp 1]
      exact Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_d9.trans (by norm_num))
    have hz_sub_logz : z / 2 ≤ z - Real.log z := by
      have h1 : Real.log (z / 2) ≤ z / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hz_pos.ne' (by norm_num)] at h1
      linarith [Real.log_two_lt_d9]
    have hT_ratio : T / M₀ = 8 * (y / z) := by
      simp only [T, M₀]
      field_simp [hx_pos.ne', hy_pos.ne', hz_pos.ne']
      ring
    have hT_ge_M₀ : M₀ ≤ T := (one_le_div hM₀_pos).mp <| by
      rw [hT_ratio]; linarith [(one_le_div hz_pos).mpr hz_lt_y.le]
    have hlog_TM₀ : z / 2 ≤ Real.log (T / M₀) - 1 := by
      rw [hT_ratio, Real.log_mul (by norm_num) (div_pos hy_pos hz_pos).ne',
        Real.log_div hy_pos.ne' hz_pos.ne']
      change z / 2 ≤ Real.log 8 + (z - Real.log z) - 1
      linarith
    have htail_j : ∀ (r : ℕ) (j : M),
        (∑ A : ι → M,
            if ((r + 1 : ℕ) : ℝ) * (T * G.optMakespan) ≤ lightLoad A j then
              productWeight p A else 0) ≤
          (1 / (m : ℝ) ^ 2) ^ (r + 1) := by
      intro r j
      set tr : ℝ := ((r + 1 : ℕ) : ℝ) * (T * G.optMakespan)
      have hr1_ge1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
      have htr_ge : M₀ * G.optMakespan ≤ tr :=
        (mul_le_mul_of_nonneg_right hT_ge_M₀ hopt_pos.le).trans
          (le_mul_of_one_le_left (mul_pos hT_pos hopt_pos).le hr1_ge1)
      have hcap : ∀ i ∈ light j, 0 < p i j → G.weight i / G.speed j ≤ 12 * G.optMakespan :=
        fun i hi hpos => (div_le_iff₀ (G.speed_pos j)).mpr <| by
          linarith [G.weight_le_twelve_mul_speed_mul_optMakespan hp j i hpos (mem_filter.mp hi).2.2]
      have hmean_light :
          ∑ i ∈ light j, p i j * (G.weight i / G.speed j) ≤ M₀ * G.optMakespan := calc
        ∑ i ∈ light j, p i j * (G.weight i / G.speed j)
            ≤ ∑ i : ι, p i j * (G.weight i / G.speed j) :=
              sum_le_univ_sum_of_nonneg fun i =>
                mul_nonneg ((hp.1 i).nonneg j) (div_nonneg (G.weight_nonneg i) (G.speed_pos j).le)
        _ ≤ M₀ * G.optMakespan := hE_le j
      have hch := G.prob_subset_load_ge_le_exp hp.1 j (light j)
        (z := 12 * G.optMakespan) (μ := M₀ * G.optMakespan) (t := tr)
        (by positivity) (by positivity) htr_ge hcap hmean_light
      have hlog_tr : z / 2 ≤ Real.log (tr / (M₀ * G.optMakespan)) - 1 := by
        have htr_div : tr / (M₀ * G.optMakespan) = ((r + 1 : ℕ) : ℝ) * (T / M₀) := by
          simp only [tr]
          field_simp [hM₀_pos.ne', hopt_pos.ne']
        rw [htr_div]
        linarith [Real.log_le_log (div_pos hT_pos hM₀_pos)
          (le_mul_of_one_le_left (div_pos hT_pos hM₀_pos).le hr1_ge1)]
      have hexp_le :
          (tr - M₀ * G.optMakespan - tr * Real.log (tr / (M₀ * G.optMakespan))) /
              (12 * G.optMakespan) ≤
            -(((r + 1 : ℕ) : ℝ) * (2 * x)) := by
        have htr_div12 : tr / (12 * G.optMakespan) = ((r + 1 : ℕ) : ℝ) * (4 * x / z) := by
          simp only [tr, T]
          field_simp [hopt_pos.ne', hz_pos.ne']
          ring
        have h1 :
            (tr - M₀ * G.optMakespan - tr * Real.log (tr / (M₀ * G.optMakespan))) /
                (12 * G.optMakespan) ≤
              -(tr / (12 * G.optMakespan) * (Real.log (tr / (M₀ * G.optMakespan)) - 1)) :=
          calc (tr - M₀ * G.optMakespan - tr * Real.log (tr / (M₀ * G.optMakespan))) /
                  (12 * G.optMakespan)
              ≤ (-(tr * (Real.log (tr / (M₀ * G.optMakespan)) - 1))) / (12 * G.optMakespan) :=
                div_le_div_of_nonneg_right
                  (by nlinarith [mul_pos hM₀_pos hopt_pos])
                  (by positivity)
            _ = -(tr / (12 * G.optMakespan) * (Real.log (tr / (M₀ * G.optMakespan)) - 1)) := by
                ring
        have h2 : ((r + 1 : ℕ) : ℝ) * (2 * x) ≤
            tr / (12 * G.optMakespan) * (Real.log (tr / (M₀ * G.optMakespan)) - 1) := by
          rw [htr_div12]
          calc ((r + 1 : ℕ) : ℝ) * (2 * x)
              = ((r + 1 : ℕ) : ℝ) * (4 * x / z) * (z / 2) := by
                field_simp [hz_pos.ne']
                ring
            _ ≤ ((r + 1 : ℕ) : ℝ) * (4 * x / z) *
                  (Real.log (tr / (M₀ * G.optMakespan)) - 1) :=
                mul_le_mul_of_nonneg_left hlog_tr (by positivity)
        linarith
      calc (∑ A : ι → M, if tr ≤ lightLoad A j then productWeight p A else 0)
          ≤ Real.exp ((tr - M₀ * G.optMakespan - tr * Real.log (tr / (M₀ * G.optMakespan))) /
              (12 * G.optMakespan)) := hch
        _ ≤ Real.exp (-(((r + 1 : ℕ) : ℝ) * (2 * x))) := Real.exp_le_exp.mpr hexp_le
        _ = (1 / (m : ℝ) ^ 2) ^ (r + 1) := by
            rw [show -(((r + 1 : ℕ) : ℝ) * (2 * x)) = ((r + 1 : ℕ) : ℝ) * (-(2 * x)) by ring,
              Real.exp_natCast_mul]
            congr 1
            rw [Real.exp_neg,
              show (2 : ℝ) * x = ((2 : ℕ) : ℝ) * Real.log (m : ℝ) by simp only [x]; norm_num,
              Real.exp_natCast_mul, Real.exp_log hm_pos, one_div]
    -- Step 4: Union bound over `m` machines for each layer `r`.
    have htail_max : ∀ r : ℕ,
        (∑ A : ι → M,
            if ((r + 1 : ℕ) : ℝ) * (T * G.optMakespan) ≤ lightMax A then
              productWeight p A else 0) ≤
          (1 / 2 : ℝ) ^ (r + 1) := by
      intro r
      set tr : ℝ := ((r + 1 : ℕ) : ℝ) * (T * G.optMakespan)
      have hpt : ∀ A : ι → M,
          (if tr ≤ lightMax A then productWeight p A else 0) ≤
            ∑ j : M, if tr ≤ lightLoad A j then productWeight p A else 0 := fun A => by
        have hw_nn : 0 ≤ productWeight p A := productWeight_nonneg (fun i => (hp.1 i).nonneg) A
        split_ifs with hms
        · obtain ⟨jstar, -, hjstar⟩ := exists_mem_eq_sup' (univ_nonempty (α := M)) (lightLoad A)
          refine (single_le_sum (f := fun j => if tr ≤ lightLoad A j then productWeight p A else 0)
            (fun j _ => by split_ifs <;> linarith) (mem_univ jstar)).trans' ?_
          rw [ite_eq_left (by simpa only [lightMax, hjstar] using hms)]
        · exact sum_nonneg fun j _ => by split_ifs <;> linarith
      calc (∑ A : ι → M, if tr ≤ lightMax A then productWeight p A else 0)
          ≤ ∑ A : ι → M, ∑ j : M, if tr ≤ lightLoad A j then productWeight p A else 0 :=
            sum_le_sum fun A _ => hpt A
        _ = ∑ j : M, ∑ A : ι → M, if tr ≤ lightLoad A j then productWeight p A else 0 := sum_comm
        _ ≤ ∑ _j : M, (1 / (m : ℝ) ^ 2) ^ (r + 1) := sum_le_sum fun j _ => htail_j r j
        _ = (m : ℝ) * (1 / (m : ℝ) ^ 2) ^ (r + 1) := by
            rw [sum_const, card_univ, nsmul_eq_mul]
        _ ≤ (1 / 2 : ℝ) ^ (r + 1) := by
            rw [pow_succ' _ r, pow_succ' _ r, ← mul_assoc,
              show (m : ℝ) * (1 / (m : ℝ) ^ 2) = 1 / m by field_simp [hm_pos.ne']]
            gcongr <;> nlinarith
    -- Step 5: Layer-cake sum bounds `E[lightMax] ≤ 2 * T * OPT`.
    set Bmax : ℝ := (univ : Finset (ι → M)).sup' univ_nonempty lightMax
    have hBmax_nn : 0 ≤ Bmax := by
      obtain ⟨j₀⟩ := ‹Nonempty M›
      exact (hlightMax_nn (fun _ => j₀)).trans (le_sup' lightMax (mem_univ (fun _ => j₀)))
    set S : ℕ := ⌊Bmax / (T * G.optMakespan)⌋₊ + 1
    have hlightMax_le_S : ∀ A : ι → M, lightMax A ≤ ((S + 1 : ℕ) : ℝ) * (T * G.optMakespan) := by
      intro A
      have h1 : lightMax A ≤ Bmax := le_sup' lightMax (mem_univ A)
      have h2 : Bmax < ((⌊Bmax / (T * G.optMakespan)⌋₊ : ℝ) + 1) * (T * G.optMakespan) :=
        (div_lt_iff₀ (mul_pos hT_pos hopt_pos)).mp (Nat.lt_floor_add_one _)
      have h3 : ((⌊Bmax / (T * G.optMakespan)⌋₊ : ℝ) + 1) ≤ ((S + 1 : ℕ) : ℝ) := by
        simp only [S]
        push_cast
        linarith
      nlinarith [mul_pos hT_pos hopt_pos]
    have hp1 : ∀ i, ∑ j, p i j = 1 := fun i => (hp.1 i).sum_eq_one
    have hE_lightMax :
        ∑ A : ι → M, productWeight p A * lightMax A ≤ 2 * (T * G.optMakespan) := by
      have hpt : ∀ A : ι → M,
          productWeight p A * lightMax A ≤
            productWeight p A * (T * G.optMakespan) +
              (T * G.optMakespan) *
                ∑ r ∈ range S,
                  if ((r + 1 : ℕ) : ℝ) * (T * G.optMakespan) ≤ lightMax A then
                    productWeight p A else 0 := fun A => by
        have hmul := mul_le_mul_of_nonneg_left
          (le_layer_cake_sum (mul_pos hT_pos hopt_pos) (hlightMax_le_S A))
          (productWeight_nonneg (fun i => (hp.1 i).nonneg) A)
        rw [mul_add, mul_left_comm (productWeight p A) (T * G.optMakespan), mul_sum] at hmul
        simpa only [mul_boole] using hmul
      calc ∑ A : ι → M, productWeight p A * lightMax A
          ≤ ∑ A : ι → M,
              (productWeight p A * (T * G.optMakespan) +
                (T * G.optMakespan) *
                  ∑ r ∈ range S,
                    if ((r + 1 : ℕ) : ℝ) * (T * G.optMakespan) ≤ lightMax A then
                      productWeight p A else 0) := sum_le_sum fun A _ => hpt A
        _ = (∑ A : ι → M, productWeight p A) * (T * G.optMakespan) +
              (T * G.optMakespan) *
                ∑ r ∈ range S, ∑ A : ι → M,
                  if ((r + 1 : ℕ) : ℝ) * (T * G.optMakespan) ≤ lightMax A then
                    productWeight p A else 0 := by
            rw [sum_add_distrib, ← sum_mul, ← mul_sum, sum_comm]
        _ ≤ 1 * (T * G.optMakespan) +
              (T * G.optMakespan) * ∑ r ∈ range S, (1 / 2 : ℝ) ^ (r + 1) := by
            rw [sum_productWeight hp1]
            gcongr with r _
            exact htail_max r
        _ ≤ 1 * (T * G.optMakespan) + (T * G.optMakespan) * 1 := by
            gcongr
            exact sum_half_pow_succ_le_one S
        _ = 2 * (T * G.optMakespan) := by ring
    -- Step 6: Combine heavy (`4 * M₀ ≤ 24 * x / z`) and light (`2 * T = 96 * x / z`).
    have hE_total :
        G.expectedMakespan p ≤ (4 * M₀ + 2 * T) * G.optMakespan := by
      have hpt : ∀ A : ι → M,
          productWeight p A * G.makespan A ≤
            productWeight p A * (4 * M₀ * G.optMakespan) +
              productWeight p A * lightMax A := fun A => by
        have hw_nn : 0 ≤ productWeight p A := productWeight_nonneg (fun i => (hp.1 i).nonneg) A
        rcases hw_nn.eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · linarith [mul_le_mul_of_nonneg_left (hms_split A hpos) hpos.le]
      calc G.expectedMakespan p
          = ∑ A : ι → M, productWeight p A * G.makespan A := rfl
        _ ≤ ∑ A : ι → M,
              (productWeight p A * (4 * M₀ * G.optMakespan) + productWeight p A * lightMax A) :=
            sum_le_sum fun A _ => hpt A
        _ = (∑ A : ι → M, productWeight p A) * (4 * M₀ * G.optMakespan) +
              ∑ A : ι → M, productWeight p A * lightMax A := by
            rw [sum_add_distrib, ← sum_mul]
        _ ≤ 1 * (4 * M₀ * G.optMakespan) + 2 * (T * G.optMakespan) := by
            rw [sum_productWeight hp1]
            linarith
        _ = (4 * M₀ + 2 * T) * G.optMakespan := by ring
    have hcoef_le : 4 * M₀ + 2 * T ≤ 120 * x / z := by
      have hdiv : x / y ≤ x / z := div_le_div_of_nonneg_left hx_pos.le hz_pos hz_lt_y.le
      have h : 4 * M₀ + 2 * T = 24 * (x / y) + 96 * (x / z) := by simp only [M₀, T]; ring
      rw [h, show 120 * x / z = 120 * (x / z) by ring]
      linarith
    exact hE_total.trans (mul_le_mul_of_nonneg_right hcoef_le hopt_pos.le)

end RelatedMixedPoAUpper

end Cslib.GameTheory.LoadBalancingGame

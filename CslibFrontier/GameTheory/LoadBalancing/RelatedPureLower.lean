/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.LoadBalancing.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogDivLogLog
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pure Nash price of anarchy lower bound on uniformly related machines

This module formalizes the `Ω(log m / log log m)` lower bound on the pure Nash price of anarchy
for selfish load balancing on uniformly related machines ([CzumajVocking2002]; [Vocking2007],
Theorem 20.9; locator not re-verified against primary PDF), matching the `O(log m / log log m)`
upper bound in `CslibFrontier.GameTheory.LoadBalancing.PurePoA`.

## Construction

For each parameter `k : ℕ`, we build `relatedPureLower k` with `k + 1` machine tiers
`t ∈ {0, 1, …, k}`:

* Tier `t` contains `relatedPureLowerTierCount k t = 2 ^ (k - t) * (k! / t!)` machines, each of
  speed `2 ^ t`. Thus `m_k = 1` and `m_t = 2 * (t + 1) * m_{t + 1}` for `t < k`, so the total
  machine count satisfies `M_k ≤ 2 ^ (k + 1) * k!`.
* For each `t < k`, there are `m_t = 2 * (t + 1) * m_{t + 1}` jobs of weight `2 ^ t`.
* In the **optimal-like assignment**, each job of type `t` occupies its own tier-`t` machine of
  speed `2 ^ t`, giving load `1` on every machine of tiers `0, …, k - 1` and load `0` on tier `k`,
  so `0 < optMakespan ≤ 1` (for `k ≥ 1`).
* In the **pure Nash assignment** `relatedPureLowerNE k`, the jobs of type `t` are distributed
  evenly (`2 * (t + 1)` jobs per machine) across tier `t + 1` (speed `2 ^ (t + 1)`), giving load
  `t + 1` on every tier-`(t + 1)` machine and load `0` on tier `0`, hence `makespan = k`.
  No job of weight `2 ^ t` on tier `t + 1` can improve by moving to any tier `r`: for `r > t`,
  tier `r` already has load `r ≥ t + 1`; for `r ≤ t`, moving gives load
  `r + 2 ^ (t - r) ≥ r + (t - r + 1) = t + 1`.

Padding `relatedPureLower k` with `m - M_k` idle machines of speed `1 / k` extends the lower bound
from the exact sequence `M_k` to **every** machine count `m ≥ 13` on `Fin m`
(`exists_relatedPureNash_makespan_ge_log_div_log_log`).

## Main definitions

* `Cslib.GameTheory.LoadBalancingGame.relatedPureLowerTierCount`: machine count in tier `t`.
* `Cslib.GameTheory.LoadBalancingGame.relatedPureLowerMachine`,
  `Cslib.GameTheory.LoadBalancingGame.relatedPureLowerJob`: machine and job index types.
* `Cslib.GameTheory.LoadBalancingGame.relatedPureLower`: the `k`-tier uniformly related game.
* `Cslib.GameTheory.LoadBalancingGame.relatedPureLowerNE`: the pure Nash assignment attaining
  makespan `k`.

## Main results

* `Cslib.GameTheory.LoadBalancingGame.isPureNash_relatedPureLowerNE`: `relatedPureLowerNE k` is a
  pure Nash equilibrium.
* `Cslib.GameTheory.LoadBalancingGame.makespan_relatedPureLowerNE`,
  `Cslib.GameTheory.LoadBalancingGame.optMakespan_relatedPureLower_le_one`,
  `Cslib.GameTheory.LoadBalancingGame.optMakespan_relatedPureLower_pos`: exact makespan `k` and
  `0 < optMakespan ≤ 1`.
* `Cslib.GameTheory.LoadBalancingGame.makespan_relatedPureLowerNE_ge_log_div_log_log`:
  `makespan ≥ (1 / 3) * (log |M| / log (log |M|)) * optMakespan` for all `k ≥ 2`.
* `Cslib.GameTheory.LoadBalancingGame.exists_relatedPureNash_makespan_ge_log_div_log_log`
  ([CzumajVocking2002]; [Vocking2007], Theorem 20.9): for every `m ≥ 13`, there exists a
  uniformly related game on `Fin m` machines with a pure Nash equilibrium attaining
  `makespan ≥ (1 / 5) * (log m / log (log m)) * optMakespan` and `0 < optMakespan`.

## References

* [CzumajVocking2002]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory.LoadBalancingGame

open Finset

/-- Number of machines in tier `t` of the `k`-tier Czumaj–Vöcking pure PoA lower-bound instance:
`m_t = 2 ^ (k - t) * (k! / t!)`. -/
@[expose] def relatedPureLowerTierCount (k t : ℕ) : ℕ :=
  2 ^ (k - t) * (k.factorial / t.factorial)

/-- Machine index type of the `k`-tier lower-bound instance: tier `t : Fin (k + 1)` paired with a
machine slot within tier `t`. -/
abbrev relatedPureLowerMachine (k : ℕ) : Type :=
  Σ t : Fin (k + 1), Fin (relatedPureLowerTierCount k t.val)

/-- Job index type of the `k`-tier lower-bound instance: for each `t : Fin k`, `2 * (t + 1)` jobs
assigned to each machine in tier `t + 1` under the pure Nash equilibrium. -/
abbrev relatedPureLowerJob (k : ℕ) : Type :=
  Σ t : Fin k, Fin (relatedPureLowerTierCount k (t.val + 1)) × Fin (2 * (t.val + 1))

/-- Every tier `t ≤ k` of `relatedPureLower k` has at least one machine. -/
theorem relatedPureLowerTierCount_pos (k : ℕ) {t : ℕ} (ht : t ≤ k) :
    0 < relatedPureLowerTierCount k t := by
  unfold relatedPureLowerTierCount
  have hdvd : t.factorial ∣ k.factorial := Nat.factorial_dvd_factorial ht
  have hq : 0 < k.factorial / t.factorial :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos k) hdvd) (Nat.factorial_pos t)
  positivity

/-- The top tier `k` of `relatedPureLower k` has exactly `1` machine. -/
theorem relatedPureLowerTierCount_last (k : ℕ) : relatedPureLowerTierCount k k = 1 := by
  simp [relatedPureLowerTierCount, Nat.div_self (Nat.factorial_pos k)]

private theorem tierCount_zero (k : ℕ) :
    relatedPureLowerTierCount k 0 = 2 ^ k * k.factorial := by
  simp [relatedPureLowerTierCount]

/-- Tier count recurrence: `m_t = m_{t + 1} * (2 * (t + 1))` for every `t < k`. -/
theorem relatedPureLowerTierCount_eq_mul_succ (k : ℕ) {t : ℕ} (ht : t < k) :
    relatedPureLowerTierCount k t =
      relatedPureLowerTierCount k (t + 1) * (2 * (t + 1)) := by
  unfold relatedPureLowerTierCount
  have hdvd1 : (t + 1).factorial ∣ k.factorial := Nat.factorial_dvd_factorial ht
  have hfac : k.factorial / t.factorial = (k.factorial / (t + 1).factorial) * (t + 1) := by
    obtain ⟨q, hq⟩ := hdvd1
    have hq' : k.factorial = t.factorial * (q * (t + 1)) := by
      rw [hq, Nat.factorial_succ]
      ring
    have h1 : k.factorial / t.factorial = q * (t + 1) := by
      rw [hq', Nat.mul_div_cancel_left _ (Nat.factorial_pos t)]
    have h2 : k.factorial / (t + 1).factorial = q := by
      rw [hq, Nat.mul_div_cancel_left _ (Nat.factorial_pos (t + 1))]
    rw [h1, h2]
  have hpow : 2 ^ (k - t) = 2 ^ (k - (t + 1)) * 2 := by
    have hsub : k - t = (k - (t + 1)) + 1 := by omega
    rw [hsub, pow_succ]
  rw [hpow, hfac]
  ring

instance (k : ℕ) : Nonempty (relatedPureLowerMachine k) :=
  ⟨⟨Fin.last k, ⟨0, relatedPureLowerTierCount_pos k le_rfl⟩⟩⟩

/-- **Czumaj–Vöcking pure PoA lower-bound game** ([CzumajVocking2002]; [Vocking2007], Theorem 20.9):
`k + 1` tiers of machines with speeds `2 ^ t`, and `m_t` jobs of weight `2 ^ t` for each `t < k`.
-/
def relatedPureLower (k : ℕ) :
    LoadBalancingGame (relatedPureLowerJob k) (relatedPureLowerMachine k) where
  weight i := (2 : ℝ) ^ i.1.val
  speed j := (2 : ℝ) ^ j.1.val
  weight_nonneg _ := by positivity
  speed_pos _ := by positivity

@[simp] theorem relatedPureLower_weight (k : ℕ) (i : relatedPureLowerJob k) :
    (relatedPureLower k).weight i = (2 : ℝ) ^ i.1.val := by
  simp [relatedPureLower]

@[simp] theorem relatedPureLower_speed (k : ℕ) (j : relatedPureLowerMachine k) :
    (relatedPureLower k).speed j = (2 : ℝ) ^ j.1.val := by
  simp [relatedPureLower]

/-- The worst-case pure Nash equilibrium on `relatedPureLower k`: every job of type `t` goes to
its designated machine in tier `t + 1`. -/
def relatedPureLowerNE (k : ℕ) :
    relatedPureLowerJob k → relatedPureLowerMachine k :=
  fun ⟨t, u, _⟩ => ⟨t.succ, u⟩

@[simp] theorem relatedPureLowerNE_apply (k : ℕ) (t : Fin k)
    (u : Fin (relatedPureLowerTierCount k (t.val + 1))) (v : Fin (2 * (t.val + 1))) :
    relatedPureLowerNE k ⟨t, u, v⟩ = ⟨t.succ, u⟩ := by
  simp [relatedPureLowerNE]

/-- Exact machine load under `relatedPureLowerNE k`: every machine in tier `r` has load `r`. -/
theorem load_relatedPureLowerNE (k : ℕ) (j : relatedPureLowerMachine k) :
    (relatedPureLower k).load (relatedPureLowerNE k) j = (j.1.val : ℝ) := by
  rcases j with ⟨r, u⟩
  rw [LoadBalancingGame.load_eq_sum_div]
  revert u
  refine Fin.cases ?_ ?_ r
  · intro u
    -- Tier `0` receives no jobs under `relatedPureLowerNE`.
    have hempty :
        (univ.filter fun i : relatedPureLowerJob k => relatedPureLowerNE k i = ⟨0, u⟩) = ∅ := by
      ext ⟨t, u', v'⟩
      rw [Finset.mem_filter]
      simp only [mem_univ, true_and, notMem_empty, iff_false, relatedPureLowerNE]
      intro h
      have h1 : t.succ = 0 := congrArg Sigma.fst h
      exact Fin.succ_ne_zero t h1
    rw [hempty, sum_empty, zero_div]
    simp
  · -- Tier `t.succ` receives `2 * (t + 1)` jobs of weight `2 ^ t`, divided by speed `2 ^ (t + 1)`.
    intro t u
    have hfilt :
        (univ.filter fun i : relatedPureLowerJob k =>
            relatedPureLowerNE k i = ⟨t.succ, u⟩) =
          univ.image (fun v : Fin (2 * (t.val + 1)) =>
            (⟨t, (u, v)⟩ : relatedPureLowerJob k)) := by
      ext ⟨t', u', v'⟩
      rw [Finset.mem_filter, Finset.mem_image]
      simp only [mem_univ, true_and, relatedPureLowerNE]
      constructor
      · intro h
        have ht : t' = t := Fin.succ_injective _ (congrArg Sigma.fst h)
        subst ht
        have hu : u' = u := by
          have := Sigma.mk.inj_iff.mp h
          exact eq_of_heq this.2
        subst hu
        exact ⟨v', rfl⟩
      · rintro ⟨v, hv⟩
        have ht : t = t' := congrArg Sigma.fst hv
        subst ht
        have hp : (u, v) = (u', v') := eq_of_heq (Sigma.mk.inj_iff.mp hv).2
        have hu : u = u' := congrArg Prod.fst hp
        subst hu
        rfl
    have hinj : Function.Injective (fun v : Fin (2 * (t.val + 1)) =>
        (⟨t, (u, v)⟩ : relatedPureLowerJob k)) := by
      intro v₁ v₂ h
      have hp : (u, v₁) = (u, v₂) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      exact congrArg Prod.snd hp
    rw [hfilt, sum_image (fun _ _ _ _ h => hinj h)]
    simp only [relatedPureLower, Fin.val_succ, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [pow_succ]
    have hpow_ne : (2 : ℝ) ^ t.val ≠ 0 := by positivity
    push_cast
    field_simp

/-- `relatedPureLowerNE k` is a pure Nash equilibrium of `relatedPureLower k`. -/
theorem isPureNash_relatedPureLowerNE (k : ℕ) :
    (relatedPureLower k).toCostGame.IsPureNash (relatedPureLowerNE k) := by
  rw [(relatedPureLower k).isPureNash_iff]
  intro ⟨t, u, v⟩ ⟨r, u'⟩ _
  rw [relatedPureLowerNE, load_relatedPureLowerNE, load_relatedPureLowerNE]
  simp only [relatedPureLower, Fin.val_succ]
  by_cases hrt : t.val + 1 ≤ r.val
  · have hrt' : (t.val : ℝ) + 1 ≤ (r.val : ℝ) := by exact_mod_cast hrt
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ t.val / (2 : ℝ) ^ r.val := by positivity
    push_cast
    linarith
  · have hle : r.val ≤ t.val := by omega
    set d : ℕ := t.val - r.val
    have htr : t.val = r.val + d := by omega
    have hdiv : (2 : ℝ) ^ t.val / (2 : ℝ) ^ r.val = (2 : ℝ) ^ d := by
      rw [htr, pow_add, mul_div_cancel_left₀ _ (by positivity)]
    have h2d : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
    have h2d' : (d : ℝ) + 1 ≤ (2 : ℝ) ^ d := by exact_mod_cast h2d
    have htr' : (t.val : ℝ) = (r.val : ℝ) + (d : ℝ) := by exact_mod_cast htr
    rw [hdiv]
    push_cast
    linarith

/-- The pure Nash equilibrium `relatedPureLowerNE k` has exact makespan `k`. -/
theorem makespan_relatedPureLowerNE (k : ℕ) :
    (relatedPureLower k).makespan (relatedPureLowerNE k) = (k : ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [(relatedPureLower k).makespan_le_iff]
    intro ⟨r, u⟩
    rw [load_relatedPureLowerNE]
    exact_mod_cast Nat.le_of_lt_succ r.isLt
  · calc (k : ℝ) = (relatedPureLower k).load (relatedPureLowerNE k)
            ⟨Fin.last k, ⟨0, relatedPureLowerTierCount_pos k le_rfl⟩⟩ := by
          simp [load_relatedPureLowerNE]
      _ ≤ (relatedPureLower k).makespan (relatedPureLowerNE k) :=
          (relatedPureLower k).load_le_makespan _ _

/-- Optimal-like assignment placing each job of type `t` on a distinct machine of tier `t`. -/
private def relatedPureLowerOpt (k : ℕ) :
    relatedPureLowerJob k → relatedPureLowerMachine k :=
  fun ⟨t, p⟩ =>
    ⟨t.castSucc, (finProdFinEquiv p).cast (relatedPureLowerTierCount_eq_mul_succ k t.isLt).symm⟩

private theorem relatedPureLowerOpt_injective (k : ℕ) :
    Function.Injective (relatedPureLowerOpt k) := by
  intro ⟨t₁, p₁⟩ ⟨t₂, p₂⟩ h
  have ht : t₁ = t₂ := Fin.castSucc_injective _ (congrArg Sigma.fst h)
  subst ht
  have hslot :
      (finProdFinEquiv p₁).cast (relatedPureLowerTierCount_eq_mul_succ k t₁.isLt).symm =
        (finProdFinEquiv p₂).cast (relatedPureLowerTierCount_eq_mul_succ k t₁.isLt).symm :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hslot' : finProdFinEquiv p₁ = finProdFinEquiv p₂ := by
    apply Fin.ext
    simpa only [Fin.val_cast] using congrArg Fin.val hslot
  have hp : p₁ = p₂ := finProdFinEquiv.injective hslot'
  subst hp
  rfl

private theorem load_relatedPureLowerOpt_le_one (k : ℕ) (j : relatedPureLowerMachine k) :
    (relatedPureLower k).load (relatedPureLowerOpt k) j ≤ 1 := by
  rw [LoadBalancingGame.load_eq_sum_div]
  set S := univ.filter fun i : relatedPureLowerJob k => relatedPureLowerOpt k i = j
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hS
    have hAi₀ : relatedPureLowerOpt k i₀ = j := (mem_filter.mp hi₀).2
    have hSing : S = {i₀} := by
      ext i
      simp only [S, mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun hi => relatedPureLowerOpt_injective k (hi.trans hAi₀.symm),
        fun hi => hi ▸ hAi₀⟩
    rw [show (∑ i with relatedPureLowerOpt k i = j, (relatedPureLower k).weight i) =
        ∑ i ∈ S, (relatedPureLower k).weight i from rfl, hSing, sum_singleton]
    have ht_eq : i₀.1.val = j.1.val := by
      have := congrArg (fun x : relatedPureLowerMachine k => x.1.val) hAi₀
      simpa only [relatedPureLowerOpt, Fin.val_castSucc] using this
    simp only [relatedPureLower_weight, relatedPureLower_speed, ht_eq]
    rw [div_self (by positivity)]
  · rw [not_nonempty_iff_eq_empty] at hS
    rw [show (∑ i with relatedPureLowerOpt k i = j, (relatedPureLower k).weight i) =
        ∑ i ∈ S, (relatedPureLower k).weight i from rfl, hS, sum_empty, zero_div]
    exact zero_le_one

/-- The optimal makespan of `relatedPureLower k` is at most `1`. -/
theorem optMakespan_relatedPureLower_le_one (k : ℕ) :
    (relatedPureLower k).optMakespan ≤ 1 :=
  ((relatedPureLower k).optMakespan_le (relatedPureLowerOpt k)).trans
    (((relatedPureLower k).makespan_le_iff _).mpr (load_relatedPureLowerOpt_le_one k))

/-- For `k ≥ 1`, `relatedPureLower k` has strictly positive optimal makespan. -/
theorem optMakespan_relatedPureLower_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < (relatedPureLower k).optMakespan := by
  let i₀ : relatedPureLowerJob k :=
    ⟨⟨0, hk⟩, (⟨0, relatedPureLowerTierCount_pos k hk⟩, ⟨0, by omega⟩)⟩
  refine (relatedPureLower k).optMakespan_pos_of_weight_pos (i := i₀) ?_
  simp [i₀]

/-- Total machine count in `relatedPureLower k` is at most `2 ^ (k + 1) * k!`. -/
theorem card_relatedPureLowerMachine_le (k : ℕ) :
    Fintype.card (relatedPureLowerMachine k) ≤ 2 ^ (k + 1) * k.factorial := by
  have hcard : Fintype.card (relatedPureLowerMachine k) =
      ∑ t ∈ range (k + 1), relatedPureLowerTierCount k t := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range (relatedPureLowerTierCount k) (k + 1)
  rw [hcard]
  have hstep : ∀ t ∈ range k,
      2 * relatedPureLowerTierCount k (t + 1) ≤ relatedPureLowerTierCount k t := by
    intro t ht
    rw [mem_range] at ht
    rw [relatedPureLowerTierCount_eq_mul_succ k ht]
    have h1 : 1 ≤ t + 1 := Nat.succ_pos t
    nlinarith
  have hsum_le :
      2 * (∑ t ∈ range k, relatedPureLowerTierCount k (t + 1)) ≤
        ∑ t ∈ range k, relatedPureLowerTierCount k t := by
    rw [mul_sum]
    exact sum_le_sum hstep
  have hsplit1 : ∑ t ∈ range (k + 1), relatedPureLowerTierCount k t =
      relatedPureLowerTierCount k 0 + ∑ t ∈ range k, relatedPureLowerTierCount k (t + 1) := by
    rw [sum_range_succ']
    omega
  have hsplit2 : ∑ t ∈ range (k + 1), relatedPureLowerTierCount k t =
      (∑ t ∈ range k, relatedPureLowerTierCount k t) + relatedPureLowerTierCount k k :=
    sum_range_succ _ k
  have h0 := tierCount_zero k
  have hpow : 2 * (2 ^ k * k.factorial) = 2 ^ (k + 1) * k.factorial := by
    rw [pow_succ]
    ring
  omega

private theorem tierCount_zero_le_card (k : ℕ) :
    2 ^ k * k.factorial ≤ Fintype.card (relatedPureLowerMachine k) := by
  have hcard : Fintype.card (relatedPureLowerMachine k) =
      ∑ t ∈ range (k + 1), relatedPureLowerTierCount k t := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact Fin.sum_univ_eq_sum_range (relatedPureLowerTierCount k) (k + 1)
  rw [hcard, ← tierCount_zero k]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.succ_pos k))

private theorem card_relatedPureLowerMachine_two :
    Fintype.card (relatedPureLowerMachine 2) = 13 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_three]
  norm_num [relatedPureLowerTierCount, Nat.factorial]

private theorem exp_lt_card_relatedPureLowerMachine {k : ℕ} (hk : 2 ≤ k) :
    Real.exp (k : ℝ) < (Fintype.card (relatedPureLowerMachine k) : ℝ) := by
  have h4 := Nat.four_pow_le_two_mul_two_pow_mul_factorial (by omega : 1 ≤ k)
  have hexp1 : Real.exp 1 < (2.72 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
  have h2_lt : (2 : ℝ) * Real.exp (k : ℝ) < (4 : ℝ) ^ k := by
    have hratio : (2 : ℝ) * (2.72 : ℝ) ^ k ≤ (4 : ℝ) ^ k := by
      have h2 : (2 : ℝ) * (2.72 : ℝ) ^ 2 ≤ (4 : ℝ) ^ 2 := by norm_num
      have hsub : k = 2 + (k - 2) := by omega
      rw [hsub, pow_add, pow_add, ← mul_assoc]
      exact mul_le_mul h2 (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by positivity)
        (by positivity)
    have hexpk : Real.exp (k : ℝ) < (2.72 : ℝ) ^ k := by
      rw [show (k : ℝ) = (k : ℕ) * (1 : ℝ) by ring, Real.exp_nat_mul]
      exact pow_lt_pow_left₀ hexp1 (Real.exp_pos 1).le (by omega)
    linarith
  have h4_real : (4 : ℝ) ^ k ≤ 2 * ((2 ^ k * k.factorial : ℕ) : ℝ) := by exact_mod_cast h4
  have hcard : ((2 ^ k * k.factorial : ℕ) : ℝ) ≤
      (Fintype.card (relatedPureLowerMachine k) : ℝ) := by
    exact_mod_cast tierCount_zero_le_card k
  linarith

/-- **Asymptotic pure PoA lower bound along the `k`-tier family**: for every `k ≥ 2`,
`relatedPureLowerNE k` achieves makespan at least
`(1 / 3) * (log |M| / log (log |M|)) * optMakespan`. -/
theorem makespan_relatedPureLowerNE_ge_log_div_log_log {k : ℕ} (hk : 2 ≤ k) :
    (1 / 3 : ℝ) *
      (Real.log (Fintype.card (relatedPureLowerMachine k)) /
        Real.log (Real.log (Fintype.card (relatedPureLowerMachine k)))) *
      (relatedPureLower k).optMakespan ≤
        (relatedPureLower k).makespan (relatedPureLowerNE k) := by
  set M : ℕ := Fintype.card (relatedPureLowerMachine k)
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp_lt : Real.exp (k : ℝ) < (M : ℝ) := exp_lt_card_relatedPureLowerMachine hk
  have hM_pos : (0 : ℝ) < (M : ℝ) := (Real.exp_pos _).trans hexp_lt
  have hM_le : (M : ℝ) ≤ (2 : ℝ) ^ (k + 1) * (k : ℝ) ^ k := by
    exact_mod_cast (card_relatedPureLowerMachine_le k).trans
      (Nat.mul_le_mul_left _ (Nat.factorial_le_pow k))
  have hlogM_le : Real.log (M : ℝ) ≤ 3 * (k : ℝ) * Real.log (k : ℝ) := by
    have h1 := Real.add_mul_log_two_le (d := 1) hk_real zero_le_one
    calc Real.log (M : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (k + 1) * (k : ℝ) ^ k) := Real.log_le_log hM_pos hM_le
      _ = ((k : ℝ) + 1) * Real.log 2 + (k : ℝ) * Real.log (k : ℝ) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; rfl
      _ ≤ 3 * (k : ℝ) * Real.log (k : ℝ) := by
          nlinarith [Real.log_pos (by linarith : (1 : ℝ) < k)]
  obtain ⟨hloglogM_pos, hratio_le_k⟩ :=
    Real.inv_mul_log_div_log_log_le hk_real (by norm_num : (0 : ℝ) < 3) hexp_lt hlogM_le
  rw [makespan_relatedPureLowerNE]
  have hratio_nn : 0 ≤ (1 / 3 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (M : ℝ))) := by
    positivity
  calc (1 / 3 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (M : ℝ))) *
          (relatedPureLower k).optMakespan
      ≤ (1 / 3 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (M : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left (optMakespan_relatedPureLower_le_one k) hratio_nn
    _ ≤ (k : ℝ) := by linarith

/-- **Uniformly related pure PoA lower bound for all `m ≥ 13`** ([CzumajVocking2002];
[Vocking2007], Theorem 20.9; locator not re-verified against primary PDF): for every `m ≥ 13`,
there exists a finite uniformly related load-balancing game on `Fin m` machines with `0 < OPT`
and a pure Nash equilibrium attaining makespan at least
`(1 / 5) * (log m / log (log m)) * OPT`. -/
theorem exists_relatedPureNash_makespan_ge_log_div_log_log {m : ℕ} [NeZero m] (hm : 13 ≤ m) :
    ∃ (n : ℕ) (G : LoadBalancingGame (Fin n) (Fin m)) (A : Fin n → Fin m),
      G.toCostGame.IsPureNash A ∧
      0 < G.optMakespan ∧
      (1 / 5 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) * G.optMakespan ≤
        G.makespan A := by
  let M : ℕ → ℕ := fun k => Fintype.card (relatedPureLowerMachine k)
  -- Pick the largest `k ≥ 2` with `M k ≤ m`.
  have hS_ne : ((range (m + 1)).filter fun k => 2 ≤ k ∧ M k ≤ m).Nonempty := by
    refine ⟨2, mem_filter.mpr ⟨mem_range.mpr (by omega), le_rfl, ?_⟩⟩
    dsimp only [M]
    rw [card_relatedPureLowerMachine_two]
    exact hm
  obtain ⟨k, hk_mem, hk_max⟩ :=
    exists_max_image ((range (m + 1)).filter fun k => 2 ≤ k ∧ M k ≤ m) id hS_ne
  obtain ⟨_, hk2, hMk_le⟩ := mem_filter.mp hk_mem
  have hm_lt_next : m < M (k + 1) := by
    by_contra hle
    push Not at hle
    have hk1_lt : k + 1 < m + 1 := by
      have h2k : 2 ^ (k + 1) ≤ M (k + 1) := by
        have h1 : 2 ^ (k + 1) * (k + 1).factorial ≤ M (k + 1) :=
          tierCount_zero_le_card (k + 1)
        have hfac : 1 ≤ (k + 1).factorial := Nat.factorial_pos (k + 1)
        have h2 : 2 ^ (k + 1) * 1 ≤ 2 ^ (k + 1) * (k + 1).factorial := Nat.mul_le_mul_left _ hfac
        omega
      have hlin : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
      omega
    have hk1_mem : k + 1 ∈ (range (m + 1)).filter fun r => 2 ≤ r ∧ M r ≤ m :=
      mem_filter.mpr ⟨mem_range.mpr hk1_lt, by omega, hle⟩
    have := hk_max (k + 1) hk1_mem
    dsimp only [id_eq] at this
    omega
  -- Reindex `relatedPureLower k` into `Fin n` jobs and the first `M k` machines of `Fin m`,
  -- padding the remaining `m - M k` idle machines with speed `1 / k`.
  let n : ℕ := Fintype.card (relatedPureLowerJob k)
  let eJ : Fin n ≃ relatedPureLowerJob k := (Fintype.equivFin (relatedPureLowerJob k)).symm
  let eM : Fin (M k) ≃ relatedPureLowerMachine k :=
    (Fintype.equivFin (relatedPureLowerMachine k)).symm
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  let G : LoadBalancingGame (Fin n) (Fin m) :=
    { weight := fun i => (relatedPureLower k).weight (eJ i)
      speed := fun j =>
        if h : j.val < M k then (relatedPureLower k).speed (eM ⟨j.val, h⟩) else 1 / (k : ℝ)
      weight_nonneg := fun i => (relatedPureLower k).weight_nonneg (eJ i)
      speed_pos := fun j => by
        split_ifs with h
        · exact (relatedPureLower k).speed_pos _
        · positivity }
  let embedM : relatedPureLowerMachine k → Fin m := fun x =>
    ⟨(eM.symm x).val, lt_of_lt_of_le (eM.symm x).isLt hMk_le⟩
  let A : Fin n → Fin m := fun i => embedM (relatedPureLowerNE k (eJ i))
  let Aopt : Fin n → Fin m := fun i => embedM (relatedPureLowerOpt k (eJ i))
  -- Helper computing `G.load (fun i => embedM (B (eJ i))) j` for any `B`.
  have hload_embed : ∀ (B : relatedPureLowerJob k → relatedPureLowerMachine k) (j : Fin m),
      G.load (fun i => embedM (B (eJ i))) j =
        if h : j.val < M k then (relatedPureLower k).load B (eM ⟨j.val, h⟩) else 0 := by
    intro B j
    rw [LoadBalancingGame.load_eq_sum_div]
    by_cases h : j.val < M k
    · rw [dite_eq_left h]
      simp only [G, dite_eq_left h]
      rw [LoadBalancingGame.load_eq_sum_div]
      congr 1
      refine Finset.sum_nbij (fun i => eJ i) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        have hv : (eM.symm (B (eJ i))).val = j.val := congrArg Fin.val hi
        have heq : eM.symm (B (eJ i)) = ⟨j.val, h⟩ := Fin.ext hv
        exact (eM.symm_apply_eq).mp heq
      · intro i₁ _ i₂ _ hEq
        exact eJ.injective hEq
      · intro x hx
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hx
        refine ⟨eJ.symm x, ?_, eJ.apply_symm_apply x⟩
        simp only [mem_coe, mem_filter, mem_univ, true_and, eJ.apply_symm_apply, hx]
        apply Fin.ext
        simp only [embedM, Equiv.symm_apply_apply]
      · intro _ _; rfl
    · rw [dite_eq_right h]
      have hempty :
          (univ.filter fun i : Fin n => embedM (B (eJ i)) = j) = ∅ := by
        ext i
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        intro hi
        have hv : (eM.symm (B (eJ i))).val = j.val := congrArg Fin.val hi
        exact h (hv ▸ (eM.symm (B (eJ i))).isLt)
      rw [hempty, sum_empty, zero_div]
  have hA_isNE : G.toCostGame.IsPureNash A := by
    rw [G.isPureNash_iff]
    intro i j _
    have hAi_lt : (A i).val < M k := (eM.symm _).isLt
    have hloadAi : G.load A (A i) =
        (relatedPureLower k).load (relatedPureLowerNE k) (relatedPureLowerNE k (eJ i)) := by
      have h1 := hload_embed (relatedPureLowerNE k) (A i)
      rw [dite_eq_left hAi_lt] at h1
      have hfin : (⟨(A i).val, hAi_lt⟩ : Fin (M k)) = eM.symm (relatedPureLowerNE k (eJ i)) :=
        Fin.ext rfl
      rw [h1, hfin, eM.apply_symm_apply]
    rw [hloadAi]
    by_cases hj : j.val < M k
    · have hloadj := hload_embed (relatedPureLowerNE k) j
      rw [dite_eq_left hj] at hloadj
      rw [hloadj]
      simp only [G, dite_eq_left hj]
      exact (relatedPureLower k).isPureNash_load_le (isPureNash_relatedPureLowerNE k)
        (eJ i) (eM ⟨j.val, hj⟩)
    · have hloadj := hload_embed (relatedPureLowerNE k) j
      rw [dite_eq_right hj] at hloadj
      rw [hloadj, zero_add]
      simp only [G, dite_eq_right hj]
      rw [load_relatedPureLowerNE]
      simp only [relatedPureLower, relatedPureLowerNE, Fin.val_succ, one_div, div_inv_eq_mul]
      have hw_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (eJ i).1.val := one_le_pow₀ (by norm_num)
      have hlt_k : ((eJ i).1.val : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast (eJ i).1.isLt
      push_cast
      nlinarith
  have hmsA : G.makespan A = (k : ℝ) := by
    refine le_antisymm ?_ ?_
    · rw [G.makespan_le_iff]
      intro j
      rw [hload_embed (relatedPureLowerNE k) j]
      split_ifs with hj
      · rw [load_relatedPureLowerNE]
        exact_mod_cast Nat.le_of_lt_succ (eM ⟨j.val, hj⟩).1.isLt
      · positivity
    · let jtop : Fin m := embedM ⟨Fin.last k, ⟨0, relatedPureLowerTierCount_pos k le_rfl⟩⟩
      have htop_lt : jtop.val < M k := (eM.symm _).isLt
      calc (k : ℝ) = G.load A jtop := by
            rw [hload_embed (relatedPureLowerNE k) jtop, dite_eq_left htop_lt]
            have hfin : (⟨jtop.val, htop_lt⟩ : Fin (M k)) =
                eM.symm ⟨Fin.last k, ⟨0, relatedPureLowerTierCount_pos k le_rfl⟩⟩ := Fin.ext rfl
            rw [hfin, eM.apply_symm_apply, load_relatedPureLowerNE]
            simp
        _ ≤ G.makespan A := G.load_le_makespan A jtop
  have hopt_le1 : G.optMakespan ≤ 1 := by
    refine (G.optMakespan_le Aopt).trans ((G.makespan_le_iff Aopt).mpr fun j => ?_)
    rw [hload_embed (relatedPureLowerOpt k) j]
    split_ifs with hj
    · exact load_relatedPureLowerOpt_le_one k _
    · exact zero_le_one
  have hopt_pos : 0 < G.optMakespan := by
    let i₀ : Fin n :=
      eJ.symm ⟨⟨0, by omega⟩, (⟨0, relatedPureLowerTierCount_pos k (by omega)⟩, ⟨0, by omega⟩)⟩
    refine G.optMakespan_pos_of_weight_pos (i := i₀) ?_
    simp [G, i₀]
  -- Asymptotic bound: `(1 / 5) * (log m / log (log m)) ≤ k`.
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hexp_lt_m : Real.exp (k : ℝ) < (m : ℝ) :=
    (exp_lt_card_relatedPureLowerMachine hk2).trans_le (by exact_mod_cast hMk_le)
  have hm_pos_real : (0 : ℝ) < (m : ℝ) := (Real.exp_pos _).trans hexp_lt_m
  have hm_le_nat : m ≤ 2 ^ (k + 2) * (k + 1) ^ (k + 1) :=
    hm_lt_next.le.trans ((card_relatedPureLowerMachine_le (k + 1)).trans
      (Nat.mul_le_mul_left _ (Nat.factorial_le_pow (k + 1))))
  have hm_le : (m : ℝ) ≤ (2 : ℝ) ^ (k + 2) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
    exact_mod_cast hm_le_nat
  have hlogm_le : Real.log (m : ℝ) ≤ 5 * (k : ℝ) * Real.log (k : ℝ) := by
    have h1 := Real.add_mul_log_two_le (d := 2) hk_real (by norm_num)
    have h2 := Real.add_one_mul_log_add_one_le hk_real
    calc Real.log (m : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (k + 2) * ((k + 1 : ℕ) : ℝ) ^ (k + 1)) :=
          Real.log_le_log hm_pos_real hm_le
      _ = ((k : ℝ) + 2) * Real.log 2 + ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; ring
      _ ≤ 5 * (k : ℝ) * Real.log (k : ℝ) := by linarith
  obtain ⟨hloglogm_pos, hratio_le_k⟩ :=
    Real.inv_mul_log_div_log_log_le hk_real (by norm_num : (0 : ℝ) < 5) hexp_lt_m hlogm_le
  have hbound :
      (1 / 5 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) * G.optMakespan ≤
        G.makespan A := by
    rw [hmsA]
    have hratio_nn : 0 ≤ (1 / 5 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) := by
      positivity
    calc (1 / 5 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) * G.optMakespan
        ≤ (1 / 5 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hopt_le1 hratio_nn
      _ ≤ (k : ℝ) := by linarith
  exact ⟨n, G, A, hA_isNE, hopt_pos, hbound⟩

end Cslib.GameTheory.LoadBalancingGame

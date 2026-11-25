/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.LoadBalancing.BallsIntoBins
public import CslibFrontier.GameTheory.LoadBalancing.RelatedPureLower
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mixed Nash price of anarchy lower bound on uniformly related machines

This module formalizes the Czumaj–Vöcking `Ω(log m / log log log m)` lower bound on the mixed
Nash price of anarchy for selfish load balancing on uniformly related machines
([CzumajVocking2002]; [Vocking2007], Theorem 20.18; locator not re-verified against primary PDF),
matching the `O(log m / log log log m)` upper bound in
`CslibFrontier.GameTheory.LoadBalancing.RelatedMixedPoA`.

## Construction

For parameters `k, B : ℕ` (`k ≥ 1`, `B ≥ 2`), `relatedMixedLower k B` replicates the `k + 1` speed
tiers of `relatedPureLower k` by a factor `B`:

* **Machines** (`RelatedMixedLowerMachine k B`): tier `t` (`0 ≤ t ≤ k`) has `B * m_t` machines of
  speed `2 ^ t`, where `m_t = relatedPureLowerTierCount k t = 2 ^ (k - t) * (k! / t!)`. In
  particular, the top tier `k` has `B` machines of speed `2 ^ k`, and total machines equal
  `B * M_k ≤ B * 2 ^ (k + 1) * k!`.
* **Jobs** (`RelatedMixedLowerJob k B`):
  - For each lower tier `t < k - 1`, `B * m_t = 2 * (t + 1) * (B * m_{t + 1})` jobs of weight
    `2 ^ t` (`RelatedMixedLowerDetJob k B`), playing **purely** on their designated machines in
    tier `t + 1` (exact load `t + 1`).
  - For the top job class `t = k - 1`, `(2 * k - 1) * B` jobs of weight `2 ^ (k - 1)`, each
    mixing **uniformly** (`1 / B`) across all `B` machines of tier `k` (expected load
    `k - 1 / 2`, deviation cost `k - 1 / (2 * B) ≤ k`).
* **Optimal makespan and task count**: mapping every lower job of type `t < k - 1` injectively to
  a tier-`t` machine and every top job injectively into tier `k - 1` (which has `2 * k * B`
  machines) gives an injective assignment of load at most `1`, proving simultaneously
  `Fintype.card (RelatedMixedLowerJob k B) ≤ Fintype.card (RelatedMixedLowerMachine k B)` and
  `0 < optMakespan ≤ 1`.
* **Mixed Nash equilibrium and balls-into-bins lower bound**: because lower jobs play purely, the
  product distribution collapses onto uniform throws of `n' = (2 * k - 1) * B` balls into the `B`
  top-tier bins (each ball contributing load `1 / 2`). Applying `ballsIntoBins_mul_tail_ge_half`
  with `B = k ^ (18 * k)` (`k ≥ 16`) and `d = ⌊4 * k * log k / log (log k)⌋₊` yields
  `expectedMakespan ≥ d / 4 ≥ (1 / 60) * (log |M| / log (log (log |M|))) * OPT`.
* **Arbitrary machine counts `m ≥ 16`** (`exists_relatedMixedNash_makespan_ge_log_div_log_log_log`,
  [Vocking2007], Theorem 20.18): padding `relatedMixedLower k (k ^ (18 * k))` with idle machines of
  speed `1 / k` extends the lower bound (preserving `n ≤ m`) to all `m ≥ M(16)`, while
  `unitIdenticalGame m` handles `16 ≤ m < M(16)`, giving a uniform constant `1 / 3200` for every
  `m ≥ 16`.

## Main definitions

* `Cslib.GameTheory.LoadBalancingGame.RelatedMixedLowerMachine`,
  `Cslib.GameTheory.LoadBalancingGame.RelatedMixedLowerDetJob`,
  `Cslib.GameTheory.LoadBalancingGame.RelatedMixedLowerJob`: machine and job index types.
* `Cslib.GameTheory.LoadBalancingGame.relatedMixedLower`: the `(k, B)` uniformly related game.
* `Cslib.GameTheory.LoadBalancingGame.relatedMixedLowerNE`: the mixed Nash strategy profile.

## Main results

* `Cslib.GameTheory.LoadBalancingGame.card_relatedMixedLowerJob_le_card_machine`: `n ≤ m`.
* `Cslib.GameTheory.LoadBalancingGame.isMixedNash_relatedMixedLowerNE`: `relatedMixedLowerNE k B`
  is a mixed Nash equilibrium for `1 ≤ k` and `1 ≤ B`.
* `Cslib.GameTheory.LoadBalancingGame.optMakespan_relatedMixedLower_le_one`,
  `Cslib.GameTheory.LoadBalancingGame.optMakespan_relatedMixedLower_pos`: `0 < optMakespan ≤ 1`.
* `Cslib.GameTheory.LoadBalancingGame.expectedMakespan_relatedMixedLowerNE_ge_log_div_log_log_log`:
  for `k ≥ 16` and `B = k ^ (18 * k)`,
  `expectedMakespan ≥ (1 / 60) * (log |M| / log (log (log |M|))) * optMakespan`.
* `Cslib.GameTheory.LoadBalancingGame.exists_relatedMixedNash_makespan_ge_log_div_log_log_log`
  ([CzumajVocking2002]; [Vocking2007], Theorem 20.18): for every `m ≥ 16`, there exist `n ≤ m`,
  a uniformly related game on `Fin n` jobs and `Fin m` machines with `0 < OPT`, and a mixed Nash
  equilibrium attaining `expectedMakespan ≥ (1 / 3200) * (log m / log (log (log m))) * OPT`.

## References

* [CzumajVocking2002]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory.LoadBalancingGame

open Finset

private theorem relatedTierCount_pred {k : ℕ} (hk : 1 ≤ k) :
    relatedPureLowerTierCount k (k - 1) = 2 * k := by
  have h := relatedPureLowerTierCount_eq_mul_succ k (t := k - 1) (by omega)
  have hkk : k - 1 + 1 = k := by omega
  rw [hkk, relatedPureLowerTierCount_last, one_mul] at h
  exact h

/-- Machine index for the `(k, B)` uniformly related mixed PoA lower-bound game: `B` replicated
copies of the `k + 1` speed tiers of `relatedPureLowerMachine k`. -/
structure RelatedMixedLowerMachine (k B : ℕ) where
  /-- Speed tier `t ∈ {0, …, k}` (machine speed `2 ^ t`). -/
  tier : Fin (k + 1)
  /-- Machine slot within `tier`. -/
  slot : Fin (relatedPureLowerTierCount k tier.val)
  /-- Replication copy index in `Fin B`. -/
  copy : Fin B
  deriving DecidableEq

/-- Lower-tier deterministic job index (tiers `t < k - 1`) in `relatedMixedLower k B`. -/
structure RelatedMixedLowerDetJob (k B : ℕ) where
  /-- Job weight tier `t < k - 1` (job weight `2 ^ t`). -/
  tier : Fin (k - 1)
  /-- Target machine slot in tier `tier + 1`. -/
  slot : Fin (relatedPureLowerTierCount k (tier.val + 1))
  /-- Local job index among the `2 * (tier + 1)` jobs assigned to `(tier + 1, slot, copy)`. -/
  idx : Fin (2 * (tier.val + 1))
  /-- Replication copy index in `Fin B`. -/
  copy : Fin B
  deriving DecidableEq

/-- Job index type for `relatedMixedLower k B`: lower-tier deterministic jobs plus
`(2 * k - 1) * B` top-tier randomizing jobs. -/
abbrev RelatedMixedLowerJob (k B : ℕ) : Type :=
  RelatedMixedLowerDetJob k B ⊕ Fin ((2 * k - 1) * B)

private def relatedMixedLowerMachineEquiv (k B : ℕ) :
    RelatedMixedLowerMachine k B ≃ relatedPureLowerMachine k × Fin B where
  toFun m := (⟨m.tier, m.slot⟩, m.copy)
  invFun := fun (⟨t, s⟩, c) => ⟨t, s, c⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def relatedMixedLowerDetJobEquiv (k B : ℕ) :
    RelatedMixedLowerDetJob k B ≃
      (Σ t : Fin (k - 1),
        Fin (relatedPureLowerTierCount k (t.val + 1)) × Fin (2 * (t.val + 1))) ×
        Fin B where
  toFun x := (⟨x.tier, (x.slot, x.idx)⟩, x.copy)
  invFun := fun (⟨t, s, i⟩, c) => ⟨t, s, i, c⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (k B : ℕ) : Finite (RelatedMixedLowerMachine k B) :=
  Finite.of_equiv _ (relatedMixedLowerMachineEquiv k B).symm

noncomputable instance (k B : ℕ) : Fintype (RelatedMixedLowerMachine k B) :=
  Fintype.ofFinite _

instance (k B : ℕ) [NeZero B] : Nonempty (RelatedMixedLowerMachine k B) :=
  ⟨⟨Fin.last k, ⟨0, relatedPureLowerTierCount_pos k le_rfl⟩, 0⟩⟩

instance (k B : ℕ) : Finite (RelatedMixedLowerDetJob k B) :=
  Finite.of_equiv _ (relatedMixedLowerDetJobEquiv k B).symm

noncomputable instance (k B : ℕ) : Fintype (RelatedMixedLowerDetJob k B) :=
  Fintype.ofFinite _

private theorem card_relatedMixedLowerMachine (k B : ℕ) :
    Fintype.card (RelatedMixedLowerMachine k B) =
      Fintype.card (relatedPureLowerMachine k) * B := by
  rw [Fintype.card_congr (relatedMixedLowerMachineEquiv k B), Fintype.card_prod, Fintype.card_fin]

/-- The designated top-tier machine `(tier k, slot 0, copy b)`. -/
private def relatedMixedTopMachine (k B : ℕ) (b : Fin B) : RelatedMixedLowerMachine k B :=
  ⟨Fin.last k, ⟨0, relatedPureLowerTierCount_pos k le_rfl⟩, b⟩

/-- The pure machine assigned to a lower-tier job under `relatedMixedLowerNE k B`. -/
private def relatedMixedDetTarget (k B : ℕ) (x : RelatedMixedLowerDetJob k B) :
    RelatedMixedLowerMachine k B :=
  ⟨⟨x.tier.val + 1, by omega⟩, x.slot, x.copy⟩

/-- **Czumaj–Vöcking mixed PoA lower-bound game** ([CzumajVocking2002]; [Vocking2007],
Theorem 20.18): `B` copies of `k + 1` speed tiers (`2 ^ t`), lower-tier jobs of weights
`2 ^ t` (`t < k - 1`), and `(2 * k - 1) * B` top-tier jobs of weight `2 ^ (k - 1)`. -/
@[expose] def relatedMixedLower (k B : ℕ) :
    LoadBalancingGame (RelatedMixedLowerJob k B) (RelatedMixedLowerMachine k B) where
  weight
    | Sum.inl x => (2 : ℝ) ^ x.tier.val
    | Sum.inr _ => (2 : ℝ) ^ (k - 1)
  speed j := (2 : ℝ) ^ j.tier.val
  weight_nonneg i := by cases i <;> positivity
  speed_pos _ := by positivity

/-- The worst-case mixed Nash equilibrium profile on `relatedMixedLower k B`: lower-tier jobs play
purely on tier `t + 1`, while the `(2 * k - 1) * B` top jobs mix uniformly across the `B` machines
of tier `k`. -/
@[expose] noncomputable def relatedMixedLowerNE (k B : ℕ) :
    RelatedMixedLowerJob k B → RelatedMixedLowerMachine k B → ℝ
  | Sum.inl x, j => if j = ⟨⟨x.tier.val + 1, by omega⟩, x.slot, x.copy⟩ then 1 else 0
  | Sum.inr _, j => if j.tier = Fin.last k then 1 / (B : ℝ) else 0

private theorem relatedMixedLowerNE_inl (k B : ℕ) (x : RelatedMixedLowerDetJob k B)
    (j : RelatedMixedLowerMachine k B) :
    relatedMixedLowerNE k B (Sum.inl x) j = if j = relatedMixedDetTarget k B x then 1 else 0 :=
  rfl

/-- Optimal-like injective assignment mapping every job to a distinct machine of equal speed. -/
private def relatedMixedLowerOpt (k B : ℕ) :
    RelatedMixedLowerJob k B → RelatedMixedLowerMachine k B
  | Sum.inl x =>
      ⟨⟨x.tier.val, by have := x.tier.isLt; omega⟩,
        (finProdFinEquiv (x.slot, x.idx)).cast
          (relatedPureLowerTierCount_eq_mul_succ k (t := x.tier.val)
            (by have := x.tier.isLt; omega)).symm,
        x.copy⟩
  | Sum.inr r =>
      let q : Fin (2 * k - 1) × Fin B := finProdFinEquiv.symm r
      have hk : 1 ≤ k := by
        have hpos : 0 < (2 * k - 1) * B := Fin.pos r
        have : 0 < 2 * k - 1 := Nat.pos_of_mul_pos_right hpos
        omega
      ⟨⟨k - 1, by omega⟩, ⟨q.1.val, by rw [relatedTierCount_pred hk]; omega⟩, q.2⟩

private theorem RelatedMixedLowerMachine.ext_val {k B : ℕ}
    {m₁ m₂ : RelatedMixedLowerMachine k B}
    (ht : m₁.tier = m₂.tier) (hs : m₁.slot.val = m₂.slot.val) (hc : m₁.copy = m₂.copy) :
    m₁ = m₂ := by
  rcases m₁ with ⟨t₁, s₁, c₁⟩
  rcases m₂ with ⟨t₂, s₂, c₂⟩
  dsimp only at ht hs hc
  subst ht hc
  exact congrArg (fun s => RelatedMixedLowerMachine.mk t₁ s c₁) (Fin.ext hs)

private theorem relatedMixedLowerOpt_injective (k B : ℕ) :
    Function.Injective (relatedMixedLowerOpt k B) := by
  intro i₁ i₂ h
  cases i₁ with
  | inl x₁ =>
    cases i₂ with
    | inl x₂ =>
      rcases x₁ with ⟨t₁, s₁, idx₁, b₁⟩
      rcases x₂ with ⟨t₂, s₂, idx₂, b₂⟩
      have hb : b₁ = b₂ := congrArg RelatedMixedLowerMachine.copy h
      subst hb
      have ht_val : t₁.val = t₂.val := by
        simpa only [relatedMixedLowerOpt] using
          congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
      have ht : t₁ = t₂ := Fin.ext ht_val
      subst ht
      have hslot_val : (finProdFinEquiv (s₁, idx₁)).val = (finProdFinEquiv (s₂, idx₂)).val := by
        simpa only [relatedMixedLowerOpt, Fin.val_cast] using
          congrArg (fun m : RelatedMixedLowerMachine k B => m.slot.val) h
      have hp : (s₁, idx₁) = (s₂, idx₂) := finProdFinEquiv.injective (Fin.ext hslot_val)
      cases hp
      rfl
    | inr r₂ =>
      have hval := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
      simp only [relatedMixedLowerOpt] at hval
      omega
  | inr r₁ =>
    cases i₂ with
    | inl x₂ =>
      have hval := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
      simp only [relatedMixedLowerOpt] at hval
      omega
    | inr r₂ =>
      have hb : (finProdFinEquiv.symm r₁).2 = (finProdFinEquiv.symm r₂).2 :=
        congrArg RelatedMixedLowerMachine.copy h
      have hq1_val : (finProdFinEquiv.symm r₁).1.val = (finProdFinEquiv.symm r₂).1.val := by
        simpa only [relatedMixedLowerOpt] using
          congrArg (fun m : RelatedMixedLowerMachine k B => m.slot.val) h
      have hpair : finProdFinEquiv.symm r₁ = finProdFinEquiv.symm r₂ :=
        Prod.ext (Fin.ext hq1_val) hb
      exact congrArg Sum.inr (finProdFinEquiv.symm.injective hpair)

/-- The number of jobs in `relatedMixedLower k B` never exceeds the number of machines. -/
theorem card_relatedMixedLowerJob_le_card_machine (k B : ℕ) :
    Fintype.card (RelatedMixedLowerJob k B) ≤ Fintype.card (RelatedMixedLowerMachine k B) :=
  Fintype.card_le_of_injective _ (relatedMixedLowerOpt_injective k B)

private theorem load_relatedMixedLowerOpt_le_one (k B : ℕ) (j : RelatedMixedLowerMachine k B) :
    (relatedMixedLower k B).load (relatedMixedLowerOpt k B) j ≤ 1 := by
  rw [LoadBalancingGame.load_eq_sum_div]
  set S := univ.filter fun i : RelatedMixedLowerJob k B => relatedMixedLowerOpt k B i = j
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hS
    have hAi₀ : relatedMixedLowerOpt k B i₀ = j := (mem_filter.mp hi₀).2
    have hSing : S = {i₀} := by
      ext i
      simp only [S, mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun hi => relatedMixedLowerOpt_injective k B (hi.trans hAi₀.symm),
        fun hi => hi ▸ hAi₀⟩
    rw [show (∑ i with relatedMixedLowerOpt k B i = j, (relatedMixedLower k B).weight i) =
        ∑ i ∈ S, (relatedMixedLower k B).weight i from rfl, hSing, sum_singleton]
    cases i₀ with
    | inl x =>
      have ht_eq : x.tier.val = j.tier.val := by
        have := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) hAi₀
        simpa only [relatedMixedLowerOpt] using this
      simp only [relatedMixedLower, ht_eq]
      rw [div_self (by positivity)]
    | inr r =>
      have ht_eq : k - 1 = j.tier.val := by
        have := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) hAi₀
        simpa only [relatedMixedLowerOpt] using this
      simp only [relatedMixedLower, ht_eq]
      rw [div_self (by positivity)]
  · rw [not_nonempty_iff_eq_empty] at hS
    rw [show (∑ i with relatedMixedLowerOpt k B i = j, (relatedMixedLower k B).weight i) =
        ∑ i ∈ S, (relatedMixedLower k B).weight i from rfl, hS, sum_empty, zero_div]
    exact zero_le_one

/-- The optimal makespan of `relatedMixedLower k B` is at most `1`. -/
theorem optMakespan_relatedMixedLower_le_one (k B : ℕ) [NeZero B] :
    (relatedMixedLower k B).optMakespan ≤ 1 :=
  ((relatedMixedLower k B).optMakespan_le (relatedMixedLowerOpt k B)).trans
    (((relatedMixedLower k B).makespan_le_iff _).mpr (load_relatedMixedLowerOpt_le_one k B))

/-- Any load-balancing game on a nonempty machine set with at least one positive-weight job has
strictly positive `optMakespan`. -/
private theorem optMakespan_pos_of_exists_weight_pos {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype M] [DecidableEq M] [Nonempty M] (G : LoadBalancingGame ι M)
    (hw : ∃ i : ι, 0 < G.weight i) :
    0 < G.optMakespan := by
  obtain ⟨i₀, hi₀⟩ := hw
  have hsum_pos : 0 < ∑ i : ι, G.weight i :=
    sum_pos' (fun i _ => G.weight_nonneg i) ⟨i₀, mem_univ i₀, hi₀⟩
  have hvol := G.sum_weight_le_sum_speed_mul_optMakespan
  have hsp_pos : 0 < ∑ j : M, G.speed j := sum_pos (fun j _ => G.speed_pos j) univ_nonempty
  by_contra hle
  push Not at hle
  have h0 : (∑ j : M, G.speed j) * G.optMakespan ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsp_pos.le hle
  linarith

private theorem two_pow_sub_one_div_two_pow {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ (k - 1) / (2 : ℝ) ^ k = 1 / 2 := by
  have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
    have : k = (k - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
  rw [hpow]
  have hne : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
  field_simp [hne]

/-- For `k ≥ 1` and `B ≥ 1`, `relatedMixedLower k B` has strictly positive optimal makespan. -/
theorem optMakespan_relatedMixedLower_pos (k B : ℕ) [NeZero B] (hk : 1 ≤ k) :
    0 < (relatedMixedLower k B).optMakespan :=
  optMakespan_pos_of_exists_weight_pos (relatedMixedLower k B)
    ⟨Sum.inr ⟨0, Nat.mul_pos (by have := hk; omega) (NeZero.pos B)⟩, by simp [relatedMixedLower]⟩

/-- Exact expected load of every machine under `relatedMixedLowerNE k B`: machines in tier `r < k`
have expected load `r`, while machines in tier `k` have expected load `k - 1 / 2`. -/
theorem expectedLoad_relatedMixedLowerNE {k B : ℕ} [NeZero B] (hk : 1 ≤ k)
    (j : RelatedMixedLowerMachine k B) :
    (relatedMixedLower k B).expectedLoad (relatedMixedLowerNE k B) j =
      if j.tier = Fin.last k then (k : ℝ) - 1 / 2 else (j.tier.val : ℝ) := by
  have hB_pos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (NeZero.pos B)
  rw [expectedLoad, Fintype.sum_sum_type]
  rcases j with ⟨r, u, b⟩
  by_cases hlast : r = Fin.last k
  · subst hlast
    rw [ite_eq_left rfl]
    -- No lower-tier job targets tier `k`.
    have hleft : ∑ x : RelatedMixedLowerDetJob k B,
        relatedMixedLowerNE k B (Sum.inl x) ⟨Fin.last k, u, b⟩ *
          ((relatedMixedLower k B).weight (Sum.inl x) /
            (relatedMixedLower k B).speed ⟨Fin.last k, u, b⟩) = 0 := by
      refine sum_eq_zero fun x _ => ?_
      have hne : (⟨Fin.last k, u, b⟩ : RelatedMixedLowerMachine k B) ≠
          relatedMixedDetTarget k B x := by
        intro h
        have hval := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
        simp only [relatedMixedDetTarget, Fin.val_last] at hval
        omega
      rw [relatedMixedLowerNE_inl, ite_eq_right hne, zero_mul]
    rw [hleft, zero_add]
    simp only [relatedMixedLowerNE, ↓reduceIte, relatedMixedLower, Fin.val_last,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
    rw [hpow, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    push_cast
    have hpow_ne : (2 : ℝ) ^ (k - 1) ≠ 0 := by positivity
    field_simp [hB_pos.ne', hpow_ne]
  · rw [ite_eq_right hlast]
    -- No top-tier job targets tier `r < k`.
    have hright : ∑ i : Fin ((2 * k - 1) * B),
        relatedMixedLowerNE k B (Sum.inr i) ⟨r, u, b⟩ *
          ((relatedMixedLower k B).weight (Sum.inr i) /
            (relatedMixedLower k B).speed ⟨r, u, b⟩) = 0 := by
      refine sum_eq_zero fun i _ => ?_
      simp only [relatedMixedLowerNE, ite_eq_right hlast, zero_mul]
    rw [hright, add_zero]
    have hr_lt : r.val < k := by
      have := r.isLt
      have hne : r.val ≠ k := fun h => hlast (Fin.ext (by simpa using h))
      omega
    by_cases hr0 : r.val = 0
    · have hleft : ∑ x : RelatedMixedLowerDetJob k B,
          relatedMixedLowerNE k B (Sum.inl x) ⟨r, u, b⟩ *
            ((relatedMixedLower k B).weight (Sum.inl x) /
              (relatedMixedLower k B).speed ⟨r, u, b⟩) = 0 := by
        refine sum_eq_zero fun x _ => ?_
        have hne : (⟨r, u, b⟩ : RelatedMixedLowerMachine k B) ≠
            relatedMixedDetTarget k B x := by
          intro h
          have hval := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
          simp only [relatedMixedDetTarget] at hval
          omega
        rw [relatedMixedLowerNE_inl, ite_eq_right hne, zero_mul]
      rw [hleft, hr0, Nat.cast_zero]
    · set t : Fin (k - 1) := ⟨r.val - 1, by omega⟩
      have ht_succ : t.val + 1 = r.val := by simp only [t]; omega
      have hu_eq : relatedPureLowerTierCount k (t.val + 1) = relatedPureLowerTierCount k r.val := by
        rw [ht_succ]
      let u' : Fin (relatedPureLowerTierCount k (t.val + 1)) := u.cast hu_eq.symm
      let emb : Fin (2 * (t.val + 1)) → RelatedMixedLowerDetJob k B :=
        fun v => ⟨t, u', v, b⟩
      have hemb_inj : Function.Injective emb := by
        intro v₁ v₂ h
        cases h
        rfl
      have hfilt :
          (univ.filter fun x : RelatedMixedLowerDetJob k B =>
              (⟨r, u, b⟩ : RelatedMixedLowerMachine k B) = relatedMixedDetTarget k B x) =
            univ.image emb := by
        ext ⟨t₁, u₁, v₁, b₁⟩
        rw [Finset.mem_filter, Finset.mem_image]
        simp only [mem_univ, true_and, emb, relatedMixedDetTarget]
        constructor
        · intro h
          have hb1 : b = b₁ := congrArg RelatedMixedLowerMachine.copy h
          subst hb1
          have ht1_val : r.val = t₁.val + 1 :=
            congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
          have ht1 : t₁ = t := Fin.ext (by omega)
          subst ht1
          have hu_val : u.val = u₁.val :=
            congrArg (fun m : RelatedMixedLowerMachine k B => m.slot.val) h
          have hu1 : u' = u₁ := Fin.ext (by simpa only [u', Fin.val_cast] using hu_val)
          subst hu1
          exact ⟨v₁, rfl⟩
        · rintro ⟨v, hv⟩
          cases hv
          exact RelatedMixedLowerMachine.ext_val (Fin.ext ht_succ.symm) (by simp [u']) rfl
      have hsum_filt :
          ∑ x : RelatedMixedLowerDetJob k B,
            relatedMixedLowerNE k B (Sum.inl x) ⟨r, u, b⟩ *
              ((relatedMixedLower k B).weight (Sum.inl x) /
                (relatedMixedLower k B).speed ⟨r, u, b⟩) =
          ∑ x ∈ univ.filter (fun x =>
              (⟨r, u, b⟩ : RelatedMixedLowerMachine k B) = relatedMixedDetTarget k B x),
            ((relatedMixedLower k B).weight (Sum.inl x) /
              (relatedMixedLower k B).speed ⟨r, u, b⟩) := by
        rw [sum_filter]
        refine sum_congr rfl fun x _ => ?_
        rw [relatedMixedLowerNE_inl]
        split_ifs <;> ring
      rw [hsum_filt, hfilt, sum_image (fun _ _ _ _ h => hemb_inj h)]
      simp only [emb, relatedMixedLower, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ht_succ, pow_succ]
      have hpow_ne : (2 : ℝ) ^ t.val ≠ 0 := by positivity
      push_cast
      field_simp [hpow_ne]

/-- For `k ≥ 1` and `B ≥ 1`, `relatedMixedLowerNE k B` is a mixed Nash equilibrium of
`relatedMixedLower k B`. -/
theorem isMixedNash_relatedMixedLowerNE {k B : ℕ} [NeZero B] (hk : 1 ≤ k) :
    (relatedMixedLower k B).toCostGame.IsMixedNash (relatedMixedLowerNE k B) := by
  have hB_pos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (NeZero.pos B)
  rw [(relatedMixedLower k B).isMixedNash_iff]
  refine ⟨fun i => ?_, fun i j hpos j' => ?_⟩
  · -- Verify `IsMixedStrategy (relatedMixedLowerNE k B i)`.
    rw [isMixedStrategy_iff]
    cases i with
    | inl x =>
      refine ⟨fun j => by simp only [relatedMixedLowerNE]; split_ifs <;> norm_num, ?_⟩
      simp only [relatedMixedLowerNE, sum_ite_eq', mem_univ, ↓reduceIte]
    | inr r =>
      refine ⟨fun j => by simp only [relatedMixedLowerNE]; split_ifs <;> positivity, ?_⟩
      have hfilt :
          (univ.filter fun j : RelatedMixedLowerMachine k B => j.tier = Fin.last k) =
            univ.image (relatedMixedTopMachine k B) := by
        ext ⟨s, u, b⟩
        simp only [mem_filter, mem_univ, true_and, mem_image, relatedMixedTopMachine]
        constructor
        · intro hs
          subst hs
          refine ⟨b, ?_⟩
          have hu_lt : u.val < 1 := by
            simpa only [Fin.val_last, relatedPureLowerTierCount_last] using u.isLt
          have hu0 : (⟨0, relatedPureLowerTierCount_pos k le_rfl⟩ :
              Fin (relatedPureLowerTierCount k (Fin.last k).val)) = u :=
            Fin.ext (show (0 : ℕ) = u.val by omega)
          rw [hu0]
        · rintro ⟨b', hb'⟩
          exact congrArg RelatedMixedLowerMachine.tier hb'.symm
      have hinj : Function.Injective (relatedMixedTopMachine k B) := fun b₁ b₂ h =>
        congrArg RelatedMixedLowerMachine.copy h
      simp only [relatedMixedLowerNE, ← sum_filter, hfilt,
        sum_image (fun _ _ _ _ h => hinj h), sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hB_pos.ne']
  · -- Verify no profitable deviation from `j` to `j'`.
    rw [expectedLoad_relatedMixedLowerNE hk j, expectedLoad_relatedMixedLowerNE hk j']
    cases i with
    | inl x =>
      have hj_eq : j = relatedMixedDetTarget k B x := by
        by_contra hne
        rw [relatedMixedLowerNE_inl, ite_eq_right hne] at hpos
        exact lt_irrefl 0 hpos
      subst hj_eq
      have hnotlast : (relatedMixedDetTarget k B x).tier ≠ Fin.last k := by
        intro h
        have hv := congrArg Fin.val h
        simp only [relatedMixedDetTarget, Fin.val_last] at hv
        omega
      rw [ite_eq_right hnotlast, relatedMixedLowerNE_inl, ite_eq_left rfl, sub_self, zero_mul,
        add_zero, relatedMixedLowerNE_inl]
      by_cases hj'_eq : j' = relatedMixedDetTarget k B x
      · subst hj'_eq
        rw [ite_eq_right hnotlast, ite_eq_left rfl, sub_self, zero_mul, add_zero]
      · rw [ite_eq_right hj'_eq, sub_zero, one_mul]
        simp only [relatedMixedDetTarget]
        by_cases hj'_last : j'.tier = Fin.last k
        · rw [ite_eq_left hj'_last]
          have hnn : 0 ≤ (relatedMixedLower k B).weight (Sum.inl x) /
              (relatedMixedLower k B).speed j' :=
            div_nonneg ((relatedMixedLower k B).weight_nonneg _)
              ((relatedMixedLower k B).speed_pos _).le
          have hlt : (x.tier.val : ℝ) + 1 ≤ (k : ℝ) - 1 := by
            have := x.tier.isLt
            have h1 : x.tier.val + 1 ≤ k - 1 := by omega
            have h2 : ((x.tier.val + 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast h1
            rw [Nat.cast_sub hk] at h2
            push_cast at h2
            linarith
          push_cast
          linarith
        · rw [ite_eq_right hj'_last]
          simp only [relatedMixedLower]
          by_cases hrt : x.tier.val + 1 ≤ j'.tier.val
          · have hrt' : (x.tier.val : ℝ) + 1 ≤ (j'.tier.val : ℝ) := by exact_mod_cast hrt
            have hnn : 0 ≤ (2 : ℝ) ^ x.tier.val / (2 : ℝ) ^ j'.tier.val := by positivity
            push_cast
            linarith
          · have hle : j'.tier.val ≤ x.tier.val := by omega
            set d : ℕ := x.tier.val - j'.tier.val
            have htr : x.tier.val = j'.tier.val + d := by omega
            have hdiv : (2 : ℝ) ^ x.tier.val / (2 : ℝ) ^ j'.tier.val = (2 : ℝ) ^ d := by
              rw [htr, pow_add, mul_div_cancel_left₀ _ (by positivity)]
            have h2d : (d : ℝ) + 1 ≤ (2 : ℝ) ^ d := by exact_mod_cast Nat.lt_two_pow_self (n := d)
            have htr' : (x.tier.val : ℝ) = (j'.tier.val : ℝ) + (d : ℝ) := by exact_mod_cast htr
            rw [hdiv]
            push_cast
            linarith
    | inr r =>
      have hj_last : j.tier = Fin.last k := by
        by_contra hne
        simp only [relatedMixedLowerNE, ite_eq_right hne] at hpos
        exact lt_irrefl 0 hpos
      rw [ite_eq_left hj_last]
      simp only [relatedMixedLowerNE, hj_last, ↓reduceIte, relatedMixedLower, Fin.val_last]
      have hpow_k : (2 : ℝ) ^ (k - 1) / (2 : ℝ) ^ k = 1 / 2 := two_pow_sub_one_div_two_pow hk
      rw [hpow_k]
      by_cases hj'_last : j'.tier = Fin.last k
      · rw [ite_eq_left hj'_last, ite_eq_left hj'_last, hj'_last, Fin.val_last, hpow_k]
      · rw [ite_eq_right hj'_last, ite_eq_right hj'_last, sub_zero, one_mul]
        have hj'_lt : j'.tier.val < k := by
          have := j'.tier.isLt
          have hne : j'.tier.val ≠ k := fun h => hj'_last (Fin.ext (by simpa using h))
          omega
        set d : ℕ := (k - 1) - j'.tier.val
        have hkr : k - 1 = j'.tier.val + d := by omega
        have hdiv : (2 : ℝ) ^ (k - 1) / (2 : ℝ) ^ j'.tier.val = (2 : ℝ) ^ d := by
          rw [hkr, pow_add, mul_div_cancel_left₀ _ (by positivity)]
        have h2d : (d : ℝ) + 1 ≤ (2 : ℝ) ^ d := by exact_mod_cast Nat.lt_two_pow_self (n := d)
        have hk_eq : (k : ℝ) = (j'.tier.val : ℝ) + (d : ℝ) + 1 := by
          have : k = j'.tier.val + d + 1 := by omega
          exact_mod_cast this
        rw [hdiv]
        have hinv_nn : 0 ≤ 1 / (B : ℝ) := by positivity
        linarith

/-- Lift a top-tier assignment `f : Fin ((2 * k - 1) * B) → Fin B` to a full pure assignment of
`relatedMixedLower k B` by fixing all lower-tier jobs to their pure machines. -/
private def liftTopAssignment (k B : ℕ) (f : Fin ((2 * k - 1) * B) → Fin B) :
    RelatedMixedLowerJob k B → RelatedMixedLowerMachine k B
  | Sum.inl x => relatedMixedDetTarget k B x
  | Sum.inr r => relatedMixedTopMachine k B (f r)

private theorem liftTopAssignment_injective (k B : ℕ) :
    Function.Injective (liftTopAssignment k B) := by
  intro f₁ f₂ h
  funext r
  have hr := congrFun h (Sum.inr r)
  exact congrArg RelatedMixedLowerMachine.copy hr

private theorem productWeight_liftTopAssignment (k B : ℕ) (f : Fin ((2 * k - 1) * B) → Fin B) :
    productWeight (relatedMixedLowerNE k B) (liftTopAssignment k B f) =
      (1 / (B : ℝ)) ^ ((2 * k - 1) * B) := by
  rw [productWeight_def, Fintype.prod_sum_type]
  have hleft : ∏ x : RelatedMixedLowerDetJob k B,
      relatedMixedLowerNE k B (Sum.inl x) (liftTopAssignment k B f (Sum.inl x)) = 1 := by
    refine prod_eq_one fun x _ => ?_
    rw [relatedMixedLowerNE_inl, liftTopAssignment, ite_eq_left rfl]
  rw [hleft, one_mul]
  simp only [relatedMixedLowerNE, liftTopAssignment, relatedMixedTopMachine, ↓reduceIte,
    prod_const, card_univ, Fintype.card_fin]

private theorem load_liftTopAssignment_top {k B : ℕ} (hk : 1 ≤ k)
    (f : Fin ((2 * k - 1) * B) → Fin B) (b : Fin B) :
    (relatedMixedLower k B).load (liftTopAssignment k B f) (relatedMixedTopMachine k B b) =
      (#(univ.filter fun r : Fin ((2 * k - 1) * B) => f r = b) : ℝ) / 2 := by
  rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fintype.sum_sum_type]
  have hleft : ∑ x : RelatedMixedLowerDetJob k B,
      (if liftTopAssignment k B f (Sum.inl x) = relatedMixedTopMachine k B b then
        (relatedMixedLower k B).weight (Sum.inl x) else 0) = 0 := by
    refine sum_eq_zero fun x _ => ?_
    have hne : liftTopAssignment k B f (Sum.inl x) ≠ relatedMixedTopMachine k B b := by
      intro h
      have hv := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
      simp only [liftTopAssignment, relatedMixedDetTarget, relatedMixedTopMachine,
        Fin.val_last] at hv
      omega
    rw [ite_eq_right hne]
  rw [hleft, zero_add]
  have hright :
      ∑ r : Fin ((2 * k - 1) * B),
        (if liftTopAssignment k B f (Sum.inr r) = relatedMixedTopMachine k B b then
          (relatedMixedLower k B).weight (Sum.inr r) else 0) =
      (#(univ.filter fun r : Fin ((2 * k - 1) * B) => f r = b) : ℝ) * (2 : ℝ) ^ (k - 1) := by
    have hiff : ∀ r : Fin ((2 * k - 1) * B),
        (liftTopAssignment k B f (Sum.inr r) = relatedMixedTopMachine k B b) ↔ f r = b := by
      intro r
      constructor
      · intro h; exact congrArg RelatedMixedLowerMachine.copy h
      · intro h; simp [liftTopAssignment, h]
    simp_rw [hiff]
    rw [← sum_filter]
    simp [relatedMixedLower]
  rw [hright]
  simp only [relatedMixedLower, relatedMixedTopMachine, Fin.val_last, mul_div_assoc,
    two_pow_sub_one_div_two_pow hk]
  ring

/-- Balls-into-bins lower bound for `relatedMixedLower k B`: whenever `d` satisfies the
`ballsIntoBins_mul_tail_ge_half` threshold for `a = 2 * k - 1` and `B` bins,
`(relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) ≥ d / 4`. -/
private theorem expectedMakespan_relatedMixedLowerNE_ge_quarter_of_ballsIntoBins
    {k B d : ℕ} [NeZero B] (hk : 1 ≤ k) (hB : 2 ≤ B) (hd : 2 * (2 * k - 1) ≤ d)
    (h2d : 2 * d ≤ (2 * k - 1) * B)
    (hcond : 3 ^ (2 * k - 1) * 2 ^ d * d.factorial ≤ B * (2 * k - 1) ^ d) :
    (d : ℝ) / 4 ≤ (relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) := by
  have htail := ballsIntoBins_mul_tail_ge_half (n := (2 * k - 1) * B) (a := 2 * k - 1) (B := B)
    (d := d) rfl (by omega) hB hd h2d hcond
  have hp_nn : ∀ i j, 0 ≤ relatedMixedLowerNE k B i j :=
    fun i j => ((isMixedNash_relatedMixedLowerNE (B := B) hk).1 i).nonneg j
  have hsub :
      ∑ f : Fin ((2 * k - 1) * B) → Fin B,
        productWeight (relatedMixedLowerNE k B) (liftTopAssignment k B f) *
          (relatedMixedLower k B).makespan (liftTopAssignment k B f) ≤
      (relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) := by
    rw [expectedMakespan, ← sum_image (f := fun A =>
        productWeight (relatedMixedLowerNE k B) A * (relatedMixedLower k B).makespan A)
      (fun _ _ _ _ h => liftTopAssignment_injective k B h)]
    exact sum_le_univ_sum_of_nonneg fun A =>
      mul_nonneg (productWeight_nonneg hp_nn A) ((relatedMixedLower k B).makespan_nonneg A)
  have hpt : ∀ f : Fin ((2 * k - 1) * B) → Fin B,
      ((d : ℝ) / 2) *
        (if ∃ b : Fin B, d ≤ #(univ.filter fun r : Fin ((2 * k - 1) * B) => f r = b) then
          (1 / (B : ℝ)) ^ ((2 * k - 1) * B) else 0) ≤
      productWeight (relatedMixedLowerNE k B) (liftTopAssignment k B f) *
        (relatedMixedLower k B).makespan (liftTopAssignment k B f) := by
    intro f
    rw [productWeight_liftTopAssignment]
    have hw_nn : 0 ≤ (1 / (B : ℝ)) ^ ((2 * k - 1) * B) := by positivity
    split_ifs with hex
    · obtain ⟨b, hb⟩ := hex
      have hms_ge : (d : ℝ) / 2 ≤ (relatedMixedLower k B).makespan (liftTopAssignment k B f) := by
        calc (d : ℝ) / 2
            ≤ (#(univ.filter fun r : Fin ((2 * k - 1) * B) => f r = b) : ℝ) / 2 := by
              have : (d : ℝ) ≤ (#(univ.filter fun r => f r = b) : ℝ) := by exact_mod_cast hb
              linarith
          _ = (relatedMixedLower k B).load (liftTopAssignment k B f)
                (relatedMixedTopMachine k B b) := (load_liftTopAssignment_top hk f b).symm
          _ ≤ (relatedMixedLower k B).makespan (liftTopAssignment k B f) :=
              (relatedMixedLower k B).load_le_makespan _ _
      nlinarith
    · rw [mul_zero]
      exact mul_nonneg hw_nn ((relatedMixedLower k B).makespan_nonneg _)
  calc (d : ℝ) / 4 = ((d : ℝ) / 2) * (1 / 2 : ℝ) := by ring
    _ ≤ ((d : ℝ) / 2) * ∑ f : Fin ((2 * k - 1) * B) → Fin B,
          if ∃ b : Fin B, d ≤ #(univ.filter fun r : Fin ((2 * k - 1) * B) => f r = b) then
            (1 / (B : ℝ)) ^ ((2 * k - 1) * B) else 0 :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = ∑ f : Fin ((2 * k - 1) * B) → Fin B, ((d : ℝ) / 2) *
          (if ∃ b : Fin B, d ≤ #(univ.filter fun r : Fin ((2 * k - 1) * B) => f r = b) then
            (1 / (B : ℝ)) ^ ((2 * k - 1) * B) else 0) := mul_sum _ _ _
    _ ≤ ∑ f : Fin ((2 * k - 1) * B) → Fin B,
          productWeight (relatedMixedLowerNE k B) (liftTopAssignment k B f) *
            (relatedMixedLower k B).makespan (liftTopAssignment k B f) :=
        sum_le_sum fun f _ => hpt f
    _ ≤ (relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) := hsub

/-- Shared threshold bound for `k ≥ 16`: `e < log k` and `1 < log (log k)`. -/
private theorem exp_one_lt_log_of_sixteen_le {k : ℕ} (hk : 16 ≤ k) :
    Real.exp 1 < Real.log (k : ℝ) ∧ 1 < Real.log (Real.log (k : ℝ)) := by
  have hk_real : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp1_lt_log16 : Real.exp 1 < Real.log (16 : ℝ) := by
    have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
  have hx : Real.exp 1 < Real.log (k : ℝ) :=
    hexp1_lt_log16.trans_le (Real.log_le_log (by norm_num) hk_real)
  refine ⟨hx, ?_⟩
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) hx

/-- Shared threshold verification for `B = k ^ (18 * k)` and `d = ⌊4 * k * log k / log (log k)⌋₊`
when `k ≥ 16`. -/
private theorem ballsIntoBins_params_of_ge_sixteen {k : ℕ} (hk : 16 ≤ k) :
    let B : ℕ := k ^ (18 * k)
    let d : ℕ := ⌊4 * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))⌋₊
    2 ≤ B ∧
    2 * (2 * k - 1) ≤ d ∧
    2 * d ≤ (2 * k - 1) * B ∧
    3 ^ (2 * k - 1) * 2 ^ d * d.factorial ≤ B * (2 * k - 1) ^ d ∧
    3 * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ)) ≤ (d : ℝ) := by
  intro B d
  have hk_real : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨hx_gt_e, hy_gt1⟩ := exp_one_lt_log_of_sixteen_le hk
  set x : ℝ := Real.log (k : ℝ)
  have he_gt2 : (2 : ℝ) < Real.exp 1 := by
    linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  have hx_pos : 0 < x := by linarith
  set y : ℝ := Real.log x
  have hy_pos : 0 < y := by linarith
  have hy_le_x_div2 : y ≤ x / 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx_pos (Real.exp_pos 1))
    rw [Real.log_div hx_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
    have h2 : x / Real.exp 1 ≤ x / 2 :=
      div_le_div_of_nonneg_left hx_pos.le (by norm_num) he_gt2.le
    linarith
  have hxy_ge2 : 2 ≤ x / y := (le_div_iff₀ hy_pos).mpr (by linarith)
  have hd_le_real : (d : ℝ) ≤ 4 * (k : ℝ) * x / y :=
    Nat.floor_le (by positivity)
  have hd_gt_sub1 : 4 * (k : ℝ) * x / y - 1 < (d : ℝ) := by
    have := Nat.lt_floor_add_one (4 * (k : ℝ) * x / y)
    linarith
  have hd_ge_3 : 3 * (k : ℝ) * x / y ≤ (d : ℝ) := by
    have h1 : 1 ≤ (k : ℝ) * x / y := by
      have : (k : ℝ) * (x / y) = (k : ℝ) * x / y := by ring
      nlinarith
    have h2 : 3 * (k : ℝ) * x / y + (k : ℝ) * x / y = 4 * (k : ℝ) * x / y := by ring
    linarith
  have hB2 : 2 ≤ B := by
    have h1 : 16 ^ 1 ≤ k ^ (18 * k) :=
      (Nat.pow_le_pow_left hk 1).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hd_ge_2a : 2 * (2 * k - 1) ≤ d := by
    have h8k : (8 : ℝ) * (k : ℝ) ≤ 4 * (k : ℝ) * x / y := by
      have : 4 * (k : ℝ) * (x / y) = 4 * (k : ℝ) * x / y := by ring
      nlinarith
    have h2a_r : ((2 * (2 * k - 1) : ℕ) : ℝ) ≤ 4 * (k : ℝ) * x / y := by
      have hnat : 2 * (2 * k - 1) ≤ 8 * k := by omega
      have : ((2 * (2 * k - 1) : ℕ) : ℝ) ≤ 8 * (k : ℝ) := by exact_mod_cast hnat
      linarith
    exact (Nat.le_floor_iff (by positivity)).mpr h2a_r
  have h2d_le_aB : 2 * d ≤ (2 * k - 1) * B := by
    have hx_le_k : x ≤ (k : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (k : ℝ))]
    have hd_le_4k2 : (d : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by
      have h1 : 4 * (k : ℝ) * x / y ≤ 4 * (k : ℝ) * x :=
        div_le_self (by positivity) hy_gt1.le
      nlinarith
    have hd_nat : d ≤ 4 * k ^ 2 := by exact_mod_cast hd_le_4k2
    have hB_ge_k2 : k ^ 2 ≤ B := Nat.pow_le_pow_right (by omega) (by omega)
    have ha_ge8 : 8 ≤ 2 * k - 1 := by omega
    have hmul : 8 * k ^ 2 ≤ (2 * k - 1) * B := Nat.mul_le_mul ha_ge8 hB_ge_k2
    omega
  have hcond : 3 ^ (2 * k - 1) * 2 ^ d * d.factorial ≤ B * (2 * k - 1) ^ d := by
    set a : ℕ := 2 * k - 1
    have ha_ge_k : k ≤ a := by omega
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hd_pos : 0 < d := by omega
    have hd_pos_r : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
    have hB_pos_r : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by omega)
    -- Suffices to compare `3^a * (2 * d)^d ≤ B * a^d` via logarithms.
    suffices hpow : 3 ^ a * 2 ^ d * d ^ d ≤ B * a ^ d by
      exact (Nat.mul_le_mul_left _ (Nat.factorial_le_pow d)).trans hpow
    have hlog_lhs_le : Real.log ((3 : ℝ) ^ a * (2 : ℝ) ^ d * (d : ℝ) ^ d) ≤
        Real.log ((B : ℝ) * (a : ℝ) ^ d) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
      have hlogB : Real.log (B : ℝ) = (18 * (k : ℝ)) * x := by
        have hBcast : (B : ℝ) = (k : ℝ) ^ (18 * k) := by exact_mod_cast rfl
        rw [hBcast, Real.log_pow]
        push_cast
        ring
      rw [hlogB]
      -- Term 1: `a * log 3 ≤ 2 * k * x`.
      have hterm1 : (a : ℝ) * Real.log 3 ≤ 2 * (k : ℝ) * x := by
        have ha_le : (a : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (by omega : a ≤ 2 * k)
        have hlog3 : Real.log 3 ≤ x := Real.log_le_log (by norm_num) (by linarith)
        have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        nlinarith
      -- Term 2: `d * (log 2 + log d - log a) ≤ 16 * k * x`.
      have hterm2 :
          (d : ℝ) * Real.log 2 + (d : ℝ) * Real.log (d : ℝ) - (d : ℝ) * Real.log (a : ℝ) ≤
            16 * (k : ℝ) * x := by
        have hrew :
            (d : ℝ) * Real.log 2 + (d : ℝ) * Real.log (d : ℝ) - (d : ℝ) * Real.log (a : ℝ) =
              (d : ℝ) * Real.log (2 * (d : ℝ) / (a : ℝ)) := by
          rw [Real.log_div (by positivity) ha_pos.ne', Real.log_mul (by norm_num) hd_pos_r.ne']
          ring
        rw [hrew]
        have hratio_le : 2 * (d : ℝ) / (a : ℝ) ≤ 8 * x := by
          have hd_le_4kx : (d : ℝ) ≤ 4 * (k : ℝ) * x :=
            hd_le_real.trans (div_le_self (by positivity) hy_gt1.le)
          have ha_ge_kr : (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha_ge_k
          rw [div_le_iff₀ ha_pos]
          nlinarith
        have hlog_ratio : Real.log (2 * (d : ℝ) / (a : ℝ)) ≤ 4 * y := by
          have h1 : Real.log (2 * (d : ℝ) / (a : ℝ)) ≤ Real.log (8 * x) :=
            Real.log_le_log (by positivity) hratio_le
          have hlog8 : Real.log 8 ≤ 3 := by
            have hlog2 : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
              linarith
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]
            push_cast
            linarith
          rw [Real.log_mul (by norm_num) hx_pos.ne'] at h1
          linarith
        calc (d : ℝ) * Real.log (2 * (d : ℝ) / (a : ℝ))
            ≤ (d : ℝ) * (4 * y) := mul_le_mul_of_nonneg_left hlog_ratio hd_pos_r.le
          _ ≤ (4 * (k : ℝ) * x / y) * (4 * y) :=
              mul_le_mul_of_nonneg_right hd_le_real (by positivity)
          _ = 16 * (k : ℝ) * x := by field_simp [hy_pos.ne']; ring
      linarith
    have hreal_le : (3 : ℝ) ^ a * (2 : ℝ) ^ d * (d : ℝ) ^ d ≤ (B : ℝ) * (a : ℝ) ^ d := by
      have := Real.exp_le_exp.mpr hlog_lhs_le
      rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at this
    exact_mod_cast hreal_le
  exact ⟨hB2, hd_ge_2a, h2d_le_aB, hcond, hd_ge_3⟩

/-- Iterated-logarithm lower bound shared across `relatedMixedLower` and its `Fin m` padding:
when `16 ≤ k`, `B = k ^ (18 * k)`, and `B ≤ X`, we have `log B = 18 * k * log k`, `(k : ℝ) < log X`,
and `log (log k) < log (log (log X))`. -/
private theorem log_log_lt_log_log_log_of_pow_le {k B X : ℕ} (hk : 16 ≤ k)
    (hB : B = k ^ (18 * k)) (hBX : B ≤ X) :
    Real.log (B : ℝ) = 18 * (k : ℝ) * Real.log (k : ℝ) ∧
    (k : ℝ) < Real.log (X : ℝ) ∧
    Real.log (Real.log (k : ℝ)) < Real.log (Real.log (Real.log (X : ℝ))) := by
  have hk_real : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨hx_gt_e, _⟩ := exp_one_lt_log_of_sixteen_le hk
  set x : ℝ := Real.log (k : ℝ)
  have hx_pos : 0 < x := (Real.exp_pos 1).trans hx_gt_e
  have hB_pos : 0 < B := by rw [hB]; positivity
  have hB_pos_r : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB_pos
  have hlogB : Real.log (B : ℝ) = 18 * (k : ℝ) * x := by
    have hBcast : (B : ℝ) = (k : ℝ) ^ (18 * k) := by rw [hB]; push_cast; rfl
    rw [hBcast, Real.log_pow]
    push_cast
    ring
  have hk_lt : (k : ℝ) < Real.log (X : ℝ) := by
    have h1 : Real.log (B : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hB_pos_r (by exact_mod_cast hBX)
    have h2 : (1 : ℝ) < x := by linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    nlinarith only [hk_real, h1, h2, hlogB]
  exact ⟨hlogB, hk_lt, Real.log_lt_log hx_pos (Real.log_lt_log (by linarith) hk_lt)⟩

/-- General optimal-makespan and expected-makespan transfer across an idle-machine padding
embedding `(eJ, embedM)` from `(G₀, p₀)` into `(G, p)`. -/
private theorem optMakespan_le_and_expectedMakespan_ge_of_idlePad
    {ι₀ M₀ ι₁ M₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype M₀] [DecidableEq M₀]
    [Nonempty M₀] [Fintype ι₁] [DecidableEq ι₁] [Fintype M₁] [DecidableEq M₁] [Nonempty M₁]
    (G₀ : LoadBalancingGame ι₀ M₀) (p₀ : ι₀ → M₀ → ℝ)
    (G : LoadBalancingGame ι₁ M₁) (p : ι₁ → M₁ → ℝ)
    (eJ : ι₁ ≃ ι₀) {embedM : M₀ → M₁} (hembedM : Function.Injective embedM)
    (hp_nn : ∀ i j, 0 ≤ p i j) (hp_eq : ∀ i x, p i (embedM x) = p₀ (eJ i) x)
    (hload_eq : ∀ (A₀ : ι₀ → M₀) (x : M₀),
      G₀.load A₀ x = G.load (fun i => embedM (A₀ (eJ i))) (embedM x))
    (hload_le : ∀ (A₀ : ι₀ → M₀) (j : M₁),
      G.load (fun i => embedM (A₀ (eJ i))) j ≤ G₀.makespan A₀) :
    G.optMakespan ≤ G₀.optMakespan ∧ G₀.expectedMakespan p₀ ≤ G.expectedMakespan p := by
  refine ⟨?_, ?_⟩
  · obtain ⟨A₀, hA₀⟩ := G₀.exists_makespan_eq_optMakespan
    exact (G.optMakespan_le (fun i => embedM (A₀ (eJ i)))).trans
      ((G.makespan_le_iff _).mpr fun j => (hload_le A₀ j).trans_eq hA₀)
  · let liftA : (ι₀ → M₀) → (ι₁ → M₁) := fun A₀ i => embedM (A₀ (eJ i))
    have hliftA_inj : Function.Injective liftA := by
      intro A₁ A₂ h
      funext x
      exact hembedM (by simpa only [liftA, eJ.apply_symm_apply] using congrFun h (eJ.symm x))
    have hpw : ∀ A₀ : ι₀ → M₀, productWeight p (liftA A₀) = productWeight p₀ A₀ := fun A₀ => by
      rw [productWeight_def, productWeight_def]
      simp_rw [liftA, hp_eq]
      exact Fintype.prod_equiv eJ _ _ fun _ => rfl
    have hp₀_nn : ∀ x y, 0 ≤ p₀ x y := fun x y => by
      have := hp_nn (eJ.symm x) (embedM y)
      rwa [hp_eq, eJ.apply_symm_apply] at this
    have hms_le : ∀ A₀ : ι₀ → M₀, G₀.makespan A₀ ≤ G.makespan (liftA A₀) := fun A₀ => by
      obtain ⟨x, hx⟩ := G₀.exists_load_eq_makespan A₀
      rw [← hx, hload_eq]
      exact G.load_le_makespan _ _
    calc G₀.expectedMakespan p₀
        = ∑ A₀ : ι₀ → M₀, productWeight p₀ A₀ * G₀.makespan A₀ := rfl
      _ ≤ ∑ A₀ : ι₀ → M₀, productWeight p (liftA A₀) * G.makespan (liftA A₀) := by
          refine sum_le_sum fun A₀ _ => ?_
          rw [hpw]
          exact mul_le_mul_of_nonneg_left (hms_le A₀) (productWeight_nonneg hp₀_nn A₀)
      _ ≤ G.expectedMakespan p := by
          rw [expectedMakespan, ← sum_image (f := fun A => productWeight p A * G.makespan A)
            (fun _ _ _ _ h => hliftA_inj h)]
          exact sum_le_univ_sum_of_nonneg fun A =>
            mul_nonneg (productWeight_nonneg hp_nn A) (G.makespan_nonneg A)

/-- Equilibrium cost of any job `x` on any active machine `y` (`0 < relatedMixedLowerNE k B x y`)
is at most `k`, while `1 ≤ weight x`. Used to rule out deviations to padded speed-`1/k` machines. -/
private theorem equilibrium_cost_relatedMixedLowerNE_le_k {k B : ℕ} [NeZero B] (hk : 1 ≤ k)
    {x : RelatedMixedLowerJob k B} {y : RelatedMixedLowerMachine k B}
    (hpos : 0 < relatedMixedLowerNE k B x y) :
    (relatedMixedLower k B).expectedLoad (relatedMixedLowerNE k B) y +
      (1 - relatedMixedLowerNE k B x y) *
        ((relatedMixedLower k B).weight x / (relatedMixedLower k B).speed y) ≤ (k : ℝ) ∧
    1 ≤ (relatedMixedLower k B).weight x := by
  rw [expectedLoad_relatedMixedLowerNE hk y]
  cases x with
  | inl t =>
    have hxeq : y = relatedMixedDetTarget k B t := by
      by_contra hne
      rw [relatedMixedLowerNE_inl, ite_eq_right hne] at hpos
      exact lt_irrefl 0 hpos
    have hnotlast : y.tier ≠ Fin.last k := by
      rw [hxeq]
      intro h
      have hv := congrArg Fin.val h
      simp only [relatedMixedDetTarget, Fin.val_last] at hv
      omega
    rw [ite_eq_right hnotlast, relatedMixedLowerNE_inl, hxeq, ite_eq_left rfl, sub_self, zero_mul,
      add_zero]
    simp only [relatedMixedLower, relatedMixedDetTarget]
    have hlt_k : (t.tier.val : ℝ) + 1 ≤ (k : ℝ) := by
      have := t.tier.isLt
      exact_mod_cast (by omega : t.tier.val + 1 ≤ k)
    refine ⟨?_, one_le_pow₀ (by norm_num)⟩
    push_cast
    linarith
  | inr r =>
    have hlast : y.tier = Fin.last k := by
      by_contra hne
      simp only [relatedMixedLowerNE, ite_eq_right hne] at hpos
      exact lt_irrefl 0 hpos
    rw [ite_eq_left hlast]
    simp only [relatedMixedLowerNE, hlast, ↓reduceIte, relatedMixedLower, Fin.val_last,
      two_pow_sub_one_div_two_pow hk]
    have hinv_nn : 0 ≤ 1 / (B : ℝ) := by positivity
    exact ⟨by linarith, one_le_pow₀ (by norm_num)⟩

/-- **Asymptotic uniformly related mixed PoA lower bound along the `(k, k ^ (18 * k))` family**:
for every `k ≥ 16` and `B = k ^ (18 * k)`, `relatedMixedLowerNE k B` achieves expected makespan at
least `(1 / 60) * (log |M| / log (log (log |M|))) * optMakespan`. -/
theorem expectedMakespan_relatedMixedLowerNE_ge_log_div_log_log_log {k B : ℕ} [NeZero B]
    (hk : 16 ≤ k) (hB : B = k ^ (18 * k)) :
    (1 / 60 : ℝ) *
      (Real.log (Fintype.card (RelatedMixedLowerMachine k B)) /
        Real.log (Real.log (Real.log (Fintype.card (RelatedMixedLowerMachine k B))))) *
      (relatedMixedLower k B).optMakespan ≤
        (relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) := by
  obtain ⟨hB2, hd_ge_2a, h2d_le_aB, hcond, hd_ge_3⟩ := ballsIntoBins_params_of_ge_sixteen hk
  rw [← hB] at hB2 h2d_le_aB hcond
  set d : ℕ := ⌊4 * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))⌋₊
  set M : ℕ := Fintype.card (RelatedMixedLowerMachine k B)
  have hk_real : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  obtain ⟨hx_gt_e, hy_gt1⟩ := exp_one_lt_log_of_sixteen_le hk
  set x : ℝ := Real.log (k : ℝ)
  have hx_pos : 0 < x := (Real.exp_pos 1).trans hx_gt_e
  set y : ℝ := Real.log x
  have hM_card : M = Fintype.card (relatedPureLowerMachine k) * B :=
    card_relatedMixedLowerMachine k B
  have hM_ge_B : B ≤ M := by
    rw [hM_card]
    exact Nat.le_mul_of_pos_left B Fintype.card_pos
  have hB_pos_r : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM_pos_r : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨hlogB_eq, _, hy_lt_log3M⟩ := log_log_lt_log_log_log_of_pow_le hk hB hM_ge_B
  have hlog3M_pos : 0 < Real.log (Real.log (Real.log (M : ℝ))) := by linarith
  -- Upper bound `log M ≤ 21 * k * log k`.
  have hM_le_nat : M ≤ 2 ^ (k + 1) * k ^ k * B := by
    rw [hM_card]
    have h1 := (card_relatedPureLowerMachine_le k).trans
      (Nat.mul_le_mul_left _ (Nat.factorial_le_pow k))
    exact Nat.mul_le_mul_right B h1
  have hlogM_le : Real.log (M : ℝ) ≤ 21 * (k : ℝ) * x := by
    have hM_le_r : (M : ℝ) ≤ (2 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (B : ℝ) := by
      exact_mod_cast hM_le_nat
    calc Real.log (M : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (B : ℝ)) := Real.log_le_log hM_pos_r hM_le_r
      _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 + (k : ℝ) * x + 18 * (k : ℝ) * x := by
          rw [Real.log_mul (by positivity) hB_pos_r.ne',
            Real.log_mul (by positivity) (by positivity),
            Real.log_pow, Real.log_pow, hlogB_eq]
      _ ≤ 2 * (k : ℝ) * x + (k : ℝ) * x + 18 * (k : ℝ) * x := by
          push_cast
          have hlog2_le : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (by linarith)
          have h1 : ((k : ℝ) + 1) * Real.log 2 ≤ 2 * (k : ℝ) * x := by
            calc ((k : ℝ) + 1) * Real.log 2
                ≤ ((k : ℝ) + 1) * x := mul_le_mul_of_nonneg_left hlog2_le (by linarith)
              _ ≤ 2 * (k : ℝ) * x := by nlinarith only [hk_real, hx_pos]
          linarith
      _ = 21 * (k : ℝ) * x := by ring
  have hratio_le :
      (1 / 60 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ)))) ≤ (d : ℝ) / 4 := by
    have hdiv1 : Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ))) ≤
        21 * (k : ℝ) * x / y := by
      calc Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ)))
          ≤ (21 * (k : ℝ) * x) / Real.log (Real.log (Real.log (M : ℝ))) :=
            div_le_div_of_nonneg_right hlogM_le hlog3M_pos.le
        _ ≤ (21 * (k : ℝ) * x) / y :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hy_lt_log3M.le
    have h1 : (1 / 60 : ℝ) * (21 * (k : ℝ) * x / y) = (21 / 60 : ℝ) * ((k : ℝ) * x / y) := by ring
    have h2 : (3 * (k : ℝ) * x / y) / 4 = (3 / 4 : ℝ) * ((k : ℝ) * x / y) := by ring
    have hnn : 0 ≤ (k : ℝ) * x / y := by positivity
    linarith only [hdiv1, hd_ge_3, h1, h2, hnn]
  have hquarter := expectedMakespan_relatedMixedLowerNE_ge_quarter_of_ballsIntoBins
    (k := k) (B := B) (d := d) (by omega) hB2 hd_ge_2a h2d_le_aB hcond
  have hratio_nn :
      0 ≤ (1 / 60 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ)))) := by
    have hlogM_nn : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
    positivity
  calc (1 / 60 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ)))) *
          (relatedMixedLower k B).optMakespan
      ≤ (1 / 60 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ)))) * 1 :=
        mul_le_mul_of_nonneg_left (optMakespan_relatedMixedLower_le_one k B) hratio_nn
    _ ≤ (d : ℝ) / 4 := by linarith
    _ ≤ (relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) := hquarter

/-- Opaque helper for the replication factor `k ^ (18 * k)` to keep kernel reduction from
evaluating large powers of concrete constants such as `16 ^ 288`. -/
private def relatedMixedRep (k : ℕ) : ℕ := k ^ (18 * k)

private theorem relatedMixedRep_eq (k : ℕ) : relatedMixedRep k = k ^ (18 * k) := rfl

private theorem le_card_relatedMixedLowerMachine_rep {k : ℕ} (hk : 1 ≤ k) :
    k ≤ Fintype.card (RelatedMixedLowerMachine k (relatedMixedRep k)) := by
  have h1 : relatedMixedRep k ≤ Fintype.card (RelatedMixedLowerMachine k (relatedMixedRep k)) := by
    rw [card_relatedMixedLowerMachine]
    exact Nat.le_mul_of_pos_left _ Fintype.card_pos
  have h2 : k ≤ relatedMixedRep k := by
    rw [relatedMixedRep_eq]
    exact Nat.le_self_pow (by omega) k
  exact h2.trans h1

/-- **Uniformly related mixed price of anarchy lower bound for all `m ≥ 16`**
([CzumajVocking2002]; [Vocking2007], Theorem 20.18; locator not re-verified against primary PDF):
for every `m ≥ 16`, there exist `n ≤ m`, a uniformly related load-balancing game on `Fin n` jobs
and `Fin m` machines with `0 < optMakespan`, and a mixed Nash equilibrium `p` attaining
`expectedMakespan p ≥ (1 / 3200) * (log m / log (log (log m))) * optMakespan`. -/
theorem exists_relatedMixedNash_makespan_ge_log_div_log_log_log {m : ℕ} [NeZero m]
    (hm : 16 ≤ m) :
    ∃ (n : ℕ) (_ : n ≤ m) (G : LoadBalancingGame (Fin n) (Fin m)) (p : Fin n → Fin m → ℝ),
      G.toCostGame.IsMixedNash p ∧
      0 < G.optMakespan ∧
      (1 / 3200 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) *
          G.optMakespan ≤
        G.expectedMakespan p := by
  let Mfn : ℕ → ℕ := fun k => Fintype.card (RelatedMixedLowerMachine k (relatedMixedRep k))
  by_cases hlarge : Mfn 16 ≤ m
  · -- Large `m ≥ Mfn 16`: pick the largest `k ≥ 16` with `Mfn k ≤ m` and pad with idle machines.
    have hS_ne : ((range (m + 1)).filter fun k => 16 ≤ k ∧ Mfn k ≤ m).Nonempty := by
      refine ⟨16, mem_filter.mpr ⟨mem_range.mpr ?_, le_rfl, hlarge⟩⟩
      have h16_le : 16 ≤ Mfn 16 := le_card_relatedMixedLowerMachine_rep (by omega)
      exact Nat.lt_succ_of_le (h16_le.trans hlarge)
    obtain ⟨k, hk_mem, hk_max⟩ :=
      exists_max_image ((range (m + 1)).filter fun k => 16 ≤ k ∧ Mfn k ≤ m) id hS_ne
    obtain ⟨_, hk16, hMk_le⟩ := mem_filter.mp hk_mem
    have hm_lt_next : m < Mfn (k + 1) := by
      by_contra hle
      push Not at hle
      have hk1_lt : k + 1 < m + 1 :=
        Nat.lt_succ_of_le ((le_card_relatedMixedLowerMachine_rep (by omega)).trans hle)
      have hk1_mem : k + 1 ∈ (range (m + 1)).filter fun r => 16 ≤ r ∧ Mfn r ≤ m :=
        mem_filter.mpr ⟨mem_range.mpr hk1_lt, by omega, hle⟩
      have := hk_max (k + 1) hk1_mem
      dsimp only [id_eq] at this
      omega
    set B : ℕ := relatedMixedRep k
    have hB_eq : B = k ^ (18 * k) := relatedMixedRep_eq k
    have : NeZero B := ⟨by rw [hB_eq]; positivity⟩
    let n : ℕ := Fintype.card (RelatedMixedLowerJob k B)
    have hn_le : n ≤ m :=
      (card_relatedMixedLowerJob_le_card_machine k B).trans hMk_le
    let eJ : Fin n ≃ RelatedMixedLowerJob k B := (Fintype.equivFin (RelatedMixedLowerJob k B)).symm
    let eM : Fin (Mfn k) ≃ RelatedMixedLowerMachine k B :=
      (Fintype.equivFin (RelatedMixedLowerMachine k B)).symm
    have hk_pos_r : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    let G : LoadBalancingGame (Fin n) (Fin m) :=
      { weight := fun i => (relatedMixedLower k B).weight (eJ i)
        speed := fun j =>
          if h : j.val < Mfn k then (relatedMixedLower k B).speed (eM ⟨j.val, h⟩) else 1 / (k : ℝ)
        weight_nonneg := fun i => (relatedMixedLower k B).weight_nonneg (eJ i)
        speed_pos := fun j => by
          split_ifs with h
          · exact (relatedMixedLower k B).speed_pos _
          · positivity }
    let p : Fin n → Fin m → ℝ := fun i j =>
      if h : j.val < Mfn k then relatedMixedLowerNE k B (eJ i) (eM ⟨j.val, h⟩) else 0
    let embedM : RelatedMixedLowerMachine k B → Fin m := fun x =>
      ⟨(eM.symm x).val, lt_of_lt_of_le (eM.symm x).isLt hMk_le⟩
    have hembedM_inj : Function.Injective embedM := by
      intro x₁ x₂ h
      have hv : (eM.symm x₁).val = (eM.symm x₂).val := by
        simpa only [embedM] using congrArg Fin.val h
      exact eM.symm.injective (Fin.ext hv)
    -- Expected load of `G` under `p` matches `relatedMixedLower k B` on the first `Mfn k` machines.
    have hE_eq : ∀ j : Fin m,
        G.expectedLoad p j =
          if h : j.val < Mfn k then
            (relatedMixedLower k B).expectedLoad (relatedMixedLowerNE k B) (eM ⟨j.val, h⟩)
          else 0 := by
      intro j
      rw [expectedLoad]
      by_cases h : j.val < Mfn k
      · rw [dite_eq_left h]
        simp only [G, p, dite_eq_left h]
        rw [expectedLoad]
        exact Fintype.sum_equiv eJ _ _ fun _ => rfl
      · rw [dite_eq_right h]
        refine sum_eq_zero fun i _ => ?_
        simp only [p, dite_eq_right h, zero_mul]
    have hbase_NE := isMixedNash_relatedMixedLowerNE (k := k) (B := B) (by omega)
    have hp_isNE : G.toCostGame.IsMixedNash p := by
      rw [G.isMixedNash_iff]
      refine ⟨fun i => ?_, fun i j hpos j' => ?_⟩
      · rw [isMixedStrategy_iff]
        refine ⟨fun j => ?_, ?_⟩
        · simp only [p]
          split_ifs with h
          · exact (hbase_NE.1 (eJ i)).nonneg _
          · exact le_rfl
        · have hfilt :
              ∑ j : Fin m, p i j =
                ∑ j ∈ univ.filter (fun j : Fin m => j.val < Mfn k), p i j := by
            rw [sum_filter]
            refine sum_congr rfl fun j _ => ?_
            simp only [p]
            split_ifs <;> rfl
          rw [hfilt]
          have hbij :
              ∑ j ∈ univ.filter (fun j : Fin m => j.val < Mfn k), p i j =
                ∑ x : RelatedMixedLowerMachine k B, relatedMixedLowerNE k B (eJ i) x := by
            refine Finset.sum_nbij (fun j => if h : j.val < Mfn k then eM ⟨j.val, h⟩ else
                relatedMixedTopMachine k B 0) ?_ ?_ ?_ ?_
            · intro _ _; exact mem_univ _
            · intro j₁ hj₁ j₂ hj₂ hEq
              have h1 : j₁.val < Mfn k := (mem_filter.mp hj₁).2
              have h2 : j₂.val < Mfn k := (mem_filter.mp hj₂).2
              dsimp only at hEq
              rw [dite_eq_left h1, dite_eq_left h2] at hEq
              have hfin := eM.injective hEq
              exact Fin.ext (by simpa only using congrArg Fin.val hfin)
            · intro x _
              refine ⟨embedM x, mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, (eM.symm x).isLt⟩), ?_⟩
              have hlt : (embedM x).val < Mfn k := (eM.symm x).isLt
              dsimp only
              rw [dite_eq_left hlt]
              have hfin : (⟨(embedM x).val, hlt⟩ : Fin (Mfn k)) = eM.symm x := Fin.ext rfl
              rw [hfin, eM.apply_symm_apply]
            · intro j hj
              have h1 : j.val < Mfn k := (mem_filter.mp hj).2
              simp only [p, dite_eq_left h1]
          rw [hbij]
          exact (hbase_NE.1 (eJ i)).sum_eq_one
      · have hj_lt : j.val < Mfn k := by
          by_contra h
          simp only [p, dite_eq_right h] at hpos
          exact lt_irrefl 0 hpos
        rw [hE_eq j, hE_eq j', dite_eq_left hj_lt]
        simp only [G, p, dite_eq_left hj_lt] at hpos ⊢
        by_cases hj'_lt : j'.val < Mfn k
        · rw [dite_eq_left hj'_lt]
          simp only [dite_eq_left hj'_lt]
          exact (((relatedMixedLower k B).isMixedNash_iff _).mp hbase_NE).2
            (eJ i) (eM ⟨j.val, hj_lt⟩) hpos (eM ⟨j'.val, hj'_lt⟩)
        · rw [dite_eq_right hj'_lt, zero_add]
          simp only [dite_eq_right hj'_lt, sub_zero, one_mul, one_div, div_inv_eq_mul]
          -- On any active machine, job `eJ i`'s equilibrium cost is at most `k`, while an idle
          -- machine of speed `1 / k` charges `weight (eJ i) * k ≥ k`.
          obtain ⟨hcost_le, hw_ge1⟩ := equilibrium_cost_relatedMixedLowerNE_le_k (by omega) hpos
          nlinarith only [hcost_le, hw_ge1, hk_pos_r]
    -- Helper computing `G.load (fun i => embedM (A (eJ i))) j`.
    have hload_embed : ∀ (A : RelatedMixedLowerJob k B → RelatedMixedLowerMachine k B) (j : Fin m),
        G.load (fun i => embedM (A (eJ i))) j =
          if h : j.val < Mfn k then (relatedMixedLower k B).load A (eM ⟨j.val, h⟩) else 0 := by
      intro A j
      rw [LoadBalancingGame.load_eq_sum_div]
      by_cases h : j.val < Mfn k
      · rw [dite_eq_left h]
        simp only [G, dite_eq_left h]
        rw [LoadBalancingGame.load_eq_sum_div]
        congr 1
        refine Finset.sum_nbij (fun i => eJ i) ?_ ?_ ?_ ?_
        · intro i hi
          simp only [mem_filter, mem_univ, true_and] at hi ⊢
          have hv : (eM.symm (A (eJ i))).val = j.val := congrArg Fin.val hi
          exact (eM.symm_apply_eq).mp (Fin.ext hv)
        · intro i₁ _ i₂ _ hEq; exact eJ.injective hEq
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx
          refine ⟨eJ.symm x, ?_, eJ.apply_symm_apply x⟩
          simp only [mem_coe, mem_filter, mem_univ, true_and, eJ.apply_symm_apply, hx]
          exact Fin.ext (by simp only [embedM, Equiv.symm_apply_apply])
        · intro _ _; rfl
      · rw [dite_eq_right h]
        have hempty : (univ.filter fun i : Fin n => embedM (A (eJ i)) = j) = ∅ := by
          ext i
          simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          intro hi
          have hv : (eM.symm (A (eJ i))).val = j.val := congrArg Fin.val hi
          exact h (hv ▸ (eM.symm (A (eJ i))).isLt)
        rw [hempty, sum_empty, zero_div]
    -- Transfer `optMakespan ≤ 1` and `d / 4 ≤ expectedMakespan` via idle padding.
    have hpad := optMakespan_le_and_expectedMakespan_ge_of_idlePad
      (relatedMixedLower k B) (relatedMixedLowerNE k B) G p eJ hembedM_inj
      (fun i j => (hp_isNE.1 i).nonneg j)
      (fun i x => by
        have hlt : (embedM x).val < Mfn k := (eM.symm x).isLt
        simp only [p, dite_eq_left hlt]
        have hfin : (⟨(embedM x).val, hlt⟩ : Fin (Mfn k)) = eM.symm x := Fin.ext rfl
        rw [hfin, eM.apply_symm_apply])
      (fun A₀ x => by
        have hlt : (embedM x).val < Mfn k := (eM.symm x).isLt
        rw [hload_embed A₀ (embedM x), dite_eq_left hlt]
        have hfin : (⟨(embedM x).val, hlt⟩ : Fin (Mfn k)) = eM.symm x := Fin.ext rfl
        rw [hfin, eM.apply_symm_apply])
      (fun A₀ j => by
        rw [hload_embed A₀ j]
        split_ifs with h
        · exact (relatedMixedLower k B).load_le_makespan A₀ _
        · exact (relatedMixedLower k B).makespan_nonneg A₀)
    have hopt_le1 : G.optMakespan ≤ 1 := hpad.1.trans (optMakespan_relatedMixedLower_le_one k B)
    have hopt_pos : 0 < G.optMakespan :=
      optMakespan_pos_of_exists_weight_pos G
        ⟨eJ.symm (Sum.inr ⟨0, Nat.mul_pos (by omega) (NeZero.pos B)⟩),
          by simp [G, relatedMixedLower]⟩
    obtain ⟨hB2, hd_ge_2a, h2d_le_aB, hcond, hd_ge_3⟩ := ballsIntoBins_params_of_ge_sixteen hk16
    rw [← hB_eq] at hB2 h2d_le_aB hcond
    set d : ℕ := ⌊4 * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))⌋₊
    have hEM_ge : (d : ℝ) / 4 ≤ G.expectedMakespan p :=
      (expectedMakespan_relatedMixedLowerNE_ge_quarter_of_ballsIntoBins
        (by omega) hB2 hd_ge_2a h2d_le_aB hcond).trans hpad.2
    -- Asymptotic bound: `(1 / 3200) * (log m / log (log (log m))) ≤ d / 4`.
    have hk_real : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk16
    obtain ⟨hx_gt_e, hy_gt1⟩ := exp_one_lt_log_of_sixteen_le hk16
    set x : ℝ := Real.log (k : ℝ)
    have hx_pos : 0 < x := (Real.exp_pos 1).trans hx_gt_e
    set y : ℝ := Real.log x
    have hB_le_m : B ≤ m := by
      have h1 : B ≤ Mfn k := by
        dsimp only [Mfn]
        rw [card_relatedMixedLowerMachine]
        exact Nat.le_mul_of_pos_left _ Fintype.card_pos
      exact h1.trans hMk_le
    have hm_pos_r : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
    obtain ⟨_, _, hy_lt_log3m⟩ := log_log_lt_log_log_log_of_pow_le hk16 hB_eq hB_le_m
    have hlog3m_pos : 0 < Real.log (Real.log (Real.log (m : ℝ))) := by linarith
    -- Upper bound `log m ≤ log (Mfn (k + 1)) ≤ 80 * k * log k`.
    have hm_le_nat : m ≤ 2 ^ (k + 2) * (k + 1) ^ (k + 1) * (k + 1) ^ (18 * (k + 1)) := by
      have h1 : Mfn (k + 1) ≤ 2 ^ (k + 2) * (k + 1) ^ (k + 1) * (k + 1) ^ (18 * (k + 1)) := by
        dsimp only [Mfn]
        rw [card_relatedMixedLowerMachine, relatedMixedRep_eq]
        exact Nat.mul_le_mul_right _ ((card_relatedPureLowerMachine_le (k + 1)).trans
          (Nat.mul_le_mul_left _ (Nat.factorial_le_pow (k + 1))))
      exact hm_lt_next.le.trans h1
    have hlogm_le : Real.log (m : ℝ) ≤ 80 * (k : ℝ) * x := by
      have hm_le_r : (m : ℝ) ≤ (2 : ℝ) ^ (k + 2) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) *
          ((k + 1 : ℕ) : ℝ) ^ (18 * (k + 1)) := by exact_mod_cast hm_le_nat
      have hlog_k1 : Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 * x := by
        have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
          push_cast
          nlinarith only [hk_real]
        calc Real.log ((k + 1 : ℕ) : ℝ)
            ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by positivity) hk1_le
          _ = 2 * x := by rw [Real.log_pow]; simp only [x]; norm_num
      have hlog2_le : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (by linarith)
      calc Real.log (m : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (k + 2) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) *
              ((k + 1 : ℕ) : ℝ) ^ (18 * (k + 1))) := Real.log_le_log hm_pos_r hm_le_r
        _ = ((k + 2 : ℕ) : ℝ) * Real.log 2 + ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) +
              ((18 * (k + 1) : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity),
              Real.log_pow, Real.log_pow, Real.log_pow]
        _ ≤ 2 * (k : ℝ) * x + 19 * ((k + 1 : ℕ) : ℝ) * (2 * x) := by
            have h1 : ((k + 2 : ℕ) : ℝ) * Real.log 2 ≤ 2 * (k : ℝ) * x := by
              have hle2k : ((k + 2 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by push_cast; linarith
              calc ((k + 2 : ℕ) : ℝ) * Real.log 2
                  ≤ ((k + 2 : ℕ) : ℝ) * x := mul_le_mul_of_nonneg_left hlog2_le (by positivity)
                _ ≤ 2 * (k : ℝ) * x := mul_le_mul_of_nonneg_right hle2k hx_pos.le
            have h2 : ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) +
                ((18 * (k + 1) : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) =
                19 * ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) := by push_cast; ring
            rw [add_assoc, h2]
            have h3 := mul_le_mul_of_nonneg_left hlog_k1
              (by positivity : 0 ≤ 19 * ((k + 1 : ℕ) : ℝ))
            linarith only [h1, h3]
        _ ≤ 80 * (k : ℝ) * x := by
            have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by push_cast; linarith
            nlinarith only [hk1_le, hk_real, hx_pos]
    have hdiv_le : Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ))) ≤
        80 * (k : ℝ) * x / y := by
      calc Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))
          ≤ (80 * (k : ℝ) * x) / Real.log (Real.log (Real.log (m : ℝ))) :=
            div_le_div_of_nonneg_right hlogm_le hlog3m_pos.le
        _ ≤ (80 * (k : ℝ) * x) / y :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hy_lt_log3m.le
    have hbound :
        (1 / 3200 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) *
            G.optMakespan ≤
          G.expectedMakespan p := by
      have hratio_nn : 0 ≤ (1 / 3200 : ℝ) *
          (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) := by
        have hlogm_nn : 0 ≤ Real.log (m : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
        positivity
      have hstep : (1 / 3200 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) ≤
          (d : ℝ) / 4 := by
        have h1 : (1 / 3200 : ℝ) * (80 * (k : ℝ) * x / y) = (1 / 40 : ℝ) * ((k : ℝ) * x / y) := by
          ring
        have h2 : (3 * (k : ℝ) * x / y) / 4 = (3 / 4 : ℝ) * ((k : ℝ) * x / y) := by ring
        have hnn : 0 ≤ (k : ℝ) * x / y := by positivity
        linarith only [hdiv_le, hd_ge_3, h1, h2, hnn]
      calc (1 / 3200 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) *
              G.optMakespan
          ≤ (1 / 3200 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) * 1 :=
            mul_le_mul_of_nonneg_left hopt_le1 hratio_nn
        _ ≤ (d : ℝ) / 4 := by linarith
        _ ≤ G.expectedMakespan p := hEM_ge
    exact ⟨n, hn_le, G, p, hp_isNE, hopt_pos, hbound⟩
  · -- Small `16 ≤ m < Mfn 16`: `unitIdenticalGame m` has `OPT = 1 ≤ expectedMakespan` and
    -- `log m / log (log (log m)) ≤ 3200`.
    push Not at hlarge
    refine ⟨m, le_rfl, unitIdenticalGame m, uniformMixedProfile m,
      isMixedNash_uniformMixedProfile m,
      by rw [optMakespan_unitIdenticalGame]; exact zero_lt_one, ?_⟩
    rw [optMakespan_unitIdenticalGame, mul_one]
    have h1_le_EM := one_le_expectedMakespan_unitIdenticalGame m
    suffices hsmall : Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ))) ≤ 3200 by linarith
    have hm_pos_r : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (NeZero.pos m)
    by_cases hm1024 : m ≤ 1024
    · -- `16 ≤ m ≤ 1024`: `log m < 10` and `log (log (log m)) ≥ 0.018`, so ratio `< 600 ≤ 3200`.
      have hlogm_lt : Real.log (m : ℝ) < 10 := by
        have hm_le : (m : ℝ) ≤ 1024 := by exact_mod_cast hm1024
        have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
          rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num, Real.log_pow]
          norm_num
        have h1 : Real.log (m : ℝ) ≤ Real.log (1024 : ℝ) := Real.log_le_log hm_pos_r hm_le
        linarith [Real.log_two_lt_d9]
      have hlogm_ge : (2.7725 : ℝ) ≤ Real.log (m : ℝ) := by
        have hm_ge : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
          norm_num
        have h1 : Real.log (16 : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm_ge
        linarith [Real.log_two_gt_d9]
      have hlog2m_ge : (1.019 : ℝ) ≤ Real.log (Real.log (m : ℝ)) := by
        have hdiv_ge : (1.0195 : ℝ) ≤ Real.log (m : ℝ) / Real.exp 1 := by
          rw [le_div_iff₀ (Real.exp_pos 1)]
          linarith [Real.exp_one_lt_d9]
        have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1.0195 : ℝ)⁻¹ by norm_num)
        rw [Real.log_inv] at hinv
        have hlog_div : Real.log (Real.log (m : ℝ) / Real.exp 1) =
            Real.log (Real.log (m : ℝ)) - 1 := by
          rw [Real.log_div (by linarith) (Real.exp_pos 1).ne', Real.log_exp]
        have hmono : Real.log (1.0195 : ℝ) ≤ Real.log (Real.log (m : ℝ) / Real.exp 1) :=
          Real.log_le_log (by norm_num) hdiv_ge
        have hnum : (1.0195 : ℝ)⁻¹ < 0.981 := by norm_num
        linarith
      have hlog3m_ge : (0.018 : ℝ) ≤ Real.log (Real.log (Real.log (m : ℝ))) := by
        have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1.019 : ℝ)⁻¹ by norm_num)
        rw [Real.log_inv] at hinv
        have hmono : Real.log (1.019 : ℝ) ≤ Real.log (Real.log (Real.log (m : ℝ))) :=
          Real.log_le_log (by norm_num) hlog2m_ge
        have hnum : (1.019 : ℝ)⁻¹ < 0.982 := by norm_num
        linarith
      rw [div_le_iff₀ (by linarith)]
      linarith
    · -- `1024 < m < Mfn 16`: `log m ≤ 1233` and `log (log (log m)) ≥ 0.4`, so ratio `< 3200`.
      push Not at hm1024
      have hm_le_nat : m ≤ 2 ^ 17 * 16 ^ 16 * 16 ^ (18 * 16) := by
        have h1 : Mfn 16 ≤ 2 ^ 17 * 16 ^ 16 * 16 ^ (18 * 16) := by
          dsimp only [Mfn]
          rw [card_relatedMixedLowerMachine, relatedMixedRep_eq]
          exact Nat.mul_le_mul_right _ ((card_relatedPureLowerMachine_le 16).trans
            (Nat.mul_le_mul_left _ (Nat.factorial_le_pow 16)))
        exact hlarge.le.trans h1
      have hlogm_le : Real.log (m : ℝ) ≤ 1233 := by
        have hrew : 2 ^ 17 * 16 ^ 16 * 16 ^ (18 * 16) = 2 ^ 1233 := by
          rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
          congr 1
        have hm_le_pow : m ≤ 2 ^ 1233 := hm_le_nat.trans hrew.le
        have hm_le_r : (m : ℝ) ≤ (2 : ℝ) ^ (1233 : ℕ) := by exact_mod_cast hm_le_pow
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
          linarith
        calc Real.log (m : ℝ)
            ≤ Real.log ((2 : ℝ) ^ (1233 : ℕ)) := Real.log_le_log hm_pos_r hm_le_r
          _ = 1233 * Real.log 2 := by rw [Real.log_pow]; norm_num
          _ ≤ 1233 := by linarith
      have hlogm_ge : (6.93 : ℝ) ≤ Real.log (m : ℝ) := by
        have hm_ge : (1024 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1024.le
        have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
          rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num, Real.log_pow]
          norm_num
        have h1 : Real.log (1024 : ℝ) ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm_ge
        linarith [Real.log_two_gt_d9]
      have hlog2m_ge : (1.69 : ℝ) ≤ Real.log (Real.log (m : ℝ)) := by
        have h2e : 2 * Real.exp 1 ≤ Real.log (m : ℝ) := by linarith [Real.exp_one_lt_d9]
        have h1 : Real.log (2 * Real.exp 1) ≤ Real.log (Real.log (m : ℝ)) :=
          Real.log_le_log (by positivity) h2e
        rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h1
        linarith [Real.log_two_gt_d9]
      have hlog3m_ge : (0.4 : ℝ) ≤ Real.log (Real.log (Real.log (m : ℝ))) := by
        have hinv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1.69 : ℝ)⁻¹ by norm_num)
        rw [Real.log_inv] at hinv
        have hmono : Real.log (1.69 : ℝ) ≤ Real.log (Real.log (Real.log (m : ℝ))) :=
          Real.log_le_log (by norm_num) hlog2m_ge
        have hnum : (1.69 : ℝ)⁻¹ < 0.6 := by norm_num
        linarith
      rw [div_le_iff₀ (by linarith)]
      linarith

end Cslib.GameTheory.LoadBalancingGame

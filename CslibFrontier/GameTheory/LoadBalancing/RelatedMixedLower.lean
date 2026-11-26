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
  rwa [Nat.sub_add_cancel hk, relatedPureLowerTierCount_last, one_mul] at h

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
  cases m₁
  cases m₂
  cases ht
  exact congrArg₂ _ (Fin.ext hs) hc

private theorem relatedMixedLowerOpt_injective (k B : ℕ) :
    Function.Injective (relatedMixedLowerOpt k B) := by
  rintro (⟨t₁, s₁, idx₁, b₁⟩ | r₁) (⟨t₂, s₂, idx₂, b₂⟩ | r₂) h
  · obtain rfl : b₁ = b₂ := congrArg RelatedMixedLowerMachine.copy h
    obtain rfl : t₁ = t₂ := Fin.ext (by
      simpa only [relatedMixedLowerOpt] using congrArg (fun m => m.tier.val) h)
    have hp := finProdFinEquiv.injective (Fin.ext (by
      simpa only [relatedMixedLowerOpt, Fin.val_cast] using congrArg (fun m => m.slot.val) h))
    cases hp
    rfl
  · exact (t₁.isLt.ne (congrArg (fun m => m.tier.val) h)).elim
  · exact (t₂.isLt.ne' (congrArg (fun m => m.tier.val) h)).elim
  · exact congrArg Sum.inr <| finProdFinEquiv.symm.injective <| Prod.ext
      (Fin.ext (by simpa only [relatedMixedLowerOpt] using congrArg (fun m => m.slot.val) h))
      (congrArg RelatedMixedLowerMachine.copy h)

/-- The number of jobs in `relatedMixedLower k B` never exceeds the number of machines. -/
theorem card_relatedMixedLowerJob_le_card_machine (k B : ℕ) :
    Fintype.card (RelatedMixedLowerJob k B) ≤ Fintype.card (RelatedMixedLowerMachine k B) :=
  Fintype.card_le_of_injective _ (relatedMixedLowerOpt_injective k B)

private theorem load_relatedMixedLowerOpt_le_one (k B : ℕ) (j : RelatedMixedLowerMachine k B) :
    (relatedMixedLower k B).load (relatedMixedLowerOpt k B) j ≤ 1 := by
  rw [LoadBalancingGame.load_eq_sum_div, div_le_one ((relatedMixedLower k B).speed_pos j),
    sum_filter]
  by_cases hS : ∃ i₀, relatedMixedLowerOpt k B i₀ = j
  · obtain ⟨i₀, rfl⟩ := hS
    rw [Finset.sum_eq_single i₀
      (fun i _ hne => ite_eq_right fun heq => hne (relatedMixedLowerOpt_injective k B heq))
      (fun h => (h (mem_univ _)).elim), ite_eq_left rfl]
    cases i₀ <;> rfl
  · rw [Finset.sum_eq_zero fun i _ => ite_eq_right fun heq => hS ⟨i, heq⟩]
    exact ((relatedMixedLower k B).speed_pos j).le

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
  exact pos_of_mul_pos_right
    ((sum_pos' (fun i _ => G.weight_nonneg i) ⟨i₀, mem_univ i₀, hi₀⟩).trans_le
      G.sum_weight_le_sum_speed_mul_optMakespan)
    (sum_pos (fun j _ => G.speed_pos j) univ_nonempty).le

private theorem two_pow_sub_one_div_two_pow {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ (k - 1) / (2 : ℝ) ^ k = 1 / 2 := by
  have hpow : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow, div_mul_eq_div_div, div_self (by positivity)]

private theorem add_two_pow_div_ge {a b : ℕ} (h : b ≤ a) :
    (a : ℝ) + 1 ≤ (b : ℝ) + (2 : ℝ) ^ a / (2 : ℝ) ^ b := by
  have h2 : ((a - b : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (a - b) := by
    exact_mod_cast (Nat.lt_two_pow_self : a - b + 1 ≤ 2 ^ (a - b))
  rw [← Nat.add_sub_cancel' h, pow_add, mul_div_cancel_left₀ _ (by positivity), Nat.cast_add]
  linarith

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
  have hdet_zero : (r = Fin.last k ∨ r.val = 0) →
      ∑ x : RelatedMixedLowerDetJob k B,
        relatedMixedLowerNE k B (Sum.inl x) ⟨r, u, b⟩ *
          ((relatedMixedLower k B).weight (Sum.inl x) /
            (relatedMixedLower k B).speed ⟨r, u, b⟩) = 0 := fun hr =>
    sum_eq_zero fun x _ => by
      have hne : (⟨r, u, b⟩ : RelatedMixedLowerMachine k B) ≠ relatedMixedDetTarget k B x := by
        intro h
        have hv := congrArg (fun m : RelatedMixedLowerMachine k B => m.tier.val) h
        simp only [relatedMixedDetTarget] at hv
        rcases hr with rfl | hr0
        · simp only [Fin.val_last] at hv; omega
        · omega
      rw [relatedMixedLowerNE_inl, ite_eq_right hne, zero_mul]
  by_cases hlast : r = Fin.last k
  · subst hlast
    -- No lower-tier job targets tier `k`.
    rw [ite_eq_left rfl, hdet_zero (.inl rfl), zero_add]
    simp only [relatedMixedLowerNE, ↓reduceIte, relatedMixedLower, Fin.val_last,
      two_pow_sub_one_div_two_pow hk, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * k), Nat.cast_ofNat, Nat.cast_one]
    field_simp [hB_pos.ne']
  · rw [ite_eq_right hlast]
    -- No top-tier job targets tier `r < k`.
    have hright : ∑ i : Fin ((2 * k - 1) * B),
        relatedMixedLowerNE k B (Sum.inr i) ⟨r, u, b⟩ *
          ((relatedMixedLower k B).weight (Sum.inr i) /
            (relatedMixedLower k B).speed ⟨r, u, b⟩) = 0 :=
      sum_eq_zero fun _ _ => by simp only [relatedMixedLowerNE, ite_eq_right hlast, zero_mul]
    rw [hright, add_zero]
    have hr_lt : r.val < k :=
      lt_of_le_of_ne (Nat.lt_succ_iff.mp r.isLt) fun h => hlast (Fin.ext (by simpa using h))
    by_cases hr0 : r.val = 0
    · rw [hdet_zero (.inr hr0), hr0, Nat.cast_zero]
    · set t : Fin (k - 1) := ⟨r.val - 1, by omega⟩
      have ht_succ : t.val + 1 = r.val := by simp only [t]; omega
      let u' : Fin (relatedPureLowerTierCount k (t.val + 1)) :=
        u.cast (congrArg (relatedPureLowerTierCount k) ht_succ.symm)
      let emb : Fin (2 * (t.val + 1)) → RelatedMixedLowerDetJob k B := fun v => ⟨t, u', v, b⟩
      have hfilt : (univ.filter fun x : RelatedMixedLowerDetJob k B =>
          (⟨r, u, b⟩ : RelatedMixedLowerMachine k B) = relatedMixedDetTarget k B x) =
          univ.image emb := by
        ext ⟨t₁, u₁, v₁, b₁⟩
        rw [Finset.mem_filter, Finset.mem_image]
        simp only [mem_univ, true_and, emb, relatedMixedDetTarget]
        constructor
        · intro h
          obtain rfl : b = b₁ := congrArg RelatedMixedLowerMachine.copy h
          have ht1_val : r.val = t₁.val + 1 := congrArg (fun m => m.tier.val) h
          obtain rfl : t₁ = t := Fin.ext (by omega)
          obtain rfl : u' = u₁ := Fin.ext (by
            simpa only [u', Fin.val_cast] using congrArg (fun m => m.slot.val) h)
          exact ⟨v₁, rfl⟩
        · rintro ⟨v, hv⟩
          cases hv
          exact RelatedMixedLowerMachine.ext_val (Fin.ext ht_succ.symm) (by simp [u']) rfl
      simp only [relatedMixedLowerNE_inl, ite_mul, one_mul, zero_mul, ← sum_filter, hfilt]
      rw [sum_image (fun _ _ _ _ h => by cases h; rfl)]
      simp only [emb, relatedMixedLower, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ht_succ, pow_succ]
      have hpow_ne : (2 : ℝ) ^ t.val ≠ 0 := by positivity
      push_cast; field_simp [hpow_ne]

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
      refine ⟨fun j => ?_, by simp only [relatedMixedLowerNE, sum_ite_eq', mem_univ, ↓reduceIte]⟩
      simp only [relatedMixedLowerNE]
      split_ifs <;> norm_num
    | inr r =>
      refine ⟨fun j => by simp only [relatedMixedLowerNE]; split_ifs <;> positivity, ?_⟩
      have hfilt :
          (univ.filter fun j : RelatedMixedLowerMachine k B => j.tier = Fin.last k) =
            univ.image (relatedMixedTopMachine k B) := by
        ext ⟨s, u, b⟩
        simp only [mem_filter, mem_univ, true_and, mem_image, relatedMixedTopMachine]
        refine ⟨fun hs => ?_, fun ⟨_, hb'⟩ => congrArg RelatedMixedLowerMachine.tier hb'.symm⟩
        subst hs
        have hu_lt : u.val < 1 := by
          simpa only [Fin.val_last, relatedPureLowerTierCount_last] using u.isLt
        exact ⟨b, RelatedMixedLowerMachine.ext_val rfl (show (0 : ℕ) = u.val by omega) rfl⟩
      simp only [relatedMixedLowerNE, ← sum_filter, hfilt]
      rw [sum_image (fun _ _ _ _ h => congrArg RelatedMixedLowerMachine.copy h)]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hB_pos.ne']
  · -- Verify no profitable deviation from `j` to `j'`.
    rw [expectedLoad_relatedMixedLowerNE hk j, expectedLoad_relatedMixedLowerNE hk j']
    cases i with
    | inl x =>
      obtain rfl : j = relatedMixedDetTarget k B x :=
        not_ne_iff.mp fun hne => by simp [relatedMixedLowerNE_inl, hne] at hpos
      have hnotlast : (relatedMixedDetTarget k B x).tier ≠ Fin.last k :=
        Fin.ne_of_val_ne (by simp [relatedMixedDetTarget]; omega)
      rw [ite_eq_right hnotlast, relatedMixedLowerNE_inl, ite_eq_left rfl, sub_self, zero_mul,
        add_zero, relatedMixedLowerNE_inl]
      by_cases hj'_eq : j' = relatedMixedDetTarget k B x
      · subst hj'_eq
        rw [ite_eq_right hnotlast, ite_eq_left rfl, sub_self, zero_mul, add_zero]
      · rw [ite_eq_right hj'_eq, sub_zero, one_mul]
        simp only [relatedMixedDetTarget]
        by_cases hj'_last : j'.tier = Fin.last k
        · rw [ite_eq_left hj'_last]
          have hlt : (x.tier.val : ℝ) + 1 ≤ (k : ℝ) - 1 := by
            simpa [Nat.cast_sub hk] using (Nat.cast_le (α := ℝ)).mpr x.tier.isLt
          have hnn : 0 ≤ (2 : ℝ) ^ x.tier.val / (2 : ℝ) ^ j'.tier.val := by positivity
          simp only [relatedMixedLower]
          push_cast; linarith
        · rw [ite_eq_right hj'_last]
          simp only [relatedMixedLower]
          by_cases hrt : x.tier.val + 1 ≤ j'.tier.val
          · have hrt' : ((x.tier.val + 1 : ℕ) : ℝ) ≤ (j'.tier.val : ℝ) := by exact_mod_cast hrt
            have hnn : 0 ≤ (2 : ℝ) ^ x.tier.val / (2 : ℝ) ^ j'.tier.val := by positivity
            linarith
          · have hge := add_two_pow_div_ge (a := x.tier.val) (b := j'.tier.val) (by omega)
            push_cast; linarith
    | inr r =>
      have hj_last : j.tier = Fin.last k :=
        not_ne_iff.mp fun hne => by simp [relatedMixedLowerNE, hne] at hpos
      rw [ite_eq_left hj_last]
      simp only [relatedMixedLowerNE, hj_last, ↓reduceIte, relatedMixedLower, Fin.val_last,
        two_pow_sub_one_div_two_pow hk]
      by_cases hj'_last : j'.tier = Fin.last k
      · rw [ite_eq_left hj'_last, ite_eq_left hj'_last, hj'_last, Fin.val_last,
          two_pow_sub_one_div_two_pow hk]
      · rw [ite_eq_right hj'_last, ite_eq_right hj'_last, sub_zero, one_mul]
        have hj'_lt : j'.tier.val < k :=
          lt_of_le_of_ne (Nat.lt_succ_iff.mp j'.tier.isLt) fun h =>
            hj'_last (Fin.ext (by simpa using h))
        have hge := add_two_pow_div_ge (a := k - 1) (b := j'.tier.val) (by omega)
        rw [Nat.cast_sub hk, Nat.cast_one] at hge
        linarith [one_div_nonneg.mpr hB_pos.le]

/-- Lift a top-tier assignment `f : Fin ((2 * k - 1) * B) → Fin B` to a full pure assignment of
`relatedMixedLower k B` by fixing all lower-tier jobs to their pure machines. -/
private def liftTopAssignment (k B : ℕ) (f : Fin ((2 * k - 1) * B) → Fin B) :
    RelatedMixedLowerJob k B → RelatedMixedLowerMachine k B
  | Sum.inl x => relatedMixedDetTarget k B x
  | Sum.inr r => relatedMixedTopMachine k B (f r)

private theorem liftTopAssignment_injective (k B : ℕ) :
    Function.Injective (liftTopAssignment k B) := fun _ _ h =>
  funext fun r => congrArg RelatedMixedLowerMachine.copy (congrFun h (Sum.inr r))

private theorem productWeight_liftTopAssignment (k B : ℕ) (f : Fin ((2 * k - 1) * B) → Fin B) :
    productWeight (relatedMixedLowerNE k B) (liftTopAssignment k B f) =
      (1 / (B : ℝ)) ^ ((2 * k - 1) * B) := by
  rw [productWeight_def, Fintype.prod_sum_type,
    prod_eq_one fun x _ => by rw [relatedMixedLowerNE_inl, liftTopAssignment, ite_eq_left rfl],
    one_mul]
  simp only [relatedMixedLowerNE, liftTopAssignment, relatedMixedTopMachine, ↓reduceIte,
    prod_const, card_univ, Fintype.card_fin]

private theorem load_liftTopAssignment_top {k B : ℕ} (hk : 1 ≤ k)
    (f : Fin ((2 * k - 1) * B) → Fin B) (b : Fin B) :
    (relatedMixedLower k B).load (liftTopAssignment k B f) (relatedMixedTopMachine k B b) =
      (#(univ.filter fun r : Fin ((2 * k - 1) * B) => f r = b) : ℝ) / 2 := by
  rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fintype.sum_sum_type,
    sum_eq_zero fun x _ => ite_eq_right fun h => by
      have hv : x.tier.val + 1 = k := congrArg (fun m => m.tier.val) h
      omega,
    zero_add]
  have hiff : ∀ r : Fin ((2 * k - 1) * B),
      (liftTopAssignment k B f (Sum.inr r) = relatedMixedTopMachine k B b) ↔ f r = b := fun r =>
    ⟨fun h => congrArg RelatedMixedLowerMachine.copy h, fun h => by simp [liftTopAssignment, h]⟩
  simp_rw [hiff]
  rw [← sum_filter]
  simp only [relatedMixedLower, relatedMixedTopMachine, Fin.val_last, sum_const, nsmul_eq_mul,
    mul_div_assoc, two_pow_sub_one_div_two_pow hk]
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
            (relatedMixedLower k B).makespan (liftTopAssignment k B f) := by
        refine sum_le_sum fun f _ => ?_
        rw [productWeight_liftTopAssignment]
        split_ifs with hex
        · obtain ⟨b, hb⟩ := hex
          have hms_ge :
              (d : ℝ) / 2 ≤ (relatedMixedLower k B).makespan (liftTopAssignment k B f) :=
            (div_le_div_of_nonneg_right (Nat.cast_le.mpr hb) zero_le_two).trans
              ((load_liftTopAssignment_top hk f b).symm.trans_le
                ((relatedMixedLower k B).load_le_makespan _ _))
          exact mul_comm ((d : ℝ) / 2) _ ▸ mul_le_mul_of_nonneg_left hms_ge (by positivity)
        · rw [mul_zero]
          exact mul_nonneg (by positivity) ((relatedMixedLower k B).makespan_nonneg _)
    _ ≤ (relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) := by
        rw [expectedMakespan, ← sum_image (f := fun A =>
            productWeight (relatedMixedLowerNE k B) A * (relatedMixedLower k B).makespan A)
          (fun _ _ _ _ h => liftTopAssignment_injective k B h)]
        exact sum_le_univ_sum_of_nonneg fun A =>
          mul_nonneg (productWeight_nonneg hp_nn A) ((relatedMixedLower k B).makespan_nonneg A)

/-- Shared threshold bound for `k ≥ 16`: `e < log k` and `1 < log (log k)`. -/
private theorem exp_one_lt_log_of_sixteen_le {k : ℕ} (hk : 16 ≤ k) :
    Real.exp 1 < Real.log (k : ℝ) ∧ 1 < Real.log (Real.log (k : ℝ)) := by
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hx : Real.exp 1 < Real.log (k : ℝ) :=
    (by linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9] : Real.exp 1 < Real.log (16 : ℝ)).trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hk))
  exact ⟨hx, Real.log_exp 1 ▸ Real.log_lt_log (Real.exp_pos 1) hx⟩

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
    linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  have hx_pos : 0 < x := by linarith
  set y : ℝ := Real.log x
  have hy_pos : 0 < y := by linarith
  have hy_le_x_div2 : y ≤ x / 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx_pos (Real.exp_pos 1))
    rw [Real.log_div hx_pos.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
    linarith [div_le_div_of_nonneg_left hx_pos.le (by norm_num : (0 : ℝ) < 2) he_gt2.le]
  have hxy_ge2 : 2 ≤ x / y := (le_div_iff₀ hy_pos).mpr (by linarith)
  have hd_le_real : (d : ℝ) ≤ 4 * (k : ℝ) * x / y := Nat.floor_le (by positivity)
  have hd_ge_3 : 3 * (k : ℝ) * x / y ≤ (d : ℝ) := by
    have hlt : 4 * (k : ℝ) * x / y < (d : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1 : 3 * (k : ℝ) * x / y + (k : ℝ) * (x / y) = 4 * (k : ℝ) * x / y := by ring
    nlinarith
  have hB2 : 2 ≤ B := (by omega : 2 ≤ 16 ^ 1).trans <|
    (Nat.pow_le_pow_left hk 1).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hd_ge_2a : 2 * (2 * k - 1) ≤ d := by
    have h2a_r : ((2 * (2 * k - 1) : ℕ) : ℝ) ≤ 8 * (k : ℝ) := by
      exact_mod_cast (by omega : 2 * (2 * k - 1) ≤ 8 * k)
    have h8k : 4 * (k : ℝ) * (x / y) = 4 * (k : ℝ) * x / y := by ring
    exact (Nat.le_floor_iff (by positivity)).mpr (by nlinarith)
  have h2d_le_aB : 2 * d ≤ (2 * k - 1) * B := by
    have hx_le_k : x ≤ (k : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < k)]
    have hd_r : (d : ℝ) ≤ 4 * (k : ℝ) ^ 2 :=
      (hd_le_real.trans (div_le_self (by positivity) hy_gt1.le)).trans (by nlinarith)
    have hd_nat : d ≤ 4 * k ^ 2 := by exact_mod_cast hd_r
    have hmul : 8 * k ^ 2 ≤ (2 * k - 1) * B :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hcond : 3 ^ (2 * k - 1) * 2 ^ d * d.factorial ≤ B * (2 * k - 1) ^ d := by
    set a : ℕ := 2 * k - 1
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hd_pos_r : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
    -- Suffices to compare `3^a * (2 * d)^d ≤ B * a^d` via logarithms.
    suffices hpow : 3 ^ a * 2 ^ d * d ^ d ≤ B * a ^ d from
      (Nat.mul_le_mul_left _ (Nat.factorial_le_pow d)).trans hpow
    have hlog_lhs_le : Real.log ((3 : ℝ) ^ a * (2 : ℝ) ^ d * (d : ℝ) ^ d) ≤
        Real.log ((B : ℝ) * (a : ℝ) ^ d) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
      have hlogB : Real.log (B : ℝ) = (18 * (k : ℝ)) * x := by
        simp only [B, Nat.cast_pow, Real.log_pow]
        push_cast; ring
      rw [hlogB]
      -- Term 1: `a * log 3 ≤ 2 * k * x`.
      have hterm1 : (a : ℝ) * Real.log 3 ≤ 2 * (k : ℝ) * x := by
        have ha_le : (a : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (by omega : a ≤ 2 * k)
        have hlog3 : Real.log 3 ≤ x := Real.log_le_log (by norm_num) (by linarith)
        nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
      -- Term 2: `d * (log 2 + log d - log a) ≤ 16 * k * x`.
      have hterm2 :
          (d : ℝ) * Real.log 2 + (d : ℝ) * Real.log (d : ℝ) - (d : ℝ) * Real.log (a : ℝ) ≤
            16 * (k : ℝ) * x := by
        have hrew :
            (d : ℝ) * Real.log 2 + (d : ℝ) * Real.log (d : ℝ) - (d : ℝ) * Real.log (a : ℝ) =
              (d : ℝ) * Real.log (2 * (d : ℝ) / (a : ℝ)) := by
          rw [Real.log_div (by positivity) ha_pos.ne', Real.log_mul (by norm_num) hd_pos_r.ne']
          ring
        have hratio_le : 2 * (d : ℝ) / (a : ℝ) ≤ 8 * x := by
          have hd_le_4kx : (d : ℝ) ≤ 4 * (k : ℝ) * x :=
            hd_le_real.trans (div_le_self (by positivity) hy_gt1.le)
          have ha_ge_kr : (k : ℝ) ≤ (a : ℝ) := by exact_mod_cast (by omega : k ≤ a)
          rw [div_le_iff₀ ha_pos]; nlinarith
        have hlog_ratio : Real.log (2 * (d : ℝ) / (a : ℝ)) ≤ 4 * y := by
          have h1 := Real.log_le_log (by positivity) hratio_le
          have hlog8 : Real.log 8 ≤ 3 := by
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat]
            linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
          rw [Real.log_mul (by norm_num) hx_pos.ne'] at h1; linarith
        rw [hrew]
        calc (d : ℝ) * Real.log (2 * (d : ℝ) / (a : ℝ))
            ≤ (d : ℝ) * (4 * y) := mul_le_mul_of_nonneg_left hlog_ratio hd_pos_r.le
          _ ≤ (4 * (k : ℝ) * x / y) * (4 * y) :=
            mul_le_mul_of_nonneg_right hd_le_real (by positivity)
          _ = 16 * (k : ℝ) * x := by field_simp [hy_pos.ne']; ring
      linarith
    exact_mod_cast (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_lhs_le
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
  have hB_pos_r : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by rw [hB]; positivity)
  have hlogB : Real.log (B : ℝ) = 18 * (k : ℝ) * x := by
    rw [show (B : ℝ) = (k : ℝ) ^ (18 * k) by exact_mod_cast hB, Real.log_pow]
    push_cast; ring
  have hk_lt : (k : ℝ) < Real.log (X : ℝ) := by
    have h1 := Real.log_le_log hB_pos_r (by exact_mod_cast hBX : (B : ℝ) ≤ X)
    have h2 : (1 : ℝ) < x := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
    nlinarith only [hk_real, h1, h2, hlogB]
  exact ⟨hlogB, hk_lt, Real.log_lt_log hx_pos (Real.log_lt_log (by linarith) hk_lt)⟩

/-- Shared ratio-transfer step: from `log X / log (log (log X)) ≤ C * k * log k / log (log k)`,
`3 * k * log k / log (log k) ≤ d`, `c * C ≤ 3 / 4`, `opt ≤ 1`, and `d / 4 ≤ EM`, deduce
`c * (log X / log (log (log X))) * opt ≤ EM`. -/
private theorem ratio_mul_opt_le_of_log_le {k d X : ℕ} {c C opt EM : ℝ} (hk : 16 ≤ k)
    (hX : 1 ≤ X) (hc : 0 ≤ c) (hcC : c * C ≤ 3 / 4)
    (hlog3_pos : 0 < Real.log (Real.log (Real.log (X : ℝ))))
    (hdiv : Real.log (X : ℝ) / Real.log (Real.log (Real.log (X : ℝ))) ≤
      C * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ)))
    (hd : 3 * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ)) ≤ (d : ℝ))
    (hopt : opt ≤ 1) (hEM : (d : ℝ) / 4 ≤ EM) :
    c * (Real.log (X : ℝ) / Real.log (Real.log (Real.log (X : ℝ)))) * opt ≤ EM := by
  obtain ⟨hx_gt_e, hy_gt1⟩ := exp_one_lt_log_of_sixteen_le hk
  have hx_pos : 0 < Real.log (k : ℝ) := (Real.exp_pos 1).trans hx_gt_e
  have hratio_nn : 0 ≤ c * (Real.log (X : ℝ) / Real.log (Real.log (Real.log (X : ℝ)))) :=
    mul_nonneg hc (div_nonneg (Real.log_nonneg (by exact_mod_cast hX)) hlog3_pos.le)
  have hstep : c * (Real.log (X : ℝ) / Real.log (Real.log (Real.log (X : ℝ)))) ≤ (d : ℝ) / 4 := by
    have hnn : 0 ≤ (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ)) := by positivity
    have h1 : c * (C * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))) =
        (c * C) * ((k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))) := by ring
    have h2 : (3 * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))) / 4 =
        (3 / 4 : ℝ) * ((k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))) := by ring
    nlinarith
  exact (mul_le_mul_of_nonneg_left hopt hratio_nn).trans (by linarith)

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
    have hliftA_inj : Function.Injective liftA := fun _ _ h => funext fun x =>
      hembedM (by simpa only [liftA, eJ.apply_symm_apply] using congrFun h (eJ.symm x))
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
    obtain rfl : y = relatedMixedDetTarget k B t :=
      not_ne_iff.mp fun hne => by simp [relatedMixedLowerNE_inl, hne] at hpos
    have hnotlast : (relatedMixedDetTarget k B t).tier ≠ Fin.last k :=
      Fin.ne_of_val_ne (by simp [relatedMixedDetTarget]; omega)
    rw [ite_eq_right hnotlast, relatedMixedLowerNE_inl, ite_eq_left rfl, sub_self, zero_mul,
      add_zero]
    simp only [relatedMixedLower, relatedMixedDetTarget]
    exact ⟨Nat.cast_le.mpr ((Nat.succ_le_of_lt t.tier.isLt).trans (Nat.sub_le k 1)),
      one_le_pow₀ (by norm_num)⟩
  | inr r =>
    have hlast : y.tier = Fin.last k :=
      not_ne_iff.mp fun hne => by simp [relatedMixedLowerNE, hne] at hpos
    rw [ite_eq_left hlast]
    simp only [relatedMixedLowerNE, hlast, ↓reduceIte, relatedMixedLower, Fin.val_last,
      two_pow_sub_one_div_two_pow hk]
    exact ⟨by linarith [one_div_nonneg.mpr (Nat.cast_nonneg (α := ℝ) B)],
      one_le_pow₀ (by norm_num)⟩

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
  have hM_ge_B : B ≤ M := hM_card ▸ Nat.le_mul_of_pos_left B Fintype.card_pos
  have h1_le_M : 1 ≤ M := by omega
  have hB_pos_r : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM_pos_r : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨hlogB_eq, _, hy_lt_log3M⟩ := log_log_lt_log_log_log_of_pow_le hk hB hM_ge_B
  have hlog3M_pos : 0 < Real.log (Real.log (Real.log (M : ℝ))) := by linarith
  -- Upper bound `log M ≤ 21 * k * log k`.
  have hM_le_nat : M ≤ 2 ^ (k + 1) * k ^ k * B :=
    hM_card ▸ Nat.mul_le_mul_right B
      ((card_relatedPureLowerMachine_le k).trans (Nat.mul_le_mul_left _ (Nat.factorial_le_pow k)))
  have hlogM_le : Real.log (M : ℝ) ≤ 21 * (k : ℝ) * x := by
    calc Real.log (M : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (k + 1) * (k : ℝ) ^ k * (B : ℝ)) :=
          Real.log_le_log hM_pos_r (by exact_mod_cast hM_le_nat)
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
  have hdiv1 : Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ))) ≤
      21 * (k : ℝ) * x / y := by
    calc Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ)))
        ≤ (21 * (k : ℝ) * x) / Real.log (Real.log (Real.log (M : ℝ))) :=
          div_le_div_of_nonneg_right hlogM_le hlog3M_pos.le
      _ ≤ (21 * (k : ℝ) * x) / y :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hy_lt_log3M.le
  calc
    (1 / 60 : ℝ) * (Real.log (M : ℝ) / Real.log (Real.log (Real.log (M : ℝ)))) *
        (relatedMixedLower k B).optMakespan
      ≤ (d : ℝ) / 4 :=
        ratio_mul_opt_le_of_log_le hk h1_le_M (by norm_num) (by norm_num) hlog3M_pos
          hdiv1 hd_ge_3 (optMakespan_relatedMixedLower_le_one k B) le_rfl
    _ ≤ (relatedMixedLower k B).expectedMakespan (relatedMixedLowerNE k B) :=
        expectedMakespan_relatedMixedLowerNE_ge_quarter_of_ballsIntoBins
          (by omega) hB2 hd_ge_2a h2d_le_aB hcond

/-- Opaque helper for the replication factor `k ^ (18 * k)` to keep kernel reduction from
evaluating large powers of concrete constants such as `16 ^ 288`. -/
private def relatedMixedRep (k : ℕ) : ℕ := k ^ (18 * k)

private theorem relatedMixedRep_eq (k : ℕ) : relatedMixedRep k = k ^ (18 * k) := rfl

private theorem le_card_relatedMixedLowerMachine_rep {k : ℕ} (hk : 1 ≤ k) :
    k ≤ Fintype.card (RelatedMixedLowerMachine k (relatedMixedRep k)) :=
  (relatedMixedRep_eq k ▸ Nat.le_self_pow (by omega : 18 * k ≠ 0) k).trans
    (card_relatedMixedLowerMachine k _ ▸ Nat.le_mul_of_pos_left _ Fintype.card_pos)

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
    have hS_ne : ((range (m + 1)).filter fun k => 16 ≤ k ∧ Mfn k ≤ m).Nonempty :=
      ⟨16, mem_filter.mpr ⟨mem_range.mpr
        (Nat.lt_succ_of_le ((le_card_relatedMixedLowerMachine_rep (by omega)).trans hlarge)),
        le_rfl, hlarge⟩⟩
    obtain ⟨k, hk_mem, hk_max⟩ :=
      exists_max_image ((range (m + 1)).filter fun k => 16 ≤ k ∧ Mfn k ≤ m) id hS_ne
    obtain ⟨_, hk16, hMk_le⟩ := mem_filter.mp hk_mem
    have hm_lt_next : m < Mfn (k + 1) := not_le.mp fun hle =>
      Nat.not_succ_le_self k <| hk_max (k + 1) <| mem_filter.mpr
        ⟨mem_range.mpr (Nat.lt_succ_of_le
          ((le_card_relatedMixedLowerMachine_rep (by omega)).trans hle)), by omega, hle⟩
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
    have hembedM_inj : Function.Injective embedM := fun _ _ h =>
      eM.symm.injective (Fin.ext (by simpa only [embedM] using congrArg Fin.val h))
    have hp_embed : ∀ i x, p i (embedM x) = relatedMixedLowerNE k B (eJ i) x := fun i x => by
      dsimp only [p]
      rw [dite_eq_left (eM.symm x).isLt, eM.apply_symm_apply]
    -- Expected load of `G` under `p` matches `relatedMixedLower k B` on the first `Mfn k` machines.
    have hE_eq : ∀ j : Fin m,
        G.expectedLoad p j =
          if h : j.val < Mfn k then
            (relatedMixedLower k B).expectedLoad (relatedMixedLowerNE k B) (eM ⟨j.val, h⟩)
          else 0 := fun j => by
      rw [expectedLoad]
      split_ifs with h
      · simp only [G, p, dite_eq_left h]
        exact Fintype.sum_equiv eJ _ _ fun _ => rfl
      · exact sum_eq_zero fun _ _ => by simp only [p, dite_eq_right h, zero_mul]
    have hbase_NE := isMixedNash_relatedMixedLowerNE (k := k) (B := B) (by omega)
    have hp_isNE : G.toCostGame.IsMixedNash p := by
      rw [G.isMixedNash_iff]
      refine ⟨fun i => ?_, fun i j hpos j' => ?_⟩
      · refine isMixedStrategy_iff.2 ⟨fun j => ?_, ?_⟩
        · simp only [p]
          split_ifs
          exacts [(hbase_NE.1 (eJ i)).nonneg _, le_rfl]
        rw [← sum_subset (subset_univ (univ.image embedM)) fun j _ hnot => by
          have hge : ¬ j.val < Mfn k := fun hlt => hnot <| mem_image.mpr
            ⟨eM ⟨j.val, hlt⟩, mem_univ _, Fin.ext (by simp [embedM])⟩
          simp only [p, dite_eq_right hge],
          sum_image (fun _ _ _ _ h => hembedM_inj h)]
        simp_rw [hp_embed]
        exact (hbase_NE.1 (eJ i)).sum_eq_one
      · have hj_lt : j.val < Mfn k := not_le.mp fun h => by simp [p, not_lt_of_ge h] at hpos
        rw [hE_eq j, hE_eq j', dite_eq_left hj_lt]
        simp only [G, p, dite_eq_left hj_lt] at hpos ⊢
        by_cases hj'_lt : j'.val < Mfn k
        · simp only [dite_eq_left hj'_lt]
          exact (((relatedMixedLower k B).isMixedNash_iff _).mp hbase_NE).2
            (eJ i) (eM ⟨j.val, hj_lt⟩) hpos (eM ⟨j'.val, hj'_lt⟩)
        · simp only [dite_eq_right hj'_lt, zero_add, sub_zero, one_mul, one_div, div_inv_eq_mul]
          -- On any active machine, job `eJ i`'s equilibrium cost is at most `k`, while an idle
          -- machine of speed `1 / k` charges `weight (eJ i) * k ≥ k`.
          obtain ⟨hcost_le, hw_ge1⟩ := equilibrium_cost_relatedMixedLowerNE_le_k (by omega) hpos
          nlinarith only [hcost_le, hw_ge1, hk_pos_r]
    -- Helper computing `G.load (fun i => embedM (A (eJ i))) j`.
    have hload_embed : ∀ (A : RelatedMixedLowerJob k B → RelatedMixedLowerMachine k B) (j : Fin m),
        G.load (fun i => embedM (A (eJ i))) j =
          if h : j.val < Mfn k then (relatedMixedLower k B).load A (eM ⟨j.val, h⟩) else 0 := by
      intro A j
      rw [LoadBalancingGame.load_eq_sum_div, sum_filter,
        Fintype.sum_equiv eJ _
          (fun x => if embedM (A x) = j then (relatedMixedLower k B).weight x else 0)
          fun _ => rfl]
      by_cases h : j.val < Mfn k
      · simp only [G, dite_eq_left h, LoadBalancingGame.load_eq_sum_div, sum_filter]
        refine congrArg (· / _) (sum_congr rfl fun x _ => if_congr ?_ rfl rfl)
        exact ⟨fun heq => eM.symm_apply_eq.mp (Fin.ext (congrArg (·.val) heq)),
          fun heq => Fin.ext (by simp [embedM, heq])⟩
      · rw [dite_eq_right h, sum_eq_zero fun x _ => by
          have hne : embedM (A x) ≠ j := fun heq => h (congrArg Fin.val heq ▸ (eM.symm (A x)).isLt)
          rw [ite_eq_right hne], zero_div]
    -- Transfer `optMakespan ≤ 1` and `d / 4 ≤ expectedMakespan` via idle padding.
    have hpad := optMakespan_le_and_expectedMakespan_ge_of_idlePad
      (relatedMixedLower k B) (relatedMixedLowerNE k B) G p eJ hembedM_inj
      (fun i j => (hp_isNE.1 i).nonneg j) hp_embed
      (fun A₀ x => by
        rw [hload_embed A₀ (embedM x), dite_eq_left (eM.symm x).isLt, eM.apply_symm_apply])
      (fun A₀ j => by
        rw [hload_embed A₀ j]
        split_ifs
        exacts [(relatedMixedLower k B).load_le_makespan A₀ _,
          (relatedMixedLower k B).makespan_nonneg A₀])
    obtain ⟨hB2, hd_ge_2a, h2d_le_aB, hcond, hd_ge_3⟩ := ballsIntoBins_params_of_ge_sixteen hk16
    rw [← hB_eq] at hB2 h2d_le_aB hcond
    set d : ℕ := ⌊4 * (k : ℝ) * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))⌋₊
    -- Asymptotic bound: `(1 / 3200) * (log m / log (log (log m))) ≤ d / 4`.
    have hk_real : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk16
    obtain ⟨hx_gt_e, hy_gt1⟩ := exp_one_lt_log_of_sixteen_le hk16
    set x : ℝ := Real.log (k : ℝ)
    have hx_pos : 0 < x := (Real.exp_pos 1).trans hx_gt_e
    set y : ℝ := Real.log x
    have hB_le_m : B ≤ m :=
      (Nat.le_mul_of_pos_left B Fintype.card_pos).trans
        ((card_relatedMixedLowerMachine k B).symm.le.trans hMk_le)
    obtain ⟨_, _, hy_lt_log3m⟩ := log_log_lt_log_log_log_of_pow_le hk16 hB_eq hB_le_m
    have hlog3m_pos : 0 < Real.log (Real.log (Real.log (m : ℝ))) := by linarith
    -- Upper bound `log m ≤ log (Mfn (k + 1)) ≤ 80 * k * log k`.
    have hm_le_nat : m ≤ 2 ^ (k + 2) * (k + 1) ^ (k + 1) * (k + 1) ^ (18 * (k + 1)) :=
      hm_lt_next.le.trans <| by
        dsimp only [Mfn]
        rw [card_relatedMixedLowerMachine, relatedMixedRep_eq]
        exact Nat.mul_le_mul_right _ ((card_relatedPureLowerMachine_le (k + 1)).trans
          (Nat.mul_le_mul_left _ (Nat.factorial_le_pow (k + 1))))
    have hlogm_le : Real.log (m : ℝ) ≤ 80 * (k : ℝ) * x := by
      have hlog_k1 : Real.log ((k + 1 : ℕ) : ℝ) ≤ 2 * x := by
        have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
          push_cast; nlinarith only [hk_real]
        calc Real.log ((k + 1 : ℕ) : ℝ)
            ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log (by positivity) hk1_le
          _ = 2 * x := by rw [Real.log_pow]; simp only [x]; norm_num
      have hlog2_le : Real.log 2 ≤ x := Real.log_le_log (by norm_num) (by linarith)
      calc Real.log (m : ℝ)
          ≤ Real.log ((2 : ℝ) ^ (k + 2) * ((k + 1 : ℕ) : ℝ) ^ (k + 1) *
              ((k + 1 : ℕ) : ℝ) ^ (18 * (k + 1))) :=
            Real.log_le_log (Nat.cast_pos.mpr (NeZero.pos m)) (by exact_mod_cast hm_le_nat)
        _ = ((k + 2 : ℕ) : ℝ) * Real.log 2 +
              19 * ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity),
              Real.log_pow, Real.log_pow, Real.log_pow]
            push_cast; ring
        _ ≤ 2 * (k : ℝ) * x + 19 * ((k + 1 : ℕ) : ℝ) * (2 * x) := by
            have h1 : ((k + 2 : ℕ) : ℝ) * Real.log 2 ≤ 2 * (k : ℝ) * x :=
              calc ((k + 2 : ℕ) : ℝ) * Real.log 2
                  ≤ ((k + 2 : ℕ) : ℝ) * x := mul_le_mul_of_nonneg_left hlog2_le (by positivity)
                _ ≤ 2 * (k : ℝ) * x :=
                  mul_le_mul_of_nonneg_right (by push_cast; linarith) hx_pos.le
            linarith [mul_le_mul_of_nonneg_left hlog_k1
              (by positivity : (0 : ℝ) ≤ 19 * ((k + 1 : ℕ) : ℝ))]
        _ ≤ 80 * (k : ℝ) * x := by
            push_cast; nlinarith only [hk_real, hx_pos]
    have hdiv_le : Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ))) ≤
        80 * (k : ℝ) * x / y := by
      calc Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))
          ≤ (80 * (k : ℝ) * x) / Real.log (Real.log (Real.log (m : ℝ))) :=
            div_le_div_of_nonneg_right hlogm_le hlog3m_pos.le
        _ ≤ (80 * (k : ℝ) * x) / y :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hy_lt_log3m.le
    refine ⟨n, hn_le, G, p, hp_isNE,
      optMakespan_pos_of_exists_weight_pos G
        ⟨eJ.symm (Sum.inr ⟨0, Nat.mul_pos (by omega) (NeZero.pos B)⟩),
          by simp [G, relatedMixedLower]⟩, ?_⟩
    calc (1 / 3200 : ℝ) * (Real.log (m : ℝ) / Real.log (Real.log (Real.log (m : ℝ)))) *
            G.optMakespan
        ≤ (d : ℝ) / 4 :=
          ratio_mul_opt_le_of_log_le hk16 (by omega) (by norm_num) (by norm_num) hlog3m_pos
            hdiv_le hd_ge_3 (hpad.1.trans (optMakespan_relatedMixedLower_le_one k B)) le_rfl
      _ ≤ G.expectedMakespan p :=
          (expectedMakespan_relatedMixedLowerNE_ge_quarter_of_ballsIntoBins
            (by omega) hB2 hd_ge_2a h2d_le_aB hcond).trans hpad.2
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
    have hlog1024 : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
      rw [show (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) by norm_num, Real.log_pow]; norm_num
    by_cases hm1024 : m ≤ 1024
    · -- `16 ≤ m ≤ 1024`: `log m < 10` and `log (log (log m)) ≥ 0.018`, so ratio `< 600 ≤ 3200`.
      have hlogm_lt : Real.log (m : ℝ) < 10 := by
        linarith [Real.log_le_log hm_pos_r (by exact_mod_cast hm1024 : (m : ℝ) ≤ 1024),
          Real.log_two_lt_d9]
      have hlogm_ge : (2.7725 : ℝ) ≤ Real.log (m : ℝ) := by
        have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_le_log (by norm_num) (by exact_mod_cast hm : (16 : ℝ) ≤ m),
          Real.log_two_gt_d9]
      have hlog2m_ge : (1.019 : ℝ) ≤ Real.log (Real.log (m : ℝ)) := by
        have hdiv_ge : (1.0195 : ℝ) ≤ Real.log (m : ℝ) / Real.exp 1 := by
          rw [le_div_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_lt_d9]
        have hmono := (Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 1.0195)).trans
          (Real.log_le_log (by norm_num) hdiv_ge)
        rw [Real.log_div (by linarith) (Real.exp_pos 1).ne', Real.log_exp] at hmono
        linarith
      have hlog3m_ge : (0.018 : ℝ) ≤ Real.log (Real.log (Real.log (m : ℝ))) :=
        (by norm_num : (0.018 : ℝ) ≤ 1 - (1.019 : ℝ)⁻¹).trans <|
          (Real.one_sub_inv_le_log_of_pos (by norm_num)).trans
            (Real.log_le_log (by norm_num) hlog2m_ge)
      rw [div_le_iff₀ (by linarith)]; linarith
    · -- `1024 < m < Mfn 16`: `log m ≤ 1233` and `log (log (log m)) ≥ 0.4`, so ratio `< 3200`.
      push Not at hm1024
      have hlogm_le : Real.log (m : ℝ) ≤ 1233 := by
        have hm_le_pow : m ≤ 2 ^ 1233 := by
          have h1 : Mfn 16 ≤ 2 ^ 17 * 16 ^ 16 * 16 ^ (18 * 16) := by
            dsimp only [Mfn]
            rw [card_relatedMixedLowerMachine, relatedMixedRep_eq]
            exact Nat.mul_le_mul_right _ ((card_relatedPureLowerMachine_le 16).trans
              (Nat.mul_le_mul_left _ (Nat.factorial_le_pow 16)))
          have h16 : (16 : ℕ) = 2 ^ 4 := rfl
          have hrew : 2 ^ 17 * 16 ^ 16 * 16 ^ (18 * 16) = 2 ^ 1233 := by
            rw [h16, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
            exact congrArg (2 ^ ·) rfl
          exact (hlarge.le.trans h1).trans hrew.le
        have hlog2 : Real.log 2 ≤ 1 := by
          linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
        calc Real.log (m : ℝ)
            ≤ Real.log ((2 : ℝ) ^ (1233 : ℕ)) :=
              Real.log_le_log hm_pos_r (by exact_mod_cast hm_le_pow)
          _ = 1233 * Real.log 2 := by rw [Real.log_pow]; norm_num
          _ ≤ 1233 := by linarith
      have hlogm_ge : (6.93 : ℝ) ≤ Real.log (m : ℝ) := by
        linarith [Real.log_le_log (by norm_num) (by exact_mod_cast hm1024.le : (1024 : ℝ) ≤ m),
          Real.log_two_gt_d9]
      have hlog2m_ge : (1.69 : ℝ) ≤ Real.log (Real.log (m : ℝ)) := by
        have h1 := Real.log_le_log (by positivity)
          (by linarith [Real.exp_one_lt_d9] : 2 * Real.exp 1 ≤ Real.log (m : ℝ))
        rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h1
        linarith [Real.log_two_gt_d9]
      have hlog3m_ge : (0.4 : ℝ) ≤ Real.log (Real.log (Real.log (m : ℝ))) :=
        (by norm_num : (0.4 : ℝ) ≤ 1 - (1.69 : ℝ)⁻¹).trans <|
          (Real.one_sub_inv_le_log_of_pos (by norm_num)).trans
            (Real.log_le_log (by norm_num) hlog2m_ge)
      rw [div_le_iff₀ (by linarith)]; linarith

end Cslib.GameTheory.LoadBalancingGame

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.LoadBalancing.Basic
public import CslibFrontier.GameTheory.Strategic.Nash
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mixed Nash equilibria in selfish load-balancing games

This module formalizes mixed Nash equilibria and expected makespan in the Koutsoupias–Papadimitriou
load-balancing model ([KoutsoupiasPapadimitriou1999]; [Vocking2007]), building directly
on `Cslib.GameTheory.CostGame.IsMixedNash`, `IsTotallyMixedNash`, and `productWeight` from
`CslibFrontier.GameTheory.Strategic`.

## Main definitions

* `Cslib.GameTheory.LoadBalancingGame.expectedLoad`: the expected load
  `E[ℓ_j] = ∑ i, p i j * (weight i / speed j)` of machine `j` under a mixed strategy profile `p`.
* `Cslib.GameTheory.LoadBalancingGame.expectedMakespan`: the Koutsoupias–Papadimitriou social cost
  `E_{A ∼ p}[max_j ℓ_j(A)] = ∑ A, productWeight p A * makespan A` ([Vocking2007]).

## Main results

* `Cslib.GameTheory.LoadBalancingGame.deviationCost_toCostGame`,
  `Cslib.GameTheory.LoadBalancingGame.isMixedNash_iff` ([Vocking2007]): closed-form expected
  deviation cost `c_i^j = E[ℓ_j] + (1 - p_i^j) * w_i / s_j` and support characterization of mixed
  Nash equilibria.
* `Cslib.GameTheory.LoadBalancingGame.eq_of_isTotallyMixedNash` ([MavronicolasSpirakis2001];
  [Vocking2007]): uniqueness of totally mixed Nash equilibria when all job weights
  are strictly positive and `|ι| ≠ 1`.
* `Cslib.GameTheory.LoadBalancingGame.exists_isTotallyMixedNash_twoUnitRelated_iff`
  ([Vocking2007]): exact characterization and closed form for 2 unit jobs on 2
  machines of speeds `1` and `s > 0` (`1 / 2 < s < 2`, with `p_i^0 = (2 - s) / (s + 1)`).
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.expectedMakespan_le_three_halves_mul_optMakespan`
  ([KoutsoupiasPapadimitriou1999]): for `2` identical machines and any finite set of jobs, every
  mixed Nash equilibrium satisfies `expectedMakespan p ≤ (3 / 2) * optMakespan`.
* `Cslib.GameTheory.LoadBalancingGame.expectedMakespan_kpTwoUnitUniform`: exact tightness of `3/2`
  on 2 unit jobs and 2 identical machines under the uniform mixed equilibrium.

## References

* [KoutsoupiasPapadimitriou1999]
* [MavronicolasSpirakis2001]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory.LoadBalancingGame

open Finset

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]

/-- The **expected load** of machine `j` under mixed strategy profile `p`:
`∑ i, p i j * (weight i / speed j)`. -/
@[expose] noncomputable def expectedLoad (G : LoadBalancingGame ι M) (p : ι → M → ℝ) (j : M) : ℝ :=
  ∑ i, p i j * (G.weight i / G.speed j)

/-- The **expected makespan** (Koutsoupias–Papadimitriou social cost, [Vocking2007]) under the
product distribution of mixed strategies `p`: `∑ A, productWeight p A * makespan A`. -/
@[expose] noncomputable def expectedMakespan [Nonempty M] (G : LoadBalancingGame ι M)
    (p : ι → M → ℝ) : ℝ :=
  ∑ A : ι → M, productWeight p A * G.makespan A

/-- Expected load equals the expectation of `G.load A j` under the product distribution. -/
theorem expectedLoad_eq_sum_productWeight (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : ∀ i, ∑ j, p i j = 1) (j : M) :
    G.expectedLoad p j = ∑ A : ι → M, productWeight p A * G.load A j := by
  have hload : ∀ A : ι → M, G.load A j = ∑ i, if A i = j then G.weight i / G.speed j else 0 :=
    fun A => by simp [load, UnrelatedLoadBalancingGame.load, toUnrelated, sum_filter]
  rw [expectedLoad]
  simp_rw [hload, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_productWeight_mul_apply (fun k _ => hp k) (fun m => if m = j then _ else 0)]
  simp

omit [DecidableEq ι] [DecidableEq M] in
/-- Speed-weighted expected loads sum to the total job weight. -/
theorem sum_speed_mul_expectedLoad (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : ∀ i, ∑ j, p i j = 1) :
    ∑ j, G.speed j * G.expectedLoad p j = ∑ i, G.weight i := by
  simp only [expectedLoad, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have hterm (j : M) : G.speed j * (p i j * (G.weight i / G.speed j)) = p i j * G.weight i := by
    have := (G.speed_pos j).ne'
    field_simp
  simp [hterm, ← sum_mul, hp i]

/-- Point-mass mixed profiles recover the deterministic makespan. -/
theorem expectedMakespan_single [Nonempty M] (G : LoadBalancingGame ι M) (A : ι → M) :
    G.expectedMakespan (fun i => Pi.single (A i) 1) = G.makespan A := by
  simp [expectedMakespan, productWeight_single]

/-- When `optMakespan = 0`, every job has weight `0`, so every profile has zero expected makespan.
-/
theorem expectedMakespan_eq_zero_of_optMakespan_eq_zero [Nonempty M] (G : LoadBalancingGame ι M)
    (hopt0 : G.optMakespan = 0) (p : ι → M → ℝ) : G.expectedMakespan p = 0 := by
  simp [expectedMakespan, G.makespan_eq_zero_of_optMakespan_eq_zero hopt0]

/-- **Closed-form expected deviation cost** ([Vocking2007]): when player `i` deviates
to machine `j` against a profile `p` of probability vectors, its expected cost is
`expectedLoad p j + (1 - p i j) * (weight i / speed j)`. -/
theorem deviationCost_toCostGame (G : LoadBalancingGame ι M) {p : ι → M → ℝ}
    (hp : ∀ k, ∑ m, p k m = 1) (i : ι) (j : M) :
    G.toCostGame.deviationCost p i j =
      G.expectedLoad p j + (1 - p i j) * (G.weight i / G.speed j) := by
  rw [CostGame.deviationCost_def]
  have hcost : ∀ A : ι → M, G.toCostGame.cost i (Function.update A i j) =
      G.weight i / G.speed j +
        ∑ k ∈ univ.erase i, if A k = j then G.weight k / G.speed j else 0 := fun A => by
    change G.load (Function.update A i j) (Function.update A i j i) = _
    rw [Function.update_self, load, UnrelatedLoadBalancingGame.load, sum_filter,
      ← add_sum_erase _ _ (mem_univ i), Function.update_self, ite_eq_left rfl]
    change G.weight i / G.speed j + _ = _
    congr 1
    exact sum_congr rfl fun k hk => by
      simp only [toUnrelated, Function.update_of_ne (ne_of_mem_erase hk)]
  simp_rw [hcost, mul_add, sum_add_distrib, ← sum_mul, sum_productWeight hp, one_mul, mul_sum]
  rw [sum_comm]
  have hrest :
      ∑ k ∈ univ.erase i, ∑ A : ι → M,
        productWeight p A * (if A k = j then G.weight k / G.speed j else 0) =
      ∑ k ∈ univ.erase i, p k j * (G.weight k / G.speed j) :=
    sum_congr rfl fun k _ => by
      rw [sum_productWeight_mul_apply (fun r _ => hp r) (fun m => if m = j then _ else 0)]
      simp
  rw [hrest, expectedLoad, ← add_sum_erase _ _ (mem_univ i)]
  ring

/-- **Mixed Nash characterization** ([Vocking2007]): a profile `p` is a mixed
Nash equilibrium of `G` if and only if each `p i` is a mixed strategy and for every player `i` and
machine `j` in the support of `p i`, no machine `k` has a strictly smaller expected deviation cost
`expectedLoad p k + (1 - p i k) * (weight i / speed k)`. -/
theorem isMixedNash_iff (G : LoadBalancingGame ι M) (p : ι → M → ℝ) :
    G.toCostGame.IsMixedNash p ↔
      (∀ i, IsMixedStrategy (p i)) ∧
      ∀ i j, 0 < p i j → ∀ k,
        G.expectedLoad p j + (1 - p i j) * (G.weight i / G.speed j) ≤
          G.expectedLoad p k + (1 - p i k) * (G.weight i / G.speed k) := by
  constructor
  · intro h
    have hp1 : ∀ k, ∑ m, p k m = 1 := fun k => (h.1 k).sum_eq_one
    refine ⟨h.1, fun i j hj k => ?_⟩
    rw [← G.deviationCost_toCostGame hp1 i j, ← G.deviationCost_toCostGame hp1 i k,
      h.deviationCost_eq_of_pos i hj]
    exact h.2 i k
  · rintro ⟨hp, hsup⟩
    have hp1 : ∀ k, ∑ m, p k m = 1 := fun k => (hp k).sum_eq_one
    refine ⟨hp, fun i k => ?_⟩
    rw [← G.toCostGame.sum_mul_deviationCost_eq_expectedCost p (hp1 i)]
    calc ∑ j, p i j * G.toCostGame.deviationCost p i j
        ≤ ∑ j, p i j * G.toCostGame.deviationCost p i k := by
          refine sum_le_sum fun j _ => ?_
          rcases ((hp i).nonneg j).eq_or_lt with h0 | hpos
          · rw [← h0, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left ?_ hpos.le
            rw [G.deviationCost_toCostGame hp1 i j, G.deviationCost_toCostGame hp1 i k]
            exact hsup i j hpos k
      _ = G.toCostGame.deviationCost p i k := by rw [← sum_mul, hp1 i, one_mul]

section TotallyMixedUniqueness

/-- **Uniqueness of totally mixed Nash equilibria** ([MavronicolasSpirakis2001]; [Vocking2007]):
if every job has strictly positive weight and `|ι| ≠ 1`, then a uniformly related
load-balancing game admits at most one totally mixed Nash equilibrium.

(The hypothesis `|ι| ≠ 1` is necessary: a single positive-weight job on two identical machines has
a continuum of totally mixed Nash equilibria.) -/
theorem eq_of_isTotallyMixedNash (G : LoadBalancingGame ι M) (hw : ∀ i, 0 < G.weight i)
    (hn : Fintype.card ι ≠ 1) {p q : ι → M → ℝ}
    (hp : G.toCostGame.IsTotallyMixedNash p) (hq : G.toCostGame.IsTotallyMixedNash q) :
    p = q := by
  rcases isEmpty_or_nonempty M with hM | _
  · funext i j
    exact hM.elim j
  have hp1 : ∀ i, ∑ j, p i j = 1 := fun i => (hp.1.1 i).sum_eq_one
  have hq1 : ∀ i, ∑ j, q i j = 1 := fun i => (hq.1.1 i).sum_eq_one
  have hS_pos : 0 < ∑ j : M, G.speed j :=
    sum_pos (fun j _ => G.speed_pos j) univ_nonempty
  -- For any totally mixed NE `r`, player `i`'s common cost `C_i` is uniquely determined by `G`.
  have hcost_eq : ∀ r : ι → M → ℝ, G.toCostGame.IsTotallyMixedNash r → ∀ i,
      (∑ j : M, G.speed j) * G.toCostGame.expectedCost r i =
        (∑ k, G.weight k) + ((Fintype.card M : ℝ) - 1) * G.weight i := by
    intro r hr i
    have hr1 : ∀ k, ∑ m, r k m = 1 := fun k => (hr.1.1 k).sum_eq_one
    have heq_j : ∀ j : M,
        G.speed j * G.toCostGame.expectedCost r i =
          G.speed j * G.expectedLoad r j + (1 - r i j) * G.weight i := by
      intro j
      have hdev := hr.1.deviationCost_eq_of_pos i (hr.2 i j)
      rw [G.deviationCost_toCostGame hr1 i j] at hdev
      have hs := (G.speed_pos j).ne'
      rw [← hdev, mul_add]
      congr 1
      field_simp
    calc (∑ j : M, G.speed j) * G.toCostGame.expectedCost r i
        = ∑ j : M, G.speed j * G.toCostGame.expectedCost r i := sum_mul _ _ _
      _ = ∑ j : M, (G.speed j * G.expectedLoad r j + (1 - r i j) * G.weight i) :=
          sum_congr rfl fun j _ => heq_j j
      _ = (∑ j : M, G.speed j * G.expectedLoad r j) +
            ∑ j : M, (1 - r i j) * G.weight i := sum_add_distrib
      _ = (∑ k, G.weight k) + ((Fintype.card M : ℝ) - 1) * G.weight i := by
          rw [G.sum_speed_mul_expectedLoad hr1, ← sum_mul, sum_sub_distrib, sum_const, card_univ,
            nsmul_eq_mul, mul_one, hr1 i]
  have hCi : ∀ i, G.toCostGame.expectedCost p i = G.toCostGame.expectedCost q i := fun i =>
    mul_left_cancel₀ hS_pos.ne' ((hcost_eq p hp i).trans (hcost_eq q hq i).symm)
  -- Express `p i j - q i j` in terms of `expectedLoad p j - expectedLoad q j`.
  have hdiff : ∀ i j,
      (p i j - q i j) * G.weight i = G.speed j * (G.expectedLoad p j - G.expectedLoad q j) := by
    intro i j
    have hpj := hp.1.deviationCost_eq_of_pos i (hp.2 i j)
    have hqj := hq.1.deviationCost_eq_of_pos i (hq.2 i j)
    rw [G.deviationCost_toCostGame hp1 i j] at hpj
    rw [G.deviationCost_toCostGame hq1 i j] at hqj
    have hs := (G.speed_pos j).ne'
    have h2 := congrArg (G.speed j * ·) (show G.expectedLoad p j + (1 - p i j) *
        (G.weight i / G.speed j) = G.expectedLoad q j + (1 - q i j) * (G.weight i / G.speed j) by
      linarith [hCi i])
    field_simp at h2
    linarith
  -- Sum over `i` to force `expectedLoad p j = expectedLoad q j` since `|ι| ≠ 1`.
  have hload_eq : ∀ j, G.expectedLoad p j = G.expectedLoad q j := by
    intro j
    have hs := (G.speed_pos j).ne'
    have hsum_lhs : ∑ i : ι, (p i j - q i j) * G.weight i =
        G.speed j * (G.expectedLoad p j - G.expectedLoad q j) := by
      simp only [expectedLoad, mul_sub, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by field_simp
    have hsum_rhs : ∑ i : ι, (p i j - q i j) * G.weight i =
        (Fintype.card ι : ℝ) * (G.speed j * (G.expectedLoad p j - G.expectedLoad q j)) := by
      simp_rw [hdiff _ j, sum_const, card_univ, nsmul_eq_mul]
    have hn_ne : (Fintype.card ι : ℝ) - 1 ≠ 0 :=
      sub_ne_zero.mpr (mod_cast hn)
    have h0 : G.speed j * (G.expectedLoad p j - G.expectedLoad q j) = 0 :=
      mul_left_cancel₀ hn_ne (by linarith)
    linarith [(mul_eq_zero.mp h0).resolve_left hs]
  funext i j
  have h0 := hdiff i j
  rw [hload_eq j, sub_self, mul_zero] at h0
  linarith [(mul_eq_zero.mp h0).resolve_right (hw i).ne']

end TotallyMixedUniqueness

section TwoUnitRelated

/-- Two unit-weight jobs on two machines of speeds `1` and `s > 0` ([Vocking2007]). -/
@[expose] def twoUnitRelated (s : ℝ) (hs : 0 < s) : LoadBalancingGame (Fin 2) (Fin 2) where
  weight _ := 1
  speed := ![1, s]
  weight_nonneg _ := zero_le_one
  speed_pos j := by
    fin_cases j
    · exact zero_lt_one
    · exact hs

private theorem isTotallyMixedNash_twoUnitRelated_profile {s : ℝ} (hs : 0 < s)
    (hs1 : 1 / 2 < s) (hs2 : s < 2) :
    (twoUnitRelated s hs).toCostGame.IsTotallyMixedNash
      (fun _ => ![(2 - s) / (s + 1), (2 * s - 1) / (s + 1)]) := by
  let G := twoUnitRelated s hs
  let p : Fin 2 → Fin 2 → ℝ := fun _ => ![(2 - s) / (s + 1), (2 * s - 1) / (s + 1)]
  have hpos_sp : 0 < s + 1 := by linarith
  have hp1 : ∀ k, ∑ m, p k m = 1 := fun k => by
    simp only [Fin.sum_univ_two, p, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    field_simp [hpos_sp.ne']
    ring
  refine G.toCostGame.isTotallyMixedNash_iff.mpr ⟨fun _ j => ?_, hp1, fun i a b => ?_⟩
  · fin_cases j <;> exact div_pos (by linarith) hpos_sp
  · rw [G.deviationCost_toCostGame hp1 i a, G.deviationCost_toCostGame hp1 i b]
    have hval : ∀ j : Fin 2,
        G.expectedLoad p j + (1 - p i j) * (G.weight i / G.speed j) = 3 / (s + 1) := fun j => by
      fin_cases j <;>
        simp only [expectedLoad, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, G,
          twoUnitRelated, p, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          div_one, mul_one] <;>
        field_simp [hs.ne', hpos_sp.ne'] <;>
        ring
    rw [hval a, hval b]

/-- **Two unit jobs on two related machines** ([Vocking2007]): a totally mixed Nash
equilibrium exists if and only if `1 / 2 < s < 2`, in which case it is uniquely given by
`p i 0 = (2 - s) / (s + 1)` and `p i 1 = (2 * s - 1) / (s + 1)`. -/
theorem exists_isTotallyMixedNash_twoUnitRelated_iff {s : ℝ} (hs : 0 < s) :
    (∃ p, (twoUnitRelated s hs).toCostGame.IsTotallyMixedNash p) ↔ 1 / 2 < s ∧ s < 2 := by
  let G := twoUnitRelated s hs
  have hpos_sp : 0 < s + 1 := by linarith
  refine ⟨?_, fun ⟨hs1, hs2⟩ => ⟨_, isTotallyMixedNash_twoUnitRelated_profile hs hs1 hs2⟩⟩
  rintro ⟨p, hp⟩
  have hp1 : ∀ i, p i 0 + p i 1 = 1 := fun i => by
    simpa only [Fin.sum_univ_two] using (hp.1.1 i).sum_eq_one
  have hdev : ∀ i : Fin 2,
      p 0 0 + p 1 0 + (1 - p i 0) = (p 0 1 + p 1 1) / s + (1 - p i 1) * (1 / s) := fun i => by
    have h := (G.toCostGame.isTotallyMixedNash_iff.mp hp).2.2 i 0 1
    have hp1' : ∀ k, ∑ m, p k m = 1 := fun k => (hp.1.1 k).sum_eq_one
    rw [G.deviationCost_toCostGame hp1' i 0, G.deviationCost_toCostGame hp1' i 1] at h
    simp only [expectedLoad, Fin.sum_univ_two, G, twoUnitRelated, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, div_one, mul_one] at h
    rw [h]; ring
  have hp0_eq : p 0 0 = (2 - s) / (s + 1) := by
    have h0' := congrArg (s * ·) (hdev 0)
    have h1' := congrArg (s * ·) (hdev 1)
    field_simp [hs.ne'] at h0' h1'
    rw [eq_div_iff hpos_sp.ne']
    nlinarith [hp1 0, hp1 1]
  have hgt0 := (div_pos_iff_of_pos_right hpos_sp).mp (hp0_eq ▸ hp.2 0 0)
  have hlt1 := (div_lt_one hpos_sp).mp (hp0_eq ▸ show p 0 0 < 1 by linarith [hp1 0, hp.2 0 1])
  exact ⟨by linarith, by linarith⟩

/-- Closed form of the unique totally mixed Nash equilibrium of `twoUnitRelated s hs` for
`1 / 2 < s < 2` ([Vocking2007]). -/
theorem isTotallyMixedNash_twoUnitRelated_eq {s : ℝ} (hs : 0 < s) (hs1 : 1 / 2 < s) (hs2 : s < 2)
    {p : Fin 2 → Fin 2 → ℝ} (hp : (twoUnitRelated s hs).toCostGame.IsTotallyMixedNash p)
    (i : Fin 2) :
    p i 0 = (2 - s) / (s + 1) ∧ p i 1 = (2 * s - 1) / (s + 1) := by
  have heq := (twoUnitRelated s hs).eq_of_isTotallyMixedNash (fun _ => zero_lt_one) (by decide) hp
    (isTotallyMixedNash_twoUnitRelated_profile hs hs1 hs2)
  subst heq
  simp

end TwoUnitRelated

section KoutsoupiasPapadimitriouTwoMachine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Koutsoupias–Papadimitriou mixed price of anarchy for two identical machines**
([KoutsoupiasPapadimitriou1999]): for `2` identical machines and any finite set of jobs with
nonnegative weights, every mixed Nash equilibrium `p` satisfies
`expectedMakespan p ≤ (3 / 2) * optMakespan`. -/
theorem IsIdentical.expectedMakespan_le_three_halves_mul_optMakespan
    {G : LoadBalancingGame ι (Fin 2)} (hId : G.IsIdentical) {p : ι → Fin 2 → ℝ}
    (hp : G.toCostGame.IsMixedNash p) :
    G.expectedMakespan p ≤ (3 / 2 : ℝ) * G.optMakespan := by
  have hp0 : ∀ i j, 0 ≤ p i j := fun i j => (hp.1 i).nonneg j
  have hp1 : ∀ i, ∑ j, p i j = 1 := fun i => (hp.1 i).sum_eq_one
  set W : ℝ := ∑ i, G.weight i
  have hW_le : W ≤ 2 * G.optMakespan := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using hId.sum_weight_le_card_mul_optMakespan
  -- For each pure assignment `A`, pick a machine attaining `makespan A`.
  let heaviest : (ι → Fin 2) → Fin 2 := fun A => if G.load A 1 ≤ G.load A 0 then 0 else 1
  have hms_eq : ∀ A : ι → Fin 2, G.makespan A = G.load A (heaviest A) := fun A => by
    refine le_antisymm ((G.makespan_le_iff A).mpr fun j => ?_) (G.load_le_makespan A (heaviest A))
    fin_cases j <;> simp only [heaviest, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      split_ifs <;> linarith
  -- `q i` is the probability that job `i` lands on `heaviest A`.
  let q : ι → ℝ := fun i => ∑ A : ι → Fin 2, productWeight p A * if A i = heaviest A then 1 else 0
  have hq_le1 : ∀ i, q i ≤ 1 := fun i => by
    calc q i ≤ ∑ A : ι → Fin 2, productWeight p A * 1 :=
          sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num)
            (productWeight_nonneg hp0 A)
      _ = 1 := by simp [sum_productWeight hp1]
  have hEM_eq : G.expectedMakespan p = ∑ i, q i * G.weight i := by
    simp only [expectedMakespan, q, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun A _ => ?_
    rw [hms_eq A, G.load_eq_sum_div, hId (heaviest A), div_one, sum_filter, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  by_cases hall : ∀ i, q i ≤ 3 / 4
  · calc G.expectedMakespan p
        = ∑ i, q i * G.weight i := hEM_eq
      _ ≤ ∑ i, (3 / 4 : ℝ) * G.weight i :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hall i) (G.weight_nonneg i)
      _ = (3 / 4 : ℝ) * W := by rw [← mul_sum]
      _ ≤ (3 / 2 : ℝ) * G.optMakespan := by linarith
  · push Not at hall
    obtain ⟨i, hqi⟩ := hall
    -- Mixed NE upper bound on player `i`'s expected cost: `expectedCost p i ≤ (W + w_i) / 2`.
    have hEc_le : G.toCostGame.expectedCost p i ≤ (W + G.weight i) / 2 := by
      have h0 := hp.2 i 0
      have h1 := hp.2 i 1
      rw [G.deviationCost_toCostGame hp1 i 0, hId 0, div_one] at h0
      rw [G.deviationCost_toCostGame hp1 i 1, hId 1, div_one] at h1
      have hsumE : G.expectedLoad p 0 + G.expectedLoad p 1 = W := by
        simpa only [Fin.sum_univ_two, hId 0, hId 1, one_mul] using G.sum_speed_mul_expectedLoad hp1
      have hsumP : p i 0 + p i 1 = 1 := by simpa only [Fin.sum_univ_two] using hp1 i
      have hsumW : (1 - p i 0) * G.weight i + (1 - p i 1) * G.weight i = G.weight i := by
        rw [← add_mul, show 1 - p i 0 + (1 - p i 1) = 1 by linarith, one_mul]
      linarith
    -- Pointwise gap bound: `makespan A - cost i A ≤ (1_{A i ≠ heaviest A}) * (W - 2 * w_i)`.
    have hpt : ∀ A : ι → Fin 2,
        G.makespan A - G.toCostGame.cost i A ≤
          (if A i = heaviest A then (0 : ℝ) else 1) * (W - 2 * G.weight i) := by
      intro A
      by_cases hAi : A i = heaviest A
      · rw [ite_eq_left hAi, zero_mul, hms_eq A]
        change G.load A (heaviest A) - G.load A (A i) ≤ 0
        rw [hAi, sub_self]
      · rw [ite_eq_right hAi, one_mul, hms_eq A]
        change G.load A (heaviest A) - G.load A (A i) ≤ W - 2 * G.weight i
        have htot : G.load A 0 + G.load A 1 = W := by
          simpa only [Fin.sum_univ_two] using hId.sum_load A
        have hsum_loads : G.load A (heaviest A) + G.load A (A i) = W := by
          generalize heaviest A = m at hAi ⊢
          generalize A i = a at hAi ⊢
          fin_cases m <;> fin_cases a <;>
            simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at hAi ⊢ <;>
            first | contradiction | linarith
        have hw_le_load : G.weight i ≤ G.load A (A i) := by
          simpa only [hId (A i), div_one] using G.weight_div_speed_le_load A i
        linarith
    -- Average the pointwise bound under `productWeight p`.
    have hgap : G.expectedMakespan p - G.toCostGame.expectedCost p i ≤
        (1 - q i) * (W - 2 * G.weight i) := by
      rw [expectedMakespan, CostGame.expectedCost_def, ← sum_sub_distrib]
      simp_rw [← mul_sub]
      calc ∑ A : ι → Fin 2, productWeight p A * (G.makespan A - G.toCostGame.cost i A)
          ≤ ∑ A : ι → Fin 2, productWeight p A *
              ((if A i = heaviest A then (0 : ℝ) else 1) * (W - 2 * G.weight i)) :=
            sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hpt A) (productWeight_nonneg hp0 A)
        _ = (∑ A : ι → Fin 2, productWeight p A * if A i = heaviest A then (0 : ℝ) else 1) *
              (W - 2 * G.weight i) := by
            rw [sum_mul]
            exact sum_congr rfl fun A _ => by ring
        _ = (1 - q i) * (W - 2 * G.weight i) := by
            congr 1
            have hcomp : ∀ A : ι → Fin 2,
                productWeight p A * (if A i = heaviest A then (0 : ℝ) else 1) =
                  productWeight p A -
                    productWeight p A * (if A i = heaviest A then (1 : ℝ) else 0) := fun A => by
              split_ifs <;> ring
            simp_rw [hcomp, sum_sub_distrib, sum_productWeight hp1]
            rfl
    nlinarith [hId.weight_le_optMakespan i, hq_le1 i]

/-- **Tightness witness for Koutsoupias–Papadimitriou `3 / 2`** ([KoutsoupiasPapadimitriou1999]):
two unit-weight jobs on two identical machines. -/
@[expose] def kpTwoUnit : LoadBalancingGame (Fin 2) (Fin 2) :=
  LoadBalancingGame.identical (fun _ => 1) (fun _ => zero_le_one)

/-- The uniform mixed strategy profile `(1/2, 1/2)` for `kpTwoUnit`. -/
@[expose] noncomputable def kpTwoUnitUniform : Fin 2 → Fin 2 → ℝ :=
  fun _ _ => 1 / 2

theorem isMixedNash_kpTwoUnitUniform : kpTwoUnit.toCostGame.IsMixedNash kpTwoUnitUniform := by
  rw [kpTwoUnit.isMixedNash_iff]
  refine ⟨fun _ => isMixedStrategy_iff.mpr ⟨fun _ => by norm_num [kpTwoUnitUniform],
      by simp [kpTwoUnitUniform]⟩,
    fun i j _ k => ?_⟩
  simp [expectedLoad, kpTwoUnit, identical, kpTwoUnitUniform]

theorem optMakespan_kpTwoUnit : kpTwoUnit.optMakespan = 1 := by
  have hload_id : ∀ j : Fin 2, kpTwoUnit.load id j = 1 := fun j => by
    rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
    fin_cases j <;> simp [kpTwoUnit, identical]
  refine le_antisymm
    ((kpTwoUnit.optMakespan_le id).trans ((kpTwoUnit.makespan_le_iff id).mpr fun j =>
      (hload_id j).le)) ?_
  simpa [kpTwoUnit, identical] using
    (isIdentical_identical (M := Fin 2) (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => zero_le_one)).weight_le_optMakespan (0 : Fin 2)

/-- The uniform mixed Nash equilibrium on two unit jobs and two identical machines achieves
expected makespan `(3 / 2) * optMakespan` ([KoutsoupiasPapadimitriou1999]). -/
theorem expectedMakespan_kpTwoUnitUniform :
    kpTwoUnit.expectedMakespan kpTwoUnitUniform = (3 / 2 : ℝ) * kpTwoUnit.optMakespan := by
  rw [optMakespan_kpTwoUnit, mul_one, expectedMakespan]
  have hprod : ∀ A : Fin 2 → Fin 2, productWeight kpTwoUnitUniform A = 1 / 4 := fun A => by
    rw [productWeight_def, Fin.prod_univ_two]
    simp only [kpTwoUnitUniform]
    norm_num
  have hms : ∀ A : Fin 2 → Fin 2, kpTwoUnit.makespan A = if A 0 = A 1 then 2 else 1 := fun A => by
    have hl : ∀ j : Fin 2, kpTwoUnit.load A j =
        (if A 0 = j then (1 : ℝ) else 0) + (if A 1 = j then 1 else 0) := fun j => by
      rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
      simp [kpTwoUnit, identical]
    refine le_antisymm ((kpTwoUnit.makespan_le_iff A).mpr fun j => ?_) ?_
    · rw [hl j]
      (by_cases h0 : A 0 = j <;> by_cases h1 : A 1 = j <;> simp only [h0, h1, ↓reduceIte]) <;>
        (try split_ifs) <;> norm_num
    · split_ifs with h
      · calc (2 : ℝ) = kpTwoUnit.load A (A 0) := by
              rw [hl (A 0), ite_eq_left rfl, ite_eq_left h.symm]; norm_num
          _ ≤ kpTwoUnit.makespan A := kpTwoUnit.load_le_makespan A (A 0)
      · calc (1 : ℝ) ≤ kpTwoUnit.load A (A 0) := by
              rw [hl (A 0), ite_eq_left rfl, ite_eq_right (Ne.symm h)]; norm_num
          _ ≤ kpTwoUnit.makespan A := kpTwoUnit.load_le_makespan A (A 0)
  simp_rw [hprod, hms, ← mul_sum]
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, ↓reduceIte, Fin.reduceEq]
  norm_num

end KoutsoupiasPapadimitriouTwoMachine

end Cslib.GameTheory.LoadBalancingGame

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.LoadBalancing.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogDivLogLog
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pure Nash price of anarchy for selfish load balancing

This module proves exact and asymptotic pure Nash price-of-anarchy bounds across the three machine
models of selfish load balancing ([Vocking2007]):

1. **Identical machines** ([FinnHorowitz1979]; [Vocking2007]):
   * Every pure Nash equilibrium `A` on `m ≥ 1` identical machines satisfies
     `makespan A ≤ (2m / (m + 1)) * optMakespan` (`IsIdentical.makespan_le_of_isPureNash`), and
     strictly `< 2 * optMakespan` whenever `0 < optMakespan`.
   * For `m = 2`, this gives `makespan A ≤ (4 / 3) * optMakespan`.
   * The `2m / (m + 1)` bound is **exact for every `m ≥ 1`**: `finnHorowitzTight m` is an explicit
     `2m`-job, `m`-machine identical instance with pure Nash equilibrium `finnHorowitzTightNE m`
     attaining `makespan = (2m / (m + 1)) * optMakespan`.
   * For `3` jobs on `2` identical machines, every pure Nash equilibrium is optimal
     (`IsIdentical.makespan_eq_opt_of_three_jobs_two_machines`, [Vocking2007]).
   * If every job has weight at most `B`, then `makespan A ≤ optMakespan + (1 - 1 / m) * B`
     ([Vocking2007]).
2. **Two uniformly related machines** ([Vocking2007], generalized to arbitrary job
   counts):
   * Every pure Nash equilibrium on `2` uniformly related machines (with any finite number of jobs)
     satisfies `makespan A ≤ ((1 + √5) / 2) * optMakespan`
     (`makespan_le_goldenRatio_mul_optMakespan`).
   * `goldenRatioTight` attains exact equality `((1 + √5) / 2) * optMakespan`.
3. **General uniformly related machines** ([CzumajVocking2002]; [Vocking2007]):
   * Speed-prefix cardinality inequality `(k + 1) * #(L_{k+1}) ≤ #(L_k)`
     (`card_speedPrefix_ge`).
   * Factorial bound: if `(c + 1) * optMakespan ≤ makespan A` (with `0 < optMakespan`), then
     `c! ≤ |M|` (`factorial_le_card_of_makespan_ge`).
   * Explicit `O(log m / log log m)` bound: for `3 ≤ |M|`,
     `makespan A ≤ (4 * log |M| / log (log |M|) + 3) * optMakespan`
     (`makespan_le_log_div_log_log_mul_optMakespan`).
4. **Unrelated machines**:
   * Pure price of anarchy is unbounded even for `2` jobs on `2` machines: for every `K ≥ 1`,
     `unrelatedTight K` has a pure Nash equilibrium with makespan `K * optMakespan`
     (`UnrelatedLoadBalancingGame.exists_isPureNash_makespan_eq_mul_optMakespan`).

## Main results

* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.makespan_le_of_isPureNash` ([FinnHorowitz1979];
  [Vocking2007])
* `Cslib.GameTheory.LoadBalancingGame.makespan_finnHorowitzTightNE` ([Vocking2007])
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.makespan_eq_opt_of_three_jobs_two_machines`
  ([Vocking2007])
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.makespan_le_optMakespan_add_of_weight_le`
  ([Vocking2007])
* `Cslib.GameTheory.LoadBalancingGame.makespan_le_goldenRatio_mul_optMakespan`,
  `Cslib.GameTheory.LoadBalancingGame.makespan_goldenRatioTightNE` ([Vocking2007])
* `Cslib.GameTheory.LoadBalancingGame.factorial_le_card_of_makespan_ge`,
  `Cslib.GameTheory.LoadBalancingGame.makespan_le_log_div_log_log_mul_optMakespan`
  ([CzumajVocking2002]; [Vocking2007])
* `Cslib.GameTheory.UnrelatedLoadBalancingGame.exists_isPureNash_makespan_eq_mul_optMakespan`

## References

* [CzumajVocking2002]
* [FinnHorowitz1979]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory

open Finset

namespace LoadBalancingGame

section IdenticalPurePoA

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M]

private theorem IsIdentical.card_mul_load_sub_le_card_mul_optMakespan
    {G : LoadBalancingGame ι M} (hId : G.IsIdentical) {A : ι → M}
    (hA : G.toCostGame.IsPureNash A) {i₀ : ι} {jstar : M} (hAi₀ : A i₀ = jstar) :
    (Fintype.card M : ℝ) * G.load A jstar - ((Fintype.card M : ℝ) - 1) * G.weight i₀ ≤
      (Fintype.card M : ℝ) * G.optMakespan := by
  have hsum_ge : (Fintype.card M : ℝ) * G.load A jstar -
      ((Fintype.card M : ℝ) - 1) * G.weight i₀ ≤ ∑ k, G.load A k := by
    rw [← add_sum_erase _ _ (mem_univ jstar)]
    have hrest : ((Fintype.card M : ℝ) - 1) * (G.load A jstar - G.weight i₀) ≤
        ∑ k ∈ univ.erase jstar, G.load A k := by
      calc ((Fintype.card M : ℝ) - 1) * (G.load A jstar - G.weight i₀)
          = ∑ _k ∈ univ.erase jstar, (G.load A jstar - G.weight i₀) := by
            rw [sum_const, card_erase_of_mem (mem_univ jstar), card_univ, nsmul_eq_mul,
              Nat.cast_sub Fintype.card_pos, Nat.cast_one]
        _ ≤ ∑ k ∈ univ.erase jstar, G.load A k := by
            refine sum_le_sum fun k hk => ?_
            have hne : k ≠ A i₀ := by
              rw [hAi₀]
              exact ne_of_mem_erase hk
            have hne_ineq := (G.isPureNash_iff A).mp hA i₀ k hne
            rw [hAi₀, hId k, div_one] at hne_ineq
            linarith
    linarith
  refine hsum_ge.trans ?_
  rw [hId.sum_load A]
  exact hId.sum_weight_le_card_mul_optMakespan

/-- **Identical-machine pure price of anarchy** ([FinnHorowitz1979]; [Vocking2007]):
every pure Nash equilibrium `A` on `m = |M| ≥ 1` identical machines satisfies
`makespan A ≤ (2 * m / (m + 1)) * optMakespan` (equivalently `(2 - 2 / (m + 1)) * optMakespan`).
-/
theorem IsIdentical.makespan_le_of_isPureNash {G : LoadBalancingGame ι M} (hId : G.IsIdentical)
    {A : ι → M} (hA : G.toCostGame.IsPureNash A) :
    G.makespan A ≤
      (2 * (Fintype.card M : ℝ) / ((Fintype.card M : ℝ) + 1)) * G.optMakespan := by
  have hm_pos : (0 : ℝ) < Fintype.card M := Nat.cast_pos.mpr Fintype.card_pos
  have hm_ge1 : (1 : ℝ) ≤ Fintype.card M := Nat.one_le_cast.mpr Fintype.card_pos
  have hratio_ge1 : (1 : ℝ) ≤ 2 * (Fintype.card M : ℝ) / ((Fintype.card M : ℝ) + 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
  set S : Finset ι := univ.filter fun i => A i = jstar
  have hload_S : G.load A jstar = ∑ i ∈ S, G.weight i := by
    rw [G.load_eq_sum_div, hId jstar, div_one]
  by_cases hcard : #S ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · rw [card_eq_zero] at h0
      have hms0 : G.makespan A = 0 := by rw [← hjstar, hload_S, h0, sum_empty]
      rw [hms0]
      exact mul_nonneg (by positivity) G.optMakespan_nonneg
    · obtain ⟨i₀, hi₀⟩ := card_eq_one.mp h1
      have hms_eq : G.makespan A = G.weight i₀ := by
        rw [← hjstar, hload_S, hi₀, sum_singleton]
      rw [hms_eq]
      calc G.weight i₀ ≤ G.optMakespan := hId.weight_le_optMakespan i₀
        _ = 1 * G.optMakespan := (one_mul _).symm
        _ ≤ (2 * (Fintype.card M : ℝ) / ((Fintype.card M : ℝ) + 1)) * G.optMakespan :=
            mul_le_mul_of_nonneg_right hratio_ge1 G.optMakespan_nonneg
  · have hcard2 : 2 ≤ #S := by omega
    have hSne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨i₀, hi₀S, hi₀min⟩ := exists_min_image S G.weight hSne
    have hAi₀ : A i₀ = jstar := (mem_filter.mp hi₀S).2
    -- Since `#S ≥ 2` and `i₀` has minimum weight on `jstar`, `2 * weight i₀ ≤ load A jstar`.
    have h2w : 2 * G.weight i₀ ≤ G.load A jstar := by
      rw [hload_S]
      calc 2 * G.weight i₀ ≤ (#S : ℝ) * G.weight i₀ := by
            have : (2 : ℝ) ≤ #S := by exact_mod_cast hcard2
            nlinarith [G.weight_nonneg i₀]
        _ = ∑ _i ∈ S, G.weight i₀ := by simp
        _ ≤ ∑ i ∈ S, G.weight i := sum_le_sum fun i hi => hi₀min i hi
    have hbound := hId.card_mul_load_sub_le_card_mul_optMakespan hA hAi₀
    rw [← hjstar, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

/-- Strict `< 2` bound for arbitrary `m` identical machines when `optMakespan > 0`. -/
theorem IsIdentical.makespan_lt_two_mul_of_isPureNash {G : LoadBalancingGame ι M}
    (hId : G.IsIdentical) {A : ι → M} (hA : G.toCostGame.IsPureNash A)
    (hopt : 0 < G.optMakespan) :
    G.makespan A < 2 * G.optMakespan := by
  have hm_pos : (0 : ℝ) < Fintype.card M := Nat.cast_pos.mpr Fintype.card_pos
  have hlt : 2 * (Fintype.card M : ℝ) / ((Fintype.card M : ℝ) + 1) < 2 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  exact (hId.makespan_le_of_isPureNash hA).trans_lt (mul_lt_mul_of_pos_right hlt hopt)

/-- Special case `m = 2` identical machines: `makespan A ≤ (4 / 3) * optMakespan`. -/
theorem IsIdentical.makespan_le_four_thirds_of_isPureNash {G : LoadBalancingGame ι (Fin 2)}
    (hId : G.IsIdentical) {A : ι → Fin 2} (hA : G.toCostGame.IsPureNash A) :
    G.makespan A ≤ 4 / 3 * G.optMakespan := by
  have h := hId.makespan_le_of_isPureNash hA
  norm_num [Fintype.card_fin] at h
  exact h

/-- **Tightness witness family for Finn–Horowitz** ([FinnHorowitz1979]; [Vocking2007]):
for every `m ≥ 1`, `2m` jobs indexed by `Bool × Fin m` on `m` identical machines.
Machine `0` receives two jobs of weight `m` in the Nash equilibrium, while each machine `k ≠ 0`
receives jobs of weights `k` and `m - k`. -/
@[expose] def finnHorowitzTight (m : ℕ) : LoadBalancingGame (Bool × Fin m) (Fin m) :=
  LoadBalancingGame.identical
    (fun p => if p.2.val = 0 then (m : ℝ) else if p.1 then ((m - p.2.val : ℕ) : ℝ) else p.2.val)
    (fun p => by split_ifs <;> positivity)

/-- The worst-case pure Nash equilibrium on `finnHorowitzTight m`: job `(b, k)` goes to machine
`k`. -/
@[expose] def finnHorowitzTightNE (m : ℕ) : Bool × Fin m → Fin m :=
  fun p => p.2

private theorem isIdentical_finnHorowitzTight (m : ℕ) : (finnHorowitzTight m).IsIdentical :=
  fun _ => rfl

private theorem load_finnHorowitzTightNE (m : ℕ) (j : Fin m) :
    (finnHorowitzTight m).load (finnHorowitzTightNE m) j =
      if j.val = 0 then 2 * (m : ℝ) else (m : ℝ) := by
  rw [LoadBalancingGame.load_eq_sum_div]
  simp only [finnHorowitzTight, identical, div_one]
  have hfilt : (univ.filter fun p : Bool × Fin m => finnHorowitzTightNE m p = j) =
      {(false, j), (true, j)} := by
    ext ⟨b, k⟩
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and, Prod.mk.injEq, finnHorowitzTightNE]
    cases b <;> simp
  change ∑ p ∈ (univ.filter fun p : Bool × Fin m => finnHorowitzTightNE m p = j),
    (if p.2.val = 0 then (m : ℝ)
     else if p.1 then ((m - p.2.val : ℕ) : ℝ) else p.2.val) = _
  rw [hfilt, sum_pair (by simp)]
  dsimp only
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte]; ring
  · simp only [hj, ↓reduceIte, Bool.false_eq_true, Nat.cast_sub j.isLt.le]; ring

theorem isPureNash_finnHorowitzTightNE (m : ℕ) :
    (finnHorowitzTight m).toCostGame.IsPureNash (finnHorowitzTightNE m) := by
  rw [(finnHorowitzTight m).isPureNash_iff]
  intro ⟨b, j⟩ k hk
  rw [finnHorowitzTightNE] at hk ⊢
  rw [load_finnHorowitzTightNE m j, load_finnHorowitzTightNE m k]
  simp only [finnHorowitzTight, identical, div_one]
  by_cases hj : j.val = 0
  · have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext (h.trans hj.symm))
    simp only [hj, hk0, ↓reduceIte]
    linarith
  · have hnonneg : (0 : ℝ) ≤ if b then ((m - j.val : ℕ) : ℝ) else (j.val : ℝ) := by
      split_ifs <;> positivity
    by_cases hk0 : k.val = 0
    · simp only [hj, hk0, ↓reduceIte]
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · simp only [hj, hk0, ↓reduceIte]
      linarith

theorem makespan_finnHorowitzTightNE (m : ℕ) [NeZero m] :
    (finnHorowitzTight m).makespan (finnHorowitzTightNE m) = 2 * (m : ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [(finnHorowitzTight m).makespan_le_iff]
    intro j
    rw [load_finnHorowitzTightNE m j]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) m]
  · calc 2 * (m : ℝ) = (finnHorowitzTight m).load (finnHorowitzTightNE m) 0 := by
          simp only [load_finnHorowitzTightNE, Fin.val_zero, ↓reduceIte]
      _ ≤ (finnHorowitzTight m).makespan (finnHorowitzTightNE m) :=
          (finnHorowitzTight m).load_le_makespan _ 0

theorem optMakespan_finnHorowitzTight (m : ℕ) [NeZero m] :
    (finnHorowitzTight m).optMakespan = (m : ℝ) + 1 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let Aopt : Bool × Fin m → Fin m := fun p =>
    if p.1 then ⟨(p.2.val + 1) % m, Nat.mod_lt _ hm_pos⟩ else p.2
  have hload_opt : ∀ j : Fin m, (finnHorowitzTight m).load Aopt j = (m : ℝ) + 1 := by
    intro j
    let prev : Fin m := ⟨(j.val + m - 1) % m, Nat.mod_lt _ hm_pos⟩
    have hprev_succ : (prev.val + 1) % m = j.val := by
      simp only [prev]
      by_cases hj : j.val = 0
      · rw [hj, zero_add]
        have : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
        rw [this, Nat.sub_add_cancel hm_pos, Nat.mod_self]
      · have h1 : (j.val + m - 1) % m = j.val - 1 := by
          have : j.val + m - 1 = (j.val - 1) + m := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt j.isLt]
    have hfilt : (univ.filter fun p : Bool × Fin m => Aopt p = j) =
        {(false, j), (true, prev)} := by
      ext ⟨b, k⟩
      cases b with
      | false => simp [Aopt]
      | true =>
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq,
          Bool.true_eq_false, false_and, true_and, false_or, Aopt, ↓reduceIte]
        constructor
        · intro hk
          have hval : (k.val + 1) % m = j.val := congrArg Fin.val hk
          apply Fin.ext
          simp only [prev]
          by_cases hk1 : k.val + 1 < m
          · rw [Nat.mod_eq_of_lt hk1] at hval
            have : j.val + m - 1 = k.val + m := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
          · have hkeq : k.val + 1 = m := by omega
            rw [hkeq, Nat.mod_self] at hval
            rw [← hval, zero_add, Nat.mod_eq_of_lt (by omega)]
            omega
        · rintro rfl
          exact Fin.ext hprev_succ
    rw [LoadBalancingGame.load_eq_sum_div]
    simp only [finnHorowitzTight, identical, div_one]
    change ∑ p ∈ univ.filter (fun p : Bool × Fin m => Aopt p = j),
      (if p.2.val = 0 then (m : ℝ)
       else if p.1 then ((m - p.2.val : ℕ) : ℝ) else p.2.val) = _
    rw [hfilt, sum_pair (by simp)]
    dsimp only
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hm1 : m = 1
    · subst hm1
      have hj0 : j.val = 0 := by omega
      have hp0 : prev.val = 0 := by omega
      simp only [hj0, hp0, ↓reduceIte, Nat.cast_one]
    · by_cases hj0 : j.val = 0
      · have hp : prev.val = m - 1 := by
          simp only [prev, hj0, zero_add]
          exact Nat.mod_eq_of_lt (by omega)
        have hpne : prev.val ≠ 0 := by omega
        rw [ite_eq_left hj0, ite_eq_right hpne, hp]
        have : m - (m - 1) = 1 := by omega
        rw [this, Nat.cast_one]
      · by_cases hj1 : j.val = 1
        · have hp : prev.val = 0 := by
            simp only [prev, hj1]
            have : 1 + m - 1 = m := by omega
            rw [this, Nat.mod_self]
          rw [ite_eq_right hj0, ite_eq_left hp, hj1, Nat.cast_one]
          ring
        · have hp : prev.val = j.val - 1 := by
            simp only [prev]
            have : j.val + m - 1 = (j.val - 1) + m := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hpne : prev.val ≠ 0 := by omega
          rw [ite_eq_right hj0, ite_eq_right hpne, hp]
          have hsub : m - (j.val - 1) = m + 1 - j.val := by omega
          rw [hsub, Nat.cast_sub (by omega)]
          push_cast
          ring
  have hsum : ∑ p : Bool × Fin m, (finnHorowitzTight m).weight p = (m : ℝ) * ((m : ℝ) + 1) := by
    rw [← (isIdentical_finnHorowitzTight m).sum_load Aopt]
    simp only [hload_opt, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_antisymm ?_ ?_
  · calc (finnHorowitzTight m).optMakespan
        ≤ (finnHorowitzTight m).makespan Aopt := (finnHorowitzTight m).optMakespan_le Aopt
      _ ≤ (m : ℝ) + 1 := ((finnHorowitzTight m).makespan_le_iff Aopt).mpr fun j => (hload_opt j).le
  · have hvol := (isIdentical_finnHorowitzTight m).sum_weight_le_card_mul_optMakespan
    rw [Fintype.card_fin, hsum] at hvol
    have hm_pos' : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
    nlinarith

/-- **Tightness of the `2m / (m + 1)` pure price of anarchy** ([FinnHorowitz1979]; [Vocking2007]):
for every `m ≥ 1`, `finnHorowitzTightNE m` attains exact equality. -/
theorem makespan_finnHorowitzTightNE_eq_ratio (m : ℕ) [NeZero m] :
    (finnHorowitzTight m).makespan (finnHorowitzTightNE m) =
      (2 * (m : ℝ) / ((m : ℝ) + 1)) * (finnHorowitzTight m).optMakespan := by
  rw [makespan_finnHorowitzTightNE, optMakespan_finnHorowitzTight]
  have hne : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- **Three jobs on two identical machines** ([Vocking2007]): every pure Nash
equilibrium of `3` jobs on `2` identical machines is makespan-optimal. -/
theorem IsIdentical.makespan_eq_opt_of_three_jobs_two_machines
    {G : LoadBalancingGame (Fin 3) (Fin 2)} (hId : G.IsIdentical) {A : Fin 3 → Fin 2}
    (hA : G.toCostGame.IsPureNash A) :
    G.makespan A = G.optMakespan := by
  refine le_antisymm ?_ (G.optMakespan_le A)
  obtain ⟨τ, hτ⟩ := G.exists_makespan_eq_optMakespan
  rw [← hτ]
  have hpair_le : ∀ {i₁ i₂ : Fin 3}, i₁ ≠ i₂ → τ i₁ = τ i₂ →
      G.weight i₁ + G.weight i₂ ≤ G.makespan τ := by
    intro i₁ i₂ hne hsame
    have hsub : ({i₁, i₂} : Finset (Fin 3)) ⊆ univ.filter fun r => τ r = τ i₁ := by
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      simp only [mem_filter, mem_univ, true_and]
      rcases hr with rfl | rfl
      · rfl
      · exact hsame.symm
    calc G.weight i₁ + G.weight i₂
        = ∑ r ∈ ({i₁, i₂} : Finset (Fin 3)), G.weight r := (sum_pair hne).symm
      _ ≤ ∑ r with τ r = τ i₁, G.weight r :=
          sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => G.weight_nonneg r
      _ = G.load τ (τ i₁) := by rw [G.load_eq_sum_div, hId (τ i₁), div_one]
      _ ≤ G.makespan τ := G.load_le_makespan τ (τ i₁)
  have hw_le : ∀ i : Fin 3, G.weight i ≤ G.makespan τ := fun i => by
    simpa only [hId (τ i), div_one] using G.weight_div_speed_le_makespan τ i
  obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
  let jother : Fin 2 := 1 - jstar
  have hjne : jother ≠ jstar := by fin_cases jstar <;> decide
  set S : Finset (Fin 3) := univ.filter fun i => A i = jstar
  have hload_S : G.load A jstar = ∑ i ∈ S, G.weight i := by
    rw [G.load_eq_sum_div, hId jstar, div_one]
  rw [← hjstar]
  have hcard_le3 : #S ≤ 3 := (card_le_univ S).trans (by simp)
  by_cases hcard1 : #S ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard1 with h0 | h1
    · rw [card_eq_zero] at h0
      rw [hload_S, h0, sum_empty]
      exact G.makespan_nonneg τ
    · obtain ⟨i₀, hi₀⟩ := card_eq_one.mp h1
      rw [hload_S, hi₀, sum_singleton]
      exact hw_le i₀
  · by_cases hcard3 : #S = 3
    · have hSuniv : S = univ := eq_univ_of_card S (by simpa using hcard3)
      have hA_all : ∀ i : Fin 3, A i = jstar := fun i => by
        have : i ∈ S := hSuniv ▸ mem_univ i
        exact (mem_filter.mp this).2
      have hload_other : G.load A jother = 0 := by
        rw [G.load_eq_sum_div, hId jother, div_one]
        have hempty : (univ.filter fun i : Fin 3 => A i = jother) = ∅ := by
          ext i
          simp [hA_all i, hjne.symm]
        rw [hempty, sum_empty]
      have hNE := (G.isPureNash_iff A).mp hA 0 jother (by rw [hA_all 0]; exact hjne)
      rw [hA_all 0, hload_other, hId jother, div_one, zero_add] at hNE
      exact hNE.trans (hw_le 0)
    · have hcard2 : #S = 2 := by omega
      obtain ⟨i₁, i₂, hi₁₂, hS_eq⟩ := card_eq_two.mp hcard2
      -- Find the unique third job `i₃ ∉ S`, which must sit on `jother`.
      have hcard_comp : #(univ \ S) = 1 := by
        rw [card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin, hcard2]
      obtain ⟨i₃, hi₃_eq⟩ := card_eq_one.mp hcard_comp
      have hi₃_notS : i₃ ∉ S := by
        have : i₃ ∈ univ \ S := by rw [hi₃_eq]; exact mem_singleton_self i₃
        exact (mem_sdiff.mp this).2
      have hAi₁ : A i₁ = jstar :=
        (mem_filter.mp (show i₁ ∈ S by rw [hS_eq]; exact mem_insert_self i₁ {i₂})).2
      have hAi₂ : A i₂ = jstar :=
        (mem_filter.mp
          (show i₂ ∈ S by rw [hS_eq]; exact mem_insert_of_mem (mem_singleton_self i₂))).2
      have hAi₃ : A i₃ = jother := by
        have hne_js : A i₃ ≠ jstar := fun h => hi₃_notS (mem_filter.mpr ⟨mem_univ i₃, h⟩)
        have hpair : (univ : Finset (Fin 2)) = {jstar, jother} := by fin_cases jstar <;> decide
        have hmem : A i₃ ∈ ({jstar, jother} : Finset (Fin 2)) := hpair ▸ mem_univ (A i₃)
        simp only [mem_insert, mem_singleton] at hmem
        exact hmem.resolve_left hne_js
      have hload_jstar : G.load A jstar = G.weight i₁ + G.weight i₂ := by
        rw [hload_S, hS_eq, sum_pair hi₁₂]
      have hload_other : G.load A jother = G.weight i₃ := by
        rw [G.load_eq_sum_div, hId jother, div_one]
        have hfilt : (univ.filter fun i : Fin 3 => A i = jother) = {i₃} := by
          rw [← hi₃_eq]
          ext i
          simp only [mem_filter, mem_univ, true_and, mem_sdiff, S]
          constructor
          · intro hi; exact fun h => hjne (hi.symm.trans h)
          · intro hne_js
            have hpair : (univ : Finset (Fin 2)) = {jstar, jother} := by fin_cases jstar <;> decide
            have hmem : A i ∈ ({jstar, jother} : Finset (Fin 2)) := hpair ▸ mem_univ (A i)
            simp only [mem_insert, mem_singleton] at hmem
            exact hmem.resolve_left hne_js
        rw [hfilt, sum_singleton]
      have hNE₁ := (G.isPureNash_iff A).mp hA i₁ jother (by rw [hAi₁]; exact hjne)
      have hNE₂ := (G.isPureNash_iff A).mp hA i₂ jother (by rw [hAi₂]; exact hjne)
      rw [hAi₁, hload_jstar, hload_other, hId jother, div_one] at hNE₁
      rw [hAi₂, hload_jstar, hload_other, hId jother, div_one] at hNE₂
      have hi₁₃ : i₁ ≠ i₃ := fun h => hi₃_notS (h ▸ hS_eq ▸ mem_insert_self i₁ {i₂})
      have hi₂₃ : i₂ ≠ i₃ := fun h =>
        hi₃_notS (h ▸ hS_eq ▸ mem_insert_of_mem (mem_singleton_self i₂))
      have hpig : τ i₁ = τ i₂ ∨ τ i₁ = τ i₃ ∨ τ i₂ = τ i₃ := by
        rcases (eq_or_ne (τ i₁) 0).imp_right (Fin.eq_one_of_ne_zero _) with h1 | h1 <;>
          rcases (eq_or_ne (τ i₂) 0).imp_right (Fin.eq_one_of_ne_zero _) with h2 | h2 <;>
          rcases (eq_or_ne (τ i₃) 0).imp_right (Fin.eq_one_of_ne_zero _) with h3 | h3 <;>
          simp [h1, h2, h3]
      rw [hload_jstar]
      rcases hpig with h | h | h
      · exact hpair_le hi₁₂ h
      · linarith [hpair_le hi₁₃ h]
      · linarith [hpair_le hi₂₃ h]

/-- **Small-job pure Nash bound on identical machines** ([Vocking2007]): if
every job has weight at most `B`, then every pure Nash equilibrium `A` satisfies
`makespan A ≤ optMakespan + (1 - 1 / |M|) * B`. In particular, if `weight i ≤ α * optMakespan`
with `0 < α` and `0 < optMakespan`, then `makespan A < (1 + α) * optMakespan`. -/
theorem IsIdentical.makespan_le_optMakespan_add_of_weight_le {G : LoadBalancingGame ι M}
    (hId : G.IsIdentical) {A : ι → M} (hA : G.toCostGame.IsPureNash A) {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ i, G.weight i ≤ B) :
    G.makespan A ≤ G.optMakespan + (1 - 1 / (Fintype.card M : ℝ)) * B := by
  have hm_pos : (0 : ℝ) < Fintype.card M := Nat.cast_pos.mpr Fintype.card_pos
  have hm_ge1 : (1 : ℝ) ≤ Fintype.card M := Nat.one_le_cast.mpr Fintype.card_pos
  obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
  set S : Finset ι := univ.filter fun i => A i = jstar
  by_cases hSne : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hSne
    have hAi₀ : A i₀ = jstar := (mem_filter.mp hi₀).2
    have hbound := hId.card_mul_load_sub_le_card_mul_optMakespan hA hAi₀
    have hmul : (Fintype.card M : ℝ) * G.makespan A ≤
        (Fintype.card M : ℝ) * G.optMakespan + ((Fintype.card M : ℝ) - 1) * B := by
      rw [← hjstar]
      nlinarith [hw i₀]
    have heq : (Fintype.card M : ℝ) * (G.optMakespan + (1 - 1 / (Fintype.card M : ℝ)) * B) =
        (Fintype.card M : ℝ) * G.optMakespan + ((Fintype.card M : ℝ) - 1) * B := by
      field_simp
    nlinarith
  · rw [not_nonempty_iff_eq_empty] at hSne
    have hms0 : G.makespan A = 0 := by
      rw [← hjstar, G.load_eq_sum_div, hId jstar, div_one]
      change ∑ i ∈ S, G.weight i = 0
      rw [hSne, sum_empty]
    rw [hms0]
    have hcoef : 0 ≤ 1 - 1 / (Fintype.card M : ℝ) := by
      rw [sub_nonneg, div_le_one hm_pos]
      exact hm_ge1
    linarith [G.optMakespan_nonneg, mul_nonneg hcoef hB]

end IdenticalPurePoA

section TwoRelatedGoldenRatio

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Two uniformly related machines: golden-ratio pure price of anarchy** ([Vocking2007], proved
here for an arbitrary finite number of jobs): every pure Nash equilibrium
`A` on `2` uniformly related machines satisfies
`makespan A ≤ ((1 + √5) / 2) * optMakespan`. -/
theorem makespan_le_goldenRatio_mul_optMakespan (G : LoadBalancingGame ι (Fin 2)) {A : ι → Fin 2}
    (hA : G.toCostGame.IsPureNash A) :
    G.makespan A ≤ ((1 + √5) / 2) * G.optMakespan := by
  set φ : ℝ := (1 + √5) / 2
  have hsq5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt5_gt : (2 : ℝ) < √5 := by
    have : (2 : ℝ) ^ 2 < (√5) ^ 2 := by rw [hsq5]; norm_num
    nlinarith [Real.sqrt_nonneg 5]
  have hφ_gt : (3 / 2 : ℝ) < φ := by simp only [φ]; linarith
  have hφ_sq : φ ^ 2 = φ + 1 := by
    simp only [φ]
    nlinarith [hsq5]
  obtain ⟨Aopt, hAopt⟩ := G.exists_makespan_eq_optMakespan
  obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
  let jother : Fin 2 := 1 - jstar
  have hjne : jother ≠ jstar := by fin_cases jstar <;> decide
  have hpair : (univ : Finset (Fin 2)) = {jstar, jother} := by
    fin_cases jstar <;> decide
  set s : ℝ := G.speed jstar
  set t : ℝ := G.speed jother
  have hs : 0 < s := G.speed_pos jstar
  have ht : 0 < t := G.speed_pos jother
  have hvol : s * G.load A jstar + t * G.load A jother ≤ (s + t) * G.optMakespan := by
    have h1 := G.sum_speed_mul_load A
    have h2 := G.sum_weight_le_sum_speed_mul_optMakespan
    rw [hpair, sum_pair hjne.symm] at h1 h2
    linarith
  set S : Finset ι := univ.filter fun i => A i = jstar
  have hload_S : s * G.load A jstar = ∑ i ∈ S, G.weight i := G.speed_mul_load A jstar
  have hopt_nn : 0 ≤ G.optMakespan := G.optMakespan_nonneg
  rw [← hjstar]
  by_cases hcard : #S ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · rw [card_eq_zero] at h0
      have h0' : s * G.load A jstar = 0 := by rw [hload_S, h0, sum_empty]
      have hl0 : G.load A jstar = 0 := (mul_eq_zero.mp h0').resolve_left hs.ne'
      rw [hl0]
      nlinarith
    · obtain ⟨i₀, hi₀⟩ := card_eq_one.mp h1
      have hAi₀ : A i₀ = jstar := by
        have : i₀ ∈ S := by rw [hi₀]; exact mem_singleton_self i₀
        exact (mem_filter.mp this).2
      have hwi₀ : G.weight i₀ = s * G.load A jstar := by
        rw [hload_S, hi₀, sum_singleton]
      by_cases hopt_i : Aopt i₀ = jstar
      · have hle : G.weight i₀ / s ≤ G.optMakespan := by
          simp only [s]
          rw [← hAopt, ← hopt_i]
          exact G.weight_div_speed_le_makespan Aopt i₀
        have hl_le : G.load A jstar ≤ G.optMakespan := by
          rw [hwi₀, mul_div_cancel_left₀ _ hs.ne'] at hle
          exact hle
        nlinarith
      · have hopt_other : Aopt i₀ = jother := by
          have : Aopt i₀ ∈ ({jstar, jother} : Finset (Fin 2)) := by rw [← hpair]; exact mem_univ _
          simp only [mem_insert, mem_singleton] at this
          exact this.resolve_left hopt_i
        have hle_t : G.weight i₀ / t ≤ G.optMakespan := by
          simp only [t]
          rw [← hAopt, ← hopt_other]
          exact G.weight_div_speed_le_makespan Aopt i₀
        have hbound1 : s * G.load A jstar ≤ t * G.optMakespan := by
          have := (div_le_iff₀ ht).mp hle_t
          linarith
        -- Pure NE for `i₀` moving to `jother`: `load A jstar ≤ load A jother + weight i₀ / t`.
        have hNE := (G.isPureNash_iff A).mp hA i₀ jother (by rw [hAi₀]; exact hjne)
        rw [hAi₀, hwi₀] at hNE
        have hNE' : t * G.load A jstar ≤ t * G.load A jother + s * G.load A jstar := by
          have := mul_le_mul_of_nonneg_left hNE ht.le
          rw [mul_add, mul_div_cancel₀ _ ht.ne'] at this
          linarith
        have hbound2 : t * G.load A jstar ≤ (s + t) * G.optMakespan := by linarith
        by_cases hratio : t ≤ φ * s
        · have : s * G.load A jstar ≤ s * (φ * G.optMakespan) := by nlinarith
          nlinarith
        · push Not at hratio
          have hφ_inv : s + t ≤ φ * t := by nlinarith
          have : t * G.load A jstar ≤ t * (φ * G.optMakespan) := by nlinarith
          nlinarith
  · -- At least 2 jobs on `jstar`: makespan is at most `(3/2) * optMakespan < φ * optMakespan`.
    have hcard2 : 2 ≤ #S := by omega
    have hSne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨i₀, hi₀S, hi₀min⟩ := exists_min_image S G.weight hSne
    have hAi₀ : A i₀ = jstar := (mem_filter.mp hi₀S).2
    have h2w : 2 * G.weight i₀ ≤ s * G.load A jstar := by
      rw [hload_S]
      calc 2 * G.weight i₀ ≤ (#S : ℝ) * G.weight i₀ := by
            have : (2 : ℝ) ≤ #S := by exact_mod_cast hcard2
            nlinarith [G.weight_nonneg i₀]
        _ = ∑ _i ∈ S, G.weight i₀ := by simp
        _ ≤ ∑ i ∈ S, G.weight i := sum_le_sum fun i hi => hi₀min i hi
    have hNE := (G.isPureNash_iff A).mp hA i₀ jother (by rw [hAi₀]; exact hjne)
    rw [hAi₀] at hNE
    have hNE' : t * G.load A jstar ≤ t * G.load A jother + G.weight i₀ := by
      have := mul_le_mul_of_nonneg_left hNE ht.le
      rw [mul_add, mul_div_cancel₀ _ ht.ne'] at this
      linarith
    have hbound_small : s * G.load A jstar ≤ (s + t) * G.optMakespan := by
      nlinarith [G.load_nonneg A jother]
    have hbound_large : (s + 2 * t) * G.load A jstar ≤ 2 * (s + t) * G.optMakespan := by
      linarith
    have hthree_halves : G.load A jstar ≤ (3 / 2 : ℝ) * G.optMakespan := by
      by_cases hst : 2 * t ≤ s
      · nlinarith
      · nlinarith
    nlinarith

/-- **Golden-ratio tightness witness** ([Vocking2007]): two jobs of weights
`1` and `φ = (1 + √5) / 2` on two machines of speeds `1` and `φ`. -/
@[expose] noncomputable def goldenRatioTight : LoadBalancingGame (Fin 2) (Fin 2) where
  weight := ![1, (1 + √5) / 2]
  speed := ![1, (1 + √5) / 2]
  weight_nonneg i := by
    rcases (eq_or_ne i 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl
    · simp only [Matrix.cons_val_zero]; exact zero_le_one
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; positivity
  speed_pos j := by
    rcases (eq_or_ne j 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl
    · simp only [Matrix.cons_val_zero]; exact zero_lt_one
    · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; positivity

/-- The worst-case pure Nash equilibrium on `goldenRatioTight`: the heavy job (`1`) sits on the
slow machine (`0`), and the light job (`0`) sits on the fast machine (`1`). -/
@[expose] def goldenRatioTightNE : Fin 2 → Fin 2 := ![1, 0]

theorem isPureNash_goldenRatioTightNE :
    goldenRatioTight.toCostGame.IsPureNash goldenRatioTightNE := by
  have hsq5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hφ_pos : (0 : ℝ) < (1 + √5) / 2 := by positivity
  have hload0 : goldenRatioTight.load goldenRatioTightNE 0 = (1 + √5) / 2 := by
    rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
    simp [goldenRatioTight, goldenRatioTightNE]
  have hload1 : goldenRatioTight.load goldenRatioTightNE 1 = 1 / ((1 + √5) / 2) := by
    rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
    simp [goldenRatioTight, goldenRatioTightNE]
  rw [goldenRatioTight.isPureNash_iff]
  intro i k hk
  rcases (eq_or_ne i 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl <;>
    rcases (eq_or_ne k 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl
  · have hne0 : goldenRatioTightNE 0 = 1 := rfl
    rw [hne0, hload1, hload0]
    simp only [goldenRatioTight, Matrix.cons_val_zero, div_one]
    rw [div_le_iff₀ hφ_pos]
    nlinarith [Real.sqrt_nonneg 5]
  · exact absurd rfl hk
  · exact absurd rfl hk
  · have hne1 : goldenRatioTightNE 1 = 0 := rfl
    rw [hne1, hload0, hload1]
    simp only [goldenRatioTight, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [div_self hφ_pos.ne']
    have : 1 / ((1 + √5) / 2) + 1 = (1 + √5) / 2 := by
      field_simp
      nlinarith [hsq5]
    linarith

theorem optMakespan_goldenRatioTight : goldenRatioTight.optMakespan = 1 := by
  have hφ_pos : (0 : ℝ) < (1 + √5) / 2 := by positivity
  have hload_id : ∀ j : Fin 2, goldenRatioTight.load id j = 1 := fun j => by
    rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
    rcases (eq_or_ne j 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl <;>
      simp [goldenRatioTight, div_self hφ_pos.ne']
  refine le_antisymm ?_ ?_
  · exact (goldenRatioTight.optMakespan_le id).trans
      ((goldenRatioTight.makespan_le_iff id).mpr fun j => (hload_id j).le)
  · have hvol := goldenRatioTight.sum_weight_le_sum_speed_mul_optMakespan
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at hvol
    change 1 + (1 + √5) / 2 ≤ (1 + (1 + √5) / 2) * goldenRatioTight.optMakespan at hvol
    nlinarith

theorem makespan_goldenRatioTightNE :
    goldenRatioTight.makespan goldenRatioTightNE =
      ((1 + √5) / 2) * goldenRatioTight.optMakespan := by
  have hφ_pos : (0 : ℝ) < (1 + √5) / 2 := by positivity
  have hφ_ge1 : (1 : ℝ) ≤ (1 + √5) / 2 := by
    have : (1 : ℝ) ≤ √5 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hload0 : goldenRatioTight.load goldenRatioTightNE 0 = (1 + √5) / 2 := by
    rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
    simp [goldenRatioTight, goldenRatioTightNE]
  have hload1 : goldenRatioTight.load goldenRatioTightNE 1 = 1 / ((1 + √5) / 2) := by
    rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
    simp [goldenRatioTight, goldenRatioTightNE]
  rw [optMakespan_goldenRatioTight, mul_one]
  refine le_antisymm ?_ ?_
  · rw [goldenRatioTight.makespan_le_iff]
    intro j
    rcases (eq_or_ne j 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl
    · rw [hload0]
    · rw [hload1, div_le_iff₀ hφ_pos]
      nlinarith
  · rw [← hload0]
    exact goldenRatioTight.load_le_makespan goldenRatioTightNE 0

end TwoRelatedGoldenRatio

section GeneralRelatedPurePoA

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M]

/-- Weight of jobs assigned by an optimal schedule `Aopt` to a subset `S` of machines is at most
`optMakespan * ∑_{j ∈ S} speed j`. -/
theorem sum_weight_Aopt_mem_le (G : LoadBalancingGame ι M) {Aopt : ι → M}
    (hAopt : G.makespan Aopt = G.optMakespan) (S : Finset M) :
    ∑ i with Aopt i ∈ S, G.weight i ≤ G.optMakespan * ∑ j ∈ S, G.speed j := by
  have hfib : ∑ i with Aopt i ∈ S, G.weight i = ∑ j ∈ S, G.speed j * G.load Aopt j := by
    simp_rw [G.speed_mul_load]
    rw [← sum_fiberwise_of_maps_to (s := univ.filter fun i => Aopt i ∈ S)
      (t := S) (g := Aopt) (fun i hi => (mem_filter.mp hi).2)]
    refine sum_congr rfl fun j hj => sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hj, h⟩⟩
  rw [hfib, mul_sum]
  refine sum_le_sum fun j _ => ?_
  have hl : G.load Aopt j ≤ G.optMakespan := by
    rw [← hAopt]
    exact G.load_le_makespan Aopt j
  nlinarith [(G.speed_pos j).le]

/-- General speed-prefix cardinality step over any machine-load map `L : M → ℝ`: for prefixes
`P k = {j | ∀ j', speed j ≤ speed j' → k * optMakespan ≤ L j'}`, if `(k + 1) * ∑_{P(k+1)} speed ≤
∑_{P k} speed` whenever `P (k + 1)` is nonempty, then `(k + 1) * #(P (k + 1)) ≤ #(P k)`. -/
theorem card_speedPrefix_step_of_sum_speed_le (G : LoadBalancingGame ι M) (L : M → ℝ)
    (P : ℕ → Finset M)
    (hP : ∀ r j, j ∈ P r ↔ ∀ j' : M, G.speed j ≤ G.speed j' → (r : ℝ) * G.optMakespan ≤ L j')
    (hopt_nn : 0 ≤ G.optMakespan) (k : ℕ)
    (hspeed_sum : (P (k + 1)).Nonempty →
      ((k + 1 : ℕ) : ℝ) * ∑ j ∈ P (k + 1), G.speed j ≤ ∑ j ∈ P k, G.speed j) :
    (k + 1) * #(P (k + 1)) ≤ #(P k) := by
  classical
  by_cases hne : (P (k + 1)).Nonempty
  · have hsub : P (k + 1) ⊆ P k := by
      intro j hj
      rw [hP] at hj ⊢
      intro j' hj'
      have := hj j' hj'
      push_cast at this
      linarith
    have hsum := hspeed_sum hne
    obtain ⟨jmin, hjmin, hmin⟩ := exists_min_image (P (k + 1)) G.speed hne
    set smin : ℝ := G.speed jmin
    have hsmin_pos : 0 < smin := G.speed_pos jmin
    have hsdiff_lt : ∀ j ∈ P k \ P (k + 1), G.speed j ≤ smin := by
      intro j hj
      rw [mem_sdiff] at hj
      by_contra hgt
      push Not at hgt
      exact hj.2 ((hP (k + 1) j).mpr fun j' hj' => (hP (k + 1) jmin).mp hjmin j' (hgt.le.trans hj'))
    have hsplit_sum : ∑ j ∈ P k, G.speed j =
        (∑ j ∈ P (k + 1), G.speed j) + (∑ j ∈ P k \ P (k + 1), G.speed j) := by
      rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hsub]
    have hlhs : (k : ℝ) * (#(P (k + 1)) : ℝ) * smin ≤
        (k : ℝ) * ∑ j ∈ P (k + 1), G.speed j := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg k)
      calc (#(P (k + 1)) : ℝ) * smin = ∑ _j ∈ P (k + 1), smin := by simp
        _ ≤ ∑ j ∈ P (k + 1), G.speed j := sum_le_sum fun j hj => hmin j hj
    have hrhs : ∑ j ∈ P k \ P (k + 1), G.speed j ≤ (#(P k \ P (k + 1)) : ℝ) * smin := by
      calc ∑ j ∈ P k \ P (k + 1), G.speed j
          ≤ ∑ _j ∈ P k \ P (k + 1), smin := sum_le_sum fun j hj => hsdiff_lt j hj
        _ = (#(P k \ P (k + 1)) : ℝ) * smin := by simp
    have hnat_real : (k : ℝ) * (#(P (k + 1)) : ℝ) ≤ (#(P k \ P (k + 1)) : ℝ) := by
      rw [hsplit_sum] at hsum
      push_cast at hsum
      nlinarith
    have hnat : k * #(P (k + 1)) ≤ #(P k \ P (k + 1)) := by exact_mod_cast hnat_real
    rw [card_sdiff_of_subset hsub] at hnat
    have hcard_le : #(P (k + 1)) ≤ #(P k) := card_le_card hsub
    have hdist : (k + 1) * #(P (k + 1)) = k * #(P (k + 1)) + #(P (k + 1)) := by ring
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    simp [hne]

omit [Fintype ι] [DecidableEq ι] [DecidableEq M] [Nonempty M] in
/-- Downward factorial induction along a family `P : ℕ → Finset M` satisfying
`(k + 1) * #(P (k + 1)) ≤ #(P k)`: if `1 ≤ #(P c)`, then `c! ≤ |M|`. -/
theorem factorial_le_card_of_prefix_step (P : ℕ → Finset M)
    (hrec_step : ∀ k : ℕ, (k + 1) * #(P (k + 1)) ≤ #(P k)) {c : ℕ} (hPc : 1 ≤ #(P c)) :
    c.factorial ≤ Fintype.card M := by
  have hstep : ∀ d ≤ c, (∏ r ∈ range d, (c - r)) * #(P c) ≤ #(P (c - d)) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      rw [prod_range_succ, mul_right_comm, mul_comm _ (c - d)]
      have hcd : c - d = (c - (d + 1)) + 1 := by omega
      have hrec := hrec_step (c - (d + 1))
      rw [← hcd] at hrec
      calc (c - d) * ((∏ r ∈ range d, (c - r)) * #(P c))
          ≤ (c - d) * #(P (c - d)) := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ #(P (c - (d + 1))) := hrec
  have hprod_eq : ∏ r ∈ range c, (c - r) = c.factorial := by
    rw [Nat.factorial_eq_prod_range_add_one]
    rw [← Finset.prod_range_reflect (fun r => r + 1) c]
    refine prod_congr rfl fun r hr => ?_
    rw [mem_range] at hr
    omega
  have hc_le : c.factorial ≤ #(P 0) := by
    calc c.factorial = c.factorial * 1 := (mul_one _).symm
      _ ≤ (∏ r ∈ range c, (c - r)) * #(P c) := by
          rw [hprod_eq]
          exact Nat.mul_le_mul_left _ hPc
      _ ≤ #(P (c - c)) := hstep c le_rfl
      _ = #(P 0) := by rw [Nat.sub_self]
  exact hc_le.trans (card_le_univ _)

/-- The **speed-sorted prefix** `L_k` of machines all of whose at-least-as-fast peers have load at
least `k * optMakespan` under `A` ([CzumajVocking2002]; [Vocking2007]). -/
@[expose] noncomputable def speedPrefix (G : LoadBalancingGame ι M) (A : ι → M) (k : ℕ) :
    Finset M :=
  open scoped Classical in
  univ.filter fun j => ∀ j' : M, G.speed j ≤ G.speed j' → (k : ℝ) * G.optMakespan ≤ G.load A j'

/-- Every machine in `speedPrefix G A k` has load at least `k * optMakespan`. -/
private theorem mul_optMakespan_le_load_of_mem_speedPrefix (G : LoadBalancingGame ι M)
    (A : ι → M) (k : ℕ) {j : M} (hj : j ∈ G.speedPrefix A k) :
    (k : ℝ) * G.optMakespan ≤ G.load A j := by
  classical
  exact (mem_filter.mp hj).2 j le_rfl

/-- Shared inclusion criteria into any load-threshold speed prefix `P k`: if job `i` has optimal
machine `Aopt i`, load lower bound `(k + 1) * optMakespan ≤ Lj` on a machine whose equilibrium
comparison gives `Lj ≤ L j' + weight i / speed j'` for every `j'`, then `Aopt i ∈ P k`. -/
theorem mem_prefix_of_nash_load_ge (G : LoadBalancingGame ι M) {Aopt : ι → M}
    (hAopt : G.makespan Aopt = G.optMakespan) {L : M → ℝ} {P : Finset M} {k : ℕ}
    (hP : ∀ j, j ∈ P ↔ ∀ j' : M, G.speed j ≤ G.speed j' → (k : ℝ) * G.optMakespan ≤ L j')
    {i : ι} {Lj : ℝ} (hge : ((k + 1 : ℕ) : ℝ) * G.optMakespan ≤ Lj)
    (hNE : ∀ j' : M, Lj ≤ L j' + G.weight i / G.speed j') :
    Aopt i ∈ P := by
  rw [hP]
  intro j' hj'
  have h1 := hNE j'
  have hdiv : G.weight i / G.speed j' ≤ G.weight i / G.speed (Aopt i) :=
    div_le_div_of_nonneg_left (G.weight_nonneg i) (G.speed_pos (Aopt i)) hj'
  have hopt : G.weight i / G.speed (Aopt i) ≤ G.optMakespan := by
    rw [← hAopt]
    exact G.weight_div_speed_le_makespan Aopt i
  push_cast at hge
  linarith

/-- **Prefix-list inclusion lemma** ([CzumajVocking2002]; [Vocking2007]): if `A` is a
pure Nash equilibrium and `Aopt` is an optimal assignment, then any job whose `A`-machine has load
at least `(k + 1) * optMakespan` is assigned by `Aopt` to a machine in `speedPrefix G A k`. -/
theorem mem_speedPrefix_of_load_ge (G : LoadBalancingGame ι M) {A Aopt : ι → M}
    (hA : G.toCostGame.IsPureNash A) (hAopt : G.makespan Aopt = G.optMakespan)
    {k : ℕ} {i : ι} (hi : ((k + 1 : ℕ) : ℝ) * G.optMakespan ≤ G.load A (A i)) :
    Aopt i ∈ G.speedPrefix A k :=
  G.mem_prefix_of_nash_load_ge hAopt
    (fun j => by simp only [speedPrefix, mem_filter, mem_univ, true_and]) hi
    (G.isPureNash_load_le hA i)

/-- **Speed-prefix cardinality growth** ([CzumajVocking2002]; [Vocking2007]): for
every pure Nash equilibrium `A` with `0 < optMakespan` and every `k : ℕ`,
`(k + 1) * #(speedPrefix G A (k + 1)) ≤ #(speedPrefix G A k)`. -/
theorem card_speedPrefix_ge (G : LoadBalancingGame ι M) {A : ι → M}
    (hA : G.toCostGame.IsPureNash A) (hopt : 0 < G.optMakespan) (k : ℕ) :
    (k + 1) * #(G.speedPrefix A (k + 1)) ≤ #(G.speedPrefix A k) := by
  classical
  refine G.card_speedPrefix_step_of_sum_speed_le (G.load A) (G.speedPrefix A)
    (fun r j => by simp only [speedPrefix, mem_filter, mem_univ, true_and])
    G.optMakespan_nonneg k fun _ => ?_
  obtain ⟨Aopt, hAopt⟩ := G.exists_makespan_eq_optMakespan
  have hjob_map : (univ.filter fun i => A i ∈ G.speedPrefix A (k + 1)) ⊆
      univ.filter fun i => Aopt i ∈ G.speedPrefix A k := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact G.mem_speedPrefix_of_load_ge hA hAopt
      (G.mul_optMakespan_le_load_of_mem_speedPrefix A (k + 1) hi)
  have h1 : ((k + 1 : ℕ) : ℝ) * G.optMakespan * ∑ j ∈ G.speedPrefix A (k + 1), G.speed j ≤
      ∑ j ∈ G.speedPrefix A (k + 1), G.speed j * G.load A j := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    have hl := G.mul_optMakespan_le_load_of_mem_speedPrefix A (k + 1) hj
    nlinarith [(G.speed_pos j).le]
  have h2 : ∑ j ∈ G.speedPrefix A (k + 1), G.speed j * G.load A j =
      ∑ i with A i ∈ G.speedPrefix A (k + 1), G.weight i := by
    simp_rw [G.speed_mul_load]
    rw [← sum_fiberwise_of_maps_to (s := univ.filter fun i => A i ∈ G.speedPrefix A (k + 1))
      (t := G.speedPrefix A (k + 1)) (g := A) (fun i hi => (mem_filter.mp hi).2)]
    refine sum_congr rfl fun j hj => sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hj, h⟩, fun h => h.2⟩
  have h3 : ∑ i with A i ∈ G.speedPrefix A (k + 1), G.weight i ≤
      ∑ i with Aopt i ∈ G.speedPrefix A k, G.weight i :=
    sum_le_sum_of_subset_of_nonneg hjob_map fun i _ _ => G.weight_nonneg i
  have h4 := G.sum_weight_Aopt_mem_le hAopt (G.speedPrefix A k)
  have hcomb :
      G.optMakespan * (((k + 1 : ℕ) : ℝ) * ∑ j ∈ G.speedPrefix A (k + 1), G.speed j) ≤
      G.optMakespan * ∑ j ∈ G.speedPrefix A k, G.speed j := by
    linarith
  exact le_of_mul_le_mul_left hcomb hopt

/-- **Factorial pure PoA bound for uniformly related machines** ([CzumajVocking2002];
[Vocking2007]): if `A` is a pure Nash equilibrium with `0 < optMakespan` and
`(c + 1) * optMakespan ≤ makespan A`, then `c! ≤ |M|`. Equivalently, `makespan A < (c + 1) *
optMakespan` whenever `|M| < c!`. -/
theorem factorial_le_card_of_makespan_ge (G : LoadBalancingGame ι M) {A : ι → M}
    (hA : G.toCostGame.IsPureNash A) (hopt : 0 < G.optMakespan) {c : ℕ}
    (hge : ((c + 1 : ℕ) : ℝ) * G.optMakespan ≤ G.makespan A) :
    c.factorial ≤ Fintype.card M := by
  classical
  obtain ⟨Aopt, hAopt⟩ := G.exists_makespan_eq_optMakespan
  obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
  have hpos_load : 0 < G.load A jstar := by
    rw [hjstar]
    have : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos c
    nlinarith
  have hi₀_exists : ∃ i₀ : ι, A i₀ = jstar := by
    by_contra hnone
    push Not at hnone
    have : G.load A jstar = 0 := by
      rw [G.load_eq_sum_div]
      have : (univ.filter fun i => A i = jstar) = ∅ := by
        ext i; simp [hnone i]
      rw [this, sum_empty, zero_div]
    linarith
  obtain ⟨i₀, hi₀⟩ := hi₀_exists
  have hLc_ne : 1 ≤ #(G.speedPrefix A c) := by
    refine card_pos.mpr ⟨Aopt i₀, G.mem_speedPrefix_of_load_ge hA hAopt ?_⟩
    rw [hi₀, hjstar]
    exact hge
  exact factorial_le_card_of_prefix_step (G.speedPrefix A) (G.card_speedPrefix_ge hA hopt) hLc_ne

private theorem pow_le_factorial_two_mul (r : ℕ) : r ^ r ≤ (2 * r).factorial := by
  rw [Nat.factorial_eq_prod_range_add_one, two_mul, prod_range_add]
  have h1 : 1 ≤ ∏ i ∈ range r, (i + 1) :=
    Finset.one_le_prod fun i _ => Nat.succ_pos i
  have h2 : r ^ r ≤ ∏ i ∈ range r, (r + i + 1) := by
    calc r ^ r = ∏ _i ∈ range r, r := by simp
      _ ≤ ∏ i ∈ range r, (r + i + 1) := Finset.prod_le_prod fun i _ => by omega
  calc r ^ r = 1 * r ^ r := (one_mul _).symm
    _ ≤ (∏ i ∈ range r, (i + 1)) * (∏ i ∈ range r, (r + i + 1)) := Nat.mul_le_mul h1 h2

/-- If `m ≥ 3`, `0 < opt`, `0 ≤ val`, and every integer `c` with `(c + 1) * opt ≤ val` satisfies
`c! ≤ m`, then `val ≤ (4 * log m / log (log m) + 3) * opt`. Shared between the uniformly related
pure makespan bound and mixed expected-load bound. -/
theorem le_log_div_log_log_add_three_mul_of_factorial_le {m : ℕ} (hm : 3 ≤ m) {val opt : ℝ}
    (hopt : 0 < opt) (hval : 0 ≤ val)
    (hfac : ∀ c : ℕ, ((c + 1 : ℕ) : ℝ) * opt ≤ val → c.factorial ≤ m) :
    val ≤ (4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) + 3) * opt := by
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm_gt1 : 1 < Real.log (m : ℝ) := Real.one_lt_log_of_three_le hm3
  have hloglog_pos : 0 < Real.log (Real.log (m : ℝ)) := Real.log_pos hlogm_gt1
  have hratio_pos : 0 < 4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by positivity
  by_cases hsmall : val ≤ 2 * opt
  · nlinarith
  · push Not at hsmall
    set q : ℕ := ⌊val / opt⌋₊
    have hq_ge2 : 2 ≤ q := by
      rw [Nat.le_floor_iff (div_nonneg hval hopt.le), le_div_iff₀ hopt]
      push_cast
      linarith
    set c : ℕ := q - 1
    have hge : ((c + 1 : ℕ) : ℝ) * opt ≤ val := by
      have hcq : c + 1 = q := by omega
      rw [hcq]
      exact (le_div_iff₀ hopt).mp (Nat.floor_le (div_nonneg hval hopt.le))
    have hc_fac : c.factorial ≤ m := hfac c hge
    set r : ℕ := c / 2
    have hpow : r ^ r ≤ m :=
      (pow_le_factorial_two_mul r).trans ((Nat.factorial_le (by omega)).trans hc_fac)
    have hr_lt : (r : ℝ) < 2 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by
      by_contra hge_r
      push Not at hge_r
      set x : ℝ := Real.log (m : ℝ)
      have hlogx_lt : Real.log x < 2 * √x := by
        have h1 : Real.log (√x) ≤ √x - 1 :=
          Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
        have h2 : Real.log (√x) = Real.log x / 2 := Real.log_sqrt (by linarith)
        linarith
      have hsqrt_lt : √x < 2 * x / Real.log x := by
        rw [lt_div_iff₀ hloglog_pos]
        have hsq : √x * √x = x := Real.mul_self_sqrt (by linarith)
        nlinarith [Real.sqrt_pos.mpr (show 0 < x by linarith)]
      have hr_gt_sqrt : √x < (r : ℝ) := hsqrt_lt.trans_le hge_r
      have hsqrt_gt1 : 1 < √x := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by norm_num) hlogm_gt1
      have hr_pos : (0 : ℝ) < r := by linarith
      have hlogr_gt : Real.log x / 2 < Real.log (r : ℝ) := by
        rw [← Real.log_sqrt (by linarith)]
        exact Real.log_lt_log (by linarith) hr_gt_sqrt
      have hmul_gt : x < (r : ℝ) * Real.log (r : ℝ) := by
        have h1 : (2 * x / Real.log x) * (Real.log x / 2) = x := by
          field_simp [hloglog_pos.ne']
        have h3 : (2 * x / Real.log x) * (Real.log x / 2) ≤ (r : ℝ) * (Real.log x / 2) :=
          mul_le_mul_of_nonneg_right hge_r (by positivity)
        have h4 : (r : ℝ) * (Real.log x / 2) < (r : ℝ) * Real.log (r : ℝ) :=
          mul_lt_mul_of_pos_left hlogr_gt hr_pos
        linarith
      have hpow_real : ((r : ℝ) ^ r) ≤ (m : ℝ) := by exact_mod_cast hpow
      have hlog_pow : (r : ℝ) * Real.log (r : ℝ) ≤ x := by
        rw [← Real.log_pow]
        exact Real.log_le_log (pow_pos hr_pos r) hpow_real
      linarith
    have hq_lt : val / opt < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    have hq_le_r : q ≤ 2 * r + 2 := by omega
    have hq_real : (q : ℝ) ≤ 2 * (r : ℝ) + 2 := by exact_mod_cast hq_le_r
    have hval_lt : val < ((q : ℝ) + 1) * opt := (div_lt_iff₀ hopt).mp hq_lt
    have hcoef : (q : ℝ) + 1 < 4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) + 3 := by
      have h2 : 2 * (2 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) =
          4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by ring
      linarith
    nlinarith

/-- **Asymptotic pure PoA for uniformly related machines** ([CzumajVocking2002]; [Vocking2007]):
for every load-balancing game on `m = |M| ≥ 3` uniformly related machines and every
pure Nash equilibrium `A`,
`makespan A ≤ (4 * log m / log (log m) + 3) * optMakespan = O(log m / log log m) * optMakespan`.
-/
theorem makespan_le_log_div_log_log_mul_optMakespan (G : LoadBalancingGame ι M)
    (hm : 3 ≤ Fintype.card M) {A : ι → M} (hA : G.toCostGame.IsPureNash A) :
    G.makespan A ≤
      (4 * Real.log (Fintype.card M) / Real.log (Real.log (Fintype.card M)) + 3) *
        G.optMakespan := by
  rcases G.optMakespan_nonneg.eq_or_lt with hopt0 | hopt_pos
  · rw [G.makespan_eq_zero_of_optMakespan_eq_zero hopt0.symm A, ← hopt0, mul_zero]
  · exact le_log_div_log_log_add_three_mul_of_factorial_le hm hopt_pos (G.makespan_nonneg A)
      fun _ hge => G.factorial_le_card_of_makespan_ge hA hopt_pos hge

end GeneralRelatedPurePoA

end LoadBalancingGame

namespace UnrelatedLoadBalancingGame

/-- **Unbounded pure price of anarchy on unrelated machines**: for every `K ≥ 1`, there is a
2-job, 2-machine unrelated load-balancing game with a pure Nash equilibrium whose makespan equals
`K * optMakespan` (contrasting with `4/3` on identical and `(1 + √5)/2` on uniformly related
2-machine games). -/
theorem exists_isPureNash_makespan_eq_mul_optMakespan {K : ℝ} (hK : 1 ≤ K) :
    ∃ (U : UnrelatedLoadBalancingGame (Fin 2) (Fin 2)) (A : Fin 2 → Fin 2),
      U.toCostGame.IsPureNash A ∧ U.makespan A = K * U.optMakespan ∧ U.optMakespan = 1 := by
  let U : UnrelatedLoadBalancingGame (Fin 2) (Fin 2) :=
    { procTime := fun i j => if i = j then K else 1
      procTime_nonneg := fun i j => by split_ifs <;> linarith }
  let A : Fin 2 → Fin 2 := id
  let Aopt : Fin 2 → Fin 2 := ![1, 0]
  have hloadA : ∀ j : Fin 2, U.load A j = K := fun j => by
    rw [load, sum_filter, Fin.sum_univ_two]
    fin_cases j <;> simp [U, A]
  have hloadOpt : ∀ j : Fin 2, U.load Aopt j = 1 := fun j => by
    rw [load, sum_filter, Fin.sum_univ_two]
    fin_cases j <;> simp [U, Aopt]
  have hNE : U.toCostGame.IsPureNash A := by
    rw [U.isPureNash_iff]
    intro i k hk
    rw [hloadA, hloadA]
    simp only [U, A, id_eq] at hk ⊢
    rw [ite_eq_right hk.symm]
    linarith
  have hmsA : U.makespan A = K := by
    refine le_antisymm ((U.makespan_le_iff A).mpr fun j => (hloadA j).le) ?_
    rw [← hloadA 0]
    exact U.load_le_makespan A 0
  have hopt : U.optMakespan = 1 := by
    refine le_antisymm ?_ ?_
    · exact (U.optMakespan_le Aopt).trans ((U.makespan_le_iff Aopt).mpr fun j => (hloadOpt j).le)
    · obtain ⟨B, hB⟩ := U.exists_makespan_eq_optMakespan
      rw [← hB]
      have hge1 : 1 ≤ U.procTime 0 (B 0) := by
        simp only [U]
        split_ifs <;> linarith
      exact hge1.trans ((U.procTime_le_load B 0).trans (U.load_le_makespan B (B 0)))
  exact ⟨U, A, hNE, by rw [hmsA, hopt, mul_one], hopt⟩

end UnrelatedLoadBalancingGame

end Cslib.GameTheory

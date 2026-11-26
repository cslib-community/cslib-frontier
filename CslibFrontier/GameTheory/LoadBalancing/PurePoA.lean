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
  have hrest : ((Fintype.card M : ℝ) - 1) * (G.load A jstar - G.weight i₀) ≤
      ∑ k ∈ univ.erase jstar, G.load A k := by
    calc ((Fintype.card M : ℝ) - 1) * (G.load A jstar - G.weight i₀)
        = ∑ _k ∈ univ.erase jstar, (G.load A jstar - G.weight i₀) := by
          rw [sum_const, card_erase_of_mem (mem_univ jstar), card_univ, nsmul_eq_mul,
            Nat.cast_sub Fintype.card_pos, Nat.cast_one]
      _ ≤ ∑ k ∈ univ.erase jstar, G.load A k := sum_le_sum fun k hk => by
          have hne := (G.isPureNash_iff A).mp hA i₀ k (hAi₀.symm ▸ ne_of_mem_erase hk)
          rw [hAi₀, hId k, div_one] at hne; linarith
  have hsum : G.load A jstar + ∑ k ∈ univ.erase jstar, G.load A k ≤
      (Fintype.card M : ℝ) * G.optMakespan := by
    rw [add_sum_erase _ _ (mem_univ jstar), hId.sum_load A]
    exact hId.sum_weight_le_card_mul_optMakespan
  linarith

/-- **Identical-machine pure price of anarchy** ([FinnHorowitz1979]; [Vocking2007]):
every pure Nash equilibrium `A` on `m = |M| ≥ 1` identical machines satisfies
`makespan A ≤ (2 * m / (m + 1)) * optMakespan` (equivalently `(2 - 2 / (m + 1)) * optMakespan`).
-/
theorem IsIdentical.makespan_le_of_isPureNash {G : LoadBalancingGame ι M} (hId : G.IsIdentical)
    {A : ι → M} (hA : G.toCostGame.IsPureNash A) :
    G.makespan A ≤
      (2 * (Fintype.card M : ℝ) / ((Fintype.card M : ℝ) + 1)) * G.optMakespan := by
  have hm_ge1 : (1 : ℝ) ≤ Fintype.card M := Nat.one_le_cast.mpr Fintype.card_pos
  have hratio_ge1 : (1 : ℝ) ≤ 2 * (Fintype.card M : ℝ) / ((Fintype.card M : ℝ) + 1) :=
    (le_div_iff₀ (by linarith)).mpr (by linarith)
  obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
  set S : Finset ι := univ.filter fun i => A i = jstar
  have hload_S : G.load A jstar = ∑ i ∈ S, G.weight i := by
    rw [G.load_eq_sum_div, hId jstar, div_one]
  by_cases hcard : #S ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · rw [← hjstar, hload_S, card_eq_zero.mp h0, sum_empty]
      exact mul_nonneg (by positivity) G.optMakespan_nonneg
    · obtain ⟨i₀, hi₀⟩ := card_eq_one.mp h1
      rw [← hjstar, hload_S, hi₀, sum_singleton]
      calc G.weight i₀ ≤ G.optMakespan := hId.weight_le_optMakespan i₀
        _ ≤ (2 * (Fintype.card M : ℝ) / ((Fintype.card M : ℝ) + 1)) * G.optMakespan := by
            nlinarith [G.optMakespan_nonneg]
  · obtain ⟨i₀, hi₀S, hi₀min⟩ := exists_min_image S G.weight (card_pos.mp (by omega))
    -- Since `#S ≥ 2` and `i₀` has minimum weight on `jstar`, `2 * weight i₀ ≤ load A jstar`.
    have h2w : 2 * G.weight i₀ ≤ G.load A jstar := by
      have h2S : (2 : ℝ) ≤ #S := Nat.ofNat_le_cast.mpr (by omega)
      rw [hload_S]
      calc 2 * G.weight i₀ ≤ (#S : ℝ) * G.weight i₀ := by nlinarith [G.weight_nonneg i₀]
        _ = ∑ _i ∈ S, G.weight i₀ := by simp
        _ ≤ ∑ i ∈ S, G.weight i := sum_le_sum fun i hi => hi₀min i hi
    have hbound := hId.card_mul_load_sub_le_card_mul_optMakespan hA (mem_filter.mp hi₀S).2
    rw [← hjstar, div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

/-- Strict `< 2` bound for arbitrary `m` identical machines when `optMakespan > 0`. -/
theorem IsIdentical.makespan_lt_two_mul_of_isPureNash {G : LoadBalancingGame ι M}
    (hId : G.IsIdentical) {A : ι → M} (hA : G.toCostGame.IsPureNash A)
    (hopt : 0 < G.optMakespan) :
    G.makespan A < 2 * G.optMakespan := by
  have hm_pos : (0 : ℝ) < Fintype.card M := Nat.cast_pos.mpr Fintype.card_pos
  exact (hId.makespan_le_of_isPureNash hA).trans_lt <|
    mul_lt_mul_of_pos_right ((div_lt_iff₀ (by linarith)).mpr (by linarith)) hopt

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
    rw [Finset.mem_filter]
    cases b <;> simp [finnHorowitzTightNE]
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
    simp only [hj, hk0, ↓reduceIte]; linarith
  · have hnonneg : (0 : ℝ) ≤ if b then ((m - j.val : ℕ) : ℝ) else (j.val : ℝ) := by
      split_ifs <;> positivity
    by_cases hk0 : k.val = 0 <;> simp only [hj, hk0, ↓reduceIte] <;>
      linarith [Nat.cast_nonneg (α := ℝ) m]

theorem makespan_finnHorowitzTightNE (m : ℕ) [NeZero m] :
    (finnHorowitzTight m).makespan (finnHorowitzTightNE m) = 2 * (m : ℝ) := by
  refine le_antisymm (((finnHorowitzTight m).makespan_le_iff _).mpr fun j => ?_) ?_
  · rw [load_finnHorowitzTightNE m j]
    split_ifs <;> linarith [Nat.cast_nonneg (α := ℝ) m]
  · calc 2 * (m : ℝ) = (finnHorowitzTight m).load (finnHorowitzTightNE m) 0 := by
          simp only [load_finnHorowitzTightNE, Fin.val_zero, ↓reduceIte]
      _ ≤ (finnHorowitzTight m).makespan (finnHorowitzTightNE m) :=
          (finnHorowitzTight m).load_le_makespan _ 0

theorem optMakespan_finnHorowitzTight (m : ℕ) [NeZero m] :
    (finnHorowitzTight m).optMakespan = (m : ℝ) + 1 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let Aopt : Bool × Fin m → Fin m := fun p =>
    if p.1 then (if h : p.2.val + 1 < m then ⟨p.2.val + 1, h⟩ else ⟨0, hm_pos⟩) else p.2
  have hload_opt : ∀ j : Fin m, (finnHorowitzTight m).load Aopt j = (m : ℝ) + 1 := by
    intro j
    let prev : Fin m := if j.val = 0 then ⟨m - 1, by omega⟩ else ⟨j.val - 1, by omega⟩
    have hfilt : (univ.filter fun p : Bool × Fin m => Aopt p = j) =
        {(false, j), (true, prev)} := by
      ext ⟨b, k⟩
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq, Aopt]
      cases b with
      | false => simp
      | true =>
        have hk_lt := k.isLt
        have hj_lt := j.isLt
        simp only [Bool.true_eq_false, false_and, true_and, false_or, prev, ↓reduceIte, Fin.ext_iff]
        split_ifs <;> simp only <;> omega
    rw [LoadBalancingGame.load_eq_sum_div]
    simp only [finnHorowitzTight, identical, div_one]
    change ∑ p ∈ univ.filter (fun p : Bool × Fin m => Aopt p = j),
      (if p.2.val = 0 then (m : ℝ)
       else if p.1 then ((m - p.2.val : ℕ) : ℝ) else p.2.val) = _
    rw [hfilt, sum_pair (by simp)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hprev_eq : (if prev.val = 0 then (m : ℝ) else ((m - prev.val : ℕ) : ℝ)) =
        ((m - prev.val : ℕ) : ℝ) := by
      split_ifs with hp <;> simp [hp]
    rw [hprev_eq]
    by_cases hj0 : j.val = 0
    · simp only [prev, hj0, ↓reduceIte, Nat.sub_sub_self hm_pos, Nat.cast_one]
    · simp only [prev, hj0, ↓reduceIte, Nat.cast_sub (by omega : j.val - 1 ≤ m),
        Nat.cast_sub (by omega : 1 ≤ j.val), Nat.cast_one]
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
    nlinarith [(Nat.cast_pos.mpr hm_pos : (0 : ℝ) < m)]

/-- **Tightness of the `2m / (m + 1)` pure price of anarchy** ([FinnHorowitz1979]; [Vocking2007]):
for every `m ≥ 1`, `finnHorowitzTightNE m` attains exact equality. -/
theorem makespan_finnHorowitzTightNE_eq_ratio (m : ℕ) [NeZero m] :
    (finnHorowitzTight m).makespan (finnHorowitzTightNE m) =
      (2 * (m : ℝ) / ((m : ℝ) + 1)) * (finnHorowitzTight m).optMakespan := by
  rw [makespan_finnHorowitzTightNE, optMakespan_finnHorowitzTight]
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
      G.weight i₁ + G.weight i₂ ≤ G.makespan τ := fun {i₁ i₂} hne hsame => by
    have hsub : ({i₁, i₂} : Finset (Fin 3)) ⊆ univ.filter fun r => τ r = τ i₁ := by
      intro r hr
      simp only [mem_insert, mem_singleton] at hr
      exact mem_filter.mpr ⟨mem_univ _, hr.elim (· ▸ rfl) (· ▸ hsame.symm)⟩
    calc G.weight i₁ + G.weight i₂ = ∑ r ∈ ({i₁, i₂} : Finset (Fin 3)), G.weight r :=
          (sum_pair hne).symm
      _ ≤ ∑ r with τ r = τ i₁, G.weight r :=
          sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => G.weight_nonneg r
      _ = G.load τ (τ i₁) := by rw [G.load_eq_sum_div, hId (τ i₁), div_one]
      _ ≤ G.makespan τ := G.load_le_makespan τ (τ i₁)
  have hw_le : ∀ i : Fin 3, G.weight i ≤ G.makespan τ := fun i => by
    simpa only [hId (τ i), div_one] using G.weight_div_speed_le_makespan τ i
  obtain ⟨jstar, hjstar⟩ := G.exists_load_eq_makespan A
  let jother : Fin 2 := 1 - jstar
  have hjne : jother ≠ jstar := by fin_cases jstar <;> decide
  have hne_eq (j : Fin 2) : j ≠ jstar → j = jother := by
    fin_cases j <;> fin_cases jstar <;> decide
  set S : Finset (Fin 3) := univ.filter fun i => A i = jstar
  have hload_S : G.load A jstar = ∑ i ∈ S, G.weight i := by
    rw [G.load_eq_sum_div, hId jstar, div_one]
  rw [← hjstar]
  have hcard_le3 : #S ≤ 3 := (card_le_univ S).trans (by simp)
  by_cases hcard1 : #S ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard1 with h0 | h1
    · rw [hload_S, card_eq_zero.mp h0, sum_empty]
      exact G.makespan_nonneg τ
    · obtain ⟨i₀, hi₀⟩ := card_eq_one.mp h1
      rw [hload_S, hi₀, sum_singleton]
      exact hw_le i₀
  · by_cases hcard3 : #S = 3
    · have hA_all : ∀ i : Fin 3, A i = jstar := fun i =>
        (mem_filter.mp (show i ∈ S from eq_univ_of_card S (by simpa using hcard3) ▸ mem_univ i)).2
      have hload_other : G.load A jother = 0 := by
        rw [G.load_eq_sum_div, sum_eq_zero fun i hi =>
          absurd (mem_filter.mp hi).2 (hA_all i ▸ hjne.symm), zero_div]
      have hNE := (G.isPureNash_iff A).mp hA 0 jother (hA_all 0 ▸ hjne)
      rw [hA_all 0, hload_other, hId jother, div_one, zero_add] at hNE
      exact hNE.trans (hw_le 0)
    · have hcard2 : #S = 2 := by omega
      obtain ⟨i₁, i₂, hi₁₂, hS_eq⟩ := card_eq_two.mp hcard2
      -- Find the unique third job `i₃ ∉ S`, which must sit on `jother`.
      have hfilt_other : (univ.filter fun i : Fin 3 => A i = jother) = univ \ S := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_sdiff, S]
        exact ⟨fun hi h => hjne (hi.symm.trans h), hne_eq (A i)⟩
      have hcard_comp : #(univ \ S) = 1 := by
        rw [card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin, hcard2]
      obtain ⟨i₃, hi₃_eq⟩ := card_eq_one.mp hcard_comp
      have hi₃_notS : i₃ ∉ S := (mem_sdiff.mp (hi₃_eq ▸ mem_singleton_self i₃)).2
      have hmemS {i} (hi : i ∈ ({i₁, i₂} : Finset (Fin 3))) : i ∈ S := hS_eq ▸ hi
      have hAi₁ : A i₁ = jstar := (mem_filter.mp (hmemS (mem_insert_self i₁ _))).2
      have hAi₂ : A i₂ = jstar :=
        (mem_filter.mp (hmemS (mem_insert_of_mem (mem_singleton_self i₂)))).2
      have hload_jstar : G.load A jstar = G.weight i₁ + G.weight i₂ := by
        rw [hload_S, hS_eq, sum_pair hi₁₂]
      have hload_other : G.load A jother = G.weight i₃ := by
        rw [G.load_eq_sum_div, hId jother, div_one, hfilt_other, hi₃_eq, sum_singleton]
      have hNE₁ := (G.isPureNash_iff A).mp hA i₁ jother (hAi₁ ▸ hjne)
      have hNE₂ := (G.isPureNash_iff A).mp hA i₂ jother (hAi₂ ▸ hjne)
      rw [hAi₁, hload_jstar, hload_other, hId jother, div_one] at hNE₁
      rw [hAi₂, hload_jstar, hload_other, hId jother, div_one] at hNE₂
      have hi₁₃ : i₁ ≠ i₃ := fun h => hi₃_notS (h ▸ hmemS (mem_insert_self i₁ _))
      have hi₂₃ : i₂ ≠ i₃ := fun h =>
        hi₃_notS (h ▸ hmemS (mem_insert_of_mem (mem_singleton_self i₂)))
      have hpig : τ i₁ = τ i₂ ∨ τ i₁ = τ i₃ ∨ τ i₂ = τ i₃ := by
        generalize τ i₁ = a, τ i₂ = b, τ i₃ = c
        fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
      rw [hload_jstar]
      rcases hpig with h | h | h <;> linarith [hpair_le (by assumption) h]

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
  rcases (univ.filter fun i => A i = jstar).eq_empty_or_nonempty with hS0 | ⟨i₀, hi₀⟩
  · rw [← hjstar, G.load_eq_sum_div, hS0, sum_empty, zero_div]
    nlinarith [G.optMakespan_nonneg, (div_le_one hm_pos).mpr hm_ge1]
  · have hbound := hId.card_mul_load_sub_le_card_mul_optMakespan hA (mem_filter.mp hi₀).2
    have heq : (Fintype.card M : ℝ) * (G.optMakespan + (1 - 1 / (Fintype.card M : ℝ)) * B) =
        (Fintype.card M : ℝ) * G.optMakespan + ((Fintype.card M : ℝ) - 1) * B := by
      field_simp
    rw [← hjstar]
    nlinarith [hw i₀]

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
  have hsqrt5_gt : (2 : ℝ) < √5 := by nlinarith [Real.sqrt_nonneg 5]
  have hφ_gt : (3 / 2 : ℝ) < φ := by simp only [φ]; linarith
  have hφ_sq : φ ^ 2 = φ + 1 := by simp only [φ]; nlinarith [hsq5]
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
    rw [hpair, sum_pair hjne.symm] at h1 h2; linarith
  set S : Finset ι := univ.filter fun i => A i = jstar
  have hload_S : s * G.load A jstar = ∑ i ∈ S, G.weight i := G.speed_mul_load A jstar
  have hopt_nn : 0 ≤ G.optMakespan := G.optMakespan_nonneg
  rw [← hjstar]
  by_cases hcard : #S ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · have hl0 : G.load A jstar = 0 :=
        (mul_eq_zero.mp (by rw [hload_S, card_eq_zero.mp h0, sum_empty])).resolve_left hs.ne'
      rw [hl0]; nlinarith
    · obtain ⟨i₀, hi₀⟩ := card_eq_one.mp h1
      have hAi₀ : A i₀ = jstar :=
        (mem_filter.mp (show i₀ ∈ S from hi₀ ▸ mem_singleton_self i₀)).2
      have hwi₀ : G.weight i₀ = s * G.load A jstar := by rw [hload_S, hi₀, sum_singleton]
      by_cases hopt_i : Aopt i₀ = jstar
      · have hle : G.weight i₀ / s ≤ G.optMakespan := by
          simpa only [s, hAopt, hopt_i] using G.weight_div_speed_le_makespan Aopt i₀
        rw [hwi₀, mul_div_cancel_left₀ _ hs.ne'] at hle; nlinarith
      · have hopt_other : Aopt i₀ = jother :=
          mem_singleton.mp ((mem_insert.mp (hpair ▸ mem_univ (Aopt i₀))).resolve_left hopt_i)
        have hle_t : G.weight i₀ / t ≤ G.optMakespan := by
          simpa only [t, hAopt, hopt_other] using G.weight_div_speed_le_makespan Aopt i₀
        have hbound1 : s * G.load A jstar ≤ t * G.optMakespan := by
          linarith [(div_le_iff₀ ht).mp hle_t]
        -- Pure NE for `i₀` moving to `jother`: `load A jstar ≤ load A jother + weight i₀ / t`.
        have hNE := (G.isPureNash_iff A).mp hA i₀ jother (hAi₀ ▸ hjne)
        rw [hAi₀, hwi₀] at hNE
        have hNE' : t * G.load A jstar ≤ t * G.load A jother + s * G.load A jstar := by
          have := mul_le_mul_of_nonneg_left hNE ht.le
          rw [mul_add, mul_div_cancel₀ _ ht.ne'] at this; linarith
        by_cases hratio : t ≤ φ * s
        · nlinarith
        · have h1 : t * G.load A jstar ≤ (s + t) * G.optMakespan := by linarith
          have hφ_pos : 0 < φ := by linarith
          have h2 : s + t ≤ φ * t :=
            le_of_mul_le_mul_left (by nlinarith [hφ_sq]) hφ_pos
          nlinarith
  · -- At least 2 jobs on `jstar`: makespan is at most `(3/2) * optMakespan < φ * optMakespan`.
    obtain ⟨i₀, hi₀S, hi₀min⟩ := exists_min_image S G.weight (card_pos.mp (by omega))
    have hAi₀ : A i₀ = jstar := (mem_filter.mp hi₀S).2
    have h2w : 2 * G.weight i₀ ≤ s * G.load A jstar := by
      have h2S : (2 : ℝ) ≤ #S := Nat.ofNat_le_cast.mpr (by omega)
      rw [hload_S]
      calc 2 * G.weight i₀ ≤ (#S : ℝ) * G.weight i₀ := by nlinarith [G.weight_nonneg i₀]
        _ = ∑ _i ∈ S, G.weight i₀ := by simp
        _ ≤ ∑ i ∈ S, G.weight i := sum_le_sum fun i hi => hi₀min i hi
    have hNE := (G.isPureNash_iff A).mp hA i₀ jother (hAi₀ ▸ hjne)
    rw [hAi₀] at hNE
    have hNE' : t * G.load A jstar ≤ t * G.load A jother + G.weight i₀ := by
      have := mul_le_mul_of_nonneg_left hNE ht.le
      rw [mul_add, mul_div_cancel₀ _ ht.ne'] at this; linarith
    have hbound_small : s * G.load A jstar ≤ (s + t) * G.optMakespan := by
      nlinarith [G.load_nonneg A jother]
    have hthree_halves : G.load A jstar ≤ (3 / 2 : ℝ) * G.optMakespan := by
      by_cases hst : 2 * t ≤ s <;> nlinarith
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

private theorem load_goldenRatioTightNE :
    goldenRatioTight.load goldenRatioTightNE 0 = (1 + √5) / 2 ∧
    goldenRatioTight.load goldenRatioTightNE 1 = 1 / ((1 + √5) / 2) := by
  constructor <;>
    (rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
     simp [goldenRatioTight, goldenRatioTightNE])

theorem isPureNash_goldenRatioTightNE :
    goldenRatioTight.toCostGame.IsPureNash goldenRatioTightNE := by
  have hsq5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hφ_pos : (0 : ℝ) < (1 + √5) / 2 := by positivity
  obtain ⟨hload0, hload1⟩ := load_goldenRatioTightNE
  rw [goldenRatioTight.isPureNash_iff]
  intro i k hk
  rcases (eq_or_ne i 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl <;>
    rcases (eq_or_ne k 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl
  · rw [show goldenRatioTightNE 0 = 1 from rfl, hload1, hload0]
    simp only [goldenRatioTight, Matrix.cons_val_zero, div_one]
    rw [div_le_iff₀ hφ_pos]; nlinarith [Real.sqrt_nonneg 5]
  · exact absurd rfl hk
  · exact absurd rfl hk
  · rw [show goldenRatioTightNE 1 = 0 from rfl, hload0, hload1]
    simp only [goldenRatioTight, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      div_self hφ_pos.ne']
    have : 1 / ((1 + √5) / 2) + 1 = (1 + √5) / 2 := by field_simp; nlinarith [hsq5]
    linarith

theorem optMakespan_goldenRatioTight : goldenRatioTight.optMakespan = 1 := by
  have hφ_pos : (0 : ℝ) < (1 + √5) / 2 := by positivity
  have hload_id : ∀ j : Fin 2, goldenRatioTight.load id j = 1 := fun j => by
    rw [LoadBalancingGame.load_eq_sum_div, sum_filter, Fin.sum_univ_two]
    fin_cases j <;> simp [goldenRatioTight, div_self hφ_pos.ne']
  refine le_antisymm
    ((goldenRatioTight.optMakespan_le id).trans
      ((goldenRatioTight.makespan_le_iff id).mpr fun j => (hload_id j).le)) ?_
  have hvol := goldenRatioTight.sum_weight_le_sum_speed_mul_optMakespan
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at hvol
  change 1 + (1 + √5) / 2 ≤ (1 + (1 + √5) / 2) * goldenRatioTight.optMakespan at hvol
  nlinarith

theorem makespan_goldenRatioTightNE :
    goldenRatioTight.makespan goldenRatioTightNE =
      ((1 + √5) / 2) * goldenRatioTight.optMakespan := by
  have hφ_pos : (0 : ℝ) < (1 + √5) / 2 := by positivity
  have hφ_ge1 : (1 : ℝ) ≤ (1 + √5) / 2 := by
    linarith [Real.sqrt_one ▸ Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 5)]
  obtain ⟨hload0, hload1⟩ := load_goldenRatioTightNE
  rw [optMakespan_goldenRatioTight, mul_one]
  refine le_antisymm ((goldenRatioTight.makespan_le_iff _).mpr fun j => ?_)
    (hload0 ▸ goldenRatioTight.load_le_makespan goldenRatioTightNE 0)
  rcases (eq_or_ne j 0).imp_right (Fin.eq_one_of_ne_zero _) with rfl | rfl
  · rw [hload0]
  · rw [hload1, div_le_iff₀ hφ_pos]; nlinarith

end TwoRelatedGoldenRatio

section GeneralRelatedPurePoA

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M] [Nonempty M]

omit [DecidableEq ι] [Fintype M] [Nonempty M] in
private theorem sum_speed_mul_load_eq_sum_weight (G : LoadBalancingGame ι M) (A : ι → M)
    (S : Finset M) :
    ∑ j ∈ S, G.speed j * G.load A j = ∑ i with A i ∈ S, G.weight i := by
  simp_rw [G.speed_mul_load]
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun i => A i ∈ S)
    (t := S) (g := A) (fun i hi => (mem_filter.mp hi).2)]
  refine sum_congr rfl fun j hj => sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h ▸ hj, h⟩, fun h => h.2⟩

/-- Weight of jobs assigned by an optimal schedule `Aopt` to a subset `S` of machines is at most
`optMakespan * ∑_{j ∈ S} speed j`. -/
theorem sum_weight_Aopt_mem_le (G : LoadBalancingGame ι M) {Aopt : ι → M}
    (hAopt : G.makespan Aopt = G.optMakespan) (S : Finset M) :
    ∑ i with Aopt i ∈ S, G.weight i ≤ G.optMakespan * ∑ j ∈ S, G.speed j := by
  rw [← G.sum_speed_mul_load_eq_sum_weight Aopt S, mul_sum]
  exact sum_le_sum fun j _ => by
    nlinarith [(G.speed_pos j).le, hAopt ▸ G.load_le_makespan Aopt j]

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
  · have hsub : P (k + 1) ⊆ P k := fun j hj => (hP k j).mpr fun j' hj' => by
      have := (hP (k + 1) j).mp hj j' hj'
      push_cast at this
      linarith
    have hsum := hspeed_sum hne
    obtain ⟨jmin, hjmin, hmin⟩ := exists_min_image (P (k + 1)) G.speed hne
    set smin : ℝ := G.speed jmin
    have hsmin_pos : 0 < smin := G.speed_pos jmin
    have hsdiff_lt : ∀ j ∈ P k \ P (k + 1), G.speed j ≤ smin := fun j hj => by
      by_contra! hgt
      exact (mem_sdiff.mp hj).2 ((hP (k + 1) j).mpr fun j' hj' =>
        (hP (k + 1) jmin).mp hjmin j' (hgt.le.trans hj'))
    have hsplit_sum : ∑ j ∈ P k, G.speed j =
        (∑ j ∈ P (k + 1), G.speed j) + (∑ j ∈ P k \ P (k + 1), G.speed j) := by
      rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hsub]
    have hlhs : (#(P (k + 1)) : ℝ) * smin ≤ ∑ j ∈ P (k + 1), G.speed j :=
      calc (#(P (k + 1)) : ℝ) * smin = ∑ _j ∈ P (k + 1), smin := by simp
        _ ≤ ∑ j ∈ P (k + 1), G.speed j := sum_le_sum fun j hj => hmin j hj
    have hrhs : ∑ j ∈ P k \ P (k + 1), G.speed j ≤ (#(P k \ P (k + 1)) : ℝ) * smin :=
      calc ∑ j ∈ P k \ P (k + 1), G.speed j
          ≤ ∑ _j ∈ P k \ P (k + 1), smin := sum_le_sum fun j hj => hsdiff_lt j hj
        _ = (#(P k \ P (k + 1)) : ℝ) * smin := by simp
    have hnat : k * #(P (k + 1)) ≤ #(P k \ P (k + 1)) := by
      rw [hsplit_sum] at hsum
      push_cast at hsum
      exact_mod_cast (by nlinarith [Nat.cast_nonneg (α := ℝ) k] :
        (k : ℝ) * (#(P (k + 1)) : ℝ) ≤ (#(P k \ P (k + 1)) : ℝ))
    rw [card_sdiff_of_subset hsub] at hnat
    have hcard_le := card_le_card hsub
    have hdist : (k + 1) * #(P (k + 1)) = k * #(P (k + 1)) + #(P (k + 1)) := by ring
    omega
  · simp [not_nonempty_iff_eq_empty.mp hne]

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
      have hrec := hrec_step (c - (d + 1))
      rw [show c - (d + 1) + 1 = c - d by omega] at hrec
      calc (c - d) * ((∏ r ∈ range d, (c - r)) * #(P c))
          ≤ (c - d) * #(P (c - d)) := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ #(P (c - (d + 1))) := hrec
  have hprod_eq : ∏ r ∈ range c, (c - r) = c.factorial := by
    rw [Nat.factorial_eq_prod_range_add_one, ← Finset.prod_range_reflect (fun r => r + 1) c]
    exact prod_congr rfl fun r hr => by rw [mem_range] at hr; omega
  calc c.factorial = (∏ r ∈ range c, (c - r)) * 1 := by rw [hprod_eq, mul_one]
    _ ≤ (∏ r ∈ range c, (c - r)) * #(P c) := Nat.mul_le_mul_left _ hPc
    _ ≤ #(P (c - c)) := hstep c le_rfl
    _ = #(P 0) := by rw [Nat.sub_self]
    _ ≤ Fintype.card M := card_le_univ _

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
  have hdiv : G.weight i / G.speed j' ≤ G.weight i / G.speed (Aopt i) :=
    div_le_div_of_nonneg_left (G.weight_nonneg i) (G.speed_pos (Aopt i)) hj'
  push_cast at hge
  linarith [hNE j', hAopt ▸ G.weight_div_speed_le_makespan Aopt i]

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
  have h1 : ((k + 1 : ℕ) : ℝ) * G.optMakespan * ∑ j ∈ G.speedPrefix A (k + 1), G.speed j ≤
      ∑ j ∈ G.speedPrefix A (k + 1), G.speed j * G.load A j := by
    rw [mul_sum]
    exact sum_le_sum fun j hj => by
      nlinarith [(G.speed_pos j).le, G.mul_optMakespan_le_load_of_mem_speedPrefix A (k + 1) hj]
  have h3 : ∑ i with A i ∈ G.speedPrefix A (k + 1), G.weight i ≤
      ∑ i with Aopt i ∈ G.speedPrefix A k, G.weight i :=
    sum_le_sum_of_subset_of_nonneg (fun i hi => by
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      exact G.mem_speedPrefix_of_load_ge hA hAopt
        (G.mul_optMakespan_le_load_of_mem_speedPrefix A (k + 1) hi))
      fun i _ _ => G.weight_nonneg i
  rw [G.sum_speed_mul_load_eq_sum_weight] at h1
  have h4 := G.sum_weight_Aopt_mem_le hAopt (G.speedPrefix A k)
  exact le_of_mul_le_mul_left (by linarith) hopt

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
    have : (1 : ℝ) ≤ ((c + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos c
    rw [hjstar]; nlinarith
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, A i₀ = jstar := by
    by_contra! hnone
    rw [G.load_eq_sum_div, filter_false_of_mem fun i _ => hnone i, sum_empty, zero_div]
      at hpos_load
    exact hpos_load.false
  exact factorial_le_card_of_prefix_step (G.speedPrefix A) (G.card_speedPrefix_ge hA hopt)
    (card_pos.mpr ⟨Aopt i₀, G.mem_speedPrefix_of_load_ge hA hAopt (by rwa [hi₀, hjstar])⟩)

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
  have hlogm_gt1 : 1 < Real.log (m : ℝ) := Real.one_lt_log_of_three_le (by exact_mod_cast hm)
  have hloglog_pos : 0 < Real.log (Real.log (m : ℝ)) := Real.log_pos hlogm_gt1
  have hratio_pos : 0 < 4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by positivity
  by_cases hsmall : val ≤ 2 * opt
  · nlinarith
  · set q : ℕ := ⌊val / opt⌋₊
    have hq_ge2 : 2 ≤ q := (Nat.le_floor_iff (div_nonneg hval hopt.le)).mpr
      ((le_div_iff₀ hopt).mpr (by push_cast; linarith))
    set c : ℕ := q - 1
    have hge : ((c + 1 : ℕ) : ℝ) * opt ≤ val := by
      rw [show c + 1 = q by omega]
      exact (le_div_iff₀ hopt).mp (Nat.floor_le (div_nonneg hval hopt.le))
    set r : ℕ := c / 2
    have hpow : r ^ r ≤ m :=
      (pow_le_factorial_two_mul r).trans ((Nat.factorial_le (by omega)).trans (hfac c hge))
    have hr_lt : (r : ℝ) < 2 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by
      by_contra! hge_r
      set x : ℝ := Real.log (m : ℝ)
      have hlogx_lt : Real.log x < 2 * √x := by
        linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : 0 < x)),
          Real.log_sqrt (by linarith : 0 ≤ x)]
      have hsqrt_lt : √x < 2 * x / Real.log x := (lt_div_iff₀ hloglog_pos).mpr <| by
        nlinarith [Real.mul_self_sqrt (by linarith : 0 ≤ x),
          Real.sqrt_pos.mpr (by linarith : 0 < x)]
      have hr_gt_sqrt : √x < (r : ℝ) := hsqrt_lt.trans_le hge_r
      have hsqrt_gt1 : 1 < √x := Real.sqrt_one ▸ Real.sqrt_lt_sqrt (by norm_num) hlogm_gt1
      have hr_pos : (0 : ℝ) < r := by linarith
      have hlogr_gt : Real.log x / 2 < Real.log (r : ℝ) :=
        Real.log_sqrt (zero_lt_one.trans hlogm_gt1).le ▸
          Real.log_lt_log (zero_lt_one.trans hsqrt_gt1) hr_gt_sqrt
      have hmul_gt : x < (r : ℝ) * Real.log (r : ℝ) := by
        have h1 : (2 * x / Real.log x) * (Real.log x / 2) = x := by field_simp [hloglog_pos.ne']
        linarith [mul_le_mul_of_nonneg_right hge_r (by positivity : 0 ≤ Real.log x / 2),
          mul_lt_mul_of_pos_left hlogr_gt hr_pos]
      have hlog_pow : (r : ℝ) * Real.log (r : ℝ) ≤ x :=
        Real.log_pow (r : ℝ) r ▸ Real.log_le_log (pow_pos hr_pos r) (by exact_mod_cast hpow)
      linarith
    have hq_real : (q : ℝ) ≤ 2 * (r : ℝ) + 2 := by exact_mod_cast (by omega : q ≤ 2 * r + 2)
    have hval_lt : val < ((q : ℝ) + 1) * opt := (div_lt_iff₀ hopt).mp (Nat.lt_floor_add_one _)
    have h2 : 2 * (2 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ))) =
        4 * Real.log (m : ℝ) / Real.log (Real.log (m : ℝ)) := by ring
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
  have hNE : U.toCostGame.IsPureNash A := (U.isPureNash_iff A).mpr fun i k hk => by
    simp only [U, A, id_eq] at hk ⊢
    rw [hloadA, hloadA, ite_eq_right hk.symm]
    linarith
  have hmsA : U.makespan A = K := le_antisymm ((U.makespan_le_iff A).mpr fun j => (hloadA j).le)
    (hloadA 0 ▸ U.load_le_makespan A 0)
  have hopt : U.optMakespan = 1 := le_antisymm
    ((U.optMakespan_le Aopt).trans ((U.makespan_le_iff Aopt).mpr fun j => (hloadOpt j).le)) <| by
      obtain ⟨B, hB⟩ := U.exists_makespan_eq_optMakespan
      have hge1 : 1 ≤ U.procTime 0 (B 0) := by
        simp only [U]
        split_ifs <;> linarith
      exact hge1.trans ((U.procTime_le_load B 0).trans ((U.load_le_makespan B (B 0)).trans_eq hB))
  exact ⟨U, A, hNE, by rw [hmsA, hopt, mul_one], hopt⟩

end UnrelatedLoadBalancingGame

end Cslib.GameTheory

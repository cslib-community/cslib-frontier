/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Scheduling.IdenticalMachines
public import CslibFrontier.GameTheory.Strategic.Basic
public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Selfish load-balancing games (Koutsoupias–Papadimitriou model)

In a **selfish load-balancing game** ([KoutsoupiasPapadimitriou1999]; [Vocking2007]),
a finite set `ι` of selfish tasks (jobs) each choose one machine from a finite set `M`. Each job
pays the total load of the machine it selects, while the social objective is the **makespan**
(the maximum machine load).

This module defines two standard machine models:

* `Cslib.GameTheory.UnrelatedLoadBalancingGame`: **unrelated machines**, where job `i` incurs an
  arbitrary nonnegative processing time `procTime i j` on machine `j`.
* `Cslib.GameTheory.LoadBalancingGame`: **uniformly related machines**, where job `i` has
  nonnegative weight `weight i`, machine `j` has positive speed `speed j`, and the processing time
  of job `i` on machine `j` is `weight i / speed j`. **Identical machines** are the special case
  `IsIdentical` (`∀ j, speed j = 1`), constructed by `LoadBalancingGame.identical`.

Both models embed into `Cslib.GameTheory.CostGame` via `toCostGame`, so pure Nash equilibria
(`CostGame.IsPureNash`), improvement steps (`CostGame.Improves`), the finite improvement property
(`CostGame.HasFIP`), and mixed Nash equilibria (`CostGame.IsMixedNash`) are inherited directly
from `CslibFrontier.GameTheory.Strategic`. Note that `CostGame.socialCost` is the sum of player
costs, whereas the Koutsoupias–Papadimitriou social cost is `makespan` (for pure assignments) and
expected makespan (for mixed profiles, in `CslibFrontier.GameTheory.LoadBalancing.MixedNash`).

## Main definitions

* `Cslib.GameTheory.UnrelatedLoadBalancingGame`: load-balancing game on unrelated machines, with
  `load`, `makespan`, `optMakespan`, and `toCostGame`.
* `Cslib.GameTheory.LoadBalancingGame`: load-balancing game on uniformly related machines, with
  `identical`, `IsIdentical`, `toUnrelated`, `load`, `makespan`, `optMakespan`, and `toCostGame`.

## Main results

* `Cslib.GameTheory.UnrelatedLoadBalancingGame.isPureNash_iff`: pure Nash characterization for
  unrelated machines.
* `Cslib.GameTheory.LoadBalancingGame.isPureNash_iff` ([Vocking2007]): pure Nash
  characterization for uniformly related machines.
* `Cslib.GameTheory.LoadBalancingGame.sum_weight_le_sum_speed_mul_optMakespan`,
  `Cslib.GameTheory.LoadBalancingGame.weight_div_speed_le_makespan`: volume and single-job lower
  bounds on makespan and optimal makespan.
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.makespan_eq_scheduling`,
  `Cslib.GameTheory.LoadBalancingGame.IsIdentical.optMakespan_eq_scheduling`: exact agreement with
  `Cslib.Algorithms.Lean.Scheduling` on `Fin n` jobs and `Fin m` identical machines.

## References

* [KoutsoupiasPapadimitriou1999]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory

open Finset

/-- A selfish load-balancing game on **unrelated machines**: job `i : ι` has nonnegative
processing time `procTime i j` on machine `j : M`. -/
structure UnrelatedLoadBalancingGame (ι M : Type*) where
  /-- The processing time (load contribution) of job `i` on machine `j`. -/
  procTime : ι → M → ℝ
  /-- Processing times are nonnegative. -/
  procTime_nonneg : ∀ i j, 0 ≤ procTime i j

namespace UnrelatedLoadBalancingGame

variable {ι M : Type*} [Fintype ι] [DecidableEq M] (U : UnrelatedLoadBalancingGame ι M)

/-- The **load** of machine `j` under pure assignment `A`: the sum of processing times of all jobs
assigned to `j`. -/
@[expose] def load (A : ι → M) (j : M) : ℝ :=
  ∑ i with A i = j, U.procTime i j

/-- The strategic cost game induced by `U`: each job pays the load of its chosen machine. -/
@[expose] def toCostGame : CostGame ι (fun _ => M) where
  cost i A := U.load A (A i)

theorem load_nonneg (A : ι → M) (j : M) : 0 ≤ U.load A j :=
  sum_nonneg fun i _ => U.procTime_nonneg i j

theorem procTime_le_load (A : ι → M) (i : ι) : U.procTime i (A i) ≤ U.load A (A i) :=
  single_le_sum (f := fun k => U.procTime k (A i)) (fun k _ => U.procTime_nonneg k (A i))
    (mem_filter.mpr ⟨mem_univ i, rfl⟩)

/-- Load of a machine after moving job `i` to machine `k`. -/
theorem load_update [DecidableEq ι] (A : ι → M) (i : ι) (k j : M) :
    U.load (Function.update A i k) j =
      U.load A j - (if A i = j then U.procTime i j else 0) +
        (if k = j then U.procTime i j else 0) := by
  simp only [load, sum_filter, ← add_sum_erase _ _ (mem_univ i), Function.update_self]
  rw [sum_congr rfl fun r hr => by rw [Function.update_of_ne (ne_of_mem_erase hr)]]
  linarith

/-- Load of the target machine `k ≠ A i` after moving job `i` to `k`. -/
theorem load_update_of_ne [DecidableEq ι] (A : ι → M) (i : ι) {k : M} (hk : k ≠ A i) :
    U.load (Function.update A i k) k = U.load A k + U.procTime i k := by
  rw [U.load_update A i k k, ite_eq_right hk.symm, ite_eq_left rfl, sub_zero]

/-- Load of the vacated machine `A i` after moving job `i` to `k ≠ A i`. -/
theorem load_update_self_of_ne [DecidableEq ι] (A : ι → M) (i : ι) {k : M} (hk : k ≠ A i) :
    U.load (Function.update A i k) (A i) = U.load A (A i) - U.procTime i (A i) := by
  rw [U.load_update A i k (A i), ite_eq_left rfl, ite_eq_right hk, add_zero]

/-- Load of any machine unaffected by moving job `i` to `k`. -/
theorem load_update_other [DecidableEq ι] (A : ι → M) (i : ι) {k j : M}
    (h1 : j ≠ A i) (h2 : j ≠ k) :
    U.load (Function.update A i k) j = U.load A j := by
  rw [U.load_update A i k j, ite_eq_right h1.symm, ite_eq_right h2.symm, sub_zero, add_zero]

/-- Pure Nash equilibrium characterization on unrelated machines: no job can strictly reduce its
machine's load by unilaterally moving to another machine. -/
theorem isPureNash_iff [DecidableEq ι] (A : ι → M) :
    U.toCostGame.IsPureNash A ↔
      ∀ i k, k ≠ A i → U.load A (A i) ≤ U.load A k + U.procTime i k := by
  constructor
  · intro h i k hk
    have hi := h i k
    simpa only [toCostGame, Function.update_self, U.load_update_of_ne A i hk] using hi
  · intro h i k
    by_cases hk : k = A i
    · subst hk
      simp [toCostGame]
    · simpa only [toCostGame, Function.update_self, U.load_update_of_ne A i hk] using h i k hk

section Makespan

variable [Fintype M] [Nonempty M]

/-- The **makespan** (social cost) of assignment `A`: the maximum machine load. -/
def makespan (A : ι → M) : ℝ :=
  univ.sup' univ_nonempty (U.load A)

/-- The **optimal makespan** `OPT(U)`: the minimum makespan over all pure assignments. -/
noncomputable def optMakespan [DecidableEq ι] : ℝ :=
  (univ : Finset (ι → M)).inf' univ_nonempty U.makespan

theorem makespan_def (A : ι → M) : U.makespan A = univ.sup' univ_nonempty (U.load A) := by
  rw [makespan]

theorem load_le_makespan (A : ι → M) (j : M) : U.load A j ≤ U.makespan A :=
  le_sup' _ (mem_univ j)

theorem makespan_le_iff (A : ι → M) {B : ℝ} : U.makespan A ≤ B ↔ ∀ j, U.load A j ≤ B := by
  simp [makespan]

theorem makespan_nonneg (A : ι → M) : 0 ≤ U.makespan A :=
  let ⟨j⟩ := ‹Nonempty M›
  (U.load_nonneg A j).trans (U.load_le_makespan A j)

theorem exists_load_eq_makespan (A : ι → M) : ∃ j : M, U.load A j = U.makespan A :=
  let ⟨j, _, hj⟩ := exists_mem_eq_sup' (univ_nonempty (α := M)) (U.load A)
  ⟨j, hj.symm⟩

theorem optMakespan_le [DecidableEq ι] (A : ι → M) : U.optMakespan ≤ U.makespan A :=
  inf'_le _ (mem_univ A)

theorem exists_makespan_eq_optMakespan [DecidableEq ι] :
    ∃ A : ι → M, U.makespan A = U.optMakespan :=
  let ⟨A, _, hA⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι → M)) U.makespan
  ⟨A, hA.symm⟩

theorem optMakespan_nonneg [DecidableEq ι] : 0 ≤ U.optMakespan :=
  let ⟨A, hA⟩ := U.exists_makespan_eq_optMakespan
  hA ▸ U.makespan_nonneg A

end Makespan

end UnrelatedLoadBalancingGame

/-- A selfish load-balancing game on **uniformly related machines**
([KoutsoupiasPapadimitriou1999]; [Vocking2007]): job `i : ι` has nonnegative weight
`weight i`, machine `j : M` has positive speed `speed j`, and assigning job `i` to machine `j`
adds `weight i / speed j` to machine `j`'s load. -/
structure LoadBalancingGame (ι M : Type*) where
  /-- The weight (size) of job `i`. -/
  weight : ι → ℝ
  /-- The speed of machine `j`. -/
  speed : M → ℝ
  /-- Every job has nonnegative weight. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Every machine has positive speed. -/
  speed_pos : ∀ j, 0 < speed j

namespace LoadBalancingGame

variable {ι M : Type*}

/-- Construct a load-balancing game on **identical machines** (all speeds equal to `1`). -/
@[expose] def identical (weight : ι → ℝ) (weight_nonneg : ∀ i, 0 ≤ weight i) :
    LoadBalancingGame ι M where
  weight := weight
  speed _ := 1
  weight_nonneg := weight_nonneg
  speed_pos _ := zero_lt_one

/-- Predicate asserting that all machines are **identical** (have unit speed `1`). -/
@[expose] def IsIdentical (G : LoadBalancingGame ι M) : Prop :=
  ∀ j, G.speed j = 1

theorem isIdentical_identical (weight : ι → ℝ) (weight_nonneg : ∀ i, 0 ≤ weight i) :
    (identical (M := M) weight weight_nonneg).IsIdentical :=
  fun _ => rfl

/-- View a uniformly related load-balancing game as an unrelated load-balancing game with
processing times `weight i / speed j`. -/
@[expose] noncomputable def toUnrelated (G : LoadBalancingGame ι M) :
    UnrelatedLoadBalancingGame ι M where
  procTime i j := G.weight i / G.speed j
  procTime_nonneg i j := div_nonneg (G.weight_nonneg i) (G.speed_pos j).le

variable [Fintype ι] [DecidableEq M] (G : LoadBalancingGame ι M)

/-- The **load** of machine `j` under assignment `A`:
`(∑ i with A i = j, weight i) / speed j = ∑ i with A i = j, weight i / speed j`. -/
@[expose] noncomputable def load (A : ι → M) (j : M) : ℝ :=
  G.toUnrelated.load A j

/-- The strategic cost game induced by `G`: each job pays the load of its chosen machine. -/
@[expose] noncomputable def toCostGame : CostGame ι (fun _ => M) :=
  G.toUnrelated.toCostGame

theorem load_eq_sum_div (A : ι → M) (j : M) :
    G.load A j = (∑ i with A i = j, G.weight i) / G.speed j :=
  (sum_div _ _ _).symm

theorem load_nonneg (A : ι → M) (j : M) : 0 ≤ G.load A j :=
  G.toUnrelated.load_nonneg A j

theorem weight_div_speed_le_load (A : ι → M) (i : ι) :
    G.weight i / G.speed (A i) ≤ G.load A (A i) :=
  G.toUnrelated.procTime_le_load A i

theorem speed_mul_load (A : ι → M) (j : M) :
    G.speed j * G.load A j = ∑ i with A i = j, G.weight i := by
  rw [G.load_eq_sum_div, mul_div_cancel₀ _ (G.speed_pos j).ne']

/-- Total speed-weighted load equals total job weight: `∑ j, speed j * load A j = ∑ i, weight i`.
-/
theorem sum_speed_mul_load [Fintype M] (A : ι → M) :
    ∑ j, G.speed j * G.load A j = ∑ i, G.weight i := by
  simp_rw [G.speed_mul_load]
  exact sum_fiberwise univ A G.weight

/-- On identical machines, the machine loads sum to the total job weight. -/
theorem IsIdentical.sum_load [Fintype M] {G : LoadBalancingGame ι M} (hId : G.IsIdentical)
    (A : ι → M) : ∑ j, G.load A j = ∑ i, G.weight i := by
  have h := G.sum_speed_mul_load A
  simp_rw [hId _, one_mul] at h
  exact h

theorem load_update_of_ne [DecidableEq ι] (A : ι → M) (i : ι) {k : M} (hk : k ≠ A i) :
    G.load (Function.update A i k) k = G.load A k + G.weight i / G.speed k :=
  G.toUnrelated.load_update_of_ne A i hk

theorem load_update_self_of_ne [DecidableEq ι] (A : ι → M) (i : ι) {k : M} (hk : k ≠ A i) :
    G.load (Function.update A i k) (A i) = G.load A (A i) - G.weight i / G.speed (A i) :=
  G.toUnrelated.load_update_self_of_ne A i hk

theorem load_update_other [DecidableEq ι] (A : ι → M) (i : ι) {k j : M}
    (h1 : j ≠ A i) (h2 : j ≠ k) :
    G.load (Function.update A i k) j = G.load A j :=
  G.toUnrelated.load_update_other A i h1 h2

/-- **Pure Nash equilibrium characterization** ([Vocking2007]): an assignment `A`
is a pure Nash equilibrium if and only if no job `i` can strictly lower its load by switching to
another machine `k`. -/
theorem isPureNash_iff [DecidableEq ι] (A : ι → M) :
    G.toCostGame.IsPureNash A ↔
      ∀ i k, k ≠ A i → G.load A (A i) ≤ G.load A k + G.weight i / G.speed k :=
  G.toUnrelated.isPureNash_iff A

/-- Unconditional pure Nash inequality: for every job `i` and machine `k` (including `k = A i`),
`load A (A i) ≤ load A k + weight i / speed k`. -/
theorem isPureNash_load_le [DecidableEq ι] {G : LoadBalancingGame ι M} {A : ι → M}
    (hA : G.toCostGame.IsPureNash A) (i : ι) (k : M) :
    G.load A (A i) ≤ G.load A k + G.weight i / G.speed k := by
  by_cases hk : k = A i
  · subst hk
    linarith [div_nonneg (G.weight_nonneg i) (G.speed_pos (A i)).le]
  · exact (G.isPureNash_iff A).mp hA i k hk

section Makespan

variable [Fintype M] [Nonempty M]

/-- The **makespan** (social cost) of assignment `A`: the maximum load over all machines. -/
@[expose] noncomputable def makespan (A : ι → M) : ℝ :=
  G.toUnrelated.makespan A

/-- The **optimal makespan** `OPT(G)` ([Vocking2007]): the minimum makespan over
all pure assignments. -/
@[expose] noncomputable def optMakespan [DecidableEq ι] : ℝ :=
  G.toUnrelated.optMakespan

theorem load_le_makespan (A : ι → M) (j : M) : G.load A j ≤ G.makespan A :=
  G.toUnrelated.load_le_makespan A j

theorem makespan_le_iff (A : ι → M) {B : ℝ} : G.makespan A ≤ B ↔ ∀ j, G.load A j ≤ B :=
  G.toUnrelated.makespan_le_iff A

theorem makespan_nonneg (A : ι → M) : 0 ≤ G.makespan A :=
  G.toUnrelated.makespan_nonneg A

theorem exists_load_eq_makespan (A : ι → M) : ∃ j : M, G.load A j = G.makespan A :=
  G.toUnrelated.exists_load_eq_makespan A

theorem optMakespan_le [DecidableEq ι] (A : ι → M) : G.optMakespan ≤ G.makespan A :=
  G.toUnrelated.optMakespan_le A

theorem exists_makespan_eq_optMakespan [DecidableEq ι] :
    ∃ A : ι → M, G.makespan A = G.optMakespan :=
  G.toUnrelated.exists_makespan_eq_optMakespan

theorem optMakespan_nonneg [DecidableEq ι] : 0 ≤ G.optMakespan :=
  G.toUnrelated.optMakespan_nonneg

/-- Volume lower bound: total job weight is at most `(∑ j, speed j) * makespan A`. -/
theorem sum_weight_le_sum_speed_mul_makespan (A : ι → M) :
    ∑ i, G.weight i ≤ (∑ j, G.speed j) * G.makespan A := by
  rw [← G.sum_speed_mul_load A, sum_mul]
  exact sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (G.load_le_makespan A j) (G.speed_pos j).le

/-- Volume lower bound against the optimum: `∑ i, weight i ≤ (∑ j, speed j) * optMakespan`. -/
theorem sum_weight_le_sum_speed_mul_optMakespan [DecidableEq ι] :
    ∑ i, G.weight i ≤ (∑ j, G.speed j) * G.optMakespan :=
  let ⟨A, hA⟩ := G.exists_makespan_eq_optMakespan
  hA ▸ G.sum_weight_le_sum_speed_mul_makespan A

/-- On identical machines, total job weight is at most `|M| * optMakespan`. -/
theorem IsIdentical.sum_weight_le_card_mul_optMakespan [DecidableEq ι]
    {G : LoadBalancingGame ι M} (hId : G.IsIdentical) :
    ∑ i, G.weight i ≤ (Fintype.card M : ℝ) * G.optMakespan := by
  have h := G.sum_weight_le_sum_speed_mul_optMakespan
  simp_rw [hId _, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  exact h

/-- Single-job lower bound: `weight i / speed (A i) ≤ makespan A`. -/
theorem weight_div_speed_le_makespan (A : ι → M) (i : ι) :
    G.weight i / G.speed (A i) ≤ G.makespan A :=
  (G.weight_div_speed_le_load A i).trans (G.load_le_makespan A (A i))

/-- On identical machines, every job's weight is at most `optMakespan`. -/
theorem IsIdentical.weight_le_optMakespan [DecidableEq ι] {G : LoadBalancingGame ι M}
    (hId : G.IsIdentical) (i : ι) : G.weight i ≤ G.optMakespan := by
  obtain ⟨A, hA⟩ := G.exists_makespan_eq_optMakespan
  rw [← hA]
  have h := G.weight_div_speed_le_makespan A i
  rw [hId (A i), div_one] at h
  exact h

/-- When `optMakespan = 0`, every job has weight `0`. -/
theorem weight_eq_zero_of_optMakespan_eq_zero [DecidableEq ι] (hopt0 : G.optMakespan = 0)
    (i : ι) : G.weight i = 0 := by
  have hsum := G.sum_weight_le_sum_speed_mul_optMakespan
  rw [hopt0, mul_zero] at hsum
  exact (sum_eq_zero_iff_of_nonneg fun k _ => G.weight_nonneg k).mp
    (le_antisymm hsum (sum_nonneg fun r _ => G.weight_nonneg r)) i (mem_univ i)

/-- When some job `i` has strictly positive weight, `0 < optMakespan`. -/
theorem optMakespan_pos_of_weight_pos [DecidableEq ι] {i : ι} (hi : 0 < G.weight i) :
    0 < G.optMakespan :=
  G.optMakespan_nonneg.lt_of_ne' fun h0 => hi.ne' (G.weight_eq_zero_of_optMakespan_eq_zero h0 i)

/-- When `optMakespan = 0`, every assignment has makespan `0`. -/
theorem makespan_eq_zero_of_optMakespan_eq_zero [DecidableEq ι] (hopt0 : G.optMakespan = 0)
    (A : ι → M) : G.makespan A = 0 :=
  le_antisymm ((G.makespan_le_iff A).mpr fun j => by
    simp [G.load_eq_sum_div, G.weight_eq_zero_of_optMakespan_eq_zero hopt0]) (G.makespan_nonneg A)

end Makespan

section SchedulingBridge

variable {n m : ℕ}

/-- On identical machines (`Fin n` jobs, `Fin m` machines), `LoadBalancingGame.load` agrees with
`Cslib.Algorithms.Lean.Scheduling.load`. -/
theorem IsIdentical.load_eq_scheduling {G : LoadBalancingGame (Fin n) (Fin m)}
    (hId : G.IsIdentical) (A : Fin n → Fin m) (j : Fin m) :
    G.load A j = Cslib.Algorithms.Lean.Scheduling.load G.weight A j := by
  rw [G.load_eq_sum_div, hId j, div_one, Cslib.Algorithms.Lean.Scheduling.load_def]

/-- On identical machines, `LoadBalancingGame.makespan` agrees with
`Cslib.Algorithms.Lean.Scheduling.makespan`. -/
theorem IsIdentical.makespan_eq_scheduling [NeZero m] {G : LoadBalancingGame (Fin n) (Fin m)}
    (hId : G.IsIdentical) (A : Fin n → Fin m) :
    G.makespan A = Cslib.Algorithms.Lean.Scheduling.makespan G.weight A := by
  rw [makespan, UnrelatedLoadBalancingGame.makespan_def,
    Cslib.Algorithms.Lean.Scheduling.makespan_def]
  congr 1
  funext j
  exact hId.load_eq_scheduling A j

/-- On identical machines, `LoadBalancingGame.optMakespan` agrees with
`Cslib.Algorithms.Lean.Scheduling.optMakespan`. -/
theorem IsIdentical.optMakespan_eq_scheduling [NeZero m] {G : LoadBalancingGame (Fin n) (Fin m)}
    (hId : G.IsIdentical) :
    G.optMakespan = Cslib.Algorithms.Lean.Scheduling.optMakespan m G.weight := by
  refine le_antisymm ?_ ?_
  · obtain ⟨A, hA⟩ := Cslib.Algorithms.Lean.Scheduling.exists_makespan_eq_optMakespan (m := m)
      G.weight
    rw [← hA, ← hId.makespan_eq_scheduling A]
    exact G.optMakespan_le A
  · obtain ⟨A, hA⟩ := G.exists_makespan_eq_optMakespan
    rw [← hA, hId.makespan_eq_scheduling A]
    exact Cslib.Algorithms.Lean.Scheduling.optMakespan_le G.weight A

end SchedulingBridge

end LoadBalancingGame

end Cslib.GameTheory

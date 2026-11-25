/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Scheduling.IdenticalMachines
public import CslibFrontier.GameTheory.Mechanism.VCG
public import CslibFrontier.GameTheory.Mechanism.Vickrey
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Truthful Makespan Scheduling on Unrelated Machines

In the **unrelated-machine scheduling mechanism design problem** ([NisanRonen2001]; [Lavi2007],
Section 12.2 and Exercise 12.2), a set of jobs `Job` must be partitioned among strategic machines
`Machine`. Each machine `i` privately knows its processing-time vector `t i : Job → ℝ` (`t i j` is
the time machine `i` needs to process job `j`), incurs cost equal to its assigned load
`∑ j with σ j = i, t i j`, and has quasilinear utility `pay t i - load t σ i`. Meanwhile, the
designer seeks a schedule `σ : Job → Machine` whose `makespan` (`max_i load t σ i`) approximates
`optMakespan t` (`min_σ makespan t σ`).

This module formalizes the unrelated-machine scheduling mechanism model, its connection to general
quasilinear Groves mechanisms (`Cslib.GameTheory.Mechanism.groves`), and the two foundational
deterministic results of Nisan and Ronen ([NisanRonen2001]):

1. **The `MinWork` (VCG / Groves) `n`-approximation mechanism** ([NisanRonen2001], Theorem 4.1,
   Claims 4.2 and 4.3; polynomial-time computability in Theorem 4.1 is not modeled here since
   `minWorkAlloc` and `minWorkMechanism` are `noncomputable` over `ℝ`):
   - `minWorkAlloc` assigns each job `j` independently to the machine minimizing `t i j` (breaking
     ties in favor of the smallest machine index), and `minWorkMechanism` pays each machine `i` the
     second-lowest processing time `secondLowestTime t i j` (`min_{k ≠ i} t k j`) for every job `j`
     assigned to `i`.
   - `minWorkMechanism` is a Groves mechanism (`GameTheory.Mechanism.groves`) on negated-load
     valuations with the machine-excluding Clarke pivot `- ∑ j, secondLowestTime t i j`
     (`groves_payment_schedulingProfile`, `exists_groves_eq_minWorkMechanism`), is
     dominant-strategy incentive compatible on all real profiles (`minWorkMechanism_isDSIC`), is
     individually rational when `[Nontrivial Machine]` (`minWorkMechanism_isIR`), and achieves an
     `n`-approximation (`n = Fintype.card Machine`) to `optMakespan` on all nonnegative profiles
     (`makespan_minWorkAlloc_le_card_mul_optMakespan`,
     `minWorkMechanism_hasApproxRatioOn_nonneg`).
   - This `n`-approximation bound for `minWorkMechanism` is tight up to any `ε > 0` for every
     `n ≥ 1` (`card_le_of_minWorkMechanism_hasApproxRatioOn`).
2. **Weak Monotonicity and the Nisan–Ronen `2`-approximation lower bound** ([NisanRonen2001],
   Section 2 and Theorem 4.4; [Lavi2007], Exercise 12.2):
   - Every DSIC scheduling mechanism satisfies weak monotonicity
     (`Mechanism.IsDSICOn.rowLoad_sub_le`), which implies **task-set invariance**
     (`Mechanism.IsDSICOn.alloc_eq_iff_of_lt_of_gt`): if machine `i` strictly decreases its
     processing times on jobs assigned to `i` and strictly increases them on jobs not assigned to
     `i`, then `i` must receive the exact same set of jobs.
   - Using two successive unilateral perturbations from a balanced three-job core, **no
     deterministic mechanism that is DSIC even on strictly positive profiles can achieve a makespan
     approximation ratio `c < 2`** whenever `2 ≤ Fintype.card Machine` and `3 ≤ Fintype.card Job`
     (`two_le_of_isDSICOn_positive_of_hasApproxRatioOn`).
   - Boundary sharpness: when `Fintype.card Machine = 1` (`[Subsingleton Machine]`,
     `makespan_eq_optMakespan_of_subsingleton_machine`) or `Fintype.card Job ≤ 1`
     (`[Subsingleton Job]`, `makespan_minWorkAlloc_eq_optMakespan_of_subsingleton_job`),
     `minWorkMechanism` achieves exact `1`-approximation (`makespan = optMakespan`).

## Main definitions

* `Cslib.GameTheory.Scheduling.rowLoad`, `Cslib.GameTheory.Scheduling.load`,
  `Cslib.GameTheory.Scheduling.totalWork`, `Cslib.GameTheory.Scheduling.makespan`,
  `Cslib.GameTheory.Scheduling.optMakespan`: machine loads (compatible with
  `Cslib.Algorithms.Lean.Scheduling.load` via `load_const_eq`), total work, makespan, and optimal
  makespan on unrelated machines.
* `Cslib.GameTheory.Scheduling.IsNonnegProfile`, `Cslib.GameTheory.Scheduling.IsPositiveProfile`:
  nonnegative and strictly positive processing-time domains.
* `Cslib.GameTheory.Scheduling.Mechanism`: direct-revelation scheduling mechanism `(alloc, pay)`
  with `utility`, `IsDSIC`, `IsDSICOn`, `IsIR`, and `HasApproxRatioOn`.
* `Cslib.GameTheory.Scheduling.schedulingVal`, `Cslib.GameTheory.Scheduling.schedulingProfile`,
  `Cslib.GameTheory.Scheduling.ofGeneralMechanism`: embedding into `Cslib.GameTheory.Mechanism`.
* `Cslib.GameTheory.Scheduling.minWorkAlloc`,
  `Cslib.GameTheory.Scheduling.secondLowestTime`, `Cslib.GameTheory.Scheduling.minWorkMechanism`:
  Nisan–Ronen's `MinWork` VCG mechanism.

## Main results

* `Cslib.GameTheory.Scheduling.Mechanism.IsDSICOn.rowLoad_sub_le`,
  `Cslib.GameTheory.Scheduling.Mechanism.IsDSICOn.alloc_eq_iff_of_lt_of_gt`: weak monotonicity and
  Nisan–Ronen task-set invariance under strict decrease/increase perturbations.
* `Cslib.GameTheory.Scheduling.minWorkMechanism_isDSIC`,
  `Cslib.GameTheory.Scheduling.minWorkMechanism_isIR`: truthfulness (Claim 4.2) and individual
  rationality of `MinWork`.
* `Cslib.GameTheory.Scheduling.groves_payment_schedulingProfile`,
  `Cslib.GameTheory.Scheduling.exists_groves_eq_minWorkMechanism`: `MinWork` is a Groves VCG
  mechanism on negated-load valuations with the machine-excluding Clarke pivot.
* `Cslib.GameTheory.Scheduling.makespan_minWorkAlloc_le_card_mul_optMakespan`,
  `Cslib.GameTheory.Scheduling.minWorkMechanism_hasApproxRatioOn_nonneg`,
  `Cslib.GameTheory.Scheduling.card_le_of_minWorkMechanism_hasApproxRatioOn`: `MinWork` is a tight
  `n`-approximation to optimal makespan (Claim 4.3 and Theorem 4.1).
* `Cslib.GameTheory.Scheduling.two_le_of_isDSICOn_positive_of_hasApproxRatioOn`: Nisan–Ronen `2`
  lower bound for all deterministic truthful unrelated-machine mechanisms when `2 ≤ |Machine|` and
  `3 ≤ |Job|` (Theorem 4.4; [Lavi2007], Exercise 12.2).

## References

* [N. Nisan, A. Ronen, *Algorithmic Mechanism Design*][NisanRonen2001], Section 2, Theorem 4.1,
  Claims 4.2–4.3, and Theorem 4.4
* [R. Lavi, *Computationally Efficient Approximation Mechanisms*][Lavi2007], Section 12.2 and
  Exercise 12.2
* [N. Nisan, *Introduction to Mechanism Design (for Computer Scientists)*][Nisan2007]
-/

public section

namespace Cslib.GameTheory.Scheduling

open Finset

/-! ### Loads, total work, makespan, and optimal makespan -/

section Objective

/-- Nonnegative processing-time matrices (`∀ i j, 0 ≤ t i j`). -/
@[expose] def IsNonnegProfile {Machine Job : Type*} (t : Machine → Job → ℝ) : Prop :=
  ∀ i j, 0 ≤ t i j

/-- Strictly positive processing-time matrices (`∀ i j, 0 < t i j`). -/
@[expose] def IsPositiveProfile {Machine Job : Type*} (t : Machine → Job → ℝ) : Prop :=
  ∀ i j, 0 < t i j

theorem IsPositiveProfile.isNonnegProfile {Machine Job : Type*} {t : Machine → Job → ℝ}
    (ht : IsPositiveProfile t) : IsNonnegProfile t :=
  fun i j => (ht i j).le

private theorem IsPositiveProfile.update {Machine Job : Type*} [DecidableEq Machine]
    {t : Machine → Job → ℝ} (ht : IsPositiveProfile t) {i : Machine} {r : Job → ℝ}
    (hr : ∀ j, 0 < r j) :
    IsPositiveProfile (Function.update t i r) := fun k j => by
  rcases eq_or_ne k i with rfl | hne
  · simpa using hr j
  · simpa [Function.update_of_ne hne] using ht k j

variable {Machine Job : Type*} [Fintype Job]

/-- Total processing time incurred by machine `i` with row `r : Job → ℝ` under schedule
`σ : Job → Machine`. -/
@[expose] def rowLoad [DecidableEq Machine] (i : Machine) (r : Job → ℝ) (σ : Job → Machine) : ℝ :=
  ∑ j with σ j = i, r j

/-- Load of machine `i` on processing-time matrix `t : Machine → Job → ℝ` under schedule `σ`. -/
@[expose] def load [DecidableEq Machine] (t : Machine → Job → ℝ) (σ : Job → Machine)
    (i : Machine) : ℝ :=
  rowLoad i (t i) σ

/-- Compatibility with `Cslib.Algorithms.Lean.Scheduling.load`: when processing times `p` do not
depend on the machine, `load` reduces to identical-machine load. -/
theorem load_const_eq {n m : ℕ} (p : Fin n → ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    load (fun _ => p) σ i = Cslib.Algorithms.Lean.Scheduling.load p σ i := by
  rw [load, rowLoad, Cslib.Algorithms.Lean.Scheduling.load_def]

/-- Total work `∑ j, t (σ j) j` across all jobs under schedule `σ`. -/
@[expose] def totalWork (t : Machine → Job → ℝ) (σ : Job → Machine) : ℝ :=
  ∑ j, t (σ j) j

theorem rowLoad_nonneg [DecidableEq Machine] {i : Machine} {r : Job → ℝ}
    (hr : ∀ j, 0 ≤ r j) (σ : Job → Machine) : 0 ≤ rowLoad i r σ :=
  Finset.sum_nonneg fun j _ => hr j

theorem load_nonneg [DecidableEq Machine] {t : Machine → Job → ℝ} (ht : IsNonnegProfile t)
    (σ : Job → Machine) (i : Machine) : 0 ≤ load t σ i :=
  rowLoad_nonneg (ht i) σ

section FiniteMachines

variable [Fintype Machine] [DecidableEq Machine]

/-- Machine loads partition all jobs, summing to `totalWork t σ`. -/
theorem sum_load_eq_totalWork (t : Machine → Job → ℝ) (σ : Job → Machine) :
    ∑ i, load t σ i = totalWork t σ := by
  unfold load rowLoad totalWork
  have hcongr : ∀ i : Machine, (∑ j with σ j = i, t i j) = ∑ j with σ j = i, t (σ j) j :=
    fun i => Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
  simp_rw [hcongr]
  exact Finset.sum_fiberwise Finset.univ σ fun j => t (σ j) j

section NonemptyMachines

variable [Nonempty Machine]

/-- The **makespan** `max_i load t σ i` of schedule `σ` under processing times `t`. -/
@[expose] noncomputable def makespan (t : Machine → Job → ℝ) (σ : Job → Machine) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (load t σ)

theorem load_le_makespan (t : Machine → Job → ℝ) (σ : Job → Machine) (i : Machine) :
    load t σ i ≤ makespan t σ :=
  Finset.le_sup' (load t σ) (Finset.mem_univ i)

private theorem entry_le_makespan {t : Machine → Job → ℝ} (ht : IsNonnegProfile t)
    (σ : Job → Machine) (j : Job) : t (σ j) j ≤ makespan t σ := by
  refine le_trans ?_ (load_le_makespan t σ (σ j))
  unfold load rowLoad
  exact Finset.single_le_sum (fun l _ => ht (σ j) l) (by simp)

theorem makespan_le_iff {t : Machine → Job → ℝ} {σ : Job → Machine} {B : ℝ} :
    makespan t σ ≤ B ↔ ∀ i, load t σ i ≤ B := by
  simp [makespan]

theorem exists_load_eq_makespan (t : Machine → Job → ℝ) (σ : Job → Machine) :
    ∃ i, load t σ i = makespan t σ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (load t σ)
  exact ⟨i, hi.symm⟩

theorem makespan_nonneg {t : Machine → Job → ℝ} (ht : IsNonnegProfile t) (σ : Job → Machine) :
    0 ≤ makespan t σ :=
  let ⟨i⟩ := ‹Nonempty Machine›
  (load_nonneg ht σ i).trans (load_le_makespan t σ i)

/-- On nonnegative profiles, `makespan` is bounded above by `totalWork`. -/
theorem makespan_le_totalWork {t : Machine → Job → ℝ} (ht : IsNonnegProfile t)
    (σ : Job → Machine) : makespan t σ ≤ totalWork t σ := by
  rw [makespan_le_iff, ← sum_load_eq_totalWork]
  intro i
  exact Finset.single_le_sum (fun k _ => load_nonneg ht σ k) (Finset.mem_univ i)

/-- Total work is at most `|Machine| * makespan`. -/
theorem totalWork_le_card_mul_makespan (t : Machine → Job → ℝ) (σ : Job → Machine) :
    totalWork t σ ≤ (Fintype.card Machine : ℝ) * makespan t σ := by
  rw [← sum_load_eq_totalWork]
  calc
    ∑ i, load t σ i ≤ ∑ _i : Machine, makespan t σ :=
      Finset.sum_le_sum fun i _ => load_le_makespan t σ i
    _ = (Fintype.card Machine : ℝ) * makespan t σ := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The **optimal makespan** `min_σ makespan t σ` over all schedules `σ : Job → Machine`. -/
@[expose] noncomputable def optMakespan (t : Machine → Job → ℝ) : ℝ :=
  letI := Classical.decEq Job
  Finset.univ.inf' Finset.univ_nonempty (makespan t)

theorem optMakespan_le_makespan (t : Machine → Job → ℝ) (σ : Job → Machine) :
    optMakespan t ≤ makespan t σ := by
  classical
  exact Finset.inf'_le (makespan t) (Finset.mem_univ σ)

theorem le_optMakespan_iff {t : Machine → Job → ℝ} {B : ℝ} :
    B ≤ optMakespan t ↔ ∀ σ, B ≤ makespan t σ := by
  classical
  simp [optMakespan]

theorem exists_makespan_eq_optMakespan (t : Machine → Job → ℝ) :
    ∃ σ : Job → Machine, makespan t σ = optMakespan t := by
  classical
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (makespan t)
  exact ⟨σ, hσ.symm⟩

theorem optMakespan_nonneg {t : Machine → Job → ℝ} (ht : IsNonnegProfile t) :
    0 ≤ optMakespan t :=
  le_optMakespan_iff.mpr (makespan_nonneg ht)

end NonemptyMachines

end FiniteMachines

end Objective

/-! ### Direct-revelation scheduling mechanisms and VCG bridge -/

/-- A deterministic direct-revelation **unrelated-machine scheduling mechanism**: on reported
processing-time rows `b : Machine → Job → ℝ`, it chooses a schedule `alloc b : Job → Machine` and
pays compensation `pay b i : ℝ` to each machine `i`. -/
structure Mechanism (Machine Job : Type*) where
  /-- The schedule allocation rule. -/
  alloc : (Machine → Job → ℝ) → (Job → Machine)
  /-- Compensation paid to machine `i`. -/
  pay : (Machine → Job → ℝ) → Machine → ℝ

namespace Mechanism

section Incentives

variable {Machine Job : Type*} [Fintype Job] [DecidableEq Machine]
  (M : Mechanism Machine Job)

/-- Quasilinear utility `pay b i - rowLoad i r (alloc b)` of machine `i` with true processing-time
row `r : Job → ℝ` when the reported profile is `b`. -/
@[expose] def utility (i : Machine) (r : Job → ℝ) (b : Machine → Job → ℝ) : ℝ :=
  M.pay b i - rowLoad i r (M.alloc b)

/-- **Dominant-strategy incentive compatibility (truthfulness)** across all real processing-time
profiles ([NisanRonen2001], Section 2). -/
@[expose] def IsDSIC : Prop :=
  ∀ (i : Machine) (b : Machine → Job → ℝ) (r : Job → ℝ),
    M.utility i r b ≤ M.utility i r (Function.update b i r)

/-- **Dominant-strategy incentive compatibility restricted to row domains `D`**. -/
@[expose] def IsDSICOn (D : Machine → Set (Job → ℝ)) : Prop :=
  ∀ (i : Machine) (b : Machine → Job → ℝ) (r : Job → ℝ),
    (∀ k, b k ∈ D k) → r ∈ D i →
      M.utility i r b ≤ M.utility i r (Function.update b i r)

theorem IsDSIC.isDSICOn {M : Mechanism Machine Job} (h : M.IsDSIC)
    (D : Machine → Set (Job → ℝ)) : M.IsDSICOn D :=
  fun i b r _ _ => h i b r

/-- **Individual rationality (voluntary participation)**: every truthful machine receives
nonnegative net utility `0 ≤ pay t i - load t (alloc t) i`. -/
@[expose] def IsIR : Prop :=
  ∀ (i : Machine) (t : Machine → Job → ℝ), 0 ≤ M.utility i (t i) t

/-- Worst-case **makespan approximation ratio `c`** on profiles satisfying `P`
([NisanRonen2001], Definition 2.4). -/
@[expose] def HasApproxRatioOn [Fintype Machine] [Nonempty Machine]
    (P : (Machine → Job → ℝ) → Prop) (c : ℝ) : Prop :=
  ∀ t, P t → makespan t (M.alloc t) ≤ c * optMakespan t

/-! ### Weak monotonicity and Nisan–Ronen task-set invariance -/

/-- **Weak monotonicity (WMON)** for scheduling mechanisms ([NisanRonen2001], Section 2;
[Lavi2007], Exercise 12.2): under `IsDSICOn D`, switching machine `i`'s report from `r` to `r'`
satisfies `rowLoad i r σ - rowLoad i r σ' ≤ rowLoad i r' σ - rowLoad i r' σ'`. -/
theorem IsDSICOn.rowLoad_sub_le {M : Mechanism Machine Job} {D : Machine → Set (Job → ℝ)}
    (hM : M.IsDSICOn D) {i : Machine} {b : Machine → Job → ℝ} {r r' : Job → ℝ}
    (hb : ∀ k, b k ∈ D k) (hr : r ∈ D i) (hr' : r' ∈ D i) :
    rowLoad i r (M.alloc (Function.update b i r)) -
        rowLoad i r (M.alloc (Function.update b i r')) ≤
      rowLoad i r' (M.alloc (Function.update b i r)) -
        rowLoad i r' (M.alloc (Function.update b i r')) := by
  have hb_r : ∀ k, Function.update b i r k ∈ D k := fun k => by
    rcases eq_or_ne k i with rfl | hne
    · simpa using hr
    · simpa [Function.update_of_ne hne] using hb k
  have hb_r' : ∀ k, Function.update b i r' k ∈ D k := fun k => by
    rcases eq_or_ne k i with rfl | hne
    · simpa using hr'
    · simpa [Function.update_of_ne hne] using hb k
  have h1 := hM i (Function.update b i r') r hb_r' hr
  have h2 := hM i (Function.update b i r) r' hb_r hr'
  simp only [Function.update_idem, utility] at h1 h2
  linarith

private theorem sum_sub_sdiff_le {M : Mechanism Machine Job}
    {D : Machine → Set (Job → ℝ)} (hM : M.IsDSICOn D) {i : Machine} {b : Machine → Job → ℝ}
    {r r' : Job → ℝ} (hb : ∀ k, b k ∈ D k) (hr : r ∈ D i) (hr' : r' ∈ D i) :
    (∑ j with M.alloc (Function.update b i r) j = i ∧ M.alloc (Function.update b i r') j ≠ i,
        (r j - r' j)) ≤
      ∑ j with M.alloc (Function.update b i r') j = i ∧ M.alloc (Function.update b i r) j ≠ i,
        (r j - r' j) := by
  classical
  set σ := M.alloc (Function.update b i r)
  set σ' := M.alloc (Function.update b i r')
  have hw := hM.rowLoad_sub_le hb hr hr'
  change (∑ j with σ j = i, r j) - (∑ j with σ' j = i, r j) ≤
    (∑ j with σ j = i, r' j) - (∑ j with σ' j = i, r' j) at hw
  have h := Finset.sum_sdiff_sub_sum_sdiff (f := fun j => r j - r' j)
    (s₁ := Finset.univ.filter fun j => σ' j = i) (s₂ := Finset.univ.filter fun j => σ j = i)
  rw [← Finset.filter_and_not, ← Finset.filter_and_not] at h
  simp only [Finset.sum_sub_distrib] at h ⊢
  linarith

/-- **Nisan–Ronen Task-Set Invariance Lemma** ([NisanRonen2001], Section 2; [Lavi2007],
Exercise 12.2): if `M` is DSIC on `D` and machine `i` changes its report from `r` to `r'` by
strictly decreasing its processing times on jobs assigned to `i` (`r' j < r j`) and strictly
increasing them on jobs not assigned to `i` (`r j < r' j`), then machine `i` is assigned the exact
same set of jobs under `r'` as under `r`. -/
theorem IsDSICOn.alloc_eq_iff_of_lt_of_gt {M : Mechanism Machine Job}
    {D : Machine → Set (Job → ℝ)} (hM : M.IsDSICOn D) {i : Machine} {b : Machine → Job → ℝ}
    {r r' : Job → ℝ} (hb : ∀ k, b k ∈ D k) (hr : r ∈ D i) (hr' : r' ∈ D i)
    (hdec : ∀ j, M.alloc (Function.update b i r) j = i → r' j < r j)
    (hinc : ∀ j, M.alloc (Function.update b i r) j ≠ i → r j < r' j) (j : Job) :
    M.alloc (Function.update b i r') j = i ↔ M.alloc (Function.update b i r) j = i := by
  classical
  set σ := M.alloc (Function.update b i r)
  set σ' := M.alloc (Function.update b i r')
  have hineq := sum_sub_sdiff_le hM hb hr hr'
  change (∑ l with σ l = i ∧ σ' l ≠ i, (r l - r' l)) ≤
    ∑ l with σ' l = i ∧ σ l ≠ i, (r l - r' l) at hineq
  have hlhs_nonneg : 0 ≤ ∑ l with σ l = i ∧ σ' l ≠ i, (r l - r' l) :=
    Finset.sum_nonneg fun l hl => by linarith [hdec l (Finset.mem_filter.mp hl).2.1]
  have hrhs_nonpos : (∑ l with σ' l = i ∧ σ l ≠ i, (r l - r' l)) ≤ 0 :=
    Finset.sum_nonpos fun l hl => by linarith [hinc l (Finset.mem_filter.mp hl).2.2]
  constructor
  · intro hσ'
    by_contra hσ
    have : (∑ l with σ' l = i ∧ σ l ≠ i, (r l - r' l)) < 0 :=
      Finset.sum_neg' (fun l hl => by linarith [hinc l (Finset.mem_filter.mp hl).2.2])
        ⟨j, by simp [hσ', hσ], by linarith [hinc j hσ]⟩
    linarith
  · intro hσ
    by_contra hσ'
    have : 0 < ∑ l with σ l = i ∧ σ' l ≠ i, (r l - r' l) :=
      Finset.sum_pos' (fun l hl => by linarith [hdec l (Finset.mem_filter.mp hl).2.1])
        ⟨j, by simp [hσ, hσ'], by linarith [hdec j hσ]⟩
    linarith

end Incentives

end Mechanism

/-! ### Embedding into `Cslib.GameTheory.Mechanism` (`VCG.lean`) -/

section VCGBridge

variable {Machine Job : Type*} [Fintype Job] [DecidableEq Machine]

/-- Negated-load valuation `-rowLoad i r σ` viewing machine `i`'s scheduling cost as a valuation on
outcomes `Job → Machine`. -/
@[expose] def schedulingVal (i : Machine) (r : Job → ℝ) (σ : Job → Machine) : ℝ :=
  -rowLoad i r σ

/-- Valuation profile on `Job → Machine` induced by processing-time matrix `t`. -/
@[expose] def schedulingProfile (t : Machine → Job → ℝ) : Machine → (Job → Machine) → ℝ :=
  fun i => schedulingVal i (t i)

theorem schedulingProfile_update (t : Machine → Job → ℝ) (i : Machine) (r : Job → ℝ) :
    schedulingProfile (Function.update t i r) =
      Function.update (schedulingProfile t) i (schedulingVal i r) := by
  funext k σ
  rcases eq_or_ne k i with rfl | hne
  · simp [schedulingProfile]
  · simp [schedulingProfile, hne]

/-- Pull back a general quasilinear `GameTheory.Mechanism Machine (Job → Machine)` along
`schedulingProfile` (negating agent payments into procurement compensations). -/
@[expose] def ofGeneralMechanism (G : GameTheory.Mechanism Machine (Job → Machine)) :
    Mechanism Machine Job where
  alloc t := G.outcome (schedulingProfile t)
  pay t i := -G.payment (schedulingProfile t) i

@[simp]
theorem ofGeneralMechanism_utility (G : GameTheory.Mechanism Machine (Job → Machine))
    (i : Machine) (r : Job → ℝ) (b : Machine → Job → ℝ) :
    (ofGeneralMechanism G).utility i r b =
      G.utility i (schedulingVal i r) (schedulingProfile b) := by
  simp only [Mechanism.utility, ofGeneralMechanism, GameTheory.Mechanism.utility, schedulingVal]
  ring

/-- Any DSIC general mechanism on `Job → Machine` pulls back to a DSIC scheduling mechanism. -/
theorem ofGeneralMechanism_isDSIC {G : GameTheory.Mechanism Machine (Job → Machine)}
    (hG : G.IsDSIC) : (ofGeneralMechanism G).IsDSIC := by
  intro i b r
  rw [ofGeneralMechanism_utility, ofGeneralMechanism_utility, schedulingProfile_update]
  exact hG i (schedulingProfile b) (schedulingVal i r)

theorem welfare_schedulingProfile [Fintype Machine] (t : Machine → Job → ℝ) (σ : Job → Machine) :
    GameTheory.Mechanism.welfare (schedulingProfile t) σ = -totalWork t σ := by
  simp only [GameTheory.Mechanism.welfare, schedulingProfile, schedulingVal, Finset.sum_neg_distrib]
  exact congrArg Neg.neg (sum_load_eq_totalWork t σ)

end VCGBridge

/-! ### Theorem 1: Nisan–Ronen `MinWork` (VCG / Groves) `n`-approximation mechanism -/

section MinWork

variable {Machine Job : Type*}

/-- Internal wrapper reusing `SingleParameter.Vickrey.Wins` on negated processing times. -/
private def WinsJob [LinearOrder Machine] (t : Machine → Job → ℝ) (j : Job) (i : Machine) :
    Prop :=
  SingleParameter.Vickrey.Wins (fun k => -t k j) i

private theorem winsJob_iff [LinearOrder Machine] {t : Machine → Job → ℝ} {j : Job} {i : Machine} :
    WinsJob t j i ↔ ∀ k, k ≠ i → t i j ≤ t k j ∧ (k < i → t i j < t k j) := by
  simp only [WinsJob, SingleParameter.Vickrey.Wins, neg_le_neg_iff, neg_lt_neg_iff]

private theorem exists_winsJob [LinearOrder Machine] [Finite Machine] [Nonempty Machine]
    (t : Machine → Job → ℝ) (j : Job) : ∃ i, WinsJob t j i :=
  SingleParameter.Vickrey.exists_wins fun k => -t k j

private theorem WinsJob.unique [LinearOrder Machine] {t : Machine → Job → ℝ} {j : Job}
    {i₁ i₂ : Machine} (h₁ : WinsJob t j i₁) (h₂ : WinsJob t j i₂) : i₁ = i₂ :=
  SingleParameter.Vickrey.Wins.unique h₁ h₂

open Classical in
/-- The **`MinWork` allocation rule** ([NisanRonen2001], Section 4): assign each job `j`
independently to the unique machine minimizing `t i j` (with smallest-index tie-breaking). -/
noncomputable def minWorkAlloc [LinearOrder Machine] [Finite Machine] [Nonempty Machine]
    (t : Machine → Job → ℝ) (j : Job) : Machine :=
  (exists_winsJob t j).choose

private theorem winsJob_minWorkAlloc [LinearOrder Machine] [Finite Machine] [Nonempty Machine]
    (t : Machine → Job → ℝ) (j : Job) : WinsJob t j (minWorkAlloc t j) :=
  (exists_winsJob t j).choose_spec

/-- Characterization of `minWorkAlloc t j = i`: machine `i` minimizes `t k j` with smallest-index
tie-breaking (`t i j ≤ t k j`, strictly when `k < i`). -/
theorem minWorkAlloc_eq_iff [LinearOrder Machine] [Finite Machine] [Nonempty Machine]
    {t : Machine → Job → ℝ} {j : Job} {i : Machine} :
    minWorkAlloc t j = i ↔ ∀ k, k ≠ i → t i j ≤ t k j ∧ (k < i → t i j < t k j) :=
  ⟨fun h => winsJob_iff.mp (h ▸ winsJob_minWorkAlloc t j),
    fun h => (winsJob_minWorkAlloc t j).unique (winsJob_iff.mpr h)⟩

theorem minWorkAlloc_le [LinearOrder Machine] [Finite Machine] [Nonempty Machine]
    (t : Machine → Job → ℝ) (j : Job) (k : Machine) :
    t (minWorkAlloc t j) j ≤ t k j := by
  rcases eq_or_ne k (minWorkAlloc t j) with rfl | hne
  · exact le_rfl
  · exact ((winsJob_iff.mp (winsJob_minWorkAlloc t j)) k hne).1

theorem totalWork_minWorkAlloc_le [LinearOrder Machine] [Finite Machine] [Nonempty Machine]
    [Fintype Job] (t : Machine → Job → ℝ) (σ : Job → Machine) :
    totalWork t (minWorkAlloc t) ≤ totalWork t σ :=
  Finset.sum_le_sum fun j _ => minWorkAlloc_le t j (σ j)

/-- The **second-lowest processing time** `min_{k ≠ i} t k j` for job `j` excluding machine `i`
(`0` when `Machine` is a subsingleton). -/
@[expose] noncomputable def secondLowestTime [Fintype Machine] [DecidableEq Machine]
    (t : Machine → Job → ℝ) (i : Machine) (j : Job) : ℝ :=
  if h : (Finset.univ.erase i).Nonempty then
    (Finset.univ.erase i).inf' h fun k => t k j
  else
    0

@[simp]
theorem secondLowestTime_update [Fintype Machine] [DecidableEq Machine]
    (t : Machine → Job → ℝ) (i : Machine) (r : Job → ℝ) (j : Job) :
    secondLowestTime (Function.update t i r) i j = secondLowestTime t i j := by
  unfold secondLowestTime
  split_ifs with h
  · exact Finset.inf'_congr h rfl fun k hk =>
      by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · rfl

private theorem erase_univ_nonempty [Fintype Machine] [DecidableEq Machine] [Nontrivial Machine]
    (i : Machine) : (Finset.univ.erase i).Nonempty := by
  obtain ⟨k, hki⟩ := exists_ne i
  exact ⟨k, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩⟩

theorem secondLowestTime_le_of_ne [Fintype Machine] [DecidableEq Machine] [Nontrivial Machine]
    (t : Machine → Job → ℝ) {i k : Machine} (hk : k ≠ i) (j : Job) :
    secondLowestTime t i j ≤ t k j := by
  have hne := erase_univ_nonempty i
  simp only [secondLowestTime, hne, ↓reduceDIte]
  exact Finset.inf'_le (fun m => t m j) (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)

theorem le_secondLowestTime_iff [Fintype Machine] [DecidableEq Machine] [Nontrivial Machine]
    {t : Machine → Job → ℝ} {i : Machine} {j : Job} {c : ℝ} :
    c ≤ secondLowestTime t i j ↔ ∀ k ≠ i, c ≤ t k j := by
  have hne := erase_univ_nonempty i
  simp only [secondLowestTime, hne, ↓reduceDIte, Finset.le_inf'_iff, Finset.mem_erase,
    Finset.mem_univ, and_true]

theorem le_secondLowestTime_of_minWorkAlloc_eq [LinearOrder Machine] [Fintype Machine]
    [Nontrivial Machine] {t : Machine → Job → ℝ} {i : Machine} {j : Job}
    (hwin : minWorkAlloc t j = i) : t i j ≤ secondLowestTime t i j := by
  rw [le_secondLowestTime_iff]
  intro k _
  rw [← hwin]
  exact minWorkAlloc_le t j k

theorem secondLowestTime_eq_of_minWorkAlloc_ne [LinearOrder Machine] [Fintype Machine]
    [Nontrivial Machine] {t : Machine → Job → ℝ} {i : Machine} {j : Job}
    (hlose : minWorkAlloc t j ≠ i) :
    secondLowestTime t i j = t (minWorkAlloc t j) j :=
  le_antisymm (secondLowestTime_le_of_ne t hlose j)
    (le_secondLowestTime_iff.mpr fun k _ => minWorkAlloc_le t j k)

/-- The **Nisan–Ronen `MinWork` mechanism** ([NisanRonen2001], Section 4): allocate each job `j` to
`minWorkAlloc t j`, and pay each machine `i` the sum of `secondLowestTime t i j` over all jobs `j`
assigned to `i`. -/
@[expose] noncomputable def minWorkMechanism [LinearOrder Machine] [Fintype Machine]
    [Nonempty Machine] [Fintype Job] : Mechanism Machine Job where
  alloc := minWorkAlloc
  pay t i := ∑ j with minWorkAlloc t j = i, secondLowestTime t i j

/-- **Claim 4.2 of [NisanRonen2001]**: `minWorkMechanism` is dominant-strategy incentive compatible
on all real processing-time profiles. -/
theorem minWorkMechanism_isDSIC [LinearOrder Machine] [Fintype Machine] [Nonempty Machine]
    [Fintype Job] : (minWorkMechanism (Machine := Machine) (Job := Job)).IsDSIC := by
  rcases subsingleton_or_nontrivial Machine with hsub | hnontriv
  · intro i b r
    have hall : ∀ t : Machine → Job → ℝ, minWorkAlloc t = fun _ => i := fun t => by
      funext j
      exact Subsingleton.elim _ _
    simp only [Mechanism.utility, minWorkMechanism, hall, secondLowestTime_update, le_rfl]
  · intro i b r
    set b' := Function.update b i r
    have hrewrite : ∀ t : Machine → Job → ℝ,
        (minWorkMechanism (Machine := Machine) (Job := Job)).utility i r t =
          ∑ j : Job, if minWorkAlloc t j = i then secondLowestTime t i j - r j else 0 := by
      intro t
      simp only [Mechanism.utility, minWorkMechanism, rowLoad, Finset.sum_filter,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [hrewrite b, hrewrite b']
    refine Finset.sum_le_sum fun j _ => ?_
    rw [secondLowestTime_update]
    by_cases hwin' : minWorkAlloc b' j = i
    · have hle : r j ≤ secondLowestTime b i j := by
        simpa [b'] using le_secondLowestTime_of_minWorkAlloc_eq hwin'
      split_ifs <;> linarith
    · have hge : secondLowestTime b i j ≤ r j := by
        have h1 : secondLowestTime b' i j ≤ b' i j := by
          rw [secondLowestTime_eq_of_minWorkAlloc_ne hwin']
          exact minWorkAlloc_le b' j i
        simpa [b'] using h1
      split_ifs <;> linarith

/-- `minWorkMechanism` is individually rational (`0 ≤ utility i (t i) t`) whenever there are at
least two machines (`[Nontrivial Machine]`). -/
theorem minWorkMechanism_isIR [LinearOrder Machine] [Fintype Machine] [Nontrivial Machine]
    [Fintype Job] : (minWorkMechanism (Machine := Machine) (Job := Job)).IsIR := by
  intro i t
  rw [Mechanism.utility, minWorkMechanism, rowLoad]
  dsimp only
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun j hj => ?_
  have := le_secondLowestTime_of_minWorkAlloc_eq (Finset.mem_filter.mp hj).2
  linarith

/-- On nonnegative processing times with `[Nontrivial Machine]`, `minWorkMechanism` makes
nonnegative payments (`0 ≤ pay t i`). -/
theorem minWorkMechanism_pay_nonneg [LinearOrder Machine] [Fintype Machine] [Nontrivial Machine]
    [Fintype Job] {t : Machine → Job → ℝ} (ht : IsNonnegProfile t) (i : Machine) :
    0 ≤ minWorkMechanism.pay t i := by
  refine Finset.sum_nonneg fun j _ => ?_
  exact le_secondLowestTime_iff.mpr fun k _ => ht k j

/-! ### Groves / VCG characterization of `minWorkMechanism` -/

section MinWorkIsGroves

variable [LinearOrder Machine] [Fintype Machine] [Nontrivial Machine] [Fintype Job]

/-- Machine-excluding Clarke pivot on `Job → Machine`: the maximum welfare
`max_{σ : Job → Finset.univ.erase i} ∑_{k ≠ i} B k σ` attainable by scheduling all jobs without
machine `i`. -/
private noncomputable def excludingPivot (i : Machine)
    (B : Machine → (Job → Machine) → ℝ) : ℝ :=
  letI := Classical.decEq Job
  have : Nonempty (Job → ↥(Finset.univ.erase i)) :=
    have : Nonempty ↥(Finset.univ.erase i) := (erase_univ_nonempty i).coe_sort
    inferInstance
  Finset.univ.sup' Finset.univ_nonempty
    fun σ : Job → ↥(Finset.univ.erase i) =>
      ∑ k ∈ Finset.univ.erase i, B k (fun j => (σ j).1)

omit [Nontrivial Machine] in
private theorem sum_other_schedulingProfile (t : Machine → Job → ℝ) (i : Machine)
    (σ : Job → Machine) :
    (∑ k ∈ Finset.univ.erase i, schedulingProfile t k σ) =
      -∑ j with σ j ≠ i, t (σ j) j := by
  classical
  simp only [schedulingProfile, schedulingVal, rowLoad, Finset.sum_neg_distrib]
  congr 1
  have hcongr : ∀ k ∈ Finset.univ.erase i,
      (∑ j with σ j = k, t k j) = ∑ j with σ j = k, t (σ j) j :=
    fun k _ => Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_filter, true_and]
    exact ⟨fun ⟨k, hk, hσ⟩ => hσ ▸ hk, fun hne => ⟨σ j, hne, rfl⟩⟩
  · intro k₁ _ k₂ _ hne
    exact Finset.disjoint_filter.mpr fun j _ h1 h2 => hne (h1.symm.trans h2)

private theorem excludingPivot_schedulingProfile (t : Machine → Job → ℝ) (i : Machine) :
    excludingPivot i (schedulingProfile t) = -∑ j : Job, secondLowestTime t i j := by
  classical
  have herase := erase_univ_nonempty i
  have hall : ∀ σ : Job → ↥(Finset.univ.erase i),
      (Finset.univ.filter fun j => (σ j).1 ≠ i) = Finset.univ := fun σ =>
    Finset.filter_true_of_mem fun j _ => (Finset.mem_erase.mp (σ j).2).1
  unfold excludingPivot
  refine le_antisymm (Finset.sup'_le _ _ fun σ _ => ?_) ?_
  · rw [sum_other_schedulingProfile, neg_le_neg_iff, hall]
    exact Finset.sum_le_sum fun j _ =>
      secondLowestTime_le_of_ne t (Finset.mem_erase.mp (σ j).2).1 j
  · have hex : ∀ j : Job, ∃ k : ↥(Finset.univ.erase i), t k.1 j = secondLowestTime t i j := by
      intro j
      obtain ⟨k, hk, hmin⟩ := Finset.exists_mem_eq_inf' herase (fun k => t k j)
      exact ⟨⟨k, hk⟩, by simp [secondLowestTime, herase, hmin]⟩
    choose σ₀ hval using hex
    refine Finset.le_sup'_of_le _ (Finset.mem_univ σ₀) ?_
    rw [sum_other_schedulingProfile, hall]
    simp [hval]

/-- The pivot term excluding `m` ignores `m`'s own bid. -/
private theorem excludingPivot_update (m : Machine) (B : Machine → (Job → Machine) → ℝ)
    (v : (Job → Machine) → ℝ) : excludingPivot m (Function.update B m v) = excludingPivot m B := by
  unfold excludingPivot
  refine Finset.sup'_congr _ rfl fun σ _ => Finset.sum_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

omit [Nontrivial Machine] in
/-- Splitting `∑ j, secondLowestTime t i j` along a schedule `σ` that pays the second-lowest
time on every job it does not give to `i`. -/
private theorem sum_secondLowestTime_eq {t : Machine → Job → ℝ} {i : Machine}
    {σ : Job → Machine} (h : ∀ j, σ j ≠ i → secondLowestTime t i j = t (σ j) j) :
    ∑ j, secondLowestTime t i j =
      (∑ j with σ j = i, secondLowestTime t i j) + ∑ j with σ j ≠ i, t (σ j) j := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => σ j = i)]
  congr 1
  exact Finset.sum_congr rfl fun j hj => h j (Finset.mem_filter.mp hj).2

/-- **Groves / VCG payment formula on `schedulingProfile`**: for every welfare-maximizing outcome
rule `f` on `Job → Machine`, the Groves mechanism with the machine-excluding Clarke pivot charges
machine `i` `-∑_{f(B) j = i} secondLowestTime t i j` (i.e., pays compensation equal to the sum of
second-lowest processing times on the jobs won by `i`, matching [NisanRonen2001], Section 4). -/
theorem groves_payment_schedulingProfile
    {f : (Machine → (Job → Machine) → ℝ) → (Job → Machine)}
    (hf : GameTheory.Mechanism.IsWelfareMaximizing f) (t : Machine → Job → ℝ) (i : Machine) :
    ∃ h : Machine → (Machine → (Job → Machine) → ℝ) → ℝ,
      (∀ m B v, h m (Function.update B m v) = h m B) ∧
        -(GameTheory.Mechanism.groves f h).payment (schedulingProfile t) i =
          ∑ j with f (schedulingProfile t) j = i, secondLowestTime t i j := by
  classical
  refine ⟨excludingPivot, excludingPivot_update, ?_⟩
  simp only [GameTheory.Mechanism.groves, excludingPivot_schedulingProfile,
    sum_other_schedulingProfile]
  set σ := f (schedulingProfile t)
  have hmax : totalWork t σ ≤ totalWork t (minWorkAlloc t) := by
    have hw := hf (schedulingProfile t) (minWorkAlloc t)
    rw [welfare_schedulingProfile, welfare_schedulingProfile] at hw
    linarith
  have hptwise : ∀ j : Job, t (σ j) j = t (minWorkAlloc t j) j := by
    intro j
    by_contra hne
    have hlt : t (minWorkAlloc t j) j < t (σ j) j :=
      (minWorkAlloc_le t j (σ j)).lt_of_ne (Ne.symm hne)
    have hstrict : totalWork t (minWorkAlloc t) < totalWork t σ :=
      Finset.sum_lt_sum (fun l _ => minWorkAlloc_le t l (σ l)) ⟨j, Finset.mem_univ j, hlt⟩
    linarith
  have hother_eq : ∀ j, σ j ≠ i → secondLowestTime t i j = t (σ j) j := fun j hne =>
    le_antisymm (secondLowestTime_le_of_ne t hne j)
      (le_secondLowestTime_iff.mpr fun k _ => (hptwise j).trans_le (minWorkAlloc_le t j k))
  linarith [sum_secondLowestTime_eq hother_eq]

/-- **`minWorkMechanism` is a Groves VCG mechanism**: there exists a welfare-maximizing outcome rule
`f` and agent-independent pivot `h` on `Job → Machine` whose pullback `ofGeneralMechanism (groves f
h)` equals `minWorkMechanism`. -/
theorem exists_groves_eq_minWorkMechanism :
    ∃ (f : (Machine → (Job → Machine) → ℝ) → (Job → Machine))
      (h : Machine → (Machine → (Job → Machine) → ℝ) → ℝ),
      GameTheory.Mechanism.IsWelfareMaximizing f ∧
        (∀ m B v, h m (Function.update B m v) = h m B) ∧
        ofGeneralMechanism (GameTheory.Mechanism.groves f h) =
          minWorkMechanism (Machine := Machine) (Job := Job) := by
  classical
  obtain ⟨f₀, hf₀⟩ :=
    GameTheory.Mechanism.exists_isWelfareMaximizing (ι := Machine) (Ω := Job → Machine)
  let f : (Machine → (Job → Machine) → ℝ) → (Job → Machine) := fun B =>
    if h : ∃ t, schedulingProfile t = B then minWorkAlloc h.choose else f₀ B
  have hf_sched : ∀ t, f (schedulingProfile t) = minWorkAlloc t := by
    intro t
    have hex : ∃ t', schedulingProfile t' = schedulingProfile t := ⟨t, rfl⟩
    dsimp only [f]
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    set t' := hex.choose
    have ht' : schedulingProfile t' = schedulingProfile t := hex.choose_spec
    have hentry : ∀ k j, t' k j = t k j := by
      intro k j
      obtain ⟨k', hk'⟩ := exists_ne k
      let σ₁ : Job → Machine := fun l => if l = j then k else k'
      have h1 := congrFun (congrFun ht' k) σ₁
      simp only [schedulingProfile, schedulingVal, rowLoad, neg_inj] at h1
      have hsingle : ∀ m : Machine → Job → ℝ,
          (∑ l with σ₁ l = k, m k l) = m k j := by
        intro m
        have hflt : (Finset.univ.filter fun l => σ₁ l = k) = {j} := by
          ext l
          by_cases hlj : l = j <;> simp [σ₁, hlj, hk']
        rw [hflt, Finset.sum_singleton]
      rw [hsingle t', hsingle t] at h1
      exact h1
    have heq_t : t' = t := funext fun k => funext fun j => hentry k j
    exact congrArg minWorkAlloc heq_t
  have hf_max : GameTheory.Mechanism.IsWelfareMaximizing f := by
    intro B σ
    by_cases hex : ∃ t, schedulingProfile t = B
    · obtain ⟨t, rfl⟩ := hex
      rw [hf_sched t, welfare_schedulingProfile, welfare_schedulingProfile, neg_le_neg_iff]
      exact totalWork_minWorkAlloc_le t σ
    · dsimp only [f]
      rw [dite_eq_right_of_eq_false (eq_false hex)]
      exact hf₀ B σ
  refine ⟨f, excludingPivot, hf_max, excludingPivot_update, ?_⟩
  unfold ofGeneralMechanism minWorkMechanism
  simp only [Mechanism.mk.injEq, GameTheory.Mechanism.groves]
  refine ⟨funext hf_sched, funext fun t => funext fun i => ?_⟩
  rw [excludingPivot_schedulingProfile, hf_sched t, sum_other_schedulingProfile]
  linarith [sum_secondLowestTime_eq (i := i) (σ := minWorkAlloc t) fun j hne =>
    secondLowestTime_eq_of_minWorkAlloc_ne hne]

end MinWorkIsGroves

/-! ### `MinWork` `n`-approximation upper bound and tightness -/

/-- **Claim 4.3 of [NisanRonen2001]**: on every nonnegative processing-time matrix, `minWorkAlloc`
achieves makespan at most `|Machine| * optMakespan t`. -/
theorem makespan_minWorkAlloc_le_card_mul_optMakespan [LinearOrder Machine] [Fintype Machine]
    [Nonempty Machine] [Fintype Job] {t : Machine → Job → ℝ} (ht : IsNonnegProfile t) :
    makespan t (minWorkAlloc t) ≤ (Fintype.card Machine : ℝ) * optMakespan t := by
  obtain ⟨σ, hσ⟩ := exists_makespan_eq_optMakespan t
  calc
    makespan t (minWorkAlloc t) ≤ totalWork t (minWorkAlloc t) := makespan_le_totalWork ht _
    _ ≤ totalWork t σ := totalWork_minWorkAlloc_le t σ
    _ ≤ (Fintype.card Machine : ℝ) * makespan t σ := totalWork_le_card_mul_makespan t σ
    _ = (Fintype.card Machine : ℝ) * optMakespan t := by rw [hσ]

/-- **Approximation bound in Theorem 4.1 of [NisanRonen2001]**: `minWorkMechanism` is a DSIC
`|Machine|`-approximation mechanism on nonnegative processing-time profiles (polynomial-time
runtime / computability in Theorem 4.1 is not modeled here; `minWorkAlloc` and `minWorkMechanism`
are `noncomputable` over `ℝ`). -/
theorem minWorkMechanism_hasApproxRatioOn_nonneg [LinearOrder Machine] [Fintype Machine]
    [Nonempty Machine] [Fintype Job] :
    (minWorkMechanism (Machine := Machine) (Job := Job)).HasApproxRatioOn IsNonnegProfile
      (Fintype.card Machine : ℝ) :=
  fun _ ht => makespan_minWorkAlloc_le_card_mul_optMakespan ht

/-- **Tightness of `MinWork`'s `n`-approximation**: when `|Machine| ≤ |Job|` and `[Nonempty
Machine]`, any approximation ratio `c` achieved by `minWorkMechanism` on strictly positive profiles
satisfies `|Machine| ≤ c` (`t i j = 1` on the smallest machine and `1 + ε` elsewhere). -/
theorem card_le_of_minWorkMechanism_hasApproxRatioOn [LinearOrder Machine] [Fintype Machine]
    [Nonempty Machine] [Fintype Job] (hcard : Fintype.card Machine ≤ Fintype.card Job)
    {c : ℝ}
    (happrox : (minWorkMechanism (Machine := Machine) (Job := Job)).HasApproxRatioOn
      IsPositiveProfile c) :
    (Fintype.card Machine : ℝ) ≤ c := by
  classical
  by_contra hc_not
  have hc : c < (Fintype.card Machine : ℝ) := not_le.mp hc_not
  set n := Fintype.card Machine
  have hn_pos : 0 < n := Fintype.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  let c' : ℝ := max c 0
  have hc'_nonneg : 0 ≤ c' := le_max_right c 0
  have hc'_lt : c' < (n : ℝ) := max_lt hc hn_real_pos
  let ε : ℝ := ((n : ℝ) - c') / (2 * (c' + 1))
  have hε_pos : 0 < ε := div_pos (by linarith) (by positivity)
  let i₀ : Machine := Finset.univ.min' Finset.univ_nonempty
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset Job)) hcard
  let eSM : S ≃ Machine := Fintype.equivOfCardEq (by simp [hScard, n])
  let η : ℝ := ε / ((Fintype.card Job : ℝ) + 1)
  have hη_pos : 0 < η := div_pos hε_pos (by positivity)
  let t : Machine → Job → ℝ := fun i j =>
    if j ∈ S then
      if i = i₀ then 1 else 1 + ε
    else
      if i = i₀ then η else 1 + ε
  have ht_pos : IsPositiveProfile t := by
    intro i j
    dsimp only [t]
    split_ifs <;> linarith
  have hall_i₀ : ∀ j : Job, minWorkAlloc t j = i₀ := by
    intro j
    rw [minWorkAlloc_eq_iff]
    intro k hki
    have hle : t i₀ j < t k j := by
      have hη_lt : η < 1 + ε := by
        have h1 : η ≤ ε :=
          div_le_self hε_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Job)])
        linarith
      simp only [t, ↓reduceIte, hki]
      split_ifs <;> linarith
    exact ⟨hle.le, fun hlt => absurd (Finset.min'_le Finset.univ k (Finset.mem_univ k))
      (not_le.mpr hlt)⟩
  have hmake_ge : (n : ℝ) ≤ makespan t (minWorkAlloc t) := by
    refine le_trans ?_ (load_le_makespan t (minWorkAlloc t) i₀)
    unfold load rowLoad
    have hflt : (Finset.univ.filter fun j => minWorkAlloc t j = i₀) = Finset.univ := by
      ext j
      simp [hall_i₀ j]
    rw [hflt]
    calc
      (n : ℝ) = ∑ j ∈ S, (1 : ℝ) := by simp [hScard]
      _ = ∑ j ∈ S, t i₀ j := Finset.sum_congr rfl fun j hj => by simp [t, hj]
      _ ≤ ∑ j ∈ Finset.univ, t i₀ j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun j _ _ => (ht_pos i₀ j).le
  let σ_opt : Job → Machine := fun j => if hj : j ∈ S then eSM ⟨j, hj⟩ else i₀
  have hopt_le : optMakespan t ≤ 1 + ε := by
    refine (optMakespan_le_makespan t σ_opt).trans (makespan_le_iff.mpr fun i => ?_)
    let j_i : S := eSM.symm i
    have hsub : (Finset.univ.filter fun j => σ_opt j = i) ⊆
        insert j_i.1 (Finset.univ \ S) := by
      intro j hj
      have hσ : σ_opt j = i := (Finset.mem_filter.mp hj).2
      by_cases hjS : j ∈ S
      · simp only [σ_opt, hjS, ↓reduceDIte] at hσ
        have heq : (⟨j, hjS⟩ : S) = j_i := eSM.injective (by simp [j_i, hσ])
        exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val heq))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjS⟩))
    unfold load rowLoad
    by_cases hi₀ : i = i₀
    · have hnot_mem : j_i.1 ∉ Finset.univ \ S := fun h => (Finset.mem_sdiff.mp h).2 j_i.2
      calc
        (∑ j with σ_opt j = i, t i j)
          ≤ ∑ j ∈ insert j_i.1 (Finset.univ \ S), t i j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (ht_pos i j).le
        _ = t i j_i.1 + ∑ j ∈ Finset.univ \ S, t i j := Finset.sum_insert hnot_mem
        _ = 1 + ∑ j ∈ Finset.univ \ S, η := by
            congr 1
            · simp [t, j_i.2, hi₀]
            · exact Finset.sum_congr rfl fun j hj =>
                by simp [t, (Finset.mem_sdiff.mp hj).2, hi₀]
        _ ≤ 1 + (Fintype.card Job : ℝ) * η := by
            have hle_card : ((Finset.univ \ S).card : ℝ) ≤ (Fintype.card Job : ℝ) := by
              exact_mod_cast (Finset.univ \ S).card_le_univ
            simp only [Finset.sum_const, nsmul_eq_mul]
            gcongr
        _ ≤ 1 + ε := by
            have hmul : (Fintype.card Job : ℝ) * η ≤ ε := by
              have hcomm : (Fintype.card Job : ℝ) * η =
                  ε * ((Fintype.card Job : ℝ) / ((Fintype.card Job : ℝ) + 1)) := by
                dsimp only [η]
                ring
              rw [hcomm]
              exact mul_le_of_le_one_right hε_pos.le
                ((div_le_one (by positivity)).mpr (by linarith))
            linarith
    · have hsingle : (Finset.univ.filter fun j => σ_opt j = i) = {j_i.1} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hσ
          by_cases hjS : j ∈ S
          · simp only [σ_opt, hjS, ↓reduceDIte] at hσ
            have heq : (⟨j, hjS⟩ : S) = j_i := eSM.injective (by simp [j_i, hσ])
            exact congrArg Subtype.val heq
          · simp only [σ_opt, hjS, ↓reduceDIte] at hσ
            exact absurd hσ.symm hi₀
        · rintro rfl
          simp [σ_opt, j_i.2, j_i]
      rw [hsingle, Finset.sum_singleton]
      simp [t, j_i.2, hi₀]
  have hbound : makespan t (minWorkAlloc t) ≤ c * optMakespan t := happrox t ht_pos
  have hc_le : c * optMakespan t ≤ c' * (1 + ε) :=
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (optMakespan_nonneg ht_pos.isNonnegProfile)).trans
      (mul_le_mul_of_nonneg_left hopt_le hc'_nonneg)
  have hprod : c' * (1 + ε) < (n : ℝ) := by
    have hden : (0 : ℝ) < 2 * (c' + 1) := by positivity
    have hmul_ε : (c' + 1) * ε = ((n : ℝ) - c') / 2 := by
      dsimp only [ε]
      field_simp
    have : c' * (1 + ε) ≤ c' + (c' + 1) * ε := by nlinarith
    linarith
  linarith [hmake_ge, hbound, hc_le, hprod]

end MinWork

/-! ### Theorem 2: Nisan–Ronen `2`-approximation lower bound and boundary sharpness -/

section LowerBound

variable {Machine Job : Type*} [DecidableEq Machine] [Fintype Job]

private theorem rowLoad_le_sum_add_card_mul {i : Machine} {r : Job → ℝ}
    {σ : Job → Machine} (A : Finset Job) {δ : ℝ} (hδ : 0 ≤ δ) (hr : ∀ j, 0 ≤ r j)
    (hout : ∀ j, σ j = i → j ∉ A → r j ≤ δ) :
    rowLoad i r σ ≤ (∑ j ∈ A, r j) + (Fintype.card Job : ℝ) * δ := by
  classical
  unfold rowLoad
  rw [← Finset.sum_filter_add_sum_filter_not _ (· ∈ A)]
  refine add_le_add (Finset.sum_le_sum_of_subset_of_nonneg
    (fun j hj => (Finset.mem_filter.mp hj).2) fun j _ _ => hr j) ?_
  calc
    _ ≤ ∑ j ∈ (Finset.univ.filter fun j => σ j = i).filter (fun j => j ∉ A), δ :=
      Finset.sum_le_sum fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hout j hj.1 hj.2
    _ ≤ (Fintype.card Job : ℝ) * δ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      gcongr
      exact_mod_cast Finset.card_le_univ _

variable [Fintype Machine]

/-- **Theorem 4.4 of [NisanRonen2001]** ([Lavi2007], Exercise 12.2): if `2 ≤ Fintype.card Machine`
and `3 ≤ Fintype.card Job`, every deterministic scheduling mechanism `M` that is DSIC on strictly
positive processing times and achieves makespan approximation ratio `c` on strictly positive
profiles satisfies `2 ≤ c`. -/
theorem two_le_of_isDSICOn_positive_of_hasApproxRatioOn [Nonempty Machine]
    (hmach : 2 ≤ Fintype.card Machine) (hjob : 3 ≤ Fintype.card Job)
    (M : Mechanism Machine Job)
    (hdsic : M.IsDSICOn (fun _ => { r : Job → ℝ | ∀ j, 0 < r j }))
    {c : ℝ} (happrox : M.HasApproxRatioOn IsPositiveProfile c) :
    2 ≤ c := by
  classical
  by_contra hc_not
  have hc_lt : c < 2 := not_le.mp hc_not
  let c' : ℝ := max c 0
  have hc'_nonneg : 0 ≤ c' := le_max_right c 0
  have hc'_lt : c' < 2 := max_lt hc_lt zero_lt_two
  have happrox' : M.HasApproxRatioOn IsPositiveProfile c' := fun t ht =>
    (happrox t ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left c 0) (optMakespan_nonneg ht.isNonnegProfile))
  set k : ℝ := (Fintype.card Job : ℝ)
  have hk_ge : (3 : ℝ) ≤ k := by dsimp [k]; exact_mod_cast hjob
  have hk_pos : 0 < k := by linarith
  let δ : ℝ := (2 - c') / (2 * ((k + 1) * c' + 2) + 1)
  have hδ_pos : 0 < δ := div_pos (by linarith) (by positivity)
  let ε : ℝ := min (1 / (4 * k)) δ
  have hε_pos : 0 < ε := lt_min (by positivity) hδ_pos
  have hkε_nonneg : 0 ≤ k * ε := mul_nonneg hk_pos.le hε_pos.le
  have hk1ε_nonneg : 0 ≤ (k + 1) * ε := mul_nonneg (by positivity) hε_pos.le
  have hkε : k * ε ≤ 1 / 4 := by
    have hle : ε ≤ 1 / (4 * k) := min_le_left _ _
    have := mul_le_mul_of_nonneg_left hle hk_pos.le
    have hcancel : k * (1 / (4 * k)) = 1 / 4 := by field_simp
    linarith
  have hε_lt : ε < 1 / 4 := by nlinarith
  have hfinal_gap : c' * (1 + (k + 1) * ε) < 2 - 2 * ε := by
    have hle : ε ≤ δ := min_le_right _ _
    have hcoeff_nonneg : 0 ≤ (k + 1) * c' + 2 := by positivity
    have h1 : ((k + 1) * c' + 2) * ε ≤ ((k + 1) * c' + 2) * δ :=
      mul_le_mul_of_nonneg_left hle hcoeff_nonneg
    have hden_pos : 0 < 2 * ((k + 1) * c' + 2) + 1 := by positivity
    have h2 : ((k + 1) * c' + 2) * δ < 2 - c' := by
      have hrew : ((k + 1) * c' + 2) * δ =
          (((k + 1) * c' + 2) * (2 - c')) / (2 * ((k + 1) * c' + 2) + 1) := by
        dsimp only [δ]; ring
      rw [hrew, div_lt_iff₀ hden_pos]
      nlinarith
    nlinarith
  have hbig_gap : c' * (2 + k * ε) < 10 := by nlinarith
  let eM := (Fintype.equivFin Machine).symm
  let i₀ : Machine := eM ⟨0, by omega⟩
  let i₁ : Machine := eM ⟨1, by omega⟩
  have hi₀₁ : i₀ ≠ i₁ := fun h => by simpa [i₀, i₁] using eM.injective h
  let eJ := (Fintype.equivFin Job).symm
  let j₀ : Job := eJ ⟨0, by omega⟩
  let j₁ : Job := eJ ⟨1, by omega⟩
  let j₂ : Job := eJ ⟨2, by omega⟩
  have hj₀₁ : j₀ ≠ j₁ := fun h => by simpa [j₀, j₁] using eJ.injective h
  have hj₀₂ : j₀ ≠ j₂ := fun h => by simpa [j₀, j₂] using eJ.injective h
  have hj₁₂ : j₁ ≠ j₂ := fun h => by simpa [j₁, j₂] using eJ.injective h
  let J₃ : Finset Job := {j₀, j₁, j₂}
  have hJ₃_card : J₃.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hj₀₁, hj₀₂]),
      Finset.card_insert_of_notMem (by simp [hj₁₂]), Finset.card_singleton]
  let t : Machine → Job → ℝ := fun i j =>
    if i = i₀ ∨ i = i₁ then (if j ∈ J₃ then 1 else ε) else 10
  have ht_pos : IsPositiveProfile t := by
    intro i j
    dsimp only [t]
    split_ifs <;> linarith
  have hopt_t : optMakespan t ≤ 2 + k * ε := by
    let σ₀ : Job → Machine := fun j => if j = j₀ ∨ j = j₁ then i₀ else i₁
    refine (optMakespan_le_makespan t σ₀).trans (makespan_le_iff.mpr fun i => ?_)
    have ht_nn : ∀ j, 0 ≤ t i j := fun j => (ht_pos i j).le
    by_cases hi : i = i₀ ∨ i = i₁
    · rcases hi with rfl | rfl
      · -- Machine `i₀` processes exactly `j₀` and `j₁`.
        refine (rowLoad_le_sum_add_card_mul {j₀, j₁} hε_pos.le ht_nn fun j hσ hj => ?_).trans ?_
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          simp only [σ₀, hj, ↓reduceIte] at hσ
          exact absurd hσ.symm hi₀₁
        · have : t i₀ j₀ + t i₀ j₁ = 2 := by norm_num [t, J₃]
          rw [Finset.sum_pair hj₀₁]
          linarith
      · -- Machine `i₁` processes `j₂` and jobs outside `J₃`.
        refine (rowLoad_le_sum_add_card_mul {j₂} hε_pos.le ht_nn fun j hσ hj => ?_).trans ?_
        · have h01 : ¬(j = j₀ ∨ j = j₁) := fun h => hi₀₁ (by simpa [σ₀, h] using hσ)
          have hj₃ : j ∉ J₃ := by
            simp only [J₃, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
            tauto
          simp [t, hj₃]
        · have : t i₁ j₂ = 1 := by simp [t, J₃]
          rw [Finset.sum_singleton]
          linarith
    · have hne : ∀ j, σ₀ j ≠ i := fun j hσ => hi (by
        dsimp only [σ₀] at hσ
        split_ifs at hσ <;> simp [← hσ])
      exact (rowLoad_le_sum_add_card_mul ∅ hε_pos.le ht_nn fun j h _ => absurd h (hne j)).trans
        (by rw [Finset.sum_empty]; linarith)
  set x := M.alloc t
  have hx_two : ∀ j, x j = i₀ ∨ x j = i₁ := by
    intro j
    by_contra hnot
    have h10 : (10 : ℝ) ≤ makespan t x := by
      simpa [t, hnot] using entry_le_makespan ht_pos.isNonnegProfile x j
    have := happrox' t ht_pos
    have := mul_le_mul_of_nonneg_left hopt_t hc'_nonneg
    linarith
  have hpigeon : 2 ≤ (J₃.filter fun j => x j = i₀).card ∨
      2 ≤ (J₃.filter fun j => x j = i₁).card := by
    have hpart : (J₃.filter fun j => x j = i₀).card +
        (J₃.filter fun j => ¬ x j = i₀).card = J₃.card := by
      simpa using Finset.sum_filter_add_sum_filter_not J₃ (fun j => x j = i₀) (fun _ => (1 : ℕ))
    have hnot_eq : J₃.filter (fun j => ¬ x j = i₀) = J₃.filter (fun j => x j = i₁) := by
      ext j
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨hj, hn0⟩ => ⟨hj, (hx_two j).resolve_left hn0⟩,
        fun ⟨hj, h1⟩ => ⟨hj, h1 ▸ hi₀₁.symm⟩⟩
    rw [hnot_eq, hJ₃_card] at hpart
    omega
  obtain ⟨iStar, iOther, hi_ne, hi_pair, hcard2⟩ :
      ∃ iStar iOther : Machine, iStar ≠ iOther ∧
        (∀ m, (m = iStar ∨ m = iOther) ↔ (m = i₀ ∨ m = i₁)) ∧
        2 ≤ (J₃.filter fun j => x j = iStar).card := by
    rcases hpigeon with h0 | h1
    · exact ⟨i₀, i₁, hi₀₁, fun _ => Iff.rfl, h0⟩
    · exact ⟨i₁, i₀, hi₀₁.symm, fun _ => or_comm, h1⟩
  have hx_pair : ∀ j, x j = iStar ∨ x j = iOther := fun j => (hi_pair (x j)).mpr (hx_two j)
  obtain ⟨a, ha_mem, b, hb_mem, hab⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (J₃.filter fun j => x j = iStar).card)
  obtain ⟨haJ, hxa⟩ := Finset.mem_filter.mp ha_mem
  obtain ⟨hbJ, hxb⟩ := Finset.mem_filter.mp hb_mem
  have hiStar_mem : iStar = i₀ ∨ iStar = i₁ := (hi_pair iStar).mp (Or.inl rfl)
  have hiOther_mem : iOther = i₀ ∨ iOther = i₁ := (hi_pair iOther).mp (Or.inr rfl)
  let row₁ : Job → ℝ := fun j =>
    if x j = iStar then (if j = a ∨ j = b then 1 - ε else ε / 2) else 10
  let t₁ : Machine → Job → ℝ := Function.update t iStar row₁
  have hrow₁_pos : ∀ j, 0 < row₁ j := fun j => by dsimp only [row₁]; split_ifs <;> linarith
  have ht₁_pos : IsPositiveProfile t₁ := ht_pos.update hrow₁_pos
  have hdec₁ : ∀ j, M.alloc (Function.update t iStar (t iStar)) j = iStar →
      row₁ j < t iStar j := by
    simp only [Function.update_eq_self]
    intro j hxj
    have hxj' : x j = iStar := hxj
    simp only [row₁, hxj', ↓reduceIte, t, hiStar_mem]
    split_ifs with hab_j hjJ
    · linarith
    · exfalso
      rcases hab_j with rfl | rfl
      · exact hjJ haJ
      · exact hjJ hbJ
    · linarith
    · linarith
  have hinc₁ : ∀ j, M.alloc (Function.update t iStar (t iStar)) j ≠ iStar →
      t iStar j < row₁ j := by
    simp only [Function.update_eq_self]
    intro j hxj
    have hxj' : x j ≠ iStar := hxj
    simp only [row₁, hxj', ↓reduceIte, t, hiStar_mem]
    split_ifs <;> linarith
  have hx₁_iStar : ∀ j, M.alloc t₁ j = iStar ↔ x j = iStar := by
    intro j
    have h := hdsic.alloc_eq_iff_of_lt_of_gt (b := t) (r := t iStar) (r' := row₁)
      ht_pos (ht_pos iStar) hrow₁_pos hdec₁ hinc₁ j
    simpa only [t₁, Function.update_eq_self] using h
  have hopt_t₁ : optMakespan t₁ ≤ 2 + k * ε := by
    let σ₁ : Job → Machine := fun j => if j = a then iStar else iOther
    refine (optMakespan_le_makespan t₁ σ₁).trans (makespan_le_iff.mpr fun i => ?_)
    by_cases hiS : i = iStar
    · have hflt : (Finset.univ.filter fun j => σ₁ j = i) = {a} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, σ₁, hiS]
        split_ifs with hja
        · simp [hja]
        · simp [hja, hi_ne.symm]
      unfold load rowLoad
      rw [hflt, Finset.sum_singleton]
      simp only [hiS, t₁, Function.update_self, row₁, hxa, true_or, ↓reduceIte]
      linarith
    · by_cases hiO : i = iOther
      · have ht₁_other : t₁ i = t i := by rw [hiO]; exact Function.update_of_ne hi_ne.symm _ _
        unfold load
        rw [ht₁_other]
        refine (rowLoad_le_sum_add_card_mul (J₃.erase a) hε_pos.le (fun j => (ht_pos i j).le)
          fun j hσ hjA => ?_).trans ?_
        · have hja : j ≠ a := by
            rintro rfl
            simp [σ₁, hiO, hi_ne] at hσ
          have hjJ : j ∉ J₃ := fun h => hjA (Finset.mem_erase.mpr ⟨hja, h⟩)
          rw [hiO]
          simp [t, hiOther_mem, hjJ]
        · have hsum : ∑ j ∈ J₃.erase a, t i j = 2 := by
            rw [Finset.sum_congr rfl fun j hj => show t i j = 1 by
                rw [hiO]; simp [t, hiOther_mem, Finset.mem_of_mem_erase hj],
              Finset.sum_const, Finset.card_erase_of_mem haJ, hJ₃_card]
            norm_num
          linarith
      · have hempty : (Finset.univ.filter fun j => σ₁ j = i) = ∅ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            σ₁]
          split_ifs <;> intro h <;> [exact hiS h.symm; exact hiO h.symm]
        unfold load rowLoad
        rw [hempty, Finset.sum_empty]
        linarith
  set x₁ := M.alloc t₁
  have hx₁_pair : ∀ j, x₁ j = iStar ∨ x₁ j = iOther := by
    intro j
    by_contra hnot
    push Not at hnot
    have hnot01 : ¬ (x₁ j = i₀ ∨ x₁ j = i₁) := mt (hi_pair (x₁ j)).mpr (by tauto)
    have hneS : x₁ j ≠ iStar := hnot.1
    have h10 : (10 : ℝ) ≤ makespan t₁ x₁ := by
      simpa [t₁, Function.update_of_ne hneS, t, hnot01] using
        entry_le_makespan ht₁_pos.isNonnegProfile x₁ j
    have := happrox' t₁ ht₁_pos
    have := mul_le_mul_of_nonneg_left hopt_t₁ hc'_nonneg
    linarith
  have hx₁_eq_x : ∀ j, x₁ j = x j := by
    intro j
    by_cases h : x j = iStar
    · rw [h, (hx₁_iStar j).mpr h]
    · have hx_o : x j = iOther := (hx_pair j).resolve_left h
      have hx₁_not : x₁ j ≠ iStar := mt (hx₁_iStar j).mp h
      rw [hx_o, (hx₁_pair j).resolve_left hx₁_not]
  let row₂ : Job → ℝ := fun j =>
    if x₁ j = iOther then ε / 2 else (if j = a then 1 + ε else 10)
  let t₂ : Machine → Job → ℝ := Function.update t₁ iOther row₂
  have hrow₂_pos : ∀ j, 0 < row₂ j := fun j => by dsimp only [row₂]; split_ifs <;> linarith
  have ht₂_pos : IsPositiveProfile t₂ := ht₁_pos.update hrow₂_pos
  have ht₁_iOther : t₁ iOther = t iOther := Function.update_of_ne hi_ne.symm _ _
  have hdec₂ : ∀ j, M.alloc (Function.update t₁ iOther (t₁ iOther)) j = iOther →
      row₂ j < t₁ iOther j := by
    simp only [Function.update_eq_self]
    intro j hxj
    have hxj' : x₁ j = iOther := hxj
    change row₂ j < t₁ iOther j
    rw [ht₁_iOther]
    simp only [row₂, hxj', ↓reduceIte, t, hiOther_mem]
    split_ifs <;> linarith
  have hinc₂ : ∀ j, M.alloc (Function.update t₁ iOther (t₁ iOther)) j ≠ iOther →
      t₁ iOther j < row₂ j := by
    simp only [Function.update_eq_self]
    intro j hxj
    have hxj' : x₁ j ≠ iOther := hxj
    change t₁ iOther j < row₂ j
    rw [ht₁_iOther]
    simp only [row₂, hxj', ↓reduceIte, t, hiOther_mem]
    split_ifs <;> linarith
  have hx₂_iOther : ∀ j, M.alloc t₂ j = iOther ↔ x₁ j = iOther := by
    intro j
    have h := hdsic.alloc_eq_iff_of_lt_of_gt (b := t₁) (r := t₁ iOther) (r' := row₂)
      ht₁_pos (ht₁_pos iOther) hrow₂_pos hdec₂ hinc₂ j
    simpa only [t₂, Function.update_eq_self] using h
  have hopt_t₂ : optMakespan t₂ ≤ 1 + (k + 1) * ε := by
    let σ₂ : Job → Machine := fun j => if j = a then iOther else if j = b then iStar else x₁ j
    refine (optMakespan_le_makespan t₂ σ₂).trans (makespan_le_iff.mpr fun i => ?_)
    by_cases hiS : i = iStar
    · have ht₂_star : t₂ i = row₁ := by
        rw [hiS]
        simp [t₂, Function.update_of_ne hi_ne, t₁]
      unfold load
      rw [ht₂_star]
      refine (rowLoad_le_sum_add_card_mul {b} hε_pos.le (fun j => (hrow₁_pos j).le) ?_).trans ?_
      · intro j hσ hjB
        have hjb : j ≠ b := Finset.notMem_singleton.mp hjB
        have hja : j ≠ a := by
          rintro rfl
          simp [σ₂, hiS, hi_ne.symm] at hσ
        have hx₁_s : x₁ j = iStar := by simpa [σ₂, hja, hjb, hiS] using hσ
        have hx_s : x j = iStar := (hx₁_eq_x j).symm.trans hx₁_s
        simp only [row₁, hx_s, hja, hjb, or_self, ↓reduceIte]
        linarith
      · have : row₁ b = 1 - ε := by simp [row₁, hxb]
        rw [Finset.sum_singleton]
        linarith
    · by_cases hiO : i = iOther
      · have ht₂_other : t₂ i = row₂ := by simp [hiO, t₂]
        unfold load
        rw [ht₂_other]
        refine (rowLoad_le_sum_add_card_mul {a} hε_pos.le (fun j => (hrow₂_pos j).le) ?_).trans ?_
        · intro j hσ hjA
          have hja : j ≠ a := Finset.notMem_singleton.mp hjA
          have hjb : j ≠ b := by
            rintro rfl
            simp [σ₂, hja, hiO, hi_ne] at hσ
          have hx₁_o : x₁ j = iOther := by simpa [σ₂, hja, hjb, hiO] using hσ
          simp only [row₂, hx₁_o, ↓reduceIte]
          linarith
        · have hx₁a_ne : x₁ a ≠ iOther := by rw [hx₁_eq_x a, hxa]; exact hi_ne
          have : row₂ a = 1 + ε := by simp [row₂, hx₁a_ne]
          rw [Finset.sum_singleton]
          linarith
      · have hempty : (Finset.univ.filter fun j => σ₂ j = i) = ∅ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
            σ₂]
          split_ifs
          · exact fun h => hiO h.symm
          · exact fun h => hiS h.symm
          · intro h
            rcases hx₁_pair j with hs | ho
            · exact hiS (h.symm.trans hs)
            · exact hiO (h.symm.trans ho)
        unfold load rowLoad
        rw [hempty, Finset.sum_empty]
        linarith
  set x₂ := M.alloc t₂
  have hx₂a_ne_other : x₂ a ≠ iOther :=
    mt (hx₂_iOther a).mp (by rw [hx₁_eq_x a, hxa]; exact hi_ne)
  have hx₂b_ne_other : x₂ b ≠ iOther :=
    mt (hx₂_iOther b).mp (by rw [hx₁_eq_x b, hxb]; exact hi_ne)
  have hmake_t₂ : 2 - 2 * ε ≤ makespan t₂ x₂ := by
    have hnot_pair : ∀ z : Job, x₂ z ≠ iStar → x₂ z ≠ iOther → 2 - 2 * ε ≤ makespan t₂ x₂ := by
      intro z hzS hzO
      refine le_trans (show 2 - 2 * ε ≤ 10 by linarith) ?_
      have hnot01 : ¬ (x₂ z = i₀ ∨ x₂ z = i₁) := mt (hi_pair (x₂ z)).mpr (by tauto)
      simpa [t₂, Function.update_of_ne hzO, t₁, Function.update_of_ne hzS, t, hnot01] using
        entry_le_makespan ht₂_pos.isNonnegProfile x₂ z
    by_cases hxa2 : x₂ a = iStar
    · by_cases hxb2 : x₂ b = iStar
      · refine le_trans ?_ (load_le_makespan t₂ x₂ iStar)
        have ht₂_star : t₂ iStar = row₁ := by simp [t₂, Function.update_of_ne hi_ne, t₁]
        unfold load rowLoad
        rw [ht₂_star]
        have hsub : ({a, b} : Finset Job) ⊆ Finset.univ.filter (fun j => x₂ j = iStar) := by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hb'
          · simp [hxa2]
          · rw [Finset.mem_singleton.mp hb']; simp [hxb2]
        calc
          2 - 2 * ε = row₁ a + row₁ b := by simp [row₁, hxa, hxb]; ring
          _ = ∑ j ∈ ({a, b} : Finset Job), row₁ j := (Finset.sum_pair hab).symm
          _ ≤ ∑ j with x₂ j = iStar, row₁ j :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (hrow₁_pos j).le
      · exact hnot_pair b hxb2 hx₂b_ne_other
    · exact hnot_pair a hxa2 hx₂a_ne_other
  have hbound2 := happrox' t₂ ht₂_pos
  have := mul_le_mul_of_nonneg_left hopt_t₂ hc'_nonneg
  linarith

/-! ### Boundary sharpness: single-machine (`|Machine| = 1`) and single-job (`|Job| ≤ 1`) -/

/-- **Single-machine boundary (`|Machine| = 1`)**: when `[Subsingleton Machine]`, every schedule
equals the optimal makespan (`1`-approximation `< 2`), showing `2 ≤ Fintype.card Machine` is
necessary in `two_le_of_isDSICOn_positive_of_hasApproxRatioOn`. -/
theorem makespan_eq_optMakespan_of_subsingleton_machine [Nonempty Machine] [Subsingleton Machine]
    (t : Machine → Job → ℝ) (σ : Job → Machine) :
    makespan t σ = optMakespan t := by
  obtain ⟨σ', hσ'⟩ := exists_makespan_eq_optMakespan t
  have heq : σ = σ' := funext fun _ => Subsingleton.elim _ _
  rw [heq, hσ']

end LowerBound

/-- **Single-job boundary (`|Job| ≤ 1`)**: when `[Subsingleton Job]`, `minWorkAlloc` achieves exact
optimal makespan (`1`-approximation `< 2`) on every nonnegative profile, showing `|Job| > 1` is
necessary for any `> 1` inapproximability bound. -/
theorem makespan_minWorkAlloc_eq_optMakespan_of_subsingleton_job {Machine Job : Type*}
    [LinearOrder Machine] [Fintype Machine] [Nonempty Machine] [Fintype Job] [Subsingleton Job]
    {t : Machine → Job → ℝ} (ht : IsNonnegProfile t) :
    makespan t (minWorkAlloc t) = optMakespan t := by
  refine le_antisymm ?_ (optMakespan_le_makespan t (minWorkAlloc t))
  rw [le_optMakespan_iff]
  intro σ
  refine (makespan_le_totalWork ht (minWorkAlloc t)).trans ?_
  rcases isEmpty_or_nonempty Job with hempty | hneJ
  · have h0 : totalWork t (minWorkAlloc t) = 0 := by simp [totalWork]
    rw [h0]
    exact makespan_nonneg ht σ
  · obtain ⟨j₀⟩ := hneJ
    have huniv : (Finset.univ : Finset Job) = {j₀} := by
      ext j
      simp [Subsingleton.elim j j₀]
    have htot1 : totalWork t (minWorkAlloc t) = t (minWorkAlloc t j₀) j₀ := by
      simp [totalWork, huniv]
    rw [htot1]
    exact (minWorkAlloc_le t j₀ (σ j₀)).trans (entry_le_makespan ht σ j₀)

end Cslib.GameTheory.Scheduling

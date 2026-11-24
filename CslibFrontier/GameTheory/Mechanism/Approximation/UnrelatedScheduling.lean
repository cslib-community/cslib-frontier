/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Mechanism.VCG
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Truthful Scheduling on Unrelated Machines

This module formalizes deterministic truthful approximation mechanisms for makespan minimization on
unrelated machines ([NisanRonen2001]; [NisanRoughgardenTardosVazirani2007], Chapter 12, Exercise
12.2, locator not verified against primary PDF).

There is a finite set `M` of selfish machines and a finite set `J` of jobs. Each machine `i : M`
holds a private vector `tᵢ : J → ℝ` of processing times. Given a reported processing-time matrix
`t : M → J → ℝ`, an `UnrelatedMechanism M J` outputs an assignment `alloc t : J → M` and payments
`payment t : M → ℝ` paid *to* the machines. Machine `i` incurs load `∑_{j : a j = i} tᵢ j`, has
quasilinear utility `payment t i - load tᵢ (alloc t) i`, and the social objective is the makespan
`max_i load (t i) a i`.

## Main definitions

* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.UnrelatedMechanism`: direct-revelation
  scheduling mechanism (`alloc` and `payment`) on unrelated machines.
* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.load`, `makespan`, `optMakespan`: machine load,
  schedule makespan, and optimal makespan.
* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.UnrelatedMechanism.IsDSICOn`, `IsIROn`,
  `IsApproxOn`: truthfulness, individual rationality, and makespan approximation ratio on a domain
  of processing-time profiles (`nonnegProfiles`, `posProfiles`).
* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.minWorkMechanism`: the VCG / Min-Work mechanism
  that assigns each job independently to a minimum-cost machine (ties broken by smallest index)
  and pays each winning machine the second-lowest processing time for each job it receives.
* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.ofMechanism`: embeds a general
  `Cslib.GameTheory.Mechanism M (J → M)` into `UnrelatedMechanism M J` via negated load valuations.

## Main results

* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.minWorkMechanism_isDSIC`,
  `minWorkMechanism_isIR`, `minWorkPayment_nonneg`: the Min-Work VCG mechanism is DSIC,
  individually rational, and makes nonnegative payments on nonnegative profiles
  ([NisanRonen2001], Theorem 2, locator not verified against primary PDF).
* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.minWorkMechanism_isApprox`: `minWorkMechanism`
  is an `m`-approximation to optimal makespan on nonnegative profiles, and is tight on uniform unit
  instances (`minWorkMechanism_tight`).
* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.UnrelatedMechanism.IsDSICOn.weakMonotone`,
  `alloc_eq_of_strict_change`: weak monotonicity (W-MON) for unrelated-machine mechanisms.
* `Cslib.GameTheory.Mechanism.UnrelatedScheduling.nisanRonen_lower_bound`: **Nisan–Ronen lower
  bound**: for any `m ≥ 2` machines and `n ≥ 3` jobs, no deterministic mechanism that is DSIC on
  strictly positive processing-time profiles achieves a makespan approximation ratio strictly less
  than `2` ([NisanRonen2001], Theorem 3; [NisanRoughgardenTardosVazirani2007], Chapter 12,
  Exercise 12.2, locator not verified against primary PDF).

## References

* [N. Nisan and A. Ronen, *Algorithmic Mechanism Design*][NisanRonen2001]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*, Chapter 12][NisanRoughgardenTardosVazirani2007]
-/

public section

namespace Cslib.GameTheory.Mechanism.UnrelatedScheduling

open Finset

/-- A direct-revelation deterministic mechanism for scheduling jobs `J` on unrelated machines `M`.
On reported processing-time matrix `t : M → J → ℝ`, it outputs a job-to-machine assignment
`alloc t` and a payment `payment t i` paid *to* machine `i`. -/
structure UnrelatedMechanism (M J : Type*) where
  /-- The job assignment rule `alloc t j : M`. -/
  alloc : (M → J → ℝ) → J → M
  /-- The payment rule `payment t i : ℝ` paid to machine `i`. -/
  payment : (M → J → ℝ) → M → ℝ

section Model

variable {M J : Type*}

/-- The total load of machine `i` with processing-time vector `ti` under assignment `a`. -/
@[expose] def load [Fintype J] [DecidableEq M] (ti : J → ℝ) (a : J → M) (i : M) : ℝ :=
  ∑ j with a j = i, ti j

/-- The domain of nonnegative processing-time matrices `t i j ≥ 0`. -/
@[expose] def nonnegProfiles : Set (M → J → ℝ) :=
  {t | ∀ i j, 0 ≤ t i j}

/-- The domain of strictly positive processing-time matrices `t i j > 0`. -/
@[expose] def posProfiles : Set (M → J → ℝ) :=
  {t | ∀ i j, 0 < t i j}

theorem posProfiles_subset_nonnegProfiles :
    (posProfiles (M := M) (J := J)) ⊆ nonnegProfiles :=
  fun _ ht i j => le_of_lt (ht i j)

theorem load_nonneg [Fintype J] [DecidableEq M] {ti : J → ℝ} (hti : ∀ j, 0 ≤ ti j)
    (a : J → M) (i : M) : 0 ≤ load ti a i :=
  Finset.sum_nonneg fun j _ => hti j

theorem sum_load_eq_sum_assigned [Fintype M] [Fintype J] [DecidableEq M]
    (t : M → J → ℝ) (a : J → M) :
    ∑ i : M, load (t i) a i = ∑ j : J, t (a j) j := by
  simp only [load, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (a j)]
  · simp only [↓reduceIte]
  · intro i _ hne
    simp only [Ne.symm hne, ↓reduceIte]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The makespan `max_i load (t i) a i` of assignment `a` on processing-time matrix `t`. -/
@[expose] def makespan [Fintype M] [Nonempty M] [Fintype J] [DecidableEq M]
    (t : M → J → ℝ) (a : J → M) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => load (t i) a i

theorem load_le_makespan [Fintype M] [Nonempty M] [Fintype J] [DecidableEq M]
    (t : M → J → ℝ) (a : J → M) (i : M) :
    load (t i) a i ≤ makespan t a :=
  Finset.le_sup' (fun k => load (t k) a k) (Finset.mem_univ i)

theorem makespan_le_iff [Fintype M] [Nonempty M] [Fintype J] [DecidableEq M]
    (t : M → J → ℝ) (a : J → M) {B : ℝ} :
    makespan t a ≤ B ↔ ∀ i : M, load (t i) a i ≤ B := by
  simp only [makespan, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

theorem makespan_nonneg [Fintype M] [Nonempty M] [Fintype J] [DecidableEq M]
    {t : M → J → ℝ} (ht : t ∈ nonnegProfiles) (a : J → M) :
    0 ≤ makespan t a := by
  obtain ⟨i⟩ := ‹Nonempty M›
  exact (load_nonneg (ht i) a i).trans (load_le_makespan t a i)

theorem makespan_le_sum_load [Fintype M] [Nonempty M] [Fintype J] [DecidableEq M]
    {t : M → J → ℝ} (ht : t ∈ nonnegProfiles) (a : J → M) :
    makespan t a ≤ ∑ i : M, load (t i) a i := by
  rw [makespan_le_iff]
  intro i
  exact Finset.single_le_sum (fun k _ => load_nonneg (ht k) a k) (Finset.mem_univ i)

theorem sum_load_le_card_mul_makespan [Fintype M] [Nonempty M] [Fintype J] [DecidableEq M]
    (t : M → J → ℝ) (a : J → M) :
    ∑ i : M, load (t i) a i ≤ (Fintype.card M : ℝ) * makespan t a := by
  calc
    ∑ i : M, load (t i) a i ≤ ∑ _i : M, makespan t a :=
      Finset.sum_le_sum fun i _ => load_le_makespan t a i
    _ = (Fintype.card M : ℝ) * makespan t a := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The optimal makespan `min_{a : J → M} makespan t a` on processing-time matrix `t`. -/
@[expose] noncomputable def optMakespan [Fintype M] [Nonempty M] [Fintype J] [DecidableEq J]
    [DecidableEq M] (t : M → J → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun a : J → M => makespan t a

theorem optMakespan_le [Fintype M] [Nonempty M] [Fintype J] [DecidableEq J] [DecidableEq M]
    (t : M → J → ℝ) (a : J → M) :
    optMakespan t ≤ makespan t a :=
  Finset.inf'_le (fun a : J → M => makespan t a) (Finset.mem_univ a)

theorem exists_makespan_eq_optMakespan [Fintype M] [Nonempty M] [Fintype J] [DecidableEq J]
    [DecidableEq M] (t : M → J → ℝ) :
    ∃ a : J → M, makespan t a = optMakespan t := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty (α := J → M)) (fun a => makespan t a)
  exact ⟨a, ha.symm⟩

theorem optMakespan_nonneg [Fintype M] [Nonempty M] [Fintype J] [DecidableEq J] [DecidableEq M]
    {t : M → J → ℝ} (ht : t ∈ nonnegProfiles) :
    0 ≤ optMakespan t := by
  obtain ⟨a, ha⟩ := exists_makespan_eq_optMakespan t
  rw [← ha]
  exact makespan_nonneg ht a

/-- Quasilinear utility `payment t i - load ti (alloc t) i` of machine `i` with true processing
times `ti` under reported matrix `t`. -/
@[expose] def UnrelatedMechanism.utility [Fintype J] [DecidableEq M]
    (mech : UnrelatedMechanism M J) (i : M) (ti : J → ℝ) (t : M → J → ℝ) : ℝ :=
  mech.payment t i - load ti (mech.alloc t) i

/-- Dominant-strategy incentive compatibility on a domain `D` of processing-time profiles:
reporting its true vector `ti` never lowers machine `i`'s utility compared to any misreport. -/
@[expose] def UnrelatedMechanism.IsDSICOn [Fintype J] [DecidableEq M]
    (mech : UnrelatedMechanism M J) (D : Set (M → J → ℝ)) : Prop :=
  ∀ t ∈ D, ∀ (i : M) (ti : J → ℝ), Function.update t i ti ∈ D →
    mech.utility i ti t ≤ mech.utility i ti (Function.update t i ti)

theorem UnrelatedMechanism.IsDSICOn.mono [Fintype J] [DecidableEq M]
    {mech : UnrelatedMechanism M J} {D₁ D₂ : Set (M → J → ℝ)} (h : mech.IsDSICOn D₂)
    (hsub : D₁ ⊆ D₂) : mech.IsDSICOn D₁ :=
  fun t ht i ti hti => h t (hsub ht) i ti (hsub hti)

/-- Individual rationality on a domain `D`: a truthful machine always receives nonnegative
utility (`load (t i) (alloc t) i ≤ payment t i`). -/
@[expose] def UnrelatedMechanism.IsIROn [Fintype J] [DecidableEq M]
    (mech : UnrelatedMechanism M J) (D : Set (M → J → ℝ)) : Prop :=
  ∀ t ∈ D, ∀ i : M, 0 ≤ mech.utility i (t i) t

/-- Makespan `c`-approximation on a domain `D`: on every profile `t ∈ D`, the mechanism's makespan
is at most `c * optMakespan t`. -/
@[expose] def UnrelatedMechanism.IsApproxOn [Fintype M] [Nonempty M] [Fintype J]
    [DecidableEq J] [DecidableEq M] (mech : UnrelatedMechanism M J)
    (D : Set (M → J → ℝ)) (c : ℝ) : Prop :=
  ∀ t ∈ D, makespan t (mech.alloc t) ≤ c * optMakespan t

/-- The negated-load valuation of machine `i` with processing times `ti`, viewing schedules
`J → M` as outcomes of a general `Cslib.GameTheory.Mechanism M (J → M)`. -/
@[expose] def negLoadValuation [Fintype J] [DecidableEq M] (ti : J → ℝ) (i : M) :
    (J → M) → ℝ :=
  fun a => -load ti a i

/-- Embed a general `Cslib.GameTheory.Mechanism M (J → M)` into an `UnrelatedMechanism M J` by
passing each machine's negated-load valuation and negating the charged payment into a transfer
paid to the machine. -/
@[expose] def ofMechanism [Fintype J] [DecidableEq M]
    (G : Cslib.GameTheory.Mechanism M (J → M)) : UnrelatedMechanism M J where
  alloc t := G.outcome fun i => negLoadValuation (t i) i
  payment t i := -G.payment (fun k => negLoadValuation (t k) k) i

theorem ofMechanism_utility [Fintype J] [DecidableEq M]
    (G : Cslib.GameTheory.Mechanism M (J → M)) (i : M) (ti : J → ℝ) (t : M → J → ℝ) :
    (ofMechanism G).utility i ti t =
      G.utility i (negLoadValuation ti i) (fun k => negLoadValuation (t k) k) := by
  simp only [UnrelatedMechanism.utility, ofMechanism, Cslib.GameTheory.Mechanism.utility,
    negLoadValuation]
  ring

/-- A general DSIC mechanism induces a DSIC unrelated-machine scheduling mechanism on all
profiles. -/
theorem ofMechanism_isDSIC [Fintype J] [DecidableEq M]
    {G : Cslib.GameTheory.Mechanism M (J → M)} (hG : G.IsDSIC) :
    (ofMechanism G).IsDSICOn Set.univ := by
  intro t _ i ti _
  rw [ofMechanism_utility, ofMechanism_utility]
  have hupd : (fun k => negLoadValuation (Function.update t i ti k) k) =
      Function.update (fun k => negLoadValuation (t k) k) i (negLoadValuation ti i) :=
    funext fun k => by
      by_cases hk : k = i
      · subst hk
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hk]
  rw [hupd]
  exact hG i (fun k => negLoadValuation (t k) k) (negLoadValuation ti i)

end Model

/-! ### Min-Work VCG Mechanism (m-approximation) -/

section MinWork

variable {M J : Type*} [Fintype M] [LinearOrder M] [Nonempty M]

private noncomputable def minJobCost (t : M → J → ℝ) (j : J) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => t i j

private noncomputable def minMachines (t : M → J → ℝ) (j : J) : Finset M :=
  Finset.univ.filter fun i => t i j = minJobCost t j

omit [LinearOrder M] in
private theorem minMachines_nonempty (t : M → J → ℝ) (j : J) :
    (minMachines t j).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty (α := M)) (fun i => t i j)
  exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi.symm⟩⟩

/-- The Min-Work allocation rule: assigns each job `j` independently to the lowest-index machine
minimizing `t i j` ([NisanRonen2001], Theorem 2, locator not verified against primary PDF). -/
noncomputable def minWorkAlloc (t : M → J → ℝ) (j : J) : M :=
  (minMachines t j).min' (minMachines_nonempty t j)

theorem minWorkAlloc_le (t : M → J → ℝ) (j : J) (k : M) :
    t (minWorkAlloc t j) j ≤ t k j := by
  have hmem : minWorkAlloc t j ∈ minMachines t j := Finset.min'_mem _ _
  have heq : t (minWorkAlloc t j) j = minJobCost t j := (Finset.mem_filter.1 hmem).2
  rw [heq]
  exact Finset.inf'_le (fun i => t i j) (Finset.mem_univ k)

theorem minWorkAlloc_le_of_le (t : M → J → ℝ) (j : J) {k : M}
    (hk : t k j ≤ t (minWorkAlloc t j) j) :
    minWorkAlloc t j ≤ k := by
  have hmem : minWorkAlloc t j ∈ minMachines t j := Finset.min'_mem _ _
  have heq : t (minWorkAlloc t j) j = minJobCost t j := (Finset.mem_filter.1 hmem).2
  have hk_eq : t k j = minJobCost t j :=
    le_antisymm (hk.trans_eq heq) (Finset.inf'_le (fun i => t i j) (Finset.mem_univ k))
  exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ k, hk_eq⟩)

/-- The minimum processing time of job `j` among machines other than `i`. -/
@[expose] noncomputable def otherMinCost [Nontrivial M] (t : M → J → ℝ) (i : M) (j : J) : ℝ :=
  (Finset.univ.erase i).inf'
    (let ⟨k, hk⟩ := exists_ne i; ⟨k, Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩⟩)
    fun k => t k j

omit [Nonempty M] in
@[simp]
theorem otherMinCost_update [Nontrivial M] (t : M → J → ℝ) (i : M) (ti : J → ℝ) (j : J) :
    otherMinCost (Function.update t i ti) i j = otherMinCost t i j := by
  unfold otherMinCost
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro k hk
    have hne : k ≠ i := Finset.ne_of_mem_erase hk
    exact (Finset.inf'_le (fun m => Function.update t i ti m j) hk).trans_eq
      (by rw [Function.update_of_ne hne])
  · rw [Finset.le_inf'_iff]
    intro k hk
    have hne : k ≠ i := Finset.ne_of_mem_erase hk
    exact (Finset.inf'_le (fun m => t m j) hk).trans_eq
      (by rw [Function.update_of_ne hne])

theorem le_otherMinCost_of_alloc_eq [Nontrivial M] (t : M → J → ℝ) {i : M} {j : J}
    (h : minWorkAlloc t j = i) :
    t i j ≤ otherMinCost t i j := by
  unfold otherMinCost
  rw [Finset.le_inf'_iff]
  intro k _
  rw [← h]
  exact minWorkAlloc_le t j k

theorem otherMinCost_le_of_alloc_ne [Nontrivial M] (t : M → J → ℝ) {i : M} {j : J}
    (h : minWorkAlloc t j ≠ i) :
    otherMinCost t i j ≤ t i j := by
  calc
    otherMinCost t i j ≤ t (minWorkAlloc t j) j :=
      Finset.inf'_le (fun k => t k j) (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩)
    _ ≤ t i j := minWorkAlloc_le t j i

variable [Fintype J]

/-- The reverse-Vickrey / VCG payment to machine `i`: for each job assigned to `i`, pay the
lowest processing time among all other machines. -/
@[expose] noncomputable def minWorkPayment [Nontrivial M] (t : M → J → ℝ) (i : M) : ℝ :=
  ∑ j with minWorkAlloc t j = i, otherMinCost t i j

/-- The **Min-Work VCG mechanism** for scheduling unrelated machines ([NisanRonen2001], Theorem 2,
locator not verified against primary PDF): each job goes independently to its minimum-cost machine,
and that machine is paid the second-lowest processing time for the job. -/
@[expose] noncomputable def minWorkMechanism [Nontrivial M] : UnrelatedMechanism M J where
  alloc := minWorkAlloc
  payment := minWorkPayment

theorem minWorkPayment_nonneg [Nontrivial M] {t : M → J → ℝ} (ht : t ∈ nonnegProfiles) (i : M) :
    0 ≤ minWorkPayment t i := by
  refine Finset.sum_nonneg fun j _ => ?_
  unfold otherMinCost
  rw [Finset.le_inf'_iff]
  intro k _
  exact ht k j

/-- **Min-Work VCG is DSIC** ([NisanRonen2001], Theorem 2, locator not verified against primary
PDF): truthful reporting maximizes each machine's utility on every job independently. -/
theorem minWorkMechanism_isDSIC [Nontrivial M] :
    (minWorkMechanism (M := M) (J := J)).IsDSICOn Set.univ := by
  intro t _ i ti _
  set t' := Function.update t i ti
  have hutil : ∀ s : M → J → ℝ, (∀ k, k ≠ i → s k = t k) →
      (minWorkMechanism (M := M) (J := J)).utility i ti s =
        ∑ j : J, if minWorkAlloc s j = i then otherMinCost t i j - ti j else 0 := by
    intro s hs
    change ∑ j with minWorkAlloc s j = i, otherMinCost s i j -
        ∑ j with minWorkAlloc s j = i, ti j = _
    rw [← Finset.sum_sub_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · have hother : otherMinCost s i j = otherMinCost t i j := by
        unfold otherMinCost
        apply le_antisymm
        · rw [Finset.le_inf'_iff]
          intro k hk
          exact (Finset.inf'_le (fun m => s m j) hk).trans_eq
            (by rw [hs k (Finset.ne_of_mem_erase hk)])
        · rw [Finset.le_inf'_iff]
          intro k hk
          exact (Finset.inf'_le (fun m => t m j) hk).trans_eq
            (by rw [hs k (Finset.ne_of_mem_erase hk)])
      rw [hother]
    · rfl
  rw [hutil t (fun _ _ => rfl), hutil t' (fun k hk => Function.update_of_ne hk _ _)]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h' : minWorkAlloc t' j = i
  · have hle : ti j ≤ otherMinCost t i j := by
      have h1 := le_otherMinCost_of_alloc_eq t' h'
      simpa only [t', Function.update_self, otherMinCost_update] using h1
    split_ifs with h
    · exact le_rfl
    · linarith
  · have hge : otherMinCost t i j ≤ ti j := by
      have h1 := otherMinCost_le_of_alloc_ne t' h'
      simpa only [t', Function.update_self, otherMinCost_update] using h1
    split_ifs with h
    · linarith
    · exact le_rfl

/-- **Min-Work VCG is individually rational**: every truthful machine receives nonnegative utility
on all profiles (each assigned job pays at least its processing time). -/
theorem minWorkMechanism_isIR [Nontrivial M] :
    (minWorkMechanism (M := M) (J := J)).IsIROn Set.univ := by
  intro t _ i
  simp only [UnrelatedMechanism.utility, minWorkMechanism, minWorkPayment, load, sub_nonneg]
  refine Finset.sum_le_sum fun j hj => ?_
  exact le_otherMinCost_of_alloc_eq t (Finset.mem_filter.1 hj).2

/-- **Min-Work VCG achieves an `m`-approximation to optimal makespan** on nonnegative profiles
([NisanRonen2001], Theorem 2, locator not verified against primary PDF). -/
theorem minWorkMechanism_isApprox [Nontrivial M] [DecidableEq J] :
    (minWorkMechanism (M := M) (J := J)).IsApproxOn nonnegProfiles (Fintype.card M : ℝ) := by
  intro t ht
  obtain ⟨aOpt, haOpt⟩ := exists_makespan_eq_optMakespan t
  rw [← haOpt]
  calc
    makespan t (minWorkMechanism.alloc t)
        ≤ ∑ i : M, load (t i) (minWorkAlloc t) i := makespan_le_sum_load ht (minWorkAlloc t)
    _ = ∑ j : J, t (minWorkAlloc t j) j := sum_load_eq_sum_assigned t (minWorkAlloc t)
    _ ≤ ∑ j : J, t (aOpt j) j :=
      Finset.sum_le_sum fun j _ => minWorkAlloc_le t j (aOpt j)
    _ = ∑ i : M, load (t i) aOpt i := (sum_load_eq_sum_assigned t aOpt).symm
    _ ≤ (Fintype.card M : ℝ) * makespan t aOpt := sum_load_le_card_mul_makespan t aOpt

/-- **Tightness of the `m`-approximation of `minWorkMechanism`**: when `J = M` and every job has
unit processing time `1` on every machine, `optMakespan = 1` whereas tie-breaking sends all `m`
jobs to the smallest machine, yielding makespan `m`. -/
theorem minWorkMechanism_tight [Nontrivial M] :
    let t : M → M → ℝ := fun _ _ => 1
    optMakespan t = 1 ∧ makespan t (minWorkMechanism.alloc t) = (Fintype.card M : ℝ) := by
  intro t
  have hbot : ∃ i₀ : M, ∀ k : M, i₀ ≤ k :=
    ⟨Finset.univ.min' Finset.univ_nonempty, fun k => Finset.min'_le _ _ (Finset.mem_univ k)⟩
  obtain ⟨i₀, hi₀⟩ := hbot
  have halloc : ∀ j : M, minWorkAlloc t j = i₀ := fun j =>
    le_antisymm (minWorkAlloc_le_of_le t j le_rfl) (hi₀ _)
  have hload_id : ∀ i : M, load (t i) id i = 1 := fun i => by
    simp only [load, id_eq, t]
    have hfilt : (Finset.univ.filter fun j : M => j = i) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hfilt, Finset.sum_singleton]
  have hopt_le : optMakespan t ≤ 1 := by
    calc
      optMakespan t ≤ makespan t id := optMakespan_le t id
      _ ≤ 1 := (makespan_le_iff t id).2 fun i => le_of_eq (hload_id i)
  have hopt_ge : 1 ≤ optMakespan t := by
    obtain ⟨a, ha⟩ := exists_makespan_eq_optMakespan t
    rw [← ha]
    have hsum : (Fintype.card M : ℝ) = ∑ i : M, load (t i) a i := by
      rw [sum_load_eq_sum_assigned]
      simp only [t, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hle := sum_load_le_card_mul_makespan t a
    rw [← hsum] at hle
    have hpos : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos (α := M)
    nlinarith
  have hm_eq : makespan t (minWorkMechanism.alloc t) = (Fintype.card M : ℝ) := by
    apply le_antisymm
    · rw [makespan_le_iff]
      intro i
      simp only [minWorkMechanism, load, halloc, t]
      by_cases hi : i₀ = i
      · subst hi
        simp only [Finset.filter_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          le_refl]
      · simp only [hi, Finset.filter_false, Finset.sum_empty, Nat.cast_nonneg]
    · calc
        (Fintype.card M : ℝ) = load (t i₀) (minWorkAlloc t) i₀ := by
          simp only [load, halloc, t, Finset.filter_true, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one]
        _ ≤ makespan t (minWorkMechanism.alloc t) := load_le_makespan t (minWorkAlloc t) i₀
  exact ⟨le_antisymm hopt_le hopt_ge, hm_eq⟩

end MinWork

/-! ### Weak Monotonicity and the Nisan–Ronen Lower Bound of `2` -/

section LowerBound

variable {M J : Type*} [Fintype J] [DecidableEq M]

/-- **Weak monotonicity (W-MON)** for unrelated-machine scheduling mechanisms: adding the two DSIC
inequalities for machine `i` between `t` and `Function.update t i ti` eliminates payments and
yields `∑_{j : a' j = i} (ti j - t i j) ≤ ∑_{j : a j = i} (ti j - t i j)`. -/
theorem UnrelatedMechanism.IsDSICOn.weakMonotone {mech : UnrelatedMechanism M J}
    {D : Set (M → J → ℝ)} (hDSIC : mech.IsDSICOn D) {t : M → J → ℝ} (ht : t ∈ D)
    (i : M) {ti : J → ℝ} (hti : Function.update t i ti ∈ D) :
    ∑ j with mech.alloc (Function.update t i ti) j = i, (ti j - t i j) ≤
      ∑ j with mech.alloc t j = i, (ti j - t i j) := by
  have h1 := hDSIC t ht i ti hti
  have h2 := hDSIC (Function.update t i ti) hti i (t i) (by simpa only [Function.update_idem,
    Function.update_eq_self] using ht)
  simp only [Function.update_idem, Function.update_eq_self, UnrelatedMechanism.utility, load]
    at h1 h2
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith

/-- **Strict-change invariance (Nisan–Ronen monotonicity lemma)**: if machine `i` strictly decreases
its reported processing time on every job it receives under `t` and strictly increases its report
on every job it does not receive, then any DSIC mechanism must assign machine `i` the exact same
set of jobs under the updated profile. -/
theorem UnrelatedMechanism.IsDSICOn.alloc_eq_of_strict_change {mech : UnrelatedMechanism M J}
    {D : Set (M → J → ℝ)} (hDSIC : mech.IsDSICOn D) {t : M → J → ℝ} (ht : t ∈ D)
    (i : M) {ti : J → ℝ} (hti : Function.update t i ti ∈ D)
    (hdec : ∀ j, mech.alloc t j = i → ti j < t i j)
    (hinc : ∀ j, mech.alloc t j ≠ i → t i j < ti j) :
    ∀ j, mech.alloc (Function.update t i ti) j = i ↔ mech.alloc t j = i := by
  have hwmon := hDSIC.weakMonotone ht i hti
  set a := mech.alloc t
  set a' := mech.alloc (Function.update t i ti)
  have hdiff :
      ∑ j : J, (if a' j = i then ti j - t i j else 0) -
        ∑ j : J, (if a j = i then ti j - t i j else 0) ≤ 0 := by
    simp only [Finset.sum_filter] at hwmon
    linarith
  rw [← Finset.sum_sub_distrib] at hdiff
  have hterm_nonneg : ∀ j ∈ (Finset.univ : Finset J),
      0 ≤ (if a' j = i then ti j - t i j else 0) - (if a j = i then ti j - t i j else 0) := by
    intro j _
    by_cases h1 : a' j = i <;> by_cases h2 : a j = i
    · simp only [h1, h2, ↓reduceIte, sub_self, le_refl]
    · simp only [h1, h2, ↓reduceIte, sub_zero]
      linarith [hinc j h2]
    · simp only [h1, h2, ↓reduceIte, zero_sub, neg_nonneg]
      linarith [hdec j h2]
    · simp only [h1, h2, ↓reduceIte, sub_self, le_refl]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).1
    (le_antisymm hdiff (Finset.sum_nonneg hterm_nonneg))
  intro j
  have hj := hzero j (Finset.mem_univ j)
  by_cases h1 : a' j = i <;> by_cases h2 : a j = i
  · exact iff_of_true h1 h2
  · simp only [h1, h2, ↓reduceIte, sub_zero] at hj
    linarith [hinc j h2]
  · simp only [h1, h2, ↓reduceIte, zero_sub, neg_eq_zero] at hj
    linarith [hdec j h2]
  · exact iff_of_false h1 h2

omit [Fintype J] [DecidableEq M] in
private theorem exists_two_same_of_three [DecidableEq J] {i₀ i₁ : M} {j₁ j₂ j₃ : J}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃)
    {a : J → M} (ha : ∀ j, a j = i₀ ∨ a j = i₁) :
    ∃ u v : M, ∃ a₁ a₂ a₃ : J,
      ((u = i₀ ∧ v = i₁) ∨ (u = i₁ ∧ v = i₀)) ∧
      ({a₁, a₂, a₃} : Finset J) = {j₁, j₂, j₃} ∧
      a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ ∧ a a₁ = u ∧ a a₂ = u := by
  rcases ha j₁ with h1 | h1 <;> rcases ha j₂ with h2 | h2 <;> rcases ha j₃ with h3 | h3
  · exact ⟨i₀, i₁, j₁, j₂, j₃, Or.inl ⟨rfl, rfl⟩, rfl, h12, h13, h23, h1, h2⟩
  · exact ⟨i₀, i₁, j₁, j₂, j₃, Or.inl ⟨rfl, rfl⟩, rfl, h12, h13, h23, h1, h2⟩
  · refine ⟨i₀, i₁, j₁, j₃, j₂, Or.inl ⟨rfl, rfl⟩, ?_, h13, h12, h23.symm, h1, h3⟩
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · refine ⟨i₁, i₀, j₂, j₃, j₁, Or.inr ⟨rfl, rfl⟩, ?_, h23, h12.symm, h13.symm, h2, h3⟩
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · refine ⟨i₀, i₁, j₂, j₃, j₁, Or.inl ⟨rfl, rfl⟩, ?_, h23, h12.symm, h13.symm, h2, h3⟩
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · refine ⟨i₁, i₀, j₁, j₃, j₂, Or.inr ⟨rfl, rfl⟩, ?_, h13, h12, h23.symm, h1, h3⟩
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · exact ⟨i₁, i₀, j₁, j₂, j₃, Or.inr ⟨rfl, rfl⟩, rfl, h12, h13, h23, h1, h2⟩
  · exact ⟨i₁, i₀, j₁, j₂, j₃, Or.inr ⟨rfl, rfl⟩, rfl, h12, h13, h23, h1, h2⟩

/-- **Nisan–Ronen lower bound** ([NisanRonen2001], Theorem 3;
[NisanRoughgardenTardosVazirani2007], Chapter 12, Exercise 12.2, locator not verified against
primary PDF): for any `m ≥ 2` machines and `n ≥ 3` jobs, no deterministic mechanism that is DSIC
on strictly positive processing-time profiles can achieve a makespan approximation ratio strictly
less than `2`. -/
theorem nisanRonen_lower_bound [Fintype M] [DecidableEq J] (hM : 2 ≤ Fintype.card M)
    (hJ : 3 ≤ Fintype.card J) (mech : UnrelatedMechanism M J)
    (hDSIC : mech.IsDSICOn posProfiles) {c : ℝ}
    (hApprox : letI : Nonempty M := Fintype.card_pos_iff.1 (by omega)
      mech.IsApproxOn posProfiles c) :
    2 ≤ c := by
  let : Nonempty M := Fintype.card_pos_iff.1 (by omega)
  have : Nonempty J := Fintype.card_pos_iff.1 (by omega)
  by_contra hc_lt
  push Not at hc_lt
  -- First rule out `c ≤ 0` using the all-ones profile.
  have hc_nonneg : 0 ≤ c := by
    let t1 : M → J → ℝ := fun _ _ => 1
    have ht1 : t1 ∈ posProfiles := fun _ _ => zero_lt_one
    have h1 := hApprox t1 ht1
    have hmk : 0 < makespan t1 (mech.alloc t1) := by
      obtain ⟨j₀⟩ := ‹Nonempty J›
      have hpos : (0 : ℝ) < load (t1 (mech.alloc t1 j₀)) (mech.alloc t1) (mech.alloc t1 j₀) := by
        calc
          (0 : ℝ) < 1 := zero_lt_one
          _ = t1 (mech.alloc t1 j₀) j₀ := rfl
          _ ≤ load (t1 (mech.alloc t1 j₀)) (mech.alloc t1) (mech.alloc t1 j₀) :=
            Finset.single_le_sum (f := fun j' => t1 (mech.alloc t1 j₀) j')
              (fun j _ => zero_le_one) (Finset.mem_filter.2 ⟨Finset.mem_univ j₀, rfl⟩)
      exact hpos.trans_le (load_le_makespan t1 (mech.alloc t1) _)
    have hopt : 0 < optMakespan t1 := by
      obtain ⟨a, ha⟩ := exists_makespan_eq_optMakespan t1
      rw [← ha]
      obtain ⟨j₀⟩ := ‹Nonempty J›
      have hpos : (0 : ℝ) < load (t1 (a j₀)) a (a j₀) := by
        calc
          (0 : ℝ) < 1 := zero_lt_one
          _ = t1 (a j₀) j₀ := rfl
          _ ≤ load (t1 (a j₀)) a (a j₀) :=
            Finset.single_le_sum (f := fun j' => t1 (a j₀) j')
              (fun j _ => zero_le_one) (Finset.mem_filter.2 ⟨Finset.mem_univ j₀, rfl⟩)
      exact hpos.trans_le (load_le_makespan t1 a _)
    nlinarith
  obtain ⟨i₀, i₁, hi₀₁⟩ := Fintype.one_lt_card_iff.1 (show 1 < Fintype.card M by omega)
  obtain ⟨j₁, -, j₂, -, j₃, -, h12, h13, h23⟩ :=
    Finset.two_lt_card.1 (show 2 < (Finset.univ : Finset J).card by simpa only [Finset.card_univ])
  let big : Finset J := {j₁, j₂, j₃}
  set ε : ℝ := min (1 / 4 : ℝ) ((2 - c) / 10)
  have hε_pos : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε_le_quarter : ε ≤ 1 / 4 := min_le_left _ _
  have hε_le_gap : 10 * ε ≤ 2 - c := by
    have : ε ≤ (2 - c) / 10 := min_le_right _ _
    linarith
  let E : Finset J := Finset.univ \ big
  set η : ℝ := ε / ((E.card : ℝ) + 1)
  have hE1_pos : (0 : ℝ) < (E.card : ℝ) + 1 := by positivity
  have hη_pos : 0 < η := div_pos hε_pos hE1_pos
  have hη_le_ε : η ≤ ε := by
    have h1 : (1 : ℝ) ≤ (E.card : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) E.card]
    exact div_le_self hε_pos.le h1
  have hEη_le : (E.card : ℝ) * η ≤ ε := by
    have : (E.card : ℝ) * η = ε * ((E.card : ℝ) / ((E.card : ℝ) + 1)) := by
      simp only [η]; ring
    rw [this]
    have hdiv : (E.card : ℝ) / ((E.card : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hE1_pos]
      linarith
    nlinarith
  -- Construct the base profile `t₀`: unit times on `{i₀, i₁}` for the 3 big jobs, `η` for extra
  -- jobs, and `10` on every other machine.
  let t₀ : M → J → ℝ := fun i j =>
    if i = i₀ ∨ i = i₁ then if j ∈ big then 1 else η else 10
  have ht₀_pos : t₀ ∈ posProfiles := by
    intro i j
    simp only [t₀]
    split_ifs <;> linarith
  -- No machine outside `{i₀, i₁}` can receive any job when `optMakespan ≤ 2`.
  have h_only_two : ∀ (t : M → J → ℝ) (u v : M),
      (∀ k, k ≠ u → k ≠ v → ∀ j, t k j = 10) →
      t ∈ posProfiles → optMakespan t ≤ 2 →
      ∀ j, mech.alloc t j = u ∨ mech.alloc t j = v := by
    intro t u v hbig ht hopt j
    by_contra hnot
    push Not at hnot
    set m := mech.alloc t j
    have h10 : 10 ≤ makespan t (mech.alloc t) := by
      calc
        (10 : ℝ) = t m j := (hbig m hnot.1 hnot.2 j).symm
        _ ≤ load (t m) (mech.alloc t) m :=
          Finset.single_le_sum (f := fun j' => t m j') (fun j' _ => (ht m j').le)
            (Finset.mem_filter.2 ⟨Finset.mem_univ j, rfl⟩)
        _ ≤ makespan t (mech.alloc t) := load_le_makespan t (mech.alloc t) m
    have hbound := hApprox t ht
    nlinarith
  -- Upper bound `optMakespan t₀ ≤ 2`: assign `{j₁, j₂}` to `i₀` and everything else to `i₁`.
  have hopt_t₀ : optMakespan t₀ ≤ 2 := by
    let a0 : J → M := fun j => if j = j₁ ∨ j = j₂ then i₀ else i₁
    refine (optMakespan_le t₀ a0).trans ((makespan_le_iff t₀ a0).2 fun k => ?_)
    by_cases hk0 : k = i₀
    · rw [hk0]
      have hfilt : (Finset.univ.filter fun j => a0 j = i₀) = {j₁, j₂} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, a0, Finset.mem_insert,
          Finset.mem_singleton]
        split_ifs with h
        · exact iff_of_true rfl h
        · exact iff_of_false hi₀₁.symm h
      rw [load, hfilt, Finset.sum_pair h12]
      have hj1 : j₁ ∈ big := by simp only [big, Finset.mem_insert, true_or]
      have hj2 : j₂ ∈ big := by simp only [big, Finset.mem_insert, Finset.mem_singleton, true_or,
        or_true]
      simp only [t₀, true_or, ↓reduceIte, hj1, hj2]
      norm_num
    · by_cases hk1 : k = i₁
      · rw [hk1]
        have hfilt : (Finset.univ.filter fun j => a0 j = i₁) = insert j₃ E := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, a0, Finset.mem_insert, E,
            Finset.mem_sdiff, big, Finset.mem_singleton]
          split_ifs with h
          · refine iff_of_false hi₀₁ ?_
            rcases h with rfl | rfl
            · simp only [h13, true_or, not_true_eq_false, or_self, not_false_eq_true]
            · simp only [h23, true_or, or_true, not_true_eq_false, or_self, not_false_eq_true]
          · push Not at h
            exact iff_of_true rfl (by tauto)
        have hj3E : j₃ ∉ E := by
          simp only [E, Finset.mem_sdiff, big, Finset.mem_insert, Finset.mem_singleton, or_true,
            not_true_eq_false, and_false, not_false_eq_true]
        rw [load, hfilt, Finset.sum_insert hj3E]
        have hj3b : j₃ ∈ big := by simp only [big, Finset.mem_insert, Finset.mem_singleton,
          or_true]
        have hEsum : ∑ j ∈ E, t₀ i₁ j = (E.card : ℝ) * η := by
          have hcongr : ∑ j ∈ E, t₀ i₁ j = ∑ _j ∈ E, η := by
            refine Finset.sum_congr rfl fun j hj => ?_
            have hnb : j ∉ big := (Finset.mem_sdiff.1 hj).2
            simp only [t₀, or_true, ↓reduceIte, hnb]
          rw [hcongr, Finset.sum_const, nsmul_eq_mul]
        rw [hEsum]
        simp only [t₀, or_true, ↓reduceIte, hj3b]
        linarith
      · have hfilt : (Finset.univ.filter fun j => a0 j = k) = ∅ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, a0, Finset.notMem_empty,
            iff_false]
          split_ifs
          · exact Ne.symm hk0
          · exact Ne.symm hk1
        rw [load, hfilt, Finset.sum_empty]
        norm_num
  have ha_two : ∀ j, mech.alloc t₀ j = i₀ ∨ mech.alloc t₀ j = i₁ :=
    h_only_two t₀ i₀ i₁ (fun k hk0 hk1 j => by simp only [t₀, hk0, hk1, or_self, ↓reduceIte])
      ht₀_pos hopt_t₀
  obtain ⟨u, v, a₁, a₂, a₃, huv_eq, hbig_eq, ha12, ha13, ha23, ha1, ha2⟩ :=
    exists_two_same_of_three h12 h13 h23 ha_two
  have huv : u ≠ v := by
    rcases huv_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hi₀₁; exact hi₀₁.symm]
  have hmem_uv : ∀ k, (k = i₀ ∨ k = i₁) ↔ (k = u ∨ k = v) := fun k => by
    rcases huv_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have ht₀_u : ∀ j, t₀ u j = if j ∈ big then 1 else η := fun j => by
    have : u = i₀ ∨ u = i₁ := (hmem_uv u).2 (Or.inl rfl)
    simp only [t₀, this, ↓reduceIte]
  have ht₀_v : ∀ j, t₀ v j = if j ∈ big then 1 else η := fun j => by
    have : v = i₀ ∨ v = i₁ := (hmem_uv v).2 (Or.inr rfl)
    simp only [t₀, this, ↓reduceIte]
  have ha1_big : a₁ ∈ big := by
    dsimp only [big]; rw [← hbig_eq]; simp only [Finset.mem_insert, true_or]
  have ha2_big : a₂ ∈ big := by
    dsimp only [big]; rw [← hbig_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  have ha3_big : a₃ ∈ big := by
    dsimp only [big]; rw [← hbig_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  have hnot_big_eq : ∀ j, j ∉ big ↔ j ≠ a₁ ∧ j ≠ a₂ ∧ j ≠ a₃ := fun j => by
    dsimp only [big]; rw [← hbig_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  -- Split on whether `a₃` goes to `u` (Case 1) or to `v` (Case 2).
  have ha3_cases : mech.alloc t₀ a₃ = u ∨ mech.alloc t₀ a₃ = v := (hmem_uv _).1 (ha_two a₃)
  rcases ha3_cases with ha3 | ha3
  · -- Case 1: `u` receives all three big jobs `a₁, a₂, a₃`.
    let tu : J → ℝ := fun j =>
      if j = a₁ then 1 - ε
      else if j = a₂ then 1 - ε
      else if j = a₃ then ε
      else if mech.alloc t₀ j = u then η / 2
      else 2
    let t' := Function.update t₀ u tu
    have ht'_pos : t' ∈ posProfiles := by
      intro k j
      by_cases hku : k = u
      · rw [hku]
        simp only [t', Function.update_self, tu]
        split_ifs <;> linarith
      · simp only [t', Function.update_of_ne hku]
        exact ht₀_pos k j
    have hsame : ∀ j, mech.alloc t' j = u ↔ mech.alloc t₀ j = u := by
      refine hDSIC.alloc_eq_of_strict_change ht₀_pos u ht'_pos ?_ ?_
      · intro j hj
        rw [ht₀_u j]
        simp only [tu]
        by_cases h1 : j = a₁
        · rw [h1]; simp only [↓reduceIte, ha1_big]; linarith
        · by_cases h2 : j = a₂
          · rw [h2]; simp only [ha12.symm, ↓reduceIte, ha2_big]; linarith
          · by_cases h3 : j = a₃
            · rw [h3]; simp only [ha13.symm, ha23.symm, ↓reduceIte, ha3_big]; linarith
            · have hnb : j ∉ big := (hnot_big_eq j).2 ⟨h1, h2, h3⟩
              simp only [h1, h2, h3, hnb, hj, ↓reduceIte]
              linarith
      · intro j hj
        rw [ht₀_u j]
        simp only [tu]
        have h1 : j ≠ a₁ := fun h => hj (h ▸ ha1)
        have h2 : j ≠ a₂ := fun h => hj (h ▸ ha2)
        have h3 : j ≠ a₃ := fun h => hj (h ▸ ha3)
        have hnb : j ∉ big := (hnot_big_eq j).2 ⟨h1, h2, h3⟩
        simp only [h1, h2, h3, hnb, hj, ↓reduceIte]
        linarith
    have hmk_ge : 2 - ε ≤ makespan t' (mech.alloc t') := by
      have hsub : ({a₁, a₂, a₃} : Finset J) ⊆ Finset.univ.filter fun j => mech.alloc t' j = u := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        refine Finset.mem_filter.2 ⟨Finset.mem_univ j, (hsame j).2 ?_⟩
        rcases hj with rfl | rfl | rfl <;> assumption
      have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (ht'_pos u j).le
      have ha1_notMem : a₁ ∉ ({a₂, a₃} : Finset J) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ha12, ha13⟩
      have h3sum : ∑ j ∈ ({a₁, a₂, a₃} : Finset J), t' u j = 2 - ε := by
        rw [Finset.sum_insert ha1_notMem, Finset.sum_pair ha23]
        simp only [t', Function.update_self, tu, ↓reduceIte, ha12.symm, ha13.symm, ha23.symm]
        ring
      calc
        2 - ε = ∑ j ∈ ({a₁, a₂, a₃} : Finset J), t' u j := h3sum.symm
        _ ≤ load (t' u) (mech.alloc t') u := hsum_le
        _ ≤ makespan t' (mech.alloc t') := load_le_makespan t' (mech.alloc t') u
    have hopt_le : optMakespan t' ≤ 1 + ε := by
      let aStar : J → M := fun j => if j = a₁ ∨ j = a₃ then u else v
      refine (optMakespan_le t' aStar).trans ((makespan_le_iff t' aStar).2 fun k => ?_)
      by_cases hku : k = u
      · rw [hku]
        have hfilt : (Finset.univ.filter fun j => aStar j = u) = {a₁, a₃} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, aStar, Finset.mem_insert,
            Finset.mem_singleton]
          split_ifs with h
          · exact iff_of_true rfl h
          · exact iff_of_false huv.symm h
        rw [load, hfilt, Finset.sum_pair ha13]
        simp only [t', Function.update_self, tu, ↓reduceIte, ha13.symm, ha23.symm]
        linarith
      · by_cases hkv : k = v
        · rw [hkv]
          have hfilt : (Finset.univ.filter fun j => aStar j = v) = insert a₂ E := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, aStar, Finset.mem_insert, E,
              Finset.mem_sdiff, hnot_big_eq]
            split_ifs with h
            · refine iff_of_false huv ?_
              rintro (h' | ⟨h1, -, h3⟩)
              · rcases h with rfl | rfl
                · exact ha12 h'
                · exact ha23.symm h'
              · rcases h with rfl | rfl
                · exact h1 rfl
                · exact h3 rfl
            · push Not at h
              exact iff_of_true rfl (by tauto)
          have ha2E : a₂ ∉ E := by
            simp only [E, Finset.mem_sdiff, ha2_big, not_true_eq_false, and_false,
              not_false_eq_true]
          rw [load, hfilt, Finset.sum_insert ha2E]
          have hEsum : ∑ j ∈ E, t' v j = (E.card : ℝ) * η := by
            have hcongr : ∑ j ∈ E, t' v j = ∑ _j ∈ E, η := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hnb : j ∉ big := (Finset.mem_sdiff.1 hj).2
              simp only [t', Function.update_of_ne huv.symm, ht₀_v, hnb, ↓reduceIte]
            rw [hcongr, Finset.sum_const, nsmul_eq_mul]
          rw [hEsum]
          simp only [t', Function.update_of_ne huv.symm, ht₀_v, ha2_big, ↓reduceIte]
          linarith
        · have hfilt : (Finset.univ.filter fun j => aStar j = k) = ∅ := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, aStar, Finset.notMem_empty,
              iff_false]
            split_ifs
            · exact Ne.symm hku
            · exact Ne.symm hkv
          rw [load, hfilt, Finset.sum_empty]
          linarith
    have hbound := hApprox t' ht'_pos
    nlinarith
  · -- Case 2: `u` receives `{a₁, a₂}` and `v` receives `a₃`.
    let tv : J → ℝ := fun j =>
      if j = a₁ then 1 + ε
      else if j = a₂ then 1 + ε
      else if j = a₃ then ε
      else if mech.alloc t₀ j = v then η / 2
      else 2
    let t' := Function.update t₀ v tv
    have ht'_pos : t' ∈ posProfiles := by
      intro k j
      by_cases hkv : k = v
      · rw [hkv]
        simp only [t', Function.update_self, tv]
        split_ifs <;> linarith
      · simp only [t', Function.update_of_ne hkv]
        exact ht₀_pos k j
    have hsame : ∀ j, mech.alloc t' j = v ↔ mech.alloc t₀ j = v := by
      refine hDSIC.alloc_eq_of_strict_change ht₀_pos v ht'_pos ?_ ?_
      · intro j hj
        rw [ht₀_v j]
        simp only [tv]
        have h1 : j ≠ a₁ := fun h => huv (by rw [← ha1, ← h, hj])
        have h2 : j ≠ a₂ := fun h => huv (by rw [← ha2, ← h, hj])
        by_cases h3 : j = a₃
        · rw [h3]
          simp only [ha13.symm, ha23.symm, ↓reduceIte, ha3_big]
          linarith
        · have hnb : j ∉ big := (hnot_big_eq j).2 ⟨h1, h2, h3⟩
          simp only [h1, h2, h3, hnb, hj, ↓reduceIte]
          linarith
      · intro j hj
        rw [ht₀_v j]
        simp only [tv]
        have h3 : j ≠ a₃ := fun h => hj (h ▸ ha3)
        by_cases h1 : j = a₁
        · rw [h1]; simp only [↓reduceIte, ha1_big]; linarith
        · by_cases h2 : j = a₂
          · rw [h2]; simp only [ha12.symm, ↓reduceIte, ha2_big]; linarith
          · have hnb : j ∉ big := (hnot_big_eq j).2 ⟨h1, h2, h3⟩
            simp only [h1, h2, h3, hnb, hj, ↓reduceIte]
            linarith
    have hopt_le : optMakespan t' ≤ 1 + 2 * ε := by
      let aStar : J → M := fun j => if j = a₂ ∨ j = a₃ then v else u
      refine (optMakespan_le t' aStar).trans ((makespan_le_iff t' aStar).2 fun k => ?_)
      by_cases hkv : k = v
      · rw [hkv]
        have hfilt : (Finset.univ.filter fun j => aStar j = v) = {a₂, a₃} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, aStar, Finset.mem_insert,
            Finset.mem_singleton]
          split_ifs with h
          · exact iff_of_true rfl h
          · exact iff_of_false huv h
        rw [load, hfilt, Finset.sum_pair ha23]
        simp only [t', Function.update_self, tv, ↓reduceIte, ha12.symm, ha13.symm, ha23.symm]
        linarith
      · by_cases hku : k = u
        · rw [hku]
          have hfilt : (Finset.univ.filter fun j => aStar j = u) = insert a₁ E := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, aStar, Finset.mem_insert, E,
              Finset.mem_sdiff, hnot_big_eq]
            split_ifs with h
            · refine iff_of_false huv.symm ?_
              rintro (h' | ⟨-, h2, h3⟩)
              · rcases h with rfl | rfl
                · exact ha12.symm h'
                · exact ha13.symm h'
              · rcases h with rfl | rfl
                · exact h2 rfl
                · exact h3 rfl
            · push Not at h
              exact iff_of_true rfl (by tauto)
          have ha1E : a₁ ∉ E := by
            simp only [E, Finset.mem_sdiff, ha1_big, not_true_eq_false, and_false,
              not_false_eq_true]
          rw [load, hfilt, Finset.sum_insert ha1E]
          have hEsum : ∑ j ∈ E, t' u j = (E.card : ℝ) * η := by
            have hcongr : ∑ j ∈ E, t' u j = ∑ _j ∈ E, η := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hnb : j ∉ big := (Finset.mem_sdiff.1 hj).2
              simp only [t', Function.update_of_ne huv, ht₀_u, hnb, ↓reduceIte]
            rw [hcongr, Finset.sum_const, nsmul_eq_mul]
          rw [hEsum]
          simp only [t', Function.update_of_ne huv, ht₀_u, ha1_big, ↓reduceIte]
          linarith
        · have hfilt : (Finset.univ.filter fun j => aStar j = k) = ∅ := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, aStar, Finset.notMem_empty,
              iff_false]
            split_ifs
            · exact Ne.symm hkv
            · exact Ne.symm hku
          rw [load, hfilt, Finset.sum_empty]
          linarith
    have ha'_two : ∀ j, mech.alloc t' j = u ∨ mech.alloc t' j = v :=
      h_only_two t' u v
        (fun k hku hkv j => by
          have hk01 : ¬(k = i₀ ∨ k = i₁) := by rw [hmem_uv]; tauto
          simp only [t', Function.update_of_ne hkv, t₀, hk01, ↓reduceIte])
        ht'_pos (by linarith)
    have ha1'_u : mech.alloc t' a₁ = u := by
      have hne : mech.alloc t' a₁ ≠ v := fun h => huv (ha1.symm.trans ((hsame a₁).1 h))
      exact (ha'_two a₁).resolve_right hne
    have ha2'_u : mech.alloc t' a₂ = u := by
      have hne : mech.alloc t' a₂ ≠ v := fun h => huv (ha2.symm.trans ((hsame a₂).1 h))
      exact (ha'_two a₂).resolve_right hne
    have hmk_ge : 2 ≤ makespan t' (mech.alloc t') := by
      have hsub : ({a₁, a₂} : Finset J) ⊆ Finset.univ.filter fun j => mech.alloc t' j = u := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        refine Finset.mem_filter.2 ⟨Finset.mem_univ j, ?_⟩
        rcases hj with rfl | rfl <;> assumption
      have hsum_le := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (ht'_pos u j).le
      have h2sum : ∑ j ∈ ({a₁, a₂} : Finset J), t' u j = 2 := by
        rw [Finset.sum_pair ha12]
        simp only [t', Function.update_of_ne huv, ht₀_u, ha1_big, ha2_big, ↓reduceIte]
        norm_num
      calc
        (2 : ℝ) = ∑ j ∈ ({a₁, a₂} : Finset J), t' u j := h2sum.symm
        _ ≤ load (t' u) (mech.alloc t') u := hsum_le
        _ ≤ makespan t' (mech.alloc t') := load_le_makespan t' (mech.alloc t') u
    have hbound := hApprox t' ht'_pos
    nlinarith

end LowerBound

end Cslib.GameTheory.Mechanism.UnrelatedScheduling

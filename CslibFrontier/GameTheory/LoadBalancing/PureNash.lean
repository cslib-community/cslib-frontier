/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Scheduling.LPT
public import CslibFrontier.GameTheory.LoadBalancing.Basic
public import CslibFrontier.GameTheory.Strategic.Potential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Existence, convergence, and price of stability of pure Nash equilibria

This module establishes the fundamental existence and convergence properties of pure Nash
equilibria in selfish load-balancing games ([Vocking2007]):

1. **Finite improvement property, existence, and `PoS = 1`** ([Vocking2007]):
   Every uniformly related load-balancing game (allowing zero-weight jobs), as well as every
   unrelated load-balancing game with strictly positive processing times, satisfies the finite
   improvement property (`CostGame.HasFIP`). The proof uses the strict lexicographic decrease of
   the descending sorted load vector (expressed directly via level-set cardinalities, with
   `CostGame.socialCost` breaking ties on zero-weight moves). Because no improving move can
   increase the makespan (`makespan_le_of_improves`), better-response dynamics started from a
   makespan-optimal assignment terminate at an optimal pure Nash equilibrium, giving
   **price of stability `1`** (`exists_isPureNash_makespan_eq_optMakespan`).
2. **Fast convergence on identical machines** ([EvenDarKesselmanMansour2003]; [Vocking2007]):
   Under max-weight best-response dynamics on identical machines, each job moves
   at most once, so every max-weight best-response sequence has length at most `|ι|` and reaches
   a pure Nash equilibrium in at most `|ι|` steps.
3. **LPT yields a pure Nash equilibrium on uniformly related machines**
   ([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Vocking2007]):
   Greedily inserting jobs in non-increasing weight order onto a machine minimizing post-insertion
   load always produces a pure Nash equilibrium. For identical machines this applies directly to
   `Cslib.Algorithms.Lean.Scheduling.lptSchedule`.

## Main definitions

* `Cslib.GameTheory.LoadBalancingGame.IsMaxWeightBestResponseStep`: one step of max-weight
  best-response dynamics.
* `Cslib.GameTheory.LoadBalancingGame.prefixLoad`,
  `Cslib.GameTheory.LoadBalancingGame.IsRelatedLPT`: greedy post-insertion load minimization in
  list order on uniformly related machines.

## Main results

* `Cslib.GameTheory.UnrelatedLoadBalancingGame.hasFIP_of_pos`,
  `Cslib.GameTheory.UnrelatedLoadBalancingGame.exists_isPureNash_makespan_eq_optMakespan_of_pos`:
  FIP and `PoS = 1` for unrelated machines with strictly positive processing times.
* `Cslib.GameTheory.LoadBalancingGame.hasFIP`,
  `Cslib.GameTheory.LoadBalancingGame.exists_isPureNash`,
  `Cslib.GameTheory.LoadBalancingGame.exists_isPureNash_makespan_eq_optMakespan`
  ([Vocking2007]): FIP, pure Nash existence, and `PoS = 1` on uniformly related
  machines.
* `Cslib.GameTheory.LoadBalancingGame.IsIdentical.maxWeightBestResponse_length_le`,
  `Cslib.GameTheory.LoadBalancingGame.IsIdentical.exists_maxWeightBestResponse_isPureNash`
  ([EvenDarKesselmanMansour2003]; [Vocking2007]): every max-weight best-response
  sequence on identical machines activates each job at most once (`≤ |ι|` steps).
* `Cslib.GameTheory.LoadBalancingGame.IsRelatedLPT.isPureNash`,
  `Cslib.GameTheory.LoadBalancingGame.exists_isPureNash_of_lptOrder`,
  `Cslib.GameTheory.LoadBalancingGame.IsIdentical.isRelatedLPT_iff_isListSchedule`,
  `Cslib.GameTheory.LoadBalancingGame.IsIdentical.isPureNash_lptSchedule`,
  `Cslib.GameTheory.LoadBalancingGame.IsIdentical.makespan_lptSchedule_le`
  ([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Graham1969]; [Vocking2007]): LPT
  produces a pure Nash equilibrium on uniformly related machines, and on identical machines
  `Cslib.Algorithms.Lean.Scheduling.lptSchedule` is itself a pure Nash equilibrium achieving
  Graham's `4 / 3 - 1 / (3m)` makespan bound.

## References

* [EvenDarKesselmanMansour2003]
* [FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]
* [Graham1969]
* [Vocking2007]
-/

public section

namespace Cslib.GameTheory

open Finset

section LexDesc

/-- Strict lexicographic descent on descendingly sorted load vectors over a finite machine set `M`:
there is a load level `c` above which `L'` and `L` have the same multiplicity of every load value,
and at `c` itself `L'` has strictly fewer machines than `L`. -/
private def LexDesc {M : Type*} [Fintype M] (L' L : M → ℝ) : Prop :=
  open scoped Classical in
  ∃ c : ℝ,
    (∀ x, c < x → #(univ.filter fun j => L' j = x) = #(univ.filter fun j => L j = x)) ∧
    #(univ.filter fun j => L' j = c) < #(univ.filter fun j => L j = c)

private theorem lexDesc_irrefl {M : Type*} [Fintype M] (L : M → ℝ) : ¬ LexDesc L L := by
  rintro ⟨c, -, hlt⟩
  exact lt_irrefl _ hlt

private theorem lexDesc_trans {M : Type*} [Fintype M] {L₁ L₂ L₃ : M → ℝ}
    (h₁ : LexDesc L₁ L₂) (h₂ : LexDesc L₂ L₃) : LexDesc L₁ L₃ := by
  classical
  rcases h₁ with ⟨c₁, heq₁, hlt₁⟩
  rcases h₂ with ⟨c₂, heq₂, hlt₂⟩
  refine ⟨max c₁ c₂, fun x hx => ?_, ?_⟩
  · exact (heq₁ x (lt_of_le_of_lt (le_max_left _ _) hx)).trans
      (heq₂ x (lt_of_le_of_lt (le_max_right _ _) hx))
  · rcases lt_trichotomy c₁ c₂ with h | rfl | h
    · simpa only [max_eq_right h.le, heq₁ c₂ h] using hlt₂
    · simpa only [max_self] using hlt₁.trans hlt₂
    · simpa only [max_eq_left h.le, ← heq₂ c₁ h] using hlt₁

/-- If `L'` agrees with `L` outside `{a, b}`, while `L' a < L a`, `L' b < L a`, and `L b < L a`,
then `LexDesc L' L`. -/
private theorem lexDesc_of_two_below {M : Type*} [Fintype M] {L' L : M → ℝ} {a b : M}
    (hla : L' a < L a) (hlb' : L' b < L a) (hlb : L b < L a)
    (hother : ∀ j, j ≠ a → j ≠ b → L' j = L j) : LexDesc L' L := by
  classical
  refine ⟨L a, fun x hx => congrArg card ?_, ?_⟩
  · ext j
    simp only [mem_filter, mem_univ, true_and]
    rcases eq_or_ne j a with rfl | hja
    · exact ⟨fun h => absurd (h ▸ hx) hla.not_gt, fun h => absurd (h ▸ hx) (lt_irrefl _)⟩
    · rcases eq_or_ne j b with rfl | hjb
      · exact ⟨fun h => absurd (h ▸ hx) hlb'.not_gt, fun h => absurd (h ▸ hx) hlb.not_gt⟩
      · rw [hother j hja hjb]
  · have herase : univ.filter (fun j => L' j = L a) = (univ.filter fun j => L j = L a).erase a := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_erase]
      rcases eq_or_ne j a with rfl | hja
      · exact ⟨fun h => absurd h hla.ne, fun h => absurd rfl h.1⟩
      · rcases eq_or_ne j b with rfl | hjb
        · exact ⟨fun h => absurd h hlb'.ne, fun h => absurd h.2 hlb.ne⟩
        · simp [hja, hother j hja hjb]
    rw [herase]
    exact card_erase_lt_of_mem (by simp)

end LexDesc

namespace UnrelatedLoadBalancingGame

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
  (U : UnrelatedLoadBalancingGame ι M)

/-- A strict improvement step never increases the makespan. -/
theorem makespan_le_of_improves [Nonempty M] {A' A : ι → M} (h : U.toCostGame.Improves A' A) :
    U.makespan A' ≤ U.makespan A := by
  rcases h with ⟨i, b, rfl, hlt⟩
  have hne : b ≠ A i := fun h => by simp [h, toCostGame] at hlt
  have hlt' : U.load (Function.update A i b) b < U.load A (A i) := by
    simpa [toCostGame] using hlt
  rw [U.makespan_le_iff]
  intro j
  rcases eq_or_ne j b with rfl | hjb
  · exact hlt'.le.trans (U.load_le_makespan A (A i))
  · rcases eq_or_ne j (A i) with rfl | hja
    · rw [U.load_update_self_of_ne A i hne]
      exact (sub_le_self _ (U.procTime_nonneg i (A i))).trans (U.load_le_makespan A (A i))
    · exact (U.load_update_other A i hja hjb).le.trans (U.load_le_makespan A j)

/-- Makespan never increases along any sequence of improvement steps. -/
theorem makespan_le_of_reflTransGen [Nonempty M] {A B : ι → M}
    (h : Relation.ReflTransGen (flip U.toCostGame.Improves) A B) :
    U.makespan B ≤ U.makespan A := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact (U.makespan_le_of_improves hstep).trans ih

/-- Every unrelated load-balancing game with strictly positive processing times has the finite
improvement property: every improving move strictly lowers the descending sorted load vector. -/
theorem hasFIP_of_pos {ι M : Type*} [Fintype ι] [DecidableEq ι] [Finite M] [DecidableEq M]
    (U : UnrelatedLoadBalancingGame ι M) (hpos : ∀ i j, 0 < U.procTime i j) :
    U.toCostGame.HasFIP := by
  have : Fintype M := Fintype.ofFinite M
  rw [CostGame.hasFIP_iff_wellFounded]
  let R : (ι → M) → (ι → M) → Prop := fun A' A => LexDesc (U.load A') (U.load A)
  have : Std.Irrefl R := ⟨fun A => lexDesc_irrefl (U.load A)⟩
  have : IsTrans (ι → M) R := ⟨fun _ _ _ => lexDesc_trans⟩
  have hwf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  refine Subrelation.wf (r := R) ?_ hwf
  rintro A' A ⟨i, b, rfl, hlt⟩
  have hne : b ≠ A i := fun h => by simp [h, toCostGame] at hlt
  have hlt' : U.load (Function.update A i b) b < U.load A (A i) := by
    simpa [toCostGame] using hlt
  have hla : U.load (Function.update A i b) (A i) < U.load A (A i) := by
    rw [U.load_update_self_of_ne A i hne]
    linarith [hpos i (A i)]
  have hlb : U.load A b < U.load A (A i) := by
    rw [U.load_update_of_ne A i hne] at hlt'
    linarith [hpos i b]
  exact lexDesc_of_two_below hla hlt' hlb fun j h1 h2 => U.load_update_other A i h1 h2

/-- **Pure Nash existence and `PoS = 1` for positive unrelated machines**: better-response dynamics
from an optimal schedule reach a pure Nash equilibrium with optimal makespan. -/
theorem exists_isPureNash_makespan_eq_optMakespan_of_pos [Nonempty M]
    (hpos : ∀ i j, 0 < U.procTime i j) :
    ∃ A : ι → M, U.toCostGame.IsPureNash A ∧ U.makespan A = U.optMakespan := by
  obtain ⟨A₀, hA₀⟩ := U.exists_makespan_eq_optMakespan
  obtain ⟨A, hpath, hNE⟩ := (U.hasFIP_of_pos hpos).exists_reflTransGen_isPureNash A₀
  refine ⟨A, hNE, le_antisymm ?_ (U.optMakespan_le A)⟩
  exact (U.makespan_le_of_reflTransGen hpath).trans hA₀.le

end UnrelatedLoadBalancingGame

namespace LoadBalancingGame

section FIPAndPoS

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq M]

/-- A strict improvement step never increases the makespan. -/
theorem makespan_le_of_improves [Fintype M] [Nonempty M] (G : LoadBalancingGame ι M)
    {A' A : ι → M} (h : G.toCostGame.Improves A' A) :
    G.makespan A' ≤ G.makespan A :=
  G.toUnrelated.makespan_le_of_improves h

/-- Makespan never increases along any sequence of improvement steps. -/
theorem makespan_le_of_reflTransGen [Fintype M] [Nonempty M] (G : LoadBalancingGame ι M)
    {A B : ι → M} (h : Relation.ReflTransGen (flip G.toCostGame.Improves) A B) :
    G.makespan B ≤ G.makespan A :=
  G.toUnrelated.makespan_le_of_reflTransGen h

/-- **Finite improvement property** ([Vocking2007]): every uniformly related
load-balancing game has the finite improvement property (even when zero-weight jobs are present).
Positive-weight improving moves strictly decrease the descending sorted load vector; zero-weight
improving moves leave all machine loads unchanged and strictly decrease `CostGame.socialCost`. -/
theorem hasFIP [Finite M] (G : LoadBalancingGame ι M) : G.toCostGame.HasFIP := by
  have : Fintype M := Fintype.ofFinite M
  rw [CostGame.hasFIP_iff_wellFounded]
  let R : (ι → M) → (ι → M) → Prop := fun A' A =>
    LexDesc (G.load A') (G.load A) ∨
      (G.load A' = G.load A ∧ G.toCostGame.socialCost A' < G.toCostGame.socialCost A)
  have : Std.Irrefl R := ⟨fun A h => by
    rcases h with h | ⟨-, hlt⟩
    · exact lexDesc_irrefl _ h
    · exact lt_irrefl _ hlt⟩
  have : IsTrans (ι → M) R := ⟨fun A₁ A₂ A₃ h₁₂ h₂₃ => by
    rcases h₁₂ with h₁ | ⟨heq₁, hlt₁⟩
    · rcases h₂₃ with h₂ | ⟨heq₂, -⟩
      · exact Or.inl (lexDesc_trans h₁ h₂)
      · exact Or.inl (heq₂ ▸ h₁)
    · rcases h₂₃ with h₂ | ⟨heq₂, hlt₂⟩
      · exact Or.inl (heq₁.symm ▸ h₂)
      · exact Or.inr ⟨heq₁.trans heq₂, hlt₁.trans hlt₂⟩⟩
  have hwf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  refine Subrelation.wf (r := R) ?_ hwf
  rintro A' A ⟨i, b, rfl, hlt⟩
  have hne : b ≠ A i := fun h => by
    simp [h, toCostGame, UnrelatedLoadBalancingGame.toCostGame] at hlt
  have hlt' : G.load (Function.update A i b) b < G.load A (A i) := by
    change G.toUnrelated.load (Function.update A i b) b < G.toUnrelated.load A (A i)
    simpa [toCostGame, UnrelatedLoadBalancingGame.toCostGame] using hlt
  rcases (G.weight_nonneg i).eq_or_lt with hw0 | hwpos
  · right
    have hload : G.load (Function.update A i b) = G.load A := funext fun j => by
      rcases eq_or_ne j b with rfl | hjb
      · rw [G.load_update_of_ne A i hne, ← hw0, zero_div, add_zero]
      · rcases eq_or_ne j (A i) with rfl | hja
        · rw [G.load_update_self_of_ne A i hne, ← hw0, zero_div, sub_zero]
        · exact G.load_update_other A i hja hjb
    refine ⟨hload, sum_lt_sum (fun k _ => ?_) ⟨i, mem_univ i, hlt⟩⟩
    rcases eq_or_ne k i with rfl | hki
    · exact hlt.le
    · change G.load (Function.update A i b) (Function.update A i b k) ≤ G.load A (A k)
      rw [hload, Function.update_of_ne hki]
  · left
    have hla : G.load (Function.update A i b) (A i) < G.load A (A i) := by
      rw [G.load_update_self_of_ne A i hne]
      linarith [div_pos hwpos (G.speed_pos (A i))]
    have hlb : G.load A b < G.load A (A i) := by
      rw [G.load_update_of_ne A i hne] at hlt'
      linarith [div_pos hwpos (G.speed_pos b)]
    exact lexDesc_of_two_below hla hlt' hlb fun j h1 h2 => G.load_update_other A i h1 h2

/-- **Existence of pure Nash equilibria** ([Vocking2007]): every uniformly
related load-balancing game with at least one machine admits a pure Nash equilibrium. -/
theorem exists_isPureNash [Finite M] [Nonempty M] (G : LoadBalancingGame ι M) :
    ∃ A : ι → M, G.toCostGame.IsPureNash A :=
  G.hasFIP.exists_isPureNash

/-- **Price of stability equals `1`** ([Vocking2007]): every uniformly related
load-balancing game admits a pure Nash equilibrium whose makespan equals `optMakespan`. -/
theorem exists_isPureNash_makespan_eq_optMakespan [Fintype M] [Nonempty M]
    (G : LoadBalancingGame ι M) :
    ∃ A : ι → M, G.toCostGame.IsPureNash A ∧ G.makespan A = G.optMakespan := by
  obtain ⟨A₀, hA₀⟩ := G.exists_makespan_eq_optMakespan
  obtain ⟨A, hpath, hNE⟩ := G.hasFIP.exists_reflTransGen_isPureNash A₀
  refine ⟨A, hNE, le_antisymm ?_ (G.optMakespan_le A)⟩
  exact (G.makespan_le_of_reflTransGen hpath).trans hA₀.le

end FIPAndPoS

section MaxWeightBestResponse

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq M]

/-- Job `i` is **satisfied** at assignment `A` if no unilateral move strictly lowers its cost. -/
@[expose] def IsSatisfied (G : LoadBalancingGame ι M) (A : ι → M) (i : ι) : Prop :=
  ∀ k : M, G.load A (A i) ≤ G.load A k + G.weight i / G.speed k

theorem isPureNash_iff_forall_isSatisfied (G : LoadBalancingGame ι M) (A : ι → M) :
    G.toCostGame.IsPureNash A ↔ ∀ i, G.IsSatisfied A i :=
  ⟨fun h i k => G.isPureNash_load_le h i k, fun h => (G.isPureNash_iff A).mpr fun i k _ => h i k⟩

/-- One step of **max-weight best-response dynamics** ([EvenDarKesselmanMansour2003];
[Vocking2007]): `A'` arises from `A` by moving an unsatisfied job `i` of maximum
weight among all unsatisfied jobs to a machine `b` minimizing its post-move load. -/
@[expose] def IsMaxWeightBestResponseStep (G : LoadBalancingGame ι M) (A' A : ι → M) (i : ι) :
    Prop :=
  ∃ b : M,
    A' = Function.update A i b ∧
    ¬ G.IsSatisfied A i ∧
    (∀ j, ¬ G.IsSatisfied A j → G.weight j ≤ G.weight i) ∧
    ∀ k : M, G.load A b + G.weight i / G.speed b ≤ G.load A k + G.weight i / G.speed k

/-- Key stability invariant for max-weight best-response on identical machines: after an unsatisfied
job `i` moves to a minimum-load machine `b`, `i` is satisfied and every already-satisfied job `j`
with `weight i ≤ weight j` remains satisfied. -/
private theorem isSatisfied_after_bestResponse {G : LoadBalancingGame ι M} (hId : G.IsIdentical)
    {A' A : ι → M} {i : ι} (hstep : G.IsMaxWeightBestResponseStep A' A i) :
    G.IsSatisfied A' i ∧
      ∀ j, G.IsSatisfied A j → G.weight i ≤ G.weight j → G.IsSatisfied A' j := by
  rcases hstep with ⟨b, rfl, hunsat, -, hmin⟩
  have hmin_load (k : M) : G.load A b ≤ G.load A k := by
    simpa only [hId b, hId k, div_one, add_le_add_iff_right] using hmin k
  have hlt_a : G.load A b + G.weight i < G.load A (A i) := by
    simp only [IsSatisfied, not_forall, not_le] at hunsat
    obtain ⟨k, hk⟩ := hunsat
    rw [hId k, div_one] at hk
    linarith [hmin_load k]
  have hne : b ≠ A i := fun h => by linarith [h ▸ hlt_a, G.weight_nonneg i]
  have hload_ge (k : M) : G.load A b ≤ G.load (Function.update A i b) k := by
    rcases eq_or_ne k b with rfl | hkb
    · rw [G.load_update_of_ne A i hne, hId k, div_one]
      linarith [G.weight_nonneg i]
    · rcases eq_or_ne k (A i) with rfl | hka
      · rw [G.load_update_self_of_ne A i hne, hId (A i), div_one]
        linarith
      · exact (G.load_update_other A i hka hkb).symm ▸ hmin_load k
  refine ⟨fun k => ?_, fun j hj hwij k => ?_⟩
  · rw [Function.update_self, G.load_update_of_ne A i hne, hId b, hId k, div_one]
    linarith [hload_ge k]
  have hji : j ≠ i := fun h => hunsat (h ▸ hj)
  rw [Function.update_of_ne hji, hId k, div_one]
  by_cases hjb : A j = b
  · rw [hjb, G.load_update_of_ne A i hne, hId b, div_one]
    linarith [hload_ge k]
  · have hle_prev : G.load (Function.update A i b) (A j) ≤ G.load A (A j) := by
      by_cases hja : A j = A i
      · rw [hja, G.load_update_self_of_ne A i hne]
        linarith [div_nonneg (G.weight_nonneg i) (G.speed_pos (A i)).le]
      · rw [G.load_update_other A i hja hjb]
    have hjb_sat : G.load A (A j) ≤ G.load A b + G.weight j := by
      simpa only [hId b, div_one] using hj b
    linarith [hload_ge k]

/-- **Max-weight best-response convergence (job-uniqueness and step bound)**
([EvenDarKesselmanMansour2003]; [Vocking2007]): along any sequence of `T` max-weight
best-response steps on identical machines, each job is activated at most once (`Function.Injective
move`), and hence `T ≤ Fintype.card ι`. -/
theorem IsIdentical.maxWeightBestResponse_injective {G : LoadBalancingGame ι M}
    (hId : G.IsIdentical) {T : ℕ} (γ : Fin (T + 1) → (ι → M)) (move : Fin T → ι)
    (hγ : ∀ t : Fin T, G.IsMaxWeightBestResponseStep (γ t.succ) (γ t.castSucc) (move t)) :
    Function.Injective move := by
  have hinv : ∀ t : Fin (T + 1),
      (∀ s : Fin T, s.val < t.val → G.IsSatisfied (γ t) (move s)) ∧
      (∀ s : Fin T, s.val < t.val → ∀ j : ι, G.weight (move s) < G.weight j →
        G.IsSatisfied (γ t) j) := by
    intro t
    induction t using Fin.induction with
    | zero =>
      exact ⟨fun s hs => absurd hs (Nat.not_lt_zero _), fun s hs => absurd hs (Nat.not_lt_zero _)⟩
    | succ t ih =>
      have hstep := hγ t
      obtain ⟨hsat_cur, hpres⟩ := isSatisfied_after_bestResponse hId hstep
      rcases hstep with ⟨_, _, hunsat_t, hmax_t, _⟩
      have hle_prev (s : Fin T) (hs : s.val < t.val) : G.weight (move t) ≤ G.weight (move s) :=
        le_of_not_gt fun hlt => hunsat_t (ih.2 s hs (move t) hlt)
      refine ⟨fun s hs => ?_, fun s hs j hj => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
        · exact hpres (move s) (ih.1 s hlt) (hle_prev s hlt)
        · exact Fin.ext heq ▸ hsat_cur
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | heq
        · exact hpres j (ih.2 s hlt j hj) ((hle_prev s hlt).trans hj.le)
        · cases Fin.ext heq
          exact hpres j (of_not_not fun hu => (hmax_t j hu).not_gt hj) hj.le
  have hlt_contra {a b : Fin T} (hlt : a.val < b.val) (heq : move a = move b) : False := by
    rcases hγ b with ⟨_, _, hunsat, _, _⟩
    exact hunsat (heq ▸ (hinv b.castSucc).1 a hlt)
  intro s₁ s₂ heq
  rcases lt_trichotomy s₁.val s₂.val with hlt | heq' | hlt
  · exact (hlt_contra hlt heq).elim
  · exact Fin.ext heq'
  · exact (hlt_contra hlt heq.symm).elim

/-- Every sequence of max-weight best-response steps on identical machines has length at most the
number of jobs `|ι|` ([EvenDarKesselmanMansour2003]; [Vocking2007]). -/
theorem IsIdentical.maxWeightBestResponse_length_le {G : LoadBalancingGame ι M}
    (hId : G.IsIdentical) {T : ℕ} (γ : Fin (T + 1) → (ι → M)) (move : Fin T → ι)
    (hγ : ∀ t : Fin T, G.IsMaxWeightBestResponseStep (γ t.succ) (γ t.castSucc) (move t)) :
    T ≤ Fintype.card ι := by
  simpa only [Fintype.card_fin] using
    Fintype.card_le_of_injective move (hId.maxWeightBestResponse_injective γ move hγ)

private theorem exists_snoc_of_not_isPureNash [Finite M] [Nonempty M]
    {G : LoadBalancingGame ι M} {k : ℕ} (γ : Fin (k + 1) → (ι → M)) (move : Fin k → ι)
    (hγ : ∀ t : Fin k, G.IsMaxWeightBestResponseStep (γ t.succ) (γ t.castSucc) (move t))
    (hNE : ¬ G.toCostGame.IsPureNash (γ (Fin.last k))) :
    ∃ (γ₁ : Fin (k + 2) → (ι → M)) (move₁ : Fin (k + 1) → ι),
      γ₁ 0 = γ 0 ∧
      ∀ t : Fin (k + 1), G.IsMaxWeightBestResponseStep (γ₁ t.succ) (γ₁ t.castSucc) (move₁ t) := by
  classical
  have : Fintype M := Fintype.ofFinite M
  obtain ⟨i, hi⟩ : ∃ i, ¬ G.IsSatisfied (γ (Fin.last k)) i := by
    rwa [G.isPureNash_iff_forall_isSatisfied, not_forall] at hNE
  let U : Finset ι := univ.filter fun j => ¬ G.IsSatisfied (γ (Fin.last k)) j
  obtain ⟨i₀, hi₀U, hi₀max⟩ := exists_max_image U G.weight ⟨i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩
  obtain ⟨b, -, hbmin⟩ := exists_min_image univ
    (fun m : M => G.load (γ (Fin.last k)) m + G.weight i₀ / G.speed m) univ_nonempty
  refine ⟨Fin.snoc (α := fun _ => ι → M) γ (Function.update (γ (Fin.last k)) i₀ b),
    Fin.snoc (α := fun _ => ι) move i₀,
    Fin.snoc_castSucc (α := fun _ => ι → M) _ γ 0, fun t => ?_⟩
  induction t using Fin.lastCases with
  | last =>
    simp only [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
    exact ⟨b, rfl, (mem_filter.mp hi₀U).2,
      fun j hj => hi₀max j (mem_filter.mpr ⟨mem_univ j, hj⟩),
      fun m => hbmin m (mem_univ m)⟩
  | cast t =>
    rw [Fin.succ_castSucc]
    simpa only [Fin.snoc_castSucc] using hγ t

/-- Starting from any assignment `A₀` on identical machines, max-weight best-response dynamics
reach a pure Nash equilibrium in at most `|ι|` steps ([EvenDarKesselmanMansour2003];
[Vocking2007]). -/
theorem IsIdentical.exists_maxWeightBestResponse_isPureNash [Finite M] [Nonempty M]
    {G : LoadBalancingGame ι M} (hId : G.IsIdentical) (A₀ : ι → M) :
    ∃ (T : ℕ) (γ : Fin (T + 1) → (ι → M)) (move : Fin T → ι),
      T ≤ Fintype.card ι ∧
      γ 0 = A₀ ∧
      (∀ t : Fin T, G.IsMaxWeightBestResponseStep (γ t.succ) (γ t.castSucc) (move t)) ∧
      G.toCostGame.IsPureNash (γ (Fin.last T)) := by
  classical
  have : Fintype M := Fintype.ofFinite M
  suffices h : ∀ k : ℕ, k ≤ Fintype.card ι →
      ∀ (γ : Fin (k + 1) → (ι → M)) (move : Fin k → ι),
        γ 0 = A₀ →
        (∀ t : Fin k, G.IsMaxWeightBestResponseStep (γ t.succ) (γ t.castSucc) (move t)) →
        ∃ (T : ℕ) (γ' : Fin (T + 1) → (ι → M)) (move' : Fin T → ι),
          T ≤ Fintype.card ι ∧ γ' 0 = A₀ ∧
          (∀ t : Fin T, G.IsMaxWeightBestResponseStep (γ' t.succ) (γ' t.castSucc) (move' t)) ∧
          G.toCostGame.IsPureNash (γ' (Fin.last T)) by
    exact h 0 (Nat.zero_le _) (fun _ => A₀) Fin.elim0 rfl (fun t => t.elim0)
  intro k
  induction hrem : Fintype.card ι + 1 - k generalizing k with
  | zero => exact fun hk => absurd hk (by omega)
  | succ d ih =>
    intro hk γ move h0 hγ
    by_cases hNE : G.toCostGame.IsPureNash (γ (Fin.last k))
    · exact ⟨k, γ, move, hk, h0, hγ, hNE⟩
    · obtain ⟨γ₁, move₁, h0₁, hγ₁⟩ := exists_snoc_of_not_isPureNash γ move hγ hNE
      have hle := hId.maxWeightBestResponse_length_le γ₁ move₁ hγ₁
      exact ih (k + 1) (by omega) hle γ₁ move₁ (h0₁.trans h0) hγ₁

end MaxWeightBestResponse

section RelatedLPT

variable {n : ℕ} {M : Type*} [DecidableEq M]

/-- The load of machine `j` contributed by jobs with index `< k`. -/
@[expose] noncomputable def prefixLoad (G : LoadBalancingGame (Fin n) M) (A : Fin n → M) (k : ℕ)
    (j : M) : ℝ :=
  ∑ r : Fin n with r.val < k ∧ A r = j, G.weight r / G.speed j

/-- **Greedy post-insertion LPT property on uniformly related machines**
([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Vocking2007]): each job
`i`, processed in index order, is assigned to a machine minimizing its post-insertion load
`prefixLoad G A i k + weight i / speed k`. -/
@[expose] def IsRelatedLPT (G : LoadBalancingGame (Fin n) M) (A : Fin n → M) : Prop :=
  ∀ (i : Fin n) (k : M),
    G.prefixLoad A i (A i) + G.weight i / G.speed (A i) ≤
      G.prefixLoad A i k + G.weight i / G.speed k

private theorem prefixLoad_le_load (G : LoadBalancingGame (Fin n) M) (A : Fin n → M) (k : ℕ)
    (j : M) : G.prefixLoad A k j ≤ G.load A j := by
  rw [prefixLoad, load, UnrelatedLoadBalancingGame.load]
  exact sum_le_sum_of_subset_of_nonneg
    (fun r hr => mem_filter.mpr ⟨mem_univ r, (mem_filter.mp hr).2.2⟩)
    fun r _ _ => div_nonneg (G.weight_nonneg r) (G.speed_pos j).le

/-- **LPT produces a pure Nash equilibrium on uniformly related machines**
([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Vocking2007]): if jobs
are ordered by non-increasing weight (`Antitone G.weight`) and `A` places each job greedily on a
machine minimizing its post-insertion load, then `A` is a pure Nash equilibrium. -/
theorem IsRelatedLPT.isPureNash {G : LoadBalancingGame (Fin n) M} {A : Fin n → M}
    (hanti : Antitone G.weight) (hlpt : G.IsRelatedLPT A) :
    G.toCostGame.IsPureNash A := by
  rw [G.isPureNash_iff]
  intro i k _
  set S : Finset (Fin n) := univ.filter fun r => A r = A i
  have hSne : S.Nonempty := ⟨i, mem_filter.mpr ⟨mem_univ i, rfl⟩⟩
  let r : Fin n := S.max' hSne
  have hrS : r ∈ S := max'_mem S hSne
  have hAr : A r = A i := (mem_filter.mp hrS).2
  have hir : i ≤ r := le_max' S i (mem_filter.mpr ⟨mem_univ i, rfl⟩)
  -- Since `r` is the last job on machine `A i`, its post-insertion load equals `G.load A (A i)`.
  have hload_r : G.load A (A i) = G.prefixLoad A r (A r) + G.weight r / G.speed (A r) := by
    rw [hAr, load, UnrelatedLoadBalancingGame.load, prefixLoad]
    have hsplit : (univ.filter fun u : Fin n => A u = A i) =
        insert r (univ.filter fun u : Fin n => u.val < r.val ∧ A u = A i) := by
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      exact ⟨fun hu => (eq_or_lt_of_le (le_max' S u (mem_filter.mpr ⟨mem_univ u, hu⟩))).imp_right
        (⟨·, hu⟩), fun h => h.elim (· ▸ hAr) And.right⟩
    change ∑ u ∈ univ.filter (fun u : Fin n => A u = A i), G.weight u / G.speed (A i) = _
    rw [hsplit, sum_insert (by simp), add_comm]
  calc G.load A (A i)
      = G.prefixLoad A r (A r) + G.weight r / G.speed (A r) := hload_r
    _ ≤ G.prefixLoad A r k + G.weight r / G.speed k := hlpt r k
    _ ≤ G.load A k + G.weight r / G.speed k := by linarith [G.prefixLoad_le_load A r k]
    _ ≤ G.load A k + G.weight i / G.speed k := by
        linarith [div_le_div_of_nonneg_right (hanti hir) (G.speed_pos k).le]

/-- **Existence of an LPT pure Nash equilibrium** for any job ordering on uniformly related
machines ([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Vocking2007]):
every game admits an `IsRelatedLPT` assignment in any given job order. -/
theorem exists_isRelatedLPT [Finite M] [Nonempty M] (G : LoadBalancingGame (Fin n) M) :
    ∃ A : Fin n → M, G.IsRelatedLPT A := by
  have : Fintype M := Fintype.ofFinite M
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0⟩
  | succ n ih =>
    let G' : LoadBalancingGame (Fin n) M :=
      { weight := Fin.init G.weight
        speed := G.speed
        weight_nonneg := fun i => G.weight_nonneg i.castSucc
        speed_pos := G.speed_pos }
    obtain ⟨A', hA'⟩ := ih G'
    obtain ⟨b, -, hbmin⟩ := exists_min_image univ
      (fun k : M => G'.load A' k + G.weight (Fin.last n) / G.speed k) univ_nonempty
    let A : Fin (n + 1) → M := Fin.snoc (α := fun _ => M) A' b
    have hpre (k : ℕ) (hk : k ≤ n) (j : M) : G.prefixLoad A k j = G'.prefixLoad A' k j := by
      simp only [prefixLoad, sum_filter, Fin.sum_univ_castSucc, A, Fin.snoc_castSucc,
        Fin.val_castSucc, Fin.val_last, G', Fin.init]
      rw [ite_eq_right (by omega), add_zero]
    have hpre_last (j : M) : G.prefixLoad A n j = G'.load A' j := by
      rw [hpre n le_rfl j, prefixLoad, load, UnrelatedLoadBalancingGame.load]
      exact sum_congr (Finset.ext fun r => by simp) fun _ _ => rfl
    refine ⟨A, fun i k => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      simpa only [Fin.val_last, A, Fin.snoc_last, hpre_last] using hbmin k (mem_univ k)
    | cast i =>
      simpa only [Fin.val_castSucc, A, Fin.snoc_castSucc, hpre i.val i.isLt.le, G', Fin.init]
        using hA' i k

private theorem isPureNash_comp_symm (G : LoadBalancingGame (Fin n) M)
    (e : Equiv.Perm (Fin n)) {As : Fin n → M}
    (hNE : ({ weight := G.weight ∘ e
              speed := G.speed
              weight_nonneg := fun i => G.weight_nonneg (e i)
              speed_pos := G.speed_pos } : LoadBalancingGame (Fin n) M).toCostGame.IsPureNash As) :
    G.toCostGame.IsPureNash (As ∘ e.symm) := by
  let Gs : LoadBalancingGame (Fin n) M :=
    { weight := G.weight ∘ e
      speed := G.speed
      weight_nonneg := fun i => G.weight_nonneg (e i)
      speed_pos := G.speed_pos }
  have hload_eq (j : M) : G.load (As ∘ e.symm) j = Gs.load As j := by
    rw [G.load_eq_sum_div, Gs.load_eq_sum_div, sum_filter, sum_filter,
      ← Equiv.sum_comp e (fun i => if (As ∘ e.symm) i = j then G.weight i else 0)]
    exact congrArg (· / G.speed j) (sum_congr rfl fun i _ => by simp [Gs])
  rw [G.isPureNash_iff]
  intro i k _
  simpa only [hload_eq, Gs, Function.comp_apply, Equiv.apply_symm_apply] using
    Gs.isPureNash_load_le hNE (e.symm i) k

/-- **LPT algorithm produces a pure Nash equilibrium for any weight vector on uniformly related
machines** ([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Vocking2007]): sorting jobs
via `Cslib.Algorithms.Lean.Scheduling.lptOrder` and applying greedy
post-insertion load minimization yields a pure Nash equilibrium. -/
theorem exists_isPureNash_of_lptOrder [Finite M] [Nonempty M] (G : LoadBalancingGame (Fin n) M) :
    ∃ A : Fin n → M,
      let e := Cslib.Algorithms.Lean.Scheduling.lptOrder G.weight
      let Gs : LoadBalancingGame (Fin n) M :=
        { weight := G.weight ∘ e
          speed := G.speed
          weight_nonneg := fun i => G.weight_nonneg (e i)
          speed_pos := G.speed_pos }
      Gs.IsRelatedLPT (A ∘ e) ∧ G.toCostGame.IsPureNash A := by
  let e := Cslib.Algorithms.Lean.Scheduling.lptOrder G.weight
  let Gs : LoadBalancingGame (Fin n) M :=
    { weight := G.weight ∘ e
      speed := G.speed
      weight_nonneg := fun i => G.weight_nonneg (e i)
      speed_pos := G.speed_pos }
  obtain ⟨As, hAs⟩ := Gs.exists_isRelatedLPT
  refine ⟨As ∘ e.symm, ?_,
    G.isPureNash_comp_symm e
      (hAs.isPureNash (Cslib.Algorithms.Lean.Scheduling.antitone_comp_lptOrder G.weight))⟩
  simpa only [Gs, e, Function.comp_def, Equiv.symm_apply_apply] using hAs

/-- On identical machines (`Fin n` jobs, `Fin m` machines), `LoadBalancingGame.prefixLoad` agrees
with `Cslib.Algorithms.Lean.Scheduling.prefixLoad`. -/
theorem IsIdentical.prefixLoad_eq_scheduling {m : ℕ} {G : LoadBalancingGame (Fin n) (Fin m)}
    (hId : G.IsIdentical) (A : Fin n → Fin m) (k : ℕ) (j : Fin m) :
    G.prefixLoad A k j = Cslib.Algorithms.Lean.Scheduling.prefixLoad G.weight A k j := by
  rw [prefixLoad, Cslib.Algorithms.Lean.Scheduling.prefixLoad_def]
  refine sum_congr rfl fun r _ => ?_
  rw [hId j, div_one]

/-- On identical machines (`Fin n` jobs, `Fin m` machines), greedy post-insertion LPT
(`IsRelatedLPT`) coincides with Graham's list-scheduling condition
(`Cslib.Algorithms.Lean.Scheduling.IsListSchedule`). -/
theorem IsIdentical.isRelatedLPT_iff_isListSchedule {m : ℕ}
    {G : LoadBalancingGame (Fin n) (Fin m)} (hId : G.IsIdentical) (A : Fin n → Fin m) :
    G.IsRelatedLPT A ↔ Cslib.Algorithms.Lean.Scheduling.IsListSchedule G.weight A := by
  rw [IsRelatedLPT, Cslib.Algorithms.Lean.Scheduling.isListSchedule_iff]
  refine forall₂_congr fun i k => ?_
  rw [hId.prefixLoad_eq_scheduling, hId.prefixLoad_eq_scheduling, hId (A i), hId k, div_one,
    add_le_add_iff_right]

/-- **Graham's computable `lptSchedule` is a pure Nash equilibrium on identical machines**
([FotakisKontogiannisKoutsoupiasMavronicolasSpirakis2002]; [Vocking2007]). -/
theorem IsIdentical.isPureNash_lptSchedule {m : ℕ} [NeZero m]
    {G : LoadBalancingGame (Fin n) (Fin m)} (hId : G.IsIdentical) :
    G.toCostGame.IsPureNash (Cslib.Algorithms.Lean.Scheduling.lptSchedule G.weight) := by
  rw [Cslib.Algorithms.Lean.Scheduling.lptSchedule_def]
  let e := Cslib.Algorithms.Lean.Scheduling.lptOrder G.weight
  let Gs : LoadBalancingGame (Fin n) (Fin m) :=
    { weight := G.weight ∘ e
      speed := G.speed
      weight_nonneg := fun i => G.weight_nonneg (e i)
      speed_pos := G.speed_pos }
  have hIds : Gs.IsIdentical := hId
  have hLPT : Gs.IsRelatedLPT
      (Cslib.Algorithms.Lean.Scheduling.listSchedule (m := m) Gs.weight) :=
    (hIds.isRelatedLPT_iff_isListSchedule _).mpr
      (Cslib.Algorithms.Lean.Scheduling.isListSchedule_listSchedule Gs.weight)
  exact G.isPureNash_comp_symm e
    (hLPT.isPureNash (Cslib.Algorithms.Lean.Scheduling.antitone_comp_lptOrder G.weight))

/-- **Graham's `4 / 3 - 1 / (3m)` makespan bound for `lptSchedule` on identical machines**
([Graham1969]; [Vocking2007]). -/
theorem IsIdentical.makespan_lptSchedule_le {m : ℕ} [NeZero m]
    {G : LoadBalancingGame (Fin n) (Fin m)} (hId : G.IsIdentical) :
    G.makespan (Cslib.Algorithms.Lean.Scheduling.lptSchedule G.weight) ≤
      (4 / 3 - 1 / (3 * (m : ℝ))) * G.optMakespan := by
  rw [hId.makespan_eq_scheduling, hId.optMakespan_eq_scheduling]
  exact Cslib.Algorithms.Lean.Scheduling.makespan_lptSchedule_le G.weight G.weight_nonneg

end RelatedLPT

end LoadBalancingGame

end Cslib.GameTheory

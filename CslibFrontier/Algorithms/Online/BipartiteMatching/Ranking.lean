/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Online.BipartiteMatching.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Fintype.Perm
public import Mathlib.NumberTheory.Harmonic.Defs
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.TupleSampler
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The `RANKING` algorithm for online bipartite matching (`1 - 1/e`, tight)

This module formalizes the randomized `RANKING` algorithm of Karp, Vazirani, and Vazirani
[KarpVaziraniVazirani1990], proves its exact **`1 - 1/e`** competitive ratio via the randomized
primal-dual analysis of Devanur, Jain, and Kleinberg [DevanurJainKleinberg2013], and proves the
matching **`1 - 1/e + o(1)`** Yao minimax upper bound for all randomized online bipartite matching
algorithms against an oblivious adversary.

## Proof structure

1. **Key-based greedy matching (`rankingByKey`, `rankingDet`, `rankingAlg`):**
   Given an injective priority key `key : L → ℕ`, `rankingByKey key hkey` greedily matches each
   arriving online vertex to its unmatched neighbor minimizing `key`. `rankingAlg L` samples a
   ranking `π : L ≃ Fin (Fintype.card L)` uniformly at random and runs `rankingDet π`.
2. **Dominance and monotonicity (`rankingByKey_monotone_choice`, `rankingByKey_dominance`):**
   Comparing `rankingByKey` on `arrivals` and on `deleteOffline u arrivals` via a three-state
   alternating-path invariant (`same`, `justU`, `shifted w`) proves both:
   - **Monotonicity:** if online vertex `j` is matched to `w` without `u`, then with `u` it is
     matched to some `a` with `key a ≤ key w`.
   - **Dominance:** if `u ∈ arrivals[j]` remains unmatched in `arrivals`, then `arrivals` and
     `deleteOffline u arrivals` produce identical matchings and `j` is matched to some `w` with
     `key w < key u`.
3. **Discrete randomized primal-dual fitting (`djkWeight`, `rankingGridAlg`,
   `rankingGrid_competitive_ratio`):**
   Sampling i.i.d. uniform discrete ranks `y : L → Fin K` (breaking ties by a fixed order
   `ord : L ≃ Fin n`) with discrete weight `djkWeight K r = (K / (K + 1)) ^ (K - r)`, we define
   explicit primal-dual variables `djkDualLeft` and `djkDualRight` summing to the matching size
   (`sum_djkDual_eq_card`) whose average over `y u ∈ Fin K` is at least `1 - (K / (K + 1)) ^ K`
   for every edge (`sum_djkDual_update_ge`). Averaging over `y` yields ratio
   `1 - (K / (K + 1)) ^ K` for `rankingGridAlg L K`.
4. **Exact `1 - 1/e` competitive ratio (`ranking_competitive_ratio`):**
   Conditioned on `y : L → Fin K` being injective (which happens with probability
   `K.descFactorial n / K ^ n → 1` as `K → ∞`), `rankingGridDet y ord` induces a uniform random
   permutation `π : L ≃ Fin n`. Passing to the limit `K → ∞` gives the exact bound
   `(1 - Real.exp (-1)) * M.card ≤ expectedMatchingSize (rankingAlg L) arrivals` for every finite
   `L`, every arrival sequence `arrivals`, and every matching `M`.
5. **Tight `1 - 1/e` Yao minimax upper bound (`triArrivals`, `det_triArrivals_avg_le_harmonic`,
   `exists_rand_harmonic_upper_bound`, `exists_rand_exp_upper_bound`,
   `not_rand_competitive_of_gt_one_sub_exp_neg_one`):**
   On a uniformly permuted upper-triangular graph `triArrivals n σ` (which always has a perfect
   matching of size `n`), the symmetry `σ ↦ σ * Equiv.swap t j` yields the exact telescoping
   recurrence `(n - t) * E[U_{t+1}] = (n - t - 1) * (E[U_t] - p_t)`, implying
   `∑ t, p_t / (n - t) ≤ 1` and hence `E[|M|] ≤ n - s * (harmonic n - harmonic s)` for every
   `s ≤ n` (in particular `3/4 * OPT` at `n = 2`, and `(1 - 1/e) * n + 2` for all `n ≥ 1`).
   Yao's principle transfers this bound to every randomized online algorithm.

## Main definitions

* `Cslib.Algorithms.Online.BipartiteMatching.minByKey`, `rankingByKey`, `rankingDet`,
  `rankingAlg`: deterministic key-ordered matching and the randomized `RANKING` algorithm.
* `Cslib.Algorithms.Online.BipartiteMatching.deleteOffline`: deleting an offline vertex from an
  arrival sequence.
* `Cslib.Algorithms.Online.BipartiteMatching.djkWeight`, `rankingGridDet`, `rankingGridAlg`,
  `djkDualLeft`, `djkDualRight`: discrete DJK randomized primal-dual construction.
* `Cslib.Algorithms.Online.BipartiteMatching.triArrivals`, `triPerfectMatching`: the permuted
  upper-triangular hard family for Yao's minimax upper bound.

## Main results

* `Cslib.Algorithms.Online.BipartiteMatching.rankingByKey_monotone_choice`,
  `rankingByKey_dominance`: monotonicity and dominance lemmas for `RANKING`.
* `Cslib.Algorithms.Online.BipartiteMatching.sum_djkDual_eq_card`, `sum_djkDual_update_ge`,
  `rankingGrid_competitive_ratio`: discrete primal-dual feasibility and `1 - (K / (K + 1)) ^ K`
  bound.
* `Cslib.Algorithms.Online.BipartiteMatching.ranking_competitive_ratio`: `RANKING` achieves exact
  competitive ratio `1 - 1/e` on every finite bipartite graph.
* `Cslib.Algorithms.Online.BipartiteMatching.det_triArrivals_avg_le_harmonic`,
  `exists_rand_harmonic_upper_bound`, `exists_rand_exp_upper_bound`,
  `not_rand_competitive_of_gt_one_sub_exp_neg_one`: no randomized online matching algorithm beats
  `1 - 1/e` against an oblivious adversary.

## References

* [R. M. Karp, U. V. Vazirani, and V. V. Vazirani, *An Optimal Algorithm for On-line Bipartite
  Matching*][KarpVaziraniVazirani1990]
* [N. R. Devanur, K. Jain, and R. D. Kleinberg, *Randomized Primal-Dual Analysis of RANKING for
  Online Bipartite Matching*][DevanurJainKleinberg2013]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

open scoped Topology
open Filter Finset

public section

namespace Cslib.Algorithms.Online.BipartiteMatching

open Cslib.Algorithms.Lean.MaxFlow

/-! ### Key-ordered greedy matching and `RANKING` -/

section RankingDef

variable {L : Type*}

/-- Binary minimum selector on `Option L` with respect to a key function `key : L → ℕ`. -/
@[expose] def minOpt (key : L → ℕ) : Option L → Option L → Option L
  | none, y => y
  | x, none => x
  | some a, some b => some (if key a ≤ key b then a else b)

theorem minOpt_comm {key : L → ℕ} (hkey : Function.Injective key) :
    Std.Commutative (minOpt key) :=
  ⟨fun x y => by
    cases x with
    | none => cases y <;> rfl
    | some a =>
      cases y with
      | none => rfl
      | some b =>
        simp only [minOpt]
        split_ifs with h₁ h₂
        · exact congrArg some (hkey (le_antisymm h₁ h₂))
        · rfl
        · rfl
        · omega⟩

theorem minOpt_assoc (key : L → ℕ) :
    Std.Associative (minOpt key) :=
  ⟨fun x y z => by
    cases x with
    | none => rfl
    | some a =>
      cases y with
      | none => rfl
      | some b =>
        cases z with
        | none => rfl
        | some c =>
          simp only [minOpt]
          split_ifs <;> first | rfl | omega⟩

/-- Computable minimum-key element of a finite set `U : Finset L` for an injective key
`key : L → ℕ`. Returns `none` iff `U = ∅`. -/
@[expose] def minByKey (key : L → ℕ) (hkey : Function.Injective key)
    (U : Finset L) : Option L :=
  haveI : Std.Commutative (minOpt key) := minOpt_comm hkey
  haveI : Std.Associative (minOpt key) := minOpt_assoc key
  U.fold (minOpt key) none some

@[simp] theorem minByKey_empty (key : L → ℕ) (hkey : Function.Injective key) :
    minByKey key hkey ∅ = none :=
  rfl

private theorem minByKey_insert [DecidableEq L] (key : L → ℕ) (hkey : Function.Injective key)
    {a : L} {s : Finset L} (ha : a ∉ s) :
    minByKey key hkey (insert a s) = minOpt key (some a) (minByKey key hkey s) := by
  have : Std.Commutative (minOpt key) := minOpt_comm hkey
  have : Std.Associative (minOpt key) := minOpt_assoc key
  unfold minByKey
  exact Finset.fold_insert ha

theorem minByKey_eq_none_iff (key : L → ℕ) (hkey : Function.Injective key) (U : Finset L) :
    minByKey key hkey U = none ↔ U = ∅ := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [minByKey_insert key hkey ha]
    cases minByKey key hkey s <;> simp [minOpt]

theorem minByKey_eq_some_iff (key : L → ℕ) (hkey : Function.Injective key) (U : Finset L) (u : L) :
    minByKey key hkey U = some u ↔ u ∈ U ∧ ∀ w ∈ U, key u ≤ key w := by
  classical
  have hspec : ∀ v, minByKey key hkey U = some v → v ∈ U ∧ ∀ w ∈ U, key v ≤ key w := by
    induction U using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      intro v hv
      rw [minByKey_insert key hkey ha] at hv
      cases hs : minByKey key hkey s with
      | none =>
        have hse := (minByKey_eq_none_iff key hkey s).mp hs
        simp only [hs, minOpt, Option.some.injEq] at hv
        simp [hse, ← hv]
      | some b =>
        obtain ⟨hbs, hbmin⟩ := ih b hs
        simp only [hs, minOpt, Option.some.injEq] at hv
        subst v
        simp only [mem_insert, forall_eq_or_imp]
        split_ifs with hab
        · exact ⟨Or.inl rfl, le_rfl, fun w hw => hab.trans (hbmin w hw)⟩
        · exact ⟨Or.inr hbs, (lt_of_not_ge hab).le, hbmin⟩
  refine ⟨hspec u, fun ⟨hu, hmin⟩ => ?_⟩
  cases hv : minByKey key hkey U with
  | none => exact (notMem_empty u ((minByKey_eq_none_iff key hkey U).mp hv ▸ hu)).elim
  | some v =>
    obtain ⟨hvU, hvmin⟩ := hspec v hv
    exact congrArg some (hkey (le_antisymm (hvmin u hu) (hmin v hvU)))

theorem minByKey_congr_order {key₁ key₂ : L → ℕ} (h₁ : Function.Injective key₁)
    (h₂ : Function.Injective key₂) {U : Finset L}
    (hord : ∀ a ∈ U, ∀ b ∈ U, key₁ a ≤ key₁ b ↔ key₂ a ≤ key₂ b) :
    minByKey key₁ h₁ U = minByKey key₂ h₂ U := by
  cases hm : minByKey key₁ h₁ U with
  | none =>
    have hU : U = ∅ := (minByKey_eq_none_iff key₁ h₁ U).mp hm
    rw [hU, minByKey_empty]
  | some u =>
    obtain ⟨hu, hmin⟩ := (minByKey_eq_some_iff key₁ h₁ U u).mp hm
    symm
    exact (minByKey_eq_some_iff key₂ h₂ U u).mpr
      ⟨hu, fun w hw => (hord u hu w hw).mp (hmin w hw)⟩

/-- Deterministic greedy online matching algorithm matching each arriving vertex to the unmatched
neighbor minimizing `key`. -/
@[expose] def rankingByKey [DecidableEq L] (key : L → ℕ) (hkey : Function.Injective key) :
    DetAlg L :=
  ⟨fun _ matched N => minByKey key hkey (N \ matched)⟩

theorem onlineStep_rankingByKey [DecidableEq L] (key : L → ℕ) (hkey : Function.Injective key)
    (hist : List (Finset L)) (matched N : Finset L) :
    onlineStep matched N ((rankingByKey key hkey).choose hist matched N) =
      minByKey key hkey (N \ matched) := by
  simp only [rankingByKey]
  cases hm : minByKey key hkey (N \ matched) with
  | none => rfl
  | some u =>
    obtain ⟨hu, _⟩ := (minByKey_eq_some_iff key hkey (N \ matched) u).mp hm
    rw [Finset.mem_sdiff] at hu
    simp [onlineStep, hu.1, hu.2]

theorem isGreedy_rankingByKey [DecidableEq L] (key : L → ℕ) (hkey : Function.Injective key) :
    (rankingByKey key hkey).IsGreedy := by
  intro hist matched N ⟨u, huN, hum⟩
  have hne : (N \ matched).Nonempty := ⟨u, Finset.mem_sdiff.mpr ⟨huN, hum⟩⟩
  cases hm : minByKey key hkey (N \ matched) with
  | none => exact absurd ((minByKey_eq_none_iff key hkey _).mp hm) hne.ne_empty
  | some w =>
    obtain ⟨hw, _⟩ := (minByKey_eq_some_iff key hkey _ w).mp hm
    rw [Finset.mem_sdiff] at hw
    exact ⟨w, hw.1, hw.2, hm⟩

theorem rankingByKey_congr_order [DecidableEq L] {key₁ key₂ : L → ℕ}
    (h₁ : Function.Injective key₁) (h₂ : Function.Injective key₂) (arrivals : List (Finset L))
    (hord : ∀ N ∈ arrivals, ∀ a ∈ N, ∀ b ∈ N, key₁ a ≤ key₁ b ↔ key₂ a ≤ key₂ b) :
    (rankingByKey key₁ h₁).runChoices arrivals = (rankingByKey key₂ h₂).runChoices arrivals := by
  suffices ∀ hist₁ hist₂ matched (rest : List (Finset L)),
      (∀ N ∈ rest, ∀ a ∈ N, ∀ b ∈ N, key₁ a ≤ key₁ b ↔ key₂ a ≤ key₂ b) →
      (rankingByKey key₁ h₁).runChoicesFrom hist₁ matched rest =
        (rankingByKey key₂ h₂).runChoicesFrom hist₂ matched rest from
    this [] [] ∅ arrivals hord
  intro hist₁ hist₂ matched rest
  induction rest generalizing hist₁ hist₂ matched with
  | nil => intro _; rfl
  | cons N rest ih =>
    intro hrest
    simp only [DetAlg.runChoicesFrom, onlineStep_rankingByKey]
    have hstep : minByKey key₁ h₁ (N \ matched) = minByKey key₂ h₂ (N \ matched) :=
      minByKey_congr_order h₁ h₂ fun a ha b hb =>
        hrest N List.mem_cons_self a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
    rw [hstep, ih _ _ _ fun M hM => hrest M (List.mem_cons_of_mem _ hM)]

/-- Deterministic `RANKING` with a fixed ranking bijection `π : L ≃ Fin (Fintype.card L)`. -/
@[expose] def rankingDet [Fintype L] [DecidableEq L]
    (π : L ≃ Fin (Fintype.card L)) : DetAlg L :=
  rankingByKey (fun u => (π u : ℕ)) (Fin.val_injective.comp π.injective)

/-- The randomized **`RANKING`** algorithm [KarpVaziraniVazirani1990]: sample a ranking
`π : L ≃ Fin (Fintype.card L)` uniformly at random and run `rankingDet π`. -/
noncomputable def rankingAlg (L : Type*) [Fintype L] [DecidableEq L] : RandAlg L :=
  haveI : Nonempty (L ≃ Fin (Fintype.card L)) := ⟨Fintype.equivFin L⟩
  (Cslib.Probability.PMF.uniformOfFintype (L ≃ Fin (Fintype.card L))).map rankingDet

theorem expectedMatchingSize_rankingAlg [Fintype L] [DecidableEq L] (arrivals : List (Finset L)) :
    RandAlg.expectedMatchingSize (rankingAlg L) arrivals =
      (∑ π : L ≃ Fin (Fintype.card L), (((rankingDet π).runMatching arrivals).card : ℝ)) /
        (Fintype.card (L ≃ Fin (Fintype.card L)) : ℝ) := by
  have : Nonempty (L ≃ Fin (Fintype.card L)) := ⟨Fintype.equivFin L⟩
  exact RandAlg.expectedMatchingSize_map_uniformOfFintype rankingDet arrivals

end RankingDef

/-! ### Dominance and monotonicity (three-state alternating-path invariant) -/

section DominanceMonotonicity

variable {L : Type*} [DecidableEq L]

/-- Delete offline vertex `u` from every neighborhood in an arrival sequence. -/
@[expose] def deleteOffline (u : L) (arrivals : List (Finset L)) : List (Finset L) :=
  arrivals.map (·.erase u)

@[simp] theorem length_deleteOffline (u : L) (arrivals : List (Finset L)) :
    (deleteOffline u arrivals).length = arrivals.length :=
  List.length_map _

/-- Three-state invariant relating the matched offline sets of `rankingByKey` on `G` (`S`) and on
`G - u` (`S'`). -/
private inductive StepRel (u : L) : Finset L → Finset L → Prop
  | same (S : Finset L) (hu : u ∉ S) : StepRel u S S
  | justU (S' : Finset L) (hu : u ∉ S') : StepRel u (insert u S') S'
  | shifted (S₀ : Finset L) (w : L) (hu : u ∉ S₀) (hw : w ∉ S₀) (hne : w ≠ u) :
      StepRel u (insert u S₀) (insert w S₀)

private theorem stepRel_step {key : L → ℕ} (hkey : Function.Injective key)
    {u : L} {S S' : Finset L} (hrel : StepRel u S S') (N : Finset L) :
    let c := minByKey key hkey (N \ S)
    let c' := minByKey key hkey (N.erase u \ S')
    StepRel u (updateMatched S c) (updateMatched S' c') ∧
      (∀ w, c' = some w → ∃ a, c = some a ∧ key a ≤ key w) := by
  intro c c'
  cases hrel with
  | same S hu =>
    have hU' : N.erase u \ S = (N \ S).erase u := Finset.ext fun _ => by
      simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
    cases hc : c with
    | none =>
      have hU : N \ S = ∅ := (minByKey_eq_none_iff key hkey _).mp hc
      have hc' : c' = none := by
        change minByKey key hkey (N.erase u \ S) = none
        rw [hU', hU, Finset.erase_empty, minByKey_empty]
      rw [hc']
      exact ⟨StepRel.same S hu, fun _ h => by cases h⟩
    | some a =>
      obtain ⟨haU, hamin⟩ := (minByKey_eq_some_iff key hkey (N \ S) a).mp hc
      by_cases hau : a = u
      · subst hau
        cases hc' : c' with
        | none =>
          exact ⟨StepRel.justU S hu, fun _ h => by cases h⟩
        | some w =>
          obtain ⟨hwU', _⟩ := (minByKey_eq_some_iff key hkey (N.erase a \ S) w).mp hc'
          rw [hU', Finset.mem_erase, Finset.mem_sdiff] at hwU'
          refine ⟨StepRel.shifted S w hu hwU'.2.2 hwU'.1, ?_⟩
          rintro _ ⟨rfl⟩
          exact ⟨a, rfl, hamin w (Finset.mem_sdiff.mpr hwU'.2)⟩
      · have hc' : c' = some a := (minByKey_eq_some_iff key hkey (N.erase u \ S) a).mpr <| by
          rw [hU']
          exact ⟨Finset.mem_erase.mpr ⟨hau, haU⟩,
            fun x hx => hamin x (Finset.mem_of_mem_erase hx)⟩
        rw [hc']
        refine ⟨StepRel.same (insert a S) (by simp [Ne.symm hau, hu]), ?_⟩
        rintro _ ⟨rfl⟩
        exact ⟨a, rfl, le_rfl⟩
  | justU S' hu =>
    have hU : N \ insert u S' = N.erase u \ S' := Finset.ext fun _ => by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    have hcc' : c = c' := congrArg (minByKey key hkey) hU
    cases hc : c with
    | none =>
      rw [← hcc', hc]
      exact ⟨StepRel.justU S' hu, fun _ h => by cases h⟩
    | some a =>
      rw [← hcc', hc]
      obtain ⟨haU, _⟩ := (minByKey_eq_some_iff key hkey (N \ insert u S') a).mp hc
      have hau : a ≠ u := by
        rw [hU, Finset.mem_sdiff, Finset.mem_erase] at haU
        exact haU.1.1
      rw [updateMatched, updateMatched, Finset.insert_comm a u S']
      refine ⟨StepRel.justU (insert a S') (by simp [Ne.symm hau, hu]), ?_⟩
      rintro _ ⟨rfl⟩
      exact ⟨a, rfl, le_rfl⟩
  | shifted S₀ w hu hw hne =>
    have hU' : N.erase u \ insert w S₀ = (N \ insert u S₀).erase w := Finset.ext fun _ => by
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    cases hc : c with
    | none =>
      have hU : N \ insert u S₀ = ∅ := (minByKey_eq_none_iff key hkey _).mp hc
      have hc' : c' = none := by
        change minByKey key hkey (N.erase u \ insert w S₀) = none
        rw [hU', hU, Finset.erase_empty, minByKey_empty]
      rw [hc']
      exact ⟨StepRel.shifted S₀ w hu hw hne, fun _ h => by cases h⟩
    | some a =>
      obtain ⟨haU, hamin⟩ := (minByKey_eq_some_iff key hkey (N \ insert u S₀) a).mp hc
      have ha_props : a ∈ N ∧ a ≠ u ∧ a ∉ S₀ := by
        simpa [Finset.mem_sdiff, Finset.mem_insert] using haU
      by_cases haw : a = w
      · subst haw
        cases hc' : c' with
        | none =>
          rw [updateMatched, updateMatched, Finset.insert_comm a u S₀]
          exact ⟨StepRel.justU (insert a S₀) (by simp [Ne.symm ha_props.2.1, hu]),
            fun _ h => by cases h⟩
        | some w' =>
          obtain ⟨hw'U', _⟩ :=
            (minByKey_eq_some_iff key hkey (N.erase u \ insert a S₀) w').mp hc'
          rw [hU', Finset.mem_erase] at hw'U'
          have hw'_props : w' ∈ N ∧ w' ≠ u ∧ w' ∉ S₀ := by
            simpa [Finset.mem_sdiff, Finset.mem_insert] using hw'U'.2
          rw [updateMatched, updateMatched, Finset.insert_comm a u S₀]
          refine ⟨StepRel.shifted (insert a S₀) w' (by simp [Ne.symm ha_props.2.1, hu])
            (by simp [hw'U'.1, hw'_props.2.2]) hw'_props.2.1, ?_⟩
          rintro _ ⟨rfl⟩
          exact ⟨a, rfl, hamin w' hw'U'.2⟩
      · have hc' : c' = some a :=
          (minByKey_eq_some_iff key hkey (N.erase u \ insert w S₀) a).mpr <| by
            rw [hU']
            exact ⟨Finset.mem_erase.mpr ⟨haw, haU⟩,
              fun x hx => hamin x (Finset.mem_of_mem_erase hx)⟩
        rw [hc', updateMatched, updateMatched, Finset.insert_comm a u S₀,
          Finset.insert_comm a w S₀]
        refine ⟨StepRel.shifted (insert a S₀) w (by simp [Ne.symm ha_props.2.1, hu])
          (by simp [Ne.symm haw, hw]) hne, ?_⟩
        rintro _ ⟨rfl⟩
        exact ⟨a, rfl, le_rfl⟩

/-- **Monotonicity lemma** [DevanurJainKleinberg2013]: if online vertex `j` is matched to `w` when
offline vertex `u` is deleted, then in the full graph `j` is matched to some vertex `a` of priority
`key a ≤ key w`. -/
theorem rankingByKey_monotone_choice {key : L → ℕ} (hkey : Function.Injective key)
    (u : L) (arrivals : List (Finset L)) (j : Fin arrivals.length) {w : L}
    (hw : ((rankingByKey key hkey).runChoices (deleteOffline u arrivals))[j.val]'(by
      simp [j.isLt]) = some w) :
    ∃ a, ((rankingByKey key hkey).runChoices arrivals)[j.val]'(by simp [j.isLt]) = some a ∧
      key a ≤ key w := by
  suffices ∀ (hist hist' : List (Finset L)) (S S' : Finset L) (rest : List (Finset L)),
      StepRel u S S' →
      ∀ (i : ℕ) (hi : i < rest.length) (w : L),
        ((rankingByKey key hkey).runChoicesFrom hist' S'
          (deleteOffline u rest))[i]'(by simp [hi]) = some w →
        ∃ a, ((rankingByKey key hkey).runChoicesFrom hist S rest)[i]'(by simp [hi]) = some a ∧
          key a ≤ key w from
    this [] [] ∅ ∅ arrivals (StepRel.same ∅ (by simp)) j.val j.isLt w hw
  intro hist hist' S S' rest
  induction rest generalizing hist hist' S S' with
  | nil => intro _ i hi; simp at hi
  | cons N rest ih =>
    intro hrel i hi w' hw'
    obtain ⟨hrel_next, hmono_head⟩ := stepRel_step hkey hrel N
    cases i with
    | zero =>
      simp only [deleteOffline, List.map_cons, DetAlg.runChoicesFrom, onlineStep_rankingByKey,
        List.getElem_cons_zero] at hw' ⊢
      exact hmono_head w' hw'
    | succ i' =>
      simp only [deleteOffline, List.map_cons, DetAlg.runChoicesFrom, onlineStep_rankingByKey,
        List.getElem_cons_succ] at hw' ⊢
      exact ih _ _ _ _ hrel_next i' (Nat.lt_of_succ_lt_succ hi) w' hw'

private theorem rankingByKey_runChoices_eq_deleteOffline_of_notMem {key : L → ℕ}
    (hkey : Function.Injective key) (u : L) :
    ∀ (hist hist' : List (Finset L)) (S : Finset L) (rest : List (Finset L)),
      u ∉ (rankingByKey key hkey).matchedLeftFrom hist S rest →
      (rankingByKey key hkey).runChoicesFrom hist S rest =
        (rankingByKey key hkey).runChoicesFrom hist' S (deleteOffline u rest)
  | _, _, _, [], _ => rfl
  | hist, hist', S, N :: rest, hnot => by
    have hnot_head : minByKey key hkey (N \ S) ≠ some u := by
      intro heq
      apply hnot
      rw [DetAlg.mem_matchedLeftFrom_iff]
      exact Or.inr (by simp [DetAlg.runChoicesFrom, onlineStep_rankingByKey, heq])
    have hU' : N.erase u \ S = (N \ S).erase u := Finset.ext fun _ => by
      simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
    have hstep_eq : minByKey key hkey (N \ S) = minByKey key hkey (N.erase u \ S) := by
      cases hc : minByKey key hkey (N \ S) with
      | none =>
        rw [hU', (minByKey_eq_none_iff key hkey _).mp hc, Finset.erase_empty, minByKey_empty]
      | some a =>
        obtain ⟨haU, hamin⟩ := (minByKey_eq_some_iff key hkey (N \ S) a).mp hc
        symm
        rw [minByKey_eq_some_iff, hU']
        exact ⟨Finset.mem_erase.mpr ⟨fun h => hnot_head (h ▸ hc), haU⟩,
          fun x hx => hamin x (Finset.mem_of_mem_erase hx)⟩
    have hnot_tail :
        u ∉ (rankingByKey key hkey).matchedLeftFrom (hist ++ [N])
          (updateMatched S (minByKey key hkey (N \ S))) rest := by
      simpa only [DetAlg.matchedLeftFrom, onlineStep_rankingByKey] using hnot
    simp only [deleteOffline, List.map_cons, DetAlg.runChoicesFrom, onlineStep_rankingByKey]
    rw [← hstep_eq,
      rankingByKey_runChoices_eq_deleteOffline_of_notMem hkey u
        (hist ++ [N]) (hist' ++ [N.erase u]) _ rest hnot_tail]
    rfl

/-- **Dominance lemma** [DevanurJainKleinberg2013]: if `(u, j)` is an edge (`u ∈ arrivals[j]`) and
offline vertex `u` remains unmatched by `rankingByKey key hkey` on `arrivals`, then:
1. deleting `u` leaves all match choices unchanged; and
2. in `deleteOffline u arrivals`, online vertex `j` is matched to some offline vertex `w` of
   strictly higher priority (`key w < key u`). -/
theorem rankingByKey_dominance {key : L → ℕ} (hkey : Function.Injective key)
    (u : L) (arrivals : List (Finset L)) (j : Fin arrivals.length)
    (huj : u ∈ arrivals[j.val])
    (hnot : u ∉ (rankingByKey key hkey).matchedLeft arrivals) :
    (rankingByKey key hkey).runChoices arrivals =
      (rankingByKey key hkey).runChoices (deleteOffline u arrivals) ∧
    ∃ w, ((rankingByKey key hkey).runChoices (deleteOffline u arrivals))[j.val]'(by simp [j.isLt]) =
        some w ∧ key w < key u := by
  have heq : (rankingByKey key hkey).runChoices arrivals =
      (rankingByKey key hkey).runChoices (deleteOffline u arrivals) :=
    rankingByKey_runChoices_eq_deleteOffline_of_notMem hkey u [] [] ∅ arrivals hnot
  refine ⟨heq, ?_⟩
  set pre := (rankingByKey key hkey).matchedLeft (arrivals.take j.val)
  have hu_pre : u ∉ pre :=
    fun hm => hnot ((rankingByKey key hkey).matchedLeft_take_subset arrivals j.val hm)
  have hne : (arrivals[j.val] \ pre).Nonempty := ⟨u, Finset.mem_sdiff.mpr ⟨huj, hu_pre⟩⟩
  cases hc : minByKey key hkey (arrivals[j.val] \ pre) with
  | none => exact absurd ((minByKey_eq_none_iff key hkey _).mp hc) hne.ne_empty
  | some w =>
    obtain ⟨_, hwmin⟩ := (minByKey_eq_some_iff key hkey _ w).mp hc
    have hget :
        ((rankingByKey key hkey).runChoices arrivals)[j.val]'(by simp [j.isLt]) = some w := by
      rw [(rankingByKey key hkey).runChoices_getElem arrivals j.isLt, onlineStep_rankingByKey]
      exact hc
    have hwu : w ≠ u := by
      rintro rfl
      apply hnot
      rw [DetAlg.mem_matchedLeft_iff, List.mem_iff_getElem]
      exact ⟨j.val, by simp [j.isLt], hget⟩
    exact ⟨w, by simpa only [heq] using hget,
      lt_of_le_of_ne (hwmin u (Finset.mem_sdiff.mpr ⟨huj, hu_pre⟩)) (fun h => hwu (hkey h))⟩

end DominanceMonotonicity

/-! ### Discrete Devanur–Jain–Kleinberg randomized primal-dual analysis -/

section DiscreteDJK

/-- Discrete DJK dual weight `g_K(r) = (K / (K + 1)) ^ (K - r)` for rank `r ≤ K`. -/
@[expose] noncomputable def djkWeight (K r : ℕ) : ℝ :=
  ((K : ℝ) / ((K : ℝ) + 1)) ^ (K - r)

theorem djkWeight_nonneg (K r : ℕ) : 0 ≤ djkWeight K r := by
  unfold djkWeight
  positivity

theorem djkWeight_le_one (K r : ℕ) : djkWeight K r ≤ 1 := by
  unfold djkWeight
  refine pow_le_one₀ (by positivity) ?_
  rw [div_le_one (by positivity)]
  linarith

theorem djkWeight_mono {K r₁ r₂ : ℕ} (h : r₁ ≤ r₂) :
    djkWeight K r₁ ≤ djkWeight K r₂ :=
  pow_le_pow_of_le_one (by positivity)
    ((div_le_one (by positivity)).mpr (by linarith)) (Nat.sub_le_sub_left h K)

private theorem sum_djkWeight_range {K t : ℕ} (ht : t ≤ K) :
    ∑ k ∈ Finset.range t, djkWeight K k =
      (K : ℝ) * (djkWeight K t - djkWeight K 0) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le ht)]
    have hsub : K - t = (K - (t + 1)) + 1 := by omega
    have hstep : djkWeight K t = ((K : ℝ) / ((K : ℝ) + 1)) * djkWeight K (t + 1) := by
      simp only [djkWeight, hsub, pow_succ']
    have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
    rw [hstep]
    field_simp [hK1]
    ring

private theorem djkWeight_balance {K t : ℕ} (ht : t ≤ K) :
    (∑ k ∈ Finset.range t, djkWeight K k) + (K : ℝ) * (1 - djkWeight K t) =
      (K : ℝ) * (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) := by
  rw [sum_djkWeight_range ht]
  simp only [djkWeight, Nat.sub_zero]
  ring

section GridKey

variable {L : Type*} [Fintype L]

/-- Lexicographic priority key `n * y(u) + ord(u)` for discrete ranks `y : L → Fin K` with
deterministic tie-breaking `ord : L ≃ Fin (Fintype.card L)`. -/
@[expose] def gridKey {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L)) (u : L) : ℕ :=
  Fintype.card L * (y u).val + (ord u).val

theorem gridKey_injective {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L)) :
    Function.Injective (gridKey y ord) := by
  intro u v h
  have hmod := congrArg (· % Fintype.card L) h
  simp only [gridKey, Nat.mul_add_mod, Nat.mod_eq_of_lt (ord u).isLt,
    Nat.mod_eq_of_lt (ord v).isLt] at hmod
  exact ord.injective (Fin.ext hmod)

private theorem val_le_of_gridKey_le {K : ℕ} {y : L → Fin K} {ord : L ≃ Fin (Fintype.card L)}
    {u v : L} (h : gridKey y ord u ≤ gridKey y ord v) :
    (y u).val ≤ (y v).val := by
  simp only [gridKey] at h
  by_contra! hgt
  have hmul := Nat.mul_le_mul_left (Fintype.card L) hgt
  rw [Nat.mul_succ] at hmul
  have := (ord v).isLt
  omega

end GridKey

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- Deterministic `RANKING` on discrete ranks `y : L → Fin K` with tie-breaker `ord`. -/
@[expose] def rankingGridDet {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L)) :
    DetAlg L :=
  rankingByKey (gridKey y ord) (gridKey_injective y ord)

/-- Randomized `RANKING` sampling i.i.d. uniform discrete ranks `y : L → Fin K` with fixed
tie-breaker `ord`. -/
noncomputable def rankingGridAlg (L : Type*) [Fintype L] [DecidableEq L]
    (K : ℕ) (hK : 0 < K) (ord : L ≃ Fin (Fintype.card L)) : RandAlg L :=
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  (Cslib.Probability.PMF.uniformOfFintype (L → Fin K)).map fun y => rankingGridDet y ord

/-- DJK dual variable `α(y, u)` for offline vertex `u`: `djkWeight K (y u)` if `u` is matched,
else `0`. -/
noncomputable def djkDualLeft {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L))
    (arrivals : List (Finset L)) (u : L) : ℝ :=
  if u ∈ (rankingGridDet y ord).matchedLeft arrivals then djkWeight K (y u).val else 0

/-- DJK dual variable `β(y, j)` for online vertex `j`: `1 - djkWeight K (y a)` if `j` is matched
to `a`, else `0`. -/
noncomputable def djkDualRight {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L))
    (arrivals : List (Finset L)) (j : Fin arrivals.length) : ℝ :=
  match ((rankingGridDet y ord).runChoices arrivals)[j.val]'(by simp [j.isLt]) with
  | some a => 1 - djkWeight K (y a).val
  | none => 0

theorem djkDualLeft_nonneg {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L))
    (arrivals : List (Finset L)) (u : L) :
    0 ≤ djkDualLeft y ord arrivals u := by
  unfold djkDualLeft
  split_ifs
  · exact djkWeight_nonneg K (y u).val
  · exact le_rfl

theorem djkDualRight_nonneg {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L))
    (arrivals : List (Finset L)) (j : Fin arrivals.length) :
    0 ≤ djkDualRight y ord arrivals j := by
  unfold djkDualRight
  cases ((rankingGridDet y ord).runChoices arrivals)[j.val]'(by simp [j.isLt]) with
  | none => exact le_rfl
  | some a => linarith [djkWeight_le_one K (y a).val]

/-- **Exact primal-dual equality:** for every discrete rank vector `y`, the dual variables sum to
the matching size `|M(y)|`. -/
theorem sum_djkDual_eq_card {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L))
    (arrivals : List (Finset L)) :
    (∑ u : L, djkDualLeft y ord arrivals u) +
      (∑ j : Fin arrivals.length, djkDualRight y ord arrivals j) =
      (((rankingGridDet y ord).runMatching arrivals).card : ℝ) := by
  set A := rankingGridDet y ord
  set M := A.runMatching arrivals
  have hM := A.isMatching_runMatching arrivals
  have hleft : (∑ u : L, djkDualLeft y ord arrivals u) =
      ∑ e ∈ M, djkWeight K (y e.1).val := by
    have hfilt : Finset.univ.filter (· ∈ (rankingGridDet y ord).matchedLeft arrivals) =
        A.matchedLeft arrivals := by
      ext u
      simp [A]
    simp only [djkDualLeft, ← Finset.sum_filter]
    rw [hfilt, ← A.image_fst_runMatching arrivals, Finset.sum_image]
    intro ⟨u₁, j₁⟩ h₁ ⟨u₂, j₂⟩ h₂ (hu : u₁ = u₂)
    exact Prod.ext hu (hM.2.1 u₁ j₁ j₂ h₁ (hu ▸ h₂))
  have hright : (∑ j : Fin arrivals.length, djkDualRight y ord arrivals j) =
      ∑ e ∈ M, (1 - djkWeight K (y e.1).val) := by
    rw [← Finset.sum_subset (Finset.subset_univ (M.image Prod.snd)), Finset.sum_image]
    · refine Finset.sum_congr rfl fun ⟨a, j⟩ haj => ?_
      have hc : ((rankingGridDet y ord).runChoices arrivals)[j.val]'(by simp [j.isLt]) = some a :=
        (A.mem_runMatching_iff arrivals a j).mp haj
      simp [djkDualRight, hc]
    · intro ⟨u₁, j₁⟩ h₁ ⟨u₂, j₂⟩ h₂ (hv : j₁ = j₂)
      exact Prod.ext (hM.2.2 u₁ u₂ j₁ h₁ (hv ▸ h₂)) hv
    · intro j _ hnot
      unfold djkDualRight
      cases hc : ((rankingGridDet y ord).runChoices arrivals)[j.val]'(by simp [j.isLt]) with
      | none => rfl
      | some a =>
        exact absurd
          (Finset.mem_image.mpr ⟨(a, j), (A.mem_runMatching_iff arrivals a j).mpr hc, rfl⟩) hnot
  rw [hleft, hright, ← Finset.sum_add_distrib]
  simp

private theorem rankingGridDet_deleteOffline_update {K : ℕ} (y : L → Fin K)
    (ord : L ≃ Fin (Fintype.card L)) (u : L) (k : Fin K) (arrivals : List (Finset L)) :
    (rankingGridDet (Function.update y u k) ord).runChoices (deleteOffline u arrivals) =
      (rankingGridDet y ord).runChoices (deleteOffline u arrivals) := by
  refine rankingByKey_congr_order _ _ (deleteOffline u arrivals) ?_
  intro N hN a ha b hb
  obtain ⟨N₀, _, rfl⟩ := List.mem_map.mp hN
  have hau : a ≠ u := (Finset.mem_erase.mp ha).1
  have hbu : b ≠ u := (Finset.mem_erase.mp hb).1
  simp [gridKey, Function.update_of_ne hau, Function.update_of_ne hbu]

/-- **Expected dual feasibility on every edge** [DevanurJainKleinberg2013]: for any edge `(u, j)`
(`u ∈ arrivals[j]`) and any ranks `y` on the other vertices, summing `α + β` over all `K`
choices of `y u` is at least `K * (1 - (K / (K + 1)) ^ K)`. -/
theorem sum_djkDual_update_ge {K : ℕ} (y : L → Fin K) (ord : L ≃ Fin (Fintype.card L))
    (arrivals : List (Finset L)) (u : L) (j : Fin arrivals.length) (huj : u ∈ arrivals[j.val]) :
    (K : ℝ) * (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) ≤
      ∑ k : Fin K,
        (djkDualLeft (Function.update y u k) ord arrivals u +
          djkDualRight (Function.update y u k) ord arrivals j) := by
  have hdom : ∀ k : Fin K,
      u ∉ (rankingGridDet (Function.update y u k) ord).matchedLeft arrivals →
      ∃ w', ((rankingGridDet y ord).runChoices (deleteOffline u arrivals))[j.val]'(by
          simp [j.isLt]) = some w' ∧
        gridKey (Function.update y u k) ord w' < gridKey (Function.update y u k) ord u := by
    intro k hnot
    obtain ⟨_, w', hw', hlt⟩ :=
      rankingByKey_dominance (gridKey_injective (Function.update y u k) ord) u arrivals j huj hnot
    change ((rankingGridDet (Function.update y u k) ord).runChoices
      (deleteOffline u arrivals))[j.val]'(by simp [j.isLt]) = some w' at hw'
    have hupd := rankingGridDet_deleteOffline_update y ord u k arrivals
    simp only [hupd] at hw'
    exact ⟨w', hw', hlt⟩
  cases hw :
      ((rankingGridDet y ord).runChoices (deleteOffline u arrivals))[j.val]'(by simp [j.isLt]) with
  | none =>
    have hα : ∀ k : Fin K,
        djkDualLeft (Function.update y u k) ord arrivals u = djkWeight K k.val := by
      intro k
      have hu_matched : u ∈ (rankingGridDet (Function.update y u k) ord).matchedLeft arrivals := by
        by_contra hnot
        obtain ⟨w', hw', _⟩ := hdom k hnot
        simp [hw] at hw'
      simp [djkDualLeft, hu_matched]
    calc (K : ℝ) * (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K)
        = ∑ k ∈ Finset.range K, djkWeight K k := by
          have := djkWeight_balance (K := K) (t := K) le_rfl
          simp only [djkWeight, Nat.sub_self, pow_zero, sub_self, mul_zero, add_zero] at this
          exact this.symm
      _ = ∑ k : Fin K, djkWeight K k.val := (Fin.sum_univ_eq_sum_range (djkWeight K) K).symm
      _ ≤ ∑ k : Fin K,
            (djkDualLeft (Function.update y u k) ord arrivals u +
              djkDualRight (Function.update y u k) ord arrivals j) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [hα k]
          linarith [djkDualRight_nonneg (Function.update y u k) ord arrivals j]
  | some w =>
    have hwu : w ≠ u := by
      have hmem : (w, ⟨j.val, by simp [j.isLt]⟩) ∈
          (rankingGridDet y ord).runMatching (deleteOffline u arrivals) :=
        ((rankingGridDet y ord).mem_runMatching_iff (deleteOffline u arrivals) w _).mpr hw
      have hedge := ((rankingGridDet y ord).isMatching_runMatching (deleteOffline u arrivals)).1
        _ hmem
      simp only [graphOfArrivals, deleteOffline, List.getElem_map, decide_eq_true_eq] at hedge
      exact (Finset.mem_erase.mp hedge).1
    set t := (y w).val
    have htK : t < K := (y w).isLt
    have hα_lt : ∀ k : Fin K, k.val < t →
        djkDualLeft (Function.update y u k) ord arrivals u = djkWeight K k.val := by
      intro k hk
      have hu_matched : u ∈ (rankingGridDet (Function.update y u k) ord).matchedLeft arrivals := by
        by_contra hnot
        obtain ⟨w', hw', hlt⟩ := hdom k hnot
        have hww' : w' = w := Option.some.inj (hw'.symm.trans hw)
        subst hww'
        have hle := val_le_of_gridKey_le hlt.le
        simp only [Function.update_of_ne hwu, Function.update_self] at hle
        omega
      simp [djkDualLeft, hu_matched]
    have hβ : ∀ k : Fin K,
        1 - djkWeight K t ≤ djkDualRight (Function.update y u k) ord arrivals j := by
      intro k
      have hw_k :
          ((rankingGridDet (Function.update y u k) ord).runChoices
            (deleteOffline u arrivals))[j.val]'(by simp [j.isLt]) = some w := by
        have hupd := rankingGridDet_deleteOffline_update y ord u k arrivals
        simp only [hupd, hw]
      obtain ⟨a, ha, hkey_le⟩ :=
        rankingByKey_monotone_choice (gridKey_injective (Function.update y u k) ord) u arrivals j
          hw_k
      change ((rankingGridDet (Function.update y u k) ord).runChoices
        arrivals)[j.val]'(by simp [j.isLt]) = some a at ha
      have hya : (Function.update y u k a).val ≤ t := by
        have hle := val_le_of_gridKey_le hkey_le
        simpa only [Function.update_of_ne hwu] using hle
      have hgw : djkWeight K (Function.update y u k a).val ≤ djkWeight K t :=
        djkWeight_mono hya
      have hr : djkDualRight (Function.update y u k) ord arrivals j =
          1 - djkWeight K (Function.update y u k a).val := by
        simp [djkDualRight, ha]
      linarith
    have hsum_α : ∑ k ∈ Finset.range t, djkWeight K k ≤
        ∑ k : Fin K, djkDualLeft (Function.update y u k) ord arrivals u := by
      have hsub : (Finset.univ.filter fun k : Fin K => k.val < t) ⊆ Finset.univ :=
        Finset.subset_univ _
      calc ∑ k ∈ Finset.range t, djkWeight K k
          = ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < t), djkWeight K k.val := by
            refine Finset.sum_bij (fun k hk => ⟨k, by have := Finset.mem_range.mp hk; omega⟩)
              (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩)
              (fun _ _ _ _ h => congrArg Fin.val h)
              (fun k hk => ⟨k.val, Finset.mem_range.mpr (Finset.mem_filter.mp hk).2, Fin.ext rfl⟩)
              (fun _ _ => rfl)
        _ = ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < t),
              djkDualLeft (Function.update y u k) ord arrivals u :=
            Finset.sum_congr rfl fun k hk => (hα_lt k (Finset.mem_filter.mp hk).2).symm
        _ ≤ ∑ k : Fin K, djkDualLeft (Function.update y u k) ord arrivals u :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
              djkDualLeft_nonneg _ ord arrivals u
    have hsum_β : (K : ℝ) * (1 - djkWeight K t) ≤
        ∑ k : Fin K, djkDualRight (Function.update y u k) ord arrivals j := by
      calc (K : ℝ) * (1 - djkWeight K t)
          = ∑ _k : Fin K, (1 - djkWeight K t) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ∑ k : Fin K, djkDualRight (Function.update y u k) ord arrivals j :=
            Finset.sum_le_sum fun k _ => hβ k
    rw [Finset.sum_add_distrib]
    linarith [djkWeight_balance (K := K) (t := t) htK.le]

/-- **Discrete `RANKING` competitive ratio:** with uniform i.i.d. ranks in `Fin K`,
`rankingGridAlg L K` achieves expected matching size at least `(1 - (K / (K + 1)) ^ K) * |M|` for
every matching `M`. -/
theorem rankingGrid_competitive_ratio (K : ℕ) (hK : 0 < K)
    (ord : L ≃ Fin (Fintype.card L)) (arrivals : List (Finset L))
    {M : Finset (L × Fin arrivals.length)} (hM : IsMatching (graphOfArrivals arrivals) M) :
    (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (M.card : ℝ) ≤
      RandAlg.expectedMatchingSize (rankingGridAlg L K hK ord) arrivals := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  have hcard_pos : (0 : ℝ) < (Fintype.card (L → Fin K) : ℝ) := by positivity
  rw [rankingGridAlg, RandAlg.expectedMatchingSize_map_uniformOfFintype,
    le_div_iff₀ hcard_pos]
  have hdual_le : ∀ y : L → Fin K,
      ∑ e ∈ M, (djkDualLeft y ord arrivals e.1 + djkDualRight y ord arrivals e.2) ≤
        (((rankingGridDet y ord).runMatching arrivals).card : ℝ) := by
    intro y
    rw [← sum_djkDual_eq_card y ord arrivals, Finset.sum_add_distrib]
    have hL : ∑ e ∈ M, djkDualLeft y ord arrivals e.1 ≤ ∑ u : L, djkDualLeft y ord arrivals u := by
      have hinj : Set.InjOn Prod.fst (M : Set (L × Fin arrivals.length)) := by
        intro ⟨u₁, j₁⟩ h₁ ⟨u₂, j₂⟩ h₂ (hu : u₁ = u₂)
        subst hu
        exact Prod.ext rfl (hM.2.1 u₁ j₁ j₂ h₁ h₂)
      rw [← Finset.sum_image hinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun u _ _ => djkDualLeft_nonneg y ord arrivals u
    have hR : ∑ e ∈ M, djkDualRight y ord arrivals e.2 ≤
        ∑ j : Fin arrivals.length, djkDualRight y ord arrivals j := by
      have hinj : Set.InjOn Prod.snd (M : Set (L × Fin arrivals.length)) := by
        intro ⟨u₁, j₁⟩ h₁ ⟨u₂, j₂⟩ h₂ (hv : j₁ = j₂)
        subst hv
        exact Prod.ext (hM.2.2 u₁ u₂ j₁ h₁ h₂) rfl
      rw [← Finset.sum_image hinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun j _ _ => djkDualRight_nonneg y ord arrivals j
    linarith
  have hedge_sum : ∀ e ∈ M,
      (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (Fintype.card (L → Fin K) : ℝ) ≤
        ∑ y : L → Fin K, (djkDualLeft y ord arrivals e.1 + djkDualRight y ord arrivals e.2) := by
    intro ⟨u, j⟩ huj
    have huN : u ∈ arrivals[j.val] := by
      simpa [graphOfArrivals] using hM.1 (u, j) huj
    have hKsum :
        (K : ℝ) * ((1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (Fintype.card (L → Fin K) : ℝ)) ≤
          (K : ℝ) * ∑ y : L → Fin K,
            (djkDualLeft y ord arrivals u + djkDualRight y ord arrivals j) := by
      calc (K : ℝ) * ((1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (Fintype.card (L → Fin K) : ℝ))
          = ∑ _y : L → Fin K, (K : ℝ) * (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) := by
            simp [mul_left_comm, mul_comm]
        _ ≤ ∑ y : L → Fin K, ∑ k : Fin K,
              (djkDualLeft (Function.update y u k) ord arrivals u +
                djkDualRight (Function.update y u k) ord arrivals j) :=
            Finset.sum_le_sum fun y _ => sum_djkDual_update_ge y ord arrivals u j huN
        _ = ∑ k : Fin K, ∑ y : L → Fin K,
              (djkDualLeft (Function.update y u k) ord arrivals u +
                djkDualRight (Function.update y u k) ord arrivals j) := Finset.sum_comm
        _ = (K : ℝ) * ∑ y : L → Fin K,
              (djkDualLeft y ord arrivals u + djkDualRight y ord arrivals j) := by
            rw [Cslib.Probability.sum_sum_update_eq_card_nsmul_sum u
              (fun (_ : Fin K) (y : L → Fin K) =>
                djkDualLeft y ord arrivals u + djkDualRight y ord arrivals j),
              Fintype.card_fin, nsmul_eq_mul]
    exact le_of_mul_le_mul_left hKsum hKpos
  calc (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (M.card : ℝ) * (Fintype.card (L → Fin K) : ℝ)
      = ∑ _e ∈ M, (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (Fintype.card (L → Fin K) : ℝ) := by
        simp [mul_left_comm, mul_comm]
    _ ≤ ∑ e ∈ M, ∑ y : L → Fin K,
          (djkDualLeft y ord arrivals e.1 + djkDualRight y ord arrivals e.2) :=
        Finset.sum_le_sum hedge_sum
    _ = ∑ y : L → Fin K, ∑ e ∈ M,
          (djkDualLeft y ord arrivals e.1 + djkDualRight y ord arrivals e.2) :=
        Finset.sum_comm
    _ ≤ ∑ y : L → Fin K, (((rankingGridDet y ord).runMatching arrivals).card : ℝ) :=
        Finset.sum_le_sum fun y _ => hdual_le y

/-! ### Exact `1 - 1/e` competitive ratio of `RANKING` -/

private theorem sum_injective_grid_eq (K : ℕ) (ord : L ≃ Fin (Fintype.card L))
    (arrivals : List (Finset L)) :
    (∑ y ∈ Finset.univ.filter (fun y : L → Fin K => Function.Injective y),
      (((rankingGridDet y ord).runMatching arrivals).card : ℝ)) =
      ((K.choose (Fintype.card L) : ℕ) : ℝ) *
        ∑ π : L ≃ Fin (Fintype.card L), (((rankingDet π).runMatching arrivals).card : ℝ) := by
  classical
  let Sset := (Finset.univ : Finset (Fin K)).powersetCard (Fintype.card L)
  have hbij :
      ∑ y ∈ Finset.univ.filter (fun y : L → Fin K => Function.Injective y),
        (((rankingGridDet y ord).runMatching arrivals).card : ℝ) =
      ∑ p ∈ Sset ×ˢ (Finset.univ : Finset (L ≃ Fin (Fintype.card L))),
        (((rankingDet p.2).runMatching arrivals).card : ℝ) := by
    symm
    refine Finset.sum_bij
      (fun (p : Finset (Fin K) × (L ≃ Fin (Fintype.card L))) (hp : p ∈ Sset ×ˢ Finset.univ) =>
        fun u : L =>
          p.1.orderEmbOfFin (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2 (p.2 u))
      ?_ ?_ ?_ ?_
    · intro p hp
      have hcard : p.1.card = Fintype.card L :=
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact (p.1.orderEmbOfFin hcard).injective.comp p.2.injective
    · intro p₁ hp₁ p₂ hp₂ heq
      have hc₁ : p₁.1.card = Fintype.card L :=
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp₁).1).2
      have hc₂ : p₂.1.card = Fintype.card L :=
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp₂).1).2
      have hS : p₁.1 = p₂.1 := Finset.coe_injective <| by
        rw [← Finset.range_orderEmbOfFin p₁.1 hc₁, ← Finset.range_orderEmbOfFin p₂.1 hc₂]
        ext x
        exact ⟨fun ⟨r, hr⟩ =>
            ⟨p₂.2 (p₁.2.symm r), by simpa [← hr] using (congrFun heq (p₁.2.symm r)).symm⟩,
          fun ⟨r, hr⟩ =>
            ⟨p₁.2 (p₂.2.symm r), by simpa [← hr] using congrFun heq (p₂.2.symm r)⟩⟩
      rcases p₁ with ⟨S₁, π₁⟩
      rcases p₂ with ⟨S₂, π₂⟩
      subst hS
      exact Prod.ext rfl (Equiv.ext fun u =>
        (S₁.orderEmbOfFin hc₁).injective (congrFun heq u))
    · intro y hy
      have hyinj : Function.Injective y := (Finset.mem_filter.mp hy).2
      let S : Finset (Fin K) := Finset.univ.image y
      have hScard : S.card = Fintype.card L := by
        rw [Finset.card_image_of_injective _ hyinj, Finset.card_univ]
      let eS : Fin (Fintype.card L) ≃ S := (S.orderIsoOfFin hScard).toEquiv
      let eY : L ≃ S :=
        Equiv.ofBijective (fun u => ⟨y u, Finset.mem_image_of_mem y (Finset.mem_univ u)⟩)
          ⟨fun u₁ u₂ h => hyinj (congrArg Subtype.val h),
            fun ⟨x, hx⟩ => by
              obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
              exact ⟨u, rfl⟩⟩
      refine ⟨(S, eY.trans eS.symm), Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, hScard⟩, Finset.mem_univ _⟩, ?_⟩
      funext u
      exact congrArg Subtype.val (eS.apply_symm_apply (eY u))
    · intro p hp
      have hc : p.1.card = Fintype.card L :=
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
      set y : L → Fin K := fun u => p.1.orderEmbOfFin hc (p.2 u)
      have hyinj : Function.Injective y := (p.1.orderEmbOfFin hc).injective.comp p.2.injective
      have hchoices : (rankingDet p.2).runChoices arrivals =
          (rankingGridDet y ord).runChoices arrivals := by
        refine rankingByKey_congr_order _ _ arrivals fun _ _ a _ b _ => ?_
        have hlt : ∀ u v : L, p.2 u < p.2 v ↔ y u < y v := fun u v =>
          ((p.1.orderEmbOfFin hc).lt_iff_lt (a := p.2 u) (b := p.2 v)).symm
        constructor
        · intro hab
          by_cases heq : a = b
          · subst heq; exact le_rfl
          · have h1 : p.2 a < p.2 b :=
              lt_of_le_of_ne (Fin.le_def.mpr hab) (fun h => heq (p.2.injective h))
            have h2 : (y a).val < (y b).val := Fin.lt_def.mp ((hlt a b).mp h1)
            simp only [gridKey]
            have ha_lt : (ord a).val < Fintype.card L := (ord a).isLt
            have hmul : Fintype.card L * (y a).val + Fintype.card L ≤
                Fintype.card L * (y b).val := by
              rw [← Nat.mul_succ]
              exact Nat.mul_le_mul_left _ h2
            omega
        · intro hab
          have hy_le : (y a).val ≤ (y b).val := val_le_of_gridKey_le hab
          by_cases heq : a = b
          · subst heq; exact le_rfl
          · have h2 : y a < y b :=
              lt_of_le_of_ne (Fin.le_def.mpr hy_le) (fun h => heq (hyinj h))
            exact (Fin.lt_def.mp ((hlt a b).mpr h2)).le
      rw [DetAlg.card_runMatching_eq_countP, DetAlg.card_runMatching_eq_countP, hchoices]
  rw [hbij, Finset.sum_product]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private theorem card_injective_grid (K : ℕ) :
    (Finset.univ.filter (fun y : L → Fin K => Function.Injective y)).card =
      K.descFactorial (Fintype.card L) := by
  classical
  let hequiv : {y : L → Fin K // Function.Injective y} ≃ (L ↪ Fin K) :=
    ⟨fun y => ⟨y.val, y.property⟩, fun f => ⟨f, f.injective⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Fintype.card_subtype, Fintype.card_congr hequiv, Fintype.card_embedding_eq,
    Fintype.card_fin]

private theorem tendsto_one_sub_div_pow_inv_exp :
    Tendsto (fun K : ℕ => 1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) atTop
      (𝓝 (1 - Real.exp (-1))) := by
  refine tendsto_const_nhds.sub ?_
  rw [Real.exp_neg]
  refine ((Real.tendsto_one_add_div_pow_exp 1).inv₀ (Real.exp_ne_zero 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hK1 : (K : ℝ) + 1 ≠ 0 := by positivity
  rw [← inv_pow]
  congr 1
  field_simp [hK0, hK1]

private theorem tendsto_descFactorial_div_pow (n : ℕ) :
    Tendsto (fun K : ℕ => (K.descFactorial n : ℝ) / ((K : ℝ) ^ n)) atTop (𝓝 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hfac : Tendsto (fun K : ℕ => 1 - (n : ℝ) / (K : ℝ)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
    have hmul := hfac.mul ih
    simp only [one_mul] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop (n + 1)] with K hK
    have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub (by omega), pow_succ']
    field_simp [hK0]

/-- **Karp–Vazirani–Vazirani (1990) / Devanur–Jain–Kleinberg (2013) exact `1 - 1/e` theorem:**
for every finite offline vertex set `L`, every arrival sequence `arrivals`, and every matching
`M` of `graphOfArrivals arrivals`, `rankingAlg L` achieves expected matching size at least
`(1 - e⁻¹) * |M|`. -/
theorem ranking_competitive_ratio (arrivals : List (Finset L))
    {M : Finset (L × Fin arrivals.length)} (hM : IsMatching (graphOfArrivals arrivals) M) :
    (1 - Real.exp (-1)) * (M.card : ℝ) ≤
      RandAlg.expectedMatchingSize (rankingAlg L) arrivals := by
  classical
  let n := Fintype.card L
  let ord : L ≃ Fin n := Fintype.equivFin L
  let E_rank := RandAlg.expectedMatchingSize (rankingAlg L) arrivals
  have hbound : ∀ K : ℕ, 1 ≤ K →
      (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (M.card : ℝ) ≤
        ((K.descFactorial n : ℝ) / ((K : ℝ) ^ n)) * E_rank +
          (1 - (K.descFactorial n : ℝ) / ((K : ℝ) ^ n)) * (arrivals.length : ℝ) := by
    intro K hK
    have hKpos : 0 < K := by omega
    have : Nonempty (Fin K) := ⟨⟨0, hKpos⟩⟩
    have hKn_pos : (0 : ℝ) < (K : ℝ) ^ n := by positivity
    have hgrid := rankingGrid_competitive_ratio (L := L) K hKpos ord arrivals hM
    rw [rankingGridAlg, RandAlg.expectedMatchingSize_map_uniformOfFintype,
      Fintype.card_fun, Fintype.card_fin] at hgrid
    have hgrid' : (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (M.card : ℝ) ≤
        (∑ y : L → Fin K, (((rankingGridDet y ord).runMatching arrivals).card : ℝ)) /
          ((K : ℝ) ^ n) := by
      simpa [Nat.cast_pow, n] using hgrid
    refine hgrid'.trans ?_
    set Inj := Finset.univ.filter (fun y : L → Fin K => Function.Injective y)
    set Coll := Finset.univ.filter (fun y : L → Fin K => ¬Function.Injective y)
    have hsplit :
        (∑ y : L → Fin K, (((rankingGridDet y ord).runMatching arrivals).card : ℝ)) =
        (∑ y ∈ Inj, (((rankingGridDet y ord).runMatching arrivals).card : ℝ)) +
        (∑ y ∈ Coll, (((rankingGridDet y ord).runMatching arrivals).card : ℝ)) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun y : L → Fin K => Function.Injective y)]
    have hInj_val :
        (∑ y ∈ Inj, (((rankingGridDet y ord).runMatching arrivals).card : ℝ)) =
          (K.descFactorial n : ℝ) * E_rank := by
      dsimp only [E_rank]
      rw [sum_injective_grid_eq K ord arrivals, expectedMatchingSize_rankingAlg]
      have hcard_perm : (Fintype.card (L ≃ Fin (Fintype.card L)) : ℝ) = (n.factorial : ℝ) := by
        exact_mod_cast Fintype.card_equiv ord
      have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
      have hdesc : (K.descFactorial n : ℝ) = (n.factorial : ℝ) * (K.choose n : ℝ) := by
        exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose K n
      set S_perm : ℝ :=
        ∑ π : L ≃ Fin (Fintype.card L), (((rankingDet π).runMatching arrivals).card : ℝ)
      rw [hcard_perm, hdesc]
      change ((K.choose n : ℕ) : ℝ) * S_perm =
        (n.factorial : ℝ) * ((K.choose n : ℕ) : ℝ) * (S_perm / (n.factorial : ℝ))
      field_simp [hfact_pos.ne']
    have hColl_card : (Coll.card : ℝ) = (K : ℝ) ^ n - (K.descFactorial n : ℝ) := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (L → Fin K))) (p := fun y => Function.Injective y)
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
      change Inj.card + Coll.card = K ^ n at h
      have hInj : Inj.card = K.descFactorial n := card_injective_grid (L := L) K
      have hnat : Coll.card = K ^ n - K.descFactorial n := by omega
      rw [hnat, Nat.cast_sub (Nat.descFactorial_le_pow K n), Nat.cast_pow]
    set S_coll : ℝ := ∑ y ∈ Coll, (((rankingGridDet y ord).runMatching arrivals).card : ℝ)
    have hColl_le :
        S_coll ≤ ((K : ℝ) ^ n - (K.descFactorial n : ℝ)) * (arrivals.length : ℝ) := by
      calc S_coll
          ≤ ∑ _y ∈ Coll, (arrivals.length : ℝ) :=
            Finset.sum_le_sum fun y _ => by
              exact_mod_cast DetAlg.card_runMatching_le_length _ arrivals
        _ = (Coll.card : ℝ) * (arrivals.length : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((K : ℝ) ^ n - (K.descFactorial n : ℝ)) * (arrivals.length : ℝ) := by rw [hColl_card]
    rw [hsplit, hInj_val, add_div]
    have h1 : (K.descFactorial n : ℝ) * E_rank / (K : ℝ) ^ n =
        ((K.descFactorial n : ℝ) / (K : ℝ) ^ n) * E_rank := by ring
    have h2 : S_coll / (K : ℝ) ^ n ≤
        (1 - (K.descFactorial n : ℝ) / (K : ℝ) ^ n) * (arrivals.length : ℝ) := by
      calc S_coll / (K : ℝ) ^ n
          ≤ ((K : ℝ) ^ n - (K.descFactorial n : ℝ)) * (arrivals.length : ℝ) / (K : ℝ) ^ n :=
            div_le_div_of_nonneg_right hColl_le hKn_pos.le
        _ = (1 - (K.descFactorial n : ℝ) / (K : ℝ) ^ n) * (arrivals.length : ℝ) := by
            field_simp [hKn_pos.ne']
    linarith
  have hLHS : Tendsto (fun K : ℕ => (1 - ((K : ℝ) / ((K : ℝ) + 1)) ^ K) * (M.card : ℝ))
      atTop (𝓝 ((1 - Real.exp (-1)) * (M.card : ℝ))) :=
    tendsto_one_sub_div_pow_inv_exp.mul tendsto_const_nhds
  have hRHS : Tendsto
      (fun K : ℕ => ((K.descFactorial n : ℝ) / ((K : ℝ) ^ n)) * E_rank +
        (1 - (K.descFactorial n : ℝ) / ((K : ℝ) ^ n)) * (arrivals.length : ℝ))
      atTop (𝓝 E_rank) := by
    have h1 := (tendsto_descFactorial_div_pow n).mul (tendsto_const_nhds (x := E_rank))
    have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_descFactorial_div_pow n)).mul
      (tendsto_const_nhds (x := (arrivals.length : ℝ)))
    simpa using h1.add h2
  exact le_of_tendsto_of_tendsto hLHS hRHS ((eventually_ge_atTop 1).mono hbound)

end DiscreteDJK

/-! ### Tight `1 - 1/e` Yao minimax upper bound (permuted upper-triangular graph) -/

section YaoUpperBound

/-- Permuted upper-triangular arrival sequence `triArrivals n σ` on `Fin n`: online vertex `j` is
adjacent to `{σ(i) | j ≤ i < n}`, i.e. `{u | j ≤ σ⁻¹(u)}`. -/
@[expose] def triArrivals (n : ℕ) (σ : Equiv.Perm (Fin n)) : List (Finset (Fin n)) :=
  (List.finRange n).map fun j => Finset.univ.filter fun u => j.val ≤ (σ.symm u).val

@[simp] theorem length_triArrivals (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (triArrivals n σ).length = n := by
  simp [triArrivals]

/-- The canonical perfect matching `{(σ(j), j) | j : Fin n}` of `triArrivals n σ`. -/
@[expose] def triPerfectMatching (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin (triArrivals n σ).length) :=
  Finset.univ.image fun j : Fin (triArrivals n σ).length =>
    (σ ⟨j.val, by simpa using j.isLt⟩, j)

theorem isMatching_triPerfectMatching (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsMatching (graphOfArrivals (triArrivals n σ)) (triPerfectMatching n σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    simp [graphOfArrivals, triArrivals]
  · intro u v₁ v₂ h₁ h₂
    obtain ⟨j₁, _, he₁⟩ := Finset.mem_image.mp h₁
    obtain ⟨j₂, _, he₂⟩ := Finset.mem_image.mp h₂
    rcases Prod.mk.inj he₁ with ⟨hu₁, rfl⟩
    rcases Prod.mk.inj he₂ with ⟨hu₂, rfl⟩
    have hσ := σ.injective (hu₁.trans hu₂.symm)
    exact Fin.ext (congrArg (Fin.val : Fin n → ℕ) hσ)
  · intro u₁ u₂ v h₁ h₂
    obtain ⟨j₁, _, he₁⟩ := Finset.mem_image.mp h₁
    obtain ⟨j₂, _, he₂⟩ := Finset.mem_image.mp h₂
    rcases Prod.mk.inj he₁ with ⟨rfl, hv₁⟩
    rcases Prod.mk.inj he₂ with ⟨rfl, hv₂⟩
    have hj : j₁ = j₂ := hv₁.trans hv₂.symm
    subst hj
    rfl

theorem card_triPerfectMatching (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (triPerfectMatching n σ).card = n := by
  rw [triPerfectMatching, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin,
    length_triArrivals]
  intro j₁ j₂ h
  exact (Prod.mk.inj h).2

private def activeSet (n : ℕ) (σ : Equiv.Perm (Fin n)) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => t ≤ (σ.symm u).val

private def availCount {n : ℕ} (A : DetAlg (Fin n)) (σ : Equiv.Perm (Fin n)) (t : ℕ) : ℕ :=
  (activeSet n σ t \ A.matchedLeft ((triArrivals n σ).take t)).card

private def matchedStep {n : ℕ} (A : DetAlg (Fin n)) (σ : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t < n) : ℕ :=
  if ((A.runChoices (triArrivals n σ))[t]'(by simp [ht])).isSome then 1 else 0

private theorem sum_matchedStep_eq_card {n : ℕ} (A : DetAlg (Fin n)) (σ : Equiv.Perm (Fin n)) :
    (∑ t : Fin n, matchedStep A σ t.val t.isLt) = (A.runMatching (triArrivals n σ)).card := by
  rw [DetAlg.card_runMatching_eq_sum]
  refine Finset.sum_bij (fun t _ => ⟨t.val, by simp [t.isLt]⟩) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro t₁ _ t₂ _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro j _; exact ⟨⟨j.val, by simpa using j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro _ _; rfl

private theorem activeSet_succ (n : ℕ) (σ : Equiv.Perm (Fin n)) (t : ℕ) (ht : t < n) :
    activeSet n σ (t + 1) = (activeSet n σ t).erase (σ ⟨t, ht⟩) := by
  ext u
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
    ← σ.symm_apply_eq, Fin.ext_iff]
  omega

private theorem activeSet_swap_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) {t r : ℕ}
    (ht : t < n) {j : Fin n} (hj : t ≤ j.val) (hr : r ≤ t) :
    activeSet n (σ * Equiv.swap ⟨t, ht⟩ j) r = activeSet n σ r := by
  ext u
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsymm : (σ * Equiv.swap ⟨t, ht⟩ j).symm u = Equiv.swap ⟨t, ht⟩ j (σ.symm u) := by
    simp [Equiv.Perm.mul_def]
  rw [hsymm]
  by_cases hx₁ : σ.symm u = ⟨t, ht⟩
  · simp only [hx₁, Equiv.swap_apply_left]; omega
  · by_cases hx₂ : σ.symm u = j
    · simp only [hx₂, Equiv.swap_apply_right]; omega
    · rw [Equiv.swap_apply_of_ne_of_ne hx₁ hx₂]

private theorem take_triArrivals_swap_eq (n : ℕ) (σ : Equiv.Perm (Fin n)) {t : ℕ}
    (ht : t < n) {j : Fin n} (hj : t ≤ j.val) :
    (triArrivals n (σ * Equiv.swap ⟨t, ht⟩ j)).take (t + 1) =
      (triArrivals n σ).take (t + 1) := by
  refine List.ext_getElem ?_ ?_
  · simp
  · intro r hr₁ hr₂
    have hrt : r ≤ t := by
      simp only [List.length_take, length_triArrivals] at hr₁
      omega
    simp only [List.getElem_take, triArrivals, List.getElem_map, List.getElem_finRange]
    exact activeSet_swap_eq n σ ht hj hrt

private theorem triArrivals_step_split {n : ℕ} (A : DetAlg (Fin n)) (σ : Equiv.Perm (Fin n))
    (t : ℕ) (ht : t < n) :
    matchedStep A σ t ht ≤ availCount A σ t ∧
    (activeSet n σ t \ A.matchedLeft ((triArrivals n σ).take (t + 1))).card =
      availCount A σ t - matchedStep A σ t ht := by
  set arr := triArrivals n σ
  have hlen : arr.length = n := length_triArrivals n σ
  have hget_arr : arr[t]'(by omega) = activeSet n σ t := by
    ext u
    simp only [arr, triArrivals, activeSet, List.getElem_map, List.getElem_finRange,
      Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_cast]
  have htake : arr.take (t + 1) = arr.take t ++ [activeSet n σ t] := by
    rw [List.take_succ_eq_append_getElem (by omega), hget_arr]
  set pre := A.matchedLeft (arr.take t)
  set c := onlineStep pre (activeSet n σ t) (A.choose (arr.take t) pre (activeSet n σ t))
  have hc_eq : (A.runChoices arr)[t]'(by simp [arr, ht]) = c := by
    rw [A.runChoices_getElem arr (by omega)]
    simp only [pre, c, hget_arr]
  have hmatched_succ : A.matchedLeft (arr.take (t + 1)) = updateMatched pre c := by
    rw [htake, A.matchedLeft_append]
    rfl
  cases hc : c with
  | none =>
    simp [matchedStep, availCount, arr, pre, hmatched_succ, hc_eq, hc, updateMatched]
  | some u =>
    have ⟨_, huN, hupre⟩ := onlineStep_eq_some_iff.mp hc
    have hu_mem : u ∈ activeSet n σ t \ pre := Finset.mem_sdiff.mpr ⟨huN, hupre⟩
    have hsdiff : activeSet n σ t \ insert u pre = (activeSet n σ t \ pre).erase u :=
      Finset.ext fun _ => by
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
    simp only [matchedStep, arr, hc_eq, hc, Option.isSome_some, ↓reduceIte, hmatched_succ,
      updateMatched, hsdiff, Finset.card_erase_of_mem hu_mem]
    exact ⟨Finset.card_pos.mpr ⟨u, hu_mem⟩, rfl⟩

/-- Exact telescoping recurrence for the expected number of remaining unmatched active offline
vertices on `triArrivals n σ`. -/
private theorem sum_availCount_succ {n : ℕ} (A : DetAlg (Fin n)) (t : ℕ) (ht : t < n) :
    (n - t) * (∑ σ : Equiv.Perm (Fin n), availCount A σ (t + 1)) =
      (n - t - 1) *
        ((∑ σ : Equiv.Perm (Fin n), availCount A σ t) -
          ∑ σ : Equiv.Perm (Fin n), matchedStep A σ t ht) := by
  let J : Finset (Fin n) := Finset.univ.filter fun j : Fin n => t ≤ j.val
  have hJcard : J.card = n - t := by
    have hbij : J.card = (Finset.Ico t n).card := by
      refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hj).2, j.isLt⟩
      · intro j₁ _ j₂ _ h
        exact Fin.ext h
      · intro m hm
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hm
        exact ⟨⟨m, h2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, rfl⟩
    rw [hbij, Nat.card_Ico]
  have hdouble :
      (n - t) * (∑ σ : Equiv.Perm (Fin n), availCount A σ (t + 1)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ j ∈ J, availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1) := by
    rw [Finset.sum_comm]
    calc (n - t) * (∑ σ : Equiv.Perm (Fin n), availCount A σ (t + 1))
        = ∑ _j ∈ J, ∑ σ : Equiv.Perm (Fin n), availCount A σ (t + 1) := by
          rw [Finset.sum_const, hJcard, smul_eq_mul]
      _ = ∑ j ∈ J, ∑ σ : Equiv.Perm (Fin n), availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          symm
          exact Equiv.sum_comp (Equiv.mulRight (Equiv.swap ⟨t, ht⟩ j))
            fun σ => availCount A σ (t + 1)
  have hinner : ∀ σ : Equiv.Perm (Fin n),
      ∑ j ∈ J, availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1) =
        (n - t - 1) * (availCount A σ t - matchedStep A σ t ht) := by
    intro σ
    set B := activeSet n σ t \ A.matchedLeft ((triArrivals n σ).take (t + 1))
    have hBcard : B.card = availCount A σ t - matchedStep A σ t ht :=
      (triArrivals_step_split A σ t ht).2
    have hterm : ∀ j ∈ J,
        availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1) =
          B.card - (if σ j ∈ B then 1 else 0) := by
      intro j hj
      have hj_ge : t ≤ j.val := (Finset.mem_filter.mp hj).2
      have hact : activeSet n (σ * Equiv.swap ⟨t, ht⟩ j) t = activeSet n σ t :=
        activeSet_swap_eq n σ ht hj_ge le_rfl
      have htake : (triArrivals n (σ * Equiv.swap ⟨t, ht⟩ j)).take (t + 1) =
          (triArrivals n σ).take (t + 1) :=
        take_triArrivals_swap_eq n σ ht hj_ge
      have hact_succ :
          activeSet n (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1) =
            (activeSet n σ t).erase (σ j) := by
        rw [activeSet_succ n (σ * Equiv.swap ⟨t, ht⟩ j) t ht, hact]
        simp [Equiv.Perm.mul_apply]
      have hsdiff :
          (activeSet n σ t).erase (σ j) \ A.matchedLeft ((triArrivals n σ).take (t + 1)) =
            B.erase (σ j) := by
        ext x
        simp only [B, Finset.mem_sdiff, Finset.mem_erase]
        tauto
      unfold availCount
      rw [hact_succ, htake, hsdiff]
      by_cases hmem : σ j ∈ B
      · simp [hmem, Finset.card_erase_of_mem hmem]
      · simp [hmem]
    have hsum_ind : (∑ j ∈ J, if σ j ∈ B then 1 else 0) = B.card := by
      rw [Finset.sum_boole, Nat.cast_id]
      refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
      · intro j hj
        exact (Finset.mem_filter.mp hj).2
      · intro j₁ _ j₂ _ h
        exact σ.injective h
      · intro u hu
        have hu_act : u ∈ activeSet n σ t := (Finset.mem_sdiff.mp hu).1
        have hu_ge : t ≤ (σ.symm u).val := (Finset.mem_filter.mp hu_act).2
        refine ⟨σ.symm u, Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu_ge⟩, by simpa using hu⟩, by simp⟩
    have hsum_split :
        (∑ j ∈ J, availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1)) +
          (∑ j ∈ J, if σ j ∈ B then 1 else 0) = (n - t) * B.card := by
      calc (∑ j ∈ J, availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1)) +
            (∑ j ∈ J, if σ j ∈ B then 1 else 0)
          = ∑ j ∈ J, (availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1) +
              if σ j ∈ B then 1 else 0) := (Finset.sum_add_distrib).symm
        _ = ∑ _j ∈ J, B.card := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [hterm j hj]
            split_ifs with hmem
            · have : 1 ≤ B.card := Finset.card_pos.mpr ⟨σ j, hmem⟩
              omega
            · omega
        _ = (n - t) * B.card := by rw [Finset.sum_const, hJcard, smul_eq_mul]
    rw [hsum_ind] at hsum_split
    have hsub : (n - t - 1) * B.card + B.card = (n - t) * B.card := by
      have hnt : n - t = (n - t - 1) + 1 := by omega
      conv_rhs => rw [hnt]
      ring
    rw [← hBcard]
    omega
  rw [hdouble]
  calc ∑ σ : Equiv.Perm (Fin n), ∑ j ∈ J, availCount A (σ * Equiv.swap ⟨t, ht⟩ j) (t + 1)
      = ∑ σ : Equiv.Perm (Fin n), (n - t - 1) * (availCount A σ t - matchedStep A σ t ht) :=
        Finset.sum_congr rfl fun σ _ => hinner σ
    _ = (n - t - 1) * ∑ σ : Equiv.Perm (Fin n), (availCount A σ t - matchedStep A σ t ht) := by
        rw [Finset.mul_sum]
    _ = (n - t - 1) * ((∑ σ : Equiv.Perm (Fin n), availCount A σ t) -
          ∑ σ : Equiv.Perm (Fin n), matchedStep A σ t ht) := by
        congr 1
        have hle : ∀ σ : Equiv.Perm (Fin n), matchedStep A σ t ht ≤ availCount A σ t :=
          fun σ => (triArrivals_step_split A σ t ht).1
        have hadd : (∑ σ : Equiv.Perm (Fin n), (availCount A σ t - matchedStep A σ t ht)) +
            (∑ σ : Equiv.Perm (Fin n), matchedStep A σ t ht) =
            ∑ σ : Equiv.Perm (Fin n), availCount A σ t := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun σ _ => Nat.sub_add_cancel (hle σ)
        omega

private theorem sum_matchedStep_div_le_one {n : ℕ} (hn : 1 ≤ n) (A : DetAlg (Fin n)) :
    let P : ℕ := Fintype.card (Equiv.Perm (Fin n))
    ∑ t : Fin n,
      ((∑ σ : Equiv.Perm (Fin n), (matchedStep A σ t.val t.isLt : ℝ)) / (P : ℝ)) /
        ((n - t.val : ℕ) : ℝ) ≤ 1 := by
  intro P
  have hPpos : (0 : ℝ) < (P : ℝ) := by positivity
  let U : ℕ → ℝ := fun t => (∑ σ : Equiv.Perm (Fin n), (availCount A σ t : ℝ)) / (P : ℝ)
  let p : (t : ℕ) → t < n → ℝ := fun t ht =>
    (∑ σ : Equiv.Perm (Fin n), (matchedStep A σ t ht : ℝ)) / (P : ℝ)
  have hU0 : U 0 / (n : ℝ) = 1 := by
    have h0 : ∀ σ : Equiv.Perm (Fin n), availCount A σ 0 = n := fun σ => by
      simp [availCount, activeSet]
    have hsum : (∑ σ : Equiv.Perm (Fin n), (availCount A σ 0 : ℝ)) = (P : ℝ) * (n : ℝ) := by
      simp [h0, P]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    simp only [U, hsum]
    field_simp [hPpos.ne', hn0]
  have hstep : ∀ (t : ℕ) (ht : t + 1 < n),
      U t / ((n - t : ℕ) : ℝ) - U (t + 1) / ((n - (t + 1) : ℕ) : ℝ) =
        p t (by omega) / ((n - t : ℕ) : ℝ) := by
    intro t ht
    have hnat := sum_availCount_succ A t (by omega)
    have hle_sum : ∑ σ : Equiv.Perm (Fin n), matchedStep A σ t (by omega) ≤
        ∑ σ : Equiv.Perm (Fin n), availCount A σ t :=
      Finset.sum_le_sum fun σ _ => (triArrivals_step_split A σ t (by omega)).1
    have hreal : ((n - t : ℕ) : ℝ) * (∑ σ : Equiv.Perm (Fin n), (availCount A σ (t + 1) : ℝ)) =
        ((n - (t + 1) : ℕ) : ℝ) *
          ((∑ σ : Equiv.Perm (Fin n), (availCount A σ t : ℝ)) -
            ∑ σ : Equiv.Perm (Fin n), (matchedStep A σ t (by omega) : ℝ)) := by
      have hcast : (((n - t) * ∑ σ : Equiv.Perm (Fin n), availCount A σ (t + 1) : ℕ) : ℝ) =
          (((n - t - 1) * ((∑ σ : Equiv.Perm (Fin n), availCount A σ t) -
            ∑ σ : Equiv.Perm (Fin n), matchedStep A σ t (by omega)) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast [Nat.cast_sub hle_sum] at hcast
      simpa only [Nat.sub_sub] using hcast
    have hd1 : ((n - t : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n - t := by omega
      positivity
    have hd2 : ((n - (t + 1) : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n - (t + 1) := by omega
      positivity
    have hUeq :
        ((n - t : ℕ) : ℝ) * U (t + 1) =
          ((n - (t + 1) : ℕ) : ℝ) * (U t - p t (by omega)) := by
      simp only [U, p]
      rw [← sub_div, mul_div_assoc', mul_div_assoc', hreal]
    field_simp [hd1, hd2]
    linarith
  have htelescope : ∀ k : ℕ, k ≤ n - 1 →
      (∑ t ∈ Finset.range k,
        if ht : t < n then p t ht / ((n - t : ℕ) : ℝ) else 0) =
      U 0 / (n : ℝ) - U k / ((n - k : ℕ) : ℝ) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega), dite_eq_left (by omega), ← hstep k (by omega)]
      ring
  have hlast : p (n - 1) (by omega) ≤ U (n - 1) := by
    simp only [p, U]
    refine div_le_div_of_nonneg_right ?_ hPpos.le
    refine Finset.sum_le_sum fun σ _ => ?_
    exact_mod_cast (triArrivals_step_split A σ (n - 1) (by omega)).1
  have hsplit_fin :
      (∑ t : Fin n, p t.val t.isLt / ((n - t.val : ℕ) : ℝ)) =
        (∑ t ∈ Finset.range (n - 1),
          if ht : t < n then p t ht / ((n - t : ℕ) : ℝ) else 0) +
        p (n - 1) (by omega) / ((n - (n - 1) : ℕ) : ℝ) := by
    have hrange :
        (∑ t : Fin n, p t.val t.isLt / ((n - t.val : ℕ) : ℝ)) =
          ∑ t ∈ Finset.range n, if ht : t < n then p t ht / ((n - t : ℕ) : ℝ) else 0 := by
      refine Finset.sum_bij (fun t _ => t.val) ?_ ?_ ?_ ?_
      · intro t _; exact Finset.mem_range.mpr t.isLt
      · intro t₁ _ t₂ _ h; exact Fin.ext h
      · intro m hm; exact ⟨⟨m, Finset.mem_range.mp hm⟩, Finset.mem_univ _, rfl⟩
      · intro t _; rw [dite_eq_left t.isLt]
    have hset : Finset.range n = insert (n - 1) (Finset.range (n - 1)) := by
      rw [← Finset.range_add_one, show n - 1 + 1 = n by omega]
    rw [hrange, hset, Finset.sum_insert Finset.notMem_range_self, add_comm,
      dite_eq_left (by omega)]
  change ∑ t : Fin n, p t.val t.isLt / ((n - t.val : ℕ) : ℝ) ≤ 1
  rw [hsplit_fin, htelescope (n - 1) le_rfl, hU0, show n - (n - 1) = 1 by omega]
  simp only [Nat.cast_one, div_one]
  linarith

/-- **Harmonic deterministic average upper bound on `triArrivals n σ`** [KarpVaziraniVazirani1990]:
for every `n ≥ 1`, every `s ≤ n`, and every deterministic online algorithm `A : DetAlg (Fin n)`,
the average matching size of `A` over all `n!` permutations `σ` is at most
`n - s * (harmonic n - harmonic s)`. -/
theorem det_triArrivals_avg_le_harmonic {n s : ℕ} (hn : 1 ≤ n) (hs : s ≤ n)
    (A : DetAlg (Fin n)) :
    (∑ σ : Equiv.Perm (Fin n), ((A.runMatching (triArrivals n σ)).card : ℝ)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤
      (n : ℝ) - (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ)) := by
  set P := Fintype.card (Equiv.Perm (Fin n))
  have hPpos : (0 : ℝ) < (P : ℝ) := by positivity
  let p : Fin n → ℝ := fun t =>
    (∑ σ : Equiv.Perm (Fin n), (matchedStep A σ t.val t.isLt : ℝ)) / (P : ℝ)
  have hp_nonneg : ∀ t : Fin n, 0 ≤ p t := fun t =>
    div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hPpos.le
  have hp_le_one : ∀ t : Fin n, p t ≤ 1 := fun t => by
    rw [div_le_one hPpos]
    calc ∑ σ : Equiv.Perm (Fin n), (matchedStep A σ t.val t.isLt : ℝ)
        ≤ ∑ _σ : Equiv.Perm (Fin n), (1 : ℝ) := by
          refine Finset.sum_le_sum fun σ _ => ?_
          unfold matchedStep
          split_ifs <;> norm_num
      _ = (P : ℝ) := by simp [P]
  have hbudget : ∑ t : Fin n, p t / ((n - t.val : ℕ) : ℝ) ≤ 1 :=
    sum_matchedStep_div_le_one hn A
  have havg_eq :
      (∑ σ : Equiv.Perm (Fin n), ((A.runMatching (triArrivals n σ)).card : ℝ)) / (P : ℝ) =
        ∑ t : Fin n, p t := by
    simp only [p, ← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact_mod_cast (sum_matchedStep_eq_card A σ).symm
  have hterm : ∀ t : Fin n,
      p t ≤ (s : ℝ) * (p t / ((n - t.val : ℕ) : ℝ)) +
        if s < n - t.val then 1 - (s : ℝ) / ((n - t.val : ℕ) : ℝ) else 0 := by
    intro t
    have hd_pos : (0 : ℝ) < ((n - t.val : ℕ) : ℝ) := by
      have : 0 < n - t.val := by omega
      positivity
    split_ifs with hlt
    · have hfrac : (s : ℝ) / ((n - t.val : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hd_pos]
        exact_mod_cast hlt.le
      have h1 : (1 - (s : ℝ) / ((n - t.val : ℕ) : ℝ)) * p t ≤
          (1 - (s : ℝ) / ((n - t.val : ℕ) : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (hp_le_one t) (by linarith)
      have hring : (s : ℝ) * (p t / ((n - t.val : ℕ) : ℝ)) +
          (1 - (s : ℝ) / ((n - t.val : ℕ) : ℝ)) * p t = p t := by ring
      linarith
    · have hge : (1 : ℝ) ≤ (s : ℝ) / ((n - t.val : ℕ) : ℝ) := by
        rw [one_le_div hd_pos]
        exact_mod_cast (show n - t.val ≤ s by omega)
      have hmul : 1 * p t ≤ ((s : ℝ) / ((n - t.val : ℕ) : ℝ)) * p t :=
        mul_le_mul_of_nonneg_right hge (hp_nonneg t)
      have hring : ((s : ℝ) / ((n - t.val : ℕ) : ℝ)) * p t =
          (s : ℝ) * (p t / ((n - t.val : ℕ) : ℝ)) := by ring
      linarith
  have hharm :
      ∑ t : Fin n, (if s < n - t.val then (1 : ℝ) - (s : ℝ) / ((n - t.val : ℕ) : ℝ) else 0) =
        ((n - s : ℕ) : ℝ) - (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ)) := by
    have hbij :
        ∑ t : Fin n, (if s < n - t.val then (1 : ℝ) - (s : ℝ) / ((n - t.val : ℕ) : ℝ) else 0) =
        ∑ k ∈ Finset.Ico s n, ((1 : ℝ) - (s : ℝ) / ((k : ℝ) + 1)) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun t _ => n - 1 - t.val) ?_ ?_ ?_ ?_
      · intro t ht
        have hlt := (Finset.mem_filter.mp ht).2
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · intro t₁ _ t₂ _ h
        exact Fin.ext (by omega)
      · intro k hk
        obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hk
        refine ⟨⟨n - 1 - k, by omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, ?_⟩
        dsimp only
        omega
      · intro t ht
        have hlt := (Finset.mem_filter.mp ht).2
        have hcast : ((n - t.val : ℕ) : ℝ) = ((n - 1 - t.val : ℕ) : ℝ) + 1 := by
          exact_mod_cast (show n - t.val = (n - 1 - t.val) + 1 by omega)
        rw [hcast]
    have hH : ∑ k ∈ Finset.Ico s n, ((k : ℝ) + 1)⁻¹ = (harmonic n : ℝ) - (harmonic s : ℝ) := by
      have hcast : ∀ m : ℕ, (harmonic m : ℝ) = ∑ k ∈ Finset.range m, ((k : ℝ) + 1)⁻¹ := fun m => by
        simp [harmonic]
      rw [hcast n, hcast s, ← Finset.sum_range_add_sum_Ico _ hs]
      ring
    rw [hbij, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    simp only [div_eq_mul_inv, ← Finset.mul_sum, hH]
  rw [havg_eq]
  calc ∑ t : Fin n, p t
      ≤ ∑ t : Fin n, ((s : ℝ) * (p t / ((n - t.val : ℕ) : ℝ)) +
          if s < n - t.val then 1 - (s : ℝ) / ((n - t.val : ℕ) : ℝ) else 0) :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = (s : ℝ) * (∑ t : Fin n, p t / ((n - t.val : ℕ) : ℝ)) +
          (((n - s : ℕ) : ℝ) - (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hharm]
    _ ≤ (s : ℝ) * 1 +
          (((n - s : ℕ) : ℝ) - (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ))) := by
        gcongr
    _ = (n : ℝ) - (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ)) := by
        rw [Nat.cast_sub hs]
        ring

/-- **Yao harmonic upper bound for all randomized algorithms:** for every `n ≥ 1`, every `s ≤ n`,
and every randomized online matching algorithm `μ : RandAlg (Fin n)`, there exists a permutation
`σ` such that `triArrivals n σ` admits a perfect matching of size `n` while
`μ.expectedMatchingSize (triArrivals n σ) ≤ n - s * (harmonic n - harmonic s)`. -/
theorem exists_rand_harmonic_upper_bound {n s : ℕ} (hn : 1 ≤ n) (hs : s ≤ n)
    (μ : RandAlg (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n),
      RandAlg.expectedMatchingSize μ (triArrivals n σ) ≤
        (n : ℝ) - (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ)) := by
  let ν : PMF (Equiv.Perm (Fin n)) := Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm (Fin n))
  have hB : 0 ≤ (n : ℝ) - (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ)) := by
    have h0 := det_triArrivals_avg_le_harmonic hn hs ⟨fun _ _ _ => none⟩
    have hnn : 0 ≤ (∑ σ : Equiv.Perm (Fin n),
        ((({ choose := fun _ _ _ => none } : DetAlg (Fin n)).runMatching
          (triArrivals n σ)).card : ℝ)) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact hnn.trans h0
  obtain ⟨σ, _, hle⟩ := RandAlg.exists_expectedMatchingSize_le ν (triArrivals n) hB (fun A => by
    have havg := det_triArrivals_avg_le_harmonic hn hs A
    convert havg using 1
    rw [div_eq_inv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [ν, Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv]) μ
  exact ⟨σ, hle⟩

private theorem log_div_le_harmonic_sub {s n : ℕ} (hs : s ≤ n) :
    Real.log (((n : ℝ) + 1) / ((s : ℝ) + 1)) ≤ (harmonic n : ℝ) - (harmonic s : ℝ) := by
  have hH : (harmonic n : ℝ) - (harmonic s : ℝ) = ∑ k ∈ Finset.Ico s n, ((k : ℝ) + 1)⁻¹ := by
    simp only [harmonic, ← Finset.sum_range_add_sum_Ico _ hs]
    push_cast; ring
  have hterm (k : ℕ) : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≤ ((k : ℝ) + 1)⁻¹ := by
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [← Real.log_div hk2.ne' hk1.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hk2 hk1)).trans_eq ?_
    field_simp [hk1.ne']
    ring
  have htelesc :
      ∑ k ∈ Finset.Ico s n, (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) =
        Real.log ((n : ℝ) + 1) - Real.log ((s : ℝ) + 1) := by
    have hfun (k : ℕ) : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) =
        Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k : ℝ) + 1) := by
      congr 2
      push_cast; ring
    simp_rw [hfun]
    exact Finset.sum_Ico_sub (fun k => Real.log ((k : ℝ) + 1)) hs
  rw [Real.log_div (by positivity) (by positivity), ← htelesc, hH]
  exact Finset.sum_le_sum fun k _ => hterm k

/-- **Explicit `1 - 1/e + 2/n` Yao upper bound:** for every `n ≥ 1` and every randomized online
matching algorithm `μ : RandAlg (Fin n)`, there exists a permutation `σ` such that
`triArrivals n σ` admits a perfect matching of size `n` while
`μ.expectedMatchingSize (triArrivals n σ) ≤ (1 - e⁻¹) * n + 2`. -/
theorem exists_rand_exp_upper_bound {n : ℕ} (hn : 1 ≤ n) (μ : RandAlg (Fin n)) :
    ∃ σ : Equiv.Perm (Fin n),
      RandAlg.expectedMatchingSize μ (triArrivals n σ) ≤
        (1 - Real.exp (-1)) * (n : ℝ) + 2 := by
  by_cases hn3 : n ≤ 2
  · obtain ⟨σ, hle⟩ := exists_rand_harmonic_upper_bound (s := 0) hn (Nat.zero_le n) μ
    refine ⟨σ, hle.trans ?_⟩
    have hexp_lt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hexp_pos : 0 < Real.exp (-1) := Real.exp_pos (-1)
    have hn_le : (n : ℝ) ≤ 2 := by exact_mod_cast hn3
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    nlinarith
  · have hn_ge : 3 ≤ n := by omega
    have he_gt : 2 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have he_lt : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
    set m : ℕ := Nat.floor (((n : ℝ) + 1) / Real.exp 1)
    have hm_ge1 : 1 ≤ m := by
      rw [Nat.one_le_floor_iff, one_le_div he_pos]
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      linarith
    set s : ℕ := m - 1
    have hs_eq : (s : ℝ) + 1 = (m : ℝ) := by
      have : s + 1 = m := Nat.sub_add_cancel hm_ge1
      exact_mod_cast this
    have hm_le : (m : ℝ) ≤ ((n : ℝ) + 1) / Real.exp 1 :=
      Nat.floor_le (by positivity)
    have hm_gt : ((n : ℝ) + 1) / Real.exp 1 - 1 < (m : ℝ) := by
      have := Nat.lt_floor_add_one (((n : ℝ) + 1) / Real.exp 1)
      linarith
    have hs_le_n : s ≤ n := by
      have : (m : ℝ) ≤ (n : ℝ) + 1 := hm_le.trans (div_le_self (by positivity) (by linarith))
      have hm_nat : m ≤ n + 1 := by exact_mod_cast this
      omega
    have hlog_ge : 1 ≤ Real.log (((n : ℝ) + 1) / ((s : ℝ) + 1)) := by
      rw [hs_eq, Real.le_log_iff_exp_le (by positivity)]
      rw [le_div_iff₀ (by positivity)]
      have := (le_div_iff₀ he_pos).mp hm_le
      linarith
    have hH_ge : 1 ≤ (harmonic n : ℝ) - (harmonic s : ℝ) :=
      hlog_ge.trans (log_div_le_harmonic_sub hs_le_n)
    obtain ⟨σ, hle⟩ := exists_rand_harmonic_upper_bound hn hs_le_n μ
    refine ⟨σ, hle.trans ?_⟩
    have hs_gt : ((n : ℝ) + 1) * Real.exp (-1) - 2 < (s : ℝ) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      linarith
    have hprod : (s : ℝ) * 1 ≤ (s : ℝ) * ((harmonic n : ℝ) - (harmonic s : ℝ)) :=
      mul_le_mul_of_nonneg_left hH_ge (Nat.cast_nonneg s)
    have hexp_pos : 0 < Real.exp (-1) := Real.exp_pos (-1)
    linarith

/-- **Tight `1 - 1/e` randomized impossibility** [KarpVaziraniVazirani1990]: no randomized online
bipartite matching algorithm `μ : RandAlg (Fin n)` (where `RandAlg L := PMF (DetAlg L)` ranges over
discrete, countably supported mixtures of deterministic online algorithms against an oblivious
adversary) achieves competitive ratio strictly above `1 - 1/e`, even with an arbitrary additive
slack `b`. -/
theorem not_rand_competitive_of_gt_one_sub_exp_neg_one
    {c : ℝ} (hc : 1 - Real.exp (-1) < c) (b : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ μ : RandAlg (Fin n),
      ∃ (arrivals : List (Finset (Fin n))) (M : Finset (Fin n × Fin arrivals.length)),
        IsMatching (graphOfArrivals arrivals) M ∧
        RandAlg.expectedMatchingSize μ arrivals < c * (M.card : ℝ) - b := by
  have hgap : 0 < c - (1 - Real.exp (-1)) := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((b + 2) / (c - (1 - Real.exp (-1))))
  let n : ℕ := max k 1
  have hn1 : 1 ≤ n := le_max_right k 1
  have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left k 1
  refine ⟨n, hn1, fun μ => ?_⟩
  obtain ⟨σ, hle⟩ := exists_rand_exp_upper_bound hn1 μ
  refine ⟨triArrivals n σ, triPerfectMatching n σ, isMatching_triPerfectMatching n σ, ?_⟩
  rw [card_triPerfectMatching]
  have h1 := (div_lt_iff₀ hgap).mp hk
  have h2 := mul_le_mul_of_nonneg_right hkn hgap.le
  linarith [mul_comm (n : ℝ) (c - (1 - Real.exp (-1)))]

end YaoUpperBound

end Cslib.Algorithms.Online.BipartiteMatching

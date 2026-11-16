/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.IdealCipher
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.UniformSubset

/-!
# The Domain Separation Lemma for the ideal cipher

Fix finite sets `U`, `V`, `X` and a function `f : U → V`. An adversary makes adaptive forward and
inverse queries `(μ, d, z)` with key `μ : U`; in Lean such a query is an `IdealCipher.Query U X`,
with `PermQuery.forward z` for `d = +1` and `PermQuery.inverse z` for `d = -1`. In the *coalesced*
experiment the keys of one fiber of `f` share one random permutation of `X`; in the *split*
experiment every key has its own, and the challenger records for each key `μ` the sampled domain
`Dom_μ^(+1)` and sampled range `Dom_μ^(-1)` of its permutation. Boneh and Shoup's Domain Separation
Lemma bounds the distance between the two experiments by the probability of the failure event `Z`:
two distinct keys with the same image under `f` share a point of their sampled domains or of their
sampled ranges.

## Main definitions

* `QueryDomains`, `recordQueryDomain`: the sets `(Dom_μ^(+1), Dom_μ^(-1))` of Attack Game 4.5 and
  their update after a query: the query's input goes into the set of its direction and the answer
  into the other.
* `DomainOverlap`: the domain separation failure event `Z`.
* `coalescedExperiment`, `splitPermStep`, `splitExperiment`: Experiments 0 and 1 of Attack Game 4.5.

## Main results

* `coalescedExperiment_closeTo_splitExperiment`: Theorem 4.15. The output distributions of the
  two experiments are `CloseTo` within the probability of `Z` in the split experiment, for every
  adversary.

## Differences from the source

* The source takes `U`, `V` and `X` nonempty. Here `U` and `V` may be empty; `X` is nonempty
  because the lazy sampler `IdealCipher.answer` needs a fallback answer.
* Each experiment samples only the permutation family it reads. The source samples both families
  in both experiments; the adversary's view is the same.
* The adversary is any `ProbOracleComp (IdealCipher.Spec U X) α`: it may use private coins, make
  any number of adaptive queries and return a value of any type, where the source's adversary
  outputs a bit.
* The conclusion is closeness on every event of the output, which for a bit output gives the
  source's bound on `|Pr[W₀] - Pr[W₁]|` through `Crypto.Game.closeTo_iff_coe_advantage_le`.

The lemma is information-theoretic: there is no query bound, and nothing is claimed about running
time.

## Proof

Both experiments are simulated lazily with one cache per key: Game 1 answers key `μ` from the
pooled cache of the fiber of `f μ` (the coalesced experiment), Game 2 from the cache of `μ` alone
(the split experiment). The handlers agree until a bad flag, which Game 2 raises exactly when the
recorded query sets overlap; `ProbOracleComp.IdenticalUntilBad.closeTo_run` gives the bound.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 4.7.4, Attack Game 4.5 (p. 160) and Theorem 4.15 (p. 161).
-/

public section

namespace Cslib.IdealCipher

open Cslib.RandomPermutation Cslib.Probability Cslib.OracleComp Cslib.ProbOracleComp
open scoped ENNReal

variable {U V X α : Type}
  [DecidableEq U] [Fintype U]
  [DecidableEq V] [Fintype V]
  [DecidableEq X] [Fintype X] [Nonempty X]

/-! ### Attack Game 4.5 and the failure event `Z` -/

/-- The sets `(Dom_μ^(+1), Dom_μ^(-1))` of Attack Game 4.5, the sampled domain and sampled range
of the permutation of each key `μ`. -/
abbrev QueryDomains (U X : Type) := U → Finset X × Finset X

omit [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
/-- Records the query `q = (μ, pq)` answered with `a`: as in Experiment 1 of Attack Game 4.5, the
query's input is added to the set of its direction and the answer to the set of the other
direction. -/
@[expose] def recordQueryDomain (dom : QueryDomains U X) (q : IdealCipher.Query U X) (a : X) :
    QueryDomains U X :=
  let e := PermQuery.toCacheEntry ⟨q.2, a⟩
  Function.update dom q.1 (insert e.1 (dom q.1).1, insert e.2 (dom q.1).2)

omit [Fintype U] [DecidableEq V] [Fintype V] [DecidableEq X] [Fintype X] [Nonempty X] in
/-- The domain separation failure event `Z` of Attack Game 4.5: there are distinct keys `μ ≠ μ'`
with `f μ = f μ'` whose sampled domains, or whose sampled ranges, intersect. -/
@[expose] def DomainOverlap (f : U → V) (dom : QueryDomains U X) : Prop :=
  ∃ μ μ', μ ≠ μ' ∧ f μ = f μ' ∧
    (((dom μ).1 ∩ (dom μ').1).Nonempty ∨ ((dom μ).2 ∩ (dom μ').2).Nonempty)

omit [DecidableEq U] [Fintype U] in
/-- Experiment 0 (the coalesced experiment) of Attack Game 4.5: sample independent uniform
permutations `P ν` of `X` for `ν : V` and answer each query `(μ, pq)` with `P (f μ)`. -/
@[expose] noncomputable def coalescedExperiment (f : U → V)
    (A : ProbOracleComp (IdealCipher.Spec U X) α) : PMF α := do
  let P ← PMF.pi (fun _ : V => PMF.uniformOfFintype (Equiv.Perm X))
  OracleComp.evalWith
    (sumHandler ProbComp.unifOracle (fun q => PMF.pure (evalPerm (P (f q.1)) q.2))) A

omit [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
/-- The query handler of Experiment 1 for fixed permutations `πFam`: answer `(μ, pq)` with
`πFam μ` and record the query in the sets `(Dom_μ^(+1), Dom_μ^(-1))`. -/
@[expose] noncomputable def splitPermStep (πFam : U → Equiv.Perm X)
    (q : IdealCipher.Query U X) : StateT (QueryDomains U X) PMF X := fun dom =>
  let a := evalPerm (πFam q.1) q.2
  PMF.pure (a, recordQueryDomain dom q a)

omit [DecidableEq V] [Fintype V] in
/-- Experiment 1 (the split experiment) of Attack Game 4.5: sample independent uniform
permutations `πFam μ` of `X` for `μ : U`, run `A` against them, and return its output together
with the final sets `(Dom_μ^(+1), Dom_μ^(-1))`. -/
@[expose] noncomputable def splitExperiment (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    PMF (α × QueryDomains U X) := do
  let πFam ← PMF.pi (fun _ : U => PMF.uniformOfFintype (Equiv.Perm X))
  ProbOracleComp.runWith (splitPermStep πFam) A (fun _ => (∅, ∅))

/-! ### Caches, fiber caches and partial bijections -/

private lemma runWith_simulation_of_invariant {Query State State' β : Type}
    {spec : Query → Type}
    (oracle : (q : Query) → StateT State PMF (spec q))
    (oracle' : (q : Query) → StateT State' PMF (spec q))
    (relate : State → PMF State') (invariant : State → Prop)
    (preserve : ∀ q s, invariant s → ∀ a s', (a, s') ∈ (oracle q s).support → invariant s')
    (step : ∀ q s, invariant s →
      (oracle q s).bind (fun (a, s') => (relate s').map (a, ·)) =
        (relate s).bind (oracle' q))
    (program : ProbOracleComp spec β) (s : State) (hs : invariant s) :
    (runWith oracle program s).bind (fun (a, s') => (relate s').map (a, ·)) =
      (relate s).bind (runWith oracle' program) := by
  apply OracleComp.run_interpret_simulation_of_invariant _ _ relate invariant ?_ ?_ program s hs
  · intro q state hstate a next hnext
    cases q with
    | inl n =>
      change (a, next) ∈ ((ProbComp.unifOracle n).map (·, state)).support at hnext
      obtain ⟨_, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      exact (Prod.mk.inj heq).2 ▸ hstate
    | inr q => exact preserve q state hstate a next hnext
  · intro q state hstate
    cases q with
    | inl n =>
      change ((ProbComp.unifOracle n).map (·, state)).bind
        (fun (a, next) => (relate next).map (a, ·)) =
          (relate state).bind (fun next => (ProbComp.unifOracle n).map (·, next))
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      exact PMF.bind_comm _ _ _
    | inr q => exact step q state hstate

omit [Fintype U] [DecidableEq V] [Fintype V] in
/-- `IdealCipher.answer` on a query whose answer is recorded in the key's cache. -/
private lemma answer_eq_pure_of_cachedAnswer_eq_some {q : IdealCipher.Query U X}
    {st : U → Cache X} {a : X} (h : cachedAnswer (st q.1) q.2 = some a) :
    IdealCipher.answer q st = PMF.pure (a, st) := by
  simp [IdealCipher.answer, RandomPermutation.answer_of_cachedAnswer_eq_some h, PMF.pure_map]

omit [Fintype U] [DecidableEq V] [Fintype V] in
/-- `IdealCipher.answer` on a query that misses the key's cache. -/
private lemma answer_eq_map_of_cachedAnswer_eq_none {q : IdealCipher.Query U X}
    {st : U → Cache X} (h : cachedAnswer (st q.1) q.2 = none)
    (hne : (freshAnswers (st q.1) q.2).Nonempty) :
    IdealCipher.answer q st = (PMF.uniformOfFinset _ hne).map fun a =>
      (a, Function.update st q.1 (PermQuery.toCacheEntry ⟨q.2, a⟩ :: st q.1)) := by
  simp [IdealCipher.answer, RandomPermutation.answer_of_cachedAnswer_eq_none h hne, PMF.map_comp,
    Function.comp_def]

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
/-- The domain and range of the entries of a cache. -/
private def cacheDomains (cache : Cache X) : Finset X × Finset X :=
  (cache.toFinset.image Prod.fst, cache.toFinset.image Prod.snd)

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma mem_cacheDomains_fst {cache : Cache X} {x : X} :
    x ∈ (cacheDomains cache).1 ↔ ∃ y, (x, y) ∈ cache := by
  simp [cacheDomains]

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma mem_cacheDomains_snd {cache : Cache X} {y : X} :
    y ∈ (cacheDomains cache).2 ↔ ∃ x, (x, y) ∈ cache := by
  simp [cacheDomains]

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma cacheDomains_toCacheEntry_cons {cache : Cache X} {q : PermQuery X} {a : X} :
    cacheDomains (PermQuery.toCacheEntry ⟨q, a⟩ :: cache) =
      (insert (PermQuery.toCacheEntry ⟨q, a⟩).1 (cacheDomains cache).1,
       insert (PermQuery.toCacheEntry ⟨q, a⟩).2 (cacheDomains cache).2) := by
  ext z <;> simp [cacheDomains, or_comm]

omit [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma recordQueryDomain_of_cacheDomains_mem {uCache : U → Cache X}
    {q : IdealCipher.Query U X} {a : X}
    (hmem : PermQuery.toCacheEntry ⟨q.2, a⟩ ∈ uCache q.1) :
    recordQueryDomain (fun μ => cacheDomains (uCache μ)) q a =
      fun μ => cacheDomains (uCache μ) := by
  ext μ z
  · by_cases hμ : μ = q.1
    · subst hμ
      simp only [recordQueryDomain, Function.update_self, Finset.mem_insert,
        or_iff_right_iff_imp]
      rintro rfl
      exact mem_cacheDomains_fst.mpr ⟨_, hmem⟩
    · simp [recordQueryDomain, hμ]
  · by_cases hμ : μ = q.1
    · subst hμ
      simp only [recordQueryDomain, Function.update_self, Finset.mem_insert,
        or_iff_right_iff_imp]
      rintro rfl
      exact mem_cacheDomains_snd.mpr ⟨_, hmem⟩
    · simp [recordQueryDomain, hμ]

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma toCacheEntry_mem_of_cachedAnswer_eq_some {cache : Cache X} {q : PermQuery X}
    {a : X} (h : cachedAnswer cache q = some a) :
    PermQuery.toCacheEntry ⟨q, a⟩ ∈ cache := by
  cases q with
  | forward x => exact mem_of_lookup_eq_some h
  | inverse y => exact mem_of_invLookup_eq_some h

omit [DecidableEq U] [Fintype V] [DecidableEq X] [Fintype X] [Nonempty X] in
/-- The pooled cache of all keys `μ` in the fiber `f⁻¹(ν)`. -/
private noncomputable def fiberCache (f : U → V) (uCache : U → Cache X) (ν : V) : Cache X :=
  (Finset.univ.filter fun μ => f μ = ν).toList.flatMap uCache

omit [DecidableEq U] [Fintype V] [DecidableEq X] [Fintype X] [Nonempty X] in
private lemma mem_fiberCache_iff {f : U → V} {uCache : U → Cache X} {ν : V} {e : X × X} :
    e ∈ fiberCache f uCache ν ↔ ∃ μ, f μ = ν ∧ e ∈ uCache μ := by
  simp [fiberCache]

omit [DecidableEq U] [Fintype V] [DecidableEq X] [Fintype X] [Nonempty X] in
private lemma agreesWith_fiberCache_iff {f : U → V} {uCache : U → Cache X} {ν : V}
    {π : Equiv.Perm X} :
    AgreesWith (fiberCache f uCache ν) π ↔ ∀ μ, f μ = ν → AgreesWith (uCache μ) π := by
  simp only [AgreesWith, mem_fiberCache_iff]
  constructor
  · intro h μ hμ e he; exact h e ⟨μ, hμ, he⟩
  · rintro h e ⟨μ, hμ, he⟩; exact h μ hμ e he

omit [DecidableEq U] [Fintype V] [Fintype X] [Nonempty X] in
private lemma cachedAnswer_fiber_of_uCache {f : U → V} {uCache : U → Cache X}
    (hbij : ∀ ν, IsPartialBijection (fiberCache f uCache ν))
    {μ : U} {q : PermQuery X} {a : X}
    (h : cachedAnswer (uCache μ) q = some a) :
    cachedAnswer (fiberCache f uCache (f μ)) q = some a := by
  obtain ⟨π, hπ⟩ := hbij (f μ)
  have ha : evalPerm π q = a :=
    (agreesWith_fiberCache_iff.mp hπ μ rfl).evalPerm_eq_of_cachedAnswer_eq_some h
  have hmem : PermQuery.toCacheEntry ⟨q, a⟩ ∈ fiberCache f uCache (f μ) :=
    mem_fiberCache_iff.mpr ⟨μ, rfl, toCacheEntry_mem_of_cachedAnswer_eq_some h⟩
  cases hfv : cachedAnswer (fiberCache f uCache (f μ)) q with
  | some b => rw [← ha, hπ.evalPerm_eq_of_cachedAnswer_eq_some hfv]
  | none =>
    exfalso
    cases q with
    | forward x => exact lookup_eq_none_iff.mp hfv _ hmem rfl
    | inverse y => exact invLookup_eq_none_iff.mp hfv _ hmem rfl

omit [DecidableEq U] [Fintype V] [Nonempty X] in
private lemma freshAnswers_fiber_subset {f : U → V} {uCache : U → Cache X}
    {μ : U} {q : PermQuery X} :
    freshAnswers (fiberCache f uCache (f μ)) q ⊆ freshAnswers (uCache μ) q := by
  intro a ha
  cases q with
  | forward x =>
    rw [freshAnswers, mem_unusedRange_iff, invLookup_eq_none_iff] at ha ⊢
    intro e he
    exact ha e (mem_fiberCache_iff.mpr ⟨μ, rfl, he⟩)
  | inverse y =>
    rw [freshAnswers, mem_unusedDomain_iff, lookup_eq_none_iff] at ha ⊢
    intro e he
    exact ha e (mem_fiberCache_iff.mpr ⟨μ, rfl, he⟩)

omit [Fintype V] [Nonempty X] in
private lemma isPartialBijection_fiber_update {f : U → V} {uCache : U → Cache X}
    (hbij : ∀ ν, IsPartialBijection (fiberCache f uCache ν))
    {μ : U} {q : PermQuery X}
    (hq : cachedAnswer (fiberCache f uCache (f μ)) q = none)
    {a : X} (ha : a ∈ freshAnswers (fiberCache f uCache (f μ)) q) :
    ∀ ν, IsPartialBijection
      (fiberCache f (Function.update uCache μ (PermQuery.toCacheEntry ⟨q, a⟩ :: uCache μ)) ν) := by
  intro ν
  by_cases hν : ν = f μ
  · subst hν
    obtain ⟨hlookup, hinv⟩ := lookup_and_invLookup_toCacheEntry_eq_none hq ha
    obtain ⟨π, hπ⟩ := (hbij (f μ)).cons_of_lookup_eq_none hlookup hinv
    rw [agreesWith_cons] at hπ
    refine ⟨π, agreesWith_fiberCache_iff.mpr fun μ' hμ' => ?_⟩
    by_cases heq : μ' = μ
    · subst heq
      rw [Function.update_self, agreesWith_cons]
      exact ⟨hπ.1, agreesWith_fiberCache_iff.mp hπ.2 μ' rfl⟩
    · simp only [Function.update_of_ne heq]
      exact agreesWith_fiberCache_iff.mp hπ.2 μ' hμ'
  · obtain ⟨π, hπ⟩ := hbij ν
    refine ⟨π, agreesWith_fiberCache_iff.mpr fun μ' hμ' => ?_⟩
    have hne : μ' ≠ μ := fun h => hν (hμ'.symm.trans (congrArg f h))
    simp only [Function.update_of_ne hne]
    exact agreesWith_fiberCache_iff.mp hπ μ' hμ'

omit [Nonempty X] in
private lemma complete_fiber_update_eq {f : U → V} {uCache : U → Cache X}
    {μ : U} {q : PermQuery X} {a : X} :
    IdealCipher.complete
        (fiberCache f (Function.update uCache μ (PermQuery.toCacheEntry ⟨q, a⟩ :: uCache μ))) =
      IdealCipher.complete
        (Function.update (fiberCache f uCache) (f μ)
          (PermQuery.toCacheEntry ⟨q, a⟩ :: fiberCache f uCache (f μ))) := by
  have hext (ν : V) :
      extPerms
          (fiberCache f (Function.update uCache μ (PermQuery.toCacheEntry ⟨q, a⟩ :: uCache μ)) ν) =
        extPerms
          (Function.update (fiberCache f uCache) (f μ)
            (PermQuery.toCacheEntry ⟨q, a⟩ :: fiberCache f uCache (f μ)) ν) := by
    ext π
    simp only [mem_extPerms_iff]
    by_cases hν : ν = f μ
    · subst hν
      rw [Function.update_self, agreesWith_fiberCache_iff, agreesWith_cons]
      constructor
      · intro h
        have hself := h μ rfl
        rw [Function.update_self, agreesWith_cons] at hself
        refine ⟨hself.1, agreesWith_fiberCache_iff.mpr fun μ' hμ' => ?_⟩
        by_cases hμ'' : μ' = μ
        · subst hμ''; exact hself.2
        · have hm := h μ' hμ'
          rwa [Function.update_of_ne hμ''] at hm
      · rintro ⟨hhead, htail⟩ μ' hμ'
        by_cases hμ'' : μ' = μ
        · subst hμ''
          rw [Function.update_self, agreesWith_cons]
          exact ⟨hhead, agreesWith_fiberCache_iff.mp htail μ' rfl⟩
        · rw [Function.update_of_ne hμ'']
          exact agreesWith_fiberCache_iff.mp htail μ' hμ'
    · have hne (μ' : U) (hμ' : f μ' = ν) : μ' ≠ μ :=
        fun h => hν (hμ'.symm.trans (congrArg f h))
      rw [Function.update_of_ne hν, agreesWith_fiberCache_iff, agreesWith_fiberCache_iff]
      constructor
      · intro h μ' hμ'
        have hm := h μ' hμ'
        rwa [Function.update_of_ne (hne μ' hμ')] at hm
      · intro h μ' hμ'
        rw [Function.update_of_ne (hne μ' hμ')]
        exact h μ' hμ'
  simp only [IdealCipher.complete, RandomPermutation.complete, hext]

/-! ### The coupled handlers of Game 1 and Game 2 -/

omit [Fintype V] in
/-- Game 1: a lazy handler whose answers have the law of `coalescedExperiment`. It raises the bad
flag when a query of `μ` misses the cache of `μ` but hits the pooled cache of the fiber of `f μ`,
or when the answer sampled fresh for `μ` is not fresh for the fiber and is resampled. -/
private noncomputable def game1Step (f : U → V) (q : IdealCipher.Query U X)
    (uCache : U → Cache X) : PMF (X × ((U → Cache X) × Bool)) :=
  match cachedAnswer (uCache q.1) q.2 with
  | some a => PMF.pure (a, (uCache, false))
  | none =>
    match cachedAnswer (fiberCache f uCache (f q.1)) q.2 with
    | some a => PMF.pure (a, (uCache, true))
    | none =>
      let vc := fiberCache f uCache (f q.1)
      let Sᵤ := freshAnswers (uCache q.1) q.2
      let Sᵥ := freshAnswers vc q.2
      if hSᵤ : Sᵤ.Nonempty then
        (PMF.uniformOfFinset Sᵤ hSᵤ).bind fun a =>
          if a ∈ Sᵥ then
            PMF.pure (a, (Function.update uCache q.1
              (PermQuery.toCacheEntry ⟨q.2, a⟩ :: uCache q.1), false))
          else if hSᵥ : Sᵥ.Nonempty then
            (PMF.uniformOfFinset Sᵥ hSᵥ).map fun a' =>
              (a', (Function.update uCache q.1
                (PermQuery.toCacheEntry ⟨q.2, a'⟩ :: uCache q.1), true))
          else
            (PMF.uniformOfFintype X).map fun a' =>
              (a', (Function.update uCache q.1
                (PermQuery.toCacheEntry ⟨q.2, a'⟩ :: uCache q.1), true))
      else
        (PMF.uniformOfFintype X).map fun a =>
          (a, (Function.update uCache q.1
            (PermQuery.toCacheEntry ⟨q.2, a⟩ :: uCache q.1), true))

omit [Fintype V] in
/-- Game 2: the lazy split handler `IdealCipher.answer`, with a bad flag raised exactly when a
query of `μ` that misses the cache of `μ` creates an overlap with another key of its fiber. -/
private noncomputable def game2Step (f : U → V) (q : IdealCipher.Query U X)
    (uCache : U → Cache X) : PMF (X × ((U → Cache X) × Bool)) :=
  (IdealCipher.answer q uCache).map fun (a, uCache') =>
    let badStep :=
      if cachedAnswer (uCache q.1) q.2 = none then
        decide (cachedAnswer (fiberCache f uCache (f q.1)) q.2 ≠ none ∨
          a ∉ freshAnswers (fiberCache f uCache (f q.1)) q.2)
      else false
    (a, (uCache', badStep))

/-! ### Game 1 simulates the coalesced experiment -/

omit [Fintype V] in
private lemma game1Step_preserve_isPartialBijection {f : U → V} (q : IdealCipher.Query U X)
    (st : (U → Cache X) × Bool)
    (hst : ∀ ν, IsPartialBijection (fiberCache f st.1 ν))
    (a : X) (st' : (U → Cache X) × Bool)
    (hmem : (a, st') ∈ (withBadFlag (game1Step f) q st).support)
    (ν : V) : IsPartialBijection (fiberCache f st'.1 ν) := by
  simp only [withBadFlag, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨a', u', b'⟩, hmem', heq⟩ := hmem
  cases heq
  change IsPartialBijection (fiberCache f u' ν)
  dsimp only [game1Step] at hmem'
  cases hqu : cachedAnswer (st.1 q.1) q.2 with
  | some b =>
    rw [hqu] at hmem'
    simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem'
    rcases hmem' with ⟨_, rfl, _⟩
    exact hst ν
  | none =>
    rw [hqu] at hmem'
    cases hqv : cachedAnswer (fiberCache f st.1 (f q.1)) q.2 with
    | some b =>
      rw [hqv] at hmem'
      simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem'
      rcases hmem' with ⟨_, rfl, _⟩
      exact hst ν
    | none =>
      rw [hqv] at hmem'
      have hv_ne := (hst (f q.1)).freshAnswers_nonempty hqv
      have hu_ne : (freshAnswers (st.1 q.1) q.2).Nonempty :=
        hv_ne.mono freshAnswers_fiber_subset
      simp only [hu_ne, ↓reduceDIte, PMF.mem_support_bind_iff] at hmem'
      obtain ⟨c, _, hc⟩ := hmem'
      by_cases hcS : c ∈ freshAnswers (fiberCache f st.1 (f q.1)) q.2
      · simp only [hcS, ↓reduceIte, PMF.mem_support_pure_iff, Prod.mk.injEq] at hc
        rcases hc with ⟨_, rfl, _⟩
        exact isPartialBijection_fiber_update hst hqv hcS ν
      · simp only [hcS, ↓reduceIte, hv_ne, ↓reduceDIte, PMF.mem_support_map_iff] at hc
        obtain ⟨c', hc', heq'⟩ := hc
        rw [PMF.mem_support_uniformOfFinset_iff] at hc'
        rcases Prod.mk.inj heq' with ⟨_, rfl, _⟩
        exact isPartialBijection_fiber_update hst hqv hc' ν

private lemma game1Step_simulate {f : U → V} (q : IdealCipher.Query U X)
    (st : (U → Cache X) × Bool)
    (hst : ∀ ν, IsPartialBijection (fiberCache f st.1 ν)) :
    (withBadFlag (game1Step f) q st).bind
        (fun (a, st') => (IdealCipher.complete (fiberCache f st'.1)).map (a, ·)) =
      (IdealCipher.complete (fiberCache f st.1)).bind
        (fun P => (fun x => (x, P)) <$> PMF.pure (evalPerm (P (f q.1)) q.2)) := by
  have hdrop : (withBadFlag (game1Step f) q st).bind
        (fun (a, st') => (IdealCipher.complete (fiberCache f st'.1)).map (a, ·)) =
      (game1Step f q st.1).bind
        (fun (a, u', _) => (IdealCipher.complete (fiberCache f u')).map (a, ·)) := by
    simp only [withBadFlag, PMF.bind_map, Function.comp_def]
    rfl
  rw [hdrop]
  have hanswer_eq : (game1Step f q st.1).bind
        (fun (a, u', _) => (IdealCipher.complete (fiberCache f u')).map (a, ·)) =
      (IdealCipher.answer (f q.1, q.2) (fiberCache f st.1)).bind
        (fun (a, v') => (IdealCipher.complete v').map (a, ·)) := by
    dsimp only [game1Step]
    cases hqu : cachedAnswer (st.1 q.1) q.2 with
    | some a =>
      rw [answer_eq_pure_of_cachedAnswer_eq_some (q := (f q.1, q.2))
        (cachedAnswer_fiber_of_uCache hst hqu), PMF.pure_bind, PMF.pure_bind]
    | none =>
      cases hqv : cachedAnswer (fiberCache f st.1 (f q.1)) q.2 with
      | some a =>
        rw [answer_eq_pure_of_cachedAnswer_eq_some (q := (f q.1, q.2)) hqv, PMF.pure_bind,
          PMF.pure_bind]
      | none =>
        have hv_ne := (hst (f q.1)).freshAnswers_nonempty hqv
        have hu_ne : (freshAnswers (st.1 q.1) q.2).Nonempty :=
          hv_ne.mono freshAnswers_fiber_subset
        simp only [hu_ne, ↓reduceDIte]
        refine (?_ : _ = ((PMF.uniformOfFinset _ hu_ne).bind fun a =>
            if a ∈ freshAnswers (fiberCache f st.1 (f q.1)) q.2 then PMF.pure a
            else PMF.uniformOfFinset _ hv_ne).bind fun a =>
              (IdealCipher.complete (Function.update (fiberCache f st.1) (f q.1)
                (PermQuery.toCacheEntry ⟨q.2, a⟩ :: fiberCache f st.1 (f q.1)))).map
                  (a, ·)).trans ?_
        · simp only [PMF.bind_bind]
          refine congr_arg _ (funext fun a => ?_)
          by_cases ha : a ∈ freshAnswers (fiberCache f st.1 (f q.1)) q.2
          · simp [ha, complete_fiber_update_eq]
          · simp only [ha, ↓reduceIte, hv_ne, ↓reduceDIte, PMF.bind_map]
            refine congr_arg _ (funext fun a' => ?_)
            simp only [Function.comp_def, complete_fiber_update_eq]
        · rw [Probability.PMF.unifOn_rehash_eq freshAnswers_fiber_subset hu_ne hv_ne,
            answer_eq_map_of_cachedAnswer_eq_none (q := (f q.1, q.2)) hqv hv_ne, PMF.bind_map]
          rfl
  rw [hanswer_eq]
  exact IdealCipher.answer_complete (f q.1, q.2) (fiberCache f st.1) hst

private lemma coalescedExperiment_eq_game1 (f : U → V)
    (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    coalescedExperiment f A =
      (runWith (withBadFlag (game1Step f)) A (fun _ => [], false)).map Prod.fst := by
  let target : (q : IdealCipher.Query U X) → StateT (V → Equiv.Perm X) PMF X :=
    fun q P => (PMF.pure (evalPerm (P (f q.1)) q.2)).map (·, P)
  have hsim := runWith_simulation_of_invariant (withBadFlag (game1Step f)) target
    (fun st => IdealCipher.complete (fiberCache f st.1))
    (fun st => ∀ ν, IsPartialBijection (fiberCache f st.1 ν))
    (fun q st hst a st' hmem => game1Step_preserve_isPartialBijection q st hst a st' hmem)
    (fun q st hst => by
      simpa [target] using game1Step_simulate q st hst)
    A (fun _ => [], false)
    (fun ν => ⟨1, agreesWith_fiberCache_iff.mpr fun μ _ => agreesWith_nil 1⟩)
  have hfiber_nil : fiberCache f (fun _ : U => ([] : Cache X)) = fun _ => [] := by
    funext ν
    simp [fiberCache]
  have hfst := congrArg (PMF.map Prod.fst) hsim
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hfst
  have hlhs : ((runWith (withBadFlag (game1Step f)) A (fun _ => [], false)).bind fun x =>
      (IdealCipher.complete (fiberCache f x.2.1)).map (fun _ => x.1)) =
      (runWith (withBadFlag (game1Step f)) A (fun _ => [], false)).map Prod.fst := by
    change ((runWith (withBadFlag (game1Step f)) A (fun _ => [], false)).bind fun x =>
      (IdealCipher.complete (fiberCache f x.2.1)).map (Function.const _ x.1)) = _
    simp only [PMF.map_const]
    rfl
  rw [hlhs, hfiber_nil, IdealCipher.complete_nil] at hfst
  rw [coalescedExperiment, hfst]
  refine congr_arg _ (funext fun P => ?_)
  dsimp only [target]
  rw [ProbOracleComp.runWith_readOnly, PMF.map_comp]
  exact (PMF.map_id _).symm

/-! ### Game 2 simulates the split experiment -/

omit [Fintype V] in
private lemma game2Step_map_fst (f : U → V) (q : IdealCipher.Query U X)
    (uCache : U → Cache X) :
    (game2Step f q uCache).map (Prod.map id Prod.fst) = IdealCipher.answer q uCache := by
  simp only [game2Step, PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq]
  exact PMF.map_id _

omit [Fintype V] in
private lemma game2_map_fst (f : U → V) (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).map (Prod.map id Prod.fst) =
      runWith IdealCipher.answer A (fun _ => []) :=
  runWith_withBadFlag_map_fst (game2Step f) IdealCipher.answer (game2Step_map_fst f)
    A (fun _ => []) false

omit [DecidableEq V] [Fintype V] in
private lemma splitExperiment_eq_answer (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    (runWith IdealCipher.answer A (fun _ => [])).map
        (fun (a, uCache) => (a, fun μ => cacheDomains (uCache μ))) =
      splitExperiment A := by
  let target : (q : IdealCipher.Query U X) →
      StateT ((U → Equiv.Perm X) × QueryDomains U X) PMF X :=
    fun q st =>
      PMF.pure (evalPerm (st.1 q.1) q.2,
        (st.1, recordQueryDomain st.2 q (evalPerm (st.1 q.1) q.2)))
  have hsim := runWith_simulation_of_invariant IdealCipher.answer target
    (fun uCache => (IdealCipher.complete uCache).map (·, fun μ => cacheDomains (uCache μ)))
    (fun uCache => ∀ μ, IsPartialBijection (uCache μ))
    IdealCipher.answer_preserve_isPartialBijection
    (fun q uCache hcache => by
      have hcomp := IdealCipher.answer_complete q uCache hcache
      have hcomp' := congrArg (PMF.map fun (a, πFam) =>
          (a, (πFam, recordQueryDomain (fun μ => cacheDomains (uCache μ)) q a))) hcomp
      rw [PMF.map_bind] at hcomp'
      simp only [PMF.map_comp, Function.comp_def] at hcomp'
      have hlhs : (IdealCipher.answer q uCache).bind (fun (a, u') =>
          ((IdealCipher.complete u').map (·, fun μ => cacheDomains (u' μ))).map (a, ·)) =
          (IdealCipher.answer q uCache).bind (fun (a, u') =>
            (IdealCipher.complete u').map (fun πFam =>
              (a, (πFam, recordQueryDomain (fun μ => cacheDomains (uCache μ)) q a)))) := by
        apply Probability.PMF.bind_congr_on_support
        rintro ⟨a, u'⟩ hmem
        have hdom : (fun μ => cacheDomains (u' μ)) =
            recordQueryDomain (fun μ => cacheDomains (uCache μ)) q a := by
          cases hhit : cachedAnswer (uCache q.1) q.2 with
          | some b₀ =>
            rw [answer_eq_pure_of_cachedAnswer_eq_some hhit, PMF.mem_support_pure_iff,
              Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl⟩
            exact (recordQueryDomain_of_cacheDomains_mem
              (toCacheEntry_mem_of_cachedAnswer_eq_some hhit)).symm
          | none =>
            rw [answer_eq_map_of_cachedAnswer_eq_none hhit
              ((hcache q.1).freshAnswers_nonempty hhit), PMF.mem_support_map_iff] at hmem
            obtain ⟨b', _, heq'⟩ := hmem
            rcases Prod.mk.inj heq' with ⟨rfl, rfl⟩
            funext μ
            by_cases hμ : μ = q.1
            · rw [hμ]
              simp [recordQueryDomain, cacheDomains_toCacheEntry_cons]
            · simp [recordQueryDomain, hμ]
        simp only [PMF.map_comp, Function.comp_def, hdom]
      have hrhs : (IdealCipher.answer q uCache).bind (fun (a, u') =>
          (IdealCipher.complete u').map (fun πFam =>
            (a, (πFam, recordQueryDomain (fun μ => cacheDomains (uCache μ)) q a)))) =
          ((IdealCipher.complete uCache).map (·, fun μ => cacheDomains (uCache μ))).bind
            (target q) :=
        hcomp'.trans (by simp [target, PMF.map_bind, Function.comp_def])
      exact hlhs.trans hrhs)
    A (fun _ => []) (fun _ => isPartialBijection_nil)
  have hfst := congrArg (PMF.map fun (a, πFam, dom) => (a, dom)) hsim
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hfst
  have hlhs : ((runWith IdealCipher.answer A fun x => []).bind fun x =>
      (IdealCipher.complete x.2).map (fun _ => (x.1, fun μ => cacheDomains (x.2 μ)))) =
      (runWith IdealCipher.answer A (fun _ => [])).map
        (fun (a, uCache) => (a, fun μ => cacheDomains (uCache μ))) := by
    change ((runWith IdealCipher.answer A fun x => []).bind fun x =>
      (IdealCipher.complete x.2).map
        (Function.const _ (x.1, fun μ => cacheDomains (x.2 μ)))) = _
    simp only [PMF.map_const]
    rfl
  have hdrop' : ∀ πFam : U → Equiv.Perm X,
      (runWith target A (πFam, fun _ => (∅, ∅))).map (fun (a, _, dom) => (a, dom)) =
        runWith (splitPermStep πFam) A (fun _ => (∅, ∅)) := fun πFam =>
    runWith_map_state_of_invariant target (splitPermStep πFam) (fun (_, dom) => dom)
      (fun st => st.1 = πFam)
      (fun q ⟨π', dom⟩ hπ a ⟨π'', dom'⟩ hmem => by
        simp only [target, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
        exact hmem.2.1 ▸ hπ)
      (fun q ⟨π', dom⟩ hπ => by
        subst hπ
        simp [target, splitPermStep, PMF.pure_map])
      A (πFam, fun _ => (∅, ∅)) rfl
  rw [hlhs, IdealCipher.complete_nil] at hfst
  rw [hfst, splitExperiment]
  simp only [PMF.bind_map, Function.comp_def]
  exact congr_arg _ (funext hdrop')

/-! ### Games 1 and 2 agree until the flag, which in Game 2 is the overlap event -/

omit [Fintype V] in
private lemma identicalUntilBad_game1_game2 (f : U → V) :
    ProbOracleComp.IdenticalUntilBad
      (withBadFlag (game1Step (X := X) f)) (withBadFlag (game2Step (X := X) f)) FlagBad := by
  refine ProbOracleComp.identicalUntilBad_withBadFlag (game1Step f) (game2Step f) ?_
  intro q uCache a uCache'
  dsimp only [game1Step, game2Step]
  cases hqu : cachedAnswer (uCache q.1) q.2 with
  | some b => simp [answer_eq_pure_of_cachedAnswer_eq_some hqu]
  | none =>
    cases hqv : cachedAnswer (fiberCache f uCache (f q.1)) q.2 with
    | some b =>
      have h1 : (PMF.pure (b, (uCache, true))) (a, (uCache', false)) = 0 := by
        simp [PMF.pure_apply]
      have h2 : (PMF.map (fun x => (x.1, x.2, true)) (IdealCipher.answer q uCache))
          (a, (uCache', false)) = 0 := by
        rw [PMF.map_apply]
        simp
      simp [h1, h2]
    | none =>
      by_cases hu_ne : (freshAnswers (uCache q.1) q.2).Nonempty
      · rw [answer_eq_map_of_cachedAnswer_eq_none hqu hu_ne]
        simp only [hu_ne, ↓reduceDIte, PMF.map_comp, Function.comp_def, PMF.bind_apply,
          tsum_fintype]
        rw [PMF.map_apply, tsum_fintype]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hc : c ∈ freshAnswers (fiberCache f uCache (f q.1)) q.2
        · simp [hc]
        · have hlhs : (if hSᵥ : (freshAnswers (fiberCache f uCache (f q.1)) q.2).Nonempty then
              PMF.map (fun a' => (a', Function.update uCache q.1
                (PermQuery.toCacheEntry ⟨q.2, a'⟩ :: uCache q.1), true))
                (PMF.uniformOfFinset (freshAnswers (fiberCache f uCache (f q.1)) q.2) hSᵥ)
            else
              PMF.map (fun a' => (a', Function.update uCache q.1
                (PermQuery.toCacheEntry ⟨q.2, a'⟩ :: uCache q.1), true))
                (PMF.uniformOfFintype X)) (a, (uCache', false)) = 0 := by
            split_ifs <;> simp [PMF.map_apply]
          simp [hc, hlhs]
      · have hzero : (freshAnswers (fiberCache f uCache (f q.1)) q.2) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro c hc
          exact hu_ne ⟨c, freshAnswers_fiber_subset hc⟩
        simp only [hu_ne, ↓reduceDIte, PMF.map_apply]
        simp [hzero]

omit [Fintype V] in
private lemma game2_bad_iff_domainOverlap_inv (f : U → V) (q : IdealCipher.Query U X)
    (st : (U → Cache X) × Bool)
    (hst : (∀ μ, IsPartialBijection (st.1 μ)) ∧
      (FlagBad st ↔ DomainOverlap f (fun μ => cacheDomains (st.1 μ))))
    (a : X) (st' : (U → Cache X) × Bool)
    (hmem : (a, st') ∈ (withBadFlag (game2Step f) q st).support) :
    (∀ μ, IsPartialBijection (st'.1 μ)) ∧
      (FlagBad st' ↔ DomainOverlap f (fun μ => cacheDomains (st'.1 μ))) := by
  simp only [withBadFlag, game2Step, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨a₁, u₁, b₁⟩, ⟨⟨a₂, u₂⟩, hans, h2⟩, h1⟩ := hmem
  cases h2; cases h1
  have hmem_ans : (a₂, u₂) ∈ (IdealCipher.answer q st.1).support := hans
  rcases hst with ⟨hbij, hiff⟩
  refine ⟨IdealCipher.answer_preserve_isPartialBijection q st.1 hbij a₂ u₂ hmem_ans, ?_⟩
  cases hhit : cachedAnswer (st.1 q.1) q.2 with
  | some b₀ =>
    rw [answer_eq_pure_of_cachedAnswer_eq_some hhit, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem_ans
    rcases hmem_ans with ⟨rfl, rfl⟩
    simpa [FlagBad] using hiff
  | none =>
    have hne := (hbij q.1).freshAnswers_nonempty hhit
    rw [answer_eq_map_of_cachedAnswer_eq_none hhit hne, PMF.mem_support_map_iff] at hmem_ans
    obtain ⟨c, hc_mem, heq⟩ := hmem_ans
    rw [PMF.mem_support_uniformOfFinset_iff] at hc_mem
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    by_cases hprev : st.2 = true
    · have hsub : ∀ μ e, e ∈ st.1 μ →
          e ∈ Function.update st.1 q.1 (PermQuery.toCacheEntry ⟨q.2, c⟩ :: st.1 q.1) μ := by
        intro μ e he
        by_cases hμ : μ = q.1
        · rw [hμ, Function.update_self]
          exact List.mem_cons_of_mem _ (hμ ▸ he)
        · rwa [Function.update_of_ne hμ]
      have hdom_new : DomainOverlap f (fun μ => cacheDomains
          (Function.update st.1 q.1 (PermQuery.toCacheEntry ⟨q.2, c⟩ :: st.1 q.1) μ)) := by
        rcases hiff.mp hprev with ⟨μ₁, μ₂, hne, hf, ⟨x, hx⟩ | ⟨y, hy⟩⟩
        · refine ⟨μ₁, μ₂, hne, hf, Or.inl ⟨x, Finset.mem_inter.mpr ?_⟩⟩
          rw [Finset.mem_inter, mem_cacheDomains_fst, mem_cacheDomains_fst] at hx
          exact ⟨mem_cacheDomains_fst.mpr ⟨hx.1.choose, hsub μ₁ _ hx.1.choose_spec⟩,
            mem_cacheDomains_fst.mpr ⟨hx.2.choose, hsub μ₂ _ hx.2.choose_spec⟩⟩
        · refine ⟨μ₁, μ₂, hne, hf, Or.inr ⟨y, Finset.mem_inter.mpr ?_⟩⟩
          rw [Finset.mem_inter, mem_cacheDomains_snd, mem_cacheDomains_snd] at hy
          exact ⟨mem_cacheDomains_snd.mpr ⟨hy.1.choose, hsub μ₁ _ hy.1.choose_spec⟩,
            mem_cacheDomains_snd.mpr ⟨hy.2.choose, hsub μ₂ _ hy.2.choose_spec⟩⟩
      simp [FlagBad, hprev, hdom_new]
    · have hfalse : st.2 = false := Bool.eq_false_iff.mpr hprev
      have hno_old : ¬DomainOverlap f (fun μ => cacheDomains (st.1 μ)) :=
        fun h => hprev (hiff.mpr h)
      simp only [FlagBad, Prod.map, id_eq, hfalse, Bool.false_or, ↓reduceIte]
      rw [decide_eq_true_eq]
      constructor
      · intro hbad
        rcases hbad with hfib | hnotfresh
        · obtain ⟨b, hfib_eq⟩ := Option.ne_none_iff_exists'.mp hfib
          have hmem_fib := toCacheEntry_mem_of_cachedAnswer_eq_some hfib_eq
          obtain ⟨μ', hμ', hmem'⟩ := mem_fiberCache_iff.mp hmem_fib
          have hne_μ : q.1 ≠ μ' := by
            rintro rfl
            cases hqq : q.2 with
            | forward x =>
              rw [hqq] at hhit hmem'
              exact lookup_eq_none_iff.mp hhit _ hmem' rfl
            | inverse y =>
              rw [hqq] at hhit hmem'
              exact invLookup_eq_none_iff.mp hhit _ hmem' rfl
          refine ⟨q.1, μ', hne_μ, hμ'.symm, ?_⟩
          cases hqq : q.2 with
          | forward x =>
            rw [hqq] at hmem'
            exact Or.inl ⟨x, Finset.mem_inter.mpr
              ⟨by simp [cacheDomains, PermQuery.toCacheEntry],
                by simp only [Function.update_of_ne hne_μ.symm]
                   exact mem_cacheDomains_fst.mpr ⟨b, hmem'⟩⟩⟩
          | inverse y =>
            rw [hqq] at hmem'
            exact Or.inr ⟨y, Finset.mem_inter.mpr
              ⟨by simp [cacheDomains, PermQuery.toCacheEntry],
                by simp only [Function.update_of_ne hne_μ.symm]
                   exact mem_cacheDomains_snd.mpr ⟨b, hmem'⟩⟩⟩
        · cases hqq : q.2 with
          | forward x =>
            rw [hqq, freshAnswers, mem_unusedRange_iff] at hnotfresh
            have hne_inv : invLookup (fiberCache f st.1 (f q.1)) c ≠ none := hnotfresh
            obtain ⟨b, hinv⟩ := Option.ne_none_iff_exists'.mp hne_inv
            have hmem_fib := mem_of_invLookup_eq_some hinv
            obtain ⟨μ', hμ', hmem'⟩ := mem_fiberCache_iff.mp hmem_fib
            rw [hqq, freshAnswers, mem_unusedRange_iff] at hc_mem
            have hne_μ : q.1 ≠ μ' := by
              rintro rfl
              exact invLookup_eq_none_iff.mp hc_mem _ hmem' rfl
            refine ⟨q.1, μ', hne_μ, hμ'.symm, Or.inr ⟨c, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
            · simp [cacheDomains, PermQuery.toCacheEntry]
            · dsimp only
              rw [Function.update_of_ne hne_μ.symm]
              exact mem_cacheDomains_snd.mpr ⟨b, hmem'⟩
          | inverse y =>
            rw [hqq, freshAnswers, mem_unusedDomain_iff] at hnotfresh
            have hne_lk : (fiberCache f st.1 (f q.1)).lookup c ≠ none := hnotfresh
            obtain ⟨b, hlk⟩ := Option.ne_none_iff_exists'.mp hne_lk
            have hmem_fib := mem_of_lookup_eq_some hlk
            obtain ⟨μ', hμ', hmem'⟩ := mem_fiberCache_iff.mp hmem_fib
            rw [hqq, freshAnswers, mem_unusedDomain_iff] at hc_mem
            have hne_μ : q.1 ≠ μ' := by
              rintro rfl
              exact lookup_eq_none_iff.mp hc_mem _ hmem' rfl
            refine ⟨q.1, μ', hne_μ, hμ'.symm, Or.inl ⟨c, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
            · simp [cacheDomains, PermQuery.toCacheEntry]
            · dsimp only
              rw [Function.update_of_ne hne_μ.symm]
              exact mem_cacheDomains_fst.mpr ⟨b, hmem'⟩
      · rintro ⟨μ₁, μ₂, hne, hf, hov⟩
        have hstep (μ' : U) (hne' : μ' ≠ q.1) (hf' : f μ' = f q.1)
            (hov' : (((cacheDomains (PermQuery.toCacheEntry ⟨q.2, c⟩ :: st.1 q.1)).1 ∩
              (cacheDomains (st.1 μ')).1).Nonempty) ∨
              (((cacheDomains (PermQuery.toCacheEntry ⟨q.2, c⟩ :: st.1 q.1)).2 ∩
                (cacheDomains (st.1 μ')).2).Nonempty)) :
            cachedAnswer (fiberCache f st.1 (f q.1)) q.2 ≠ none ∨
              c ∉ freshAnswers (fiberCache f st.1 (f q.1)) q.2 := by
          rcases hov' with ⟨x, hx⟩ | ⟨y, hy⟩
          · rw [Finset.mem_inter, cacheDomains_toCacheEntry_cons, Finset.mem_insert] at hx
            rcases hx with ⟨hx_eq | hx_old, hxμ'⟩
            · cases hqq : q.2 with
              | forward x₀ =>
                rw [hqq, PermQuery.toCacheEntry] at hx_eq
                dsimp only at hx_eq
                rw [hx_eq] at hxμ'
                left
                obtain ⟨b, hb⟩ := mem_cacheDomains_fst.mp hxμ'
                have hmem_fib : (x₀, b) ∈ fiberCache f st.1 (f q.1) :=
                  mem_fiberCache_iff.mpr ⟨μ', hf', hb⟩
                intro hnone
                exact lookup_eq_none_iff.mp hnone _ hmem_fib rfl
              | inverse y₀ =>
                rw [hqq, PermQuery.toCacheEntry] at hx_eq
                dsimp only at hx_eq
                rw [hx_eq] at hxμ'
                right
                rw [freshAnswers, mem_unusedDomain_iff]
                obtain ⟨b, hb⟩ := mem_cacheDomains_fst.mp hxμ'
                have hmem_fib : (c, b) ∈ fiberCache f st.1 (f q.1) :=
                  mem_fiberCache_iff.mpr ⟨μ', hf', hb⟩
                intro hmem_dom
                exact lookup_eq_none_iff.mp hmem_dom _ hmem_fib rfl
            · exfalso
              exact hno_old ⟨q.1, μ', hne'.symm, hf'.symm,
                Or.inl ⟨x, Finset.mem_inter.mpr ⟨hx_old, hxμ'⟩⟩⟩
          · rw [Finset.mem_inter, cacheDomains_toCacheEntry_cons, Finset.mem_insert] at hy
            rcases hy with ⟨hy_eq | hy_old, hyμ'⟩
            · cases hqq : q.2 with
              | forward x₀ =>
                rw [hqq, PermQuery.toCacheEntry] at hy_eq
                dsimp only at hy_eq
                rw [hy_eq] at hyμ'
                right
                rw [freshAnswers, mem_unusedRange_iff]
                obtain ⟨b, hb⟩ := mem_cacheDomains_snd.mp hyμ'
                have hmem_fib : (b, c) ∈ fiberCache f st.1 (f q.1) :=
                  mem_fiberCache_iff.mpr ⟨μ', hf', hb⟩
                intro hmem_ran
                exact invLookup_eq_none_iff.mp hmem_ran _ hmem_fib rfl
              | inverse y₀ =>
                rw [hqq, PermQuery.toCacheEntry] at hy_eq
                dsimp only at hy_eq
                rw [hy_eq] at hyμ'
                left
                obtain ⟨b, hb⟩ := mem_cacheDomains_snd.mp hyμ'
                have hmem_fib : (b, y₀) ∈ fiberCache f st.1 (f q.1) :=
                  mem_fiberCache_iff.mpr ⟨μ', hf', hb⟩
                intro hnone
                exact invLookup_eq_none_iff.mp hnone _ hmem_fib rfl
            · exfalso
              exact hno_old ⟨q.1, μ', hne'.symm, hf'.symm,
                Or.inr ⟨y, Finset.mem_inter.mpr ⟨hy_old, hyμ'⟩⟩⟩
        dsimp only at hov
        by_cases h1' : μ₁ = q.1
        · rw [h1', Function.update_self,
            Function.update_of_ne (by rw [← h1']; exact hne.symm)] at hov
          exact hstep μ₂ (by rw [← h1']; exact hne.symm) (by rw [← h1']; exact hf.symm) hov
        · by_cases h2' : μ₂ = q.1
          · rw [h2', Function.update_self, Function.update_of_ne h1',
              Finset.inter_comm (cacheDomains (st.1 μ₁)).1,
              Finset.inter_comm (cacheDomains (st.1 μ₁)).2] at hov
            exact hstep μ₁ h1' (by rw [← h2']; exact hf) hov
          · exfalso
            rw [Function.update_of_ne h1', Function.update_of_ne h2'] at hov
            exact hno_old ⟨μ₁, μ₂, hne, hf, hov⟩

/-! ### Theorem 4.15 (Domain Separation Lemma) -/

omit [Fintype V] in
/-- The probability that Game 2 raises its flag is the probability of `Z` in Experiment 1. -/
private lemma game2_bad_eq_failureProb (f : U → V)
    (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).toOuterMeasure
        {x | FlagBad x.2} =
      (splitExperiment A).toOuterMeasure {x | DomainOverlap f x.2} := by
  have hinv : ∀ x ∈ (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).support,
      (∀ μ, IsPartialBijection (x.2.1 μ)) ∧
        (FlagBad x.2 ↔ DomainOverlap f (fun μ => cacheDomains (x.2.1 μ))) := by
    rintro ⟨a, st'⟩ hmem
    exact ProbOracleComp.runWith_invariant (withBadFlag (game2Step f))
      (fun st => (∀ μ, IsPartialBijection (st.1 μ)) ∧
        (FlagBad st ↔ DomainOverlap f (fun μ => cacheDomains (st.1 μ))))
      (fun q st hst a st' h => game2_bad_iff_domainOverlap_inv f q st hst a st' h)
      A (fun _ => [], false)
      ⟨fun _ => isPartialBijection_nil, by simp [FlagBad, DomainOverlap, cacheDomains]⟩
      a st' hmem
  have hcongr :
      (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).toOuterMeasure
          {x | FlagBad x.2} =
        (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).toOuterMeasure
          {x | DomainOverlap f (fun μ => cacheDomains (x.2.1 μ))} := by
    rw [← PMF.toOuterMeasure_apply_inter_support
        (s := {x : α × ((U → Cache X) × Bool) | FlagBad x.2}),
      ← PMF.toOuterMeasure_apply_inter_support (s := {x : α × ((U → Cache X) × Bool) |
        DomainOverlap f (fun μ => cacheDomains (x.2.1 μ))})]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact and_congr_left fun hmem => (hinv x hmem).2
  rw [hcongr]
  have hmap1 :
      (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).toOuterMeasure
          {x | DomainOverlap f (fun μ => cacheDomains (x.2.1 μ))} =
        (runWith IdealCipher.answer A (fun _ => [])).toOuterMeasure
          {x | DomainOverlap f (fun μ => cacheDomains (x.2 μ))} := by
    rw [← game2_map_fst f A, PMF.toOuterMeasure_map_apply]
    rfl
  have hmap2 :
      (runWith IdealCipher.answer A (fun _ => [])).toOuterMeasure
          {x | DomainOverlap f (fun μ => cacheDomains (x.2 μ))} =
        (splitExperiment A).toOuterMeasure {x | DomainOverlap f x.2} := by
    rw [← splitExperiment_eq_answer A, PMF.toOuterMeasure_map_apply]
    rfl
  exact hmap1.trans hmap2

omit [DecidableEq V] in
/-- **Domain Separation Lemma** ([BonehShoup2023], Theorem 4.15, p. 161). For every function
`f : U → V` and every adversary `A`, the output distributions of the coalesced experiment
(Experiment 0) and of the split experiment (Experiment 1) are close on every event, within the
domain separation failure probability: the probability of `Z` (`DomainOverlap`) in the split
experiment. -/
theorem coalescedExperiment_closeTo_splitExperiment (f : U → V)
    (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    CloseTo (coalescedExperiment f A) ((splitExperiment A).map Prod.fst)
      ((splitExperiment A).toOuterMeasure {x | DomainOverlap f x.2}) := by
  classical
  have hclose := (identicalUntilBad_game1_game2 (U := U) (V := V) (X := X) f).closeTo_run A
    (fun _ => [], false)
  have hclose_fst := hclose.map Prod.fst
  rw [← coalescedExperiment_eq_game1 f A] at hclose_fst
  have hsplit_fst :
      (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).map Prod.fst =
        (splitExperiment A).map Prod.fst := by
    rw [← splitExperiment_eq_answer A, ← game2_map_fst f A]
    simp [PMF.map_comp, Function.comp_def]
  rw [hsplit_fst] at hclose_fst
  have hbad : (runWith (withBadFlag (game1Step f)) A (fun _ => [], false)).toOuterMeasure
      {x | FlagBad x.2} = (splitExperiment A).toOuterMeasure {x | DomainOverlap f x.2} := by
    rw [(identicalUntilBad_game1_game2 (U := U) (V := V) (X := X) f).bad_eq A
      (fun _ => [], false)]
    exact game2_bad_eq_failureProb f A
  simpa only [hbad] using hclose_fst

end Cslib.IdealCipher

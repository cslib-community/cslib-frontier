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
private lemma cacheDomains_cons {cache : Cache X} {e : X × X} :
    cacheDomains (e :: cache) =
      (insert e.1 (cacheDomains cache).1, insert e.2 (cacheDomains cache).2) := by
  ext z <;> simp [cacheDomains]

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma mem_cacheDomains_fst_iff {cache : Cache X} {x : X} :
    x ∈ (cacheDomains cache).1 ↔ cache.lookup x ≠ none := by
  simp [mem_cacheDomains_fst]

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma mem_cacheDomains_snd_iff {cache : Cache X} {y : X} :
    y ∈ (cacheDomains cache).2 ↔ invLookup cache y ≠ none := by
  simp [mem_cacheDomains_snd, invLookup_eq_none_iff]

omit [DecidableEq U] [Fintype U] [DecidableEq V] [Fintype V] [Nonempty X] in
/-- The flag condition of Game 2 on a miss: the entry recording the answer `c` to `q` has its input
in the recorded domain of `cache` or its output in the recorded range. -/
private lemma cachedAnswer_ne_none_or_not_mem_freshAnswers_iff {cache : Cache X}
    {q : PermQuery X} {c : X} :
    (cachedAnswer cache q ≠ none ∨ c ∉ freshAnswers cache q) ↔
      ((PermQuery.toCacheEntry ⟨q, c⟩).1 ∈ (cacheDomains cache).1 ∨
        (PermQuery.toCacheEntry ⟨q, c⟩).2 ∈ (cacheDomains cache).2) := by
  cases q <;> simp [cachedAnswer, freshAnswers, mem_cacheDomains_fst_iff,
    mem_cacheDomains_snd_iff, or_comm]

omit [Fintype U] [DecidableEq V] [Fintype V] [Fintype X] [Nonempty X] in
private lemma recordQueryDomain_of_cacheDomains_mem {uCache : U → Cache X}
    {q : IdealCipher.Query U X} {a : X}
    (hmem : PermQuery.toCacheEntry ⟨q.2, a⟩ ∈ uCache q.1) :
    recordQueryDomain (fun μ => cacheDomains (uCache μ)) q a =
      fun μ => cacheDomains (uCache μ) := by
  ext μ z <;> rcases eq_or_ne μ q.1 with rfl | hμ
  · simp only [recordQueryDomain, Function.update_self, Finset.mem_insert, or_iff_right_iff_imp]
    rintro rfl; exact mem_cacheDomains_fst.mpr ⟨_, hmem⟩
  · simp [recordQueryDomain, hμ]
  · simp only [recordQueryDomain, Function.update_self, Finset.mem_insert, or_iff_right_iff_imp]
    rintro rfl; exact mem_cacheDomains_snd.mpr ⟨_, hmem⟩
  · simp [recordQueryDomain, hμ]

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
  exact ⟨fun h μ hμ e he => h e ⟨μ, hμ, he⟩, fun h e ⟨μ, hμ, he⟩ => h μ hμ e he⟩

omit [DecidableEq U] [Fintype V] [Fintype X] [Nonempty X] in
/-- The recorded domain and range of a pooled cache are the unions over the fiber. -/
private lemma mem_cacheDomains_fiberCache {f : U → V} {uCache : U → Cache X} {ν : V} {x : X} :
    (x ∈ (cacheDomains (fiberCache f uCache ν)).1 ↔
        ∃ μ, f μ = ν ∧ x ∈ (cacheDomains (uCache μ)).1) ∧
      (x ∈ (cacheDomains (fiberCache f uCache ν)).2 ↔
        ∃ μ, f μ = ν ∧ x ∈ (cacheDomains (uCache μ)).2) := by
  simp only [mem_cacheDomains_fst, mem_cacheDomains_snd, mem_fiberCache_iff]
  exact ⟨⟨fun ⟨y, μ, hμ, h⟩ => ⟨μ, hμ, y, h⟩, fun ⟨μ, hμ, y, h⟩ => ⟨y, μ, hμ, h⟩⟩,
    ⟨fun ⟨y, μ, hμ, h⟩ => ⟨μ, hμ, y, h⟩, fun ⟨μ, hμ, y, h⟩ => ⟨y, μ, hμ, h⟩⟩⟩

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
  cases q <;> simp only [freshAnswers, mem_unusedRange_iff, invLookup_eq_none_iff,
    mem_unusedDomain_iff, lookup_eq_none_iff] at ha ⊢ <;>
    exact fun e he => ha e (mem_fiberCache_iff.mpr ⟨μ, rfl, he⟩)

omit [Fintype V] [DecidableEq X] [Fintype X] [Nonempty X] in
/-- Recording an entry under the key `μ` adds it to the pooled cache of the fiber of `f μ` and
leaves the other pooled caches unchanged, up to the order of entries. -/
private lemma mem_fiberCache_update_iff {f : U → V} {uCache : U → Cache X} {μ : U}
    {e e' : X × X} {ν : V} :
    e' ∈ fiberCache f (Function.update uCache μ (e :: uCache μ)) ν ↔
      e' ∈ Function.update (fiberCache f uCache) (f μ) (e :: fiberCache f uCache (f μ)) ν := by
  rw [mem_fiberCache_iff]
  by_cases hν : ν = f μ
  · subst hν
    rw [Function.update_self, List.mem_cons, mem_fiberCache_iff]
    constructor
    · rintro ⟨μ', hμ', he'⟩
      by_cases h : μ' = μ
      · rw [h, Function.update_self, List.mem_cons] at he'
        exact he'.imp_right fun he' => ⟨μ, rfl, he'⟩
      · exact Or.inr ⟨μ', hμ', by rwa [Function.update_of_ne h] at he'⟩
    · rintro (rfl | ⟨μ', hμ', he'⟩)
      · exact ⟨μ, rfl, by simp⟩
      · refine ⟨μ', hμ', ?_⟩
        by_cases h : μ' = μ
        · rw [h, Function.update_self]
          exact List.mem_cons_of_mem _ (h ▸ he')
        · rwa [Function.update_of_ne h]
  · rw [Function.update_of_ne hν, mem_fiberCache_iff]
    refine exists_congr fun μ' => and_congr_right fun hμ' => ?_
    rw [Function.update_of_ne fun h => hν (hμ'.symm.trans (congrArg f h))]

omit [Fintype V] [Nonempty X] in
private lemma isPartialBijection_fiber_update {f : U → V} {uCache : U → Cache X}
    (hbij : ∀ ν, IsPartialBijection (fiberCache f uCache ν))
    {μ : U} {q : PermQuery X}
    (hq : cachedAnswer (fiberCache f uCache (f μ)) q = none)
    {a : X} (ha : a ∈ freshAnswers (fiberCache f uCache (f μ)) q) (ν : V) :
    IsPartialBijection
      (fiberCache f (Function.update uCache μ (PermQuery.toCacheEntry ⟨q, a⟩ :: uCache μ)) ν) := by
  have h : IsPartialBijection (Function.update (fiberCache f uCache) (f μ)
      (PermQuery.toCacheEntry ⟨q, a⟩ :: fiberCache f uCache (f μ)) ν) := by
    rcases eq_or_ne ν (f μ) with rfl | hν
    · rw [Function.update_self]; exact (hbij _).cons_toCacheEntry hq ha
    · rw [Function.update_of_ne hν]; exact hbij ν
  obtain ⟨π, hπ⟩ := h
  exact ⟨π, fun e he => hπ e (mem_fiberCache_update_iff.mp he)⟩

omit [Nonempty X] in
private lemma complete_fiber_update_eq {f : U → V} {uCache : U → Cache X}
    {μ : U} {e : X × X} :
    IdealCipher.complete (fiberCache f (Function.update uCache μ (e :: uCache μ))) =
      IdealCipher.complete
        (Function.update (fiberCache f uCache) (f μ) (e :: fiberCache f uCache (f μ))) := by
  have hext (ν : V) : extPerms (fiberCache f (Function.update uCache μ (e :: uCache μ)) ν) =
      extPerms
        (Function.update (fiberCache f uCache) (f μ) (e :: fiberCache f uCache (f μ)) ν) := by
    ext π
    simp only [mem_extPerms_iff, AgreesWith, mem_fiberCache_update_iff]
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
    simp only [hqu, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem'
    exact hmem'.2.1 ▸ hst ν
  | none =>
    rw [hqu] at hmem'
    cases hqv : cachedAnswer (fiberCache f st.1 (f q.1)) q.2 with
    | some b =>
      simp only [hqv, PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem'
      exact hmem'.2.1 ▸ hst ν
    | none =>
      have hv_ne := (hst (f q.1)).freshAnswers_nonempty hqv
      have hu_ne : (freshAnswers (st.1 q.1) q.2).Nonempty :=
        hv_ne.mono freshAnswers_fiber_subset
      simp only [hqv, hu_ne, ↓reduceDIte, PMF.mem_support_bind_iff] at hmem'
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
  refine Eq.trans ?_ (IdealCipher.answer_complete (f q.1, q.2) (fiberCache f st.1) hst)
  simp only [withBadFlag, PMF.bind_map, Function.comp_def]
  dsimp only [game1Step]
  cases hqu : cachedAnswer (st.1 q.1) q.2 with
  | some a =>
    rw [answer_eq_pure_of_cachedAnswer_eq_some (q := (f q.1, q.2))
      (cachedAnswer_fiber_of_uCache hst hqu), PMF.pure_bind, PMF.pure_bind]
    rfl
  | none =>
    cases hqv : cachedAnswer (fiberCache f st.1 (f q.1)) q.2 with
    | some a =>
      rw [answer_eq_pure_of_cachedAnswer_eq_some (q := (f q.1, q.2)) hqv, PMF.pure_bind,
        PMF.pure_bind]
      rfl
    | none =>
      have hv_ne := (hst (f q.1)).freshAnswers_nonempty hqv
      have hu_ne : (freshAnswers (st.1 q.1) q.2).Nonempty :=
        hv_ne.mono freshAnswers_fiber_subset
      simp only [hu_ne, ↓reduceDIte]
      rw [answer_eq_map_of_cachedAnswer_eq_none (q := (f q.1, q.2)) hqv hv_ne, PMF.bind_map,
        Function.comp_def, ← Probability.PMF.unifOn_rehash_eq freshAnswers_fiber_subset hu_ne hv_ne]
      simp only [PMF.bind_bind]
      refine congr_arg _ (funext fun a => ?_)
      by_cases ha : a ∈ freshAnswers (fiberCache f st.1 (f q.1)) q.2 <;>
        simp [ha, hv_ne, PMF.bind_map, Function.comp_def, complete_fiber_update_eq]

private lemma coalescedExperiment_eq_game1 (f : U → V)
    (A : ProbOracleComp (IdealCipher.Spec U X) α) :
    coalescedExperiment f A =
      (runWith (withBadFlag (game1Step f)) A (fun _ => [], false)).map Prod.fst := by
  let target : (q : IdealCipher.Query U X) → StateT (V → Equiv.Perm X) PMF X :=
    fun q P => (PMF.pure (evalPerm (P (f q.1)) q.2)).map (·, P)
  have hsim := runWith_simulation_of_invariant (withBadFlag (game1Step f)) target
    (fun st => IdealCipher.complete (fiberCache f st.1))
    (fun st => ∀ ν, IsPartialBijection (fiberCache f st.1 ν))
    game1Step_preserve_isPartialBijection
    (fun q st hst => by simpa [target] using game1Step_simulate q st hst)
    A (fun _ => [], false)
    (fun ν => ⟨1, agreesWith_fiberCache_iff.mpr fun μ _ => agreesWith_nil 1⟩)
  have hfiber_nil : fiberCache f (fun _ : U => ([] : Cache X)) = fun _ => [] :=
    funext fun ν => by simp [fiberCache]
  have hconst (p : PMF (V → Equiv.Perm X)) (y : α) : p.map (fun _ => y) = PMF.pure y :=
    PMF.map_const p y
  have hfst := congrArg (PMF.map Prod.fst) hsim
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, hconst,
    hfiber_nil, IdealCipher.complete_nil] at hfst
  rw [coalescedExperiment]
  refine Eq.trans ?_ hfst.symm
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
      have hcomp := congrArg (PMF.map fun (a, πFam) =>
        (a, (πFam, recordQueryDomain (fun μ => cacheDomains (uCache μ)) q a)))
        (IdealCipher.answer_complete q uCache hcache)
      simp only [PMF.map_bind, PMF.monad_map_eq_map, PMF.map_comp, PMF.pure_map,
        Function.comp_def] at hcomp
      simp only [target, PMF.bind_map, Function.comp_def]
      rw [← hcomp]
      refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨a, u'⟩ hmem => ?_
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
          obtain ⟨_, _, heq'⟩ := hmem
          rcases Prod.mk.inj heq' with ⟨rfl, rfl⟩
          funext μ
          by_cases hμ : μ = q.1 <;> simp [recordQueryDomain, cacheDomains_cons, hμ]
      simp [PMF.map_comp, Function.comp_def, hdom])
    A (fun _ => []) (fun _ => isPartialBijection_nil)
  have hconst (p : PMF (U → Equiv.Perm X)) (y : α × QueryDomains U X) :
      p.map (fun _ => y) = PMF.pure y := PMF.map_const p y
  have hfst := congrArg (PMF.map fun (a, πFam, dom) => (a, dom)) hsim
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, hconst,
    IdealCipher.complete_nil] at hfst
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
  rw [splitExperiment]
  refine Eq.trans hfst ?_
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
      simp [PMF.pure_apply, PMF.map_apply]
    | none =>
      by_cases hu_ne : (freshAnswers (uCache q.1) q.2).Nonempty
      · rw [answer_eq_map_of_cachedAnswer_eq_none hqu hu_ne]
        simp only [hu_ne, ↓reduceDIte, PMF.map_comp, Function.comp_def, PMF.bind_apply,
          tsum_fintype]
        rw [PMF.map_apply, tsum_fintype]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hc : c ∈ freshAnswers (fiberCache f uCache (f q.1)) q.2
        · simp [hc]
        · simp [hc, apply_dite (DFunLike.coe · (a, uCache', false)), PMF.map_apply]
      · have hzero : (freshAnswers (fiberCache f uCache (f q.1)) q.2) = ∅ :=
          Finset.eq_empty_iff_forall_notMem.2 fun c hc => hu_ne ⟨c, freshAnswers_fiber_subset hc⟩
        simp [hu_ne, hzero, PMF.map_apply]

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
    · have hsub (μ : U) : (cacheDomains (st.1 μ)).1 ⊆ (cacheDomains (Function.update st.1 q.1
            (PermQuery.toCacheEntry ⟨q.2, c⟩ :: st.1 q.1) μ)).1 ∧
          (cacheDomains (st.1 μ)).2 ⊆ (cacheDomains (Function.update st.1 q.1
            (PermQuery.toCacheEntry ⟨q.2, c⟩ :: st.1 q.1) μ)).2 := by
        by_cases hμ : μ = q.1
        · rw [hμ, Function.update_self, cacheDomains_cons]
          exact ⟨Finset.subset_insert _ _, Finset.subset_insert _ _⟩
        · rw [Function.update_of_ne hμ]
          exact ⟨subset_rfl, subset_rfl⟩
      obtain ⟨μ₁, μ₂, hne, hf, hov⟩ := hiff.mp hprev
      have hdom_new : DomainOverlap f (fun μ => cacheDomains
          (Function.update st.1 q.1 (PermQuery.toCacheEntry ⟨q.2, c⟩ :: st.1 q.1) μ)) :=
        ⟨μ₁, μ₂, hne, hf, hov.imp
          (·.mono (Finset.inter_subset_inter (hsub μ₁).1 (hsub μ₂).1))
          (·.mono (Finset.inter_subset_inter (hsub μ₁).2 (hsub μ₂).2))⟩
      simp [FlagBad, hprev, hdom_new]
    · have hno_old : ¬DomainOverlap f (fun μ => cacheDomains (st.1 μ)) :=
        fun h => hprev (hiff.mpr h)
      simp only [FlagBad, Prod.map, id_eq, Bool.eq_false_iff.mpr hprev, Bool.false_or,
        ↓reduceIte]
      rw [decide_eq_true_eq, cachedAnswer_ne_none_or_not_mem_freshAnswers_iff,
        mem_cacheDomains_fiberCache.1, mem_cacheDomains_fiberCache.2]
      have hfresh := lookup_and_invLookup_toCacheEntry_eq_none hhit hc_mem
      have hx₀ : (PermQuery.toCacheEntry ⟨q.2, c⟩).1 ∉ (cacheDomains (st.1 q.1)).1 :=
        fun h => mem_cacheDomains_fst_iff.mp h hfresh.1
      have hy₀ : (PermQuery.toCacheEntry ⟨q.2, c⟩).2 ∉ (cacheDomains (st.1 q.1)).2 :=
        fun h => mem_cacheDomains_snd_iff.mp h hfresh.2
      generalize PermQuery.toCacheEntry ⟨q.2, c⟩ = e at hx₀ hy₀ ⊢
      constructor
      · rintro (⟨μ', hμ', hx⟩ | ⟨μ', hμ', hy⟩)
        · have hne : q.1 ≠ μ' := fun h => hx₀ (h ▸ hx)
          exact ⟨q.1, μ', hne, hμ'.symm, Or.inl ⟨e.1, Finset.mem_inter.mpr
            ⟨by simp [cacheDomains_cons], by simpa [Function.update_of_ne hne.symm] using hx⟩⟩⟩
        · have hne : q.1 ≠ μ' := fun h => hy₀ (h ▸ hy)
          exact ⟨q.1, μ', hne, hμ'.symm, Or.inr ⟨e.2, Finset.mem_inter.mpr
            ⟨by simp [cacheDomains_cons], by simpa [Function.update_of_ne hne.symm] using hy⟩⟩⟩
      · rintro ⟨μ₁, μ₂, hne, hf, hov⟩
        -- An overlap between the new cache of `q.1` and the cache of another key `μ'` of its
        -- fiber is either at the new entry, or an overlap that existed before.
        have hstep (μ' : U) (hne' : μ' ≠ q.1) (hf' : f μ' = f q.1)
            (hov' : (insert e.1 (cacheDomains (st.1 q.1)).1 ∩ (cacheDomains (st.1 μ')).1).Nonempty ∨
              (insert e.2 (cacheDomains (st.1 q.1)).2 ∩ (cacheDomains (st.1 μ')).2).Nonempty) :
            (∃ μ, f μ = f q.1 ∧ e.1 ∈ (cacheDomains (st.1 μ)).1) ∨
              ∃ μ, f μ = f q.1 ∧ e.2 ∈ (cacheDomains (st.1 μ)).2 := by
          rcases hov' with ⟨x, hx⟩ | ⟨y, hy⟩
          · rw [Finset.mem_inter, Finset.mem_insert] at hx
            rcases hx with ⟨rfl | hx_old, hxμ'⟩
            · exact Or.inl ⟨μ', hf', hxμ'⟩
            · exact (hno_old ⟨q.1, μ', hne'.symm, hf'.symm,
                Or.inl ⟨x, Finset.mem_inter.mpr ⟨hx_old, hxμ'⟩⟩⟩).elim
          · rw [Finset.mem_inter, Finset.mem_insert] at hy
            rcases hy with ⟨rfl | hy_old, hyμ'⟩
            · exact Or.inr ⟨μ', hf', hyμ'⟩
            · exact (hno_old ⟨q.1, μ', hne'.symm, hf'.symm,
                Or.inr ⟨y, Finset.mem_inter.mpr ⟨hy_old, hyμ'⟩⟩⟩).elim
        dsimp only at hov
        by_cases h1 : μ₁ = q.1
        · have h2 : μ₂ ≠ q.1 := by rw [← h1]; exact hne.symm
          rw [h1, Function.update_self, cacheDomains_cons, Function.update_of_ne h2] at hov
          exact hstep μ₂ h2 (by rw [← h1]; exact hf.symm) hov
        · by_cases h2 : μ₂ = q.1
          · rw [h2, Function.update_self, cacheDomains_cons, Function.update_of_ne h1,
              Finset.inter_comm (cacheDomains (st.1 μ₁)).1,
              Finset.inter_comm (cacheDomains (st.1 μ₁)).2] at hov
            exact hstep μ₁ h1 (by rw [← h2]; exact hf) hov
          · rw [Function.update_of_ne h1, Function.update_of_ne h2] at hov
            exact (hno_old ⟨μ₁, μ₂, hne, hf, hov⟩).elim

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
      (game2_bad_iff_domainOverlap_inv f)
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
  rw [hcongr, ← splitExperiment_eq_answer A, PMF.toOuterMeasure_map_apply,
    ← game2_map_fst f A, PMF.toOuterMeasure_map_apply]
  rfl

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
  have hclose_fst := ((identicalUntilBad_game1_game2 (U := U) (V := V) (X := X) f).closeTo_run A
    (fun _ => [], false)).map Prod.fst
  rw [← coalescedExperiment_eq_game1 f A] at hclose_fst
  have hsplit_fst :
      (runWith (withBadFlag (game2Step f)) A (fun _ => [], false)).map Prod.fst =
        (splitExperiment A).map Prod.fst := by
    rw [← splitExperiment_eq_answer A, ← game2_map_fst f A]
    simp [PMF.map_comp, Function.comp_def]
  rwa [hsplit_fst, (identicalUntilBad_game1_game2 (U := U) (V := V) (X := X) f).bad_eq A
    (fun _ => [], false), game2_bad_eq_failureProb f A] at hclose_fst

end Cslib.IdealCipher

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Memoize
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Computability.Probabilistic.Oracle.RunState
public import CslibFrontier.Crypto.Game.StatisticalIndistinguishability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Guarded association-list sampler caches for word-oracle simulations

Runs a single-channel `WordOracleComp` against an association-list cache (`memoize`) that draws
independent replies from a word sampler on valid queries (`valid query = true`) and answers invalid
queries with `[]` without modifying the cache.

## Main definitions

* `Cslib.Probability.cachedSamplerOracle`: closed stateful word-oracle handler memoizing a
  `ProbComp (List Bool)` sampler on valid queries and returning `[]` on invalid queries.
* `Cslib.Probability.cachedDistOracle`: distribution-level (`PMF`) counterpart of
  `cachedSamplerOracle`.

## Main results

* `Cslib.Probability.eval_cachedSamplerOracle`: `ProbComp.eval` identifies `cachedSamplerOracle`
  with `cachedDistOracle`.
* `Cslib.Probability.cachedSamplerOracle_support`: per-call cache length growth (`≤ +1`) and key
  validity preservation.
* `Cslib.Probability.valid_of_mem_runState_cachedSamplerOracle`: every key stored in the final
  cache of a run from `[]` satisfies `valid`.
* `Cslib.Probability.isPPTOn_runState_cachedSamplerOracle`: whole-run uniform strict-PPT
  certificate for running an `IsOraclePPTOn` program against `cachedSamplerOracle`.
* `Cslib.Probability.closeTo_cachedDistOracle`: per-call statistical distance preservation for
  `cachedDistOracle`.
-/

public section

open Cslib Turing.MultiTapeTM
open scoped ENNReal

namespace Cslib.Probability

/-- Memoize independent draws from `sampleReply` on valid word queries, rejecting malformed words
with `[]` without modifying the cache. -/
@[expose] noncomputable def cachedSamplerOracle (valid : List Bool → Bool)
    (sampleReply : ProbComp (List Bool)) (query : List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) := fun cache =>
  if valid query then memoize (fun _ => sampleReply) query cache
  else pure ([], cache)

/-- Distribution-level (`PMF`) counterpart of `cachedSamplerOracle`. -/
@[expose] noncomputable def cachedDistOracle (valid : List Bool → Bool) (dist : PMF (List Bool))
    (query : List Bool) : StateT (List (List Bool × List Bool)) PMF (List Bool) := fun cache =>
  if valid query then memoize (fun _ => dist) query cache
  else PMF.pure ([], cache)

/-- Evaluating `cachedSamplerOracle` yields `cachedDistOracle` on `ProbComp.eval sampleReply`. -/
theorem eval_cachedSamplerOracle (valid : List Bool → Bool)
    (sampleReply : ProbComp (List Bool)) (q : List Bool) (cache : List (List Bool × List Bool)) :
    ProbComp.eval (cachedSamplerOracle valid sampleReply q cache) =
      cachedDistOracle valid (ProbComp.eval sampleReply) q cache := by
  by_cases hv : valid q = true
  · simp [cachedSamplerOracle, cachedDistOracle, hv, ProbComp.eval_memoize]
  · simp [cachedSamplerOracle, cachedDistOracle, hv, ProbComp.eval_pure]

/-- A call to `cachedSamplerOracle` adds at most one entry and preserves validity of cached keys. -/
theorem cachedSamplerOracle_support {valid : List Bool → Bool}
    {sampleReply : ProbComp (List Bool)} {q : List Bool}
    {cache : List (List Bool × List Bool)} {res : List Bool × List (List Bool × List Bool)}
    (hres : res ∈ (ProbComp.eval (cachedSamplerOracle valid sampleReply q cache)).support) :
    res.2.length ≤ cache.length + 1 ∧
      ((∀ entry ∈ cache, valid entry.1 = true) → ∀ entry ∈ res.2, valid entry.1 = true) := by
  by_cases hvalid : valid q = true
  · simp only [cachedSamplerOracle, ite_eq_left hvalid, ProbComp.eval_memoize] at hres
    rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hres with ⟨_, hsame⟩ | ⟨_, _, hnext⟩
    · rw [hsame]
      exact ⟨Nat.le_succ _, id⟩
    · rw [hnext]
      refine ⟨by simp, fun hcache entry hentry => ?_⟩
      rcases List.mem_cons.mp hentry with rfl | hmem
      · exact hvalid
      · exact hcache entry hmem
  · simp only [cachedSamplerOracle, ite_eq_right hvalid, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hres
    obtain rfl := hres
    exact ⟨Nat.le_succ _, id⟩

/-- Every key recorded in the final cache of a `runState` execution against `cachedSamplerOracle`
from `[]` satisfies `valid`. -/
theorem valid_of_mem_runState_cachedSamplerOracle {α : Type}
    (valid : List Bool → Bool) (sampleReply : ProbComp (List Bool))
    (P : WordOracleComp Unit α) {res : α × List (List Bool × List Bool)}
    (hres : res ∈ (ProbComp.eval
      ((P.runState fun req => cachedSamplerOracle valid sampleReply req.2).run [])).support) :
    ∀ entry ∈ res.2, valid entry.1 = true := by
  rw [ProbOracleComp.eval_runState] at hres
  exact ProbOracleComp.runWith_invariant
    (State := List (List Bool × List Bool))
    (fun (req : Unit × List Bool) (cache : List (List Bool × List Bool)) =>
      ProbComp.eval (cachedSamplerOracle valid sampleReply req.2 cache))
    (fun cache => ∀ entry ∈ cache, valid entry.1 = true)
    (fun _ cache hcache _ _ hstep => (cachedSamplerOracle_support hstep).2 hcache)
    P [] (by simp) res.1 res.2 hres

/-- Running a strict oracle-PPT word program against `cachedSamplerOracle` from `[]` is uniform
strict PPT when `prepare` and `valid` are computable in polynomial time and `sampleReply` is
uniform strict PPT. -/
theorem isPPTOn_runState_cachedSamplerOracle {Caller α β : Type}
    {input : Caller ↪ List Bool} {source : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp Unit β} {prepare : Caller → α}
    {valid : Caller → List Bool → Bool} {sampleReply : Caller → ProbComp (List Bool)}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hvalid : ComputableInPolyTime (fun p : Caller × List Bool => valid p.1 p.2)
      (encPair input encBits) encBool)
    (hsample : IsPPTOn input encBits sampleReply) :
    IsPPTOn input (encPair output (encMemoCache encBits encBits)) (fun a =>
      ((program (prepare a)).runState fun req =>
        cachedSamplerOracle (valid a) (sampleReply a) req.2).run []) := by
  obtain ⟨cS, dS, hlenS⟩ := hsample.length_le
  let maxVal (a : Caller) : ℕ := cS * ((input a).length + 1) ^ dS
  have hraw : ComputableInPolyTime (fun a : Caller => input a) input encBits :=
    ComputableInPolyTime.of_enc_eq (ComputableInPolyTime.id' (encIn := input)) fun _ => rfl
  have hmaxVal : ComputableInPolyTime maxVal input encUnary := by
    dsimp only [maxVal]
    fun_prop
  refine hprogram.isPPTOn_runState (operationEncoding := encFinEnum Unit)
    (resources := fun a query => 4 * query.length + 2 * maxVal a + 3)
    hprepare ?_ (.const [])
    (fun a cache => ∀ entry ∈ cache, entry.2.length ≤ maxVal a) (by simp) (by fun_prop) ?_
  · let cacheEncoding := encMemoCache encBits encBits
    let requestEncoding := encPair (encFinEnum Unit) encBits
    let hcaller := ComputableInPolyTime.fst input (encPair requestEncoding cacheEncoding)
    let hrest := ComputableInPolyTime.snd input (encPair requestEncoding cacheEncoding)
    unfold cachedSamplerOracle
    exact IsPPTOn.cond
      (hvalid.comp (hcaller.prod hrest.fst'.snd'))
      (IsPPTOn.memoize (compute := fun p _ => sampleReply p.1)
        (hsample.preprocess hcaller) hrest.fst'.snd' hrest.snd')
      (((ComputableInPolyTime.const ([] : List Bool)).prod hrest.snd').isPPTOn)
  · intro a request cache hcache result hresult
    by_cases hquery : valid a request.2 = true
    · simp only [cachedSamplerOracle, ite_eq_left hquery, ProbComp.eval_memoize] at hresult
      obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le encBits encBits
        (fun _ => ProbComp.eval (sampleReply a)) request.2 cache (maxVal a) hcache
        (fun value hvalue => by simpa only [encBits_apply] using hlenS a value hvalue)
        result hresult
      exact ⟨hcache', by simpa only [encBits_apply] using hreply.trans (by omega),
        by simpa only [encBits_apply, Nat.add_assoc] using hgrowth⟩
    · simp only [cachedSamplerOracle, ite_eq_right hquery, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨hcache, Nat.zero_le _, Nat.le_add_right _ _⟩

/-- If `CloseTo μ ν ε`, one call to `cachedDistOracle` preserves `CloseTo` with error `ε`. -/
theorem closeTo_cachedDistOracle (valid : List Bool → Bool) {μ ν : PMF (List Bool)}
    {ε : ℝ≥0∞} (hclose : CloseTo μ ν ε) (q : List Bool) (cache : List (List Bool × List Bool)) :
    CloseTo (cachedDistOracle valid μ q cache) (cachedDistOracle valid ν q cache) ε := by
  unfold cachedDistOracle
  split_ifs with hv
  · unfold Cslib.memoize
    cases cache.lookup q with
    | some v => exact (CloseTo.refl _).mono (zero_le : 0 ≤ ε)
    | none => exact hclose.map fun v => (v, (q, v) :: cache)
  · exact (CloseTo.refl _).mono (zero_le : 0 ≤ ε)

end Cslib.Probability

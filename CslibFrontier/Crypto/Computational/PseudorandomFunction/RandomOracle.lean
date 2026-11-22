/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Computability.Probabilistic.Memoize
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Oracle.RunState
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString

/-!
# An executable finite-list oracle for the PRF ideal game

Valid queries are memoized as ordinary words. Malformed queries receive the empty word and retain
the cache. Injective key representations and the shared eager/lazy theorem identify this program
with the length-preserving ideal PRF game `prfIdealGame id id` for every randomized adaptive
adversary.

## Main definitions

* `Cslib.Crypto.cachedRandomFunctionOracle`: a list cache with fair-bit sampling on misses.

## Main results

* `Cslib.Crypto.prfIdealGame_eq_cached`: exact equality of the eager and cached experiments.
* `Cslib.Crypto.isPPT_prfIdealGame`: a strict PPT realization for every oracle-PPT adversary.
* `Cslib.Crypto.isPPTOn_runState_cachedRandomFunctionOracle`: the strict PPT run retaining its
  cache, for a polynomial-time validity test and output-width schedule.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].

Adapts Crypto/Computational/PseudorandomFunction/RandomOracle.lean on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared typed interpreter.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- Memoize uniform `outLen`-bit samples on valid queries, rejecting malformed words without
altering the cache. -/
noncomputable def cachedRandomFunctionOracle (valid : List Bool → Bool) (outLen : ℕ)
    (query : List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) := fun cache =>
  if valid query then memoize (fun _ => BitString.sampleList outLen) query cache
  else pure ([], cache)

/-- A call either leaves the cache untouched or prepends the reply to a fresh valid query. -/
theorem cachedRandomFunctionOracle_cache_of_mem_support {valid : List Bool → Bool}
    {outLen : ℕ} {query : List Bool} {cache : List (List Bool × List Bool)}
    {result : List Bool × List (List Bool × List Bool)}
    (hresult : result ∈
      (ProbComp.eval (cachedRandomFunctionOracle valid outLen query cache)).support) :
    result.2 = cache ∨
      valid query = true ∧ cache.lookup query = none ∧ result.2 = (query, result.1) :: cache := by
  by_cases hvalid : valid query = true
  · simp only [cachedRandomFunctionOracle, ite_eq_left hvalid, ProbComp.eval_memoize] at hresult
    rcases (RandomOracle.mem_support_memoize_iff _ _ _ _).mp hresult with
      ⟨_, hsame⟩ | ⟨hfresh, _, hnew⟩
    · exact Or.inl hsame
    · exact Or.inr ⟨hvalid, hfresh, hnew⟩
  · simp only [cachedRandomFunctionOracle, ite_eq_right hvalid, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    exact Or.inl (congrArg Prod.snd hresult)

open Turing.MultiTapeTM in
/-- Each cached call charges the validity test, sampling, query and complete input/output cache. -/
@[fun_prop]
theorem isPPTOn_cachedRandomFunctionOracle {α : Type} {input : α ↪ List Bool}
    {valid : α → List Bool → Bool} {outLen : α → ℕ} {query : α → List Bool}
    {cache : α → List (List Bool × List Bool)}
    (hvalid : ComputableInPolyTime (fun a => valid a (query a)) input encBool)
    (houtLen : ComputableInPolyTime outLen input encUnary)
    (hquery : ComputableInPolyTime query input encBits)
    (hcache : ComputableInPolyTime cache input (encMemoCache encBits encBits)) :
    IsPPTOn input (encPair encBits (encMemoCache encBits encBits))
      (fun a => cachedRandomFunctionOracle (valid a) (outLen a) (query a) (cache a)) := by
  unfold cachedRandomFunctionOracle
  exact IsPPTOn.cond hvalid
    (IsPPTOn.memoize (compute := fun a _ => BitString.sampleList (outLen a))
      houtLen.sampleList hquery hcache)
    (((ComputableInPolyTime.const ([] : List Bool)).prod hcache).isPPTOn)

open Turing.MultiTapeTM in
/-- Run a strict oracle-PPT program against the guarded random-function cache starting empty.
The validity test and sampled reply width are polynomial-time in the encoded caller and query.
The final cache is part of the certified output. -/
theorem isPPTOn_runState_cachedRandomFunctionOracle {Caller α β : Type}
    {input : Caller ↪ List Bool} {source : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp Unit β} {prepare : Caller → α}
    {valid : Caller → List Bool → Bool} {outLen : Caller → ℕ}
    (hprogram : IsOraclePPTOn source output program)
    (hprepare : ComputableInPolyTime prepare input source)
    (hvalid : ComputableInPolyTime (fun p => valid p.1 p.2) (encPair input encBits) encBool)
    (houtLen : ComputableInPolyTime outLen input encUnary) :
    IsPPTOn input (encPair output (encMemoCache encBits encBits)) (fun a =>
      ((program (prepare a)).runState fun req =>
        cachedRandomFunctionOracle (valid a) (outLen a) req.2).run []) := by
  refine hprogram.isPPTOn_runState (operationEncoding := encFinEnum Unit)
    (resources := fun a query => 4 * query.length + 2 * outLen a + 3)
    hprepare ?_ (.const [])
    (fun a cache => ∀ entry ∈ cache, entry.2.length ≤ outLen a) (by simp) (by fun_prop) ?_
  · let cacheEncoding := encMemoCache encBits encBits
    let requestEncoding := encPair (encFinEnum Unit) encBits
    let hcaller := ComputableInPolyTime.fst input (encPair requestEncoding cacheEncoding)
    let hrest := ComputableInPolyTime.snd input (encPair requestEncoding cacheEncoding)
    exact isPPTOn_cachedRandomFunctionOracle
      (valid := fun (p : Caller × (Unit × List Bool) × List (List Bool × List Bool)) => valid p.1)
      (hvalid.comp (hcaller.prod hrest.fst'.snd')) (houtLen.comp hcaller)
      hrest.fst'.snd' hrest.snd'
  · intro a request cache hcache result hresult
    by_cases hquery : valid a request.2 = true
    · simp only [cachedRandomFunctionOracle, ite_eq_left hquery, ProbComp.eval_memoize] at hresult
      obtain ⟨hreply, hcache', hgrowth⟩ := memoize_call_size_le encBits encBits
        (fun _ => ProbComp.eval (BitString.sampleList (outLen a))) request.2 cache (outLen a)
        hcache (fun value hvalue => by
          rw [BitString.eval_sampleList] at hvalue
          exact (BitString.length_of_mem_support_uniformList hvalue).le) result hresult
      exact ⟨hcache', by simpa only [encBits_apply] using hreply.trans (by omega),
        by simpa only [encBits_apply, Nat.add_assoc] using hgrowth⟩
    · simp only [cachedRandomFunctionOracle, ite_eq_right hquery, ProbComp.eval_pure,
        PMF.mem_support_pure_iff] at hresult
      subst result
      exact ⟨hcache, Nat.zero_le _, Nat.le_add_right _ _⟩

/-- An executable list cache realizes the ideal experiment, preserving repeated-query
consistency and independent private randomness under arbitrary adaptive interaction. -/
theorem prfIdealGame_eq_cached (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame id id adversary n) =
      ProbComp.eval (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun request => cachedRandomFunctionOracle (·.length == n) n request.2))
            (adversary n [])).run []) := by
  let adapter := fun query : List Bool => if query.length = n then
    (ProbOracleComp.query (BitString.ofList n query) :
      ProbOracleComp (fun _ : BitString n => List Bool) (List Bool))
    else pure []
  have h := RandomOracle.interpret_prob_eq_memoize_map
    (Turing.MultiTapeTM.encBitString n) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString n)) (fun _ => BitString.uniformList n)
    (fun _ => rfl)
    (ProbOracleComp.simulate (fun request : Unit × List Bool => adapter request.2) (adversary n []))
  have hstep (query : List Bool) : OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun key => memoize (fun _ => BitString.uniformList n) (List.ofFn key)))
          (adapter query) =
        fun cache => ProbComp.eval (cachedRandomFunctionOracle (·.length == n) n query cache) := by
    funext cache
    by_cases hquery : query.length = n
    · simp [adapter, cachedRandomFunctionOracle, hquery, BitString.ofFn_ofList hquery,
        ProbComp.eval_memoize, BitString.eval_sampleList]
    · simp only [adapter, cachedRandomFunctionOracle, beq_iff_eq, hquery, ↓reduceIte,
        OracleComp.interpret_pure, ProbComp.eval_pure]
      rfl
  have heager (table : BitString n → BitString n) (query : List Bool) : OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifOracle (fun key => PMF.pure (List.ofFn (table key))))
        (adapter query) = PMF.pure (randomFunctionOracle n table query) := by
    by_cases hquery : query.length = n <;> simp [adapter, randomFunctionOracle, hquery]
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret]
  simpa only [prfIdealGame, id_eq, ProbOracleComp.run, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, PMF.pi_uniformOfFintype,
    ProbOracleComp.interpret_simulate,
    Turing.MultiTapeTM.encBitString_apply, hstep, heager, PMF.monad_bind_eq_bind] using h

open Turing.MultiTapeTM in
/-- The ideal experiment has a strict PPT realization through its lazy cache. This does not
construct the exponentially large eager table; the entire adaptive interaction is certified. -/
theorem isPPT_prfIdealGame {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsPPT encBool (fun n _ => prfIdealGame id id adversary n) := by
  have hrun := isPPTOn_runState_cachedRandomFunctionOracle (input := encPair encUnary encBits)
    (prepare := fun p => (p.1, [])) (valid := fun p q => q.length == p.1) (outLen := Prod.fst)
    hadversary.on (by fun_prop) (by fun_prop) (ComputableInPolyTime.fst _ _)
  exact ((hrun.map (ComputableInPolyTime.fst _ _)).isPPT).congr
    (fun n _ => (prfIdealGame_eq_cached adversary n).symm)

end Cslib.Crypto

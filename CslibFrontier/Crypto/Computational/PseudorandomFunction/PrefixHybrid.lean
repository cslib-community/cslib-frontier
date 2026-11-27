/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Domain
public import CslibFrontier.Computability.Probabilistic.Memoize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.PairCapture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Prefix hybrids for word PRFs

A query uses a memoized uniform label at the chosen prefix length and evaluates the remaining
suffix from that label. A query shorter than the cut uses its own label. These experiments are
shared by the binary GGM tree and the arbitrary block-width cascade. At cut zero the label is
the real key. Once the cut covers the domain, labels are the ideal oracle replies if evaluation
on an empty suffix returns the label itself.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Answer a valid query by sampling a label once at its prefix and evaluating the suffix.
Invalid queries return the empty word without touching the cache. -/
@[expose]
noncomputable def prefixHybridOracle (valid : List Bool → Bool)
    (family : List Bool → List Bool → List Bool) (n cut : ℕ) (query : List Bool) :
    StateT (List (List Bool × List Bool)) ProbComp (List Bool) := fun cache =>
  if valid query then do
    let (seed, cache') ← memoize (fun _ => BitString.sampleList n) (query.take cut) cache
    return (family seed (query.drop cut), cache')
  else pure ([], cache)

/-- Run a distinguisher with a prefix hybrid from an empty cache. The cut counts bits. -/
@[expose]
noncomputable def prefixHybridGame (valid : ℕ → List Bool → Bool)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher)
    (n cut : ℕ) : ProbComp Bool :=
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (fun request => prefixHybridOracle (valid n) family n cut request.2)) (adversary n [])).run []

/-- At cut zero every valid query shares the uniform root key of the real game. -/
theorem eval_prefixHybridGame_zero (valid : ℕ → List Bool → Bool)
    (family : List Bool → List Bool → List Bool) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prefixHybridGame valid family adversary n 0) =
      ProbComp.eval (prfRealGameOn valid family adversary n) := by
  let root (cache : List (List Bool × List Bool)) :=
    (cache.lookup []).elim (BitString.uniformList n) PMF.pure
  have h := ProbOracleComp.runWith_simulation
    (fun request cache => ProbComp.eval (prefixHybridOracle (valid n) family n 0 request.2 cache))
    (fun request seed =>
      (PMF.pure (prfOracleOn (valid n) family seed request.2)).map (·, seed))
    root (fun request cache => by
      cases hquery : valid n request.2 <;> cases hcache : cache.lookup [] <;>
        simp [prefixHybridOracle, memoize, root, hquery, hcache, BitString.eval_sampleList,
          prfOracleOn, PMF.map, Function.comp_def]) (adversary n []) []
  simp only [funext (ProbOracleComp.runWith_readOnly _ _)] at h
  simpa [prefixHybridGame, prfRealGameOn, ProbOracleComp.run,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_interpret,
    BitString.eval_sampleList, root, PMF.map, Function.comp_def, OracleComp.evalWith_eq_interpret]
    using congrArg (PMF.map Prod.fst) h

/-- Once the cut covers all valid queries, a cached label is the reply itself. -/
theorem prefixHybridOracle_eq_cachedRandomFunctionOracle
    {valid : List Bool → Bool} {family : List Bool → List Bool → List Bool} {n cut : ℕ}
    (hcut : ∀ query, valid query = true → query.length ≤ cut)
    (hnil : ∀ seed, family seed [] = seed) :
    prefixHybridOracle valid family n cut = cachedRandomFunctionOracle valid n := by
  funext query cache
  cases hquery : valid query
  · simp [prefixHybridOracle, cachedSamplerOracle, hquery]
  · simp [prefixHybridOracle, cachedSamplerOracle, hquery,
      List.take_of_length_le (hcut query hquery),
      List.drop_eq_nil_of_le (hcut query hquery), hnil]

/-- Each valid query adds at most one prefix label; malformed queries leave the cache unchanged.
The reply bound also holds on cache hits when every stored label has length at most `n`. -/
theorem prefixHybridOracle_bounds {valid : List Bool → Bool}
    {family : List Bool → List Bool → List Bool} {n cut : ℕ}
    (hEval : ∀ seed suffix, seed.length ≤ n → (family seed suffix).length ≤ n)
    {query : List Bool} {cache : List (List Bool × List Bool)}
    (hcache : ∀ entry ∈ cache, entry.2.length ≤ n)
    {result : List Bool × List (List Bool × List Bool)}
    (hresult : result ∈
      (ProbComp.eval (prefixHybridOracle valid family n cut query cache)).support) :
    (∀ entry ∈ result.2, entry.2.length ≤ n) ∧ result.1.length ≤ n ∧
      (encMemoCache encBits encBits result.2).length ≤
        (encMemoCache encBits encBits cache).length + 4 * query.length + 2 * n + 3 := by
  cases hvalid : valid query
  · simp only [prefixHybridOracle, hvalid, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
      PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨hcache, by simp, by dsimp; lia⟩
  · simp only [prefixHybridOracle, hvalid, ↓reduceIte, ProbComp.eval_bind,
      PMF.mem_support_bind_iff, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    obtain ⟨⟨seed, cache'⟩, hseed, rfl⟩ := hresult
    obtain ⟨hwidth, hcache', hgrowth⟩ := memoize_call_size_le encBits encBits
      (fun _ : List Bool => BitString.uniformList n) (query.take cut) cache n hcache
      (fun _ hvalue => (BitString.length_of_mem_support_uniformList hvalue).le)
      (seed, cache')
      (by simpa only [ProbComp.eval_memoize, BitString.eval_sampleList] using hseed)
    have hprefix : (query.take cut).length ≤ query.length := by simp
    refine ⟨hcache', hEval _ _ hwidth, ?_⟩
    simp only [encBits_apply] at hgrowth
    dsimp
    lia

/-- Certify one hybrid oracle call with computed parameters, query and complete cache. -/
@[fun_prop]
theorem isPPTOn_prefixHybridOracle {α : Type} {input : α ↪ List Bool}
    {valid : α → List Bool → Bool} {family : List Bool → List Bool → List Bool}
    {n cut : α → ℕ} {query : α → List Bool} {cache : α → List (List Bool × List Bool)}
    (hValid : ComputableInPolyTime (fun a => valid a (query a)) input encBool)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hN : ComputableInPolyTime n input encUnary)
    (hCut : ComputableInPolyTime cut input encUnary)
    (hQuery : ComputableInPolyTime query input encBits)
    (hCache : ComputableInPolyTime cache input (encMemoCache encBits encBits)) :
    IsPPTOn input (encPair encBits (encMemoCache encBits encBits)) (fun a =>
      prefixHybridOracle (valid a) family (n a) (cut a) (query a) (cache a)) := by
  unfold prefixHybridOracle
  refine IsPPTOn.cond hValid ?_ (((ComputableInPolyTime.const []).prod hCache).isPPTOn)
  have hLabel := IsPPTOn.memoize (compute := fun a _ => BitString.sampleList (n a))
    hN.sampleList
    (show ComputableInPolyTime (fun a => (query a).take (cut a)) input encBits by fun_prop)
    hCache
  exact hLabel.map_pair (second := fun p => (family p.2.1 ((query p.1).drop (cut p.1)), p.2.2))
    (by fun_prop)

/-- The complete adaptive hybrid is strict PPT, with the security parameter and cut in unary.
The output-length bound accounts for all oracle replies and for each stored prefix and label. -/
theorem isPPTOn_prefixHybridGame {valid : ℕ → List Bool → Bool}
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher}
    (hValid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hLength : ∀ seed suffix, (family seed suffix).length ≤ seed.length)
    (hAdversary : IsOraclePPT encBool adversary) :
    IsPPTOn (encPair encUnary encUnary) encBool
      (fun p => prefixHybridGame valid family adversary p.1 p.2) := by
  let cacheEncoding := encMemoCache encBits encBits
  have hRun : IsPPTOn (encPair encUnary encUnary) (encPair encBool cacheEncoding)
      (fun p : ℕ × ℕ => (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun request => prefixHybridOracle (valid p.1) family p.1 p.2 request.2))
          (adversary p.1 [])).run []) := by
    apply hAdversary.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
      (prepare := fun p : ℕ × ℕ => (p.1, []))
      (resources := fun p query => 4 * query.length + 2 * p.1 + 3)
      (by fun_prop) (by
        dsimp only [cacheEncoding]
        apply isPPTOn_prefixHybridOracle _ hEval <;> fun_prop)
      (.const []) (fun p cache => ∀ entry ∈ cache, entry.2.length ≤ p.1) (by simp) (by fun_prop)
    intro p request cache hCache result hResult
    obtain ⟨hCache', hReply, hGrowth⟩ :=
      prefixHybridOracle_bounds (fun seed suffix hs => (hLength seed suffix).trans hs)
        hCache hResult
    exact ⟨hCache', by lia, by lia⟩
  exact hRun.map (ComputableInPolyTime.fst _ _)

end Cslib.Crypto

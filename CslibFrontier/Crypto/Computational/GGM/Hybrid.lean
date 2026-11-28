/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GGM.Evaluation
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.PrefixHybrid
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.RandomOracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The GGM prefix hybrids

At level `depth`, sample an independent label for each newly queried prefix of that length.
Remember it for later queries with the same prefix, and evaluate the remaining suffix using the
generator. Malformed queries receive the empty word, as in the PRF games.

The cache is an ordinary list. One call preserves a label-width invariant and adds at most one
entry. The shared stateful interpreter certifies the entire adaptive game, including copying,
sampling, replies and growing storage. This module identifies the endpoint games; adjacent-hybrid
security requires a further reduction.

## Main definitions

* `Cslib.Crypto.GGM.frontierOracle`: memoized prefix labels followed by tree evaluation.
* `Cslib.Crypto.GGM.hybridGame`: the complete adaptive prefix experiment.

## Main results

* `Cslib.Crypto.GGM.frontierOracle_bounds`: bounds label widths and the cache-encoding growth
  per query.
* `Cslib.Crypto.GGM.hybridGame_zero`, `.hybridGame_self`: exact real and ideal endpoints.
* `Cslib.Crypto.GGM.isPPTOn_hybridGame`: uniform strict PPT for the complete experiment.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3, the algorithms `A_i` in the proof of Theorem 3.

Adapts Crypto/Computational/GGM/Hybrid.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared typed interpreter.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability Turing.MultiTapeTM

/-- A finite collection of queried prefixes and their sampled labels. -/
abbrev Cache := List (List Bool × List Bool)

/-- Charge every stored prefix and label, including list and pair delimiters. -/
def cacheEncoding : Cache ↪ List Bool := encMemoCache encBits encBits

/-- Answer from a cached random label at the chosen level, followed by ordinary tree evaluation. -/
noncomputable def frontierOracle (generator : List Bool → List Bool) (n depth : ℕ)
    (query : List Bool) : StateT Cache ProbComp (List Bool) :=
  prefixHybridOracle (·.length == n) (eval generator) n depth query

/-- The adaptive hybrid game starts with an empty prefix cache. -/
noncomputable def hybridGame (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n depth : ℕ) : ProbComp Bool :=
  prefixHybridGame (fun n query => query.length == n) (eval generator) adversary n depth

/-- At level zero, all valid queries share one root label. Sampling that label on demand agrees
with choosing the key at the start of the real PRF game, even if there are no valid queries. -/
theorem hybridGame_zero (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n : ℕ) :
    ProbComp.eval (hybridGame generator adversary n 0) =
      ProbComp.eval (prfRealGame id (eval generator) adversary n) := by
  rw [hybridGame, ← eval_prfRealGameOn_length_eq id]
  exact eval_prefixHybridGame_zero (fun n query => query.length == n) (eval generator) adversary n

/-- The final level caches full query answers directly. There is no suffix left to evaluate. -/
theorem frontierOracle_self (generator : List Bool → List Bool) (n : ℕ) :
    frontierOracle generator n n = cachedRandomFunctionOracle (·.length == n) n := by
  apply prefixHybridOracle_eq_cachedRandomFunctionOracle
  · intro query hquery
    exact (beq_iff_eq.mp hquery).le
  · intro seed
    rfl

/-- At the final level, the prefix hybrid is exactly the ideal PRF game. -/
theorem hybridGame_self (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n : ℕ) :
    ProbComp.eval (hybridGame generator adversary n n) =
      ProbComp.eval (prfIdealGame id id adversary n) := by
  rw [← eval_prfIdealGameOn_length_eq]
  have hOracle := frontierOracle_self generator n
  unfold frontierOracle at hOracle
  simp only [hybridGame, prefixHybridGame, prfIdealGameOn, id_eq, hOracle]

/-- Each call preserves label widths and adds at most one encoded entry. Key lengths and duplicate
cache keys are unrestricted; only cached label widths are constrained. -/
theorem frontierOracle_bounds (generator : List Bool → List Bool) (n depth : ℕ)
    (query : List Bool) (cache : Cache) (hcache : ∀ entry ∈ cache, entry.2.length ≤ n)
    (result : List Bool × Cache)
    (hresult : result ∈ (ProbComp.eval (frontierOracle generator n depth query cache)).support) :
    (∀ entry ∈ result.2, entry.2.length ≤ n) ∧ result.1.length ≤ n ∧
      (cacheEncoding result.2).length ≤
        (cacheEncoding cache).length + 4 * query.length + 2 * n + 3 := by
  exact prefixHybridOracle_bounds (fun seed suffix hs => (length_eval_le _ seed suffix).trans hs)
    hcache hresult

/-- Certify a prefix call written with computed parameters, query and full cache. -/
@[fun_prop]
theorem isPPTOn_frontierOracle {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {parameter depth : α → ℕ}
    {query : α → List Bool} {cache : α → Cache}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hparameter : ComputableInPolyTime parameter input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hquery : ComputableInPolyTime query input encBits)
    (hcache : ComputableInPolyTime cache input cacheEncoding) :
    IsPPTOn input (encPair encBits cacheEncoding)
      (fun a => frontierOracle generator (parameter a) (depth a) (query a) (cache a)) := by
  unfold frontierOracle cacheEncoding
  exact isPPTOn_prefixHybridOracle (by fun_prop) (computableInPolyTime_eval hgenerator)
    hparameter hdepth hquery hcache

/-- A uniform adversary's complete adaptive prefix game is strict PPT, uniformly over the chosen
level. The local invariant accounts for every reply and all added encoded storage. -/
theorem isPPTOn_hybridGame {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn (encPair encUnary encUnary) encBool
      (fun pair => hybridGame generator adversary pair.1 pair.2) := by
  exact isPPTOn_prefixHybridGame (by fun_prop) (computableInPolyTime_eval hgenerator)
    (length_eval_le generator) hadversary

end Cslib.Crypto.GGM

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Domain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# An executable finite-list oracle for the PRF ideal game

Valid queries are memoized as ordinary words via `Cslib.Probability.cachedSamplerOracle`. Malformed
queries receive the empty word and retain the cache. Injective key representations and the shared
eager/lazy theorem identify this program with the length-preserving ideal PRF game
`prfIdealGame id id` for every randomized adaptive adversary.

## Main results

* `Cslib.Crypto.prfIdealGame_eq_cached`: exact equality of the eager and cached experiments.
* `Cslib.Crypto.isPPT_prfIdealGame`: a strict PPT realization for every oracle-PPT adversary.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].

Adapts Crypto/Computational/PseudorandomFunction/RandomOracle.lean on the cslib `crypto`
branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8` to the shared typed interpreter.
-/

public section

namespace Cslib.Crypto

open Probability

/-- An executable list cache realizes the ideal experiment, preserving repeated-query
consistency and independent private randomness under arbitrary adaptive interaction. -/
theorem prfIdealGame_eq_cached (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame id id adversary n) =
      ProbComp.eval (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun request => cachedRandomFunctionOracle (·.length == n) n request.2))
            (adversary n [])).run []) := by
  simpa only [id_eq, prfIdealGameOn] using
    (eval_prfIdealGameOn_length_eq id id adversary n).symm

open Turing.MultiTapeTM in
/-- The ideal experiment has a strict PPT realization through its lazy cache. This does not
construct the exponentially large eager table; the entire adaptive interaction is certified. -/
theorem isPPT_prfIdealGame {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsPPT encBool (fun n _ => prfIdealGame id id adversary n) := by
  have hrun := isPPTOn_runState_cachedSamplerOracle (input := encPair encUnary encBits)
    (prepare := fun p => (p.1, [])) (valid := fun p q => q.length == p.1)
    (sampleReply := fun p => BitString.sampleList p.1)
    hadversary.on (by fun_prop) (by fun_prop) (ComputableInPolyTime.fst _ _).sampleList
  exact ((hrun.map (ComputableInPolyTime.fst _ _)).isPPT).congr
    (fun n _ => (prfIdealGame_eq_cached adversary n).symm)

end Cslib.Crypto

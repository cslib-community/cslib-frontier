/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.IVStream.Reduction
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for the random-IV reduction

Checks for `CslibFrontier/Crypto/Computational/Encryption/IVStream/Reduction.lean` with a body
that is not a keystream XOR: the body that returns the message, computed with no oracle query.
The file is a `module` client with ordinary imports.
-/

namespace CslibFrontierTests.Crypto.IVModeReduction

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-- With the body that returns the message and makes no query, the reduction is certified for
every certified adversary, and against the keyed oracle it plays the CPA game of `ivModeEncrypt`
with that body. -/
example {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary)
    (family : List Bool → List Bool → List Bool) (bit : Bool) (n : ℕ) :
    IsOraclePPT encBool (ivModeToPrfDistinguisher (fun _ _ msg => pure msg) adversary bit) ∧
      ProbComp.eval (prfRealGame id family
          (ivModeToPrfDistinguisher (fun _ _ msg => pure msg) adversary bit) n) =
        ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
          (ivModeEncrypt fun _ _ _ msg => msg) adversary bit n) :=
  ⟨isOraclePPT_ivModeToPrfDistinguisher
      (ComputableInPolyTime.isOraclePPTOn (f := fun a : ℕ × List Bool × List Bool => a.2.2)
        (by fun_prop))
      (fun _ _ _ _ hreply => by rw [OracleComp.eq_of_mem_supportWith_pure hreply])
      hadversary bit,
    eval_prfRealGame_ivModeToPrfDistinguisher (fun _ _ _ _ _ _ => by simp) adversary bit⟩

end CslibFrontierTests.Crypto.IVModeReduction

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

Checks for `CslibFrontier/Crypto/Computational/Encryption/IVStream/Reduction.lean` with bodies
that are not a keystream XOR: the body that returns the message, computed with no oracle query,
and a body that queries the function oracle on `iv ⊕ msg`, so that its query depends on the
message.
The file is a `module` client with ordinary imports.
-/

public section

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

/-- A body that depends on the message through its query, as CBC mode's does: query the function
oracle on `iv ⊕ msg` and keep at most `msg.length` bits of the answer. -/
noncomputable def xorQueryBody (_n : ℕ) (iv msg : List Bool) : WordOracleComp Unit (List Bool) :=
  List.take msg.length <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
    ((), List.zipWith xor iv msg)

/-- With the querying body `xorQueryBody`, the reduction is certified for every certified
adversary, and against the keyed oracle it plays the CPA game of `ivModeEncrypt` with the body
that truncates the keyed function's value on `iv ⊕ msg`. -/
example {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary)
    (family : List Bool → List Bool → List Bool) (bit : Bool) (n : ℕ) :
    IsOraclePPT encBool (ivModeToPrfDistinguisher xorQueryBody adversary bit) ∧
      ProbComp.eval (prfRealGame id family (ivModeToPrfDistinguisher xorQueryBody adversary bit)
          n) =
        ProbComp.eval (symmetricCPAGameOn blockPairValid BitString.sampleList
          (ivModeEncrypt fun n k iv msg =>
            (prfOracle family n k (List.zipWith xor iv msg)).take msg.length) adversary bit n) :=
  ⟨isOraclePPT_ivModeToPrfDistinguisher
      (IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop))
      (fun _ _ _ _ hreply => by
        obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
        exact List.length_take_le _ _)
      hadversary bit,
    eval_prfRealGame_ivModeToPrfDistinguisher (fun _ _ _ _ _ _ => by
      simp [xorQueryBody, ProbOracleComp.run_map, ProbOracleComp.run_query]) adversary bit⟩

end CslibFrontierTests.Crypto.IVModeReduction

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.NonceCTR
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for `NonceBased` and `NonceCTR`

Concrete round-trips, associated-data (`D ≠ Unit`) instantiations, and theorem-application checks
for `CslibFrontier.Crypto.Computational.Encryption.NonceBased` and
`CslibFrontier.Crypto.Computational.Encryption.NonceCTR` using ordinary `import` (no `import all`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.NonceCipher

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### 1. Concrete `nonceCTRCipher` and `unitCPACodec` round-trips -/

/-- Toy keyed bitwise XOR family for executable round-trip checks. -/
def xorFamily (k x : List Bool) : List Bool :=
  List.zipWith Bool.xor k x

example :
    let E := nonceCTRCipher xorFamily 4 2
    let k := [true, false, true, true]
    let m := [true, true, false, false, false, true, false, true]
    let nonce := [true, false]
    E.decrypt k (E.encrypt k m () nonce) () nonce = some m := by
  decide

example :
    let E := nonceCTRCipher xorFamily 4 2
    let k := [true, false, true, true]
    let m := [true, false, true]
    let nonce := [false, true]
    E.decrypt k (E.encrypt k m () nonce) () nonce = some m := by
  decide

example :
    ctrWordCounter 4 (nonceCTRCounter 4 2 [true, false] 0) 3 =
      nonceCTRCounter 4 2 [true, false] 3 := by
  decide

example :
    let q : MessagePair (List Bool) × Unit × List Bool :=
      (⟨[true, false], [false, true]⟩, (), [true, true])
    NonceCipher.unitCPACodec.decodeQuery (NonceCipher.unitCPACodec.encodeQuery q) = some q :=
  rfl

example : NonceCipher.unitCPACodec.decodeQuery ((), []) = none := rfl

example : NonceCipher.unitCPACodec.decodeQuery ((), [false]) = none := rfl

/-! ### 2. Associated-data (`D = List Bool ≠ Unit`) instantiation -/

/-- Concrete associated-data nonce-based cipher (`D = List Bool`) prefixing the associated data to
a `nonceCTRCipher` ciphertext and checking it on decryption. -/
def toyADCipher : NonceCipher (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) where
  encrypt k m d nonce :=
    d ++ (nonceCTRCipher xorFamily 4 2).encrypt k m () nonce
  decrypt k c d nonce :=
    if c.take d.length == d then
      (nonceCTRCipher xorFamily 4 2).decrypt k (c.drop d.length) () nonce
    else
      none

theorem correct_toyADCipher : toyADCipher.Correct := by
  intro k m d nonce
  simp only [toyADCipher, List.take_left, beq_self_eq_true, ↓reduceIte, List.drop_left]
  exact correct_nonceStreamCipher xorFamily 4 _ k m () nonce

example :
    toyADCipher.decrypt [true, false, true, true]
      (toyADCipher.encrypt [true, false, true, true] [true, true] [true, false] [false, true])
      [false, false] [false, true] = none := by
  decide

/-- Repeating a nonce in `cpaExperiment` with `D = List Bool` sets `ok = false` and forces output
`false` for both `b = false` and `b = true`. -/
example (b : Bool) :
    let repeatAdv :
        ProbOracleComp
          (fun _ : MessagePair (List Bool) × List Bool × List Bool => Option (List Bool)) Bool := do
      let q := (⟨[false], [true]⟩, [true, false], [false])
      let _ ← ProbOracleComp.query q
      let _ ← ProbOracleComp.query q
      return true
    ProbComp.eval
      (toyADCipher.cpaExperiment (pure [true]) (fun m₀ m₁ => m₀.length == m₁.length)
        (fun nonce => nonce.length == 1) repeatAdv b) = PMF.pure false := by
  intro repeatAdv
  rw [NonceCipher.eval_cpaExperiment]
  simp [repeatAdv, ProbComp.eval_pure, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
    NonceCipher.cpaOracle, PMF.pure_bind, PMF.pure_map]

/-! ### 3. Instantiation of Theorem 5.6 (`indcpa_nonceCTR`) and unscaled-CTR attack -/

/-- Multi-block schedule `nonceLen n = n / 2` admitting up to `2 ^ (n - n / 2)` blocks per query. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    NonceCipher.INDCPA (fun n => nonceCTRCipher family n (n / 2))
      Cslib.BitString.sampleList (nonceCTRValid (fun n => n / 2))
      (nonceCTRValidNonce (fun n => n / 2)) :=
  hprf.indcpa_nonceCTR (by polytime) (fun n => Nat.div_le_self n 2)

/-- Single-block schedule `nonceLen = id` (`s = n`, admitting `1` block per `n`-bit nonce). -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    NonceCipher.INDCPA (fun n => nonceCTRCipher family n n)
      Cslib.BitString.sampleList (nonceCTRValid id) (nonceCTRValidNonce id) :=
  hprf.indcpa_nonceCTR (by polytime) (fun _ => le_rfl)

/-- Every `PseudorandomFunction` is length-preserving, so `unscaledNonceCTRCipher` fails
`NonceCipher.INDCPA` even when instantiated with a secure PRF. -/
example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    ¬ NonceCipher.INDCPA (fun n => unscaledNonceCTRCipher family n)
        Cslib.BitString.sampleList blockPairValid (nonceCTRValidNonce id) :=
  not_indcpa_unscaledNonceCTRCipher hprf.length_eq

end CslibFrontierTests.Crypto.NonceCipher

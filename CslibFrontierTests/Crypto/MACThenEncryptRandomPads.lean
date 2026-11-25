/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt.RandomPads
import CslibFrontierTests.Crypto.MACThenEncryptFixture
import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for the random-pad step of MAC-then-encrypt over the one-block PRF cipher

An ordinary `module` client of
`CslibFrontier.Crypto.Computational.Encryption.MACThenEncrypt.RandomPads`, which proves step (9.13)
of the proof of Boneh–Shoup Theorem 9.3 and not the theorem (#640).

* `mtePlaintextValid` on the echo MAC (`tag = msg`): a canonical tagged pair is accepted; a wrong
  tag, a wrong message length and the empty word are rejected; and the canonical-encoding check
  alone rejects a word whose two halves the MAC accepts.
* `StrictMono ptLen` is what the reduction needs: a schedule that `hpairLen` allows and that is not
  injective makes `GeneratorReindex.parameter`, which `mteCIToPrfDistinguisher` uses to recover the
  security parameter, return the wrong one.
* `eval_ciGame_macThenEncrypt_prfCipher_le_freshPads` on the echo family and the echo MAC with
  `ptLen n = 3 * n + 1`: every hypothesis is discharged. For an adversary that asks two queries
  the collision term is `1 / 2 ^ (3 * n + 1)`; for one that asks none it vanishes.
* `isOraclePPT_mteCIToPrfDistinguisher` on the same schedule.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MACThenEncryptRandomPads

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM
open CslibFrontierTests.Crypto.MACThenEncrypt (echoMAC echo_pairLen)
open scoped NNReal ENNReal

/-! ### The plaintext check -/

-- A canonical tagged pair is accepted; a wrong tag, a wrong message length and a word that is no
-- pair encoding are rejected.
example :
    let p := encPair encBits encBits ([false, true], [false, true])
    mtePlaintextValid echoMAC 2 [] p = true ∧
    mtePlaintextValid echoMAC 2 [] (encPair encBits encBits ([false, true], [true, true])) = false ∧
    mtePlaintextValid echoMAC 3 [] p = false ∧
    mtePlaintextValid echoMAC 0 [] [] = false := by
  simp only [mtePlaintextValid, echoMAC]
  decide

-- The canonical-encoding check alone: the halves of `[true]` are the empty message and the empty
-- tag, which the echo MAC accepts at `n = 0`, yet `[true]` is rejected; the canonical word of that
-- pair, `[false]`, is accepted.
example :
    unframe [true] = ([] : List Bool) ∧ dropFrame [true] = ([] : List Bool) ∧
      echoMAC.verify [] [] [] = true ∧
      mtePlaintextValid echoMAC 0 [] [true] = false ∧
      mtePlaintextValid echoMAC 0 [] [false] = true := by
  simp only [mtePlaintextValid, echoMAC]
  decide

/-! ### `StrictMono ptLen` -/

-- `hpairLen` allows a schedule that is not injective: two-bit tags on the empty message and empty
-- tags on one-bit messages both frame to three bits.
example :
    (encPair encBits encBits (([] : List Bool), [true, true])).length = 3 ∧
      (encPair encBits encBits ([true], ([] : List Bool))).length = 3 := by
  decide

-- For such a schedule the reduction recovers the wrong parameter: at PRF parameter `ptLen 0 = 3`
-- it would run the adversary at `n = 1`.
example : GeneratorReindex.parameter (fun n => if n ≤ 1 then 3 else 2 * n + 3) 3 = 1 := by
  decide

/-! ### The step on the echo family -/

theorem echoLen_polyTime : ComputableInPolyTime (fun n : ℕ => 3 * n + 1) encUnary encUnary := by
  polytime

theorem echoLen_strictMono : StrictMono (fun n : ℕ => 3 * n + 1) :=
  fun a b hab => show 3 * a + 1 < 3 * b + 1 by omega

/-- The echo family `F(k, x) = x`. Nothing here needs it to be pseudorandom. -/
def echoFamily : List Bool → List Bool → List Bool := fun _ query => query

theorem echoFamily_polyTime :
    ComputableInPolyTime (fun pair : List Bool × List Bool => echoFamily pair.1 pair.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.snd _ _

/-- MAC-then-encrypt of the echo MAC over the one-block cipher of the echo family. -/
noncomputable def echoMtE : SymmetricCipher :=
  macThenEncrypt (prfCipher echoFamily echoFamily_polyTime (fun _ _ h => h)) echoMAC
    (fun n => 3 * n + 1) echoLen_polyTime (fun _ => rfl) echo_pairLen

-- Every hypothesis of the step is discharged here, for every adversary and query bound.
example (adversary : CIAdversary) (Q : ℕ → ℕ) (n : ℕ)
    (hq : (adversary n []).IsQueryBounded (Q n)) :
    (ProbComp.eval (echoMtE.ciGame adversary n)) true ≤
      ((Game.advantage
          (ProbComp.eval (prfRealGame id echoFamily
            (mteCIToPrfDistinguisher echoMAC (fun n => 3 * n + 1) adversary) (3 * n + 1)))
          (ProbComp.eval (prfIdealGame id id
            (mteCIToPrfDistinguisher echoMAC (fun n => 3 * n + 1) adversary) (3 * n + 1))) : ℝ≥0) :
          ℝ≥0∞) +
        ((Q n).choose 2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ (3 * n + 1)) +
        ((ProbComp.eval (echoMAC.keyGen n)).bind fun km =>
          (ProbOracleComp.runWith (mteForgetfulOracle echoMAC n (3 * n + 1) km) (adversary n [])
            {}).bind (mteIdealFinal echoMAC n (3 * n + 1) km)) true :=
  eval_ciGame_macThenEncrypt_prfCipher_le_freshPads echoFamily echoFamily_polyTime
    (fun _ _ h => h) echoMAC _ echoLen_polyTime echoLen_strictMono (fun _ => rfl) echo_pairLen
    adversary Q n hq

-- Named record and state fields of `MteRec` and `MteState` under ordinary `module` import.
example :
    let rec1 : MteRec := {
      iv := [true, false, false, false]
      pad := [false, false, false, false]
      msg := [true]
      tag := [true]
    }
    let st : MteState := { cache := [(rec1.iv, rec1.pad)], history := [rec1] }
    st.history.map (MteRec.ct 4) =
      [[true, false, false, false] ++
        List.zipWith xor [false, false, false, false] (encPair encBits encBits ([true], [true]))] :=
  rfl

/-- Asks for encryptions of `0ⁿ` and `1ⁿ` and outputs the second ciphertext. -/
def twoQueries : CIAdversary :=
  fun n _ => do
    let _ ← ProbOracleComp.query ((), List.replicate n false)
    ProbOracleComp.query ((), List.replicate n true)

theorem twoQueries_isQueryBounded (n : ℕ) : (twoQueries n []).IsQueryBounded 2 :=
  (ProbOracleComp.IsQueryBounded.query _).bind fun _ => ProbOracleComp.IsQueryBounded.query _

-- With two queries the collision term is live: it is `1 / 2 ^ (3 * n + 1)`, the chance that the
-- two IVs coincide.
example (n : ℕ) :
    (ProbComp.eval (echoMtE.ciGame twoQueries n)) true ≤
      ((Game.advantage
          (ProbComp.eval (prfRealGame id echoFamily
            (mteCIToPrfDistinguisher echoMAC (fun n => 3 * n + 1) twoQueries) (3 * n + 1)))
          (ProbComp.eval (prfIdealGame id id
            (mteCIToPrfDistinguisher echoMAC (fun n => 3 * n + 1) twoQueries) (3 * n + 1))) : ℝ≥0) :
          ℝ≥0∞) +
        (1 : ℝ≥0∞) / 2 ^ (3 * n + 1) +
        ((ProbComp.eval (echoMAC.keyGen n)).bind fun km =>
          (ProbOracleComp.runWith (mteForgetfulOracle echoMAC n (3 * n + 1) km) (twoQueries n [])
            {}).bind (mteIdealFinal echoMAC n (3 * n + 1) km)) true := by
  have h := eval_ciGame_macThenEncrypt_prfCipher_le_freshPads echoFamily echoFamily_polyTime
    (fun _ _ h => h) echoMAC _ echoLen_polyTime echoLen_strictMono (fun _ => rfl) echo_pairLen
    twoQueries (fun _ => 2) n (twoQueries_isQueryBounded n)
  rwa [show (2 : ℕ).choose 2 = 1 from rfl, Nat.cast_one, one_mul] at h

-- Without queries the collision term vanishes: the game is bounded by the PRF advantage and
-- Game 1.
example (adversary : CIAdversary) (n : ℕ) (hq : (adversary n []).IsQueryBounded 0) :
    (ProbComp.eval (echoMtE.ciGame adversary n)) true ≤
      ((Game.advantage
          (ProbComp.eval (prfRealGame id echoFamily
            (mteCIToPrfDistinguisher echoMAC (fun n => 3 * n + 1) adversary) (3 * n + 1)))
          (ProbComp.eval (prfIdealGame id id
            (mteCIToPrfDistinguisher echoMAC (fun n => 3 * n + 1) adversary) (3 * n + 1))) : ℝ≥0) :
          ℝ≥0∞) +
        ((ProbComp.eval (echoMAC.keyGen n)).bind fun km =>
          (ProbOracleComp.runWith (mteForgetfulOracle echoMAC n (3 * n + 1) km) (adversary n [])
            {}).bind (mteIdealFinal echoMAC n (3 * n + 1) km)) true := by
  have h := eval_ciGame_macThenEncrypt_prfCipher_le_freshPads echoFamily echoFamily_polyTime
    (fun _ _ h => h) echoMAC _ echoLen_polyTime echoLen_strictMono (fun _ => rfl) echo_pairLen
    adversary (fun _ => 0) n hq
  rwa [show (0 : ℕ).choose 2 = 0 from rfl, Nat.cast_zero, zero_mul, add_zero] at h

/-! ### The certificate -/

-- The distinguisher is certified on the echo schedule, for every certified adversary.
example {adversary : CIAdversary} (h : IsOraclePPT encBits adversary) :
    IsOraclePPT encBool (mteCIToPrfDistinguisher echoMAC (fun n => 3 * n + 1) adversary) :=
  isOraclePPT_mteCIToPrfDistinguisher _ _ echoLen_polyTime h

end CslibFrontierTests.Crypto.MACThenEncryptRandomPads

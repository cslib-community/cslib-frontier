/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC.PartialTag
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Partial-Tag Encrypt-then-MAC Tests

An ordinary `module` client of
`CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC.PartialTag`: checks `flipHeadBit`,
concrete IV-bit-flip forgery vs body-tamper rejection, the `n = 0` boundary failure vs `n ≥ 1`
win of `partialTagCIAdversary`, `IsOraclePPT` / `IsQueryBounded` / `IsPPT` certificates,
unconditional CI/AE failures, preserved `INDCPA`, and end-to-end `PseudorandomFunction`
instantiation.
-/

public section

namespace CslibFrontierTests.Crypto.EncryptThenMACPartialTag

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-- Toy length-preserving family returning its query unchanged. -/
@[expose]
def echoFamily (_ x : List Bool) : List Bool := x

theorem echoFamily_polyTime :
    ComputableInPolyTime (fun pair : List Bool × List Bool => echoFamily pair.1 pair.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.snd encBits encBits

theorem echoFamily_length (key query : List Bool) (hq : query.length = key.length) :
    (echoFamily key query).length = key.length :=
  hq

/-- Toy deterministic MAC scheme whose tag equals the message itself (`msgLen n = n`). -/
@[expose]
def echoMAC : MACScheme where
  msgLen n := n
  keyGen _ := pure []
  sign _ msg := pure msg
  verify _ msg tag := msg == tag
  keyGen_ppt := (ComputableInPolyTime.const ([] : List Bool)).isPPTOn
  sign_ppt := (ComputableInPolyTime.snd encBits encBits).isPPTOn
  verify_polyTime := by polytime
  verify_sign n km _ msg _ tag htag := by
    change tag ∈ (ProbComp.eval (pure msg)).support at htag
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    exact beq_self_eq_true _

/-- Concrete `prfCipherPartialTag` instantiated with `echoFamily` and `echoMAC`. -/
private noncomputable def echoPrfPartialTag : SymmetricCipher :=
  prfCipherPartialTag echoFamily echoFamily_polyTime echoFamily_length echoMAC (fun _ => rfl)

/-! ### Concrete checks: `flipHeadBit`, IV-bit-flip forgery, and body tamper rejection -/

-- `flipHeadBit` returns `[]` on the empty bit string and flips the leading bit otherwise.
example :
    flipHeadBit [] = [] ∧
    flipHeadBit [false, true, true, false] = [true, true, true, false] := by
  decide

-- Flipping the first bit of the unauthenticated IV changes the framed ciphertext while still
-- passing `echoPrfPartialTag.decrypt`, whereas tampering with the MAC-protected body fails.
example :
    let ke := [true, false]
    let km : List Bool := []
    let k := encPair encBits encBits (ke, km)
    let cFull := [false, true, true, false]
    let tag := [true, false]
    let honestCt := encPair encBits encBits (cFull, tag)
    let flippedIvCt := encPair encBits encBits (flipHeadBit cFull, tag)
    let tamperedBodyCt := encPair encBits encBits ([false, true, true, true], tag)
    flippedIvCt ≠ honestCt ∧
    echoPrfPartialTag.decrypt 2 k honestCt = some [true, true] ∧
    (echoPrfPartialTag.decrypt 2 k flippedIvCt).isSome = true ∧
    echoPrfPartialTag.decrypt 2 k tamperedBodyCt = none ∧
    echoPrfPartialTag.decrypt 2 k [false, true] = none := by
  simp only [echoPrfPartialTag, prfCipherPartialTag, echoMAC, flipHeadBit]
  decide

/-! ### Exact ciphertext bound, `n = 0` boundary failure, and `n ≥ 1` `ciOneTimeGame` win -/

/-- Honest ciphertexts of `echoPrfPartialTag` on `n`-bit plaintexts have length `≤ 5 * n + 1`. -/
private theorem echoPrfPartialTag_ctBound (n : ℕ) :
    echoPrfPartialTag.CiphertextLengthLE n (5 * n + 1) := by
  intro k hk msg hmsg ct hct
  simp only [echoPrfPartialTag, prfCipherPartialTag, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk hct
  obtain ⟨ke, hke, km, _, rfl⟩ := hk
  rw [unframe_encPair_encBits] at hct
  obtain ⟨cFull, hcFull, tag, htag, rfl⟩ := hct
  have hcFullLen : cFull.length = 2 * n :=
    prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length n ke hke
      msg hmsg cFull hcFull
  change tag ∈ (ProbComp.eval (pure (cFull.drop n))).support at htag
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
  subst htag
  simp only [length_encPair, encBits_apply, List.length_drop, hcFullLen]
  omega

-- At `n = 0` (`1 ≤ n` violated), `flipHeadBit [] = []`, so `partialTagCIAdversary` outputs the
-- queried ciphertext unchanged and loses `ciOneTimeGame` with probability `1`.
example :
    ProbComp.eval
        (echoPrfPartialTag.ciOneTimeGame (partialTagCIAdversary (fun m => 5 * m + 1)) 0) =
      PMF.pure false := by
  simp only [SymmetricCipher.ciOneTimeGame, partialTagCIAdversary, OracleComp.interpret_bind,
    OracleComp.interpret_map, OracleComp.interpret_pure, ProbOracleComp.interpret_query,
    StateT.run_bind, StateT.run_map, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.bind_map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  trans ((ProbComp.eval (echoPrfPartialTag.keyGen 0)).bind fun _ => PMF.pure false)
  · apply PMF.bind_congr_on_support
    intro k hk
    have hk' := hk
    simp only [echoPrfPartialTag, prfCipherPartialTag, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk'
    obtain ⟨ke, hke, km, _, rfl⟩ := hk'
    simp only [SymmetricCipher.oneTimeCIEncryptionOracle, StateT.run, List.isEmpty_nil,
      List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    trans ((ProbComp.eval (echoPrfPartialTag.encrypt 0 (encPair encBits encBits (ke, km))
        [])).bind fun _ => PMF.pure false)
    · apply PMF.bind_congr_on_support
      intro ct hct
      rw [List.take_of_length_le (echoPrfPartialTag_ctBound 0 _ hk [] rfl ct hct)]
      simp only [echoPrfPartialTag, prfCipherPartialTag, unframe_encPair_encBits,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hct
      obtain ⟨cFull, hcFull, tag, _, rfl⟩ := hct
      have hcFullLen : cFull.length = 2 * 0 :=
        prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length 0 ke hke
          [] rfl cFull hcFull
      have hNil : cFull = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hNil
      rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
      simp [flipHeadBit]
    · simp
  · simp

-- For `n = 2 ≥ 1`, `partialTagCIAdversary` wins `ciOneTimeGame` with probability `1`, satisfies
-- `IsOraclePPT` and 1-query boundedness, and yields a `IsPPT` closed game.
example :
    IsOraclePPT encBits (partialTagCIAdversary (fun m => 5 * m + 1)) ∧
    (partialTagCIAdversary (fun m => 5 * m + 1) 2 []).IsQueryBounded 1 ∧
    IsPPT encBool
      (fun n _ => echoPrfPartialTag.ciOneTimeGame (partialTagCIAdversary (fun m => 5 * m + 1)) n) ∧
    ProbComp.eval
        (echoPrfPartialTag.ciOneTimeGame (partialTagCIAdversary (fun m => 5 * m + 1)) 2) =
      PMF.pure true :=
  ⟨isOraclePPT_partialTagCIAdversary (by polytime),
   isQueryBounded_partialTagCIAdversary (fun m => 5 * m + 1) 2 [],
   echoPrfPartialTag.isPPT_ciOneTimeGame (isOraclePPT_partialTagCIAdversary (by polytime)),
   eval_ciOneTimeGame_prfCipherPartialTag echoFamily echoFamily_polyTime echoFamily_length
     echoMAC (fun _ => rfl) (fun m => 5 * m + 1) (by decide) (echoPrfPartialTag_ctBound 2)⟩

/-! ### Unconditional CI/AE failures, CPA preservation, and PRF counterexample -/

-- `echoPrfPartialTag` fails all four ciphertext-integrity and authenticated-encryption notions.
example :
    ¬ echoPrfPartialTag.OneTimeCiphertextIntegrity ∧
    ¬ echoPrfPartialTag.CiphertextIntegrity ∧
    ¬ echoPrfPartialTag.OneTimeAuthenticatedEncryption ∧
    ¬ echoPrfPartialTag.AuthenticatedEncryption :=
  ⟨not_oneTimeCiphertextIntegrity_prfCipherPartialTag echoFamily echoFamily_polyTime
     echoFamily_length echoMAC (fun _ => rfl),
   not_ciphertextIntegrity_prfCipherPartialTag echoFamily echoFamily_polyTime
     echoFamily_length echoMAC (fun _ => rfl),
   not_oneTimeAuthenticatedEncryption_prfCipherPartialTag echoFamily echoFamily_polyTime
     echoFamily_length echoMAC (fun _ => rfl),
   not_authenticatedEncryption_prfCipherPartialTag echoFamily echoFamily_polyTime
     echoFamily_length echoMAC (fun _ => rfl)⟩

/-- Zero-query CPA distinguisher returning `false`. -/
@[expose]
def zeroCPAAdversary : OracleDistinguisher :=
  fun _ _ => ProbOracleComp.sample (pure false)

theorem isOraclePPT_zeroCPAAdversary : IsOraclePPT encBool zeroCPAAdversary :=
  (ComputableInPolyTime.const false :
      ComputableInPolyTime (fun _ : ℕ × List Bool => false) (encPair encUnary encBits)
        encBool).isPPTOn.isOraclePPTOn.isOraclePPT

-- `partialTagToCPAAdversary` preserves `IsOraclePPT` and matches the `cpaGame` distribution.
example (bit : Bool) (n : ℕ) :
    IsOraclePPT encBool (partialTagToCPAAdversary echoMAC zeroCPAAdversary) ∧
    ProbComp.eval
        ((prfCipher echoFamily echoFamily_polyTime echoFamily_length).cpaGame
          (partialTagToCPAAdversary echoMAC zeroCPAAdversary) bit n) =
      ProbComp.eval (echoPrfPartialTag.cpaGame zeroCPAAdversary bit n) :=
  ⟨isOraclePPT_partialTagToCPAAdversary echoMAC isOraclePPT_zeroCPAAdversary,
   eval_cpaGame_partialTagToCPAAdversary echoFamily echoFamily_polyTime echoFamily_length
     echoMAC (fun _ => rfl) zeroCPAAdversary bit n⟩

-- `INDCPA` preservation and non-vacuous instantiation from any `PseudorandomFunction`
-- (both with an abstract `MACScheme` and with `prfMAC family hprf.polyTime`).
example
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    (prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen).INDCPA :=
  hprf.indcpa_prfCipherPartialTag M hmsgLen

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfCipherPartialTag family hprf.polyTime hprf.length_eq
        (prfMAC family hprf.polyTime) (fun _ => rfl)).INDCPA ∧
      (prfCipherPartialTag family hprf.polyTime hprf.length_eq
        (prfMAC family hprf.polyTime) (fun _ => rfl)).OneTimeINDCPA ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq
          (prfMAC family hprf.polyTime) (fun _ => rfl)).OneTimeCiphertextIntegrity ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq
          (prfMAC family hprf.polyTime) (fun _ => rfl)).CiphertextIntegrity ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq
          (prfMAC family hprf.polyTime) (fun _ => rfl)).OneTimeAuthenticatedEncryption ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq
          (prfMAC family hprf.polyTime) (fun _ => rfl)).AuthenticatedEncryption :=
  hprf.prfCipherPartialTag_counterexample (prfMAC family hprf.polyTime) (fun _ => rfl)

end CslibFrontierTests.Crypto.EncryptThenMACPartialTag

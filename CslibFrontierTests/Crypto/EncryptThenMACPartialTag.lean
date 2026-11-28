/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC.PartialTag
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PolyTime

/-!
# Partial-Tag Encrypt-then-MAC Tests

An ordinary `module` client of
`CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC.PartialTag`: checks `flipHeadBit`,
concrete IV-bit-flip forgery vs body-tamper rejection, the `n = 0` and insufficient-`ctBound`
failing cases vs the `n = 2` win of `partialTagCIAdversary` with its certificates, and the
non-vacuous `PseudorandomFunction` / `prfMAC` instantiation.
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

-- `flipHeadBit` flips the leading bit of a non-empty bit string.
example : flipHeadBit [false, true, true, false] = [true, true, true, false] :=
  rfl

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
  simp only [echoPrfPartialTag, prfCipherPartialTag, encryptThenMAC, partialTagMAC, echoMAC,
    flipHeadBit]
  decide

/-! ### `CiphertextLengthLE` bound, `n = 0` & short-`ctBound` failures, and `n = 2` win -/

/-- Honest ciphertexts of `echoPrfPartialTag` on `n`-bit plaintexts have length `≤ 5 * n + 1`. -/
private theorem echoPrfPartialTag_ctBound (n : ℕ) :
    echoPrfPartialTag.CiphertextLengthLE n (5 * n + 1) := by
  intro k hk msg hmsg ct hct
  simp only [echoPrfPartialTag, prfCipherPartialTag, encryptThenMAC, partialTagMAC,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hk hct
  obtain ⟨ke, hke, km, _, rfl⟩ := hk
  rw [unframe_encPair_encBits] at hct
  obtain ⟨cFull, hcFull, tag, htag, rfl⟩ := hct
  have hcFullLen : cFull.length = 2 * n :=
    prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length n ke hke
      msg hmsg cFull hcFull
  have hcHalf : cFull.length / 2 = n := by rw [hcFullLen]; omega
  rw [hcHalf] at htag
  change tag ∈ (ProbComp.eval (pure (cFull.drop n))).support at htag
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
  subst htag
  simp only [length_encPair, encBits_apply, List.length_drop, hcFullLen]
  omega

-- At `n = 0` (`1 ≤ n` violated), `flipHeadBit [] = [true]`, so `partialTagCIAdversary`
-- outputs a `1`-bit candidate that fails the `2 * 0`-bit length check in decryption, losing
-- `ciOneTimeGame` with probability `1`.
example :
    ProbComp.eval
        (echoPrfPartialTag.ciOneTimeGame (partialTagCIAdversary (fun m => 5 * m + 1)) 0) =
      PMF.pure false := by
  simp only [SymmetricCipher.ciOneTimeGame, partialTagCIAdversary, SymmetricCipher.maulCIAdversary,
    runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun k hk => ?_
  have hk' := hk
  simp only [echoPrfPartialTag, prfCipherPartialTag, encryptThenMAC, partialTagMAC,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hk'
  obtain ⟨ke, hke, km, _, rfl⟩ := hk'
  simp only [SymmetricCipher.oneTimeCIEncryptionOracle, List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun ct hct => ?_
  rw [List.take_of_length_le (echoPrfPartialTag_ctBound 0 _ hk [] rfl ct hct)]
  simp only [echoPrfPartialTag, prfCipherPartialTag, encryptThenMAC, partialTagMAC,
    unframe_encPair_encBits, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hct
  obtain ⟨cFull, hcFull, tag, _, rfl⟩ := hct
  have hcFullLen : cFull.length = 2 * 0 :=
    prfCipher_ciphertext_length echoFamily echoFamily_polyTime echoFamily_length 0 ke hke
      [] rfl cFull hcFull
  have hNil : cFull = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hNil
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits,
    show flipHeadBit [] = [true] from rfl]
  simp only [echoPrfPartialTag, prfCipherPartialTag, encryptThenMAC, partialTagMAC,
    unframe_encPair_encBits, dropFrame_encPair_encBits]
  simp

-- When `ctBound` violates `CiphertextLengthLE` (`ctBound _ = 0` at `n = 2`), the reply is cut to
-- `[]`, producing an ill-sized forgery that fails decryption, so the adversary loses
-- `ciOneTimeGame`.
example :
    ProbComp.eval
        (echoPrfPartialTag.ciOneTimeGame (partialTagCIAdversary (fun _ => 0)) 2) =
      PMF.pure false := by
  simp only [SymmetricCipher.ciOneTimeGame, partialTagCIAdversary, SymmetricCipher.maulCIAdversary,
    runWith_norm, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun _ _ => ?_
  simp only [SymmetricCipher.oneTimeCIEncryptionOracle, List.isEmpty_nil,
    List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, pmf_norm]
  refine PMF.bind_eq_pure_of_forall_mem_support fun _ _ => ?_
  simp [echoPrfPartialTag, prfCipherPartialTag, encryptThenMAC, partialTagMAC, flipHeadBit,
    unframe]

-- For `n = 2 ≥ 1`, `partialTagCIAdversary` wins `ciOneTimeGame` with probability `1`, satisfies
-- `IsOraclePPT` and 1-query boundedness, and yields an `IsPPT` closed game.
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
   eval_ciOneTimeGame_prfCipherPartialTag_partialTagCIAdversary echoFamily echoFamily_polyTime
     echoFamily_length echoMAC (fun _ => rfl) (fun m => 5 * m + 1) (by decide)
     (echoPrfPartialTag_ctBound 2)⟩

/-! ### Non-vacuous `PseudorandomFunction` / `prfMAC` instantiation -/

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfCipherPartialTag family hprf.polyTime hprf.length_eq
        (prfMAC family hprf.polyTime) (fun _ => rfl)).INDCPA ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq
          (prfMAC family hprf.polyTime) (fun _ => rfl)).OneTimeCiphertextIntegrity :=
  hprf.prfCipherPartialTag_counterexample (prfMAC family hprf.polyTime) (fun _ => rfl)

end CslibFrontierTests.Crypto.EncryptThenMACPartialTag

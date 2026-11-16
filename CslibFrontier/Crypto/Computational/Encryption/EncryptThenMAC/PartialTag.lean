/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Partial-Tag Encrypt-then-MAC Counterexample

This module formalizes the ciphertext-integrity failure of **partial-tag Encrypt-then-MAC**
([BonehShoup2023], Section 9.4.1.1, printed pp. 368–369), where the MAC tag authenticates only
the ciphertext body `c` and omits the random initialization vector (IV) `r`.

1. **Construction (`prfCipherPartialTag`)**: wraps the PRF-based randomized cipher
   `prfCipher family hpoly hlen` (whose ciphertexts on `n`-bit plaintexts have the form `r ++ c`
   with an `n`-bit IV `r` and `n`-bit body `c`, `prfCipher_ciphertext_length`) together with any
   `MACScheme M` authenticating `n`-bit messages (`∀ n, M.msgLen n = n`). Encryption samples
   `cFull ← (prfCipher ...).encrypt n ke msg`, computes `tag ← M.sign km (cFull.drop n)` (signing
   only `c`, not `r`), and frames `encPair encBits encBits (cFull, tag)`. Decryption checks
   canonical `encPair` framing, `(unframe ct).length == 2 * n`, and
   `M.verify km ((unframe ct).drop n) (dropFrame ct)`, then decrypts `unframe ct` using `prfCipher`.
2. **Explicit 1-query ciphertext-integrity attack (`partialTagCIAdversary`,
   `isOraclePPT_partialTagCIAdversary`, `eval_ciOneTimeGame_prfCipherPartialTag`)**: an explicit
   `IsOraclePPT` one-query adversary queries `0^n`, splits `(cFull, tag)`, and flips the first IV
   bit (`flipHeadBit cFull`) while keeping `tag` intact. For every `n ≥ 1`, flipping the first bit
   of `r` changes `cFull` (hence the framed ciphertext) without changing `cFull.drop n`, so MAC
   verification and length-`2 * n` decryption succeed with probability `1`. This unconditionally
   refutes `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeAuthenticatedEncryption`,
   and `AuthenticatedEncryption` for every `MACScheme` on `n`-bit messages.
3. **Preserved CPA security (`partialTagToCPAAdversary`,
   `PseudorandomFunction.indcpa_prfCipherPartialTag`)**: signing `cFull.drop n` uses only the
   independent MAC key `km` and public ciphertext `cFull`, so the `prfCipherPartialTag` CPA game
   distribution coincides with that of `prfCipher` under `partialTagToCPAAdversary`
   (`eval_cpaGame_partialTagToCPAAdversary`). Thus every `PseudorandomFunction` keeps
   `prfCipherPartialTag` both `INDCPA` (`PseudorandomFunction.indcpa_prfCipherPartialTag`) and
   `OneTimeINDCPA`, giving an explicit `INDCPA` yet non-AE counterexample
   (`PseudorandomFunction.prfCipherPartialTag_counterexample`).

## Scope limitation

The **CBC half of Section 9.4.1.1 (printed pp. 368–369) is not covered** here: in Boneh–Shoup's
randomized CBC example, changing `(r, c, t)` to `(r ⊕ Δ, c, t)` additionally shifts the decrypted
first plaintext block deterministically to `m'[0] = m[0] ⊕ Δ` (and breaks chosen-ciphertext
secrecy). Under `prfCipher`, changing the IV `r` evaluates the PRF on a fresh nonce `r'` instead
of XORing `Δ` into `m`, so only the IV-malleability ciphertext-integrity break (and preserved
`INDCPA`) is formalized here.

## Main definitions

* `Cslib.Crypto.flipHeadBit`: flips the leading bit of a non-empty bit string.
* `Cslib.Crypto.prfCipherPartialTag`: partial-tag Encrypt-then-MAC variant over `prfCipher`.
* `Cslib.Crypto.partialTagCIAdversary`: explicit 1-query IV-bit-flip ciphertext-integrity
  adversary.
* `Cslib.Crypto.partialTagToCPAAdversary`: CPA reduction from `prfCipherPartialTag` to
  `prfCipher`.

## Main results

* `Cslib.Crypto.isOraclePPT_partialTagCIAdversary`: strict oracle-PPT admissibility for
  `partialTagCIAdversary`.
* `Cslib.Crypto.eval_ciOneTimeGame_prfCipherPartialTag`: `partialTagCIAdversary` wins
  `ciOneTimeGame` with probability `1` for every `n ≥ 1`.
* `Cslib.Crypto.not_oneTimeCiphertextIntegrity_prfCipherPartialTag`,
  `Cslib.Crypto.not_ciphertextIntegrity_prfCipherPartialTag`,
  `Cslib.Crypto.not_oneTimeAuthenticatedEncryption_prfCipherPartialTag`,
  `Cslib.Crypto.not_authenticatedEncryption_prfCipherPartialTag`: ciphertext-integrity and
  authenticated-encryption failures for every `MACScheme` on `n`-bit messages.
* `Cslib.Crypto.PseudorandomFunction.indcpa_prfCipherPartialTag`,
  `Cslib.Crypto.PseudorandomFunction.prfCipherPartialTag_counterexample`: preserved `INDCPA`
  alongside failed ciphertext integrity and authenticated encryption.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 9.4.1.1 (printed pp. 368–369).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Flip the leading bit of a bit string, returning `[]` on `[]`. -/
@[expose]
def flipHeadBit (xs : List Bool) : List Bool :=
  if xs.isEmpty then []
  else if xs.take 1 == [true] then [false] ++ xs.tail else [true] ++ xs.tail

@[fun_prop]
private theorem computableInPolyTime_flipHeadBit :
    ComputableInPolyTime flipHeadBit encBits encBits := by
  unfold flipHeadBit
  fun_prop

private theorem flipHeadBit_cons (b : Bool) (rest : List Bool) :
    flipHeadBit (b :: rest) = (!b) :: rest := by
  cases b <;> rfl

private theorem flipHeadBit_ne {xs : List Bool} (hne : xs ≠ []) :
    flipHeadBit xs ≠ xs := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons b rest =>
    rw [flipHeadBit_cons]
    intro h
    exact Bool.not_ne_self b (List.cons.inj h).1

private theorem length_flipHeadBit (xs : List Bool) :
    (flipHeadBit xs).length = xs.length := by
  cases xs with
  | nil => rfl
  | cons b rest => simp [flipHeadBit_cons]

private theorem drop_flipHeadBit {n : ℕ} (hn : 1 ≤ n) (xs : List Bool) (hxs : n ≤ xs.length) :
    (flipHeadBit xs).drop n = xs.drop n := by
  cases xs with
  | nil =>
    simp only [List.length_nil] at hxs
    lia
  | cons b rest =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : n ≠ 0)
    simp [flipHeadBit_cons]

/-- Partial-tag Encrypt-then-MAC over `prfCipher` ([BonehShoup2023], Section 9.4.1.1, printed
pp. 368–369): runs `prfCipher family hpoly hlen` to produce `cFull = r ++ c` (`2 * n` bits on
`n`-bit messages), signs only the `n`-bit masked body `c = cFull.drop n` using `M`, and outputs
`encPair encBits encBits (cFull, tag)`, leaving the `n`-bit IV `r` unauthenticated.

Note: this covers the partial-tag Encrypt-then-MAC construction over `prfCipher` rather than
randomized CBC mode, so the deterministic CBC plaintext-shift `m'[0] = m[0] ⊕ Δ` is not covered. -/
@[expose]
noncomputable def prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) : SymmetricCipher where
  keyGen n := do
    let ke ← (prfCipher family hpoly hlen).keyGen n
    let km ← M.keyGen n
    return encPair encBits encBits (ke, km)
  encrypt n k msg := do
    let cFull ← (prfCipher family hpoly hlen).encrypt n (unframe k) msg
    let tag ← M.sign (dropFrame k) (cFull.drop n)
    return encPair encBits encBits (cFull, tag)
  decrypt n k ct :=
    if (encPair encBits encBits (unframe ct, dropFrame ct) == ct) &&
        ((unframe ct).length == 2 * n) &&
        M.verify (dropFrame k) ((unframe ct).drop n) (dropFrame ct) then
      (prfCipher family hpoly hlen).decrypt n (unframe k) (unframe ct)
    else
      none
  keyGen_ppt := by
    let E := prfCipher family hpoly hlen
    have hpost : ComputableInPolyTime
        (fun p : (ℕ × List Bool) × List Bool => encPair encBits encBits (p.1.2, p.2))
        (encPair (encPair encUnary encBits) encBits) encBits :=
      ComputableInPolyTime.encoding_comp (by fun_prop)
    exact E.keyGen_ppt.bind_with
      ((M.keyGen_ppt.preprocess (ComputableInPolyTime.fst encUnary encBits)).bind_with
        hpost.isPPTOn)
  encrypt_ppt := by
    let E := prfCipher family hpoly hlen
    let I := encPair encUnary (encPair encBits encBits)
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.1) I encUnary := by
      dsimp only [I]; fun_prop
    have hk : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.1) I encBits := by
      dsimp only [I]; fun_prop
    have hm : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) I encBits := by
      dsimp only [I]; fun_prop
    have hrun := E.isPPTOn_encrypt_comp hn (ComputableInPolyTime.unframe.comp hk) hm
    have hkm : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => dropFrame p.1.2.1)
        (encPair I encBits) encBits := by
      dsimp only [I]; fun_prop
    have hdrop : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => p.2.drop p.1.1)
        (encPair I encBits) encBits := by
      dsimp only [I]
      exact ComputableTidilyInPolyTime.bitsDropWithInput (by fun_prop) (by fun_prop)
        |>.computableInPolyTime
    have hsign := M.isPPTOn_sign_comp hkm hdrop
    have hpost : ComputableInPolyTime
        (fun p : ((ℕ × List Bool × List Bool) × List Bool) × List Bool =>
          encPair encBits encBits (p.1.2, p.2))
        (encPair (encPair I encBits) encBits) encBits :=
      ComputableInPolyTime.encoding_comp (by fun_prop)
    exact hrun.bind_with (hsign.bind_with hpost.isPPTOn)
  decrypt_polyTime := by
    let E := prfCipher family hpoly hlen
    let EIn := encPair encUnary (encPair encBits encBits)
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.1) EIn encUnary := by
      dsimp only [EIn]; fun_prop
    have hke : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => unframe p.2.1) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have hkm : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => dropFrame p.2.1) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have hcFull : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => unframe p.2.2) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have htag : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => dropFrame p.2.2) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have hcBody : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (unframe p.2.2).drop p.1) EIn encBits := by
      dsimp only [EIn]
      exact ComputableTidilyInPolyTime.bitsDropWithInput (by fun_prop) (by fun_prop)
        |>.computableInPolyTime
    have hct : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => p.2.2) EIn encBits := by
      dsimp only [EIn]; fun_prop
    have hroundTrip : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          encPair encBits encBits (unframe p.2.2, dropFrame p.2.2) == p.2.2) EIn encBool :=
      ComputableInPolyTime.beq
        (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.frame.comp hcFull) htag) hct
    have hsize : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (unframe p.2.2).length == 2 * p.1) EIn encBool := by
      dsimp only [EIn]; fun_prop
    have hver := M.computableInPolyTime_verify_comp hkm hcBody htag
    have hcond : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          (encPair encBits encBits (unframe p.2.2, dropFrame p.2.2) == p.2.2) &&
            ((unframe p.2.2).length == 2 * p.1) &&
            M.verify (dropFrame p.2.1) ((unframe p.2.2).drop p.1) (dropFrame p.2.2))
        EIn encBool :=
      ComputableInPolyTime.bool_and.comp
        ((ComputableInPolyTime.bool_and.comp (hroundTrip.prod hsize)).prod hver)
    have hyes := E.computableInPolyTime_decrypt_comp hn hke hcFull
    exact ComputableInPolyTime.ite hcond hyes (ComputableInPolyTime.const none)
  decrypt_encrypt := by
    intro n k hk msg hmsg ct hct
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hk hct
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
    rw [unframe_encPair_encBits, dropFrame_encPair_encBits] at hct
    obtain ⟨cFull, hcFull, tag, htag, rfl⟩ := hct
    have hcFullLen : cFull.length = 2 * n :=
      prfCipher_ciphertext_length family hpoly hlen n ke hke msg hmsg cFull hcFull
    have hcBodyLen : (cFull.drop n).length = M.msgLen n := by
      rw [List.length_drop, hcFullLen, hmsgLen n]
      omega
    have hver : M.verify km (cFull.drop n) tag = true :=
      M.verify_sign n km hkm (cFull.drop n) hcBodyLen tag htag
    have hdec : (prfCipher family hpoly hlen).decrypt n ke cFull = some msg :=
      (prfCipher family hpoly hlen).decrypt_encrypt n ke hke msg hmsg cFull hcFull
    rw [unframe_encPair_encBits, dropFrame_encPair_encBits,
      unframe_encPair_encBits, dropFrame_encPair_encBits]
    simp [hcFullLen, hver, hdec]

/-! ### 1-Query IV-Bit-Flip Attack and Ciphertext-Integrity Break -/

/-- Explicit 1-query ciphertext-integrity adversary against `prfCipherPartialTag`
([BonehShoup2023], Section 9.4.1.1, printed pp. 368–369): queries `0^n`, splits the canonical
ciphertext `ct` into `(cFull, tag)`, and outputs `encPair encBits encBits (flipHeadBit cFull, tag)`,
flipping the first IV bit while leaving the body and MAC tag unchanged. -/
@[expose]
def partialTagCIAdversary (ctBound : ℕ → ℕ) : CIAdversary :=
  fun n _ => do
    let ct ← List.take (ctBound n) <$> ProbOracleComp.query ((), List.replicate n false)
    return encPair encBits encBits (flipHeadBit (unframe ct), dropFrame ct)

/-- `partialTagCIAdversary` is uniformly strict oracle-PPT (`IsOraclePPT`). -/
theorem isOraclePPT_partialTagCIAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (partialTagCIAdversary ctBound) := by
  have hct := hctBound.tidy
  ppt [partialTagCIAdversary]

/-- `partialTagCIAdversary` makes at most `1` encryption query. -/
theorem isQueryBounded_partialTagCIAdversary (ctBound : ℕ → ℕ) (n : ℕ) (aux : List Bool) :
    (partialTagCIAdversary ctBound n aux).IsQueryBounded 1 := by
  unfold partialTagCIAdversary
  have hq :
      (List.take (ctBound n) <$>
        (ProbOracleComp.query ((), List.replicate n false) :
          WordOracleComp Unit (List Bool))).IsQueryBounded 1 := by
    simp only [OracleComp.isCostBounded_map_iff]
    exact ProbOracleComp.IsQueryBounded.query ((), List.replicate n false)
  exact hq.bind fun _ => OracleComp.IsCostBounded.pure _ 0

private theorem malleate_prfCipherPartialTag_ciphertext
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    {n : ℕ} (hn : 1 ≤ n) {ke km msg ct : List Bool}
    (hke : ke ∈ (ProbComp.eval ((prfCipher family hpoly hlen).keyGen n)).support)
    (hkm : km ∈ (ProbComp.eval (M.keyGen n)).support)
    (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval ((prfCipherPartialTag family hpoly hlen M hmsgLen).encrypt n
      (encPair encBits encBits (ke, km)) msg)).support) :
    encPair encBits encBits (flipHeadBit (unframe ct), dropFrame ct) ≠ ct ∧
    ((prfCipherPartialTag family hpoly hlen M hmsgLen).decrypt n
      (encPair encBits encBits (ke, km))
      (encPair encBits encBits (flipHeadBit (unframe ct), dropFrame ct))).isSome = true := by
  simp only [prfCipherPartialTag, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
    unframe_encPair_encBits, dropFrame_encPair_encBits] at hct
  obtain ⟨cFull, hcFull, tag, htag, rfl⟩ := hct
  have hcFullLen : cFull.length = 2 * n :=
    prfCipher_ciphertext_length family hpoly hlen n ke hke msg hmsg cFull hcFull
  have hcFullNe : cFull ≠ [] := by
    intro hNil
    simp only [hNil, List.length_nil] at hcFullLen
    omega
  have hcBodyLen : (cFull.drop n).length = M.msgLen n := by
    simp only [List.length_drop, hcFullLen, hmsgLen n]
    omega
  have hver : M.verify km (cFull.drop n) tag = true :=
    M.verify_sign n km hkm (cFull.drop n) hcBodyLen tag htag
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
  refine ⟨?_, ?_⟩
  · intro hEq
    have hUnframe := congrArg unframe hEq
    rw [unframe_encPair_encBits, unframe_encPair_encBits] at hUnframe
    exact flipHeadBit_ne hcFullNe hUnframe
  · have hLenFlip : (flipHeadBit cFull).length = 2 * n := by
      rw [length_flipHeadBit, hcFullLen]
    have hDropFlip : (flipHeadBit cFull).drop n = cFull.drop n :=
      drop_flipHeadBit hn cFull (by omega)
    simp only [prfCipherPartialTag]
    rw [unframe_encPair_encBits, dropFrame_encPair_encBits,
      unframe_encPair_encBits, dropFrame_encPair_encBits,
      hLenFlip, hDropFlip, hver]
    simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, prfCipher, hLenFlip]
    simp

/-- `partialTagCIAdversary` wins `ciOneTimeGame` against `prfCipherPartialTag` with probability
`1` at every security parameter `n ≥ 1`. -/
theorem eval_ciOneTimeGame_prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (ctBound : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hctBound :
      (prfCipherPartialTag family hpoly hlen M hmsgLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval ((prfCipherPartialTag family hpoly hlen M hmsgLen).ciOneTimeGame
      (partialTagCIAdversary ctBound) n) = PMF.pure true := by
  let E' := prfCipherPartialTag family hpoly hlen M hmsgLen
  simp only [SymmetricCipher.ciOneTimeGame, partialTagCIAdversary,
    OracleComp.interpret_bind, OracleComp.interpret_map, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  trans ((ProbComp.eval (E'.keyGen n)).bind fun _ => PMF.pure true)
  · apply PMF.bind_congr_on_support
    intro k hk
    have hk' := hk
    simp only [prfCipherPartialTag, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk'
    obtain ⟨ke, hke, km, hkm, rfl⟩ := hk'
    simp only [SymmetricCipher.oneTimeCIEncryptionOracle, StateT.run, List.isEmpty_nil,
      List.length_replicate, beq_self_eq_true, Bool.and_self, ↓reduceIte, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
    trans ((ProbComp.eval (E'.encrypt n (encPair encBits encBits (ke, km))
        (List.replicate n false))).bind fun _ => PMF.pure true)
    · apply PMF.bind_congr_on_support
      intro ct hct
      rw [List.take_of_length_le (hctBound _ hk _ List.length_replicate ct hct)]
      obtain ⟨hne, hdec⟩ := malleate_prfCipherPartialTag_ciphertext family hpoly hlen M hmsgLen
        hn hke hkm List.length_replicate hct
      simp only [encPair_apply, encBits_apply] at hne hdec
      simp [hne, hdec]
    · simp
  · simp

/-- `prfCipherPartialTag` unconditionally fails `OneTimeCiphertextIntegrity` for every `MACScheme`
on `n`-bit messages. -/
theorem not_oneTimeCiphertextIntegrity_prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    ¬ (prfCipherPartialTag family hpoly hlen M hmsgLen).OneTimeCiphertextIntegrity := by
  intro hci
  let E' := prfCipherPartialTag family hpoly hlen M hmsgLen
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E'.exists_ciphertext_length_bound_of_length_eq
  have hneg := (hci.negligible (partialTagCIAdversary ctBound)
    (isOraclePPT_partialTagCIAdversary hctBoundPoly)).shift 1
  have hconst : Negligible (fun _ : ℕ => (1 : ℝ≥0)) := by
    refine hneg.congr fun n => ?_
    rw [eval_ciOneTimeGame_prfCipherPartialTag family hpoly hlen M hmsgLen ctBound
      (by omega) (hctBound (n + 1))]
    simp [Game.succProbability]
  exact not_negligible_const one_ne_zero hconst

/-- `prfCipherPartialTag` unconditionally fails `CiphertextIntegrity` for every `MACScheme` on
`n`-bit messages. -/
theorem not_ciphertextIntegrity_prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    ¬ (prfCipherPartialTag family hpoly hlen M hmsgLen).CiphertextIntegrity :=
  fun hci => not_oneTimeCiphertextIntegrity_prfCipherPartialTag family hpoly hlen M hmsgLen
    hci.oneTimeCiphertextIntegrity

/-- `prfCipherPartialTag` fails `OneTimeAuthenticatedEncryption`. -/
theorem not_oneTimeAuthenticatedEncryption_prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    ¬ (prfCipherPartialTag family hpoly hlen M hmsgLen).OneTimeAuthenticatedEncryption :=
  fun hae => not_oneTimeCiphertextIntegrity_prfCipherPartialTag family hpoly hlen M hmsgLen hae.2

/-- `prfCipherPartialTag` fails `AuthenticatedEncryption`. -/
theorem not_authenticatedEncryption_prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    ¬ (prfCipherPartialTag family hpoly hlen M hmsgLen).AuthenticatedEncryption :=
  fun hae => not_ciphertextIntegrity_prfCipherPartialTag family hpoly hlen M hmsgLen hae.2

/-! ### IND-CPA Preservation and Combined Counterexample -/

/-- Open handler simulating the CPA encryption oracle of `prfCipherPartialTag` inside
`(prfCipher family hpoly hlen).cpaGame`: forwards valid `n`-bit message pairs to the underlying
encryption oracle (truncating the reply to `2 * n` bits) and signs `cFull.drop n` using `km`. -/
private noncomputable def partialTagToCPAHandler (M : MACScheme) (n : ℕ) (km : List Bool)
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) :=
  fun _ =>
    let m0 := unframe request.2
    let m1 := dropFrame request.2
    if (m0.length == n) && (m1.length == n) then do
      let cFull ← List.take (2 * n) <$> ProbOracleComp.query ((), request.2)
      (fun tag => (encPair encBits encBits (cFull, tag), ())) <$>
        ProbOracleComp.sample (M.sign km (cFull.drop n))
    else
      pure ([], ())

/-- IND-CPA reduction `partialTagToCPAAdversary` from `prfCipherPartialTag` to `prfCipher`: draws
the MAC key `km ← M.keyGen n` locally and runs `adversary n []` against
`partialTagToCPAHandler M n km`. -/
noncomputable def partialTagToCPAAdversary (M : MACScheme) (adversary : OracleDistinguisher) :
    OracleDistinguisher :=
  fun n _ => do
    let km ← ProbOracleComp.sample (M.keyGen n)
    Prod.fst <$> (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (partialTagToCPAHandler M n km))
      (adversary n [])).run ()

private theorem isOraclePPTOn_partialTagToCPAHandler (M : MACScheme) :
    IsOraclePPTOn
      (encPair (encPair (encPair encUnary encBits) encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : ((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit) =>
        partialTagToCPAHandler M pair.1.1.1 pair.1.2 pair.2.1 pair.2.2) := by
  let EIn := encPair (encPair (encPair encUnary encBits) encBits)
    (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hDrop :
      IsOraclePPTOn (Operation := Unit) (encPair EIn encBits) encBits
        (fun p => ProbOracleComp.sample (M.sign p.1.1.2 (p.2.drop p.1.1.1.1))) := by
    have hkm : ComputableInPolyTime
        (fun p : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) =>
          p.1.1.2)
        (encPair EIn encBits) encBits := by
      dsimp only [EIn]; fun_prop
    have hmsg : ComputableInPolyTime
        (fun p : ((((ℕ × List Bool) × List Bool) × ((Unit × List Bool) × Unit)) × List Bool) =>
          p.2.drop p.1.1.1.1)
        (encPair EIn encBits) encBits := by
      dsimp only [EIn]
      exact ComputableTidilyInPolyTime.bitsDropWithInput (by fun_prop) (by fun_prop)
        |>.computableInPolyTime
    exact (M.isPPTOn_sign_comp hkm hmsg).isOraclePPTOn (Operation := Unit)
  ppt [partialTagToCPAHandler]

/-- `partialTagToCPAAdversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_partialTagToCPAAdversary (M : MACScheme) {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (partialTagToCPAAdversary M adversary) := by
  obtain ⟨cs, ds, hlenSign⟩ := M.sign_ppt.length_le
  let ECaller := encPair (encPair encUnary encBits) encBits
  have hkm : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encBits
      (fun caller : ℕ × List Bool => ProbOracleComp.sample (M.keyGen caller.1)) :=
    (M.keyGen_ppt.preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn (Operation := Unit)
  have hhandler := isOraclePPTOn_partialTagToCPAHandler M
  have hprepare : ComputableInPolyTime
      (fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hres : ComputableInPolyTime
      (fun pair : ((ℕ × List Bool) × List Bool) × List Bool =>
        4 * pair.1.1.1 + cs * (2 * pair.1.2.length + 2 * pair.1.1.1 + 2) ^ ds + 2)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; fun_prop
  have hrun : IsOraclePPTOn (Operation := Unit) ECaller (encPair encBool (encFinEnum Unit))
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (partialTagToCPAHandler M caller.1.1 caller.2))
          (adversary caller.1.1 [])).run ()) := by
    apply hadversary.run_interpret_preprocess_open
      (input := ECaller)
      (handler := fun caller : (ℕ × List Bool) × List Bool =>
        partialTagToCPAHandler M caller.1.1 caller.2)
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => ())
      (resources := fun caller _ =>
        4 * caller.1.1 + cs * (2 * caller.2.length + 2 * caller.1.1 + 2) ^ ds + 2)
      hprepare hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) hres
    intro caller request state _ result hresult
    unfold partialTagToCPAHandler at hresult
    dsimp only at hresult
    split_ifs at hresult with hlenEq
    · obtain ⟨cFull, hc, hresult⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain ⟨rawCt, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hc
      have hcTake : (List.take (2 * caller.1.1) rawCt).length ≤ 2 * caller.1.1 :=
        List.length_take_le _ _
      have hcDrop :
          ((List.take (2 * caller.1.1) rawCt).drop caller.1.1).length ≤ 2 * caller.1.1 := by
        rw [List.length_drop]
        exact (Nat.sub_le _ _).trans hcTake
      obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      simp only [ProbOracleComp.support_sample] at htag
      have htagLen := hlenSign
        (caller.2, (List.take (2 * caller.1.1) rawCt).drop caller.1.1) tag htag
      simp only [length_encPair, encBits_apply] at htagLen
      have htagBound : tag.length ≤ cs * (2 * caller.2.length + 2 * caller.1.1 + 2) ^ ds :=
        htagLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))
      refine ⟨trivial, ?_, by lia⟩
      enc_len
    · have hresEq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst hresEq
      exact ⟨trivial, by simp, by lia⟩
  have hrunMap : IsOraclePPTOn (Operation := Unit) ECaller encBool
      (fun caller : (ℕ × List Bool) × List Bool =>
        Prod.fst <$> (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (partialTagToCPAHandler M caller.1.1 caller.2))
          (adversary caller.1.1 [])).run ()) := by ppt
  unfold partialTagToCPAAdversary
  exact (hkm.bind_with hrunMap).isOraclePPT

/-- `partialTagToCPAAdversary` in `(prfCipher family hpoly hlen).cpaGame` produces the exact same
output distribution as running `adversary` in `(prfCipherPartialTag ...).cpaGame`. -/
theorem eval_cpaGame_partialTagToCPAAdversary
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) :
    ProbComp.eval ((prfCipher family hpoly hlen).cpaGame
        (partialTagToCPAAdversary M adversary) bit n) =
      ProbComp.eval ((prfCipherPartialTag family hpoly hlen M hmsgLen).cpaGame
        adversary bit n) := by
  have hkeyGen : (prfCipherPartialTag family hpoly hlen M hmsgLen).keyGen =
      (fun n => do
        let ke ← (prfCipher family hpoly hlen).keyGen n
        let km ← M.keyGen n
        return encPair encBits encBits (ke, km)) := rfl
  simp only [SymmetricCipher.cpaGame, partialTagToCPAAdversary, hkeyGen, runWith_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun ke hke => ?_
  refine PMF.bind_congr_on_support _ _ _ fun km _ => ?_
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun q (state : Unit × Unit) =>
      (ProbOracleComp.runWith (fun q s =>
          ProbComp.eval ((prfCipher family hpoly hlen).cpaEncryptionOracle n ke bit q s))
          (partialTagToCPAHandler M n km q state.1) state.2).map
        (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s =>
      ProbComp.eval ((prfCipherPartialTag family hpoly hlen M hmsgLen).cpaEncryptionOracle n
        (encPair encBits encBits (ke, km)) bit q s))
    (represent := fun _ : Unit × Unit => ())
    (step := by
      intro ⟨⟨⟩, payload⟩ ⟨⟨⟩, ⟨⟩⟩
      unfold partialTagToCPAHandler SymmetricCipher.cpaEncryptionOracle
      dsimp only [prfCipherPartialTag]
      rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
      by_cases hlenEq : ((unframe payload).length == n && (dropFrame payload).length == n) = true
      · simp only [hlenEq, ↓reduceIte, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
          ProbOracleComp.runWith_query, ProbOracleComp.runWith_sample, ProbComp.eval_bind,
          ProbComp.eval_pure]
        simp only [Bool.and_eq_true, beq_iff_eq] at hlenEq
        have hmbLen : (if bit then dropFrame payload else unframe payload).length = n := by
          cases bit <;> simp [hlenEq]
        simp only [PMF.map_comp, PMF.map_bind, Function.comp_def,
          PMF.pure_map, PMF.pure_bind, PMF.bind_bind, Prod.map_apply, id_eq]
        apply PMF.bind_congr_on_support
        intro cFull hcFull
        have hcLen : cFull.length = 2 * n :=
          prfCipher_ciphertext_length family hpoly hlen n ke hke _ hmbLen cFull hcFull
        rw [List.take_of_length_le hcLen.le]
        rfl
      · simp [hlenEq, ProbOracleComp.runWith_pure, ProbComp.eval_pure])
    (adversary n []) ((), ())
  have hsim' := congrArg (PMF.map Prod.fst) hsim
  simp only [PMF.map_comp, Function.comp_def] at hsim'
  exact hsim'

/-- For any secure `PseudorandomFunction family`, `prfCipherPartialTag` satisfies `INDCPA`. -/
theorem PseudorandomFunction.indcpa_prfCipherPartialTag
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    (prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen).INDCPA := by
  intro adversary hadversary
  have hred := hprf.indcpa_prfCipher (partialTagToCPAAdversary M adversary)
    (isOraclePPT_partialTagToCPAAdversary M hadversary)
  refine hred.congr fun n => ?_
  dsimp only
  rw [eval_cpaGame_partialTagToCPAAdversary family hprf.polyTime hprf.length_eq M hmsgLen
        adversary false n,
      eval_cpaGame_partialTagToCPAAdversary family hprf.polyTime hprf.length_eq M hmsgLen
        adversary true n]

/-- **End-to-end partial-tag Encrypt-then-MAC counterexample** ([BonehShoup2023], Section 9.4.1.1,
printed pp. 368–369): for any secure `PseudorandomFunction family` and any `MACScheme M` on
`n`-bit messages, `prfCipherPartialTag` remains `INDCPA` and `OneTimeINDCPA` yet unconditionally
fails `OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeAuthenticatedEncryption`, and
`AuthenticatedEncryption`. -/
theorem PseudorandomFunction.prfCipherPartialTag_counterexample
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    (prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen).INDCPA ∧
      (prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen).OneTimeINDCPA ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq M
          hmsgLen).OneTimeCiphertextIntegrity ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen).CiphertextIntegrity ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq M
          hmsgLen).OneTimeAuthenticatedEncryption ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq M
          hmsgLen).AuthenticatedEncryption :=
  let hcpa := hprf.indcpa_prfCipherPartialTag M hmsgLen
  ⟨hcpa, hcpa.oneTimeINDCPA,
    not_oneTimeCiphertextIntegrity_prfCipherPartialTag family hprf.polyTime hprf.length_eq
      M hmsgLen,
    not_ciphertextIntegrity_prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen,
    not_oneTimeAuthenticatedEncryption_prfCipherPartialTag family hprf.polyTime hprf.length_eq M
      hmsgLen,
    not_authenticatedEncryption_prfCipherPartialTag family hprf.polyTime hprf.length_eq M
      hmsgLen⟩

end Cslib.Crypto

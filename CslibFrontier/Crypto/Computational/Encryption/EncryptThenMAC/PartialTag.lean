/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Authenticated.Malleability
public import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
public import CslibFrontier.Crypto.Computational.FlipHeadBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PPT

/-!
# Partial-Tag Encrypt-then-MAC Counterexample

This module formalizes the ciphertext-integrity failure of **partial-tag Encrypt-then-MAC**
([BonehShoup2023], Section 9.4.1.1, printed pp. 368–369): given a symmetric cipher producing
`2 * n`-bit ciphertexts `r ++ c` (an `n`-bit IV `r` and `n`-bit body `c`), the scheme signs and
verifies only the second half `c` while leaving `r` unauthenticated.

We construct `partialTagMAC M hmsgLen` (wrapping any `MACScheme M` with `∀ n, M.msgLen n = n`
into a `2 * n`-bit `MACScheme` that authenticates only the second half `msg.drop (msg.length / 2)`)
and define `prfCipherPartialTag` directly via `encryptThenMAC (prfCipher ...) (partialTagMAC ...)`.
The explicit 1-query `IsOraclePPT` adversary `partialTagCIAdversary ctBound` queries `0^n`,
truncates the reply to `ctBound n`, and flips the first IV bit via `Cslib.Crypto.flipHeadBit`,
winning `ciOneTimeGame` with probability `1` for every `n ≥ 1` and unconditionally refuting
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, and `AuthenticatedEncryption`, while
`indcpa_encryptThenMAC` immediately preserves `INDCPA` under any `PseudorandomFunction`.

## Scope and deviations

Boneh–Shoup Section 9.4.1.1 (printed pp. 368–369) illustrates partial-tag Encrypt-then-MAC over
randomized CBC mode, where changing `(r, c, t)` to `(r ⊕ Δ, c, t)` both breaks ciphertext integrity
and deterministically shifts the first decrypted plaintext block (`m'[0] = m[0] ⊕ Δ`). Here
`prfCipherPartialTag` replaces randomized CBC with `prfCipher` (`r ++ (F(k, r) ⊕ m)`): flipping `r`
evaluates the PRF on a fresh nonce rather than XORing into `m`, so only the ciphertext-integrity
failure and preserved `INDCPA` are formalized here; the CBC plaintext-shift effect needs a CBC
`SymmetricCipher`, and chosen-ciphertext security (`INDCCA`) of `prfCipherPartialTag` is neither
proved nor refuted here.

## Main definitions

* `Cslib.Crypto.partialTagMAC`: lifts any `n`-bit `MACScheme` to `2 * n`-bit messages by
  signing and verifying only `msg.drop (msg.length / 2)`.
* `Cslib.Crypto.prfCipherPartialTag`: `encryptThenMAC` over `prfCipher` and `partialTagMAC`.
* `Cslib.Crypto.partialTagCIAdversary`: explicit 1-query IV-bit-flip ciphertext-integrity
  adversary.

## Main results

* `Cslib.Crypto.isOraclePPT_partialTagCIAdversary`,
  `Cslib.Crypto.isQueryBounded_partialTagCIAdversary`: strict oracle-PPT admissibility and 1-query
  bound for `partialTagCIAdversary`.
* `Cslib.Crypto.eval_ciOneTimeGame_prfCipherPartialTag_partialTagCIAdversary`:
  `partialTagCIAdversary` wins `ciOneTimeGame` with probability `1` for every `n ≥ 1` when
  `ctBound` bounds ciphertext lengths.
* `Cslib.Crypto.not_oneTimeCiphertextIntegrity_prfCipherPartialTag`,
  `Cslib.Crypto.not_ciphertextIntegrity_prfCipherPartialTag`,
  `Cslib.Crypto.not_authenticatedEncryption_prfCipherPartialTag`: unconditional ciphertext-integrity
  and authenticated-encryption failures for every `MACScheme` on `n`-bit messages.
* `Cslib.Crypto.PseudorandomFunction.indcpa_prfCipherPartialTag`,
  `Cslib.Crypto.PseudorandomFunction.prfCipherPartialTag_counterexample`: preserved `INDCPA`
  via `indcpa_encryptThenMAC` alongside failed `OneTimeCiphertextIntegrity`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 9.4.1.1 (printed pp. 368–369).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

private theorem length_flipHeadBit {xs : List Bool} (hne : xs ≠ []) :
    (flipHeadBit xs).length = xs.length := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons _ _ => rfl

private theorem drop_flipHeadBit {n : ℕ} (hn : 1 ≤ n) (xs : List Bool) (hxs : n ≤ xs.length) :
    (flipHeadBit xs).drop n = xs.drop n := by
  cases xs with
  | nil =>
    simp only [List.length_nil] at hxs
    omega
  | cons _ _ =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rfl

/-- Lifts any `MACScheme M` on `n`-bit messages (`∀ n, M.msgLen n = n`) to a `MACScheme` on
`2 * n`-bit messages that signs and verifies only the second half `msg.drop (msg.length / 2)`,
leaving the `n`-bit prefix unauthenticated. -/
@[expose]
noncomputable def partialTagMAC (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) : MACScheme where
  msgLen n := 2 * n
  msgLen_polyTime := by fun_prop
  keyGen := M.keyGen
  sign sk msg := M.sign sk (msg.drop (msg.length / 2))
  verify sk msg tag := M.verify sk (msg.drop (msg.length / 2)) tag
  keyGen_ppt := M.keyGen_ppt
  sign_ppt := by
    have hdrop : ComputableInPolyTime
        (fun p : List Bool × List Bool => p.2.drop (p.2.length / 2))
        (encPair encBits encBits) encBits :=
      ComputableInPolyTime.bitsDropWithInput (by fun_prop) (by fun_prop)
    exact M.isPPTOn_sign_comp (by fun_prop) hdrop
  verify_polyTime := by
    have hdrop : ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool => p.2.1.drop (p.2.1.length / 2))
        encBitsTriple encBits :=
      ComputableInPolyTime.bitsDropWithInput (by fun_prop) (by fun_prop)
    exact M.computableInPolyTime_verify_comp (by fun_prop) hdrop (by fun_prop)
  verify_sign n sk hsk msg hmsg tag htag := by
    have hhalf : (msg.drop (msg.length / 2)).length = M.msgLen n := by
      rw [List.length_drop, hmsg, hmsgLen n]
      omega
    exact M.verify_sign n sk hsk (msg.drop (msg.length / 2)) hhalf tag htag

/-- Partial-tag Encrypt-then-MAC over `prfCipher` ([BonehShoup2023], Section 9.4.1.1, printed
pp. 368–369): instantiates `encryptThenMAC` with `prfCipher family hpoly hlen` (`2 * n`-bit
ciphertexts `r ++ c`) and `partialTagMAC M hmsgLen`, signing only the `n`-bit body `c` and leaving
the `n`-bit IV `r` unauthenticated.

Note: this covers the partial-tag construction over `prfCipher` rather than randomized CBC mode,
so the CBC plaintext-shift effect `m'[0] = m[0] ⊕ Δ` is not covered, and `INDCCA` security of
this scheme is neither proved nor refuted here. -/
@[expose]
noncomputable def prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) : SymmetricCipher :=
  encryptThenMAC (prfCipher family hpoly hlen) (partialTagMAC M hmsgLen)
    (prfCipher_ciphertext_length family hpoly hlen)

/-! ### 1-Query IV-Bit-Flip Attack and Ciphertext-Integrity Break -/

/-- Explicit 1-query ciphertext-integrity adversary against `prfCipherPartialTag`
([BonehShoup2023], Section 9.4.1.1, printed pp. 368–369): queries `0^n`, cuts the reply to
`ctBound n` bits, splits `(cFull, tag)`, and outputs
`encPair encBits encBits (flipHeadBit cFull, tag)`, flipping the first IV bit while leaving the
body and MAC tag unchanged. -/
@[expose]
def partialTagCIAdversary (ctBound : ℕ → ℕ) : CIAdversary :=
  SymmetricCipher.maulCIAdversary
    (fun _ ct => encPair encBits encBits (flipHeadBit (unframe ct), dropFrame ct)) false ctBound

/-- Flipping the first initial-value bit of a framed ciphertext and keeping its tag, on the second
component, is polynomial-time. -/
private theorem computableInPolyTime_partialTagMaul :
    ComputableInPolyTime
      (fun p : ℕ × List Bool => encPair encBits encBits (flipHeadBit (unframe p.2), dropFrame p.2))
      (encPair encUnary encBits) encBits := by
  polytime

/-- `partialTagCIAdversary` is uniformly strict oracle-PPT (`IsOraclePPT`) when `ctBound` is
computable in plain polynomial time. -/
theorem isOraclePPT_partialTagCIAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary) :
    IsOraclePPT encBits (partialTagCIAdversary ctBound) :=
  SymmetricCipher.isOraclePPT_maulCIAdversary computableInPolyTime_partialTagMaul false hctBound

/-- `partialTagCIAdversary` makes at most `1` encryption query. -/
theorem isQueryBounded_partialTagCIAdversary (ctBound : ℕ → ℕ) (n : ℕ) (aux : List Bool) :
    (partialTagCIAdversary ctBound n aux).IsQueryBounded 1 := by
  unfold partialTagCIAdversary SymmetricCipher.maulCIAdversary
  exact ((OracleComp.isCostBounded_map_iff _ _ _).mpr
    (ProbOracleComp.IsQueryBounded.query ((), List.replicate n false))).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

private theorem malleate_prfCipherPartialTag_ciphertext
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    {n : ℕ} (hn : 1 ≤ n) {k msg ct : List Bool}
    (hk : k ∈ (ProbComp.eval ((prfCipherPartialTag family hpoly hlen M hmsgLen).keyGen n)).support)
    (hmsg : msg.length = n)
    (hct : ct ∈ (ProbComp.eval ((prfCipherPartialTag family hpoly hlen M hmsgLen).encrypt n
      k msg)).support) :
    encPair encBits encBits (flipHeadBit (unframe ct), dropFrame ct) ≠ ct ∧
    ((prfCipherPartialTag family hpoly hlen M hmsgLen).decrypt n k
      (encPair encBits encBits (flipHeadBit (unframe ct), dropFrame ct))).isSome = true := by
  simp only [prfCipherPartialTag, encryptThenMAC, partialTagMAC, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hk
  obtain ⟨ke, hke, km, hkm, rfl⟩ := hk
  simp only [prfCipherPartialTag, encryptThenMAC, partialTagMAC, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
    unframe_encPair_encBits, dropFrame_encPair_encBits] at hct
  obtain ⟨cFull, hcFull, tag, htag, rfl⟩ := hct
  have hcFullLen : cFull.length = 2 * n :=
    prfCipher_ciphertext_length family hpoly hlen n ke hke msg hmsg cFull hcFull
  have hcHalf : cFull.length / 2 = n := by rw [hcFullLen]; omega
  rw [hcHalf] at htag
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
    exact flipHeadBit_ne_self cFull hUnframe
  · have hLenFlip : (flipHeadBit cFull).length = 2 * n := by
      rw [length_flipHeadBit (List.ne_nil_of_length_pos (by omega)), hcFullLen]
    simp [prfCipherPartialTag, encryptThenMAC, partialTagMAC, prfCipher, hLenFlip,
      drop_flipHeadBit hn cFull (by omega), hver]

/-- `partialTagCIAdversary` wins `ciOneTimeGame` against `prfCipherPartialTag` with probability
`1` at every security parameter `n ≥ 1` where `ctBound n` bounds ciphertext lengths. -/
theorem eval_ciOneTimeGame_prfCipherPartialTag_partialTagCIAdversary
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n)
    (ctBound : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n)
    (hctBound :
      (prfCipherPartialTag family hpoly hlen M hmsgLen).CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval ((prfCipherPartialTag family hpoly hlen M hmsgLen).ciOneTimeGame
      (partialTagCIAdversary ctBound) n) = PMF.pure true :=
  SymmetricCipher.eval_ciOneTimeGame_maulCIAdversary _ false ctBound n hctBound fun _ hk _ hct =>
    malleate_prfCipherPartialTag_ciphertext family hpoly hlen M hmsgLen hn hk List.length_replicate
      hct

/-- `prfCipherPartialTag` unconditionally fails `OneTimeCiphertextIntegrity` for every `MACScheme`
on `n`-bit messages. -/
theorem not_oneTimeCiphertextIntegrity_prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    ¬ (prfCipherPartialTag family hpoly hlen M hmsgLen).OneTimeCiphertextIntegrity :=
  SymmetricCipher.not_oneTimeCiphertextIntegrity_of_maul _ computableInPolyTime_partialTagMaul
    false 1 fun _ hn _ hk _ hct =>
      malleate_prfCipherPartialTag_ciphertext family hpoly hlen M hmsgLen hn hk
        List.length_replicate hct

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

/-- `prfCipherPartialTag` unconditionally fails `AuthenticatedEncryption` for every `MACScheme`
on `n`-bit messages. -/
theorem not_authenticatedEncryption_prfCipherPartialTag
    (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    ¬ (prfCipherPartialTag family hpoly hlen M hmsgLen).AuthenticatedEncryption :=
  fun hae => not_ciphertextIntegrity_prfCipherPartialTag family hpoly hlen M hmsgLen hae.2

/-! ### IND-CPA Preservation and Combined Counterexample -/

/-- For any secure `PseudorandomFunction family`, `prfCipherPartialTag` satisfies `INDCPA` by
`indcpa_encryptThenMAC` and `hprf.indcpa_prfCipher`. -/
theorem PseudorandomFunction.indcpa_prfCipherPartialTag
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    (prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen).INDCPA :=
  indcpa_encryptThenMAC (prfCipher family hprf.polyTime hprf.length_eq)
    (partialTagMAC M hmsgLen) (prfCipher_ciphertext_length family hprf.polyTime hprf.length_eq)
    hprf.indcpa_prfCipher

/-- **End-to-end partial-tag Encrypt-then-MAC counterexample** ([BonehShoup2023], Section 9.4.1.1,
printed pp. 368–369): for any secure `PseudorandomFunction family` and any `MACScheme M` on
`n`-bit messages, `prfCipherPartialTag` remains `INDCPA` yet unconditionally fails
`OneTimeCiphertextIntegrity`. -/
theorem PseudorandomFunction.prfCipherPartialTag_counterexample
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    (M : MACScheme) (hmsgLen : ∀ n, M.msgLen n = n) :
    (prfCipherPartialTag family hprf.polyTime hprf.length_eq M hmsgLen).INDCPA ∧
      ¬ (prfCipherPartialTag family hprf.polyTime hprf.length_eq M
          hmsgLen).OneTimeCiphertextIntegrity :=
  ⟨hprf.indcpa_prfCipherPartialTag M hmsgLen,
    not_oneTimeCiphertextIntegrity_prfCipherPartialTag family hprf.polyTime hprf.length_eq
      M hmsgLen⟩

end Cslib.Crypto

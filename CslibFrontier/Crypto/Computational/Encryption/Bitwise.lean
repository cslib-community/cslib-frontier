/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Crypto.Computational.Encryption.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Traverse
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindCompare
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import Mathlib.Data.List.GetD
import CslibFrontier.Tactic.Negligible

/-!
# Multi-bit chosen-plaintext security of bitwise public-key encryption

Library infrastructure for bitwise multi-bit public-key encryption (`bitwiseEncrypt`,
`bitwiseDecrypt`) and its single-challenge coordinate hybrid reduction step (after
[KatzLindell2020], Section 12.2.2, locator not verified, rather than Theorem 12.6's
multi-encryption oracle endpoint; cf. [BonehShoup2023], Section 11.3.2, Attack Game 11.2 and
Theorem 11.1, pp. 438–440, which instead lifts single-challenge to multi-challenge CPA security
over the same message space `M` as in `Cslib.Crypto.Encryption.LoRCPA.FromSingle`, rather than
1-bit-to-multi-bit bitwise encryption `{0, 1} → {0, 1}^ℓ`). Encrypting each bit of a message word
independently under
a single-bit public-key scheme yields a bit-word encryption scheme. Any chosen-message adversary
against equal-length challenge words of length at most `maxLen n` reduces to a single-bit
chosen-message adversary (`bitwiseToSingle`) by a hybrid argument across the coordinates: the
reduction chooses its challenge pair first, samples an index `split` from
`Fin (dyadicSize (maxLen n))` via `ProbComp.sampleDyadicIndex (maxLen n)` so that sampling runs in
strict fair-coin polynomial time with zero approximation error, submits `(m₀[split], m₁[split])` to
the single-bit challenger, and encrypts the prefix `m₁.take split` and suffix `m₀.drop (split + 1)`
itself using the public key.

Because all bits of the challenge word are chosen before any ciphertext is produced, the prefix and
suffix ciphertexts are sampled non-adaptively with `List.mapM`: unlike the adaptive multi-query
reduction `lorToSingle` (`Cslib.Crypto.Encryption.LoRCPA.FromSingle`), `isPPT_bitwiseToSingle`
needs no global polynomial cap on ciphertext lengths under malformed public keys.

For unrestricted equal-length challenges (`WordINDCPA`), the length of the adversary's chosen words
is bounded by a polynomial in `n` plus the public-key length (`IsPPTOn.length_le`). Whenever the
honest key generator produces public keys of polynomially bounded length—in particular whenever key
generation is uniform strict PPT—every strict-PPT word adversary's challenge words satisfy a
uniform unary polynomial-time length schedule `maxLen`, so single-bit `INDCPA` implies
`WordINDCPA`. Without a polynomial bound on public-key length, a single-bit `INDCPA` scheme with
exponentially long public keys and `2⁻ⁿ` per-bit leakage fails `WordINDCPA`.

## Main definitions

* `Cslib.Crypto.Encryption.bitwiseEncrypt`, `Cslib.Crypto.Encryption.bitwiseDecrypt`: framed
  bit-by-bit encryption and decryption of bit words from a single-bit scheme.
* `Cslib.Crypto.Encryption.validBoundedWords`: equal-length challenge admissibility with an explicit
  upper bound `maxLen n`.
* `Cslib.Crypto.Encryption.bitwiseToSingleAt`, `Cslib.Crypto.Encryption.bitwiseToSingle`:
  single-bit chosen-message adversaries at a fixed coordinate and at a dyadically sampled
  coordinate.
* `Cslib.Crypto.Encryption.bitwiseHybridGameOn`: coordinate hybrid experiment encrypting
  `m₁.take split ++ m₀.drop split`.

## Main results

* `Cslib.Crypto.Encryption.isPPTOn_bitwiseEncrypt`,
  `Cslib.Crypto.Encryption.computableInPolyTime_bitwiseDecrypt`,
  `Cslib.Crypto.Encryption.bitwiseDecrypt_bitwiseEncrypt`: efficiency and support-level round-trip
  correctness of `bitwiseEncrypt` and `bitwiseDecrypt`.
* `Cslib.Crypto.Encryption.computableInPolyTime_validBoundedWords`: polynomial-time evaluation of
  `validBoundedWords maxLen` for unary polynomial-time `maxLen`.
* `Cslib.Crypto.Encryption.isPPT_bitwiseToSingleAt`,
  `Cslib.Crypto.Encryption.isPPT_bitwiseToSingle`: uniform strict-PPT certificates for the
  coordinate hybrid reductions.
* `Cslib.Crypto.Encryption.bitwiseHybridGameOn_step_gap`,
  `Cslib.Crypto.Encryption.eval_game_bitwiseToSingle`,
  `Cslib.Crypto.Encryption.advantage_bitwiseEncrypt_eq`: single-step hybrid identity, mixture
  decomposition, and exact strict-PPT advantage identity with factor `dyadicSize (maxLen n)`.
* `Cslib.Crypto.Encryption.INDCPA.indcpaOn_bitwiseEncrypt`,
  `Cslib.Crypto.Encryption.INDCPA.wordINDCPA_bitwiseEncrypt_of_publicKey_length_le`,
  `Cslib.Crypto.Encryption.INDCPA.wordINDCPA_bitwiseEncrypt`: asymptotic single-bit-to-multi-bit
  chosen-plaintext security for bounded challenge predicates, public-key-bounded schemes, and
  uniform strict-PPT key generators.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 12.2.2 (locator not verified).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.2 (Attack Game 11.1, p. 436) and Section 11.3.2
  (Attack Game 11.2 and Theorem 11.1, pp. 438–440; multi-challenge hybrid over a fixed message
  space `M`).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Bitwise word encryption, decryption, and bounded-word admissibility -/

/-- Encrypt each bit of `bits` independently with `encrypt n pk` and frame the resulting ciphertext
list with `encList encBits`. -/
@[expose]
noncomputable def bitwiseEncrypt (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (n : ℕ) (pk bits : List Bool) : ProbComp (List Bool) :=
  encList encBits <$> bits.mapM (encrypt n pk)

/-- Split `ct` into its framed bit ciphertexts via `frames` and decrypt each with `decrypt sk`. -/
@[expose]
def bitwiseDecrypt (decrypt : List Bool → List Bool → Bool) (sk ct : List Bool) : List Bool :=
  (frames ct).map (decrypt sk)

/-- `bitwiseEncrypt encrypt` is uniformly strict PPT whenever `encrypt` is. -/
@[program_certificate]
theorem isPPTOn_bitwiseEncrypt {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, pk, b⟩ => encrypt n pk b)) :
    IsPPTOn (encKeyedInput encBits) encBits
      (fun ⟨n, pk, bits⟩ => bitwiseEncrypt encrypt n pk bits) := by
  let prog (x : ℕ × List Bool × List Bool) (b : Bool) : ProbComp (List Bool) :=
    encrypt x.1 x.2.1 b
  have hstep : IsPPTOn (encPair (encKeyedInput encBits) encBool) encBits
      (fun p => prog p.1 p.2) := by
    have hp1 := ComputableInPolyTime.fst (encKeyedInput encBits) encBool
    have hn := (ComputableInPolyTime.fst encUnary (encPair encBits encBits)).comp hp1
    have hpk := ((ComputableInPolyTime.snd encUnary (encPair encBits encBits)).fst').comp hp1
    have hb := ComputableInPolyTime.snd (encKeyedInput encBits) encBool
    exact (hencrypt.preprocess
      (prepare := fun p : (ℕ × List Bool × List Bool) × Bool => (p.1.1, p.1.2.1, p.2))
      (hn.prod (hpk.prod hb))).congr fun _ => rfl
  have hlist : ComputableInPolyTime (fun x : ℕ × List Bool × List Bool => x.2.2)
      (encKeyedInput encBits) (encList encBool) :=
    ComputableInPolyTime.bitsToList.comp
      (ComputableInPolyTime.snd encUnary (encPair encBits encBits)).snd'
  exact (isPPTOn_iff_encoded.mp (IsPPTOn.mapMWith (program := prog) hstep hlist)).congr
    fun ⟨_, _, _⟩ => rfl

/-- `bitwiseDecrypt decrypt` is computable in polynomial time whenever `decrypt` is. -/
theorem computableInPolyTime_bitwiseDecrypt {decrypt : List Bool → List Bool → Bool}
    (hdecrypt : ComputableInPolyTime (fun ⟨sk, ct⟩ => decrypt sk ct)
      (encPair encBits encBits) encBool) :
    ComputableInPolyTime (fun ⟨sk, ct⟩ => bitwiseDecrypt decrypt sk ct)
      (encPair encBits encBits) encBits := by
  have hcts : ComputableInPolyTime (fun p : List Bool × List Bool => frames p.2)
      (encPair encBits encBits) (encList encBits) :=
    computableInPolyTime_frames.comp (ComputableInPolyTime.snd encBits encBits)
  have hbit : ComputableInPolyTime
      (fun q : (List Bool × List Bool) × List Bool => decrypt q.1.1 q.2)
      (encPair (encPair encBits encBits) encBits) encBool :=
    hdecrypt.comp
      (((ComputableInPolyTime.fst encBits encBits).comp
        (ComputableInPolyTime.fst (encPair encBits encBits) encBits)).prod
        (ComputableInPolyTime.snd (encPair encBits encBits) encBits))
  exact ComputableInPolyTime.mapToBitsWithInput
    (f := fun (p : List Bool × List Bool) ct => decrypt p.1 ct) hcts hbit

/-- `bitwiseDecrypt decrypt sk` on a framed list of bit ciphertexts maps `decrypt sk` across it. -/
@[simp] theorem bitwiseDecrypt_encList (decrypt : List Bool → List Bool → Bool) (sk : List Bool)
    (cts : List (List Bool)) :
    bitwiseDecrypt decrypt sk (encList encBits cts) = cts.map (decrypt sk) := by
  simp only [bitwiseDecrypt, frames_encList, List.map_map, Function.comp_def, encBits_apply]

/-- Support-level round-trip correctness of `bitwiseEncrypt` and `bitwiseDecrypt`: if `decrypt sk`
recovers every bit encrypted under `pk`, then `bitwiseDecrypt decrypt sk` recovers every bit word
encrypted by `bitwiseEncrypt encrypt n pk`. -/
theorem bitwiseDecrypt_bitwiseEncrypt {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : List Bool → List Bool → Bool} {n : ℕ} {pk sk : List Bool}
    (hcorrect : ∀ b ct, ct ∈ (ProbComp.eval (encrypt n pk b)).support → decrypt sk ct = b)
    (bits : List Bool) {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (bitwiseEncrypt encrypt n pk bits)).support) :
    bitwiseDecrypt decrypt sk ct = bits := by
  simp only [bitwiseEncrypt, ProbComp.eval_map, PMF.mem_support_map_iff,
    ProbComp.mem_support_mapM_iff] at hct
  obtain ⟨cts, hcts, rfl⟩ := hct
  rw [bitwiseDecrypt_encList]
  induction hcts with
  | nil => rfl
  | cons hhead _ ih =>
    simp only [List.map_cons, hcorrect _ _ hhead, ih]

/-- Admissibility predicate for equal-length bit-word challenges of length at most `maxLen n`. -/
@[expose]
def validBoundedWords (maxLen : ℕ → ℕ) (n : ℕ) (_pk m₀ m₁ : List Bool) : Bool :=
  (m₀.length == m₁.length) && decide (m₀.length ≤ maxLen n)

/-- `validBoundedWords maxLen` is computable in polynomial time on the challenge-pair input when
`maxLen` is unary polynomial-time computable. -/
theorem computableInPolyTime_validBoundedWords {maxLen : ℕ → ℕ}
    (hmax : ComputableInPolyTime maxLen encUnary encUnary) :
    ComputableInPolyTime (fun ⟨n, pk, m₀, m₁⟩ => validBoundedWords maxLen n pk m₀ m₁)
      (encChallengePairInput encBits) encBool := by
  unfold validBoundedWords
  polytime

/-! ### Saved state and coordinate hybrid reduction -/

/-- Saved state passed from `choose` to `guess` in `bitwiseToSingleAt` and `bitwiseToSingle`. -/
private structure BitwiseToSingleState where
  /-- Whether the challenge pair was admissible and `split` fell within `m₀` and `maxLen n`. -/
  active : Bool
  /-- Public key forwarded to encrypt the prefix and suffix bits in `guess`. -/
  pk : List Bool
  /-- Prefix `m₁.take split` encrypted before the challenge ciphertext. -/
  front : List Bool
  /-- Suffix `m₀.drop (split + 1)` encrypted after the challenge ciphertext. -/
  back : List Bool
  /-- Saved state word of the underlying word adversary. -/
  stateA : List Bool

/-- Framing encoding of `BitwiseToSingleState`. -/
private enc_structure encBitwiseToSingleState : BitwiseToSingleState where
  active : encBool, pk : encBits, front : encBits, back : encBits, stateA : encBits

/-- Total polynomial-time decoder for `encBitwiseToSingleState`. -/
private def bitwiseToSingleStateDecoder : Decoder encBitwiseToSingleState :=
  (Decoder.bool.pair (Decoder.bits.pair (Decoder.bits.pair
    (Decoder.bits.pair Decoder.bits)))).map
    (fun (active, pk, front, back, stateA) => ⟨active, pk, front, back, stateA⟩)
    (fun s => (s.active, s.pk, s.front, s.back, s.stateA)) (fun _ => rfl) (fun _ => rfl)

/-- Encoded inactive state returned when `valid` fails or `split` is out of range. -/
private def rejectBitwiseToSingleState : List Bool :=
  encBitwiseToSingleState ⟨false, [], [], [], []⟩

@[simp] private theorem decode_rejectBitwiseToSingleState :
    bitwiseToSingleStateDecoder.decode rejectBitwiseToSingleState = ⟨false, [], [], [], []⟩ :=
  bitwiseToSingleStateDecoder.decode_enc ⟨false, [], [], [], []⟩

/-- Single-bit chosen-message adversary wrapping `adversary : WordAdversary` at a fixed coordinate
`split : ℕ`. On admissible challenges with `split < m₀.length` and `split < maxLen n`, `choose`
submits `(m₀[split], m₁[split])` and saves `pk`, `m₁.take split`, `m₀.drop (split + 1)` and
`adversary`'s state; `guess` encrypts the prefix and suffix under `pk` and splices the challenge
ciphertext between them. -/
noncomputable def bitwiseToSingleAt
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (maxLen : ℕ → ℕ) (adversary : WordAdversary) (split : ℕ) : Adversary where
  choose n pk := do
    let choice ← adversary.choose n pk
    let m₀ := ChoiceOut.msg₀ choice
    let m₁ := ChoiceOut.msg₁ choice
    if valid n pk m₀ m₁ && decide (split < m₀.length) && decide (split < maxLen n) then
      return ((m₀.getD split false, m₁.getD split false),
        encBitwiseToSingleState ⟨true, pk, m₁.take split, m₀.drop (split + 1),
          ChoiceOut.state choice⟩)
    else
      return ((false, false), rejectBitwiseToSingleState)
  guess n state ct :=
    let decoded := bitwiseToSingleStateDecoder.decode state
    if decoded.active then do
      let front ← decoded.front.mapM (encrypt n decoded.pk)
      let back ← decoded.back.mapM (encrypt n decoded.pk)
      adversary.guess n decoded.stateA (encList encBits (front ++ ct :: back))
    else
      pure false

/-- Uniform strict-PPT single-bit chosen-message adversary wrapping `adversary : WordAdversary`,
sampling the coordinate `split` via `ProbComp.sampleDyadicIndex (maxLen n)`. -/
noncomputable def bitwiseToSingle
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (maxLen : ℕ → ℕ) (adversary : WordAdversary) : Adversary where
  choose n pk := do
    let split ← ProbComp.sampleDyadicIndex (maxLen n)
    (bitwiseToSingleAt valid encrypt maxLen adversary split).choose n pk
  guess n state ct :=
    (bitwiseToSingleAt valid encrypt maxLen adversary 0).guess n state ct

/-! ### Uniform strict PPT certificates -/

private theorem isPPTOn_bitwiseToSingleAt_choose
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {maxLen : ℕ → ℕ} {adversary : WordAdversary}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encBits) encBool)
    (hmax : ComputableInPolyTime maxLen encUnary encUnary)
    (hadversary : adversary.IsPPT) :
    IsPPTOn (encPair (encPair encUnary encBits) encUnary) (encChoiceOut encBool)
      (fun p => (bitwiseToSingleAt valid encrypt maxLen adversary p.2).choose p.1.1 p.1.2) := by
  let EIn := encPair (encPair encUnary encBits) encUnary
  let EMid := encPair EIn (encChoiceOut encBits)
  have hchoose : IsPPTOn EIn (encChoiceOut encBits)
      (fun p : (ℕ × List Bool) × ℕ => adversary.choose p.1.1 p.1.2) :=
    hadversary.choose.on.preprocess (ComputableInPolyTime.fst (encPair encUnary encBits) encUnary)
  have hcp : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ℕ) × ChoiceOut (List Bool) =>
        (q.1.1.1, q.1.1.2, ChoiceOut.msg₀ q.2, ChoiceOut.msg₁ q.2))
      EMid (encChallengePairInput encBits) := by
    dsimp only [EMid, EIn, encChallengePairInput, encChoiceOut]; fun_prop
  have hv := hvalid.comp hcp
  have hltMsg : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ℕ) × ChoiceOut (List Bool) =>
        decide (q.1.2 < (ChoiceOut.msg₀ q.2).length))
      EMid encBool := by
    dsimp only [EMid, EIn, encChoiceOut]; polytime
  have hltMax : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ℕ) × ChoiceOut (List Bool) =>
        decide (q.1.2 < maxLen q.1.1.1))
      EMid encBool := by
    dsimp only [EMid, EIn]; polytime
  have hcond : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ℕ) × ChoiceOut (List Bool) =>
        valid q.1.1.1 q.1.1.2 (ChoiceOut.msg₀ q.2) (ChoiceOut.msg₁ q.2) &&
          decide (q.1.2 < (ChoiceOut.msg₀ q.2).length) && decide (q.1.2 < maxLen q.1.1.1))
      EMid encBool :=
    ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.bool_and.comp (hv.prod hltMsg)).prod hltMax)
  have hrec : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ℕ) × ChoiceOut (List Bool) =>
        (⟨true, q.1.1.2, (ChoiceOut.msg₁ q.2).take q.1.2,
          (ChoiceOut.msg₀ q.2).drop (q.1.2 + 1), ChoiceOut.state q.2⟩ : BitwiseToSingleState))
      EMid encBitwiseToSingleState :=
    encBitwiseToSingleState_mk_polyTime (ComputableInPolyTime.const true)
      (by dsimp only [EMid, EIn]; fun_prop)
      (by dsimp only [EMid, EIn, encChoiceOut]; fun_prop)
      (by dsimp only [EMid, EIn, encChoiceOut]; fun_prop)
      (by dsimp only [EMid, encChoiceOut]; fun_prop)
  have hmsgs : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × ℕ) × ChoiceOut (List Bool) =>
        ((ChoiceOut.msg₀ q.2).getD q.1.2 false, (ChoiceOut.msg₁ q.2).getD q.1.2 false))
      EMid (encPair encBool encBool) := by
    dsimp only [EMid, EIn, encChoiceOut]; fun_prop
  have hpost := ComputableInPolyTime.ite hcond (hmsgs.prod hrec.encoding_comp)
    (.const ((false, false), rejectBitwiseToSingleState))
  exact (hchoose.bind_with
    (second := fun p choice =>
      pure (if valid p.1.1 p.1.2 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) &&
          decide (p.2 < (ChoiceOut.msg₀ choice).length) && decide (p.2 < maxLen p.1.1) then
        (((ChoiceOut.msg₀ choice).getD p.2 false, (ChoiceOut.msg₁ choice).getD p.2 false),
          encBitwiseToSingleState ⟨true, p.1.2, (ChoiceOut.msg₁ choice).take p.2,
            (ChoiceOut.msg₀ choice).drop (p.2 + 1), ChoiceOut.state choice⟩)
      else
        ((false, false), rejectBitwiseToSingleState))) hpost.isPPTOn).congr fun p => by
    simp only [bitwiseToSingleAt, ProbComp.eval_bind, ProbComp.eval_pure,
      apply_ite ProbComp.eval, apply_ite PMF.pure]

/-- `bitwiseToSingleAt` is uniformly strict PPT whenever `valid` and `maxLen` are computable in
polynomial time and `encrypt` and `adversary` are strict PPT. -/
theorem isPPT_bitwiseToSingleAt
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {maxLen : ℕ → ℕ} {adversary : WordAdversary}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encBits) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, k, b⟩ => encrypt n k b))
    (hmax : ComputableInPolyTime maxLen encUnary encUnary)
    (hadversary : adversary.IsPPT) (split : ℕ) :
    (bitwiseToSingleAt valid encrypt maxLen adversary split).IsPPT where
  choose :=
    (isPPTOn_bitwiseToSingleAt_choose hvalid hmax hadversary).preprocess
      (ComputableInPolyTime.id'.prod (ComputableInPolyTime.const split))
  guess := by
    let E1 := encPair encGuessInput (encList encBits)
    let E2 := encPair E1 (encList encBits)
    have hdec : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => bitwiseToSingleStateDecoder.decode p.2.1)
        encGuessInput encBitwiseToSingleState :=
      bitwiseToSingleStateDecoder.computableInPolyTime.comp
        (by dsimp only [encGuessInput]; fun_prop)
    have hpk := encBitwiseToSingleState_pk_polyTime hdec
    have hfrontBits := encBitwiseToSingleState_front_polyTime hdec
    have hbackBits := encBitwiseToSingleState_back_polyTime hdec
    have hstateA := encBitwiseToSingleState_stateA_polyTime hdec
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.1)
        encGuessInput encUnary := by dsimp only [encGuessInput]; fun_prop
    have hstep₀ : IsPPTOn (encPair encGuessInput encBool) encBits
        (fun q => encrypt q.1.1 (bitwiseToSingleStateDecoder.decode q.1.2.1).pk q.2) :=
      hencrypt.preprocess
        ((hn.comp (ComputableInPolyTime.fst encGuessInput encBool)).prod
          ((hpk.comp (ComputableInPolyTime.fst encGuessInput encBool)).prod
            (ComputableInPolyTime.snd encGuessInput encBool)))
    have hfront : IsPPTOn encGuessInput (encList encBits)
        (fun p => (bitwiseToSingleStateDecoder.decode p.2.1).front.mapM
          (encrypt p.1 (bitwiseToSingleStateDecoder.decode p.2.1).pk)) :=
      IsPPTOn.mapMWith hstep₀ (ComputableInPolyTime.bitsToList.comp hfrontBits)
    have hp1 := ComputableInPolyTime.fst encGuessInput (encList encBits)
    have hstep₁ : IsPPTOn (encPair E1 encBool) encBits
        (fun q => encrypt q.1.1.1 (bitwiseToSingleStateDecoder.decode q.1.1.2.1).pk q.2) :=
      hencrypt.preprocess
        (((hn.comp hp1).comp (ComputableInPolyTime.fst E1 encBool)).prod
          (((hpk.comp hp1).comp (ComputableInPolyTime.fst E1 encBool)).prod
            (ComputableInPolyTime.snd E1 encBool)))
    have hback : IsPPTOn E1 (encList encBits)
        (fun q => (bitwiseToSingleStateDecoder.decode q.1.2.1).back.mapM
          (encrypt q.1.1 (bitwiseToSingleStateDecoder.decode q.1.2.1).pk)) :=
      IsPPTOn.mapMWith hstep₁ (ComputableInPolyTime.bitsToList.comp (hbackBits.comp hp1))
    have hp2 := ComputableInPolyTime.fst E1 (encList encBits)
    have hct : ComputableInPolyTime (fun r : ((ℕ × List Bool × List Bool) × List (List Bool)) ×
        List (List Bool) => r.1.1.2.2) E2 encBits := by
      dsimp only [E2, E1, encGuessInput]; fun_prop
    have hsplice : ComputableInPolyTime
        (fun r : ((ℕ × List Bool × List Bool) × List (List Bool)) × List (List Bool) =>
          encList encBits (r.1.2 ++ r.1.1.2.2 :: r.2))
        E2 encBits :=
      ((ComputableInPolyTime.listAppend encBits).comp
        (((ComputableInPolyTime.snd encGuessInput (encList encBits)).comp hp2).prod
          ((ComputableInPolyTime.cons encBits).comp
            (hct.prod (ComputableInPolyTime.snd E1 (encList encBits)))))).encoding_comp
    have hguessArg : ComputableInPolyTime
        (fun r : ((ℕ × List Bool × List Bool) × List (List Bool)) × List (List Bool) =>
          (r.1.1.1, (bitwiseToSingleStateDecoder.decode r.1.1.2.1).stateA,
            encList encBits (r.1.2 ++ r.1.1.2.2 :: r.2)))
        E2 encGuessInput :=
      ((hn.comp hp1).comp hp2).prod (((hstateA.comp hp1).comp hp2).prod hsplice)
    have hguess := hadversary.guess.preprocess hguessArg
    simpa only [bitwiseToSingleAt] using IsPPTOn.cond
      (encBitwiseToSingleState_active_polyTime hdec)
      (hfront.bind_with (hback.bind_with hguess))
      (ComputableInPolyTime.const false).isPPTOn

/-- `bitwiseToSingle` is uniformly strict PPT whenever `valid` and `maxLen` are computable in
polynomial time and `encrypt` and `adversary` are strict PPT. -/
theorem isPPT_bitwiseToSingle
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {maxLen : ℕ → ℕ} {adversary : WordAdversary}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encBits) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, k, b⟩ => encrypt n k b))
    (hmax : ComputableInPolyTime maxLen encUnary encUnary)
    (hadversary : adversary.IsPPT) :
    (bitwiseToSingle valid encrypt maxLen adversary).IsPPT where
  choose := by
    have hsample : IsPPTOn (encPair encUnary encBits) encUnary
        (fun p : ℕ × List Bool => ProbComp.sampleDyadicIndex (maxLen p.1)) :=
      isPPTOn_sampleDyadicIndex (hmax.comp (ComputableInPolyTime.fst encUnary encBits))
    exact hsample.bind_with (isPPTOn_bitwiseToSingleAt_choose hvalid hmax hadversary)
  guess := (isPPT_bitwiseToSingleAt hvalid hencrypt hmax hadversary 0).guess

/-! ### Coordinate hybrid games and exact advantage identity -/

/-- Coordinate hybrid experiment at `split : ℕ`: on admissible challenges `(m₀, m₁)`, encrypt the
mixed word `m₁.take split ++ m₀.drop split` with `bitwiseEncrypt encrypt`. -/
noncomputable def bitwiseHybridGameOn
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : WordAdversary) (split n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choice ← adversary.choose n keys.1
  let m₀ := ChoiceOut.msg₀ choice
  let m₁ := ChoiceOut.msg₁ choice
  if valid n keys.1 m₀ m₁ then
    let ct ← bitwiseEncrypt encrypt n keys.1 (m₁.take split ++ m₀.drop split)
    adversary.guess n (ChoiceOut.state choice) ct
  else
    return false

/-- At `split = 0`, `bitwiseHybridGameOn` is the `false` side of `gameOn`. -/
@[simp] theorem eval_bitwiseHybridGameOn_zero
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : WordAdversary) (n : ℕ) :
    ProbComp.eval (bitwiseHybridGameOn valid keyGen encrypt adversary 0 n) =
      ProbComp.eval (gameOn valid keyGen (bitwiseEncrypt encrypt) adversary false n) := by
  simp only [bitwiseHybridGameOn, gameOn, List.take_zero, List.drop_zero, List.nil_append,
    Bool.false_eq_true, ↓reduceIte, ChoiceOut.state]

/-- When every admissible challenge pair on supported keys has equal lengths at most `split`,
`bitwiseHybridGameOn` at `split` is the `true` side of `gameOn`. -/
theorem eval_bitwiseHybridGameOn_of_le
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (adversary : WordAdversary) {split n : ℕ}
    (hlen : ∀ keys ∈ (ProbComp.eval (keyGen n)).support, ∀ m₀ m₁,
      valid n keys.1 m₀ m₁ = true → m₀.length = m₁.length ∧ m₀.length ≤ split) :
    ProbComp.eval (bitwiseHybridGameOn valid keyGen encrypt adversary split n) =
      ProbComp.eval (gameOn valid keyGen (bitwiseEncrypt encrypt) adversary true n) := by
  simp only [bitwiseHybridGameOn, gameOn, pmf_norm, ↓reduceIte, ChoiceOut.state]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun keys hkeys =>
    congrArg (PMF.bind _) (funext fun choice => ?_)
  by_cases hv : valid n keys.1 (ChoiceOut.msg₀ choice) (ChoiceOut.msg₁ choice) = true
  · obtain ⟨heq, hle⟩ := hlen keys hkeys _ _ hv
    have hle₁ : (ChoiceOut.msg₁ choice).length ≤ split := heq ▸ hle
    simp only [hv, ↓reduceIte, List.take_of_length_le hle₁, List.drop_eq_nil_of_le hle,
      List.append_nil]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]

/-- Single-coordinate hybrid step for `bitwiseHybridGameOn`: for `split < maxLen n`, whenever
admissible challenges on supported keys have equal lengths, the signed gap between
`bitwiseHybridGameOn` at `split` and at `split + 1` equals the signed single-bit gap of
`bitwiseToSingleAt ... split`. -/
theorem bitwiseHybridGameOn_step_gap
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (maxLen : ℕ → ℕ) (adversary : WordAdversary) {split n : ℕ} (hlt : split < maxLen n)
    (heqLen : ∀ keys ∈ (ProbComp.eval (keyGen n)).support, ∀ m₀ m₁,
      valid n keys.1 m₀ m₁ = true → m₀.length = m₁.length) :
    (Game.succProbability
        (ProbComp.eval (bitwiseHybridGameOn valid keyGen encrypt adversary split n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval (bitwiseHybridGameOn valid keyGen encrypt adversary (split + 1) n)) =
      (Game.succProbability
        (ProbComp.eval
          (game keyGen encrypt
            (bitwiseToSingleAt valid encrypt maxLen adversary split) false n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (game keyGen encrypt
            (bitwiseToSingleAt valid encrypt maxLen adversary split) true n)) := by
  rw [sub_eq_sub_iff_add_eq_add, Game.coe_succProbability, Game.coe_succProbability,
    Game.coe_succProbability, Game.coe_succProbability,
    ← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    ← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  refine congrArg ENNReal.toReal ?_
  simp only [bitwiseHybridGameOn, game, gameOn, bitwiseToSingleAt, decide_eq_true hlt,
    Bool.and_true, pmf_norm, ↓reduceIte, Bool.false_eq_true, apply_ite ProbComp.eval]
  refine PMF.bind_apply_add_eq_on_support fun keys hkeys =>
    PMF.bind_apply_add_eq_on_support fun choice _ => ?_
  let m₀ := ChoiceOut.msg₀ choice
  let m₁ := ChoiceOut.msg₁ choice
  by_cases hv : valid n keys.1 m₀ m₁ = true
  · have hlenEq : m₀.length = m₁.length := heqLen keys hkeys m₀ m₁ hv
    by_cases hs : split < m₀.length
    · have hs₁ : split < m₁.length := hlenEq ▸ hs
      simp only [m₀, m₁, hv, decide_eq_true hs, Bool.and_self, ↓reduceIte,
        PMF.pure_bind, ChoiceOut.msg₀_mk, ChoiceOut.msg₁_mk,
        bitwiseToSingleStateDecoder.decode_enc]
      have hsplice (b : Bool) (word : List Bool)
          (hword : m₁.take split ++ b :: m₀.drop (split + 1) = word) :
          (ProbComp.eval (encrypt n keys.1 b)).bind (fun ct =>
            (ProbComp.eval ((m₁.take split).mapM (encrypt n keys.1))).bind fun front =>
              (ProbComp.eval ((m₀.drop (split + 1)).mapM (encrypt n keys.1))).bind fun back =>
                ProbComp.eval (adversary.guess n (ChoiceOut.state choice)
                  (encList encBits (front ++ ct :: back)))) =
            (ProbComp.eval (bitwiseEncrypt encrypt n keys.1 word)).bind
              (fun ct => ProbComp.eval (adversary.guess n (ChoiceOut.state choice) ct)) := by
        have hsp := ProbComp.eval_mapM_splice (encrypt n keys.1) (m₁.take split) b
          (m₀.drop (split + 1))
        simp only [ProbComp.eval_bind, ProbComp.eval_pure] at hsp
        have hbind := congrArg (fun p : PMF (List (List Bool)) =>
          p.bind fun cts => ProbComp.eval (adversary.guess n (ChoiceOut.state choice)
            (encList encBits cts))) hsp
        simpa only [PMF.bind_bind, PMF.pure_bind, bitwiseEncrypt, ProbComp.eval_map,
          PMF.bind_map, Function.comp_def, hword] using hbind
      have hw₀ : m₁.take split ++ m₀.getD split false :: m₀.drop (split + 1) =
          m₁.take split ++ m₀.drop split := by
        rw [List.getD_eq_getElem _ _ hs, List.getElem_cons_drop]
      have hw₁ : m₁.take split ++ m₁.getD split false :: m₀.drop (split + 1) =
          m₁.take (split + 1) ++ m₀.drop (split + 1) := by
        rw [List.getD_eq_getElem _ _ hs₁, ← List.singleton_append, ← List.append_assoc,
          List.take_append_getElem]
      rw [hsplice _ _ hw₁, hsplice _ _ hw₀, add_comm]
    · have hle₀ : m₀.length ≤ split := Nat.le_of_not_lt hs
      have hle₁ : m₁.length ≤ split := hlenEq ▸ hle₀
      simp only [m₀, m₁, hv, decide_eq_false hs, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        PMF.pure_bind, ChoiceOut.msg₀_mk, ChoiceOut.msg₁_mk,
        decode_rejectBitwiseToSingleState, PMF.bind_const,
        List.take_of_length_le hle₁, List.take_of_length_le (hle₁.trans (Nat.le_succ _)),
        List.drop_eq_nil_of_le hle₀, List.drop_eq_nil_of_le (hle₀.trans (Nat.le_succ _))]
      exact add_comm _ _
  · simp only [m₀, m₁, hv, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      PMF.pure_bind, ChoiceOut.msg₀_mk, ChoiceOut.msg₁_mk,
      decode_rejectBitwiseToSingleState, PMF.bind_const]

/-- Running `bitwiseToSingle` in `game` averages `bitwiseToSingleAt` uniformly over
`Fin (dyadicSize (maxLen n))`, padding indices `i.val ≥ maxLen n` with `PMF.pure false`. -/
theorem eval_game_bitwiseToSingle
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (maxLen : ℕ → ℕ) (adversary : WordAdversary) (bit : Bool) (n : ℕ) :
    ProbComp.eval (game keyGen encrypt (bitwiseToSingle valid encrypt maxLen adversary) bit n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (maxLen n)))).bind fun i =>
        if i.val < maxLen n then
          ProbComp.eval
            (game keyGen encrypt (bitwiseToSingleAt valid encrypt maxLen adversary i.val) bit n)
        else PMF.pure false := by
  simp only [game, gameOn, bitwiseToSingle, pmf_norm, ↓reduceIte]
  rw [PMF.bind_comm]
  simp only [ProbComp.eval_sampleDyadicIndex, PMF.bind_map, Function.comp_def]
  congr 1 with i
  by_cases hi : i.val < maxLen n
  · simp only [hi, ↓reduceIte]; rfl
  · rw [ite_eq_right_of_eq_false (c := i.val < maxLen n) (h := eq_false hi)]
    simp only [bitwiseToSingleAt, decide_eq_false hi, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, pmf_norm, decode_rejectBitwiseToSingleState, PMF.bind_const]

/-- Coordinate-hybrid reduction step for `bitwiseEncrypt`: when every admissible challenge pair on
supported keys has equal lengths at most `maxLen n`, the word adversary's chosen-message advantage
against `bitwiseEncrypt encrypt` equals `dyadicSize (maxLen n)` times the single-bit advantage of
`bitwiseToSingle valid encrypt maxLen adversary`. -/
theorem advantage_bitwiseEncrypt_eq
    (valid : ℕ → List Bool → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (maxLen : ℕ → ℕ) (adversary : WordAdversary) (n : ℕ)
    (hlen : ∀ keys ∈ (ProbComp.eval (keyGen n)).support, ∀ m₀ m₁,
      valid n keys.1 m₀ m₁ = true → m₀.length = m₁.length ∧ m₀.length ≤ maxLen n) :
    advantage (gameOn valid keyGen (bitwiseEncrypt encrypt) adversary) n =
      dyadicSize (maxLen n) *
        advantage (game keyGen encrypt (bitwiseToSingle valid encrypt maxLen adversary)) n := by
  have hred := Game.succProbability_hybrid_reduction
    (games := fun split =>
      ProbComp.eval (bitwiseHybridGameOn valid keyGen encrypt adversary split n))
    (game1 := fun split => ProbComp.eval
      (game keyGen encrypt (bitwiseToSingleAt valid encrypt maxLen adversary split) false n))
    (game2 := fun split => ProbComp.eval
      (game keyGen encrypt (bitwiseToSingleAt valid encrypt maxLen adversary split) true n))
    (maxLen n) (dyadicSize (maxLen n)) (lt_dyadicSize (maxLen n)).le 1
    (fun split hs => by
      rw [one_mul]
      exact bitwiseHybridGameOn_step_gap valid keyGen encrypt maxLen adversary hs
        fun keys hkeys m₀ m₁ hv => (hlen keys hkeys m₀ m₁ hv).1)
  rw [eval_bitwiseHybridGameOn_zero, eval_bitwiseHybridGameOn_of_le valid keyGen encrypt adversary
    hlen, mul_one] at hred
  simp only [advantage]
  rw [eval_game_bitwiseToSingle, eval_game_bitwiseToSingle]
  apply NNReal.eq
  rw [NNReal.coe_mul, Game.coe_advantage, Game.coe_advantage, NNReal.coe_natCast, hred,
    abs_mul, Nat.abs_cast]

/-! ### Asymptotic 1-bit-to-multi-bit chosen-plaintext security -/

/-- Bounded-length bitwise hybrid step: for any polynomial-time admissibility predicate `valid` and
unary polynomial-time length schedule `maxLen` such that admissible pairs on supported keys have
equal lengths at most `maxLen n`, single-bit `INDCPA keyGen encrypt` and strict-PPT `encrypt` imply
`INDCPAOn valid encBits keyGen (bitwiseEncrypt encrypt)`. Nothing is assumed about `keyGen`. -/
theorem INDCPA.indcpaOn_bitwiseEncrypt
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {maxLen : ℕ → ℕ}
    (hvalid : ComputableInPolyTime (fun ⟨n, k, m₀, m₁⟩ => valid n k m₀ m₁)
      (encChallengePairInput encBits) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, k, b⟩ => encrypt n k b))
    (hmax : ComputableInPolyTime maxLen encUnary encUnary)
    (hlen : ∀ n, ∀ keys ∈ (ProbComp.eval (keyGen n)).support, ∀ m₀ m₁,
      valid n keys.1 m₀ m₁ = true → m₀.length = m₁.length ∧ m₀.length ≤ maxLen n)
    (h : INDCPA keyGen encrypt) :
    INDCPAOn valid encBits keyGen (bitwiseEncrypt encrypt) := by
  intro adversary hadversary
  have hsingle := h (bitwiseToSingle valid encrypt maxLen adversary)
    (isPPT_bitwiseToSingle hvalid hencrypt hmax hadversary)
  negligible using fun n =>
    (advantage_bitwiseEncrypt_eq valid keyGen encrypt maxLen adversary n (hlen n)).le

/-- For any word encryption `encWord` and key generator `keyGen` whose supported public keys have
polynomially bounded bit-length `pkBound n`, chosen-plaintext security on
`validBoundedWords maxLen` for every unary polynomial-time length cap `maxLen : ℕ → ℕ` implies full
`WordINDCPA keyGen encWord`. -/
theorem wordINDCPA_of_indcpaOn_validBoundedWords
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encWord : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {pkBound : ℕ → ℕ}
    (hpkBound : Cslib.PolynomiallyBounded pkBound)
    (hpkLen : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support → keys.1.length ≤ pkBound n)
    (hbounded : ∀ (maxLen : ℕ → ℕ), ComputableInPolyTime maxLen encUnary encUnary →
      INDCPAOn (validBoundedWords maxLen) encBits keyGen encWord) :
    WordINDCPA keyGen encWord := by
  intro adversary hadversary
  obtain ⟨ck, dk, hpkPoly⟩ := Cslib.polynomiallyBounded_iff_le.mp hpkBound
  obtain ⟨ca, da, hchooseLen⟩ := hadversary.choose.on.length_le
  let maxLen (n : ℕ) : ℕ := ca * (2 * n + 2 * (ck * (n + 1) ^ dk) + 4) ^ da
  have hmax : ComputableInPolyTime maxLen encUnary encUnary := by
    dsimp only [maxLen]; fun_prop
  have hAdv := hbounded maxLen hmax adversary hadversary
  have heqGame (bit : Bool) (n : ℕ) :
      ProbComp.eval (gameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) keyGen
        encWord adversary bit n) =
      ProbComp.eval (gameOn (validBoundedWords maxLen) keyGen
        encWord adversary bit n) := by
    simp only [gameOn, pmf_norm, apply_ite ProbComp.eval]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun keys hkeys =>
      Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun choice hchoice => ?_
    have hmsgLen : (ChoiceOut.msg₀ choice).length ≤ maxLen n := by
      have hout := hchooseLen (n, keys.1) choice hchoice
      have hk : keys.1.length ≤ ck * (n + 1) ^ dk := (hpkLen n keys hkeys).trans (hpkPoly n)
      have hin : (encPair encUnary encBits (n, keys.1)).length + 1 ≤
          2 * n + 2 * (ck * (n + 1) ^ dk) + 4 := by
        enc_len
      have hm₀ : (ChoiceOut.msg₀ choice).length ≤ (encChoiceOut encBits choice).length := by
        dsimp only [ChoiceOut.msg₀, ChoiceOut.msgs]; enc_len
      exact hm₀.trans (hout.trans (Nat.mul_le_mul_left ca (Nat.pow_le_pow_left hin da)))
    simp only [validBoundedWords, decide_eq_true hmsgLen, Bool.and_true]
  simpa only [heqGame] using hAdv

/-- Public-key-bounded bitwise hybrid step: when every public key produced by `keyGen n` has bit
length at most `pkBound n` for a polynomially bounded function `pkBound` (which need not be
computable), every uniform strict-PPT word adversary's chosen messages are bounded by an explicit
unary polynomial-time schedule in `n`, so single-bit `INDCPA keyGen encrypt` and strict-PPT
`encrypt` imply `WordINDCPA keyGen (bitwiseEncrypt encrypt)`. -/
theorem INDCPA.wordINDCPA_bitwiseEncrypt_of_publicKey_length_le
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {pkBound : ℕ → ℕ}
    (hpkBound : Cslib.PolynomiallyBounded pkBound)
    (hpkLen : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support → keys.1.length ≤ pkBound n)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, k, b⟩ => encrypt n k b))
    (h : INDCPA keyGen encrypt) :
    WordINDCPA keyGen (bitwiseEncrypt encrypt) :=
  wordINDCPA_of_indcpaOn_validBoundedWords hpkBound hpkLen fun maxLen hmax =>
    h.indcpaOn_bitwiseEncrypt (computableInPolyTime_validBoundedWords hmax) hencrypt hmax
      fun _ _ _ _ _ hv => by
        simpa only [validBoundedWords, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hv

/-- Single-challenge bitwise reduction step (library infrastructure after [KatzLindell2020],
Section 12.2.2, locator not verified, rather than Theorem 12.6's multi-encryption oracle endpoint;
cf. [BonehShoup2023], Section 11.3.2, which lifts single- to multi-challenge CPA security over one
message space `M` rather than `{0, 1} → {0, 1}^ℓ`): when `keyGen` and `encrypt` are uniform strict
PPT, single-bit `INDCPA keyGen encrypt` implies `WordINDCPA keyGen (bitwiseEncrypt encrypt)`. -/
theorem INDCPA.wordINDCPA_bitwiseEncrypt
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits (fun ⟨n, k, b⟩ => encrypt n k b))
    (h : INDCPA keyGen encrypt) :
    WordINDCPA keyGen (bitwiseEncrypt encrypt) := by
  obtain ⟨c, d, hcap, hbound⟩ := exists_keyLength_bound hkeyGen
  exact h.wordINDCPA_bitwiseEncrypt_of_publicKey_length_le hcap.polynomiallyBounded
    (fun n keys hkeys => (Nat.le_add_right _ _).trans (hbound n keys hkeys)) hencrypt

end Cslib.Crypto.Encryption

/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.Signature.Bridge
public import CslibFrontier.Crypto.Game.Concrete
public import CslibFrontier.Crypto.Protocols.AnonymousToken.RandomTarget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Polynomial-time random-target reduction witnesses for anonymous tokens

This module provides uniform strict oracle-PPT realizations, an original extracted-model
word-level security theorem, and a query-bounded transfer lemma for
`Cslib.Crypto.AnonymousToken.reduceRedemptions`
(`CslibFrontier/Crypto/Protocols/AnonymousToken/RandomTarget.lean`).

Word-level adversaries operate on uniform `List Bool` encodings over a typed message family
`Message n` and challenge count `N n` varying with the security parameter `n : ℕ`:

* Adversaries receive `encWordTargetsInput ⟨pk, List.ofFn targets⟩`, whose length is at least
  `N n`. Because `IsOraclePPT` clocks every adversary in time polynomial in `n + input.length`,
  both `WordRedemptionAdversary` and `WordOneMoreAdversary` (as well as `reduceRedemptionsWord`)
  run in time polynomial in `n + N n`. Computational `oneMoreWordGame` / `WordOneMoreUnforgeable`
  therefore models polynomial-time one-more hardness when `N n` is polynomially bounded in `n`,
  whereas super-polynomial `N n` allows `2^{O(n)}`-time adversaries.
* `slotWord : ℕ → List Bool → ℕ` realizes `slot n : Message n ↪ Fin (N n)` in binary (`encNat`)
  polynomial time so individual `(index, preimage)` claim words stay logarithmic in `N n` (this
  keeps claim slots short without compressing the `N n`-element target vector input).
* Total decoding and out-of-range claim rejection: `WordRedemptionAdversary.toTyped` and
  `WordOneMoreAdversary.toTyped` process every output word as the typed value returned by its
  total decoder (`dec n` for redemption messages; `wordClaimListDecoder` via
  `Decoder.list (Decoder.pair Decoder.nat Decoder.bits)` for claim lists), rather than rejecting
  malformed non-codewords under a `PartialDecoder`. Because `Decoder.list` splits arbitrary bit
  strings via `frames` and decodes each frame pair with `(Decoder.nat, Decoder.bits)`, malformed
  claim-list words still yield typed claim lists depending on the input. `wordClaimListDecoder`
  then rejects the entire claim list (`none`, mapping to `[]`, failing `Signature.oneMoreAccept`)
  if any decoded claim index satisfies `i ≥ N n`, with no modular wraparound or element filtering.
* `reduceRedemptionsWord` preserves both `IsOraclePPT` (`isOraclePPT_reduceRedemptionsWord`) and
  input-uniform query bounds (`withinWordQueries_reduceRedemptionsWord`), and matches
  `RandomTarget.reduceRedemptions` in exact `PMF` law inside `oneMoreWordGame`
  (`eval_oneMoreWordGame_reduceRedemptionsWord_eq`).

## Main definitions

* `Cslib.Crypto.AnonymousToken.encRedemptionPayload`,
  `Cslib.Crypto.AnonymousToken.encRedemptionToken`,
  `Cslib.Crypto.AnonymousToken.encRedemptionTokenList`: encodings for unit-opening redemption
  tokens.
* `Cslib.Crypto.AnonymousToken.WordClaim`, `Cslib.Crypto.AnonymousToken.encWordClaim`,
  `Cslib.Crypto.AnonymousToken.encWordClaimList`,
  `Cslib.Crypto.AnonymousToken.WordTargetsInput`, `Cslib.Crypto.AnonymousToken.encWordTargetsInput`,
  `Cslib.Crypto.AnonymousToken.wordTargetsInputDecoder`: named-field structures, encodings, and
  total input decoder for `(index, preimage)` claims and `(pk, targets)` inputs (keeping the
  pair word layouts unchanged).
* `Cslib.Crypto.AnonymousToken.wordClaimListDecoder`: checked claim-list decoder rejecting any
  out-of-range index `i ≥ N`.
* `Cslib.Crypto.AnonymousToken.WordRedemptionAdversary`,
  `Cslib.Crypto.AnonymousToken.WordOneMoreAdversary`,
  `Cslib.Crypto.AnonymousToken.reduceRedemptionsWord`: word-level adversary types and uniform
  word realization of `RandomTarget.reduceRedemptions`.
* `Cslib.Crypto.AnonymousToken.extractedRedemptionWordGame`,
  `Cslib.Crypto.AnonymousToken.oneMoreWordGame`,
  `Cslib.Crypto.AnonymousToken.WordOneMoreUnforgeable`: word-level extracted redemption and
  fixed-budget one-more games and the `novel` word-level one-more unforgeability premise.
* `Cslib.Crypto.AnonymousToken.WithinWordQueries`: input-uniform signing-query bound predicate.

## Main results

* `Cslib.Crypto.AnonymousToken.isOraclePPT_reduceRedemptionsWord`: uniform strict `IsOraclePPT`
  runtime certificate for `reduceRedemptionsWord`.
* `Cslib.Crypto.AnonymousToken.eval_oneMoreWordGame_reduceRedemptionsWord_eq`: exact `PMF` law
  equality against `Signature.oneMoreExperiment`.
* `Cslib.Crypto.AnonymousToken.extractedRedemptionWordGame_succProbability_le`: finite
  success-probability bound against `oneMoreWordGame`.
* `Cslib.Crypto.AnonymousToken.negligible_extractedRedemptionWordGame_of_wordOneMoreUnforgeable`:
  original asymptotic word-level redemption theorem assuming `WordOneMoreUnforgeable` against
  uniform strict `IsOraclePPT` adversaries.

## Query-bounded transfer lemma

* `Cslib.Crypto.AnonymousToken.withinWordQueries_reduceRedemptionsWord`,
  `Cslib.Crypto.AnonymousToken.succWithin_extractedRedemptionWordGame_withinQueries`: query-only
  transfer (`WithinWordQueries` bounds signing-oracle calls across inputs without bounding
  computational runtime).
-/

public section

namespace Cslib.Crypto.AnonymousToken

open Probability Turing.MultiTapeTM

/-! ### Encodings and checked claim-list decoders -/

section Encodings

variable {M : Type}

/-- Encode a unit-opening redemption payload `(message, ())` with `encUnit` opening. -/
enc_structure encRedemptionPayload (encM : M ↪ List Bool) : Payload M Unit where
  message : encM, opening : encUnit

attribute [fun_prop] encRedemptionPayload_message_polyTime encRedemptionPayload_opening_polyTime
  encRedemptionPayload_mk_polyTime

/-- Encode a unit-opening redemption token `(payload, signature)` with bit-string signature. -/
enc_structure encRedemptionToken (encM : M ↪ List Bool) : Token M Unit (List Bool) where
  payload : (encRedemptionPayload encM), signature : encBits

attribute [fun_prop] encRedemptionToken_payload_polyTime encRedemptionToken_signature_polyTime
  encRedemptionToken_mk_polyTime

/-- Encode a list of unit-opening redemption tokens. -/
abbrev encRedemptionTokenList (encM : M ↪ List Bool) :
    List (Token M Unit (List Bool)) ↪ List Bool :=
  encList (encRedemptionToken encM)

/-- Word-level one-more preimage claim pairing a challenge slot index with a candidate
signature word. -/
structure WordClaim where
  /-- Challenged slot index (encoded in binary `encNat`). -/
  index : ℕ
  /-- Candidate preimage/signature bit string (`encBits`). -/
  preimage : List Bool
  deriving DecidableEq

/-- Encode a `WordClaim` (`index` with `encNat`, `preimage` with `encBits`; identical word layout
to `encPair encNat encBits`). -/
enc_structure encWordClaim : WordClaim where
  index : encNat, preimage : encBits

attribute [fun_prop] encWordClaim_index_polyTime encWordClaim_preimage_polyTime
  encWordClaim_mk_polyTime

/-- Encode a list of binary-indexed `WordClaim` values. -/
abbrev encWordClaimList : List WordClaim ↪ List Bool :=
  encList encWordClaim

/-- Public `(pk, targets)` input passed to word-level redemption and one-more adversaries. -/
structure WordTargetsInput where
  /-- Encoded public key word (`encBits`). -/
  pk : List Bool
  /-- Encoded list of `N n` challenge target words (`encList encBits`). -/
  targets : List (List Bool)
  deriving DecidableEq

/-- Encode a `WordTargetsInput` (`pk` with `encBits`, `targets` with `encList encBits`; identical
word layout to `encPair encBits (encList encBits)`). -/
enc_structure encWordTargetsInput : WordTargetsInput where
  pk : encBits, targets : (encList encBits)

attribute [fun_prop] encWordTargetsInput_pk_polyTime encWordTargetsInput_targets_polyTime
  encWordTargetsInput_mk_polyTime

end Encodings

private def wordClaimDecoder : Decoder encWordClaim :=
  (Decoder.pair Decoder.nat Decoder.bits).map
    (fun p => ⟨p.1, p.2⟩) (fun c => (c.index, c.preimage)) (fun _ => rfl) (fun _ => rfl)

/-- Total decoder for `encWordTargetsInput`. -/
@[expose] def wordTargetsInputDecoder : Decoder encWordTargetsInput :=
  (Decoder.pair Decoder.bits (Decoder.list Decoder.bits)).map
    (fun p => ⟨p.1, p.2⟩) (fun x => (x.pk, x.targets)) (fun _ => rfl) (fun _ => rfl)

private def wordClaimListRawDecoder : Decoder encWordClaimList :=
  Decoder.list wordClaimDecoder

private def decodeWordClaimsChecked (N : ℕ) :
    List WordClaim → Option (List (Signature.PreimageClaim N (List Bool)))
  | [] => some []
  | c :: rest =>
    if h : c.index < N then
      (⟨⟨c.index, h⟩, c.preimage⟩ :: ·) <$> decodeWordClaimsChecked N rest
    else
      none

/-- Checked claim-list decoder at challenge size `N`: processes any bit string `w` through the
total decoder `Decoder.list (Decoder.pair Decoder.nat Decoder.bits)` (so malformed non-codewords
still yield decoded pairs depending on `w`), and rejects the entire claim list (`none`) whenever
any decoded pair has out-of-range index `i ≥ N`. -/
def wordClaimListDecoder (N : ℕ) (w : List Bool) :
    Option (List (Signature.PreimageClaim N (List Bool))) :=
  decodeWordClaimsChecked N (wordClaimListRawDecoder.decode w)

private theorem decodeWordClaimsChecked_map_fin {α : Type} (N : ℕ) (xs : List α)
    (idx : α → Fin N) (sig : α → List Bool) :
    decodeWordClaimsChecked N (xs.map fun x => (⟨(idx x).val, sig x⟩ : WordClaim)) =
      some (xs.map fun x => (⟨idx x, sig x⟩ : Signature.PreimageClaim N (List Bool))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [decodeWordClaimsChecked, ih]

/-- Whenever the underlying raw pair parse of `w` consists of pairs `(i, sig)` with `i < N`
(including when `w` is a malformed non-codeword), `wordClaimListDecoder N w` accepts and produces
the corresponding `Fin N` claims. -/
theorem wordClaimListDecoder_eq_some_of_raw_eq {N : ℕ} {w : List Bool}
    {xs : List (Fin N × List Bool)}
    (h : (Decoder.list (Decoder.pair Decoder.nat Decoder.bits)).decode w =
      xs.map fun x => (x.1.val, x.2)) :
    wordClaimListDecoder N w = some (xs.map fun x => ⟨x.1, x.2⟩) := by
  have hraw : wordClaimListRawDecoder.decode w =
      xs.map fun x => (⟨x.1.val, x.2⟩ : WordClaim) := by
    change (frames w).map wordClaimDecoder.decode = _
    have hmap : (frames w).map wordClaimDecoder.decode =
        ((Decoder.list (Decoder.pair Decoder.nat Decoder.bits)).decode w).map
          fun p => (⟨p.1, p.2⟩ : WordClaim) := by
      simp [Decoder.list, wordClaimDecoder, Decoder.map]
    rw [hmap, h, List.map_map]
    rfl
  simp only [wordClaimListDecoder, hraw]
  exact decodeWordClaimsChecked_map_fin N xs Prod.fst Prod.snd

/-- `wordClaimListDecoder` round-trips identically on every encoded list of valid `Fin N` claims. -/
@[simp] theorem wordClaimListDecoder_encWordClaimList_map {α : Type} (N : ℕ) (xs : List α)
    (idx : α → Fin N) (sig : α → List Bool) :
    wordClaimListDecoder N
        (encWordClaimList (xs.map fun x => (⟨(idx x).val, sig x⟩ : WordClaim))) =
      some (xs.map fun x => (⟨idx x, sig x⟩ : Signature.PreimageClaim N (List Bool))) := by
  have hraw :
      (Decoder.list (Decoder.pair Decoder.nat Decoder.bits)).decode
          (encWordClaimList (xs.map fun x => (⟨(idx x).val, sig x⟩ : WordClaim))) =
        (xs.map fun x => (idx x, sig x)).map fun x => (x.1.val, x.2) := by
    simp only [Decoder.list, encWordClaimList, frames_encList, List.map_map, Function.comp_def,
      encWordClaim_apply, (Decoder.pair Decoder.nat Decoder.bits).decode_enc]
  simpa [List.map_map, Function.comp_def] using wordClaimListDecoder_eq_some_of_raw_eq hraw

private theorem decodeWordClaimsChecked_eq_none_of_mem_ge {N : ℕ} :
    ∀ {claims : List WordClaim} {c : WordClaim},
      c ∈ claims → N ≤ c.index → decodeWordClaimsChecked N claims = none
  | [], _, hc, _ => by cases hc
  | c₀ :: rest, c, hc, hge => by
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · have hnot : ¬ c.index < N := Nat.not_lt.mpr hge
      simp [decodeWordClaimsChecked, hnot]
    · by_cases hi : c₀.index < N
      · simp [decodeWordClaimsChecked, hi,
          decodeWordClaimsChecked_eq_none_of_mem_ge hc hge]
      · simp [decodeWordClaimsChecked, hi]

/-- Any out-of-range claim `c` with `c.index ≥ N` causes `wordClaimListDecoder N` to reject the
entire encoded claim list (`none`). -/
theorem wordClaimListDecoder_eq_none_of_mem_ge {N : ℕ} {claims : List WordClaim}
    {c : WordClaim} (hc : c ∈ claims) (hge : N ≤ c.index) :
    wordClaimListDecoder N (encWordClaimList claims) = none := by
  simp only [wordClaimListDecoder, wordClaimListRawDecoder.decode_enc]
  exact decodeWordClaimsChecked_eq_none_of_mem_ge hc hge

/-! ### Word adversaries, games, and `reduceRedemptionsWord` -/

/-- A word-level extracted redemption adversary receives `(n, encWordTargetsInput ⟨pk, ys⟩)`,
queries `Unit × List Bool` for bit-string signatures, and outputs unit-opening word tokens. -/
abbrev WordRedemptionAdversary :=
  ℕ → List Bool → WordOracleComp Unit (List (Token (List Bool) Unit (List Bool)))

/-- A word-level chosen-target one-more adversary receives `(n, encWordTargetsInput ⟨pk, ys⟩)`,
queries `Unit × List Bool` for bit-string signatures, and outputs an encoded `encWordClaimList`. -/
abbrev WordOneMoreAdversary :=
  ℕ → List Bool → WordOracleComp Unit (List Bool)

/-- Convert a word-level redemption adversary to a typed adversary at security parameter `n` by
processing every output token message through the total decoder `dec : Decoder encM` (so
malformed message words yield whatever typed message `dec.decode` returns rather than being
rejected as parse errors under a `PartialDecoder`). -/
@[expose] def WordRedemptionAdversary.toTyped {Message : Type} {encM : Message ↪ List Bool}
    (dec : Decoder encM) (N : ℕ) (A : WordRedemptionAdversary) (n : ℕ) :
    List Bool → (Fin N → List Bool) →
      ProbOracleComp (fun _ : List Bool => List Bool) (List (Token Message Unit (List Bool))) :=
  fun pk targets =>
    (fun out => out.map fun tok =>
      (⟨⟨dec.decode tok.payload.message, ()⟩, tok.signature⟩ : Token Message Unit (List Bool))) <$>
      ProbOracleComp.simulate
        (fun req : Unit × List Bool => ProbOracleComp.query req.2)
        (A n (encWordTargetsInput ⟨pk, List.ofFn targets⟩))

/-- Convert a word-level one-more adversary to a typed one-more adversary at security parameter `n`
via `wordClaimListDecoder N`. Every non-codeword output is processed as the claim list returned by
the underlying total decoder `Decoder.list (Decoder.pair Decoder.nat Decoder.bits)`, and any
decoded claim with an out-of-range index `i ≥ N` causes `wordClaimListDecoder N` to return `none`,
which maps to `[]` (failing `Signature.oneMoreAccept` since `budget + 1 ≥ 1`). -/
@[expose] def WordOneMoreAdversary.toTyped (N : ℕ) (B : WordOneMoreAdversary) (n : ℕ) :
    List Bool → (Fin N → List Bool) →
      ProbOracleComp (fun _ : List Bool => List Bool)
        (List (Signature.PreimageClaim N (List Bool))) :=
  fun pk targets =>
    (fun w => (wordClaimListDecoder N w).getD []) <$>
      ProbOracleComp.simulate
        (fun req : Unit × List Bool => ProbOracleComp.query req.2)
        (B n (encWordTargetsInput ⟨pk, List.ofFn targets⟩))

/-- Word-level extracted redemption experiment at security parameter `n`. Adversaries receive the
full `encWordTargetsInput ⟨pk, List.ofFn targets⟩` vector of length `≥ N n`, and token messages are
processed through `dec n : Decoder (encM n)`. -/
@[expose] noncomputable def extractedRedemptionWordGame (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (encM : ∀ n, Message n ↪ List Bool) (dec : ∀ n, Decoder (encM n))
    (slot : ∀ n, Message n ↪ Fin (N n)) (budget : ℕ → ℕ)
    (A : WordRedemptionAdversary) (n : ℕ) : ProbComp Bool :=
  extractedRedemptionExperiment (S.toScheme n) (targets n) (slot n) (budget n)
    (A.toTyped (dec n) (N n) n)

/-- Word-level chosen-target one-more experiment at security parameter `n`. Adversaries receive the
full `encWordTargetsInput ⟨pk, List.ofFn targets⟩` vector of length `≥ N n` (so `IsOraclePPT`
runtime is polynomial in `n + N n`, corresponding to PPT security when `N n` is polynomially
bounded), and output words are processed through `wordClaimListDecoder (N n)`. -/
@[expose] noncomputable def oneMoreWordGame (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (budget : ℕ → ℕ) (B : WordOneMoreAdversary) (n : ℕ) : ProbComp Bool :=
  Signature.oneMoreExperiment (S.toScheme n) (targets n) (budget n) (B.toTyped (N n) n)

/-- Word-level chosen-target one-more unforgeability (novel to this library; closest source
[PoMFRIT2026], Definition 3.1, printed p. 7). Differs from [PoMFRIT2026] Definition 3.1 in four
respects: (1) adversaries run in the uniform strict oracle-PPT class `IsOraclePPT encBits` rather
than non-uniform PPT; (2) `targets` is an explicit caller sampler rather than independent uniform
target words (so colliding targets violate this premise); (3) `oneMoreWordGame` hands the full
encoded target vector `List.ofFn targets` (length `≥ N n`) in the input word, so adversary clocks
are polynomial in `n + N n` (representing PPT one-more unforgeability when `N n` is polynomially
bounded, whereas super-polynomial `N n` allows `2^{O(n)}`-time adversaries); and (4) claim outputs
are processed via the lenient total decoder `wordClaimListDecoder` (rejecting any index `i ≥ N n`,
while decoding malformed bit words via `Decoder.list (Decoder.pair Decoder.nat Decoder.bits)`).
No implication to or from [PoMFRIT2026] Definition 3.1 is established here; it holds
unconditionally at the pigeonhole boundary `N n = 1 < budget n + 1`
(`wordOneMoreUnforgeable_one_slot`), fails on colliding targets
(`not_wordOneMoreUnforgeable_constTargets`), and for `N n ≥ budget n + 1` with efficient `targets`
proving it unconditionally would imply one-way functions. -/
@[expose] def WordOneMoreUnforgeable (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool)) (budget : ℕ → ℕ) : Prop :=
  Game.Indistinguishable
    (fun B n => ProbComp.eval (oneMoreWordGame S N targets budget B n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- Uniform word-level realization of `RandomTarget.reduceRedemptions`: runs `A n input`, keeps
the first `budget n + 1` tokens, maps each token's message word via binary `slotWord n` into a
`WordClaim`, and encodes the claim list with `encWordClaimList`. -/
@[expose] def reduceRedemptionsWord (budget : ℕ → ℕ) (slotWord : ℕ → List Bool → ℕ)
    (A : WordRedemptionAdversary) : WordOneMoreAdversary :=
  fun n input =>
    (fun out =>
      encWordClaimList ((out.take (budget n + 1)).map fun tok =>
        (⟨slotWord n tok.payload.message, tok.signature⟩ : WordClaim))) <$>
      A n input

/-! ### Efficiency and query certificates for `reduceRedemptionsWord` -/

/-- `reduceRedemptionsWord` is uniform strict `IsOraclePPT encBits` whenever `n ↦ budget n + 1`,
`slotWord`, and `A` are efficient. -/
theorem isOraclePPT_reduceRedemptionsWord {budget : ℕ → ℕ}
    (hbudget : ComputableInPolyTime (fun n => budget n + 1) encUnary encUnary)
    {slotWord : ℕ → List Bool → ℕ}
    (hslot : ComputableInPolyTime (fun p : ℕ × List Bool => slotWord p.1 p.2)
      (encPair encUnary encBits) encNat)
    {A : WordRedemptionAdversary} (hA : IsOraclePPT (encRedemptionTokenList encBits) A) :
    IsOraclePPT encBits (reduceRedemptionsWord budget slotWord A) := by
  let encParam := encPair encUnary encBits
  let encTokList := encRedemptionTokenList encBits
  let encStepIn := encPair encParam encTokList
  have hn : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List (Token (List Bool) Unit (List Bool)) => q.1.1)
      encStepIn encUnary :=
    (ComputableInPolyTime.fst encParam encTokList).fst'
  have hout : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List (Token (List Bool) Unit (List Bool)) => q.2)
      encStepIn encTokList :=
    ComputableInPolyTime.snd encParam encTokList
  have htake : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List (Token (List Bool) Unit (List Bool)) =>
        q.2.take (budget q.1.1 + 1))
      encStepIn encTokList :=
    ComputableInPolyTime.listTakeWithInput hout (hbudget.comp hn)
  let encMapIn := encPair encStepIn (encRedemptionToken encBits)
  have hmn : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × List (Token (List Bool) Unit (List Bool))) ×
          Token (List Bool) Unit (List Bool) => r.1.1.1)
      encMapIn encUnary :=
    hn.comp (ComputableInPolyTime.fst encStepIn (encRedemptionToken encBits))
  have hmtok : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × List (Token (List Bool) Unit (List Bool))) ×
          Token (List Bool) Unit (List Bool) => r.2)
      encMapIn (encRedemptionToken encBits) :=
    ComputableInPolyTime.snd encStepIn (encRedemptionToken encBits)
  have hmpay := encRedemptionToken_payload_polyTime encBits hmtok
  have hmmsg := encRedemptionPayload_message_polyTime encBits hmpay
  have hmsig := encRedemptionToken_signature_polyTime encBits hmtok
  have hmslot : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × List (Token (List Bool) Unit (List Bool))) ×
          Token (List Bool) Unit (List Bool) => slotWord r.1.1.1 r.2.payload.message)
      encMapIn encNat :=
    hslot.comp (hmn.prod hmmsg)
  have hmclaim : ComputableInPolyTime
      (fun r : ((ℕ × List Bool) × List (Token (List Bool) Unit (List Bool))) ×
          Token (List Bool) Unit (List Bool) =>
        (⟨slotWord r.1.1.1 r.2.payload.message, r.2.signature⟩ : WordClaim))
      encMapIn encWordClaim :=
    encWordClaim_mk_polyTime hmslot hmsig
  have hmap : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List (Token (List Bool) Unit (List Bool)) =>
        (q.2.take (budget q.1.1 + 1)).map fun tok =>
          (⟨slotWord q.1.1 tok.payload.message, tok.signature⟩ : WordClaim))
      encStepIn encWordClaimList :=
    ComputableInPolyTime.mapWithInput htake hmclaim
  have henc : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List (Token (List Bool) Unit (List Bool)) =>
        encWordClaimList ((q.2.take (budget q.1.1 + 1)).map fun tok =>
          (⟨slotWord q.1.1 tok.payload.message, tok.signature⟩ : WordClaim)))
      encStepIn encBits :=
    (ComputableInPolyTime.of_eq (f := encWordClaimList) (encOut := encBits) fun _ => rfl).comp
      hmap
  have hon : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p => reduceRedemptionsWord budget slotWord A p.1 p.2) := by
    simpa only [reduceRedemptionsWord] using hA.on.map_with henc
  exact hon.isOraclePPT

private theorem reduceRedemptionsWord_queryBound (budget : ℕ → ℕ) (slotWord : ℕ → List Bool → ℕ)
    (A : WordRedemptionAdversary) (n : ℕ) (input : List Bool) {queries : ℕ}
    (h : (A n input).IsQueryBounded queries) :
    (reduceRedemptionsWord budget slotWord A n input).IsQueryBounded queries := by
  simpa only [reduceRedemptionsWord, ProbOracleComp.IsQueryBounded,
    OracleComp.isCostBounded_map_iff] using h

/-- Input-uniform signing-query admissibility for word adversaries: `adversary n input` makes at
most `q` signing-oracle queries on every `input : List Bool`. Unlike `Game.WithinQueries` (which
only constrains `input = []`) and unlike `IsOraclePPT`, this bounds signing-oracle calls across
all `(pk, targets)` inputs without bounding computational runtime. -/
@[expose] def WithinWordQueries {β : Type} (n q : ℕ)
    (adversary : ℕ → List Bool → WordOracleComp Unit β) : Prop :=
  ∀ input : List Bool, (adversary n input).IsQueryBounded q

/-- `reduceRedemptionsWord` preserves `WithinWordQueries` with the exact same query budget. -/
theorem withinWordQueries_reduceRedemptionsWord (budget : ℕ → ℕ)
    (slotWord : ℕ → List Bool → ℕ) (A : WordRedemptionAdversary)
    {n q : ℕ} (h : WithinWordQueries n q A) :
    WithinWordQueries n q (reduceRedemptionsWord budget slotWord A) :=
  fun input => reduceRedemptionsWord_queryBound budget slotWord A n input (h input)

/-! ### Exact `PMF` correspondence and security reductions -/

private theorem reduceRedemptionsWord_toTyped_eq
    {N : ℕ} {Message : Type} {encM : Message ↪ List Bool} (dec : Decoder encM)
    (slot : Message ↪ Fin N) (budget : ℕ → ℕ) (slotWord : ℕ → List Bool → ℕ)
    (n : ℕ) (hslot : ∀ w, slotWord n w = (slot (dec.decode w)).val)
    (A : WordRedemptionAdversary) (pk : List Bool) (targets : Fin N → List Bool) :
    (reduceRedemptionsWord budget slotWord A).toTyped N n pk targets =
      reduceRedemptions slot (budget n) (A.toTyped dec N n) pk targets := by
  simp only [WordOneMoreAdversary.toTyped, reduceRedemptionsWord, reduceRedemptions,
    WordRedemptionAdversary.toTyped, ProbOracleComp.simulate_map, Functor.map_map]
  congr 1
  funext out
  have hclaims :
      ((out.take (budget n + 1)).map fun tok =>
          (⟨slotWord n tok.payload.message, tok.signature⟩ : WordClaim)) =
        (out.take (budget n + 1)).map fun tok =>
          (⟨(slot (dec.decode tok.payload.message)).val, tok.signature⟩ : WordClaim) := by
    apply List.map_congr_left
    intro tok _
    rw [hslot tok.payload.message]
  rw [hclaims, wordClaimListDecoder_encWordClaimList_map]
  simp [List.map_take, List.map_map, Function.comp_def]

/-- `oneMoreWordGame` played by `reduceRedemptionsWord budget slotWord A` has the exact `PMF`
law of `Signature.oneMoreExperiment` played by `RandomTarget.reduceRedemptions` whenever
`slotWord n w = (slot n ((dec n).decode w)).val`. -/
theorem eval_oneMoreWordGame_reduceRedemptionsWord_eq
    (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (budget : ℕ → ℕ) (slotWord : ℕ → List Bool → ℕ) (n : ℕ)
    {Message : Type} {encM : Message ↪ List Bool} (dec : Decoder encM)
    (slot : Message ↪ Fin (N n))
    (hslot : ∀ w, slotWord n w = (slot (dec.decode w)).val)
    (A : WordRedemptionAdversary) :
    ProbComp.eval
        (oneMoreWordGame S N targets budget (reduceRedemptionsWord budget slotWord A) n) =
      ProbComp.eval (Signature.oneMoreExperiment (S.toScheme n) (targets n) (budget n)
        (reduceRedemptions slot (budget n) (A.toTyped dec (N n) n))) :=
  congrArg
    (fun adv => ProbComp.eval (Signature.oneMoreExperiment (S.toScheme n) (targets n) (budget n)
      adv))
    (funext fun pk => funext fun ys =>
      reduceRedemptionsWord_toTyped_eq dec slot budget slotWord n hslot A pk ys)

/-- Finite success-probability reduction for the word-level redemption game against
`oneMoreWordGame`. -/
theorem extractedRedemptionWordGame_succProbability_le
    (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (encM : ∀ n, Message n ↪ List Bool) (dec : ∀ n, Decoder (encM n))
    (slot : ∀ n, Message n ↪ Fin (N n)) (budget : ℕ → ℕ)
    (slotWord : ℕ → List Bool → ℕ)
    (hslot : ∀ n w, slotWord n w = (slot n ((dec n).decode w)).val)
    (A : WordRedemptionAdversary) (n : ℕ) :
    Game.succProbability (ProbComp.eval
        (extractedRedemptionWordGame S N targets Message encM dec slot budget A n)) ≤
      Game.succProbability (ProbComp.eval
        (oneMoreWordGame S N targets budget (reduceRedemptionsWord budget slotWord A) n)) := by
  have hle := extractedRedemption_succProbability_le (S.toScheme n) (targets n) (slot n)
    (budget n) (A.toTyped (dec n) (N n) n)
  simp only [Experiment.succProbability] at hle
  rw [← eval_oneMoreWordGame_reduceRedemptionsWord_eq S N targets budget slotWord n (dec n) (slot n)
    (hslot n) A] at hle
  simpa only [extractedRedemptionWordGame] using hle

/-- Query-bounded transfer lemma (`Game.SuccWithin` over `WithinWordQueries`): any concrete
`q`-query bound `ε n q` for `oneMoreWordGame` transfers to `extractedRedemptionWordGame` with
loss `1`, error `0`, and identical signing-query budget `q`. This lemma bounds signing-oracle calls
only (not computational runtime), unlike
`negligible_extractedRedemptionWordGame_of_wordOneMoreUnforgeable`, which enforces uniform strict
`IsOraclePPT encBits`. -/
theorem succWithin_extractedRedemptionWordGame_withinQueries
    (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (encM : ∀ n, Message n ↪ List Bool) (dec : ∀ n, Decoder (encM n))
    (slot : ∀ n, Message n ↪ Fin (N n)) (budget : ℕ → ℕ)
    (slotWord : ℕ → List Bool → ℕ)
    (hslot : ∀ n w, slotWord n w = (slot n ((dec n).decode w)).val)
    {ε : ℕ → ℕ → NNReal}
    (hOneMore : Game.SuccWithin
      (fun B n => ProbComp.eval (oneMoreWordGame S N targets budget B n)) WithinWordQueries ε) :
    Game.SuccWithin
      (fun A n => ProbComp.eval
        (extractedRedemptionWordGame S N targets Message encM dec slot budget A n))
      WithinWordQueries ε := by
  have hred := Game.SuccWithin.of_reduction hOneMore
    (reduceRedemptionsWord budget slotWord)
    (fun _ q => q) (fun _ _ => 1) (fun _ _ => 0)
    (fun _ _ _ hq => withinWordQueries_reduceRedemptionsWord budget slotWord _ hq)
    (fun n _ A _ => by
      simpa only [one_mul, add_zero] using
        extractedRedemptionWordGame_succProbability_le S N targets Message encM dec slot budget
          slotWord hslot A n)
  exact hred.mono fun _ _ => by simp

/-- Original asymptotic word-level redemption step in the extracted random-target model:
assuming `WordOneMoreUnforgeable S N targets budget` against uniform strict `IsOraclePPT encBits`
adversaries (representing PPT one-more hardness when `N n` is polynomially bounded, since
`oneMoreWordGame` passes `List.ofFn targets` in the input word), and polynomial-time
`n ↦ budget n + 1` and `slotWord`, every uniform strict `IsOraclePPT` adversary `A` has negligible
success probability in `extractedRedemptionWordGame`. -/
theorem negligible_extractedRedemptionWordGame_of_wordOneMoreUnforgeable
    (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (encM : ∀ n, Message n ↪ List Bool) (dec : ∀ n, Decoder (encM n))
    (slot : ∀ n, Message n ↪ Fin (N n)) (budget : ℕ → ℕ)
    (slotWord : ℕ → List Bool → ℕ)
    (hOneMore : WordOneMoreUnforgeable S N targets budget)
    (hbudget : ComputableInPolyTime (fun n => budget n + 1) encUnary encUnary)
    (hslot : ComputableInPolyTime (fun p : ℕ × List Bool => slotWord p.1 p.2)
      (encPair encUnary encBits) encNat)
    (hslotEq : ∀ n w, slotWord n w = (slot n ((dec n).decode w)).val)
    (A : WordRedemptionAdversary) (hA : IsOraclePPT (encRedemptionTokenList encBits) A) :
    Negligible (fun n => Game.succProbability (ProbComp.eval
      (extractedRedemptionWordGame S N targets Message encM dec slot budget A n))) := by
  have hred := isOraclePPT_reduceRedemptionsWord hbudget hslot hA
  have hneg := (Game.indistinguishable_pure_false_iff _ _).mp hOneMore
    (reduceRedemptionsWord budget slotWord A) hred
  exact negligible_of_le hneg fun n =>
    extractedRedemptionWordGame_succProbability_le S N targets Message encM dec slot budget
      slotWord hslotEq A n

end Cslib.Crypto.AnonymousToken

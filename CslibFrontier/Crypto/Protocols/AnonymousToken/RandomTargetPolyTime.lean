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

This module provides uniform strict oracle-PPT realizations and asymptotic as well as concrete
query-bounded security theorems for `Cslib.Crypto.AnonymousToken.reduceRedemptions`
(`CslibFrontier/Crypto/Protocols/AnonymousToken/RandomTarget.lean`).

Because the typed message family `Message n` and challenge count `N n` may vary with the security
parameter `n : ℕ` (for instance `Message n = { b : List Bool // b.length = k n }` with
`N n = 2 ^ (k n)`), word-level adversaries operate on uniform `List Bool` encodings:

* `WordRedemptionAdversary` outputs `List (Token (List Bool) Unit (List Bool))` under
  `encRedemptionTokenList encBits`, converted to `Token (Message n) Unit (List Bool)` per
  parameter `n` via a total decoder `dec n : Decoder (encM n)`.
* `slotWord : ℕ → List Bool → ℕ` realizes `slot n : Message n ↪ Fin (N n)` in binary (`encNat`)
  polynomial time so even exponential target spaces `N n` remain tractable.
* `WordOneMoreAdversary` outputs a framed list of binary `(index, signature)` pairs
  (`encWordClaimList`), decoded at challenge size `N n` by `wordClaimListDecoder`. If any
  decoded claim index satisfies `i ≥ N n`, `wordClaimListDecoder` rejects the entire claim list
  (`none`, yielding `false` in `oneMoreWordGame`) without silent modular wraparound or element
  filtering.
* `reduceRedemptionsWord` preserves both `IsOraclePPT` (`isOraclePPT_reduceRedemptionsWord`) and
  input-uniform query bounds (`WithinWordQueries`), and matches `RandomTarget.reduceRedemptions`
  in exact `PMF` law inside `oneMoreWordGame` (`eval_oneMoreGame_reduceRedemptionsWord_eq`).

## Main definitions

* `Cslib.Crypto.AnonymousToken.encRedemptionPayload`,
  `Cslib.Crypto.AnonymousToken.encRedemptionToken`,
  `Cslib.Crypto.AnonymousToken.encRedemptionTokenList`: encodings for unit-opening redemption
  tokens.
* `Cslib.Crypto.AnonymousToken.encWordClaim`, `Cslib.Crypto.AnonymousToken.encWordClaimList`,
  `Cslib.Crypto.AnonymousToken.encWordTargetsInput`: word encodings for `(index, signature)` claims
  and `(pk, targets)` inputs.
* `Cslib.Crypto.AnonymousToken.wordClaimListDecoder`: checked claim-list decoder rejecting any
  out-of-range index `i ≥ N`.
* `Cslib.Crypto.AnonymousToken.reduceRedemptionsWord`: uniform word-level realization of
  `RandomTarget.reduceRedemptions`.
* `Cslib.Crypto.AnonymousToken.extractedRedemptionWordGame`,
  `Cslib.Crypto.AnonymousToken.oneMoreWordGame`,
  `Cslib.Crypto.AnonymousToken.WordOneMoreUnforgeable`: word-level experiments and hardness
  assumption.
* `Cslib.Crypto.AnonymousToken.WithinWordQueries`: input-uniform signing-query bound predicate.

## Main results

* `Cslib.Crypto.AnonymousToken.isOraclePPTOn_reduceRedemptionsWord`,
  `Cslib.Crypto.AnonymousToken.isOraclePPT_reduceRedemptionsWord`: uniform strict `IsOraclePPT`
  runtime certificates for `reduceRedemptionsWord`.
* `Cslib.Crypto.AnonymousToken.reduceRedemptionsWord_queryBound`: exact signing-query preservation.
* `Cslib.Crypto.AnonymousToken.eval_extractedRedemptionWordGame_eq`,
  `Cslib.Crypto.AnonymousToken.eval_oneMoreGame_reduceRedemptionsWord_eq`: exact `PMF` law
  identities against `RandomTarget.extractedRedemptionExperiment` and
  `Signature.oneMoreExperiment`.
* `Cslib.Crypto.AnonymousToken.extractedRedemptionWordGame_succProbability_le`,
  `Cslib.Crypto.AnonymousToken.succWithin_extractedRedemptionWordGame_withinQueries`,
  `Cslib.Crypto.AnonymousToken.indistinguishable_extractedRedemptionWordGame`,
  `Cslib.Crypto.AnonymousToken.negligible_extractedRedemptionWordGame`: finite, concrete
  query-bounded (`WithinWordQueries`), and asymptotic `IsOraclePPT` security transfers.
-/

@[expose] public section

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

/-- Encode one `(index, signature)` preimage claim with binary natural index `encNat`. -/
abbrev encWordClaim : (ℕ × List Bool) ↪ List Bool :=
  encPair encNat encBits

/-- Encode a list of binary-indexed `(index, signature)` preimage claims. -/
abbrev encWordClaimList : List (ℕ × List Bool) ↪ List Bool :=
  encList encWordClaim

/-- Encode public inputs `(pk, List.ofFn targets)` passed to redemption and one-more
adversaries. -/
abbrev encWordTargetsInput : (List Bool × List (List Bool)) ↪ List Bool :=
  encPair encBits (encList encBits)

/-- Encode `(n, (pk, List.ofFn targets))` for uniform PPT certificates. -/
abbrev encRedemptionInput : (ℕ × (List Bool × List (List Bool))) ↪ List Bool :=
  encPair encUnary encWordTargetsInput

end Encodings

/-- Total decoder for `encWordTargetsInput`. -/
def wordTargetsInputDecoder : Decoder encWordTargetsInput :=
  Decoder.pair Decoder.bits (Decoder.list Decoder.bits)

/-- Total raw decoder for `encWordClaimList`, yielding `(index, signature)` pairs. -/
def wordClaimListRawDecoder : Decoder encWordClaimList :=
  Decoder.list (Decoder.pair Decoder.nat Decoder.bits)

/-- Validate a list of `(index, signature)` word pairs at challenge size `N`. If any pair has
`i ≥ N`, the entire claim list is rejected (`none`) rather than wrapping modulo `N` or skipping
bad entries. -/
def decodeWordClaimsChecked (N : ℕ) :
    List (ℕ × List Bool) → Option (List (Signature.PreimageClaim N (List Bool)))
  | [] => some []
  | (i, sig) :: rest =>
    if h : i < N then
      (⟨⟨i, h⟩, sig⟩ :: ·) <$> decodeWordClaimsChecked N rest
    else
      none

/-- Checked claim-list decoder at challenge size `N`: decodes `encWordClaimList` words and
rejects the entire claim list (`none`) whenever any pair has out-of-range index `i ≥ N`. -/
def wordClaimListDecoder (N : ℕ) (w : List Bool) :
    Option (List (Signature.PreimageClaim N (List Bool))) :=
  decodeWordClaimsChecked N (wordClaimListRawDecoder.decode w)

@[simp] theorem decodeWordClaimsChecked_map_fin {α : Type} (N : ℕ) (xs : List α)
    (idx : α → Fin N) (sig : α → List Bool) :
    decodeWordClaimsChecked N (xs.map fun x => ((idx x).val, sig x)) =
      some (xs.map fun x => (⟨idx x, sig x⟩ : Signature.PreimageClaim N (List Bool))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [decodeWordClaimsChecked, ih]

/-- `wordClaimListDecoder` round-trips identically on every encoded list of valid `Fin N` claims. -/
@[simp] theorem wordClaimListDecoder_encWordClaimList_map {α : Type} (N : ℕ) (xs : List α)
    (idx : α → Fin N) (sig : α → List Bool) :
    wordClaimListDecoder N (encWordClaimList (xs.map fun x => ((idx x).val, sig x))) =
      some (xs.map fun x => (⟨idx x, sig x⟩ : Signature.PreimageClaim N (List Bool))) := by
  simp only [wordClaimListDecoder, wordClaimListRawDecoder.decode_enc,
    decodeWordClaimsChecked_map_fin]

/-- Any out-of-range pair `(i, sig)` with `i ≥ N` in the decoded raw list causes
`decodeWordClaimsChecked N` to reject the entire claim list. -/
theorem decodeWordClaimsChecked_eq_none_of_mem_ge {N : ℕ} :
    ∀ {pairs : List (ℕ × List Bool)} {p : ℕ × List Bool},
      p ∈ pairs → N ≤ p.1 → decodeWordClaimsChecked N pairs = none
  | [], _, hp, _ => by cases hp
  | (i, sig) :: rest, p, hp, hge => by
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · have hnot : ¬ i < N := Nat.not_lt.mpr hge
      simp [decodeWordClaimsChecked, hnot]
    · by_cases hi : i < N
      · simp [decodeWordClaimsChecked, hi,
          decodeWordClaimsChecked_eq_none_of_mem_ge hp hge]
      · simp [decodeWordClaimsChecked, hi]

/-- Any out-of-range index `i ≥ N` causes `wordClaimListDecoder N` to reject the entire encoded
claim list (`none`). -/
theorem wordClaimListDecoder_eq_none_of_mem_ge {N : ℕ} {pairs : List (ℕ × List Bool)}
    {p : ℕ × List Bool} (hp : p ∈ pairs) (hge : N ≤ p.1) :
    wordClaimListDecoder N (encWordClaimList pairs) = none := by
  simp only [wordClaimListDecoder, wordClaimListRawDecoder.decode_enc]
  exact decodeWordClaimsChecked_eq_none_of_mem_ge hp hge

/-! ### Word adversaries, games, and `reduceRedemptionsWord` -/

/-- A word-level extracted redemption adversary receives `(n, encWordTargetsInput (pk, ys))`,
queries `Unit × List Bool` for bit-string signatures, and outputs unit-opening word tokens. -/
abbrev WordRedemptionAdversary :=
  ℕ → List Bool → WordOracleComp Unit (List (Token (List Bool) Unit (List Bool)))

/-- A word-level chosen-target one-more adversary receives `(n, encWordTargetsInput (pk, ys))`,
queries `Unit × List Bool` for bit-string signatures, and outputs an encoded `encWordClaimList`. -/
abbrev WordOneMoreAdversary :=
  ℕ → List Bool → WordOracleComp Unit (List Bool)

/-- Convert a word-level redemption adversary to a typed adversary at security parameter `n` by
decoding each token message with `dec : Decoder encM`. -/
def WordRedemptionAdversary.toTyped {Message : Type} {encM : Message ↪ List Bool}
    (dec : Decoder encM) (N : ℕ) (A : WordRedemptionAdversary) (n : ℕ) :
    List Bool → (Fin N → List Bool) →
      ProbOracleComp (fun _ : List Bool => List Bool) (List (Token Message Unit (List Bool))) :=
  fun pk targets =>
    (fun out => out.map fun tok =>
      (⟨⟨dec.decode tok.payload.message, ()⟩, tok.signature⟩ : Token Message Unit (List Bool))) <$>
      ProbOracleComp.simulate
        (fun req : Unit × List Bool => ProbOracleComp.query req.2)
        (A n (encWordTargetsInput (pk, List.ofFn targets)))

/-- Convert a word-level one-more adversary to a typed one-more adversary at security parameter `n`
via `wordClaimListDecoder N`, falling back to `[]` (which fails `oneMoreAccept` since `budget + 1
≥ 1`) whenever any claim index is out of range. -/
def WordOneMoreAdversary.toTyped (N : ℕ) (B : WordOneMoreAdversary) (n : ℕ) :
    List Bool → (Fin N → List Bool) →
      ProbOracleComp (fun _ : List Bool => List Bool)
        (List (Signature.PreimageClaim N (List Bool))) :=
  fun pk targets =>
    (fun w => (wordClaimListDecoder N w).getD []) <$>
      ProbOracleComp.simulate
        (fun req : Unit × List Bool => ProbOracleComp.query req.2)
        (B n (encWordTargetsInput (pk, List.ofFn targets)))

/-- Word-level extracted redemption experiment at security parameter `n`. -/
noncomputable def extractedRedemptionWordGame (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (encM : ∀ n, Message n ↪ List Bool) (dec : ∀ n, Decoder (encM n))
    (slot : ∀ n, Message n ↪ Fin (N n)) (budget : ℕ → ℕ)
    (A : WordRedemptionAdversary) (n : ℕ) : ProbComp Bool :=
  extractedRedemptionExperiment (S.toScheme n) (targets n) (slot n) (budget n)
    (A.toTyped (dec n) (N n) n)

/-- Word-level chosen-target one-more experiment at security parameter `n`. Out-of-range claim
indices cause `wordClaimListDecoder (N n)` to return `none`, yielding `[]` and failing
`Signature.oneMoreAccept` because `0 ≠ budget n + 1`. -/
noncomputable def oneMoreWordGame (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (budget : ℕ → ℕ) (B : WordOneMoreAdversary) (n : ℕ) : ProbComp Bool :=
  Signature.oneMoreExperiment (S.toScheme n) (targets n) (budget n) (B.toTyped (N n) n)

/-- Asymptotic word-level chosen-target one-more unforgeability (`[pomfrit26]`, `[voleihat26]`):
every uniform strict `IsOraclePPT encBits` word adversary has negligible success probability in
`oneMoreWordGame`. -/
def WordOneMoreUnforgeable (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (budget : ℕ → ℕ) : Prop :=
  Game.Indistinguishable
    (fun B n => ProbComp.eval (oneMoreWordGame S N targets budget B n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT encBits)

/-- Uniform word-level realization of `RandomTarget.reduceRedemptions`: runs `A n input`, keeps
the first `budget n + 1` tokens, maps each token's message word via binary `slotWord n`, and
encodes the resulting `(index, signature)` claim list with `encWordClaimList`. -/
def reduceRedemptionsWord (budget : ℕ → ℕ) (slotWord : ℕ → List Bool → ℕ)
    (A : WordRedemptionAdversary) : WordOneMoreAdversary :=
  fun n input =>
    (fun out =>
      encWordClaimList ((out.take (budget n + 1)).map fun tok =>
        (slotWord n tok.payload.message, tok.signature))) <$>
      A n input

/-! ### Efficiency and query certificates for `reduceRedemptionsWord` -/

/-- `reduceRedemptionsWord` is uniform strict `IsOraclePPTOn` on `(n, input)` whenever
`n ↦ budget n + 1`, `slotWord`, and `A` are efficient. -/
theorem isOraclePPTOn_reduceRedemptionsWord {budget : ℕ → ℕ}
    (hbudget : ComputableInPolyTime (fun n => budget n + 1) encUnary encUnary)
    {slotWord : ℕ → List Bool → ℕ}
    (hslot : ComputableInPolyTime (fun p : ℕ × List Bool => slotWord p.1 p.2)
      (encPair encUnary encBits) encNat)
    {A : WordRedemptionAdversary} (hA : IsOraclePPT (encRedemptionTokenList encBits) A) :
    IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p => reduceRedemptionsWord budget slotWord A p.1 p.2) := by
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
  have hmap : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List (Token (List Bool) Unit (List Bool)) =>
        (q.2.take (budget q.1.1 + 1)).map fun tok =>
          (slotWord q.1.1 tok.payload.message, tok.signature))
      encStepIn encWordClaimList :=
    ComputableInPolyTime.mapWithInput htake (hmslot.prod hmsig)
  have henc : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List (Token (List Bool) Unit (List Bool)) =>
        encWordClaimList ((q.2.take (budget q.1.1 + 1)).map fun tok =>
          (slotWord q.1.1 tok.payload.message, tok.signature)))
      encStepIn encBits :=
    (ComputableInPolyTime.of_eq (f := encWordClaimList) (encOut := encBits) fun _ => rfl).comp
      hmap
  simpa only [reduceRedemptionsWord] using hA.on.map_with henc

/-- `reduceRedemptionsWord` satisfies `IsOraclePPT encBits` whenever `n ↦ budget n + 1`,
`slotWord`, and `A` are efficient. -/
theorem isOraclePPT_reduceRedemptionsWord {budget : ℕ → ℕ}
    (hbudget : ComputableInPolyTime (fun n => budget n + 1) encUnary encUnary)
    {slotWord : ℕ → List Bool → ℕ}
    (hslot : ComputableInPolyTime (fun p : ℕ × List Bool => slotWord p.1 p.2)
      (encPair encUnary encBits) encNat)
    {A : WordRedemptionAdversary} (hA : IsOraclePPT (encRedemptionTokenList encBits) A) :
    IsOraclePPT encBits (reduceRedemptionsWord budget slotWord A) :=
  (isOraclePPTOn_reduceRedemptionsWord hbudget hslot hA).isOraclePPT

/-- `reduceRedemptionsWord` preserves every signing-oracle query bound identically on every input
word. -/
theorem reduceRedemptionsWord_queryBound (budget : ℕ → ℕ) (slotWord : ℕ → List Bool → ℕ)
    (A : WordRedemptionAdversary) (n : ℕ) (input : List Bool) {queries : ℕ}
    (h : (A n input).IsQueryBounded queries) :
    (reduceRedemptionsWord budget slotWord A n input).IsQueryBounded queries := by
  simpa only [reduceRedemptionsWord, ProbOracleComp.IsQueryBounded,
    OracleComp.isCostBounded_map_iff] using h

/-- Input-uniform signing-query admissibility for word adversaries: `adversary n input` makes at
most `q` signing-oracle queries on every `input : List Bool`. Unlike `Game.WithinQueries` (which
only constrains `input = []`) and unlike `IsOraclePPT`, this bounds signing-oracle calls across
all `(pk, targets)` inputs without bounding computational runtime. -/
def WithinWordQueries {β : Type} (n q : ℕ)
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
          (slotWord n tok.payload.message, tok.signature)) =
        (out.take (budget n + 1)).map fun tok =>
          ((slot (dec.decode tok.payload.message)).val, tok.signature) := by
    apply List.map_congr_left
    intro tok _
    rw [hslot tok.payload.message]
  rw [hclaims, wordClaimListDecoder_encWordClaimList_map]
  simp [List.map_take, List.map_map, Function.comp_def]

/-- `extractedRedemptionWordGame` agrees by definition with `extractedRedemptionExperiment`
at every parameter `n`. -/
theorem eval_extractedRedemptionWordGame_eq
    (S : WordSignatureScheme) (N : ℕ → ℕ)
    (targets : ∀ n, List Bool → ProbComp (Fin (N n) → List Bool))
    (Message : ℕ → Type) [∀ n, DecidableEq (Message n)]
    (encM : ∀ n, Message n ↪ List Bool) (dec : ∀ n, Decoder (encM n))
    (slot : ∀ n, Message n ↪ Fin (N n)) (budget : ℕ → ℕ)
    (A : WordRedemptionAdversary) (n : ℕ) :
    ProbComp.eval
        (extractedRedemptionWordGame S N targets Message encM dec slot budget A n) =
      ProbComp.eval (extractedRedemptionExperiment (S.toScheme n) (targets n) (slot n) (budget n)
        (A.toTyped (dec n) (N n) n)) := rfl

/-- `oneMoreWordGame` played by `reduceRedemptionsWord budget slotWord A` has the exact `PMF`
law of `Signature.oneMoreExperiment` played by `RandomTarget.reduceRedemptions` whenever
`slotWord n w = (slot n ((dec n).decode w)).val`. -/
theorem eval_oneMoreGame_reduceRedemptionsWord_eq
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
  rw [← eval_oneMoreGame_reduceRedemptionsWord_eq S N targets budget slotWord n (dec n) (slot n)
    (hslot n) A] at hle
  simpa only [eval_extractedRedemptionWordGame_eq] using hle

/-- Concrete query-bounded reduction (`Game.SuccWithin` over `WithinWordQueries`): any concrete
`q`-query bound `ε n q` for `oneMoreWordGame` transfers to `extractedRedemptionWordGame` with
loss `1`, error `0`, and identical signing-query budget `q`. Note that `WithinWordQueries` bounds
signing-oracle queries only (not computational runtime), unlike
`negligible_extractedRedemptionWordGame`, which enforces uniform strict `IsOraclePPT encBits`. -/
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

/-- Asymptotic word-level redemption security in the extracted random-target model: assuming
`WordOneMoreUnforgeable S N targets budget` and polynomial-time `n ↦ budget n + 1` and `slotWord`,
every uniform strict `IsOraclePPT` adversary `A` has negligible success probability in
`extractedRedemptionWordGame`. -/
theorem negligible_extractedRedemptionWordGame
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

/-- `Game.Indistinguishable` packaging of `negligible_extractedRedemptionWordGame` for uniform
strict `IsOraclePPT` adversaries. -/
theorem indistinguishable_extractedRedemptionWordGame
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
    (hslotEq : ∀ n w, slotWord n w = (slot n ((dec n).decode w)).val) :
    Game.Indistinguishable
      (fun A n => ProbComp.eval
        (extractedRedemptionWordGame S N targets Message encM dec slot budget A n))
      (fun _ _ => PMF.pure false)
      (IsOraclePPT (encRedemptionTokenList encBits)) :=
  (Game.indistinguishable_pure_false_iff _ _).mpr fun A hA =>
    negligible_extractedRedemptionWordGame S N targets Message encM dec slot budget slotWord
      hOneMore hbudget hslot hslotEq A hA

end Cslib.Crypto.AnonymousToken

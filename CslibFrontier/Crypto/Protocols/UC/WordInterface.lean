/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Execution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Fin
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.PMF.Map

/-!
# Binary word presentation of typed UC interfaces

Library infrastructure toward #6043 and #8377 (no cited result): typed UC machines and environments
communicate over indexed query-reply specifications `E : ι → Type` (`partySpec`, `netSpec`,
`protocolSpec`, `execSpec`), whereas `WordOracleComp` and `IsOraclePPTOn` execute on finite channel
tags carrying `List Bool` payloads. This module supplies the lowering from typed `ProbOracleComp`
programs to `WordOracleComp` programs over finitely many channels, together with the dual encoded
oracle, canonical-request normalizer, and strict oracle PPT preservation certificates.

## Modelling decisions and restrictions

* **Named structures.** `WordPort` packages total polynomial-time decoders for queries and replies
  on a single `netSpec Q R` port, and `WordInterface` packages channel routing, total query/reply
  decoding, and per-channel normalization cost certificates (`replyNormalize`, `requestNormalize`).
* **Relation to `Cslib.OracleCodec` and off-image requests.** `WordInterface.toOracleCodec` builds
  a partial `OracleCodec I.Channel ι E` whose `decodeQuery` recognizes valid
  `(I.channel q, I.request q)` requests. `WordInterface.encodeOracle` normalizes each incoming word
  with `I.requestNormalize` and delegates to `I.toOracleCodec.wordOracle`; by
  `I.request_decodeQuery`, the normalized pair is the encoded query of `I.decodeQuery cw.1 cw.2`,
  so off-image requests still call `oracle` once (`WordInterface.encodeOracle_apply`), while
  canonical requests agree directly with `I.toOracleCodec.wordOracle`
  (`WordInterface.encodeOracle_eq_wordOracle`). Conversely, `WordInterface.normalizeRequests`
  rewrites every query `(c, w)` of an arbitrary word program to `(c, I.requestNormalize c w)`, so
  interacting with `I.encodeOracle oracle` has the exact same joint output and oracle-state law as
  running the canonicalized program against the strict non-mutating `I.toOracleCodec.wordOracle`
  (`WordInterface.runWith_encodeOracle_eq_wordOracle_normalizeRequests`), while preserving strict
  oracle PPT (`WordInterface.isOraclePPTOn_normalizeRequests`) without extra reply-length bounds.
  Total request/reply decoders and the finite `Channel` normalization certificates
  (`replyNormalize`, `requestNormalize`) are needed so a word machine can normalize arbitrary
  incoming or outgoing words in polynomial time.
* **Unary `Fin n` party rank (`[NeZero n]`).** `WordPort.party` encodes party indices in unary
  and decodes arbitrary words modulo `n`. Because a total decoder requires a nonempty target type,
  `n ≥ 1` (`[NeZero n]`) is required on `WordPort.party`.
* **Interface coverage.** The constructors `WordInterface.empty`, `WordInterface.net`, and
  `WordInterface.sum` cover `OracleSpec.empty`, `netSpec`, and `⊕ₒ`, which suffices for
  `Execution`, `Composition`, and `DummyAdversary`. Dependent-reply interfaces such as
  `SSP.sessionSpec` (`MultiSession`) are not covered here.
* **Explicit reply truncation (`limit`).** `ProbOracleComp.lowerWith I limit` is
  `ProbOracleComp.simulate (I.lowerQuery limit)`: it truncates each word reply to `limit` bits via
  `List.take limit` before decoding, matching the strict clock contract of
  `IsOraclePPTOn.query_take`. Structural equations come directly from `ProbOracleComp.simulate_*`.
  When every reply of a typed stateful oracle encodes within `limit` bits,
  `ProbOracleComp.runWith_lowerWith` equates the lowered word run against
  `I.encodeOracle oracle` with the original typed run.

## Main definitions

* `Cslib.Crypto.Protocols.UC.WordPort`: total query and reply decoders for a `netSpec` port.
* `Cslib.Crypto.Protocols.UC.WordInterface`: finite-channel word presentation of a typed interface.
* `Cslib.Crypto.Protocols.UC.WordInterface.empty`, `.net`, `.sum`, `.protocol`, `.exec`,
  `WordPort.sum`, `WordPort.party`: constructors and UC interface abbreviations.
* `Cslib.Crypto.Protocols.UC.WordInterface.toOracleCodec`, `.encodeOracle`, `.lowerQuery`,
  `.normalizeRequests`: `OracleCodec` view, total channel-encoded oracle, single-query lowering
  handler, and canonical-request normalizer.
* `Cslib.ProbOracleComp.lowerWith`: lower a typed `ProbOracleComp` via
  `ProbOracleComp.simulate (I.lowerQuery limit)`.

## Main results

* `Cslib.Crypto.Protocols.UC.WordInterface.encodeOracle_apply`: stateful evaluation of
  `encodeOracle` via `toOracleCodec.wordOracle` at the normalized request.
* `Cslib.Crypto.Protocols.UC.WordInterface.encodeOracle_eq_wordOracle`: agreement with
  `toOracleCodec.wordOracle` on encoded requests.
* `Cslib.Crypto.Protocols.UC.WordInterface.encodeOracle_sum`: encoded sum-interface routing.
* `Cslib.Crypto.Protocols.UC.WordInterface.runWith_lowerQuery` and
  `Cslib.ProbOracleComp.runWith_lowerWith`: lowered execution agrees with typed execution when
  every supported reply fits within `limit` bits.
* `Cslib.Crypto.Protocols.UC.WordPort.computable_partyIndex`: `WordPort.party` exposes the decoded
  party index in polynomial time.
* `Cslib.Crypto.Protocols.UC.WordInterface.isOraclePPTOn_lowerWith_query` and
  `Cslib.Crypto.Protocols.UC.WordInterface.isOraclePPTOn_lowerWith_decodeQuery`: lowered, re-encoded
  queries (and decoded `(channel, word)` queries) are uniform strict oracle PPT when their channel,
  request/word, and reply bound are polynomial time.
* `Cslib.Crypto.Protocols.UC.WordInterface.runWith_encodeOracle_eq_wordOracle_normalizeRequests`:
  running any word program against `I.encodeOracle oracle` has the same joint output and state law
  as running `I.normalizeRequests program` against the strict non-mutating
  `I.toOracleCodec.wordOracle oracle`.
* `Cslib.Crypto.Protocols.UC.WordInterface.queriesSatisfy_normalizeRequests`,
  `Cslib.Crypto.Protocols.UC.WordInterface.normalizeRequests_idempotent`, and
  `Cslib.Crypto.Protocols.UC.WordInterface.normalizeRequests_lowerWith`: normalized programs issue
  only canonical requests, normalization is idempotent, and lowered programs are fixed points.
* `Cslib.Crypto.Protocols.UC.WordInterface.isOraclePPTOn_normalizeRequests`: canonical-request
  normalization preserves uniform strict oracle PPT for arbitrary word adversaries.
-/

@[expose] public section

namespace Cslib

namespace Crypto.Protocols.UC

open Turing.MultiTapeTM
open Cslib.Probability

/-- Library construction (no cited definition): a binary presentation of one typed port
`netSpec Q R` packaging total decoders for its queries and replies. -/
structure WordPort (Q R : Type) : Type where
  /-- Injection from typed queries to bit words. -/
  query : Q ↪ List Bool
  /-- Total polynomial-time decoder for queries. -/
  queryDecoder : Decoder query
  /-- Injection from typed replies to bit words. -/
  reply : R ↪ List Bool
  /-- Total polynomial-time decoder for replies. -/
  replyDecoder : Decoder reply

/-- Library construction (no cited definition): a typed interface presented over finitely many
word channels. -/
structure WordInterface {ι : Type} (E : ι → Type) : Type 1 where
  /-- Finite tag type identifying the interface's word channels. -/
  Channel : Type
  [decEq : DecidableEq Channel]
  [finite : Finite Channel]
  /-- Channel carrying each typed query. -/
  channel : ι → Channel
  /-- Encoded request word for each typed query. -/
  request : ι → List Bool
  /-- Total decoder recovering a typed query from a channel and request word. -/
  decodeQuery : Channel → List Bool → ι
  decodeQuery_request : ∀ q, decodeQuery (channel q) (request q) = q
  /-- Query-dependent injection from typed replies to bit words. -/
  reply : (q : ι) → E q ↪ List Bool
  /-- Total decoder recovering a typed reply from a word. -/
  decodeReply : (q : ι) → List Bool → E q
  decodeReply_reply : ∀ q r, decodeReply q (reply q r) = r
  /-- Decoding a reply word and re-encoding it is one polynomial-time word map per channel. -/
  replyNormalize : Channel → List Bool → List Bool
  reply_decodeReply : ∀ q w, reply q (decodeReply q w) = replyNormalize (channel q) w
  computable_replyNormalize :
    ComputableInPolyTime (fun c : Channel × List Bool => replyNormalize c.1 c.2)
      (encPair (encFinite Channel) encBits) encBits
  /-- The same normalization cost certificate for requests. -/
  requestNormalize : Channel → List Bool → List Bool
  request_decodeQuery : ∀ c w,
    channel (decodeQuery c w) = c ∧ request (decodeQuery c w) = requestNormalize c w
  computable_requestNormalize :
    ComputableInPolyTime (fun c : Channel × List Bool => requestNormalize c.1 c.2)
      (encPair (encFinite Channel) encBits) encBits

attribute [instance] WordInterface.decEq WordInterface.finite

namespace WordInterface

/-- Library infrastructure: word presentation of the empty interface `OracleSpec.empty`. -/
def empty : WordInterface OracleSpec.empty where
  Channel := Empty
  channel q := q.elim
  request q := q.elim
  decodeQuery c _ := c.elim
  decodeQuery_request q := q.elim
  reply q := q.elim
  decodeReply q := q.elim
  decodeReply_reply q := q.elim
  replyNormalize c _ := c.elim
  reply_decodeReply q _ := q.elim
  computable_replyNormalize := by
    have : IsEmpty (Empty × List Bool) := ⟨fun c => c.1.elim⟩
    exact ComputableInPolyTime.of_finite _
  requestNormalize c _ := c.elim
  request_decodeQuery c _ := c.elim
  computable_requestNormalize := by
    have : IsEmpty (Empty × List Bool) := ⟨fun c => c.1.elim⟩
    exact ComputableInPolyTime.of_finite _

/-- Library infrastructure: word presentation of a single typed port `netSpec Q R`. -/
def net {Q R : Type} (port : WordPort Q R) : WordInterface (netSpec Q R) where
  Channel := Unit
  channel _ := ()
  request q := port.query q
  decodeQuery _ w := port.queryDecoder.decode w
  decodeQuery_request q := port.queryDecoder.decode_enc q
  reply _ := port.reply
  decodeReply _ := port.replyDecoder.decode
  decodeReply_reply _ r := port.replyDecoder.decode_enc r
  replyNormalize _ w := port.reply (port.replyDecoder.decode w)
  reply_decodeReply _ _ := rfl
  computable_replyNormalize :=
    (port.replyDecoder.computableInPolyTime.comp
      (ComputableInPolyTime.snd (encFinite Unit) encBits)).of_enc_eq fun _ => rfl
  requestNormalize _ w := port.query (port.queryDecoder.decode w)
  request_decodeQuery _ _ := ⟨rfl, rfl⟩
  computable_requestNormalize :=
    (port.queryDecoder.computableInPolyTime.comp
      (ComputableInPolyTime.snd (encFinite Unit) encBits)).of_enc_eq fun _ => rfl

/-- Shared channel-tagged word normalization for disjoint sums of interfaces. -/
private theorem computable_sum_channel_word
    {C₁ C₂ : Type} [Finite C₁] [Finite C₂]
    {f₁ : C₁ → List Bool → List Bool} {f₂ : C₂ → List Bool → List Bool}
    (hf₁ : ComputableInPolyTime (fun p : C₁ × List Bool => f₁ p.1 p.2)
      (encPair (encFinite C₁) encBits) encBits)
    (hf₂ : ComputableInPolyTime (fun p : C₂ × List Bool => f₂ p.1 p.2)
      (encPair (encFinite C₂) encBits) encBits) :
    ComputableInPolyTime
      (fun p : (C₁ ⊕ C₂) × List Bool => Sum.elim f₁ f₂ p.1 p.2)
      (encPair (encFinite (C₁ ⊕ C₂)) encBits) encBits := by
  refine ComputableInPolyTime.finite_cases (tagEncoding := encFinite (C₁ ⊕ C₂))
    (tag := Prod.fst) (branch := fun choice p => Sum.elim f₁ f₂ choice p.2)
    (ComputableInPolyTime.fst (encFinite (C₁ ⊕ C₂)) encBits) ?_
  rintro (c₁ | c₂)
  · exact hf₁.comp ((ComputableInPolyTime.const (encIn := encPair (encFinite (C₁ ⊕ C₂)) encBits)
      (encOut := encFinite C₁) c₁).prod
      (ComputableInPolyTime.snd (encFinite (C₁ ⊕ C₂)) encBits))
  · exact hf₂.comp ((ComputableInPolyTime.const (encIn := encPair (encFinite (C₁ ⊕ C₂)) encBits)
      (encOut := encFinite C₂) c₂).prod
      (ComputableInPolyTime.snd (encFinite (C₁ ⊕ C₂)) encBits))

/-- Library infrastructure: disjoint sum of two typed word interfaces. -/
def sum {ι₁ ι₂ : Type} {E₁ : ι₁ → Type} {E₂ : ι₂ → Type}
    (left : WordInterface E₁) (right : WordInterface E₂) :
    WordInterface (E₁ ⊕ₒ E₂) where
  Channel := left.Channel ⊕ right.Channel
  channel := Sum.map left.channel right.channel
  request := Sum.elim left.request right.request
  decodeQuery
    | Sum.inl c, w => Sum.inl (left.decodeQuery c w)
    | Sum.inr c, w => Sum.inr (right.decodeQuery c w)
  decodeQuery_request
    | Sum.inl q => by simp [left.decodeQuery_request]
    | Sum.inr q => by simp [right.decodeQuery_request]
  reply
    | Sum.inl q => left.reply q
    | Sum.inr q => right.reply q
  decodeReply
    | Sum.inl q => left.decodeReply q
    | Sum.inr q => right.decodeReply q
  decodeReply_reply
    | Sum.inl q, r => left.decodeReply_reply q r
    | Sum.inr q, r => right.decodeReply_reply q r
  replyNormalize := Sum.elim left.replyNormalize right.replyNormalize
  reply_decodeReply
    | Sum.inl q, w => left.reply_decodeReply q w
    | Sum.inr q, w => right.reply_decodeReply q w
  computable_replyNormalize := by
    exact computable_sum_channel_word left.computable_replyNormalize right.computable_replyNormalize
  requestNormalize := Sum.elim left.requestNormalize right.requestNormalize
  request_decodeQuery
    | Sum.inl c, w => by
      simpa using left.request_decodeQuery c w
    | Sum.inr c, w => by
      simpa using right.request_decodeQuery c w
  computable_requestNormalize := by
    exact computable_sum_channel_word
      left.computable_requestNormalize right.computable_requestNormalize

/-- Library construction (no cited definition): word interface for a UC protocol
`protocolSpec n In Out NetQ NetR`. -/
abbrev protocol {n : ℕ} {In Out NetQ NetR : Type}
    (party : WordPort (Fin n × In) (Option Out)) (netPort : WordPort NetQ NetR) :
    WordInterface (protocolSpec n In Out NetQ NetR) :=
  sum (net party) (net netPort)

/-- Library construction (no cited definition): word interface for a UC execution environment
`execSpec n In Out AdvQ AdvR`. -/
abbrev exec {n : ℕ} {In Out AdvQ AdvR : Type}
    (party : WordPort (Fin n × In) (Option Out)) (adv : WordPort AdvQ AdvR) :
    WordInterface (execSpec n In Out AdvQ AdvR) :=
  sum (net party) (net adv)

/-- Library infrastructure (no cited result): view a `WordInterface` as a partial `OracleCodec`
that accepts exactly canonical `(I.channel q, I.request q)` pairs. -/
def toOracleCodec {ι : Type} {E : ι → Type} (I : WordInterface E) :
    OracleCodec I.Channel ι E where
  encodeQuery q := (I.channel q, I.request q)
  decodeQuery cw :=
    let q := I.decodeQuery cw.1 cw.2
    if (I.channel q, I.request q) = cw then some q else none
  decodeQuery_eq_some_iff request q := by
    constructor
    · intro h
      dsimp only at h
      split_ifs at h with heq
      cases h
      exact heq
    · intro h
      subst h
      dsimp only
      rw [I.decodeQuery_request]
      simp
  encodeReply := I.reply

/-- Library infrastructure (no cited result): present a typed stateful oracle on `I.Channel` by
routing through `I.toOracleCodec.wordOracle` at the `I.requestNormalize`-normalized request.
Unlike calling `I.toOracleCodec.wordOracle` directly (which answers off-image requests with `[]`
without querying `oracle`), `encodeOracle` normalizes every request to
`I.toOracleCodec.encodeQuery (I.decodeQuery cw.1 cw.2)` via `I.request_decodeQuery` and calls
`oracle` once (`encodeOracle_apply`); both agree on encoded requests (`encodeOracle_eq_wordOracle`).
-/
noncomputable def encodeOracle {ι : Type} {E : ι → Type} {σ : Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q)) :
    I.Channel × List Bool → StateT σ PMF (List Bool) :=
  fun cw => I.toOracleCodec.wordOracle oracle (cw.1, I.requestNormalize cw.1 cw.2)

/-- Library infrastructure (no cited result): stateful equation for `I.encodeOracle oracle` on any
`(c, w)` and state `s`, obtained by normalizing `(c, w)` via `I.request_decodeQuery` and applying
`OracleCodec.wordOracle_encodeQuery`. -/
theorem encodeOracle_apply {ι : Type} {E : ι → Type} {σ : Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q))
    (c : I.Channel) (w : List Bool) (s : σ) :
    I.encodeOracle oracle (c, w) s =
      (oracle (I.decodeQuery c w) s).map fun x => (I.reply (I.decodeQuery c w) x.1, x.2) := by
  have hreq : (c, I.requestNormalize c w) = I.toOracleCodec.encodeQuery (I.decodeQuery c w) :=
    Prod.ext (I.request_decodeQuery c w).1.symm (I.request_decodeQuery c w).2.symm
  dsimp only [encodeOracle]
  rw [hreq, OracleCodec.wordOracle_encodeQuery]
  rfl

/-- Library infrastructure (no cited result): `I.requestNormalize` fixes every canonical request
word `I.request q` on its channel `I.channel q`. -/
@[simp] theorem requestNormalize_request {ι : Type} {E : ι → Type}
    (I : WordInterface E) (q : ι) :
    I.requestNormalize (I.channel q) (I.request q) = I.request q := by
  rw [← (I.request_decodeQuery (I.channel q) (I.request q)).2, I.decodeQuery_request]

/-- Library infrastructure (no cited result): `I.requestNormalize` is idempotent on every channel
and word. -/
@[simp] theorem requestNormalize_idem {ι : Type} {E : ι → Type}
    (I : WordInterface E) (c : I.Channel) (w : List Bool) :
    I.requestNormalize c (I.requestNormalize c w) = I.requestNormalize c w := by
  have ⟨hch, hreq⟩ := I.request_decodeQuery c w
  calc I.requestNormalize c (I.requestNormalize c w)
      = I.requestNormalize (I.channel (I.decodeQuery c w)) (I.request (I.decodeQuery c w)) := by
        rw [hch, hreq]
    _ = I.request (I.decodeQuery c w) := I.requestNormalize_request _
    _ = I.requestNormalize c w := hreq

/-- Library infrastructure (no cited result): on every canonical query request
`(I.channel q, I.request q)`, the total channel-encoded oracle agrees with
`I.toOracleCodec.wordOracle`. Off-image requests differ: `encodeOracle` normalizes the request via
`I.requestNormalize` before delegating to `I.toOracleCodec.wordOracle` and therefore still calls
`oracle` on `I.decodeQuery`, whereas `OracleCodec.wordOracle` directly returns `[]`. -/
theorem encodeOracle_eq_wordOracle {ι : Type} {E : ι → Type} {σ : Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q)) (q : ι) :
    I.encodeOracle oracle (I.channel q, I.request q) =
      I.toOracleCodec.wordOracle oracle (I.channel q, I.request q) := by
  dsimp only [encodeOracle]
  rw [I.requestNormalize_request]

/-- Library infrastructure (no cited result): the encoded oracle of a sum interface routes left and
right channel requests to the respective component encoded oracles. -/
theorem encodeOracle_sum {ι₁ ι₂ : Type} {E₁ : ι₁ → Type} {E₂ : ι₂ → Type} {σ : Type}
    (I₁ : WordInterface E₁) (I₂ : WordInterface E₂)
    (o₁ : (q : ι₁) → StateT σ PMF (E₁ q)) (o₂ : (q : ι₂) → StateT σ PMF (E₂ q)) :
    (I₁.sum I₂).encodeOracle (OracleComp.sumHandler o₁ o₂) =
      fun cw => Sum.elim (fun c₁ => I₁.encodeOracle o₁ (c₁, cw.2))
        (fun c₂ => I₂.encodeOracle o₂ (c₂, cw.2)) cw.1 := by
  funext cw s
  rcases cw with ⟨c | c, w⟩
  · rw [(I₁.sum I₂).encodeOracle_apply _ (.inl c), Sum.elim_inl, I₁.encodeOracle_apply]; rfl
  · rw [(I₁.sum I₂).encodeOracle_apply _ (.inr c), Sum.elim_inr, I₂.encodeOracle_apply]; rfl

/-- Library infrastructure: lower a single typed query to its channel request with reply
truncation to `limit` bits and decoding. -/
def lowerQuery {ι : Type} {E : ι → Type} (I : WordInterface E) (limit : ℕ) (q : ι) :
    WordOracleComp I.Channel (E q) :=
  I.decodeReply q <$> (List.take limit <$> ProbOracleComp.query (I.channel q, I.request q))

/-- Library infrastructure: running a single lowered query against `I.encodeOracle oracle` agrees
with running `oracle` when every supported reply fits in `limit` bits. -/
theorem runWith_lowerQuery {ι : Type} {E : ι → Type} {σ : Type}
    (I : WordInterface E) {limit : ℕ}
    (oracle : (q : ι) → StateT σ PMF (E q))
    (hfit : ∀ q s, ∀ x ∈ (oracle q s).support, (I.reply q x.1).length ≤ limit)
    (q : ι) (s : σ) :
    ProbOracleComp.runWith (I.encodeOracle oracle) (I.lowerQuery limit q) s =
      oracle q s := by
  rw [lowerQuery, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, encodeOracle_apply]
  generalize hq : I.decodeQuery (I.channel q) (I.request q) = q'
  rw [I.decodeQuery_request] at hq
  subst hq
  simp only [PMF.map_comp, Function.comp_def]
  exact (Probability.PMF.map_congr_on_support (oracle q s)
    (fun x : E q × σ => (I.decodeReply q (List.take limit (I.reply q x.1)), x.2)) id fun x hx => by
      rw [List.take_of_length_le (hfit q s x hx), I.decodeReply_reply]; rfl).trans (PMF.map_id _)

end WordInterface

namespace WordPort

/-- Library construction (no cited definition): disjoint sum of two typed word ports, e.g. for
`RoutedNetQ` / `RoutedNetR`. -/
def sum {Q₁ R₁ Q₂ R₂ : Type} (p₁ : WordPort Q₁ R₁) (p₂ : WordPort Q₂ R₂) :
    WordPort (Q₁ ⊕ Q₂) (R₁ ⊕ R₂) where
  query := encSum p₁.query p₂.query
  queryDecoder := Decoder.sum p₁.queryDecoder p₂.queryDecoder
  reply := encSum p₁.reply p₂.reply
  replyDecoder := Decoder.sum p₁.replyDecoder p₂.replyDecoder

/-- Library construction (no cited definition): party-port word presentation for `n ≥ 1`
(`[NeZero n]`) parties, encoding party indices in unary and decoding arbitrary words modulo `n`.
-/
def party {n : ℕ} [NeZero n] {In Out : Type} (input : WordPort In Out) :
    WordPort (Fin n × In) (Option Out) :=
  let finDecoder : Decoder (encFinEnum (Fin n)) :=
    { decode := fun w => ⟨Decoder.unary.decode w % n, Nat.mod_lt _ (NeZero.pos n)⟩
      decode_enc := fun i => Fin.ext (by
        change Decoder.unary.decode (encFinEnum (Fin n) i) % n = i.val
        rw [encFinEnum_fin_apply, Decoder.unary.decode_enc i.val]
        exact Nat.mod_eq_of_lt i.isLt)
      computable :=
        ((ComputableInPolyTime.unary_finMod (NeZero.pos n) (encFinEnum (Fin n))).comp
          Decoder.unary.computableInPolyTime).exists_degree }
  { query := encPair (encFinEnum (Fin n)) input.query
    queryDecoder := Decoder.pair finDecoder input.queryDecoder
    reply := encOption input.reply
    replyDecoder := Decoder.option input.replyDecoder }

/-- Library infrastructure (no cited result): `WordPort.party input` exposes the decoded party
index `Fin n` in polynomial time. -/
theorem computable_partyIndex {n : ℕ} [NeZero n] {In Out : Type}
    (input : WordPort In Out) :
    ComputableInPolyTime (fun w => ((WordPort.party (n := n) input).queryDecoder.decode w).1)
      encBits (encFinite (Fin n)) :=
  (ComputableInPolyTime.of_finite (id : Fin n → Fin n)
    (encIn := encFinEnum (Fin n)) (encOut := encFinite (Fin n))).comp
    ((ComputableInPolyTime.fst (encFinEnum (Fin n)) input.query).comp
      (WordPort.party (n := n) input).queryDecoder.computableInPolyTime)

end WordPort

end Crypto.Protocols.UC

namespace ProbOracleComp

open Crypto.Protocols.UC
open Cslib.Probability

/-- Library construction (no cited definition): lower a typed program `ProbOracleComp E α` to a
word program over `I.Channel` via `ProbOracleComp.simulate (I.lowerQuery limit)`, keeping private
samples private and truncating each word reply to `limit` bits before decoding. -/
def lowerWith {ι : Type} {E : ι → Type} {α : Type}
    (I : WordInterface E) (limit : ℕ) (program : ProbOracleComp E α) :
    WordOracleComp I.Channel α :=
  simulate (I.lowerQuery limit) program

/-- Library infrastructure (no cited result): a typed program lowered with reply bound `limit` has
the joint law of the typed program against every typed stateful oracle whose encoded replies fit in
`limit` bits. -/
theorem runWith_lowerWith {ι : Type} {E : ι → Type} {α : Type} (I : WordInterface E)
    {limit : ℕ} {σ : Type} (oracle : (q : ι) → StateT σ PMF (E q))
    (hfit : ∀ q s, ∀ x ∈ (oracle q s).support, (I.reply q x.1).length ≤ limit)
    (program : ProbOracleComp E α) (s : σ) :
    runWith (I.encodeOracle oracle) (program.lowerWith I limit) s =
      runWith oracle program s := by
  rw [lowerWith, runWith_simulate]
  congr 1
  funext q t
  exact I.runWith_lowerQuery oracle hfit q t

end ProbOracleComp

namespace Crypto.Protocols.UC.WordInterface

open Turing.MultiTapeTM
open Cslib.Probability

/-- Library infrastructure (no cited result): one lowered typed query, re-encoded, is uniform
strict oracle PPT on `I.Channel` when its channel, request, and reply bound are computed in
polynomial time. This consumes the `replyNormalize` and `computable_replyNormalize` interface
certificates. -/
theorem isOraclePPTOn_lowerWith_query {ι α : Type} {E : ι → Type}
    (I : WordInterface E) {input : α ↪ List Bool}
    {query : α → ι} {limit : α → ℕ}
    (hchannel : ComputableInPolyTime (fun a => I.channel (query a)) input (encFinite I.Channel))
    (hrequest : ComputableInPolyTime (fun a => I.request (query a)) input encBits)
    (hlimit : ComputableInPolyTime limit input encUnary) :
    IsOraclePPTOn input encBits (fun a =>
      I.reply (query a) <$>
        ProbOracleComp.lowerWith I (limit a) (ProbOracleComp.query (query a))) := by
  simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, lowerQuery,
    Functor.map_map, I.reply_decodeReply]
  exact (IsOraclePPTOn.query_take_with hchannel hrequest hlimit).map_with
    (I.computable_replyNormalize.comp
      ((hchannel.comp (ComputableInPolyTime.fst input encBits)).prod
        (ComputableInPolyTime.snd input encBits)))

/-- Library infrastructure (no cited result): a lowered, re-encoded decoded query
`I.decodeQuery (ch a) (word a)` is uniform strict oracle PPT when its channel, request word, and
reply bound are computable in polynomial time. -/
theorem isOraclePPTOn_lowerWith_decodeQuery {ι α : Type} {E : ι → Type}
    (I : WordInterface E) {input : α ↪ List Bool}
    {ch : α → I.Channel} {word : α → List Bool} {limit : α → ℕ}
    (hch : ComputableInPolyTime ch input (encFinite I.Channel))
    (hword : ComputableInPolyTime word input encBits)
    (hlimit : ComputableInPolyTime limit input encUnary) :
    IsOraclePPTOn input encBits (fun a =>
      I.reply (I.decodeQuery (ch a) (word a)) <$>
        ProbOracleComp.lowerWith I (limit a)
          (ProbOracleComp.query (I.decodeQuery (ch a) (word a)))) := by
  refine I.isOraclePPTOn_lowerWith_query ?_ ?_ hlimit
  · simpa only [fun a => (I.request_decodeQuery (ch a) (word a)).1] using hch
  · simpa only [Function.comp_def, ← fun a => (I.request_decodeQuery (ch a) (word a)).2] using
      I.computable_requestNormalize.comp (hch.prod hword)

/-! ### Canonical-request normalizer -/

/-- Library construction (no cited definition): rewrite every external word query `(c, w)` of a
word program to its canonical representative `(c, I.requestNormalize c w)`, preserving private coin
draws and returning oracle replies verbatim. -/
def normalizeRequests {ι α : Type} {E : ι → Type} (I : WordInterface E)
    (program : WordOracleComp I.Channel α) : WordOracleComp I.Channel α :=
  ProbOracleComp.simulate
    (fun cw => ProbOracleComp.query (cw.1, I.requestNormalize cw.1 cw.2)) program

/-- Library infrastructure (no cited result): request normalization preserves returned values. -/
@[simp] theorem normalizeRequests_pure {ι α : Type} {E : ι → Type} (I : WordInterface E)
    (a : α) : I.normalizeRequests (pure a) = pure a := rfl

/-- Library infrastructure (no cited result): request normalization distributes over bind. -/
@[simp] theorem normalizeRequests_bind {ι α β : Type} {E : ι → Type} (I : WordInterface E)
    (program : WordOracleComp I.Channel α) (next : α → WordOracleComp I.Channel β) :
    I.normalizeRequests (program >>= next) =
      (I.normalizeRequests program >>= fun a => I.normalizeRequests (next a)) :=
  ProbOracleComp.simulate_bind _ _ _

/-- Library infrastructure (no cited result): request normalization commutes with mapping. -/
@[simp] theorem normalizeRequests_map {ι α β : Type} {E : ι → Type} (I : WordInterface E)
    (f : α → β) (program : WordOracleComp I.Channel α) :
    I.normalizeRequests (f <$> program) = f <$> I.normalizeRequests program :=
  ProbOracleComp.simulate_map _ _ _

/-- Library infrastructure (no cited result): request normalization preserves private samples. -/
@[simp] theorem normalizeRequests_sample {ι α : Type} {E : ι → Type} (I : WordInterface E)
    (program : ProbComp α) :
    I.normalizeRequests (ProbOracleComp.sample program) = ProbOracleComp.sample program :=
  ProbOracleComp.simulate_sample _ _

/-- Library infrastructure (no cited result): request normalization rewrites a single query
`(c, w)` to `(c, I.requestNormalize c w)`. -/
@[simp] theorem normalizeRequests_query {ι : Type} {E : ι → Type} (I : WordInterface E)
    (cw : I.Channel × List Bool) :
    I.normalizeRequests (ProbOracleComp.query cw) =
      ProbOracleComp.query (cw.1, I.requestNormalize cw.1 cw.2) :=
  ProbOracleComp.simulate_query _ _

/-- Library infrastructure (no cited result): interacting with the total normalized oracle
`I.encodeOracle oracle` produces the exact same joint output and oracle-state distribution as
running `I.normalizeRequests program` against the strict non-mutating
`I.toOracleCodec.wordOracle oracle`, for every word program (including off-image queries). -/
theorem runWith_encodeOracle_eq_wordOracle_normalizeRequests {ι α σ : Type} {E : ι → Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q))
    (program : WordOracleComp I.Channel α) (s : σ) :
    ProbOracleComp.runWith (I.encodeOracle oracle) program s =
      ProbOracleComp.runWith (I.toOracleCodec.wordOracle oracle)
        (I.normalizeRequests program) s := by
  rw [normalizeRequests, ProbOracleComp.runWith_simulate]
  congr 1
  funext cw t
  rw [ProbOracleComp.runWith_query]
  rfl

/-- Library infrastructure (no cited result): interacting with `I.encodeOracle oracle` produces the
same joint output and oracle-state law as running the typed adaptation
`I.toOracleCodec.adapt (I.normalizeRequests program)` directly against `oracle`. -/
theorem runWith_encodeOracle_eq_adapt_normalizeRequests {ι α σ : Type} {E : ι → Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q))
    (program : WordOracleComp I.Channel α) (s : σ) :
    ProbOracleComp.runWith (I.encodeOracle oracle) program s =
      ProbOracleComp.runWith oracle (I.toOracleCodec.adapt (I.normalizeRequests program)) s := by
  rw [I.runWith_encodeOracle_eq_wordOracle_normalizeRequests, I.toOracleCodec.runWith_adapt]

/-- Library infrastructure (no cited result): every external query issued by
`I.normalizeRequests program` is a canonical `(I.channel q, I.request q)` pair. -/
theorem queriesSatisfy_normalizeRequests {ι α : Type} {E : ι → Type}
    (I : WordInterface E) (program : WordOracleComp I.Channel α) :
    (I.normalizeRequests program).QueriesSatisfy
      (fun cw => ∃ q : ι, cw = (I.channel q, I.request q)) := by
  refine ProbOracleComp.queriesSatisfy_simulate (fun cw => ?_) program
  exact ProbOracleComp.QueriesSatisfy.query
    ⟨I.decodeQuery cw.1 cw.2,
      Prod.ext (I.request_decodeQuery cw.1 cw.2).1.symm
        (I.request_decodeQuery cw.1 cw.2).2.symm⟩

/-- Library infrastructure (no cited result): any word program whose queries are already canonical
is fixed identically by `I.normalizeRequests`. -/
theorem normalizeRequests_eq_self {ι α : Type} {E : ι → Type}
    (I : WordInterface E) {program : WordOracleComp I.Channel α}
    (h : program.QueriesSatisfy (fun cw => ∃ q : ι, cw = (I.channel q, I.request q))) :
    I.normalizeRequests program = program := by
  rw [normalizeRequests, ProbOracleComp.simulate, OracleComp.substitute_eq_interpret]
  have hid : OracleComp.interpret OracleComp.query program = program := by
    rw [← OracleComp.substitute_eq_interpret]
    exact OracleComp.substitute_query_eq_self program
  refine (OracleComp.QueriesSatisfy.interpret_congr h fun q hq => ?_).trans hid
  cases q with
  | inl n => exact ProbOracleComp.sample_unifFin n
  | inr cw =>
    rcases hq with ⟨q, rfl⟩
    simp only [OracleComp.sumHandler, I.requestNormalize_request]
    rfl

/-- Library infrastructure (no cited result): canonical-request normalization is idempotent. -/
@[simp] theorem normalizeRequests_idempotent {ι α : Type} {E : ι → Type}
    (I : WordInterface E) (program : WordOracleComp I.Channel α) :
    I.normalizeRequests (I.normalizeRequests program) = I.normalizeRequests program :=
  I.normalizeRequests_eq_self (I.queriesSatisfy_normalizeRequests program)

/-- Library infrastructure (no cited result): every external query issued by a lowered typed
program `program.lowerWith I limit` is canonical. -/
theorem queriesSatisfy_lowerWith {ι α : Type} {E : ι → Type}
    (I : WordInterface E) (limit : ℕ) (program : ProbOracleComp E α) :
    (program.lowerWith I limit).QueriesSatisfy
      (fun cw => ∃ q : ι, cw = (I.channel q, I.request q)) := by
  refine ProbOracleComp.queriesSatisfy_simulate (fun q => ?_) program
  simp only [lowerQuery, OracleComp.queriesSatisfy_map_iff]
  exact ProbOracleComp.QueriesSatisfy.query ⟨q, rfl⟩

/-- Library infrastructure (no cited result): lowered typed programs are already canonical and
therefore fixed by `I.normalizeRequests`. -/
@[simp] theorem normalizeRequests_lowerWith {ι α : Type} {E : ι → Type}
    (I : WordInterface E) (limit : ℕ) (program : ProbOracleComp E α) :
    I.normalizeRequests (program.lowerWith I limit) = program.lowerWith I limit :=
  I.normalizeRequests_eq_self (I.queriesSatisfy_lowerWith limit program)

/-- Library infrastructure (no cited result): for any word program whose queries are all canonical,
`I.encodeOracle oracle` and `I.toOracleCodec.wordOracle oracle` induce the same joint output and
oracle-state law. -/
theorem runWith_encodeOracle_eq_wordOracle_of_queriesSatisfy {ι α σ : Type} {E : ι → Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q))
    {program : WordOracleComp I.Channel α}
    (h : program.QueriesSatisfy (fun cw => ∃ q : ι, cw = (I.channel q, I.request q)))
    (s : σ) :
    ProbOracleComp.runWith (I.encodeOracle oracle) program s =
      ProbOracleComp.runWith (I.toOracleCodec.wordOracle oracle) program s := by
  rw [I.runWith_encodeOracle_eq_wordOracle_normalizeRequests, I.normalizeRequests_eq_self h]

/-- Library infrastructure (no cited result): canonical-request normalization preserves external
query budgets. -/
theorem isQueryBounded_normalizeRequests {ι α : Type} {E : ι → Type}
    (I : WordInterface E) {program : WordOracleComp I.Channel α} {n : ℕ}
    (h : program.IsQueryBounded n) :
    (I.normalizeRequests program).IsQueryBounded n :=
  h.simulate fun cw => ProbOracleComp.IsQueryBounded.query (cw.1, I.requestNormalize cw.1 cw.2)

/-- Two machine configurations agree within `fuel` steps of their current answer heads. -/
private def AnswerAgree {k : ℕ} {Symbol State Oracle : Type} {input : List Symbol}
    (fuel : ℕ) (cfg₁ cfg₂ : Turing.MultiTapeMachine.Config k Symbol State Oracle input) : Prop :=
  cfg₁.tapes = cfg₂.tapes ∧
    ∀ o, (cfg₁.channels o).queryBuffer = (cfg₂.channels o).queryBuffer ∧
      (cfg₁.channels o).answerPos = (cfg₂.channels o).answerPos ∧
      ∀ i : ℕ, (i : ℤ) < (cfg₁.channels o).answerPos + fuel →
        (cfg₁.channels o).answer[i]? = (cfg₂.channels o).answer[i]?

private theorem answerAgree_refl {k : ℕ} {Symbol State Oracle : Type} {input : List Symbol}
    (fuel : ℕ) (cfg : Turing.MultiTapeMachine.Config k Symbol State Oracle input) :
    AnswerAgree fuel cfg cfg :=
  ⟨rfl, fun _ => ⟨rfl, rfl, fun _ _ => rfl⟩⟩

private theorem answerAgree_answerSymbols {k : ℕ} {Symbol State Oracle : Type} {input : List Symbol}
    {fuel : ℕ} {cfg₁ cfg₂ : Turing.MultiTapeMachine.Config k Symbol State Oracle input}
    (h : AnswerAgree (fuel + 1) cfg₁ cfg₂) :
    cfg₁.answerSymbols = cfg₂.answerSymbols := by
  funext o
  obtain ⟨_, hpos, hans⟩ := h.2 o
  dsimp only [Turing.MultiTapeMachine.Config.answerSymbols,
    Turing.MultiTapeMachine.Channel.answerSymbol]
  rw [← hpos]
  split_ifs with hnn
  · exact hans (cfg₁.channels o).answerPos.toNat (by omega)
  · rfl

private theorem answerAgree_step {k : ℕ} {Symbol State Oracle : Type} {input : List Symbol}
    {fuel : ℕ} {cfg₁ cfg₂ : Turing.MultiTapeMachine.Config k Symbol State Oracle input}
    (h : AnswerAgree (fuel + 1) cfg₁ cfg₂)
    (action : Turing.Action k Symbol State) (symbol : Oracle → Option Symbol)
    (move : Oracle → SignType) :
    AnswerAgree fuel (cfg₁.step action symbol move) (cfg₂.step action symbol move) := by
  refine ⟨congrArg action.apply h.1, fun o => ?_⟩
  obtain ⟨hq, hpos, hans⟩ := h.2 o
  refine ⟨congrArg (· ++ (symbol o).toList) hq, congrArg (· + (move o : ℤ)) hpos, fun i hi => ?_⟩
  have hmove : (move o : ℤ) ≤ 1 := by cases move o <;> decide
  exact hans i (by dsimp only [Turing.MultiTapeMachine.Config.step] at hi; omega)

private theorem answerAgree_receive {k : ℕ} {Symbol State Oracle : Type} {input : List Symbol}
    [DecidableEq Oracle] {fuel limit : ℕ} (hfl : fuel ≤ limit)
    {cfg₁ cfg₂ : Turing.MultiTapeMachine.Config k Symbol State Oracle input}
    (h : AnswerAgree (fuel + 1) cfg₁ cfg₂) (op : Oracle) (next : State) (answer : List Symbol) :
    AnswerAgree fuel (cfg₁.receive op next answer)
      (cfg₂.receive op next (List.take limit answer)) := by
  refine ⟨by simp only [Turing.MultiTapeMachine.Config.receive, h.1], fun o => ?_⟩
  by_cases ho : o = op
  · subst ho
    refine ⟨by simp only [Turing.MultiTapeMachine.Config.receive, Function.update_self],
      by simp only [Turing.MultiTapeMachine.Config.receive, Function.update_self], fun i hi => ?_⟩
    simp only [Turing.MultiTapeMachine.Config.receive, Function.update_self] at hi ⊢
    exact (List.getElem?_take_of_lt (by omega)).symm
  · obtain ⟨hq, hpos, hans⟩ := h.2 o
    simp only [Turing.MultiTapeMachine.Config.receive, Function.update_of_ne ho]
    exact ⟨hq, hpos, fun i hi => hans i (by omega)⟩

/-- A clocked `MultiTapeMachine` with `fuel ≤ limit` steps can read at most indices `< fuel` of any
oracle reply, so truncating every reply to `limit` symbols leaves its output program unchanged. -/
private theorem runFrom_eq_take_answers
    {k : ℕ} {Symbol State Oracle Query : Type}
    {Choose : Type → Type} {spec : OracleSpec.{0, 0} Query}
    {input : List Symbol} [DecidableEq Oracle]
    (machine : Turing.MultiTapeMachine k Symbol State Oracle Choose)
    (choose : Choose (Turing.MultiTapeMachine.Action k Symbol State Oracle) →
      OracleComp spec (Turing.MultiTapeMachine.Action k Symbol State Oracle))
    (query : Oracle → List Symbol → OracleComp spec (List Symbol)) {limit : ℕ} :
    ∀ (fuel : ℕ), fuel ≤ limit →
    ∀ (cfg₁ cfg₂ : Turing.MultiTapeMachine.Config k Symbol State Oracle input),
      AnswerAgree fuel cfg₁ cfg₂ →
      machine.runFrom choose query fuel cfg₁ =
        machine.runFrom choose (fun op w => List.take limit <$> query op w) fuel cfg₂
  | 0, _, cfg₁, cfg₂, h => by
    simp only [Turing.MultiTapeMachine.runFrom_zero, h.1]
  | fuel + 1, hfl, cfg₁, cfg₂, h => by
    unfold Turing.MultiTapeMachine.runFrom Turing.MultiTapeMachine.runConfigFrom
    cases hs : cfg₁.tapes.state with
    | none =>
      have hs₂ : cfg₂.tapes.state = none := by rw [← h.1, hs]
      simp only [hs₂, map_pure, h.1]
    | some state =>
      simp only [← h.1, hs, map_bind, answerAgree_answerSymbols h]
      congr 1 with act : 1
      cases act with
      | step action symbol move =>
        exact runFrom_eq_take_answers machine choose query fuel (Nat.le_of_succ_le hfl)
          _ _ (answerAgree_step h action symbol move)
      | query op next =>
        simp only [map_bind, bind_map_left, (h.2 op).1]
        congr 1 with answer : 1
        exact runFrom_eq_take_answers machine choose query fuel (Nat.le_of_succ_le hfl)
          _ _ (answerAgree_receive (Nat.le_of_succ_le hfl) h op next answer)

/-- Truncating every oracle reply to `fuel` bits leaves `machine.runOracle fuel input` unchanged.
-/
private theorem runOracle_eq_simulate_take
    {k : ℕ} {Control Operation : Type} [DecidableEq Operation]
    (machine : Turing.MultiTapePTM k Bool Control Operation)
    (fuel : ℕ) (input : List Bool) :
    machine.runOracle fuel input =
      ProbOracleComp.simulate (fun cw => List.take fuel <$> ProbOracleComp.query cw)
        (machine.runOracle fuel input) := by
  simp only [Turing.MultiTapePTM.runOracle, Turing.MultiTapePTM.run, Turing.MultiTapePTM.runFrom,
    Turing.MultiTapePTM.runConfigFrom, ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    OracleComp.interpret_map, Turing.MultiTapeMachine.interpret_runConfigFrom]
  have hsample :
      OracleComp.interpret
        (OracleComp.sumHandler
          (fun n =>
            ProbOracleComp.sample (spec := fun _ : Operation × List Bool => List Bool)
              (ProbComp.unifFin n))
          (fun cw =>
            List.take fuel <$> ProbOracleComp.query
              (spec := fun _ : Operation × List Bool => List Bool) cw))
        (ProbOracleComp.sample (spec := fun _ : Operation × List Bool => List Bool)
          (ProbComp.uniform Bool)) =
      ProbOracleComp.sample (spec := fun _ : Operation × List Bool => List Bool)
        (ProbComp.uniform Bool) := by
    rw [← OracleComp.substitute_eq_interpret]
    exact ProbOracleComp.simulate_sample _ _
  have hquery : ∀ (oracle : Operation) (word : List Bool),
      OracleComp.interpret
        (OracleComp.sumHandler
          (fun n =>
            ProbOracleComp.sample (spec := fun _ : Operation × List Bool => List Bool)
              (ProbComp.unifFin n))
          (fun cw =>
            List.take fuel <$> ProbOracleComp.query
              (spec := fun _ : Operation × List Bool => List Bool) cw))
        (ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
          (oracle, word)) =
      List.take fuel <$> ProbOracleComp.query
        (spec := fun _ : Operation × List Bool => List Bool) (oracle, word) :=
    fun oracle word => by
      rw [← OracleComp.substitute_eq_interpret]
      exact ProbOracleComp.simulate_query _ (oracle, word)
  simp only [hsample, hquery]
  exact runFrom_eq_take_answers machine _ _ fuel le_rfl _ _ (answerAgree_refl _ _)

/-- Library infrastructure (no cited result): canonical-request normalization preserves uniform
strict oracle PPT for arbitrary word adversaries, with no extra reply-length assumption: a
polynomial-time realizing machine running for `T` steps cannot inspect beyond the first `T` bits
of any oracle reply, so normalizing each request and taking `T` reply bits realizes
`I.normalizeRequests` identically against every stateful external oracle. -/
theorem isOraclePPTOn_normalizeRequests {ι α β : Type} {E : ι → Type}
    (I : WordInterface E) {input : α ↪ List Bool} {output : β ↪ List Bool}
    {program : α → WordOracleComp I.Channel β}
    (hprogram : IsOraclePPTOn input output program) :
    IsOraclePPTOn input output (fun a => I.normalizeRequests (program a)) := by
  obtain ⟨_, k, Control, hfiniteC, machine, c, d, hrealize⟩ := hprogram
  let _ := hfiniteC
  let fuel (a : α) : ℕ := c * ((input a).length + 1) ^ d
  have hfuel : ComputableInPolyTime fuel input encUnary :=
    (by fun_prop : ComputableInPolyTime (fun n => c * (n + 1) ^ d) encUnary encUnary).comp
      (ComputableInPolyTime.length_bits.comp
        ((ComputableInPolyTime.id' (encIn := input)).of_enc_eq fun _ => rfl))
  let handler (a : α) (cw : I.Channel × List Bool) : WordOracleComp I.Channel (List Bool) :=
    List.take (fuel a) <$> ProbOracleComp.query (cw.1, I.requestNormalize cw.1 cw.2)
  have hhandler :
      IsOraclePPTOn (encPair input (encPair (encFinite I.Channel) encBits)) encBits
        (fun p => handler p.1 p.2) :=
    IsOraclePPTOn.query_take_with (opEncoding := encFinite I.Channel)
      ((ComputableInPolyTime.fst (encFinite I.Channel) encBits).comp
        (ComputableInPolyTime.snd input (encPair (encFinite I.Channel) encBits)))
      (I.computable_requestNormalize.comp
        (ComputableInPolyTime.snd input (encPair (encFinite I.Channel) encBits)))
      (hfuel.comp (ComputableInPolyTime.fst input (encPair (encFinite I.Channel) encBits)))
  have hsim :=
    (IsOraclePPTOn.of_machine (input := input) machine c d).interpret_preprocess_open'
      (operationEncoding := encFinite I.Channel)
      (handler := handler) (prepare := id) (resources := fun a _ => fuel a)
      ComputableInPolyTime.id' hhandler
      (hfuel.comp (ComputableInPolyTime.fst input encBits))
      (fun _ _ _ hmem => by
        obtain ⟨w, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hmem
        exact List.length_take_le _ _)
  refine IsOraclePPTOn.iff_encoded.mpr (hsim.congr fun a State oracle s => ?_)
  let normOracle : I.Channel × List Bool → StateT State PMF (List Bool) :=
    fun cw => oracle (cw.1, I.requestNormalize cw.1 cw.2)
  have hstep : (fun cw => ProbOracleComp.runWith oracle (handler a cw)) =
      (fun cw => ProbOracleComp.runWith normOracle
        (List.take (fuel a) <$> ProbOracleComp.query cw)) := by
    funext cw t
    simp only [handler, normOracle, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
  rw [← OracleComp.substitute_eq_interpret]
  change ProbOracleComp.runWith oracle
      (ProbOracleComp.simulate (handler a) (machine.runOracle (fuel a) (input a))) s = _
  rw [ProbOracleComp.runWith_simulate, hstep, ← ProbOracleComp.runWith_simulate,
    ← runOracle_eq_simulate_take machine (fuel a) (input a),
    ← hrealize a State normOracle s, ← I.normalizeRequests_map,
    normalizeRequests, ProbOracleComp.runWith_simulate]
  congr 1
  funext cw t
  rw [ProbOracleComp.runWith_query]

end Crypto.Protocols.UC.WordInterface

end Cslib

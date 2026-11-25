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
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Probability.PMF.Map

/-!
# Binary word presentation of typed UC interfaces

Library infrastructure toward #6043 (no cited result): typed UC machines and environments
communicate over indexed query-reply specifications `E : ι → Type` (`partySpec`, `netSpec`,
`protocolSpec`, `execSpec`), whereas `WordOracleComp` and `IsOraclePPTOn` execute on finite channel
tags carrying `List Bool` payloads. This module supplies the lowering from typed `ProbOracleComp`
programs to `WordOracleComp` programs over finitely many channels, together with the dual encoded
oracle and single-query strict oracle PPT certificate.

## Modelling decisions and restrictions

* **Named structures.** `WordPort` packages total polynomial-time decoders for queries and replies
  on a single `netSpec Q R` port, and `WordInterface` packages channel routing, total query/reply
  decoding, and per-channel normalization cost certificates (`replyNormalize`, `requestNormalize`).
* **Relation to `Cslib.OracleCodec`.** `WordInterface.toOracleCodec` builds a partial
  `OracleCodec I.Channel ι E` whose `decodeQuery` recognizes valid `(I.channel q, I.request q)`
  requests. `WordInterface.encodeOracle` normalizes each incoming word with `I.requestNormalize`
  and delegates to `I.toOracleCodec.wordOracle`; by `I.request_decodeQuery`, the normalized pair is
  the encoded query of `I.decodeQuery cw.1 cw.2`, so off-image requests still call `oracle` once
  (`WordInterface.encodeOracle_apply`), while canonical requests agree directly with
  `I.toOracleCodec.wordOracle` (`WordInterface.encodeOracle_eq_wordOracle`). Total request/reply
  decoders and the finite `Channel` normalization certificates (`replyNormalize`,
  `requestNormalize`) are needed so a word machine can normalize arbitrary incoming or outgoing
  words in polynomial time.
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
* `Cslib.Crypto.Protocols.UC.WordInterface.toOracleCodec`, `.encodeOracle`, `.lowerQuery`:
  `OracleCodec` view, total channel-encoded oracle, and single-query lowering handler.
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

/-- Library infrastructure (no cited result): on every canonical query request
`(I.channel q, I.request q)`, the total channel-encoded oracle agrees with
`I.toOracleCodec.wordOracle`. Off-image requests differ: `encodeOracle` normalizes the request via
`I.requestNormalize` before delegating to `I.toOracleCodec.wordOracle` and therefore still calls
`oracle` on `I.decodeQuery`, whereas `OracleCodec.wordOracle` directly returns `[]`. -/
theorem encodeOracle_eq_wordOracle {ι : Type} {E : ι → Type} {σ : Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q)) (q : ι) :
    I.encodeOracle oracle (I.channel q, I.request q) =
      I.toOracleCodec.wordOracle oracle (I.channel q, I.request q) := by
  have hnorm : I.requestNormalize (I.channel q) (I.request q) = I.request q := by
    have h := (I.request_decodeQuery (I.channel q) (I.request q)).2
    rw [I.decodeQuery_request] at h
    exact h.symm
  dsimp only [encodeOracle]
  rw [hnorm]

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
  · rw [(I₁.sum I₂).encodeOracle_apply (OracleComp.sumHandler o₁ o₂) (Sum.inl c) w s,
      Sum.elim_inl, I₁.encodeOracle_apply o₁ c w s]
    rfl
  · rw [(I₁.sum I₂).encodeOracle_apply (OracleComp.sumHandler o₁ o₂) (Sum.inr c) w s,
      Sum.elim_inr, I₂.encodeOracle_apply o₂ c w s]
    rfl

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
  have hid :
      (oracle q s).map
          (fun x : E q × σ => (I.decodeReply q (List.take limit (I.reply q x.1)), x.2)) =
        (oracle q s).map id := by
    refine Probability.PMF.map_congr_on_support (oracle q s) _ id fun x hx => ?_
    rw [List.take_of_length_le (hfit q s x hx), I.decodeReply_reply]
    rfl
  exact hid.trans (PMF.map_id _)

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
      encBits (encFinite (Fin n)) := by
  have hdec : ComputableInPolyTime (WordPort.party (n := n) input).queryDecoder.decode
      encBits (encPair (encFinEnum (Fin n)) input.query) :=
    (WordPort.party (n := n) input).queryDecoder.computableInPolyTime
  have hfst : ComputableInPolyTime
      (fun w => ((WordPort.party (n := n) input).queryDecoder.decode w).1)
      encBits (encFinEnum (Fin n)) :=
    (ComputableInPolyTime.fst (encFinEnum (Fin n)) input.query).comp hdec
  exact (ComputableInPolyTime.of_finite (id : Fin n → Fin n)
    (encIn := encFinEnum (Fin n)) (encOut := encFinite (Fin n))).comp hfst

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
  have heq :
      (fun a => I.reply (query a) <$>
          ProbOracleComp.lowerWith I (limit a) (ProbOracleComp.query (query a))) =
        fun a => I.replyNormalize (I.channel (query a)) <$>
          (List.take (limit a) <$>
            ProbOracleComp.query (spec := fun _ : I.Channel × List Bool => List Bool)
              (I.channel (query a), I.request (query a))) := by
    funext a
    simp only [ProbOracleComp.lowerWith, ProbOracleComp.simulate_query, lowerQuery,
      Functor.map_map, I.reply_decodeReply]
  rw [heq]
  refine (IsOraclePPTOn.query_take_with hchannel hrequest hlimit).map_with
    (f := fun a reply => I.replyNormalize (I.channel (query a)) reply) ?_
  exact I.computable_replyNormalize.comp
    ((hchannel.comp (ComputableInPolyTime.fst input encBits)).prod
      (ComputableInPolyTime.snd input encBits))

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
  refine I.isOraclePPTOn_lowerWith_query
    (query := fun a => I.decodeQuery (ch a) (word a)) (limit := limit) ?_ ?_ hlimit
  · have heq : (fun a => I.channel (I.decodeQuery (ch a) (word a))) = ch :=
      funext fun a => (I.request_decodeQuery (ch a) (word a)).1
    rwa [heq]
  · have heq : (fun a => I.request (I.decodeQuery (ch a) (word a))) =
        fun a => I.requestNormalize (ch a) (word a) :=
      funext fun a => (I.request_decodeQuery (ch a) (word a)).2
    rw [heq]
    exact I.computable_requestNormalize.comp (hch.prod hword)

end Crypto.Protocols.UC.WordInterface

end Cslib

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
import CslibFrontier.Probability.PMF.Map

/-!
# Binary word presentation of typed UC interfaces

Library infrastructure toward #6043 (no cited result): typed UC machines and environments
communicate over indexed query-reply specifications `E : ι → Type` (`partySpec`, `netSpec`,
`protocolSpec`, `execSpec`), whereas `WordOracleComp` and `IsOraclePPTOn` execute on finite channel
tags carrying `List Bool` payloads. This module supplies the lowering from typed `ProbOracleComp`
programs to `WordOracleComp` programs over finitely many channels, together with the dual encoded
oracle.

## Modelling decisions and restrictions

* **Named structures.** `WordPort` packages total polynomial-time decoders for queries and replies
  on a single `netSpec Q R` port, and `WordInterface` packages channel routing, total query/reply
  decoding, and per-channel normalization cost certificates (`replyNormalize`, `requestNormalize`).
* **Unary `Fin n` party rank (`[NeZero n]`).** `WordPort.party` encodes party indices in unary
  and decodes arbitrary words modulo `n`. Because a total decoder requires a nonempty target type,
  `n ≥ 1` (`[NeZero n]`) is required on `WordPort.party`.
* **Interface coverage.** The constructors `WordInterface.empty`, `WordInterface.net`, and
  `WordInterface.sum` cover `OracleSpec.empty`, `netSpec`, and `⊕ₒ`, which suffices for
  `Execution`, `Composition`, and `DummyAdversary`. Dependent-reply interfaces such as
  `SSP.sessionSpec` (`MultiSession`) are not covered here.
* **Explicit reply truncation (`limit`).** `ProbOracleComp.lowerWith I limit` truncates each word
  reply to `limit` bits via `List.take limit` before decoding, matching the strict clock contract
  of `IsOraclePPTOn.query_take`. When every reply of a typed stateful oracle encodes within `limit`
  bits, `ProbOracleComp.runWith_lowerWith` equates the lowered word run against
  `I.encodeOracle oracle` with the original typed run.

## Main definitions

* `Cslib.Crypto.Protocols.UC.WordPort`: total query and reply decoders for a `netSpec` port.
* `Cslib.Crypto.Protocols.UC.WordInterface`: finite-channel word presentation of a typed interface.
* `Cslib.Crypto.Protocols.UC.WordInterface.empty`, `.net`, `.sum`, `.protocol`, `.exec`,
  `WordPort.sum`, `WordPort.party`: constructors and UC interface abbreviations.
* `Cslib.ProbOracleComp.lowerWith`: lower a typed `ProbOracleComp` with reply bound `limit`.
* `Cslib.Crypto.Protocols.UC.WordInterface.encodeOracle`: present a typed oracle on channels.

## Main results

* `Cslib.ProbOracleComp.lowerWith_pure`, `.lowerWith_bind`, `.lowerWith_map`,
  `.lowerWith_sample`, `.lowerWith_query`: structural equations for lowering.
* `Cslib.ProbOracleComp.runWith_lowerWith`: lowered execution agrees with typed execution when
  every supported reply fits within `limit` bits.
-/

@[expose] public section

namespace Cslib

namespace Crypto.Protocols.UC

open Turing.MultiTapeTM
open Cslib.Probability

/-- A binary presentation of one typed port `netSpec Q R`: total decoders for its queries and
replies. -/
structure WordPort (Q R : Type) : Type where
  query : Q ↪ List Bool
  queryDecoder : Decoder query
  reply : R ↪ List Bool
  replyDecoder : Decoder reply

/-- A typed interface presented over finitely many word channels. -/
structure WordInterface {ι : Type} (E : ι → Type) : Type 1 where
  Channel : Type
  [decEq : DecidableEq Channel]
  [finite : Finite Channel]
  channel : ι → Channel
  request : ι → List Bool
  decodeQuery : Channel → List Bool → ι
  decodeQuery_request : ∀ q, decodeQuery (channel q) (request q) = q
  reply : (q : ι) → E q ↪ List Bool
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

/-- Word interface for a UC protocol `protocolSpec n In Out NetQ NetR`. -/
abbrev protocol {n : ℕ} {In Out NetQ NetR : Type}
    (party : WordPort (Fin n × In) (Option Out)) (netPort : WordPort NetQ NetR) :
    WordInterface (protocolSpec n In Out NetQ NetR) :=
  sum (net party) (net netPort)

/-- Word interface for a UC execution environment `execSpec n In Out AdvQ AdvR`. -/
abbrev exec {n : ℕ} {In Out AdvQ AdvR : Type}
    (party : WordPort (Fin n × In) (Option Out)) (adv : WordPort AdvQ AdvR) :
    WordInterface (execSpec n In Out AdvQ AdvR) :=
  sum (net party) (net adv)

/-- Present a typed stateful oracle as a word oracle over `I.Channel`. -/
noncomputable def encodeOracle {ι : Type} {E : ι → Type} {σ : Type}
    (I : WordInterface E) (oracle : (q : ι) → StateT σ PMF (E q)) :
    I.Channel × List Bool → StateT σ PMF (List Bool) :=
  fun cw s =>
    let q := I.decodeQuery cw.1 cw.2
    (oracle q s).map fun (r, s') => (I.reply q r, s')

end WordInterface

namespace WordPort

/-- Disjoint sum of two typed word ports, e.g. for `RoutedNetQ` / `RoutedNetR`. -/
def sum {Q₁ R₁ Q₂ R₂ : Type} (p₁ : WordPort Q₁ R₁) (p₂ : WordPort Q₂ R₂) :
    WordPort (Q₁ ⊕ Q₂) (R₁ ⊕ R₂) where
  query := encSum p₁.query p₂.query
  queryDecoder := Decoder.sum p₁.queryDecoder p₂.queryDecoder
  reply := encSum p₁.reply p₂.reply
  replyDecoder := Decoder.sum p₁.replyDecoder p₂.replyDecoder

/-- Party-port word presentation for `n ≥ 1` (`[NeZero n]`) parties, encoding party indices in
unary and decoding arbitrary words modulo `n`. -/
def party {n : ℕ} [NeZero n] {In Out : Type} (input : WordPort In Out) :
    WordPort (Fin n × In) (Option Out) :=
  let encFin : Fin n ↪ List Bool :=
    ⟨fun i => encUnary i.val, fun _ _ h => Fin.val_injective (encUnary.injective h)⟩
  let finDecoder : Decoder encFin :=
    { decode := fun w => ⟨Decoder.unary.decode w % n, Nat.mod_lt _ (NeZero.pos n)⟩
      decode_enc := fun i => Fin.ext (by
        change Decoder.unary.decode (encUnary i.val) % n = i.val
        rw [Decoder.unary.decode_enc i.val]
        exact Nat.mod_eq_of_lt i.isLt)
      computable := by
        exact ((ComputableInPolyTime.unary_finMod (NeZero.pos n) encFin).comp
          Decoder.unary.computableInPolyTime).exists_degree }
  { query := encPair encFin input.query
    queryDecoder := Decoder.pair finDecoder input.queryDecoder
    reply := encOption input.reply
    replyDecoder := Decoder.option input.replyDecoder }

end WordPort

end Crypto.Protocols.UC

namespace ProbOracleComp

open Crypto.Protocols.UC
open Cslib.Probability

/-- Lower a typed program `ProbOracleComp E α` to a word program over `I.Channel`, keeping private
samples private and truncating each word reply to `limit` bits before decoding. -/
def lowerWith {ι : Type} {E : ι → Type} {α : Type}
    (I : WordInterface E) (limit : ℕ) (program : ProbOracleComp E α) :
    WordOracleComp I.Channel α :=
  OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => sample (ProbComp.unifFin n))
      (fun q =>
        I.decodeReply q <$> (List.take limit <$> query (I.channel q, I.request q))))
    program

variable {ι : Type} {E : ι → Type} {α β : Type}

/-- Lowering a pure value returns it directly. -/
@[simp]
theorem lowerWith_pure (I : WordInterface E) (limit : ℕ) (a : α) :
    (pure a : ProbOracleComp E α).lowerWith I limit = pure a :=
  rfl

/-- Lowering commutes with sequential composition. -/
@[simp]
theorem lowerWith_bind (I : WordInterface E) (limit : ℕ)
    (program : ProbOracleComp E α) (next : α → ProbOracleComp E β) :
    (program >>= next).lowerWith I limit =
      program.lowerWith I limit >>= fun a => (next a).lowerWith I limit :=
  OracleComp.interpret_bind _ _ _

/-- Lowering commutes with deterministic postprocessing. -/
@[simp]
theorem lowerWith_map (I : WordInterface E) (limit : ℕ)
    (f : α → β) (program : ProbOracleComp E α) :
    (f <$> program).lowerWith I limit = f <$> program.lowerWith I limit :=
  OracleComp.interpret_map _ _ _

/-- Lowering leaves embedded closed sampling programs unchanged. -/
@[simp]
theorem lowerWith_sample (I : WordInterface E) (limit : ℕ) (program : ProbComp α) :
    (sample program : ProbOracleComp E α).lowerWith I limit = sample program := by
  rw [lowerWith, interpret_sample]
  simp only [sample_unifFin, ← OracleComp.substitute_eq_interpret]
  rfl

/-- Lowering a single typed query calls `I.channel q` with `I.request q`, truncates the word
reply to `limit` bits, and decodes it via `I.decodeReply q`. -/
@[simp]
theorem lowerWith_query (I : WordInterface E) (limit : ℕ) (q : ι) :
    (query q : ProbOracleComp E (E q)).lowerWith I limit =
      I.decodeReply q <$> (List.take limit <$> query (I.channel q, I.request q)) :=
  interpret_query _ _ _

/-- Library infrastructure (no cited result): a typed program lowered with reply bound `limit` has
the joint law of the typed program against every typed stateful oracle whose encoded replies fit in
`limit` bits. -/
theorem runWith_lowerWith (I : WordInterface E) {limit : ℕ} {σ : Type}
    (oracle : (q : ι) → StateT σ PMF (E q))
    (hfit : ∀ q s, ∀ x ∈ (oracle q s).support, (I.reply q x.1).length ≤ limit)
    (program : ProbOracleComp E α) (s : σ) :
    runWith (I.encodeOracle oracle) (program.lowerWith I limit) s =
      runWith oracle program s := by
  rw [lowerWith, runWith_interpret_sumHandler]
  congr 1 with q t : 2
  rw [runWith_map, runWith_map, runWith_query]
  dsimp only [WordInterface.encodeOracle]
  rw [I.decodeQuery_request q]
  simp only [PMF.map_comp, Function.comp_def]
  have hid :
      (oracle q t).map
          (fun x : E q × σ => (I.decodeReply q (List.take limit (I.reply q x.1)), x.2)) =
        (oracle q t).map id := by
    refine Probability.PMF.map_congr_on_support (oracle q t) _ id fun x hx => ?_
    rw [List.take_of_length_le (hfit q t x hx), I.decodeReply_reply]
    rfl
  simpa [runWith_query] using hid.trans (PMF.map_id _)

end ProbOracleComp

end Cslib

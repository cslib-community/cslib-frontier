/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.Signature.Bridge
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Polynomial-time reduction witnesses for anonymous tokens and VOLE-ACT

This module provides uniform strict-PPT / oracle-PPT word-level realizations and runtime
certificates for the extracted-model reductions in `CslibFrontier.Crypto.Protocols.AnonymousToken`
(tracked under #7068):

* `Cslib.Crypto.AnonymousToken.targetForgerWord` (`Basic.targetForger`),
* `Cslib.Crypto.AnonymousToken.bindingReductionWord` (`Basic.bindingReduction`),
* `Cslib.Crypto.AnonymousToken.Conservation.noteForgerWord` (`Conservation.noteForger`), and
* `Cslib.Crypto.AnonymousToken.Conservation.commitmentBindingReductionWord`
  (`Conservation.commitmentBindingReduction`).

Each reduction is certified directly against `IsPPTOn` / `IsOraclePPTOn` / `IsPPT` / `IsOraclePPT`
with truncated adaptive oracle replies (`IsOraclePPTOn.query_take`) and proved equal in `PMF` law
to its typed extracted-model counterpart when instantiated on a `WordSignatureScheme` and a
polynomial-time target / commitment function. Combining `WordSignatureScheme.EUFCMA` and
`CollisionResistant` yields asymptotic word-level unforgeability and extracted credit conservation
without introducing any new hardness assumptions or leaking `ComputableTidily` / `IsTidy`.

This module stays within the extracted-witness asymptotic word model; VOLEitH witness extraction,
zero-knowledge, issuer V4 range / policy enforcement, and `RandomTarget.reduceRedemptions` remain
separate (#7068).

Because word-level adversaries (`WordExtractedForgerOf`, `WordExtractedAdversary`) emit arbitrary
bit strings `w : List Bool` as oracle queries, both reductions (`targetForgerWordOf`,
`noteForgerHandlerWord`) and their corresponding word games (`extractedTokenWordGame`,
`extractedConservationWordGame`, via `.toTyped`) process every query as the typed value returned
by its total `Decoder` (`payloadDecoderOf D`, `wordRequestDecoder`), rather than rejecting
malformed query words as parse errors under a `PartialDecoder`. Because these total decoders
still parse pieces of the input (e.g., pair components or the leading tag bit selecting issue
vs. spend before decoding the tail), the resulting typed value can depend on the malformed input.
-/

@[expose] public section

namespace Cslib.Crypto.AnonymousToken

open Probability Turing.MultiTapeTM

/-! ### Encodings and total decoders -/

section Encodings

variable {Message : Type}

/-- Encode a semantic payload `(message, opening)` with bit-string opening randomness. -/
enc_structure encPayloadOf (encM : Message ↪ List Bool) : Payload Message (List Bool) where
  message : encM, opening : encBits

attribute [fun_prop] encPayloadOf_message_polyTime encPayloadOf_opening_polyTime
  encPayloadOf_mk_polyTime

/-- Encode a certified token `(payload, signature)` with bit-string signature. -/
enc_structure encTokenOf (encM : Message ↪ List Bool) :
    Token Message (List Bool) (List Bool) where
  payload : (encPayloadOf encM), signature : encBits

attribute [fun_prop] encTokenOf_payload_polyTime encTokenOf_signature_polyTime
  encTokenOf_mk_polyTime

/-- Encode a binding witness `(first, second)` over `Payload Message (List Bool)`. -/
enc_structure encBindingWitnessOf (encM : Message ↪ List Bool) :
    BindingWitness Message (List Bool) where
  first : (encPayloadOf encM), second : (encPayloadOf encM)

attribute [fun_prop] encBindingWitnessOf_first_polyTime encBindingWitnessOf_second_polyTime
  encBindingWitnessOf_mk_polyTime

end Encodings

/-- Encoding of one `(payload, signature)` entry in an extracted transcript. -/
abbrev encPayloadLogEntryOf {Message : Type} (encM : Message ↪ List Bool) :
    (Payload Message (List Bool) × List Bool) ↪ List Bool :=
  encPair (encPayloadOf encM) encBits

/-- Encoding of an extracted transcript `log`. -/
abbrev encPayloadLogOf {Message : Type} (encM : Message ↪ List Bool) :
    List (Payload Message (List Bool) × List Bool) ↪ List Bool :=
  encList (encPayloadLogEntryOf encM)

section ExecutionEncoding

variable {Message : Type}

/-- Encode an extracted execution `(publicKey, output, log)`. -/
enc_structure encExecutionOf (encM : Message ↪ List Bool) :
    Execution (List Bool) Message (List Bool) (List Bool) where
  publicKey : encBits, output : (encTokenOf encM), log : (encPayloadLogOf encM)

attribute [fun_prop] encExecutionOf_publicKey_polyTime encExecutionOf_output_polyTime
  encExecutionOf_log_polyTime encExecutionOf_mk_polyTime

end ExecutionEncoding

/-- Encoding of a bit-string payload `(msg, opening)`. -/
abbrev encWordPayload : Payload (List Bool) (List Bool) ↪ List Bool := encPayloadOf encBits

/-- Encoding of a bit-string token `(payload, signature)`. -/
abbrev encWordToken : Token (List Bool) (List Bool) (List Bool) ↪ List Bool := encTokenOf encBits

/-- Encoding of a bit-string binding witness. -/
abbrev encWordBindingWitness : BindingWitness (List Bool) (List Bool) ↪ List Bool :=
  encBindingWitnessOf encBits

/-- Encoding of an optional bit-string binding witness. -/
abbrev encOptionWordBindingWitness :
    Option (BindingWitness (List Bool) (List Bool)) ↪ List Bool :=
  encOption encWordBindingWitness

/-- Encoding of a public word pair `(spk, ck)` or `(msg, sig)`. -/
abbrev encWordPair : (List Bool × List Bool) ↪ List Bool := encPair encBits encBits

/-- Encoding of `(n, ck)` passed to parameterized collision and binding reductions. -/
abbrev encParamInput : (ℕ × List Bool) ↪ List Bool := encPair encUnary encBits

/-- Encoding of `(n, (spk, ck))` supplied to parameterized anonymous-token reductions. -/
abbrev encPublicInput : (ℕ × (List Bool × List Bool)) ↪ List Bool :=
  encPair encUnary encWordPair

/-- Encoding of `((n, ck), (pk, sk))` during logged execution against a word signature scheme. -/
abbrev encExtractedCaller : ((ℕ × List Bool) × (List Bool × List Bool)) ↪ List Bool :=
  encPair encParamInput encWordPair

/-- Encoding of `(n, L)` supplied to signature-length bounds. -/
abbrev encNatPair : (ℕ × ℕ) ↪ List Bool := encPair encUnary encUnary

/-- Encoding of `(ck, (msg, opening))` supplied to keyed target encoders. -/
abbrev encKeyedWordPair : (List Bool × (List Bool × List Bool)) ↪ List Bool :=
  encPair encBits encWordPair

/-- Encoding of `(n, (ck, (msg, opening)))` supplied to keyed target encoders. -/
abbrev encTargetArgsOf {Message : Type} (encM : Message ↪ List Bool) :
    (ℕ × (List Bool × (Message × List Bool))) ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encM encBits))

/-- Encoding of `(n, (ck, (msg, opening)))` supplied to keyed bit-string target encoders. -/
abbrev encTargetArgs : (ℕ × (List Bool × (List Bool × List Bool))) ↪ List Bool :=
  encTargetArgsOf encBits

/-- Total decoder for `encWordPair`. -/
def wordPairDecoder : Decoder encWordPair :=
  Decoder.pair Decoder.bits Decoder.bits

/-- Total decoder for `encPayloadOf encM` given a total decoder for `encM`. -/
def payloadDecoderOf {Message : Type} {encM : Message ↪ List Bool}
    (D : Decoder encM) : Decoder (encPayloadOf encM) :=
  (Decoder.pair D Decoder.bits).map
    (fun p => ⟨p.1, p.2⟩) (fun p => (p.message, p.opening))
    (fun _ => rfl) (fun p => (encPayloadOf_apply encM ⟨p.1, p.2⟩).symm)

/-- Total decoder for `encWordPayload`. -/
abbrev wordPayloadDecoder : Decoder encWordPayload := payloadDecoderOf Decoder.bits

/-! ### Word-level extracted forgers and `targetForgerWord` -/

/-- A word-level extracted forger receives `(n, pkParam)` and queries the word payload channel
`((), encPayloadOf encM payload)` for bit-string signatures, returning a `Token`. -/
abbrev WordExtractedForgerOf (Message : Type) :=
  ℕ → List Bool → WordOracleComp Unit (Token Message (List Bool) (List Bool))

/-- Restrict a word-level extracted forger at verification key `spk` and auxiliary parameter `ck`
encoded via `encWordPair (spk, ck)`. -/
def WordExtractedForgerOf.atKey {Message : Type}
    (A : WordExtractedForgerOf Message) (ck : List Bool) : WordExtractedForgerOf Message :=
  fun n spk => A n (encWordPair (spk, ck))

/-- Interpret a word-level extracted forger as a typed `ExtractedForger` by processing every
query as the `Payload` returned by the total decoder `payloadDecoderOf D`, rather than rejecting
malformed query words (`PartialDecoder`), matching the oracle view simulated inside
`targetForgerWordOf`. -/
def WordExtractedForgerOf.toTyped {Message : Type} {encM : Message ↪ List Bool}
    (D : Decoder encM) (A : WordExtractedForgerOf Message) (n : ℕ) :
    ExtractedForger (List Bool) Message (List Bool) (List Bool) := fun pk =>
  ProbOracleComp.simulate
    (fun req : Unit × List Bool => ProbOracleComp.query ((payloadDecoderOf D).decode req.2))
    (A n pk)

/-- Generic word-level target-forgery reduction corresponding to `targetForger`: runs `A` on
`encWordPair (spk, ck)`, decodes each payload query with `payloadDecoderOf D`, forwards
`target n ck payload.message payload.opening` to the signing oracle with reply truncation
`sigBound`, and outputs `(target n ck tok.payload.message tok.payload.opening, tok.signature)`. -/
def targetForgerWordOf {Message : Type} {encM : Message ↪ List Bool} (D : Decoder encM)
    (sigBound : ℕ → ℕ → ℕ)
    (target : ℕ → List Bool → Message → List Bool → List Bool)
    (A : WordExtractedForgerOf Message)
    (n : ℕ) (keys : List Bool × List Bool) : WordOracleComp Unit (List Bool × List Bool) := do
  let (spk, ck) := keys
  let tok ← OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request : Unit × List Bool =>
        let payload := (payloadDecoderOf D).decode request.2
        let msg := target n ck payload.message payload.opening
        List.take (sigBound n msg.length) <$> ProbOracleComp.query ((), msg)))
    (A n (encWordPair (spk, ck)))
  return (target n ck tok.payload.message tok.payload.opening, tok.signature)

private theorem computableInPolyTime_target_comp {α Message : Type} {encM : Message ↪ List Bool}
    {encIn : α ↪ List Bool} {target : ℕ → List Bool → Message → List Bool → List Bool}
    (htarget : ComputableInPolyTime
      (fun p : ℕ × List Bool × Message × List Bool => target p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encTargetArgsOf encM) encBits)
    {n : α → ℕ} {ck : α → List Bool} {pay : α → Payload Message (List Bool)}
    (hn : ComputableInPolyTime n encIn encUnary) (hck : ComputableInPolyTime ck encIn encBits)
    (hpay : ComputableInPolyTime pay encIn (encPayloadOf encM)) :
    ComputableInPolyTime (fun a => target (n a) (ck a) (pay a).message (pay a).opening)
      encIn encBits :=
  htarget.comp (hn.prod (hck.prod
    ((encPayloadOf_message_polyTime encM hpay).prod (encPayloadOf_opening_polyTime encM hpay))))

/-- `targetForgerWordOf` is uniform strict oracle PPT on `(n, (spk, ck))` whenever `A`,
`sigBound`, and `target` are polynomial-time. -/
theorem isOraclePPTOn_targetForgerWordOf {Message : Type} {encM : Message ↪ List Bool}
    (D : Decoder encM) {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {target : ℕ → List Bool → Message → List Bool → List Bool}
    (htarget : ComputableInPolyTime
      (fun p : ℕ × List Bool × Message × List Bool => target p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encTargetArgsOf encM) encBits)
    {A : WordExtractedForgerOf Message} (hA : IsOraclePPT (encTokenOf encM) A) :
    IsOraclePPTOn encPublicInput encWordPair
      (fun p => targetForgerWordOf D sigBound target A p.1 p.2) := by
  have hdec : ComputableInPolyTime (payloadDecoderOf D).decode encBits (encPayloadOf encM) :=
    (payloadDecoderOf D).computableInPolyTime
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.1, encWordPair p.2))
      encPublicInput (encPair encUnary encBits) := by
    unfold encPublicInput encWordPair
    fun_prop
  have hcaller := ComputableInPolyTime.fst encPublicInput (encPair (encFinEnum Unit) encBits)
  have hreq := computableInPolyTime_target_comp htarget hcaller.fst' hcaller.snd'.snd'
    (hdec.comp (ComputableInPolyTime.snd _ _).snd')
  have hlim := hsigBound.comp (hcaller.fst'.prod (ComputableInPolyTime.length_bits.comp hreq))
  -- The resource bound reads only the request word, so it factors through `callIn`.
  have hres : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        sigBound p.1.1 (target p.1.1 p.1.2.2 ((payloadDecoderOf D).decode p.2).message
          ((payloadDecoderOf D).decode p.2).opening).length)
      (encPair encPublicInput encBits) encUnary :=
    hlim.comp ((ComputableInPolyTime.fst _ _).prod
      ((ComputableInPolyTime.const ()).prod (ComputableInPolyTime.snd _ _)))
  have hinterp := hA.on.interpret_preprocess_open'
    (operationEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool × List Bool) (request : Unit × List Bool) =>
      let payload := (payloadDecoderOf D).decode request.2
      let msg := target p.1 p.2.2 payload.message payload.opening
      List.take (sigBound p.1 msg.length) <$> ProbOracleComp.query ((), msg))
    (resources := fun p w =>
      let payload := (payloadDecoderOf D).decode w
      sigBound p.1 (target p.1 p.2.2 payload.message payload.opening).length)
    hprep (IsOraclePPTOn.query_take () hreq hlim) hres fun p request reply hreply => by
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact List.length_take_le _ _
  have hfst := ComputableInPolyTime.fst encPublicInput (encTokenOf encM)
  have hsnd := ComputableInPolyTime.snd encPublicInput (encTokenOf encM)
  have hpost := (computableInPolyTime_target_comp htarget hfst.fst' hfst.snd'.snd'
    (encTokenOf_payload_polyTime encM hsnd)).prod (encTokenOf_signature_polyTime encM hsnd)
  simpa only [targetForgerWordOf, bind_pure_comp] using hinterp.map_with hpost

/-- Running a generic word-level forger with `sigBound`-truncation against
`SignatureScheme.signingOracleOf` along an encoding `tag : Target → List Bool` preserves the joint
law of `(output, targetLog)` against `targetForger` and `runState`. -/
private theorem eval_signingOracle_take_eq_targetForger_runLog_of
    {α Message Target : Type} {encM : Message ↪ List Bool} (D : Decoder encM)
    (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool)
    (target : Message → List Bool → Target) (tag : Target → List Bool)
    (sigBound : ℕ → ℕ)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (sign sk msg)).support →
      sig.length ≤ sigBound msg.length)
    (prog : WordOracleComp Unit α) (queried : List (List Bool))
    (log : List (Target × List Bool))
    (hlog : (log.map (fun e => tag e.1)).reverse = queried) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (SignatureScheme.signingOracleOf sign sk))
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
          (fun req : Unit × List Bool =>
            List.take (sigBound
                (tag (target ((payloadDecoderOf D).decode req.2).message
                  ((payloadDecoderOf D).decode req.2).opening)).length) <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
                ((), tag (target ((payloadDecoderOf D).decode req.2).message
                  ((payloadDecoderOf D).decode req.2).opening))))
        prog)).run queried) =
      (ProbComp.eval ((ProbOracleComp.simulate
        (fun payload => ProbOracleComp.query (target payload.message payload.opening))
        (ProbOracleComp.simulate
          (fun req : Unit × List Bool =>
            ProbOracleComp.query ((payloadDecoderOf D).decode req.2))
          prog)).runState
        (fun msg acc => (fun sig => (sig, acc ++ [(msg, sig)])) <$> sign sk (tag msg)) |>.run
          log)).map
        fun ⟨res, acc⟩ => (res, (acc.map (fun e => tag e.1)).reverse) := by
  subst hlog
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_interpret_sumHandler,
    ProbOracleComp.eval_runState, ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    ProbOracleComp.interpret_simulate]
  simp only [ProbOracleComp.interpret_query, ProbOracleComp.runWith_interpret_sumHandler]
  symm
  refine ProbOracleComp.runWith_map_state _ _ (fun acc => (acc.map (fun e => tag e.1)).reverse)
    (fun req acc => ?_) prog log
  simp only [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    SignatureScheme.signingOracleOf, SignatureScheme.signingOracleOn, ↓reduceIte,
    ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, pmf_norm, PMF.map,
    Function.comp_def]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
  simp [List.take_of_length_le (hbound _ sig hsig), List.map_append, List.reverse_append]

/-- Word-level target-forgery reduction corresponding to `targetForger`: specializes
`targetForgerWordOf Decoder.bits`. -/
def targetForgerWord (sigBound : ℕ → ℕ → ℕ)
    (target : ℕ → List Bool → List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool))
    (n : ℕ) (keys : List Bool × List Bool) : WordOracleComp Unit (List Bool × List Bool) :=
  targetForgerWordOf Decoder.bits sigBound target A n keys

/-- `targetForgerWord` is uniform strict oracle PPT on `(n, (spk, ck))` whenever `A`, `sigBound`,
and `target` are polynomial-time. -/
theorem isOraclePPTOn_targetForgerWord {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {target : ℕ → List Bool → List Bool → List Bool → List Bool}
    (htarget : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => target p.1 p.2.1 p.2.2.1 p.2.2.2)
      encTargetArgs encBits)
    {A : WordExtractedForgerOf (List Bool)} (hA : IsOraclePPT encWordToken A) :
    IsOraclePPTOn encPublicInput encWordPair
      (fun p => targetForgerWord sigBound target A p.1 p.2) :=
  isOraclePPTOn_targetForgerWordOf Decoder.bits hsigBound htarget hA

/-- At every security parameter `n` and public parameter `ck`, `targetForgerWord` matches the typed
`Basic.targetForger` reduction inside `EUFCMA`, provided `sigBound` bounds supported signature
lengths of `S`. -/
theorem eval_eufCmaGame_targetForgerWord_eq (S : WordSignatureScheme)
    (target : ℕ → List Bool → List Bool → List Bool → List Bool)
    (sigBound : ℕ → ℕ → ℕ)
    (hbound : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (S.keyGen n)).support →
      ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
        sig.length ≤ sigBound n msg.length)
    (A : WordExtractedForgerOf (List Bool)) (n : ℕ) (ck : List Bool) :
    ProbComp.eval (S.eufCmaGame (fun m spk => targetForgerWord sigBound target A m (spk, ck)) n) =
      ProbComp.eval ((S.toScheme n).eufCmaExperiment
        (targetForger (target n ck)
          (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n))) := by
  simp only [WordSignatureScheme.eufCmaGame, Signature.Scheme.eufCmaExperiment, forgeExperiment,
    WordSignatureScheme.toScheme_keyGen, WordSignatureScheme.toScheme_sign,
    WordSignatureScheme.toScheme_verify, ProbComp.eval_bind, ProbComp.eval_pure]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ hkeys => ?_
  dsimp only
  rw [funext fun l => funext (Signer.ofSign_apply S.sign sk l), ProbOracleComp.runLogWith_some]
  simp only [targetForgerWord, targetForgerWordOf, targetForger, WordExtractedForgerOf.toTyped,
    WordExtractedForgerOf.atKey, ProbOracleComp.runLog, bind_pure_comp, OracleComp.interpret_map,
    StateT.run_map, ProbComp.eval_map, ProbOracleComp.runState_map]
  change (PMF.map _ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (SignatureScheme.signingOracleOf S.sign sk)) _).run []))).bind _ = _
  rw [eval_signingOracle_take_eq_targetForger_runLog_of Decoder.bits S.sign sk
    (target n ck) (fun x => x) (sigBound n) (hbound n pk sk hkeys)
    (A n (encWordPair (pk, ck))) [] [] rfl]
  simp only [PMF.bind_map, Function.comp_def, freshMessage, List.contains_reverse]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨tok, log⟩ _ => ?_
  simp [Bool.and_comm]

/-! ### `bindingReductionWord` and asymptotic extracted-token security -/

/-- Word-level logged execution corresponding to `runExtracted`: generates `keys ← S.keyGen n`,
runs `A` on `encWordPair (keys.1, ck)` against `S.sign keys.2` after decoding each request with
`payloadDecoderOf D`, and records every semantic payload query and reply. -/
def runExtractedWord {Message : Type} {encM : Message ↪ List Bool}
    (S : WordSignatureScheme)
    (target : ℕ → List Bool → Message → List Bool → List Bool)
    (D : Decoder encM)
    (A : WordExtractedForgerOf Message)
    (n : ℕ) (ck : List Bool) :
    ProbComp (Execution (List Bool) Message (List Bool) (List Bool)) := do
  let keys ← S.keyGen n
  let (output, log) ←
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbComp.unifFin k))
        (fun (req : Unit × List Bool)
             (acc : List (Payload Message (List Bool) × List Bool)) =>
          let payload := (payloadDecoderOf D).decode req.2
          let msg := target n ck payload.message payload.opening
          (fun sig => (sig, acc ++ [(payload, sig)])) <$> S.sign keys.2 msg))
      (A n (encWordPair (keys.1, ck)))).run []
  return ⟨keys.1, output, log⟩

private theorem isPPTOn_runExtractedHandler {Message : Type} {encM : Message ↪ List Bool}
    (S : WordSignatureScheme)
    {target : ℕ → List Bool → Message → List Bool → List Bool}
    (htarget : ComputableInPolyTime
      (fun p : ℕ × List Bool × Message × List Bool => target p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encTargetArgsOf encM) encBits)
    (D : Decoder encM) :
    IsPPTOn (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
      (encPair encBits (encPayloadLogOf encM))
      (fun ⟨caller, req, acc⟩ =>
        let payload := (payloadDecoderOf D).decode req.2
        let msg := target caller.1.1 caller.1.2 payload.message payload.opening
        (fun sig => (sig, acc ++ [(payload, sig)])) <$> S.sign caller.2.2 msg) := by
  dsimp only
  have hcaller := ComputableInPolyTime.fst encExtractedCaller
    (encPair (encPair (encFinEnum Unit) encBits) (encPayloadLogOf encM))
  have hrest := ComputableInPolyTime.snd encExtractedCaller
    (encPair (encPair (encFinEnum Unit) encBits) (encPayloadLogOf encM))
  have hp := (payloadDecoderOf D).computableInPolyTime.comp hrest.fst'.snd'
  have hmsg := computableInPolyTime_target_comp htarget hcaller.fst'.fst' hcaller.fst'.snd' hp
  refine (S.isPPTOn_sign_comp hcaller.snd'.snd' hmsg).map_with
    (f := fun p sig => (sig, p.2.2 ++ [((payloadDecoderOf D).decode p.2.1.2, sig)])) ?_
  have hfst := ComputableInPolyTime.fst
    (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM)) encBits
  have hsig := ComputableInPolyTime.snd
    (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM)) encBits
  have hentry := (ComputableInPolyTime.cons (encPayloadLogEntryOf encM)).comp
    (((hp.comp hfst).prod hsig).prod (ComputableInPolyTime.const []))
  exact hsig.prod ((ComputableInPolyTime.listAppend (encPayloadLogEntryOf encM)).comp
    ((hrest.snd'.comp hfst).prod hentry))

/-- `runExtractedWord` is uniform strict PPT in `(n, ck)` whenever `target` and `A` are
efficient. -/
theorem isPPTOn_runExtractedWord {Message : Type} {encM : Message ↪ List Bool}
    (S : WordSignatureScheme)
    {target : ℕ → List Bool → Message → List Bool → List Bool}
    (htarget : ComputableInPolyTime
      (fun p : ℕ × List Bool × Message × List Bool => target p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encTargetArgsOf encM) encBits)
    (D : Decoder encM)
    {A : WordExtractedForgerOf Message} (hA : IsOraclePPT (encTokenOf encM) A) :
    IsPPTOn encParamInput (encExecutionOf encM)
      (fun p => runExtractedWord S target D A p.1 p.2) := by
  have hdec : ComputableInPolyTime (payloadDecoderOf D).decode encBits (encPayloadOf encM) :=
    (payloadDecoderOf D).computableInPolyTime
  have hprep : ComputableInPolyTime
      (fun c : (ℕ × List Bool) × (List Bool × List Bool) => (c.1.1, encWordPair (c.2.1, c.1.2)))
      encExtractedCaller encParamInput := by
    unfold encExtractedCaller encParamInput encWordPair
    fun_prop
  have hhandler := isPPTOn_runExtractedHandler S htarget D
  obtain ⟨dc, dd, hdecBound⟩ := hdec.polyBounded_length.exists_le
  obtain ⟨tc, td, htBound⟩ := htarget.polyBounded_length.exists_le
  obtain ⟨sc, sd, hsBound⟩ := S.sign_ppt.length_le
  let polyB (B : ℕ) : ℕ :=
    let decL := dc * (B + 1) ^ dd
    let msgL := tc * (4 * B + 2 * decL + 10) ^ td
    let sigL := sc * (2 * B + msgL + 2) ^ sd
    2 * (2 * decL + 2 * sigL + 4) + 2
  let growth (c : (ℕ × List Bool) × (List Bool × List Bool)) (w : List Bool) : ℕ :=
    polyB (encPair encExtractedCaller encBits (c, w)).length
  have hgrowth : PolyBounded
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        (encPair encExtractedCaller encBits p).length)
      (fun ⟨c, w⟩ => growth c w) :=
    PolyBounded.of_polynomiallyBounded_comp (p := polyB) (by
      dsimp only [polyB]
      fun_prop)
      (PolyBounded.self (size := fun p => (encPair encExtractedCaller encBits p).length))
  have hrun := hA.run_interpret_preprocess_of_bounded_growth
    (stateEncoding := encPayloadLogOf encM)
    (handler := fun caller req acc =>
      let payload := (payloadDecoderOf D).decode req.2
      let msg := target caller.1.1 caller.1.2 payload.message payload.opening
      (fun sig => (sig, acc ++ [(payload, sig)])) <$> S.sign caller.2.2 msg)
    hprep hhandler (ComputableInPolyTime.const []) (fun _ _ => True) (fun _ => trivial)
    hgrowth
    (fun caller req acc _ res hres => by
      simp only [ProbComp.eval_map, PMF.mem_support_map_iff] at hres
      obtain ⟨sig, hsig, rfl⟩ := hres
      refine ⟨trivial, ?_⟩
      let B := (encPair encExtractedCaller encBits (caller, req.2)).length
      obtain ⟨hB_w, hB_n, hB_ck, hB_sk⟩ :
          req.2.length ≤ B ∧ caller.1.1 ≤ B ∧ caller.1.2.length ≤ B ∧ caller.2.2.length ≤ B := by
        dsimp only [B, encExtractedCaller, encParamInput, encWordPair]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> enc_len
      let payload := (payloadDecoderOf D).decode req.2
      let msg := target caller.1.1 caller.1.2 payload.message payload.opening
      have hplen : (encPayloadOf encM payload).length ≤ dc * (B + 1) ^ dd :=
        le_trans (by simpa only [encBits_apply] using hdecBound req.2)
          (Nat.mul_le_mul_left dc (Nat.pow_le_pow_left (by omega) dd))
      have hmlen : msg.length ≤ tc * (4 * B + 2 * (dc * (B + 1) ^ dd) + 10) ^ td := by
        have hm := htBound (caller.1.1, caller.1.2, payload.message, payload.opening)
        have hpenc := congrArg List.length (encPayloadOf_apply encM payload)
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
          at hm hpenc
        exact hm.trans (Nat.mul_le_mul_left tc (Nat.pow_le_pow_left (by omega) td))
      have hslen : sig.length ≤
          sc * (2 * B + tc * (4 * B + 2 * (dc * (B + 1) ^ dd) + 10) ^ td + 2) ^ sd := by
        have hs := hsBound (caller.2.2, msg) sig hsig
        simp only [length_encPair, encBits_apply] at hs
        exact hs.trans (Nat.mul_le_mul_left sc (Nat.pow_le_pow_left (by omega) sd))
      change (encPayloadLogOf encM (acc ++ [(payload, sig)])).length ≤
        (encPayloadLogOf encM acc).length + growth caller req.2
      simp only [encPayloadLogOf, encList_append, encList_cons, encList_nil, List.length_append,
        List.length_nil, length_frame, encPayloadLogEntryOf, length_encPair, encBits_apply,
        growth, polyB, B] at hplen hslen ⊢
      omega)
  have hres' := ComputableInPolyTime.snd encExtractedCaller
    (encPair (encTokenOf encM) (encPayloadLogOf encM))
  have hpost := encExecutionOf_mk_polyTime encM
    (ComputableInPolyTime.fst encExtractedCaller _).snd'.fst' hres'.fst' hres'.snd'
  simpa only [runExtractedWord, bind_pure_comp] using
    (S.keyGen_ppt.preprocess (ComputableInPolyTime.fst encUnary encBits)).bind_with
      (hrun.map_with hpost)

/-- `runExtractedWord` agrees in `PMF` law with `Basic.runExtracted` on `S.toScheme n` and
`WordExtractedForgerOf.toTyped`. -/
theorem eval_runExtractedWord_eq {Message : Type} {encM : Message ↪ List Bool}
    (S : WordSignatureScheme)
    (target : ℕ → List Bool → Message → List Bool → List Bool)
    (D : Decoder encM) (A : WordExtractedForgerOf Message) (n : ℕ) (ck : List Bool) :
    ProbComp.eval (runExtractedWord S target D A n ck) =
      ProbComp.eval (runExtracted (S.toScheme n) (target n ck)
        (WordExtractedForgerOf.toTyped D (A.atKey ck) n)) := by
  simp only [runExtractedWord, runExtracted, WordSignatureScheme.toScheme_keyGen,
    WordSignatureScheme.toScheme_sign, ProbComp.eval_bind, ProbComp.eval_pure]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ _ => ?_
  simp only [WordExtractedForgerOf.toTyped, WordExtractedForgerOf.atKey, ProbOracleComp.runLog,
    ProbOracleComp.runState, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    ProbOracleComp.runWith_interpret_sumHandler]
  congr 2
  funext q state
  rw [ProbOracleComp.runWith_query]

/-- Finding a binding witness in a transcript runs in plain polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_findBindingWitness {Message : Type} {encM : Message ↪ List Bool}
    {target : ℕ → List Bool → Message → List Bool → List Bool}
    (htarget : ComputableInPolyTime
      (fun p : ℕ × List Bool × Message × List Bool => target p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encTargetArgsOf encM) encBits) :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × Payload Message (List Bool) ×
          List (Payload Message (List Bool) × List Bool) =>
        findBindingWitness (target p.1.1 p.1.2) p.2.1 p.2.2)
      (encPair encParamInput (encPair (encPayloadOf encM) (encPayloadLogOf encM)))
      (encOption (encBindingWitnessOf encM)) := by
  let E := encPair encParamInput (encPair (encPayloadOf encM) (encPayloadLogOf encM))
  have hp := ComputableInPolyTime.id' (encIn := encPair E (encPayloadLogEntryOf encM))
  have htest := ComputableInPolyTime.decide_eq'
    (computableInPolyTime_target_comp htarget hp.fst'.fst'.fst' hp.fst'.fst'.snd' hp.snd'.fst')
    (computableInPolyTime_target_comp htarget hp.fst'.fst'.fst' hp.fst'.fst'.snd'
      hp.fst'.snd'.fst')
  exact ComputableInPolyTime.optionMapWithInput
    (ComputableInPolyTime.findWithInput (ComputableInPolyTime.snd encParamInput _).snd' htest)
    (encBindingWitnessOf_mk_polyTime encM hp.fst'.snd'.fst' hp.snd'.fst')

/-- Word-level binding reduction corresponding to `Basic.bindingReduction`: executes
`runExtractedWord` and searches the transcript for a target collision with the output payload. -/
def bindingReductionWord {Message : Type} {encM : Message ↪ List Bool}
    (S : WordSignatureScheme)
    (target : ℕ → List Bool → Message → List Bool → List Bool)
    (D : Decoder encM) (A : WordExtractedForgerOf Message)
    (n : ℕ) (ck : List Bool) : ProbComp (Option (BindingWitness Message (List Bool))) :=
  (fun run => findBindingWitness (target n ck) run.output.payload run.log) <$>
    runExtractedWord S target D A n ck

/-- `bindingReductionWord` is uniform strict PPT in `(n, ck)`. -/
@[program_certificate]
theorem isPPTOn_bindingReductionWord {Message : Type} {encM : Message ↪ List Bool}
    (S : WordSignatureScheme)
    {target : ℕ → List Bool → Message → List Bool → List Bool}
    (htarget : ComputableInPolyTime
      (fun p : ℕ × List Bool × Message × List Bool => target p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encTargetArgsOf encM) encBits)
    (D : Decoder encM) {A : WordExtractedForgerOf Message} (hA : IsOraclePPT (encTokenOf encM) A) :
    IsPPTOn encParamInput (encOption (encBindingWitnessOf encM))
      (fun p => bindingReductionWord S target D A p.1 p.2) := by
  have hq := ComputableInPolyTime.snd encParamInput (encExecutionOf encM)
  have hpost := (computableInPolyTime_findBindingWitness htarget).comp
    ((ComputableInPolyTime.fst _ _).prod
      ((encTokenOf_payload_polyTime encM (encExecutionOf_output_polyTime encM hq)).prod
        (encExecutionOf_log_polyTime encM hq)))
  simpa only [bindingReductionWord] using
    (isPPTOn_runExtractedWord S htarget D hA).map_with hpost

/-- `bindingReductionWord` has the exact `PMF` law of `Basic.bindingReduction` on `S.toScheme n`
and `WordExtractedForgerOf.toTyped`. -/
theorem eval_bindingReductionWord_eq {Message : Type} {encM : Message ↪ List Bool}
    (S : WordSignatureScheme)
    (target : ℕ → List Bool → Message → List Bool → List Bool)
    (D : Decoder encM) (A : WordExtractedForgerOf Message) (n : ℕ) (ck : List Bool) :
    ProbComp.eval (bindingReductionWord S target D A n ck) =
      ProbComp.eval (bindingReduction (S.toScheme n) (target n ck)
        (WordExtractedForgerOf.toTyped D (A.atKey ck) n)) := by
  simp only [bindingReductionWord, bindingReduction, ProbComp.eval_map, eval_runExtractedWord_eq]

/-- Keyed word-level target function applying a collision-resistant hash `H` under key `ck` to
the framed payload `encWordPayload ⟨msg, opening⟩`. -/
def wordPayloadTarget (H : List Bool → List Bool → List Bool)
    (_ : ℕ) (ck msg opening : List Bool) : List Bool :=
  H ck (encWordPayload ⟨msg, opening⟩)

private theorem computableInPolyTime_wordPayloadTarget
    {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool =>
        wordPayloadTarget H p.1 p.2.1 p.2.2.1 p.2.2.2)
      encTargetArgs encBits := by
  have hargs : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool × List Bool => p.2)
      encTargetArgs encKeyedWordPair := ComputableInPolyTime.snd _ _
  exact hH.comp (hargs.fst'.prod
    ((ComputableInPolyTime.of_eq (f := encWordPayload) (encOut := encBits) fun _ => rfl).comp
      (encPayloadOf_mk_polyTime encBits hargs.snd'.fst' hargs.snd'.snd')))

private theorem isOraclePPT_sampleList_bind
    {B : ℕ → List Bool × List Bool → WordOracleComp Unit (List Bool × List Bool)}
    (hB : IsOraclePPTOn encPublicInput encWordPair (fun p => B p.1 p.2)) :
    IsOraclePPT (encPair encBits encBits) (fun n pk => do
      let ck ← ProbOracleComp.sample (BitString.sampleList n)
      B n (pk, ck)) := by
  have hprep : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List Bool => (q.1.1, (q.1.2, q.2)))
      (encPair (encPair encUnary encBits) encBits) encPublicInput := by
    dsimp only [encPublicInput, encWordPair]
    fun_prop
  exact (((isPPTOn_sampleList.preprocess
    (ComputableInPolyTime.fst encUnary encBits)).isOraclePPTOn).bind_with
      (hB.preprocess hprep)).isOraclePPT

private theorem eval_eufCmaGame_sampleList_bind_eq (S : WordSignatureScheme)
    (B : ℕ → List Bool × List Bool → WordOracleComp Unit (List Bool × List Bool)) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame (fun m pk => do
        let ck ← ProbOracleComp.sample (BitString.sampleList m)
        B m (pk, ck)) n) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
        ProbComp.eval (S.eufCmaGame (fun m spk => B m (spk, ck)) n) := by
  simp only [WordSignatureScheme.eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_sample_bind, PMF.bind_bind]
  exact PMF.bind_comm _ _ _

/-- Key-sampling EUF-CMA wrapper around `targetForgerWord` for `wordPayloadTarget H`. -/
noncomputable def sampledTargetForger (sigBound : ℕ → ℕ → ℕ)
    (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) : Forger :=
  fun n pk => do
    let ck ← ProbOracleComp.sample (BitString.sampleList n)
    targetForgerWord sigBound (wordPayloadTarget H) A n (pk, ck)

/-- `sampledTargetForger` is uniform strict oracle PPT whenever `sigBound`, `H`, and `A` are
efficient. -/
theorem isOraclePPT_sampledTargetForger {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {A : WordExtractedForgerOf (List Bool)} (hA : IsOraclePPT encWordToken A) :
    IsOraclePPT (encPair encBits encBits) (sampledTargetForger sigBound H A) :=
  isOraclePPT_sampleList_bind
    (isOraclePPTOn_targetForgerWord hsigBound (computableInPolyTime_wordPayloadTarget hH) hA)

private theorem eval_eufCmaGame_sampledTargetForger_eq (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ) (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame (sampledTargetForger sigBound H A) n) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
        ProbComp.eval (S.eufCmaGame
          (fun m spk => targetForgerWord sigBound (wordPayloadTarget H) A m (spk, ck)) n) :=
  eval_eufCmaGame_sampleList_bind_eq S _ n

/-- Collision finder extracted from `bindingReductionWord` by mapping `some w` to its two distinct
encoded payloads `(encWordPayload w.first, encWordPayload w.second)`. -/
def targetCollisionFinder (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) : CollisionFinder :=
  fun n ck =>
    (fun witness =>
      witness.elim ([], []) fun w => (encWordPayload w.first, encWordPayload w.second)) <$>
        bindingReductionWord S (wordPayloadTarget H) Decoder.bits A n ck

/-- `targetCollisionFinder` is uniform strict PPT whenever `H` and `A` are efficient. -/
@[program_certificate]
theorem isPPT_targetCollisionFinder (S : WordSignatureScheme)
    {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {A : WordExtractedForgerOf (List Bool)} (hA : IsOraclePPT encWordToken A) :
    IsPPT (encPair encBits encBits) (targetCollisionFinder S H A) := by
  have hbody : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × Option (BindingWitness (List Bool) (List Bool))) ×
          BindingWitness (List Bool) (List Bool) =>
        (encWordPayload q.2.first, encWordPayload q.2.second))
      (encPair (encPair encParamInput encOptionWordBindingWitness) encWordBindingWitness)
      (encPair encBits encBits) := by
    have hw := ComputableInPolyTime.snd (encPair encParamInput encOptionWordBindingWitness)
      encWordBindingWitness
    have henc : ComputableInPolyTime (fun p => encWordPayload p) encWordPayload encBits :=
      ComputableInPolyTime.of_eq (f := encWordPayload) (encOut := encBits) fun _ => rfl
    exact (henc.comp (encBindingWitnessOf_first_polyTime encBits hw)).prod
      (henc.comp (encBindingWitnessOf_second_polyTime encBits hw))
  exact ((isPPTOn_bindingReductionWord S (computableInPolyTime_wordPayloadTarget hH)
    Decoder.bits hA).map_with (ComputableInPolyTime.optionElimWithInput
      (ComputableInPolyTime.snd encParamInput encOptionWordBindingWitness)
      (ComputableInPolyTime.const ([], [])) hbody)).isPPT

private theorem bindingExperiment_le_collision (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) (n : ℕ) (ck : List Bool) :
    (ProbComp.eval (bindingExperiment (S.toScheme n) (wordPayloadTarget H n ck)
      (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n))) true ≤
      (ProbComp.eval (do
        let pair ← targetCollisionFinder S H A n ck
        return isCollision H (fun _ _ => true) n ck pair.1 pair.2)) true := by
  simp only [bindingExperiment, targetCollisionFinder, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, eval_bindingReductionWord_eq, PMF.bind_map, Function.comp_def]
  refine Cslib.Probability.PMF.map_true_mono _ fun w _ hw => ?_
  rcases w with _ | w
  · simp at hw
  · simp only [Option.any_some, checkBindingWitness, decide_eq_true_eq] at hw
    simp only [Option.elim_some, isCollision_eq_true_iff, ne_eq, true_and]
    exact ⟨fun heq => hw.1 (congrArg Payload.message (encWordPayload.injective heq)), hw.2⟩

private theorem negligible_sampleList_add_bound (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool)
    (game : ℕ → ProbComp Bool) (perKeyGame : ℕ → List Bool → ProbComp Bool)
    (forger : Forger) (perKeyForger : ℕ → List Bool → Forger)
    (collFinder : CollisionFinder)
    (hforgeNeg : Negligible
      (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame forger n))))
    (hcollNeg : Negligible
      (fun n =>
        Game.succProbability (ProbComp.eval (collisionGame H (fun _ _ => true) collFinder n))))
    (hgame : ∀ n, ProbComp.eval (game n) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck => ProbComp.eval (perKeyGame n ck))
    (hforge : ∀ n, ProbComp.eval (S.eufCmaGame forger n) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
        ProbComp.eval (S.eufCmaGame (perKeyForger n ck) n))
    (hpt : ∀ n ck,
      (ProbComp.eval (perKeyGame n ck)) true ≤
        (ProbComp.eval (S.eufCmaGame (perKeyForger n ck) n)) true +
          (ProbComp.eval (do
            let pair ← collFinder n ck
            return isCollision H (fun _ _ => true) n ck pair.1 pair.2)) true) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (game n))) := by
  refine negligible_of_le (hforgeNeg.add_fun hcollNeg) fun n => ?_
  have hbind : (ProbComp.eval (game n)) true ≤
      (ProbComp.eval (S.eufCmaGame forger n)) true +
        (ProbComp.eval (collisionGame H (fun _ _ => true) collFinder n)) true := by
    rw [hgame n, hforge n, collisionGame, ProbComp.eval_bind]
    exact Cslib.Probability.PMF.bind_apply_le_add_on_support _ true fun ck _ => hpt n ck
  simpa only [Game.succProbability, ENNReal.toNNReal_add (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)] using ENNReal.toNNReal_mono
      (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩) hbind

/-- Word-level extracted anonymous-token game: sample `ck ← BitString.sampleList n`, run
`runExtractedWord` with `wordPayloadTarget H`, and accept when `extractedAccept` holds. Every
bit-string oracle query from `A` is processed as the `Payload` returned by the total decoder
`payloadDecoderOf Decoder.bits` (`WordExtractedForgerOf.toTyped Decoder.bits`), rather than
rejecting malformed query words (`PartialDecoder`). -/
noncomputable def extractedTokenWordGame (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) (n : ℕ) : ProbComp Bool := do
  let ck ← BitString.sampleList n
  let run ← runExtractedWord S (wordPayloadTarget H) Decoder.bits A n ck
  return extractedAccept (S.toScheme n) (wordPayloadTarget H n ck) run

/-- `extractedTokenWordGame` has the exact `PMF` law of sampling `ck ← BitString.sampleList n`
and running `extractedExperiment` on `(A.atKey ck).toTyped Decoder.bits n`. -/
theorem eval_extractedTokenWordGame_eq (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) (n : ℕ) :
    ProbComp.eval (extractedTokenWordGame S H A n) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
        ProbComp.eval (extractedExperiment (S.toScheme n) (wordPayloadTarget H n ck)
          (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n)) := by
  simp only [extractedTokenWordGame, extractedExperiment, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, eval_runExtractedWord_eq]
  rfl

/-- Word-level unforgeability of extracted anonymous tokens: assuming only `S.EUFCMA`,
`CollisionResistant H`, and efficient `H` and `A` (with the signature length bound obtained
internally from `S.toSignatureScheme.exists_sign_length_bound`), any oracle-PPT adversary has
negligible winning probability in `extractedTokenWordGame`. -/
theorem negligible_extractedTokenWordGame (S : WordSignatureScheme) (hS : S.EUFCMA)
    (H : List Bool → List Bool → List Bool)
    (hHPoly : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hH : CollisionResistant H)
    (A : WordExtractedForgerOf (List Bool)) (hA : IsOraclePPT encWordToken A) :
    Negligible
      (fun n => Game.succProbability (ProbComp.eval (extractedTokenWordGame S H A n))) := by
  obtain ⟨sigBound, hsigPoly, hsigBound⟩ := S.toSignatureScheme.exists_sign_length_bound
  simp only [WordSignatureScheme.toSignatureScheme_keyGen,
    WordSignatureScheme.toSignatureScheme_sign] at hsigBound
  have hforgeNeg := hS.negligible (sampledTargetForger sigBound H A)
    (isOraclePPT_sampledTargetForger hsigPoly hHPoly hA)
  have hcollNeg := hH.negligible (targetCollisionFinder S H A)
    (isPPT_targetCollisionFinder S hHPoly hA)
  refine negligible_sampleList_add_bound S H
    (extractedTokenWordGame S H A)
    (fun n ck => extractedExperiment (S.toScheme n) (wordPayloadTarget H n ck)
      (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n))
    (sampledTargetForger sigBound H A)
    (fun _ ck m spk => targetForgerWord sigBound (wordPayloadTarget H) A m (spk, ck))
    (targetCollisionFinder S H A)
    hforgeNeg hcollNeg
    (eval_extractedTokenWordGame_eq S H A)
    (eval_eufCmaGame_sampledTargetForger_eq S sigBound H A) ?_
  intro n ck
  have hle_enn := ENNReal.coe_le_coe.mpr (extracted_succProbability_le (S.toScheme n)
    (wordPayloadTarget H n ck) (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n))
  simp only [Experiment.succProbability, Game.succProbability, ENNReal.coe_add,
    ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] at hle_enn
  rw [← eval_eufCmaGame_targetForgerWord_eq S (wordPayloadTarget H) sigBound
    (fun m pk sk hkeys msg sig hsig => hsigBound m (pk, sk) hkeys msg sig hsig) A n ck]
    at hle_enn
  exact hle_enn.trans (add_le_add le_rfl (bindingExperiment_le_collision S H A n ck))

/-! ### Extracted VOLE-ACT conservation: `noteForgerWord` -/

namespace Conservation

section ConservationEncodings

/-- Binary-credit encoding of semantic `Credit.Note`s with bit-string nullifiers and contexts. -/
enc_structure encCreditNote : Credit.Note (List Bool) (List Bool) where
  nullifier : encBits, context : encBits, credit : encNat, refund : encNat

attribute [fun_prop] encCreditNote_nullifier_polyTime encCreditNote_context_polyTime
  encCreditNote_credit_polyTime encCreditNote_refund_polyTime encCreditNote_mk_polyTime

/-- Encoding of extracted issuance requests with binary credit amount. -/
enc_structure encIssueRequest :
    IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) where
  ctx : encBits, amount : encNat, commitment : encBits, nullifier : encBits, opening : encBits

attribute [fun_prop] encIssueRequest_ctx_polyTime encIssueRequest_amount_polyTime
  encIssueRequest_commitment_polyTime encIssueRequest_nullifier_polyTime
  encIssueRequest_opening_polyTime encIssueRequest_mk_polyTime

/-- Encoding of extracted spend requests with binary credit, debit, and refund fields. -/
enc_structure encSpendRequest :
    SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) where
  ctx : encBits, nullifier : encBits, debit : encNat, refund : encNat,
  changeCommitment : encBits, oldCredit : encNat, oldOpening : encBits, oldRefund : encNat,
  signature : encBits, newNullifier : encBits, newCredit : encNat, newOpening : encBits

attribute [fun_prop] encSpendRequest_ctx_polyTime encSpendRequest_nullifier_polyTime
  encSpendRequest_debit_polyTime encSpendRequest_refund_polyTime
  encSpendRequest_changeCommitment_polyTime encSpendRequest_oldCredit_polyTime
  encSpendRequest_oldOpening_polyTime encSpendRequest_oldRefund_polyTime
  encSpendRequest_signature_polyTime encSpendRequest_newNullifier_polyTime
  encSpendRequest_newCredit_polyTime encSpendRequest_newOpening_polyTime
  encSpendRequest_mk_polyTime

end ConservationEncodings

/-- Equivalence between `Request` and the sum `IssueRequest ⊕ SpendRequest`. -/
def requestEquiv :
    Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) ≃
      IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) ⊕
        SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) where
  toFun
    | .issue req => .inl req
    | .spend req => .inr req
  invFun
    | .inl req => .issue req
    | .inr req => .spend req
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

/-- Sum encoding of `IssueRequest ⊕ SpendRequest`. -/
abbrev encRequestSum :
    IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) ⊕
      SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) ↪ List Bool :=
  encSum encIssueRequest encSpendRequest

/-- Tagged sum encoding of an extracted issuance/spend `Request`. -/
abbrev encWordRequest :
    Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) ↪ List Bool :=
  requestEquiv.toEmbedding.trans encRequestSum

/-- Encoding of a semantic note payload `(note, opening)`. -/
abbrev encNotePayload : Payload (Credit.Note (List Bool) (List Bool)) (List Bool) ↪ List Bool :=
  encPayloadOf encCreditNote

/-- Encoding of a semantic note token `(payload, signature)`. -/
abbrev encNoteToken :
    Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool) ↪ List Bool :=
  encTokenOf encCreditNote

/-- Encoding of a list of accepted `Request` records. -/
abbrev encRequestLog :
    List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ↪ List Bool :=
  encList encWordRequest

/-- Inputs `(nullifier, context, credit, opening)` supplied to note commitment functions. -/
structure ComInput where
  /-- Nullifier of the note being committed. -/
  nullifier : List Bool
  /-- Issuance context of the note being committed. -/
  context : List Bool
  /-- Credit balance committed in the note. -/
  credit : ℕ
  /-- Opening randomness of the commitment. -/
  opening : List Bool
  deriving DecidableEq

/-- Framed layout encoding of `ComInput`, keeping the nested layout
`encPair encBits (encPair encBits (encPair encNat encBits))`. -/
enc_structure encComInput : ComInput where
  nullifier : encBits, context : encBits, credit : encNat, opening : encBits

attribute [fun_prop] encComInput_nullifier_polyTime encComInput_context_polyTime
  encComInput_credit_polyTime encComInput_opening_polyTime encComInput_mk_polyTime

/-- Encoding of `((n, ck), comInput)` supplied to keyed note commitments. -/
abbrev encComArgs : ((ℕ × List Bool) × ComInput) ↪ List Bool :=
  encPair encParamInput encComInput

/-- Encoding of `(commitment, refund)` passed to commitment-refund taggers. -/
abbrev encTagPair : (List Bool × ℕ) ↪ List Bool :=
  encPair encBits encNat

/-- Encoding of a handler invocation `(caller, req, accepted)` in `noteForgerWord`. -/
abbrev encRequestCall :
    (ℕ × List Bool) × (Unit × List Bool) ×
      List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ↪ List Bool :=
  encHandlerCall encParamInput (encFinEnum Unit) encRequestLog

/-- Encoding of a handler result `(replyWord, accepted)` in `noteForgerWord`. -/
abbrev encRequestReply :
    (List Bool × List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))) ↪
      List Bool :=
  encPair encBits encRequestLog

/-- Total decoder for `encCreditNote`. -/
def creditNoteDecoder : Decoder encCreditNote :=
  (Decoder.pair Decoder.bits (Decoder.pair Decoder.bits (Decoder.pair Decoder.nat Decoder.nat))).map
    (fun (nf, ctx, cr, rf) => ⟨nf, ctx, cr, rf⟩)
    (fun n => (n.nullifier, n.context, n.credit, n.refund))
    (fun _ => rfl)
    (fun (nf, ctx, cr, rf) => (encCreditNote_apply ⟨nf, ctx, cr, rf⟩).symm)

/-- Total decoder for `encIssueRequest`. -/
def issueRequestDecoder : Decoder encIssueRequest :=
  (Decoder.pair Decoder.bits (Decoder.pair Decoder.nat
      (Decoder.pair Decoder.bits (Decoder.pair Decoder.bits Decoder.bits)))).map
    (fun (ctx, amt, c, nf, op) => ⟨ctx, amt, c, nf, op⟩)
    (fun r => (r.ctx, r.amount, r.commitment, r.nullifier, r.opening))
    (fun _ => rfl)
    (fun (ctx, amt, c, nf, op) => (encIssueRequest_apply ⟨ctx, amt, c, nf, op⟩).symm)

/-- Total decoder for `encSpendRequest`. -/
def spendRequestDecoder : Decoder encSpendRequest :=
  (Decoder.pair Decoder.bits (Decoder.pair Decoder.bits (Decoder.pair Decoder.nat
      (Decoder.pair Decoder.nat (Decoder.pair Decoder.bits (Decoder.pair Decoder.nat
        (Decoder.pair Decoder.bits (Decoder.pair Decoder.nat (Decoder.pair Decoder.bits
          (Decoder.pair Decoder.bits (Decoder.pair Decoder.nat Decoder.bits))))))))))).map
    (fun (ctx, nf, deb, ref, cc, oc, oo, oref, sig, nnf, nc, no) =>
      ⟨ctx, nf, deb, ref, cc, oc, oo, oref, sig, nnf, nc, no⟩)
    (fun s => (s.ctx, s.nullifier, s.debit, s.refund, s.changeCommitment, s.oldCredit,
      s.oldOpening, s.oldRefund, s.signature, s.newNullifier, s.newCredit, s.newOpening))
    (fun _ => rfl)
    (fun (ctx, nf, deb, ref, cc, oc, oo, oref, sig, nnf, nc, no) =>
      (encSpendRequest_apply ⟨ctx, nf, deb, ref, cc, oc, oo, oref, sig, nnf, nc, no⟩).symm)

/-- Total decoder for `encWordRequest`. -/
def wordRequestDecoder : Decoder encWordRequest :=
  (Decoder.sum issueRequestDecoder spendRequestDecoder).map
    requestEquiv.symm requestEquiv requestEquiv.left_inv
    (fun s => by cases s <;> rfl)

/-- Total decoder for `encNotePayload`. -/
abbrev notePayloadDecoder : Decoder encNotePayload :=
  payloadDecoderOf creditNoteDecoder

/-- Canonical injective word tag pairing a commitment word and binary refund natural number. -/
def wordTag (c : List Bool) (x : ℕ) : List Bool :=
  encTagPair (c, x)

/-- `wordTag` is injective as a function of `(commitment, refund)`. -/
theorem wordTag_injective : Function.Injective (fun p : List Bool × ℕ => wordTag p.1 p.2) :=
  encTagPair.injective

/-- `wordTag` is computable in polynomial time under `encTagPair`. -/
theorem computableInPolyTime_wordTag :
    ComputableInPolyTime (fun p : List Bool × ℕ => wordTag p.1 p.2) encTagPair encBits :=
  ComputableInPolyTime.of_eq (f := encTagPair) (encOut := encBits) fun _ => rfl

/-- Lift a `WordSignatureScheme` at security parameter `n` via `tag` to a typed scheme signing
`(commitment, refund)` pairs. -/
def pairScheme (S : WordSignatureScheme) (tag : List Bool → ℕ → List Bool) (n : ℕ) :
    Signature.Scheme (List Bool) (List Bool) (List Bool × ℕ) (List Bool) where
  keyGen := S.keyGen n
  sign sk p := S.sign sk (tag p.1 p.2)
  verify pk p sig := S.verify pk (tag p.1 p.2) sig

/-- A word-level extracted VOLE-ACT adversary querying encoded `Request`s for encoded `Option Sig`
replies and outputting a context `ctx : List Bool`. -/
abbrev WordExtractedAdversary := ℕ → List Bool → WordOracleComp Unit (List Bool)

/-- Interpret a word-level conservation adversary as a typed `ExtractedAdversary` at `(n, ck)`
by processing every word query as the `Request` returned by the total decoder `wordRequestDecoder`,
rather than rejecting malformed query words (`PartialDecoder`), matching the oracle view simulated
inside `noteForgerHandlerWord`. -/
def WordExtractedAdversary.toTyped (A : WordExtractedAdversary) (n : ℕ) (ck : List Bool) :
    ExtractedAdversary (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) :=
  fun spk =>
    ProbOracleComp.simulate
      (fun req : Unit × List Bool =>
        encOption encBits <$> ProbOracleComp.query (wordRequestDecoder.decode req.2))
      (A n (encWordPair (spk, ck)))

private theorem computableInPolyTime_requestOutputPayload :
    ComputableInPolyTime
      (Request.outputPayload :
        Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) →
          Payload (Credit.Note (List Bool) (List Bool)) (List Bool))
      encWordRequest encNotePayload := by
  have heq : ComputableInPolyTime requestEquiv encWordRequest encRequestSum :=
    ComputableInPolyTime.of_eq (f := requestEquiv) (encOut := encRequestSum) fun _ => rfl
  have his : ComputableInPolyTime
      (fun r : IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
        (⟨⟨r.nullifier, r.ctx, r.amount, 0⟩, r.opening⟩ :
          Payload (Credit.Note (List Bool) (List Bool)) (List Bool)))
      encIssueRequest encNotePayload := by fun_prop
  have hsp : ComputableInPolyTime
      (fun s : SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        (⟨⟨s.newNullifier, s.ctx, s.newCredit, s.refund⟩, s.newOpening⟩ :
          Payload (Credit.Note (List Bool) (List Bool)) (List Bool)))
      encSpendRequest encNotePayload := by
    fun_prop
  exact ((ComputableInPolyTime.sumElim his hsp).comp heq).of_enc_eq fun r => by cases r <;> rfl

private theorem computableInPolyTime_requestElim {γ δ : Type}
    {encG : γ ↪ List Bool} {encD : δ ↪ List Bool}
    {req : γ → Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)}
    {f : γ → δ}
    (onIssue : γ → IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) → δ)
    (onSpend : γ → SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) → δ)
    (hreq : ComputableInPolyTime req encG encWordRequest)
    (hi : ComputableInPolyTime
      (fun p : γ × IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
        onIssue p.1 p.2)
      (encPair encG encIssueRequest) encD)
    (hs : ComputableInPolyTime
      (fun p : γ × SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        onSpend p.1 p.2)
      (encPair encG encSpendRequest) encD)
    (hf : ∀ g, f g = (requestEquiv (req g)).elim (onIssue g) (onSpend g)) :
    ComputableInPolyTime f encG encD := by
  have heq : ComputableInPolyTime (fun g => requestEquiv (req g)) encG encRequestSum :=
    (ComputableInPolyTime.of_eq (f := requestEquiv) (encOut := encRequestSum) fun _ => rfl).comp
      hreq
  exact (ComputableInPolyTime.sumElimWithInput heq hi hs).of_enc_eq fun g =>
    congrArg encD (hf g)

private theorem computableInPolyTime_acceptLocal
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits)
    (tag : List Bool → ℕ → List Bool)
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits)
    (S : WordSignatureScheme) :
    ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) ×
          Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        acceptLocal (com p.1.1.1 p.1.1.2) Prod.mk (pairScheme S tag p.1.1.1) p.1.2 p.2)
      (encPair (encPair encParamInput encBits) encWordRequest) encBool := by
  let PIn := ((ℕ × List Bool) × List Bool)
  let encP := encPair encParamInput encBits
  have his : ComputableInPolyTime
      (fun q : (PIn × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
        decide (com q.1.1.1.1 q.1.1.1.2 q.2.nullifier q.2.ctx q.2.amount q.2.opening =
          q.2.commitment))
      (encPair (encPair encP encWordRequest) encIssueRequest) encBool := by
    have hq1 := (ComputableInPolyTime.fst (encPair encP encWordRequest) encIssueRequest).fst'.fst'
    have hq2 := ComputableInPolyTime.snd (encPair encP encWordRequest) encIssueRequest
    have hc := hcom.comp (hq1.prod (encComInput_mk_polyTime
      (encIssueRequest_nullifier_polyTime hq2) (encIssueRequest_ctx_polyTime hq2)
      (encIssueRequest_amount_polyTime hq2) (encIssueRequest_opening_polyTime hq2)))
    exact ComputableInPolyTime.decide_eq' hc (encIssueRequest_commitment_polyTime hq2)
  have hsp : ComputableInPolyTime
      (fun q : (PIn × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        S.verify q.1.1.2
            (tag (com q.1.1.1.1 q.1.1.1.2 q.2.nullifier q.2.ctx q.2.oldCredit q.2.oldOpening)
              q.2.oldRefund)
            q.2.signature &&
          decide (com q.1.1.1.1 q.1.1.1.2 q.2.newNullifier q.2.ctx q.2.newCredit q.2.newOpening =
            q.2.changeCommitment) &&
          decide (q.2.oldCredit + q.2.oldRefund = q.2.newCredit + q.2.debit))
      (encPair (encPair encP encWordRequest) encSpendRequest) encBool := by
    have hq := (ComputableInPolyTime.fst (encPair encP encWordRequest) encSpendRequest).fst'
    have hq1 := hq.fst'
    have hq2 := ComputableInPolyTime.snd (encPair encP encWordRequest) encSpendRequest
    have hcom1 := hcom.comp (hq1.prod (encComInput_mk_polyTime
      (encSpendRequest_nullifier_polyTime hq2) (encSpendRequest_ctx_polyTime hq2)
      (encSpendRequest_oldCredit_polyTime hq2) (encSpendRequest_oldOpening_polyTime hq2)))
    have ht1 := htag.comp (hcom1.prod (encSpendRequest_oldRefund_polyTime hq2))
    have hv := S.computableInPolyTime_verify_comp hq.snd' ht1
      (encSpendRequest_signature_polyTime hq2)
    have hcom2 := hcom.comp (hq1.prod (encComInput_mk_polyTime
      (encSpendRequest_newNullifier_polyTime hq2) (encSpendRequest_ctx_polyTime hq2)
      (encSpendRequest_newCredit_polyTime hq2) (encSpendRequest_newOpening_polyTime hq2)))
    have hc2 := ComputableInPolyTime.decide_eq' hcom2
      (encSpendRequest_changeCommitment_polyTime hq2)
    have hadd1 := ComputableInPolyTime.binary_add'
      (encSpendRequest_oldCredit_polyTime hq2) (encSpendRequest_oldRefund_polyTime hq2)
    have hadd2 := ComputableInPolyTime.binary_add'
      (encSpendRequest_newCredit_polyTime hq2) (encSpendRequest_debit_polyTime hq2)
    have hbal := ComputableInPolyTime.decide_eq' hadd1 hadd2
    exact ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.bool_and.comp (hv.prod hc2)).prod hbal)
  dsimp only [encP] at his hsp
  exact computableInPolyTime_requestElim
    (fun q i => decide (com q.1.1.1 q.1.1.2 i.nullifier i.ctx i.amount i.opening = i.commitment))
    (fun q s =>
      S.verify q.1.2 (tag (com q.1.1.1 q.1.1.2 s.nullifier s.ctx s.oldCredit s.oldOpening)
          s.oldRefund) s.signature &&
        decide (com q.1.1.1 q.1.1.2 s.newNullifier s.ctx s.newCredit s.newOpening =
          s.changeCommitment) &&
        decide (s.oldCredit + s.oldRefund = s.newCredit + s.debit))
    (ComputableInPolyTime.snd _ _) his hsp fun p => by
      cases p.2 <;>
        simp [acceptLocal, Credit.target, SpendRequest.inputNote, pairScheme, requestEquiv]

private theorem computableInPolyTime_hasSpentNullifier :
    ComputableInPolyTime
      (fun p : List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          (List Bool × List Bool) =>
        hasSpentNullifier p.1 p.2.1 p.2.2)
      (encPair encRequestLog encWordPair) encBool := by
  let ETy := List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
    (List Bool × List Bool)
  have hlist : ComputableInPolyTime (fun p : ETy => p.1)
      (encPair encRequestLog encWordPair) encRequestLog := ComputableInPolyTime.fst _ _
  let encQ := encPair (encPair encRequestLog encWordPair) encWordRequest
  have hr : ComputableInPolyTime
      (fun q : (ETy × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        decide (q.2.ctx = q.1.1.2.1 ∧ q.2.nullifier = q.1.1.2.2))
      (encPair encQ encSpendRequest) encBool := by
    have hq := ComputableInPolyTime.snd encQ encSpendRequest
    have hpair := (ComputableInPolyTime.fst encQ encSpendRequest).fst'.snd'
    have hctx := ComputableInPolyTime.decide_eq' (encSpendRequest_ctx_polyTime hq) hpair.fst'
    have hnf := ComputableInPolyTime.decide_eq' (encSpendRequest_nullifier_polyTime hq) hpair.snd'
    exact (ComputableInPolyTime.bool_and.comp (hctx.prod hnf)).of_enc_eq
      fun q => congrArg encBool (Bool.decide_and _ _)
  let testNull : ETy → Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) → Bool :=
    fun q r => match r with
      | .issue _ => false
      | .spend s => decide (s.ctx = q.2.1 ∧ s.nullifier = q.2.2)
  have htest : ComputableInPolyTime (fun q : ETy × _ => testNull q.1 q.2)
      (encPair (encPair encRequestLog encWordPair) encWordRequest) encBool :=
    computableInPolyTime_requestElim
      (fun _ _ => false)
      (fun q s => decide (s.ctx = q.1.2.1 ∧ s.nullifier = q.1.2.2))
      (ComputableInPolyTime.snd (encPair encRequestLog encWordPair) encWordRequest)
      (ComputableInPolyTime.const false) hr
      fun q => by cases q.2 <;> rfl
  exact (ComputableInPolyTime.anyWithInput (encA := encWordRequest) hlist htest).of_enc_eq
    fun ⟨reqs, _⟩ => congrArg (fun f => encBool (reqs.any f)) (funext fun r => by cases r <;> rfl)

private theorem computableInPolyTime_acceptRequest
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits)
    (tag : List Bool → ℕ → List Bool)
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits)
    (S : WordSignatureScheme) :
    ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List Bool) ×
          List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        acceptRequest (com p.1.1.1 p.1.1.2) Prod.mk (pairScheme S tag p.1.1.1) p.1.2 p.2.1 p.2.2)
      (encPair (encPair encParamInput encBits) (encPair encRequestLog encWordRequest)) encBool := by
  let ETy := ((ℕ × List Bool) × List Bool) ×
    List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
    Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)
  let encE := encPair (encPair encParamInput encBits) (encPair encRequestLog encWordRequest)
  have hparam : ComputableInPolyTime (fun p : ETy => p.1) encE (encPair encParamInput encBits) :=
    ComputableInPolyTime.fst _ _
  have hlog : ComputableInPolyTime (fun p : ETy => p.2.1) encE encRequestLog :=
    (ComputableInPolyTime.snd _ _).fst'
  have hreq : ComputableInPolyTime (fun p : ETy => p.2.2) encE encWordRequest :=
    (ComputableInPolyTime.snd _ _).snd'
  have hsymm : ComputableInPolyTime requestEquiv.symm encRequestSum encWordRequest :=
    ComputableInPolyTime.of_eq (f := requestEquiv.symm) (encOut := encWordRequest)
      fun s => by cases s <;> rfl
  have hl : ComputableInPolyTime
      (fun q : ETy × IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
        acceptLocal (com q.1.1.1.1 q.1.1.1.2) Prod.mk (pairScheme S tag q.1.1.1.1) q.1.1.2
          (.issue q.2))
      (encPair encE encIssueRequest) encBool :=
    (computableInPolyTime_acceptLocal com hcom tag htag S).comp
      ((hparam.comp (ComputableInPolyTime.fst _ _)).prod (hsymm.comp
        ((ComputableInPolyTime.sumInl encIssueRequest encSpendRequest).comp
          (ComputableInPolyTime.snd _ _))))
  have hr : ComputableInPolyTime
      (fun q : ETy × SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        acceptLocal (com q.1.1.1.1 q.1.1.1.2) Prod.mk (pairScheme S tag q.1.1.1.1) q.1.1.2
          (.spend q.2) &&
          !hasSpentNullifier q.1.2.1 q.2.ctx q.2.nullifier)
      (encPair encE encSpendRequest) encBool := by
    have hl' := (computableInPolyTime_acceptLocal com hcom tag htag S).comp
      ((hparam.comp (ComputableInPolyTime.fst _ _)).prod (hsymm.comp
        ((ComputableInPolyTime.sumInr encIssueRequest encSpendRequest).comp
          (ComputableInPolyTime.snd _ _))))
    have hs := computableInPolyTime_hasSpentNullifier.comp
      ((hlog.comp (ComputableInPolyTime.fst _ _)).prod
        ((encSpendRequest_ctx_polyTime (ComputableInPolyTime.snd _ _)).prod
          (encSpendRequest_nullifier_polyTime (ComputableInPolyTime.snd _ _))))
    exact ComputableInPolyTime.bool_and.comp (hl'.prod (ComputableInPolyTime.bool_not.comp hs))
  dsimp only [encE] at hl hr
  exact computableInPolyTime_requestElim _ _ hreq hl hr fun p => by cases p.2.2 <;> rfl

private theorem findNoteForgery_eq_find
    (reqs : List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)))
    (certified : List (Credit.Note (List Bool) (List Bool))) :
    ((spends reqs).findSome? fun s =>
        if s.inputNote ∈ certified then none
        else some (⟨s.inputPayload, s.signature⟩ :
          Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool))) =
      ((reqs.find? fun
          | .issue _ => false
          | .spend s => !decide (s.inputNote ∈ certified)).elim none fun
          | .issue _ => none
          | .spend s => some (⟨s.inputPayload, s.signature⟩ :
              Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool))) := by
  induction reqs with
  | nil => rfl
  | cons r rest ih =>
    cases r with
    | issue ir =>
      simpa [spends] using ih
    | spend sr =>
      by_cases h : sr.inputNote ∈ certified
      · simpa [spends, h] using ih
      · simp [spends, h]

private theorem computableInPolyTime_findNoteForgery :
    ComputableInPolyTime
      (findNoteForgery :
        List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) →
          Option (Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool)))
      encRequestLog (encOption encNoteToken) := by
  have hcert : ComputableInPolyTime
      (fun reqs : List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) =>
        reqs.map fun r => r.outputPayload.message)
      encRequestLog (encList encCreditNote) := by
    have hf := encPayloadOf_message_polyTime encCreditNote
      (computableInPolyTime_requestOutputPayload.comp (ComputableInPolyTime.snd encBool _))
    exact ComputableInPolyTime.mapWith hf (ComputableInPolyTime.const true)
      ComputableInPolyTime.id'
  have hq2 := ComputableInPolyTime.snd (encPair encRequestLog encWordRequest) encSpendRequest
  have hnote : ComputableInPolyTime
      (fun q : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        q.2.inputNote)
      (encPair (encPair encRequestLog encWordRequest) encSpendRequest) encCreditNote := by
    dsimp only [SpendRequest.inputNote]
    fun_prop
  have hc := hcert.comp
    (ComputableInPolyTime.fst (encPair encRequestLog encWordRequest) encSpendRequest).fst'
  have hmem := ComputableInPolyTime.decide_mem hc hnote
  let testForged :
      List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) →
      Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) → Bool :=
    fun reqs r => match r with
      | .issue _ => false
      | .spend s => !decide (s.inputNote ∈ reqs.map fun x => x.outputPayload.message)
  have htest : ComputableInPolyTime (fun p : _ × _ => testForged p.1 p.2)
      (encPair encRequestLog encWordRequest) encBool :=
    computableInPolyTime_requestElim
      (fun _ _ => false)
      (fun p s => !decide (s.inputNote ∈ p.1.map fun r => r.outputPayload.message))
      (ComputableInPolyTime.snd encRequestLog encWordRequest) (ComputableInPolyTime.const false)
      (by exact ComputableInPolyTime.bool_not.comp hmem)
      fun p => by cases p.2 <;> rfl
  have hfind := ComputableInPolyTime.findWithInput
    (encA := encWordRequest) (ComputableInPolyTime.id' (encIn := encRequestLog)) htest
  let bodyForged :
      List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) →
      Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) →
      Option (Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool)) :=
    fun _ r => match r with
      | .issue _ => none
      | .spend s => some (⟨s.inputPayload, s.signature⟩ :
          Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool))
  have hbody : ComputableInPolyTime (fun q : _ × _ => bodyForged q.1 q.2)
      (encPair encRequestLog encWordRequest) (encOption encNoteToken) :=
    computableInPolyTime_requestElim
      (fun _ _ =>
        (none : Option (Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool))))
      (fun _ s => some (⟨s.inputPayload, s.signature⟩ :
        Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool)))
      (ComputableInPolyTime.snd encRequestLog encWordRequest) (ComputableInPolyTime.const none)
      ((ComputableInPolyTime.optionSome encNoteToken).comp (encTokenOf_mk_polyTime encCreditNote
        (encPayloadOf_mk_polyTime encCreditNote hnote (encSpendRequest_oldOpening_polyTime hq2))
        (encSpendRequest_signature_polyTime hq2)))
      fun q => by cases q.2 <;> rfl
  exact (ComputableInPolyTime.optionElimWithInput (body := bodyForged) hfind
    (ComputableInPolyTime.const none) hbody).of_enc_eq fun reqs =>
      congrArg (encOption encNoteToken) (findNoteForgery_eq_find reqs _)

/-- Stateful handler used by `noteForgerWord`: decodes each `Request`, checks `acceptRequest`
against `pairScheme S tag`, queries the external note signing oracle with `sigBound`-truncation on
accepted requests, and records accepted requests. -/
def noteForgerHandlerWord (sigBound : ℕ → ℕ → ℕ)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool) (S : WordSignatureScheme)
    (n : ℕ) (keys : List Bool)
    (req : Unit × List Bool)
    (accepted : List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))) :
    WordOracleComp Unit
      (List Bool ×
        List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))) :=
  let (spk, ck) := wordPairDecoder.decode keys
  let decReq := wordRequestDecoder.decode req.2
  if acceptRequest (com n ck) Prod.mk (pairScheme S tag n) spk accepted decReq then do
    let out := decReq.outputPayload
    let tgt := tag (com n ck out.message.nullifier out.message.context
      out.message.credit out.opening) out.message.refund
    let sig ← List.take (sigBound n tgt.length) <$> ProbOracleComp.query ((), encNotePayload out)
    return (encOption encBits (some sig), accepted ++ [decReq])
  else
    return (encOption encBits none, accepted)

private theorem isOraclePPTOn_noteForgerHandlerWord (sigBound : ℕ → ℕ → ℕ)
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits)
    (tag : List Bool → ℕ → List Bool)
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits)
    (S : WordSignatureScheme) :
    IsOraclePPTOn encRequestCall encRequestReply
      (fun ⟨caller, req, accepted⟩ =>
        noteForgerHandlerWord sigBound com tag S caller.1 caller.2 req accepted) := by
  dsimp only [noteForgerHandlerWord]
  let CallTy := (ℕ × List Bool) × (Unit × List Bool) ×
    List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))
  have hfst := ComputableInPolyTime.fst encParamInput
    (encPair (encPair (encFinEnum Unit) encBits) encRequestLog)
  have hsnd := ComputableInPolyTime.snd encParamInput
    (encPair (encPair (encFinEnum Unit) encBits) encRequestLog)
  have hn := hfst.fst'
  have hkeys := wordPairDecoder.computableInPolyTime.comp hfst.snd'
  have hparam := hn.prod hkeys.snd'
  have hdecReq := wordRequestDecoder.computableInPolyTime.comp hsnd.fst'.snd'
  have hacc := hsnd.snd'
  have hcond := (computableInPolyTime_acceptRequest com hcom tag htag S).comp
    ((hparam.prod hkeys.fst').prod (hacc.prod hdecReq))
  have hout := computableInPolyTime_requestOutputPayload.comp hdecReq
  have hreq :=
    (ComputableInPolyTime.of_eq (f := encNotePayload) (encOut := encBits) fun _ => rfl).comp hout
  have hnote := encPayloadOf_message_polyTime encCreditNote hout
  have htgt := htag.comp ((hcom.comp (hparam.prod (encComInput_mk_polyTime
    (encCreditNote_nullifier_polyTime hnote) (encCreditNote_context_polyTime hnote)
    (encCreditNote_credit_polyTime hnote) (encPayloadOf_opening_polyTime encCreditNote hout)))).prod
    (encCreditNote_refund_polyTime hnote))
  have hlim := hsigBound.comp (hn.prod (ComputableInPolyTime.length_bits.comp htgt))
  have hpost : ComputableInPolyTime
      (fun q : CallTy × List Bool =>
        (encOption encBits (some q.2), q.1.2.2 ++ [wordRequestDecoder.decode q.1.2.1.2]))
      (encPair encRequestCall encBits) encRequestReply := by
    have hq1 := ComputableInPolyTime.fst encRequestCall encBits
    have hsig := ComputableInPolyTime.snd encRequestCall encBits
    have hopt : ComputableInPolyTime (fun q : CallTy × List Bool => encOption encBits (some q.2))
        (encPair encRequestCall encBits) encBits :=
      (ComputableInPolyTime.of_eq (f := encOption encBits) (encOut := encBits) fun _ => rfl).comp
        ((ComputableInPolyTime.optionSome encBits).comp hsig)
    have hentry := (ComputableInPolyTime.cons encWordRequest).comp
      ((hdecReq.comp hq1).prod (ComputableInPolyTime.const []))
    exact hopt.prod ((ComputableInPolyTime.listAppend encWordRequest).comp
      ((hacc.comp hq1).prod hentry))
  simpa only [bind_pure_comp, Function.comp_def] using
    IsOraclePPTOn.cond hcond ((IsOraclePPTOn.query_take () hreq hlim).map_with hpost)
      ((ComputableInPolyTime.const (encOption encBits none)).prod hacc).isOraclePPTOn

/-- Execution phase of `noteForgerWord`, running `A n keys` under `noteForgerHandlerWord`. -/
def noteForgerRun (sigBound : ℕ → ℕ → ℕ)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool) (S : WordSignatureScheme)
    (A : WordExtractedAdversary) (n : ℕ) (keys : List Bool) :
    WordOracleComp Unit
      (List Bool ×
        List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool))) :=
  (OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (noteForgerHandlerWord sigBound com tag S n keys))
    (A n keys)).run []

/-- Word-level semantic note-forgery reduction corresponding to `Conservation.noteForger`: runs
`A` against `noteForgerHandlerWord` and extracts the first uncertified spend note via
`findNoteForgery`. -/
def noteForgerWord (sigBound : ℕ → ℕ → ℕ)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool) (S : WordSignatureScheme)
    (A : WordExtractedAdversary) :
    WordExtractedForgerOf (Credit.Note (List Bool) (List Bool)) :=
  fun n keys =>
    (fun st : List Bool ×
        List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) =>
      (findNoteForgery st.2).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩) <$>
      noteForgerRun sigBound com tag S A n keys

private theorem mem_support_noteForgerHandlerWord_length_le
    {sigBound : ℕ → ℕ → ℕ}
    {com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool}
    {tag : List Bool → ℕ → List Bool} {S : WordSignatureScheme}
    {dc dd : ℕ}
    (hdecBound : ∀ w : List Bool, (encWordRequest (wordRequestDecoder.decode w)).length ≤
      dc * (w.length + 1) ^ dd)
    (caller : ℕ × List Bool) (req : Unit × List Bool)
    (accepted : List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)))
    (res : List Bool ×
      List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)))
    (hres : res ∈
      (noteForgerHandlerWord sigBound com tag S caller.1 caller.2 req accepted).support) :
    (encRequestLog res.2).length ≤
      (encRequestLog accepted).length +
        (2 * (dc * ((encPair encParamInput encBits (caller, req.2)).length + 1) ^ dd) + 2) := by
  dsimp only [noteForgerHandlerWord] at hres
  split_ifs at hres with hcond
  · simp only [OracleComp.supportWith_bind, Set.mem_iUnion, exists_prop] at hres
    obtain ⟨sig, -, rfl⟩ := by
      simpa only [OracleComp.supportWith_map, Set.mem_image, OracleComp.supportWith_pure,
        Set.mem_singleton_iff, exists_eq_right] using hres
    have hBw : req.2.length ≤ (encPair encParamInput encBits (caller, req.2)).length := by
      enc_len
    have hd' := (hdecBound req.2).trans
      (Nat.mul_le_mul_left dc (Nat.pow_le_pow_left (Nat.add_le_add_right hBw 1) dd))
    simp only [encRequestLog, encList_append, encList_cons, encList_nil, List.length_append,
      List.length_nil, length_frame]
    omega
  · simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff] at hres
    subst hres
    exact Nat.le_add_right _ _

private theorem isOraclePPTOn_noteForgerRun {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool}
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits)
    {tag : List Bool → ℕ → List Bool}
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits)
    (S : WordSignatureScheme)
    {A : WordExtractedAdversary} (hA : IsOraclePPT encBits A) :
    IsOraclePPTOn encParamInput (encPair encBits encRequestLog)
      (fun p => noteForgerRun sigBound com tag S A p.1 p.2) := by
  have hhandler := isOraclePPTOn_noteForgerHandlerWord sigBound hsigBound com hcom tag htag S
  have hdec := wordRequestDecoder.computableInPolyTime
  obtain ⟨dc, dd, hdecBound⟩ := hdec.polyBounded_length.exists_le
  have hdecBound' (w : List Bool) : (encWordRequest (wordRequestDecoder.decode w)).length ≤
      dc * (w.length + 1) ^ dd := by
    simpa only [encBits_apply] using hdecBound w
  have hgrowth : PolyBounded
      (fun pair : (ℕ × List Bool) × List Bool => (encPair encParamInput encBits pair).length)
      (fun ⟨c, w⟩ => 2 * (dc * ((encPair encParamInput encBits (c, w)).length + 1) ^ dd) + 2) :=
    PolyBounded.of_polynomiallyBounded_comp
      (p := fun B : ℕ => 2 * (dc * (B + 1) ^ dd) + 2) (by fun_prop)
      (PolyBounded.self (size := fun pair => (encPair encParamInput encBits pair).length))
  dsimp only [noteForgerRun]
  refine hA.run_interpret_preprocess_open_of_bounded_growth
    (input := encParamInput) (stateEncoding := encRequestLog)
    (operationEncoding := encFinEnum Unit)
    (handler := fun caller => noteForgerHandlerWord sigBound com tag S caller.1 caller.2)
    (prepare := fun p : ℕ × List Bool => (p.1, p.2))
    (initial := fun _ => [])
    (growth := fun c w =>
      2 * (dc * ((encPair encParamInput encBits (c, w)).length + 1) ^ dd) + 2)
    (by fun_prop) hhandler (ComputableInPolyTime.const [])
    (fun _ _ => True) (fun _ => trivial) hgrowth
    (fun caller req accepted _ res hres =>
      ⟨trivial, mem_support_noteForgerHandlerWord_length_le hdecBound' caller req accepted res
        hres⟩)

/-- `noteForgerWord` is uniform strict oracle PPT whenever `sigBound`, `com`, `tag`, and `A` are
efficient. -/
theorem isOraclePPTOn_noteForgerWord {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool}
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits)
    {tag : List Bool → ℕ → List Bool}
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits)
    (S : WordSignatureScheme)
    {A : WordExtractedAdversary} (hA : IsOraclePPT encBits A) :
    IsOraclePPTOn encParamInput encNoteToken
      (fun p => noteForgerWord sigBound com tag S A p.1 p.2) := by
  simpa only [noteForgerWord, Function.comp_def] using
    (isOraclePPTOn_noteForgerRun hsigBound hcom htag S hA).map
      (ComputableInPolyTime.optionGetDWithInput
        (computableInPolyTime_findNoteForgery.comp (ComputableInPolyTime.snd _ _))
        (ComputableInPolyTime.const _))

private theorem eval_noteForgerWord_runState_eq (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool)
    (A : WordExtractedAdversary) (n : ℕ) (ck pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
      sig.length ≤ sigBound n msg.length)
    {State : Type}
    (step : Payload (Credit.Note (List Bool) (List Bool)) (List Bool) → List Bool → State → State)
    (log₀ : State) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (fun req acc =>
          let payload := notePayloadDecoder.decode req.2
          let msg := tag (com n ck payload.message.nullifier payload.message.context
            payload.message.credit payload.opening) payload.message.refund
          (fun sig => (sig, step payload sig acc)) <$> S.sign sk msg))
      (noteForgerWord sigBound com tag S A n (encWordPair (pk, ck)))).run log₀) =
      ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun msg acc =>
            (fun sig => (sig, step msg sig acc)) <$>
              (pairScheme S tag n).sign sk (Credit.target (com n ck) Prod.mk msg.message
                msg.opening)))
        (noteForger (com n ck) Prod.mk (pairScheme S tag n) (A.toTyped n ck) pk)).run log₀) := by
  simp only [noteForgerWord, noteForgerRun, noteForger, WordExtractedAdversary.toTyped,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure]
  have hinner :
      ProbOracleComp.runWith
        (fun req acc =>
          let payload := notePayloadDecoder.decode req.2
          let msg := tag (com n ck payload.message.nullifier payload.message.context
            payload.message.credit payload.opening) payload.message.refund
          ((ProbComp.eval (S.sign sk msg)).map fun sig => (sig, step payload sig acc)))
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (noteForgerHandlerWord sigBound com tag S n (encWordPair (pk, ck))))
          (A n (encWordPair (pk, ck)))).run []) log₀ =
      ProbOracleComp.runWith
        (fun msg acc =>
          (ProbComp.eval ((pairScheme S tag n).sign sk (Credit.target (com n ck) Prod.mk
            msg.message msg.opening))).map fun sig => (sig, step msg sig acc))
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (noteForgerHandler (com n ck) Prod.mk (pairScheme S tag n) pk))
          (ProbOracleComp.simulate
            (fun req : Unit × List Bool =>
              encOption encBits <$> ProbOracleComp.query (wordRequestDecoder.decode req.2))
            (A n (encWordPair (pk, ck))))).run []) log₀ := by
    rw [ProbOracleComp.runWith_run_interpret, ProbOracleComp.runWith_run_interpret]
    congr 1
    rw [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
      ProbOracleComp.runWith_interpret_sumHandler]
    congr 1
    funext req ⟨accepted, log⟩
    rw [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query]
    dsimp only [StateT.run, noteForgerHandlerWord, noteForgerHandler]
    simp only [wordPairDecoder.decode_enc]
    split_ifs with hcond
    · simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, notePayloadDecoder,
        payloadDecoderOf, Decoder.decode_enc, pairScheme, Credit.target, Request.outputPayload,
        PMF.bind_map, PMF.map_bind, PMF.map_comp, PMF.pure_map, Prod.map_fst, Prod.map_snd,
        id_eq, Function.comp_def]
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
      rw [List.take_of_length_le (hbound _ sig hsig)]
      rfl
    · simp only [ProbOracleComp.runWith_pure, PMF.pure_map, Prod.map_apply, id_eq]
  simpa only [ProbComp.eval_map, PMF.map, Function.comp_def, Prod.map, id_eq] using
    congrArg (PMF.map fun ⟨⟨_, accepted⟩, log⟩ =>
      ((findNoteForgery accepted).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩, log)) hinner

/-- Under `runExtractedWord`, `noteForgerWord` agrees in `PMF` law with `Conservation.noteForger`
on `pairScheme S tag n` and `WordExtractedAdversary.toTyped`, provided `sigBound` bounds supported
signature lengths of `S`. -/
theorem eval_runExtracted_noteForgerWord_eq (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ)
    (hbound : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (S.keyGen n)).support →
      ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
        sig.length ≤ sigBound n msg.length)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool) (A : WordExtractedAdversary) (n : ℕ) (ck : List Bool) :
    ProbComp.eval (runExtractedWord S
      (fun m c note opening =>
        tag (com m c note.nullifier note.context note.credit opening) note.refund)
      creditNoteDecoder (noteForgerWord sigBound com tag S A) n ck) =
      ProbComp.eval (runExtracted (pairScheme S tag n) (Credit.target (com n ck) Prod.mk)
        (noteForger (com n ck) Prod.mk (pairScheme S tag n) (A.toTyped n ck))) := by
  simp only [runExtractedWord, runExtracted, pairScheme, ProbComp.eval_bind, ProbComp.eval_pure]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ hkeys => ?_
  dsimp only
  congr 1
  exact eval_noteForgerWord_runState_eq S sigBound com tag A n ck pk sk
    (hbound n pk sk hkeys) (fun msg sig acc => acc ++ [(msg, sig)]) []

/-! ### Extracted VOLE-ACT conservation: `commitmentBindingReductionWord` and headline -/

/-- Binary encoding of `(nullifier, context, credit)` message triples committed by `wordNoteCom`. -/
abbrev encWordComMessage : (List Bool × List Bool × ℕ) ↪ List Bool :=
  encPair encBits (encPair encBits encNat)

/-- Encoding of a commitment binding collision over `(nullifier, context, credit)` triples. -/
enc_structure encWordBindingCollision :
    Crypto.Commitment.BindingCollision (List Bool × List Bool × ℕ) (List Bool) (List Bool) where
  commitment : encBits, msg₀ : encWordComMessage, opening₀ : encBits,
  msg₁ : encWordComMessage, opening₁ : encBits

attribute [fun_prop] encWordBindingCollision_commitment_polyTime
  encWordBindingCollision_msg₀_polyTime encWordBindingCollision_opening₀_polyTime
  encWordBindingCollision_msg₁_polyTime encWordBindingCollision_opening₁_polyTime
  encWordBindingCollision_mk_polyTime

/-- Two-stage target mapping a semantic `Credit.Note` and opening via `com` and `tag`. -/
def noteTarget (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool) (m : ℕ) (c : List Bool)
    (note : Credit.Note (List Bool) (List Bool)) (opening : List Bool) : List Bool :=
  tag (com m c note.nullifier note.context note.credit opening) note.refund

private theorem computableInPolyTime_noteTarget
    {com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool}
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits)
    {tag : List Bool → ℕ → List Bool}
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × Credit.Note (List Bool) (List Bool) × List Bool =>
        noteTarget com tag p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encTargetArgsOf encCreditNote) encBits := by
  have h1 := ComputableInPolyTime.fst encUnary (encPair encBits (encPair encCreditNote encBits))
  have h2 := ComputableInPolyTime.snd encUnary (encPair encBits (encPair encCreditNote encBits))
  have hnote := h2.snd'.fst'
  have hcom_val := hcom.comp ((h1.prod h2.fst').prod (encComInput_mk_polyTime
    (encCreditNote_nullifier_polyTime hnote) (encCreditNote_context_polyTime hnote)
    (encCreditNote_credit_polyTime hnote) h2.snd'.snd'))
  exact htag.comp (hcom_val.prod (encCreditNote_refund_polyTime hnote))

private theorem computableInPolyTime_noteBindingCollisionOrTrivial
    {com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool}
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits) :
    ComputableInPolyTime
      (fun q : (ℕ × List Bool) ×
          Option (BindingWitness (Credit.Note (List Bool) (List Bool)) (List Bool)) =>
        Conservation.noteBindingCollisionOrTrivial (com q.1.1 q.1.2) q.2)
      (encPair encParamInput (encOption (encBindingWitnessOf encCreditNote)))
      encWordBindingCollision := by
  let encOpt := encOption (encBindingWitnessOf encCreditNote)
  have hnone : ComputableInPolyTime
      (fun q : (ℕ × List Bool) ×
          Option (BindingWitness (Credit.Note (List Bool) (List Bool)) (List Bool)) =>
        ({ commitment := com q.1.1 q.1.2 default default 0 default
           msg₀ := (default, default, 0)
           opening₀ := default
           msg₁ := (default, default, 0)
           opening₁ := default } :
          Crypto.Commitment.BindingCollision (List Bool × List Bool × ℕ) (List Bool) (List Bool)))
      (encPair encParamInput encOpt) encWordBindingCollision :=
    encWordBindingCollision_mk_polyTime (hcom.comp ((ComputableInPolyTime.fst _ _).prod
        (ComputableInPolyTime.const (⟨default, default, 0, default⟩ : ComInput))))
      (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (ComputableInPolyTime.const _)
      (ComputableInPolyTime.const _)
  have hp_some := (ComputableInPolyTime.fst (encPair encParamInput encOpt)
    (encBindingWitnessOf encCreditNote)).fst'
  have hw := ComputableInPolyTime.snd (encPair encParamInput encOpt)
    (encBindingWitnessOf encCreditNote)
  have hfirst := encBindingWitnessOf_first_polyTime encCreditNote hw
  have hsecond := encBindingWitnessOf_second_polyTime encCreditNote hw
  have hn0 := encPayloadOf_message_polyTime encCreditNote hfirst
  have hr0 := encPayloadOf_opening_polyTime encCreditNote hfirst
  have hn1 := encPayloadOf_message_polyTime encCreditNote hsecond
  have hr1 := encPayloadOf_opening_polyTime encCreditNote hsecond
  have hargs0 := encComInput_mk_polyTime
    (encCreditNote_nullifier_polyTime hn0) (encCreditNote_context_polyTime hn0)
    (encCreditNote_credit_polyTime hn0) hr0
  have hcom0 := hcom.comp (hp_some.prod hargs0)
  have hmsg0 :=
    (encCreditNote_nullifier_polyTime hn0).prod
      ((encCreditNote_context_polyTime hn0).prod (encCreditNote_credit_polyTime hn0))
  have hmsg1 :=
    (encCreditNote_nullifier_polyTime hn1).prod
      ((encCreditNote_context_polyTime hn1).prod (encCreditNote_credit_polyTime hn1))
  have hsome := encWordBindingCollision_mk_polyTime hcom0 hmsg0 hr0 hmsg1 hr1
  have helim := ComputableInPolyTime.optionElimWithInput
    (body := fun (q : (ℕ × List Bool) ×
        Option (BindingWitness (Credit.Note (List Bool) (List Bool)) (List Bool)))
        (w : BindingWitness (Credit.Note (List Bool) (List Bool)) (List Bool)) =>
      ({ commitment := com q.1.1 q.1.2 w.first.message.nullifier
           w.first.message.context w.first.message.credit w.first.opening
         msg₀ := (w.first.message.nullifier, w.first.message.context,
           w.first.message.credit)
         opening₀ := w.first.opening
         msg₁ := (w.second.message.nullifier, w.second.message.context,
           w.second.message.credit)
         opening₁ := w.second.opening } :
        Crypto.Commitment.BindingCollision (List Bool × List Bool × ℕ) (List Bool) (List Bool)))
    (ComputableInPolyTime.snd encParamInput encOpt) hnone hsome
  convert helim using 1
  funext q
  cases q.2 <;> rfl

/-- Word-level commitment-binding reduction corresponding to
`Conservation.commitmentBindingReduction`: runs `bindingReductionWord` on `noteForgerWord` under
`noteTarget com tag` and maps any resulting witness via
`Conservation.noteBindingCollisionOrTrivial`. -/
def commitmentBindingReductionWord (sigBound : ℕ → ℕ → ℕ)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool) (S : WordSignatureScheme)
    (A : WordExtractedAdversary) (n : ℕ) (ck : List Bool) :
    ProbComp
      (Crypto.Commitment.BindingCollision (List Bool × List Bool × ℕ) (List Bool) (List Bool)) :=
  Conservation.noteBindingCollisionOrTrivial (com n ck) <$>
    bindingReductionWord S (noteTarget com tag) creditNoteDecoder
      (noteForgerWord sigBound com tag S A) n ck

/-- `commitmentBindingReductionWord` is uniform strict PPT in `(n, ck)` whenever `sigBound`,
`com`, `tag`, and `A` are efficient. -/
@[program_certificate]
theorem isPPTOn_commitmentBindingReductionWord {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool}
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        com p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits)
    {tag : List Bool → ℕ → List Bool}
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits)
    (S : WordSignatureScheme)
    {A : WordExtractedAdversary} (hA : IsOraclePPT encBits A) :
    IsPPTOn encParamInput encWordBindingCollision
      (fun p => commitmentBindingReductionWord sigBound com tag S A p.1 p.2) := by
  simpa only [commitmentBindingReductionWord] using
    (isPPTOn_bindingReductionWord S (computableInPolyTime_noteTarget hcom htag) creditNoteDecoder
      (isOraclePPTOn_noteForgerWord hsigBound hcom htag S hA).isOraclePPT).map_with
      (computableInPolyTime_noteBindingCollisionOrTrivial hcom)

private theorem findBindingWitness_noteTarget_eq
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool)
    (htag : Function.Injective (fun p : List Bool × ℕ => tag p.1 p.2))
    (n : ℕ) (ck : List Bool)
    (payload : Payload (Credit.Note (List Bool) (List Bool)) (List Bool))
    (log : List (Payload (Credit.Note (List Bool) (List Bool)) (List Bool) × List Bool)) :
    findBindingWitness (noteTarget com tag n ck) payload log =
      findBindingWitness (Credit.target (com n ck) Prod.mk) payload log := by
  simp only [findBindingWitness]
  congr 2
  funext entry
  exact decide_eq_decide.mpr (htag.eq_iff (a := (_, _)) (b := (_, _)))

/-- `commitmentBindingReductionWord` has the exact `PMF` law of
`Conservation.commitmentBindingReduction` at `(com n ck)` and `pairScheme S tag n`, provided
`sigBound` bounds signature lengths of `S` and `tag` is injective. -/
theorem eval_commitmentBindingReductionWord_eq {K : Type} (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ)
    (hbound : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (S.keyGen n)).support →
      ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
        sig.length ≤ sigBound n msg.length)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool)
    (htag : Function.Injective (fun p : List Bool × ℕ => tag p.1 p.2))
    (A : WordExtractedAdversary) (n : ℕ) (ck : List Bool) (k : K) :
    ProbComp.eval (commitmentBindingReductionWord sigBound com tag S A n ck) =
      ProbComp.eval (Conservation.commitmentBindingReduction (com n ck)
        (pairScheme S tag n) (A.toTyped n ck) k) := by
  simp only [Conservation.commitmentBindingReduction_eq, commitmentBindingReductionWord,
    bindingReductionWord, bindingReduction, ProbComp.eval_map, PMF.map_comp, Function.comp_def,
    findBindingWitness_noteTarget_eq com tag htag n ck]
  exact congrArg (PMF.map _)
    (eval_runExtracted_noteForgerWord_eq S sigBound hbound com tag A n ck)

private theorem eval_targetForger_noteForgerWord_runState_eq (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool)
    (A : WordExtractedAdversary) (n : ℕ) (ck pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
      sig.length ≤ sigBound n msg.length) :
    ProbComp.eval ((ProbOracleComp.simulate
      (fun payload => ProbOracleComp.query
        (Credit.target (com n ck) Prod.mk payload.message payload.opening))
      (ProbOracleComp.simulate
        (fun req : Unit × List Bool => ProbOracleComp.query (notePayloadDecoder.decode req.2))
        (noteForgerWord sigBound com tag S A n (encWordPair (pk, ck))))).runState
      (fun msg acc =>
        (fun sig => (sig, acc ++ [(msg, sig)])) <$> S.sign sk (tag msg.1 msg.2)) |>.run []) =
      ProbComp.eval ((ProbOracleComp.simulate
        (fun payload => ProbOracleComp.query
          (Credit.target (com n ck) Prod.mk payload.message payload.opening))
        (noteForger (com n ck) Prod.mk (pairScheme S tag n) (A.toTyped n ck) pk)).runState
        (fun msg acc =>
          (fun sig => (sig, acc ++ [(msg, sig)])) <$> S.sign sk (tag msg.1 msg.2))
        |>.run []) := by
  rw [ProbOracleComp.eval_runState, ProbOracleComp.eval_runState, ProbOracleComp.simulate,
    OracleComp.substitute_eq_interpret, ProbOracleComp.interpret_simulate,
    ProbOracleComp.simulate, OracleComp.substitute_eq_interpret]
  simp only [ProbOracleComp.interpret_query, ProbOracleComp.runWith_interpret_sumHandler]
  have h := eval_noteForgerWord_runState_eq S sigBound com tag A n ck pk sk hbound
    (fun msg sig acc => acc ++ [(Credit.target (com n ck) Prod.mk msg.message msg.opening, sig)]) []
  simp only [ProbOracleComp.eval_run_interpret_eq_runWith] at h
  convert h using 2 <;> funext q acc <;> exact ProbOracleComp.runWith_query _ _ _

/-- At every security parameter `n` and public parameter `ck`, wrapping `noteForgerWord` inside
`targetForgerWordOf creditNoteDecoder sigBound (noteTarget com tag)` matches `S.eufCmaExperiment`
of `Basic.targetForger` on `Conservation.noteForger`, provided `sigBound` bounds signature lengths
of `S` and `tag` is injective. -/
theorem eval_eufCmaGame_noteForgerWord_eq (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ)
    (hbound : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (S.keyGen n)).support →
      ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
        sig.length ≤ sigBound n msg.length)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool)
    (htag : Function.Injective (fun p : List Bool × ℕ => tag p.1 p.2))
    (A : WordExtractedAdversary) (n : ℕ) (ck : List Bool) :
    ProbComp.eval (S.eufCmaGame
      (fun m spk => targetForgerWordOf creditNoteDecoder sigBound (noteTarget com tag)
        (noteForgerWord sigBound com tag S A) m (spk, ck)) n) =
      ProbComp.eval ((pairScheme S tag n).eufCmaExperiment
        (targetForger (Credit.target (com n ck) Prod.mk)
          (noteForger (com n ck) Prod.mk (pairScheme S tag n) (A.toTyped n ck)))) := by
  simp only [WordSignatureScheme.eufCmaGame, Signature.Scheme.eufCmaExperiment, forgeExperiment,
    ProbComp.eval_bind, ProbComp.eval_pure]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨pk, sk⟩ hkeys => ?_
  dsimp only
  rw [funext fun l => funext (Signer.ofSign_apply (pairScheme S tag n).sign sk l),
    ProbOracleComp.runLogWith_some]
  simp only [targetForgerWordOf, targetForger, ProbOracleComp.runLog, bind_pure_comp,
    OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map, ProbOracleComp.runState_map]
  change (PMF.map _ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (SignatureScheme.signingOracleOf S.sign sk)) _).run []))).bind _ = _
  have hrun' := (eval_signingOracle_take_eq_targetForger_runLog_of creditNoteDecoder S.sign sk
    (Credit.target (com n ck) Prod.mk) (fun p : List Bool × ℕ => tag p.1 p.2)
    (sigBound n) (hbound n pk sk hkeys)
    (noteForgerWord sigBound com tag S A n (encWordPair (pk, ck))) [] [] rfl).trans
    (congrArg (PMF.map _) (eval_targetForger_noteForgerWord_runState_eq S sigBound com tag A n ck
      pk sk (hbound n pk sk hkeys)))
  dsimp only [noteTarget, Credit.target] at hrun' ⊢
  rw [hrun']
  simp only [PMF.bind_map, Function.comp_def, freshMessage, List.contains_reverse, pairScheme]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨tok, acc⟩ _ => ?_
  have hcontains : _ ∈ (acc.map Prod.fst).map (fun p => tag p.1 p.2) ↔
      (com n ck tok.payload.message.nullifier tok.payload.message.context
        tok.payload.message.credit tok.payload.opening, tok.payload.message.refund) ∈
        acc.map Prod.fst :=
    List.mem_map_of_injective htag
  simp only [List.map_map, Function.comp_def] at hcontains
  simp [decide_eq_decide.mpr hcontains, Bool.and_comm]

/-- Keyed hash-based note commitment applying `H ck` to the framed `ComInput` word
`encComInput ⟨nullifier, ctx, credit, opening⟩`. -/
def wordNoteCom (H : List Bool → List Bool → List Bool)
    (_ : ℕ) (ck nullifier ctx : List Bool) (credit : ℕ) (opening : List Bool) : List Bool :=
  H ck (encComInput ⟨nullifier, ctx, credit, opening⟩)

private theorem computableInPolyTime_wordNoteCom
    {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ComInput =>
        wordNoteCom H p.1.1 p.1.2 p.2.nullifier p.2.context p.2.credit p.2.opening)
      encComArgs encBits :=
  hH.comp (((ComputableInPolyTime.fst encParamInput encComInput).snd').prod
    ((ComputableInPolyTime.of_eq (f := encComInput) (encOut := encBits) fun _ => rfl).comp
      (ComputableInPolyTime.snd _ _)))

/-- Key-sampling EUF-CMA wrapper around `noteForgerWord` using `wordNoteCom H` and `wordTag`. -/
noncomputable def sampledConservationForger (sigBound : ℕ → ℕ → ℕ)
    (H : List Bool → List Bool → List Bool)
    (S : WordSignatureScheme) (A : WordExtractedAdversary) : Forger :=
  fun n pk => do
    let ck ← ProbOracleComp.sample (BitString.sampleList n)
    targetForgerWordOf creditNoteDecoder sigBound (noteTarget (wordNoteCom H) wordTag)
      (noteForgerWord sigBound (wordNoteCom H) wordTag S A) n (pk, ck)

/-- `sampledConservationForger` is uniform strict oracle PPT whenever `sigBound`, `H`, and `A` are
efficient. -/
theorem isOraclePPT_sampledConservationForger {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (S : WordSignatureScheme) {A : WordExtractedAdversary} (hA : IsOraclePPT encBits A) :
    IsOraclePPT (encPair encBits encBits) (sampledConservationForger sigBound H S A) := by
  have hcom := computableInPolyTime_wordNoteCom hH
  have hnf :=
    (isOraclePPTOn_noteForgerWord hsigBound hcom computableInPolyTime_wordTag S hA).isOraclePPT
  exact isOraclePPT_sampleList_bind
    (isOraclePPTOn_targetForgerWordOf creditNoteDecoder hsigBound
      (computableInPolyTime_noteTarget hcom computableInPolyTime_wordTag) hnf)

private theorem eval_eufCmaGame_sampledConservationForger_eq (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ) (H : List Bool → List Bool → List Bool)
    (A : WordExtractedAdversary) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame (sampledConservationForger sigBound H S A) n) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
        ProbComp.eval (S.eufCmaGame
          (fun m spk => targetForgerWordOf creditNoteDecoder sigBound
            (noteTarget (wordNoteCom H) wordTag)
            (noteForgerWord sigBound (wordNoteCom H) wordTag S A) m (spk, ck)) n) :=
  eval_eufCmaGame_sampleList_bind_eq S _ n

/-- Collision finder extracted from `commitmentBindingReductionWord` by mapping each commitment
binding collision `(c, m₀, r₀, m₁, r₁)` to the framed `ComInput` word pair
`(encComInput ..., encComInput ...)`. -/
def noteCollisionFinder (sigBound : ℕ → ℕ → ℕ) (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool) (A : WordExtractedAdversary) : CollisionFinder :=
  fun n ck =>
    (fun col =>
      let (nf₀, ctx₀, cr₀) := col.msg₀
      let (nf₁, ctx₁, cr₁) := col.msg₁
      (encComInput ⟨nf₀, ctx₀, cr₀, col.opening₀⟩,
       encComInput ⟨nf₁, ctx₁, cr₁, col.opening₁⟩)) <$>
      commitmentBindingReductionWord sigBound (wordNoteCom H) wordTag S A n ck

/-- `noteCollisionFinder` is uniform strict PPT whenever `sigBound`, `H`, and `A` are
efficient. -/
@[program_certificate]
theorem isPPT_noteCollisionFinder {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    (S : WordSignatureScheme)
    {H : List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    {A : WordExtractedAdversary} (hA : IsOraclePPT encBits A) :
    IsPPT (encPair encBits encBits) (noteCollisionFinder sigBound S H A) := by
  have hbr := isPPTOn_commitmentBindingReductionWord hsigBound
    (computableInPolyTime_wordNoteCom hH) computableInPolyTime_wordTag S hA
  have hmk (msg : Crypto.Commitment.BindingCollision
        (List Bool × List Bool × ℕ) (List Bool) (List Bool) → List Bool × List Bool × ℕ)
      (op : Crypto.Commitment.BindingCollision
        (List Bool × List Bool × ℕ) (List Bool) (List Bool) → List Bool)
      (hmsg : ComputableInPolyTime msg encWordBindingCollision encWordComMessage)
      (hop : ComputableInPolyTime op encWordBindingCollision encBits) :
      ComputableInPolyTime
        (fun col => encComInput ⟨(msg col).1, (msg col).2.1, (msg col).2.2, op col⟩)
        encWordBindingCollision encBits :=
    (ComputableInPolyTime.of_eq (f := encComInput) (encOut := encBits) fun _ => rfl).comp
      (encComInput_mk_polyTime hmsg.fst' hmsg.snd'.fst' hmsg.snd'.snd' hop)
  have hpair0 := hmk _ _ (encWordBindingCollision_msg₀_polyTime ComputableInPolyTime.id')
    (encWordBindingCollision_opening₀_polyTime ComputableInPolyTime.id')
  have hpair1 := hmk _ _ (encWordBindingCollision_msg₁_polyTime ComputableInPolyTime.id')
    (encWordBindingCollision_opening₁_polyTime ComputableInPolyTime.id')
  exact (hbr.map (hpair0.prod hpair1)).isPPT

private noncomputable def wordNoteCommitmentScheme
    (H : List Bool → List Bool → List Bool) (n : ℕ) (ck : List Bool) :
    Crypto.Commitment.Scheme (List Bool) (List Bool × List Bool × ℕ) (List Bool) (List Bool) where
  keyGen := pure ck
  commit _ _ := pure ([], [])
  verify _ msg c r :=
    let (nf, ctx, cr) := msg
    decide (wordNoteCom H n ck nf ctx cr r = c)

/-- Word-level extracted VOLE-ACT credit-conservation game: sample `ck ← BitString.sampleList n`
and run `Conservation.extractedConservationExperiment` with `wordNoteCom H n ck`,
`pairScheme S wordTag n`, and `A.toTyped n ck`. Every bit-string oracle query from `A` is
processed as the `Request` returned by the total decoder `wordRequestDecoder`
(`WordExtractedAdversary.toTyped`), rather than rejecting malformed words (`PartialDecoder`). -/
noncomputable def extractedConservationWordGame (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool) (A : WordExtractedAdversary) (n : ℕ) :
    ProbComp Bool := do
  let ck ← BitString.sampleList n
  extractedConservationExperiment (wordNoteCom H n ck) Prod.mk (pairScheme S wordTag n)
    (A.toTyped n ck)

/-- Word-level credit conservation in the extracted VOLE-ACT model: assuming only `S.EUFCMA`,
`CollisionResistant H`, and efficient `H` and `A` (with the signature length bound obtained
internally from `S.toSignatureScheme.exists_sign_length_bound`), any oracle-PPT adversary has
negligible probability of violating credit conservation in `extractedConservationWordGame`. -/
theorem negligible_extractedConservationWordGame (S : WordSignatureScheme) (hS : S.EUFCMA)
    (H : List Bool → List Bool → List Bool)
    (hHPoly : ComputableInPolyTime (fun p : List Bool × List Bool => H p.1 p.2)
      (encPair encBits encBits) encBits)
    (hH : CollisionResistant H)
    (A : WordExtractedAdversary) (hA : IsOraclePPT encBits A) :
    Negligible
      (fun n => Game.succProbability (ProbComp.eval (extractedConservationWordGame S H A n))) := by
  obtain ⟨sigBound, hsigPoly, hsigBound⟩ := S.toSignatureScheme.exists_sign_length_bound
  simp only [WordSignatureScheme.toSignatureScheme_keyGen,
    WordSignatureScheme.toSignatureScheme_sign] at hsigBound
  have hforgeNeg := hS.negligible (sampledConservationForger sigBound H S A)
    (isOraclePPT_sampledConservationForger hsigPoly hHPoly S hA)
  have hcollNeg := hH.negligible (noteCollisionFinder sigBound S H A)
    (isPPT_noteCollisionFinder hsigPoly S hHPoly hA)
  refine negligible_sampleList_add_bound S H
    (extractedConservationWordGame S H A)
    (fun n ck => extractedConservationExperiment (wordNoteCom H n ck) Prod.mk
      (pairScheme S wordTag n) (A.toTyped n ck))
    (sampledConservationForger sigBound H S A)
    (fun _ ck m spk => targetForgerWordOf creditNoteDecoder sigBound
      (noteTarget (wordNoteCom H) wordTag)
      (noteForgerWord sigBound (wordNoteCom H) wordTag S A) m (spk, ck))
    (noteCollisionFinder sigBound S H A)
    hforgeNeg hcollNeg
    (fun n => by simp only [extractedConservationWordGame, ProbComp.eval_bind])
    (eval_eufCmaGame_sampledConservationForger_eq S sigBound H A) ?_
  intro n ck
  have hle_enn := ENNReal.coe_le_coe.mpr
    (extractedConservationExperiment_succProbability_le_prod_mk (wordNoteCom H n ck)
      (wordNoteCommitmentScheme H n ck) (fun _ _ _ _ _ _ => rfl) (pairScheme S wordTag n)
      (A.toTyped n ck))
  simp only [Experiment.succProbability, Game.succProbability, ENNReal.coe_add,
    ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] at hle_enn
  rw [← eval_eufCmaGame_noteForgerWord_eq S sigBound
    (fun m pk sk hkeys msg sig hsig => hsigBound m (pk, sk) hkeys msg sig hsig)
    (wordNoteCom H) wordTag wordTag_injective A n ck] at hle_enn
  refine hle_enn.trans (add_le_add le_rfl ?_)
  simp only [Crypto.Commitment.Scheme.bindingExperiment, wordNoteCommitmentScheme,
    noteCollisionFinder, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.pure_bind, ← eval_commitmentBindingReductionWord_eq S sigBound
      (fun m pk sk hkeys msg sig hsig => hsigBound m (pk, sk) hkeys msg sig hsig)
      (wordNoteCom H) wordTag wordTag_injective A n ck ck, PMF.bind_map, Function.comp_def]
  refine Cslib.Probability.PMF.map_true_mono _ fun col _ hcol => ?_
  simp only [Crypto.Commitment.Scheme.isBindingCollision, Bool.and_eq_true, decide_eq_true_eq]
    at hcol
  rcases hcol with ⟨⟨hne, hc0⟩, hc1⟩
  simp only [isCollision_eq_true_iff, ne_eq, true_and]
  refine ⟨fun heq => hne ?_, hc0.trans hc1.symm⟩
  have hinj := encComInput.injective heq
  exact Prod.ext (congrArg ComInput.nullifier hinj)
    (Prod.ext (congrArg ComInput.context hinj) (congrArg ComInput.credit hinj))

end Conservation

end Cslib.Crypto.AnonymousToken

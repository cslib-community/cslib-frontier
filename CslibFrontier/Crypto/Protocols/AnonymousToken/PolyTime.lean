/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
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

/-- Interpret a word-level extracted forger as a typed `ExtractedForger` by decoding each word
query with `payloadDecoderOf D`. -/
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
  let callIn := encPair encPublicInput (encPair (encFinEnum Unit) encBits)
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.1, encWordPair p.2))
      encPublicInput (encPair encUnary encBits) := by
    unfold encPublicInput encWordPair
    fun_prop
  have hreq : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
        target p.1.1 p.1.2.2 ((payloadDecoderOf D).decode p.2.2).message
          ((payloadDecoderOf D).decode p.2.2).opening)
      callIn encBits := by
    have hp : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
          (payloadDecoderOf D).decode p.2.2) callIn (encPayloadOf encM) := by
      dsimp only [callIn, encPublicInput, encWordPair]
      exact hdec.comp (ComputableInPolyTime.snd _ _).snd'
    have hn : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool => p.1.1)
        callIn encUnary := by
      dsimp only [callIn, encPublicInput, encWordPair]
      fun_prop
    have hck : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool => p.1.2.2)
        callIn encBits := by
      dsimp only [callIn, encPublicInput, encWordPair]
      fun_prop
    exact htarget.comp (hn.prod (hck.prod
      ((encPayloadOf_message_polyTime encM hp).prod
        (encPayloadOf_opening_polyTime encM hp))))
  have hlim : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
        sigBound p.1.1 (target p.1.1 p.1.2.2 ((payloadDecoderOf D).decode p.2.2).message
          ((payloadDecoderOf D).decode p.2.2).opening).length)
      callIn encUnary := by
    have hn : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool => p.1.1)
        callIn encUnary := by
      dsimp only [callIn, encPublicInput, encWordPair]
      fun_prop
    exact hsigBound.comp (hn.prod (ComputableInPolyTime.length_bits.comp hreq))
  have hres : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        sigBound p.1.1 (target p.1.1 p.1.2.2 ((payloadDecoderOf D).decode p.2).message
          ((payloadDecoderOf D).decode p.2).opening).length)
      (encPair encPublicInput encBits) encUnary := by
    let E := encPair encPublicInput encBits
    have hpe : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool =>
          (payloadDecoderOf D).decode p.2) E (encPayloadOf encM) :=
      hdec.comp (ComputableInPolyTime.snd _ _)
    have hn : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => p.1.1) E encUnary := by
      dsimp only [E, encPublicInput, encWordPair]
      fun_prop
    have hck : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => p.1.2.2) E encBits := by
      dsimp only [E, encPublicInput, encWordPair]
      fun_prop
    have hm := htarget.comp (hn.prod (hck.prod
      ((encPayloadOf_message_polyTime encM hpe).prod
        (encPayloadOf_opening_polyTime encM hpe))))
    exact hsigBound.comp (hn.prod (ComputableInPolyTime.length_bits.comp hm))
  have hhandler : IsOraclePPTOn callIn encBits
      (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
        let payload := (payloadDecoderOf D).decode p.2.2
        let msg := target p.1.1 p.1.2.2 payload.message payload.opening
        List.take (sigBound p.1.1 msg.length) <$> ProbOracleComp.query ((), msg)) :=
    IsOraclePPTOn.query_take () hreq hlim
  have hinterp := hA.on.interpret_preprocess_open'
    (operationEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool × List Bool) (request : Unit × List Bool) =>
      let payload := (payloadDecoderOf D).decode request.2
      let msg := target p.1 p.2.2 payload.message payload.opening
      List.take (sigBound p.1 msg.length) <$> ProbOracleComp.query ((), msg))
    (prepare := fun p : ℕ × List Bool × List Bool => (p.1, encWordPair p.2))
    (resources := fun p w =>
      let payload := (payloadDecoderOf D).decode w
      sigBound p.1 (target p.1 p.2.2 payload.message payload.opening).length)
    hprep hhandler hres fun p request reply hreply => by
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact List.length_take_le _ _
  have hpost : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × Token Message (List Bool) (List Bool) =>
        (target p.1.1 p.1.2.2 p.2.payload.message p.2.payload.opening, p.2.signature))
      (encPair encPublicInput (encTokenOf encM)) encWordPair := by
    have hn : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token Message (List Bool) (List Bool) =>
          p.1.1) (encPair encPublicInput (encTokenOf encM)) encUnary := by
      dsimp only [encPublicInput, encWordPair]
      fun_prop
    have hck : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token Message (List Bool) (List Bool) =>
          p.1.2.2) (encPair encPublicInput (encTokenOf encM)) encBits := by
      dsimp only [encPublicInput, encWordPair]
      fun_prop
    have hpay : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token Message (List Bool) (List Bool) =>
          p.2.payload) (encPair encPublicInput (encTokenOf encM)) (encPayloadOf encM) :=
      encTokenOf_payload_polyTime encM (ComputableInPolyTime.snd _ _)
    have hsig : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token Message (List Bool) (List Bool) =>
          p.2.signature) (encPair encPublicInput (encTokenOf encM)) encBits :=
      encTokenOf_signature_polyTime encM (ComputableInPolyTime.snd _ _)
    have ht := htarget.comp (hn.prod (hck.prod
      ((encPayloadOf_message_polyTime encM hpay).prod
        (encPayloadOf_opening_polyTime encM hpay))))
    exact ht.prod hsig
  simpa only [targetForgerWordOf, bind_pure_comp] using
    hinterp.map_with (f := fun p tok =>
      (target p.1 p.2.2 tok.payload.message tok.payload.opening, tok.signature)) hpost

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
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_interpret_sumHandler]
  rw [ProbOracleComp.eval_runState]
  have hsim : ∀ (prog' : WordOracleComp Unit α),
      ProbOracleComp.simulate
        (fun payload => ProbOracleComp.query (target payload.message payload.opening))
        (ProbOracleComp.simulate
          (fun req : Unit × List Bool =>
            ProbOracleComp.query ((payloadDecoderOf D).decode req.2))
          prog') =
        OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
            (fun req : Unit × List Bool =>
              let payload := (payloadDecoderOf D).decode req.2
              ProbOracleComp.query (spec := fun _ : Target => List Bool)
                (target payload.message payload.opening)))
          prog' := by
    intro prog'
    rw [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
      ProbOracleComp.interpret_simulate]
    simp only [ProbOracleComp.interpret_query]
  rw [hsim, ProbOracleComp.runWith_interpret_sumHandler]
  symm
  refine ProbOracleComp.runWith_map_state _ _ (fun acc => (acc.map (fun e => tag e.1)).reverse)
    (fun req acc => ?_) prog log
  dsimp only
  simp only [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    SignatureScheme.signingOracleOf, SignatureScheme.signingOracleOn, ↓reduceIte,
    ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, pmf_norm, PMF.map,
    Function.comp_def]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
  have htake : List.take (sigBound
      (tag (target ((payloadDecoderOf D).decode req.2).message
        ((payloadDecoderOf D).decode req.2).opening)).length) sig = sig :=
    List.take_of_length_le (hbound _ sig hsig)
  simp [htake, List.map_append, List.reverse_append]

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
  have hs : Signer.ofSign S.sign sk = fun _ msg => some (S.sign sk msg) := by
    funext _ msg
    exact Signer.ofSign_apply _ _ _ _
  rw [hs, ProbOracleComp.runLogWith_some]
  simp only [targetForgerWord, targetForgerWordOf, targetForger, WordExtractedForgerOf.toTyped,
    WordExtractedForgerOf.atKey, ProbOracleComp.runLog, bind_pure_comp, OracleComp.interpret_map,
    StateT.run_map, ProbComp.eval_map, ProbOracleComp.runState_map]
  change (PMF.map _ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (SignatureScheme.signingOracleOf S.sign sk)) _).run []))).bind _ = _
  have hrun := eval_signingOracle_take_eq_targetForger_runLog_of Decoder.bits S.sign sk
    (target n ck) id (sigBound n) (hbound n pk sk hkeys) (A n (encWordPair (pk, ck))) [] [] rfl
  dsimp only [id_eq] at hrun
  rw [hrun]
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
  have hdec : ComputableInPolyTime (payloadDecoderOf D).decode encBits (encPayloadOf encM) :=
    (payloadDecoderOf D).computableInPolyTime
  have hcaller : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool) => p.1)
      (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
      encExtractedCaller := ComputableInPolyTime.fst _ _
  have hparam : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool) => p.1.1)
      (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
      encParamInput := hcaller.fst'
  have hkeys : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool) => p.1.2)
      (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
      encWordPair := hcaller.snd'
  have hn := hparam.fst'
  have hck := hparam.snd'
  have hsk := hkeys.snd'
  have hrest : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool) => p.2)
      (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
      (encPair (encPair (encFinEnum Unit) encBits) (encPayloadLogOf encM)) :=
    ComputableInPolyTime.snd _ _
  have hreqw := hrest.fst'.snd'
  have hacc := hrest.snd'
  have hp : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool) => (payloadDecoderOf D).decode p.2.1.2)
      (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
      (encPayloadOf encM) :=
    hdec.comp hreqw
  have hmsg : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool) =>
        target p.1.1.1 p.1.1.2 ((payloadDecoderOf D).decode p.2.1.2).message
          ((payloadDecoderOf D).decode p.2.1.2).opening)
      (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
      encBits :=
    htarget.comp (hn.prod (hck.prod
      ((encPayloadOf_message_polyTime encM hp).prod
        (encPayloadOf_opening_polyTime encM hp))))
  have hsign := S.isPPTOn_sign_comp hsk hmsg
  refine hsign.map_with
    (f := fun p sig => (sig, p.2.2 ++ [((payloadDecoderOf D).decode p.2.1.2, sig)])) ?_
  have hfst : ComputableInPolyTime
      (fun q : (((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool)) × List Bool => q.1)
      (encPair (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
        encBits)
      (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM)) :=
    ComputableInPolyTime.fst _ _
  have hsig : ComputableInPolyTime
      (fun q : (((ℕ × List Bool) × (List Bool × List Bool)) × (Unit × List Bool) ×
          List (Payload Message (List Bool) × List Bool)) × List Bool => q.2)
      (encPair (encHandlerCall encExtractedCaller (encFinEnum Unit) (encPayloadLogOf encM))
        encBits)
      encBits :=
    ComputableInPolyTime.snd _ _
  have hpay' := hp.comp hfst
  have hacc' := hacc.comp hfst
  have hentry := (ComputableInPolyTime.cons (encPayloadLogEntryOf encM)).comp
    ((hpay'.prod hsig).prod (ComputableInPolyTime.const []))
  exact hsig.prod ((ComputableInPolyTime.listAppend (encPayloadLogEntryOf encM)).comp
    (hacc'.prod hentry))

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
    have hc1 : ComputableInPolyTime
        (fun c : (ℕ × List Bool) × (List Bool × List Bool) => c.1)
        encExtractedCaller encParamInput := ComputableInPolyTime.fst _ _
    have hc2 : ComputableInPolyTime
        (fun c : (ℕ × List Bool) × (List Bool × List Bool) => c.2)
        encExtractedCaller encWordPair := ComputableInPolyTime.snd _ _
    exact hc1.fst'.prod (hc2.fst'.prod hc1.snd')
  have hhandler := isPPTOn_runExtractedHandler S htarget D
  obtain ⟨dc, dd, hdecBound⟩ := hdec.polyBounded_length.exists_le
  obtain ⟨tc, td, htBound⟩ := htarget.polyBounded_length.exists_le
  obtain ⟨sc, sd, hsBound⟩ := S.sign_ppt.length_le
  let polyB (B : ℕ) : ℕ :=
    let decL := dc * (B + 1) ^ dd
    let msgL := tc * (4 * B + 2 * decL + 10) ^ td
    let sigL := sc * (2 * B + msgL + 2) ^ sd
    2 * (2 * decL + 2 * sigL + 4) + 2
  have hpolyB : PolynomiallyBounded polyB := by
    dsimp only [polyB]
    fun_prop
  let growth (c : (ℕ × List Bool) × (List Bool × List Bool)) (w : List Bool) : ℕ :=
    polyB (encPair encExtractedCaller encBits (c, w)).length
  have hgrowth : PolyBounded
      (fun p : ((ℕ × List Bool) × (List Bool × List Bool)) × List Bool =>
        (encPair encExtractedCaller encBits p).length)
      (fun ⟨c, w⟩ => growth c w) := by
    dsimp only [growth]
    exact PolyBounded.of_polynomiallyBounded_comp (p := polyB) hpolyB
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
      have hB_w : req.2.length ≤ B := by
        dsimp only [B]
        enc_len
      have hB_n : caller.1.1 ≤ B := by
        dsimp only [B, encExtractedCaller, encParamInput]
        enc_len
      have hB_ck : caller.1.2.length ≤ B := by
        dsimp only [B, encExtractedCaller, encParamInput]
        enc_len
      have hB_sk : caller.2.2.length ≤ B := by
        dsimp only [B, encExtractedCaller, encWordPair]
        enc_len
      let payload := (payloadDecoderOf D).decode req.2
      let msg := target caller.1.1 caller.1.2 payload.message payload.opening
      have hplen : (encPayloadOf encM payload).length ≤ dc * (B + 1) ^ dd := by
        have hd := hdecBound req.2
        simp only [encBits_apply] at hd
        exact hd.trans (Nat.mul_le_mul_left dc (Nat.pow_le_pow_left (by omega) dd))
      have hmlen : msg.length ≤ tc * (4 * B + 2 * (dc * (B + 1) ^ dd) + 10) ^ td := by
        have hm := htBound (caller.1.1, caller.1.2, payload.message, payload.opening)
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hm
        have hpenc : (encPayloadOf encM payload).length =
            2 * (encM payload.message).length + 1 + payload.opening.length := by
          simp [encPayloadOf_apply, encBits_apply]
        exact hm.trans (Nat.mul_le_mul_left tc (Nat.pow_le_pow_left (by omega) td))
      have hslen : sig.length ≤
          sc * (2 * B + tc * (4 * B + 2 * (dc * (B + 1) ^ dd) + 10) ^ td + 2) ^ sd := by
        have hs := hsBound (caller.2.2, msg) sig hsig
        simp only [length_encPair, encBits_apply] at hs
        exact hs.trans (Nat.mul_le_mul_left sc (Nat.pow_le_pow_left (by omega) sd))
      change (encPayloadLogOf encM (acc ++ [(payload, sig)])).length ≤
        (encPayloadLogOf encM acc).length + growth caller req.2
      have hlen : (encPayloadLogOf encM (acc ++ [(payload, sig)])).length =
          (encPayloadLogOf encM acc).length +
            (2 * (encPayloadLogEntryOf encM (payload, sig)).length + 1) := by
        simp [encPayloadLogOf, encList_append, encList_cons, encList_nil, length_frame]
      have hentry : (encPayloadLogEntryOf encM (payload, sig)).length ≤
          2 * (dc * (B + 1) ^ dd) +
            sc * (2 * B + tc * (4 * B + 2 * (dc * (B + 1) ^ dd) + 10) ^ td + 2) ^ sd + 2 := by
        simp only [encPayloadLogEntryOf, length_encPair, encBits_apply]
        omega
      dsimp only [growth, polyB, B] at hlen hentry ⊢
      omega)
  have hkeys : IsPPTOn encParamInput (encPair encBits encBits)
      (fun p : ℕ × List Bool => S.keyGen p.1) :=
    S.keyGen_ppt.preprocess (ComputableInPolyTime.fst encUnary encBits)
  let PostTy := ((ℕ × List Bool) × (List Bool × List Bool)) ×
    (Token Message (List Bool) (List Bool) × List (Payload Message (List Bool) × List Bool))
  let encPost := encPair encExtractedCaller (encPair (encTokenOf encM) (encPayloadLogOf encM))
  have hcaller' : ComputableInPolyTime (fun q : PostTy => q.1)
      encPost encExtractedCaller := ComputableInPolyTime.fst _ _
  have hres' : ComputableInPolyTime (fun q : PostTy => q.2)
      encPost (encPair (encTokenOf encM) (encPayloadLogOf encM)) := ComputableInPolyTime.snd _ _
  have hpost : ComputableInPolyTime
      (fun q : PostTy =>
        (⟨q.1.2.1, q.2.1, q.2.2⟩ : Execution (List Bool) Message (List Bool) (List Bool)))
      encPost (encExecutionOf encM) :=
    encExecutionOf_mk_polyTime encM hcaller'.snd'.fst' hres'.fst' hres'.snd'
  simpa only [runExtractedWord, bind_pure_comp] using hkeys.bind_with (hrun.map_with hpost)

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
  dsimp only
  congr 1
  simp only [WordExtractedForgerOf.toTyped, WordExtractedForgerOf.atKey, ProbOracleComp.runLog,
    ProbOracleComp.runState]
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
    ProbOracleComp.runWith_interpret_sumHandler]
  congr 1
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
  let ETy := (ℕ × List Bool) × Payload Message (List Bool) ×
    List (Payload Message (List Bool) × List Bool)
  have he1 : ComputableInPolyTime (fun p : ETy => p.1) E encParamInput :=
    ComputableInPolyTime.fst _ _
  have he2 : ComputableInPolyTime (fun p : ETy => p.2)
      E (encPair (encPayloadOf encM) (encPayloadLogOf encM)) := ComputableInPolyTime.snd _ _
  have hlog : ComputableInPolyTime (fun p : ETy => p.2.2) E (encPayloadLogOf encM) := he2.snd'
  have hq1 : ComputableInPolyTime (fun q : ETy × (Payload Message (List Bool) × List Bool) => q.1)
      (encPair E (encPayloadLogEntryOf encM)) E := ComputableInPolyTime.fst _ _
  have hq2 : ComputableInPolyTime (fun q : ETy × (Payload Message (List Bool) × List Bool) => q.2)
      (encPair E (encPayloadLogEntryOf encM)) (encPayloadLogEntryOf encM) :=
    ComputableInPolyTime.snd _ _
  have hn := (he1.comp hq1).fst'
  have hck := (he1.comp hq1).snd'
  have hpay1 := hq2.fst'
  have hpay2 := (he2.comp hq1).fst'
  have ht1 := htarget.comp (hn.prod (hck.prod
    ((encPayloadOf_message_polyTime encM hpay1).prod
      (encPayloadOf_opening_polyTime encM hpay1))))
  have ht2 := htarget.comp (hn.prod (hck.prod
    ((encPayloadOf_message_polyTime encM hpay2).prod
      (encPayloadOf_opening_polyTime encM hpay2))))
  have htest : ComputableInPolyTime
      (fun q : ETy × (Payload Message (List Bool) × List Bool) =>
        decide (target q.1.1.1 q.1.1.2 q.2.1.message q.2.1.opening =
          target q.1.1.1 q.1.1.2 q.1.2.1.message q.1.2.1.opening))
      (encPair E (encPayloadLogEntryOf encM)) encBool :=
    ComputableInPolyTime.decide_eq' ht1 ht2
  have hfind := ComputableInPolyTime.findWithInput
    (test := fun p entry =>
      decide (target p.1.1 p.1.2 entry.1.message entry.1.opening =
        target p.1.1 p.1.2 p.2.1.message p.2.1.opening))
    hlog htest
  exact ComputableInPolyTime.optionMapWithInput hfind
    (encBindingWitnessOf_mk_polyTime encM hpay2 hpay1)

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
  have hrun := isPPTOn_runExtractedWord S htarget D hA
  have hfind := computableInPolyTime_findBindingWitness htarget
  have hpost : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × Execution (List Bool) Message (List Bool) (List Bool) =>
        findBindingWitness (target q.1.1 q.1.2) q.2.output.payload q.2.log)
      (encPair encParamInput (encExecutionOf encM)) (encOption (encBindingWitnessOf encM)) := by
    have hp : ComputableInPolyTime
        (fun q : (ℕ × List Bool) × Execution (List Bool) Message (List Bool) (List Bool) =>
          q.1) (encPair encParamInput (encExecutionOf encM)) encParamInput :=
      ComputableInPolyTime.fst _ _
    have hq : ComputableInPolyTime
        (fun q : (ℕ × List Bool) × Execution (List Bool) Message (List Bool) (List Bool) =>
          q.2) (encPair encParamInput (encExecutionOf encM)) (encExecutionOf encM) :=
      ComputableInPolyTime.snd _ _
    have hout := encExecutionOf_output_polyTime encM hq
    have hpay := encTokenOf_payload_polyTime encM hout
    have hlog := encExecutionOf_log_polyTime encM hq
    exact hfind.comp (hp.prod (hpay.prod hlog))
  simpa only [bindingReductionWord] using hrun.map_with hpost

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
  have hck : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => p.2.1) encTargetArgs encBits := by
    dsimp only [encTargetArgs, encKeyedWordPair, encWordPair]
    fun_prop
  have hm : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => p.2.2.1) encTargetArgs encBits := by
    dsimp only [encTargetArgs, encKeyedWordPair, encWordPair]
    fun_prop
  have ho : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => p.2.2.2) encTargetArgs encBits := by
    dsimp only [encTargetArgs, encKeyedWordPair, encWordPair]
    fun_prop
  have hpay : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × List Bool => encWordPayload ⟨p.2.2.1, p.2.2.2⟩)
      encTargetArgs encBits :=
    (ComputableInPolyTime.of_eq (f := encWordPayload) (encOut := encBits) fun _ => rfl).comp
      (encPayloadOf_mk_polyTime encBits hm ho)
  exact hH.comp (hck.prod hpay)

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
    IsOraclePPT (encPair encBits encBits) (sampledTargetForger sigBound H A) := by
  have hsamp : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool => ProbOracleComp.sample (BitString.sampleList p.1)) :=
    (isPPTOn_sampleList.preprocess (ComputableInPolyTime.fst encUnary encBits)).isOraclePPTOn
      (Operation := Unit)
  have htf : IsOraclePPTOn encPublicInput encWordPair
      (fun p => targetForgerWord sigBound (wordPayloadTarget H) A p.1 p.2) :=
    isOraclePPTOn_targetForgerWord hsigBound (computableInPolyTime_wordPayloadTarget hH) hA
  have hprep : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × List Bool => (q.1.1, (q.1.2, q.2)))
      (encPair (encPair encUnary encBits) encBits) encPublicInput := by
    dsimp only [encPublicInput, encWordPair]
    fun_prop
  exact (hsamp.bind_with (htf.preprocess hprep)).isOraclePPT

private theorem eval_eufCmaGame_sampledTargetForger_eq (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ) (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) (n : ℕ) :
    ProbComp.eval (S.eufCmaGame (sampledTargetForger sigBound H A) n) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
        ProbComp.eval (S.eufCmaGame
          (fun m spk => targetForgerWord sigBound (wordPayloadTarget H) A m (spk, ck)) n) := by
  simp only [WordSignatureScheme.eufCmaGame, sampledTargetForger,
    ProbComp.eval_bind, ProbComp.eval_pure]
  have h1 : ∀ pk sk : List Bool,
      ((ProbComp.eval ((OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.signingOracle sk))
          (ProbOracleComp.sample (BitString.sampleList n) >>= fun ck =>
            targetForgerWord sigBound (wordPayloadTarget H) A n (pk, ck))).run [])).bind
          fun out => PMF.pure (!out.2.contains out.1.1 && S.verify pk out.1.1 out.1.2)) =
      (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
        ((ProbComp.eval ((OracleComp.interpret
            (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
              (S.signingOracle sk))
            (targetForgerWord sigBound (wordPayloadTarget H) A n (pk, ck))).run [])).bind
          fun out => PMF.pure (!out.2.contains out.1.1 && S.verify pk out.1.1 out.1.2)) := by
    intro pk sk
    rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_sample_bind,
      PMF.bind_bind]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ck _ => ?_
    rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  simp only [h1]
  exact PMF.bind_comm _ _ _

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
  have hbr := isPPTOn_bindingReductionWord S (computableInPolyTime_wordPayloadTarget hH)
    Decoder.bits hA
  have hbody : ComputableInPolyTime
      (fun q : ((ℕ × List Bool) × Option (BindingWitness (List Bool) (List Bool))) ×
          BindingWitness (List Bool) (List Bool) =>
        (encWordPayload q.2.first, encWordPayload q.2.second))
      (encPair (encPair encParamInput encOptionWordBindingWitness) encWordBindingWitness)
      (encPair encBits encBits) := by
    have hw : ComputableInPolyTime
        (fun q : ((ℕ × List Bool) × Option (BindingWitness (List Bool) (List Bool))) ×
            BindingWitness (List Bool) (List Bool) => q.2)
        (encPair (encPair encParamInput encOptionWordBindingWitness) encWordBindingWitness)
        encWordBindingWitness := ComputableInPolyTime.snd _ _
    have henc : ComputableInPolyTime (fun p => encWordPayload p) encWordPayload encBits :=
      ComputableInPolyTime.of_eq (f := encWordPayload) (encOut := encBits) fun _ => rfl
    exact (henc.comp (encBindingWitnessOf_first_polyTime encBits hw)).prod
      (henc.comp (encBindingWitnessOf_second_polyTime encBits hw))
  have hpost : ComputableInPolyTime
      (fun q : (ℕ × List Bool) × Option (BindingWitness (List Bool) (List Bool)) =>
        q.2.elim ([], []) fun w => (encWordPayload w.first, encWordPayload w.second))
      (encPair encParamInput encOptionWordBindingWitness) (encPair encBits encBits) :=
    ComputableInPolyTime.optionElimWithInput
      (ComputableInPolyTime.snd encParamInput encOptionWordBindingWitness)
      (ComputableInPolyTime.const ([], [])) hbody
  exact (hbr.map_with hpost).isPPT

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
    refine ⟨fun heq => hw.1 ?_, hw.2⟩
    have hinj := encWordPayload.injective heq
    exact congrArg Payload.message hinj

/-- Word-level extracted anonymous-token game: sample `ck ← BitString.sampleList n`, run
`runExtractedWord` with `wordPayloadTarget H`, and accept when `extractedAccept` holds. -/
noncomputable def extractedTokenWordGame (S : WordSignatureScheme)
    (H : List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool)) (n : ℕ) : ProbComp Bool := do
  let ck ← BitString.sampleList n
  let run ← runExtractedWord S (wordPayloadTarget H) Decoder.bits A n ck
  return extractedAccept (S.toScheme n) (wordPayloadTarget H n ck) run

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
  refine negligible_of_le (hforgeNeg.add_fun hcollNeg) fun n => ?_
  have hpt : ∀ ck : List Bool,
      (ProbComp.eval (extractedExperiment (S.toScheme n) (wordPayloadTarget H n ck)
        (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n))) true ≤
      (ProbComp.eval (S.eufCmaGame
        (fun m spk => targetForgerWord sigBound (wordPayloadTarget H) A m (spk, ck)) n)) true +
      (ProbComp.eval (do
        let pair ← targetCollisionFinder S H A n ck
        return isCollision H (fun _ _ => true) n ck pair.1 pair.2)) true := by
    intro ck
    have hle := extracted_succProbability_le (S.toScheme n) (wordPayloadTarget H n ck)
      (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n)
    have hle_enn := ENNReal.coe_le_coe.mpr hle
    simp only [Experiment.succProbability, Game.succProbability, ENNReal.coe_add,
      ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] at hle_enn
    rw [← eval_eufCmaGame_targetForgerWord_eq S (wordPayloadTarget H) sigBound
      (fun m pk sk hkeys msg sig hsig => hsigBound m (pk, sk) hkeys msg sig hsig) A n ck]
      at hle_enn
    exact hle_enn.trans (add_le_add le_rfl (bindingExperiment_le_collision S H A n ck))
  have hbind : (ProbComp.eval (extractedTokenWordGame S H A n)) true ≤
      (ProbComp.eval (S.eufCmaGame (sampledTargetForger sigBound H A) n)) true +
      (ProbComp.eval (collisionGame H (fun _ _ => true) (targetCollisionFinder S H A) n)) true := by
    have hext : ProbComp.eval (extractedTokenWordGame S H A n) =
        (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
          ProbComp.eval (extractedExperiment (S.toScheme n) (wordPayloadTarget H n ck)
            (WordExtractedForgerOf.toTyped Decoder.bits (A.atKey ck) n)) := by
      simp only [extractedTokenWordGame, extractedExperiment, ProbComp.eval_bind,
        ProbComp.eval_map, ProbComp.eval_pure]
      refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ck _ => ?_
      rw [eval_runExtractedWord_eq]
      exact PMF.bind_pure_comp _ _
    have hcoll : ProbComp.eval (collisionGame H (fun _ _ => true)
          (targetCollisionFinder S H A) n) =
        (ProbComp.eval (BitString.sampleList n)).bind fun ck =>
          ProbComp.eval (do
            let pair ← targetCollisionFinder S H A n ck
            return isCollision H (fun _ _ => true) n ck pair.1 pair.2) := by
      simp only [collisionGame, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [hext, eval_eufCmaGame_sampledTargetForger_eq, hcoll]
    exact Cslib.Probability.PMF.bind_apply_le_add_on_support _ true fun ck _ => hpt ck
  have hsucc : (ProbComp.eval (extractedTokenWordGame S H A n) true).toNNReal ≤
      ((ProbComp.eval (S.eufCmaGame (sampledTargetForger sigBound H A) n) true) +
        (ProbComp.eval (collisionGame H (fun _ _ => true)
          (targetCollisionFinder S H A) n) true)).toNNReal :=
    ENNReal.toNNReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)
      hbind
  simpa only [Game.succProbability, ENNReal.toNNReal_add (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)] using hsucc

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

/-- Encoding of `(nullifier, ctx, amount, opening)` passed to commitment functions. -/
abbrev encComTuple : (List Bool × List Bool × ℕ × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits (encPair encNat encBits))

/-- Encoding of `((n, ck), (nullifier, ctx, amount, opening))` supplied to keyed commitments. -/
abbrev encComArgs :
    ((ℕ × List Bool) × (List Bool × List Bool × ℕ × List Bool)) ↪ List Bool :=
  encPair encParamInput encComTuple

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

theorem wordTag_injective : Function.Injective (fun p : List Bool × ℕ => wordTag p.1 p.2) :=
  encTagPair.injective

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

/-- Interpret a word-level conservation adversary as a typed `ExtractedAdversary` at `(n, ck)`. -/
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
      encIssueRequest encNotePayload := by
    have hnote : ComputableInPolyTime
        (fun r : IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
          (⟨r.nullifier, r.ctx, r.amount, 0⟩ : Credit.Note (List Bool) (List Bool)))
        encIssueRequest encCreditNote := by
      have h0 : ComputableInPolyTime
          (fun _ : IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) => (0 : ℕ))
          encIssueRequest encNat := ComputableInPolyTime.const 0
      fun_prop
    exact encPayloadOf_mk_polyTime encCreditNote hnote (by fun_prop)
  have hsp : ComputableInPolyTime
      (fun s : SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        (⟨⟨s.newNullifier, s.ctx, s.newCredit, s.refund⟩, s.newOpening⟩ :
          Payload (Credit.Note (List Bool) (List Bool)) (List Bool)))
      encSpendRequest encNotePayload := by
    have hnote : ComputableInPolyTime
        (fun s : SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
          (⟨s.newNullifier, s.ctx, s.newCredit, s.refund⟩ :
            Credit.Note (List Bool) (List Bool)))
        encSpendRequest encCreditNote := by
      fun_prop
    exact encPayloadOf_mk_polyTime encCreditNote hnote (by fun_prop)
  have h := (ComputableInPolyTime.sumElim his hsp).comp heq
  refine h.of_enc_eq ?_
  intro r
  cases r <;> rfl

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
      (fun p : (ℕ × List Bool) × (List Bool × List Bool × ℕ × List Bool) =>
        com p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
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
    have hq1 : ComputableInPolyTime
        (fun q : (PIn × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) => q.1.1.1)
        (encPair (encPair encP encWordRequest) encIssueRequest) encParamInput :=
      (ComputableInPolyTime.fst _ _).fst'.fst'
    have hq2 := ComputableInPolyTime.snd (encPair encP encWordRequest) encIssueRequest
    have hc := hcom.comp (hq1.prod
      ((encIssueRequest_nullifier_polyTime hq2).prod
        ((encIssueRequest_ctx_polyTime hq2).prod
          ((encIssueRequest_amount_polyTime hq2).prod
            (encIssueRequest_opening_polyTime hq2)))))
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
    have hq1 : ComputableInPolyTime
        (fun q : (PIn × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) => q.1.1.1)
        (encPair (encPair encP encWordRequest) encSpendRequest) encParamInput :=
      (ComputableInPolyTime.fst _ _).fst'.fst'
    have hspk : ComputableInPolyTime
        (fun q : (PIn × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) => q.1.1.2)
        (encPair (encPair encP encWordRequest) encSpendRequest) encBits :=
      (ComputableInPolyTime.fst _ _).fst'.snd'
    have hq2 := ComputableInPolyTime.snd (encPair encP encWordRequest) encSpendRequest
    have hcom1 := hcom.comp (hq1.prod
      ((encSpendRequest_nullifier_polyTime hq2).prod
        ((encSpendRequest_ctx_polyTime hq2).prod
          ((encSpendRequest_oldCredit_polyTime hq2).prod
            (encSpendRequest_oldOpening_polyTime hq2)))))
    have ht1 := htag.comp (hcom1.prod (encSpendRequest_oldRefund_polyTime hq2))
    have hv := S.computableInPolyTime_verify_comp hspk ht1 (encSpendRequest_signature_polyTime hq2)
    have hcom2 := hcom.comp (hq1.prod
      ((encSpendRequest_newNullifier_polyTime hq2).prod
        ((encSpendRequest_ctx_polyTime hq2).prod
          ((encSpendRequest_newCredit_polyTime hq2).prod
            (encSpendRequest_newOpening_polyTime hq2)))))
    have hc2 := ComputableInPolyTime.decide_eq' hcom2
      (encSpendRequest_changeCommitment_polyTime hq2)
    have hadd1 := ComputableInPolyTime.binary_add'
      (encSpendRequest_oldCredit_polyTime hq2) (encSpendRequest_oldRefund_polyTime hq2)
    have hadd2 := ComputableInPolyTime.binary_add'
      (encSpendRequest_newCredit_polyTime hq2) (encSpendRequest_debit_polyTime hq2)
    have hbal := ComputableInPolyTime.decide_eq' hadd1 hadd2
    have hand : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
        (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _
    exact hand.comp ((hand.comp (hv.prod hc2)).prod hbal)
  dsimp only [encP] at his hsp
  exact computableInPolyTime_requestElim
    (fun q : (PIn × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) =>
      fun i : IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
        decide (com q.1.1.1 q.1.1.2 i.nullifier i.ctx i.amount i.opening = i.commitment))
    (fun q : (PIn × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) =>
      fun s : SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        S.verify q.1.2
            (tag (com q.1.1.1 q.1.1.2 s.nullifier s.ctx s.oldCredit s.oldOpening) s.oldRefund)
            s.signature &&
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
  have hl : ComputableInPolyTime
      (fun _ : (ETy × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) => false)
      (encPair encQ encIssueRequest) encBool := ComputableInPolyTime.const false
  have hr : ComputableInPolyTime
      (fun q : (ETy × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        decide (q.2.ctx = q.1.1.2.1 ∧ q.2.nullifier = q.1.1.2.2))
      (encPair encQ encSpendRequest) encBool := by
    have hctx1 := encSpendRequest_ctx_polyTime (ComputableInPolyTime.snd encQ encSpendRequest)
    have hnf1 := encSpendRequest_nullifier_polyTime
      (ComputableInPolyTime.snd encQ encSpendRequest)
    have hpair : ComputableInPolyTime
        (fun q : (ETy × Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
          q.1.1.2)
        (encPair encQ encSpendRequest) encWordPair :=
      (ComputableInPolyTime.fst _ _).fst'.snd'
    have hand : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
        (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _
    exact (hand.comp
      ((ComputableInPolyTime.decide_eq' hctx1 hpair.fst').prod
        (ComputableInPolyTime.decide_eq' hnf1 hpair.snd'))).of_enc_eq
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
      (by dsimp only [encQ] at hl; exact hl)
      (by dsimp only [encQ] at hr; exact hr)
      fun q => by cases q.2 <;> rfl
  refine (ComputableInPolyTime.anyWithInput (encA := encWordRequest) hlist htest).of_enc_eq
    fun p => congrArg encBool ?_
  simp only [hasSpentNullifier]
  congr 1
  funext r
  cases r <;> rfl

private theorem computableInPolyTime_acceptRequest
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (List Bool × List Bool × ℕ × List Bool) =>
        com p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
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
  have hl : ComputableInPolyTime
      (fun q : ETy × IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
        acceptLocal (com q.1.1.1.1 q.1.1.1.2) Prod.mk (pairScheme S tag q.1.1.1.1) q.1.1.2
          (.issue q.2))
      (encPair encE encIssueRequest) encBool := by
    have hin : ComputableInPolyTime
        (fun q : ETy × IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
          (q.1.1, Request.issue q.2))
        (encPair encE encIssueRequest) (encPair (encPair encParamInput encBits) encWordRequest) :=
      (hparam.comp (ComputableInPolyTime.fst _ _)).prod
        ((ComputableInPolyTime.of_eq (f := requestEquiv.symm) (encOut := encWordRequest)
          fun s => by cases s <;> rfl).comp
          ((ComputableInPolyTime.sumInl encIssueRequest encSpendRequest).comp
            (ComputableInPolyTime.snd _ _)))
    exact (computableInPolyTime_acceptLocal com hcom tag htag S).comp hin
  have hr : ComputableInPolyTime
      (fun q : ETy × SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        acceptLocal (com q.1.1.1.1 q.1.1.1.2) Prod.mk (pairScheme S tag q.1.1.1.1) q.1.1.2
          (.spend q.2) &&
          !hasSpentNullifier q.1.2.1 q.2.ctx q.2.nullifier)
      (encPair encE encSpendRequest) encBool := by
    have hin : ComputableInPolyTime
        (fun q : ETy × SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
          (q.1.1, Request.spend q.2))
        (encPair encE encSpendRequest) (encPair (encPair encParamInput encBits) encWordRequest) :=
      (hparam.comp (ComputableInPolyTime.fst _ _)).prod
        ((ComputableInPolyTime.of_eq (f := requestEquiv.symm) (encOut := encWordRequest)
          fun s => by cases s <;> rfl).comp
          ((ComputableInPolyTime.sumInr encIssueRequest encSpendRequest).comp
            (ComputableInPolyTime.snd _ _)))
    have hl' := (computableInPolyTime_acceptLocal com hcom tag htag S).comp hin
    have hs := computableInPolyTime_hasSpentNullifier.comp
      ((hlog.comp (ComputableInPolyTime.fst _ _)).prod
        ((encSpendRequest_ctx_polyTime (ComputableInPolyTime.snd _ _)).prod
          (encSpendRequest_nullifier_polyTime (ComputableInPolyTime.snd _ _))))
    have hnot : ComputableInPolyTime (fun b : Bool => !b) encBool encBool :=
      ComputableInPolyTime.of_finite _
    have hand : ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2)
        (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _
    exact hand.comp (hl'.prod (hnot.comp hs))
  dsimp only [encE] at hl hr
  exact computableInPolyTime_requestElim
    (fun q i =>
      acceptLocal (com q.1.1.1 q.1.1.2) Prod.mk (pairScheme S tag q.1.1.1) q.1.2 (.issue i))
    (fun q s =>
      acceptLocal (com q.1.1.1 q.1.1.2) Prod.mk (pairScheme S tag q.1.1.1) q.1.2 (.spend s) &&
        !hasSpentNullifier q.2.1 s.ctx s.nullifier)
    hreq hl hr fun p => by cases p.2.2 <;> rfl

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
  let encP := encPair encRequestLog encWordRequest
  have hlTest : ComputableInPolyTime
      (fun _ : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) => false)
      (encPair encP encIssueRequest) encBool := ComputableInPolyTime.const false
  have hrTest : ComputableInPolyTime
      (fun q : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        !decide (q.2.inputNote ∈ q.1.1.map fun r => r.outputPayload.message))
      (encPair encP encSpendRequest) encBool := by
    have hnote : ComputableInPolyTime
        (fun q : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
          q.2.inputNote)
        (encPair encP encSpendRequest) encCreditNote := by
      dsimp only [SpendRequest.inputNote]
      fun_prop
    have hc := hcert.comp (ComputableInPolyTime.fst encP encSpendRequest |>.fst')
    have hmem := ComputableInPolyTime.decide_mem hc hnote
    exact (ComputableInPolyTime.of_finite (fun b : Bool => !b)).comp hmem
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
      (ComputableInPolyTime.snd encRequestLog encWordRequest)
      (by dsimp only [encP] at hlTest; exact hlTest)
      (by dsimp only [encP] at hrTest; exact hrTest)
      fun p => by cases p.2 <;> rfl
  have hfind := ComputableInPolyTime.findWithInput
    (encA := encWordRequest) (ComputableInPolyTime.id' (encIn := encRequestLog)) htest
  have hlBody : ComputableInPolyTime
      (fun _ : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          IssueRequest (List Bool) (List Bool) (List Bool) (List Bool) =>
        (none : Option (Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool))))
      (encPair encP encIssueRequest) (encOption encNoteToken) :=
    ComputableInPolyTime.const none
  have hrBody : ComputableInPolyTime
      (fun q : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
          SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
        some (⟨q.2.inputPayload, q.2.signature⟩ :
          Token (Credit.Note (List Bool) (List Bool)) (List Bool) (List Bool)))
      (encPair encP encSpendRequest) (encOption encNoteToken) := by
    have hnote : ComputableInPolyTime
        (fun q : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
          q.2.inputNote)
        (encPair encP encSpendRequest) encCreditNote := by
      dsimp only [SpendRequest.inputNote]
      fun_prop
    have hop := encSpendRequest_oldOpening_polyTime (ComputableInPolyTime.snd encP encSpendRequest)
    have hpay : ComputableInPolyTime
        (fun q : (List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) ×
            SpendRequest (List Bool) (List Bool) (List Bool) (List Bool) (List Bool) =>
          q.2.inputPayload)
        (encPair encP encSpendRequest) encNotePayload := by
      dsimp only [SpendRequest.inputPayload]
      exact encPayloadOf_mk_polyTime encCreditNote hnote hop
    have hsig := encSpendRequest_signature_polyTime (ComputableInPolyTime.snd encP encSpendRequest)
    have htok := encTokenOf_mk_polyTime encCreditNote hpay hsig
    exact (ComputableInPolyTime.optionSome encNoteToken).comp htok
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
      (ComputableInPolyTime.snd encRequestLog encWordRequest)
      (by dsimp only [encP] at hlBody; exact hlBody)
      (by dsimp only [encP] at hrBody; exact hrBody)
      fun q => by cases q.2 <;> rfl
  have helim := ComputableInPolyTime.optionElimWithInput (body := bodyForged) hfind
    (ComputableInPolyTime.const none) hbody
  refine helim.of_enc_eq fun reqs => congrArg (encOption encNoteToken) ?_
  rw [findNoteForgery, findNoteForgery_eq_find]

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
      (fun p : (ℕ × List Bool) × (List Bool × List Bool × ℕ × List Bool) =>
        com p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
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
  have hn : ComputableInPolyTime (fun p : CallTy => p.1.1) encRequestCall encUnary :=
    (ComputableInPolyTime.fst _ _).fst'
  have hkeys : ComputableInPolyTime (fun p : CallTy => wordPairDecoder.decode p.1.2)
      encRequestCall encWordPair :=
    wordPairDecoder.computableInPolyTime.comp (ComputableInPolyTime.fst _ _).snd'
  have hparam : ComputableInPolyTime
      (fun p : CallTy => (p.1.1, (wordPairDecoder.decode p.1.2).2))
      encRequestCall encParamInput := hn.prod hkeys.snd'
  have hdecReq : ComputableInPolyTime (fun p : CallTy => wordRequestDecoder.decode p.2.1.2)
      encRequestCall encWordRequest :=
    wordRequestDecoder.computableInPolyTime.comp (ComputableInPolyTime.snd _ _).fst'.snd'
  have hacc : ComputableInPolyTime
      (fun p : CallTy => p.2.2) encRequestCall encRequestLog :=
    (ComputableInPolyTime.snd _ _).snd'
  have hcond : ComputableInPolyTime
      (fun p : CallTy =>
        let keys := wordPairDecoder.decode p.1.2
        acceptRequest (com p.1.1 keys.2) Prod.mk (pairScheme S tag p.1.1) keys.1 p.2.2
          (wordRequestDecoder.decode p.2.1.2))
      encRequestCall encBool :=
    (computableInPolyTime_acceptRequest com hcom tag htag S).comp
      ((hparam.prod hkeys.fst').prod (hacc.prod hdecReq))
  have hout : ComputableInPolyTime
      (fun p : CallTy => (wordRequestDecoder.decode p.2.1.2).outputPayload)
      encRequestCall encNotePayload :=
    computableInPolyTime_requestOutputPayload.comp hdecReq
  have hreq : ComputableInPolyTime
      (fun p : CallTy => encNotePayload (wordRequestDecoder.decode p.2.1.2).outputPayload)
      encRequestCall encBits :=
    (ComputableInPolyTime.of_eq (f := encNotePayload) (encOut := encBits) fun _ => rfl).comp hout
  have hnote : ComputableInPolyTime
      (fun p : CallTy => (wordRequestDecoder.decode p.2.1.2).outputPayload.message)
      encRequestCall encCreditNote :=
    encPayloadOf_message_polyTime encCreditNote hout
  have hop : ComputableInPolyTime
      (fun p : CallTy => (wordRequestDecoder.decode p.2.1.2).outputPayload.opening)
      encRequestCall encBits :=
    encPayloadOf_opening_polyTime encCreditNote hout
  have htgt : ComputableInPolyTime
      (fun p : CallTy =>
        let ck := (wordPairDecoder.decode p.1.2).2
        let out := (wordRequestDecoder.decode p.2.1.2).outputPayload
        tag (com p.1.1 ck out.message.nullifier out.message.context out.message.credit out.opening)
          out.message.refund)
      encRequestCall encBits := by
    have hcom_out := hcom.comp (hparam.prod
      ((encCreditNote_nullifier_polyTime hnote).prod
        ((encCreditNote_context_polyTime hnote).prod
          ((encCreditNote_credit_polyTime hnote).prod hop))))
    exact htag.comp (hcom_out.prod (encCreditNote_refund_polyTime hnote))
  have hlim : ComputableInPolyTime
      (fun p : CallTy =>
        let ck := (wordPairDecoder.decode p.1.2).2
        let out := (wordRequestDecoder.decode p.2.1.2).outputPayload
        sigBound p.1.1
          (tag (com p.1.1 ck out.message.nullifier out.message.context out.message.credit
            out.opening) out.message.refund).length)
      encRequestCall encUnary :=
    hsigBound.comp (hn.prod (ComputableInPolyTime.length_bits.comp htgt))
  have hq : IsOraclePPTOn encRequestCall encBits
      (fun p : CallTy =>
        let ck := (wordPairDecoder.decode p.1.2).2
        let out := (wordRequestDecoder.decode p.2.1.2).outputPayload
        let tgt := tag (com p.1.1 ck out.message.nullifier out.message.context
          out.message.credit out.opening) out.message.refund
        List.take (sigBound p.1.1 tgt.length) <$> ProbOracleComp.query ((), encNotePayload out)) :=
    IsOraclePPTOn.query_take () hreq hlim
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
  have hnone : ComputableInPolyTime
      (fun p : CallTy => (encOption encBits none, p.2.2)) encRequestCall encRequestReply :=
    (ComputableInPolyTime.const (encOption encBits none)).prod hacc
  simpa only [bind_pure_comp] using
    IsOraclePPTOn.cond hcond (hq.map_with hpost) hnone.isOraclePPTOn

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
    have hlen : (encRequestLog (accepted ++ [wordRequestDecoder.decode req.2])).length =
        (encRequestLog accepted).length +
          (2 * (encWordRequest (wordRequestDecoder.decode req.2)).length + 1) := by
      simp [encRequestLog, encList_append, encList_cons, encList_nil, length_frame]
    have hd := hdecBound req.2
    have hBw : req.2.length ≤ (encPair encParamInput encBits (caller, req.2)).length := by
      enc_len
    have hd' : (encWordRequest (wordRequestDecoder.decode req.2)).length ≤
        dc * ((encPair encParamInput encBits (caller, req.2)).length + 1) ^ dd :=
      hd.trans (Nat.mul_le_mul_left dc (Nat.pow_le_pow_left (by omega) dd))
    rw [hlen]
    omega
  · simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff] at hres
    subst hres
    exact Nat.le_add_right _ _

private theorem isOraclePPTOn_noteForgerRun {sigBound : ℕ → ℕ → ℕ}
    (hsigBound : ComputableInPolyTime (fun p : ℕ × ℕ => sigBound p.1 p.2) encNatPair encUnary)
    {com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool}
    (hcom : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (List Bool × List Bool × ℕ × List Bool) =>
        com p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
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
  have hdecBound' : ∀ w : List Bool, (encWordRequest (wordRequestDecoder.decode w)).length ≤
      dc * (w.length + 1) ^ dd := by
    intro w
    simpa only [encBits_apply] using hdecBound w
  have hpolyG : PolynomiallyBounded (fun B : ℕ => 2 * (dc * (B + 1) ^ dd) + 2) := by
    fun_prop
  have hgrowth : PolyBounded
      (fun pair : (ℕ × List Bool) × List Bool => (encPair encParamInput encBits pair).length)
      (fun ⟨c, w⟩ => 2 * (dc * ((encPair encParamInput encBits (c, w)).length + 1) ^ dd) + 2) :=
    PolyBounded.of_polynomiallyBounded_comp
      (p := fun B : ℕ => 2 * (dc * (B + 1) ^ dd) + 2) hpolyG
      (PolyBounded.self (size := fun pair => (encPair encParamInput encBits pair).length))
  have hprep : ComputableInPolyTime (fun p : ℕ × List Bool => (p.1, p.2))
      encParamInput (encPair encUnary encBits) := by
    fun_prop
  dsimp only [noteForgerRun]
  refine hA.run_interpret_preprocess_open_of_bounded_growth
    (input := encParamInput) (stateEncoding := encRequestLog)
    (operationEncoding := encFinEnum Unit)
    (handler := fun caller => noteForgerHandlerWord sigBound com tag S caller.1 caller.2)
    (prepare := fun p : ℕ × List Bool => (p.1, p.2))
    (initial := fun _ => [])
    (growth := fun c w =>
      2 * (dc * ((encPair encParamInput encBits (c, w)).length + 1) ^ dd) + 2)
    hprep hhandler (ComputableInPolyTime.const [])
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
      (fun p : (ℕ × List Bool) × (List Bool × List Bool × ℕ × List Bool) =>
        com p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      encComArgs encBits)
    {tag : List Bool → ℕ → List Bool}
    (htag : ComputableInPolyTime (fun p : List Bool × ℕ => tag p.1 p.2) encTagPair encBits)
    (S : WordSignatureScheme)
    {A : WordExtractedAdversary} (hA : IsOraclePPT encBits A) :
    IsOraclePPTOn encParamInput encNoteToken
      (fun p => noteForgerWord sigBound com tag S A p.1 p.2) := by
  have hinterp := isOraclePPTOn_noteForgerRun hsigBound hcom htag S hA
  have hfind : ComputableInPolyTime
      (fun st : List Bool ×
          List (Request (List Bool) (List Bool) (List Bool) (List Bool) (List Bool)) =>
        (findNoteForgery st.2).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩)
      (encPair encBits encRequestLog) encNoteToken :=
    ComputableInPolyTime.optionGetDWithInput
      (computableInPolyTime_findNoteForgery.comp (ComputableInPolyTime.snd _ _))
      (ComputableInPolyTime.const _)
  simpa only [noteForgerWord] using hinterp.map hfind

private theorem eval_runExtracted_noteForgerWord_inner (S : WordSignatureScheme)
    (sigBound : ℕ → ℕ → ℕ)
    (com : ℕ → List Bool → List Bool → List Bool → ℕ → List Bool → List Bool)
    (tag : List Bool → ℕ → List Bool)
    (A : WordExtractedAdversary) (n : ℕ) (ck pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (S.sign sk msg)).support →
      sig.length ≤ sigBound n msg.length)
    (log₀ : List (Payload (Credit.Note (List Bool) (List Bool)) (List Bool) × List Bool)) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (fun req acc =>
          let payload := notePayloadDecoder.decode req.2
          let msg := tag (com n ck payload.message.nullifier payload.message.context
            payload.message.credit payload.opening) payload.message.refund
          (fun sig => (sig, acc ++ [(payload, sig)])) <$> S.sign sk msg))
      (noteForgerWord sigBound com tag S A n (encWordPair (pk, ck)))).run log₀) =
      ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          (fun msg acc =>
            (fun sig => (sig, acc ++ [(msg, sig)])) <$>
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
          ((ProbComp.eval (S.sign sk msg)).map fun sig => (sig, acc ++ [(payload, sig)])))
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (noteForgerHandlerWord sigBound com tag S n (encWordPair (pk, ck))))
          (A n (encWordPair (pk, ck)))).run []) log₀ =
      ProbOracleComp.runWith
        (fun msg acc =>
          (ProbComp.eval ((pairScheme S tag n).sign sk (Credit.target (com n ck) Prod.mk
            msg.message msg.opening))).map fun sig => (sig, acc ++ [(msg, sig)]))
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
  have hinner' := congrArg (PMF.map fun ⟨⟨_, accepted⟩, log⟩ =>
      ((findNoteForgery accepted).getD ⟨⟨⟨default, default, 0, 0⟩, default⟩, default⟩, log))
    hinner
  simpa only [ProbComp.eval_map, PMF.map, Function.comp_def, Prod.map, id_eq] using hinner'

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
  exact eval_runExtracted_noteForgerWord_inner S sigBound com tag A n ck pk sk
    (hbound n pk sk hkeys) []

end Conservation

end Cslib.Crypto.AnonymousToken

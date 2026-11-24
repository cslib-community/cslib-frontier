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
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.Signature.Bridge
public import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
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
abbrev encTargetArgs : (ℕ × (List Bool × (List Bool × List Bool))) ↪ List Bool :=
  encPair encUnary encKeyedWordPair

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

/-- Word-level target-forgery reduction corresponding to `targetForger`: runs `A` on
`encWordPair (spk, ck)`, decodes each payload query with `wordPayloadDecoder`, forwards
`target n ck payload.message payload.opening` to the signing oracle with reply truncation
`sigBound`, and outputs `(target n ck tok.payload.message tok.payload.opening, tok.signature)`. -/
def targetForgerWord (sigBound : ℕ → ℕ → ℕ)
    (target : ℕ → List Bool → List Bool → List Bool → List Bool)
    (A : WordExtractedForgerOf (List Bool))
    (n : ℕ) (keys : List Bool × List Bool) : WordOracleComp Unit (List Bool × List Bool) := do
  let (spk, ck) := keys
  let tok ← OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request : Unit × List Bool =>
        let payload := wordPayloadDecoder.decode request.2
        let msg := target n ck payload.message payload.opening
        List.take (sigBound n msg.length) <$> ProbOracleComp.query ((), msg)))
    (A n (encWordPair (spk, ck)))
  return (target n ck tok.payload.message tok.payload.opening, tok.signature)

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
      (fun p => targetForgerWord sigBound target A p.1 p.2) := by
  have hdec : ComputableInPolyTime wordPayloadDecoder.decode encBits encWordPayload :=
    wordPayloadDecoder.computableInPolyTime
  let callIn := encPair encPublicInput (encPair (encFinEnum Unit) encBits)
  have hprep : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => (p.1, encWordPair p.2))
      encPublicInput (encPair encUnary encBits) := by
    unfold encPublicInput encWordPair
    fun_prop
  have hreq : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
        target p.1.1 p.1.2.2 (wordPayloadDecoder.decode p.2.2).message
          (wordPayloadDecoder.decode p.2.2).opening)
      callIn encBits := by
    have hp : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
          wordPayloadDecoder.decode p.2.2) callIn encWordPayload := by
      dsimp only [callIn, encPublicInput, encWordPair]
      fun_prop
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
      ((encPayloadOf_message_polyTime encBits hp).prod
        (encPayloadOf_opening_polyTime encBits hp))))
  have hlim : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
        sigBound p.1.1 (target p.1.1 p.1.2.2 (wordPayloadDecoder.decode p.2.2).message
          (wordPayloadDecoder.decode p.2.2).opening).length)
      callIn encUnary := by
    have hn : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool => p.1.1)
        callIn encUnary := by
      dsimp only [callIn, encPublicInput, encWordPair]
      fun_prop
    exact hsigBound.comp (hn.prod (ComputableInPolyTime.length_bits.comp hreq))
  have hres : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × List Bool =>
        sigBound p.1.1 (target p.1.1 p.1.2.2 (wordPayloadDecoder.decode p.2).message
          (wordPayloadDecoder.decode p.2).opening).length)
      (encPair encPublicInput encBits) encUnary := by
    let E := encPair encPublicInput encBits
    have hpe : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => wordPayloadDecoder.decode p.2)
        E encWordPayload := by
      dsimp only [E, encPublicInput, encWordPair]
      fun_prop
    have hn : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => p.1.1) E encUnary := by
      dsimp only [E, encPublicInput, encWordPair]
      fun_prop
    have hck : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => p.1.2.2) E encBits := by
      dsimp only [E, encPublicInput, encWordPair]
      fun_prop
    have hm := htarget.comp (hn.prod (hck.prod
      ((encPayloadOf_message_polyTime encBits hpe).prod
        (encPayloadOf_opening_polyTime encBits hpe))))
    exact hsigBound.comp (hn.prod (ComputableInPolyTime.length_bits.comp hm))
  have hhandler : IsOraclePPTOn callIn encBits
      (fun p : (ℕ × List Bool × List Bool) × Unit × List Bool =>
        let payload := wordPayloadDecoder.decode p.2.2
        let msg := target p.1.1 p.1.2.2 payload.message payload.opening
        List.take (sigBound p.1.1 msg.length) <$> ProbOracleComp.query ((), msg)) :=
    IsOraclePPTOn.query_take () hreq hlim
  have hinterp := hA.on.interpret_preprocess_open'
    (operationEncoding := encFinEnum Unit)
    (handler := fun (p : ℕ × List Bool × List Bool) (request : Unit × List Bool) =>
      let payload := wordPayloadDecoder.decode request.2
      let msg := target p.1 p.2.2 payload.message payload.opening
      List.take (sigBound p.1 msg.length) <$> ProbOracleComp.query ((), msg))
    (prepare := fun p : ℕ × List Bool × List Bool => (p.1, encWordPair p.2))
    (resources := fun p w =>
      let payload := wordPayloadDecoder.decode w
      sigBound p.1 (target p.1 p.2.2 payload.message payload.opening).length)
    hprep hhandler hres fun p request reply hreply => by
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact List.length_take_le _ _
  have hpost : ComputableInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × Token (List Bool) (List Bool) (List Bool) =>
        (target p.1.1 p.1.2.2 p.2.payload.message p.2.payload.opening, p.2.signature))
      (encPair encPublicInput encWordToken) encWordPair := by
    have hn : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token (List Bool) (List Bool) (List Bool) =>
          p.1.1) (encPair encPublicInput encWordToken) encUnary := by
      dsimp only [encPublicInput, encWordPair, encWordToken]
      fun_prop
    have hck : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token (List Bool) (List Bool) (List Bool) =>
          p.1.2.2) (encPair encPublicInput encWordToken) encBits := by
      dsimp only [encPublicInput, encWordPair, encWordToken]
      fun_prop
    have hpay : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token (List Bool) (List Bool) (List Bool) =>
          p.2.payload) (encPair encPublicInput encWordToken) encWordPayload := by
      dsimp only [encPublicInput, encWordPair, encWordToken, encWordPayload]
      fun_prop
    have hsig : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × Token (List Bool) (List Bool) (List Bool) =>
          p.2.signature) (encPair encPublicInput encWordToken) encBits := by
      dsimp only [encPublicInput, encWordPair, encWordToken]
      fun_prop
    have ht := htarget.comp (hn.prod (hck.prod
      ((encPayloadOf_message_polyTime encBits hpay).prod
        (encPayloadOf_opening_polyTime encBits hpay))))
    exact ht.prod hsig
  simpa only [targetForgerWord, bind_pure_comp] using
    hinterp.map_with (f := fun p tok =>
      (target p.1 p.2.2 tok.payload.message tok.payload.opening, tok.signature)) hpost

/-- Running a word-level forger with `sigBound`-truncation against `SignatureScheme.signingOracleOf`
gives the same `(output, targetLog)` law as running `WordExtractedForgerOf.toTyped` under
`targetForger` and `runState`. -/
private theorem eval_signingOracle_take_eq_targetForger_runLog {α : Type}
    (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool)
    (target : List Bool → List Bool → List Bool) (sigBound : ℕ → ℕ)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (sign sk msg)).support →
      sig.length ≤ sigBound msg.length)
    (prog : WordOracleComp Unit α) (queried : List (List Bool))
    (log : List (List Bool × List Bool))
    (hlog : (log.map Prod.fst).reverse = queried) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (SignatureScheme.signingOracleOf sign sk))
      (OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
          (fun req : Unit × List Bool =>
            let payload := wordPayloadDecoder.decode req.2
            let msg := target payload.message payload.opening
            List.take (sigBound msg.length) <$>
              ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool) ((), msg)))
        prog)).run queried) =
      (ProbComp.eval ((ProbOracleComp.simulate
        (fun payload => ProbOracleComp.query (target payload.message payload.opening))
        (ProbOracleComp.simulate
          (fun req : Unit × List Bool => ProbOracleComp.query (wordPayloadDecoder.decode req.2))
          prog)).runState
        (fun msg acc => (fun sig => (sig, acc ++ [(msg, sig)])) <$> sign sk msg) |>.run log)).map
        fun ⟨res, acc⟩ => (res, (acc.map Prod.fst).reverse) := by
  subst hlog
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runWith_interpret_sumHandler]
  rw [ProbOracleComp.eval_runState]
  have hsim : ∀ (prog' : WordOracleComp Unit α),
      ProbOracleComp.simulate
        (fun payload => ProbOracleComp.query (target payload.message payload.opening))
        (ProbOracleComp.simulate
          (fun req : Unit × List Bool => ProbOracleComp.query (wordPayloadDecoder.decode req.2))
          prog') =
        OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
            (fun req : Unit × List Bool =>
              let payload := wordPayloadDecoder.decode req.2
              ProbOracleComp.query (spec := fun _ : List Bool => List Bool)
                (target payload.message payload.opening)))
          prog' := by
    intro prog'
    rw [ProbOracleComp.simulate, OracleComp.substitute_eq_interpret,
      ProbOracleComp.interpret_simulate]
    simp only [ProbOracleComp.interpret_query]
  rw [hsim, ProbOracleComp.runWith_interpret_sumHandler]
  symm
  refine ProbOracleComp.runWith_map_state _ _ (fun acc => (acc.map Prod.fst).reverse)
    (fun req acc => ?_) prog log
  dsimp only
  simp only [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    SignatureScheme.signingOracleOf, SignatureScheme.signingOracleOn, ↓reduceIte,
    ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, pmf_norm, PMF.map,
    Function.comp_def]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
  have htake : List.take (sigBound
      (target (wordPayloadDecoder.decode req.2).message
        (wordPayloadDecoder.decode req.2).opening).length) sig = sig :=
    List.take_of_length_le (hbound _ sig hsig)
  simp [htake, List.map_append, List.reverse_append]

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
  simp only [targetForgerWord, targetForger, WordExtractedForgerOf.toTyped,
    WordExtractedForgerOf.atKey, ProbOracleComp.runLog, bind_pure_comp, OracleComp.interpret_map,
    StateT.run_map, ProbComp.eval_map, ProbOracleComp.runState_map]
  change (PMF.map _ (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (SignatureScheme.signingOracleOf S.sign sk)) _).run []))).bind _ = _
  rw [eval_signingOracle_take_eq_targetForger_runLog S.sign sk (target n ck) (sigBound n)
    (hbound n pk sk hkeys) (A n (encWordPair (pk, ck))) [] [] rfl]
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
      (encPair encUnary (encPair encBits (encPair encM encBits))) encBits)
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
      (encPair encUnary (encPair encBits (encPair encM encBits))) encBits)
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
      (encPair encUnary (encPair encBits (encPair encM encBits))) encBits) :
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
      (encPair encUnary (encPair encBits (encPair encM encBits))) encBits)
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

end Cslib.Crypto.AnonymousToken

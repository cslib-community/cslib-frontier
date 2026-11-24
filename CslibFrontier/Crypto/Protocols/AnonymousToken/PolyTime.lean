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
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Oracle.SubstitutionGrowth
import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
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

/-- Encoding of `(n, (spk, ck))` supplied to parameterized anonymous-token reductions. -/
abbrev encPublicInput : (ℕ × (List Bool × List Bool)) ↪ List Bool :=
  encPair encUnary encWordPair

/-- Encoding of `(n, L)` supplied to signature-length bounds. -/
abbrev encNatPair : (ℕ × ℕ) ↪ List Bool := encPair encUnary encUnary

/-- Encoding of `(n, (ck, (msg, opening)))` supplied to keyed target encoders. -/
abbrev encTargetArgs : (ℕ × (List Bool × (List Bool × List Bool))) ↪ List Bool :=
  encPair encUnary (encPair encBits encWordPair)

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

end Cslib.Crypto.AnonymousToken

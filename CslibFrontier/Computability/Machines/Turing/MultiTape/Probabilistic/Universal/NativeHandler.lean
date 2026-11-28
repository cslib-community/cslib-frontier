/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Interpreter.Native
public import CslibFrontier.Languages.Probabilistic.Oracle.RunState
import CslibFrontier.Foundations.Control.Monad.StateT

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.BitString

import CslibFrontier.Languages.Probabilistic.Iteration.Reachable

/-!
# Retained stateful handlers for native universal queries

This module supplies the executable query seam needed to close a retained fixed-channel universal
interpreter against a local stateful handler. The source operation, request and suspended
configuration remain typed data. An actual supplied `NativeOracleProgram` executes the handler;
the retained continuation decodes the reply, updates the source configuration and returns the new
handler state.

The construction does not hide the handler behind a semantic callback. Its final witness contains
the composed finite-control machine, state encoding, phase accounting and generated description.
A handler with no external channels specializes the branch to a closed `MultiTapePTM` fragment.

The locally installed handler receives the selected operation, the encoded request and its
private state. Its retained compiler emits a raw reply and the next private state. The controller
copies the specified raw prefix, decodes it and updates the source and handler state together.
The finite-state instance constructs the loop and output bounds by enumerating reachable
prefixes. The handler supplies its own native artifact and a clock bound for reply installation
on supported outputs.

* `run_handlerRunProgram_eq_runState` gives the source output together with the final handler
  state, including rejection of malformed operation counts.
* `runWith_artifact_machine` identifies the output distribution of the closed clocked machine.
* `time_queryBranch`, `time_handlerLoopArtifact` and `time_artifact` account for the installed
  query, the additional stopping round and the output copy. The deterministic raw-prefix
  compiler also bounds its time and workspace by the raw length and requested count. Whole-run
  independent workspace, an online polynomial clock and a concrete production handler remain open.

## References

The retained handler installation and its resource accounting are original to this module.
-/

public section

namespace Turing.MultiTapePTM.Universal.NativeHandler

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM
  Turing.MultiTapeTM.Internal Turing.MultiTapePTM.Internal
open Turing.MultiTapePTM.Universal
open Turing.MultiTapePTM.Universal.NativeInterpreter

variable {HandlerState α : Type} {r external : ℕ} {encHandlerState : HandlerState ↪ List Bool}

/-! ### Typed handler boundary -/

/-- A local stateful-handler call. -/
structure HandlerCall (r : ℕ) (HandlerState : Type) where
  /-- Source operation requested from the handler. -/
  operation : Fin r
  /-- Boolean request word supplied to the handler. -/
  request : List Bool
  /-- Current private handler state. -/
  state : HandlerState

/-- Encode operation, request and state in that order. -/
enc_structure eHandlerCall (r : ℕ) (encHandlerState : HandlerState ↪ List Bool) :
    HandlerCall r HandlerState where
  operation : (eOperation r), request : encBits, state : encHandlerState

/-- A local handler's raw reply and updated private state. -/
structure HandlerResult (HandlerState : Type) where
  /-- Raw Boolean reply word. -/
  reply : List Bool
  /-- Updated private handler state. -/
  state : HandlerState

/-- Encode reply then updated handler state. -/
enc_structure eHandlerResult (encHandlerState : HandlerState ↪ List Bool) :
    HandlerResult HandlerState where
  reply : encBits, state : encHandlerState

/-- One validated source query together with the private state of the installed handler. -/
structure QueryInput (r : ℕ) (HandlerState : Type) where
  /-- Suspended source interpreter state. -/
  source : NativeInterpreter.LoopState
  /-- Requested source operation. -/
  operation : Fin r
  /-- Unary source request. -/
  request : List ℕ
  /-- Source continuation tag. -/
  next : ℕ
  /-- Suspended source configuration. -/
  pending : ICfg
  /-- Current private handler state. -/
  handlerState : HandlerState

/-- Encode source, operation, request, continuation, configuration and handler state in order. -/
enc_structure eQueryInput (r : ℕ) (encHandlerState : HandlerState ↪ List Bool) :
    QueryInput r HandlerState where
  source : eLoopState, operation : (eOperation r), request : (encList encUnary),
  next : encUnary, pending : eICfg, handlerState : encHandlerState

/-- State retained after one installed source query. -/
structure RetainedState (HandlerState : Type) where
  /-- Updated source interpreter state. -/
  source : NativeInterpreter.LoopState
  /-- Updated private handler state. -/
  handlerState : HandlerState
deriving Inhabited

/-- Encode the source state then the handler state. -/
enc_structure eRetainedState (encHandlerState : HandlerState ↪ List Bool) :
    RetainedState HandlerState where
  source : eLoopState, handlerState : encHandlerState

/-- The updated source loop state and installed-handler state, wrapped in the nonempty option used
by the outer retained loop. -/
abbrev QueryResult (HandlerState : Type) :=
  Option (RetainedState HandlerState)

/-- Encoding of the complete result of one installed source query. -/
abbrev eQueryResult (encHandlerState : HandlerState ↪ List Bool) :
    QueryResult HandlerState ↪ List Bool :=
  encOption (eRetainedState encHandlerState)

/-- Marshal the typed source request into the Boolean word consumed by a local handler. -/
@[expose] def handlerCall (input : QueryInput r HandlerState) : HandlerCall r HandlerState :=
  { operation := input.operation
    request := encList encUnary input.request
    state := input.handlerState }

/-- Copy the permitted raw handler-reply prefix, decode it and install it in the suspended source
configuration. This is definitionally the same order as the open interpreter: raw-bit prefix
first, unary-frame decoding second, and source-fuel truncation last. -/
def installReply (input : QueryInput r HandlerState)
    (result : HandlerResult HandlerState) : QueryResult HandlerState :=
  let reply := result.reply.take input.source.replyBits
  let decoded := (frames reply).map List.length |>.take input.source.fuel
  let next := input.pending.receive input.operation input.next decoded
  some { source := advance input.source next, handlerState := result.state }

/-- The exact stateful semantics executed by the retained query branch. -/
noncomputable def queryProgram
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState))
    (input : QueryInput r HandlerState) :
    WordOracleComp (Fin external) (QueryResult HandlerState) :=
  NativeOracleProgram.capturedProgram
    (fun query => handler (handlerCall query))
    (fun postInput => pure (installReply postInput.1 postInput.2)) input

/-! ### Retained marshalling -/

private abbrev QueryTail₁ (r : ℕ) (HandlerState : Type) :=
  Fin r × (List ℕ × (ℕ × (ICfg × HandlerState)))
private abbrev QueryTail₂ (HandlerState : Type) :=
  List ℕ × (ℕ × (ICfg × HandlerState))
private abbrev QueryTail₃ (HandlerState : Type) := ℕ × (ICfg × HandlerState)
private abbrev QueryTail₄ (HandlerState : Type) := ICfg × HandlerState

private def eQueryTail₁ (r : ℕ) (encHandlerState : HandlerState ↪ List Bool) :
    QueryTail₁ r HandlerState ↪ List Bool :=
  encPair (eOperation r)
    (encPair (encList encUnary) (encPair encUnary (encPair eICfg encHandlerState)))
private def eQueryTail₂ (encHandlerState : HandlerState ↪ List Bool) :
    QueryTail₂ HandlerState ↪ List Bool :=
  encPair (encList encUnary) (encPair encUnary (encPair eICfg encHandlerState))
private def eQueryTail₃ (encHandlerState : HandlerState ↪ List Bool) :
    QueryTail₃ HandlerState ↪ List Bool :=
  encPair encUnary (encPair eICfg encHandlerState)
private def eQueryTail₄ (encHandlerState : HandlerState ↪ List Bool) :
    QueryTail₄ HandlerState ↪ List Bool :=
  encPair eICfg encHandlerState

private def queryFields (input : QueryInput r HandlerState) :
    NativeInterpreter.LoopState × QueryTail₁ r HandlerState :=
  (input.source,
    (input.operation, (input.request, (input.next, (input.pending, input.handlerState)))))

private noncomputable def sourceCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState => input.source)
      (eQueryInput r encHandlerState) eLoopState :=
  (NativeCompiler.first eLoopState (eQueryTail₁ r encHandlerState)).ofInputEq
    queryFields fun _ => rfl

private noncomputable def tail₁Compiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState =>
      (input.operation, (input.request, (input.next, (input.pending, input.handlerState)))))
      (eQueryInput r encHandlerState) (eQueryTail₁ r encHandlerState) :=
  (NativeCompiler.second eLoopState (eQueryTail₁ r encHandlerState)).ofInputEq
    queryFields fun _ => rfl

private noncomputable def operationCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState => input.operation)
      (eQueryInput r encHandlerState) (eOperation r) :=
  (NativeCompiler.first (eOperation r) (eQueryTail₂ encHandlerState)).comp
    (tail₁Compiler r encHandlerState)

private noncomputable def tail₂Compiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState =>
      (input.request, (input.next, (input.pending, input.handlerState))))
      (eQueryInput r encHandlerState) (eQueryTail₂ encHandlerState) :=
  (NativeCompiler.second (eOperation r) (eQueryTail₂ encHandlerState)).comp
    (tail₁Compiler r encHandlerState)

private noncomputable def requestCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState => input.request)
      (eQueryInput r encHandlerState) (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) (eQueryTail₃ encHandlerState)).comp
    (tail₂Compiler r encHandlerState)

private noncomputable def tail₃Compiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState =>
      (input.next, (input.pending, input.handlerState)))
      (eQueryInput r encHandlerState) (eQueryTail₃ encHandlerState) :=
  (NativeCompiler.second (encList encUnary) (eQueryTail₃ encHandlerState)).comp
    (tail₂Compiler r encHandlerState)

private noncomputable def nextCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState => input.next)
      (eQueryInput r encHandlerState) encUnary :=
  (NativeCompiler.first encUnary (eQueryTail₄ encHandlerState)).comp
    (tail₃Compiler r encHandlerState)

private noncomputable def tail₄Compiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState =>
      (input.pending, input.handlerState))
      (eQueryInput r encHandlerState) (eQueryTail₄ encHandlerState) :=
  (NativeCompiler.second encUnary (eQueryTail₄ encHandlerState)).comp
    (tail₃Compiler r encHandlerState)

private noncomputable def pendingCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState => input.pending)
      (eQueryInput r encHandlerState) eICfg :=
  (NativeCompiler.first eICfg encHandlerState).comp (tail₄Compiler r encHandlerState)

private noncomputable def handlerStateCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : QueryInput r HandlerState => input.handlerState)
      (eQueryInput r encHandlerState) encHandlerState :=
  (NativeCompiler.second eICfg encHandlerState).comp (tail₄Compiler r encHandlerState)

private noncomputable def classifiedOfOutputEq {Alpha Beta Gamma : Type}
    {f : Alpha → Beta} {g : Alpha → Gamma}
    {encIn : Alpha ↪ List Bool} {encMid : Beta ↪ List Bool}
    {encOut : Gamma ↪ List Bool}
    (compiler : ClassifiedCompiler f encIn encMid)
    (henc : ∀ input, encOut (g input) = encMid (f input)) :
    ClassifiedCompiler g encIn encOut where
  compiler := compiler.compiler.ofOutputEq henc
  online := compiler.online
  time_eq := compiler.time_eq

/-- Retained operation/request/state marshalling for one local handler call. -/
private noncomputable def handlerCallCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    ClassifiedCompiler (handlerCall : QueryInput r HandlerState → HandlerCall r HandlerState)
      (eQueryInput r encHandlerState) (eHandlerCall r encHandlerState) := by
  let operation := ClassifiedCompiler.inPhase .tags
    (operationCompiler r encHandlerState)
  let request := ClassifiedCompiler.inPhase .marshalling
    ((requestCompiler r encHandlerState).ofOutputEq fun _ => rfl)
  let state := ClassifiedCompiler.inPhase .controller
    (handlerStateCompiler r encHandlerState)
  exact classifiedOfOutputEq (operation.pair (request.pair state)) fun _ => rfl

/-! ### Retained reply installation -/

private abbrev PostInput (r : ℕ) (HandlerState : Type) :=
  QueryInput r HandlerState × HandlerResult HandlerState
private def ePostInput (r : ℕ) (encHandlerState : HandlerState ↪ List Bool) :
    PostInput r HandlerState ↪ List Bool :=
  encPair (eQueryInput r encHandlerState) (eHandlerResult encHandlerState)

private noncomputable def postQueryCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : PostInput r HandlerState => input.1)
      (ePostInput r encHandlerState) (eQueryInput r encHandlerState) :=
  NativeCompiler.first (eQueryInput r encHandlerState) (eHandlerResult encHandlerState)

private noncomputable def postResultCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : PostInput r HandlerState => input.2)
      (ePostInput r encHandlerState) (eHandlerResult encHandlerState) :=
  NativeCompiler.second (eQueryInput r encHandlerState) (eHandlerResult encHandlerState)

private noncomputable def postReplyCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : PostInput r HandlerState => input.2.reply)
      (ePostInput r encHandlerState) encBits :=
  ((NativeCompiler.first encBits encHandlerState).ofInputEq
      (fun result : HandlerResult HandlerState => (result.reply, result.state)) fun _ => rfl).comp
    (postResultCompiler r encHandlerState)

private noncomputable def postHandlerStateCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (fun input : PostInput r HandlerState => input.2.state)
      (ePostInput r encHandlerState) encHandlerState :=
  ((NativeCompiler.second encBits encHandlerState).ofInputEq
      (fun result : HandlerResult HandlerState => (result.reply, result.state)) fun _ => rfl).comp
    (postResultCompiler r encHandlerState)

/-- Retained raw-reply decoding, source-symbol truncation, source-state update and handler-state
threading. -/
private noncomputable def installReplyCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    ClassifiedCompiler
      (fun input : PostInput r HandlerState => installReply input.1 input.2)
      (ePostInput r encHandlerState) (eQueryResult encHandlerState) := by
  let query := ClassifiedCompiler.inPhase .marshalling
    (postQueryCompiler r encHandlerState)
  let source := (ClassifiedCompiler.inPhase .controller
    (sourceCompiler r encHandlerState)).comp query
  let operation := (ClassifiedCompiler.inPhase .tags
    (operationCompiler r encHandlerState)).comp query
  let next := (ClassifiedCompiler.inPhase .tags
    (nextCompiler r encHandlerState)).comp query
  let pending := (ClassifiedCompiler.inPhase .parsing
    (pendingCompiler r encHandlerState)).comp query
  let fuel := (ClassifiedCompiler.inPhase .controller fuelCompiler).comp source
  let reply := ClassifiedCompiler.inPhase .replyCopy
    (postReplyCompiler r encHandlerState)
  let replyBits := (ClassifiedCompiler.inPhase .replyCopy replyBitsCompiler).comp source
  let retained := (ClassifiedCompiler.inPhase .replyCopy NativeCompiler.takeBits).comp
    (reply.pair replyBits)
  let decoded := (ClassifiedCompiler.inPhase .codec
    NativeCompiler.unaryListDecoder).comp retained
  let sourceSymbols := (ClassifiedCompiler.inPhase .codec
    (NativeCompiler.takeUnary encUnary)).comp (decoded.pair fuel)
  let receiveInput := pending.pair (operation.pair (next.pair sourceSymbols))
  let received := (ClassifiedCompiler.inPhase .localStep
    (ICfg.receiveCompiler r)).comp receiveInput
  let advanced := (ClassifiedCompiler.inPhase .controller advanceCompiler).comp
    (source.pair received)
  let state := ClassifiedCompiler.inPhase .controller
    (postHandlerStateCompiler r encHandlerState)
  let result := advanced.pair state
  let present := (ClassifiedCompiler.inPhase .controller
    (NativeCompiler.optionSome (encPair eLoopState encHandlerState))).comp result
  exact classifiedOfOutputEq present fun _ => rfl

/-- The deterministic retained continuation after a local handler returns. -/
noncomputable def installReplyArtifact (external r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeOracleProgram external
      (fun input : QueryInput r HandlerState × HandlerResult HandlerState =>
        pure (installReply input.1 input.2))
      (encPair (eQueryInput r encHandlerState) (eHandlerResult encHandlerState))
      (eQueryResult encHandlerState) :=
  NativeOracleProgram.ofCompiler (r := external)
    (installReplyCompiler r encHandlerState)

/-- Execute an actual retained stateful handler after retained call marshalling. -/
noncomputable def preparedHandler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState)) :
    NativeOracleProgram external (fun input => handler (handlerCall input))
      (eQueryInput r encHandlerState) (eHandlerResult encHandlerState) :=
  NativeOracleProgram.preprocess (handlerCallCompiler r encHandlerState) artifact

/-- A phasewise bound for the retained reply installer on every result supported by the supplied
handler artifact. This is deliberately a support-local construction obligation: callers need not
bound impossible handler states or replies. -/
@[expose]
def PostBound (r : ℕ) (encHandlerState : HandlerState ↪ List Bool)
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState)) : Prop :=
  ∀ input (OracleState : Type)
    (oracle : Fin external × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (result : HandlerResult HandlerState) (state' : OracleState),
    (result, state') ∈
      (ProbOracleComp.runWith oracle (handler (handlerCall input)) state).support →
    ∀ phase,
      (installReplyArtifact external r encHandlerState).online.time phase (input, result) ≤
          postOnline.time phase input

/-- Install one actual retained stateful handler in a validated source-query branch. The caller's
phasewise post bound covers continuation costs only on results in the supplied handler artifact's
support. Raw replies are always copied through the canonical retained `NativeCompiler.takeBits`;
the bound carries no reply-length assumption. The resulting witness retains the composed
finite-control machine and has no semantic handler callback beyond `artifact`'s certified program.
For `external = 0` this is a closed native query branch. -/
noncomputable def queryBranch (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState))
    (hpost : PostBound r encHandlerState handler postOnline) :
    NativeOracleProgram external (queryProgram handler)
      (eQueryInput r encHandlerState) (eQueryResult encHandlerState) :=
  NativeOracleProgram.sequenceCaptured
    (preparedHandler r encHandlerState artifact)
    (installReplyArtifact external r encHandlerState) postOnline hpost

/-- The retained branch calls the encoded operation/request/state triple, copies exactly the raw
reply prefix permitted by `replyBits`, decodes unary source symbols, truncates them to source fuel,
installs the reply and returns the handler's updated state. -/
theorem queryProgram_apply
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState))
    (input : QueryInput r HandlerState) :
    queryProgram handler input = (do
      let result ← handler
        { operation := input.operation
          request := encList encUnary input.request
          state := input.handlerState }
      let reply := result.reply.take input.source.replyBits
      let decoded := (frames reply).map List.length |>.take input.source.fuel
      let next := input.pending.receive input.operation input.next decoded
      pure (some { source := advance input.source next, handlerState := result.state })) := by
  simp [queryProgram, handlerCall, installReply, NativeOracleProgram.capturedProgram]

/-- Exact construction-assigned branch time: retained caller framing and handler execution,
followed by the phasewise reply-installer bound and the outer composition overhead. -/
theorem time_queryBranch (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState))
    (hpost : PostBound r encHandlerState handler postOnline)
    (input : QueryInput r HandlerState) :
    (queryBranch r encHandlerState artifact postOnline hpost).time input =
      5 * ((NativeCompiler.encodeFrame (eQueryInput r encHandlerState)).time input +
        (preparedHandler r encHandlerState artifact).time input) +
          postOnline.totalTime input + 9 :=
  NativeOracleProgram.time_sequenceCaptured _ _ _ _ _

/-- On every supported handler result, each reply-installer phase is charged by the final branch
clock through the declared componentwise continuation ledger. -/
theorem installReplyTime_le_queryBranch (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState))
    (hpost : PostBound r encHandlerState handler postOnline)
    (input : QueryInput r HandlerState) (OracleState : Type)
    (oracle : Fin external × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (result : HandlerResult HandlerState) (state' : OracleState)
    (hresult : (result, state') ∈
      (ProbOracleComp.runWith oracle (handler (handlerCall input)) state).support)
    (phase : OnlinePhase) :
    (installReplyArtifact external r encHandlerState).online.time phase (input, result) ≤
      (queryBranch r encHandlerState artifact postOnline hpost).time input := by
  calc
    _ ≤ postOnline.time phase input :=
      hpost input OracleState oracle state result state' hresult phase
    _ ≤ postOnline.totalTime input := postOnline.time_le_totalTime phase input
    _ ≤ (queryBranch r encHandlerState artifact postOnline hpost).time input := by
      rw [time_queryBranch]
      omega

/-! ### Closed retained handler loop -/

/-- Runtime source input together with the initial private state of an installed handler. -/
structure HandlerRunInput (HandlerState : Type) where
  /-- Runtime first-order source program, input and bounds. -/
  source : RunInput
  /-- Initial private handler state. -/
  handlerState : HandlerState

/-- Encode the runtime source input followed by the initial handler state. -/
enc_structure eHandlerRunInput (encHandlerState : HandlerState ↪ List Bool) :
    HandlerRunInput HandlerState where
  source : eRunInput, handlerState : encHandlerState

/-- Observable result of a valid closed run. -/
structure HandlerRunOutput (HandlerState : Type) where
  /-- Final source output word. -/
  output : List ℕ
  /-- Final private handler state. -/
  handlerState : HandlerState

/-- Encode the final source output followed by the final handler state. -/
enc_structure eHandlerRunOutput (encHandlerState : HandlerState ↪ List Bool) :
    HandlerRunOutput HandlerState where
  output : (encList encUnary), handlerState : encHandlerState

/-- Proof decoder for the paired retained state. It is consumed only by the typed iteration
certificate and is not installed or executed. -/
def retainedStateDecoder {encHandlerState : HandlerState ↪ List Bool}
    (handlerStateDecoder : Decoder encHandlerState) :
    Decoder (eRetainedState encHandlerState) :=
  (Decoder.pair loopStateDecoder handlerStateDecoder).map
    (fun state => { source := state.1, handlerState := state.2 })
    (fun state => (state.source, state.handlerState))
    (fun _ => rfl) fun _ => rfl

/-- Initialize the source loop and retain the caller-supplied private handler state. A malformed
runtime operation count becomes an exhausted retained state, so the source result is `[]` while
the caller's handler state remains observable. -/
@[expose] def initialHandlerState (r : ℕ) (input : HandlerRunInput HandlerState) :
    QueryResult HandlerState :=
  some
    { source := (initialState r input.source).getD default
      handlerState := input.handlerState }

/-- Runtime source-round schedule of a retained handler state. -/
@[expose] def handlerRounds : QueryResult HandlerState → ℕ
  | none => 0
  | some state => state.source.remaining

/-- Return the final source output and private handler state together. The absent case is only the
total compiler fallback: exact retained runs finish in a present state. -/
@[expose] def handlerOutput [Inhabited HandlerState] :
    QueryResult HandlerState → HandlerRunOutput HandlerState
  | none => { output := [], handlerState := default }
  | some state => { output := state.source.cfg.output, handlerState := state.handlerState }

@[simp]
theorem handlerOutput_some [Inhabited HandlerState] (state : RetainedState HandlerState) :
    handlerOutput (some state) =
      { output := state.source.cfg.output, handlerState := state.handlerState } := rfl

/-- Local source commands advance the source state and preserve private handler state. -/
@[expose] def localUpdate (input : RetainedState HandlerState × ICfg) :
    RetainedState HandlerState :=
  { source := advance input.1.source input.2
    handlerState := input.1.handlerState }

/-- Marshal a selected source query and the retained private state into the installed-handler
boundary. The total local-command fallback is never executed because `bodyWithQueryBranch`
dispatches on the command tag before entering this artifact. -/
@[expose] def handlerQueryInput (r : ℕ)
    (input : RetainedCommandInput (r + 1) (RetainedState HandlerState)) :
    QueryInput (r + 1) HandlerState :=
  let payload := retainedCommandQueryPayload (r + 1) 0 input
  { source := input.1.source
    operation := payload.operation
    request := payload.request
    next := payload.next
    pending := payload.pending
    handlerState := input.1.handlerState }

/-- On an actual query command, handler marshalling preserves every source and handler field. -/
@[simp]
theorem handlerQueryInput_query (r : ℕ) (state : RetainedState HandlerState)
    (operation : Fin (r + 1)) (request : List ℕ) (next : ℕ) (pending : ICfg) :
    handlerQueryInput r (state, .query operation request next pending) =
      { source := state.source
        operation
        request
        next
        pending
        handlerState := state.handlerState } := by
  simp [handlerQueryInput, retainedCommandQueryPayload_query]

/-- Closed query semantics installed in the generic body. -/
noncomputable def handlerCommandProgram (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : RetainedCommandInput (r + 1) (RetainedState HandlerState)) :
    WordOracleComp (Fin 0) (QueryResult HandlerState) :=
  queryProgram handler (handlerQueryInput r input)

/-- The installed query program invokes the supplied handler, truncates and decodes its raw reply,
updates the suspended source and retains the returned private state. -/
theorem handlerCommandProgram_query (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (state : RetainedState HandlerState) (operation : Fin (r + 1))
    (request : List ℕ) (next : ℕ) (pending : ICfg) :
    handlerCommandProgram r handler (state, .query operation request next pending) = (do
      let result ← handler
        { operation
          request := encList encUnary request
          state := state.handlerState }
      let reply := result.reply.take state.source.replyBits
      let decoded := (frames reply).map List.length |>.take state.source.fuel
      let cfg := pending.receive operation next decoded
      pure (some
        { source := advance state.source cfg
          handlerState := result.state })) := by
  simpa [handlerCommandProgram] using
    queryProgram_apply handler
      { source := state.source
        operation
        request
        next
        pending
        handlerState := state.handlerState }

/-! ### Stateful source semantics -/

/-- Run one installed handler call as the stateful oracle seen by the original open interpreter.
The handler's own private samples remain fresh, and its returned state becomes the next oracle
state. -/
@[expose] noncomputable def localHandlerOracle
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (query : Fin r × List Bool) : StateT HandlerState ProbComp (List Bool) :=
  fun state => do
    let result ← (handler { operation := query.1, request := query.2, state }).run
      (fun impossible => impossible.1.elim0)
    pure (result.reply, result.state)

/-- The same handler lifted before closing its impossible external channel. This form is used to
compare the concrete retained controller with stateful interpretation of `Universal.run`.
-/
private noncomputable def localHandlerProgram
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (query : Fin r × List Bool) :
    StateT HandlerState (WordOracleComp (Fin 0)) (List Bool) :=
  fun state => do
    let result ← handler { operation := query.1, request := query.2, state }
    pure (result.reply, result.state)

/-- Interpret an open Boolean-word program through the locally installed stateful handler, while
keeping the handler's impossible external channel in the resulting program type. -/
private noncomputable def runWithLocalHandler
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (program : WordOracleComp (Fin r) α) (state : HandlerState) :
    WordOracleComp (Fin 0) (α × HandlerState) :=
  (OracleComp.interpret
    (OracleComp.sumHandler
      (fun n => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin n)))
      (localHandlerProgram handler)) program).run state

private theorem sample_run_empty (program : WordOracleComp (Fin 0) α) :
    ProbOracleComp.sample (program.run (fun impossible => impossible.1.elim0)) = program := by
  induction program using ProbOracleComp.induction with
  | pure value => simp
  | sample_bind n next ih =>
      simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample,
        ProbOracleComp.sample_bind]
      apply congrArg (ProbOracleComp.sample (ProbComp.unifFin n) >>= ·)
      funext value
      exact ih value
  | query_bind query next ih => exact query.1.elim0

/-- Closing the impossible channel after handler installation is exactly the ordinary
`ProbOracleComp.runState` execution, including the final private state. -/
private theorem run_runWithLocalHandler
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (program : WordOracleComp (Fin r) α) (state : HandlerState) :
    (runWithLocalHandler handler program state).run (fun impossible => impossible.1.elim0) =
      (program.runState (localHandlerOracle handler)).run state := by
  have hsample :
      ProbOracleComp.sample
          ((program.runState (localHandlerOracle handler)).run state) =
        runWithLocalHandler handler program state := by
    rw [ProbOracleComp.runState, ProbOracleComp.sample_run_interpret]
    unfold runWithLocalHandler
    congr 2 with q t : 2
    cases q with
    | inl n => rfl
    | inr query =>
        simp [StateT.run, localHandlerOracle, localHandlerProgram,
          sample_run_empty]
  calc
    _ = (ProbOracleComp.sample (spec := fun _ : Fin 0 × List Bool => List Bool)
        ((program.runState (localHandlerOracle handler)).run state)).run
          (fun impossible => impossible.1.elim0) :=
      congrArg (fun closed : WordOracleComp (Fin 0) (α × HandlerState) =>
        closed.run (fun impossible => impossible.1.elim0)) hsample.symm
    _ = _ := ProbOracleComp.run_sample _ _

private def retainedFields (s : RetainedState HandlerState) := (s.source, s.handlerState)

private noncomputable opaque retainedHandlerStateCompiler
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler RetainedState.handlerState (eRetainedState encHandlerState) encHandlerState :=
  (NativeCompiler.second eLoopState encHandlerState).ofInputEq retainedFields fun _ => rfl

private noncomputable opaque retainedSourceCompiler
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler RetainedState.source (eRetainedState encHandlerState) eLoopState :=
  (NativeCompiler.first eLoopState encHandlerState).ofInputEq
    (encIn := eRetainedState encHandlerState) retainedFields fun _ => rfl

private noncomputable def localUpdateCompiler
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (localUpdate : RetainedState HandlerState × ICfg → RetainedState HandlerState)
      (encPair (eRetainedState encHandlerState) eICfg)
      (eRetainedState encHandlerState) := by
  let retained := NativeCompiler.first (eRetainedState encHandlerState) eICfg
  let source := (retainedSourceCompiler encHandlerState).comp retained
  let cfg := NativeCompiler.second (eRetainedState encHandlerState) eICfg
  let advanced := advanceCompiler.comp (source.pair cfg)
  let state := (retainedHandlerStateCompiler encHandlerState).comp retained
  exact (advanced.pair state).ofOutputEq fun _ => rfl

private noncomputable opaque handlerQueryInputCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (handlerQueryInput r)
      (eRetainedCommandInput (r + 1) (eRetainedState encHandlerState))
      (eQueryInput (r + 1) encHandlerState) := by
  let retained := NativeCompiler.first (eRetainedState encHandlerState) (eCommand (r + 1))
  let source := (retainedSourceCompiler encHandlerState).comp retained
  let state := (retainedHandlerStateCompiler encHandlerState).comp retained
  let encState := eRetainedState encHandlerState
  let operation := queryOperationCompiler (r + 1) 0 encState
  let request := queryRequestCompiler (r + 1) 0 encState
  let next := queryNextCompiler (r + 1) 0 encState
  let pending := queryCfgCompiler (r + 1) 0 encState
  exact (source.pair (operation.pair (request.pair (next.pair (pending.pair state)))))
    |>.ofOutputEq fun _ => rfl

/-- Retained closed query artifact on the narrow command boundary. The actual handler branch is
the previously certified `queryBranch`; this preprocessor only marshals the selected command. -/
noncomputable def handlerQueryArtifact (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) :
    NativeOracleProgram 0 (handlerCommandProgram r handler)
      (eRetainedCommandInput (r + 1) (eRetainedState encHandlerState))
      (eQueryResult encHandlerState) :=
  NativeOracleProgram.preprocess
    (ClassifiedCompiler.inPhase .marshalling
      (handlerQueryInputCompiler r encHandlerState))
    (queryBranch (r + 1) encHandlerState handlerArtifact postOnline hpost)

/-- Exact one-round semantics of the installed handler controller. -/
noncomputable def handlerBodyProgram [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)) :
    QueryResult HandlerState → WordOracleComp (Fin 0) (QueryResult HandlerState) :=
  bodyProgramWithQueryBranch (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler)

@[simp]
private theorem handlerBodyProgram_none [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)) :
    handlerBodyProgram r handler none = pure none :=
  bodyProgramWithQueryBranch_none (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler)

/-- Exhausted retained source storage stops before sampling or invoking the handler. -/
private theorem handlerBodyProgram_exhausted [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (state : RetainedState HandlerState) (hremaining : state.source.remaining = 0) :
    handlerBodyProgram r handler (some state) = pure none :=
  bodyProgramWithQueryBranch_exhausted (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler) state hremaining

/-- A halted source advances locally while preserving the private handler state. -/
private theorem handlerBodyProgram_halted [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (state : RetainedState HandlerState) (hremaining : state.source.remaining ≠ 0)
    (hcontrol : state.source.cfg.control = none) :
    handlerBodyProgram r handler (some state) =
      pure (some (localUpdate (state, state.source.cfg))) :=
  bodyProgramWithQueryBranch_halted (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler) state hremaining hcontrol

/-- Active retained storage uses exactly the shared fair-coin/lookup/command semantics. -/
private theorem handlerBodyProgram_active [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (state : RetainedState HandlerState) (control : Option ℕ)
    (hremaining : state.source.remaining ≠ 0)
    (hcontrol : state.source.cfg.control = some control) :
    handlerBodyProgram r handler (some state) =
      activeProgramWithQueryBranch (r + 1) RetainedState.source localUpdate
        (handlerCommandProgram r handler) state :=
  bodyProgramWithQueryBranch_active (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler) state control hremaining hcontrol

private def withDynamicHandlerState (template : LoopState) (remaining : ℕ) (cfg : ICfg)
    (handlerState : HandlerState) : RetainedState HandlerState :=
  { source := { template with remaining, cfg }
    handlerState }

private theorem handlerBodyProgram_withDynamic [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (template : LoopState) (remaining : ℕ) (cfg : ICfg) (handlerState : HandlerState) :
    handlerBodyProgram r handler
        (some (withDynamicHandlerState template (remaining + 1) cfg handlerState)) =
      (fun result => some
        (withDynamicHandlerState template remaining result.1 result.2)) <$>
        runWithLocalHandler handler
          (wordStep (r + 1) template.desc template.input template.fuel template.replyBits cfg)
          handlerState := by
  have hremaining :
      (withDynamicHandlerState template (remaining + 1) cfg handlerState).source.remaining ≠ 0 :=
    by simp [withDynamicHandlerState]
  cases hcontrol : cfg.control with
  | none =>
      rw [handlerBodyProgram_halted r handler _ hremaining]
      · simp [runWithLocalHandler, wordStep, hcontrol, withDynamicHandlerState, localUpdate,
          advance]
      · exact hcontrol
  | some control =>
      rw [handlerBodyProgram_active r handler _ control hremaining]
      · rw [activeProgramWithQueryBranch_apply]
        simp only [runWithLocalHandler, wordStep, hcontrol, OracleComp.interpret_bind,
          StateT.run_bind, ProbOracleComp.run_interpret_lift_sample, bind_map_left, map_bind]
        apply congrArg (ProbOracleComp.sample (ProbComp.uniform Bool) >>= ·)
        funext coin
        dsimp only [withDynamicHandlerState]
        cases hcommand : cfg.commandAt (r + 1) template.desc template.input coin with
        | «local» next =>
            simp [localUpdate, advance]
        | query operation request next pending =>
            simp [handlerCommandProgram_query, advance, unaryListDecoder, Decoder.list,
              Decoder.unary, Cslib.StateT.map_apply, StateT.run, localHandlerProgram,
              Functor.map_map]
      · simpa [withDynamicHandlerState] using hcontrol

private theorem handlerIterate_withDynamic [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (template : LoopState) (cfg : ICfg) (handlerState : HandlerState) : ∀ count,
    OracleComp.iterate count (handlerBodyProgram r handler)
        (some (withDynamicHandlerState template count cfg handlerState)) =
      (fun result => some (withDynamicHandlerState template 0 result.1 result.2)) <$>
        runWithLocalHandler handler
          (OracleComp.iterate count
            (wordStep (r + 1) template.desc template.input template.fuel template.replyBits) cfg)
          handlerState
  | 0 => by simp [withDynamicHandlerState, runWithLocalHandler]
  | count + 1 => by
      rw [OracleComp.iterate_succ_bind, OracleComp.iterate_succ_bind,
        handlerBodyProgram_withDynamic]
      simp only [runWithLocalHandler, OracleComp.interpret_bind, StateT.run_bind, map_bind,
        bind_map_left]
      apply OracleComp.bind_congr_on_support
      rintro ⟨nextCfg, nextHandlerState⟩ -
      simpa only [runWithLocalHandler] using
        handlerIterate_withDynamic r handler template nextCfg nextHandlerState count

/-- One actual retained controller round with a locally installed stateful handler. It instantiates
the single shared `bodyWithQueryBranch` coin/lookup/command pipeline. -/
noncomputable def handlerBodyArtifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) :
    NativeOracleProgram 0 (handlerBodyProgram r handler)
      (eQueryResult encHandlerState) (eQueryResult encHandlerState) :=
  bodyWithQueryBranch (r + 1) (eRetainedState encHandlerState) RetainedState.source
    (retainedSourceCompiler encHandlerState) localUpdate
    (localUpdateCompiler encHandlerState)
    (handlerQueryArtifact r encHandlerState handlerArtifact postOnline hpost)

/-- Public proof obligations for retaining a runtime-bounded closed handler loop. The decoder and
invariant are proof data only. Every executed round is the concrete `handlerBodyArtifact`; its
execution time is bounded phase by phase, and the final stopping round must
produce the empty option encoding required by `iterateWhile`. -/
structure LoopCertificate [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) where
  /-- Retraction for the private handler-state encoding. -/
  handlerStateDecoder : Decoder encHandlerState
  /-- Maximum encoded loop-state length on the certified reachable prefix. -/
  lengthBound : QueryResult HandlerState → ℕ
  /-- Phasewise maximum of one concrete handler body on the certified reachable prefix. -/
  roundOnline : OnlineAccounting (QueryResult HandlerState)
  /-- Reachability and progress invariant indexed by completed source rounds. -/
  invariant : QueryResult HandlerState → ℕ → QueryResult HandlerState → Prop
  /-- The initial stored state satisfies the invariant. -/
  base : ∀ initial, invariant initial 0 initial
  /-- Every reachable body phase is charged by `roundOnline`. -/
  time : ∀ initial count, count ≤ handlerRounds initial → ∀ current,
    invariant initial count current → ∀ phase,
      (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).online.time
          phase current ≤ roundOnline.time phase initial
  /-- One supported body result preserves the invariant and has a nonempty state encoding before
  the final stopping round. -/
  preserve : ∀ initial count, count < handlerRounds initial → ∀ current,
    invariant initial count current → ∀ (OracleState : Type)
      (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
      (state state' : OracleState) (next : QueryResult HandlerState),
      (next, state') ∈
          (ProbOracleComp.runWith oracle (handlerBodyProgram r handler current) state).support →
        invariant initial (count + 1) next ∧ eQueryResult encHandlerState next ≠ []
  /-- The additional stopping round emits the empty option word. -/
  last : ∀ initial current, invariant initial (handlerRounds initial) current →
    ∀ (OracleState : Type)
      (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState),
      ProbOracleComp.runWith oracle
          (eQueryResult encHandlerState <$> handlerBodyProgram r handler current) state =
        ProbOracleComp.runWith oracle (pure []) state
  /-- Every invariant-reachable encoded state fits `lengthBound`. -/
  length : ∀ initial count, count ≤ handlerRounds initial → ∀ current,
    invariant initial count current →
      (eQueryResult encHandlerState current).length ≤ lengthBound initial

/-! ### Finite handler-state certificates -/

private def finiteSuccessorForReply (state : RetainedState HandlerState)
    (operation : Fin (r + 1)) (next : ℕ) (pending : ICfg) (reply : List Bool)
    (handlerState : HandlerState) : QueryResult HandlerState :=
  some
    { source := advance state.source (pending.receive operation next
        ((unaryListDecoder.decode reply).take state.source.fuel))
      handlerState }

private noncomputable def finiteCoinSuccessors [Fintype HandlerState] (r : ℕ)
    (state : RetainedState HandlerState) (coin : Bool) : List (QueryResult HandlerState) :=
  match state.source.cfg.commandAt (r + 1) state.source.desc state.source.input coin with
  | .local cfg => [some (localUpdate (state, cfg))]
  | .query operation _ next pending =>
      (boundedReplyWords state.source.replyBits).flatMap fun reply =>
        Finset.univ.toList.map fun handlerState =>
          finiteSuccessorForReply state operation next pending reply handlerState

/-- Finite overapproximation of every one-round result when the private handler state is finite.
The handler program itself need not be deterministic: reply prefixes and final private states are
both enumerated independently. -/
private noncomputable def finiteSuccessors [Fintype HandlerState] (r : ℕ) :
    QueryResult HandlerState → List (QueryResult HandlerState)
  | none => [none]
  | some state =>
      if state.source.remaining = 0 then [none]
      else match state.source.cfg.control with
        | none => [some (localUpdate (state, state.source.cfg))]
        | some _ => [false, true].flatMap (finiteCoinSuccessors r state)

/-- States in the finite overapproximation after exactly `count` retained rounds. -/
private noncomputable abbrev finiteReachable [Fintype HandlerState] (r : ℕ) :=
  ProbOracleComp.reachableIn (finiteSuccessors r (HandlerState := HandlerState))

/-- All finitely enumerated retained states at indices used by the loop certificate. -/
private noncomputable def finiteReachablePrefix [Fintype HandlerState] (r : ℕ)
    (initial : QueryResult HandlerState) : List (QueryResult HandlerState) :=
  (List.range (handlerRounds initial + 1)).flatMap (finiteReachable r initial)

private theorem support_mem_finiteSuccessors [Inhabited HandlerState] [Fintype HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (current next : QueryResult HandlerState) (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (handlerBodyProgram r handler current) state).support) :
    next ∈ finiteSuccessors r current := by
  classical
  rcases current with _ | current
  · simp only [handlerBodyProgram_none, ProbOracleComp.runWith_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hnext
    rcases hnext with ⟨rfl, rfl⟩
    simp [finiteSuccessors]
  · by_cases hremaining : current.source.remaining = 0
    · rw [handlerBodyProgram_exhausted r handler current hremaining] at hnext
      simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hnext
      rcases hnext with ⟨rfl, rfl⟩
      simp [finiteSuccessors, hremaining]
    · cases hcontrol : current.source.cfg.control with
      | none =>
          rw [handlerBodyProgram_halted r handler current hremaining hcontrol] at hnext
          simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hnext
          rcases hnext with ⟨rfl, rfl⟩
          simp [finiteSuccessors, hremaining, hcontrol]
      | some control =>
          rw [handlerBodyProgram_active r handler current control hremaining hcontrol,
            activeProgramWithQueryBranch_apply, ProbOracleComp.runWith_bind] at hnext
          obtain ⟨⟨coin, coinState⟩, hcoin, hcommand⟩ :=
            (PMF.mem_support_bind_iff _ _ _).mp hnext
          dsimp only at hcommand
          have hcoinValue : coin = false ∨ coin = true := by cases coin <;> simp
          cases hcmd : current.source.cfg.commandAt (r + 1) current.source.desc
              current.source.input coin with
          | «local» cfg =>
              simp only [hcmd, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                Prod.mk.injEq] at hcommand
              rcases hcommand with ⟨rfl, rfl⟩
              simp only [finiteSuccessors, hremaining, ↓reduceIte, hcontrol, List.mem_flatMap,
                List.mem_cons, List.not_mem_nil, or_false]
              exact ⟨coin, hcoinValue, by simp [finiteCoinSuccessors, hcmd]⟩
          | query operation request nextTag pending =>
              rw [hcmd, handlerCommandProgram_query, ProbOracleComp.runWith_bind] at hcommand
              obtain ⟨⟨result, resultState⟩, hresult, hfinal⟩ :=
                (PMF.mem_support_bind_iff _ _ _).mp hcommand
              simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                Prod.mk.injEq] at hfinal
              rcases hfinal with ⟨rfl, rfl⟩
              have hprefix : result.reply.take current.source.replyBits ∈
                  boundedReplyWords current.source.replyBits :=
                (mem_boundedReplyWords_iff _ _).2 (List.length_take_le _ _)
              have hstate : result.state ∈ (Finset.univ.toList : List HandlerState) :=
                Finset.mem_toList.mpr (Finset.mem_univ _)
              simp only [finiteSuccessors, hremaining, ↓reduceIte, hcontrol, List.mem_flatMap,
                List.mem_cons, List.not_mem_nil, or_false]
              refine ⟨coin, hcoinValue, ?_⟩
              simp only [finiteCoinSuccessors, hcmd, List.mem_flatMap, List.mem_map]
              exact ⟨result.reply.take current.source.replyBits, hprefix,
                result.state, hstate, rfl⟩

private theorem support_mem_finiteReachable [Inhabited HandlerState] [Fintype HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (initial : QueryResult HandlerState) (count : ℕ) (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (current : QueryResult HandlerState) (state' : OracleState)
    (hcurrent : (current, state') ∈
      (ProbOracleComp.runWith oracle
        (OracleComp.iterate count (handlerBodyProgram r handler) initial) state).support) :
    current ∈ finiteReachable r initial count :=
  ProbOracleComp.mem_reachableIn_of_runWith_iterate (handlerBodyProgram r handler)
    (finiteSuccessors r) oracle
    (fun a b s t => support_mem_finiteSuccessors r handler a b OracleState oracle s t)
      initial count state hcurrent

private def FiniteProgress (initial : QueryResult HandlerState) (count : ℕ)
    (current : QueryResult HandlerState) : Prop :=
  match initial with
  | none => current = none
  | some first => ∃ second, current = some second ∧
      first.source.SameStatic second.source ∧
      second.source.remaining + count = first.source.remaining

/-- Reachability, source-static preservation and exact remaining-round progress for the finite
handler-state certificate. -/
private def FiniteInvariant [Fintype HandlerState] (r : ℕ)
    (initial : QueryResult HandlerState)
    (count : ℕ) (current : QueryResult HandlerState) : Prop :=
  FiniteProgress initial count current ∧ current ∈ finiteReachable r initial count

private theorem finiteInvariant_zero [Fintype HandlerState] (r : ℕ)
    (initial : QueryResult HandlerState) : FiniteInvariant r initial 0 initial := by
  constructor
  · cases initial with
    | none => rfl
    | some s => exact ⟨s, rfl, ⟨rfl, rfl, rfl, rfl⟩, by simp⟩
  · simp [finiteReachable, ProbOracleComp.reachableIn]

private theorem finiteProgress_successor [Inhabited HandlerState]
    {r : ℕ} {initial current next : QueryResult HandlerState} {count : ℕ}
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (hcount : count < handlerRounds initial)
    (hprogress : FiniteProgress initial count current) (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (handlerBodyProgram r handler current) state).support) :
    FiniteProgress initial (count + 1) next ∧ eQueryResult encHandlerState next ≠ [] := by
  cases hinitial : initial with
  | none => simp [hinitial, handlerRounds] at hcount
  | some first =>
      simp only [FiniteProgress, hinitial] at hprogress
      obtain ⟨second, rfl, hstatic, hremaining⟩ := hprogress
      simp only [hinitial, handlerRounds] at hcount
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show second.source.remaining ≠ 0 by omega)
      have hsecond : second =
          withDynamicHandlerState second.source (n + 1) second.source.cfg second.handlerState := by
        cases second with
        | mk source state => cases source; simp_all [withDynamicHandlerState]
      rw [hsecond, handlerBodyProgram_withDynamic, ProbOracleComp.runWith_map] at hnext
      obtain ⟨⟨⟨cfg, hs⟩, middle⟩, _, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hnext
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact ⟨⟨_, rfl, ⟨hstatic.desc, hstatic.input, hstatic.fuel, hstatic.replyBits⟩,
        by dsimp [withDynamicHandlerState]; omega⟩, by simp [eQueryResult]⟩

private theorem finiteInvariant_successor [Inhabited HandlerState] [Fintype HandlerState]
    {r : ℕ} {initial current next : QueryResult HandlerState} {count : ℕ}
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (hcount : count < handlerRounds initial)
    (hinvariant : FiniteInvariant r initial count current) (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (handlerBodyProgram r handler current) state).support) :
    FiniteInvariant r initial (count + 1) next ∧ eQueryResult encHandlerState next ≠ [] := by
  obtain ⟨hprogress, hpresent⟩ := finiteProgress_successor (encHandlerState := encHandlerState)
    handler hcount hinvariant.1 OracleState oracle state state' hnext
  exact ⟨⟨hprogress, ProbOracleComp.mem_reachableIn_succ hinvariant.2
    (support_mem_finiteSuccessors r handler current next OracleState oracle state state' hnext)⟩,
    hpresent⟩

private theorem finiteInvariant_last [Inhabited HandlerState] [Fintype HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (initial current : QueryResult HandlerState)
    (hinvariant : FiniteInvariant r initial (handlerRounds initial) current)
    (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) :
    ProbOracleComp.runWith oracle
        (eQueryResult encHandlerState <$> handlerBodyProgram r handler current) state =
      ProbOracleComp.runWith oracle (pure []) state := by
  cases hinitial : initial with
  | none =>
      have hcurrent : current = none := by simpa only [FiniteProgress, hinitial] using hinvariant.1
      subst current
      simp [handlerBodyProgram_none, eQueryResult]
  | some first =>
      simp only [hinitial, handlerRounds] at hinvariant
      obtain ⟨second, rfl, hstatic, hremaining⟩ := hinvariant.1
      have hzero : second.source.remaining = 0 := by omega
      rw [handlerBodyProgram_exhausted r handler second hzero]
      simp [eQueryResult]

private theorem mem_finiteReachablePrefix [Fintype HandlerState]
    {r : ℕ} {initial current : QueryResult HandlerState} {count : ℕ}
    (hcount : count ≤ handlerRounds initial)
    (hcurrent : current ∈ finiteReachable r initial count) :
    current ∈ finiteReachablePrefix r initial := by
  simp only [finiteReachablePrefix, List.mem_flatMap]
  exact ⟨count, List.mem_range.mpr (by omega), hcurrent⟩

/-- Maximum encoded retained-state length on the finite reachable prefix. -/
private noncomputable def finiteLengthBound [Fintype HandlerState]
    (encHandlerState : HandlerState ↪ List Bool) (r : ℕ)
    (initial : QueryResult HandlerState) : ℕ :=
  listMax (fun state => (eQueryResult encHandlerState state).length)
    (finiteReachablePrefix r initial)

/-- Phasewise maxima of the concrete retained body on the finite reachable prefix. -/
private noncomputable def finiteRoundOnline [Inhabited HandlerState]
    [Fintype HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) :
    OnlineAccounting (QueryResult HandlerState) where
  time := fun phase initial =>
    listMax (fun current =>
      (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).online.time
        phase current) (finiteReachablePrefix r initial)

/-- Canonical loop certificate for any finitely inhabited private handler state. It enumerates all
bounded reply prefixes and all next private states, so it applies to probabilistic handlers without
a semantic determinism assumption. -/
noncomputable def finiteLoopCertificate [Inhabited HandlerState] [Fintype HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    (handlerStateDecoder : Decoder encHandlerState)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) :
    LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost where
  handlerStateDecoder := handlerStateDecoder
  lengthBound := finiteLengthBound encHandlerState r
  roundOnline := finiteRoundOnline r encHandlerState handlerArtifact postOnline hpost
  invariant := FiniteInvariant r
  base := finiteInvariant_zero r
  time := fun _ _ hcount _ hinvariant _ =>
    le_listMax (mem_finiteReachablePrefix hcount hinvariant.2)
  preserve := fun _ _ hcount _ hinvariant OracleState oracle state state' _
      hnext => finiteInvariant_successor handler hcount hinvariant OracleState oracle state state'
        hnext
  last := finiteInvariant_last r handler
  length := fun _ _ hcount _ hinvariant =>
    le_listMax (f := fun s => (eQueryResult encHandlerState s).length)
      (mem_finiteReachablePrefix hcount hinvariant.2)

/-- Exact closed loop semantics before runtime initialization and final-output projection. -/
noncomputable def handlerLoopProgram [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (initial : QueryResult HandlerState) :
    WordOracleComp (Fin 0) (QueryResult HandlerState) :=
  OracleComp.iterate (handlerRounds initial) (handlerBodyProgram r handler) initial

/-- Actual retained stateful loop. Runtime fuel changes the clock and encoded initial state, not
the installed body or loop machine. -/
noncomputable def handlerLoopArtifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    NativeOracleProgram 0 (handlerLoopProgram r handler)
      (eQueryResult encHandlerState) (eQueryResult encHandlerState) :=
  NativeOracleProgram.boundedIterationEncodedOn
    (.option (retainedStateDecoder certificate.handlerStateDecoder))
    (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost)
    handlerRounds certificate.lengthBound certificate.roundOnline certificate.invariant
    certificate.base certificate.time certificate.preserve certificate.last
    certificate.length

/-- Exact construction-assigned loop time, including every handler body round and the final
stopping round. -/
theorem time_handlerLoopArtifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost)
    (initial : QueryResult HandlerState) :
    (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost certificate).time
        initial =
      (handlerRounds initial + 1) *
          (certificate.roundOnline.totalTime initial +
            10 * certificate.lengthBound initial + 23) +
        8 * certificate.lengthBound initial + 17 :=
  NativeOracleProgram.time_boundedIterationEncodedOn _ _ _ _ _ _ _ _ _ _ _ _

/-! ### Runtime preparation and final projection -/

/-- Actual retained compiler for runtime source initialization and private-state capture. -/
noncomputable def initialHandlerStateCompiler [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (initialHandlerState r)
      (eHandlerRunInput encHandlerState) (eQueryResult encHandlerState) := by
  let sourceInput := (NativeCompiler.first eRunInput encHandlerState).ofInputEq
    (encIn := eHandlerRunInput encHandlerState)
    (fun i : HandlerRunInput HandlerState => (i.source, i.handlerState)) fun _ => rfl
  let state := (NativeCompiler.second eRunInput encHandlerState).ofInputEq
    (encIn := eHandlerRunInput encHandlerState)
    (fun i : HandlerRunInput HandlerState => (i.source, i.handlerState)) fun _ => rfl
  let source := (initialCompiler r).comp sourceInput
  let retainedSource := (NativeCompiler.optionGetD default eLoopState).comp source
  let retained : NativeCompiler
      (fun input : HandlerRunInput HandlerState =>
        (⟨(initialState r input.source).getD default, input.handlerState⟩ :
          RetainedState HandlerState))
      (eHandlerRunInput encHandlerState) (eRetainedState encHandlerState) :=
    (retainedSource.pair state).ofOutputEq fun _ => rfl
  exact ((NativeCompiler.optionSome (eRetainedState encHandlerState)).comp retained).ofOutputEq
    fun input => by
      cases hsource : initialState r input.source <;>
        simp [initialHandlerState, hsource]

/-- Retained compiler for the complete output/final-handler-state projection. -/
noncomputable def handlerOutputCompiler [Inhabited HandlerState]
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler handlerOutput (eQueryResult encHandlerState)
      (eHandlerRunOutput encHandlerState) := by
  let condition := NativeCompiler.optionIsSomeTest (eRetainedState encHandlerState)
  let retained := NativeCompiler.optionGetD default (eRetainedState encHandlerState)
  let source := (retainedSourceCompiler encHandlerState).comp retained
  let cfg := cfgCompiler.comp source
  let output := ICfg.outputCompiler.comp cfg
  let state := (retainedHandlerStateCompiler encHandlerState).comp retained
  let result : NativeCompiler
      (fun input : QueryResult HandlerState =>
        (⟨(input.getD default).source.cfg.output, (input.getD default).handlerState⟩ :
          HandlerRunOutput HandlerState))
      (eQueryResult encHandlerState) (eHandlerRunOutput encHandlerState) :=
    (output.pair state).ofOutputEq fun _ => rfl
  let absent := NativeCompiler.const (eQueryResult encHandlerState)
    (eHandlerRunOutput encHandlerState)
    ({ output := [], handlerState := default } : HandlerRunOutput HandlerState)
  exact (NativeCompiler.ite condition result absent).ofOutputEq fun input => by
    cases input <;> rfl

/-- Semantics after retained runtime initialization, before final-output projection. -/
noncomputable def initializedHandlerProgram [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState) :
    WordOracleComp (Fin 0) (QueryResult HandlerState) :=
  handlerLoopProgram r handler (initialHandlerState (r + 1) input)

/-- Retained input initialization followed by the certified closed handler loop. -/
noncomputable def initializedHandlerArtifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    NativeOracleProgram 0 (initializedHandlerProgram r handler)
      (eHandlerRunInput encHandlerState) (eQueryResult encHandlerState) :=
  NativeOracleProgram.preprocess
    (ClassifiedCompiler.inPhase .inputCopy
      (initialHandlerStateCompiler (r + 1) encHandlerState))
    (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost certificate)

/-- Exact initialization-plus-loop time; source input copying and the retained loop remain
separate construction-derived terms. -/
theorem time_initializedHandlerArtifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost)
    (input : HandlerRunInput HandlerState) :
    (initializedHandlerArtifact r encHandlerState handlerArtifact postOnline hpost
        certificate).time input =
      5 * (initialHandlerStateCompiler (r + 1) encHandlerState).time input +
        (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost certificate).time
          (initialHandlerState (r + 1) input) + 9 :=
  NativeOracleProgram.time_preprocess _ _ _

/-- Exact complete closed semantics: initialize, execute every source round with the retained local
handler, then return the source output and final private handler state together. -/
noncomputable def handlerRunProgram [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState) :
    WordOracleComp (Fin 0) (HandlerRunOutput HandlerState) :=
  handlerOutput <$> initializedHandlerProgram r handler input

/-- The retained closed controller is extensionally the original fixed-channel interpreter run
through the installed stateful handler. This program-level equality includes the final handler
state rather than only projecting the source output. -/
private theorem handlerRunProgram_eq_runWithLocalHandler [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState) :
    handlerRunProgram r handler input =
      (fun result =>
        ({ output := result.1, handlerState := result.2 } : HandlerRunOutput HandlerState)) <$>
        runWithLocalHandler handler (Turing.MultiTapePTM.Universal.run (r + 1) input.source)
          input.handlerState := by
  by_cases hoperations : input.source.desc.operations = r + 1
  · let template : LoopState :=
      ⟨input.source.desc, input.source.input, input.source.fuel, input.source.replyBits,
        input.source.fuel, ICfg.init input.source.desc⟩
    simp only [Turing.MultiTapePTM.Universal.run, hoperations, ↓reduceIte]
    change handlerOutput <$> OracleComp.iterate _ (handlerBodyProgram r handler) _ = _
    have hinit : initialHandlerState (r + 1) input =
        some (withDynamicHandlerState template input.source.fuel (ICfg.init input.source.desc)
          input.handlerState) := by simp [initialHandlerState, initialState, hoperations, template,
            withDynamicHandlerState]
    rw [hinit]
    change handlerOutput <$> OracleComp.iterate input.source.fuel _ _ = _
    rw [handlerIterate_withDynamic]
    simp [runWithLocalHandler, withDynamicHandlerState, template,
      Functor.map_map, Cslib.StateT.map_apply, StateT.run]
  · simp [handlerRunProgram, initializedHandlerProgram, handlerLoopProgram, initialHandlerState,
      initialState, hoperations, handlerRounds, Turing.MultiTapePTM.Universal.run,
      runWithLocalHandler, show (default : LoopState).remaining = 0 from rfl]
    rfl

/-- **Exact retained local-handler semantics.** Closing the impossible external channel of the
constructed program gives the complete stateful interpreter computation: malformed
operation counts return `[]` and preserve the initial handler state, while valid runs return the
source output beside the handler's actual final state. -/
theorem run_handlerRunProgram_eq_runState [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState) :
    (handlerRunProgram r handler input).run (fun impossible => impossible.1.elim0) =
      (fun result =>
        ({ output := result.1, handlerState := result.2 } : HandlerRunOutput HandlerState)) <$>
        ((Turing.MultiTapePTM.Universal.run (r + 1) input.source).runState
          (localHandlerOracle handler)).run input.handlerState := by
  rw [handlerRunProgram_eq_runWithLocalHandler, ProbOracleComp.run_map,
    run_runWithLocalHandler]

/-- A malformed runtime operation count returns the source interpreter's empty result and keeps
the caller's handler state unchanged. -/
theorem handlerRunProgram_malformed [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState)
    (hoperations : input.source.desc.operations ≠ r + 1) :
    handlerRunProgram r handler input =
      pure { output := [], handlerState := input.handlerState } := by
  simp [handlerRunProgram, initializedHandlerProgram, handlerLoopProgram,
    initialHandlerState, initialState, hoperations, handlerRounds,
    show (default : LoopState).remaining = 0 from rfl]
  rfl

/-- A valid zero-clock run performs no body round and returns the initialized source output beside
the unchanged private handler state. -/
theorem handlerRunProgram_zero_fuel [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState)
    (hoperations : input.source.desc.operations = r + 1)
    (hfuel : input.source.fuel = 0) :
    handlerRunProgram r handler input =
      pure
        { output := (ICfg.init input.source.desc).output
          handlerState := input.handlerState } := by
  simp [handlerRunProgram, initializedHandlerProgram, handlerLoopProgram,
    initialHandlerState, initialState, hoperations, hfuel, handlerRounds, handlerOutput]

/-- Proof-carrying output-copy bound for the final retained handler artifact. The loop certificate
owns reachability and body bounds. This record adds the support-local final projection bound. -/
structure RunCertificate [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) where
  /-- Complete typed-loop certificate. -/
  loop : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost
  /-- Phasewise final-output-copy bound indexed by the original runtime input. -/
  outputOnline : OnlineAccounting (HandlerRunInput HandlerState)
  /-- Every supported final loop state is charged by `outputOnline`. -/
  outputBound : ∀ input (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (current : QueryResult HandlerState) (state' : OracleState),
    (current, state') ∈
        (ProbOracleComp.runWith oracle (initializedHandlerProgram r handler input) state).support →
      ∀ phase,
        (ClassifiedCompiler.inPhase .outputCopy
            (handlerOutputCompiler encHandlerState)).online.time phase current ≤
            outputOnline.time phase input

/-- Phasewise maxima of final output copying over the finite set of reachable final retained
states. -/
private noncomputable def finiteOutputOnline [Inhabited HandlerState]
    [Fintype HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    OnlineAccounting (HandlerRunInput HandlerState) where
  time := fun phase input =>
    listMax (fun current =>
      (ClassifiedCompiler.inPhase .outputCopy
        (handlerOutputCompiler encHandlerState)).online.time phase current)
      (finiteReachable r (initialHandlerState (r + 1) input)
        (handlerRounds (initialHandlerState (r + 1) input)))

/-- Canonical complete run certificate for a finite private handler state. -/
noncomputable def finiteRunCertificate [Inhabited HandlerState] [Fintype HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    (handlerStateDecoder : Decoder encHandlerState)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) :
    RunCertificate r encHandlerState handler handlerArtifact postOnline hpost where
  loop := finiteLoopCertificate r encHandlerState handlerStateDecoder handlerArtifact postOnline
    hpost
  outputOnline := finiteOutputOnline r encHandlerState
  outputBound := fun input OracleState oracle state current state' hcurrent phase => by
    have hreach := support_mem_finiteReachable r handler
      (initialHandlerState (r + 1) input)
      (handlerRounds (initialHandlerState (r + 1) input)) OracleState oracle state current state'
      (by simpa [initializedHandlerProgram, handlerLoopProgram] using hcurrent)
    exact le_listMax hreach

/-- Complete actual closed retained artifact. Its operation type is `Fin 0`: every source query is
handled locally, so no validation or other external call remains. -/
noncomputable def artifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    NativeOracleProgram 0 (handlerRunProgram r handler)
      (eHandlerRunInput encHandlerState)
      (eHandlerRunOutput encHandlerState) :=
  NativeOracleProgram.postprocess
    (initializedHandlerArtifact r encHandlerState handlerArtifact postOnline hpost
      certificate.loop)
    (ClassifiedCompiler.inPhase .outputCopy (handlerOutputCompiler encHandlerState))
    certificate.outputOnline certificate.outputBound

/-- Installed and runtime bits for the closed controller. Its own description includes the
installed handler. The source description occurs inside the framed source input and the initial
private handler state follows that frame. -/
theorem installed_add_input_bits [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost)
    (input : HandlerRunInput HandlerState) :
    let installed := artifact r encHandlerState handlerArtifact postOnline hpost certificate
    installed.staticBits + (eHandlerRunInput encHandlerState input).length =
      descLen installed.description +
        (2 * (2 * suppliedDescSize input.source + 1 + runParameterSize input.source) +
          1 + (encHandlerState input.handlerState).length) := by
  simp only [eHandlerRunInput_apply, length_encPair, ← runInputSize_eq_framed, runInputSize]
  rfl

/-- Exact final composition time, with the initialized loop and support-local output copy kept as
separate coordinates. -/
theorem time_artifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost)
    (input : HandlerRunInput HandlerState) :
    (artifact r encHandlerState handlerArtifact postOnline hpost certificate).time input =
      5 * (initializedHandlerArtifact r encHandlerState handlerArtifact postOnline hpost
          certificate.loop).time input + certificate.outputOnline.totalTime input + 9 :=
  NativeOracleProgram.time_postprocess _ _ _ _ _

/-- Exact stateful distribution equality for the clocked closed machine. Running the native
clocked machine through the empty external interface yields the encoded source result and final
private handler state. The unrelated external state passes through unchanged. -/
theorem runWith_artifact_machine [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost)
    (input : HandlerRunInput HandlerState) (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) :
    ProbOracleComp.runWith oracle
        ((artifact r encHandlerState handlerArtifact postOnline hpost certificate).machine.runOracle
          ((artifact r encHandlerState handlerArtifact postOnline hpost certificate).time input)
          (eHandlerRunInput encHandlerState input)) state =
      (ProbComp.eval (((Turing.MultiTapePTM.Universal.run (r + 1) input.source).runState
          (localHandlerOracle handler)).run input.handlerState)).map (fun result =>
        (eHandlerRunOutput encHandlerState ⟨result.1, result.2⟩, state)) := by
  rw [NativeOracleProgram.time,
    ((artifact r encHandlerState handlerArtifact postOnline hpost certificate).computes
    input).runOracle oracle state, ProbOracleComp.runWith_map,
    ← sample_run_empty (handlerRunProgram r handler input), run_handlerRunProgram_eq_runState,
    ProbOracleComp.runWith_sample, ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
  rfl

end Turing.MultiTapePTM.Universal.NativeHandler

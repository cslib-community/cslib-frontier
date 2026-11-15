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

## Main definitions

* `Turing.MultiTapePTM.Universal.NativeHandler.HandlerCall`: encoded operation, request word and
  handler state.
* `Turing.MultiTapePTM.Universal.NativeHandler.QueryInput`: suspended source query and handler
  state.
* `Turing.MultiTapePTM.Universal.NativeHandler.queryBranch`: actual retained handler invocation
  followed by retained reply installation.
* `Turing.MultiTapePTM.Universal.NativeHandler.handlerBodyArtifact`: the single shared universal
  controller instantiated with the retained handler branch.
* `Turing.MultiTapePTM.Universal.NativeHandler.finiteLoopCertificate` and
  `finiteRunCertificate`: canonical certificates for finite private handler states.
* `Turing.MultiTapePTM.Universal.NativeHandler.artifact`: complete closed retained initialization,
  typed loop and output-plus-final-state projection.

## Main results

* `Turing.MultiTapePTM.Universal.NativeHandler.queryProgram_apply`: the exact stateful handler,
  prefix-copy, decode and source-update semantics.
* `Turing.MultiTapePTM.Universal.NativeHandler.machine_queryBranch` and
  `Turing.MultiTapePTM.Universal.NativeHandler.time_queryBranch`: the specialized retained machine
  term and exact construction-assigned time sum.
* `Turing.MultiTapePTM.Universal.NativeHandler.online_queryBranch` and
  `Turing.MultiTapePTM.Universal.NativeHandler.installReplyWorkspace_le_queryBranch`: the complete
  componentwise ledger and supported-continuation workspace bound.
* `Turing.MultiTapePTM.Universal.NativeHandler.queryBranch_installedDescriptions`: the final
  composed branch occurs once in its installed-description inventory.
* `Turing.MultiTapePTM.Universal.NativeHandler.queryBranch_installedBits`: the occurrence-sensitive
  installed charge is the generated composed description size.
* `Turing.MultiTapePTM.Universal.NativeHandler.run_handlerRunProgram_eq_runState`: exact source
  `runState` semantics, including operation-count rejection and final private state.
* `Turing.MultiTapePTM.Universal.NativeHandler.runWith_artifact_machine`: exact clocked-machine
  equality for the complete closed output and final private state.
* `Turing.MultiTapePTM.Universal.NativeHandler.time_handlerLoopArtifact` and
  `Turing.MultiTapePTM.Universal.NativeHandler.artifact_installedDescriptions`: exact repeated-body
  clock and one-occurrence installed inventory.

## References

The retained handler installation and its resource accounting are original to this module.
-/

public section

namespace Turing.MultiTapePTM.Universal.NativeHandler

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM
  Turing.MultiTapeTM.Internal Turing.MultiTapePTM.Internal
open Turing.MultiTapePTM.Universal
open Turing.MultiTapePTM.Universal.NativeInterpreter

variable {HandlerState : Type}

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
def eQueryResult (encHandlerState : HandlerState ↪ List Bool) :
    QueryResult HandlerState ↪ List Bool :=
  encOption (eRetainedState encHandlerState)

/-- Marshal the typed source request into the Boolean word consumed by a local handler. -/
def handlerCall (input : QueryInput r HandlerState) : HandlerCall r HandlerState :=
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
  some { source := input.source.advance next, handlerState := result.state }

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
  workspace_le := compiler.workspace_le
  clockWorkspace_le := compiler.clockWorkspace_le

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
      (fun input : PostInput r HandlerState => pure (installReply input.1 input.2))
      (ePostInput r encHandlerState) (eQueryResult encHandlerState) :=
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
          postOnline.time phase input ∧
        (installReplyArtifact external r encHandlerState).online.workspace phase
            (input, result) ≤ postOnline.workspace phase input

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
    queryProgram handler input = do
      let result ← handler
        { operation := input.operation
          request := encList encUnary input.request
          state := input.handlerState }
      let reply := result.reply.take input.source.replyBits
      let decoded := (frames reply).map List.length |>.take input.source.fuel
      let next := input.pending.receive input.operation input.next decoded
      pure (some { source := input.source.advance next, handlerState := result.state }) :=
  rfl

/-- The specialized branch exposes the literal capture append, supplied handler machine and
retained reply installer. In particular, the raw-prefix compiler is part of the executed second
machine rather than a semantic support assumption. -/
theorem machine_queryBranch (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState))
    (hpost : PostBound r encHandlerState handler postOnline) :
    (queryBranch r encHandlerState artifact postOnline hpost).machine =
      (installReplyArtifact external r encHandlerState).machine.tidyComp
        (appendPTM
          (ofDeterministic
            (NativeCompiler.encodeFrame (eQueryInput r encHandlerState)).machine)
          (preparedHandler r encHandlerState artifact).machine) true :=
  NativeOracleProgram.machine_sequenceCaptured _ _ _ _

/-- The complete phase ledger is the captured-input construction ledger: handler preparation and
execution are sequenced with the caller-supplied continuation bound, while capture and final tidy
composition are charged to marshalling. Aggregate time and peak workspace are derived from this
record. -/
theorem online_queryBranch (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState))
    (hpost : PostBound r encHandlerState handler postOnline) :
    (queryBranch r encHandlerState artifact postOnline hpost).online =
      NativeOracleProgram.capturedAccounting
        (preparedHandler r encHandlerState artifact)
        (installReplyArtifact external r encHandlerState) postOnline :=
  rfl

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
      5 * (NativeCompiler.encodeFrame (eQueryInput r encHandlerState) |>.time input +
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
      (hpost input OracleState oracle state result state' hresult phase).1
    _ ≤ postOnline.totalTime input := postOnline.time_le_totalTime phase input
    _ ≤ (queryBranch r encHandlerState artifact postOnline hpost).time input := by
      rw [time_queryBranch]
      omega

/-- On every supported handler result, each reply-installer phase fits the final branch's peak
workspace. This retains the raw-prefix, codec, local-step and controller costs as separate ledger
coordinates before the aggregate peak is taken. -/
theorem installReplyWorkspace_le_queryBranch (r : ℕ)
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
    (installReplyArtifact external r encHandlerState).online.workspace phase (input, result) ≤
      (queryBranch r encHandlerState artifact postOnline hpost).workspace input :=
  NativeOracleProgram.secondWorkspace_le_sequenceCaptured
    (preparedHandler r encHandlerState artifact)
    (installReplyArtifact external r encHandlerState) postOnline hpost
    input OracleState oracle state result state' hresult phase

/-- The installed inventory contains one occurrence of the final composed query branch. The
handler control is inlined into this description rather than charged as a second installed copy. -/
theorem queryBranch_installedDescriptions (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState))
    (hpost : PostBound r encHandlerState handler postOnline) :
    (queryBranch r encHandlerState artifact postOnline hpost).installedDescriptions =
      [(queryBranch r encHandlerState artifact postOnline hpost).description] :=
  NativeOracleProgram.installedDescriptions_eq_singleton _

/-- The one-occurrence installed code charge is exactly the final composed description size. -/
theorem queryBranch_installedBits (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall r HandlerState →
      WordOracleComp (Fin external) (HandlerResult HandlerState)}
    (artifact : NativeOracleProgram external handler
      (eHandlerCall r encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput r HandlerState))
    (hpost : PostBound r encHandlerState handler postOnline) :
    (queryBranch r encHandlerState artifact postOnline hpost).installedBits =
      (queryBranch r encHandlerState artifact postOnline hpost).staticBits :=
  NativeOracleProgram.installedBits_eq_staticBits _

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
def initialHandlerState (r : ℕ) (input : HandlerRunInput HandlerState) :
    QueryResult HandlerState :=
  some
    { source := (initialState r input.source).getD default
      handlerState := input.handlerState }

/-- Exact valid/malformed boundary of the retained handler initializer. -/
theorem initialHandlerState_apply (r : ℕ) (input : HandlerRunInput HandlerState) :
    initialHandlerState r input =
      if input.source.desc.operations = r then
        some
          { source :=
              { desc := input.source.desc
                input := input.source.input
                fuel := input.source.fuel
                replyBits := input.source.replyBits
                remaining := input.source.fuel
                cfg := ICfg.init input.source.desc }
            handlerState := input.handlerState }
      else some
        { source := default
          handlerState := input.handlerState } := by
  simp [initialHandlerState, initialState]

/-- Runtime source-round schedule of a retained handler state. -/
def handlerRounds : QueryResult HandlerState → ℕ
  | none => 0
  | some state => state.source.remaining

/-- Return the final source output and private handler state together. The absent case is only the
total compiler fallback: exact retained runs finish in a present state. -/
def handlerOutput [Inhabited HandlerState] :
    QueryResult HandlerState → HandlerRunOutput HandlerState
  | none => { output := [], handlerState := default }
  | some state => { output := state.source.cfg.output, handlerState := state.handlerState }

@[simp]
theorem handlerOutput_some (state : RetainedState HandlerState) :
    handlerOutput (some state) =
      { output := state.source.cfg.output, handlerState := state.handlerState } :=
  rfl

/-- Local source commands advance the source state and preserve private handler state. -/
def localUpdate (input : RetainedState HandlerState × ICfg) : RetainedState HandlerState :=
  { source := input.1.source.advance input.2
    handlerState := input.1.handlerState }

@[simp]
theorem localUpdate_handlerState (input : RetainedState HandlerState × ICfg) :
    (localUpdate input).handlerState = input.1.handlerState :=
  rfl

/-- Marshal a selected source query and the retained private state into the installed-handler
boundary. The total local-command fallback is never executed because `bodyWithQueryBranch`
dispatches on the command tag before entering this artifact. -/
def handlerQueryInput (r : ℕ)
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
        handlerState := state.handlerState } :=
  rfl

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
    handlerCommandProgram r handler (state, .query operation request next pending) = do
      let result ← handler
        { operation
          request := encList encUnary request
          state := state.handlerState }
      let reply := result.reply.take state.source.replyBits
      let decoded := (frames reply).map List.length |>.take state.source.fuel
      let cfg := pending.receive operation next decoded
      pure (some
        { source := state.source.advance cfg
          handlerState := result.state }) := by
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
noncomputable def localHandlerOracle
    (handler : HandlerCall r HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (query : Fin r × List Bool) : StateT HandlerState ProbComp (List Bool) :=
  fun state => do
    let result ← (handler { operation := query.1, request := query.2, state }).run
      (fun impossible => impossible.1.elim0)
    pure (result.reply, result.state)

/-- The same handler lifted before closing its impossible external channel. This form is used to
compare the concrete retained controller with stateful interpretation of `NativeInterpreter.run`.
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
    rw [ProbOracleComp.sample_run_interpret]
    unfold runWithLocalHandler
    apply congrArg (fun oracle => (OracleComp.interpret oracle program).run state)
    funext query
    cases query with
    | inl n => rfl
    | inr query =>
        funext handlerState
        simp [localHandlerOracle, localHandlerProgram, sample_run_empty]
  calc
    _ = (ProbOracleComp.sample
        ((program.runState (localHandlerOracle handler)).run state)).run
          (fun impossible => impossible.1.elim0) :=
      congrArg (fun closed => closed.run (fun impossible => impossible.1.elim0)) hsample.symm
    _ = _ := ProbOracleComp.run_sample _ _

private noncomputable def retainedSourceCompiler
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler RetainedState.source (eRetainedState encHandlerState) eLoopState :=
  (NativeCompiler.first eLoopState encHandlerState).ofInputEq
    RetainedState.source fun _ => rfl

private noncomputable def localUpdateCompiler
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (localUpdate : RetainedState HandlerState × ICfg → RetainedState HandlerState)
      (encPair (eRetainedState encHandlerState) eICfg)
      (eRetainedState encHandlerState) := by
  let retained := NativeCompiler.first (eRetainedState encHandlerState) eICfg
  let source := (retainedSourceCompiler encHandlerState).comp retained
  let cfg := NativeCompiler.second (eRetainedState encHandlerState) eICfg
  let advanced := advanceCompiler.comp (source.pair cfg)
  let state := ((NativeCompiler.second eLoopState encHandlerState).ofInputEq
    RetainedState.handlerState fun _ => rfl).comp retained
  exact (advanced.pair state).ofOutputEq fun _ => rfl

private noncomputable def handlerQueryInputCompiler (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (handlerQueryInput r)
      (eRetainedCommandInput (r + 1) (eRetainedState encHandlerState))
      (eQueryInput (r + 1) encHandlerState) := by
  let retained := NativeCompiler.first (eRetainedState encHandlerState) (eCommand (r + 1))
  let source := (retainedSourceCompiler encHandlerState).comp retained
  let state := ((NativeCompiler.second eLoopState encHandlerState).ofInputEq
    RetainedState.handlerState fun _ => rfl).comp retained
  let payload := retainedCommandQueryPayloadCompiler (r + 1) 0
    (eRetainedState encHandlerState)
  let fields : NativeCompiler
      (fun input : RetainedCommandInput (r + 1) (RetainedState HandlerState) =>
        let payload := retainedCommandQueryPayload (r + 1) 0 input
        (payload.operation, payload.request, payload.next, payload.pending))
      (eRetainedCommandInput (r + 1) (eRetainedState encHandlerState))
      (encPair (eOperation (r + 1))
        (encPair (encList encUnary) (encPair encUnary eICfg))) :=
    ((NativeCompiler.identity
        (encPair (eOperation (r + 1))
          (encPair (encList encUnary) (encPair encUnary eICfg))))
      |>.ofInputEq
        (fun payload : RetainedQueryPayload (r + 1) =>
          (payload.operation, payload.request, payload.next, payload.pending))
        fun _ => rfl).comp payload
  let operation := (NativeCompiler.first (eOperation (r + 1))
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp fields
  let tail := (NativeCompiler.second (eOperation (r + 1))
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp fields
  let request := (NativeCompiler.first (encList encUnary)
    (encPair encUnary eICfg)).comp tail
  let nextCfg := (NativeCompiler.second (encList encUnary)
    (encPair encUnary eICfg)).comp tail
  let next := (NativeCompiler.first encUnary eICfg).comp nextCfg
  let pending := (NativeCompiler.second encUnary eICfg).comp nextCfg
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

/-- Exact command-boundary query time: marshalling, the actual retained handler branch and the
preprocessing composition overhead are all visible. -/
theorem time_handlerQueryArtifact (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (input : RetainedCommandInput (r + 1) (RetainedState HandlerState)) :
    (handlerQueryArtifact r encHandlerState handlerArtifact postOnline hpost).time input =
      5 * (handlerQueryInputCompiler r encHandlerState).time input +
        (queryBranch (r + 1) encHandlerState handlerArtifact postOnline hpost).time
          (handlerQueryInput r input) + 9 :=
  NativeOracleProgram.time_preprocess _ _

/-- Exact one-round semantics of the installed handler controller. -/
def handlerBodyProgram [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)) :
    QueryResult HandlerState → WordOracleComp (Fin 0) (QueryResult HandlerState) :=
  bodyProgramWithQueryBranch (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler)

@[simp]
theorem handlerBodyProgram_none [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)) :
    handlerBodyProgram r handler none = pure none :=
  bodyProgramWithQueryBranch_none (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler)

/-- Exhausted retained source storage stops before sampling or invoking the handler. -/
theorem handlerBodyProgram_exhausted [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (state : RetainedState HandlerState) (hremaining : state.source.remaining = 0) :
    handlerBodyProgram r handler (some state) = pure none :=
  bodyProgramWithQueryBranch_exhausted (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler) state hremaining

/-- A halted source advances locally while preserving the private handler state. -/
theorem handlerBodyProgram_halted [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (state : RetainedState HandlerState) (hremaining : state.source.remaining ≠ 0)
    (hcontrol : state.source.cfg.control = none) :
    handlerBodyProgram r handler (some state) =
      pure (some (localUpdate (state, state.source.cfg))) :=
  bodyProgramWithQueryBranch_halted (r + 1) RetainedState.source localUpdate
    (handlerCommandProgram r handler) state hremaining hcontrol

/-- Active retained storage uses exactly the shared fair-coin/lookup/command semantics. -/
theorem handlerBodyProgram_active [Inhabited HandlerState] (r : ℕ)
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
          StateT.run_bind, ProbOracleComp.interpret_sample, OracleComp.run_interpret_lift,
          bind_map_left]
        apply congrArg (ProbOracleComp.sample (ProbComp.uniform Bool) >>= ·)
        funext coin
        rw [commandAtFromLookup_firstMatch]
        cases hcommand : cfg.commandAt (r + 1) template.desc template.input coin with
        | local next =>
            simp [hcommand, localUpdate, withDynamicHandlerState, advance]
        | query operation request next pending =>
            rw [show handlerCommandProgram r handler
                (withDynamicHandlerState template (remaining + 1) cfg handlerState,
                  .query operation request next pending) = _ from
              handlerCommandProgram_query r handler _ operation request next pending]
            simp [hcommand, localHandlerProgram, withDynamicHandlerState, advance]
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
      simp only [runWithLocalHandler, OracleComp.interpret_bind, StateT.run_bind, map_bind]
      apply OracleComp.bind_congr_on_support
      rintro (nextCfg, nextHandlerState) -
      simpa only [Nat.succ_sub_one] using
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

/-- The complete installed one-round controller remains one composed description occurrence. -/
theorem handlerBodyArtifact_installedDescriptions [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) :
    (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).installedDescriptions =
      [(handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).description] :=
  NativeOracleProgram.installedDescriptions_eq_singleton _

/-- The one-round controller's exact installed charge is its final composed static size. -/
theorem handlerBodyArtifact_installedBits [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline) :
    (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).installedBits =
      (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).staticBits :=
  NativeOracleProgram.installedBits_eq_staticBits _

/-- Public proof obligations for retaining a runtime-bounded closed handler loop. The decoder and
invariant are proof data only. Every executed round is the concrete `handlerBodyArtifact`; its
componentwise time and workspace are bounded phase by phase, and the final stopping round must
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
  /-- Every reachable body workspace phase is charged by `roundOnline`. -/
  workspace : ∀ initial count, count ≤ handlerRounds initial → ∀ current,
    invariant initial count current → ∀ phase,
      (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).online.workspace
          phase current ≤ roundOnline.workspace phase initial
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
    { source := state.source.advance (pending.receive operation next
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
private noncomputable def finiteReachable [Fintype HandlerState] (r : ℕ)
    (initial : QueryResult HandlerState) : ℕ → List (QueryResult HandlerState)
  | 0 => [initial]
  | count + 1 =>
      (finiteSuccessors r initial).flatMap fun next => finiteReachable r next count

/-- All finitely enumerated retained states at indices used by the loop certificate. -/
private noncomputable def finiteReachablePrefix [Fintype HandlerState] (r : ℕ)
    (initial : QueryResult HandlerState) : List (QueryResult HandlerState) :=
  (List.range (handlerRounds initial + 1)).flatMap (finiteReachable r initial)

private theorem support_mem_finiteSuccessors [Fintype HandlerState] (r : ℕ)
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
          have hcoinValue : coin = false ∨ coin = true := by cases coin <;> simp
          rw [commandAtFromLookup_firstMatch] at hcommand
          cases hcmd : current.source.cfg.commandAt (r + 1) current.source.desc
              current.source.input coin with
          | local cfg =>
              simp only [hcmd, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                Prod.mk.injEq] at hcommand
              rcases hcommand with ⟨rfl, rfl⟩
              simp only [finiteSuccessors, hremaining, hcontrol, List.mem_flatMap,
                List.mem_cons, List.mem_singleton]
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
              simp only [finiteSuccessors, hremaining, hcontrol, List.mem_flatMap,
                List.mem_cons, List.mem_singleton]
              refine ⟨coin, hcoinValue, ?_⟩
              simp only [finiteCoinSuccessors, hcmd, List.mem_flatMap, List.mem_map]
              exact ⟨result.reply.take current.source.replyBits, hprefix,
                result.state, hstate, rfl⟩

private theorem mem_finiteReachable_succ [Fintype HandlerState]
    {r : ℕ} {initial current next : QueryResult HandlerState} {count : ℕ}
    (hcurrent : current ∈ finiteReachable r initial count)
    (hnext : next ∈ finiteSuccessors r current) :
    next ∈ finiteReachable r initial (count + 1) := by
  induction count generalizing initial with
  | zero =>
      simp only [finiteReachable, List.mem_singleton] at hcurrent
      subst current
      simp only [finiteReachable, List.mem_flatMap]
      exact ⟨next, hnext, by simp [finiteReachable]⟩
  | succ count ih =>
      simp only [finiteReachable, List.mem_flatMap] at hcurrent ⊢
      obtain ⟨middle, hmiddle, hcurrent⟩ := hcurrent
      exact ⟨middle, hmiddle, ih hcurrent hnext⟩

private theorem support_mem_finiteReachable [Fintype HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (initial : QueryResult HandlerState) (count : ℕ) (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (current : QueryResult HandlerState) (state' : OracleState)
    (hcurrent : (current, state') ∈
      (ProbOracleComp.runWith oracle
        (OracleComp.iterate count (handlerBodyProgram r handler) initial) state).support) :
    current ∈ finiteReachable r initial count := by
  induction count generalizing initial state current with
  | zero =>
      simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hcurrent
      rcases hcurrent with ⟨rfl, rfl⟩
      simp [finiteReachable]
  | succ count ih =>
      rw [OracleComp.iterate_succ_bind, ProbOracleComp.runWith_bind] at hcurrent
      obtain ⟨⟨middle, middleState⟩, hmiddle, htail⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp hcurrent
      simp only [finiteReachable, List.mem_flatMap]
      exact ⟨middle,
        support_mem_finiteSuccessors r handler initial middle OracleState oracle state middleState
          hmiddle,
        ih middle middleState current htail⟩

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
  · cases initial <;> simp [FiniteProgress, LoopState.SameStatic]
  · simp [finiteReachable]

private theorem finiteProgress_successor [Fintype HandlerState]
    {r : ℕ} {initial current next : QueryResult HandlerState} {count : ℕ}
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (hcount : count < handlerRounds initial)
    (hprogress : FiniteProgress initial count current) (OracleState : Type)
    (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (handlerBodyProgram r handler current) state).support) :
    FiniteProgress initial (count + 1) next := by
  cases hinitial : initial with
  | none => simp [handlerRounds, hinitial] at hcount
  | some first =>
      simp only [FiniteProgress, hinitial] at hprogress
      obtain ⟨second, rfl, hstatic, hremaining⟩ := hprogress
      have hpositive : second.source.remaining ≠ 0 := by omega
      cases hcontrol : second.source.cfg.control with
      | none =>
          rw [handlerBodyProgram_halted r handler second hpositive hcontrol] at hnext
          simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hnext
          rcases hnext with ⟨rfl, rfl⟩
          refine ⟨localUpdate (second, second.source.cfg), rfl, ?_, ?_⟩
          · exact ⟨hstatic.desc, hstatic.input, hstatic.fuel, hstatic.replyBits⟩
          · simp only [localUpdate, advance]
            omega
      | some control =>
          rw [handlerBodyProgram_active r handler second control hpositive hcontrol,
            activeProgramWithQueryBranch_apply, ProbOracleComp.runWith_bind] at hnext
          obtain ⟨⟨coin, coinState⟩, hcoin, hcommand⟩ :=
            (PMF.mem_support_bind_iff _ _ _).mp hnext
          rw [commandAtFromLookup_firstMatch] at hcommand
          cases hcmd : second.source.cfg.commandAt (r + 1) second.source.desc
              second.source.input coin with
          | local cfg =>
              simp only [hcmd, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                Prod.mk.injEq] at hcommand
              rcases hcommand with ⟨rfl, rfl⟩
              refine ⟨localUpdate (second, cfg), rfl, ?_, ?_⟩
              · exact ⟨hstatic.desc, hstatic.input, hstatic.fuel, hstatic.replyBits⟩
              · simp only [localUpdate, advance]
                omega
          | query operation request nextTag pending =>
              rw [hcmd, handlerCommandProgram_query, ProbOracleComp.runWith_bind] at hcommand
              obtain ⟨⟨result, resultState⟩, hresult, hfinal⟩ :=
                (PMF.mem_support_bind_iff _ _ _).mp hcommand
              simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                Prod.mk.injEq] at hfinal
              rcases hfinal with ⟨rfl, rfl⟩
              refine ⟨_, rfl, ?_, ?_⟩
              · exact ⟨hstatic.desc, hstatic.input, hstatic.fuel, hstatic.replyBits⟩
              · simp only [advance]
                omega

private theorem finiteInvariant_successor [Fintype HandlerState]
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
  refine ⟨⟨finiteProgress_successor handler hcount hinvariant.1 OracleState oracle state state'
    hnext, ?_⟩, ?_⟩
  · exact mem_finiteReachable_succ hinvariant.2
      (support_mem_finiteSuccessors r handler current next OracleState oracle state state' hnext)
  · obtain ⟨second, rfl, -, -⟩ := finiteProgress_successor handler hcount hinvariant.1
      OracleState oracle state state' hnext
    simp

private theorem finiteInvariant_last [Fintype HandlerState] (r : ℕ)
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
      simp only [FiniteProgress, hinitial] at hinvariant
      subst current
      simp
  | some first =>
      simp only [FiniteProgress, hinitial, handlerRounds] at hinvariant
      obtain ⟨second, rfl, hstatic, hremaining⟩ := hinvariant.1
      have hzero : second.source.remaining = 0 := by omega
      rw [handlerBodyProgram_exhausted r handler second hzero]
      simp

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
  workspace := fun phase initial =>
    listMax (fun current =>
      (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).online.workspace
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
  time := fun initial count hcount current hinvariant phase =>
    le_listMax (mem_finiteReachablePrefix hcount hinvariant.2)
  workspace := fun initial count hcount current hinvariant phase =>
    le_listMax (mem_finiteReachablePrefix hcount hinvariant.2)
  preserve := fun initial count hcount current hinvariant OracleState oracle state state' next
      hnext => finiteInvariant_successor handler hcount hinvariant OracleState oracle state state'
        hnext
  last := finiteInvariant_last r handler
  length := fun initial count hcount current hinvariant =>
    le_listMax (mem_finiteReachablePrefix hcount hinvariant.2)

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
    certificate.base certificate.time certificate.workspace certificate.preserve certificate.last
    certificate.length

/-- The retained loop is literally `iterateWhile` over the one reviewed handler body. -/
theorem machine_handlerLoopArtifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost certificate).machine =
      (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).machine.iterateWhile
        true :=
  NativeOracleProgram.machine_boundedIterationEncodedOn _ _ _ _ _ _ _ _ _ _ _ _

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
  NativeOracleProgram.time_boundedIterationEncodedOn _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The closed loop's one installed occurrence is the final composed `iterateWhile` description;
the body and query controls are inlined and are not listed again. -/
theorem handlerLoopArtifact_installedDescriptions [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost
      certificate).installedDescriptions =
        [(handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost
          certificate).description] :=
  NativeOracleProgram.installedDescriptions_eq_singleton _

/-- The typed loop's exact installed charge is its final composed static size. -/
theorem handlerLoopArtifact_installedBits [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost
      certificate).installedBits =
        (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost
          certificate).staticBits :=
  NativeOracleProgram.installedBits_eq_staticBits _

/-- Every certified body phase remains visible in the closed loop's peak workspace. Repetition
changes time, while workspace is a peak. -/
theorem handlerBodyWorkspace_le_loopWorkspace [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : LoopCertificate r encHandlerState handler handlerArtifact postOnline hpost)
    (initial : QueryResult HandlerState) (count : ℕ)
    (hcount : count ≤ handlerRounds initial) (current : QueryResult HandlerState)
    (hcurrent : certificate.invariant initial count current) (phase : OnlinePhase) :
    (handlerBodyArtifact r encHandlerState handlerArtifact postOnline hpost).online.workspace
        phase current ≤
      (handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost certificate).workspace
        initial :=
  NativeOracleProgram.bodyWorkspace_le_boundedIterationEncodedOn _ _ _ _ _ _ _ _ _ _ _ _
    initial count hcount current hcurrent phase

/-! ### Runtime preparation and final projection -/

/-- Actual retained compiler for runtime source initialization and private-state capture. -/
noncomputable def initialHandlerStateCompiler [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler (initialHandlerState r)
      (eHandlerRunInput encHandlerState) (eQueryResult encHandlerState) := by
  let sourceInput := (NativeCompiler.first eRunInput encHandlerState).ofInputEq
    HandlerRunInput.source fun _ => rfl
  let state := (NativeCompiler.second eRunInput encHandlerState).ofInputEq
    HandlerRunInput.handlerState fun _ => rfl
  let source := (initialCompiler r).comp sourceInput
  let retainedSource := (NativeCompiler.optionGetD default eLoopState).comp source
  let retained : NativeCompiler
      (fun input : HandlerRunInput HandlerState =>
        ({ source := (initialState r input.source).getD default
          handlerState := input.handlerState } : RetainedState HandlerState))
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
  let state := ((NativeCompiler.second eLoopState encHandlerState).ofInputEq
    RetainedState.handlerState fun _ => rfl).comp retained
  let result : NativeCompiler
      (fun input : QueryResult HandlerState =>
        ({ output := (input.getD default).source.cfg.output
          handlerState := (input.getD default).handlerState } :
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
  NativeOracleProgram.time_preprocess _ _

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
        runWithLocalHandler handler (NativeInterpreter.run (r + 1) input.source)
          input.handlerState := by
  by_cases hoperations : input.source.desc.operations = r + 1
  · rw [← congrFun (stagedRun_eq_run (r + 1)) input.source]
    simp only [handlerRunProgram, initializedHandlerProgram, handlerLoopProgram,
      initialHandlerState, initialState, hoperations, ↓reduceIte, stagedRun,
      handlerRounds, rounds]
    rw [show
      { source :=
          { desc := input.source.desc
            input := input.source.input
            fuel := input.source.fuel
            replyBits := input.source.replyBits
            remaining := input.source.fuel
            cfg := ICfg.init input.source.desc }
        handlerState := input.handlerState } =
        withDynamicHandlerState
          { desc := input.source.desc
            input := input.source.input
            fuel := input.source.fuel
            replyBits := input.source.replyBits
            remaining := input.source.fuel
            cfg := ICfg.init input.source.desc }
          input.source.fuel (ICfg.init input.source.desc) input.handlerState by rfl]
    rw [show
      { desc := input.source.desc
        input := input.source.input
        fuel := input.source.fuel
        replyBits := input.source.replyBits
        remaining := input.source.fuel
        cfg := ICfg.init input.source.desc } =
        LoopState.withDynamic
          { desc := input.source.desc
            input := input.source.input
            fuel := input.source.fuel
            replyBits := input.source.replyBits
            remaining := input.source.fuel
            cfg := ICfg.init input.source.desc }
          input.source.fuel (ICfg.init input.source.desc) by rfl]
    rw [handlerIterate_withDynamic, iterate_step_withDynamic]
    simp [runWithLocalHandler, handlerOutput, output, withDynamicHandlerState]
  · simp [handlerRunProgram, initializedHandlerProgram, handlerLoopProgram,
      initialHandlerState, initialState, hoperations, handlerRounds,
      handlerOutput, NativeInterpreter.run, runWithLocalHandler]

/-- **Exact retained local-handler semantics.** Closing the impossible external channel of the
constructed program gives the complete `NativeInterpreter.runState` computation: malformed
operation counts return `[]` and preserve the initial handler state, while valid runs return the
source output beside the handler's actual final state. -/
theorem run_handlerRunProgram_eq_runState [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState) :
    (handlerRunProgram r handler input).run (fun impossible => impossible.1.elim0) =
      (fun result =>
        ({ output := result.1, handlerState := result.2 } : HandlerRunOutput HandlerState)) <$>
        ((NativeInterpreter.run (r + 1) input.source).runState
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
    handlerOutput]

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
owns reachability and body bounds; this record adds only the support-local final projection bound. -/
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
            outputOnline.time phase input ∧
          (ClassifiedCompiler.inPhase .outputCopy
              (handlerOutputCompiler encHandlerState)).online.workspace phase current ≤
            outputOnline.workspace phase input

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
  workspace := fun phase input =>
    listMax (fun current =>
      (ClassifiedCompiler.inPhase .outputCopy
        (handlerOutputCompiler encHandlerState)).online.workspace phase current)
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
    exact ⟨le_listMax hreach, le_listMax hreach⟩

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

/-- The complete machine contains exactly input initialization, one typed iteration of the shared
handler body, and final output projection. No parallel controller or semantic callback is hidden. -/
theorem machine_artifact [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    (artifact r encHandlerState handlerArtifact postOnline hpost certificate).machine =
      (ofDeterministic
        (ClassifiedCompiler.inPhase .outputCopy
          (handlerOutputCompiler encHandlerState)).compiler.machine).tidyComp
        ((handlerLoopArtifact r encHandlerState handlerArtifact postOnline hpost
          certificate.loop).machine.tidyComp
            (ofDeterministic
              (ClassifiedCompiler.inPhase .inputCopy
                (initialHandlerStateCompiler (r + 1) encHandlerState)).compiler.machine) true) true :=
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

/-- Direct clean-phase certificate for the complete output-plus-final-state law. -/
theorem artifact_computes [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost)
    (input : HandlerRunInput HandlerState) :
    (artifact r encHandlerState handlerArtifact postOnline hpost certificate).machine.ComputesTidily
      (eHandlerRunInput encHandlerState input)
      ((artifact r encHandlerState handlerArtifact postOnline hpost certificate).time input)
      ((eHandlerRunOutput encHandlerState) <$> handlerRunProgram r handler input) :=
  (artifact r encHandlerState handlerArtifact postOnline hpost certificate).computes input

/-- Exact stateful distribution equality for the clocked closed machine. The impossible external
operation channel is retained in the statement only to use the common machine semantics. -/
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
      ProbOracleComp.runWith oracle
        ((eHandlerRunOutput encHandlerState) <$> handlerRunProgram r handler input)
        state :=
  (artifact_computes r encHandlerState handlerArtifact postOnline hpost certificate input).runOracle
    oracle state

/-- The final composed closed artifact occurs once. Input/output compilers, handler body, query
branch and loop control are inlined and are not separately installed occurrences. -/
theorem artifact_installedDescriptions [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    (artifact r encHandlerState handlerArtifact postOnline hpost
      certificate).installedDescriptions =
        [(artifact r encHandlerState handlerArtifact postOnline hpost certificate).description] :=
  NativeOracleProgram.installedDescriptions_eq_singleton _

/-- Exact occurrence-sensitive static charge of the complete closed artifact. -/
theorem artifact_installedBits [Inhabited HandlerState] (r : ℕ)
    (encHandlerState : HandlerState ↪ List Bool)
    {handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState)}
    (handlerArtifact : NativeOracleProgram 0 handler
      (eHandlerCall (r + 1) encHandlerState) (eHandlerResult encHandlerState))
    (postOnline : OnlineAccounting (QueryInput (r + 1) HandlerState))
    (hpost : PostBound (r + 1) encHandlerState handler postOnline)
    (certificate : RunCertificate r encHandlerState handler handlerArtifact postOnline hpost) :
    (artifact r encHandlerState handlerArtifact postOnline hpost certificate).installedBits =
      (artifact r encHandlerState handlerArtifact postOnline hpost certificate).staticBits :=
  NativeOracleProgram.installedBits_eq_staticBits _

end Turing.MultiTapePTM.Universal.NativeHandler

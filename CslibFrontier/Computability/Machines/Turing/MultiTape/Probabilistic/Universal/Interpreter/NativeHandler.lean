/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Interpreter.Native

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

/-- Optional stored state consumed by the retained closed loop. Absence records a malformed
channel-count boundary and is also the loop terminator. -/
abbrev HandlerLoopState (HandlerState : Type) := Option (RetainedState HandlerState)

/-- Encoding of the complete optional source-and-handler loop state. -/
def eHandlerLoopState (encHandlerState : HandlerState ↪ List Bool) :
    HandlerLoopState HandlerState ↪ List Bool :=
  encOption (eRetainedState encHandlerState)

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
runtime operation count remains the explicit absent state. -/
def initialHandlerState (r : ℕ) (input : HandlerRunInput HandlerState) :
    HandlerLoopState HandlerState :=
  (initialState r input.source).map fun source =>
    { source, handlerState := input.handlerState }

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
      else none := by
  simp [initialHandlerState, initialState]

/-- Runtime source-round schedule of a retained handler state. -/
def handlerRounds : HandlerLoopState HandlerState → ℕ
  | none => 0
  | some state => state.source.remaining

/-- Return the final source output and private handler state together. An absent malformed run has
no fabricated handler result. -/
def handlerOutput : HandlerLoopState HandlerState → Option (HandlerRunOutput HandlerState)
  | none => none
  | some state => some { output := state.source.cfg.output, handlerState := state.handlerState }

@[simp]
theorem handlerOutput_some (state : RetainedState HandlerState) :
    handlerOutput (some state) =
      some { output := state.source.cfg.output, handlerState := state.handlerState } :=
  rfl

/-- Local source commands advance the source state and preserve private handler state. -/
def localUpdate (input : RetainedState HandlerState × ICfg) : RetainedState HandlerState :=
  { source := input.1.source.advance input.2
    handlerState := input.1.handlerState }

@[simp]
theorem localUpdate_handlerState (input : RetainedState HandlerState × ICfg) :
    (localUpdate input).handlerState = input.1.handlerState :=
  rfl

private abbrev HandlerCommandPayload (r : ℕ) :=
  Fin r × (List ℕ × (ℕ × ICfg))

private def eHandlerCommandPayload (r : ℕ) : HandlerCommandPayload r ↪ List Bool :=
  encPair (eOperation r) (encPair (encList encUnary) (encPair encUnary eICfg))

private def defaultHandlerCommandPayload (r : ℕ) : HandlerCommandPayload (r + 1) :=
  (0, [], 0, default)

private def handlerCommandPayload (r : ℕ)
    (input : RetainedCommandInput (r + 1) (RetainedState HandlerState)) :
    HandlerCommandPayload (r + 1) :=
  Sum.elim (Function.const ICfg (defaultHandlerCommandPayload r)) id
    (Command.equivSum (r + 1) input.2)

/-- Marshal a selected source query and the retained private state into the installed-handler
boundary. The total local-command fallback is never executed because `bodyWithQueryBranch`
dispatches on the command tag before entering this artifact. -/
def handlerQueryInput (r : ℕ)
    (input : RetainedCommandInput (r + 1) (RetainedState HandlerState)) :
    QueryInput (r + 1) HandlerState :=
  let payload := handlerCommandPayload r input
  { source := input.1.source
    operation := payload.1
    request := payload.2.1
    next := payload.2.2.1
    pending := payload.2.2.2
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
    WordOracleComp (Fin 0) (HandlerLoopState HandlerState) :=
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
  let command := NativeCompiler.second (eRetainedState encHandlerState) (eCommand (r + 1))
  let commandSum :=
    (NativeCompiler.identity (encSum eICfg (eHandlerCommandPayload (r + 1)))).ofInputEq
      (Command.equivSum (r + 1)) fun _ => rfl
  let payload := (NativeCompiler.sumRightD (defaultHandlerCommandPayload r)
    eICfg (eHandlerCommandPayload (r + 1))).comp (commandSum.comp command)
  let operation := (NativeCompiler.first (eOperation (r + 1))
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp payload
  let tail := (NativeCompiler.second (eOperation (r + 1))
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp payload
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
      (eHandlerLoopState encHandlerState) :=
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
    HandlerLoopState HandlerState → WordOracleComp (Fin 0) (HandlerLoopState HandlerState) :=
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
      (eHandlerLoopState encHandlerState) (eHandlerLoopState encHandlerState) :=
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
  lengthBound : HandlerLoopState HandlerState → ℕ
  /-- Phasewise maximum of one concrete handler body on the certified reachable prefix. -/
  roundOnline : OnlineAccounting (HandlerLoopState HandlerState)
  /-- Reachability and progress invariant indexed by completed source rounds. -/
  invariant : HandlerLoopState HandlerState → ℕ → HandlerLoopState HandlerState → Prop
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
      (state state' : OracleState) (next : HandlerLoopState HandlerState),
      (next, state') ∈
          (ProbOracleComp.runWith oracle (handlerBodyProgram r handler current) state).support →
        invariant initial (count + 1) next ∧ eHandlerLoopState encHandlerState next ≠ []
  /-- The additional stopping round emits the empty option word. -/
  last : ∀ initial current, invariant initial (handlerRounds initial) current →
    ∀ (OracleState : Type)
      (oracle : Fin 0 × List Bool → StateT OracleState PMF (List Bool))
      (state : OracleState),
      ProbOracleComp.runWith oracle
          (eHandlerLoopState encHandlerState <$> handlerBodyProgram r handler current) state =
        ProbOracleComp.runWith oracle (pure []) state
  /-- Every invariant-reachable encoded state fits `lengthBound`. -/
  length : ∀ initial count, count ≤ handlerRounds initial → ∀ current,
    invariant initial count current →
      (eHandlerLoopState encHandlerState current).length ≤ lengthBound initial

/-- Exact closed loop semantics before runtime initialization and final-output projection. -/
noncomputable def handlerLoopProgram [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (initial : HandlerLoopState HandlerState) :
    WordOracleComp (Fin 0) (HandlerLoopState HandlerState) :=
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
      (eHandlerLoopState encHandlerState) (eHandlerLoopState encHandlerState) :=
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
    (initial : HandlerLoopState HandlerState) :
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
    (initial : HandlerLoopState HandlerState) (count : ℕ)
    (hcount : count ≤ handlerRounds initial) (current : HandlerLoopState HandlerState)
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
      (eHandlerRunInput encHandlerState) (eHandlerLoopState encHandlerState) := by
  let sourceInput := (NativeCompiler.first eRunInput encHandlerState).ofInputEq
    HandlerRunInput.source fun _ => rfl
  let state := (NativeCompiler.second eRunInput encHandlerState).ofInputEq
    HandlerRunInput.handlerState fun _ => rfl
  let source := (initialCompiler r).comp sourceInput
  let condition := (NativeCompiler.optionIsSomeTest eLoopState).comp source
  let retainedSource := (NativeCompiler.optionGetD default eLoopState).comp source
  let retained : NativeCompiler
      (fun input : HandlerRunInput HandlerState =>
        ({ source := (initialState r input.source).getD default
          handlerState := input.handlerState } : RetainedState HandlerState))
      (eHandlerRunInput encHandlerState) (eRetainedState encHandlerState) :=
    (retainedSource.pair state).ofOutputEq fun _ => rfl
  let present := (NativeCompiler.optionSome (eRetainedState encHandlerState)).comp retained
  let absent := NativeCompiler.const (eHandlerRunInput encHandlerState)
    (eHandlerLoopState encHandlerState) none
  exact (NativeCompiler.ite condition present absent).ofOutputEq fun input => by
    cases hsource : initialState r input.source <;>
      simp [initialHandlerState, hsource]

/-- Retained compiler for the complete optional output/final-handler-state projection. -/
noncomputable def handlerOutputCompiler [Inhabited HandlerState]
    (encHandlerState : HandlerState ↪ List Bool) :
    NativeCompiler handlerOutput (eHandlerLoopState encHandlerState)
      (encOption (eHandlerRunOutput encHandlerState)) := by
  let condition := NativeCompiler.optionIsSomeTest (eRetainedState encHandlerState)
  let retained := NativeCompiler.optionGetD default (eRetainedState encHandlerState)
  let source := (retainedSourceCompiler encHandlerState).comp retained
  let cfg := cfgCompiler.comp source
  let output := ICfg.outputCompiler.comp cfg
  let state := ((NativeCompiler.second eLoopState encHandlerState).ofInputEq
    RetainedState.handlerState fun _ => rfl).comp retained
  let result : NativeCompiler
      (fun input : HandlerLoopState HandlerState =>
        ({ output := (input.getD default).source.cfg.output
          handlerState := (input.getD default).handlerState } :
          HandlerRunOutput HandlerState))
      (eHandlerLoopState encHandlerState) (eHandlerRunOutput encHandlerState) :=
    (output.pair state).ofOutputEq fun _ => rfl
  let present := (NativeCompiler.optionSome (eHandlerRunOutput encHandlerState)).comp result
  let absent := NativeCompiler.const (eHandlerLoopState encHandlerState)
    (encOption (eHandlerRunOutput encHandlerState)) none
  exact (NativeCompiler.ite condition present absent).ofOutputEq fun input => by
    cases input <;> rfl

/-- Semantics after retained runtime initialization, before final-output projection. -/
noncomputable def initializedHandlerProgram [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState) :
    WordOracleComp (Fin 0) (HandlerLoopState HandlerState) :=
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
      (eHandlerRunInput encHandlerState) (eHandlerLoopState encHandlerState) :=
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
    WordOracleComp (Fin 0) (Option (HandlerRunOutput HandlerState)) :=
  handlerOutput <$> initializedHandlerProgram r handler input

/-- A malformed runtime operation count produces no fabricated output or handler state. -/
theorem handlerRunProgram_malformed [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState)
    (hoperations : input.source.desc.operations ≠ r + 1) :
    handlerRunProgram r handler input = pure none := by
  simp [handlerRunProgram, initializedHandlerProgram, handlerLoopProgram,
    initialHandlerState, initialState, hoperations, handlerRounds, handlerOutput]

/-- A valid zero-clock run performs no body round and returns the initialized source output beside
the unchanged private handler state. -/
theorem handlerRunProgram_zero_fuel [Inhabited HandlerState] (r : ℕ)
    (handler : HandlerCall (r + 1) HandlerState →
      WordOracleComp (Fin 0) (HandlerResult HandlerState))
    (input : HandlerRunInput HandlerState)
    (hoperations : input.source.desc.operations = r + 1)
    (hfuel : input.source.fuel = 0) :
    handlerRunProgram r handler input =
      pure (some
        { output := (ICfg.init input.source.desc).output
          handlerState := input.handlerState }) := by
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
    (state : OracleState) (current : HandlerLoopState HandlerState) (state' : OracleState),
    (current, state') ∈
        (ProbOracleComp.runWith oracle (initializedHandlerProgram r handler input) state).support →
      ∀ phase,
        (ClassifiedCompiler.inPhase .outputCopy
            (handlerOutputCompiler encHandlerState)).online.time phase current ≤
            outputOnline.time phase input ∧
          (ClassifiedCompiler.inPhase .outputCopy
              (handlerOutputCompiler encHandlerState)).online.workspace phase current ≤
            outputOnline.workspace phase input

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
      (encOption (eHandlerRunOutput encHandlerState)) :=
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
      ((encOption (eHandlerRunOutput encHandlerState)) <$> handlerRunProgram r handler input) :=
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
        ((encOption (eHandlerRunOutput encHandlerState)) <$> handlerRunProgram r handler input)
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

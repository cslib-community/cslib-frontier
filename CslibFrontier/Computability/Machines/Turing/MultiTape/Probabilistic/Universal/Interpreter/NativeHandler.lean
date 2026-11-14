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

end Turing.MultiTapePTM.Universal.NativeHandler

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Interpreter.NativeHandler

/-! Ordinary-import boundary client for a closed retained stateful handler and its typed loop. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.NativeHandler

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM
  Turing.MultiTapeTM.Internal Turing.MultiTapePTM.Internal
open Turing.MultiTapePTM.Universal
open Turing.MultiTapePTM.Universal.NativeInterpreter
open Turing.MultiTapePTM.Universal.NativeHandler

/-- A nonconstant retained handler: every request receives the raw all-false unary word, while the
private Boolean state is preserved and therefore remains input-dependent. -/
def falseHandler (call : HandlerCall 1 Bool) :
    WordOracleComp (Fin 0) (HandlerResult Bool) :=
  pure { reply := [false], state := call.state }

private noncomputable def falseHandlerCompiler :
    NativeCompiler (fun call : HandlerCall 1 Bool =>
      ({ reply := [false], state := call.state } : HandlerResult Bool))
      (eHandlerCall 1 encBool) (eHandlerResult encBool) := by
  let tail : NativeCompiler (fun call : HandlerCall 1 Bool => (call.request, call.state))
      (eHandlerCall 1 encBool) (encPair encBits encBool) :=
    (NativeCompiler.second (eOperation 1) (encPair encBits encBool)).ofInputEq
      (fun call : HandlerCall 1 Bool => (call.request, call.state)) fun _ => rfl
  let state := (NativeCompiler.second encBits encBool).comp tail
  let reply := NativeCompiler.const (eHandlerCall 1 encBool) encBits [false]
  exact (reply.pair state).ofOutputEq fun _ => rfl

/-- The fixture is an actual closed retained machine, not a semantic handler assumption. -/
noncomputable def falseHandlerArtifact :
    NativeOracleProgram 0 falseHandler (eHandlerCall 1 encBool) (eHandlerResult encBool) :=
  NativeOracleProgram.ofCompiler (r := 0)
    (ClassifiedCompiler.inPhase .localStep falseHandlerCompiler)

/-- Public handler-run encodings retain their documented source/state and output/state layouts. -/
example (input : HandlerRunInput Bool) (output : HandlerRunOutput Bool) :
    eHandlerRunInput encBool input = encPair eRunInput encBool (input.source, input.handlerState) ∧
      eHandlerRunOutput encBool output =
        encPair (encList encUnary) encBool (output.output, output.handlerState) :=
  ⟨rfl, rfl⟩

/-- The shared retained-command query view exposes the exact selected fields, and its compiler
retains the documented payload encoding. -/
example (state : RetainedState Bool) (request : List ℕ) (next : ℕ) (pending : ICfg) :
    retainedCommandQueryPayload 1 0 (state, .query 0 request next pending) =
        { operation := 0, request, next, pending } ∧
      (retainedCommandQueryPayloadCompiler 1 0 (eRetainedState encBool)).outputBits
          (state, .query 0 request next pending) =
        (eRetainedQueryPayload 1 { operation := 0, request, next, pending }).length :=
  ⟨rfl, rfl⟩

/-- Replacing the former tuple payload with named fields preserves every encoded word. -/
example (payload : RetainedQueryPayload 1) :
    eRetainedQueryPayload 1 payload =
      encPair (eOperation 1) (encPair (encList encUnary) (encPair encUnary eICfg))
        (payload.operation, payload.request, payload.next, payload.pending) :=
  rfl

/-- The actual query boundary preserves the selected request and private state. -/
example (state : RetainedState Bool) (request : List ℕ) (next : ℕ) (pending : ICfg) :
    handlerQueryInput 0 (state, .query 0 request next pending) =
      { source := state.source
        operation := 0
        request
        next
        pending
        handlerState := state.handlerState } :=
  handlerQueryInput_query 0 state 0 request next pending

/-- Exact reply-installer ledger for the sole result returned by `falseHandler`. -/
noncomputable def falsePostOnline : OnlineAccounting (QueryInput 1 Bool) where
  time := fun phase input =>
    (installReplyArtifact 0 1 encBool).online.time phase
      (input, { reply := [false], state := input.handlerState })
  workspace := fun phase input =>
    (installReplyArtifact 0 1 encBool).online.workspace phase
      (input, { reply := [false], state := input.handlerState })

/-- The exact ledger bounds every supported result of the concrete handler. -/
theorem falsePostBound : PostBound 1 encBool falseHandler falsePostOnline := by
  intro input OracleState oracle state result state' hresult phase
  simp only [falseHandler, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  exact ⟨le_rfl, le_rfl⟩

/-- The finite Boolean private state supplies an actual loop certificate. -/
noncomputable def falseLoopCertificate :
    LoopCertificate 0 encBool falseHandler falseHandlerArtifact falsePostOnline falsePostBound :=
  finiteLoopCertificate 0 encBool Decoder.bool falseHandlerArtifact falsePostOnline falsePostBound

/-- The complete output certificate is constructed rather than assumed. -/
noncomputable def falseRunCertificate :
    RunCertificate 0 encBool falseHandler falseHandlerArtifact falsePostOnline falsePostBound :=
  finiteRunCertificate 0 encBool Decoder.bool falseHandlerArtifact falsePostOnline falsePostBound

/-- The ordinary importer reaches the one shared stateful body and its exact singleton installed
inventory without referring to private controller helpers. -/
example :
    (handlerBodyArtifact 0 encBool falseHandlerArtifact falsePostOnline
      falsePostBound).installedDescriptions =
      [(handlerBodyArtifact 0 encBool falseHandlerArtifact falsePostOnline
        falsePostBound).description] :=
  handlerBodyArtifact_installedDescriptions 0 encBool falseHandlerArtifact falsePostOnline
    falsePostBound

/-- The typed full loop is the literal iteration of that same body. -/
example :
    (handlerLoopArtifact 0 encBool falseHandlerArtifact falsePostOnline falsePostBound
      falseLoopCertificate).machine =
        (handlerBodyArtifact 0 encBool falseHandlerArtifact falsePostOnline
          falsePostBound).machine.iterateWhile true :=
  machine_handlerLoopArtifact 0 encBool falseHandlerArtifact falsePostOnline falsePostBound
    falseLoopCertificate

/-- The final closed artifact has no external operation channel and charges the composed
description once rather than adding its inlined handler, body and loop controls again. -/
example :
    (Turing.MultiTapePTM.Universal.NativeHandler.artifact 0 encBool falseHandlerArtifact
      falsePostOnline falsePostBound falseRunCertificate).installedBits =
      (Turing.MultiTapePTM.Universal.NativeHandler.artifact 0 encBool falseHandlerArtifact
        falsePostOnline falsePostBound falseRunCertificate).staticBits :=
  artifact_installedBits 0 encBool falseHandlerArtifact falsePostOnline falsePostBound
    falseRunCertificate

/-- A valid one-operation description whose first instruction queries its sole channel for either
private coin. -/
def positiveQueryDesc : Desc :=
  let base : Desc := ⟨0, 2, 1, 0, []⟩
  let cfg := ICfg.init base
  let branches : Branches := ⟨.query 0 1, .query 0 1⟩
  { base with table := [(cfg.key [] 0, branches)] }

/-- Concrete valid runtime input with positive fuel and a nondefault initial handler state. -/
def positiveRunInput : HandlerRunInput Bool :=
  { source := { desc := positiveQueryDesc, fuel := 1, input := [], replyBits := 1 }
    handlerState := true }

/-- The positive runtime input really initializes one retained source round. -/
example : handlerRounds (initialHandlerState 1 positiveRunInput) = 1 := by
  decide

/-- The positive-fuel fixture reaches a query for either private coin, so the concrete closed body
cannot discharge this client through only its stopped or local branch. -/
example (coin : Bool) :
    match (ICfg.init positiveQueryDesc).commandAt 1 positiveQueryDesc [] coin with
    | .query operation request _ _ => operation = 0 ∧ request = []
    | .local _ => False := by
  cases coin <;> decide

/-- The concrete complete program therefore has a positive-fuel execution that enters the locally
installed handler branch, while remaining a closed `Fin 0` oracle program. -/
noncomputable def positiveClosedRun : WordOracleComp (Fin 0) (HandlerRunOutput Bool) :=
  handlerRunProgram 0 falseHandler positiveRunInput

/-- The positive-fuel client reaches the public complete `runState` law, including its final
Boolean handler state. -/
example :
    positiveClosedRun.run (fun impossible => impossible.1.elim0) =
      (fun result =>
        ({ output := result.1, handlerState := result.2 } : HandlerRunOutput Bool)) <$>
        ((Turing.MultiTapePTM.Universal.NativeInterpreter.run 1 positiveRunInput.source).runState
          (localHandlerOracle falseHandler)).run positiveRunInput.handlerState :=
  run_handlerRunProgram_eq_runState 0 falseHandler positiveRunInput

/-- The constructed final artifact is inhabited for the same concrete locally installed handler. -/
noncomputable def falseFinalArtifact :
    NativeOracleProgram 0 (handlerRunProgram 0 falseHandler)
      (eHandlerRunInput encBool) (eHandlerRunOutput encBool) :=
  Turing.MultiTapePTM.Universal.NativeHandler.artifact 0 encBool falseHandlerArtifact
    falsePostOnline falsePostBound falseRunCertificate

end CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.NativeHandler

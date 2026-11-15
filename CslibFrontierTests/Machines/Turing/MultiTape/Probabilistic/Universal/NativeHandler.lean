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

section CertifiedLoop

variable (postOnline : OnlineAccounting (QueryInput 1 Bool))
variable (hpost : PostBound 1 encBool falseHandler postOnline)
variable (loopCertificate :
  LoopCertificate 0 encBool falseHandler falseHandlerArtifact postOnline hpost)

/-- The ordinary importer reaches the one shared stateful body and its exact singleton installed
inventory without referring to private controller helpers. -/
example :
    (handlerBodyArtifact 0 encBool falseHandlerArtifact postOnline hpost).installedDescriptions =
      [(handlerBodyArtifact 0 encBool falseHandlerArtifact postOnline hpost).description] :=
  handlerBodyArtifact_installedDescriptions 0 encBool falseHandlerArtifact postOnline hpost

/-- The typed full loop is the literal iteration of that same body. -/
example :
    (handlerLoopArtifact 0 encBool falseHandlerArtifact postOnline hpost
      loopCertificate).machine =
        (handlerBodyArtifact 0 encBool falseHandlerArtifact postOnline hpost).machine.iterateWhile
          true :=
  machine_handlerLoopArtifact 0 encBool falseHandlerArtifact postOnline hpost loopCertificate

variable (runCertificate :
  RunCertificate 0 encBool falseHandler falseHandlerArtifact postOnline hpost)

/-- The final closed artifact has no external operation channel and charges the composed
description once rather than adding its inlined handler, body and loop controls again. -/
example :
    (Turing.MultiTapePTM.Universal.NativeHandler.artifact 0 encBool falseHandlerArtifact
      postOnline hpost runCertificate).installedBits =
      (Turing.MultiTapePTM.Universal.NativeHandler.artifact 0 encBool falseHandlerArtifact
        postOnline hpost runCertificate).staticBits :=
  artifact_installedBits 0 encBool falseHandlerArtifact postOnline hpost runCertificate

end CertifiedLoop

end CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.NativeHandler

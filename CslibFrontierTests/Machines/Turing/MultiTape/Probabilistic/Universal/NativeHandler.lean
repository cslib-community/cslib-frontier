/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.NativeHandler
import CslibFrontier.Foundations.Control.Monad.StateT

/-! Ordinary-import boundary client for a closed retained stateful handler and its typed loop. -/

-- This ordinary-import test keeps its concrete machines and inputs private.
set_option linter.privateModule false


namespace CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.NativeHandler

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM
  Turing.MultiTapeTM.Internal Turing.MultiTapePTM.Internal
open Turing.MultiTapePTM.Universal
open Turing.MultiTapePTM.Universal.NativeInterpreter
open Turing.MultiTapePTM.Universal.NativeHandler

/-- A nonconstant retained handler: every request receives the raw all-false unary word, while the
private Boolean state is flipped on each call. -/
private def falseHandler (call : HandlerCall 1 Bool) :
    WordOracleComp (Fin 0) (HandlerResult Bool) :=
  pure { reply := [false], state := !call.state }

private noncomputable def falseHandlerCompiler :
    NativeCompiler (fun call : HandlerCall 1 Bool =>
      ({ reply := [false], state := !call.state } : HandlerResult Bool))
      (eHandlerCall 1 encBool) (eHandlerResult encBool) := by
  let tail : NativeCompiler (fun call : HandlerCall 1 Bool => (call.request, call.state))
      (eHandlerCall 1 encBool) (encPair encBits encBool) :=
    (NativeCompiler.second (eOperation 1) (encPair encBits encBool)).ofInputEq
      (fun call : HandlerCall 1 Bool => (call.operation, call.request, call.state)) fun _ => rfl
  let state := (NativeCompiler.second encBits encBool).comp tail
  let reply := NativeCompiler.const (eHandlerCall 1 encBool) encBits [false]
  let yes := NativeCompiler.const (eHandlerCall 1 encBool) encBool false
  let no := NativeCompiler.const (eHandlerCall 1 encBool) encBool true
  let flipped := NativeCompiler.ite (NativeCompiler.boolToTest.comp state) yes no
  exact (reply.pair flipped).ofOutputEq fun call => by cases call.state <;> rfl

/-- The fixture is an actual closed retained machine, not a semantic handler assumption. -/
private noncomputable def falseHandlerArtifact :
    NativeOracleProgram 0 falseHandler (eHandlerCall 1 encBool) (eHandlerResult encBool) :=
  NativeOracleProgram.ofCompiler (r := 0)
    (ClassifiedCompiler.inPhase .localStep falseHandlerCompiler)

/-- Initialization captures the supplied private state for any encoded type. -/
noncomputable example {α : Type} (enc : α ↪ List Bool) (r : ℕ) :
    NativeCompiler (initialHandlerState r) (eHandlerRunInput enc) (eQueryResult enc) :=
  initialHandlerStateCompiler r enc

/-- Public handler-run encodings retain their documented source/state and output/state layouts. -/
example (input : HandlerRunInput Bool) (output : HandlerRunOutput Bool) :
    eHandlerRunInput encBool input = encPair eRunInput encBool (input.source, input.handlerState) ∧
      eHandlerRunOutput encBool output =
        encPair (encList encUnary) encBool (output.output, output.handlerState) :=
  ⟨rfl, rfl⟩

/-- Handler request, result and in-loop state preserve the original right-nested tuple bytes. -/
example (call : HandlerCall 1 Bool) (result : HandlerResult Bool) (state : RetainedState Bool) :
    eHandlerCall 1 encBool call = encPair (eOperation 1) (encPair encBits encBool)
        (call.operation, call.request, call.state) ∧
      eHandlerResult encBool result = encPair encBits encBool (result.reply, result.state) ∧
      eRetainedState encBool state =
        encPair eLoopState encBool (state.source, state.handlerState) :=
  ⟨rfl, rfl, rfl⟩

/-- The shared retained-command query view exposes the exact selected fields, and its compiler
retains the documented payload encoding. -/
example (state : RetainedState Bool) (request : List ℕ) (next : ℕ) (pending : ICfg) :
    retainedCommandQueryPayload 1 0 (state, .query 0 request next pending) =
        { operation := 0, request, next, pending } ∧
      (retainedCommandQueryPayloadCompiler 1 0 (eRetainedState encBool)).outputBits
          (state, .query 0 request next pending) =
        (eRetainedQueryPayload 1 { operation := 0, request, next, pending }).length :=
  ⟨retainedCommandQueryPayload_query _ _ _ _ _ _, by
    simp only [NativeCompiler.outputBits, retainedCommandQueryPayload_query]⟩

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
private noncomputable def falsePostOnline : OnlineAccounting (QueryInput 1 Bool) where
  time := fun phase input =>
    (installReplyArtifact 0 1 encBool).online.time phase
      (input, { reply := [false], state := !input.handlerState })

/-- The exact ledger bounds every supported result of the concrete handler. -/
private theorem falsePostBound : PostBound 1 encBool falseHandler falsePostOnline := by
  intro input OracleState oracle state result state' hresult phase
  simp only [falseHandler, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hresult
  rcases hresult with ⟨rfl, rfl⟩
  exact Nat.le_refl _

/-- The complete output certificate is constructed rather than assumed. -/
private noncomputable def falseRunCertificate :
    RunCertificate 0 encBool falseHandler falseHandlerArtifact falsePostOnline falsePostBound :=
  finiteRunCertificate 0 encBool Decoder.bool falseHandlerArtifact falsePostOnline falsePostBound

/-- The canonical raw-prefix compiler handles an empty prefix and a count larger than the word. -/
example : NativeCompiler.takeBits.time ([true, false], 0) = 383 ∧
    NativeCompiler.takeBits.workspace ([true, false], 7) = 509 := by
  constructor
  · rw [NativeCompiler.time_takeBits_expanded]
    decide
  · rw [NativeCompiler.workspace_takeBits_expanded]
    decide

/-- A valid one-operation description whose first instruction queries its sole channel for either
private coin. -/
private def positiveQueryDesc : Desc :=
  let base : Desc := ⟨0, 2, 1, 0, []⟩
  let cfg := ICfg.init base
  let branches : Branches := ⟨.query 0 1, .query 0 1⟩
  { base with table := [(cfg.key [] 0, branches)] }

/-- Concrete valid runtime input with positive fuel and a nondefault initial handler state. -/
private def positiveRunInput : HandlerRunInput Bool :=
  { source := { desc := positiveQueryDesc, fuel := 1, input := [], replyBits := 1 }
    handlerState := true }

/-- The positive runtime input really initializes one retained source round. -/
example : handlerRounds (initialHandlerState 1 positiveRunInput) = 1 := by
  decide

/-- The positive-fuel fixture reaches a query for either private coin, so the concrete closed body
cannot discharge this client through only its stopped or local branch. -/
private theorem positive_command (coin : Bool) :
    (ICfg.init positiveQueryDesc).commandAt 1 positiveQueryDesc [] coin =
      .query 0 [] 1 (ICfg.init positiveQueryDesc) := by
  cases coin <;> rfl

/-- The concrete complete program therefore has a positive-fuel execution that enters the locally
installed handler branch, while remaining a closed `Fin 0` oracle program. -/
private noncomputable def positiveClosedRun : WordOracleComp (Fin 0) (HandlerRunOutput Bool) :=
  handlerRunProgram 0 falseHandler positiveRunInput

/-- The positive-fuel client reaches the public complete `runState` law, including its final
Boolean handler state. -/
example :
    positiveClosedRun.run (fun impossible => impossible.1.elim0) =
      (fun result =>
        ({ output := result.1, handlerState := result.2 } : HandlerRunOutput Bool)) <$>
        ((Turing.MultiTapePTM.Universal.run 1 positiveRunInput.source).runState
          (localHandlerOracle falseHandler)).run positiveRunInput.handlerState :=
  run_handlerRunProgram_eq_runState 0 falseHandler positiveRunInput

/-- The constructed final artifact is inhabited for the same concrete locally installed handler. -/
private noncomputable def falseFinalArtifact :
    NativeOracleProgram 0 (handlerRunProgram 0 falseHandler)
      (eHandlerRunInput encBool) (eHandlerRunOutput encBool) :=
  Turing.MultiTapePTM.Universal.NativeHandler.artifact 0 encBool falseHandlerArtifact
    falsePostOnline falsePostBound falseRunCertificate

/-- Rejecting a malformed operation count preserves even a nondefault private state. -/
example :
    handlerRunProgram 0 falseHandler ⟨⟨⟨0, 0, 0, 0, []⟩, 1, [], 1⟩, true⟩ =
      pure ⟨[], true⟩ :=
  handlerRunProgram_malformed 0 falseHandler _ (by decide)

/-- One actual call flips the private bit to false, observed in the clocked machine output. -/
example (oracle : Fin 0 × List Bool → StateT Unit PMF (List Bool)) :
    ProbOracleComp.runWith oracle (falseFinalArtifact.machine.runOracle
      (falseFinalArtifact.time positiveRunInput) (eHandlerRunInput encBool positiveRunInput)) () =
      PMF.pure (eHandlerRunOutput encBool ⟨[], false⟩, ()) := by
  rw [falseFinalArtifact, runWith_artifact_machine]
  have hctrl : (ICfg.init positiveQueryDesc).control = some (some 0) := rfl
  simp only [positiveRunInput, Turing.MultiTapePTM.Universal.run, show
    positiveQueryDesc.operations = 1 from rfl, ↓reduceIte, OracleComp.iterate_succ_bind,
    OracleComp.iterate_zero, bind_pure, wordStep, hctrl,
    ProbOracleComp.runState_map, ProbOracleComp.runState_bind,
    ProbOracleComp.runState_sample, ProbOracleComp.runState_pure,
    StateT.run_map, StateT.run_bind, StateT.run_lift]
  simp only [StateT.run, ProbComp.eval_map, ProbComp.eval_bind,
    ProbComp.eval_uniform]
  simp
  simp only [positive_command, ProbOracleComp.runState_map, ProbOracleComp.runState_query]
  simp [localHandlerOracle, falseHandler, Cslib.StateT.map_apply, PMF.bind_const, ICfg.receive]
  rfl

end CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.NativeHandler

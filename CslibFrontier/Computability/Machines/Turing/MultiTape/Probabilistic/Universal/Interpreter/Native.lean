/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeOracleProgram.Static
public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Interpreter
public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Native

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Foundations.Data.BitString.ShortWords

/-!
# Retained fixed-channel oracle interpreter

This module retains one actual finite-control `MultiTapePTM` that realizes the fixed-channel
interpreter `Turing.MultiTapePTM.Universal.run r`. Runtime fuel changes the encoded input and the
certified clock, not the installed machine. The runtime description remains data; the generated
interpreter description is a separate one-occurrence installed artifact.

The construction executes named parsing, table lookup, tag, finite-dispatch, local-step,
marshalling, query, reply-copy, codec and controller machines. Its proof-only reachable-state
enumeration ranges over both private coins and every copied reply prefix of length at most the
runtime reply budget. That finite enumeration supplies uniform phase and encoded-state bounds; it
is not installed or executed.

## Main definitions

* `Turing.MultiTapePTM.Universal.NativeInterpreter.LoopState`: typed runtime loop storage.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.body`: retained one-round interpreter.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.artifact`: retained complete interpreter.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.generatedStaticBits`: exact generated artifact
  size, separate from runtime input, supplied description and emitted output sizes.

## Main results

* `Turing.MultiTapePTM.Universal.NativeInterpreter.artifact_computes`: the retained machine has
  exactly the open semantics of `run r` for every stateful handler.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.runWith_artifact_machine`: the corresponding
  stateful-distribution equality for the retained machine's clocked open execution.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.installedBits_eq_generatedStaticBits`: the
  complete composed description occurs exactly once in the installed inventory.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.generatedStaticBits_le_structuralBound`: the
  exact artifact fits the explicit exhaustive-table structural bound.
* `Turing.MultiTapePTM.Universal.NativeInterpreter.staticBits_polynomiallyBounded_of_schedules`:
  family preservation under explicit component, exhaustive-row and maximum-row schedules.

## References

The retained interpreter and its resource accounting are original to this module.
-/

@[expose] public section

namespace Turing.MultiTapePTM.Universal.NativeInterpreter

open Cslib Cslib.Probability Turing.MultiTapeMachine Turing.MultiTapeTM
  Turing.MultiTapeTM.Internal Turing.MultiTapePTM.Internal
open Turing.MultiTapePTM.Universal

/-! ### Typed loop semantics -/

/-- Complete dynamic state of the fuel-independent retained loop. `fuel` is kept separately from
`remaining` because every decoded reply is truncated to the original source instruction clock. -/
structure LoopState where
  /-- Runtime first-order source program. -/
  desc : Desc
  /-- Runtime source input. -/
  input : List ℕ
  /-- Original source instruction clock. -/
  fuel : ℕ
  /-- Maximum raw Boolean reply prefix copied on each call. -/
  replyBits : ℕ
  /-- Source rounds not yet executed. -/
  remaining : ℕ
  /-- First-order interpreted configuration. -/
  cfg : ICfg
deriving Inhabited

/-- Standard field-order encoding of dynamic loop storage. -/
enc_structure eLoopState : LoopState where
  desc : eDesc, input : (encList encUnary), fuel : encUnary, replyBits : encUnary,
  remaining : encUnary, cfg : eICfg

/-- Constructive proof decoder used only by the typed bounded-iteration theorem. The retained body
still executes and charges its concrete parsers. -/
def loopStateDecoder : Decoder eLoopState :=
  (Decoder.pair descDecoder
    (.pair (.list .unary)
      (.pair .unary (.pair .unary (.pair .unary iCfgDecoder))))).map
    (fun state =>
      ⟨state.1, state.2.1, state.2.2.1, state.2.2.2.1, state.2.2.2.2.1,
        state.2.2.2.2.2⟩)
    (fun state =>
      (state.desc, state.input, state.fuel, state.replyBits, state.remaining, state.cfg))
    (fun _ => rfl) fun _ => rfl

/-- Loop storage is absent on a channel-count mismatch. -/
def initialState (r : ℕ) (input : RunInput) : Option LoopState :=
  if input.desc.operations = r then
    some
      { desc := input.desc
        input := input.input
        fuel := input.fuel
        replyBits := input.replyBits
        remaining := input.fuel
        cfg := ICfg.init input.desc }
  else none

/-- Replace the first-order configuration and consume one source round. -/
def advance (state : LoopState) (cfg : ICfg) : LoopState :=
  { state with remaining := state.remaining - 1, cfg := cfg }

/-- Number of semantic source rounds selected by the initial typed state. -/
def rounds : Option LoopState → ℕ
  | none => 0
  | some state => state.remaining

/-- One semantic loop round. The absent and zero-remaining cases are the encoded empty-word
terminator required by `boundedIterationEncodedOn`. A halted source configuration still consumes
one outer source round but draws no coin, exactly as `wordStep`. -/
noncomputable def step (r : ℕ) : Option LoopState → WordOracleComp (Fin r) (Option LoopState)
  | none => pure none
  | some state =>
      if state.remaining = 0 then pure none
      else do
        let cfg ← wordStep r state.desc state.input state.fuel state.replyBits state.cfg
        pure (some (state.advance cfg))

/-- Extract the interpreted output without conflating it with the generated static artifact or
the runtime input and supplied-description coordinates. -/
def output : Option LoopState → List ℕ
  | none => []
  | some state => state.cfg.output

/-- Native-friendly staging of the exact fixed-channel semantics. -/
noncomputable def stagedRun (r : ℕ) (input : RunInput) : WordOracleComp (Fin r) (List ℕ) := do
  let initial := initialState r input
  let final ← OracleComp.iterate (rounds initial) (step r) initial
  pure (output final)

/-! ### Concrete deterministic layouts -/

private abbrev LoopTail1 := List ℕ × (ℕ × (ℕ × (ℕ × ICfg)))
private abbrev LoopTail2 := ℕ × (ℕ × (ℕ × ICfg))
private abbrev LoopTail3 := ℕ × (ℕ × ICfg)
private abbrev LoopTail4 := ℕ × ICfg

private def eLoopTail1 : LoopTail1 ↪ List Bool :=
  encPair (encList encUnary)
    (encPair encUnary (encPair encUnary (encPair encUnary eICfg)))
private def eLoopTail2 : LoopTail2 ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary eICfg))
private def eLoopTail3 : LoopTail3 ↪ List Bool := encPair encUnary (encPair encUnary eICfg)
private def eLoopTail4 : LoopTail4 ↪ List Bool := encPair encUnary eICfg

private abbrev RunTail := ℕ × (List ℕ × ℕ)
private def eRunTail : RunTail ↪ List Bool :=
  encPair encUnary (encPair (encList encUnary) encUnary)

/-- Retained loop-state description projection. -/
noncomputable def descCompiler : NativeCompiler LoopState.desc eLoopState eDesc :=
  NativeCompiler.first eDesc eLoopTail1

/-- Retained loop-state source-input projection. -/
noncomputable def inputCompiler : NativeCompiler LoopState.input eLoopState (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) eLoopTail2).comp
    (NativeCompiler.second eDesc eLoopTail1)

/-- Retained original-fuel projection. -/
noncomputable def fuelCompiler : NativeCompiler LoopState.fuel eLoopState encUnary :=
  (NativeCompiler.first encUnary eLoopTail3).comp
    ((NativeCompiler.second (encList encUnary) eLoopTail2).comp
      (NativeCompiler.second eDesc eLoopTail1))

/-- Retained reply-prefix budget projection. -/
noncomputable def replyBitsCompiler : NativeCompiler LoopState.replyBits eLoopState encUnary :=
  (NativeCompiler.first encUnary eLoopTail4).comp
    ((NativeCompiler.second encUnary eLoopTail3).comp
      ((NativeCompiler.second (encList encUnary) eLoopTail2).comp
        (NativeCompiler.second eDesc eLoopTail1)))

/-- Retained remaining-round projection. -/
noncomputable def remainingCompiler : NativeCompiler LoopState.remaining eLoopState encUnary :=
  (NativeCompiler.first encUnary eICfg).comp
    ((NativeCompiler.second encUnary eLoopTail4).comp
      ((NativeCompiler.second encUnary eLoopTail3).comp
        ((NativeCompiler.second (encList encUnary) eLoopTail2).comp
          (NativeCompiler.second eDesc eLoopTail1))))

/-- Retained first-order configuration projection. -/
noncomputable def cfgCompiler : NativeCompiler LoopState.cfg eLoopState eICfg :=
  (NativeCompiler.second encUnary eICfg).comp
    ((NativeCompiler.second encUnary eLoopTail4).comp
      ((NativeCompiler.second encUnary eLoopTail3).comp
        ((NativeCompiler.second (encList encUnary) eLoopTail2).comp
          (NativeCompiler.second eDesc eLoopTail1))))

private noncomputable def runDescCompiler : NativeCompiler RunInput.desc eRunInput eDesc :=
  NativeCompiler.first eDesc eRunTail

private noncomputable def runFuelCompiler : NativeCompiler RunInput.fuel eRunInput encUnary :=
  (NativeCompiler.first encUnary (encPair (encList encUnary) encUnary)).comp
    (NativeCompiler.second eDesc eRunTail)

private noncomputable def runInputCompiler :
    NativeCompiler RunInput.input eRunInput (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) encUnary).comp
    ((NativeCompiler.second encUnary (encPair (encList encUnary) encUnary)).comp
      (NativeCompiler.second eDesc eRunTail))

private noncomputable def runReplyBitsCompiler :
    NativeCompiler RunInput.replyBits eRunInput encUnary :=
  (NativeCompiler.second (encList encUnary) encUnary).comp
    ((NativeCompiler.second encUnary (encPair (encList encUnary) encUnary)).comp
      (NativeCompiler.second eDesc eRunTail))

/-- Actual initializer for the optional typed loop state, including the runtime channel-count
test and the retained first-order blank-storage constructor. -/
noncomputable def initialCompiler (r : ℕ) :
    NativeCompiler (initialState r) eRunInput (encOption eLoopState) := by
  let operations := Desc.operationsCompiler.comp runDescCompiler
  let countMatches := NativeCompiler.wordEqTest encUnary |>.comp
    (operations.pair (NativeCompiler.const eRunInput encUnary r))
  let cfg := ICfg.initCompiler.comp runDescCompiler
  let fields := runDescCompiler.pair
    (runInputCompiler.pair
      (runFuelCompiler.pair (runReplyBitsCompiler.pair (runFuelCompiler.pair cfg))))
  let present := (NativeCompiler.optionSome eLoopState).comp
    (fields.ofOutputEq fun _ => rfl)
  let absent := NativeCompiler.const eRunInput (encOption eLoopState) none
  refine (NativeCompiler.ite countMatches present absent).ofOutputEq ?_
  intro input
  by_cases h : input.desc.operations = r <;> simp [initialState, h]

private abbrev AdvanceInput := LoopState × ICfg
private def eAdvanceInput : AdvanceInput ↪ List Bool := encPair eLoopState eICfg

/-- Retained record update for one consumed source round. -/
noncomputable def advanceCompiler : NativeCompiler (fun input : AdvanceInput =>
    input.1.advance input.2) eAdvanceInput eLoopState := by
  let state := NativeCompiler.first eLoopState eICfg
  let cfg := NativeCompiler.second eLoopState eICfg
  let remaining := NativeCompiler.unaryPred.comp (remainingCompiler.comp state)
  let fields := (descCompiler.comp state).pair
    ((inputCompiler.comp state).pair
      ((fuelCompiler.comp state).pair
        ((replyBitsCompiler.comp state).pair (remaining.pair cfg))))
  exact fields.ofOutputEq fun _ => rfl

/-- Retained update wrapped in the nonempty option encoding used by the loop. -/
noncomputable def advanceSomeCompiler : NativeCompiler (fun input : AdvanceInput =>
    some (input.1.advance input.2)) eAdvanceInput (encOption eLoopState) :=
  (NativeCompiler.optionSome eLoopState).comp advanceCompiler

private abbrev BodyInput := Option LoopState
private def eBodyInput : BodyInput ↪ List Bool := encOption eLoopState
private abbrev CoinInput := BodyInput × Bool
private def eCoinInput : CoinInput ↪ List Bool := encPair eBodyInput encBool
private abbrev LookupInput := CoinInput × Option Branches
private def eLookupInput : LookupInput ↪ List Bool :=
  encPair eCoinInput (encOption eBranches)

private noncomputable def bodyStateCompiler :
    NativeCompiler (fun state : BodyInput => state.getD default) eBodyInput eLoopState :=
  NativeCompiler.optionGetD default eLoopState

private noncomputable def bodyCfgCompiler :
    NativeCompiler (fun state : BodyInput => (state.getD default).cfg) eBodyInput eICfg :=
  cfgCompiler.comp bodyStateCompiler

private noncomputable def bodyRemainingCompiler :
    NativeCompiler (fun state : BodyInput => (state.getD default).remaining)
      eBodyInput encUnary :=
  remainingCompiler.comp bodyStateCompiler

private noncomputable def advanceCurrentCompiler :
    NativeCompiler (fun state : BodyInput =>
      some ((state.getD default).advance (state.getD default).cfg))
      eBodyInput eBodyInput :=
  advanceSomeCompiler.comp (bodyStateCompiler.pair bodyCfgCompiler)

private abbrev CommandAtInput := Desc × (List ℕ × (ICfg × Bool))
private def eCommandAtInput : CommandAtInput ↪ List Bool :=
  encPair eDesc (encPair (encList encUnary) (encPair eICfg encBool))
private abbrev CommandAtLookupInput := CommandAtInput × Option Branches
private def eCommandAtLookupInput : CommandAtLookupInput ↪ List Bool :=
  encPair eCommandAtInput (encOption eBranches)

private def toCommandAtInput (input : CoinInput) : CommandAtInput :=
  let state := input.1.getD default
  (state.desc, state.input, state.cfg, input.2)

private noncomputable def commandAtInputCompiler :
    NativeCompiler
      toCommandAtInput
      eCoinInput eCommandAtInput := by
  let state := bodyStateCompiler.comp (NativeCompiler.first eBodyInput encBool)
  let coin := NativeCompiler.second eBodyInput encBool
  let fields := (descCompiler.comp state).pair
    ((inputCompiler.comp state).pair ((cfgCompiler.comp state).pair coin))
  exact fields.ofOutputEq fun _ => rfl

private noncomputable def commandAtLookupInputCompiler :
    NativeCompiler
      (fun input : LookupInput =>
        (toCommandAtInput input.1, input.2))
      eLookupInput eCommandAtLookupInput := by
  let coinInput := NativeCompiler.first eCoinInput (encOption eBranches)
  let lookup := NativeCompiler.second eCoinInput (encOption eBranches)
  exact (commandAtInputCompiler.comp coinInput).pair lookup

/-- Retained post-lookup command interpreter. The table scan itself is deliberately outside this
compiler so it can be charged once in the `lookup` phase. -/
noncomputable def commandCompiler (r : ℕ) :
    NativeCompiler
      (fun input : LookupInput =>
        commandAtFromLookup r (toCommandAtInput input.1, input.2))
      eLookupInput (eCommand r) :=
  (ICfg.commandAtFromLookupCompiler r).comp commandAtLookupInputCompiler

private abbrev QueryPayload (r : ℕ) := Fin r × (List ℕ × (ℕ × ICfg))
private def eQueryPayload (r : ℕ) : QueryPayload r ↪ List Bool :=
  encPair (eOperation r) (encPair (encList encUnary) (encPair encUnary eICfg))
private abbrev CommandSum (r : ℕ) := ICfg ⊕ QueryPayload r
private def eCommandSum (r : ℕ) : CommandSum r ↪ List Bool :=
  encSum eICfg (eQueryPayload r)
private abbrev CommandInput (r : ℕ) := LookupInput × Command r
private def eCommandInput (r : ℕ) : CommandInput r ↪ List Bool :=
  encPair eLookupInput (eCommand r)

private def defaultQueryPayload {r : ℕ} (fallback : Fin r) : QueryPayload r :=
  (fallback, [], 0, default)

private def commandQueryPayload (r : ℕ) (fallback : Fin r)
    (input : CommandInput r) : QueryPayload r :=
  Sum.elim (Function.const ICfg (defaultQueryPayload fallback)) id
    (Command.equivSum r input.2)

private def commandState (input : LookupInput) : LoopState :=
  input.1.1.getD default

private noncomputable def commandSumCompiler (r : ℕ) :
    NativeCompiler (Command.equivSum r) (eCommand r) (eCommandSum r) :=
  (NativeCompiler.identity (eCommandSum r)).ofInputEq (Command.equivSum r) fun _ => rfl

private noncomputable def commandValueCompiler (r : ℕ) :
    NativeCompiler (fun input : CommandInput r => input.2) (eCommandInput r) (eCommand r) :=
  NativeCompiler.second eLookupInput (eCommand r)

private noncomputable def commandSumInputCompiler (r : ℕ) :
    NativeCompiler (fun input : CommandInput r => Command.equivSum r input.2)
      (eCommandInput r) (eCommandSum r) :=
  (commandSumCompiler r).comp (commandValueCompiler r)

private noncomputable def commandIsQueryCompiler (r : ℕ) :
    NativeCompiler (fun input : CommandInput r => (Command.equivSum r input.2).isRight)
      (eCommandInput r) encTest :=
  NativeCompiler.boolToTest.comp
    ((NativeCompiler.sumTag eICfg (eQueryPayload r)).comp (commandSumInputCompiler r))

private noncomputable def localCfgCompiler (r : ℕ) :
    NativeCompiler
      (fun input : CommandInput r =>
        Sum.elim id (Function.const (QueryPayload r) default) (Command.equivSum r input.2))
      (eCommandInput r) eICfg :=
  (NativeCompiler.sumLeftD default eICfg (eQueryPayload r)).comp
    (commandSumInputCompiler r)

private noncomputable def queryPayloadCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (commandQueryPayload r fallback)
      (eCommandInput r) (eQueryPayload r) :=
  (NativeCompiler.sumRightD (defaultQueryPayload fallback) eICfg (eQueryPayload r)).comp
    (commandSumInputCompiler r)

private noncomputable def lookupValueCompiler (r : ℕ) :
    NativeCompiler (fun input : CommandInput r => input.1)
      (eCommandInput r) eLookupInput :=
  NativeCompiler.first eLookupInput (eCommand r)

private noncomputable def commandLoopStateCompiler (r : ℕ) :
    NativeCompiler
      (fun input : CommandInput r => commandState input.1)
      (eCommandInput r) eLoopState :=
  bodyStateCompiler.comp
    ((NativeCompiler.first eCoinInput (encOption eBranches)).comp
      (lookupValueCompiler r))

private noncomputable def localAdvanceCompiler (r : ℕ) :
    NativeCompiler (fun input : CommandInput r =>
      some ((input.1.1.1.getD default).advance
        (Sum.elim id (Function.const (QueryPayload r) default)
          (Command.equivSum r input.2))))
      (eCommandInput r) eBodyInput :=
  advanceSomeCompiler.comp
    ((commandLoopStateCompiler r).pair (localCfgCompiler r))

private noncomputable def queryOperationCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (commandQueryPayload r fallback input).1)
      (eCommandInput r) (eOperation r) :=
  (NativeCompiler.first (eOperation r)
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp
      (queryPayloadCompiler r fallback)

private noncomputable def queryTailCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (commandQueryPayload r fallback input).2)
      (eCommandInput r) (encPair (encList encUnary) (encPair encUnary eICfg)) :=
  (NativeCompiler.second (eOperation r)
    (encPair (encList encUnary) (encPair encUnary eICfg))).comp
      (queryPayloadCompiler r fallback)

private noncomputable def queryRequestCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (commandQueryPayload r fallback input).2.1)
      (eCommandInput r) (encList encUnary) :=
  (NativeCompiler.first (encList encUnary) (encPair encUnary eICfg)).comp
    (queryTailCompiler r fallback)

private noncomputable def queryNextCfgCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (commandQueryPayload r fallback input).2.2)
      (eCommandInput r) (encPair encUnary eICfg) :=
  (NativeCompiler.second (encList encUnary) (encPair encUnary eICfg)).comp
    (queryTailCompiler r fallback)

private noncomputable def queryNextCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (commandQueryPayload r fallback input).2.2.1)
      (eCommandInput r) encUnary :=
  (NativeCompiler.first encUnary eICfg).comp (queryNextCfgCompiler r fallback)

private noncomputable def queryCfgCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (commandQueryPayload r fallback input).2.2.2)
      (eCommandInput r) eICfg :=
  (NativeCompiler.second encUnary eICfg).comp (queryNextCfgCompiler r fallback)

private noncomputable def queryRequestWordCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r =>
        encList encUnary (commandQueryPayload r fallback input).2.1)
      (eCommandInput r) encBits :=
  (queryRequestCompiler r fallback).ofOutputEq fun _ => rfl

private noncomputable def queryReplyBitsCompiler (r : ℕ) :
    NativeCompiler
      (fun input : CommandInput r => (commandState input.1).replyBits)
      (eCommandInput r) encUnary :=
  replyBitsCompiler.comp (commandLoopStateCompiler r)

private def queryInput (r : ℕ) (fallback : Fin r) (input : CommandInput r) :
    List Bool × ℕ :=
  (encList encUnary (commandQueryPayload r fallback input).2.1,
    (commandState input.1).replyBits)

/-- Retained marshalling of a validated query command into the raw request and reply-copy limit
expected by a fixed-operation query primitive. -/
noncomputable def queryInputCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler (queryInput r fallback)
      (eCommandInput r) (encPair encBits encUnary) :=
  (queryRequestWordCompiler r fallback).pair (queryReplyBitsCompiler r)

private abbrev QueryPostInput (r : ℕ) := CommandInput r × List Bool
private def eQueryPostInput (r : ℕ) : QueryPostInput r ↪ List Bool :=
  encPair (eCommandInput r) encBits

private noncomputable def queryPostCommandCompiler (r : ℕ) :
    NativeCompiler (fun input : QueryPostInput r => input.1)
      (eQueryPostInput r) (eCommandInput r) :=
  NativeCompiler.first (eCommandInput r) encBits

private noncomputable def queryPostReplyCompiler (r : ℕ) :
    NativeCompiler (fun input : QueryPostInput r => input.2)
      (eQueryPostInput r) encBits :=
  NativeCompiler.second (eCommandInput r) encBits

private def queryPost (r : ℕ) (fallback : Fin r) (input : QueryPostInput r) :
    BodyInput :=
  let command := input.1
  let state := commandState command.1
  let payload := commandQueryPayload r fallback command
  let decoded := (frames input.2).map List.length |>.take state.fuel
  some (state.advance payload.2.2.2.receive payload.1 payload.2.2.1 decoded)

/-- Phase-preserving deterministic reply decoding, source-symbol truncation, checked reply
installation and loop-state update. -/
noncomputable def queryPostCompiler (r : ℕ) (fallback : Fin r) : ClassifiedCompiler
    (queryPost r fallback)
    (eQueryPostInput r) eBodyInput := by
  let command := ClassifiedCompiler.inPhase .parsing (queryPostCommandCompiler r)
  let reply := ClassifiedCompiler.inPhase .replyCopy (queryPostReplyCompiler r)
  let decoded := (ClassifiedCompiler.inPhase .codec NativeCompiler.unaryListDecoder).comp reply
  let state := (ClassifiedCompiler.inPhase .parsing (commandLoopStateCompiler r)).comp command
  let fuel := (ClassifiedCompiler.inPhase .parsing fuelCompiler).comp state
  let retained := (ClassifiedCompiler.inPhase .codec
    (NativeCompiler.takeUnary encUnary)).comp (decoded.pair fuel)
  let operation := (ClassifiedCompiler.inPhase .tags
    (queryOperationCompiler r fallback)).comp command
  let next := (ClassifiedCompiler.inPhase .tags
    (queryNextCompiler r fallback)).comp command
  let cfg := (ClassifiedCompiler.inPhase .parsing
    (queryCfgCompiler r fallback)).comp command
  let receiveInput := cfg.pair (operation.pair (next.pair retained))
  let received := (ClassifiedCompiler.inPhase .localStep
    (ICfg.receiveCompiler r)).comp receiveInput
  exact (ClassifiedCompiler.inPhase .controller advanceSomeCompiler).comp
    (state.pair received)

/-! ### Retained validated-query execution -/

private noncomputable def castProgram {r : ℕ} {Alpha Beta : Type}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    {first second : Alpha → WordOracleComp (Fin r) Beta}
    (witness : NativeOracleProgram r first encIn encOut) (h : first = second) :
    NativeOracleProgram r second encIn encOut :=
  h ▸ witness

/-- Fixed-operation query primitive after retained request/limit marshalling. -/
noncomputable def preparedQuery (r : ℕ) (fallback operation : Fin r) :=
  NativeOracleProgram.preprocess
    (ClassifiedCompiler.inPhase .marshalling (queryInputCompiler r fallback))
    (NativeOracleProgram.queryTake operation)

/-- Deterministic retained reply pipeline. -/
noncomputable def queryPostArtifact (r : ℕ) (fallback : Fin r) :=
  NativeOracleProgram.ofCompiler (r := r) (queryPostCompiler r fallback)

/-- Every raw word that can be returned by the fixed query primitive after prefix copying. This
finite proof list is never part of the retained machine or installed description. -/
noncomputable def replyPrefixes (r : ℕ) (input : CommandInput r) : List (List Bool) :=
  (BitString.shortWords (commandState input.1).replyBits).toList

/-- Uniform phase bounds for the deterministic post-query pipeline over every copied reply prefix
that the external handler can produce. -/
noncomputable def queryPostOnline (r : ℕ) (fallback : Fin r) :
    OnlineAccounting (CommandInput r) where
  time := fun phase input =>
    listMax (fun reply =>
      (queryPostArtifact r fallback).online.time phase (input, reply))
      (replyPrefixes r input)
  workspace := fun phase input =>
    listMax (fun reply =>
      (queryPostArtifact r fallback).online.workspace phase (input, reply))
      (replyPrefixes r input)

private theorem queryPostOnline_le (r : ℕ) (fallback : Fin r)
    (input : CommandInput r) (reply : List Bool)
    (hreply : reply.length ≤ (commandState input.1).replyBits) (phase : OnlinePhase) :
    (queryPostArtifact r fallback).online.time phase (input, reply) ≤
        (queryPostOnline r fallback).time phase input ∧
      (queryPostArtifact r fallback).online.workspace phase (input, reply) ≤
        (queryPostOnline r fallback).workspace phase input := by
  have hmem : reply ∈ replyPrefixes r input := by
    exact Finset.mem_toList.mpr (BitString.mem_shortWords.mpr hreply)
  exact ⟨le_listMax hmem, le_listMax hmem⟩

private theorem queryPost_resource_bound (r : ℕ) (fallback operation : Fin r)
    (input : CommandInput r) (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (reply : List Bool) (state' : OracleState)
    (hreply : (reply, state') ∈
      (ProbOracleComp.runWith oracle
        (NativeOracleProgram.queryTakeProgram operation (queryInput r fallback input))
        state).support)
    (phase : OnlinePhase) :
    (queryPostArtifact r fallback).online.time phase (input, reply) ≤
        (queryPostOnline r fallback).time phase input ∧
      (queryPostArtifact r fallback).online.workspace phase (input, reply) ≤
        (queryPostOnline r fallback).workspace phase input := by
  have hlength : reply.length ≤ (queryInput r fallback input).2 := by
    rw [NativeOracleProgram.queryTakeProgram, ProbOracleComp.runWith_map] at hreply
    obtain ⟨⟨rawReply, replyState⟩, -, heq⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp hreply
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact List.length_take_le _ _
  exact queryPostOnline_le r fallback input reply hlength phase

/-- Stateful semantics of one validated fixed-operation query and its retained reply pipeline. -/
noncomputable def queryBranchProgram (r : ℕ) (fallback operation : Fin r)
    (input : CommandInput r) : WordOracleComp (Fin r) BodyInput :=
  NativeOracleProgram.capturedProgram
    (fun command =>
      NativeOracleProgram.queryTakeProgram operation (queryInput r fallback command))
    (fun postInput => pure (queryPost r fallback postInput)) input

/-- One actual fixed-operation query branch. -/
noncomputable def queryBranch (r : ℕ) (fallback operation : Fin r) :
    NativeOracleProgram r (queryBranchProgram r fallback operation)
      (eCommandInput r) eBodyInput :=
  NativeOracleProgram.sequenceCaptured (preparedQuery r fallback operation)
    (queryPostArtifact r fallback) (queryPostOnline r fallback)
    (queryPost_resource_bound r fallback operation)

private def operationTest (r : ℕ) (fallback operation : Fin r)
    (input : CommandInput r) : List Bool :=
  encTest (decide ((commandQueryPayload r fallback input).1 = operation))

private noncomputable def operationNatCompiler (r : ℕ) (fallback : Fin r) :
    NativeCompiler
      (fun input : CommandInput r => (commandQueryPayload r fallback input).1.val)
      (eCommandInput r) encUnary :=
  (queryOperationCompiler r fallback).ofOutputEq fun _ => rfl

/-- Retained equality test for one statically installed operation branch. -/
noncomputable def operationTestCompiler (r : ℕ) (fallback operation : Fin r) :
    ClassifiedCompiler (operationTest r fallback operation) (eCommandInput r) encBits := by
  let compared := (operationNatCompiler r fallback).pair
    (NativeCompiler.const (eCommandInput r) encUnary operation.val)
  exact ClassifiedCompiler.inPhase .tags
    ((NativeCompiler.wordEqTest encUnary).comp compared |>.ofOutputEq fun _ => rfl)

/-- One case of the fixed finite operation dispatcher. -/
noncomputable def operationCase (r : ℕ) (fallback operation : Fin r) :
    NativeOracleProgram.DispatchCase r (CommandInput r) BodyInput
      (eCommandInput r) eBodyInput where
  test := operationTest r fallback operation
  condition := operationTestCompiler r fallback operation
  program := queryBranchProgram r fallback operation
  branch := queryBranch r fallback operation

/-- Explicit operation order used by the retained finite dispatcher. -/
def operations (r : ℕ) : List (Fin r) := List.finRange r

/-- Fallback is unreachable for a well-typed query command, but remains an actual deterministic
artifact. It advances the original state with the explicit local default rather than invoking a
semantic callback. -/
private def localAdvance (r : ℕ) (input : CommandInput r) : BodyInput :=
  some ((commandState input.1).advance
    (Sum.elim id (Function.const (QueryPayload r) default)
      (Command.equivSum r input.2)))

noncomputable def queryFallback (r : ℕ) :=
  NativeOracleProgram.ofCompiler (r := r)
    (ClassifiedCompiler.inPhase .controller (localAdvanceCompiler r))

/-- Actual finite fixed-operation dispatcher. For `r = 0` the case list is empty. -/
noncomputable def queryDispatch (r : ℕ) (fallback : Fin r) :=
  NativeOracleProgram.finiteDispatch
    ((operations r).map (operationCase r fallback)) (queryFallback r)

private theorem dispatchProgram_operations (r : ℕ) (fallback operation : Fin r)
    (input : CommandInput r) :
    NativeOracleProgram.dispatchProgram
        ((operations r).map (operationCase r fallback))
        (fun command => pure (localAdvance r command)) input =
      queryBranchProgram r fallback operation input := by
  have hmem : operation ∈ operations r := by simp [operations]
  generalize hops : operations r = operationList at hmem ⊢
  induction operationList with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [List.map_cons, NativeOracleProgram.dispatchProgram]
      by_cases h : head = operation
      · subst head
        simp [operationCase, operationTest]
      · have htail : operation ∈ tail := (List.mem_cons.mp hmem).resolve_left h
        simp only [operationCase, operationTest, h, decide_false, encTest_apply,
          Bool.false_eq_true, List.replicate_zero]
        exact ih htail

private def executeCommand (r : ℕ) (fallback : Fin r)
    (input : CommandInput r) : WordOracleComp (Fin r) BodyInput :=
  match input.2 with
  | .local cfg => pure (some ((commandState input.1).advance cfg))
  | .query operation _ _ _ => queryBranchProgram r fallback operation input

private def commandProgram : (r : ℕ) → CommandInput r → WordOracleComp (Fin r) BodyInput
  | 0, input =>
      match input.2 with
      | .local cfg => pure (some ((commandState input.1).advance cfg))
      | .query operation _ _ _ => Fin.elim0 operation
  | r + 1, input => executeCommand (r + 1) 0 input

/-- Complete validated-command executor for a nonempty fixed channel type. The command tag is
tested by a retained compiler, and query selection is a literal finite dispatcher. -/
noncomputable def commandExecutorSucc (r : ℕ) :
    NativeOracleProgram (r + 1) (executeCommand (r + 1) 0)
      (eCommandInput (r + 1)) eBodyInput := by
  let condition := ClassifiedCompiler.inPhase .tags (commandIsQueryCompiler (r + 1))
  let assembled := NativeOracleProgram.dispatch condition
    (queryDispatch (r + 1) 0) (queryFallback (r + 1))
  apply castProgram assembled
  funext input
  cases input.2 with
  | local cfg => simp [executeCommand, operationTest, queryFallback]
  | query operation request next cfg =>
      simp only [executeCommand, commandIsQueryCompiler, commandSumInputCompiler,
        commandValueCompiler, commandSumCompiler, Command.equivSum, encTest_apply,
        Bool.true_eq, List.replicate_one, List.cons_ne_nil, ↓reduceIte]
      exact dispatchProgram_operations (r + 1) 0 operation input

/-- Zero-channel command execution has no query branch and therefore installs no dummy `Fin 0`
operation or query artifact. -/
noncomputable def commandExecutorZero :
    NativeOracleProgram 0 (commandProgram 0)
      (eCommandInput 0) eBodyInput := by
  let local := queryFallback 0
  apply castProgram local
  funext input
  cases input.2 with
  | local cfg => rfl
  | query operation request next cfg => exact Fin.elim0 operation

/-- Complete validated-command executor, including the empty fixed-channel boundary. -/
noncomputable def commandExecutor : (r : ℕ) →
    NativeOracleProgram r (commandProgram r) (eCommandInput r) eBodyInput
  | 0 => commandExecutorZero
  | r + 1 => commandExecutorSucc r

/-! ### Single-lookup active round -/

private def lookupResult (input : CoinInput) : Option Branches :=
  let commandInput := toCommandAtInput input
  NativeCompiler.firstMatch (commandInput.1.table,
    commandInput.2.2.1.key commandInput.2.1
      ((commandInput.2.2.1.control.getD none).getD 0))

/-- The lookup scan is an actual retained deterministic artifact, after explicit marshalling of
the active loop state and private coin. -/
noncomputable def lookupArtifact (r : ℕ) :
    NativeOracleProgram r (fun input : CoinInput => pure (lookupResult input))
      eCoinInput (encOption eBranches) :=
  NativeOracleProgram.preprocess
    (ClassifiedCompiler.inPhase .marshalling commandAtInputCompiler)
    (NativeOracleProgram.ofCompiler (r := r)
      (ClassifiedCompiler.inPhase .lookup ICfg.commandAtLookupCompiler))

private def commandFromLookup (r : ℕ) (input : LookupInput) : Command r :=
  commandAtFromLookup r (toCommandAtInput input.1, input.2)

/-- Retained post-lookup command construction. It performs no table scan. -/
noncomputable def commandFromLookupArtifact (r : ℕ) :
    NativeOracleProgram r (fun input : LookupInput => pure (commandFromLookup r input))
      eLookupInput (eCommand r) :=
  NativeOracleProgram.ofCompiler (r := r)
    (ClassifiedCompiler.inPhase .localStep (commandCompiler r))

/-- Uniform resource record for the command executor at the unique deterministic command produced
from one captured lookup result. -/
def commandExecutorOnline (r : ℕ) : OnlineAccounting LookupInput :=
  (commandExecutor r).online.reindex fun input => (input, commandFromLookup r input)

private theorem commandExecutor_resource_bound (r : ℕ) (input : LookupInput)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (command : Command r) (state' : OracleState)
    (hcommand : (command, state') ∈
      (ProbOracleComp.runWith oracle (pure (commandFromLookup r input)) state).support)
    (phase : OnlinePhase) :
    (commandExecutor r).online.time phase (input, command) ≤
        (commandExecutorOnline r).time phase input ∧
      (commandExecutor r).online.workspace phase (input, command) ≤
        (commandExecutorOnline r).workspace phase input := by
  simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hcommand
  rcases hcommand with ⟨rfl, rfl⟩
  exact ⟨le_rfl, le_rfl⟩

/-- Execute the captured post-lookup command, including any validated external query. -/
noncomputable def fromLookupArtifact (r : ℕ) :=
  NativeOracleProgram.sequenceCaptured (commandFromLookupArtifact r) (commandExecutor r)
    (commandExecutorOnline r) (commandExecutor_resource_bound r)

/-- Resource record for the unique deterministic table result on one coin-bearing input. -/
def fromLookupOnline (r : ℕ) : OnlineAccounting CoinInput :=
  (fromLookupArtifact r).online.reindex fun input => (input, lookupResult input)

private theorem fromLookup_resource_bound (r : ℕ) (input : CoinInput)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (lookup : Option Branches) (state' : OracleState)
    (hlookup : (lookup, state') ∈
      (ProbOracleComp.runWith oracle (pure (lookupResult input)) state).support)
    (phase : OnlinePhase) :
    (fromLookupArtifact r).online.time phase (input, lookup) ≤
        (fromLookupOnline r).time phase input ∧
      (fromLookupArtifact r).online.workspace phase (input, lookup) ≤
        (fromLookupOnline r).workspace phase input := by
  simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
    Prod.mk.injEq] at hlookup
  rcases hlookup with ⟨rfl, rfl⟩
  exact ⟨le_rfl, le_rfl⟩

/-- One coin-bearing active round with exactly one captured table scan. -/
noncomputable def coinRoundArtifact (r : ℕ) :=
  NativeOracleProgram.sequenceCaptured (lookupArtifact r) (fromLookupArtifact r)
    (fromLookupOnline r) (fromLookup_resource_bound r)

/-- Phasewise maximum of the active continuation over the two fair-coin outcomes. -/
def coinRoundOnline (r : ℕ) : OnlineAccounting BodyInput where
  time := fun phase input =>
    max (coinRoundArtifact r).online.time phase (input, false)
      ((coinRoundArtifact r).online.time phase (input, true))
  workspace := fun phase input =>
    max (coinRoundArtifact r).online.workspace phase (input, false)
      ((coinRoundArtifact r).online.workspace phase (input, true))

private theorem coinRound_resource_bound (r : ℕ) (input : BodyInput)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (coin : Bool) (state' : OracleState)
    (hcoin : (coin, state') ∈
      (ProbOracleComp.runWith oracle
        (ProbOracleComp.sample (ProbComp.uniform Bool)) state).support)
    (phase : OnlinePhase) :
    (coinRoundArtifact r).online.time phase (input, coin) ≤
        (coinRoundOnline r).time phase input ∧
      (coinRoundArtifact r).online.workspace phase (input, coin) ≤
        (coinRoundOnline r).workspace phase input := by
  cases coin
  · exact ⟨le_max_left _ _, le_max_left _ _⟩
  · exact ⟨le_max_right _ _, le_max_right _ _⟩

/-- Active source round: sample one retained fair bit, scan the runtime table once, then execute
the selected local or validated query command. -/
noncomputable def activeArtifact (r : ℕ) :=
  NativeOracleProgram.sequenceCaptured
    (NativeOracleProgram.fairBit (r := r) eBodyInput) (coinRoundArtifact r)
    (coinRoundOnline r) (coinRound_resource_bound r)

private def activeProgram (r : ℕ) (input : BodyInput) :
    WordOracleComp (Fin r) BodyInput :=
  NativeOracleProgram.capturedProgram
    (fun _ : BodyInput => ProbOracleComp.sample (ProbComp.uniform Bool))
    (fun coinInput =>
      NativeOracleProgram.capturedProgram
        (fun input : CoinInput => pure (lookupResult input))
        (fun lookupInput =>
          NativeOracleProgram.capturedProgram
            (fun input : LookupInput => pure (commandFromLookup r input))
            (commandProgram r) lookupInput)
        coinInput)
    input

/-! ### Outer one-round controller -/

private def bodyIsSome (input : BodyInput) : List Bool := encTest input.isSome
private def bodyRemainingIsZero (input : BodyInput) : List Bool :=
  encTest ((input.getD default).remaining = 0)
private def bodyControlIsSome (input : BodyInput) : List Bool :=
  encTest (input.getD default).cfg.control.isSome

private noncomputable def bodyIsSomeCompiler :
    ClassifiedCompiler bodyIsSome eBodyInput encBits :=
  ClassifiedCompiler.inPhase .tags
    ((NativeCompiler.optionIsSomeTest eLoopState).ofOutputEq fun _ => rfl)

private noncomputable def bodyRemainingIsZeroCompiler :
    ClassifiedCompiler bodyRemainingIsZero eBodyInput encBits :=
  ClassifiedCompiler.inPhase .controller
    ((NativeCompiler.unaryIsZeroTest.comp bodyRemainingCompiler).ofOutputEq fun _ => rfl)

private noncomputable def bodyControlIsSomeCompiler :
    ClassifiedCompiler bodyControlIsSome eBodyInput encBits := by
  let control := ICfg.controlCompiler.comp bodyCfgCompiler
  exact ClassifiedCompiler.inPhase .tags
    (((NativeCompiler.optionIsSomeTest Turing.MultiTapeTM.Universal.eSym).comp control).ofOutputEq
      fun _ => rfl)

private noncomputable def stopArtifact (r : ℕ) :=
  NativeOracleProgram.ofCompiler (r := r)
    (ClassifiedCompiler.inPhase .controller
      (NativeCompiler.const eBodyInput eBodyInput none))

private noncomputable def haltedRoundArtifact (r : ℕ) :=
  NativeOracleProgram.ofCompiler (r := r)
    (ClassifiedCompiler.inPhase .controller advanceCurrentCompiler)

/-- Retained one-round controller. Absent and zero-remaining states emit the empty option word;
halted source storage decrements the source clock without sampling; active storage executes the
coin/lookup/command pipeline. -/
noncomputable def body (r : ℕ) :
    NativeOracleProgram r (step r) eBodyInput eBodyInput := by
  let byControl := NativeOracleProgram.dispatch bodyControlIsSomeCompiler
    (activeArtifact r) (haltedRoundArtifact r)
  let byRemaining := NativeOracleProgram.dispatch bodyRemainingIsZeroCompiler
    (stopArtifact r) byControl
  let assembled := NativeOracleProgram.dispatch bodyIsSomeCompiler byRemaining (stopArtifact r)
  apply castProgram assembled
  funext input
  cases input with
  | none => simp [step, bodyIsSome, NativeOracleProgram.dispatchProgram]
  | some state =>
      by_cases hremaining : state.remaining = 0
      · simp [step, bodyIsSome, bodyRemainingIsZero, hremaining,
          NativeOracleProgram.dispatchProgram]
      · cases hcontrol : state.cfg.control with
        | none =>
            simp [step, bodyIsSome, bodyRemainingIsZero, bodyControlIsSome,
              hremaining, hcontrol, NativeOracleProgram.dispatchProgram,
              advanceCurrentCompiler, advance]
        | some control =>
            simp only [bodyIsSome, bodyRemainingIsZero, bodyControlIsSome, hremaining,
              hcontrol, Option.isSome_some, encTest_apply, Bool.true_eq,
              List.replicate_one, List.cons_ne_nil, ↓reduceIte]
            simp [step, activeProgram, NativeOracleProgram.capturedProgram, lookupResult,
              commandFromLookup, commandProgram, executeCommand, queryBranchProgram,
              NativeOracleProgram.queryTakeProgram, queryInput, queryPost,
              commandQueryPayload, defaultQueryPayload,
              commandAtFromLookup_firstMatch, hremaining, hcontrol]

/-! ### Finite proof reachability and uniform round bounds -/

private def withDynamic (template : LoopState) (remaining : ℕ) (cfg : ICfg) : LoopState :=
  { template with remaining := remaining, cfg := cfg }

private theorem iterate_step_withDynamic (r : ℕ) (template : LoopState) (cfg : ICfg) :
    ∀ count,
      OracleComp.iterate count (step r) (some (withDynamic template count cfg)) =
        (fun final => some (withDynamic template 0 final)) <$>
          OracleComp.iterate count
            (wordStep r template.desc template.input template.fuel template.replyBits) cfg
  | 0 => by simp [withDynamic]
  | count + 1 => by
      rw [OracleComp.iterate_succ_bind, OracleComp.iterate_succ_bind]
      simp only [step, withDynamic, Nat.succ_ne_zero, ↓reduceIte, advance]
      apply OracleComp.bind_congr_on_support
      intro next _
      simpa only [Nat.succ_sub_one] using iterate_step_withDynamic r template next count

/-- Native-friendly staging is extensionally the original source word program. -/
theorem stagedRun_eq_run (r : ℕ) : stagedRun r = run r := by
  funext input
  by_cases hcount : input.desc.operations = r
  · simp only [stagedRun, initialState, hcount, ↓reduceIte, rounds]
    rw [show
      { desc := input.desc, input := input.input, fuel := input.fuel,
          replyBits := input.replyBits, remaining := input.fuel, cfg := ICfg.init input.desc } =
        withDynamic
          { desc := input.desc, input := input.input, fuel := input.fuel,
            replyBits := input.replyBits, remaining := input.fuel, cfg := ICfg.init input.desc }
          input.fuel (ICfg.init input.desc) by rfl]
    rw [iterate_step_withDynamic]
    simp [run, hcount, output, withDynamic]
  · simp [stagedRun, initialState, hcount, rounds, output, run]

private noncomputable def replyWords (replyBits : ℕ) : List (List Bool) :=
  (BitString.shortWords replyBits).toList

private def successorForReply (state : LoopState) (operation : Fin r) (next : ℕ)
    (pending : ICfg) (reply : List Bool) : BodyInput :=
  some (state.advance (pending.receive operation next
    ((unaryListDecoder.decode reply).take state.fuel)))

private noncomputable def coinSuccessors (r : ℕ) (state : LoopState) (coin : Bool) :
    List BodyInput :=
  match state.cfg.commandAt r state.desc state.input coin with
  | .local cfg => [some (state.advance cfg)]
  | .query operation _ next pending =>
      (replyWords state.replyBits).map
        (successorForReply state operation next pending)

/-- Finite overapproximation of all one-round results under arbitrary stateful handlers. Duplicate
states are harmless and keep the proof enumeration independent of `DecidableEq LoopState`. -/
noncomputable def successors (r : ℕ) : BodyInput → List BodyInput
  | none => [none]
  | some state =>
      if state.remaining = 0 then [none]
      else match state.cfg.control with
        | none => [some (state.advance state.cfg)]
        | some _ => [false, true].flatMap (coinSuccessors r state)

/-- States reachable after exactly `count` semantic rounds in the proof enumeration. -/
noncomputable def reachable (r : ℕ) (initial : BodyInput) : ℕ → List BodyInput
  | 0 => [initial]
  | count + 1 => (successors r initial).flatMap fun next => reachable r next count

/-- All reachable typed states at indices used by the bounded-iteration certificate. -/
noncomputable def reachablePrefix (r : ℕ) (initial : BodyInput) : List BodyInput :=
  (List.range (rounds initial + 1)).flatMap (reachable r initial)

private theorem support_mem_successors (r : ℕ) (current next : BodyInput)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (step r current) state).support) :
    next ∈ successors r current := by
  rcases current with _ | current
  · simp only [step, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hnext
    rcases hnext with ⟨rfl, rfl⟩
    simp [successors]
  · by_cases hremaining : current.remaining = 0
    · simp only [step, hremaining, ↓reduceIte, ProbOracleComp.runWith_pure,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hnext
      rcases hnext with ⟨rfl, rfl⟩
      simp [successors, hremaining]
    · cases hcontrol : current.cfg.control with
      | none =>
          simp only [step, hremaining, hcontrol, wordStep, ↓reduceIte,
            ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hnext
          rcases hnext with ⟨rfl, rfl⟩
          simp [successors, hremaining, hcontrol]
      | some control =>
          rw [step, if_neg hremaining, wordStep, hcontrol,
            ProbOracleComp.runWith_bind] at hnext
          obtain ⟨⟨coin, coinState⟩, hcoin, hcommand⟩ :=
            (PMF.mem_support_bind_iff _ _ _).mp hnext
          have hcoinValue : coin = false ∨ coin = true := by cases coin <;> simp
          cases hcmd : current.cfg.commandAt r current.desc current.input coin with
          | local cfg =>
              simp only [hcmd, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                Prod.mk.injEq] at hcommand
              rcases hcommand with ⟨rfl, rfl⟩
              simp only [successors, hremaining, hcontrol, coinSuccessors, hcmd,
                List.mem_flatMap, List.mem_cons, List.mem_singleton]
              exact ⟨coin, hcoinValue, by simp⟩
          | query operation request nextTag pending =>
              rw [hcmd, ProbOracleComp.runWith_bind] at hcommand
              obtain ⟨⟨reply, replyState⟩, hreply, hfinal⟩ :=
                (PMF.mem_support_bind_iff _ _ _).mp hcommand
              simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                Prod.mk.injEq] at hfinal
              rcases hfinal with ⟨rfl, rfl⟩
              have hprefix : reply.take current.replyBits ∈ replyWords current.replyBits := by
                exact Finset.mem_toList.mpr
                  (BitString.mem_shortWords.mpr (List.length_take_le _ _))
              simp only [successors, hremaining, hcontrol, List.mem_flatMap,
                List.mem_cons, List.mem_singleton]
              refine ⟨coin, hcoinValue, ?_⟩
              simp only [coinSuccessors, hcmd, List.mem_map]
              exact ⟨reply.take current.replyBits, hprefix, rfl⟩

private theorem mem_reachable_succ {r : ℕ} {initial current next : BodyInput} {count : ℕ}
    (hcurrent : current ∈ reachable r initial count)
    (hnext : next ∈ successors r current) :
    next ∈ reachable r initial (count + 1) := by
  induction count generalizing initial with
  | zero =>
      simp only [reachable, List.mem_singleton] at hcurrent
      subst current
      simp only [reachable, List.mem_flatMap]
      exact ⟨next, hnext, by simp [reachable]⟩
  | succ count ih =>
      simp only [reachable, List.mem_flatMap] at hcurrent ⊢
      obtain ⟨middle, hmiddle, hcurrent⟩ := hcurrent
      exact ⟨middle, hmiddle, ih hcurrent hnext⟩

private theorem support_mem_reachable (r : ℕ) (initial : BodyInput) (count : ℕ)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (current : BodyInput) (state' : OracleState)
    (hcurrent : (current, state') ∈
      (ProbOracleComp.runWith oracle
        (OracleComp.iterate count (step r) initial) state).support) :
    current ∈ reachable r initial count := by
  induction count generalizing initial state current with
  | zero =>
      simp only [OracleComp.iterate_zero, ProbOracleComp.runWith_pure,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hcurrent
      rcases hcurrent with ⟨rfl, rfl⟩
      simp [reachable]
  | succ count ih =>
      rw [OracleComp.iterate_succ_bind, ProbOracleComp.runWith_bind] at hcurrent
      obtain ⟨⟨middle, middleState⟩, hmiddle, htail⟩ :=
        (PMF.mem_support_bind_iff _ _ _).mp hcurrent
      simp only [reachable, List.mem_flatMap]
      exact ⟨middle,
        support_mem_successors r initial middle OracleState oracle state middleState hmiddle,
        ih middle middleState current htail⟩

private structure SameStatic (first second : LoopState) : Prop where
  desc : second.desc = first.desc
  input : second.input = first.input
  fuel : second.fuel = first.fuel
  replyBits : second.replyBits = first.replyBits

private def Progress (initial : BodyInput) (count : ℕ) (current : BodyInput) : Prop :=
  match initial with
  | none => current = none
  | some first => ∃ second, current = some second ∧ first.SameStatic second ∧
      second.remaining + count = first.remaining

/-- Reachability plus the exact remaining-round equation. -/
def Invariant (r : ℕ) (initial : BodyInput) (count : ℕ) (current : BodyInput) : Prop :=
  Progress initial count current ∧ current ∈ reachable r initial count

private theorem invariant_zero (r : ℕ) (initial : BodyInput) :
    Invariant r initial 0 initial := by
  constructor
  · cases initial <;> simp [Progress, SameStatic]
  · simp [reachable]

private theorem progress_successor {r : ℕ} {initial current next : BodyInput} {count : ℕ}
    (hcount : count < rounds initial) (hprogress : Progress initial count current)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (step r current) state).support) :
    Progress initial (count + 1) next ∧ (encOption eLoopState next ≠ []) := by
  cases hinitial : initial with
  | none => simp [rounds, hinitial] at hcount
  | some first =>
      simp only [Progress, hinitial] at hprogress
      obtain ⟨second, rfl, hstatic, hremaining⟩ := hprogress
      have hpositive : second.remaining ≠ 0 := by omega
      cases hcontrol : second.cfg.control with
      | none =>
          simp only [step, hpositive, hcontrol, wordStep, ↓reduceIte,
            ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
            Prod.mk.injEq] at hnext
          rcases hnext with ⟨rfl, rfl⟩
          constructor
          · refine ⟨second.advance second.cfg, rfl, ?_, ?_⟩
            · exact ⟨hstatic.desc, hstatic.input, hstatic.fuel, hstatic.replyBits⟩
            · simp only [advance]
              omega
          · simp
      | some control =>
          have hsome : ∃ nextCfg, next = some (second.advance nextCfg) := by
            rw [step, if_neg hpositive, wordStep, hcontrol,
              ProbOracleComp.runWith_bind] at hnext
            obtain ⟨⟨coin, coinState⟩, hcoin, hcommand⟩ :=
              (PMF.mem_support_bind_iff _ _ _).mp hnext
            cases hcmd : second.cfg.commandAt r second.desc second.input coin with
            | local cfg =>
                simp only [hcmd, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                  Prod.mk.injEq] at hcommand
                exact ⟨cfg, hcommand.1⟩
            | query operation request nextTag pending =>
                rw [hcmd, ProbOracleComp.runWith_bind] at hcommand
                obtain ⟨⟨reply, replyState⟩, hreply, hfinal⟩ :=
                  (PMF.mem_support_bind_iff _ _ _).mp hcommand
                simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
                  Prod.mk.injEq] at hfinal
                exact ⟨pending.receive operation nextTag
                  ((unaryListDecoder.decode (reply.take second.replyBits)).take second.fuel),
                  hfinal.1⟩
          obtain ⟨nextCfg, rfl⟩ := hsome
          constructor
          · refine ⟨second.advance nextCfg, rfl, ?_, ?_⟩
            · exact ⟨hstatic.desc, hstatic.input, hstatic.fuel, hstatic.replyBits⟩
            · simp only [advance]
              omega
          · simp

private theorem invariant_successor {r : ℕ} {initial current next : BodyInput} {count : ℕ}
    (hcount : count < rounds initial) (hinvariant : Invariant r initial count current)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state state' : OracleState)
    (hnext : (next, state') ∈
      (ProbOracleComp.runWith oracle (step r current) state).support) :
    Invariant r initial (count + 1) next ∧ encOption eLoopState next ≠ [] := by
  refine ⟨⟨(progress_successor hcount hinvariant.1 OracleState oracle state state' hnext).1,
    ?_⟩, (progress_successor hcount hinvariant.1 OracleState oracle state state' hnext).2⟩
  exact mem_reachable_succ hinvariant.2
    (support_mem_successors r current next OracleState oracle state state' hnext)

private theorem invariant_last (r : ℕ) (initial current : BodyInput)
    (hinvariant : Invariant r initial (rounds initial) current)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) :
    ProbOracleComp.runWith oracle (encOption eLoopState <$> step r current) state =
      ProbOracleComp.runWith oracle (pure []) state := by
  cases hinitial : initial with
  | none =>
      simp only [Progress, hinitial] at hinvariant
      subst current
      simp [step]
  | some first =>
      simp only [Progress, hinitial, rounds] at hinvariant
      obtain ⟨second, rfl, hstatic, hremaining⟩ := hinvariant.1
      have hzero : second.remaining = 0 := by omega
      simp [step, hzero]

private theorem mem_reachablePrefix {r : ℕ} {initial current : BodyInput} {count : ℕ}
    (hcount : count ≤ rounds initial) (hcurrent : current ∈ reachable r initial count) :
    current ∈ reachablePrefix r initial := by
  simp only [reachablePrefix, List.mem_flatMap]
  exact ⟨count, List.mem_range.mpr (by omega), hcurrent⟩

/-- Maximum encoded typed-state length over every finitely enumerated reachable prefix state. -/
noncomputable def lengthBound (r : ℕ) (initial : BodyInput) : ℕ :=
  listMax (fun state => (encOption eLoopState state).length) (reachablePrefix r initial)

/-- Phasewise maximum of the retained body over every finitely enumerated reachable prefix state. -/
noncomputable def roundOnline (r : ℕ) : OnlineAccounting BodyInput where
  time := fun phase initial =>
    listMax (fun current => (body r).online.time phase current) (reachablePrefix r initial)
  workspace := fun phase initial =>
    listMax (fun current => (body r).online.workspace phase current) (reachablePrefix r initial)

private theorem body_resource_bound (r : ℕ) (initial : BodyInput) (count : ℕ)
    (hcount : count ≤ rounds initial) (current : BodyInput)
    (hinvariant : Invariant r initial count current) (phase : OnlinePhase) :
    (body r).online.time phase current ≤ (roundOnline r).time phase initial ∧
      (body r).online.workspace phase current ≤
        (roundOnline r).workspace phase initial := by
  have hmem := mem_reachablePrefix hcount hinvariant.2
  exact ⟨le_listMax hmem, le_listMax hmem⟩

private theorem state_length_bound (r : ℕ) (initial : BodyInput) (count : ℕ)
    (hcount : count ≤ rounds initial) (current : BodyInput)
    (hinvariant : Invariant r initial count current) :
    (encOption eLoopState current).length ≤ lengthBound r initial :=
  le_listMax (mem_reachablePrefix hcount hinvariant.2)

/-! ### Complete retained artifact -/

/-- Retained typed loop with runtime-indexed clock, state-length and per-phase bounds. -/
noncomputable def loopArtifact (r : ℕ) :=
  NativeOracleProgram.boundedIterationEncodedOn (.option loopStateDecoder) (body r) rounds
    (lengthBound r) (roundOnline r) (Invariant r) (invariant_zero r)
    (fun initial count hcount current hinvariant phase =>
      (body_resource_bound r initial count hcount current hinvariant phase).1)
    (fun initial count hcount current hinvariant phase =>
      (body_resource_bound r initial count hcount current hinvariant phase).2)
    (fun initial count hcount current hinvariant OracleState oracle state state' next hnext =>
      invariant_successor hcount hinvariant OracleState oracle state state' hnext)
    (invariant_last r) (state_length_bound r)

private noncomputable def classifiedInitial (r : ℕ) :=
  ClassifiedCompiler.inPhase .inputCopy (initialCompiler r)

/-- Copy and initialize the encoded runtime input before the fixed loop machine. -/
noncomputable def initializedLoop (r : ℕ) :=
  NativeOracleProgram.preprocess (classifiedInitial r) (loopArtifact r)

private noncomputable def outputCompiler :
    NativeCompiler output eBodyInput (encList encUnary) := by
  let state := bodyStateCompiler
  exact (ICfg.outputCompiler.comp (cfgCompiler.comp state)).ofOutputEq fun input => by
    cases input <;> rfl

/-- Reachability maximum for the output-copy compiler on final loop results. -/
noncomputable def outputOnline (r : ℕ) : OnlineAccounting RunInput where
  time := fun phase input =>
    listMax (fun current =>
      (ClassifiedCompiler.inPhase .outputCopy outputCompiler).online.time phase current)
      (reachable r (initialState r input) (rounds (initialState r input)))
  workspace := fun phase input =>
    listMax (fun current =>
      (ClassifiedCompiler.inPhase .outputCopy outputCompiler).online.workspace phase current)
      (reachable r (initialState r input) (rounds (initialState r input)))

private theorem output_resource_bound (r : ℕ) (input : RunInput)
    (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool))
    (state : OracleState) (current : BodyInput) (state' : OracleState)
    (hcurrent : (current, state') ∈
      (ProbOracleComp.runWith oracle
        (OracleComp.iterate (rounds (initialState r input)) (step r)
          (initialState r input)) state).support)
    (phase : OnlinePhase) :
    (ClassifiedCompiler.inPhase .outputCopy outputCompiler).online.time phase current ≤
        (outputOnline r).time phase input ∧
      (ClassifiedCompiler.inPhase .outputCopy outputCompiler).online.workspace phase current ≤
        (outputOnline r).workspace phase input := by
  have hreach := support_mem_reachable r (initialState r input)
    (rounds (initialState r input)) OracleState oracle state current state' hcurrent
  exact ⟨le_listMax hreach, le_listMax hreach⟩

/-- Complete fixed-channel retained interpreter before the extensional source-semantics cast. -/
noncomputable def stagedArtifact (r : ℕ) :
    NativeOracleProgram r (stagedRun r) eRunInput (encList encUnary) :=
  NativeOracleProgram.postprocess (initializedLoop r)
    (ClassifiedCompiler.inPhase .outputCopy outputCompiler) (outputOnline r)
    (output_resource_bound r)

/-- Complete actual finite-control interpreter for `run r`. -/
noncomputable def artifact (r : ℕ) :
    NativeOracleProgram r (run r) eRunInput (encList encUnary) :=
  castProgram (stagedArtifact r) (stagedRun_eq_run r)

/-- Direct clean-phase certificate for the actual retained machine. -/
theorem artifact_computes (r : ℕ) (input : RunInput) :
    (artifact r).machine.ComputesTidily (eRunInput input) ((artifact r).time input)
      ((encList encUnary) <$> run r input) :=
  (artifact r).computes input

/-- Exact open semantics of the actual retained finite-control machine against every adaptive
stateful Boolean-word handler. -/
theorem runWith_artifact_machine (r : ℕ) (input : RunInput) (OracleState : Type)
    (oracle : Fin r × List Bool → StateT OracleState PMF (List Bool)) (state : OracleState) :
    ProbOracleComp.runWith oracle
        ((artifact r).machine.runOracle ((artifact r).time input) (eRunInput input)) state =
      ProbOracleComp.runWith oracle ((encList encUnary) <$> run r input) state :=
  (artifact_computes r input).runOracle oracle state

/-! ### Separate concrete resource coordinates -/

/-- Exact generated and installed interpreter-description size. It excludes the runtime input,
the supplied runtime `Desc`, emitted output and every external handler artifact. -/
noncomputable def generatedStaticBits (r : ℕ) : ℕ := (artifact r).staticBits

/-- Construction-derived structural bound for the generated interpreter description. -/
noncomputable def structuralBound (r : ℕ) : ℕ := (artifact r).staticBitsBound

/-- Exact emitted result size, separate from generated code and runtime input. -/
def emittedOutputBits (output : List ℕ) : ℕ := (encList encUnary output).length

/-- Canonical componentwise online time ledger. -/
noncomputable def phaseTime (r : ℕ) (phase : OnlinePhase) (input : RunInput) : ℕ :=
  (artifact r).online.time phase input

/-- Canonical componentwise online ordinary-workspace ledger. Communication buffers and the
external handler's private storage remain separate. -/
noncomputable def phaseWorkspace (r : ℕ) (phase : OnlinePhase) (input : RunInput) : ℕ :=
  (artifact r).online.workspace phase input

/-- Scalar online time is derived only by summing the componentwise ledger. -/
theorem time_eq_sum_phaseTime (r : ℕ) (input : RunInput) :
    (artifact r).time input = ∑ phase, phaseTime r phase input :=
  rfl

/-- Scalar online workspace is derived only as the peak of the componentwise ledger. -/
theorem workspace_eq_sup_phaseWorkspace (r : ℕ) (input : RunInput) :
    (artifact r).workspace input = Finset.univ.sup fun phase =>
      phaseWorkspace r phase input :=
  rfl

/-- The complete composed interpreter is the only installed description occurrence. Its inlined
initializer, controller, dispatcher, query primitives, codecs and local-step machines are not
charged again as separate installed copies. -/
theorem installedDescriptions_eq_singleton (r : ℕ) :
    (artifact r).installedDescriptions = [(artifact r).description] :=
  (artifact r).installedDescriptions_eq_singleton

/-- The exact one-occurrence installed inventory equals the generated static-size coordinate. -/
theorem installedBits_eq_generatedStaticBits (r : ℕ) :
    (artifact r).installedBits = generatedStaticBits r :=
  (artifact r).installedBits_eq_staticBits

/-- Exact generated size is the `descLen` of the final composed first-order description. -/
theorem generatedStaticBits_eq_descLen (r : ℕ) :
    generatedStaticBits r = descLen (artifact r).description :=
  (artifact r).staticBits_eq_descLen

/-- The generated artifact fits the honest exhaustive-table structural bound. -/
theorem generatedStaticBits_le_structuralBound (r : ℕ) :
    generatedStaticBits r ≤ structuralBound r :=
  (artifact r).staticBits_le_staticBitsBound

/-! ### Static-size families -/

/-- Exact generated static-size schedule for a channel-count family. -/
noncomputable def staticBitsSchedule (channels : ℕ → ℕ) (n : ℕ) : ℕ :=
  generatedStaticBits (channels n)

noncomputable def tapeSchedule (channels : ℕ → ℕ) (n : ℕ) : ℕ :=
  (artifact (channels n)).tapeCount

noncomputable def stateCardSchedule (channels : ℕ → ℕ) (n : ℕ) : ℕ :=
  (artifact (channels n)).stateCard

noncomputable def stateTagSchedule (channels : ℕ → ℕ) (n : ℕ) : ℕ :=
  (artifact (channels n)).stateTagCount

noncomputable def initialTagSchedule (channels : ℕ → ℕ) (n : ℕ) : ℕ :=
  (artifact (channels n)).initialStateTag

noncomputable def maxRowSchedule (channels : ℕ → ℕ) (n : ℕ) : ℕ :=
  (artifact (channels n)).maxEncodedRowBits

/-- Honest family preservation theorem. In particular, polynomial channel and tape counts do not
discharge `hrows`: the exhaustive table contains the explicit exponential factor
`3 ^ tapeSchedule * 3 ^ channels`. A growing-channel result therefore needs a separate compressed
or wildcard representation, or an independently proved polynomial exhaustive-row schedule. -/
theorem staticBits_polynomiallyBounded_of_schedules (channels : ℕ → ℕ)
    (htapes : PolynomiallyBounded (tapeSchedule channels))
    (htags : PolynomiallyBounded (stateTagSchedule channels))
    (hchannels : PolynomiallyBounded channels)
    (hinitial : PolynomiallyBounded (initialTagSchedule channels))
    (hrows : PolynomiallyBounded fun n =>
      Description.observationRowCount (stateCardSchedule channels n)
        (tapeSchedule channels n) (channels n))
    (hmaxRow : PolynomiallyBounded (maxRowSchedule channels)) :
    PolynomiallyBounded (staticBitsSchedule channels) := by
  apply Description.staticBits_polynomiallyBounded_of_le htapes htags hchannels hinitial hrows
    hmaxRow
  intro n
  simpa [staticBitsSchedule, generatedStaticBits, structuralBound,
    tapeSchedule, stateCardSchedule, stateTagSchedule, initialTagSchedule, maxRowSchedule,
    NativeOracleProgram.staticBitsBound, NativeOracleProgram.observationRowCount,
    NativeOracleProgram.operationCount, Description.scheduledBitsBound] using
    (artifact (channels n)).staticBits_le_staticBitsBound

/-- For every fixed finite channel count, the one installed interpreter is independent of runtime
input size, so its exact static size is a constant polynomial schedule. -/
theorem staticBits_polynomiallyBounded_fixed (r : ℕ) :
    PolynomiallyBounded (fun _ : ℕ => generatedStaticBits r) :=
  PolynomiallyBounded.const (generatedStaticBits r)

end Turing.MultiTapePTM.Universal.NativeInterpreter
